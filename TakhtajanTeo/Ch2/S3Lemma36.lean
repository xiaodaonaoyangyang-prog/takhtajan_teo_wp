import TakhtajanTeo.Ch2.S3PreSchwarzianKernel
import TakhtajanTeo.Ch2.S5_Embedding
import TakhtajanTeo.Appendix.B_PeriodMapping
import TakhtajanTeo.Appendix.AppACor6
import TakhtajanTeo.Ch2.S3AeContinuity

/-! # Lemma 3.6 (TT:4962–5154) (Program G, 下属4, prefix `s36l_`)

Route (TT's own): the identity is first proved for "smooth" points, then for general points of `T₀(1)` by dilation.
It is proved in the `(𝖿, 𝗀) = (fsans κ, gsans κ)` model as `K₁v̄₁ + K₂v̄₂ = -u₁` on `𝔻 \ {0}` (`s36l_core`), and
transferred to the `(f̃, g̃)` model of `lemma_3_6` through the inverse class (`s3pk_gTilde_pair`, `s3pk_fTilde_pair`).

* Smooth case (`s36l_smooth_pair`): an abstract complementary pair `f` on `𝔻`, `g` on `𝔻*`, both holomorphic and
  injective across `S¹`. TT's Stokes/Cauchy argument on the analytic curve `f(S¹)`.
* Approximation: `κₙ(z) = κ(ρₙ z)·1_{|z| > 1/ρₙ}`, `ρₙ ↑ 1` along which `κ(ρₙ ·) → κ` a.e. (`s36l_dil_seq`). The
  Model B plane solution of `κₙ` is `W(ρₙ ·)/W(ρₙ)` (`s36l_V_ns`), so `fsans κₙ` is a Möbius normalization of
  `f(ρₙ ·)/ρₙ` (`s36l_dil_fsans`; the Model A poles converge by `Ch2/S3AeContinuity`), `κₙ` vanishes on `1 < |z| < 1/ρₙ`, and the `𝗀`-side converges
  (`s36l_dil_gconv`, `s36l_dil_gtail`), with a uniform energy bound (`s36l_dil_energy`, from Cor. A.4/A.6); the tail
  bound uses the null quasicircle of Remark 2.2 (`s36l_G_circle_null`).
  The `𝖿`-side terms converge explicitly; no Carathéodory kernel theorem is needed.
-/

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal ComplexConjugate Classical Real

noncomputable section

namespace TakhtajanTeo.Ch2

open LiZhongQC

/-! ### Smooth case -/

/-! ### Helpers for `s36l_smooth_pair` (sub-interface) -/

/-- Holomorphic primitives on the disc `|w| < R`: `P' = 𝒜(f)` and `Q' = 𝒜(f) - 2f'/f + 2/w` (`w ≠ 0`; the right side
is removable at `0`). -/
theorem s36l_sp_primD {f : ℂ → ℂ} {R : ℝ} (hR : 1 < R)
    (hf : DifferentiableOn ℂ f (ball 0 R)) (hfi : InjOn f (ball 0 R)) (hf0 : f 0 = 0) :
    ∃ P Q : ℂ → ℂ, DifferentiableOn ℂ P (ball 0 R) ∧ DifferentiableOn ℂ Q (ball 0 R) ∧
      (∀ w ∈ ball (0 : ℂ) R, HasDerivAt P (preSchwarzian f w) w) ∧
      ∀ w ∈ ball (0 : ℂ) R, w ≠ 0 → HasDerivAt Q (preSchwarzian f w - 2 * deriv f w / f w + 2 / w) w := by
  have hR0 : (0 : ℂ) ∈ ball (0 : ℂ) R := mem_ball_self (by linarith)
  have hn : ball (0 : ℂ) R ∈ 𝓝 0 := isOpen_ball.mem_nhds hR0
  have hf' : DifferentiableOn ℂ (deriv f) (ball 0 R) := (hf.analyticOnNhd isOpen_ball).deriv.differentiableOn
  have hf'' : DifferentiableOn ℂ (deriv (deriv f)) (ball 0 R) :=
    (hf'.analyticOnNhd isOpen_ball).deriv.differentiableOn
  have hf'ne : ∀ w ∈ ball (0 : ℂ) R, deriv f w ≠ 0 := fun w hw => deriv_ne_zero_of_injOn isOpen_ball hf hfi hw
  have hA : DifferentiableOn ℂ (preSchwarzian f) (ball 0 R) := hf''.div hf' hf'ne
  set q : ℂ → ℂ := dslope f 0 with hq_def
  have hq : DifferentiableOn ℂ q (ball 0 R) := (differentiableOn_dslope hn).mpr hf
  have hq' : DifferentiableOn ℂ (deriv q) (ball 0 R) := (hq.analyticOnNhd isOpen_ball).deriv.differentiableOn
  have hfe : ∀ w, f w = w * q w := fun w => by
    have := sub_smul_dslope f 0 w
    rw [smul_eq_mul, hf0, sub_zero, sub_zero] at this
    exact this.symm
  have hqne : ∀ w ∈ ball (0 : ℂ) R, q w ≠ 0 := by
    intro w hw
    by_cases hw0 : w = 0
    · rw [hw0, hq_def, dslope_same]; exact hf'ne 0 hR0
    · rw [hq_def, dslope_of_ne f hw0, slope_def_field, hf0, sub_zero, sub_zero]
      exact div_ne_zero (fun h => hw0 (hfi hw hR0 (h.trans hf0.symm))) hw0
  have hh : DifferentiableOn ℂ (fun w => preSchwarzian f w - 2 * (deriv q w / q w)) (ball 0 R) :=
    hA.sub ((differentiableOn_const _).mul (hq'.div hq hqne))
  obtain ⟨P, hP⟩ := hA.isExactOn_ball
  obtain ⟨Q, hQ⟩ := hh.isExactOn_ball
  refine ⟨P, Q, fun w hw => (hP w hw).differentiableAt.differentiableWithinAt,
    fun w hw => (hQ w hw).differentiableAt.differentiableWithinAt, hP, ?_⟩
  intro w hw hw0
  convert hQ w hw using 1
  have hqw : HasDerivAt q (deriv q w) w := (hq.differentiableAt (isOpen_ball.mem_nhds hw)).hasDerivAt
  have hF : f = fun w => w * q w := funext hfe
  have hdf : deriv f w = q w + w * deriv q w := by
    conv_lhs => rw [hF]
    have hd : HasDerivAt (fun w => w * q w) ((1 : ℂ) * q w + w * deriv q w) w := (hasDerivAt_id w).mul hqw
    rw [hd.deriv]; ring
  rw [hdf, hfe w]
  have := hqne w hw
  field_simp
  ring

/-- The welding `γ = g⁻¹ ∘ f` near `S¹`: holomorphic on an annulus `a < |w| < b`, `g ∘ γ = f` there, `γ` maps into
`|ξ| > r'` and maps `S¹` into `S¹`. -/
theorem s36l_sp_weld {f g : ℂ → ℂ} {R r r' : ℝ} (hR : 1 < R) (hr : r ≤ r') (hr' : r' < 1)
    (hf : DifferentiableOn ℂ f (ball 0 R)) (hfi : InjOn f (ball 0 R))
    (hg : DifferentiableOn ℂ g {w | r < ‖w‖}) (hgi : InjOn g {w | r < ‖w‖})
    (hginf : Tendsto g (cocompact ℂ) (cocompact ℂ))
    (hc : g '' unitDiscExterior = (f '' closedBall 0 1)ᶜ) :
    ∃ γ : ℂ → ℂ, ∃ a b : ℝ, a < 1 ∧ 1 < b ∧ b ≤ R ∧
      DifferentiableOn ℂ γ {w | a < ‖w‖ ∧ ‖w‖ < b} ∧
      (∀ w : ℂ, a < ‖w‖ → ‖w‖ < b → r' < ‖γ w‖ ∧ g (γ w) = f w) ∧
      ∀ w : ℂ, ‖w‖ = 1 → ‖γ w‖ = 1 := by
  set E : Set ℂ := {w | r < ‖w‖} with hE_def
  have hEo : IsOpen E := isOpen_lt continuous_const continuous_norm
  have hconf : IsConformalOnto g E (g '' E) := ⟨hg, hgi, rfl⟩
  have hgEo : IsOpen (g '' E) := hconf.isOpen hEo
  set Ψ : ℂ → ℂ := Function.invFunOn g E with hΨ
  have hΨd : DifferentiableOn ℂ Ψ (g '' E) := (hconf.symm hEo).1
  have hcb : closedBall (0 : ℂ) 1 ⊆ ball 0 R := fun w hw =>
    mem_ball_zero_iff.mpr (lt_of_le_of_lt (mem_closedBall_zero_iff.mp hw) hR)
  -- every boundary value `f(w)`, `|w| = 1`, is `g(ξ)` with `|ξ| = 1`
  have hK : ∀ w : ℂ, ‖w‖ = 1 → ∃ ξ : ℂ, ‖ξ‖ = 1 ∧ g ξ = f w := by
    intro w hw
    have hwB : w ∈ ball (0 : ℂ) R := hcb (by simp [hw])
    set t : ℕ → ℝ := fun n => 1 + (R - 1) / (n + 2) with ht
    have ht1 : ∀ n, 1 < t n := by
      intro n
      simp only [ht]
      have : 0 < (R - 1) / ((n : ℝ) + 2) := div_pos (by linarith) (by positivity)
      linarith
    have htR : ∀ n, t n < R := fun n => by
      simp only [ht]
      have h2 : (1 : ℝ) < (n : ℝ) + 2 := by have := (Nat.cast_nonneg n : (0 : ℝ) ≤ n); linarith
      have : (R - 1) / ((n : ℝ) + 2) < R - 1 := div_lt_self (by linarith) h2
      linarith
    have httend : Tendsto t atTop (𝓝 1) := by
      have : Tendsto (fun n : ℕ => (R - 1) / ((n : ℝ) + 2)) atTop (𝓝 0) := by
        apply Tendsto.div_atTop tendsto_const_nhds
        exact tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop
      simpa [ht] using this.const_add 1
    set wn : ℕ → ℂ := fun n => (t n : ℂ) * w with hwn
    have hwnn : ∀ n, ‖wn n‖ = t n := fun n => by
      simp only [hwn, norm_mul, Complex.norm_real, hw, mul_one]
      exact Real.norm_of_nonneg (by linarith [ht1 n])
    have hwnB : ∀ n, wn n ∈ ball (0 : ℂ) R := fun n => mem_ball_zero_iff.mpr (by rw [hwnn]; exact htR n)
    have hwntend : Tendsto wn atTop (𝓝 w) := by
      have := (Complex.continuous_ofReal.tendsto 1).comp httend
      simpa [hwn] using this.mul_const w
    have hfc : ContinuousAt f w := (hf w hwB).differentiableAt (isOpen_ball.mem_nhds hwB) |>.continuousAt
    have hfn : Tendsto (fun n => f (wn n)) atTop (𝓝 (f w)) := hfc.tendsto.comp hwntend
    have hex : ∀ n, ∃ ξ ∈ unitDiscExterior, g ξ = f (wn n) := by
      intro n
      have : f (wn n) ∈ (f '' closedBall 0 1)ᶜ := by
        rintro ⟨v, hv, hfv⟩
        have := hfi (hcb hv) (hwnB n) hfv
        rw [this, mem_closedBall_zero_iff, hwnn] at hv
        linarith [ht1 n]
      rw [← hc] at this
      obtain ⟨ξ, hξ, hgξ⟩ := this
      exact ⟨ξ, hξ, hgξ⟩
    choose ξ hξ hgξ using hex
    -- the `ξₙ` stay in a compact set
    obtain ⟨C, hC, hCs⟩ := mem_cocompact.mp (hginf ((isCompact_closedBall (f w) 1).compl_mem_cocompact))
    have hev : ∀ᶠ n in atTop, ξ n ∈ C := by
      filter_upwards [hfn.eventually (Metric.closedBall_mem_nhds (f w) one_pos)] with n hn
      by_contra hnC
      have := hCs hnC
      exact this (by rw [hgξ n]; exact hn)
    obtain ⟨N, hN⟩ := eventually_atTop.mp hev
    obtain ⟨ξs, hξsC, φ, hφ, hφt⟩ := hC.tendsto_subseq (x := fun m => ξ (m + N)) fun m => hN _ (by omega)
    have hξs1 : 1 ≤ ‖ξs‖ := by
      have hcl : IsClosed {v : ℂ | 1 ≤ ‖v‖} := isClosed_le continuous_const continuous_norm
      exact hcl.mem_of_tendsto hφt (Eventually.of_forall fun m => le_of_lt (show 1 < ‖ξ (φ m + N)‖ from hξ _))
    have hξsE : r < ‖ξs‖ := by linarith
    have hgc : ContinuousAt g ξs := (hg ξs hξsE).differentiableAt (hEo.mem_nhds hξsE) |>.continuousAt
    have hlim1 : Tendsto (fun m => g (ξ (φ m + N))) atTop (𝓝 (g ξs)) := hgc.tendsto.comp hφt
    have hlim2 : Tendsto (fun m => g (ξ (φ m + N))) atTop (𝓝 (f w)) := by
      simp only [hgξ]
      exact hfn.comp ((tendsto_add_atTop_nat N).comp hφ.tendsto_atTop)
    have hgs : g ξs = f w := tendsto_nhds_unique hlim1 hlim2
    refine ⟨ξs, le_antisymm (not_lt.mp fun h => ?_) hξs1, hgs⟩
    have : f w ∈ g '' unitDiscExterior := ⟨ξs, h, hgs⟩
    rw [hc] at this
    exact this ⟨w, by simp [hw], rfl⟩
  set γ : ℂ → ℂ := fun w => Ψ (f w) with hγ_def
  have hγS : ∀ w : ℂ, ‖w‖ = 1 → ‖γ w‖ = 1 ∧ f w ∈ g '' E := by
    intro w hw
    obtain ⟨ξ, hξ1, hgξ⟩ := hK w hw
    have hξE : ξ ∈ E := by show r < ‖ξ‖; rw [hξ1]; linarith
    refine ⟨?_, ⟨ξ, hξE, hgξ⟩⟩
    simp only [hγ_def, hΨ, ← hgξ, hgi.leftInvOn_invFunOn hξE, hξ1]
  set U : Set ℂ := ball 0 R ∩ f ⁻¹' (g '' E) with hU_def
  have hUo : IsOpen U := hf.continuousOn.isOpen_inter_preimage isOpen_ball hgEo
  have hγU : ∀ w ∈ U, DifferentiableAt ℂ γ w := fun w hw =>
    ((hΨd _ hw.2).differentiableAt (hgEo.mem_nhds hw.2)).comp w
      ((hf w hw.1).differentiableAt (isOpen_ball.mem_nhds hw.1))
  have hγc : ContinuousOn γ U := fun w hw => (hγU w hw).continuousAt.continuousWithinAt
  set O : Set ℂ := U ∩ γ ⁻¹' {v | r' < ‖v‖} with hO_def
  have hOo : IsOpen O := hγc.isOpen_inter_preimage hUo (isOpen_lt continuous_const continuous_norm)
  have hsO : sphere (0 : ℂ) 1 ⊆ O := by
    intro w hw
    have hw1 : ‖w‖ = 1 := by simpa using hw
    obtain ⟨h1, h2⟩ := hγS w hw1
    exact ⟨⟨hcb (sphere_subset_closedBall hw), h2⟩, by show r' < ‖γ w‖; rw [h1]; exact hr'⟩
  obtain ⟨δ, hδ, hδO⟩ := (isCompact_sphere (0 : ℂ) 1).exists_cthickening_subset_open hOo hsO
  set a : ℝ := max (1 - δ / 2) (1 / 2) with ha_def
  set b : ℝ := min (1 + δ / 2) ((1 + R) / 2) with hb_def
  have hann : ∀ w : ℂ, a < ‖w‖ → ‖w‖ < b → w ∈ O := by
    intro w h1 h2
    have hw12 : 1 / 2 < ‖w‖ := lt_of_le_of_lt (le_max_right _ _) h1
    have hwl : 1 - δ / 2 < ‖w‖ := lt_of_le_of_lt (le_max_left _ _) h1
    have hwu : ‖w‖ < 1 + δ / 2 := lt_of_lt_of_le h2 (min_le_left _ _)
    have hw0 : 0 < ‖w‖ := by linarith
    set v : ℂ := ((‖w‖⁻¹ : ℝ) : ℂ) * w with hv
    have hvs : v ∈ sphere (0 : ℂ) 1 := by
      rw [mem_sphere_zero_iff_norm, hv, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
      field_simp
    have hdist : dist w v ≤ δ := by
      rw [dist_eq_norm, hv, show w - ((‖w‖⁻¹ : ℝ) : ℂ) * w = ((1 - ‖w‖⁻¹ : ℝ) : ℂ) * w by push_cast; ring,
        norm_mul, Complex.norm_real, Real.norm_eq_abs]
      have : |1 - ‖w‖⁻¹| * ‖w‖ = |‖w‖ - 1| := by
        rw [← abs_of_pos hw0, ← abs_mul, abs_of_pos hw0]
        congr 1; field_simp
      rw [this, abs_le]
      constructor <;> linarith
    exact hδO (Metric.mem_cthickening_of_dist_le w v δ _ hvs hdist)
  refine ⟨γ, a, b, max_lt (by linarith) (by norm_num), lt_min (by linarith) (by linarith),
    (min_le_right _ _).trans (by linarith), ?_, ?_, fun w hw => (hγS w hw).1⟩
  · intro w hw
    exact (hγU w (hann w hw.1 hw.2).1).differentiableWithinAt
  · intro w h1 h2
    have hwO := hann w h1 h2
    refine ⟨hwO.2, ?_⟩
    exact Function.invFunOn_eq hwO.1.2

/-- Change of variables in a circle integral along a `C¹` self-map of `S¹` (degree `k`). -/
theorem s36l_sp_subst {γ : ℂ → ℂ} {a b : ℝ} (ha : a < 1) (hb : 1 < b)
    (hγ : DifferentiableOn ℂ γ {w | a < ‖w‖ ∧ ‖w‖ < b}) (hS : ∀ w : ℂ, ‖w‖ = 1 → ‖γ w‖ = 1) :
    ∃ k : ℤ, ∀ Ψ : ℂ → ℂ, ContinuousOn Ψ (sphere 0 1) →
      (∮ w in C(0, 1), Ψ (γ w) * deriv γ w) = (k : ℂ) * ∮ w in C(0, 1), Ψ w := by
  set A : Set ℂ := {w | a < ‖w‖ ∧ ‖w‖ < b} with hA
  have hAo : IsOpen A :=
    (isOpen_lt continuous_const continuous_norm).inter (isOpen_lt continuous_norm continuous_const)
  set e : ℝ → ℂ := circleMap 0 1 with he
  have heA : ∀ θ, e θ ∈ A := fun θ => by
    have : ‖e θ‖ = 1 := by simp [he]
    exact ⟨by rw [this]; exact ha, by rw [this]; exact hb⟩
  have hγ' : ContinuousOn (deriv γ) A := (hγ.analyticOnNhd hAo).deriv.continuousOn
  set c : ℝ → ℂ := fun θ => γ (e θ) with hc
  set c' : ℝ → ℂ := fun θ => deriv γ (e θ) * (e θ * I) with hc'
  have hcd : ∀ θ, HasDerivAt c (c' θ) θ := by
    intro θ
    have h1 : HasDerivAt γ (deriv γ (e θ)) (e θ) :=
      ((hγ _ (heA θ)).differentiableAt (hAo.mem_nhds (heA θ))).hasDerivAt
    have h2 : HasDerivAt e (e θ * I) θ := by
      have := hasDerivAt_circleMap (0 : ℂ) 1 θ
      simpa [he, circleMap_zero] using this
    exact h1.comp θ h2
  have hc1 : ∀ θ, ‖c θ‖ = 1 := fun θ => hS _ (by simp [he])
  have hc0 : ∀ θ, c θ ≠ 0 := fun θ h => by have := hc1 θ; rw [h, norm_zero] at this; norm_num at this
  have hecont : Continuous e := continuous_circleMap 0 1
  have hc'cont : Continuous c' :=
    (hγ'.comp_continuous hecont heA).mul (hecont.mul continuous_const)
  have hccont : Continuous c := continuous_iff_continuousAt.mpr fun θ => (hcd θ).continuousAt
  have hq : Continuous fun θ => c' θ / c θ := hc'cont.div hccont hc0
  set L : ℝ → ℂ := fun θ => ∫ s in (0 : ℝ)..θ, c' s / c s with hL
  have hLd : ∀ θ, HasDerivAt L (c' θ / c θ) θ := fun θ => (hq.integral_hasStrictDerivAt 0 θ).hasDerivAt
  have hL0 : L 0 = 0 := by simp [hL]
  -- `c = c 0 · exp L`
  have hcL : ∀ θ, c θ = c 0 * exp (L θ) := by
    have hd : ∀ θ, HasDerivAt (fun θ => c θ * exp (-L θ)) 0 θ := by
      intro θ
      have := (hcd θ).mul ((hLd θ).neg.cexp)
      convert this using 1
      field_simp [hc0 θ]
      ring
    intro θ
    have h := is_const_of_deriv_eq_zero (fun θ => (hd θ).differentiableAt) (fun θ => (hd θ).deriv) θ 0
    simp only [hL0, neg_zero, Complex.exp_zero, mul_one] at h
    rw [← h, mul_assoc, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero, mul_one]
  -- `Re L = 0`
  have hLre : ∀ θ, (L θ).re = 0 := by
    intro θ
    have h := congrArg norm (hcL θ)
    rw [hc1, norm_mul, hc1, one_mul, Complex.norm_exp] at h
    have := Real.exp_eq_one_iff (L θ).re |>.mp h.symm
    exact this
  set φ : ℝ → ℝ := fun θ => (L θ).im with hφ
  have hLφ : ∀ θ, L θ = (φ θ : ℂ) * I := fun θ => by
    apply Complex.ext <;> simp [hφ, hLre θ]
  have hφd : ∀ θ, HasDerivAt φ ((c' θ / c θ).im) θ := fun θ =>
    (Complex.imCLM.hasFDerivAt.comp_hasDerivAt θ (hLd θ))
  have hreq : ∀ θ, (c' θ / c θ).re = 0 := by
    intro θ
    have h1 : HasDerivAt (fun θ => (L θ).re) ((c' θ / c θ).re) θ :=
      Complex.reCLM.hasFDerivAt.comp_hasDerivAt θ (hLd θ)
    have h2 : HasDerivAt (fun θ => (L θ).re) 0 θ := by
      have : (fun θ => (L θ).re) = fun _ => (0 : ℝ) := funext hLre
      rw [this]; exact hasDerivAt_const θ 0
    exact h1.unique h2
  have hc'eq : ∀ θ, c' θ = c θ * (((c' θ / c θ).im : ℂ) * I) := by
    intro θ
    have : c' θ / c θ = (((c' θ / c θ).im : ℂ) * I) := by
      apply Complex.ext <;> simp [hreq θ]
    rw [← this, mul_div_cancel₀ _ (hc0 θ)]
  -- `c 0 = exp(α I)`
  set α : ℝ := Complex.arg (c 0) with hα
  have hc0α : c 0 = exp (α * I) := by
    have := Complex.norm_mul_exp_arg_mul_I (c 0)
    rw [hc1 0, Complex.ofReal_one, one_mul] at this
    exact this.symm
  -- `φ(2π) = 2πn`
  have hper : c (2 * π) = c 0 := by simp only [hc, he, (periodic_circleMap 0 1) 0 |>.symm, zero_add]
  obtain ⟨n, hn⟩ : ∃ n : ℤ, φ (2 * π) = n * (2 * π) := by
    have h := hcL (2 * π)
    rw [hper] at h
    have h1 : exp (L (2 * π)) = 1 := by
      have := hc0 0
      field_simp at h
      exact h.symm
    obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp h1
    refine ⟨n, ?_⟩
    rw [hLφ] at hn
    have := congrArg Complex.im hn
    simpa using this
  refine ⟨n, fun Ψ hΨ => ?_⟩
  set F : ℝ → ℂ := fun s => deriv (circleMap 0 1) s • Ψ (circleMap 0 1 s) with hF
  have hFc : Continuous F := by
    have hΨc : Continuous fun s => Ψ (circleMap 0 1 s) :=
      hΨ.comp_continuous (continuous_circleMap 0 1) fun s => circleMap_mem_sphere 0 zero_le_one s
    simp only [hF, deriv_circleMap, smul_eq_mul]
    exact ((continuous_circleMap 0 1).mul continuous_const).mul hΨc
  have hFp : Function.Periodic F (2 * π) := by
    intro s
    simp only [hF, deriv_circleMap, (periodic_circleMap 0 1) s]
  set φ' : ℝ → ℝ := fun θ => (c' θ / c θ).im with hφ'
  have hφ'c : Continuous φ' := Complex.continuous_im.comp hq
  have hpt : ∀ θ, deriv (circleMap 0 1) θ • (Ψ (γ (circleMap 0 1 θ)) * deriv γ (circleMap 0 1 θ)) =
      φ' θ • F (φ θ + α) := by
    intro θ
    have hcm : circleMap 0 1 (φ θ + α) = c θ := by
      rw [circleMap_zero, Complex.ofReal_one, one_mul, hcL θ, hc0α, hLφ θ, ← Complex.exp_add]
      congr 1; push_cast; ring
    simp only [hF, deriv_circleMap, smul_eq_mul, hcm, Complex.real_smul]
    have := hc'eq θ
    simp only [hc'] at this
    have e2 : circleMap 0 1 θ = e θ := rfl
    rw [e2]
    calc e θ * I * (Ψ (γ (e θ)) * deriv γ (e θ)) = (deriv γ (e θ) * (e θ * I)) * Ψ (c θ) := by
          simp only [hc]; ring
      _ = c θ * (((c' θ / c θ).im : ℂ) * I) * Ψ (c θ) := by rw [← this]
      _ = _ := by simp only [hφ']; ring
  calc (∮ w in C(0, 1), Ψ (γ w) * deriv γ w)
      = ∫ θ in (0 : ℝ)..2 * π, φ' θ • (fun s => F (s + α)) (φ θ) := by
        unfold circleIntegral
        exact intervalIntegral.integral_congr fun θ _ => hpt θ
    _ = ∫ s in φ 0..φ (2 * π), F (s + α) :=
        intervalIntegral.integral_deriv_smul_comp (fun θ _ => hφd θ) hφ'c.continuousOn
          (hFc.comp (continuous_id.add continuous_const))
    _ = ∫ s in α..α + n • (2 * π), F s := by
        rw [intervalIntegral.integral_comp_add_right, hn, show φ 0 = 0 by simp [hφ, hL0], zero_add, zsmul_eq_mul,
          add_comm]
    _ = n • ∫ s in α..α + 2 * π, F s :=
        hFp.intervalIntegral_add_zsmul_eq n α fun t₁ t₂ => hFc.intervalIntegrable t₁ t₂
    _ = (n : ℂ) * ∮ w in C(0, 1), Ψ w := by
        rw [hFp.intervalIntegral_add_eq α 0, zero_add, zsmul_eq_mul]
        rfl

/-- Winding of `f(S¹)` around `f(z)`. -/
theorem s36l_sp_windD {f : ℂ → ℂ} {R : ℝ} (hR : 1 < R)
    (hf : DifferentiableOn ℂ f (ball 0 R)) (hfi : InjOn f (ball 0 R)) {z : ℂ} (hz : z ∈ unitDisc) :
    (∮ w in C(0, 1), deriv f w / (f w - f z)) = 2 * π * I := by
  have hzR : z ∈ ball (0 : ℂ) R := mem_ball_zero_iff.mpr (lt_trans (mem_ball_zero_iff.mp hz) hR)
  have hzn : ball (0 : ℂ) R ∈ 𝓝 z := isOpen_ball.mem_nhds hzR
  set q : ℂ → ℂ := dslope f z with hq_def
  have hq : DifferentiableOn ℂ q (ball 0 R) := (differentiableOn_dslope hzn).mpr hf
  have hq' : DifferentiableOn ℂ (deriv q) (ball 0 R) := (hq.analyticOnNhd isOpen_ball).deriv.differentiableOn
  have hfe : ∀ w, f w = f z + (w - z) * q w := fun w => by
    have := sub_smul_dslope f z w
    rw [smul_eq_mul] at this
    rw [this]; ring
  have hF : f = fun w => f z + (w - z) * q w := funext hfe
  have hqne : ∀ w ∈ ball (0 : ℂ) R, q w ≠ 0 := by
    intro w hw
    by_cases hwz : w = z
    · rw [hwz, hq_def, dslope_same]
      exact deriv_ne_zero_of_injOn isOpen_ball hf hfi hzR
    · rw [hq_def, dslope_of_ne f hwz, slope_def_field]
      exact div_ne_zero (sub_ne_zero.mpr fun h => hwz (hfi hw hzR h)) (sub_ne_zero.mpr hwz)
  have hcb : closedBall (0 : ℂ) 1 ⊆ ball 0 R := fun w hw =>
    mem_ball_zero_iff.mpr (lt_of_le_of_lt (mem_closedBall_zero_iff.mp hw) hR)
  have hz1 : ‖z‖ < 1 := mem_ball_zero_iff.mp hz
  have heq : EqOn (fun w => deriv f w / (f w - f z)) (fun w => (w - z)⁻¹ + deriv q w / q w) (sphere 0 1) := by
    intro w hw
    have hw1 : ‖w‖ = 1 := by simpa using hw
    have hwB : w ∈ ball (0 : ℂ) R := hcb (sphere_subset_closedBall hw)
    have hwz : w - z ≠ 0 := fun h => by rw [sub_eq_zero] at h; rw [h] at hw1; linarith
    have hqw : HasDerivAt q (deriv q w) w := (hq.differentiableAt (isOpen_ball.mem_nhds hwB)).hasDerivAt
    have hd : HasDerivAt (fun w => f z + (w - z) * q w) ((1 : ℂ) * q w + (w - z) * deriv q w) w :=
      (((hasDerivAt_id w).sub_const z).mul hqw).const_add (f z)
    have hdf : deriv f w = q w + (w - z) * deriv q w := by
      conv_lhs => rw [hF]
      rw [hd.deriv]; ring
    simp only
    rw [hdf, hfe w, add_sub_cancel_left]
    have := hqne w hwB
    field_simp
  rw [circleIntegral.integral_congr zero_le_one heq]
  have hc1 : ContinuousOn (fun w : ℂ => (w - z)⁻¹) (sphere 0 1) := fun w hw => by
    have hw1 : ‖w‖ = 1 := by simpa using hw
    have hne : w - z ≠ 0 := fun h => by rw [sub_eq_zero] at h; rw [h] at hw1; linarith
    exact ((continuousAt_id.sub continuousAt_const).inv₀ hne).continuousWithinAt
  have hd2 : DifferentiableOn ℂ (fun w => deriv q w / q w) (ball 0 R) := hq'.div hq hqne
  have e := circleIntegral.integral_add (c := 0) (R := 1) (f := fun w : ℂ => (w - z)⁻¹)
    (g := fun w => deriv q w / q w) (hc1.circleIntegrable zero_le_one)
    ((hd2.continuousOn.mono (sphere_subset_closedBall.trans hcb)).circleIntegrable zero_le_one)
  beta_reduce at e
  rw [e, circleIntegral.integral_sub_inv_of_mem_ball (by simpa using hz1),
    circleIntegral_eq_zero_of_differentiable_on_off_countable zero_le_one countable_empty
      (hd2.continuousOn.mono hcb) fun w hw => (hd2 w (hcb (ball_subset_closedBall hw.1))).differentiableAt
        (isOpen_ball.mem_nhds (hcb (ball_subset_closedBall hw.1))), add_zero]

/-- Inversion of the unit circle in a circle integral: `∮ F(w) dw = ∮ F(1/u) u⁻² du`. -/
theorem s36l_sp_circ_inv (F : ℂ → ℂ) :
    (∮ w in C(0, 1), F w) = ∮ u in C(0, 1), F u⁻¹ * (u⁻¹) ^ 2 := by
  have hcm : ∀ θ : ℝ, circleMap 0 1 (2 * π - θ) = (circleMap 0 1 θ)⁻¹ := by
    intro θ
    simp only [circleMap_zero, Complex.ofReal_one, one_mul, Complex.ofReal_sub, Complex.ofReal_mul,
      Complex.ofReal_ofNat]
    rw [← Complex.exp_neg, sub_mul, Complex.exp_sub, show (2 * (π : ℂ)) * I = 2 * π * I by ring,
      Complex.exp_two_pi_mul_I, one_div, ← Complex.exp_neg]
  unfold circleIntegral
  have h := intervalIntegral.integral_comp_sub_left
    (fun θ => deriv (circleMap 0 1) θ • F (circleMap 0 1 θ)) (2 * π) (a := 0) (b := 2 * π)
  simp only [sub_self, sub_zero] at h
  rw [← h]
  refine intervalIntegral.integral_congr fun θ _ => ?_
  simp only [deriv_circleMap, smul_eq_mul, hcm]
  have hne : circleMap 0 1 θ ≠ 0 := by simp [circleMap_zero, Complex.exp_ne_zero]
  field_simp

/-- The inverted exterior map: `G(u) = 1/g(1/u)` extends holomorphically and injectively to `|u| < 1/s`, `G(0) = 0`. -/
theorem s36l_sp_inv {g : ℂ → ℂ} {s : ℝ} (hs : 0 < s) (hg : DifferentiableOn ℂ g {w | s < ‖w‖})
    (hgi : InjOn g {w | s < ‖w‖}) (hginf : Tendsto g (cocompact ℂ) (cocompact ℂ))
    (hg0 : ∀ w : ℂ, s < ‖w‖ → g w ≠ 0) :
    ∃ G : ℂ → ℂ, DifferentiableOn ℂ G (ball 0 s⁻¹) ∧ InjOn G (ball 0 s⁻¹) ∧ G 0 = 0 ∧
      ∀ u : ℂ, u ≠ 0 → ‖u‖ < s⁻¹ → G u = (g u⁻¹)⁻¹ := by
  set G : ℂ → ℂ := fun u => if u = 0 then 0 else (g u⁻¹)⁻¹ with hG
  have hmem : ∀ u : ℂ, u ≠ 0 → ‖u‖ < s⁻¹ → s < ‖u⁻¹‖ := by
    intro u hu hus
    rw [norm_inv]
    have hu0 : 0 < ‖u‖ := norm_pos_iff.mpr hu
    rw [lt_inv_comm₀ hs hu0]; exact hus
  have hE : IsOpen {w : ℂ | s < ‖w‖} := isOpen_lt continuous_const continuous_norm
  have hdiff : ∀ u : ℂ, u ≠ 0 → ‖u‖ < s⁻¹ → DifferentiableAt ℂ G u := by
    intro u hu hus
    have hw := hmem u hu hus
    have hgd : DifferentiableAt ℂ g u⁻¹ := (hg _ hw).differentiableAt (hE.mem_nhds hw)
    have hH : DifferentiableAt ℂ (fun u => (g u⁻¹)⁻¹) u :=
      (hgd.comp u (differentiableAt_inv hu)).inv (hg0 _ hw)
    refine hH.congr_of_eventuallyEq ?_
    filter_upwards [eventually_ne_nhds hu] with v hv
    simp [hG, hv]
  have hlim : Tendsto G (𝓝[≠] 0) (𝓝 0) := by
    have h1 : Tendsto (fun u : ℂ => (g u⁻¹)⁻¹) (𝓝[≠] 0) (𝓝 0) := by
      have hi : Tendsto (fun u : ℂ => u⁻¹) (𝓝[≠] 0) (cocompact ℂ) :=
        Metric.cobounded_eq_cocompact (α := ℂ) ▸ tendsto_inv₀_nhdsNE_zero
      exact (Metric.cobounded_eq_cocompact (α := ℂ) ▸ tendsto_inv₀_cobounded).comp (hginf.comp hi)
    refine h1.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with u hu
    simp [hG, show u ≠ 0 from hu]
  have hcont : ContinuousAt G 0 := by
    rw [← continuousWithinAt_compl_self]
    have : G 0 = 0 := by simp [hG]
    rw [ContinuousWithinAt, this]
    exact hlim
  have hB : ball (0 : ℂ) s⁻¹ ∈ 𝓝 (0 : ℂ) := isOpen_ball.mem_nhds (mem_ball_self (inv_pos.mpr hs))
  refine ⟨G, ?_, ?_, by simp [hG], fun u hu hus => by simp [hG, hu]⟩
  · refine (differentiableOn_compl_singleton_and_continuousAt_iff hB).mp ⟨?_, hcont⟩
    intro u hu
    exact (hdiff u hu.2 (mem_ball_zero_iff.mp hu.1)).differentiableWithinAt
  · intro u hu v hv huv
    have hu' := mem_ball_zero_iff.mp hu
    have hv' := mem_ball_zero_iff.mp hv
    by_cases hu0 : u = 0 <;> by_cases hv0 : v = 0
    · rw [hu0, hv0]
    · exfalso
      simp only [hG, hu0, hv0, if_true, if_false] at huv
      exact hg0 _ (hmem v hv0 hv') (inv_eq_zero.mp huv.symm)
    · exfalso
      simp only [hG, hu0, hv0, if_true, if_false] at huv
      exact hg0 _ (hmem u hu0 hu') (inv_eq_zero.mp huv)
    · simp only [hG, hu0, hv0, if_false] at huv
      have := hgi (hmem u hu0 hu') (hmem v hv0 hv') (inv_injective huv)
      exact inv_injective this

/-- Derivative of the inverted map: `g'(1/u) u⁻² = G'(u)/G(u)²`. -/
theorem s36l_sp_inv_deriv {g G : ℂ → ℂ} {s : ℝ} (hs : 0 < s) (hg : DifferentiableOn ℂ g {w | s < ‖w‖})
    (hg0 : ∀ w : ℂ, s < ‖w‖ → g w ≠ 0)
    (hGe : ∀ u : ℂ, u ≠ 0 → ‖u‖ < s⁻¹ → G u = (g u⁻¹)⁻¹) {u : ℂ} (hu : u ≠ 0) (hus : ‖u‖ < s⁻¹) :
    deriv g u⁻¹ * (u⁻¹) ^ 2 = deriv G u / G u ^ 2 := by
  have hw : s < ‖u⁻¹‖ := by
    rw [norm_inv, lt_inv_comm₀ hs (norm_pos_iff.mpr hu)]; exact hus
  have hE : IsOpen {w : ℂ | s < ‖w‖} := isOpen_lt continuous_const continuous_norm
  have hgd : HasDerivAt g (deriv g u⁻¹) u⁻¹ := ((hg _ hw).differentiableAt (hE.mem_nhds hw)).hasDerivAt
  have h1 : HasDerivAt (fun v => g v⁻¹) (deriv g u⁻¹ * -(u ^ 2)⁻¹) u := by
    have := hgd.comp u (hasDerivAt_inv hu)
    simpa [Function.comp_def] using this
  have h2 : HasDerivAt (fun v => (g v⁻¹)⁻¹) (-(deriv g u⁻¹ * -(u ^ 2)⁻¹) / g u⁻¹ ^ 2) u := h1.inv (hg0 _ hw)
  have hev : G =ᶠ[𝓝 u] fun v => (g v⁻¹)⁻¹ := by
    have hB : IsOpen (ball (0 : ℂ) s⁻¹ \ {0}) := isOpen_ball.sdiff isClosed_singleton
    filter_upwards [hB.mem_nhds ⟨mem_ball_zero_iff.mpr hus, hu⟩] with v hv
    exact hGe v hv.2 (mem_ball_zero_iff.mp hv.1)
  rw [hev.deriv_eq, h2.deriv, hGe u hu hus]
  have ha := hg0 _ hw
  generalize g u⁻¹ = a at ha ⊢
  generalize deriv g u⁻¹ = d
  have ha2 : a ^ 2 ≠ 0 := pow_ne_zero 2 ha
  rw [inv_pow, inv_pow, mul_neg, neg_neg, div_inv_eq_mul, div_mul_cancel₀ _ ha2]

/-- A holomorphic function on `|w| > r'`, bounded near `∞`, inverts to a holomorphic function on a disc `|u| < ρ`,
`ρ > 1` (removable singularity at `0`). -/
theorem s36l_sp_remove {Q : ℂ → ℂ} {r' : ℝ} (hr0 : 0 < r') (hr' : r' < 1)
    (hQ : DifferentiableOn ℂ Q {w | r' < ‖w‖}) {C : ℝ} (hC : ∀ w : ℂ, 2 ≤ ‖w‖ → ‖Q w‖ ≤ C) :
    ∃ ρ : ℝ, 1 < ρ ∧ ρ < r'⁻¹ ∧ ∃ Q' : ℂ → ℂ, DifferentiableOn ℂ Q' (ball 0 ρ) ∧
      ∀ u : ℂ, u ≠ 0 → ‖u‖ < ρ → Q' u = Q u⁻¹ := by
  have h1 : 1 < r'⁻¹ := one_lt_inv₀ hr0 |>.mpr hr'
  set ρ : ℝ := (1 + r'⁻¹) / 2 with hρ
  have hρ1 : 1 < ρ := by rw [hρ]; linarith
  have hρ2 : ρ < r'⁻¹ := by rw [hρ]; linarith
  have hρ0 : 0 < ρ := by linarith
  have hmem : ∀ u : ℂ, u ≠ 0 → ‖u‖ < ρ → r' < ‖u⁻¹‖ := by
    intro u hu hus
    rw [norm_inv, lt_inv_comm₀ hr0 (norm_pos_iff.mpr hu)]; linarith
  have hE : IsOpen {w : ℂ | r' < ‖w‖} := isOpen_lt continuous_const continuous_norm
  have hd : DifferentiableOn ℂ (fun u => Q u⁻¹) (ball 0 ρ \ {0}) := by
    intro u hu
    have hu0 : u ≠ 0 := hu.2
    have hw := hmem u hu0 (mem_ball_zero_iff.mp hu.1)
    exact (((hQ _ hw).differentiableAt (hE.mem_nhds hw)).comp u (differentiableAt_inv hu0)).differentiableWithinAt
  set K : Set ℂ := {w : ℂ | ρ⁻¹ ≤ ‖w‖ ∧ ‖w‖ ≤ 2} with hK
  have hKc : IsCompact K := by
    refine Metric.isCompact_of_isClosed_isBounded ?_ ?_
    · exact (isClosed_le continuous_const continuous_norm).inter (isClosed_le continuous_norm continuous_const)
    · exact (Metric.isBounded_closedBall (x := (0 : ℂ)) (r := 2)).subset fun w hw => by
        simpa using hw.2
  have hKE : K ⊆ {w : ℂ | r' < ‖w‖} := fun w hw => by
    show r' < ‖w‖
    have : r' < ρ⁻¹ := by rw [lt_inv_comm₀ hr0 hρ0]; exact hρ2
    linarith [hw.1]
  obtain ⟨M, hM⟩ := hKc.exists_bound_of_continuousOn (hQ.continuousOn.mono hKE)
  have hb : BddAbove (norm ∘ (fun u => Q u⁻¹) '' (ball 0 ρ \ {0})) := by
    refine ⟨max C M, ?_⟩
    rintro _ ⟨u, hu, rfl⟩
    have hu0 : u ≠ 0 := hu.2
    have hus := mem_ball_zero_iff.mp hu.1
    simp only [Function.comp_apply]
    by_cases h2 : 2 ≤ ‖u⁻¹‖
    · exact (hC _ h2).trans (le_max_left _ _)
    · refine (hM _ ⟨?_, (not_le.mp h2).le⟩).trans (le_max_right _ _)
      rw [norm_inv]
      exact inv_anti₀ (norm_pos_iff.mpr hu0) hus.le
  refine ⟨ρ, hρ1, hρ2, _, differentiableOn_update_limUnder_of_bddAbove
    (isOpen_ball.mem_nhds (mem_ball_self hρ0)) hd hb, fun u hu _ => ?_⟩
  rw [Function.update_of_ne hu]

/-- An annulus `r' < |w|` (`1/2 ≤ r' < 1`) on which `g` avoids `0 = f(0)` and `f(z)`: on `|w| ≥ 1` because
`f(𝔻)` is open and disjoint from `g(𝔻*)`; across `S¹` by compactness. -/
theorem s36l_sp_annulus {f g : ℂ → ℂ} {R r : ℝ} (hR : 1 < R) (hr : r < 1)
    (hf : DifferentiableOn ℂ f (ball 0 R)) (hfi : InjOn f (ball 0 R)) (hf0 : f 0 = 0)
    (hg : DifferentiableOn ℂ g {w | r < ‖w‖}) (hgi : InjOn g {w | r < ‖w‖})
    (hginf : Tendsto g (cocompact ℂ) (cocompact ℂ))
    (hc : g '' unitDiscExterior = (f '' closedBall 0 1)ᶜ) {z : ℂ} (hz : z ∈ unitDisc) :
    ∃ r' : ℝ, r ≤ r' ∧ 1 / 2 ≤ r' ∧ r' < 1 ∧ ∀ w : ℂ, r' < ‖w‖ → g w ≠ 0 ∧ g w ≠ f z := by
  have hcb : closedBall (0 : ℂ) 1 ⊆ ball 0 R := fun w hw =>
    mem_ball_zero_iff.mpr (lt_of_le_of_lt (mem_closedBall_zero_iff.mp hw) hR)
  have hbB : ball (0 : ℂ) 1 ⊆ ball 0 R := ball_subset_closedBall.trans hcb
  -- `V = f(𝔻)` is open
  have hVo : IsOpen (f '' ball 0 1) := by
    rcases ((hf.mono hbB).analyticOnNhd isOpen_ball).is_constant_or_isOpen (convex_ball 0 1).isPreconnected with
      ⟨c, hc'⟩ | h
    · exfalso
      have h1 : f 0 = f (1 / 2) := (hc' 0 (mem_ball_self one_pos)).trans (hc' _ (by simp; norm_num)).symm
      have := hfi (hbB (mem_ball_self one_pos)) (hbB (by simp; norm_num)) h1
      norm_num at this
    · exact h _ subset_rfl isOpen_ball
  have h0V : (0 : ℂ) ∈ f '' ball 0 1 := ⟨0, mem_ball_self one_pos, hf0⟩
  have hzV : f z ∈ f '' ball 0 1 := ⟨z, hz, rfl⟩
  have hVc : f '' ball 0 1 ⊆ f '' closedBall 0 1 := image_mono ball_subset_closedBall
  have hE : IsOpen {w : ℂ | r < ‖w‖} := isOpen_lt continuous_const continuous_norm
  -- on `|w| ≥ 1`, `g w ∉ V`
  have hout : ∀ w : ℂ, 1 ≤ ‖w‖ → g w ∉ f '' ball 0 1 := by
    intro w hw hgV
    have hwE : r < ‖w‖ := by linarith
    have hpre : g ⁻¹' (f '' ball 0 1) ∈ 𝓝 w :=
      ((hg w hwE).differentiableAt (hE.mem_nhds hwE)).continuousAt.preimage_mem_nhds (hVo.mem_nhds hgV)
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hpre
    have hw0 : 0 < ‖w‖ := by linarith
    set w' : ℂ := ((1 + ε / (2 * ‖w‖) : ℝ) : ℂ) * w with hw'
    have hw'n : ‖w'‖ = ‖w‖ + ε / 2 := by
      rw [hw', norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
      field_simp
    have hd : w' ∈ ball w ε := by
      rw [mem_ball, dist_eq_norm, hw', show ((1 + ε / (2 * ‖w‖) : ℝ) : ℂ) * w - w =
        ((ε / (2 * ‖w‖) : ℝ) : ℂ) * w by push_cast; ring, norm_mul, Complex.norm_real,
        Real.norm_of_nonneg (by positivity)]
      field_simp
      linarith
    have hmem : g w' ∈ g '' unitDiscExterior := ⟨w', by show 1 < ‖w'‖; rw [hw'n]; linarith, rfl⟩
    rw [hc] at hmem
    exact hmem (hVc (hball hd))
  set O : Set ℂ := {w : ℂ | r < ‖w‖} ∩ g ⁻¹' ({0, f z}ᶜ) with hO
  have hOo : IsOpen O := hg.continuousOn.isOpen_inter_preimage hE (by
    have : IsClosed ({0, f z} : Set ℂ) := (Set.toFinite _).isClosed
    exact this.isOpen_compl)
  have hgood : ∀ w : ℂ, 1 ≤ ‖w‖ → g w ≠ 0 ∧ g w ≠ f z := by
    intro w hw
    exact ⟨fun h => hout w hw (h ▸ h0V), fun h => hout w hw (h ▸ hzV)⟩
  have hsO : sphere (0 : ℂ) 1 ⊆ O := by
    intro w hw
    have hw1 : ‖w‖ = 1 := by simpa using hw
    refine ⟨by show r < ‖w‖; rw [hw1]; exact hr, ?_⟩
    obtain ⟨h1, h2⟩ := hgood w hw1.ge
    simp only [mem_preimage, mem_compl_iff, mem_insert_iff, mem_singleton_iff, not_or]
    exact ⟨h1, h2⟩
  obtain ⟨δ, hδ, hδO⟩ := (isCompact_sphere (0 : ℂ) 1).exists_cthickening_subset_open hOo hsO
  refine ⟨max (max r (1 / 2)) (1 - δ / 2), (le_max_left _ _).trans (le_max_left _ _),
    (le_max_right _ _).trans (le_max_left _ _), max_lt (max_lt hr (by norm_num)) (by linarith), ?_⟩
  intro w hw
  by_cases hw1 : 1 ≤ ‖w‖
  · exact hgood w hw1
  · push_neg at hw1
    have hwd : 1 - δ / 2 < ‖w‖ := lt_of_le_of_lt (le_max_right _ _) hw
    have hw12 : 1 / 2 < ‖w‖ := lt_of_le_of_lt ((le_max_right _ _).trans (le_max_left _ _)) hw
    have hw0 : 0 < ‖w‖ := by linarith
    set v : ℂ := ((‖w‖⁻¹ : ℝ) : ℂ) * w with hv
    have hvs : v ∈ sphere (0 : ℂ) 1 := by
      rw [mem_sphere_zero_iff_norm, hv, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
      field_simp
    have hdist : dist w v ≤ δ := by
      rw [dist_eq_norm, hv, show w - ((‖w‖⁻¹ : ℝ) : ℂ) * w = ((1 - ‖w‖⁻¹ : ℝ) : ℂ) * w by push_cast; ring,
        norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos]
      · rw [neg_sub, sub_mul, inv_mul_cancel₀ hw0.ne', one_mul]; linarith
      · rw [sub_nonpos]; exact one_le_inv₀ hw0 |>.mpr hw1.le
    have hwO := hδO (Metric.mem_cthickening_of_dist_le w v δ _ hvs hdist)
    have h2 := hwO.2
    simp only [mem_preimage, mem_compl_iff, mem_insert_iff, mem_singleton_iff, not_or] at h2
    exact h2

/-- Holomorphic primitives on a neighbourhood `|w| > r'` of `𝔻̄*` (including `∞`): `P' = 𝒜(g)`,
`Q' = 𝒜(g) - 2g'/g + 2/w`, both bounded near `∞`; there `g ≠ 0` and `g ≠ f(z)`. -/
theorem s36l_sp_primE {f g : ℂ → ℂ} {R r : ℝ} (hR : 1 < R) (hr : r < 1)
    (hf : DifferentiableOn ℂ f (ball 0 R)) (hfi : InjOn f (ball 0 R)) (hf0 : f 0 = 0)
    (hg : DifferentiableOn ℂ g {w | r < ‖w‖}) (hgi : InjOn g {w | r < ‖w‖})
    (hginf : Tendsto g (cocompact ℂ) (cocompact ℂ))
    (hc : g '' unitDiscExterior = (f '' closedBall 0 1)ᶜ) {z : ℂ} (hz : z ∈ unitDisc) :
    ∃ r' : ℝ, r ≤ r' ∧ 0 < r' ∧ r' < 1 ∧ (∀ w : ℂ, r' < ‖w‖ → g w ≠ 0 ∧ g w ≠ f z) ∧
      ∃ P Q : ℂ → ℂ, DifferentiableOn ℂ P {w | r' < ‖w‖} ∧ DifferentiableOn ℂ Q {w | r' < ‖w‖} ∧
        (∀ w : ℂ, r' < ‖w‖ → HasDerivAt P (preSchwarzian g w) w) ∧
        (∀ w : ℂ, r' < ‖w‖ → HasDerivAt Q (preSchwarzian g w - 2 * deriv g w / g w + 2 / w) w) ∧
        ∃ C : ℝ, ∀ w : ℂ, 2 ≤ ‖w‖ → ‖P w‖ ≤ C ∧ ‖Q w‖ ≤ C := by
  obtain ⟨r', hrr', hr12, hr'1, hne⟩ := s36l_sp_annulus hR hr hf hfi hf0 hg hgi hginf hc hz
  have hr0 : 0 < r' := by linarith
  have hsub : {w : ℂ | r' < ‖w‖} ⊆ {w | r < ‖w‖} := fun w hw => lt_of_le_of_lt hrr' hw
  have hg' := hg.mono hsub
  have hgi' := hgi.mono hsub
  have hE : IsOpen {w : ℂ | r' < ‖w‖} := isOpen_lt continuous_const continuous_norm
  obtain ⟨G, hGd, hGi, hG0, hGe⟩ := s36l_sp_inv hr0 hg' hgi' hginf fun w hw => (hne w hw).1
  have h1 : 1 < r'⁻¹ := (one_lt_inv₀ hr0).mpr hr'1
  obtain ⟨PG, QG, hPGd, hQGd, hPG, hQG⟩ := s36l_sp_primD h1 hGd hGi hG0
  have hmem : ∀ w : ℂ, r' < ‖w‖ → w⁻¹ ≠ 0 ∧ ‖w⁻¹‖ < r'⁻¹ := by
    intro w hw
    have hw0 : w ≠ 0 := by intro h; rw [h, norm_zero] at hw; linarith
    refine ⟨inv_ne_zero hw0, ?_⟩
    rw [norm_inv]; exact inv_strictAnti₀ hr0 hw
  -- germs: `g = (G ∘ inv)⁻¹` near `w`, `G = (g ∘ inv)⁻¹` near `w⁻¹`
  have hgerm1 : ∀ w : ℂ, r' < ‖w‖ → g =ᶠ[𝓝 w] fun v => (G v⁻¹)⁻¹ := by
    intro w hw
    filter_upwards [hE.mem_nhds hw] with v hv
    obtain ⟨hv0, hvs⟩ := hmem v hv
    rw [hGe _ hv0 hvs, inv_inv, inv_inv]
  have hgerm2 : ∀ w : ℂ, r' < ‖w‖ → G =ᶠ[𝓝 w⁻¹] fun u => (g u⁻¹)⁻¹ := by
    intro w hw
    obtain ⟨hv0, hvs⟩ := hmem w hw
    have hB : IsOpen (ball (0 : ℂ) r'⁻¹ \ {0}) := isOpen_ball.sdiff isClosed_singleton
    filter_upwards [hB.mem_nhds ⟨mem_ball_zero_iff.mpr hvs, hv0⟩] with u hu
    exact hGe u hu.2 (mem_ball_zero_iff.mp hu.1)
  have hpre : ∀ {h k : ℂ → ℂ} {x : ℂ}, h =ᶠ[𝓝 x] k → preSchwarzian h x = preSchwarzian k x := by
    intro h k x hx
    unfold preSchwarzian
    rw [hx.deriv.deriv_eq, hx.deriv_eq]
  have hGa : ∀ u ∈ ball (0 : ℂ) r'⁻¹, AnalyticAt ℂ G u := fun u hu => hGd.analyticAt (isOpen_ball.mem_nhds hu)
  have hga : ∀ w : ℂ, r' < ‖w‖ → AnalyticAt ℂ g w := fun w hw => hg'.analyticAt (hE.mem_nhds hw)
  have hG'ne : ∀ u ∈ ball (0 : ℂ) r'⁻¹, deriv G u ≠ 0 := fun u hu => deriv_ne_zero_of_injOn isOpen_ball hGd hGi hu
  have hg'ne : ∀ w : ℂ, r' < ‖w‖ → deriv g w ≠ 0 := fun w hw => deriv_ne_zero_of_injOn hE hg' hgi' hw
  have hGne : ∀ u ∈ ball (0 : ℂ) r'⁻¹, u ≠ 0 → G u ≠ 0 := fun u hu hu0 h =>
    hu0 (hGi hu (mem_ball_self (by linarith)) (h.trans hG0.symm))
  refine ⟨r', hrr', hr0, hr'1, hne, fun w => QG w⁻¹, fun w => PG w⁻¹, ?_, ?_, ?_, ?_, ?_⟩
  · intro w hw
    obtain ⟨hv0, hvs⟩ := hmem w hw
    exact ((hQGd _ (mem_ball_zero_iff.mpr hvs)).differentiableAt (isOpen_ball.mem_nhds (mem_ball_zero_iff.mpr hvs))
      |>.comp w (differentiableAt_inv (by simpa using hv0))).differentiableWithinAt
  · intro w hw
    obtain ⟨hv0, hvs⟩ := hmem w hw
    exact ((hPGd _ (mem_ball_zero_iff.mpr hvs)).differentiableAt (isOpen_ball.mem_nhds (mem_ball_zero_iff.mpr hvs))
      |>.comp w (differentiableAt_inv (by simpa using hv0))).differentiableWithinAt
  · intro w hw
    obtain ⟨hv0, hvs⟩ := hmem w hw
    have hw0 : w ≠ 0 := by simpa using hv0
    have hc := (hQG _ (mem_ball_zero_iff.mpr hvs) hv0).comp w (hasDerivAt_inv hw0)
    refine hc.congr_deriv ?_
    -- `𝒜(g)(w) = (𝒜(G) - 2G'/G + 2/u)(w⁻¹) · (-w⁻²)`
    have hinv := preSchwarzian_inversion (hGa _ (mem_ball_zero_iff.mpr hvs)) hv0
      (hGne _ (mem_ball_zero_iff.mpr hvs) hv0) (hG'ne _ (mem_ball_zero_iff.mpr hvs))
    rw [inv_inv, ← hpre (hgerm1 w hw)] at hinv
    rw [← hinv]
    field_simp
  · intro w hw
    obtain ⟨hv0, hvs⟩ := hmem w hw
    have hw0 : w ≠ 0 := by simpa using hv0
    have hc := (hPG _ (mem_ball_zero_iff.mpr hvs)).comp w (hasDerivAt_inv hw0)
    refine hc.congr_deriv ?_
    have hgw0 := (hne w hw).1
    have hinv := preSchwarzian_inversion (hga w hw) hw0 hgw0 (hg'ne w hw)
    rw [← hpre (hgerm2 w hw)] at hinv
    rw [← hinv]
    field_simp
  · have hK : IsCompact (closedBall (0 : ℂ) (1 / 2)) := isCompact_closedBall 0 _
    have hKB : closedBall (0 : ℂ) (1 / 2) ⊆ ball 0 r'⁻¹ := fun u hu =>
      mem_ball_zero_iff.mpr (lt_of_le_of_lt (mem_closedBall_zero_iff.mp hu) (by linarith))
    obtain ⟨C1, hC1⟩ := hK.exists_bound_of_continuousOn (hQGd.continuousOn.mono hKB)
    obtain ⟨C2, hC2⟩ := hK.exists_bound_of_continuousOn (hPGd.continuousOn.mono hKB)
    refine ⟨max C1 C2, fun w hw => ?_⟩
    have hwK : w⁻¹ ∈ closedBall (0 : ℂ) (1 / 2) := by
      rw [mem_closedBall_zero_iff, norm_inv]
      rw [inv_le_comm₀ (by linarith) (by norm_num)]; norm_num; exact hw
    exact ⟨(hC1 _ hwK).trans (le_max_left _ _), (hC2 _ hwK).trans (le_max_right _ _)⟩

/-- Winding of `g(S¹)` around a point not in `g(|w| > r')`. -/
theorem s36l_sp_windE {g : ℂ → ℂ} {r' : ℝ} (hr0 : 0 < r') (hr' : r' < 1)
    (hg : DifferentiableOn ℂ g {w | r' < ‖w‖})
    (hgi : InjOn g {w | r' < ‖w‖}) (hginf : Tendsto g (cocompact ℂ) (cocompact ℂ))
    (hg0 : ∀ w : ℂ, r' < ‖w‖ → g w ≠ 0) {ζ : ℂ}
    (hζ : ∀ w : ℂ, r' < ‖w‖ → g w ≠ ζ) :
    (∮ w in C(0, 1), deriv g w / (g w - ζ)) = 2 * π * I := by
  obtain ⟨G, hGd, hGi, hG0, hGe⟩ := s36l_sp_inv hr0 hg hgi hginf hg0
  have h1 : 1 < r'⁻¹ := (one_lt_inv₀ hr0).mpr hr'
  have hcb : closedBall (0 : ℂ) 1 ⊆ ball 0 r'⁻¹ := fun w hw =>
    mem_ball_zero_iff.mpr (lt_of_le_of_lt (mem_closedBall_zero_iff.mp hw) h1)
  have hmem : ∀ u : ℂ, u ≠ 0 → ‖u‖ < r'⁻¹ → r' < ‖u⁻¹‖ := by
    intro u hu hus
    rw [norm_inv, lt_inv_comm₀ hr0 (norm_pos_iff.mpr hu)]; exact hus
  have hG1 : ∀ u ∈ ball (0 : ℂ) r'⁻¹, 1 - ζ * G u ≠ 0 := by
    intro u hu
    by_cases hu0 : u = 0
    · rw [hu0, hG0]; simp
    · have hus := mem_ball_zero_iff.mp hu
      have ha := hg0 _ (hmem u hu0 hus)
      have hz := hζ _ (hmem u hu0 hus)
      rw [hGe u hu0 hus]
      intro h
      apply hz
      have h' : ζ * (g u⁻¹)⁻¹ = 1 := by linear_combination -h
      rw [mul_inv_eq_one₀ ha] at h'
      exact h'.symm
  have hG' : DifferentiableOn ℂ (deriv G) (ball 0 r'⁻¹) := (hGd.analyticOnNhd isOpen_ball).deriv.differentiableOn
  have hH : DifferentiableOn ℂ (fun u => ζ * deriv G u / (1 - ζ * G u)) (ball 0 r'⁻¹) :=
    ((differentiableOn_const _).mul hG').div ((differentiableOn_const _).sub ((differentiableOn_const _).mul hGd)) hG1
  have heq : EqOn (fun u => deriv g u⁻¹ / (g u⁻¹ - ζ) * (u⁻¹) ^ 2)
      (fun u => deriv G u / (G u - G 0) + ζ * deriv G u / (1 - ζ * G u)) (sphere 0 1) := by
    intro u hu
    have hu1 : ‖u‖ = 1 := by simpa using hu
    have hu0 : u ≠ 0 := by intro h; rw [h, norm_zero] at hu1; norm_num at hu1
    have hus : ‖u‖ < r'⁻¹ := by rw [hu1]; exact h1
    have hd := s36l_sp_inv_deriv hr0 hg hg0 hGe hu0 hus
    have ha := hg0 _ (hmem u hu0 hus)
    have hz := hζ _ (hmem u hu0 hus)
    have hd' : deriv g u⁻¹ / (g u⁻¹ - ζ) * (u⁻¹) ^ 2 = deriv G u / G u ^ 2 / (g u⁻¹ - ζ) := by
      rw [← hd]; ring
    simp only
    rw [hd', hG0, sub_zero, hGe u hu0 hus]
    have hzs : g u⁻¹ - ζ ≠ 0 := sub_ne_zero.mpr hz
    generalize g u⁻¹ = a at ha hzs ⊢
    generalize deriv G u = d
    have h3 : 1 - ζ * a⁻¹ ≠ 0 := by
      rw [show 1 - ζ * a⁻¹ = (a - ζ) / a by field_simp]
      exact div_ne_zero hzs ha
    field_simp
    ring
  rw [s36l_sp_circ_inv, circleIntegral.integral_congr zero_le_one heq]
  have hGs : ∀ u ∈ sphere (0 : ℂ) 1, G u - G 0 ≠ 0 := by
    intro u hu
    have hu1 : ‖u‖ = 1 := by simpa using hu
    have hu0 : u ≠ 0 := by intro h; rw [h, norm_zero] at hu1; norm_num at hu1
    exact sub_ne_zero.mpr fun h => hu0 (hGi (hcb (sphere_subset_closedBall hu))
      (mem_ball_self (by linarith)) h)
  have hc1 : ContinuousOn (fun u => deriv G u / (G u - G 0)) (sphere 0 1) :=
    ((hG'.continuousOn.mono (sphere_subset_closedBall.trans hcb)).div
      ((hGd.continuousOn.mono (sphere_subset_closedBall.trans hcb)).sub continuousOn_const) hGs)
  have e := circleIntegral.integral_add (c := 0) (R := 1) (f := fun u => deriv G u / (G u - G 0))
    (g := fun u => ζ * deriv G u / (1 - ζ * G u)) (hc1.circleIntegrable zero_le_one)
    ((hH.continuousOn.mono (sphere_subset_closedBall.trans hcb)).circleIntegrable zero_le_one)
  beta_reduce at e
  rw [e, s36l_sp_windD h1 hGd hGi (mem_ball_self zero_lt_one : (0 : ℂ) ∈ unitDisc),
    circleIntegral_eq_zero_of_differentiable_on_off_countable zero_le_one countable_empty
      (hH.continuousOn.mono hcb) fun w hw => (hH w (hcb (ball_subset_closedBall hw.1))).differentiableAt
        (isOpen_ball.mem_nhds (hcb (ball_subset_closedBall hw.1))), add_zero]

/-- The jump relation on `S¹`: `U_𝔻 = -P̄_𝔻 + Q_𝔻` and `U_{𝔻*} = -P̄_* + Q_*` agree along the welding up to a
constant (their tangential derivatives agree: `1 + Re(w𝒜(γ)) = wγ'/γ` on `S¹`). -/
theorem s36l_sp_jump {f g γ PD QD PE QE : ℂ → ℂ} {R r' a b : ℝ} (hR : 1 < R) (hr' : r' < 1)
    (hf : DifferentiableOn ℂ f (ball 0 R)) (hfi : InjOn f (ball 0 R)) (hf0 : f 0 = 0)
    (hg : DifferentiableOn ℂ g {w | r' < ‖w‖}) (hgi : InjOn g {w | r' < ‖w‖})
    (hg0 : ∀ w : ℂ, r' < ‖w‖ → g w ≠ 0)
    (hPD : ∀ w ∈ ball (0 : ℂ) R, HasDerivAt PD (preSchwarzian f w) w)
    (hQD : ∀ w ∈ ball (0 : ℂ) R, w ≠ 0 → HasDerivAt QD (preSchwarzian f w - 2 * deriv f w / f w + 2 / w) w)
    (hPE : ∀ w : ℂ, r' < ‖w‖ → HasDerivAt PE (preSchwarzian g w) w)
    (hQE : ∀ w : ℂ, r' < ‖w‖ → HasDerivAt QE (preSchwarzian g w - 2 * deriv g w / g w + 2 / w) w)
    (ha : a < 1) (hb : 1 < b) (hbR : b ≤ R) (hγ : DifferentiableOn ℂ γ {w | a < ‖w‖ ∧ ‖w‖ < b})
    (hγg : ∀ w : ℂ, a < ‖w‖ → ‖w‖ < b → r' < ‖γ w‖ ∧ g (γ w) = f w)
    (hS : ∀ w : ℂ, ‖w‖ = 1 → ‖γ w‖ = 1) :
    ∃ c : ℂ, ∀ w : ℂ, ‖w‖ = 1 → -conj (PD w) + QD w = -conj (PE (γ w)) + QE (γ w) + c := by
  set A : Set ℂ := {w | a < ‖w‖ ∧ ‖w‖ < b} with hA
  have hAo : IsOpen A :=
    (isOpen_lt continuous_const continuous_norm).inter (isOpen_lt continuous_norm continuous_const)
  have hE : IsOpen {w : ℂ | r' < ‖w‖} := isOpen_lt continuous_const continuous_norm
  set e : ℝ → ℂ := circleMap 0 1 with he
  have he1 : ∀ θ, ‖e θ‖ = 1 := fun θ => by simp [he]
  have heA : ∀ θ, e θ ∈ A := fun θ => ⟨by rw [he1 θ]; exact ha, by rw [he1 θ]; exact hb⟩
  have heB : ∀ θ, e θ ∈ ball (0 : ℂ) R := fun θ => mem_ball_zero_iff.mpr (by rw [he1 θ]; exact hR)
  have he' : ∀ θ, HasDerivAt e (e θ * I) θ := fun θ => by
    have := hasDerivAt_circleMap (0 : ℂ) 1 θ
    simpa [he, circleMap_zero] using this
  have hγ'd : DifferentiableOn ℂ (deriv γ) A := (hγ.analyticOnNhd hAo).deriv.differentiableOn
  have hγa : ∀ θ, HasDerivAt γ (deriv γ (e θ)) (e θ) := fun θ =>
    ((hγ _ (heA θ)).differentiableAt (hAo.mem_nhds (heA θ))).hasDerivAt
  have hγ'a : ∀ θ, HasDerivAt (deriv γ) (deriv (deriv γ) (e θ)) (e θ) := fun θ =>
    ((hγ'd _ (heA θ)).differentiableAt (hAo.mem_nhds (heA θ))).hasDerivAt
  have hξE : ∀ θ, r' < ‖γ (e θ)‖ := fun θ => (hγg _ (heA θ).1 (heA θ).2).1
  have hξ1 : ∀ θ, ‖γ (e θ)‖ = 1 := fun θ => hS _ (he1 θ)
  have hγξ0 : ∀ θ, γ (e θ) ≠ 0 := fun θ h => by have := hξ1 θ; rw [h, norm_zero] at this; norm_num at this
  have hfg : ∀ θ, g (γ (e θ)) = f (e θ) := fun θ => (hγg _ (heA θ).1 (heA θ).2).2
  have hgerm : ∀ θ, (g ∘ γ) =ᶠ[𝓝 (e θ)] f := fun θ => by
    filter_upwards [hAo.mem_nhds (heA θ)] with u hu
    exact (hγg u hu.1 hu.2).2
  have hga : ∀ θ, HasDerivAt g (deriv g (γ (e θ))) (γ (e θ)) := fun θ =>
    ((hg _ (hξE θ)).differentiableAt (hE.mem_nhds (hξE θ))).hasDerivAt
  have hchain : ∀ θ, deriv f (e θ) = deriv g (γ (e θ)) * deriv γ (e θ) := fun θ => by
    rw [← (hgerm θ).deriv_eq, deriv_comp _ (hga θ).differentiableAt (hγa θ).differentiableAt]
  have hf'ne : ∀ θ, deriv f (e θ) ≠ 0 := fun θ => deriv_ne_zero_of_injOn isOpen_ball hf hfi (heB θ)
  have hγ'ne : ∀ θ, deriv γ (e θ) ≠ 0 := fun θ h => hf'ne θ (by rw [hchain θ, h, mul_zero])
  have hg'ne : ∀ θ, deriv g (γ (e θ)) ≠ 0 := fun θ => deriv_ne_zero_of_injOn hE hg hgi (hξE θ)
  have hg0' : ∀ θ, g (γ (e θ)) ≠ 0 := fun θ => hg0 _ (hξE θ)
  -- pre-Schwarzian chain rule along the welding
  have hApre : ∀ θ, preSchwarzian f (e θ) =
      preSchwarzian g (γ (e θ)) * deriv γ (e θ) + preSchwarzian γ (e θ) := by
    intro θ
    have h := preSchwarzian_comp_of_analyticAt (hγ.analyticAt (hAo.mem_nhds (heA θ)))
      (hg.analyticAt (hE.mem_nhds (hξE θ))) (hγ'ne θ) (hg'ne θ)
    rw [← h]
    unfold preSchwarzian
    rw [(hgerm θ).deriv.deriv_eq, (hgerm θ).deriv_eq]
  -- the real function `T = wγ'/γ` along `S¹`
  set T : ℝ → ℂ := fun θ => e θ * deriv γ (e θ) / γ (e θ) with hT
  have hTim : ∀ θ, (T θ).im = 0 := by
    intro θ
    set c : ℝ → ℂ := fun θ => γ (e θ) with hc_def
    have hc : ∀ θ, HasDerivAt c (deriv γ (e θ) * (e θ * I)) θ := fun θ => (hγa θ).comp θ (he' θ)
    have h1 : HasDerivAt (fun θ => c θ * star (c θ))
        (deriv γ (e θ) * (e θ * I) * star (c θ) + c θ * star (deriv γ (e θ) * (e θ * I))) θ :=
      (hc θ).mul (hc θ).star
    have hconst : (fun θ => c θ * star (c θ)) = fun _ => (1 : ℂ) := by
      funext θ
      show γ (e θ) * conj (γ (e θ)) = 1
      rw [Complex.mul_conj', hξ1 θ]; norm_num
    rw [hconst] at h1
    have h0 := h1.unique (hasDerivAt_const θ (1 : ℂ))
    have hcc : conj (γ (e θ)) = (γ (e θ))⁻¹ := by
      rw [Complex.inv_def, Complex.normSq_eq_norm_sq, hξ1 θ]; simp
    have hX : deriv γ (e θ) * (e θ * I) * conj (γ (e θ)) = I * T θ := by
      rw [hcc, hT]; field_simp [hγξ0 θ]
    have h2 : deriv γ (e θ) * (e θ * I) * conj (γ (e θ)) +
        conj (deriv γ (e θ) * (e θ * I) * conj (γ (e θ))) = 0 := by
      have e1 : conj (deriv γ (e θ) * (e θ * I) * conj (γ (e θ))) =
          c θ * star (deriv γ (e θ) * (e θ * I)) := by
        simp only [map_mul, Complex.conj_conj, hc_def, Complex.star_def]; ring
      rw [e1]
      exact h0
    rw [hX, Complex.add_conj] at h2
    have h3 : (I * T θ).re = 0 := by exact_mod_cast (by simpa using h2 : ((I * T θ).re : ℂ) = 0)
    simpa using h3
  have hTre : ∀ θ, T θ = ((T θ).re : ℂ) := fun θ => by
    apply Complex.ext <;> simp [hTim θ]
  have hT0 : ∀ θ, T θ ≠ 0 := fun θ => by
    simp only [hT]
    exact div_ne_zero (mul_ne_zero (by intro h; have := he1 θ; rw [h, norm_zero] at this; norm_num at this)
      (hγ'ne θ)) (hγξ0 θ)
  have hReA : ∀ θ, (e θ * preSchwarzian γ (e θ)).re = (T θ).re - 1 := by
    intro θ
    have hd : HasDerivAt T (I * T θ * (1 + e θ * preSchwarzian γ (e θ) - T θ)) θ := by
      have h1 := ((he' θ).mul ((hγ'a θ).comp θ (he' θ))).div ((hγa θ).comp θ (he' θ)) (hγξ0 θ)
      refine h1.congr_deriv ?_
      simp only [hT, preSchwarzian, Function.comp_apply, Pi.mul_apply]
      have := hγ'ne θ
      have := hγξ0 θ
      field_simp
    have him : HasDerivAt (fun θ => (T θ).im) (I * T θ * (1 + e θ * preSchwarzian γ (e θ) - T θ)).im θ :=
      Complex.imCLM.hasFDerivAt.comp_hasDerivAt θ hd
    have him0 : HasDerivAt (fun θ => (T θ).im) 0 θ := by
      have : (fun θ => (T θ).im) = fun _ => (0 : ℝ) := funext hTim
      rw [this]; exact hasDerivAt_const θ 0
    have h0 := him.unique him0
    rw [hTre θ] at h0
    have hTr : (T θ).re ≠ 0 := fun h => hT0 θ (by rw [hTre θ, h]; simp)
    generalize e θ * preSchwarzian γ (e θ) = X at h0 ⊢
    simp only [Complex.mul_im, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.sub_re, Complex.add_re, Complex.one_re, Complex.sub_im, Complex.add_im,
      Complex.one_im] at h0
    have : (T θ).re * (1 + X.re - (T θ).re) = 0 := by linear_combination h0
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h hTr
    · linarith
  -- the difference `D(θ)` has zero derivative
  set D : ℝ → ℂ := fun θ => (-conj (PD (e θ)) + QD (e θ)) - (-conj (PE (γ (e θ))) + QE (γ (e θ))) with hD
  have hDd : ∀ θ, HasDerivAt D 0 θ := by
    intro θ
    have he0 : e θ ≠ 0 := by intro h; have := he1 θ; rw [h, norm_zero] at this; norm_num at this
    have hP1 := ((hPD _ (heB θ)).comp θ (he' θ)).star
    have hQ1 := (hQD _ (heB θ) he0).comp θ (he' θ)
    have hγe := (hγa θ).comp θ (he' θ)
    have hP2 := ((hPE _ (hξE θ)).comp θ hγe).star
    have hQ2 := (hQE _ (hξE θ)).comp θ hγe
    have h := (hP1.neg.add hQ1).sub (hP2.neg.add hQ2)
    refine h.congr_deriv ?_
    have hX : preSchwarzian f (e θ) * (e θ * I) =
        I * (preSchwarzian g (γ (e θ)) * T θ * γ (e θ) + e θ * preSchwarzian γ (e θ)) := by
      rw [hApre θ, hT]; field_simp [hγξ0 θ]
    have hW : deriv f (e θ) / f (e θ) * (e θ * I) =
        I * (T θ * γ (e θ) * deriv g (γ (e θ)) / g (γ (e θ))) := by
      rw [hchain θ, ← hfg θ, hT]; field_simp [hγξ0 θ, hg0' θ]
    have hV : deriv γ (e θ) * (e θ * I) = I * T θ * γ (e θ) := by rw [hT]; field_simp [hγξ0 θ]
    have hQf : (preSchwarzian f (e θ) - 2 * deriv f (e θ) / f (e θ) + 2 / e θ) * (e θ * I) =
        preSchwarzian f (e θ) * (e θ * I) - 2 * (deriv f (e θ) / f (e θ) * (e θ * I)) + 2 * I := by
      field_simp
    have hQg : (preSchwarzian g (γ (e θ)) - 2 * deriv g (γ (e θ)) / g (γ (e θ)) + 2 / γ (e θ)) *
        (deriv γ (e θ) * (e θ * I)) =
        I * T θ * (preSchwarzian g (γ (e θ)) * γ (e θ) - 2 * (γ (e θ) * deriv g (γ (e θ)) / g (γ (e θ))) + 2) := by
      rw [hV]; field_simp [hγξ0 θ]
    have hY := Complex.add_conj (e θ * preSchwarzian γ (e θ))
    rw [hReA θ] at hY
    rw [hQf, hQg, hX, hW, show preSchwarzian g (γ (e θ)) * (deriv γ (e θ) * (e θ * I)) =
      I * T θ * (preSchwarzian g (γ (e θ)) * γ (e θ)) by rw [hV]; ring]
    rw [hTre θ]
    simp only [Complex.star_def, map_mul, map_add, map_neg, map_sub, map_ofNat, Complex.conj_I, Complex.conj_ofReal, star_mul', star_add, star_neg, star_sub]
    push_cast at hY
    simp only [map_mul] at hY
    linear_combination I * hY
  -- constancy and evaluation
  refine ⟨D 0, fun w hw => ?_⟩
  have hDc : ∀ θ, D θ = D 0 := fun θ =>
    is_const_of_deriv_eq_zero (fun θ => (hDd θ).differentiableAt) (fun θ => (hDd θ).deriv) θ 0
  have hwe : e (Complex.arg w) = w := by
    have := Complex.norm_mul_exp_arg_mul_I w
    rw [hw, Complex.ofReal_one, one_mul] at this
    simp [he, circleMap_zero, this]
  have := hDc (Complex.arg w)
  simp only [hD, hwe] at this
  linear_combination this

/-- `w ↦ K₁(f)(z, w)` agrees off `w = z` with a function holomorphic on `|w| < R` (removable diagonal, TT:3949):
with `q = dslope f z`, `ρ = dslope q z`, `πK₁ = (ρ² - f'(z)ρ')/q²`. -/
theorem s36l_sp_K1_holo {f : ℂ → ℂ} {R : ℝ} (hf : DifferentiableOn ℂ f (ball 0 R))
    (hfi : InjOn f (ball 0 R)) {z : ℂ} (hz : z ∈ ball (0 : ℂ) R) :
    ∃ K : ℂ → ℂ, DifferentiableOn ℂ K (ball 0 R) ∧ ∀ w ∈ ball (0 : ℂ) R, w ≠ z → K w = kerK1 f z w := by
  have hzn : ball (0 : ℂ) R ∈ 𝓝 z := isOpen_ball.mem_nhds hz
  set q : ℂ → ℂ := dslope f z with hq_def
  set ρ : ℂ → ℂ := dslope q z with hρ_def
  have hq : DifferentiableOn ℂ q (ball 0 R) := (differentiableOn_dslope hzn).mpr hf
  have hρ : DifferentiableOn ℂ ρ (ball 0 R) := (differentiableOn_dslope hzn).mpr hq
  have hρ' : DifferentiableOn ℂ (deriv ρ) (ball 0 R) := (hρ.analyticOnNhd isOpen_ball).deriv.differentiableOn
  have hfe : ∀ w, f w = f z + (w - z) * q w := fun w => by
    have := sub_smul_dslope f z w
    rw [smul_eq_mul] at this
    rw [this]; ring
  have hqe : ∀ w, q w = deriv f z + (w - z) * ρ w := fun w => by
    have := sub_smul_dslope q z w
    rw [smul_eq_mul, hq_def, dslope_same] at this
    rw [← hq_def] at this
    rw [hρ_def, this]; ring
  have hF : f = fun w => f z + (w - z) * (deriv f z + (w - z) * ρ w) := by
    funext w; rw [hfe w, hqe w]
  have hdf : ∀ w ∈ ball (0 : ℂ) R, deriv f w =
      deriv f z + 2 * (w - z) * ρ w + (w - z) ^ 2 * deriv ρ w := by
    intro w hw
    have hρw : HasDerivAt ρ (deriv ρ w) w :=
      (hρ.differentiableAt (isOpen_ball.mem_nhds hw)).hasDerivAt
    have h1 : HasDerivAt (fun w => f z + (w - z) * (deriv f z + (w - z) * ρ w))
        ((1 : ℂ) * (deriv f z + (w - z) * ρ w) + (w - z) * ((1 : ℂ) * ρ w + (w - z) * deriv ρ w)) w := by
      have hl : HasDerivAt (fun w : ℂ => w - z) 1 w := (hasDerivAt_id w).sub_const z
      exact ((hl.mul ((hl.mul hρw).const_add (deriv f z)))).const_add (f z)
    conv_lhs => rw [hF]
    rw [h1.deriv]
    ring
  have hqne : ∀ w ∈ ball (0 : ℂ) R, q w ≠ 0 := by
    intro w hw
    by_cases hwz : w = z
    · rw [hwz, hq_def, dslope_same]
      exact deriv_ne_zero_of_injOn isOpen_ball hf hfi hz
    · rw [hq_def, dslope_of_ne f hwz, slope_def_field]
      exact div_ne_zero (sub_ne_zero.mpr fun h => hwz (hfi hw hz h)) (sub_ne_zero.mpr hwz)
  refine ⟨fun w => 1 / π * ((ρ w ^ 2 - deriv f z * deriv ρ w) / q w ^ 2), ?_, ?_⟩
  · exact (differentiableOn_const _).mul (((hρ.pow 2).sub ((differentiableOn_const _).mul hρ')).div
      (hq.pow 2) fun w hw => pow_ne_zero 2 (hqne w hw))
  · intro w hw hwz
    have hzw : z ≠ w := fun h => hwz h.symm
    beta_reduce
    rw [kerK1_of_ne f hzw, hdf w hw]
    have hfzw : f z - f w = -((w - z) * q w) := by rw [hfe w]; ring
    rw [hfzw, hqe w]
    have ht : w - z ≠ 0 := sub_ne_zero.mpr hwz
    have hq' : deriv f z + (w - z) * ρ w ≠ 0 := by rw [← hqe w]; exact hqne w hw
    rw [show z - w = -(w - z) by ring]
    generalize w - z = t at ht hq' ⊢
    generalize deriv f z = a at hq' ⊢
    generalize ρ w = b at hq' ⊢
    generalize deriv ρ w = d
    congr 1
    have h1 : (-t) ^ 2 ≠ 0 := pow_ne_zero 2 (neg_ne_zero.mpr ht)
    have h2 : (-(t * (a + t * b))) ^ 2 ≠ 0 := pow_ne_zero 2 (neg_ne_zero.mpr (mul_ne_zero ht hq'))
    have h3 : (a + t * b) ^ 2 ≠ 0 := pow_ne_zero 2 hq'
    rw [div_sub_div _ _ h1 h2, div_eq_div_iff h3 (mul_ne_zero h1 h2)]
    ring

/-- Green on `𝔻` for the `K₁`-term: `∬_𝔻 K₁ \overline{𝒜(f)} = (1/2i) ∮_{S¹} K₁ \overline{P}`. -/
theorem s36l_sp_I1 {f P : ℂ → ℂ} {R : ℝ} (hR : 1 < R)
    (hf : DifferentiableOn ℂ f (ball 0 R)) (hfi : InjOn f (ball 0 R))
    (hP : ∀ w ∈ ball (0 : ℂ) R, HasDerivAt P (preSchwarzian f w) w) {z : ℂ} (hz : z ∈ unitDisc) :
    (∫ w in unitDisc, kerK1 f z w * conj (preSchwarzian f w)) =
      1 / (2 * I) * ∮ w in C(0, 1), kerK1 f z w * conj (P w) := by
  have hzR : z ∈ ball (0 : ℂ) R := mem_ball_zero_iff.mpr (lt_trans (mem_ball_zero_iff.mp hz) hR)
  obtain ⟨K, hK, hKe⟩ := s36l_sp_K1_holo hf hfi hzR
  have hcb : closedBall (0 : ℂ) 1 ⊆ ball 0 R := fun w hw =>
    mem_ball_zero_iff.mpr (lt_of_le_of_lt (mem_closedBall_zero_iff.mp hw) hR)
  have hPd : DifferentiableOn ℂ P (ball 0 R) := fun w hw => (hP w hw).differentiableAt.differentiableWithinAt
  have hKr : ContDiffOn ℝ 1 K (ball 0 R) := (hK.contDiffOn isOpen_ball).restrict_scalars ℝ
  have hPr : ContDiffOn ℝ 1 P (ball 0 R) := (hPd.contDiffOn isOpen_ball).restrict_scalars ℝ
  have hcP : ContDiffOn ℝ 1 (fun w => conj (P w)) (ball 0 R) :=
    Complex.conjCLE.contDiff.comp_contDiffOn hPr
  have hF : ContDiffOn ℝ 1 (fun w => K w * conj (P w)) (closedBall 0 1) := (hKr.mul hcP).mono hcb
  have hG := eq11_9_green_dz zero_lt_one hF
  have hsph : EqOn (fun w => K w * conj (P w)) (fun w => kerK1 f z w * conj (P w)) (sphere 0 1) := by
    intro w hw
    have hw1 : ‖w‖ = 1 := by simpa using hw
    have hwz : w ≠ z := fun h => by
      rw [h] at hw1; have := mem_ball_zero_iff.mp hz; linarith
    simp only [hKe w (hcb (sphere_subset_closedBall hw)) hwz]
  rw [circleIntegral.integral_congr zero_le_one hsph] at hG
  rw [hG]
  have hI : (2 * I : ℂ) ≠ 0 := by simp [I_ne_zero]
  rw [← mul_assoc, one_div, inv_mul_cancel₀ hI, one_mul]
  refine setIntegral_congr_ae measurableSet_ball ?_
  filter_upwards [(volume : Measure ℂ).ae_ne z] with w hwz hw
  have hwB : w ∈ ball (0 : ℂ) R := hcb (ball_subset_closedBall hw)
  have hKw : DifferentiableAt ℂ K w := (hK w hwB).differentiableAt (isOpen_ball.mem_nhds hwB)
  have hPw : DifferentiableAt ℂ P w := (hP w hwB).differentiableAt
  have hcPw : DifferentiableAt ℝ (fun w => conj (P w)) w :=
    Complex.conjCLE.differentiableAt.comp w (hPw.restrictScalars ℝ)
  rw [dzbar_mul (hKw.restrictScalars ℝ) hcPw, dzbar_conj (hPw.restrictScalars ℝ), dz_eq_deriv hPw,
    (cauchyRiemann_iff.1 hKw).2, (hP w hwB).deriv, hKe w hwB hwz, mul_zero, add_zero]

/-- Green on `𝔻*` for the `K₂`-term (with the outer circle pushed to `∞`). -/
theorem s36l_sp_I2 {f g P : ℂ → ℂ} {R r' : ℝ} (hR : 1 < R) (hr0 : 0 < r') (hr' : r' < 1)
    (hf : DifferentiableOn ℂ f (ball 0 R)) (hg : DifferentiableOn ℂ g {w | r' < ‖w‖})
    (hgi : InjOn g {w | r' < ‖w‖}) (hginf : Tendsto g (cocompact ℂ) (cocompact ℂ))
    (hg0 : ∀ w : ℂ, r' < ‖w‖ → g w ≠ 0) {z : ℂ} (hz : z ∈ unitDisc)
    (hgz : ∀ w : ℂ, r' < ‖w‖ → g w ≠ f z)
    (hP : ∀ w : ℂ, r' < ‖w‖ → HasDerivAt P (preSchwarzian g w) w) {C : ℝ}
    (hC : ∀ w : ℂ, 2 ≤ ‖w‖ → ‖P w‖ ≤ C) :
    (∫ w in unitDiscExterior, kerK2 f g z w * conj (-preSchwarzian g w)) =
      1 / (2 * I) * ∮ w in C(0, 1), kerK2 f g z w * conj (P w) := by
  obtain ⟨G, hGd, hGi, hG0, hGe⟩ := s36l_sp_inv hr0 hg hgi hginf hg0
  obtain ⟨ρ, hρ1, hρ2, P', hP'd, hP'e⟩ := s36l_sp_remove hr0 hr'
    (fun w hw => (hP w hw).differentiableAt.differentiableWithinAt) hC
  have hcb : closedBall (0 : ℂ) 1 ⊆ ball 0 ρ := fun w hw =>
    mem_ball_zero_iff.mpr (lt_of_le_of_lt (mem_closedBall_zero_iff.mp hw) hρ1)
  have hbb : ball (0 : ℂ) ρ ⊆ ball 0 r'⁻¹ := ball_subset_ball hρ2.le
  have hmem : ∀ u : ℂ, u ≠ 0 → ‖u‖ < r'⁻¹ → r' < ‖u⁻¹‖ := by
    intro u hu hus
    rw [norm_inv, lt_inv_comm₀ hr0 (norm_pos_iff.mpr hu)]; exact hus
  have hG1 : ∀ u ∈ ball (0 : ℂ) ρ, f z * G u - 1 ≠ 0 := by
    intro u hu
    have hus : ‖u‖ < r'⁻¹ := mem_ball_zero_iff.mp (hbb hu)
    by_cases hu0 : u = 0
    · rw [hu0, hG0]; simp
    · have ha := hg0 _ (hmem u hu0 hus)
      have hz := hgz _ (hmem u hu0 hus)
      rw [hGe u hu0 hus]
      intro h
      apply hz
      have h' : f z * (g u⁻¹)⁻¹ = 1 := by linear_combination h
      rw [mul_inv_eq_one₀ ha] at h'
      exact h'.symm
  have hG' : DifferentiableOn ℂ (deriv G) (ball 0 r'⁻¹) := (hGd.analyticOnNhd isOpen_ball).deriv.differentiableOn
  set H : ℂ → ℂ := fun u => 1 / π * (deriv f z * deriv G u / (f z * G u - 1) ^ 2) with hH_def
  have hH : DifferentiableOn ℂ H (ball 0 ρ) :=
    (differentiableOn_const _).mul (((differentiableOn_const _).mul (hG'.mono hbb)).div
      ((((differentiableOn_const _).mul (hGd.mono hbb)).sub (differentiableOn_const _)).pow 2)
        fun u hu => pow_ne_zero 2 (hG1 u hu))
  have hHe : ∀ u : ℂ, u ≠ 0 → ‖u‖ < ρ → H u = kerK2 f g z u⁻¹ * (u⁻¹) ^ 2 := by
    intro u hu0 huρ
    have hus : ‖u‖ < r'⁻¹ := lt_trans huρ hρ2
    have hd := s36l_sp_inv_deriv hr0 hg hg0 hGe hu0 hus
    have ha := hg0 _ (hmem u hu0 hus)
    have hz := hgz _ (hmem u hu0 hus)
    have e1 : kerK2 f g z u⁻¹ * (u⁻¹) ^ 2 =
        1 / π * (deriv f z * (deriv g u⁻¹ * (u⁻¹) ^ 2) / (f z - g u⁻¹) ^ 2) := by
      unfold kerK2; ring
    rw [e1, hd, hH_def]
    simp only
    rw [hGe u hu0 hus]
    have hzs : f z - g u⁻¹ ≠ 0 := sub_ne_zero.mpr hz.symm
    generalize g u⁻¹ = a at ha hzs ⊢
    generalize deriv G u = d
    have h3 : f z * a⁻¹ - 1 ≠ 0 := by
      rw [show f z * a⁻¹ - 1 = (f z - a) / a by field_simp]
      exact div_ne_zero hzs ha
    field_simp
  -- derivative of `P' = P ∘ inv`
  have hP'deriv : ∀ u : ℂ, u ≠ 0 → ‖u‖ < ρ → deriv P' u = preSchwarzian g u⁻¹ * -(u ^ 2)⁻¹ := by
    intro u hu0 huρ
    have hw := hmem u hu0 (lt_trans huρ hρ2)
    have hc : HasDerivAt (fun u => P u⁻¹) (preSchwarzian g u⁻¹ * -(u ^ 2)⁻¹) u := by
      have := (hP _ hw).comp u (hasDerivAt_inv hu0)
      simpa [Function.comp_def] using this
    have hB : IsOpen (ball (0 : ℂ) ρ \ {0}) := isOpen_ball.sdiff isClosed_singleton
    have hev : P' =ᶠ[𝓝 u] fun u => P u⁻¹ := by
      filter_upwards [hB.mem_nhds ⟨mem_ball_zero_iff.mpr huρ, hu0⟩] with v hv
      exact hP'e v hv.2 (mem_ball_zero_iff.mp hv.1)
    rw [hev.deriv_eq, hc.deriv]
  -- Green on the unit disc for `H · conj P'`
  have hHr : ContDiffOn ℝ 1 H (ball 0 ρ) := (hH.contDiffOn isOpen_ball).restrict_scalars ℝ
  have hPr : ContDiffOn ℝ 1 P' (ball 0 ρ) := (hP'd.contDiffOn isOpen_ball).restrict_scalars ℝ
  have hcP : ContDiffOn ℝ 1 (fun u => conj (P' u)) (ball 0 ρ) := Complex.conjCLE.contDiff.comp_contDiffOn hPr
  have hF : ContDiffOn ℝ 1 (fun u => H u * conj (P' u)) (closedBall 0 1) := (hHr.mul hcP).mono hcb
  have hGr := eq11_9_green_dz zero_lt_one hF
  -- the circle integral is the original one, by inversion
  have hcirc : (∮ u in C(0, 1), H u * conj (P' u)) = ∮ w in C(0, 1), kerK2 f g z w * conj (P w) := by
    rw [s36l_sp_circ_inv (fun w => kerK2 f g z w * conj (P w))]
    refine circleIntegral.integral_congr zero_le_one fun u hu => ?_
    have hu1 : ‖u‖ = 1 := by simpa using hu
    have hu0 : u ≠ 0 := by intro h; rw [h, norm_zero] at hu1; norm_num at hu1
    rw [hHe u hu0 (by rw [hu1]; exact hρ1), hP'e u hu0 (by rw [hu1]; exact hρ1)]
    ring
  rw [hcirc] at hGr
  rw [hGr]
  have hI : (2 * I : ℂ) ≠ 0 := by simp [I_ne_zero]
  rw [← mul_assoc, one_div, inv_mul_cancel₀ hI, one_mul]
  -- change of variables `w = 1/u`
  rw [integral_image_conformal_complex (isOpen_ball.sdiff isClosed_singleton) isConformalOnto_inv_puncturedDisc]
  have hnull : (ball (0 : ℂ) 1 \ {0} : Set ℂ) =ᵐ[volume] ball (0 : ℂ) 1 :=
    sdiff_null_ae_eq_self (measure_singleton 0)
  rw [setIntegral_congr_set hnull]
  refine setIntegral_congr_ae measurableSet_ball ?_
  filter_upwards [(volume : Measure ℂ).ae_ne 0] with u hu0 hu
  have huρ : ‖u‖ < ρ := lt_trans (mem_ball_zero_iff.mp hu) hρ1
  have hHu : DifferentiableAt ℂ H u := (hH u (mem_ball_zero_iff.mpr huρ)).differentiableAt
    (isOpen_ball.mem_nhds (mem_ball_zero_iff.mpr huρ))
  have hPu : DifferentiableAt ℂ P' u := (hP'd u (mem_ball_zero_iff.mpr huρ)).differentiableAt
    (isOpen_ball.mem_nhds (mem_ball_zero_iff.mpr huρ))
  have hcPu : DifferentiableAt ℝ (fun u => conj (P' u)) u :=
    Complex.conjCLE.differentiableAt.comp u (hPu.restrictScalars ℝ)
  rw [dzbar_mul (hHu.restrictScalars ℝ) hcPu, dzbar_conj (hPu.restrictScalars ℝ), dz_eq_deriv hPu,
    (cauchyRiemann_iff.1 hHu).2, mul_zero, add_zero, hP'deriv u hu0 huρ, hHe u hu0 huρ, deriv_inv]
  have hn : ((‖-(u ^ 2)⁻¹‖ ^ 2 : ℝ) : ℂ) = (u⁻¹) ^ 2 * conj (-(u ^ 2)⁻¹) * (-1) := by
    rw [norm_neg, norm_inv, norm_pow, map_neg, map_inv₀, map_pow]
    have hc : (u⁻¹) ^ 2 * -((conj u ^ 2)⁻¹) * (-1) = ((u * conj u) ^ 2)⁻¹ := by ring
    rw [hc, Complex.mul_conj']
    push_cast
    ring
  push_cast at hn ⊢
  rw [hn]
  simp only [map_mul, map_neg]
  ring

/-- The boundary values of an antiholomorphic function have no `(w - z)⁻²` moment. -/
theorem s36l_sp_conj_zero {P : ℂ → ℂ} {R : ℝ} (hR : 1 < R) (hP : DifferentiableOn ℂ P (ball 0 R))
    {z : ℂ} (hz : z ∈ unitDisc) :
    (∮ w in C(0, 1), conj (P w) / (w - z) ^ 2) = 0 := by
  have hz1 : ‖z‖ < 1 := mem_ball_zero_iff.mp hz
  set U : Set ℂ := ball 0 R ∩ {u | 1 - conj z * u ≠ 0} with hU
  have hUo : IsOpen U :=
    isOpen_ball.inter (isOpen_ne_fun (continuous_const.sub (continuous_const.mul continuous_id)) continuous_const)
  have hcU : closedBall (0 : ℂ) 1 ⊆ U := by
    intro u hu
    have hu1 : ‖u‖ ≤ 1 := mem_closedBall_zero_iff.mp hu
    refine ⟨mem_ball_zero_iff.mpr (lt_of_le_of_lt hu1 hR), ?_⟩
    show 1 - conj z * u ≠ 0
    intro h
    have h' : conj z * u = 1 := by linear_combination -h
    have := congrArg norm h'
    rw [norm_mul, Complex.norm_conj, norm_one] at this
    nlinarith [norm_nonneg u, norm_nonneg z]
  have hG : DifferentiableOn ℂ (fun u => P u / (1 - conj z * u) ^ 2) U :=
    (hP.mono inter_subset_left).div ((((differentiableOn_const _).sub
      ((differentiableOn_const _).mul differentiableOn_id))).pow 2) fun u hu => pow_ne_zero 2 hu.2
  have h0 : (∮ u in C(0, 1), P u / (1 - conj z * u) ^ 2) = 0 :=
    circleIntegral_eq_zero_of_differentiable_on_off_countable zero_le_one countable_empty
      (hG.continuousOn.mono hcU) fun u hu => (hG u (hcU (ball_subset_closedBall hu.1))).differentiableAt
        (hUo.mem_nhds (hcU (ball_subset_closedBall hu.1)))
  have key : ∀ θ : ℝ, deriv (circleMap 0 1) θ • (conj (P (circleMap 0 1 θ)) / (circleMap 0 1 θ - z) ^ 2) =
      conj (-(deriv (circleMap 0 1) θ • (P (circleMap 0 1 θ) / (1 - conj z * circleMap 0 1 θ) ^ 2))) := by
    intro θ
    rw [deriv_circleMap, smul_eq_mul, smul_eq_mul]
    set w := circleMap 0 1 θ with hw
    have hw1 : ‖w‖ = 1 := by simp [hw]
    have hwne : w ≠ 0 := by intro h; rw [h, norm_zero] at hw1; norm_num at hw1
    have hcw : conj w = w⁻¹ := by
      rw [Complex.inv_def, Complex.normSq_eq_norm_sq, hw1]; simp
    have hwz : w - z ≠ 0 := fun h => by rw [sub_eq_zero] at h; rw [h] at hw1; linarith
    have h1 : 1 - z * w⁻¹ ≠ 0 := by
      rw [show 1 - z * w⁻¹ = (w - z) / w by field_simp]
      exact div_ne_zero hwz hwne
    have hc0 : circleMap 0 1 θ * 0 = 0 := mul_zero _
    simp only [circleMap_zero, map_neg, map_mul, map_div₀, map_pow, map_sub, map_one, Complex.conj_conj,
      Complex.conj_I] at *
    rw [hcw]
    field_simp
  rw [circleIntegral, intervalIntegral.integral_congr (fun θ _ => key θ),
    intervalIntegral.integral_of_le Real.two_pi_pos.le, integral_conj, integral_neg,
    ← intervalIntegral.integral_of_le Real.two_pi_pos.le]
  change conj (-(∮ u in C(0, 1), P u / (1 - conj z * u) ^ 2)) = 0
  rw [h0, neg_zero, map_zero]

/-- Cauchy on `𝔻̄*`: the `K₂` row times a bounded holomorphic function on `|w| > r'` has zero circle integral. -/
theorem s36l_sp_ext_zero {f g Q : ℂ → ℂ} {r' : ℝ} (hr0 : 0 < r') (hr' : r' < 1)
    (hg : DifferentiableOn ℂ g {w | r' < ‖w‖})
    (hgi : InjOn g {w | r' < ‖w‖}) (hginf : Tendsto g (cocompact ℂ) (cocompact ℂ))
    (hg0 : ∀ w : ℂ, r' < ‖w‖ → g w ≠ 0) {z : ℂ}
    (hgz : ∀ w : ℂ, r' < ‖w‖ → g w ≠ f z) (hQ : DifferentiableOn ℂ Q {w | r' < ‖w‖}) {C : ℝ}
    (hC : ∀ w : ℂ, 2 ≤ ‖w‖ → ‖Q w‖ ≤ C) :
    (∮ w in C(0, 1), kerK2 f g z w * Q w) = 0 := by
  obtain ⟨G, hGd, hGi, hG0, hGe⟩ := s36l_sp_inv hr0 hg hgi hginf hg0
  obtain ⟨ρ, hρ1, hρ2, Q', hQ'd, hQ'e⟩ := s36l_sp_remove hr0 hr' hQ hC
  have hcb : closedBall (0 : ℂ) 1 ⊆ ball 0 ρ := fun w hw =>
    mem_ball_zero_iff.mpr (lt_of_le_of_lt (mem_closedBall_zero_iff.mp hw) hρ1)
  have hbb : ball (0 : ℂ) ρ ⊆ ball 0 r'⁻¹ := ball_subset_ball hρ2.le
  have hmem : ∀ u : ℂ, u ≠ 0 → ‖u‖ < r'⁻¹ → r' < ‖u⁻¹‖ := by
    intro u hu hus
    rw [norm_inv, lt_inv_comm₀ hr0 (norm_pos_iff.mpr hu)]; exact hus
  have hG1 : ∀ u ∈ ball (0 : ℂ) ρ, f z * G u - 1 ≠ 0 := by
    intro u hu
    have hus : ‖u‖ < r'⁻¹ := mem_ball_zero_iff.mp (hbb hu)
    by_cases hu0 : u = 0
    · rw [hu0, hG0]; simp
    · have ha := hg0 _ (hmem u hu0 hus)
      have hz := hgz _ (hmem u hu0 hus)
      rw [hGe u hu0 hus]
      intro h
      apply hz
      have h' : f z * (g u⁻¹)⁻¹ = 1 := by linear_combination h
      rw [mul_inv_eq_one₀ ha] at h'
      exact h'.symm
  have hG' : DifferentiableOn ℂ (deriv G) (ball 0 r'⁻¹) := (hGd.analyticOnNhd isOpen_ball).deriv.differentiableOn
  have hH : DifferentiableOn ℂ (fun u => 1 / π * (deriv f z * deriv G u / (f z * G u - 1) ^ 2) * Q' u)
      (ball 0 ρ) :=
    ((differentiableOn_const _).mul (((differentiableOn_const _).mul (hG'.mono hbb)).div
      ((((differentiableOn_const _).mul (hGd.mono hbb)).sub (differentiableOn_const _)).pow 2)
        fun u hu => pow_ne_zero 2 (hG1 u hu))).mul hQ'd
  have heq : EqOn (fun u => kerK2 f g z u⁻¹ * Q u⁻¹ * (u⁻¹) ^ 2)
      (fun u => 1 / π * (deriv f z * deriv G u / (f z * G u - 1) ^ 2) * Q' u) (sphere 0 1) := by
    intro u hu
    have hu1 : ‖u‖ = 1 := by simpa using hu
    have hu0 : u ≠ 0 := by intro h; rw [h, norm_zero] at hu1; norm_num at hu1
    have hus : ‖u‖ < r'⁻¹ := by rw [hu1]; exact (one_lt_inv₀ hr0).mpr hr'
    have hd := s36l_sp_inv_deriv hr0 hg hg0 hGe hu0 hus
    have ha := hg0 _ (hmem u hu0 hus)
    have hz := hgz _ (hmem u hu0 hus)
    simp only
    rw [hQ'e u hu0 (by rw [hu1]; exact hρ1)]
    have e1 : kerK2 f g z u⁻¹ * Q u⁻¹ * (u⁻¹) ^ 2 =
        1 / π * (deriv f z * (deriv g u⁻¹ * (u⁻¹) ^ 2) / (f z - g u⁻¹) ^ 2) * Q u⁻¹ := by
      unfold kerK2; ring
    rw [e1, hd, hGe u hu0 hus]
    have hzs : f z - g u⁻¹ ≠ 0 := sub_ne_zero.mpr hz.symm
    generalize g u⁻¹ = a at ha hzs ⊢
    generalize deriv G u = d
    have h3 : f z * a⁻¹ - 1 ≠ 0 := by
      rw [show f z * a⁻¹ - 1 = (f z - a) / a by field_simp]
      exact div_ne_zero hzs ha
    field_simp
  rw [s36l_sp_circ_inv, circleIntegral.integral_congr zero_le_one heq]
  exact circleIntegral_eq_zero_of_differentiable_on_off_countable zero_le_one countable_empty
    (hH.continuousOn.mono hcb) fun w hw => (hH w (hcb (ball_subset_closedBall hw.1))).differentiableAt
      (isOpen_ball.mem_nhds (hcb (ball_subset_closedBall hw.1)))

/-- (TT:4970–5040) The smooth case of Lemma 3.6, for an abstract complementary pair: `f` holomorphic and injective
on a disc `|z| < R` (`R > 1`) with `f(0) = 0`, `g` holomorphic and injective on `|z| > r` (`r < 1`) with `g(∞) = ∞`,
and `g(𝔻*) = ℂ \ f(𝔻̄)`. Then `K₁v̄₁ + K₂v̄₂ = -u₁` on `𝔻 \ {0}`, with `v = (𝒜(f), -𝒜(g))` and
`u₁ = 𝒜(f) - 2f'/f + 2/z`. -/
theorem s36l_smooth_pair {f g : ℂ → ℂ} {R r : ℝ} (hR : 1 < R) (hr : r < 1)
    (hf : DifferentiableOn ℂ f (ball 0 R)) (hfi : InjOn f (ball 0 R)) (hf0 : f 0 = 0)
    (hg : DifferentiableOn ℂ g {w | r < ‖w‖}) (hgi : InjOn g {w | r < ‖w‖})
    (hginf : Tendsto g (cocompact ℂ) (cocompact ℂ))
    (hc : g '' unitDiscExterior = (f '' closedBall 0 1)ᶜ)
    {z : ℂ} (hz : z ∈ unitDisc) (hz0 : z ≠ 0) :
    (∫ w in unitDisc, kerK1 f z w * conj (preSchwarzian f w)) +
        (∫ w in unitDiscExterior, kerK2 f g z w * conj (-preSchwarzian g w)) =
      -(preSchwarzian f z - 2 * deriv f z / f z + 2 / z) := by
  obtain ⟨PD, QD, hPDd, hQDd, hPD, hQD⟩ := s36l_sp_primD hR hf hfi hf0
  obtain ⟨r', hrr', hr0, hr'1, hgne, PE, QE, hPEd, hQEd, hPE, hQE, C, hC⟩ :=
    s36l_sp_primE hR hr hf hfi hf0 hg hgi hginf hc hz
  have hsub : {w : ℂ | r' < ‖w‖} ⊆ {w | r < ‖w‖} := fun w hw => lt_of_le_of_lt hrr' hw
  have hg' := hg.mono hsub
  have hgi' := hgi.mono hsub
  obtain ⟨γ, a, b, ha, hb, hbR, hγ, hγg, hS⟩ := s36l_sp_weld hR hrr' hr'1 hf hfi hg hgi hginf hc
  obtain ⟨k, hk⟩ := s36l_sp_subst ha hb hγ hS
  obtain ⟨c, hjump⟩ := s36l_sp_jump hR hr'1 hf hfi hf0 hg' hgi' (fun w hw => (hgne w hw).1) hPD hQD hPE hQE
    ha hb hbR hγ hγg hS
  rw [s36l_sp_I1 hR hf hfi hPD hz, s36l_sp_I2 hR hr0 hr'1 hf hg' hgi' hginf (fun w hw => (hgne w hw).1) hz (fun w hw => (hgne w hw).2) hPE
    (fun w hw => (hC w hw).1)]
  -- basic facts
  have hzR : z ∈ ball (0 : ℂ) R := mem_ball_zero_iff.mpr (lt_trans (mem_ball_zero_iff.mp hz) hR)
  have hz1 : ‖z‖ < 1 := mem_ball_zero_iff.mp hz
  have hU : IsOpen {w : ℂ | a < ‖w‖ ∧ ‖w‖ < b} :=
    (isOpen_lt continuous_const continuous_norm).inter (isOpen_lt continuous_norm continuous_const)
  have hE : IsOpen {w : ℂ | r' < ‖w‖} := isOpen_lt continuous_const continuous_norm
  have hS1 : ∀ w : ℂ, w ∈ sphere (0 : ℂ) 1 → ‖w‖ = 1 := fun w hw => by simpa using hw
  have hUw : ∀ w : ℂ, ‖w‖ = 1 → w ∈ {w : ℂ | a < ‖w‖ ∧ ‖w‖ < b} := fun w hw => ⟨by rw [hw]; exact ha, by rw [hw]; exact hb⟩
  have hEw : ∀ w : ℂ, ‖w‖ = 1 → r' < ‖w‖ := fun w hw => by rw [hw]; exact hr'1
  have hwz : ∀ w : ℂ, ‖w‖ = 1 → w - z ≠ 0 := fun w hw h => by
    rw [sub_eq_zero] at h; rw [h] at hw; linarith
  have hchain : ∀ w : ℂ, ‖w‖ = 1 → deriv g (γ w) * deriv γ w = deriv f w := by
    intro w hw
    have hwU := hUw w hw
    have hγw : DifferentiableAt ℂ γ w := (hγ w hwU).differentiableAt (hU.mem_nhds hwU)
    have hgw : DifferentiableAt ℂ g (γ w) :=
      (hg' (γ w) (hγg w hwU.1 hwU.2).1).differentiableAt (hE.mem_nhds (hγg w hwU.1 hwU.2).1)
    have heq : (g ∘ γ) =ᶠ[𝓝 w] f := by
      filter_upwards [hU.mem_nhds hwU] with u hu
      exact (hγg u hu.1 hu.2).2
    rw [← heq.deriv_eq, deriv_comp w hgw hγw]
  -- continuity on the sphere
  have hgc : ContinuousOn g {w : ℂ | r' < ‖w‖} := hg'.continuousOn
  have hg'c : ContinuousOn (deriv g) {w : ℂ | r' < ‖w‖} := (hg'.analyticOnNhd hE).deriv.continuousOn
  have hγc : ContinuousOn γ (sphere 0 1) := hγ.continuousOn.mono fun w hw => hUw w (hS1 w hw)
  have hγ'c : ContinuousOn (deriv γ) (sphere 0 1) :=
    (hγ.analyticOnNhd hU).deriv.continuousOn.mono fun w hw => hUw w (hS1 w hw)
  have hγE : MapsTo γ (sphere (0 : ℂ) 1) {w : ℂ | r' < ‖w‖} := fun w hw => by
    show r' < ‖γ w‖; rw [hS w (hS1 w hw)]; exact hr'1
  have hsE : sphere (0 : ℂ) 1 ⊆ {w : ℂ | r' < ‖w‖} := fun w hw => hEw w (hS1 w hw)
  have hsB : sphere (0 : ℂ) 1 ⊆ ball 0 R := fun w hw => mem_ball_zero_iff.mpr (by rw [hS1 w hw]; exact hR)
  have hHc : ContinuousOn (kerK2 f g z) {w : ℂ | r' < ‖w‖} := by
    intro w hw
    unfold kerK2
    refine (continuousWithinAt_const.mul ((continuousWithinAt_const.mul (hg'c w hw)).div
      ((continuousWithinAt_const.sub (hgc w hw)).pow 2) ?_))
    exact pow_ne_zero 2 (sub_ne_zero.mpr (hgne w hw).2.symm)
  obtain ⟨K, hK1, hKe⟩ := s36l_sp_K1_holo hf hfi hzR
  have hKs : EqOn K (kerK1 f z) (sphere 0 1) := fun w hw => hKe w (hsB hw) (fun h => hwz w (hS1 w hw) (by rw [h, sub_self]))
  have hK1c : ContinuousOn (kerK1 f z) (sphere 0 1) := (hK1.continuousOn.mono hsB).congr hKs.symm
  have hPDc : ContinuousOn (fun w => conj (PD w)) (sphere 0 1) :=
    (continuous_conj.comp_continuousOn hPDd.continuousOn).mono hsB
  have hQDc : ContinuousOn QD (sphere 0 1) := hQDd.continuousOn.mono hsB
  have hPEc : ContinuousOn (fun w => conj (PE w)) {w : ℂ | r' < ‖w‖} :=
    continuous_conj.comp_continuousOn hPEd.continuousOn
  have hinvc : ContinuousOn (fun w : ℂ => ((w - z) ^ 2)⁻¹) (sphere 0 1) := fun w hw =>
    (((continuous_id.sub continuous_const).pow 2).continuousAt.inv₀
      (pow_ne_zero 2 (hwz w (hS1 w hw)))).continuousWithinAt
  -- k = 1
  have hk1 : (k : ℂ) = 1 := by
    have hΨ : ContinuousOn (fun ξ => deriv g ξ / (g ξ - f z)) (sphere 0 1) := fun w hw =>
      ((hg'c w (hsE hw)).div (hgc.sub continuousOn_const w (hsE hw))
        (sub_ne_zero.mpr (hgne w (hsE hw)).2)).mono hsE
    have h := hk _ hΨ
    rw [s36l_sp_windE hr0 hr'1 hg' hgi' hginf (fun w hw => (hgne w hw).1) (fun w hw => (hgne w hw).2)] at h
    have hl : (∮ w in C(0, 1), deriv g (γ w) / (g (γ w) - f z) * deriv γ w) =
        ∮ w in C(0, 1), deriv f w / (f w - f z) := by
      refine circleIntegral.integral_congr zero_le_one fun w hw => ?_
      have hw1 := hS1 w hw
      have hwU := hUw w hw1
      rw [(hγg w hwU.1 hwU.2).2, ← hchain w hw1]
      ring
    rw [hl, s36l_sp_windD hR hf hfi hz] at h
    have hpi : (2 * π * I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero, I_ne_zero]
    exact (mul_right_cancel₀ hpi (by rw [one_mul]; exact h : (1 : ℂ) * (2 * π * I) = (k : ℂ) * (2 * π * I))).symm
  -- the substituted K₂ boundary terms
  have hA2 : (∮ w in C(0, 1), kerK2 f g z w * conj (PE w)) =
      ∮ w in C(0, 1), kerK2 f g z (γ w) * conj (PE (γ w)) * deriv γ w := by
    have h := hk (fun ξ => kerK2 f g z ξ * conj (PE ξ)) ((hHc.mul hPEc).mono hsE)
    simp only [hk1, one_mul] at h
    exact h.symm
  have hB2 : (∮ w in C(0, 1), kerK2 f g z (γ w) * QE (γ w) * deriv γ w) = 0 := by
    have h := hk (fun ξ => kerK2 f g z ξ * QE ξ) ((hHc.mul hQEd.continuousOn).mono hsE)
    simp only [hk1, one_mul] at h
    rw [h, s36l_sp_ext_zero hr0 hr'1 hg' hgi' hginf (fun w hw => (hgne w hw).1) (fun w hw => (hgne w hw).2) hQEd (fun w hw => (hC w hw).2)]
  -- pointwise identity on S¹
  set m : ℂ → ℂ := fun w => 1 / π * (deriv f z * deriv f w / (f z - f w) ^ 2) with hm
  have hHm : ∀ w : ℂ, ‖w‖ = 1 → kerK2 f g z (γ w) * deriv γ w = m w := by
    intro w hw
    have hwU := hUw w hw
    simp only [kerK2, hm, (hγg w hwU.1 hwU.2).2, ← hchain w hw]
    ring
  have hKm : ∀ w : ℂ, ‖w‖ = 1 → kerK1 f z w + m w = 1 / π * ((w - z) ^ 2)⁻¹ := by
    intro w hw
    have hzw : z ≠ w := fun h => hwz w hw (by rw [h, sub_self])
    rw [kerK1_of_ne f hzw, hm]
    have : (z - w) ^ 2 = (w - z) ^ 2 := by ring
    rw [this]
    ring
  have hpt : EqOn (fun w => kerK1 f z w * conj (PD w) + kerK2 f g z (γ w) * conj (PE (γ w)) * deriv γ w)
      (fun w => 1 / π * (((w - z) ^ 2)⁻¹ * conj (PD w)) - 1 / π * (((w - z) ^ 2)⁻¹ * QD w) +
        kerK1 f z w * QD w + kerK2 f g z (γ w) * QE (γ w) * deriv γ w +
          c * (1 / π * ((w - z) ^ 2)⁻¹ - kerK1 f z w)) (sphere 0 1) := by
    intro w hw
    have hw1 := hS1 w hw
    have h1 := hjump w hw1
    have h2 := hHm w hw1
    have h3 := hKm w hw1
    have hPE' : conj (PE (γ w)) = conj (PD w) - QD w + QE (γ w) + c := by linear_combination h1
    have e1 : kerK2 f g z (γ w) * conj (PE (γ w)) * deriv γ w = m w * conj (PE (γ w)) := by
      rw [← h2]; ring
    have e2 : kerK2 f g z (γ w) * QE (γ w) * deriv γ w = m w * QE (γ w) := by rw [← h2]; ring
    have e3 : m w = 1 / π * ((w - z) ^ 2)⁻¹ - kerK1 f z w := by linear_combination h3
    simp only
    rw [e1, e2, hPE', e3]
    ring
  -- integrate
  have ci : ∀ {F : ℂ → ℂ}, ContinuousOn F (sphere 0 1) → CircleIntegrable F 0 1 :=
    fun h => h.circleIntegrable zero_le_one
  have hT1 : ContinuousOn (fun w => 1 / π * (((w - z) ^ 2)⁻¹ * conj (PD w))) (sphere 0 1) :=
    continuousOn_const.mul (hinvc.mul hPDc)
  have hT2 : ContinuousOn (fun w => 1 / π * (((w - z) ^ 2)⁻¹ * QD w)) (sphere 0 1) :=
    continuousOn_const.mul (hinvc.mul hQDc)
  have hT3 : ContinuousOn (fun w => kerK1 f z w * QD w) (sphere 0 1) := hK1c.mul hQDc
  have hT4 : ContinuousOn (fun w => kerK2 f g z (γ w) * QE (γ w) * deriv γ w) (sphere 0 1) :=
    ((hHc.comp hγc hγE).mul (hQEd.continuousOn.comp hγc hγE)).mul hγ'c
  have hT5 : ContinuousOn (fun w => c * (1 / π * ((w - z) ^ 2)⁻¹ - kerK1 f z w)) (sphere 0 1) :=
    continuousOn_const.mul ((continuousOn_const.mul hinvc).sub hK1c)
  have hL1 : ContinuousOn (fun w => kerK1 f z w * conj (PD w)) (sphere 0 1) := hK1c.mul hPDc
  have hL2 : ContinuousOn (fun w => kerK2 f g z (γ w) * conj (PE (γ w)) * deriv γ w) (sphere 0 1) :=
    ((hHc.comp hγc hγE).mul (hPEc.comp hγc hγE)).mul hγ'c
  have hsum := circleIntegral.integral_congr zero_le_one hpt
  have e0 := circleIntegral.integral_add (c := 0) (R := 1)
    (f := fun w => kerK1 f z w * conj (PD w)) (g := fun w => kerK2 f g z (γ w) * conj (PE (γ w)) * deriv γ w)
    (ci hL1) (ci hL2)
  have e5 := circleIntegral.integral_add (c := 0) (R := 1)
    (f := fun w => 1 / π * (((w - z) ^ 2)⁻¹ * conj (PD w)) - 1 / π * (((w - z) ^ 2)⁻¹ * QD w) + kerK1 f z w * QD w + kerK2 f g z (γ w) * QE (γ w) * deriv γ w) (g := fun w => c * (1 / π * ((w - z) ^ 2)⁻¹ - kerK1 f z w))
    (ci (((hT1.sub hT2).add hT3).add hT4)) (ci hT5)
  have e4 := circleIntegral.integral_add (c := 0) (R := 1)
    (f := fun w => 1 / π * (((w - z) ^ 2)⁻¹ * conj (PD w)) - 1 / π * (((w - z) ^ 2)⁻¹ * QD w) + kerK1 f z w * QD w) (g := fun w => kerK2 f g z (γ w) * QE (γ w) * deriv γ w) (ci ((hT1.sub hT2).add hT3)) (ci hT4)
  have e3 := circleIntegral.integral_add (c := 0) (R := 1)
    (f := fun w => 1 / π * (((w - z) ^ 2)⁻¹ * conj (PD w)) - 1 / π * (((w - z) ^ 2)⁻¹ * QD w)) (g := fun w => kerK1 f z w * QD w) (ci (hT1.sub hT2)) (ci hT3)
  have e2 := circleIntegral.integral_sub (c := 0) (R := 1)
    (f := fun w => 1 / π * (((w - z) ^ 2)⁻¹ * conj (PD w))) (g := fun w => 1 / π * (((w - z) ^ 2)⁻¹ * QD w)) (ci hT1) (ci hT2)
  beta_reduce at e0 e5 e4 e3 e2
  rw [e0, e5, e4, e3, e2] at hsum
  -- the five boundary integrals
  have hz2 : (∮ w in C(0, 1), ((w - z) ^ 2)⁻¹) = 0 := by
    simpa using! circleIntegral.integral_sub_zpow_of_ne (by decide : (-2 : ℤ) ≠ -1) 0 z 1
  have hcb : closedBall (0 : ℂ) 1 ⊆ ball 0 R := fun w hw =>
    mem_ball_zero_iff.mpr (lt_of_le_of_lt (mem_closedBall_zero_iff.mp hw) hR)
  have hcauchy : ∀ {F : ℂ → ℂ}, DifferentiableOn ℂ F (ball 0 R) → (∮ w in C(0, 1), F w) = 0 := by
    intro F hF
    exact circleIntegral_eq_zero_of_differentiable_on_off_countable zero_le_one countable_empty
      (hF.continuousOn.mono hcb) fun w hw => (hF w (hcb (ball_subset_closedBall hw.1))).differentiableAt
        (isOpen_ball.mem_nhds (hcb (ball_subset_closedBall hw.1)))
  have i1 : (∮ w in C(0, 1), 1 / π * (((w - z) ^ 2)⁻¹ * conj (PD w))) = 0 := by
    rw [circleIntegral.integral_const_mul]
    have := s36l_sp_conj_zero hR hPDd hz
    simp only [div_eq_mul_inv] at this
    rw [show (∮ w in C(0, 1), ((w - z) ^ 2)⁻¹ * conj (PD w)) = ∮ w in C(0, 1), conj (PD w) * ((w - z) ^ 2)⁻¹ by
      simp only [mul_comm], this, mul_zero]
  have i2 : (∮ w in C(0, 1), 1 / π * (((w - z) ^ 2)⁻¹ * QD w)) = 1 / π * (2 * π * I * deriv QD z) := by
    rw [circleIntegral.integral_const_mul]
    have h := two_pi_I_inv_smul_circleIntegral_sub_sq_inv_smul_of_differentiable isOpen_ball hcb hQDd
      (mem_ball_zero_iff.mpr hz1 : z ∈ ball (0 : ℂ) 1)
    simp only [smul_eq_mul] at h
    have hpi : (2 * π * I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero, I_ne_zero]
    rw [← h, mul_inv_cancel_left₀ hpi]
  have i3 : (∮ w in C(0, 1), kerK1 f z w * QD w) = 0 := by
    have e : (∮ w in C(0, 1), kerK1 f z w * QD w) = ∮ w in C(0, 1), K w * QD w :=
      circleIntegral.integral_congr zero_le_one fun w hw => by simp only [hKs hw]
    rw [e]
    exact hcauchy (hK1.mul hQDd)
  have i5 : (∮ w in C(0, 1), c * (1 / π * ((w - z) ^ 2)⁻¹ - kerK1 f z w)) = 0 := by
    have e := circleIntegral.integral_sub (c := 0) (R := 1) (f := fun w => 1 / π * ((w - z) ^ 2)⁻¹)
      (g := fun w => kerK1 f z w) (ci (continuousOn_const.mul hinvc)) (ci hK1c)
    beta_reduce at e
    rw [circleIntegral.integral_const_mul, e, circleIntegral.integral_const_mul, hz2,
      (circleIntegral.integral_congr zero_le_one hKs).symm.trans (hcauchy hK1)]
    ring
  rw [i1, i2, i3, hB2, i5, ← hA2] at hsum
  have hdQ : deriv QD z = preSchwarzian f z - 2 * deriv f z / f z + 2 / z := (hQD z hzR hz0).deriv
  rw [← hdQ, ← mul_add, hsum]
  have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  field_simp
  ring

/-! ### General welding pairs -/

/-- The two sides of the welding pair are complementary, and `𝗀(∞) = ∞` (TT:823). -/
theorem s36l_complement {κ : LinfStar} (hκ : κ ∈ LinfStarBall) :
    gsans κ '' unitDiscExterior = (fsans κ '' closedBall 0 1)ᶜ ∧
      Tendsto (gsans κ) (cocompact ℂ) (cocompact ℂ) := by
  obtain ⟨-, -, -, -, hext⟩ := hc6_welding_quasidisc hκ
  have hcont : ContinuousOn (fsans κ) (closedBall 0 1) := by
    intro z hz
    rw [S2C.s2c_fsans_eq hκ]
    exact (s5e_fB_continuousAt hκ (mem_closedBall_zero_iff.mp hz)).continuousWithinAt
  have hcl : closure (fsans κ '' unitDisc) = fsans κ '' closedBall 0 1 := by
    apply subset_antisymm
    · exact closure_minimal (image_mono ball_subset_closedBall)
        ((isCompact_closedBall 0 1).image_of_continuousOn hcont).isClosed
    · have h := (show ContinuousOn (fsans κ) (closure (ball (0 : ℂ) 1)) by
        rw [closure_ball 0 one_ne_zero]; exact hcont).image_closure
      rwa [closure_ball 0 one_ne_zero] at h
  refine ⟨hext.trans (by rw [hcl]), ?_⟩
  rw [S2C.s2c_gsans_eq hκ]
  exact (gMu_isWelding hκ).2.2.2.2.2.2.2.2

/-- If `κ` vanishes on `1 < |z| < R`, `fsans κ` is holomorphic and injective on a disc `|z| < R'`, `R' > 1`: the plane
solution of Model B is conformal on `|z| < R`, and its Möbius normalization has no pole on `𝔻̄`. -/
theorem s36l_rf_fsans {κ : LinfStar} (hκ : κ ∈ LinfStarBall) {R : ℝ} (hR : 1 < R)
    (h0 : ∀ᵐ z ∂(volume.restrict unitDiscExterior), ‖z‖ < R → (κ : ℂ → ℂ) z = 0) :
    ∃ R' : ℝ, 1 < R' ∧ DifferentiableOn ℂ (fsans κ) (ball 0 R') ∧ InjOn (fsans κ) (ball 0 R') ∧
      ∀ z ∈ ball (0 : ℂ) R', wB κ z = (fsans κ z : ExtPlane) := by
  obtain ⟨M, hM, W, hW, hfinite, -, -, -, -⟩ := (wB_spec hκ).1
  obtain ⟨a, b, c, d, hdet, rfl⟩ := hM
  obtain ⟨⟨K, hK⟩, -, -, -, hchar⟩ := hW
  have hEm : MeasurableSet unitDiscExterior := (isOpen_lt continuous_const continuous_norm).measurableSet
  have h0' := (ae_restrict_iff' hEm).mp h0
  have hzero : ∀ᵐ z ∂(volume.restrict (ball (0 : ℂ) R)), complexDilatation W z = 0 := by
    filter_upwards [ae_restrict_of_ae hchar, self_mem_ae_restrict measurableSet_ball, ae_restrict_of_ae h0']
      with z hz hzB hz0
    rw [hz, extB]
    by_cases hzE : z ∈ unitDiscExterior
    · rw [indicator_of_mem hzE]
      exact hz0 hzE (mem_ball_zero_iff.mp hzB)
    · exact indicator_of_notMem hzE _
  have hWd : DifferentiableOn ℂ W (ball 0 R) :=
    nx_differentiableOn_of_dilatation_zero (nx_isKQC_restrict hK isOpen_ball (subset_univ _)) hzero
  have hden : ∀ z : ℂ, ‖z‖ ≤ 1 → c * W z + d ≠ 0 := by
    intro z hz he
    apply s5e_wB_finite hκ hz
    rw [hfinite z, mobiusExt_coe_of_eq_zero he]
  set O : Set ℂ := ball 0 R ∩ {z | c * W z + d ≠ 0} with hO
  have hOo : IsOpen O :=
    ((continuous_const.mul continuous_id).add continuous_const |>.continuousOn.comp hWd.continuousOn
      (mapsTo_univ _ _)).isOpen_inter_preimage isOpen_ball (isOpen_ne_fun continuous_id continuous_const) |>
      fun h => by simpa [hO, Set.preimage, Function.comp_def] using h
  have hcO : closedBall (0 : ℂ) 1 ⊆ O := fun z hz =>
    ⟨mem_ball_zero_iff.mpr (lt_of_le_of_lt (mem_closedBall_zero_iff.mp hz) hR),
      hden z (mem_closedBall_zero_iff.mp hz)⟩
  obtain ⟨δ, hδ, hδO⟩ := (isCompact_closedBall (0 : ℂ) 1).exists_cthickening_subset_open hOo hcO
  rw [cthickening_closedBall hδ.le zero_le_one] at hδO
  have hBO : ball (0 : ℂ) (1 + δ / 2) ⊆ O := fun z hz => hδO (mem_closedBall_zero_iff.mpr (by
    have := mem_ball_zero_iff.mp hz; linarith))
  have hrep : ∀ z ∈ O, fsans κ z = (a * W z + b) / (c * W z + d) := by
    intro z hz
    rw [S2C.s2c_fsans_eq hκ, fB, hfinite z, mobiusExt_coe hz.2]
    rfl
  have hlift : ∀ z ∈ O, wB κ z = (fsans κ z : ExtPlane) := by
    intro z hz
    rw [hrep z hz, hfinite z, mobiusExt_coe hz.2]
    rfl
  refine ⟨1 + δ / 2, by linarith, ?_, ?_, ?_⟩
  · intro z hz
    have hzO := hBO hz
    have hd : DifferentiableAt ℂ (fun z => (a * W z + b) / (c * W z + d)) z := by
      have hWz : DifferentiableAt ℂ W z := (hWd z hzO.1).differentiableAt (isOpen_ball.mem_nhds hzO.1)
      exact ((hWz.const_mul a).add_const b).div ((hWz.const_mul c).add_const d) hzO.2
    refine (hd.congr_of_eventuallyEq ?_).differentiableWithinAt
    filter_upwards [hOo.mem_nhds hzO] with u hu
    exact hrep u hu
  · intro x hx y hy hxy
    apply OnePoint.coe_injective
    apply (wB_bijective κ).injective
    rw [hlift x (hBO hx), hlift y (hBO hy), hxy]
  · exact fun z hz => hlift z (hBO hz)

/-- If `κ` vanishes on `1 < |z| < R`, `gsans κ` extends holomorphically and injectively to `|ξ| > r`, `r < 1`:
`𝗀 = w^κ ∘ w_κ⁻¹` on `𝔻*` (welding factorization), and `w_κ` is conformal near `S¹`. -/
theorem s36l_rf_gsans {κ : LinfStar} (hκ : κ ∈ LinfStarBall) {R : ℝ} (hR : 1 < R)
    (h0 : ∀ᵐ z ∂(volume.restrict unitDiscExterior), ‖z‖ < R → (κ : ℂ → ℂ) z = 0) :
    ∃ r < 1, ∃ G : ℂ → ℂ, EqOn G (gsans κ) unitDiscExterior ∧
      DifferentiableOn ℂ G {w | r < ‖w‖} ∧ InjOn G {w | r < ‖w‖} := by
  obtain ⟨R1, hR1, hfd, -, hlift⟩ := s36l_rf_fsans hκ hR h0
  obtain ⟨M, ⟨a, b, c, d, hdet, rfl⟩, W, hW, hwf, -, -, -, -⟩ := wA_spec hκ
  obtain ⟨⟨K, hK⟩, -, -, -, hchar⟩ := hW
  have hEm : MeasurableSet unitDiscExterior := (isOpen_lt continuous_const continuous_norm).measurableSet
  have h0' := (ae_restrict_iff' hEm).mp h0
  have hR0 : 0 < R := by linarith
  set Ann : Set ℂ := {z : ℂ | R⁻¹ < ‖z‖ ∧ ‖z‖ < R} with hAnn
  have hAo : IsOpen Ann :=
    (isOpen_lt continuous_const continuous_norm).inter (isOpen_lt continuous_norm continuous_const)
  have hzero : ∀ᵐ z ∂(volume.restrict Ann), complexDilatation W z = 0 := by
    filter_upwards [ae_restrict_of_ae hchar, self_mem_ae_restrict hAo.measurableSet, ae_restrict_of_ae h0',
      ae_restrict_of_ae (ae_refl h0')] with z hz hzA hz0 hzr
    rw [hz, extA]
    by_cases h1 : 1 < ‖z‖
    · rw [if_pos h1]; exact hz0 h1 hzA.2
    · rw [if_neg h1]
      by_cases h2 : ‖z‖ < 1
      · rw [if_pos h2]
        have hz0' : z ≠ 0 := fun h => by
          have := hzA.1; rw [h, norm_zero] at this; linarith [inv_pos.mpr hR0]
        have hr1 : 1 < ‖refl z‖ := by
          rw [norm_refl]; exact (one_lt_inv₀ (norm_pos_iff.mpr hz0')).mpr h2
        have hrR : ‖refl z‖ < R := by
          rw [norm_refl]; rw [inv_lt_comm₀ (norm_pos_iff.mpr hz0') hR0]; exact hzA.1
        rw [hzr hr1 hrR]; simp
      · rw [if_neg h2]
  have hWd : DifferentiableOn ℂ W Ann :=
    nx_differentiableOn_of_dilatation_zero (nx_isKQC_restrict hK hAo (subset_univ _)) hzero
  have hWi : InjOn W univ := hK.2.2.1.2.1
  have hden : ∀ z : ℂ, ‖z‖ = 1 → c * W z + d ≠ 0 := by
    intro z hz he
    obtain ⟨u, -, hu⟩ := wAS_maps_circle hκ hz
    rw [hwf z, mobiusExt_coe_of_eq_zero he] at hu
    exact OnePoint.infty_ne_coe _ hu
  -- the domain `O` around `S¹` where `w_κ` is conformal and lands in the disc of `fsans`
  set O : Set ℂ := (Ann ∩ ball 0 R1) ∩ {z | c * W z + d ≠ 0} with hO
  have hOo : IsOpen O := by
    rw [isOpen_iff_mem_nhds]
    intro z hz
    have hWc : ContinuousAt (fun z => c * W z + d) z :=
      (((hWd z hz.1.1).differentiableAt (hAo.mem_nhds hz.1.1)).continuousAt.const_mul c).add continuousAt_const
    filter_upwards [(hAo.inter isOpen_ball).mem_nhds hz.1, hWc.eventually_ne hz.2] with u hu1 hu2
    exact ⟨hu1, hu2⟩
  have hsO : sphere (0 : ℂ) 1 ⊆ O := by
    intro z hz
    have hz1 : ‖z‖ = 1 := by simpa using hz
    refine ⟨⟨⟨by rw [hz1]; exact inv_lt_one_of_one_lt₀ hR, by rw [hz1]; exact hR⟩,
      mem_ball_zero_iff.mpr (by rw [hz1]; exact hR1)⟩, hden z hz1⟩
  set φ : ℂ → ℂ := fun z => (a * W z + b) / (c * W z + d) with hφ
  have hφS : ∀ z ∈ O, wAS κ z = (φ z : ExtPlane) := fun z hz => by
    rw [hwf z, mobiusExt_coe hz.2]; rfl
  have hφd : DifferentiableOn ℂ φ O := fun z hz =>
    ((((hWd z hz.1.1).differentiableAt (hAo.mem_nhds hz.1.1)).const_mul a |>.add_const b).div
      (((hWd z hz.1.1).differentiableAt (hAo.mem_nhds hz.1.1)).const_mul c |>.add_const d) hz.2).differentiableWithinAt
  have hφi : InjOn φ O := by
    intro x hx y hy hxy
    apply OnePoint.coe_injective
    apply (wAS_bijective κ).injective
    rw [hφS x hx, hφS y hy, hxy]
  have hconf : IsConformalOnto φ O (φ '' O) := ⟨hφd, hφi, rfl⟩
  have hVo : IsOpen (φ '' O) := hconf.isOpen hOo
  set ψ : ℂ → ℂ := Function.invFunOn φ O with hψ
  have hψd : DifferentiableOn ℂ ψ (φ '' O) := (hconf.symm hOo).1
  have hsV : sphere (0 : ℂ) 1 ⊆ φ '' O := by
    intro u hu
    have hu1 : ‖u‖ = 1 := by simpa using hu
    have hmem : (u : ExtPlane) ∈ wAS κ '' toExt unitCircle := by
      rw [(wA_mapsTo hκ).2.2]; exact ⟨u, by simpa [unitCircle] using hu1, rfl⟩
    obtain ⟨z', ⟨z, hz, rfl⟩, hzu⟩ := hmem
    have hz1 : ‖z‖ = 1 := by simpa [unitCircle] using hz
    have hzO := hsO (by simpa using hz1)
    refine ⟨z, hzO, ?_⟩
    apply OnePoint.coe_injective
    rw [← hφS z hzO]; exact hzu
  obtain ⟨δ, hδ, hδV⟩ := (isCompact_sphere (0 : ℂ) 1).exists_cthickening_subset_open hVo hsV
  -- in `φ(O)`, `wAS⁻¹ ξ = ψ ξ`, and `w^κ` is finite there
  have hinvψ : ∀ ξ ∈ φ '' O, Function.invFun (wAS κ) (ξ : ExtPlane) = (ψ ξ : ExtPlane) := by
    intro ξ hξ
    have hψO : ψ ξ ∈ O := Function.invFunOn_mem hξ
    have hφψ : φ (ψ ξ) = ξ := Function.invFunOn_eq hξ
    apply (wAS_bijective κ).injective
    rw [Function.rightInverse_invFun (wAS_bijective κ).surjective, hφS _ hψO, hφψ]
  have hψB : ∀ ξ ∈ φ '' O, ψ ξ ∈ ball (0 : ℂ) R1 := fun ξ hξ => (Function.invFunOn_mem hξ).1.2
  set G : ℂ → ℂ := fun ξ => if ξ ∈ φ '' O then fsans κ (ψ ξ) else gsans κ ξ with hG
  have hGw : ∀ ξ : ℂ, ξ ∈ φ '' O ∨ ξ ∈ unitDiscExterior →
      (G ξ : ExtPlane) = wB κ (Function.invFun (wAS κ) (ξ : ExtPlane)) := by
    intro ξ hξ
    by_cases hV : ξ ∈ φ '' O
    · simp only [hG, if_pos hV]
      rw [hinvψ ξ hV, hlift _ (hψB ξ hV)]
    · have hE : ξ ∈ unitDiscExterior := hξ.resolve_left hV
      simp only [hG, if_neg hV]
      rw [S2C.s2c_gsans_eq hκ]
      exact gMu_sphere_factorization hκ hE
  have hEqE : EqOn G (gsans κ) unitDiscExterior := by
    intro ξ hξ
    apply OnePoint.coe_injective
    rw [hGw ξ (Or.inr hξ), S2C.s2c_gsans_eq hκ, gMu_sphere_factorization hκ hξ]
  set r : ℝ := max (1 - δ / 2) (1 / 2) with hr
  have hin : ∀ ξ : ℂ, r < ‖ξ‖ → ‖ξ‖ ≤ 1 → ξ ∈ φ '' O := by
    intro ξ h1 h2
    have hξ0 : 0 < ‖ξ‖ := lt_of_le_of_lt (by positivity) h1
    set v : ℂ := ((‖ξ‖⁻¹ : ℝ) : ℂ) * ξ with hv
    have hvs : v ∈ sphere (0 : ℂ) 1 := by
      rw [mem_sphere_zero_iff_norm, hv, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
      field_simp
    have hdist : dist ξ v ≤ δ := by
      rw [dist_eq_norm, hv, show ξ - ((‖ξ‖⁻¹ : ℝ) : ℂ) * ξ = ((1 - ‖ξ‖⁻¹ : ℝ) : ℂ) * ξ by push_cast; ring,
        norm_mul, Complex.norm_real, Real.norm_eq_abs]
      have : |1 - ‖ξ‖⁻¹| * ‖ξ‖ = |‖ξ‖ - 1| := by
        rw [← abs_of_pos hξ0, ← abs_mul, abs_of_pos hξ0]
        congr 1; field_simp
      rw [this, abs_le]
      have : 1 - δ / 2 < ‖ξ‖ := lt_of_le_of_lt (le_max_left _ _) h1
      constructor <;> linarith
    exact hδV (Metric.mem_cthickening_of_dist_le ξ v δ _ hvs hdist)
  have hcase : ∀ ξ : ℂ, r < ‖ξ‖ → ξ ∈ φ '' O ∨ ξ ∈ unitDiscExterior := by
    intro ξ hξ
    by_cases h : ‖ξ‖ ≤ 1
    · exact Or.inl (hin ξ hξ h)
    · exact Or.inr (not_le.mp h)
  refine ⟨r, max_lt (by linarith) (by norm_num), G, hEqE, ?_, ?_⟩
  · intro ξ hξ
    rcases hcase ξ hξ with hV | hE
    · have hd : DifferentiableAt ℂ (fun ξ => fsans κ (ψ ξ)) ξ :=
        ((hfd _ (hψB ξ hV)).differentiableAt (isOpen_ball.mem_nhds (hψB ξ hV))).comp ξ
          ((hψd ξ hV).differentiableAt (hVo.mem_nhds hV))
      refine (hd.congr_of_eventuallyEq ?_).differentiableWithinAt
      filter_upwards [hVo.mem_nhds hV] with u hu
      show (if u ∈ φ '' O then fsans κ (ψ u) else gsans κ u) = fsans κ (ψ u)
      rw [if_pos hu]
    · have hEo : IsOpen unitDiscExterior := isOpen_lt continuous_const continuous_norm
      have hd : DifferentiableAt ℂ (gsans κ) ξ :=
        ((s2c_facts hκ).2.2.2.2.1 ξ hE).differentiableAt (hEo.mem_nhds hE)
      refine (hd.congr_of_eventuallyEq ?_).differentiableWithinAt
      filter_upwards [hEo.mem_nhds hE] with u hu
      exact hEqE hu
  · intro x hx y hy hxy
    have h1 := hGw x (hcase x hx)
    have h2 := hGw y (hcase y hy)
    have := (wB_bijective κ).injective (h1.symm.trans ((congrArg _ hxy).trans h2))
    have e := congrArg (wAS κ) this
    rw [Function.rightInverse_invFun (wAS_bijective κ).surjective,
      Function.rightInverse_invFun (wAS_bijective κ).surjective] at e
    exact OnePoint.coe_injective e

/-- If `κ` vanishes on the annulus `1 < |z| < R`, then `𝖿 = fsans κ` is holomorphic and injective on a disc `|z| < R'`,
`R' > 1` (the normalization pole of `w^κ` lies outside `𝔻̄` but possibly inside `|z| < R`), and
`𝗀 = gsans κ` extends holomorphically and injectively across `S¹` (Schwarz reflection for the self-map `w_κ` of `𝔻*`,
which is conformal near `S¹`). -/
theorem s36l_reflect {κ : LinfStar} (hκ : κ ∈ LinfStarBall) {R : ℝ} (hR : 1 < R)
    (h0 : ∀ᵐ z ∂(volume.restrict unitDiscExterior), ‖z‖ < R → (κ : ℂ → ℂ) z = 0) :
    (∃ R' : ℝ, 1 < R' ∧ DifferentiableOn ℂ (fsans κ) (ball 0 R') ∧ InjOn (fsans κ) (ball 0 R')) ∧
      ∃ r < 1, ∃ G : ℂ → ℂ, EqOn G (gsans κ) unitDiscExterior ∧
        DifferentiableOn ℂ G {w | r < ‖w‖} ∧ InjOn G {w | r < ‖w‖} := by
  obtain ⟨R', hR', hfd, hfi, -⟩ := s36l_rf_fsans hκ hR h0
  exact ⟨⟨R', hR', hfd, hfi⟩, s36l_rf_gsans hκ hR h0⟩

/-- The Schwarzian of a locally injective holomorphic map is holomorphic. -/
theorem s36l_schwarzian_holo {f : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U) (hf : DifferentiableOn ℂ f U)
    (hf' : ∀ z ∈ U, deriv f z ≠ 0) : DifferentiableOn ℂ (schwarzianHol f) U := by
  have h1 : DifferentiableOn ℂ (deriv f) U := (hf.analyticOnNhd hU).deriv.differentiableOn
  have h2 : DifferentiableOn ℂ (deriv (deriv f)) U := (h1.analyticOnNhd hU).deriv.differentiableOn
  have hq : DifferentiableOn ℂ (fun w => deriv (deriv f) w / deriv f w) U := h2.div h1 hf'
  have hq' : DifferentiableOn ℂ (deriv fun w => deriv (deriv f) w / deriv f w) U :=
    (hq.analyticOnNhd hU).deriv.differentiableOn
  unfold schwarzianHol
  exact hq'.sub ((differentiableOn_const _).mul (hq.pow 2))

/-- A function holomorphic on a disc `|z| < R'`, `R' > 1`, lies in `A₂(𝔻)`. -/
theorem s36l_A2_of_ball {φ : ℂ → ℂ} {R' : ℝ} (hR' : 1 < R') (hφ : DifferentiableOn ℂ φ (ball 0 R')) :
    φ ∈ A2fun unitDisc := by
  have hcb : closedBall (0 : ℂ) 1 ⊆ ball 0 R' := fun z hz =>
    mem_ball_zero_iff.mpr (lt_of_le_of_lt (mem_closedBall_zero_iff.mp hz) hR')
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : ℂ) 1).exists_bound_of_continuousOn (hφ.continuousOn.mono hcb)
  refine ⟨hφ.mono (ball_subset_closedBall.trans hcb), ?_⟩
  unfold normA2
  have hfin : (∫⁻ z in unitDisc, (‖φ z‖₊ : ℝ≥0∞) ^ 2 * ENNReal.ofReal (rho z)⁻¹) < ∞ := by
    have hle : (∫⁻ z in unitDisc, (‖φ z‖₊ : ℝ≥0∞) ^ 2 * ENNReal.ofReal (rho z)⁻¹) ≤
        ∫⁻ _z in unitDisc, (ENNReal.ofReal C) ^ 2 := by
      refine setLIntegral_mono measurable_const fun z hz => ?_
      have hz1 : ‖z‖ < 1 := mem_ball_zero_iff.mp hz
      have hρ : (rho z)⁻¹ ≤ 1 := by
        unfold rho
        rw [inv_div]
        have h0 : 0 ≤ ‖z‖ ^ 2 := by positivity
        have h1 : ‖z‖ ^ 2 < 1 := by nlinarith [norm_nonneg z]
        rw [div_le_one (by norm_num)]
        nlinarith
      have hb : (‖φ z‖₊ : ℝ≥0∞) ≤ ENNReal.ofReal C := by
        rw [← enorm_eq_nnnorm, ← ofReal_norm]
        exact ENNReal.ofReal_le_ofReal (hC z (ball_subset_closedBall hz))
      calc (‖φ z‖₊ : ℝ≥0∞) ^ 2 * ENNReal.ofReal (rho z)⁻¹ ≤ (ENNReal.ofReal C) ^ 2 * 1 := by
            gcongr
            exact ENNReal.ofReal_le_one.mpr hρ
        _ = _ := mul_one _
    refine lt_of_le_of_lt hle ?_
    rw [setLIntegral_const]
    exact ENNReal.mul_lt_top (ENNReal.pow_lt_top ENNReal.ofReal_lt_top) measure_ball_lt_top
  exact ENNReal.rpow_lt_top_of_nonneg (by norm_num) hfin.ne

/-! ### Analytic tools for the limits -/

open scoped Pointwise

/-- Cauchy–Schwarz in `ℝ≥0∞` form. -/
theorem s36l_cs {α : Type*} [MeasurableSpace α] {μ : Measure α} {u v : α → ℂ}
    (hu : AEStronglyMeasurable u μ) (hv : AEStronglyMeasurable v μ) :
    (∫⁻ x, ‖u x * v x‖ₑ ∂μ) ≤ (∫⁻ x, ‖u x‖ₑ ^ 2 ∂μ) ^ (1 / 2 : ℝ) * (∫⁻ x, ‖v x‖ₑ ^ 2 ∂μ) ^ (1 / 2 : ℝ) := by
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq μ Real.HolderConjugate.two_two hu.enorm hv.enorm
  simp only [Pi.mul_apply, ENNReal.rpow_ofNat] at h
  simp only [enorm_mul]
  exact h

/-- Products `aₙ bₙ` with `L²`-bounded `aₙ`, uniformly square-integrable `bₙ` and a.e. convergence converge in
integral (Vitali). -/
theorem s36l_vitali_pair {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]
    {a b : ℕ → α → ℂ} {A B : α → ℂ} {C : ℝ≥0∞} (hC : C ≠ ∞)
    (ha : ∀ n, AEStronglyMeasurable (a n) μ) (hb : ∀ n, AEStronglyMeasurable (b n) μ)
    (haL : ∀ n, ∫⁻ x, ‖a n x‖ₑ ^ 2 ∂μ ≤ C) (hbL : ∀ n, ∫⁻ x, ‖b n x‖ₑ ^ 2 ∂μ ≠ ∞)
    (hbUI : ∀ ε > (0 : ℝ≥0∞), ∃ δ > (0 : ℝ≥0∞), ∀ n s, MeasurableSet s → μ s ≤ δ →
      ∫⁻ x in s, ‖b n x‖ₑ ^ 2 ∂μ ≤ ε)
    (hAB : Integrable (fun x => A x * B x) μ)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun n => a n x * b n x) atTop (𝓝 (A x * B x))) :
    Tendsto (fun n => ∫ x, a n x * b n x ∂μ) atTop (𝓝 (∫ x, A x * B x ∂μ)) := by
  have hF : ∀ n, AEStronglyMeasurable (fun x => a n x * b n x) μ := fun n => (ha n).mul (hb n)
  set K : ℝ≥0∞ := C ^ (1 / 2 : ℝ) with hK
  have hKt : K ≠ ∞ := ENNReal.rpow_ne_top_of_nonneg (by norm_num) hC
  have hint : ∀ n, Integrable (fun x => a n x * b n x) μ := by
    intro n
    refine ⟨hF n, ?_⟩
    show (∫⁻ x, ‖a n x * b n x‖ₑ ∂μ) < ∞
    refine lt_of_le_of_lt (s36l_cs (ha n) (hb n)) (ENNReal.mul_lt_top ?_ ?_)
    · exact ENNReal.rpow_lt_top_of_nonneg (by norm_num) ((haL n).trans_lt hC.lt_top).ne
    · exact ENNReal.rpow_lt_top_of_nonneg (by norm_num) (hbL n)
  have hui : UnifIntegrable (fun n x => a n x * b n x) 1 μ := by
    rw [unifIntegrable_iff']
    intro ε hε
    set η : ℝ≥0∞ := ε / (K + 1) with hη
    have hη0 : 0 < η := ENNReal.div_pos hε.ne' (by simp [hKt])
    obtain ⟨δ, hδ, hδs⟩ := hbUI (η ^ 2) (ENNReal.pow_pos hη0 2)
    refine ⟨δ, hδ, fun n s hs hμs => ?_⟩
    rw [eLpNorm_one_eq_lintegral_enorm (hF n).restrict]
    refine (s36l_cs (ha n).restrict (hb n).restrict).trans ?_
    have h1 : (∫⁻ x in s, ‖a n x‖ₑ ^ 2 ∂μ) ^ (1 / 2 : ℝ) ≤ K :=
      ENNReal.rpow_le_rpow ((setLIntegral_le_lintegral _ _).trans (haL n)) (by norm_num)
    have h2 : (∫⁻ x in s, ‖b n x‖ₑ ^ 2 ∂μ) ^ (1 / 2 : ℝ) ≤ η := by
      calc (∫⁻ x in s, ‖b n x‖ₑ ^ 2 ∂μ) ^ (1 / 2 : ℝ) ≤ (η ^ 2) ^ (1 / 2 : ℝ) :=
            ENNReal.rpow_le_rpow (hδs n s hs hμs) (by norm_num)
        _ = η := by
          rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
          norm_num
    calc _ ≤ K * η := mul_le_mul' h1 h2
      _ ≤ (K + 1) * η := by gcongr; exact le_self_add
      _ ≤ ε := by rw [hη]; exact ENNReal.mul_div_le
  have hV := tendsto_Lp_finite_of_tendsto_ae le_rfl ENNReal.one_ne_top hF
    (memLp_one_iff_integrable.mpr hAB) hui hlim
  refine tendsto_integral_of_L1 _ hAB.aestronglyMeasurable (Eventually.of_forall hint) ?_
  refine hV.congr fun n => ?_
  rw [eLpNorm_one_eq_lintegral_enorm ((hF n).sub hAB.aestronglyMeasurable)]
  rfl

/-- Dilations `w ↦ r φ(rw)`, `0 < r ≤ 1`, of a square-integrable function on `𝔻` are uniformly
square-integrable on `𝔻` (change of variables `u = rw`). -/
theorem s36l_dil_ui {φ : ℂ → ℂ} (hφ : (∫⁻ u in unitDisc, ‖φ u‖ₑ ^ 2) ≠ ∞) {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ δ > (0 : ℝ≥0∞), ∀ r : ℝ, 0 < r → r ≤ 1 → ∀ s, MeasurableSet s → volume.restrict unitDisc s ≤ δ →
      (∫⁻ w in s, ENNReal.ofReal (r ^ 2) * ‖φ ((r : ℂ) * w)‖ₑ ^ 2 ∂(volume.restrict unitDisc)) ≤ ε := by
  obtain ⟨δ, hδ, hδs⟩ := exists_pos_setLIntegral_lt_of_measure_lt (μ := volume.restrict unitDisc)
    (f := fun u => ‖φ u‖ₑ ^ 2) hφ hε
  refine ⟨δ / 2, ENNReal.half_pos hδ.ne', fun r hr0 hr1 s hs hμs => ?_⟩
  have hD : MeasurableSet unitDisc := measurableSet_ball
  set T : Set ℂ := r • (s ∩ unitDisc) with hT
  have hTm : MeasurableSet T := (hs.inter hD).const_smul₀ r
  have hTD : T ⊆ unitDisc := by
    rintro _ ⟨w, hw, rfl⟩
    have hw1 := mem_ball_zero_iff.mp hw.2
    refine mem_ball_zero_iff.mpr ?_
    rw [norm_smul, Real.norm_of_nonneg hr0.le]
    nlinarith [norm_nonneg w]
  -- the measure of the image
  have hvolT : volume T ≤ volume.restrict unitDisc s := by
    rw [Measure.restrict_apply hs, hT, Measure.addHaar_smul, Complex.finrank_real_complex]
    calc ENNReal.ofReal |r ^ 2| * volume (s ∩ unitDisc) ≤ 1 * volume (s ∩ unitDisc) := by
          gcongr
          rw [abs_of_nonneg (by positivity)]
          exact ENNReal.ofReal_le_one.mpr (by nlinarith)
      _ = _ := one_mul _
  have hlt : volume.restrict unitDisc T < δ := by
    rw [Measure.restrict_apply hTm, inter_eq_left.mpr hTD]
    rcases eq_or_ne δ ∞ with h | h
    · rw [h]; exact (measure_mono hTD).trans_lt measure_ball_lt_top
    · exact lt_of_le_of_lt (hvolT.trans hμs) (ENNReal.half_lt_self hδ.ne' h)
  have hbound := (hδs T hlt).le
  -- change of variables
  have hr0' : r ≠ 0 := hr0.ne'
  let g : ℂ → ℝ≥0∞ := T.indicator (fun u => ‖φ u‖ₑ ^ 2)
  have hpt : ∀ w, (s ∩ unitDisc).indicator (fun w => ENNReal.ofReal (r ^ 2) * ‖φ ((r : ℂ) * w)‖ₑ ^ 2) w =
      ENNReal.ofReal (r ^ 2) * g (r • w) := by
    intro w
    show _ = ENNReal.ofReal (r ^ 2) * T.indicator (fun u => ‖φ u‖ₑ ^ 2) (r • w)
    by_cases hw : w ∈ s ∩ unitDisc
    · have hw' : r • w ∈ T := smul_mem_smul_set hw
      rw [indicator_of_mem hw, indicator_of_mem hw', Complex.real_smul]
    · have hw' : r • w ∉ T := fun h => hw ((smul_mem_smul_set_iff₀ hr0' _ _).mp h)
      rw [indicator_of_notMem hw, indicator_of_notMem hw', mul_zero]
  have hmap : (∫⁻ w, g (r • w)) = ENNReal.ofReal |(r ^ 2)⁻¹| * ∫⁻ u, g u := by
    have h1 := lintegral_map_equiv g (Homeomorph.smulOfNeZero r hr0').toMeasurableEquiv
      (μ := (volume : Measure ℂ))
    have h2 := Measure.map_addHaar_smul (volume : Measure ℂ) hr0'
    rw [Complex.finrank_real_complex] at h2
    have h3 : ⇑(Homeomorph.smulOfNeZero r hr0').toMeasurableEquiv = fun x : ℂ => r • x := rfl
    rw [h3, h2, lintegral_smul_measure] at h1
    rw [← h1]
    rfl
  calc (∫⁻ w in s, ENNReal.ofReal (r ^ 2) * ‖φ ((r : ℂ) * w)‖ₑ ^ 2 ∂(volume.restrict unitDisc))
      = ∫⁻ w, (s ∩ unitDisc).indicator
          (fun w => ENNReal.ofReal (r ^ 2) * ‖φ ((r : ℂ) * w)‖ₑ ^ 2) w := by
        rw [Measure.restrict_restrict hs, lintegral_indicator (hs.inter hD)]
    _ = ENNReal.ofReal (r ^ 2) * ∫⁻ w, g (r • w) := by
        simp_rw [hpt]
        exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ = ∫⁻ u, g u := by
        rw [hmap, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity), abs_of_pos (by positivity),
          mul_inv_cancel₀ (by positivity), ENNReal.ofReal_one, one_mul]
    _ = ∫⁻ u in T, ‖φ u‖ₑ ^ 2 ∂(volume.restrict unitDisc) := by
        rw [lintegral_indicator hTm, Measure.restrict_restrict hTm, inter_eq_left.mpr hTD]
    _ ≤ ε := hbound

/-- Pre-Schwarzians agree where the functions agree on an open set. -/
theorem s36l_preS_eqOn {f g : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U) (h : EqOn f g U) :
    EqOn (preSchwarzian f) (preSchwarzian g) U := by
  intro w hw
  have hev : f =ᶠ[𝓝 w] g := by
    filter_upwards [hU.mem_nhds hw] with u hu
    exact h hu
  unfold preSchwarzian
  rw [hev.deriv.deriv_eq, hev.deriv_eq]

/-- On `T₀(1)`, `𝒜(𝖿) ∈ A₂¹(𝔻)` (Theorem 1.12 for the representative, and `𝖿` is a class function on `𝔻`). -/
theorem s36l_psi_mem {κ : LinfStar} (hκ : κ ∈ LinfStarBall) (hκT : Phi ⟨κ, hκ⟩ ∈ T01) :
    preSchwarzian (fsans κ) ∈ A21fun unitDisc := by
  set p := Phi ⟨κ, hκ⟩ with hp
  have h := (thm_1_12 p).2.1.mp hκT
  have heq : Phi (Quotient.out p) = Phi ⟨κ, hκ⟩ := Quotient.out_eq p
  have hc := (s2c_class_pair (Quotient.exact heq)).1
  exact (ab112_A21fun_congr isOpen_ball (s36l_preS_eqOn isOpen_ball hc)).mp h

/-- `𝖿` is bounded on `𝔻` (continuous on `𝔻̄`, `s5e_fB_continuousAt`). -/
theorem s36l_fsans_bdd {κ : LinfStar} (hκ : κ ∈ LinfStarBall) :
    ∃ M : ℝ, 0 < M ∧ ∀ z ∈ unitDisc, ‖fsans κ z‖ ≤ M := by
  have hc : ContinuousOn (fB κ) (closedBall 0 1) := fun z hz =>
    (s5e_fB_continuousAt hκ (mem_closedBall_zero_iff.mp hz)).continuousWithinAt
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : ℂ) 1).exists_bound_of_continuousOn hc
  refine ⟨max C 1, lt_max_of_lt_right one_pos, fun z hz => ?_⟩
  rw [S2C.s2c_fsans_eq hκ]
  exact (hC z (ball_subset_closedBall hz)).trans (le_max_left _ _)

/-- Area formula: `∬_𝔻 |f'|² = |f(𝔻)|` for `f` univalent on `𝔻`. -/
theorem s36l_area {f : ℂ → ℂ} (hfd : DifferentiableOn ℂ f unitDisc) (hfi : InjOn f unitDisc) :
    (∫⁻ u in unitDisc, ‖deriv f u‖ₑ ^ 2) = volume (f '' unitDisc) := by
  have hder : ∀ x ∈ unitDisc, HasFDerivWithinAt f
      ((ContinuousLinearMap.toSpanSingleton ℂ (deriv f x)).restrictScalars ℝ) unitDisc x := fun x hx =>
    (((hfd x hx).differentiableAt (isOpen_ball.mem_nhds hx)).hasDerivAt.hasFDerivAt.restrictScalars ℝ).hasFDerivWithinAt
  rw [← lintegral_abs_det_fderiv_eq_addHaar_image (s := unitDisc) volume measurableSet_ball hder hfi]
  refine setLIntegral_congr_fun measurableSet_ball fun x _ => ?_
  rw [LiZhongQC.det_restrictScalars_toSpanSingleton, abs_of_nonneg (by positivity),
    ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]

/-- `f' ∈ L²(𝔻)` for `𝖿`. -/
theorem s36l_fsans_deriv_L2 {κ : LinfStar} (hκ : κ ∈ LinfStarBall) :
    (∫⁻ u in unitDisc, ‖deriv (fsans κ) u‖ₑ ^ 2) ≠ ∞ := by
  obtain ⟨hfd, hfi, -⟩ := s2c_facts hκ
  obtain ⟨M, -, hM⟩ := s36l_fsans_bdd hκ
  rw [s36l_area hfd hfi]
  refine ne_top_of_le_ne_top (measure_closedBall_lt_top (x := (0 : ℂ)) (r := M)).ne (measure_mono ?_)
  rintro _ ⟨z, hz, rfl⟩
  exact mem_closedBall_zero_iff.mpr (hM z hz)

/-- `M_c(ζ) = ζ/(1 + cζ)` has derivative `(1 + cζ)⁻²`. -/
theorem s36l_mob_hasDerivAt {c ζ : ℂ} (h : 1 + c * ζ ≠ 0) :
    HasDerivAt (fun x => x / (1 + c * x)) (1 / (1 + c * ζ) ^ 2) ζ := by
  have h1 : HasDerivAt (fun x => x / (1 + c * x)) ((1 * (1 + c * ζ) - ζ * (c * 1)) / (1 + c * ζ) ^ 2) ζ :=
    (hasDerivAt_id' ζ).div (((hasDerivAt_id' ζ).const_mul c).const_add 1) h
  convert h1 using 2
  ring

/-- `𝒜(M_c)(ζ) = -2c/(1 + cζ)`. -/
theorem s36l_mob_preS {c ζ : ℂ} (h : 1 + c * ζ ≠ 0) :
    preSchwarzian (fun x => x / (1 + c * x)) ζ = -2 * c / (1 + c * ζ) := by
  have hcont : ContinuousAt (fun x : ℂ => 1 + c * x) ζ :=
    (continuous_const.add (continuous_const.mul continuous_id)).continuousAt
  have hev : deriv (fun x : ℂ => x / (1 + c * x)) =ᶠ[𝓝 ζ] fun x => ((1 + c * x) ^ 2)⁻¹ := by
    filter_upwards [hcont.eventually_ne h] with x hx
    rw [(s36l_mob_hasDerivAt hx).deriv, one_div]
  have hd2 := ((((hasDerivAt_id' ζ).const_mul c).const_add 1).pow 2).inv (pow_ne_zero 2 h)
  unfold preSchwarzian
  rw [hev.deriv_eq, show deriv (fun x : ℂ => ((1 + c * x) ^ 2)⁻¹) ζ = _ from hd2.deriv,
    (s36l_mob_hasDerivAt h).deriv]
  simp only [Pi.pow_apply]
  norm_num
  field_simp
  try ring

/-- Derivative of `M_c ∘ F`. -/
theorem s36l_mob_comp_deriv {F : ℂ → ℂ} {c w : ℂ} (hF : DifferentiableAt ℂ F w) (h : 1 + c * F w ≠ 0) :
    deriv (fun u => F u / (1 + c * F u)) w = deriv F w / (1 + c * F w) ^ 2 := by
  have h1 := (s36l_mob_hasDerivAt h).comp w hF.hasDerivAt
  rw [show (fun u => F u / (1 + c * F u)) = (fun x => x / (1 + c * x)) ∘ F from rfl, h1.deriv]
  ring

/-- Pre-Schwarzian of `M_c ∘ F`. -/
theorem s36l_mob_comp_preS {F : ℂ → ℂ} {c w : ℂ} (hF : AnalyticAt ℂ F w) (hF' : deriv F w ≠ 0)
    (h : 1 + c * F w ≠ 0) :
    preSchwarzian (fun u => F u / (1 + c * F u)) w =
      preSchwarzian F w - 2 * c * deriv F w / (1 + c * F w) := by
  have hden : AnalyticAt ℂ (fun x : ℂ => 1 + c * x) (F w) := analyticAt_const.add (analyticAt_const.mul analyticAt_id)
  have hM : AnalyticAt ℂ (fun x : ℂ => x / (1 + c * x)) (F w) := analyticAt_id.div hden h
  have hM' : deriv (fun x : ℂ => x / (1 + c * x)) (F w) ≠ 0 := by
    rw [(s36l_mob_hasDerivAt h).deriv]
    exact one_div_ne_zero (pow_ne_zero 2 h)
  have hc := preSchwarzian_comp_of_analyticAt hF hM hF' hM'
  rw [s36l_mob_preS h] at hc
  rw [show (fun u => F u / (1 + c * F u)) = (fun x => x / (1 + c * x)) ∘ F from rfl, hc]
  ring

/-- `K₁` is invariant under post-composition with `M_c` (off the diagonal). -/
theorem s36l_kerK1_mob {F : ℂ → ℂ} {c z w : ℂ} (hzw : z ≠ w) (hFz : DifferentiableAt ℂ F z)
    (hFw : DifferentiableAt ℂ F w) (hz : 1 + c * F z ≠ 0) (hw : 1 + c * F w ≠ 0) (hne : F z ≠ F w) :
    kerK1 (fun u => F u / (1 + c * F u)) z w = kerK1 F z w := by
  rw [kerK1_of_ne _ hzw, kerK1_of_ne _ hzw, s36l_mob_comp_deriv hFz hz, s36l_mob_comp_deriv hFw hw]
  have hs : F z - F w ≠ 0 := sub_ne_zero.mpr hne
  have key : F z / (1 + c * F z) - F w / (1 + c * F w) = (F z - F w) / ((1 + c * F z) * (1 + c * F w)) := by
    rw [div_sub_div _ _ hz hw]
    congr 1
    ring
  rw [key]
  field_simp
  try ring

/-- The dilation `F(u) = f(ru)/r` on `𝔻`. -/
theorem s36l_dilF {f : ℂ → ℂ} (hfd : DifferentiableOn ℂ f unitDisc) {r : ℂ} (hr0 : r ≠ 0) {w : ℂ}
    (hw : r * w ∈ unitDisc) :
    AnalyticAt ℂ (fun u => f (r * u) / r) w ∧ deriv (fun u => f (r * u) / r) w = deriv f (r * w) ∧
      preSchwarzian (fun u => f (r * u) / r) w = r * preSchwarzian f (r * w) := by
  have hfa : AnalyticAt ℂ f (r * w) := hfd.analyticAt (isOpen_ball.mem_nhds hw)
  have hlin : AnalyticAt ℂ (fun u : ℂ => r * u) w := analyticAt_const.mul analyticAt_id
  refine ⟨(hfa.comp hlin).div_const, ?_, ?_⟩
  · have h1 := deriv_affine_precomp f r 0 w
    simp only [add_zero] at h1
    rw [deriv_div_const, h1, mul_div_cancel_left₀ _ hr0]
  · have h1 := preSchwarzian_affine_postcomp (fun u => f (r * u + 0)) (inv_ne_zero hr0) 0 w
    have h2 := preSchwarzian_affine_precomp f r 0 w
    simp only [add_zero] at h1 h2
    rw [← h2, ← h1]
    congr 1
    funext u
    rw [div_eq_inv_mul]

/-- `K₁` of the dilation: `K₁(F)(z, w) = r² K₁(f)(rz, rw)` off the diagonal. -/
theorem s36l_kerK1_dilF {f : ℂ → ℂ} (hfd : DifferentiableOn ℂ f unitDisc) (hfi : InjOn f unitDisc) {r : ℂ}
    (hr0 : r ≠ 0) {z w : ℂ} (hzw : z ≠ w) (hz : r * z ∈ unitDisc) (hw : r * w ∈ unitDisc) :
    kerK1 (fun u => f (r * u) / r) z w = r ^ 2 * kerK1 f (r * z) (r * w) := by
  have hrzw : r * z ≠ r * w := fun h => hzw (mul_left_cancel₀ hr0 h)
  have hne : f (r * z) - f (r * w) ≠ 0 := sub_ne_zero.mpr fun h => hrzw (hfi hz hw h)
  rw [kerK1_of_ne _ hzw, kerK1_of_ne _ hrzw, (s36l_dilF hfd hr0 hz).2.1, (s36l_dilF hfd hr0 hw).2.1]
  have hzw' : z - w ≠ 0 := sub_ne_zero.mpr hzw
  field_simp
  try ring

theorem s36l_mul_mem {r : ℝ} (h0 : 0 < r) (h1 : r ≤ 1) {w : ℂ} (hw : w ∈ unitDisc) : (r : ℂ) * w ∈ unitDisc := by
  have hw1 := mem_ball_zero_iff.mp hw
  refine mem_ball_zero_iff.mpr ?_
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg h0.le]
  nlinarith [norm_nonneg w]

theorem s36l_A21_L2 {ψ : ℂ → ℂ} {U : Set ℂ} (h : ψ ∈ A21fun U) : (∫⁻ u in U, ‖ψ u‖ₑ ^ 2) ≠ ∞ := by
  have h2 := h.2
  unfold normA21 at h2
  have h3 := (ENNReal.rpow_lt_top_iff_of_pos (by norm_num : (0 : ℝ) < 1 / 2)).mp h2
  simpa only [enorm_eq_nnnorm] using h3.ne

theorem s36l_enorm_conj (x : ℂ) : ‖conj x‖ₑ = ‖x‖ₑ := by
  rw [enorm_eq_nnnorm, enorm_eq_nnnorm]
  congr 1
  exact NNReal.eq (by simp only [coe_nnnorm, Complex.norm_conj])

theorem s36l_int_mul {α : Type*} [MeasurableSpace α] {μ : Measure α} {u v : α → ℂ}
    (hu : AEStronglyMeasurable u μ) (hv : AEStronglyMeasurable v μ)
    (hu2 : (∫⁻ x, ‖u x‖ₑ ^ 2 ∂μ) ≠ ∞) (hv2 : (∫⁻ x, ‖v x‖ₑ ^ 2 ∂μ) ≠ ∞) :
    Integrable (fun x => u x * v x) μ := by
  refine ⟨hu.mul hv, ?_⟩
  show (∫⁻ x, ‖u x * v x‖ₑ ∂μ) < ∞
  exact lt_of_le_of_lt (s36l_cs hu hv) (ENNReal.mul_lt_top
    (ENNReal.rpow_lt_top_of_nonneg (by norm_num) hu2) (ENNReal.rpow_lt_top_of_nonneg (by norm_num) hv2))

theorem s36l_enorm_sq_le {x y : ℂ} {r : ℝ} (hr : 0 ≤ r) (h : ‖x‖ ≤ r * ‖y‖) :
    ‖x‖ₑ ^ 2 ≤ ENNReal.ofReal (r ^ 2) * ‖y‖ₑ ^ 2 := by
  have e : ∀ v : ℂ, ‖v‖ₑ ^ 2 = ENNReal.ofReal (‖v‖ ^ 2) := fun v => by
    rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
  rw [e, e, ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ r ^ 2)]
  refine ENNReal.ofReal_le_ofReal ?_
  have := pow_le_pow_left₀ (norm_nonneg x) h 2
  nlinarith

theorem s36l_enorm_sq_add_le {x y : ℂ} {t : ℝ} (ht : 0 ≤ t) (h : ‖x‖ ≤ ‖y‖ + t) :
    ‖x‖ₑ ^ 2 ≤ 2 * ‖y‖ₑ ^ 2 + 2 * ENNReal.ofReal (t ^ 2) := by
  have e : ∀ v : ℂ, ‖v‖ₑ ^ 2 = ENNReal.ofReal (‖v‖ ^ 2) := fun v => by
    rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
  rw [e, e]
  have hr : ‖x‖ ^ 2 ≤ 2 * ‖y‖ ^ 2 + 2 * t ^ 2 := by
    have := pow_le_pow_left₀ (norm_nonneg x) h 2
    nlinarith [sq_nonneg (‖y‖ - t), norm_nonneg y]
  calc ENNReal.ofReal (‖x‖ ^ 2) ≤ ENNReal.ofReal (2 * ‖y‖ ^ 2 + 2 * t ^ 2) := ENNReal.ofReal_le_ofReal hr
    _ = _ := by
      rw [ENNReal.ofReal_add (by positivity : (0 : ℝ) ≤ 2 * ‖y‖ ^ 2) (by positivity : (0 : ℝ) ≤ 2 * t ^ 2),
        ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
        ENNReal.ofReal_ofNat]

/-- Koebe separation: `|𝗀(w) - 𝖿(z)| ≥ |𝖿'(z)|(1 - |z|²)/4` for `w ∈ 𝔻*`. -/
theorem s36l_koebe_sep {κ : LinfStar} (hκ : κ ∈ LinfStarBall) {z : ℂ} (hz : z ∈ unitDisc) {w : ℂ}
    (hw : w ∈ unitDiscExterior) :
    ‖deriv (fsans κ) z‖ * (1 - ‖z‖ ^ 2) / 4 ≤ ‖gsans κ w - fsans κ z‖ := by
  obtain ⟨hfd, hfi, -⟩ := s2c_facts hκ
  have hK := r24_koebe_point hfd hfi hz
  have hdisj := (AppB.b8_welding_normalized_pair hκ).2.2.2.2.2
  by_contra hlt
  push_neg at hlt
  have hmem : gsans κ w ∈ ball (fsans κ z) (‖deriv (fsans κ) z‖ * (1 - ‖z‖ ^ 2) / 4) := by
    rw [mem_ball, dist_eq_norm]
    exact hlt
  exact Set.disjoint_left.mp hdisj (hK hmem) ⟨w, hw, rfl⟩

/-- `L²` bound of a `K₂`-row over a set kept at distance `≥ D` from `𝖿(z)` by `𝗀`. -/
theorem s36l_K2row_bound {f g : ℂ → ℂ} {S : Set ℂ} (hS : IsOpen S) (hgd : DifferentiableOn ℂ g S)
    (hgi : InjOn g S) {z : ℂ} {D : ℝ} (hD0 : 0 < D) (hD : ∀ w ∈ S, D ≤ ‖g w - f z‖) :
    (∫⁻ w in S, ‖kerK2 f g z w‖ₑ ^ 2) ≤
      ENNReal.ofReal (‖deriv f z‖ ^ 2 / π ^ 2) * ENNReal.ofReal (π / D ^ 2) := by
  set B : ℝ := ‖deriv f z‖ ^ 2 / π ^ 2 with hB
  let G : ℂ → ℝ≥0∞ := fun u => ENNReal.ofReal B * (‖u - f z‖₊ : ℝ≥0∞)⁻¹ ^ 4
  have hpt : ∀ w ∈ S, ‖kerK2 f g z w‖ₑ ^ 2 = ENNReal.ofReal (‖deriv g w‖ ^ 2) * G (g w) := by
    intro w hw
    have hne : 0 < ‖g w - f z‖ := lt_of_lt_of_le hD0 (hD w hw)
    have e1 : (‖g w - f z‖₊ : ℝ≥0∞)⁻¹ ^ 4 = ENNReal.ofReal (‖g w - f z‖⁻¹ ^ 4) := by
      rw [← enorm_eq_nnnorm, ← ofReal_norm, ← ENNReal.ofReal_inv_of_pos hne,
        ENNReal.ofReal_pow (by positivity : (0 : ℝ) ≤ ‖g w - f z‖⁻¹)]
    show _ = ENNReal.ofReal (‖deriv g w‖ ^ 2) * (ENNReal.ofReal B * (‖g w - f z‖₊ : ℝ≥0∞)⁻¹ ^ 4)
    rw [e1, ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ B),
      ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ ‖deriv g w‖ ^ 2), ← ofReal_norm,
      ← ENNReal.ofReal_pow (norm_nonneg _)]
    congr 1
    have h1 : ‖f z - g w‖ = ‖g w - f z‖ := norm_sub_rev _ _
    unfold kerK2
    simp only [norm_mul, norm_div, norm_pow, norm_one, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le]
    rw [h1, hB]
    have hpi : (0 : ℝ) < π := Real.pi_pos
    field_simp
  calc (∫⁻ w in S, ‖kerK2 f g z w‖ₑ ^ 2) = ∫⁻ w in S, ENNReal.ofReal (‖deriv g w‖ ^ 2) * G (g w) :=
        setLIntegral_congr_fun hS.measurableSet hpt
    _ = ∫⁻ u in g '' S, G u := (r24_conformal_lintegral hS hgd hgi G).symm
    _ = ENNReal.ofReal B * ∫⁻ u in g '' S, (‖u - f z‖₊ : ℝ≥0∞)⁻¹ ^ 4 :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal B * ENNReal.ofReal (π / D ^ 2) := by
        gcongr
        refine r24_lintegral_outside hD0 ?_
        rintro _ ⟨w, hw, rfl⟩
        exact hD w hw

/-- Uniform square-integrability from eventual uniform square-integrability of square-integrable functions. -/
theorem s36l_ui_eventually {α : Type*} [MeasurableSpace α] {μ : Measure α} {b : ℕ → α → ℂ}
    (hbL : ∀ n, (∫⁻ x, ‖b n x‖ₑ ^ 2 ∂μ) ≠ ∞)
    (h : ∀ ε > (0 : ℝ≥0∞), ∃ δ > (0 : ℝ≥0∞), ∃ N : ℕ, ∀ n, N ≤ n → ∀ s, MeasurableSet s → μ s ≤ δ →
      ∫⁻ x in s, ‖b n x‖ₑ ^ 2 ∂μ ≤ ε) :
    ∀ ε > (0 : ℝ≥0∞), ∃ δ > (0 : ℝ≥0∞), ∀ n s, MeasurableSet s → μ s ≤ δ →
      ∫⁻ x in s, ‖b n x‖ₑ ^ 2 ∂μ ≤ ε := by
  intro ε hε
  obtain ⟨δ0, hδ0, N, hN⟩ := h ε hε
  choose δf hδf hδs using fun n => exists_pos_setLIntegral_lt_of_measure_lt (μ := μ)
    (f := fun x => ‖b n x‖ₑ ^ 2) (hbL n) hε.ne'
  set δ1 : ℝ≥0∞ := (Finset.range N).inf (fun n => min (δf n) 1 / 2) with hδ1
  have hδ1p : 0 < δ1 := by
    rw [hδ1, Finset.lt_inf_iff ENNReal.zero_lt_top]
    intro n _
    exact ENNReal.half_pos (lt_min (hδf n) one_pos).ne'
  refine ⟨min δ0 δ1, lt_min hδ0 hδ1p, fun n s hs hμs => ?_⟩
  rcases le_or_gt N n with hn | hn
  · exact hN n hn s hs (hμs.trans (min_le_left _ _))
  · have hle : μ s ≤ min (δf n) 1 / 2 :=
      (hμs.trans (min_le_right _ _)).trans (Finset.inf_le (Finset.mem_range.mpr hn))
    have hfin : min (δf n) 1 ≠ ∞ := ne_top_of_le_ne_top ENNReal.one_ne_top (min_le_right _ _)
    have hlt : μ s < δf n :=
      lt_of_lt_of_le (lt_of_le_of_lt hle (ENNReal.half_lt_self (lt_min (hδf n) one_pos).ne' hfin))
        (min_le_left _ _)
    exact (hδs n s hlt).le

/-- Splitting criterion for convergence. -/
theorem s36l_split_tendsto {x : ℕ → ℂ} {x0 : ℂ}
    (h : ∀ ε > (0 : ℝ), ∃ y : ℕ → ℂ, ∃ y0 : ℂ, Tendsto y atTop (𝓝 y0) ∧ (∀ᶠ n in atTop, ‖x n - y n‖ ≤ ε) ∧
      ‖x0 - y0‖ ≤ ε) :
    Tendsto x atTop (𝓝 x0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨y, y0, hy, hxy, hx0⟩ := h (ε / 4) (by positivity)
  obtain ⟨N1, hN1⟩ := eventually_atTop.mp hxy
  obtain ⟨N2, hN2⟩ := Metric.tendsto_atTop.mp hy (ε / 4) (by positivity)
  refine ⟨max N1 N2, fun n hn => ?_⟩
  have h1 := hN1 n (le_of_max_le_left hn)
  have h2 := hN2 n (le_of_max_le_right hn)
  rw [dist_eq_norm] at h2 ⊢
  calc ‖x n - x0‖ = ‖(x n - y n) + (y n - y0) + (y0 - x0)‖ := by ring_nf
    _ ≤ ‖x n - y n‖ + ‖y n - y0‖ + ‖y0 - x0‖ := norm_add₃_le
    _ < ε := by rw [norm_sub_rev y0 x0]; linarith

/-- Near `∞`, `𝗀` and (eventually, uniformly) the `𝗀ₙ` are large: inversion `ξ ↦ 1/𝗀(1/ξ)` (`r24_inversion`) and the
maximum principle on `|ξ| ≤ r`. -/
theorem s36l_far {κ : LinfStar} (hκ : κ ∈ LinfStarBall) {κs : ℕ → LinfStar} (hκs : ∀ n, κs n ∈ LinfStarBall)
    (hconv : TendstoLocallyUniformlyOn (fun n => gsans (κs n)) (gsans κ) atTop unitDiscExterior) (D : ℝ) :
    ∃ R : ℝ, 1 < R ∧ (∀ w : ℂ, R ≤ ‖w‖ → D ≤ ‖gsans κ w‖) ∧
      ∀ᶠ n in atTop, ∀ w : ℂ, R ≤ ‖w‖ → D ≤ ‖gsans (κs n) w‖ := by
  set D' : ℝ := max D 1 with hD'def
  have hD' : 0 < D' := lt_max_of_lt_right one_pos
  let G : LinfStar → ℂ → ℂ := fun μ ξ => if ξ = 0 then 0 else (gsans μ ξ⁻¹)⁻¹
  have hGv : ∀ μ : LinfStar, ∀ w : ℂ, w ≠ 0 → G μ w⁻¹ = (gsans μ w)⁻¹ := fun μ w hw => by
    simp only [G, inv_eq_zero, hw, if_false, inv_inv]
  obtain ⟨hG0d, -, hg0ne⟩ := r24_inversion hκ
  have h0 : (0 : ℂ) ∈ unitDisc := mem_ball_self one_pos
  have hcont : ContinuousAt (G κ) 0 := (hG0d.differentiableAt (isOpen_ball.mem_nhds h0)).continuousAt
  have hG00 : G κ 0 = 0 := if_pos rfl
  obtain ⟨r0, hr0, hr0b⟩ := Metric.continuousAt_iff.mp hcont (1 / (2 * D')) (by positivity)
  set r : ℝ := min (r0 / 2) (1 / 2) with hr
  have hrpos : 0 < r := lt_min (by positivity) (by norm_num)
  have hr1 : r < 1 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  have hrr0 : r < r0 := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hsmall : ∀ ξ : ℂ, ‖ξ‖ ≤ r → ‖G κ ξ‖ ≤ 1 / (2 * D') := fun ξ hξ => by
    have h := hr0b (x := ξ) (by rw [dist_zero_right]; linarith)
    rw [dist_eq_norm, hG00, sub_zero] at h
    exact h.le
  have hR1 : 1 < r⁻¹ := (one_lt_inv₀ hrpos).mpr hr1
  have hext : ∀ w : ℂ, r⁻¹ ≤ ‖w‖ → w ∈ unitDiscExterior := fun w hw => by
    show 1 < ‖w‖
    linarith
  have hw0 : ∀ w : ℂ, r⁻¹ ≤ ‖w‖ → w ≠ 0 := fun w hw h => by
    rw [h, norm_zero] at hw
    linarith
  have hξr : ∀ w : ℂ, r⁻¹ ≤ ‖w‖ → ‖w⁻¹‖ ≤ r := fun w hw => by
    rw [norm_inv]
    exact inv_le_of_inv_le₀ hrpos hw
  set C : Set ℂ := sphere (0 : ℂ) r⁻¹ with hC
  have hCsub : C ⊆ unitDiscExterior := fun w hw => hext w (mem_sphere_zero_iff_norm.mp hw).ge
  have hCc : IsCompact C := isCompact_sphere 0 r⁻¹
  have hgc : ContinuousOn (gsans κ) C := ((s2c_facts hκ).2.2.2.2.1).continuousOn.mono hCsub
  have hCne : C.Nonempty := NormedSpace.sphere_nonempty.mpr (inv_nonneg.mpr hrpos.le)
  obtain ⟨w0, hw0C, hw0min⟩ := hCc.exists_isMinOn hCne hgc.norm
  set m : ℝ := ‖gsans κ w0‖ with hmdef
  have hm : 0 < m := norm_pos_iff.mpr (hg0ne w0 (hCsub hw0C))
  have hmle : ∀ w ∈ C, m ≤ ‖gsans κ w‖ := fun w hw => hw0min hw
  have hU := (tendstoLocallyUniformlyOn_iff_forall_isCompact
    (isOpen_lt continuous_const continuous_norm)).mp hconv C hCsub hCc
  set η : ℝ := min (m / 2) (m ^ 2 / (8 * D')) with hη
  have hηp : 0 < η := lt_min (by positivity) (by positivity)
  have hev := Metric.tendstoUniformlyOn_iff.mp hU η hηp
  refine ⟨r⁻¹, hR1, ?_, ?_⟩
  · intro w hw
    have h := hsmall w⁻¹ (hξr w hw)
    rw [hGv κ w (hw0 w hw), norm_inv] at h
    have hgw : 0 < ‖gsans κ w‖ := norm_pos_iff.mpr (hg0ne w (hext w hw))
    rw [inv_le_comm₀ hgw (by positivity), one_div, inv_inv] at h
    linarith [le_max_left D 1]
  · filter_upwards [hev] with n hn
    obtain ⟨hGnd, -, hgnne⟩ := r24_inversion (hκs n)
    have hsph : ∀ ξ ∈ sphere (0 : ℂ) r, ‖G (κs n) ξ - G κ ξ‖ ≤ 1 / (4 * D') := by
      intro ξ hξ
      have hξn : ‖ξ‖ = r := mem_sphere_zero_iff_norm.mp hξ
      have hξ0 : ξ ≠ 0 := fun h => by rw [h, norm_zero] at hξn; linarith
      have hwC : ξ⁻¹ ∈ C := by rw [hC, mem_sphere_zero_iff_norm, norm_inv, hξn]
      have hd := hn ξ⁻¹ hwC
      rw [dist_eq_norm] at hd
      have hm1 := hmle _ hwC
      have hb : m / 2 ≤ ‖gsans (κs n) ξ⁻¹‖ := by
        have h := norm_sub_norm_le (gsans κ ξ⁻¹) (gsans κ ξ⁻¹ - gsans (κs n) ξ⁻¹)
        rw [sub_sub_cancel] at h
        linarith [min_le_left (m / 2) (m ^ 2 / (8 * D'))]
      have ha0 : gsans κ ξ⁻¹ ≠ 0 := hg0ne _ (hCsub hwC)
      have hb0 : gsans (κs n) ξ⁻¹ ≠ 0 := hgnne _ (hCsub hwC)
      have e1 := hGv κ ξ⁻¹ (inv_ne_zero hξ0)
      have e2 := hGv (κs n) ξ⁻¹ (inv_ne_zero hξ0)
      rw [inv_inv] at e1 e2
      rw [e1, e2, inv_sub_inv hb0 ha0, norm_div, norm_mul, div_le_iff₀ (by positivity)]
      calc ‖gsans κ ξ⁻¹ - gsans (κs n) ξ⁻¹‖ ≤ η := hd.le
        _ ≤ m ^ 2 / (8 * D') := min_le_right _ _
        _ = 1 / (4 * D') * (m / 2 * m) := by field_simp; ring
        _ ≤ 1 / (4 * D') * (‖gsans (κs n) ξ⁻¹‖ * ‖gsans κ ξ⁻¹‖) := by gcongr
    have hsub : closedBall (0 : ℂ) r ⊆ unitDisc := closedBall_subset_ball hr1
    have hball : ∀ ξ ∈ closedBall (0 : ℂ) r, ‖G (κs n) ξ - G κ ξ‖ ≤ 1 / (4 * D') := by
      intro ξ hξ
      have hdc : DiffContOnCl ℂ (fun ξ => G (κs n) ξ - G κ ξ) (ball 0 r) :=
        ((hGnd.sub hG0d).mono (by rw [closure_ball 0 hrpos.ne']; exact hsub)).diffContOnCl
      refine norm_le_of_forall_mem_frontier_norm_le isBounded_ball hdc ?_
        (by rw [closure_ball 0 hrpos.ne']; exact hξ)
      rw [frontier_ball 0 hrpos.ne']
      exact hsph
    intro w hw
    have hξ := hξr w hw
    have h1 := hball w⁻¹ (mem_closedBall_zero_iff.mpr hξ)
    have h2 := hsmall w⁻¹ hξ
    have hgn : 0 < ‖gsans (κs n) w‖ := norm_pos_iff.mpr (hgnne w (hext w hw))
    have h3 : ‖G (κs n) w⁻¹‖ ≤ 1 / D' := by
      have h4 := norm_sub_norm_le (G (κs n) w⁻¹) (G κ w⁻¹)
      have h5 : 1 / (4 * D') + 1 / (2 * D') ≤ 1 / D' := by
        rw [div_add_div _ _ (by positivity) (by positivity), div_le_div_iff₀ (by positivity) hD']
        nlinarith
      linarith
    rw [hGv (κs n) w (hw0 w hw), norm_inv, one_div, inv_le_inv₀ hgn hD'] at h3
    linarith [le_max_left D 1]

/-- On `T₀(1)`, `𝒜(𝗀) ∈ A₂¹(𝔻*)`. -/
theorem s36l_psiE_mem {κ : LinfStar} (hκ : κ ∈ LinfStarBall) (hκT : Phi ⟨κ, hκ⟩ ∈ T01) :
    preSchwarzian (gsans κ) ∈ A21fun unitDiscExterior := by
  have hEo : IsOpen unitDiscExterior := isOpen_lt continuous_const continuous_norm
  set p := Phi ⟨κ, hκ⟩ with hp
  have h := (thm_1_12 p).2.2.2.mp hκT
  have heq : Phi (Quotient.out p) = Phi ⟨κ, hκ⟩ := Quotient.out_eq p
  have hc := (s2c_class_pair (Quotient.exact heq)).2
  exact (ab112_A21fun_congr hEo (s36l_preS_eqOn hEo hc)).mp h

theorem s36l_koebe_pos {κ : LinfStar} (hκ : κ ∈ LinfStarBall) {z : ℂ} (hz : z ∈ unitDisc) :
    0 < ‖deriv (fsans κ) z‖ * (1 - ‖z‖ ^ 2) / 4 := by
  have h1 := norm_pos_iff.mpr ((s2c_facts hκ).2.2.2.2.2.2.2.2.2 z hz)
  have h2 := mem_ball_zero_iff.mp hz
  have h3 : 0 < 1 - ‖z‖ ^ 2 := by nlinarith [norm_nonneg z]
  positivity

theorem s36l_K2row_cont {κ : LinfStar} (hκ : κ ∈ LinfStarBall) {z : ℂ} (hz : z ∈ unitDisc) :
    ContinuousOn (fun w => kerK2 (fsans κ) (gsans κ) z w) unitDiscExterior := by
  have hEo : IsOpen unitDiscExterior := isOpen_lt continuous_const continuous_norm
  have hgd := (s2c_facts hκ).2.2.2.2.1
  have hg'c : ContinuousOn (deriv (gsans κ)) unitDiscExterior := ((hgd.analyticOnNhd hEo).deriv).continuousOn
  show ContinuousOn (fun w => 1 / (π : ℂ) * (deriv (fsans κ) z * deriv (gsans κ) w /
    (fsans κ z - gsans κ w) ^ 2)) unitDiscExterior
  refine continuousOn_const.mul ((continuousOn_const.mul hg'c).div
    ((continuousOn_const.sub hgd.continuousOn).pow 2) fun w hw => pow_ne_zero 2 ?_)
  intro h
  have h1 := s36l_koebe_sep hκ hz hw
  rw [norm_sub_rev, h, norm_zero] at h1
  linarith [s36l_koebe_pos hκ hz]

theorem s36l_K2row_L2 {κ : LinfStar} (hκ : κ ∈ LinfStarBall) {z : ℂ} (hz : z ∈ unitDisc) :
    (∫⁻ w in unitDiscExterior, ‖kerK2 (fsans κ) (gsans κ) z w‖ₑ ^ 2) ≠ ∞ :=
  ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)
    (s36l_K2row_bound (isOpen_lt continuous_const continuous_norm) (s2c_facts hκ).2.2.2.2.1
      (s2c_facts hκ).2.2.2.2.2.1 (s36l_koebe_pos hκ hz) fun w hw => s36l_koebe_sep hκ hz hw)

/-- `𝖿ₙ(z) → 𝖿(z)` and `𝖿ₙ'(z) → 𝖿'(z)` from `𝖿ₙ = M_{cₙ} ∘ (𝖿(ρₙ ·)/ρₙ)`, `cₙ → 0`. -/
theorem s36l_fn_conv {f : ℂ → ℂ} (hfd : DifferentiableOn ℂ f unitDisc) {ρ : ℕ → ℝ}
    (hρ : ∀ n, 0 < ρ n ∧ ρ n < 1) (hρl : Tendsto ρ atTop (𝓝 1)) {c : ℕ → ℂ} (hc0 : Tendsto c atTop (𝓝 0))
    {h : ℕ → ℂ → ℂ} (hh : ∀ n, ∀ u ∈ unitDisc, 1 + c n * (f ((ρ n : ℂ) * u) / (ρ n : ℂ)) ≠ 0 ∧
      h n u = f ((ρ n : ℂ) * u) / (ρ n : ℂ) / (1 + c n * (f ((ρ n : ℂ) * u) / (ρ n : ℂ))))
    {z : ℂ} (hz : z ∈ unitDisc) :
    Tendsto (fun n => h n z) atTop (𝓝 (f z)) ∧ Tendsto (fun n => deriv (h n) z) atTop (𝓝 (deriv f z)) := by
  have hrN : Tendsto (fun n => (ρ n : ℂ)) atTop (𝓝 1) := by
    have h := (Complex.continuous_ofReal.tendsto 1).comp hρl
    rw [Complex.ofReal_one] at h
    exact h
  have hrz : Tendsto (fun n => (ρ n : ℂ) * z) atTop (𝓝 z) := by simpa using hrN.mul_const z
  have ha := hfd.analyticAt (isOpen_ball.mem_nhds hz)
  have hF : Tendsto (fun n => f ((ρ n : ℂ) * z) / (ρ n : ℂ)) atTop (𝓝 (f z)) := by
    have h := (ha.continuousAt.tendsto.comp hrz).div hrN one_ne_zero
    rw [div_one] at h
    exact h
  have hden : Tendsto (fun n => 1 + c n * (f ((ρ n : ℂ) * z) / (ρ n : ℂ))) atTop (𝓝 1) := by
    have h := tendsto_const_nhds (x := (1 : ℂ)).add (hc0.mul hF)
    rw [zero_mul, add_zero] at h
    exact h
  constructor
  · have h := hF.div hden one_ne_zero
    rw [div_one] at h
    exact h.congr fun n => ((hh n z hz).2).symm
  · have hd : ∀ n, deriv (h n) z =
        deriv f ((ρ n : ℂ) * z) / (1 + c n * (f ((ρ n : ℂ) * z) / (ρ n : ℂ))) ^ 2 := by
      intro n
      obtain ⟨hρ0, hρ1⟩ := hρ n
      have hr0 : (ρ n : ℂ) ≠ 0 := by exact_mod_cast hρ0.ne'
      obtain ⟨hFa, hFd, -⟩ := s36l_dilF hfd hr0 (s36l_mul_mem hρ0 hρ1.le hz)
      have hev : h n =ᶠ[𝓝 z]
          fun u => f ((ρ n : ℂ) * u) / (ρ n : ℂ) / (1 + c n * (f ((ρ n : ℂ) * u) / (ρ n : ℂ))) := by
        filter_upwards [isOpen_ball.mem_nhds hz] with u hu
        exact (hh n u hu).2
      rw [hev.deriv_eq, s36l_mob_comp_deriv (F := fun u => f ((ρ n : ℂ) * u) / (ρ n : ℂ))
        hFa.differentiableAt (hh n z hz).1, hFd]
    have hdl : Tendsto (fun n => deriv f ((ρ n : ℂ) * z)) atTop (𝓝 (deriv f z)) :=
      ha.deriv.continuousAt.tendsto.comp hrz
    have h := hdl.div (hden.pow 2) (by norm_num)
    rw [one_pow, div_one] at h
    exact h.congr fun n => (hd n).symm

/-- Pointwise convergence of `G`, `G'`, `G''` from locally uniform convergence of holomorphic maps on `𝔻*`. -/
theorem s36l_gconv_pt {G : ℕ → ℂ → ℂ} {g : ℂ → ℂ}
    (hconv : TendstoLocallyUniformlyOn G g atTop unitDiscExterior)
    (hGd : ∀ n, DifferentiableOn ℂ (G n) unitDiscExterior) {w : ℂ} (hw : w ∈ unitDiscExterior) :
    Tendsto (fun n => G n w) atTop (𝓝 (g w)) ∧ Tendsto (fun n => deriv (G n) w) atTop (𝓝 (deriv g w)) ∧
      Tendsto (fun n => deriv (deriv (G n)) w) atTop (𝓝 (deriv (deriv g) w)) := by
  have hEo : IsOpen unitDiscExterior := isOpen_lt continuous_const continuous_norm
  have h1 := hconv.deriv (Eventually.of_forall hGd) hEo
  have hGd' : ∀ n, DifferentiableOn ℂ (deriv (G n)) unitDiscExterior := fun n =>
    ((hGd n).analyticOnNhd hEo).deriv.differentiableOn
  have h2 := h1.deriv (Eventually.of_forall hGd') hEo
  exact ⟨hconv.tendsto_at hw, h1.tendsto_at hw, h2.tendsto_at hw⟩

/-- `𝒮(M_c ∘ (f(r ·)/r))(w) = r² 𝒮(f)(rw)`. -/
theorem s36l_S_dil {f : ℂ → ℂ} (hfd : DifferentiableOn ℂ f unitDisc) (hfd' : ∀ y ∈ unitDisc, deriv f y ≠ 0)
    {c : ℂ} {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) {w : ℂ} (hw : w ∈ unitDisc)
    (h1 : 1 + c * (f ((r : ℂ) * w) / (r : ℂ)) ≠ 0) :
    schwarzianHol (fun u => f ((r : ℂ) * u) / (r : ℂ) / (1 + c * (f ((r : ℂ) * u) / (r : ℂ)))) w =
      (r : ℂ) ^ 2 * schwarzianHol f ((r : ℂ) * w) := by
  have hrC : (r : ℂ) ≠ 0 := by exact_mod_cast hr0.ne'
  set F : ℂ → ℂ := fun u => f ((r : ℂ) * u) / (r : ℂ) with hF
  -- the open set where everything is defined
  have hO : IsOpen {u : ℂ | (r : ℂ) * u ∈ unitDisc} := isOpen_ball.preimage (continuous_const.mul continuous_id)
  have hwO : w ∈ {u : ℂ | (r : ℂ) * u ∈ unitDisc} := s36l_mul_mem hr0 hr1.le hw
  have hFa : ∀ u ∈ {u : ℂ | (r : ℂ) * u ∈ unitDisc}, AnalyticAt ℂ F u := fun u hu => (s36l_dilF hfd hrC hu).1
  have hFd : ∀ u ∈ {u : ℂ | (r : ℂ) * u ∈ unitDisc}, deriv F u ≠ 0 := fun u hu => by
    rw [(s36l_dilF hfd hrC hu).2.1]; exact hfd' _ hu
  have hcont : ContinuousAt (fun u => 1 + c * F u) w :=
    continuousAt_const.add (continuousAt_const.mul (hFa w hwO).continuousAt)
  have hev : preSchwarzian (fun u => F u / (1 + c * F u)) =ᶠ[𝓝 w]
      fun u => preSchwarzian F u - 2 * c * deriv F u / (1 + c * F u) := by
    filter_upwards [hO.mem_nhds hwO, hcont.eventually_ne h1] with u hu hu1
    exact s36l_mob_comp_preS (hFa u hu) (hFd u hu) hu1
  have ha := hFa w hwO
  have hPF : HasDerivAt (preSchwarzian F) (deriv (preSchwarzian F) w) w :=
    (ha.deriv.deriv.div ha.deriv (hFd w hwO)).differentiableAt.hasDerivAt
  have hE : HasDerivAt (fun u => 2 * c * deriv F u / (1 + c * F u))
      ((2 * c * deriv (deriv F) w * (1 + c * F w) - 2 * c * deriv F w * (c * deriv F w)) / (1 + c * F w) ^ 2) w :=
    ((ha.deriv.differentiableAt.hasDerivAt.const_mul (2 * c)).div
      ((ha.differentiableAt.hasDerivAt.const_mul c).const_add 1) h1)
  have hSF : deriv (preSchwarzian F) w - 1 / 2 * (preSchwarzian F w) ^ 2 =
      (r : ℂ) ^ 2 * schwarzianHol f ((r : ℂ) * w) := by
    have hfa : AnalyticAt ℂ f ((r : ℂ) * w) := hfd.analyticAt (isOpen_ball.mem_nhds hwO)
    have hS := schwarzianHol_mul_comp_mul (f := f) (z := w) (inv_ne_zero hrC) hrC hfa (hfd' _ hwO)
    have he : F = fun u => (r : ℂ)⁻¹ * f ((r : ℂ) * u) := by
      funext u
      exact div_eq_inv_mul _ _
    rw [← hS, ← he]
    rfl
  show deriv (preSchwarzian (fun u => F u / (1 + c * F u))) w -
    1 / 2 * (preSchwarzian (fun u => F u / (1 + c * F u)) w) ^ 2 = _
  rw [hev.deriv_eq, hev.eq_of_nhds, show deriv (fun u => preSchwarzian F u - 2 * c * deriv F u / (1 + c * F u)) w = _
    from (hPF.sub hE).deriv, ← hSF]
  have hd0 := hFd w hwO
  have h1' : 1 + c * F w ≠ 0 := h1
  unfold preSchwarzian
  field_simp
  ring

/-- On `T₀(1)`, `𝒮(𝖿) ∈ A₂(𝔻)` and `𝒮(𝗀) ∈ A₂(𝔻*)`. -/
theorem s36l_S_mem {κ : LinfStar} (hκ : κ ∈ LinfStarBall) (hκT : Phi ⟨κ, hκ⟩ ∈ T01) :
    schwarzianHol (fsans κ) ∈ A2fun unitDisc ∧ schwarzianHol (gsans κ) ∈ A2fun unitDiscExterior := by
  have hEo : IsOpen unitDiscExterior := isOpen_lt continuous_const continuous_norm
  set p := Phi ⟨κ, hκ⟩ with hp
  have heq : Phi (Quotient.out p) = Phi ⟨κ, hκ⟩ := Quotient.out_eq p
  have hc := s2c_class_pair (Quotient.exact heq)
  exact ⟨(ab112_A2fun_congr isOpen_ball (ab112_S_eqOn isOpen_ball hc.1)).mp ((thm_1_12 p).1.mp hκT),
    (ab112_A2fun_congr hEo (ab112_S_eqOn hEo hc.2)).mp ((thm_1_12 p).2.2.1.mp hκT)⟩

/-- `L²` Vitali: uniformly square-integrable, a.e. convergent sequences converge in `L²` on finite measures. -/
theorem s36l_L2_vitali {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]
    {u : ℕ → α → ℂ} {u0 : α → ℂ} (hu : ∀ n, AEStronglyMeasurable (u n) μ) (hu0 : AEStronglyMeasurable u0 μ)
    (hu0L : (∫⁻ x, ‖u0 x‖ₑ ^ 2 ∂μ) ≠ ∞)
    (hUI : ∀ ε > (0 : ℝ≥0∞), ∃ δ > (0 : ℝ≥0∞), ∀ n s, MeasurableSet s → μ s ≤ δ →
      ∫⁻ x in s, ‖u n x‖ₑ ^ 2 ∂μ ≤ ε)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun n => u n x) atTop (𝓝 (u0 x))) :
    Tendsto (fun n => ∫⁻ x, ‖u n x - u0 x‖ₑ ^ 2 ∂μ) atTop (𝓝 0) := by
  have key : ∀ (ν : Measure α) (v : α → ℂ), AEStronglyMeasurable v ν →
      eLpNorm v 2 ν = (∫⁻ x, ‖v x‖ₑ ^ 2 ∂ν) ^ (1 / 2 : ℝ) := by
    intro ν v hv
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top hv]
    simp only [ENNReal.toReal_ofNat, ENNReal.rpow_ofNat]
  have key2 : ∀ (ν : Measure α) (v : α → ℂ), AEStronglyMeasurable v ν →
      eLpNorm v 2 ν ^ 2 = ∫⁻ x, ‖v x‖ₑ ^ 2 ∂ν := by
    intro ν v hv
    rw [key ν v hv, ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
    norm_num
  have hmem : MemLp u0 2 μ := by
    show eLpNorm u0 2 μ < ∞
    rw [key μ u0 hu0]
    exact ENNReal.rpow_lt_top_of_nonneg (by norm_num) hu0L
  have hui : UnifIntegrable u 2 μ := by
    rw [unifIntegrable_iff']
    intro ε hε
    obtain ⟨δ, hδ, hδs⟩ := hUI (ε ^ 2) (ENNReal.pow_pos hε 2)
    refine ⟨δ, hδ, fun n s hs hμs => ?_⟩
    rw [key _ _ (hu n).restrict]
    calc (∫⁻ x, ‖u n x‖ₑ ^ 2 ∂μ.restrict s) ^ (1 / 2 : ℝ) ≤ (ε ^ 2) ^ (1 / 2 : ℝ) :=
          ENNReal.rpow_le_rpow (hδs n s hs hμs) (by norm_num)
      _ = ε := by rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]; norm_num
  have hV := tendsto_Lp_finite_of_tendsto_ae one_le_two ENNReal.ofNat_ne_top hu hmem hui hlim
  have h2 := ((ENNReal.continuous_pow 2).tendsto 0).comp hV
  rw [zero_pow two_ne_zero] at h2
  refine h2.congr fun n => ?_
  simp only [Function.comp_apply]
  rw [key2 μ _ ((hu n).sub hu0)]
  rfl

/-- The representative `out [κ]` has the same `𝖿` on `𝔻` and `𝗀` on `𝔻*`. -/
theorem s36l_class_out {κ : LinfStar} (hκ : κ ∈ LinfStarBall) :
    EqOn (fsans ((Quotient.out (Phi ⟨κ, hκ⟩) : LinfStarBall) : LinfStar)) (fsans κ) unitDisc ∧
      EqOn (gsans ((Quotient.out (Phi ⟨κ, hκ⟩) : LinfStarBall) : LinfStar)) (gsans κ) unitDiscExterior := by
  have heq : Phi (Quotient.out (Phi ⟨κ, hκ⟩)) = Phi ⟨κ, hκ⟩ := Quotient.out_eq _
  have hc := s2c_class_pair (Quotient.exact heq)
  exact hc

/-- Inward dilation on a ball: `∬_{B_R} g(rz) ≤ r⁻² ∬_{B_R} g`, `0 < r ≤ 1`. -/
theorem s36l_dil_lint_le (g : ℂ → ℝ≥0∞) {R r : ℝ} (hr0 : 0 < r) (hr1 : r ≤ 1) :
    (∫⁻ z in closedBall (0 : ℂ) R, g ((r : ℂ) * z)) ≤
      ENNReal.ofReal (r ^ 2)⁻¹ * ∫⁻ z in closedBall (0 : ℂ) R, g z := by
  have hr0' : r ≠ 0 := hr0.ne'
  set B : Set ℂ := closedBall (0 : ℂ) R with hB
  have hBm : MeasurableSet B := measurableSet_closedBall
  have hpt : ∀ z, B.indicator (fun z => g ((r : ℂ) * z)) z ≤ B.indicator g (r • z) := by
    intro z
    by_cases hz : z ∈ B
    · have hz' : r • z ∈ B := by
        rw [hB, mem_closedBall_zero_iff, norm_smul, Real.norm_of_nonneg hr0.le]
        have := mem_closedBall_zero_iff.mp hz
        nlinarith [norm_nonneg z]
      rw [indicator_of_mem hz, indicator_of_mem hz', Complex.real_smul]
    · rw [indicator_of_notMem hz]
      exact bot_le
  have hmap : (∫⁻ w, B.indicator g (r • w)) = ENNReal.ofReal |(r ^ 2)⁻¹| * ∫⁻ u, B.indicator g u := by
    have h1 := lintegral_map_equiv (B.indicator g) (Homeomorph.smulOfNeZero r hr0').toMeasurableEquiv
      (μ := (volume : Measure ℂ))
    have h2 := Measure.map_addHaar_smul (volume : Measure ℂ) hr0'
    rw [Complex.finrank_real_complex] at h2
    have h3 : ⇑(Homeomorph.smulOfNeZero r hr0').toMeasurableEquiv = fun x : ℂ => r • x := rfl
    rw [h3, h2, lintegral_smul_measure] at h1
    rw [← h1]
    try rfl
  calc (∫⁻ z in B, g ((r : ℂ) * z)) = ∫⁻ z, B.indicator (fun z => g ((r : ℂ) * z)) z :=
        (lintegral_indicator hBm _).symm
    _ ≤ ∫⁻ z, B.indicator g (r • z) := lintegral_mono hpt
    _ = ENNReal.ofReal (r ^ 2)⁻¹ * ∫⁻ z in B, g z := by
        rw [hmap, lintegral_indicator hBm, abs_of_pos (by positivity)]

/-- `L¹` continuity of inward dilations for the weight `(1 + |z|)⁻³` (bounded measurable functions). -/
theorem s36l_dilL1 {h : ℂ → ℂ} (hh : AEStronglyMeasurable h volume) {B : ℝ} (hB0 : 0 < B)
    (hB : ∀ᵐ z, ‖h z‖ ≤ B) {r : ℕ → ℝ} (hr0 : ∀ n, 1 / 2 ≤ r n) (hr1 : ∀ n, r n ≤ 1)
    (hrl : Tendsto r atTop (𝓝 1)) :
    Tendsto (fun n => ∫⁻ z, ENNReal.ofReal ((1 + ‖z‖) ^ (-3 : ℝ)) * ‖h ((r n : ℂ) * z) - h z‖ₑ)
      atTop (𝓝 0) := by
  set ω : ℂ → ℝ≥0∞ := fun z => ENNReal.ofReal ((1 + ‖z‖) ^ (-3 : ℝ)) with hω
  have hrpos : ∀ n, 0 < r n := fun n => lt_of_lt_of_le (by norm_num) (hr0 n)
  -- transfer of measurability and bounds through the dilation
  have hq : ∀ n, Measure.QuasiMeasurePreserving (fun z : ℂ => (r n : ℂ) * z) volume volume := by
    intro n
    have hdet : LinearMap.det ((r n : ℝ) • (LinearMap.id : ℂ →ₗ[ℝ] ℂ)) ≠ 0 := by
      rw [LinearMap.det_smul, LinearMap.det_id, mul_one, Complex.finrank_real_complex]
      exact pow_ne_zero 2 (hrpos n).ne'
    have h := MeasureTheory.Measure.LinearMap.quasiMeasurePreserving (μ := (volume : Measure ℂ)) _ hdet
    convert h using 1
  have hhr : ∀ n, AEStronglyMeasurable (fun z => h ((r n : ℂ) * z)) volume := fun n =>
    hh.comp_quasiMeasurePreserving (hq n)
  have hBr : ∀ n, ∀ᵐ z, ‖h ((r n : ℂ) * z)‖ ≤ B := fun n => (hq n).ae hB
  rw [ENNReal.tendsto_atTop_zero]
  intro ε hε
  obtain ⟨e, he0, he⟩ : ∃ e : ℝ, 0 < e ∧ ENNReal.ofReal e ≤ ε := by
    obtain ⟨e, he0, he1, he2⟩ := ENNReal.lt_iff_exists_real_btwn.mp hε
    exact ⟨e, ENNReal.ofReal_pos.mp he1, he2.le⟩
  -- the tail radius
  set R : ℝ := max 1 (12 * π * B / e) with hR
  have hR1 : 1 ≤ R := le_max_left _ _
  have hR0 : 0 < R := by linarith
  have htail : (∫⁻ z in {z : ℂ | R < ‖z - 0‖}, ‖z - 0‖ₑ ^ (-(3 : ℝ))) = ENNReal.ofReal (2 * π) * ENNReal.ofReal (R⁻¹) := by
    rw [lintegral_compl_ball_sub_enorm_rpow_neg (by norm_num) hR0 0]
    congr 1
    congr 1
    rw [show (2 : ℝ) - 3 = -1 by norm_num, Real.rpow_neg_one]
    ring
  -- the approximation on the ball
  set Bl : Set ℂ := closedBall (0 : ℂ) R with hBl
  have hBlm : MeasurableSet Bl := measurableSet_closedBall
  have hBlf : volume Bl < ∞ := measure_closedBall_lt_top
  set h1 : ℂ → ℂ := Bl.indicator h with hh1
  have hh1i : Integrable h1 volume := by
    refine (integrable_indicator_iff hBlm).mpr ?_
    exact Measure.integrableOn_of_bounded (M := B) hBlf.ne hh (ae_restrict_of_ae hB)
  set δ : ℝ := e / 30 with hδ
  have hδ0 : 0 < δ := by positivity
  obtain ⟨φ, hφc, hφ1, hφcont, hφi⟩ := hh1i.exists_hasCompactSupport_integral_sub_le hδ0
  have hφu := hφc.uniformContinuous_of_continuous hφcont
  set V : ℝ := (volume Bl).toReal + 1 with hV
  have hV0 : 0 < V := by positivity
  obtain ⟨η, hη0, hη⟩ := Metric.uniformContinuous_iff.mp hφu (δ / V) (by positivity)
  -- choose `n` large
  have hev : ∀ᶠ n in atTop, (1 - r n) * R < η := by
    have h := ((tendsto_const_nhds (x := (1 : ℝ))).sub hrl).mul_const R
    rw [sub_self, zero_mul] at h
    exact h.eventually (gt_mem_nhds hη0)
  obtain ⟨N, hN⟩ := eventually_atTop.mp hev
  refine ⟨N, fun n hn => le_trans ?_ he⟩
  have hηn := hN n hn
  have hrn0 := hrpos n
  have hrn1 := hr1 n
  have hrn2 := hr0 n
  -- split
  have hsplit : (∫⁻ z, ω z * ‖h ((r n : ℂ) * z) - h z‖ₑ) ≤
      (∫⁻ z in Bl, ‖h ((r n : ℂ) * z) - h z‖ₑ) +
        ∫⁻ z in {z : ℂ | R < ‖z - 0‖}, ENNReal.ofReal (2 * B) * ‖z - 0‖ₑ ^ (-(3 : ℝ)) := by
    have hU : (univ : Set ℂ) ⊆ Bl ∪ {z : ℂ | R < ‖z - 0‖} := by
      intro z _
      by_cases hz : ‖z‖ ≤ R
      · exact Or.inl (mem_closedBall_zero_iff.mpr hz)
      · exact Or.inr (show R < ‖z - 0‖ by rw [sub_zero]; exact not_le.mp hz)
    calc (∫⁻ z, ω z * ‖h ((r n : ℂ) * z) - h z‖ₑ)
        = ∫⁻ z in univ, ω z * ‖h ((r n : ℂ) * z) - h z‖ₑ := (setLIntegral_univ _).symm
      _ ≤ ∫⁻ z in Bl ∪ {z : ℂ | R < ‖z - 0‖}, ω z * ‖h ((r n : ℂ) * z) - h z‖ₑ := lintegral_mono_set hU
      _ ≤ (∫⁻ z in Bl, ω z * ‖h ((r n : ℂ) * z) - h z‖ₑ) +
            ∫⁻ z in {z : ℂ | R < ‖z - 0‖}, ω z * ‖h ((r n : ℂ) * z) - h z‖ₑ := lintegral_union_le _ _ _
      _ ≤ _ := by
          refine add_le_add (lintegral_mono fun z => ?_) ?_
          · calc ω z * ‖h ((r n : ℂ) * z) - h z‖ₑ ≤ 1 * ‖h ((r n : ℂ) * z) - h z‖ₑ := by
                  gcongr
                  rw [hω]
                  refine ENNReal.ofReal_le_one.mpr ?_
                  exact Real.rpow_le_one_of_one_le_of_nonpos (by linarith [norm_nonneg z]) (by norm_num)
              _ = _ := one_mul _
          · refine setLIntegral_mono_ae ((measurable_const.mul
              ((measurable_id.sub measurable_const).enorm.pow_const _)).aemeasurable) ?_
            filter_upwards [hB, hBr n] with z hz1 hz2 hzR
            have hzR' : R < ‖z‖ := by simpa using hzR
            have hz0 : 0 < ‖z‖ := by linarith
            rw [mul_comm]
            gcongr
            · rw [← ofReal_norm]
              refine ENNReal.ofReal_le_ofReal ?_
              calc ‖h ((r n : ℂ) * z) - h z‖ ≤ ‖h ((r n : ℂ) * z)‖ + ‖h z‖ := norm_sub_le _ _
                _ ≤ 2 * B := by linarith
            · rw [hω, sub_zero, ← ofReal_norm, ENNReal.ofReal_rpow_of_pos hz0]
              refine ENNReal.ofReal_le_ofReal ?_
              exact Real.rpow_le_rpow_of_nonpos hz0 (by linarith) (by norm_num)
  refine hsplit.trans ?_
  -- the tail
  have hT : (∫⁻ z in {z : ℂ | R < ‖z - 0‖}, ENNReal.ofReal (2 * B) * ‖z - 0‖ₑ ^ (-(3 : ℝ))) ≤
      ENNReal.ofReal (e / 3) := by
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, htail, ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    have hRb : 12 * π * B / e ≤ R := le_max_right _ _
    rw [div_le_iff₀ he0] at hRb
    rw [show 2 * B * (2 * π * R⁻¹) = 4 * π * B / R by field_simp; ring, div_le_iff₀ hR0]
    nlinarith [Real.pi_pos]
  -- the ball
  have hball : (∫⁻ z in Bl, ‖h ((r n : ℂ) * z) - h z‖ₑ) ≤ ENNReal.ofReal (e / 3) := by
    have hrz : ∀ z ∈ Bl, (r n : ℂ) * z ∈ Bl := fun z hz => by
      rw [hBl, mem_closedBall_zero_iff, norm_mul, Complex.norm_real, Real.norm_of_nonneg hrn0.le]
      have := mem_closedBall_zero_iff.mp hz
      nlinarith [norm_nonneg z]
    have hpt : ∀ z ∈ Bl, ‖h ((r n : ℂ) * z) - h z‖ₑ ≤
        ‖h1 ((r n : ℂ) * z) - φ ((r n : ℂ) * z)‖ₑ + ‖φ ((r n : ℂ) * z) - φ z‖ₑ + ‖h1 z - φ z‖ₑ := by
      intro z hz
      have e1 : h ((r n : ℂ) * z) = h1 ((r n : ℂ) * z) := (indicator_of_mem (hrz z hz) h).symm
      have e2 : h z = h1 z := (indicator_of_mem hz h).symm
      rw [e1, e2]
      calc ‖h1 ((r n : ℂ) * z) - h1 z‖ₑ = ‖(h1 ((r n : ℂ) * z) - φ ((r n : ℂ) * z)) +
            (φ ((r n : ℂ) * z) - φ z) + -(h1 z - φ z)‖ₑ := by congr 1; ring
        _ ≤ _ := by
            refine (enorm_add_le _ _).trans ?_
            rw [enorm_neg]
            gcongr
            exact enorm_add_le _ _
    have hmid : ∀ z ∈ Bl, ‖φ ((r n : ℂ) * z) - φ z‖ₑ ≤ ENNReal.ofReal (δ / V) := by
      intro z hz
      have hd : dist ((r n : ℂ) * z) z < η := by
        rw [dist_eq_norm, show (r n : ℂ) * z - z = ((r n : ℂ) - 1) * z by ring, norm_mul,
          show ((r n : ℂ) - 1) = ((r n - 1 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
          Real.norm_of_nonpos (by linarith)]
        have := mem_closedBall_zero_iff.mp hz
        nlinarith [norm_nonneg z]
      have := hη hd
      rw [dist_eq_norm] at this
      rw [← ofReal_norm]
      exact ENNReal.ofReal_le_ofReal this.le
    have hint1 : (∫⁻ z in Bl, ‖h1 z - φ z‖ₑ) ≤ ENNReal.ofReal δ := by
      refine (setLIntegral_le_lintegral _ _).trans ?_
      have h := ofReal_integral_norm_eq_lintegral_enorm (hh1i.sub hφi)
      simp only [Pi.sub_apply] at h
      rw [← h]
      exact ENNReal.ofReal_le_ofReal hφ1
    have hm1 : AEMeasurable (fun z => ‖h1 ((r n : ℂ) * z) - φ ((r n : ℂ) * z)‖ₑ) (volume.restrict Bl) :=
      (((hh1i.1.sub hφi.1).comp_quasiMeasurePreserving (hq n)).enorm).restrict
    have hm2 : AEMeasurable (fun z => ‖φ ((r n : ℂ) * z) - φ z‖ₑ) (volume.restrict Bl) := by fun_prop
    calc (∫⁻ z in Bl, ‖h ((r n : ℂ) * z) - h z‖ₑ)
        ≤ ∫⁻ z in Bl, (‖h1 ((r n : ℂ) * z) - φ ((r n : ℂ) * z)‖ₑ + ‖φ ((r n : ℂ) * z) - φ z‖ₑ +
            ‖h1 z - φ z‖ₑ) := setLIntegral_mono_ae (by fun_prop) (Eventually.of_forall hpt)
      _ = (∫⁻ z in Bl, ‖h1 ((r n : ℂ) * z) - φ ((r n : ℂ) * z)‖ₑ) + (∫⁻ z in Bl, ‖φ ((r n : ℂ) * z) - φ z‖ₑ) +
            ∫⁻ z in Bl, ‖h1 z - φ z‖ₑ := by
          rw [lintegral_add_left' (f := fun z => ‖h1 ((r n : ℂ) * z) - φ ((r n : ℂ) * z)‖ₑ +
            ‖φ ((r n : ℂ) * z) - φ z‖ₑ) (hm1.add hm2), lintegral_add_left' hm1]
      _ ≤ ENNReal.ofReal (r n ^ 2)⁻¹ * ENNReal.ofReal δ + (ENNReal.ofReal (δ / V) * volume Bl) +
            ENNReal.ofReal δ := by
          gcongr
          · exact (s36l_dil_lint_le (fun u => ‖h1 u - φ u‖ₑ) hrn0 hrn1).trans (by gcongr)
          · calc (∫⁻ z in Bl, ‖φ ((r n : ℂ) * z) - φ z‖ₑ) ≤ ∫⁻ _z in Bl, ENNReal.ofReal (δ / V) :=
                  setLIntegral_mono (by fun_prop) hmid
              _ = _ := setLIntegral_const _ _
      _ ≤ ENNReal.ofReal (4 * δ) + ENNReal.ofReal δ + ENNReal.ofReal δ := by
          gcongr
          · rw [← ENNReal.ofReal_mul (by positivity)]
            refine ENNReal.ofReal_le_ofReal ?_
            have : (r n ^ 2)⁻¹ ≤ 4 := by
              rw [inv_le_comm₀ (by positivity) (by norm_num)]
              nlinarith
            nlinarith
          · rw [← ENNReal.ofReal_toReal hBlf.ne, ← ENNReal.ofReal_mul (by positivity)]
            refine ENNReal.ofReal_le_ofReal ?_
            rw [div_mul_eq_mul_div, div_le_iff₀ hV0]
            nlinarith [ENNReal.toReal_nonneg (a := volume Bl)]
      _ ≤ ENNReal.ofReal (e / 3) := by
          rw [← ENNReal.ofReal_add (by positivity) (by positivity),
            ← ENNReal.ofReal_add (by positivity) (by positivity)]
          refine ENNReal.ofReal_le_ofReal ?_
          rw [hδ]
          linarith
  calc _ ≤ ENNReal.ofReal (e / 3) + ENNReal.ofReal (e / 3) := add_le_add hball hT
    _ ≤ ENNReal.ofReal e := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
        exact ENNReal.ofReal_le_ofReal (by linarith)

/-! ### The dilation approximants -/

/-- A dilation sequence `ρₙ ↑ 1` along which `extB κ (ρₙ ·) → extB κ` a.e. (continuity of dilation in `L¹_loc`
and an a.e. convergent subsequence). -/
theorem s36l_dil_seq (κ : LinfStar) :
    ∃ ρ : ℕ → ℝ, (∀ n, 0 < ρ n ∧ ρ n < 1) ∧ Tendsto ρ atTop (𝓝 1) ∧
      ∀ᵐ z, Tendsto (fun n => extB κ ((ρ n : ℂ) * z)) atTop (𝓝 (extB κ z)) := by
  have hEm : MeasurableSet unitDiscExterior := (isOpen_lt continuous_const continuous_norm).measurableSet
  set r : ℕ → ℝ := fun n => 1 - 1 / ((n : ℝ) + 2) with hrdef
  have hr0 : ∀ n, 1 / 2 ≤ r n := fun n => by
    rw [hrdef]; dsimp only
    have : 1 / ((n : ℝ) + 2) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) (by linarith [n.cast_nonneg (α := ℝ)])
    linarith
  have hr1 : ∀ n, r n < 1 := fun n => by
    rw [hrdef]; dsimp only
    have : 0 < 1 / ((n : ℝ) + 2) := by positivity
    linarith
  have hrl : Tendsto r atTop (𝓝 1) := by
    have h := (tendsto_const_nhds (x := (1 : ℝ))).sub (Tendsto.div_atTop (tendsto_const_nhds (x := (1 : ℝ)))
      (tendsto_natCast_atTop_atTop.atTop_add (tendsto_const_nhds (x := (2 : ℝ)))))
    rw [sub_zero] at h
    exact h
  have hh : AEStronglyMeasurable (extB κ) volume :=
    (aestronglyMeasurable_indicator_iff hEm).mpr (Lp.aestronglyMeasurable κ)
  have hB : ∀ᵐ z, ‖extB κ z‖ ≤ ‖κ‖ + 1 := by
    filter_upwards [(ae_restrict_iff' hEm).mp (LinfStar_ae_norm_le κ)] with z hz
    unfold extB
    by_cases hzE : z ∈ unitDiscExterior
    · rw [indicator_of_mem hzE]; linarith [hz hzE]
    · rw [indicator_of_notMem hzE, norm_zero]; positivity
  have hL := s36l_dilL1 hh (by positivity) hB hr0 (fun n => (hr1 n).le) hrl
  set ω : ℂ → ℝ≥0∞ := fun z => ENNReal.ofReal ((1 + ‖z‖) ^ (-3 : ℝ)) with hω
  have hωm : Measurable ω := ENNReal.measurable_ofReal.comp ((measurable_const.add measurable_norm).pow_const _)
  have hω0 : ∀ z, ω z ≠ 0 := fun z =>
    (ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos (by linarith [norm_nonneg z]) _)).ne'
  have hac := withDensity_absolutelyContinuous (volume : Measure ℂ) ω
  have hq : ∀ n, Measure.QuasiMeasurePreserving (fun z : ℂ => (r n : ℂ) * z) volume volume := by
    intro n
    have hdet : LinearMap.det ((r n : ℝ) • (LinearMap.id : ℂ →ₗ[ℝ] ℂ)) ≠ 0 := by
      rw [LinearMap.det_smul, LinearMap.det_id, mul_one, Complex.finrank_real_complex]
      exact pow_ne_zero 2 (lt_of_lt_of_le (by norm_num) (hr0 n)).ne'
    have h := MeasureTheory.Measure.LinearMap.quasiMeasurePreserving (μ := (volume : Measure ℂ)) _ hdet
    convert h using 1
  have hfm : ∀ n, AEStronglyMeasurable (fun z => extB κ ((r n : ℂ) * z) - extB κ z) volume := fun n =>
    (hh.comp_quasiMeasurePreserving (hq n)).sub hh
  have hE : Tendsto (fun n => eLpNorm ((fun n z => extB κ ((r n : ℂ) * z)) n - extB κ) 1
      (volume.withDensity ω)) atTop (𝓝 0) := by
    refine hL.congr fun n => ?_
    symm
    show eLpNorm (fun z => extB κ ((r n : ℂ) * z) - extB κ z) 1 (volume.withDensity ω) = _
    rw [eLpNorm_one_eq_lintegral_enorm ((hfm n).mono_ac hac),
      lintegral_withDensity_eq_lintegral_mul₀ (μ := volume) hωm.aemeasurable (hfm n).enorm]
    rfl
  obtain ⟨ns, hns, hae'⟩ := (tendstoInMeasure_of_tendsto_eLpNorm one_ne_zero hE).exists_seq_tendsto_ae
  refine ⟨fun i => r (ns i), fun i => ⟨lt_of_lt_of_le (by norm_num) (hr0 _), hr1 _⟩,
    hrl.comp hns.tendsto_atTop, ?_⟩
  filter_upwards [(ae_withDensity_iff hωm).mp hae'] with z hz
  exact hz (hω0 z)

/-- The dilated coefficients vanish on `1 < |z| < 1/ρₙ`. -/
theorem s36l_dil_vanish (κ : LinfStar)
    (ρ : ℕ → ℝ) (hρ : ∀ n, 0 < ρ n ∧ ρ n < 1) :
    let κn : ℕ → LinfStar := fun n =>
      toLinf (fun z => if 1 / ρ n < ‖z‖ then (κ : ℂ → ℂ) ((ρ n : ℂ) * z) else 0)
    ∀ n, ∀ᵐ z ∂(volume.restrict unitDiscExterior), ‖z‖ < 1 / ρ n → (κn n : ℂ → ℂ) z = 0 := by
  intro κn n
  simp only [κn]
  unfold toLinf
  split_ifs with h
  · filter_upwards [MemLp.coeFn_toLp h] with z hz hzr
    rw [hz, if_neg (not_lt.mpr hzr.le)]
  · filter_upwards [Lp.coeFn_zero ℂ ∞ (volume.restrict unitDiscExterior)] with z hz _
    rw [hz]; rfl

/-- The dilated coefficients are admissible and stay in `T₀(1)`. -/
theorem s36l_dil_mem {κ : LinfStar} (hκ : κ ∈ LinfStarBall) (hκT : Phi ⟨κ, hκ⟩ ∈ T01)
    (ρ : ℕ → ℝ) (hρ : ∀ n, 0 < ρ n ∧ ρ n < 1) :
    let κn : ℕ → LinfStar := fun n =>
      toLinf (fun z => if 1 / ρ n < ‖z‖ then (κ : ℂ → ℂ) ((ρ n : ℂ) * z) else 0)
    ∀ n, ∃ h : κn n ∈ LinfStarBall, Phi ⟨κn n, h⟩ ∈ T01 := by
  intro κn n
  obtain ⟨hρ0, hρ1⟩ := hρ n
  -- the dilation is quasi-measure-preserving
  have hdet : LinearMap.det ((ρ n : ℝ) • (LinearMap.id : ℂ →ₗ[ℝ] ℂ)) ≠ 0 := by
    rw [LinearMap.det_smul, LinearMap.det_id, mul_one, Complex.finrank_real_complex]
    exact pow_ne_zero 2 hρ0.ne'
  have hq := MeasureTheory.Measure.LinearMap.quasiMeasurePreserving (μ := (volume : Measure ℂ)) _ hdet
  have hEm : MeasurableSet unitDiscExterior := (isOpen_lt continuous_const continuous_norm).measurableSet
  have hb := (ae_restrict_iff' hEm).mp (LinfStar_ae_norm_le κ)
  have hb' := hq.ae hb
  have hbound : ∀ᵐ z ∂(volume.restrict unitDiscExterior),
      ‖(if 1 / ρ n < ‖z‖ then (κ : ℂ → ℂ) ((ρ n : ℂ) * z) else 0)‖ ≤ ‖κ‖ := by
    refine ae_restrict_of_ae ?_
    filter_upwards [hb'] with z hz
    by_cases h : 1 / ρ n < ‖z‖
    · rw [if_pos h]
      have hm : ((ρ n : ℝ) • (LinearMap.id : ℂ →ₗ[ℝ] ℂ)) z = (ρ n : ℂ) * z := by
        simp [Complex.real_smul]
      rw [hm] at hz
      apply hz
      show 1 < ‖(ρ n : ℂ) * z‖
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hρ0.le]
      rw [one_div, inv_lt_iff_one_lt_mul₀ hρ0] at h
      linarith
    · rw [if_neg h, norm_zero]; exact norm_nonneg _
  have hn : ‖κn n‖ ≤ ‖κ‖ := norm_toLinf_le_of_ae_bound (norm_nonneg _) hbound
  have hmem : κn n ∈ LinfStarBall := mem_ball_zero_iff.mpr (hn.trans_lt (mem_ball_zero_iff.mp hκ))
  refine ⟨hmem, ?_⟩
  -- `T₀(1)` through the Bers image (Ch. 1, Cor. 3.2)
  have hR : 1 < 1 / ρ n := by rw [one_div]; exact (one_lt_inv₀ hρ0).mpr hρ1
  obtain ⟨R', hR', hfd, hfi, -⟩ := s36l_rf_fsans hmem hR (s36l_dil_vanish κ ρ hρ n)
  have hf' : ∀ z ∈ ball (0 : ℂ) R', deriv (fsans (κn n)) z ≠ 0 := fun z hz =>
    deriv_ne_zero_of_injOn isOpen_ball hfd hfi hz
  have hS := s36l_A2_of_ball hR' (s36l_schwarzian_holo isOpen_ball hfd hf')
  rw [_root_.TakhtajanTeo.cor_3_2]
  show AInf.toFun (bers (Phi ⟨κn n, hmem⟩)) ∈ A2fun unitDisc
  rw [bers_Phi, bersPhi]
  show AInf.toFun (toAInf unitDisc (schwarzianHol (fB (κn n)))) ∈ A2fun unitDisc
  obtain ⟨hFd, hFi⟩ := fB_holomorphic_injective hmem
  have heq := (schwarzianHol_AInf_spec hFd hFi).1
  rw [S2C.s2c_fsans_eq hmem] at hS
  refine ⟨hS.1.congr fun z hz => heq z hz, ?_⟩
  rw [show normA2 unitDisc (AInf.toFun (toAInf unitDisc (schwarzianHol (fB (κn n))))) =
      normA2 unitDisc (schwarzianHol (fB (κn n))) by
    unfold normA2
    congr 1
    refine setLIntegral_congr_fun isOpen_ball.measurableSet fun z hz => ?_
    rw [heq z hz]]
  exact hS.2

/-- The dilation `z ↦ r z` is quasi-measure-preserving: a.e. statements pull back along it. -/
theorem s36l_dil_ae {r : ℝ} (hr : 0 < r) {P : ℂ → Prop} (h : ∀ᵐ z, P z) : ∀ᵐ z, P ((r : ℂ) * z) := by
  have hdet : LinearMap.det ((r : ℝ) • (LinearMap.id : ℂ →ₗ[ℝ] ℂ)) ≠ 0 := by
    rw [LinearMap.det_smul, LinearMap.det_id, mul_one, Complex.finrank_real_complex]
    exact pow_ne_zero 2 hr.ne'
  have hq := MeasureTheory.Measure.LinearMap.quasiMeasurePreserving (μ := (volume : Measure ℂ)) _ hdet
  filter_upwards [hq.ae h] with z hz
  have hm : ((r : ℝ) • (LinearMap.id : ℂ →ₗ[ℝ] ℂ)) z = (r : ℂ) * z := by
    simp [Complex.real_smul]
  rw [hm] at hz
  exact hz

/-- **(M3)** The normalized solution of a dilated coefficient is the rescaled dilation of the normalized solution:
if `μ' = μ(r ·)` a.e. then `w^{μ'}(z) = w^μ(r z)/w^μ(r)`. -/
theorem s36l_V_ns {κ κ' : LinfStar} (hκ : κ ∈ LinfStarBall) (hκ' : κ' ∈ LinfStarBall) {r : ℝ} (hr : 0 < r)
    (he : ∀ᵐ z, extB κ' z = extB κ ((r : ℂ) * z)) :
    normalizedSolution (extB κ') =
      fun z => normalizedSolution (extB κ) ((r : ℂ) * z) / normalizedSolution (extB κ) (r : ℂ) := by
  have hk' : ‖κ'‖ < 1 := by simpa [LinfStarBall] using hκ'
  obtain ⟨⟨K, hK⟩, hsurj, hW0, -, hcd⟩ := AppA.acc_ns_spec hκ
  set W := normalizedSolution (extB κ) with hWdef
  have hr0 : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have hWr : W (r : ℂ) ≠ 0 := by
    intro h
    exact hr0 (hK.2.2.1.2.1 (mem_univ _) (mem_univ 0) (h.trans hW0.symm))
  have hD : IsKQC (fun u => (u - 0) / ((r : ℂ)⁻¹)) univ 1 :=
    isKQC_one_of_conformal isOpen_univ (nxE_affine_isConformalOnto (inv_ne_zero hr0))
  have hA : IsKQC (fun u => (u - 0) / W (r : ℂ)) univ 1 :=
    isKQC_one_of_conformal isOpen_univ (nxE_affine_isConformalOnto hWr)
  have h2 := thm7_1_comp (thm7_1_comp hD hK (subset_univ _)) hA (subset_univ _)
  have hfun : (fun z => W ((r : ℂ) * z) / W (r : ℂ)) =
      (fun u => (u - 0) / W (r : ℂ)) ∘ (W ∘ (fun u => (u - 0) / ((r : ℂ)⁻¹))) := by
    funext z
    simp only [Function.comp_apply, sub_zero, div_inv_eq_mul, mul_comm z]
  refine QCV.qcv_ns_eq (norm_nonneg κ') hk' (extB_isBeltramiCoeff κ') ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hfun]; exact ⟨_, h2⟩
  · refine eq_univ_of_forall fun w => ?_
    obtain ⟨z, -, hz⟩ : w * W (r : ℂ) ∈ W '' univ := by rw [hsurj]; exact mem_univ _
    refine ⟨z / (r : ℂ), mem_univ _, ?_⟩
    show W ((r : ℂ) * (z / (r : ℂ))) / W (r : ℂ) = w
    rw [mul_div_cancel₀ z hr0, hz, mul_div_cancel_right₀ w hWr]
  · show W ((r : ℂ) * 0) / W (r : ℂ) = 0
    rw [mul_zero, hW0, zero_div]
  · show W ((r : ℂ) * 1) / W (r : ℂ) = 1
    rw [mul_one, div_self hWr]
  · have hdiff := thm9_3_differentiable_ae hK
    rw [Measure.restrict_univ] at hdiff
    filter_upwards [he, s36l_dil_ae hr hdiff, s36l_dil_ae hr hcd] with z hz hd hc
    have hlin : DifferentiableAt ℂ (fun u : ℂ => (r : ℂ) * u) z := (differentiableAt_id.const_mul _)
    have hder : deriv (fun u : ℂ => (r : ℂ) * u) z = (r : ℂ) := by
      simpa using ((hasDerivAt_id z).const_mul (r : ℂ)).deriv
    rw [show (fun z => W ((r : ℂ) * z) / W (r : ℂ)) =
        fun ζ => ((W ∘ (fun u : ℂ => (r : ℂ) * u)) ζ - 0) / W (r : ℂ) by
      funext ζ; simp only [Function.comp_apply, sub_zero]]
    rw [nxE_complexDilatation_affine hWr, complexDilatation_comp_conformal_right hlin (by rw [hder]; exact hr0) hd,
      hder, hz, hc, Complex.conj_ofReal, div_self hr0, mul_one]

/-- Bound and essential boundedness of the dilated coefficient. -/
theorem s36l_dil_bound (κ : LinfStar) {r : ℝ} (hr : 0 < r) :
    ∀ᵐ z ∂(volume.restrict unitDiscExterior),
      ‖(if 1 / r < ‖z‖ then (κ : ℂ → ℂ) ((r : ℂ) * z) else 0)‖ ≤ ‖κ‖ := by
  have hEm : MeasurableSet unitDiscExterior := (isOpen_lt continuous_const continuous_norm).measurableSet
  have hb' := s36l_dil_ae hr ((ae_restrict_iff' hEm).mp (LinfStar_ae_norm_le κ))
  refine ae_restrict_of_ae ?_
  filter_upwards [hb'] with z hz
  by_cases h : 1 / r < ‖z‖
  · rw [if_pos h]
    apply hz
    show 1 < ‖(r : ℂ) * z‖
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hr.le]
    rw [one_div, inv_lt_iff_one_lt_mul₀ hr] at h
    linarith
  · rw [if_neg h, norm_zero]; exact norm_nonneg _

/-- The dilated coefficient does not increase the norm. -/
theorem s36l_dil_norm (κ : LinfStar) {r : ℝ} (hr : 0 < r) :
    ‖toLinf (fun z => if 1 / r < ‖z‖ then (κ : ℂ → ℂ) ((r : ℂ) * z) else 0)‖ ≤ ‖κ‖ :=
  norm_toLinf_le_of_ae_bound (norm_nonneg _) (s36l_dil_bound κ hr)

/-- The Model B coefficient of the dilated coefficient is the dilation of the Model B coefficient. -/
theorem s36l_dil_extB (κ : LinfStar) {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) :
    ∀ᵐ z, extB (toLinf (fun z => if 1 / r < ‖z‖ then (κ : ℂ → ℂ) ((r : ℂ) * z) else 0)) z =
      extB κ ((r : ℂ) * z) := by
  have hEm : MeasurableSet unitDiscExterior := (isOpen_lt continuous_const continuous_norm).measurableSet
  set u : ℂ → ℂ := fun z => if 1 / r < ‖z‖ then (κ : ℂ → ℂ) ((r : ℂ) * z) else 0 with hu
  have hsm : StronglyMeasurable u := by
    refine StronglyMeasurable.ite (measurableSet_lt measurable_const measurable_norm) ?_ stronglyMeasurable_const
    exact (Lp.stronglyMeasurable κ).comp_measurable (measurable_const.mul measurable_id)
  have hmem : MemLp u ∞ (volume.restrict unitDiscExterior) :=
    memLp_top_of_bound hsm.aestronglyMeasurable _ (s36l_dil_bound κ hr)
  have hae := (ae_restrict_iff' hEm).mp (bc_toLinf_ae hmem)
  filter_upwards [hae] with z hz
  have hnr : ‖(r : ℂ) * z‖ = r * ‖z‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hr.le]
  by_cases hzE : z ∈ unitDiscExterior
  · rw [extB, indicator_of_mem hzE, hz hzE, hu]
    dsimp only
    by_cases h : 1 / r < ‖z‖
    · rw [if_pos h, extB, indicator_of_mem]
      show 1 < ‖(r : ℂ) * z‖
      rw [hnr]
      rw [one_div, inv_lt_iff_one_lt_mul₀ hr] at h
      linarith
    · rw [if_neg h, extB, indicator_of_notMem]
      show ¬ 1 < ‖(r : ℂ) * z‖
      rw [hnr, not_lt]
      have h' := mul_le_mul_of_nonneg_left (not_lt.mp h) hr.le
      rw [mul_one_div_cancel hr.ne'] at h'
      exact h'
  · rw [extB, indicator_of_notMem hzE, extB, indicator_of_notMem]
    have hz1 : ‖z‖ ≤ 1 := not_lt.mp hzE
    show ¬ 1 < ‖(r : ℂ) * z‖
    rw [hnr, not_lt]
    nlinarith [norm_nonneg z]

/-- Quasiconformality bound of the Model B plane solution. -/
theorem s36l_qcB {μ : LinfStar} {k : ℝ} (hk : k < 1) (hμ : ‖μ‖ ≤ k) :
    IsKQCNormalizedPlane (normalizedSolution (extB μ)) ((1 + k) / (1 - k)) := by
  have hk' : ‖μ‖ < 1 := lt_of_le_of_lt hμ hk
  obtain ⟨f, hf, hfK, -⟩ := thm13_7_normalized_existence (norm_nonneg μ) hk' (extB_isBeltramiCoeff μ)
  rw [QCV.qcv_ns_eq (norm_nonneg μ) hk' (extB_isBeltramiCoeff μ) hf]
  have hK : (1 + ‖μ‖) / (1 - ‖μ‖) ≤ (1 + k) / (1 - k) := by
    have h1 : 0 < 1 - k := by linarith
    have h2 : 0 < 1 - ‖μ‖ := by linarith
    rw [div_le_div_iff₀ h2 h1]
    nlinarith [norm_nonneg μ]
  exact ⟨hfK.mono hK, hf.2.1, hf.2.2.1, hf.2.2.2.1⟩

/-- On `𝔻`, `𝖿 = α W/(1 + γ W)` with `W = w^{μ}`, `α = 1/W'(0)`, `γ = -1/W(p)` (`p` the pole of the normalization),
and the denominator does not vanish. -/
theorem s36l_fB_rep {μ : LinfStar} (hμ : μ ∈ LinfStarBall) {z : ℂ} (hz : z ∈ unitDisc) :
    -finPart (mobiusExt 0 1 1 0 (OnePoint.map (normalizedSolution (extB μ)) (Function.invFun (wAS μ) extInf))) *
        normalizedSolution (extB μ) z + 1 ≠ 0 ∧
      fB μ z = (1 / deriv (normalizedSolution (extB μ)) 0 * normalizedSolution (extB μ) z + 0) /
        (-finPart (mobiusExt 0 1 1 0 (OnePoint.map (normalizedSolution (extB μ)) (Function.invFun (wAS μ) extInf))) *
          normalizedSolution (extB μ) z + 1) := by
  obtain ⟨-, -, hrep⟩ := AppA.acc_wB_rep hμ
  obtain ⟨-, -, -, -, -, -, f, hf, -⟩ := (wB_spec hμ).1
  have h1 := hf z hz
  rw [hrep] at h1
  have hmap : OnePoint.map (normalizedSolution (extB μ)) (z : ExtPlane) =
      ((normalizedSolution (extB μ) z : ℂ) : ExtPlane) := rfl
  rw [hmap] at h1
  have hden : -finPart (mobiusExt 0 1 1 0 (OnePoint.map (normalizedSolution (extB μ))
      (Function.invFun (wAS μ) extInf))) * normalizedSolution (extB μ) z + 1 ≠ 0 := by
    intro h0
    rw [mobiusExt_coe_of_eq_zero h0] at h1
    exact OnePoint.infty_ne_coe _ h1
  refine ⟨hden, ?_⟩
  show finPart (wB μ z) = _
  rw [hrep, hmap, mobiusExt_coe hden]
  rfl

/-- The algebra of the renormalization constant. -/
theorem s36l_dil_alg {D V ρ g g' w F G : ℂ} (hD : D ≠ 0) (hV : V ≠ 0) (hρ : ρ ≠ 0) (h1 : -g * w + 1 ≠ 0)
    (h2 : -g' * (w / V) + 1 ≠ 0) (hF : F = (1 / D * w + 0) / (-g * w + 1))
    (hG : G = (1 / (D * ρ / V) * (w / V) + 0) / (-g' * (w / V) + 1)) :
    1 + ρ * (g - g' / V) * D * (F / ρ) ≠ 0 ∧ G = F / ρ / (1 + ρ * (g - g' / V) * D * (F / ρ)) := by
  generalize hA : -g * w + 1 = A at h1 hF
  generalize hB : -g' * (w / V) + 1 = B at h2 hG
  have key : 1 + ρ * (g - g' / V) * D * (F / ρ) = B / A := by
    rw [hF, eq_div_iff h1]
    field_simp
    rw [← hA, ← hB]
    field_simp
    ring
  refine ⟨by rw [key]; exact div_ne_zero h2 h1, ?_⟩
  rw [key, hG, hF]
  field_simp
  ring

/-- `q ↦ finPart (1/q)` is continuous at every `q ≠ 0` of `ℂ̄`. -/
theorem s36l_finInv_tendsto {q : ℕ → ExtPlane} {q0 : ExtPlane} (hq : Tendsto q atTop (𝓝 q0))
    (hq0 : q0 ≠ ((0 : ℂ) : ExtPlane)) :
    Tendsto (fun n => finPart (mobiusExt 0 1 1 0 (q n))) atTop (𝓝 (finPart (mobiusExt 0 1 1 0 q0))) := by
  obtain ⟨y0, hy0⟩ : ∃ y0 : ℂ, mobiusExt 0 1 1 0 q0 = (y0 : ExtPlane) := by
    induction q0 using OnePoint.rec with
    | infty => exact ⟨0 / 1, mobiusExt_infty_of_ne one_ne_zero⟩
    | coe u =>
      have hu : (1 : ℂ) * u + 0 ≠ 0 := by
        rw [one_mul, add_zero]
        rintro rfl
        exact hq0 rfl
      exact ⟨_, mobiusExt_coe hu⟩
  have hopen : IsOpen ({x : ℂ × ℂ × ℂ × ℂ | x.1 * x.2.2.2 - x.2.1 * x.2.2.1 ≠ 0} ×ˢ (univ : Set ExtPlane)) :=
    (isOpen_ne_fun (by fun_prop) continuous_const).prod isOpen_univ
  set c0 : (ℂ × ℂ × ℂ × ℂ) × ExtPlane := (((0 : ℂ), (1 : ℂ), (1 : ℂ), (0 : ℂ)), q0) with hc0
  have hc0m : c0 ∈ {x : ℂ × ℂ × ℂ × ℂ | x.1 * x.2.2.2 - x.2.1 * x.2.2.1 ≠ 0} ×ˢ (univ : Set ExtPlane) :=
    ⟨by norm_num, mem_univ _⟩
  have hcont := (AppA.acc_mob_cont c0 hc0m).continuousAt (hopen.mem_nhds hc0m)
  have h := hcont.tendsto.comp ((tendsto_const_nhds (x := (((0 : ℂ), (1 : ℂ), (1 : ℂ), (0 : ℂ))))).prodMk_nhds hq)
  have hfin : ContinuousAt finPart (y0 : ExtPlane) :=
    OnePoint.isOpenEmbedding_coe.continuousAt_iff.mp (continuousAt_id : ContinuousAt (fun x : ℂ => x) y0)
  have h' : Tendsto (fun n => mobiusExt 0 1 1 0 (q n)) atTop (𝓝 (y0 : ExtPlane)) := by
    rw [← hy0]
    exact h
  have h2 := hfin.tendsto.comp h'
  rw [hy0]
  exact h2

/-- Common data of the dilation approximants: norm bound, the explicit Model B plane solutions and their locally
uniform convergence, their derivatives at `0`, and continuous convergence of the inverses of Model A along every
subsequence. -/
theorem s36l_dil_base {κ : LinfStar} (hκ : κ ∈ LinfStarBall)
    (ρ : ℕ → ℝ) (hρ : ∀ n, 0 < ρ n ∧ ρ n < 1) (hρl : Tendsto ρ atTop (𝓝 1))
    (hae : ∀ᵐ z, Tendsto (fun n => extB κ ((ρ n : ℂ) * z)) atTop (𝓝 (extB κ z))) :
    let κn : ℕ → LinfStar := fun n =>
      toLinf (fun z => if 1 / ρ n < ‖z‖ then (κ : ℂ → ℂ) ((ρ n : ℂ) * z) else 0)
    (∀ n, ‖κn n‖ ≤ ‖κ‖ ∧ κn n ∈ LinfStarBall) ∧
      (∀ n, normalizedSolution (extB (κn n)) = fun z =>
        normalizedSolution (extB κ) ((ρ n : ℂ) * z) / normalizedSolution (extB κ) (ρ n : ℂ)) ∧
      TendstoLocallyUniformly (fun n => normalizedSolution (extB (κn n))) (normalizedSolution (extB κ)) atTop ∧
      (∀ n, deriv (normalizedSolution (extB (κn n))) 0 =
        deriv (normalizedSolution (extB κ)) 0 * (ρ n : ℂ) / normalizedSolution (extB κ) (ρ n : ℂ)) ∧
      Tendsto (fun n => ((ρ n : ℝ) : ℂ)) atTop (𝓝 1) ∧
      Tendsto (fun n => normalizedSolution (extB κ) (ρ n : ℂ)) atTop (𝓝 1) ∧
      (∀ n, normalizedSolution (extB κ) (ρ n : ℂ) ≠ 0) ∧
      ∀ ψ : ℕ → ℕ, StrictMono ψ → ∀ (y : ℕ → ExtPlane) (y0 : ExtPlane), Tendsto y atTop (𝓝 y0) →
        Tendsto (fun k => Function.invFun (wAS (κn (ψ k))) (y k)) atTop (𝓝 (Function.invFun (wAS κ) y0)) := by
  intro κn
  have hk : ‖κ‖ < 1 := by simpa [LinfStarBall] using hκ
  have hnorm : ∀ n, ‖κn n‖ ≤ ‖κ‖ := fun n => s36l_dil_norm κ (hρ n).1
  have hmem : ∀ n, κn n ∈ LinfStarBall := fun n => mem_ball_zero_iff.mpr ((hnorm n).trans_lt hk)
  have hext : ∀ n, ∀ᵐ z, extB (κn n) z = extB κ ((ρ n : ℂ) * z) := fun n =>
    s36l_dil_extB κ (hρ n).1 (hρ n).2.le
  have haeN : ∀ᵐ z, Tendsto (fun n => extB (κn n) z) atTop (𝓝 (extB κ z)) := by
    filter_upwards [ae_all_iff.2 hext, hae] with z h1 h2
    exact h2.congr fun n => (h1 n).symm
  have hV : ∀ n, normalizedSolution (extB (κn n)) = fun z =>
      normalizedSolution (extB κ) ((ρ n : ℂ) * z) / normalizedSolution (extB κ) (ρ n : ℂ) := fun n =>
    s36l_V_ns hκ (hmem n) (hρ n).1 (hext n)
  have hqc0 := s36l_qcB (μ := κ) hk le_rfl
  have hWc : Continuous (normalizedSolution (extB κ)) := continuousOn_univ.1 hqc0.1.2.2.1.1
  have hW1 : normalizedSolution (extB κ) 1 = 1 := hqc0.2.2.2
  have hρc : Tendsto (fun n => ((ρ n : ℝ) : ℂ)) atTop (𝓝 1) := by
    have h := (Complex.continuous_ofReal.tendsto 1).comp hρl
    rw [Complex.ofReal_one] at h
    exact h
  have hWρ : Tendsto (fun n => normalizedSolution (extB κ) (ρ n : ℂ)) atTop (𝓝 1) := by
    have h := (hWc.tendsto 1).comp hρc
    rw [hW1] at h
    exact h
  have hWρne : ∀ n, normalizedSolution (extB κ) (ρ n : ℂ) ≠ 0 := fun n h => by
    have h1 := (s36l_qcB hk (hnorm n)).2.2.2
    rw [hV n] at h1
    simp only [mul_one, h, div_zero] at h1
    exact zero_ne_one h1
  have hL : TendstoLocallyUniformly (fun n => normalizedSolution (extB (κn n))) (normalizedSolution (extB κ))
      atTop := by
    rw [← tendstoLocallyUniformlyOn_univ]
    refine s36a_luc_of_contconv isOpen_univ hWc.continuousOn (fun ψ hψ w w0 _ _ hw => ?_)
    have hρψ := hρc.comp hψ.tendsto_atTop
    have h1 : Tendsto (fun k => (ρ (ψ k) : ℂ) * w k) atTop (𝓝 w0) := by
      have h := hρψ.mul hw
      rw [one_mul] at h
      exact h
    have h2 := ((hWc.tendsto w0).comp h1).div (hWρ.comp hψ.tendsto_atTop) one_ne_zero
    rw [div_one] at h2
    refine h2.congr fun k => ?_
    rw [hV (ψ k)]
    rfl
  have hDne : deriv (normalizedSolution (extB κ)) 0 ≠ 0 := (AppA.acc_wB_rep hκ).1
  have hWd : DifferentiableAt ℂ (normalizedSolution (extB κ)) 0 := differentiableAt_of_deriv_ne_zero hDne
  have hderiv : ∀ n, deriv (normalizedSolution (extB (κn n))) 0 =
      deriv (normalizedSolution (extB κ)) 0 * (ρ n : ℂ) / normalizedSolution (extB κ) (ρ n : ℂ) := by
    intro n
    rw [hV n]
    have h0 : HasDerivAt (normalizedSolution (extB κ)) (deriv (normalizedSolution (extB κ)) 0)
        ((ρ n : ℂ) * 0) := by
      rw [mul_zero]; exact hWd.hasDerivAt
    have h1 := (h0.comp (0 : ℂ) ((hasDerivAt_id (0 : ℂ)).const_mul (ρ n : ℂ))).div_const
      (normalizedSolution (extB κ) (ρ n : ℂ))
    rw [mul_one] at h1
    exact h1.deriv
  refine ⟨fun n => ⟨hnorm n, hmem n⟩, hV, hL, hderiv, hρc, hWρ, hWρne, fun ψ hψ y y0 hy => ?_⟩
  refine s36a_inv_tendsto (fun n => wAS_bijective _) (wAS_bijective κ) (fun φ hφ x x0 hx => ?_) hy
  have haeψ : ∀ᵐ z, Tendsto (fun j => extB (κn (ψ (φ j))) z) atTop (𝓝 (extB κ z)) := by
    filter_upwards [haeN] with z hz
    exact hz.comp (hψ.comp hφ).tendsto_atTop
  exact s36a_wAS_tendsto (μs := fun j => κn (ψ (φ j))) hk (fun j => hnorm _) le_rfl haeψ hx

/-- Locally uniform convergence passes to subsequences. -/
theorem s36l_tlu_subseq {F : ℕ → ℂ → ℂ} {f : ℂ → ℂ} (hL : TendstoLocallyUniformly F f atTop) {ψ : ℕ → ℕ}
    (hψ : StrictMono ψ) : TendstoLocallyUniformly (fun k => F (ψ k)) f atTop := by
  intro u hu x
  obtain ⟨t, ht, h⟩ := hL u hu x
  exact ⟨t, ht, hψ.tendsto_atTop.eventually h⟩

/-- The Model B map is finite at `w_μ⁻¹(w)` for every finite `w`. -/
theorem s36l_wB_fin {μ : LinfStar} (hμ : μ ∈ LinfStarBall) (w : ℂ) :
    ((finPart (wB μ (Function.invFun (wAS μ) (w : ExtPlane))) : ℂ) : ExtPlane) =
      wB μ (Function.invFun (wAS μ) (w : ExtPlane)) := by
  have hne : wB μ (Function.invFun (wAS μ) (w : ExtPlane)) ≠ extInf := by
    intro h
    have hp := (fB_normalization μ).2.2 ⟨wB μ, (wB_spec hμ).1⟩
    have he := (wB_bijective μ).1 (h.trans hp.symm)
    have h1 := Function.rightInverse_invFun (wAS_bijective μ).2 (w : ExtPlane)
    have h2 := Function.rightInverse_invFun (wAS_bijective μ).2 extInf
    rw [he, h2] at h1
    exact OnePoint.coe_ne_infty w h1.symm
  obtain ⟨a, ha⟩ := OnePoint.ne_infty_iff_exists.mp hne
  rw [← ha]
  rfl

/-- On `𝔻*`, `𝗀 = w^μ ∘ (w_μ)⁻¹` at finite points. -/
theorem s36l_gsans_fin {μ : LinfStar} (hμ : μ ∈ LinfStarBall) {w : ℂ} (hw : w ∈ unitDiscExterior) :
    gsans μ w = finPart (wB μ (Function.invFun (wAS μ) (w : ExtPlane))) := by
  rw [← gMu_sphere_factorization hμ hw, S2C.s2c_gsans_eq hμ]
  rfl

/-- Continuity of the extended map `w ↦ w^μ((w_μ)⁻¹(w))` at finite points. -/
theorem s36l_G_cont {μ : LinfStar} (hμ : μ ∈ LinfStarBall) :
    Continuous (fun w : ℂ => finPart (wB μ (Function.invFun (wAS μ) (w : ExtPlane)))) := by
  refine continuous_iff_continuousAt.mpr fun w0 => ?_
  have hfin : ContinuousAt finPart (wB μ (Function.invFun (wAS μ) (w0 : ExtPlane))) := by
    rw [← s36l_wB_fin hμ w0]
    exact OnePoint.isOpenEmbedding_coe.continuousAt_iff.mp (continuousAt_id : ContinuousAt (fun x : ℂ => x) _)
  have h1 : ContinuousAt (fun w : ℂ => wB μ (Function.invFun (wAS μ) (w : ExtPlane))) w0 :=
    ((wB_continuous hμ).comp ((wAS_invFun_continuous hμ).comp OnePoint.continuous_coe)).continuousAt
  exact ContinuousAt.comp (g := finPart)
    (f := fun w : ℂ => wB μ (Function.invFun (wAS μ) (w : ExtPlane))) hfin h1

/-- Continuous convergence on `ℂ` of the extended maps `w ↦ w^{κₙ}((w_{κₙ})⁻¹(w))` (along every subsequence). -/
theorem s36l_dil_Gcc {κ : LinfStar} (hκ : κ ∈ LinfStarBall)
    (ρ : ℕ → ℝ) (hρ : ∀ n, 0 < ρ n ∧ ρ n < 1) (hρl : Tendsto ρ atTop (𝓝 1))
    (hae : ∀ᵐ z, Tendsto (fun n => extB κ ((ρ n : ℂ) * z)) atTop (𝓝 (extB κ z))) :
    let κn : ℕ → LinfStar := fun n =>
      toLinf (fun z => if 1 / ρ n < ‖z‖ then (κ : ℂ → ℂ) ((ρ n : ℂ) * z) else 0)
    ∀ ψ : ℕ → ℕ, StrictMono ψ → ∀ (w : ℕ → ℂ) (w0 : ℂ), Tendsto w atTop (𝓝 w0) →
      Tendsto (fun k => finPart (wB (κn (ψ k)) (Function.invFun (wAS (κn (ψ k))) (w k : ExtPlane)))) atTop
        (𝓝 (finPart (wB κ (Function.invFun (wAS κ) (w0 : ExtPlane))))) := by
  intro κn ψ hψ w w0 hwl
  obtain ⟨hnm, -, hL, hderiv, hρc, hWρ, -, hpinv⟩ := s36l_dil_base hκ ρ hρ hρl hae
  have hk : ‖κ‖ < 1 := by simpa [LinfStarBall] using hκ
  have hDne : deriv (normalizedSolution (extB κ)) 0 ≠ 0 := (AppA.acc_wB_rep hκ).1
  have hLψ := s36l_tlu_subseq hL hψ
  have hqcψ : ∀ k, IsKQCNormalizedPlane (normalizedSolution (extB (κn (ψ k)))) ((1 + ‖κ‖) / (1 - ‖κ‖)) :=
    fun k => s36l_qcB hk (hnm (ψ k)).1
  have hqc0 := s36l_qcB (μ := κ) hk le_rfl
  have hpψ := hpinv ψ hψ (fun _ => extInf) extInf tendsto_const_nhds
  have hwl' : Tendsto (fun k => ((w k : ℂ) : ExtPlane)) atTop (𝓝 ((w0 : ℂ) : ExtPlane)) :=
    (OnePoint.continuous_coe.tendsto w0).comp hwl
  have hxψ := hpinv ψ hψ (fun k => ((w k : ℂ) : ExtPlane)) (w0 : ExtPlane) hwl'
  have hmap1 := s36a_map_tendsto hqcψ hqc0 hLψ hpψ
  have hmap2 := s36a_map_tendsto hqcψ hqc0 hLψ hxψ
  have hg := s36l_finInv_tendsto hmap1 (AppA.acc_wB_rep hκ).2.1
  -- the leading coefficients `1/Wₙ'(0)`
  have hD : Tendsto (fun k => deriv (normalizedSolution (extB (κn (ψ k)))) 0) atTop
      (𝓝 (deriv (normalizedSolution (extB κ)) 0)) := by
    have h := ((tendsto_const_nhds (x := deriv (normalizedSolution (extB κ)) 0)).mul
      (hρc.comp hψ.tendsto_atTop)).div (hWρ.comp hψ.tendsto_atTop) one_ne_zero
    rw [mul_one, div_one] at h
    refine h.congr fun k => ?_
    rw [hderiv (ψ k)]
    rfl
  have hα := (tendsto_const_nhds (x := (1 : ℂ))).div hD hDne
  -- joint continuity of the Möbius action
  have hcoef : Tendsto (fun k => (1 / deriv (normalizedSolution (extB (κn (ψ k)))) 0, (0 : ℂ),
      -finPart (mobiusExt 0 1 1 0 (OnePoint.map (normalizedSolution (extB (κn (ψ k))))
        (Function.invFun (wAS (κn (ψ k))) extInf))), (1 : ℂ))) atTop
      (𝓝 (1 / deriv (normalizedSolution (extB κ)) 0, (0 : ℂ),
        -finPart (mobiusExt 0 1 1 0 (OnePoint.map (normalizedSolution (extB κ))
          (Function.invFun (wAS κ) extInf))), (1 : ℂ))) :=
    hα.prodMk_nhds (tendsto_const_nhds.prodMk_nhds (hg.neg.prodMk_nhds tendsto_const_nhds))
  have hopen : IsOpen ({x : ℂ × ℂ × ℂ × ℂ | x.1 * x.2.2.2 - x.2.1 * x.2.2.1 ≠ 0} ×ˢ (univ : Set ExtPlane)) :=
    (isOpen_ne_fun (by fun_prop) continuous_const).prod isOpen_univ
  set q0 : (ℂ × ℂ × ℂ × ℂ) × ExtPlane := ((1 / deriv (normalizedSolution (extB κ)) 0, (0 : ℂ),
      -finPart (mobiusExt 0 1 1 0 (OnePoint.map (normalizedSolution (extB κ))
        (Function.invFun (wAS κ) extInf))), (1 : ℂ)),
      OnePoint.map (normalizedSolution (extB κ)) (Function.invFun (wAS κ) (w0 : ExtPlane))) with hq0
  have hq0m : q0 ∈ {x : ℂ × ℂ × ℂ × ℂ | x.1 * x.2.2.2 - x.2.1 * x.2.2.1 ≠ 0} ×ˢ (univ : Set ExtPlane) := by
    refine ⟨?_, mem_univ _⟩
    show 1 / deriv (normalizedSolution (extB κ)) 0 * 1 - 0 * _ ≠ 0
    rw [mul_one, zero_mul, sub_zero]
    exact one_div_ne_zero hDne
  have hcont := (AppA.acc_mob_cont q0 hq0m).continuousAt (hopen.mem_nhds hq0m)
  have h := hcont.tendsto.comp (hcoef.prodMk_nhds hmap2)
  -- identify the limit and the terms
  have hlim : mobiusExt q0.1.1 q0.1.2.1 q0.1.2.2.1 q0.1.2.2.2 q0.2 =
      wB κ (Function.invFun (wAS κ) (w0 : ExtPlane)) := by
    rw [(AppA.acc_wB_rep hκ).2.2]
  have h' : Tendsto (fun k => wB (κn (ψ k)) (Function.invFun (wAS (κn (ψ k))) (w k : ExtPlane))) atTop
      (𝓝 (wB κ (Function.invFun (wAS κ) (w0 : ExtPlane)))) := by
    rw [← hlim]
    refine h.congr fun k => ?_
    rw [(AppA.acc_wB_rep (hnm (ψ k)).2).2.2]
    rfl
  have hfin : ContinuousAt finPart (wB κ (Function.invFun (wAS κ) (w0 : ExtPlane))) := by
    rw [← s36l_wB_fin hκ w0]
    exact OnePoint.isOpenEmbedding_coe.continuousAt_iff.mp (continuousAt_id : ContinuousAt (fun x : ℂ => x) _)
  have h2 := hfin.tendsto.comp h'
  exact h2

/-- Area formula on an open set: `∬_U |f'|² = |f(U)|` for `f` univalent on `U`. -/
theorem s36l_area_open {f : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U) (hfd : DifferentiableOn ℂ f U)
    (hfi : InjOn f U) : (∫⁻ u in U, (‖deriv f u‖₊ : ℝ≥0∞) ^ 2) = volume (f '' U) := by
  have hder : ∀ x ∈ U, HasFDerivWithinAt f
      ((ContinuousLinearMap.toSpanSingleton ℂ (deriv f x)).restrictScalars ℝ) U x := fun x hx =>
    (((hfd x hx).differentiableAt (hU.mem_nhds hx)).hasDerivAt.hasFDerivAt.restrictScalars ℝ).hasFDerivWithinAt
  rw [← lintegral_abs_det_fderiv_eq_addHaar_image (s := U) volume hU.measurableSet hder hfi]
  refine setLIntegral_congr_fun hU.measurableSet fun x _ => ?_
  rw [LiZhongQC.det_restrictScalars_toSpanSingleton, abs_of_nonneg (by positivity),
    ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
  rfl

/-- The image of `S¹` under the extended map lies off `𝖿(𝔻) ∪ 𝗀(𝔻*)`, hence is null (Remark 2.2). -/
theorem s36l_G_circle_null {μ : LinfStar} (hμ : μ ∈ LinfStarBall) :
    volume ((fun w : ℂ => finPart (wB μ (Function.invFun (wAS μ) (w : ExtPlane)))) '' unitCircle) = 0 := by
  refine measure_mono_null ?_ (remark_2_2 hμ).2.1
  rintro _ ⟨ζ, hζ, rfl⟩
  obtain ⟨-, -, hC⟩ := wA_mapsTo hμ
  have hζC : (ζ : ExtPlane) ∈ wAS μ '' toExt unitCircle := by
    rw [hC]; exact ⟨ζ, hζ, rfl⟩
  obtain ⟨y, ⟨u, hu, rfl⟩, hyu⟩ := hζC
  have hinv : Function.invFun (wAS μ) (ζ : ExtPlane) = (u : ExtPlane) := by
    rw [← hyu]
    exact Function.leftInverse_invFun (wAS_bijective μ).1 _
  have hfinu := s36l_wB_fin hμ ζ
  rw [hinv] at hfinu
  simp only [hinv]
  rintro (⟨z, hz, hzeq⟩ | ⟨w', hw', hweq⟩)
  · have h1 : wB μ (z : ExtPlane) = wB μ (u : ExtPlane) := by
      rw [wB_disc_eq_fB hμ hz, ← hfinu, ← S2C.s2c_fsans_eq hμ, hzeq]
    have h2 := (wB_bijective μ).1 h1
    have h3 : z = u := OnePoint.coe_injective h2
    have hz1 : ‖z‖ < 1 := mem_ball_zero_iff.mp hz
    have hu1 : ‖u‖ = 1 := hu
    rw [h3] at hz1
    linarith
  · have h1 : wB μ (Function.invFun (wAS μ) (w' : ExtPlane)) = wB μ (u : ExtPlane) := by
      rw [← s36l_wB_fin hμ w', ← s36l_gsans_fin hμ hw', hweq, hfinu]
    have h2 := (wB_bijective μ).1 h1
    have h3 : (w' : ExtPlane) = (ζ : ExtPlane) := by
      rw [← Function.rightInverse_invFun (wAS_bijective μ).2 (w' : ExtPlane), h2, hyu]
    have h4 : w' = ζ := OnePoint.coe_injective h3
    have hw1 : 1 < ‖w'‖ := hw'
    have hζ1 : ‖ζ‖ = 1 := hζ
    rw [h4] at hw1
    linarith

/-- `fsans κₙ = M_{cₙ} ∘ (f(ρₙ ·)/ρₙ)` with `M_c(ζ) = ζ/(1 + cζ)` and `cₙ → 0` (uniqueness of the normalized
solution; `cₙ = -ρₙ/𝖿(ρₙ pₙ)` for the pole `pₙ` of the normalization). -/
theorem s36l_dil_fsans {κ : LinfStar} (hκ : κ ∈ LinfStarBall)
    (ρ : ℕ → ℝ) (hρ : ∀ n, 0 < ρ n ∧ ρ n < 1) (hρl : Tendsto ρ atTop (𝓝 1))
    (hae : ∀ᵐ z, Tendsto (fun n => extB κ ((ρ n : ℂ) * z)) atTop (𝓝 (extB κ z))) :
    let κn : ℕ → LinfStar := fun n =>
      toLinf (fun z => if 1 / ρ n < ‖z‖ then (κ : ℂ → ℂ) ((ρ n : ℂ) * z) else 0)
    ∃ c : ℕ → ℂ, Tendsto c atTop (𝓝 0) ∧ ∀ n, ∀ z ∈ unitDisc,
      1 + c n * (fsans κ ((ρ n : ℂ) * z) / (ρ n : ℂ)) ≠ 0 ∧
        fsans (κn n) z = (fsans κ ((ρ n : ℂ) * z) / (ρ n : ℂ)) / (1 + c n * (fsans κ ((ρ n : ℂ) * z) / (ρ n : ℂ))) := by
  intro κn
  obtain ⟨hnm, hV, hL, hderiv, hρc, hWρ, hWρne, hpinv⟩ := s36l_dil_base hκ ρ hρ hρl hae
  have hk : ‖κ‖ < 1 := by simpa [LinfStarBall] using hκ
  have hp := hpinv id strictMono_id (fun _ => extInf) extInf tendsto_const_nhds
  have hmapc := s36a_map_tendsto (fun n => s36l_qcB hk (hnm n).1) (s36l_qcB (μ := κ) hk le_rfl) hL hp
  have hg := s36l_finInv_tendsto hmapc (AppA.acc_wB_rep hκ).2.1
  have hDne : deriv (normalizedSolution (extB κ)) 0 ≠ 0 := (AppA.acc_wB_rep hκ).1
  set g : ℂ := finPart (mobiusExt 0 1 1 0 (OnePoint.map (normalizedSolution (extB κ))
    (Function.invFun (wAS κ) extInf))) with hgdef
  set gn : ℕ → ℂ := fun n => finPart (mobiusExt 0 1 1 0 (OnePoint.map (normalizedSolution (extB (κn n)))
    (Function.invFun (wAS (κn n)) extInf))) with hgndef
  refine ⟨fun n => (ρ n : ℂ) * (g - gn n / normalizedSolution (extB κ) (ρ n : ℂ)) *
    deriv (normalizedSolution (extB κ)) 0, ?_, fun n z hz => ?_⟩
  · have h := (hρc.mul ((tendsto_const_nhds (x := g)).sub (hg.div hWρ one_ne_zero))).mul_const
      (deriv (normalizedSolution (extB κ)) 0)
    rw [div_one, sub_self, mul_zero, zero_mul] at h
    exact h
  · have hρz : (ρ n : ℂ) * z ∈ unitDisc := by
      have hz1 : ‖z‖ < 1 := mem_ball_zero_iff.mp hz
      refine mem_ball_zero_iff.mpr ?_
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hρ n).1.le]
      nlinarith [(hρ n).1, (hρ n).2, norm_nonneg z]
    obtain ⟨h1, hF⟩ := s36l_fB_rep hκ hρz
    obtain ⟨h2, hG⟩ := s36l_fB_rep (hnm n).2 hz
    rw [congrFun (hV n) z] at h2 hG
    rw [hderiv n] at hG
    rw [S2C.s2c_fsans_eq hκ, S2C.s2c_fsans_eq (hnm n).2]
    have hρ0 : (ρ n : ℂ) ≠ 0 := by exact_mod_cast (hρ n).1.ne'
    have h3 := s36l_dil_alg hDne (hWρne n) hρ0 h1 h2 hF hG
    beta_reduce
    exact h3

/-- The `𝗀`-side converges locally uniformly on `𝔻*` (continuous dependence of normalized solutions on the Beltrami
coefficient under a.e. convergence). -/
theorem s36l_dil_gconv {κ : LinfStar} (hκ : κ ∈ LinfStarBall)
    (ρ : ℕ → ℝ) (hρ : ∀ n, 0 < ρ n ∧ ρ n < 1) (hρl : Tendsto ρ atTop (𝓝 1))
    (hae : ∀ᵐ z, Tendsto (fun n => extB κ ((ρ n : ℂ) * z)) atTop (𝓝 (extB κ z))) :
    let κn : ℕ → LinfStar := fun n =>
      toLinf (fun z => if 1 / ρ n < ‖z‖ then (κ : ℂ → ℂ) ((ρ n : ℂ) * z) else 0)
    TendstoLocallyUniformlyOn (fun n => gsans (κn n)) (gsans κ) atTop unitDiscExterior := by
  intro κn
  obtain ⟨hnm, -⟩ := s36l_dil_base hκ ρ hρ hρl hae
  have hcc := s36l_dil_Gcc hκ ρ hρ hρl hae
  have hEo : IsOpen unitDiscExterior := isOpen_lt continuous_const continuous_norm
  have hgc : ContinuousOn (gsans κ) unitDiscExterior := (s2c_facts hκ).2.2.2.2.1.continuousOn
  refine s36a_luc_of_contconv hEo hgc (fun ψ hψ w w0 hw0 hw hwl => ?_)
  have h := hcc ψ hψ w w0 hwl
  rw [s36l_gsans_fin hκ hw0]
  refine h.congr fun k => ?_
  rw [s36l_gsans_fin (hnm (ψ k)).2 (hw k)]

/-- Uniform smallness of the area of `𝗀ₙ(1 < |w| < 1 + δ)` (uniform convergence of the q.c. extensions on compacts
of `ℂ`; the quasicircle `𝗀(S¹)` has measure zero). -/
theorem s36l_dil_gtail {κ : LinfStar} (hκ : κ ∈ LinfStarBall)
    (ρ : ℕ → ℝ) (hρ : ∀ n, 0 < ρ n ∧ ρ n < 1) (hρl : Tendsto ρ atTop (𝓝 1))
    (hae : ∀ᵐ z, Tendsto (fun n => extB κ ((ρ n : ℂ) * z)) atTop (𝓝 (extB κ z))) :
    let κn : ℕ → LinfStar := fun n =>
      toLinf (fun z => if 1 / ρ n < ‖z‖ then (κ : ℂ → ℂ) ((ρ n : ℂ) * z) else 0)
    ∀ ε > (0 : ℝ≥0∞), ∃ δ > (0 : ℝ), ∀ᶠ n in atTop,
      (∫⁻ w in {w : ℂ | 1 < ‖w‖ ∧ ‖w‖ < 1 + δ}, (‖deriv (gsans (κn n)) w‖₊ : ℝ≥0∞) ^ 2) ≤ ε := by
  intro κn ε hε
  obtain ⟨hnm, -⟩ := s36l_dil_base hκ ρ hρ hρl hae
  have hcc := s36l_dil_Gcc hκ ρ hρ hρl hae
  set G : ℂ → ℂ := fun w => finPart (wB κ (Function.invFun (wAS κ) (w : ExtPlane))) with hGdef
  set Gn : ℕ → ℂ → ℂ := fun n w => finPart (wB (κn n) (Function.invFun (wAS (κn n)) (w : ExtPlane)))
    with hGndef
  have hGc : Continuous G := s36l_G_cont hκ
  -- locally uniform convergence on `ℂ`
  have hL : TendstoLocallyUniformly Gn G atTop := by
    rw [← tendstoLocallyUniformlyOn_univ]
    exact s36a_luc_of_contconv isOpen_univ hGc.continuousOn
      (fun ψ hψ w w0 _ _ hw => hcc ψ hψ w w0 hw)
  set K : Set ℂ := closedBall (0 : ℂ) 2 with hK
  have hKc : IsCompact K := isCompact_closedBall _ _
  have hU := (tendstoLocallyUniformly_iff_forall_isCompact.1 hL) K hKc
  -- the image of `S¹` and its thickenings
  set C : Set ℂ := G '' unitCircle with hC
  have hCc : IsCompact C := by
    have hS : IsCompact unitCircle := by
      have h : unitCircle = sphere (0 : ℂ) 1 := by
        ext z; simp [unitCircle]
      rw [h]; exact isCompact_sphere _ _
    exact hS.image hGc
  have hC0 : volume C = 0 := s36l_G_circle_null hκ
  have htend := tendsto_measure_cthickening_of_isCompact (μ := (volume : Measure ℂ)) hCc
  rw [hC0] at htend
  obtain ⟨r, hr0, hr⟩ : ∃ r : ℝ, 0 < r ∧ volume (cthickening r C) ≤ ε := by
    obtain ⟨t, ht, ht1⟩ := Metric.eventually_nhds_iff.mp
      (htend.eventually (Iic_mem_nhds hε))
    refine ⟨t / 2, half_pos ht, ht1 ?_⟩
    rw [Real.dist_eq, sub_zero, abs_of_pos (half_pos ht)]
    exact half_lt_self ht
  -- uniform continuity of `G` on `K`
  obtain ⟨δ, hδ0, hδ⟩ := Metric.uniformContinuousOn_iff.mp
    (hKc.uniformContinuousOn_of_continuous hGc.continuousOn) (r / 2) (half_pos hr0)
  refine ⟨min δ 1, lt_min hδ0 one_pos, ?_⟩
  filter_upwards [(Metric.tendstoUniformlyOn_iff.mp hU) (r / 2) (half_pos hr0)] with n hn
  set A : Set ℂ := {w : ℂ | 1 < ‖w‖ ∧ ‖w‖ < 1 + min δ 1} with hA
  have hAo : IsOpen A :=
    (isOpen_lt continuous_const continuous_norm).inter (isOpen_lt continuous_norm continuous_const)
  have hAE : A ⊆ unitDiscExterior := fun w hw => hw.1
  obtain ⟨hgd, hgi⟩ := (s2c_facts (hnm n).2).2.2.2.2
  rw [s36l_area_open hAo (hgd.mono hAE) (hgi.1.mono hAE)]
  refine le_trans (measure_mono ?_) hr
  rintro _ ⟨w, hw, rfl⟩
  have hw1 : 1 < ‖w‖ := hw.1
  have hw2 : ‖w‖ < 1 + min δ 1 := hw.2
  have hwK : w ∈ K := by
    rw [hK, mem_closedBall, dist_zero_right]
    linarith [min_le_right δ 1]
  have hn0 : (‖w‖ : ℂ) ≠ 0 := by
    exact_mod_cast (show ‖w‖ ≠ 0 by linarith)
  set ζ : ℂ := w / (‖w‖ : ℂ) with hζ
  have hζn : ‖ζ‖ = 1 := by
    rw [hζ, norm_div, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _), div_self (by linarith)]
  have hζK : ζ ∈ K := by
    rw [hK, mem_closedBall, dist_zero_right, hζn]; norm_num
  have hdist : dist w ζ < δ := by
    have h : w - ζ = ζ * ((‖w‖ : ℂ) - 1) := by
      rw [hζ]; field_simp
    rw [dist_eq_norm, h, norm_mul, hζn, one_mul, ← Complex.ofReal_one, ← Complex.ofReal_sub,
      Complex.norm_real, Real.norm_of_nonneg (by linarith)]
    linarith [min_le_left δ 1]
  have h1 := hδ w hwK ζ hζK hdist
  have h2 := hn w hwK
  rw [s36l_gsans_fin (hnm n).2 (hAE hw)]
  refine Metric.mem_cthickening_of_dist_le _ (G ζ) r C ⟨ζ, hζn, rfl⟩ ?_
  have h3 := dist_triangle (Gn n w) (G w) (G ζ)
  rw [dist_comm] at h2
  show dist (Gn n w) (G ζ) ≤ r
  linarith

/-- Uniform energy bound on the `𝗀`-side: `sup ∬_{𝔻*} |𝒜(𝗀ₙ)|² < ∞` (from Cor. A.4 (ii)⇒(i) and Cor. A.6: `κₙ → κ`
in `T₀(1)` since `𝒜(𝖿ₙ) → 𝒜(𝖿)` in `A₂¹(𝔻)`). -/
theorem s36l_dil_energy {κ : LinfStar} (hκ : κ ∈ LinfStarBall) (hκT : Phi ⟨κ, hκ⟩ ∈ T01)
    (ρ : ℕ → ℝ) (hρ : ∀ n, 0 < ρ n ∧ ρ n < 1) (hρl : Tendsto ρ atTop (𝓝 1))
    (hae : ∀ᵐ z, Tendsto (fun n => extB κ ((ρ n : ℂ) * z)) atTop (𝓝 (extB κ z))) :
    let κn : ℕ → LinfStar := fun n =>
      toLinf (fun z => if 1 / ρ n < ‖z‖ then (κ : ℂ → ℂ) ((ρ n : ℂ) * z) else 0)
    ∃ M : ℝ≥0∞, M < ∞ ∧ ∀ n,
      (∫⁻ w in unitDiscExterior, (‖preSchwarzian (gsans (κn n)) w‖₊ : ℝ≥0∞) ^ 2) ≤ M := by
  intro κn
  obtain ⟨c, -, hf⟩ := s36l_dil_fsans hκ ρ hρ hρl hae
  have hT := s36l_dil_mem hκ hκT ρ hρ
  have hgc := s36l_dil_gconv hκ ρ hρ hρl hae
  dsimp only at hT hf hgc
  have hmem : ∀ m, κn m ∈ LinfStarBall := fun m => (hT m).1
  have hEo : IsOpen unitDiscExterior := isOpen_lt continuous_const continuous_norm
  have hEm : MeasurableSet unitDiscExterior := hEo.measurableSet
  obtain ⟨hfd, hfi, -, -, hgd, hgi, hgne, hgd', -, hfd'⟩ := s2c_facts hκ
  obtain ⟨hSf, hSg⟩ := s36l_S_mem hκ hκT
  have hgnd : ∀ n, DifferentiableOn ℂ (gsans (κn n)) unitDiscExterior := fun n => (s2c_facts (hmem n)).2.2.2.2.1
  -- the classes
  set p : ℕ → T1 := fun n => Phi ⟨κn n, hmem n⟩ with hpdef
  have hpT : ∀ n, p n ∈ T01 := fun n => (hT n).2
  have hcl : ∀ n, EqOn (fsans ((Quotient.out (p n) : LinfStarBall) : LinfStar)) (fsans (κn n)) unitDisc ∧
      EqOn (gsans ((Quotient.out (p n) : LinfStarBall) : LinfStar)) (gsans (κn n)) unitDiscExterior :=
    fun n => s36l_class_out (hmem n)
  have hcl0 := s36l_class_out hκ
  -- (E1) `𝒮(𝖿ₙ) = ρₙ² 𝒮(𝖿)(ρₙ ·) → 𝒮(𝖿)` in `A₂(𝔻)`
  have hSfd : DifferentiableOn ℂ (schwarzianHol (fsans κ)) unitDisc :=
    s36l_schwarzian_holo isOpen_ball hfd hfd'
  have hSn : ∀ n, ∀ z ∈ unitDisc, schwarzianHol (fsans (κn n)) z =
      (ρ n : ℂ) ^ 2 * schwarzianHol (fsans κ) ((ρ n : ℂ) * z) := by
    intro n z hz
    have hev : fsans (κn n) =ᶠ[𝓝 z] (fun u => fsans κ ((ρ n : ℂ) * u) / (ρ n : ℂ) /
        (1 + c n * (fsans κ ((ρ n : ℂ) * u) / (ρ n : ℂ)))) := by
      filter_upwards [isOpen_ball.mem_nhds hz] with u hu
      exact (hf n u hu).2
    rw [ab112_S_congr hev]
    exact s36l_S_dil hfd hfd' (hρ n).1 (hρ n).2 hz (hf n z hz).1
  set W : ℂ → ℂ := fun z => (((1 - ‖z‖ ^ 2) / 2 : ℝ) : ℂ) with hW
  have hWc : Continuous W := by rw [hW]; fun_prop
  have hWn : ∀ z, ENNReal.ofReal (rho z)⁻¹ = ‖W z‖ₑ ^ 2 := by
    intro z
    rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _), hW]
    simp only [Complex.norm_real, Real.norm_eq_abs, sq_abs]
    congr 1
    unfold rho
    rw [inv_div]
    ring
  have hA2sq : ∀ φ : ℂ → ℂ, normA2 unitDisc φ ^ 2 = ∫⁻ z in unitDisc, ‖φ z * W z‖ₑ ^ 2 := by
    intro φ
    unfold normA2
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
    norm_num
    refine lintegral_congr fun z => ?_
    simp only [hWn, enorm_mul, mul_pow, enorm_eq_nnnorm]
  have hSc : ContinuousOn (schwarzianHol (fsans κ)) unitDisc := hSfd.continuousOn
  have hmapsto : ∀ n, MapsTo (fun z : ℂ => (ρ n : ℂ) * z) unitDisc unitDisc := fun n z hz =>
    s36l_mul_mem (hρ n).1 (hρ n).2.le hz
  have hfin : IsFiniteMeasure (volume.restrict unitDisc) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact measure_ball_lt_top⟩
  have hΦL : (∫⁻ u in unitDisc, ‖schwarzianHol (fsans κ) u * W u‖ₑ ^ 2) ≠ ∞ := by
    rw [← hA2sq]
    exact ENNReal.pow_ne_top hSf.2.ne
  have hL2 := s36l_L2_vitali (μ := volume.restrict unitDisc)
    (u := fun n z => (ρ n : ℂ) ^ 2 * schwarzianHol (fsans κ) ((ρ n : ℂ) * z) * W z)
    (u0 := fun z => schwarzianHol (fsans κ) z * W z)
    (fun n => ((continuousOn_const.mul (hSc.comp (continuousOn_const.mul continuousOn_id) (hmapsto n))).mul
      hWc.continuousOn).aestronglyMeasurable measurableSet_ball)
    ((hSc.mul hWc.continuousOn).aestronglyMeasurable measurableSet_ball) hΦL ?_ ?_
  rotate_left
  · intro ε hε
    obtain ⟨δ, hδ, hδs⟩ := s36l_dil_ui hΦL hε.ne'
    refine ⟨δ, hδ, fun n s hs hμs => le_trans ?_ (hδs (ρ n) (hρ n).1 (hρ n).2.le s hs hμs)⟩
    refine lintegral_mono_ae ?_
    filter_upwards [ae_restrict_of_ae (ae_restrict_mem measurableSet_ball)] with w hw
    refine s36l_enorm_sq_le (hρ n).1.le ?_
    have hw1 := mem_ball_zero_iff.mp hw
    have hr0 := (hρ n).1
    have hr1 := (hρ n).2
    have hsq1 : ‖w‖ ^ 2 ≤ 1 := pow_le_one₀ (norm_nonneg w) hw1.le
    have hsq2 : (ρ n * ‖w‖) ^ 2 ≤ 1 :=
      pow_le_one₀ (by positivity) (mul_le_one₀ hr1.le (norm_nonneg w) hw1.le)
    have hW1 : ‖W w‖ = (1 - ‖w‖ ^ 2) / 2 := by
      rw [hW]; dsimp only; rw [Complex.norm_real, Real.norm_of_nonneg (by linarith)]
    have hrw : ‖(ρ n : ℂ) * w‖ = ρ n * ‖w‖ := by
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hr0.le]
    have hW2 : ‖W ((ρ n : ℂ) * w)‖ = (1 - (ρ n * ‖w‖) ^ 2) / 2 := by
      rw [hW]; dsimp only; rw [hrw, Complex.norm_real, Real.norm_of_nonneg (by linarith)]
    rw [norm_mul, norm_mul, norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hr0.le, hW1, hW2]
    have hS0 := norm_nonneg (schwarzianHol (fsans κ) ((ρ n : ℂ) * w))
    have hab : (1 - ‖w‖ ^ 2) / 2 ≤ (1 - (ρ n * ‖w‖) ^ 2) / 2 := by
      have : (ρ n * ‖w‖) ^ 2 ≤ ‖w‖ ^ 2 := by
        rw [mul_pow]; exact mul_le_of_le_one_left (sq_nonneg _) (pow_le_one₀ hr0.le hr1.le)
      linarith
    have h0 : 0 ≤ (1 - ‖w‖ ^ 2) / 2 := by linarith
    calc ρ n ^ 2 * ‖schwarzianHol (fsans κ) ((ρ n : ℂ) * w)‖ * ((1 - ‖w‖ ^ 2) / 2)
        ≤ ρ n * ‖schwarzianHol (fsans κ) ((ρ n : ℂ) * w)‖ * ((1 - (ρ n * ‖w‖) ^ 2) / 2) := by
          gcongr
          nlinarith
      _ = _ := by ring
  · filter_upwards [ae_restrict_mem measurableSet_ball] with w hw
    have hrN : Tendsto (fun n => (ρ n : ℂ)) atTop (𝓝 1) := by
      have h := (Complex.continuous_ofReal.tendsto 1).comp hρl
      rw [Complex.ofReal_one] at h
      exact h
    have hrw : Tendsto (fun n => (ρ n : ℂ) * w) atTop (𝓝 w) := by simpa using hrN.mul_const w
    have hSw := (hSfd.differentiableAt (isOpen_ball.mem_nhds hw)).continuousAt.tendsto.comp hrw
    have h := ((hrN.pow 2).mul hSw).mul_const (W w)
    rw [one_pow, one_mul] at h
    exact h
  have hS1 : Tendsto (fun n => normA2 unitDisc (fun z => schwarzianHol (fsans (κn n)) z -
      schwarzianHol (fsans κ) z)) atTop (𝓝 0) := by
    refine AppA.a6_tendsto_of_sq (hL2.congr fun n => ?_)
    rw [hA2sq]
    refine setLIntegral_congr_fun measurableSet_ball fun z hz => ?_
    rw [hSn n z hz]
    congr 2
    ring
  have hpq : @Tendsto _ _ p atTop (@nhds _ hilbertTopology (Phi ⟨κ, hκ⟩)) := by
    refine (AppA.a4_T01_tendsto_iff hpT hκT).mpr (hS1.congr fun n => ?_)
    refine normA2_congr measurableSet_ball fun z hz => ?_
    show _ = schwarzianHol (fsans ((Quotient.out (p n) : LinfStarBall) : LinfStar)) z -
      schwarzianHol (fsans ((Quotient.out (Phi ⟨κ, hκ⟩) : LinfStarBall) : LinfStar)) z
    rw [ab112_S_eqOn isOpen_ball (hcl n).1 hz, ab112_S_eqOn isOpen_ball hcl0.1 hz]
  -- (E2) `𝒮(𝗀ₙ) → 𝒮(𝗀)` in `A₂(𝔻*)`
  have hSLU := AppA.a6_S_LU hEo hgnd (fun n z hz => (s2c_facts (hmem n)).2.2.2.2.2.2.2.1 z hz) hgd hgd' hgc
  have hnorm := AppA.a6_norm_tendsto hpT hκT hpq
  have hgM : ∀ μ : LinfStarBall, gMu (μ : LinfStar) = gsans (μ : LinfStar) := fun μ =>
    (S2C.s2c_gsans_eq μ.2).symm
  have hnorm' : Tendsto (fun n => normA2 unitDiscExterior (schwarzianHol (gsans (κn n)))) atTop
      (𝓝 (normA2 unitDiscExterior (schwarzianHol (gsans κ)))) := by
    have e : ∀ n, normA2 unitDiscExterior (schwarzianHol (gMu ((Quotient.out (p n) : LinfStarBall) : LinfStar))) =
        normA2 unitDiscExterior (schwarzianHol (gsans (κn n))) := fun n => by
      rw [hgM]
      exact normA2_congr hEm (ab112_S_eqOn hEo (hcl n).2)
    have e0 : normA2 unitDiscExterior (schwarzianHol (gMu ((Quotient.out (Phi ⟨κ, hκ⟩) : LinfStarBall) : LinfStar))) =
        normA2 unitDiscExterior (schwarzianHol (gsans κ)) := by
      rw [hgM]
      exact normA2_congr hEm (ab112_S_eqOn hEo hcl0.2)
    rw [e0] at hnorm
    exact hnorm.congr e
  have hS2 := AppA.a6_RR (fun n => (s36l_S_mem (hmem n) (hpT n)).2) hSg hSLU hnorm'
  -- (E3) `𝒜(𝗀ₙ) → 𝒜(𝗀)` in `A₂¹(𝔻*)` (Cor. A.6 inverse step)
  have hψmem : ∀ n, preSchwarzian (gsans (κn n)) ∈ AppA.A21tildeExt := fun n =>
    ⟨s36l_psiE_mem (hmem n) (hpT n), AppA.appa2_preSchwarzian_cubic (AppB.b8_welding_normalized_pair (hmem n)).2.2.2.2.1⟩
  have hψ0 : preSchwarzian (gsans κ) ∈ AppA.A21tildeExt :=
    ⟨s36l_psiE_mem hκ hκT, AppA.appa2_preSchwarzian_cubic (AppB.b8_welding_normalized_pair hκ).2.2.2.2.1⟩
  have hA21 := AppA.a6_ext_inverse hψ0 hψmem hS2
  -- the bound
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hA21.eventually (Iic_mem_nhds zero_lt_one))
  set L0 : ℝ≥0∞ := ∫⁻ w in unitDiscExterior, ‖preSchwarzian (gsans κ) w‖ₑ ^ 2 with hL0
  have hL0t : L0 ≠ ∞ := s36l_A21_L2 hψ0.1
  set Mlow : ℝ≥0∞ := (Finset.range N).sup
    (fun n => ∫⁻ w in unitDiscExterior, ‖preSchwarzian (gsans (κn n)) w‖ₑ ^ 2) with hMlow
  have hMlowt : Mlow < ∞ := by
    rw [hMlow, Finset.sup_lt_iff ENNReal.zero_lt_top]
    intro n _
    exact (s36l_A21_L2 (hψmem n).1).lt_top
  refine ⟨Mlow + (2 * 1 + 2 * L0), ENNReal.add_lt_top.mpr ⟨hMlowt, ENNReal.add_lt_top.mpr
    ⟨ENNReal.mul_lt_top (by norm_num) (by norm_num), ENNReal.mul_lt_top (by norm_num) hL0t.lt_top⟩⟩, fun n => ?_⟩
  simp only [← enorm_eq_nnnorm]
  rcases lt_or_ge n N with hn | hn
  · exact le_add_right (Finset.le_sup (f := fun n => ∫⁻ w in unitDiscExterior,
      ‖preSchwarzian (gsans (κn n)) w‖ₑ ^ 2) (Finset.mem_range.mpr hn))
  · refine le_add_left ?_
    have h1 : (∫⁻ w in unitDiscExterior, ‖preSchwarzian (gsans (κn n)) w - preSchwarzian (gsans κ) w‖ₑ ^ 2) ≤ 1 := by
      have h : normA21 unitDiscExterior (fun z => preSchwarzian (gsans (κn n)) z - preSchwarzian (gsans κ) z) ≤ 1 :=
        hN n hn
      unfold normA21 at h
      have h2 := ENNReal.rpow_le_rpow h (by norm_num : (0 : ℝ) ≤ 2)
      rw [← ENNReal.rpow_mul, ENNReal.one_rpow] at h2
      norm_num at h2
      simpa only [enorm_eq_nnnorm] using h2
    calc (∫⁻ w in unitDiscExterior, ‖preSchwarzian (gsans (κn n)) w‖ₑ ^ 2)
        ≤ ∫⁻ w in unitDiscExterior, (2 * ‖preSchwarzian (gsans (κn n)) w - preSchwarzian (gsans κ) w‖ₑ ^ 2 +
            2 * ‖preSchwarzian (gsans κ) w‖ₑ ^ 2) := by
          refine lintegral_mono fun w => ?_
          have h := s36l_enorm_sq_add_le (x := preSchwarzian (gsans (κn n)) w)
            (y := preSchwarzian (gsans (κn n)) w - preSchwarzian (gsans κ) w) (norm_nonneg (preSchwarzian (gsans κ) w))
            (by have := norm_sub_norm_le (preSchwarzian (gsans (κn n)) w) (preSchwarzian (gsans κ) w); linarith)
          rwa [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm] at h
      _ = 2 * (∫⁻ w in unitDiscExterior, ‖preSchwarzian (gsans (κn n)) w - preSchwarzian (gsans κ) w‖ₑ ^ 2) +
            2 * L0 := by
          rw [lintegral_add_right' _ (((hψ0.1.1.continuousOn.aestronglyMeasurable hEm).enorm.pow_const 2).const_mul 2),
            lintegral_const_mul' _ _ (by norm_num), lintegral_const_mul' _ _ (by norm_num)]
      _ ≤ 2 * 1 + 2 * L0 := by gcongr

/-! ### Passage to the limit -/

/-- The left side converges (explicit `𝖿`-side). -/
theorem s36l_lhs_tendsto {κ : LinfStar} (hκ : κ ∈ LinfStarBall) {z : ℂ} (hz : z ∈ unitDisc) (hz0 : z ≠ 0)
    (ρ : ℕ → ℝ) (hρ : ∀ n, 0 < ρ n ∧ ρ n < 1) (hρl : Tendsto ρ atTop (𝓝 1))
    (hae : ∀ᵐ z, Tendsto (fun n => extB κ ((ρ n : ℂ) * z)) atTop (𝓝 (extB κ z))) :
    let κn : ℕ → LinfStar := fun n =>
      toLinf (fun z => if 1 / ρ n < ‖z‖ then (κ : ℂ → ℂ) ((ρ n : ℂ) * z) else 0)
    Tendsto (fun n => -(preSchwarzian (fsans (κn n)) z - 2 * deriv (fsans (κn n)) z / fsans (κn n) z + 2 / z))
      atTop (𝓝 (-(preSchwarzian (fsans κ) z - 2 * deriv (fsans κ) z / fsans κ z + 2 / z))) := by
  intro κn
  obtain ⟨c, -, hf⟩ := s36l_dil_fsans hκ ρ hρ hρl hae
  obtain ⟨hfd, -, -, -, -, -, -, -, hfnz, hfd'⟩ := s2c_facts hκ
  set f := fsans κ with hfdef
  have hD : IsOpen unitDisc := isOpen_ball
  have hfa : ∀ y ∈ unitDisc, AnalyticAt ℂ f y := fun y hy => hfd.analyticAt (hD.mem_nhds hy)
  -- `𝖿ₙ = M_{cₙ} ∘ Fₙ` and `M_c(ζ) = (ζ⁻¹ + c)⁻¹`: the left side only sees `Fₙ = 𝖿(ρₙ ·)/ρₙ`
  have hQ : ∀ n, preSchwarzian (fsans (κn n)) z - 2 * deriv (fsans (κn n)) z / fsans (κn n) z + 2 / z =
      (ρ n : ℂ) * (preSchwarzian f ((ρ n : ℂ) * z) - 2 * deriv f ((ρ n : ℂ) * z) / f ((ρ n : ℂ) * z)) +
        2 / z := by
    intro n
    obtain ⟨hρ0, hρ1⟩ := hρ n
    set r : ℂ := (ρ n : ℂ) with hr
    have hr0 : r ≠ 0 := by rw [hr]; exact_mod_cast hρ0.ne'
    have hFz : r * z ∈ unitDisc := by
      have hz1 := mem_ball_zero_iff.mp hz
      refine mem_ball_zero_iff.mpr ?_
      rw [norm_mul, hr, Complex.norm_real, Real.norm_of_nonneg hρ0.le]
      nlinarith [norm_nonneg z]
    have hrz0 : r * z ≠ 0 := mul_ne_zero hr0 hz0
    let F : ℂ → ℂ := fun w => f (r * w) / r
    have hlin : AnalyticAt ℂ (fun w : ℂ => r * w) z := analyticAt_const.mul analyticAt_id
    have hFa : AnalyticAt ℂ F z := ((hfa _ hFz).comp hlin).div_const
    have hFz0 : F z ≠ 0 := div_ne_zero (hfnz _ hFz hrz0) hr0
    have hdF : deriv F z = deriv f (r * z) := by
      have h1 := deriv_affine_precomp f r 0 z
      simp only [add_zero] at h1
      show deriv (fun w => f (r * w) / r) z = _
      rw [deriv_div_const, h1, mul_div_cancel_left₀ _ hr0]
    have hpF : preSchwarzian F z = r * preSchwarzian f (r * z) := by
      have h1 := preSchwarzian_affine_postcomp (fun u => f (r * u + 0)) (inv_ne_zero hr0) 0 z
      have h2 := preSchwarzian_affine_precomp f r 0 z
      simp only [add_zero] at h1 h2
      rw [← h2, ← h1]
      show preSchwarzian (fun w => f (r * w) / r) z = _
      congr 1
      funext w
      rw [div_eq_inv_mul]
    have hFd : deriv F z ≠ 0 := by rw [hdF]; exact hfd' _ hFz
    have hHz : (F z)⁻¹ + c n ≠ 0 := by
      intro h
      apply (hf n z hz).1
      calc 1 + c n * (f (r * z) / r) = F z * ((F z)⁻¹ + c n) := by
            rw [mul_add, mul_inv_cancel₀ hFz0]; ring
        _ = 0 := by rw [h, mul_zero]
    let h2 : ℂ → ℂ := fun w => ((F w)⁻¹ + c n)⁻¹
    have hHa : AnalyticAt ℂ (fun w => (F w)⁻¹ + c n) z := (hFa.inv hFz0).add analyticAt_const
    have hh2a : AnalyticAt ℂ h2 z := hHa.inv hHz
    have hh2z : h2 z ≠ 0 := inv_ne_zero hHz
    have hh2d : deriv h2 z ≠ 0 := by
      have hdH : HasDerivAt (fun w => (F w)⁻¹ + c n) (-(deriv F z) / (F z) ^ 2) z :=
        (hFa.differentiableAt.hasDerivAt.inv hFz0).add_const (c n)
      have hdh2 := hdH.inv hHz
      rw [show deriv h2 z = _ from hdh2.deriv]
      exact div_ne_zero (neg_ne_zero.mpr (div_ne_zero (neg_ne_zero.mpr hFd) (pow_ne_zero 2 hFz0)))
        (pow_ne_zero 2 hHz)
    have hev : fsans (κn n) =ᶠ[𝓝 z] h2 := by
      filter_upwards [hD.mem_nhds hz, hFa.continuousAt.eventually_ne hFz0] with w hw hFw
      refine (hf n w hw).2.trans ?_
      show F w / (1 + c n * F w) = ((F w)⁻¹ + c n)⁻¹
      rw [← inv_div]
      congr 1
      rw [add_div, one_div, mul_div_assoc, div_self hFw, mul_one]
    have hpre : preSchwarzian (fsans (κn n)) z = preSchwarzian h2 z := by
      unfold preSchwarzian
      rw [hev.deriv.deriv_eq, hev.deriv_eq]
    have e1 := preSchwarzian_inv_comp hh2a hh2z hh2d
    have e2 : preSchwarzian (fun w => (h2 w)⁻¹) z = preSchwarzian (fun w => (F w)⁻¹) z :=
      (congrArg (fun φ => preSchwarzian φ z) (funext fun w => inv_inv ((F w)⁻¹ + c n))).trans
        (preSchwarzian_add_const (fun u => (F u)⁻¹) (c n) z)
    have e3 := preSchwarzian_inv_comp hFa hFz0 hFd
    have key : preSchwarzian h2 z - 2 * deriv h2 z / h2 z = preSchwarzian F z - 2 * deriv F z / F z :=
      e1.symm.trans (e2.trans e3)
    rw [hpre, hev.deriv_eq, hev.eq_of_nhds, key, hpF, hdF]
    show r * preSchwarzian f (r * z) - 2 * deriv f (r * z) / (f (r * z) / r) + 2 / z = _
    rw [div_div_eq_mul_div]
    ring
  refine Tendsto.neg (Tendsto.congr (fun n => (hQ n).symm) ?_)
  have hρc : Tendsto (fun n => (ρ n : ℂ)) atTop (𝓝 1) := by
    have h := (Complex.continuous_ofReal.tendsto 1).comp hρl
    rw [Complex.ofReal_one] at h
    exact h
  have hz' : Tendsto (fun n => (ρ n : ℂ) * z) atTop (𝓝 z) := by simpa using hρc.mul_const z
  have ha := hfa z hz
  have hΦ : ContinuousAt (fun w => preSchwarzian f w - 2 * deriv f w / f w) z := by
    show ContinuousAt (fun w => deriv (deriv f) w / deriv f w - 2 * deriv f w / f w) z
    exact (ha.deriv.deriv.continuousAt.div ha.deriv.continuousAt (hfd' z hz)).sub
      ((continuousAt_const.mul ha.deriv.continuousAt).div ha.continuousAt (hfnz z hz hz0))
  convert (hρc.mul (hΦ.tendsto.comp hz')).add_const (2 / z) using 2
  all_goals first | rw [one_mul] | simp only [Function.comp_def]

/-- The `K₁`-term converges (explicit `𝖿`-side: `K₁(𝖿ₙ)(z, w) = ρₙ² K₁(𝖿)(ρₙz, ρₙw)` by Möbius invariance). -/
theorem s36l_K1_tendsto {κ : LinfStar} (hκ : κ ∈ LinfStarBall) (hκT : Phi ⟨κ, hκ⟩ ∈ T01) {z : ℂ}
    (hz : z ∈ unitDisc)
    (ρ : ℕ → ℝ) (hρ : ∀ n, 0 < ρ n ∧ ρ n < 1) (hρl : Tendsto ρ atTop (𝓝 1))
    (hae : ∀ᵐ z, Tendsto (fun n => extB κ ((ρ n : ℂ) * z)) atTop (𝓝 (extB κ z))) :
    let κn : ℕ → LinfStar := fun n =>
      toLinf (fun z => if 1 / ρ n < ‖z‖ then (κ : ℂ → ℂ) ((ρ n : ℂ) * z) else 0)
    Tendsto (fun n => ∫ w in unitDisc, kerK1 (fsans (κn n)) z w * conj (preSchwarzian (fsans (κn n)) w))
      atTop (𝓝 (∫ w in unitDisc, kerK1 (fsans κ) z w * conj (preSchwarzian (fsans κ) w))) := by
  intro κn
  obtain ⟨c, hc0, hf⟩ := s36l_dil_fsans hκ ρ hρ hρl hae
  have hT := s36l_dil_mem hκ hκT ρ hρ
  dsimp only at hT hf
  obtain ⟨hfd, hfi, -, -, -, -, -, -, -, hfd'⟩ := s2c_facts hκ
  have hψA := s36l_psi_mem hκ hκT
  have hψL := s36l_A21_L2 hψA
  have hfL := s36l_fsans_deriv_L2 hκ
  obtain ⟨M, hM0, hM⟩ := s36l_fsans_bdd hκ
  have hrow := AppB.kerK1_row_mem_A21 (And.intro hfd hfi : AppB.IsUnivalentDisc (fsans κ)) hz
  set f := fsans κ with hfdef
  set ψ := preSchwarzian f with hψdef
  have hD : IsOpen unitDisc := isOpen_ball
  have hfa : ∀ y ∈ unitDisc, AnalyticAt ℂ f y := fun y hy => hfd.analyticAt (hD.mem_nhds hy)
  have hU : ∀ m, AppB.IsUnivalentDisc (fsans (κn m)) := fun m =>
    And.intro (s2c_facts (hT m).1).1 (s2c_facts (hT m).1).2.1
  have hψm : ∀ m, preSchwarzian (fsans (κn m)) ∈ A21fun unitDisc := fun m => s36l_psi_mem (hT m).1 (hT m).2
  -- pointwise formulas: `𝖿ₙ = M_{cₙ} ∘ Fₙ` on `𝔻`, `Fₙ = f(ρₙ ·)/ρₙ`
  have hpt : ∀ m, ∀ w ∈ unitDisc,
      preSchwarzian (fsans (κn m)) w = (ρ m : ℂ) * ψ ((ρ m : ℂ) * w) -
          2 * c m * deriv f ((ρ m : ℂ) * w) / (1 + c m * (f ((ρ m : ℂ) * w) / (ρ m : ℂ))) ∧
        (w ≠ z → kerK1 (fsans (κn m)) z w = (ρ m : ℂ) ^ 2 * kerK1 f ((ρ m : ℂ) * z) ((ρ m : ℂ) * w)) := by
    intro m w hw
    obtain ⟨hρ0, hρ1⟩ := hρ m
    have hr0 : (ρ m : ℂ) ≠ 0 := by exact_mod_cast hρ0.ne'
    have hrw := s36l_mul_mem hρ0 hρ1.le hw
    have hrz := s36l_mul_mem hρ0 hρ1.le hz
    have hloc : ∀ u ∈ unitDisc, fsans (κn m) =ᶠ[𝓝 u]
        (fun v => f ((ρ m : ℂ) * v) / (ρ m : ℂ) / (1 + c m * (f ((ρ m : ℂ) * v) / (ρ m : ℂ)))) := by
      intro u hu
      filter_upwards [hD.mem_nhds hu] with v hv
      exact (hf m v hv).2
    obtain ⟨hFa, hFd, hFp⟩ := s36l_dilF hfd hr0 hrw
    constructor
    · have hev := hloc w hw
      have hpre : preSchwarzian (fsans (κn m)) w = preSchwarzian
          (fun v => f ((ρ m : ℂ) * v) / (ρ m : ℂ) / (1 + c m * (f ((ρ m : ℂ) * v) / (ρ m : ℂ)))) w := by
        unfold preSchwarzian
        rw [hev.deriv.deriv_eq, hev.deriv_eq]
      rw [hpre, s36l_mob_comp_preS (F := fun v => f ((ρ m : ℂ) * v) / (ρ m : ℂ)) hFa
        (by rw [hFd]; exact hfd' _ hrw) (hf m w hw).1, hFp, hFd]
    · intro hwz
      have hzw : z ≠ w := fun h => hwz h.symm
      obtain ⟨hFza, -, -⟩ := s36l_dilF hfd hr0 hrz
      have hne : f ((ρ m : ℂ) * z) / (ρ m : ℂ) ≠ f ((ρ m : ℂ) * w) / (ρ m : ℂ) := by
        intro h
        have h' : f ((ρ m : ℂ) * z) = f ((ρ m : ℂ) * w) := by
          have := congrArg (fun x => x * (ρ m : ℂ)) h
          simpa only [div_mul_cancel₀ _ hr0] using this
        exact hzw (mul_left_cancel₀ hr0 (hfi hrz hrw h'))
      rw [gk_kerK1_congr_eventually (hloc z hz) (hloc w hw),
        s36l_kerK1_mob (F := fun v => f ((ρ m : ℂ) * v) / (ρ m : ℂ)) hzw hFza.differentiableAt
          hFa.differentiableAt (hf m z hz).1 (hf m w hw).1 hne,
        s36l_kerK1_dilF hfd hfi hr0 hzw hrz hrw]
  -- eventually `|cₙ| < 1/(4M)` and `ρₙ > 1/2`
  have hc1 : Tendsto (fun n => ‖c n‖) atTop (𝓝 0) := by simpa using hc0.norm
  have hM4 : (0 : ℝ) < 1 / (4 * M) := by positivity
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    ((hc1.eventually (gt_mem_nhds hM4)).and (hρl.eventually (lt_mem_nhds (by norm_num : (1 / 2 : ℝ) < 1))))
  -- the dominating dilation profile
  set Φ : ℂ → ℂ := fun u => ((‖ψ u‖ + 2 / M * ‖deriv f u‖ : ℝ) : ℂ) with hΦ
  have hΦn : ∀ u, ‖Φ u‖ = ‖ψ u‖ + 2 / M * ‖deriv f u‖ := fun u => by
    rw [hΦ]
    dsimp only
    rw [Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  have hΦL : (∫⁻ u in unitDisc, ‖Φ u‖ₑ ^ 2) ≠ ∞ := by
    have hle : ∀ u, ‖Φ u‖ₑ ^ 2 ≤ 2 * ‖ψ u‖ₑ ^ 2 + 2 * ENNReal.ofReal ((2 / M) ^ 2) * ‖deriv f u‖ₑ ^ 2 := by
      intro u
      have h := s36l_enorm_sq_add_le (x := Φ u) (y := ψ u) (by positivity : (0 : ℝ) ≤ 2 / M * ‖deriv f u‖)
        (hΦn u).le
      rw [mul_pow, ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ (2 / M) ^ 2),
        ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm, ← mul_assoc] at h
      exact h
    have hψm' : AEMeasurable (fun u => 2 * ‖ψ u‖ₑ ^ 2) (volume.restrict unitDisc) :=
      ((hψA.1.continuousOn.aestronglyMeasurable measurableSet_ball).enorm.pow_const 2).const_mul 2
    refine ne_top_of_le_ne_top ?_ (lintegral_mono fun u => hle u)
    rw [lintegral_add_left' hψm', lintegral_const_mul' _ _ (by norm_num),
      lintegral_const_mul' _ _ (ENNReal.mul_ne_top (by norm_num) ENNReal.ofReal_ne_top)]
    exact ENNReal.add_ne_top.mpr ⟨ENNReal.mul_ne_top (by norm_num) hψL,
      ENNReal.mul_ne_top (ENNReal.mul_ne_top (by norm_num) ENNReal.ofReal_ne_top) hfL⟩
  -- pointwise domination for `n ≥ N`
  have hbound : ∀ m, N ≤ m → ∀ w ∈ unitDisc,
      ‖preSchwarzian (fsans (κn m)) w‖ ≤ ρ m * ‖Φ ((ρ m : ℂ) * w)‖ := by
    intro m hm w hw
    obtain ⟨hcm, hρm⟩ := hN m hm
    obtain ⟨hρ0, hρ1⟩ := hρ m
    have hrw := s36l_mul_mem hρ0 hρ1.le hw
    have hfM := hM _ hrw
    rw [(hpt m w hw).1, hΦn]
    have hnF : ‖c m * (f ((ρ m : ℂ) * w) / (ρ m : ℂ))‖ ≤ 1 / 2 := by
      rw [norm_mul, norm_div, Complex.norm_real, Real.norm_of_nonneg hρ0.le]
      have hcm' := hcm.le
      calc ‖c m‖ * (‖f ((ρ m : ℂ) * w)‖ / ρ m) ≤ (1 / (4 * M)) * (M / ρ m) := by gcongr
        _ ≤ 1 / 2 := by
          rw [div_mul_div_comm, one_mul, div_le_div_iff₀ (by positivity) (by norm_num)]
          nlinarith [mul_lt_mul_of_pos_left hρm hM0]
    have hQ : 1 / 2 ≤ ‖1 + c m * (f ((ρ m : ℂ) * w) / (ρ m : ℂ))‖ := by
      have h := norm_sub_norm_le (1 : ℂ) (-(c m * (f ((ρ m : ℂ) * w) / (ρ m : ℂ))))
      rw [norm_one, norm_neg, sub_neg_eq_add] at h
      linarith
    have hQ0 : 0 < ‖1 + c m * (f ((ρ m : ℂ) * w) / (ρ m : ℂ))‖ := by linarith
    refine (norm_sub_le _ _).trans ?_
    rw [mul_add]
    refine add_le_add (le_of_eq ?_) ?_
    · rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hρ0.le]
    · rw [norm_div, norm_mul, norm_mul, Complex.norm_two, div_le_iff₀ hQ0]
      have hD0 := norm_nonneg (deriv f ((ρ m : ℂ) * w))
      have hMi : 0 < M⁻¹ := inv_pos.mpr hM0
      have hc'' : ‖c m‖ ≤ M⁻¹ / 4 := by
        have := hcm.le
        rwa [one_div, mul_inv, mul_comm, ← div_eq_mul_inv] at this
      rw [div_eq_mul_inv 2 M]
      nlinarith [mul_le_mul_of_nonneg_right hc'' (by positivity : (0 : ℝ) ≤ 2 * ‖deriv f ((ρ m : ℂ) * w)‖),
        mul_le_mul_of_nonneg_left (mul_le_mul hρm.le hQ (by norm_num) hρ0.le)
          (by positivity : (0 : ℝ) ≤ 2 * M⁻¹ * ‖deriv f ((ρ m : ℂ) * w)‖)]
  have : IsFiniteMeasure (volume.restrict unitDisc) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact measure_ball_lt_top⟩
  rw [← tendsto_add_atTop_iff_nat N]
  refine s36l_vitali_pair (μ := volume.restrict unitDisc)
    (a := fun n w => kerK1 (fsans (κn (n + N))) z w)
    (b := fun n w => conj (preSchwarzian (fsans (κn (n + N))) w))
    (A := fun w => kerK1 f z w) (B := fun w => conj (ψ w))
    (C := ENNReal.ofReal (1 / (π * (1 - ‖z‖ ^ 2) ^ 2))) ENNReal.ofReal_ne_top ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro n
    exact (AppB.kerK1_row_mem_A21 (hU (n + N)) hz).1.continuousOn.aestronglyMeasurable measurableSet_ball
  · intro n
    exact (Complex.continuous_conj.comp_continuousOn (hψm (n + N)).1.continuousOn).aestronglyMeasurable
      measurableSet_ball
  · intro n
    have h := AppB.kerK1_row_sq_le (hU (n + N)) hz
    simpa only [enorm_eq_nnnorm] using h
  · intro n
    simp only [s36l_enorm_conj]
    exact s36l_A21_L2 (hψm (n + N))
  · intro ε hε
    obtain ⟨δ, hδ, hδs⟩ := s36l_dil_ui hΦL hε.ne'
    refine ⟨δ, hδ, fun n s hs hμs => le_trans ?_ (hδs (ρ (n + N)) (hρ _).1 (hρ _).2.le s hs hμs)⟩
    refine lintegral_mono_ae ?_
    filter_upwards [ae_restrict_of_ae (ae_restrict_mem measurableSet_ball)] with w hw
    show ‖conj (preSchwarzian (fsans (κn (n + N))) w)‖ₑ ^ 2 ≤ _
    rw [s36l_enorm_conj]
    exact s36l_enorm_sq_le (hρ _).1.le (hbound (n + N) (Nat.le_add_left N n) w hw)
  · refine s36l_int_mul (hrow.1.continuousOn.aestronglyMeasurable measurableSet_ball)
      ((Complex.continuous_conj.comp_continuousOn hψA.1.continuousOn).aestronglyMeasurable measurableSet_ball)
      (s36l_A21_L2 hrow) ?_
    simp only [s36l_enorm_conj]
    exact hψL
  · filter_upwards [ae_restrict_mem measurableSet_ball, ae_restrict_of_ae (Measure.ae_ne volume z)] with w hw hwz
    have hrN : Tendsto (fun n => (ρ (n + N) : ℂ)) atTop (𝓝 1) := by
      have h := (Complex.continuous_ofReal.tendsto 1).comp (hρl.comp (tendsto_add_atTop_nat N))
      rw [Complex.ofReal_one] at h
      exact h
    have hcN : Tendsto (fun n => c (n + N)) atTop (𝓝 0) := hc0.comp (tendsto_add_atTop_nat N)
    have hrw : Tendsto (fun n => (ρ (n + N) : ℂ) * w) atTop (𝓝 w) := by simpa using hrN.mul_const w
    have hrz : Tendsto (fun n => (ρ (n + N) : ℂ) * z) atTop (𝓝 z) := by simpa using hrN.mul_const z
    have hψc : ContinuousAt ψ w := (hψA.1.differentiableAt (hD.mem_nhds hw)).continuousAt
    have hdw : ContinuousAt (deriv f) w := (hfa w hw).deriv.continuousAt
    have hdz : ContinuousAt (deriv f) z := (hfa z hz).deriv.continuousAt
    have hfw : ContinuousAt f w := (hfa w hw).continuousAt
    have hfz : ContinuousAt f z := (hfa z hz).continuousAt
    have hzw : z - w ≠ 0 := sub_ne_zero.mpr fun h => hwz h.symm
    have hfzw : f z - f w ≠ 0 := sub_ne_zero.mpr fun h => hwz (hfi hw hz h.symm)
    have hne : ∀ n, (ρ (n + N) : ℂ) * z ≠ (ρ (n + N) : ℂ) * w := fun n h =>
      hwz (mul_left_cancel₀ (by exact_mod_cast (hρ (n + N)).1.ne') h).symm
    -- the kernel
    have T1 := tendsto_const_nhds (x := (1 : ℂ)).div ((hrz.sub hrw).pow 2) (pow_ne_zero 2 hzw)
    have T2 := ((hdz.tendsto.comp hrz).mul (hdw.tendsto.comp hrw)).div
      (((hfz.tendsto.comp hrz).sub (hfw.tendsto.comp hrw)).pow 2) (pow_ne_zero 2 hfzw)
    have hK := (hrN.pow 2).mul ((tendsto_const_nhds (x := (1 / (π : ℂ)))).mul (T1.sub T2))
    rw [one_pow, one_mul, ← kerK1_of_ne f fun h => hwz h.symm] at hK
    -- the pre-Schwarzian
    have B1 := hrN.mul (hψc.tendsto.comp hrw)
    have B2 := ((tendsto_const_nhds (x := (2 : ℂ))).mul hcN).mul (hdw.tendsto.comp hrw)
    have B3 := (tendsto_const_nhds (x := (1 : ℂ))).add (hcN.mul ((hfw.tendsto.comp hrw).div hrN one_ne_zero))
    have hB := B1.sub (B2.div B3 (by simp))
    have hL : (1 : ℂ) * ψ w - 2 * 0 * deriv f w / (1 + 0 * (f w / 1)) = ψ w := by simp
    rw [hL] at hB
    have hprod := hK.mul ((Complex.continuous_conj.tendsto _).comp hB)
    refine hprod.congr fun n => ?_
    obtain ⟨h1, h2⟩ := hpt (n + N) w hw
    simp only [h1, h2 hwz, kerK1_of_ne f (hne n), Function.comp_apply, Pi.div_apply, Pi.sub_apply,
      Pi.pow_apply, Pi.mul_apply]

/-- The `K₂`-term converges: locally uniform convergence on `𝔻*` (`s36l_dil_gconv`), the uniform tail bound near
`S¹` (`s36l_dil_gtail`) with Cauchy–Schwarz and the uniform energy bound (`s36l_dil_energy`). -/
theorem s36l_K2_tendsto {κ : LinfStar} (hκ : κ ∈ LinfStarBall) (hκT : Phi ⟨κ, hκ⟩ ∈ T01) {z : ℂ}
    (hz : z ∈ unitDisc)
    (ρ : ℕ → ℝ) (hρ : ∀ n, 0 < ρ n ∧ ρ n < 1) (hρl : Tendsto ρ atTop (𝓝 1))
    (hae : ∀ᵐ z, Tendsto (fun n => extB κ ((ρ n : ℂ) * z)) atTop (𝓝 (extB κ z))) :
    let κn : ℕ → LinfStar := fun n =>
      toLinf (fun z => if 1 / ρ n < ‖z‖ then (κ : ℂ → ℂ) ((ρ n : ℂ) * z) else 0)
    Tendsto (fun n => ∫ w in unitDiscExterior,
        kerK2 (fsans (κn n)) (gsans (κn n)) z w * conj (-preSchwarzian (gsans (κn n)) w))
      atTop (𝓝 (∫ w in unitDiscExterior, kerK2 (fsans κ) (gsans κ) z w * conj (-preSchwarzian (gsans κ) w))) := by
  intro κn
  obtain ⟨c, hc0, hf⟩ := s36l_dil_fsans hκ ρ hρ hρl hae
  have hT := s36l_dil_mem hκ hκT ρ hρ
  have hgc := s36l_dil_gconv hκ ρ hρ hρl hae
  have hgt := s36l_dil_gtail hκ ρ hρ hρl hae
  obtain ⟨M, hMt, hMb⟩ := s36l_dil_energy hκ hκT ρ hρ hρl hae
  dsimp only at hT hf hgc hgt hMb
  have hmem : ∀ m, κn m ∈ LinfStarBall := fun m => (hT m).1
  have hEo : IsOpen unitDiscExterior := isOpen_lt continuous_const continuous_norm
  have hEm : MeasurableSet unitDiscExterior := hEo.measurableSet
  obtain ⟨hfd, hfi, -, -, hgd, hgi, hgne, hgd', -, hfd'⟩ := s2c_facts hκ
  have hψE := s36l_psiE_mem hκ hκT
  have hψEL := s36l_A21_L2 hψE
  obtain ⟨hfzt, hfdt⟩ := s36l_fn_conv hfd hρ hρl hc0 (h := fun n => fsans (κn n)) hf hz
  have hkp := s36l_koebe_pos hκ hz
  have hksep : ∀ w ∈ unitDiscExterior, ‖deriv (fsans κ) z‖ * (1 - ‖z‖ ^ 2) / 4 ≤
      ‖gsans κ w - fsans κ z‖ := fun w hw => s36l_koebe_sep hκ hz hw
  have hgnd : ∀ n, DifferentiableOn ℂ (gsans (κn n)) unitDiscExterior := fun n => (s2c_facts (hmem n)).2.2.2.2.1
  have hgni : ∀ n, InjOn (gsans (κn n)) unitDiscExterior := fun n => (s2c_facts (hmem n)).2.2.2.2.2.1
  have hψn : ∀ n, preSchwarzian (gsans (κn n)) ∈ A21fun unitDiscExterior := fun n =>
    s36l_psiE_mem (hT n).1 (hT n).2
  set f := fsans κ with hfdef
  set g := gsans κ with hgdef
  set d0 : ℝ := ‖deriv f z‖ * (1 - ‖z‖ ^ 2) / 8 with hd0
  have hd0p : 0 < d0 := by rw [hd0]; linarith
  have hsep : ∀ w ∈ unitDiscExterior, d0 ≤ ‖g w - f z‖ := fun w hw => by
    have := hksep w hw
    rw [hd0]; linarith
  -- eventual control of `𝖿ₙ(z)`, `𝖿ₙ'(z)`
  have hf'0 : 0 < ‖deriv f z‖ := norm_pos_iff.mpr (hfd' z hz)
  have hN0 : ∀ᶠ n in atTop, ‖deriv f z‖ / 2 ≤ ‖deriv (fsans (κn n)) z‖ ∧
      ‖deriv (fsans (κn n)) z‖ ≤ ‖deriv f z‖ + 1 ∧ ‖fsans (κn n) z‖ ≤ ‖f z‖ + 1 :=
    ((hfdt.norm.eventually (lt_mem_nhds (half_lt_self hf'0))).and
      ((hfdt.norm.eventually (gt_mem_nhds (lt_add_one _))).and
        (hfzt.norm.eventually (gt_mem_nhds (lt_add_one _))))).mono fun n h => ⟨h.1.le, h.2.1.le, h.2.2.le⟩
  have hsepn : ∀ n, ‖deriv f z‖ / 2 ≤ ‖deriv (fsans (κn n)) z‖ → ∀ w ∈ unitDiscExterior,
      d0 ≤ ‖gsans (κn n) w - fsans (κn n) z‖ := by
    intro n hn w hw
    have h1 := s36l_koebe_sep (hmem n) hz hw
    have h2 : 0 ≤ 1 - ‖z‖ ^ 2 := by
      have := mem_ball_zero_iff.mp hz
      nlinarith [norm_nonneg z]
    have h3 : ‖deriv f z‖ / 2 * (1 - ‖z‖ ^ 2) ≤ ‖deriv (fsans (κn n)) z‖ * (1 - ‖z‖ ^ 2) :=
      mul_le_mul_of_nonneg_right hn h2
    rw [hd0]
    linarith
  -- kernel bound
  set K1 : ℝ := (‖deriv f z‖ + 1) / (π * d0 ^ 2) with hK1
  have hK1p : 0 < K1 := by rw [hK1]; positivity
  have hkerb : ∀ n, ‖deriv (fsans (κn n)) z‖ ≤ ‖deriv f z‖ + 1 →
      (∀ w ∈ unitDiscExterior, d0 ≤ ‖gsans (κn n) w - fsans (κn n) z‖) → ∀ w ∈ unitDiscExterior,
      ‖kerK2 (fsans (κn n)) (gsans (κn n)) z w‖ ≤ K1 * ‖deriv (gsans (κn n)) w‖ := by
    intro n ha hs w hw
    have hq : d0 ^ 2 ≤ ‖gsans (κn n) w - fsans (κn n) z‖ ^ 2 := pow_le_pow_left₀ hd0p.le (hs w hw) 2
    show ‖1 / (π : ℂ) * (deriv (fsans (κn n)) z * deriv (gsans (κn n)) w /
      (fsans (κn n) z - gsans (κn n) w) ^ 2)‖ ≤ _
    simp only [norm_mul, norm_div, norm_pow, norm_one, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le]
    rw [norm_sub_rev (fsans (κn n) z)]
    have h1 : ‖deriv (fsans (κn n)) z‖ * ‖deriv (gsans (κn n)) w‖ / ‖gsans (κn n) w - fsans (κn n) z‖ ^ 2 ≤
        (‖deriv f z‖ + 1) * ‖deriv (gsans (κn n)) w‖ / d0 ^ 2 :=
      div_le_div₀ (by positivity) (mul_le_mul_of_nonneg_right ha (norm_nonneg _)) (pow_pos hd0p 2) hq
    calc 1 / π * (‖deriv (fsans (κn n)) z‖ * ‖deriv (gsans (κn n)) w‖ /
          ‖gsans (κn n) w - fsans (κn n) z‖ ^ 2)
        ≤ 1 / π * ((‖deriv f z‖ + 1) * ‖deriv (gsans (κn n)) w‖ / d0 ^ 2) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = K1 * ‖deriv (gsans (κn n)) w‖ := by
          rw [hK1]
          field_simp
  -- `L²` facts in `‖·‖ₑ` form
  have hPn : ∀ n, (∫⁻ w in unitDiscExterior, ‖conj (-preSchwarzian (gsans (κn n)) w)‖ₑ ^ 2) ≤ M := by
    intro n
    simp only [s36l_enorm_conj, enorm_neg]
    simpa only [enorm_eq_nnnorm] using hMb n
  set Mtot : ℝ≥0∞ := M + ∫⁻ w in unitDiscExterior, ‖preSchwarzian g w‖ₑ ^ 2 with hMtot
  have hMtott : Mtot ≠ ∞ := ENNReal.add_ne_top.mpr ⟨hMt.ne, hψEL⟩
  have hMtotr : Mtot = ENNReal.ofReal Mtot.toReal := (ENNReal.ofReal_toReal hMtott).symm
  have hP0 : (∫⁻ w in unitDiscExterior, ‖conj (-preSchwarzian g w)‖ₑ ^ 2) ≤ Mtot := by
    simp only [s36l_enorm_conj, enorm_neg]
    exact le_add_self
  have hPn' : ∀ n, (∫⁻ w in unitDiscExterior, ‖conj (-preSchwarzian (gsans (κn n)) w)‖ₑ ^ 2) ≤ Mtot :=
    fun n => (hPn n).trans le_self_add
  -- measurability
  have hcPn : ∀ n, ContinuousOn (fun w => conj (-preSchwarzian (gsans (κn n)) w)) unitDiscExterior := fun n =>
    Complex.continuous_conj.comp_continuousOn (hψn n).1.continuousOn.neg
  have hcP0 : ContinuousOn (fun w => conj (-preSchwarzian g w)) unitDiscExterior :=
    Complex.continuous_conj.comp_continuousOn hψE.1.continuousOn.neg
  have hcKn : ∀ n, ContinuousOn (fun w => kerK2 (fsans (κn n)) (gsans (κn n)) z w) unitDiscExterior :=
    fun n => s36l_K2row_cont (hmem n) hz
  have hcK0 : ContinuousOn (fun w => kerK2 f g z w) unitDiscExterior := s36l_K2row_cont hκ hz
  have hFint : ∀ n, IntegrableOn
      (fun w => kerK2 (fsans (κn n)) (gsans (κn n)) z w * conj (-preSchwarzian (gsans (κn n)) w))
      unitDiscExterior :=
    fun n => s36l_int_mul ((hcKn n).aestronglyMeasurable hEm) ((hcPn n).aestronglyMeasurable hEm)
      (s36l_K2row_L2 (hmem n) hz) (ne_top_of_le_ne_top hMt.ne (hPn n))
  have hFint0 : IntegrableOn (fun w => kerK2 f g z w * conj (-preSchwarzian g w)) unitDiscExterior :=
    s36l_int_mul (hcK0.aestronglyMeasurable hEm) (hcP0.aestronglyMeasurable hEm)
      (s36l_K2row_L2 hκ hz) (ne_top_of_le_ne_top hMtott hP0)
  refine s36l_split_tendsto fun ε hε => ?_
  -- choice of the tail radius
  set Kc : ℝ := (‖deriv f z‖ + 1) ^ 2 / π ^ 2 * π with hKc
  have hKc0 : 0 ≤ Kc := by rw [hKc]; positivity
  set Mr : ℝ := Mtot.toReal with hMr
  have hMr0 : 0 ≤ Mr := ENNReal.toReal_nonneg
  set D : ℝ := Kc * (Mr + 1) / ε ^ 2 + 1 with hD
  have hD1 : 1 ≤ D := by rw [hD]; have : 0 ≤ Kc * (Mr + 1) / ε ^ 2 := by positivity
                         linarith
  have hD0 : 0 < D := by linarith
  have hKD : Kc / D ^ 2 * Mr ≤ ε ^ 2 := by
    have hD2 : D ≤ D ^ 2 := by nlinarith
    have hDK : Kc * (Mr + 1) ≤ ε ^ 2 * D := by
      have h := (div_le_iff₀ (by positivity : (0 : ℝ) < ε ^ 2)).mp
        (show Kc * (Mr + 1) / ε ^ 2 ≤ D by rw [hD]; linarith)
      linarith [mul_comm D (ε ^ 2)]
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left hD2 (sq_nonneg ε), mul_nonneg hKc0 hMr0]
  obtain ⟨R, hR1, hfar0, hfarN⟩ := s36l_far hκ hmem hgc (D + ‖f z‖ + 1)
  set A : Set ℂ := {w : ℂ | 1 < ‖w‖ ∧ ‖w‖ ≤ R} with hA
  set Tt : Set ℂ := {w : ℂ | R < ‖w‖} with hTt
  have hAm : MeasurableSet A :=
    (measurableSet_lt measurable_const measurable_norm).inter (measurableSet_le measurable_norm measurable_const)
  have hTo : IsOpen Tt := isOpen_lt continuous_const continuous_norm
  have hAsub : A ⊆ unitDiscExterior := fun w hw => hw.1
  have hTsub : Tt ⊆ unitDiscExterior := fun w (hw : R < ‖w‖) => show 1 < ‖w‖ by linarith
  have hU : unitDiscExterior = A ∪ Tt := by
    ext w
    show 1 < ‖w‖ ↔ (1 < ‖w‖ ∧ ‖w‖ ≤ R) ∨ R < ‖w‖
    constructor
    · intro h
      by_cases hw : ‖w‖ ≤ R
      · exact Or.inl ⟨h, hw⟩
      · exact Or.inr (not_le.mp hw)
    · rintro (⟨h, -⟩ | h)
      · exact h
      · linarith
  have hdisj : Disjoint A Tt := Set.disjoint_left.mpr fun w hA hT => by
    have h1 : ‖w‖ ≤ R := hA.2
    have h2 : R < ‖w‖ := hT
    linarith
  have hsplit : ∀ F : ℂ → ℂ, IntegrableOn F unitDiscExterior →
      (∫ w in unitDiscExterior, F w) = (∫ w in A, F w) + ∫ w in Tt, F w := fun F hF => by
    rw [hU] at hF ⊢
    exact setIntegral_union hdisj hTo.measurableSet (hF.mono_set subset_union_left)
      (hF.mono_set subset_union_right)
  -- the tail estimate
  have htail : ∀ (Fk : ℂ → ℂ) (Fp : ℂ → ℂ), ContinuousOn Fk unitDiscExterior →
      ContinuousOn Fp unitDiscExterior →
      (∫⁻ w in Tt, ‖Fk w‖ₑ ^ 2) ≤ ENNReal.ofReal (Kc / D ^ 2) →
      (∫⁻ w in unitDiscExterior, ‖Fp w‖ₑ ^ 2) ≤ Mtot →
      ‖∫ w in Tt, Fk w * Fp w‖ ≤ ε := by
    intro Fk Fp hk hp hkb hpb
    refine (norm_integral_le_lintegral_norm _).trans (ENNReal.toReal_le_of_le_ofReal hε.le ?_)
    simp only [ofReal_norm]
    refine (s36l_cs ((hk.mono hTsub).aestronglyMeasurable hTo.measurableSet)
      ((hp.mono hTsub).aestronglyMeasurable hTo.measurableSet)).trans ?_
    have hpb' : (∫⁻ w in Tt, ‖Fp w‖ₑ ^ 2) ≤ ENNReal.ofReal Mr :=
      ((lintegral_mono_set hTsub).trans hpb).trans hMtotr.le
    calc (∫⁻ w in Tt, ‖Fk w‖ₑ ^ 2) ^ (1 / 2 : ℝ) * (∫⁻ w in Tt, ‖Fp w‖ₑ ^ 2) ^ (1 / 2 : ℝ)
        ≤ ENNReal.ofReal (Kc / D ^ 2) ^ (1 / 2 : ℝ) * ENNReal.ofReal Mr ^ (1 / 2 : ℝ) := by
          gcongr
      _ = ENNReal.ofReal ((Kc / D ^ 2 * Mr) ^ (1 / 2 : ℝ)) := by
          rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num),
            ENNReal.ofReal_rpow_of_nonneg hMr0 (by norm_num), ← ENNReal.ofReal_mul (by positivity),
            Real.mul_rpow (by positivity) hMr0]
      _ ≤ ENNReal.ofReal ((ε ^ 2) ^ (1 / 2 : ℝ)) := by
          gcongr
      _ = ENNReal.ofReal ε := by
          rw [← Real.sqrt_eq_rpow, Real.sqrt_sq hε.le]
  have hrowT : ∀ (f₁ g₁ : ℂ → ℂ), DifferentiableOn ℂ g₁ unitDiscExterior → InjOn g₁ unitDiscExterior →
      ‖deriv f₁ z‖ ≤ ‖deriv f z‖ + 1 → (∀ w ∈ Tt, D ≤ ‖g₁ w - f₁ z‖) →
      (∫⁻ w in Tt, ‖kerK2 f₁ g₁ z w‖ₑ ^ 2) ≤ ENNReal.ofReal (Kc / D ^ 2) := by
    intro f₁ g₁ hd hi hf1 hDs
    refine (s36l_K2row_bound hTo (hd.mono hTsub) (hi.mono hTsub) hD0 hDs).trans ?_
    rw [← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [hKc]
    have h1 : ‖deriv f₁ z‖ ^ 2 ≤ (‖deriv f z‖ + 1) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hf1 2
    have h2 : ‖deriv f₁ z‖ ^ 2 / π ^ 2 * (π / D ^ 2) ≤ (‖deriv f z‖ + 1) ^ 2 / π ^ 2 * (π / D ^ 2) := by
      gcongr
    calc _ ≤ _ := h2
      _ = (‖deriv f z‖ + 1) ^ 2 / π ^ 2 * π / D ^ 2 := by ring
  refine ⟨fun n => ∫ w in A, kerK2 (fsans (κn n)) (gsans (κn n)) z w * conj (-preSchwarzian (gsans (κn n)) w),
    ∫ w in A, kerK2 f g z w * conj (-preSchwarzian g w), ?_, ?_, ?_⟩
  · -- Vitali on the annulus `1 < |w| ≤ R`
    have hAfin : IsFiniteMeasure (volume.restrict A) := ⟨by
      rw [Measure.restrict_apply_univ]
      exact (measure_mono fun w (hw : w ∈ A) => mem_closedBall_zero_iff.mpr hw.2).trans_lt
        measure_closedBall_lt_top⟩
    have hV := s36l_vitali_pair (μ := volume.restrict A)
      (a := fun n w => conj (-preSchwarzian (gsans (κn n)) w))
      (b := fun n w => kerK2 (fsans (κn n)) (gsans (κn n)) z w)
      (A := fun w => conj (-preSchwarzian g w)) (B := fun w => kerK2 f g z w) hMt.ne
      (fun n => ((hcPn n).mono hAsub).aestronglyMeasurable hAm)
      (fun n => ((hcKn n).mono hAsub).aestronglyMeasurable hAm)
      (fun n => (lintegral_mono_set hAsub).trans (hPn n))
      (fun n => ne_top_of_le_ne_top (s36l_K2row_L2 (hmem n) hz) (lintegral_mono_set hAsub)) ?_ ?_ ?_
    · have e : ∀ (u v : ℂ → ℂ), (∫ w in A, u w * v w) = ∫ w in A, v w * u w := fun u v =>
        integral_congr_ae (Eventually.of_forall fun w => mul_comm _ _)
      rw [e] at hV
      exact hV.congr fun n => e _ _
    · -- uniform square-integrability of the kernel rows
      refine s36l_ui_eventually
        (fun n => ne_top_of_le_ne_top (s36l_K2row_L2 (hmem n) hz) (lintegral_mono_set hAsub)) ?_
      intro ε' hε'
      set ε'' : ℝ≥0∞ := ε' / 2 with hε''
      have hε''0 : ε'' ≠ 0 := (ENNReal.half_pos hε'.ne').ne'
      have hK1t : ENNReal.ofReal (K1 ^ 2) ≠ 0 := (ENNReal.ofReal_pos.mpr (by positivity)).ne'
      obtain ⟨δt, hδt, hevt⟩ := hgt (ε'' / ENNReal.ofReal (K1 ^ 2))
        (ENNReal.div_pos hε''0 ENNReal.ofReal_ne_top)
      -- the compact part `1 + δt ≤ |w| ≤ R`
      set Kc' : Set ℂ := closedBall (0 : ℂ) R ∩ {w : ℂ | 1 + δt ≤ ‖w‖} with hKc'
      have hKcc : IsCompact Kc' := (isCompact_closedBall 0 R).inter_right (isClosed_le continuous_const continuous_norm)
      have hKsub : Kc' ⊆ unitDiscExterior := fun w hw => show 1 < ‖w‖ by linarith [hw.2.out]
      have hgdc : ContinuousOn (deriv g) Kc' := ((hgd.analyticOnNhd hEo).deriv.continuousOn).mono hKsub
      obtain ⟨Bg, hBg⟩ := hKcc.exists_bound_of_continuousOn hgdc
      set B : ℝ := max Bg 0 + 1 with hB
      have hBp : 0 < B := by positivity
      have hUd := (tendstoLocallyUniformlyOn_iff_forall_isCompact hEo).mp
        (hgc.deriv (Eventually.of_forall hgnd) hEo) Kc' hKsub hKcc
      have hevd := Metric.tendstoUniformlyOn_iff.mp hUd 1 one_pos
      have hKB : ENNReal.ofReal ((K1 * B) ^ 2) ≠ 0 := (ENNReal.ofReal_pos.mpr (by positivity)).ne'
      refine ⟨ε'' / ENNReal.ofReal ((K1 * B) ^ 2), ENNReal.div_pos hε''0 ENNReal.ofReal_ne_top, ?_⟩
      obtain ⟨N, hN⟩ := eventually_atTop.mp ((hN0.and hevt).and hevd)
      refine ⟨N, fun n hn s hs hμs => ?_⟩
      obtain ⟨⟨⟨hn1, hn2, -⟩, hnt⟩, hnd⟩ := hN n hn
      have hkb := hkerb n hn2 (hsepn n hn1)
      set near : Set ℂ := {w : ℂ | 1 < ‖w‖ ∧ ‖w‖ < 1 + δt} with hnear
      have hnearm : MeasurableSet near :=
        (measurableSet_lt measurable_const measurable_norm).inter (measurableSet_lt measurable_norm measurable_const)
      have hpt : ∀ w ∈ A, ‖kerK2 (fsans (κn n)) (gsans (κn n)) z w‖ₑ ^ 2 ≤
          ENNReal.ofReal (K1 ^ 2) * near.indicator (fun w => ‖deriv (gsans (κn n)) w‖ₑ ^ 2) w +
            ENNReal.ofReal ((K1 * B) ^ 2) := by
        intro w hw
        have hwE := hAsub hw
        have h1 := hkb w hwE
        by_cases hwn : w ∈ near
        · rw [indicator_of_mem hwn]
          refine le_add_right ?_
          exact s36l_enorm_sq_le (x := kerK2 _ _ z w) (y := deriv (gsans (κn n)) w) hK1p.le h1
        · have hwK : w ∈ Kc' := ⟨mem_closedBall_zero_iff.mpr hw.2, by
            have : ¬ (1 < ‖w‖ ∧ ‖w‖ < 1 + δt) := hwn
            push_neg at this
            exact this hw.1⟩
          have hd1 := hnd w hwK
          rw [dist_eq_norm] at hd1
          have hgB : ‖deriv (gsans (κn n)) w‖ ≤ B := by
            have h3 := hBg w hwK
            rw [hB]
            have : ‖deriv (gsans (κn n)) w‖ ≤ ‖deriv g w‖ + 1 := by
              have h4 := norm_sub_norm_le (deriv (gsans (κn n)) w) (deriv g w)
              rw [norm_sub_rev] at hd1
              have h5 : ‖deriv (gsans (κn n)) w - deriv g w‖ < 1 := by
                exact hd1
              linarith
            linarith [le_max_left Bg 0]
          rw [indicator_of_notMem hwn, mul_zero, zero_add]
          have h6 : ‖kerK2 (fsans (κn n)) (gsans (κn n)) z w‖ ≤ K1 * B * ‖(1 : ℂ)‖ := by
            rw [norm_one, mul_one]
            exact h1.trans (mul_le_mul_of_nonneg_left hgB hK1p.le)
          have h7 := s36l_enorm_sq_le (by positivity : (0 : ℝ) ≤ K1 * B) h6
          rwa [enorm_one, one_pow, mul_one] at h7
      calc (∫⁻ w in s, ‖kerK2 (fsans (κn n)) (gsans (κn n)) z w‖ₑ ^ 2 ∂(volume.restrict A))
          ≤ ∫⁻ w in s, (ENNReal.ofReal (K1 ^ 2) * near.indicator (fun w => ‖deriv (gsans (κn n)) w‖ₑ ^ 2) w +
              ENNReal.ofReal ((K1 * B) ^ 2)) ∂(volume.restrict A) := by
            refine lintegral_mono_ae ?_
            filter_upwards [ae_restrict_of_ae (ae_restrict_mem hAm)] with w hw
            exact hpt w hw
        _ = (∫⁻ w in s, ENNReal.ofReal (K1 ^ 2) *
              near.indicator (fun w => ‖deriv (gsans (κn n)) w‖ₑ ^ 2) w ∂(volume.restrict A)) +
              ENNReal.ofReal ((K1 * B) ^ 2) * (volume.restrict A) s := by
            rw [lintegral_add_right _ measurable_const, setLIntegral_const]
        _ ≤ ENNReal.ofReal (K1 ^ 2) * (ε'' / ENNReal.ofReal (K1 ^ 2)) +
              ENNReal.ofReal ((K1 * B) ^ 2) * (ε'' / ENNReal.ofReal ((K1 * B) ^ 2)) := by
            gcongr
            rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
            gcongr
            calc (∫⁻ w in s, near.indicator (fun w => ‖deriv (gsans (κn n)) w‖ₑ ^ 2) w ∂(volume.restrict A))
                ≤ ∫⁻ w, near.indicator (fun w => ‖deriv (gsans (κn n)) w‖ₑ ^ 2) w :=
                  lintegral_mono' (Measure.restrict_le_self.trans Measure.restrict_le_self) le_rfl
              _ = ∫⁻ w in near, ‖deriv (gsans (κn n)) w‖ₑ ^ 2 := lintegral_indicator hnearm _
              _ ≤ ε'' / ENNReal.ofReal (K1 ^ 2) := by
                  simpa only [enorm_eq_nnnorm] using hnt
        _ ≤ ε'' + ε'' := add_le_add ENNReal.mul_div_le ENNReal.mul_div_le
        _ = ε' := ENNReal.add_halves ε'
    · exact s36l_int_mul ((hcP0.mono hAsub).aestronglyMeasurable hAm) ((hcK0.mono hAsub).aestronglyMeasurable hAm)
        (ne_top_of_le_ne_top hMtott ((lintegral_mono_set hAsub).trans hP0))
        (ne_top_of_le_ne_top (s36l_K2row_L2 hκ hz) (lintegral_mono_set hAsub))
    · filter_upwards [ae_restrict_mem hAm] with w hw
      have hwE := hAsub hw
      obtain ⟨hg0, hg1, hg2⟩ := s36l_gconv_pt hgc hgnd hwE
      have hfg : f z - g w ≠ 0 := by
        intro h
        have := hsep w hwE
        rw [norm_sub_rev, h, norm_zero] at this
        linarith
      have hP := (Complex.continuous_conj.tendsto _).comp ((hg2.div hg1 (hgd' w hwE)).neg)
      have hK := (tendsto_const_nhds (x := (1 / (π : ℂ)))).mul
        ((hfdt.mul hg1).div ((hfzt.sub hg0).pow 2) (pow_ne_zero 2 hfg))
      exact hP.mul hK
  · -- the tail of `𝗀ₙ`
    filter_upwards [hN0, hfarN] with n hn hfn
    rw [hsplit _ (hFint n), add_sub_cancel_left]
    refine htail _ _ (hcKn n) (hcPn n) ?_ (hPn' n)
    refine hrowT _ _ (hgnd n) (hgni n) hn.2.1 fun w (hw : R < ‖w‖) => ?_
    have h1 := hfn w hw.le
    have h2 := norm_sub_norm_le (gsans (κn n) w) (fsans (κn n) z)
    linarith [hn.2.2]
  · -- the tail of `𝗀`
    rw [hsplit _ hFint0, add_sub_cancel_left]
    refine htail _ _ hcK0 hcP0 ?_ hP0
    refine hrowT _ _ hgd hgi (by linarith) fun w (hw : R < ‖w‖) => ?_
    have h1 := hfar0 w hw.le
    have h2 := norm_sub_norm_le (g w) (f z)
    linarith

/-! ### Assembly -/

/-- The value of a kernel pairing on `𝔻*` only depends on `g` on `𝔻*` (open). -/
theorem s36l_K2_congr {f g G : ℂ → ℂ} (h : EqOn G g unitDiscExterior) (z : ℂ) :
    (∫ w in unitDiscExterior, kerK2 f G z w * conj (-preSchwarzian G w)) =
      ∫ w in unitDiscExterior, kerK2 f g z w * conj (-preSchwarzian g w) := by
  refine setIntegral_congr_fun (isOpen_lt continuous_const continuous_norm).measurableSet fun w hw => ?_
  have hev : G =ᶠ[𝓝 w] g := by
    filter_upwards [(isOpen_lt continuous_const continuous_norm : IsOpen unitDiscExterior).mem_nhds hw] with u hu
    exact h hu
  have hp : preSchwarzian G w = preSchwarzian g w := by
    unfold preSchwarzian
    rw [hev.deriv.deriv_eq, hev.deriv_eq]
  simp only [kerK2, hev.deriv_eq, h hw, hp]

/-- **Lemma 3.6 in the `(𝖿, 𝗀)` model** (TT:4962–5154; Remark 3.10, `K₁v̄₁ + K₂v̄₂ = -u₁` on `𝔻 \ {0}`). -/
theorem s36l_core {κ : LinfStar} (hκ : κ ∈ LinfStarBall) (hκT : Phi ⟨κ, hκ⟩ ∈ T01) {z : ℂ}
    (hz : z ∈ unitDisc) (hz0 : z ≠ 0) :
    (∫ w in unitDisc, kerK1 (fsans κ) z w * conj (preSchwarzian (fsans κ) w)) +
        (∫ w in unitDiscExterior, kerK2 (fsans κ) (gsans κ) z w * conj (-preSchwarzian (gsans κ) w)) =
      -(preSchwarzian (fsans κ) z - 2 * deriv (fsans κ) z / fsans κ z + 2 / z) := by
  obtain ⟨ρ, hρ, hρl, hae⟩ := s36l_dil_seq κ
  have hT := s36l_dil_mem hκ hκT ρ hρ
  have hV := s36l_dil_vanish κ ρ hρ
  obtain ⟨c, -, hf⟩ := s36l_dil_fsans hκ ρ hρ hρl hae
  have h1 := s36l_lhs_tendsto hκ hz hz0 ρ hρ hρl hae
  have h2 := s36l_K1_tendsto hκ hκT hz ρ hρ hρl hae
  have h3 := s36l_K2_tendsto hκ hκT hz ρ hρ hρl hae
  dsimp only at hT hV hf h1 h2 h3
  refine tendsto_nhds_unique ((h2.add h3).congr' (Eventually.of_forall fun n => ?_)) h1
  obtain ⟨hn, -⟩ := hT n
  have hρ1 : 1 < 1 / ρ n := by rw [one_div]; exact (one_lt_inv₀ (hρ n).1).mpr (hρ n).2
  obtain ⟨⟨R', hR', hfd, hfi⟩, r, hr, G, hGg, hGd, hGi⟩ := s36l_reflect hn hρ1 (hV n)
  obtain ⟨hcomp, hinf⟩ := s36l_complement hn
  have hf0 := (s2c_facts hn).2.2.1
  have hGinf : Tendsto G (cocompact ℂ) (cocompact ℂ) := by
    refine hinf.congr' ?_
    filter_upwards [(isCompact_closedBall (0 : ℂ) 1).compl_mem_cocompact] with w hw
    simp only [mem_compl_iff, mem_closedBall, dist_zero_right, not_le] at hw
    exact (hGg hw).symm
  have hGc : G '' unitDiscExterior = _ := (hGg.image_eq).trans hcomp
  have hs := s36l_smooth_pair hR' hr hfd hfi hf0 hGd hGi hGinf hGc hz hz0
  rw [s36l_K2_congr hGg] at hs
  exact hs

/-- Reflection `u ↦ ū` preserves area integrals over a reflection-invariant set. -/
theorem s36l_conj_integral {D : Set ℂ} (hD : MeasurableSet D) (hconj : ∀ z, conj z ∈ D ↔ z ∈ D)
    (Φ : ℂ → ℂ) : (∫ u in D, Φ (conj u)) = ∫ u in D, Φ u := by
  have he : (fun z : ℂ => conj z) ⁻¹' D = D := Set.ext hconj
  have hm : MeasurePreserving (fun z : ℂ => conj z) (volume.restrict D) (volume.restrict D) := by
    have hm := Complex.conjLIE.measurePreserving.restrict_preimage hD
    change MeasurePreserving (fun z : ℂ => conj z)
      (volume.restrict ((fun z : ℂ => conj z) ⁻¹' D)) (volume.restrict D) at hm
    rwa [he] at hm
  exact hm.integral_comp Complex.conjLIE.toHomeomorph.measurableEmbedding Φ

/-- Transfer of `s36l_core` for `ν⁻¹` (at `z̄`) to the `(f̃, g̃)` model of Lemma 3.6 for `ν`: `s3pk_gTilde_pair`,
`s3pk_fTilde_pair` (conjugation and the common scale `𝗀'(∞)`), `s3pk_lemma_3_6_rhs`. -/
theorem s36l_transfer {ν : LinfStar} (hν : ν ∈ LinfStarBall) {z : ℂ} (hz : z ∈ unitDisc) (hz0 : z ≠ 0)
    (h : (∫ w in unitDisc, kerK1 (fsans (beltramiInv ν)) (conj z) w *
          conj (preSchwarzian (fsans (beltramiInv ν)) w)) +
        (∫ w in unitDiscExterior, kerK2 (fsans (beltramiInv ν)) (gsans (beltramiInv ν)) (conj z) w *
          conj (-preSchwarzian (gsans (beltramiInv ν)) w)) =
      -(preSchwarzian (fsans (beltramiInv ν)) (conj z) -
          2 * deriv (fsans (beltramiInv ν)) (conj z) / fsans (beltramiInv ν) (conj z) + 2 / conj z)) :
    preSchwarzian (gTilde ν) z - 2 * deriv (gTilde ν) z / gTilde ν z + 2 / z =
      1 / π * (∫ w in unitDiscExterior, deriv (gTilde ν) z * deriv (fTilde ν) w / (gTilde ν z - fTilde ν w) ^ 2 *
          conj (preSchwarzian (fTilde ν) w)) +
        1 / π * ∫ w in unitDisc,
          (deriv (gTilde ν) z * deriv (gTilde ν) w / (gTilde ν z - gTilde ν w) ^ 2 - 1 / (z - w) ^ 2) *
            conj (preSchwarzian (gTilde ν) w) := by
  set ν' := beltramiInv ν with hν'
  set F := fsans ν' with hF
  set G := gsans ν' with hG
  obtain ⟨c, hc0, hcd, -⟩ := s2c_gTilde_facts hν
  have hD : IsOpen unitDisc := isOpen_ball
  have hE : IsOpen unitDiscExterior := isOpen_lt continuous_const continuous_norm
  have hgp := s3pk_gTilde_pair hν
  have hfp := s3pk_fTilde_pair hν
  rw [hcd] at hgp hfp
  -- values and derivatives of the tilde pair
  have hgv : ∀ x ∈ unitDisc, gTilde ν x = c⁻¹ * conj (F (conj x)) := fun x hx => by
    have := hgp hx; simp only at this; rw [this]; field_simp
  have hfv : ∀ x ∈ unitDiscExterior, fTilde ν x = c⁻¹ * conj (G (conj x)) := fun x hx => by
    have := hfp hx; simp only at this; rw [this]; field_simp
  have hgd : ∀ x ∈ unitDisc, deriv (gTilde ν) x = c⁻¹ * conj (deriv F (conj x)) := by
    intro x hx
    have h1 := (hgp.deriv hD) hx
    rw [s2c_conj_deriv, deriv_const_mul_field'] at h1
    rw [h1]; field_simp
  have hfd : ∀ x ∈ unitDiscExterior, deriv (fTilde ν) x = c⁻¹ * conj (deriv G (conj x)) := by
    intro x hx
    have h1 := (hfp.deriv hE) hx
    rw [s2c_conj_deriv, deriv_const_mul_field'] at h1
    rw [h1]; field_simp
  have hgA := s3pk_pre_gTilde hν
  have hfA := s3pk_pre_fTilde hν
  -- the exterior term
  have hT2 : (∫ w in unitDiscExterior, deriv (gTilde ν) z * deriv (fTilde ν) w / (gTilde ν z - fTilde ν w) ^ 2 *
      conj (preSchwarzian (fTilde ν) w)) =
      conj ((π : ℂ) * ∫ w in unitDiscExterior, kerK2 F G (conj z) w * conj (preSchwarzian G w)) := by
    conv_rhs => rw [← integral_const_mul, ← integral_conj, ← s36l_conj_integral hE.measurableSet
      (fun w => s3pk_conj_exterior)]
    refine setIntegral_congr_fun hE.measurableSet fun w hw => ?_
    rw [hgd z hz, hfd w hw, hgv z hz, hfv w hw, hfA hw, kerK2]
    simp only [map_mul, map_div₀, map_pow, map_sub, Complex.conj_conj, map_one, Complex.conj_ofReal]
    field_simp
    ring
  -- the disc term (off the diagonal)
  have hT1 : (∫ w in unitDisc, (deriv (gTilde ν) z * deriv (gTilde ν) w / (gTilde ν z - gTilde ν w) ^ 2 -
      1 / (z - w) ^ 2) * conj (preSchwarzian (gTilde ν) w)) =
      conj (-(π : ℂ) * ∫ w in unitDisc, kerK1 F (conj z) w * conj (preSchwarzian F w)) := by
    conv_rhs => rw [← integral_const_mul, ← integral_conj, ← s36l_conj_integral hD.measurableSet
      (fun w => s3pk_conj_disc)]
    refine setIntegral_congr_ae hD.measurableSet ?_
    filter_upwards [(volume : Measure ℂ).ae_ne z] with w hwz hw
    have hzw : conj z ≠ conj w := fun h =>
      hwz ((Complex.conj_conj w).symm.trans ((congrArg conj h).symm.trans (Complex.conj_conj z)))
    rw [hgd z hz, hgd w hw, hgv z hz, hgv w hw, hgA hw, kerK1_of_ne F hzw]
    simp only [map_mul, map_div₀, map_pow, map_sub, map_neg, Complex.conj_conj, map_one, Complex.conj_ofReal]
    field_simp
    ring
  rw [hT1, hT2, hgv z hz, hgd z hz, hgA hz]
  have hcore : (∫ w in unitDisc, kerK1 F (conj z) w * conj (preSchwarzian F w)) =
      -(preSchwarzian F (conj z) - 2 * deriv F (conj z) / F (conj z) + 2 / conj z) -
        ∫ w in unitDiscExterior, kerK2 F G (conj z) w * conj (-preSchwarzian G w) := by
    rw [← h]; ring
  have hneg : (∫ w in unitDiscExterior, kerK2 F G (conj z) w * conj (-preSchwarzian G w)) =
      -∫ w in unitDiscExterior, kerK2 F G (conj z) w * conj (preSchwarzian G w) := by
    rw [← integral_neg]; congr 1; funext w; simp [map_neg]
  rw [hcore, hneg]
  have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  simp only [map_mul, map_neg, map_sub, map_add, map_div₀, Complex.conj_conj, Complex.conj_ofReal, map_ofNat]
  field_simp
  ring

/-- The inverse of a point of `T₀(1)` is in `T₀(1)` (`lemma_3_4`, Ch. 1), at the level of representatives. -/
theorem s36l_inv_T01 {ν : LinfStar} (hν : ν ∈ LinfStarBall) (hνT : Phi ⟨ν, hν⟩ ∈ T01) :
    ∃ h : beltramiInv ν ∈ LinfStarBall, Phi ⟨beltramiInv ν, h⟩ ∈ T01 := by
  refine ⟨grp_inv_mem hν, ?_⟩
  rw [← gtp_invT_phi ⟨ν, hν⟩]
  exact _root_.TakhtajanTeo.lemma_3_4.2.2 _ hνT

/-- **Lemma 3.6** (TT:4962–5154), in the model `T(1) ≃ L∞(𝔻)₁/∼`, i.e. for the pair `(f̃^μ, g̃_μ)` of `[μ] ∈ T₀(1)`
(misprint corrected, see the module docstring). For `z ∈ 𝔻`, `z ≠ 0`:
`𝒜(g)(z) - 2g'(z)/g(z) + 2/z = (1/π) ∬_{𝔻*} g'(z)f'(w)/(g(z) - f(w))² \overline{𝒜(f)(w)} d²w
  + (1/π) ∬_𝔻 (g'(z)g'(w)/(g(z) - g(w))² - 1/(z - w)²) \overline{𝒜(g)(w)} d²w`. -/
theorem s36l_lemma_3_6 {p : T1} (hp : p ∈ T01) {z : ℂ} (hz : z ∈ unitDisc) (hz0 : z ≠ 0) :
    let μ : LinfStar := (Quotient.out p : LinfStarBall)
    let f := fTilde μ
    let g := gTilde μ
    preSchwarzian g z - 2 * deriv g z / g z + 2 / z =
      1 / π * (∫ w in unitDiscExterior, deriv g z * deriv f w / (g z - f w) ^ 2 * conj (preSchwarzian f w)) +
        1 / π * ∫ w in unitDisc,
          (deriv g z * deriv g w / (g z - g w) ^ 2 - 1 / (z - w) ^ 2) * conj (preSchwarzian g w) := by
  intro μ f g
  have hμ : μ ∈ LinfStarBall := (Quotient.out p).2
  have hμT : Phi ⟨μ, hμ⟩ ∈ T01 := by
    rw [show Phi ⟨μ, hμ⟩ = p from Quotient.out_eq p]
    exact hp
  obtain ⟨hi, hiT⟩ := s36l_inv_T01 hμ hμT
  have hzc : conj z ∈ unitDisc := s3pk_conj_disc.mpr (by simpa using hz)
  have hzc0 : conj z ≠ 0 := by simpa using hz0
  exact s36l_transfer hμ hz hz0 (s36l_core hi hiT hzc hzc0)

/-- **Lemma 3.6** (TT:4962–5154), in the model `T(1) ≃ L∞(𝔻)₁/∼`, i.e. for the pair `(f̃^μ, g̃_μ)` of `[μ] ∈ T₀(1)`
(misprint corrected, see the module docstring). For `z ∈ 𝔻`, `z ≠ 0`:
`𝒜(g)(z) - 2g'(z)/g(z) + 2/z = (1/π) ∬_{𝔻*} g'(z)f'(w)/(g(z) - f(w))² \overline{𝒜(f)(w)} d²w
  + (1/π) ∬_𝔻 (g'(z)g'(w)/(g(z) - g(w))² - 1/(z - w)²) \overline{𝒜(g)(w)} d²w`. -/
theorem lemma_3_6 {p : T1} (hp : p ∈ T01) {z : ℂ} (hz : z ∈ unitDisc) (hz0 : z ≠ 0) :
    let μ : LinfStar := (Quotient.out p : LinfStarBall)
    let f := fTilde μ
    let g := gTilde μ
    preSchwarzian g z - 2 * deriv g z / g z + 2 / z =
      1 / π * (∫ w in unitDiscExterior, deriv g z * deriv f w / (g z - f w) ^ 2 * conj (preSchwarzian f w)) +
        1 / π * ∫ w in unitDisc,
          (deriv g z * deriv g w / (g z - g w) ^ 2 - 1 / (z - w) ^ 2) * conj (preSchwarzian g w) := by
  exact s36l_lemma_3_6 hp hz hz0

end TakhtajanTeo.Ch2
