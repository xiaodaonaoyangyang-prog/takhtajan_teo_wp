import TakhtajanTeo.Ch2.S4GFirstVariation
import TakhtajanTeo.Ch1.AhlforsWeillCompleted
import TakhtajanTeo.Ch1.QCVariationSurjSmall
import TakhtajanTeo.Ch1.S5ExteriorChartRegularity
import TakhtajanTeo.Ch1.S5Thm53Curve
import TakhtajanTeo.Ch2.S5_Embedding
import TakhtajanTeo.Appendix.AppACont

/-!
# S3GDom: the Schauder core `s3d_g_dom` by analytic welding (Program G, 下属3, route (iii), prefix `s3g_`)

Sub-interface for `s3d_g_dom` (S3Density_IFACE fa90ef38). Families are indexed by `t` near `0`; "C¹ family" means
`ContDiffOn ℝ 1` of `(t, z) ↦ X t z`, "holomorphic injective" is in `z` for each `t`. With `f_ν = fB ν` on `𝔻`,
`g_ν = gMu ν` on `𝔻*` and the welding `h_ν = w^A_ν` on `𝕊¹` (`g_ν ∘ h_ν = f_ν` there):

* (a) `s3g_aw_extend`: for polynomial `ψ_a, ψ_m` (Ahlfors–Weill: `bersPhi (Λ ψ) = ψ`, `qs_AW`), `f_{Λ(ψ_a + t ψ_m)}`
  extends holomorphically and injectively to a disc `|z| < R`, `R > 1`, as a C¹ family (rescaled AW on `|z| < R` plus
  uniqueness of solutions of `𝒮 f = ψ` up to Möbius);
* (b) `s3g_weld_of_ext`: if `f_{ν_t}` extends across `𝕊¹` (C¹ family), then so does `g_{ν_t}` and the welding
  `h_{ν_t}` has a holomorphic injective extension to an annulus (C¹ families): `Φ = f⁻¹ ∘ g` has modulus `1` on `𝕊¹`
  and extends by reflection (`schwarz_reflection_arc_norm_one`);
* (b′) `s3g_ext_of_weld`: conversely, an annulus extension of the welding gives an extension of `f` across `𝕊¹`
  (`f = g ∘ H` outside, continuity across `𝕊¹`, removability of the circle);
* (c) `s3g_weld_mul`: welding extensions compose along `w^A_{μ * κ} = w^A_μ ∘ w^A_κ` (`grp_wAS_mul`);
* (d) `s3g_dom_of_ext`: a C¹ family of extensions of `g_{ν_t}` across `𝕊¹` (plus holomorphy of `t ↦ ν_t`) gives the
  `L²(𝔻*)` domination of `𝒜(g_t)` and of its `t`-derivative (compact collar + GAN-type joint analyticity on `𝔻*` +
  the chart at `∞`).

Assembly of `s3d_g_dom` (statement byte-identical to the master interface): induction along the `D`-chain (each
factor a constant family through (a), (b), (c); base `wA 0 = id`), then the line factor `a + t m = Λ(ψ_a + t ψ_m)`
through (a), (b), (c) with `κ`, then (b′), (b), (d).
-/

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal ComplexConjugate Classical Real

noncomputable section

namespace TakhtajanTeo.Ch2

open LiZhongQC

/-! ### Annuli around the unit circle (下属3) -/

/-- Every open neighbourhood of `𝕊¹` contains a round annulus `1 - ε < |z| < 1 + ε`. -/
theorem s3g_annulus_sub {U : Set ℂ} (hU : IsOpen U) (hcU : unitCircle ⊆ U) :
    ∃ ε > 0, ε < 1 ∧ {z : ℂ | 1 - ε < ‖z‖ ∧ ‖z‖ < 1 + ε} ⊆ U := by
  have hc : IsCompact unitCircle := by
    have he : unitCircle = sphere (0 : ℂ) 1 := by
      ext z
      simp [unitCircle]
    rw [he]
    exact isCompact_sphere 0 1
  obtain ⟨δ, hδ, hδU⟩ := hc.exists_thickening_subset_open hU hcU
  have hm1 := min_le_left δ (1 / 2)
  have hm2 := min_le_right δ (1 / 2)
  refine ⟨min δ (1 / 2), lt_min hδ (by norm_num), hm2.trans_lt (by norm_num), fun z hz => hδU ?_⟩
  obtain ⟨hz1, hz2⟩ := hz
  have hr : (0 : ℝ) < ‖z‖ := by linarith
  have hz0 : z ≠ 0 := norm_pos_iff.1 hr
  have hrc : (‖z‖ : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  rw [mem_thickening_iff]
  refine ⟨z / (‖z‖ : ℂ), ?_, ?_⟩
  · show ‖z / (‖z‖ : ℂ)‖ = 1
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr, div_self hr.ne']
  · have he : z - z / (‖z‖ : ℂ) = ((‖z‖ - 1 : ℝ) : ℂ) * (z / (‖z‖ : ℂ)) := by
      push_cast
      field_simp
    rw [dist_eq_norm, he, norm_mul, norm_div, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_of_pos hr, div_self hr.ne', mul_one, abs_lt]
    constructor <;> linarith

/-! ### Parametric Cauchy formula (下属3) -/

/-- **Parametric Cauchy formula.** If `(t, z) ↦ F t z` is C¹ on `P × U` and each `F t` is holomorphic on `U`, then
`(t, z) ↦ ∂_z F t z` is C¹ on `P × U` (and each `∂_z F t` is holomorphic): differentiation under the circle integral
`∂_z F t z = (2πi)⁻¹ ∮_{|w - z| = δ} F t w / (w - z)²` of fixed radius, centred at `z`. -/
theorem s3g_param_deriv {P U : Set ℂ} (hP : IsOpen P) (hU : IsOpen U) {F : ℂ → ℂ → ℂ}
    (hF : ContDiffOn ℝ 1 (fun q : ℂ × ℂ => F q.1 q.2) (P ×ˢ U))
    (hFt : ∀ t ∈ P, DifferentiableOn ℂ (F t) U) :
    ContDiffOn ℝ 1 (fun q : ℂ × ℂ => deriv (F q.1) q.2) (P ×ˢ U) ∧
      ∀ t ∈ P, DifferentiableOn ℂ (deriv (F t)) U := by
  refine ⟨?_, fun t ht => (hFt t ht).deriv hU⟩
  have hPU : IsOpen (P ×ˢ U) := hP.prod hU
  have hDc : ContinuousOn (fderiv ℝ (fun q : ℂ × ℂ => F q.1 q.2)) (P ×ˢ U) :=
    hF.continuousOn_fderiv_of_isOpen hPU le_rfl
  have hDd : DifferentiableOn ℝ (fun q : ℂ × ℂ => F q.1 q.2) (P ×ˢ U) := hF.differentiableOn one_ne_zero
  refine contDiffOn_of_locally_contDiffOn fun q₀ hq₀ => ?_
  obtain ⟨ε, hε, hεs⟩ := Metric.isOpen_iff.1 hPU q₀ hq₀
  obtain ⟨δ, hδdef⟩ : ∃ δ : ℝ, δ = ε / 3 := ⟨_, rfl⟩
  have hδ0 : 0 < δ := by rw [hδdef]; positivity
  have hcb : closedBall q₀ (2 * δ) ⊆ P ×ˢ U :=
    (closedBall_subset_ball (by rw [hδdef]; linarith)).trans hεs
  -- points of `{q.1} × closedBall q.2 δ`, `q ∈ ball q₀ δ`, lie in the closed `2δ`-ball
  have hpt : ∀ q ∈ ball q₀ δ, ∀ w : ℂ, dist w q.2 ≤ δ → (q.1, w) ∈ closedBall q₀ (2 * δ) := by
    intro q hq w hw
    rw [mem_ball, Prod.dist_eq, max_lt_iff] at hq
    rw [mem_closedBall, Prod.dist_eq, max_le_iff]
    refine ⟨by linarith [hq.1], ?_⟩
    calc dist w q₀.2 ≤ dist w q.2 + dist q.2 q₀.2 := dist_triangle _ _ _
      _ ≤ 2 * δ := by linarith [hq.2]
  have hen : ∀ θ : ℝ, ‖circleMap 0 δ θ‖ = δ := fun θ => by
    rw [norm_circleMap_zero, abs_of_pos hδ0]
  have hen0 : ∀ θ : ℝ, circleMap 0 δ θ ≠ 0 := fun θ h => by
    have := hen θ
    rw [h, norm_zero] at this
    linarith
  have hsh : ∀ q ∈ ball q₀ δ, ∀ θ : ℝ, (q.1, q.2 + circleMap 0 δ θ) ∈ closedBall q₀ (2 * δ) := by
    intro q hq θ
    refine hpt q hq _ ?_
    rw [dist_eq_norm, add_sub_cancel_left, hen]
  -- the kernel
  obtain ⟨k, hk⟩ : ∃ k : ℝ → ℂ, k = fun θ => (2 * π * I : ℂ)⁻¹ *
      (circleMap 0 δ θ * I * (1 / (circleMap 0 δ θ) ^ 2)) := ⟨_, rfl⟩
  have hkc : Continuous k := by
    rw [hk]
    have hc := continuous_circleMap 0 δ
    exact continuous_const.mul ((hc.mul continuous_const).mul
      (continuous_const.div (hc.pow 2) fun θ => pow_ne_zero 2 (hen0 θ)))
  -- the representation on `ball q₀ δ`
  have hrep : ∀ q ∈ ball q₀ δ,
      deriv (F q.1) q.2 = ∫ θ in (0 : ℝ)..2 * π, k θ * F q.1 (q.2 + circleMap 0 δ θ) := by
    intro q hq
    have hdisc : DifferentiableOn ℂ (F q.1) (closedBall q.2 δ) :=
      (hFt q.1 (hcb (hsh q hq 0)).1).mono fun w hw => (hcb (hpt q hq w hw)).2
    have h := hdisc.deriv_eq_smul_circleIntegral hδ0
    have hπ : (2 * π * I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero, I_ne_zero]
    have h2 : deriv (F q.1) q.2 =
        (2 * π * I : ℂ)⁻¹ * ∮ z in C(q.2, δ), (1 / (z - q.2) ^ 2) • F q.1 z := by
      rw [h, smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hπ, one_mul]
    rw [h2, circleIntegral, ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun θ _ => ?_
    have hcm : circleMap q.2 δ θ = q.2 + circleMap 0 δ θ := by simp [circleMap]
    simp only [deriv_circleMap, hcm, add_sub_cancel_left, smul_eq_mul, hk]
    ring
  -- derivative of the parametric integral
  obtain ⟨M, hM⟩ := (isCompact_closedBall q₀ (2 * δ)).exists_bound_of_continuousOn (hDc.mono hcb)
  obtain ⟨Kb, hKb⟩ :=
    (isCompact_Icc (a := (0 : ℝ)) (b := 2 * π)).exists_bound_of_continuousOn hkc.continuousOn
  have hI : Set.uIoc (0 : ℝ) (2 * π) ⊆ Icc 0 (2 * π) := by
    rw [uIoc_of_le (by positivity)]
    exact Ioc_subset_Icc_self
  obtain ⟨Lp, hLp⟩ : ∃ Lp : ℂ × ℂ →L[ℝ] ℂ × ℂ,
      Lp = (ContinuousLinearMap.fst ℝ ℂ ℂ).prod (ContinuousLinearMap.snd ℝ ℂ ℂ) := ⟨_, rfl⟩
  obtain ⟨L, hL⟩ : ∃ L : ℂ × ℂ → ℝ → ℂ × ℂ →L[ℝ] ℂ, L = fun x θ => (ContinuousLinearMap.mul ℝ ℂ (k θ)).comp
      ((fderiv ℝ (fun q : ℂ × ℂ => F q.1 q.2) (x.1, x.2 + circleMap 0 δ θ)).comp Lp) := ⟨_, rfl⟩
  have hshc : ∀ θ : ℝ, Continuous fun x : ℂ × ℂ => (x.1, x.2 + circleMap 0 δ θ) := fun θ => by fun_prop
  have hdiff : ∀ x ∈ ball q₀ δ, ∀ θ : ℝ,
      HasFDerivAt (fun x : ℂ × ℂ => k θ * F x.1 (x.2 + circleMap 0 δ θ)) (L x θ) x := by
    intro x hx θ
    have hy := hcb (hsh x hx θ)
    have hFx := ((hDd _ hy).differentiableAt (hPU.mem_nhds hy)).hasFDerivAt
    have hs : HasFDerivAt (fun x : ℂ × ℂ => (x.1, x.2 + circleMap 0 δ θ)) Lp x := by
      rw [hLp]
      exact hasFDerivAt_fst.prodMk (hasFDerivAt_snd.add_const _)
    have h1 : HasFDerivAt (fun x : ℂ × ℂ => F x.1 (x.2 + circleMap 0 δ θ))
        ((fderiv ℝ (fun q : ℂ × ℂ => F q.1 q.2) (x.1, x.2 + circleMap 0 δ θ)).comp Lp) x :=
      HasFDerivAt.comp (g := fun q : ℂ × ℂ => F q.1 q.2)
        (f := fun x : ℂ × ℂ => (x.1, x.2 + circleMap 0 δ θ)) x hFx hs
    rw [hL]
    exact HasFDerivAt.comp (g := ⇑(ContinuousLinearMap.mul ℝ ℂ (k θ)))
      (f := fun x : ℂ × ℂ => F x.1 (x.2 + circleMap 0 δ θ)) x
      (ContinuousLinearMap.mul ℝ ℂ (k θ)).hasFDerivAt h1
  have hbound : ∀ x ∈ ball q₀ δ, ∀ θ ∈ Set.uIoc (0 : ℝ) (2 * π), ‖L x θ‖ ≤ Kb * (M * ‖Lp‖) := by
    intro x hx θ hθ
    rw [hL]
    refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
    refine mul_le_mul ?_ ((ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_mul_of_nonneg_right (hM _ (hsh x hx θ)) (norm_nonneg _))) (by positivity)
      ((norm_nonneg _).trans (hKb θ (hI hθ)))
    exact (ContinuousLinearMap.opNorm_mul_apply_le ℝ ℂ (k θ)).trans (hKb θ (hI hθ))
  have hcontθ : ∀ x ∈ ball q₀ δ, Continuous fun θ : ℝ => k θ * F x.1 (x.2 + circleMap 0 δ θ) := by
    intro x hx
    have hc : Continuous fun θ : ℝ => (x.1, x.2 + circleMap 0 δ θ) := by fun_prop
    exact hkc.mul (hF.continuousOn.comp_continuous hc fun θ => hcb (hsh x hx θ))
  have hcontL : ∀ x ∈ ball q₀ δ, Continuous fun θ : ℝ => L x θ := by
    intro x hx
    have hc : Continuous fun θ : ℝ => (x.1, x.2 + circleMap 0 δ θ) := by fun_prop
    rw [hL]
    exact ((ContinuousLinearMap.mul ℝ ℂ).continuous.comp hkc).clm_comp
      ((hDc.comp_continuous hc fun θ => hcb (hsh x hx θ)).clm_comp continuous_const)
  have hderiv : ∀ x ∈ ball q₀ δ, HasFDerivAt
      (fun x : ℂ × ℂ => ∫ θ in (0 : ℝ)..2 * π, k θ * F x.1 (x.2 + circleMap 0 δ θ))
      (∫ θ in (0 : ℝ)..2 * π, L x θ) x := by
    intro x hx
    refine intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le
      (bound := fun _ => Kb * (M * ‖Lp‖)) (isOpen_ball.mem_nhds hx) ?_ ((hcontθ x hx).intervalIntegrable _ _)
      (hcontL x hx).aestronglyMeasurable ?_ intervalIntegrable_const ?_
    · filter_upwards [isOpen_ball.mem_nhds hx] with y hy
      exact (hcontθ y hy).aestronglyMeasurable
    · exact Eventually.of_forall fun θ hθ y hy => hbound y hy θ hθ
    · exact Eventually.of_forall fun θ _ y hy => hdiff y hy θ
  have hcontD : ContinuousOn (fun x : ℂ × ℂ => ∫ θ in (0 : ℝ)..2 * π, L x θ) (ball q₀ δ) := by
    intro x hx
    refine (intervalIntegral.continuousAt_of_dominated_interval (bound := fun _ => Kb * (M * ‖Lp‖)) ?_ ?_
      intervalIntegrable_const ?_).continuousWithinAt
    · filter_upwards [isOpen_ball.mem_nhds hx] with y hy
      exact (hcontL y hy).aestronglyMeasurable
    · filter_upwards [isOpen_ball.mem_nhds hx] with y hy
      exact Eventually.of_forall fun θ hθ => hbound y hy θ hθ
    · refine Eventually.of_forall fun θ _ => ?_
      have hy := hcb (hsh x hx θ)
      rw [hL]
      exact continuousAt_const.clm_comp
        ((ContinuousAt.comp (g := fderiv ℝ (fun q : ℂ × ℂ => F q.1 q.2))
          (f := fun x : ℂ × ℂ => (x.1, x.2 + circleMap 0 δ θ)) (hDc.continuousAt (hPU.mem_nhds hy))
          (hshc θ).continuousAt).clm_comp continuousAt_const)
  have hΨ : ContDiffOn ℝ (0 + 1)
      (fun x : ℂ × ℂ => ∫ θ in (0 : ℝ)..2 * π, k θ * F x.1 (x.2 + circleMap 0 δ θ)) (ball q₀ δ) := by
    rw [contDiffOn_succ_iff_fderiv_of_isOpen isOpen_ball]
    refine ⟨fun x hx => (hderiv x hx).differentiableAt.differentiableWithinAt, fun h => by simp at h, ?_⟩
    rw [contDiffOn_zero]
    exact hcontD.congr fun x hx => (hderiv x hx).fderiv
  rw [zero_add] at hΨ
  refine ⟨ball q₀ δ, isOpen_ball, mem_ball_self hδ0, ?_⟩
  exact (hΨ.mono inter_subset_right).congr fun q hq => hrep q hq.2

/-- **C¹ parametric integrals.** If `x ↦ Φ x θ` has derivative `Φ' x θ` on an open `V ⊆ ℂ × ℂ` for `θ ∈ [a, b]`, with
`Φ`, `Φ'` jointly continuous on `V × [a, b]`, then `x ↦ ∫_a^b Φ x θ dθ` is C¹ on `V`. -/
theorem s3g_param_integral {V : Set (ℂ × ℂ)} (hV : IsOpen V) {a b : ℝ} (hab : a ≤ b) {Φ : ℂ × ℂ → ℝ → ℂ}
    {Φ' : ℂ × ℂ → ℝ → ℂ × ℂ →L[ℝ] ℂ}
    (hd : ∀ x ∈ V, ∀ θ ∈ Icc a b, HasFDerivAt (fun y => Φ y θ) (Φ' x θ) x)
    (hc : ContinuousOn (fun p : (ℂ × ℂ) × ℝ => Φ p.1 p.2) (V ×ˢ Icc a b))
    (hc' : ContinuousOn (fun p : (ℂ × ℂ) × ℝ => Φ' p.1 p.2) (V ×ˢ Icc a b)) :
    ContDiffOn ℝ 1 (fun x => ∫ θ in a..b, Φ x θ) V := by
  have hI : Set.uIoc a b ⊆ Icc a b := by
    rw [uIoc_of_le hab]
    exact Ioc_subset_Icc_self
  refine contDiffOn_of_locally_contDiffOn fun x₀ hx₀ => ?_
  obtain ⟨ε, hε, hεV⟩ := Metric.isOpen_iff.1 hV x₀ hx₀
  have hcb : closedBall x₀ (ε / 2) ⊆ V := (closedBall_subset_ball (by linarith)).trans hεV
  have hK : IsCompact (closedBall x₀ (ε / 2) ×ˢ Icc a b) := (isCompact_closedBall _ _).prod isCompact_Icc
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn (hc'.mono (prod_mono hcb subset_rfl))
  have hb : ∀ x ∈ ball x₀ (ε / 2), ∀ θ ∈ Set.uIoc a b, ‖Φ' x θ‖ ≤ M := fun x hx θ hθ =>
    hM (x, θ) ⟨ball_subset_closedBall hx, hI hθ⟩
  have hxV : ∀ x ∈ ball x₀ (ε / 2), x ∈ V := fun x hx => hcb (ball_subset_closedBall hx)
  have hcθ : ∀ x ∈ V, ContinuousOn (fun θ => Φ x θ) (Icc a b) := fun x hx =>
    hc.comp (continuousOn_const.prodMk continuousOn_id) fun θ hθ => ⟨hx, hθ⟩
  have hcθ' : ∀ x ∈ V, ContinuousOn (fun θ => Φ' x θ) (Icc a b) := fun x hx =>
    hc'.comp (continuousOn_const.prodMk continuousOn_id) fun θ hθ => ⟨hx, hθ⟩
  have hmeas : ∀ x ∈ V, AEStronglyMeasurable (fun θ => Φ x θ) (volume.restrict (Set.uIoc a b)) := fun x hx =>
    ((hcθ x hx).mono hI).aestronglyMeasurable measurableSet_uIoc
  have hmeas' : ∀ x ∈ V, AEStronglyMeasurable (fun θ => Φ' x θ) (volume.restrict (Set.uIoc a b)) := fun x hx =>
    ((hcθ' x hx).mono hI).aestronglyMeasurable measurableSet_uIoc
  have hderiv : ∀ x ∈ ball x₀ (ε / 2), HasFDerivAt (fun y => ∫ θ in a..b, Φ y θ) (∫ θ in a..b, Φ' x θ) x := by
    intro x hx
    refine intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le (bound := fun _ => M)
      (isOpen_ball.mem_nhds hx) ?_ ?_ (hmeas' x (hxV x hx)) ?_ intervalIntegrable_const ?_
    · filter_upwards [isOpen_ball.mem_nhds hx] with y hy
      exact hmeas y (hxV y hy)
    · rw [intervalIntegrable_iff_integrableOn_Icc_of_le hab]
      exact (hcθ x (hxV x hx)).integrableOn_Icc
    · exact Eventually.of_forall fun θ hθ y hy => hb y hy θ hθ
    · exact Eventually.of_forall fun θ hθ y hy => hd y (hxV y hy) θ (hI hθ)
  have hcont : ContinuousOn (fun x => ∫ θ in a..b, Φ' x θ) (ball x₀ (ε / 2)) := by
    intro x hx
    refine (intervalIntegral.continuousAt_of_dominated_interval (bound := fun _ => M) ?_ ?_
      intervalIntegrable_const ?_).continuousWithinAt
    · filter_upwards [isOpen_ball.mem_nhds hx] with y hy
      exact hmeas' y (hxV y hy)
    · filter_upwards [isOpen_ball.mem_nhds hx] with y hy
      exact Eventually.of_forall fun θ hθ => hb y hy θ hθ
    · refine Eventually.of_forall fun θ hθ => ?_
      have hp : (x, θ) ∈ V ×ˢ Icc a b := ⟨hxV x hx, hI hθ⟩
      have hcA : ContinuousWithinAt (fun y : ℂ × ℂ => Φ' y θ) V x :=
        ContinuousWithinAt.comp (g := fun p : (ℂ × ℂ) × ℝ => Φ' p.1 p.2) (f := fun y : ℂ × ℂ => (y, θ))
          (hc'.continuousWithinAt hp) (continuous_id.prodMk continuous_const).continuousWithinAt
          (fun y hy => ⟨hy, hI hθ⟩)
      exact hcA.continuousAt (hV.mem_nhds (hxV x hx))
  have hΨ : ContDiffOn ℝ (0 + 1) (fun x => ∫ θ in a..b, Φ x θ) (ball x₀ (ε / 2)) := by
    rw [contDiffOn_succ_iff_fderiv_of_isOpen isOpen_ball]
    refine ⟨fun x hx => (hderiv x hx).differentiableAt.differentiableWithinAt, fun h => by simp at h, ?_⟩
    rw [contDiffOn_zero]
    exact hcont.congr fun x hx => (hderiv x hx).fderiv
  rw [zero_add] at hΨ
  exact ⟨ball x₀ (ε / 2), isOpen_ball, mem_ball_self (by linarith), hΨ.mono inter_subset_right⟩

/-- **The difference quotient at `0`** of a C¹ family of holomorphic functions on `𝔻` is a C¹ family:
`dslope (H t) 0 u = ∫₀¹ ∂_u H t (s u) ds`. -/
theorem s3g_dslope_param {P : Set ℂ} (hP : IsOpen P) {H : ℂ → ℂ → ℂ}
    (hH : ContDiffOn ℝ 1 (fun q : ℂ × ℂ => H q.1 q.2) (P ×ˢ ball 0 1))
    (hHt : ∀ t ∈ P, DifferentiableOn ℂ (H t) (ball 0 1)) :
    ContDiffOn ℝ 1 (fun q : ℂ × ℂ => dslope (H q.1) 0 q.2) (P ×ˢ ball 0 1) := by
  obtain ⟨hD, -⟩ := s3g_param_deriv hP isOpen_ball hH hHt
  have hV : IsOpen (P ×ˢ ball (0 : ℂ) 1) := hP.prod isOpen_ball
  have hDc : ContinuousOn (fderiv ℝ (fun q : ℂ × ℂ => deriv (H q.1) q.2)) (P ×ˢ ball 0 1) :=
    hD.continuousOn_fderiv_of_isOpen hV le_rfl
  have hDd : DifferentiableOn ℝ (fun q : ℂ × ℂ => deriv (H q.1) q.2) (P ×ˢ ball 0 1) :=
    hD.differentiableOn one_ne_zero
  -- the segment `s ↦ (t, s u)` stays in `P × 𝔻`
  have hseg : ∀ x ∈ P ×ˢ ball (0 : ℂ) 1, ∀ s ∈ Icc (0 : ℝ) 1, (x.1, (s : ℂ) * x.2) ∈ P ×ˢ ball (0 : ℂ) 1 := by
    intro x hx s hs
    refine ⟨hx.1, ?_⟩
    rw [mem_ball_zero_iff, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hs.1]
    exact lt_of_le_of_lt (mul_le_of_le_one_left (norm_nonneg _) hs.2) (mem_ball_zero_iff.1 hx.2)
  -- the representation
  have hrep : ∀ x ∈ P ×ˢ ball (0 : ℂ) 1,
      dslope (H x.1) 0 x.2 = ∫ s in (0 : ℝ)..1, deriv (H x.1) ((s : ℂ) * x.2) := by
    intro x hx
    by_cases hu : x.2 = 0
    · rw [hu, dslope_same]
      simp
    · rw [dslope_of_ne _ hu, slope_def_field, sub_zero]
      have hdiff : ∀ s ∈ Set.uIcc (0 : ℝ) 1, HasDerivAt (fun s : ℝ => H x.1 ((s : ℂ) * x.2))
          (deriv (H x.1) ((s : ℂ) * x.2) * x.2) s := by
        intro s hs
        rw [uIcc_of_le zero_le_one] at hs
        have hm := hseg x hx s hs
        have hHd : DifferentiableAt ℂ (H x.1) ((s : ℂ) * x.2) :=
          (hHt x.1 hx.1).differentiableAt (isOpen_ball.mem_nhds hm.2)
        have hl : HasDerivAt (fun s : ℝ => (s : ℂ) * x.2) x.2 s := by
          simpa using ((hasDerivAt_id s).ofReal_comp).mul_const x.2
        exact hHd.hasDerivAt.comp s hl
      have hcont : ContinuousOn (fun s : ℝ => deriv (H x.1) ((s : ℂ) * x.2) * x.2) (Set.uIcc 0 1) := by
        rw [uIcc_of_le zero_le_one]
        have hc := hD.continuousOn.comp (continuousOn_const.prodMk
          ((Complex.continuous_ofReal.mul continuous_const).continuousOn)) (fun s hs => hseg x hx s hs)
        exact hc.mul continuousOn_const
      have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hdiff (hcont.intervalIntegrable)
      have h2 : (∫ s in (0 : ℝ)..1, deriv (H x.1) ((s : ℂ) * x.2)) * x.2 = H x.1 x.2 - H x.1 0 := by
        rw [← intervalIntegral.integral_mul_const, hftc]
        simp
      rw [← h2, mul_div_cancel_right₀ _ hu]
  refine ContDiffOn.congr ?_ hrep
  refine s3g_param_integral hV zero_le_one
    (Φ' := fun x s => (fderiv ℝ (fun q : ℂ × ℂ => deriv (H q.1) q.2) (x.1, (s : ℂ) * x.2)).comp
      ((ContinuousLinearMap.fst ℝ ℂ ℂ).prod 0 + s • (0 : ℂ × ℂ →L[ℝ] ℂ).prod
        (ContinuousLinearMap.snd ℝ ℂ ℂ))) ?_ ?_ ?_
  · intro x hx s hs
    have hm := hseg x hx s hs
    have hF := ((hDd _ hm).differentiableAt (hV.mem_nhds hm)).hasFDerivAt
    have hl0 : HasFDerivAt (fun y : ℂ × ℂ => (y.1, s • y.2))
        ((ContinuousLinearMap.fst ℝ ℂ ℂ).prod (s • ContinuousLinearMap.snd ℝ ℂ ℂ)) x :=
      hasFDerivAt_fst.prodMk (hasFDerivAt_snd.const_smul s)
    have hl : HasFDerivAt (fun y : ℂ × ℂ => (y.1, (s : ℂ) * y.2))
        ((ContinuousLinearMap.fst ℝ ℂ ℂ).prod 0 + s • (0 : ℂ × ℂ →L[ℝ] ℂ).prod
          (ContinuousLinearMap.snd ℝ ℂ ℂ)) x := by
      convert hl0 using 1
      ext v <;> simp [Complex.real_smul]
    exact HasFDerivAt.comp (g := fun q : ℂ × ℂ => deriv (H q.1) q.2)
      (f := fun y : ℂ × ℂ => (y.1, (s : ℂ) * y.2)) x hF hl
  · have hcm : Continuous fun p : (ℂ × ℂ) × ℝ => (p.1.1, (p.2 : ℂ) * p.1.2) := by fun_prop
    exact hD.continuousOn.comp hcm.continuousOn
      fun (p : (ℂ × ℂ) × ℝ) (hp : p ∈ (P ×ˢ ball (0 : ℂ) 1) ×ˢ Icc (0 : ℝ) 1) => hseg p.1 hp.1 p.2 hp.2
  · have hcm : Continuous fun p : (ℂ × ℂ) × ℝ => (p.1.1, (p.2 : ℂ) * p.1.2) := by fun_prop
    refine (hDc.comp hcm.continuousOn
      fun (p : (ℂ × ℂ) × ℝ) (hp : p ∈ (P ×ˢ ball (0 : ℂ) 1) ×ˢ Icc (0 : ℝ) 1) => hseg p.1 hp.1 p.2 hp.2).clm_comp ?_
    exact (continuous_const.add
      (continuous_snd.smul continuous_const)).continuousOn

/-! ### The exterior pre-Schwarzian at `∞` through the reciprocal chart (下属3) -/

/-- `𝒜(w ↦ w / q(1/w))(z) = -u³ (q'' q - 2 q'²) / (q (q + u q'))` at `u = 1/z`. -/
theorem s3g_presch_inv {q : ℂ → ℂ} {z : ℂ} (hz : z ≠ 0) (hq : AnalyticAt ℂ q z⁻¹) (hq0 : q z⁻¹ ≠ 0)
    (hq1 : q z⁻¹ + z⁻¹ * deriv q z⁻¹ ≠ 0) :
    preSchwarzian (fun w => w / q w⁻¹) z = -(z⁻¹) ^ 3 * (deriv (deriv q) z⁻¹ * q z⁻¹ - 2 * deriv q z⁻¹ ^ 2) /
      (q z⁻¹ * (q z⁻¹ + z⁻¹ * deriv q z⁻¹)) := by
  -- the first derivative near `z`
  have hinv : Tendsto (fun w : ℂ => w⁻¹) (𝓝 z) (𝓝 z⁻¹) := tendsto_inv₀ hz
  have hev : ∀ᶠ w in 𝓝 z, w ≠ 0 ∧ AnalyticAt ℂ q w⁻¹ ∧ q w⁻¹ ≠ 0 := by
    have h1 : ∀ᶠ w in 𝓝 z, w ≠ 0 := isOpen_ne.mem_nhds hz
    have h2 := hinv.eventually hq.eventually_analyticAt
    have h3 := hinv.eventually (hq.continuousAt.eventually_ne hq0)
    filter_upwards [h1, h2, h3] with w hw1 hw2 hw3
    exact ⟨hw1, hw2, hw3⟩
  have hd1 : ∀ w : ℂ, w ≠ 0 → AnalyticAt ℂ q w⁻¹ → q w⁻¹ ≠ 0 →
      HasDerivAt (fun w => w / q w⁻¹) ((q w⁻¹ + w⁻¹ * deriv q w⁻¹) / q w⁻¹ ^ 2) w := by
    intro w hw ha hqw
    have hi : HasDerivAt (fun w : ℂ => w⁻¹) (-(w ^ 2)⁻¹) w := hasDerivAt_inv hw
    have hqc : HasDerivAt (fun w : ℂ => q w⁻¹) (deriv q w⁻¹ * -(w ^ 2)⁻¹) w :=
      ha.differentiableAt.hasDerivAt.comp w hi
    have h := (hasDerivAt_id' w).div hqc hqw
    convert h using 1
    field_simp
    ring
  have hD1 : deriv (fun w => w / q w⁻¹) =ᶠ[𝓝 z]
      fun w => (fun u => (q u + u * deriv q u) / q u ^ 2) w⁻¹ := by
    filter_upwards [hev] with w hw
    exact (hd1 w hw.1 hw.2.1 hw.2.2).deriv
  -- the second derivative at `z`
  have hq' : AnalyticAt ℂ (deriv q) z⁻¹ := hq.deriv
  have ha : HasDerivAt (fun u => (q u + u * deriv q u) / q u ^ 2)
      (z⁻¹ * (deriv (deriv q) z⁻¹ * q z⁻¹ - 2 * deriv q z⁻¹ ^ 2) / q z⁻¹ ^ 3) z⁻¹ := by
    have hqd := hq.differentiableAt.hasDerivAt
    have hq'd := hq'.differentiableAt.hasDerivAt
    have hnum : HasDerivAt (fun u => q u + u * deriv q u) _ z⁻¹ := hqd.add ((hasDerivAt_id' z⁻¹).mul hq'd)
    have hden : HasDerivAt (fun u => q u ^ 2) _ z⁻¹ := hqd.pow 2
    have h := hnum.div hden (pow_ne_zero 2 hq0)
    convert h using 1
    all_goals first
      | rfl
      | (generalize q z⁻¹ = Q at hq0 ⊢
         simp only [Nat.cast_ofNat, show (2 : ℕ) - 1 = 1 from rfl, pow_one]
         field_simp
         ring)
  have hcomp := ha.comp z (hasDerivAt_inv hz)
  have hD2 : deriv (deriv (fun w => w / q w⁻¹)) z =
      z⁻¹ * (deriv (deriv q) z⁻¹ * q z⁻¹ - 2 * deriv q z⁻¹ ^ 2) / q z⁻¹ ^ 3 * -(z ^ 2)⁻¹ := by
    rw [hD1.deriv_eq]
    exact hcomp.deriv
  have hD1z : deriv (fun w => w / q w⁻¹) z = (q z⁻¹ + z⁻¹ * deriv q z⁻¹) / q z⁻¹ ^ 2 :=
    (hd1 z hz hq hq0).deriv
  rw [preSchwarzian, hD2, hD1z]
  field_simp

/-! ### Welding normalization helpers (copies of the GAN helpers, 下属3) -/

/-- `𝗀 = g_μ` (welding normalization `c = 0`, `α_μ = id`). -/
theorem s3g_gsans_eq {μ : LinfStar} (hμ : μ ∈ LinfStarBall) (ζ : ℂ) : gsans μ ζ = gMu μ ζ := by
  have hid : Function.invFun (id : ExtPlane → ExtPlane) = id :=
    funext fun z => Function.leftInverse_invFun Function.injective_id z
  show lambdaW (weldConst μ) (gMu μ (finPart (Function.invFun (alphaMu μ) (ζ : ExtPlane)))) = gMu μ ζ
  rw [AppB.b8_weldConst_zero hμ, alphaMu_eq_id, hid]
  simp only [lambdaW, zero_mul, zero_add, div_one]
  rfl

theorem s3g_inv_mem {z : ℂ} (hz : z ∈ unitDiscExterior) : z ≠ 0 ∧ z⁻¹ ∈ unitDisc := by
  have hz1 : 1 < ‖z‖ := hz
  have hz0 : z ≠ 0 := by
    intro h
    rw [h, norm_zero] at hz1
    linarith
  refine ⟨hz0, mem_ball_zero_iff.mpr ?_⟩
  rw [norm_inv]
  exact inv_lt_one_of_one_lt₀ hz1

/-- On `𝔻*`, `1/𝗀_μ(z) = E((μ, μ̄), 1/z)` (`s5cf_gchart_eq`). -/
theorem s3g_recip {μ : LinfStar} (hμ : μ ∈ LinfStarBall) {z : ℂ} (hz : z ∈ unitDiscExterior) :
    s5cf_exterior_reciprocal (μ, star μ) z⁻¹ = (gsans μ z)⁻¹ := by
  obtain ⟨hz0, hu⟩ := s3g_inv_mem hz
  rw [← s5cf_gchart_eq hμ hu, s3g_gsans_eq hμ z]
  show (if z⁻¹ = 0 then 0 else (gMu μ z⁻¹⁻¹)⁻¹) = (gMu μ z)⁻¹
  rw [ite_eq_right_of_eq_false _ _ (eq_false (inv_ne_zero hz0)), inv_inv]

/-- The pre-Schwarzian at `z` depends only on the germ at `z`. -/
theorem s3g_presch_congr {f g : ℂ → ℂ} {z : ℂ} (h : f =ᶠ[𝓝 z] g) : preSchwarzian f z = preSchwarzian g z := by
  rw [preSchwarzian, preSchwarzian, h.deriv.deriv_eq, h.deriv_eq]

/-- **The collar region.** Along a C¹ family `G_t` of injective extensions of `𝗀_{ν_t}` to `|z| > ρ`,
`𝒜(𝗀_t)(z) = G_t''(z)/G_t'(z)` on `𝔻*`, and the right side is C¹ in `(t, z)` on `|t| < r`, `|z| > ρ`. -/
theorem s3g_mid {ν : ℂ → LinfStar} {r ρ : ℝ} (hν : ∀ t ∈ ball (0 : ℂ) r, ν t ∈ LinfStarBall)
    {G : ℂ → ℂ → ℂ} (hG : ContDiffOn ℝ 1 (fun q : ℂ × ℂ => G q.1 q.2) (ball 0 r ×ˢ {z | ρ < ‖z‖}))
    (hGt : ∀ t ∈ ball (0 : ℂ) r, DifferentiableOn ℂ (G t) {z | ρ < ‖z‖} ∧ InjOn (G t) {z | ρ < ‖z‖} ∧
      EqOn (G t) (gMu (ν t)) unitDiscExterior) :
    ContDiffOn ℝ 1 (fun q : ℂ × ℂ => deriv (deriv (G q.1)) q.2 / deriv (G q.1) q.2)
        (ball 0 r ×ˢ {z | ρ < ‖z‖}) ∧
      ∀ t ∈ ball (0 : ℂ) r, ∀ z ∈ unitDiscExterior,
        preSchwarzian (gsans (ν t)) z = deriv (deriv (G t)) z / deriv (G t) z := by
  have hU : IsOpen {z : ℂ | ρ < ‖z‖} := isOpen_lt continuous_const continuous_norm
  obtain ⟨h1, h1h⟩ := s3g_param_deriv isOpen_ball hU hG fun t ht => (hGt t ht).1
  obtain ⟨h2, -⟩ := s3g_param_deriv (F := fun t z => deriv (G t) z) isOpen_ball hU h1 h1h
  have hne : ∀ q ∈ ball (0 : ℂ) r ×ˢ {z : ℂ | ρ < ‖z‖}, deriv (G q.1) q.2 ≠ 0 := fun q hq =>
    deriv_ne_zero_of_injOn hU (hGt q.1 hq.1).1 (hGt q.1 hq.1).2.1 hq.2
  refine ⟨(h2.mul (h1.inv hne)).congr fun q _ => by simp only [div_eq_mul_inv, Pi.inv_apply], ?_⟩
  intro t ht z hz
  have hev : gsans (ν t) =ᶠ[𝓝 z] G t := by
    filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds hz] with w hw
    rw [s3g_gsans_eq (hν t ht) w]
    exact ((hGt t ht).2.2 hw).symm
  rw [s3g_presch_congr hev, preSchwarzian]

/-- **The region near `∞`.** In the reciprocal chart `u = 1/z`, `𝒜(𝗀_t)(z) = -u³ Ψ(t, u)` with `Ψ` C¹ on
`|t| < r`, `|u| < 1` (`Ψ = (q'' q - 2q'²)/(q (q + u q'))`, `q = E/u`, `E = s5cf_exterior_reciprocal`). -/
theorem s3g_inf {ν : ℂ → LinfStar} {r : ℝ} (hν : ∀ t ∈ ball (0 : ℂ) r, ν t ∈ LinfStarBall)
    (hνa : ∀ t ∈ ball (0 : ℂ) r, AnalyticAt ℂ ν t) :
    ∃ Ψ : ℂ × ℂ → ℂ, ContDiffOn ℝ 1 Ψ (ball 0 r ×ˢ ball 0 1) ∧
      ∀ t ∈ ball (0 : ℂ) r, ∀ z ∈ unitDiscExterior,
        preSchwarzian (gsans (ν t)) z = -(z⁻¹) ^ 3 * Ψ (t, z⁻¹) := by
  have h0 : (0 : ℂ) ∈ unitDisc := by simp [unitDisc]
  -- opaque names for the chart `H t u = E((ν_t, ν̄_t), u)` and the quotient `q t = dslope (H t) 0`
  obtain ⟨P, hP⟩ : ∃ P : ℂ → LinfStar × LinfStar, P = fun t => (ν t, star (ν t)) := ⟨_, rfl⟩
  have hPt : ∀ t, P t = (ν t, star (ν t)) := fun t => by rw [hP]
  obtain ⟨H, hHdef⟩ : ∃ H : ℂ → ℂ → ℂ, H = fun t u => s5cf_exterior_reciprocal (P t) u := ⟨_, rfl⟩
  have hHf : ∀ t, H t = fun u => s5cf_exterior_reciprocal (ν t, star (ν t)) u := fun t => by
    rw [hHdef]
    funext u
    show s5cf_exterior_reciprocal (P t) u = _
    rw [hPt]
  have hHa : ∀ q ∈ ball (0 : ℂ) r ×ˢ ball (0 : ℂ) 1, AnalyticAt ℝ (fun q : ℂ × ℂ => H q.1 q.2) q := by
    intro q hq
    have hE : AnalyticAt ℝ (fun p : (LinfStar × LinfStar) × ℂ => s5cf_exterior_reciprocal p.1 p.2)
        (P q.1, q.2) := by
      rw [hPt]
      exact (s5cf_exterior_reciprocal_analytic (hν q.1 hq.1) hq.2).restrictScalars
    have hn : AnalyticAt ℝ ν q.1 := (hνa q.1 hq.1).restrictScalars
    have hPa : AnalyticAt ℝ P q.1 := by
      rw [hP]
      exact hn.prod ((s5cf_star_analytic _).comp hn)
    have hm : AnalyticAt ℝ (fun q : ℂ × ℂ => (P q.1, q.2)) q := (hPa.comp analyticAt_fst).prod analyticAt_snd
    have hfe : (fun q : ℂ × ℂ => H q.1 q.2) =
        (fun p : (LinfStar × LinfStar) × ℂ => s5cf_exterior_reciprocal p.1 p.2) ∘
          (fun q : ℂ × ℂ => (P q.1, q.2)) := by
      rw [hHdef]
      rfl
    rw [hfe]
    exact AnalyticAt.comp_of_eq hE hm rfl
  have hHc : ContDiffOn ℝ 1 (fun q : ℂ × ℂ => H q.1 q.2) (ball 0 r ×ˢ ball 0 1) := fun q hq =>
    (hHa q hq).contDiffAt.contDiffWithinAt
  have hHt : ∀ t ∈ ball (0 : ℂ) r, DifferentiableOn ℂ (H t) (ball 0 1) := by
    intro t ht u hu
    rw [hHf]
    exact ((s5cf_exterior_reciprocal_analytic (hν t ht) hu).comp_of_eq
      (analyticAt_const.prod analyticAt_id) rfl).differentiableAt.differentiableWithinAt
  have hH0 : ∀ t : ℂ, H t 0 = 0 := fun t => by
    rw [hHf]
    simp [s5cf_exterior_reciprocal]
  have hHinj : ∀ t ∈ ball (0 : ℂ) r, InjOn (H t) (ball 0 1) := by
    intro t ht u hu v hv he
    rw [hHf] at he
    apply s5cf_gchart_inj (hν t ht) hu hv
    rw [s5cf_gchart_eq (hν t ht) hu, s5cf_gchart_eq (hν t ht) hv]
    exact he
  have hHd0 : ∀ t ∈ ball (0 : ℂ) r, deriv (H t) 0 ≠ 0 := fun t ht => by
    rw [hHf]
    exact s5cf_exterior_reciprocal_deriv_ne_zero (hν t ht) h0
  obtain ⟨q, hqdef⟩ : ∃ q : ℂ → ℂ → ℂ, q = fun t => dslope (H t) 0 := ⟨_, rfl⟩
  have hq : ContDiffOn ℝ 1 (fun x : ℂ × ℂ => q x.1 x.2) (ball 0 r ×ˢ ball 0 1) := by
    rw [hqdef]
    exact s3g_dslope_param isOpen_ball hHc hHt
  have hqt : ∀ t ∈ ball (0 : ℂ) r, DifferentiableOn ℂ (q t) (ball 0 1) := fun t ht => by
    rw [hqdef]
    exact (differentiableOn_dslope (isOpen_ball.mem_nhds (mem_ball_self one_pos))).2 (hHt t ht)
  obtain ⟨hq1, hq1t⟩ := s3g_param_deriv isOpen_ball isOpen_ball hq hqt
  obtain ⟨hq2, -⟩ := s3g_param_deriv (F := fun t u => deriv (q t) u) isOpen_ball isOpen_ball hq1 hq1t
  have hHq : ∀ t u : ℂ, H t u = u * q t u := by
    intro t u
    have h := sub_smul_dslope (H t) 0 u
    rw [hH0, sub_zero, sub_zero, smul_eq_mul] at h
    rw [hqdef]
    exact h.symm
  have hqne : ∀ x ∈ ball (0 : ℂ) r ×ˢ ball (0 : ℂ) 1, q x.1 x.2 ≠ 0 := by
    intro x hx
    by_cases hu : x.2 = 0
    · rw [hu, hqdef]
      show dslope (H x.1) 0 0 ≠ 0
      rw [dslope_same]
      exact hHd0 x.1 hx.1
    · intro h
      have hH := hHq x.1 x.2
      rw [h, mul_zero] at hH
      apply hu
      exact hHinj x.1 hx.1 hx.2 (mem_ball_self one_pos) (hH.trans (hH0 x.1).symm)
  have hH'ne : ∀ x ∈ ball (0 : ℂ) r ×ˢ ball (0 : ℂ) 1, q x.1 x.2 + x.2 * deriv (q x.1) x.2 ≠ 0 := by
    intro x hx
    have hdq := ((hqt x.1 hx.1).differentiableAt (isOpen_ball.mem_nhds hx.2)).hasDerivAt
    have h := (hasDerivAt_id' x.2).mul hdq
    have hd : HasDerivAt (H x.1) (q x.1 x.2 + x.2 * deriv (q x.1) x.2) x.2 := by
      rw [show H x.1 = fun u => u * q x.1 u from funext (hHq x.1)]
      convert h using 1
      ring
    rw [← hd.deriv]
    exact deriv_ne_zero_of_injOn isOpen_ball (hHt x.1 hx.1) (hHinj x.1 hx.1) hx.2
  refine ⟨fun x => (deriv (deriv (q x.1)) x.2 * q x.1 x.2 - 2 * deriv (q x.1) x.2 ^ 2) /
      (q x.1 x.2 * (q x.1 x.2 + x.2 * deriv (q x.1) x.2)), ?_, ?_⟩
  · have hnum := (hq2.mul hq).sub ((hq1.pow 2).const_smul (2 : ℂ))
    have hden := hq.mul (hq.add (contDiffOn_snd.mul hq1))
    refine (hnum.mul (hden.inv fun x hx => mul_ne_zero (hqne x hx) (hH'ne x hx))).congr fun x _ => ?_
    simp only [div_eq_mul_inv, Pi.inv_apply, smul_eq_mul]
  · intro t ht z hz
    have hz1 : 1 < ‖z‖ := hz
    have hz0 : z ≠ 0 := by
      intro h
      rw [h, norm_zero] at hz1
      linarith
    have hu : z⁻¹ ∈ ball (0 : ℂ) 1 := by
      rw [mem_ball_zero_iff, norm_inv]
      exact inv_lt_one_of_one_lt₀ hz1
    have hev : gsans (ν t) =ᶠ[𝓝 z] fun w => w / q t w⁻¹ := by
      filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds hz] with w hw
      have hr := s3g_recip (hν t ht) hw
      rw [← congrFun (hHf t) w⁻¹, hHq t w⁻¹] at hr
      rw [← inv_inv (gsans (ν t) w), ← hr, mul_inv, inv_inv, div_eq_mul_inv]
    have hqa : AnalyticAt ℂ (q t) z⁻¹ := (hqt t ht).analyticAt (isOpen_ball.mem_nhds hu)
    rw [s3g_presch_congr hev, s3g_presch_inv hz0 hqa (hqne (t, z⁻¹) ⟨ht, hu⟩) (hH'ne (t, z⁻¹) ⟨ht, hu⟩),
      mul_div_assoc]

/-! ### Helpers for (a): rescaled Ahlfors–Weill data and the Möbius identification (下属3) -/

/-- The pointwise weighted bound of an `A∞(𝔻)` element. -/
theorem s3g_ainf_pt (φ : AInf unitDisc) {z : ℂ} (hz : z ∈ unitDisc) :
    ‖AInf.toFun φ z‖ * (1 - ‖z‖ ^ 2) ^ 2 ≤ ‖φ‖ := by
  have hz1 : ‖z‖ < 1 := mem_ball_zero_iff.mp hz
  have hw : 0 < 1 - ‖z‖ ^ 2 := by nlinarith [norm_nonneg z]
  have he : AInf.toFun φ z = φ.1 ⟨z, hz⟩ / (1 - (‖z‖ : ℂ) ^ 2) ^ 2 := by
    show (if h : z ∈ unitDisc then φ.1 ⟨z, h⟩ / (1 - (‖z‖ : ℂ) ^ 2) ^ 2 else 0) = _
    rw [dif_pos hz]
  have hn : ‖(1 - (‖z‖ : ℂ) ^ 2)‖ = 1 - ‖z‖ ^ 2 := by
    rw [show (1 - (‖z‖ : ℂ) ^ 2) = ((1 - ‖z‖ ^ 2 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
      Real.norm_of_nonneg hw.le]
  rw [he, norm_div, norm_pow, hn, div_mul_cancel₀ _ (pow_pos hw 2).ne']
  exact φ.1.norm_coe_le_norm _

/-- Values of `φ + t ψ` in `A∞(𝔻)`. -/
theorem s3g_ainf_add_smul (φ ψ : AInf unitDisc) (t z : ℂ) :
    AInf.toFun (φ + t • ψ) z = AInf.toFun φ z + t * AInf.toFun ψ z := by
  show unweight unitDisc (φ.1 + t • ψ.1) z = unweight unitDisc φ.1 z + t * unweight unitDisc ψ.1 z
  rw [unweight_add, unweight_smul]
  rfl

/-- Rescaling `p ↦ ρ² p(ρ ·)` moves `p` uniformly little on the closed unit disc for `ρ` near `1`. -/
theorem s3g_rescale {p : ℂ → ℂ} (hp : Continuous p) {δ : ℝ} (hδ : 0 < δ) :
    ∃ ε > 0, ∀ ρ : ℝ, |ρ - 1| < ε → ∀ z ∈ closedBall (0 : ℂ) 1, ‖(ρ : ℂ) ^ 2 * p (ρ * z) - p z‖ < δ := by
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : ℝ × ℂ → ℂ, Φ = fun q => (q.1 : ℂ) ^ 2 * p (q.1 * q.2) - p q.2 := ⟨_, rfl⟩
  have hc : Continuous Φ := by
    rw [hΦ]
    have := Complex.continuous_ofReal
    fun_prop
  have hn : IsOpen {q : ℝ × ℂ | ‖Φ q‖ < δ} := isOpen_lt (continuous_norm.comp hc) continuous_const
  have hsub : ({1} : Set ℝ) ×ˢ closedBall (0 : ℂ) 1 ⊆ {q : ℝ × ℂ | ‖Φ q‖ < δ} := by
    rintro ⟨a, z⟩ ⟨ha, -⟩
    rw [mem_singleton_iff] at ha
    subst ha
    show ‖Φ (1, z)‖ < δ
    simp [hΦ, hδ]
  obtain ⟨u, v, hu, -, h1u, hv, huv⟩ :=
    generalized_tube_lemma isCompact_singleton (isCompact_closedBall (0 : ℂ) 1) hn hsub
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hu 1 (h1u (mem_singleton 1))
  refine ⟨ε, hε, fun ρ hρ z hz => ?_⟩
  have h := huv (show (ρ, z) ∈ u ×ˢ v from ⟨hball (by rw [mem_ball, Real.dist_eq]; exact hρ), hv hz⟩)
  have h' : ‖Φ (ρ, z)‖ < δ := h
  rw [hΦ] at h'
  exact h'

/-- `f^μ` is continuous on the closed unit disc. -/
theorem s3g_fB_contOn {μ : LinfStar} (hμ : μ ∈ LinfStarBall) : ContinuousOn (fB μ) (closedBall 0 1) := by
  intro z hz
  have hz1 : ‖z‖ ≤ 1 := mem_closedBall_zero_iff.mp hz
  have h : ContinuousAt (fun w : ℂ => finPart (wB μ (w : ExtPlane))) z :=
    ContinuousAt.comp (g := finPart) (f := fun w : ℂ => wB μ (w : ExtPlane))
      (s5rh_finPart_contAt (s5e_wB_finite hμ hz1))
      ((wB_continuous hμ).continuousAt.comp OnePoint.continuous_coe.continuousAt)
  exact h.continuousWithinAt

/-- A family `(t, z) ↦ f^{ν_t}(c z)` along a real-analytic curve `ν` is C¹ and holomorphic in `z`. -/
theorem s3g_fB_family {ν : ℂ → LinfStar} {r : ℝ} (hν : ∀ t ∈ ball (0 : ℂ) r, ν t ∈ LinfStarBall)
    (hνa : ∀ t, AnalyticAt ℝ ν t) {c : ℂ} {R : ℝ} (hc : ∀ z ∈ ball (0 : ℂ) R, c * z ∈ unitDisc) :
    ContDiffOn ℝ 1 (fun q : ℂ × ℂ => fB (ν q.1) (c * q.2)) (ball 0 r ×ˢ ball 0 R) ∧
      ∀ t ∈ ball (0 : ℂ) r, DifferentiableOn ℂ (fun z => fB (ν t) (c * z)) (ball 0 R) := by
  refine ⟨fun q hq => ?_, fun t ht => ?_⟩
  · have hm : AnalyticAt ℝ (fun q : ℂ × ℂ => (ν q.1, c * q.2)) q :=
      (AnalyticAt.comp_of_eq (g := ν) (f := fun q : ℂ × ℂ => q.1) (hνa q.1) analyticAt_fst rfl).prod
        (analyticAt_const.mul analyticAt_snd)
    have h := AnalyticAt.comp_of_eq (g := fun p : LinfStar × ℂ => fB p.1 p.2)
      (f := fun q : ℂ × ℂ => (ν q.1, c * q.2)) (s5t53_fB_joint (hν q.1 hq.1) (hc q.2 hq.2)) hm rfl
    exact h.contDiffAt.contDiffWithinAt
  · exact (fB_holomorphic_injective (hν t ht)).1.comp (differentiableOn_id.const_mul c) (fun z hz => hc z hz)

/-- The second `z`-jet at a point of a C¹ holomorphic family is C¹ in the parameter. -/
theorem s3g_jet2 {P U : Set ℂ} (hP : IsOpen P) (hU : IsOpen U) {F : ℂ → ℂ → ℂ} {z₀ : ℂ} (hz₀ : z₀ ∈ U)
    (hF : ContDiffOn ℝ 1 (fun q : ℂ × ℂ => F q.1 q.2) (P ×ˢ U)) (hFt : ∀ t ∈ P, DifferentiableOn ℂ (F t) U) :
    ContDiffOn ℝ 1 (fun t => deriv (deriv (F t)) z₀) P := by
  obtain ⟨h1, h1t⟩ := s3g_param_deriv hP hU hF hFt
  obtain ⟨h2, -⟩ := s3g_param_deriv (F := fun t z => deriv (F t) z) hP hU h1 h1t
  have hm : MapsTo (fun t : ℂ => (t, z₀)) P (P ×ˢ U) := fun t ht => ⟨ht, hz₀⟩
  exact h2.comp (ContDiffOn.prodMk contDiffOn_id contDiffOn_const) hm

/-- **Möbius identification.** If `f` (univalent on `𝔻`, continuous on `𝔻̄`) and `F` (univalent on `|z| < ρ`,
`ρ > 1`) have the same Schwarzian on `𝔻` and both are normalized by `0 ↦ 0`, `(·)'(0) = 1`, then
`f = F / (γ F + 1)` on `𝔻̄` with `γ = (F''(0) - f''(0))/2`, and `γ F + 1 ≠ 0` on `𝔻̄`. -/
theorem s3g_mob_ident {f F : ℂ → ℂ} {ρ : ℝ} (hρ : 1 < ρ)
    (hf : DifferentiableOn ℂ f unitDisc) (hfc : ContinuousOn f (closedBall 0 1))
    (hF : DifferentiableOn ℂ F (ball 0 ρ)) (hFi : InjOn F (ball 0 ρ))
    (hf0 : f 0 = 0) (hf1 : deriv f 0 = 1) (hF0 : F 0 = 0) (hF1 : deriv F 0 = 1)
    (hS : EqOn (schwarzianHol f) (schwarzianHol F) unitDisc) {γ : ℂ}
    (hγ : γ = (deriv (deriv F) 0 - deriv (deriv f) 0) / 2) :
    (∀ z ∈ closedBall (0 : ℂ) 1, f z * (γ * F z + 1) = F z) ∧
      ∀ z ∈ closedBall (0 : ℂ) 1, γ * F z + 1 ≠ 0 := by
  have hzero : (0 : ℂ) ∈ unitDisc := mem_ball_self (by norm_num)
  have hzρ : (0 : ℂ) ∈ ball (0 : ℂ) ρ := mem_ball_self (by linarith)
  have hDρ : unitDisc ⊆ ball (0 : ℂ) ρ := ball_subset_ball hρ.le
  have hfan : AnalyticOnNhd ℂ f unitDisc := fun z hz => hf.analyticAt (isOpen_ball.mem_nhds hz)
  have hFan : AnalyticOnNhd ℂ F (ball 0 ρ) := fun z hz => hF.analyticAt (isOpen_ball.mem_nhds hz)
  have hSe : schwarzianHol f =ᶠ[𝓝 (0 : ℂ)] schwarzianHol F := by
    filter_upwards [isOpen_ball.mem_nhds hzero] with z hz
    exact hS hz
  obtain ⟨a, b, c, d, hdet, he⟩ := exists_mobius_of_schwarzianHol_eventuallyEq
    (hfan 0 hzero) (by simp [hf1]) (hFan 0 hzρ) (by simp [hF1]) hSe
  have hd : d ≠ 0 := by
    intro hd0
    have hc : c ≠ 0 := by
      intro hc0
      apply hdet
      simp [hd0, hc0]
    have he' : (fun z => f z * (c * F z + d)) =ᶠ[𝓝[≠] (0 : ℂ)] (fun z => a * F z + b) := by
      filter_upwards [he.filter_mono nhdsWithin_le_nhds,
        mem_nhdsWithin_of_mem_nhds (isOpen_ball.mem_nhds hzρ), self_mem_nhdsWithin]
        with z hz hzD hz0
      have hFz : F z ≠ 0 := by
        intro h
        exact hz0 (hFi hzD hzρ (h.trans hF0.symm))
      exact (eq_div_iff (by simpa only [hd0, add_zero] using mul_ne_zero hc hFz)).mp hz
    have hfc0 : ContinuousAt f 0 := (hfan 0 hzero).continuousAt
    have hFc0 : ContinuousAt F 0 := (hFan 0 hzρ).continuousAt
    have hL : ContinuousAt (fun z => f z * (c * F z + d)) 0 := by fun_prop
    have hR : ContinuousAt (fun z => a * F z + b) 0 := by fun_prop
    have hlim := tendsto_nhds_unique
      (hL.tendsto.mono_left (nhdsWithin_le_nhds : 𝓝[≠] (0 : ℂ) ≤ 𝓝 (0 : ℂ)))
      ((hR.tendsto.mono_left (nhdsWithin_le_nhds : 𝓝[≠] (0 : ℂ) ≤ 𝓝 (0 : ℂ))).congr' he'.symm)
    have hb : b = 0 := by simpa [hf0, hF0] using hlim.symm
    exact hdet (by simp [hd0, hb])
  have heM : f =ᶠ[𝓝 (0 : ℂ)] (fun z => mobiusFn a b c d (F z)) := he
  have hden0 : c * F 0 + d ≠ 0 := by simpa [hF0] using hd
  have hb : b = 0 := by
    have h0 : f 0 = mobiusFn a b c d (F 0) := heM.self_of_nhds
    rw [hf0, hF0, mobiusFn, mul_zero, zero_add, mul_zero, zero_add] at h0
    exact (div_eq_zero_iff.mp h0.symm).resolve_right hd
  obtain ⟨he1, he2⟩ := mobius_comp_first_second (a := a) (b := b) (hFan 0 hzρ) hden0
  have h1 : (a * d - b * c) / (c * F 0 + d) ^ 2 * deriv F 0 = 1 :=
    he1.symm.trans (heM.deriv_eq.symm.trans hf1)
  rw [hF0, hF1, hb] at h1
  simp only [zero_mul, sub_zero, mul_zero, zero_add, mul_one] at h1
  have had : a * d = d ^ 2 := (div_eq_one_iff_eq (pow_ne_zero 2 hd)).mp h1
  have ha : a = d := mul_right_cancel₀ hd (by rw [had]; ring)
  have h2 := heM.deriv.deriv_eq.trans he2
  rw [hF0, hF1, hb, ha] at h2
  have hγd : γ * d = c := by
    have hd3 : d ^ 3 * d⁻¹ ^ 3 = 1 := by rw [← mul_pow, mul_inv_cancel₀ hd, one_pow]
    rw [hγ, h2]
    field_simp
    linear_combination (2 * c - d * deriv (deriv F) 0) * hd3
  -- `f (γ F + 1) = F` on `𝔻` by the identity theorem
  have hFc : ContinuousOn F (closedBall 0 1) := hF.continuousOn.mono (closedBall_subset_ball hρ)
  have hid : EqOn (fun z => f z * (γ * F z + 1)) F unitDisc := by
    have hLa : AnalyticOnNhd ℂ (fun z => f z * (γ * F z + 1)) unitDisc := fun z hz =>
      (hfan z hz).mul ((analyticAt_const.mul (hFan z (hDρ hz))).add analyticAt_const)
    have hRa : AnalyticOnNhd ℂ F unitDisc := fun z hz => hFan z (hDρ hz)
    have hcd : ContinuousAt (fun z => c * F z + d) 0 := (continuousAt_const.mul (hFan 0 hzρ).continuousAt).add continuousAt_const
    have hev : (fun z => f z * (γ * F z + 1)) =ᶠ[𝓝 (0 : ℂ)] F := by
      filter_upwards [heM, hcd.eventually_ne hden0] with z hz hz'
      have hz2 : f z = (a * F z + b) / (c * F z + d) := hz
      have hz3 : c * F z + d ≠ 0 := hz'
      show f z * (γ * F z + 1) = F z
      rw [hz2, hb, ha, add_zero, ← hγd]
      rw [← hγd] at hz3
      rw [div_mul_eq_mul_div, div_eq_iff hz3]
      ring
    exact hLa.eqOn_of_preconnected_of_eventuallyEq hRa (convex_ball (0 : ℂ) (1 : ℝ)).isPreconnected hzero hev
  have hcl : EqOn (fun z => f z * (γ * F z + 1)) F (closedBall 0 1) := by
    refine hid.of_subset_closure (hfc.mul ((continuousOn_const.mul hFc).add continuousOn_const)) hFc
      ball_subset_closedBall ?_
    show closedBall (0 : ℂ) 1 ⊆ closure (ball 0 1)
    rw [closure_ball _ one_ne_zero]
  refine ⟨fun z hz => hcl hz, fun z hz h0 => ?_⟩
  have h := hcl hz
  simp only [h0, mul_zero] at h
  have hz0 : z = 0 := hFi (closedBall_subset_ball hρ hz) hzρ (h.symm.trans hF0.symm)
  rw [hz0, hF0, mul_zero, zero_add] at h0
  exact one_ne_zero h0

/-! ### Generic tools for (b), (b′): inverse families and the annulus Cauchy formula (下属3) -/

/-- **Inverse of a C¹ family of univalent maps.** For a C¹ family `F_t` of injective holomorphic maps on `U`, the set
`{(t, F_t z)}` is open and the inverse family `(t, w) ↦ F_t⁻¹(w)` is C¹ there and holomorphic in `w`. -/
theorem s3g_inv_family {P U : Set ℂ} (hP : IsOpen P) (hU : IsOpen U) {F : ℂ → ℂ → ℂ}
    (hF : ContDiffOn ℝ 1 (fun q : ℂ × ℂ => F q.1 q.2) (P ×ˢ U))
    (hFt : ∀ t ∈ P, DifferentiableOn ℂ (F t) U) (hFi : ∀ t ∈ P, InjOn (F t) U) :
    ∃ Inv : ℂ → ℂ → ℂ,
      IsOpen ((fun q : ℂ × ℂ => (q.1, F q.1 q.2)) '' (P ×ˢ U)) ∧
      ContDiffOn ℝ 1 (fun q : ℂ × ℂ => Inv q.1 q.2) ((fun q : ℂ × ℂ => (q.1, F q.1 q.2)) '' (P ×ˢ U)) ∧
      (∀ t ∈ P, ∀ z ∈ U, Inv t (F t z) = z) ∧
      (∀ t w, (t, w) ∈ (fun q : ℂ × ℂ => (q.1, F q.1 q.2)) '' (P ×ˢ U) → Inv t w ∈ U ∧ F t (Inv t w) = w) ∧
      (∀ t ∈ P, DifferentiableOn ℂ (Inv t) (F t '' U)) := by
  obtain ⟨Ψ, hΨ⟩ : ∃ Ψ : ℂ × ℂ → ℂ × ℂ, Ψ = fun q => (q.1, F q.1 q.2) := ⟨_, rfl⟩
  have hPU : IsOpen (P ×ˢ U) := hP.prod hU
  have hΨap : ∀ q : ℂ × ℂ, Ψ q = (q.1, F q.1 q.2) := fun q => by rw [hΨ]
  have hinjΨ : InjOn Ψ (P ×ˢ U) := by
    intro q hq q' hq' he
    rw [hΨap, hΨap] at he
    have h1 : q.1 = q'.1 := (Prod.ext_iff.mp he).1
    have h2 : F q.1 q.2 = F q'.1 q'.2 := (Prod.ext_iff.mp he).2
    rw [← h1] at h2
    exact Prod.ext h1 (hFi q.1 hq.1 hq.2 hq'.2 h2)
  obtain ⟨Ginv, hGinv⟩ : ∃ Ginv : ℂ × ℂ → ℂ × ℂ,
      Ginv = fun y => if h : ∃ q ∈ P ×ˢ U, Ψ q = y then h.choose else 0 := ⟨_, rfl⟩
  have hGΨ : ∀ q ∈ P ×ˢ U, Ginv (Ψ q) = q := by
    intro q hq
    have hex : ∃ q' ∈ P ×ˢ U, Ψ q' = Ψ q := ⟨q, hq, rfl⟩
    rw [hGinv]
    show (if h : ∃ q' ∈ P ×ˢ U, Ψ q' = Ψ q then h.choose else 0) = q
    rw [dif_pos hex]
    exact hinjΨ hex.choose_spec.1 hq hex.choose_spec.2
  -- the local inverse function theorem at each point
  have hloc : ∀ q0 ∈ P ×ˢ U, ∃ T : Set (ℂ × ℂ), IsOpen T ∧ Ψ q0 ∈ T ∧ T ⊆ Ψ '' (P ×ˢ U) ∧
      ContDiffAt ℝ 1 Ginv (Ψ q0) := by
    intro q0 hq0
    have hΦ : ContDiffAt ℝ 1 (fun q : ℂ × ℂ => F q.1 q.2) q0 := hF.contDiffAt (hPU.mem_nhds hq0)
    have hΨc : ContDiffAt ℝ 1 Ψ q0 := by
      rw [hΨ]
      exact contDiffAt_fst.prodMk hΦ
    obtain ⟨DΦ, hDΦ⟩ : ∃ D, D = fderiv ℝ (fun q : ℂ × ℂ => F q.1 q.2) q0 := ⟨_, rfl⟩
    have hΦd : HasFDerivAt (fun q : ℂ × ℂ => F q.1 q.2) DΦ q0 := by
      rw [hDΦ]
      exact (hΦ.differentiableAt one_ne_zero).hasFDerivAt
    have hΨd : HasFDerivAt Ψ ((ContinuousLinearMap.fst ℝ ℂ ℂ).prod DΦ) q0 := by
      rw [hΨ]
      exact hasFDerivAt_fst.prodMk hΦd
    have hpart : ∀ v : ℂ, DΦ (0, v) = v * deriv (F q0.1) q0.2 := by
      have hFz : HasDerivAt (F q0.1) (deriv (F q0.1) q0.2) q0.2 :=
        ((hFt q0.1 hq0.1).differentiableAt (hU.mem_nhds hq0.2)).hasDerivAt
      have hm : HasFDerivAt (fun z : ℂ => (q0.1, z)) ((0 : ℂ →L[ℝ] ℂ).prod (ContinuousLinearMap.id ℝ ℂ)) q0.2 :=
        (hasFDerivAt_const q0.1 q0.2).prodMk (hasFDerivAt_id q0.2)
      have h1 : HasFDerivAt (fun z : ℂ => F q0.1 z)
          (DΦ.comp ((0 : ℂ →L[ℝ] ℂ).prod (ContinuousLinearMap.id ℝ ℂ))) q0.2 :=
        HasFDerivAt.comp (g := fun q : ℂ × ℂ => F q.1 q.2) (f := fun z : ℂ => (q0.1, z)) q0.2 hΦd hm
      have h3 := h1.unique (hFz.hasFDerivAt.restrictScalars ℝ)
      intro v
      have h4 := congrArg (fun L : ℂ →L[ℝ] ℂ => L v) h3
      simpa using h4
    have hc0 : deriv (F q0.1) q0.2 ≠ 0 := deriv_ne_zero_of_injOn hU (hFt q0.1 hq0.1) (hFi q0.1 hq0.1) hq0.2
    obtain ⟨L, hL⟩ : ∃ L : ℂ × ℂ →L[ℝ] ℂ × ℂ, L = (ContinuousLinearMap.fst ℝ ℂ ℂ).prod DΦ := ⟨_, rfl⟩
    have hinj : Function.Injective L := by
      refine (injective_iff_map_eq_zero L).mpr fun v hv => ?_
      rw [hL] at hv
      have h1 : v.1 = 0 := by simpa using congrArg Prod.fst hv
      have h2 : DΦ v = 0 := by simpa using congrArg Prod.snd hv
      have hv' : v = (0, v.2) := Prod.ext h1 rfl
      rw [hv', hpart] at h2
      rw [hv', (mul_eq_zero.mp h2).resolve_right hc0]
      rfl
    have hsurj : Function.Surjective L :=
      (LinearMap.injective_iff_surjective (f := (L : ℂ × ℂ →ₗ[ℝ] ℂ × ℂ))).mp hinj
    obtain ⟨e, he⟩ : ∃ e : (ℂ × ℂ) ≃L[ℝ] (ℂ × ℂ),
        e = (LinearEquiv.ofBijective (L : ℂ × ℂ →ₗ[ℝ] ℂ × ℂ) ⟨hinj, hsurj⟩).toContinuousLinearEquiv :=
      ⟨_, rfl⟩
    have hf' : HasFDerivAt Ψ (e : ℂ × ℂ →L[ℝ] ℂ × ℂ) q0 := by
      refine (hL ▸ hΨd).congr_fderiv (ContinuousLinearMap.ext fun v => ?_)
      rw [he]
      rfl
    obtain ⟨PH, hPH⟩ : ∃ PH : OpenPartialHomeomorph (ℂ × ℂ) (ℂ × ℂ),
        PH = hΨc.toOpenPartialHomeomorph Ψ hf' one_ne_zero := ⟨_, rfl⟩
    have hPHc : ∀ x, PH x = Ψ x := fun x => by rw [hPH]; rfl
    have hsymm : ContDiffAt ℝ 1 PH.symm (Ψ q0) := by
      rw [hPH]
      exact hΨc.to_localInverse hf' one_ne_zero
    have hsrc : q0 ∈ PH.source := by
      rw [hPH]
      exact hΨc.mem_toOpenPartialHomeomorph_source hf' one_ne_zero
    have htgt : Ψ q0 ∈ PH.target := by
      rw [hPH]
      exact hΨc.image_mem_toOpenPartialHomeomorph_target hf' one_ne_zero
    have hTo : IsOpen (PH.target ∩ PH.symm ⁻¹' (P ×ˢ U)) :=
      PH.continuousOn_symm.isOpen_inter_preimage PH.open_target hPU
    have hmem : Ψ q0 ∈ PH.target ∩ PH.symm ⁻¹' (P ×ˢ U) := by
      refine ⟨htgt, ?_⟩
      show PH.symm (Ψ q0) ∈ P ×ˢ U
      rw [← hPHc, PH.left_inv hsrc]
      exact hq0
    have hright : ∀ y ∈ PH.target ∩ PH.symm ⁻¹' (P ×ˢ U), Ψ (PH.symm y) = y := fun y hy => by
      rw [← hPHc]
      exact PH.right_inv hy.1
    refine ⟨_, hTo, hmem, fun y hy => ⟨PH.symm y, hy.2, hright y hy⟩, ?_⟩
    refine hsymm.congr_of_eventuallyEq ?_
    filter_upwards [hTo.mem_nhds hmem] with y hy
    rw [← hright y hy, hGΨ _ hy.2, hright y hy]
  -- assembly
  have hWo : IsOpen (Ψ '' (P ×ˢ U)) := by
    rw [isOpen_iff_mem_nhds]
    rintro _ ⟨q0, hq0, rfl⟩
    obtain ⟨T, hT, hqT, hTs, -⟩ := hloc q0 hq0
    exact Filter.mem_of_superset (hT.mem_nhds hqT) hTs
  obtain ⟨Inv, hInv⟩ : ∃ Inv : ℂ → ℂ → ℂ, ∀ t w, Inv t w = (Ginv (t, w)).2 := ⟨_, fun _ _ => rfl⟩
  have hInvf : (fun q : ℂ × ℂ => Inv q.1 q.2) = Prod.snd ∘ Ginv := by
    funext q
    rw [hInv]
    rfl
  have hCD : ContDiffOn ℝ 1 (fun q : ℂ × ℂ => Inv q.1 q.2) (Ψ '' (P ×ˢ U)) := by
    rintro _ ⟨q0, hq0, rfl⟩
    obtain ⟨-, -, -, -, hG⟩ := hloc q0 hq0
    rw [hInvf]
    exact (contDiffAt_snd.comp _ hG).contDiffWithinAt
  have hleft : ∀ t ∈ P, ∀ z ∈ U, Inv t (F t z) = z := by
    intro t ht z hz
    have h := hGΨ (t, z) ⟨ht, hz⟩
    rw [hΨap] at h
    rw [hInv, h]
  have hWin : ∀ t w, (t, w) ∈ Ψ '' (P ×ˢ U) → Inv t w ∈ U ∧ F t (Inv t w) = w := by
    rintro t w ⟨q, hq, hqe⟩
    rw [hΨap] at hqe
    have h1 : q.1 = t := (Prod.ext_iff.mp hqe).1
    have h2 : F q.1 q.2 = w := (Prod.ext_iff.mp hqe).2
    have h3 : Inv t w = q.2 := by
      rw [hInv, ← h2, ← h1]
      have h := hGΨ q hq
      rw [hΨap] at h
      rw [h]
    rw [h3, ← h1]
    exact ⟨hq.2, h2⟩
  have hΨeq : Ψ '' (P ×ˢ U) = (fun q : ℂ × ℂ => (q.1, F q.1 q.2)) '' (P ×ˢ U) := by rw [hΨ]
  refine ⟨Inv, hΨeq ▸ hWo, hΨeq ▸ hCD, hleft, fun t w hw => hWin t w (hΨeq ▸ hw), ?_⟩
  rintro t ht _ ⟨z, hz, rfl⟩
  have hmemW : (t, F t z) ∈ Ψ '' (P ×ˢ U) := ⟨(t, z), ⟨ht, hz⟩, by rw [hΨap]⟩
  have hcont : ContinuousAt (Inv t) (F t z) := by
    have h := (hCD.contDiffAt (hWo.mem_nhds hmemW)).continuousAt
    exact ContinuousAt.comp (g := fun q : ℂ × ℂ => Inv q.1 q.2) (f := fun w : ℂ => (t, w)) h
      (continuousAt_const.prodMk continuousAt_id)
  have hFd : HasDerivAt (F t) (deriv (F t) (Inv t (F t z))) (Inv t (F t z)) := by
    rw [hleft t ht z hz]
    exact ((hFt t ht).differentiableAt (hU.mem_nhds hz)).hasDerivAt
  have hne : deriv (F t) (Inv t (F t z)) ≠ 0 := by
    rw [hleft t ht z hz]
    exact deriv_ne_zero_of_injOn hU (hFt t ht) (hFi t ht) hz
  have hev : ∀ᶠ y in 𝓝 (F t z), F t (Inv t y) = y := by
    have hpre : IsOpen ((fun w : ℂ => (t, w)) ⁻¹' (Ψ '' (P ×ˢ U))) :=
      hWo.preimage (continuous_const.prodMk continuous_id)
    filter_upwards [hpre.mem_nhds hmemW] with y hy
    exact (hWin t y hy).2
  exact (HasDerivAt.of_local_left_inverse hcont hFd hne hev).differentiableAt.differentiableWithinAt

/-- **Cauchy formula on an annulus** `a < |z| < b`. -/
theorem s3g_annulus_cauchy {φ : ℂ → ℂ} {a b : ℝ} (ha : 0 < a) (hab : a < b) {U : Set ℂ} (hU : IsOpen U)
    (hsub : closedBall (0 : ℂ) b \ ball 0 a ⊆ U) (hφ : DifferentiableOn ℂ φ U) {z : ℂ} (hz1 : a < ‖z‖)
    (hz2 : ‖z‖ < b) :
    φ z = (2 * π * I)⁻¹ * ((∮ ζ in C(0, b), (ζ - z)⁻¹ • φ ζ) - ∮ ζ in C(0, a), (ζ - z)⁻¹ • φ ζ) := by
  have hb0 : 0 ≤ b := by linarith
  have hzU : z ∈ U := hsub ⟨mem_closedBall_zero_iff.mpr hz2.le, fun h => by
    rw [mem_ball_zero_iff] at h; linarith⟩
  have hφd : ∀ w ∈ U, DifferentiableAt ℂ φ w := fun w hw => hφ.differentiableAt (hU.mem_nhds hw)
  have hkc : ContinuousOn (dslope φ z) (closedBall 0 b \ ball 0 a) := by
    intro w hw
    by_cases hwz : w = z
    · rw [hwz]
      exact (continuousAt_dslope_same.mpr (hφd z hzU)).continuousWithinAt
    · exact ((continuousAt_dslope_of_ne hwz).mpr (hφd w (hsub hw)).continuousAt).continuousWithinAt
  have hkd : ∀ w ∈ (ball (0 : ℂ) b \ closedBall 0 a) \ {z}, DifferentiableAt ℂ (dslope φ z) w := by
    intro w hw
    have hw1 : w ∈ closedBall (0 : ℂ) b \ ball 0 a :=
      ⟨ball_subset_closedBall hw.1.1, fun h => hw.1.2 (ball_subset_closedBall h)⟩
    exact (differentiableAt_dslope_of_ne hw.2).mpr (hφd w (hsub hw1))
  have hann := circleIntegral_eq_of_differentiable_on_annulus_off_countable ha hab.le (countable_singleton z)
    hkc hkd
  -- on each circle, `dslope φ z ζ = (ζ - z)⁻¹ • φ ζ - (ζ - z)⁻¹ • φ z`
  have hcirc : ∀ R : ℝ, 0 < R → R ≠ ‖z‖ → sphere (0 : ℂ) R ⊆ U →
      (∮ ζ in C(0, R), dslope φ z ζ) =
        (∮ ζ in C(0, R), (ζ - z)⁻¹ • φ ζ) - (∮ ζ in C(0, R), (ζ - z)⁻¹) • φ z := by
    intro R hR hRz hsU
    have hne : ∀ ζ ∈ sphere (0 : ℂ) R, ζ ≠ z := by
      intro ζ hζ h
      rw [h, mem_sphere_zero_iff_norm] at hζ
      exact hRz hζ.symm
    have hcinv : ContinuousOn (fun ζ : ℂ => (ζ - z)⁻¹) (sphere 0 R) :=
      (continuousOn_id.sub continuousOn_const).inv₀ fun ζ hζ => sub_ne_zero.mpr (hne ζ hζ)
    have hcφ : ContinuousOn φ (sphere 0 R) := fun ζ hζ => (hφd ζ (hsU hζ)).continuousAt.continuousWithinAt
    rw [circleIntegral.integral_congr hR.le (g := fun ζ => (ζ - z)⁻¹ • φ ζ - (ζ - z)⁻¹ • φ z)
      (fun ζ hζ => by
        show dslope φ z ζ = (ζ - z)⁻¹ • φ ζ - (ζ - z)⁻¹ • φ z
        rw [dslope_of_ne _ (hne ζ hζ), slope_def_module, smul_sub]),
      circleIntegral.integral_sub (f := fun ζ => (ζ - z)⁻¹ • φ ζ) (g := fun ζ => (ζ - z)⁻¹ • φ z)
        (show CircleIntegrable (fun ζ => (ζ - z)⁻¹ • φ ζ) 0 R from (hcinv.smul hcφ).circleIntegrable hR.le)
        (show CircleIntegrable (fun ζ => (ζ - z)⁻¹ • φ z) 0 R from
          (hcinv.smul continuousOn_const).circleIntegrable hR.le),
      circleIntegral.integral_smul_const]
  have hsb : sphere (0 : ℂ) b ⊆ U := fun ζ hζ => hsub ⟨sphere_subset_closedBall hζ, fun h => by
    rw [mem_sphere_zero_iff_norm] at hζ; rw [mem_ball_zero_iff] at h; linarith⟩
  have hsa : sphere (0 : ℂ) a ⊆ U := fun ζ hζ => hsub ⟨by
    rw [mem_closedBall_zero_iff, (mem_sphere_zero_iff_norm.mp hζ)]; exact hab.le, fun h => by
    rw [mem_sphere_zero_iff_norm] at hζ; rw [mem_ball_zero_iff] at h; linarith⟩
  rw [hcirc b (by linarith) (by linarith) hsb, hcirc a ha (by linarith) hsa] at hann
  have hIb : (∮ ζ in C(0, b), (ζ - z)⁻¹) = 2 * π * I :=
    circleIntegral.integral_sub_inv_of_mem_ball (mem_ball_zero_iff.mpr hz2)
  have hIa : (∮ ζ in C(0, a), (ζ - z)⁻¹) = 0 := by
    refine circleIntegral_eq_zero_of_differentiable_on_off_countable ha.le countable_empty ?_ ?_
    · refine (continuousOn_id.sub continuousOn_const).inv₀ fun ζ hζ => sub_ne_zero.mpr fun h => ?_
      have h' : ζ = z := h
      rw [h', mem_closedBall_zero_iff] at hζ
      linarith
    · intro ζ hζ
      have hζz : ζ - z ≠ 0 := sub_ne_zero.mpr fun h => by
        have := hζ.1
        rw [h, mem_ball_zero_iff] at this; linarith
      exact (differentiableAt_id.sub (differentiableAt_const z)).inv hζz
  rw [hIb, hIa, zero_smul, sub_zero, smul_eq_mul] at hann
  have h2 : (2 * π * I : ℂ) ≠ 0 := Complex.two_pi_I_ne_zero
  rw [← hann, sub_sub_cancel, ← mul_assoc, inv_mul_cancel₀ h2, one_mul]

/-- **C¹ dependence of a Cauchy integral** over `|ζ| = R` on the parameter and on the point `z`, `|z| ≠ R`. -/
theorem s3g_cauchy_param {P O : Set ℂ} (hP : IsOpen P) (hO : IsOpen O) {R : ℝ} (hR : 0 < R)
    (hRO : sphere (0 : ℂ) R ⊆ O) {Φ : ℂ → ℂ → ℂ}
    (hΦ : ContDiffOn ℝ 1 (fun q : ℂ × ℂ => Φ q.1 q.2) (P ×ˢ O)) :
    ContDiffOn ℝ 1 (fun q : ℂ × ℂ => ∮ ζ in C(0, R), (ζ - q.2)⁻¹ • Φ q.1 ζ) (P ×ˢ {z | ‖z‖ ≠ R}) := by
  have hV : IsOpen (P ×ˢ {z : ℂ | ‖z‖ ≠ R}) := hP.prod (isOpen_ne_fun continuous_norm continuous_const)
  obtain ⟨K, hK⟩ : ∃ K : (ℂ × ℂ) × ℝ → ℂ, K = fun p =>
      (circleMap 0 R p.2 * I) * ((circleMap 0 R p.2 - p.1.2)⁻¹ * Φ p.1.1 (circleMap 0 R p.2)) := ⟨_, rfl⟩
  have hW : IsOpen ((P ×ˢ {z : ℂ | ‖z‖ ≠ R}) ×ˢ (univ : Set ℝ)) := hV.prod isOpen_univ
  have hγ : ContDiff ℝ 1 (circleMap (0 : ℂ) R) := contDiff_circleMap 0 R
  have hγn : ∀ θ : ℝ, ‖circleMap 0 R θ‖ = R := fun θ => by
    rw [← mem_sphere_zero_iff_norm]; exact circleMap_mem_sphere 0 hR.le θ
  have hKc : ContDiffOn ℝ 1 K ((P ×ˢ {z : ℂ | ‖z‖ ≠ R}) ×ˢ univ) := by
    rw [hK]
    have h1 : ContDiffOn ℝ 1 (fun p : (ℂ × ℂ) × ℝ => circleMap 0 R p.2 * I) ((P ×ˢ {z : ℂ | ‖z‖ ≠ R}) ×ˢ univ) :=
      ((hγ.comp contDiff_snd).mul contDiff_const).contDiffOn
    have h2 : ContDiffOn ℝ 1 (fun p : (ℂ × ℂ) × ℝ => (circleMap 0 R p.2 - p.1.2)⁻¹)
        ((P ×ˢ {z : ℂ | ‖z‖ ≠ R}) ×ˢ univ) := by
      refine ((hγ.comp contDiff_snd).sub (contDiff_snd.comp contDiff_fst)).contDiffOn.inv ?_
      intro p hp h0
      have h3 : circleMap 0 R p.2 = p.1.2 := sub_eq_zero.mp h0
      have h4 := hγn p.2
      rw [h3] at h4
      exact hp.1.2 h4
    have h3 : ContDiffOn ℝ 1 (fun p : (ℂ × ℂ) × ℝ => Φ p.1.1 (circleMap 0 R p.2))
        ((P ×ˢ {z : ℂ | ‖z‖ ≠ R}) ×ˢ univ) := by
      have hm : ContDiff ℝ 1 (fun p : (ℂ × ℂ) × ℝ => (p.1.1, circleMap 0 R p.2)) :=
        (contDiff_fst.comp contDiff_fst).prodMk (hγ.comp contDiff_snd)
      exact hΦ.comp hm.contDiffOn fun p hp => ⟨hp.1.1, hRO (circleMap_mem_sphere 0 hR.le p.2)⟩
    exact h1.mul (h2.mul h3)
  have hKd : DifferentiableOn ℝ K ((P ×ˢ {z : ℂ | ‖z‖ ≠ R}) ×ˢ univ) := hKc.differentiableOn one_ne_zero
  have hKf : ContinuousOn (fderiv ℝ K) ((P ×ˢ {z : ℂ | ‖z‖ ≠ R}) ×ˢ univ) :=
    hKc.continuousOn_fderiv_of_isOpen hW le_rfl
  have hrep : ∀ q ∈ P ×ˢ {z : ℂ | ‖z‖ ≠ R},
      (∮ ζ in C(0, R), (ζ - q.2)⁻¹ • Φ q.1 ζ) = ∫ θ in (0 : ℝ)..2 * π, K (q, θ) := by
    intro q _
    rw [hK]
    simp only [circleIntegral, deriv_circleMap, smul_eq_mul]
  refine ContDiffOn.congr ?_ hrep
  refine s3g_param_integral hV (by positivity) (Φ := fun x θ => K (x, θ))
    (Φ' := fun x θ => (fderiv ℝ K (x, θ)).comp (ContinuousLinearMap.inl ℝ (ℂ × ℂ) ℝ)) ?_ ?_ ?_
  · intro x hx θ _
    have hm : (x, θ) ∈ (P ×ˢ {z : ℂ | ‖z‖ ≠ R}) ×ˢ (univ : Set ℝ) := ⟨hx, mem_univ θ⟩
    have hF := ((hKd _ hm).differentiableAt (hW.mem_nhds hm)).hasFDerivAt
    have hl : HasFDerivAt (fun y : ℂ × ℂ => (y, θ)) (ContinuousLinearMap.inl ℝ (ℂ × ℂ) ℝ) x :=
      (hasFDerivAt_id x).prodMk (hasFDerivAt_const θ x)
    exact HasFDerivAt.comp (g := K) (f := fun y : ℂ × ℂ => (y, θ)) x hF hl
  · exact hKc.continuousOn.mono (prod_mono subset_rfl (subset_univ _))
  · exact (hKf.mono (prod_mono subset_rfl (subset_univ _))).clm_comp continuousOn_const

/-! ### Boundary facts for (b): the sphere welding `ĝ = w^ν ∘ (w_ν)⁻¹` (下属3) -/

/-- The preimage under `w_μ` of a finite point of modulus `≥ 1`: on `𝕊¹` it is a point of `𝕊¹`, off `𝔻̄` it is not
in `𝔻̄`; and `w^μ` of it is finite. -/
theorem s3g_sphere_pre {μ : LinfStar} (hμ : μ ∈ LinfStarBall) (z : ℂ) :
    wB μ (Function.invFun (wAS μ) (z : ExtPlane)) ≠ extInf ∧
      (‖z‖ = 1 → ∃ u : ℂ, ‖u‖ = 1 ∧ Function.invFun (wAS μ) (z : ExtPlane) = (u : ExtPlane)) ∧
      (1 < ‖z‖ → ∀ u : ℂ, ‖u‖ ≤ 1 → Function.invFun (wAS μ) (z : ExtPlane) ≠ (u : ExtPlane)) := by
  have hri : ∀ y, wAS μ (Function.invFun (wAS μ) y) = y :=
    Function.rightInverse_invFun (wAS_bijective μ).2
  refine ⟨fun h => ?_, fun hz => ?_, fun hz u hu he => ?_⟩
  · have hp := (fB_normalization μ).2.2 ⟨wB μ, (wB_spec hμ).1⟩
    have he := (wB_bijective μ).1 (h.trans hp.symm)
    have h2 := congrArg (wAS μ) he
    rw [hri, hri] at h2
    exact OnePoint.coe_ne_infty z h2
  · obtain ⟨v, hv⟩ : ∃ v, v = Function.invFun (wAS μ) (z : ExtPlane) := ⟨_, rfl⟩
    rw [← hv]
    have hwv : wAS μ v = (z : ExtPlane) := by rw [hv]; exact hri _
    induction v using OnePoint.rec with
    | infty =>
      exfalso
      rcases wAS_maps_infty hμ with h | ⟨u, hu, h⟩
      · rw [h] at hwv
        exact OnePoint.coe_ne_infty z hwv.symm
      · rw [h] at hwv
        have := OnePoint.coe_injective hwv
        rw [this, hz] at hu
        exact lt_irrefl _ hu
    | coe u =>
      refine ⟨u, ?_, rfl⟩
      rcases lt_trichotomy ‖u‖ 1 with h | h | h
      · exfalso
        obtain ⟨w, hw, hwe⟩ := wAS_maps_disc hμ h
        rw [hwe] at hwv
        have := OnePoint.coe_injective hwv
        rw [this, hz] at hw
        exact lt_irrefl _ hw
      · exact h
      · exfalso
        rcases wAS_maps_ext hμ h with he | ⟨w, hw, hwe⟩
        · rw [he] at hwv
          exact OnePoint.coe_ne_infty z hwv.symm
        · rw [hwe] at hwv
          have := OnePoint.coe_injective hwv
          rw [this, hz] at hw
          exact lt_irrefl _ hw
  · have hwv : wAS μ (u : ExtPlane) = (z : ExtPlane) := by rw [← he]; exact hri _
    rcases hu.lt_or_eq with h | h
    · obtain ⟨w, hw, hwe⟩ := wAS_maps_disc hμ h
      rw [hwe] at hwv
      have := OnePoint.coe_injective hwv
      rw [this] at hw
      linarith
    · obtain ⟨w, hw, hwe⟩ := wAS_maps_circle hμ h
      rw [hwe] at hwv
      have := OnePoint.coe_injective hwv
      rw [this] at hw
      linarith

/-- On `𝔻*`, `g_μ = finPart (w^μ ∘ (w_μ)⁻¹)`. -/
theorem s3g_gMu_sphere {μ : LinfStar} (hμ : μ ∈ LinfStarBall) {z : ℂ} (hz : z ∈ unitDiscExterior) :
    gMu μ z = finPart (wB μ (Function.invFun (wAS μ) (z : ExtPlane))) := by
  rw [← gMu_sphere_factorization hμ hz]
  exact (finPart_coe _).symm

/-- Joint continuity of `ĝ(t, z) = finPart (w^{ν_t} ((w_{ν_t})⁻¹ z))` along a continuous curve `ν`. -/
theorem s3g_ghat_cont {ν : ℂ → LinfStar} {P : Set ℂ} (hν : ∀ t ∈ P, ν t ∈ LinfStarBall)
    (hνc : ∀ t ∈ P, ContinuousAt ν t) :
    ContinuousOn (fun q : ℂ × ℂ => finPart (wB (ν q.1) (Function.invFun (wAS (ν q.1)) (q.2 : ExtPlane))))
      (P ×ˢ univ) := by
  obtain ⟨A, hA⟩ : ∃ A : LinfStar × ExtPlane → ExtPlane, A = fun p => Function.invFun (wAS p.1) p.2 := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B : LinfStar × ExtPlane → ExtPlane, B = fun p => wB p.1 p.2 := ⟨_, rfl⟩
  have hAc : ContinuousOn A (LinfStarBall ×ˢ univ) := by rw [hA]; exact AppA.acc_wAS_inv_cont
  have hBc : ContinuousOn B (LinfStarBall ×ˢ univ) := by rw [hB]; exact AppA.acc_wB_cont
  obtain ⟨m1, hm1⟩ : ∃ m1 : ℂ × ℂ → LinfStar × ExtPlane, m1 = fun q => (ν q.1, ((q.2 : ℂ) : ExtPlane)) := ⟨_, rfl⟩
  have hm1c : ContinuousOn m1 (P ×ˢ univ) := by
    intro q hq
    rw [hm1]
    exact (((hνc q.1 hq.1).comp continuousAt_fst).prodMk
      (OnePoint.continuous_coe.continuousAt.comp continuousAt_snd)).continuousWithinAt
  have hm1s : MapsTo m1 (P ×ˢ univ) (LinfStarBall ×ˢ univ) := by
    intro q hq
    rw [hm1]
    exact ⟨hν q.1 hq.1, mem_univ _⟩
  obtain ⟨m2, hm2⟩ : ∃ m2 : ℂ × ℂ → LinfStar × ExtPlane, m2 = fun q => (ν q.1, A (m1 q)) := ⟨_, rfl⟩
  have hm2c : ContinuousOn m2 (P ×ˢ univ) := by
    intro q hq
    rw [hm2]
    exact (((hνc q.1 hq.1).comp continuousAt_fst).continuousWithinAt).prodMk
      ((hAc.comp hm1c hm1s) q hq)
  have hm2s : MapsTo m2 (P ×ˢ univ) (LinfStarBall ×ˢ univ) := by
    intro q hq
    rw [hm2]
    exact ⟨hν q.1 hq.1, mem_univ _⟩
  have hBm : ContinuousOn (fun q => B (m2 q)) (P ×ˢ univ) := hBc.comp hm2c hm2s
  have hfe : (fun q : ℂ × ℂ => finPart (wB (ν q.1) (Function.invFun (wAS (ν q.1)) (q.2 : ExtPlane)))) =
      fun q => finPart (B (m2 q)) := by
    funext q
    rw [hB, hm2, hA, hm1]
  rw [hfe]
  intro q hq
  have hne : B (m2 q) ≠ extInf := by
    rw [hB, hm2, hA, hm1]
    exact (s3g_sphere_pre (hν q.1 hq.1) q.2).1
  exact ContinuousAt.comp_continuousWithinAt (g := finPart) (s5rh_finPart_contAt hne) (hBm q hq)

/-- Joint real-analyticity of `(t, z) ↦ 𝗀_{ν_t}(z)` on `𝔻*` along a real-analytic curve `ν`. -/
theorem s3g_gsans_analytic {ν : ℂ → LinfStar} {P : Set ℂ} (hν : ∀ t ∈ P, ν t ∈ LinfStarBall)
    (hνa : ∀ t ∈ P, AnalyticAt ℝ ν t) {q : ℂ × ℂ} (hq : q ∈ P ×ˢ unitDiscExterior) :
    AnalyticAt ℝ (fun q : ℂ × ℂ => gsans (ν q.1) q.2) q := by
  obtain ⟨hz0, hu⟩ := s3g_inv_mem hq.2
  have hE : AnalyticAt ℝ (fun p : (LinfStar × LinfStar) × ℂ => s5cf_exterior_reciprocal p.1 p.2)
      ((ν q.1, star (ν q.1)), q.2⁻¹) :=
    (s5cf_exterior_reciprocal_analytic (hν q.1 hq.1) hu).restrictScalars
  have hn : AnalyticAt ℝ ν q.1 := hνa q.1 hq.1
  have hm : AnalyticAt ℝ (fun q : ℂ × ℂ => ((ν q.1, star (ν q.1)), q.2⁻¹)) q := by
    have h1 : AnalyticAt ℝ (fun q : ℂ × ℂ => ν q.1) q :=
      AnalyticAt.comp_of_eq (g := ν) (f := fun q : ℂ × ℂ => q.1) hn analyticAt_fst rfl
    have h2 : AnalyticAt ℝ (fun q : ℂ × ℂ => star (ν q.1)) q :=
      AnalyticAt.comp_of_eq (g := fun μ : LinfStar => star μ) (f := fun q : ℂ × ℂ => ν q.1)
        (s5cf_star_analytic _) h1 rfl
    have h3 : AnalyticAt ℝ (fun q : ℂ × ℂ => q.2⁻¹) q := by
      have : AnalyticAt ℂ (fun w : ℂ => w⁻¹) q.2 := analyticAt_inv hz0
      exact AnalyticAt.comp_of_eq (g := fun w : ℂ => w⁻¹) (f := fun q : ℂ × ℂ => q.2) this.restrictScalars
        analyticAt_snd rfl
    exact (h1.prod h2).prod h3
  have hc : AnalyticAt ℝ (fun q : ℂ × ℂ => s5cf_exterior_reciprocal (ν q.1, star (ν q.1)) q.2⁻¹) q :=
    AnalyticAt.comp_of_eq (g := fun p : (LinfStar × LinfStar) × ℂ => s5cf_exterior_reciprocal p.1 p.2)
      (f := fun q : ℂ × ℂ => ((ν q.1, star (ν q.1)), q.2⁻¹)) hE hm rfl
  have hne : s5cf_exterior_reciprocal (ν q.1, star (ν q.1)) q.2⁻¹ ≠ 0 := by
    rw [s3g_recip (hν q.1 hq.1) hq.2, s3g_gsans_eq (hν q.1 hq.1)]
    exact inv_ne_zero (gMu_exterior_ne_zero (hν q.1 hq.1) hq.2)
  have hev : (fun q : ℂ × ℂ => gsans (ν q.1) q.2) =ᶠ[𝓝 q]
      fun q : ℂ × ℂ => (s5cf_exterior_reciprocal (ν q.1, star (ν q.1)) q.2⁻¹)⁻¹ := by
    have hO : IsOpen (univ ×ˢ unitDiscExterior : Set (ℂ × ℂ)) :=
      isOpen_univ.prod (isOpen_lt continuous_const continuous_norm)
    have hPO : ∀ᶠ x in 𝓝 q, x ∈ (univ ×ˢ unitDiscExterior : Set (ℂ × ℂ)) :=
      hO.mem_nhds ⟨mem_univ _, hq.2⟩
    have hPP : ∀ᶠ x : ℂ × ℂ in 𝓝 q, ν x.1 ∈ LinfStarBall := by
      have hc1 : ContinuousAt (fun x : ℂ × ℂ => ν x.1) q := hn.continuousAt.comp continuousAt_fst
      exact hc1.preimage_mem_nhds (isOpen_ball.mem_nhds (hν q.1 hq.1))
    filter_upwards [hPO, hPP] with x hx hxν
    rw [s3g_recip hxν hx.2, inv_inv]
  exact (hc.inv hne).congr hev.symm

/-- `𝗀_μ` is holomorphic on `𝔻*` (through the S5 reciprocal chart). -/
theorem s3g_gsans_holo {μ : LinfStar} (hμ : μ ∈ LinfStarBall) {z : ℂ} (hz : z ∈ unitDiscExterior) :
    DifferentiableAt ℂ (gsans μ) z := by
  obtain ⟨hz0, hu⟩ := s3g_inv_mem hz
  have hE : AnalyticAt ℂ (fun u => s5cf_exterior_reciprocal (μ, star μ) u) z⁻¹ :=
    AnalyticAt.comp_of_eq (g := fun q : (LinfStar × LinfStar) × ℂ => s5cf_exterior_reciprocal q.1 q.2)
      (f := fun u : ℂ => ((μ, star μ), u)) (s5cf_exterior_reciprocal_analytic hμ hu)
      (analyticAt_const.prod analyticAt_id) rfl
  have hc : DifferentiableAt ℂ (fun w : ℂ => s5cf_exterior_reciprocal (μ, star μ) w⁻¹) z :=
    DifferentiableAt.comp (g := fun u => s5cf_exterior_reciprocal (μ, star μ) u) (f := fun w : ℂ => w⁻¹) z
      hE.differentiableAt (differentiableAt_inv hz0)
  have hne : s5cf_exterior_reciprocal (μ, star μ) z⁻¹ ≠ 0 := by
    rw [s3g_recip hμ hz, s3g_gsans_eq hμ]
    exact inv_ne_zero (gMu_exterior_ne_zero hμ hz)
  have hev : gsans μ =ᶠ[𝓝 z] fun w => (s5cf_exterior_reciprocal (μ, star μ) w⁻¹)⁻¹ := by
    filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds hz] with w hw
    rw [s3g_recip hμ hw, inv_inv]
  exact (hc.inv hne).congr_of_eventuallyEq hev

/-- `R z = 1/z̄` is smooth (over `ℝ`) away from `0`. -/
theorem s3g_cr_contDiffAt {z : ℂ} (hz : z ≠ 0) : ContDiffAt ℝ 1 circleReflect z := by
  have h1 : ContDiffAt ℝ 1 (fun w : ℂ => conj w) z := Complex.conjCLE.contDiff.contDiffAt
  have h2 : ContDiffAt ℝ 1 (fun w : ℂ => (conj w)⁻¹) z := h1.inv ((map_ne_zero _).mpr hz)
  have he : circleReflect = fun w : ℂ => (conj w)⁻¹ := by
    funext w
    rw [circleReflect, one_div]
  rw [he]
  exact h2

/-! ### Reflection across `𝕊¹` and annuli (下属3) -/

/-- An open set containing `𝕊¹` contains an annulus `1 - δ < |z| < 1 + δ`. -/
theorem s3g_annulus_of_sphere {v : Set ℂ} (hv : IsOpen v) (hs : sphere (0 : ℂ) 1 ⊆ v) :
    ∃ δ > 0, δ < 1 ∧ ∀ z : ℂ, 1 - δ < ‖z‖ → ‖z‖ < 1 + δ → z ∈ v := by
  obtain ⟨δ, hδ, hth⟩ := (isCompact_sphere (0 : ℂ) 1).exists_thickening_subset_open hv hs
  have hm1 := min_le_left δ (1 / 2)
  have hm2 := min_le_right δ (1 / 2)
  refine ⟨min δ (1 / 2), lt_min hδ (by norm_num), by linarith, fun z h1 h2 => hth ?_⟩
  have hn : 0 < ‖z‖ := by linarith
  have hz0 : z ≠ 0 := norm_pos_iff.mp hn
  have hc : (‖z‖ : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [mem_thickening_iff]
  refine ⟨z / (‖z‖ : ℂ), ?_, ?_⟩
  · rw [mem_sphere_zero_iff_norm, norm_div, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _),
      div_self hn.ne']
  · have he : z - z / (‖z‖ : ℂ) = (((‖z‖ - 1) / ‖z‖ : ℝ) : ℂ) * z := by
      push_cast
      field_simp
    rw [dist_eq_norm, he, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_div, abs_of_pos hn,
      div_mul_cancel₀ _ hn.ne', abs_lt]
    constructor <;> linarith

/-- `z ↦ R(h(R z))` with `R z = 1/z̄` is holomorphic where `h` is and `h ≠ 0`. -/
theorem s3g_cr_diff {h : ℂ → ℂ} {z : ℂ} (hz : z ≠ 0) (hd : DifferentiableAt ℂ h (circleReflect z))
    (hne : h (circleReflect z) ≠ 0) : DifferentiableAt ℂ (fun w => circleReflect (h (circleReflect w))) z := by
  have hcz : conj z ≠ 0 := (map_ne_zero _).mpr hz
  have h1 : DifferentiableAt ℂ (fun w : ℂ => 1 / w) (conj z) :=
    (differentiableAt_const _).div differentiableAt_id hcz
  have hk : DifferentiableAt ℂ (fun w : ℂ => 1 / h (1 / w)) (conj z) :=
    (differentiableAt_const _).div (DifferentiableAt.comp (g := h) (f := fun w : ℂ => 1 / w) (conj z) hd h1) hne
  have he : (fun w => circleReflect (h (circleReflect w))) = conj ∘ (fun w : ℂ => 1 / h (1 / w)) ∘ conj := by
    funext w
    simp only [circleReflect, Function.comp, map_div₀, map_one]
  have h2 := hk.conj_conj
  rw [Complex.conj_conj] at h2
  rw [he]
  exact h2

/-- **Reflection across `𝕊¹`.** If `Φ` is holomorphic on `1 < |z| < b`, continuous on `1 ≤ |z| < b`, of modulus
`1` on `𝕊¹` and `> 1` off it, then its reflection extension is holomorphic on `1/b < |z| < b`. -/
theorem s3g_reflect {Φ : ℂ → ℂ} {b : ℝ} (hb : 1 < b)
    (hd : DifferentiableOn ℂ Φ {z | 1 < ‖z‖ ∧ ‖z‖ < b})
    (hc : ContinuousOn Φ {z | 1 ≤ ‖z‖ ∧ ‖z‖ < b})
    (hn1 : ∀ z : ℂ, ‖z‖ = 1 → ‖Φ z‖ = 1) (hn : ∀ z : ℂ, 1 < ‖z‖ → ‖z‖ < b → 1 < ‖Φ z‖) :
    DifferentiableOn ℂ (fun z => if ‖z‖ ≤ 1 then circleReflect (Φ (circleReflect z))
        else circleReflect (circleReflect (Φ (circleReflect (circleReflect z))))) {z | b⁻¹ < ‖z‖ ∧ ‖z‖ < b} := by
  have hb0 : 0 < b := by linarith
  have hbi : b⁻¹ < 1 := inv_lt_one_of_one_lt₀ hb
  have hbi0 : 0 < b⁻¹ := inv_pos.mpr hb0
  obtain ⟨U, hU⟩ : ∃ U : Set ℂ, U = {z | b⁻¹ < ‖z‖ ∧ ‖z‖ < b} := ⟨_, rfl⟩
  have hUo : IsOpen U := by
    rw [hU]
    exact (isOpen_lt continuous_const continuous_norm).inter (isOpen_lt continuous_norm continuous_const)
  have hcrn : ∀ z : ℂ, ‖circleReflect z‖ = ‖z‖⁻¹ := norm_circleReflect
  have hUA : IsCircleSymmetricNbhd U (sphere 0 1) := by
    refine ⟨hUo, ?_, ?_⟩
    · ext z
      rw [hU]
      simp only [mem_inter_iff, mem_setOf_eq, mem_sphere_zero_iff_norm]
      constructor
      · exact fun h => h.2
      · intro h
        rw [h]
        exact ⟨⟨hbi, hb⟩, rfl⟩
    · intro z hz
      rw [hU] at hz ⊢
      have hz0 : 0 < ‖z‖ := lt_trans hbi0 hz.1
      refine ⟨?_, ?_⟩
      · rw [hcrn]
        exact inv_strictAnti₀ hz0 hz.2
      · rw [hcrn]
        have := inv_strictAnti₀ hbi0 hz.1
        rwa [inv_inv] at this
  -- the inner function `f = R ∘ Φ ∘ R`
  have hmapin : ∀ z : ℂ, b⁻¹ < ‖z‖ → ‖z‖ ≤ 1 → 1 ≤ ‖circleReflect z‖ ∧ ‖circleReflect z‖ < b := by
    intro z h1 h2
    have hz0 : 0 < ‖z‖ := lt_trans hbi0 h1
    rw [hcrn]
    refine ⟨one_le_inv₀ hz0 |>.mpr h2, ?_⟩
    have := inv_strictAnti₀ hbi0 h1
    rwa [inv_inv] at this
  have hΦne : ∀ w : ℂ, 1 ≤ ‖w‖ → ‖w‖ < b → Φ w ≠ 0 := by
    intro w h1 h2 h0
    rcases h1.lt_or_eq with h | h
    · have := hn w h h2
      rw [h0, norm_zero] at this
      linarith
    · have := hn1 w h.symm
      rw [h0, norm_zero] at this
      exact zero_ne_one this
  have hf : DifferentiableOn ℂ (fun z => circleReflect (Φ (circleReflect z))) (U ∩ unitDisc) := by
    intro z hz
    rw [hU] at hz
    have hz1 : ‖z‖ < 1 := mem_ball_zero_iff.mp hz.2
    have hz0 : z ≠ 0 := norm_pos_iff.mp (lt_trans hbi0 hz.1.1)
    obtain ⟨h1, h2⟩ := hmapin z hz.1.1 hz1.le
    have h1' : 1 < ‖circleReflect z‖ := by
      rw [hcrn]
      exact (one_lt_inv₀ (norm_pos_iff.mpr hz0)).mpr hz1
    have hdo : DifferentiableAt ℂ Φ (circleReflect z) :=
      hd.differentiableAt ((isOpen_lt continuous_const continuous_norm).inter
        (isOpen_lt continuous_norm continuous_const) |>.mem_nhds ⟨h1', h2⟩)
    exact (s3g_cr_diff hz0 hdo (hΦne _ h1 h2)).differentiableWithinAt
  have hcont : ContinuousOn (fun z => circleReflect (Φ (circleReflect z))) ((U ∩ unitDisc) ∪ sphere 0 1) := by
    intro z hz
    have hzz : b⁻¹ < ‖z‖ ∧ ‖z‖ ≤ 1 := by
      rcases hz with hz | hz
      · rw [hU] at hz
        exact ⟨hz.1.1, (mem_ball_zero_iff.mp hz.2).le⟩
      · rw [mem_sphere_zero_iff_norm] at hz
        rw [hz]
        exact ⟨hbi, le_rfl⟩
    have hz0 : z ≠ 0 := norm_pos_iff.mp (lt_trans hbi0 hzz.1)
    obtain ⟨h1, h2⟩ := hmapin z hzz.1 hzz.2
    have hcr : ContinuousAt circleReflect z := continuousAt_circleReflect hz0
    have hms : MapsTo circleReflect ((U ∩ unitDisc) ∪ sphere 0 1) {w : ℂ | 1 ≤ ‖w‖ ∧ ‖w‖ < b} := by
      intro w hw
      have hww : b⁻¹ < ‖w‖ ∧ ‖w‖ ≤ 1 := by
        rcases hw with hw | hw
        · rw [hU] at hw
          exact ⟨hw.1.1, (mem_ball_zero_iff.mp hw.2).le⟩
        · rw [mem_sphere_zero_iff_norm] at hw
          rw [hw]
          exact ⟨hbi, le_rfl⟩
      exact hmapin w hww.1 hww.2
    have hΦc : ContinuousWithinAt (fun z => Φ (circleReflect z)) ((U ∩ unitDisc) ∪ sphere 0 1) z :=
      ContinuousWithinAt.comp (g := Φ) (f := circleReflect) (hc _ ⟨h1, h2⟩) hcr.continuousWithinAt hms
    have hΦ0 : Φ (circleReflect z) ≠ 0 := hΦne _ h1 h2
    have hcr2 : ContinuousAt circleReflect (Φ (circleReflect z)) := continuousAt_circleReflect hΦ0
    exact ContinuousAt.comp_continuousWithinAt (g := circleReflect) hcr2 hΦc
  have hnorm : ∀ z ∈ sphere (0 : ℂ) 1, ‖circleReflect (Φ (circleReflect z))‖ = 1 := by
    intro z hz
    have hz1 : ‖z‖ = 1 := mem_sphere_zero_iff_norm.mp hz
    rw [circleReflect_of_norm_eq_one hz1, hcrn, hn1 z hz1, inv_one]
  intro z hz
  have hzU : z ∈ U := by rw [hU]; exact hz
  have hz0 : z ≠ 0 := norm_pos_iff.mp (lt_trans hbi0 hz.1)
  rcases lt_trichotomy ‖z‖ 1 with h | h | h
  · have hev : (fun z => if ‖z‖ ≤ 1 then circleReflect (Φ (circleReflect z))
        else circleReflect (circleReflect (Φ (circleReflect (circleReflect z))))) =ᶠ[𝓝 z]
        fun z => circleReflect (Φ (circleReflect z)) := by
      filter_upwards [(isOpen_lt continuous_norm continuous_const).mem_nhds h] with w hw
      rw [if_pos (le_of_lt hw)]
    refine (DifferentiableAt.congr_of_eventuallyEq ?_ hev).differentiableWithinAt
    exact (hf z ⟨hzU, mem_ball_zero_iff.mpr h⟩).differentiableAt
      ((hUo.inter isOpen_ball).mem_nhds ⟨hzU, mem_ball_zero_iff.mpr h⟩)
  · exact (differentiableAt_circleReflectExtend_norm_one_of_mem_arc hUA hf hcont hnorm
      (mem_sphere_zero_iff_norm.mpr h)).differentiableWithinAt
  · have hO : IsOpen {w : ℂ | 1 < ‖w‖ ∧ ‖w‖ < b} :=
      (isOpen_lt continuous_const continuous_norm).inter (isOpen_lt continuous_norm continuous_const)
    have hzO : z ∈ {w : ℂ | 1 < ‖w‖ ∧ ‖w‖ < b} := ⟨h, hz.2⟩
    have hev : (fun z => if ‖z‖ ≤ 1 then circleReflect (Φ (circleReflect z))
        else circleReflect (circleReflect (Φ (circleReflect (circleReflect z))))) =ᶠ[𝓝 z] Φ := by
      filter_upwards [hO.mem_nhds hzO] with w hw
      have hw0 : w ≠ 0 := norm_pos_iff.mp (lt_trans one_pos hw.1)
      rw [if_neg (not_le.mpr hw.1), circleReflect_circleReflect hw0,
        circleReflect_circleReflect (hΦne w hw.1.le hw.2)]
    exact ((hd.differentiableAt (hO.mem_nhds hzO)).congr_of_eventuallyEq hev).differentiableWithinAt

/-- Values, size and injectivity of the reflection extension. -/
theorem s3g_reflect_facts {Φ : ℂ → ℂ} {b : ℝ} (hb : 1 < b)
    (hn1 : ∀ z : ℂ, ‖z‖ = 1 → ‖Φ z‖ = 1) (hn : ∀ z : ℂ, 1 < ‖z‖ → ‖z‖ < b → 1 < ‖Φ z‖)
    (hi : InjOn Φ {z | 1 ≤ ‖z‖ ∧ ‖z‖ < b}) {E : ℂ → ℂ}
    (hE : E = fun z => if ‖z‖ ≤ 1 then circleReflect (Φ (circleReflect z))
        else circleReflect (circleReflect (Φ (circleReflect (circleReflect z))))) :
    (∀ z : ℂ, 1 ≤ ‖z‖ → ‖z‖ < b → E z = Φ z) ∧
      (∀ z : ℂ, b⁻¹ < ‖z‖ → ‖z‖ < 1 → ‖E z‖ < 1 ∧ E z = circleReflect (Φ (circleReflect z))) ∧
      InjOn E {z | b⁻¹ < ‖z‖ ∧ ‖z‖ < b} := by
  have hb0 : 0 < b := by linarith
  have hbi0 : 0 < b⁻¹ := inv_pos.mpr hb0
  have hcrn : ∀ z : ℂ, ‖circleReflect z‖ = ‖z‖⁻¹ := norm_circleReflect
  have hΦge : ∀ w : ℂ, 1 ≤ ‖w‖ → ‖w‖ < b → 1 ≤ ‖Φ w‖ := by
    intro w h1 h2
    rcases h1.lt_or_eq with h | h
    · exact (hn w h h2).le
    · exact (hn1 w h.symm).ge
  have hΦne : ∀ w : ℂ, 1 ≤ ‖w‖ → ‖w‖ < b → Φ w ≠ 0 := fun w h1 h2 h0 => by
    have := hΦge w h1 h2
    rw [h0, norm_zero] at this
    linarith
  have hin : ∀ z : ℂ, b⁻¹ < ‖z‖ → ‖z‖ < 1 → 1 < ‖circleReflect z‖ ∧ ‖circleReflect z‖ < b := by
    intro z h1 h2
    have hz0 : 0 < ‖z‖ := lt_trans hbi0 h1
    rw [hcrn]
    refine ⟨(one_lt_inv₀ hz0).mpr h2, ?_⟩
    have := inv_strictAnti₀ hbi0 h1
    rwa [inv_inv] at this
  have h1 : ∀ z : ℂ, 1 ≤ ‖z‖ → ‖z‖ < b → E z = Φ z := by
    intro z hz1 hz2
    rw [hE]
    rcases hz1.lt_or_eq with h | h
    · have hz0 : z ≠ 0 := norm_pos_iff.mp (lt_trans one_pos h)
      show (if ‖z‖ ≤ 1 then _ else _) = _
      rw [if_neg (not_le.mpr h), circleReflect_circleReflect hz0,
        circleReflect_circleReflect (hΦne z hz1 hz2)]
    · show (if ‖z‖ ≤ 1 then _ else _) = _
      rw [if_pos h.symm.le, circleReflect_of_norm_eq_one h.symm,
        circleReflect_of_norm_eq_one (hn1 z h.symm)]
  have h2 : ∀ z : ℂ, b⁻¹ < ‖z‖ → ‖z‖ < 1 → ‖E z‖ < 1 ∧ E z = circleReflect (Φ (circleReflect z)) := by
    intro z hz1 hz2
    have he : E z = circleReflect (Φ (circleReflect z)) := by
      rw [hE]
      show (if ‖z‖ ≤ 1 then _ else _) = _
      rw [if_pos hz2.le]
    refine ⟨?_, he⟩
    obtain ⟨hc1, hc2⟩ := hin z hz1 hz2
    rw [he, hcrn]
    exact inv_lt_one_of_one_lt₀ (hn _ hc1 hc2)
  refine ⟨h1, h2, fun x hx y hy hxy => ?_⟩
  have hx0 : x ≠ 0 := norm_pos_iff.mp (lt_trans hbi0 hx.1)
  have hy0 : y ≠ 0 := norm_pos_iff.mp (lt_trans hbi0 hy.1)
  rcases lt_or_ge ‖x‖ 1 with hx1 | hx1 <;> rcases lt_or_ge ‖y‖ 1 with hy1 | hy1
  · obtain ⟨-, hex⟩ := h2 x hx.1 hx1
    obtain ⟨-, hey⟩ := h2 y hy.1 hy1
    rw [hex, hey] at hxy
    obtain ⟨hcx1, hcx2⟩ := hin x hx.1 hx1
    obtain ⟨hcy1, hcy2⟩ := hin y hy.1 hy1
    have h3 := congrArg circleReflect hxy
    rw [circleReflect_circleReflect (hΦne _ hcx1.le hcx2), circleReflect_circleReflect (hΦne _ hcy1.le hcy2)] at h3
    have h4 := hi ⟨hcx1.le, hcx2⟩ ⟨hcy1.le, hcy2⟩ h3
    have h5 := congrArg circleReflect h4
    rwa [circleReflect_circleReflect hx0, circleReflect_circleReflect hy0] at h5
  · exfalso
    have h3 := (h2 x hx.1 hx1).1
    rw [hxy, h1 y hy1 hy.2] at h3
    linarith [hΦge y hy1 hy.2]
  · exfalso
    have h3 := (h2 y hy.1 hy1).1
    rw [← hxy, h1 x hx1 hx.2] at h3
    linarith [hΦge x hx1 hx.2]
  · rw [h1 x hx1 hx.2, h1 y hy1 hy.2] at hxy
    exact hi ⟨hx1, hx.2⟩ ⟨hy1, hy.2⟩ hxy

/-! ### Tools for (b′): removability of `𝕊¹` and orientation of the welding extension (下属3) -/

/-- Removability of `𝕊¹` at a point of the slit plane (Morera across the line `Re w = 0` after `exp`). -/
theorem s3g_circle_removable_at {φ : ℂ → ℂ} {A : Set ℂ} (hA : IsOpen A) (hc : ContinuousOn φ A)
    (hd : ∀ z ∈ A, ‖z‖ ≠ 1 → DifferentiableAt ℂ φ z) {ζ : ℂ} (hζA : ζ ∈ A) (hζ : ζ ∈ slitPlane) :
    DifferentiableAt ℂ φ ζ := by
  have hV : IsOpen (Complex.exp ⁻¹' A) := hA.preimage Complex.continuous_exp
  have hψc : ContinuousOn (fun w => φ (Complex.exp w)) (Complex.exp ⁻¹' A) :=
    hc.comp Complex.continuous_exp.continuousOn (fun w hw => hw)
  have hψd : DifferentiableOn ℂ (fun w => φ (Complex.exp w)) (Complex.exp ⁻¹' A) := by
    refine differentiableOn_of_continuousOn_of_differentiableAt_off_line hV hψc 0 I I_ne_zero ?_
    intro w hw hre
    have him : ((w - 0) / I).im = -w.re := by simp [div_I]
    have hre' : w.re ≠ 0 := fun h0 => hre (by rw [him, h0, neg_zero])
    have hn : ‖Complex.exp w‖ ≠ 1 := by
      rw [Complex.norm_exp]
      exact fun h1 => hre' (Real.exp_eq_one_iff w.re |>.mp h1)
    exact DifferentiableAt.comp (g := φ) (f := Complex.exp) w (hd _ hw hn)
      Complex.differentiable_exp.differentiableAt
  have hζ0 : ζ ≠ 0 := slitPlane_ne_zero hζ
  have hmem : Complex.log ζ ∈ Complex.exp ⁻¹' A := by
    show Complex.exp (Complex.log ζ) ∈ A
    rw [Complex.exp_log hζ0]
    exact hζA
  have hψ : DifferentiableAt ℂ (fun w => φ (Complex.exp w)) (Complex.log ζ) :=
    hψd.differentiableAt (hV.mem_nhds hmem)
  have hcomp := DifferentiableAt.comp (g := fun w => φ (Complex.exp w)) (f := Complex.log) ζ hψ
    (Complex.differentiableAt_log hζ)
  refine hcomp.congr_of_eventuallyEq ?_
  filter_upwards [isOpen_ne.mem_nhds hζ0] with z hz
  show φ z = φ (Complex.exp (Complex.log z))
  rw [Complex.exp_log hz]

/-- **Removability of `𝕊¹`.** A function continuous on a symmetric open set and holomorphic off `𝕊¹` is
holomorphic. -/
theorem s3g_circle_removable {φ : ℂ → ℂ} {A : Set ℂ} (hA : IsOpen A) (hAn : ∀ z ∈ A, -z ∈ A)
    (hc : ContinuousOn φ A) (hd : ∀ z ∈ A, ‖z‖ ≠ 1 → DifferentiableAt ℂ φ z) : DifferentiableOn ℂ φ A := by
  intro ζ hζ
  by_cases hn : ‖ζ‖ = 1
  · by_cases hs : ζ ∈ slitPlane
    · exact (s3g_circle_removable_at hA hc hd hζ hs).differentiableWithinAt
    · have hs' : -ζ ∈ slitPlane := by
        rw [mem_slitPlane_iff] at hs ⊢
        push_neg at hs
        have hζ0 : ζ ≠ 0 := fun h => by rw [h, norm_zero] at hn; exact zero_ne_one hn
        have hre : ζ.re ≠ 0 := fun h => hζ0 (Complex.ext h hs.2)
        left
        rw [neg_re]
        exact neg_pos.mpr (lt_of_le_of_ne hs.1 hre)
      have hc' : ContinuousOn (fun z => φ (-z)) A :=
        hc.comp continuous_neg.continuousOn (fun z hz => hAn z hz)
      have hd' : ∀ z ∈ A, ‖z‖ ≠ 1 → DifferentiableAt ℂ (fun z => φ (-z)) z := by
        intro z hz hz1
        exact DifferentiableAt.comp (g := φ) (f := fun z : ℂ => -z) z
          (hd (-z) (hAn z hz) (by rwa [norm_neg])) differentiableAt_id.neg
      have h1 := s3g_circle_removable_at hA hc' hd' (hAn ζ hζ) hs'
      have h2 := DifferentiableAt.comp (g := fun z => φ (-z)) (f := fun z : ℂ => -z) ζ h1 differentiableAt_id.neg
      have he : (fun z => φ (-z)) ∘ (fun z : ℂ => -z) = φ := by
        funext z
        simp
      rw [he] at h2
      exact h2.differentiableWithinAt
  · exact (hd ζ hζ hn).differentiableWithinAt

/-- If `L g'(0) < 0` for a real-linear `L`, then `L ∘ g` drops just to the right of `0`. -/
theorem s3g_slope_neg {g : ℝ → ℂ} {g' : ℂ} (hg : HasDerivAt g g' 0) (L : ℂ →L[ℝ] ℝ) (hL : L g' < 0) :
    ∀ᶠ θ in 𝓝[>] (0 : ℝ), L (g θ) < L (g 0) := by
  have h := (hasDerivAt_iff_tendsto_slope.mp hg).mono_left (nhdsWithin_mono _ (fun x (hx : 0 < x) => hx.ne'))
  have h2 := (L.continuous.tendsto g').comp h
  filter_upwards [h2.eventually (Iio_mem_nhds hL), self_mem_nhdsWithin] with θ hθ hθ0
  have hθ0' : (0 : ℝ) < θ := hθ0
  have hθ' : L (slope g 0 θ) < 0 := hθ
  rw [slope_def_module, sub_zero, map_smul, map_sub, smul_eq_mul] at hθ'
  have h3 : L (g θ) - L (g 0) < 0 := by
    by_contra hc
    have : 0 ≤ θ⁻¹ * (L (g θ) - L (g 0)) := mul_nonneg (inv_nonneg.mpr hθ0'.le) (not_lt.mp hc)
    linarith
  linarith

/-- **Orientation.** A holomorphic injective extension `H` of the welding `w^A_μ` to an annulus maps the outer part
`1 < |z| < R` outside `𝕊¹`. -/
theorem s3g_orient {H : ℂ → ℂ} {ρ R : ℝ} (hρ : ρ < 1) (hR : 1 < R)
    (hd : DifferentiableOn ℂ H {z | ρ < ‖z‖ ∧ ‖z‖ < R}) (hi : InjOn H {z | ρ < ‖z‖ ∧ ‖z‖ < R})
    {μ : LinfStar} (hμ : μ ∈ LinfStarBall) (hc : ∀ z ∈ unitCircle, H z = wA μ z) :
    ∀ z : ℂ, 1 < ‖z‖ → ‖z‖ < R → 1 < ‖H z‖ := by
  have hA : IsOpen {z : ℂ | ρ < ‖z‖ ∧ ‖z‖ < R} :=
    (isOpen_lt continuous_const continuous_norm).inter (isOpen_lt continuous_norm continuous_const)
  have hcA : ∀ z : ℂ, ‖z‖ = 1 → z ∈ {z : ℂ | ρ < ‖z‖ ∧ ‖z‖ < R} := fun z hz =>
    ⟨by rw [hz]; exact hρ, by rw [hz]; exact hR⟩
  -- `H` maps `𝕊¹` onto `𝕊¹`
  have hcirc1 : ∀ z : ℂ, ‖z‖ = 1 → ‖H z‖ = 1 := by
    intro z hz
    rw [hc z hz]
    obtain ⟨u, hu, he⟩ := wAS_maps_circle hμ hz
    show ‖finPart (wAS μ (z : ExtPlane))‖ = 1
    rw [he]
    exact hu
  have hcirc2 : ∀ w : ℂ, ‖w‖ = 1 → ∃ ζ : ℂ, ‖ζ‖ = 1 ∧ H ζ = w := by
    intro w hw
    obtain ⟨u, hu, he⟩ := (s3g_sphere_pre hμ w).2.1 hw
    refine ⟨u, hu, ?_⟩
    rw [hc u hu]
    show finPart (wAS μ (u : ExtPlane)) = w
    rw [← he, Function.rightInverse_invFun (wAS_bijective μ).2]
    rfl
  have hne1 : ∀ z : ℂ, 1 < ‖z‖ → ‖z‖ < R → ‖H z‖ ≠ 1 := by
    intro z h1 h2 he
    obtain ⟨ζ, hζ, hHζ⟩ := hcirc2 _ he
    have := hi (hcA ζ hζ) ⟨by linarith, h2⟩ hHζ
    rw [← this, hζ] at h1
    exact lt_irrefl _ h1
  -- the outer annulus is preconnected
  have hpc : IsPreconnected {z : ℂ | 1 < ‖z‖ ∧ ‖z‖ < R} := by
    have himg : {z : ℂ | 1 < ‖z‖ ∧ ‖z‖ < R} =
        (fun p : ℝ × ℝ => (p.1 : ℂ) * Complex.exp (p.2 * I)) '' (Ioo 1 R ×ˢ univ) := by
      ext z
      constructor
      · intro hz
        refine ⟨(‖z‖, Complex.arg z), ⟨⟨hz.1, hz.2⟩, mem_univ _⟩, ?_⟩
        exact Complex.norm_mul_exp_arg_mul_I z
      · rintro ⟨p, ⟨hp, -⟩, rfl⟩
        have hp0 : 0 ≤ p.1 := by linarith [hp.1]
        simp only [mem_setOf_eq, norm_mul, Complex.norm_real, Real.norm_of_nonneg hp0, norm_exp_ofReal_mul_I,
          mul_one]
        exact ⟨hp.1, hp.2⟩
    rw [himg]
    exact (isPreconnected_Ioo.prod isPreconnected_univ).image _ (by fun_prop : Continuous fun p : ℝ × ℝ =>
      (p.1 : ℂ) * Complex.exp (p.2 * I)).continuousOn
  have hHc : ContinuousOn H {z : ℂ | 1 < ‖z‖ ∧ ‖z‖ < R} :=
    hd.continuousOn.mono fun z hz => ⟨by linarith [hz.1], hz.2⟩
  have hpc2 : IsPreconnected ((fun z => ‖H z‖) '' {z : ℂ | 1 < ‖z‖ ∧ ‖z‖ < R}) :=
    hpc.image _ (continuous_norm.comp_continuousOn hHc)
  -- one point of the outer annulus is mapped outside: the boundary derivative argument
  have h10 : (1 : ℂ) ∈ {z : ℂ | ρ < ‖z‖ ∧ ‖z‖ < R} := hcA 1 (by simp)
  obtain ⟨hHd1, hHi1⟩ := And.intro (hd.differentiableAt (hA.mem_nhds h10)) (hcirc1 1 (by simp))
  set c : ℂ := H 1 with hcdef
  set c' : ℂ := deriv H 1 with hc'def
  have hc0 : c ≠ 0 := fun h => by rw [h, norm_zero] at hHi1; exact zero_ne_one hHi1
  have hc'0 : c' ≠ 0 := deriv_ne_zero_of_injOn hA hd hi h10
  have hHD : HasDerivAt H c' 1 := hHd1.hasDerivAt
  -- the angular function `θ ↦ H(e^{iθ}) / c`
  have hexpD : HasDerivAt (fun θ : ℝ => Complex.exp (θ * I)) I 0 := by
    have h := ((hasDerivAt_id (0 : ℝ)).ofReal_comp.mul_const I).cexp
    simpa using h
  have hang : HasDerivAt (fun θ : ℝ => H (Complex.exp (θ * I)) / c) (c' * I / c) 0 := by
    have h1 : HasDerivAt H c' (Complex.exp ((0 : ℝ) * I)) := by simpa using hHD
    exact (HasDerivAt.comp (h := fun θ : ℝ => Complex.exp (θ * I)) (h₂ := H) (0 : ℝ) h1 hexpD).div_const c
  have hrad : HasDerivAt (fun s : ℝ => H (1 + s) / c) (c' / c) 0 := by
    have h0 : HasDerivAt (fun s : ℝ => (1 : ℂ) + s) 1 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).ofReal_comp).const_add (1 : ℂ)
    have h1 : HasDerivAt H c' ((fun s : ℝ => (1 : ℂ) + s) 0) := by simpa using hHD
    have h2 := (HasDerivAt.comp (h := fun s : ℝ => (1 : ℂ) + s) (h₂ := H) (0 : ℝ) h1 h0).div_const c
    simpa using h2
  obtain ⟨u, huc, hum, -, hu⟩ : ∃ u : ℝ → ℝ, Continuous u ∧ StrictMono u ∧ (∀ t, u (t + 2 * π) = u t + 2 * π) ∧
      ∀ t : ℝ, wA μ (Complex.exp (t * I)) = Complex.exp (u t * I) := wA_circle_sensePreserving hμ
  have hHexp : ∀ θ : ℝ, H (Complex.exp (θ * I)) / c = Complex.exp ((u θ - u 0 : ℝ) * I) := by
    intro θ
    have hθ : Complex.exp (θ * I) ∈ unitCircle := norm_exp_ofReal_mul_I θ
    rw [hc _ hθ, hu θ]
    have hc1 : c = Complex.exp (u 0 * I) := by
      rw [hcdef, hc 1 (show ‖(1 : ℂ)‖ = 1 by simp)]
      have := hu 0
      simpa using this
    rw [hc1, ← Complex.exp_sub]
    congr 1
    push_cast
    ring
  -- the sign of `Re (c'/c)`
  have hexpDm : HasDerivAt (fun θ : ℝ => Complex.exp (((-θ : ℝ) : ℂ) * I)) (-I) 0 := by
    have h := (((hasDerivAt_id (0 : ℝ)).neg).ofReal_comp.mul_const I).cexp
    simpa using h
  have hangm : HasDerivAt (fun θ : ℝ => H (Complex.exp (((-θ : ℝ) : ℂ) * I)) / c) (c' * (-I) / c) 0 := by
    have h1 : HasDerivAt H c' (Complex.exp ((((-(0 : ℝ)) : ℝ) : ℂ) * I)) := by simpa using hHD
    exact (HasDerivAt.comp (h := fun θ : ℝ => Complex.exp (((-θ : ℝ) : ℂ) * I)) (h₂ := H) (0 : ℝ) h1
      hexpDm).div_const c
  have hval : Complex.imCLM (c' * I / c) = (c' / c).re := by
    rw [Complex.imCLM_apply, mul_div_right_comm, Complex.mul_im, Complex.I_re, Complex.I_im]
    ring
  have hval2 : (-Complex.reCLM) (c' * I / c) = (c' / c).im := by
    rw [ContinuousLinearMap.neg_apply, Complex.reCLM_apply, mul_div_right_comm, Complex.mul_re, Complex.I_re,
      Complex.I_im]
    ring
  have hval3 : (-Complex.reCLM) (c' * (-I) / c) = -(c' / c).im := by
    rw [ContinuousLinearMap.neg_apply, Complex.reCLM_apply, mul_div_right_comm, Complex.mul_re, Complex.neg_re,
      Complex.neg_im, Complex.I_re, Complex.I_im]
    ring
  have hre0 : ∀ θ : ℝ, (H (Complex.exp (θ * I)) / c).re ≤ 1 := fun θ => by
    rw [hHexp, exp_ofReal_mul_I_re]
    exact Real.cos_le_one _
  have hc10 : H (Complex.exp (((0 : ℝ) : ℂ) * I)) / c = 1 := by
    rw [Complex.ofReal_zero, zero_mul, Complex.exp_zero, ← hcdef, div_self hc0]
  have hc10' : H (Complex.exp ((((-(0 : ℝ)) : ℝ) : ℂ) * I)) / c = 1 := by
    rw [neg_zero]
    exact hc10
  have hlam0 : c' / c ≠ 0 := div_ne_zero hc'0 hc0
  have hlre : 0 < (c' / c).re := by
    rcases lt_trichotomy (c' / c).re 0 with h | h | h
    · exfalso
      have hev := s3g_slope_neg hang Complex.imCLM (by rw [hval]; exact h)
      have hcu : ∀ᶠ θ in 𝓝[>] (0 : ℝ), u θ - u 0 < π := by
        have hct : ContinuousAt (fun θ => u θ - u 0) 0 := (huc.sub continuous_const).continuousAt
        have := hct.preimage_mem_nhds (Iio_mem_nhds (show u 0 - u 0 < π by rw [sub_self]; exact Real.pi_pos))
        exact nhdsWithin_le_nhds this
      obtain ⟨θ, ⟨hθ1, hθ2⟩, hθ0⟩ := ((hev.and hcu).and self_mem_nhdsWithin).exists
      have hθ0' : (0 : ℝ) < θ := hθ0
      have hpos : 0 < u θ - u 0 := sub_pos.mpr (hum hθ0')
      have hsin : 0 < Real.sin (u θ - u 0) := Real.sin_pos_of_pos_of_lt_pi hpos hθ2
      simp only [Complex.imCLM_apply] at hθ1
      rw [hHexp, hHexp, exp_ofReal_mul_I_im, exp_ofReal_mul_I_im, sub_self, Real.sin_zero] at hθ1
      linarith
    · exfalso
      have him : (c' / c).im ≠ 0 := fun h' => hlam0 (Complex.ext h h')
      rcases lt_or_gt_of_ne him with h' | h'
      · have hev := s3g_slope_neg hang (-Complex.reCLM) (by rw [hval2]; exact h')
        obtain ⟨θ, hθ, -⟩ := (hev.and self_mem_nhdsWithin).exists
        simp only [ContinuousLinearMap.neg_apply, Complex.reCLM_apply] at hθ
        rw [hc10, Complex.one_re] at hθ
        linarith [hre0 θ]
      · have hev := s3g_slope_neg hangm (-Complex.reCLM) (by rw [hval3]; linarith)
        obtain ⟨θ, hθ, -⟩ := (hev.and self_mem_nhdsWithin).exists
        simp only [ContinuousLinearMap.neg_apply, Complex.reCLM_apply] at hθ
        rw [hc10', Complex.one_re] at hθ
        linarith [hre0 (-θ)]
    · exact h
  -- radially, `‖H(1 + s)‖ > 1` for small `s > 0`
  have hev2 := s3g_slope_neg hrad (-Complex.reCLM) (by
    rw [ContinuousLinearMap.neg_apply, Complex.reCLM_apply]
    linarith)
  have hsR : ∀ᶠ s in 𝓝[>] (0 : ℝ), s < R - 1 :=
    nhdsWithin_le_nhds (Iio_mem_nhds (by linarith))
  obtain ⟨s, ⟨hs1, hs2⟩, hs0⟩ := ((hev2.and hsR).and self_mem_nhdsWithin).exists
  have hs0' : (0 : ℝ) < s := hs0
  have hval1 : (H (1 + ((0 : ℝ) : ℂ)) / c).re = 1 := by
    rw [Complex.ofReal_zero, add_zero, ← hcdef, div_self hc0, Complex.one_re]
  simp only [ContinuousLinearMap.neg_apply, Complex.reCLM_apply] at hs1
  rw [hval1] at hs1
  have hgt : 1 < ‖H (1 + s)‖ := by
    have h3 : 1 < (H (1 + s) / c).re := by linarith
    have h4 : (H (1 + s) / c).re ≤ ‖H (1 + s) / c‖ := Complex.re_le_norm _
    rw [norm_div, hHi1, div_one] at h4
    linarith
  have hmem1 : (1 + (s : ℂ)) ∈ {z : ℂ | 1 < ‖z‖ ∧ ‖z‖ < R} := by
    have hn : ‖(1 + (s : ℂ))‖ = 1 + s := by
      rw [show (1 + (s : ℂ)) = ((1 + s : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
        Real.norm_of_nonneg (by linarith)]
    exact ⟨by rw [hn]; linarith, by rw [hn]; linarith⟩
  -- conclude by connectedness
  intro z h1 h2
  by_contra hcon
  have hle : ‖H z‖ ≤ 1 := not_lt.mp hcon
  have hlt : ‖H z‖ < 1 := lt_of_le_of_ne hle (hne1 z h1 h2)
  have hIcc := hpc2.Icc_subset ⟨z, ⟨h1, h2⟩, rfl⟩ ⟨_, hmem1, rfl⟩
  obtain ⟨w, hw, hw1⟩ := hIcc ⟨hlt.le, hgt.le⟩
  exact hne1 w hw.1 hw.2 hw1

/-! ### The welding identity for extensions (下属3) -/

/-- Extensions `F` of `f_μ` across `𝕊¹` and `G` of `g_μ` across `𝕊¹` satisfy `G ∘ w^A_μ = F` on `𝕊¹`. -/
theorem s3g_weld_circle {μ : LinfStar} (hμ : μ ∈ LinfStarBall) {ρ R : ℝ} (hρ : ρ < 1) (hR : 1 < R)
    {F G : ℂ → ℂ} (hF : ContinuousOn F (ball 0 R)) (hFe : EqOn F (fB μ) unitDisc)
    (hG : ContinuousOn G {z | ρ < ‖z‖}) (hGe : EqOn G (gMu μ) unitDiscExterior) {z : ℂ} (hz : ‖z‖ = 1) :
    G (wA μ z) = F z := by
  obtain ⟨u, hu, he⟩ := wAS_maps_circle hμ hz
  have hw : wA μ z = u := by
    show finPart (wAS μ (z : ExtPlane)) = u
    rw [he]
    rfl
  -- `ĝ` is continuous and equals `G` on `|w| ≥ 1`
  have hgc' : ContinuousOn (fun w : ℂ => finPart (wB μ (Function.invFun (wAS μ) (w : ExtPlane)))) univ := by
    intro w _
    have h1 : ContinuousAt (fun w : ℂ => wB μ (Function.invFun (wAS μ) (w : ExtPlane))) w :=
      ((wB_continuous hμ).comp ((wAS_invFun_continuous hμ).comp OnePoint.continuous_coe)).continuousAt
    exact (ContinuousAt.comp (g := finPart) (f := fun w : ℂ => wB μ (Function.invFun (wAS μ) (w : ExtPlane)))
      (s5rh_finPart_contAt (s3g_sphere_pre hμ w).1) h1).continuousWithinAt
  have hext : {w : ℂ | 1 < ‖w‖} = (closedBall (0 : ℂ) 1)ᶜ := by
    ext w
    simp only [mem_setOf_eq, mem_compl_iff, mem_closedBall_zero_iff, not_le]
  have hcl : {w : ℂ | 1 ≤ ‖w‖} ⊆ closure unitDiscExterior := by
    show {w : ℂ | 1 ≤ ‖w‖} ⊆ closure {w : ℂ | 1 < ‖w‖}
    rw [hext, closure_compl, interior_closedBall (0 : ℂ) one_ne_zero]
    intro w hw h
    exact absurd (mem_ball_zero_iff.mp h) (not_lt.mpr hw)
  have hGg : EqOn G (fun w : ℂ => finPart (wB μ (Function.invFun (wAS μ) (w : ExtPlane)))) unitDiscExterior :=
    fun w hw => (hGe hw).trans (s3g_gMu_sphere hμ hw)
  have hGg' := hGg.of_subset_closure (hG.mono fun w (hw : 1 ≤ ‖w‖) => show ρ < ‖w‖ by linarith)
    (hgc'.mono (subset_univ _)) (fun w (hw : 1 < ‖w‖) => show 1 ≤ ‖w‖ from hw.le) hcl
  have hFf : EqOn F (fB μ) (closedBall 0 1) :=
    hFe.of_subset_closure (hF.mono (closedBall_subset_ball hR)) (s3g_fB_contOn hμ) ball_subset_closedBall (by
      show closedBall (0 : ℂ) 1 ⊆ closure (ball 0 1)
      rw [closure_ball _ one_ne_zero])
  rw [hGg' (show 1 ≤ ‖wA μ z‖ by rw [hw, hu]), hFf (mem_closedBall_zero_iff.mpr hz.le)]
  show finPart (wB μ (Function.invFun (wAS μ) ((wA μ z : ℂ) : ExtPlane))) = fB μ z
  rw [hw, ← he]
  show finPart (wB μ (Function.invFun (wAS μ) (wAS μ (z : ExtPlane)))) = finPart (wB μ (z : ExtPlane))
  rw [Function.leftInverse_invFun (wAS_bijective μ).1 (z : ExtPlane)]

/-- **(a)** Ahlfors–Weill with polynomial data: `f_{Λ(ψ_a + t ψ_m)}` extends holomorphically and injectively across
`𝕊¹`, as a C¹ family in `t`. -/
theorem s3g_aw_extend {ψa ψm : A2 unitDisc}
    (hpa : ∃ q : Polynomial ℂ, ∀ z ∈ unitDisc, A2.toFun ψa z = q.eval z)
    (hpm : ∃ q : Polynomial ℂ, ∀ z ∈ unitDisc, A2.toFun ψm z = q.eval z)
    (hsa : ‖A2toAInf ψa‖ < 2) :
    ∃ r > 0, ∃ R > 1, ∃ F : ℂ → ℂ → ℂ,
      ContDiffOn ℝ 1 (fun q : ℂ × ℂ => F q.1 q.2) (ball 0 r ×ˢ ball 0 R) ∧
      ∀ t ∈ ball (0 : ℂ) r, Lambda (A2toAInf (ψa + t • ψm)) ∈ LinfStarBall ∧
        DifferentiableOn ℂ (F t) (ball 0 R) ∧ InjOn (F t) (ball 0 R) ∧
        EqOn (F t) (fB (Lambda (A2toAInf (ψa + t • ψm)))) unitDisc := by
  obtain ⟨pa, hpa⟩ := hpa
  obtain ⟨pm, hpm⟩ := hpm
  have h0D : (0 : ℂ) ∈ unitDisc := mem_ball_self one_pos
  -- linearity of `A² → A∞` and the values of the line
  have hlin : ∀ t : ℂ, A2toAInf (ψa + t • ψm) = A2toAInf ψa + t • A2toAInf ψm := by
    intro t
    rw [add_comm ψa, A2toAInf_bounded.1 t ψm ψa, add_comm]
  have hval : ∀ t : ℂ, ∀ z ∈ unitDisc,
      AInf.toFun (A2toAInf ψa + t • A2toAInf ψm) z = pa.eval z + t * pm.eval z := by
    intro t z hz
    rw [s3g_ainf_add_smul, (A2toAInf_bounded.2 ψa).2 z hz, (A2toAInf_bounded.2 ψm).2 z hz, hpa z hz, hpm z hz]
  -- constants
  obtain ⟨s, hs⟩ : ∃ s, s = ‖A2toAInf ψa‖ := ⟨_, rfl⟩
  obtain ⟨Bm, hBm⟩ : ∃ B, B = ‖A2toAInf ψm‖ + 1 := ⟨_, rfl⟩
  have hs0 : 0 ≤ s := by rw [hs]; exact norm_nonneg _
  have hBm0 : 0 < Bm := by rw [hBm]; positivity
  have hs2 : s < 2 := by rw [hs]; exact hsa
  obtain ⟨δ, hδ⟩ : ∃ δ : ℝ, δ = (2 - s) / 4 := ⟨_, rfl⟩
  have hδ0 : 0 < δ := by rw [hδ]; linarith
  obtain ⟨ε1, hε1, hr1⟩ := s3g_rescale (p := fun z => pa.eval z) pa.continuous hδ0
  obtain ⟨ε2, hε2, hr2⟩ := s3g_rescale (p := fun z => pm.eval z) pm.continuous one_pos
  have hε := lt_min hε1 hε2
  obtain ⟨ρ, hρ⟩ : ∃ ρ : ℝ, ρ = 1 + min ε1 ε2 / 2 := ⟨_, rfl⟩
  have hρ1 : 1 < ρ := by rw [hρ]; linarith
  have hρe : |ρ - 1| = min ε1 ε2 / 2 := by
    rw [hρ, show 1 + min ε1 ε2 / 2 - 1 = min ε1 ε2 / 2 by ring, abs_of_pos (half_pos hε)]
  have hρa : |ρ - 1| < ε1 := by rw [hρe]; linarith [min_le_left ε1 ε2]
  have hρm : |ρ - 1| < ε2 := by rw [hρe]; linarith [min_le_right ε1 ε2]
  have hρ0 : (ρ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by linarith)
  have hcρ : ∀ z ∈ ball (0 : ℂ) ρ, (ρ : ℂ)⁻¹ * z ∈ unitDisc := by
    intro z hz
    rw [mem_ball_zero_iff] at hz
    show (ρ : ℂ)⁻¹ * z ∈ ball (0 : ℂ) 1
    rw [mem_ball_zero_iff, norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg (by linarith),
      inv_mul_lt_iff₀ (by linarith)]
    linarith
  have hw : ∀ z ∈ unitDisc, 0 ≤ (1 - ‖z‖ ^ 2) ^ 2 ∧ (1 - ‖z‖ ^ 2) ^ 2 ≤ 1 := by
    intro z hz
    have hz1 : ‖z‖ < 1 := mem_ball_zero_iff.mp hz
    have h0 : 0 ≤ 1 - ‖z‖ ^ 2 := by nlinarith [norm_nonneg z]
    have h1 : 1 - ‖z‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg z]
    exact ⟨by positivity, pow_le_one₀ h0 h1⟩
  have hpa' : ∀ z ∈ unitDisc, ‖pa.eval z‖ * (1 - ‖z‖ ^ 2) ^ 2 ≤ s := by
    intro z hz
    rw [hs, ← hpa z hz, ← (A2toAInf_bounded.2 ψa).2 z hz]
    exact s3g_ainf_pt _ hz
  have hpm' : ∀ z ∈ unitDisc, ‖pm.eval z‖ * (1 - ‖z‖ ^ 2) ^ 2 ≤ Bm - 1 := by
    intro z hz
    rw [hBm, add_sub_cancel_right, ← hpm z hz, ← (A2toAInf_bounded.2 ψm).2 z hz]
    exact s3g_ainf_pt _ hz
  -- the rescaled data `ρ² p(ρ z)`
  obtain ⟨Pa, hPa⟩ : ∃ P : ℂ → ℂ, P = fun z => (ρ : ℂ) ^ 2 * pa.eval ((ρ : ℂ) * z) := ⟨_, rfl⟩
  obtain ⟨Pm, hPm⟩ : ∃ P : ℂ → ℂ, P = fun z => (ρ : ℂ) ^ 2 * pm.eval ((ρ : ℂ) * z) := ⟨_, rfl⟩
  have hPad : DifferentiableOn ℂ Pa unitDisc := by
    rw [hPa]
    exact ((differentiable_const _).mul (pa.differentiable.comp
      ((differentiable_const _).mul differentiable_id))).differentiableOn
  have hPmd : DifferentiableOn ℂ Pm unitDisc := by
    rw [hPm]
    exact ((differentiable_const _).mul (pm.differentiable.comp
      ((differentiable_const _).mul differentiable_id))).differentiableOn
  have hPab : ∀ z ∈ unitDisc, ‖Pa z‖ * (1 - ‖z‖ ^ 2) ^ 2 ≤ s + δ := by
    intro z hz
    obtain ⟨hw0, hw1⟩ := hw z hz
    have h1 : ‖(ρ : ℂ) ^ 2 * pa.eval ((ρ : ℂ) * z) - pa.eval z‖ < δ := hr1 ρ hρa z (ball_subset_closedBall hz)
    have h2 : ‖Pa z‖ ≤ ‖pa.eval z‖ + δ := by
      have h3 : Pa z = (ρ : ℂ) ^ 2 * pa.eval ((ρ : ℂ) * z) := by rw [hPa]
      rw [h3]
      linarith [norm_le_insert' ((ρ : ℂ) ^ 2 * pa.eval ((ρ : ℂ) * z)) (pa.eval z)]
    have h3 := mul_le_mul_of_nonneg_right h2 hw0
    have h4 : δ * (1 - ‖z‖ ^ 2) ^ 2 ≤ δ := mul_le_of_le_one_right hδ0.le hw1
    rw [add_mul] at h3
    linarith [hpa' z hz]
  have hPmb : ∀ z ∈ unitDisc, ‖Pm z‖ * (1 - ‖z‖ ^ 2) ^ 2 ≤ Bm := by
    intro z hz
    obtain ⟨hw0, hw1⟩ := hw z hz
    have h1 : ‖(ρ : ℂ) ^ 2 * pm.eval ((ρ : ℂ) * z) - pm.eval z‖ < 1 := hr2 ρ hρm z (ball_subset_closedBall hz)
    have h2 : ‖Pm z‖ ≤ ‖pm.eval z‖ + 1 := by
      have h3 : Pm z = (ρ : ℂ) ^ 2 * pm.eval ((ρ : ℂ) * z) := by rw [hPm]
      rw [h3]
      linarith [norm_le_insert' ((ρ : ℂ) ^ 2 * pm.eval ((ρ : ℂ) * z)) (pm.eval z)]
    have h3 := mul_le_mul_of_nonneg_right h2 hw0
    rw [add_mul, one_mul] at h3
    linarith [hpm' z hz]
  obtain ⟨Ψa, hΨa⟩ : ∃ Ψ : AInf unitDisc, Ψ = toAInf unitDisc Pa := ⟨_, rfl⟩
  obtain ⟨Ψm, hΨm⟩ : ∃ Ψ : AInf unitDisc, Ψ = toAInf unitDisc Pm := ⟨_, rfl⟩
  have hΨa' := toAInf_disc_spec_of_bound (by linarith) hPad hPab
  have hΨm' := toAInf_disc_spec_of_bound hBm0.le hPmd hPmb
  rw [← hΨa] at hΨa'
  rw [← hΨm] at hΨm'
  -- the radius in `t`
  obtain ⟨r, hr⟩ : ∃ r : ℝ, r = δ / Bm := ⟨_, rfl⟩
  have hr0 : 0 < r := by rw [hr]; positivity
  have htB : ∀ t ∈ ball (0 : ℂ) r, ‖t‖ * Bm < δ := by
    intro t ht
    rw [mem_ball_zero_iff, hr] at ht
    rwa [lt_div_iff₀ hBm0] at ht
  have hnφ : ∀ t ∈ ball (0 : ℂ) r, ‖A2toAInf (ψa + t • ψm)‖ < 2 := by
    intro t ht
    have h1 := htB t ht
    rw [hBm, mul_add, mul_one] at h1
    rw [hlin]
    calc ‖A2toAInf ψa + t • A2toAInf ψm‖ ≤ ‖A2toAInf ψa‖ + ‖t‖ * ‖A2toAInf ψm‖ := by
          refine (norm_add_le _ _).trans ?_
          rw [norm_smul]
      _ < 2 := by linarith [norm_nonneg t]
  have hnΨ : ∀ t ∈ ball (0 : ℂ) r, ‖Ψa + t • Ψm‖ < 2 := by
    intro t ht
    have h1 := htB t ht
    have h2 : ‖t‖ * ‖Ψm‖ ≤ ‖t‖ * Bm := mul_le_mul_of_nonneg_left hΨm'.2 (norm_nonneg t)
    calc ‖Ψa + t • Ψm‖ ≤ ‖Ψa‖ + ‖t‖ * ‖Ψm‖ := by
          refine (norm_add_le _ _).trans ?_
          rw [norm_smul]
      _ < 2 := by linarith [hΨa'.2]
  -- the two Beltrami lines
  obtain ⟨μ, hμt⟩ : ∃ μ : ℂ → LinfStar, ∀ t, μ t = Lambda (A2toAInf (ψa + t • ψm)) := ⟨_, fun _ => rfl⟩
  obtain ⟨ν, hνt⟩ : ∃ ν : ℂ → LinfStar, ∀ t, ν t = Lambda (Ψa + t • Ψm) := ⟨_, fun _ => rfl⟩
  have hμa : ∀ t, AnalyticAt ℝ μ t := by
    have he : μ = fun t => Lambda (A2toAInf ψa) + t • Lambda (A2toAInf ψm) := by
      funext t
      rw [hμt, hlin, Lambda_add, Lambda_smul]
    intro t
    rw [he]
    exact analyticAt_const.add (analyticAt_id.smul analyticAt_const)
  have hνa : ∀ t, AnalyticAt ℝ ν t := by
    have he : ν = fun t => Lambda Ψa + t • Lambda Ψm := by
      funext t
      rw [hνt, Lambda_add, Lambda_smul]
    intro t
    rw [he]
    exact analyticAt_const.add (analyticAt_id.smul analyticAt_const)
  have hAWμ : ∀ t ∈ ball (0 : ℂ) r, μ t ∈ LinfStarBall ∧ bersPhi (μ t) = A2toAInf (ψa + t • ψm) := by
    intro t ht
    rw [hμt]
    exact QCV.qs_AW (hnφ t ht)
  have hAWν : ∀ t ∈ ball (0 : ℂ) r, ν t ∈ LinfStarBall ∧ bersPhi (ν t) = Ψa + t • Ψm := by
    intro t ht
    rw [hνt]
    exact QCV.qs_AW (hnΨ t ht)
  -- the rescaled family `F̂_t(z) = ρ f^{ν_t}(z/ρ)` on `|z| < ρ`
  obtain ⟨Fh, hFh⟩ : ∃ Fh : ℂ → ℂ → ℂ, Fh = fun t z => (ρ : ℂ) * fB (ν t) ((ρ : ℂ)⁻¹ * z) := ⟨_, rfl⟩
  have hfam := s3g_fB_family (fun t ht => (hAWν t ht).1) hνa hcρ
  have hFc : ContDiffOn ℝ 1 (fun q : ℂ × ℂ => Fh q.1 q.2) (ball 0 r ×ˢ ball 0 ρ) := by
    rw [hFh]
    exact contDiffOn_const.mul hfam.1
  have hFt : ∀ t ∈ ball (0 : ℂ) r, DifferentiableOn ℂ (Fh t) (ball 0 ρ) := by
    intro t ht
    rw [hFh]
    exact (hfam.2 t ht).const_mul _
  have hFi : ∀ t ∈ ball (0 : ℂ) r, InjOn (Fh t) (ball 0 ρ) := by
    intro t ht x hx y hy hxy
    have h' : (ρ : ℂ) * fB (ν t) ((ρ : ℂ)⁻¹ * x) = (ρ : ℂ) * fB (ν t) ((ρ : ℂ)⁻¹ * y) := by
      rw [hFh] at hxy
      exact hxy
    have h3 := (fB_holomorphic_injective (hAWν t ht).1).2 (hcρ x hx) (hcρ y hy) (mul_left_cancel₀ hρ0 h')
    exact mul_left_cancel₀ (inv_ne_zero hρ0) h3
  have hF0 : ∀ t, Fh t 0 = 0 := by
    intro t
    rw [hFh]
    show (ρ : ℂ) * fB (ν t) ((ρ : ℂ)⁻¹ * 0) = 0
    rw [mul_zero, (fB_normalization _).1, mul_zero]
  have hF1 : ∀ t ∈ ball (0 : ℂ) r, deriv (Fh t) 0 = 1 := by
    intro t ht
    have hd0 : DifferentiableAt ℂ (fB (ν t)) ((ρ : ℂ)⁻¹ * 0) := by
      rw [mul_zero]
      exact (fB_holomorphic_injective (hAWν t ht).1).1.differentiableAt (isOpen_ball.mem_nhds h0D)
    have h2 := (HasDerivAt.comp (h := fun y : ℂ => (ρ : ℂ)⁻¹ * id y) (h₂ := fB (ν t)) (0 : ℂ) hd0.hasDerivAt
      ((hasDerivAt_id (0 : ℂ)).const_mul ((ρ : ℂ)⁻¹))).const_mul (ρ : ℂ)
    have hfe : Fh t = fun y => (ρ : ℂ) * (fB (ν t) ∘ fun y => (ρ : ℂ)⁻¹ * id y) y := by
      rw [hFh]
      rfl
    rw [hfe, h2.deriv, mul_zero, (fB_normalization (ν t)).2.1]
    field_simp
  have hSF : ∀ t ∈ ball (0 : ℂ) r, ∀ z ∈ ball (0 : ℂ) ρ, schwarzianHol (Fh t) z = pa.eval z + t * pm.eval z := by
    intro t ht z hz
    have hu := hcρ z hz
    obtain ⟨hνb, hνφ⟩ := hAWν t ht
    obtain ⟨hd, hi⟩ := fB_holomorphic_injective hνb
    have han : AnalyticAt ℂ (fB (ν t)) ((ρ : ℂ)⁻¹ * z) := hd.analyticAt (isOpen_ball.mem_nhds hu)
    have hne : deriv (fB (ν t)) ((ρ : ℂ)⁻¹ * z) ≠ 0 := deriv_ne_zero_of_injOn isOpen_ball hd hi hu
    have hρz : (ρ : ℂ) * ((ρ : ℂ)⁻¹ * z) = z := by field_simp
    have hfe : Fh t = fun w => (ρ : ℂ) * fB (ν t) ((ρ : ℂ)⁻¹ * w) := by rw [hFh]
    rw [hfe, schwarzianHol_mul_comp_mul hρ0 (inv_ne_zero hρ0) han hne, ← (bersPhi_spec hνb).1 _ hu, hνφ,
      s3g_ainf_add_smul, hΨa'.1 _ hu, hΨm'.1 _ hu, hPa, hPm]
    simp only [hρz]
    field_simp
  have hSf : ∀ t ∈ ball (0 : ℂ) r, ∀ z ∈ unitDisc, schwarzianHol (fB (μ t)) z = pa.eval z + t * pm.eval z := by
    intro t ht z hz
    obtain ⟨hμb, hμφ⟩ := hAWμ t ht
    rw [← (bersPhi_spec hμb).1 z hz, hμφ, hlin, hval t z hz]
  -- `γ_t = (F̂_t''(0) - f_t''(0))/2` is C¹
  have hft : ∀ t ∈ ball (0 : ℂ) r, DifferentiableOn ℂ (fB (μ t)) unitDisc := fun t ht =>
    (fB_holomorphic_injective (hAWμ t ht).1).1
  have hfam2 := s3g_fB_family (c := 1) (R := 1) (fun t ht => (hAWμ t ht).1) hμa
    (fun z hz => by rw [one_mul]; exact hz)
  have hfc : ContDiffOn ℝ 1 (fun q : ℂ × ℂ => fB (μ q.1) q.2) (ball 0 r ×ˢ unitDisc) := by
    have h := hfam2.1
    simp only [one_mul] at h
    exact h
  obtain ⟨γ, hγ⟩ : ∃ γ : ℂ → ℂ, γ = fun t => (deriv (deriv (Fh t)) 0 - deriv (deriv (fB (μ t))) 0) / 2 :=
    ⟨_, rfl⟩
  have hγc : ContDiffOn ℝ 1 γ (ball 0 r) := by
    rw [hγ]
    exact ((s3g_jet2 isOpen_ball isOpen_ball (mem_ball_self (by linarith)) hFc hFt).sub
      (s3g_jet2 (F := fun t => fB (μ t)) isOpen_ball isOpen_ball h0D hfc hft)).div_const 2
  -- the Möbius identification for each `t`
  have hid : ∀ t ∈ ball (0 : ℂ) r, (∀ z ∈ closedBall (0 : ℂ) 1, fB (μ t) z * (γ t * Fh t z + 1) = Fh t z) ∧
      ∀ z ∈ closedBall (0 : ℂ) 1, γ t * Fh t z + 1 ≠ 0 := by
    intro t ht
    have hμb := (hAWμ t ht).1
    refine s3g_mob_ident hρ1 (hft t ht) (s3g_fB_contOn hμb) (hFt t ht) (hFi t ht)
      (fB_normalization _).1 (fB_normalization _).2.1 (hF0 t) (hF1 t ht) ?_ (by rw [hγ])
    intro z hz
    rw [hSf t ht z hz, hSF t ht z (ball_subset_ball hρ1.le hz)]
  -- the denominator stays away from `0` on `|t| ≤ r/2`, `|z| < R` (compactness)
  have hdenC : ContDiffOn ℝ 1 (fun q : ℂ × ℂ => γ q.1 * Fh q.1 q.2 + 1) (ball 0 r ×ˢ ball 0 ρ) :=
    ((hγc.comp contDiffOn_fst (fun q hq => hq.1)).mul hFc).add contDiffOn_const
  have hO := hdenC.continuousOn.isOpen_inter_preimage (isOpen_ball.prod isOpen_ball)
    (isOpen_compl_singleton : IsOpen ({0}ᶜ : Set ℂ))
  have hK : closedBall (0 : ℂ) (r / 2) ×ˢ closedBall (0 : ℂ) 1 ⊆
      (ball 0 r ×ˢ ball 0 ρ) ∩ (fun q : ℂ × ℂ => γ q.1 * Fh q.1 q.2 + 1) ⁻¹' {0}ᶜ := by
    rintro ⟨t, z⟩ ⟨ht, hz⟩
    have ht' : t ∈ ball (0 : ℂ) r := by
      rw [mem_closedBall_zero_iff] at ht
      rw [mem_ball_zero_iff]
      linarith
    exact ⟨⟨ht', closedBall_subset_ball hρ1 hz⟩, (hid t ht').2 z hz⟩
  obtain ⟨u, v, -, hv, hu, hcv, huv⟩ :=
    generalized_tube_lemma (isCompact_closedBall (0 : ℂ) (r / 2)) (isCompact_closedBall (0 : ℂ) 1) hO hK
  obtain ⟨η, hη, hth⟩ := (isCompact_closedBall (0 : ℂ) 1).exists_thickening_subset_open hv hcv
  rw [thickening_closedBall hη zero_le_one] at hth
  have hsub : ∀ t ∈ ball (0 : ℂ) (r / 2), ∀ z ∈ ball (0 : ℂ) (η + 1),
      (t ∈ ball (0 : ℂ) r ∧ z ∈ ball (0 : ℂ) ρ) ∧ γ t * Fh t z + 1 ≠ 0 := fun t ht z hz =>
    huv (show (t, z) ∈ u ×ˢ v from ⟨hu (ball_subset_closedBall ht), hth hz⟩)
  have hm : ball (0 : ℂ) (r / 2) ×ˢ ball (0 : ℂ) (η + 1) ⊆ ball 0 r ×ˢ ball 0 ρ := fun q hq =>
    (hsub q.1 hq.1 q.2 hq.2).1
  refine ⟨r / 2, half_pos hr0, η + 1, by linarith, fun t z => Fh t z / (γ t * Fh t z + 1), ?_, fun t ht => ?_⟩
  · refine ((hFc.mono hm).mul ((hdenC.mono hm).inv (fun (q : ℂ × ℂ)
      (hq : q ∈ ball (0 : ℂ) (r / 2) ×ˢ ball (0 : ℂ) (η + 1)) => (hsub q.1 hq.1 q.2 hq.2).2))).congr fun q _ => ?_
    simp only [div_eq_mul_inv]
    rfl
  have ht' : t ∈ ball (0 : ℂ) r := (hsub t ht 0 (mem_ball_self (by linarith))).1.1
  have hsubρ : ball (0 : ℂ) (η + 1) ⊆ ball 0 ρ := fun z hz => (hsub t ht z hz).1.2
  have hne : ∀ z ∈ ball (0 : ℂ) (η + 1), γ t * Fh t z + 1 ≠ 0 := fun z hz => (hsub t ht z hz).2
  refine ⟨by rw [← hμt t]; exact (hAWμ t ht').1, ?_, ?_, ?_⟩
  · exact ((hFt t ht').mono hsubρ).div ((((hFt t ht').mono hsubρ).const_mul (γ t)).add_const 1) hne
  · intro x hx y hy hxy
    have hxy' : Fh t x / (γ t * Fh t x + 1) = Fh t y / (γ t * Fh t y + 1) := hxy
    rw [div_eq_div_iff (hne x hx) (hne y hy)] at hxy'
    have h3 : Fh t x = Fh t y := by linear_combination hxy'
    exact hFi t ht' (hsubρ hx) (hsubρ hy) h3
  · intro z hz
    show Fh t z / (γ t * Fh t z + 1) = fB (Lambda (A2toAInf (ψa + t • ψm))) z
    rw [← hμt t, div_eq_iff ((hid t ht').2 z (ball_subset_closedBall hz))]
    exact ((hid t ht').1 z (ball_subset_closedBall hz)).symm

/-- **(b)** An extension of `f_{ν_t}` across `𝕊¹` gives extensions of `g_{ν_t}` (to `|z| > ρ`) and of the welding
`h_{ν_t} = w^A_{ν_t}|_{𝕊¹}` (to an annulus), as C¹ families. -/
theorem s3g_weld_of_ext {ν : ℂ → LinfStar} {r R : ℝ} (hr : 0 < r) (hR : 1 < R)
    (hν : ∀ t ∈ ball (0 : ℂ) r, ν t ∈ LinfStarBall) (hνa : ∀ t ∈ ball (0 : ℂ) r, AnalyticAt ℝ ν t)
    {F : ℂ → ℂ → ℂ} (hF : ContDiffOn ℝ 1 (fun q : ℂ × ℂ => F q.1 q.2) (ball 0 r ×ˢ ball 0 R))
    (hFt : ∀ t ∈ ball (0 : ℂ) r, DifferentiableOn ℂ (F t) (ball 0 R) ∧ InjOn (F t) (ball 0 R) ∧
      EqOn (F t) (fB (ν t)) unitDisc) :
    ∃ r' > 0, ∃ ρ < 1, ∃ R' > 1, ∃ G H : ℂ → ℂ → ℂ,
      ContDiffOn ℝ 1 (fun q : ℂ × ℂ => G q.1 q.2) (ball 0 r' ×ˢ {z | ρ < ‖z‖}) ∧
      ContDiffOn ℝ 1 (fun q : ℂ × ℂ => H q.1 q.2) (ball 0 r' ×ˢ {z | ρ < ‖z‖ ∧ ‖z‖ < R'}) ∧
      ∀ t ∈ ball (0 : ℂ) r',
        (DifferentiableOn ℂ (G t) {z | ρ < ‖z‖} ∧ InjOn (G t) {z | ρ < ‖z‖} ∧
          EqOn (G t) (gMu (ν t)) unitDiscExterior) ∧
        (DifferentiableOn ℂ (H t) {z | ρ < ‖z‖ ∧ ‖z‖ < R'} ∧ InjOn (H t) {z | ρ < ‖z‖ ∧ ‖z‖ < R'} ∧
          ∀ z ∈ unitCircle, H t z = wA (ν t) z) := by
  have hFh : ∀ t ∈ ball (0 : ℂ) r, DifferentiableOn ℂ (F t) (ball 0 R) := fun t ht => (hFt t ht).1
  have hFi : ∀ t ∈ ball (0 : ℂ) r, InjOn (F t) (ball 0 R) := fun t ht => (hFt t ht).2.1
  have hFe : ∀ t ∈ ball (0 : ℂ) r, EqOn (F t) (fB (ν t)) unitDisc := fun t ht => (hFt t ht).2.2
  have hcl1R : closedBall (0 : ℂ) 1 ⊆ ball 0 R := closedBall_subset_ball hR
  have hr2 : ball (0 : ℂ) (r / 2) ⊆ ball 0 r := ball_subset_ball (by linarith)
  -- `w^{ν_t} = F_t` on the closed disc
  have hdisc : ∀ t ∈ ball (0 : ℂ) r, ∀ u : ℂ, ‖u‖ ≤ 1 → wB (ν t) (u : ExtPlane) = ((F t u : ℂ) : ExtPlane) := by
    intro t ht u hu
    have hEq : EqOn (F t) (fB (ν t)) (closedBall 0 1) :=
      (hFe t ht).of_subset_closure ((hFh t ht).continuousOn.mono hcl1R) (s3g_fB_contOn (hν t ht))
        ball_subset_closedBall (by
          show closedBall (0 : ℂ) 1 ⊆ closure (ball 0 1)
          rw [closure_ball _ one_ne_zero])
    rw [hEq (mem_closedBall_zero_iff.mpr hu)]
    exact (coe_finPart_of_ne (s5e_wB_finite (hν t ht) hu)).symm
  -- the sphere welding `ĝ`
  obtain ⟨gh, hgh⟩ : ∃ gh : ℂ → ℂ → ℂ,
      gh = fun t (z : ℂ) => finPart (wB (ν t) (Function.invFun (wAS (ν t)) (z : ExtPlane))) := ⟨_, rfl⟩
  have hghap : ∀ t z, gh t z = finPart (wB (ν t) (Function.invFun (wAS (ν t)) (z : ExtPlane))) :=
    fun t z => by rw [hgh]
  have hghcoe : ∀ t ∈ ball (0 : ℂ) r, ∀ z : ℂ,
      ((gh t z : ℂ) : ExtPlane) = wB (ν t) (Function.invFun (wAS (ν t)) (z : ExtPlane)) := fun t ht z => by
    rw [hghap]
    exact coe_finPart_of_ne (s3g_sphere_pre (hν t ht) z).1
  have hνc : ∀ t ∈ ball (0 : ℂ) r, ContinuousAt ν t := fun t ht => (hνa t ht).continuousAt
  have hghc : ContinuousOn (fun q : ℂ × ℂ => gh q.1 q.2) (ball 0 r ×ˢ univ) := by
    rw [hgh]
    exact s3g_ghat_cont hν hνc
  have hri : ∀ t y, wAS (ν t) (Function.invFun (wAS (ν t)) y) = y := fun t =>
    Function.rightInverse_invFun (wAS_bijective (ν t)).2
  have hli : ∀ t y, Function.invFun (wAS (ν t)) (wAS (ν t) y) = y := fun t =>
    Function.leftInverse_invFun (wAS_bijective (ν t)).1
  have hgh1 : ∀ t ∈ ball (0 : ℂ) r, ∀ z : ℂ, ‖z‖ = 1 → ∃ u : ℂ, ‖u‖ = 1 ∧ gh t z = F t u ∧
      Function.invFun (wAS (ν t)) (z : ExtPlane) = (u : ExtPlane) := by
    intro t ht z hz
    obtain ⟨u, hu, he⟩ := (s3g_sphere_pre (hν t ht) z).2.1 hz
    refine ⟨u, hu, ?_, he⟩
    apply OnePoint.coe_injective
    rw [hghcoe t ht, he, hdisc t ht u hu.le]
  have hgh2 : ∀ t ∈ ball (0 : ℂ) r, ∀ z : ℂ, 1 < ‖z‖ → ∀ u : ℂ, ‖u‖ ≤ 1 → gh t z ≠ F t u := by
    intro t ht z hz u hu he
    have h1 : ((gh t z : ℂ) : ExtPlane) = ((F t u : ℂ) : ExtPlane) := by rw [he]
    rw [hghcoe t ht, ← hdisc t ht u hu] at h1
    exact (s3g_sphere_pre (hν t ht) z).2.2 hz u hu ((wB_bijective (ν t)).1 h1)
  have hgh3 : ∀ t ∈ ball (0 : ℂ) r, ∀ z ∈ unitDiscExterior, gh t z = gsans (ν t) z := by
    intro t ht z hz
    rw [hghap, s3g_gsans_eq (hν t ht), s3g_gMu_sphere (hν t ht) hz]
  have hghi : ∀ t ∈ ball (0 : ℂ) r, ∀ z₁ z₂ : ℂ, gh t z₁ = gh t z₂ → z₁ = z₂ := by
    intro t ht z₁ z₂ he
    have h1 : ((gh t z₁ : ℂ) : ExtPlane) = ((gh t z₂ : ℂ) : ExtPlane) := by rw [he]
    rw [hghcoe t ht, hghcoe t ht] at h1
    have h2 := congrArg (wAS (ν t)) ((wB_bijective (ν t)).1 h1)
    rw [hri, hri] at h2
    exact OnePoint.coe_injective h2
  -- the inverse family of `F`
  obtain ⟨Inv, hWo, hInvC, hleft, hWin, hInvd⟩ := s3g_inv_family isOpen_ball isOpen_ball hF hFh hFi
  obtain ⟨W, hW⟩ : ∃ W : Set (ℂ × ℂ), W = (fun q : ℂ × ℂ => (q.1, F q.1 q.2)) '' (ball 0 r ×ˢ ball 0 R) :=
    ⟨_, rfl⟩
  rw [← hW] at hWo hInvC hWin
  have hsl : ∀ t ∈ ball (0 : ℂ) r, F t '' ball 0 R = (fun w : ℂ => (t, w)) ⁻¹' W := by
    intro t ht
    ext w
    constructor
    · rintro ⟨z, hz, rfl⟩
      rw [hW]
      exact ⟨(t, z), ⟨ht, hz⟩, rfl⟩
    · intro hw
      rw [mem_preimage, hW] at hw
      obtain ⟨q, hq, hqe⟩ := hw
      have h1 : q.1 = t := (Prod.ext_iff.mp hqe).1
      have h2 : F q.1 q.2 = w := (Prod.ext_iff.mp hqe).2
      exact ⟨q.2, hq.2, by rw [← h1]; exact h2⟩
  have hInvD : ∀ t ∈ ball (0 : ℂ) r, ∀ w, (t, w) ∈ W → DifferentiableAt ℂ (Inv t) w := by
    intro t ht w hw
    have hO : IsOpen (F t '' ball 0 R) := by
      rw [hsl t ht]
      exact hWo.preimage (continuous_const.prodMk continuous_id)
    have hm : w ∈ F t '' ball 0 R := by
      rw [hsl t ht]
      exact hw
    exact (hInvd t ht).differentiableAt (hO.mem_nhds hm)
  -- a uniform collar where `(t, ĝ_t(z)) ∈ W`
  have hW1 : ∀ t ∈ ball (0 : ℂ) r, ∀ z : ℂ, ‖z‖ = 1 → (t, gh t z) ∈ W := by
    intro t ht z hz
    obtain ⟨u, hu, he, -⟩ := hgh1 t ht z hz
    rw [he, hW]
    exact ⟨(t, u), ⟨ht, hcl1R (mem_closedBall_zero_iff.mpr hu.le)⟩, rfl⟩
  have hO1 : IsOpen ((ball (0 : ℂ) r ×ˢ univ) ∩ (fun q : ℂ × ℂ => (q.1, gh q.1 q.2)) ⁻¹' W) :=
    (continuousOn_fst.prodMk hghc).isOpen_inter_preimage (isOpen_ball.prod isOpen_univ) hWo
  have hK1 : closedBall (0 : ℂ) (r / 2) ×ˢ sphere (0 : ℂ) 1 ⊆
      (ball (0 : ℂ) r ×ˢ univ) ∩ (fun q : ℂ × ℂ => (q.1, gh q.1 q.2)) ⁻¹' W := by
    rintro ⟨t, z⟩ ⟨ht, hz⟩
    have ht' : t ∈ ball (0 : ℂ) r := closedBall_subset_ball (by linarith) ht
    exact ⟨⟨ht', mem_univ _⟩, hW1 t ht' z (mem_sphere_zero_iff_norm.mp hz)⟩
  obtain ⟨u1, v1, -, hv1, hu1, hsv1, huv1⟩ :=
    generalized_tube_lemma (isCompact_closedBall (0 : ℂ) (r / 2)) (isCompact_sphere (0 : ℂ) 1) hO1 hK1
  obtain ⟨δ1, hδ1, hδ11, hann1⟩ := s3g_annulus_of_sphere hv1 hsv1
  obtain ⟨b, hb⟩ : ∃ b : ℝ, b = 1 + δ1 := ⟨_, rfl⟩
  have hb1 : 1 < b := by rw [hb]; linarith
  have hb0 : 0 < b := by linarith
  have hdom : ∀ t ∈ ball (0 : ℂ) (r / 2), ∀ z : ℂ, 1 ≤ ‖z‖ → ‖z‖ < b →
      t ∈ ball (0 : ℂ) r ∧ (t, gh t z) ∈ W := by
    intro t ht z hz1 hz2
    have h := huv1 (show (t, z) ∈ u1 ×ˢ v1 from
      ⟨hu1 (ball_subset_closedBall ht), hann1 z (by linarith) (by rw [← hb]; exact hz2)⟩)
    exact ⟨h.1.1, h.2⟩
  -- the outer map `Φ_t = F_t⁻¹ ∘ ĝ_t`
  obtain ⟨Φo, hΦo⟩ : ∃ Φo : ℂ → ℂ → ℂ, Φo = fun t z => Inv t (gh t z) := ⟨_, rfl⟩
  have hΦoap : ∀ t z, Φo t z = Inv t (gh t z) := fun t z => by rw [hΦo]
  have hΦoW : ∀ t ∈ ball (0 : ℂ) (r / 2), ∀ z : ℂ, 1 ≤ ‖z‖ → ‖z‖ < b →
      Φo t z ∈ ball (0 : ℂ) R ∧ F t (Φo t z) = gh t z := by
    intro t ht z h1 h2
    rw [hΦoap]
    exact hWin t _ (hdom t ht z h1 h2).2
  have hΦo1 : ∀ t ∈ ball (0 : ℂ) (r / 2), ∀ z : ℂ, ‖z‖ = 1 → ∃ u : ℂ, ‖u‖ = 1 ∧ Φo t z = u ∧
      Function.invFun (wAS (ν t)) (z : ExtPlane) = (u : ExtPlane) := by
    intro t ht z hz
    have ht' := (hdom t ht z hz.ge (by rw [hz]; exact hb1)).1
    obtain ⟨u, hu, he, hinv⟩ := hgh1 t ht' z hz
    refine ⟨u, hu, ?_, hinv⟩
    rw [hΦoap, he, hleft t ht' u (hcl1R (mem_closedBall_zero_iff.mpr hu.le))]
  have hΦon1 : ∀ t ∈ ball (0 : ℂ) (r / 2), ∀ z : ℂ, ‖z‖ = 1 → ‖Φo t z‖ = 1 := by
    intro t ht z hz
    obtain ⟨u, hu, he, -⟩ := hΦo1 t ht z hz
    rw [he, hu]
  have hΦon : ∀ t ∈ ball (0 : ℂ) (r / 2), ∀ z : ℂ, 1 < ‖z‖ → ‖z‖ < b → 1 < ‖Φo t z‖ := by
    intro t ht z h1 h2
    by_contra hc
    have ht' := (hdom t ht z h1.le h2).1
    exact hgh2 t ht' z h1 _ (not_lt.mp hc) (hΦoW t ht z h1.le h2).2.symm
  have hΦoi : ∀ t ∈ ball (0 : ℂ) (r / 2), InjOn (Φo t) {z | 1 ≤ ‖z‖ ∧ ‖z‖ < b} := by
    intro t ht x hx y hy hxy
    have ht' := (hdom t ht x hx.1 hx.2).1
    have h1 := (hΦoW t ht x hx.1 hx.2).2
    have h2 := (hΦoW t ht y hy.1 hy.2).2
    rw [hxy] at h1
    exact hghi t ht' x y (h1.symm.trans h2)
  have hΦod : ∀ t ∈ ball (0 : ℂ) (r / 2), DifferentiableOn ℂ (Φo t) {z | 1 < ‖z‖ ∧ ‖z‖ < b} := by
    intro t ht z hz
    have ht' := (hdom t ht z hz.1.le hz.2).1
    have hgd : DifferentiableAt ℂ (gh t) z := by
      have hev : gh t =ᶠ[𝓝 z] gsans (ν t) := by
        filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds hz.1] with w hw
        exact hgh3 t ht' w hw
      exact (s3g_gsans_holo (hν t ht') hz.1).congr_of_eventuallyEq hev
    have hId := hInvD t ht' _ (hdom t ht z hz.1.le hz.2).2
    have hfe : Φo t = fun z => Inv t (gh t z) := by rw [hΦo]
    rw [hfe]
    exact (DifferentiableAt.comp (g := Inv t) (f := gh t) z hId hgd).differentiableWithinAt
  have hΦofe : (fun q : ℂ × ℂ => Φo q.1 q.2) =
      (fun p : ℂ × ℂ => Inv p.1 p.2) ∘ (fun q : ℂ × ℂ => (q.1, gh q.1 q.2)) := by
    funext q
    rw [hΦoap]
    rfl
  have hΦoc : ContinuousOn (fun q : ℂ × ℂ => Φo q.1 q.2) (ball (0 : ℂ) (r / 2) ×ˢ {z | 1 ≤ ‖z‖ ∧ ‖z‖ < b}) := by
    rw [hΦofe]
    refine hInvC.continuousOn.comp (continuousOn_fst.prodMk (hghc.mono ?_)) ?_
    · exact prod_mono hr2 (subset_univ _)
    · intro q hq
      exact (hdom q.1 hq.1 q.2 hq.2.1 hq.2.2).2
  have hΦoC : ContDiffOn ℝ 1 (fun q : ℂ × ℂ => Φo q.1 q.2) (ball (0 : ℂ) (r / 2) ×ˢ {z | 1 < ‖z‖ ∧ ‖z‖ < b}) := by
    have hgC : ContDiffOn ℝ 1 (fun q : ℂ × ℂ => gh q.1 q.2) (ball (0 : ℂ) (r / 2) ×ˢ {z | 1 < ‖z‖ ∧ ‖z‖ < b}) := by
      intro q hq
      have ht' : q.1 ∈ ball (0 : ℂ) r := hr2 hq.1
      have ha := s3g_gsans_analytic hν hνa (q := q) ⟨ht', hq.2.1⟩
      refine (ha.contDiffAt.congr_of_eventuallyEq ?_).contDiffWithinAt
      have hO : IsOpen (ball (0 : ℂ) r ×ˢ unitDiscExterior) :=
        isOpen_ball.prod (isOpen_lt continuous_const continuous_norm)
      filter_upwards [hO.mem_nhds ⟨ht', hq.2.1⟩] with x hx
      exact hgh3 x.1 hx.1 x.2 hx.2
    rw [hΦofe]
    exact hInvC.comp (contDiffOn_fst.prodMk hgC) (fun q hq => (hdom q.1 hq.1 q.2 hq.2.1.le hq.2.2).2)
  -- the reflected map `Φ̃_t` on `1/b < |z| < b`
  obtain ⟨Φt, hΦt⟩ : ∃ Φt : ℂ → ℂ → ℂ, Φt = fun t z => if ‖z‖ ≤ 1 then circleReflect (Φo t (circleReflect z))
      else circleReflect (circleReflect (Φo t (circleReflect (circleReflect z)))) := ⟨_, rfl⟩
  have hΦtf : ∀ t ∈ ball (0 : ℂ) (r / 2), (∀ z : ℂ, 1 ≤ ‖z‖ → ‖z‖ < b → Φt t z = Φo t z) ∧
      (∀ z : ℂ, b⁻¹ < ‖z‖ → ‖z‖ < 1 → ‖Φt t z‖ < 1 ∧ Φt t z = circleReflect (Φo t (circleReflect z))) ∧
      InjOn (Φt t) {z | b⁻¹ < ‖z‖ ∧ ‖z‖ < b} := fun t ht =>
    s3g_reflect_facts hb1 (hΦon1 t ht) (hΦon t ht) (hΦoi t ht) (by rw [hΦt])
  have hΦtd : ∀ t ∈ ball (0 : ℂ) (r / 2), DifferentiableOn ℂ (Φt t) {z | b⁻¹ < ‖z‖ ∧ ‖z‖ < b} := by
    intro t ht
    have hc : ContinuousOn (Φo t) {z | 1 ≤ ‖z‖ ∧ ‖z‖ < b} :=
      hΦoc.comp (continuousOn_const.prodMk continuousOn_id) (fun z hz => ⟨ht, hz⟩)
    have h := s3g_reflect hb1 (hΦod t ht) hc (hΦon1 t ht) (hΦon t ht)
    have hfe : Φt t = fun z => if ‖z‖ ≤ 1 then circleReflect (Φo t (circleReflect z))
        else circleReflect (circleReflect (Φo t (circleReflect (circleReflect z)))) := by rw [hΦt]
    rw [hfe]
    exact h
  -- radii `1/b < a₁ < 1 < a₂ < b`
  obtain ⟨a2, ha2⟩ : ∃ a : ℝ, a = (1 + b) / 2 := ⟨_, rfl⟩
  have ha21 : 1 < a2 := by rw [ha2]; linarith
  have ha2b : a2 < b := by rw [ha2]; linarith
  have ha20 : 0 < a2 := by linarith
  obtain ⟨a1, ha1⟩ : ∃ a : ℝ, a = a2⁻¹ := ⟨_, rfl⟩
  have ha10 : 0 < a1 := by rw [ha1]; exact inv_pos.mpr ha20
  have ha11 : a1 < 1 := by rw [ha1]; exact inv_lt_one_of_one_lt₀ ha21
  have ha1b : b⁻¹ < a1 := by rw [ha1]; exact inv_strictAnti₀ ha20 ha2b
  have hbi0 : 0 < b⁻¹ := inv_pos.mpr hb0
  have hOout : IsOpen {z : ℂ | 1 < ‖z‖ ∧ ‖z‖ < b} :=
    (isOpen_lt continuous_const continuous_norm).inter (isOpen_lt continuous_norm continuous_const)
  have hOin : IsOpen {z : ℂ | b⁻¹ < ‖z‖ ∧ ‖z‖ < 1} :=
    (isOpen_lt continuous_const continuous_norm).inter (isOpen_lt continuous_norm continuous_const)
  have hOann : IsOpen {z : ℂ | b⁻¹ < ‖z‖ ∧ ‖z‖ < b} :=
    (isOpen_lt continuous_const continuous_norm).inter (isOpen_lt continuous_norm continuous_const)
  -- joint C¹ of `Φ̃` on both sides, then across `𝕊¹` by the annulus Cauchy formula
  have hΦtCo : ContDiffOn ℝ 1 (fun q : ℂ × ℂ => Φt q.1 q.2) (ball (0 : ℂ) (r / 2) ×ˢ {z | 1 < ‖z‖ ∧ ‖z‖ < b}) :=
    hΦoC.congr fun q hq => (hΦtf q.1 hq.1).1 q.2 hq.2.1.le hq.2.2
  have hΦtCi : ContDiffOn ℝ 1 (fun q : ℂ × ℂ => Φt q.1 q.2) (ball (0 : ℂ) (r / 2) ×ˢ {z | b⁻¹ < ‖z‖ ∧ ‖z‖ < 1}) := by
    have hin : ContDiffOn ℝ 1 (fun q : ℂ × ℂ => circleReflect (Φo q.1 (circleReflect q.2)))
        (ball (0 : ℂ) (r / 2) ×ˢ {z | b⁻¹ < ‖z‖ ∧ ‖z‖ < 1}) := by
      intro q hq
      have hz0 : q.2 ≠ 0 := norm_pos_iff.mp (lt_trans hbi0 hq.2.1)
      have hcrin : 1 < ‖circleReflect q.2‖ ∧ ‖circleReflect q.2‖ < b := by
        rw [norm_circleReflect]
        refine ⟨(one_lt_inv₀ (norm_pos_iff.mpr hz0)).mpr hq.2.2, ?_⟩
        have := inv_strictAnti₀ hbi0 hq.2.1
        rwa [inv_inv] at this
      have hm : ContDiffAt ℝ 1 (fun q : ℂ × ℂ => (q.1, circleReflect q.2)) q :=
        contDiffAt_fst.prodMk (ContDiffAt.comp (g := circleReflect) (f := Prod.snd) q (s3g_cr_contDiffAt hz0)
          contDiffAt_snd)
      have hΦ1 : ContDiffAt ℝ 1 (fun q : ℂ × ℂ => Φo q.1 q.2) (q.1, circleReflect q.2) :=
        hΦoC.contDiffAt ((isOpen_ball.prod hOout).mem_nhds ⟨hq.1, hcrin⟩)
      have h2 : ContDiffAt ℝ 1 (fun q : ℂ × ℂ => Φo q.1 (circleReflect q.2)) q :=
        ContDiffAt.comp (g := fun q : ℂ × ℂ => Φo q.1 q.2) (f := fun q : ℂ × ℂ => (q.1, circleReflect q.2)) q hΦ1 hm
      have hne : Φo q.1 (circleReflect q.2) ≠ 0 := by
        intro h0
        have := hΦon q.1 hq.1 _ hcrin.1 hcrin.2
        rw [h0, norm_zero] at this
        linarith
      exact (ContDiffAt.comp (g := circleReflect) (f := fun q : ℂ × ℂ => Φo q.1 (circleReflect q.2)) q
        (s3g_cr_contDiffAt hne) h2).contDiffWithinAt
    exact hin.congr fun q hq => ((hΦtf q.1 hq.1).2.1 q.2 hq.2.1 hq.2.2).2
  obtain ⟨U2, hU2⟩ : ∃ U : Set ℂ, U = {z | a1 < ‖z‖ ∧ ‖z‖ < a2} := ⟨_, rfl⟩
  have hU2o : IsOpen U2 := by
    rw [hU2]
    exact (isOpen_lt continuous_const continuous_norm).inter (isOpen_lt continuous_norm continuous_const)
  have hU2s : U2 ⊆ {z | b⁻¹ < ‖z‖ ∧ ‖z‖ < b} := by
    intro z hz
    rw [hU2] at hz
    exact ⟨lt_trans ha1b hz.1, lt_trans hz.2 ha2b⟩
  have hsph2 : sphere (0 : ℂ) a2 ⊆ {z | 1 < ‖z‖ ∧ ‖z‖ < b} := fun z hz => by
    rw [mem_sphere_zero_iff_norm] at hz
    exact ⟨by rw [hz]; exact ha21, by rw [hz]; exact ha2b⟩
  have hsph1 : sphere (0 : ℂ) a1 ⊆ {z | b⁻¹ < ‖z‖ ∧ ‖z‖ < 1} := fun z hz => by
    rw [mem_sphere_zero_iff_norm] at hz
    exact ⟨by rw [hz]; exact ha1b, by rw [hz]; exact ha11⟩
  have hA := s3g_cauchy_param isOpen_ball hOout ha20 hsph2 hΦtCo
  have hB := s3g_cauchy_param isOpen_ball hOin ha10 hsph1 hΦtCi
  have hΦtC : ContDiffOn ℝ 1 (fun q : ℂ × ℂ => Φt q.1 q.2) (ball (0 : ℂ) (r / 2) ×ˢ U2) := by
    refine ((contDiffOn_const (c := (2 * π * I : ℂ)⁻¹)).mul ((hA.mono ?_).sub (hB.mono ?_))).congr ?_
    · intro q hq
      rw [hU2] at hq
      exact ⟨hq.1, ne_of_lt hq.2.2⟩
    · intro q hq
      rw [hU2] at hq
      exact ⟨hq.1, ne_of_gt hq.2.1⟩
    · intro q hq
      have hq2 := hq.2
      rw [hU2] at hq2
      refine s3g_annulus_cauchy ha10 (by linarith) hOann ?_ (hΦtd q.1 hq.1) hq2.1 hq2.2
      intro z hz
      refine ⟨lt_of_lt_of_le ha1b ?_, lt_of_le_of_lt (mem_closedBall_zero_iff.mp hz.1) ha2b⟩
      by_contra hc
      exact hz.2 (mem_ball_zero_iff.mpr (lt_of_not_ge hc))
  -- values of `Φ̃` stay in `|w| < R`; `F_t ∘ Φ̃_t = 𝗀_t` outside `𝕊¹`
  have hΦtR : ∀ t ∈ ball (0 : ℂ) (r / 2), ∀ z : ℂ, b⁻¹ < ‖z‖ → ‖z‖ < b → Φt t z ∈ ball (0 : ℂ) R := by
    intro t ht z h1 h2
    rcases lt_or_ge ‖z‖ 1 with h | h
    · rw [mem_ball_zero_iff]
      linarith [((hΦtf t ht).2.1 z h1 h).1]
    · rw [(hΦtf t ht).1 z h h2]
      exact (hΦoW t ht z h h2).1
  have hΦtle : ∀ t ∈ ball (0 : ℂ) (r / 2), ∀ z : ℂ, b⁻¹ < ‖z‖ → ‖z‖ ≤ 1 → ‖Φt t z‖ ≤ 1 := by
    intro t ht z h1 h2
    rcases h2.lt_or_eq with h | h
    · exact ((hΦtf t ht).2.1 z h1 h).1.le
    · rw [(hΦtf t ht).1 z h.ge (by rw [h]; exact hb1), hΦon1 t ht z h]
  have hFΦ : ∀ t ∈ ball (0 : ℂ) (r / 2), ∀ z : ℂ, 1 < ‖z‖ → ‖z‖ < b → F t (Φt t z) = gsans (ν t) z := by
    intro t ht z h1 h2
    rw [(hΦtf t ht).1 z h1.le h2, (hΦoW t ht z h1.le h2).2, hgh3 t (hr2 ht) z h1]
  -- the inverse family `H_t = Φ̃_t⁻¹`
  have hΦtd2 : ∀ t ∈ ball (0 : ℂ) (r / 2), DifferentiableOn ℂ (Φt t) U2 := fun t ht => (hΦtd t ht).mono hU2s
  have hΦti2 : ∀ t ∈ ball (0 : ℂ) (r / 2), InjOn (Φt t) U2 := fun t ht => (hΦtf t ht).2.2.mono hU2s
  obtain ⟨Inv2, hW2o, hInv2C, hleft2, hWin2, hInv2d⟩ := s3g_inv_family isOpen_ball hU2o hΦtC hΦtd2 hΦti2
  obtain ⟨W2, hW2⟩ : ∃ W : Set (ℂ × ℂ), W = (fun q : ℂ × ℂ => (q.1, Φt q.1 q.2)) '' (ball 0 (r / 2) ×ˢ U2) :=
    ⟨_, rfl⟩
  rw [← hW2] at hW2o hInv2C hWin2
  have h1U2 : ∀ y : ℂ, ‖y‖ = 1 → y ∈ U2 := fun y hy => by
    rw [hU2]
    exact ⟨by rw [hy]; exact ha11, by rw [hy]; exact ha21⟩
  have hcirc : ∀ t ∈ ball (0 : ℂ) (r / 2), ∀ w : ℂ, ‖w‖ = 1 →
      ∃ y : ℂ, ‖y‖ = 1 ∧ Φt t y = w ∧ wA (ν t) w = y := by
    intro t ht w hw
    obtain ⟨y, hy, he⟩ := wAS_maps_circle (hν t (hr2 ht)) hw
    obtain ⟨u, -, hu, hinv⟩ := hΦo1 t ht y hy
    have huw : u = w := by
      have h1 := hli t (w : ExtPlane)
      rw [he, hinv] at h1
      exact OnePoint.coe_injective h1
    refine ⟨y, hy, ?_, ?_⟩
    · rw [(hΦtf t ht).1 y hy.ge (by rw [hy]; exact hb1), hu, huw]
    · show finPart (wAS (ν t) (w : ExtPlane)) = y
      rw [he]
      rfl
  have hK2 : closedBall (0 : ℂ) (r / 4) ×ˢ sphere (0 : ℂ) 1 ⊆ W2 := by
    rintro ⟨t, w⟩ ⟨ht, hw⟩
    have ht' : t ∈ ball (0 : ℂ) (r / 2) := closedBall_subset_ball (by linarith) ht
    obtain ⟨y, hy, he, -⟩ := hcirc t ht' w (mem_sphere_zero_iff_norm.mp hw)
    rw [hW2]
    exact ⟨(t, y), ⟨ht', h1U2 y hy⟩, by rw [← he]⟩
  obtain ⟨u2, v2, -, hv2, hu2, hsv2, huv2⟩ :=
    generalized_tube_lemma (isCompact_closedBall (0 : ℂ) (r / 4)) (isCompact_sphere (0 : ℂ) 1) hW2o hK2
  obtain ⟨δ2, hδ2, hδ21, hann2⟩ := s3g_annulus_of_sphere hv2 hsv2
  obtain ⟨ρ, hρ⟩ : ∃ ρ : ℝ, ρ = max a1 (1 - δ2) := ⟨_, rfl⟩
  have hρ1 : ρ < 1 := by rw [hρ]; exact max_lt ha11 (by linarith)
  have hρa1 : a1 ≤ ρ := by rw [hρ]; exact le_max_left _ _
  have hρd : 1 - δ2 ≤ ρ := by rw [hρ]; exact le_max_right _ _
  have hr4 : ball (0 : ℂ) (r / 4) ⊆ ball 0 (r / 2) := ball_subset_ball (by linarith)
  have hdom2 : ∀ t ∈ ball (0 : ℂ) (r / 4), ∀ w : ℂ, ρ < ‖w‖ → ‖w‖ < 1 + δ2 → (t, w) ∈ W2 := fun t ht w h1 h2 =>
    huv2 (show (t, w) ∈ u2 ×ˢ v2 from ⟨hu2 (ball_subset_closedBall ht), hann2 w (by linarith) h2⟩)
  -- `G_t = F_t ∘ Φ̃_t` near `𝕊¹`, `𝗀_t` outside
  obtain ⟨G, hG⟩ : ∃ G : ℂ → ℂ → ℂ, G = fun t z => if ‖z‖ < a2 then F t (Φt t z) else gsans (ν t) z :=
    ⟨_, rfl⟩
  have hGap : ∀ t z, G t z = if ‖z‖ < a2 then F t (Φt t z) else gsans (ν t) z := fun t z => by rw [hG]
  have hGg : ∀ t ∈ ball (0 : ℂ) (r / 2), ∀ z : ℂ, 1 < ‖z‖ → G t z = gsans (ν t) z := by
    intro t ht z hz
    rw [hGap]
    split_ifs with h
    · exact hFΦ t ht z hz (lt_trans h ha2b)
    · rfl
  have hGF : ∀ t z, ‖z‖ < a2 → G t z = F t (Φt t z) := fun t z h => by rw [hGap, if_pos h]
  have hgC : ContDiffOn ℝ 1 (fun q : ℂ × ℂ => gsans (ν q.1) q.2) (ball (0 : ℂ) r ×ˢ unitDiscExterior) :=
    fun q hq => (s3g_gsans_analytic hν hνa hq).contDiffAt.contDiffWithinAt
  have hFΦC : ContDiffOn ℝ 1 (fun q : ℂ × ℂ => F q.1 (Φt q.1 q.2)) (ball (0 : ℂ) (r / 2) ×ˢ U2) := by
    refine hF.comp (f := fun q : ℂ × ℂ => (q.1, Φt q.1 q.2)) (contDiffOn_fst.prodMk hΦtC) ?_
    intro q hq
    have hq2 := hU2s hq.2
    exact ⟨hr2 hq.1, hΦtR q.1 hq.1 q.2 hq2.1 hq2.2⟩
  have hsetA : ∀ q : ℂ × ℂ, q ∈ ball (0 : ℂ) (r / 4) ×ˢ {z : ℂ | ρ < ‖z‖} → ‖q.2‖ < a2 →
      q ∈ ball (0 : ℂ) (r / 2) ×ˢ U2 := by
    intro q hq h
    refine ⟨hr4 hq.1, ?_⟩
    rw [hU2]
    exact ⟨lt_of_le_of_lt hρa1 hq.2, h⟩
  refine ⟨r / 4, by linarith, ρ, hρ1, 1 + δ2, by linarith, G, Inv2, ?_, ?_, fun t ht => ?_⟩
  · -- C¹ of `G`
    refine contDiffOn_of_locally_contDiffOn fun q hq => ?_
    rcases lt_or_ge ‖q.2‖ a2 with h | h
    · refine ⟨univ ×ˢ {z : ℂ | ‖z‖ < a2}, isOpen_univ.prod (isOpen_lt continuous_norm continuous_const),
        ⟨mem_univ _, h⟩, ?_⟩
      refine (hFΦC.mono fun x hx => hsetA x hx.1 hx.2.2).congr fun x hx => ?_
      exact hGF x.1 x.2 hx.2.2
    · refine ⟨univ ×ˢ unitDiscExterior, isOpen_univ.prod (isOpen_lt continuous_const continuous_norm),
        ⟨mem_univ _, lt_of_lt_of_le ha21 h⟩, ?_⟩
      refine (hgC.mono fun x hx => ⟨hr2 (hr4 hx.1.1), hx.2.2⟩).congr fun x hx => ?_
      exact hGg x.1 (hr4 hx.1.1) x.2 hx.2.2
  · -- C¹ of `H`
    exact hInv2C.mono fun q hq => hdom2 q.1 hq.1 q.2 hq.2.1 hq.2.2
  have ht2 : t ∈ ball (0 : ℂ) (r / 2) := hr4 ht
  have ht1 : t ∈ ball (0 : ℂ) r := hr2 ht2
  refine ⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩⟩
  · -- `G_t` holomorphic
    intro z hz
    have hz' : ρ < ‖z‖ := hz
    rcases lt_or_ge ‖z‖ a2 with h | h
    · have hzU : z ∈ U2 := by rw [hU2]; exact ⟨lt_of_le_of_lt hρa1 hz', h⟩
      have hzA := hU2s hzU
      have hd1 : DifferentiableAt ℂ (Φt t) z := (hΦtd t ht2).differentiableAt (hOann.mem_nhds hzA)
      have hd2 : DifferentiableAt ℂ (F t) (Φt t z) :=
        (hFh t ht1).differentiableAt (isOpen_ball.mem_nhds (hΦtR t ht2 z hzA.1 hzA.2))
      have hev : G t =ᶠ[𝓝 z] fun z => F t (Φt t z) := by
        filter_upwards [(isOpen_lt continuous_norm continuous_const).mem_nhds h] with w hw
        exact hGF t w hw
      exact ((DifferentiableAt.comp (g := F t) (f := Φt t) z hd2 hd1).congr_of_eventuallyEq
        hev).differentiableWithinAt
    · have hz1 : 1 < ‖z‖ := lt_of_lt_of_le ha21 h
      have hev : G t =ᶠ[𝓝 z] gsans (ν t) := by
        filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds hz1] with w hw
        exact hGg t ht2 w hw
      exact ((s3g_gsans_holo (hν t ht1) hz1).congr_of_eventuallyEq hev).differentiableWithinAt
  · -- `G_t` injective
    have hGin : ∀ z : ℂ, ρ < ‖z‖ → ‖z‖ ≤ 1 →
        G t z = F t (Φt t z) ∧ ‖Φt t z‖ ≤ 1 ∧ Φt t z ∈ ball (0 : ℂ) R := by
      intro z h1 h2
      have hb' : b⁻¹ < ‖z‖ := lt_of_lt_of_le ha1b (hρa1.trans h1.le)
      exact ⟨hGF t z (lt_of_le_of_lt h2 ha21), hΦtle t ht2 z hb' h2, hΦtR t ht2 z hb' (by linarith)⟩
    have hGout : ∀ z : ℂ, 1 < ‖z‖ → G t z = gh t z := fun z h => by
      rw [hGg t ht2 z h, hgh3 t ht1 z h]
    intro x hx y hy hxy
    have hx' : ρ < ‖x‖ := hx
    have hy' : ρ < ‖y‖ := hy
    rcases le_or_gt ‖x‖ 1 with hx1 | hx1 <;> rcases le_or_gt ‖y‖ 1 with hy1 | hy1
    · obtain ⟨hgx, -, hRx⟩ := hGin x hx' hx1
      obtain ⟨hgy, -, hRy⟩ := hGin y hy' hy1
      rw [hgx, hgy] at hxy
      have hbx : b⁻¹ < ‖x‖ := lt_of_lt_of_le ha1b (hρa1.trans hx'.le)
      have hby : b⁻¹ < ‖y‖ := lt_of_lt_of_le ha1b (hρa1.trans hy'.le)
      exact (hΦtf t ht2).2.2 ⟨hbx, by linarith⟩ ⟨hby, by linarith⟩ (hFi t ht1 hRx hRy hxy)
    · exfalso
      obtain ⟨hgx, hlx, -⟩ := hGin x hx' hx1
      rw [hgx, hGout y hy1] at hxy
      exact hgh2 t ht1 y hy1 _ hlx hxy.symm
    · exfalso
      obtain ⟨hgy, hly, -⟩ := hGin y hy' hy1
      rw [hgy, hGout x hx1] at hxy
      exact hgh2 t ht1 x hx1 _ hly hxy
    · rw [hGout x hx1, hGout y hy1] at hxy
      exact hghi t ht1 x y hxy
  · -- `G_t = g_{ν_t}` on `𝔻*`
    intro z hz
    rw [hGg t ht2 z hz, s3g_gsans_eq (hν t ht1)]
  · -- `H_t` holomorphic
    refine (hInv2d t ht2).mono fun w hw => ?_
    obtain ⟨h1, h2⟩ := hWin2 t w (hdom2 t ht w hw.1 hw.2)
    exact ⟨Inv2 t w, h1, h2⟩
  · -- `H_t` injective
    intro x hx y hy hxy
    have hx2 := (hWin2 t x (hdom2 t ht x hx.1 hx.2)).2
    have hy2 := (hWin2 t y (hdom2 t ht y hy.1 hy.2)).2
    have hxy' : Inv2 t x = Inv2 t y := hxy
    rw [← hx2, ← hy2, hxy']
  · -- `H_t = w^A_{ν_t}` on `𝕊¹`
    intro z hz
    have hz1 : ‖z‖ = 1 := hz
    obtain ⟨y, hy, he, hwA⟩ := hcirc t ht2 z hz1
    rw [hwA, ← he, hleft2 t ht2 y (h1U2 y hy)]

/-- **(b′)** An annulus extension of the welding `h_{ν_t}` (C¹ family) gives an extension of `f_{ν_t}` across `𝕊¹`
(C¹ family). -/
theorem s3g_ext_of_weld {ν : ℂ → LinfStar} {r ρ R : ℝ} (hr : 0 < r) (hρ : ρ < 1) (hR : 1 < R)
    (hν : ∀ t ∈ ball (0 : ℂ) r, ν t ∈ LinfStarBall) (hνa : ∀ t ∈ ball (0 : ℂ) r, AnalyticAt ℝ ν t)
    {H : ℂ → ℂ → ℂ} (hH : ContDiffOn ℝ 1 (fun q : ℂ × ℂ => H q.1 q.2) (ball 0 r ×ˢ {z | ρ < ‖z‖ ∧ ‖z‖ < R}))
    (hHt : ∀ t ∈ ball (0 : ℂ) r, DifferentiableOn ℂ (H t) {z | ρ < ‖z‖ ∧ ‖z‖ < R} ∧
      InjOn (H t) {z | ρ < ‖z‖ ∧ ‖z‖ < R} ∧ ∀ z ∈ unitCircle, H t z = wA (ν t) z) :
    ∃ r' > 0, ∃ R' > 1, ∃ F : ℂ → ℂ → ℂ,
      ContDiffOn ℝ 1 (fun q : ℂ × ℂ => F q.1 q.2) (ball 0 r' ×ˢ ball 0 R') ∧
      ∀ t ∈ ball (0 : ℂ) r', DifferentiableOn ℂ (F t) (ball 0 R') ∧ InjOn (F t) (ball 0 R') ∧
        EqOn (F t) (fB (ν t)) unitDisc := by
  have hνc : ∀ t ∈ ball (0 : ℂ) r, ContinuousAt ν t := fun t ht => (hνa t ht).continuousAt
  -- the sphere welding `ĝ`
  obtain ⟨gh, hgh⟩ : ∃ gh : ℂ → ℂ → ℂ,
      gh = fun t (z : ℂ) => finPart (wB (ν t) (Function.invFun (wAS (ν t)) (z : ExtPlane))) := ⟨_, rfl⟩
  have hghap : ∀ t z, gh t z = finPart (wB (ν t) (Function.invFun (wAS (ν t)) (z : ExtPlane))) :=
    fun t z => by rw [hgh]
  have hghcoe : ∀ t ∈ ball (0 : ℂ) r, ∀ z : ℂ,
      ((gh t z : ℂ) : ExtPlane) = wB (ν t) (Function.invFun (wAS (ν t)) (z : ExtPlane)) := fun t ht z => by
    rw [hghap]
    exact coe_finPart_of_ne (s3g_sphere_pre (hν t ht) z).1
  have hghc : ContinuousOn (fun q : ℂ × ℂ => gh q.1 q.2) (ball 0 r ×ˢ univ) := by
    rw [hgh]
    exact s3g_ghat_cont hν hνc
  have hri : ∀ t y, wAS (ν t) (Function.invFun (wAS (ν t)) y) = y := fun t =>
    Function.rightInverse_invFun (wAS_bijective (ν t)).2
  have hli : ∀ t y, Function.invFun (wAS (ν t)) (wAS (ν t) y) = y := fun t =>
    Function.leftInverse_invFun (wAS_bijective (ν t)).1
  have hgh3 : ∀ t ∈ ball (0 : ℂ) r, ∀ z ∈ unitDiscExterior, gh t z = gsans (ν t) z := by
    intro t ht z hz
    rw [hghap, s3g_gsans_eq (hν t ht), s3g_gMu_sphere (hν t ht) hz]
  have hghi : ∀ t ∈ ball (0 : ℂ) r, ∀ z₁ z₂ : ℂ, gh t z₁ = gh t z₂ → z₁ = z₂ := by
    intro t ht z₁ z₂ he
    have h1 : ((gh t z₁ : ℂ) : ExtPlane) = ((gh t z₂ : ℂ) : ExtPlane) := by rw [he]
    rw [hghcoe t ht, hghcoe t ht] at h1
    have h2 := congrArg (wAS (ν t)) ((wB_bijective (ν t)).1 h1)
    rw [hri, hri] at h2
    exact OnePoint.coe_injective h2
  have hfBcoe : ∀ t ∈ ball (0 : ℂ) r, ∀ u : ℂ, ‖u‖ ≤ 1 → ((fB (ν t) u : ℂ) : ExtPlane) = wB (ν t) (u : ExtPlane) :=
    fun t ht u hu => coe_finPart_of_ne (s5e_wB_finite (hν t ht) hu)
  -- the welding identity on `𝕊¹`: `ĝ_t(H_t ζ) = f_t(ζ)`
  have hweld : ∀ t ∈ ball (0 : ℂ) r, ∀ ζ : ℂ, ‖ζ‖ = 1 → gh t (H t ζ) = fB (ν t) ζ := by
    intro t ht ζ hζ
    apply OnePoint.coe_injective
    rw [hghcoe t ht, (hHt t ht).2.2 ζ hζ, hfBcoe t ht ζ hζ.le]
    obtain ⟨u, -, hu⟩ := wAS_maps_circle (hν t ht) hζ
    show wB (ν t) (Function.invFun (wAS (ν t)) ((finPart (wAS (ν t) (ζ : ExtPlane)) : ℂ) : ExtPlane)) = _
    rw [hu, finPart_coe, ← hu, hli]
  -- orientation: `|H_t z| > 1` for `1 < |z| < R`
  have hor : ∀ t ∈ ball (0 : ℂ) r, ∀ z : ℂ, 1 < ‖z‖ → ‖z‖ < R → 1 < ‖H t z‖ := fun t ht =>
    s3g_orient hρ hR (hHt t ht).1 (hHt t ht).2.1 (hν t ht) (hHt t ht).2.2
  -- a symmetric annulus `1/R₁ < |z| < R₁` inside `ρ < |z| < R`
  obtain ⟨s, hs⟩ : ∃ s : ℝ, s = (max ρ 0 + 1) / 2 := ⟨_, rfl⟩
  have hs0 : 0 < s := by rw [hs]; linarith [le_max_right ρ 0]
  have hs1 : s < 1 := by rw [hs]; linarith [max_lt hρ one_pos]
  have hsρ : ρ < s := by rw [hs]; linarith [le_max_left ρ 0, max_lt hρ one_pos]
  obtain ⟨R1, hR1⟩ : ∃ R1 : ℝ, R1 = min R s⁻¹ := ⟨_, rfl⟩
  have hR11 : 1 < R1 := by rw [hR1]; exact lt_min hR (one_lt_inv₀ hs0 |>.mpr hs1)
  have hR1R : R1 ≤ R := by rw [hR1]; exact min_le_left _ _
  have hR10 : 0 < R1 := by linarith
  have hR1i : ρ < R1⁻¹ := by
    have h1 : R1 ≤ s⁻¹ := by rw [hR1]; exact min_le_right _ _
    have h2 : s ≤ R1⁻¹ := by
      have := inv_anti₀ hR10 h1
      rwa [inv_inv] at this
    linarith
  have hR1i1 : R1⁻¹ < 1 := inv_lt_one_of_one_lt₀ hR11
  obtain ⟨A, hA⟩ : ∃ A : Set ℂ, A = {z : ℂ | R1⁻¹ < ‖z‖ ∧ ‖z‖ < R1} := ⟨_, rfl⟩
  have hAo : IsOpen A := by
    rw [hA]
    exact (isOpen_lt continuous_const continuous_norm).inter (isOpen_lt continuous_norm continuous_const)
  have hAH : ∀ z ∈ A, ρ < ‖z‖ ∧ ‖z‖ < R := fun z hz => by
    rw [hA] at hz
    exact ⟨lt_trans hR1i hz.1, lt_of_lt_of_le hz.2 hR1R⟩
  -- the glued extension
  obtain ⟨F, hFdef⟩ : ∃ F : ℂ → ℂ → ℂ, F = fun t z => if ‖z‖ ≤ 1 then fB (ν t) z else gh t (H t z) :=
    ⟨_, rfl⟩
  have hFap : ∀ t z, F t z = if ‖z‖ ≤ 1 then fB (ν t) z else gh t (H t z) := fun t z => by rw [hFdef]
  have hFin : ∀ t z, ‖z‖ ≤ 1 → F t z = fB (ν t) z := fun t z h => by rw [hFap, if_pos h]
  have hFout : ∀ t ∈ ball (0 : ℂ) r, ∀ z : ℂ, 1 ≤ ‖z‖ → ‖z‖ < R → F t z = gh t (H t z) := by
    intro t ht z h1 h2
    rcases h1.lt_or_eq with h | h
    · rw [hFap, if_neg (not_le.mpr h)]
    · rw [hFin t z h.symm.le, hweld t ht z h.symm]
  have hFg : ∀ t ∈ ball (0 : ℂ) r, ∀ z : ℂ, 1 < ‖z‖ → ‖z‖ < R → F t z = gsans (ν t) (H t z) := by
    intro t ht z h1 h2
    rw [hFout t ht z h1.le h2, hgh3 t ht _ (hor t ht z h1 h2)]
  -- holomorphy of `F_t` on `|z| < R₁`
  have hFd : ∀ t ∈ ball (0 : ℂ) r, DifferentiableOn ℂ (F t) (ball 0 R1) := by
    intro t ht
    have hμ := hν t ht
    obtain ⟨hfd, -⟩ := fB_holomorphic_injective hμ
    have hHd : ∀ z ∈ A, DifferentiableAt ℂ (H t) z := fun z hz =>
      (hHt t ht).1.differentiableAt
        (((isOpen_lt continuous_const continuous_norm).inter (isOpen_lt continuous_norm continuous_const)).mem_nhds
          (hAH z hz))
    have hdin : ∀ z : ℂ, ‖z‖ < 1 → DifferentiableAt ℂ (F t) z := by
      intro z hz
      have hev : F t =ᶠ[𝓝 z] fB (ν t) := by
        filter_upwards [(isOpen_lt continuous_norm continuous_const).mem_nhds hz] with w hw
        exact hFin t w hw.le
      exact (hfd.differentiableAt (isOpen_ball.mem_nhds (mem_ball_zero_iff.mpr hz))).congr_of_eventuallyEq hev
    have hdout : ∀ z ∈ A, 1 < ‖z‖ → DifferentiableAt ℂ (F t) z := by
      intro z hz h1
      have hz2 := (hAH z hz).2
      have hev : F t =ᶠ[𝓝 z] fun w => gsans (ν t) (H t w) := by
        have hO : IsOpen {w : ℂ | 1 < ‖w‖ ∧ ‖w‖ < R} :=
          (isOpen_lt continuous_const continuous_norm).inter (isOpen_lt continuous_norm continuous_const)
        filter_upwards [hO.mem_nhds ⟨h1, hz2⟩] with w hw
        exact hFg t ht w hw.1 hw.2
      have hg := s3g_gsans_holo hμ (hor t ht z h1 hz2)
      exact (DifferentiableAt.comp (g := gsans (ν t)) (f := H t) z hg (hHd z hz)).congr_of_eventuallyEq hev
    have hcA : ContinuousOn (F t) A := by
      have hc1 : ContinuousOn (fB (ν t)) (closedBall 0 1) := s3g_fB_contOn hμ
      have hHc : ContinuousOn (H t) {w : ℂ | ρ < ‖w‖ ∧ ‖w‖ < R} := (hHt t ht).1.continuousOn
      have hgt : Continuous (gh t) := by
        have h : ContinuousOn (fun w : ℂ => gh t w) univ :=
          hghc.comp (s := univ) (continuousOn_const.prodMk continuousOn_id) (fun w _ => ⟨ht, mem_univ w⟩)
        exact continuousOn_univ.mp h
      have hc2 : ContinuousOn (fun z => gh t (H t z)) {w : ℂ | 1 ≤ ‖w‖ ∧ ‖w‖ < R} :=
        hgt.comp_continuousOn (hHc.mono fun w hw => ⟨lt_of_lt_of_le hρ hw.1, hw.2⟩)
      intro z hz
      have hzR := hAH z hz
      have hw1 : ContinuousWithinAt (F t) (closedBall 0 1) z := by
        by_cases hz1 : ‖z‖ ≤ 1
        · exact (hc1 z (mem_closedBall_zero_iff.mpr hz1)).congr
            (fun w hw => hFin t w (mem_closedBall_zero_iff.mp hw)) (hFin t z hz1)
        · have hcl : IsClosed (closedBall (0 : ℂ) 1) := isClosed_closedBall
          refine (continuousWithinAt_of_notMem_closure ?_)
          rw [hcl.closure_eq, mem_closedBall_zero_iff]
          exact hz1
      have hw2 : ContinuousWithinAt (F t) {w : ℂ | 1 ≤ ‖w‖ ∧ ‖w‖ < R} z := by
        by_cases hz1 : 1 ≤ ‖z‖
        · exact (hc2 z ⟨hz1, hzR.2⟩).congr (fun w hw => hFout t ht w hw.1 hw.2) (hFout t ht z hz1 hzR.2)
        · refine continuousWithinAt_of_notMem_closure fun hcl => hz1 ?_
          have hsub : closure {w : ℂ | 1 ≤ ‖w‖ ∧ ‖w‖ < R} ⊆ {w : ℂ | 1 ≤ ‖w‖} :=
            closure_minimal (fun w hw => hw.1) (isClosed_le continuous_const continuous_norm)
          exact hsub hcl
      have hu := hw1.union hw2
      refine (hu.continuousAt ?_).continuousWithinAt
      refine Filter.mem_of_superset ((isOpen_lt continuous_norm continuous_const).mem_nhds hzR.2) ?_
      intro w hw
      by_cases hw1' : ‖w‖ ≤ 1
      · exact Or.inl (mem_closedBall_zero_iff.mpr hw1')
      · exact Or.inr ⟨(not_le.mp hw1').le, hw⟩
    have hAn : ∀ z ∈ A, -z ∈ A := fun z hz => by
      rw [hA] at hz ⊢
      simpa only [mem_setOf_eq, norm_neg] using hz
    have hdA := s3g_circle_removable hAo hAn hcA (fun z hz hz1 => by
      rcases lt_or_gt_of_ne hz1 with h | h
      · exact hdin z h
      · exact hdout z hz h)
    intro z hz
    have hz' : ‖z‖ < R1 := mem_ball_zero_iff.mp hz
    rcases lt_or_ge ‖z‖ 1 with h | h
    · exact (hdin z h).differentiableWithinAt
    · have hzA : z ∈ A := by rw [hA]; exact ⟨lt_of_lt_of_le hR1i1 h, hz'⟩
      exact (hdA.differentiableAt (hAo.mem_nhds hzA)).differentiableWithinAt
  -- injectivity of `F_t` on `|z| < R₁`
  have hFi : ∀ t ∈ ball (0 : ℂ) r, InjOn (F t) (ball 0 R1) := by
    intro t ht x hx y hy hxy
    have hx' : ‖x‖ < R := lt_of_lt_of_le (mem_ball_zero_iff.mp hx) hR1R
    have hy' : ‖y‖ < R := lt_of_lt_of_le (mem_ball_zero_iff.mp hy) hR1R
    have hcross : ∀ a b : ℂ, ‖a‖ ≤ 1 → 1 < ‖b‖ → ‖b‖ < R → F t a ≠ F t b := by
      intro a b ha hb1 hb2 he
      rw [hFin t a ha, hFout t ht b hb1.le hb2] at he
      have h1 : ((fB (ν t) a : ℂ) : ExtPlane) = ((gh t (H t b) : ℂ) : ExtPlane) := by rw [he]
      rw [hfBcoe t ht a ha, hghcoe t ht] at h1
      exact (s3g_sphere_pre (hν t ht) (H t b)).2.2 (hor t ht b hb1 hb2) a ha ((wB_bijective (ν t)).1 h1).symm
    rcases le_or_gt ‖x‖ 1 with hx1 | hx1 <;> rcases le_or_gt ‖y‖ 1 with hy1 | hy1
    · rw [hFin t x hx1, hFin t y hy1] at hxy
      have h1 : ((fB (ν t) x : ℂ) : ExtPlane) = ((fB (ν t) y : ℂ) : ExtPlane) := by rw [hxy]
      rw [hfBcoe t ht x hx1, hfBcoe t ht y hy1] at h1
      exact OnePoint.coe_injective ((wB_bijective (ν t)).1 h1)
    · exact absurd hxy (hcross x y hx1 hy1 hy')
    · exact absurd hxy.symm (hcross y x hy1 hx1 hx')
    · rw [hFout t ht x hx1.le hx', hFout t ht y hy1.le hy'] at hxy
      exact (hHt t ht).2.1 ⟨lt_trans hρ hx1, hx'⟩ ⟨lt_trans hρ hy1, hy'⟩ (hghi t ht _ _ hxy)
  -- joint C¹: inside, outside, and across `𝕊¹` by the annulus Cauchy formula
  have hCin : ContDiffOn ℝ 1 (fun q : ℂ × ℂ => fB (ν q.1) q.2) (ball (0 : ℂ) r ×ˢ unitDisc) := by
    intro q hq
    have hm : AnalyticAt ℝ (fun q : ℂ × ℂ => (ν q.1, q.2)) q :=
      (AnalyticAt.comp_of_eq (g := ν) (f := fun q : ℂ × ℂ => q.1) (hνa q.1 hq.1) analyticAt_fst rfl).prod
        analyticAt_snd
    exact (AnalyticAt.comp_of_eq (g := fun p : LinfStar × ℂ => fB p.1 p.2) (f := fun q : ℂ × ℂ => (ν q.1, q.2))
      (s5t53_fB_joint (hν q.1 hq.1) hq.2) hm rfl).contDiffAt.contDiffWithinAt
  have hOout : IsOpen {z : ℂ | 1 < ‖z‖ ∧ ‖z‖ < R} :=
    (isOpen_lt continuous_const continuous_norm).inter (isOpen_lt continuous_norm continuous_const)
  have hCout : ContDiffOn ℝ 1 (fun q : ℂ × ℂ => gsans (ν q.1) (H q.1 q.2))
      (ball (0 : ℂ) r ×ˢ {z : ℂ | 1 < ‖z‖ ∧ ‖z‖ < R}) := by
    have hgC : ContDiffOn ℝ 1 (fun q : ℂ × ℂ => gsans (ν q.1) q.2) (ball (0 : ℂ) r ×ˢ unitDiscExterior) :=
      fun q hq => (s3g_gsans_analytic hν hνa hq).contDiffAt.contDiffWithinAt
    refine hgC.comp (f := fun q : ℂ × ℂ => (q.1, H q.1 q.2)) (contDiffOn_fst.prodMk (hH.mono ?_)) ?_
    · exact prod_mono subset_rfl (fun z hz => ⟨lt_trans hρ hz.1, hz.2⟩)
    · intro q hq
      exact ⟨hq.1, hor q.1 hq.1 q.2 hq.2.1 hq.2.2⟩
  have hFCin : ContDiffOn ℝ 1 (fun q : ℂ × ℂ => F q.1 q.2) (ball (0 : ℂ) r ×ˢ unitDisc) :=
    hCin.congr fun q hq => hFin q.1 q.2 (mem_ball_zero_iff.mp hq.2).le
  have hFCout : ContDiffOn ℝ 1 (fun q : ℂ × ℂ => F q.1 q.2) (ball (0 : ℂ) r ×ˢ {z : ℂ | 1 < ‖z‖ ∧ ‖z‖ < R}) :=
    hCout.congr fun q hq => hFg q.1 hq.1 q.2 hq.2.1 hq.2.2
  obtain ⟨a2, ha2⟩ : ∃ a : ℝ, a = (1 + R1) / 2 := ⟨_, rfl⟩
  have ha21 : 1 < a2 := by rw [ha2]; linarith
  have ha2R : a2 < R1 := by rw [ha2]; linarith
  have ha20 : 0 < a2 := by linarith
  obtain ⟨a1, ha1⟩ : ∃ a : ℝ, a = a2⁻¹ := ⟨_, rfl⟩
  have ha10 : 0 < a1 := by rw [ha1]; exact inv_pos.mpr ha20
  have ha11 : a1 < 1 := by rw [ha1]; exact inv_lt_one_of_one_lt₀ ha21
  have hsph2 : sphere (0 : ℂ) a2 ⊆ {z : ℂ | 1 < ‖z‖ ∧ ‖z‖ < R} := fun z hz => by
    rw [mem_sphere_zero_iff_norm] at hz
    exact ⟨by rw [hz]; exact ha21, by rw [hz]; linarith⟩
  have hsph1 : sphere (0 : ℂ) a1 ⊆ unitDisc := fun z hz => by
    rw [mem_sphere_zero_iff_norm] at hz
    show z ∈ ball (0 : ℂ) 1
    rw [mem_ball_zero_iff, hz]
    exact ha11
  have hAc := s3g_cauchy_param isOpen_ball hOout ha20 hsph2 hFCout
  have hBc := s3g_cauchy_param isOpen_ball isOpen_ball ha10 hsph1 hFCin
  have hFCann : ContDiffOn ℝ 1 (fun q : ℂ × ℂ => F q.1 q.2) (ball (0 : ℂ) r ×ˢ {z : ℂ | a1 < ‖z‖ ∧ ‖z‖ < a2}) := by
    refine ((contDiffOn_const (c := (2 * π * I : ℂ)⁻¹)).mul ((hAc.mono ?_).sub (hBc.mono ?_))).congr ?_
    · intro q hq
      exact ⟨hq.1, ne_of_lt hq.2.2⟩
    · intro q hq
      exact ⟨hq.1, ne_of_gt hq.2.1⟩
    · intro q hq
      refine s3g_annulus_cauchy ha10 (by linarith) isOpen_ball ?_ (hFd q.1 hq.1) hq.2.1 hq.2.2
      intro z hz
      exact mem_ball_zero_iff.mpr (lt_of_le_of_lt (mem_closedBall_zero_iff.mp hz.1) ha2R)
  refine ⟨r, hr, a2, ha21, F, ?_, fun t ht => ⟨(hFd t ht).mono (ball_subset_ball ha2R.le),
    (hFi t ht).mono (ball_subset_ball ha2R.le), fun z hz => hFin t z (mem_ball_zero_iff.mp hz).le⟩⟩
  refine contDiffOn_of_locally_contDiffOn fun q hq => ?_
  rcases lt_or_ge ‖q.2‖ 1 with h | h
  · refine ⟨univ ×ˢ ball (0 : ℂ) 1, isOpen_univ.prod isOpen_ball, ⟨mem_univ _, mem_ball_zero_iff.mpr h⟩, ?_⟩
    exact hFCin.mono fun x hx => ⟨hx.1.1, hx.2.2⟩
  · refine ⟨univ ×ˢ {z : ℂ | a1 < ‖z‖ ∧ ‖z‖ < a2},
      isOpen_univ.prod ((isOpen_lt continuous_const continuous_norm).inter (isOpen_lt continuous_norm continuous_const)),
      ⟨mem_univ _, lt_of_lt_of_le ha11 h, mem_ball_zero_iff.mp hq.2⟩, ?_⟩
    exact hFCann.mono fun x hx => ⟨hx.1.1, hx.2.2⟩

/-- **(c)** Welding extensions compose: `w^A_{μ_t * κ} = w^A_{μ_t} ∘ w^A_κ`. -/
theorem s3g_weld_mul {μ : ℂ → LinfStar} {κ : LinfStar} (hκ : κ ∈ LinfStarBall) {r ρ R ρ₀ R₀ : ℝ} (hr : 0 < r)
    (hρ : ρ < 1) (hR : 1 < R) (hρ₀ : ρ₀ < 1) (hR₀ : 1 < R₀)
    (hμ : ∀ t ∈ ball (0 : ℂ) r, μ t ∈ LinfStarBall)
    {H : ℂ → ℂ → ℂ} (hH : ContDiffOn ℝ 1 (fun q : ℂ × ℂ => H q.1 q.2) (ball 0 r ×ˢ {z | ρ < ‖z‖ ∧ ‖z‖ < R}))
    (hHt : ∀ t ∈ ball (0 : ℂ) r, DifferentiableOn ℂ (H t) {z | ρ < ‖z‖ ∧ ‖z‖ < R} ∧
      InjOn (H t) {z | ρ < ‖z‖ ∧ ‖z‖ < R} ∧ ∀ z ∈ unitCircle, H t z = wA (μ t) z)
    {K : ℂ → ℂ} (hK : DifferentiableOn ℂ K {z | ρ₀ < ‖z‖ ∧ ‖z‖ < R₀})
    (hKi : InjOn K {z | ρ₀ < ‖z‖ ∧ ‖z‖ < R₀}) (hKc : ∀ z ∈ unitCircle, K z = wA κ z) :
    ∃ r' > 0, ∃ ρ' < 1, ∃ R' > 1, ∃ H' : ℂ → ℂ → ℂ,
      ContDiffOn ℝ 1 (fun q : ℂ × ℂ => H' q.1 q.2) (ball 0 r' ×ˢ {z | ρ' < ‖z‖ ∧ ‖z‖ < R'}) ∧
      ∀ t ∈ ball (0 : ℂ) r', DifferentiableOn ℂ (H' t) {z | ρ' < ‖z‖ ∧ ‖z‖ < R'} ∧
        InjOn (H' t) {z | ρ' < ‖z‖ ∧ ‖z‖ < R'} ∧ ∀ z ∈ unitCircle, H' t z = wA (beltramiMul (μ t) κ) z := by
  -- `K` maps `𝕊¹` into itself
  have hKs : ∀ z ∈ unitCircle, K z ∈ unitCircle := by
    intro z hz
    obtain ⟨u, hu, he⟩ := wAS_maps_circle hκ (show ‖z‖ = 1 from hz)
    rw [hKc z hz]
    show ‖finPart (wAS κ (z : ExtPlane))‖ = 1
    rw [he]
    exact hu
  -- an annulus that `K` maps into the annulus of `H`
  have hKcont : ContinuousOn K {z : ℂ | ρ₀ < ‖z‖ ∧ ‖z‖ < R₀} := hK.continuousOn
  have hA₀ : IsOpen {z : ℂ | ρ₀ < ‖z‖ ∧ ‖z‖ < R₀} :=
    (isOpen_lt continuous_const continuous_norm).inter (isOpen_lt continuous_norm continuous_const)
  have hA : IsOpen {z : ℂ | ρ < ‖z‖ ∧ ‖z‖ < R} :=
    (isOpen_lt continuous_const continuous_norm).inter (isOpen_lt continuous_norm continuous_const)
  have hUo := hKcont.isOpen_inter_preimage hA₀ hA
  have hcU : unitCircle ⊆ {z : ℂ | ρ₀ < ‖z‖ ∧ ‖z‖ < R₀} ∩ K ⁻¹' {z : ℂ | ρ < ‖z‖ ∧ ‖z‖ < R} := by
    intro z hz
    have hz1 : ‖z‖ = 1 := hz
    have hk1 : ‖K z‖ = 1 := hKs z hz
    exact ⟨⟨by rw [hz1]; exact hρ₀, by rw [hz1]; exact hR₀⟩, ⟨by rw [hk1]; exact hρ, by rw [hk1]; exact hR⟩⟩
  obtain ⟨ε, hε, hε1, hεU⟩ := s3g_annulus_sub hUo hcU
  have hmaps : MapsTo K {z : ℂ | 1 - ε < ‖z‖ ∧ ‖z‖ < 1 + ε} {z : ℂ | ρ < ‖z‖ ∧ ‖z‖ < R} :=
    fun z hz => (hεU hz).2
  have hsub : {z : ℂ | 1 - ε < ‖z‖ ∧ ‖z‖ < 1 + ε} ⊆ {z : ℂ | ρ₀ < ‖z‖ ∧ ‖z‖ < R₀} := fun z hz => (hεU hz).1
  refine ⟨r, hr, 1 - ε, by linarith, 1 + ε, by linarith, fun t z => H t (K z), ?_, ?_⟩
  · have hKd : ContDiffOn ℝ 1 K {z : ℂ | ρ₀ < ‖z‖ ∧ ‖z‖ < R₀} :=
      (hK.contDiffOn (n := 1) hA₀).restrict_scalars ℝ
    have hin : ContDiffOn ℝ 1 (fun q : ℂ × ℂ => (q.1, K q.2))
        (ball 0 r ×ˢ {z : ℂ | 1 - ε < ‖z‖ ∧ ‖z‖ < 1 + ε}) :=
      contDiffOn_fst.prodMk ((hKd.mono hsub).comp contDiffOn_snd fun q hq => hq.2)
    exact hH.comp hin fun q hq => ⟨hq.1, hmaps hq.2⟩
  · intro t ht
    obtain ⟨hHd, hHi, hHc⟩ := hHt t ht
    refine ⟨hHd.comp (hK.mono hsub) hmaps, hHi.comp (hKi.mono hsub) hmaps, fun z hz => ?_⟩
    obtain ⟨u, hu, he⟩ := wAS_maps_circle hκ (show ‖z‖ = 1 from hz)
    have hwk : wA κ z = u := by
      show finPart (wAS κ (z : ExtPlane)) = u
      rw [he]
      rfl
    show H t (K z) = finPart (wAS (beltramiMul (μ t) κ) (z : ExtPlane))
    rw [hKc z hz, hwk, hHc u hu, grp_wAS_mul (hμ t ht) hκ, Function.comp_apply, he]
    rfl

/-- **(d)** Domination from a C¹ family of extensions of `g_{ν_t}` across `𝕊¹`, for a holomorphic line `t ↦ ν_t`. -/
theorem s3g_dom_of_ext {ν : ℂ → LinfStar} {r ρ : ℝ} (hr : 0 < r) (hρ : ρ < 1)
    (hν : ∀ t ∈ ball (0 : ℂ) r, ν t ∈ LinfStarBall) (hνa : ∀ t ∈ ball (0 : ℂ) r, AnalyticAt ℂ ν t)
    {G : ℂ → ℂ → ℂ} (hG : ContDiffOn ℝ 1 (fun q : ℂ × ℂ => G q.1 q.2) (ball 0 r ×ˢ {z | ρ < ‖z‖}))
    (hGt : ∀ t ∈ ball (0 : ℂ) r, DifferentiableOn ℂ (G t) {z | ρ < ‖z‖} ∧ InjOn (G t) {z | ρ < ‖z‖} ∧
      EqOn (G t) (gMu (ν t)) unitDiscExterior) :
    ∃ r' > 0, ∃ D : ℂ → ℝ, MemLp D 2 (volume.restrict unitDiscExterior) ∧ ∀ s ∈ ball (0 : ℂ) r',
      AEStronglyMeasurable (preSchwarzian (gsans (ν s))) (volume.restrict unitDiscExterior) ∧
        ∀ z ∈ unitDiscExterior,
        DifferentiableAt ℝ (fun t : ℂ => preSchwarzian (gsans (ν t)) z) s ∧
        ‖fderiv ℝ (fun t : ℂ => preSchwarzian (gsans (ν t)) z) s‖ ≤ D z ∧
        ‖preSchwarzian (gsans (ν s)) z‖ ≤ D z := by
  have hU : IsOpen {z : ℂ | ρ < ‖z‖} := isOpen_lt continuous_const continuous_norm
  have hWm : IsOpen (ball (0 : ℂ) r ×ˢ {z : ℂ | ρ < ‖z‖}) := isOpen_ball.prod hU
  have hWi : IsOpen (ball (0 : ℂ) r ×ˢ ball (0 : ℂ) 1) := isOpen_ball.prod isOpen_ball
  obtain ⟨hMc, hMrep⟩ := s3g_mid hν hG hGt
  obtain ⟨Ψ, hΨc, hΨrep⟩ := s3g_inf hν hνa
  -- bounds on compact pieces: the collar `1 ≤ |z| ≤ 2` and the chart disc `|u| ≤ 1/2`
  have hKm : IsCompact (closedBall (0 : ℂ) (r / 2) ×ˢ (closedBall (0 : ℂ) 2 ∩ {z : ℂ | 1 ≤ ‖z‖})) :=
    (isCompact_closedBall _ _).prod
      ((isCompact_closedBall _ _).inter_right (isClosed_le continuous_const continuous_norm))
  have hKmsub : closedBall (0 : ℂ) (r / 2) ×ˢ (closedBall (0 : ℂ) 2 ∩ {z : ℂ | 1 ≤ ‖z‖}) ⊆
      ball (0 : ℂ) r ×ˢ {z : ℂ | ρ < ‖z‖} :=
    fun x hx => ⟨closedBall_subset_ball (by linarith) hx.1, lt_of_lt_of_le hρ hx.2.2⟩
  have hKi : IsCompact (closedBall (0 : ℂ) (r / 2) ×ˢ closedBall (0 : ℂ) (1 / 2)) :=
    (isCompact_closedBall _ _).prod (isCompact_closedBall _ _)
  have hKisub : closedBall (0 : ℂ) (r / 2) ×ˢ closedBall (0 : ℂ) (1 / 2) ⊆
      ball (0 : ℂ) r ×ˢ ball (0 : ℂ) 1 :=
    fun x hx => ⟨closedBall_subset_ball (by linarith) hx.1, closedBall_subset_ball (by norm_num) hx.2⟩
  obtain ⟨A0, hA0⟩ := hKm.exists_bound_of_continuousOn (hMc.continuousOn.mono hKmsub)
  obtain ⟨A1, hA1⟩ :=
    hKm.exists_bound_of_continuousOn ((hMc.continuousOn_fderiv_of_isOpen hWm le_rfl).mono hKmsub)
  obtain ⟨B0, hB0⟩ := hKi.exists_bound_of_continuousOn (hΨc.continuousOn.mono hKisub)
  obtain ⟨B1, hB1⟩ :=
    hKi.exists_bound_of_continuousOn ((hΨc.continuousOn_fderiv_of_isOpen hWi le_rfl).mono hKisub)
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = ‖ContinuousLinearMap.inl ℝ ℂ ℂ‖ := ⟨_, rfl⟩
  have hK0 : 0 ≤ K := by rw [hK]; exact norm_nonneg _
  obtain ⟨C, hC⟩ : ∃ C : ℝ, C = (|A0| + |A1| + |B0| + |B1|) * (1 + K) := ⟨_, rfl⟩
  have hCA0 : |A0| ≤ C := by
    rw [hC]; nlinarith [abs_nonneg A0, abs_nonneg A1, abs_nonneg B0, abs_nonneg B1]
  have hCA1 : |A1| * K ≤ C := by
    rw [hC]; nlinarith [abs_nonneg A0, abs_nonneg A1, abs_nonneg B0, abs_nonneg B1]
  have hCB0 : |B0| ≤ C := by
    rw [hC]; nlinarith [abs_nonneg A0, abs_nonneg A1, abs_nonneg B0, abs_nonneg B1]
  have hCB1 : |B1| * K ≤ C := by
    rw [hC]; nlinarith [abs_nonneg A0, abs_nonneg A1, abs_nonneg B0, abs_nonneg B1]
  have hC0 : 0 ≤ C := (abs_nonneg A0).trans hCA0
  -- partial derivatives in `t`
  have hpart : ∀ {Φ : ℂ × ℂ → ℂ} {W : Set (ℂ × ℂ)}, IsOpen W → ContDiffOn ℝ 1 Φ W → ∀ s z : ℂ, (s, z) ∈ W →
      HasFDerivAt (fun t : ℂ => Φ (t, z)) ((fderiv ℝ Φ (s, z)).comp (ContinuousLinearMap.inl ℝ ℂ ℂ)) s := by
    intro Φ W hW hΦ s z hsz
    have hd := ((hΦ.differentiableOn one_ne_zero _ hsz).differentiableAt (hW.mem_nhds hsz)).hasFDerivAt
    exact HasFDerivAt.comp (g := Φ) (f := fun t : ℂ => (t, z)) s hd (hasFDerivAt_prodMk_left s z)
  refine ⟨r / 2, by positivity, fun z => C * (2 / ‖z‖) ^ 3, ?_, fun s hs => ⟨?_, fun z hz => ?_⟩⟩
  · -- the dominating function is in `L²(𝔻*)`
    have hfin : ((Module.finrank ℝ ℂ : ℕ) : ℝ) < 6 := by rw [Complex.finrank_real_complex]; norm_num
    have hgm : AEStronglyMeasurable (fun z : ℂ => (1 + ‖z‖) ^ (-3 : ℝ)) volume :=
      (by fun_prop : Measurable fun z : ℂ => (1 + ‖z‖) ^ (-3 : ℝ)).aestronglyMeasurable
    have hg : MemLp (fun z : ℂ => (1 + ‖z‖) ^ (-3 : ℝ)) 2 volume := by
      rw [memLp_two_iff_integrable_sq hgm]
      refine (integrable_one_add_norm (μ := volume) hfin).congr (Eventually.of_forall fun z => ?_)
      show (1 + ‖z‖) ^ (-6 : ℝ) = ((1 + ‖z‖) ^ (-3 : ℝ)) ^ 2
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
      norm_num
    refine ((hg.restrict unitDiscExterior).const_mul (64 * C)).of_le ?_ ?_
    · exact (by fun_prop : Measurable fun z : ℂ => C * (2 / ‖z‖) ^ 3).aestronglyMeasurable
    · refine (ae_restrict_iff' (isOpen_lt continuous_const continuous_norm).measurableSet).2
        (Eventually.of_forall fun z hz => ?_)
      have hz1 : 1 < ‖z‖ := hz
      have h1 : 2 / ‖z‖ ≤ 4 / (1 + ‖z‖) := by
        rw [div_le_div_iff₀ (by linarith) (by linarith)]
        linarith
      have h2 := pow_le_pow_left₀ (by positivity) h1 3
      have h3 : (4 / (1 + ‖z‖)) ^ 3 = 64 * (1 + ‖z‖) ^ (-3 : ℝ) := by
        rw [show (-3 : ℝ) = -((3 : ℕ) : ℝ) by norm_num, Real.rpow_neg (by positivity), Real.rpow_natCast,
          div_pow]
        norm_num
        ring
      rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity)]
      calc C * (2 / ‖z‖) ^ 3 ≤ C * (4 / (1 + ‖z‖)) ^ 3 := mul_le_mul_of_nonneg_left h2 hC0
        _ = 64 * C * (1 + ‖z‖) ^ (-3 : ℝ) := by rw [h3]; ring
  · -- measurability
    have hsr : s ∈ ball (0 : ℂ) r := ball_subset_ball (by linarith) hs
    have hc : ContinuousOn (fun z => (fun q : ℂ × ℂ => deriv (deriv (G q.1)) q.2 / deriv (G q.1) q.2) (s, z))
        unitDiscExterior :=
      hMc.continuousOn.comp (continuousOn_const.prodMk continuousOn_id) fun z hz => ⟨hsr, hρ.trans hz⟩
    exact (hc.congr fun z hz => hMrep s hsr z hz).aestronglyMeasurable
      (isOpen_lt continuous_const continuous_norm).measurableSet
  · have hz1 : 1 < ‖z‖ := hz
    have hsr : s ∈ ball (0 : ℂ) r := ball_subset_ball (by linarith) hs
    have hsc : s ∈ closedBall (0 : ℂ) (r / 2) := ball_subset_closedBall hs
    have hzp : 0 < ‖z‖ := by linarith
    by_cases hz2 : ‖z‖ ≤ 2
    · -- the collar
      have he : (fun t : ℂ => preSchwarzian (gsans (ν t)) z) =ᶠ[𝓝 s]
          fun t => (fun q : ℂ × ℂ => deriv (deriv (G q.1)) q.2 / deriv (G q.1) q.2) (t, z) := by
        filter_upwards [isOpen_ball.mem_nhds hsr] with t ht
        exact hMrep t ht z hz
      have hD := (hpart hWm hMc s z ⟨hsr, hρ.trans hz1⟩).congr_of_eventuallyEq he
      have hKz : (s, z) ∈ closedBall (0 : ℂ) (r / 2) ×ˢ (closedBall (0 : ℂ) 2 ∩ {z : ℂ | 1 ≤ ‖z‖}) :=
        ⟨hsc, mem_closedBall_zero_iff.2 hz2, hz1.le⟩
      have hpow : 1 ≤ (2 / ‖z‖) ^ 3 := one_le_pow₀ (by rw [le_div_iff₀ hzp]; linarith)
      refine ⟨hD.differentiableAt, ?_, ?_⟩
      · rw [hD.fderiv]
        calc _ ≤ ‖fderiv ℝ (fun q : ℂ × ℂ => deriv (deriv (G q.1)) q.2 / deriv (G q.1) q.2) (s, z)‖ *
              ‖ContinuousLinearMap.inl ℝ ℂ ℂ‖ := ContinuousLinearMap.opNorm_comp_le _ _
          _ ≤ |A1| * K := by
              rw [← hK]
              exact mul_le_mul_of_nonneg_right ((hA1 _ hKz).trans (le_abs_self _)) hK0
          _ ≤ C * (2 / ‖z‖) ^ 3 := hCA1.trans (le_mul_of_one_le_right hC0 hpow)
      · rw [hMrep s hsr z hz]
        exact ((hA0 _ hKz).trans (le_abs_self _)).trans (hCA0.trans (le_mul_of_one_le_right hC0 hpow))
    · -- the chart at `∞`
      push_neg at hz2
      have hu2 : ‖z⁻¹‖ ≤ 1 / 2 := by
        rw [norm_inv, one_div]
        exact inv_anti₀ (by norm_num) hz2.le
      have hu : z⁻¹ ∈ ball (0 : ℂ) 1 := mem_ball_zero_iff.2 (by linarith)
      have he : (fun t : ℂ => preSchwarzian (gsans (ν t)) z) =ᶠ[𝓝 s] fun t => -(z⁻¹) ^ 3 * Ψ (t, z⁻¹) := by
        filter_upwards [isOpen_ball.mem_nhds hsr] with t ht
        exact hΨrep t ht z hz
      have hP := hpart hWi hΨc s z⁻¹ ⟨hsr, hu⟩
      have hD0 : HasFDerivAt (fun t : ℂ => -(z⁻¹) ^ 3 * Ψ (t, z⁻¹))
          ((ContinuousLinearMap.mul ℝ ℂ (-(z⁻¹) ^ 3)).comp
            ((fderiv ℝ Ψ (s, z⁻¹)).comp (ContinuousLinearMap.inl ℝ ℂ ℂ))) s :=
        HasFDerivAt.comp (g := ⇑(ContinuousLinearMap.mul ℝ ℂ (-(z⁻¹) ^ 3))) (f := fun t : ℂ => Ψ (t, z⁻¹)) s
          (ContinuousLinearMap.mul ℝ ℂ (-(z⁻¹) ^ 3)).hasFDerivAt hP
      have hD := hD0.congr_of_eventuallyEq he
      have hKz : (s, z⁻¹) ∈ closedBall (0 : ℂ) (r / 2) ×ˢ closedBall (0 : ℂ) (1 / 2) :=
        ⟨hsc, mem_closedBall_zero_iff.2 hu2⟩
      have hc3 : ‖-(z⁻¹) ^ 3‖ = (‖z‖ ^ 3)⁻¹ := by rw [norm_neg, norm_pow, norm_inv, inv_pow]
      have h8 : C * (2 / ‖z‖) ^ 3 = 8 * C * (‖z‖ ^ 3)⁻¹ := by rw [div_pow]; ring
      have hw : 0 < (‖z‖ ^ 3)⁻¹ := by positivity
      refine ⟨hD.differentiableAt, ?_, ?_⟩
      · rw [hD.fderiv]
        show _ ≤ C * (2 / ‖z‖) ^ 3
        rw [h8]
        calc _ ≤ ‖ContinuousLinearMap.mul ℝ ℂ (-(z⁻¹) ^ 3)‖ *
              ‖(fderiv ℝ Ψ (s, z⁻¹)).comp (ContinuousLinearMap.inl ℝ ℂ ℂ)‖ :=
              ContinuousLinearMap.opNorm_comp_le _ _
          _ ≤ (‖z‖ ^ 3)⁻¹ * (|B1| * K) := by
              refine mul_le_mul ((ContinuousLinearMap.opNorm_mul_apply_le ℝ ℂ _).trans hc3.le) ?_
                (norm_nonneg _) hw.le
              refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
              rw [← hK]
              exact mul_le_mul_of_nonneg_right ((hB1 _ hKz).trans (le_abs_self _)) hK0
          _ ≤ 8 * C * (‖z‖ ^ 3)⁻¹ := by nlinarith
      · show ‖preSchwarzian (gsans (ν s)) z‖ ≤ C * (2 / ‖z‖) ^ 3
        rw [hΨrep s hsr z hz, h8, norm_mul, hc3]
        have hb := (hB0 _ hKz).trans (le_abs_self _)
        nlinarith

/-- **(e) Export (D-points).** Along the line `ν_t = (a + t m) * κ` on a `D`-base, `f_{ν_t}`, `g_{ν_t}` and the welding
`h_{ν_t}` extend holomorphically and injectively across `𝕊¹` (to `|z| < R`, `|z| > ρ`, and the annulus), as C¹ families
in `(t, z)` together with their first two `z`-derivatives; `G_t ∘ H_t = F_t` and `|H_t| = 1` on `𝕊¹`. -/
theorem s3g_D_ext {κ : LinfStarBall} (hκ : Phi κ ∈ T01)
    (hκD : ∃ L : List (A2 unitDisc), (∀ φ ∈ L, (∃ q : Polynomial ℂ, ∀ z ∈ unitDisc, A2.toFun φ z = q.eval z) ∧
      ‖φ‖ < min (Real.sqrt (π / 3)) (2 * delta0 / Real.sqrt (12 / π))) ∧
      (κ : LinfStar) = L.foldr (fun φ acc => beltramiMul (Lambda (A2toAInf φ)) acc) 0)
    {a : LinfStar} (ha : a ∈ harmonicBeltrami) (has : ‖a‖ < delta0) (haL : normL2 unitDiscExterior a < ∞)
    (haD : ∃ ψ : A2 unitDisc, (∃ q : Polynomial ℂ, ∀ z ∈ unitDisc, A2.toFun ψ z = q.eval z) ∧ a = Lambda (A2toAInf ψ))
    {m : ℂ → ℂ} (hm : m ∈ harmonicL2 unitDiscExterior)
    (hmD : ∃ ψ : A2 unitDisc, (∃ q : Polynomial ℂ, ∀ z ∈ unitDisc, A2.toFun ψ z = q.eval z) ∧
      toLinf m = Lambda (A2toAInf ψ)) :
    ∃ r > 0, ∃ ρ < 1, ∃ R > 1, ∃ F G H : ℂ → ℂ → ℂ,
      ContDiffOn ℝ 1 (fun q : ℂ × ℂ => F q.1 q.2) (ball 0 r ×ˢ ball 0 R) ∧
      ContDiffOn ℝ 1 (fun q : ℂ × ℂ => deriv (F q.1) q.2) (ball 0 r ×ˢ ball 0 R) ∧
      ContDiffOn ℝ 1 (fun q : ℂ × ℂ => deriv (deriv (F q.1)) q.2) (ball 0 r ×ˢ ball 0 R) ∧
      ContDiffOn ℝ 1 (fun q : ℂ × ℂ => G q.1 q.2) (ball 0 r ×ˢ {z | ρ < ‖z‖}) ∧
      ContDiffOn ℝ 1 (fun q : ℂ × ℂ => deriv (G q.1) q.2) (ball 0 r ×ˢ {z | ρ < ‖z‖}) ∧
      ContDiffOn ℝ 1 (fun q : ℂ × ℂ => deriv (deriv (G q.1)) q.2) (ball 0 r ×ˢ {z | ρ < ‖z‖}) ∧
      ContDiffOn ℝ 1 (fun q : ℂ × ℂ => H q.1 q.2) (ball 0 r ×ˢ {z | ρ < ‖z‖ ∧ ‖z‖ < R}) ∧
      ∀ t ∈ ball (0 : ℂ) r,
        (DifferentiableOn ℂ (F t) (ball 0 R) ∧ InjOn (F t) (ball 0 R) ∧
          (∀ z ∈ ball (0 : ℂ) R, deriv (F t) z ≠ 0) ∧
          EqOn (F t) (fsans (beltramiMul (a + t • toLinf m) κ)) unitDisc) ∧
        (DifferentiableOn ℂ (G t) {z | ρ < ‖z‖} ∧ InjOn (G t) {z | ρ < ‖z‖} ∧
          (∀ z : ℂ, ρ < ‖z‖ → deriv (G t) z ≠ 0) ∧
          EqOn (G t) (gsans (beltramiMul (a + t • toLinf m) κ)) unitDiscExterior) ∧
        (DifferentiableOn ℂ (H t) {z | ρ < ‖z‖ ∧ ‖z‖ < R} ∧ InjOn (H t) {z | ρ < ‖z‖ ∧ ‖z‖ < R} ∧
          ∀ z ∈ unitCircle, H t z = wA (beltramiMul (a + t • toLinf m) κ) z ∧ ‖H t z‖ = 1 ∧
            G t (H t z) = F t z) := by
  -- hypotheses not needed for the extension (kept for the shape of `s3d_g_dom`)
  have _h1 := hκ
  have _h2 := ha
  have _h4 := haL
  have _h5 := hm
  have hκb : (κ : LinfStar) ∈ LinfStarBall := κ.2
  have hD1 : ∀ z ∈ unitDisc, ‖z‖ ≠ 1 := fun z hz => (mem_ball_zero_iff.mp hz).ne
  have h0poly : ∃ q : Polynomial ℂ, ∀ z ∈ unitDisc, A2.toFun (0 : A2 unitDisc) z = q.eval z := by
    refine ⟨0, fun z hz => ?_⟩
    have h := A2.toFun_smul isOpen_ball hD1 (0 : ℂ) (0 : A2 unitDisc) hz
    have h0 : A2.toFun ((0 : ℂ) • (0 : A2 unitDisc)) = A2.toFun (0 : A2 unitDisc) := by
      congr 1
      exact smul_zero _
    have h' : A2.toFun (0 : A2 unitDisc) z = ((0 : ℂ) • A2.toFun (0 : A2 unitDisc)) z := (congrFun h0 z).symm.trans h
    simpa using h'
  -- the welding extension of a constant chart factor `Λ φ`
  have hconst : ∀ φ : A2 unitDisc, (∃ q : Polynomial ℂ, ∀ z ∈ unitDisc, A2.toFun φ z = q.eval z) →
      ‖A2toAInf φ‖ < 2 → Lambda (A2toAInf φ) ∈ LinfStarBall ∧ ∃ ρ₀ < 1, ∃ R₀ > 1, ∃ K : ℂ → ℂ,
        DifferentiableOn ℂ K {z | ρ₀ < ‖z‖ ∧ ‖z‖ < R₀} ∧ InjOn K {z | ρ₀ < ‖z‖ ∧ ‖z‖ < R₀} ∧
        ∀ z ∈ unitCircle, K z = wA (Lambda (A2toAInf φ)) z := by
    intro φ hφp hφn
    obtain ⟨r1, hr1, R1, hR1, F1, hF1, hF1t⟩ := s3g_aw_extend hφp h0poly hφn
    have hsimp : ∀ t : ℂ, φ + t • (0 : A2 unitDisc) = φ := fun t => by rw [smul_zero, add_zero]
    have hμ : Lambda (A2toAInf φ) ∈ LinfStarBall := by
      have := (hF1t 0 (mem_ball_self hr1)).1
      rwa [hsimp] at this
    obtain ⟨r2, hr2, ρ2, hρ2, R2, hR2, G2, H2, -, -, hGH⟩ :=
      s3g_weld_of_ext (ν := fun _ => Lambda (A2toAInf φ)) hr1 hR1 (fun _ _ => hμ) (fun _ _ => analyticAt_const)
        hF1 (fun t ht => by
          obtain ⟨-, h1, h2, h3⟩ := hF1t t ht
          rw [hsimp] at h3
          exact ⟨h1, h2, h3⟩)
    obtain ⟨-, hH1, hH2, hH3⟩ := hGH 0 (mem_ball_self hr2)
    exact ⟨hμ, ρ2, hρ2, R2, hR2, H2 0, hH1, hH2, hH3⟩
  -- the `D`-chain: induction along the list
  have hind : ∀ L' : List (A2 unitDisc), (∀ φ ∈ L', (∃ q : Polynomial ℂ, ∀ z ∈ unitDisc, A2.toFun φ z = q.eval z) ∧
      ‖A2toAInf φ‖ < 2) →
      L'.foldr (fun φ acc => beltramiMul (Lambda (A2toAInf φ)) acc) 0 ∈ LinfStarBall ∧
      ∃ ρ₀ < 1, ∃ R₀ > 1, ∃ K : ℂ → ℂ, DifferentiableOn ℂ K {z | ρ₀ < ‖z‖ ∧ ‖z‖ < R₀} ∧
        InjOn K {z | ρ₀ < ‖z‖ ∧ ‖z‖ < R₀} ∧
        ∀ z ∈ unitCircle, K z = wA (L'.foldr (fun φ acc => beltramiMul (Lambda (A2toAInf φ)) acc) 0) z := by
    intro L'
    induction L' with
    | nil =>
      intro _
      refine ⟨by simp [LinfStarBall], 0, zero_lt_one, 2, one_lt_two, id, differentiableOn_id, injOn_id _,
        fun z _ => ?_⟩
      simp only [List.foldr_nil, wp_wA_zero, id]
    | cons φ L ih =>
      intro hL'
      obtain ⟨hacc, ρ₀, hρ₀, R₀, hR₀, K, hKd, hKi, hKc⟩ := ih (fun ψ hψ => hL' ψ (List.mem_cons_of_mem φ hψ))
      obtain ⟨hφp, hφn⟩ := hL' φ (by simp)
      obtain ⟨hμ, ρ1, hρ1, R1, hR1, K1, hK1d, hK1i, hK1c⟩ := hconst φ hφp hφn
      have hO1 : IsOpen {z : ℂ | ρ1 < ‖z‖ ∧ ‖z‖ < R1} :=
        (isOpen_lt continuous_const continuous_norm).inter (isOpen_lt continuous_norm continuous_const)
      have hK1C : ContDiffOn ℝ 1 (fun q : ℂ × ℂ => (fun _ : ℂ => K1) q.1 q.2) (ball 0 1 ×ˢ {z | ρ1 < ‖z‖ ∧ ‖z‖ < R1}) := by
        have h := ((hK1d.contDiffOn hO1 (n := 1)).restrict_scalars ℝ).comp contDiffOn_snd
          (fun q (hq : q ∈ ball (0 : ℂ) 1 ×ˢ {z : ℂ | ρ1 < ‖z‖ ∧ ‖z‖ < R1}) => hq.2)
        exact h
      obtain ⟨r', hr', ρ', hρ', R', hR', H', -, hH'⟩ :=
        s3g_weld_mul (μ := fun _ => Lambda (A2toAInf φ)) hacc one_pos hρ1 hR1 hρ₀ hR₀ (fun _ _ => hμ) hK1C
          (fun _ _ => ⟨hK1d, hK1i, hK1c⟩) hKd hKi hKc
      obtain ⟨hH'1, hH'2, hH'3⟩ := hH' 0 (mem_ball_self hr')
      simp only [List.foldr_cons]
      exact ⟨bg_mul_mem_ball hacc hμ, ρ', hρ', R', hR', H' 0, hH'1, hH'2, hH'3⟩
  -- norms of the chart data
  have hpi : (0 : ℝ) < π := Real.pi_pos
  have hn2 : ∀ φ : A2 unitDisc, ‖φ‖ < min (Real.sqrt (π / 3)) (2 * delta0 / Real.sqrt (12 / π)) →
      ‖A2toAInf φ‖ < 2 := by
    intro φ hφ
    have h1 := (A2toAInf_bounded.2 φ).1
    have hφ' : ‖φ‖ < Real.sqrt (π / 3) := lt_of_lt_of_le hφ (min_le_left _ _)
    have hs : 0 < Real.sqrt (12 / π) := Real.sqrt_pos.mpr (by positivity)
    have h2 : Real.sqrt (12 / π) * Real.sqrt (π / 3) = 2 := by
      rw [← Real.sqrt_mul (by positivity), show 12 / π * (π / 3) = (2 : ℝ) ^ 2 by field_simp; ring,
        Real.sqrt_sq (by norm_num)]
    calc ‖A2toAInf φ‖ ≤ Real.sqrt (12 / π) * ‖φ‖ := h1
      _ < Real.sqrt (12 / π) * Real.sqrt (π / 3) := mul_lt_mul_of_pos_left hφ' hs
      _ = 2 := h2
  obtain ⟨L, hL, hκL⟩ := hκD
  obtain ⟨-, ρκ, hρκ, Rκ, hRκ, Kκ, hKκd, hKκi, hKκc⟩ :=
    hind L (fun φ hφ => ⟨(hL φ hφ).1, hn2 φ (hL φ hφ).2⟩)
  rw [← hκL] at hKκc
  -- the line factor `a + t m = Λ(ψ_a + t ψ_m)`
  obtain ⟨ψa, hψap, haeq⟩ := haD
  obtain ⟨ψm, hψmp, hmeq⟩ := hmD
  have hlin : ∀ t : ℂ, A2toAInf (ψa + t • ψm) = A2toAInf ψa + t • A2toAInf ψm := by
    intro t
    rw [add_comm ψa, A2toAInf_bounded.1 t ψm ψa, add_comm]
  have hν0eq : ∀ t : ℂ, Lambda (A2toAInf (ψa + t • ψm)) = a + t • toLinf m := by
    intro t
    rw [hlin, Lambda_add, Lambda_smul, ← haeq, ← hmeq]
  have hsa : ‖A2toAInf ψa‖ < 2 := by
    have h := Lambda_norm_eq (A2toAInf ψa)
    rw [← haeq] at h
    have := delta0_bounds.2
    linarith
  obtain ⟨r1, hr1, R1, hR1, F1, hF1, hF1t⟩ := s3g_aw_extend hψap hψmp hsa
  have hν0b : ∀ t ∈ ball (0 : ℂ) r1, a + t • toLinf m ∈ LinfStarBall := fun t ht => by
    rw [← hν0eq]
    exact (hF1t t ht).1
  have hν0a : ∀ t, AnalyticAt ℝ (fun t : ℂ => Lambda (A2toAInf (ψa + t • ψm))) t := by
    have he : (fun t : ℂ => Lambda (A2toAInf (ψa + t • ψm))) = fun t => a + t • toLinf m := funext hν0eq
    intro t
    rw [he]
    exact analyticAt_const.add (analyticAt_id.smul analyticAt_const)
  obtain ⟨r2, hr2, ρ2, hρ2, R2, hR2, G2, H2, -, hH2C, hGH2⟩ :=
    s3g_weld_of_ext (ν := fun t : ℂ => Lambda (A2toAInf (ψa + t • ψm))) hr1 hR1 (fun t ht => (hF1t t ht).1)
      (fun t _ => hν0a t) hF1 (fun t ht => (hF1t t ht).2)
  -- compose with the base `κ`
  obtain ⟨s2, hs2⟩ : ∃ s : ℝ, s = min r1 r2 := ⟨_, rfl⟩
  have hs20 : 0 < s2 := by rw [hs2]; exact lt_min hr1 hr2
  have hs21 : ball (0 : ℂ) s2 ⊆ ball 0 r1 := ball_subset_ball (by rw [hs2]; exact min_le_left _ _)
  have hs22 : ball (0 : ℂ) s2 ⊆ ball 0 r2 := ball_subset_ball (by rw [hs2]; exact min_le_right _ _)
  obtain ⟨r3, hr3, ρ3, hρ3, R3, hR3, H3, hH3C, hH3t⟩ :=
    s3g_weld_mul (μ := fun t : ℂ => Lambda (A2toAInf (ψa + t • ψm))) hκb hs20 hρ2 hR2 hρκ hRκ
      (fun t ht => (hF1t t (hs21 ht)).1) (hH2C.mono (prod_mono hs22 subset_rfl))
      (fun t ht => (hGH2 t (hs22 ht)).2) hKκd hKκi hKκc
  obtain ⟨ν, hν⟩ : ∃ ν : ℂ → LinfStar, ν = fun t => beltramiMul (a + t • toLinf m) (κ : LinfStar) := ⟨_, rfl⟩
  have hνap : ∀ t, ν t = beltramiMul (a + t • toLinf m) (κ : LinfStar) := fun t => by rw [hν]
  obtain ⟨s3, hs3⟩ : ∃ s : ℝ, s = min s2 r3 := ⟨_, rfl⟩
  have hs30 : 0 < s3 := by rw [hs3]; exact lt_min hs20 hr3
  have hs31 : ball (0 : ℂ) s3 ⊆ ball 0 s2 := ball_subset_ball (by rw [hs3]; exact min_le_left _ _)
  have hs32 : ball (0 : ℂ) s3 ⊆ ball 0 r3 := ball_subset_ball (by rw [hs3]; exact min_le_right _ _)
  have hνb : ∀ t ∈ ball (0 : ℂ) r1, ν t ∈ LinfStarBall := fun t ht => by
    rw [hνap]
    exact bg_mul_mem_ball hκb (hν0b t ht)
  -- `ν` is holomorphic on `|t| < r₁`
  have hνC : ∀ t ∈ ball (0 : ℂ) r1, AnalyticAt ℂ ν t := by
    obtain ⟨U, hU⟩ : ∃ U : Set ℂ, U = (fun t : ℂ => a + t • toLinf m) ⁻¹' LinfStarBall := ⟨_, rfl⟩
    have hUo : IsOpen U := by
      rw [hU]
      exact isOpen_ball.preimage (continuous_const.add (continuous_id.smul continuous_const))
    have hdU : DifferentiableOn ℂ ν U := by
      intro t ht
      rw [hU] at ht
      have h1 : DifferentiableAt ℂ (fun l => beltramiMul l (κ : LinfStar)) (a + t • toLinf m) :=
        (bd_differentiableOn hκb).differentiableAt (isOpen_ball.mem_nhds ht)
      have h2 : DifferentiableAt ℂ (fun t : ℂ => a + t • toLinf m) t :=
        (differentiableAt_const _).add (differentiableAt_id.smul_const _)
      rw [hν]
      exact (DifferentiableAt.comp (g := fun l => beltramiMul l (κ : LinfStar))
        (f := fun t : ℂ => a + t • toLinf m) t h1 h2).differentiableWithinAt
    intro t ht
    have htU : t ∈ U := by rw [hU]; exact hν0b t ht
    exact hdU.analyticAt (hUo.mem_nhds htU)
  have hνa : ∀ t ∈ ball (0 : ℂ) r1, AnalyticAt ℝ ν t := fun t ht => (hνC t ht).restrictScalars
  -- (b′): an extension of `f_{ν_t}`
  obtain ⟨r4, hr4, R4, hR4, F4, hF4C, hF4t⟩ :=
    s3g_ext_of_weld (ν := ν) (H := H3) hs30 hρ3 hR3 (fun t ht => hνb t (hs21 (hs31 ht)))
      (fun t ht => hνa t (hs21 (hs31 ht))) (hH3C.mono (prod_mono hs32 subset_rfl)) (fun t ht => by
        obtain ⟨h1, h2, h3⟩ := hH3t t (hs32 ht)
        refine ⟨h1, h2, fun z hz => ?_⟩
        rw [h3 z hz, hνap, hν0eq])
  obtain ⟨s4, hs4⟩ : ∃ s : ℝ, s = min s3 r4 := ⟨_, rfl⟩
  have hs40 : 0 < s4 := by rw [hs4]; exact lt_min hs30 hr4
  have hs41 : ball (0 : ℂ) s4 ⊆ ball 0 s3 := ball_subset_ball (by rw [hs4]; exact min_le_left _ _)
  have hs42 : ball (0 : ℂ) s4 ⊆ ball 0 r4 := ball_subset_ball (by rw [hs4]; exact min_le_right _ _)
  have hin4 : ∀ t ∈ ball (0 : ℂ) s4, t ∈ ball (0 : ℂ) r1 := fun t ht => hs21 (hs31 (hs41 ht))
  -- (b): extensions of `g_{ν_t}` and of the welding
  obtain ⟨r5, hr5, ρ5, hρ5, R5, hR5, G5, H5, hG5C, hH5C, hGH5⟩ :=
    s3g_weld_of_ext (ν := ν) (F := F4) hs40 hR4 (fun t ht => hνb t (hin4 t ht)) (fun t ht => hνa t (hin4 t ht))
      (hF4C.mono (prod_mono hs42 subset_rfl)) (fun t ht => hF4t t (hs42 ht))
  obtain ⟨s5, hs5⟩ : ∃ s : ℝ, s = min s4 r5 := ⟨_, rfl⟩
  have hs50 : 0 < s5 := by rw [hs5]; exact lt_min hs40 hr5
  have hs51 : ball (0 : ℂ) s5 ⊆ ball 0 s4 := ball_subset_ball (by rw [hs5]; exact min_le_left _ _)
  have hs52 : ball (0 : ℂ) s5 ⊆ ball 0 r5 := ball_subset_ball (by rw [hs5]; exact min_le_right _ _)
  obtain ⟨R, hR⟩ : ∃ R : ℝ, R = min R4 R5 := ⟨_, rfl⟩
  have hR1' : 1 < R := by rw [hR]; exact lt_min hR4 hR5
  have hRR4 : ball (0 : ℂ) R ⊆ ball 0 R4 := ball_subset_ball (by rw [hR]; exact min_le_left _ _)
  have hRR5 : R ≤ R5 := by rw [hR]; exact min_le_right _ _
  have hsubH : {z : ℂ | ρ5 < ‖z‖ ∧ ‖z‖ < R} ⊆ {z : ℂ | ρ5 < ‖z‖ ∧ ‖z‖ < R5} := fun z hz =>
    ⟨hz.1, lt_of_lt_of_le hz.2 hRR5⟩
  -- the C¹ families of derivatives
  have hP : IsOpen (ball (0 : ℂ) s5) := isOpen_ball
  have hGo : IsOpen {z : ℂ | ρ5 < ‖z‖} := isOpen_lt continuous_const continuous_norm
  have hF4C' : ContDiffOn ℝ 1 (fun q : ℂ × ℂ => F4 q.1 q.2) (ball (0 : ℂ) s5 ×ˢ ball 0 R) :=
    hF4C.mono (prod_mono (fun t ht => hs42 (hs51 ht)) hRR4)
  have hF4d : ∀ t ∈ ball (0 : ℂ) s5, DifferentiableOn ℂ (F4 t) (ball 0 R) := fun t ht =>
    (hF4t t (hs42 (hs51 ht))).1.mono hRR4
  have hG5C' : ContDiffOn ℝ 1 (fun q : ℂ × ℂ => G5 q.1 q.2) (ball (0 : ℂ) s5 ×ˢ {z : ℂ | ρ5 < ‖z‖}) :=
    hG5C.mono (prod_mono hs52 subset_rfl)
  have hG5d : ∀ t ∈ ball (0 : ℂ) s5, DifferentiableOn ℂ (G5 t) {z : ℂ | ρ5 < ‖z‖} := fun t ht =>
    (hGH5 t (hs52 ht)).1.1
  obtain ⟨hF1C, hF1d⟩ := s3g_param_deriv hP isOpen_ball hF4C' hF4d
  obtain ⟨hF2C, -⟩ := s3g_param_deriv (F := fun t z => deriv (F4 t) z) hP isOpen_ball hF1C hF1d
  obtain ⟨hG1C, hG1d⟩ := s3g_param_deriv hP hGo hG5C' hG5d
  obtain ⟨hG2C, -⟩ := s3g_param_deriv (F := fun t z => deriv (G5 t) z) hP hGo hG1C hG1d
  refine ⟨s5, hs50, ρ5, hρ5, R, hR1', F4, G5, H5, hF4C', hF1C, hF2C, hG5C', hG1C, hG2C,
    hH5C.mono (prod_mono hs52 hsubH), fun t ht => ?_⟩
  have ht4 : t ∈ ball (0 : ℂ) r4 := hs42 (hs51 ht)
  have ht5 : t ∈ ball (0 : ℂ) r5 := hs52 ht
  have hμt : ν t ∈ LinfStarBall := hνb t (hin4 t (hs51 ht))
  obtain ⟨hFd, hFi, hFe⟩ := hF4t t ht4
  obtain ⟨⟨hGd, hGi, hGe⟩, ⟨hHd, hHi, hHc⟩⟩ := hGH5 t ht5
  have hνt : ν t = beltramiMul (a + t • toLinf m) (κ : LinfStar) := hνap t
  have hfs : fsans (ν t) = fB (ν t) := by
    funext z
    simp [fsans, lambdaW, AppB.b8_weldConst_zero hμt]
  refine ⟨⟨hFd.mono hRR4, hFi.mono hRR4, fun z hz => deriv_ne_zero_of_injOn isOpen_ball (hFd.mono hRR4)
      (hFi.mono hRR4) hz, ?_⟩, ⟨hGd, hGi, fun z hz => deriv_ne_zero_of_injOn hGo hGd hGi hz, ?_⟩,
    ⟨hHd.mono hsubH, hHi.mono hsubH,
      fun z hz => ?_⟩⟩
  · rw [← hνt, hfs]
    exact hFe
  · rw [← hνt]
    intro z hz
    rw [hGe hz, s3g_gsans_eq hμt]
  · have hz1 : ‖z‖ = 1 := hz
    refine ⟨by rw [← hνt]; exact hHc z hz, ?_, ?_⟩
    · rw [hHc z hz]
      obtain ⟨u, hu, he⟩ := wAS_maps_circle hμt hz1
      show ‖finPart (wAS (ν t) (z : ExtPlane))‖ = 1
      rw [he]
      exact hu
    · rw [hHc z hz]
      exact s3g_weld_circle hμt hρ5 hR4 (hFd.continuousOn) hFe hGd.continuousOn hGe hz1

/-- **`s3d_g_dom`** (master S3Density_IFACE, md5 29319fbc), proved by analytic welding: `(e)` gives the C¹ family
of extensions `G_t` of `𝗀_{ν_t}` across `𝕊¹`, and `(d)` the `L²(𝔻*)` domination. -/
theorem s3d_g_dom_proof {κ : LinfStarBall} (hκ : Phi κ ∈ T01)
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
  have _h1 := ha
  obtain ⟨r, hr, ρ, hρ, R, hR, F, G, H, -, -, -, hGC, -, -, -, hEt⟩ :=
    s3g_D_ext hκ hκD ha has haL haD hm hmD
  have hκb : (κ : LinfStar) ∈ LinfStarBall := κ.2
  -- `a + t m` stays in the unit ball for `|t| < r₀`
  have has1 : ‖a‖ < 1 := lt_trans has delta0_bounds.2
  obtain ⟨r0, hr0⟩ : ∃ r0 : ℝ, r0 = (1 - ‖a‖) / (‖toLinf m‖ + 1) := ⟨_, rfl⟩
  have hr00 : 0 < r0 := by rw [hr0]; exact div_pos (by linarith) (by positivity)
  have hball : ∀ t ∈ ball (0 : ℂ) r0, a + t • toLinf m ∈ LinfStarBall := by
    intro t ht
    rw [mem_ball_zero_iff, hr0, lt_div_iff₀ (by positivity)] at ht
    show a + t • toLinf m ∈ ball (0 : LinfStar) 1
    rw [mem_ball_zero_iff]
    calc ‖a + t • toLinf m‖ ≤ ‖a‖ + ‖t‖ * ‖toLinf m‖ := by
          refine (norm_add_le _ _).trans ?_
          rw [norm_smul]
      _ < 1 := by nlinarith [norm_nonneg t, norm_nonneg (toLinf m)]
  obtain ⟨r1, hr1⟩ : ∃ r1 : ℝ, r1 = min r r0 := ⟨_, rfl⟩
  have hr10 : 0 < r1 := by rw [hr1]; exact lt_min hr hr00
  have hr1r : ball (0 : ℂ) r1 ⊆ ball 0 r := ball_subset_ball (by rw [hr1]; exact min_le_left _ _)
  have hr10' : ball (0 : ℂ) r1 ⊆ ball 0 r0 := ball_subset_ball (by rw [hr1]; exact min_le_right _ _)
  have hν : ∀ t ∈ ball (0 : ℂ) r1, beltramiMul (a + t • toLinf m) (κ : LinfStar) ∈ LinfStarBall := fun t ht =>
    bg_mul_mem_ball hκb (hball t (hr10' ht))
  have hνa : ∀ t ∈ ball (0 : ℂ) r1, AnalyticAt ℂ (fun t : ℂ => beltramiMul (a + t • toLinf m) (κ : LinfStar)) t := by
    obtain ⟨U, hU⟩ : ∃ U : Set ℂ, U = (fun t : ℂ => a + t • toLinf m) ⁻¹' LinfStarBall := ⟨_, rfl⟩
    have hUo : IsOpen U := by
      rw [hU]
      exact isOpen_ball.preimage (continuous_const.add (continuous_id.smul continuous_const))
    have hdU : DifferentiableOn ℂ (fun t : ℂ => beltramiMul (a + t • toLinf m) (κ : LinfStar)) U := by
      intro t ht
      rw [hU] at ht
      have h1 : DifferentiableAt ℂ (fun l => beltramiMul l (κ : LinfStar)) (a + t • toLinf m) :=
        (bd_differentiableOn hκb).differentiableAt (isOpen_ball.mem_nhds ht)
      have h2 : DifferentiableAt ℂ (fun t : ℂ => a + t • toLinf m) t :=
        (differentiableAt_const _).add (differentiableAt_id.smul_const _)
      exact (DifferentiableAt.comp (g := fun l => beltramiMul l (κ : LinfStar))
        (f := fun t : ℂ => a + t • toLinf m) t h1 h2).differentiableWithinAt
    intro t ht
    have htU : t ∈ U := by rw [hU]; exact hball t (hr10' ht)
    exact hdU.analyticAt (hUo.mem_nhds htU)
  exact s3g_dom_of_ext (ν := fun t : ℂ => beltramiMul (a + t • toLinf m) (κ : LinfStar)) hr10 hρ hν hνa
    (hGC.mono (prod_mono hr1r subset_rfl)) (fun t ht => by
      obtain ⟨-, ⟨hGd, hGi, -, hGe⟩, -⟩ := hEt t (hr1r ht)
      refine ⟨hGd, hGi, fun z hz => ?_⟩
      rw [hGe hz, s3g_gsans_eq (hν t ht)])


end TakhtajanTeo.Ch2
