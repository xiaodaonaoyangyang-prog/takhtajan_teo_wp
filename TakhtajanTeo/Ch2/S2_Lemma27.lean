import TakhtajanTeo.Ch2.S2_Grunsky
import TakhtajanTeo.Ch1.Lemma29Plane
import TakhtajanTeo.Ch1.S1_1_Completed
import TakhtajanTeo.Ch1.QCVariationSchwarzianBasePoint
import TakhtajanTeo.Appendix.B1Entries

/-!
# Ch2 §2: Lemma 2.7 along general paths (`l27_` copy)

`lemma_2_7` is proved here as `l27_lemma_2_7`, with the statement byte-identical; `l27_general` is the general-path form
used by the `thm_2_6` assembly. The other `l27_` lemmas are helpers.
Route (TT:4078–4110), in source coordinates `a, b ∈ 𝔻`:
* `kerK1 (fsans v) a b = kerK1 W_v a b` (Möbius invariance, `b1_kerK1_fB_eq`), `W_v = qcv_planeSolution v`.
* L1: `v ↦ kerK1 (fsans v) a b` is holomorphic on `L∞(𝔻*)₁` (Gateaux along complex lines via
  `qcv_param_hasDerivAt_iter 1` + Koebe bounds, then `qcv_gateaux_to_frechet`).
* L2: its derivative along `κ + tν` is `(1/π²) W'(a) W'(b) ∬_{𝔻*} ν (∂W)² / ((W - W a)²(W - W b)²)`
  (base variation of `W_{κ+tν} ∘ W_κ⁻¹`, kernel identity
  `kerD1 y₁ + kerD1 y₂ - 2(ahKer y₁ - ahKer y₂)/(y₁ - y₂) = (y₁ - y₂)²/((u - y₁)²(u - y₂)²)`,
  `qcv_base_dot_kernel_source`).
* L3: transport to `Ω_κ* = 𝗀_κ(𝔻*)` (as `s2c_main`/`s2c_eq_2_1`, product kernel instead of the fourth power;
  direction `ν = D₀R_κ(Rnm ν κ)` by `qcv_rightDerivative_Rnm`).
* L4: general real `C¹`-free path `γ` (only `HasDerivAt γ γ' s₀`), chain rule; `eq_1_5` names the tangent.
* L5: `lemma_2_7` with `γ s = (s + t) μ`.
* L6: continuity of the derivative of L1 on the ball (Cauchy estimates on complex lines).
-/

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal ComplexConjugate Classical Real
noncomputable section
namespace TakhtajanTeo
open LiZhongQC
namespace Ch2
open QCV

/-- Integrability of a bounded coefficient vanishing on an open set against `ahKer y` and `kerD1 y`, `y` in that set. -/
theorem l27_int_kernels {κ : ℂ → ℂ} {k : ℝ} {U : Set ℂ} (hk : 0 ≤ k) (hκ : IsBeltramiCoeff κ univ k)
    (hU : IsOpen U) (hzero : ∀ u ∈ U, κ u = 0) {y : ℂ} (hy : y ∈ U) :
    Integrable (fun u => κ u * ahKer y u) ∧ Integrable (fun u => κ u * kerD1 y u) := by
  have hκm : AEStronglyMeasurable κ volume := by simpa using hκ.1
  have hκb : ∀ᵐ u : ℂ, ‖κ u‖ ≤ k := by simpa using hκ.2
  refine ⟨(ah_ker_integrable y).bdd_mul hκm hκb, ?_⟩
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hU y hy
  have hr : 0 < ε / 8 := by positivity
  obtain ⟨C, hC, hmaj⟩ := qcv_kernel_ball_majorant (y := y) hr
  have hgood : ∀ᵐ u : ℂ, u ≠ 0 ∧ u ≠ 1 ∧ u ≠ I := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp (show volume ({0} : Set ℂ) = 0 by simp),
      measure_eq_zero_iff_ae_notMem.mp (show volume ({1} : Set ℂ) = 0 by simp),
      measure_eq_zero_iff_ae_notMem.mp (show volume ({I} : Set ℂ) = 0 by simp)] with u h0 h1 hI
    exact ⟨h0, h1, hI⟩
  have hdom : Integrable (fun u => k * (C * ‖ahKer I u‖)) :=
    ((ah_ker_integrable I).norm.const_mul C).const_mul k
  have hm1 : Measurable (kerD1 y) := by unfold kerD1; fun_prop
  apply hdom.mono' (hκm.mul hm1.aestronglyMeasurable)
  filter_upwards [hκb, hgood] with u hκu hu
  show ‖κ u * kerD1 y u‖ ≤ k * (C * ‖ahKer I u‖)
  by_cases h0 : κ u = 0
  · simp only [h0, zero_mul, norm_zero]
    positivity
  · have hfar : 8 * (ε / 8) ≤ ‖u - y‖ := by
      by_contra h
      exact h0 (hzero u (hball (by
        rw [mem_ball, dist_eq_norm]
        linarith [lt_of_not_ge h])))
    have hB := (hmaj u hu.1 hu.2.1 hu.2.2 hfar y (mem_ball_self hr)).2.1
    rw [norm_mul]
    exact mul_le_mul hκu hB (norm_nonneg _) hk

/-- The pointwise kernel identity behind (2.6): the affine parts of `ahKer` cancel. -/
theorem l27_kernel_identity {y₁ y₂ u : ℂ} (h12 : y₁ ≠ y₂) (h0 : u ≠ 0) (h1 : u ≠ 1) (hu1 : u ≠ y₁)
    (hu2 : u ≠ y₂) :
    kerD1 y₁ u + kerD1 y₂ u - 2 / (y₁ - y₂) * (ahKer y₁ u - ahKer y₂ u) =
      (y₁ - y₂) ^ 2 / ((u - y₁) ^ 2 * (u - y₂) ^ 2) := by
  have hd : y₁ - y₂ ≠ 0 := sub_ne_zero.2 h12
  have e1 : u - 1 ≠ 0 := sub_ne_zero.2 h1
  have a1 : u - y₁ ≠ 0 := sub_ne_zero.2 hu1
  have a2 : u - y₂ ≠ 0 := sub_ne_zero.2 hu2
  unfold kerD1 ahKer
  field_simp
  ring

/-- The `t`-derivative of the space derivative of the moving transition, at every base point. -/
theorem l27_transition_deriv {μ : LinfStar} (hμ : μ ∈ LinfStarBall) (ν : LinfStar) {y : ℂ}
    (hy : y ∈ qcv_planeDisk μ) :
    HasDerivAt (fun t : ℂ => deriv (qcv_planeTransition (μ + t • ν) μ) y)
      (deriv (ahVar (ahT_dot (extB ν) (extB μ) (qcv_planeSolution μ))) y) 0 := by
  let z := Function.invFun (qcv_planeSolution μ) y
  have hz : z ∈ unitDisc := qcv_planeSolution_inv_mem hμ hy
  have hz1 : ‖z‖ < 1 := mem_ball_zero_iff.mp hz
  let ρ : ℝ := (1 + ‖z‖) / 2
  have hzρ : ‖z‖ < ρ := by dsimp [ρ]; linarith
  have hρ1 : ρ < 1 := by dsimp [ρ]; linarith
  have hic : ContinuousAt (Function.invFun (qcv_planeSolution μ)) y :=
    (qcv_planeSolution_inv_differentiableOn hμ).continuousOn.continuousAt
      ((qcv_planeDisk_isOpen hμ).mem_nhds hy)
  have hnear : {p : ℂ | p ∈ qcv_planeDisk μ ∧
      ‖Function.invFun (qcv_planeSolution μ) p‖ < ρ} ∈ 𝓝 y := by
    exact inter_mem ((qcv_planeDisk_isOpen hμ).mem_nhds hy)
      (hic ((isOpen_lt continuous_norm continuous_const).mem_nhds hzρ))
  obtain ⟨R, hR, hRsub⟩ := Metric.mem_nhds_iff.mp hnear
  let r₀ : ℝ := (1 - ‖μ‖) / (2 * (‖ν‖ + 1))
  have hr₀ : 0 < r₀ := by dsimp [r₀]; have := bc_norm_lt_one hμ; positivity
  let r := r₀ / 2
  have hr : 0 < r := by dsimp [r]; positivity
  have hball : ∀ t ∈ ball (0 : ℂ) r₀, μ + t • ν ∈ LinfStarBall :=
    fun t ht => qcv_affine_curve_mem_ball hμ ν (mem_ball_zero_iff.mp ht)
  have hrsub : closedBall (0 : ℂ) r ⊆ ball 0 r₀ :=
    closedBall_subset_ball (by dsimp [r]; linarith)
  have hsmall : ball (0 : ℂ) r ⊆ ball 0 r₀ := ball_subset_closedBall.trans hrsub
  have hWt : ∀ p : ℂ, DifferentiableOn ℂ
      (fun t => qcv_planeSolution (μ + t • ν) p) (ball (0 : ℂ) r₀) := by
    intro p
    exact (qcv_planeB_differentiableOn p).comp
      ((differentiableOn_const μ).add (differentiableOn_id.smul_const ν)) hball
  obtain ⟨B, hB⟩ := (isCompact_closedBall (0 : ℂ) r).exists_bound_of_continuousOn
    ((hWt 2).continuousOn.mono hrsub)
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0 (mem_closedBall_self hr.le))
  let H : ℂ → ℂ → ℂ := fun t => qcv_planeTransition (μ + t • ν) μ
  have hHζ : ∀ t ∈ ball (0 : ℂ) r, DifferentiableOn ℂ (H t) (ball y R) := by
    intro t ht
    exact (qcv_planeTransition_conformal hμ (hball t (hsmall ht))).1.mono
      (fun p hp => (hRsub hp).1)
  have hHt : ∀ p ∈ ball y R, DifferentiableOn ℂ (fun t => H t p) (ball (0 : ℂ) r) := by
    intro p _
    exact (hWt (Function.invFun (qcv_planeSolution μ) p)).mono hsmall
  have hM : ∀ t ∈ ball (0 : ℂ) r, ∀ p ∈ ball y R,
      ‖H t p‖ ≤ 4 * B * (ρ / (1 - ρ) ^ 2) := by
    intro t ht p hp
    have hpr := (hRsub hp).2
    have hp1 : ‖Function.invFun (qcv_planeSolution μ) p‖ < 1 := hpr.trans hρ1
    have hb := qcv_W_koebe (bc_norm_lt_one (hball t (hsmall ht))) hp1
    refine hb.trans ?_
    have hm := qcv_mono_koebe (norm_nonneg _) hpr.le hρ1
    have hBt := hB t (ball_subset_closedBall ht)
    calc 4 * ‖qcv_planeSolution (μ + t • ν) 2‖ *
          (‖Function.invFun (qcv_planeSolution μ) p‖ /
            (1 - ‖Function.invFun (qcv_planeSolution μ) p‖) ^ 2)
        ≤ 4 * B * (‖Function.invFun (qcv_planeSolution μ) p‖ /
            (1 - ‖Function.invFun (qcv_planeSolution μ) p‖) ^ 2) := by gcongr
      _ ≤ _ := by gcongr
  have hs := qcv_param_hasDerivAt_iter 1 hr hR hHζ hHt hM
  have he : (fun p => deriv (fun t => H t p) 0) =
      ahVar (ahT_dot (extB ν) (extB μ) (qcv_planeSolution μ)) := by
    ext p
    exact (qcv_planeTransition_base_hasDerivAt hμ ν p).deriv
  rw [he] at hs
  simpa only [iteratedDeriv_one] using hs

/-- **L2.** The derivative of `K₁(𝖿^{κ+tν})(a, b)` at `t = 0`, in source coordinates of the plane solution
`W = W_κ`. -/
theorem l27_kerK1_line {κ : LinfStar} (hκ : κ ∈ LinfStarBall) (ν : LinfStar) {a b : ℂ}
    (ha : a ∈ unitDisc) (hb : b ∈ unitDisc) (hab : a ≠ b) :
    HasDerivAt (fun t : ℂ => kerK1 (fsans (κ + t • ν)) a b)
      (1 / π ^ 2 * (deriv (qcv_planeSolution κ) a * deriv (qcv_planeSolution κ) b) *
        ∫ x in unitDiscExterior, ν x * dz (qcv_planeSolution κ) x ^ 2 /
          ((qcv_planeSolution κ x - qcv_planeSolution κ a) ^ 2 *
            (qcv_planeSolution κ x - qcv_planeSolution κ b) ^ 2)) 0 := by
  set W := qcv_planeSolution κ with hWdef
  set κd := ahT_dot (extB ν) (extB κ) W with hκd
  set V := ahVar κd with hVdef
  set ya := W a with hya_def
  set yb := W b with hyb_def
  let H : ℂ → ℂ → ℂ := fun t => qcv_planeTransition (κ + t • ν) κ
  have hya : ya ∈ qcv_planeDisk κ := ⟨a, ha, rfl⟩
  have hyb : yb ∈ qcv_planeDisk κ := ⟨b, hb, rfl⟩
  have hconf := qcv_planeSolution_conformal hκ
  have hdab : ya ≠ yb := fun h => hab (hconf.2.1 ha hb h)
  have hd : ya - yb ≠ 0 := sub_ne_zero.2 hdab
  have hWa : DifferentiableAt ℂ W a := hconf.1.differentiableAt (isOpen_ball.mem_nhds ha)
  have hWb : DifferentiableAt ℂ W b := hconf.1.differentiableAt (isOpen_ball.mem_nhds hb)
  -- the kernel along the line, through the transition `H t = W_{κ+tν} ∘ W⁻¹`
  have hev : (fun t : ℂ => kerK1 (fsans (κ + t • ν)) a b) =ᶠ[𝓝 0]
      fun t => 1 / π * (1 / (a - b) ^ 2) + (-(1 / π) * (deriv W a * deriv W b)) *
        (deriv (H t) ya * deriv (H t) yb / (H t ya - H t yb) ^ 2) := by
    have hr₀ : 0 < (1 - ‖κ‖) / (2 * (‖ν‖ + 1)) := by have := bc_norm_lt_one hκ; positivity
    filter_upwards [ball_mem_nhds (0 : ℂ) hr₀] with t ht
    have hv := qcv_affine_curve_mem_ball hκ ν (mem_ball_zero_iff.mp ht)
    have hcomp := qcv_planeTransition_comp hκ (κ + t • ν)
    have hHc := qcv_planeTransition_conformal hκ hv
    have hHa : DifferentiableAt ℂ (H t) ya := hHc.1.differentiableAt ((qcv_planeDisk_isOpen hκ).mem_nhds hya)
    have hHb : DifferentiableAt ℂ (H t) yb := hHc.1.differentiableAt ((qcv_planeDisk_isOpen hκ).mem_nhds hyb)
    have hval : ∀ x, qcv_planeSolution (κ + t • ν) x = H t (W x) := fun x => by
      rw [← hcomp]; rfl
    have hder : ∀ x, DifferentiableAt ℂ W x → DifferentiableAt ℂ (H t) (W x) →
        deriv (qcv_planeSolution (κ + t • ν)) x = deriv (H t) (W x) * deriv W x := by
      intro x h1 h2
      rw [← hcomp]
      exact deriv_comp x h2 h1
    rw [S2C.s2c_fsans_eq hv, AppB.b1_kerK1_fB_eq hv ha hb hab]
    change kerK1 (qcv_planeSolution (κ + t • ν)) a b = _
    unfold kerK1
    rw [if_neg hab, hval a, hval b, hder a hWa hHa, hder b hWb hHb]
    ring
  -- derivatives at `t = 0`
  have hHa := qcv_planeTransition_base_hasDerivAt hκ ν ya
  have hHb := qcv_planeTransition_base_hasDerivAt hκ ν yb
  have hDa := l27_transition_deriv hκ ν hya
  have hDb := l27_transition_deriv hκ ν hyb
  have e0 : ∀ y, qcv_planeTransition (κ + (0 : ℂ) • ν) κ y = y := by
    intro y
    simp only [zero_smul, add_zero, qcv_planeTransition_self hκ, id_eq]
  have e1 : ∀ y, deriv (qcv_planeTransition (κ + (0 : ℂ) • ν) κ) y = 1 := by
    intro y
    simp only [zero_smul, add_zero, qcv_planeTransition_self hκ]
    exact deriv_id y
  have hden : (qcv_planeTransition (κ + (0 : ℂ) • ν) κ ya - qcv_planeTransition (κ + (0 : ℂ) • ν) κ yb) ^ 2 ≠ 0 := by
    rw [e0, e0]
    exact pow_ne_zero 2 hd
  have hG0 := (hDa.mul hDb).div ((hHa.sub hHb).pow 2) hden
  have hG : HasDerivAt (fun t => deriv (H t) ya * deriv (H t) yb / (H t ya - H t yb) ^ 2)
      (((deriv V ya * 1 + 1 * deriv V yb) * (ya - yb) ^ 2 - 1 * (2 * (ya - yb) * (V ya - V yb))) /
        ((ya - yb) ^ 2) ^ 2) 0 := by
    refine hG0.congr_deriv ?_
    simp only [Pi.sub_apply, Pi.pow_apply, Pi.mul_apply, e0, e1, Nat.cast_ofNat]
    field_simp
    ring
  have hF := (hG.const_mul (-(1 / π) * (deriv W a * deriv W b))).const_add (1 / π * (1 / (a - b) ^ 2))
  refine (hF.congr_of_eventuallyEq hev).congr_deriv ?_
  -- identification of the derivative
  have hk := qcv_base_dot_isBeltramiCoeff hκ ν
  have hk0 : 0 ≤ ‖ν‖ / (1 - ‖κ‖ ^ 2) := by
    have := bc_norm_lt_one hκ
    have : 0 < 1 - ‖κ‖ ^ 2 := by nlinarith [norm_nonneg κ]
    positivity
  have hzero : ∀ u ∈ qcv_planeDisk κ, κd u = 0 := fun u hu => qcv_base_dot_zero_on_disk hκ ν hu
  have hU := qcv_planeDisk_isOpen hκ
  have hV' : ∀ y ∈ qcv_planeDisk κ, deriv V y = -(1 / π : ℂ) * ∫ u, κd u * kerD1 y u := by
    intro y hy
    have h := ((qcv_ahVar_kernel_derivatives hk0 hk hU hzero hy).1).const_mul (-(1 / π : ℂ))
    exact h.deriv
  have hVv : ∀ y, V y = -(1 / π : ℂ) * ∫ u, κd u * ahKer y u := fun y => rfl
  obtain ⟨iA, iDa⟩ := l27_int_kernels hk0 hk hU hzero hya
  obtain ⟨iB, iDb⟩ := l27_int_kernels hk0 hk hU hzero hyb
  set J := ∫ u, κd u * (1 / ((u - ya) ^ 2 * (u - yb) ^ 2)) with hJ
  have hcomb : (∫ u, κd u * kerD1 ya u) + (∫ u, κd u * kerD1 yb u) -
      2 / (ya - yb) * ((∫ u, κd u * ahKer ya u) - ∫ u, κd u * ahKer yb u) = (ya - yb) ^ 2 * J := by
    rw [← integral_add iDa iDb, ← integral_sub iA iB, ← integral_const_mul]
    have h1 : Integrable (fun u => κd u * kerD1 ya u + κd u * kerD1 yb u) := iDa.add iDb
    have h2 : Integrable (fun u => 2 / (ya - yb) * (κd u * ahKer ya u - κd u * ahKer yb u)) :=
      (iA.sub iB).const_mul _
    rw [← integral_sub h1 h2, hJ, ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp (show volume ({0} : Set ℂ) = 0 by simp),
      measure_eq_zero_iff_ae_notMem.mp (show volume ({1} : Set ℂ) = 0 by simp),
      measure_eq_zero_iff_ae_notMem.mp (show volume ({ya} : Set ℂ) = 0 by simp),
      measure_eq_zero_iff_ae_notMem.mp (show volume ({yb} : Set ℂ) = 0 by simp)] with u h0 h1 h2 h3
    have hid := l27_kernel_identity hdab h0 h1 h2 h3
    rw [show (ya - yb) ^ 2 * (κd u * (1 / ((u - ya) ^ 2 * (u - yb) ^ 2))) =
      κd u * ((ya - yb) ^ 2 / ((u - ya) ^ 2 * (u - yb) ^ 2)) by ring, ← hid]
    ring
  have hsrc := qcv_base_dot_kernel_source hκ ν (fun v => 1 / ((v - ya) ^ 2 * (v - yb) ^ 2)) (by fun_prop)
  have hI : (∫ x in unitDiscExterior, ν x * dz W x ^ 2 / ((W x - ya) ^ 2 * (W x - yb) ^ 2)) = J := by
    rw [hJ, hsrc]
    apply integral_congr_ae
    exact ae_of_all _ fun x => by ring
  rw [hI]
  have hVb' : deriv V yb = (-(1 / π : ℂ)) * ((ya - yb) ^ 2 * J) - deriv V ya +
      2 / (ya - yb) * (V ya - V yb) := by
    rw [hV' ya hya, hV' yb hyb, hVv ya, hVv yb, ← hcomb]
    field_simp
    ring
  rw [hVb']
  have hpi : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  field_simp
  ring

/-- A Cauchy bound for the derivative of the plane solution at a point of `𝔻`. -/
theorem l27_deriv_bound {y : LinfStar} (hy : y ∈ LinfStarBall) {c : ℂ} (hc : c ∈ unitDisc) :
    ‖deriv (qcv_planeSolution y) c‖ ≤
      4 * ‖qcv_planeSolution y 2‖ * ((1 + ‖c‖) / 2 / (1 - (1 + ‖c‖) / 2) ^ 2) / ((1 - ‖c‖) / 4) := by
  have hk := bc_norm_lt_one hy
  have hc1 : ‖c‖ < 1 := mem_ball_zero_iff.mp hc
  have hr : 0 < (1 - ‖c‖) / 4 := by linarith
  have hρ1 : (1 + ‖c‖) / 2 < 1 := by linarith
  have hsub : ∀ z ∈ ball c ((1 - ‖c‖) / 4 + (1 - ‖c‖) / 4), ‖z‖ < (1 + ‖c‖) / 2 := by
    intro z hz
    rw [mem_ball, dist_eq_norm] at hz
    have := norm_le_insert' z c
    have h2 : ‖z‖ ≤ ‖c‖ + ‖z - c‖ := by
      have := norm_add_le c (z - c)
      simpa using this
    linarith
  have hdW := (qcv_W_props hk).2.1
  have hd : ∀ z ∈ ball c ((1 - ‖c‖) / 4 + (1 - ‖c‖) / 4),
      HasDerivAt (qcv_planeSolution y) (deriv (qcv_planeSolution y) z) z := by
    intro z hz
    have hz1 : z ∈ unitDisc := mem_ball_zero_iff.mpr ((hsub z hz).trans hρ1)
    exact (hdW.differentiableAt (isOpen_ball.mem_nhds hz1)).hasDerivAt
  have hb : ∀ z ∈ ball c ((1 - ‖c‖) / 4 + (1 - ‖c‖) / 4),
      ‖qcv_planeSolution y z‖ ≤ 4 * ‖qcv_planeSolution y 2‖ * ((1 + ‖c‖) / 2 / (1 - (1 + ‖c‖) / 2) ^ 2) := by
    intro z hz
    have hzr := hsub z hz
    refine (qcv_W_koebe hk (hzr.trans hρ1)).trans ?_
    exact mul_le_mul_of_nonneg_left (qcv_mono_koebe (norm_nonneg _) hzr.le hρ1) (by positivity)
  exact qcv_cauchy_shrink hr hd hb c (mem_ball_self hr)

/-- Local boundedness of `v ↦ K₁(𝖿^v)(a, b)` on `L∞(𝔻*)₁`. -/
theorem l27_kerK1_locBound {a b : ℂ} (ha : a ∈ unitDisc) (hb : b ∈ unitDisc) (hab : a ≠ b) {x : LinfStar}
    (hx : x ∈ LinfStarBall) :
    ∃ r > 0, ∃ C : ℝ, ∀ y ∈ ball x r, ‖kerK1 (fsans y) a b‖ ≤ C := by
  have hk := bc_norm_lt_one hx
  have hxo : LinfStarBall ∈ 𝓝 x := isOpen_ball.mem_nhds hx
  have hca : ContinuousAt (fun v : LinfStar => qcv_planeSolution v a) x :=
    (qcv_planeB_differentiableOn a).continuousOn.continuousAt hxo
  have hcb : ContinuousAt (fun v : LinfStar => qcv_planeSolution v b) x :=
    (qcv_planeB_differentiableOn b).continuousOn.continuousAt hxo
  have hc2 : ContinuousAt (fun v : LinfStar => qcv_planeSolution v 2) x :=
    (qcv_planeB_differentiableOn 2).continuousOn.continuousAt hxo
  have hne : qcv_planeSolution x a - qcv_planeSolution x b ≠ 0 := by
    intro h
    exact hab ((qcv_W_props hk).2.2.1 (mem_univ a) (mem_univ b) (sub_eq_zero.mp h))
  set δ := ‖qcv_planeSolution x a - qcv_planeSolution x b‖ / 2 with hδ
  have hδ0 : 0 < δ := by rw [hδ]; exact half_pos (norm_pos_iff.mpr hne)
  have h1 : ∀ᶠ v in 𝓝 x, δ < ‖qcv_planeSolution v a - qcv_planeSolution v b‖ :=
    (hca.sub hcb).norm.eventually (lt_mem_nhds (by
      show δ < ‖qcv_planeSolution x a - qcv_planeSolution x b‖
      linarith [hδ0, hδ]))
  have h2 : ∀ᶠ v in 𝓝 x, ‖qcv_planeSolution v 2‖ < ‖qcv_planeSolution x 2‖ + 1 :=
    hc2.norm.eventually (gt_mem_nhds (by linarith))
  obtain ⟨r, hr, hrsub⟩ := Metric.mem_nhds_iff.mp ((h1.and h2).and hxo)
  set B := ‖qcv_planeSolution x 2‖ + 1
  set Ma := 4 * B * ((1 + ‖a‖) / 2 / (1 - (1 + ‖a‖) / 2) ^ 2) / ((1 - ‖a‖) / 4)
  set Mb := 4 * B * ((1 + ‖b‖) / 2 / (1 - (1 + ‖b‖) / 2) ^ 2) / ((1 - ‖b‖) / 4)
  refine ⟨r, hr, 1 / π * (‖1 / (a - b) ^ 2‖ + Ma * Mb / δ ^ 2), fun y hy => ?_⟩
  obtain ⟨⟨hy1, hy2⟩, hyb⟩ := hrsub hy
  have hya1 : ‖a‖ < 1 := mem_ball_zero_iff.mp ha
  have hyb1 : ‖b‖ < 1 := mem_ball_zero_iff.mp hb
  have hmono : ∀ c : ℂ, c ∈ unitDisc → ‖deriv (qcv_planeSolution y) c‖ ≤
      4 * B * ((1 + ‖c‖) / 2 / (1 - (1 + ‖c‖) / 2) ^ 2) / ((1 - ‖c‖) / 4) := by
    intro c hc
    have hc1 : ‖c‖ < 1 := mem_ball_zero_iff.mp hc
    refine (l27_deriv_bound hyb hc).trans ?_
    have hq : 0 ≤ (1 + ‖c‖) / 2 / (1 - (1 + ‖c‖) / 2) ^ 2 := by
      apply div_nonneg <;> [linarith [norm_nonneg c]; positivity]
    have hr4 : 0 < (1 - ‖c‖) / 4 := by linarith
    gcongr
  have hDa := hmono a ha
  have hDb := hmono b hb
  rw [S2C.s2c_fsans_eq hyb, AppB.b1_kerK1_fB_eq hyb ha hb hab]
  change ‖kerK1 (qcv_planeSolution y) a b‖ ≤ _
  unfold kerK1
  rw [if_neg hab]
  have hpi : (0 : ℝ) < π := Real.pi_pos
  have hden : δ ^ 2 ≤ ‖qcv_planeSolution y a - qcv_planeSolution y b‖ ^ 2 := by
    gcongr
  have hfrac : ‖deriv (qcv_planeSolution y) a * deriv (qcv_planeSolution y) b /
      (qcv_planeSolution y a - qcv_planeSolution y b) ^ 2‖ ≤ Ma * Mb / δ ^ 2 := by
    rw [norm_div, norm_mul, norm_pow]
    have hMa0 : 0 ≤ Ma := (norm_nonneg _).trans hDa
    calc ‖deriv (qcv_planeSolution y) a‖ * ‖deriv (qcv_planeSolution y) b‖ /
          ‖qcv_planeSolution y a - qcv_planeSolution y b‖ ^ 2
        ≤ Ma * Mb / ‖qcv_planeSolution y a - qcv_planeSolution y b‖ ^ 2 := by
          gcongr
      _ ≤ Ma * Mb / δ ^ 2 := by
          gcongr
  rw [norm_mul]
  have hpin : ‖(1 / π : ℂ)‖ = 1 / π := by
    rw [norm_div, norm_one, Complex.norm_real, Real.norm_of_nonneg hpi.le]
  rw [hpin]
  gcongr
  exact (norm_sub_le _ _).trans (add_le_add le_rfl hfrac)

/-- **L1.** For fixed `a ≠ b` in `𝔻`, `v ↦ K₁(𝖿^v)(a, b)` is holomorphic on `L∞(𝔻*)₁`. -/
theorem l27_kerK1_differentiableOn {a b : ℂ} (ha : a ∈ unitDisc) (hb : b ∈ unitDisc) (hab : a ≠ b) :
    DifferentiableOn ℂ (fun v : LinfStar => kerK1 (fsans v) a b) LinfStarBall := by
  apply qcv_gateaux_to_frechet isOpen_ball
  · intro x hx
    exact l27_kerK1_locBound ha hb hab hx
  · intro x hx v
    exact (l27_kerK1_line hx v ha hb hab).differentiableAt

/-- Conformal change of variables for the product kernel, with the phase `g'/ḡ'` of the frozen `μ_t`. -/
theorem l27_g_transport {g : ℂ → ℂ} {U V : Set ℂ} (hU : IsOpen U) (hg : IsConformalOnto g U V)
    (ν : ℂ → ℂ) (z w : ℂ) :
    (∫ u in g '' U, ν (Function.invFunOn g U u) *
      (deriv g (Function.invFunOn g U u) / conj (deriv g (Function.invFunOn g U u))) /
        ((u - z) ^ 2 * (u - w) ^ 2)) =
      ∫ ξ in U, ν ξ * deriv g ξ ^ 2 / ((g ξ - z) ^ 2 * (g ξ - w) ^ 2) := by
  rw [ahP_integral_image hU hg.1 hg.2.1]
  apply setIntegral_congr_fun hU.measurableSet
  intro ξ hξ
  have hleft := hg.2.1.leftInvOn_invFunOn hξ
  have hne : deriv g ξ ≠ 0 := deriv_ne_zero_of_injOn hU hg.1 hg.2.1 hξ
  dsimp only
  rw [hleft, Complex.real_smul]
  have hcn : conj (deriv g ξ) ≠ 0 := by simpa using hne
  have hn : ((‖deriv g ξ‖ ^ 2 : ℝ) : ℂ) = deriv g ξ * conj (deriv g ξ) := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  rw [hn]
  field_simp

/-- Pure algebra behind `l27_transport`. -/
theorem l27_alg {Δ P Pa Pb Wa Wb R D e₁ e₂ : ℂ} (hΔ : Δ ≠ 0) (hP : P ≠ 0) (hPa : Pa ≠ 0) (hPb : Pb ≠ 0)
    (hWa : Wa ≠ 0) (hWb : Wb ≠ 0) (he₁ : e₁ ≠ 0) (he₂ : e₂ ≠ 0) :
    Wa * Wb * (Δ / Pa ^ 2 * Wa)⁻¹ * (Δ / Pb ^ 2 * Wb)⁻¹ * (R * D ^ 2 / (e₁ ^ 2 * e₂ ^ 2)) =
      R * (Δ / P ^ 2 * D) ^ 2 * (1 / ((Δ * e₁ / (P * Pa)) ^ 2 * (Δ * e₂ / (P * Pb)) ^ 2)) := by
  field_simp

/-- **L3.** Transport of the L2 value to `Ω_κ* = 𝗀_κ(𝔻*)`, with `z = 𝖿_κ(a)`, `w = 𝖿_κ(b)`. -/
theorem l27_transport {κ : LinfStar} (hκ : κ ∈ LinfStarBall) (ν : LinfStar) {z w : ℂ}
    (hz : z ∈ fsans κ '' unitDisc) (hw : w ∈ fsans κ '' unitDisc) (hzw : z ≠ w) :
    let finv := Function.invFunOn (fsans κ) unitDisc
    let ginv := Function.invFunOn (gsans κ) unitDiscExterior
    deriv (qcv_planeSolution κ) (finv z) * deriv (qcv_planeSolution κ) (finv w) *
        (∫ x in unitDiscExterior, ν x * dz (qcv_planeSolution κ) x ^ 2 /
          ((qcv_planeSolution κ x - qcv_planeSolution κ (finv z)) ^ 2 *
            (qcv_planeSolution κ x - qcv_planeSolution κ (finv w)) ^ 2)) *
        deriv finv z * deriv finv w =
      ∫ u in gsans κ '' unitDiscExterior, Rnm ν κ (ginv u) *
        (deriv (gsans κ) (ginv u) / conj (deriv (gsans κ) (ginv u))) / ((u - z) ^ 2 * (u - w) ^ 2) := by
  intro finv ginv
  obtain ⟨a, ha, rfl⟩ := hz
  obtain ⟨b, hb, rfl⟩ := hw
  have hUo : IsOpen unitDisc := isOpen_ball
  have hVo : IsOpen unitDiscExterior := bc_hEo
  have hcf := S2C.s2c_conf_f hκ
  have hcW := qcv_planeSolution_conformal hκ
  have hfa : finv (fsans κ a) = a := hcf.2.1.leftInvOn_invFunOn ha
  have hfb : finv (fsans κ b) = b := hcf.2.1.leftInvOn_invFunOn hb
  have hia : deriv finv (fsans κ a) = (deriv (fsans κ) a)⁻¹ :=
    eq_inv_of_mul_eq_one_left (t1_deriv_invFunOn_mul hUo hcf ha)
  have hib : deriv finv (fsans κ b) = (deriv (fsans κ) b)⁻¹ :=
    eq_inv_of_mul_eq_one_left (t1_deriv_invFunOn_mul hUo hcf hb)
  rw [hfa, hfb, hia, hib, l27_g_transport hVo (S2C.s2c_conf_g hκ)]
  obtain ⟨A, B, C, D, hdet, hf, hg⟩ := S2C.s2c_mobius hκ
  have hk := bc_norm_lt_one hκ
  have hKm : Measurable fun u : ℂ => 1 / ((u - fsans κ a) ^ 2 * (u - fsans κ b) ^ 2) := by fun_prop
  have hcov := S2C.s2c_cov_var hκ (Rnm ν κ) (fun u => 1 / ((u - fsans κ a) ^ 2 * (u - fsans κ b) ^ 2)) hKm
  rw [qcv_rightDerivative_Rnm hκ ν] at hcov
  have hR : ∫ ξ in unitDiscExterior, Rnm ν κ ξ * deriv (gsans κ) ξ ^ 2 /
        ((gsans κ ξ - fsans κ a) ^ 2 * (gsans κ ξ - fsans κ b) ^ 2) =
      ∫ ξ in unitDiscExterior, Rnm ν κ ξ * deriv (gsans κ) ξ ^ 2 *
        (1 / ((gsans κ ξ - fsans κ a) ^ 2 * (gsans κ ξ - fsans κ b) ^ 2)) := by
    refine integral_congr_ae (ae_of_all _ fun ξ => ?_)
    simp only [mul_one_div]
  rw [hR, ← hcov]
  have hconst : ∀ I : ℂ, deriv (qcv_planeSolution κ) a * deriv (qcv_planeSolution κ) b * I *
      (deriv (fsans κ) a)⁻¹ * (deriv (fsans κ) b)⁻¹ = deriv (qcv_planeSolution κ) a *
        deriv (qcv_planeSolution κ) b * (deriv (fsans κ) a)⁻¹ * (deriv (fsans κ) b)⁻¹ * I := by
    intro I; ring
  rw [hconst, ← integral_const_mul]
  have hdiffW : ∀ᵐ x : ℂ, DifferentiableAt ℝ (qcv_planeSolution κ) x := by
    obtain ⟨⟨KW, hKW⟩, -⟩ := (qcv_W_props hk).1
    have h := s23_c2_ae_good hKW
    rw [Measure.restrict_univ] at h
    filter_upwards [h] with x hx using hx.1
  have hpole : ∀ᵐ x : ℂ, wAS κ (x : ExtPlane) ≠ extInf :=
    measure_eq_zero_iff_ae_notMem.mp ((S2C.s2c_pole_subsingleton κ).measure_zero volume)
  refine setIntegral_congr_ae hVo.measurableSet ?_
  filter_upwards [hdiffW, hpole] with x hdx hpx hx
  obtain ⟨hdenx, hgx⟩ := hg x hx hpx
  have hZ : ∀ᶠ y in 𝓝 x, gsans κ (wA κ y) =
      (A * qcv_planeSolution κ y + B) / (C * qcv_planeSolution κ y + D) := by
    filter_upwards [hVo.mem_nhds hx, (S2C.s2c_pole_open κ).mem_nhds hpx] with y hy hpy
    exact (hg y hy hpy).2
  have hdz := S2C.s2c_dz_mobius hZ hdenx hdx
  have hdena := (hf a ha).1
  have hdenb := (hf b hb).1
  have hda := S2C.s2c_deriv_mobius hκ hf ha
  have hdb := S2C.s2c_deriv_mobius hκ hf hb
  have hWa' : deriv (qcv_planeSolution κ) a ≠ 0 := deriv_ne_zero_of_injOn hUo hcW.1 hcW.2.1 ha
  have hWb' : deriv (qcv_planeSolution κ) b ≠ 0 := deriv_ne_zero_of_injOn hUo hcW.1 hcW.2.1 hb
  have hdiffM : ∀ y, y ∈ unitDisc → (A * qcv_planeSolution κ x + B) / (C * qcv_planeSolution κ x + D) -
      (A * qcv_planeSolution κ y + B) / (C * qcv_planeSolution κ y + D) =
      (A * D - B * C) * (qcv_planeSolution κ x - qcv_planeSolution κ y) /
        ((C * qcv_planeSolution κ x + D) * (C * qcv_planeSolution κ y + D)) := by
    intro y hy
    rw [div_sub_div _ _ hdenx (hf y hy).1]
    congr 1
    ring
  rw [hdz, hda, hdb, hgx, (hf a ha).2, (hf b hb).2, hdiffM a ha, hdiffM b hb]
  by_cases hxa : qcv_planeSolution κ x = qcv_planeSolution κ a
  · rw [hxa]
    simp
  by_cases hxb : qcv_planeSolution κ x = qcv_planeSolution κ b
  · rw [hxb]
    simp
  exact l27_alg hdet hdenx hdena hdenb hWa' hWb' (sub_ne_zero.2 hxa) (sub_ne_zero.2 hxb)

/-- **L4 (general path, for the `thm_2_6` assembly).** For any path `γ : ℝ → L∞(𝔻*)` differentiable at `s₀` with
`γ s₀ ∈ L∞(𝔻*)₁`, the variation of `K₁` along `γ` at `s₀`, in the coordinates of `Ω_{s₀} = 𝖿^{γ s₀}(𝔻)`, is the
integral (2.6) with `μ_{s₀}` defined by `(μ_{s₀} ∘ g) ḡ'/g' = D_{γ s₀} R_{(γ s₀)⁻¹}(γ')`. -/
theorem l27_general {γ : ℝ → LinfStar} {γ' : LinfStar} {s₀ : ℝ} (hγ : HasDerivAt γ γ' s₀)
    (hball : γ s₀ ∈ LinfStarBall) {z w : ℂ} (hz : z ∈ fsans (γ s₀) '' unitDisc)
    (hw : w ∈ fsans (γ s₀) '' unitDisc) (hzw : z ≠ w) :
    let ft := fsans (γ s₀)
    let gt := gsans (γ s₀)
    let finv := Function.invFunOn ft unitDisc
    let ginv := Function.invFunOn gt unitDiscExterior
    let μt : ℂ → ℂ := fun u =>
      fderiv ℂ (fun l => beltramiMul l (beltramiInv (γ s₀))) (γ s₀) γ' (ginv u) *
        (deriv gt (ginv u) / conj (deriv gt (ginv u)))
    HasDerivAt (fun s : ℝ => kerK1 (fsans (γ s)) (finv z) (finv w) * deriv finv z * deriv finv w)
      (1 / π ^ 2 * ∫ u in gt '' unitDiscExterior, μt u / ((u - z) ^ 2 * (u - w) ^ 2)) s₀ := by
  intro ft gt finv ginv μt
  have ha : finv z ∈ unitDisc := Function.invFunOn_mem hz
  have hb : finv w ∈ unitDisc := Function.invFunOn_mem hw
  have hab : finv z ≠ finv w := by
    intro h
    apply hzw
    rw [← Function.invFunOn_eq hz, ← Function.invFunOn_eq hw]
    exact congrArg ft h
  have hD := ((l27_kerK1_differentiableOn ha hb hab (γ s₀) hball).differentiableAt
    (isOpen_ball.mem_nhds hball)).hasFDerivAt
  have hc := (hD.restrictScalars ℝ).comp_hasDerivAt s₀ hγ
  have hline : HasDerivAt (fun t : ℂ => γ s₀ + t • γ') γ' 0 := by
    simpa using ((hasDerivAt_id (0 : ℂ)).smul_const γ').const_add (γ s₀)
  have hD' : HasFDerivAt (fun v : LinfStar => kerK1 (fsans v) (finv z) (finv w))
      (fderiv ℂ (fun v : LinfStar => kerK1 (fsans v) (finv z) (finv w)) (γ s₀)) (γ s₀ + (0 : ℂ) • γ') := by
    simpa using hD
  have hl := hD'.comp_hasDerivAt (0 : ℂ) hline
  have hval := hl.unique (l27_kerK1_line hball γ' ha hb hab)
  have htr := l27_transport hball γ' hz hw hzw
  dsimp only at htr
  have hμt : μt = fun u => Rnm γ' (γ s₀) (ginv u) * (deriv gt (ginv u) / conj (deriv gt (ginv u))) := by
    funext u
    show fderiv ℂ (fun l => beltramiMul l (beltramiInv (γ s₀))) (γ s₀) γ' (ginv u) * _ = _
    rw [eq_1_5 hball]
  have hfin := (hc.mul_const (deriv finv z)).mul_const (deriv finv w)
  refine hfin.congr_deriv ?_
  change fderiv ℂ (fun v : LinfStar => kerK1 (fsans v) (finv z) (finv w)) (γ s₀) γ' * deriv finv z *
    deriv finv w = _
  rw [hval, hμt]
  simp only [mul_div_assoc] at htr ⊢
  rw [← htr]
  ring

/-- **Lemma 2.7** with **(2.6)** (TT:4064–4076).
- Setting: `μ ∈ L²(𝔻*, ρ d²z) ∩ 𝒪(𝔻*)₁`, `f_t = 𝖿^{tμ}`, `g_t = 𝗀_{tμ}`, `Ω_t* = f_t(𝔻*) = g_t(𝔻*)`.
- `μ_t` on `Ω_t*` is defined by `(μ_t ∘ g_t) \overline{g_t'}/g_t' = D_{tμ}R_{(tμ)⁻¹}(μ)`.
- Then `d/ds|_{s=0} (K₁)_{s+t}(f_t⁻¹(z), f_t⁻¹(w)) (f_t⁻¹)'(z) (f_t⁻¹)'(w)` equals
  `(1/π²) ∬_{Ω_t*} μ_t(u)/((u - z)²(u - w)²) d²u`, for `z, w ∈ Ω_t = f_t(𝔻)` (the poles lie outside `Ω_t*`, so the
  integral is absolutely convergent). -/
theorem l27_lemma_2_7 {μ : LinfStar} (hμ : μ ∈ groupO) (hμ2 : normL2 unitDiscExterior μ < ∞) {t : ℝ} (ht0 : 0 ≤ t)
    (ht1 : t ≤ 1) {z w : ℂ} (hz : z ∈ fsans ((t : ℂ) • μ) '' unitDisc) (hw : w ∈ fsans ((t : ℂ) • μ) '' unitDisc)
    (hzw : z ≠ w) :
    let ft := fsans ((t : ℂ) • μ)
    let gt := gsans ((t : ℂ) • μ)
    let finv := Function.invFunOn ft unitDisc
    let ginv := Function.invFunOn gt unitDiscExterior
    let μt : ℂ → ℂ := fun u =>
      fderiv ℂ (fun l => beltramiMul l (beltramiInv ((t : ℂ) • μ))) ((t : ℂ) • μ) μ (ginv u) *
        (deriv gt (ginv u) / conj (deriv gt (ginv u)))
    HasDerivAt (fun s : ℝ => kerK1 (fsans (((s + t : ℝ) : ℂ) • μ)) (finv z) (finv w) * deriv finv z * deriv finv w)
      (1 / π ^ 2 * ∫ u in gt '' unitDiscExterior, μt u / ((u - z) ^ 2 * (u - w) ^ 2)) 0 := by
  -- `μ ∈ L²` is not needed for the pointwise variation; it is used only in the `thm_2_6` assembly.
  have _h := hμ2
  intro ft gt finv ginv μt
  have hμb := l29b_groupO_ball hμ
  let γ : ℝ → LinfStar := fun s => ((s + t : ℝ) : ℂ) • μ
  have hγ : HasDerivAt γ μ 0 := by
    have h1 : HasDerivAt (fun s : ℝ => ((s + t : ℝ) : ℂ)) ((1 : ℝ) : ℂ) 0 :=
      ((hasDerivAt_id (0 : ℝ)).add_const t).ofReal_comp
    simpa [γ] using h1.smul_const μ
  have hγ0 : γ 0 = (t : ℂ) • μ := by simp [γ]
  have hb : γ 0 ∈ LinfStarBall := by
    rw [hγ0]
    have hμ1 : ‖μ‖ < 1 := by simpa [LinfStarBall] using hμb
    have hn : ‖(t : ℂ) • μ‖ < 1 := by
      rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg ht0]
      nlinarith [norm_nonneg μ]
    simpa [LinfStarBall] using hn
  have h := l27_general hγ hb (by rw [hγ0]; exact hz) (by rw [hγ0]; exact hw) hzw
  simp only [hγ0] at h
  exact h

/-- An operator norm bound from the unit ball (complex scalars). -/
theorem l27_opNorm_le {T : LinfStar →L[ℂ] ℂ} {K : ℝ} (hK : 0 ≤ K) (h : ∀ v : LinfStar, ‖v‖ ≤ 1 → ‖T v‖ ≤ K) :
    ‖T‖ ≤ K := by
  refine ContinuousLinearMap.opNorm_le_bound T hK fun v => ?_
  by_cases hv : v = 0
  · simp [hv]
  have hn : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have hu : ‖((‖v‖ : ℂ))⁻¹ • v‖ ≤ 1 := by
    rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hn.le, inv_mul_cancel₀ hn.ne']
  have h1 := h _ hu
  rw [map_smul, smul_eq_mul, norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hn.le] at h1
  rw [inv_mul_le_iff₀ hn] at h1
  linarith [mul_comm K ‖v‖]

/-- Cauchy estimate along a complex line for the difference of two parallel lines. -/
theorem l27_line_cauchy {Φ : LinfStar → ℂ} {U : Set LinfStar} (hΦ : DifferentiableOn ℂ Φ U) (hU : IsOpen U)
    {v v' h : LinfStar} {ρ M : ℝ} (hρ : 0 < ρ) (hs : ∀ t : ℂ, ‖t‖ ≤ ρ → v + t • h ∈ U)
    (hs' : ∀ t : ℂ, ‖t‖ ≤ ρ → v' + t • h ∈ U)
    (hM : ∀ t : ℂ, ‖t‖ = ρ → ‖Φ (v + t • h) - Φ (v' + t • h)‖ ≤ M) :
    ‖fderiv ℂ Φ v h - fderiv ℂ Φ v' h‖ ≤ M / ρ := by
  let g : ℂ → ℂ := fun t => Φ (v + t • h) - Φ (v' + t • h)
  have hline : ∀ w : LinfStar, ∀ t : ℂ, HasDerivAt (fun s : ℂ => w + s • h) h t := fun w t => by
    simpa using ((hasDerivAt_id t).smul_const h).const_add w
  have hdiff : ∀ w : LinfStar, (∀ t : ℂ, ‖t‖ ≤ ρ → w + t • h ∈ U) → ∀ t : ℂ, ‖t‖ ≤ ρ →
      HasDerivAt (fun s : ℂ => Φ (w + s • h)) (fderiv ℂ Φ (w + t • h) h) t := by
    intro w hw t ht
    have hD := (hΦ.differentiableAt (hU.mem_nhds (hw t ht))).hasFDerivAt
    exact hD.comp_hasDerivAt t (hline w t)
  have hg : DifferentiableOn ℂ g (closedBall 0 ρ) := fun t ht => by
    have ht' : ‖t‖ ≤ ρ := by simpa using ht
    exact ((hdiff v hs t ht').sub (hdiff v' hs' t ht')).differentiableAt.differentiableWithinAt
  have hg0 : deriv g 0 = fderiv ℂ Φ v h - fderiv ℂ Φ v' h := by
    have h0 := (hdiff v hs 0 (by simp [hρ.le])).sub (hdiff v' hs' 0 (by simp [hρ.le]))
    have h1 := h0.deriv
    simp only [zero_smul, add_zero] at h1
    exact h1
  rw [← hg0]
  apply Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hρ
  · apply DifferentiableOn.diffContOnCl
    rw [closure_ball _ hρ.ne']
    exact hg
  · intro t ht
    exact hM t (by simpa using ht)

/-- **L6 (optional).** The derivative of L1 is continuous on the ball (Cauchy estimates on complex lines). -/
theorem l27_fderiv_continuousOn {a b : ℂ} (ha : a ∈ unitDisc) (hb : b ∈ unitDisc) (hab : a ≠ b) :
    ContinuousOn (fun v : LinfStar => fderiv ℂ (fun v : LinfStar => kerK1 (fsans v) a b) v) LinfStarBall := by
  set Φ : LinfStar → ℂ := fun v => kerK1 (fsans v) a b with hΦdef
  have hΦ : DifferentiableOn ℂ Φ LinfStarBall := l27_kerK1_differentiableOn ha hb hab
  intro x hx
  obtain ⟨R₀, hR₀, C, hC⟩ := l27_kerK1_locBound ha hb hab hx
  obtain ⟨R₁, hR₁, hR₁sub⟩ := Metric.isOpen_iff.mp (isOpen_ball : IsOpen LinfStarBall) x hx
  set R := min R₀ R₁ with hR
  have hRpos : 0 < R := lt_min hR₀ hR₁
  set U := ball x R with hU
  have hUo : IsOpen U := isOpen_ball
  have hUsub : U ⊆ LinfStarBall := (ball_subset_ball (min_le_right _ _)).trans hR₁sub
  have hCU : ∀ y ∈ U, ‖Φ y‖ ≤ C := fun y hy => hC y (ball_subset_ball (min_le_left _ _) hy)
  have hΦU : DifferentiableOn ℂ Φ U := hΦ.mono hUsub
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hCU x (mem_ball_self hRpos))
  set ρ := R / 4 with hρ
  have hρ0 : 0 < ρ := by positivity
  have hmem : ∀ y : LinfStar, ∀ s : ℝ, ‖y - x‖ < s → ∀ h : LinfStar, ‖h‖ ≤ 1 → ∀ t : ℂ, ‖t‖ ≤ ρ →
      s + ρ ≤ R → y + t • h ∈ U := by
    intro y s hy h hh t ht hs
    rw [hU, mem_ball, dist_eq_norm]
    have h1 : ‖t • h‖ ≤ ρ := by
      rw [norm_smul]
      nlinarith [norm_nonneg t, norm_nonneg h]
    have h2 : ‖y + t • h - x‖ ≤ ‖y - x‖ + ‖t • h‖ := by
      rw [show y + t • h - x = (y - x) + t • h by abel]
      exact norm_add_le _ _
    linarith
  -- the derivative is bounded by `C/ρ` on `ball x (R/2)`
  set L := C / ρ with hL
  have hL0 : 0 ≤ L := by positivity
  have hDb : ∀ u ∈ ball x (R / 2), ‖fderiv ℂ Φ u‖ ≤ L := by
    intro u hu
    apply l27_opNorm_le hL0
    intro h hh
    have hu' : ‖u - x‖ < R / 2 := by simpa [mem_ball, dist_eq_norm] using hu
    have hs : ∀ t : ℂ, ‖t‖ ≤ ρ → u + t • h ∈ U := fun t ht =>
      hmem u (R / 2) hu' h hh t ht (by rw [hρ]; linarith)
    have hline : ∀ t : ℂ, HasDerivAt (fun s : ℂ => u + s • h) h t := fun t => by
      simpa using ((hasDerivAt_id t).smul_const h).const_add u
    let g : ℂ → ℂ := fun t => Φ (u + t • h)
    have hgd : DifferentiableOn ℂ g (closedBall 0 ρ) := fun t ht => by
      have ht' : ‖t‖ ≤ ρ := by simpa using ht
      have hD := (hΦU.differentiableAt (hUo.mem_nhds (hs t ht'))).hasFDerivAt
      exact (hD.comp_hasDerivAt t (hline t)).differentiableAt.differentiableWithinAt
    have hg0 : deriv g 0 = fderiv ℂ Φ u h := by
      have hD := (hΦU.differentiableAt (hUo.mem_nhds (hs 0 (by simp [hρ0.le])))).hasFDerivAt
      have h1 := (hD.comp_hasDerivAt 0 (hline 0)).deriv
      simp only [zero_smul, add_zero] at h1
      exact h1
    rw [← hg0]
    apply Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hρ0
    · apply DifferentiableOn.diffContOnCl
      rw [closure_ball _ hρ0.ne']
      exact hgd
    · intro t ht
      have ht' : ‖t‖ = ρ := by simpa using ht
      exact hCU _ (hs t ht'.le)
  -- Lipschitz bound for `Φ` on `ball x (R/2)`
  have hLip : ∀ y₁ ∈ ball x (R / 2), ∀ y₂ ∈ ball x (R / 2), ‖Φ y₁ - Φ y₂‖ ≤ L * ‖y₁ - y₂‖ := by
    intro y₁ h₁ y₂ h₂
    have hsub : ball x (R / 2) ⊆ U := ball_subset_ball (by linarith)
    exact (convex_ball x (R / 2)).norm_image_sub_le_of_norm_fderiv_le
      (fun u hu => hΦU.differentiableAt (hUo.mem_nhds (hsub hu))) hDb h₂ h₁
  -- Lipschitz bound for the derivative on `ball x (R/4)`
  have hDL : ∀ v ∈ ball x (R / 4), ‖fderiv ℂ Φ v - fderiv ℂ Φ x‖ ≤ L / ρ * ‖v - x‖ := by
    intro v hv
    have hv' : ‖v - x‖ < R / 4 := by simpa [mem_ball, dist_eq_norm] using hv
    have hK0 : 0 ≤ L / ρ * ‖v - x‖ := by positivity
    apply l27_opNorm_le hK0
    intro h hh
    have hx0 : ‖x - x‖ < R / 4 := by simpa using div_pos hRpos (by norm_num : (0 : ℝ) < 4)
    have hs : ∀ t : ℂ, ‖t‖ ≤ ρ → v + t • h ∈ U := fun t ht =>
      hmem v (R / 4) hv' h hh t ht (by rw [hρ]; linarith)
    have hs' : ∀ t : ℂ, ‖t‖ ≤ ρ → x + t • h ∈ U := fun t ht =>
      hmem x (R / 4) hx0 h hh t ht (by rw [hρ]; linarith)
    have hq : ∀ t : ℂ, ‖t‖ = ρ → ∀ y : LinfStar, ‖y - x‖ < R / 4 → y + t • h ∈ ball x (R / 2) := by
      intro t ht y hy
      rw [mem_ball, dist_eq_norm]
      have h1 : ‖t • h‖ ≤ ρ := by
        rw [norm_smul, ht]
        nlinarith [norm_nonneg h]
      have h2 : ‖y + t • h - x‖ ≤ ‖y - x‖ + ‖t • h‖ := by
        rw [show y + t • h - x = (y - x) + t • h by abel]
        exact norm_add_le _ _
      rw [hρ] at h1
      linarith
    have hc := l27_line_cauchy hΦU hUo hρ0 hs hs' (M := L * ‖v - x‖) (fun t ht => by
      have := hLip _ (hq t ht v hv') _ (hq t ht x hx0)
      simpa [add_sub_add_right_eq_sub] using this)
    rw [ContinuousLinearMap.sub_apply]
    refine hc.trans (le_of_eq ?_)
    ring
  -- conclude continuity at `x`
  apply ContinuousAt.continuousWithinAt
  rw [Metric.continuousAt_iff]
  intro ε hε
  have hLρ : 0 ≤ L / ρ := by positivity
  refine ⟨min (R / 4) (ε / (L / ρ + 1)), lt_min (by positivity) (by positivity), fun v hv => ?_⟩
  have hv1 : v ∈ ball x (R / 4) := mem_ball.mpr (lt_of_lt_of_le hv (min_le_left _ _))
  have hv2 : ‖v - x‖ < ε / (L / ρ + 1) := by
    have := lt_of_lt_of_le hv (min_le_right _ _)
    rwa [dist_eq_norm] at this
  rw [dist_eq_norm]
  calc ‖fderiv ℂ Φ v - fderiv ℂ Φ x‖ ≤ L / ρ * ‖v - x‖ := hDL v hv1
    _ ≤ (L / ρ + 1) * ‖v - x‖ := by nlinarith [norm_nonneg (v - x)]
    _ < (L / ρ + 1) * (ε / (L / ρ + 1)) := by gcongr
    _ = ε := by field_simp

/-- **Lemma 2.7** with **(2.6)** (TT:4064–4076).
- Setting: `μ ∈ L²(𝔻*, ρ d²z) ∩ 𝒪(𝔻*)₁`, `f_t = 𝖿^{tμ}`, `g_t = 𝗀_{tμ}`, `Ω_t* = f_t(𝔻*) = g_t(𝔻*)`.
- `μ_t` on `Ω_t*` is defined by `(μ_t ∘ g_t) \overline{g_t'}/g_t' = D_{tμ}R_{(tμ)⁻¹}(μ)`.
- Then `d/ds|_{s=0} (K₁)_{s+t}(f_t⁻¹(z), f_t⁻¹(w)) (f_t⁻¹)'(z) (f_t⁻¹)'(w)` equals
  `(1/π²) ∬_{Ω_t*} μ_t(u)/((u - z)²(u - w)²) d²u`, for `z, w ∈ Ω_t = f_t(𝔻)` (the poles lie outside `Ω_t*`, so the
  integral is absolutely convergent). -/
theorem lemma_2_7 {μ : LinfStar} (hμ : μ ∈ groupO) (hμ2 : normL2 unitDiscExterior μ < ∞) {t : ℝ} (ht0 : 0 ≤ t)
    (ht1 : t ≤ 1) {z w : ℂ} (hz : z ∈ fsans ((t : ℂ) • μ) '' unitDisc) (hw : w ∈ fsans ((t : ℂ) • μ) '' unitDisc)
    (hzw : z ≠ w) :
    let ft := fsans ((t : ℂ) • μ)
    let gt := gsans ((t : ℂ) • μ)
    let finv := Function.invFunOn ft unitDisc
    let ginv := Function.invFunOn gt unitDiscExterior
    let μt : ℂ → ℂ := fun u =>
      fderiv ℂ (fun l => beltramiMul l (beltramiInv ((t : ℂ) • μ))) ((t : ℂ) • μ) μ (ginv u) *
        (deriv gt (ginv u) / conj (deriv gt (ginv u)))
    HasDerivAt (fun s : ℝ => kerK1 (fsans (((s + t : ℝ) : ℂ) • μ)) (finv z) (finv w) * deriv finv z * deriv finv w)
      (1 / π ^ 2 * ∫ u in gt '' unitDiscExterior, μt u / ((u - z) ^ 2 * (u - w) ^ 2)) 0 :=
  l27_lemma_2_7 hμ hμ2 ht0 ht1 hz hw hzw

end Ch2
end TakhtajanTeo
