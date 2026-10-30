import TakhtajanTeo.Ch2.S4_Completed
import TakhtajanTeo.Ch1.HilbertBersDifferentialL2
import TakhtajanTeo.Ch1.GroupTranslation
import TakhtajanTeo.Ch1.S6Eq62
import TakhtajanTeo.Ch1.L613

/-! # Reductions of Corollary 4.2, Remark 4.3 and the potential on `T(1)` to Theorem 4.1 (`s4g_`)

`cor_4_2`, `remark_4_3` and `wpPotential_spec` follow from `thm_4_1` (and, for Remark 4.3, from the first clause of
`thm_3_8`). The analytic input is local: near `0`, the Bers-coordinate points of the chart `V_κ` stay in the
component of `[κ]` and do not depend on the representative `κ`. -/

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal ComplexConjugate Classical Real
noncomputable section
namespace TakhtajanTeo
open LiZhongQC
namespace Ch2

/-- The Bers-coordinate point `[l * κ]` depends only on `[κ]`. -/
theorem s4g_ptT_congr {κ κ' : LinfStarBall} (h : Phi κ = Phi κ') {l : LinfStar} (hl : l ∈ LinfStarBall) :
    ptT (beltramiMul l κ) = ptT (beltramiMul l κ') := by
  have h1 : beltramiMul l κ ∈ LinfStarBall := bg_mul_mem_ball κ.2 hl
  have h2 : beltramiMul l κ' ∈ LinfStarBall := bg_mul_mem_ball κ'.2 hl
  have hs : teichSetoid κ κ' := Quotient.exact h
  unfold ptT
  rw [dif_pos h1, dif_pos h2]
  apply Quotient.sound
  show ∀ z ∈ unitCircle, wA (beltramiMul l κ) z = wA (beltramiMul l κ') z
  exact beltramiMul_respects (l₁ := ⟨l, hl⟩) (l₂ := ⟨l, hl⟩) (teichSetoid.iseqv.refl _) hs

/-- The inverse Bers chart at `κ` sends `ψ` with `Λψ = l` to the Bers-coordinate point `[l * κ]`. -/
theorem s4g_chart_eq (κ : LinfStarBall) {ψ : AInf unitDisc} {l : LinfStar} (hψ : Lambda ψ = l)
    (hl : l ∈ LinfStarBall) : bersChartInv κ ψ = ptT (beltramiMul l κ) := by
  subst hψ
  have h1 : beltramiMul (Lambda ψ) κ ∈ LinfStarBall := bg_mul_mem_ball κ.2 hl
  unfold bersChartInv ptT
  rw [dif_pos h1, dif_pos h1]

/-- Near `0`, the Bers-coordinate points of `V_κ` along harmonic `μ, ν` stay in the component of `[κ]`. -/
theorem s4g_local_component {μ ν : ℂ → ℂ} (hμ : μ ∈ harmonicL2 unitDiscExterior)
    (hν : ν ∈ harmonicL2 unitDiscExterior) (κ : LinfStarBall) :
    ∀ᶠ e in 𝓝 (0 : ℂ × ℂ), e.1 • toLinf μ + e.2 • toLinf ν ∈ LinfStarBall ∧
      ptT (beltramiMul (e.1 • toLinf μ + e.2 • toLinf ν) κ) ∈ componentT (Phi κ) := by
  letI : TopologicalSpace T1 := hilbertTopology
  obtain ⟨κ0, hκ0O, hκ0⟩ := ctb_exists_groupO_rep (Phi κ)
  obtain ⟨φμ, hΛμ, -⟩ := hbL2_harmonic_coordinate hμ
  obtain ⟨φν, hΛν, -⟩ := hbL2_harmonic_coordinate hν
  set Φ : ℂ × ℂ → A2 unitDisc := fun e => e.1 • φμ + e.2 • φν with hΦ
  set L : ℂ × ℂ → LinfStar := fun e => e.1 • toLinf μ + e.2 • toLinf ν with hL
  have hΦc : Continuous Φ := (continuous_fst.smul continuous_const).add (continuous_snd.smul continuous_const)
  have hLc : Continuous L := (continuous_fst.smul continuous_const).add (continuous_snd.smul continuous_const)
  have hr0 : 0 < Real.sqrt (π / 3) := by positivity
  have hW : IsOpen (Φ ⁻¹' ball 0 (Real.sqrt (π / 3)) ∩ L ⁻¹' LinfStarBall) :=
    (isOpen_ball.preimage hΦc).inter (isOpen_ball.preimage hLc)
  have h0W : (0 : ℂ × ℂ) ∈ Φ ⁻¹' ball 0 (Real.sqrt (π / 3)) ∩ L ⁻¹' LinfStarBall := by
    refine ⟨?_, ?_⟩
    · show Φ 0 ∈ ball 0 (Real.sqrt (π / 3))
      simp [hΦ, Real.pi_pos]
    · show L 0 ∈ ball (0 : LinfStar) 1
      simp [hL]
  obtain ⟨r, hr, hrW⟩ := Metric.isOpen_iff.1 hW 0 h0W
  -- the chart image of the coordinate ball is connected and contains `[κ]`
  have hco : ContinuousOn (fun φ : A2 unitDisc => bersChartInv κ0 (A2toAInf φ))
      (ball (0 : A2 unitDisc) (Real.sqrt (π / 3))) :=
    continuousOn_iff_continuous_domRestrict.2 (gtr_chart_continuous hκ0O)
  have hcomp : ContinuousOn (fun e => bersChartInv κ0 (A2toAInf (Φ e))) (ball (0 : ℂ × ℂ) r) :=
    hco.comp hΦc.continuousOn (fun e he => (hrW he).1)
  have hconn := ((convex_ball (0 : ℂ × ℂ) r).isPreconnected).image _ hcomp
  have hmem0 : Phi κ ∈ (fun e => bersChartInv κ0 (A2toAInf (Φ e))) '' ball (0 : ℂ × ℂ) r := by
    refine ⟨0, mem_ball_self hr, ?_⟩
    show bersChartInv κ0 (A2toAInf (Φ 0)) = Phi κ
    have h0 : Φ 0 = 0 := by simp [hΦ]
    rw [h0, gtr_chart_zero, hκ0]
  have hsub := hconn.subset_connectedComponent hmem0
  filter_upwards [ball_mem_nhds (0 : ℂ × ℂ) hr] with e he
  have hLe : L e ∈ LinfStarBall := (hrW he).2
  refine ⟨hLe, ?_⟩
  have hA : A2toAInf (Φ e) = e.1 • A2toAInf φμ + e.2 • A2toAInf φν := by
    show A2toAInfCLM (e.1 • φμ + e.2 • φν) = _
    rw [map_add, map_smul, map_smul]
    rfl
  have hΛ : Lambda (A2toAInf (Φ e)) = L e := by
    rw [hA, Lambda_add, Lambda_smul, Lambda_smul, hΛμ, hΛν]
  have hpt : ptT (beltramiMul (L e) κ) = bersChartInv κ0 (A2toAInf (Φ e)) := by
    rw [s4g_chart_eq κ0 hΛ hLe]
    exact s4g_ptT_congr hκ0 hLe
  show ptT (beltramiMul (L e) κ) ∈ @connectedComponent _ hilbertTopology (Phi κ)
  rw [hpt]
  exact hsub ⟨e, he, rfl⟩

/-- `bersDzDzbar` only sees the germ at `0` of the two-parameter function. -/
theorem s4g_bersDzDzbar_congr {F G : T1 → ℝ} {κ κ' : LinfStar} {μ ν : ℂ → ℂ}
    (h : ∀ᶠ e in 𝓝 (0 : ℂ × ℂ), F (ptT (beltramiMul (e.1 • toLinf μ + e.2 • toLinf ν) κ)) =
      G (ptT (beltramiMul (e.1 • toLinf μ + e.2 • toLinf ν) κ'))) :
    bersDzDzbar F κ μ ν = bersDzDzbar G κ' μ ν := by
  have h' : ∀ᶠ e in 𝓝 (0 : ℂ) ×ˢ 𝓝 (0 : ℂ), F (ptT (beltramiMul (e.1 • toLinf μ + e.2 • toLinf ν) κ)) =
      G (ptT (beltramiMul (e.1 • toLinf μ + e.2 • toLinf ν) κ')) := by
    rw [← nhds_prod_eq]
    exact h
  obtain ⟨pa, hpa, pb, hpb, hab⟩ := Filter.eventually_prod_iff.1 h'
  unfold bersDzDzbar
  apply l613_dz_congr
  filter_upwards [hpa] with a ha
  have hin : (fun e₂ : ℂ => (F (ptT (beltramiMul (a • toLinf μ + e₂ • toLinf ν) κ)) : ℂ)) =ᶠ[𝓝 (0 : ℂ)]
      fun e₂ : ℂ => (G (ptT (beltramiMul (a • toLinf μ + e₂ • toLinf ν) κ')) : ℂ) := by
    filter_upwards [hpb] with b hb
    have hx := hab ha hb
    dsimp only at hx
    rw [hx]
  show (fderiv ℝ _ 0 1 + I * fderiv ℝ _ 0 I) / 2 = (fderiv ℝ _ 0 1 + I * fderiv ℝ _ 0 I) / 2
  rw [hin.fderiv_eq]

/-- `∂_ε̄ (c g) = c ∂_ε̄ g` for a nonzero constant `c`, without a differentiability hypothesis. -/
theorem s4g_dzbar_const_mul {g : ℂ → ℂ} {c : ℂ} (hc : c ≠ 0) (ε : ℂ) :
    dzbar (fun e => c * g e) ε = c * dzbar g ε := by
  by_cases hg : DifferentiableAt ℝ g ε
  · have h := (hg.hasFDerivAt.const_mul c).fderiv
    show (fderiv ℝ (fun e => c * g e) ε 1 + I * fderiv ℝ (fun e => c * g e) ε I) / 2 =
      c * ((fderiv ℝ g ε 1 + I * fderiv ℝ g ε I) / 2)
    rw [h]
    simp only [smul_apply, smul_eq_mul]
    ring
  · have hcg : ¬ DifferentiableAt ℝ (fun e => c * g e) ε := by
      intro h
      apply hg
      have h2 := h.const_mul c⁻¹
      refine h2.congr_of_eventuallyEq (Eventually.of_forall fun e => ?_)
      show g e = c⁻¹ * (c * g e)
      rw [← mul_assoc, inv_mul_cancel₀ hc, one_mul]
    show (fderiv ℝ (fun e => c * g e) ε 1 + I * fderiv ℝ (fun e => c * g e) ε I) / 2 =
      c * ((fderiv ℝ g ε 1 + I * fderiv ℝ g ε I) / 2)
    rw [fderiv_zero_of_not_differentiableAt hg, fderiv_zero_of_not_differentiableAt hcg]
    simp

/-- `bersDzDzbar` commutes with real constant factors. -/
theorem s4g_bersDzDzbar_const_mul (c : ℝ) (F : T1 → ℝ) (κ : LinfStar) (μ ν : ℂ → ℂ) :
    bersDzDzbar (fun q => c * F q) κ μ ν = c * bersDzDzbar F κ μ ν := by
  unfold bersDzDzbar
  have hcast : ∀ x : ℝ, ((c * x : ℝ) : ℂ) = (c : ℂ) * (x : ℂ) := fun x => by push_cast; ring
  simp only [hcast]
  by_cases hc : (c : ℂ) = 0
  · rw [hc]
    simp only [zero_mul]
    show (fderiv ℝ (fun _ : ℂ => (fderiv ℝ (fun _ : ℂ => (0 : ℂ)) 0 1 + I * fderiv ℝ (fun _ : ℂ => (0 : ℂ)) 0 I) / 2)
      0 1 - I * fderiv ℝ (fun _ : ℂ => (fderiv ℝ (fun _ : ℂ => (0 : ℂ)) 0 1 +
        I * fderiv ℝ (fun _ : ℂ => (0 : ℂ)) 0 I) / 2) 0 I) / 2 = 0
    simp
  · have he : (fun e₁ : ℂ => dzbar (fun e₂ : ℂ => (c : ℂ) *
        (F (ptT (beltramiMul (e₁ • toLinf μ + e₂ • toLinf ν) κ)) : ℂ)) 0) =
        fun e₁ : ℂ => (c : ℂ) * dzbar (fun e₂ : ℂ => (F (ptT (beltramiMul (e₁ • toLinf μ + e₂ • toLinf ν) κ)) : ℂ)) 0 := by
      funext e₁
      exact s4g_dzbar_const_mul hc 0
    rw [he, e62_dz_const_mul hc]

/-- Corollary 4.2 from Theorem 4.1 at `p`. -/
theorem s4g_cor_4_2 {p : T1} {μ ν : ℂ → ℂ}
    (h41 : bersDzDzbar liouvilleS1 (Quotient.out p : LinfStarBall) μ ν = wpInner μ ν) :
    bersDzDzbar liouvilleS1 (Quotient.out p : LinfStarBall) μ ν = -2 * I * omegaWPOrigin μ ν := by
  rw [h41, omegaWPOrigin]
  ring_nf
  rw [I_sq]
  ring

/-- Remark 4.3 from `S₂ = -(1/12π) S₁` on `T₀(1)` (Theorem 3.8) and Theorem 4.1 at `p`. -/
theorem s4g_remark_4_3 (h38 : ∀ p ∈ T01, liouvilleS2 p = -(1 / (12 * π)) * liouvilleS1 p) {p : T1} (hp : p ∈ T01)
    {μ ν : ℂ → ℂ} (hμ : μ ∈ harmonicL2 unitDiscExterior) (hν : ν ∈ harmonicL2 unitDiscExterior)
    (h41 : bersDzDzbar liouvilleS1 (Quotient.out p : LinfStarBall) μ ν = wpInner μ ν) :
    bersDzDzbar liouvilleS2 (Quotient.out p : LinfStarBall) μ ν = I / (6 * π) * omegaWPOrigin μ ν := by
  have hc : componentT (Phi (Quotient.out p : LinfStarBall)) = T01 := by
    have h1 : Phi (Quotient.out p : LinfStarBall) = p := Quotient.out_eq (s := teichSetoid) p
    rw [h1]
    exact (@connectedComponent_eq _ hilbertTopology _ _ hp).symm
  have he : bersDzDzbar liouvilleS2 (Quotient.out p : LinfStarBall) μ ν =
      bersDzDzbar (fun q => -(1 / (12 * π)) * liouvilleS1 q) (Quotient.out p : LinfStarBall) μ ν := by
    apply s4g_bersDzDzbar_congr
    filter_upwards [s4g_local_component hμ hν (Quotient.out p)] with e he
    rw [hc] at he
    exact h38 _ he.2
  rw [he, s4g_bersDzDzbar_const_mul, h41, omegaWPOrigin]
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.2 Real.pi_ne_zero
  push_cast
  field_simp
  ring_nf
  rw [I_sq]
  ring

/-- The Weil–Petersson potential on `T(1)` from Theorem 4.1 on `T₀(1)`: right translation by `[μ_α]⁻¹` maps the
Bers coordinates of `V_κ` to those of `V_{κ * μ_α⁻¹}`. -/
theorem s4g_wpPotential_spec {μ ν : ℂ → ℂ} (hμ : μ ∈ harmonicL2 unitDiscExterior)
    (hν : ν ∈ harmonicL2 unitDiscExterior)
    (h41 : ∀ q ∈ T01, bersDzDzbar liouvilleS1 (Quotient.out q : LinfStarBall) μ ν = wpInner μ ν) (p : T1) :
    bersDzDzbar wpPotential (Quotient.out p : LinfStarBall) μ ν = wpInner μ ν := by
  have hP : ∀ q : T1, Phi (Quotient.out q : LinfStarBall) = q := fun q => Quotient.out_eq (s := teichSetoid) q
  set κ : LinfStarBall := Quotient.out p with hκ
  set b := componentBase p with hb
  set β : LinfStarBall := Quotient.out (invT b) with hβ
  obtain ⟨-, hbase, hq0⟩ := s4c_componentBase_spec p
  set κ' : LinfStarBall := ⟨beltramiMul (κ : LinfStar) β, bg_mul_mem_ball β.2 κ.2⟩ with hκ'
  have hq0eq : Phi κ' = mulT p (invT b) := by
    have h := gtp_mulT_phi κ β
    rw [hκ, hP p, hβ, hP (invT b)] at h
    exact h.symm
  have hκ'q : Phi κ' = Phi (Quotient.out (mulT p (invT b)) : LinfStarBall) := by rw [hP, hq0eq]
  rw [← h41 _ hq0]
  apply s4g_bersDzDzbar_congr
  filter_upwards [s4g_local_component hμ hν κ] with e he
  obtain ⟨hl, hc⟩ := he
  rw [hκ, hP p] at hc
  set l := e.1 • toLinf μ + e.2 • toLinf ν with hldef
  have hx : beltramiMul l κ ∈ LinfStarBall := bg_mul_mem_ball κ.2 hl
  have hpt : ptT (beltramiMul l κ) = Phi ⟨_, hx⟩ := by unfold ptT; rw [dif_pos hx]
  have hcb : componentBase (ptT (beltramiMul l κ)) = b := hbase _ hc
  have hm : mulT (ptT (beltramiMul l κ)) (invT b) = ptT (beltramiMul l κ') := by
    rw [hpt, ← hP (invT b), ← hβ, gtp_mulT_phi]
    have hy : beltramiMul l κ' ∈ LinfStarBall := bg_mul_mem_ball κ'.2 hl
    unfold ptT
    rw [dif_pos hy]
    apply congrArg Phi
    apply Subtype.ext
    exact grp_mul_assoc hl κ.2 β.2
  show liouvilleS1 (mulT (ptT (beltramiMul l κ)) (invT (componentBase (ptT (beltramiMul l κ))))) = _
  rw [hcb, hm, s4g_ptT_congr hκ'q hl]

end Ch2
end TakhtajanTeo
