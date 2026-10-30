import TakhtajanTeo.Ch2.S3S1Tilde
import TakhtajanTeo.Ch2.S3FirstVariationCompleted
import TakhtajanTeo.Ch2.R43Potential
import TakhtajanTeo.Ch1.GroupL2Representatives
import TakhtajanTeo.Ch1.GroupTopology
import TakhtajanTeo.Ch1.Lemma29Plane

/-!
# W-CONST: constancy of `S₂ + S₁/12π` on `T₀(1)` (Program G, 下属6)

Host for Ch2 `thm_3_8` (TT:5162–5198), `cor_3_7` (TT:5156) and `cor_3_9` (TT:5200).
- `F = S₂ + S₁/12π` is real. Along every line `a + t μ` of harmonic Beltrami differentials at every point `a` of the
  small harmonic ball of a chart, `F` is ℝ-differentiable with `∂F = 0` (S₂: `s4g_S2_offcentre_variation`; S₁: the
  off-centre variation `s35_S1_offcentre_variation` of 下属4, entering here as the hypothesis `h35off`).
- So `F` is constant on segments of the chart ball, hence on the open chart image (`glr_chart_image_open`),
  hence locally constant on `T₀(1)`, hence constant on the connected component `T₀(1)`.
- `F(origin) = 0` gives `S₂ = -(1/12π) S₁`; `S̃₁ = S₁` (`s35_thm38_clauses`); `∂S₁` follows from `thm_3_1`.

No Fréchet regularity of `S₁` in chart coordinates is used.
-/

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal ComplexConjugate Classical Real

noncomputable section

namespace TakhtajanTeo

open LiZhongQC

namespace Ch2

/-- W0. Every `Λ ψ`, `ψ ∈ A₂(𝔻)`, is `toLinf m` for a harmonic `L²` Beltrami differential `m`
(`D0bers_harmonicL2`, `hp_eq_Lambda`, `wp_harmonicProj_fix`). -/
theorem s3wc_dir (ψ : A2 unitDisc) :
    ∃ m ∈ harmonicL2 unitDiscExterior, toLinf m = Lambda (A2toAInf ψ) := by
  have hmem : AInf.toFun (A2toAInf ψ) ∈ A2fun unitDisc := by
    have hr : A2toAInf ψ ∈ range A2toAInf := mem_range_self ψ
    rw [A2toAInf_range] at hr
    exact hr
  obtain ⟨m, hm, hmz⟩ := D0bers_harmonicL2.2 _ hmem
  have he : fderiv ℂ bersPhi 0 (toLinf m) = A2toAInf ψ := AInf.ext_toFun_disc fun z hz => hmz z hz
  refine ⟨m, hm, ?_⟩
  rw [← he, ← hp_eq_Lambda, wp_harmonicProj_fix hm]

/-- W1. Segments. If `F` is real with vanishing `∂` along harmonic lines at every point of the small harmonic ball,
then on the chart ball of radius `ε₁ = min √(π/3) (2δ₀/√(12/π))` the value `F([Λφ * κ])` equals `F([κ])`.
- The segment is `t ↦ Λ(t φ)`, `t ∈ [0,1]`. Every point of it satisfies `‖·‖ < δ₀` and `L²`-finiteness
  (`gtp_small_a`, `l29b_Lambda_L2`).
- At each `t₀` the hypothesis is applied re-based at `a = Λ(t₀ φ)` with direction `m`, `toLinf m = Λφ`
  (`s3wc_dir`). This gives `DifferentiableAt` at every `t₀` with zero real derivative.
- Constancy then follows from a real mean-value lemma on `[0,1]`. -/
theorem s3wc_seg_const {F : T1 → ℝ}
    (hoff : ∀ (κ : LinfStarBall), Phi κ ∈ T01 → ∀ a : LinfStar, a ∈ harmonicBeltrami → ‖a‖ < delta0 →
      normL2 unitDiscExterior a < ∞ → ∀ m : ℂ → ℂ, m ∈ harmonicL2 unitDiscExterior →
        DifferentiableAt ℝ (fun t : ℂ => (F (ptT (beltramiMul (a + t • toLinf m) κ)) : ℂ)) 0 ∧
          dz (fun t : ℂ => (F (ptT (beltramiMul (a + t • toLinf m) κ)) : ℂ)) 0 = 0)
    {κ : LinfStarBall} (hκ : Phi κ ∈ T01) {φ : A2 unitDisc}
    (hφ : ‖φ‖ < min (Real.sqrt (π / 3)) (2 * delta0 / Real.sqrt (12 / π))) :
    F (ptT (beltramiMul (Lambda (A2toAInf φ)) κ)) = F (Phi κ) := by
  set ε₁ : ℝ := min (Real.sqrt (π / 3)) (2 * delta0 / Real.sqrt (12 / π)) with hε₁
  have hz : Lambda (0 : AInf unitDisc) = 0 := by
    have := Lambda_smul 0 (0 : AInf unitDisc)
    simpa using this
  obtain ⟨m, hm, hmt⟩ := s3wc_dir φ
  set g : ℝ → ℝ := fun t => F (ptT (beltramiMul (Lambda (A2toAInf ((t : ℂ) • φ))) κ)) with hg
  have hD : ∀ t₀ ∈ Icc (0 : ℝ) 1, HasDerivAt g 0 t₀ := by
    intro t₀ ht₀
    have hsm : ‖(t₀ : ℂ) • φ‖ < ε₁ := by
      rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht₀.1]
      calc t₀ * ‖φ‖ ≤ 1 * ‖φ‖ := mul_le_mul_of_nonneg_right ht₀.2 (norm_nonneg _)
        _ = ‖φ‖ := one_mul _
        _ < ε₁ := hφ
    obtain ⟨-, ha, has, -⟩ := gtp_small_a hsm
    have haL : normL2 unitDiscExterior ⇑(Lambda (A2toAInf ((t₀ : ℂ) • φ))) < ∞ := by
      rw [l29b_Lambda_L2]
      exact ENNReal.mul_lt_top (by norm_num) ENNReal.coe_lt_top
    obtain ⟨hdiff, hdz⟩ := hoff κ hκ _ ha has haL m hm
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

/-- W2. Local constancy. Every `q ∈ T₀(1)` has a `hilbertTopology`-open neighbourhood on which `F` is constant:
the chart image of the `ε₁`-ball at a `groupO` representative of `q` (`r43p_groupO_rep`, `glr_chart_image_open`). -/
theorem s3wc_locconst {F : T1 → ℝ}
    (hoff : ∀ (κ : LinfStarBall), Phi κ ∈ T01 → ∀ a : LinfStar, a ∈ harmonicBeltrami → ‖a‖ < delta0 →
      normL2 unitDiscExterior a < ∞ → ∀ m : ℂ → ℂ, m ∈ harmonicL2 unitDiscExterior →
        DifferentiableAt ℝ (fun t : ℂ => (F (ptT (beltramiMul (a + t • toLinf m) κ)) : ℂ)) 0 ∧
          dz (fun t : ℂ => (F (ptT (beltramiMul (a + t • toLinf m) κ)) : ℂ)) 0 = 0)
    {q : T1} (hq : q ∈ T01) :
    ∃ U : Set T1, @IsOpen T1 hilbertTopology U ∧ q ∈ U ∧ ∀ q' ∈ U, F q' = F q := by
  set ε₁ : ℝ := min (Real.sqrt (π / 3)) (2 * delta0 / Real.sqrt (12 / π)) with hε₁
  have hd := delta0_bounds
  have hε₁0 : 0 < ε₁ := lt_min (by positivity) (div_pos (by linarith [hd.1]) (Real.sqrt_pos.2 (by positivity)))
  have hz : Lambda (0 : AInf unitDisc) = 0 := by
    have := Lambda_smul 0 (0 : AInf unitDisc)
    simpa using this
  obtain ⟨κ, hκO, hqκ⟩ := r43p_groupO_rep q
  have hκT : Phi κ ∈ T01 := hqκ ▸ hq
  refine ⟨(fun φ => bersChartInv κ (A2toAInf φ)) '' ball 0 ε₁,
    glr_chart_image_open hκO isOpen_ball (ball_subset_ball (min_le_left _ _)), ?_, ?_⟩
  · refine ⟨0, mem_ball_self hε₁0, ?_⟩
    show bersChartInv κ (A2toAInf 0) = q
    rw [A2toAInf_zero, ct_bersChartInv_eq (by simp), bt_rightTrans_phi, hqκ]
    exact congrArg Phi (Subtype.ext (by simp only [hz, hb_zero_mul κ.2]))
  · rintro q' ⟨φ, hφ, rfl⟩
    have hφ' : ‖φ‖ < ε₁ := mem_ball_zero_iff.mp hφ
    obtain ⟨hn, -, -, -⟩ := gtp_small_a hφ'
    have hm : beltramiMul (Lambda (A2toAInf φ)) κ ∈ LinfStarBall := bg_mul_mem_ball κ.2 (Lambda_mem_ball hn)
    have hpt : bersChartInv κ (A2toAInf φ) = ptT (beltramiMul (Lambda (A2toAInf φ)) κ) := by
      rw [ct_bersChartInv_eq hn, bt_rightTrans_phi]
      unfold ptT
      rw [dif_pos hm]
    show F (bersChartInv κ (A2toAInf φ)) = F q
    rw [hpt, s3wc_seg_const hoff hκT hφ', hqκ]

/-- W3. **The W-CONST engine.** `F` is constant on the connected component `T₀(1)` of `hilbertTopology`. -/
theorem s3wc_const {F : T1 → ℝ}
    (hoff : ∀ (κ : LinfStarBall), Phi κ ∈ T01 → ∀ a : LinfStar, a ∈ harmonicBeltrami → ‖a‖ < delta0 →
      normL2 unitDiscExterior a < ∞ → ∀ m : ℂ → ℂ, m ∈ harmonicL2 unitDiscExterior →
        DifferentiableAt ℝ (fun t : ℂ => (F (ptT (beltramiMul (a + t • toLinf m) κ)) : ℂ)) 0 ∧
          dz (fun t : ℂ => (F (ptT (beltramiMul (a + t • toLinf m) κ)) : ℂ)) 0 = 0) :
    ∀ p ∈ T01, F p = F originT := by
  letI : TopologicalSpace T1 := hilbertTopology
  set c := F originT with hc
  have hpre : IsPreconnected T01 := isPreconnected_connectedComponent
  have h0 : originT ∈ T01 := mem_connectedComponent
  set U : Set T1 := {x | ∃ W : Set T1, IsOpen W ∧ x ∈ W ∧ ∀ y ∈ W, F y = c} with hU
  set V : Set T1 := {x | ∃ W : Set T1, IsOpen W ∧ x ∈ W ∧ ∀ y ∈ W, F y ≠ c} with hV
  have hUo : IsOpen U := by
    refine isOpen_iff_forall_mem_open.2 fun x hx => ?_
    obtain ⟨W, hW, hxW, hWc⟩ := hx
    exact ⟨W, fun y hy => ⟨W, hW, hy, hWc⟩, hW, hxW⟩
  have hVo : IsOpen V := by
    refine isOpen_iff_forall_mem_open.2 fun x hx => ?_
    obtain ⟨W, hW, hxW, hWc⟩ := hx
    exact ⟨W, fun y hy => ⟨W, hW, hy, hWc⟩, hW, hxW⟩
  have hcov : T01 ⊆ U ∪ V := fun x hx => by
    obtain ⟨W, hW, hxW, hWc⟩ := s3wc_locconst hoff hx
    by_cases hxc : F x = c
    · exact Or.inl ⟨W, hW, hxW, fun y hy => (hWc y hy).trans hxc⟩
    · exact Or.inr ⟨W, hW, hxW, fun y hy => (hWc y hy).trans_ne hxc⟩
  have h0U : originT ∈ U := by
    obtain ⟨W, hW, hxW, hWc⟩ := s3wc_locconst hoff h0
    exact ⟨W, hW, hxW, hWc⟩
  intro p hp
  by_contra hpc
  have hpV : p ∈ V := by
    rcases hcov hp with ⟨W, -, hpW, hWc⟩ | hV'
    · exact absurd (hWc p hpW) hpc
    · exact hV'
  obtain ⟨x, -, ⟨W₁, -, hxW₁, hW₁⟩, ⟨W₂, -, hxW₂, hW₂⟩⟩ := hpre U V hUo hVo hcov ⟨originT, h0, h0U⟩ ⟨p, hp, hpV⟩
  exact hW₂ x hxW₂ (hW₁ x hxW₁)

/-- At the origin `𝗀^0 = id` on `𝔻*` (`gMu_sphere_factorization`, `w_0 = id`, `w^0 = id`). -/
theorem s3wc_gsans_zero {z : ℂ} (hz : z ∈ unitDiscExterior) : gsans (0 : LinfStar) z = z := by
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
  have hinv : Function.invFun (id : ExtPlane → ExtPlane) = id :=
    funext fun w => Function.leftInverse_invFun Function.injective_id w
  have h1 := gMu_sphere_factorization h0 hz
  rw [grp_wAS_zero, hinv, hwB] at h1
  rw [e13_gsans_eq h0]
  exact OnePoint.coe_injective h1

/-- W4. `S₁(origin) = 0`. Class invariance of `S₁` reduces it to the identity pair `𝖿 = 𝗀 = id`:
`𝒜 = 0` and `𝗀'(∞) = 1`. -/
theorem s3wc_S1_origin : liouvilleS1 originT = 0 := by
  have h0 : (0 : LinfStar) ∈ LinfStarBall := by simp [LinfStarBall]
  set ν : LinfStarBall := Quotient.out originT with hν
  have he : Phi ν = Phi ⟨0, h0⟩ := Quotient.out_eq originT
  obtain ⟨hf, hg⟩ := s2c_class_pair (Quotient.exact he)
  have hEo : IsOpen unitDiscExterior := isOpen_lt continuous_const continuous_norm
  have hpf : ∀ z ∈ unitDisc, preSchwarzian (fsans (ν : LinfStar)) z = 0 := fun z hz => by
    have hev : fsans (ν : LinfStar) =ᶠ[𝓝 z] id := by
      filter_upwards [isOpen_ball.mem_nhds hz] with w hw
      rw [hf hw, gk_fsans_zero]
    unfold preSchwarzian
    rw [hev.deriv_eq, hev.deriv.deriv_eq]
    simp
  have hpg : ∀ z ∈ unitDiscExterior, preSchwarzian (gsans (ν : LinfStar)) z = 0 := fun z hz => by
    have hev : gsans (ν : LinfStar) =ᶠ[𝓝 z] id := by
      filter_upwards [hEo.mem_nhds hz] with w hw
      exact (hg hw).trans (s3wc_gsans_zero hw)
    unfold preSchwarzian
    rw [hev.deriv_eq, hev.deriv.deriv_eq]
    simp
  have hD : derivAtInfty (gsans (ν : LinfStar)) = 1 := by
    unfold derivAtInfty
    apply Filter.Tendsto.limUnder_eq
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [(isCompact_closedBall (0 : ℂ) 1).compl_mem_cocompact] with z hz
    have hz1 : z ∈ unitDiscExterior := by
      have : 1 < ‖z‖ := by simpa [Metric.mem_closedBall, dist_zero_right, not_le] using hz
      exact this
    have hz0 : z ≠ 0 := by
      intro h
      have h1 : (1 : ℝ) < ‖z‖ := hz1
      rw [h, norm_zero] at h1
      linarith
    rw [hg hz1, s3wc_gsans_zero hz1, div_self hz0]
  have I1 : (∫ z in unitDisc, ‖preSchwarzian (fsans (ν : LinfStar)) z‖ ^ 2) = 0 := by
    exact setIntegral_eq_zero_of_forall_eq_zero fun z hz => by simp [hpf z hz]
  have I2 : (∫ z in unitDiscExterior, ‖preSchwarzian (gsans (ν : LinfStar)) z‖ ^ 2) = 0 := by
    exact setIntegral_eq_zero_of_forall_eq_zero fun z hz => by simp [hpg z hz]
  show (∫ z in unitDisc, ‖preSchwarzian (fsans (ν : LinfStar)) z‖ ^ 2) +
    (∫ z in unitDiscExterior, ‖preSchwarzian (gsans (ν : LinfStar)) z‖ ^ 2) -
      4 * π * Real.log ‖derivAtInfty (gsans (ν : LinfStar))‖ = 0
  rw [I1, I2, hD]
  simp

/-- W5. `S₂(origin) = 0`. Class invariance of the Grunsky coefficients reduces it to `B₁ = 0`, so `det F = 1`. -/
theorem s3wc_S2_origin : liouvilleS2 originT = 0 := by
  have h0 : (0 : LinfStar) ∈ LinfStarBall := by simp [LinfStarBall]
  have h := s3fd_liouville_eq h0 (0 : s3tc_HS) (fun m n => by rw [k23_B1_origin]; simp)
  have hz : s3fd_logSeries (0 : s3tc_HS) = 0 := by
    unfold s3fd_logSeries s3fd_coeff
    simp
  rw [hz] at h
  exact h.symm

/-- W6. `F = S₂ + S₁/12π` satisfies the engine hypothesis. The `S₂` part is `s4g_S2_offcentre_variation`, the `S₁`
part is `h35off`, the integrands agree, and `-(1/6π) + 2/12π = 0`. -/
theorem s3wc_F_off
    (h35off : ∀ (κ : LinfStarBall), Phi κ ∈ T01 → ∀ a : LinfStar, a ∈ harmonicBeltrami → ‖a‖ < delta0 →
      normL2 unitDiscExterior a < ∞ → ∀ m : ℂ → ℂ, m ∈ harmonicL2 unitDiscExterior →
        DifferentiableAt ℝ (fun t : ℂ => (liouvilleS1 (ptT (beltramiMul (a + t • toLinf m) κ)) : ℂ)) 0 ∧
          dz (fun t : ℂ => (liouvilleS1 (ptT (beltramiMul (a + t • toLinf m) κ)) : ℂ)) 0 =
            2 * ∫ z in unitDiscExterior, schwarzianHol (gsans (beltramiMul a κ)) z * RnmFun (toLinf m) a z) :
    ∀ (κ : LinfStarBall), Phi κ ∈ T01 → ∀ a : LinfStar, a ∈ harmonicBeltrami → ‖a‖ < delta0 →
      normL2 unitDiscExterior a < ∞ → ∀ m : ℂ → ℂ, m ∈ harmonicL2 unitDiscExterior →
        DifferentiableAt ℝ (fun t : ℂ => (((fun p => liouvilleS2 p + 1 / (12 * π) * liouvilleS1 p)
          (ptT (beltramiMul (a + t • toLinf m) κ)) : ℝ) : ℂ)) 0 ∧
          dz (fun t : ℂ => (((fun p => liouvilleS2 p + 1 / (12 * π) * liouvilleS1 p)
            (ptT (beltramiMul (a + t • toLinf m) κ)) : ℝ) : ℂ)) 0 = 0 := by
  intro κ hκ a ha has haL m hm
  obtain ⟨hD2, hV2⟩ := s4g_S2_offcentre_variation hκ ha has haL hm
  obtain ⟨hD1, hV1⟩ := h35off κ hκ a ha has haL m hm
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

/-- **Theorem 3.8** (TT:5162–5198), from the off-centre variation of `S₁`. Same statement as Ch2 `thm_3_8`. -/
theorem s3wc_thm_3_8
    (h35off : ∀ (κ : LinfStarBall), Phi κ ∈ T01 → ∀ a : LinfStar, a ∈ harmonicBeltrami → ‖a‖ < delta0 →
      normL2 unitDiscExterior a < ∞ → ∀ m : ℂ → ℂ, m ∈ harmonicL2 unitDiscExterior →
        DifferentiableAt ℝ (fun t : ℂ => (liouvilleS1 (ptT (beltramiMul (a + t • toLinf m) κ)) : ℂ)) 0 ∧
          dz (fun t : ℂ => (liouvilleS1 (ptT (beltramiMul (a + t • toLinf m) κ)) : ℂ)) 0 =
            2 * ∫ z in unitDiscExterior, schwarzianHol (gsans (beltramiMul a κ)) z * RnmFun (toLinf m) a z) :
    (∀ p ∈ T01, liouvilleS2 p = -(1 / (12 * π)) * liouvilleS1 p) ∧
      (∀ p ∈ T01, liouvilleS2 p = -(1 / (12 * π)) * liouvilleS1Tilde p) ∧
      ∀ p ∈ T01, ∀ μ ∈ harmonicL2 unitDiscExterior,
        BersDiffAt liouvilleS1 (Quotient.out p : LinfStarBall) μ ∧
          bersDz liouvilleS1 (Quotient.out p : LinfStarBall) μ =
            2 * ∫ z in unitDiscExterior, schwarzianHol (gsans (Quotient.out p : LinfStarBall)) z * μ z := by
  have hF := s3wc_const (F := fun p => liouvilleS2 p + 1 / (12 * π) * liouvilleS1 p) (s3wc_F_off h35off)
  have hπ : (π : ℝ) ≠ 0 := Real.pi_ne_zero
  have h1 : ∀ p ∈ T01, liouvilleS2 p = -(1 / (12 * π)) * liouvilleS1 p := by
    intro p hp
    have h := hF p hp
    simp only [s3wc_S1_origin, s3wc_S2_origin, mul_zero, add_zero] at h
    linarith
  refine ⟨h1, s35_thm38_clauses.mp h1, ?_⟩
  intro p hp μ hμ
  set ν : LinfStar := ((Quotient.out p : LinfStarBall) : LinfStar) with hνdef
  have hν : ν ∈ LinfStarBall := (Quotient.out p).2
  have hνT : Phi ⟨ν, hν⟩ ∈ T01 := by
    rw [show Phi ⟨ν, hν⟩ = p from Quotient.out_eq p]
    exact hp
  have h31 := TakhtajanTeo.Ch2.thm_3_1 hp hμ
  obtain ⟨hD2, hV2⟩ := h31
  have h0 : normL2 unitDiscExterior ⇑(0 : LinfStar) = 0 := by
    unfold normL2
    rw [lintegral_congr_ae (g := fun _ => 0) ?_, lintegral_zero, ENNReal.zero_rpow_of_pos (by norm_num)]
    filter_upwards [Lp.coeFn_zero ℂ ∞ (volume.restrict unitDiscExterior)] with z hz
    rw [hz]
    simp
  have hsmall : ∀ᶠ e : ℂ in 𝓝 0, ‖e‖ * ‖toLinf μ‖ < 1 ∧ ‖e‖ ≤ 1 := by
    refine ((continuous_norm.mul continuous_const).continuousAt.eventually_lt continuousAt_const
      (by simp)).and ?_
    exact (continuous_norm.continuousAt.eventually_lt continuousAt_const (by simp)).mono fun e he => he.le
  have hev : (fun e : ℂ => liouvilleS1 (ptT (beltramiMul (e • toLinf μ) ν))) =ᶠ[𝓝 (0 : ℂ)]
      fun e : ℂ => -(12 * π) * liouvilleS2 (ptT (beltramiMul (e • toLinf μ) ν)) := by
    filter_upwards [hsmall] with e he
    have hball : e • toLinf μ ∈ LinfStarBall := by
      rw [LinfStarBall, mem_ball_zero_iff, norm_smul]
      exact he.1
    have hL : normL2 unitDiscExterior ⇑(e • toLinf μ) < ∞ := by
      have h := s4g_normL2_line 0 hμ he.2
      rw [zero_add, h0, zero_add] at h
      exact h.trans_lt hμ.choose_spec.2.2
    have hmem := bg_mul_mem_ball hν hball
    have hT := s4g_T01_mul hν hνT hball hL
    have h2 := h1 _ hT
    rw [ptT, dif_pos hmem, h2, ← mul_assoc, neg_mul_neg, mul_one_div_cancel (by positivity), one_mul]
  have hD1 : BersDiffAt liouvilleS1 ν μ := by
    unfold BersDiffAt at hD2 ⊢
    exact (hD2.const_mul (-(12 * π))).congr_of_eventuallyEq hev
  refine ⟨hD1, ?_⟩
  unfold BersDiffAt at hD2
  have hD2c : DifferentiableAt ℝ (fun e : ℂ => ((liouvilleS2 (ptT (beltramiMul (e • toLinf μ) ν)) : ℝ) : ℂ)) 0 :=
    Complex.ofRealCLM.differentiableAt.comp (0 : ℂ) hD2
  have hevc : (fun e : ℂ => ((liouvilleS1 (ptT (beltramiMul (e • toLinf μ) ν)) : ℝ) : ℂ)) =ᶠ[𝓝 (0 : ℂ)]
      fun e : ℂ => (-(12 * π) : ℂ) * ((liouvilleS2 (ptT (beltramiMul (e • toLinf μ) ν)) : ℝ) : ℂ) := by
    filter_upwards [hev] with e he
    exact_mod_cast congrArg (fun x : ℝ => (x : ℂ)) he
  unfold bersDz at hV2 ⊢
  unfold dz at hV2 ⊢
  rw [hevc.fderiv_eq, fderiv_const_mul hD2c]
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
  have hπc : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hk : (-(12 * (π : ℂ))) * (-(1 / (6 * (π : ℂ))) *
      ∫ z in unitDiscExterior, schwarzianHol (gsans ν) z * μ z) =
      2 * ∫ z in unitDiscExterior, schwarzianHol (gsans ν) z * μ z := by
    field_simp
    ring
  linear_combination (-(12 * (π : ℂ))) * hV2 + hk

/-- **Corollary 3.7** (TT:5156) from the second clause of Theorem 3.5. -/
theorem s3wc_cor_3_7 {p : T1} {μ : ℂ → ℂ}
    (h : bersDz liouvilleS1Tilde (Quotient.out p : LinfStarBall) μ =
      2 * ∫ z in unitDiscExterior, schwarzianHol (gsans (Quotient.out p : LinfStarBall)) z * μ z) :
    bersDz liouvilleS1Tilde (Quotient.out p : LinfStarBall) μ = 2 * varthetaPair p μ := by
  unfold varthetaPair vartheta
  exact h

/-- **Corollary 3.9** (TT:5200) from the third clause of Theorem 3.8. -/
theorem s3wc_cor_3_9 {p : T1} {μ : ℂ → ℂ}
    (h : bersDz liouvilleS1 (Quotient.out p : LinfStarBall) μ =
      2 * ∫ z in unitDiscExterior, schwarzianHol (gsans (Quotient.out p : LinfStarBall)) z * μ z) :
    bersDz liouvilleS1 (Quotient.out p : LinfStarBall) μ = 2 * varthetaPair p μ := by
  unfold varthetaPair vartheta
  exact h

end Ch2

end TakhtajanTeo
