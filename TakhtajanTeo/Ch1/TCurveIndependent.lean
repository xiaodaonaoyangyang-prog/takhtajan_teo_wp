import TakhtajanTeo.Ch1.TCurve

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal NNReal ComplexConjugate Classical Real
noncomputable section
namespace TakhtajanTeo
open LiZhongQC


/-- A sense-preserving circle homeomorphism is onto the circle. -/
theorem tmi_circle_surj {h : ℂ → ℂ} (hh : Pommerenke1992.IsSensePreservingCircleHomeo h) {y : ℂ}
    (hy : ‖y‖ = 1) : ∃ z : ℂ, ‖z‖ = 1 ∧ h z = y := by
  obtain ⟨u, hc, hm, hper, hu⟩ := hh
  obtain ⟨s, rfl⟩ := (Complex.norm_eq_one_iff y).1 hy
  have hper' : ∀ n : ℕ, ∀ t, u (t + n * (2 * π)) = u t + n * (2 * π) := by
    intro n
    induction n with
    | zero => intro t; simp
    | succ n ih =>
      intro t
      have : t + ((n + 1 : ℕ) : ℝ) * (2 * π) = (t + n * (2 * π)) + 2 * π := by push_cast; ring
      rw [this, hper, ih]
      push_cast
      ring
  have hper'' : ∀ n : ℕ, ∀ t, u (t - n * (2 * π)) = u t - n * (2 * π) := by
    intro n t
    have := hper' n (t - n * (2 * π))
    rw [sub_add_cancel] at this
    linarith
  have htop : Tendsto u atTop atTop := by
    refine tendsto_atTop_atTop_of_monotone hm.monotone fun b => ?_
    obtain ⟨n, hn⟩ := exists_nat_ge ((b - u 0) / (2 * π))
    refine ⟨0 + n * (2 * π), ?_⟩
    rw [hper']
    have h2 : 0 < 2 * π := by positivity
    have := (div_le_iff₀ h2).1 hn
    linarith
  have hbot : Tendsto u atBot atBot := by
    refine tendsto_atBot_atBot_of_monotone hm.monotone fun b => ?_
    obtain ⟨n, hn⟩ := exists_nat_ge ((u 0 - b) / (2 * π))
    refine ⟨0 - n * (2 * π), ?_⟩
    rw [hper'']
    have h2 : 0 < 2 * π := by positivity
    have := (div_le_iff₀ h2).1 hn
    linarith
  obtain ⟨t, ht⟩ := hc.surjective htop hbot s
  refine ⟨exp (t * I), by simp [norm_exp], ?_⟩
  rw [hu t, ht]

/-- `σ_w` maps the circle into the circle (finite parameter). -/
theorem tmi_sigmaW_norm {w z : ℂ} (hw : 1 < ‖w‖) (hz : ‖z‖ = 1) : ‖sigmaW w z‖ = 1 := by
  have hw1 : w ≠ 1 := by rintro rfl; simp at hw
  have hc : 1 - conj w ≠ 0 := by
    intro he
    apply hw1
    simpa using congrArg (starRingEnd ℂ) (sub_eq_zero.mp he).symm
  have hzw : z - w ≠ 0 := by
    intro he
    have : z = w := sub_eq_zero.1 he
    rw [this] at hz
    linarith
  have hzz : z * conj z = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hz]; norm_num
  have h1 : (1 : ℂ) - z * conj w = z * conj (z - w) := by
    rw [map_sub, mul_sub, hzz]
  have hn1 : ‖(1 : ℂ) - w‖ = ‖(1 : ℂ) - conj w‖ := by
    rw [← Complex.norm_conj ((1 : ℂ) - w)]
    simp
  have hn2 : ‖(1 : ℂ) - z * conj w‖ = ‖z - w‖ := by
    rw [h1, norm_mul, hz, one_mul, Complex.norm_conj]
  unfold sigmaW
  rw [norm_mul, norm_div, norm_div, hn1, hn2, div_self (norm_ne_zero_iff.2 hc), div_self (norm_ne_zero_iff.2 hzw),
    mul_one]

/-- `σ_w` is onto the circle: explicit preimage. -/
theorem tmi_sigmaW_surj {w y : ℂ} (hw : 1 < ‖w‖) (hy : ‖y‖ = 1) :
    ∃ z : ℂ, ‖z‖ = 1 ∧ sigmaW w z = y := by
  have hw1 : w ≠ 1 := by rintro rfl; simp at hw
  have hc : 1 - conj w ≠ 0 := by
    intro he
    apply hw1
    simpa using congrArg (starRingEnd ℂ) (sub_eq_zero.mp he).symm
  have hc1 : 1 - w ≠ 0 := sub_ne_zero.2 (Ne.symm hw1)
  set k : ℂ := (1 - w) / (1 - conj w) with hk
  have hkn : ‖k‖ = 1 := by
    rw [hk, norm_div]
    have : ‖(1 : ℂ) - w‖ = ‖(1 : ℂ) - conj w‖ := by
      rw [← Complex.norm_conj ((1 : ℂ) - w)]; simp
    rw [this, div_self (norm_ne_zero_iff.2 hc)]
  have hkk : k * conj k = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hkn]; norm_num
  have hden : y + k * conj w ≠ 0 := by
    intro he
    have : ‖y‖ = ‖k * conj w‖ := by
      have : y = -(k * conj w) := by linear_combination he
      rw [this, norm_neg]
    rw [norm_mul, hkn, Complex.norm_conj, one_mul, hy] at this
    linarith
  refine ⟨(k + y * w) / (y + k * conj w), ?_, ?_⟩
  · rw [norm_div]
    rw [div_eq_one_iff_eq (norm_ne_zero_iff.2 hden)]
    have e : k + y * w = y * k * (conj y + w * conj k) := by
      have hyy : y * conj y = 1 := by
        rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hy]; norm_num
      linear_combination (-(k)) * hyy + (-(y * w)) * hkk
    have e2 : ‖conj y + w * conj k‖ = ‖y + k * conj w‖ := by
      rw [← Complex.norm_conj (conj y + w * conj k)]
      simp [mul_comm]
    rw [e, norm_mul, norm_mul, hy, hkn, e2]
    ring
  · have hww : 1 - w * conj w ≠ 0 := by
      intro he
      have h1 : w * conj w = 1 := by linear_combination -he
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq] at h1
      have h2 : ‖w‖ ^ 2 = 1 := by exact_mod_cast h1
      nlinarith
    have hk0 : k ≠ 0 := by
      intro h0; rw [h0, norm_zero] at hkn; exact zero_ne_one hkn
    unfold sigmaW
    rw [← hk]
    have e1 : 1 - (k + y * w) / (y + k * conj w) * conj w = y * (1 - w * conj w) / (y + k * conj w) := by
      field_simp
      ring
    have e2 : (k + y * w) / (y + k * conj w) - w = k * (1 - w * conj w) / (y + k * conj w) := by
      field_simp
      ring
    rw [e1, e2]
    field_simp

/-- The boundary map `finPart (σ_u ∘ γ_μ)` maps the circle onto the circle. -/
theorem tmi_boundary {μ : LinfStar} (hμ : μ ∈ LinfStarBall) {u : ExtPlane} (hu : u ∈ extDiscExterior) :
    (∀ z : ℂ, ‖z‖ = 1 → ‖finPart (sigmaSphere u (gammaMu μ z))‖ = 1) ∧
      ∀ y : ℂ, ‖y‖ = 1 → ∃ z : ℂ, ‖z‖ = 1 ∧ finPart (sigmaSphere u (gammaMu μ z)) = y := by
  have hsp := wA_circle_sensePreserving hμ
  induction u using OnePoint.rec with
  | infty =>
    refine ⟨fun z hz => ?_, fun y hy => ?_⟩
    · obtain ⟨hg, hn⟩ := tce_gamma_circle hμ hz
      have : sigmaSphere extInf (gammaMu μ z) = ((wA μ z : ℂ) : ExtPlane) := hg
      rw [this]
      exact hn
    · obtain ⟨z, hz, hzy⟩ := tmi_circle_surj hsp hy
      refine ⟨z, hz, ?_⟩
      obtain ⟨hg, -⟩ := tce_gamma_circle hμ hz
      have : sigmaSphere extInf (gammaMu μ z) = ((wA μ z : ℂ) : ExtPlane) := hg
      rw [this]
      exact hzy
  | coe w =>
    have hw' : w ∈ unitDiscExterior := by simpa [extDiscExterior, toExt] using hu
    have hw1 : 1 < ‖w‖ := hw'
    refine ⟨fun z hz => ?_, fun y hy => ?_⟩
    · obtain ⟨hg, hn⟩ := tce_gamma_circle hμ hz
      have hne : wA μ z ≠ w := by
        intro h; rw [h] at hn; linarith
      rw [hg, sigmaSphere_coe_eq hw' hne]
      exact tmi_sigmaW_norm hw1 hn
    · obtain ⟨z', hz', hz'y⟩ := tmi_sigmaW_surj hw1 hy
      obtain ⟨z, hz, hzz⟩ := tmi_circle_surj hsp hz'
      refine ⟨z, hz, ?_⟩
      obtain ⟨hg, -⟩ := tce_gamma_circle hμ hz
      have hne : wA μ z ≠ w := by
        intro h; rw [h] at hzz; rw [← hzz] at hz'; linarith
      rw [hg, sigmaSphere_coe_eq hw' hne, hzz]
      exact hz'y

/-- A plane q.c. homeomorphism with circle-onto-circle boundary values maps `𝔻*` onto `𝔻*`. -/
theorem tmi_G_regions {G : ℂ → ℂ} {K : ℝ} (hK : IsKQC G univ K) (hs : G '' univ = univ)
    (hc : G '' sphere (0 : ℂ) 1 = sphere (0 : ℂ) 1) :
    ∃ e : ℂ ≃ₜ ℂ, ⇑e = G ∧ G '' unitDiscExterior = unitDiscExterior ∧ G '' unitDisc = unitDisc ∧
      G '' closedBall (0 : ℂ) 1 = closedBall (0 : ℂ) 1 := by
  obtain ⟨e, rfl⟩ := t1_homeomorph hK hs
  obtain ⟨h1, h2, h3⟩ := planeHomeomorph_circle_regions e hc
  exact ⟨e, rfl, h3, h2, h1⟩




/-- a.e. statements on `𝔻*` pull back through the inverse of a plane q.c. homeomorphism preserving `𝔻*`. -/
theorem tmi_ae_pull_inv {G : ℂ → ℂ} {K : ℝ} (hK : IsKQC G univ K) (hs : G '' univ = univ)
    (hD : G '' unitDiscExterior = unitDiscExterior) {P : ℂ → Prop}
    (h : ∀ᵐ z ∂(volume.restrict unitDiscExterior), P z) :
    ∀ᵐ w ∂(volume.restrict unitDiscExterior), P (Function.invFun G w) := by
  have hE : MeasurableSet unitDiscExterior := bc_hEo.measurableSet
  rw [ae_restrict_iff' hE] at h ⊢
  rw [ae_iff] at h ⊢
  have hinj : Function.Injective G := fun a b hab => hK.2.2.1.2.1 (mem_univ a) (mem_univ b) hab
  have hsurj : Function.Surjective G := fun y => by
    have : y ∈ G '' univ := by rw [hs]; exact mem_univ y
    obtain ⟨x, -, hx⟩ := this
    exact ⟨x, hx⟩
  have hsub : {w | ¬(w ∈ unitDiscExterior → P (Function.invFun G w))} ⊆
      G '' {z | ¬(z ∈ unitDiscExterior → P z)} := by
    intro w hw
    simp only [mem_setOf_eq, not_imp] at hw
    obtain ⟨hwE, hwP⟩ := hw
    have hinv : G (Function.invFun G w) = w := Function.invFun_eq (hsurj w)
    refine ⟨Function.invFun G w, ?_, hinv⟩
    simp only [mem_setOf_eq, not_imp]
    refine ⟨?_, hwP⟩
    have : w ∈ G '' unitDiscExterior := by rw [hD]; exact hwE
    obtain ⟨z0, hz0, hz0w⟩ := this
    have : Function.invFun G w = z0 := hinj (hinv.trans hz0w.symm)
    rw [this]
    exact hz0
  exact measure_mono_null hsub (thm9_6_cor1_null hK (subset_univ _) h)

/-- a.e. statements on `𝔻*` pull back through a plane q.c. homeomorphism preserving `𝔻*`. -/
theorem tmi_ae_pull {G : ℂ → ℂ} {K : ℝ} (hK : IsKQC G univ K) (hs : G '' univ = univ)
    (hD : G '' unitDiscExterior = unitDiscExterior) {P : ℂ → Prop}
    (h : ∀ᵐ w ∂(volume.restrict unitDiscExterior), P w) :
    ∀ᵐ z ∂(volume.restrict unitDiscExterior), P (G z) := by
  have hE : MeasurableSet unitDiscExterior := bc_hEo.measurableSet
  rw [ae_restrict_iff' hE] at h ⊢
  rw [ae_iff] at h ⊢
  have hinj : InjOn G univ := hK.2.2.1.2.1
  have hleft : LeftInvOn (Function.invFunOn G univ) G univ := hinj.leftInvOn_invFunOn
  have hinv : IsKQC (Function.invFunOn G univ) univ K := by
    have := thm7_2_inv hK
    rwa [hs] at this
  have hsub : {z | ¬(z ∈ unitDiscExterior → P (G z))} ⊆
      Function.invFunOn G univ '' {w | ¬(w ∈ unitDiscExterior → P w)} := by
    intro z hz
    simp only [mem_setOf_eq, not_imp] at hz
    obtain ⟨hzE, hzP⟩ := hz
    refine ⟨G z, ?_, hleft (mem_univ z)⟩
    simp only [mem_setOf_eq, not_imp]
    refine ⟨?_, hzP⟩
    rw [← hD]
    exact mem_image_of_mem G hzE
  exact measure_mono_null hsub (thm9_6_cor1_null hinv (subset_univ _) h)

/-- The dilatation of `W ∘ G⁻¹` on `𝔻*`: the integrand of `tcurveLambda` (a.e.). -/
theorem tmi_dilatation_comp_inv {W G : ℂ → ℂ} {K₁ K₂ : ℝ} (hW : IsKQC W univ K₁) (hG : IsKQC G univ K₂)
    (hGs : G '' univ = univ) (hD : G '' unitDiscExterior = unitDiscExterior) {ν : ℂ → ℂ}
    (hν : ∀ᵐ z ∂(volume.restrict unitDiscExterior), complexDilatation W z = ν z) :
    ∀ᵐ w ∂(volume.restrict unitDiscExterior),
      complexDilatation (W ∘ Function.invFunOn G unitDiscExterior) w =
        (ν (Function.invFun G w) - complexDilatation G (Function.invFun G w)) /
            (1 - conj (complexDilatation G (Function.invFun G w)) * ν (Function.invFun G w)) *
          (dz G (Function.invFun G w) / conj (dz G (Function.invFun G w))) := by
  have hWD : IsKQC W unitDiscExterior K₁ := t3b_isKQC_restrict hW bc_hEo (subset_univ _)
  have hGD : IsKQC G unitDiscExterior K₂ := t3b_isKQC_restrict hG bc_hEo (subset_univ _)
  have h1 := ahQ_comp_inv_dilatation hWD hGD
  have h2 : ∀ᵐ z ∂(volume.restrict unitDiscExterior),
      complexDilatation (W ∘ Function.invFunOn G unitDiscExterior) (G z) =
        (ν z - complexDilatation G z) / (1 - conj (complexDilatation G z) * ν z) *
          (dz G z / conj (dz G z)) := by
    filter_upwards [h1, hν] with z hz hνz
    rw [hz, hνz]
  have h3 := tmi_ae_pull_inv hG hGs hD h2
  have hsurj : Function.Surjective G := fun y => by
    have : y ∈ G '' univ := by rw [hGs]; exact mem_univ y
    obtain ⟨x, -, hx⟩ := this
    exact ⟨x, hx⟩
  filter_upwards [h3] with w hw
  rwa [Function.invFun_eq (hsurj w)] at hw

/-- `tcurveLambda ν G` lies in the unit ball and agrees a.e. with its integrand. -/
theorem tmi_lambda_props {ν : LinfStar} (hν : ν ∈ LinfStarBall) {G : ℂ → ℂ} {K : ℝ} (hG : IsKQC G univ K)
    (hGs : G '' univ = univ) (hD : G '' unitDiscExterior = unitDiscExterior) :
    tcurveLambda ν G ∈ LinfStarBall ∧
      ∀ᵐ w ∂(volume.restrict unitDiscExterior),
        ((tcurveLambda ν G : LinfStar) : ℂ → ℂ) w =
          (ν (Function.invFun G w) - complexDilatation G (Function.invFun G w)) /
              (1 - conj (complexDilatation G (Function.invFun G w)) * ν (Function.invFun G w)) *
            (dz G (Function.invFun G w) / conj (dz G (Function.invFun G w))) := by
  obtain ⟨e, he⟩ := t1_homeomorph hG hGs
  have hGD : IsKQC G unitDiscExterior K := t3b_isKQC_restrict hG bc_hEo (subset_univ _)
  set F : ℂ → ℂ := fun u => (ν u - complexDilatation G u) / (1 - conj (complexDilatation G u) * ν u) *
    (dz G u / conj (dz G u)) with hF
  set f : ℂ → ℂ := fun w => F (Function.invFun G w) with hf
  have hν1 : ‖ν‖ < 1 := bc_norm_lt_one hν
  obtain ⟨hk0', hk1', hkb⟩ := c36_b_dilatation_bound hGD
  set k : ℝ := max ‖ν‖ ((K - 1) / (K + 1)) with hk
  have hk0 : 0 ≤ k := le_max_of_le_left (norm_nonneg _)
  have hk1 : k < 1 := max_lt hν1 hk1'
  set c : ℝ := 2 * k / (1 + k ^ 2) with hc
  have hc0 : 0 ≤ c := by positivity
  have hc1 : c < 1 := by
    rw [hc, div_lt_one (by positivity)]
    nlinarith [sq_nonneg (1 - k)]
  -- bound for the integrand
  have hFb : ∀ᵐ u ∂(volume.restrict unitDiscExterior), ‖F u‖ ≤ c := by
    filter_upwards [LinfStar_ae_norm_le ν, hkb, thm9_6_cor2_jacobian_pos hGD] with u h1 h2 h3
    have hdz : dz G u ≠ 0 := by
      intro h0
      unfold jacobian at h3
      rw [h0, norm_zero] at h3
      nlinarith [norm_nonneg (dzbar G u)]
    have hτ : ‖dz G u / conj (dz G u)‖ = 1 := by
      rw [norm_div, Complex.norm_conj, div_self (norm_ne_zero_iff.2 hdz)]
    rw [hF]
    simp only
    rw [norm_mul, hτ, mul_one]
    exact ahQ_pseudo_bound hk0 hk1 (h1.trans (le_max_left _ _)) (h2.trans (le_max_right _ _))
  have hfb : ∀ᵐ w ∂(volume.restrict unitDiscExterior), ‖f w‖ ≤ c :=
    tmi_ae_pull_inv hG hGs hD hFb
  -- measurability
  have hFm : AEMeasurable F (volume.restrict unitDiscExterior) := by
    have hν' : AEMeasurable (fun u => ν u) (volume.restrict unitDiscExterior) :=
      (Lp.aestronglyMeasurable ν).aemeasurable
    have hμ' : Measurable (complexDilatation G) := (measurable_dzbar G).div (measurable_dz G)
    have hc' : Measurable (fun u => conj (complexDilatation G u)) :=
      Complex.continuous_conj.measurable.comp hμ'
    have hd' : Measurable (fun u => conj (dz G u)) := Complex.continuous_conj.measurable.comp (measurable_dz G)
    exact ((hν'.sub hμ'.aemeasurable).div (aemeasurable_const.sub (hc'.aemeasurable.mul hν'))).mul
      ((measurable_dz G).aemeasurable.div hd'.aemeasurable)
  have hinvm : Measurable (Function.invFun G) := by
    subst he
    have : Function.invFun (⇑e) = ⇑e.symm := by
      funext y
      apply e.injective
      rw [e.apply_symm_apply]
      exact Function.invFun_eq (e.surjective y)
    rw [this]
    exact e.symm.continuous.measurable
  have hqmp : Measure.QuasiMeasurePreserving (Function.invFun G) (volume.restrict unitDiscExterior)
      (volume.restrict unitDiscExterior) := by
    refine ⟨hinvm, ?_⟩
    refine Measure.AbsolutelyContinuous.mk fun s hs hs0 => ?_
    rw [Measure.map_apply hinvm hs]
    have h : ∀ᵐ u ∂(volume.restrict unitDiscExterior), u ∉ s :=
      measure_eq_zero_iff_ae_notMem.mp hs0
    exact measure_eq_zero_iff_ae_notMem.mpr (tmi_ae_pull_inv hG hGs hD h)
  have hfm : AEStronglyMeasurable f (volume.restrict unitDiscExterior) :=
    (hFm.comp_quasiMeasurePreserving hqmp).aestronglyMeasurable
  have hmem : MemLp f ∞ (volume.restrict unitDiscExterior) := memLp_top_of_bound hfm c hfb
  refine ⟨?_, bc_toLinf_ae hmem⟩
  show tcurveLambda ν G ∈ ball (0 : LinfStar) 1
  rw [mem_ball_zero_iff]
  exact lt_of_le_of_lt (norm_toLinf_le_of_ae_bound hc0 hfb) hc1




/-- `sphere_circle_id` with the identity also on the exterior: a continuous sphere bijection preserving the complement of the closed disc,
conformal there (in the chart `1/z`), and fixing `-1, -i, 1`, is the identity on the circle. -/
theorem tmi_tail {Csph : ExtPlane → ExtPlane} (hCcont : Continuous Csph)
    (hCinj : Function.Injective Csph)
    (hCnot : ∀ p ∉ toExt (closedBall (0 : ℂ) 1), Csph p ∉ toExt (closedBall (0 : ℂ) 1))
    (hCsurj : ∀ p' ∉ toExt (closedBall (0 : ℂ) 1), ∃ p ∉ toExt (closedBall (0 : ℂ) 1), Csph p = p')
    (hdiff' : DifferentiableOn ℂ (fun w : ℂ =>
      finPart (mobiusExt 0 1 1 0 (Csph (mobiusExt 0 1 1 0 (w : ExtPlane))))) unitDisc)
    (hfix1 : Csph ((-1 : ℂ) : ExtPlane) = ((-1 : ℂ) : ExtPlane))
    (hfixI : Csph ((-I : ℂ) : ExtPlane) = ((-I : ℂ) : ExtPlane))
    (hfix2 : Csph ((1 : ℂ) : ExtPlane) = ((1 : ℂ) : ExtPlane)) :
    (∀ ζ : ℂ, ‖ζ‖ = 1 → Csph (ζ : ExtPlane) = (ζ : ExtPlane)) ∧
      ∀ p ∉ toExt (closedBall (0 : ℂ) 1), Csph p = p := by
  have hσc : Continuous (mobiusExt 0 1 1 0) := continuous_mobiusExt (by norm_num)
  have hσi : Function.Injective (mobiusExt 0 1 1 0) := fun a b h => by
    rw [← sigma_invol a, ← sigma_invol b, h]
  obtain ⟨c, hcdef⟩ : ∃ c : ℂ → ℂ, c = fun w : ℂ =>
      finPart (mobiusExt 0 1 1 0 (Csph (mobiusExt 0 1 1 0 (w : ExtPlane)))) := ⟨_, rfl⟩
  rw [← hcdef] at hdiff'
  have hc1 : ∀ w ∈ unitDisc, mobiusExt 0 1 1 0 (Csph (mobiusExt 0 1 1 0 (w : ExtPlane))) =
      ((c w : ℂ) : ExtPlane) ∧ c w ∈ unitDisc := by
    intro w hw
    obtain ⟨y, hy, hyD⟩ := sigma_of_not_closed (hCnot _ (sigma_not_closed hw))
    have hcy : c w = y := by
      rw [hcdef]
      show finPart (mobiusExt 0 1 1 0 (Csph _)) = y
      rw [hy]
      rfl
    exact ⟨by rw [hcy]; exact hy, hcy ▸ hyD⟩
  have hcinj : InjOn c unitDisc := by
    intro w1 hw1 w2 hw2 h
    have e1 := (hc1 w1 hw1).1
    have e2 := (hc1 w2 hw2).1
    rw [h] at e1
    have := hCinj (hσi (e1.trans e2.symm))
    exact OnePoint.coe_injective (hσi this)
  have hcsurj : c '' unitDisc = unitDisc := by
    apply Subset.antisymm
    · rintro _ ⟨w, hw, rfl⟩
      exact (hc1 w hw).2
    · intro y hy
      obtain ⟨p, hpn, hp⟩ := hCsurj _ (sigma_not_closed hy)
      obtain ⟨w, hwp, hwD⟩ := sigma_of_not_closed hpn
      refine ⟨w, hwD, ?_⟩
      have e := (hc1 w hwD).1
      rw [← hwp, sigma_invol, hp, sigma_invol] at e
      exact (OnePoint.coe_injective e).symm
  obtain ⟨A, B, C, D, hdet, heq⟩ :=
    exists_mobius_of_isConformalOnto_unitDisc ⟨hdiff', hcinj, hcsurj⟩
  have hmc : Continuous (mobiusExt A B C D) := continuous_mobiusExt hdet
  have hZ : {x : ℂ | C * x + D = 0}.Subsingleton := by
    intro x hx y hy
    have hx' : C * x + D = 0 := hx
    have hy' : C * y + D = 0 := hy
    by_cases hC : C = 0
    · exfalso
      rw [hC, zero_mul, zero_add] at hx'
      apply hdet
      rw [hC, hx']
      ring
    · have : C * (x - y) = 0 := by linear_combination hx' - hy'
      exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_left hC)
  have hZd : Dense ({x : ℂ | C * x + D = 0}ᶜ) := Set.Countable.dense_compl ℂ hZ.finite.countable
  have hagree : EqOn (fun p => mobiusExt 0 1 1 0 (Csph (mobiusExt 0 1 1 0 p))) (mobiusExt A B C D)
      (((↑) : ℂ → ExtPlane) '' (ball (0 : ℂ) 1 ∩ {x : ℂ | C * x + D = 0}ᶜ)) := by
    rintro _ ⟨w, ⟨hw, hwZ⟩, rfl⟩
    have hwD : w ∈ unitDisc := hw
    show mobiusExt 0 1 1 0 (Csph (mobiusExt 0 1 1 0 (w : ExtPlane))) = _
    rw [(hc1 w hwD).1, mobiusExt_coe hwZ, heq hwD]
  have hcl : EqOn (fun p => mobiusExt 0 1 1 0 (Csph (mobiusExt 0 1 1 0 p))) (mobiusExt A B C D)
      (closure (((↑) : ℂ → ExtPlane) '' (ball (0 : ℂ) 1 ∩ {x : ℂ | C * x + D = 0}ᶜ))) :=
    EqOn.closure hagree (hσc.comp (hCcont.comp hσc)) hmc
  have hcirc : ∀ ζ : ℂ, ‖ζ‖ = 1 → mobiusExt 0 1 1 0 (Csph (mobiusExt 0 1 1 0 (ζ : ExtPlane))) =
      mobiusExt A B C D (ζ : ExtPlane) := by
    intro ζ hζ
    apply hcl
    have h1 : ζ ∈ closure (ball (0 : ℂ) 1 ∩ {x : ℂ | C * x + D = 0}ᶜ) := by
      have hsub : ball (0 : ℂ) 1 ⊆ closure (ball (0 : ℂ) 1 ∩ {x : ℂ | C * x + D = 0}ᶜ) :=
        hZd.open_subset_closure_inter isOpen_ball
      have : closure (ball (0 : ℂ) 1) ⊆ closure (ball (0 : ℂ) 1 ∩ {x : ℂ | C * x + D = 0}ᶜ) :=
        closure_minimal hsub isClosed_closure
      apply this
      rw [closure_ball _ one_ne_zero]
      exact mem_closedBall_zero_iff.2 hζ.le
    exact (image_closure_subset_closure_image OnePoint.continuous_coe) ⟨ζ, h1, rfl⟩
  have hid : ∀ p, mobiusExt 1 0 0 1 p = p := by
    intro p
    induction p using OnePoint.rec with
    | infty => exact mobiusExt_infty_of_eq rfl
    | coe z =>
      rw [mobiusExt_coe (by simp)]
      congr 1
      simp [mobiusFn]
  have hI0 : (-I : ℂ) ≠ 0 := neg_ne_zero.2 Complex.I_ne_zero
  have hMid : mobiusExt A B C D = mobiusExt 1 0 0 1 := by
    refine mobius_eq_of_three_points (p₁ := -1) (p₂ := I) (p₃ := 1) ⟨A, B, C, D, hdet, rfl⟩
      ⟨1, 0, 0, 1, by norm_num, rfl⟩ ?_ ?_ ?_ ?_ ?_ ?_
    · intro h
      have := congrArg Complex.re h
      norm_num at this
    · norm_num
    · intro h
      have := congrArg Complex.re h
      norm_num at this
    · rw [← hcirc (-1) (by simp), sigma_coe (by norm_num), hid]
      have : ((-1 : ℂ)⁻¹) = -1 := by norm_num
      rw [this, hfix1, sigma_coe (by norm_num), this]
    · rw [← hcirc I (by simp), sigma_coe Complex.I_ne_zero, hid]
      have : (I : ℂ)⁻¹ = -I := by simp
      rw [this, hfixI, sigma_coe hI0]
      simp
    · rw [← hcirc 1 (by simp), sigma_coe one_ne_zero, hid]
      rw [inv_one, hfix2, sigma_coe one_ne_zero, inv_one]
  refine ⟨?_, ?_⟩
  · intro ζ hζ
    have hζ0 : ζ ≠ 0 := norm_ne_zero_iff.1 (by rw [hζ]; exact one_ne_zero)
    have h1 := hcirc ζ⁻¹ (by rw [norm_inv, hζ]; simp)
    rw [hMid, hid, sigma_coe (inv_ne_zero hζ0), inv_inv] at h1
    have h2 := congrArg (mobiusExt 0 1 1 0) h1
    rw [sigma_invol, sigma_coe (inv_ne_zero hζ0), inv_inv] at h2
    exact h2
  · intro p hp
    obtain ⟨y, hy, hyD⟩ := sigma_of_not_closed hp
    have hcy : c y = y := by
      have h1 := heq hyD
      have h2 : mobiusExt A B C D (y : ExtPlane) = (y : ExtPlane) := by rw [hMid, hid]
      by_cases hCy : C * y + D = 0
      · exfalso
        rw [mobiusExt_coe_of_eq_zero hCy] at h2
        exact OnePoint.infty_ne_coe _ h2
      · rw [mobiusExt_coe hCy] at h2
        rw [h1]
        exact OnePoint.coe_injective h2
    have hpσ : p = mobiusExt 0 1 1 0 (y : ExtPlane) := by rw [← hy, sigma_invol]
    have h3 := (hc1 y hyD).1
    rw [hcy, ← hpσ] at h3
    -- h3 : σ (Csph (σ y)) = y  with σ y = p
    apply hσi
    rw [h3, hy]





/-- Differentiability of the chart expression `c(w) = σ ∘ C ∘ σ` on the disc for `C = M₂ ∘ map R ∘ M₁`, `R`
holomorphic on `Ω` and `M₁` sending the exterior into `map Ω ∪ {∞}` (finite exceptional set, as in
`eq19_exists_mu`). -/
theorem tmi_hdiff {Csph M₁ M₂ : ExtPlane → ExtPlane} (hM₁ : IsMobius M₁) (hM₂ : IsMobius M₂) {R : ℂ → ℂ}
    {Ω : Set ℂ} (hΩ : IsOpen Ω) (hR : DifferentiableOn ℂ R Ω)
    (hCdef : ∀ p, Csph p = M₂ (OnePoint.map R (M₁ p)))
    (hmaps : ∀ p ∉ toExt (closedBall (0 : ℂ) 1), M₁ p = extInf ∨ ∃ x ∈ Ω, M₁ p = (x : ExtPlane))
    (hCcont : Continuous Csph) (hCinj : Function.Injective Csph)
    (hCnot : ∀ p ∉ toExt (closedBall (0 : ℂ) 1), Csph p ∉ toExt (closedBall (0 : ℂ) 1)) :
    DifferentiableOn ℂ (fun w : ℂ =>
      finPart (mobiusExt 0 1 1 0 (Csph (mobiusExt 0 1 1 0 (w : ExtPlane))))) unitDisc := by
  obtain ⟨a, b, c, d, hdet, rfl⟩ := hM₁
  obtain ⟨a', b', c', d', hdet', rfl⟩ := hM₂
  have hσi : Function.Injective (mobiusExt 0 1 1 0) := fun x y h => by
    rw [← sigma_invol x, ← sigma_invol y, h]
  have hM₁i : Function.Injective (mobiusExt a b c d) := (mobiusHomeomorph a b c d hdet).injective
  have hmap : ∀ x : ℂ, OnePoint.map R (x : ExtPlane) = ((R x : ℂ) : ExtPlane) := fun x => rfl
  obtain ⟨Ω0, hΩ0⟩ : ∃ Ω0 : Set ℂ, Ω0 = {w | w ∈ unitDisc ∧ w ≠ 0 ∧
      mobiusExt a b c d (mobiusExt 0 1 1 0 (w : ExtPlane)) ≠ extInf ∧
      Csph (mobiusExt 0 1 1 0 (w : ExtPlane)) ≠ extInf} := ⟨_, rfl⟩
  have hS1 : {w : ℂ | w ∈ unitDisc ∧ mobiusExt a b c d (mobiusExt 0 1 1 0 (w : ExtPlane)) = extInf}.Subsingleton := by
    intro w1 h1 w2 h2
    have := hσi (hM₁i (h1.2.trans h2.2.symm))
    exact OnePoint.coe_injective this
  have hS2 : {w : ℂ | w ∈ unitDisc ∧ Csph (mobiusExt 0 1 1 0 (w : ExtPlane)) = extInf}.Subsingleton := by
    intro w1 h1 w2 h2
    have := hσi (hCinj (h1.2.trans h2.2.symm))
    exact OnePoint.coe_injective this
  have hfin : (unitDisc \ Ω0).Finite := by
    refine ((Set.finite_singleton (0 : ℂ)).union (hS1.finite.union hS2.finite)).subset ?_
    intro w hw
    by_cases h0 : w = 0
    · exact Or.inl h0
    · refine Or.inr ?_
      by_cases hA : mobiusExt a b c d (mobiusExt 0 1 1 0 (w : ExtPlane)) = extInf
      · exact Or.inl ⟨hw.1, hA⟩
      · refine Or.inr ⟨hw.1, ?_⟩
        by_contra hB
        apply hw.2
        rw [hΩ0]
        exact ⟨hw.1, h0, hA, hB⟩
  refine differentiableOn_of_finite_exceptional (show IsOpen unitDisc from isOpen_ball) hfin ?_ ?_
  · exact sphere_c_continuousOn hCcont hCnot
  · set Gc : ℂ → ℂ := fun w => (mobiusFn a' b' c' d' (R (mobiusFn a b c d w⁻¹)))⁻¹ with hGc
    -- structure at a point of `Ω0`
    have key : ∀ w ∈ Ω0, ∃ x y : ℂ, w ≠ 0 ∧ c * w⁻¹ + d ≠ 0 ∧ x = mobiusFn a b c d w⁻¹ ∧ x ∈ Ω ∧
        c' * R x + d' ≠ 0 ∧ y = mobiusFn a' b' c' d' (R x) ∧ y ≠ 0 ∧
        finPart (mobiusExt 0 1 1 0 (Csph (mobiusExt 0 1 1 0 (w : ExtPlane)))) = y⁻¹ := by
      intro w hw
      rw [hΩ0] at hw
      obtain ⟨hwD, hw0, hA, hB⟩ := hw
      have hp : mobiusExt 0 1 1 0 (w : ExtPlane) ∉ toExt (closedBall (0 : ℂ) 1) := sigma_not_closed hwD
      have hσw : mobiusExt 0 1 1 0 (w : ExtPlane) = ((w⁻¹ : ℂ) : ExtPlane) := sigma_coe hw0
      rw [hσw] at hp hA hB ⊢
      have hden : c * w⁻¹ + d ≠ 0 := by
        intro h0
        exact hA (mobiusExt_coe_of_eq_zero h0)
      have hM1 : mobiusExt a b c d ((w⁻¹ : ℂ) : ExtPlane) = ((mobiusFn a b c d w⁻¹ : ℂ) : ExtPlane) :=
        mobiusExt_coe hden
      obtain ⟨x, hxΩ, hx⟩ : ∃ x ∈ Ω, mobiusFn a b c d w⁻¹ = x := by
        rcases hmaps _ hp with h | ⟨x, hx, h⟩
        · exact absurd h hA
        · refine ⟨x, hx, ?_⟩
          rw [hM1] at h
          exact OnePoint.coe_injective h
      have hC : Csph ((w⁻¹ : ℂ) : ExtPlane) = mobiusExt a' b' c' d' ((R x : ℂ) : ExtPlane) := by
        rw [hCdef, hM1, hx, hmap]
      rw [hC] at hB
      have hden' : c' * R x + d' ≠ 0 := by
        intro h0
        exact hB (mobiusExt_coe_of_eq_zero h0)
      have hM2 : mobiusExt a' b' c' d' ((R x : ℂ) : ExtPlane) = ((mobiusFn a' b' c' d' (R x) : ℂ) : ExtPlane) :=
        mobiusExt_coe hden'
      have hCnot' := hCnot _ hp
      rw [hC, hM2] at hCnot'
      have hy0 : mobiusFn a' b' c' d' (R x) ≠ 0 := by
        intro h0
        apply hCnot'
        rw [h0, coe_mem_toExt_iff]
        simp
      refine ⟨x, mobiusFn a' b' c' d' (R x), hw0, hden, hx.symm, hxΩ, hden', rfl, hy0, ?_⟩
      rw [hC, hM2, sigma_coe hy0]
      rfl
    have hdiffΩ0 : DifferentiableOn ℂ (fun w : ℂ =>
        finPart (mobiusExt 0 1 1 0 (Csph (mobiusExt 0 1 1 0 (w : ExtPlane))))) Ω0 := by
      refine DifferentiableOn.congr (f := Gc) (fun w hw => ?_) (fun w hw => ?_)
      · obtain ⟨x, y, hw0, hden, hx, hxΩ, hden', hy, hy0, -⟩ := key w hw
        have h1 : DifferentiableAt ℂ (fun w : ℂ => w⁻¹) w := differentiableAt_inv hw0
        have h2 : DifferentiableAt ℂ (mobiusFn a b c d) w⁻¹ :=
          (bc_mobiusFn_hasDerivAt hden).differentiableAt
        have h3 : DifferentiableAt ℂ R (mobiusFn a b c d w⁻¹) :=
          hR.differentiableAt (hΩ.mem_nhds (hx ▸ hxΩ))
        have h4 : DifferentiableAt ℂ (mobiusFn a' b' c' d') (R (mobiusFn a b c d w⁻¹)) := by
          rw [← hx]
          exact (bc_mobiusFn_hasDerivAt hden').differentiableAt
        have h5 : DifferentiableAt ℂ (fun t : ℂ => t⁻¹) (mobiusFn a' b' c' d' (R (mobiusFn a b c d w⁻¹))) := by
          refine differentiableAt_inv ?_
          rw [← hx, ← hy]
          exact hy0
        exact (h5.comp w (h4.comp w (h3.comp w (h2.comp w h1)))).differentiableWithinAt
      · obtain ⟨x, y, hw0, hden, hx, hxΩ, hden', hy, hy0, hfp⟩ := key w hw
        rw [hfp, hGc]
        simp only
        rw [← hx, ← hy]
    refine hdiffΩ0.mono ?_
    intro w hw
    by_contra h
    exact hw.2 ⟨hw.1, h⟩




/-- Basic data of an admissible extension `G`. -/
theorem tmi_G_data {μ : LinfStar} (hμ : μ ∈ LinfStarBall) {u : ExtPlane} (hu : u ∈ extDiscExterior)
    {G : ℂ → ℂ}
    (hG : IsQuasiconformal G univ ∧ G '' univ = univ ∧
      EqOn G (fun z : ℂ => finPart (sigmaSphere u (gammaMu μ z))) unitCircle) :
    ∃ (K : ℝ) (e : ℂ ≃ₜ ℂ), IsKQC G univ K ∧ ⇑e = G ∧ G '' unitDiscExterior = unitDiscExterior ∧
      G '' closedBall (0 : ℂ) 1 = closedBall (0 : ℂ) 1 ∧ G '' sphere (0 : ℂ) 1 = sphere (0 : ℂ) 1 := by
  obtain ⟨⟨K, hK⟩, hs, hb⟩ := hG
  obtain ⟨hn0, hsurj0⟩ := tmi_boundary hμ hu
  have hGc : G '' sphere (0 : ℂ) 1 = sphere (0 : ℂ) 1 := by
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      have hz1 : ‖z‖ = 1 := mem_sphere_zero_iff_norm.1 hz
      rw [mem_sphere_zero_iff_norm, hb (show z ∈ unitCircle from hz1)]
      exact hn0 z hz1
    · intro hy
      obtain ⟨z, hz, hzy⟩ := hsurj0 y (mem_sphere_zero_iff_norm.1 hy)
      exact ⟨z, mem_sphere_zero_iff_norm.2 hz, (hb (show z ∈ unitCircle from hz)).trans hzy⟩
  obtain ⟨e, he, h1, h2, h3⟩ := tmi_G_regions hK hs hGc
  exact ⟨K, e, hK, he, h1, h3, hGc⟩

/-- Conformal data of `wAS (tcurveLambda ν G)` relative to the Model B plane solution `W` of `ν`. -/
theorem tmi_conf_data {ν : LinfStar} (hν : ν ∈ LinfStarBall) {W : ℂ → ℂ} {KW : ℝ} (hW : IsKQC W univ KW)
    (hWae : ∀ᵐ z ∂(volume.restrict unitDiscExterior), complexDilatation W z = ν z)
    {G : ℂ → ℂ} {K : ℝ} (hG : IsKQC G univ K) (hGs : G '' univ = univ)
    (hD : G '' unitDiscExterior = unitDiscExterior) :
    ∃ (M : ExtPlane → ExtPlane) (W' : ℂ → ℂ) (K' : ℝ) (Ψ : ℂ → ℂ), IsMobius M ∧ IsKQC W' univ K' ∧
      W' '' univ = univ ∧
      (∀ z : ℂ, wAS (tcurveLambda ν G) (z : ExtPlane) = M ((W' z : ℂ) : ExtPlane)) ∧
      wAS (tcurveLambda ν G) extInf = M extInf ∧
      wAS (tcurveLambda ν G) ((-1 : ℂ) : ExtPlane) = ((-1 : ℂ) : ExtPlane) ∧
      wAS (tcurveLambda ν G) ((-I : ℂ) : ExtPlane) = ((-I : ℂ) : ExtPlane) ∧
      wAS (tcurveLambda ν G) ((1 : ℂ) : ExtPlane) = ((1 : ℂ) : ExtPlane) ∧
      IsConformalOnto Ψ (W '' unitDiscExterior) (W' '' unitDiscExterior) ∧
      ∀ y ∈ unitDiscExterior, Ψ (W y) = W' (G y) := by
  obtain ⟨hlam, hae⟩ := tmi_lambda_props hν hG hGs hD
  obtain ⟨M, hM, W', hW', hwf, hwi, hm1, hmI, hm2⟩ := wA_spec hlam
  obtain ⟨K', hK'⟩ := hW'.1
  have hGD : IsKQC G unitDiscExterior K := t3b_isKQC_restrict hG bc_hEo (subset_univ _)
  have hWD : IsKQC W unitDiscExterior KW := t3b_isKQC_restrict hW bc_hEo (subset_univ _)
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
    filter_upwards [ae_restrict_of_ae hW'.2.2.2.2, hae, tmi_dilatation_comp_inv hW hG hGs hD hWae,
      ae_restrict_mem bc_hEo.measurableSet] with z h1 h2 h3 hzE
    rw [h1, extA_eq_on_exterior _ hzE, h2, ← h3]
  have hconf := bg_conformal_of_dilatation_eq hh hW'D hdil
  have himg : (W ∘ Function.invFunOn G unitDiscExterior) '' unitDiscExterior = W '' unitDiscExterior := by
    rw [image_comp, hinvimg]
  rw [himg] at hconf
  refine ⟨M, W', K', W' ∘ Function.invFunOn (W ∘ Function.invFunOn G unitDiscExterior) unitDiscExterior,
    hM, hK', hW'.2.1, hwf, hwi, hm1, hmI, hm2, hconf, ?_⟩
  intro y hy
  have hGy : G y ∈ unitDiscExterior := by rw [← hD]; exact mem_image_of_mem G hy
  have e1 : (W ∘ Function.invFunOn G unitDiscExterior) (G y) = W y := by
    simp only [Function.comp_apply, hleft hy]
  have e2 : Function.invFunOn (W ∘ Function.invFunOn G unitDiscExterior) unitDiscExterior (W y) = G y := by
    rw [← e1]
    exact hh.2.2.1.2.1.leftInvOn_invFunOn hGy
  simp only [Function.comp_apply, e2]

/-- Preservation of the closed disc by a plane homeomorphism, as an `iff`. -/
theorem tmi_cb_iff {e : ℂ ≃ₜ ℂ} (h : e '' closedBall (0 : ℂ) 1 = closedBall (0 : ℂ) 1) (x : ℂ) :
    x ∈ closedBall (0 : ℂ) 1 ↔ e x ∈ closedBall (0 : ℂ) 1 := by
  constructor
  · intro hx
    rw [← h]
    exact mem_image_of_mem e hx
  · intro hx
    rw [← h] at hx
    obtain ⟨x', hx', hxx⟩ := hx
    rw [e.injective hxx] at hx'
    exact hx'

/-- The same on the sphere. -/
theorem tmi_map_iff {e : ℂ ≃ₜ ℂ} (h : ∀ x : ℂ, x ∈ closedBall (0 : ℂ) 1 ↔ e x ∈ closedBall (0 : ℂ) 1)
    (q : ExtPlane) :
    q ∈ toExt (closedBall (0 : ℂ) 1) ↔ OnePoint.map e q ∈ toExt (closedBall (0 : ℂ) 1) := by
  induction q using OnePoint.rec with
  | infty =>
    constructor
    · intro hq; exact absurd hq (infty_notMem_toExt _)
    · intro hq; exact absurd hq (infty_notMem_toExt _)
  | coe x =>
    show ((x : ℂ) : ExtPlane) ∈ toExt (closedBall (0 : ℂ) 1) ↔ ((e x : ℂ) : ExtPlane) ∈ toExt (closedBall (0 : ℂ) 1)
    rw [coe_mem_toExt_iff, coe_mem_toExt_iff]
    exact h x


/-- Core of the independence theorem: the Model A maps of the two Beltrami coefficients agree on the circle and,
after composing with `G₁, G₂`, on the exterior. -/
theorem tmi_main {μ ν : LinfStar} (hμ : μ ∈ LinfStarBall) (hν : ν ∈ LinfStarBall) {u : ExtPlane}
    (hu : u ∈ extDiscExterior) {G₁ G₂ : ℂ → ℂ}
    (hG₁ : IsQuasiconformal G₁ univ ∧ G₁ '' univ = univ ∧
      EqOn G₁ (fun z : ℂ => finPart (sigmaSphere u (gammaMu μ z))) unitCircle)
    (hG₂ : IsQuasiconformal G₂ univ ∧ G₂ '' univ = univ ∧
      EqOn G₂ (fun z : ℂ => finPart (sigmaSphere u (gammaMu μ z))) unitCircle) :
    tcurveLambda ν G₁ ∈ LinfStarBall ∧ tcurveLambda ν G₂ ∈ LinfStarBall ∧
    (∀ z : ℂ, ‖z‖ = 1 → wAS (tcurveLambda ν G₁) (z : ExtPlane) = wAS (tcurveLambda ν G₂) (z : ExtPlane)) ∧
    (∀ p ∉ toExt (closedBall (0 : ℂ) 1),
      OnePoint.map G₁ p ∉ toExt (closedBall (0 : ℂ) 1) ∧ OnePoint.map G₂ p ∉ toExt (closedBall (0 : ℂ) 1) ∧
      wAS (tcurveLambda ν G₁) (OnePoint.map G₁ p) = wAS (tcurveLambda ν G₂) (OnePoint.map G₂ p)) := by
  -- the Model B plane solution of `ν`
  obtain ⟨⟨Mν, hMν, W, hWn, -⟩, -⟩ := wB_spec hν
  obtain ⟨⟨KW, hKW⟩, hWs, -, -, hWae0⟩ := hWn
  have hWae : ∀ᵐ z ∂(volume.restrict unitDiscExterior), complexDilatation W z = ν z := by
    filter_upwards [ae_restrict_of_ae hWae0, ae_restrict_mem bc_hEo.measurableSet] with z h hz
    rw [h]
    simp [extB, Set.indicator_of_mem hz]
  obtain ⟨K₁, e₁, hK₁, he₁, hD₁, hCl₁, hS₁⟩ := tmi_G_data hμ hu hG₁
  obtain ⟨K₂, e₂, hK₂, he₂, hD₂, hCl₂, hS₂⟩ := tmi_G_data hμ hu hG₂
  have hGs₁ := hG₁.2.1
  have hGs₂ := hG₂.2.1
  have hb₁ := hG₁.2.2
  have hb₂ := hG₂.2.2
  obtain ⟨hlam₁, -⟩ := tmi_lambda_props hν hK₁ hGs₁ hD₁
  obtain ⟨hlam₂, -⟩ := tmi_lambda_props hν hK₂ hGs₂ hD₂
  obtain ⟨M₁, W₁, K₁', Ψ₁, hM₁, hK₁', hW₁s, hwf₁, hwi₁, hm1₁, hmI₁, hm2₁, hconf₁, hval₁⟩ :=
    tmi_conf_data hν hKW hWae hK₁ hGs₁ hD₁
  obtain ⟨M₂, W₂, K₂', Ψ₂, hM₂, hK₂', hW₂s, hwf₂, hwi₂, hm1₂, hmI₂, hm2₂, hconf₂, hval₂⟩ :=
    tmi_conf_data hν hKW hWae hK₂ hGs₂ hD₂
  set l₁ := tcurveLambda ν G₁ with hl₁
  set l₂ := tcurveLambda ν G₂ with hl₂
  -- the composite homeomorphism `Φ = G₂ ∘ G₁⁻¹`
  set Φ : ℂ ≃ₜ ℂ := e₁.symm.trans e₂ with hΦ
  have hΦG : ∀ x : ℂ, Φ (G₁ x) = G₂ x := fun x => by
    rw [← he₁, ← he₂]
    simp [hΦ]
  have hΦS : ∀ y : ℂ, ‖y‖ = 1 → Φ y = y := by
    intro y hy
    have : y ∈ G₁ '' sphere (0 : ℂ) 1 := by rw [hS₁]; exact mem_sphere_zero_iff_norm.2 hy
    obtain ⟨z, hz, rfl⟩ := this
    have hz1 : ‖z‖ = 1 := mem_sphere_zero_iff_norm.1 hz
    rw [hΦG]
    exact (hb₂ (show z ∈ unitCircle from hz1)).trans (hb₁ (show z ∈ unitCircle from hz1)).symm
  have hΦcb : ∀ x : ℂ, x ∈ closedBall (0 : ℂ) 1 ↔ Φ x ∈ closedBall (0 : ℂ) 1 := by
    intro x
    have h1 : e₁.symm x ∈ closedBall (0 : ℂ) 1 ↔ x ∈ closedBall (0 : ℂ) 1 := by
      have := tmi_cb_iff (he₁ ▸ hCl₁) (e₁.symm x)
      rwa [e₁.apply_symm_apply] at this
    rw [← h1]
    exact tmi_cb_iff (he₂ ▸ hCl₂) (e₁.symm x)
  have hΦs : ∀ q : ExtPlane, q ∈ toExt (closedBall (0 : ℂ) 1) ↔
      OnePoint.map Φ q ∈ toExt (closedBall (0 : ℂ) 1) := tmi_map_iff hΦcb
  have hΦsymm_cb : ∀ x : ℂ, x ∈ closedBall (0 : ℂ) 1 ↔ Φ.symm x ∈ closedBall (0 : ℂ) 1 := by
    intro x
    have := hΦcb (Φ.symm x)
    rw [Φ.apply_symm_apply] at this
    exact this.symm
  have hΦssymm : ∀ q : ExtPlane, q ∈ toExt (closedBall (0 : ℂ) 1) ↔
      OnePoint.map Φ.symm q ∈ toExt (closedBall (0 : ℂ) 1) := tmi_map_iff hΦsymm_cb
  have hmapΦ : ∀ p : ExtPlane, OnePoint.map Φ (OnePoint.map G₁ p) = OnePoint.map G₂ p := by
    intro p
    induction p using OnePoint.rec with
    | infty => rfl
    | coe x => exact congrArg (fun y : ℂ => (y : ExtPlane)) (hΦG x)
  have hmapΦinv : ∀ q : ExtPlane, OnePoint.map Φ (OnePoint.map Φ.symm q) = q := by
    intro q
    induction q using OnePoint.rec with
    | infty => rfl
    | coe x => exact congrArg (fun y : ℂ => (y : ExtPlane)) (Φ.apply_symm_apply x)
  -- the plane homeomorphisms of `W₁, W₂` and `W`
  obtain ⟨eW₁, heW₁⟩ := t1_homeomorph hK₁' hW₁s
  obtain ⟨eW₂, heW₂⟩ := t1_homeomorph hK₂' hW₂s
  obtain ⟨eW, heW⟩ := t1_homeomorph hKW hWs
  set R : ℂ ≃ₜ ℂ := eW₁.symm.trans (Φ.trans eW₂) with hR
  have hRapp : ∀ x : ℂ, R x = W₂ (Φ (eW₁.symm x)) := fun x => by
    rw [← heW₂]; rfl
  have hΩ : IsOpen (W '' unitDiscExterior) := by
    rw [← heW]; exact eW.isOpenMap _ bc_hEo
  have hΩ₁ : IsOpen (W₁ '' unitDiscExterior) := by
    rw [← heW₁]; exact eW₁.isOpenMap _ bc_hEo
  -- `R` is holomorphic on `W₁(𝔻*)`
  have hRdiff : DifferentiableOn ℂ R (W₁ '' unitDiscExterior) := by
    have hsymm := hconf₁.symm hΩ
    have hcomp : DifferentiableOn ℂ (Ψ₂ ∘ Function.invFunOn Ψ₁ (W '' unitDiscExterior))
        (W₁ '' unitDiscExterior) :=
      hconf₂.1.comp hsymm.1 (fun x hx => by
        have := hsymm.2.2 ▸ mem_image_of_mem (Function.invFunOn Ψ₁ (W '' unitDiscExterior)) hx
        exact this)
    refine hcomp.congr (fun x hx => ?_)
    obtain ⟨z, hz, rfl⟩ := hx
    have hz' : z ∈ G₁ '' unitDiscExterior := by rw [hD₁]; exact hz
    obtain ⟨y, hy, rfl⟩ := hz'
    have hWy : W y ∈ W '' unitDiscExterior := mem_image_of_mem W hy
    have e1 : Ψ₁ (W y) = W₁ (G₁ y) := hval₁ y hy
    have e2 : Function.invFunOn Ψ₁ (W '' unitDiscExterior) (W₁ (G₁ y)) = W y := by
      rw [← e1]
      exact hconf₁.2.1.leftInvOn_invFunOn hWy
    simp only [Function.comp_apply, e2, hval₂ y hy]
    have hs : eW₁.symm (W₁ (G₁ y)) = G₁ y := by
      rw [← heW₁]
      exact eW₁.symm_apply_apply _
    rw [hRapp, hs, hΦG]
  -- the Möbius data
  obtain ⟨a, b, c, d, hdet, rfl⟩ := hM₁
  obtain ⟨a', b', c', d', hdet', rfl⟩ := hM₂
  have hdetinv : d * a - (-b) * (-c) ≠ 0 := by
    have : d * a - (-b) * (-c) = a * d - b * c := by ring
    rwa [this]
  set M₁inv : ExtPlane → ExtPlane := mobiusExt d (-b) (-c) a with hM₁inv
  have hinv₁ : ∀ q, M₁inv (mobiusExt a b c d q) = q := mobiusExt_inv_apply hdet
  have hinv₁' : ∀ q, mobiusExt a b c d (M₁inv q) = q := by
    intro q
    have := mobiusExt_inv_apply (a := d) (b := -b) (c := -c) (d := a) hdetinv q
    simpa using this
  set C : ExtPlane → ExtPlane := fun p => mobiusExt a' b' c' d' (R.onePointCongr (M₁inv p)) with hC
  have hCdef : ∀ p, C p = mobiusExt a' b' c' d' (OnePoint.map R (M₁inv p)) := fun p => by
    simp only [hC]
    congr 1
  -- key identity
  have KI : ∀ y : ExtPlane, C (wAS l₁ y) = wAS l₂ (OnePoint.map Φ y) := by
    intro y
    induction y using OnePoint.rec with
    | infty =>
      rw [hwi₁, hCdef, hinv₁]
      show mobiusExt a' b' c' d' (R.onePointCongr extInf) = _
      have : OnePoint.map Φ (extInf : ExtPlane) = extInf := rfl
      rw [this, hwi₂]
      rfl
    | coe x =>
      rw [hwf₁, hCdef, hinv₁]
      have : OnePoint.map Φ ((x : ℂ) : ExtPlane) = ((Φ x : ℂ) : ExtPlane) := rfl
      rw [this, hwf₂]
      congr 1
      show ((R (W₁ x) : ℂ) : ExtPlane) = ((W₂ (Φ x) : ℂ) : ExtPlane)
      congr 1
      rw [hRapp]
      have : eW₁.symm (W₁ x) = x := by
        rw [← heW₁]; exact eW₁.symm_apply_apply _
      rw [this]
  -- properties of `C`
  have hCcont : Continuous C :=
    (continuous_mobiusExt hdet').comp (R.onePointCongr.continuous.comp (continuous_mobiusExt hdetinv))
  have hM₁i : Function.Injective M₁inv := fun p q h => by
    have := congrArg (mobiusExt a b c d) h
    rwa [hinv₁', hinv₁'] at this
  have hCinj : Function.Injective C := fun p q h => by
    apply hM₁i
    apply R.onePointCongr.injective
    exact (mobiusHomeomorph a' b' c' d' hdet').injective h
  have hcl : ∀ (l : LinfStar), l ∈ LinfStarBall → ∀ q : ExtPlane,
      q ∈ toExt (closedBall (0 : ℂ) 1) ↔ wAS l q ∈ toExt (closedBall (0 : ℂ) 1) := fun l hl q =>
    wAS_closed_iff hl q
  have hext₁ : ∀ p ∉ toExt (closedBall (0 : ℂ) 1), OnePoint.map G₁ p ∉ toExt (closedBall (0 : ℂ) 1) := by
    intro p hp
    exact fun h => hp ((tmi_map_iff (fun x => tmi_cb_iff (he₁ ▸ hCl₁) x) p).2 (by simpa [← he₁] using h))
  have hext₂ : ∀ p ∉ toExt (closedBall (0 : ℂ) 1), OnePoint.map G₂ p ∉ toExt (closedBall (0 : ℂ) 1) := by
    intro p hp
    exact fun h => hp ((tmi_map_iff (fun x => tmi_cb_iff (he₂ ▸ hCl₂) x) p).2 (by simpa [← he₂] using h))
  have hCnot : ∀ p ∉ toExt (closedBall (0 : ℂ) 1), C p ∉ toExt (closedBall (0 : ℂ) 1) := by
    intro p hp
    obtain ⟨y, rfl⟩ := (wAS_bijective l₁).2 p
    have hy : y ∉ toExt (closedBall (0 : ℂ) 1) := fun h => hp ((hcl l₁ hlam₁ y).1 h)
    rw [KI]
    intro h
    exact hy ((hΦs y).2 ((hcl l₂ hlam₂ _).2 h))
  have hCsurj : ∀ p' ∉ toExt (closedBall (0 : ℂ) 1), ∃ p ∉ toExt (closedBall (0 : ℂ) 1), C p = p' := by
    intro p' hp'
    obtain ⟨x, rfl⟩ := (wAS_bijective l₂).2 p'
    have hx : x ∉ toExt (closedBall (0 : ℂ) 1) := fun h => hp' ((hcl l₂ hlam₂ x).1 h)
    have hy : OnePoint.map Φ.symm x ∉ toExt (closedBall (0 : ℂ) 1) := fun h => hx ((hΦssymm x).2 h)
    refine ⟨wAS l₁ (OnePoint.map Φ.symm x), fun h => hy ((hcl l₁ hlam₁ _).2 h), ?_⟩
    rw [KI, hmapΦinv]
  have hfix : ∀ w : ℂ, ‖w‖ = 1 → wAS l₁ (w : ExtPlane) = (w : ExtPlane) →
      wAS l₂ (w : ExtPlane) = (w : ExtPlane) → C (w : ExtPlane) = (w : ExtPlane) := by
    intro w hw h1 h2
    have := KI (w : ExtPlane)
    have hΦw : OnePoint.map Φ (w : ExtPlane) = (w : ExtPlane) := congrArg (fun y : ℂ => (y : ExtPlane)) (hΦS w hw)
    rw [h1, hΦw, h2] at this
    exact this
  have hmaps : ∀ p ∉ toExt (closedBall (0 : ℂ) 1),
      M₁inv p = extInf ∨ ∃ x ∈ W₁ '' unitDiscExterior, M₁inv p = (x : ExtPlane) := by
    intro p hp
    obtain ⟨y, rfl⟩ := (wAS_bijective l₁).2 p
    have hy : y ∈ extDiscExterior := by
      rw [fi_extDiscExterior_eq_compl]
      exact fun h => hp ((hcl l₁ hlam₁ y).1 h)
    induction y using OnePoint.rec with
    | infty =>
      left
      rw [hwi₁, hinv₁]
    | coe x =>
      right
      have hx : x ∈ unitDiscExterior := by
        rcases hy with hy | hy
        · obtain ⟨x', hx', hx'x⟩ := hy
          rwa [← OnePoint.coe_injective hx'x]
        · exact absurd hy (OnePoint.coe_ne_infty x)
      exact ⟨W₁ x, mem_image_of_mem W₁ hx, by rw [hwf₁, hinv₁]⟩
  have hRΩ : DifferentiableOn ℂ R (W₁ '' unitDiscExterior) := hRdiff
  have hdiff := tmi_hdiff (Csph := C) (M₁ := M₁inv) (M₂ := mobiusExt a' b' c' d')
    ⟨d, -b, -c, a, hdetinv, rfl⟩ ⟨a', b', c', d', hdet', rfl⟩ hΩ₁ hRΩ hCdef hmaps hCcont hCinj hCnot
  obtain ⟨hid1, hid2⟩ := tmi_tail hCcont hCinj hCnot hCsurj hdiff
    (hfix (-1) (by simp) hm1₁ hm1₂) (hfix (-I) (by simp) hmI₁ hmI₂) (hfix 1 (by simp) hm2₁ hm2₂)
  refine ⟨hlam₁, hlam₂, ?_, ?_⟩
  · intro z hz
    obtain ⟨η, hη, hηe⟩ := wAS_maps_circle hlam₁ hz
    have h1 := KI (z : ExtPlane)
    have hΦz : OnePoint.map Φ (z : ExtPlane) = (z : ExtPlane) := congrArg (fun y : ℂ => (y : ExtPlane)) (hΦS z hz)
    rw [hηe, hΦz, hid1 η hη] at h1
    exact hηe.trans h1
  · intro p hp
    refine ⟨hext₁ p hp, hext₂ p hp, ?_⟩
    have hX : wAS l₁ (OnePoint.map G₁ p) ∉ toExt (closedBall (0 : ℂ) 1) := fun h =>
      hext₁ p hp ((hcl l₁ hlam₁ _).2 h)
    have h1 := KI (OnePoint.map G₁ p)
    rw [hid2 _ hX, hmapΦ] at h1
    exact h1




theorem tmi_wA_oneFixed {lam' : LinfStar} (hlam : lam' ∈ LinfStarBall) : IsOneFixedQS (wA lam') := by
  obtain ⟨M, hM, W, hW, hwf, hwi, hm1, hmI, hm2⟩ := wA_spec hlam
  exact ⟨⟨wA_circle_sensePreserving hlam, wA_circle_quasisymmetric hlam⟩, congrArg finPart hm2⟩

/-- Clause 2 of the independence theorem: if the Model A maps agree after composing with `F₁, F₂` on the
exterior and the two classes agree, then the Model B maps agree after composing with `F₁, F₂`. -/
theorem tmi_clause2 {l₁ l₂ : LinfStar} (hl₁ : l₁ ∈ LinfStarBall) (hl₂ : l₂ ∈ LinfStarBall)
    (hcirc : ∀ z ∈ unitCircle, wA l₁ z = wA l₂ z) {F₁ F₂ : ExtPlane → ExtPlane}
    (hF₁ : ∀ p ∉ toExt (closedBall (0 : ℂ) 1), F₁ p ∉ toExt (closedBall (0 : ℂ) 1))
    (hF₂ : ∀ p ∉ toExt (closedBall (0 : ℂ) 1), F₂ p ∉ toExt (closedBall (0 : ℂ) 1))
    (hB : ∀ p ∉ toExt (closedBall (0 : ℂ) 1), wAS l₁ (F₁ p) = wAS l₂ (F₂ p)) :
    ∀ p ∉ toExt (closedBall (0 : ℂ) 1), wB l₁ (F₁ p) = wB l₂ (F₂ p) := by
  -- the welding maps `g_{l₁} = g_{l₂}` on `𝔻*`
  have hw₁ : IsWeldingPrime (wA l₁) (fB l₁) (gMu l₁) := by
    have := gMu_isWelding hl₁
    rw [alphaMu_eq_id] at this
    exact weldingPrime_of_welding this
  have hw₂ : IsWeldingPrime (wA l₁) (fB l₂) (gMu l₂) := by
    have := gMu_isWelding hl₂
    rw [alphaMu_eq_id] at this
    exact weldingPrime_congr_h (fun z hz => (hcirc z hz).symm) (weldingPrime_of_welding this)
  have hg : EqOn (gMu l₁) (gMu l₂) unitDiscExterior :=
    (conformal_welding_prime_unique (tmi_wA_oneFixed hl₁) hw₁ hw₂).2
  have hex : ∀ {l : LinfStar}, l ∈ LinfStarBall → ∃ w, IsNormalizedB l w := fun {l} hl =>
    ⟨wB l, (wB_spec hl).1⟩
  -- the value of `wB l q` from `X = wAS l q`
  have hval : ∀ {l : LinfStar}, l ∈ LinfStarBall → ∀ q : ExtPlane,
      (wAS l q = extInf → wB l q = extInf) ∧
      ∀ z : ℂ, z ∈ unitDiscExterior → wAS l q = (z : ExtPlane) → wB l q = ((gMu l z : ℂ) : ExtPlane) := by
    intro l hl q
    refine ⟨fun hX => ?_, fun z hz hX => ?_⟩
    · have hq : q = Function.invFun (wAS l) extInf := by
        apply (wAS_bijective l).1
        rw [hX]
        exact (Function.invFun_eq ((wAS_bijective l).2 extInf)).symm
      rw [hq]
      exact (fB_normalization l).2.2 (hex hl)
    · have hq : Function.invFun (wAS l) (z : ExtPlane) = q := by
        rw [← hX]
        exact Function.leftInverse_invFun (wAS_bijective l).1 q
      rw [gMu_sphere_factorization hl hz, hq]
  intro p hp
  have hX := hB p hp
  have hXE : wAS l₂ (F₂ p) ∉ toExt (closedBall (0 : ℂ) 1) := fun h =>
    hF₂ p hp ((wAS_closed_iff hl₂ _).2 h)
  generalize hXg : wAS l₂ (F₂ p) = X at hX hXE
  induction X using OnePoint.rec with
  | infty =>
    rw [(hval hl₁ _).1 hX, (hval hl₂ _).1 hXg]
  | coe z =>
    have hz : z ∈ unitDiscExterior := by
      rw [coe_mem_toExt_iff, mem_closedBall_zero_iff, not_le] at hXE
      exact hXE
    rw [(hval hl₁ _).2 z hz hX, (hval hl₂ _).2 z hz hXg, hg hz]


theorem tcurve_mul_independent_new {μ ν : LinfStar} (hμ : μ ∈ LinfStarBall) (hν : ν ∈ LinfStarBall) {u : ExtPlane}
    (hu : u ∈ extDiscExterior) {G₁ G₂ : ℂ → ℂ}
    (hG₁ : IsQuasiconformal G₁ univ ∧ G₁ '' univ = univ ∧
      EqOn G₁ (fun z : ℂ => finPart (sigmaSphere u (gammaMu μ z))) unitCircle)
    (hG₂ : IsQuasiconformal G₂ univ ∧ G₂ '' univ = univ ∧
      EqOn G₂ (fun z : ℂ => finPart (sigmaSphere u (gammaMu μ z))) unitCircle) :
    (∀ z ∈ unitCircle, wA (tcurveLambda ν G₁) z = wA (tcurveLambda ν G₂) z) ∧
      ∀ ζ ∈ wB ν '' extDiscExterior,
        tcurveZ ν G₁ (tcurveLambda ν G₁) ζ = tcurveZ ν G₂ (tcurveLambda ν G₂) ζ := by
  obtain ⟨hl1, hl2, hcirc, hB⟩ := tmi_main hμ hν hu hG₁ hG₂
  have hwA : ∀ z ∈ unitCircle, wA (tcurveLambda ν G₁) z = wA (tcurveLambda ν G₂) z := fun z hz =>
    congrArg finPart (hcirc z hz)
  refine ⟨hwA, ?_⟩
  intro ζ hζ
  obtain ⟨p0, hp0, rfl⟩ := hζ
  have hinv : Function.invFun (wB ν) (wB ν p0) = p0 :=
    Function.leftInverse_invFun (wB_bijective ν).1 p0
  have hp0' : p0 ∉ toExt (closedBall (0 : ℂ) 1) := by
    rw [fi_extDiscExterior_eq_compl] at hp0
    exact hp0
  unfold tcurveZ
  rw [hinv]
  exact tmi_clause2 hl1 hl2 hwA (F₁ := OnePoint.map G₁) (F₂ := OnePoint.map G₂)
    (fun p hp => (hB p hp).1) (fun p hp => (hB p hp).2.1) (fun p hp => (hB p hp).2.2) p0 hp0'

/-! ### Original relocated from `TCurve` (2026-10-26) -/

/-- (TT:800) The point `([λ], z)` of (1.13)–(1.14) does not depend on the choice of the q.c. extension `𝗀` of
`σ_u ∘ 𝗀_μ`, where `u ∈ 𝔻* ∪ {∞}` is the fibre coordinate (`u = g_μ⁻¹(w)` in TT:800).
- **[CORRECTION 2026-10-26]** (i) The fibre coordinate `u : ℂ̄` is the hypothesis (the term `invFun (gMu μ) w` is
  junk for `w ∉ g_μ(𝔻*)`, and `u = ∞` is allowed). (ii) The second clause is restricted to `ζ` on the fibre
  `w^ν(𝔻* ∪ {∞})`: for `ζ = w^ν(p)`, `p ∈ 𝔻`, it is false (`𝗀` is only constrained on `S¹`, and `λ` only sees `𝔻*`). (iii) `λ` uses the dilatation of `𝗀`
  (`tcurveLambda`, user-approved option B). -/
theorem tcurve_mul_independent {μ ν : LinfStar} (hμ : μ ∈ LinfStarBall) (hν : ν ∈ LinfStarBall) {u : ExtPlane}
    (hu : u ∈ extDiscExterior) {G₁ G₂ : ℂ → ℂ}
    (hG₁ : IsQuasiconformal G₁ univ ∧ G₁ '' univ = univ ∧
      EqOn G₁ (fun z : ℂ => finPart (sigmaSphere u (gammaMu μ z))) unitCircle)
    (hG₂ : IsQuasiconformal G₂ univ ∧ G₂ '' univ = univ ∧
      EqOn G₂ (fun z : ℂ => finPart (sigmaSphere u (gammaMu μ z))) unitCircle) :
    (∀ z ∈ unitCircle, wA (tcurveLambda ν G₁) z = wA (tcurveLambda ν G₂) z) ∧
      ∀ ζ ∈ wB ν '' extDiscExterior,
        tcurveZ ν G₁ (tcurveLambda ν G₁) ζ = tcurveZ ν G₂ (tcurveLambda ν G₂) ζ :=
  tcurve_mul_independent_new hμ hν hu hG₁ hG₂

end TakhtajanTeo
