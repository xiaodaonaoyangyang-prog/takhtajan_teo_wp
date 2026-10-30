import TakhtajanTeo.Ch1.Eq19Completed

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal NNReal ComplexConjugate Classical Real
noncomputable section
namespace TakhtajanTeo
open LiZhongQC

theorem tce_gamma_circle {μ : LinfStar} (hμ : μ ∈ LinfStarBall) {z : ℂ} (hz : ‖z‖ = 1) :
    gammaMu μ z = ((wA μ z : ℂ) : ExtPlane) ∧ ‖wA μ z‖ = 1 := by
  obtain ⟨u, hu, he⟩ := wAS_maps_circle hμ hz
  have h1 : gammaMu μ z = (u : ExtPlane) := by
    unfold gammaMu
    rw [alphaMu_eq_id]
    exact he
  have hw : wA μ z = u := congrArg finPart he
  exact ⟨by rw [h1, hw], by rw [hw]; exact hu⟩

theorem tce_sigma_circle {w : ExtPlane} (hw : w ∈ extDiscExterior) {η : ℂ} (hη : ‖η‖ = 1) :
    ∃ y : ℂ, sigmaSphere w (η : ExtPlane) = (y : ExtPlane) := by
  induction w using OnePoint.rec with
  | infty => exact ⟨η, rfl⟩
  | coe w =>
    have hw' : w ∈ unitDiscExterior := by simpa [extDiscExterior, toExt] using hw
    have hne : η ≠ w := by
      intro h
      have h1 : 1 < ‖w‖ := hw'
      rw [← h, hη] at h1
      exact lt_irrefl _ h1
    exact ⟨sigmaW w η, sigmaSphere_coe_eq hw' hne⟩

theorem tce_sigma_inj {w : ExtPlane} (hw : w ∈ extDiscExterior) : Function.Injective (sigmaSphere w) := by
  induction w using OnePoint.rec with
  | infty => exact fun a b h => h
  | coe w =>
    have hw' : w ∈ unitDiscExterior := by simpa [extDiscExterior, toExt] using hw
    exact (mobiusHomeomorph _ _ _ _ (sigmaSphere_det hw')).injective

theorem tce_sigma_isMobius {w : ExtPlane} (hw : w ∈ extDiscExterior) : IsMobius (sigmaSphere w) := by
  obtain ⟨u, v, hσ, hd, -⟩ := sigmaSphere_matrix hw
  exact ⟨u, v, conj v, conj u, by simpa [mul_comm] using hd, hσ⟩

theorem tce_inj (p q : T1) (w v : ExtPlane) (hw : w ∈ extDiscExterior) (hv : v ∈ extDiscExterior)
    (h : EqOn (fun z : ℂ => finPart (sigmaSphere w (gammaMu (Quotient.out p : LinfStarBall) z)))
      (fun z : ℂ => finPart (sigmaSphere v (gammaMu (Quotient.out q : LinfStarBall) z))) unitCircle) :
    p = q ∧ w = v := by
  have hμp := (Quotient.out p : LinfStarBall).property
  have hμq := (Quotient.out q : LinfStarBall).property
  obtain ⟨hnp, -, -⟩ := eq_1_9_homeo
  have hnp' := hnp p
  have hnq' := hnp q
  -- pointwise equality of the sphere values on the circle
  have key : ∀ z : ℂ, ‖z‖ = 1 →
      sigmaSphere w ((wA (Quotient.out p : LinfStarBall) z : ℂ) : ExtPlane) =
        sigmaSphere v ((wA (Quotient.out q : LinfStarBall) z : ℂ) : ExtPlane) := by
    intro z hz
    have e := h (show z ∈ unitCircle from hz)
    obtain ⟨hg1, hn1⟩ := tce_gamma_circle hμp hz
    obtain ⟨hg2, hn2⟩ := tce_gamma_circle hμq hz
    have e' : finPart (sigmaSphere w ((wA (Quotient.out p : LinfStarBall) z : ℂ) : ExtPlane)) =
        finPart (sigmaSphere v ((wA (Quotient.out q : LinfStarBall) z : ℂ) : ExtPlane)) := by
      have := e
      simp only at this
      rw [hg1, hg2] at this
      exact this
    obtain ⟨y1, hy1⟩ := tce_sigma_circle hw hn1
    obtain ⟨y2, hy2⟩ := tce_sigma_circle hv hn2
    rw [hy1, hy2] at e' ⊢
    have : y1 = y2 := e'
    rw [this]
  have hfix := hnp'
  obtain ⟨-, hp1, hp2, hp3⟩ := hnp'
  obtain ⟨-, hq1, hq2, hq3⟩ := hnq'
  have hMeq : sigmaSphere w = sigmaSphere v := by
    refine mobius_eq_of_three_points (tce_sigma_isMobius hw) (tce_sigma_isMobius hv)
      (p₁ := -1) (p₂ := -I) (p₃ := 1) ?_ ?_ ?_ ?_ ?_ ?_
    · intro h
      have := congrArg Complex.im h
      simp at this
    · norm_num
    · intro h
      have := congrArg Complex.re h
      simp at this
    · have := key (-1) (by simp)
      rwa [hp1, hq1] at this
    · have := key (-I) (by simp)
      rwa [hp2, hq2] at this
    · have := key 1 (by simp)
      rwa [hp3, hq3] at this
  have hwv : w = v := by
    apply tce_sigma_inj hv
    rw [← hMeq, sigmaSphere_pole, hMeq, sigmaSphere_pole]
  subst hwv
  refine ⟨?_, rfl⟩
  have hEq : EqOn (wA (Quotient.out p : LinfStarBall)) (wA (Quotient.out q : LinfStarBall)) unitCircle := by
    intro z hz
    have := tce_sigma_inj hw (key z hz)
    exact OnePoint.coe_injective this
  exact (eq_1_9_homeo.2.1 p q hEq)


theorem tce_circle_norm {h : ℂ → ℂ} (hh : IsQSCircleHomeo h) {z : ℂ} (hz : ‖z‖ = 1) : ‖h z‖ = 1 := by
  obtain ⟨u, -, -, -, hu⟩ := hh.1
  obtain ⟨t, rfl⟩ := (Complex.norm_eq_one_iff _).1 hz
  rw [hu t]
  exact Complex.norm_exp_ofReal_mul_I _

theorem tce_alg {a b c c' ζ : ℂ} (hab : a * b ≠ 1) (ha : a ≠ 0) (hb : b ≠ 0) (hcc : c * c' = 1)
    (hR : c * (1 - a) = 1 - b) (hR' : c' * (1 - b) = 1 - a) (hd : 1 - a * ζ ≠ 0) :
    (1 - (-c' / a)) / (1 - (-c / b)) *
      ((1 - (ζ - b) / (c * (1 - a * ζ)) * (-c / b)) / ((ζ - b) / (c * (1 - a * ζ)) - (-c' / a))) = ζ := by
  have hc : c ≠ 0 := left_ne_zero_of_mul_eq_one hcc
  have hc' : c' ≠ 0 := right_ne_zero_of_mul_eq_one hcc
  have h1ab : 1 - a * b ≠ 0 := sub_ne_zero.2 (Ne.symm hab)
  have hbc : b + c ≠ 0 := by
    intro h
    apply hab
    have : c = -b := by linear_combination h
    rw [this] at hR
    linear_combination hR
  have hrel : a + c' = c' * (b + c) := by linear_combination hR' - hcc
  have hac : a + c' ≠ 0 := by
    rw [hrel]
    exact mul_ne_zero hc' hbc
  have hd2 : 1 - ζ * a ≠ 0 := by rwa [mul_comm]
  have h1ab2 : 1 - b * a ≠ 0 := by rwa [mul_comm]
  have hc'eq : c' = c⁻¹ := eq_inv_of_mul_eq_one_right hcc
  subst hc'eq
  have e1 : 1 - (-c⁻¹ / a) = (a + c⁻¹) / a := by field_simp; ring
  have e2 : 1 - (-c / b) = (b + c) / b := by field_simp; ring
  have e3 : (ζ - b) / (c * (1 - a * ζ)) - (-c⁻¹ / a) = (1 - a * b) / (a * c * (1 - a * ζ)) := by
    field_simp
    ring
  have e4 : 1 - (ζ - b) / (c * (1 - a * ζ)) * (-c / b) = ζ * (1 - a * b) / (b * (1 - a * ζ)) := by
    field_simp
    ring
  rw [e1, e2, e3, e4, hrel]
  field_simp


/-- Variant of `sphere_circle_id` without the three fixed points: the circle values of `Csph` are those of an
explicit disc Möbius map `ζ ↦ (ζ - ā)/(c (1 - a ζ))`. -/
theorem tce_sphere_circle_mobius {Csph : ExtPlane → ExtPlane} (hCcont : Continuous Csph)
    (hCinj : Function.Injective Csph)
    (hCnot : ∀ p ∉ toExt (closedBall (0 : ℂ) 1), Csph p ∉ toExt (closedBall (0 : ℂ) 1))
    (hCsurj : ∀ p' ∉ toExt (closedBall (0 : ℂ) 1), ∃ p ∉ toExt (closedBall (0 : ℂ) 1), Csph p = p')
    (hdiff' : DifferentiableOn ℂ (fun w : ℂ =>
      finPart (mobiusExt 0 1 1 0 (Csph (mobiusExt 0 1 1 0 (w : ExtPlane))))) unitDisc) :
    ∃ a c : ℂ, ‖a‖ < 1 ∧ ‖c‖ = 1 ∧ ∀ ζ : ℂ, ‖ζ‖ = 1 →
      Csph (ζ : ExtPlane) = (((ζ - conj a) / (c * (1 - a * ζ)) : ℂ) : ExtPlane) := by
  have hσc : Continuous (mobiusExt 0 1 1 0) := continuous_mobiusExt (by norm_num)
  have hσi : Function.Injective (mobiusExt 0 1 1 0) := fun a b h => by
    rw [← sigma_invol a, ← sigma_invol b, h]
  obtain ⟨cf, hcdef⟩ : ∃ cf : ℂ → ℂ, cf = fun w : ℂ =>
      finPart (mobiusExt 0 1 1 0 (Csph (mobiusExt 0 1 1 0 (w : ExtPlane)))) := ⟨_, rfl⟩
  rw [← hcdef] at hdiff'
  have hc1 : ∀ w ∈ unitDisc, mobiusExt 0 1 1 0 (Csph (mobiusExt 0 1 1 0 (w : ExtPlane))) =
      ((cf w : ℂ) : ExtPlane) ∧ cf w ∈ unitDisc := by
    intro w hw
    obtain ⟨y, hy, hyD⟩ := sigma_of_not_closed (hCnot _ (sigma_not_closed hw))
    have hcy : cf w = y := by
      rw [hcdef]
      show finPart (mobiusExt 0 1 1 0 (Csph _)) = y
      rw [hy]
      rfl
    exact ⟨by rw [hcy]; exact hy, hcy ▸ hyD⟩
  have hcinj : InjOn cf unitDisc := by
    intro w1 hw1 w2 hw2 h
    have e1 := (hc1 w1 hw1).1
    have e2 := (hc1 w2 hw2).1
    rw [h] at e1
    have := hCinj (hσi (e1.trans e2.symm))
    exact OnePoint.coe_injective (hσi this)
  have hcsurj : cf '' unitDisc = unitDisc := by
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
  obtain ⟨c0, a, hc0n, han, hbl⟩ :=
    exists_rotation_blaschke_of_isConformalOnto_unitDisc ⟨hdiff', hcinj, hcsurj⟩
  have hc0ne : c0 ≠ 0 := by
    intro h
    rw [h, norm_zero] at hc0n
    exact zero_ne_one hc0n
  have hden : ∀ x : ℂ, ‖x‖ ≤ 1 → 1 - conj a * x ≠ 0 := by
    intro x hx h
    have h1 : conj a * x = 1 := by linear_combination -h
    have h2 : ‖conj a * x‖ < 1 := by
      rw [norm_mul, Complex.norm_conj]
      calc ‖a‖ * ‖x‖ ≤ ‖a‖ * 1 := mul_le_mul_of_nonneg_left hx (norm_nonneg _)
        _ < 1 := by rw [mul_one]; exact han
    rw [h1, norm_one] at h2
    exact lt_irrefl _ h2
  have hden' : ∀ x : ℂ, ‖x‖ ≤ 1 → 1 - a * x ≠ 0 := by
    intro x hx h
    have := hden x hx
    apply this
    have h1 : a * x = 1 := by linear_combination -h
    have h2 : ‖a * x‖ < 1 := by
      rw [norm_mul]
      calc ‖a‖ * ‖x‖ ≤ ‖a‖ * 1 := mul_le_mul_of_nonneg_left hx (norm_nonneg _)
        _ < 1 := by rw [mul_one]; exact han
    rw [h1, norm_one] at h2
    exact absurd h2 (lt_irrefl _)
  have hnn : c0 * 1 - (-(c0 * a)) * (-(conj a)) ≠ 0 := by
    have : c0 * 1 - (-(c0 * a)) * (-(conj a)) = c0 * (1 - conj a * a) := by ring
    rw [this]
    exact mul_ne_zero hc0ne (by simpa using hden a (le_of_lt han))
  obtain ⟨A, B, C, D, hdet, heq, hA, hB, hC, hD⟩ : ∃ A B C D : ℂ, A * D - B * C ≠ 0 ∧
      EqOn cf (mobiusFn A B C D) unitDisc ∧ A = c0 ∧ B = -(c0 * a) ∧ C = -(conj a) ∧ D = 1 :=
    ⟨c0, -(c0 * a), -(conj a), 1, hnn, fun z hz => by
      rw [hbl hz]
      have hz' := hden z (le_of_lt (mem_ball_zero_iff.1 hz))
      show c0 * ((z - a) / (1 - conj a * z)) = (c0 * z + -(c0 * a)) / (-(conj a) * z + 1)
      rw [← mul_div_assoc]
      congr 1 <;> ring, rfl, rfl, rfl, rfl⟩
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
  refine ⟨a, c0, han, hc0n, fun ζ hζ => ?_⟩
  have hζ0 : ζ ≠ 0 := norm_ne_zero_iff.1 (by rw [hζ]; exact one_ne_zero)
  have hζi : ‖ζ⁻¹‖ = 1 := by rw [norm_inv, hζ]; simp
  have h1 := hcirc ζ⁻¹ hζi
  rw [sigma_coe (inv_ne_zero hζ0), inv_inv] at h1
  have hCD : C * ζ⁻¹ + D ≠ 0 := by
    rw [hC, hD]
    have := hden ζ⁻¹ hζi.le
    intro h
    apply this
    linear_combination h
  rw [mobiusExt_coe hCD] at h1
  have hy0 : mobiusFn A B C D ζ⁻¹ ≠ 0 := by
    unfold mobiusFn
    rw [hA, hB]
    refine div_ne_zero ?_ hCD
    have : c0 * ζ⁻¹ + -(c0 * a) = c0 * (ζ⁻¹ - a) := by ring
    rw [this]
    refine mul_ne_zero hc0ne (sub_ne_zero.2 fun h => ?_)
    have := congrArg norm h
    rw [hζi] at this
    linarith
  have h2 := congrArg (mobiusExt 0 1 1 0) h1
  rw [sigma_invol, sigma_coe hy0] at h2
  rw [h2]
  congr 1
  unfold mobiusFn
  rw [hA, hB, hC, hD]
  have h1a := hden' ζ hζ.le
  have h1b := hden ζ⁻¹ hζi.le
  have hne : ζ⁻¹ - a ≠ 0 := by
    intro h
    have h' : ζ⁻¹ = a := by linear_combination h
    rw [h', ] at hζi
    linarith
  field_simp
  ring

theorem tce_exists_mu {h : ℂ → ℂ} {K : ℝ} {e : ℂ ≃ₜ ℂ} (hH : IsKQC (⇑e) univ K)
    (hHc : e '' sphere (0 : ℂ) 1 = sphere (0 : ℂ) 1) (hHh : EqOn (⇑e) h unitCircle) :
    ∃ μ : LinfStar, μ ∈ LinfStarBall ∧ ∃ a c : ℂ, ‖a‖ < 1 ∧ ‖c‖ = 1 ∧ wA μ 1 = 1 ∧
      ∀ z : ℂ, ‖z‖ = 1 → wA μ z = (h z - conj a) / (c * (1 - a * h z)) := by
  have hK1 : (1 : ℝ) ≤ K := hH.2.1
  have hk0 : 0 ≤ (K - 1) / (K + 1) := div_nonneg (by linarith) (by linarith)
  have hk1 : (K - 1) / (K + 1) < 1 := by
    rw [div_lt_one (by linarith)]
    linarith
  have hDo : IsOpen {w : ℂ | 1 < ‖w‖} := isOpen_lt continuous_const continuous_norm
  have hbd0 := (isKQC_maxDilatation_le hH).2
  have hbd : ∀ᵐ z ∂(volume.restrict unitDiscExterior),
      ‖complexDilatation (⇑e) z‖ ≤ (K - 1) / (K + 1) :=
    ae_restrict_of_ae_restrict_of_subset (subset_univ _) hbd0
  have hmeas : AEStronglyMeasurable (complexDilatation (⇑e)) (volume.restrict unitDiscExterior) :=
    (thm10_2_genHomeoSolution_of_isKQC hH).1.1.mono_measure
      (Measure.restrict_mono (subset_univ _) le_rfl)
  have hmem : MemLp (complexDilatation (⇑e)) ∞ (volume.restrict unitDiscExterior) :=
    memLp_top_of_bound hmeas _ hbd
  obtain ⟨μ, hμdef⟩ : ∃ μ : LinfStar, μ = toLinf (complexDilatation (⇑e)) := ⟨_, rfl⟩
  have hμae : (μ : ℂ → ℂ) =ᵐ[volume.restrict unitDiscExterior] complexDilatation (⇑e) := by
    rw [hμdef]
    exact bc_toLinf_ae hmem
  have hμ : μ ∈ LinfStarBall := by
    change μ ∈ ball (0 : LinfStar) 1
    rw [mem_ball_zero_iff, hμdef]
    exact lt_of_le_of_lt (norm_toLinf_le_of_ae_bound hk0 hbd) hk1
  refine ⟨μ, hμ, ?_⟩
  obtain ⟨Mμ, hMμ, Wμ, hWμ, hwfμ, hwiμ, hm1', hmI', hm2'⟩ := wA_spec hμ
  obtain ⟨KW, hKW⟩ := hWμ.1
  have hKWD := ac_t_isKQC_restrict hKW hDo (subset_univ _)
  have hKeD := ac_t_isKQC_restrict hH hDo (subset_univ _)
  have hdil : ∀ᵐ z ∂(volume.restrict {w : ℂ | 1 < ‖w‖}),
      complexDilatation Wμ z = complexDilatation (⇑e) z := by
    filter_upwards [ae_restrict_of_ae hWμ.2.2.2.2, hμae, ae_restrict_mem hDo.measurableSet]
      with z h1 h2 hz
    rw [h1, extA_eq_on_exterior μ hz]
    exact h2
  have hψ := bg_conformal_of_dilatation_eq hKeD hKWD hdil
  obtain ⟨hreg1, hreg2, hreg3⟩ := planeHomeomorph_circle_regions e hHc
  have hD : (⇑e) '' {w : ℂ | 1 < ‖w‖} = {w : ℂ | 1 < ‖w‖} := hreg3
  rw [hD] at hψ
  -- the sphere map
  have hE : ∀ u : ℂ, e.onePointCongr (u : ExtPlane) = ((e u : ℂ) : ExtPlane) := fun u => rfl
  have hEs : ∀ u : ℂ, e.onePointCongr.symm (u : ExtPlane) = ((e.symm u : ℂ) : ExtPlane) := by
    intro u
    exact e.onePointCongr.symm_apply_eq.2 (by rw [hE, e.apply_symm_apply])
  have hEinf : e.onePointCongr.symm extInf = extInf :=
    e.onePointCongr.symm_apply_eq.2 rfl
  have hEcl : ∀ q ∈ toExt (closedBall (0 : ℂ) 1), e.onePointCongr q ∈ toExt (closedBall (0 : ℂ) 1) := by
    rintro _ ⟨v, hv, rfl⟩
    exact ⟨e v, hreg1 ▸ mem_image_of_mem e hv, rfl⟩
  have hEscl : ∀ p ∈ toExt (closedBall (0 : ℂ) 1),
      e.onePointCongr.symm p ∈ toExt (closedBall (0 : ℂ) 1) := by
    rintro _ ⟨u, hu, rfl⟩
    rw [hEs]
    rw [← hreg1] at hu
    obtain ⟨v, hv, rfl⟩ := hu
    refine ⟨v, hv, ?_⟩
    rw [e.symm_apply_apply]
  obtain ⟨Csph, hCdef⟩ : ∃ Csph : ExtPlane → ExtPlane,
      Csph = fun p => wAS μ (e.onePointCongr.symm p) := ⟨_, rfl⟩
  have hCcont : Continuous Csph := by
    rw [hCdef]
    exact (wAS_continuous hμ).comp e.onePointCongr.symm.continuous
  have hCinj : Function.Injective Csph := by
    intro p q hpq
    rw [hCdef] at hpq
    exact e.onePointCongr.symm.injective ((wAS_bijective μ).1 hpq)
  have hCnot : ∀ p ∉ toExt (closedBall (0 : ℂ) 1), Csph p ∉ toExt (closedBall (0 : ℂ) 1) := by
    intro p hp hC
    rw [hCdef] at hC
    have h2 := hEcl _ ((wAS_closed_iff hμ _).2 hC)
    rw [e.onePointCongr.apply_symm_apply] at h2
    exact hp h2
  have hCsurj : ∀ p' ∉ toExt (closedBall (0 : ℂ) 1), ∃ p ∉ toExt (closedBall (0 : ℂ) 1),
      Csph p = p' := by
    intro p' hp'
    obtain ⟨q, hq⟩ := (wAS_bijective μ).2 p'
    have hqn : q ∉ toExt (closedBall (0 : ℂ) 1) := by
      intro hqc
      apply hp'
      rw [← hq]
      exact (wAS_closed_iff hμ q).1 hqc
    refine ⟨e.onePointCongr q, ?_, ?_⟩
    · intro hc
      have h5 := hEscl _ hc
      rw [e.onePointCongr.symm_apply_apply] at h5
      exact hqn h5
    · rw [hCdef]
      show wAS μ (e.onePointCongr.symm (e.onePointCongr q)) = p'
      rw [e.onePointCongr.symm_apply_apply, hq]
  have hcirc : ∀ z : ℂ, ‖z‖ = 1 → e z = h z := fun z hz => hHh (show z ∈ unitCircle from hz)
  have hsymm : ∀ z : ℂ, ‖z‖ = 1 → e.symm (h z) = z := by
    intro z hz
    rw [← hcirc z hz, e.symm_apply_apply]
  -- conformality of `c`
  have hσi : Function.Injective (mobiusExt 0 1 1 0) := fun a b h => by
    rw [← sigma_invol a, ← sigma_invol b, h]
  have hσ : IsMobius (mobiusExt 0 1 1 0) := ⟨0, 1, 1, 0, by norm_num, rfl⟩
  have hP : IsMobius (fun p => mobiusExt 0 1 1 0 (Mμ p)) := isMobius_comp hMμ hσ
  have hPc := mobius_finite_conformal hP
  obtain ⟨c, hcdef⟩ : ∃ c : ℂ → ℂ, c = fun w : ℂ =>
      finPart (mobiusExt 0 1 1 0 (Csph (mobiusExt 0 1 1 0 (w : ExtPlane)))) := ⟨_, rfl⟩
  have hinvon : ∀ u ∈ {w : ℂ | 1 < ‖w‖}, Function.invFunOn (⇑e) {w : ℂ | 1 < ‖w‖} u = e.symm u := by
    intro u hu
    rw [← hD] at hu
    obtain ⟨v, hv, rfl⟩ := hu
    rw [e.symm_apply_apply]
    exact (e.injective.injOn).leftInvOn_invFunOn hv
  obtain ⟨Ω, hΩ⟩ : ∃ Ω : Set ℂ, Ω = {w | w ∈ unitDisc ∧ w ≠ 0 ∧
      Csph (mobiusExt 0 1 1 0 (w : ExtPlane)) ≠ extInf} := ⟨_, rfl⟩
  have hcw : ∀ w ∈ Ω, w⁻¹ ∈ {w : ℂ | 1 < ‖w‖} ∧
      c w = finPart (mobiusExt 0 1 1 0 (Mμ (((Wμ ∘ Function.invFunOn (⇑e) {w : ℂ | 1 < ‖w‖}) w⁻¹ : ℂ) :
        ExtPlane))) ∧
      mobiusExt 0 1 1 0 (Mμ (((Wμ ∘ Function.invFunOn (⇑e) {w : ℂ | 1 < ‖w‖}) w⁻¹ : ℂ) : ExtPlane)) ≠
        extInf := by
    intro w hw
    rw [hΩ] at hw
    obtain ⟨hwD, hw0, hwne⟩ := hw
    have hwin : w⁻¹ ∈ {w : ℂ | 1 < ‖w‖} := by
      show 1 < ‖w⁻¹‖
      rw [norm_inv]
      have : ‖w‖ < 1 := mem_ball_zero_iff.1 hwD
      exact one_lt_inv₀ (norm_pos_iff.2 hw0) |>.2 this
    have hCw : Csph (mobiusExt 0 1 1 0 (w : ExtPlane)) =
        Mμ (((Wμ ∘ Function.invFunOn (⇑e) {w : ℂ | 1 < ‖w‖}) w⁻¹ : ℂ) : ExtPlane) := by
      rw [hCdef]
      show wAS μ (e.onePointCongr.symm (mobiusExt 0 1 1 0 (w : ExtPlane))) = _
      rw [sigma_coe hw0, hEs, Function.comp_apply, hinvon _ hwin]
      exact hwfμ _
    refine ⟨hwin, ?_, ?_⟩
    · rw [hcdef]
      show finPart (mobiusExt 0 1 1 0 (Csph (mobiusExt 0 1 1 0 (w : ExtPlane)))) = _
      rw [hCw]
    · rw [← hCw]
      obtain ⟨y, hy, -⟩ := sigma_of_not_closed (hCnot _ (sigma_not_closed hwD))
      rw [hy]
      exact OnePoint.coe_ne_infty y
  have hdiffΩ : DifferentiableOn ℂ c Ω := by
    have h1 : DifferentiableOn ℂ (fun w : ℂ => w⁻¹) Ω := fun w hw =>
      ((differentiableAt_id.inv (by
        rw [hΩ] at hw
        exact hw.2.1))).differentiableWithinAt
    have h2 : DifferentiableOn ℂ ((Wμ ∘ Function.invFunOn (⇑e) {w : ℂ | 1 < ‖w‖}) ∘ fun w : ℂ => w⁻¹) Ω :=
      hψ.1.comp h1 (fun w hw => (hcw w hw).1)
    have h3 := hPc.1.comp h2 (fun w hw => (hcw w hw).2.2)
    refine h3.congr (fun w hw => ?_)
    exact (hcw w hw).2.1
  have hE1 : {w : ℂ | w ∈ unitDisc ∧ Csph (mobiusExt 0 1 1 0 (w : ExtPlane)) = extInf}.Subsingleton := by
    intro w1 h1 w2 h2
    have := hCinj (h1.2.trans h2.2.symm)
    exact OnePoint.coe_injective (hσi this)
  have hEfin : (unitDisc \ Ω).Finite := by
    refine ((Set.finite_singleton (0 : ℂ)).union hE1.finite).subset ?_
    intro w hw
    by_cases h0 : w = 0
    · exact Or.inl h0
    · refine Or.inr ⟨hw.1, ?_⟩
      by_contra hb
      apply hw.2
      rw [hΩ]
      exact ⟨hw.1, h0, hb⟩
  have hdiffc : DifferentiableOn ℂ c unitDisc := by
    refine differentiableOn_of_finite_exceptional (show IsOpen unitDisc from isOpen_ball) hEfin ?_ ?_
    · rw [hcdef]
      exact sphere_c_continuousOn hCcont hCnot
    · refine hdiffΩ.mono ?_
      intro w hw
      by_contra h
      exact hw.2 ⟨hw.1, h⟩
  obtain ⟨a, c, ha, hc, hform⟩ := tce_sphere_circle_mobius hCcont hCinj hCnot hCsurj
    (by rw [← hcdef]; exact hdiffc)
  refine ⟨a, c, ha, hc, congrArg finPart hm2', fun z hz => ?_⟩
  have hez : ‖e z‖ = 1 := mem_sphere_zero_iff_norm.1 (hHc ▸ mem_image_of_mem e (mem_sphere_zero_iff_norm.2 hz))
  have h3 := hform (e z) hez
  rw [hCdef] at h3
  have h4 : wAS μ (z : ExtPlane) = (((e z - conj a) / (c * (1 - a * e z)) : ℂ) : ExtPlane) := by
    have := h3
    simp only [hEs, e.symm_apply_apply] at this
    exact this
  show finPart (wAS μ (z : ExtPlane)) = (h z - conj a) / (c * (1 - a * h z))
  rw [h4, ← hcirc z hz]
  rfl


theorem tce_surj {h : ℂ → ℂ} (hh : IsOneFixedQS h) :
    ∃ (p : T1) (w : ExtPlane), w ∈ extDiscExterior ∧
      EqOn (fun z : ℂ => finPart (sigmaSphere w (gammaMu (Quotient.out p : LinfStarBall) z))) h unitCircle := by
  obtain ⟨H, ⟨K, hK⟩, hHs, hHc, hHh⟩ := circle_quasisymmetric_plane_extension hh.1
  obtain ⟨e, rfl⟩ := t1_homeomorph hK hHs
  obtain ⟨μ, hμ, a, c, ha, hc, hw1, hform⟩ := tce_exists_mu hK hHc hHh
  have h2 : teichSetoid.r (Phi ⟨μ, hμ⟩).out ⟨μ, hμ⟩ := Quotient.mk_out (s := teichSetoid) ⟨μ, hμ⟩
  have hμo := (Quotient.out (Phi ⟨μ, hμ⟩) : LinfStarBall).property
  have hh1 : h 1 = 1 := hh.2
  have hc0 : c ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hc
    exact zero_ne_one hc
  have h1a : 1 - a ≠ 0 := by
    intro h0
    have : a = 1 := by linear_combination -h0
    rw [this, norm_one] at ha
    exact lt_irrefl _ ha
  -- the relation `c (1 - a) = 1 - ā`
  have hR : c * (1 - a) = 1 - conj a := by
    have := hform 1 (by simp)
    rw [hw1, hh1] at this
    rw [eq_div_iff (mul_ne_zero hc0 (by simpa using h1a))] at this
    linear_combination this
  refine ⟨Phi ⟨μ, hμ⟩, ?_⟩
  by_cases ha0 : a = 0
  · -- the identity fibre point
    refine ⟨extInf, Or.inr rfl, fun z hz => ?_⟩
    have hz1 : ‖z‖ = 1 := hz
    obtain ⟨hg, -⟩ := tce_gamma_circle hμo hz1
    have hc1 : c = 1 := by
      rw [ha0] at hR
      simpa using hR
    have hw := hform z hz1
    rw [ha0, hc1] at hw
    have e1 : wA (Quotient.out (Phi ⟨μ, hμ⟩) : LinfStarBall) z = wA μ z := h2 z hz
    show finPart (sigmaSphere extInf (gammaMu (Quotient.out (Phi ⟨μ, hμ⟩) : LinfStarBall) z)) = h z
    rw [hg, e1, hw]
    simp [sigmaSphere, finPart]
  · have hb : conj a ≠ 0 := (map_ne_zero conj).2 ha0
    have han : ‖a‖ < 1 := ha
    have hwn : 1 < ‖(-conj c / a : ℂ)‖ := by
      rw [norm_div, norm_neg, Complex.norm_conj, hc]
      rw [lt_div_iff₀ (norm_pos_iff.2 ha0)]
      linarith
    have hwmem : ((-conj c / a : ℂ) : ExtPlane) ∈ extDiscExterior :=
      Or.inl ⟨-conj c / a, hwn, rfl⟩
    refine ⟨((-conj c / a : ℂ) : ExtPlane), hwmem, fun z hz => ?_⟩
    have hz1 : ‖z‖ = 1 := hz
    obtain ⟨hg, hn⟩ := tce_gamma_circle hμo hz1
    have e1 : wA (Quotient.out (Phi ⟨μ, hμ⟩) : LinfStarBall) z = wA μ z := h2 z hz
    have hw := hform z hz1
    have hzn : ‖h z‖ = 1 := tce_circle_norm hh.1 hz1
    have hne : wA (Quotient.out (Phi ⟨μ, hμ⟩) : LinfStarBall) z ≠ -conj c / a := by
      intro he
      have := congrArg norm he
      rw [hn] at this
      linarith
    show finPart (sigmaSphere ((-conj c / a : ℂ) : ExtPlane)
      (gammaMu (Quotient.out (Phi ⟨μ, hμ⟩) : LinfStarBall) z)) = h z
    rw [hg, sigmaSphere_coe_eq hwn hne]
    show sigmaW (-conj c / a) (wA (Quotient.out (Phi ⟨μ, hμ⟩) : LinfStarBall) z) = h z
    rw [e1, hw]
    have hcc : c * conj c = 1 := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hc]
      norm_num
    have hR' : conj c * (1 - conj a) = 1 - a := by
      have := congrArg conj hR
      simpa using this
    have hab : a * conj a ≠ 1 := by
      intro h0
      have h3 : ‖a * conj a‖ = 1 := by rw [h0, norm_one]
      rw [norm_mul, Complex.norm_conj] at h3
      nlinarith [norm_nonneg a]
    have hd : 1 - a * h z ≠ 0 := by
      intro h0
      have h3 : a * h z = 1 := by linear_combination -h0
      have h4 : ‖a * h z‖ = 1 := by rw [h3, norm_one]
      rw [norm_mul, hzn] at h4
      linarith
    unfold sigmaW
    rw [show conj (-conj c / a) = -c / conj a by simp [map_div₀]]
    exact tce_alg hab ha0 hb hcc hR hR' hd

theorem TCurve_equiv_oneFixed_new :
    (∀ (p q : T1) (w v : ExtPlane), w ∈ extDiscExterior → v ∈ extDiscExterior →
        EqOn (fun z : ℂ => finPart (sigmaSphere w (gammaMu (Quotient.out p : LinfStarBall) z)))
          (fun z : ℂ => finPart (sigmaSphere v (gammaMu (Quotient.out q : LinfStarBall) z))) unitCircle →
        p = q ∧ w = v) ∧
      ∀ h, IsOneFixedQS h → ∃ (p : T1) (w : ExtPlane), w ∈ extDiscExterior ∧
        EqOn (fun z : ℂ => finPart (sigmaSphere w (gammaMu (Quotient.out p : LinfStarBall) z))) h unitCircle :=
  ⟨fun p q w v hw hv h => tce_inj p q w v hw hv h, fun _ hh => tce_surj hh⟩

/-! ### Original relocated from `S1_2` (2026-10-26), statement corrected (user-approved) -/

/-- (TT:764–768) `𝒯(1) ≅ S¹\Homeo_qs(S¹)`: the map `([μ], g_μ(w)) ↦ σ_w ∘ 𝗀_μ` is a bijection of `𝒯(1)` onto the
maps fixing `1` (compared on `S¹`). It is stated on the parametrization `T(1) × (𝔻* ∪ {∞})` of TT:571.
- **[CORRECTION 2026-10-26]** The fibre coordinate `w` ranges over `𝔻* ∪ {∞}` (`σ_∞ = id` is the zero section
  `(0, ∞)`); with finite `w` only the surjectivity clause fails (`h = id`). `w : ℂ̄`, and `σ_w` is `sigmaSphere w`. -/
theorem TCurve_equiv_oneFixed :
    (∀ (p q : T1) (w v : ExtPlane), w ∈ extDiscExterior → v ∈ extDiscExterior →
        EqOn (fun z : ℂ => finPart (sigmaSphere w (gammaMu (Quotient.out p : LinfStarBall) z)))
          (fun z : ℂ => finPart (sigmaSphere v (gammaMu (Quotient.out q : LinfStarBall) z))) unitCircle →
        p = q ∧ w = v) ∧
      ∀ h, IsOneFixedQS h → ∃ (p : T1) (w : ExtPlane), w ∈ extDiscExterior ∧
        EqOn (fun z : ℂ => finPart (sigmaSphere w (gammaMu (Quotient.out p : LinfStarBall) z))) h unitCircle :=
  TCurve_equiv_oneFixed_new

/-! ### Corrected original relocated from `S1_2` (2026-10-26, user-approved; open) -/

-- `tcurve_mul_independent` moved to `Ch1/TCurveIndependent.lean` (2026-10-26).

end TakhtajanTeo
