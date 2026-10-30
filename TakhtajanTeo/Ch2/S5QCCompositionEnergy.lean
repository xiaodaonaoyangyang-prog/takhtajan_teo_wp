import TakhtajanTeo.Ch2.S5SobolevTrace
import TakhtajanTeo.Ch1.CircleQCPlaneExtension

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal NNReal ComplexConjugate Classical Real

noncomputable section
namespace TakhtajanTeo.Ch2
open LiZhongQC

-- L1
theorem s5qc_area {Γ : ℂ → ℂ} {D : Set ℂ} {K : ℝ} (hΓ : IsKQC Γ D K)
    (G : ℂ → ℝ) :
    (IntegrableOn G (Γ '' D) ↔ IntegrableOn (fun z => jacobian Γ z * G (Γ z)) D) ∧
      (∫ w in Γ '' D, G w) = ∫ z in D, jacobian Γ z * G (Γ z) := by
  let S : Set ℂ := D ∩ {z | DifferentiableAt ℝ Γ z}
  have hSD : S ⊆ D := inter_subset_left
  have hSm : MeasurableSet S := hΓ.1.measurableSet.inter (measurableSet_of_differentiableAt ℝ Γ)
  have hn : volume (D \ S) = 0 := by
    have h := (ae_restrict_iff' hΓ.1.measurableSet).mp (thm9_3_differentiable_ae hΓ)
    rw [ae_iff] at h
    apply measure_mono_null (fun z hz => ?_) h
    intro hd
    exact hz.2 ⟨hz.1, hd hz.1⟩
  have hSae : S =ᵐ[volume] D := ae_eq_set.mpr
    ⟨by rw [sdiff_eq_empty.mpr hSD, measure_empty], hn⟩
  have hIn : volume (Γ '' D \ Γ '' S) = 0 :=
    measure_mono_null (Set.subset_image_sdiff Γ D S)
      (thm9_6_cor1_null hΓ sdiff_subset hn)
  have hIae : Γ '' S =ᵐ[volume] Γ '' D := ae_eq_set.mpr
    ⟨by rw [sdiff_eq_empty.mpr (image_mono hSD), measure_empty], hIn⟩
  have hd : ∀ z ∈ S, HasFDerivWithinAt Γ (fderiv ℝ Γ z) S z :=
    fun z hz => hz.2.hasFDerivAt.hasFDerivWithinAt
  have hi : InjOn Γ S := hΓ.2.2.1.2.1.mono hSD
  have he : EqOn (fun z => |(fderiv ℝ Γ z).det| • G (Γ z))
      (fun z => jacobian Γ z * G (Γ z)) S := by
    intro z hz
    dsimp only
    rw [← ar_jacobian_eq_abs_det hΓ hz.1 hz.2]
    rfl
  have hI := integrableOn_image_iff_integrableOn_abs_det_fderiv_smul volume hSm hd hi G
  rw [integrableOn_congr_set_ae hIae, integrableOn_congr_fun he hSm,
    integrableOn_congr_set_ae hSae] at hI
  have hJ := integral_image_eq_integral_abs_det_fderiv_smul volume hSm hd hi G
  rw [setIntegral_congr_set hIae, setIntegral_congr_fun hSm he,
    setIntegral_congr_set hSae] at hJ
  exact ⟨hI, hJ⟩

-- L2
theorem s5qc_linear_energy (a b p q : ℂ) :
    ‖a * p + b * conj q‖ ^ 2 + ‖a * q + b * conj p‖ ^ 2 ≤
      (‖a‖ ^ 2 + ‖b‖ ^ 2) * (‖p‖ + ‖q‖) ^ 2 := by
  have h1 : ‖a * p + b * conj q‖ ≤ ‖a‖ * ‖p‖ + ‖b‖ * ‖q‖ := by
    simpa only [norm_mul, norm_conj] using norm_add_le (a * p) (b * conj q)
  have h2 : ‖a * q + b * conj p‖ ≤ ‖a‖ * ‖q‖ + ‖b‖ * ‖p‖ := by
    simpa only [norm_mul, norm_conj] using norm_add_le (a * q) (b * conj p)
  have hs1 := pow_le_pow_left₀ (norm_nonneg _) h1 2
  have hs2 := pow_le_pow_left₀ (norm_nonneg _) h2 2
  have hr := mul_nonneg (mul_nonneg (norm_nonneg p) (norm_nonneg q))
    (sq_nonneg (‖a‖ - ‖b‖))
  nlinarith

-- L3
theorem s5qc_pointwise_energy {Γ ψ : ℂ → ℂ} {D : Set ℂ} {K : ℝ} {z : ℂ}
    (hΓ : IsKQC Γ D K) (hz : z ∈ D) (hd : DifferentiableAt ℝ Γ z)
    (hψ : DifferentiableAt ℝ ψ (Γ z)) :
    ‖dz (ψ ∘ Γ) z‖ ^ 2 + ‖dzbar (ψ ∘ Γ) z‖ ^ 2 ≤
      K * jacobian Γ z * (‖dz ψ (Γ z)‖ ^ 2 + ‖dzbar ψ (Γ z)‖ ^ 2) := by
  rw [eq6_2_dz_comp hd hψ, eq6_2_dzbar_comp hd hψ,
    ← (eq6_3 hd).1, ← (eq6_3 hd).2]
  have h := s5qc_linear_energy (dz ψ (Γ z)) (dzbar ψ (Γ z)) (dz Γ z) (dzbar Γ z)
  have hK := ac_t_dilatation_of_differentiableAt hΓ hz hd
  have hmul := mul_le_mul_of_nonneg_right hK
    (add_nonneg (norm_nonneg (dz Γ z)) (norm_nonneg (dzbar Γ z)))
  have hs : (‖dz Γ z‖ + ‖dzbar Γ z‖) ^ 2 ≤ K * jacobian Γ z := by
    unfold jacobian
    nlinarith
  have hnonneg : 0 ≤ ‖dz ψ (Γ z)‖ ^ 2 + ‖dzbar ψ (Γ z)‖ ^ 2 := by positivity
  have h' := mul_le_mul_of_nonneg_left hs hnonneg
  exact h.trans (by nlinarith [h'])

-- L4
theorem s5qc_compact_chain {Γ ψ : ℂ → ℂ} {K : ℝ} (hΓ : IsKQC Γ univ K)
    (hψ : ContDiff ℝ 1 ψ) (hc : HasCompactSupport ψ) :
    ∃ Fx Fy : ℂ → ℂ, HasGenPartials (ψ ∘ Γ) Fx Fy univ 2 ∧
      MemLp Fx 2 (volume.restrict unitDisc) ∧ MemLp Fy 2 (volume.restrict unitDisc) := by
  obtain ⟨B, hB⟩ := (hc.fderiv (𝕜 := ℝ)).exists_bound_of_continuous
    (hψ.continuous_fderiv one_ne_zero)
  have hg := eq22w_hasGen_comp isOpen_univ (thm9_5_L2_derivatives hΓ).1 hψ hB
  have hL := hg.1 (closedBall 0 1) (subset_univ _) (isCompact_closedBall _ _)
  have hμ : volume.restrict unitDisc ≤ volume.restrict (closedBall (0 : ℂ) 1) :=
    Measure.restrict_mono ball_subset_closedBall le_rfl
  exact ⟨_, _, hg, hL.1.mono_measure hμ, hL.2.mono_measure hμ⟩

theorem s5qc_gen_restrict {F Fx Fy : ℂ → ℂ} {D U : Set ℂ}
    (h : HasGenPartials F Fx Fy D 2) (hUD : U ⊆ D) : HasGenPartials F Fx Fy U 2 := by
  obtain ⟨hl, fn, hfn, hc, hLp⟩ := h
  exact ⟨fun C hC hK => hl C (hC.trans hUD) hK, fn,
    fun n => (hfn n).mono hUD, hc.mono hUD, fun C hC hK => hLp C (hC.trans hUD) hK⟩

theorem s5qc_gen_congr {F G Fx Fy : ℂ → ℂ} {D : Set ℂ}
    (h : HasGenPartials F Fx Fy D 2) (he : EqOn F G D) : HasGenPartials G Fx Fy D 2 := by
  obtain ⟨hl, fn, hfn, hc, hLp⟩ := h
  exact ⟨hl, fn, hfn, hc.congr_right he, hLp⟩

theorem s5qc_gen_energy_ae {F Fx Fy : ℂ → ℂ} {D : Set ℂ}
    (hD : IsOpen D) (h : HasGenPartials F Fx Fy D 2)
    (hd : ∀ᵐ z ∂(volume.restrict D), DifferentiableAt ℝ F z) :
    (fun z => ‖genDz Fx Fy z‖ ^ 2 + ‖genDzbar Fx Fy z‖ ^ 2) =ᵐ[volume.restrict D]
      (fun z => ‖dz F z‖ ^ 2 + ‖dzbar F z‖ ^ 2) := by
  obtain ⟨_, hx, hy⟩ := lemma9_2_isACL_of_genPartials hD (by norm_num : (1 : ℝ≥0∞) ≤ 2) h
  filter_upwards [hx, hy, hd] with z hzx hzy hzd
  simp only [genDz, genDzbar, dz, dzbar, ← hzx, ← hzy,
    partialX_eq_of_differentiableAt hzd, partialY_eq_of_differentiableAt hzd]

theorem s5qc_target_partials {ψ : ℂ → ℂ} (hψ : ContDiff ℝ 1 ψ) (v : ℂ) :
    MemLp (fun z => fderiv ℝ ψ z v) 2 (volume.restrict unitDisc) := by
  exact (eq22w_cont_memLp
    (((hψ.continuous_fderiv one_ne_zero).clm_apply continuous_const).continuousOn)
    (show closedBall (0 : ℂ) 1 ⊆ univ from subset_univ _) (isCompact_closedBall _ _)).mono_measure
      (Measure.restrict_mono ball_subset_closedBall le_rfl)

/-- Real Dirichlet energy of a genuine weak composition, after proving
the weighted area term integrable through the QC change-of-variables theorem. -/
theorem s5qc_energy {Γ ψ Fx Fy : ℂ → ℂ} {K : ℝ}
    (hΓ : IsKQC Γ unitDisc K) (himage : Γ '' unitDisc = unitDisc)
    (hψ : ContDiff ℝ 1 ψ) (hg : HasGenPartials (ψ ∘ Γ) Fx Fy unitDisc 2)
    (hx : MemLp Fx 2 (volume.restrict unitDisc))
    (hy : MemLp Fy 2 (volume.restrict unitDisc)) :
    (∫ z in unitDisc, ‖Fx z‖ ^ 2 + ‖Fy z‖ ^ 2) ≤
      K * ∫ z in unitDisc, ‖fderiv ℝ ψ z 1‖ ^ 2 + ‖fderiv ℝ ψ z I‖ ^ 2 := by
  have hpx := s5qc_target_partials hψ 1
  have hpy := s5qc_target_partials hψ I
  have hpd : IntegrableOn (fun z => ‖dz ψ z‖ ^ 2) unitDisc :=
    (s5st_wirtinger_memLp hpx hpy).1.integrable_norm_pow (by decide : 2 ≠ 0)
  have hpb : IntegrableOn (fun z => ‖dzbar ψ z‖ ^ 2) unitDisc :=
    (s5st_wirtinger_memLp hpx hpy).2.integrable_norm_pow (by decide : 2 ≠ 0)
  let E : ℂ → ℝ := fun z => ‖dz ψ z‖ ^ 2 + ‖dzbar ψ z‖ ^ 2
  have hEi : IntegrableOn E unitDisc := hpd.add hpb
  have harea := s5qc_area hΓ E
  rw [himage] at harea
  have hweighted : IntegrableOn (fun z => jacobian Γ z * E (Γ z)) unitDisc := harea.1.mp hEi
  have hgd := (s5st_wirtinger_memLp hx hy).1.integrable_norm_pow (by decide : 2 ≠ 0)
  have hgb := (s5st_wirtinger_memLp hx hy).2.integrable_norm_pow (by decide : 2 ≠ 0)
  have hd : ∀ᵐ z ∂(volume.restrict unitDisc), DifferentiableAt ℝ (ψ ∘ Γ) z :=
    (thm9_3_differentiable_ae hΓ).mono fun z hz =>
      (hψ.differentiable one_ne_zero (Γ z)).comp z hz
  have he := s5qc_gen_energy_ae isOpen_ball hg hd
  have hbound : ∀ᵐ z ∂(volume.restrict unitDisc),
      ‖genDz Fx Fy z‖ ^ 2 + ‖genDzbar Fx Fy z‖ ^ 2 ≤ K * (jacobian Γ z * E (Γ z)) := by
    filter_upwards [he, thm9_3_differentiable_ae hΓ, ae_restrict_mem measurableSet_ball]
      with z hez hdz hz
    rw [hez]
    simpa only [E, mul_assoc] using s5qc_pointwise_energy hΓ hz hdz
      (hψ.differentiable one_ne_zero (Γ z))
  have h := integral_mono_ae (hgd.add hgb) (hweighted.const_mul K) hbound
  simp only [Pi.add_apply] at h
  rw [integral_add hgd hgb, s5st_wirtinger_energy hx hy, integral_const_mul, ← harea.2] at h
  have hT : (∫ z in unitDisc, E z) =
      (∫ z in unitDisc, ‖fderiv ℝ ψ z 1‖ ^ 2 + ‖fderiv ℝ ψ z I‖ ^ 2) / 2 := by
    rw [show E = (fun z => ‖dz ψ z‖ ^ 2 + ‖dzbar ψ z‖ ^ 2) from rfl, integral_add hpd hpb]
    exact s5st_wirtinger_energy hpx hpy
  rw [hT] at h
  linarith

/-- The cutoff is used only to construct weak derivatives. The resulting
statement is about the original smooth target and its actual composition. -/
theorem s5qc_smooth_comp {Γ ψ : ℂ → ℂ} {K : ℝ} (hΓ : IsKQC Γ univ K)
    (himage : Γ '' unitDisc = unitDisc) (hψ : ContDiff ℝ 1 ψ) :
    ∃ Fx Fy : ℂ → ℂ, HasGenPartials (ψ ∘ Γ) Fx Fy unitDisc 2 ∧
      MemLp Fx 2 (volume.restrict unitDisc) ∧ MemLp Fy 2 (volume.restrict unitDisc) ∧
      (∫ z in unitDisc, ‖Fx z‖ ^ 2 + ‖Fy z‖ ^ 2) ≤
        K * ∫ z in unitDisc, ‖fderiv ℝ ψ z 1‖ ^ 2 + ‖fderiv ℝ ψ z I‖ ^ 2 := by
  obtain ⟨φ, hφ, hc, he⟩ := eq22w_target_extension isOpen_univ
    (isCompact_closedBall (0 : ℂ) 1) (subset_univ _) hψ.contDiffOn
  obtain ⟨Fx, Fy, hg, hx, hy⟩ := s5qc_compact_chain hΓ hφ hc
  have hg' : HasGenPartials (ψ ∘ Γ) Fx Fy unitDisc 2 := by
    apply s5qc_gen_congr (s5qc_gen_restrict hg (subset_univ _))
    intro z hz
    have hm : Γ z ∈ unitDisc := himage ▸ mem_image_of_mem Γ hz
    exact (he _ (ball_subset_closedBall hm)).eq_of_nhds
  exact ⟨Fx, Fy, hg', hx, hy, s5qc_energy
    (ac_t_isKQC_restrict hΓ isOpen_ball (subset_univ _)) himage hψ hg' hx hy⟩

theorem s5qc_smooth_trace {Γ ψ : ℂ → ℂ} {K : ℝ} (hΓ : IsKQC Γ univ K)
    (himage : Γ '' unitDisc = unitDisc) (hψ : ContDiff ℝ 1 ψ) :
    (ψ ∘ Γ) ∈ HC ∧ (∑' n : ℤ, |(n : ℝ)| * ‖circleCoeff (ψ ∘ Γ) n‖ ^ 2) ≤
      K * ((∫ z in unitDisc, ‖fderiv ℝ ψ z 1‖ ^ 2 + ‖fderiv ℝ ψ z I‖ ^ 2) / (2 * π)) := by
  obtain ⟨Fx, Fy, hg, hx, hy, he⟩ := s5qc_smooth_comp hΓ himage hψ
  have hcΓ : Continuous Γ := continuousOn_univ.mp hΓ.2.2.1.1
  obtain ⟨hHC, ht⟩ := s5st_trace_energy hg (hψ.continuous.comp hcΓ).continuousOn hx hy
  refine ⟨hHC, ht.trans ?_⟩
  simpa only [mul_div_assoc] using div_le_div_of_nonneg_right he
    (by positivity : (0 : ℝ) ≤ 2 * π)

theorem s5qc_extension {γ : ℂ → ℂ} (hγ : IsQSCircleHomeo γ) :
    ∃ K : ℝ, ∃ Γ : ℂ → ℂ, IsKQC Γ univ K ∧ Γ '' unitDisc = unitDisc ∧
      EqOn Γ γ unitCircle := by
  obtain ⟨Γ, ⟨K, hK⟩, hs, hcircle, heq⟩ := circle_quasisymmetric_plane_extension hγ
  have hh : IsHomeomorphOnto Γ univ univ := by simpa only [hs] using hK.2.2.1
  obtain ⟨e, he⟩ := s13x_de_exists_homeomorph hh
  have hcircle' : e '' sphere (0 : ℂ) 1 = sphere (0 : ℂ) 1 := by rw [he]; exact hcircle
  have hd := (planeHomeomorph_circle_regions e hcircle').2.1
  rw [he] at hd
  exact ⟨K, Γ, hK, hd, heq⟩

theorem s5qc_coeff_congr {F G : ℂ → ℂ} (he : EqOn F G unitCircle) (n : ℤ) :
    circleCoeff F n = circleCoeff G n := by
  unfold circleCoeff fourierCoeff
  congr 1
  apply intervalIntegral.integral_congr
  intro θ hθ
  dsimp only
  rw [he (by change ‖exp ((θ : ℂ) * I)‖ = 1; simp [Complex.norm_exp])]

theorem s5qc_HC_congr {F G : ℂ → ℂ} (he : EqOn F G unitCircle) : F ∈ HC ↔ G ∈ HC := by
  have ht : (fun θ : ℝ => F (exp (θ * I))) = (fun θ : ℝ => G (exp (θ * I))) := by
    funext θ
    exact he (by change ‖exp ((θ : ℂ) * I)‖ = 1; simp [Complex.norm_exp])
  simp only [HC, mem_ofPred_eq, ht, s5qc_coeff_congr he]

theorem s5qc_piHat_of_extension {γ Γ ψ : ℂ → ℂ} {K : ℝ}
    (hΓ : IsKQC Γ univ K) (himage : Γ '' unitDisc = unitDisc)
    (he : EqOn Γ γ unitCircle) (hψ : ContDiff ℝ 1 ψ) :
    piHat γ ψ ∈ HC ∧ (∑' n : ℤ, |(n : ℝ)| * ‖circleCoeff (piHat γ ψ) n‖ ^ 2) ≤
      K * ((∫ z in unitDisc, ‖fderiv ℝ ψ z 1‖ ^ 2 + ‖fderiv ℝ ψ z I‖ ^ 2) / (2 * π)) := by
  let c : ℂ := circleCoeff (ψ ∘ γ) 0
  let φ : ℂ → ℂ := fun z => ψ z - c
  have hφ : ContDiff ℝ 1 φ := hψ.sub contDiff_const
  have h := s5qc_smooth_trace hΓ himage hφ
  have hfd (z : ℂ) : fderiv ℝ φ z = fderiv ℝ ψ z := fderiv_sub_const c
  have hfg : EqOn (φ ∘ Γ) (piHat γ ψ) unitCircle := by
    intro z hz
    change ψ (Γ z) - c = ψ (γ z) - c
    rw [he hz]
  refine ⟨(s5qc_HC_congr hfg).mp h.1, ?_⟩
  simpa only [s5qc_coeff_congr hfg, hfd] using h.2

/-- One K works for every C1 target; centering affects neither its true
derivatives nor the nonzero Fourier energy. -/
theorem s5qc_piHat_smooth {γ : ℂ → ℂ} (hγ : IsQSCircleHomeo γ) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ ψ : ℂ → ℂ, ContDiff ℝ 1 ψ →
      piHat γ ψ ∈ HC ∧ (∑' n : ℤ, |(n : ℝ)| * ‖circleCoeff (piHat γ ψ) n‖ ^ 2) ≤
        K * ((∫ z in unitDisc, ‖fderiv ℝ ψ z 1‖ ^ 2 + ‖fderiv ℝ ψ z I‖ ^ 2) / (2 * π)) := by
  obtain ⟨K, Γ, hΓ, hi, he⟩ := s5qc_extension hγ
  exact ⟨K, hΓ.2.1, fun ψ hψ => s5qc_piHat_of_extension hΓ hi he hψ⟩

/-- Positive normalized finite Fourier polynomial, with zero constant term. -/
def s5qc_polynomial (s : Finset ℕ) (x : ℕ → ℂ) : Polynomial ℂ :=
  ∑ n ∈ s, Polynomial.monomial (n + 1) (x n / (Real.sqrt ((n : ℝ) + 1) : ℂ))

/-- The actual harmonic extension of arbitrary positive and negative finite data. -/
def s5qc_harmonic (s : Finset ℕ) (x y : ℕ → ℂ) (z : ℂ) : ℂ :=
  (s5qc_polynomial s x).eval z + conj ((s5qc_polynomial s (fun n => conj (y n))).eval z)

theorem s5qc_polynomial_deriv (s : Finset ℕ) (x : ℕ → ℂ) (z : ℂ) :
    (s5qc_polynomial s x).derivative.eval z =
      ∑ n ∈ s, ((Real.sqrt π : ℂ) * x n) * basisE n z := by
  simp only [s5qc_polynomial, Polynomial.derivative_sum, Polynomial.eval_finsetSum]
  apply Finset.sum_congr rfl
  intro n hn
  simp only [Polynomial.derivative_monomial_succ, Polynomial.eval_monomial, basisE]
  have hπ : (Real.sqrt π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have hn0 : (Real.sqrt ((n : ℝ) + 1) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (by positivity)).ne'
  have hsq : (Real.sqrt ((n : ℝ) + 1) : ℂ) ^ 2 = (n : ℂ) + 1 := by
    exact_mod_cast Real.sq_sqrt (show 0 ≤ (n : ℝ) + 1 by positivity)
  rw [Real.sqrt_div (by positivity), Complex.ofReal_div]
  field_simp
  rw [hsq]

theorem s5qc_polynomial_area (s : Finset ℕ) (x : ℕ → ℂ) :
    (∫ z in unitDisc, ‖(s5qc_polynomial s x).derivative.eval z‖ ^ 2) =
      π * ∑ n ∈ s, ‖x n‖ ^ 2 := by
  let c : ℕ → ℂ := fun n => if n ∈ s then (Real.sqrt π : ℂ) * x n else 0
  have hs (z : ℂ) : HasSum (fun n => c n * basisE n z) ((s5qc_polynomial s x).derivative.eval z) := by
    rw [s5qc_polynomial_deriv]
    have h : HasSum (fun n => c n * basisE n z) (∑ n ∈ s, c n * basisE n z) :=
      hasSum_sum_of_ne_finset_zero (fun n hn => by simp [c, hn])
    simpa [c] using h
  have h := (A21_basis_parseval (polynomial_mem_A21 (s5qc_polynomial s x).derivative)
    (fun z _ => hs z)).tsum_eq
  have hc (n : ℕ) : ‖c n‖ ^ 2 = if n ∈ s then π * ‖x n‖ ^ 2 else 0 := by
    by_cases hn : n ∈ s
    · simp [c, hn, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg π),
        mul_pow, Real.sq_sqrt Real.pi_pos.le]
    · simp [c, hn]
  rw [← h]
  simp only [hc]
  rw [tsum_eq_sum (s := s) (fun n hn => ite_eq_right hn)]
  simp [Finset.mul_sum]

theorem s5qc_harmonic_contDiff (s : Finset ℕ) (x y : ℕ → ℂ) :
    ContDiff ℝ 1 (s5qc_harmonic s x y) := by
  have hp : ContDiff ℝ 1 (fun z => (s5qc_polynomial s x).eval z) :=
    (s5qc_polynomial s x).differentiable.contDiff.restrict_scalars ℝ
  have hq : ContDiff ℝ 1 (fun z => (s5qc_polynomial s (fun n => conj (y n))).eval z) :=
    (s5qc_polynomial s (fun n => conj (y n))).differentiable.contDiff.restrict_scalars ℝ
  exact hp.add ((Complex.conjCLE : ℂ →L[ℝ] ℂ).contDiff.comp hq)

theorem s5qc_polynomial_harmonic_energy (P Q : Polynomial ℂ) :
    (∫ z in unitDisc,
      ‖fderiv ℝ (fun w => P.eval w + conj (Q.eval w)) z 1‖ ^ 2 +
      ‖fderiv ℝ (fun w => P.eval w + conj (Q.eval w)) z I‖ ^ 2) / (2 * π) =
      ((∫ z in unitDisc, ‖P.derivative.eval z‖ ^ 2) +
        (∫ z in unitDisc, ‖Q.derivative.eval z‖ ^ 2)) / π := by
  have hfd (z v : ℂ) : fderiv ℝ (fun w => P.eval w + conj (Q.eval w)) z v =
      P.derivative.eval z * v + conj (Q.derivative.eval z * v) := by
    have hp := (P.differentiable z).restrictScalars ℝ
    have hq := (Q.differentiable z).restrictScalars ℝ
    have hqc : DifferentiableAt ℝ (fun w => conj (Q.eval w)) z :=
      (Complex.conjCLE : ℂ →L[ℝ] ℂ).differentiableAt.comp z hq
    rw [fderiv_fun_add hp hqc, add_apply, fderiv_conj_comp hq,
      fderiv_eq_dz_dzbar hp, fderiv_eq_dz_dzbar hq,
      (cauchyRiemann_iff.mp (P.differentiable z)).2,
      (cauchyRiemann_iff.mp (Q.differentiable z)).2,
      dz_eq_deriv (P.differentiable z), dz_eq_deriv (Q.differentiable z)]
    simp only [zero_mul, add_zero, P.deriv, Q.deriv]
  have he (z : ℂ) :
      ‖fderiv ℝ (fun w => P.eval w + conj (Q.eval w)) z 1‖ ^ 2 +
      ‖fderiv ℝ (fun w => P.eval w + conj (Q.eval w)) z I‖ ^ 2 =
        2 * (‖P.derivative.eval z‖ ^ 2 + ‖Q.derivative.eval z‖ ^ 2) := by
    rw [hfd, hfd]
    simp only [Complex.sq_norm, Complex.normSq_apply, Complex.add_re, Complex.add_im,
      Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im,
      Complex.one_re, Complex.one_im, I_re, I_im]
    ring
  simp_rw [he]
  have hiP : IntegrableOn (fun z => ‖P.derivative.eval z‖ ^ 2) unitDisc :=
    a21_integrable_sq measurableSet_ball (polynomial_mem_A21 P.derivative)
  have hiQ : IntegrableOn (fun z => ‖Q.derivative.eval z‖ ^ 2) unitDisc :=
    a21_integrable_sq measurableSet_ball (polynomial_mem_A21 Q.derivative)
  rw [integral_const_mul, integral_add hiP hiQ]
  field_simp

theorem s5qc_harmonic_energy (s : Finset ℕ) (x y : ℕ → ℂ) :
    (∫ z in unitDisc, ‖fderiv ℝ (s5qc_harmonic s x y) z 1‖ ^ 2 +
      ‖fderiv ℝ (s5qc_harmonic s x y) z I‖ ^ 2) / (2 * π) =
      ∑ n ∈ s, (‖x n‖ ^ 2 + ‖y n‖ ^ 2) := by
  change (∫ z in unitDisc,
    ‖fderiv ℝ (fun w => (s5qc_polynomial s x).eval w +
      conj ((s5qc_polynomial s (fun n => conj (y n))).eval w)) z 1‖ ^ 2 +
    ‖fderiv ℝ (fun w => (s5qc_polynomial s x).eval w +
      conj ((s5qc_polynomial s (fun n => conj (y n))).eval w)) z I‖ ^ 2) / (2 * π) = _
  rw [s5qc_polynomial_harmonic_energy, s5qc_polynomial_area, s5qc_polynomial_area]
  simp only [norm_conj, Finset.sum_add_distrib]
  field_simp

/-- A single actual extension and distortion constant control every finite
frequency combination, with genuine weak derivatives and both frequency signs. -/
theorem s5qc_finite_action {γ : ℂ → ℂ} (hγ : IsQSCircleHomeo γ) :
    ∃ K : ℝ, ∃ Γ : ℂ → ℂ, IsKQC Γ univ K ∧ Γ '' unitDisc = unitDisc ∧
      EqOn Γ γ unitCircle ∧ ∀ s : Finset ℕ, ∀ x y : ℕ → ℂ,
      (∃ Fx Fy : ℂ → ℂ, HasGenPartials (s5qc_harmonic s x y ∘ Γ) Fx Fy unitDisc 2 ∧
        MemLp Fx 2 (volume.restrict unitDisc) ∧ MemLp Fy 2 (volume.restrict unitDisc) ∧
        (∫ z in unitDisc, ‖Fx z‖ ^ 2 + ‖Fy z‖ ^ 2) / (2 * π) ≤
          K * ∑ n ∈ s, (‖x n‖ ^ 2 + ‖y n‖ ^ 2)) ∧
      piHat γ (s5qc_harmonic s x y) ∈ HC ∧
      (∑' n : ℤ, |(n : ℝ)| * ‖circleCoeff (piHat γ (s5qc_harmonic s x y)) n‖ ^ 2) ≤
        K * ∑ n ∈ s, (‖x n‖ ^ 2 + ‖y n‖ ^ 2) := by
  obtain ⟨K, Γ, hΓ, hi, he⟩ := s5qc_extension hγ
  refine ⟨K, Γ, hΓ, hi, he, ?_⟩
  intro s x y
  have hψ := s5qc_harmonic_contDiff s x y
  obtain ⟨Fx, Fy, hg, hx, hy, hE⟩ := s5qc_smooth_comp hΓ hi hψ
  have hB := s5qc_piHat_of_extension hΓ hi he hψ
  rw [s5qc_harmonic_energy] at hB
  refine ⟨⟨Fx, Fy, hg, hx, hy, ?_⟩, hB⟩
  have h := div_le_div_of_nonneg_right hE (by positivity : (0 : ℝ) ≤ 2 * π)
  simpa only [mul_div_assoc, s5qc_harmonic_energy] using h

/-- Explicit finite data compatibility of the actual harmonic polynomial. -/
theorem s5qc_harmonic_sum (s : Finset ℕ) (x y : ℕ → ℂ) (z : ℂ) :
    s5qc_harmonic s x y z =
      ∑ n ∈ s, (x n * z ^ (n + 1) + y n * conj z ^ (n + 1)) /
        (Real.sqrt ((n : ℝ) + 1) : ℂ) := by
  simp only [s5qc_harmonic, s5qc_polynomial, Polynomial.eval_finsetSum,
    Polynomial.eval_monomial, map_sum, map_mul, map_div₀, map_pow, conj_ofReal, conj_conj]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  ring

theorem s5qc_harmonic_circle (s : Finset ℕ) (x y : ℕ → ℂ) {z : ℂ}
    (hz : z ∈ unitCircle) :
    s5qc_harmonic s x y z =
      ∑ n ∈ s, (x n * z ^ (n + 1) + y n * z ^ (-(n + 1 : ℤ))) /
        (Real.sqrt ((n : ℝ) + 1) : ℂ) := by
  rw [s5qc_harmonic_sum, ← Complex.inv_eq_conj hz]
  apply Finset.sum_congr rfl
  intro n hn
  have hp : (z⁻¹) ^ (n + 1) = z ^ (-(n + 1 : ℤ)) := by
    rw [show (n + 1 : ℤ) = ((n + 1 : ℕ) : ℤ) by omega, zpow_neg, zpow_natCast, inv_pow]
  rw [hp]

end TakhtajanTeo.Ch2
