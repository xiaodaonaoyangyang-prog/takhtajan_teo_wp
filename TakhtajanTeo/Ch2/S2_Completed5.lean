import TakhtajanTeo.Ch2.S2_Completed

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal ComplexConjugate Classical Real
noncomputable section
namespace TakhtajanTeo
open LiZhongQC
namespace Ch2

/-- `∬_{|ω - ζ| ≥ d} |ω - ζ|⁻⁴ d²ω = π/d²`. -/
theorem s2c_l4_outside_ball (ζ : ℂ) {d : ℝ} (hd : 0 < d) :
    IntegrableOn (fun ω : ℂ => (‖ω - ζ‖ ^ 4)⁻¹) {ω | d ≤ ‖ω - ζ‖} ∧
      ∫ ω in {ω : ℂ | d ≤ ‖ω - ζ‖}, (‖ω - ζ‖ ^ 4)⁻¹ = π / d ^ 2 := by
  let f : ℝ → ℝ := (Set.Ici d).indicator (fun y => (y ^ 4)⁻¹)
  have hF : ∀ ω : ℂ, f ‖ω - ζ‖ = ({ω : ℂ | d ≤ ‖ω - ζ‖}).indicator (fun ω => (‖ω - ζ‖ ^ 4)⁻¹) ω := by
    intro ω
    by_cases h : d ≤ ‖ω - ζ‖
    · simp [f, h]
    · simp [f, h]
  have hg : EqOn (fun y : ℝ => y ^ (Module.finrank ℝ ℂ - 1) • f y)
      ((Set.Ici d).indicator (fun y : ℝ => y ^ (-3 : ℝ))) (Ioi 0) := by
    intro y hy
    have hy0 : (0 : ℝ) < y := hy
    by_cases h : d ≤ y
    · simp only [f, Set.indicator_of_mem (show y ∈ Ici d from h), Complex.finrank_real_complex,
        smul_eq_mul]
      rw [Real.rpow_neg hy0.le]
      rw [show (y : ℝ) ^ (3 : ℝ) = y ^ 3 by exact_mod_cast Real.rpow_natCast y 3]
      rw [show (2 - 1 : ℕ) = 1 by norm_num, pow_one]
      field_simp
    · simp [f, Set.indicator_of_notMem (show y ∉ Ici d from h)]
  have hIci : IntegrableOn (fun y : ℝ => y ^ (-3 : ℝ)) (Ici d) := by
    rw [integrableOn_Ici_iff_integrableOn_Ioi]
    exact integrableOn_Ioi_rpow_of_lt (by norm_num) hd
  have hint : IntegrableOn (fun y : ℝ => y ^ (Module.finrank ℝ ℂ - 1) • f y) (Ioi 0) :=
    ((hIci.integrable_indicator measurableSet_Ici).integrableOn).congr_fun hg.symm measurableSet_Ioi
  have hmeas : MeasurableSet {ω : ℂ | d ≤ ‖ω - ζ‖} :=
    measurableSet_le measurable_const (measurable_norm.comp (measurable_id.sub_const ζ))
  have hI : Integrable (fun x : ℂ => f ‖x‖) := (integrable_fun_norm_addHaar volume).2 hint
  have hI' : Integrable (fun ω : ℂ => f ‖ω - ζ‖) := hI.comp_sub_right ζ
  refine ⟨?_, ?_⟩
  · refine (integrable_indicator_iff hmeas).1 ?_
    have heq : (fun ω : ℂ => f ‖ω - ζ‖) =
        ({ω : ℂ | d ≤ ‖ω - ζ‖}).indicator (fun ω => (‖ω - ζ‖ ^ 4)⁻¹) := funext hF
    rw [heq] at hI'
    exact hI'
  · have hJ : ∫ y in Ioi (0 : ℝ), (Set.Ici d).indicator (fun y : ℝ => y ^ (-3 : ℝ)) y =
        1 / (2 * d ^ 2) := by
      have hset : Ici d ∩ Ioi (0 : ℝ) = Ici d :=
        Set.inter_eq_left.2 (fun x (hx : d ≤ x) => lt_of_lt_of_le hd hx)
      rw [integral_indicator measurableSet_Ici, Measure.restrict_restrict measurableSet_Ici, hset,
        integral_Ici_eq_integral_Ioi, integral_Ioi_rpow_of_lt (by norm_num) hd]
      rw [show (-3 : ℝ) + 1 = -2 by norm_num, Real.rpow_neg hd.le,
        show d ^ (2 : ℝ) = d ^ 2 by exact_mod_cast Real.rpow_natCast d 2]
      field_simp
    rw [← integral_indicator hmeas]
    simp only [← hF]
    rw [integral_sub_right_eq_self (fun x : ℂ => f ‖x‖) ζ, integral_fun_norm_addHaar,
      setIntegral_congr_fun measurableSet_Ioi hg, hJ, Complex.finrank_real_complex]
    have hb : volume.real (ball (0 : ℂ) 1) = π := by
      simp [Measure.real, Complex.volume_ball]
    rw [hb]
    simp
    field_simp


/-- The `1/ζ`-chart of the exterior: `φ/b` maps `𝔻` onto `(1/·)(Ω*) ∪ {0}`. -/
theorem s2c_chart_eq {g φ : ℂ → ℂ} {b : ℂ} (hφi : InjOn φ unitDisc) (hφ0 : φ 0 = 0) (hb : b ≠ 0)
    (hg : ∀ s ∈ unitDisc, s ≠ 0 → g (1 / s) = b / φ s) :
    (fun s => φ s / b) '' unitDisc = (fun w : ℂ => w⁻¹) '' (g '' unitDiscExterior) ∪ {0} := by
  have hne : ∀ s ∈ unitDisc, s ≠ 0 → φ s ≠ 0 := fun s hs hs0 h =>
    hs0 (hφi hs (mem_ball_self one_pos) (h.trans hφ0.symm))
  have hext : ∀ s ∈ unitDisc, s ≠ 0 → 1 / s ∈ unitDiscExterior := by
    intro s hs hs0
    have hsn : ‖s‖ < 1 := mem_ball_zero_iff.mp hs
    have hpos : 0 < ‖s‖ := norm_pos_iff.mpr hs0
    show 1 < ‖1 / s‖
    rw [norm_div, norm_one, lt_div_iff₀ hpos]
    linarith
  have hdisc : ∀ u ∈ unitDiscExterior, 1 / u ∈ unitDisc ∧ 1 / u ≠ 0 := by
    intro u hu
    have hu1 : 1 < ‖u‖ := hu
    have hu0 : u ≠ 0 := fun h => by simp [h] at hu1; linarith
    refine ⟨?_, one_div_ne_zero hu0⟩
    refine mem_ball_zero_iff.2 ?_
    rw [norm_div, norm_one]
    exact (div_lt_one (by linarith)).2 hu1
  ext ζ
  constructor
  · rintro ⟨s, hs, rfl⟩
    by_cases hs0 : s = 0
    · subst hs0
      simp [hφ0]
    · left
      refine ⟨g (1 / s), ⟨1 / s, hext s hs hs0, rfl⟩, ?_⟩
      show (g (1 / s))⁻¹ = φ s / b
      have hφne : φ s ≠ 0 := fun h => hs0 (hφi hs (mem_ball_self one_pos) (h.trans hφ0.symm))
      rw [hg s hs hs0]
      field_simp
  · rintro (⟨w, ⟨u, hu, rfl⟩, rfl⟩ | h)
    · obtain ⟨hsD, hs0⟩ := hdisc u hu
      refine ⟨1 / u, hsD, ?_⟩
      show φ (1 / u) / b = (g u)⁻¹
      have hφne : φ (1 / u) ≠ 0 :=
        fun h => hs0 (hφi hsD (mem_ball_self one_pos) (h.trans hφ0.symm))
      have h1 := hg (1 / u) hsD hs0
      rw [one_div_one_div] at h1
      rw [h1]
      field_simp
    · rw [Set.mem_singleton_iff.1 h]
      exact ⟨0, mem_ball_self one_pos, by simp [hφ0]⟩

/-- **(2.8)** (TT:4133). For `Ω = 𝖿(𝔻)`, `Ω* = 𝗀(𝔻*)` and `z ∈ Ω*`: `∬_Ω d²w/|w - z|⁴ ≤ 4π ρ₂(z)`, where
`ρ₂ = λ_{Ω*}²` is the hyperbolic density of `Ω*`.

[CORRECTION 2026-10-25] `λ_{Ω*}` is computed in the sphere chart `1/z` (`poincareDensityNearInfty`): `Ω*` contains a
neighbourhood of `∞`, and `LiZhongQC.poincareDensity` of it is junk `0`. 
Proved here as `s2c_eq_2_8`; statement identical to `eq_2_8`. -/
theorem s2c_eq_2_8 {μ : LinfStar} (hμ : μ ∈ LinfStarBall) {z : ℂ} (hz : z ∈ gsans μ '' unitDiscExterior) :
    ∫ w in fsans μ '' unitDisc, 1 / ‖w - z‖ ^ 4 ≤
      4 * π * poincareDensityNearInfty (gsans μ '' unitDiscExterior) z ^ 2 := by
  have hpair := AppB.b8_welding_normalized_pair hμ
  obtain ⟨φ, b, hφd, hφi, hφ0, -, hb, -, hg⟩ := g1_inverted_exterior hpair
  obtain ⟨hfd, hfi, hf0, -, -, hdisj⟩ := hpair
  have hgne : ∀ u ∈ unitDiscExterior, gsans μ u ≠ 0 := by
    intro u hu h
    exact Set.disjoint_left.mp hdisj ⟨0, mem_ball_self one_pos, hf0⟩ ⟨u, hu, h⟩
  have hGeq := s2c_chart_eq (g := gsans μ) hφi hφ0 hb hg
  set G : Set ℂ := (fun s => φ s / b) '' unitDisc with hGdef
  have hψ : IsConformalOnto (fun s => φ s / b) unitDisc G :=
    ⟨hφd.div_const b, fun x hx y hy h => hφi hx hy ((div_left_inj' hb).1 h), rfl⟩
  have hGopen : IsOpen G := hψ.isOpen isOpen_ball
  have hψs : IsConformalOnto (Function.invFunOn (fun s => φ s / b) unitDisc) G unitDisc :=
    hψ.symm isOpen_ball
  rcases hz with ⟨u, hu, rfl⟩
  have hu0 : gsans μ u ≠ 0 := hgne u hu
  set z : ℂ := gsans μ u with hzdef
  set ζ : ℂ := z⁻¹ with hζ
  have hζ0 : ζ ≠ 0 := inv_ne_zero hu0
  have hzζ : ζ⁻¹ = z := inv_inv z
  have hζG : ζ ∈ G := by
    rw [hGeq]
    exact Or.inl ⟨z, ⟨u, hu, rfl⟩, rfl⟩
  have hdens : poincareDensityNearInfty (gsans μ '' unitDiscExterior) z =
      poincareDensity G ζ / ‖z‖ ^ 2 := by
    unfold poincareDensityNearInfty
    rw [← hGeq]
  have hf12 : (1 / 2 : ℂ) ∈ unitDisc := by
    refine mem_ball_zero_iff.2 ?_
    norm_num
  have hGc : (Gᶜ).Nonempty := by
    refine ⟨(fsans μ (1 / 2))⁻¹, ?_⟩
    have hne : fsans μ (1 / 2) ≠ 0 := fun h => by
      have := hfi hf12 (mem_ball_self one_pos) (h.trans hf0.symm)
      norm_num at this
    intro hG
    rw [hGeq] at hG
    rcases hG with ⟨w, ⟨u', hu', hw⟩, h⟩ | h
    · exact Set.disjoint_left.mp hdisj ⟨1 / 2, hf12, rfl⟩ ⟨u', hu', hw.trans (inv_injective h)⟩
    · exact hne (inv_eq_zero.1 (Set.mem_singleton_iff.1 h))
  have hclosed : IsClosed Gᶜ := hGopen.isClosed_compl
  have hd0 : 0 < Metric.infDist ζ Gᶜ :=
    (hclosed.notMem_iff_infDist_pos hGc).1 (by simpa using hζG)
  set d : ℝ := Metric.infDist ζ Gᶜ with hd
  have hlow : ∀ w' ∈ Gᶜ, 1 / (2 * ‖w' - ζ‖) ≤ poincareDensity G ζ := fun w' hw' =>
    t203_density_ge hGopen hψs hζG hw'
  set lam : ℝ := poincareDensity G ζ with hlam
  have hne' : ∀ w' ∈ Gᶜ, ‖w' - ζ‖ ≠ 0 := fun w' hw' =>
    norm_ne_zero_iff.2 (sub_ne_zero.2 (fun h => hw' (h ▸ hζG)))
  have hlpos : 0 < lam := by
    obtain ⟨w', hw'⟩ := hGc
    have h1 := hlow w' hw'
    have : 0 < 1 / (2 * ‖w' - ζ‖) := by
      have := hne' w' hw'
      positivity
    linarith
  have hlam2 : 1 / (2 * d) ≤ lam := by
    by_contra hcon
    push Not at hcon
    have hd' : d < 1 / (2 * lam) := by
      rw [lt_div_iff₀ (by positivity)]
      have := (lt_div_iff₀ (by positivity : 0 < 2 * d)).1 hcon
      linarith
    obtain ⟨w', hw', hdist⟩ := (Metric.infDist_lt_iff hGc).1 hd'
    have h1 := hlow w' hw'
    rw [dist_eq_norm, norm_sub_rev] at hdist
    have hr : 0 < ‖w' - ζ‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm (hne' w' hw'))
    have h2 : lam < 1 / (2 * ‖w' - ζ‖) := by
      rw [lt_div_iff₀ (by positivity)]
      have := (lt_div_iff₀ (by positivity : 0 < 2 * lam)).1 hdist
      linarith
    linarith
  -- the integral over `Ω = f(𝔻)`
  set Ω : Set ℂ := fsans μ '' unitDisc with hΩ
  have hΩopen : IsOpen Ω :=
    (show IsConformalOnto (fsans μ) unitDisc Ω from ⟨hfd, hfi, rfl⟩).isOpen isOpen_ball
  have e1 : ∫ w in Ω, 1 / ‖w - z‖ ^ 4 = ∫ w in Ω \ {0}, 1 / ‖w - z‖ ^ 4 :=
    setIntegral_congr_set (sdiff_null_ae_eq_self (measure_singleton 0)).symm
  set Ω' : Set ℂ := (fun w : ℂ => w⁻¹) '' (Ω \ {0}) with hΩ'
  have himg : (fun w : ℂ => w⁻¹) '' Ω' = Ω \ {0} := by
    rw [hΩ', Set.image_image]
    simp
  have hΩ'meas : MeasurableSet Ω' := by
    rw [hΩ', Set.image_eq_preimage_of_inverse (f := fun w : ℂ => w⁻¹) (g := fun w : ℂ => w⁻¹)
      (fun x => inv_inv x) (fun x => inv_inv x)]
    exact (hΩopen.measurableSet.diff (measurableSet_singleton _)).preimage measurable_inv
  have hΩ'ne : ∀ ω ∈ Ω', ω ≠ 0 := by
    rintro ω ⟨w, hw, rfl⟩
    exact inv_ne_zero hw.2
  have hΩ'G : ∀ ω ∈ Ω', ω ∈ Gᶜ := by
    rintro ω ⟨w, hw, rfl⟩ hG
    rw [hGeq] at hG
    rcases hG with ⟨w', ⟨u', hu', hw'⟩, h⟩ | h
    · have : w' = w := inv_injective h
      exact Set.disjoint_left.mp hdisj hw.1 ⟨u', hu', hw'.trans this⟩
    · exact hw.2 (inv_eq_zero.1 (Set.mem_singleton_iff.1 h))
  have e2 : ∫ w in Ω \ {0}, 1 / ‖w - z‖ ^ 4 =
      ∫ ω in Ω', ‖deriv (fun x : ℂ => x⁻¹) ω‖ ^ 2 • (1 / ‖ω⁻¹ - z‖ ^ 4) := by
    conv_lhs => rw [← himg]
    rw [integral_image_eq_integral_abs_det_fderiv_smul volume hΩ'meas
      (fun ω hω => ((differentiableAt_inv (hΩ'ne ω hω)).hasDerivAt.hasFDerivAt.restrictScalars
        ℝ).hasFDerivWithinAt) (fun a _ b _ h => inv_injective h)]
    refine setIntegral_congr_fun hΩ'meas fun ω hω => ?_
    simp only [det_restrictScalars_toSpanSingleton]
    rw [abs_of_nonneg (sq_nonneg _)]
  have e3 : ∀ ω ∈ Ω', ‖deriv (fun x : ℂ => x⁻¹) ω‖ ^ 2 • (1 / ‖ω⁻¹ - z‖ ^ 4) =
      ‖ζ‖ ^ 4 * (‖ω - ζ‖ ^ 4)⁻¹ := by
    intro ω hω
    have hω0 := hΩ'ne ω hω
    have hωζ : ‖ω - ζ‖ ≠ 0 := by
      have := hΩ'G ω hω
      exact norm_ne_zero_iff.2 (sub_ne_zero.2 (fun h => this (h ▸ hζG)))
    have hn : ‖ω⁻¹ - z‖ = ‖ω - ζ‖ / (‖ω‖ * ‖ζ‖) := by
      rw [← hzζ, show ω⁻¹ - ζ⁻¹ = (ζ - ω) / (ω * ζ) by field_simp, norm_div, norm_mul, norm_sub_rev]
    rw [deriv_inv', norm_neg, norm_inv, norm_pow, hn, smul_eq_mul]
    have h1 : ‖ω‖ ≠ 0 := norm_ne_zero_iff.2 hω0
    have h2 : ‖ζ‖ ≠ 0 := norm_ne_zero_iff.2 hζ0
    field_simp
  rw [hdens, e1, e2, setIntegral_congr_fun hΩ'meas e3]
  obtain ⟨hI, hV⟩ := s2c_l4_outside_ball ζ hd0
  have hsub : Ω' ⊆ {ω : ℂ | d ≤ ‖ω - ζ‖} := by
    intro ω hω
    have h := Metric.infDist_le_dist_of_mem (x := ζ) (hΩ'G ω hω)
    show d ≤ ‖ω - ζ‖
    rw [dist_eq_norm, norm_sub_rev] at h
    exact h
  have hle : ∫ ω in Ω', ‖ζ‖ ^ 4 * (‖ω - ζ‖ ^ 4)⁻¹ ≤
      ∫ ω in {ω : ℂ | d ≤ ‖ω - ζ‖}, ‖ζ‖ ^ 4 * (‖ω - ζ‖ ^ 4)⁻¹ :=
    setIntegral_mono_set (hI.const_mul _) (Filter.Eventually.of_forall fun ω => by positivity)
      (Filter.Eventually.of_forall hsub)
  simp only [integral_const_mul] at hle
  rw [hV] at hle
  rw [integral_const_mul]
  refine hle.trans ?_
  have hz2 : ‖z‖ ≠ 0 := norm_ne_zero_iff.2 hu0
  have hζn : ‖ζ‖ = ‖z‖⁻¹ := by rw [hζ, norm_inv]
  have hlam3 : 1 / d ≤ 2 * lam := by
    have := hlam2
    rw [div_le_iff₀ (by positivity)] at this ⊢
    nlinarith
  have hpos : 0 < ‖z‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz2)
  have key : π / d ^ 2 ≤ 4 * π * lam ^ 2 := by
    have h1 : (1 / d) ^ 2 ≤ (2 * lam) ^ 2 := pow_le_pow_left₀ (by positivity) hlam3 2
    have h2 : π / d ^ 2 = π * (1 / d) ^ 2 := by field_simp
    rw [h2]
    nlinarith [Real.pi_pos]
  calc ‖ζ‖ ^ 4 * (π / d ^ 2) ≤ ‖ζ‖ ^ 4 * (4 * π * lam ^ 2) :=
        mul_le_mul_of_nonneg_left key (by positivity)
    _ = 4 * π * (lam / ‖z‖ ^ 2) ^ 2 := by
        rw [hζn]
        field_simp

/-! ### Original relocated (2026-10-26) -/

/-- **(2.8)** (TT:4133). For `Ω = 𝖿(𝔻)`, `Ω* = 𝗀(𝔻*)` and `z ∈ Ω*`: `∬_Ω d²w/|w - z|⁴ ≤ 4π ρ₂(z)`, where
`ρ₂ = λ_{Ω*}²` is the hyperbolic density of `Ω*`.

[CORRECTION 2026-10-25] `λ_{Ω*}` is computed in the sphere chart `1/z` (`poincareDensityNearInfty`): `Ω*` contains a
neighbourhood of `∞`, and `LiZhongQC.poincareDensity` of it is junk `0`. -/
theorem eq_2_8 {μ : LinfStar} (hμ : μ ∈ LinfStarBall) {z : ℂ} (hz : z ∈ gsans μ '' unitDiscExterior) :
    ∫ w in fsans μ '' unitDisc, 1 / ‖w - z‖ ^ 4 ≤
      4 * π * poincareDensityNearInfty (gsans μ '' unitDiscExterior) z ^ 2 :=
  s2c_eq_2_8 hμ hz

end Ch2

end TakhtajanTeo
