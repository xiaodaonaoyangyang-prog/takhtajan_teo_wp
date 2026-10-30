import TakhtajanTeo.Ch1.S8PeterssonConditional
import TakhtajanTeo.Ch1.BeltramiRealAnalytic
import TakhtajanTeo.Ch1.GroupBaseSequence

/-!
# §8: Lemma 8.4, conditional on Lemma 1.9 (`s8w_` prefix)

`lemma_8_4` (S8) is proved from the conclusion of `lemma_1_9` for the given group (hypothesis `hL`, as in
`s8c_petersson_average`). Once `lemma_1_9` is proved, `hL := fun hm hb ha => lemma_1_9 hΓ hm hb ha`.

Route (TT:3304–3349), with `w = w_κ`, `Λ = P(R(μ, κ))` and
`λ(v) = Λ(w v) \overline{w_v(v)}² ρ(w v)/ρ(v)`:
- **K** facts on `w_κ` for small harmonic `κ`: homeomorphism of `ℂ` preserving `𝔻`, `C¹` on `𝔻` with `w_z̄ = κ w_z`,
  change of variables, the density bound `ρ(w)|w_z|² ≤ Cρ` (TT's `w_κ^*ρ ≤ (3/2)ρ`), `Γ`-equivariance.
- **P** facts on the projector: `L¹(ρ)`-boundedness, symmetry, harmonicity, `Γ`-equivariance, and self-adjointness over a
  fundamental domain.
- **A** the inner limit `s → 1` equals `∬ P(λ)_r ν̄_r ρ`; Lemma 1.9 (via `s8c_petersson_average`) gives
  `(P λ, ν)_Γ`, which is `g_{μν̄}(κ)` by two quotient self-adjointness steps (for `Γ` and for `Γ_κ`).
-/

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal ComplexConjugate Classical Real

noncomputable section

namespace TakhtajanTeo

open LiZhongQC

/-- The reflection of `κ` to `𝔻*`, `\overline{κ(1/z̄)} z²/z̄²`, is bounded by `k` there and essentially bounded. -/
theorem s8w_fk_memLp {κ : ℂ → ℂ} (hκ : IsHarmonicD κ) {k : ℝ} (hk : ∀ z ∈ unitDisc, ‖κ z‖ ≤ k) :
    MemLp (fun z => conj (κ (refl z)) * z ^ 2 / conj z ^ 2) ∞ (volume.restrict unitDiscExterior) ∧
      ∀ z ∈ unitDiscExterior, ‖conj (κ (refl z)) * z ^ 2 / conj z ^ 2‖ ≤ k := by
  have hEm : MeasurableSet unitDiscExterior := (isOpen_lt continuous_const continuous_norm).measurableSet
  have hmaps : MapsTo refl unitDiscExterior unitDisc := fun z hz =>
    (refl_mem_disc_iff (fdr_ne_zero_of_exterior hz)).mpr hz
  have hb : ∀ z ∈ unitDiscExterior, ‖conj (κ (refl z)) * z ^ 2 / conj z ^ 2‖ ≤ k := by
    intro z hz
    have hz0 := fdr_ne_zero_of_exterior hz
    rw [norm_div, norm_mul, Complex.norm_conj, norm_pow, norm_pow, Complex.norm_conj,
      mul_div_assoc, div_self (pow_ne_zero 2 (norm_ne_zero_iff.mpr hz0)), mul_one]
    exact hk _ (hmaps hz)
  have hrc : ContinuousOn refl unitDiscExterior := by
    have : refl = fun z : ℂ => (conj z)⁻¹ := rfl
    rw [this]
    exact Complex.continuous_conj.continuousOn.inv₀ fun z hz =>
      (map_ne_zero _).mpr (fdr_ne_zero_of_exterior hz)
  have hc : ContinuousOn (fun z => conj (κ (refl z)) * z ^ 2 / conj z ^ 2) unitDiscExterior := by
    refine ((Complex.continuous_conj.comp_continuousOn ((harmonicD_continuousOn hκ).comp hrc hmaps)).mul
      (continuousOn_id.pow 2)).div (Complex.continuous_conj.continuousOn.pow 2) ?_
    intro z hz
    exact pow_ne_zero 2 ((map_ne_zero _).mpr (fdr_ne_zero_of_exterior hz))
  exact ⟨memLp_top_of_bound (hc.aestronglyMeasurable hEm) k
    ((ae_restrict_iff' hEm).mpr (Eventually.of_forall hb)), hb⟩

/-- The Model A extension of the reflected coefficient is `extD κ` almost everywhere. -/
theorem s8w_extA_fk {κ : ℂ → ℂ} (hκ : IsHarmonicD κ) {k : ℝ} (hk : ∀ z ∈ unitDisc, ‖κ z‖ ≤ k) :
    extA (toLinf (fun z => conj (κ (refl z)) * z ^ 2 / conj z ^ 2)) =ᵐ[volume] extD κ := by
  set f : ℂ → ℂ := fun z => conj (κ (refl z)) * z ^ 2 / conj z ^ 2 with hf
  have hEm : MeasurableSet unitDiscExterior := (isOpen_lt continuous_const continuous_norm).measurableSet
  have hae := bc_toLinf_ae (s8w_fk_memLp hκ hk).1
  have h1 : ∀ᵐ y, y ∈ unitDiscExterior → (toLinf f : ℂ → ℂ) y = f y := (ae_restrict_iff' hEm).mp hae
  have h2 := ae_refl h1
  have h0 : ∀ᵐ z : ℂ, z ∈ ({0} : Set ℂ)ᶜ := compl_mem_ae_iff.mpr (measure_singleton 0)
  filter_upwards [h1, h2, h0] with z hz1 hz2 hz0
  have hz0' : z ≠ 0 := hz0
  unfold extA extD
  by_cases hE : 1 < ‖z‖
  · rw [if_pos hE, if_neg (by linarith : ¬ ‖z‖ < 1), if_pos hE]
    exact hz1 hE
  · by_cases hD : ‖z‖ < 1
    · rw [if_neg hE, if_pos hD, if_pos hD]
      have hrE : refl z ∈ unitDiscExterior :=
        (refl_mem_exterior_iff hz0').mpr (mem_ball_zero_iff.mpr hD)
      rw [hz2 hrE]
      simp only [hf, refl_involutive z]
      simp only [refl, map_div₀, map_mul, map_pow, map_inv₀, Complex.conj_conj]
      have hc : conj z ≠ 0 := (map_ne_zero _).mpr hz0'
      field_simp
    · rw [if_neg hE, if_neg hD, if_neg hE, if_neg hD]

/-- `w_κ` is the normalized solution of `extD κ`, also of the Model A extension of the reflected coefficient, and is
unique. -/
theorem s8w_wD_normalized {κ : ℂ → ℂ} (hκ : IsHarmonicD κ) {k : ℝ} (hk1 : k < 1)
    (hk : ∀ z ∈ unitDisc, ‖κ z‖ ≤ k) :
    toLinf (fun z => conj (κ (refl z)) * z ^ 2 / conj z ^ 2) ∈ LinfStarBall ∧
      IsNormalizedSolution (wD κ) (extD κ) ∧
      IsNormalizedSolution (wD κ) (extA (toLinf (fun z => conj (κ (refl z)) * z ^ 2 / conj z ^ 2))) ∧
      ∀ V, IsNormalizedSolution V (extD κ) → V = wD κ := by
  set f : ℂ → ℂ := fun z => conj (κ (refl z)) * z ^ 2 / conj z ^ 2 with hf
  have hk0 : 0 ≤ k := (norm_nonneg _).trans (hk 0 (by simp [unitDisc]))
  obtain ⟨-, hb⟩ := s8w_fk_memLp hκ hk
  have hEm : MeasurableSet unitDiscExterior := (isOpen_lt continuous_const continuous_norm).measurableSet
  have hball : toLinf f ∈ LinfStarBall := by
    have := norm_toLinf_le_of_ae_bound hk0 ((ae_restrict_iff' hEm).mpr (Eventually.of_forall hb))
    exact mem_ball_zero_iff.mpr (this.trans_lt hk1)
  have hae := s8w_extA_fk hκ hk
  obtain ⟨W, hW, -, huniq⟩ := extA_normalized_plane_exists hball
  have conv : ∀ V : ℂ → ℂ, IsNormalizedSolution V (extA (toLinf f)) ↔ IsNormalizedSolution V (extD κ) := by
    intro V
    constructor
    · rintro ⟨h1, h2, h3, h4, h5⟩
      exact ⟨h1, h2, h3, h4, by filter_upwards [h5, hae] with z a b; rw [a, b]⟩
    · rintro ⟨h1, h2, h3, h4, h5⟩
      exact ⟨h1, h2, h3, h4, by filter_upwards [h5, hae] with z a b; rw [a, b]⟩
  have hex : ∃ w, IsNormalizedFix (extD κ) w := ⟨W, (conv W).mp hW⟩
  have hwD : IsNormalizedSolution (wD κ) (extD κ) := by
    have h : IsNormalizedFix (extD κ) (wD κ) := by
      unfold wD
      rw [dif_pos hex]
      exact hex.choose_spec
    exact h
  refine ⟨hball, hwD, (conv _).mpr hwD, fun V hV => ?_⟩
  rw [huniq V ((conv V).mpr hV), huniq _ ((conv _).mpr hwD)]

/-- `|z|²` as a complex number is real-analytic. -/
theorem s8w_normSq_analytic (z : ℂ) : AnalyticAt ℝ (fun x : ℂ => ((‖x‖ : ℂ)) ^ 2) z := by
  have e : (fun x : ℂ => ((‖x‖ : ℂ)) ^ 2) = fun x => x * conj x := by
    funext x
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
    push_cast
    ring
  rw [e]
  exact analyticAt_id.mul (Complex.conjCLE.toContinuousLinearMap.analyticAt z)

/-- A harmonic Beltrami differential on `𝔻` is real-analytic there. -/
theorem s8w_harmD_analytic {κ : ℂ → ℂ} (hκ : IsHarmonicD κ) : AnalyticOnNhd ℝ κ unitDisc := by
  obtain ⟨φ, hφ, -, hκφ⟩ := hκ
  have hφa : AnalyticOnNhd ℂ φ unitDisc := hφ.analyticOnNhd isOpen_ball
  intro z hz
  have h1 : AnalyticAt ℝ (fun x : ℂ => (1 - (‖x‖ : ℂ) ^ 2) ^ 2 * conj (φ x)) z := by
    have hc : AnalyticAt ℝ (fun x => conj (φ x)) z :=
      (Complex.conjCLE.toContinuousLinearMap.analyticAt _).comp ((hφa z hz).restrictScalars)
    exact ((analyticAt_const.sub (s8w_normSq_analytic z)).pow 2).mul hc
  refine h1.congr ?_
  filter_upwards [isOpen_ball.mem_nhds hz] with x hx
  exact (hκφ x hx).symm

/-- On `𝔻`, `w_κ` is real-analytic with `(w_κ)_z ≠ 0`, and its complex dilatation is `κ` everywhere on `𝔻`. -/
theorem s8w_wD_analytic {κ : ℂ → ℂ} (hκ : IsHarmonicD κ) {k : ℝ} (hk1 : k < 1)
    (hk : ∀ z ∈ unitDisc, ‖κ z‖ ≤ k) :
    ∀ z ∈ unitDisc, AnalyticAt ℝ (wD κ) z ∧ dz (wD κ) z ≠ 0 ∧ complexDilatation (wD κ) z = κ z := by
  obtain ⟨-, hN, -, -⟩ := s8w_wD_normalized hκ hk1 hk
  obtain ⟨⟨K, hK⟩, -, -, -, hdil⟩ := hN
  have hKD : IsKQC (wD κ) unitDisc K := nx_isKQC_restrict hK isOpen_ball (subset_univ _)
  have hDm : MeasurableSet unitDisc := measurableSet_ball
  have hfg : ∀ᵐ z ∂(volume.restrict unitDisc), complexDilatation (wD κ) z = κ z := by
    filter_upwards [ae_restrict_of_ae hdil, ae_restrict_mem hDm] with z hz hzD
    rw [hz]
    have hz1 : ‖z‖ < 1 := mem_ball_zero_iff.mp hzD
    simp [extD, hz1]
  have ha := ra_qc_analytic hKD (s8w_harmD_analytic hκ) hfg
  have hcont : ContinuousOn (complexDilatation (wD κ)) unitDisc := by
    intro z hz
    obtain ⟨hza, hzd⟩ := ha z hz
    have hev : ∀ᶠ x in 𝓝 z, AnalyticAt ℝ (wD κ) x ∧ dz (wD κ) x ≠ 0 := by
      filter_upwards [isOpen_ball.mem_nhds hz] with x hx
      exact ha x hx
    have hdz : ContinuousAt (dz (wD κ)) z := by
      have hfd : ContinuousAt (fderiv ℝ (wD κ)) z := (hza.fderiv).continuousAt
      have : dz (wD κ) = fun x => (fderiv ℝ (wD κ) x 1 - I * fderiv ℝ (wD κ) x I) / 2 := rfl
      rw [this]
      exact ((hfd.clm_apply continuousAt_const).sub
        (continuousAt_const.mul (hfd.clm_apply continuousAt_const))).div_const 2
    have hdzb : ContinuousAt (dzbar (wD κ)) z := by
      have hfd : ContinuousAt (fderiv ℝ (wD κ)) z := (hza.fderiv).continuousAt
      have : dzbar (wD κ) = fun x => (fderiv ℝ (wD κ) x 1 + I * fderiv ℝ (wD κ) x I) / 2 := rfl
      rw [this]
      exact ((hfd.clm_apply continuousAt_const).add
        (continuousAt_const.mul (hfd.clm_apply continuousAt_const))).div_const 2
    exact (hdzb.div hdz hzd).continuousWithinAt
  have heq : EqOn (complexDilatation (wD κ)) κ unitDisc :=
    Measure.eqOn_open_of_ae_eq hfg isOpen_ball hcont (harmonicD_continuousOn hκ)
  exact fun z hz => ⟨(ha z hz).1, (ha z hz).2, heq hz⟩

/-- The reflected coefficient is a harmonic Beltrami differential on `𝔻*`. -/
theorem s8w_fk_harmonic {κ : ℂ → ℂ} (hκ : IsHarmonicD κ) {k : ℝ} (hk : ∀ z ∈ unitDisc, ‖κ z‖ ≤ k) :
    toLinf (fun z => conj (κ (refl z)) * z ^ 2 / conj z ^ 2) ∈ harmonicBeltrami := by
  obtain ⟨hm, hb⟩ := s8w_fk_memLp hκ hk
  have hκ' := hκ
  obtain ⟨φ, hφ, -, hκφ⟩ := hκ'
  have hk0 : 0 ≤ k := (norm_nonneg _).trans (hk 0 (by simp [unitDisc]))
  set ψ : ℂ → ℂ := fun z => conj (φ (refl z)) / z ^ 4 with hψ
  have hEz : ∀ z ∈ unitDiscExterior, z ≠ 0 := fun z hz => fdr_ne_zero_of_exterior hz
  have hreflD : ∀ z ∈ unitDiscExterior, refl z ∈ unitDisc := fun z hz => (refl_mem_disc_iff (hEz z hz)).mpr hz
  have hident : ∀ z ∈ unitDiscExterior,
      conj (κ (refl z)) * z ^ 2 / conj z ^ 2 = (1 - (‖z‖ : ℂ) ^ 2) ^ 2 * conj (ψ z) := by
    intro z hz
    have hz0 := hEz z hz
    have hc0 : conj z ≠ 0 := (map_ne_zero _).mpr hz0
    rw [hκφ _ (hreflD z hz)]
    have hn : ((‖z‖ : ℂ)) ^ 2 = z * conj z := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; ring
    have hnr : ((‖refl z‖ : ℂ)) ^ 2 = (z * conj z)⁻¹ := by
      rw [norm_refl]; push_cast; rw [inv_pow, hn]
    rw [hnr, hn]
    simp only [hψ, map_mul, map_div₀, map_pow, map_sub, map_one, map_inv₀, Complex.conj_conj]
    field_simp
    ring
  have hdiff : DifferentiableOn ℂ ψ unitDiscExterior := by
    intro z hz
    have hz0 := hEz z hz
    have hφd : DifferentiableAt ℂ φ (conj (z⁻¹)) := by
      have : refl z = conj (z⁻¹) := by simp [refl]
      rw [← this]
      exact (hφ.differentiableAt (isOpen_ball.mem_nhds (hreflD z hz)))
    have h1 : DifferentiableAt ℂ (fun x : ℂ => conj (φ (conj x))) (z⁻¹) := by
      have := hφd.conj_conj
      simpa [Function.comp_def] using this
    have h2 : DifferentiableAt ℂ (fun x : ℂ => conj (φ (refl x))) z := by
      have e : (fun x : ℂ => conj (φ (refl x))) = (fun x : ℂ => conj (φ (conj x))) ∘ fun x => x⁻¹ := by
        funext x; simp [refl, Function.comp_def]
      rw [e]
      exact h1.comp z (differentiableAt_inv hz0)
    exact (h2.div (differentiableAt_pow 4) (pow_ne_zero 4 hz0)).differentiableWithinAt
  have hbound : ∀ z ∈ unitDiscExterior, ‖(1 - (‖z‖ : ℂ) ^ 2) ^ 2 * ψ z‖ ≤ k := by
    intro z hz
    have h := hb z hz
    rw [hident z hz, norm_mul, Complex.norm_conj] at h
    rwa [norm_mul]
  obtain ⟨hEq, -⟩ := toAInf_spec_of_bound (D := unitDiscExterior) (fun z hz => by
    have : 1 < ‖z‖ := hz
    linarith) hdiff hk0 hbound
  rw [mem_harmonicBeltrami_iff]
  refine ⟨toAInf unitDiscExterior ψ, ?_⟩
  have hEm : MeasurableSet unitDiscExterior := (isOpen_lt continuous_const continuous_norm).measurableSet
  filter_upwards [bc_toLinf_ae hm, ae_restrict_mem hEm] with z hz hzE
  rw [hz, hEq hzE, hident z hzE]

/-- **K3 at the origin.** There is `δ₀ ∈ (0, 1)` with `|(w_κ)_z(0)|² ≤ 2` for every harmonic `κ` with `‖κ‖∞ < δ₀`
(TT:3310; by `grp25b_sequence`, `|(w_κ)_z(0)|² → 1` as `‖κ‖∞ → 0`). -/
theorem s8w_density_zero :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ < 1 ∧ ∀ κ : ℂ → ℂ, IsHarmonicD κ → (∀ z ∈ unitDisc, ‖κ z‖ < δ₀) →
      ‖dz (wD κ) 0‖ ^ 2 ≤ 2 := by
  by_contra hcon
  push_neg at hcon
  have hseq : ∀ n : ℕ, ∃ κ : ℂ → ℂ, IsHarmonicD κ ∧ (∀ z ∈ unitDisc, ‖κ z‖ < 1 / ((n : ℝ) + 2)) ∧
      2 < ‖dz (wD κ) 0‖ ^ 2 := by
    intro n
    have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 2) := by positivity
    have hlt : 1 / ((n : ℝ) + 2) < 1 := by
      rw [div_lt_one (by positivity)]; linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    exact hcon _ hpos hlt
  choose κ hκ hκb hκd using hseq
  have hδ1 : ∀ n : ℕ, 1 / ((n : ℝ) + 2) < 1 := fun n => by
    rw [div_lt_one (by positivity)]; linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have hkle : ∀ n, ∀ z ∈ unitDisc, ‖κ n z‖ ≤ 1 / ((n : ℝ) + 2) := fun n z hz => (hκb n z hz).le
  set μ : ℕ → LinfStar := fun n => toLinf (fun z => conj (κ n (refl z)) * z ^ 2 / conj z ^ 2) with hμ
  have hEm : MeasurableSet unitDiscExterior := (isOpen_lt continuous_const continuous_norm).measurableSet
  have hnorm : ∀ n, ‖μ n‖ ≤ 1 / ((n : ℝ) + 2) := by
    intro n
    exact norm_toLinf_le_of_ae_bound (by positivity)
      ((ae_restrict_iff' hEm).mpr (Eventually.of_forall (s8w_fk_memLp (hκ n) (hkle n)).2))
  have hlim : Tendsto (fun n => ‖μ n‖) atTop (𝓝 0) :=
    squeeze_zero (fun n => norm_nonneg _)
      (fun n => (hnorm n).trans (one_div_le_one_div_of_le (by positivity) (by linarith)))
      tendsto_one_div_add_atTop_nhds_zero_nat
  have hS := grp25b_sequence (fun n => s8w_fk_harmonic (hκ n) (hkle n))
    (fun n => (hnorm n).trans_lt (hδ1 n)) hlim
  have hval : ∀ n, ‖dz (wA (μ n)) 0‖ ^ 2 / (1 - ‖wA (μ n) 0‖ ^ 2) ^ 2 = ‖dz (wD (κ n)) 0‖ ^ 2 := by
    intro n
    obtain ⟨hball, -, hNA, -⟩ := s8w_wD_normalized (hκ n) (hδ1 n) (hkle n)
    have hcd : ContDiffAt ℝ 1 (wD (κ n)) 0 :=
      ((s8w_wD_analytic (hκ n) (hδ1 n) (hkle n) 0 (by simp [unitDisc])).1.contDiffAt).of_le le_top
    exact grp25b_normalized_density hball hNA hcd
  have hev := hS.eventually (gt_mem_nhds (show (1 : ℝ) < 2 by norm_num))
  obtain ⟨N, hN⟩ := eventually_atTop.mp hev
  have h1 := hN N le_rfl
  rw [hval N] at h1
  linarith [hκd N]

/-- Wirtinger chain rule with a holomorphic inner map. -/
theorem s8w_dz_comp_right {f σ : ℂ → ℂ} {z : ℂ} (hf : DifferentiableAt ℝ f (σ z)) (hσ : DifferentiableAt ℂ σ z) :
    dz (f ∘ σ) z = dz f (σ z) * deriv σ z ∧ dzbar (f ∘ σ) z = dzbar f (σ z) * conj (deriv σ z) := by
  have hσR : DifferentiableAt ℝ σ z := hσ.restrictScalars ℝ
  have h0 : dzbar σ z = 0 := (cauchyRiemann_iff.mp hσ).2
  have h1 : dz σ z = deriv σ z := dz_eq_deriv hσ
  rw [eq6_2_dz_comp hσR hf, eq6_2_dzbar_comp hσR hf, dz_conj hσR, dzbar_conj hσR, h0, h1]
  simp

/-- `w_κ` maps `𝔻` onto `𝔻`. -/
theorem s8w_wD_disc {κ : ℂ → ℂ} (hκ : IsHarmonicD κ) {k : ℝ} (hk1 : k < 1)
    (hk : ∀ z ∈ unitDisc, ‖κ z‖ ≤ k) : wD κ '' unitDisc = unitDisc := by
  obtain ⟨-, -, hNA, -⟩ := s8w_wD_normalized hκ hk1 hk
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact mem_ball_zero_iff.mpr (normalized_solution_disc hNA (mem_ball_zero_iff.mp hx))
  · intro hy
    have hy' : y ∈ wD κ '' univ := by rw [hNA.2.1]; trivial
    obtain ⟨x, -, rfl⟩ := hy'
    refine ⟨x, ?_, rfl⟩
    by_contra hx
    have hx' : 1 ≤ ‖x‖ := by
      by_contra h
      exact hx (mem_ball_zero_iff.mpr (lt_of_not_ge h))
    have hy1 : ‖wD κ x‖ < 1 := mem_ball_zero_iff.mp hy
    rcases hx'.lt_or_eq with h | h
    · linarith [normalized_solution_exterior hNA h]
    · rw [normalized_solution_circle hNA h.symm] at hy1
      exact lt_irrefl 1 hy1

/-- The derivative of the disc automorphism `σ = blaschke (-u)` does not vanish on `𝔻`, and
`(1 - |σ z|²)² = (1 - |z|²)² |σ'(z)|²`. -/
theorem s8w_blaschke_facts {u : ℂ} (hu : ‖u‖ < 1) {z : ℂ} (hz : ‖z‖ < 1) :
    deriv (blaschke (-u)) z ≠ 0 ∧
      (1 - ‖blaschke (-u) z‖ ^ 2) ^ 2 = (1 - ‖z‖ ^ 2) ^ 2 * ‖deriv (blaschke (-u)) z‖ ^ 2 := by
  have hu' : ‖-u‖ < 1 := by simpa using hu
  have hd := hasDerivAt_blaschke hu' hz
  have hne : deriv (blaschke (-u)) z ≠ 0 := by
    rw [hd.deriv]
    exact div_ne_zero (one_sub_mul_conj_ne_zero hu') (pow_ne_zero 2 (blaschke_den_ne_zero hu' hz))
  refine ⟨hne, ?_⟩
  have hJ := rho_blaschke_jacobian hu' hz
  have hbz : ‖blaschke (-u) z‖ < 1 := blaschke_mem_unitDisc hu' hz
  have hs1 : 0 < 1 - ‖blaschke (-u) z‖ ^ 2 := by nlinarith [norm_nonneg (blaschke (-u) z)]
  have hs2 : 0 < 1 - ‖z‖ ^ 2 := by nlinarith [norm_nonneg z]
  unfold rho at hJ
  field_simp at hJ
  linarith

/-- The pull-back `κ' = (κ ∘ σ) σ̄'/σ'` of a harmonic differential by `σ = blaschke (-u)` is harmonic, with
`|κ'(z)| = |κ(σ z)|`. -/
theorem s8w_pullback_harmonic {κ : ℂ → ℂ} (hκ : IsHarmonicD κ) {u : ℂ} (hu : ‖u‖ < 1) :
    IsHarmonicD (fun z => κ (blaschke (-u) z) * (conj (deriv (blaschke (-u)) z) / deriv (blaschke (-u)) z)) ∧
      ∀ z ∈ unitDisc, ‖κ (blaschke (-u) z) * (conj (deriv (blaschke (-u)) z) / deriv (blaschke (-u)) z)‖ =
        ‖κ (blaschke (-u) z)‖ := by
  have hu' : ‖-u‖ < 1 := by simpa using hu
  have hσ := isConformalOnto_blaschke hu'
  obtain ⟨φ, hφ, ⟨C, hC⟩, hκφ⟩ := hκ
  have hσD : ∀ z ∈ unitDisc, blaschke (-u) z ∈ unitDisc := fun z hz => hσ.2.2 ▸ mem_image_of_mem _ hz
  have hnorm : ∀ z ∈ unitDisc, ‖κ (blaschke (-u) z) * (conj (deriv (blaschke (-u)) z) /
      deriv (blaschke (-u)) z)‖ = ‖κ (blaschke (-u) z)‖ := by
    intro z hz
    have hne := (s8w_blaschke_facts hu (mem_ball_zero_iff.mp hz)).1
    rw [norm_mul, norm_div, Complex.norm_conj, div_self (norm_ne_zero_iff.mpr hne), mul_one]
  refine ⟨⟨fun z => φ (blaschke (-u) z) * deriv (blaschke (-u)) z ^ 2, ?_, ⟨C, fun z hz => ?_⟩, fun z hz => ?_⟩, hnorm⟩
  · have hd : DifferentiableOn ℂ (deriv (blaschke (-u))) unitDisc :=
      hσ.1.deriv isOpen_ball
    exact (hφ.comp hσ.1 (fun z hz => hσD z hz)).mul (hd.pow 2)
  · have hz1 : ‖z‖ < 1 := mem_ball_zero_iff.mp hz
    obtain ⟨hne, hid⟩ := s8w_blaschke_facts hu hz1
    have h := hC _ (hσD z hz)
    have e : ‖(1 - (‖z‖ : ℂ) ^ 2) ^ 2 * (φ (blaschke (-u) z) * deriv (blaschke (-u)) z ^ 2)‖ =
        ‖(1 - (‖blaschke (-u) z‖ : ℂ) ^ 2) ^ 2 * φ (blaschke (-u) z)‖ := by
      have hbz : ‖blaschke (-u) z‖ < 1 := mem_ball_zero_iff.mp (hσD z hz)
      have c1 : ‖(1 : ℂ) - (‖z‖ : ℂ) ^ 2‖ = 1 - ‖z‖ ^ 2 := by
        rw [show (1 : ℂ) - (‖z‖ : ℂ) ^ 2 = ((1 - ‖z‖ ^ 2 : ℝ) : ℂ) by push_cast; ring,
          Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by nlinarith [norm_nonneg z])]
      have c2 : ‖(1 : ℂ) - (‖blaschke (-u) z‖ : ℂ) ^ 2‖ = 1 - ‖blaschke (-u) z‖ ^ 2 := by
        rw [show (1 : ℂ) - (‖blaschke (-u) z‖ : ℂ) ^ 2 = ((1 - ‖blaschke (-u) z‖ ^ 2 : ℝ) : ℂ) by
          push_cast; ring, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (by nlinarith [norm_nonneg (blaschke (-u) z)])]
      simp only [norm_mul, norm_pow, c1, c2]
      rw [hid]
      ring
    rw [e]
    exact h
  · have hz1 : ‖z‖ < 1 := mem_ball_zero_iff.mp hz
    obtain ⟨hne, hid⟩ := s8w_blaschke_facts hu hz1
    beta_reduce
    rw [hκφ _ (hσD z hz)]
    have hc : (1 - (‖blaschke (-u) z‖ : ℂ) ^ 2) ^ 2 =
        (1 - (‖z‖ : ℂ) ^ 2) ^ 2 * (deriv (blaschke (-u)) z * conj (deriv (blaschke (-u)) z)) := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
      exact_mod_cast hid
    rw [hc]
    simp only [map_mul, map_pow]
    field_simp

/-- `ρ(h 0) |h'(0)|² = ρ(0)` for a conformal self-map `h` of `𝔻`. -/
theorem s8w_conformal_rho {h : ℂ → ℂ} (hh : IsConformalOnto h unitDisc unitDisc) :
    rho (h 0) * ‖deriv h 0‖ ^ 2 = rho 0 := by
  obtain ⟨c, a, hc, ha, heq⟩ := exists_rotation_blaschke_of_isConformalOnto_unitDisc hh
  have h0 : (0 : ℂ) ∈ unitDisc := by simp [unitDisc]
  have hev : h =ᶠ[𝓝 0] fun z => c * blaschke a z := by
    filter_upwards [isOpen_ball.mem_nhds h0] with z hz
    exact heq hz
  have hd : deriv h 0 = c * deriv (blaschke a) 0 := by
    rw [hev.deriv_eq]
    exact deriv_const_mul _ ((hasDerivAt_blaschke ha (by simp)).differentiableAt)
  have hv : h 0 = c * blaschke a 0 := heq h0
  have hJ := rho_blaschke_jacobian ha (show ‖(0 : ℂ)‖ < 1 by simp)
  have hr : rho (c * blaschke a 0) = rho (blaschke a 0) := by
    simp only [rho, norm_mul, hc, one_mul]
  rw [hv, hd, hr, norm_mul, hc, one_mul, hJ]

/-- **K3.** The density bound `ρ(w_κ(u)) |(w_κ)_z(u)|² ≤ 2 ρ(u)` on `𝔻` for harmonic `κ` with `‖κ‖∞ < δ₀`. -/
theorem s8w_density_proof :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ < 1 ∧ ∃ C : ℝ, ∀ κ : ℂ → ℂ, IsHarmonicD κ → (∀ z ∈ unitDisc, ‖κ z‖ < δ₀) →
      ∀ u ∈ unitDisc, rho (wD κ u) * ‖dz (wD κ) u‖ ^ 2 ≤ C * rho u := by
  obtain ⟨δ₀, hδ0, hδ1, hD⟩ := s8w_density_zero
  refine ⟨δ₀, hδ0, hδ1, 2, fun κ hκ hκδ u hu => ?_⟩
  have hu1 : ‖u‖ < 1 := mem_ball_zero_iff.mp hu
  have hu' : ‖-u‖ < 1 := by simpa using hu1
  have hσ := isConformalOnto_blaschke hu'
  have hσD : ∀ z ∈ unitDisc, blaschke (-u) z ∈ unitDisc := fun z hz => hσ.2.2 ▸ mem_image_of_mem _ hz
  have h0 : (0 : ℂ) ∈ unitDisc := by simp [unitDisc]
  have hσ0 : blaschke (-u) 0 = u := by simp [blaschke]
  obtain ⟨hκ', hn'⟩ := s8w_pullback_harmonic hκ hu1
  set κ' : ℂ → ℂ := fun z => κ (blaschke (-u) z) * (conj (deriv (blaschke (-u)) z) / deriv (blaschke (-u)) z)
    with hκ'def
  have hk : ∀ z ∈ unitDisc, ‖κ z‖ ≤ δ₀ := fun z hz => (hκδ z hz).le
  have hκ'δ : ∀ z ∈ unitDisc, ‖κ' z‖ < δ₀ := fun z hz => by rw [hn' z hz]; exact hκδ _ (hσD z hz)
  have hk' : ∀ z ∈ unitDisc, ‖κ' z‖ ≤ δ₀ := fun z hz => (hκ'δ z hz).le
  have hd0 := hD κ' hκ' hκ'δ
  obtain ⟨-, hN, -, -⟩ := s8w_wD_normalized hκ hδ1 hk
  obtain ⟨-, hN', -, -⟩ := s8w_wD_normalized hκ' hδ1 hk'
  obtain ⟨⟨K, hK⟩, -, -, -, -⟩ := hN
  obtain ⟨⟨K', hK'⟩, -, hw'0, -, -⟩ := hN'
  have hF : IsQuasiconformal (wD κ') unitDisc := ⟨K', nx_isKQC_restrict hK' isOpen_ball (subset_univ _)⟩
  have hσK : IsKQC (blaschke (-u)) unitDisc 1 := isKQC_one_of_conformal isOpen_ball hσ
  have hG : IsQuasiconformal (wD κ ∘ blaschke (-u)) unitDisc :=
    ⟨1 * K, thm7_1_comp hσK (nx_isKQC_restrict hK isOpen_univ (subset_univ _)) (subset_univ _)⟩
  have hdil : ∀ᵐ z ∂(volume.restrict unitDisc),
      complexDilatation (wD κ') z = complexDilatation (wD κ ∘ blaschke (-u)) z := by
    refine (ae_restrict_iff' measurableSet_ball).mpr (Eventually.of_forall fun z hz => ?_)
    rw [(s8w_wD_analytic hκ' hδ1 hk' z hz).2.2]
    obtain ⟨hwa, hwd, hwdil⟩ := s8w_wD_analytic hκ hδ1 hk _ (hσD z hz)
    have hσd : DifferentiableAt ℂ (blaschke (-u)) z :=
      hσ.1.differentiableAt (isOpen_ball.mem_nhds hz)
    have hne := (s8w_blaschke_facts hu1 (mem_ball_zero_iff.mp hz)).1
    obtain ⟨e1, e2⟩ := s8w_dz_comp_right hwa.differentiableAt hσd
    unfold complexDilatation at hwdil ⊢
    rw [e1, e2, hκ'def]
    dsimp only
    rw [← hwdil]
    have hcne : conj (deriv (blaschke (-u)) z) ≠ 0 := (map_ne_zero _).mpr hne
    field_simp
  obtain ⟨φ, hφ, hrel⟩ := grp_stoilow (D := unitDisc) isOpen_ball hF hG hdil
  rw [s8w_wD_disc hκ' hδ1 hk', image_comp, hσ.2.2, s8w_wD_disc hκ hδ1 hk] at hφ
  have hφρ := s8w_conformal_rho hφ
  have hw'a := (s8w_wD_analytic hκ' hδ1 hk' 0 h0).1
  have hφd : DifferentiableAt ℂ φ (wD κ' 0) := by
    rw [hw'0]
    exact hφ.1.differentiableAt (isOpen_ball.mem_nhds h0)
  have hev : (wD κ ∘ blaschke (-u)) =ᶠ[𝓝 0] φ ∘ wD κ' := by
    filter_upwards [isOpen_ball.mem_nhds h0] with z hz
    exact hrel z hz
  have hdzL : dz (wD κ ∘ blaschke (-u)) 0 = dz (wD κ) u * deriv (blaschke (-u)) 0 := by
    have hwa := (s8w_wD_analytic hκ hδ1 hk _ (hσD 0 h0)).1
    have hσd : DifferentiableAt ℂ (blaschke (-u)) 0 := hσ.1.differentiableAt (isOpen_ball.mem_nhds h0)
    have := (s8w_dz_comp_right hwa.differentiableAt hσd).1
    rw [hσ0] at this
    exact this
  have hdzR : dz (φ ∘ wD κ') 0 = deriv φ 0 * dz (wD κ') 0 := by
    have := (ra_dz_comp_holo hφd hw'a.differentiableAt).1
    rw [hw'0] at this
    exact this
  have hφ0 : φ 0 = wD κ u := by
    have := hrel 0 h0
    rw [hw'0] at this
    simp only [Function.comp_apply, hσ0] at this
    exact this.symm
  have hkey : dz (wD κ) u * deriv (blaschke (-u)) 0 = deriv φ 0 * dz (wD κ') 0 := by
    rw [← hdzL, ← hdzR]
    exact (ra_dz_congr hev).1
  have hJσ := rho_blaschke_jacobian hu' (show ‖(0 : ℂ)‖ < 1 by simp)
  rw [hσ0] at hJσ
  have hne0 := (s8w_blaschke_facts hu1 (show ‖(0 : ℂ)‖ < 1 by simp)).1
  have hpos : 0 < ‖deriv (blaschke (-u)) 0‖ ^ 2 := by positivity
  have hρ0 : rho 0 = 4 := by simp [rho]
  have hmain : rho (wD κ u) * ‖dz (wD κ) u‖ ^ 2 * ‖deriv (blaschke (-u)) 0‖ ^ 2 =
      rho 0 * ‖dz (wD κ') 0‖ ^ 2 := by
    have := congrArg (fun x : ℂ => ‖x‖ ^ 2) hkey
    simp only [norm_mul, mul_pow] at this
    rw [mul_assoc, this, ← hφ0, ← mul_assoc, hφρ]
  have hfin : rho (wD κ u) * ‖dz (wD κ) u‖ ^ 2 * ‖deriv (blaschke (-u)) 0‖ ^ 2 ≤
      2 * rho u * ‖deriv (blaschke (-u)) 0‖ ^ 2 := by
    rw [hmain, mul_assoc, hJσ]
    have h4 : 0 ≤ rho 0 := by rw [hρ0]; norm_num
    nlinarith [hd0, h4]
  exact le_of_mul_le_mul_right hfin hpos

/-- **K1.** -/
theorem s8w_wD_facts_proof {κ : ℂ → ℂ} (hκ : IsHarmonicD κ) {k : ℝ} (hk1 : k < 1)
    (hk : ∀ z ∈ unitDisc, ‖κ z‖ ≤ k) :
    (∃ e : ℂ ≃ₜ ℂ, ⇑e = wD κ) ∧ MapsTo (wD κ) unitDisc unitDisc ∧ wD κ '' unitDisc = unitDisc ∧
      ∀ u ∈ unitDisc, DifferentiableAt ℝ (wD κ) u ∧ dz (wD κ) u ≠ 0 ∧ dzbar (wD κ) u = κ u * dz (wD κ) u := by
  obtain ⟨-, hN, -, -⟩ := s8w_wD_normalized hκ hk1 hk
  obtain ⟨⟨K, hK⟩, hs, -, -, -⟩ := hN
  obtain ⟨e, he⟩ := t1_homeomorph hK hs
  have hD := s8w_wD_disc hκ hk1 hk
  refine ⟨⟨e, he⟩, fun z hz => by rw [← hD]; exact mem_image_of_mem _ hz, hD, fun u hu => ?_⟩
  obtain ⟨ha, hd, hdil⟩ := s8w_wD_analytic hκ hk1 hk u hu
  refine ⟨ha.differentiableAt, hd, ?_⟩
  unfold complexDilatation at hdil
  rw [← hdil]
  field_simp

/-- **K2.** -/
theorem s8w_change_proof {w a : ℂ → ℂ} (hinj : InjOn w unitDisc)
    (hd : ∀ u ∈ unitDisc, DifferentiableAt ℝ w u ∧ dzbar w u = a u * dz w u ∧ ‖a u‖ ≤ 1)
    {S : Set ℂ} (hS : MeasurableSet S) (hSD : S ⊆ unitDisc) (f : ℂ → ℂ) :
    ∫ z in w '' S, f z = ∫ u in S, (‖dz w u‖ ^ 2 * (1 - ‖a u‖ ^ 2)) • f (w u) := by
  have hJ : ∀ u ∈ S, |(fderiv ℝ w u).det| = ‖dz w u‖ ^ 2 * (1 - ‖a u‖ ^ 2) := by
    intro u hu
    obtain ⟨h1, h2, h3⟩ := hd u (hSD hu)
    have e : (fderiv ℝ w u).det = jacobian w u := det_fderiv_eq_jacobian h1
    have e2 : jacobian w u = ‖dz w u‖ ^ 2 * (1 - ‖a u‖ ^ 2) := by
      unfold jacobian
      rw [h2, norm_mul]
      ring
    have h4 : 0 ≤ 1 - ‖a u‖ ^ 2 := by nlinarith [norm_nonneg (a u)]
    rw [e, e2, abs_of_nonneg (mul_nonneg (sq_nonneg _) h4)]
  rw [integral_image_eq_integral_abs_det_fderiv_smul volume hS
    (fun u hu => ((hd u (hSD hu)).1.hasFDerivAt).hasFDerivWithinAt) (hinj.mono hSD) f]
  exact setIntegral_congr_fun hS fun u hu => by rw [hJ u hu]

/-- **K2'.** -/
theorem s8w_lchange_proof {w a : ℂ → ℂ} (hinj : InjOn w unitDisc)
    (hd : ∀ u ∈ unitDisc, DifferentiableAt ℝ w u ∧ dzbar w u = a u * dz w u ∧ ‖a u‖ ≤ 1)
    {S : Set ℂ} (hS : MeasurableSet S) (hSD : S ⊆ unitDisc) (φ : ℂ → ℝ≥0∞) :
    ∫⁻ z in w '' S, φ z = ∫⁻ u in S, ENNReal.ofReal (‖dz w u‖ ^ 2 * (1 - ‖a u‖ ^ 2)) * φ (w u) := by
  have hJ : ∀ u ∈ S, |(fderiv ℝ w u).det| = ‖dz w u‖ ^ 2 * (1 - ‖a u‖ ^ 2) := by
    intro u hu
    obtain ⟨h1, h2, h3⟩ := hd u (hSD hu)
    have e : (fderiv ℝ w u).det = jacobian w u := det_fderiv_eq_jacobian h1
    have e2 : jacobian w u = ‖dz w u‖ ^ 2 * (1 - ‖a u‖ ^ 2) := by
      unfold jacobian
      rw [h2, norm_mul]
      ring
    have h4 : 0 ≤ 1 - ‖a u‖ ^ 2 := by nlinarith [norm_nonneg (a u)]
    rw [e, e2, abs_of_nonneg (mul_nonneg (sq_nonneg _) h4)]
  rw [lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hS
    (fun u hu => ((hd u (hSD hu)).1.hasFDerivAt).hasFDerivWithinAt) (hinj.mono hSD) φ]
  exact setLIntegral_congr_fun hS fun u hu => by rw [hJ u hu]

/-- An `SU(1,1)` matrix acts as a conformal automorphism of `𝔻`. -/
theorem s8w_mob_conformal {g : SL2C} (hg : IsSU11 g) : IsConformalOnto (mob g) unitDisc unitDisc := by
  refine ⟨fun z hz => ?_, fun z₁ h₁ z₂ h₂ he => ?_, ?_⟩
  · exact (wp_mob_hasDerivAt g (fdD_denom_ne hg (mem_ball_zero_iff.mp hz))).differentiableAt.differentiableWithinAt
  · have e1 := (fd_inv_step g (fdD_denom_ne hg (mem_ball_zero_iff.mp h₁))).2
    have e2 := (fd_inv_step g (fdD_denom_ne hg (mem_ball_zero_iff.mp h₂))).2
    rw [← e1, ← e2, he]
  · ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact mem_ball_zero_iff.mpr (fdD_mob_lt hg (mem_ball_zero_iff.mp hz))
    · intro hy
      have hy1 : ‖y‖ < 1 := mem_ball_zero_iff.mp hy
      have hgi := isSU11_inv hg
      have hD := fdD_denom_ne hgi hy1
      have h := fd_inv_step g⁻¹ hD
      rw [inv_inv] at h
      exact ⟨mob g⁻¹ y, mem_ball_zero_iff.mpr (fdD_mob_lt hgi hy1), h.2⟩

/-- A rotated Blaschke factor `c · blaschke a` (`|c| = 1`, `|a| < 1`) is the action of an `SU(1,1)` matrix. -/
theorem s8w_su11_of_blaschke {c a : ℂ} (hc : ‖c‖ = 1) (ha : ‖a‖ < 1) :
    ∃ g' : SL2C, IsSU11 g' ∧ ∀ z ∈ unitDisc, mob g' z = c * blaschke a z := by
  obtain ⟨s, hs⟩ := IsAlgClosed.exists_pow_nat_eq c (by norm_num : 0 < 2)
  have hsn : ‖s‖ = 1 := by
    have h := congrArg norm hs
    rw [norm_pow, hc] at h
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg s) (by norm_num)).mp h
  have hss : s * conj s = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hsn]; norm_num
  have ha2 : 0 < 1 - ‖a‖ ^ 2 := by nlinarith [norm_nonneg a]
  set t : ℝ := 1 / Real.sqrt (1 - ‖a‖ ^ 2) with ht
  have htt : t ^ 2 * (1 - ‖a‖ ^ 2) = 1 := by
    rw [ht, div_pow, Real.sq_sqrt ha2.le]
    field_simp
  have haa : a * conj a = ((‖a‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  set α : ℂ := s * t with hα
  set β : ℂ := -(s * t * a) with hβ
  have hdet : Matrix.det !![α, β; conj β, conj α] = 1 := by
    rw [Matrix.det_fin_two_of]
    simp only [hα, hβ, map_mul, map_neg, Complex.conj_ofReal]
    have : s * ↑t * (conj s * ↑t) - -(s * ↑t * a) * -(conj s * ↑t * conj a) =
        (s * conj s) * ((t ^ 2 : ℝ) : ℂ) * (1 - a * conj a) := by push_cast; ring
    rw [this, hss, haa, one_mul]
    exact_mod_cast htt
  refine ⟨⟨!![α, β; conj β, conj α], hdet⟩, ⟨rfl, by simp⟩, fun z hz => ?_⟩
  have hz1 : ‖z‖ < 1 := mem_ball_zero_iff.mp hz
  have hden := blaschke_den_ne_zero ha hz1
  have ht0 : (t : ℂ) ≠ 0 := by
    rw [ht]; exact_mod_cast (one_div_pos.mpr (Real.sqrt_pos.mpr ha2)).ne'
  have hcs : conj s ≠ 0 := by
    intro h; rw [h, mul_zero] at hss; exact zero_ne_one hss
  show (α * z + β) / (conj β * z + conj α) = c * blaschke a z
  simp only [hα, hβ, map_mul, map_neg, Complex.conj_ofReal, blaschke]
  rw [← hs]
  have e : -(conj s * ↑t * conj a) * z + conj s * ↑t = conj s * ↑t * (1 - conj a * z) := by ring
  rw [e]
  have hs' : s ^ 2 = s / conj s := by
    field_simp
    linear_combination s * hss
  rw [hs']
  field_simp
  ring

/-- **K4.** -/
theorem s8w_equivariant_proof {Γ : Subgroup SL2C} (hΓ : IsFuchsian Γ) {κ : ℂ → ℂ} (hκ : IsHarmonicD κ)
    (hκΓ : IsGammaInvD Γ κ) {k : ℝ} (hk1 : k < 1) (hk : ∀ z ∈ unitDisc, ‖κ z‖ ≤ k) :
    ∀ g ∈ Γ, ∃ g' : SL2C, IsSU11 g' ∧ ∀ u ∈ unitDisc, wD κ (mob g u) = mob g' (wD κ u) := by
  intro g hg
  have hsu := hΓ.1 g hg
  have hgC := s8w_mob_conformal hsu
  obtain ⟨-, hN, -, -⟩ := s8w_wD_normalized hκ hk1 hk
  obtain ⟨⟨K, hK⟩, -, -, -, -⟩ := hN
  have hF : IsQuasiconformal (wD κ) unitDisc := ⟨K, nx_isKQC_restrict hK isOpen_ball (subset_univ _)⟩
  have hgK : IsKQC (mob g) unitDisc 1 := isKQC_one_of_conformal isOpen_ball hgC
  have hG : IsQuasiconformal (wD κ ∘ mob g) unitDisc :=
    ⟨1 * K, thm7_1_comp hgK (nx_isKQC_restrict hK isOpen_univ (subset_univ _)) (subset_univ _)⟩
  have hgD : ∀ z ∈ unitDisc, mob g z ∈ unitDisc := fun z hz => hgC.2.2 ▸ mem_image_of_mem _ hz
  have hdil : ∀ᵐ z ∂(volume.restrict unitDisc),
      complexDilatation (wD κ) z = complexDilatation (wD κ ∘ mob g) z := by
    refine (ae_restrict_iff' measurableSet_ball).mpr (Eventually.of_forall fun z hz => ?_)
    rw [(s8w_wD_analytic hκ hk1 hk z hz).2.2]
    obtain ⟨hwa, hwd, hwdil⟩ := s8w_wD_analytic hκ hk1 hk _ (hgD z hz)
    have hD := fdD_denom_ne hsu (mem_ball_zero_iff.mp hz)
    have hgd : DifferentiableAt ℂ (mob g) z := (wp_mob_hasDerivAt g hD).differentiableAt
    have hne : deriv (mob g) z ≠ 0 := by
      rw [(wp_mob_hasDerivAt g hD).deriv]
      exact one_div_ne_zero (pow_ne_zero 2 hD)
    obtain ⟨e1, e2⟩ := s8w_dz_comp_right hwa.differentiableAt hgd
    unfold complexDilatation at hwdil ⊢
    rw [e1, e2, ← hκΓ g hg z hz, ← hwdil]
    have hcne : conj (deriv (mob g) z) ≠ 0 := (map_ne_zero _).mpr hne
    field_simp
  obtain ⟨φ, hφ, hrel⟩ := grp_stoilow (D := unitDisc) isOpen_ball hF hG hdil
  rw [s8w_wD_disc hκ hk1 hk, image_comp, hgC.2.2, s8w_wD_disc hκ hk1 hk] at hφ
  obtain ⟨c, a, hc, ha, heq⟩ := exists_rotation_blaschke_of_isConformalOnto_unitDisc hφ
  obtain ⟨g', hg', hmob⟩ := s8w_su11_of_blaschke hc ha
  refine ⟨g', hg', fun u hu => ?_⟩
  have hwu : wD κ u ∈ unitDisc := by rw [← s8w_wD_disc hκ hk1 hk]; exact mem_image_of_mem _ hu
  have h2 : φ (wD κ u) = c * blaschke a (wD κ u) := heq hwu
  rw [hmob _ hwu, ← h2]
  exact hrel u hu

/-- Two `SU(1,1)` actions that agree on `𝔻` are equal. -/
theorem s8w_mob_eq_of_eqOn {g h : SL2C} (hg : IsSU11 g) (hh : IsSU11 h)
    (heq : ∀ z ∈ unitDisc, mob g z = mob h z) : mob g = mob h := by
  by_contra hne
  have hfin := fd_agree_finite hne
  have hinf : (unitDisc : Set ℂ).Infinite := by
    refine Set.infinite_of_injective_forall_mem (f := fun n : ℕ => ((1 / ((n : ℝ) + 2) : ℝ) : ℂ)) ?_ ?_
    · intro m n hmn
      have h := congrArg Complex.re hmn
      simp only [Complex.ofReal_re] at h
      have h2 : (m : ℝ) + 2 = (n : ℝ) + 2 := by
        have hm : (0 : ℝ) < (m : ℝ) + 2 := by positivity
        have hn : (0 : ℝ) < (n : ℝ) + 2 := by positivity
        field_simp at h
        linarith
      exact_mod_cast (by linarith : (m : ℝ) = n)
    · intro n
      refine mem_ball_zero_iff.mpr ?_
      rw [Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (by positivity : (0 : ℝ) < 1 / ((n : ℝ) + 2))]
      rw [div_lt_one (by positivity)]
      linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  apply hinf
  refine hfin.subset fun z hz => ?_
  have hz1 : ‖z‖ < 1 := mem_ball_zero_iff.mp hz
  exact ⟨fdD_denom_ne hg hz1, fdD_denom_ne hh hz1, heq z hz⟩

/-- Entries of an `SU(1,1)` matrix are bounded in terms of `|γ(0)|`. -/
theorem s8w_su11_entries_bound {g : SL2C} (hg : IsSU11 g) {r : ℝ} (hr0 : 0 ≤ r) (hr : r < 1)
    (h0 : ‖mob g 0‖ ≤ r) : ∀ i j, ‖(g : Matrix (Fin 2) (Fin 2) ℂ) i j‖ ≤ Real.sqrt (1 / (1 - r ^ 2)) := by
  have hdet := fd_su11_det hg
  have ha1 : 1 ≤ ‖g 0 0‖ := by nlinarith [norm_nonneg (g 0 1), norm_nonneg (g 0 0)]
  have hg11 : g 1 1 ≠ 0 := by
    rw [hg.2]; intro h; rw [map_eq_zero] at h; rw [h, norm_zero] at ha1; linarith
  have hm : mob g 0 = g 0 1 / g 1 1 := by simp [mob]
  have hb : ‖g 0 1‖ ≤ r * ‖g 0 0‖ := by
    rw [hm, norm_div, hg.2, Complex.norm_conj] at h0
    rwa [div_le_iff₀ (by linarith)] at h0
  have hr2 : 0 < 1 - r ^ 2 := by nlinarith
  have ha2 : ‖g 0 0‖ ^ 2 ≤ 1 / (1 - r ^ 2) := by
    rw [le_div_iff₀ hr2]
    nlinarith [norm_nonneg (g 0 1), mul_le_mul hb hb (norm_nonneg _) (by positivity)]
  have hA : ‖g 0 0‖ ≤ Real.sqrt (1 / (1 - r ^ 2)) := Real.le_sqrt_of_sq_le ha2
  have hB : ‖g 0 1‖ ≤ ‖g 0 0‖ := by nlinarith [norm_nonneg (g 0 1)]
  intro i j
  fin_cases i <;> fin_cases j
  · exact hA
  · exact hB.trans hA
  · show ‖g 1 0‖ ≤ _
    rw [hg.1, Complex.norm_conj]; exact hB.trans hA
  · show ‖g 1 1‖ ≤ _
    rw [hg.2, Complex.norm_conj]; exact hA

/-- `|γ(0)|` is bounded away from `1` on a bounded set of `SU(1,1)` matrices. -/
theorem s8w_su11_mob_zero {g : SL2C} (hg : IsSU11 g) {C : ℝ}
    (hC : ∀ i j, ‖(g : Matrix (Fin 2) (Fin 2) ℂ) i j‖ ≤ C) :
    ‖mob g 0‖ ≤ Real.sqrt (1 - 1 / (max C 1) ^ 2) := by
  have hdet := fd_su11_det hg
  have ha1 : 1 ≤ ‖g 0 0‖ := by nlinarith [norm_nonneg (g 0 1), norm_nonneg (g 0 0)]
  have hg11 : g 1 1 ≠ 0 := by
    rw [hg.2]; intro h; rw [map_eq_zero] at h; rw [h, norm_zero] at ha1; linarith
  have hm : mob g 0 = g 0 1 / g 1 1 := by simp [mob]
  have haC : ‖g 0 0‖ ≤ max C 1 := (hC 0 0).trans (le_max_left _ _)
  have hM1 : 1 ≤ max C 1 := le_max_right _ _
  apply Real.le_sqrt_of_sq_le
  rw [hm, norm_div, hg.2, Complex.norm_conj, div_pow]
  have hapos : 0 < ‖g 0 0‖ ^ 2 := by positivity
  rw [div_le_iff₀ hapos]
  have hb2 : ‖g 0 1‖ ^ 2 = ‖g 0 0‖ ^ 2 - 1 := by linarith
  rw [hb2]
  have h1 : 1 / (max C 1) ^ 2 * ‖g 0 0‖ ^ 2 ≥ 1 / (max C 1) ^ 2 * 1 := by
    apply mul_le_mul_of_nonneg_left (by nlinarith) (by positivity)
  have h2 : 1 / (max C 1) ^ 2 * ‖g 0 0‖ ^ 2 ≤ 1 := by
    rw [div_mul_eq_mul_div, one_mul, div_le_one (by positivity)]
    nlinarith [norm_nonneg (g 0 0)]
  nlinarith [h2]

/-- **K5.** -/
theorem s8w_conj_group_proof {Γ : Subgroup SL2C} (hΓ : IsCofinite Γ) {κ : ℂ → ℂ} (hκ : IsHarmonicD κ)
    (hκΓ : IsGammaInvD Γ κ) {k : ℝ} (hk1 : k < 1) (hk : ∀ z ∈ unitDisc, ‖κ z‖ ≤ k) :
    ∃ Γ' : Subgroup SL2C, IsFuchsian Γ' ∧ IsFundDomainD Γ' (wD κ '' fundDomainOn Γ unitDisc) ∧
      (∀ g' ∈ Γ', ∃ g ∈ Γ, ∀ u ∈ unitDisc, wD κ (mob g u) = mob g' (wD κ u)) ∧
      ∀ g ∈ Γ, ∃ g' ∈ Γ', ∀ u ∈ unitDisc, wD κ (mob g u) = mob g' (wD κ u) := by
  have hF : IsFuchsian Γ := hΓ.1
  haveI : DiscreteTopology Γ := hF.2
  obtain ⟨⟨e, he⟩, hmaps, hD, hdiff⟩ := s8w_wD_facts_proof hκ hk1 hk
  have hw0 : wD κ 0 = 0 := (s8w_wD_normalized hκ hk1 hk).2.1.2.2.1
  have hK4 := s8w_equivariant_proof hF hκ hκΓ hk1 hk
  have hinj : Function.Injective (wD κ) := by rw [← he]; exact e.injective
  have hmobD : ∀ {g : SL2C}, IsSU11 g → ∀ z ∈ unitDisc, mob g z ∈ unitDisc := fun hg z hz =>
    mem_ball_zero_iff.mpr (fdD_mob_lt hg (mem_ball_zero_iff.mp hz))
  have hmul : ∀ {g h : SL2C}, IsSU11 g → IsSU11 h → ∀ z ∈ unitDisc, mob (g * h) z = mob g (mob h z) :=
    fun hg hh z hz => (fd_mob_mul (fdD_denom_ne hh (mem_ball_zero_iff.mp hz))
      (fdD_denom_ne hg (mem_ball_zero_iff.mp (hmobD hh z hz)))).2
  let Γ' : Subgroup SL2C :=
    { carrier := {g' | IsSU11 g' ∧ ∃ g ∈ Γ, ∀ u ∈ unitDisc, wD κ (mob g u) = mob g' (wD κ u)}
      mul_mem' := by
        rintro a b ⟨ha, g₁, hg₁, h₁⟩ ⟨hb, g₂, hg₂, h₂⟩
        refine ⟨isSU11_mul ha hb, g₁ * g₂, Γ.mul_mem hg₁ hg₂, fun u hu => ?_⟩
        have hs₁ := hF.1 _ hg₁
        have hs₂ := hF.1 _ hg₂
        rw [hmul hs₁ hs₂ u hu, h₁ _ (hmobD hs₂ u hu), h₂ u hu, hmul ha hb _ (hmaps hu)]
      one_mem' := by
        refine ⟨⟨by simp, by simp⟩, 1, Γ.one_mem, fun u _ => ?_⟩
        simp [mob]
      inv_mem' := by
        rintro a ⟨ha, g, hg, h⟩
        refine ⟨isSU11_inv ha, g⁻¹, Γ.inv_mem hg, fun u hu => ?_⟩
        have hs := hF.1 _ hg
        have hu1 : ‖u‖ < 1 := mem_ball_zero_iff.mp hu
        have hv : mob g⁻¹ u ∈ unitDisc := hmobD (isSU11_inv hs) u hu
        have hgv : mob g (mob g⁻¹ u) = u := by
          have := fd_inv_step g⁻¹ (fdD_denom_ne (isSU11_inv hs) hu1)
          rw [inv_inv] at this
          exact this.2
        have h1 := h _ hv
        rw [hgv] at h1
        have hden := fdD_denom_ne ha (mem_ball_zero_iff.mp (hmaps hv))
        rw [h1, (fd_inv_step a hden).2] }
  have hmem : ∀ g', g' ∈ Γ' ↔ IsSU11 g' ∧ ∃ g ∈ Γ, ∀ u ∈ unitDisc, wD κ (mob g u) = mob g' (wD κ u) :=
    fun g' => Iff.rfl
  -- agreement on `𝔻` via `w`
  have hagree : ∀ {g g₁ g₂ : SL2C}, IsSU11 g₁ → IsSU11 g₂ →
      (∀ u ∈ unitDisc, wD κ (mob g u) = mob g₁ (wD κ u)) →
      (∀ u ∈ unitDisc, wD κ (mob g u) = mob g₂ (wD κ u)) → mob g₁ = mob g₂ := by
    intro g g₁ g₂ h₁ h₂ e₁ e₂
    refine s8w_mob_eq_of_eqOn h₁ h₂ fun y hy => ?_
    rw [← hD] at hy
    obtain ⟨u, hu, rfl⟩ := hy
    rw [← e₁ u hu, e₂ u hu]
  -- discreteness
  have hbdd : ∀ C : ℝ, {g' : SL2C | g' ∈ Γ' ∧ ∀ i j, ‖(g' : Matrix (Fin 2) (Fin 2) ℂ) i j‖ ≤ C}.Finite := by
    intro C
    set r₀ : ℝ := Real.sqrt (1 - 1 / (max C 1) ^ 2) with hr₀
    have hM1 : 1 ≤ max C 1 := le_max_right _ _
    have hr₀1 : r₀ < 1 := by
      rw [hr₀, Real.sqrt_lt' one_pos]
      have : 0 < 1 / (max C 1) ^ 2 := by positivity
      linarith
    have hr₀0 : 0 ≤ r₀ := Real.sqrt_nonneg _
    set Q : Set ℂ := e.symm '' closedBall 0 r₀ with hQ
    have hQc : IsCompact Q := (isCompact_closedBall 0 r₀).image e.symm.continuous
    have hQD : Q ⊆ unitDisc := by
      rintro _ ⟨y, hy, rfl⟩
      have hyD : y ∈ unitDisc := mem_ball_zero_iff.mpr ((mem_closedBall_zero_iff.mp hy).trans_lt hr₀1)
      rw [← hD] at hyD
      obtain ⟨u, hu, hwu⟩ := hyD
      rw [← hwu, ← he, e.symm_apply_apply]
      exact hu
    have hQne : Q.Nonempty := ⟨e.symm 0, 0, mem_closedBall_self hr₀0, rfl⟩
    obtain ⟨q, hqQ, hqmax⟩ := hQc.exists_isMaxOn hQne continuous_norm.continuousOn
    set r₁ : ℝ := ‖q‖ with hr₁
    have hr₁1 : r₁ < 1 := mem_ball_zero_iff.mp (hQD hqQ)
    have hr₁0 : 0 ≤ r₁ := norm_nonneg _
    set C₁ : ℝ := Real.sqrt (1 / (1 - r₁ ^ 2))
    set S : Set SL2C := {g : SL2C | g ∈ Γ ∧ ∀ i j, ‖(g : Matrix (Fin 2) (Fin 2) ℂ) i j‖ ≤ C₁}
    have hS : S.Finite := fd_bounded_finite C₁
    set T : SL2C → Set SL2C := fun g =>
      {g' : SL2C | IsSU11 g' ∧ ∀ u ∈ unitDisc, wD κ (mob g u) = mob g' (wD κ u)}
    have hT : ∀ g, (T g).Finite := by
      intro g
      by_cases hne : (T g).Nonempty
      · obtain ⟨g₀, hg₀⟩ := hne
        refine (Set.toFinite ({g₀, -g₀} : Set SL2C)).subset fun g' hg' => ?_
        have hm := hagree hg₀.1 hg'.1 hg₀.2 hg'.2
        rcases fd_mob_eq hm with h | h
        · exact Or.inl h
        · exact Or.inr h
      · rw [Set.not_nonempty_iff_eq_empty] at hne
        rw [hne]
        exact Set.finite_empty
    refine (hS.biUnion fun g _ => hT g).subset ?_
    rintro g' ⟨⟨hs', g, hg, hrel⟩, hC⟩
    refine Set.mem_biUnion (x := g) ⟨hg, ?_⟩ ⟨hs', hrel⟩
    have hs := hF.1 g hg
    have h0 : ‖mob g' 0‖ ≤ r₀ := s8w_su11_mob_zero hs' hC
    have hv : mob g 0 = e.symm (mob g' 0) := by
      have h1 := hrel 0 (by simp [unitDisc])
      rw [hw0, ← he] at h1
      rw [← h1, e.symm_apply_apply]
    have hvQ : mob g 0 ∈ Q := by
      rw [hv]
      exact ⟨mob g' 0, mem_closedBall_zero_iff.mpr h0, rfl⟩
    have hle : ‖mob g 0‖ ≤ r₁ := hqmax hvQ
    exact s8w_su11_entries_bound hs hr₁0 hr₁1 hle
  have hdisc : DiscreteTopology Γ' := by
    rw [discreteTopology_iff_isOpen_singleton]
    intro x
    have hc : Continuous ((↑) : SL2C → Matrix (Fin 2) (Fin 2) ℂ) :=
      Matrix.SpecialLinearGroup.isClosedEmbedding_val.continuous
    set C : ℝ := (∑ i, ∑ j, ‖((x : SL2C) : Matrix (Fin 2) (Fin 2) ℂ) i j‖) + 1 with hCdef
    set U : Set SL2C := {g | ∀ i j, ‖(g : Matrix (Fin 2) (Fin 2) ℂ) i j‖ < C} with hUdef
    have hUo : IsOpen U := by
      have e : U = ⋂ i, ⋂ j, {g : SL2C | ‖(g : Matrix (Fin 2) (Fin 2) ℂ) i j‖ < C} := by
        ext g
        simp [hUdef]
      rw [e]
      exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
        isOpen_lt ((continuous_apply j).comp ((continuous_apply i).comp hc)).norm continuous_const
    have hxU : (x : SL2C) ∈ U := by
      intro i j
      have h2 : ‖((x : SL2C) : Matrix (Fin 2) (Fin 2) ℂ) i j‖ ≤
          ∑ i, ∑ j, ‖((x : SL2C) : Matrix (Fin 2) (Fin 2) ℂ) i j‖ :=
        (Finset.single_le_sum (f := fun j => ‖((x : SL2C) : Matrix (Fin 2) (Fin 2) ℂ) i j‖)
          (fun _ _ => norm_nonneg _) (Finset.mem_univ j)).trans
        (Finset.single_le_sum (f := fun i => ∑ j, ‖((x : SL2C) : Matrix (Fin 2) (Fin 2) ℂ) i j‖)
          (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ i))
      exact lt_of_le_of_lt h2 (lt_add_one _)
    have hfin : (((↑) : Γ' → SL2C) ⁻¹' U).Finite :=
      ((hbdd C).preimage Subtype.val_injective.injOn).subset fun y hy => ⟨y.2, fun i j => (hy i j).le⟩
    exact isOpen_singleton_of_finite_mem_nhds x ((hUo.preimage continuous_subtype_val).mem_nhds hxU) hfin
  -- the fundamental domain
  have hex : ∃ F, IsFundDomain Γ F := ⟨_, fd_exists_isFundDomain hF⟩
  have hFD : IsFundDomain Γ (fundDomain Γ) := by
    unfold fundDomain
    rw [dif_pos hex]
    exact hex.choose_spec
  have hexD : ∃ F, IsFundDomainOn Γ unitDisc F := ⟨_, fdr_isFundDomainD_refl hF hFD⟩
  have hG : IsFundDomainD Γ (fundDomainOn Γ unitDisc) := by
    have h : IsFundDomainOn Γ unitDisc (fundDomainOn Γ unitDisc) := by
      unfold fundDomainOn
      rw [dif_pos hexD]
      exact hexD.choose_spec
    exact h
  set F := fundDomainOn Γ unitDisc with hFdef
  have hnull : ∀ N : Set ℂ, N ⊆ unitDisc → volume N = 0 → volume (wD κ '' N) = 0 := by
    intro N hN h0
    set M := toMeasurable volume N ∩ unitDisc
    have hMm : MeasurableSet M := (measurableSet_toMeasurable _ _).inter measurableSet_ball
    have hNM : N ⊆ M := fun x hx => ⟨subset_toMeasurable _ _ hx, hN hx⟩
    have hM0 : volume M = 0 := measure_mono_null inter_subset_left (by rw [measure_toMeasurable]; exact h0)
    have hd' : ∀ u ∈ unitDisc, DifferentiableAt ℝ (wD κ) u ∧ dzbar (wD κ) u = κ u * dz (wD κ) u ∧
        ‖κ u‖ ≤ 1 := fun u hu => ⟨(hdiff u hu).1, (hdiff u hu).2.2, (hk u hu).trans hk1.le⟩
    have hl := s8w_lchange_proof hinj.injOn hd' hMm inter_subset_right (fun _ => (1 : ℝ≥0∞))
    have hv : volume (wD κ '' M) = 0 := by
      rw [← setLIntegral_one, hl]
      exact setLIntegral_measure_zero _ _ hM0
    exact measure_mono_null (image_mono hNM) hv
  have hpre : ∀ {g g' : SL2C}, (∀ u ∈ unitDisc, wD κ (mob g u) = mob g' (wD κ u)) →
      ∀ v ∈ unitDisc, mob g' (wD κ v) ∈ wD κ '' F → mob g v ∈ F := by
    intro g g' hrel v hv hm
    rw [← hrel v hv] at hm
    obtain ⟨f, hf, hfe⟩ := hm
    rw [← hinj hfe]
    exact hf
  refine ⟨Γ', ⟨fun g' hg' => hg'.1, hdisc⟩, ⟨?_, ?_, ?_, ?_⟩, fun g' hg' => hg'.2,
    fun g hg => ?_⟩
  · rw [← he]
    exact e.measurableEmbedding.measurableSet_image.mpr hG.1
  · rintro _ ⟨v, hv, rfl⟩
    exact hmaps (hG.2.1 hv)
  · have hB := hG.2.2.1
    rw [ae_restrict_iff' (show MeasurableSet unitDisc from measurableSet_ball)] at hB ⊢
    rw [ae_iff] at hB ⊢
    refine measure_mono_null ?_ (hnull _ (fun x hx => ?_) hB)
    · intro z hz
      simp only [mem_setOf_eq, not_forall, exists_prop] at hz
      obtain ⟨hzD, hbad⟩ := hz
      have hzD' := hzD
      rw [← hD] at hzD'
      obtain ⟨v, hv, rfl⟩ := hzD'
      refine ⟨v, ?_, rfl⟩
      simp only [mem_setOf_eq, not_forall, exists_prop]
      refine ⟨hv, fun hex => hbad ?_⟩
      obtain ⟨g, hg, hgv⟩ := hex
      obtain ⟨g', hg', hrel⟩ := hK4 g hg
      exact ⟨g', ⟨hg', g, hg, hrel⟩, by rw [← hrel v hv]; exact mem_image_of_mem _ hgv⟩
    · simp only [mem_setOf_eq, not_forall, exists_prop] at hx
      exact hx.1
  · intro g' hg' h' hh' hne
    obtain ⟨hs', g, hg, hrel⟩ := hg'
    obtain ⟨hsh', h, hh, hrelh⟩ := hh'
    have hgh : mob g ≠ mob h := by
      intro hgh
      apply hne
      refine hagree hs' hsh' hrel ?_
      intro u hu
      rw [← hrelh u hu, hgh]
    refine measure_mono_null ?_ (hnull _ (fun x hx => hx.2) (hG.2.2.2 g hg h hh hgh))
    rintro z ⟨⟨hz1, hz2⟩, hzD⟩
    have hzD' := hzD
    rw [← hD] at hzD'
    obtain ⟨v, hv, rfl⟩ := hzD'
    exact ⟨v, ⟨⟨hpre hrel v hv hz1, hpre hrelh v hv hz2⟩, hv⟩, rfl⟩
  · obtain ⟨g', hg', hrel⟩ := hK4 g hg
    exact ⟨g', ⟨hg', g, hg, hrel⟩, hrel⟩

/-! ## P: the projector -/

/-- `|1 - z ζ̄| ≥ 1 - R` for `|z| ≤ R` and `ζ ∈ 𝔻`. -/
theorem s8w_den_lower {z ζ : ℂ} {R : ℝ} (hz : ‖z‖ ≤ R) (hζ : ‖ζ‖ < 1) : 1 - R ≤ ‖1 - z * conj ζ‖ := by
  have h := norm_sub_norm_le (1 : ℂ) (z * conj ζ)
  have h2 : ‖z * conj ζ‖ ≤ R := by
    rw [norm_mul, Complex.norm_conj]
    have hR : 0 ≤ R := (norm_nonneg z).trans hz
    nlinarith [norm_nonneg z, norm_nonneg ζ]
  rw [norm_one] at h
  linarith

/-- The kernel representation of `P F` for an arbitrary `F`. -/
theorem s8w_proj_repr (F : ℂ → ℂ) {z : ℂ} (hz : z ∈ unitDisc) :
    harmonicProjD F z = (rho z : ℂ)⁻¹ *
      conj ((12 / π : ℂ) * ∫ ζ in unitDisc, conj (F ζ) / (1 - z * conj ζ) ^ 4) := by
  have hz1 : ‖z‖ < 1 := mem_ball_zero_iff.mp hz
  have hs : (1 : ℂ) - (‖z‖ : ℂ) ^ 2 ≠ 0 := by
    have : (1 : ℝ) - ‖z‖ ^ 2 ≠ 0 := by nlinarith [norm_nonneg z]
    exact_mod_cast this
  have hI : conj (∫ ζ in unitDisc, conj (F ζ) / (1 - z * conj ζ) ^ 4) =
      ∫ ζ in unitDisc, F ζ / (1 - ζ * conj z) ^ 4 := by
    rw [← integral_conj]
    apply integral_congr_ae
    filter_upwards with ζ
    simp only [map_div₀, map_pow, map_sub, map_one, map_mul, Complex.conj_conj]
    rw [mul_comm (conj z) ζ]
  unfold harmonicProjD
  rw [map_mul, hI]
  have h12 : conj (12 / π : ℂ) = 12 / π := by
    rw [show (12 / π : ℂ) = ((12 / π : ℝ) : ℂ) by push_cast; rfl, Complex.conj_ofReal]
  rw [h12]
  have hr : (rho z : ℂ) = 4 / (1 - (‖z‖ : ℂ) ^ 2) ^ 2 := by simp [rho]
  rw [hr]
  generalize (∫ ζ in unitDisc, F ζ / (1 - ζ * conj z) ^ 4) = J
  field_simp
  ring

/-- Holomorphy of the projector integral for a bounded coefficient. -/
theorem s8w_proj_integral_differentiableOn {g : ℂ → ℂ} {C : ℝ} (hg : ∀ ζ ∈ unitDisc, ‖g ζ‖ ≤ C)
    (hm : AEStronglyMeasurable g (volume.restrict unitDisc)) :
    DifferentiableOn ℂ (fun z : ℂ => ∫ ζ in unitDisc, g ζ / (1 - z * conj ζ) ^ 4) unitDisc := by
  have hC : 0 ≤ C := (norm_nonneg _).trans (hg 0 (by simp [unitDisc]))
  have hDm : MeasurableSet unitDisc := measurableSet_ball
  intro z0 hz0
  have hz01 : ‖z0‖ < 1 := mem_ball_zero_iff.mp hz0
  set R : ℝ := (1 + ‖z0‖) / 2 with hR
  have hR1 : R < 1 := by rw [hR]; linarith
  have h1R : 0 < 1 - R := by linarith
  have hball : ball z0 ((1 - ‖z0‖) / 2) ∈ 𝓝 z0 := ball_mem_nhds z0 (by linarith)
  have hzR : ∀ z ∈ ball z0 ((1 - ‖z0‖) / 2), ‖z‖ ≤ R := by
    intro z hz
    have := norm_le_of_mem_closedBall (ball_subset_closedBall hz)
    rw [hR]; linarith
  have hmeas : ∀ z : ℂ, AEStronglyMeasurable (fun ζ => g ζ / (1 - z * conj ζ) ^ 4) (volume.restrict unitDisc) := by
    intro z
    exact (hm.aemeasurable.div (by fun_prop : Measurable fun ζ : ℂ => (1 - z * conj ζ) ^ 4).aemeasurable).aestronglyMeasurable
  have hmeas' : ∀ z : ℂ, AEStronglyMeasurable (fun ζ => 4 * conj ζ * g ζ / (1 - z * conj ζ) ^ 5)
      (volume.restrict unitDisc) := by
    intro z
    exact ((((by fun_prop : Continuous fun ζ : ℂ => 4 * conj ζ).aestronglyMeasurable).mul hm).aemeasurable.div
      (by fun_prop : Measurable fun ζ : ℂ => (1 - z * conj ζ) ^ 5).aemeasurable).aestronglyMeasurable
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume.restrict unitDisc)
    (F := fun z ζ => g ζ / (1 - z * conj ζ) ^ 4)
    (F' := fun z ζ => 4 * conj ζ * g ζ / (1 - z * conj ζ) ^ 5) (x₀ := z0)
    (bound := fun _ => 4 * C / (1 - R) ^ 5) (s := ball z0 ((1 - ‖z0‖) / 2))
    hball (Eventually.of_forall hmeas) ?_ (hmeas' z0) ?_ ?_ ?_
  · exact key.2.differentiableAt.differentiableWithinAt
  · refine Integrable.mono' (g := fun _ => C / (1 - R) ^ 4) ?_ (hmeas z0) ?_
    · exact integrableOn_const (measure_ball_lt_top).ne (by simp)
    · refine (ae_restrict_iff' hDm).mpr (Eventually.of_forall fun ζ hζ => ?_)
      have hl := s8w_den_lower (hzR z0 (mem_ball_self (by linarith))) (mem_ball_zero_iff.mp hζ)
      rw [norm_div, norm_pow]
      exact div_le_div₀ hC (hg ζ hζ) (by positivity) (pow_le_pow_left₀ h1R.le hl 4)
  · refine (ae_restrict_iff' hDm).mpr (Eventually.of_forall fun ζ hζ z hz => ?_)
    have hl := s8w_den_lower (hzR z hz) (mem_ball_zero_iff.mp hζ)
    have hnum : ‖4 * conj ζ * g ζ‖ ≤ 4 * C := by
      rw [norm_mul, norm_mul, Complex.norm_conj]
      have : ‖ζ‖ ≤ 1 := (mem_ball_zero_iff.mp hζ).le
      have h4 : ‖(4 : ℂ)‖ = 4 := by simp
      rw [h4]
      nlinarith [norm_nonneg ζ, norm_nonneg (g ζ), hg ζ hζ]
    rw [norm_div, norm_pow]
    exact div_le_div₀ (by positivity) hnum (by positivity) (pow_le_pow_left₀ h1R.le hl 5)
  · exact integrableOn_const (measure_ball_lt_top).ne (by simp)
  · refine (ae_restrict_iff' hDm).mpr (Eventually.of_forall fun ζ hζ z hz => ?_)
    have hl := s8w_den_lower (hzR z hz) (mem_ball_zero_iff.mp hζ)
    have hne : 1 - z * conj ζ ≠ 0 := by
      intro h0; rw [h0, norm_zero] at hl; linarith
    have h1 : HasDerivAt (fun z : ℂ => 1 - z * conj ζ) (-(conj ζ)) z := by
      simpa using ((hasDerivAt_id z).mul_const (conj ζ)).const_sub 1
    have h2 := ((h1.pow 4).inv (pow_ne_zero 4 hne)).const_mul (g ζ)
    have e : (fun z : ℂ => g ζ / (1 - z * conj ζ) ^ 4) =
        fun z => g ζ * ((1 - z * conj ζ) ^ 4)⁻¹ := by
      funext z; rw [div_eq_mul_inv]
    rw [e]
    refine HasDerivAt.congr_deriv h2 ?_
    simp only [Pi.pow_apply, Nat.cast_ofNat]
    field_simp

/-- **P3.** -/
theorem s8w_proj_harmonic_proof {G : ℂ → ℂ} (hG : AEStronglyMeasurable G (volume.restrict unitDisc))
    (hGb : ∃ C, ∀ z ∈ unitDisc, ‖G z‖ ≤ C) : IsHarmonicD (harmonicProjD G) := by
  obtain ⟨C, hC⟩ := hGb
  refine ⟨fun z => (3 / π : ℂ) * ∫ ζ in unitDisc, conj (G ζ) / (1 - z * conj ζ) ^ 4, ?_, ⟨3 * C, fun z hz => ?_⟩,
    fun z hz => ?_⟩
  · refine (s8w_proj_integral_differentiableOn (g := fun ζ => conj (G ζ)) (C := C) (fun ζ hζ => ?_) ?_).const_mul _
    · rw [Complex.norm_conj]; exact hC ζ hζ
    · exact Complex.continuous_conj.comp_aestronglyMeasurable hG
  · have h := harmonicProjD_norm_le hC (mem_ball_zero_iff.mp hz)
    have e : (1 - (‖z‖ : ℂ) ^ 2) ^ 2 * ((3 / π : ℂ) * ∫ ζ in unitDisc, conj (G ζ) / (1 - z * conj ζ) ^ 4) =
        conj (harmonicProjD G z) := by
      unfold harmonicProjD
      simp only [map_mul, map_div₀, map_pow, map_sub, map_one, Complex.conj_ofReal, map_ofNat]
      rw [← integral_conj]
      have : (∫ ζ in unitDisc, conj (G ζ / (1 - ζ * conj z) ^ 4)) =
          ∫ ζ in unitDisc, conj (G ζ) / (1 - z * conj ζ) ^ 4 := by
        apply integral_congr_ae
        filter_upwards with ζ
        simp only [map_div₀, map_pow, map_sub, map_one, map_mul, Complex.conj_conj]
        rw [mul_comm (conj ζ) z]
      rw [this]
      ring
    rw [e, Complex.norm_conj]
    exact h
  · unfold harmonicProjD
    simp only [map_mul, map_div₀, map_pow, map_sub, map_one, Complex.conj_ofReal, map_ofNat]
    rw [← integral_conj]
    have : (∫ ζ in unitDisc, conj (conj (G ζ) / (1 - z * conj ζ) ^ 4)) =
        ∫ ζ in unitDisc, G ζ / (1 - ζ * conj z) ^ 4 := by
      apply integral_congr_ae
      filter_upwards with ζ
      simp only [map_div₀, map_pow, map_sub, map_one, map_mul, Complex.conj_conj]
      rw [mul_comm (conj z) ζ]
    rw [this]
    ring

/-- `∫_𝔻 |1 - ζ z̄|⁻⁴ d²ζ = π/(1 - |z|²)²` as a lower integral. -/
theorem s8w_kernel_lintegral {z : ℂ} (hz : ‖z‖ < 1) :
    ∫⁻ ζ in unitDisc, ENNReal.ofReal ‖(1 - ζ * conj z) ^ 4‖⁻¹ = ENNReal.ofReal (π / (1 - ‖z‖ ^ 2) ^ 2) := by
  rw [← proj_kernel_integral hz]
  exact (ofReal_integral_eq_lintegral_ofReal (proj_kernel_integrableOn hz)
    (Eventually.of_forall fun _ => inv_nonneg.mpr (norm_nonneg _))).symm

/-- The kernel is symmetric in modulus: `|1 - ζ z̄| = |1 - z ζ̄|`. -/
theorem s8w_kernel_symm (ζ z : ℂ) : ‖(1 - ζ * conj z) ^ 4‖ = ‖(1 - z * conj ζ) ^ 4‖ := by
  rw [← Complex.norm_conj ((1 - z * conj ζ) ^ 4)]
  simp only [map_pow, map_sub, map_one, map_mul, Complex.conj_conj]
  rw [mul_comm]

/-- **P1.** -/
theorem s8w_proj_integrable_proof {F : ℂ → ℂ} (hF : AEStronglyMeasurable F (volume.restrict unitDisc))
    (hFi : IntegrableOn (fun z => F z * rho z) unitDisc) :
    IntegrableOn (fun z => harmonicProjD F z * rho z) unitDisc := by
  have hDm : MeasurableSet unitDisc := measurableSet_ball
  set K : ℂ × ℂ → ℝ := fun p => ‖F p.2‖ * ‖(1 - p.2 * conj p.1) ^ 4‖⁻¹ with hK
  have hKm : AEStronglyMeasurable K ((volume.restrict unitDisc).prod (volume.restrict unitDisc)) := by
    have h1 : AEStronglyMeasurable (fun p : ℂ × ℂ => ‖F p.2‖)
        ((volume.restrict unitDisc).prod (volume.restrict unitDisc)) :=
      hF.norm.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_snd
    have h2 : Measurable (fun p : ℂ × ℂ => ‖(1 - p.2 * conj p.1) ^ 4‖⁻¹) := by fun_prop
    exact h1.mul h2.aestronglyMeasurable
  have hKi : Integrable K ((volume.restrict unitDisc).prod (volume.restrict unitDisc)) := by
    rw [integrable_prod_iff' hKm]
    refine ⟨(ae_restrict_iff' hDm).mpr (Eventually.of_forall fun ζ hζ => ?_), ?_⟩
    · have hk := proj_kernel_integrableOn (mem_ball_zero_iff.mp hζ)
      refine (hk.const_mul ‖F ζ‖).congr (Eventually.of_forall fun z => ?_)
      simp only [hK]
      rw [s8w_kernel_symm z ζ]
    · refine (hFi.norm.const_mul (π / 4)).congr ((ae_restrict_iff' hDm).mpr
        (Eventually.of_forall fun ζ hζ => ?_))
      have hζ1 : ‖ζ‖ < 1 := mem_ball_zero_iff.mp hζ
      have e : ∀ z : ℂ, ‖K (z, ζ)‖ = ‖F ζ‖ * ‖(1 - z * conj ζ) ^ 4‖⁻¹ := by
        intro z
        simp only [hK]
        rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (norm_nonneg _) (inv_nonneg.mpr (norm_nonneg _))),
          s8w_kernel_symm]
      simp only [e]
      rw [integral_const_mul, proj_kernel_integral hζ1, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (show 0 ≤ rho ζ by unfold rho; positivity)]
      unfold rho
      have hs : 0 < 1 - ‖ζ‖ ^ 2 := by nlinarith [norm_nonneg ζ]
      field_simp
  have hI := hKi.integral_prod_left
  have hPm : AEStronglyMeasurable (fun z => harmonicProjD F z * rho z) (volume.restrict unitDisc) := by
    have hint : AEStronglyMeasurable (fun z => ∫ ζ in unitDisc, F ζ / (1 - ζ * conj z) ^ 4)
        (volume.restrict unitDisc) := by
      have hf : AEStronglyMeasurable (fun p : ℂ × ℂ => F p.2 / (1 - p.2 * conj p.1) ^ 4)
          ((volume.restrict unitDisc).prod (volume.restrict unitDisc)) := by
        have h1 : AEStronglyMeasurable (fun p : ℂ × ℂ => F p.2)
            ((volume.restrict unitDisc).prod (volume.restrict unitDisc)) :=
          hF.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_snd
        exact (h1.aemeasurable.div (by fun_prop : Measurable fun p : ℂ × ℂ =>
          (1 - p.2 * conj p.1) ^ 4).aemeasurable).aestronglyMeasurable
      exact hf.integral_prod_right'
    have hc : Continuous fun z : ℂ => (3 * (1 - (‖z‖ : ℂ) ^ 2) ^ 2 / π : ℂ) := by fun_prop
    have hr : Measurable fun z : ℂ => ((rho z : ℝ) : ℂ) := by
      unfold rho; fun_prop
    exact (hc.aestronglyMeasurable.mul hint).mul hr.aestronglyMeasurable
  refine Integrable.mono' (hI.const_mul (12 / π)) hPm ((ae_restrict_iff' hDm).mpr
    (Eventually.of_forall fun z hz => ?_))
  have hz1 : ‖z‖ < 1 := mem_ball_zero_iff.mp hz
  have hs : 0 < 1 - ‖z‖ ^ 2 := by nlinarith [norm_nonneg z]
  have hle : ‖∫ ζ in unitDisc, F ζ / (1 - ζ * conj z) ^ 4‖ ≤ ∫ ζ in unitDisc, K (z, ζ) := by
    refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
    apply integral_congr_ae
    filter_upwards with ζ
    simp only [hK]
    rw [norm_div, div_eq_mul_inv]
  have hP := harmonicProjD_norm_le_of hz1 hle
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (show 0 ≤ rho z by unfold rho; positivity)]
  calc ‖harmonicProjD F z‖ * rho z ≤ 3 * (1 - ‖z‖ ^ 2) ^ 2 / π * (∫ ζ in unitDisc, K (z, ζ)) * rho z :=
        mul_le_mul_of_nonneg_right hP (by unfold rho; positivity)
    _ = 12 / π * ∫ ζ in unitDisc, K (z, ζ) := by
        generalize (∫ ζ in unitDisc, K (z, ζ)) = J
        unfold rho
        field_simp
        ring

/-- Measurability of the kernel integrand in the first variable. -/
theorem s8w_ker_meas {G : ℂ → ℂ} (hG : AEStronglyMeasurable G (volume.restrict unitDisc)) (c ζ : ℂ) :
    AEStronglyMeasurable (fun z => G z * c / (1 - z * conj ζ) ^ 4) (volume.restrict unitDisc) :=
  ((hG.mul aestronglyMeasurable_const).aemeasurable.div (by fun_prop : Measurable fun z : ℂ =>
    (1 - z * conj ζ) ^ 4).aemeasurable).aestronglyMeasurable

/-- The pointwise bound `|G(z) c (1 - z ζ̄)⁻⁴| ≤ C |c| |1 - z ζ̄|⁻⁴`. -/
theorem s8w_ker_bound {G : ℂ → ℂ} {C : ℝ} (hC : ∀ z ∈ unitDisc, ‖G z‖ ≤ C) (c ζ : ℂ) {z : ℂ}
    (hz : z ∈ unitDisc) :
    ‖G z * c / (1 - z * conj ζ) ^ 4‖ ≤ C * ‖c‖ * ‖(1 - z * conj ζ) ^ 4‖⁻¹ := by
  rw [norm_div, norm_mul, div_eq_mul_inv]
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hC z hz) (norm_nonneg _))
    (inv_nonneg.mpr (norm_nonneg _))

/-- Integrability of the symmetric kernel on `𝔻 × 𝔻`. -/
theorem s8w_ker_prod_integrable {G F : ℂ → ℂ} (hG : AEStronglyMeasurable G (volume.restrict unitDisc))
    {C : ℝ} (hC : ∀ z ∈ unitDisc, ‖G z‖ ≤ C) (hF : AEStronglyMeasurable F (volume.restrict unitDisc))
    (hFi : IntegrableOn (fun z => F z * rho z) unitDisc) :
    Integrable (Function.uncurry fun ζ z : ℂ => G z * conj (F ζ) / (1 - z * conj ζ) ^ 4)
      ((volume.restrict unitDisc).prod (volume.restrict unitDisc)) := by
  have hDm : MeasurableSet unitDisc := measurableSet_ball
  have hfm : AEStronglyMeasurable (Function.uncurry fun ζ z : ℂ => G z * conj (F ζ) / (1 - z * conj ζ) ^ 4)
      ((volume.restrict unitDisc).prod (volume.restrict unitDisc)) := by
    have h1 : AEStronglyMeasurable (fun p : ℂ × ℂ => G p.2)
        ((volume.restrict unitDisc).prod (volume.restrict unitDisc)) :=
      hG.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_snd
    have h2 : AEStronglyMeasurable (fun p : ℂ × ℂ => conj (F p.1))
        ((volume.restrict unitDisc).prod (volume.restrict unitDisc)) :=
      (Complex.continuous_conj.comp_aestronglyMeasurable hF).comp_quasiMeasurePreserving
        Measure.quasiMeasurePreserving_fst
    have h3 := ((h1.mul h2).aemeasurable.div (by fun_prop : Measurable fun p : ℂ × ℂ =>
      (1 - p.2 * conj p.1) ^ 4).aemeasurable).aestronglyMeasurable
    exact h3
  rw [integrable_prod_iff hfm]
  refine ⟨(ae_restrict_iff' hDm).mpr (Eventually.of_forall fun ζ hζ => ?_), ?_⟩
  · have hk := (proj_kernel_integrableOn (mem_ball_zero_iff.mp hζ)).const_mul (C * ‖conj (F ζ)‖)
    exact Integrable.mono' hk (s8w_ker_meas hG (conj (F ζ)) ζ)
      ((ae_restrict_iff' hDm).mpr (Eventually.of_forall fun z hz => s8w_ker_bound hC _ ζ hz))
  · have hb : Integrable (fun ζ => C * (π / 4) * ‖F ζ * rho ζ‖) (volume.restrict unitDisc) :=
      hFi.norm.const_mul _
    refine Integrable.mono' hb hfm.norm.integral_prod_right' ((ae_restrict_iff' hDm).mpr
      (Eventually.of_forall fun ζ hζ => ?_))
    have hζ1 : ‖ζ‖ < 1 := mem_ball_zero_iff.mp hζ
    rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
    have hint : Integrable (fun z => C * ‖conj (F ζ)‖ * ‖(1 - z * conj ζ) ^ 4‖⁻¹) (volume.restrict unitDisc) :=
      (proj_kernel_integrableOn hζ1).const_mul _
    have hle : ∫ z in unitDisc, ‖G z * conj (F ζ) / (1 - z * conj ζ) ^ 4‖ ≤
        ∫ z in unitDisc, C * ‖conj (F ζ)‖ * ‖(1 - z * conj ζ) ^ 4‖⁻¹ :=
      setIntegral_mono_on ((hint.mono' (s8w_ker_meas hG (conj (F ζ)) ζ)
        ((ae_restrict_iff' hDm).mpr (Eventually.of_forall fun z hz => s8w_ker_bound hC _ ζ hz))).norm)
        hint hDm fun z hz => s8w_ker_bound hC _ ζ hz
    refine le_trans (le_of_eq ?_) (hle.trans (le_of_eq ?_))
    · rfl
    · rw [integral_const_mul, proj_kernel_integral hζ1, Complex.norm_conj, norm_mul, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg (show 0 ≤ rho ζ by unfold rho; positivity)]
      unfold rho
      have hs : 0 < 1 - ‖ζ‖ ^ 2 := by nlinarith [norm_nonneg ζ]
      field_simp

/-- **P2.** -/
theorem s8w_proj_symm_proof {G F : ℂ → ℂ} (hG : AEStronglyMeasurable G (volume.restrict unitDisc))
    (hGb : ∃ C, ∀ z ∈ unitDisc, ‖G z‖ ≤ C) (hF : AEStronglyMeasurable F (volume.restrict unitDisc))
    (hFi : IntegrableOn (fun z => F z * rho z) unitDisc) :
    l2InnerD G (harmonicProjD F) = l2InnerD (harmonicProjD G) F := by
  obtain ⟨C, hC⟩ := hGb
  have hDm : MeasurableSet unitDisc := measurableSet_ball
  have hfi := s8w_ker_prod_integrable hG hC hF hFi
  have hL : l2InnerD G (harmonicProjD F) = (12 / π : ℂ) *
      ∫ z in unitDisc, ∫ ζ in unitDisc, G z * conj (F ζ) / (1 - z * conj ζ) ^ 4 := by
    unfold l2InnerD
    rw [← integral_const_mul]
    refine setIntegral_congr_fun hDm fun z hz => ?_
    have hz1 : ‖z‖ < 1 := mem_ball_zero_iff.mp hz
    have hρ : (rho z : ℂ) ≠ 0 := by
      have hs : 0 < 1 - ‖z‖ ^ 2 := by nlinarith [norm_nonneg z]
      exact Complex.ofReal_ne_zero.mpr (by unfold rho; positivity)
    have hI : ∫ ζ in unitDisc, G z * conj (F ζ) / (1 - z * conj ζ) ^ 4 =
        G z * ∫ ζ in unitDisc, conj (F ζ) / (1 - z * conj ζ) ^ 4 := by
      rw [← integral_const_mul]
      congr 1
      funext ζ
      ring
    rw [hI, s8w_proj_repr F hz]
    generalize (∫ ζ in unitDisc, conj (F ζ) / (1 - z * conj ζ) ^ 4) = J
    simp only [map_mul, Complex.conj_conj, map_inv₀, Complex.conj_ofReal]
    field_simp
  have hR : l2InnerD (harmonicProjD G) F = (12 / π : ℂ) *
      ∫ ζ in unitDisc, ∫ z in unitDisc, G z * conj (F ζ) / (1 - z * conj ζ) ^ 4 := by
    unfold l2InnerD
    rw [← integral_const_mul]
    refine setIntegral_congr_fun hDm fun ζ hζ => ?_
    have hI : ∫ z in unitDisc, G z * conj (F ζ) / (1 - z * conj ζ) ^ 4 =
        conj (F ζ) * ∫ z in unitDisc, G z / (1 - z * conj ζ) ^ 4 := by
      rw [← integral_const_mul]
      congr 1
      funext z
      ring
    have hs : (1 : ℂ) - (‖ζ‖ : ℂ) ^ 2 ≠ 0 := by
      have : (1 : ℝ) - ‖ζ‖ ^ 2 ≠ 0 := by nlinarith [norm_nonneg ζ, mem_ball_zero_iff.mp hζ]
      exact_mod_cast this
    have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    rw [hI]
    unfold harmonicProjD
    generalize (∫ z in unitDisc, G z / (1 - z * conj ζ) ^ 4) = J
    simp only [rho]
    push_cast
    field_simp
    ring
  rw [hL, hR]
  congr 1
  exact (integral_integral_swap hfi).symm

/-- The `SU(1,1)` covariance of the Bergman kernel: `1 - γa \overline{γb} = (1 - a b̄)/((c a + d) \overline{(c b + d)})`. -/
theorem s8w_su11_kernel {g : SL2C} (hg : IsSU11 g) {a b : ℂ} (ha : g 1 0 * a + g 1 1 ≠ 0)
    (hb : g 1 0 * b + g 1 1 ≠ 0) :
    1 - mob g a * conj (mob g b) = (1 - a * conj b) / ((g 1 0 * a + g 1 1) * conj (g 1 0 * b + g 1 1)) := by
  have hdet := fd_det g
  have hbc : conj (g 1 0 * b + g 1 1) ≠ 0 := (map_ne_zero _).mpr hb
  have hprod : (g 1 0 * a + g 1 1) * conj (g 1 0 * b + g 1 1) ≠ 0 := mul_ne_zero ha hbc
  have e : mob g a * conj (mob g b) = ((g 0 0 * a + g 0 1) * conj (g 0 0 * b + g 0 1)) /
      ((g 1 0 * a + g 1 1) * conj (g 1 0 * b + g 1 1)) := by
    unfold mob
    rw [map_div₀, div_mul_div_comm]
  rw [e, one_sub_div hprod]
  congr 1
  rw [hg.1, hg.2] at hdet ⊢
  simp only [map_add, map_mul, Complex.conj_conj]
  linear_combination (1 - a * conj b) * hdet

/-- `P` commutes with one `SU(1,1)` element under which `G` is invariant. -/
theorem s8w_proj_inv_elem {g : SL2C} (hs : IsSU11 g) {G : ℂ → ℂ}
    (hGg : ∀ z ∈ unitDisc, G (mob g z) * (conj (deriv (mob g) z) / deriv (mob g) z) = G z) {z : ℂ}
    (hz : z ∈ unitDisc) :
    harmonicProjD G (mob g z) * (conj (deriv (mob g) z) / deriv (mob g) z) = harmonicProjD G z := by
  have hz1 : ‖z‖ < 1 := mem_ball_zero_iff.mp hz
  have hDz := fdD_denom_ne hs hz1
  have hd : ∀ x ∈ unitDisc, deriv (mob g) x = 1 / (g 1 0 * x + g 1 1) ^ 2 := fun x hx =>
    (wp_mob_hasDerivAt g (fdD_denom_ne hs (mem_ball_zero_iff.mp hx))).deriv
  have hnsq : ∀ x : ℂ, ((‖x‖ : ℂ)) ^ 2 = x * conj x := fun x => by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; ring
  have hI : ∫ ζ in unitDisc, G ζ / (1 - ζ * conj (mob g z)) ^ 4 =
      conj (g 1 0 * z + g 1 1) ^ 4 * ∫ ξ in unitDisc, G ξ / (1 - ξ * conj z) ^ 4 := by
    have hcv := fdq_mob_integral_image g (show MeasurableSet unitDisc from measurableSet_ball)
      (fun w hw => fdD_denom_ne hs (mem_ball_zero_iff.mp hw)) (fun ζ => G ζ / (1 - ζ * conj (mob g z)) ^ 4)
    rw [(s8w_mob_conformal hs).2.2] at hcv
    rw [hcv, ← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_ball fun ξ hξ => ?_
    have hDξ := fdD_denom_ne hs (mem_ball_zero_iff.mp hξ)
    have hinv := hGg ξ hξ
    rw [hd ξ hξ] at hinv
    have hcξ : conj (g 1 0 * ξ + g 1 1) ≠ 0 := (map_ne_zero _).mpr hDξ
    have hGξ : G (mob g ξ) = G ξ * (conj (g 1 0 * ξ + g 1 1) ^ 2 / (g 1 0 * ξ + g 1 1) ^ 2) := by
      rw [← hinv]
      simp only [map_div₀, map_one, map_pow]
      field_simp
    have hk := s8w_su11_kernel hs hDξ hDz
    have hn : ((‖deriv (mob g) ξ‖ ^ 2 : ℝ) : ℂ) =
        1 / (g 1 0 * ξ + g 1 1) ^ 2 * conj (1 / (g 1 0 * ξ + g 1 1) ^ 2) := by
      rw [hd ξ hξ, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    have hK0 : 1 - ξ * conj z ≠ 0 := by
      have h := s8w_den_lower (le_refl ‖ξ‖) hz1
      intro h0
      rw [h0, norm_zero] at h
      linarith [mem_ball_zero_iff.mp hξ]
    have hcz : conj (g 1 0 * z + g 1 1) ≠ 0 := (map_ne_zero _).mpr hDz
    simp only [Complex.real_smul]
    rw [hn, hGξ, hk]
    simp only [map_div₀, map_one, map_pow]
    generalize g 1 0 * ξ + g 1 1 = Dξ at hDξ hcξ ⊢
    generalize g 1 0 * z + g 1 1 = Dz at hDz hcz ⊢
    generalize 1 - ξ * conj z = Kξ at hK0 ⊢
    generalize conj Dξ = cDξ at hcξ ⊢
    generalize conj Dz = cDz at hcz ⊢
    field_simp
  have hcz : conj (g 1 0 * z + g 1 1) ≠ 0 := (map_ne_zero _).mpr hDz
  have hk := s8w_su11_kernel hs hDz hDz
  unfold harmonicProjD
  rw [hI, hd z hz, hnsq (mob g z), hnsq z, hk]
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  generalize (∫ ξ in unitDisc, G ξ / (1 - ξ * conj z) ^ 4) = J
  simp only [map_div₀, map_one, map_pow]
  generalize g 1 0 * z + g 1 1 = Dz at hDz hcz ⊢
  generalize conj Dz = cDz at hcz ⊢
  generalize z * conj z = Z
  field_simp


/-- **P4.** -/
theorem s8w_proj_gammaInv_proof {Γ : Subgroup SL2C} (hΓ : IsFuchsian Γ) {G : ℂ → ℂ}
    (hG : AEStronglyMeasurable G (volume.restrict unitDisc)) (hGb : ∃ C, ∀ z ∈ unitDisc, ‖G z‖ ≤ C)
    (hGΓ : IsGammaInvD Γ G) : IsGammaInvD Γ (harmonicProjD G) := by
  have _h := And.intro hG hGb
  intro g hg z hz
  exact s8w_proj_inv_elem (hΓ.1 g hg) (hGΓ g hg) hz

/-- `ρ` is integrable on a set of finite hyperbolic area. -/
theorem s8w_rho_integrableOn {E : Set ℂ} (hEA : ∫⁻ z in E, ENNReal.ofReal (rho z) < ⊤) :
    IntegrableOn (fun z => rho z) E := by
  refine ⟨(by unfold rho; fun_prop : Measurable fun z : ℂ => rho z).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun z => by unfold rho; positivity)]
  exact hEA

/-- Measurability of `A(x) B(y) (1 - x ȳ)⁻⁴` for any product of restricted measures inside `𝔻 × 𝔻`. -/
theorem s8w_kerAB_meas {A B : ℂ → ℂ} {E₁ E₂ : Set ℂ} (hA : AEStronglyMeasurable A (volume.restrict E₁))
    (hB : AEStronglyMeasurable B (volume.restrict E₂)) :
    AEStronglyMeasurable (Function.uncurry fun x y : ℂ => A x * B y / (1 - x * conj y) ^ 4)
      ((volume.restrict E₁).prod (volume.restrict E₂)) := by
  have h1 : AEStronglyMeasurable (fun p : ℂ × ℂ => A p.1) ((volume.restrict E₁).prod (volume.restrict E₂)) :=
    hA.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_fst
  have h2 : AEStronglyMeasurable (fun p : ℂ × ℂ => B p.2) ((volume.restrict E₁).prod (volume.restrict E₂)) :=
    hB.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_snd
  have h3 : AEStronglyMeasurable (fun p : ℂ × ℂ => A p.1 * B p.2 / (1 - p.1 * conj p.2) ^ 4)
      ((volume.restrict E₁).prod (volume.restrict E₂)) :=
    ((h1.mul h2).aemeasurable.div (by fun_prop : Measurable fun p : ℂ × ℂ =>
      (1 - p.1 * conj p.2) ^ 4).aemeasurable).aestronglyMeasurable
  exact h3

/-- The kernel bound and its integral over one variable. -/
theorem s8w_kerAB_slice {A B : ℂ → ℂ} {CA CB : ℝ} (hCA : ∀ z ∈ unitDisc, ‖A z‖ ≤ CA)
    (hCB : ∀ z ∈ unitDisc, ‖B z‖ ≤ CB) :
    (∀ x ∈ unitDisc, ∀ y ∈ unitDisc,
      ‖A x * B y / (1 - x * conj y) ^ 4‖ ≤ CA * CB * ‖(1 - x * conj y) ^ 4‖⁻¹) ∧
    (∀ x ∈ unitDisc, Integrable (fun y => CA * CB * ‖(1 - x * conj y) ^ 4‖⁻¹) (volume.restrict unitDisc) ∧
      ∫ y in unitDisc, CA * CB * ‖(1 - x * conj y) ^ 4‖⁻¹ = CA * CB * π / 4 * rho x) ∧
    (∀ y ∈ unitDisc, Integrable (fun x => CA * CB * ‖(1 - x * conj y) ^ 4‖⁻¹) (volume.restrict unitDisc) ∧
      ∫ x in unitDisc, CA * CB * ‖(1 - x * conj y) ^ 4‖⁻¹ = CA * CB * π / 4 * rho y) := by
  have hCA0 : 0 ≤ CA := (norm_nonneg _).trans (hCA 0 (by simp [unitDisc]))
  refine ⟨fun x hx y hy => ?_, fun x hx => ⟨?_, ?_⟩, fun y hy => ⟨?_, ?_⟩⟩
  · rw [norm_div, norm_mul, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right (mul_le_mul (hCA x hx) (hCB y hy) (norm_nonneg _) hCA0)
      (inv_nonneg.mpr (norm_nonneg _))
  · refine ((proj_kernel_integrableOn (mem_ball_zero_iff.mp hx)).const_mul (CA * CB)).congr
      (Eventually.of_forall fun y => ?_)
    show CA * CB * ‖(1 - y * conj x) ^ 4‖⁻¹ = CA * CB * ‖(1 - x * conj y) ^ 4‖⁻¹
    rw [s8w_kernel_symm y x]
  · have hx1 : ‖x‖ < 1 := mem_ball_zero_iff.mp hx
    have e : ∀ y : ℂ, ‖(1 - x * conj y) ^ 4‖⁻¹ = ‖(1 - y * conj x) ^ 4‖⁻¹ := fun y => by
      rw [s8w_kernel_symm y x]
    simp only [e]
    rw [integral_const_mul, proj_kernel_integral hx1]
    unfold rho
    have hs : 0 < 1 - ‖x‖ ^ 2 := by nlinarith [norm_nonneg x]
    field_simp
  · exact (proj_kernel_integrableOn (mem_ball_zero_iff.mp hy)).const_mul (CA * CB)
  · have hy1 : ‖y‖ < 1 := mem_ball_zero_iff.mp hy
    rw [integral_const_mul, proj_kernel_integral hy1]
    unfold rho
    have hs : 0 < 1 - ‖y‖ ^ 2 := by nlinarith [norm_nonneg y]
    field_simp

/-- Integrability of `A(x) B(y) (1 - x ȳ)⁻⁴` on `E × 𝔻` and on `𝔻 × E`, for bounded `A, B` and `E ⊆ 𝔻` of finite
hyperbolic area. -/
theorem s8w_pair_integrable {A B : ℂ → ℂ} (hA : AEStronglyMeasurable A (volume.restrict unitDisc))
    {CA : ℝ} (hCA : ∀ z ∈ unitDisc, ‖A z‖ ≤ CA) (hB : AEStronglyMeasurable B (volume.restrict unitDisc))
    {CB : ℝ} (hCB : ∀ z ∈ unitDisc, ‖B z‖ ≤ CB) {E : Set ℂ} (hE : MeasurableSet E) (hED : E ⊆ unitDisc)
    (hEA : ∫⁻ z in E, ENNReal.ofReal (rho z) < ⊤) :
    Integrable (Function.uncurry fun x y : ℂ => A x * B y / (1 - x * conj y) ^ 4)
        ((volume.restrict E).prod (volume.restrict unitDisc)) ∧
      Integrable (Function.uncurry fun x y : ℂ => A x * B y / (1 - x * conj y) ^ 4)
        ((volume.restrict unitDisc).prod (volume.restrict E)) := by
  have hDm : MeasurableSet unitDisc := measurableSet_ball
  have hAE : AEStronglyMeasurable A (volume.restrict E) := hA.mono_measure (Measure.restrict_mono hED le_rfl)
  have hBE : AEStronglyMeasurable B (volume.restrict E) := hB.mono_measure (Measure.restrict_mono hED le_rfl)
  have hρi := s8w_rho_integrableOn hEA
  obtain ⟨hbound, hsx, hsy⟩ := s8w_kerAB_slice hCA hCB
  constructor
  · have hfm := s8w_kerAB_meas (A := A) (B := B) hAE hB
    rw [integrable_prod_iff hfm]
    refine ⟨(ae_restrict_iff' hE).mpr (Eventually.of_forall fun x hx => ?_), ?_⟩
    · have hm : AEStronglyMeasurable (fun y => A x * B y / (1 - x * conj y) ^ 4) (volume.restrict unitDisc) :=
        ((aestronglyMeasurable_const.mul hB).aemeasurable.div (by fun_prop : Measurable fun y : ℂ =>
          (1 - x * conj y) ^ 4).aemeasurable).aestronglyMeasurable
      exact Integrable.mono' (hsx x (hED hx)).1 hm ((ae_restrict_iff' hDm).mpr
        (Eventually.of_forall fun y hy => hbound x (hED hx) y hy))
    · refine Integrable.mono' (hρi.const_mul (CA * CB * π / 4)) hfm.norm.integral_prod_right'
        ((ae_restrict_iff' hE).mpr (Eventually.of_forall fun x hx => ?_))
      rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun _ => norm_nonneg _), ← (hsx x (hED hx)).2]
      refine integral_mono_of_nonneg (Eventually.of_forall fun _ => norm_nonneg _) (hsx x (hED hx)).1
        ((ae_restrict_iff' hDm).mpr (Eventually.of_forall fun y hy => ?_))
      exact hbound x (hED hx) y hy
  · have hfm := s8w_kerAB_meas (A := A) (B := B) hA hBE
    rw [integrable_prod_iff' hfm]
    refine ⟨(ae_restrict_iff' hE).mpr (Eventually.of_forall fun y hy => ?_), ?_⟩
    · have hm : AEStronglyMeasurable (fun x => A x * B y / (1 - x * conj y) ^ 4) (volume.restrict unitDisc) :=
        ((hA.mul aestronglyMeasurable_const).aemeasurable.div (by fun_prop : Measurable fun x : ℂ =>
          (1 - x * conj y) ^ 4).aemeasurable).aestronglyMeasurable
      exact Integrable.mono' (hsy y (hED hy)).1 hm ((ae_restrict_iff' hDm).mpr
        (Eventually.of_forall fun x hx => hbound x hx y (hED hy)))
    · refine Integrable.mono' (hρi.const_mul (CA * CB * π / 4)) hfm.norm.prod_swap.integral_prod_right'
        ((ae_restrict_iff' hE).mpr (Eventually.of_forall fun y hy => ?_))
      rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun _ => norm_nonneg _), ← (hsy y (hED hy)).2]
      refine integral_mono_of_nonneg (Eventually.of_forall fun _ => norm_nonneg _) (hsy y (hED hy)).1
        ((ae_restrict_iff' hDm).mpr (Eventually.of_forall fun x hx => ?_))
      exact hbound x hx y (hED hy)

/-- The pointwise identity behind the unfolding of P5 on one tile. -/
theorem s8w_tile_pointwise {g : SL2C} (hs : IsSU11 g) {l ν : ℂ → ℂ}
    (hlg : ∀ w ∈ unitDisc, l (mob g w) * (conj (deriv (mob g) w) / deriv (mob g) w) = l w)
    (hνg : ∀ w ∈ unitDisc, ν (mob g w) * (conj (deriv (mob g) w) / deriv (mob g) w) = ν w)
    {w y : ℂ} (hw : w ∈ unitDisc) (hy : y ∈ unitDisc) :
    ((‖deriv (mob g) w‖ ^ 2 : ℝ) : ℂ) * l (mob g w) *
        (((‖deriv (mob g) y‖ ^ 2 : ℝ) : ℂ) * (conj (ν (mob g y)) / (1 - mob g w * conj (mob g y)) ^ 4)) =
      l w * conj (ν y) / (1 - w * conj y) ^ 4 := by
  have hDw := fdD_denom_ne hs (mem_ball_zero_iff.mp hw)
  have hDy := fdD_denom_ne hs (mem_ball_zero_iff.mp hy)
  have hd : ∀ x ∈ unitDisc, deriv (mob g) x = 1 / (g 1 0 * x + g 1 1) ^ 2 := fun x hx =>
    (wp_mob_hasDerivAt g (fdD_denom_ne hs (mem_ball_zero_iff.mp hx))).deriv
  have hlw := hlg w hw
  have hνy := hνg y hy
  rw [hd w hw] at hlw
  rw [hd y hy] at hνy
  have hcw : conj (g 1 0 * w + g 1 1) ≠ 0 := (map_ne_zero _).mpr hDw
  have hcy : conj (g 1 0 * y + g 1 1) ≠ 0 := (map_ne_zero _).mpr hDy
  have hl' : l (mob g w) = l w * (conj (g 1 0 * w + g 1 1) ^ 2 / (g 1 0 * w + g 1 1) ^ 2) := by
    rw [← hlw]; simp only [map_div₀, map_one, map_pow]; field_simp
  have hν' : ν (mob g y) = ν y * (conj (g 1 0 * y + g 1 1) ^ 2 / (g 1 0 * y + g 1 1) ^ 2) := by
    rw [← hνy]; simp only [map_div₀, map_one, map_pow]; field_simp
  have hK0 : 1 - w * conj y ≠ 0 := by
    have h := s8w_den_lower (le_refl ‖w‖) (mem_ball_zero_iff.mp hy)
    intro h0
    rw [h0, norm_zero] at h
    linarith [mem_ball_zero_iff.mp hw]
  have hk := s8w_su11_kernel hs hDw hDy
  have hn : ∀ x ∈ unitDisc, ((‖deriv (mob g) x‖ ^ 2 : ℝ) : ℂ) =
      1 / (g 1 0 * x + g 1 1) ^ 2 * conj (1 / (g 1 0 * x + g 1 1) ^ 2) := fun x hx => by
    rw [hd x hx, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  rw [hn w hw, hn y hy, hl', hν', hk]
  simp only [map_div₀, map_one, map_pow, map_mul, Complex.conj_conj]
  generalize g 1 0 * w + g 1 1 = Dw at hDw hcw ⊢
  generalize g 1 0 * y + g 1 1 = Dy at hDy hcy ⊢
  generalize 1 - w * conj y = Kw at hK0 ⊢
  generalize conj Dw = cDw at hcw ⊢
  generalize conj Dy = cDy at hcy ⊢
  field_simp

/-- **P5.** -/
theorem s8w_selfAdj_quot_proof {Γ : Subgroup SL2C} (hΓ : IsFuchsian Γ) {D : Set ℂ} (hD : IsFundDomainD Γ D)
    (hA : ∫⁻ z in D, ENNReal.ofReal (rho z) < ⊤) {l ν : ℂ → ℂ}
    (hl : AEStronglyMeasurable l (volume.restrict unitDisc)) (hlb : ∃ C, ∀ z ∈ unitDisc, ‖l z‖ ≤ C)
    (hlΓ : IsGammaInvD Γ l) (hν : IsHarmonicD ν) (hνΓ : IsGammaInvD Γ ν) :
    ∫ z in D, harmonicProjD l z * conj (ν z) * rho z = ∫ z in D, l z * conj (ν z) * rho z := by
  classical
  obtain ⟨Cl, hCl⟩ := hlb
  obtain ⟨Cν, hCν⟩ := harmonicD_bound hν
  have hDm' : MeasurableSet unitDisc := measurableSet_ball
  have hνm : AEStronglyMeasurable ν (volume.restrict unitDisc) :=
    (harmonicD_continuousOn hν).aestronglyMeasurable hDm'
  have hcνm : AEStronglyMeasurable (fun z => conj (ν z)) (volume.restrict unitDisc) :=
    Complex.continuous_conj.comp_aestronglyMeasurable hνm
  have hcνb : ∀ z ∈ unitDisc, ‖conj (ν z)‖ ≤ Cν := fun z hz => by rw [Complex.norm_conj]; exact hCν z hz
  have hDm := hD.1
  have hDD := hD.2.1
  obtain ⟨hI1, hI2⟩ := s8w_pair_integrable hl hCl hcνm hcνb hDm hDD hA
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  -- the left side
  have hL : ∫ z in D, harmonicProjD l z * conj (ν z) * rho z =
      (12 / π : ℂ) * ∫ ζ in unitDisc, l ζ * ∫ z in D, conj (ν z) / (1 - ζ * conj z) ^ 4 := by
    have h1 : ∀ z ∈ D, harmonicProjD l z * conj (ν z) * rho z =
        (12 / π : ℂ) * ∫ ζ in unitDisc, l ζ * conj (ν z) / (1 - ζ * conj z) ^ 4 := by
      intro z hz
      have hz1 : ‖z‖ < 1 := mem_ball_zero_iff.mp (hDD hz)
      have hI : ∫ ζ in unitDisc, l ζ * conj (ν z) / (1 - ζ * conj z) ^ 4 =
          conj (ν z) * ∫ ζ in unitDisc, l ζ / (1 - ζ * conj z) ^ 4 := by
        rw [← integral_const_mul]; congr 1; funext ζ; ring
      have hs : (1 : ℂ) - (‖z‖ : ℂ) ^ 2 ≠ 0 := by
        have : (1 : ℝ) - ‖z‖ ^ 2 ≠ 0 := by nlinarith [norm_nonneg z]
        exact_mod_cast this
      unfold harmonicProjD
      rw [hI]
      generalize (∫ ζ in unitDisc, l ζ / (1 - ζ * conj z) ^ 4) = J
      simp only [rho]
      push_cast
      field_simp
      ring
    rw [setIntegral_congr_fun hDm h1, integral_const_mul]
    congr 1
    have hsw := integral_integral_swap hI2
    rw [← hsw]
    refine setIntegral_congr_fun hDm' fun ζ _ => ?_
    rw [← integral_const_mul]
    congr 1
    funext z
    ring
  -- the right side
  have hR : ∫ z in D, l z * conj (ν z) * rho z =
      (12 / π : ℂ) * ∫ w in D, l w * ∫ y in unitDisc, conj (ν y) / (1 - w * conj y) ^ 4 := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun hDm fun w hw => ?_
    have hwD := hDD hw
    have hw1 : ‖w‖ < 1 := mem_ball_zero_iff.mp hwD
    have hrep := s8w_proj_repr ν hwD
    rw [harmonicProjD_self hν hwD] at hrep
    have hρ : (rho w : ℂ) ≠ 0 := by
      have hs : 0 < 1 - ‖w‖ ^ 2 := by nlinarith [norm_nonneg w]
      exact Complex.ofReal_ne_zero.mpr (by unfold rho; positivity)
    have h12 : conj (12 / π : ℂ) = 12 / π := by
      rw [show (12 / π : ℂ) = ((12 / π : ℝ) : ℂ) by push_cast; rfl, Complex.conj_ofReal]
    have e : conj (ν w) * rho w = (12 / π) * ∫ y in unitDisc, conj (ν y) / (1 - w * conj y) ^ 4 := by
      rw [hrep, map_mul, map_inv₀, Complex.conj_ofReal, Complex.conj_conj]
      field_simp
    calc l w * conj (ν w) * rho w = l w * (conj (ν w) * rho w) := by ring
      _ = _ := by rw [e]; ring
  -- unfolding and the tile decomposition
  haveI : DiscreteTopology Γ := hΓ.2
  set A := (fun g : SL2C => mob g) '' (Γ : Set SL2C) with hAdef
  haveI : Countable A := (fd_countable (Γ := Γ)).image _ |>.to_subtype
  have hΦi : IntegrableOn (fun ζ => l ζ * ∫ z in D, conj (ν z) / (1 - ζ * conj z) ^ 4) unitDisc := by
    refine hI2.integral_prod_left.congr (Eventually.of_forall fun ζ => ?_)
    simp only [Function.uncurry_apply_pair]
    rw [← integral_const_mul]
    congr 1
    funext z
    ring
  have hU := fdD_hasSum_integral_unfold hΓ hD hΦi
  have hsplit := fdD_restrict_eq_sum hΓ hD
  have hgi : Integrable (Function.uncurry fun w y : ℂ => l w * conj (ν y) / (1 - w * conj y) ^ 4)
      (Measure.sum fun b : A => (volume.restrict D).prod
        (volume.restrict {z : ℂ | ‖z‖ < 1 ∧ (b : ℂ → ℂ) z ∈ D})) := by
    rw [← Measure.prod_sum_right, ← hsplit]
    exact hI1
  have hS := hasSum_integral_measure hgi
  rw [← Measure.prod_sum_right, ← hsplit, integral_prod _ hI1] at hS
  have hterm : ∀ b : A, ∫ p, Function.uncurry (fun w y : ℂ => l w * conj (ν y) / (1 - w * conj y) ^ 4) p
      ∂((volume.restrict D).prod (volume.restrict {z : ℂ | ‖z‖ < 1 ∧ (b : ℂ → ℂ) z ∈ D})) =
      ∫ w in D, (‖deriv (b : ℂ → ℂ) w‖ ^ 2) • (l ((b : ℂ → ℂ) w) *
        ∫ z in D, conj (ν z) / (1 - (b : ℂ → ℂ) w * conj z) ^ 4) := by
    intro b
    rw [integral_prod _ (hgi.mono_measure (Measure.le_sum (fun b : A => (volume.restrict D).prod
      (volume.restrict {z : ℂ | ‖z‖ < 1 ∧ (b : ℂ → ℂ) z ∈ D})) b))]
    obtain ⟨g, hg, hgb⟩ := b.2
    have hs := hΓ.1 g hg
    refine setIntegral_congr_fun hDm fun w hw => ?_
    have hwD := hDD hw
    simp only [Function.uncurry_apply_pair]
    rw [← hgb]
    set T : Set ℂ := {z : ℂ | ‖z‖ < 1 ∧ mob g z ∈ D} with hT
    have hTm : MeasurableSet T :=
      (measurableSet_lt measurable_norm measurable_const).inter ((fd_measurable_mob g) hDm)
    have hTimg : mob g '' T = D := by
      ext z
      constructor
      · rintro ⟨y, hy, rfl⟩; exact hy.2
      · intro hz
        have hz1 : ‖z‖ < 1 := mem_ball_zero_iff.mp (hDD hz)
        have hgi' := isSU11_inv hs
        have h := fd_inv_step g⁻¹ (fdD_denom_ne hgi' hz1)
        rw [inv_inv] at h
        exact ⟨mob g⁻¹ z, ⟨fdD_mob_lt hgi' hz1, by rw [h.2]; exact hz⟩, h.2⟩
    have hcv := fdq_mob_integral_image g hTm (fun y hy => fdD_denom_ne hs hy.1)
      (fun z => conj (ν z) / (1 - mob g w * conj z) ^ 4)
    rw [hTimg] at hcv
    rw [hcv, Complex.real_smul, ← integral_const_mul, ← integral_const_mul]
    refine setIntegral_congr_fun hTm fun y hy => ?_
    have hyD : y ∈ unitDisc := mem_ball_zero_iff.mpr hy.1
    rw [Complex.real_smul, ← mul_assoc]
    exact (s8w_tile_pointwise hs (hlΓ g hg) (hνΓ g hg) hwD hyD).symm
  simp only [hterm] at hS
  have heq := hU.unique hS
  rw [hL, hR, heq]
  congr 1
  refine setIntegral_congr_fun hDm fun w _ => ?_
  simp only [Function.uncurry_apply_pair]
  rw [← integral_const_mul]
  congr 1
  funext y
  ring

/-! ## A: the limits -/

/-- `(w_κ)_z` is continuous on `𝔻`. -/
theorem s8w_dz_continuousOn {κ : ℂ → ℂ} (hκ : IsHarmonicD κ) {k : ℝ} (hk1 : k < 1)
    (hk : ∀ z ∈ unitDisc, ‖κ z‖ ≤ k) : ContinuousOn (dz (wD κ)) unitDisc := by
  intro z hz
  have hza := (s8w_wD_analytic hκ hk1 hk z hz).1
  have hfd : ContinuousAt (fderiv ℝ (wD κ)) z := (hza.fderiv).continuousAt
  have e : dz (wD κ) = fun x => (fderiv ℝ (wD κ) x 1 - I * fderiv ℝ (wD κ) x I) / 2 := rfl
  rw [e]
  exact (((hfd.clm_apply continuousAt_const).sub
    (continuousAt_const.mul (hfd.clm_apply continuousAt_const))).div_const 2).continuousWithinAt

/-- The chain rule for `w_κ ∘ γ = γ_κ ∘ w_κ`: `(w_κ)_z(γ u) γ'(u) = γ_κ'(w_κ u) (w_κ)_z(u)`. -/
theorem s8w_dz_equivariant {κ : ℂ → ℂ} (hκ : IsHarmonicD κ) {k : ℝ} (hk1 : k < 1)
    (hk : ∀ z ∈ unitDisc, ‖κ z‖ ≤ k) {g g' : SL2C} (hg : IsSU11 g) (hg' : IsSU11 g')
    (hrel : ∀ u ∈ unitDisc, wD κ (mob g u) = mob g' (wD κ u)) {u : ℂ} (hu : u ∈ unitDisc) :
    dz (wD κ) (mob g u) * deriv (mob g) u = deriv (mob g') (wD κ u) * dz (wD κ) u := by
  obtain ⟨-, hmaps, -, hdiff⟩ := s8w_wD_facts_proof hκ hk1 hk
  have hgu : mob g u ∈ unitDisc := (s8w_mob_conformal hg).2.2 ▸ mem_image_of_mem _ hu
  have hev : (wD κ ∘ mob g) =ᶠ[𝓝 u] (mob g' ∘ wD κ) := by
    filter_upwards [isOpen_ball.mem_nhds hu] with x hx
    exact hrel x hx
  have hgd : DifferentiableAt ℂ (mob g) u :=
    (wp_mob_hasDerivAt g (fdD_denom_ne hg (mem_ball_zero_iff.mp hu))).differentiableAt
  have hg'd : DifferentiableAt ℂ (mob g') (wD κ u) :=
    (wp_mob_hasDerivAt g' (fdD_denom_ne hg' (mem_ball_zero_iff.mp (hmaps hu)))).differentiableAt
  have h1 := (s8w_dz_comp_right (hdiff _ hgu).1 hgd).1
  have h2 := (ra_dz_comp_holo hg'd (hdiff u hu).1).1
  rw [← h1, ← h2]
  exact (ra_dz_congr hev).1

/-- `R(f, κ)` at `w_κ(u)`, its bound and its continuity on `𝔻`. -/
theorem s8w_R_facts {κ : ℂ → ℂ} (hκ : IsHarmonicD κ) {k : ℝ} (hk1 : k < 1)
    (hk : ∀ z ∈ unitDisc, ‖κ z‖ ≤ k) {f : ℂ → ℂ} (hf : ContinuousOn f unitDisc) {C : ℝ}
    (hC : ∀ z ∈ unitDisc, ‖f z‖ ≤ C) :
    (∀ u ∈ unitDisc, RnmD f κ (wD κ u) =
      f u / (1 - ‖κ u‖ ^ 2) * (dz (wD κ) u / conj (dz (wD κ) u))) ∧
    (∀ z ∈ unitDisc, ‖RnmD f κ z‖ ≤ C / (1 - k ^ 2)) ∧ ContinuousOn (RnmD f κ) unitDisc := by
  obtain ⟨⟨e, he⟩, hmaps, hD, hdiff⟩ := s8w_wD_facts_proof hκ hk1 hk
  have hinj : Function.Injective (wD κ) := by rw [← he]; exact e.injective
  have hk0 : 0 ≤ k := (norm_nonneg _).trans (hk 0 (by simp [unitDisc]))
  have hk2 : 0 < 1 - k ^ 2 := by nlinarith
  have hval : ∀ u ∈ unitDisc, RnmD f κ (wD κ u) =
      f u / (1 - ‖κ u‖ ^ 2) * (dz (wD κ) u / conj (dz (wD κ) u)) := by
    intro u _
    unfold RnmD
    rw [Function.leftInverse_invFun hinj u]
  have hinvD : ∀ z ∈ unitDisc, e.symm z ∈ unitDisc ∧ wD κ (e.symm z) = z := by
    intro z hz
    rw [← hD] at hz
    obtain ⟨u, hu, rfl⟩ := hz
    have : e.symm (wD κ u) = u := by rw [← he, e.symm_apply_apply]
    rw [this]
    exact ⟨hu, rfl⟩
  have hden : ∀ u ∈ unitDisc, (1 : ℂ) - (‖κ u‖ : ℂ) ^ 2 ≠ 0 := by
    intro u hu
    have : (1 : ℝ) - ‖κ u‖ ^ 2 ≠ 0 := by nlinarith [hk u hu, norm_nonneg (κ u)]
    exact_mod_cast this
  refine ⟨hval, fun z hz => ?_, ?_⟩
  · obtain ⟨hu, hwu⟩ := hinvD z hz
    rw [← hwu, hval _ hu]
    have hd := (hdiff _ hu).2.1
    rw [norm_mul, norm_div, norm_div, Complex.norm_conj, div_self (norm_ne_zero_iff.mpr hd), mul_one]
    have h1 : ‖(1 : ℂ) - (‖κ (e.symm z)‖ : ℂ) ^ 2‖ = 1 - ‖κ (e.symm z)‖ ^ 2 := by
      rw [show (1 : ℂ) - (‖κ (e.symm z)‖ : ℂ) ^ 2 = ((1 - ‖κ (e.symm z)‖ ^ 2 : ℝ) : ℂ) by push_cast; ring,
        Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by nlinarith [hk _ hu, norm_nonneg (κ (e.symm z))])]
    rw [h1]
    have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC _ hu)
    have hle : 1 - k ^ 2 ≤ 1 - ‖κ (e.symm z)‖ ^ 2 := by nlinarith [hk _ hu, norm_nonneg (κ (e.symm z))]
    exact div_le_div₀ hC0 (hC _ hu) hk2 hle
  · have hcont : ContinuousOn (fun u => f u / (1 - (‖κ u‖ : ℂ) ^ 2) * (dz (wD κ) u / conj (dz (wD κ) u)))
        unitDisc := by
      have hdz := s8w_dz_continuousOn hκ hk1 hk
      have hκc := harmonicD_continuousOn hκ
      refine (hf.div (continuousOn_const.sub ((Complex.continuous_ofReal.comp_continuousOn
        hκc.norm).pow 2)) hden).mul (hdz.div (Complex.continuous_conj.comp_continuousOn hdz) ?_)
      intro u hu
      exact (map_ne_zero _).mpr (hdiff u hu).2.1
    have hc2 : ContinuousOn (fun z => (fun u => f u / (1 - (‖κ u‖ : ℂ) ^ 2) *
        (dz (wD κ) u / conj (dz (wD κ) u))) (e.symm z)) unitDisc :=
      hcont.comp e.symm.continuous.continuousOn fun z hz => (hinvD z hz).1
    refine hc2.congr fun z hz => ?_
    obtain ⟨hu, hwu⟩ := hinvD z hz
    show RnmD f κ z = f (e.symm z) / (1 - (‖κ (e.symm z)‖ : ℂ) ^ 2) *
      (dz (wD κ) (e.symm z) / conj (dz (wD κ) (e.symm z)))
    conv_lhs => rw [← hwu]
    rw [hval _ hu]

/-- Hyperbolic area is preserved by an `SU(1,1)` Möbius map away from its pole. -/
theorem s8w_rho_mob {g : SL2C} (hg : IsSU11 g) {w : ℂ} (hD : g 1 0 * w + g 1 1 ≠ 0) :
    rho (mob g w) * ‖deriv (mob g) w‖ ^ 2 = rho w := by
  have hn : ‖g 1 0 * w + g 1 1‖ ≠ 0 := norm_ne_zero_iff.mpr hD
  rw [(wp_mob_hasDerivAt g hD).deriv, norm_div, norm_one, norm_pow]
  unfold rho
  rw [su11_one_sub_norm_mob g hg w hD]
  field_simp

/-- The derivative of an `SU(1,1)` Möbius map does not vanish on `𝔻`. -/
theorem s8w_mob_deriv_ne {g : SL2C} (hg : IsSU11 g) {u : ℂ} (hu : u ∈ unitDisc) : deriv (mob g) u ≠ 0 := by
  have hDu := fdD_denom_ne hg (mem_ball_zero_iff.mp hu)
  rw [(wp_mob_hasDerivAt g hDu).deriv]
  exact one_div_ne_zero (pow_ne_zero _ hDu)

/-- `R(f, κ)` is invariant under `γ_κ` when `f` and `κ` are invariant under `γ`. -/
theorem s8w_R_inv_elem {κ : ℂ → ℂ} (hκ : IsHarmonicD κ) {k : ℝ} (hk1 : k < 1)
    (hk : ∀ z ∈ unitDisc, ‖κ z‖ ≤ k) {g g' : SL2C} (hg : IsSU11 g) (hg' : IsSU11 g')
    (hrel : ∀ u ∈ unitDisc, wD κ (mob g u) = mob g' (wD κ u))
    (hκg : ∀ z ∈ unitDisc, κ (mob g z) * (conj (deriv (mob g) z) / deriv (mob g) z) = κ z) {f : ℂ → ℂ}
    (hfg : ∀ z ∈ unitDisc, f (mob g z) * (conj (deriv (mob g) z) / deriv (mob g) z) = f z) {z : ℂ}
    (hz : z ∈ unitDisc) :
    RnmD f κ (mob g' z) * (conj (deriv (mob g') z) / deriv (mob g') z) = RnmD f κ z := by
  obtain ⟨⟨e, he⟩, hmaps, hD, hdiff⟩ := s8w_wD_facts_proof hκ hk1 hk
  have hinj : Function.Injective (wD κ) := by rw [← he]; exact e.injective
  have hval : ∀ u, RnmD f κ (wD κ u) = f u / (1 - ‖κ u‖ ^ 2) * (dz (wD κ) u / conj (dz (wD κ) u)) := by
    intro u
    unfold RnmD
    rw [Function.leftInverse_invFun hinj u]
  rw [← hD] at hz
  obtain ⟨u, hu, rfl⟩ := hz
  have hgu : mob g u ∈ unitDisc := (s8w_mob_conformal hg).2.2 ▸ mem_image_of_mem _ hu
  have hchain := s8w_dz_equivariant hκ hk1 hk hg hg' hrel hu
  have ha := s8w_mob_deriv_ne hg hu
  have hb := s8w_mob_deriv_ne hg' (hmaps hu)
  have hd1 := (hdiff _ hgu).2.1
  have hκn : ‖κ (mob g u)‖ = ‖κ u‖ := by
    have h := congrArg norm (hκg u hu)
    rw [norm_mul, norm_div, Complex.norm_conj, div_self (norm_ne_zero_iff.mpr ha), mul_one] at h
    exact h
  have hK : (1 : ℂ) - (‖κ u‖ : ℂ) ^ 2 ≠ 0 := by
    have : (1 : ℝ) - ‖κ u‖ ^ 2 ≠ 0 := by nlinarith [hk u hu, norm_nonneg (κ u)]
    exact_mod_cast this
  have hdd : dz (wD κ) u = dz (wD κ) (mob g u) * deriv (mob g) u / deriv (mob g') (wD κ u) := by
    rw [hchain]
    field_simp
  rw [← hrel u hu, hval, hval, hκn, ← hfg u hu, hdd]
  simp only [map_div₀, map_mul]
  have hcd1 : conj (dz (wD κ) (mob g u)) ≠ 0 := (map_ne_zero _).mpr hd1
  have hca : conj (deriv (mob g) u) ≠ 0 := (map_ne_zero _).mpr ha
  have hcb : conj (deriv (mob g') (wD κ u)) ≠ 0 := (map_ne_zero _).mpr hb
  generalize f (mob g u) = F
  generalize (1 : ℂ) - (‖κ u‖ : ℂ) ^ 2 = K at hK ⊢
  generalize conj (dz (wD κ) (mob g u)) = cD at hcd1 ⊢
  generalize conj (deriv (mob g) u) = cA at hca ⊢
  generalize conj (deriv (mob g') (wD κ u)) = cB at hcb ⊢
  generalize dz (wD κ) (mob g u) = D at hd1 ⊢
  generalize deriv (mob g) u = A at ha ⊢
  generalize deriv (mob g') (wD κ u) = B at hb ⊢
  field_simp

/-- `ρ > 0` on `𝔻`. -/
theorem s8w_rho_pos {v : ℂ} (hv : v ∈ unitDisc) : 0 < rho v := by
  have hs : 0 < 1 - ‖v‖ ^ 2 := by nlinarith [norm_nonneg v, mem_ball_zero_iff.mp hv]
  unfold rho
  positivity

/-- Bound and measurability of the pull-back `w_κ^*(P R(f, κ))` for bounded continuous `f`. -/
theorem s8w_lambda_bm {κ : ℂ → ℂ} (hκ : IsHarmonicD κ) {k : ℝ} (hk1 : k < 1)
    (hk : ∀ z ∈ unitDisc, ‖κ z‖ ≤ k) {C : ℝ}
    (hC : ∀ u ∈ unitDisc, rho (wD κ u) * ‖dz (wD κ) u‖ ^ 2 ≤ C * rho u) {f : ℂ → ℂ}
    (hf : ContinuousOn f unitDisc) {Cf : ℝ} (hCf : ∀ z ∈ unitDisc, ‖f z‖ ≤ Cf) :
    (∀ v ∈ unitDisc, ‖harmonicProjD (RnmD f κ) (wD κ v) * conj (dz (wD κ) v) ^ 2 * rho (wD κ v) / rho v‖ ≤
        3 * (Cf / (1 - k ^ 2)) * C) ∧
      AEStronglyMeasurable (fun v => harmonicProjD (RnmD f κ) (wD κ v) * conj (dz (wD κ) v) ^ 2 * rho (wD κ v) /
        rho v) (volume.restrict unitDisc) := by
  obtain ⟨⟨e, he⟩, hmaps, -, -⟩ := s8w_wD_facts_proof hκ hk1 hk
  have hwc : Continuous (wD κ) := he ▸ e.continuous
  have hRf := s8w_R_facts hκ hk1 hk hf hCf
  have hRm : AEStronglyMeasurable (RnmD f κ) (volume.restrict unitDisc) :=
    hRf.2.2.aestronglyMeasurable measurableSet_ball
  have hΛ := s8w_proj_harmonic_proof hRm ⟨_, hRf.2.1⟩
  have hΛb : ∀ z ∈ unitDisc, ‖harmonicProjD (RnmD f κ) z‖ ≤ 3 * (Cf / (1 - k ^ 2)) := fun z hz =>
    harmonicProjD_norm_le hRf.2.1 (mem_ball_zero_iff.mp hz)
  refine ⟨fun v hv => ?_, ?_⟩
  · have hwv := hmaps hv
    have e1 : ‖harmonicProjD (RnmD f κ) (wD κ v) * conj (dz (wD κ) v) ^ 2 * rho (wD κ v) / rho v‖ =
        ‖harmonicProjD (RnmD f κ) (wD κ v)‖ * (rho (wD κ v) * ‖dz (wD κ) v‖ ^ 2 / rho v) := by
      simp only [norm_div, norm_mul, norm_pow, Complex.norm_conj, Complex.norm_real,
        Real.norm_of_nonneg (s8w_rho_pos hwv).le, Real.norm_of_nonneg (s8w_rho_pos hv).le]
      ring
    rw [e1]
    have hr0 : 0 ≤ rho (wD κ v) * ‖dz (wD κ) v‖ ^ 2 / rho v :=
      div_nonneg (mul_nonneg (s8w_rho_pos hwv).le (sq_nonneg _)) (s8w_rho_pos hv).le
    have hr1 : rho (wD κ v) * ‖dz (wD κ) v‖ ^ 2 / rho v ≤ C := (div_le_iff₀ (s8w_rho_pos hv)).mpr (hC v hv)
    exact mul_le_mul (hΛb _ hwv) hr1 hr0 ((norm_nonneg _).trans (hΛb _ hwv))
  · have hΛc : ContinuousOn (fun v => harmonicProjD (RnmD f κ) (wD κ v)) unitDisc :=
      (harmonicD_continuousOn hΛ).comp hwc.continuousOn hmaps
    have hdz := s8w_dz_continuousOn hκ hk1 hk
    have hρm : Measurable fun v : ℂ => (rho v : ℂ) := by
      unfold rho
      fun_prop
    have h1 : AEStronglyMeasurable (fun v => harmonicProjD (RnmD f κ) (wD κ v) * conj (dz (wD κ) v) ^ 2)
        (volume.restrict unitDisc) :=
      (hΛc.mul ((Complex.continuous_conj.comp_continuousOn hdz).pow 2)).aestronglyMeasurable measurableSet_ball
    exact ((h1.aemeasurable.mul (hρm.comp hwc.measurable).aemeasurable).div
      hρm.aemeasurable).aestronglyMeasurable

/-- **A1.** -/
theorem s8w_lambda_facts_proof {Γ : Subgroup SL2C} (hΓ : IsFuchsian Γ) {κ : ℂ → ℂ} (hκ : IsHarmonicD κ)
    (hκΓ : IsGammaInvD Γ κ) {k : ℝ} (hk1 : k < 1) (hk : ∀ z ∈ unitDisc, ‖κ z‖ ≤ k) {C : ℝ}
    (hC : ∀ u ∈ unitDisc, rho (wD κ u) * ‖dz (wD κ) u‖ ^ 2 ≤ C * rho u) {μ : ℂ → ℂ} (hμ : IsHarmonicD μ)
    (hμΓ : IsGammaInvD Γ μ) :
    (∃ B, ∀ v ∈ unitDisc,
        ‖harmonicProjD (RnmD μ κ) (wD κ v) * conj (dz (wD κ) v) ^ 2 * rho (wD κ v) / rho v‖ ≤ B) ∧
      AEStronglyMeasurable (fun v => harmonicProjD (RnmD μ κ) (wD κ v) * conj (dz (wD κ) v) ^ 2 * rho (wD κ v) /
        rho v) (volume.restrict unitDisc) ∧
      IsGammaInvD Γ (fun v => harmonicProjD (RnmD μ κ) (wD κ v) * conj (dz (wD κ) v) ^ 2 * rho (wD κ v) / rho v) := by
  obtain ⟨-, hmaps, -, hdiff⟩ := s8w_wD_facts_proof hκ hk1 hk
  obtain ⟨Cμ, hCμ⟩ := harmonicD_bound hμ
  obtain ⟨hb, hm⟩ := s8w_lambda_bm hκ hk1 hk hC (harmonicD_continuousOn hμ) hCμ
  refine ⟨⟨_, hb⟩, hm, ?_⟩
  · intro g hg v hv
    have hs := hΓ.1 g hg
    obtain ⟨g', hg', hrel⟩ := s8w_equivariant_proof hΓ hκ hκΓ hk1 hk g hg
    have hgv : mob g v ∈ unitDisc := (s8w_mob_conformal hs).2.2 ▸ mem_image_of_mem _ hv
    have hwv := hmaps hv
    have hg'w : mob g' (wD κ v) ∈ unitDisc := (s8w_mob_conformal hg').2.2 ▸ mem_image_of_mem _ hwv
    have hchain := s8w_dz_equivariant hκ hk1 hk hs hg' hrel hv
    have hΛinv := s8w_proj_inv_elem hg'
      (fun z hz => s8w_R_inv_elem hκ hk1 hk hs hg' hrel (hκΓ g hg) (hμΓ g hg) hz) hwv
    have hρa := s8w_rho_mob hs (fdD_denom_ne hs (mem_ball_zero_iff.mp hv))
    have hρb := s8w_rho_mob hg' (fdD_denom_ne hg' (mem_ball_zero_iff.mp hwv))
    have ha := s8w_mob_deriv_ne hs hv
    have hb := s8w_mob_deriv_ne hg' hwv
    have hd1 := (hdiff _ hgv).2.1
    have hd : dz (wD κ) v = dz (wD κ) (mob g v) * deriv (mob g) v / deriv (mob g') (wD κ v) := by
      rw [hchain]
      field_simp
    have hnsq : ∀ x : ℂ, ((‖x‖ : ℂ)) ^ 2 = x * conj x := fun x => by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; ring
    have hp1 : (rho (mob g v) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (s8w_rho_pos hgv).ne'
    have hp2 : (rho (mob g' (wD κ v)) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (s8w_rho_pos hg'w).ne'
    show harmonicProjD (RnmD μ κ) (wD κ (mob g v)) * conj (dz (wD κ) (mob g v)) ^ 2 *
        rho (wD κ (mob g v)) / rho (mob g v) * (conj (deriv (mob g) v) / deriv (mob g) v) =
      harmonicProjD (RnmD μ κ) (wD κ v) * conj (dz (wD κ) v) ^ 2 * rho (wD κ v) / rho v
    rw [hrel v hv, ← hΛinv, ← hρa, ← hρb, hd]
    push_cast
    rw [hnsq, hnsq]
    simp only [map_div₀, map_mul]
    have hcd1 : conj (dz (wD κ) (mob g v)) ≠ 0 := (map_ne_zero _).mpr hd1
    have hca : conj (deriv (mob g) v) ≠ 0 := (map_ne_zero _).mpr ha
    have hcb : conj (deriv (mob g') (wD κ v)) ≠ 0 := (map_ne_zero _).mpr hb
    generalize harmonicProjD (RnmD μ κ) (mob g' (wD κ v)) = L
    generalize (rho (mob g v) : ℂ) = P1 at hp1 ⊢
    generalize (rho (mob g' (wD κ v)) : ℂ) = P2 at hp2 ⊢
    generalize conj (dz (wD κ) (mob g v)) = cD at hcd1 ⊢
    generalize conj (deriv (mob g) v) = cA at hca ⊢
    generalize conj (deriv (mob g') (wD κ v)) = cB at hcb ⊢
    generalize dz (wD κ) (mob g v) = D at hd1 ⊢
    generalize deriv (mob g) v = A at ha ⊢
    generalize deriv (mob g') (wD κ v) = B at hb ⊢
    field_simp

/-- `R(g, κ) ρ ∈ L¹(𝔻)` when `g ρ` is bounded on `𝔻`. -/
theorem s8w_pull_integrable {κ : ℂ → ℂ} (hκ : IsHarmonicD κ) {k : ℝ} (hk1 : k < 1)
    (hk : ∀ z ∈ unitDisc, ‖κ z‖ ≤ k) {C : ℝ}
    (hC : ∀ u ∈ unitDisc, rho (wD κ u) * ‖dz (wD κ) u‖ ^ 2 ≤ C * rho u) {g : ℂ → ℂ}
    (hg : ContinuousOn g unitDisc) {Cg : ℝ} (hCg : ∀ z ∈ unitDisc, ‖g z‖ ≤ Cg) {M : ℝ}
    (hM : ∀ z ∈ unitDisc, ‖g z‖ * rho z ≤ M) : IntegrableOn (fun z => RnmD g κ z * rho z) unitDisc := by
  obtain ⟨⟨e, he⟩, hmaps, hD, hdiff⟩ := s8w_wD_facts_proof hκ hk1 hk
  have hinj : InjOn (wD κ) unitDisc := by rw [← he]; exact e.injective.injOn
  have hd : ∀ u ∈ unitDisc, DifferentiableAt ℝ (wD κ) u ∧ dzbar (wD κ) u = κ u * dz (wD κ) u ∧ ‖κ u‖ ≤ 1 :=
    fun u hu => ⟨(hdiff u hu).1, (hdiff u hu).2.2, (hk u hu).trans hk1.le⟩
  have hRf := s8w_R_facts hκ hk1 hk hg hCg
  have hρm : Measurable fun v : ℂ => (rho v : ℂ) := by
    unfold rho
    fun_prop
  have hm : AEStronglyMeasurable (fun z => RnmD g κ z * rho z) (volume.restrict unitDisc) :=
    ((hRf.2.2.aestronglyMeasurable measurableSet_ball).aemeasurable.mul hρm.aemeasurable).aestronglyMeasurable
  have h0 : (0 : ℂ) ∈ unitDisc := by simp [unitDisc]
  have hC0 : 0 ≤ C := by
    have h := (mul_nonneg (s8w_rho_pos (hmaps h0)).le (sq_nonneg ‖dz (wD κ) 0‖)).trans (hC 0 h0)
    by_contra hneg
    push_neg at hneg
    linarith [mul_neg_of_neg_of_pos hneg (s8w_rho_pos h0)]
  refine ⟨hm, ?_⟩
  show ∫⁻ z in unitDisc, ‖RnmD g κ z * rho z‖ₑ < ⊤
  conv_lhs => rw [← hD]
  rw [s8w_lchange_proof hinj hd (show MeasurableSet unitDisc from measurableSet_ball) subset_rfl]
  refine lt_of_le_of_lt (setLIntegral_mono (measurable_const (a := ENNReal.ofReal (C * M))) fun u hu => ?_) ?_
  · beta_reduce
    have hK : 0 < 1 - ‖κ u‖ ^ 2 := by nlinarith [hk u hu, norm_nonneg (κ u)]
    have hJ : 0 ≤ ‖dz (wD κ) u‖ ^ 2 * (1 - ‖κ u‖ ^ 2) := mul_nonneg (sq_nonneg _) hK.le
    rw [← ofReal_norm_eq_enorm, ← ENNReal.ofReal_mul hJ]
    apply ENNReal.ofReal_le_ofReal
    have h1 : ‖(1 : ℂ) - (‖κ u‖ : ℂ) ^ 2‖ = 1 - ‖κ u‖ ^ 2 := by
      rw [show (1 : ℂ) - (‖κ u‖ : ℂ) ^ 2 = ((1 - ‖κ u‖ ^ 2 : ℝ) : ℂ) by push_cast; ring,
        Complex.norm_real, Real.norm_eq_abs, abs_of_pos hK]
    rw [hRf.1 u hu, norm_mul, norm_mul, norm_div, norm_div, Complex.norm_conj,
      div_self (norm_ne_zero_iff.mpr (hdiff u hu).2.1), mul_one, Complex.norm_real,
      Real.norm_of_nonneg (s8w_rho_pos (hmaps hu)).le, h1]
    calc ‖dz (wD κ) u‖ ^ 2 * (1 - ‖κ u‖ ^ 2) * (‖g u‖ / (1 - ‖κ u‖ ^ 2) * rho (wD κ u))
        = ‖g u‖ * (rho (wD κ u) * ‖dz (wD κ) u‖ ^ 2) := by field_simp
      _ ≤ ‖g u‖ * (C * rho u) := mul_le_mul_of_nonneg_left (hC u hu) (norm_nonneg _)
      _ = C * (‖g u‖ * rho u) := by ring
      _ ≤ C * M := mul_le_mul_of_nonneg_left (hM u hu) hC0
  · rw [setLIntegral_const]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top measure_ball_lt_top

/-- The pointwise identity behind the change of variables `z = w_κ(u)` (TT:3304–3316). -/
theorem s8w_pull_pt {κ : ℂ → ℂ} (hκ : IsHarmonicD κ) {k : ℝ} (hk1 : k < 1)
    (hk : ∀ z ∈ unitDisc, ‖κ z‖ ≤ k) (A g : ℂ → ℂ) {u : ℂ} (hu : u ∈ unitDisc) :
    (‖dz (wD κ) u‖ ^ 2 * (1 - ‖κ u‖ ^ 2)) • (A (wD κ u) * conj (RnmD g κ (wD κ u)) * rho (wD κ u)) =
      A (wD κ u) * conj (dz (wD κ) u) ^ 2 * rho (wD κ u) / rho u * conj (g u) * rho u := by
  obtain ⟨⟨e, he⟩, -, -, hdiff⟩ := s8w_wD_facts_proof hκ hk1 hk
  have hinj : Function.Injective (wD κ) := by rw [← he]; exact e.injective
  have hval : RnmD g κ (wD κ u) = g u / (1 - ‖κ u‖ ^ 2) * (dz (wD κ) u / conj (dz (wD κ) u)) := by
    unfold RnmD
    rw [Function.leftInverse_invFun hinj u]
  have hnsq : ∀ x : ℂ, ((‖x‖ : ℂ)) ^ 2 = x * conj x := fun x => by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; ring
  have hρu : (rho u : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (s8w_rho_pos hu).ne'
  have hdn := (hdiff u hu).2.1
  have hcd : conj (dz (wD κ) u) ≠ 0 := (map_ne_zero _).mpr hdn
  have hK : (1 : ℂ) - (‖κ u‖ : ℂ) ^ 2 ≠ 0 := by
    have : (1 : ℝ) - ‖κ u‖ ^ 2 ≠ 0 := by nlinarith [hk u hu, norm_nonneg (κ u)]
    exact_mod_cast this
  rw [hval, Complex.real_smul]
  simp only [map_mul, map_div₀, map_sub, map_one, map_pow, Complex.conj_ofReal, Complex.conj_conj]
  push_cast
  rw [hnsq (dz (wD κ) u)]
  generalize A (wD κ u) = L
  generalize conj (g u) = G
  generalize (rho (wD κ u) : ℂ) = P1
  generalize (rho u : ℂ) = P2 at hρu ⊢
  generalize (1 : ℂ) - (‖κ u‖ : ℂ) ^ 2 = K at hK ⊢
  generalize conj (dz (wD κ) u) = cD at hcd ⊢
  generalize dz (wD κ) u = D at hdn ⊢
  field_simp
  try ring


/-- The change of variables of TT:3304–3316: `(P R(f, κ), P R(g, κ)) = (w_κ^*(P R(f, κ)), g)`. -/
theorem s8w_pull_inner {κ : ℂ → ℂ} (hκ : IsHarmonicD κ) {k : ℝ} (hk1 : k < 1)
    (hk : ∀ z ∈ unitDisc, ‖κ z‖ ≤ k) {C : ℝ}
    (hC : ∀ u ∈ unitDisc, rho (wD κ u) * ‖dz (wD κ) u‖ ^ 2 ≤ C * rho u) {f g : ℂ → ℂ}
    (hf : ContinuousOn f unitDisc) {Cf : ℝ} (hCf : ∀ z ∈ unitDisc, ‖f z‖ ≤ Cf)
    (hg : ContinuousOn g unitDisc) {Cg : ℝ} (hCg : ∀ z ∈ unitDisc, ‖g z‖ ≤ Cg) {M : ℝ}
    (hM : ∀ z ∈ unitDisc, ‖g z‖ * rho z ≤ M) :
    l2InnerD (harmonicProjD (RnmD f κ)) (harmonicProjD (RnmD g κ)) =
      l2InnerD (fun v => harmonicProjD (RnmD f κ) (wD κ v) * conj (dz (wD κ) v) ^ 2 * rho (wD κ v) / rho v) g := by
  obtain ⟨⟨e, he⟩, hmaps, hD, hdiff⟩ := s8w_wD_facts_proof hκ hk1 hk
  have hinj : InjOn (wD κ) unitDisc := by rw [← he]; exact e.injective.injOn
  have hd : ∀ u ∈ unitDisc, DifferentiableAt ℝ (wD κ) u ∧ dzbar (wD κ) u = κ u * dz (wD κ) u ∧ ‖κ u‖ ≤ 1 :=
    fun u hu => ⟨(hdiff u hu).1, (hdiff u hu).2.2, (hk u hu).trans hk1.le⟩
  have hDm : MeasurableSet unitDisc := measurableSet_ball
  have hRf := s8w_R_facts hκ hk1 hk hf hCf
  have hRg := s8w_R_facts hκ hk1 hk hg hCg
  have hA := s8w_proj_harmonic_proof (hRf.2.2.aestronglyMeasurable hDm) ⟨_, hRf.2.1⟩
  have hAm : AEStronglyMeasurable (harmonicProjD (RnmD f κ)) (volume.restrict unitDisc) :=
    (harmonicD_continuousOn hA).aestronglyMeasurable hDm
  rw [s8w_proj_symm_proof hAm (harmonicD_bound hA) (hRg.2.2.aestronglyMeasurable hDm)
    (s8w_pull_integrable hκ hk1 hk hC hg hCg hM)]
  unfold l2InnerD
  have h1 : ∫ z in unitDisc, harmonicProjD (harmonicProjD (RnmD f κ)) z * conj (RnmD g κ z) * rho z =
      ∫ z in unitDisc, harmonicProjD (RnmD f κ) z * conj (RnmD g κ z) * rho z :=
    setIntegral_congr_fun hDm fun z hz => by rw [harmonicProjD_self hA hz]
  rw [h1]
  conv_lhs => rw [← hD]
  rw [s8w_change_proof hinj hd hDm subset_rfl]
  exact setIntegral_congr_fun hDm fun u hu => s8w_pull_pt hκ hk1 hk _ g hu

/-- `P R(P μ_s, κ) → P R(μ, κ)` pointwise on `𝔻` as `s → 1⁻`. -/
theorem s8w_projR_tendsto {κ : ℂ → ℂ} (hκ : IsHarmonicD κ) {k : ℝ} (hk1 : k < 1)
    (hk : ∀ z ∈ unitDisc, ‖κ z‖ ≤ k) {μ : ℂ → ℂ} (hμ : IsHarmonicD μ) {Cμ : ℝ}
    (hCμ : ∀ z ∈ unitDisc, ‖μ z‖ ≤ Cμ) {z : ℂ} (hz : z ∈ unitDisc) :
    Tendsto (fun s : ℝ => harmonicProjD (RnmD (harmonicProjD (truncR s μ)) κ) z) (𝓝[<] 1)
      (𝓝 (harmonicProjD (RnmD μ κ) z)) := by
  obtain ⟨⟨e, he⟩, -, hD, -⟩ := s8w_wD_facts_proof hκ hk1 hk
  have hinj : Function.Injective (wD κ) := by rw [← he]; exact e.injective
  have hDm : MeasurableSet unitDisc := measurableSet_ball
  have hR : ∀ s ∈ Ioo (0 : ℝ) 1, (∀ ζ ∈ unitDisc, ‖RnmD (harmonicProjD (truncR s μ)) κ ζ‖ ≤ 3 * Cμ / (1 - k ^ 2)) ∧
      ContinuousOn (RnmD (harmonicProjD (truncR s μ)) κ) unitDisc := fun s hs =>
    (s8w_R_facts hκ hk1 hk (harmonicProjD_trunc_continuousOn hμ hs.1 hs.2)
      (fun ζ hζ => harmonicProjD_norm_le (truncR_norm_le s hCμ) (mem_ball_zero_iff.mp hζ))).2
  show Tendsto (fun s : ℝ => (3 * (1 - ‖z‖ ^ 2) ^ 2 / π *
      ∫ ζ in unitDisc, RnmD (harmonicProjD (truncR s μ)) κ ζ / (1 - ζ * conj z) ^ 4 : ℂ)) (𝓝[<] 1)
    (𝓝 (3 * (1 - ‖z‖ ^ 2) ^ 2 / π * ∫ ζ in unitDisc, RnmD μ κ ζ / (1 - ζ * conj z) ^ 4 : ℂ))
  refine Tendsto.const_mul _ (tendsto_integral_filter_of_dominated_convergence
    (fun ζ => 3 * Cμ / (1 - k ^ 2) * ‖(1 - ζ * conj z) ^ 4‖⁻¹) ?_ ?_ ?_ ?_)
  · filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with s hs
    exact (((hR s hs).2.aestronglyMeasurable hDm).aemeasurable.div (by fun_prop : Measurable fun ζ : ℂ =>
      (1 - ζ * conj z) ^ 4).aemeasurable).aestronglyMeasurable
  · filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with s hs
    refine (ae_restrict_iff' hDm).mpr (Eventually.of_forall fun ζ hζ => ?_)
    rw [norm_div, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right ((hR s hs).1 ζ hζ) (inv_nonneg.mpr (norm_nonneg _))
  · exact (proj_kernel_integrableOn (mem_ball_zero_iff.mp hz)).const_mul _
  · refine (ae_restrict_iff' hDm).mpr (Eventually.of_forall fun ζ hζ => ?_)
    rw [← hD] at hζ
    obtain ⟨u, hu, rfl⟩ := hζ
    refine Tendsto.div_const ?_ _
    show Tendsto (fun s : ℝ => harmonicProjD (truncR s μ) (Function.invFun (wD κ) (wD κ u)) /
        (1 - ‖κ (Function.invFun (wD κ) (wD κ u))‖ ^ 2) * (dz (wD κ) (Function.invFun (wD κ) (wD κ u)) /
          conj (dz (wD κ) (Function.invFun (wD κ) (wD κ u))))) (𝓝[<] 1)
      (𝓝 (μ (Function.invFun (wD κ) (wD κ u)) / (1 - ‖κ (Function.invFun (wD κ) (wD κ u))‖ ^ 2) *
        (dz (wD κ) (Function.invFun (wD κ) (wD κ u)) / conj (dz (wD κ) (Function.invFun (wD κ) (wD κ u))))))
    rw [Function.leftInverse_invFun hinj u]
    exact ((harmonicProjD_trunc_tendsto hμ hu).div_const _).mul_const _

/-- **A2.** -/
theorem s8w_inner_limit_proof {κ : ℂ → ℂ} (hκ : IsHarmonicD κ) {k : ℝ} (hk1 : k < 1)
    (hk : ∀ z ∈ unitDisc, ‖κ z‖ ≤ k) {C : ℝ}
    (hC : ∀ u ∈ unitDisc, rho (wD κ u) * ‖dz (wD κ) u‖ ^ 2 ≤ C * rho u) {μ ν : ℂ → ℂ} (hμ : IsHarmonicD μ)
    (hν : IsHarmonicD ν) {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    Tendsto (fun s : ℝ => l2InnerD (harmonicProjD (RnmD (harmonicProjD (truncR s μ)) κ))
        (harmonicProjD (RnmD (harmonicProjD (truncR r ν)) κ))) (𝓝[<] 1)
      (𝓝 (l2InnerD (truncR r (harmonicProjD (fun v => harmonicProjD (RnmD μ κ) (wD κ v) *
        conj (dz (wD κ) v) ^ 2 * rho (wD κ v) / rho v))) (truncR r ν))) := by
  obtain ⟨-, hmaps, -, -⟩ := s8w_wD_facts_proof hκ hk1 hk
  have hDm : MeasurableSet unitDisc := measurableSet_ball
  obtain ⟨Cμ, hCμ⟩ := harmonicD_bound hμ
  obtain ⟨Cν, hCν⟩ := harmonicD_bound hν
  have hρm : Measurable fun v : ℂ => (rho v : ℂ) := by
    unfold rho
    fun_prop
  have hgc : ContinuousOn (harmonicProjD (truncR r ν)) unitDisc := harmonicProjD_trunc_continuousOn hν hr0 hr1
  have hgb : ∀ z ∈ unitDisc, ‖harmonicProjD (truncR r ν) z‖ ≤ 3 * Cν := fun z hz =>
    harmonicProjD_norm_le (truncR_norm_le r hCν) (mem_ball_zero_iff.mp hz)
  have hgM : ∀ z ∈ unitDisc, ‖harmonicProjD (truncR r ν) z‖ * rho z ≤ 3 * Cν / (1 - r) ^ 4 * 4 := by
    intro z hz
    have h := harmonicProjD_trunc_norm_le hr0 hr1 hCν (mem_ball_zero_iff.mp hz)
    have hs : 0 < 1 - ‖z‖ ^ 2 := by nlinarith [norm_nonneg z, mem_ball_zero_iff.mp hz]
    have hρ : (1 - ‖z‖ ^ 2) ^ 2 * rho z = 4 := by unfold rho; field_simp
    calc ‖harmonicProjD (truncR r ν) z‖ * rho z ≤ 3 * Cν / (1 - r) ^ 4 * (1 - ‖z‖ ^ 2) ^ 2 * rho z :=
          mul_le_mul_of_nonneg_right h (s8w_rho_pos hz).le
      _ = 3 * Cν / (1 - r) ^ 4 * 4 := by rw [mul_assoc, hρ]
  have hfs : ∀ s ∈ Ioo (0 : ℝ) 1, ContinuousOn (harmonicProjD (truncR s μ)) unitDisc ∧
      ∀ z ∈ unitDisc, ‖harmonicProjD (truncR s μ) z‖ ≤ 3 * Cμ := fun s hs =>
    ⟨harmonicProjD_trunc_continuousOn hμ hs.1 hs.2, fun z hz =>
      harmonicProjD_norm_le (truncR_norm_le s hCμ) (mem_ball_zero_iff.mp hz)⟩
  have hev : ∀ᶠ s in 𝓝[<] (1 : ℝ),
      l2InnerD (fun v => harmonicProjD (RnmD (harmonicProjD (truncR s μ)) κ) (wD κ v) * conj (dz (wD κ) v) ^ 2 *
          rho (wD κ v) / rho v) (harmonicProjD (truncR r ν)) =
        l2InnerD (harmonicProjD (RnmD (harmonicProjD (truncR s μ)) κ))
          (harmonicProjD (RnmD (harmonicProjD (truncR r ν)) κ)) := by
    filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with s hs
    exact (s8w_pull_inner hκ hk1 hk hC (hfs s hs).1 (hfs s hs).2 hgc hgb hgM).symm
  have hlim : Tendsto (fun s : ℝ => l2InnerD (fun v => harmonicProjD (RnmD (harmonicProjD (truncR s μ)) κ) (wD κ v) *
      conj (dz (wD κ) v) ^ 2 * rho (wD κ v) / rho v) (harmonicProjD (truncR r ν))) (𝓝[<] 1)
      (𝓝 (l2InnerD (fun v => harmonicProjD (RnmD μ κ) (wD κ v) * conj (dz (wD κ) v) ^ 2 * rho (wD κ v) / rho v)
        (harmonicProjD (truncR r ν)))) := by
    unfold l2InnerD
    refine tendsto_integral_filter_of_dominated_convergence
      (fun _ => 3 * (3 * Cμ / (1 - k ^ 2)) * C * (3 * Cν / (1 - r) ^ 4 * 4)) ?_ ?_ ?_ ?_
    · filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with s hs
      exact (((s8w_lambda_bm hκ hk1 hk hC (hfs s hs).1 (hfs s hs).2).2.aemeasurable.mul
        ((Complex.continuous_conj.comp_continuousOn hgc).aestronglyMeasurable hDm).aemeasurable).mul
        hρm.aemeasurable).aestronglyMeasurable
    · filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with s hs
      refine (ae_restrict_iff' hDm).mpr (Eventually.of_forall fun u hu => ?_)
      have hb := (s8w_lambda_bm hκ hk1 hk hC (hfs s hs).1 (hfs s hs).2).1 u hu
      rw [show ∀ X : ℂ, ‖X * conj (harmonicProjD (truncR r ν) u) * (rho u : ℂ)‖ =
          ‖X‖ * (‖harmonicProjD (truncR r ν) u‖ * rho u) from fun X => by
        rw [norm_mul, norm_mul, Complex.norm_conj, Complex.norm_real,
          Real.norm_of_nonneg (s8w_rho_pos hu).le, mul_assoc]]
      exact mul_le_mul hb (hgM u hu) (mul_nonneg (norm_nonneg _) (s8w_rho_pos hu).le)
        ((norm_nonneg _).trans hb)
    · exact integrableOn_const measure_ball_lt_top.ne
    · refine (ae_restrict_iff' hDm).mpr (Eventually.of_forall fun u hu => ?_)
      exact (((((s8w_projR_tendsto hκ hk1 hk hμ hCμ (hmaps hu)).mul_const _).mul_const _).div_const _).mul_const
        _).mul_const _
  have hfin : l2InnerD (fun v => harmonicProjD (RnmD μ κ) (wD κ v) * conj (dz (wD κ) v) ^ 2 * rho (wD κ v) / rho v)
      (harmonicProjD (truncR r ν)) = l2InnerD (truncR r (harmonicProjD (fun v => harmonicProjD (RnmD μ κ) (wD κ v) *
        conj (dz (wD κ) v) ^ 2 * rho (wD κ v) / rho v))) (truncR r ν) := by
    obtain ⟨hLb, hLm⟩ := s8w_lambda_bm hκ hk1 hk hC (harmonicD_continuousOn hμ) hCμ
    have hνr := s8w_proj_harmonic_proof (truncR_aestronglyMeasurable hν hr1).restrict ⟨_, truncR_norm_le r hCν⟩
    have hgi : IntegrableOn (fun z => harmonicProjD (truncR r ν) z * rho z) unitDisc := by
      refine Integrable.mono' (integrableOn_const (C := 3 * Cν / (1 - r) ^ 4 * 4) measure_ball_lt_top.ne)
        ((hgc.aestronglyMeasurable hDm).aemeasurable.mul hρm.aemeasurable).aestronglyMeasurable
        ((ae_restrict_iff' hDm).mpr (Eventually.of_forall fun z hz => ?_))
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (s8w_rho_pos hz).le]
      exact hgM z hz
    have h1 : l2InnerD (fun v => harmonicProjD (RnmD μ κ) (wD κ v) * conj (dz (wD κ) v) ^ 2 * rho (wD κ v) / rho v)
        (harmonicProjD (truncR r ν)) = l2InnerD (fun v => harmonicProjD (RnmD μ κ) (wD κ v) *
          conj (dz (wD κ) v) ^ 2 * rho (wD κ v) / rho v) (harmonicProjD (harmonicProjD (truncR r ν))) := by
      unfold l2InnerD
      exact setIntegral_congr_fun hDm fun z hz => by rw [harmonicProjD_self hνr hz]
    rw [h1, s8w_proj_symm_proof hLm ⟨_, hLb⟩ (hgc.aestronglyMeasurable hDm) hgi]
    exact s8c_inner_proj_trunc (s8w_proj_harmonic_proof hLm ⟨_, hLb⟩) hν hr0 hr1
  rw [← hfin]
  exact hlim.congr' hev

/-- The chosen fundamental domain in `𝔻` is a fundamental domain. -/
theorem s8w_fundD {Γ : Subgroup SL2C} (hΓ : IsFuchsian Γ) : IsFundDomainD Γ (fundDomainOn Γ unitDisc) := by
  have hex : ∃ F, IsFundDomain Γ F := ⟨_, fd_exists_isFundDomain hΓ⟩
  have hFD : IsFundDomain Γ (fundDomain Γ) := by
    unfold fundDomain
    rw [dif_pos hex]
    exact hex.choose_spec
  have hexD : ∃ F, IsFundDomainOn Γ unitDisc F := ⟨_, fdr_isFundDomainD_refl hΓ hFD⟩
  have h : IsFundDomainOn Γ unitDisc (fundDomainOn Γ unitDisc) := by
    unfold fundDomainOn
    rw [dif_pos hexD]
    exact hexD.choose_spec
  exact h

/-- `Γ\𝔻` has finite hyperbolic area for cofinite `Γ`. -/
theorem s8w_area_fin {Γ : Subgroup SL2C} (hΓ : IsCofinite Γ) :
    ∫⁻ z in fundDomainOn Γ unitDisc, ENNReal.ofReal (rho z) < ⊤ := by
  have hex : ∃ F, IsFundDomain Γ F := ⟨_, fd_exists_isFundDomain hΓ.1⟩
  have hFD : IsFundDomain Γ (fundDomain Γ) := by
    unfold fundDomain
    rw [dif_pos hex]
    exact hex.choose_spec
  have hS0 : ∀ z ∈ fundDomain Γ, z ≠ 0 := fun z hz => fdr_ne_zero_of_exterior (hFD.2.1 hz)
  rw [← fdD_lintegral_rho_independent hΓ.1 (fdr_isFundDomainD_refl hΓ.1 hFD) (s8w_fundD hΓ.1),
    fdr_lintegral_rho_refl hFD.1 hS0]
  exact hΓ.2

/-- **A3.** -/
theorem s8w_final_proof {Γ : Subgroup SL2C} (hΓ : IsCofinite Γ) {κ : ℂ → ℂ} (hκ : IsHarmonicD κ)
    (hκΓ : IsGammaInvD Γ κ) {k : ℝ} (hk1 : k < 1) (hk : ∀ z ∈ unitDisc, ‖κ z‖ ≤ k) {C : ℝ}
    (hC : ∀ u ∈ unitDisc, rho (wD κ u) * ‖dz (wD κ) u‖ ^ 2 ≤ C * rho u) {μ ν : ℂ → ℂ} (hμ : IsHarmonicD μ)
    (hν : IsHarmonicD ν) (hμΓ : IsGammaInvD Γ μ) (hνΓ : IsGammaInvD Γ ν) :
    innerGamma Γ (harmonicProjD (fun v => harmonicProjD (RnmD μ κ) (wD κ v) * conj (dz (wD κ) v) ^ 2 *
      rho (wD κ v) / rho v)) ν = gGamma Γ μ ν κ := by
  obtain ⟨⟨e, he⟩, hmaps, -, hdiff⟩ := s8w_wD_facts_proof hκ hk1 hk
  have hinj : InjOn (wD κ) unitDisc := by rw [← he]; exact e.injective.injOn
  have hd : ∀ u ∈ unitDisc, DifferentiableAt ℝ (wD κ) u ∧ dzbar (wD κ) u = κ u * dz (wD κ) u ∧ ‖κ u‖ ≤ 1 :=
    fun u hu => ⟨(hdiff u hu).1, (hdiff u hu).2.2, (hk u hu).trans hk1.le⟩
  have hDm : MeasurableSet unitDisc := measurableSet_ball
  have hF := s8w_fundD hΓ.1
  have hFA := s8w_area_fin hΓ
  obtain ⟨hLb, hLm, hLΓ⟩ := s8w_lambda_facts_proof hΓ.1 hκ hκΓ hk1 hk hC hμ hμΓ
  have h1 := s8w_selfAdj_quot_proof hΓ.1 hF hFA hLm hLb hLΓ hν hνΓ
  have h2 : ∫ z in fundDomainOn Γ unitDisc, (fun v => harmonicProjD (RnmD μ κ) (wD κ v) *
        conj (dz (wD κ) v) ^ 2 * rho (wD κ v) / rho v) z * conj (ν z) * rho z =
      ∫ z in wD κ '' fundDomainOn Γ unitDisc, harmonicProjD (RnmD μ κ) z * conj (RnmD ν κ z) * rho z := by
    rw [s8w_change_proof hinj hd hF.1 hF.2.1]
    exact setIntegral_congr_fun hF.1 fun u hu => (s8w_pull_pt hκ hk1 hk _ ν (hF.2.1 hu)).symm
  obtain ⟨Γ', hΓ', hF', hback, -⟩ := s8w_conj_group_proof hΓ hκ hκΓ hk1 hk
  obtain ⟨Cμ, hCμ⟩ := harmonicD_bound hμ
  obtain ⟨Cν, hCν⟩ := harmonicD_bound hν
  have hRμ := s8w_R_facts hκ hk1 hk (harmonicD_continuousOn hμ) hCμ
  have hRν := s8w_R_facts hκ hk1 hk (harmonicD_continuousOn hν) hCν
  have hΛ := s8w_proj_harmonic_proof (hRμ.2.2.aestronglyMeasurable hDm) ⟨_, hRμ.2.1⟩
  have hRinv : ∀ f : ℂ → ℂ, IsGammaInvD Γ f → IsGammaInvD Γ' (RnmD f κ) := by
    intro f hf g' hg' z hz
    obtain ⟨g, hg, hrel⟩ := hback g' hg'
    exact s8w_R_inv_elem hκ hk1 hk (hΓ.1.1 g hg) (hΓ'.1 g' hg') hrel (hκΓ g hg) (hf g hg) hz
  have hΛΓ : IsGammaInvD Γ' (harmonicProjD (RnmD μ κ)) := fun g' hg' z hz =>
    s8w_proj_inv_elem (hΓ'.1 g' hg') (fun x hx => hRinv μ hμΓ g' hg' x hx) hz
  have hρm : Measurable rho := by
    unfold rho
    fun_prop
  have h0 : (0 : ℂ) ∈ unitDisc := by simp [unitDisc]
  have hC0 : 0 ≤ C := by
    have h := (mul_nonneg (s8w_rho_pos (hmaps h0)).le (sq_nonneg ‖dz (wD κ) 0‖)).trans (hC 0 h0)
    by_contra hneg
    push_neg at hneg
    linarith [mul_neg_of_neg_of_pos hneg (s8w_rho_pos h0)]
  have hA' : ∫⁻ z in wD κ '' fundDomainOn Γ unitDisc, ENNReal.ofReal (rho z) < ⊤ := by
    rw [s8w_lchange_proof hinj hd hF.1 hF.2.1]
    refine lt_of_le_of_lt (setLIntegral_mono (show Measurable fun u : ℂ => ENNReal.ofReal C * ENNReal.ofReal (rho u)
      from measurable_const.mul (ENNReal.measurable_ofReal.comp hρm)) fun u hu => ?_) ?_
    · beta_reduce
      have hu' := hF.2.1 hu
      have hK : 0 ≤ 1 - ‖κ u‖ ^ 2 := by nlinarith [hk u hu', norm_nonneg (κ u)]
      rw [← ENNReal.ofReal_mul (mul_nonneg (sq_nonneg _) hK), ← ENNReal.ofReal_mul hC0]
      apply ENNReal.ofReal_le_ofReal
      have := hC u hu'
      nlinarith [mul_nonneg (mul_nonneg (sq_nonneg ‖dz (wD κ) u‖) (sq_nonneg ‖κ u‖))
        (s8w_rho_pos (hmaps hu')).le]
    · rw [lintegral_const_mul _ (show Measurable fun u : ℂ => ENNReal.ofReal (rho u)
        from ENNReal.measurable_ofReal.comp hρm)]
      exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hFA
  have h3 := s8w_selfAdj_quot_proof hΓ' hF' hA' (hRν.2.2.aestronglyMeasurable hDm) ⟨_, hRν.2.1⟩
    (hRinv ν hνΓ) hΛ hΛΓ
  have h4 := congrArg conj h3
  rw [← integral_conj, ← integral_conj] at h4
  have e4 : ∀ (a b : ℂ) (t : ℝ), conj (a * conj b * (t : ℂ)) = b * conj a * (t : ℂ) := fun a b t => by
    simp only [map_mul, Complex.conj_conj, Complex.conj_ofReal]
    ring
  simp only [e4] at h4
  unfold innerGamma quotIntD gGamma
  exact h1.trans (h2.trans h4.symm)

/-! ## K: the normalized solution `w_κ` -/

/-- **K1.** For harmonic `κ` with `‖κ‖∞ ≤ k < 1`, `w_κ` is a homeomorphism of `ℂ` mapping `𝔻` onto `𝔻`; on `𝔻` it is
real-differentiable with `(w_κ)_z ≠ 0` and `(w_κ)_z̄ = κ (w_κ)_z`. -/
theorem s8w_wD_facts {κ : ℂ → ℂ} (hκ : IsHarmonicD κ) {k : ℝ} (hk1 : k < 1)
    (hk : ∀ z ∈ unitDisc, ‖κ z‖ ≤ k) :
    (∃ e : ℂ ≃ₜ ℂ, ⇑e = wD κ) ∧ MapsTo (wD κ) unitDisc unitDisc ∧ wD κ '' unitDisc = unitDisc ∧
      ∀ u ∈ unitDisc, DifferentiableAt ℝ (wD κ) u ∧ dz (wD κ) u ≠ 0 ∧ dzbar (wD κ) u = κ u * dz (wD κ) u := by
  exact s8w_wD_facts_proof hκ hk1 hk

/-- **K2.** Change of variables for an injective map, real-differentiable on `𝔻` with `w_z̄ = a w_z`, `|a| ≤ 1`:
the Jacobian is `|w_z|²(1 - |a|²)`. -/
theorem s8w_change {w a : ℂ → ℂ} (hinj : InjOn w unitDisc)
    (hd : ∀ u ∈ unitDisc, DifferentiableAt ℝ w u ∧ dzbar w u = a u * dz w u ∧ ‖a u‖ ≤ 1)
    {S : Set ℂ} (hS : MeasurableSet S) (hSD : S ⊆ unitDisc) (f : ℂ → ℂ) :
    ∫ z in w '' S, f z = ∫ u in S, (‖dz w u‖ ^ 2 * (1 - ‖a u‖ ^ 2)) • f (w u) := by
  exact s8w_change_proof hinj hd hS hSD f

/-- **K2'.** The lower-integral form of K2. -/
theorem s8w_lchange {w a : ℂ → ℂ} (hinj : InjOn w unitDisc)
    (hd : ∀ u ∈ unitDisc, DifferentiableAt ℝ w u ∧ dzbar w u = a u * dz w u ∧ ‖a u‖ ≤ 1)
    {S : Set ℂ} (hS : MeasurableSet S) (hSD : S ⊆ unitDisc) (φ : ℂ → ℝ≥0∞) :
    ∫⁻ z in w '' S, φ z = ∫⁻ u in S, ENNReal.ofReal (‖dz w u‖ ^ 2 * (1 - ‖a u‖ ^ 2)) * φ (w u) := by
  exact s8w_lchange_proof hinj hd hS hSD φ

/-- **K3** (TT:3310, `(1/2)ρ ≤ w_κ^*ρ ≤ (3/2)ρ`). There are `δ₀ ∈ (0, 1)` and `C` such that
`ρ(w_κ(u)) |(w_κ)_z(u)|² ≤ C ρ(u)` on `𝔻` for every harmonic `κ` with `‖κ‖∞ < δ₀`. -/
theorem s8w_density :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ < 1 ∧ ∃ C : ℝ, ∀ κ : ℂ → ℂ, IsHarmonicD κ → (∀ z ∈ unitDisc, ‖κ z‖ < δ₀) →
      ∀ u ∈ unitDisc, rho (wD κ u) * ‖dz (wD κ) u‖ ^ 2 ≤ C * rho u := by
  exact s8w_density_proof

/-- **K4.** `Γ`-equivariance: `w_κ ∘ γ = γ_κ ∘ w_κ` on `𝔻` with `γ_κ ∈ SU(1,1)`. -/
theorem s8w_equivariant {Γ : Subgroup SL2C} (hΓ : IsFuchsian Γ) {κ : ℂ → ℂ} (hκ : IsHarmonicD κ)
    (hκΓ : IsGammaInvD Γ κ) {k : ℝ} (hk1 : k < 1) (hk : ∀ z ∈ unitDisc, ‖κ z‖ ≤ k) :
    ∀ g ∈ Γ, ∃ g' : SL2C, IsSU11 g' ∧ ∀ u ∈ unitDisc, wD κ (mob g u) = mob g' (wD κ u) := by
  exact s8w_equivariant_proof hΓ hκ hκΓ hk1 hk

/-- **K5.** The conjugate group `Γ_κ`: Fuchsian, with fundamental domain `w_κ(F)`, and its elements are exactly the
conjugates `w_κ γ w_κ⁻¹` on `𝔻`. -/
theorem s8w_conj_group {Γ : Subgroup SL2C} (hΓ : IsCofinite Γ) {κ : ℂ → ℂ} (hκ : IsHarmonicD κ)
    (hκΓ : IsGammaInvD Γ κ) {k : ℝ} (hk1 : k < 1) (hk : ∀ z ∈ unitDisc, ‖κ z‖ ≤ k) :
    ∃ Γ' : Subgroup SL2C, IsFuchsian Γ' ∧ IsFundDomainD Γ' (wD κ '' fundDomainOn Γ unitDisc) ∧
      (∀ g' ∈ Γ', ∃ g ∈ Γ, ∀ u ∈ unitDisc, wD κ (mob g u) = mob g' (wD κ u)) ∧
      ∀ g ∈ Γ, ∃ g' ∈ Γ', ∀ u ∈ unitDisc, wD κ (mob g u) = mob g' (wD κ u) := by
  exact s8w_conj_group_proof hΓ hκ hκΓ hk1 hk

/-! ## P: the projector -/

/-- **P1.** `P` maps `L¹(𝔻, ρ)` to itself. -/
theorem s8w_proj_integrable {F : ℂ → ℂ} (hF : AEStronglyMeasurable F (volume.restrict unitDisc))
    (hFi : IntegrableOn (fun z => F z * rho z) unitDisc) :
    IntegrableOn (fun z => harmonicProjD F z * rho z) unitDisc := by
  exact s8w_proj_integrable_proof hF hFi

/-- **P2.** Symmetry of `P`: `(G, P F) = (P G, F)` for bounded `G` and `F ∈ L¹(𝔻, ρ)`. -/
theorem s8w_proj_symm {G F : ℂ → ℂ} (hG : AEStronglyMeasurable G (volume.restrict unitDisc))
    (hGb : ∃ C, ∀ z ∈ unitDisc, ‖G z‖ ≤ C) (hF : AEStronglyMeasurable F (volume.restrict unitDisc))
    (hFi : IntegrableOn (fun z => F z * rho z) unitDisc) :
    l2InnerD G (harmonicProjD F) = l2InnerD (harmonicProjD G) F := by
  exact s8w_proj_symm_proof hG hGb hF hFi

/-- **P3.** `P` of a bounded measurable function is in `Ω^{-1,1}(𝔻)`. -/
theorem s8w_proj_harmonic {G : ℂ → ℂ} (hG : AEStronglyMeasurable G (volume.restrict unitDisc))
    (hGb : ∃ C, ∀ z ∈ unitDisc, ‖G z‖ ≤ C) : IsHarmonicD (harmonicProjD G) := by
  exact s8w_proj_harmonic_proof hG hGb

/-- **P4.** `P` commutes with the action of a Fuchsian group on Beltrami differentials. -/
theorem s8w_proj_gammaInv {Γ : Subgroup SL2C} (hΓ : IsFuchsian Γ) {G : ℂ → ℂ}
    (hG : AEStronglyMeasurable G (volume.restrict unitDisc)) (hGb : ∃ C, ∀ z ∈ unitDisc, ‖G z‖ ≤ C)
    (hGΓ : IsGammaInvD Γ G) : IsGammaInvD Γ (harmonicProjD G) := by
  exact s8w_proj_gammaInv_proof hΓ hG hGb hGΓ

/-- **P5.** Self-adjointness over a fundamental domain ("any one variable may range over `Γ\𝔻`", TT:3349): for bounded
`Γ`-invariant `λ` and `ν ∈ Ω^{-1,1}(𝔻, Γ)`, `∬_D P(λ) ν̄ ρ = ∬_D λ ν̄ ρ`. -/
theorem s8w_selfAdj_quot {Γ : Subgroup SL2C} (hΓ : IsFuchsian Γ) {D : Set ℂ} (hD : IsFundDomainD Γ D)
    (hA : ∫⁻ z in D, ENNReal.ofReal (rho z) < ⊤) {l ν : ℂ → ℂ}
    (hl : AEStronglyMeasurable l (volume.restrict unitDisc)) (hlb : ∃ C, ∀ z ∈ unitDisc, ‖l z‖ ≤ C)
    (hlΓ : IsGammaInvD Γ l) (hν : IsHarmonicD ν) (hνΓ : IsGammaInvD Γ ν) :
    ∫ z in D, harmonicProjD l z * conj (ν z) * rho z = ∫ z in D, l z * conj (ν z) * rho z := by
  exact s8w_selfAdj_quot_proof hΓ hD hA hl hlb hlΓ hν hνΓ

/-! ## A: the limits -/

/-- **A1.** The pulled-back differential `λ = w_κ^*(P R(μ, κ))` is bounded, measurable and `Γ`-invariant. -/
theorem s8w_lambda_facts {Γ : Subgroup SL2C} (hΓ : IsFuchsian Γ) {κ : ℂ → ℂ} (hκ : IsHarmonicD κ)
    (hκΓ : IsGammaInvD Γ κ) {k : ℝ} (hk1 : k < 1) (hk : ∀ z ∈ unitDisc, ‖κ z‖ ≤ k) {C : ℝ}
    (hC : ∀ u ∈ unitDisc, rho (wD κ u) * ‖dz (wD κ) u‖ ^ 2 ≤ C * rho u) {μ : ℂ → ℂ} (hμ : IsHarmonicD μ)
    (hμΓ : IsGammaInvD Γ μ) :
    (∃ B, ∀ v ∈ unitDisc,
        ‖harmonicProjD (RnmD μ κ) (wD κ v) * conj (dz (wD κ) v) ^ 2 * rho (wD κ v) / rho v‖ ≤ B) ∧
      AEStronglyMeasurable (fun v => harmonicProjD (RnmD μ κ) (wD κ v) * conj (dz (wD κ) v) ^ 2 * rho (wD κ v) /
        rho v) (volume.restrict unitDisc) ∧
      IsGammaInvD Γ (fun v => harmonicProjD (RnmD μ κ) (wD κ v) * conj (dz (wD κ) v) ^ 2 * rho (wD κ v) / rho v) := by
  exact s8w_lambda_facts_proof hΓ hκ hκΓ hk1 hk hC hμ hμΓ

/-- **A2.** The inner limit (TT:3304–3322): `lim_{s → 1⁻} ∬ P(R(P μ_s, κ)) \overline{P(R(P ν_r, κ))} ρ = ∬ P(λ)_r ν̄_r ρ`. -/
theorem s8w_inner_limit {κ : ℂ → ℂ} (hκ : IsHarmonicD κ) {k : ℝ} (hk1 : k < 1)
    (hk : ∀ z ∈ unitDisc, ‖κ z‖ ≤ k) {C : ℝ}
    (hC : ∀ u ∈ unitDisc, rho (wD κ u) * ‖dz (wD κ) u‖ ^ 2 ≤ C * rho u) {μ ν : ℂ → ℂ} (hμ : IsHarmonicD μ)
    (hν : IsHarmonicD ν) {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    Tendsto (fun s : ℝ => l2InnerD (harmonicProjD (RnmD (harmonicProjD (truncR s μ)) κ))
        (harmonicProjD (RnmD (harmonicProjD (truncR r ν)) κ))) (𝓝[<] 1)
      (𝓝 (l2InnerD (truncR r (harmonicProjD (fun v => harmonicProjD (RnmD μ κ) (wD κ v) *
        conj (dz (wD κ) v) ^ 2 * rho (wD κ v) / rho v))) (truncR r ν))) := by
  exact s8w_inner_limit_proof hκ hk1 hk hC hμ hν hr0 hr1

/-- **A3.** The final identity (TT:3340–3349): `(P λ, ν)_Γ = g_{μν̄}(κ)`. -/
theorem s8w_final {Γ : Subgroup SL2C} (hΓ : IsCofinite Γ) {κ : ℂ → ℂ} (hκ : IsHarmonicD κ)
    (hκΓ : IsGammaInvD Γ κ) {k : ℝ} (hk1 : k < 1) (hk : ∀ z ∈ unitDisc, ‖κ z‖ ≤ k) {C : ℝ}
    (hC : ∀ u ∈ unitDisc, rho (wD κ u) * ‖dz (wD κ) u‖ ^ 2 ≤ C * rho u) {μ ν : ℂ → ℂ} (hμ : IsHarmonicD μ)
    (hν : IsHarmonicD ν) (hμΓ : IsGammaInvD Γ μ) (hνΓ : IsGammaInvD Γ ν) :
    innerGamma Γ (harmonicProjD (fun v => harmonicProjD (RnmD μ κ) (wD κ v) * conj (dz (wD κ) v) ^ 2 *
      rho (wD κ v) / rho v)) ν = gGamma Γ μ ν κ := by
  exact s8w_final_proof hΓ hκ hκΓ hk1 hk hC hμ hν hμΓ hνΓ

/-- **Lemma 8.4**, conditional on the conclusion of `lemma_1_9` for `Γ` (statement of `lemma_8_4` plus `hL`). Once
`lemma_1_9` is proved, `lemma_8_4` closes by `s8w_lemma_8_4 hΓ (fun hm hb ha => lemma_1_9 hΓ hm hb ha) hμ hν hμΓ hνΓ`. -/
theorem s8w_lemma_8_4 {Γ : Subgroup SL2C} (hΓ : IsCofinite Γ)
    (hL : ∀ {h : ℂ → ℂ}, AEStronglyMeasurable h (volume.restrict unitDiscExterior) →
      (∃ C, ∀ᵐ z ∂(volume.restrict unitDiscExterior), ‖h z‖ ≤ C) →
      (∀ g ∈ Γ, ∀ᵐ z ∂(volume.restrict unitDiscExterior), h (mob g z) = h z) →
      Tendsto (fun r : ℝ => ((hypArea Γ).toReal / (∫ z in discExteriorR r, rho z) : ℂ) *
          ∫ z in discExteriorR r, h z * rho z)
        (𝓝[>] 1) (𝓝 (quotientIntegral Γ fun z => h z * rho z)))
    {μ ν : ℂ → ℂ} (hμ : IsHarmonicD μ) (hν : IsHarmonicD ν) (hμΓ : IsGammaInvD Γ μ) (hνΓ : IsGammaInvD Γ ν) :
    ∃ δ > 0, ∀ κ : ℂ → ℂ, IsHarmonicD κ → IsGammaInvD Γ κ → (∀ z ∈ unitDisc, ‖κ z‖ < δ) →
      Tendsto (fun r : ℝ => limUnder (𝓝[<] (1 : ℝ)) fun s : ℝ =>
          (hypAreaD Γ / hypAreaDiscR r : ℂ) * l2InnerD (harmonicProjD (RnmD (harmonicProjD (truncR s μ)) κ))
            (harmonicProjD (RnmD (harmonicProjD (truncR r ν)) κ)))
        (𝓝[<] 1) (𝓝 (gGamma Γ μ ν κ)) := by
  obtain ⟨δ₀, hδ0, hδ1, C, hC⟩ := s8w_density
  refine ⟨δ₀, hδ0, fun κ hκ hκΓ hκδ => ?_⟩
  have hk : ∀ z ∈ unitDisc, ‖κ z‖ ≤ δ₀ := fun z hz => (hκδ z hz).le
  have hCκ := hC κ hκ hκδ
  obtain ⟨hlb, hlm, hlΓ⟩ := s8w_lambda_facts hΓ.1 hκ hκΓ hδ1 hk hCκ hμ hμΓ
  have hP := s8c_petersson_average hΓ hL (s8w_proj_harmonic hlm hlb) hν
    (s8w_proj_gammaInv hΓ.1 hlm hlb hlΓ) hνΓ
  rw [s8w_final hΓ hκ hκΓ hδ1 hk hCκ hμ hν hμΓ hνΓ] at hP
  refine hP.congr' ?_
  filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with r hr
  exact ((s8w_inner_limit hκ hδ1 hk hCκ hμ hν hr.1 hr.2).const_mul _).limUnder_eq.symm

end TakhtajanTeo
