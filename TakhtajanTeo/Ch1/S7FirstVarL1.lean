import TakhtajanTeo.Ch1.S6Eq64
import TakhtajanTeo.Ch1.S7FirstVarTransfer
import TakhtajanTeo.Ch1.S7FirstVarSchur

/-!
# Program G, F1 piece R1: polytorus-uniform `L¹(𝕌 × 𝕌)` bound of the double kernel (下属1)

`s7g_L1`: for the four-parameter family `W_P` (coefficient `p₁a + p₂b` on `𝕌`, its `q`-reflection on `𝕃`,
`‖P‖ ≤ R`, `2Rk < 1`) and harmonic `m₁, m₂` of finite `L²(ρ_𝕌)` norm,
`∬_{𝕌×𝕌} |m₁(z)| |m₂(u)| |W'(u) W'(z̄)/(W u - W z̄)²|² ≤ M` uniformly in `P`. Proof:
* `s7g_r1_W`: `W_P` is `K`-q.c. onto `ℂ`, `C¹` off `ℝ`, and `(1 - (2Rk)²)|∂W|² ≤ J_W` off `ℝ`;
* `s7g_r1_cov`: change of variables `X = W u` (`𝕌 → Ω`), `Y = W(z̄)` (`𝕃 → Ω*`, via `conj`);
* `s7g_schur` (R2) on `Ω*, Ω`, and `s7g_transfer` (R3) for `W` and for `conj ∘ W ∘ conj` (`s7g_r1_lower`).
-/

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal NNReal ComplexConjugate Classical Real
noncomputable section
namespace TakhtajanTeo
open LiZhongQC

/-- A continuous function bounded a.e. on an open set is bounded everywhere on it. -/
theorem s7g_r1_bound_of_ae {a : ℂ → ℂ} {U : Set ℂ} {k : ℝ} (hU : IsOpen U) (ha : ContinuousOn a U)
    (hae : ∀ᵐ z ∂(volume.restrict U), ‖a z‖ ≤ k) : ∀ z ∈ U, ‖a z‖ ≤ k := by
  have heq : (fun z => min ‖a z‖ k) =ᵐ[volume.restrict U] fun z => ‖a z‖ := by
    filter_upwards [hae] with z hz
    exact min_eq_left hz
  have hc2 : ContinuousOn (fun z => ‖a z‖) U := continuous_norm.comp_continuousOn ha
  have hc1 : ContinuousOn (fun z => min ‖a z‖ k) U :=
    continuous_min.comp_continuousOn (hc2.prodMk continuousOn_const)
  intro z hz
  have h := Measure.eqOn_open_of_ae_eq heq hU hc1 hc2 hz
  simp only at h
  rw [← h]
  exact min_le_right _ _

/-- Two coefficients with disjoint supports `𝕌`, `𝕃`, each bounded by `k'`: every `Q.1 m₁ + Q.2 m₂` is
bounded by `max |Q.1| |Q.2| · k'`. -/
theorem s7g_r1_supp {m₁ m₂ : ℂ → ℂ} {k' : ℝ} (hk0 : 0 ≤ k') (hm₁ : IsBeltramiCoeff m₁ univ k')
    (hm₂ : IsBeltramiCoeff m₂ univ k') (hm₂0 : ∀ u : ℂ, 0 < u.im → m₂ u = 0)
    (hm₁0 : ∀ u : ℂ, ¬ 0 < u.im → m₁ u = 0) (Q : ℂ × ℂ) :
    IsBeltramiCoeff (fun u => Q.1 * m₁ u + Q.2 * m₂ u) univ (max ‖Q.1‖ ‖Q.2‖ * k') := by
  refine ⟨(hm₁.1.const_mul Q.1).add (hm₂.1.const_mul Q.2), ?_⟩
  filter_upwards [hm₁.2, hm₂.2] with u h₁ h₂
  by_cases hu : 0 < u.im
  · rw [hm₂0 u hu, mul_zero, add_zero, norm_mul]
    exact mul_le_mul (le_max_left _ _) h₁ (norm_nonneg _) (by positivity)
  · rw [hm₁0 u hu, mul_zero, zero_add, norm_mul]
    exact mul_le_mul (le_max_right _ _) h₂ (norm_nonneg _) (by positivity)

/-- Smoothness of the `(1, 1)` member off `ℝ`. -/
theorem s7g_r1_smooth {m₁ m₂ : ℂ → ℂ} {k' : ℝ} (hk0 : 0 ≤ k') (hk1 : k' < 1)
    (hm₁ : IsBeltramiCoeff m₁ univ k') (hm₂ : IsBeltramiCoeff m₂ univ k')
    (hs₁ : ContDiffOn ℝ (⊤ : ℕ∞) m₁ {u : ℂ | u.im ≠ 0}) (hs₂ : ContDiffOn ℝ (⊤ : ℕ∞) m₂ {u : ℂ | u.im ≠ 0})
    (hm₂0 : ∀ u : ℂ, 0 < u.im → m₂ u = 0) (hm₁0 : ∀ u : ℂ, ¬ 0 < u.im → m₁ u = 0) :
    ContDiffOn ℝ 3 (normalizedSolution fun u => (1 : ℂ) * m₁ u + 1 * m₂ u) {u : ℂ | u.im ≠ 0} := by
  have hΩ : IsOpen {u : ℂ | u.im ≠ 0} := isOpen_ne_fun Complex.continuous_im continuous_const
  have hWo : IsOpen {Q : ℂ × ℂ | max ‖Q.1‖ ‖Q.2‖ * k' < 1} :=
    isOpen_lt (((continuous_norm.comp continuous_fst).max (continuous_norm.comp continuous_snd)).mul
      continuous_const) continuous_const
  have hjoint := wr_local_joint_contDiff hm₁ hm₂ hΩ hs₁ hs₂ hWo
    (fun Q hQ => ⟨_, hQ, s7g_r1_supp hk0 hm₁ hm₂ hm₂0 hm₁0 Q⟩)
  have h11 : ((1 : ℂ), (1 : ℂ)) ∈ {Q : ℂ × ℂ | max ‖Q.1‖ ‖Q.2‖ * k' < 1} := by
    show max ‖(1 : ℂ)‖ ‖(1 : ℂ)‖ * k' < 1
    simpa using hk1
  have hcomp := ContDiffOn.comp
    (g := fun q : (ℂ × ℂ) × ℂ => normalizedSolution (fun u => q.1.1 * m₁ u + q.1.2 * m₂ u) q.2)
    (f := fun y : ℂ => (((1 : ℂ), (1 : ℂ)), y)) hjoint (contDiffOn_const.prodMk contDiffOn_id)
    (fun y hy => ⟨h11, hy⟩)
  have hfun : ((fun q : (ℂ × ℂ) × ℂ => normalizedSolution (fun u => q.1.1 * m₁ u + q.1.2 * m₂ u) q.2) ∘
      fun y : ℂ => (((1 : ℂ), (1 : ℂ)), y)) = normalizedSolution fun u => (1 : ℂ) * m₁ u + 1 * m₂ u := by
    funext y
    rfl
  rw [hfun] at hcomp
  exact hcomp

/-- The kernel bound `(1 - k'²) |∂W|² ≤ J_W` off `ℝ` for the `(1, 1)` member. -/
theorem s7g_r1_kernel {m₁ m₂ : ℂ → ℂ} {k' : ℝ} (hk0 : 0 ≤ k') (hk1 : k' < 1)
    (hm₁ : IsBeltramiCoeff m₁ univ k') (hm₂ : IsBeltramiCoeff m₂ univ k')
    (hs₁ : ContDiffOn ℝ (⊤ : ℕ∞) m₁ {u : ℂ | u.im ≠ 0}) (hs₂ : ContDiffOn ℝ (⊤ : ℕ∞) m₂ {u : ℂ | u.im ≠ 0})
    (hm₂0 : ∀ u : ℂ, 0 < u.im → m₂ u = 0) (hm₁0 : ∀ u : ℂ, ¬ 0 < u.im → m₁ u = 0) {y : ℂ} (hy : y.im ≠ 0) :
    (1 - k' ^ 2) * ‖dz (normalizedSolution fun u => (1 : ℂ) * m₁ u + 1 * m₂ u) y‖ ^ 2 ≤
      jacobian (normalizedSolution fun u => (1 : ℂ) * m₁ u + 1 * m₂ u) y := by
  have hΩ : IsOpen {u : ℂ | u.im ≠ 0} := isOpen_ne_fun Complex.continuous_im continuous_const
  have hc : IsBeltramiCoeff (fun u => (1 : ℂ) * m₁ u + 1 * m₂ u) univ k' := by
    simpa using s7g_r1_supp hk0 hm₁ hm₂ hm₂0 hm₁0 (1, 1)
  set f := normalizedSolution fun u => (1 : ℂ) * m₁ u + 1 * m₂ u with hf
  have hCf : ContDiffOn ℝ 3 f {u : ℂ | u.im ≠ 0} := s7g_r1_smooth hk0 hk1 hm₁ hm₂ hs₁ hs₂ hm₂0 hm₁0
  have hJpos : ∀ x : ℂ, x.im ≠ 0 → 0 < ‖dz f x‖ ^ 2 - ‖dzbar f x‖ ^ 2 := fun x hx =>
    wr_local_jacobian_pos hm₁ hm₂ hΩ hs₁ hs₂ (P := (1, 1)) ⟨k', hk1, hc⟩ hx
  have hdz0 : ∀ x : ℂ, x.im ≠ 0 → dz f x ≠ 0 := by
    intro x hx h0
    have := hJpos x hx
    rw [h0, norm_zero] at this
    nlinarith [norm_nonneg (dzbar f x)]
  have hfd : ContinuousOn (fderiv ℝ f) {u : ℂ | u.im ≠ 0} := hCf.continuousOn_fderiv_of_isOpen hΩ (by norm_num)
  have hdzc : ContinuousOn (dz f) {u : ℂ | u.im ≠ 0} := by
    unfold dz
    exact (((hfd.clm_apply continuousOn_const).sub (continuousOn_const.mul
      (hfd.clm_apply continuousOn_const)))).div_const _
  have hdzbc : ContinuousOn (dzbar f) {u : ℂ | u.im ≠ 0} := by
    unfold dzbar
    exact (((hfd.clm_apply continuousOn_const).add (continuousOn_const.mul
      (hfd.clm_apply continuousOn_const)))).div_const _
  have hcd : ContinuousOn (complexDilatation f) {u : ℂ | u.im ≠ 0} := hdzbc.div hdzc hdz0
  have hcm : ContinuousOn (fun u => (1 : ℂ) * m₁ u + 1 * m₂ u) {u : ℂ | u.im ≠ 0} :=
    ((continuousOn_const.mul hs₁.continuousOn).add (continuousOn_const.mul hs₂.continuousOn))
  have hns := QCV.qcv_ns_spec hk0 hk1 hc
  have hae : complexDilatation f =ᵐ[volume.restrict {u : ℂ | u.im ≠ 0}] fun u => (1 : ℂ) * m₁ u + 1 * m₂ u :=
    ae_restrict_of_ae hns.2.2.2.2
  have heq : complexDilatation f y = (1 : ℂ) * m₁ y + 1 * m₂ y := Measure.eqOn_open_of_ae_eq hae hΩ hcd hcm hy
  have hbel : dzbar f y = ((1 : ℂ) * m₁ y + 1 * m₂ y) * dz f y := by
    rw [← heq]
    exact (div_mul_cancel₀ _ (hdz0 y hy)).symm
  have hcy : ‖(1 : ℂ) * m₁ y + 1 * m₂ y‖ ≤ k' := by
    have hU : IsOpen upperHalf := isOpen_lt continuous_const Complex.continuous_im
    have hL : IsOpen {u : ℂ | u.im < 0} := isOpen_lt Complex.continuous_im continuous_const
    have hcont1 : ContinuousOn m₁ upperHalf := hs₁.continuousOn.mono fun u hu => ne_of_gt hu
    have hcont2 : ContinuousOn m₂ {u : ℂ | u.im < 0} := hs₂.continuousOn.mono fun u hu => ne_of_lt hu
    have hm₁a : ∀ᵐ z, ‖m₁ z‖ ≤ k' := by simpa using hm₁.2
    have hm₂a : ∀ᵐ z, ‖m₂ z‖ ≤ k' := by simpa using hm₂.2
    have hb1 := s7g_r1_bound_of_ae hU hcont1 (ae_restrict_of_ae hm₁a)
    have hb2 := s7g_r1_bound_of_ae hL hcont2 (ae_restrict_of_ae hm₂a)
    rcases lt_or_gt_of_ne hy with hyl | hyu
    · rw [hm₁0 y (by linarith), mul_zero, zero_add, one_mul]
      exact hb2 y hyl
    · rw [hm₂0 y hyu, mul_zero, add_zero, one_mul]
      exact hb1 y hyu
  unfold jacobian
  rw [hbel, norm_mul]
  nlinarith [mul_le_mul hcy hcy (norm_nonneg _) hk0, sq_nonneg ‖dz f y‖,
    norm_nonneg ((1 : ℂ) * m₁ y + 1 * m₂ y)]

/-- The four-parameter family as a `(1, 1)` member: coefficients on `𝕌` and `𝕃`, with bounds and smoothness. -/
theorem s7g_r1_coeffs {a b : ℂ → ℂ} {k : ℝ} (hk : 0 ≤ k) (ha : IsBeltramiCoeff a upperHalf k)
    (hb : IsBeltramiCoeff b upperHalf k) (has : ContDiffOn ℝ (⊤ : ℕ∞) a upperHalf)
    (hbs : ContDiffOn ℝ (⊤ : ℕ∞) b upperHalf) {R : ℝ} {P : (ℂ × ℂ) × (ℂ × ℂ)}
    (hP : P ∈ closedBall (0 : (ℂ × ℂ) × (ℂ × ℂ)) R) :
    ∃ m₁ m₂ : ℂ → ℂ, IsBeltramiCoeff m₁ univ (2 * R * k) ∧ IsBeltramiCoeff m₂ univ (2 * R * k) ∧
      ContDiffOn ℝ (⊤ : ℕ∞) m₁ {u : ℂ | u.im ≠ 0} ∧ ContDiffOn ℝ (⊤ : ℕ∞) m₂ {u : ℂ | u.im ≠ 0} ∧
      (∀ u : ℂ, 0 < u.im → m₂ u = 0) ∧ (∀ u : ℂ, ¬ 0 < u.im → m₁ u = 0) ∧
      (fun u => (if 0 < u.im then P.1.1 * a u + P.1.2 * b u else 0) +
        (if u.im < 0 then P.2.1 * conj (a (conj u)) + P.2.2 * conj (b (conj u)) else 0)) =
        fun u => (1 : ℂ) * m₁ u + 1 * m₂ u := by
  have hP' : ‖P‖ ≤ R := by simpa using hP
  have hp1 : ‖P.1.1‖ ≤ R := (norm_fst_le P.1).trans ((norm_fst_le P).trans hP')
  have hp2 : ‖P.1.2‖ ≤ R := (norm_snd_le P.1).trans ((norm_fst_le P).trans hP')
  have hq1 : ‖P.2.1‖ ≤ R := (norm_fst_le P.2).trans ((norm_snd_le P).trans hP')
  have hq2 : ‖P.2.2‖ ≤ R := (norm_snd_le P.2).trans ((norm_snd_le P).trans hP')
  obtain ⟨hA, hAl, -, -, -⟩ := wr_U_coeffs hk ha has
  obtain ⟨hB, hBl, -, -, -⟩ := wr_U_coeffs hk hb hbs
  obtain ⟨hAs, hAls⟩ := e64_m_smooth has
  obtain ⟨hBs, hBls⟩ := e64_m_smooth hbs
  have hbd : ∀ {p q : ℂ}, ‖p‖ ≤ R → ‖q‖ ≤ R → (|k| + |k|) * ‖(p, q)‖ ≤ 2 * R * k := by
    intro p q hp hq
    rw [abs_of_nonneg hk]
    have : ‖(p, q)‖ ≤ R := by rw [Prod.norm_def]; exact max_le hp hq
    nlinarith
  refine ⟨fun u => P.1.1 * (if 0 < u.im then a u else 0) + P.1.2 * (if 0 < u.im then b u else 0),
    fun u => P.2.1 * (if u.im < 0 then conj (a (conj u)) else 0) + P.2.2 * (if u.im < 0 then conj (b (conj u)) else 0),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have h := wr_coeff_lin hA hB (P.1.1, P.1.2)
    exact ⟨h.1, h.2.mono fun _ hu => hu.trans (hbd hp1 hp2)⟩
  · have h := wr_coeff_lin hAl hBl (P.2.1, P.2.2)
    exact ⟨h.1, h.2.mono fun _ hu => hu.trans (hbd hq1 hq2)⟩
  · exact (contDiffOn_const.mul hAs).add (contDiffOn_const.mul hBs)
  · exact (contDiffOn_const.mul hAls).add (contDiffOn_const.mul hBls)
  · intro u hu
    have h : ¬ u.im < 0 := by linarith
    simp only [h, ↓reduceIte, mul_zero, add_zero]
  · intro u hu
    simp only [hu, ↓reduceIte, mul_zero, add_zero]
  · funext u
    simp only [one_mul]
    split_ifs <;> (try ring) <;> (exfalso; linarith)

/-- Basic properties of `W_P` on the closed polydisc `‖P‖ ≤ R`, `2Rk < 1`: `K`-q.c. onto `ℂ`
(`K = (1 + 2Rk)/(1 - 2Rk)`), `C¹` off `ℝ`, and `(1 - (2Rk)²) |∂W|² ≤ J_W` off `ℝ`. -/
theorem s7g_r1_W {a b : ℂ → ℂ} {k : ℝ} (hk : 0 ≤ k) (ha : IsBeltramiCoeff a upperHalf k)
    (hb : IsBeltramiCoeff b upperHalf k) (has : ContDiffOn ℝ (⊤ : ℕ∞) a upperHalf)
    (hbs : ContDiffOn ℝ (⊤ : ℕ∞) b upperHalf) {R : ℝ} (hR : 0 ≤ R) (hRk : 2 * R * k < 1)
    {W : (ℂ × ℂ) × (ℂ × ℂ) → ℂ → ℂ} (hW : W = fun P => normalizedSolution fun u =>
      (if 0 < u.im then P.1.1 * a u + P.1.2 * b u else 0) +
        (if u.im < 0 then P.2.1 * conj (a (conj u)) + P.2.2 * conj (b (conj u)) else 0))
    {P : (ℂ × ℂ) × (ℂ × ℂ)} (hP : P ∈ closedBall (0 : (ℂ × ℂ) × (ℂ × ℂ)) R) :
    IsKQC (W P) univ ((1 + 2 * R * k) / (1 - 2 * R * k)) ∧ W P '' univ = univ ∧
      ContDiffOn ℝ 1 (W P) {u : ℂ | u.im ≠ 0} ∧
      ∀ y : ℂ, y.im ≠ 0 → (1 - (2 * R * k) ^ 2) * ‖dz (W P) y‖ ^ 2 ≤ jacobian (W P) y := by
  obtain ⟨m₁, m₂, hm₁, hm₂, hs₁, hs₂, hm₂0, hm₁0, heq⟩ := s7g_r1_coeffs hk ha hb has hbs hP
  have hk0 : 0 ≤ 2 * R * k := by positivity
  have hWP : W P = normalizedSolution fun u => (1 : ℂ) * m₁ u + 1 * m₂ u := by
    rw [hW]
    exact congrArg normalizedSolution heq
  have hc : IsBeltramiCoeff (fun u => (1 : ℂ) * m₁ u + 1 * m₂ u) univ (2 * R * k) := by
    simpa using s7g_r1_supp hk0 hm₁ hm₂ hm₂0 hm₁0 (1, 1)
  have hqc := wr_ns_qc hk0 hRk hc le_rfl
  rw [hWP]
  exact ⟨hqc.1, hqc.2.1, (s7g_r1_smooth hk0 hRk hm₁ hm₂ hs₁ hs₂ hm₂0 hm₁0).of_le (by norm_num),
    fun y hy => s7g_r1_kernel hk0 hRk hm₁ hm₂ hs₁ hs₂ hm₂0 hm₁0 hy⟩

/-- `conj` maps `𝕌` onto `𝕃`. -/
theorem s7g_r1_conj_image : (fun z : ℂ => conj z) '' upperHalf = {u : ℂ | u.im < 0} := by
  ext w
  constructor
  · rintro ⟨z, hz, rfl⟩
    have : 0 < z.im := hz
    show (conj z).im < 0
    rw [Complex.conj_im]; linarith
  · intro hw
    refine ⟨conj w, ?_, Complex.conj_conj w⟩
    have : w.im < 0 := hw
    show 0 < (conj w).im
    rw [Complex.conj_im]; linarith

/-- Pointwise kernel bound: `|∂W(u) ∂W(z̄)/(W u - W z̄)²|² ≤ c₀² J(z̄) J(u)/|W u - W z̄|⁴`. -/
theorem s7g_r1_pt {W : ℂ → ℂ} {k' : ℝ} (hk1 : k' < 1) (hk0 : 0 ≤ k')
    (hker : ∀ y : ℂ, y.im ≠ 0 → (1 - k' ^ 2) * ‖dz W y‖ ^ 2 ≤ jacobian W y) {z u : ℂ}
    (hz : z ∈ upperHalf) (hu : u ∈ upperHalf) (hw : W u - W (conj z) ≠ 0) (x₁ x₂ : ℝ≥0∞) :
    x₁ * x₂ * ‖dz W u * dz W (conj z) / (W u - W (conj z)) ^ 2‖ₑ ^ 2 ≤
      ENNReal.ofReal ((1 - k' ^ 2)⁻¹) ^ 2 * ((x₁ * ENNReal.ofReal (jacobian W (conj z))) *
        (ENNReal.ofReal (jacobian W u) * (x₂ / ‖W u - W (conj z)‖ₑ ^ 4))) := by
  have hc : 0 < 1 - k' ^ 2 := by nlinarith
  have hzi : (conj z).im ≠ 0 := by
    have : 0 < z.im := hz
    rw [Complex.conj_im]; linarith
  have hui : u.im ≠ 0 := ne_of_gt hu
  have hb : ∀ y : ℂ, y.im ≠ 0 → ‖dz W y‖ₑ ^ 2 ≤ ENNReal.ofReal ((1 - k' ^ 2)⁻¹) * ENNReal.ofReal (jacobian W y) := by
    intro y hy
    rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _), ← ENNReal.ofReal_mul (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    rw [inv_mul_eq_div, le_div_iff₀ hc, mul_comm]
    exact hker y hy
  have hnorm : ‖dz W u * dz W (conj z) / (W u - W (conj z)) ^ 2‖ₑ ^ 2 =
      ‖dz W u‖ₑ ^ 2 * ‖dz W (conj z)‖ₑ ^ 2 / ‖W u - W (conj z)‖ₑ ^ 4 := by
    have h1 : ‖dz W u * dz W (conj z) / (W u - W (conj z)) ^ 2‖ₑ =
        ‖dz W u‖ₑ * ‖dz W (conj z)‖ₑ / ‖W u - W (conj z)‖ₑ ^ 2 := by
      rw [enorm_eq_nnnorm, enorm_eq_nnnorm, enorm_eq_nnnorm, enorm_eq_nnnorm, nnnorm_div, nnnorm_mul,
        nnnorm_pow, ENNReal.coe_div (pow_ne_zero 2 (nnnorm_ne_zero_iff.2 hw)), ENNReal.coe_mul, ENNReal.coe_pow]
    rw [h1, div_eq_mul_inv, div_eq_mul_inv, mul_pow, mul_pow, ENNReal.inv_pow, ← pow_mul, ENNReal.inv_pow]
  rw [hnorm]
  calc x₁ * x₂ * (‖dz W u‖ₑ ^ 2 * ‖dz W (conj z)‖ₑ ^ 2 / ‖W u - W (conj z)‖ₑ ^ 4)
      ≤ x₁ * x₂ * ((ENNReal.ofReal ((1 - k' ^ 2)⁻¹) * ENNReal.ofReal (jacobian W u)) *
          (ENNReal.ofReal ((1 - k' ^ 2)⁻¹) * ENNReal.ofReal (jacobian W (conj z))) / ‖W u - W (conj z)‖ₑ ^ 4) := by
        gcongr
        · exact hb u hui
        · exact hb _ hzi
    _ = _ := by
        rw [div_eq_mul_inv, div_eq_mul_inv]
        ring

/-- The lower-half norm: through `W̃ = conj ∘ W ∘ conj` and R3. -/
theorem s7g_r1_lower {W : ℂ → ℂ} {K : ℝ} (hK : IsKQC W univ K) (hs : W '' univ = univ)
    (hC : ContDiffOn ℝ 1 W {u : ℂ | u.im ≠ 0}) {C3 : ℝ≥0∞}
    (hC3 : ∀ W : ℂ → ℂ, IsKQC W univ K → W '' univ = univ → ContDiffOn ℝ 1 W upperHalf → ∀ m φ : ℂ → ℂ,
      DifferentiableOn ℂ φ upperHalf → (∀ u ∈ upperHalf, m u = (u - conj u) ^ 2 / 2 * conj (φ u)) →
      (∫⁻ u in upperHalf, ‖m u‖ₑ ^ 2 * ENNReal.ofReal (jacobian W u) /
          ENNReal.ofReal (infDist (W u) (W '' upperHalf)ᶜ) ^ 2) ≤
        C3 * ∫⁻ u in upperHalf, ‖m u‖ₑ ^ 2 * ENNReal.ofReal (rhoU u))
    {m φ : ℂ → ℂ} (hφ : DifferentiableOn ℂ φ upperHalf)
    (hm : ∀ u ∈ upperHalf, m u = (u - conj u) ^ 2 / 2 * conj (φ u)) :
    (∫⁻ w in {u : ℂ | u.im < 0}, ENNReal.ofReal (jacobian W w) *
        (‖m (conj w)‖ₑ ^ 2 / ENNReal.ofReal (infDist (W w) (W '' {u : ℂ | u.im < 0})ᶜ) ^ 2)) ≤
      C3 * ∫⁻ u in upperHalf, ‖m u‖ₑ ^ 2 * ENNReal.ofReal (rhoU u) := by
  set Wt : ℂ → ℂ := fun z => conj (W (conj z)) with hWt
  have hKt : IsKQC Wt univ K := by
    have h := abR_x_isKQC_conj hK
    rwa [preimage_univ] at h
  have hst : Wt '' univ = univ := by
    refine eq_univ_of_forall fun w => ?_
    have hw : conj w ∈ W '' univ := by rw [hs]; exact mem_univ _
    obtain ⟨v, -, hv⟩ := hw
    refine ⟨conj v, mem_univ _, ?_⟩
    show conj (W (conj (conj v))) = w
    rw [Complex.conj_conj, hv, Complex.conj_conj]
  have hΩ : IsOpen {u : ℂ | u.im ≠ 0} := isOpen_ne_fun Complex.continuous_im continuous_const
  have hmaps : MapsTo (fun z : ℂ => conj z) upperHalf {u : ℂ | u.im ≠ 0} := by
    intro z hz
    have : 0 < z.im := hz
    show (conj z).im ≠ 0
    rw [Complex.conj_im]; linarith
  have hCt : ContDiffOn ℝ 1 Wt upperHalf :=
    Complex.conjCLE.contDiff.comp_contDiffOn (hC.comp Complex.conjCLE.contDiff.contDiffOn hmaps)
  have hR3 := hC3 Wt hKt hst hCt m φ hφ hm
  -- the image of `𝕌` under `W̃` and the distance
  have himg : Wt '' upperHalf = (fun x : ℂ => conj x) '' (W '' {u : ℂ | u.im < 0}) := by
    rw [← s7g_r1_conj_image, image_image, image_image]
  have hcompl : (Wt '' upperHalf)ᶜ = (fun x : ℂ => conj x) '' (W '' {u : ℂ | u.im < 0})ᶜ := by
    have hbij : Function.Bijective (fun x : ℂ => conj x) :=
      Function.Involutive.bijective fun x => Complex.conj_conj x
    rw [himg, image_compl_eq hbij]
  have hdist : ∀ z, infDist (Wt z) (Wt '' upperHalf)ᶜ = infDist (W (conj z)) (W '' {u : ℂ | u.im < 0})ᶜ := by
    intro z
    rw [hcompl]
    exact infDist_image Complex.conjLIE.isometry
  have hjac : ∀ z ∈ upperHalf, jacobian Wt z = jacobian W (conj z) := by
    intro z hz
    have hd : DifferentiableAt ℝ W (conj z) :=
      ((hC.differentiableOn (by norm_num)).differentiableAt (hΩ.mem_nhds (hmaps hz)))
    obtain ⟨-, h1, h2⟩ := abR_x_dz_dzbar_conj hd
    unfold jacobian
    rw [hWt, h1, h2, Complex.norm_conj, Complex.norm_conj]
  -- move the lower integral to `𝕌`
  have hemb := Complex.conjLIE.toHomeomorph.measurableEmbedding
  have hL : (∫⁻ w in {u : ℂ | u.im < 0}, ENNReal.ofReal (jacobian W w) *
        (‖m (conj w)‖ₑ ^ 2 / ENNReal.ofReal (infDist (W w) (W '' {u : ℂ | u.im < 0})ᶜ) ^ 2)) =
      ∫⁻ z in upperHalf, ENNReal.ofReal (jacobian W (conj z)) *
        (‖m z‖ₑ ^ 2 / ENNReal.ofReal (infDist (W (conj z)) (W '' {u : ℂ | u.im < 0})ᶜ) ^ 2) := by
    rw [← s7g_r1_conj_image]
    rw [← gzE_conj_measurePreserving.setLIntegral_comp_emb hemb _ upperHalf]
    simp only [Complex.conj_conj]
  rw [hL]
  refine le_trans (le_of_eq ?_) hR3
  refine setLIntegral_congr_fun (isOpen_lt continuous_const Complex.continuous_im).measurableSet fun z hz => ?_
  rw [hjac z hz, hdist z, div_eq_mul_inv, div_eq_mul_inv]
  ring

/-- Change of variables through a q.c. map, with the weight transported by `e⁻¹`. -/
theorem s7g_r1_cov {W : ℂ → ℂ} {D : Set ℂ} {K : ℝ} (e : ℂ ≃ₜ ℂ) (he : ⇑e = W) (hKD : IsKQC W D K)
    (n : ℂ → ℝ≥0∞) (G : ℂ → ℝ≥0∞ → ℝ≥0∞) :
    (∫⁻ u in D, ENNReal.ofReal (jacobian W u) * G (W u) (n u)) =
      ∫⁻ X in W '' D, G X ((W '' D).piecewise (fun X => n (e.symm X)) 0 X) := by
  rw [QCV.qcv_lintegral_image_eq hKD (fun X => G X ((W '' D).piecewise (fun X => n (e.symm X)) 0 X))]
  refine setLIntegral_congr_fun hKD.1.measurableSet fun u hu => ?_
  have hmem : W u ∈ W '' D := mem_image_of_mem W hu
  rw [piecewise_eq_of_mem _ _ _ hmem]
  have : e.symm (W u) = u := by rw [← he, e.symm_apply_apply]
  rw [this]

/-- Measurability of the transported weight. -/
theorem s7g_r1_pw_meas {W : ℂ → ℂ} {D : Set ℂ} (e : ℂ ≃ₜ ℂ) (he : ⇑e = W) (hD : IsOpen D) {n : ℂ → ℂ}
    (hn : ContinuousOn n D) : Measurable ((W '' D).piecewise (fun X => ‖n (e.symm X)‖ₑ) 0) := by
  have hO : IsOpen (W '' D) := by rw [← he]; exact e.isOpenMap _ hD
  have hmaps : MapsTo e.symm (W '' D) D := by
    rintro _ ⟨u, hu, rfl⟩
    rw [← he, e.symm_apply_apply]
    exact hu
  exact ContinuousOn.measurable_piecewise
    (continuous_enorm.comp_continuousOn (hn.comp e.symm.continuous.continuousOn hmaps))
    continuousOn_const hO.measurableSet

/-- `m = (u - ū)²/2 · φ̄` is continuous on `𝕌`. -/
theorem s7g_r1_m_cont {m φ : ℂ → ℂ} (hφ : DifferentiableOn ℂ φ upperHalf)
    (hm : ∀ u ∈ upperHalf, m u = (u - conj u) ^ 2 / 2 * conj (φ u)) : ContinuousOn m upperHalf :=
  (((continuous_id.sub Complex.continuous_conj).pow 2 |>.div_const 2).continuousOn.mul
    (Complex.continuous_conj.comp_continuousOn hφ.continuousOn)).congr fun u hu => hm u hu

/-- R1 for a fixed parameter. -/
theorem s7g_r1_fixed {W : ℂ → ℂ} {K k' : ℝ} (hK : IsKQC W univ K) (hs : W '' univ = univ)
    (hC : ContDiffOn ℝ 1 W {u : ℂ | u.im ≠ 0}) (hk0 : 0 ≤ k') (hk1 : k' < 1)
    (hker : ∀ y : ℂ, y.im ≠ 0 → (1 - k' ^ 2) * ‖dz W y‖ ^ 2 ≤ jacobian W y) {C3 CS : ℝ≥0∞}
    (hC3 : ∀ W : ℂ → ℂ, IsKQC W univ K → W '' univ = univ → ContDiffOn ℝ 1 W upperHalf → ∀ m φ : ℂ → ℂ,
      DifferentiableOn ℂ φ upperHalf → (∀ u ∈ upperHalf, m u = (u - conj u) ^ 2 / 2 * conj (φ u)) →
      (∫⁻ u in upperHalf, ‖m u‖ₑ ^ 2 * ENNReal.ofReal (jacobian W u) /
          ENNReal.ofReal (infDist (W u) (W '' upperHalf)ᶜ) ^ 2) ≤
        C3 * ∫⁻ u in upperHalf, ‖m u‖ₑ ^ 2 * ENNReal.ofReal (rhoU u))
    (hCS : ∀ Ω Ω' : Set ℂ, IsOpen Ω → IsOpen Ω' → Disjoint Ω Ω' →
      ∀ f g : ℂ → ℝ≥0∞, Measurable f → Measurable g →
        (∫⁻ X in Ω, ∫⁻ Y in Ω', f X * g Y / ‖X - Y‖ₑ ^ 4) ≤
          CS * (∫⁻ X in Ω, f X ^ 2 / ENNReal.ofReal (infDist X Ωᶜ) ^ 2) ^ (1 / 2 : ℝ) *
            (∫⁻ Y in Ω', g Y ^ 2 / ENNReal.ofReal (infDist Y Ω'ᶜ) ^ 2) ^ (1 / 2 : ℝ))
    {m₁ m₂ φ₁ φ₂ : ℂ → ℂ} (hφ₁ : DifferentiableOn ℂ φ₁ upperHalf)
    (hm₁ : ∀ u ∈ upperHalf, m₁ u = (u - conj u) ^ 2 / 2 * conj (φ₁ u))
    (hφ₂ : DifferentiableOn ℂ φ₂ upperHalf) (hm₂ : ∀ u ∈ upperHalf, m₂ u = (u - conj u) ^ 2 / 2 * conj (φ₂ u)) :
    (∫⁻ z in upperHalf, ∫⁻ u in upperHalf, ‖m₁ z‖ₑ * ‖m₂ u‖ₑ *
        ‖dz W u * dz W (conj z) / (W u - W (conj z)) ^ 2‖ₑ ^ 2) ≤
      ENNReal.ofReal ((1 - k' ^ 2)⁻¹) ^ 2 * (CS *
        (C3 * ∫⁻ u in upperHalf, ‖m₁ u‖ₑ ^ 2 * ENNReal.ofReal (rhoU u)) ^ (1 / 2 : ℝ) *
        (C3 * ∫⁻ u in upperHalf, ‖m₂ u‖ₑ ^ 2 * ENNReal.ofReal (rhoU u)) ^ (1 / 2 : ℝ)) := by
  obtain ⟨e, he⟩ := t1_homeomorph hK hs
  have hinj : Function.Injective W := by rw [← he]; exact e.injective
  set L : Set ℂ := {u : ℂ | u.im < 0} with hLd
  have hU : IsOpen upperHalf := isOpen_lt continuous_const Complex.continuous_im
  have hLo : IsOpen L := isOpen_lt Complex.continuous_im continuous_const
  have hKU : IsKQC W upperHalf K := nx_isKQC_restrict hK hU (subset_univ _)
  have hKL : IsKQC W L K := nx_isKQC_restrict hK hLo (subset_univ _)
  set Ω : Set ℂ := W '' upperHalf with hΩd
  set Ωs : Set ℂ := W '' L with hΩsd
  have hΩo : IsOpen Ω := by rw [hΩd, ← he]; exact e.isOpenMap _ hU
  have hΩso : IsOpen Ωs := by rw [hΩsd, ← he]; exact e.isOpenMap _ hLo
  have hdisj : Disjoint Ωs Ω := by
    rw [disjoint_left]
    rintro _ ⟨w, hw, rfl⟩ ⟨u, hu, huw⟩
    have := hinj huw
    have h1 : 0 < u.im := hu
    have h2 : w.im < 0 := hw
    rw [this] at h1
    linarith
  set n₂ : ℂ → ℝ≥0∞ := fun u => ‖m₂ u‖ₑ with hn₂
  set n₁ : ℂ → ℝ≥0∞ := fun w => ‖m₁ (conj w)‖ₑ with hn₁
  set f : ℂ → ℝ≥0∞ := Ω.piecewise (fun X => n₂ (e.symm X)) 0 with hfd
  set g : ℂ → ℝ≥0∞ := Ωs.piecewise (fun Y => n₁ (e.symm Y)) 0 with hgd
  have hfm : Measurable f := s7g_r1_pw_meas e he hU (s7g_r1_m_cont hφ₂ hm₂)
  have hgm : Measurable g := by
    have hc : ContinuousOn (fun w => m₁ (conj w)) L := by
      refine (s7g_r1_m_cont hφ₁ hm₁).comp Complex.continuous_conj.continuousOn fun w hw => ?_
      have : w.im < 0 := hw
      show 0 < (conj w).im
      rw [Complex.conj_im]; linarith
    exact s7g_r1_pw_meas e he hLo hc
  set c0 : ℝ≥0∞ := ENNReal.ofReal ((1 - k' ^ 2)⁻¹) with hc0
  set H : ℂ → ℝ≥0∞ := fun Y => ∫⁻ X in Ω, f X / ‖X - Y‖ₑ ^ 4 with hHd
  -- step 1: pointwise kernel bound
  have hstep1 : (∫⁻ z in upperHalf, ∫⁻ u in upperHalf, ‖m₁ z‖ₑ * ‖m₂ u‖ₑ *
        ‖dz W u * dz W (conj z) / (W u - W (conj z)) ^ 2‖ₑ ^ 2) ≤
      c0 ^ 2 * ∫⁻ z in upperHalf, (‖m₁ z‖ₑ * ENNReal.ofReal (jacobian W (conj z))) * H (W (conj z)) := by
    rw [← lintegral_const_mul' _ _ (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)]
    refine setLIntegral_mono' hU.measurableSet fun z hz => ?_
    have hzi : 0 < z.im := hz
    have hinner : (∫⁻ u in upperHalf, ENNReal.ofReal (jacobian W u) * (‖m₂ u‖ₑ / ‖W u - W (conj z)‖ₑ ^ 4)) =
        H (W (conj z)) :=
      s7g_r1_cov e he hKU n₂ (fun X t => t / ‖X - W (conj z)‖ₑ ^ 4)
    rw [← hinner, ← lintegral_const_mul' _ _ (ENNReal.mul_ne_top enorm_ne_top ENNReal.ofReal_ne_top),
      ← lintegral_const_mul' _ _ (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)]
    refine setLIntegral_mono' hU.measurableSet fun u hu => ?_
    have hui : 0 < u.im := hu
    have hw : W u - W (conj z) ≠ 0 := by
      intro h
      have := hinj (sub_eq_zero.1 h)
      have h2 := congrArg Complex.im this
      rw [Complex.conj_im] at h2
      linarith
    exact s7g_r1_pt hk1 hk0 hker hz hu hw _ _
  -- step 3: the outer integral through `conj` and the change of variables on `𝕃`
  have hstep3 : (∫⁻ z in upperHalf, (‖m₁ z‖ₑ * ENNReal.ofReal (jacobian W (conj z))) * H (W (conj z))) =
      ∫⁻ Y in Ωs, H Y * g Y := by
    have hemb := Complex.conjLIE.toHomeomorph.measurableEmbedding
    have h1 : (∫⁻ z in upperHalf, (‖m₁ z‖ₑ * ENNReal.ofReal (jacobian W (conj z))) * H (W (conj z))) =
        ∫⁻ w in L, ENNReal.ofReal (jacobian W w) * (H (W w) * n₁ w) := by
      rw [hLd, ← s7g_r1_conj_image, ← gzE_conj_measurePreserving.setLIntegral_comp_emb hemb _ upperHalf]
      refine setLIntegral_congr_fun hU.measurableSet fun z _ => ?_
      simp only [hn₁, Complex.conj_conj]
      ring
    rw [h1]
    exact s7g_r1_cov e he hKL n₁ (fun Y t => H Y * t)
  -- step 4: Schur
  have hstep4 : (∫⁻ Y in Ωs, H Y * g Y) ≤
      CS * (∫⁻ Y in Ωs, g Y ^ 2 / ENNReal.ofReal (infDist Y Ωsᶜ) ^ 2) ^ (1 / 2 : ℝ) *
        (∫⁻ X in Ω, f X ^ 2 / ENNReal.ofReal (infDist X Ωᶜ) ^ 2) ^ (1 / 2 : ℝ) := by
    refine le_trans (le_of_eq ?_) (hCS Ωs Ω hΩso hΩo hdisj g f hgm hfm)
    refine setLIntegral_congr_fun hΩso.measurableSet fun Y _ => ?_
    have hmX : Measurable fun X => f X / ‖X - Y‖ₑ ^ 4 := hfm.div (by fun_prop)
    rw [hHd, mul_comm, ← lintegral_const_mul _ hmX]
    congr 1
    funext X
    rw [enorm_sub_rev, mul_div_assoc]
  -- steps 5, 6: the two weighted norms
  have hstep5 : (∫⁻ X in Ω, f X ^ 2 / ENNReal.ofReal (infDist X Ωᶜ) ^ 2) ≤
      C3 * ∫⁻ u in upperHalf, ‖m₂ u‖ₑ ^ 2 * ENNReal.ofReal (rhoU u) := by
    rw [← s7g_r1_cov e he hKU n₂ (fun X t => t ^ 2 / ENNReal.ofReal (infDist X Ωᶜ) ^ 2)]
    refine le_trans (le_of_eq ?_) (hC3 W hK hs (hC.mono fun u hu => ne_of_gt hu) m₂ φ₂ hφ₂ hm₂)
    refine setLIntegral_congr_fun hU.measurableSet fun u _ => ?_
    simp only [hn₂, div_eq_mul_inv]
    ring
  have hstep6 : (∫⁻ Y in Ωs, g Y ^ 2 / ENNReal.ofReal (infDist Y Ωsᶜ) ^ 2) ≤
      C3 * ∫⁻ u in upperHalf, ‖m₁ u‖ₑ ^ 2 * ENNReal.ofReal (rhoU u) := by
    rw [← s7g_r1_cov e he hKL n₁ (fun Y t => t ^ 2 / ENNReal.ofReal (infDist Y Ωsᶜ) ^ 2)]
    exact s7g_r1_lower hK hs hC hC3 hφ₁ hm₁
  calc _ ≤ c0 ^ 2 * ∫⁻ z in upperHalf, (‖m₁ z‖ₑ * ENNReal.ofReal (jacobian W (conj z))) * H (W (conj z)) :=
        hstep1
    _ = c0 ^ 2 * ∫⁻ Y in Ωs, H Y * g Y := by rw [hstep3]
    _ ≤ c0 ^ 2 * (CS * (∫⁻ Y in Ωs, g Y ^ 2 / ENNReal.ofReal (infDist Y Ωsᶜ) ^ 2) ^ (1 / 2 : ℝ) *
          (∫⁻ X in Ω, f X ^ 2 / ENNReal.ofReal (infDist X Ωᶜ) ^ 2) ^ (1 / 2 : ℝ)) := by
        gcongr
    _ ≤ _ := by
        gcongr <;> assumption

/-- **R1** (stub `s7g_L1`). -/
theorem s7g_L1 {a b : ℂ → ℂ} {k : ℝ} (hk : 0 ≤ k) (ha : IsBeltramiCoeff a upperHalf k)
    (hb : IsBeltramiCoeff b upperHalf k) (has : ContDiffOn ℝ (⊤ : ℕ∞) a upperHalf)
    (hbs : ContDiffOn ℝ (⊤ : ℕ∞) b upperHalf) {R : ℝ} (hR : 0 ≤ R) (hRk : 2 * R * k < 1)
    {W : (ℂ × ℂ) × (ℂ × ℂ) → ℂ → ℂ} (hW : W = fun P => normalizedSolution fun u =>
      (if 0 < u.im then P.1.1 * a u + P.1.2 * b u else 0) +
        (if u.im < 0 then P.2.1 * conj (a (conj u)) + P.2.2 * conj (b (conj u)) else 0))
    {m₁ m₂ φ₁ φ₂ : ℂ → ℂ} (hφ₁ : DifferentiableOn ℂ φ₁ upperHalf)
    (hm₁ : ∀ u ∈ upperHalf, m₁ u = (u - conj u) ^ 2 / 2 * conj (φ₁ u))
    (hf₁ : ∫⁻ u in upperHalf, ‖m₁ u‖ₑ ^ 2 * ENNReal.ofReal (rhoU u) < ∞)
    (hφ₂ : DifferentiableOn ℂ φ₂ upperHalf) (hm₂ : ∀ u ∈ upperHalf, m₂ u = (u - conj u) ^ 2 / 2 * conj (φ₂ u))
    (hf₂ : ∫⁻ u in upperHalf, ‖m₂ u‖ₑ ^ 2 * ENNReal.ofReal (rhoU u) < ∞) :
    ∃ M : ℝ≥0∞, M < ∞ ∧ ∀ P ∈ closedBall (0 : (ℂ × ℂ) × (ℂ × ℂ)) R,
      (∫⁻ z in upperHalf, ∫⁻ u in upperHalf, ‖m₁ z‖ₑ * ‖m₂ u‖ₑ *
        ‖dz (W P) u * dz (W P) (conj z) / (W P u - W P (conj z)) ^ 2‖ₑ ^ 2) ≤ M := by
  set K0 : ℝ := (1 + 2 * R * k) / (1 - 2 * R * k) with hK0
  have hk'0 : 0 ≤ 2 * R * k := by positivity
  have hK1 : 1 ≤ K0 := by
    rw [hK0, le_div_iff₀ (by linarith)]
    linarith
  obtain ⟨C3, hC3t, hC3⟩ := s7g_transfer hK1
  obtain ⟨CS, hCSt, hCS⟩ := s7g_schur
  refine ⟨ENNReal.ofReal ((1 - (2 * R * k) ^ 2)⁻¹) ^ 2 * (CS *
      (C3 * ∫⁻ u in upperHalf, ‖m₁ u‖ₑ ^ 2 * ENNReal.ofReal (rhoU u)) ^ (1 / 2 : ℝ) *
      (C3 * ∫⁻ u in upperHalf, ‖m₂ u‖ₑ ^ 2 * ENNReal.ofReal (rhoU u)) ^ (1 / 2 : ℝ)), ?_, ?_⟩
  · refine ENNReal.mul_lt_top (ENNReal.pow_lt_top ENNReal.ofReal_lt_top) (ENNReal.mul_lt_top
      (ENNReal.mul_lt_top hCSt (ENNReal.rpow_lt_top_of_nonneg (by norm_num) (ENNReal.mul_lt_top hC3t hf₁).ne))
      (ENNReal.rpow_lt_top_of_nonneg (by norm_num) (ENNReal.mul_lt_top hC3t hf₂).ne))
  · intro P hP
    obtain ⟨hKP, hsP, hCP, hkerP⟩ := s7g_r1_W hk ha hb has hbs hR hRk hW hP
    exact s7g_r1_fixed hKP hsP hCP hk'0 hRk hkerP hC3 hCS hφ₁ hm₁ hφ₂ hm₂

end TakhtajanTeo
