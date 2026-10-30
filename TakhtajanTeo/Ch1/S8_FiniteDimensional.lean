import TakhtajanTeo.Ch1.S7_Curvature
import TakhtajanTeo.Ch1.IdentityContributionCore

/-!
# Chapter 1, §8 — Finite-dimensional Teichmüller spaces (TT:3158–3474)

For a cofinite Fuchsian group `Γ`, Wolpert's curvature formulas for `T(Γ)` are derived from those of `T(1)`.

* `Ω^{-1,1}(𝔻*, Γ) ∩ H^{-1,1}(𝔻*) = {0}`; the Petersson product as an average (Lemma 1.9)
* Lemma 8.1, Lemma 8.2, Remark 8.3, the metric `g_{μν̄}` near the origin of `T(Γ)`, Lemma 8.4
* Theorem 8.5 (Wolpert: first and second variations), the projector kernel and the Ricci tensor (8.1), and the
  contribution `-13/(12π)` of the identity

**Modelling.**
- The section works in the model `𝔻`, with `Γ` acting on `𝔻` and Beltrami differentials on `𝔻`.
- `w_κ` is the normalized solution (fixing `-1, -i, 1`) for `κ` on `𝔻`, extended to `𝔻*` by reflection (1.1).
- `P` is (1.7) on `𝔻`.
- Integrals over `Γ\𝔻` use a fundamental domain in `𝔻`. Integrals over `Γ_κ\𝔻`, `Γ_κ = w_κ Γ w_κ⁻¹`, use the image
  `w_κ(F)` of a fundamental domain `F` of `Γ`.

**Not stated** (recorded):
- "The embedding `T(Γ) ↪ T(1)` is not holomorphic for the Hilbert structure" (TT:3162) is explained by the trivial
  intersection, which is stated.
- "`T(Γ)` is not Kähler–Einstein" and the conjugacy-class discussion after (8.1) (TT:3468) are not made precise in
  the memoir.
- Remark 8.6 is a citation.
-/

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal ComplexConjugate Classical Real

noncomputable section

namespace TakhtajanTeo

open LiZhongQC


/-! ## The model `𝔻` -/

/-- `μ ∈ Ω^{-1,1}(𝔻)`: `μ = (1 - |z|²)² φ̄` on `𝔻` with `φ` holomorphic and `(1 - |z|²)² φ` bounded on `𝔻`. -/
def IsHarmonicD (μ : ℂ → ℂ) : Prop :=
  ∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ unitDisc ∧ (∃ C, ∀ z ∈ unitDisc, ‖(1 - ‖z‖ ^ 2) ^ 2 * φ z‖ ≤ C) ∧
    ∀ z ∈ unitDisc, μ z = (1 - ‖z‖ ^ 2) ^ 2 * conj (φ z)

/-- `μ` is a Beltrami differential for `Γ` on `𝔻`: `μ(γz) \overline{γ'(z)}/γ'(z) = μ(z)` on `𝔻`. -/
def IsGammaInvD (Γ : Subgroup SL2C) (μ : ℂ → ℂ) : Prop :=
  ∀ g ∈ Γ, ∀ z ∈ unitDisc, μ (mob g z) * (conj (deriv (mob g) z) / deriv (mob g) z) = μ z

/-- `F` is a measurable fundamental domain of `Γ` in `D` (as `IsFundDomain`, for a general domain `D`). -/
def IsFundDomainOn (Γ : Subgroup SL2C) (D F : Set ℂ) : Prop :=
  MeasurableSet F ∧ F ⊆ D ∧ (∀ᵐ z ∂(volume.restrict D), ∃ g ∈ Γ, mob g z ∈ F) ∧
    ∀ g ∈ Γ, ∀ h ∈ Γ, mob g ≠ mob h → volume (mob g ⁻¹' F ∩ mob h ⁻¹' F ∩ D) = 0

/-- A chosen fundamental domain of `Γ` in `D` (junk `∅`). -/
def fundDomainOn (Γ : Subgroup SL2C) (D : Set ℂ) : Set ℂ :=
  if h : ∃ F, IsFundDomainOn Γ D F then h.choose else ∅

/-- `∬_{Γ\𝔻} f d²z`, over the chosen fundamental domain in `𝔻`. -/
def quotIntD (Γ : Subgroup SL2C) (f : ℂ → ℂ) : ℂ := ∫ z in fundDomainOn Γ unitDisc, f z

/-- The hyperbolic area `A(Γ\𝔻)`. -/
def hypAreaD (Γ : Subgroup SL2C) : ℝ := ∫ z in fundDomainOn Γ unitDisc, rho z

/-- `𝔻_r = {|z| ≤ r}` (TT:3186). -/
def closedDiscR (r : ℝ) : Set ℂ := closedBall 0 r

/-- The hyperbolic area `A(𝔻_r)`. -/
def hypAreaDiscR (r : ℝ) : ℝ := ∫ z in closedDiscR r, rho z

/-- The Petersson inner product `(f, g)_Γ = ∬_{Γ\𝔻} f ḡ ρ d²z` (TT:3186). -/
def innerGamma (Γ : Subgroup SL2C) (f g : ℂ → ℂ) : ℂ := quotIntD Γ fun z => f z * conj (g z) * rho z

/-- The inner product `( , )` of `L²(𝔻, ρ d²z)`. -/
def l2InnerD (f g : ℂ → ℂ) : ℂ := ∫ z in unitDisc, f z * conj (g z) * rho z

/-- `μ_r = χ_r μ`, `χ_r` the characteristic function of `𝔻_r` (TT:3186). -/
def truncR (r : ℝ) (μ : ℂ → ℂ) : ℂ → ℂ := (closedDiscR r).indicator μ

/-- (1.7) on `𝔻`: `(Pμ)(z) = (3(1 - |z|²)²/π) ∬_𝔻 μ(ζ)/(1 - ζ z̄)⁴ d²ζ`. -/
def harmonicProjD (μ : ℂ → ℂ) (z : ℂ) : ℂ :=
  3 * (1 - ‖z‖ ^ 2) ^ 2 / π * ∫ ζ in unitDisc, μ ζ / (1 - ζ * conj z) ^ 4

/-! ### Bounds on the projector `P` (used for Remark 8.3 and Lemma 8.1) -/

theorem proj_kernel_jacobian {z w : ℂ} (hz : ‖z‖ < 1) (hw : ‖w‖ < 1) :
    ‖deriv (blaschke (-z)) w‖ ^ 2 * ‖(1 - blaschke (-z) w * conj z) ^ 4‖⁻¹ =
      ((1 - ‖z‖ ^ 2) ^ 2)⁻¹ := by
  have hz' : ‖-z‖ < 1 := by simpa using hz
  have hρ := rho_blaschke_jacobian hz' hw
  have h1 := one_sub_normSq_blaschke hz' hw
  simp only [Complex.normSq_eq_norm_sq] at h1
  have hden : (1 : ℂ) + conj z * w ≠ 0 := by
    have := blaschke_den_ne_zero hz' hw
    simpa using this
  have hs : 0 < 1 - ‖z‖ ^ 2 := by nlinarith [norm_nonneg z]
  have hws : 0 < 1 - ‖w‖ ^ 2 := by nlinarith [norm_nonneg w]
  set N : ℝ := ‖(1 : ℂ) + conj z * w‖ with hN
  have hNpos : 0 < N := norm_pos_iff.mpr hden
  have hzz : conj z * z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
    rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have hb : blaschke (-z) w = (w + z) / (1 + conj z * w) := by
    unfold blaschke
    rw [map_neg, neg_mul, sub_neg_eq_add, sub_neg_eq_add]
  have hzz' : conj z * z = (‖z‖ : ℂ) ^ 2 := by rw [hzz]; push_cast; rfl
  have h2 : 1 - blaschke (-z) w * conj z = (((1 - ‖z‖ ^ 2 : ℝ)) : ℂ) / (1 + conj z * w) := by
    have hX : (w + z) / (1 + conj z * w) * (1 + conj z * w) = w + z := div_mul_cancel₀ _ hden
    have h : 1 - (w + z) / (1 + conj z * w) * conj z = (1 - conj z * z) / (1 + conj z * w) := by
      rw [eq_div_iff hden]
      linear_combination (-(conj z)) * hX
    rw [hb, h, hzz']
    push_cast
    ring
  have h3 : ‖1 - blaschke (-z) w * conj z‖ = (1 - ‖z‖ ^ 2) / N := by
    rw [h2, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs]
  have h4 : 1 - ‖blaschke (-z) w‖ ^ 2 = (1 - ‖w‖ ^ 2) * (1 - ‖z‖ ^ 2) / N ^ 2 := by
    have := h1
    simp only [norm_neg, map_neg, neg_mul, sub_neg_eq_add] at this
    rw [this]
  have hρ' : 4 / (1 - ‖blaschke (-z) w‖ ^ 2) ^ 2 * ‖deriv (blaschke (-z)) w‖ ^ 2 =
      4 / (1 - ‖w‖ ^ 2) ^ 2 := by simpa [rho] using hρ
  rw [h4] at hρ'
  rw [norm_pow, h3]
  have hd : ‖deriv (blaschke (-z)) w‖ ^ 2 = (1 - ‖z‖ ^ 2) ^ 2 / N ^ 4 := by
    field_simp at hρ' ⊢
    nlinarith [hρ']
  rw [hd]
  field_simp


theorem proj_kernel_image {z : ℂ} (hz : ‖z‖ < 1) :
    blaschke (-z) '' unitDisc = unitDisc := (isConformalOnto_blaschke (a := -z) (by simpa using hz)).2.2

theorem proj_kernel_integrableOn {z : ℂ} (hz : ‖z‖ < 1) :
    IntegrableOn (fun ζ : ℂ => ‖(1 - ζ * conj z) ^ 4‖⁻¹) unitDisc := by
  have hz' : ‖-z‖ < 1 := by simpa using hz
  have hf := isConformalOnto_blaschke hz'
  have hi := ahP_integrableOn_image (U := unitDisc) (show IsOpen unitDisc from isOpen_ball) hf.1 hf.2.1
    (fun ζ : ℂ => ‖(1 - ζ * conj z) ^ 4‖⁻¹)
  rw [hf.2.2] at hi
  refine hi.mpr ?_
  have hc : IntegrableOn (fun _ : ℂ => ((1 - ‖z‖ ^ 2) ^ 2)⁻¹) unitDisc := by
    exact integrableOn_const (measure_ball_lt_top).ne (by simp)
  refine hc.congr_fun (fun w hw => ?_) measurableSet_ball
  have := proj_kernel_jacobian hz (mem_ball_zero_iff.mp hw)
  simpa [smul_eq_mul] using this.symm

theorem proj_kernel_integral {z : ℂ} (hz : ‖z‖ < 1) :
    (∫ ζ in unitDisc, ‖(1 - ζ * conj z) ^ 4‖⁻¹) = π / (1 - ‖z‖ ^ 2) ^ 2 := by
  have hz' : ‖-z‖ < 1 := by simpa using hz
  have hf := isConformalOnto_blaschke hz'
  have hi := ahP_integral_image (U := unitDisc) (show IsOpen unitDisc from isOpen_ball) hf.1 hf.2.1
    (fun ζ : ℂ => ‖(1 - ζ * conj z) ^ 4‖⁻¹)
  rw [hf.2.2] at hi
  have hc : (∫ w in unitDisc, ‖deriv (blaschke (-z)) w‖ ^ 2 • ‖(1 - blaschke (-z) w * conj z) ^ 4‖⁻¹) =
      ∫ _w in unitDisc, ((1 - ‖z‖ ^ 2) ^ 2)⁻¹ := by
    apply setIntegral_congr_fun (show MeasurableSet unitDisc from measurableSet_ball)
    intro w hw
    have := proj_kernel_jacobian hz (mem_ball_zero_iff.mp hw)
    simpa [smul_eq_mul] using this
  rw [hi, hc]
  rw [setIntegral_const]
  have hv : volume.real unitDisc = π := by
    simp [unitDisc, Measure.real, Complex.volume_ball]
  rw [hv, smul_eq_mul]
  field_simp

theorem proj_kernel_norm_pos {ζ z : ℂ} (hζ : ‖ζ‖ < 1) (hz : ‖z‖ < 1) : 0 < ‖(1 - ζ * conj z) ^ 4‖ := by
  have : (1 : ℂ) - ζ * conj z ≠ 0 := by
    have := blaschke_den_ne_zero (a := z) (z := ζ) hz hζ
    rwa [mul_comm] at this
  exact norm_pos_iff.mpr (pow_ne_zero 4 this)

theorem harmonicProjD_norm_le_of {ν : ℂ → ℂ} {I : ℝ} {z : ℂ} (hz : ‖z‖ < 1)
    (hI : ‖∫ ζ in unitDisc, ν ζ / (1 - ζ * conj z) ^ 4‖ ≤ I) :
    ‖harmonicProjD ν z‖ ≤ 3 * (1 - ‖z‖ ^ 2) ^ 2 / π * I := by
  have hs : 0 < 1 - ‖z‖ ^ 2 := by nlinarith [norm_nonneg z]
  unfold harmonicProjD
  rw [norm_mul]
  have hn : ‖(3 * (1 - ‖z‖ ^ 2) ^ 2 / π : ℂ)‖ = 3 * (1 - ‖z‖ ^ 2) ^ 2 / π := by
    have : (3 * (1 - ‖z‖ ^ 2) ^ 2 / π : ℂ) = ((3 * (1 - ‖z‖ ^ 2) ^ 2 / π : ℝ) : ℂ) := by push_cast; ring
    rw [this, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (div_pos (mul_pos three_pos (pow_pos hs 2)) Real.pi_pos)]
  rw [hn]
  exact mul_le_mul_of_nonneg_left hI (div_pos (mul_pos three_pos (pow_pos hs 2)) Real.pi_pos).le

theorem harmonicProjD_norm_le {ν : ℂ → ℂ} {C : ℝ} (hC : ∀ ζ ∈ unitDisc, ‖ν ζ‖ ≤ C) {z : ℂ}
    (hz : ‖z‖ < 1) : ‖harmonicProjD ν z‖ ≤ 3 * C := by
  have hs : 0 < 1 - ‖z‖ ^ 2 := by nlinarith [norm_nonneg z]
  have h0 : 0 ≤ C := (norm_nonneg _).trans (hC 0 (by simp [unitDisc]))
  have hI : ‖∫ ζ in unitDisc, ν ζ / (1 - ζ * conj z) ^ 4‖ ≤ C * (π / (1 - ‖z‖ ^ 2) ^ 2) := by
    refine (norm_integral_le_integral_norm _).trans ?_
    rw [← proj_kernel_integral hz, ← integral_const_mul]
    apply integral_mono_of_nonneg
    · exact Filter.Eventually.of_forall (fun ζ => norm_nonneg _)
    · exact (proj_kernel_integrableOn hz).const_mul C
    · filter_upwards [ae_restrict_mem (show MeasurableSet unitDisc from measurableSet_ball)] with ζ hζ
      rw [norm_div, div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_right (hC ζ hζ) (inv_nonneg.mpr (norm_nonneg _))
  refine (harmonicProjD_norm_le_of hz hI).trans (le_of_eq ?_)
  field_simp

theorem harmonicProjD_trunc_norm_le {μ : ℂ → ℂ} {C s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (hC : ∀ ζ ∈ unitDisc, ‖μ ζ‖ ≤ C) {z : ℂ} (hz : ‖z‖ < 1) :
    ‖harmonicProjD (truncR s μ) z‖ ≤ 3 * C / (1 - s) ^ 4 * (1 - ‖z‖ ^ 2) ^ 2 := by
  have h0 : 0 ≤ C := (norm_nonneg _).trans (hC 0 (by simp [unitDisc]))
  have hs : 0 < 1 - ‖z‖ ^ 2 := by nlinarith [norm_nonneg z]
  have h1s : 0 < 1 - s := by linarith
  have hI : ‖∫ ζ in unitDisc, truncR s μ ζ / (1 - ζ * conj z) ^ 4‖ ≤ C / (1 - s) ^ 4 * π := by
    have hv : volume.real unitDisc = π := by
      simp [unitDisc, Measure.real, Complex.volume_ball]
    have := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := unitDisc)
      (f := fun ζ => truncR s μ ζ / (1 - ζ * conj z) ^ 4) (C := C / (1 - s) ^ 4)
      (by simp [unitDisc, measure_ball_lt_top]) (fun ζ hζ => ?_)
    · rwa [hv] at this
    · have hζ1 : ‖ζ‖ < 1 := mem_ball_zero_iff.mp hζ
      have hp := proj_kernel_norm_pos hζ1 hz
      by_cases hin : ζ ∈ closedDiscR s
      · have hζs : ‖ζ‖ ≤ s := by simpa [closedDiscR] using hin
        have hlow : 1 - s ≤ ‖1 - ζ * conj z‖ := by
          have h := norm_sub_norm_le (1 : ℂ) (ζ * conj z)
          have h2 : ‖ζ * conj z‖ ≤ s := by
            rw [norm_mul, Complex.norm_conj]
            nlinarith [norm_nonneg ζ, norm_nonneg z]
          simp only [norm_one] at h
          linarith
        have hp4 : (1 - s) ^ 4 ≤ ‖(1 - ζ * conj z) ^ 4‖ := by
          rw [norm_pow]; exact pow_le_pow_left₀ h1s.le hlow 4
        simp only [truncR, indicator_of_mem hin]
        rw [norm_div]
        exact div_le_div₀ h0 (hC ζ hζ) (by positivity) hp4
      · rw [show truncR s μ ζ = 0 by simp [truncR, hin]]
        simp only [zero_div, norm_zero]
        positivity
  refine (harmonicProjD_norm_le_of hz hI).trans (le_of_eq ?_)
  field_simp

theorem l2InnerD_norm_le {f g : ℂ → ℂ} {K Cg : ℝ}
    (hf : ∀ z ∈ unitDisc, ‖f z‖ ≤ K * (1 - ‖z‖ ^ 2) ^ 2) (hg : ∀ z ∈ unitDisc, ‖g z‖ ≤ Cg) :
    ‖l2InnerD f g‖ ≤ 4 * K * Cg * π := by
  have h0 : 0 ≤ Cg := (norm_nonneg _).trans (hg 0 (by simp [unitDisc]))
  have hv : volume.real unitDisc = π := by
    simp [unitDisc, Measure.real, Complex.volume_ball]
  have := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := unitDisc)
    (f := fun z => f z * conj (g z) * (rho z : ℂ)) (C := 4 * K * Cg)
    (by simp [unitDisc]) (fun z hz => ?_)
  · unfold l2InnerD
    rw [hv] at this
    linarith
  · have hz1 : ‖z‖ < 1 := mem_ball_zero_iff.mp hz
    have hs : 0 < 1 - ‖z‖ ^ 2 := by nlinarith [norm_nonneg z]
    rw [norm_mul, norm_mul, Complex.norm_conj, Complex.norm_real, rho, Real.norm_eq_abs,
      abs_of_pos (by positivity)]
    calc ‖f z‖ * ‖g z‖ * (4 / (1 - ‖z‖ ^ 2) ^ 2)
        ≤ (K * (1 - ‖z‖ ^ 2) ^ 2) * Cg * (4 / (1 - ‖z‖ ^ 2) ^ 2) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          exact mul_le_mul (hf z hz) (hg z hz) (norm_nonneg _) ((norm_nonneg _).trans (hf z hz))
      _ = 4 * K * Cg := by field_simp

theorem hypAreaDiscR_eq {r : ℝ} (h0 : 0 < r) (h1 : r < 1) :
    hypAreaDiscR r = 2 * π * (2 / (1 - r ^ 2) - 2) := by
  unfold hypAreaDiscR closedDiscR
  have hsub : closedBall (0 : ℂ) r ⊆ unitDisc := fun z hz => by
    have := mem_closedBall_zero_iff.mp hz
    exact mem_ball_zero_iff.mpr (by linarith)
  have e1 : (∫ z in closedBall (0 : ℂ) r, rho z) =
      ∫ z in unitDisc, (closedBall (0 : ℂ) r).indicator rho z := by
    rw [setIntegral_indicator measurableSet_closedBall, inter_eq_right.mpr hsub]
  have e2 : ∀ z : ℂ, (closedBall (0 : ℂ) r).indicator rho z =
      (Iic r).indicator (fun t : ℝ => 4 / (1 - t ^ 2) ^ 2) ‖z‖ := by
    intro z
    by_cases h : ‖z‖ ≤ r
    · simp [indicator, mem_closedBall_zero_iff, h, rho]
    · simp [indicator, mem_closedBall_zero_iff, h]
  rw [e1]
  simp_rw [e2]
  rw [integral_unitDisc_radial (fun t => (Iic r).indicator (fun t : ℝ => 4 / (1 - t ^ 2) ^ 2) t)]
  have e3 : ∀ t ∈ Ioo (0 : ℝ) 1, t * (Iic r).indicator (fun t : ℝ => 4 / (1 - t ^ 2) ^ 2) t =
      (Ioc 0 r).indicator (fun t : ℝ => t * (4 / (1 - t ^ 2) ^ 2)) t := by
    intro t ht
    by_cases h : t ≤ r
    · simp [indicator, h, ht.1]
    · simp [indicator, h]
  rw [setIntegral_congr_fun measurableSet_Ioo e3, setIntegral_indicator measurableSet_Ioc,
    inter_eq_right.mpr (Ioc_subset_Ioo_right h1), ← intervalIntegral.integral_of_le h0.le]
  have hd : ∀ x ∈ uIcc (0 : ℝ) r, HasDerivAt (fun t : ℝ => 2 / (1 - t ^ 2)) (x * (4 / (1 - x ^ 2) ^ 2)) x := by
    intro x hx
    have hx1 : x < 1 := by
      rcases mem_uIcc.mp hx with ⟨_, h⟩ | ⟨_, h⟩ <;> linarith [h]
    have hx0 : -1 < x := by
      rcases mem_uIcc.mp hx with ⟨h, _⟩ | ⟨h, _⟩ <;> linarith [h]
    have hne : 1 - x ^ 2 ≠ 0 := by nlinarith
    have h1' : HasDerivAt (fun t : ℝ => 1 - t ^ 2) (-(2 * x)) x := by
      simpa using ((hasDerivAt_pow 2 x).const_sub 1)
    have := (hasDerivAt_const x (2 : ℝ)).div h1' hne
    convert this using 1
    field_simp
    ring
  have hc : ContinuousOn (fun x : ℝ => x * (4 / (1 - x ^ 2) ^ 2)) (uIcc 0 r) := by
    apply ContinuousOn.mul continuousOn_id
    apply ContinuousOn.div continuousOn_const (by fun_prop)
    intro x hx
    have hx1 : x < 1 := by
      rcases mem_uIcc.mp hx with ⟨_, h⟩ | ⟨_, h⟩ <;> linarith [h]
    have hx0 : -1 < x := by
      rcases mem_uIcc.mp hx with ⟨h, _⟩ | ⟨h, _⟩ <;> linarith [h]
    have : 1 - x ^ 2 ≠ 0 := by nlinarith
    exact pow_ne_zero 2 this
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd (hc.intervalIntegrable)]
  norm_num

theorem hypAreaDiscR_tendsto : Tendsto hypAreaDiscR (𝓝[<] 1) atTop := by
  have h1 : Tendsto (fun r : ℝ => 1 - r ^ 2) (𝓝[<] 1) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · have : Tendsto (fun r : ℝ => 1 - r ^ 2) (𝓝 1) (𝓝 (1 - 1 ^ 2)) :=
        (continuous_const.sub (continuous_pow 2)).tendsto 1
      simpa using this.mono_left nhdsWithin_le_nhds
    · filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with r hr
      have : r ^ 2 < 1 := by nlinarith [hr.1, hr.2]
      exact sub_pos.mpr this
  have h2 := tendsto_inv_nhdsGT_zero.comp h1
  have h3 : Tendsto (fun r : ℝ => 2 * π * (2 * (1 - r ^ 2)⁻¹ - 2)) (𝓝[<] 1) atTop := by
    refine Tendsto.const_mul_atTop (by positivity) ?_
    exact tendsto_atTop_add_const_right _ (-2) (Tendsto.const_mul_atTop (by norm_num) h2)
  refine h3.congr' ?_
  filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with r hr
  rw [hypAreaDiscR_eq hr.1 hr.2]
  ring

theorem harmonicD_bound {μ : ℂ → ℂ} (hμ : IsHarmonicD μ) : ∃ C : ℝ, ∀ z ∈ unitDisc, ‖μ z‖ ≤ C := by
  obtain ⟨φ, _, ⟨C, hC⟩, hμφ⟩ := hμ
  refine ⟨C, fun z hz => ?_⟩
  rw [hμφ z hz, norm_mul, Complex.norm_conj, ← norm_mul] at *
  have := hC z hz
  have hs : 0 ≤ (1 - ‖z‖ ^ 2) ^ 2 := sq_nonneg _
  simpa [norm_mul, Real.norm_eq_abs, abs_of_nonneg hs] using this

theorem truncR_norm_le {μ : ℂ → ℂ} {C : ℝ} (r : ℝ) (hC : ∀ z ∈ unitDisc, ‖μ z‖ ≤ C) :
    ∀ z ∈ unitDisc, ‖truncR r μ z‖ ≤ C := by
  intro z hz
  by_cases h : z ∈ closedDiscR r
  · simp only [truncR, indicator_of_mem h]; exact hC z hz
  · simp only [truncR, indicator_of_notMem h, norm_zero]
    exact (norm_nonneg _).trans (hC z hz)

/-- The determinant-one Möbius derivative away from its pole (TT:3164). -/
theorem wp_mob_hasDerivAt (g : SL2C) {z : ℂ} (hD : g 1 0 * z + g 1 1 ≠ 0) :
    HasDerivAt (mob g) (1 / (g 1 0 * z + g 1 1) ^ 2) z := by
  have h := (((hasDerivAt_id z).const_mul (g 0 0)).add_const (g 0 1)).div
    (((hasDerivAt_id z).const_mul (g 1 0)).add_const (g 1 1)) hD
  convert h using 1
  · rfl
  · congr 1
    linear_combination -(fd_det g)

/-- Hyperbolic area is preserved by a Fuchsian Möbius map away from its pole (TT:3164). -/
theorem wp_mob_rho_cov {g : SL2C} (hg : IsSU11 g) {z : ℂ} (hz : z ∈ unitDiscExterior)
    (hD : g 1 0 * z + g 1 1 ≠ 0) :
    ‖deriv (mob g) z‖ ^ 2 * rho (mob g z) = rho z := by
  have h := fd_mob_norm hg hz hD
  have hd : ‖g 1 0 * z + g 1 1‖ ≠ 0 := norm_ne_zero_iff.mpr hD
  have hz1 : 1 - ‖z‖ ^ 2 ≠ 0 := by have : 1 < ‖z‖ := hz; nlinarith
  have he : 1 - ‖mob g z‖ ^ 2 = (1 - ‖z‖ ^ 2) / ‖g 1 0 * z + g 1 1‖ ^ 2 := by
    linear_combination -h
  rw [(wp_mob_hasDerivAt g hD).deriv]
  simp only [norm_div, norm_one, norm_pow, rho, he]
  field_simp

/-- The totalized Möbius pole is negligible for exterior area integration (TT:3164). -/
theorem wp_mob_denom_ae (g : SL2C) :
    ∀ᵐ z ∂(volume.restrict unitDiscExterior), g 1 0 * z + g 1 1 ≠ 0 := by
  have h : ∀ᵐ z : ℂ, z ∉ {z : ℂ | g 1 0 * z + g 1 1 = 0} :=
    measure_eq_zero_iff_ae_notMem.mp ((fd_denom_finite g).measure_zero volume)
  exact ae_restrict_of_ae h

/-- Unfolding an invariant nonnegative density gives a sum of equal tile masses (TT:3164). -/
theorem wp_fd_unfold_invariant {Γ : Subgroup SL2C} (hΓ : IsFuchsian Γ)
    (ψ : ℂ → ℝ≥0∞)
    (hψ : ∀ g ∈ Γ, ∀ᵐ z ∂(volume.restrict unitDiscExterior),
      ENNReal.ofReal (‖deriv (mob g) z‖ ^ 2) * ψ (mob g z) = ψ z) :
    ∫⁻ z in unitDiscExterior, ψ z =
      ∑' _a : (fun g : SL2C => mob g) '' (Γ : Set SL2C), ∫⁻ z in fundDomain Γ, ψ z := by
  have hF := isFundDomain_fundDomain hΓ
  rw [fd_unfold hΓ hF ψ]
  apply tsum_congr
  rintro ⟨_, g, hg, rfl⟩
  exact lintegral_congr_ae (ae_restrict_of_ae_restrict_of_subset hF.2.1 (hψ g hg))

/-- The hyperbolic density is invariant almost everywhere under each group element (TT:3164). -/
theorem wp_rho_gamma_ae {g : SL2C} (hg : IsSU11 g) :
    ∀ᵐ z ∂(volume.restrict unitDiscExterior),
      ENNReal.ofReal (‖deriv (mob g) z‖ ^ 2) * ENNReal.ofReal (rho (mob g z)) =
        ENNReal.ofReal (rho z) := by
  filter_upwards [wp_mob_denom_ae g, ae_restrict_mem wp_exterior_isOpen.measurableSet] with z hd hz
  rw [← ENNReal.ofReal_mul (sq_nonneg _), wp_mob_rho_cov hg hz hd]


/-- The full exterior has infinite hyperbolic area (TT:3164). -/
theorem wp_exterior_hypArea_top :
    (∫⁻ z in unitDiscExterior, ENNReal.ofReal (rho z)) = ∞ := by
  by_contra htop
  have hi : IntegrableOn rho unitDiscExterior := by
    have hm : Measurable rho := by unfold rho; fun_prop
    refine ⟨hm.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_norm]
    simpa only [Real.norm_eq_abs, abs_of_nonneg (wp_rho_nonneg _)] using
      (lt_top_iff_ne_top.mpr htop)
  have hpunct : IntegrableOn rho (unitDisc \ {0}) := by
    have hc := inversion_puncturedDisk_conformal
    have hopen : IsOpen (unitDisc \ {0}) := isOpen_ball.sdiff isClosed_singleton
    have ht := (ahP_integrableOn_image hopen hc.1 hc.2.1 rho)
    rw [hc.2.2] at ht
    apply (ht.mp hi).congr
    filter_upwards [ae_restrict_mem hopen.measurableSet] with z hz
    simpa only [smul_eq_mul, mul_comm] using rho_inv_jacobian hz.2
  have hdisk : IntegrableOn rho unitDisc :=
    (integrableOn_congr_set_ae (sdiff_null_ae_eq_self (measure_singleton (0 : ℂ)))).mp hpunct
  have he := (tendsto_atTop.1 hypAreaDiscR_tendsto) ((∫ z in unitDisc, rho z) + 1)
  obtain ⟨r, hr, hlt⟩ := (he.and self_mem_nhdsWithin).exists
  have hb : hypAreaDiscR r ≤ ∫ z in unitDisc, rho z := by
    apply setIntegral_mono_set hdisk (ae_of_all _ (fun z => wp_rho_nonneg z))
    exact ae_of_all _ (fun z hz => (mem_ball_zero_iff.mpr
      ((mem_closedBall_zero_iff.mp hz).trans_lt hlt)))
  linarith

/-- A cofinite Fuchsian group has infinitely many distinct Möbius actions (TT:3164). -/
theorem wp_cofinite_actions_infinite {Γ : Subgroup SL2C} (hΓ : IsCofinite Γ) :
    Infinite ((fun g : SL2C => mob g) '' (Γ : Set SL2C)) := by
  by_contra h
  haveI : Finite ((fun g : SL2C => mob g) '' (Γ : Set SL2C)) := not_infinite_iff_finite.mp h
  have he := wp_fd_unfold_invariant hΓ.1 (fun z => ENNReal.ofReal (rho z))
    (fun g hg => wp_rho_gamma_ae (hΓ.1.1 g hg))
  have ht : (∑' _a : (fun g : SL2C => mob g) '' (Γ : Set SL2C), hypArea Γ) < ∞ := by
    letI := Fintype.ofFinite ((fun g : SL2C => mob g) '' (Γ : Set SL2C))
    rw [tsum_fintype]
    exact ENNReal.sum_lt_top.2 (fun _ _ => hΓ.2)
  rw [wp_exterior_hypArea_top] at he
  exact (ne_of_lt ht) he.symm


/-- The weighted L2 energy of an invariant Beltrami differential has equal mass on every tile (TT:3164). -/
theorem wp_gamma_energy_ae {Γ : Subgroup SL2C} (hΓ : IsFuchsian Γ) {μ : LinfStar}
    (hμ : μ ∈ LinfGamma Γ) {g : SL2C} (hg : g ∈ Γ) :
    ∀ᵐ z ∂(volume.restrict unitDiscExterior),
      ENNReal.ofReal (‖deriv (mob g) z‖ ^ 2) *
        ((‖μ (mob g z)‖₊ : ℝ≥0∞) ^ 2 * ENNReal.ofReal (rho (mob g z))) =
      (‖μ z‖₊ : ℝ≥0∞) ^ 2 * ENNReal.ofReal (rho z) := by
  filter_upwards [hμ g hg, wp_mob_denom_ae g, wp_rho_gamma_ae (hΓ.1 g hg)] with z hm hd hr
  have hder : deriv (mob g) z ≠ 0 := by
    rw [(wp_mob_hasDerivAt g hd).deriv]
    exact div_ne_zero one_ne_zero (pow_ne_zero 2 hd)
  have hn : ‖μ (mob g z)‖₊ = ‖μ z‖₊ := by
    apply Subtype.ext
    change ‖μ (mob g z)‖ = ‖μ z‖
    have hh := congrArg norm hm
    simpa only [norm_mul, norm_div, norm_conj, div_self (norm_ne_zero_iff.mpr hder),
      mul_one] using hh
  rw [hn, ← mul_assoc, mul_comm _ ((‖μ z‖₊ : ℝ≥0∞) ^ 2), mul_assoc, hr]

/-- Every invariant finite-L2 Beltrami differential for a cofinite group vanishes (TT:3164). -/
theorem wp_LinfGamma_inter_L2 {Γ : Subgroup SL2C} (hΓ : IsCofinite Γ) {μ : LinfStar}
    (hμ : μ ∈ LinfGamma Γ) (h2 : normL2 unitDiscExterior μ < ∞) : μ = 0 := by
  let ψ : ℂ → ℝ≥0∞ := fun z => (‖μ z‖₊ : ℝ≥0∞) ^ 2 * ENNReal.ofReal (rho z)
  have hfinite : (∫⁻ z in unitDiscExterior, ψ z) < ∞ :=
    (ENNReal.rpow_lt_top_iff_of_pos (by norm_num : (0 : ℝ) < 1 / 2)).mp h2
  have he := wp_fd_unfold_invariant hΓ.1 ψ (fun g hg => wp_gamma_energy_ae hΓ.1 hμ hg)
  haveI := wp_cofinite_actions_infinite hΓ
  have hzero : (∫⁻ z in fundDomain Γ, ψ z) = 0 := by
    by_contra hn
    rw [ENNReal.tsum_const_eq_top_of_ne_zero hn] at he
    exact hfinite.ne he
  have hezero : (∫⁻ z in unitDiscExterior, ψ z) = 0 := by
    rw [he, hzero, tsum_zero]
  have hmeas : AEMeasurable ψ (volume.restrict unitDiscExterior) := by
    dsimp [ψ]
    exact ((Lp.aestronglyMeasurable μ).nnnorm.aemeasurable.coe_nnreal_ennreal.pow_const 2).mul
      (by unfold rho; fun_prop : Measurable (fun z : ℂ => ENNReal.ofReal (rho z))).aemeasurable
  have hz := (lintegral_eq_zero_iff' hmeas).mp hezero
  apply Lp.ext
  filter_upwards [hz, ae_restrict_mem wp_exterior_isOpen.measurableSet,
    Lp.coeFn_zero ℂ ∞ (volume.restrict unitDiscExterior)] with z hzero hz hz0
  rw [hz0]
  have hρ : ENNReal.ofReal (rho z) ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.mpr (wp_rho_pos hz))
  have hn : (‖μ z‖₊ : ℝ≥0∞) ^ 2 = 0 := (mul_eq_zero.mp hzero).resolve_right hρ
  have hc : (‖μ z‖₊ : ℝ≥0∞) = 0 := by simpa only [sq, mul_eq_zero, or_self] using hn
  exact nnnorm_eq_zero.mp (ENNReal.coe_eq_zero.mp hc)

/-- (TT:3164) For a cofinite Fuchsian group, `Ω^{-1,1}(𝔻*, Γ) ∩ H^{-1,1}(𝔻*) = {0}`: a `Γ`-invariant bounded harmonic
Beltrami differential with finite `L²(𝔻*, ρ d²z)` norm vanishes. -/
theorem harmonicGamma_inter_L2 {Γ : Subgroup SL2C} (hΓ : IsCofinite Γ) {μ : LinfStar} (hμ : μ ∈ harmonicGamma Γ)
    (h2 : normL2 unitDiscExterior μ < ∞) : μ = 0 := by
  exact wp_LinfGamma_inter_L2 hΓ hμ.2 h2

-- `petersson_average` moved to `TakhtajanTeo.Ch1.S8Closure` (2026-10-29, Program G).

/-! ### Truncated projections (Lemma 8.1) -/

theorem proj_denominator_lower {ζ z : ℂ} {s : ℝ} (hζ : ‖ζ‖ ≤ s) (hz : ‖z‖ < 1) (hs : s < 1) :
    1 - s ≤ ‖1 - z * conj ζ‖ := by
  have h := norm_sub_norm_le (1 : ℂ) (z * conj ζ)
  have h2 : ‖z * conj ζ‖ ≤ s := by
    rw [norm_mul, Complex.norm_conj]
    have := norm_nonneg ζ
    have := norm_nonneg z
    nlinarith
  simp only [norm_one] at h
  linarith

/-- The antiholomorphic part of the projector is holomorphic in the conjugate variable. -/
theorem proj_integral_differentiableOn {g : ℂ → ℂ} {s C : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (hg : ∀ ζ, ‖g ζ‖ ≤ C) (hsupp : ∀ ζ, s < ‖ζ‖ → g ζ = 0)
    (hm : AEStronglyMeasurable g volume) :
    DifferentiableOn ℂ (fun z : ℂ => ∫ ζ in unitDisc, g ζ / (1 - z * conj ζ) ^ 4) unitDisc := by
  have h1s : 0 < 1 - s := by linarith
  have hC : 0 ≤ C := (norm_nonneg _).trans (hg 0)
  intro z0 hz0
  have hz01 : ‖z0‖ < 1 := mem_ball_zero_iff.mp hz0
  have hmeas : ∀ z : ℂ, AEStronglyMeasurable (fun ζ => g ζ / (1 - z * conj ζ) ^ 4) (volume.restrict unitDisc) := by
    intro z
    exact ((hm.mono_measure Measure.restrict_le_self).aemeasurable.div (by fun_prop : Measurable fun ζ : ℂ => (1 - z * conj ζ) ^ 4).aemeasurable).aestronglyMeasurable
  have hmeas' : ∀ z : ℂ, AEStronglyMeasurable (fun ζ => 4 * conj ζ * g ζ / (1 - z * conj ζ) ^ 5)
      (volume.restrict unitDisc) := by
    intro z
    exact ((((by fun_prop : Continuous fun ζ : ℂ => 4 * conj ζ).aestronglyMeasurable).mul
      (hm.mono_measure Measure.restrict_le_self)).aemeasurable.div
      (by fun_prop : Measurable fun ζ : ℂ => (1 - z * conj ζ) ^ 5).aemeasurable).aestronglyMeasurable
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume.restrict unitDisc)
    (F := fun z ζ => g ζ / (1 - z * conj ζ) ^ 4)
    (F' := fun z ζ => 4 * conj ζ * g ζ / (1 - z * conj ζ) ^ 5) (x₀ := z0)
    (bound := fun _ => 4 * C / (1 - s) ^ 5) (s := ball (0 : ℂ) 1)
    (isOpen_ball.mem_nhds hz0) (Eventually.of_forall hmeas) ?_ (hmeas' z0) ?_ ?_ ?_
  · exact key.2.differentiableAt.differentiableWithinAt
  · refine Integrable.mono' (g := fun _ => C / (1 - s) ^ 4) ?_ (hmeas z0) ?_
    · exact integrableOn_const (measure_ball_lt_top).ne (by simp)
    · filter_upwards with ζ
      by_cases h : s < ‖ζ‖
      · simp [hsupp ζ h]; positivity
      · replace h := not_lt.mp h
        have hl := proj_denominator_lower h hz01 hs1
        rw [norm_div, norm_pow]
        exact div_le_div₀ hC (hg ζ) (by positivity) (pow_le_pow_left₀ h1s.le hl 4)
  · filter_upwards with ζ z hz
    have hz1 : ‖z‖ < 1 := mem_ball_zero_iff.mp hz
    by_cases h : s < ‖ζ‖
    · simp [hsupp ζ h]; positivity
    · replace h := not_lt.mp h
      have hl := proj_denominator_lower h hz1 hs1
      have hnum : ‖4 * conj ζ * g ζ‖ ≤ 4 * C := by
        rw [norm_mul, norm_mul, Complex.norm_conj]
        have : ‖ζ‖ ≤ 1 := by linarith
        have h4 : ‖(4 : ℂ)‖ = 4 := by simp
        rw [h4]
        nlinarith [norm_nonneg ζ, norm_nonneg (g ζ), hg ζ]
      rw [norm_div, norm_pow]
      exact div_le_div₀ (by positivity) hnum (by positivity) (pow_le_pow_left₀ h1s.le hl 5)
  · exact integrableOn_const (measure_ball_lt_top).ne (by simp)
  · filter_upwards with ζ z hz
    have hz1 : ‖z‖ < 1 := mem_ball_zero_iff.mp hz
    by_cases h : s < ‖ζ‖
    · simp [hsupp ζ h]
      exact hasDerivAt_const z 0
    · replace h := not_lt.mp h
      have hl := proj_denominator_lower h hz1 hs1
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

theorem harmonicD_continuousOn {μ : ℂ → ℂ} (hμ : IsHarmonicD μ) : ContinuousOn μ unitDisc := by
  obtain ⟨φ, hφ, _, hμφ⟩ := hμ
  have : ContinuousOn (fun z : ℂ => (1 - ‖z‖ ^ 2) ^ 2 * conj (φ z)) unitDisc :=
    (((continuous_const.sub ((Complex.continuous_ofReal.comp continuous_norm).pow 2)).pow 2).continuousOn).mul
      (Complex.continuous_conj.comp_continuousOn hφ.continuousOn)
  exact this.congr (fun z hz => hμφ z hz)

theorem truncR_aestronglyMeasurable {μ : ℂ → ℂ} (hμ : IsHarmonicD μ) {r : ℝ} (hr : r < 1) :
    AEStronglyMeasurable (truncR r μ) volume := by
  have hsub : closedDiscR r ⊆ unitDisc := fun z hz => by
    have := mem_closedBall_zero_iff.mp hz
    exact mem_ball_zero_iff.mpr (by linarith)
  exact (aestronglyMeasurable_indicator_iff measurableSet_closedBall).mpr
    (((harmonicD_continuousOn hμ).mono hsub).aestronglyMeasurable measurableSet_closedBall)

theorem truncR_support {μ : ℂ → ℂ} {r : ℝ} : ∀ ζ : ℂ, r < ‖ζ‖ → truncR r μ ζ = 0 := by
  intro ζ h
  have : ζ ∉ closedDiscR r := by simpa [closedDiscR, not_le] using h
  simp [truncR, this]

theorem closedDiscR_subset {r : ℝ} (hr : r < 1) : closedDiscR r ⊆ unitDisc := fun z hz => by
  have := mem_closedBall_zero_iff.mp hz
  exact mem_ball_zero_iff.mpr (by linarith)

theorem harmonicProjD_trunc_repr {μ : ℂ → ℂ} {r : ℝ} {z : ℂ} (hz : z ∈ unitDisc) :
    harmonicProjD (truncR r μ) z = (rho z : ℂ)⁻¹ *
      conj ((12 / π : ℂ) * ∫ ζ in unitDisc, conj (truncR r μ ζ) / (1 - z * conj ζ) ^ 4) := by
  have hz1 : ‖z‖ < 1 := mem_ball_zero_iff.mp hz
  have hs : (1 : ℂ) - (‖z‖ : ℂ) ^ 2 ≠ 0 := by
    have : (1 : ℝ) - ‖z‖ ^ 2 ≠ 0 := by nlinarith [norm_nonneg z]
    exact_mod_cast this
  have hI : conj (∫ ζ in unitDisc, conj (truncR r μ ζ) / (1 - z * conj ζ) ^ 4) =
      ∫ ζ in unitDisc, truncR r μ ζ / (1 - ζ * conj z) ^ 4 := by
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
  generalize (∫ ζ in unitDisc, truncR r μ ζ / (1 - ζ * conj z) ^ 4) = J
  field_simp
  ring

theorem harmonicProjD_trunc_mem {μ : ℂ → ℂ} (hμ : IsHarmonicD μ) {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    harmonicProjD (truncR r μ) ∈ harmonicL2 unitDisc ∧
      ∃ C : ℝ, ∀ z ∈ unitDisc, ‖harmonicProjD (truncR r μ) z‖ ≤ C * (1 - ‖z‖ ^ 2) ^ 2 := by
  obtain ⟨Cμ, hCμ⟩ := harmonicD_bound hμ
  have hC0 : 0 ≤ Cμ := (norm_nonneg _).trans (hCμ 0 (by simp [unitDisc]))
  have hbd : ∀ z ∈ unitDisc, ‖harmonicProjD (truncR r μ) z‖ ≤
      3 * Cμ / (1 - r) ^ 4 * (1 - ‖z‖ ^ 2) ^ 2 := fun z hz =>
    harmonicProjD_trunc_norm_le hr0 hr1 hCμ (mem_ball_zero_iff.mp hz)
  refine ⟨⟨fun z => (12 / π : ℂ) * ∫ ζ in unitDisc, conj (truncR r μ ζ) / (1 - z * conj ζ) ^ 4, ?_,
    fun z hz => harmonicProjD_trunc_repr hz, ?_⟩, ⟨_, hbd⟩⟩
  · refine (proj_integral_differentiableOn (g := fun ζ => conj (truncR r μ ζ)) (C := Cμ) hr0 hr1 ?_ ?_ ?_).const_mul _
    · intro ζ
      rw [Complex.norm_conj]
      by_cases h : ζ ∈ unitDisc
      · exact truncR_norm_le r hCμ ζ h
      · have : ζ ∉ closedDiscR r := fun hin => h (closedDiscR_subset hr1 hin)
        simp [truncR, this, hC0]
    · intro ζ h
      simp [truncR_support ζ h]
    · exact (Complex.continuous_conj.comp_aestronglyMeasurable (truncR_aestronglyMeasurable hμ hr1))
  · unfold normL2
    refine ENNReal.rpow_lt_top_of_nonneg (by norm_num) ?_
    set K : ℝ := 3 * Cμ / (1 - r) ^ 4 with hK
    have hpt : ∀ z ∈ unitDisc, (‖harmonicProjD (truncR r μ) z‖₊ : ℝ≥0∞) ^ 2 * ENNReal.ofReal (rho z) ≤
        ENNReal.ofReal (4 * K ^ 2) := by
      intro z hz
      have hz1 : ‖z‖ < 1 := mem_ball_zero_iff.mp hz
      have hs : 0 < 1 - ‖z‖ ^ 2 := by nlinarith [norm_nonneg z]
      have hs1 : 1 - ‖z‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg z]
      have h1 := hbd z hz
      have e : (‖harmonicProjD (truncR r μ) z‖₊ : ℝ≥0∞) ^ 2 * ENNReal.ofReal (rho z) =
          ENNReal.ofReal (‖harmonicProjD (truncR r μ) z‖ ^ 2 * rho z) := by
        rw [ENNReal.ofReal_mul (sq_nonneg _), ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm_eq_enorm]
        rfl
      rw [e]
      apply ENNReal.ofReal_le_ofReal
      have hK0 : 0 ≤ K := by positivity
      calc ‖harmonicProjD (truncR r μ) z‖ ^ 2 * rho z
          ≤ (K * (1 - ‖z‖ ^ 2) ^ 2) ^ 2 * (4 / (1 - ‖z‖ ^ 2) ^ 2) := by
            apply mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) h1 2) (by simp [rho]) (by simp [rho]; positivity) (by positivity)
        _ = 4 * K ^ 2 * (1 - ‖z‖ ^ 2) ^ 2 := by field_simp
        _ ≤ 4 * K ^ 2 := by
            have : (1 - ‖z‖ ^ 2) ^ 2 ≤ 1 := pow_le_one₀ hs.le hs1
            nlinarith [sq_nonneg K]
    apply LT.lt.ne
    calc ∫⁻ z in unitDisc, (‖harmonicProjD (truncR r μ) z‖₊ : ℝ≥0∞) ^ 2 * ENNReal.ofReal (rho z)
        ≤ ∫⁻ _z in unitDisc, ENNReal.ofReal (4 * K ^ 2) :=
          setLIntegral_mono' measurableSet_ball hpt
      _ = ENNReal.ofReal (4 * K ^ 2) * volume unitDisc := setLIntegral_const _ _
      _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top (by simp [unitDisc, measure_ball_lt_top])

/-- Weighted Bergman reproduction for the projector: `P μ = μ` for `μ ∈ Ω^{-1,1}(𝔻)`. -/
theorem harmonicProjD_self {μ : ℂ → ℂ} (hμ : IsHarmonicD μ) {z : ℂ} (hz : z ∈ unitDisc) :
    harmonicProjD μ z = μ z := by
  obtain ⟨φ, hφ, ⟨C, hC⟩, hμφ⟩ := hμ
  have hz1 : ‖z‖ < 1 := mem_ball_zero_iff.mp hz
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0 (by simp [unitDisc]))
  have hb : ∀ w ∈ unitDisc, ‖φ w * ((rho w)⁻¹ : ℝ)‖ ≤ C := by
    intro w hw
    have e : φ w * (((rho w)⁻¹ : ℝ) : ℂ) = ((1 - (‖w‖ : ℂ) ^ 2) ^ 2 * φ w) / 4 := by
      simp only [rho, inv_div]; push_cast; ring
    rw [e, norm_div]
    have h4 : ‖(4 : ℂ)‖ = 4 := by simp
    rw [h4]
    have := hC w hw
    linarith
  have hR := wp_bergman_reproduce hφ hb hz
  have hint : (∫ ζ in unitDisc, μ ζ / (1 - ζ * conj z) ^ 4) =
      conj (4 * ∫ ζ in unitDisc, φ ζ * ((rho ζ)⁻¹ : ℝ) / (1 - z * conj ζ) ^ 4) := by
    rw [← integral_const_mul, ← integral_conj]
    apply setIntegral_congr_fun (show MeasurableSet unitDisc from measurableSet_ball)
    intro ζ hζ
    simp only [map_div₀, map_pow, map_sub, map_one, map_mul, Complex.conj_conj, hμφ ζ hζ]
    rw [mul_comm (conj z) ζ]
    simp only [rho, inv_div]
    push_cast
    simp only [map_div₀, map_pow, map_sub, map_one, map_mul, Complex.conj_ofReal, map_ofNat,
      Complex.conj_conj]
    ring
  unfold harmonicProjD
  rw [hint, hR, hμφ z hz]
  simp only [Complex.real_smul, map_mul]
  push_cast
  simp only [map_mul, map_one, map_ofNat, Complex.conj_ofReal, map_div₀]
  have hs : (1 : ℂ) - (‖z‖ : ℂ) ^ 2 ≠ 0 := by
    have : (1 : ℝ) - ‖z‖ ^ 2 ≠ 0 := by nlinarith [norm_nonneg z, mem_ball_zero_iff.mp hz]
    exact_mod_cast this
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  field_simp
  ring

theorem harmonicProjD_trunc_tendsto {μ : ℂ → ℂ} (hμ : IsHarmonicD μ) {z : ℂ} (hz : z ∈ unitDisc) :
    Tendsto (fun r : ℝ => harmonicProjD (truncR r μ) z) (𝓝[<] 1) (𝓝 (μ z)) := by
  obtain ⟨Cμ, hCμ⟩ := harmonicD_bound hμ
  have hz1 : ‖z‖ < 1 := mem_ball_zero_iff.mp hz
  rw [← harmonicProjD_self hμ hz]
  unfold harmonicProjD
  refine Tendsto.const_mul _ ?_
  refine tendsto_integral_filter_of_dominated_convergence
    (fun ζ => Cμ * ‖(1 - ζ * conj z) ^ 4‖⁻¹) ?_ ?_ ?_ ?_
  · filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with r hr
    exact (((truncR_aestronglyMeasurable hμ hr.2).mono_measure Measure.restrict_le_self).aemeasurable.div
      (by fun_prop : Measurable fun ζ : ℂ => (1 - ζ * conj z) ^ 4).aemeasurable).aestronglyMeasurable
  · refine Eventually.of_forall fun r => ?_
    refine (ae_restrict_iff' (show MeasurableSet unitDisc from measurableSet_ball)).mpr
      (Eventually.of_forall fun ζ hζ => ?_)
    rw [norm_div, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right (truncR_norm_le r hCμ ζ hζ) (inv_nonneg.mpr (norm_nonneg _))
  · exact (proj_kernel_integrableOn hz1).const_mul Cμ
  · refine (ae_restrict_iff' (show MeasurableSet unitDisc from measurableSet_ball)).mpr
      (Eventually.of_forall fun ζ hζ => ?_)
    have hζ1 : ‖ζ‖ < 1 := mem_ball_zero_iff.mp hζ
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [Ioo_mem_nhdsLT hζ1] with r hr
    have hin : ζ ∈ closedDiscR r := by simpa [closedDiscR] using hr.1.le
    simp [truncR, indicator_of_mem hin]

theorem harmonicProjD_trunc_continuousOn {μ : ℂ → ℂ} (hμ : IsHarmonicD μ) {r : ℝ} (hr0 : 0 < r)
    (hr1 : r < 1) : ContinuousOn (harmonicProjD (truncR r μ)) unitDisc := by
  obtain ⟨φ', hφ', hrep, _⟩ := (harmonicProjD_trunc_mem hμ hr0 hr1).1
  have hρ : ContinuousOn (fun z : ℂ => (rho z : ℂ)⁻¹) unitDisc :=
    resolvent_rho_continuousOn.inv₀ (fun z hz => Complex.ofReal_ne_zero.mpr
      (div_ne_zero (by norm_num) (pow_ne_zero 2 (resolvent_domain_denominator_ne_zero (Or.inl rfl) hz))))
  exact (hρ.mul (Complex.continuous_conj.comp_continuousOn hφ'.continuousOn)).congr hrep

theorem lemma_8_1_limit {μ ν : ℂ → ℂ} (hμ : IsHarmonicD μ) (hνb : ∃ C, ∀ z ∈ unitDisc, ‖ν z‖ ≤ C)
    (hν1 : IntegrableOn (fun z => ν z * rho z) unitDisc) :
    Tendsto (fun r : ℝ => l2InnerD (harmonicProjD (truncR r μ)) ν) (𝓝[<] 1) (𝓝 (l2InnerD μ ν)) := by
  obtain ⟨Cμ, hCμ⟩ := harmonicD_bound hμ
  unfold l2InnerD
  refine tendsto_integral_filter_of_dominated_convergence
    (fun z => 3 * Cμ * ‖ν z * (rho z : ℂ)‖) ?_ ?_ ?_ ?_
  · filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with r hr
    have h1 := (harmonicProjD_trunc_continuousOn hμ hr.1 hr.2).aestronglyMeasurable (μ := volume)
      (show MeasurableSet unitDisc from measurableSet_ball)
    have h2 := Complex.continuous_conj.comp_aestronglyMeasurable hν1.1
    have := h1.mul h2
    refine this.congr ?_
    filter_upwards with z
    simp [map_mul, mul_assoc]
  · refine Eventually.of_forall fun r => ?_
    refine (ae_restrict_iff' (show MeasurableSet unitDisc from measurableSet_ball)).mpr
      (Eventually.of_forall fun z hz => ?_)
    have hP := harmonicProjD_norm_le (truncR_norm_le r hCμ) (mem_ball_zero_iff.mp hz)
    have e : harmonicProjD (truncR r μ) z * conj (ν z) * (rho z : ℂ) =
        harmonicProjD (truncR r μ) z * conj (ν z * (rho z : ℂ)) := by
      simp [map_mul, mul_assoc]
    rw [e, norm_mul, Complex.norm_conj]
    exact mul_le_mul_of_nonneg_right hP (norm_nonneg _)
  · exact hν1.norm.const_mul _
  · refine (ae_restrict_iff' (show MeasurableSet unitDisc from measurableSet_ball)).mpr
      (Eventually.of_forall fun z hz => ?_)
    exact ((harmonicProjD_trunc_tendsto hμ hz).mul_const _).mul_const _

/-- **Lemma 8.1** (TT:3188–3200). Let `μ ∈ Ω^{-1,1}(𝔻)`, and let `ν` be bounded with `∬_𝔻 |ν| ρ < ∞`.
- (i) For `0 < r < 1`, `P(μ_r) ∈ H^{-1,1}(𝔻)`, and `P(μ_r)(z) = O((1 - |z|²)²)` as `|z| → 1`.
- (ii) `lim_{r → 1⁻} ∬_𝔻 P(μ_r) ν̄ ρ d²z = ∬_𝔻 μ ν̄ ρ d²z`. -/
theorem lemma_8_1 {μ ν : ℂ → ℂ} (hμ : IsHarmonicD μ) (hνb : ∃ C, ∀ z ∈ unitDisc, ‖ν z‖ ≤ C)
    (hν1 : IntegrableOn (fun z => ν z * rho z) unitDisc) :
    (∀ r : ℝ, 0 < r → r < 1 → harmonicProjD (truncR r μ) ∈ harmonicL2 unitDisc ∧
      ∃ C, ∀ z ∈ unitDisc, ‖harmonicProjD (truncR r μ) z‖ ≤ C * (1 - ‖z‖ ^ 2) ^ 2) ∧
      Tendsto (fun r : ℝ => l2InnerD (harmonicProjD (truncR r μ)) ν) (𝓝[<] 1) (𝓝 (l2InnerD μ ν)) := by
  exact ⟨fun r hr0 hr1 => harmonicProjD_trunc_mem hμ hr0 hr1, lemma_8_1_limit hμ hνb hν1⟩

-- `lemma_8_2` moved to `TakhtajanTeo.Ch1.S8Closure` (2026-10-29, Program G).

/-- **Remark 8.3** (TT:3280). The limits in Lemma 8.2 cannot be interchanged: for fixed `s < 1`, the limit as
`r → 1⁻` is `0`. -/
theorem remark_8_3 {Γ : Subgroup SL2C} (hΓ : IsCofinite Γ) {μ ν : ℂ → ℂ} (hμ : IsHarmonicD μ) (hν : IsHarmonicD ν)
    (hμΓ : IsGammaInvD Γ μ) (hνΓ : IsGammaInvD Γ ν) {s : ℝ} (hs0 : 0 < s) (hs : s < 1) :
    Tendsto (fun r : ℝ => (hypAreaD Γ / hypAreaDiscR r : ℂ) *
        l2InnerD (harmonicProjD (truncR s μ)) (harmonicProjD (truncR r ν))) (𝓝[<] 1) (𝓝 0) := by
  obtain ⟨Cμ, hCμ⟩ := harmonicD_bound hμ
  obtain ⟨Cν, hCν⟩ := harmonicD_bound hν
  set M : ℝ := 4 * (3 * Cμ / (1 - s) ^ 4) * (3 * Cν) * π with hM
  have hbound : ∀ r : ℝ, ‖l2InnerD (harmonicProjD (truncR s μ)) (harmonicProjD (truncR r ν))‖ ≤ M := by
    intro r
    exact l2InnerD_norm_le (fun z hz => harmonicProjD_trunc_norm_le hs0 hs hCμ (mem_ball_zero_iff.mp hz))
      (fun z hz => harmonicProjD_norm_le (truncR_norm_le r hCν) (mem_ball_zero_iff.mp hz))
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hA := hypAreaDiscR_tendsto
  have hlim : Tendsto (fun r : ℝ => |hypAreaD Γ| * M / hypAreaDiscR r) (𝓝[<] 1) (𝓝 0) :=
    tendsto_const_nhds.div_atTop hA
  refine squeeze_zero' (Eventually.of_forall fun r => norm_nonneg _) ?_ hlim
  filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with r hr
  have hApos : 0 < hypAreaDiscR r := by
    rw [hypAreaDiscR_eq hr.1 hr.2]
    have : 1 < 1 / (1 - r ^ 2) := by
      rw [lt_div_iff₀ (by nlinarith [hr.1, hr.2])]
      nlinarith [hr.1, hr.2]
    have h' : 2 / (1 - r ^ 2) = 2 * (1 / (1 - r ^ 2)) := by ring
    nlinarith [Real.pi_pos]
  rw [norm_mul]
  have hn : ‖(hypAreaD Γ / hypAreaDiscR r : ℂ)‖ = |hypAreaD Γ| / hypAreaDiscR r := by
    rw [show (hypAreaD Γ / hypAreaDiscR r : ℂ) = ((hypAreaD Γ / hypAreaDiscR r : ℝ) : ℂ) by push_cast; rfl,
      Complex.norm_real, Real.norm_eq_abs, abs_div, abs_of_pos hApos]
  rw [hn, mul_div_right_comm]
  exact mul_le_mul_of_nonneg_left (hbound r) (by positivity)

/-- The reflection extension for Beltrami differentials on `𝔻`: `κ` on `𝔻`, `\overline{κ(1/z̄)} z²/z̄²` on `𝔻*`. -/
def extD (κ : ℂ → ℂ) (z : ℂ) : ℂ :=
  if ‖z‖ < 1 then κ z else if 1 < ‖z‖ then conj (κ (refl z)) * z ^ 2 / conj z ^ 2 else 0

/-- `w` is the normalized q.c. map (fixing `0, 1, ∞`) with complex dilatation `m`.
- **[CORRECTION 2026-10-29, Program G]** Formerly `w` was a plane homeomorphism fixing `-1, -i, 1`. For the
  reflection-symmetric `extD κ` that forces `w 0 = 0` as well (uniqueness of the symmetric sphere solution), which fails
  for generic `κ`, so `wD κ` was the junk `id` (下属2). Fixing `0, 1, ∞` gives the symmetric solution preserving `𝔻`; the
  memoir's quantities are invariant under post-composition by `Aut(𝔻)`, so nothing else changes. -/
def IsNormalizedFix (m : ℂ → ℂ) (w : ℂ → ℂ) : Prop :=
  IsQuasiconformal w univ ∧ w '' univ = univ ∧ w 0 = 0 ∧ w 1 = 1 ∧
    ∀ᵐ z, complexDilatation w z = m z

/-- `w_κ` in the model `𝔻` (TT:1322): the normalized solution for `extD κ` (junk `id`). -/
def wD (κ : ℂ → ℂ) : ℂ → ℂ := if h : ∃ w, IsNormalizedFix (extD κ) w then h.choose else id

/-- `R(ν, κ) = ((ν/(1 - |κ|²)) (w_κ)_z/\overline{(w_κ)_z}) ∘ w_κ⁻¹` in the model `𝔻` (1.6). -/
def RnmD (ν κ : ℂ → ℂ) (z : ℂ) : ℂ :=
  (fun u => ν u / (1 - ‖κ u‖ ^ 2) * (dz (wD κ) u / conj (dz (wD κ) u))) (Function.invFun (wD κ) z)

/-- The Weil–Petersson metric near the origin of `T(Γ)` (TT:3285):
`g_{μν̄}(κ) = ∬_{Γ_κ\𝔻} P(R(μ, κ)) \overline{P(R(ν, κ))} ρ d²z`, `Γ_κ = w_κ ∘ Γ ∘ w_κ⁻¹`. The integral is over
`w_κ(F)`, `F` a fundamental domain of `Γ`. -/
def gGamma (Γ : Subgroup SL2C) (μ ν κ : ℂ → ℂ) : ℂ :=
  ∫ z in wD κ '' fundDomainOn Γ unitDisc,
    harmonicProjD (RnmD μ κ) z * conj (harmonicProjD (RnmD ν κ) z) * rho z

-- `lemma_8_4` moved to `TakhtajanTeo.Ch1.S8Closure` (2026-10-29, Program G).

/-- `G_Γ(f)(z) = ∬_{Γ\𝔻} G_Γ(z, u) f(u) ρ(u) d²u`, with `G_Γ` of (1.20). -/
def resolventGammaD (Γ : Subgroup SL2C) (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  quotIntD Γ fun u => (resolventKernelGamma Γ z u : ℂ) * f u * rho u

-- `thm_8_5` moved to `TakhtajanTeo.Ch1.S8Gamma85` (2026-10-29, Program G).

-- `projector_kernel` moved to `Ch1/ProjKernel.lean` (2026-10-28).

/-- The Riemann tensor of `T(Γ)` at the origin (as `riemannR`, for `g_{μν̄}` of `T(Γ)`):
`R_{k l̄ m n̄} = -∂²/∂ε₁∂ε̄₂|₀ g_{k l̄}(ε₁ m + ε₂ n)`. -/
def riemannRGamma (Γ : Subgroup SL2C) (k l m n : ℂ → ℂ) : ℂ :=
  -dz (fun e₁ => dzbar (fun e₂ => gGamma Γ k l (fun z => e₁ * m z + e₂ * n z)) 0) 0

-- `eq_8_1` moved to `TakhtajanTeo.Ch1.S8Gamma85` (2026-10-29, Program G).

/-- (TT:3466–3472) The contribution of the identity element of `Γ` to (8.1), by Theorem 7.11:
`-(3/4π) ∬_𝔻 ∬_{Γ\𝔻} μ(z)\overline{ν(z)} G(z, w) ρ(w)ρ(z) d²w d²z - (12/π) ∬_{Γ\𝔻} ∬_𝔻 μ(z)\overline{ν(w)} G(z, w)/(1 - z w̄)⁴ d²w d²z`
equals `-(13/(12π)) (μ, ν)_Γ`.
- **[CORRECTION 2026-10-26]** The first integral is parenthesized: `∫ z, A z - c * Q` parsed as `∫ z, (A z - c * Q)`,
  integrating the constant second term over `𝔻` (found by 下属1). -/
theorem identity_contribution {Γ : Subgroup SL2C} (hΓ : IsCofinite Γ) {μ ν : ℂ → ℂ} (hμ : IsHarmonicD μ)
    (hν : IsHarmonicD ν) (hμΓ : IsGammaInvD Γ μ) (hνΓ : IsGammaInvD Γ ν) :
    -(3 / (4 * π)) * (∫ z in unitDisc, quotIntD Γ (fun w => μ z * conj (ν z) * resolventKernel z w * rho w * rho z)) -
        (12 / π) * quotIntD Γ (fun z => ∫ w in unitDisc, μ z * conj (ν w) * resolventKernel z w / (1 - z * conj w) ^ 4) =
      -(13 / (12 * π)) * innerGamma Γ μ ν := by
  classical
  by_cases hex : ∃ F, IsFundDomainOn Γ unitDisc F
  · have hF : IsFundDomainOn Γ unitDisc hex.choose := hex.choose_spec
    have hfd : fundDomainOn Γ unitDisc = hex.choose := by
      unfold fundDomainOn; rw [dif_pos hex]
    obtain ⟨φ, hφ, ⟨Cφ, hCφ⟩, hμφ⟩ := hμ
    obtain ⟨ψ, hψ, ⟨Cψ, hCψ⟩, hνψ⟩ := hν
    have hcast : ∀ z : ℂ, (((1 - ‖z‖ ^ 2) ^ 2 : ℝ) : ℂ) = (1 - ‖z‖ ^ 2) ^ 2 := by
      intro z; push_cast; ring
    have h := idc_main hΓ (F := hex.choose) hF hφ (Cφ := Cφ)
      (fun z hz => by rw [hcast]; exact hCφ z hz) hψ (Cψ := Cψ)
      (fun z hz => by rw [hcast]; exact hCψ z hz)
      (fun z hz => by rw [hcast]; exact hμφ z hz) (fun z hz => by rw [hcast]; exact hνψ z hz)
      hμΓ hνΓ
    simp only [quotIntD, innerGamma, hfd]
    exact h
  · -- No disk fundamental domain: `fundDomainOn` is the junk value `∅`, so both sides are `0`.
    have hfd : fundDomainOn Γ unitDisc = ∅ := by
      unfold fundDomainOn; rw [dite_eq_right_iff.mpr (fun h => absurd h hex)]
    simp [quotIntD, innerGamma, hfd]

end TakhtajanTeo
