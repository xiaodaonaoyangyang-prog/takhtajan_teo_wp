import TakhtajanTeo.Appendix.AppACor6
import TakhtajanTeo.Ch2.S3_Variations
import TakhtajanTeo.Ch1.L55
import TakhtajanTeo.Ch2.S3PreSchwarzianKernel

/-!
# Appendix A, Corollary A.4, (i) ⇔ (iii) (`a4_`, 下属2, Program G)

Host of `cor_A_4` (the leader relocates it here with body `a4_cor_A_4 hp hw hq hv`); needs `AppACor6`, which imports
`AppACor4`.

(i) ⇒ (iii) (`a4_i_imp_iii`). Invert the exterior map, `g(1/s) = b/φ(s)` with `φ` normalized on `𝔻`
(`g1_inverted_exterior`, U1–U2).
- U3 `a4_lg_norm`: the (iii) quantity is the inverted pre-Schwarzian of `φ`, isometrically (`preSchwarzian_inversion`).
- U4 `a4_S_norm`: Schwarzian differences are carried isometrically `A₂(𝔻*) → A₂(𝔻)`.
- U5 `a4_inv_pre_A21`: `φ = b (c + g̃_μ ∘ t)` with `t` a disc automorphism (`a4_phi_rep`), so `𝒜φ ∈ A₂¹(𝔻)`.
- U6 `a4_inv_value`: `𝒜φₙ(0) → 𝒜φ(0)` (`a6_weldG_LU`, maximum principle, Weierstrass).
- U7: `a4_inverse` at `φ`, with T1 of Corollary A.6.

(iii) ⇒ (i) (`a4_iii_imp_i`). A *partner* `γ'` of `γ` has circle map `h_{γ'} = h_γ⁻¹` (`a4_sharp_exists`,
`a4_sharp_symm`); its interior map is the reflection of `φ_γ` (`a4_sharp_betaHat`: welding uniqueness for the pair
`(A ∘ f_{μ⁻¹} ∘ R⁻¹, A ∘ g_{μ⁻¹})`, `a4_tbar`, `s3pk_gTilde_pair`). Then (iii)_γₙ ⇒ (ii)_{γ'ₙ} ⇒ (i)_{γ'ₙ} ⇒
(iii)_{γ'ₙ} (`a4_i_imp_iii`) ⇒ (ii)_γₙ ⇒ (i)_γₙ.
-/

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal NNReal ComplexConjugate Classical Real

noncomputable section

namespace TakhtajanTeo

open LiZhongQC Ch2

namespace AppA

/-- **U1.** The fibre welding `(weldF, weldG)` is a normalized disjoint pair. -/
theorem a4_weld_pair {μ : LinfStar} (hμ : μ ∈ LinfStarBall) {w : ℂ} (hw : w ∈ unitDiscExterior) :
    IsNormalizedDisjointPair (weldF μ w) (weldG μ w) := by
  have hFW := fiber_welding hμ hw
  dsimp only at hFW
  obtain ⟨hOF, hWP, -⟩ := hFW
  exact (l55_disjoint_pair hOF hWP).1

/-- **U2.** The normalized inverted exterior map `φ`, with `weldG(1/s) = b/φ(s)`. -/
theorem a4_inv_data {μ : LinfStar} (hμ : μ ∈ LinfStarBall) {w : ℂ} (hw : w ∈ unitDiscExterior) :
    ∃ φ : ℂ → ℂ, ∃ b : ℂ, DifferentiableOn ℂ φ unitDisc ∧ (∀ s ∈ unitDisc, deriv φ s ≠ 0) ∧ φ 0 = 0 ∧
      deriv φ 0 = 1 ∧ b ≠ 0 ∧ ∀ s ∈ unitDisc, s ≠ 0 → weldG μ w (1 / s) = b / φ s := by
  obtain ⟨φ, b, hφd, hφi, hφ0, hφ1, hb, -, he⟩ := g1_inverted_exterior (a4_weld_pair hμ hw)
  exact ⟨φ, b, hφd, fun s hs => LiZhongQC.deriv_ne_zero_of_injOn isOpen_ball hφd hφi hs, hφ0, hφ1, hb, he⟩

theorem a4_inv_mem {z : ℂ} (hz : z ∈ unitDiscExterior) : z⁻¹ ∈ unitDisc \ {0} := by
  have hz1 : 1 < ‖z‖ := hz
  have hz0 : z ≠ 0 := by rintro rfl; simp at hz1; linarith
  exact ⟨mem_ball_zero_iff.2 (by rw [norm_inv]; exact inv_lt_one_of_one_lt₀ hz1), inv_ne_zero hz0⟩

theorem a4_one_div_mem {x : ℂ} (hx : x ∈ unitDisc \ {0}) : 1 / x ∈ unitDiscExterior := by
  show 1 < ‖1 / x‖
  have hx1 := mem_ball_zero_iff.mp hx.1
  rw [norm_div, norm_one, lt_div_iff₀ (norm_pos_iff.2 hx.2)]
  linarith

/-- `φ = b / g ∘ (1/·)` on the punctured disc. -/
theorem a4_phi_eq {g φ : ℂ → ℂ} {b : ℂ} (h0 : ∀ z ∈ unitDiscExterior, g z ≠ 0) (hb : b ≠ 0)
    (he : ∀ s ∈ unitDisc, s ≠ 0 → g (1 / s) = b / φ s) {x : ℂ} (hx : x ∈ unitDisc \ {0}) :
    φ x = b / g x⁻¹ := by
  have h := he x hx.1 hx.2
  have hne : φ x ≠ 0 := by
    intro h'
    rw [h', div_zero] at h
    exact h0 _ (a4_one_div_mem hx) h
  rw [← one_div, h]
  field_simp

/-- Pointwise inversion of the (iii) quantity. -/
theorem a4_lg_pt {g φ : ℂ → ℂ} {b : ℂ} (hg : IsUnivalentAtInfty g) (h0 : ∀ z ∈ unitDiscExterior, g z ≠ 0)
    (hb : b ≠ 0) (he : ∀ s ∈ unitDisc, s ≠ 0 → g (1 / s) = b / φ s) {z : ℂ} (hz : z ∈ unitDiscExterior) :
    preSchwarzian φ z⁻¹ * (-1 / z ^ 2) = preSchwarzian g z - 2 * deriv g z / g z + 2 / z := by
  have hU := a6_ext_open
  have hzi := a4_inv_mem hz
  have hz0 : z ≠ 0 := fun h => hzi.2 (by rw [h, inv_zero]; rfl)
  have hF : preSchwarzian (fun w => (g w⁻¹)⁻¹) z⁻¹ = preSchwarzian φ z⁻¹ := by
    rw [s2c_pre_congr (f := fun w => (g w⁻¹)⁻¹) (g := fun x => b⁻¹ * φ x) ?_
      (isOpen_ball.sdiff isClosed_singleton) hzi, s2c_pre_const_mul (inv_ne_zero hb)]
    intro x hx
    show (g x⁻¹)⁻¹ = b⁻¹ * φ x
    rw [a4_phi_eq h0 hb he hx]
    have hgx : g x⁻¹ ≠ 0 := by
      have := h0 _ (a4_one_div_mem hx)
      rwa [one_div] at this
    field_simp
  rw [← hF]
  exact preSchwarzian_inversion (hg.1.analyticAt (hU.mem_nhds hz)) hz0 (h0 z hz)
    (LiZhongQC.deriv_ne_zero_of_injOn hU hg.1 hg.2.1 hz)

/-- Pointwise inversion of the Schwarzian. -/
theorem a4_S_pt {g φ : ℂ → ℂ} {b : ℂ} (hg : IsUnivalentAtInfty g) (h0 : ∀ z ∈ unitDiscExterior, g z ≠ 0)
    (hb : b ≠ 0) (he : ∀ s ∈ unitDisc, s ≠ 0 → g (1 / s) = b / φ s) {z : ℂ} (hz : z ∈ unitDiscExterior) :
    schwarzianHol φ z⁻¹ = schwarzianHol g z * (z ^ 2) ^ 2 := by
  have hU := a6_ext_open
  have hzi := a4_inv_mem hz
  have hz0 : z ≠ 0 := fun h => hzi.2 (by rw [h, inv_zero]; rfl)
  set s : ℂ → ℂ := fun v => (0 * v + 1) / (1 * v + 0) with hs
  have hsz : s z⁻¹ = z := by simp [hs]
  have hN : (1 : ℂ) * z⁻¹ + 0 ≠ 0 := by simpa using hzi.2
  have hsd := hasDerivAt_mobius (a := 0) (b := 1) hN
  have hsa : AnalyticAt ℂ s z⁻¹ :=
    (by fun_prop : AnalyticAt ℂ (fun v : ℂ => 0 * v + 1) z⁻¹).div
      (by fun_prop : AnalyticAt ℂ (fun v : ℂ => 1 * v + 0) z⁻¹) hN
  have hs' : deriv s z⁻¹ ≠ 0 := by
    rw [hsd.deriv]
    exact div_ne_zero (by norm_num) (pow_ne_zero 2 hN)
  have hga : AnalyticAt ℂ g (s z⁻¹) := by
    rw [hsz]
    exact hg.1.analyticAt (hU.mem_nhds hz)
  have hg' : deriv g (s z⁻¹) ≠ 0 := by
    rw [hsz]
    exact LiZhongQC.deriv_ne_zero_of_injOn hU hg.1 hg.2.1 hz
  have hGa : AnalyticAt ℂ (g ∘ s) z⁻¹ := hga.comp hsa
  have hG' : deriv (g ∘ s) z⁻¹ ≠ 0 := by
    rw [deriv_comp _ hga.differentiableAt hsa.differentiableAt]
    exact mul_ne_zero hg' hs'
  have hev : φ =ᶠ[𝓝 z⁻¹] fun v => (0 * (g ∘ s) v + b) / (1 * (g ∘ s) v + 0) := by
    filter_upwards [(isOpen_ball.sdiff isClosed_singleton).mem_nhds hzi] with v hv
    rw [a4_phi_eq h0 hb he hv]
    simp [hs]
  have hgs : (1 : ℂ) * (g ∘ s) z⁻¹ + 0 ≠ 0 := by
    simpa [Function.comp_apply, hsz] using h0 z hz
  have hMa : AnalyticAt ℂ (fun v => (0 * (g ∘ s) v + b) / (1 * (g ∘ s) v + 0)) z⁻¹ :=
    ((analyticAt_const.mul hGa).add analyticAt_const).div ((analyticAt_const.mul hGa).add analyticAt_const) hgs
  have hφa : AnalyticAt ℂ φ z⁻¹ := hMa.congr hev.symm
  rw [← schwarzian_of_analyticAt hφa, schwarzian_congr (hev.filter_mono nhdsWithin_le_nhds),
    schwarzian_mobius_comp_analytic hGa hG' (by simpa using hb), eq19_1_chain_rule hsa hs' hga hg',
    schwarzian_of_analyticAt hga, schwarzian_of_analyticAt hsa,
    show schwarzianHol s z⁻¹ = 0 from schwarzianHol_mobius (by norm_num) hN, add_zero, hsz, hsd.deriv]
  congr 1
  field_simp
  try ring

theorem a4_rho_inv {z : ℂ} (hz : z ∈ unitDiscExterior) : rho z⁻¹ = ‖z‖ ^ 4 * rho z := by
  have h1 : 1 < ‖z‖ := hz
  have hn : ‖z‖ ≠ 0 := by positivity
  have h2 : 1 - ‖z‖ ^ 2 ≠ 0 := by nlinarith
  have h3 : 1 - ‖z‖⁻¹ ^ 2 = -(1 - ‖z‖ ^ 2) / ‖z‖ ^ 2 := by
    field_simp
    ring
  unfold rho
  rw [norm_inv, h3]
  field_simp
  try ring

/-- **U3.** Inversion carries the (iii) quantity to the pre-Schwarzian of `φ`, isometrically. -/
theorem a4_lg_norm {g₁ g₂ φ₁ φ₂ : ℂ → ℂ} {b₁ b₂ : ℂ} (hg₁ : IsUnivalentAtInfty g₁) (hg₂ : IsUnivalentAtInfty g₂)
    (h0₁ : ∀ z ∈ unitDiscExterior, g₁ z ≠ 0) (h0₂ : ∀ z ∈ unitDiscExterior, g₂ z ≠ 0)
    (hb₁ : b₁ ≠ 0) (hb₂ : b₂ ≠ 0)
    (he₁ : ∀ s ∈ unitDisc, s ≠ 0 → g₁ (1 / s) = b₁ / φ₁ s) (he₂ : ∀ s ∈ unitDisc, s ≠ 0 → g₂ (1 / s) = b₂ / φ₂ s) :
    normA21 unitDiscExterior (fun z =>
        (preSchwarzian g₁ z - 2 * deriv g₁ z / g₁ z + 2 / z) - (preSchwarzian g₂ z - 2 * deriv g₂ z / g₂ z + 2 / z)) =
      normA21 unitDisc (fun s => preSchwarzian φ₁ s - preSchwarzian φ₂ s) := by
  have hU := a6_ext_open
  set ψ : ℂ → ℂ := fun s => preSchwarzian φ₁ s - preSchwarzian φ₂ s with hψ
  have hpull := normA21_pullback hU isConformalOnto_inv_exterior ψ
  rw [← normA21_sdiff_singleton unitDisc ψ 0, ← hpull]
  unfold normA21
  congr 1
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_mem hU.measurableSet] with z hz
  have key : ψ z⁻¹ * deriv (fun w : ℂ => w⁻¹) z =
      (preSchwarzian g₁ z - 2 * deriv g₁ z / g₁ z + 2 / z) - (preSchwarzian g₂ z - 2 * deriv g₂ z / g₂ z + 2 / z) := by
    rw [deriv_inv, ← a4_lg_pt hg₁ h0₁ hb₁ he₁ hz, ← a4_lg_pt hg₂ h0₂ hb₂ he₂ hz]
    simp only [hψ]
    ring
  exact congrArg (fun v : ℂ => (‖v‖₊ : ℝ≥0∞) ^ 2) key.symm

/-- **U4.** Inversion carries Schwarzian differences isometrically, `A₂(𝔻*) → A₂(𝔻)`. -/
theorem a4_S_norm {g₁ g₂ φ₁ φ₂ : ℂ → ℂ} {b₁ b₂ : ℂ} (hg₁ : IsUnivalentAtInfty g₁) (hg₂ : IsUnivalentAtInfty g₂)
    (h0₁ : ∀ z ∈ unitDiscExterior, g₁ z ≠ 0) (h0₂ : ∀ z ∈ unitDiscExterior, g₂ z ≠ 0)
    (hb₁ : b₁ ≠ 0) (hb₂ : b₂ ≠ 0)
    (he₁ : ∀ s ∈ unitDisc, s ≠ 0 → g₁ (1 / s) = b₁ / φ₁ s) (he₂ : ∀ s ∈ unitDisc, s ≠ 0 → g₂ (1 / s) = b₂ / φ₂ s) :
    normA2 unitDiscExterior (fun z => schwarzianHol g₁ z - schwarzianHol g₂ z) =
      normA2 unitDisc (fun s => schwarzianHol φ₁ s - schwarzianHol φ₂ s) := by
  have hU := a6_ext_open
  have hc := isConformalOnto_inv_exterior
  have e1 : ∀ x : ℂ, ((‖x‖₊ : ℝ≥0∞)) ^ 2 = ENNReal.ofReal (‖x‖ ^ 2) := fun x => by
    rw [← enorm_eq_nnnorm, ← ofReal_norm, ENNReal.ofReal_pow (norm_nonneg _)]
  unfold normA2
  congr 1
  calc (∫⁻ z in unitDiscExterior, (‖schwarzianHol g₁ z - schwarzianHol g₂ z‖₊ : ℝ≥0∞) ^ 2 *
        ENNReal.ofReal (rho z)⁻¹)
      = ∫⁻ z in unitDiscExterior, ENNReal.ofReal (‖deriv (fun w : ℂ => w⁻¹) z‖ ^ 2) *
          ((‖schwarzianHol φ₁ z⁻¹ - schwarzianHol φ₂ z⁻¹‖₊ : ℝ≥0∞) ^ 2 * ENNReal.ofReal (rho z⁻¹)⁻¹) := by
        apply setLIntegral_congr_fun hU.measurableSet
        intro z hz
        have hz0 : z ≠ 0 := fun h => (a4_inv_mem hz).2 (by rw [h, inv_zero]; rfl)
        have h1 : 1 < ‖z‖ := hz
        have hr : 0 < rho z := by
          unfold rho
          have : 1 - ‖z‖ ^ 2 ≠ 0 := by nlinarith
          positivity
        have hreal : ‖schwarzianHol g₁ z - schwarzianHol g₂ z‖ ^ 2 * (rho z)⁻¹ =
            ‖-(z ^ 2)⁻¹‖ ^ 2 * (‖(schwarzianHol g₁ z - schwarzianHol g₂ z) * (z ^ 2) ^ 2‖ ^ 2 * (rho z⁻¹)⁻¹) := by
          rw [a4_rho_inv hz]
          simp only [norm_mul, norm_neg, norm_inv, norm_pow]
          have hn : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz0
          field_simp
          try ring
        beta_reduce
        rw [deriv_inv, a4_S_pt hg₁ h0₁ hb₁ he₁ hz, a4_S_pt hg₂ h0₂ hb₂ he₂ hz, ← sub_mul]
        rw [show (‖schwarzianHol g₁ z - schwarzianHol g₂ z‖₊ : ℝ≥0∞) ^ 2 * ENNReal.ofReal (rho z)⁻¹ =
            ENNReal.ofReal (‖schwarzianHol g₁ z - schwarzianHol g₂ z‖ ^ 2 * (rho z)⁻¹) from by
              rw [ENNReal.ofReal_mul (sq_nonneg _), e1],
          show ENNReal.ofReal (‖-(z ^ 2)⁻¹‖ ^ 2) *
              ((‖(schwarzianHol g₁ z - schwarzianHol g₂ z) * (z ^ 2) ^ 2‖₊ : ℝ≥0∞) ^ 2 *
                ENNReal.ofReal (rho z⁻¹)⁻¹) =
            ENNReal.ofReal (‖-(z ^ 2)⁻¹‖ ^ 2 *
              (‖(schwarzianHol g₁ z - schwarzianHol g₂ z) * (z ^ 2) ^ 2‖ ^ 2 * (rho z⁻¹)⁻¹)) from by
              rw [ENNReal.ofReal_mul (sq_nonneg _), ENNReal.ofReal_mul (sq_nonneg _), e1], hreal]
    _ = ∫⁻ u in (fun w : ℂ => w⁻¹) '' unitDiscExterior,
          (‖schwarzianHol φ₁ u - schwarzianHol φ₂ u‖₊ : ℝ≥0∞) ^ 2 * ENNReal.ofReal (rho u)⁻¹ :=
        (r24_conformal_lintegral hU hc.1 hc.2.1
          (fun u => (‖schwarzianHol φ₁ u - schwarzianHol φ₂ u‖₊ : ℝ≥0∞) ^ 2 * ENNReal.ofReal (rho u)⁻¹)).symm
    _ = ∫⁻ u in unitDisc, (‖schwarzianHol φ₁ u - schwarzianHol φ₂ u‖₊ : ℝ≥0∞) ^ 2 * ENNReal.ofReal (rho u)⁻¹ := by
        rw [hc.2.2]
        exact setLIntegral_congr (sdiff_null_ae_eq_self (measure_singleton 0))

theorem a4_pair_ne_zero {f g : ℂ → ℂ} (h : IsNormalizedDisjointPair f g) :
    ∀ z ∈ unitDiscExterior, g z ≠ 0 := by
  intro z hz hgz
  exact Set.disjoint_left.mp h.2.2.2.2.2 ⟨0, mem_ball_self one_pos, h.2.2.1⟩ ⟨z, hz, hgz⟩

/-! #### The disc automorphism `t = j ∘ σ_w⁻¹ ∘ j` -/

theorem a4_t_key {w : ℂ} (s : ℂ) :
    ‖-(1 - w) * s + -w * (1 - conj w)‖ ^ 2 - ‖-(1 - w) * conj w * s + -(1 - conj w)‖ ^ 2 =
      ‖1 - w‖ ^ 2 * (‖w‖ ^ 2 - 1) * (1 - ‖s‖ ^ 2) := by
  obtain ⟨-, hkey⟩ := appa2_sigmaInv_coeffs (w := w)
  have hC : ‖-(1 - conj w)‖ = ‖1 - w‖ := by
    rw [norm_neg, ← Complex.norm_conj]
    simp [map_sub]
  by_cases hs : s = 0
  · subst hs
    have hA : -w * (1 - conj w) = w * -(1 - conj w) := by ring
    simp only [mul_zero, zero_add, norm_zero]
    rw [hA, norm_mul, hC]
    ring
  · have h := hkey s⁻¹
    have e1 : -(1 - w) * s + -w * (1 - conj w) = s * (-w * (1 - conj w) * s⁻¹ + -(1 - w)) := by
      field_simp
      ring
    have e2 : -(1 - w) * conj w * s + -(1 - conj w) = s * (-(1 - conj w) * s⁻¹ + -(1 - w) * conj w) := by
      field_simp
      ring
    have hn : ‖s‖ ≠ 0 := norm_ne_zero_iff.mpr hs
    rw [e1, e2, norm_mul, norm_mul, mul_pow, mul_pow, ← mul_sub, h, norm_inv]
    field_simp
    try ring

theorem a4_t_pole {w : ℂ} (hw : w ∈ unitDiscExterior) {s : ℂ} (hs : ‖s‖ ≤ 1) :
    -(1 - w) * s + -w * (1 - conj w) ≠ 0 := by
  have hw1 : 1 < ‖w‖ := hw
  have hw0 : w ≠ 1 := by rintro rfl; simp at hw1
  have h1 : 0 < ‖1 - w‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (Ne.symm hw0))
  have hC : ‖1 - conj w‖ = ‖1 - w‖ := by
    rw [← Complex.norm_conj]
    simp [map_sub]
  intro h
  have h2 : -w * (1 - conj w) = (1 - w) * s := by linear_combination h
  have h3 := congrArg norm h2
  rw [norm_mul, norm_neg, hC, norm_mul] at h3
  nlinarith [mul_le_mul_of_nonneg_left hs h1.le]

theorem a4_t_disc {w : ℂ} (hw : w ∈ unitDiscExterior) {s : ℂ} (hs : s ∈ unitDisc) :
    (-(1 - w) * conj w * s + -(1 - conj w)) / (-(1 - w) * s + -w * (1 - conj w)) ∈ unitDisc := by
  have hs1 := mem_ball_zero_iff.mp hs
  have hw1 : 1 < ‖w‖ := hw
  have hw0 : w ≠ 1 := by rintro rfl; simp at hw1
  have h1 : 0 < ‖1 - w‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (Ne.symm hw0))
  have hP := a4_t_pole hw hs1.le
  have hk := a4_t_key (w := w) s
  have hpos : 0 < ‖1 - w‖ ^ 2 * (‖w‖ ^ 2 - 1) * (1 - ‖s‖ ^ 2) := by
    have : 1 < ‖w‖ ^ 2 := by nlinarith
    have : ‖s‖ ^ 2 < 1 := by nlinarith [norm_nonneg s]
    have : 0 < ‖1 - w‖ ^ 2 := by positivity
    have : 0 < ‖1 - w‖ ^ 2 * (‖w‖ ^ 2 - 1) := by nlinarith
    nlinarith
  refine mem_ball_zero_iff.mpr ?_
  rw [norm_div, div_lt_one (norm_pos_iff.mpr hP)]
  exact lt_of_pow_lt_pow_left₀ 2 (norm_nonneg _) (by linarith)

theorem a4_t_hasDerivAt {w : ℂ} (hw : w ∈ unitDiscExterior) {s : ℂ} (hs : ‖s‖ ≤ 1) :
    HasDerivAt (fun x => (-(1 - w) * conj w * x + -(1 - conj w)) / (-(1 - w) * x + -w * (1 - conj w)))
      (((-(1 - w) * conj w) * (-w * (1 - conj w)) - (-(1 - conj w)) * (-(1 - w))) /
        (-(1 - w) * s + -w * (1 - conj w)) ^ 2) s :=
  hasDerivAt_mobius (a4_t_pole hw hs)

theorem a4_t_det {w : ℂ} (hw : w ∈ unitDiscExterior) :
    (-(1 - w) * conj w) * (-w * (1 - conj w)) - (-(1 - conj w)) * (-(1 - w)) ≠ 0 := by
  obtain ⟨hdet, -⟩ := appa2_sigmaInv_coeffs (w := w)
  have hw1 : 1 < ‖w‖ := hw
  have hw0 : w ≠ 1 := by rintro rfl; simp at hw1
  have h1 : 0 < ‖1 - w‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (Ne.symm hw0))
  have hκ : 0 < ‖1 - w‖ ^ 2 * (‖w‖ ^ 2 - 1) := by
    have : 1 < ‖w‖ ^ 2 := by nlinarith
    have : 0 < ‖1 - w‖ ^ 2 := by positivity
    nlinarith
  have e : (-(1 - w) * conj w) * (-w * (1 - conj w)) - (-(1 - conj w)) * (-(1 - w)) =
      (-w * (1 - conj w)) * (-(1 - w) * conj w) - (-(1 - w)) * (-(1 - conj w)) := by ring
  rw [e, hdet]
  exact_mod_cast hκ.ne'

theorem a4_mob_pre_A21 {a b c d : ℂ} (hdet : a * d - b * c ≠ 0)
    (hpole : ∀ x ∈ closedBall (0 : ℂ) 1, c * x + d ≠ 0) :
    preSchwarzian (fun x => (a * x + b) / (c * x + d)) ∈ A21fun unitDisc := by
  have hdet' : -(c * b) + a * d ≠ 0 := by
    intro h
    apply hdet
    linear_combination h
  have hEq : EqOn (preSchwarzian (fun x => (a * x + b) / (c * x + d))) (fun x => -(2 * c) / (c * x + d))
      unitDisc := by
    intro x hx
    have hx0 := hpole x (ball_subset_closedBall hx)
    have hopen : IsOpen {v : ℂ | c * v + d ≠ 0} := isOpen_ne_fun (by fun_prop) continuous_const
    have hev : deriv (fun x => (a * x + b) / (c * x + d)) =ᶠ[𝓝 x] fun v => (a * d - b * c) / (c * v + d) ^ 2 := by
      filter_upwards [hopen.mem_nhds hx0] with v hv
      exact (hasDerivAt_mobius hv).deriv
    show deriv (deriv (fun x => (a * x + b) / (c * x + d))) x / deriv (fun x => (a * x + b) / (c * x + d)) x =
      -(2 * c) / (c * x + d)
    rw [hev.deriv_eq, hev.eq_of_nhds, (hasDerivAt_mobius_deriv hx0).deriv]
    have hX := mul_inv_cancel₀ hdet'
    field_simp
    linear_combination (-c) * hX
  have hkc : ContinuousOn (fun x => -(2 * c) / (c * x + d)) (closedBall 0 1) := fun x hx =>
    (continuousAt_const.div (by fun_prop : Continuous fun y : ℂ => c * y + d).continuousAt
      (hpole x hx)).continuousWithinAt
  have hkA : (fun x => -(2 * c) / (c * x + d)) ∈ A21fun unitDisc := by
    apply (mem_A21fun_iff_memLp measurableSet_ball).mpr
    refine ⟨fun x hx => ?_, ?_⟩
    · exact ((differentiableAt_const _).div (by fun_prop : DifferentiableAt ℂ (fun y : ℂ => c * y + d) x)
        (hpole x (ball_subset_closedBall hx))).differentiableWithinAt
    · apply (memLp_two_iff_integrable_sq_norm
        ((hkc.mono ball_subset_closedBall).aestronglyMeasurable measurableSet_ball)).mpr
      exact ((hkc.norm.pow 2).integrableOn_compact (isCompact_closedBall 0 1)).mono_set ball_subset_closedBall
  exact a21_congr_on measurableSet_ball hkA (fun x hx => (hEq hx).symm)

theorem a4_t_pre_A21 {w : ℂ} (hw : w ∈ unitDiscExterior) :
    preSchwarzian (fun x => (-(1 - w) * conj w * x + -(1 - conj w)) / (-(1 - w) * x + -w * (1 - conj w))) ∈
      A21fun unitDisc :=
  a4_mob_pre_A21 (a4_t_det hw) (fun _x hx => a4_t_pole hw (mem_closedBall_zero_iff.mp hx))

/-- `φ = b (c + g̃_μ ∘ t)` on `𝔻`. -/
theorem a4_phi_rep {μ : LinfStar} (hμ : μ ∈ LinfStarBall) {w : ℂ} (hw : w ∈ unitDiscExterior) {φ : ℂ → ℂ} {b : ℂ}
    (hφ : DifferentiableOn ℂ φ unitDisc) (hb : b ≠ 0)
    (he : ∀ s ∈ unitDisc, s ≠ 0 → weldG μ w (1 / s) = b / φ s) :
    EqOn φ (fun s => b * (-1 / gMu μ w + gTilde μ
      ((-(1 - w) * conj w * s + -(1 - conj w)) / (-(1 - w) * s + -w * (1 - conj w))))) unitDisc := by
  set t : ℂ → ℂ := fun s => (-(1 - w) * conj w * s + -(1 - conj w)) / (-(1 - w) * s + -w * (1 - conj w)) with htdef
  set c := -1 / gMu μ w with hcdef
  have hg0 := gMu_exterior_ne_zero hμ hw
  have hc : c ≠ 0 := div_ne_zero (neg_ne_zero.mpr one_ne_zero) hg0
  obtain ⟨bG, -, -, hGd, -, hG0, -⟩ := s2c_gTilde_facts hμ
  have h0 := a4_pair_ne_zero (a4_weld_pair hμ hw)
  have htc : ContinuousOn t unitDisc := fun s hs =>
    ((a4_t_hasDerivAt hw (mem_ball_zero_iff.mp hs).le).continuousAt).continuousWithinAt
  have hR : ContinuousOn (fun s => b * (c + gTilde μ (t s))) unitDisc :=
    continuousOn_const.mul (continuousOn_const.add (hGd.continuousOn.comp htc fun s hs => a4_t_disc hw hs))
  have hpunct : ∀ s ∈ unitDisc, s ≠ 0 → φ s = b * (c + gTilde μ (t s)) := by
    intro s hs hs0
    have hsm : s ∈ unitDisc \ {0} := ⟨hs, hs0⟩
    have hz := a4_one_div_mem hsm
    set z := 1 / s with hzdef
    have hφs : φ s = b / weldG μ w z := by
      rw [a4_phi_eq h0 hb he hsm, hzdef, one_div]
    have hsz : s * z = 1 := by rw [hzdef]; field_simp
    have eN : -(1 - w) * s + -w * (1 - conj w) = s * (-w * (1 - conj w) * z + -(1 - w)) := by
      have hss : s * s⁻¹ = 1 := mul_inv_cancel₀ hs0
      rw [hzdef, one_div]
      linear_combination (w * (1 - conj w)) * hss
    have eD : -(1 - w) * conj w * s + -(1 - conj w) = s * (-(1 - conj w) * z + -(1 - w) * conj w) := by
      have hss : s * s⁻¹ = 1 := mul_inv_cancel₀ hs0
      rw [hzdef, one_div]
      linear_combination (1 - conj w) * hss
    by_cases hCD : -(1 - conj w) * z + -(1 - w) * conj w = 0
    · have hsig : sigmaInvSphere (w : ExtPlane) (z : ExtPlane) = extInf := by
        rw [a6_sigmaInv_eq]
        exact mobiusExt_coe_of_eq_zero hCD
      have hW : weldG μ w z = 1 / c := by
        show finPart (mobiusExt 1 0 c 1 (normalizedWeldingSphere μ (sigmaInvSphere (w : ExtPlane) (z : ExtPlane)))) = _
        rw [hsig, normalizedWeldingSphere_infty hμ, mobiusExt_infty_of_ne hc, finPart_coe]
      have ht : t s = 0 := by
        simp only [htdef]
        rw [eD, hCD, mul_zero, zero_div]
      rw [hφs, hW, ht, hG0, add_zero]
      field_simp
    · set u := (-w * (1 - conj w) * z + -(1 - w)) / (-(1 - conj w) * z + -(1 - w) * conj w) with hudef
      have hsig : sigmaInvSphere (w : ExtPlane) (z : ExtPlane) = (u : ExtPlane) := by
        rw [a6_sigmaInv_eq, mobiusExt_coe hCD]
        rfl
      have hu : u ∈ unitDiscExterior := by
        have := a6_sigmaInv_mem hw hz
        rw [hsig] at this
        simpa [extDiscExterior, toExt] using this
      have hu0 : u ≠ 0 := by
        rintro h
        rw [h] at hu
        have : (1 : ℝ) < ‖(0 : ℂ)‖ := hu
        norm_num at this
      have hN : -w * (1 - conj w) * z + -(1 - w) ≠ 0 := by
        intro h
        apply hu0
        rw [hudef, h, zero_div]
      have hW : weldG μ w z = lambdaW c (gMu μ u) := fiberWeldingExterior_finite hμ hw hz hsig
      have ht : t s = u⁻¹ := by
        simp only [htdef]
        rw [eN, eD, hudef, inv_div, mul_div_mul_left _ _ hs0]
      have hGt : gTilde μ u⁻¹ = 1 / gMu μ u := by
        simp only [gTilde, inv_eq_zero, hu0, ite_false, one_div, inv_inv, S2C.s2c_gsans_eq hμ]
      have hx := gMu_exterior_ne_zero hμ hu
      rw [hφs, hW, ht, hGt, lambdaW]
      field_simp
      try ring
  intro s hs
  by_cases hs0 : s = 0
  · subst hs0
    have hφc : ContinuousAt φ 0 := (hφ.differentiableAt (isOpen_ball.mem_nhds hs)).continuousAt
    have hRc : ContinuousAt (fun s => b * (c + gTilde μ (t s))) 0 := hR.continuousAt (isOpen_ball.mem_nhds hs)
    have hev : φ =ᶠ[𝓝[≠] (0 : ℂ)] fun s => b * (c + gTilde μ (t s)) := by
      filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (isOpen_ball.mem_nhds hs)] with x hx0 hx
      exact hpunct x hx hx0
    exact tendsto_nhds_unique (hφc.tendsto.mono_left nhdsWithin_le_nhds)
      ((hRc.tendsto.mono_left nhdsWithin_le_nhds).congr' hev.symm)
  · exact hpunct s hs hs0

/-- **U5.** For a point of `𝒯₀(1)`, the inverted exterior map has `𝒜(φ) ∈ A₂¹(𝔻)`. -/
theorem a4_inv_pre_A21 {p : T1} (hp : p ∈ T01) {w : ℂ} (hw : w ∈ unitDiscExterior) {φ : ℂ → ℂ} {b : ℂ}
    (hφ : DifferentiableOn ℂ φ unitDisc) (hb : b ≠ 0)
    (he : ∀ s ∈ unitDisc, s ≠ 0 → weldG (Quotient.out p : LinfStarBall) w (1 / s) = b / φ s) :
    preSchwarzian φ ∈ A21fun unitDisc := by
  have hμ := (Quotient.out p : LinfStarBall).2
  set μ : LinfStar := ((Quotient.out p : LinfStarBall) : LinfStar) with hμdef
  set t : ℂ → ℂ := fun s => (-(1 - w) * conj w * s + -(1 - conj w)) / (-(1 - w) * s + -w * (1 - conj w))
    with htdef
  obtain ⟨bG, -, -, hGd, hGi, -, -⟩ := s2c_gTilde_facts hμ
  have hGA : preSchwarzian (gTilde μ) ∈ A21fun unitDisc := (s3pk_tilde_A21 hp).1
  have hrep := a4_phi_rep hμ hw hφ hb he
  have htd : ∀ s ∈ unitDisc, HasDerivAt t (((-(1 - w) * conj w) * (-w * (1 - conj w)) - (-(1 - conj w)) * (-(1 - w))) /
      (-(1 - w) * s + -w * (1 - conj w)) ^ 2) s := fun s hs => a4_t_hasDerivAt hw (mem_ball_zero_iff.mp hs).le
  have htD : DifferentiableOn ℂ t unitDisc := fun s hs => (htd s hs).differentiableAt.differentiableWithinAt
  have hmaps : MapsTo t unitDisc unitDisc := fun s hs => a4_t_disc hw hs
  have ht' : ∀ s ∈ unitDisc, deriv t s ≠ 0 := fun s hs => by
    rw [(htd s hs).deriv]
    exact div_ne_zero (a4_t_det hw) (pow_ne_zero 2 (a4_t_pole hw (mem_ball_zero_iff.mp hs).le))
  have hti : InjOn t unitDisc := by
    intro x hx y hy hxy
    have hpx := a4_t_pole hw (mem_ball_zero_iff.mp hx).le
    have hpy := a4_t_pole hw (mem_ball_zero_iff.mp hy).le
    simp only [htdef] at hxy
    rw [div_eq_div_iff hpx hpy] at hxy
    have h : (x - y) * ((-(1 - w) * conj w) * (-w * (1 - conj w)) - (-(1 - conj w)) * (-(1 - w))) = 0 := by
      linear_combination hxy
    exact sub_eq_zero.mp ((mul_eq_zero.mp h).resolve_right (a4_t_det hw))
  -- the pre-Schwarzian of `φ`
  have hpre : EqOn (preSchwarzian φ) (fun s => preSchwarzian (gTilde μ) (t s) * deriv t s + preSchwarzian t s)
      unitDisc := by
    intro s hs
    have hta : AnalyticAt ℂ t s := htD.analyticAt (isOpen_ball.mem_nhds hs)
    have hGa : AnalyticAt ℂ (gTilde μ) (t s) := hGd.analyticAt (isOpen_ball.mem_nhds (hmaps hs))
    have hG' : deriv (gTilde μ) (t s) ≠ 0 := LiZhongQC.deriv_ne_zero_of_injOn isOpen_ball hGd hGi (hmaps hs)
    rw [s2c_pre_congr hrep isOpen_ball hs, s2c_pre_const_mul hb,
      show (fun x => -1 / gMu μ w + gTilde μ (t x)) = fun x => (gTilde μ ∘ t) x + -1 / gMu μ w from
        funext fun x => add_comm _ _,
      preSchwarzian_add_const, preSchwarzian_comp_of_analyticAt hta hGa (ht' s hs) hG']
  -- the pulled-back term
  have hconf : IsConformalOnto t unitDisc (t '' unitDisc) := ⟨htD, hti, rfl⟩
  have hpull := normA21_pullback isOpen_ball hconf (preSchwarzian (gTilde μ))
  have hle : normA21 (t '' unitDisc) (preSchwarzian (gTilde μ)) ≤ normA21 unitDisc (preSchwarzian (gTilde μ)) := by
    unfold normA21
    exact ENNReal.rpow_le_rpow (lintegral_mono_set (image_subset_iff.mpr hmaps)) (by norm_num)
  have h1 : (fun s => preSchwarzian (gTilde μ) (t s) * deriv t s) ∈ A21fun unitDisc :=
    ⟨(hGA.1.comp htD hmaps).mul (htD.deriv isOpen_ball), hpull ▸ lt_of_le_of_lt hle hGA.2⟩
  exact a21_congr_on measurableSet_ball (a21_add measurableSet_ball h1 (a4_t_pre_A21 hw))
    (fun s hs => (hpre hs).symm)

/-- Maximum principle upgrade: uniform convergence on the circle `|s| = r` of holomorphic functions on `𝔻` gives uniform
convergence on the closed disc `|s| ≤ r`. -/
theorem a4_max_upgrade {F : ℕ → ℂ → ℂ} {F₀ : ℂ → ℂ} {r : ℝ} (hr : 0 < r) (hr1 : r < 1)
    (hF : ∀ n, DifferentiableOn ℂ (F n) unitDisc) (hF₀ : DifferentiableOn ℂ F₀ unitDisc)
    (hK : TendstoUniformlyOn F F₀ atTop (sphere 0 r)) : TendstoUniformlyOn F F₀ atTop (closedBall 0 r) := by
  rw [Metric.tendstoUniformlyOn_iff] at hK ⊢
  intro ε hε
  filter_upwards [hK (ε / 2) (by positivity)] with n hn x hx
  have hsub : closure (ball (0 : ℂ) r) ⊆ unitDisc := by
    rw [closure_ball _ hr.ne']
    exact closedBall_subset_ball hr1
  have hd : DiffContOnCl ℂ (fun s => F n s - F₀ s) (ball (0 : ℂ) r) :=
    ((hF n).sub hF₀).mono hsub |>.diffContOnCl
  have hC : ∀ z ∈ frontier (ball (0 : ℂ) r), ‖F n z - F₀ z‖ ≤ ε / 2 := by
    intro z hz
    rw [frontier_ball _ hr.ne'] at hz
    have := hn z hz
    rw [dist_eq_norm, norm_sub_rev] at this
    exact this.le
  have hx' : x ∈ closure (ball (0 : ℂ) r) := by rwa [closure_ball _ hr.ne']
  have h := Complex.norm_le_of_forall_mem_frontier_norm_le isBounded_ball hd hC hx'
  rw [dist_eq_norm, norm_sub_rev]
  linarith

/-- **U6.** Under (i), the values `𝒜(φₙ)(0)` converge. -/
theorem a4_inv_value {p : ℕ → T1} {w : ℕ → ℂ} {q : T1} {v : ℂ}
    (hw : ∀ n, w n ∈ unitDiscExterior) (hv : v ∈ unitDiscExterior)
    (hlim : @Tendsto _ _ (fun n => (p n, ((gMu (Quotient.out (p n) : LinfStarBall) (w n) : ℂ) : ExtPlane))) atTop
      (@nhds _ (@instTopologicalSpaceProd _ _ hilbertTopology inferInstance)
        (q, ((gMu (Quotient.out q : LinfStarBall) v : ℂ) : ExtPlane))))
    {φ : ℕ → ℂ → ℂ} {b : ℕ → ℂ} {φ₀ : ℂ → ℂ} {b₀ : ℂ}
    (hφ : ∀ n, DifferentiableOn ℂ (φ n) unitDisc) (hφ₀ : DifferentiableOn ℂ φ₀ unitDisc)
    (hb : ∀ n, b n ≠ 0) (hb₀ : b₀ ≠ 0)
    (he : ∀ n, ∀ s ∈ unitDisc, s ≠ 0 → weldG (Quotient.out (p n) : LinfStarBall) (w n) (1 / s) = b n / φ n s)
    (he₀ : ∀ s ∈ unitDisc, s ≠ 0 → weldG (Quotient.out q : LinfStarBall) v (1 / s) = b₀ / φ₀ s)
    (h1 : ∀ n, deriv (φ n) 0 = 1) (h1₀ : deriv φ₀ 0 = 1) :
    Tendsto (fun n => preSchwarzian (φ n) 0) atTop (𝓝 (preSchwarzian φ₀ 0)) := by
  have hU := a6_ext_open
  have hL := a6_weldG_LU hw hv hlim
  have hUq := appa2_weldG_univalent (Quotient.out q : LinfStarBall).2 hv
  have h0q := a4_pair_ne_zero (a4_weld_pair (Quotient.out q : LinfStarBall).2 hv)
  have h0p := fun n => a4_pair_ne_zero (a4_weld_pair (Quotient.out (p n) : LinfStarBall).2 (hw n))
  have hinv : TendstoLocallyUniformlyOn (fun n z => (weldG (Quotient.out (p n) : LinfStarBall) (w n) z)⁻¹)
      (fun z => (weldG (Quotient.out q : LinfStarBall) v z)⁻¹) atTop unitDiscExterior :=
    hL.inv₀ hUq.1.continuousOn h0q
  have hmaps : MapsTo (fun s : ℂ => s⁻¹) (unitDisc \ {0}) unitDiscExterior := fun s hs => by
    have := a4_one_div_mem hs
    rwa [one_div] at this
  have hcont : ContinuousOn (fun s : ℂ => s⁻¹) (unitDisc \ {0}) := continuousOn_inv₀.mono fun s hs => hs.2
  have hcomp := hinv.comp (fun s : ℂ => s⁻¹) hmaps hcont
  have hD0 : IsOpen (unitDisc \ {0}) := isOpen_ball.sdiff isClosed_singleton
  have hF : TendstoLocallyUniformlyOn (fun n s => φ n s / b n) (fun s => φ₀ s / b₀) atTop (unitDisc \ {0}) := by
    refine (hcomp.congr fun n s hs => ?_).congr_right fun s hs => ?_
    · show (weldG (Quotient.out (p n) : LinfStarBall) (w n) s⁻¹)⁻¹ = φ n s / b n
      have hG : weldG (Quotient.out (p n) : LinfStarBall) (w n) s⁻¹ ≠ 0 := h0p n _ (hmaps hs)
      have hbn := hb n
      rw [a4_phi_eq (h0p n) (hb n) (he n) hs]
      field_simp
    · show (weldG (Quotient.out q : LinfStarBall) v s⁻¹)⁻¹ = φ₀ s / b₀
      have hG : weldG (Quotient.out q : LinfStarBall) v s⁻¹ ≠ 0 := h0q _ (hmaps hs)
      rw [a4_phi_eq h0q hb₀ he₀ hs]
      field_simp
  have hsph : sphere (0 : ℂ) (1 / 2) ⊆ unitDisc \ {0} := by
    intro x hx
    have hx' : ‖x‖ = 1 / 2 := mem_sphere_zero_iff_norm.mp hx
    refine ⟨mem_ball_zero_iff.2 (by rw [hx']; norm_num), fun h0 => ?_⟩
    rw [mem_singleton_iff.mp h0, norm_zero] at hx'
    norm_num at hx'
  have hK := (tendstoLocallyUniformlyOn_iff_forall_isCompact hD0).1 hF _ hsph (isCompact_sphere _ _)
  have hcb := a4_max_upgrade (by norm_num) (by norm_num) (fun n => (hφ n).div_const (b n)) (hφ₀.div_const b₀) hK
  have hball : ball (0 : ℂ) (1 / 2) ⊆ unitDisc := ball_subset_ball (by norm_num)
  have hLb : TendstoLocallyUniformlyOn (fun n s => φ n s / b n) (fun s => φ₀ s / b₀) atTop (ball 0 (1 / 2)) :=
    (hcb.mono ball_subset_closedBall).tendstoLocallyUniformlyOn
  have hd1 := hLb.deriv (Eventually.of_forall fun n => ((hφ n).div_const (b n)).mono hball) isOpen_ball
  have hd2 := hd1.deriv (Eventually.of_forall fun n =>
    ((((hφ n).div_const (b n)).deriv isOpen_ball).mono hball)) isOpen_ball
  have h0b : (0 : ℂ) ∈ ball (0 : ℂ) (1 / 2) := mem_ball_self (by norm_num)
  have t1 := hd1.tendsto_at h0b
  have t2 := hd2.tendsto_at h0b
  have ed : ∀ (ψ : ℂ → ℂ) (c : ℂ), deriv (fun s => ψ s / c) = fun s => deriv ψ s / c := fun ψ c =>
    funext fun s => deriv_div_const c
  simp only [Function.comp_apply, ed] at t1 t2
  rw [h1₀] at t1
  have t1' : Tendsto (fun n => b n) atTop (𝓝 b₀) := by
    have := t1.inv₀ (div_ne_zero one_ne_zero hb₀)
    simp only [h1, one_div, inv_inv] at this
    exact this
  have t3 := t1'.mul t2
  have e : ∀ n, preSchwarzian (φ n) 0 = b n * (deriv (deriv (φ n)) 0 / b n) := fun n => by
    rw [preSchwarzian, h1, div_one]
    field_simp [hb n]
  have e₀ : preSchwarzian φ₀ 0 = b₀ * (deriv (deriv φ₀) 0 / b₀) := by
    rw [preSchwarzian, h1₀, div_one]
    field_simp [hb₀]
  rw [e₀]
  exact t3.congr fun n => (e n).symm

/-- **U7.** (i) ⇒ (iii) of Corollary A.4. -/
theorem a4_i_imp_iii {p : ℕ → T1} {w : ℕ → ℂ} {q : T1} {v : ℂ} (hp : ∀ n, p n ∈ T01)
    (hw : ∀ n, w n ∈ unitDiscExterior) (hq : q ∈ T01) (hv : v ∈ unitDiscExterior)
    (hlim : @Tendsto _ _ (fun n => (p n, ((gMu (Quotient.out (p n) : LinfStarBall) (w n) : ℂ) : ExtPlane))) atTop
      (@nhds _ (@instTopologicalSpaceProd _ _ hilbertTopology inferInstance)
        (q, ((gMu (Quotient.out q : LinfStarBall) v : ℂ) : ExtPlane)))) :
    Tendsto (fun n => normA21 unitDiscExterior (fun z =>
        (preSchwarzian (weldG (Quotient.out (p n) : LinfStarBall) (w n)) z -
            2 * deriv (weldG (Quotient.out (p n) : LinfStarBall) (w n)) z /
              weldG (Quotient.out (p n) : LinfStarBall) (w n) z + 2 / z) -
          (preSchwarzian (weldG (Quotient.out q : LinfStarBall) v) z -
            2 * deriv (weldG (Quotient.out q : LinfStarBall) v) z / weldG (Quotient.out q : LinfStarBall) v z +
              2 / z))) atTop (𝓝 0) := by
  have hμ : ∀ n, ((Quotient.out (p n) : LinfStarBall) : LinfStar) ∈ LinfStarBall := fun n =>
    (Quotient.out (p n) : LinfStarBall).2
  have hν := (Quotient.out q : LinfStarBall).2
  choose φ b hφd hφne hφ0 hφ1 hb he using fun n => a4_inv_data (hμ n) (hw n)
  obtain ⟨φ₀, b₀, hφ₀d, hφ₀ne, hφ₀0, hφ₀1, hb₀, he₀⟩ := a4_inv_data hν hv
  have hpair := fun n => a4_weld_pair (hμ n) (hw n)
  have hpair₀ := a4_weld_pair hν hv
  have hg0 : ∀ {f g : ℂ → ℂ}, IsNormalizedDisjointPair f g → ∀ z ∈ unitDiscExterior, g z ≠ 0 := by
    intro f g h z hz hgz
    exact Set.disjoint_left.mp h.2.2.2.2.2 ⟨0, mem_ball_self one_pos, h.2.2.1⟩ ⟨z, hz, hgz⟩
  have hS := (a6_ext_schwarzian_tendsto hp hw hq hv hlim).congr fun n =>
    a4_S_norm (hpair n).2.2.2.2.1 hpair₀.2.2.2.2.1 (hg0 (hpair n)) (hg0 hpair₀) (hb n) hb₀ (he n) he₀
  have hψ := a4_inverse hφ₀d hφ₀ne hφ₀1 (a4_inv_pre_A21 hq hv hφ₀d hb₀ he₀)
    (ψ := fun n => preSchwarzian (φ n)) (fun n => a4_inv_pre_A21 (hp n) (hw n) (hφd n) (hb n) (he n))
    (hS.congr fun n => by
      apply normA2_congr measurableSet_ball
      intro s _
      rfl)
    (a4_inv_value hw hv hlim hφd hφ₀d hb hb₀ he he₀ hφ1 hφ₀1)
  exact hψ.congr fun n =>
    (a4_lg_norm (hpair n).2.2.2.2.1 hpair₀.2.2.2.2.1 (hg0 (hpair n)) (hg0 hpair₀) (hb n) hb₀ (he n) he₀).symm

/-! ### (iii) ⇒ (i): partners -/

/-- On the circle the two forms of the fibre homeomorphism agree. -/
theorem a4_h_eq {μ : LinfStar} (hμ : μ ∈ LinfStarBall) {w : ℂ} (hw : w ∈ unitDiscExterior) {z : ℂ}
    (hz : z ∈ unitCircle) :
    finPart (sigmaSphere (w : ExtPlane) (gammaMu μ z)) = sigmaW w (finPart (gammaMu μ z)) := by
  have hz1 : ‖z‖ = 1 := hz
  obtain ⟨hg, hn⟩ := tce_gamma_circle hμ hz1
  have hw1 : 1 < ‖w‖ := hw
  have hne : wA μ z ≠ w := by
    intro h
    rw [h] at hn
    linarith
  rw [hg, sigmaSphere_coe_eq hw hne, finPart_coe, finPart_coe]

theorem a4_mobius_id : IsMobius (id : ExtPlane → ExtPlane) := by
  refine ⟨1, 0, 0, 1, by norm_num, ?_⟩
  funext x
  induction x using OnePoint.rec with
  | infty => exact (mobiusExt_infty_of_eq rfl).symm
  | coe z =>
    rw [mobiusExt_coe (by simp)]
    simp [mobiusFn]

/-- `tce_surj` from a given plane extension. -/
theorem a4_tce_surj' {e : ℂ ≃ₜ ℂ} {K : ℝ} (hK : IsKQC (⇑e) univ K)
    (hHc : e '' sphere (0 : ℂ) 1 = sphere (0 : ℂ) 1) (h1 : e 1 = 1) :
    ∃ (p : T1) (w : ExtPlane), w ∈ extDiscExterior ∧
      EqOn (fun z : ℂ => finPart (sigmaSphere w (gammaMu (Quotient.out p : LinfStarBall) z))) (⇑e) unitCircle := by
  obtain ⟨μ, hμ, a, c, ha, hc, hw1, hform⟩ := tce_exists_mu hK hHc (fun _ _ => rfl)
  have h2 : teichSetoid.r (Phi ⟨μ, hμ⟩).out ⟨μ, hμ⟩ := Quotient.mk_out (s := teichSetoid) ⟨μ, hμ⟩
  have hμo := (Quotient.out (Phi ⟨μ, hμ⟩) : LinfStarBall).property
  have hc0 : c ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hc
    exact zero_ne_one hc
  have h1a : 1 - a ≠ 0 := by
    intro h0
    have : a = 1 := by linear_combination -h0
    rw [this, norm_one] at ha
    exact lt_irrefl _ ha
  have hR : c * (1 - a) = 1 - conj a := by
    have := hform 1 (by simp)
    rw [hw1, h1] at this
    rw [eq_div_iff (mul_ne_zero hc0 (by simpa using h1a))] at this
    linear_combination this
  have hnorm : ∀ z : ℂ, ‖z‖ = 1 → ‖e z‖ = 1 := by
    intro z hz
    have : e z ∈ e '' sphere (0 : ℂ) 1 := mem_image_of_mem _ (mem_sphere_zero_iff_norm.mpr hz)
    rw [hHc] at this
    exact mem_sphere_zero_iff_norm.mp this
  refine ⟨Phi ⟨μ, hμ⟩, ?_⟩
  by_cases ha0 : a = 0
  · refine ⟨extInf, Or.inr rfl, fun z hz => ?_⟩
    have hz1 : ‖z‖ = 1 := hz
    obtain ⟨hg, -⟩ := tce_gamma_circle hμo hz1
    have hc1 : c = 1 := by
      rw [ha0] at hR
      simpa using hR
    have hw := hform z hz1
    rw [ha0, hc1] at hw
    have e1 : wA (Quotient.out (Phi ⟨μ, hμ⟩) : LinfStarBall) z = wA μ z := h2 z hz
    show finPart (sigmaSphere extInf (gammaMu (Quotient.out (Phi ⟨μ, hμ⟩) : LinfStarBall) z)) = e z
    rw [hg, e1, hw]
    simp [sigmaSphere, finPart]
  · have hb : conj a ≠ 0 := (map_ne_zero conj).2 ha0
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
    have hzn : ‖e z‖ = 1 := hnorm z hz1
    have hne : wA (Quotient.out (Phi ⟨μ, hμ⟩) : LinfStarBall) z ≠ -conj c / a := by
      intro he
      have := congrArg norm he
      rw [hn] at this
      linarith
    show finPart (sigmaSphere ((-conj c / a : ℂ) : ExtPlane)
      (gammaMu (Quotient.out (Phi ⟨μ, hμ⟩) : LinfStarBall) z)) = e z
    rw [hg, sigmaSphere_coe_eq hwn hne]
    show sigmaW (-conj c / a) (wA (Quotient.out (Phi ⟨μ, hμ⟩) : LinfStarBall) z) = e z
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
    have hd : 1 - a * e z ≠ 0 := by
      intro h0
      have h3 : a * e z = 1 := by linear_combination -h0
      have h4 : ‖a * e z‖ = 1 := by rw [h3, norm_one]
      rw [norm_mul, hzn] at h4
      linarith
    unfold sigmaW
    rw [show conj (-conj c / a) = -c / conj a by simp [map_div₀]]
    exact tce_alg hab ha0 hb hcc hR hR' hd

/-- **R1'.** Every point `(p, w)` with finite `w` has a partner with finite fibre coordinate. -/
theorem a4_sharp_exists {p : T1} {w : ℂ} (hw : w ∈ unitDiscExterior) :
    ∃ p' : T1, ∃ w' : ℂ, w' ∈ unitDiscExterior ∧
      ∀ z ∈ unitCircle, finPart (sigmaSphere (w' : ExtPlane) (gammaMu (Quotient.out p' : LinfStarBall)
        (finPart (sigmaSphere (w : ExtPlane) (gammaMu (Quotient.out p : LinfStarBall) z))))) = z := by
  have hμ := (Quotient.out p : LinfStarBall).2
  have hFW := fiber_welding hμ hw
  dsimp only at hFW
  obtain ⟨hOF, -, -⟩ := hFW
  obtain ⟨H, ⟨K, hK⟩, hHs, hHc, hHh⟩ := circle_quasisymmetric_plane_extension hOF.1
  obtain ⟨e, rfl⟩ := t1_homeomorph hK hHs
  have hK' := homeomorph_inverse_isKQC e hK
  have hHc' : e.symm '' sphere (0 : ℂ) 1 = sphere (0 : ℂ) 1 := by
    conv_lhs => rw [← hHc]
    exact e.symm_image_image _
  have he1 : e 1 = 1 := (hHh (show (1 : ℂ) ∈ unitCircle by simp [unitCircle])).trans hOF.2
  have h1 : e.symm 1 = 1 := by rw [e.symm_apply_eq, he1]
  obtain ⟨p', w'', hw'', hEq⟩ := a4_tce_surj' hK' hHc' h1
  -- `h_γ = e` on the circle
  have hhe : ∀ z ∈ unitCircle, finPart (sigmaSphere (w : ExtPlane) (gammaMu (Quotient.out p : LinfStarBall) z)) =
      e z := fun z hz => by rw [a4_h_eq hμ hw hz]; exact (hHh hz).symm
  -- the fibre coordinate of the partner is finite
  have hfin : w'' ≠ extInf := by
    intro hinf
    subst hinf
    have hμ' := (Quotient.out p' : LinfStarBall).2
    obtain ⟨-, -, -, -, -, -, hm1, hmI, hm2⟩ := wA_spec hμ'
    obtain ⟨-, -, -, -, -, -, hn1, hnI, hn2⟩ := wA_spec hμ
    have hfix : ∀ x : ℂ, (x = 1 ∨ x = -1 ∨ x = -I) → sigmaSphere (w : ExtPlane) (x : ExtPlane) = (x : ExtPlane) := by
      intro x hx
      have hxc : x ∈ unitCircle := by
        rcases hx with rfl | rfl | rfl <;> simp [unitCircle]
      have hγ' : gammaMu (Quotient.out p' : LinfStarBall) x = (x : ExtPlane) := by
        unfold gammaMu
        rw [alphaMu_eq_id]
        rcases hx with rfl | rfl | rfl
        · exact hm2
        · exact hm1
        · exact hmI
      have hγ : gammaMu (Quotient.out p : LinfStarBall) x = (x : ExtPlane) := by
        unfold gammaMu
        rw [alphaMu_eq_id]
        rcases hx with rfl | rfl | rfl
        · exact hn2
        · exact hn1
        · exact hnI
      have hs : e.symm x = x := by
        have := hEq hxc
        simp only [hγ'] at this
        rw [← this]
        rfl
      have hex : e x = x := by
        have := congrArg e hs
        rwa [e.apply_symm_apply, eq_comm] at this
      have h3 := hhe x hxc
      rw [hγ, hex] at h3
      have hx1 : ‖x‖ = 1 := hxc
      have hw1 : 1 < ‖w‖ := hw
      have hne : x ≠ w := by
        rintro rfl
        linarith
      rw [sigmaSphere_coe_eq hw hne, finPart_coe] at h3
      rw [sigmaSphere_coe_eq hw hne, h3]
    have hid := mobius_eq_of_three_points (tce_sigma_isMobius (Or.inl ⟨w, hw, rfl⟩)) a4_mobius_id
      (p₁ := 1) (p₂ := -1) (p₃ := -I) (by norm_num)
      (by intro h; have := congrArg Complex.re h; simp at this)
      (by intro h; have := congrArg Complex.im h; simp at this)
      (hfix 1 (Or.inl rfl)) (hfix (-1) (Or.inr (Or.inl rfl))) (hfix (-I) (Or.inr (Or.inr rfl)))
    have hp := sigmaSphere_pole (w : ExtPlane)
    rw [hid] at hp
    exact OnePoint.coe_ne_infty w hp
  rcases hw'' with ⟨w', hw', rfl⟩ | hinf
  · refine ⟨p', w', hw', fun z hz => ?_⟩
    have hz1 : ‖z‖ = 1 := hz
    have hnz : ‖e z‖ = 1 := by
      have : e z ∈ e '' sphere (0 : ℂ) 1 := mem_image_of_mem _ (mem_sphere_zero_iff_norm.mpr hz1)
      rw [hHc] at this
      exact mem_sphere_zero_iff_norm.mp this
    rw [hhe z hz]
    exact (hEq (show e z ∈ unitCircle from hnz)).trans (e.symm_apply_apply z)
  · exact absurd hinf hfin

/-! #### R2 support -/

theorem a4_affine_qc {a c : ℂ} (ha : a ≠ 0) {F : ℂ → ℂ} (hF : IsQuasiconformal F univ) (hFs : F '' univ = univ) :
    IsQuasiconformal (fun z => a * F z + c) univ ∧ (fun z => a * F z + c) '' univ = univ := by
  have hAs : (fun x : ℂ => a * x + c) '' univ = univ := by
    refine eq_univ_of_forall fun y => ⟨(y - c) / a, mem_univ _, ?_⟩
    field_simp
    ring
  have hA : IsConformalOnto (fun x : ℂ => a * x + c) univ univ := by
    refine ⟨(by fun_prop : Differentiable ℂ fun x : ℂ => a * x + c).differentiableOn, ?_, hAs⟩
    intro x _ y _ hxy
    have : a * (x - y) = 0 := by linear_combination hxy
    exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left ha)
  obtain ⟨K, hK⟩ := hF
  refine ⟨⟨K * 1, thm7_1_comp hK (isKQC_one_of_conformal isOpen_univ hA) (subset_univ _)⟩, ?_⟩
  rw [show (fun z => a * F z + c) = (fun x : ℂ => a * x + c) ∘ F from rfl, image_comp, hFs, hAs]

theorem a4_R_circle {R : ℂ ≃ₜ ℂ} (hRE : R '' unitDiscExterior = unitDiscExterior)
    (hRD : IsConformalOnto (⇑R.symm) unitDisc unitDisc) {y : ℂ} (hy : y ∈ unitCircle) : R.symm y ∈ unitCircle := by
  have hy1 : ‖y‖ = 1 := hy
  show ‖R.symm y‖ = 1
  rcases lt_trichotomy ‖R.symm y‖ 1 with h | h | h
  · exfalso
    have hx : R.symm y ∈ unitDisc := mem_ball_zero_iff.mpr h
    rw [← hRD.2.2] at hx
    obtain ⟨x', hx', hxe⟩ := hx
    have : y = x' := by
      have := congrArg R hxe
      simpa using this.symm
    rw [this] at hy1
    have := mem_ball_zero_iff.mp hx'
    linarith
  · exact h
  · exfalso
    have hx : R (R.symm y) ∈ R '' unitDiscExterior := mem_image_of_mem _ (show 1 < ‖R.symm y‖ from h)
    rw [hRE, R.apply_symm_apply] at hx
    have : (1 : ℝ) < ‖y‖ := hx
    linarith

theorem a4_wA_inv {μ : LinfStar} (hμ : μ ∈ LinfStarBall) {ζ : ℂ} (hζ : ‖ζ‖ = 1) :
    wA μ (wA (beltramiInv μ) ζ) = ζ := by
  have hμ₁ := grp_inv_mem hμ
  obtain ⟨hg, -⟩ := tce_gamma_circle hμ₁ hζ
  have hw : wAS (beltramiInv μ) (ζ : ExtPlane) = ((wA (beltramiInv μ) ζ : ℂ) : ExtPlane) := by
    unfold gammaMu at hg
    rw [alphaMu_eq_id] at hg
    exact hg
  show finPart (wAS μ ((wA (beltramiInv μ) ζ : ℂ) : ExtPlane)) = ζ
  rw [← hw, show wAS μ (wAS (beltramiInv μ) (ζ : ExtPlane)) = (wAS μ ∘ wAS (beltramiInv μ)) (ζ : ExtPlane) from rfl,
    grp_wAS_inv_left hμ]
  rfl

theorem a4_sigmaInv_circle {w : ℂ} (hw : w ∈ unitDiscExterior) {y : ℂ} (hy : ‖y‖ = 1) :
    -(1 - conj w) * y + -(1 - w) * conj w ≠ 0 ∧
      ‖(-w * (1 - conj w) * y + -(1 - w)) / (-(1 - conj w) * y + -(1 - w) * conj w)‖ = 1 := by
  obtain ⟨hdet, hkey⟩ := appa2_sigmaInv_coeffs (w := w)
  have hk := hkey y
  rw [hy] at hk
  simp only [one_pow, sub_self, mul_zero] at hk
  have hD : -(1 - conj w) * y + -(1 - w) * conj w ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hk
    have hN : -w * (1 - conj w) * y + -(1 - w) = 0 := by
      have : ‖-w * (1 - conj w) * y + -(1 - w)‖ = 0 := by nlinarith [norm_nonneg (-w * (1 - conj w) * y + -(1 - w))]
      exact norm_eq_zero.mp this
    have hw1 : 1 < ‖w‖ := hw
    have hw0 : w ≠ 1 := by rintro rfl; simp at hw1
    have h1 : 0 < ‖1 - w‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (Ne.symm hw0))
    have hκ : (0 : ℝ) < ‖1 - w‖ ^ 2 * (‖w‖ ^ 2 - 1) := by
      have : 1 < ‖w‖ ^ 2 := by nlinarith
      have : 0 < ‖1 - w‖ ^ 2 := by positivity
      nlinarith
    have hy0 : y ≠ 0 := by rintro rfl; simp at hy
    have hz' : y * ((-w * (1 - conj w)) * (-(1 - w) * conj w) - (-(1 - w)) * (-(1 - conj w))) = 0 := by
      linear_combination (-(1 - w) * conj w) * hN - (-(1 - w)) * h0
    have hz := (mul_eq_zero.mp hz').resolve_left hy0
    rw [hdet] at hz
    exact hκ.ne' (by exact_mod_cast hz)
  refine ⟨hD, ?_⟩
  rw [norm_div, div_eq_one_iff_eq (norm_ne_zero_iff.mpr hD)]
  have h2 : ‖-w * (1 - conj w) * y + -(1 - w)‖ ^ 2 = ‖-(1 - conj w) * y + -(1 - w) * conj w‖ ^ 2 := by linarith
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h2

/-- `t̄ = R⁻¹` on `𝔻`, where `t = j ∘ σ_w⁻¹ ∘ j` and `R` is a σ-extension. -/
theorem a4_tbar {w : ℂ} (hw : w ∈ unitDiscExterior) {R : ℂ ≃ₜ ℂ}
    (hRE : R '' unitDiscExterior = unitDiscExterior) (hRD : IsConformalOnto (⇑R.symm) unitDisc unitDisc)
    (hRb : EqOn (⇑R) (fun z : ℂ => finPart (sigmaSphere (w : ExtPlane) (z : ExtPlane))) unitCircle) :
    ∀ s ∈ unitDisc, conj ((-(1 - w) * conj w * conj s + -(1 - conj w)) / (-(1 - w) * conj s + -w * (1 - conj w))) =
      R.symm s := by
  have _hRE := hRE
  set T : ℂ → ℂ := fun s =>
    conj ((-(1 - w) * conj w * conj s + -(1 - conj w)) / (-(1 - w) * conj s + -w * (1 - conj w))) with hTdef
  -- `T` is a Möbius map with pole off the closed disc
  have hTe : ∀ s, T s = (conj (-(1 - w) * conj w) * s + conj (-(1 - conj w))) /
      (conj (-(1 - w)) * s + conj (-w * (1 - conj w))) := fun s => by
    simp only [hTdef, map_div₀, map_add, map_mul, Complex.conj_conj]
  have hpole : ∀ s : ℂ, ‖s‖ ≤ 1 → conj (-(1 - w)) * s + conj (-w * (1 - conj w)) ≠ 0 := by
    intro s hs h0
    apply a4_t_pole hw (show ‖conj s‖ ≤ 1 by rwa [Complex.norm_conj])
    have := congrArg conj h0
    simpa [map_add, map_mul] using this
  have hTd : ∀ s : ℂ, ‖s‖ ≤ 1 → DifferentiableAt ℂ T s := fun s hs => by
    rw [show T = fun s => (conj (-(1 - w) * conj w) * s + conj (-(1 - conj w))) /
      (conj (-(1 - w)) * s + conj (-w * (1 - conj w))) from funext hTe]
    exact ((by fun_prop : DifferentiableAt ℂ (fun s : ℂ => conj (-(1 - w) * conj w) * s + conj (-(1 - conj w))) s).div
      (by fun_prop : DifferentiableAt ℂ (fun s : ℂ => conj (-(1 - w)) * s + conj (-w * (1 - conj w))) s) (hpole s hs))
  -- boundary values
  have hbd : ∀ y : ℂ, ‖y‖ = 1 → T y = R.symm y := by
    intro y hy
    obtain ⟨hD, hn⟩ := a4_sigmaInv_circle hw hy
    set v := (-w * (1 - conj w) * y + -(1 - w)) / (-(1 - conj w) * y + -(1 - w) * conj w) with hvdef
    have hsig : sigmaInvSphere (w : ExtPlane) (y : ExtPlane) = (v : ExtPlane) := by
      rw [a6_sigmaInv_eq, mobiusExt_coe hD]
      rfl
    have hRv : R v = y := by
      have h1 := hRb (show v ∈ unitCircle from hn)
      rw [h1]
      show finPart (sigmaSphere (w : ExtPlane) (v : ExtPlane)) = y
      rw [← hsig, sigmaSphere_inv_apply (Or.inl ⟨w, hw, rfl⟩)]
      rfl
    have hRs : R.symm y = v := by rw [← hRv, R.symm_apply_apply]
    rw [hRs]
    have hy0 : y ≠ 0 := by rintro rfl; simp at hy
    have hcy : conj y = y⁻¹ := by
      rw [Complex.inv_def, Complex.normSq_eq_norm_sq, hy]
      simp
    have hv0 : v ≠ 0 := by intro h; rw [h, norm_zero] at hn; exact zero_ne_one hn
    have hN : -w * (1 - conj w) * y + -(1 - w) ≠ 0 := by
      intro h
      apply hv0
      rw [hvdef, h, zero_div]
    have hcv : conj v = v⁻¹ := by
      rw [Complex.inv_def, Complex.normSq_eq_norm_sq, hn]
      simp
    have ht : (-(1 - w) * conj w * conj y + -(1 - conj w)) / (-(1 - w) * conj y + -w * (1 - conj w)) = v⁻¹ := by
      rw [hcy, hvdef, inv_div]
      field_simp
      ring
    show conj ((-(1 - w) * conj w * conj y + -(1 - conj w)) / (-(1 - w) * conj y + -w * (1 - conj w))) = v
    rw [ht, ← hcv, Complex.conj_conj]
  -- maximum principle on `T - R⁻¹`
  intro s hs
  have hd : DiffContOnCl ℂ (fun x => T x - R.symm x) (ball (0 : ℂ) 1) := by
    refine ⟨fun x hx => ?_, ?_⟩
    · have hx1 : ‖x‖ ≤ 1 := (mem_ball_zero_iff.mp hx).le
      exact ((hTd x hx1).differentiableWithinAt).sub (hRD.1 x hx)
    · rw [closure_ball _ one_ne_zero]
      refine ContinuousOn.sub (fun x hx => (hTd x (mem_closedBall_zero_iff.mp hx)).continuousAt.continuousWithinAt)
        R.symm.continuous.continuousOn
  have hC : ∀ z ∈ frontier (ball (0 : ℂ) 1), ‖T z - R.symm z‖ ≤ 0 := by
    intro z hz
    rw [frontier_ball _ one_ne_zero] at hz
    rw [hbd z (mem_sphere_zero_iff_norm.mp hz), sub_self, norm_zero]
  have h := Complex.norm_le_of_forall_mem_frontier_norm_le isBounded_ball hd hC (subset_closure hs)
  exact sub_eq_zero.mp (norm_le_zero_iff.mp h)

/-- The reflected inverted exterior map is `f_{μ⁻¹} ∘ R⁻¹`. -/
theorem a4_pre_reflect {μ : LinfStar} (hμ : μ ∈ LinfStarBall) {w : ℂ} (hw : w ∈ unitDiscExterior)
    {R : ℂ ≃ₜ ℂ} (hRE : R '' unitDiscExterior = unitDiscExterior)
    (hRD : IsConformalOnto (⇑R.symm) unitDisc unitDisc)
    (hRb : EqOn (⇑R) (fun z : ℂ => finPart (sigmaSphere (w : ExtPlane) (z : ExtPlane))) unitCircle)
    {φ : ℂ → ℂ} {b : ℂ} (hφ : DifferentiableOn ℂ φ unitDisc) (hb : b ≠ 0)
    (he : ∀ s ∈ unitDisc, s ≠ 0 → weldG μ w (1 / s) = b / φ s) {z : ℂ} (hz : z ∈ unitDisc) :
    preSchwarzian (fun s => fB (beltramiInv μ) (R.symm s)) z = conj (preSchwarzian φ (conj z)) := by
  have hμ₁ := grp_inv_mem hμ
  set t : ℂ → ℂ := fun s => (-(1 - w) * conj w * s + -(1 - conj w)) / (-(1 - w) * s + -w * (1 - conj w)) with htdef
  obtain ⟨d, hd, hdg, -⟩ := s2c_gTilde_facts hμ
  have hrep := a4_phi_rep hμ hw hφ hb he
  have hconj : ∀ {x : ℂ}, x ∈ unitDisc → conj x ∈ unitDisc := fun hx => by simpa [unitDisc] using hx
  have hx := hconj hz
  -- `φ = b (c + g̃ ∘ t)`
  have h1 : preSchwarzian φ (conj z) = preSchwarzian (gTilde μ ∘ t) (conj z) := by
    rw [s2c_pre_congr hrep isOpen_ball hx, s2c_pre_const_mul hb,
      show (fun x => -1 / gMu μ w + gTilde μ (t x)) = fun x => (gTilde μ ∘ t) x + -1 / gMu μ w from
        funext fun x => add_comm _ _, preSchwarzian_add_const]
  -- `g̃ ∘ t = d⁻¹ conj ∘ (f_{μ⁻¹} ∘ R⁻¹) ∘ conj`
  have h2 : EqOn (gTilde μ ∘ t) (fun x => d⁻¹ * conj (fB (beltramiInv μ) (R.symm (conj x)))) unitDisc := by
    intro x hxD
    have htx := a4_t_disc hw hxD
    have hp := s3pk_gTilde_pair hμ htx
    simp only at hp
    rw [hdg, S2C.s2c_fsans_eq hμ₁] at hp
    have hT := a4_tbar hw hRE hRD hRb (conj x) (hconj hxD)
    rw [Complex.conj_conj] at hT
    show gTilde μ (t x) = d⁻¹ * conj (fB (beltramiInv μ) (R.symm (conj x)))
    rw [← hT]
    have ht : conj ((-(1 - w) * conj w * x + -(1 - conj w)) / (-(1 - w) * x + -w * (1 - conj w))) = conj (t x) := rfl
    rw [ht, hp, ← mul_assoc, inv_mul_cancel₀ hd, one_mul]
  have hcp := s2c_conj_pre (fun y => fB (beltramiInv μ) (R.symm y)) (conj z)
  try simp only at hcp
  rw [h1, s2c_pre_congr h2 isOpen_ball hx, s2c_pre_const_mul (inv_ne_zero hd), hcp, Complex.conj_conj,
    Complex.conj_conj]

/-- The partner's interior map is an affine image of `f_{μ⁻¹} ∘ R⁻¹`. -/
theorem a4_weldF_partner {μ μ' : LinfStar} (hμ : μ ∈ LinfStarBall) (hμ' : μ' ∈ LinfStarBall)
    {w w' : ℂ} (hw : w ∈ unitDiscExterior) (hw' : w' ∈ unitDiscExterior)
    {R : ℂ ≃ₜ ℂ} {KR : ℝ} (hR : IsKQC (⇑R) univ KR) (hRE : R '' unitDiscExterior = unitDiscExterior)
    (hRD : IsConformalOnto (⇑R.symm) unitDisc unitDisc)
    (hRb : EqOn (⇑R) (fun z : ℂ => finPart (sigmaSphere (w : ExtPlane) (z : ExtPlane))) unitCircle)
    (hcirc : ∀ z ∈ unitCircle, finPart (sigmaSphere (w' : ExtPlane) (gammaMu μ'
      (finPart (sigmaSphere (w : ExtPlane) (gammaMu μ z))))) = z) :
    ∃ a c : ℂ, a ≠ 0 ∧ EqOn (weldF μ' w') (fun z => a * fB (beltramiInv μ) (R.symm z) + c) unitDisc := by
  have hμ₁ := grp_inv_mem hμ
  set μ₁ := beltramiInv μ with hμ₁def
  obtain ⟨hα, ⟨F₁, G₁, hF₁q, hF₁s, hF₁f, hG₁q, hG₁s, hG₁g, hbd⟩, hfd, hfi, -, -, hgU⟩ := gMu_isWelding hμ₁
  have hRmaps : MapsTo (⇑R.symm) unitDisc unitDisc := fun z hz => hRD.2.2 ▸ mem_image_of_mem _ hz
  -- the circle map of the partner
  have hpart : ∀ y ∈ unitCircle, sigmaW w' (finPart (gammaMu μ' y)) = wA μ₁ (R.symm y) := by
    intro y hy
    have hRy := a4_R_circle hRE hRD hy
    have hRy1 : ‖R.symm y‖ = 1 := hRy
    set x := wA μ₁ (R.symm y) with hxdef
    have hx1 : ‖x‖ = 1 := (tce_gamma_circle hμ₁ hRy1).2
    have hxc : x ∈ unitCircle := hx1
    have hhx : finPart (sigmaSphere (w : ExtPlane) (gammaMu μ x)) = y := by
      rw [a4_h_eq hμ hw hxc, (tce_gamma_circle hμ hx1).1, finPart_coe]
      show sigmaW w (wA μ (wA (beltramiInv μ) (R.symm y))) = y
      rw [a4_wA_inv hμ hRy1]
      have hw1 : 1 < ‖w‖ := hw
      have hne : R.symm y ≠ w := by
        intro h
        rw [h] at hRy1
        linarith
      have h := hRb hRy
      simp only at h
      rw [R.apply_symm_apply, sigmaSphere_coe_eq hw hne, finPart_coe] at h
      exact h.symm
    have h := hcirc x hxc
    rw [hhx, a4_h_eq hμ' hw' hy] at h
    exact h
  -- normalization constants
  have hRd0 : DifferentiableAt ℂ (⇑R.symm) 0 := hRD.1.differentiableAt (isOpen_ball.mem_nhds (mem_ball_self one_pos))
  have hfd0 : DifferentiableAt ℂ (fB μ₁) (R.symm 0) :=
    hfd.differentiableAt (isOpen_ball.mem_nhds (hRmaps (mem_ball_self one_pos)))
  set κ := deriv (fun z => fB μ₁ (R.symm z)) 0 with hκdef
  have hκ : κ ≠ 0 := by
    rw [hκdef, show (fun z => fB μ₁ (R.symm z)) = fB μ₁ ∘ R.symm from rfl,
      deriv_comp _ hfd0 hRd0]
    exact mul_ne_zero (LiZhongQC.deriv_ne_zero_of_injOn isOpen_ball hfd hfi (hRmaps (mem_ball_self one_pos)))
      (LiZhongQC.deriv_ne_zero_of_injOn isOpen_ball hRD.1 hRD.2.1 (mem_ball_self one_pos))
  set c₀ := -(κ⁻¹ * fB μ₁ (R.symm 0)) with hc₀
  have hk : κ⁻¹ ≠ 0 := inv_ne_zero hκ
  -- the explicit welding pair
  have hFR : IsQuasiconformal (F₁ ∘ R.symm) univ ∧ (F₁ ∘ R.symm) '' univ = univ := by
    obtain ⟨KF, hKF⟩ := hF₁q
    refine ⟨⟨KR * KF, thm7_1_comp (homeomorph_inverse_isKQC R hR) hKF (subset_univ _)⟩, ?_⟩
    rw [image_comp, image_univ.trans R.symm.surjective.range_eq, hF₁s]
  obtain ⟨hFq, hFs⟩ := a4_affine_qc hk (c := c₀) hFR.1 hFR.2
  obtain ⟨hGq, hGs⟩ := a4_affine_qc hk (c := c₀) hG₁q hG₁s
  have hfR : DifferentiableOn ℂ (fun z => fB μ₁ (R.symm z)) unitDisc := hfd.comp hRD.1 hRmaps
  have hWP : IsWeldingPrime (fun z => sigmaW w' (finPart (gammaMu μ' z)))
      (fun z => κ⁻¹ * fB μ₁ (R.symm z) + c₀) (fun z => κ⁻¹ * gMu μ₁ z + c₀) := by
    refine ⟨⟨fun z => κ⁻¹ * (F₁ ∘ R.symm) z + c₀, fun z => κ⁻¹ * G₁ z + c₀, hFq, hFs, ?_, hGq, hGs, ?_, ?_⟩,
      (hfR.const_mul κ⁻¹).add_const c₀, ?_, ?_, ?_, ?_⟩
    · intro z hz
      show κ⁻¹ * F₁ (R.symm z) + c₀ = κ⁻¹ * fB μ₁ (R.symm z) + c₀
      rw [hF₁f (hRmaps hz)]
    · intro z hz
      show κ⁻¹ * G₁ z + c₀ = κ⁻¹ * gMu μ₁ z + c₀
      rw [hG₁g hz]
    · intro z hz
      show κ⁻¹ * G₁ (sigmaW w' (finPart (gammaMu μ' z))) + c₀ = κ⁻¹ * F₁ (R.symm z) + c₀
      rw [hpart z hz]
      have h := hbd (R.symm z) (a4_R_circle hRE hRD hz)
      rw [hα] at h
      have h' : G₁ (wA μ₁ (R.symm z)) = F₁ (R.symm z) := OnePoint.coe_injective h
      rw [h']
    · intro x hx y hy hxy
      have h1 : fB μ₁ (R.symm x) = fB μ₁ (R.symm y) := by
        have : κ⁻¹ * (fB μ₁ (R.symm x) - fB μ₁ (R.symm y)) = 0 := by linear_combination hxy
        exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left hk)
      exact hRD.2.1 hx hy (hfi (hRmaps hx) (hRmaps hy) h1)
    · show κ⁻¹ * fB μ₁ (R.symm 0) + -(κ⁻¹ * fB μ₁ (R.symm 0)) = 0
      ring
    · have hd := (hfd0.comp (0 : ℂ) hRd0).hasDerivAt
      have h2 := (hd.const_mul κ⁻¹).add_const c₀
      rw [show (fun z => κ⁻¹ * fB μ₁ (R.symm z) + c₀) = (fun x => κ⁻¹ * (fB μ₁ ∘ R.symm) x + c₀) from rfl,
        h2.deriv]
      show κ⁻¹ * deriv (fB μ₁ ∘ R.symm) 0 = 1
      rw [show (fB μ₁ ∘ R.symm) = fun z => fB μ₁ (R.symm z) from rfl, ← hκdef]
      exact inv_mul_cancel₀ hκ
    · refine ⟨(hgU.1.const_mul κ⁻¹).add_const c₀, ?_, ?_⟩
      · intro x hx y hy hxy
        have : κ⁻¹ * (gMu μ₁ x - gMu μ₁ y) = 0 := by linear_combination hxy
        exact hgU.2.1 hx hy (sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left hk))
      · have ht := tendsto_affine_cobounded hk c₀
        rw [Metric.cobounded_eq_cocompact] at ht
        exact ht.comp hgU.2.2
  -- uniqueness against the fibre welding of the partner
  have hFW := fiber_welding hμ' hw'
  dsimp only at hFW
  obtain ⟨hOF, hWP', -⟩ := hFW
  have hh : (fun z => sigmaW w' (finPart (gammaMu μ' z))) '' unitCircle = unitCircle := by
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact tce_circle_norm hOF.1 hz
    · intro hy
      obtain ⟨z, hz, hze⟩ := tmi_circle_surj hOF.1.1 (show ‖y‖ = 1 from hy)
      exact ⟨z, hz, hze⟩
  refine ⟨κ⁻¹, c₀, hk, ?_⟩
  exact (weldingPrime_pair_unique hh hWP' hWP).1

/-- **R2.** The interior map of a partner is the reflection of the inverted exterior map. -/
theorem a4_sharp_betaHat {p p' : T1} {w w' : ℂ} (hw : w ∈ unitDiscExterior) (hw' : w' ∈ unitDiscExterior)
    (hcirc : ∀ z ∈ unitCircle, finPart (sigmaSphere (w' : ExtPlane) (gammaMu (Quotient.out p' : LinfStarBall)
      (finPart (sigmaSphere (w : ExtPlane) (gammaMu (Quotient.out p : LinfStarBall) z))))) = z)
    {φ : ℂ → ℂ} {b : ℂ} (hφ : DifferentiableOn ℂ φ unitDisc) (hφ0 : φ 0 = 0) (hφ1 : deriv φ 0 = 1) (hb : b ≠ 0)
    (he : ∀ s ∈ unitDisc, s ≠ 0 → weldG (Quotient.out p : LinfStarBall) w (1 / s) = b / φ s) :
    ∀ z ∈ unitDisc, betaHat p' w' z = conj (preSchwarzian φ (conj z)) := by
  have hμ := (Quotient.out p : LinfStarBall).2
  have hμ' := (Quotient.out p' : LinfStarBall).2
  obtain ⟨R, KR, hR, hRE, hRD, hRb⟩ := tcg_sigma_extension (show (w : ExtPlane) ∈ extDiscExterior from
    Or.inl ⟨w, hw, rfl⟩)
  obtain ⟨a, c, ha, hEq⟩ := a4_weldF_partner hμ hμ' hw hw' hR hRE hRD hRb hcirc
  intro z hz
  have _h := hφ0
  have _h1 := hφ1
  show preSchwarzian (weldF (Quotient.out p' : LinfStarBall) w') z = _
  rw [s2c_pre_congr hEq isOpen_ball hz, preSchwarzian_add_const, s2c_pre_const_mul ha]
  exact a4_pre_reflect hμ hw hRE hRD hRb hφ hb he hz

/-- **R3'.** Partnership is symmetric. -/
theorem a4_sharp_symm {p p' : T1} {w w' : ℂ} (hw : w ∈ unitDiscExterior) (hw' : w' ∈ unitDiscExterior)
    (hcirc : ∀ z ∈ unitCircle, finPart (sigmaSphere (w' : ExtPlane) (gammaMu (Quotient.out p' : LinfStarBall)
      (finPart (sigmaSphere (w : ExtPlane) (gammaMu (Quotient.out p : LinfStarBall) z))))) = z) :
    ∀ z ∈ unitCircle, finPart (sigmaSphere (w : ExtPlane) (gammaMu (Quotient.out p : LinfStarBall)
      (finPart (sigmaSphere (w' : ExtPlane) (gammaMu (Quotient.out p' : LinfStarBall) z))))) = z := by
  have _hw' := hw'
  have hμ := (Quotient.out p : LinfStarBall).2
  have hFW := fiber_welding hμ hw
  dsimp only at hFW
  obtain ⟨hOF, -, -⟩ := hFW
  intro y hy
  obtain ⟨z, hz, rfl⟩ := tmi_circle_surj hOF.1.1 (show ‖y‖ = 1 from hy)
  have hz' : z ∈ unitCircle := hz
  rw [← a4_h_eq hμ hw hz', hcirc z hz']

/-- **R4.** Reflection `ψ ↦ conj ∘ ψ ∘ conj` preserves the `A₂¹(𝔻)` norm. -/
theorem a4_conj_normA21 (ψ : ℂ → ℂ) : normA21 unitDisc (fun z => conj (ψ (conj z))) = normA21 unitDisc ψ := by
  unfold normA21
  congr 1
  have hemb : MeasurableEmbedding (⇑Complex.conjLIE) := Complex.conjLIE.toHomeomorph.measurableEmbedding
  have hpre : (⇑Complex.conjLIE) ⁻¹' unitDisc = unitDisc := by
    ext w
    simp [unitDisc]
  have h := (Complex.conjLIE.measurePreserving).setLIntegral_comp_preimage_emb hemb
    (fun w => (‖ψ w‖₊ : ℝ≥0∞) ^ 2) unitDisc
  rw [hpre] at h
  rw [← h]
  refine lintegral_congr (fun w => ?_)
  simp

/-- **R4b.** Reflection preserves `A₂¹(𝔻)`. -/
theorem a4_conj_A21 {ψ : ℂ → ℂ} (hψ : ψ ∈ A21fun unitDisc) : (fun z => conj (ψ (conj z))) ∈ A21fun unitDisc := by
  exact ⟨a55_conj_diff hψ.1, (a4_conj_normA21 ψ).symm ▸ hψ.2⟩

/-- A partner of a point of `𝒯₀(1)` lies over `T₀(1)`. -/
theorem a4_sharp_T01 {p p' : T1} (hp : p ∈ T01) {w w' : ℂ} (hw : w ∈ unitDiscExterior)
    (hw' : w' ∈ unitDiscExterior)
    (hcirc : ∀ z ∈ unitCircle, finPart (sigmaSphere (w' : ExtPlane) (gammaMu (Quotient.out p' : LinfStarBall)
      (finPart (sigmaSphere (w : ExtPlane) (gammaMu (Quotient.out p : LinfStarBall) z))))) = z) :
    p' ∈ T01 := by
  obtain ⟨φ, b, hφd, -, hφ0, hφ1, hb, he⟩ := a4_inv_data (Quotient.out p : LinfStarBall).2 hw
  have hA := a4_conj_A21 (a4_inv_pre_A21 hp hw hφd hb he)
  have hβ := a4_sharp_betaHat hw hw' hcirc hφd hφ0 hφ1 hb he
  exact (appa_betaHat_spec p' hw').1.mp (a21_congr_on measurableSet_ball hA fun z hz => (hβ z hz).symm)

/-- (iii) for a sequence transfers to (ii) for partners. -/
theorem a4_sharp_transfer {p p' : ℕ → T1} {w w' : ℕ → ℂ} {q q' : T1} {v v' : ℂ}
    (hw : ∀ n, w n ∈ unitDiscExterior) (hw' : ∀ n, w' n ∈ unitDiscExterior)
    (hv : v ∈ unitDiscExterior) (hv' : v' ∈ unitDiscExterior)
    (hc : ∀ n, ∀ z ∈ unitCircle, finPart (sigmaSphere (w' n : ExtPlane) (gammaMu (Quotient.out (p' n) : LinfStarBall)
      (finPart (sigmaSphere (w n : ExtPlane) (gammaMu (Quotient.out (p n) : LinfStarBall) z))))) = z)
    (hcq : ∀ z ∈ unitCircle, finPart (sigmaSphere (v' : ExtPlane) (gammaMu (Quotient.out q' : LinfStarBall)
      (finPart (sigmaSphere (v : ExtPlane) (gammaMu (Quotient.out q : LinfStarBall) z))))) = z)
    (h : Tendsto (fun n => normA21 unitDiscExterior (fun z =>
        (preSchwarzian (weldG (Quotient.out (p n) : LinfStarBall) (w n)) z -
            2 * deriv (weldG (Quotient.out (p n) : LinfStarBall) (w n)) z /
              weldG (Quotient.out (p n) : LinfStarBall) (w n) z + 2 / z) -
          (preSchwarzian (weldG (Quotient.out q : LinfStarBall) v) z -
            2 * deriv (weldG (Quotient.out q : LinfStarBall) v) z / weldG (Quotient.out q : LinfStarBall) v z +
              2 / z))) atTop (𝓝 0)) :
    Tendsto (fun n => normA21 unitDisc (fun z => betaHat (p' n) (w' n) z - betaHat q' v' z)) atTop (𝓝 0) := by
  choose φ b hφd hφne hφ0 hφ1 hb he using fun n => a4_inv_data (Quotient.out (p n) : LinfStarBall).2 (hw n)
  obtain ⟨φ₀, b₀, hφ₀d, -, hφ₀0, hφ₀1, hb₀, he₀⟩ := a4_inv_data (Quotient.out q : LinfStarBall).2 hv
  have hpair := fun n => a4_weld_pair (Quotient.out (p n) : LinfStarBall).2 (hw n)
  have hpair₀ := a4_weld_pair (Quotient.out q : LinfStarBall).2 hv
  refine h.congr fun n => ?_
  rw [a4_lg_norm (hpair n).2.2.2.2.1 hpair₀.2.2.2.2.1 (a4_pair_ne_zero (hpair n)) (a4_pair_ne_zero hpair₀)
    (hb n) hb₀ (he n) he₀, ← a4_conj_normA21]
  apply a4_normA21_congr
  intro z hz
  show conj (preSchwarzian (φ n) (conj z) - preSchwarzian φ₀ (conj z)) = betaHat (p' n) (w' n) z - betaHat q' v' z
  rw [a4_sharp_betaHat (hw n) (hw' n) (hc n) (hφd n) (hφ0 n) (hφ1 n) (hb n) (he n) z hz,
    a4_sharp_betaHat hv hv' hcq hφ₀d hφ₀0 hφ₀1 hb₀ he₀ z hz, map_sub]

/-- **R5.** (iii) ⇒ (i) of Corollary A.4. -/
theorem a4_iii_imp_i {p : ℕ → T1} {w : ℕ → ℂ} {q : T1} {v : ℂ} (hp : ∀ n, p n ∈ T01)
    (hw : ∀ n, w n ∈ unitDiscExterior) (hq : q ∈ T01) (hv : v ∈ unitDiscExterior)
    (h : Tendsto (fun n => normA21 unitDiscExterior (fun z =>
        (preSchwarzian (weldG (Quotient.out (p n) : LinfStarBall) (w n)) z -
            2 * deriv (weldG (Quotient.out (p n) : LinfStarBall) (w n)) z /
              weldG (Quotient.out (p n) : LinfStarBall) (w n) z + 2 / z) -
          (preSchwarzian (weldG (Quotient.out q : LinfStarBall) v) z -
            2 * deriv (weldG (Quotient.out q : LinfStarBall) v) z / weldG (Quotient.out q : LinfStarBall) v z +
              2 / z))) atTop (𝓝 0)) :
    @Tendsto _ _ (fun n => (p n, ((gMu (Quotient.out (p n) : LinfStarBall) (w n) : ℂ) : ExtPlane))) atTop
      (@nhds _ (@instTopologicalSpaceProd _ _ hilbertTopology inferInstance)
        (q, ((gMu (Quotient.out q : LinfStarBall) v : ℂ) : ExtPlane))) := by
  choose p' w' hw' hc using fun n => a4_sharp_exists (p := p n) (hw n)
  obtain ⟨q', v', hv', hcq⟩ := a4_sharp_exists (p := q) hv
  have hp' : ∀ n, p' n ∈ T01 := fun n => a4_sharp_T01 (hp n) (hw n) (hw' n) (hc n)
  have hq' : q' ∈ T01 := a4_sharp_T01 hq hv hv' hcq
  -- the partners converge
  have h2 := a4_sharp_transfer hw hw' hv hv' hc hcq h
  have hlim' := a4_ii_imp_i hp' hw' hq' hv' h2
  -- hence (iii) for the partners, and back
  have h3 := a4_i_imp_iii hp' hw' hq' hv' hlim'
  have h4 := a4_sharp_transfer hw' hw hv' hv (fun n => a4_sharp_symm (hw n) (hw' n) (hc n))
    (a4_sharp_symm hv hv' hcq) h3
  exact a4_ii_imp_i hp hw hq hv h4

/-- **S5.** (i) ⇔ (iii) of Corollary A.4, by the inversion `γ ↦ γ⁻¹` of the paper (sub-interface to follow). -/
theorem a4_i_iff_iii {p : ℕ → T1} {w : ℕ → ℂ} {q : T1} {v : ℂ} (hp : ∀ n, p n ∈ T01)
    (hw : ∀ n, w n ∈ unitDiscExterior) (hq : q ∈ T01) (hv : v ∈ unitDiscExterior) :
    @Tendsto _ _ (fun n => (p n, ((gMu (Quotient.out (p n) : LinfStarBall) (w n) : ℂ) : ExtPlane))) atTop
        (@nhds _ (@instTopologicalSpaceProd _ _ hilbertTopology inferInstance)
          (q, ((gMu (Quotient.out q : LinfStarBall) v : ℂ) : ExtPlane))) ↔
      Tendsto (fun n => normA21 unitDiscExterior (fun z =>
        (preSchwarzian (weldG (Quotient.out (p n) : LinfStarBall) (w n)) z -
            2 * deriv (weldG (Quotient.out (p n) : LinfStarBall) (w n)) z /
              weldG (Quotient.out (p n) : LinfStarBall) (w n) z + 2 / z) -
          (preSchwarzian (weldG (Quotient.out q : LinfStarBall) v) z -
            2 * deriv (weldG (Quotient.out q : LinfStarBall) v) z / weldG (Quotient.out q : LinfStarBall) v z +
              2 / z))) atTop (𝓝 0) := by
  exact ⟨a4_i_imp_iii hp hw hq hv, a4_iii_imp_i hp hw hq hv⟩

/-- Byte-identical copy of `cor_A_4` (assembly). -/
theorem a4_cor_A_4 {p : ℕ → T1} {w : ℕ → ℂ} {q : T1} {v : ℂ} (hp : ∀ n, p n ∈ T01)
    (hw : ∀ n, w n ∈ unitDiscExterior) (hq : q ∈ T01) (hv : v ∈ unitDiscExterior) :
    let μ : ℕ → LinfStar := fun n => (Quotient.out (p n) : LinfStarBall)
    let ν : LinfStar := (Quotient.out q : LinfStarBall)
    let lg : (ℂ → ℂ) → ℂ → ℂ := fun g z => preSchwarzian g z - 2 * deriv g z / g z + 2 / z
    [@Tendsto _ _ (fun n => (p n, ((gMu (μ n) (w n) : ℂ) : ExtPlane))) atTop
        (@nhds _ (@instTopologicalSpaceProd _ _ hilbertTopology inferInstance) (q, ((gMu ν v : ℂ) : ExtPlane))),
      Tendsto (fun n => normA21 unitDisc (fun z => betaHat (p n) (w n) z - betaHat q v z)) atTop (𝓝 0),
      Tendsto (fun n => normA21 unitDiscExterior (fun z => lg (weldG (μ n) (w n)) z - lg (weldG ν v) z)) atTop
        (𝓝 0)].TFAE := by
  intro μ ν lg
  have hν := (Quotient.out q : LinfStarBall).2
  have hβq : betaHat q v ∈ A21fun unitDisc := (appa_betaHat_spec q hv).1.mpr hq
  have hβp : ∀ n, betaHat (p n) (w n) ∈ A21fun unitDisc := fun n => (appa_betaHat_spec (p n) (hw n)).1.mpr (hp n)
  have hSeq : ∀ n, normA2 unitDisc (fun z => schwarzianHol (fsans (μ n)) z - schwarzianHol (fsans ν) z) =
      normA2 unitDisc (fun z => PsiOp (betaHat (p n) (w n)) z - PsiOp (betaHat q v) z) := fun n => by
    apply normA2_congr measurableSet_ball
    intro z hz
    show _ = PsiOp (betaHat (p n) (w n)) z - PsiOp (betaHat q v) z
    rw [ac2_psi_betaHat (p n) (hw n) hz, ac2_psi_betaHat q hv hz]
  tfae_have 1 ↔ 3 := a4_i_iff_iii hp hw hq hv
  tfae_have 1 → 2 := by
    intro h
    let _ : TopologicalSpace T1 := hilbertTopology
    have hpl : Tendsto p atTop (𝓝 q) := (continuous_fst.tendsto _).comp h
    have hpt := (a4_point_tendsto_iff hw hv hpl).mp ((continuous_snd.tendsto _).comp h)
    obtain ⟨hfd, -, hfne⟩ := weldF_regular_of_avoids_pole hν v (appa_pole hν hv)
    have hS := ((a4_T01_tendsto_iff hp hq).mp hpl).congr hSeq
    exact a4_inverse (f := weldF ν v) hfd hfne (weldF_normalization ν v).2 hβq hβp hS hpt
  tfae_have 2 → 1 := by
    intro h
    let _ : TopologicalSpace T1 := hilbertTopology
    -- `Ψ` is continuous `A₂¹ → A₂`
    have hS : Tendsto (fun n => normA2 unitDisc (fun z => PsiOp (betaHat (p n) (w n)) z - PsiOp (betaHat q v) z))
        atTop (𝓝 0) := by
      refine tendsto_order.2 ⟨fun a ha => absurd ha not_lt_zero, fun a ha => ?_⟩
      obtain ⟨ε, -, hε0, hεa⟩ := ENNReal.lt_iff_exists_real_btwn.mp ha
      have hε : 0 < ε := ENNReal.ofReal_pos.mp hε0
      obtain ⟨δ, hδ, hcont⟩ := ac2_psi_cont_disc hβq ε hε
      filter_upwards [(tendsto_order.1 h).2 _ (ENNReal.ofReal_pos.mpr hδ)] with n hn
      exact (hcont _ (hβp n) hn).trans hεa
    have hpl : Tendsto p atTop (𝓝 q) := (a4_T01_tendsto_iff hp hq).mpr (hS.congr fun n => (hSeq n).symm)
    -- the values at `0` (Lemma 1.3 at `z = 0`)
    have h0 : Tendsto (fun n => betaHat (p n) (w n) 0) atTop (𝓝 (betaHat q v 0)) := by
      rw [Metric.tendsto_atTop]
      intro ε hε
      have hπ : 0 < Real.sqrt π := Real.sqrt_pos.mpr Real.pi_pos
      obtain ⟨N, hN⟩ := (tendsto_order.1 h).2 _ (ENNReal.ofReal_pos.mpr (mul_pos hε hπ)) |>.exists_forall_of_atTop
      refine ⟨N, fun n hn => ?_⟩
      have hd : (fun z => betaHat (p n) (w n) z - betaHat q v z) ∈ A21fun unitDisc := by
        have h2 := a21_add measurableSet_ball (hβp n) (a21_const_mul measurableSet_ball hβq (-1))
        refine (ab112_A21fun_congr (U := unitDisc) isOpen_ball (fun z _ => ?_)).mp h2
        ring
      have hb := lemma_1_3 (Or.inl rfl) hd 0 (mem_ball_self one_pos)
      have he : ENNReal.ofReal (ε * Real.sqrt π) * ENNReal.ofReal (1 / Real.sqrt π) = ENNReal.ofReal ε := by
        rw [← ENNReal.ofReal_mul (by positivity)]
        congr 1
        field_simp
      have hlt : ENNReal.ofReal ‖(1 - ((‖(0 : ℂ)‖ : ℝ) : ℂ) ^ 2) * (betaHat (p n) (w n) 0 - betaHat q v 0)‖ <
          ENNReal.ofReal ε := by
        refine hb.trans_lt ?_
        rw [mul_comm, ← he]
        exact ENNReal.mul_lt_mul_left (ENNReal.ofReal_pos.mpr (by positivity : (0 : ℝ) < 1 / Real.sqrt π)).ne' ENNReal.ofReal_ne_top (hN n hn)
      rw [ENNReal.ofReal_lt_ofReal_iff hε] at hlt
      simpa [dist_eq_norm] using hlt
    have hpt := (a4_point_tendsto_iff hw hv hpl).mpr h0
    exact hpl.prodMk_nhds hpt
  tfae_finish

/-- **Corollary A.4** (TT:5858–5918). Let `γ_n = g_n⁻¹ ∘ f_n` and `γ = g⁻¹ ∘ f` be points of `𝒯₀(1)`. The following
are equivalent:
- (i) `γ_n → γ` in the topology of `𝒯₀(1)`;
- (ii) `𝒜(f_n) → 𝒜(f)` in `A₂¹(𝔻)`;
- (iii) `𝒜(g_n) - 2g_n'/g_n + 2/z → 𝒜(g) - 2g'/g + 2/z` in `A₂¹(𝔻*)`. -/
theorem cor_A_4 {p : ℕ → T1} {w : ℕ → ℂ} {q : T1} {v : ℂ} (hp : ∀ n, p n ∈ T01)
    (hw : ∀ n, w n ∈ unitDiscExterior) (hq : q ∈ T01) (hv : v ∈ unitDiscExterior) :
    let μ : ℕ → LinfStar := fun n => (Quotient.out (p n) : LinfStarBall)
    let ν : LinfStar := (Quotient.out q : LinfStarBall)
    let lg : (ℂ → ℂ) → ℂ → ℂ := fun g z => preSchwarzian g z - 2 * deriv g z / g z + 2 / z
    [@Tendsto _ _ (fun n => (p n, ((gMu (μ n) (w n) : ℂ) : ExtPlane))) atTop
        (@nhds _ (@instTopologicalSpaceProd _ _ hilbertTopology inferInstance) (q, ((gMu ν v : ℂ) : ExtPlane))),
      Tendsto (fun n => normA21 unitDisc (fun z => betaHat (p n) (w n) z - betaHat q v z)) atTop (𝓝 0),
      Tendsto (fun n => normA21 unitDiscExterior (fun z => lg (weldG (μ n) (w n)) z - lg (weldG ν v) z)) atTop
        (𝓝 0)].TFAE := by
  exact a4_cor_A_4 hp hw hq hv

end AppA

end TakhtajanTeo
