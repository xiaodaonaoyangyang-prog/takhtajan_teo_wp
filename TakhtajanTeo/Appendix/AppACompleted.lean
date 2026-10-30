import TakhtajanTeo.Appendix.A_HilbertStructure
import TakhtajanTeo.Ch2.S1_Theorem112Completed
import TakhtajanTeo.Ch1.HilbertChosenReflection
import TakhtajanTeo.Ch1.QuasidiskKernel

/-!
# Appendix A completed originals (`appa_` copies)

- `appa_betaHat_spec` is `betaHat_spec` (TT:5768): by Theorem 1.12 and the Möbius rule
  `𝒜(λ_c ∘ f) = 𝒜(f) - 2c f'/(cf + 1)`, whose correction term is in `A₂¹(𝔻)` because `g_μ(w)` lies at positive
  distance from `f(𝔻)` (`hc6_welding_quasidisc`) and `∬_𝔻 |f'|² = area(f(𝔻)) < ∞`.
- `appa_thm_A_3` is `thm_A_3` (TT:5804–5856): `thm_A_3_of_pole_and_A21` with the pole premise from the disjointness of
  the welding domains.
-/

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal ComplexConjugate Classical Real NNReal

noncomputable section

namespace TakhtajanTeo

open LiZhongQC Ch2

namespace AppA

/-- The welding value `g_μ(w)` (`w ∈ 𝔻*`) lies outside the closure of `f^μ(𝔻)`, and `f^μ(𝔻)` is bounded. -/
theorem appa_gMu_not_mem_closure {μ : LinfStar} (hμ : μ ∈ LinfStarBall) {w : ℂ} (hw : w ∈ unitDiscExterior) :
    gMu μ w ∉ closure (fB μ '' unitDisc) ∧ Bornology.IsBounded (fB μ '' unitDisc) := by
  obtain ⟨K, -, -, hb, hext⟩ := hc6_welding_quasidisc hμ
  rw [S2C.s2c_fsans_eq hμ] at hb hext
  rw [S2C.s2c_gsans_eq hμ] at hext
  refine ⟨?_, hb⟩
  have : gMu μ w ∈ (closure (fB μ '' unitDisc))ᶜ := hext ▸ ⟨w, hw, rfl⟩
  exact this

/-- The pole premise of Theorem A.3: `c f^μ(z) + 1 ≠ 0` on `𝔻`, `c = -1/g_μ(w)`. -/
theorem appa_pole {μ : LinfStar} (hμ : μ ∈ LinfStarBall) {w : ℂ} (hw : w ∈ unitDiscExterior) :
    ∀ z ∈ unitDisc, (-1 / gMu μ w) * fB μ z + 1 ≠ 0 := by
  apply weldF_avoids_pole_of_excluded_value
  intro z hz he
  exact (appa_gMu_not_mem_closure hμ hw).1 (he ▸ subset_closure ⟨z, hz, rfl⟩)

/-- `𝒜(λ_c ∘ F) = 𝒜(F) - 2c F'/(cF + 1)` on an open set where `cF + 1 ≠ 0` and `F' ≠ 0`. -/
theorem appa_preSchwarzian_lambdaW {F : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U) (hF : DifferentiableOn ℂ F U)
    {c : ℂ} (hpole : ∀ z ∈ U, c * F z + 1 ≠ 0) {z : ℂ} (hz : z ∈ U) (hF' : deriv F z ≠ 0) :
    preSchwarzian (fun z => lambdaW c (F z)) z =
      preSchwarzian F z - 2 * c * deriv F z / (c * F z + 1) := by
  have hd1 : ∀ y ∈ U, HasDerivAt (fun z => lambdaW c (F z)) (deriv F y / (c * F y + 1) ^ 2) y := by
    intro y hy
    have hFd := (hF.differentiableAt (hU.mem_nhds hy)).hasDerivAt
    have h := (lambdaW_hasDerivAt c (F y) (hpole y hy)).comp y hFd
    exact h.congr_deriv (by ring)
  have hev : deriv (fun z => lambdaW c (F z)) =ᶠ[𝓝 z] fun y => deriv F y / (c * F y + 1) ^ 2 := by
    filter_upwards [hU.mem_nhds hz] with y hy
    exact (hd1 y hy).deriv
  have hF1 : HasDerivAt F (deriv F z) z := (hF.differentiableAt (hU.mem_nhds hz)).hasDerivAt
  have hF2 : HasDerivAt (deriv F) (deriv (deriv F) z) z :=
    ((hF.deriv hU).differentiableAt (hU.mem_nhds hz)).hasDerivAt
  have hden : HasDerivAt (fun y => (c * F y + 1) ^ 2) (2 * (c * F z + 1) * (c * deriv F z)) z := by
    have := ((hF1.const_mul c).add_const 1).pow 2
    convert this using 1
    push_cast; ring
  have hq : HasDerivAt (fun y => deriv F y / (c * F y + 1) ^ 2) _ z :=
    hF2.div hden (pow_ne_zero 2 (hpole z hz))
  have hd2 : deriv (deriv (fun z => lambdaW c (F z))) z =
      (deriv (deriv F) z * (c * F z + 1) ^ 2 - deriv F z * (2 * (c * F z + 1) * (c * deriv F z))) /
        ((c * F z + 1) ^ 2) ^ 2 := by
    rw [hev.deriv_eq, hq.deriv]
  unfold preSchwarzian
  rw [hd2, (hd1 z hz).deriv]
  have hp := hpole z hz
  field_simp
  try ring

/-- The correction term `2c F'/(cF + 1)` of the Möbius rule lies in `A₂¹(𝔻)`. -/
theorem appa_correction_mem {μ : LinfStar} (hμ : μ ∈ LinfStarBall) {w : ℂ} (hw : w ∈ unitDiscExterior) :
    (fun z => 2 * (-1 / gMu μ w) * deriv (fB μ) z / ((-1 / gMu μ w) * fB μ z + 1)) ∈ A21fun unitDisc := by
  obtain ⟨hcl, hb⟩ := appa_gMu_not_mem_closure hμ hw
  have hB := fB_holomorphic_injective hμ
  have hpole := appa_pole hμ hw
  set a := gMu μ w with ha
  set c : ℂ := -1 / a with hc
  have ha0 : a ≠ 0 := by
    intro h
    apply hcl
    rw [h]
    exact subset_closure ⟨0, mem_ball_self one_pos, (fB_normalization μ).1⟩
  -- distance from `a` to `f(𝔻)`
  obtain ⟨d, hd0, hd⟩ : ∃ d > 0, ∀ z ∈ unitDisc, d ≤ ‖a - fB μ z‖ := by
    have hne : (closure (fB μ '' unitDisc)).Nonempty :=
      ⟨fB μ 0, subset_closure ⟨0, mem_ball_self one_pos, rfl⟩⟩
    have hpos : 0 < infDist a (closure (fB μ '' unitDisc)) :=
      (isClosed_closure.notMem_iff_infDist_pos hne).mp hcl
    refine ⟨_, hpos, fun z hz => ?_⟩
    rw [← dist_eq_norm]
    exact infDist_le_dist_of_mem (subset_closure ⟨z, hz, rfl⟩)
  have hden : ∀ z ∈ unitDisc, ‖c * fB μ z + 1‖ = ‖a - fB μ z‖ / ‖a‖ := by
    intro z hz
    rw [hc, show -1 / a * fB μ z + 1 = (a - fB μ z) / a by field_simp; ring, norm_div]
  have hdiff : DifferentiableOn ℂ (fun z => 2 * c * deriv (fB μ) z / (c * fB μ z + 1)) unitDisc :=
    ((hB.1.deriv isOpen_ball).const_mul _).div ((hB.1.const_mul _).add_const 1) hpole
  refine ⟨hdiff, ?_⟩
  -- the energy bound
  have hM : ∀ z ∈ unitDisc, ‖2 * c * deriv (fB μ) z / (c * fB μ z + 1)‖ ≤ (2 * ‖c‖ * ‖a‖ / d) * ‖deriv (fB μ) z‖ := by
    intro z hz
    have h1 := hd z hz
    rw [norm_div, norm_mul, norm_mul, hden z hz, Complex.norm_ofNat]
    have ha' : 0 < ‖a‖ := norm_pos_iff.mpr ha0
    have h2 : 0 < ‖a - fB μ z‖ := lt_of_lt_of_le hd0 h1
    rw [div_div_eq_mul_div, div_le_iff₀ h2]
    calc 2 * ‖c‖ * ‖deriv (fB μ) z‖ * ‖a‖ = (2 * ‖c‖ * ‖a‖ / d) * ‖deriv (fB μ) z‖ * d := by
          field_simp
      _ ≤ (2 * ‖c‖ * ‖a‖ / d) * ‖deriv (fB μ) z‖ * ‖a - fB μ z‖ := by gcongr
  have harea : ∫⁻ z in unitDisc, (‖deriv (fB μ) z‖₊ : ℝ≥0∞) ^ 2 < ∞ := by
    have h := r24_conformal_lintegral isOpen_ball hB.1 hB.2 (fun _ => (1 : ℝ≥0∞))
    simp only [mul_one, setLIntegral_const, one_mul] at h
    have hv : volume (fB μ '' unitDisc) < ∞ := hb.measure_lt_top
    calc ∫⁻ z in unitDisc, (‖deriv (fB μ) z‖₊ : ℝ≥0∞) ^ 2
        = ∫⁻ z in unitDisc, ENNReal.ofReal (‖deriv (fB μ) z‖ ^ 2) := by
          apply lintegral_congr; intro z
          rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm, enorm_eq_nnnorm]
      _ = volume (fB μ '' unitDisc) := h.symm
      _ < ∞ := hv
  have hfin : ∫⁻ z in unitDisc, (‖2 * c * deriv (fB μ) z / (c * fB μ z + 1)‖₊ : ℝ≥0∞) ^ 2 < ∞ := by
    calc ∫⁻ z in unitDisc, (‖2 * c * deriv (fB μ) z / (c * fB μ z + 1)‖₊ : ℝ≥0∞) ^ 2
        ≤ ∫⁻ z in unitDisc, ENNReal.ofReal ((2 * ‖c‖ * ‖a‖ / d) ^ 2) * (‖deriv (fB μ) z‖₊ : ℝ≥0∞) ^ 2 := by
          apply setLIntegral_mono' isOpen_ball.measurableSet
          intro z hz
          simp only [← enorm_eq_nnnorm, ← ofReal_norm]
          rw [← ENNReal.ofReal_pow (norm_nonneg _),
            ← ENNReal.ofReal_pow (norm_nonneg _), ← ENNReal.ofReal_mul (by positivity)]
          apply ENNReal.ofReal_le_ofReal
          rw [← mul_pow]
          exact pow_le_pow_left₀ (norm_nonneg _) (hM z hz) 2
      _ = ENNReal.ofReal ((2 * ‖c‖ * ‖a‖ / d) ^ 2) * ∫⁻ z in unitDisc, (‖deriv (fB μ) z‖₊ : ℝ≥0∞) ^ 2 :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ < ∞ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top harea
  unfold normA21
  exact ENNReal.rpow_lt_top_of_nonneg (by norm_num) hfin.ne

/-- `betaHat p w = 𝒜(f^μ) - (correction)` on `𝔻`. -/
theorem appa_betaHat_eq {μ : LinfStarBall} {w : ℂ} (hw : w ∈ unitDiscExterior) :
    EqOn (preSchwarzian (weldF (μ : LinfStar) w))
      (fun z => preSchwarzian (fB μ) z +
        -1 * (2 * (-1 / gMu μ w) * deriv (fB μ) z / ((-1 / gMu μ w) * fB μ z + 1))) unitDisc := by
  intro z hz
  have hB := fB_holomorphic_injective μ.2
  have h := appa_preSchwarzian_lambdaW isOpen_ball hB.1 (appa_pole μ.2 hw) hz
    (deriv_ne_zero_of_injOn isOpen_ball hB.1 hB.2 hz)
  change preSchwarzian (fun z => lambdaW (-1 / gMu μ w) (fB μ z)) z = _
  rw [h]
  ring

/-- **(TT:5768)** `betaHat_spec`, proved. -/
theorem appa_betaHat_spec (p : T1) {w : ℂ} (hw : w ∈ unitDiscExterior) :
    (betaHat p w ∈ A21fun unitDisc ↔ p ∈ T01) ∧
      EqOn (betaT p w).1 (PsiOp (betaHat p w)) unitDisc ∧ (betaT p w).2 = (1 / 2) * betaHat p w 0 := by
  set μ : LinfStarBall := Quotient.out p with hμ
  have hT := (thm_1_12 p).2.1
  rw [S2C.s2c_fsans_eq μ.2] at hT
  have hcorr := appa_correction_mem μ.2 hw
  have hcorr' := a21_const_mul measurableSet_ball hcorr (-1)
  refine ⟨?_, fun z _ => rfl, rfl⟩
  have heq := appa_betaHat_eq (μ := μ) hw
  change preSchwarzian (weldF (μ : LinfStar) w) ∈ A21fun unitDisc ↔ p ∈ T01
  rw [ab112_A21fun_congr (U := unitDisc) isOpen_ball heq, hT]
  constructor
  · intro h
    have h2 := a21_add measurableSet_ball h (a21_const_mul measurableSet_ball hcorr' (-1))
    refine (ab112_A21fun_congr (U := unitDisc) isOpen_ball (fun z _ => ?_)).mp h2
    ring
  · intro h
    exact a21_add measurableSet_ball h hcorr'

/-- **Theorem A.3** (TT:5804–5856), proved. -/
theorem appa_thm_A_3 {p : T1} (hp : p ∈ T01) {w : ℂ} (hw : w ∈ unitDiscExterior) :
    let f := weldF (Quotient.out p : LinfStarBall) w
    let ψ := betaHat p w
    (∀ ϕ ∈ A2fun unitDisc, ∀ c : ℂ,
      let φ : ℂ → ℂ := fun z => deriv f z * ((∫ t in (0 : ℝ)..1, ϕ (t * z) / deriv f (t * z) * z) + 2 * c)
      φ ∈ A21fun unitDisc ∧ EqOn (fun z => deriv φ z - ψ z * φ z) ϕ unitDisc ∧ (1 / 2) * φ 0 = c) ∧
      (∀ φ ∈ A21fun unitDisc, EqOn (fun z => deriv φ z - ψ z * φ z) 0 unitDisc → φ 0 = 0 → EqOn φ 0 unitDisc) ∧
      ∃ C : ℝ≥0∞, C < ∞ ∧ ∀ φ ∈ A21fun unitDisc,
        normA2 unitDisc (fun z => deriv φ z - ψ z * φ z) ≤ C * normA21 unitDisc φ :=
  thm_A_3_of_pole_and_A21 p w (appa_pole (Quotient.out p : LinfStarBall).2 hw)
    ((appa_betaHat_spec p hw).1.mpr hp)

/-- (TT:5768) By Theorem 1.12, `β̂(γ) ∈ A₂¹(𝔻)` iff `γ ∈ 𝒯₀(1)`. Moreover `β = Ψ̂ ∘ β̂` on `𝔻`, with
`Ψ̂(ψ) = (ψ' - ½ψ², ½ψ(0))`. -/
theorem betaHat_spec (p : T1) {w : ℂ} (hw : w ∈ unitDiscExterior) :
    (betaHat p w ∈ A21fun unitDisc ↔ p ∈ T01) ∧
      EqOn (betaT p w).1 (PsiOp (betaHat p w)) unitDisc ∧ (betaT p w).2 = (1 / 2) * betaHat p w 0 :=
  appa_betaHat_spec p hw

/-- **Theorem A.3** (TT:5804–5856). The embeddings `β : 𝒯₀(1) ↪ A₂(𝔻) ⊕ ℂ` and `β̂ : 𝒯₀(1) ↪ A₂¹(𝔻)` induce the same
Hilbert manifold structure. At `ψ = 𝒜(f) ∈ β̂(𝒯₀(1))`, `D_ψΨ̂(φ) = (φ' - ψφ, ½φ(0))` is a bounded bijection
`A₂¹(𝔻) → A₂(𝔻) ⊕ ℂ`:
- onto, with preimage `φ(z) = f'(z)(∫₀^z ϕ(u)/f'(u) du + 2c)` of `(ϕ, c)` (the integral along the segment `[0, z]`);
- one to one;
- bounded: `‖φ' - ψφ‖_{A₂} ≤ C ‖φ‖_{A₂¹}`. -/
theorem thm_A_3 {p : T1} (hp : p ∈ T01) {w : ℂ} (hw : w ∈ unitDiscExterior) :
    let f := weldF (Quotient.out p : LinfStarBall) w
    let ψ := betaHat p w
    (∀ ϕ ∈ A2fun unitDisc, ∀ c : ℂ,
      let φ : ℂ → ℂ := fun z => deriv f z * ((∫ t in (0 : ℝ)..1, ϕ (t * z) / deriv f (t * z) * z) + 2 * c)
      φ ∈ A21fun unitDisc ∧ EqOn (fun z => deriv φ z - ψ z * φ z) ϕ unitDisc ∧ (1 / 2) * φ 0 = c) ∧
      (∀ φ ∈ A21fun unitDisc, EqOn (fun z => deriv φ z - ψ z * φ z) 0 unitDisc → φ 0 = 0 → EqOn φ 0 unitDisc) ∧
      ∃ C : ℝ≥0∞, C < ∞ ∧ ∀ φ ∈ A21fun unitDisc,
        normA2 unitDisc (fun z => deriv φ z - ψ z * φ z) ≤ C * normA21 unitDisc φ :=
  appa_thm_A_3 hp hw

end AppA

end TakhtajanTeo
