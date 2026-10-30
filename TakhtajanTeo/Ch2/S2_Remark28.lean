import TakhtajanTeo.Ch2.S2_Completed5
import TakhtajanTeo.Ch2.S2_Completed6
import TakhtajanTeo.Ch2.S2_Remark22

/-!
# Ch2 §2: the sharp bound of Remark 2.8 (`ab28_` copy)

`remark_2_8` (`∬_Ω d²w/|z - w|⁴ ≤ (π/4) ρ₂(z)`), proved as `ab28_remark_2_8` with the statement of `remark_2_8`
byte-identical. Route (TT:4170–4186): `∬_Ω |w - g(ζ)|⁻⁴ = π² 𝖪₃(ζ, ζ)/|g'(ζ)|²` by the change of variables `w = f(v)`,
`𝖪₃(ζ, ζ) = 1/(π(|ζ|² - 1)²) - 𝖪₄(ζ, ζ) ≤ 1/(π(|ζ|² - 1)²)` by `eq_2_4`, and `λ_{Ω*}(g(ζ)) = 2/(|g'(ζ)|(|ζ|² - 1))`
from the inverted chart of `g1_inverted_exterior`. The `ab28_` lemmas are helpers.
-/

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal ComplexConjugate Classical Real
noncomputable section
namespace TakhtajanTeo
open LiZhongQC
namespace Ch2

theorem ab28_kk3_diag (f g : ℂ → ℂ) (u : ℂ) :
    kerKK3 f g u u = (((∫ v in unitDisc, ‖kerK3 f g u v‖ ^ 2 : ℝ)) : ℂ) := by
  have h : (fun v => kerK3 f g u v * conj (kerK3 f g u v)) =
      fun v => (((‖kerK3 f g u v‖ ^ 2 : ℝ)) : ℂ) := by
    funext v
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  unfold kerKK3
  rw [h]
  exact integral_ofReal

theorem ab28_kk4_diag (g : ℂ → ℂ) (u : ℂ) :
    kerKK4 g u u = (((∫ v in unitDiscExterior, ‖kerK4 g u v‖ ^ 2 : ℝ)) : ℂ) := by
  have h : (fun v => kerK4 g u v * conj (kerK4 g u v)) =
      fun v => (((‖kerK4 g u v‖ ^ 2 : ℝ)) : ℂ) := by
    funext v
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  unfold kerKK4
  rw [h]
  exact integral_ofReal

/-- Change of variables `w = f(v)` for the weight `|w - z|⁻⁴`. -/
theorem ab28_cov {f : ℂ → ℂ} (hfd : DifferentiableOn ℂ f unitDisc) (hfi : InjOn f unitDisc) (z : ℂ) :
    ∫ w in f '' unitDisc, 1 / ‖w - z‖ ^ 4 =
      ∫ v in unitDisc, ‖deriv f v‖ ^ 2 * (1 / ‖f v - z‖ ^ 4) := by
  have hm : MeasurableSet unitDisc := measurableSet_ball
  rw [integral_image_eq_integral_abs_det_fderiv_smul volume hm
    (fun v hv => ((hfd.differentiableAt (isOpen_ball.mem_nhds hv)).hasDerivAt.hasFDerivAt.restrictScalars
      ℝ).hasFDerivWithinAt) hfi]
  refine setIntegral_congr_fun measurableSet_ball fun v hv => ?_
  simp only [det_restrictScalars_toSpanSingleton]
  rw [abs_of_nonneg (sq_nonneg _), smul_eq_mul]

theorem ab28_int_bound {f g : ℂ → ℂ} (h : IsNormalizedDisjointPair f g)
    (hF : volume ((f '' unitDisc ∪ g '' unitDiscExterior)ᶜ) = 0) {u : ℂ} (hu : u ∈ unitDiscExterior) :
    ‖deriv g u‖ ^ 2 / π ^ 2 * ∫ w in f '' unitDisc, 1 / ‖w - g u‖ ^ 4 ≤
      1 / (π * (‖u‖ ^ 2 - 1) ^ 2) := by
  have h' := h
  obtain ⟨hfd, hfi, -⟩ := h
  have e24 := (eq_2_4 h' hF).2 u hu u hu
  rw [ab28_kk3_diag, ab28_kk4_diag] at e24
  have hmul : u * conj u = ((‖u‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have hB : 0 ≤ ∫ v in unitDiscExterior, ‖kerK4 g u v‖ ^ 2 :=
    integral_nonneg (fun v => by positivity)
  have hA : ((∫ v in unitDisc, ‖kerK3 f g u v‖ ^ 2 : ℝ) : ℂ) =
      ((1 / (π * (1 - ‖u‖ ^ 2) ^ 2) - ∫ v in unitDiscExterior, ‖kerK4 g u v‖ ^ 2 : ℝ) : ℂ) := by
    rw [e24, hmul]
    push_cast
    ring
  have hA' := Complex.ofReal_injective hA
  have hpt : ∀ v, ‖kerK3 f g u v‖ ^ 2 =
      ‖deriv g u‖ ^ 2 / π ^ 2 * (‖deriv f v‖ ^ 2 * (1 / ‖f v - g u‖ ^ 4)) := by
    intro v
    unfold kerK3
    simp only [norm_mul, norm_div, norm_pow, norm_one, Complex.norm_real,
      Real.norm_of_nonneg Real.pi_pos.le]
    rw [norm_sub_rev (g u) (f v)]
    ring
  have hint : ∫ v in unitDisc, ‖kerK3 f g u v‖ ^ 2 =
      ‖deriv g u‖ ^ 2 / π ^ 2 * ∫ w in f '' unitDisc, 1 / ‖w - g u‖ ^ 4 := by
    rw [ab28_cov hfd hfi (g u), ← integral_const_mul]
    exact integral_congr_ae (Eventually.of_forall fun v => hpt v)
  rw [← hint, hA']
  have h1 : (1 - ‖u‖ ^ 2) ^ 2 = (‖u‖ ^ 2 - 1) ^ 2 := by ring
  rw [h1]
  linarith

/-- The hyperbolic density of `Ω* = 𝗀(𝔻*)` at `𝗀(u)`, in the sphere chart: `λ = 2/(|𝗀'(u)|(|u|² - 1))`. -/
theorem ab28_density {μ : LinfStar} (hμ : μ ∈ LinfStarBall) {u : ℂ} (hu : u ∈ unitDiscExterior) :
    deriv (gsans μ) u ≠ 0 ∧
      poincareDensityNearInfty (gsans μ '' unitDiscExterior) (gsans μ u) =
        2 / (‖deriv (gsans μ) u‖ * (‖u‖ ^ 2 - 1)) := by
  have hpair := AppB.b8_welding_normalized_pair hμ
  obtain ⟨φ, b, hφd, hφi, hφ0, -, hb, -, hg⟩ := g1_inverted_exterior hpair
  have hGeq := s2c_chart_eq (g := gsans μ) hφi hφ0 hb hg
  have hu1 : 1 < ‖u‖ := hu
  have hun : 0 < ‖u‖ := by linarith
  have hu0 : u ≠ 0 := norm_pos_iff.1 hun
  have hs : u⁻¹ ∈ unitDisc := by
    refine mem_ball_zero_iff.2 ?_
    rw [norm_inv]
    exact inv_lt_one_of_one_lt₀ hu1
  have hs0 : u⁻¹ ≠ 0 := inv_ne_zero hu0
  have hφne : ∀ x ∈ unitDisc, x ≠ 0 → φ x ≠ 0 := fun x hx hx0 h =>
    hx0 (hφi hx (mem_ball_self one_pos) (h.trans hφ0.symm))
  have hgeq : ∀ v ∈ unitDiscExterior, gsans μ v = b / φ v⁻¹ := by
    intro v hv
    have hv1 : 1 < ‖v‖ := hv
    have hv0 : v ≠ 0 := norm_pos_iff.1 (by linarith)
    have hvs : v⁻¹ ∈ unitDisc := by
      refine mem_ball_zero_iff.2 ?_
      rw [norm_inv]
      exact inv_lt_one_of_one_lt₀ hv1
    have h1 := hg v⁻¹ hvs (inv_ne_zero hv0)
    rwa [one_div, inv_inv] at h1
  have hgu : gsans μ u = b / φ u⁻¹ := hgeq u hu
  have hφs : φ u⁻¹ ≠ 0 := hφne _ hs hs0
  have hφat : DifferentiableAt ℂ φ u⁻¹ := hφd.differentiableAt (isOpen_ball.mem_nhds hs)
  have hinv : HasDerivAt (fun v : ℂ => v⁻¹) (-(u ^ 2)⁻¹) u := hasDerivAt_inv hu0
  have hc : HasDerivAt (fun v : ℂ => φ v⁻¹) (deriv φ u⁻¹ * (-(u ^ 2)⁻¹)) u :=
    hφat.hasDerivAt.comp u hinv
  have hd := (hasDerivAt_const u b).div hc hφs
  have hev : gsans μ =ᶠ[𝓝 u] fun v => b / φ v⁻¹ := by
    filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds hu] with v hv
    exact hgeq v hv
  have hgd := hd.congr_of_eventuallyEq hev
  have hderiv : deriv (gsans μ) u = b * deriv φ u⁻¹ / (u ^ 2 * φ u⁻¹ ^ 2) := by
    rw [hgd.deriv]
    field_simp
    ring
  have hφ' : deriv φ u⁻¹ ≠ 0 := deriv_ne_zero_of_injOn isOpen_ball hφd hφi hs
  have hg'ne : deriv (gsans μ) u ≠ 0 := by
    rw [hderiv]
    exact div_ne_zero (mul_ne_zero hb hφ') (mul_ne_zero (pow_ne_zero 2 hu0) (pow_ne_zero 2 hφs))
  refine ⟨hg'ne, ?_⟩
  -- the chart
  set G : Set ℂ := (fun s => φ s / b) '' unitDisc with hGdef
  have hψ : IsConformalOnto (fun s => φ s / b) unitDisc G :=
    ⟨hφd.div_const b, fun x hx y hy h => hφi hx hy ((div_left_inj' hb).1 h), rfl⟩
  have hGopen : IsOpen G := hψ.isOpen isOpen_ball
  have hψs : IsConformalOnto (Function.invFunOn (fun s => φ s / b) unitDisc) G unitDisc :=
    hψ.symm isOpen_ball
  set z : ℂ := gsans μ u with hzdef
  set ζ : ℂ := z⁻¹ with hζ
  have hζψ : (fun s => φ s / b) u⁻¹ = ζ := by
    show φ u⁻¹ / b = z⁻¹
    rw [hgu, inv_div]
  have hζG : ζ ∈ G := ⟨u⁻¹, hs, hζψ⟩
  have hdens : poincareDensityNearInfty (gsans μ '' unitDiscExterior) z =
      poincareDensity G ζ / ‖z‖ ^ 2 := by
    unfold poincareDensityNearInfty
    rw [← hGeq]
  have hPD := (poincareDensity_well_defined hGopen hψs hψs hζG).2
  have hleft : Function.invFunOn (fun s => φ s / b) unitDisc ζ = u⁻¹ := by
    rw [← hζψ]
    exact hψ.2.1.leftInvOn_invFunOn hs
  have hψat : HasDerivAt (fun s => φ s / b) (deriv φ u⁻¹ / b) u⁻¹ := hφat.hasDerivAt.div_const b
  have hψat' : HasDerivAt (fun s => φ s / b) (deriv φ u⁻¹ / b)
      (Function.invFunOn (fun s => φ s / b) unitDisc ζ) := by
    rw [hleft]
    exact hψat
  have hcont : ContinuousAt (Function.invFunOn (fun s => φ s / b) unitDisc) ζ :=
    (hψs.1.differentiableAt (hGopen.mem_nhds hζG)).continuousAt
  have hfg : ∀ᶠ y in 𝓝 ζ, (fun s => φ s / b) (Function.invFunOn (fun s => φ s / b) unitDisc y) = y := by
    filter_upwards [hGopen.mem_nhds hζG] with y hy
    exact Function.invFunOn_eq hy
  have hdinv := HasDerivAt.of_local_left_inverse hcont hψat' (div_ne_zero hφ' hb) hfg
  rw [hdens, hPD, hdinv.deriv, hleft]
  -- real arithmetic
  have hZ : 0 < ‖z‖ := by
    exact norm_pos_iff.2 (by rw [hgu]; exact div_ne_zero hb hφs)
  have hF : ‖z‖ * ‖φ u⁻¹‖ = ‖b‖ := by
    rw [hgu, norm_div]
    have : ‖φ u⁻¹‖ ≠ 0 := norm_ne_zero_iff.2 hφs
    exact div_mul_cancel₀ _ this
  have hbn : 0 < ‖b‖ := norm_pos_iff.2 hb
  have hP : 0 < ‖deriv φ u⁻¹‖ := norm_pos_iff.2 hφ'
  have hFp : 0 < ‖φ u⁻¹‖ := norm_pos_iff.2 hφs
  have hN : ‖deriv (gsans μ) u‖ = ‖b‖ * ‖deriv φ u⁻¹‖ / (‖u‖ ^ 2 * ‖φ u⁻¹‖ ^ 2) := by
    rw [hderiv, norm_div, norm_mul, norm_mul, norm_pow, norm_pow]
  have hFe : ‖φ u⁻¹‖ = ‖b‖ / ‖z‖ := by
    rw [eq_div_iff hZ.ne', mul_comm]
    exact hF
  have hs1 : 1 - ‖u⁻¹‖ ^ 2 = (‖u‖ ^ 2 - 1) / ‖u‖ ^ 2 := by
    rw [norm_inv]
    field_simp
  have hU2 : 0 < ‖u‖ ^ 2 - 1 := by nlinarith
  rw [norm_inv, norm_div, hN, hFe, hs1]
  field_simp

/-- **Remark 2.8** (TT:4170–4186). The sharper bound `∬_Ω d²w/|z - w|⁴ ≤ (π/4) ρ₂(z)`, `z ∈ Ω*`.

[CORRECTION 2026-10-25] `λ_{Ω*}` in the sphere chart `1/z` (`poincareDensityNearInfty`), as in `eq_2_8`. -/
theorem ab28_remark_2_8 {μ : LinfStar} (hμ : μ ∈ LinfStarBall) {z : ℂ} (hz : z ∈ gsans μ '' unitDiscExterior) :
    ∫ w in fsans μ '' unitDisc, 1 / ‖w - z‖ ^ 4 ≤
      π / 4 * poincareDensityNearInfty (gsans μ '' unitDiscExterior) z ^ 2 := by
  have hpair := AppB.b8_welding_normalized_pair hμ
  have hF := (mg_remark_2_2 hμ).2.1
  rcases hz with ⟨u, hu, rfl⟩
  obtain ⟨hg'ne, hdens⟩ := ab28_density hμ hu
  have hbd := ab28_int_bound hpair hF hu
  rw [hdens]
  have hN : 0 < ‖deriv (gsans μ) u‖ := norm_pos_iff.2 hg'ne
  have hU : 0 < ‖u‖ ^ 2 - 1 := by
    have : 1 < ‖u‖ := hu
    nlinarith
  have hc : 0 < ‖deriv (gsans μ) u‖ ^ 2 / π ^ 2 := by positivity
  have hI : ∫ w in fsans μ '' unitDisc, 1 / ‖w - gsans μ u‖ ^ 4 ≤
      1 / (π * (‖u‖ ^ 2 - 1) ^ 2) / (‖deriv (gsans μ) u‖ ^ 2 / π ^ 2) :=
    (le_div_iff₀ hc).2 (by rw [mul_comm]; exact hbd)
  refine hI.trans (le_of_eq ?_)
  field_simp
  norm_num

/-- **Remark 2.8** (TT:4170–4186). The sharper bound `∬_Ω d²w/|z - w|⁴ ≤ (π/4) ρ₂(z)`, `z ∈ Ω*`.

[CORRECTION 2026-10-25] `λ_{Ω*}` in the sphere chart `1/z` (`poincareDensityNearInfty`), as in `eq_2_8`. -/
theorem remark_2_8 {μ : LinfStar} (hμ : μ ∈ LinfStarBall) {z : ℂ} (hz : z ∈ gsans μ '' unitDiscExterior) :
    ∫ w in fsans μ '' unitDisc, 1 / ‖w - z‖ ^ 4 ≤
      π / 4 * poincareDensityNearInfty (gsans μ '' unitDiscExterior) z ^ 2 :=
  ab28_remark_2_8 hμ hz

end Ch2
end TakhtajanTeo
