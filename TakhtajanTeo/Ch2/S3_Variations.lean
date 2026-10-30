import TakhtajanTeo.Ch2.S2_Grunsky

/-!
# Chapter 2, §3 — Variations of the functions `S₁` and `S₂` (TT:4582–5293)

* §3.1 Theorem 3.1, the 1-form `ϑ`, Corollary 3.2
* §3.2 `S̃₁`, its formula via (1.3), Lemma 3.4, Theorem 3.5, Lemma 3.6, Corollary 3.7, Theorem 3.8, Corollary 3.9,
  Remark 3.10

**Modelling.**
- Bers coordinates on the chart `V_ν` (Chapter 1, §2.3): `ε_μ ↦ [εμ * ν]` for `μ ∈ H^{-1,1}(𝔻*)`.
  - `∂F/∂ε_μ([ν]) = ∂/∂ε|_{ε=0} F([εμ * ν])` (TT:4604) is the Wirtinger derivative `dz` of `ε ↦ F([εμ * ν])`.
  - Second derivatives `∂²F/∂ε_μ∂ε̄_ν` (§4) are `dz`/`dzbar` of `(ε₁, ε₂) ↦ F([(ε₁μ + ε₂ν) * κ])`.
- `ϑ_{[μ]} = 𝒮(𝗀_μ) ∈ A₂(𝔻*)` (TT:4664). It is paired with tangent vectors `μ ∈ H^{-1,1}(𝔻*)` by `∬_{𝔻*} ϑ μ d²z`.
  "`∂F = c ϑ`" means `∂F/∂ε_μ([ν]) = c ∬ ϑ_{[ν]} μ` at every `[ν] ∈ T₀(1)` and for every `μ`.
- The model `T(1) ≃ L∞(𝔻)₁/∼` of §3.2 is reached by conjugation with `ι(z) = 1/z`:
  `f̃ = ι ∘ 𝖿^μ ∘ ι` (univalent on `𝔻*`) and `g̃ = ι ∘ 𝗀_μ ∘ ι` (univalent on `𝔻`) (TT:4690).
- Lemma 3.4 is stated as the identity its proof reduces to (TT:4736–4778): the invariance of
  `∬_𝔻 |𝒜(g)|² + 4π log |g'(0)|` under `g ↦ g ∘ α⁻¹`, `α ∈ PSU(1,1)`.
  - The rest of that proof (the fibers of `𝒯₀(1) → T₀(1)` are `f ↦ σ ∘ f`, `g ↦ σ ∘ g ∘ α⁻¹` with `σ` a translation, and
    `𝒜` is translation invariant) is bookkeeping on the normalizations.

**Corrections.** Lemma 3.6 (TT:4966): the kernel `g'(z)g'(w)/(g(w) - g(w))²` is a misprint for
`g'(z)g'(w)/(g(z) - g(w))²`. This is the kernel `K₁` of `(f, g)` (cf. Remark 3.10 and TT:3949).

**Not stated.**
- (3.1) `∂ log det(I - 𝖪₁(ε)) = -Tr((I - 𝖪₁)⁻¹ ∂𝖪₁)` is a general fact on Fredholm determinants ([GK69]), used in the
  proof.
- Remark 3.11's (3.3) (the Polyakov–Alvarez formula), Corollary 3.12 and Remark 3.13 use zeta-regularized determinants
  of Laplacians, which are not available.
-/

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal ComplexConjugate Classical Real

noncomputable section

namespace TakhtajanTeo

open LiZhongQC

namespace Ch2

/-- The quadratic area energy under addition of a constant, used to identify
the mean functional from the sharp Bergman point-evaluation bound. -/
theorem a21_integral_add_const_sq {ψ : ℂ → ℂ} (hψ : ψ ∈ A21fun unitDisc) (c : ℂ) :
    (∫ z in unitDisc, ‖ψ z + c‖ ^ 2) =
      (∫ z in unitDisc, ‖ψ z‖ ^ 2) + π * ‖c‖ ^ 2 +
        2 * ((∫ z in unitDisc, ψ z) * conj c).re := by
  letI : IsFiniteMeasure (volume.restrict unitDisc) := isFiniteMeasure_restrict.mpr
    (by change volume (ball (0 : ℂ) 1) ≠ ∞; exact measure_ball_lt_top.ne)
  have hD : MeasurableSet unitDisc := isOpen_ball.measurableSet
  have hi : Integrable ψ (volume.restrict unitDisc) :=
    MemLp.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2) (a21_memLp_two hD hψ)
  have hs := a21_integrable_sq hD hψ
  have hc : Integrable (fun _ : ℂ => ‖c‖ ^ 2) (volume.restrict unitDisc) := integrable_const _
  have hx : Integrable (fun z => 2 * (ψ z * conj c).re) (volume.restrict unitDisc) :=
    ((hi.mul_const (conj c)).re).const_mul 2
  have he (z : ℂ) : ‖ψ z + c‖ ^ 2 = ‖ψ z‖ ^ 2 + ‖c‖ ^ 2 + 2 * (ψ z * conj c).re := by
    simpa only [Complex.normSq_eq_norm_sq] using Complex.normSq_add (ψ z) c
  simp_rw [he]
  have hsc : Integrable (fun z => ‖ψ z‖ ^ 2 + ‖c‖ ^ 2)
      (volume.restrict unitDisc) := hs.add hc
  have hre : (∫ z in unitDisc, (ψ z * conj c).re) =
      (∫ z in unitDisc, ψ z * conj c).re := integral_re (hi.mul_const (conj c))
  rw [integral_add hsc hx, integral_add hs hc,
    integral_const_mul, hre, integral_mul_const]
  have hv : (volume unitDisc).toReal = π := by simp [unitDisc]
  rw [integral_const]
  simp only [Measure.real, Measure.restrict_apply_univ, hv, smul_eq_mul]

/-- The disk area mean of a finite-energy holomorphic function equals its
central value times the area. This follows from sharp point evaluation by polarization. -/
theorem a21_area_mean {ψ : ℂ → ℂ} (hψ : ψ ∈ A21fun unitDisc) :
    (∫ z in unitDisc, ψ z) = (π : ℂ) * ψ 0 := by
  letI : IsFiniteMeasure (volume.restrict unitDisc) := isFiniteMeasure_restrict.mpr
    (by change volume (ball (0 : ℂ) 1) ≠ ∞; exact measure_ball_lt_top.ne)
  have hD : MeasurableSet unitDisc := isOpen_ball.measurableSet
  let A : ℝ := (∫ z in unitDisc, ‖ψ z‖ ^ 2) - π * ‖ψ 0‖ ^ 2
  let d : ℂ := (∫ z in unitDisc, ψ z) - (π : ℂ) * ψ 0
  have hvar (c : ℂ) : 0 ≤ A + 2 * (d * conj c).re := by
    have hFc : (fun z => ψ z + c) ∈ A21fun unitDisc := by
      apply (mem_A21fun_iff_memLp hD).mpr
      exact ⟨hψ.1.add_const c, (a21_memLp_two hD hψ).add (memLp_const c)⟩
    have hb := a21_origin_area_bound hFc.1
    have hi : ENNReal.ofReal (∫ z in unitDisc, ‖ψ z + c‖ ^ 2) =
        ∫⁻ z in unitDisc, (‖ψ z + c‖₊ : ℝ≥0∞) ^ 2 := by
      rw [ofReal_integral_eq_lintegral_ofReal (a21_integrable_sq hD hFc)
        (Eventually.of_forall fun z => sq_nonneg ‖ψ z + c‖)]
      simp only [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm, enorm_eq_nnnorm]
    rw [← hi] at hb
    have hr := (ENNReal.ofReal_le_ofReal_iff (integral_nonneg fun z => sq_nonneg ‖ψ z + c‖)).mp hb
    rw [a21_integral_add_const_sq hψ c] at hr
    have he : ‖ψ 0 + c‖ ^ 2 = ‖ψ 0‖ ^ 2 + ‖c‖ ^ 2 + 2 * (ψ 0 * conj c).re := by
      simpa only [Complex.normSq_eq_norm_sq] using Complex.normSq_add (ψ 0) c
    rw [he] at hr
    have hd : (d * conj c).re = ((∫ z in unitDisc, ψ z) * conj c).re - π * (ψ 0 * conj c).re := by
      dsimp only [d]
      simp [sub_mul, mul_assoc, Complex.mul_re]
    rw [hd]
    dsimp only [A]
    linarith
  have hd0 : d = 0 := by
    by_contra hd
    let t : ℝ := (A + 1) / (2 * ‖d‖ ^ 2)
    have hn : ‖d‖ ≠ 0 := norm_ne_zero_iff.mpr hd
    have ht : 2 * t * ‖d‖ ^ 2 = A + 1 := by
      dsimp only [t]
      field_simp
    have hc : (d * conj ((-t : ℝ) * d)).re = -t * ‖d‖ ^ 2 := by
      rw [map_mul, conj_ofReal, Complex.ofReal_neg]
      have he : d * ((-t : ℂ) * conj d) = (-t : ℂ) * (d * conj d) := by ring
      rw [he, Complex.mul_conj, Complex.normSq_eq_norm_sq]
      simp [← Complex.ofReal_pow]
    have h := hvar ((-t : ℝ) * d)
    rw [hc] at h
    nlinarith
  exact sub_eq_zero.mp hd0

/-- Complex area change of variables for the cross terms in TT:4736–4778. -/
theorem integral_image_conformal_complex {U V : Set ℂ} {f : ℂ → ℂ}
    (hU : IsOpen U) (hf : IsConformalOnto f U V) (ψ : ℂ → ℂ) :
    (∫ z in V, ψ z) = ∫ z in U, (‖deriv f z‖ ^ 2 : ℂ) * ψ (f z) := by
  rw [← hf.2.2, integral_image_eq_integral_abs_det_fderiv_smul volume hU.measurableSet
    (fun z hz => ((hf.1.differentiableAt (hU.mem_nhds hz)).hasDerivAt.hasFDerivAt.restrictScalars
      ℝ).hasFDerivWithinAt) hf.2.1 ψ]
  apply setIntegral_congr_fun hU.measurableSet
  intro z _
  dsimp only
  rw [det_restrictScalars_toSpanSingleton, abs_of_nonneg (sq_nonneg _)]
  simp [Complex.real_smul]

/-- The area pairing of one-forms is conformally invariant (TT:4736–4778). -/
theorem a21_pairing_pullback {U V : Set ℂ} {f : ℂ → ℂ}
    (hU : IsOpen U) (hf : IsConformalOnto f U V) (ψ η : ℂ → ℂ) :
    (∫ z in U, (ψ (f z) * deriv f z) * conj (η (f z) * deriv f z)) =
      ∫ z in V, ψ z * conj (η z) := by
  rw [integral_image_conformal_complex hU hf]
  apply setIntegral_congr_fun hU.measurableSet
  intro z _
  dsimp only
  rw [map_mul]
  have he : (ψ (f z) * deriv f z) * (conj (η (f z)) * conj (deriv f z)) =
      (deriv f z * conj (deriv f z)) * (ψ (f z) * conj (η (f z))) := by ring
  rw [he, Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.ofReal_pow]

/-- The area mean transported by inverse disk automorphisms (TT:4736–4778). -/
theorem a21_inverse_deriv_pairing {f g ψ : ℂ → ℂ}
    (hf : IsConformalOnto f unitDisc unitDisc)
    (hg : DifferentiableOn ℂ g unitDisc) (hinv : EqOn (g ∘ f) id unitDisc)
    (hψ : ψ ∈ A21fun unitDisc) :
    (∫ z in unitDisc, ψ z * conj (deriv g z)) =
      (π : ℂ) * (ψ (f 0) * deriv f 0) := by
  have hd (z : ℂ) (hz : z ∈ unitDisc) : deriv g (f z) * deriv f z = 1 := by
    have he := hinv.deriv isOpen_ball hz
    rw [deriv_comp z (hg.differentiableAt (isOpen_ball.mem_nhds (hf.mapsTo hz)))
      (hf.1.differentiableAt (isOpen_ball.mem_nhds hz)), deriv_id] at he
    exact he
  calc
    _ = ∫ z in unitDisc, (ψ (f z) * deriv f z) *
        conj (deriv g (f z) * deriv f z) := (a21_pairing_pullback isOpen_ball hf ψ (deriv g)).symm
    _ = ∫ z in unitDisc, ψ (f z) * deriv f z := by
      apply setIntegral_congr_fun isOpen_ball.measurableSet
      intro z hz
      dsimp only
      rw [hd z hz, map_one, mul_one]
    _ = _ := a21_area_mean (a21_pullback isOpen_ball hf hψ)

/-- Pairing with the derivative of a Blaschke factor reproduces point evaluation,
the first cross-integral identity needed in Lemma 3.4 (TT:4736–4778). -/
theorem a21_blaschke_deriv_pairing {ψ : ℂ → ℂ} (hψ : ψ ∈ A21fun unitDisc)
    {w : ℂ} (hw : w ∈ unitDisc) :
    (∫ z in unitDisc, ψ z * conj (deriv (blaschke w) z)) =
      (π : ℂ) * (ψ w * (1 - ‖w‖ ^ 2)) := by
  have hwn : ‖w‖ < 1 := mem_ball_zero_iff.mp hw
  have hwneg : ‖-w‖ < 1 := by simpa using hwn
  have hinv : EqOn (blaschke w ∘ blaschke (-w)) id unitDisc := by
    intro z hz
    exact blaschke_blaschke_neg hwn (mem_ball_zero_iff.mp hz)
  have h := a21_inverse_deriv_pairing (isConformalOnto_blaschke hwneg)
    (differentiableOn_blaschke hwn) hinv hψ
  have hd : deriv (blaschke (-w)) 0 = (1 - ‖w‖ ^ 2 : ℂ) := by
    rw [(hasDerivAt_blaschke hwneg (by simp)).deriv]
    simp only [map_neg, mul_neg, neg_mul, neg_neg, mul_zero, sub_zero, one_pow,
      div_one, Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.ofReal_pow]
  simpa only [blaschke_neg_zero, hd] using h

/-- The Bergman reproducing formula for finite-energy holomorphic functions,
used to evaluate the cross terms in TT:4736–4778. -/
theorem a21_bergman_reproducing {ψ : ℂ → ℂ} (hψ : ψ ∈ A21fun unitDisc)
    {w : ℂ} (hw : w ∈ unitDisc) :
    (∫ z in unitDisc, ψ z / (1 - w * conj z) ^ 2) = (π : ℂ) * ψ w := by
  have hwn : ‖w‖ < 1 := mem_ball_zero_iff.mp hw
  let c : ℂ := 1 - ‖w‖ ^ 2
  have hc : c ≠ 0 := by
    have h := one_sub_mul_conj_ne_zero hwn
    simpa only [Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.ofReal_pow] using h
  have hker (z : ℂ) (hz : z ∈ unitDisc) :
      conj (deriv (blaschke w) z) = c / (1 - w * conj z) ^ 2 := by
    rw [(hasDerivAt_blaschke hwn (mem_ball_zero_iff.mp hz)).deriv,
      Complex.mul_conj, Complex.normSq_eq_norm_sq]
    simp [c, map_div, map_sub, map_pow, map_mul, ← Complex.ofReal_pow]
  have he : (∫ z in unitDisc, ψ z * conj (deriv (blaschke w) z)) =
      c * (∫ z in unitDisc, ψ z / (1 - w * conj z) ^ 2) := by
    calc
      _ = ∫ z in unitDisc, c * (ψ z / (1 - w * conj z) ^ 2) := by
        apply setIntegral_congr_fun isOpen_ball.measurableSet
        intro z hz
        dsimp only
        rw [hker z hz]
        ring
      _ = _ := integral_const_mul _ _
  have h := a21_blaschke_deriv_pairing hψ hw
  rw [he] at h
  apply mul_left_cancel₀ hc
  calc
    c * (∫ z in unitDisc, ψ z / (1 - w * conj z) ^ 2) = (π : ℂ) * (ψ w * c) := h
    _ = c * ((π : ℂ) * ψ w) := by ring

/-- The pre-Schwarzian chain rule used in the inversion formulas of TT:4680–4690. -/
theorem preSchwarzian_comp_of_analyticAt {f g : ℂ → ℂ} {z : ℂ}
    (hg : AnalyticAt ℂ g z) (hf : AnalyticAt ℂ f (g z))
    (hg' : deriv g z ≠ 0) (hf' : deriv f (g z) ≠ 0) :
    preSchwarzian (f ∘ g) z = preSchwarzian f (g z) * deriv g z + preSchwarzian g z := by
  have he : deriv (f ∘ g) =ᶠ[𝓝 z] (fun w => deriv f (g w) * deriv g w) := by
    filter_upwards [hg.eventually_analyticAt,
      hg.continuousAt.eventually hf.eventually_analyticAt] with w hgw hfw
    exact deriv_comp w hfw.differentiableAt hgw.differentiableAt
  have hA : HasDerivAt (deriv f ∘ g) (deriv (deriv f) (g z) * deriv g z) z :=
    hf.deriv.differentiableAt.hasDerivAt.comp z hg.differentiableAt.hasDerivAt
  have hB := hg.deriv.differentiableAt.hasDerivAt
  have hD := (hA.mul hB).deriv
  change deriv (fun w => deriv f (g w) * deriv g w) z =
    (deriv (deriv f) (g z) * deriv g z) * deriv g z +
      deriv f (g z) * deriv (deriv g) z at hD
  unfold preSchwarzian
  rw [he.deriv_eq, hD, deriv_comp z hf.differentiableAt hg.differentiableAt]
  field_simp [hg', hf']

/-- The pre-Schwarzian of inversion, used in TT:4680–4690. -/
theorem preSchwarzian_inv {z : ℂ} (hz : z ≠ 0) :
    preSchwarzian (fun w : ℂ => w⁻¹) z = -2 / z := by
  have hd := (((hasDerivAt_id z).pow 2).inv (pow_ne_zero 2 hz)).neg
  change HasDerivAt (fun w : ℂ => -(w ^ 2)⁻¹) _ z at hd
  simp only [preSchwarzian, deriv_inv']
  rw [hd.deriv]
  field_simp [hz]
  simp only [Pi.pow_apply, id_eq]
  ring

/-- Post-composition by inversion gives the correction `-2g'/g` (TT:4680–4690). -/
theorem preSchwarzian_inv_comp {g : ℂ → ℂ} {z : ℂ}
    (hg : AnalyticAt ℂ g z) (hgz : g z ≠ 0) (hg' : deriv g z ≠ 0) :
    preSchwarzian (fun w => (g w)⁻¹) z = preSchwarzian g z - 2 * deriv g z / g z := by
  have hi : AnalyticAt ℂ (fun w : ℂ => w⁻¹) (g z) := analyticAt_id.inv hgz
  have hi' : deriv (fun w : ℂ => w⁻¹) (g z) ≠ 0 := by
    rw [deriv_inv]
    exact neg_ne_zero.mpr (inv_ne_zero (pow_ne_zero 2 hgz))
  have h := preSchwarzian_comp_of_analyticAt hg hi hg' hi'
  rw [preSchwarzian_inv hgz] at h
  change preSchwarzian (fun w => (g w)⁻¹) z = -2 / g z * deriv g z + preSchwarzian g z at h
  rw [h]
  ring

/-- (TT:4680–4690, 5206–5248) Inversion in both source and target gives
the pre-Schwarzian identity used by the tilde Liouville action. -/
theorem preSchwarzian_inversion {f : ℂ → ℂ} {z : ℂ}
    (hf : AnalyticAt ℂ f z) (hz : z ≠ 0) (hfz : f z ≠ 0) (hf' : deriv f z ≠ 0) :
    preSchwarzian (fun w => (f w⁻¹)⁻¹) z⁻¹ * (-1 / z ^ 2) =
      preSchwarzian f z - 2 * deriv f z / f z + 2 / z := by
  let ι : ℂ → ℂ := fun w => w⁻¹
  have hi : AnalyticAt ℂ ι z⁻¹ := analyticAt_id.inv (inv_ne_zero hz)
  have hi' : deriv ι z⁻¹ ≠ 0 := by
    dsimp only [ι]
    rw [deriv_inv]
    exact neg_ne_zero.mpr (inv_ne_zero (pow_ne_zero 2 (inv_ne_zero hz)))
  have hfi : AnalyticAt ℂ f (ι z⁻¹) := by simpa only [ι, inv_inv] using hf
  have hfi' : deriv f (ι z⁻¹) ≠ 0 := by simpa only [ι, inv_inv] using hf'
  have hcomp : AnalyticAt ℂ (f ∘ ι) z⁻¹ := hfi.comp hi
  have hcomp0 : (f ∘ ι) z⁻¹ ≠ 0 := by simpa only [Function.comp_apply, ι, inv_inv] using hfz
  have hcomp' : deriv (f ∘ ι) z⁻¹ ≠ 0 := by
    rw [deriv_comp z⁻¹ hfi.differentiableAt hi.differentiableAt]
    exact mul_ne_zero hfi' hi'
  change preSchwarzian (fun w => ((f ∘ ι) w)⁻¹) z⁻¹ * (-1 / z ^ 2) = _
  rw [preSchwarzian_inv_comp hcomp hcomp0 hcomp',
    preSchwarzian_comp_of_analyticAt hi hfi hi' hfi',
    deriv_comp z⁻¹ hfi.differentiableAt hi.differentiableAt]
  simp only [ι, Function.comp_apply, inv_inv]
  rw [preSchwarzian_inv (inv_ne_zero hz), deriv_inv]
  field_simp [hz, hfz]; ring

/-- (TT:4736–4778) Target translations leave the pre-Schwarzian unchanged. -/
theorem preSchwarzian_add_const (f : ℂ → ℂ) (b z : ℂ) :
    preSchwarzian (fun w => f w + b) z = preSchwarzian f z := by
  have he : deriv (fun w => f w + b) = deriv f := by
    funext w
    simp
  unfold preSchwarzian
  rw [he]

/-- Uniform denominator separation on a compact parameter subdisk, used for
differentiation of the cross-integral in TT:4736–4778. -/
theorem one_sub_mul_conj_norm_lower {w z : ℂ} {r : ℝ}
    (hw : ‖w‖ ≤ r) (hz : z ∈ unitDisc) :
    1 - r ≤ ‖1 - w * conj z‖ := by
  have hzn : ‖z‖ ≤ 1 := (mem_ball_zero_iff.mp hz).le
  have hm : ‖w * conj z‖ ≤ r := by
    rw [norm_mul, norm_conj]
    calc
      ‖w‖ * ‖z‖ ≤ ‖w‖ * 1 := mul_le_mul_of_nonneg_left hzn (norm_nonneg _)
      _ ≤ r := by simpa using hw
  have h := norm_sub_norm_le (1 : ℂ) (w * conj z)
  rw [norm_one] at h
  linarith

/-- Differentiation of the Dirichlet reproducing integral is justified by an
integrable uniform bound; only the explicit A21 hypothesis is used (TT:4736–4778). -/
theorem a21_hasDerivAt_dirichlet_integral {ψ : ℂ → ℂ}
    (hψ : ψ ∈ A21fun unitDisc) {w : ℂ} (hw : w ∈ unitDisc) :
    HasDerivAt (fun v => ∫ z in unitDisc, ψ z * (v / (1 - v * conj z)))
      ((π : ℂ) * ψ w) w := by
  letI : IsFiniteMeasure (volume.restrict unitDisc) := isFiniteMeasure_restrict.mpr
    (by change volume (ball (0 : ℂ) 1) ≠ ∞; exact measure_ball_lt_top.ne)
  have hD : MeasurableSet unitDisc := isOpen_ball.measurableSet
  have hi : Integrable ψ (volume.restrict unitDisc) :=
    MemLp.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2) (a21_memLp_two hD hψ)
  obtain ⟨r, hwr, hr⟩ := exists_between (mem_ball_zero_iff.mp hw)
  have hr0 : 0 < r := lt_of_le_of_lt (norm_nonneg _) hwr
  have hs : ball (0 : ℂ) r ∈ 𝓝 w := isOpen_ball.mem_nhds (mem_ball_zero_iff.mpr hwr)
  have hsep (v z : ℂ) (hv : v ∈ ball (0 : ℂ) r) (hz : z ∈ unitDisc) :
      1 - r ≤ ‖1 - v * conj z‖ :=
    one_sub_mul_conj_norm_lower (mem_ball_zero_iff.mp hv).le hz
  have hne (v z : ℂ) (hv : v ∈ ball (0 : ℂ) r) (hz : z ∈ unitDisc) :
      1 - v * conj z ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le (sub_pos.mpr hr) (hsep v z hv hz))
  let F : ℂ → ℂ → ℂ := fun v z => ψ z * (v / (1 - v * conj z))
  let F' : ℂ → ℂ → ℂ := fun v z => ψ z / (1 - v * conj z) ^ 2
  have hFm (v : ℂ) : AEStronglyMeasurable (F v) (volume.restrict unitDisc) :=
    hi.aestronglyMeasurable.mul
      ((show Measurable (fun z : ℂ => v / (1 - v * conj z)) by fun_prop).aestronglyMeasurable)
  have hF'm (v : ℂ) : AEStronglyMeasurable (F' v) (volume.restrict unitDisc) := by
    simp only [F', div_eq_mul_inv]
    exact hi.aestronglyMeasurable.mul (by fun_prop)
  have hFi : Integrable (F w) (volume.restrict unitDisc) := by
    apply (hi.norm.const_mul (‖w‖ / (1 - r))).mono' (hFm w)
    filter_upwards [ae_restrict_mem hD] with z hz
    dsimp only [F]
    rw [norm_mul, norm_div]
    have hb : ‖w‖ / ‖1 - w * conj z‖ ≤ ‖w‖ / (1 - r) :=
      div_le_div_of_nonneg_left (norm_nonneg _) (sub_pos.mpr hr)
        (hsep w z (mem_ball_zero_iff.mpr hwr) hz)
    calc
      _ ≤ ‖ψ z‖ * (‖w‖ / (1 - r)) := mul_le_mul_of_nonneg_left hb (norm_nonneg _)
      _ = _ := by ring
  have hb : ∀ᵐ z ∂volume.restrict unitDisc, ∀ v ∈ ball (0 : ℂ) r,
      ‖F' v z‖ ≤ (1 / (1 - r) ^ 2) * ‖ψ z‖ := by
    filter_upwards [ae_restrict_mem hD] with z hz
    intro v hv
    dsimp only [F']
    rw [norm_div, norm_pow]
    have hsq : (1 - r) ^ 2 ≤ ‖1 - v * conj z‖ ^ 2 := by
      nlinarith [hsep v z hv hz, norm_nonneg (1 - v * conj z)]
    have ht := div_le_div_of_nonneg_left (norm_nonneg (ψ z)) (sq_pos_of_pos (sub_pos.mpr hr)) hsq
    calc
      _ ≤ ‖ψ z‖ / (1 - r) ^ 2 := ht
      _ = _ := by ring
  have hd : ∀ᵐ z ∂volume.restrict unitDisc, ∀ v ∈ ball (0 : ℂ) r,
      HasDerivAt (fun v => F v z) (F' v z) v := by
    filter_upwards [ae_restrict_mem hD] with z hz
    intro v hv
    have h := ((hasDerivAt_id v).div
      (((hasDerivAt_id v).mul_const (conj z)).const_sub 1) (hne v z hv hz)).const_mul (ψ z)
    convert h using 1 <;> dsimp only [F, F', Pi.div_apply, id_eq] <;> ring
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le (F := F) (F' := F')
    (bound := fun z => (1 / (1 - r) ^ 2) * ‖ψ z‖) hs
    (Eventually.of_forall hFm) hFi (hF'm w) hb (hi.norm.const_mul _) hd
  have he : (∫ z in unitDisc, F' w z) = (π : ℂ) * ψ w := a21_bergman_reproducing hψ hw
  rw [he] at h
  exact h.2

/-- The Dirichlet reproducing identity for a specified holomorphic primitive,
supporting the pre-Schwarzian cross term of Lemma 3.4 (TT:4736–4778). -/
theorem a21_dirichlet_reproducing {ψ H : ℂ → ℂ} (hψ : ψ ∈ A21fun unitDisc)
    (hH : ∀ z ∈ unitDisc, HasDerivAt H (ψ z) z) {w : ℂ} (hw : w ∈ unitDisc) :
    (∫ z in unitDisc, ψ z * (w / (1 - w * conj z))) = (π : ℂ) * (H w - H 0) := by
  let F : ℂ → ℂ := fun v => ∫ z in unitDisc, ψ z * (v / (1 - v * conj z))
  have hd (v : ℂ) (hv : v ∈ unitDisc) : HasDerivAt (fun v => F v - (π : ℂ) * H v) 0 v := by
    have h := (a21_hasDerivAt_dirichlet_integral hψ hv).sub ((hH v hv).const_mul (π : ℂ))
    convert h using 1 <;> simp only [F, Pi.sub_apply, sub_self]
  have he := isOpen_ball.is_const_of_deriv_eq_zero (convex_ball (0 : ℂ) 1).isPreconnected
    (fun v hv => (hd v hv).differentiableAt.differentiableWithinAt)
    (fun v hv => (hd v hv).deriv) hw (show (0 : ℂ) ∈ unitDisc by simp [unitDisc])
  have h0 : F 0 = 0 := by simp [F]
  change F w - (π : ℂ) * H w = F 0 - (π : ℂ) * H 0 at he
  rw [h0] at he
  change F w = _
  linear_combination he

/-- The real pre-Schwarzian cross integral is a logarithmic derivative ratio,
as used in Lemma 3.4 (TT:4736–4778). -/
theorem preSchwarzian_dirichlet_integral {g : ℂ → ℂ}
    (hg : DifferentiableOn ℂ g unitDisc) (hinj : InjOn g unitDisc)
    (hA : preSchwarzian g ∈ A21fun unitDisc) {w : ℂ} (hw : w ∈ unitDisc) :
    (∫ z in unitDisc, preSchwarzian g z * (w / (1 - w * conj z))).re =
      π * (Real.log ‖deriv g w‖ - Real.log ‖deriv g 0‖) := by
  have hn : ∀ z ∈ unitDisc, deriv g z ≠ 0 := fun z hz =>
    deriv_ne_zero_of_injOn isOpen_ball hg hinj hz
  obtain ⟨L, hL, he⟩ := kb_exists_log (hg.deriv isOpen_ball) hn
  have hD (z : ℂ) (hz : z ∈ unitDisc) : HasDerivAt L (preSchwarzian g z) z := by
    have hdL := (hL.differentiableAt (isOpen_ball.mem_nhds hz)).hasDerivAt
    have heq : EqOn (fun z => exp (L z)) (deriv g) unitDisc := he
    have h := heq.deriv isOpen_ball hz
    rw [hdL.cexp.deriv, he z hz] at h
    have hp : deriv L z = preSchwarzian g z := by
      rw [preSchwarzian, eq_div_iff (hn z hz)]
      simpa only [mul_comm] using h
    rwa [hp] at hdL
  have hr (z : ℂ) (hz : z ∈ unitDisc) : (L z).re = Real.log ‖deriv g z‖ := by
    rw [← he z hz, Complex.norm_exp, Real.log_exp]
  rw [a21_dirichlet_reproducing hA hD hw]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
    Complex.sub_re, hr w hw, hr 0 (by simp [unitDisc])]

/-- The elementary Dirichlet kernel belongs to A21 for every interior pole
parameter; its uniform bound retains the distance to the boundary (TT:4736–4778). -/
theorem dirichlet_kernel_mem_A21 {w : ℂ} (hw : w ∈ unitDisc) :
    (fun z => conj w / (1 - conj w * z)) ∈ A21fun unitDisc := by
  letI : IsFiniteMeasure (volume.restrict unitDisc) := isFiniteMeasure_restrict.mpr
    (by change volume (ball (0 : ℂ) 1) ≠ ∞; exact measure_ball_lt_top.ne)
  have hD : MeasurableSet unitDisc := isOpen_ball.measurableSet
  have hwn : ‖w‖ < 1 := mem_ball_zero_iff.mp hw
  have hd : DifferentiableOn ℂ (fun z => conj w / (1 - conj w * z)) unitDisc := by
    apply DifferentiableOn.div (by fun_prop) (by fun_prop)
    intro z hz
    exact blaschke_den_ne_zero hwn (mem_ball_zero_iff.mp hz)
  apply (mem_A21fun_iff_memLp hD).mpr
  refine ⟨hd, MemLp.of_bound (hd.continuousOn.aestronglyMeasurable hD) (‖w‖ / (1 - ‖w‖)) ?_⟩
  filter_upwards [ae_restrict_mem hD] with z hz
  have hs := one_sub_mul_conj_norm_lower (w := w) (z := z) le_rfl hz
  have hn : ‖1 - conj w * z‖ = ‖1 - w * conj z‖ := by
    rw [← norm_conj (1 - conj w * z)]
    simp
  rw [norm_div, norm_conj, hn]
  exact div_le_div_of_nonneg_left (norm_nonneg _) (sub_pos.mpr hwn) hs

/-- The Dirichlet kernel has the logarithmic primitive used in TT:4736–4778. -/
theorem hasDerivAt_dirichlet_kernel_primitive {w z : ℂ}
    (hw : w ∈ unitDisc) (hz : z ∈ unitDisc) :
    HasDerivAt (fun z => -Complex.log (1 - conj w * z)) (conj w / (1 - conj w * z)) z := by
  have hwn : ‖w‖ < 1 := mem_ball_zero_iff.mp hw
  have hzn : ‖z‖ < 1 := mem_ball_zero_iff.mp hz
  have hn : ‖-(conj w * z)‖ < 1 := by
    rw [norm_neg, norm_mul, norm_conj]
    calc
      ‖w‖ * ‖z‖ ≤ ‖w‖ * 1 := mul_le_mul_of_nonneg_left hzn.le (norm_nonneg _)
      _ < 1 := by simpa using hwn
  have hs : 1 - conj w * z ∈ slitPlane := by
    simpa only [sub_eq_add_neg] using mem_slitPlane_of_norm_lt_one hn
  have hd := ((hasDerivAt_log hs).comp z
    (((hasDerivAt_id z).const_mul (conj w)).const_sub 1)).neg
  change HasDerivAt (fun u => -Complex.log (1 - conj w * u)) _ z at hd
  convert hd using 1 <;> (try dsimp only [id_eq]) <;> ring

/-- The area energy of the Dirichlet kernel is `-π log (1-|w|²)` (TT:4736–4778). -/
theorem dirichlet_kernel_energy {w : ℂ} (hw : w ∈ unitDisc) :
    (∫ z in unitDisc, ‖conj w / (1 - conj w * z)‖ ^ 2) =
      -π * Real.log (1 - ‖w‖ ^ 2) := by
  let K : ℂ → ℂ := fun z => conj w / (1 - conj w * z)
  have he (z : ℂ) : K z * (w / (1 - w * conj z)) = ((‖K z‖ ^ 2 : ℝ) : ℂ) := by
    have hc : w / (1 - w * conj z) = conj (K z) := by simp [K]
    rw [hc, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have h := a21_dirichlet_reproducing (dirichlet_kernel_mem_A21 hw)
    (fun z hz => hasDerivAt_dirichlet_kernel_primitive hw hz) hw
  change (∫ z in unitDisc, K z * (w / (1 - w * conj z))) = _ at h
  simp_rw [he] at h
  have hi : (∫ z in unitDisc, ((‖K z‖ ^ 2 : ℝ) : ℂ)) =
      ((∫ z in unitDisc, ‖K z‖ ^ 2 : ℝ) : ℂ) := integral_complex_ofReal
  rw [hi] at h
  have hr := congrArg Complex.re h
  have hn : (conj w * w) = ((‖w‖ ^ 2 : ℝ) : ℂ) := by
    rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have hp : 0 < 1 - ‖w‖ ^ 2 := by
    have ht := mem_ball_zero_iff.mp hw
    nlinarith [norm_nonneg w]
  have hnrm : ‖(1 : ℂ) - (‖w‖ : ℂ) ^ 2‖ = 1 - ‖w‖ ^ 2 := by
    rw [← Complex.ofReal_pow, ← Complex.ofReal_one, ← Complex.ofReal_sub,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos hp]
  simpa [K, hn, Complex.log_re, hnrm, Complex.mul_re] using hr

/-- Affine source changes give the exact derivative scaling used by TT:4680–4690. -/
theorem deriv_affine_precomp (f : ℂ → ℂ) (a b z : ℂ) :
    deriv (fun w => f (a * w + b)) z = a * deriv f (a * z + b) := by
  simpa only [smul_eq_mul, deriv_comp_add_const] using
    deriv_comp_mul_left a (fun w => f (w + b)) z

/-- Affine source changes transform the pre-Schwarzian as a one-form. -/
theorem preSchwarzian_affine_precomp (f : ℂ → ℂ) (a b z : ℂ) :
    preSchwarzian (fun w => f (a * w + b)) z = a * preSchwarzian f (a * z + b) := by
  have he : deriv (fun w => f (a * w + b)) = fun w => a * deriv f (a * w + b) :=
    funext (deriv_affine_precomp f a b)
  unfold preSchwarzian
  rw [he, deriv_const_mul_field, deriv_affine_precomp]
  by_cases ha : a = 0
  · simp [ha]
  · rw [mul_div_mul_left _ _ ha]
    ring

/-- Nondegenerate affine target changes preserve the pre-Schwarzian. -/
theorem preSchwarzian_affine_postcomp (f : ℂ → ℂ) {a : ℂ} (ha : a ≠ 0) (b z : ℂ) :
    preSchwarzian (fun w => a * f w + b) z = preSchwarzian f z := by
  rw [preSchwarzian_add_const]
  unfold preSchwarzian
  rw [deriv_const_mul_field', deriv_const_mul_field]
  exact mul_div_mul_left _ _ ha

/-- Inversion is a conformal bijection from the punctured disk to its exterior. -/
theorem isConformalOnto_inv_puncturedDisc :
    IsConformalOnto (fun z : ℂ => z⁻¹) (unitDisc \ {0}) unitDiscExterior := by
  refine ⟨?_, inv_injective.injOn, ?_⟩
  · intro z hz
    have hz0 : z ≠ 0 := by simpa using hz.2
    exact (differentiableAt_inv hz0).differentiableWithinAt
  · ext w
    constructor
    · rintro ⟨z, hz, rfl⟩
      have hz0 : z ≠ 0 := by simpa using hz.2
      change 1 < ‖z⁻¹‖
      rw [norm_inv]
      exact (one_lt_inv₀ (norm_pos_iff.mpr hz0)).mpr (mem_ball_zero_iff.mp hz.1)
    · intro hw
      change 1 < ‖w‖ at hw
      have hw0 : w ≠ 0 := by intro h; subst w; norm_num at hw
      refine ⟨w⁻¹, ⟨?_, ?_⟩, inv_inv w⟩
      · apply mem_ball_zero_iff.mpr
        rw [norm_inv]
        exact (inv_lt_one₀ (lt_trans zero_lt_one hw)).mpr hw
      · simpa using inv_ne_zero hw0

/-- (TT:4680–4690) The inversion correction has exactly the exterior
pre-Schwarzian area norm. The omitted origin is an area-null singleton. -/
theorem preSchwarzian_inversion_area {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f unitDisc) (hi : InjOn f unitDisc) (h0 : f 0 = 0) :
    normA21 unitDisc (fun z => preSchwarzian f z - 2 * deriv f z / f z + 2 / z) =
      normA21 unitDiscExterior (preSchwarzian (fun w => (f w⁻¹)⁻¹)) := by
  let U : Set ℂ := unitDisc \ {0}
  let κ : ℂ → ℂ := fun z => preSchwarzian f z - 2 * deriv f z / f z + 2 / z
  let ψ : ℂ → ℂ := preSchwarzian (fun w => (f w⁻¹)⁻¹)
  have hU : IsOpen U := isOpen_ball.sdiff isClosed_singleton
  have hpull := normA21_pullback hU isConformalOnto_inv_puncturedDisc ψ
  have he : EqOn (fun z => ψ z⁻¹ * deriv (fun w : ℂ => w⁻¹) z) κ U := by
    intro z hz
    have hz0 : z ≠ 0 := by simpa using hz.2
    have hfz : f z ≠ 0 := by
      intro he
      apply hz0
      exact hi hz.1 (by simp [unitDisc]) (he.trans h0.symm)
    have hfa := hf.analyticAt (isOpen_ball.mem_nhds hz.1)
    have hf' := LiZhongQC.deriv_ne_zero_of_injOn isOpen_ball hf hi hz.1
    simpa only [ψ, κ, deriv_inv, div_eq_mul_inv, neg_mul, one_mul] using
      preSchwarzian_inversion hfa hz0 hfz hf'
  have hnorm : normA21 U (fun z => ψ z⁻¹ * deriv (fun w : ℂ => w⁻¹) z) = normA21 U κ := by
    unfold normA21
    congr 1
    apply lintegral_congr_ae
    filter_upwards [ae_restrict_mem hU.measurableSet] with z hz
    exact congrArg (fun v : ℂ => (‖v‖₊ : ℝ≥0∞) ^ 2) (he hz)
  have hmeasure : volume.restrict U = volume.restrict unitDisc := by
    apply Measure.restrict_congr_set
    filter_upwards [volume.ae_ne (0 : ℂ)] with z hz
    simp [U, hz]
  have hremove : normA21 U κ = normA21 unitDisc κ := by
    unfold normA21
    rw [hmeasure]
  exact hremove.symm.trans (hnorm.symm.trans hpull)

/-- Area norms are unchanged by deleting a single point. -/
theorem normA21_sdiff_singleton (D : Set ℂ) (ψ : ℂ → ℂ) (a : ℂ) :
    normA21 (D \ {a}) ψ = normA21 D ψ := by
  have hmeasure : volume.restrict (D \ {a}) = volume.restrict D := by
    apply Measure.restrict_congr_set
    filter_upwards [volume.ae_ne a] with z hz
    simp [hz]
  unfold normA21
  rw [hmeasure]

/-- Inversion is also a conformal bijection from the exterior to the punctured disk. -/
theorem isConformalOnto_inv_exterior :
    IsConformalOnto (fun z : ℂ => z⁻¹) unitDiscExterior (unitDisc \ {0}) := by
  refine ⟨?_, inv_injective.injOn, ?_⟩
  · intro z hz
    have hz0 : z ≠ 0 := by intro h; subst z; norm_num [unitDiscExterior] at hz
    exact (differentiableAt_inv hz0).differentiableWithinAt
  · rw [← isConformalOnto_inv_puncturedDisc.2.2, Set.image_image]
    simp

/-- (TT:4680–4690) The exterior inversion correction has the disk area norm
of the inverted pre-Schwarzian; the value assigned at the origin does not affect it. -/
theorem preSchwarzian_inversion_area_exterior {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f unitDiscExterior) (hi : InjOn f unitDiscExterior)
    (h0 : ∀ z ∈ unitDiscExterior, f z ≠ 0) :
    normA21 unitDiscExterior (fun z => preSchwarzian f z - 2 * deriv f z / f z + 2 / z) =
      normA21 unitDisc (preSchwarzian (fun w => (f w⁻¹)⁻¹)) := by
  let κ : ℂ → ℂ := fun z => preSchwarzian f z - 2 * deriv f z / f z + 2 / z
  let ψ : ℂ → ℂ := preSchwarzian (fun w => (f w⁻¹)⁻¹)
  have hU : IsOpen unitDiscExterior := isOpen_lt continuous_const continuous_norm
  have hpull := normA21_pullback hU isConformalOnto_inv_exterior ψ
  have he : EqOn (fun z => ψ z⁻¹ * deriv (fun w : ℂ => w⁻¹) z) κ unitDiscExterior := by
    intro z hz
    have hz0 : z ≠ 0 := by intro h; subst z; norm_num [unitDiscExterior] at hz
    have hfa := hf.analyticAt (hU.mem_nhds hz)
    have hf' := LiZhongQC.deriv_ne_zero_of_injOn hU hf hi hz
    simpa only [ψ, κ, deriv_inv, div_eq_mul_inv, neg_mul, one_mul] using
      preSchwarzian_inversion hfa hz0 (h0 z hz) hf'
  have hnorm : normA21 unitDiscExterior
      (fun z => ψ z⁻¹ * deriv (fun w : ℂ => w⁻¹) z) = normA21 unitDiscExterior κ := by
    unfold normA21
    congr 1
    apply lintegral_congr_ae
    filter_upwards [ae_restrict_mem hU.measurableSet] with z hz
    exact congrArg (fun v : ℂ => (‖v‖₊ : ℝ≥0∞) ^ 2) (he hz)
  exact hnorm.symm.trans (hpull.trans (normA21_sdiff_singleton unitDisc ψ 0))

/-- (TT:4680–4690) With finite exterior energy, the disk inversion identity
holds for the ordinary real area integrals in the Liouville action. -/
theorem preSchwarzian_inversion_integral {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f unitDisc) (hi : InjOn f unitDisc) (h0 : f 0 = 0)
    (hA : preSchwarzian (fun w => (f w⁻¹)⁻¹) ∈ A21fun unitDiscExterior) :
    (∫ z in unitDisc, ‖preSchwarzian f z - 2 * deriv f z / f z + 2 / z‖ ^ 2) =
      ∫ z in unitDiscExterior, ‖preSchwarzian (fun w => (f w⁻¹)⁻¹) z‖ ^ 2 := by
  let U : Set ℂ := unitDisc \ {0}
  let κ : ℂ → ℂ := fun z => preSchwarzian f z - 2 * deriv f z / f z + 2 / z
  let ψ : ℂ → ℂ := preSchwarzian (fun w => (f w⁻¹)⁻¹)
  have hU : IsOpen U := isOpen_ball.sdiff isClosed_singleton
  have hEx : IsOpen unitDiscExterior := isOpen_lt continuous_const continuous_norm
  have hpull := a21_pullback hU isConformalOnto_inv_puncturedDisc hA
  have he : EqOn (fun z => ψ z⁻¹ * deriv (fun w : ℂ => w⁻¹) z) κ U := by
    intro z hz
    have hz0 : z ≠ 0 := by simpa using hz.2
    have hfz : f z ≠ 0 := by
      intro he
      exact hz0 (hi hz.1 (by simp [unitDisc]) (he.trans h0.symm))
    simpa only [ψ, κ, deriv_inv, div_eq_mul_inv, neg_mul, one_mul] using
      preSchwarzian_inversion (hf.analyticAt (isOpen_ball.mem_nhds hz.1)) hz0 hfz
        (LiZhongQC.deriv_ne_zero_of_injOn isOpen_ball hf hi hz.1)
  have hN : normA21 U κ = normA21 unitDiscExterior ψ :=
    (normA21_sdiff_singleton unitDisc κ 0).trans (preSchwarzian_inversion_area hf hi h0)
  have hκ : κ ∈ A21fun U := by
    refine ⟨(differentiableOn_congr he).mp hpull.1, ?_⟩
    rw [hN]
    exact hA.2
  have hsq : ENNReal.ofReal (∫ z in U, ‖κ z‖ ^ 2) =
      ENNReal.ofReal (∫ z in unitDiscExterior, ‖ψ z‖ ^ 2) := by
    rw [← a21_norm_sq_eq_integral hU.measurableSet hκ,
      ← a21_norm_sq_eq_integral hEx.measurableSet hA, hN]
  have hreal := congrArg ENNReal.toReal hsq
  rw [ENNReal.toReal_ofReal (integral_nonneg fun z => sq_nonneg ‖κ z‖),
    ENNReal.toReal_ofReal (integral_nonneg fun z => sq_nonneg ‖ψ z‖)] at hreal
  have hmeasure : volume.restrict U = volume.restrict unitDisc := by
    apply Measure.restrict_congr_set
    filter_upwards [volume.ae_ne (0 : ℂ)] with z hz
    simp [U, hz]
  change (∫ z, ‖κ z‖ ^ 2 ∂(volume.restrict unitDisc)) = _
  rw [← hmeasure]
  exact hreal

/-- (TT:4680–4690) The exterior correction transfers its real energy to the
disk. Only punctured-disk holomorphy is required at the omitted origin. -/
theorem preSchwarzian_inversion_integral_exterior {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f unitDiscExterior) (hi : InjOn f unitDiscExterior)
    (h0 : ∀ z ∈ unitDiscExterior, f z ≠ 0)
    (hA : preSchwarzian (fun w => (f w⁻¹)⁻¹) ∈ A21fun (unitDisc \ {0})) :
    (∫ z in unitDiscExterior, ‖preSchwarzian f z - 2 * deriv f z / f z + 2 / z‖ ^ 2) =
      ∫ z in unitDisc, ‖preSchwarzian (fun w => (f w⁻¹)⁻¹) z‖ ^ 2 := by
  let V : Set ℂ := unitDisc \ {0}
  let κ : ℂ → ℂ := fun z => preSchwarzian f z - 2 * deriv f z / f z + 2 / z
  let ψ : ℂ → ℂ := preSchwarzian (fun w => (f w⁻¹)⁻¹)
  have hU : IsOpen unitDiscExterior := isOpen_lt continuous_const continuous_norm
  have hV : IsOpen V := isOpen_ball.sdiff isClosed_singleton
  have hpull := a21_pullback hU isConformalOnto_inv_exterior hA
  have he : EqOn (fun z => ψ z⁻¹ * deriv (fun w : ℂ => w⁻¹) z) κ unitDiscExterior := by
    intro z hz
    have hz0 : z ≠ 0 := by intro h; subst z; norm_num [unitDiscExterior] at hz
    simpa only [ψ, κ, deriv_inv, div_eq_mul_inv, neg_mul, one_mul] using
      preSchwarzian_inversion (hf.analyticAt (hU.mem_nhds hz)) hz0 (h0 z hz)
        (LiZhongQC.deriv_ne_zero_of_injOn hU hf hi hz)
  have hN : normA21 unitDiscExterior κ = normA21 V ψ :=
    (preSchwarzian_inversion_area_exterior hf hi h0).trans
      (normA21_sdiff_singleton unitDisc ψ 0).symm
  have hκ : κ ∈ A21fun unitDiscExterior := by
    refine ⟨(differentiableOn_congr he).mp hpull.1, ?_⟩
    rw [hN]
    exact hA.2
  have hsq : ENNReal.ofReal (∫ z in unitDiscExterior, ‖κ z‖ ^ 2) =
      ENNReal.ofReal (∫ z in V, ‖ψ z‖ ^ 2) := by
    rw [← a21_norm_sq_eq_integral hU.measurableSet hκ,
      ← a21_norm_sq_eq_integral hV.measurableSet hA, hN]
  have hreal := congrArg ENNReal.toReal hsq
  rw [ENNReal.toReal_ofReal (integral_nonneg fun z => sq_nonneg ‖κ z‖),
    ENNReal.toReal_ofReal (integral_nonneg fun z => sq_nonneg ‖ψ z‖)] at hreal
  have hmeasure : volume.restrict V = volume.restrict unitDisc := by
    apply Measure.restrict_congr_set
    filter_upwards [volume.ae_ne (0 : ℂ)] with z hz
    simp [V, hz]
  change _ = ∫ z, ‖ψ z‖ ^ 2 ∂(volume.restrict unitDisc)
  rw [← hmeasure]
  exact hreal

/-- The point `[λ] ∈ T(1)` of `λ ∈ L∞(𝔻*)` (junk: the origin when `‖λ‖∞ ≥ 1`). -/
def ptT (l : LinfStar) : T1 := if h : l ∈ LinfStarBall then Phi ⟨l, h⟩ else originT

/-- `F` is (real) differentiable at `[ν]` in the Bers coordinate `ε_μ` of the chart `V_ν`. -/
def BersDiffAt (F : T1 → ℝ) (ν : LinfStar) (μ : ℂ → ℂ) : Prop :=
  DifferentiableAt ℝ (fun e : ℂ => F (ptT (beltramiMul (e • toLinf μ) ν))) 0

/-- `∂F/∂ε_μ([ν]) = ∂/∂ε|_{ε=0} F([εμ * ν])` (TT:4604), in the Bers coordinates of the chart `V_ν`. -/
def bersDz (F : T1 → ℝ) (ν : LinfStar) (μ : ℂ → ℂ) : ℂ :=
  dz (fun e => (F (ptT (beltramiMul (e • toLinf μ) ν)) : ℂ)) 0

/-- `∂²F/∂ε_μ∂ε̄_ν([κ])` (TT:5302), in the Bers coordinates of the chart `V_κ`. -/
def bersDzDzbar (F : T1 → ℝ) (κ : LinfStar) (μ ν : ℂ → ℂ) : ℂ :=
  dz (fun e₁ => dzbar (fun e₂ => (F (ptT (beltramiMul (e₁ • toLinf μ + e₂ • toLinf ν) κ)) : ℂ)) 0) 0

/-- The holomorphic 1-form `ϑ_{[μ]} = 𝒮(𝗀_μ) ∈ A₂(𝔻*)` on `T₀(1)` (TT:4664). -/
def vartheta (p : T1) : ℂ → ℂ := schwarzianHol (gsans (Quotient.out p : LinfStarBall))

/-- `ϑ` paired with a tangent vector: `ϑ_{[ν]}(μ) = ∬_{𝔻*} ϑ_{[ν]}(z) μ(z) d²z`. -/
def varthetaPair (p : T1) (μ : ℂ → ℂ) : ℂ := ∫ z in unitDiscExterior, vartheta p z * μ z

-- thm_3_1 moved unchanged to Ch2/S3FirstVariationCompleted (2026-10-28).

-- `vartheta_spec` moved to `Ch2/S3Var_Completed.lean` (2026-10-27).

-- cor_3_2 moved unchanged to Ch2/S3FirstVariationCompleted (2026-10-28).

/-- `S̃₁([μ]) = S₁([μ⁻¹])` (TT:4676). -/
def liouvilleS1Tilde (p : T1) : ℝ := liouvilleS1 (invT p)

/-- `f̃^μ = ι ∘ 𝖿^μ ∘ ι`, univalent on `𝔻*` (TT:4690). -/
def fTilde (μ : LinfStar) (z : ℂ) : ℂ := 1 / fsans μ (1 / z)
/-- `g̃_μ = ι ∘ 𝗀_μ ∘ ι`, univalent on `𝔻` (TT:4690).
- **[CORRECTION 2026-10-26]** The removable value `g̃_μ(0) = 0` is set explicitly: `gsans μ 0` is an unconstrained
  choice (the welding fixes `g_μ` only on `𝔻*`), so `1 / gsans μ (1 / 0)` was junk (found by 下属4). -/
def gTilde (μ : LinfStar) (z : ℂ) : ℂ := if z = 0 then 0 else 1 / gsans μ (1 / z)

-- `liouvilleS1Tilde_eq` moved to `Ch2/S3_Completed.lean` (2026-10-26).

/-- The real area energy of a one-form is conformally invariant (TT:4736–4778). -/
theorem integral_sq_norm_pullback {U V : Set ℂ} {f : ℂ → ℂ}
    (hU : IsOpen U) (hf : IsConformalOnto f U V) (ψ : ℂ → ℂ) :
    (∫ z in U, ‖ψ (f z) * deriv f z‖ ^ 2) = ∫ z in V, ‖ψ z‖ ^ 2 := by
  rw [← hf.2.2, integral_image_eq_integral_abs_det_fderiv_smul volume hU.measurableSet
    (fun z hz => ((hf.1.differentiableAt (hU.mem_nhds hz)).hasDerivAt.hasFDerivAt.restrictScalars
      ℝ).hasFDerivWithinAt) hf.2.1 (fun z => ‖ψ z‖ ^ 2)]
  apply setIntegral_congr_fun hU.measurableSet
  intro z _
  dsimp only
  rw [det_restrictScalars_toSpanSingleton, abs_of_nonneg (sq_nonneg _)]
  simp [smul_eq_mul, norm_mul, mul_pow, mul_comm]

/-- Polarization of the finite area energy, with all cross terms integrable
by the A21 hypotheses (TT:4736–4778). -/
theorem a21_integral_add_sq {ψ η : ℂ → ℂ} (hψ : ψ ∈ A21fun unitDisc)
    (hη : η ∈ A21fun unitDisc) :
    (∫ z in unitDisc, ‖ψ z + η z‖ ^ 2) =
      (∫ z in unitDisc, ‖ψ z‖ ^ 2) + (∫ z in unitDisc, ‖η z‖ ^ 2) +
        2 * (∫ z in unitDisc, ψ z * conj (η z)).re := by
  have hD : MeasurableSet unitDisc := isOpen_ball.measurableSet
  have hi : Integrable (fun z => ψ z * conj (η z)) (volume.restrict unitDisc) :=
    (a21_memLp_two hD hψ).integrable_mul (a21_memLp_two hD hη).star
  have hs := a21_integrable_sq hD hψ
  have ht := a21_integrable_sq hD hη
  have hx : Integrable (fun z => 2 * (ψ z * conj (η z)).re) (volume.restrict unitDisc) :=
    hi.re.const_mul 2
  have hst : Integrable (fun z => ‖ψ z‖ ^ 2 + ‖η z‖ ^ 2)
      (volume.restrict unitDisc) := hs.add ht
  have he (z : ℂ) : ‖ψ z + η z‖ ^ 2 = ‖ψ z‖ ^ 2 + ‖η z‖ ^ 2 +
      2 * (ψ z * conj (η z)).re := by
    simpa only [Complex.normSq_eq_norm_sq] using Complex.normSq_add (ψ z) (η z)
  have hre : (∫ z in unitDisc, (ψ z * conj (η z)).re) =
      (∫ z in unitDisc, ψ z * conj (η z)).re := integral_re hi
  simp_rw [he]
  rw [integral_add hst hx, integral_add hs ht, integral_const_mul, hre]

/-- Holomorphically equal functions have equal pre-Schwarzians on their open
domain; this handles inverse-map cancellation in TT:4736–4778. -/
theorem preSchwarzian_eqOn {U : Set ℂ} {f g : ℂ → ℂ}
    (hU : IsOpen U) (he : EqOn f g U) : EqOn (preSchwarzian f) (preSchwarzian g) U := by
  intro z hz
  simp only [preSchwarzian, he.deriv hU hz, (he.deriv hU).deriv hU hz]

/-- The explicit Möbius correction term in Lemma 3.4 (TT:4736–4778). -/
theorem preSchwarzian_blaschke {w z : ℂ} (hw : w ∈ unitDisc) (hz : z ∈ unitDisc) :
    preSchwarzian (blaschke w) z = 2 * conj w / (1 - conj w * z) := by
  have hwn : ‖w‖ < 1 := mem_ball_zero_iff.mp hw
  have hn := blaschke_den_ne_zero hwn (mem_ball_zero_iff.mp hz)
  have ha := one_sub_mul_conj_ne_zero hwn
  have ha' : 1 - conj w * w ≠ 0 := by simpa only [mul_comm] using ha
  have he : deriv (blaschke w) =ᶠ[𝓝 z]
      (fun u => (1 - w * conj w) / (1 - conj w * u) ^ 2) := by
    filter_upwards [isOpen_ball.mem_nhds hz] with u hu
    exact (hasDerivAt_blaschke hwn (mem_ball_zero_iff.mp hu)).deriv
  have hd := (hasDerivAt_const z (1 - w * conj w)).div
    ((((hasDerivAt_id z).const_mul (conj w)).const_sub 1).pow 2) (pow_ne_zero 2 hn)
  change HasDerivAt (fun u => (1 - w * conj w) / (1 - conj w * u) ^ 2) _ z at hd
  unfold preSchwarzian
  rw [he.deriv_eq, hd.deriv, (hasDerivAt_blaschke hwn (mem_ball_zero_iff.mp hz)).deriv]
  dsimp only [id_eq, Pi.pow_apply]
  field_simp [hn, ha, ha']
  ring

/-- Inverse disk maps turn the pre-Schwarzian chain rule into an additive
correction of one-forms (TT:4736–4778). -/
theorem preSchwarzian_inverse_pullback {f b g : ℂ → ℂ}
    (hf : IsConformalOnto f unitDisc unitDisc) (hb : IsConformalOnto b unitDisc unitDisc)
    (hinv : EqOn (f ∘ b) id unitDisc)
    (hg : DifferentiableOn ℂ g unitDisc) (hi : InjOn g unitDisc) {z : ℂ} (hz : z ∈ unitDisc) :
    preSchwarzian (g ∘ f) (b z) * deriv b z = preSchwarzian g z - preSchwarzian b z := by
  have hH : DifferentiableOn ℂ (g ∘ f) unitDisc := hg.comp hf.1 hf.mapsTo
  have hHi : InjOn (g ∘ f) unitDisc := hi.comp hf.2.1 hf.mapsTo
  have he : EqOn ((g ∘ f) ∘ b) g unitDisc := by
    intro u hu
    change g (f (b u)) = g u
    exact congrArg g (hinv hu)
  have hc := preSchwarzian_comp_of_analyticAt
    (hb.1.analyticAt (isOpen_ball.mem_nhds hz))
    (hH.analyticAt (isOpen_ball.mem_nhds (hb.mapsTo hz)))
    (deriv_ne_zero_of_injOn isOpen_ball hb.1 hb.2.1 hz)
    (deriv_ne_zero_of_injOn isOpen_ball hH hHi (hb.mapsTo hz))
  rw [preSchwarzian_eqOn isOpen_ball he hz] at hc
  linear_combination -hc

/-- The pre-Schwarzian energy after a disk automorphism, expressed through its
inverse correction; no integrability is silently inferred (TT:4736–4778). -/
theorem preSchwarzian_energy_inverse {f b g : ℂ → ℂ}
    (hf : IsConformalOnto f unitDisc unitDisc) (hb : IsConformalOnto b unitDisc unitDisc)
    (hinv : EqOn (f ∘ b) id unitDisc)
    (hg : DifferentiableOn ℂ g unitDisc) (hi : InjOn g unitDisc) :
    (∫ z in unitDisc, ‖preSchwarzian (g ∘ f) z‖ ^ 2) =
      ∫ z in unitDisc, ‖preSchwarzian g z - preSchwarzian b z‖ ^ 2 := by
  rw [← integral_sq_norm_pullback isOpen_ball hb (preSchwarzian (g ∘ f))]
  apply setIntegral_congr_fun isOpen_ball.measurableSet
  intro z hz
  exact congrArg (fun v : ℂ => ‖v‖ ^ 2) (preSchwarzian_inverse_pullback hf hb hinv hg hi hz)

/-- Rotating the source leaves the pre-Schwarzian energy and derivative norm
at the origin unchanged (TT:4736–4778). -/
theorem preSchwarzian_energy_rotation (g : ℂ → ℂ) {c : ℂ} (hc : ‖c‖ = 1) :
    (∫ z in unitDisc, ‖preSchwarzian (fun u => g (c * u)) z‖ ^ 2) +
        4 * π * Real.log ‖deriv (fun u => g (c * u)) 0‖ =
      (∫ z in unitDisc, ‖preSchwarzian g z‖ ^ 2) + 4 * π * Real.log ‖deriv g 0‖ := by
  have hconf : IsConformalOnto (fun z => c * z) unitDisc unitDisc := isConformalOnto_rotation hc
  have he (z : ℂ) : preSchwarzian (fun u => g (c * u)) z =
      preSchwarzian g (c * z) * deriv (fun u : ℂ => c * u) z := by
    have h := preSchwarzian_affine_precomp g c 0 z
    simpa [mul_comm] using h
  simp_rw [he]
  have henergy : (∫ z in unitDisc, ‖preSchwarzian g (c * z) * deriv (fun u : ℂ => c * u) z‖ ^ 2) =
      ∫ z in unitDisc, ‖preSchwarzian g z‖ ^ 2 :=
    integral_sq_norm_pullback isOpen_ball hconf (preSchwarzian g)
  rw [henergy]
  have hd := deriv_affine_precomp g c 0 0
  have hnorm : ‖deriv (fun u => g (c * u)) 0‖ = ‖deriv g 0‖ := by
    have hd' : deriv (fun u => g (c * u)) 0 = c * deriv g 0 := by simpa using hd
    rw [hd', norm_mul, hc, one_mul]
  rw [hnorm]

/-- The nonrotational part of Lemma 3.4: the cross term and the Möbius kernel
energy cancel the logarithm of the derivative at the origin (TT:4736–4778). -/
theorem lemma_3_4_blaschke {g : ℂ → ℂ} (hg : DifferentiableOn ℂ g unitDisc)
    (hinj : InjOn g unitDisc) (hA : preSchwarzian g ∈ A21fun unitDisc)
    {w : ℂ} (hw : w ∈ unitDisc) :
    (∫ z in unitDisc, ‖preSchwarzian (g ∘ blaschke (-w)) z‖ ^ 2) +
        4 * π * Real.log ‖deriv (g ∘ blaschke (-w)) 0‖ =
      (∫ z in unitDisc, ‖preSchwarzian g z‖ ^ 2) + 4 * π * Real.log ‖deriv g 0‖ := by
  have hD : MeasurableSet unitDisc := isOpen_ball.measurableSet
  have hwn : ‖w‖ < 1 := mem_ball_zero_iff.mp hw
  have hwn' : ‖-w‖ < 1 := by simpa using hwn
  have hf := isConformalOnto_blaschke hwn'
  have hb := isConformalOnto_blaschke hwn
  have hinv : EqOn (blaschke (-w) ∘ blaschke w) id unitDisc := by
    intro z hz
    exact blaschke_neg_blaschke hwn (mem_ball_zero_iff.mp hz)
  let K : ℂ → ℂ := fun z => conj w / (1 - conj w * z)
  have hK : K ∈ A21fun unitDisc := dirichlet_kernel_mem_A21 hw
  have hQ := a21_const_mul hD hK (-2)
  have hquad := a21_integral_add_sq hA hQ
  have hcov := preSchwarzian_energy_inverse hf hb hinv hg hinj
  have heq : (∫ z in unitDisc, ‖preSchwarzian (g ∘ blaschke (-w)) z‖ ^ 2) =
      ∫ z in unitDisc, ‖preSchwarzian g z + (-2 : ℂ) * K z‖ ^ 2 := by
    rw [hcov]
    apply setIntegral_congr_fun hD
    intro z hz
    dsimp only
    rw [preSchwarzian_blaschke hw hz]
    congr 1
    dsimp only [K]
    ring
  have hnorm : (∫ z in unitDisc, ‖(-2 : ℂ) * K z‖ ^ 2) =
      4 * (∫ z in unitDisc, ‖K z‖ ^ 2) := by
    calc
      _ = ∫ z in unitDisc, 4 * ‖K z‖ ^ 2 := by
        apply integral_congr_ae
        exact Eventually.of_forall fun z => by norm_num [norm_mul, mul_pow]
      _ = _ := integral_const_mul _ _
  have hcross : (∫ z in unitDisc, preSchwarzian g z * conj ((-2 : ℂ) * K z)) =
      (-2 : ℂ) * (∫ z in unitDisc, preSchwarzian g z * (w / (1 - w * conj z))) := by
    calc
      _ = ∫ z in unitDisc, (-2 : ℂ) * (preSchwarzian g z * (w / (1 - w * conj z))) := by
        apply integral_congr_ae
        exact Eventually.of_forall fun z => by
          simp [K, show conj (2 : ℂ) = 2 from conj_ofReal 2] <;> ring
      _ = _ := integral_const_mul _ _
  have hKE : (∫ z in unitDisc, ‖K z‖ ^ 2) = -π * Real.log (1 - ‖w‖ ^ 2) :=
    dirichlet_kernel_energy hw
  have hp : 0 < 1 - ‖w‖ ^ 2 := by nlinarith [norm_nonneg w]
  have hdB : deriv (blaschke (-w)) 0 = ((1 - ‖w‖ ^ 2 : ℝ) : ℂ) := by
    rw [(hasDerivAt_blaschke hwn' (by simp)).deriv]
    simp only [map_neg, mul_neg, neg_mul, neg_neg, mul_zero, sub_zero, one_pow,
      div_one, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    push_cast
    rfl
  have hderiv : deriv (g ∘ blaschke (-w)) 0 = deriv g w * ((1 - ‖w‖ ^ 2 : ℝ) : ℂ) := by
    rw [deriv_comp 0 (hg.differentiableAt (isOpen_ball.mem_nhds (hf.mapsTo (by simp [unitDisc]))))
      (hf.1.differentiableAt (isOpen_ball.mem_nhds (by simp [unitDisc]))), blaschke_neg_zero, hdB]
  have hlog : Real.log ‖deriv (g ∘ blaschke (-w)) 0‖ =
      Real.log ‖deriv g w‖ + Real.log (1 - ‖w‖ ^ 2) := by
    rw [hderiv, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hp,
      Real.log_mul (norm_ne_zero_iff.mpr (deriv_ne_zero_of_injOn isOpen_ball hg hinj hw)) hp.ne']
  rw [heq, hquad, hnorm, hKE, hcross, hlog]
  simp only [Complex.mul_re]
  norm_num
  rw [preSchwarzian_dirichlet_integral hg hinj hA hw]
  ring

/-- **Lemma 3.4** (TT:4730–4778), in the form its proof reduces to. For `g` univalent on `𝔻` with `𝒜(g) ∈ A₂¹(𝔻)` and
`α(z) = e^{iθ}(z - w)/(1 - z w̄)` (`w ∈ 𝔻`):
`∬_𝔻 |𝒜(g ∘ α⁻¹)|² + 4π log |(g ∘ α⁻¹)'(0)| = ∬_𝔻 |𝒜(g)|² + 4π log |g'(0)|`.

Hence `S̃` is constant on the fibers of `𝒯₀(1) → T₀(1)`, `S̃ = S̃₁ ∘ π`. -/
theorem lemma_3_4 {g : ℂ → ℂ} (hg : DifferentiableOn ℂ g unitDisc) (hinj : InjOn g unitDisc)
    (hA : preSchwarzian g ∈ A21fun unitDisc) {w : ℂ} (hw : w ∈ unitDisc) (θ : ℝ) :
    let αinv : ℂ → ℂ := fun z => (exp (-(θ * I)) * z + w) / (1 + conj w * exp (-(θ * I)) * z)
    (∫ z in unitDisc, ‖preSchwarzian (g ∘ αinv) z‖ ^ 2) + 4 * π * Real.log ‖deriv (g ∘ αinv) 0‖ =
      (∫ z in unitDisc, ‖preSchwarzian g z‖ ^ 2) + 4 * π * Real.log ‖deriv g 0‖ := by
  dsimp only
  let c : ℂ := exp (-(θ * I))
  have hc : ‖c‖ = 1 := by simp [c, Complex.norm_exp, Complex.mul_re]
  have he : (g ∘ fun z => (c * z + w) / (1 + conj w * c * z)) =
      (fun z => (g ∘ blaschke (-w)) (c * z)) := by
    funext z
    simp [Function.comp_apply, blaschke, mul_assoc]
  change (∫ z in unitDisc, ‖preSchwarzian (g ∘ fun u => (c * u + w) / (1 + conj w * c * u)) z‖ ^ 2) +
      4 * π * Real.log ‖deriv (g ∘ fun u => (c * u + w) / (1 + conj w * c * u)) 0‖ = _
  rw [he]
  exact (preSchwarzian_energy_rotation (g ∘ blaschke (-w)) hc).trans (lemma_3_4_blaschke hg hinj hA hw)

-- `thm_3_5` moved to `TakhtajanTeo.Ch2.S3Density` (2026-10-29, Program G).

-- `lemma_3_6` moved to `TakhtajanTeo.Ch2.S3Lemma36` (2026-10-29, Program G).

-- `cor_3_7` moved to `TakhtajanTeo.Ch2.S3Density` (2026-10-29, Program G).

-- `thm_3_8` moved to `TakhtajanTeo.Ch2.S3Density` (2026-10-29, Program G).

-- `cor_3_9` moved to `TakhtajanTeo.Ch2.S3Density` (2026-10-29, Program G).

-- `remark_3_10` moved to `TakhtajanTeo.Ch2.S3Remark310` (2026-10-29, Program G).

end Ch2

end TakhtajanTeo
