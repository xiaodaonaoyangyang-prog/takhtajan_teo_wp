import TakhtajanTeo.Ch1.S6_HyperbolicMetricVariation
import TakhtajanTeo.Ch1.ResolventBoundarySmoothness
import TakhtajanTeo.Ch1.QCVariationBergman

/-!
# Chapter 1, §7 — Riemann curvature tensor (TT:2676–3156)

* §7.1 `Q(μ, ν)`, Proposition 7.1 with (7.1)–(7.5), `Q̇(μ)[ν]`, Proposition 7.2 with (7.6), Corollary 7.3,
  Theorem 7.4 with (7.7), the orthonormal basis `μ_n`, Corollary 7.5 (Kähler, geodesic Bers coordinates)
* §7.2 the Riemann tensor `R_{k l̄ m n̄}`, Theorem 7.7, Lemma 7.8, Corollary 7.9
* §7.3 the Ricci tensor, the kernel `B` (7.8), Theorem 7.11 (`𝓡_{k l̄} = -13/(12π) δ_{kl}`), Corollary 7.12
  (Kähler–Einstein), sectional curvature (7.9), Theorem 7.14 (negative curvatures)

**Modelling.**
- `ε`-derivatives are taken pointwise, so `Q`, `P` and `R` are used in function form: `harmonicProjFun`, `RnmFun`,
  `Qfun`. They are the formulas (1.6), (1.7) applied to functions.
- `( , )` is the inner product of `L²(𝔻*, ρ d²z)` (`l2Inner`), and `G(f) = resolventStar f`.
- The Riemann tensor follows [YB53] (TT:2873): `R_{k l̄ m n̄} = -∂²g_{k l̄}/∂ε_m∂ε̄_n(0)`, in the polarized form of
  TT:3009.
- The `𝕌`-model formulas (7.1)–(7.5) are stated with the `𝕌`-model versions of `P` (1.23) and `R` (1.6).

**Readings.**
- The kernel `B` (TT:3053–3082) is evaluated with the resolvent kernel of `𝔻`. The formula for `B(0, v)` uses
  `G(0, w) = (1/2π)((1 + |w|²)/(1 - |w|²)) log(1/|w|²) - 1/π`, i.e. the center `0 ∈ 𝔻`. The memoir writes `𝔻*`, but
  the identity is model independent; `B` is stated on `𝔻`.

**Not stated.**
- Remarks 7.6, 7.10, 7.13 (citations).
- The bounds on the auxiliary integrals `I₁, …, I₆` in the proof of Lemma 7.8.
-/

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal ComplexConjugate Classical Real

noncomputable section

namespace TakhtajanTeo

open LiZhongQC

/-- The inner product `(f, g) = ∬_{𝔻*} f ḡ ρ d²z` of `L²(𝔻*, ρ d²z)` (TT:2768). -/
def l2Inner (f g : ℂ → ℂ) : ℂ := ∫ z in unitDiscExterior, f z * conj (g z) * rho z

/-- The projection (1.7) applied to a function: `(Pm)(z) = (3(1 - |z|²)²/π) ∬_{𝔻*} m(ζ)/(1 - ζ z̄)⁴ d²ζ`. -/
def harmonicProjFun (m : ℂ → ℂ) (z : ℂ) : ℂ :=
  3 * (1 - ‖z‖ ^ 2) ^ 2 / π * ∫ ζ in unitDiscExterior, m ζ / (1 - ζ * conj z) ^ 4

/-- `R(ν, μ)` of (1.6) as a function: `((ν/(1 - |μ|²)) (w_μ)_z/\overline{(w_μ)_z}) ∘ w_μ⁻¹`. -/
def RnmFun (ν μ : LinfStar) (z : ℂ) : ℂ :=
  (fun u => ν u / (1 - ‖μ u‖ ^ 2) * (dz (wA μ) u / conj (dz (wA μ) u))) (Function.invFun (wA μ) z)

/-- `Q(μ, ν) = P(R(μ, ν)) ∘ w_ν · (\overline{w_ν})_{z̄}/(w_ν)_z` (TT:2683), with
`(\overline{w_ν})_{z̄} = \overline{(w_ν)_z}`. -/
def Qfun (μ ν : LinfStar) (z : ℂ) : ℂ :=
  harmonicProjFun (RnmFun μ ν) (wA ν z) * (conj (dz (wA ν) z) / dz (wA ν) z)

/-- `Q̇(μ)[ν] = ∂/∂ε̄|_{ε=0} Q(μ, εν)` (TT:2759). -/
def Qdot (μ ν : LinfStar) (z : ℂ) : ℂ := dzbar (fun ε => Qfun μ (ε • ν) z) 0

/-! ## §7.1 The first variation of the Weil–Petersson metric -/

-- `prop_7_1` moved to `Ch1/S7Prop71.lean` (2026-10-28).

/-- `R(ν, μ)` of (1.6) in the model `𝕌`: `((ν/(1 - |μ|²)) (w_μ)_z/\overline{(w_μ)_z}) ∘ w_μ⁻¹`, with `w_μ = wU μ`. -/
def RnmFunU (ν μ : ℂ → ℂ) (z : ℂ) : ℂ :=
  (fun u => ν u / (1 - ‖μ u‖ ^ 2) * (dz (wU μ) u / conj (dz (wU μ) u))) (Function.invFun (wU μ) z)

/-- `Q(μ, ν)` in the model `𝕌`, with `P` of (1.23). -/
def QfunU (μ ν : ℂ → ℂ) (z : ℂ) : ℂ :=
  harmonicProjU (RnmFunU μ ν) (wU ν z) * (conj (dz (wU ν) z) / dz (wU ν) z)

-- `eq_7_1` moved to `Ch1/S7First.lean` (2026-10-28).

-- `eq_7_2` moved to `Ch1/S7First.lean` (2026-10-28).

-- `eq_7_3` moved to `Ch1/S7First.lean` (2026-10-28).

/-- (TT:2723) `1/((u - v)(u - z̄)(v - z̄)) = (1/(u - v)²)(1/(v - z̄) - 1/(u - z̄))`. -/
theorem eq_7_4_identity {u v z : ℂ} (h1 : u - v ≠ 0) (h2 : u - conj z ≠ 0) (h3 : v - conj z ≠ 0) :
    1 / ((u - v) * (u - conj z) * (v - conj z)) = 1 / (u - v) ^ 2 * (1 / (v - conj z) - 1 / (u - conj z)) := by
  field_simp
  ring

/-- Points in the upper half-plane do not meet the conjugates of other upper-half-plane
points; these are the nonsingular denominators in (7.4) (TT:2729). -/
theorem eq_7_4_sub_conj_ne_zero {u z : ℂ} (hu : u ∈ upperHalf) (hz : z ∈ upperHalf) :
    u - conj z ≠ 0 := by
  intro h
  have hi := congrArg Complex.im h
  simp only [Complex.sub_im, Complex.conj_im, Complex.zero_im] at hi
  change 0 < u.im at hu
  change 0 < z.im at hz
  linarith

/-- The four-term algebraic decomposition of the kernel in (7.4) (TT:2729). -/
theorem eq_7_4_four_terms {u v z : ℂ} (h1 : u - v ≠ 0) (h2 : u - conj z ≠ 0)
    (h3 : v - conj z ≠ 0) :
    1 / ((u - conj z) ^ 2 * (u - v) ^ 2 * (v - conj z) ^ 2) =
      1 / ((u - v) ^ 4 * (v - conj z) ^ 2) - 2 / ((u - v) ^ 5 * (v - conj z)) +
        2 / ((u - v) ^ 5 * (u - conj z)) + 1 / ((u - v) ^ 4 * (u - conj z) ^ 2) := by
  field_simp
  ring

/-- The equality of finite-cutoff integrals in (7.4), before the analytic cancellation
needed for the principal-value limit; no harmonicity assumption is needed (TT:2729). -/
theorem eq_7_4_integral_identity (μ ν : ℂ → ℂ) {z : ℂ} (hz : z ∈ upperHalf)
    {δ : ℝ} (hδ : 0 < δ) :
    (∫ p in (upperHalf ×ˢ upperHalf) ∩ {p : ℂ × ℂ | δ ≤ ‖p.1 - p.2‖},
        μ p.1 * ν p.2 / ((p.1 - conj z) ^ 2 * (p.1 - p.2) ^ 2 * (p.2 - conj z) ^ 2)) =
      ∫ p in (upperHalf ×ˢ upperHalf) ∩ {p : ℂ × ℂ | δ ≤ ‖p.1 - p.2‖},
        (1 / ((p.1 - p.2) ^ 4 * (p.2 - conj z) ^ 2) - 2 / ((p.1 - p.2) ^ 5 * (p.2 - conj z)) +
          2 / ((p.1 - p.2) ^ 5 * (p.1 - conj z)) + 1 / ((p.1 - p.2) ^ 4 * (p.1 - conj z) ^ 2)) *
          μ p.1 * ν p.2 := by
  have hU : IsOpen upperHalf := isOpen_lt continuous_const Complex.continuous_im
  have hcut : MeasurableSet {p : ℂ × ℂ | δ ≤ ‖p.1 - p.2‖} :=
    isClosed_le continuous_const ((continuous_fst.sub continuous_snd).norm) |>.measurableSet
  apply setIntegral_congr_fun ((hU.measurableSet.prod hU.measurableSet).inter hcut)
  intro p hp
  have huv : p.1 - p.2 ≠ 0 := by
    intro heq
    have hbound := hp.2
    change δ ≤ ‖p.1 - p.2‖ at hbound
    rw [heq, norm_zero] at hbound
    exact (not_le_of_gt hδ) hbound
  dsimp only
  rw [← eq_7_4_four_terms huv (eq_7_4_sub_conj_ne_zero hp.1.1 hz)
    (eq_7_4_sub_conj_ne_zero hp.1.2 hz)]
  ring

-- `eq_7_4` moved to `Ch1/S7Eq74.lean` (2026-10-28).

-- `eq_7_5` moved to `Ch1/S7First.lean` (2026-10-28).


/-- Local smoothness of the holomorphic Wirtinger derivative on an open set,
used in the factorization at TT:2787. -/
theorem wp_contDiffOn_dz {D : Set ℂ} {f : ℂ → ℂ} {n m : WithTop ℕ∞}
    (hf : ContDiffOn ℝ n f D) (hD : IsOpen D) (hmn : m + 1 ≤ n) :
    ContDiffOn ℝ m (dz f) D := by
  have hd := hf.fderiv_of_isOpen hD hmn
  have h1 := hd.clm_apply (contDiffOn_const (c := (1 : ℂ)))
  have hI := hd.clm_apply (contDiffOn_const (c := I))
  exact (h1.sub (contDiffOn_const.mul hI)).div_const 2

/-- Local smoothness of the antiholomorphic Wirtinger derivative on an open set,
used in the factorization at TT:2787. -/
theorem wp_contDiffOn_dzbar {D : Set ℂ} {f : ℂ → ℂ} {n m : WithTop ℕ∞}
    (hf : ContDiffOn ℝ n f D) (hD : IsOpen D) (hmn : m + 1 ≤ n) :
    ContDiffOn ℝ m (dzbar f) D := by
  have hd := hf.fderiv_of_isOpen hD hmn
  have h1 := hd.clm_apply (contDiffOn_const (c := (1 : ℂ)))
  have hI := hd.clm_apply (contDiffOn_const (c := I))
  exact (h1.add (contDiffOn_const.mul hI)).div_const 2

/-- Fréchet derivative of the holomorphic Wirtinger derivative, expressed in
the two real coordinate directions (TT:2787). -/
theorem wp_fderiv_dz {f : ℂ → ℂ} {z : ℂ} (hf : DifferentiableAt ℝ (fderiv ℝ f) z) :
    fderiv ℝ (dz f) z = (1 / 2 : ℂ) •
      (fderiv ℝ (fun w => fderiv ℝ f w 1) z - I • fderiv ℝ (fun w => fderiv ℝ f w I) z) := by
  have h1 := hf.clm_apply (differentiableAt_const (1 : ℂ))
  have hI := hf.clm_apply (differentiableAt_const I)
  have heq : dz f = fun w => (1 / 2 : ℂ) * (fderiv ℝ f w 1 - I * fderiv ℝ f w I) := by
    funext w
    unfold dz
    ring
  rw [heq]
  exact ((h1.hasFDerivAt.sub (hI.hasFDerivAt.const_mul I)).const_mul (1 / 2 : ℂ)).fderiv

/-- Fréchet derivative of the antiholomorphic Wirtinger derivative, expressed in
the two real coordinate directions (TT:2787). -/
theorem wp_fderiv_dzbar {f : ℂ → ℂ} {z : ℂ} (hf : DifferentiableAt ℝ (fderiv ℝ f) z) :
    fderiv ℝ (dzbar f) z = (1 / 2 : ℂ) •
      (fderiv ℝ (fun w => fderiv ℝ f w 1) z + I • fderiv ℝ (fun w => fderiv ℝ f w I) z) := by
  have h1 := hf.clm_apply (differentiableAt_const (1 : ℂ))
  have hI := hf.clm_apply (differentiableAt_const I)
  have heq : dzbar f = fun w => (1 / 2 : ℂ) * (fderiv ℝ f w 1 + I * fderiv ℝ f w I) := by
    funext w
    unfold dzbar
    ring
  rw [heq]
  exact ((h1.hasFDerivAt.add (hI.hasFDerivAt.const_mul I)).const_mul (1 / 2 : ℂ)).fderiv

/-- Mixed Wirtinger derivatives commute for C2 functions, by symmetry of the
second real Fréchet derivative (TT:2787). -/
theorem wp_wirtinger_comm {f : ℂ → ℂ} {z : ℂ} (hf : ContDiffAt ℝ 2 f z) :
    dz (dzbar f) z = dzbar (dz f) z := by
  have hd : DifferentiableAt ℝ (fderiv ℝ f) z :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have hs := hf.isSymmSndFDerivAt (by norm_num)
  have hdir (a b : ℂ) : fderiv ℝ (fun w => fderiv ℝ f w a) z b =
      fderiv ℝ (fderiv ℝ f) z b a := by
    rw [fderiv_clm_apply hd (differentiableAt_const a)]
    simp
  change (fderiv ℝ (dzbar f) z 1 - I * fderiv ℝ (dzbar f) z I) / 2 =
    (fderiv ℝ (dz f) z 1 + I * fderiv ℝ (dz f) z I) / 2
  rw [wp_fderiv_dzbar hd, wp_fderiv_dz hd]
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.sub_apply, smul_eq_mul]
  rw [hdir 1 1, hdir I 1, hdir 1 I, hdir I I, hs 1 I]
  ring

/-- Constant-multiple rule for the holomorphic Wirtinger derivative (TT:2787). -/
theorem wp_dz_const_mul {f : ℂ → ℂ} {z : ℂ} (hf : DifferentiableAt ℝ f z) (c : ℂ) :
    dz (fun w => c * f w) z = c * dz f z := by
  unfold dz
  rw [fderiv_const_mul hf c]
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

/-- Constant-multiple rule for the antiholomorphic Wirtinger derivative (TT:2787). -/
theorem wp_dzbar_const_mul {f : ℂ → ℂ} {z : ℂ} (hf : DifferentiableAt ℝ f z) (c : ℂ) :
    dzbar (fun w => c * f w) z = c * dzbar f z := by
  unfold dzbar
  rw [fderiv_const_mul hf c]
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

/-- Sum rule for the holomorphic Wirtinger derivative (TT:2787). -/
theorem wp_dz_add {f g : ℂ → ℂ} {z : ℂ} (hf : DifferentiableAt ℝ f z)
    (hg : DifferentiableAt ℝ g z) : dz (fun w => f w + g w) z = dz f z + dz g z := by
  unfold dz
  rw [fderiv_fun_add hf hg]
  simp only [ContinuousLinearMap.add_apply]
  ring

/-- Sum rule for the antiholomorphic Wirtinger derivative (TT:2787). -/
theorem wp_dzbar_add {f g : ℂ → ℂ} {z : ℂ} (hf : DifferentiableAt ℝ f z)
    (hg : DifferentiableAt ℝ g z) : dzbar (fun w => f w + g w) z = dzbar f z + dzbar g z := by
  unfold dzbar
  rw [fderiv_fun_add hf hg]
  simp only [ContinuousLinearMap.add_apply]
  ring

/-- Difference rule for the antiholomorphic Wirtinger derivative (TT:2787). -/
theorem wp_dzbar_sub {f g : ℂ → ℂ} {z : ℂ} (hf : DifferentiableAt ℝ f z)
    (hg : DifferentiableAt ℝ g z) : dzbar (fun w => f w - g w) z = dzbar f z - dzbar g z := by
  unfold dzbar
  rw [fderiv_fun_sub hf hg]
  simp only [ContinuousLinearMap.sub_apply]
  ring

/-- Reciprocal rule for the holomorphic Wirtinger derivative away from zero
(TT:2787). -/
theorem wp_dz_inv {f : ℂ → ℂ} {z : ℂ} (hf : DifferentiableAt ℝ f z) (hne : f z ≠ 0) :
    dz (fun w => (f w)⁻¹) z = -((f z) ^ 2)⁻¹ * dz f z := by
  have hi : DifferentiableAt ℂ (fun w : ℂ => w⁻¹) (f z) :=
    (hasDerivAt_inv hne).differentiableAt
  have hchain := eq6_2_dz_comp hf (hi.restrictScalars ℝ)
  rw [dz_eq_deriv hi, (cauchyRiemann_iff.mp hi).2, (hasDerivAt_inv hne).deriv] at hchain
  simpa only [Function.comp_def, zero_mul, add_zero] using hchain



/-- The disk boundary factor does not vanish inside the disk (TT:2787). -/
theorem wp_disk_factor_ne_zero {z : ℂ} (hz : z ∈ unitDisc) : 1 - z * conj z ≠ 0 := by
  have hn : ‖z‖ < 1 := mem_ball_zero_iff.mp hz
  have h : (1 : ℝ) - ‖z‖ ^ 2 ≠ 0 := by nlinarith [norm_nonneg z]
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  exact_mod_cast h

/-- Global real smoothness of the polynomial reciprocal density (TT:2787). -/
theorem wp_rho_inv_contDiff : ContDiff ℝ ⊤ (fun z => (rho z : ℂ)⁻¹) := by
  have heq : (fun z => (rho z : ℂ)⁻¹) = (fun z => (1 - z * conj z) ^ 2 / 4) :=
    funext wp_rho_inv_complex
  rw [heq]
  have hq : ContDiff ℝ ⊤ (fun z : ℂ => 1 - z * conj z) :=
    contDiff_const.sub (contDiff_id.mul Complex.conjCLE.contDiff)
  exact (hq.pow 2).div_const 4

/-- Real smoothness of the density on the open disk (TT:2787). -/
theorem wp_rho_contDiffOn : ContDiffOn ℝ ⊤ (fun z => (rho z : ℂ)) unitDisc := by
  have heq : (fun z => (rho z : ℂ)) = (fun z => 4 / (1 - z * conj z) ^ 2) :=
    funext wp_rho_complex
  rw [heq]
  have hq : ContDiff ℝ ⊤ (fun z : ℂ => 1 - z * conj z) :=
    contDiff_const.sub (contDiff_id.mul Complex.conjCLE.contDiff)
  have hc : ContDiffOn ℝ ⊤ (fun _ : ℂ => (4 : ℂ)) unitDisc := contDiffOn_const
  simpa only [Pi.mul_apply, Pi.inv_apply, div_eq_mul_inv] using
    hc.mul ((hq.contDiffOn.pow 2).inv (fun z hz => pow_ne_zero 2 (wp_disk_factor_ne_zero hz)))

/-- Holomorphic derivative of the disk boundary factor (TT:2787). -/
theorem wp_dz_disk_factor (z : ℂ) : dz (fun w => 1 - w * conj w) z = -conj z := by
  have hid : DifferentiableAt ℝ (fun w : ℂ => w) z := differentiableAt_id
  have hc : DifferentiableAt ℝ (conj : ℂ → ℂ) z := Complex.differentiable_conj.differentiableAt
  have hprod : DifferentiableAt ℝ (fun w : ℂ => w * conj w) z := hid.mul hc
  have hc0 : dz (conj : ℂ → ℂ) z = 0 := by
    simpa [dzbar, fderiv_id] using (dz_conj (f := id) (z := z) hid)
  rw [dz_sub_pointwise (differentiableAt_const (1 : ℂ)) hprod, dz_mul hid hc,
    hc0, show dz (fun w : ℂ => w) z = 1 from rhoVar_dz_id z]
  simp [dz]

/-- Antiholomorphic derivative of the disk boundary factor (TT:2787). -/
theorem wp_dzbar_disk_factor (z : ℂ) : dzbar (fun w => 1 - w * conj w) z = -z := by
  have hid : DifferentiableAt ℝ (fun w : ℂ => w) z := differentiableAt_id
  have hc : DifferentiableAt ℝ (conj : ℂ → ℂ) z := Complex.differentiable_conj.differentiableAt
  have hprod : DifferentiableAt ℝ (fun w : ℂ => w * conj w) z := hid.mul hc
  have hc1 : dzbar (conj : ℂ → ℂ) z = 1 := by
    simpa [dz, fderiv_id] using (dzbar_conj (f := id) (z := z) hid)
  have hi0 : dzbar (fun w : ℂ => w) z = 0 := by simp [dzbar, fderiv_id]
  rw [wp_dzbar_sub (differentiableAt_const (1 : ℂ)) hprod, dzbar_mul hid hc, hc1, hi0]
  simp [dzbar]

/-- Parameter-dependent holomorphic differentiation in the first variable (TT:2781). -/
def wp_paramDz (F : ℂ × ℂ → ℂ) (p : ℂ × ℂ) : ℂ :=
  dz (fun z => F (z, p.2)) p.1

/-- Parameter-dependent antiholomorphic differentiation in the first variable (TT:2781). -/
def wp_paramDzbar (F : ℂ × ℂ → ℂ) (p : ℂ × ℂ) : ℂ :=
  dzbar (fun z => F (z, p.2)) p.1

/-- First-variable differentiation preserves smooth dependence on both parameters (TT:2781). -/
theorem wp_paramDz_contDiffAt {F : ℂ × ℂ → ℂ} {p : ℂ × ℂ}
    (hF : ContDiffAt ℝ (⊤ : ℕ∞) F p) :
    ContDiffAt ℝ (⊤ : ℕ∞) (wp_paramDz F) p := by
  have h : ContDiffAt ℝ (⊤ : ℕ∞)
      (fun q : (ℂ × ℂ) × ℂ => F (q.2, q.1.2)) (p, p.1) :=
    hF.comp _ (contDiffAt_snd.prodMk contDiffAt_fst.snd)
  have hd := h.fderiv (f := fun (p : ℂ × ℂ) z => F (z, p.2))
    (g := fun p : ℂ × ℂ => p.1) (x₀ := p) (n := (⊤ : ℕ∞)) contDiffAt_fst
    (m := (⊤ : ℕ∞)) (by simp)
  exact ((hd.clm_apply contDiffAt_const).sub
    (contDiffAt_const.mul (hd.clm_apply contDiffAt_const))).div_const 2

/-- The conjugate first-variable derivative also preserves smooth parameter dependence (TT:2781). -/
theorem wp_paramDzbar_contDiffAt {F : ℂ × ℂ → ℂ} {p : ℂ × ℂ}
    (hF : ContDiffAt ℝ (⊤ : ℕ∞) F p) :
    ContDiffAt ℝ (⊤ : ℕ∞) (wp_paramDzbar F) p := by
  have h : ContDiffAt ℝ (⊤ : ℕ∞)
      (fun q : (ℂ × ℂ) × ℂ => F (q.2, q.1.2)) (p, p.1) :=
    hF.comp _ (contDiffAt_snd.prodMk contDiffAt_fst.snd)
  have hd := h.fderiv (f := fun (p : ℂ × ℂ) z => F (z, p.2))
    (g := fun p : ℂ × ℂ => p.1) (x₀ := p) (n := (⊤ : ℕ∞)) contDiffAt_fst
    (m := (⊤ : ℕ∞)) (by simp)
  exact ((hd.clm_apply contDiffAt_const).add
    (contDiffAt_const.mul (hd.clm_apply contDiffAt_const))).div_const 2

/-- The boundary factor in complex polynomial coordinates (TT:2781). -/
def wp_boundaryQ (z : ℂ) : ℂ := 1 - z * conj z

/-- Weighted kernel with the boundary variable first (TT:2781). -/
def wp_boundaryW (p : ℂ × ℂ) : ℂ := resolventBoundaryKernel p.2 p.1

/-- Smooth residual factor in the first derivative of the kernel (TT:2781). -/
def wp_boundaryV (p : ℂ × ℂ) : ℂ :=
  -conj p.1 / 2 * wp_boundaryW p + wp_boundaryQ p.1 / 4 * wp_paramDz wp_boundaryW p

/-- Smooth residual factor in the twice differentiated weighted kernel (TT:2781). -/
def wp_boundaryB (p : ℂ × ℂ) : ℂ :=
  -(3 : ℂ) * conj p.1 / 4 * wp_boundaryV p +
    wp_boundaryQ p.1 / 4 * wp_paramDz wp_boundaryV p

/-- The kernel residual factor is smooth through the outer circle (TT:2781). -/
theorem wp_boundaryW_contDiffAt {z w : ℂ} (hz : ‖z‖ ≤ 1)
    (hw : w ∈ unitDisc) (hzw : z ≠ w) :
    ContDiffAt ℝ (⊤ : ℕ∞) wp_boundaryW (z, w) := by
  have h := wp_boundaryKernel_contDiffAt hw (mem_closedBall_zero_iff.mpr hz) hzw.symm
  have hs : ContDiffAt ℝ (⊤ : ℕ∞)
      (fun p : ℂ × ℂ => resolventBoundaryKernel p.2 p.1) (z, w) :=
    h.comp (z, w) (contDiffAt_snd.prodMk contDiffAt_fst)
  exact Complex.ofRealCLM.contDiff.contDiffAt.comp (z, w) hs

/-- The polynomial boundary factor is globally smooth (TT:2781). -/
theorem wp_boundaryQ_contDiff : ContDiff ℝ (⊤ : ℕ∞) wp_boundaryQ := by
  exact contDiff_const.sub (contDiff_id.mul Complex.conjCLE.contDiff)

/-- Smoothness of the first derivative's residual factor (TT:2781). -/
theorem wp_boundaryV_contDiffAt {p : ℂ × ℂ}
    (h : ContDiffAt ℝ (⊤ : ℕ∞) wp_boundaryW p) :
    ContDiffAt ℝ (⊤ : ℕ∞) wp_boundaryV p := by
  exact (((Complex.conjCLE.contDiff.contDiffAt.comp _ contDiffAt_fst).neg.div_const 2).mul h).add
    (((wp_boundaryQ_contDiff.contDiffAt.comp _ contDiffAt_fst).div_const 4).mul
      (wp_paramDz_contDiffAt h))

/-- Smoothness of the weighted second derivative's residual factor (TT:2781). -/
theorem wp_boundaryB_contDiffAt {p : ℂ × ℂ}
    (h : ContDiffAt ℝ (⊤ : ℕ∞) wp_boundaryW p) :
    ContDiffAt ℝ (⊤ : ℕ∞) wp_boundaryB p := by
  have hv := wp_boundaryV_contDiffAt h
  exact ((contDiffAt_const.mul
    (Complex.conjCLE.contDiff.contDiffAt.comp _ contDiffAt_fst)).div_const 4 |>.mul hv).add
    (((wp_boundaryQ_contDiff.contDiffAt.comp _ contDiffAt_fst).div_const 4).mul
      (wp_paramDz_contDiffAt hv))

/-- Holomorphic differentiation depends only on a neighborhood germ (TT:2781). -/
theorem wp_dz_congr_of_eventuallyEq {f g : ℂ → ℂ} {z : ℂ}
    (h : f =ᶠ[𝓝 z] g) : dz f z = dz g z := by
  simp only [dz, h.fderiv_eq]

/-- Power rule for the holomorphic Wirtinger derivative (TT:2781). -/
theorem wp_dz_pow {f : ℂ → ℂ} {z : ℂ} (hf : DifferentiableAt ℝ f z) (n : ℕ) :
    dz (fun x => f x ^ n) z = n * f z ^ (n - 1) * dz f z := by
  unfold dz
  rw [fderiv_fun_pow n hf]
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul, nsmul_eq_mul]
  ring

/-- Power rule for the antiholomorphic Wirtinger derivative (TT:2781). -/
theorem wp_dzbar_pow {f : ℂ → ℂ} {z : ℂ} (hf : DifferentiableAt ℝ f z) (n : ℕ) :
    dzbar (fun x => f x ^ n) z = n * f z ^ (n - 1) * dzbar f z := by
  unfold dzbar
  rw [fderiv_fun_pow n hf]
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul, nsmul_eq_mul]
  ring

/-- Division by a constant commutes with the holomorphic derivative (TT:2781). -/
theorem wp_dz_div_const {f : ℂ → ℂ} {z : ℂ} (hf : DifferentiableAt ℝ f z) (c : ℂ) :
    dz (fun x => f x / c) z = dz f z / c := by
  have he : (fun x => f x / c) = (fun x => c⁻¹ * f x) := by funext x; ring
  rw [he, wp_dz_const_mul hf]
  ring

/-- Extract the quadratic boundary zero from the resolvent kernel (TT:2781). -/
theorem wp_boundary_kernel_eq {z w : ℂ} (hz : z ∈ unitDisc) (hw : w ∈ unitDisc)
    (hzw : z ≠ w) :
    (resolventKernel z w : ℂ) = wp_boundaryQ z ^ 2 / 4 * wp_boundaryW (z, w) := by
  have hρ : (rho z : ℂ) ≠ 0 := by
    rw [wp_rho_complex]
    exact div_ne_zero (by norm_num) (pow_ne_zero 2 (wp_disk_factor_ne_zero hz))
  change (resolventKernel z w : ℂ) = (1 - z * conj z) ^ 2 / 4 *
    (resolventBoundaryKernel w z : ℂ)
  rw [← wp_rho_inv_complex, resolventBoundaryKernel_eq_weighted hw hz hzw.symm,
    ← resolventKernel_symm z w, Complex.ofReal_mul]
  field_simp

/-- The first derivative has a linear boundary zero and a smooth residual factor (TT:2781). -/
theorem wp_boundary_kernel_dz {z w : ℂ} (hz : z ∈ unitDisc) (hw : w ∈ unitDisc)
    (hzw : z ≠ w) :
    dz (fun x => (resolventKernel x w : ℂ)) z = wp_boundaryQ z * wp_boundaryV (z, w) := by
  have he : (fun x => (resolventKernel x w : ℂ)) =ᶠ[𝓝 z]
      (fun x => wp_boundaryQ x ^ 2 / 4 * wp_boundaryW (x, w)) := by
    filter_upwards [isOpen_ball.mem_nhds hz, eventually_ne_nhds hzw] with x hx hxw
    exact wp_boundary_kernel_eq hx hw hxw
  have hq : DifferentiableAt ℝ wp_boundaryQ z :=
    wp_boundaryQ_contDiff.contDiffAt.differentiableAt (by simp)
  have hW := wp_boundaryW_contDiffAt (mem_ball_zero_iff.mp hz).le hw hzw
  have hdW : DifferentiableAt ℝ (fun x => wp_boundaryW (x, w)) z :=
    (hW.comp z (contDiffAt_id.prodMk contDiffAt_const)).differentiableAt (by simp)
  have hq2 : DifferentiableAt ℝ (fun x => wp_boundaryQ x ^ 2) z := by fun_prop
  have hq24 : DifferentiableAt ℝ (fun x => wp_boundaryQ x ^ 2 / 4) z := by fun_prop
  rw [wp_dz_congr_of_eventuallyEq he, dz_mul hq24 hdW,
    wp_dz_div_const hq2, wp_dz_pow hq]
  change _ = wp_boundaryQ z *
    (-conj z / 2 * wp_boundaryW (z, w) + wp_boundaryQ z / 4 *
      dz (fun x => wp_boundaryW (x, w)) z)
  rw [show dz wp_boundaryQ z = -conj z from wp_dz_disk_factor z]
  norm_num
  ring

/-- The weighted second derivative has a quadratic boundary zero (TT:2781). -/
theorem wp_boundary_kernel_weighted_dz {z w : ℂ} (hz : z ∈ unitDisc)
    (hw : w ∈ unitDisc) (hzw : z ≠ w) :
    dz (fun y => (rho y : ℂ)⁻¹ * dz (fun x => (resolventKernel x w : ℂ)) y) z =
      wp_boundaryQ z ^ 2 * wp_boundaryB (z, w) := by
  have he : (fun y => (rho y : ℂ)⁻¹ * dz (fun x => (resolventKernel x w : ℂ)) y) =ᶠ[𝓝 z]
      (fun y => wp_boundaryQ y ^ 3 / 4 * wp_boundaryV (y, w)) := by
    filter_upwards [isOpen_ball.mem_nhds hz, eventually_ne_nhds hzw] with y hy hyw
    rw [wp_boundary_kernel_dz hy hw hyw, wp_rho_inv_complex]
    unfold wp_boundaryQ
    ring
  have hq : DifferentiableAt ℝ wp_boundaryQ z :=
    wp_boundaryQ_contDiff.contDiffAt.differentiableAt (by simp)
  have hV := wp_boundaryV_contDiffAt
    (wp_boundaryW_contDiffAt (mem_ball_zero_iff.mp hz).le hw hzw)
  have hdV : DifferentiableAt ℝ (fun x => wp_boundaryV (x, w)) z :=
    (hV.comp z (contDiffAt_id.prodMk contDiffAt_const)).differentiableAt (by simp)
  have hq3 : DifferentiableAt ℝ (fun x => wp_boundaryQ x ^ 3) z := by fun_prop
  have hq34 : DifferentiableAt ℝ (fun x => wp_boundaryQ x ^ 3 / 4) z := by fun_prop
  rw [wp_dz_congr_of_eventuallyEq he, dz_mul hq34 hdV,
    wp_dz_div_const hq3, wp_dz_pow hq]
  change _ = wp_boundaryQ z ^ 2 *
    (-(3 : ℂ) * conj z / 4 * wp_boundaryV (z, w) + wp_boundaryQ z / 4 *
      dz (fun x => wp_boundaryV (x, w)) z)
  rw [show dz wp_boundaryQ z = -conj z from wp_dz_disk_factor z]
  norm_num
  ring

/-- The conjugate derivative of the weighted second derivative extends smoothly (TT:2781). -/
theorem wp_boundary_kernel_weighted_dzbar {z w : ℂ} (hz : z ∈ unitDisc)
    (hw : w ∈ unitDisc) (hzw : z ≠ w) :
    dzbar (dz fun y => (rho y : ℂ)⁻¹ * dz (fun x => (resolventKernel x w : ℂ)) y) z =
      -2 * z * wp_boundaryQ z * wp_boundaryB (z, w) +
        wp_boundaryQ z ^ 2 * wp_paramDzbar wp_boundaryB (z, w) := by
  have he : (dz fun y => (rho y : ℂ)⁻¹ * dz (fun x => (resolventKernel x w : ℂ)) y) =ᶠ[𝓝 z]
      (fun y => wp_boundaryQ y ^ 2 * wp_boundaryB (y, w)) := by
    filter_upwards [isOpen_ball.mem_nhds hz, eventually_ne_nhds hzw] with y hy hyw
    exact wp_boundary_kernel_weighted_dz hy hw hyw
  have hq : DifferentiableAt ℝ wp_boundaryQ z :=
    wp_boundaryQ_contDiff.contDiffAt.differentiableAt (by simp)
  have hB := wp_boundaryB_contDiffAt
    (wp_boundaryW_contDiffAt (mem_ball_zero_iff.mp hz).le hw hzw)
  have hdB : DifferentiableAt ℝ (fun x => wp_boundaryB (x, w)) z :=
    (hB.comp z (contDiffAt_id.prodMk contDiffAt_const)).differentiableAt (by simp)
  have hq2 : DifferentiableAt ℝ (fun x => wp_boundaryQ x ^ 2) z := by fun_prop
  rw [dzbar_congr_of_eventuallyEq he, dzbar_mul hq2 hdB, wp_dzbar_pow hq]
  rw [show dzbar wp_boundaryQ z = -z from wp_dzbar_disk_factor z]
  change _ = -2 * z * wp_boundaryQ z * wp_boundaryB (z, w) +
    wp_boundaryQ z ^ 2 * dzbar (fun x => wp_boundaryB (x, w)) z
  norm_num
  ring

/-- Uniform bounds for the smooth residual factors on an outer annulus times a compact source set (TT:2781). -/
theorem wp_boundary_compact_bounds {K : Set ℂ} (hK : IsCompact K) (hKD : K ⊆ unitDisc) :
    ∃ M r : ℝ, 0 ≤ M ∧ 0 < r ∧ r < 1 ∧
      ∀ z, r ≤ ‖z‖ → ‖z‖ ≤ 1 → ∀ w ∈ K, z ≠ w ∧
        ‖wp_boundaryW (z, w)‖ ≤ M ∧ ‖wp_boundaryV (z, w)‖ ≤ M ∧
        ‖wp_boundaryB (z, w)‖ ≤ M ∧ ‖wp_paramDzbar wp_boundaryB (z, w)‖ ≤ M := by
  rcases K.eq_empty_or_nonempty with hKe | hKn
  · refine ⟨0, 1 / 2, by norm_num, by norm_num, by norm_num, ?_⟩
    intro z _ _ w hw
    simpa [hKe] using hw
  obtain ⟨a, ha, hmax⟩ := hK.exists_isMaxOn hKn continuous_norm.continuousOn
  have ha1 : ‖a‖ < 1 := mem_ball_zero_iff.mp (hKD ha)
  let r : ℝ := (‖a‖ + 1) / 2
  have hr0 : 0 < r := by dsimp [r]; linarith [norm_nonneg a]
  have hr1 : r < 1 := by dsimp [r]; linarith
  have har : ‖a‖ < r := by dsimp [r]; linarith
  let S : Set (ℂ × ℂ) := (closedBall (0 : ℂ) 1 ∩ {z | r ≤ ‖z‖}) ×ˢ K
  have hS : IsCompact S :=
    ((isCompact_closedBall (0 : ℂ) 1).inter_right
      (isClosed_le continuous_const continuous_norm)).prod hK
  have hsep {p : ℂ × ℂ} (hp : p ∈ S) : p.1 ≠ p.2 := by
    have hm : ‖p.2‖ ≤ ‖a‖ := hmax hp.2
    have hr : r ≤ ‖p.1‖ := hp.1.2
    intro he
    rw [he] at hr
    linarith
  have hW {p : ℂ × ℂ} (hp : p ∈ S) : ContDiffAt ℝ (⊤ : ℕ∞) wp_boundaryW p :=
    wp_boundaryW_contDiffAt (mem_closedBall_zero_iff.mp hp.1.1) (hKD hp.2) (hsep hp)
  obtain ⟨cW, hcW⟩ := hS.exists_bound_of_continuousOn
    (fun p hp => (hW hp).continuousAt.continuousWithinAt)
  obtain ⟨cV, hcV⟩ := hS.exists_bound_of_continuousOn
    (fun p hp => (wp_boundaryV_contDiffAt (hW hp)).continuousAt.continuousWithinAt)
  obtain ⟨cB, hcB⟩ := hS.exists_bound_of_continuousOn
    (fun p hp => (wp_boundaryB_contDiffAt (hW hp)).continuousAt.continuousWithinAt)
  obtain ⟨cD, hcD⟩ := hS.exists_bound_of_continuousOn
    (fun p hp => (wp_paramDzbar_contDiffAt (wp_boundaryB_contDiffAt (hW hp))).continuousAt.continuousWithinAt)
  let M := |cW| + |cV| + |cB| + |cD|
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hMW : cW ≤ M := by dsimp [M]; linarith [le_abs_self cW, abs_nonneg cV, abs_nonneg cB, abs_nonneg cD]
  have hMV : cV ≤ M := by dsimp [M]; linarith [le_abs_self cV, abs_nonneg cW, abs_nonneg cB, abs_nonneg cD]
  have hMB : cB ≤ M := by dsimp [M]; linarith [le_abs_self cB, abs_nonneg cW, abs_nonneg cV, abs_nonneg cD]
  have hMD : cD ≤ M := by dsimp [M]; linarith [le_abs_self cD, abs_nonneg cW, abs_nonneg cV, abs_nonneg cB]
  refine ⟨M, r, hM, hr0, hr1, ?_⟩
  intro z hz hz1 w hw
  have hp : (z, w) ∈ S := ⟨⟨mem_closedBall_zero_iff.mpr hz1, hz⟩, hw⟩
  exact ⟨hsep hp, (hcW _ hp).trans hMW, (hcV _ hp).trans hMV,
    (hcB _ hp).trans hMB, (hcD _ hp).trans hMD⟩

/-- **(7.6)** (TT:2781). On `𝔻`, as `|z| → 1`, uniformly for `w` in compact subsets of `𝔻`:
- `G(z, w) = O(1 - |z|²)`;
- `(∂_z ρ⁻¹ ∂_z) G(z, w) = O(1 - |z|²)`;
- `∂_z G(z, w) = O(1)`;
- `∂_{z̄}(∂_z ρ⁻¹ ∂_z) G(z, w) = O(1)`.

Derivatives are in `z`. -/
theorem eq_7_6 {Kc : Set ℂ} (hK : IsCompact Kc) (hKD : Kc ⊆ unitDisc) :
    ∃ C r : ℝ, r < 1 ∧ ∀ z ∈ unitDisc, r < ‖z‖ → ∀ w ∈ Kc,
      |resolventKernel z w| ≤ C * (1 - ‖z‖ ^ 2) ∧
      ‖dz (fun y => (rho y : ℂ)⁻¹ * dz (fun x => (resolventKernel x w : ℂ)) y) z‖ ≤ C * (1 - ‖z‖ ^ 2) ∧
      ‖dz (fun x => (resolventKernel x w : ℂ)) z‖ ≤ C ∧
      ‖dzbar (dz fun y => (rho y : ℂ)⁻¹ * dz (fun x => (resolventKernel x w : ℂ)) y) z‖ ≤ C := by
  obtain ⟨M, r, hM, _, hr1, hb⟩ := wp_boundary_compact_bounds hK hKD
  refine ⟨4 * M, r, hr1, ?_⟩
  intro z hz hrz w hw
  have hz1 : ‖z‖ ≤ 1 := (mem_ball_zero_iff.mp hz).le
  obtain ⟨hzw, hW, hV, hB, hD⟩ := hb z hrz.le hz1 w hw
  have hq0 : 0 ≤ 1 - ‖z‖ ^ 2 := by nlinarith [norm_nonneg z]
  have hq1 : 1 - ‖z‖ ^ 2 ≤ 1 := by nlinarith [sq_nonneg ‖z‖]
  have hq2 : (1 - ‖z‖ ^ 2) ^ 2 ≤ 1 - ‖z‖ ^ 2 := by nlinarith
  have hq21 : (1 - ‖z‖ ^ 2) ^ 2 ≤ 1 := hq2.trans hq1
  have hqnorm : ‖wp_boundaryQ z‖ = 1 - ‖z‖ ^ 2 := by
    have he : wp_boundaryQ z = ((1 - ‖z‖ ^ 2 : ℝ) : ℂ) := by
      simp [wp_boundaryQ, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    rw [he, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hq0]
  have hMq : 0 ≤ M * (1 - ‖z‖ ^ 2) := mul_nonneg hM hq0
  have hMq2 := mul_le_mul_of_nonneg_left hq2 hM
  refine ⟨?_, ?_, ?_, ?_⟩
  · calc
      |resolventKernel z w| = ‖(resolventKernel z w : ℂ)‖ := by simp
      _ = (1 - ‖z‖ ^ 2) ^ 2 / 4 * ‖wp_boundaryW (z, w)‖ := by
        rw [wp_boundary_kernel_eq hz (hKD hw) hzw, norm_mul, norm_div, norm_pow, hqnorm]
        norm_num
      _ ≤ (1 - ‖z‖ ^ 2) ^ 2 / 4 * M :=
        mul_le_mul_of_nonneg_left hW (by positivity)
      _ ≤ 4 * M * (1 - ‖z‖ ^ 2) := by nlinarith
  · rw [wp_boundary_kernel_weighted_dz hz (hKD hw) hzw, norm_mul, norm_pow, hqnorm]
    calc
      _ ≤ (1 - ‖z‖ ^ 2) ^ 2 * M := mul_le_mul_of_nonneg_left hB (sq_nonneg _)
      _ ≤ 4 * M * (1 - ‖z‖ ^ 2) := by nlinarith
  · rw [wp_boundary_kernel_dz hz (hKD hw) hzw, norm_mul, hqnorm]
    calc
      _ ≤ (1 - ‖z‖ ^ 2) * M := mul_le_mul_of_nonneg_left hV hq0
      _ ≤ 1 * M := mul_le_mul_of_nonneg_right hq1 hM
      _ ≤ 4 * M := by linarith
  · rw [wp_boundary_kernel_weighted_dzbar hz (hKD hw) hzw]
    calc
      _ ≤ ‖-2 * z * wp_boundaryQ z * wp_boundaryB (z, w)‖ +
          ‖wp_boundaryQ z ^ 2 * wp_paramDzbar wp_boundaryB (z, w)‖ := norm_add_le _ _
      _ = 2 * ‖z‖ * (1 - ‖z‖ ^ 2) * ‖wp_boundaryB (z, w)‖ +
          (1 - ‖z‖ ^ 2) ^ 2 * ‖wp_paramDzbar wp_boundaryB (z, w)‖ := by
        simp [norm_mul, norm_pow, hqnorm]
      _ ≤ 2 * 1 * 1 * M + 1 * M := by
        gcongr
      _ ≤ 4 * M := by linarith


/-- Holomorphic derivative of the reciprocal density (TT:2787). -/
theorem wp_dz_rho_inv (z : ℂ) :
    dz (fun w => (rho w : ℂ)⁻¹) z = -(1 - z * conj z) * conj z / 2 := by
  have hq : DifferentiableAt ℝ (fun w : ℂ => 1 - w * conj w) z := by fun_prop
  have hqq : DifferentiableAt ℝ
      (fun w : ℂ => (1 - w * conj w) * (1 - w * conj w)) z := hq.mul hq
  have heq : (fun w => (rho w : ℂ)⁻¹) =
      (fun w => (1 / 4 : ℂ) * ((1 - w * conj w) * (1 - w * conj w))) := by
    funext w
    rw [wp_rho_inv_complex]
    ring
  rw [heq, wp_dz_const_mul hqq, dz_mul hq hq, wp_dz_disk_factor]
  ring

/-- Antiholomorphic derivative of the reciprocal density (TT:2787). -/
theorem wp_dzbar_rho_inv (z : ℂ) :
    dzbar (fun w => (rho w : ℂ)⁻¹) z = -(1 - z * conj z) * z / 2 := by
  have hq : DifferentiableAt ℝ (fun w : ℂ => 1 - w * conj w) z := by fun_prop
  have hqq : DifferentiableAt ℝ
      (fun w : ℂ => (1 - w * conj w) * (1 - w * conj w)) z := hq.mul hq
  have heq : (fun w => (rho w : ℂ)⁻¹) =
      (fun w => (1 / 4 : ℂ) * ((1 - w * conj w) * (1 - w * conj w))) := by
    funext w
    rw [wp_rho_inv_complex]
    ring
  rw [heq, wp_dzbar_const_mul hqq, dzbar_mul hq hq, wp_dzbar_disk_factor]
  ring

/-- The derivative of the coefficient z/(1-|z|²) appearing after the first
weighted derivative in the factorization (TT:2787). -/
theorem wp_dz_disk_ratio {z : ℂ} (hz : z ∈ unitDisc) :
    dz (fun w => w / (1 - w * conj w)) z = ((1 - z * conj z) ^ 2)⁻¹ := by
  have hq : DifferentiableAt ℝ (fun w : ℂ => 1 - w * conj w) z := by fun_prop
  have hid : DifferentiableAt ℝ (fun w : ℂ => w) z := differentiableAt_id
  have hi : DifferentiableAt ℝ (fun w : ℂ => (1 - w * conj w)⁻¹) z :=
    hq.inv (wp_disk_factor_ne_zero hz)
  simp_rw [div_eq_mul_inv]
  rw [dz_mul hid hi, wp_dz_inv hq (wp_disk_factor_ne_zero hz), wp_dz_disk_factor,
    show dz (fun w : ℂ => w) z = 1 from rhoVar_dz_id z]
  field_simp [wp_disk_factor_ne_zero hz]
  ring

/-- Mixed derivative of the reciprocal density, including the coefficient 1/2
which appears in the factorization (TT:2787). -/
theorem wp_dz_dzbar_rho_inv (z : ℂ) :
    dz (dzbar (fun w => (rho w : ℂ)⁻¹)) z = z * conj z - 1 / 2 := by
  have hq : DifferentiableAt ℝ (fun w : ℂ => 1 - w * conj w) z := by fun_prop
  have hid : DifferentiableAt ℝ (fun w : ℂ => w) z := differentiableAt_id
  have hqw : DifferentiableAt ℝ (fun w : ℂ => (1 - w * conj w) * w) z := hq.mul hid
  have heq : dzbar (fun w => (rho w : ℂ)⁻¹) =
      (fun w => (-1 / 2 : ℂ) * ((1 - w * conj w) * w)) := by
    funext w
    rw [wp_dzbar_rho_inv]
    ring
  rw [heq, wp_dz_const_mul hqw, dz_mul hq hid, wp_dz_disk_factor,
    show dz (fun w : ℂ => w) z = 1 from rhoVar_dz_id z]
  ring

/-- The first weighted antiholomorphic derivative in the factorization at
TT:2787, with the reciprocal-density derivative made explicit. -/
theorem wp_weighted_bar_core {f : ℂ → ℂ} {z : ℂ}
    (hf : DifferentiableAt ℝ (dzbar f) z) (hz : z ∈ unitDisc) :
    (rho z : ℂ) * dzbar (fun w => (rho w : ℂ)⁻¹ * dzbar f w) z =
      dzbar (dzbar f) z - 2 * (z / (1 - z * conj z)) * dzbar f z := by
  have ha : DifferentiableAt ℝ (fun w => (rho w : ℂ)⁻¹) z :=
    wp_rho_inv_contDiff.differentiable (by simp) z
  rw [dzbar_mul ha hf, wp_dzbar_rho_inv, wp_rho_inv_complex, wp_rho_complex]
  field_simp [wp_disk_factor_ne_zero hz]
  <;> ring

/-- The next weighted holomorphic derivative in the factorization at TT:2787.
This is the third-order intermediate expression before the final derivative. -/
theorem wp_weighted_dz_bar_core {f : ℂ → ℂ} (hf : ContDiffOn ℝ (⊤ : ℕ∞) f unitDisc)
    {z : ℂ} (hz : z ∈ unitDisc) :
    (rho z : ℂ)⁻¹ * dz (fun w => (rho w : ℂ) *
      dzbar (fun v => (rho v : ℂ)⁻¹ * dzbar f v) w) z =
        (rho z : ℂ)⁻¹ * dz (dzbar (dzbar f)) z - (1 / 2 : ℂ) * dzbar f z -
          ((1 - z * conj z) * z / 2) * dz (dzbar f) z := by
  have hB : ContDiffOn ℝ (⊤ : ℕ∞) (dzbar f) unitDisc := wp_contDiffOn_dzbar hf isOpen_ball (by simp)
  have hBB : ContDiffOn ℝ (⊤ : ℕ∞) (dzbar (dzbar f)) unitDisc :=
    wp_contDiffOn_dzbar hB isOpen_ball (by simp)
  have hBd : DifferentiableAt ℝ (dzbar f) z :=
    (hB.differentiableOn (by simp)).differentiableAt (isOpen_ball.mem_nhds hz)
  have hBBd : DifferentiableAt ℝ (dzbar (dzbar f)) z :=
    (hBB.differentiableOn (by simp)).differentiableAt (isOpen_ball.mem_nhds hz)
  have hq : DifferentiableAt ℝ (fun w : ℂ => 1 - w * conj w) z := by fun_prop
  have hR : DifferentiableAt ℝ (fun w : ℂ => w / (1 - w * conj w)) z := by
    have hid : DifferentiableAt ℝ (fun w : ℂ => w) z := differentiableAt_id
    have hi : DifferentiableAt ℝ (fun w : ℂ => (1 - w * conj w)⁻¹) z :=
      hq.inv (wp_disk_factor_ne_zero hz)
    have hp : DifferentiableAt ℝ (fun w : ℂ => w * (1 - w * conj w)⁻¹) z := hid.mul hi
    simpa only [div_eq_mul_inv] using hp
  have h2R : DifferentiableAt ℝ (fun w : ℂ => 2 * (w / (1 - w * conj w))) z := hR.const_mul 2
  have hprod : DifferentiableAt ℝ
      (fun w => 2 * (w / (1 - w * conj w)) * dzbar f w) z := h2R.mul hBd
  have heq : (fun w => (rho w : ℂ) * dzbar (fun v => (rho v : ℂ)⁻¹ * dzbar f v) w) =ᶠ[𝓝 z]
      (fun w => dzbar (dzbar f) w - 2 * (w / (1 - w * conj w)) * dzbar f w) := by
    filter_upwards [isOpen_ball.mem_nhds hz] with w hw
    exact wp_weighted_bar_core
      ((hB.differentiableOn (by simp)).differentiableAt (isOpen_ball.mem_nhds hw)) hw
  have hd : dz (fun w => (rho w : ℂ) * dzbar (fun v => (rho v : ℂ)⁻¹ * dzbar f v) w) z =
      dz (fun w => dzbar (dzbar f) w - 2 * (w / (1 - w * conj w)) * dzbar f w) z := by
    unfold dz
    rw [heq.fderiv_eq (𝕜 := ℝ)]
  rw [hd, dz_sub_pointwise hBBd hprod, dz_mul h2R hBd,
    wp_dz_const_mul hR, wp_dz_disk_ratio hz, wp_rho_inv_complex]
  field_simp [wp_disk_factor_ne_zero hz]
  <;> ring

/-- (TT:2787) `ρ⁻¹ ∂_z ρ⁻¹ ∂_z ρ ∂_{z̄} ρ⁻¹ ∂_{z̄} = Δ₀(Δ₀ + ½)` on smooth functions on `𝔻`. -/
theorem laplace_factorization {f : ℂ → ℂ} (hf : ContDiffOn ℝ (⊤ : ℕ∞) f unitDisc) {z : ℂ} (hz : z ∈ unitDisc) :
    (rho z : ℂ)⁻¹ * dz (fun y => (rho y : ℂ)⁻¹ * dz (fun x => (rho x : ℂ) *
        dzbar (fun s => (rho s : ℂ)⁻¹ * dzbar f s) x) y) z =
      laplace0 (fun y => laplace0 f y + (1 / 2) * f y) z := by
  let a : ℂ → ℂ := fun w => (rho w : ℂ)⁻¹
  let b := dzbar f
  let h := dz b
  let k := dzbar b
  let s : ℂ → ℂ := fun w => a w * h w
  let r : ℂ → ℂ := fun w => a w * dz k w - (1 / 2 : ℂ) * b w + dzbar a w * h w
  let l : ℂ → ℂ := fun w => a w * dz (fun y => (rho y : ℂ) *
    dzbar (fun x => a x * b x) y) w
  have ha : ContDiffOn ℝ (⊤ : ℕ∞) a unitDisc := wp_rho_inv_contDiff.contDiffOn.of_le le_top
  have hb : ContDiffOn ℝ (⊤ : ℕ∞) b unitDisc := wp_contDiffOn_dzbar hf isOpen_ball (by simp)
  have hh : ContDiffOn ℝ (⊤ : ℕ∞) h unitDisc := wp_contDiffOn_dz hb isOpen_ball (by simp)
  have hk : ContDiffOn ℝ (⊤ : ℕ∞) k unitDisc := wp_contDiffOn_dzbar hb isOpen_ball (by simp)
  have hdk : ContDiffOn ℝ (⊤ : ℕ∞) (dz k) unitDisc := wp_contDiffOn_dz hk isOpen_ball (by simp)
  have hBa : ContDiffOn ℝ (⊤ : ℕ∞) (dzbar a) unitDisc := wp_contDiffOn_dzbar ha isOpen_ball (by simp)
  have hs : ContDiffOn ℝ (⊤ : ℕ∞) s unitDisc := ha.mul hh
  have hc : ContDiffOn ℝ (⊤ : ℕ∞) (fun _ : ℂ => (1 / 2 : ℂ)) unitDisc := contDiffOn_const
  have hr : ContDiffOn ℝ (⊤ : ℕ∞) r unitDisc := ((ha.mul hdk).sub (hc.mul hb)).add (hBa.mul hh)
  have diff (g : ℂ → ℂ) (hg : ContDiffOn ℝ (⊤ : ℕ∞) g unitDisc) (w : ℂ) (hw : w ∈ unitDisc) :
      DifferentiableAt ℝ g w :=
    (hg.differentiableOn (by simp)).differentiableAt (isOpen_ball.mem_nhds hw)
  have hleft (w : ℂ) (hw : w ∈ unitDisc) : l w = r w := by
    calc
      l w = a w * dz k w - (1 / 2 : ℂ) * b w -
          ((1 - w * conj w) * w / 2) * h w := wp_weighted_dz_bar_core hf hw
      _ = r w := by
        have hba : dzbar a w = -(1 - w * conj w) * w / 2 := wp_dzbar_rho_inv w
        dsimp only [r]
        rw [hba]
        ring
  have hLap : laplace0 f = fun w => (-1 : ℂ) * s w := by
    funext w
    change -(a w * h w) = (-1 : ℂ) * (a w * h w)
    ring
  have hright (w : ℂ) (hw : w ∈ unitDisc) :
      dzbar (fun y => laplace0 f y + (1 / 2 : ℂ) * f y) w = -r w := by
    have hsd := diff s hs w hw
    have hfd := diff f hf w hw
    have hneg : DifferentiableAt ℝ (fun y => (-1 : ℂ) * s y) w := hsd.const_mul (-1)
    have hcf : DifferentiableAt ℝ (fun y => (1 / 2 : ℂ) * f y) w := hfd.const_mul (1 / 2)
    have hsb : dzbar s w = a w * dzbar h w + h w * dzbar a w :=
      dzbar_mul (diff a ha w hw) (diff h hh w hw)
    have hcomm : dzbar h w = dz k w :=
      (wp_wirtinger_comm ((hb.contDiffAt (isOpen_ball.mem_nhds hw)).of_le (by simp))).symm
    rw [hLap, wp_dzbar_add hneg hcf, wp_dzbar_const_mul hsd,
      wp_dzbar_const_mul hfd, hsb, hcomm]
    change (-1 : ℂ) * (a w * dz k w + h w * dzbar a w) + (1 / 2 : ℂ) * b w = -r w
    dsimp only [r]
    ring
  have hle : l =ᶠ[𝓝 z] r := by
    filter_upwards [isOpen_ball.mem_nhds hz] with w hw
    exact hleft w hw
  have hre : dzbar (fun y => laplace0 f y + (1 / 2 : ℂ) * f y) =ᶠ[𝓝 z]
      (fun y => -r y) := by
    filter_upwards [isOpen_ball.mem_nhds hz] with w hw
    exact hright w hw
  have hld : dz l z = dz r z := by
    unfold dz
    rw [hle.fderiv_eq (𝕜 := ℝ)]
  have hrd : dz (dzbar (fun y => laplace0 f y + (1 / 2 : ℂ) * f y)) z =
      dz (fun y => -r y) z := by
    unfold dz
    rw [hre.fderiv_eq (𝕜 := ℝ)]
  have hneg : dz (fun y => -r y) z = -dz r z := by
    simpa only [neg_one_mul] using wp_dz_const_mul (diff r hr z hz) (-1 : ℂ)
  change a z * dz l z = -(a z * dz (dzbar (fun y => laplace0 f y + (1 / 2 : ℂ) * f y)) z)
  rw [hld, hrd, hneg]
  ring

-- prop_7_2 moved unchanged to Ch1/S7EnergyCompleted (2026-10-28).

-- cor_7_3 moved unchanged to Ch1/S7PolarizationCompleted (2026-10-28).

-- `eq_7_7` moved to `Ch1/WPChangeOfVariables.lean` (2026-10-26).

-- `thm_7_4` moved to `TakhtajanTeo.Ch1.S7Thm74` (2026-10-29, Program G).

/-- The orthonormal basis of `H^{-1,1}(𝔻*)` (TT:2847):
`μ_n(z) = -√((n³ - n)/(8π)) (1 - |z|²)² z̄^{-n-2}`, `n = 2, 3, …`. -/
def basisMu (n : ℕ) (z : ℂ) : ℂ :=
  -(Real.sqrt (((n : ℝ) ^ 3 - n) / (8 * π)) : ℂ) * ((1 - ‖z‖ ^ 2) ^ 2 : ℝ) * conj z ^ (-(n : ℤ) - 2)

/-- Inversion turns the exterior monomial of the basis in TT:2844 into a disk monomial. -/
theorem basisMu_inverted_monomial (k : ℕ) {z : ℂ} (hz : z ≠ 0) :
    (z⁻¹) ^ (-(k : ℤ) - 4) / z ^ 4 = z ^ k := by
  have he : -(k : ℤ) - 4 = -((k + 4 : ℕ) : ℤ) := by push_cast; ring
  rw [he, zpow_neg, zpow_natCast, inv_pow, inv_inv, pow_add]
  exact mul_div_cancel_right₀ _ (pow_ne_zero 4 hz)

/-- Exact exterior quadratic-monomial norm, used to normalize the basis in TT:2844–2850. -/
theorem basisMu_exterior_monomial_integral (k : ℕ) :
    (∫ z in unitDiscExterior, ‖z ^ (-(k : ℤ) - 4)‖ ^ 2 * (rho z)⁻¹) =
      π / (2 * (((k : ℝ) + 1) * ((k : ℝ) + 2) * ((k : ℝ) + 3))) := by
  rw [← inverted_quadratic_weighted_integral]
  calc
    _ = ∫ z in unitDisc \ {0}, ‖z ^ k‖ ^ 2 * (rho z)⁻¹ := by
      apply setIntegral_congr_fun (measurableSet_ball.diff (measurableSet_singleton 0))
      intro z hz
      dsimp only
      rw [basisMu_inverted_monomial k hz.2]
    _ = ∫ z in unitDisc, ‖z ^ k‖ ^ 2 * (rho z)⁻¹ := by
      apply setIntegral_congr_set
      exact sdiff_null_ae_eq_self (measure_singleton 0)
    _ = _ := bergman_monomial_area k

/-- Absolute convergence for the exterior quadratic monomials of TT:2844. -/
theorem basisMu_exterior_monomial_integrable (k : ℕ) :
    IntegrableOn (fun z : ℂ => ‖z ^ (-(k : ℤ) - 4)‖ ^ 2 * (rho z)⁻¹) unitDiscExterior := by
  have hc : Continuous (fun z : ℂ => ‖z ^ k‖ ^ 2 * (rho z)⁻¹) := by
    simp only [rho, inv_div]
    fun_prop
  have hi : IntegrableOn (fun z : ℂ => ‖z ^ k‖ ^ 2 * (rho z)⁻¹) unitDisc :=
    (hc.continuousOn.integrableOn_compact (isCompact_closedBall (0 : ℂ) 1)).mono_set
      ball_subset_closedBall
  have hopen : IsOpen (unitDisc \ {(0 : ℂ)}) := isOpen_ball.sdiff isClosed_singleton
  have hinv := inversion_puncturedDisk_conformal
  have hchange := ahP_integrableOn_image hopen hinv.1 hinv.2.1
    (fun z : ℂ => ‖z ^ (-(k : ℤ) - 4)‖ ^ 2 * (rho z)⁻¹)
  rw [hinv.2.2] at hchange
  apply hchange.mpr
  apply (hi.mono_set sdiff_subset).congr
  filter_upwards [ae_restrict_mem hopen.measurableSet] with z hz
  have he := inverted_quadratic_weight (φ := fun w : ℂ => w ^ (-(k : ℤ) - 4)) hz.2
  rw [basisMu_inverted_monomial k hz.2] at he
  simpa only [smul_eq_mul, mul_comm] using he

/-- The exterior monomials underlying the basis are in `A₂`, TT:2844–2850. -/
theorem basisMu_exterior_monomial_A2 (k : ℕ) :
    (fun z : ℂ => z ^ (-(k : ℤ) - 4)) ∈ A2fun unitDiscExterior := by
  refine ⟨?_, normA2_lt_top_of_integrable_weighted_sq (basisMu_exterior_monomial_integrable k)⟩
  intro z hz
  have hz0 : z ≠ 0 := by
    intro h
    have hh : (1 : ℝ) < 0 := by simpa only [unitDiscExterior, mem_setOf_eq, h, norm_zero] using hz
    linarith
  exact (differentiableAt_id.zpow (Or.inl hz0)).differentiableWithinAt

/-- The explicit holomorphic representative of the basis in TT:2844. -/
theorem basisMu_harmonic_representation (k : ℕ) (z : ℂ) :
    basisMu (k + 2) z = (rho z : ℂ)⁻¹ *
      conj (-4 * (Real.sqrt (((k + 2 : ℕ) : ℝ) ^ 3 - ((k + 2 : ℕ) : ℝ)) /
        Real.sqrt (8 * π) : ℂ) * z ^ (-(k : ℤ) - 4)) := by
  have he : -((k + 2 : ℕ) : ℤ) - 2 = -(k : ℤ) - 4 := by push_cast; ring
  have hp : 0 ≤ (((k + 2 : ℕ) : ℝ) ^ 3 - ((k + 2 : ℕ) : ℝ)) := by
    have hk : 0 ≤ (k : ℝ) := Nat.cast_nonneg k
    norm_num
    nlinarith [sq_nonneg (k : ℝ), mul_nonneg hk (sq_nonneg (k : ℝ))]
  simp only [basisMu, he, Real.sqrt_div hp, map_mul, map_div₀, map_neg,
    map_ofNat, conj_ofReal, map_zpow₀, rho, Complex.ofReal_div, inv_div,
    Complex.ofReal_ofNat, Complex.ofReal_pow]
  ring

/-- Each explicit basis vector lies in the harmonic Hilbert tangent space, TT:2844–2850. -/
theorem basisMu_mem_harmonicL2 (k : ℕ) : basisMu (k + 2) ∈ harmonicL2 unitDiscExterior := by
  let c : ℂ := -4 * (Real.sqrt (((k + 2 : ℕ) : ℝ) ^ 3 - ((k + 2 : ℕ) : ℝ)) /
    Real.sqrt (8 * π) : ℂ)
  let φ : ℂ → ℂ := fun z => c * z ^ (-(k : ℤ) - 4)
  have hm := basisMu_exterior_monomial_A2 k
  have hφ : DifferentiableOn ℂ φ unitDiscExterior := (differentiableOn_const c).mul hm.1
  have hf : normA2 unitDiscExterior φ < ∞ := by
    rw [show φ = (fun z => c * z ^ (-(k : ℤ) - 4)) from rfl, normA2_const_mul]
    exact ENNReal.mul_lt_top (by simp) hm.2
  have hr : ∀ z ∈ unitDiscExterior, basisMu (k + 2) z = (rho z : ℂ)⁻¹ * conj (φ z) := by
    intro z _
    exact basisMu_harmonic_representation k z
  refine ⟨φ, hφ, hr, ?_⟩
  rw [← normA2_eq_normL2_of_harmonic wp_exterior_isOpen.measurableSet
    (fun z hz => ne_of_gt hz) hr]
  exact hf

/-- The weighted squared norm of each explicit basis vector is one, TT:2844–2850. -/
theorem basisMu_energy_integral (k : ℕ) :
    (∫ z in unitDiscExterior, ‖basisMu (k + 2) z‖ ^ 2 * rho z) = 1 := by
  let C : ℝ := (((k + 2 : ℕ) : ℝ) ^ 3 - ((k + 2 : ℕ) : ℝ)) / (8 * π)
  have hC : 0 ≤ C := by
    apply div_nonneg _ (by positivity)
    have hk : 0 ≤ (k : ℝ) := Nat.cast_nonneg k
    norm_num
    nlinarith [sq_nonneg (k : ℝ), mul_nonneg hk (sq_nonneg (k : ℝ))]
  have hp (z : ℂ) (hz : z ∈ unitDiscExterior) :
      ‖basisMu (k + 2) z‖ ^ 2 * rho z =
        (16 * C) * (‖z ^ (-(k : ℤ) - 4)‖ ^ 2 * (rho z)⁻¹) := by
    have he : -((k + 2 : ℕ) : ℤ) - 2 = -(k : ℤ) - 4 := by push_cast; ring
    have hd : 1 - ‖z‖ ^ 2 ≠ 0 := by
      change 1 < ‖z‖ at hz
      nlinarith [norm_nonneg z]
    change ‖-(Real.sqrt C : ℂ) * ((1 - ‖z‖ ^ 2) ^ 2 : ℝ) *
      conj z ^ (-((k + 2 : ℕ) : ℤ) - 2)‖ ^ 2 * rho z = _
    simp only [he, norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg C), abs_of_nonneg (sq_nonneg (1 - ‖z‖ ^ 2)), mul_pow,
      Real.sq_sqrt hC, norm_zpow, norm_conj, rho, inv_div]
    field_simp
    <;> ring
  calc
    _ = (16 * C) * ∫ z in unitDiscExterior, ‖z ^ (-(k : ℤ) - 4)‖ ^ 2 * (rho z)⁻¹ := by
      rw [← integral_const_mul]
      exact setIntegral_congr_fun wp_exterior_isOpen.measurableSet hp
    _ = 1 := by
      rw [basisMu_exterior_monomial_integral]
      dsimp [C]
      push_cast
      field_simp
      <;> ring

/-- Diagonal orthonormality of the explicit WP basis, TT:2844–2850. -/
theorem basisMu_wpInner_self (k : ℕ) : wpInner (basisMu (k + 2)) (basisMu (k + 2)) = 1 := by
  apply Complex.ext
  · simpa only [Complex.one_re, wpInner_self_re (basisMu_mem_harmonicL2 k)] using
      basisMu_energy_integral k
  · have hi := congrArg Complex.im (wpInner_conj_symm (basisMu (k + 2)) (basisMu (k + 2)))
    simp only [Complex.conj_im] at hi
    simp only [Complex.one_im]
    linarith


-- `cor_7_5` moved to `TakhtajanTeo.Ch1.S7Thm74` (2026-10-29, Program G).

/-! ## §7.2 The second variation of the Weil–Petersson metric -/

/-- The Riemann tensor at the origin (TT:2873, TT:3009), in polarized form:
`R_{k l̄ m n̄} = -∂²/∂ε₁∂ε̄₂|_{ε₁=ε₂=0} g_{k l̄}(ε₁ m + ε₂ n)` for directions `k, l, m, n ∈ H^{-1,1}(𝔻*)`. -/
def riemannR (k l m n : ℂ → ℂ) : ℂ :=
  -dz (fun e₁ => dzbar (fun e₂ => gWP k l (e₁ • toLinf m + e₂ • toLinf n)) 0) 0

-- `thm_7_7` moved to `TakhtajanTeo.Ch1.S7SecondVariation` (2026-10-29, Program G).

-- `lemma_7_8` moved to `TakhtajanTeo.Ch1.S7Lemma78` (2026-10-29, Program G).

-- `cor_7_9` moved to `TakhtajanTeo.Ch1.S7Cor79` (2026-10-29, Program G).

/-! ## §7.3 Ricci and sectional curvatures -/

/-- The Ricci tensor at the origin (TT:3023): `𝓡_{μ ν̄} = Σ_{n ≥ 2} R_{μ n̄ n ν̄}` for the orthonormal basis `μ_n`. -/
def ricciT (μ ν : ℂ → ℂ) : ℂ := ∑' n : ℕ, riemannR μ (basisMu (n + 2)) (basisMu (n + 2)) ν

/-- The kernel `B(z, v) = ∬_𝔻 G(z, w) (1 - |w|²)²/((1 - w v̄)⁴(1 - z w̄)⁴) d²w` on `𝔻` (TT:3053; see the module
docstring). -/
def bKernel (z v : ℂ) : ℂ :=
  ∫ w in unitDisc, (resolventKernel z w : ℂ) * ((1 - ‖w‖ ^ 2) ^ 2 : ℝ) / ((1 - w * conj v) ^ 4 * (1 - z * conj w) ^ 4)

/-- Continuity of the logarithmic moment used in the center computation of (7.8), TT:3072. -/
theorem bKernel_sq_log_continuous : Continuous (fun t : ℝ => t ^ 2 * Real.log t) := by
  convert continuous_id.mul Real.continuous_mul_log using 1
  funext t
  dsimp
  ring

/-- The logarithmic second moment in the center computation of (7.8), TT:3072. -/
theorem bKernel_log_square_moment :
    (∫ t in (0 : ℝ)..1, t ^ 2 * Real.log t) = -1 / 9 := by
  have hc : Continuous (fun t : ℝ => t ^ 3 * Real.log t / 3 - t ^ 3 / 9) := by
    convert ((continuous_id.pow 2).mul Real.continuous_mul_log).div_const 3 |>.sub
      ((continuous_id.pow 3).div_const 9) using 1
    funext t
    dsimp
    ring
  have hd (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) :
      HasDerivAt (fun t : ℝ => t ^ 3 * Real.log t / 3 - t ^ 3 / 9)
        (t ^ 2 * Real.log t) t := by
    convert (((hasDerivAt_pow 3 t).mul (Real.hasDerivAt_log ht.1.ne')).div_const 3).sub
      ((hasDerivAt_pow 3 t).div_const 9) using 1 <;> dsimp
    field_simp
    <;> ring
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
    (by norm_num : (0 : ℝ) ≤ 1) hc.continuousOn hd
    (bKernel_sq_log_continuous.intervalIntegrable 0 1)
  norm_num at hi ⊢
  exact hi

/-- The polynomial second moment in the center computation of (7.8), TT:3072. -/
theorem bKernel_polynomial_moment : (∫ t in (0 : ℝ)..1, (1 - t) ^ 2) = 1 / 3 := by
  have hd (t : ℝ) : HasDerivAt (fun t : ℝ => t - t ^ 2 + t ^ 3 / 3) ((1 - t) ^ 2) t := by
    convert ((hasDerivAt_id t).sub (hasDerivAt_pow 2 t)).add
      ((hasDerivAt_pow 3 t).div_const 3) using 1
    · ext x
      simp
    · norm_num
      ring
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
    (by norm_num : (0 : ℝ) ≤ 1) (by fun_prop) (fun t _ => hd t)
    (show IntervalIntegrable (fun t : ℝ => (1 - t) ^ 2) volume 0 1 from
      (by fun_prop : Continuous (fun t : ℝ => (1 - t) ^ 2)).intervalIntegrable 0 1)
  norm_num at hi ⊢
  exact hi

/-- The weighted radial profile has integral `1/9`, as required for (7.8), TT:3072. -/
theorem bKernel_center_profile_integral :
    (∫ t in (0 : ℝ)..1, -(1 - t ^ 2) / 2 * Real.log t - (1 - t) ^ 2) = 1 / 9 := by
  have heq (t : ℝ) : -(1 - t ^ 2) / 2 * Real.log t - (1 - t) ^ 2 =
      (-1 / 2) * Real.log t + (1 / 2) * (t ^ 2 * Real.log t) - (1 - t) ^ 2 := by ring
  simp_rw [heq]
  rw [intervalIntegral.integral_sub
    ((intervalIntegral.intervalIntegrable_log'.const_mul (-1 / 2)).add
      ((bKernel_sq_log_continuous.intervalIntegrable 0 1).const_mul (1 / 2)))
    ((by fun_prop : Continuous (fun t : ℝ => (1 - t) ^ 2)).intervalIntegrable 0 1),
    intervalIntegral.integral_add (intervalIntegral.intervalIntegrable_log'.const_mul (-1 / 2))
      ((bKernel_sq_log_continuous.intervalIntegrable 0 1).const_mul (1 / 2)),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    integral_log, bKernel_log_square_moment, bKernel_polynomial_moment]
  norm_num

/-- Squared-radius substitution on the open unit interval, used in (7.8), TT:3072. -/
theorem bKernel_radius_square_integral (f : ℝ → ℝ) :
    (∫ r in Ioo (0 : ℝ) 1, 2 * r * f (r ^ 2)) = ∫ t in (0 : ℝ)..1, f t := by
  have h := intervalIntegral.integral_comp_mul_deriv_of_deriv_nonneg
    (a := (0 : ℝ)) (b := 1) (f := fun r : ℝ => r ^ 2) (f' := fun r => 2 * r) (g := f)
    (by fun_prop)
    (fun r _ => by simpa using hasDerivAt_pow 2 r)
    (by
      intro r hr
      have hr0 : 0 ≤ r := le_trans (by norm_num) hr.1.le
      positivity)
  rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
    integral_Ioc_eq_integral_Ioo] at h
  simpa only [Function.comp_def, zero_pow (by decide : 2 ≠ 0), one_pow, mul_comm] using h

/-- The scalar profile after squared-radius substitution for `B(0,0)`, TT:3072. -/
theorem bKernel_center_radial_jacobian {r : ℝ} (hr : r ∈ Ioo (0 : ℝ) 1) :
    2 * π * r * (resolventKernel 0 (r : ℂ) * (1 - r ^ 2) ^ 2) =
      2 * r * (-(1 - (r ^ 2) ^ 2) / 2 * Real.log (r ^ 2) - (1 - r ^ 2) ^ 2) := by
  have hr0 : r ≠ 0 := hr.1.ne'
  have hrd : 1 - r ^ 2 ≠ 0 := by nlinarith [hr.1, hr.2]
  have hlog : (r ^ 2 / (1 - r ^ 2) + 1) / (r ^ 2 / (1 - r ^ 2)) = (r ^ 2)⁻¹ := by
    field_simp
    <;> ring
  simp only [resolventKernel, pointPair, zero_sub, norm_neg, norm_zero,
    zero_pow (by decide : 2 ≠ 0), sub_zero, one_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos hr.1]
  rw [hlog, Real.log_inv]
  field_simp
  <;> ring

/-- The polar radius integral for `B(0,0)` equals `1/9`, TT:3072. -/
theorem bKernel_center_radius_integral :
    (∫ r in Ioo (0 : ℝ) 1, 2 * π * r *
      (resolventKernel 0 (r : ℂ) * (1 - r ^ 2) ^ 2)) = 1 / 9 := by
  calc
    _ = ∫ r in Ioo (0 : ℝ) 1, 2 * r *
        (-(1 - (r ^ 2) ^ 2) / 2 * Real.log (r ^ 2) - (1 - r ^ 2) ^ 2) :=
      setIntegral_congr_fun measurableSet_Ioo (fun r hr => bKernel_center_radial_jacobian hr)
    _ = _ := (bKernel_radius_square_integral _).trans bKernel_center_profile_integral

/-- The real disk integral at the center in (7.8), TT:3072. -/
theorem bKernel_center_real_integral :
    (∫ w in unitDisc, resolventKernel 0 w * (1 - ‖w‖ ^ 2) ^ 2) = 1 / 9 := by
  calc
    _ = ∫ w in unitDisc, resolventKernel 0 (‖w‖ : ℂ) * (1 - ‖w‖ ^ 2) ^ 2 := by
      apply integral_congr_ae
      filter_upwards with w
      simp [resolventKernel, pointPair, Complex.norm_real, abs_of_nonneg (norm_nonneg w)]
    _ = 2 * π * ∫ r in Ioo (0 : ℝ) 1,
        r * (resolventKernel 0 (r : ℂ) * (1 - r ^ 2) ^ 2) :=
      integral_unitDisc_radial (fun r : ℝ => resolventKernel 0 (r : ℂ) * (1 - r ^ 2) ^ 2)
    _ = ∫ r in Ioo (0 : ℝ) 1,
        2 * π * r * (resolventKernel 0 (r : ℂ) * (1 - r ^ 2) ^ 2) := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with r
      ring
    _ = _ := bKernel_center_radius_integral

/-- The center value `B(0,0) = 1/9` in (7.8), TT:3072. -/
theorem bKernel_center_value : bKernel 0 0 = 1 / 9 := by
  unfold bKernel
  simp only [map_zero, mul_zero, zero_mul, sub_zero, one_pow, mul_one, div_one,
    ← Complex.ofReal_mul, integral_complex_ofReal, bKernel_center_real_integral]
  norm_num

/-- Absolute convergence of the weighted kernel entering (7.8), TT:3053–3072. -/
theorem bKernel_weight_integrable {z : ℂ} (hz : z ∈ unitDisc) :
    IntegrableOn (fun w => resolventKernel z w * (1 - ‖w‖ ^ 2) ^ 2) unitDisc := by
  have hc : Continuous (fun w : ℂ => (1 - ‖w‖ ^ 2) ^ 4 / 4) := by fun_prop
  have hb : ∀ᵐ w ∂(volume.restrict unitDisc), ‖(1 - ‖w‖ ^ 2) ^ 4 / 4‖ ≤ 1 := by
    filter_upwards [ae_restrict_mem measurableSet_ball] with w hw
    have hw1 : ‖w‖ < 1 := mem_ball_zero_iff.mp hw
    have hq0 : 0 ≤ 1 - ‖w‖ ^ 2 := by nlinarith [norm_nonneg w]
    have hq1 : 1 - ‖w‖ ^ 2 ≤ 1 := by nlinarith [sq_nonneg ‖w‖]
    have hpow : (1 - ‖w‖ ^ 2) ^ 4 ≤ 1 := pow_le_one₀ hq0 hq1
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    linarith
  have hi := (resolvent_mass_integrable (Or.inl rfl) hz).mul_bdd
    hc.aestronglyMeasurable hb
  apply hi.congr
  filter_upwards [ae_restrict_mem measurableSet_ball] with w hw
  have hw1 : ‖w‖ < 1 := mem_ball_zero_iff.mp hw
  have hd : 1 - ‖w‖ ^ 2 ≠ 0 := by nlinarith [norm_nonneg w]
  unfold rho
  field_simp
  <;> ring



/-- Uniform control of the fourth-power denominator in (7.8), TT:3053–3072. -/
theorem bKernel_inverse_denominator_bound {w v : ℂ} (hw : ‖w‖ ≤ 1) (hv : ‖v‖ < 1) :
    ‖1 / (1 - w * conj v) ^ 4‖ ≤ 1 / (1 - ‖v‖) ^ 4 := by
  rw [norm_div, norm_one, norm_pow]
  exact one_div_le_one_div_of_le (pow_pos (sub_pos.mpr hv) 4)
    (pow_le_pow_left₀ (sub_pos.mpr hv).le (bKernel_denominator_lower_bound hw) 4)

/-- The holomorphic angular factor has mean one on every subdisk, TT:3072. -/
theorem bKernel_angular_average {v : ℂ} (hv : ‖v‖ < 1) {r : ℝ} (hr : |r| ≤ 1) :
    Real.circleAverage (fun w : ℂ => 1 / (1 - w * conj v) ^ 4) 0 r = 1 := by
  have hn (w : ℂ) (hw : w ∈ closedBall (0 : ℂ) |r|) : (1 - w * conj v) ^ 4 ≠ 0 :=
    pow_ne_zero 4 (bKernel_denominator_ne_zero ((mem_closedBall_zero_iff.mp hw).trans hr) hv)
  have hc : ContinuousOn (fun w : ℂ => 1 / (1 - w * conj v) ^ 4)
      (closedBall (0 : ℂ) |r|) :=
    continuousOn_const.div ((continuousOn_const.sub
      (continuousOn_id.mul continuousOn_const)).pow 4) hn
  have hd : ∀ w ∈ ball (0 : ℂ) |r| \ (∅ : Set ℂ),
      DifferentiableAt ℂ (fun w : ℂ => 1 / (1 - w * conj v) ^ 4) w := by
    intro w hw
    exact (differentiableAt_const (1 : ℂ)).div
      (((differentiableAt_const (1 : ℂ)).sub
        (differentiableAt_id.mul (differentiableAt_const (conj v)))).pow 4)
      (hn w (ball_subset_closedBall hw.1))
  simpa using circleAverage_of_differentiable_on_off_countable countable_empty hc hd




/-- Absolute convergence of the radius weight in the computation of (7.8), TT:3072. -/
theorem bKernel_radius_integrable :
    IntegrableOn (fun r : ℝ => r * (resolventKernel 0 (r : ℂ) * (1 - r ^ 2) ^ 2)) (Ioo 0 1) := by
  have hi : IntegrableOn (fun w : ℂ =>
      resolventKernel 0 (‖w‖ : ℂ) * (1 - ‖w‖ ^ 2) ^ 2) unitDisc := by
    simpa [resolventKernel, pointPair, Complex.norm_real] using
      bKernel_weight_integrable (show (0 : ℂ) ∈ unitDisc by simp [unitDisc])
  have h := (integrableOn_fun_norm_addHaar (volume : Measure ℂ)
    (f := fun r : ℝ => resolventKernel 0 (r : ℂ) * (1 - r ^ 2) ^ 2)).mp hi
  simpa only [Complex.finrank_real_complex, Nat.reduceSub, pow_one, smul_eq_mul] using h

/-- Joint absolute convergence justifies angular integration for `B(0,v)`, TT:3072. -/
theorem bKernel_center_polar_integrable {v : ℂ} (hv : ‖v‖ < 1) :
    IntegrableOn (fun p : ℝ × ℝ => p.1 •
      ((resolventKernel 0 (Complex.polarCoord.symm p) : ℂ) *
        ((1 - ‖Complex.polarCoord.symm p‖ ^ 2) ^ 2 : ℝ) /
        (1 - Complex.polarCoord.symm p * conj v) ^ 4))
      (Ioo (0 : ℝ) 1 ×ˢ Ioo (-π) π) := by
  let S : Set (ℝ × ℝ) := Ioo (0 : ℝ) 1 ×ˢ Ioo (-π) π
  let g : ℝ × ℝ → ℂ := fun p => 1 / (1 - Complex.polarCoord.symm p * conj v) ^ 4
  have hp (p : ℝ × ℝ) (hp : p ∈ S) : ‖Complex.polarCoord.symm p‖ ≤ 1 := by
    rw [norm_polarCoord_symm, abs_of_pos hp.1.1]
    exact hp.1.2.le
  have hpc : Continuous (fun p : ℝ × ℝ => Complex.polarCoord.symm p) := by
    simp only [Complex.polarCoord_symm_apply]
    fun_prop
  have hc : ContinuousOn g S :=
    continuousOn_const.div ((continuousOn_const.sub
      (hpc.continuousOn.mul continuousOn_const)).pow 4)
      (fun p hps => pow_ne_zero 4 (bKernel_denominator_ne_zero (hp p hps) hv))
  have hb : ∀ᵐ p ∂(volume.restrict S), ‖g p‖ ≤ 1 / (1 - ‖v‖) ^ 4 := by
    filter_upwards [ae_restrict_mem (measurableSet_Ioo.prod measurableSet_Ioo)] with p hps
    exact bKernel_inverse_denominator_bound (hp p hps) hv
  have hi : IntegrableOn (fun p : ℝ × ℝ =>
      ((p.1 * (resolventKernel 0 (p.1 : ℂ) * (1 - p.1 ^ 2) ^ 2) : ℝ) : ℂ)) S := by
    have h := (bKernel_radius_integrable.ofReal (𝕜 := ℂ)).comp_fst
      (volume.restrict (Ioo (-π) π))
    rwa [Measure.prod_restrict, ← Measure.volume_eq_prod] at h
  apply (hi.mul_bdd (hc.aestronglyMeasurable
    (measurableSet_Ioo.prod measurableSet_Ioo)) hb).congr
  filter_upwards [ae_restrict_mem (measurableSet_Ioo.prod measurableSet_Ioo)] with p hps
  have hG : resolventKernel 0 (Complex.polarCoord.symm p) = resolventKernel 0 (p.1 : ℂ) := by
    simp [resolventKernel, pointPair, norm_polarCoord_symm, Complex.norm_real]
  simp only [g, hG, norm_polarCoord_symm, abs_of_pos hps.1.1, Complex.ofReal_mul,
    Complex.real_smul, div_eq_mul_inv, one_mul]
  ring

/-- The angular average of the full center integrand in (7.8), TT:3072. -/
theorem bKernel_center_circle_average {v : ℂ} (hv : ‖v‖ < 1) {r : ℝ} (hr : r ∈ Ioo (0 : ℝ) 1) :
    Real.circleAverage (fun w : ℂ => (resolventKernel 0 w : ℂ) *
      ((1 - ‖w‖ ^ 2) ^ 2 : ℝ) / (1 - w * conj v) ^ 4) 0 r =
      ((resolventKernel 0 (r : ℂ) * (1 - r ^ 2) ^ 2 : ℝ) : ℂ) := by
  calc
    _ = Real.circleAverage (fun w : ℂ =>
        (((resolventKernel 0 (r : ℂ) * (1 - r ^ 2) ^ 2 : ℝ) : ℂ) •
          (1 / (1 - w * conj v) ^ 4))) 0 r := by
      apply Real.circleAverage_congr_sphere
      intro w hw
      have hn : ‖w‖ = r := by simpa only [mem_sphere, dist_zero_right, abs_of_pos hr.1] using hw
      have hG : resolventKernel 0 w = resolventKernel 0 (r : ℂ) := by
        simp [resolventKernel, pointPair, hn, Complex.norm_real, abs_of_pos hr.1]
      simp only [hG, hn, smul_eq_mul, Complex.ofReal_mul, div_eq_mul_inv, one_mul]
    _ = _ := by
      rw [Real.circleAverage_fun_smul, bKernel_angular_average hv
        (by simpa only [abs_of_pos hr.1] using hr.2.le), smul_eq_mul, mul_one]

set_option maxHeartbeats 600000 in
/-- The full center normalization `B(0,v) = 1/9` in (7.8), TT:3072. -/
theorem bKernel_center_parameter {v : ℂ} (hv : v ∈ unitDisc) : bKernel 0 v = 1 / 9 := by
  have hv1 : ‖v‖ < 1 := mem_ball_zero_iff.mp hv
  unfold bKernel
  simp only [zero_mul, sub_zero, one_pow, mul_one]
  rw [bKernel_polar_integral (fun w : ℂ => (resolventKernel 0 w : ℂ) *
    ((1 - ‖w‖ ^ 2) ^ 2 : ℝ) / (1 - w * conj v) ^ 4) (bKernel_center_polar_integrable hv1)]
  calc
    _ = ∫ r in Ioo (0 : ℝ) 1,
        Complex.ofReal (2 * π * r * (resolventKernel 0 (r : ℂ) * (1 - r ^ 2) ^ 2)) := by
      apply setIntegral_congr_fun measurableSet_Ioo
      intro r hr
      dsimp only
      rw [bKernel_center_circle_average hv1 hr]
      simp only [Complex.real_smul, Complex.ofReal_mul]
      ring
    _ = Complex.ofReal (∫ r in Ioo (0 : ℝ) 1,
        2 * π * r * (resolventKernel 0 (r : ℂ) * (1 - r ^ 2) ^ 2)) := integral_complex_ofReal
    _ = _ := by rw [bKernel_center_radius_integral]; norm_num


/-- The real Jacobian of a disk Blaschke map in squared-norm form, TT:3058. -/
theorem bKernel_blaschke_jacobian {a w : ℂ} (ha : ‖a‖ < 1) (hw : ‖w‖ < 1) :
    ‖deriv (blaschke a) w‖ ^ 2 =
      ((1 - ‖a‖ ^ 2) / ‖1 - conj a * w‖ ^ 2) ^ 2 := by
  have hn : 0 ≤ 1 - ‖a‖ ^ 2 := by nlinarith [norm_nonneg a]
  rw [(hasDerivAt_blaschke ha hw).deriv, norm_div, norm_pow,
    Complex.mul_conj, Complex.normSq_eq_norm_sq,
    ← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hn]

set_option maxHeartbeats 800000 in
/-- Full weighted integrand transformation moving the first argument to zero in (7.8). (TT:3053–3082). -/
theorem bKernel_blaschke_integrand {a v w : ℂ}
    (ha : ‖a‖ < 1) (hv : ‖v‖ < 1) (hw : ‖w‖ < 1) :
    (‖deriv (blaschke a) w‖ ^ 2 : ℝ) •
      ((resolventKernel 0 (blaschke a w) : ℂ) * ((1 - ‖blaschke a w‖ ^ 2) ^ 2 : ℝ) /
        (1 - blaschke a w * conj (blaschke a v)) ^ 4) =
      ((resolventKernel a w : ℂ) * ((1 - ‖w‖ ^ 2) ^ 2 : ℝ) /
        ((1 - w * conj v) ^ 4 * (1 - a * conj w) ^ 4)) * (1 - a * conj v) ^ 4 := by
  have hwd := blaschke_den_ne_zero ha hw
  have hwd' : 1 - w * conj a ≠ 0 := by simpa only [mul_comm] using hwd
  have hwdc : 1 - a * conj w ≠ 0 := by
    intro h
    apply hwd
    simpa using congrArg (starRingEnd ℂ) h
  have ha0 := one_sub_mul_conj_ne_zero ha
  have hav := bKernel_denominator_ne_zero ha.le hv
  have hwv := bKernel_denominator_ne_zero hw.le hv
  have hA : ((1 - ‖a‖ ^ 2 : ℝ) : ℂ) = 1 - a * conj a := by
    simp only [Complex.ofReal_sub, Complex.ofReal_one, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have hD : ((‖1 - conj a * w‖ ^ 2 : ℝ) : ℂ) =
      (1 - conj a * w) * (1 - a * conj w) := by
    rw [← Complex.normSq_eq_norm_sq, ← Complex.mul_conj]
    simp only [map_sub, map_one, map_mul, conj_conj]
  have hB := one_sub_normSq_blaschke ha hw
  simp only [Complex.normSq_eq_norm_sq] at hB
  rw [bKernel_blaschke_jacobian ha hw, resolventKernel_blaschke_center ha hw,
    hB, bKernel_blaschke_polarization ha hw hv]
  simp only [Complex.real_smul, Complex.ofReal_pow, Complex.ofReal_div, Complex.ofReal_mul]
  have hnorm : (‖1 - conj a * w‖ : ℂ) ^ 2 =
      (1 - conj a * w) * (1 - a * conj w) := by exact_mod_cast hD
  rw [hA, hnorm]
  field_simp [ha0, hwd, hwd', hwdc, hav, hwv]
  <;> ring

/-- Integral transport from the disk center in (7.8), TT:3058–3082. -/
theorem bKernel_blaschke_center_transport {a v : ℂ} (ha : a ∈ unitDisc) (hv : v ∈ unitDisc) :
    bKernel 0 (blaschke a v) = bKernel a v * (1 - a * conj v) ^ 4 := by
  have ha1 : ‖a‖ < 1 := mem_ball_zero_iff.mp ha
  have hv1 : ‖v‖ < 1 := mem_ball_zero_iff.mp hv
  have hf := isConformalOnto_blaschke ha1
  have hi := ahP_integral_image (U := unitDisc) (show IsOpen unitDisc from isOpen_ball)
    hf.1 hf.2.1 (fun w : ℂ => (resolventKernel 0 w : ℂ) *
      ((1 - ‖w‖ ^ 2) ^ 2 : ℝ) / (1 - w * conj (blaschke a v)) ^ 4)
  rw [hf.2.2] at hi
  unfold bKernel
  simp only [zero_mul, sub_zero, one_pow, mul_one]
  rw [hi, ← integral_mul_const]
  apply setIntegral_congr_fun measurableSet_ball
  intro w hw
  exact bKernel_blaschke_integrand ha1 hv1 (mem_ball_zero_iff.mp hw)

/-- The explicit disk kernel formula in (7.8), TT:3082. -/
theorem bKernel_closed_form {z v : ℂ} (hz : z ∈ unitDisc) (hv : v ∈ unitDisc) :
    bKernel z v = 1 / (9 * (1 - z * conj v) ^ 4) := by
  have hz1 : ‖z‖ < 1 := mem_ball_zero_iff.mp hz
  have hv1 : ‖v‖ < 1 := mem_ball_zero_iff.mp hv
  have he := bKernel_blaschke_center_transport hz hv
  rw [bKernel_center_parameter (mem_ball_zero_iff.mpr (blaschke_mem_unitDisc hz1 hv1))] at he
  have hd := pow_ne_zero 4 (bKernel_denominator_ne_zero hz1.le hv1)
  apply (eq_div_iff (mul_ne_zero (by norm_num) hd)).mpr
  calc
    _ = 9 * (bKernel z v * (1 - z * conj v) ^ 4) := by ring
    _ = 1 := by rw [← he]; norm_num

/-- SU(1,1) maps have no pole on the disk in (7.8), TT:3058. -/
theorem bKernel_su11_denominator {g : SL2C} (hg : IsSU11 g) {z : ℂ} (hz : ‖z‖ < 1) :
    g 1 0 * z + g 1 1 ≠ 0 := by
  intro h
  have hb := su11_denominator_balance g hg z
  rw [h, norm_zero, zero_pow (by decide : 2 ≠ 0)] at hb
  nlinarith [sq_nonneg ‖g 0 0 * z + g 0 1‖, norm_nonneg z]

/-- The SU(1,1) action preserves the disk in (7.8), TT:3058. -/
theorem bKernel_su11_mapsTo {g : SL2C} (hg : IsSU11 g) {z : ℂ} (hz : z ∈ unitDisc) :
    mob g z ∈ unitDisc := by
  have hz1 : ‖z‖ < 1 := mem_ball_zero_iff.mp hz
  have hd := bKernel_su11_denominator hg hz1
  have he := su11_one_sub_norm_mob g hg z hd
  have hn : 0 < 1 - ‖z‖ ^ 2 := by nlinarith [norm_nonneg z]
  have hpos := div_pos hn (sq_pos_of_ne_zero (norm_ne_zero_iff.mpr hd))
  apply mem_ball_zero_iff.mpr
  nlinarith [norm_nonneg (mob g z)]

/-- The determinant-one derivative formula used in (7.8), TT:3058. -/
theorem bKernel_mob_hasDerivAt {g : SL2C} {z : ℂ} (hz : g 1 0 * z + g 1 1 ≠ 0) :
    HasDerivAt (mob g) (1 / (g 1 0 * z + g 1 1) ^ 2) z := by
  have hd : g 0 0 * g 1 1 - g 0 1 * g 1 0 = 1 := by
    simpa only [Matrix.det_fin_two] using g.property
  have hnum : HasDerivAt (fun w : ℂ => g 0 0 * w + g 0 1) (g 0 0) z := by
    simpa using (((hasDerivAt_id z).const_mul (g 0 0)).add_const (g 0 1))
  have hden : HasDerivAt (fun w : ℂ => g 1 0 * w + g 1 1) (g 1 0) z := by
    simpa using (((hasDerivAt_id z).const_mul (g 1 0)).add_const (g 1 1))
  have hn : g 0 0 * (g 1 0 * z + g 1 1) -
      (g 0 0 * z + g 0 1) * g 1 0 = 1 := by
    calc
      _ = g 0 0 * g 1 1 - g 0 1 * g 1 0 := by ring
      _ = 1 := hd
  convert hnum.div hden hz using 1
  · ext w
    rfl
  · simp only [hn]

/-- Polarized SU(1,1) denominator identity underlying (7.8), TT:3058. -/
theorem bKernel_su11_polarization {g : SL2C} (hg : IsSU11 g) {z v : ℂ}
    (hz : ‖z‖ < 1) (hv : ‖v‖ < 1) :
    1 - mob g z * conj (mob g v) = (1 - z * conj v) /
      ((g 1 0 * z + g 1 1) * conj (g 1 0 * v + g 1 1)) := by
  have hd : g 0 0 * conj (g 0 0) - g 0 1 * conj (g 0 1) = 1 := by
    have h : g 0 0 * g 1 1 - g 0 1 * g 1 0 = 1 := by
      simpa only [Matrix.det_fin_two] using g.property
    simpa only [hg.1, hg.2] using h
  have hzd := bKernel_su11_denominator hg hz
  have hzd' : z * g 1 0 + g 1 1 ≠ 0 := by simpa only [mul_comm] using hzd
  have hvd := bKernel_su11_denominator hg hv
  have hvdc : conj (g 1 0 * v + g 1 1) ≠ 0 := by
    intro h
    apply hvd
    simpa only [conj_conj, map_zero] using congrArg (starRingEnd ℂ) h
  have hn : (g 1 0 * z + g 1 1) * conj (g 1 0 * v + g 1 1) -
      (g 0 0 * z + g 0 1) * conj (g 0 0 * v + g 0 1) = 1 - z * conj v := by
    calc
      _ = (1 - z * conj v) * (g 0 0 * conj (g 0 0) - g 0 1 * conj (g 0 1)) := by
        simp only [hg.1, hg.2, map_add, map_mul, conj_conj]
        ring
      _ = _ := by rw [hd, mul_one]
  unfold mob
  rw [map_div₀]
  calc
    _ = ((g 1 0 * z + g 1 1) * conj (g 1 0 * v + g 1 1) -
        (g 0 0 * z + g 0 1) * conj (g 0 0 * v + g 0 1)) /
        ((g 1 0 * z + g 1 1) * conj (g 1 0 * v + g 1 1)) := by
      field_simp [hzd, hzd', hvdc]
      <;> ring
    _ = _ := by rw [hn]

/-- SU(1,1) covariance of the kernel in (7.8), TT:3058. -/
theorem bKernel_covariance {g : SL2C} (hg : IsSU11 g) {z v : ℂ}
    (hz : z ∈ unitDisc) (hv : v ∈ unitDisc) :
    bKernel z v = bKernel (mob g z) (mob g v) *
      deriv (mob g) z ^ 2 * conj (deriv (mob g) v) ^ 2 := by
  have hz1 : ‖z‖ < 1 := mem_ball_zero_iff.mp hz
  have hv1 : ‖v‖ < 1 := mem_ball_zero_iff.mp hv
  have hzd := bKernel_su11_denominator hg hz1
  have hvd := bKernel_su11_denominator hg hv1
  have hzd' : z * g 1 0 + g 1 1 ≠ 0 := by simpa only [mul_comm] using hzd
  have hvdc : conj (g 1 0 * v + g 1 1) ≠ 0 := by
    intro h
    apply hvd
    simpa only [conj_conj, map_zero] using congrArg (starRingEnd ℂ) h
  have hd := bKernel_denominator_ne_zero hz1.le hv1
  rw [bKernel_closed_form hz hv,
    bKernel_closed_form (bKernel_su11_mapsTo hg hz) (bKernel_su11_mapsTo hg hv),
    bKernel_su11_polarization hg hz1 hv1, (bKernel_mob_hasDerivAt hzd).deriv,
    (bKernel_mob_hasDerivAt hvd).deriv]
  simp only [map_div₀, map_one, map_pow]
  field_simp [hzd, hzd', hvdc, hd]
  <;> ring

/-- **(7.8)** (TT:3058–3082).
- `B(z, v) = B(σz, σv) σ'(z)² \overline{σ'(v)}²` for `σ ∈ PSU(1,1)`;
- `B(0, v) = 1/9`;
- hence `B(z, v) = 1/(9(1 - z v̄)⁴)`. -/
theorem eq_7_8 :
    (∀ g : SL2C, IsSU11 g → ∀ z ∈ unitDisc, ∀ v ∈ unitDisc,
      bKernel z v = bKernel (mob g z) (mob g v) * deriv (mob g) z ^ 2 * conj (deriv (mob g) v) ^ 2) ∧
      (∀ v ∈ unitDisc, bKernel 0 v = 1 / 9) ∧ ∀ z ∈ unitDisc, ∀ v ∈ unitDisc, bKernel z v = 1 / (9 * (1 - z * conj v) ^ 4) := by
  exact ⟨fun _ hg _ hz _ hv => bKernel_covariance hg hz hv,
    fun _ hv => bKernel_center_parameter hv, fun _ hz _ hv => bKernel_closed_form hz hv⟩

/-- Angular orthogonality of distinct disk monomials, for the basis in TT:2844–2850. -/
theorem basisMu_monomial_circle_orthogonal {m n : ℕ} (hmn : m ≠ n) (r : ℝ) :
    Real.circleAverage (fun z : ℂ => z ^ m * conj (z ^ n)) 0 r = 0 := by
  have hc : ((m : ℂ) - (n : ℂ)) * I ≠ 0 :=
    mul_ne_zero (sub_ne_zero.mpr (by exact_mod_cast hmn : (m : ℂ) ≠ (n : ℂ))) I_ne_zero
  have he (θ : ℝ) : circleMap 0 r θ ^ m * conj (circleMap 0 r θ ^ n) =
      (r : ℂ) ^ (m + n) * Complex.exp ((((m : ℂ) - (n : ℂ)) * I) * (θ : ℂ)) := by
    simp only [circleMap, zero_add, mul_pow, map_pow, map_mul, conj_ofReal,
      ← Complex.exp_conj, conj_I, ← Complex.exp_nat_mul, pow_add, map_natCast]
    calc
      _ = ((r : ℂ) ^ m * (r : ℂ) ^ n) *
          (Complex.exp ((m : ℂ) * ((θ : ℂ) * I)) *
            Complex.exp ((n : ℂ) * ((θ : ℂ) * -I))) := by ring
      _ = _ := by rw [← Complex.exp_add]; congr 2 <;> ring
  have hend : Complex.exp ((((m : ℂ) - (n : ℂ)) * I) * (2 * π : ℝ)) = 1 := by
    have harg : (((m : ℂ) - (n : ℂ)) * I) * (2 * π : ℝ) =
        (m : ℂ) * (2 * π * I) - (n : ℂ) * (2 * π * I) := by push_cast; ring
    rw [harg, Complex.exp_sub, Complex.exp_nat_mul, Complex.exp_nat_mul,
      Complex.exp_two_pi_mul_I]
    simp
  simp only [Real.circleAverage, he]
  rw [intervalIntegral.integral_const_mul, integral_exp_mul_complex hc]
  rw [hend]
  simp

/-- The weighted disk pairing of distinct monomials vanishes, TT:2844–2850. -/
theorem basisMu_disk_monomial_orthogonal {m n : ℕ} (hmn : m ≠ n) :
    (∫ z in unitDisc, z ^ m * conj (z ^ n) * ((rho z)⁻¹ : ℝ)) = 0 := by
  let f : ℂ → ℂ := fun z => z ^ m * conj (z ^ n) * ((rho z)⁻¹ : ℝ)
  have hf : Continuous f := by
    dsimp [f, rho]
    simp only [inv_div]
    fun_prop
  have hpolar : Continuous (fun p : ℝ × ℝ => p.1 • f (Complex.polarCoord.symm p)) := by
    have hp : Continuous (fun p : ℝ × ℝ => Complex.polarCoord.symm p) := by
      simp only [Complex.polarCoord_symm_apply]
      fun_prop
    exact continuous_fst.smul (hf.comp hp)
  have hi : IntegrableOn (fun p : ℝ × ℝ => p.1 • f (Complex.polarCoord.symm p))
      (Ioo (0 : ℝ) 1 ×ˢ Ioo (-π) π) :=
    (hpolar.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)).mono_set
      (prod_mono Ioo_subset_Icc_self Ioo_subset_Icc_self)
  have havg (r : ℝ) : Real.circleAverage f 0 r = 0 := by
    have he : Real.circleAverage f 0 r =
        (((1 - r ^ 2) ^ 2 / 4 : ℝ) : ℂ) •
          Real.circleAverage (fun z : ℂ => z ^ m * conj (z ^ n)) 0 r := by
      rw [← Real.circleAverage_fun_smul]
      apply Real.circleAverage_congr_sphere
      intro z hz
      have hn : ‖z‖ = |r| := by simpa only [mem_sphere, dist_zero_right] using hz
      dsimp only [f]
      simp only [rho, inv_div, hn, sq_abs, smul_eq_mul, Complex.ofReal_div,
        Complex.ofReal_pow, Complex.ofReal_sub, Complex.ofReal_one, Complex.ofReal_ofNat]
      ring
    rw [he, basisMu_monomial_circle_orthogonal hmn, smul_zero]
  change (∫ z in unitDisc, f z) = 0
  rw [bKernel_polar_integral f hi]
  simp only [havg, smul_zero, integral_zero]

/-- Complex pairings of quadratic differentials transform under inversion, TT:2844–2850. -/
theorem basisMu_inverted_pair_integral (φ ψ : ℂ → ℂ) :
    (∫ z in unitDisc \ {0}, (φ z⁻¹ / z ^ 4) * conj (ψ z⁻¹ / z ^ 4) * ((rho z)⁻¹ : ℝ)) =
      ∫ z in unitDiscExterior, φ z * conj (ψ z) * ((rho z)⁻¹ : ℝ) := by
  have hopen : IsOpen (unitDisc \ {(0 : ℂ)}) := isOpen_ball.sdiff isClosed_singleton
  have hc := inversion_puncturedDisk_conformal
  have hi := ahP_integral_image hopen hc.1 hc.2.1
    (fun z : ℂ => φ z * conj (ψ z) * ((rho z)⁻¹ : ℝ))
  rw [hc.2.2] at hi
  rw [hi]
  apply setIntegral_congr_fun hopen.measurableSet
  intro z hz
  have hz0 : z ≠ 0 := hz.2
  have hzc : conj z ≠ 0 := by
    intro h
    apply hz0
    simpa only [conj_conj, map_zero] using congrArg (starRingEnd ℂ) h
  have hJ : ((‖deriv (fun w : ℂ => w⁻¹) z‖ ^ 2 : ℝ) : ℂ) = 1 / (z * conj z) ^ 2 := by
    rw [(hasDerivAt_inv hz0).deriv, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    simp only [norm_neg, norm_inv, norm_pow, Complex.ofReal_pow, Complex.ofReal_inv,
      one_div, inv_pow]
  dsimp only
  rw [Complex.real_smul, hJ]
  simp only [Complex.ofReal_inv, wp_rho_inv_complex, map_div₀, map_pow, map_inv₀]
  field_simp [hz0, hzc]
  <;> ring

/-- The exterior quadratic monomials are pairwise orthogonal, TT:2844–2850. -/
theorem basisMu_exterior_monomial_orthogonal {m n : ℕ} (hmn : m ≠ n) :
    (∫ z in unitDiscExterior, z ^ (-(m : ℤ) - 4) * conj (z ^ (-(n : ℤ) - 4)) *
      ((rho z)⁻¹ : ℝ)) = 0 := by
  rw [← basisMu_inverted_pair_integral]
  calc
    _ = ∫ z in unitDisc \ {0}, z ^ m * conj (z ^ n) * ((rho z)⁻¹ : ℝ) := by
      apply setIntegral_congr_fun (measurableSet_ball.diff (measurableSet_singleton 0))
      intro z hz
      dsimp only
      rw [basisMu_inverted_monomial m hz.2, basisMu_inverted_monomial n hz.2]
    _ = ∫ z in unitDisc, z ^ m * conj (z ^ n) * ((rho z)⁻¹ : ℝ) :=
      setIntegral_congr_set (sdiff_null_ae_eq_self (measure_singleton 0))
    _ = 0 := basisMu_disk_monomial_orthogonal hmn

/-- Off-diagonal orthogonality of the explicit WP basis, TT:2844–2850. -/
theorem basisMu_wpInner_ne {m n : ℕ} (hmn : m ≠ n) :
    wpInner (basisMu (m + 2)) (basisMu (n + 2)) = 0 := by
  let c : ℕ → ℂ := fun k => -4 *
    (Real.sqrt (((k + 2 : ℕ) : ℝ) ^ 3 - ((k + 2 : ℕ) : ℝ)) / Real.sqrt (8 * π) : ℂ)
  have hc (k : ℕ) : conj (c k) = c k := by
    simp only [c, map_mul, map_neg, map_ofNat, map_div₀, conj_ofReal]
  have hp (z : ℂ) (hz : z ∈ unitDiscExterior) :
      basisMu (m + 2) z * conj (basisMu (n + 2) z) * (rho z : ℂ) =
        (c m * c n) * (z ^ (-(n : ℤ) - 4) * conj (z ^ (-(m : ℤ) - 4)) * ((rho z)⁻¹ : ℝ)) := by
    have hm : basisMu (m + 2) z = (rho z : ℂ)⁻¹ * conj (c m * z ^ (-(m : ℤ) - 4)) :=
      basisMu_harmonic_representation m z
    have hn : basisMu (n + 2) z = (rho z : ℂ)⁻¹ * conj (c n * z ^ (-(n : ℤ) - 4)) :=
      basisMu_harmonic_representation n z
    have hr : (rho z : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (wp_rho_pos hz).ne'
    rw [hm, hn]
    simp only [map_mul, map_inv₀, conj_ofReal, conj_conj, hc, Complex.ofReal_inv]
    field_simp
    <;> ring
  unfold wpInner
  calc
    _ = (c m * c n) * ∫ z in unitDiscExterior,
        z ^ (-(n : ℤ) - 4) * conj (z ^ (-(m : ℤ) - 4)) * ((rho z)⁻¹ : ℝ) := by
      rw [← integral_const_mul]
      exact setIntegral_congr_fun wp_exterior_isOpen.measurableSet hp
    _ = 0 := by rw [basisMu_exterior_monomial_orthogonal hmn.symm, mul_zero]

/-- The orthonormality clause for all indices of the explicit WP basis, TT:2844–2850. -/
theorem basisMu_wpInner {m n : ℕ} (hm : 2 ≤ m) (hn : 2 ≤ n) :
    wpInner (basisMu m) (basisMu n) = if m = n then 1 else 0 := by
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, m = k + 2 := ⟨m - 2, by omega⟩
  obtain ⟨l, rfl⟩ : ∃ l : ℕ, n = l + 2 := ⟨n - 2, by omega⟩
  by_cases h : k = l
  · subst l
    simpa using basisMu_wpInner_self k
  · have hne : k + 2 ≠ l + 2 := by omega
    rw [if_neg hne]
    exact basisMu_wpInner_ne h

/-- The explicit WP family is orthonormal in its genuine weighted L2 realization, TT:2844–2850. -/
theorem basisMu_weighted_orthonormal :
    Orthonormal ℂ (fun k : ℕ =>
      (wp_weighted_memLp (basisMu_mem_harmonicL2 k)).toLp
        (fun z => basisMu (k + 2) z * (Real.sqrt (rho z) : ℂ))) := by
  rw [orthonormal_iff_ite]
  intro m n
  rw [wpInner_eq_L2_inner (basisMu_mem_harmonicL2 n) (basisMu_mem_harmonicL2 m),
    basisMu_wpInner (by omega) (by omega)]
  simp only [Nat.add_right_cancel_iff, eq_comm]

/-- Finite Bessel inequality for the explicit WP coefficients, TT:2844–2850. -/
theorem basisMu_bessel_finset {μ : ℂ → ℂ} (hμ : μ ∈ harmonicL2 unitDiscExterior)
    (s : Finset ℕ) :
    ∑ k ∈ s, ‖wpInner μ (basisMu (k + 2))‖ ^ 2 ≤ (wpInner μ μ).re := by
  let x := (wp_weighted_memLp hμ).toLp (fun z => μ z * (Real.sqrt (rho z) : ℂ))
  have hi := basisMu_weighted_orthonormal.sum_inner_products_le (s := s) x
  simp only [x, wpInner_eq_L2_inner hμ (basisMu_mem_harmonicL2 _)] at hi
  have hx : ‖x‖ ^ 2 = (wpInner μ μ).re :=
    (norm_sq_eq_re_inner (𝕜 := ℂ) x).trans (congrArg Complex.re (wpInner_eq_L2_inner hμ hμ))
  exact hi.trans_eq hx

/-- Bessel inequality for the full sequence of WP coefficients, TT:2844–2850. -/
theorem basisMu_bessel {μ : ℂ → ℂ} (hμ : μ ∈ harmonicL2 unitDiscExterior) :
    (∑' k : ℕ, ‖wpInner μ (basisMu (k + 2))‖ ^ 2) ≤ (wpInner μ μ).re := by
  exact tsum_le_of_sum_le' (by simpa using basisMu_bessel_finset hμ ∅)
    (fun s => basisMu_bessel_finset hμ s)

/-- The squared WP coefficients of every harmonic L2 representative are summable, TT:2844–2850. -/
theorem basisMu_coefficients_summable {μ : ℂ → ℂ} (hμ : μ ∈ harmonicL2 unitDiscExterior) :
    Summable (fun k : ℕ => ‖wpInner μ (basisMu (k + 2))‖ ^ 2) := by
  have hi := basisMu_weighted_orthonormal.inner_products_summable
    ((wp_weighted_memLp hμ).toLp (fun z => μ z * (Real.sqrt (rho z) : ℂ)))
  simpa only [wpInner_eq_L2_inner hμ (basisMu_mem_harmonicL2 _)] using hi












/-- The weighted Bergman moment series reproduces a holomorphic disk function, TT:1374–1390. -/
theorem wp_bergman_kernel_moment_series {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f unitDisc)
    {C : ℝ} (hb : ∀ w ∈ unitDisc, ‖f w * ((rho w)⁻¹ : ℝ)‖ ≤ C)
    {a : ℂ} (ha : a ∈ unitDisc) :
    HasSum (fun n : ℕ => ((n + 3).choose 3 : ℂ) * a ^ n *
      (∫ w in unitDisc, f w * conj (w ^ n) * ((rho w)⁻¹ : ℝ))) ((π / 12 : ℝ) • f a) := by
  let F : ℕ → ℂ → ℂ := fun n w => ((n + 3).choose 3 : ℂ) * (a * conj w) ^ n *
    (f w * ((rho w)⁻¹ : ℝ))
  let b : ℕ → ℂ → ℝ := fun n _ => C * ((n + 3).choose 3 : ℝ) * ‖a‖ ^ n
  haveI : IsFiniteMeasure (volume.restrict unitDisc) := by
    apply isFiniteMeasure_restrict.mpr
    exact (lt_of_le_of_lt (measure_mono ball_subset_closedBall)
      (isCompact_closedBall (0 : ℂ) 1).measure_lt_top).ne
  have ha1 : ‖a‖ < 1 := mem_ball_zero_iff.mp ha
  have hw : Continuous (fun w : ℂ => ((rho w)⁻¹ : ℝ)) := by
    simp only [rho, inv_div]
    fun_prop
  have hFmeas (n : ℕ) : AEStronglyMeasurable (F n) (volume.restrict unitDisc) := by
    apply ContinuousOn.aestronglyMeasurable _ measurableSet_ball
    exact (continuousOn_const.mul ((continuousOn_const.mul
      Complex.continuous_conj.continuousOn).pow n)).mul
      (hf.continuousOn.mul (Complex.continuous_ofReal.comp_continuousOn hw.continuousOn))
  have hbound (n : ℕ) : ∀ᵐ w ∂(volume.restrict unitDisc), ‖F n w‖ ≤ b n w := by
    filter_upwards [ae_restrict_mem measurableSet_ball] with w hwD
    have hw1 : ‖w‖ ≤ 1 := (mem_ball_zero_iff.mp hwD).le
    have hnorm : ‖a * conj w‖ ≤ ‖a‖ := by
      simpa only [norm_mul, norm_conj] using mul_le_of_le_one_right (norm_nonneg a) hw1
    dsimp only [F, b]
    rw [norm_mul, norm_mul, Complex.norm_natCast, norm_pow]
    calc
      _ ≤ (((n + 3).choose 3 : ℝ) * ‖a‖ ^ n) * C :=
        mul_le_mul (mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (norm_nonneg _) hnorm n) (Nat.cast_nonneg _)) (hb w hwD)
          (norm_nonneg _) (by positivity)
      _ = _ := by ring
  have hbs : Summable (fun n : ℕ => C * ((n + 3).choose 3 : ℝ) * ‖a‖ ^ n) := by
    have h := (hasSum_choose_mul_geometric_of_norm_lt_one (r := ‖a‖) 3
      (by simpa only [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg a)] using ha1)).summable.mul_left C
    simpa only [mul_assoc] using h
  have hlim : ∀ᵐ w ∂(volume.restrict unitDisc), HasSum (fun n => F n w)
      (f w * ((rho w)⁻¹ : ℝ) / (1 - a * conj w) ^ 4) := by
    filter_upwards [ae_restrict_mem measurableSet_ball] with w hwD
    have hnorm : ‖a * conj w‖ < 1 := by
      rw [norm_mul, norm_conj]
      exact (mul_le_of_le_one_right (norm_nonneg a) (mem_ball_zero_iff.mp hwD).le).trans_lt ha1
    have h := (hasSum_choose_mul_geometric_of_norm_lt_one 3 hnorm).mul_right
      (f w * ((rho w)⁻¹ : ℝ))
    convert h using 1
    norm_num
    ring
  have hbi : Integrable (fun w : ℂ => ∑' n, b n w) (volume.restrict unitDisc) := by
    simpa only [b] using (integrable_const (μ := volume.restrict unitDisc)
      (∑' n : ℕ, C * ((n + 3).choose 3 : ℝ) * ‖a‖ ^ n))
  have hs := hasSum_integral_of_dominated_convergence b hFmeas hbound
    (ae_of_all _ (fun _ => hbs)) hbi hlim
  rw [wp_bergman_reproduce hf hb ha] at hs
  convert hs using 1
  ext n
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with w
  simp only [F, map_pow, mul_pow]
  ring

/-- Vanishing of all weighted Bergman moments forces vanishing of the function, TT:2844–2850. -/
theorem wp_bergman_moments_determine {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f unitDisc)
    {C : ℝ} (hb : ∀ w ∈ unitDisc, ‖f w * ((rho w)⁻¹ : ℝ)‖ ≤ C)
    (hzero : ∀ n : ℕ, (∫ w in unitDisc, f w * conj (w ^ n) * ((rho w)⁻¹ : ℝ)) = 0) :
    EqOn f 0 unitDisc := by
  intro a ha
  have hs := (wp_bergman_kernel_moment_series hf hb ha).tsum_eq
  simp only [hzero, mul_zero, tsum_zero] at hs
  have hp : (π / 12 : ℝ) ≠ 0 := by positivity
  exact (smul_eq_zero.mp hs.symm).resolve_left hp

/-- Weighted monomial moments separate all disk A2 functions, TT:2844–2850. -/
theorem wp_bergman_A2_moments_determine {f : ℂ → ℂ} (hf : f ∈ A2fun unitDisc)
    (hzero : ∀ n : ℕ, (∫ w in unitDisc, f w * conj (w ^ n) * ((rho w)⁻¹ : ℝ)) = 0) :
    EqOn f 0 unitDisc :=
  wp_bergman_moments_determine hf.1 (fun _ hw => wp_bergman_A2_weighted_bound hf hw) hzero

/-- The Hilbert inner product of A2 elements is the weighted integral of their holomorphic representatives. (TT:1351–1390, TT:2844–2850). -/
theorem wp_A2_inner_integral {D : Set ℂ} (φ ψ : A2 D) :
    inner ℂ φ ψ = ∫ z in D, A2.toFun ψ z * conj (A2.toFun φ z) * ((rho z)⁻¹ : ℝ) := by
  change inner ℂ (φ : Lp ℂ 2 (rhoInvMeasure D)) (ψ : Lp ℂ 2 (rhoInvMeasure D)) = _
  rw [L2.inner_def]
  calc
    _ = ∫ z, A2.toFun ψ z * conj (A2.toFun φ z) ∂rhoInvMeasure D := by
      apply integral_congr_ae
      filter_upwards [(A2.toFun_spec φ).2, (A2.toFun_spec ψ).2] with z hφ hψ
      rw [hφ, hψ, RCLike.inner_apply]
    _ = _ := by
      have hm : Measurable (fun z : ℂ => ENNReal.ofReal (rho z)⁻¹) := by
        unfold rho
        fun_prop
      rw [rhoInvMeasure, integral_withDensity_eq_integral_toReal_smul hm
        (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))]
      apply integral_congr_ae
      filter_upwards with z
      rw [ENNReal.toReal_ofReal (inv_nonneg.mpr (wp_rho_nonneg z)), Complex.real_smul]
      ring

/-- Every disk monomial defines a genuine A2 element. (TT:1351–1390, TT:2844–2850). -/
theorem wp_disk_monomial_A2 (n : ℕ) : (fun z : ℂ => z ^ n) ∈ A2fun unitDisc := by
  refine ⟨differentiableOn_id.pow n, normA2_lt_top_of_integrable_weighted_sq ?_⟩
  have hc : Continuous (fun z : ℂ => ‖z ^ n‖ ^ 2 * (rho z)⁻¹) := by
    simp only [rho, inv_div]
    fun_prop
  exact (hc.continuousOn.integrableOn_compact (isCompact_closedBall (0 : ℂ) 1)).mono_set
    ball_subset_closedBall

/-- The selected A2 monomial agrees pointwise with its polynomial on the disk. (TT:1351–1390, TT:2844–2850). -/
theorem wp_A2_monomial_toFun (n : ℕ) :
    EqOn (A2.toFun (toA2 unitDisc (fun z : ℂ => z ^ n))) (fun z => z ^ n) unitDisc :=
  toA2_spec isOpen_ball (fun z hz => (mem_ball_zero_iff.mp hz).ne) (wp_disk_monomial_A2 n)

/-- Weighted monomial inner products in the actual A2 Hilbert space, TT:1374–1378. -/
theorem wp_A2_monomial_inner (m n : ℕ) :
    inner ℂ (toA2 unitDisc (fun z : ℂ => z ^ m)) (toA2 unitDisc (fun z : ℂ => z ^ n)) =
      if m = n then (π / (2 * (((n : ℝ) + 1) * ((n : ℝ) + 2) * ((n : ℝ) + 3))) : ℝ) else 0 := by
  rw [wp_A2_inner_integral]
  have he : (∫ z in unitDisc, A2.toFun (toA2 unitDisc (fun z : ℂ => z ^ n)) z *
      conj (A2.toFun (toA2 unitDisc (fun z : ℂ => z ^ m)) z) * ((rho z)⁻¹ : ℝ)) =
      ∫ z in unitDisc, z ^ n * conj (z ^ m) * ((rho z)⁻¹ : ℝ) := by
    apply setIntegral_congr_fun measurableSet_ball
    intro z hz
    dsimp only
    rw [wp_A2_monomial_toFun n hz, wp_A2_monomial_toFun m hz]
  rw [he]
  by_cases hmn : m = n
  · subst m
    rw [if_pos rfl]
    simp only [Complex.mul_conj, Complex.normSq_eq_norm_sq, ← Complex.ofReal_mul,
      integral_complex_ofReal, bergman_monomial_area]
  · rw [if_neg hmn]
    exact basisMu_disk_monomial_orthogonal (Ne.symm hmn)

/-- Normalized disk monomials in A2, corresponding to the exterior WP basis of TT:2844. -/
def wp_A2_basisVector (n : ℕ) : A2 unitDisc :=
  (Real.sqrt (2 * (((n : ℝ) + 1) * ((n : ℝ) + 2) * ((n : ℝ) + 3)) / π) : ℂ) •
    toA2 unitDisc (fun z : ℂ => z ^ n)

/-- The normalized disk monomials are an orthonormal family, TT:1374–1378, TT:2844–2850. -/
theorem wp_A2_basisVector_orthonormal : Orthonormal ℂ wp_A2_basisVector := by
  rw [orthonormal_iff_ite]
  intro m n
  have hscale (x y : A2 unitDisc) (c d : ℂ) :
      inner ℂ (c • x) (d • y) = conj c * (d * inner ℂ x y) := by
    change inner ℂ (c • (x : Lp ℂ 2 (rhoInvMeasure unitDisc)))
      (d • (y : Lp ℂ 2 (rhoInvMeasure unitDisc))) =
      conj c * (d * inner ℂ (x : Lp ℂ 2 (rhoInvMeasure unitDisc))
        (y : Lp ℂ 2 (rhoInvMeasure unitDisc)))
    rw [inner_smul_left, inner_smul_right]
  change inner ℂ
    ((Real.sqrt (2 * (((m : ℝ) + 1) * ((m : ℝ) + 2) * ((m : ℝ) + 3)) / π) : ℂ) •
      toA2 unitDisc (fun z : ℂ => z ^ m))
    ((Real.sqrt (2 * (((n : ℝ) + 1) * ((n : ℝ) + 2) * ((n : ℝ) + 3)) / π) : ℂ) •
      toA2 unitDisc (fun z : ℂ => z ^ n)) = _
  rw [hscale, conj_ofReal, wp_A2_monomial_inner]
  by_cases hmn : m = n
  · subst m
    simp only [ite_true]
    have hq : 0 ≤ 2 * (((n : ℝ) + 1) * ((n : ℝ) + 2) * ((n : ℝ) + 3)) / π := by positivity
    have hc : (Real.sqrt (2 * (((n : ℝ) + 1) * ((n : ℝ) + 2) * ((n : ℝ) + 3)) / π)) ^ 2 *
        (π / (2 * (((n : ℝ) + 1) * ((n : ℝ) + 2) * ((n : ℝ) + 3)))) = 1 := by
      rw [Real.sq_sqrt hq]
      field_simp
    have hcast := congrArg Complex.ofReal hc
    push_cast at hcast
    push_cast
    convert hcast using 1 <;> ring
  · simp only [if_neg hmn, Complex.ofReal_zero, mul_zero]

/-- Hilbert coefficients of normalized disk monomials are weighted moments. (TT:1351–1390, TT:2844–2850). -/
theorem wp_A2_basisVector_inner (n : ℕ) (φ : A2 unitDisc) :
    inner ℂ (wp_A2_basisVector n) φ =
      (Real.sqrt (2 * (((n : ℝ) + 1) * ((n : ℝ) + 2) * ((n : ℝ) + 3)) / π) : ℂ) *
        ∫ z in unitDisc, A2.toFun φ z * conj (z ^ n) * ((rho z)⁻¹ : ℝ) := by
  change inner ℂ
    ((Real.sqrt (2 * (((n : ℝ) + 1) * ((n : ℝ) + 2) * ((n : ℝ) + 3)) / π) : ℂ) •
      (toA2 unitDisc (fun z : ℂ => z ^ n) : Lp ℂ 2 (rhoInvMeasure unitDisc)))
    (φ : Lp ℂ 2 (rhoInvMeasure unitDisc)) = _
  rw [inner_smul_left, conj_ofReal]
  change (Real.sqrt (2 * (((n : ℝ) + 1) * ((n : ℝ) + 2) * ((n : ℝ) + 3)) / π) : ℂ) *
    inner ℂ (toA2 unitDisc (fun z : ℂ => z ^ n)) φ = _
  rw [wp_A2_inner_integral]
  congr 1
  apply setIntegral_congr_fun measurableSet_ball
  intro z hz
  dsimp only
  rw [wp_A2_monomial_toFun n hz]

/-- The normalized disk monomials have trivial orthogonal complement, by moment separation. (TT:1351–1390, TT:2844–2850). -/
theorem wp_A2_basisVector_total :
    (Submodule.span ℂ (Set.range wp_A2_basisVector))ᗮ = ⊥ := by
  apply bot_unique
  intro φ hφ
  have hinner (n : ℕ) : inner ℂ (wp_A2_basisVector n) φ = 0 :=
    Submodule.inner_right_of_mem_orthogonal (Submodule.subset_span
      (show wp_A2_basisVector n ∈ Set.range wp_A2_basisVector from ⟨n, rfl⟩)) hφ
  have hmom (n : ℕ) : (∫ z in unitDisc, A2.toFun φ z * conj (z ^ n) * ((rho z)⁻¹ : ℝ)) = 0 := by
    have hi := hinner n
    rw [wp_A2_basisVector_inner] at hi
    have hc : (Real.sqrt (2 * (((n : ℝ) + 1) * ((n : ℝ) + 2) * ((n : ℝ) + 3)) / π) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (by positivity)).ne'
    exact (mul_eq_zero.mp hi).resolve_left hc
  have hfzero := wp_bergman_A2_moments_determine (A2.toFun_mem φ) hmom
  have hzero : EqOn (A2.toFun (0 : A2 unitDisc)) (fun _ : ℂ => 0) unitDisc := by
    apply A2.toFun_eqOn isOpen_ball (fun z hz => (mem_ball_zero_iff.mp hz).ne)
      (0 : A2 unitDisc) (differentiableOn_const (0 : ℂ))
    exact Lp.coeFn_zero _ _ _
  change φ = 0
  apply A2.ext_of_toFun_eqOn measurableSet_ball
  intro z hz
  exact (hfzero hz).trans (hzero hz).symm

/-- The complete normalized monomial Hilbert basis of the disk A2 space. (TT:1351–1390, TT:2844–2850). -/
def wp_A2_hilbertBasis : HilbertBasis ℕ ℂ (A2 unitDisc) :=
  HilbertBasis.mkOfOrthogonalEqBot wp_A2_basisVector_orthonormal wp_A2_basisVector_total

/-- The Hilbert-basis constructor preserves the explicit normalized monomials. (TT:1351–1390, TT:2844–2850). -/
theorem wp_A2_hilbertBasis_apply (n : ℕ) : wp_A2_hilbertBasis n = wp_A2_basisVector n := by
  simp only [wp_A2_hilbertBasis, HilbertBasis.coe_mkOfOrthogonalEqBot]

/-- Every disk A2 element has its norm-convergent normalized monomial expansion. (TT:1351–1390, TT:2844–2850). -/
theorem wp_A2_basis_expansion (φ : A2 unitDisc) :
    HasSum (fun n : ℕ => inner ℂ (wp_A2_basisVector n) φ • wp_A2_basisVector n) φ := by
  simpa only [HilbertBasis.repr_apply_apply, wp_A2_hilbertBasis_apply] using
    wp_A2_hilbertBasis.hasSum_repr φ


/-- A disk A2 function pulls back to an integrable exterior quadratic differential. (TT:1351–1410, TT:2844–2850). -/
theorem wp_inverted_disk_A2_integrable {f : ℂ → ℂ} (hf : f ∈ A2fun unitDisc) :
    IntegrableOn (fun w : ℂ => ‖f w⁻¹ / w ^ 4‖ ^ 2 * (rho w)⁻¹) unitDiscExterior := by
  have hopen : IsOpen (unitDisc \ {(0 : ℂ)}) := isOpen_ball.sdiff isClosed_singleton
  have hinv := inversion_puncturedDisk_conformal
  have hchange := ahP_integrableOn_image hopen hinv.1 hinv.2.1
    (fun w : ℂ => ‖f w⁻¹ / w ^ 4‖ ^ 2 * (rho w)⁻¹)
  rw [hinv.2.2] at hchange
  apply hchange.mpr
  apply ((A2fun.integrable_weighted_sq isOpen_ball hf).mono_set sdiff_subset).congr
  filter_upwards [ae_restrict_mem hopen.measurableSet] with z hz
  have he := inverted_quadratic_weight (φ := fun w : ℂ => f w⁻¹ / w ^ 4) hz.2
  rw [wp_quadratic_inversion_involutive f hz.2] at he
  simpa only [smul_eq_mul, mul_comm] using he

/-- The inverse-direction disk-to-exterior map on quadratic A2 functions. (TT:1351–1410, TT:2844–2850). -/
theorem wp_inverted_disk_A2 {f : ℂ → ℂ} (hf : f ∈ A2fun unitDisc) :
    (fun w : ℂ => f w⁻¹ / w ^ 4) ∈ A2fun unitDiscExterior := by
  refine ⟨?_, normA2_lt_top_of_integrable_weighted_sq (wp_inverted_disk_A2_integrable hf)⟩
  intro w hw
  have hw0 := resolvent_exterior_ne_zero hw
  have hwi := resolvent_inv_exterior_conformal.mapsTo hw
  exact (((hf.1.differentiableAt (isOpen_ball.mem_nhds hwi.1)).comp w
    (differentiableAt_inv hw0)).div (differentiableAt_id.pow 4)
      (pow_ne_zero 4 hw0)).differentiableWithinAt

/-- Disk-to-exterior inversion preserves the quadratic A2 norm. (TT:1351–1410, TT:2844–2850). -/
theorem wp_inverted_disk_A2_norm {f : ℂ → ℂ} (hf : f ∈ A2fun unitDisc) :
    normA2 unitDiscExterior (fun w => f w⁻¹ / w ^ 4) = normA2 unitDisc f := by
  have harea : (∫ w in unitDiscExterior, ‖f w⁻¹ / w ^ 4‖ ^ 2 * (rho w)⁻¹) =
      ∫ z in unitDisc, ‖f z‖ ^ 2 * (rho z)⁻¹ := by
    rw [← inverted_quadratic_weighted_integral]
    calc
      _ = ∫ z in unitDisc \ {0}, ‖f z‖ ^ 2 * (rho z)⁻¹ := by
        apply setIntegral_congr_fun (measurableSet_ball.diff (measurableSet_singleton 0))
        intro z hz
        dsimp only
        rw [wp_quadratic_inversion_involutive f hz.2]
      _ = _ := setIntegral_congr_set (sdiff_null_ae_eq_self (measure_singleton 0))
  apply (ENNReal.strictMono_rpow_of_pos (by norm_num : (0 : ℝ) < 2)).injective
  simp only [ENNReal.rpow_two]
  rw [A2fun.normA2_sq wp_exterior_isOpen (wp_inverted_disk_A2 hf),
    A2fun.normA2_sq (D := unitDisc) isOpen_ball hf, harea]


/-- The disk-to-harmonic map preserves the weighted norms. (TT:1351–1410, TT:2844–2850). -/
theorem wp_harmonicOfDisk_norm {f : ℂ → ℂ} (hf : f ∈ A2fun unitDisc) :
    normL2 unitDiscExterior (wp_harmonicOfDisk f) = normA2 unitDisc f := by
  have he := normA2_eq_normL2_of_harmonic wp_exterior_isOpen.measurableSet
    (fun w hw => ne_of_gt hw) (μ := wp_harmonicOfDisk f) (φ := fun w => f w⁻¹ / w ^ 4)
    (fun _ _ => rfl)
  rw [← he, wp_inverted_disk_A2_norm hf]

/-- Disk A2 functions give harmonic exterior L2 representatives. (TT:1351–1410, TT:2844–2850). -/
theorem wp_harmonicOfDisk_mem {f : ℂ → ℂ} (hf : f ∈ A2fun unitDisc) :
    wp_harmonicOfDisk f ∈ harmonicL2 unitDiscExterior := by
  refine ⟨fun w => f w⁻¹ / w ^ 4, (wp_inverted_disk_A2 hf).1, fun _ _ => rfl, ?_⟩
  rw [wp_harmonicOfDisk_norm hf]
  exact hf.2


/-- The harmonic weighted norm depends only on values on its integration domain (TT:1401). -/
theorem wp_normL2_congr {D : Set ℂ} (hD : MeasurableSet D) {μ ν : ℂ → ℂ}
    (he : EqOn μ ν D) : normL2 D μ = normL2 D ν := by
  unfold normL2
  congr 1
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_mem hD] with z hz
  rw [he hz]

/-- The function-level harmonic image of an actual disk A2 element (TT:1401, TT:2844). -/
def wp_harmonicOfA2 (φ : A2 unitDisc) : ℂ → ℂ := wp_harmonicOfDisk (A2.toFun φ)

/-- The harmonic image of a disk A2 element lies in the exterior Hilbert tangent space (TT:1401). -/
theorem wp_harmonicOfA2_mem (φ : A2 unitDisc) :
    wp_harmonicOfA2 φ ∈ harmonicL2 unitDiscExterior :=
  wp_harmonicOfDisk_mem (A2.toFun_mem φ)

/-- The A2 and harmonic extended norms agree under the disk model map (TT:1401). -/
theorem wp_harmonicOfA2_norm (φ : A2 unitDisc) :
    normL2 unitDiscExterior (wp_harmonicOfA2 φ) = (‖φ‖₊ : ℝ≥0∞) := by
  rw [wp_harmonicOfA2, wp_harmonicOfDisk_norm (A2.toFun_mem φ), A2.norm_toFun]

/-- Zero is preserved on the exterior domain by harmonic contraction (TT:1401). -/
theorem wp_harmonicOfA2_zero : EqOn (wp_harmonicOfA2 0) 0 unitDiscExterior := by
  have hz : EqOn (A2.toFun (0 : A2 unitDisc)) (fun _ : ℂ => 0) unitDisc := by
    apply A2.toFun_eqOn (D := unitDisc) isOpen_ball (fun z hz => (mem_ball_zero_iff.mp hz).ne)
      (0 : A2 unitDisc) (differentiableOn_const (0 : ℂ))
    exact Lp.coeFn_zero _ _ _
  intro w hw
  have hwi := (resolvent_inv_exterior_conformal.mapsTo hw).1
  simp only [wp_harmonicOfA2, wp_harmonicOfDisk, hz hwi, zero_div, map_zero, mul_zero, Pi.zero_apply]

/-- Addition is preserved on the exterior domain (TT:1401, TT:2844–2850). -/
theorem wp_harmonicOfA2_add (φ ψ : A2 unitDisc) :
    EqOn (wp_harmonicOfA2 (φ + ψ)) (wp_harmonicOfA2 φ + wp_harmonicOfA2 ψ) unitDiscExterior := by
  intro w hw
  have hwi := (resolvent_inv_exterior_conformal.mapsTo hw).1
  have he := A2.toFun_add (D := unitDisc) isOpen_ball
    (fun z hz => (mem_ball_zero_iff.mp hz).ne) φ ψ hwi
  simp only [wp_harmonicOfA2, wp_harmonicOfDisk, he, Pi.add_apply, add_div, map_add, mul_add]

/-- Subtraction is preserved on the exterior domain (TT:1401, TT:2844–2850). -/
theorem wp_harmonicOfA2_sub (φ ψ : A2 unitDisc) :
    EqOn (wp_harmonicOfA2 (φ - ψ)) (wp_harmonicOfA2 φ - wp_harmonicOfA2 ψ) unitDiscExterior := by
  intro w hw
  have hwi := (resolvent_inv_exterior_conformal.mapsTo hw).1
  have he := A2.toFun_sub (D := unitDisc) isOpen_ball
    (fun z hz => (mem_ball_zero_iff.mp hz).ne) φ ψ hwi
  simp only [wp_harmonicOfA2, wp_harmonicOfDisk, he, Pi.sub_apply, sub_div, map_sub, mul_sub]

/-- Harmonic contraction conjugates complex scalar coefficients (TT:1401, TT:2844–2850). -/
theorem wp_harmonicOfA2_smul (c : ℂ) (φ : A2 unitDisc) :
    EqOn (wp_harmonicOfA2 (c • φ)) (conj c • wp_harmonicOfA2 φ) unitDiscExterior := by
  intro w hw
  have hwi := (resolvent_inv_exterior_conformal.mapsTo hw).1
  have he := A2.toFun_smul (D := unitDisc) isOpen_ball
    (fun z hz => (mem_ball_zero_iff.mp hz).ne) c φ hwi
  simp only [wp_harmonicOfA2, wp_harmonicOfDisk, he, Pi.smul_apply, smul_eq_mul,
    mul_div_assoc, map_mul]
  ring

/-- Finite sums transport pointwise to the exterior harmonic model (TT:2844–2850). -/
theorem wp_harmonicOfA2_sum {ι : Type*} (s : Finset ι) (φ : ι → A2 unitDisc) :
    EqOn (wp_harmonicOfA2 (∑ i ∈ s, φ i)) (fun w => ∑ i ∈ s, wp_harmonicOfA2 (φ i) w)
      unitDiscExterior := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro w hw
    simpa only [Finset.sum_empty, Pi.zero_apply] using wp_harmonicOfA2_zero hw
  | @insert i s hi ih =>
    intro w hw
    dsimp only
    rw [Finset.sum_insert hi, wp_harmonicOfA2_add _ _ hw, Pi.add_apply,
      ih hw]
    dsimp only
    rw [Finset.sum_insert hi]

/-- Differences of harmonic images have the exact A2 Hilbert norm (TT:2844–2850). -/
theorem wp_harmonicOfA2_norm_sub (φ ψ : A2 unitDisc) :
    normL2 unitDiscExterior (wp_harmonicOfA2 φ - wp_harmonicOfA2 ψ) = (‖φ - ψ‖₊ : ℝ≥0∞) := by
  rw [← wp_normL2_congr wp_exterior_isOpen.measurableSet (wp_harmonicOfA2_sub φ ψ),
    wp_harmonicOfA2_norm]

/-- Harmonic contraction exchanges the two inner-product conventions (TT:1401, TT:2844–2850). -/
theorem wp_harmonicOfA2_inner (φ ψ : A2 unitDisc) :
    wpInner (wp_harmonicOfA2 φ) (wp_harmonicOfA2 ψ) = inner ℂ φ ψ := by
  let p : ℂ → ℂ := fun w => A2.toFun φ w⁻¹ / w ^ 4
  let q : ℂ → ℂ := fun w => A2.toFun ψ w⁻¹ / w ^ 4
  unfold wpInner
  calc
    _ = ∫ w in unitDiscExterior, q w * conj (p w) * ((rho w)⁻¹ : ℝ) := by
      apply setIntegral_congr_fun wp_exterior_isOpen.measurableSet
      intro w hw
      have hr : (rho w : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (wp_rho_pos hw).ne'
      simp only [wp_harmonicOfA2, wp_harmonicOfDisk, p, q, map_mul, map_inv₀,
        conj_ofReal, conj_conj, Complex.ofReal_inv]
      field_simp
      <;> ring
    _ = ∫ z in unitDisc \ {0}, (q z⁻¹ / z ^ 4) * conj (p z⁻¹ / z ^ 4) * ((rho z)⁻¹ : ℝ) :=
      (basisMu_inverted_pair_integral q p).symm
    _ = ∫ z in unitDisc, A2.toFun ψ z * conj (A2.toFun φ z) * ((rho z)⁻¹ : ℝ) := by
      calc
        _ = ∫ z in unitDisc \ {0}, A2.toFun ψ z * conj (A2.toFun φ z) * ((rho z)⁻¹ : ℝ) := by
          apply setIntegral_congr_fun (measurableSet_ball.diff (measurableSet_singleton 0))
          intro z hz
          dsimp only [p, q]
          rw [wp_quadratic_inversion_involutive _ hz.2, wp_quadratic_inversion_involutive _ hz.2]
        _ = _ := setIntegral_congr_set (sdiff_null_ae_eq_self (measure_singleton 0))
    _ = _ := (wp_A2_inner_integral φ ψ).symm

/-- Every harmonic exterior L2 function is represented by an actual disk A2 element (TT:1401). -/
theorem wp_harmonicOfA2_surjective {μ : ℂ → ℂ} (hμ : μ ∈ harmonicL2 unitDiscExterior) :
    ∃ φ : A2 unitDisc, EqOn μ (wp_harmonicOfA2 φ) unitDiscExterior := by
  obtain ⟨f, hf, he, _⟩ := wp_harmonic_disk_representative hμ
  refine ⟨toA2 unitDisc f, ?_⟩
  intro w hw
  rw [he hw]
  have hwi := (resolvent_inv_exterior_conformal.mapsTo hw).1
  simp only [wp_harmonicOfA2, wp_harmonicOfDisk,
    toA2_spec (D := unitDisc) isOpen_ball (fun z hz => (mem_ball_zero_iff.mp hz).ne) hf hwi]

/-- The disk and exterior normalization constants agree after harmonic contraction (TT:2844). -/
theorem wp_A2_basis_factor (n : ℕ) :
    Real.sqrt (2 * (((n : ℝ) + 1) * ((n : ℝ) + 2) * ((n : ℝ) + 3)) / π) =
      4 * Real.sqrt ((((n + 2 : ℕ) : ℝ) ^ 3 - ((n + 2 : ℕ) : ℝ)) / (8 * π)) := by
  have he : 2 * (((n : ℝ) + 1) * ((n : ℝ) + 2) * ((n : ℝ) + 3)) / π =
      16 * ((((n + 2 : ℕ) : ℝ) ^ 3 - ((n + 2 : ℕ) : ℝ)) / (8 * π)) := by
    push_cast
    ring
  rw [he, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 16)]
  norm_num

/-- The normalized disk Hilbert basis maps to the memoir's harmonic basis with its sign (TT:2844). -/
theorem wp_harmonicOfA2_basis (n : ℕ) :
    EqOn (wp_harmonicOfA2 (wp_A2_basisVector n)) (fun w => -basisMu (n + 2) w) unitDiscExterior := by
  intro w hw
  have hw0 := resolvent_exterior_ne_zero hw
  have hwi := (resolvent_inv_exterior_conformal.mapsTo hw).1
  have he : A2.toFun (wp_A2_basisVector n) w⁻¹ =
      (Real.sqrt (2 * (((n : ℝ) + 1) * ((n : ℝ) + 2) * ((n : ℝ) + 3)) / π) : ℂ) * w⁻¹ ^ n := by
    unfold wp_A2_basisVector
    rw [A2.toFun_smul (D := unitDisc) isOpen_ball (fun z hz => (mem_ball_zero_iff.mp hz).ne) _ _ hwi]
    simp only [Pi.smul_apply, smul_eq_mul, wp_A2_monomial_toFun n hwi]
  rw [wp_A2_basis_factor] at he
  have hp : w⁻¹ ^ n / w ^ 4 = w ^ (-(n : ℤ) - 4) := by
    rw [show -(n : ℤ) - 4 = -((n + 4 : ℕ) : ℤ) by push_cast; ring]
    simp only [zpow_neg, zpow_natCast, pow_add, inv_pow, mul_inv_rev, div_eq_mul_inv]
    ring
  have hn : -((n + 2 : ℕ) : ℤ) - 2 = -(n : ℤ) - 4 := by push_cast; ring
  simp only [wp_harmonicOfA2, wp_harmonicOfDisk, he, mul_div_assoc, hp, map_mul,
    conj_ofReal, map_zpow₀, basisMu, hn,
    rho, Complex.ofReal_div, inv_div, Complex.ofReal_ofNat, Complex.ofReal_mul, map_ofNat]
  ring

/-- The WP coefficients are the negative conjugates of the disk Hilbert coefficients (TT:2844–2850). -/
theorem wp_harmonicOfA2_basis_coefficient (φ : A2 unitDisc) (n : ℕ) :
    wpInner (wp_harmonicOfA2 φ) (basisMu (n + 2)) =
      -conj (inner ℂ (wp_A2_basisVector n) φ) := by
  calc
    _ = -wpInner (wp_harmonicOfA2 φ) (wp_harmonicOfA2 (wp_A2_basisVector n)) := by
      unfold wpInner
      rw [← integral_neg]
      apply setIntegral_congr_fun wp_exterior_isOpen.measurableSet
      intro w hw
      have he : basisMu (n + 2) w = -wp_harmonicOfA2 (wp_A2_basisVector n) w := by
        rw [wp_harmonicOfA2_basis n hw, neg_neg]
      dsimp only
      rw [he, map_neg]
      ring
    _ = -inner ℂ φ (wp_A2_basisVector n) := by rw [wp_harmonicOfA2_inner]
    _ = _ := by
      change -inner ℂ (φ : Lp ℂ 2 (rhoInvMeasure unitDisc))
        (wp_A2_basisVector n : Lp ℂ 2 (rhoInvMeasure unitDisc)) =
        -conj (inner ℂ (wp_A2_basisVector n : Lp ℂ 2 (rhoInvMeasure unitDisc))
          (φ : Lp ℂ 2 (rhoInvMeasure unitDisc)))
      rw [inner_conj_symm]

/-- Finite Hilbert projections transport to the stated WP coefficient sums (TT:2844–2850). -/
theorem wp_harmonicOfA2_projection (φ : A2 unitDisc) (s : Finset ℕ) :
    EqOn (wp_harmonicOfA2 (∑ k ∈ s, inner ℂ (wp_A2_basisVector k) φ • wp_A2_basisVector k))
      (fun w => ∑ k ∈ s, wpInner (wp_harmonicOfA2 φ) (basisMu (k + 2)) * basisMu (k + 2) w)
      unitDiscExterior := by
  intro w hw
  rw [wp_harmonicOfA2_sum s _ hw]
  apply Finset.sum_congr rfl
  intro k _
  rw [wp_harmonicOfA2_smul _ _ hw, Pi.smul_apply, smul_eq_mul,
    wp_harmonicOfA2_basis k hw, wp_harmonicOfA2_basis_coefficient]
  ring

/-- The finite WP expansion error has the exact disk Hilbert error norm (TT:2844–2850). -/
theorem wp_harmonicOfA2_projection_error (φ : A2 unitDisc) (s : Finset ℕ) :
    normL2 unitDiscExterior (fun w => wp_harmonicOfA2 φ w -
      ∑ k ∈ s, wpInner (wp_harmonicOfA2 φ) (basisMu (k + 2)) * basisMu (k + 2) w) =
      (‖φ - ∑ k ∈ s, inner ℂ (wp_A2_basisVector k) φ • wp_A2_basisVector k‖₊ : ℝ≥0∞) := by
  rw [← wp_harmonicOfA2_norm_sub]
  apply wp_normL2_congr wp_exterior_isOpen.measurableSet
  intro w hw
  dsimp only [Pi.sub_apply]
  rw [wp_harmonicOfA2_projection φ s hw]

/-- Range-indexed WP expansions converge for harmonic images of disk A2 elements (TT:2844–2850). -/
theorem wp_harmonicOfA2_expansion (φ : A2 unitDisc) :
    Tendsto (fun N : ℕ => normL2 unitDiscExterior (fun w => wp_harmonicOfA2 φ w -
      ∑ k ∈ Finset.range N, wpInner (wp_harmonicOfA2 φ) (basisMu (k + 2)) * basisMu (k + 2) w))
      atTop (𝓝 0) := by
  have hs := (wp_A2_basis_expansion φ).tendsto_sum_nat
  have ht : Tendsto (fun N : ℕ => ‖φ - ∑ k ∈ Finset.range N,
      inner ℂ (wp_A2_basisVector k) φ • wp_A2_basisVector k‖) atTop (𝓝 0) := by
    have hc : Tendsto (fun _ : ℕ => φ) atTop (𝓝 φ) := tendsto_const_nhds
    simpa only [sub_self, norm_zero] using (hc.sub hs).norm
  have hE := (ENNReal.continuous_ofReal.tendsto (0 : ℝ)).comp ht
  simpa only [wp_harmonicOfA2_projection_error, Function.comp_def, ENNReal.ofReal_zero, ofReal_norm,
    enorm_eq_nnnorm] using hE

/-- Range-indexed WP expansions converge for every harmonic exterior L2 representative (TT:2844–2850). -/
theorem basisMu_expansion_range {μ : ℂ → ℂ} (hμ : μ ∈ harmonicL2 unitDiscExterior) :
    Tendsto (fun N : ℕ => normL2 unitDiscExterior (fun w => μ w -
      ∑ k ∈ Finset.range N, wpInner μ (basisMu (k + 2)) * basisMu (k + 2) w)) atTop (𝓝 0) := by
  obtain ⟨φ, he⟩ := wp_harmonicOfA2_surjective hμ
  have hc (k : ℕ) : wpInner μ (basisMu (k + 2)) =
      wpInner (wp_harmonicOfA2 φ) (basisMu (k + 2)) := by
    unfold wpInner
    apply setIntegral_congr_fun wp_exterior_isOpen.measurableSet
    intro w hw
    dsimp only
    rw [he hw]
  have hn (N : ℕ) : normL2 unitDiscExterior (fun w => μ w -
      ∑ k ∈ Finset.range N, wpInner μ (basisMu (k + 2)) * basisMu (k + 2) w) =
      normL2 unitDiscExterior (fun w => wp_harmonicOfA2 φ w -
        ∑ k ∈ Finset.range N, wpInner (wp_harmonicOfA2 φ) (basisMu (k + 2)) * basisMu (k + 2) w) := by
    apply wp_normL2_congr wp_exterior_isOpen.measurableSet
    intro w hw
    simp only [he hw, hc]
  simpa only [hn] using wp_harmonicOfA2_expansion φ

/-- The exact finite-interval-indexed completeness clause for the memoir's WP basis (TT:2844–2850). -/
theorem basisMu_expansion {μ : ℂ → ℂ} (hμ : μ ∈ harmonicL2 unitDiscExterior) :
    Tendsto (fun N : ℕ => normL2 unitDiscExterior
      (fun z => μ z - ∑ n ∈ Finset.Icc 2 N, wpInner μ (basisMu n) * basisMu n z)) atTop (𝓝 0) := by
  have he (N : ℕ) (z : ℂ) : (∑ n ∈ Finset.Icc 2 N, wpInner μ (basisMu n) * basisMu n z) =
      ∑ k ∈ Finset.range (N - 1), wpInner μ (basisMu (k + 2)) * basisMu (k + 2) z := by
    have hset : Finset.Icc 2 N = Finset.Ico 2 (N + 1) := by
      ext n
      simp only [Finset.mem_Icc, Finset.mem_Ico]
      omega
    rw [hset, Finset.sum_Ico_eq_sum_range]
    rw [show N + 1 - 2 = N - 1 by omega]
    simp only [Nat.add_comm 2]
  simp_rw [he]
  exact (basisMu_expansion_range hμ).comp (tendsto_sub_atTop_nat 1)

/-- Conjugate reflection preserves the disk quadratic norm (TT:2844–2850). -/
theorem wp_normA2_conj_reflect (f : ℂ → ℂ) :
    normA2 unitDisc (fun z => conj (f (conj z))) = normA2 unitDisc f := by
  have hs : (Complex.conjLIE : ℂ → ℂ) ⁻¹' unitDisc = unitDisc := by
    ext z
    simp [unitDisc, Complex.conjLIE_apply]
  unfold normA2
  congr 1
  have h := Complex.conjLIE.measurePreserving.setLIntegral_comp_preimage_emb
    Complex.conjLIE.toHomeomorph.measurableEmbedding
    (fun z : ℂ => (‖f z‖₊ : ℝ≥0∞) ^ 2 * ENNReal.ofReal ((rho z)⁻¹)) unitDisc
  have hn (z : ℂ) : ‖conj z‖₊ = ‖z‖₊ := Subtype.ext (Complex.norm_conj z)
  simpa only [hs, Function.comp_def, Complex.conjLIE_apply, hn,
    rho, Complex.norm_conj] using h

/-- Conjugate reflection preserves holomorphic disk L2 functions (TT:2844–2850). -/
theorem wp_A2_conj_reflect {f : ℂ → ℂ} (hf : f ∈ A2fun unitDisc) :
    (fun z => conj (f (conj z))) ∈ A2fun unitDisc := by
  refine ⟨?_, by rw [wp_normA2_conj_reflect]; exact hf.2⟩
  intro z hz
  have hc : conj z ∈ unitDisc := by simpa [unitDisc, mem_ball_zero_iff] using hz
  have h := (hf.1.differentiableAt (isOpen_ball.mem_nhds hc)).conj_conj
  simpa only [Function.comp_def, conj_conj] using h.differentiableWithinAt


/-- The explicit inverse Bers map recovers the harmonic disk representative (TT:498–501, TT:2844). -/
theorem wp_bers_of_harmonic_disk {μ f : ℂ → ℂ}
    (hμ : μ ∈ harmonicL2 unitDiscExterior) (hf : f ∈ A2fun unitDisc)
    (he : EqOn μ (wp_harmonicOfDisk f) unitDiscExterior) :
    EqOn (AInf.toFun (fderiv ℂ bersPhi 0 (toLinf μ)))
      (fun z => -(1 / 2 : ℂ) * conj (f (conj z))) unitDisc := by
  let g : ℂ → ℂ := fun z => -(1 / 2 : ℂ) * conj (f (conj z))
  have hg : g ∈ A2fun unitDisc := by
    refine ⟨(wp_A2_conj_reflect hf).1.const_mul _, ?_⟩
    dsimp [g]
    rw [normA2_const_mul, wp_normA2_conj_reflect]
    exact ENNReal.mul_lt_top ENNReal.coe_lt_top hf.2
  let φ := A2toAInf (toA2 unitDisc g)
  have hφ : EqOn (AInf.toFun φ) g unitDisc := by
    intro z hz
    exact ((A2toAInf_bounded.2 (toA2 unitDisc g)).2 z hz).trans
      (toA2_spec isOpen_ball (fun z hz => ne_of_lt (mem_ball_zero_iff.mp hz)) hg hz)
  have hΛ : Lambda φ = toLinf μ := by
    apply Lp.ext
    filter_upwards [Lambda_coe_ae φ, wp_harmonic_toLinf_ae hμ,
      ae_restrict_mem wp_exterior_isOpen.measurableSet] with w hL hM hw
    rw [hL, hM, he hw, hφ ((refl_mem_disc_iff (resolvent_exterior_ne_zero hw)).mpr hw)]
    dsimp [g, wp_harmonicOfDisk, refl]
    simp only [map_inv₀, conj_conj, map_div₀, map_pow]
    simp only [rho, Complex.ofReal_div, Complex.ofReal_ofNat, inv_div]
    push_cast
    ring
  rw [← hΛ, lambda_inverse_D0bers.2.1]
  exact hφ

/-- The differential of the Bers embedding scales the harmonic L2 norm by one half (TT:2844–2850). -/
theorem wp_bers_harmonic_norm {μ : ℂ → ℂ} (hμ : μ ∈ harmonicL2 unitDiscExterior) :
    normL2 unitDiscExterior μ =
      2 * normA2 unitDisc (AInf.toFun (fderiv ℂ bersPhi 0 (toLinf μ))) := by
  obtain ⟨f, hf, he, hn⟩ := wp_harmonic_disk_representative hμ
  rw [normA2_congr (D := unitDisc) measurableSet_ball (wp_bers_of_harmonic_disk hμ hf he),
    normA2_const_mul, wp_normA2_conj_reflect, ← hn, ← mul_assoc]
  norm_num [nnnorm_neg, nnnorm_div, ENNReal.coe_inv, ENNReal.mul_inv_cancel]

/-- (TT:2844–2850) `{μ_n}_{n ≥ 2}` is an orthonormal basis of `H^{-1,1}(𝔻*)`:
- each `μ_n` lies in `H^{-1,1}(𝔻*)`;
- `⟨μ_m, μ_n⟩_WP = δ_{mn}`;
- every `μ ∈ H^{-1,1}(𝔻*)` is the `L²`-sum `Σ ⟨μ, μ_n⟩ μ_n`.

Moreover `‖μ‖₂ = 2‖D₀β(μ)‖₂`. -/
theorem basisMu_orthonormal :
    (∀ n ≥ 2, basisMu n ∈ harmonicL2 unitDiscExterior) ∧
      (∀ m ≥ 2, ∀ n ≥ 2, wpInner (basisMu m) (basisMu n) = if m = n then 1 else 0) ∧
      (∀ μ ∈ harmonicL2 unitDiscExterior, Tendsto (fun N : ℕ => normL2 unitDiscExterior
        (fun z => μ z - ∑ n ∈ Finset.Icc 2 N, wpInner μ (basisMu n) * basisMu n z)) atTop (𝓝 0)) ∧
      ∀ μ ∈ harmonicL2 unitDiscExterior,
        normL2 unitDiscExterior μ = 2 * normA2 unitDisc (AInf.toFun (fderiv ℂ bersPhi 0 (toLinf μ))) := by
  refine ⟨?_, fun _ hm _ hn => basisMu_wpInner hm hn,
    fun _ hμ => basisMu_expansion hμ, fun _ hμ => wp_bers_harmonic_norm hμ⟩
  intro n hn
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  simpa only [Nat.add_comm] using basisMu_mem_harmonicL2 k

-- `thm_7_11` moved to `TakhtajanTeo.Ch1.S7Thm711` (2026-10-29, Program G).

-- `cor_7_12` moved to `TakhtajanTeo.Ch1.S7Thm711` (2026-10-29, Program G).

/-- **(7.9)** (TT:3117). The numerator `R = R_{μν̄νμ̄} + R_{νμ̄μν̄} - R_{μν̄μν̄} - R_{νμ̄νμ̄}` of the sectional curvature of
the plane spanned by the real vectors `∂/∂t_μ`, `∂/∂t_ν`. -/
def sectionalNum (μ ν : ℂ → ℂ) : ℂ :=
  riemannR μ ν ν μ + riemannR ν μ μ ν - riemannR μ ν μ ν - riemannR ν μ ν μ

/-- (TT:3121) The denominator `g = 4 g_{μμ̄} g_{νν̄} - 2|g_{μν̄}|² - 2 Re (g_{μν̄})²`. -/
def sectionalDen (μ ν : ℂ → ℂ) : ℝ :=
  4 * (wpInner μ μ).re * (wpInner ν ν).re - 2 * ‖wpInner μ ν‖ ^ 2 - 2 * ((wpInner μ ν) ^ 2).re

/-- The denominator in (7.9) is four times the real Gram determinant (TT:3121). -/
theorem sectionalDen_eq_gram (μ ν : ℂ → ℂ) :
    sectionalDen μ ν = 4 * ((wpInner μ μ).re * (wpInner ν ν).re - (wpInner μ ν).re ^ 2) := by
  have hn : ‖wpInner μ ν‖ ^ 2 = (wpInner μ ν).re ^ 2 + (wpInner μ ν).im ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    ring
  have hr : ((wpInner μ ν) ^ 2).re = (wpInner μ ν).re ^ 2 - (wpInner μ ν).im ^ 2 := by
    simp only [pow_two, Complex.mul_re]
  unfold sectionalDen
  rw [hn, hr]
  ring

/-- Strict positivity of the real Gram determinant used in (7.9) (TT:3121).
Independence is required in the inner product space itself. -/
theorem wp_real_gram_pos {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {x y : E} (hli : LinearIndependent ℝ ![x, y]) :
    0 < ‖x‖ ^ 2 * ‖y‖ ^ 2 - (inner ℝ y x) ^ 2 := by
  have hp := linearIndependent_fin2.mp hli
  change y ≠ 0 ∧ ∀ a : ℝ, a • y ≠ x at hp
  have hx : x ≠ 0 := by
    intro h
    exact hp.2 0 (by simp [h])
  have hlt : ‖inner ℝ y x‖ < ‖y‖ * ‖x‖ := by
    refine lt_of_le_of_ne (norm_inner_le_norm (𝕜 := ℝ) y x) ?_
    intro heq
    obtain ⟨a, _, ha⟩ := (norm_inner_eq_norm_iff (𝕜 := ℝ) hp.1 hx).mp heq
    exact hp.2 a ha.symm
  have hs := (sq_lt_sq₀ (norm_nonneg (inner ℝ y x))
    (mul_nonneg (norm_nonneg y) (norm_nonneg x))).mpr hlt
  simp only [Real.norm_eq_abs, sq_abs, mul_pow] at hs
  nlinarith

/-- Positivity of the sectional denominator for independent L2 tangent vectors,
the intrinsic independence condition in Theorem 7.14 (TT:3121–3128). -/
theorem sectionalDen_pos_of_L2_linearIndependent {μ ν : ℂ → ℂ}
    (hμ : μ ∈ harmonicL2 unitDiscExterior) (hν : ν ∈ harmonicL2 unitDiscExterior)
    (hli : LinearIndependent ℝ
      ![(wp_weighted_memLp hμ).toLp (fun z => μ z * (Real.sqrt (rho z) : ℂ)),
        (wp_weighted_memLp hν).toLp (fun z => ν z * (Real.sqrt (rho z) : ℂ))]) :
    0 < sectionalDen μ ν := by
  let f := (wp_weighted_memLp hμ).toLp (fun z => μ z * (Real.sqrt (rho z) : ℂ))
  let g := (wp_weighted_memLp hν).toLp (fun z => ν z * (Real.sqrt (rho z) : ℂ))
  let : Inner ℝ (Lp ℂ 2 (volume.restrict unitDiscExterior)) :=
    Inner.rclikeToReal ℂ _
  let : InnerProductSpace ℝ (Lp ℂ 2 (volume.restrict unitDiscExterior)) :=
    InnerProductSpace.rclikeToReal ℂ _
  have hg : 0 < ‖f‖ ^ 2 * ‖g‖ ^ 2 - (inner ℝ g f) ^ 2 := wp_real_gram_pos hli
  have hff : ‖f‖ ^ 2 = (wpInner μ μ).re := by
    exact (norm_sq_eq_re_inner (𝕜 := ℂ) f).trans
      (congrArg Complex.re (wpInner_eq_L2_inner hμ hμ))
  have hgg : ‖g‖ ^ 2 = (wpInner ν ν).re := by
    exact (norm_sq_eq_re_inner (𝕜 := ℂ) g).trans
      (congrArg Complex.re (wpInner_eq_L2_inner hν hν))
  have hgf : inner ℝ g f = (wpInner μ ν).re := by
    exact congrArg Complex.re (wpInner_eq_L2_inner hμ hν)
  rw [hff, hgg, hgf] at hg
  rw [sectionalDen_eq_gram]
  exact mul_pos (by norm_num) hg

/-- The sectional denominator is positive for independent harmonic representatives
on the exterior disk, the minimal corrected independence condition for Theorem 7.14
(TT:3121–3128). This does not assert negativity of the curvature numerator. -/
theorem sectionalDen_pos_of_restriction_linearIndependent {μ ν : ℂ → ℂ}
    (hμ : μ ∈ harmonicL2 unitDiscExterior) (hν : ν ∈ harmonicL2 unitDiscExterior)
    (hli : LinearIndependent ℝ
      ![(fun z : unitDiscExterior => μ z), (fun z : unitDiscExterior => ν z)]) :
    0 < sectionalDen μ ν := by
  exact sectionalDen_pos_of_L2_linearIndependent hμ hν
    ((wp_weighted_linearIndependent_iff hμ hν).mpr hli)

/-- The resolvent of real data is the complex coercion of a real integral,
in either disk model used in the curvature argument (TT:3128–3156). -/
theorem wp_resolvent_ofReal (D : Set ℂ) (f : ℂ → ℝ) (z : ℂ) :
    resolventOp D (fun w => (f w : ℂ)) z =
      Complex.ofReal (∫ w in D, resolventKernel z w * f w * rho w) := by
  unfold resolventOp
  simp only [← Complex.ofReal_mul, integral_complex_ofReal]

/-- Real weighted integrability for bounded continuous input in either disk
model, prior to the strict positivity argument (TT:3128–3156). -/
theorem wp_resolvent_real_integrable {D : Set ℂ} (hD : D = unitDisc ∨ D = unitDiscExterior)
    {f : ℂ → ℝ} (hf : ContinuousOn f D) {C : ℝ} (hb : ∀ w ∈ D, |f w| ≤ C)
    {z : ℂ} (hz : z ∈ D) : IntegrableOn (fun w => resolventKernel z w * f w * rho w) D := by
  have hc := Complex.continuous_ofReal.comp_continuousOn hf
  have hbc : ∀ w ∈ D, ‖(f w : ℂ)‖ ≤ C := by
    simpa only [Complex.norm_real, Real.norm_eq_abs] using hb
  have hi := resolvent_integrand_integrable_of_bounded hD
    (hc.aestronglyMeasurable (resolvent_domain_isOpen hD).measurableSet) hbc hz
  have hi' : IntegrableOn (fun w => ((resolventKernel z w * f w * rho w : ℝ) : ℂ)) D := by
    simpa only [IntegrableOn, Function.comp_def, Complex.ofReal_mul] using hi
  exact (IntegrableOn.iff_ofReal (𝕜 := ℂ)).mpr hi'

/-- Strict positivity of the disk/exterior resolvent on nonzero nonnegative
continuous bounded input, with the kernel diagonal removed as a null singleton.
This is a positivity prerequisite for Theorem 7.14, not a curvature formula
(TT:3128–3156). -/
theorem wp_resolvent_real_pos {D : Set ℂ} (hD : D = unitDisc ∨ D = unitDiscExterior)
    {f : ℂ → ℝ} (hf : ContinuousOn f D) (hn : ∀ w ∈ D, 0 ≤ f w)
    {C : ℝ} (hb : ∀ w ∈ D, |f w| ≤ C) (hp : ∃ w ∈ D, 0 < f w)
    {z : ℂ} (hz : z ∈ D) : 0 < (resolventOp D (fun w => (f w : ℂ)) z).re := by
  rw [wp_resolvent_ofReal, Complex.ofReal_re]
  have hnint : ∀ᵐ w ∂(volume.restrict D), 0 ≤ resolventKernel z w * f w * rho w := by
    filter_upwards [resolvent_mass_nonneg_ae hD hz,
      ae_restrict_mem (resolvent_domain_isOpen hD).measurableSet] with w hw hwD
    simpa only [mul_assoc, mul_left_comm, mul_comm] using mul_nonneg hw (hn w hwD)
  apply (setIntegral_pos_iff_support_of_nonneg_ae hnint
    (wp_resolvent_real_integrable hD hf hb hz)).mpr
  have hopen := hf.isOpen_inter_preimage (resolvent_domain_isOpen hD) (isOpen_Ioi (a := (0 : ℝ)))
  obtain ⟨w, hw, hfw⟩ := hp
  have hm : 0 < volume ((D ∩ f ⁻¹' Ioi 0) \ {z}) := by
    rw [measure_sdiff_null (measure_singleton z)]
    exact hopen.measure_pos (μ := volume) ⟨w, hw, hfw⟩
  apply lt_of_lt_of_le hm
  apply measure_mono
  intro w hw
  refine ⟨?_, hw.1.1⟩
  have hzw : w ≠ z := by simpa only [mem_singleton_iff] using hw.2
  have hpair : z ∈ unitDisc ∧ w ∈ unitDisc ∨ z ∈ unitDiscExterior ∧ w ∈ unitDiscExterior := by
    rcases hD with rfl | rfl
    · exact Or.inl ⟨hz, hw.1.1⟩
    · exact Or.inr ⟨hz, hw.1.1⟩
  have hnorm : ‖w‖ ≠ 1 := by
    rcases hD with rfl | rfl
    · exact ne_of_lt (mem_ball_zero_iff.mp hw.1.1)
    · exact ne_of_gt hw.1.1
  change resolventKernel z w * f w * rho w ≠ 0
  exact (mul_pos (mul_pos (RK2 hzw.symm hpair) hw.1.2) (rho_pos_of_norm_ne_one hnorm)).ne'

/-- The positive-resolvent prerequisite of Theorem 7.14 for a bounded nonzero
harmonic L2 representative. The uniform bound is explicit until the full exterior
H-to-Omega estimate is available (TT:3128–3156). -/
theorem wp_harmonic_resolvent_sq_pos_of_bounded {μ : ℂ → ℂ}
    (hμ : μ ∈ harmonicL2 unitDiscExterior) {C : ℝ}
    (hb : ∀ w ∈ unitDiscExterior, ‖μ w‖ ≤ C)
    (hne : ∃ w ∈ unitDiscExterior, μ w ≠ 0) {z : ℂ} (hz : z ∈ unitDiscExterior) :
    0 < (resolventStar (fun w => (‖μ w‖ ^ 2 : ℝ)) z).re := by
  apply wp_resolvent_real_pos (Or.inr rfl) ((wp_harmonic_continuousOn hμ).norm.pow 2)
    (fun _ _ => sq_nonneg _) (C := C ^ 2) _ _ hz
  · intro w hw
    rw [abs_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (norm_nonneg _) (hb w hw) 2
  · obtain ⟨w, hw, hmw⟩ := hne
    exact ⟨w, hw, sq_pos_of_pos (norm_pos_iff.mpr hmw)⟩

/-- Strict positivity of the resolvent energy for nonnegative, nonzero, continuous
bounded data with finite weighted L1 mass. This does not assert positivity for
sign-changing data, which needs the separate elliptic argument (TT:3128–3156). -/
theorem wp_resolvent_energy_pos {D : Set ℂ} (hD : D = unitDisc ∨ D = unitDiscExterior)
    {f : ℂ → ℝ} (hf : ContinuousOn f D) (hn : ∀ w ∈ D, 0 ≤ f w)
    {C : ℝ} (hb : ∀ w ∈ D, |f w| ≤ C) (hp : ∃ w ∈ D, 0 < f w)
    (hi : IntegrableOn (fun w => f w * rho w) D) :
    0 < ∫ w in D, f w * (resolventOp D (fun v => (f v : ℂ)) w).re * rho w := by
  let g : ℂ → ℝ := fun w => (resolventOp D (fun v => (f v : ℂ)) w).re
  have hfc := Complex.continuous_ofReal.comp_continuousOn hf
  have hbc : ∀ w ∈ D, ‖(f w : ℂ)‖ ≤ C := by
    simpa only [Complex.norm_real, Real.norm_eq_abs] using hb
  have hgc : ContinuousOn g D := Complex.continuous_re.comp_continuousOn
    (resolventOp_continuousOn_of_bounded hD
      (hfc.aestronglyMeasurable (resolvent_domain_isOpen hD).measurableSet) hbc)
  have hgb : ∀ w ∈ D, ‖g w‖ ≤ C := by
    intro w hw
    change |(resolventOp D (fun v => (f v : ℂ)) w).re| ≤ C
    exact (Complex.abs_re_le_norm _).trans (resolventOp_norm_le hD hbc hw)
  have hgpos : ∀ w ∈ D, 0 < g w := fun w hw => wp_resolvent_real_pos hD hf hn hb hp hw
  have hbound : ∀ᵐ w ∂(volume.restrict D), ‖g w‖ ≤ C := by
    filter_upwards [ae_restrict_mem (resolvent_domain_isOpen hD).measurableSet] with w hw
    exact hgb w hw
  have hi' : Integrable (fun w => f w * rho w) (volume.restrict D) := hi
  have henergy : IntegrableOn (fun w => f w * g w * rho w) D := by
    apply (hi'.mul_bdd (hgc.aestronglyMeasurable (resolvent_domain_isOpen hD).measurableSet)
      hbound).congr
    filter_upwards with w
    ring
  have hnonneg : ∀ᵐ w ∂(volume.restrict D), 0 ≤ f w * g w * rho w := by
    filter_upwards [ae_restrict_mem (resolvent_domain_isOpen hD).measurableSet] with w hw
    exact mul_nonneg (mul_nonneg (hn w hw) (hgpos w hw).le) (wp_rho_nonneg w)
  apply (setIntegral_pos_iff_support_of_nonneg_ae hnonneg henergy).mpr
  have hopen := hf.isOpen_inter_preimage (resolvent_domain_isOpen hD) (isOpen_Ioi (a := (0 : ℝ)))
  obtain ⟨w, hw, hfw⟩ := hp
  have hm : 0 < volume (D ∩ f ⁻¹' Ioi 0) := hopen.measure_pos (μ := volume) ⟨w, hw, hfw⟩
  apply lt_of_lt_of_le hm
  apply measure_mono
  intro w hw
  refine ⟨?_, hw.1⟩
  have hnorm : ‖w‖ ≠ 1 := by
    rcases hD with rfl | rfl
    · exact ne_of_lt (mem_ball_zero_iff.mp hw.1)
    · exact ne_of_gt hw.1
  change f w * g w * rho w ≠ 0
  exact (mul_pos (mul_pos hw.2 (hgpos w hw.1)) (rho_pos_of_norm_ne_one hnorm)).ne'

/-- The positive nonnegative-input resolvent energy used in the holomorphic
sectional-curvature argument, for a bounded nonzero harmonic L2 representative.
The boundedness hypothesis remains explicit (TT:3128–3156). -/
theorem wp_harmonic_resolvent_energy_pos_of_bounded {μ : ℂ → ℂ}
    (hμ : μ ∈ harmonicL2 unitDiscExterior) {C : ℝ}
    (hb : ∀ w ∈ unitDiscExterior, ‖μ w‖ ≤ C)
    (hne : ∃ w ∈ unitDiscExterior, μ w ≠ 0) :
    0 < (l2Inner (fun w => (‖μ w‖ ^ 2 : ℝ))
      (resolventStar (fun w => (‖μ w‖ ^ 2 : ℝ)))).re := by
  let f : ℂ → ℝ := fun w => ‖μ w‖ ^ 2
  have hbound : ∀ w ∈ unitDiscExterior, |f w| ≤ C ^ 2 := by
    intro w hw
    change |‖μ w‖ ^ 2| ≤ C ^ 2
    rw [abs_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (norm_nonneg _) (hb w hw) 2
  have hp : ∃ w ∈ unitDiscExterior, 0 < f w := by
    obtain ⟨w, hw, hmw⟩ := hne
    exact ⟨w, hw, sq_pos_of_pos (norm_pos_iff.mpr hmw)⟩
  have he := wp_resolvent_energy_pos (Or.inr rfl)
    ((wp_harmonic_continuousOn hμ).norm.pow 2) (fun _ _ => sq_nonneg _)
    hbound hp (wp_integrable_sq hμ)
  have heq : l2Inner (fun w => (f w : ℂ)) (resolventStar (fun w => (f w : ℂ))) =
      Complex.ofReal (∫ w in unitDiscExterior,
        f w * (resolventOp unitDiscExterior (fun v => (f v : ℂ)) w).re * rho w) := by
    unfold l2Inner
    calc
      _ = ∫ w in unitDiscExterior, Complex.ofReal
          (f w * (resolventOp unitDiscExterior (fun v => (f v : ℂ)) w).re * rho w) := by
        apply integral_congr_ae
        filter_upwards with w
        simp only [resolventStar, wp_resolvent_ofReal, Complex.conj_ofReal,
          Complex.ofReal_re, Complex.ofReal_mul]
      _ = _ := integral_complex_ofReal
  change 0 < (l2Inner (fun w => (f w : ℂ)) (resolventStar (fun w => (f w : ℂ)))).re
  rw [heq, Complex.ofReal_re]
  exact he


/-- The resolvent of the squared modulus of a nonzero harmonic L2 representative is positive,
without an additional boundedness hypothesis (TT:3128–3156). -/
theorem wp_harmonic_resolvent_sq_pos {μ : ℂ → ℂ} (hμ : μ ∈ harmonicL2 unitDiscExterior)
    (hne : ∃ w ∈ unitDiscExterior, μ w ≠ 0) {z : ℂ} (hz : z ∈ unitDiscExterior) :
    0 < (resolventStar (fun w => (‖μ w‖ ^ 2 : ℝ)) z).re :=
  wp_harmonic_resolvent_sq_pos_of_bounded hμ (fun _ hw => wp_harmonic_pointwise_bound hμ hw) hne hz

/-- Positive squared-modulus resolvent energy for a nonzero harmonic L2 representative,
without an additional boundedness hypothesis (TT:3128–3156). -/
theorem wp_harmonic_resolvent_energy_pos {μ : ℂ → ℂ} (hμ : μ ∈ harmonicL2 unitDiscExterior)
    (hne : ∃ w ∈ unitDiscExterior, μ w ≠ 0) :
    0 < (l2Inner (fun w => (‖μ w‖ ^ 2 : ℝ))
      (resolventStar (fun w => (‖μ w‖ ^ 2 : ℝ)))).re :=
  wp_harmonic_resolvent_energy_pos_of_bounded hμ
    (fun _ hw => wp_harmonic_pointwise_bound hμ hw) hne

-- `thm_7_14` moved to `TakhtajanTeo.Ch1.S7Thm714` (2026-10-29, Program G).

/-- The third-order weighted intermediate in TT:2787 for genuinely C-infinity input.
The explicit ENat order distinguishes smoothness from the analytic bare top order. -/
theorem wp_weighted_dz_bar_core_smooth {f : ℂ → ℂ} (hf : ContDiffOn ℝ (⊤ : ℕ∞) f unitDisc)
    {z : ℂ} (hz : z ∈ unitDisc) :
    (rho z : ℂ)⁻¹ * dz (fun w => (rho w : ℂ) *
      dzbar (fun v => (rho v : ℂ)⁻¹ * dzbar f v) w) z =
        (rho z : ℂ)⁻¹ * dz (dzbar (dzbar f)) z - (1 / 2 : ℂ) * dzbar f z -
          ((1 - z * conj z) * z / 2) * dz (dzbar f) z := by
  exact wp_weighted_dz_bar_core hf hz

/-- A convenience name for the factorization in TT:2787 with genuinely C-infinity
input, after the approved explicit-ENat-infinity correction to the original declaration. -/
theorem laplace_factorization_smooth {f : ℂ → ℂ} (hf : ContDiffOn ℝ (⊤ : ℕ∞) f unitDisc) {z : ℂ} (hz : z ∈ unitDisc) :
    (rho z : ℂ)⁻¹ * dz (fun y => (rho y : ℂ)⁻¹ * dz (fun x => (rho x : ℂ) *
        dzbar (fun s => (rho s : ℂ)⁻¹ * dzbar f s) x) y) z =
      laplace0 (fun y => laplace0 f y + (1 / 2) * f y) z := by
  exact laplace_factorization hf hz

end TakhtajanTeo
