import TakhtajanTeo.Ch2.S3Lemma36
import TakhtajanTeo.Ch2.S2_Thm21

/-! # Remark 3.10 (TT:5206–5248) (Program G, 下属4, prefix `s310_`)

For `[μ] ∈ T₀(1)` and the pair `(f, g) = (𝖿^μ, 𝗀_μ)`, with `u, v, w` as in TT:

* `u = v - 2w` (`s310_uvw_disc`, `s310_uvw_ext`): the Möbius change of `𝒜` under `ι`.
* `K₁v̄₁ + K₂v̄₂ = -u₁` on `𝔻 \ {0}`: Lemma 3.6 in the `(𝖿, 𝗀)` model (`s36l_core`).
* `K₃ū₁ + K₄ū₂ = -v₂` on `𝔻*` (`s310_ext_Ku`): `lemma_3_6` (the `(f̃, g̃)` model) read through `z ↦ 1/z`.
* `K w̄ = w` (`s310_Kw_disc`, `s310_Kw_ext`): the kernels and `w` expanded in the Bergman bases; the coefficient identity
  is the column-`0` case of the generalized Grunsky equality (`s310_col0`, polarization of `thm_2_1` at `e₀ + t e_l`,
  the complement being null by Remark 2.2).
* The remaining identities by linearity (`s310_split`; integrability from `A₂¹` representatives, `s310_int_ae`).
-/

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal ComplexConjugate Classical Real

noncomputable section

namespace TakhtajanTeo.Ch2

open LiZhongQC

/-- Derivative of the inversion conjugate `ι ∘ g ∘ ι` at `1/ζ`. -/
theorem s310_inv_deriv {g : ℂ → ℂ} {ζ : ℂ} (hζ : ζ ≠ 0) (hg : DifferentiableAt ℂ g ζ) (hg0 : g ζ ≠ 0) :
    deriv (fun x => (g x⁻¹)⁻¹) ζ⁻¹ = deriv g ζ * ζ ^ 2 / g ζ ^ 2 := by
  have h1 : HasDerivAt (fun x : ℂ => x⁻¹) (-((ζ⁻¹) ^ 2)⁻¹) ζ⁻¹ := hasDerivAt_inv (inv_ne_zero hζ)
  have h2 : HasDerivAt g (deriv g ζ) ((ζ⁻¹)⁻¹) := by rw [inv_inv]; exact hg.hasDerivAt
  have h3 := (h2.comp ζ⁻¹ h1).inv (by simp only [Function.comp_apply, inv_inv]; exact hg0)
  have h4 : deriv (fun x => (g x⁻¹)⁻¹) ζ⁻¹ = _ := h3.deriv
  rw [h4]
  simp only [Function.comp_apply, inv_inv]
  field_simp

/-- `g̃ = ι ∘ 𝗀 ∘ ι` near every `x ≠ 0` (`gTilde` differs only at `0`). -/
theorem s310_gTilde_ev {μ : LinfStar} {x : ℂ} (hx : x ≠ 0) :
    gTilde μ =ᶠ[𝓝 x] fun y => (gsans μ y⁻¹)⁻¹ := by
  filter_upwards [isOpen_ne.mem_nhds hx] with y hy
  rw [gTilde, if_neg hy, one_div, one_div]

/-- **(P1, disc)** `u₁ = v₁ - 2w₁` on `𝔻 \ {0}`. -/
theorem s310_uvw_disc {μ : LinfStar} (hμ : μ ∈ LinfStarBall) {z : ℂ} (hz : z ∈ unitDisc) (hz0 : z ≠ 0) :
    preSchwarzian (fun ζ => 1 / fsans μ (1 / ζ)) (1 / z) * (-1 / z ^ 2) =
      preSchwarzian (fsans μ) z - 2 * (deriv (fsans μ) z / fsans μ z - 1 / z) := by
  obtain ⟨hfd, hfi, -, -, -, -, -, -, hfne, hfd'⟩ := s2c_facts hμ
  have h := preSchwarzian_inversion (hfd.analyticAt (isOpen_ball.mem_nhds hz)) hz0 (hfne z hz hz0) (hfd' z hz)
  have hfun : (fun ζ => 1 / fsans μ (1 / ζ)) = fun w => (fsans μ w⁻¹)⁻¹ := by
    funext ζ; rw [one_div, one_div]
  rw [hfun, one_div z, h]
  ring

/-- **(P1, exterior)** `u₂ = v₂ - 2w₂` on `𝔻*`. -/
theorem s310_uvw_ext {μ : LinfStar} (hμ : μ ∈ LinfStarBall) {z : ℂ} (hz : z ∈ unitDiscExterior) :
    -(preSchwarzian (fun ζ => 1 / gsans μ (1 / ζ)) (1 / z) * (-1 / z ^ 2)) =
      -preSchwarzian (gsans μ) z - 2 * (-(deriv (gsans μ) z / gsans μ z - 1 / z)) := by
  obtain ⟨-, -, -, -, hgd, hgi, hgne, hgd', -, -⟩ := s2c_facts hμ
  have hEo : IsOpen unitDiscExterior := isOpen_lt continuous_const continuous_norm
  have hz0 : z ≠ 0 := by
    rintro rfl
    have h1 : (1 : ℝ) < ‖(0 : ℂ)‖ := hz
    rw [norm_zero] at h1
    linarith
  have h := preSchwarzian_inversion (hgd.analyticAt (hEo.mem_nhds hz)) hz0 (hgne z hz) (hgd' z hz)
  have hfun : (fun ζ => 1 / gsans μ (1 / ζ)) = fun w => (gsans μ w⁻¹)⁻¹ := by
    funext ζ; rw [one_div, one_div]
  rw [hfun, one_div z, h]
  ring

/-- `∫_{𝔻*} F = ∫_{𝔻 \ {0}} |η|⁻⁴ F(1/η)` (inversion). -/
theorem s310_inv_integral' (F : ℂ → ℂ) :
    ∫ w in unitDiscExterior, F w = ∫ η in unitDisc \ {0}, (‖η‖ ^ 4)⁻¹ • F η⁻¹ := by
  have hEo : IsOpen unitDiscExterior := isOpen_lt continuous_const continuous_norm
  rw [s2c_inv_integral]
  refine setIntegral_congr_fun hEo.measurableSet fun w hw => ?_
  have hw0 : w ≠ 0 := by
    rintro rfl
    have h1 : (1 : ℝ) < ‖(0 : ℂ)‖ := hw
    rw [norm_zero] at h1
    linarith
  have hn : ‖w‖ ^ 4 ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.mpr hw0)
  simp only [inv_inv, norm_inv, inv_pow, smul_smul]
  rw [inv_mul_cancel₀ hn, one_smul]

/-- `∫_𝔻 = ∫_{𝔻 \ {0}}`. -/
theorem s310_disc_punct (F : ℂ → ℂ) : ∫ w in unitDisc, F w = ∫ w in unitDisc \ {0}, F w :=
  setIntegral_congr_set (sdiff_null_ae_eq_self (measure_singleton 0)).symm

/-- `|η|⁴ = η² η̄²`. -/
theorem s310_norm4 (η : ℂ) : ((‖η‖ : ℂ) ^ 4) = η ^ 2 * conj η ^ 2 := by
  have h := Complex.mul_conj' η
  rw [show ((‖η‖ : ℂ)) ^ 4 = ((‖η‖ : ℂ) ^ 2) ^ 2 by ring, ← h]
  ring

/-- **(P4)** `K₃ū₁ + K₄ū₂ = -v₂` on `𝔻*`: Lemma 3.6 (in the `(f̃, g̃)` model) read through the inversion `z ↦ 1/z`. -/
theorem s310_ext_Ku {p : T1} (hp : p ∈ T01) {ζ : ℂ} (hζ : ζ ∈ unitDiscExterior) :
    let μ : LinfStar := (Quotient.out p : LinfStarBall)
    (∫ w in unitDisc, kerK3 (fsans μ) (gsans μ) ζ w *
        conj (preSchwarzian (fun ζ => 1 / fsans μ (1 / ζ)) (1 / w) * (-1 / w ^ 2))) +
      (∫ w in unitDiscExterior, kerK4 (gsans μ) ζ w *
        conj (-(preSchwarzian (fun ζ => 1 / gsans μ (1 / ζ)) (1 / w) * (-1 / w ^ 2)))) =
      preSchwarzian (gsans μ) ζ := by
  intro μ
  have hμ : μ ∈ LinfStarBall := (Quotient.out p).2
  obtain ⟨hfd, hfi, -, -, hgd, hgi, hgne, hgd', hfne, -⟩ := s2c_facts hμ
  have hdisj := (remark_2_2 hμ).1.2.2.2.2.2
  obtain ⟨-, -, -, hgTd, hgTi, hgT0, -⟩ := s2c_gTilde_facts hμ
  have hEo : IsOpen unitDiscExterior := isOpen_lt continuous_const continuous_norm
  have hE0 : ∀ w ∈ unitDiscExterior, w ≠ 0 := fun w hw h => by
    have h1 : (1 : ℝ) < ‖w‖ := hw
    rw [h, norm_zero] at h1
    linarith
  have hζ0 := hE0 ζ hζ
  have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  set z := ζ⁻¹ with hzdef
  have hzD : z ∈ unitDisc := by
    refine mem_ball_zero_iff.mpr ?_
    rw [hzdef, norm_inv]
    exact inv_lt_one_of_one_lt₀ hζ
  have hz0 : z ≠ 0 := inv_ne_zero hζ0
  have hL := lemma_3_6 hp hzD hz0
  dsimp only at hL
  -- facts on `g̃` at `z`
  have hgζd : DifferentiableAt ℂ (gsans μ) ζ := hgd.differentiableAt (hEo.mem_nhds hζ)
  have hevz := s310_gTilde_ev (μ := μ) hz0
  have hgTz : gTilde μ z = (gsans μ ζ)⁻¹ := by
    rw [gTilde, if_neg hz0]; simp only [hzdef, one_div, inv_inv]
  have hgTz' : deriv (gTilde μ) z = deriv (gsans μ) ζ * ζ ^ 2 / gsans μ ζ ^ 2 := by
    rw [hevz.deriv_eq, hzdef]
    exact s310_inv_deriv hζ0 hgζd (hgne ζ hζ)
  -- the left side: `L = -ζ² 𝒜(𝗀)(ζ)`
  have hgTne : gTilde μ z ≠ 0 := by rw [hgTz]; exact inv_ne_zero (hgne ζ hζ)
  have hgTd' : deriv (gTilde μ) z ≠ 0 := deriv_ne_zero_of_injOn isOpen_ball hgTd hgTi hzD
  have hinv := preSchwarzian_inversion (hgTd.analyticAt (isOpen_ball.mem_nhds hzD)) hz0 hgTne hgTd'
  have hback : preSchwarzian (fun w => (gTilde μ w⁻¹)⁻¹) z⁻¹ = preSchwarzian (gsans μ) ζ := by
    rw [hzdef, inv_inv]
    refine s2c_pre_congr (S := {w | w ≠ 0}) (fun w hw => ?_) isOpen_ne hζ0
    have hw : w ≠ 0 := hw
    show (gTilde μ w⁻¹)⁻¹ = gsans μ w
    rw [gTilde, if_neg (inv_ne_zero hw), one_div, inv_inv, one_div, inv_inv]
  rw [hback, hzdef, inv_pow, div_inv_eq_mul] at hinv
  rw [← hinv] at hL
  -- the first integral
  have hT1 : 1 / π * (∫ w in unitDiscExterior, deriv (gTilde μ) z * deriv (fTilde μ) w /
      (gTilde μ z - fTilde μ w) ^ 2 * conj (preSchwarzian (fTilde μ) w)) =
      -ζ ^ 2 * ∫ w in unitDisc, kerK3 (fsans μ) (gsans μ) ζ w *
        conj (preSchwarzian (fun ζ => 1 / fsans μ (1 / ζ)) (1 / w) * (-1 / w ^ 2)) := by
    rw [s310_inv_integral', s310_disc_punct, ← integral_const_mul, ← integral_const_mul]
    refine setIntegral_congr_fun (measurableSet_ball.diff (measurableSet_singleton 0)) fun η hη => ?_
    obtain ⟨hηD, hη0⟩ := hη
    have hη0 : η ≠ 0 := hη0
    have hfη := hfne η hηD hη0
    have hfηd : DifferentiableAt ℂ (fsans μ) η := hfd.differentiableAt (isOpen_ball.mem_nhds hηD)
    have hfT : fTilde μ η⁻¹ = (fsans μ η)⁻¹ := by
      rw [fTilde]; simp only [one_div, inv_inv]
    have hfT' : deriv (fTilde μ) η⁻¹ = deriv (fsans μ) η * η ^ 2 / fsans μ η ^ 2 := by
      rw [show fTilde μ = fun x => (fsans μ x⁻¹)⁻¹ by funext x; rw [fTilde, one_div, one_div]]
      exact s310_inv_deriv hη0 hfηd hfη
    have hne : gsans μ ζ - fsans μ η ≠ 0 := by
      intro h
      exact Set.disjoint_left.mp hdisj ⟨η, hηD, rfl⟩ ⟨ζ, hζ, sub_eq_zero.mp h⟩
    have hpre : preSchwarzian (fTilde μ) η⁻¹ = preSchwarzian (fun ζ => 1 / fsans μ (1 / ζ)) (1 / η) := by
      rw [one_div η]; rfl
    have hcη : conj η ≠ 0 := (map_ne_zero _).mpr hη0
    have hg0 := hgne ζ hζ
    have hFG : fsans μ η - gsans μ ζ ≠ 0 := fun h => hne (by linear_combination -h)
    rw [hfT, hfT', hgTz, hgTz', hpre, kerK3, Complex.real_smul, inv_sub_inv hg0 hfη]
    set P := preSchwarzian (fun ζ => 1 / fsans μ (1 / ζ)) (1 / η) with hP
    push_cast
    rw [s310_norm4]
    simp only [map_mul, map_div₀, map_neg, map_one, map_pow]
    field_simp
    ring
  -- the second integral
  have hT2 : 1 / π * ∫ w in unitDisc, (deriv (gTilde μ) z * deriv (gTilde μ) w / (gTilde μ z - gTilde μ w) ^ 2 -
      1 / (z - w) ^ 2) * conj (preSchwarzian (gTilde μ) w) =
      -ζ ^ 2 * ∫ w in unitDiscExterior, kerK4 (gsans μ) ζ w *
        conj (-(preSchwarzian (fun ζ => 1 / gsans μ (1 / ζ)) (1 / w) * (-1 / w ^ 2))) := by
    rw [s310_disc_punct, s2c_inv_integral, ← integral_const_mul, ← integral_const_mul]
    refine setIntegral_congr_ae hEo.measurableSet ?_
    filter_upwards [compl_mem_ae_iff.mpr (measure_singleton ζ)] with η hηζ hη
    have hηζ : η ≠ ζ := hηζ
    have hη0 := hE0 η hη
    have hgη := hgne η hη
    have hgηd : DifferentiableAt ℂ (gsans μ) η := hgd.differentiableAt (hEo.mem_nhds hη)
    have hevη := s310_gTilde_ev (μ := μ) (inv_ne_zero hη0)
    have hgT : gTilde μ η⁻¹ = (gsans μ η)⁻¹ := by
      rw [gTilde, if_neg (inv_ne_zero hη0)]; simp only [one_div, inv_inv]
    have hgT' : deriv (gTilde μ) η⁻¹ = deriv (gsans μ) η * η ^ 2 / gsans μ η ^ 2 := by
      rw [hevη.deriv_eq]
      exact s310_inv_deriv hη0 hgηd hgη
    have hpre : preSchwarzian (gTilde μ) η⁻¹ =
        preSchwarzian (fun ζ => 1 / gsans μ (1 / ζ)) (1 / η) := by
      rw [one_div η]
      refine s2c_pre_congr (S := {w | w ≠ 0}) (fun w hw => ?_) isOpen_ne (inv_ne_zero hη0)
      have hw : w ≠ 0 := hw
      show gTilde μ w = 1 / gsans μ (1 / w)
      rw [gTilde, if_neg hw]
    have hne : gsans μ ζ - gsans μ η ≠ 0 := fun h => hηζ (hgi hη hζ (sub_eq_zero.mp h).symm)
    have hne' : ζ - η ≠ 0 := sub_ne_zero.mpr (Ne.symm hηζ)
    have hcη : conj η ≠ 0 := (map_ne_zero _).mpr hη0
    have hg0 := hgne ζ hζ
    have hne'' : η - ζ ≠ 0 := sub_ne_zero.mpr hηζ
    have hHG : gsans μ η - gsans μ ζ ≠ 0 := fun h => hne (by linear_combination -h)
    rw [hgT, hgT', hgTz, hgTz', hpre, kerK4_of_ne _ (Ne.symm hηζ), Complex.real_smul, hzdef,
      inv_sub_inv hg0 hgη, inv_sub_inv hζ0 hη0]
    set P := preSchwarzian (fun ζ => 1 / gsans μ (1 / ζ)) (1 / η) with hP
    push_cast
    rw [s310_norm4]
    simp only [map_mul, map_div₀, map_neg, map_one, map_pow]
    field_simp
    ring
  rw [hT1, hT2, ← mul_add] at hL
  have hζ2 : -ζ ^ 2 ≠ 0 := neg_ne_zero.mpr (pow_ne_zero 2 hζ0)
  apply mul_left_cancel₀ hζ2
  linear_combination (-1 : ℂ) * hL

/-- Expansion of a weighted square sum `Σ w |a + t c|²`. -/
theorem s310_polar_sum {w : ℕ → ℝ} {a c : ℕ → ℂ} (hw : ∀ j, 0 ≤ w j)
    (ha : Summable (fun j => w j * ‖a j‖ ^ 2)) (hc : Summable (fun j => w j * ‖c j‖ ^ 2)) (t : ℂ) :
    Summable (fun j => (w j : ℂ) * (c j * conj (a j))) ∧
      ∑' j, w j * ‖a j + t * c j‖ ^ 2 =
        (∑' j, w j * ‖a j‖ ^ 2) + ‖t‖ ^ 2 * (∑' j, w j * ‖c j‖ ^ 2) +
          2 * (t * ∑' j, (w j : ℂ) * (c j * conj (a j))).re := by
  have hX : Summable (fun j => (w j : ℂ) * (c j * conj (a j))) := by
    refine Summable.of_norm_bounded (g := fun j => w j * ‖a j‖ ^ 2 + w j * ‖c j‖ ^ 2) (ha.add hc) ?_
    intro j
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg (hw j), RCLike.norm_conj]
    nlinarith [hw j, sq_nonneg (‖a j‖ - ‖c j‖), norm_nonneg (a j), norm_nonneg (c j)]
  refine ⟨hX, ?_⟩
  have hexp : ∀ j, w j * ‖a j + t * c j‖ ^ 2 =
      w j * ‖a j‖ ^ 2 + ‖t‖ ^ 2 * (w j * ‖c j‖ ^ 2) + 2 * (t * ((w j : ℂ) * (c j * conj (a j)))).re := by
    intro j
    have h1 : ‖a j + t * c j‖ ^ 2 = ‖a j‖ ^ 2 + ‖t‖ ^ 2 * ‖c j‖ ^ 2 + 2 * (t * (c j * conj (a j))).re := by
      simp only [← Complex.normSq_eq_norm_sq]
      rw [Complex.normSq_add, Complex.normSq_mul]
      simp only [Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im]
      ring
    rw [h1]
    have h2 : (t * ((w j : ℂ) * (c j * conj (a j)))).re = w j * (t * (c j * conj (a j))).re := by
      rw [show t * ((w j : ℂ) * (c j * conj (a j))) = (w j : ℂ) * (t * (c j * conj (a j))) by ring,
        Complex.re_ofReal_mul]
    rw [h2]
    ring
  have hre : Summable (fun j => 2 * (t * ((w j : ℂ) * (c j * conj (a j)))).re) :=
    ((Complex.reCLM.summable (hX.mul_left t)).mul_left 2)
  rw [tsum_congr hexp, (ha.add (hc.mul_left _)).tsum_add hre, ha.tsum_add (hc.mul_left _), tsum_mul_left,
    tsum_mul_left]
  congr 2
  rw [← tsum_mul_left]
  exact (Complex.reCLM.map_tsum (hX.mul_left t)).symm

/-- **(P5)** The column-`0` identity of the generalized Grunsky equality (polarization of Theorem 2.1 at
`λ = e₀ + t e_l`): `Σ_{k ≠ 0} |k| b_{kl} \overline{b_{k0}} = b_{0l}` for `l ≠ 0`, with square summability of the
column `(√|k| b_{k0})`. -/
theorem s310_col0 {f g : ℂ → ℂ} (h : IsNormalizedDisjointPair f g)
    (hF : volume ((f '' unitDisc ∪ g '' unitDiscExterior)ᶜ) = 0) {l : ℤ} (hl : l ≠ 0) :
    Summable (fun j : ℕ => ((j + 1 : ℕ) : ℝ) * ‖grunsky f g ((j : ℤ) + 1) 0‖ ^ 2) ∧
      Summable (fun j : ℕ => ((j + 1 : ℕ) : ℝ) * ‖grunsky f g (-((j : ℤ) + 1)) 0‖ ^ 2) ∧
      (∑' j : ℕ, (((j + 1 : ℕ) : ℝ) : ℂ) * (grunsky f g ((j : ℤ) + 1) l * conj (grunsky f g ((j : ℤ) + 1) 0))) +
        (∑' j : ℕ, (((j + 1 : ℕ) : ℝ) : ℂ) *
          (grunsky f g (-((j : ℤ) + 1)) l * conj (grunsky f g (-((j : ℤ) + 1)) 0))) = grunsky f g 0 l := by
  set b := grunsky f g with hb
  set m : ℕ := l.natAbs with hm
  have hl0 : (0 : ℤ) ∈ Finset.Icc (-(m : ℤ)) m := by simp [Finset.mem_Icc]
  have hlI : l ∈ Finset.Icc (-(m : ℤ)) m := by
    simp only [Finset.mem_Icc, hm]; constructor <;> omega
  have hlE : l ∈ (Finset.Icc (-(m : ℤ)) m).erase 0 := Finset.mem_erase.mpr ⟨hl, hlI⟩
  -- the test vectors `λ = e₀ + t e_l`
  set lamt : ℂ → ℤ → ℂ := fun t k => if k = 0 then 1 else if k = l then t else 0 with hlamt
  have hrow : ∀ (t : ℂ) (k : ℤ), (∑ l' ∈ Finset.Icc (-(m : ℤ)) m, b k l' * lamt t l') = b k 0 + t * b k l := by
    intro t k
    rw [Finset.sum_eq_add (0 : ℤ) l (Ne.symm hl) (fun c _ hc => by simp [hlamt, hc.1, hc.2])
      (fun h0 => absurd hl0 h0) (fun h0 => absurd hlI h0)]
    simp only [hlamt, if_pos rfl, if_neg hl, if_true, mul_one]
    ring
  have hdiag : ∀ t : ℂ, (∑ k ∈ (Finset.Icc (-(m : ℤ)) m).erase 0, ‖lamt t k‖ ^ 2 / |(k : ℝ)|) =
      ‖t‖ ^ 2 / |(l : ℝ)| := by
    intro t
    rw [Finset.sum_eq_single l (fun c hc hcl => by
      have hc0 : c ≠ 0 := (Finset.mem_erase.mp hc).1
      simp [hlamt, hc0, hcl]) (fun h0 => absurd hlE h0)]
    simp [hlamt, hl]
  have hlam0 : ∀ t : ℂ, lamt t 0 = 1 := fun t => by simp [hlamt]
  -- the equality for each `t`
  have hE : ∀ t : ℂ,
      Summable (fun j : ℕ => ((j + 1 : ℕ) : ℝ) * ‖b ((j : ℤ) + 1) 0 + t * b ((j : ℤ) + 1) l‖ ^ 2) ∧
      Summable (fun j : ℕ => ((j + 1 : ℕ) : ℝ) * ‖b (-((j : ℤ) + 1)) 0 + t * b (-((j : ℤ) + 1)) l‖ ^ 2) ∧
      (∑' j : ℕ, ((j + 1 : ℕ) : ℝ) * ‖b ((j : ℤ) + 1) 0 + t * b ((j : ℤ) + 1) l‖ ^ 2) +
        (∑' j : ℕ, ((j + 1 : ℕ) : ℝ) * ‖b (-((j : ℤ) + 1)) 0 + t * b (-((j : ℤ) + 1)) l‖ ^ 2) =
        ‖t‖ ^ 2 / |(l : ℝ)| + 2 * (b 0 0 + t * b 0 l).re := by
    intro t
    obtain ⟨-, -, -, -, -, -, -, hs1, hs2, -⟩ := t21_core h m (lamt t)
    have heq := ((thm_2_1 h m).2.mpr hF) (lamt t)
    rw [t21_lhs m (lamt t) hs1 hs2] at heq
    simp only [← hb] at hs1 hs2 heq
    simp only [hrow, hdiag, hlam0, map_one, one_mul] at heq hs1 hs2
    exact ⟨hs1, hs2, heq⟩
  obtain ⟨hA1, hA2, hE0⟩ := hE 0
  simp only [zero_mul, add_zero, norm_zero] at hA1 hA2 hE0
  obtain ⟨hL1, hL2, -⟩ := hE 1
  -- summability of the `c`-columns: `c = (a + c) - a`
  have hw : ∀ j : ℕ, (0 : ℝ) ≤ ((j + 1 : ℕ) : ℝ) := fun j => by positivity
  have hcs : ∀ {a c : ℕ → ℂ}, Summable (fun j : ℕ => ((j + 1 : ℕ) : ℝ) * ‖a j‖ ^ 2) →
      Summable (fun j : ℕ => ((j + 1 : ℕ) : ℝ) * ‖a j + 1 * c j‖ ^ 2) →
      Summable (fun j : ℕ => ((j + 1 : ℕ) : ℝ) * ‖c j‖ ^ 2) := by
    intro a c ha hac
    refine Summable.of_nonneg_of_le (fun j => by positivity) (fun j => ?_) ((ha.add hac).mul_left 2)
    have h1 : ‖c j‖ ≤ ‖a j‖ + ‖a j + 1 * c j‖ := by
      calc ‖c j‖ = ‖-(a j) + (a j + 1 * c j)‖ := by congr 1; ring
        _ ≤ ‖-(a j)‖ + ‖a j + 1 * c j‖ := norm_add_le _ _
        _ = ‖a j‖ + ‖a j + 1 * c j‖ := by rw [norm_neg]
    have h2 : ‖c j‖ ^ 2 ≤ 2 * (‖a j‖ ^ 2 + ‖a j + 1 * c j‖ ^ 2) := by
      nlinarith [norm_nonneg (c j), norm_nonneg (a j), norm_nonneg (a j + 1 * c j),
        sq_nonneg (‖a j‖ - ‖a j + 1 * c j‖)]
    have := mul_le_mul_of_nonneg_left h2 (hw j)
    linarith
  have hC1 := hcs hA1 hL1
  have hC2 := hcs hA2 hL2
  have hP1 := s310_polar_sum hw hA1 hC1
  have hP2 := s310_polar_sum hw hA2 hC2
  set W : ℂ := (∑' j : ℕ, (((j + 1 : ℕ) : ℝ) : ℂ) * (b ((j : ℤ) + 1) l * conj (b ((j : ℤ) + 1) 0))) +
    (∑' j : ℕ, (((j + 1 : ℕ) : ℝ) : ℂ) * (b (-((j : ℤ) + 1)) l * conj (b (-((j : ℤ) + 1)) 0))) with hW
  set A : ℝ := (∑' j : ℕ, ((j + 1 : ℕ) : ℝ) * ‖b ((j : ℤ) + 1) 0‖ ^ 2) +
    ∑' j : ℕ, ((j + 1 : ℕ) : ℝ) * ‖b (-((j : ℤ) + 1)) 0‖ ^ 2 with hA
  set C : ℝ := (∑' j : ℕ, ((j + 1 : ℕ) : ℝ) * ‖b ((j : ℤ) + 1) l‖ ^ 2) +
    ∑' j : ℕ, ((j + 1 : ℕ) : ℝ) * ‖b (-((j : ℤ) + 1)) l‖ ^ 2 with hC
  have hkey : ∀ t : ℂ, A + ‖t‖ ^ 2 * C + 2 * (t * W).re = ‖t‖ ^ 2 / |(l : ℝ)| + 2 * (b 0 0 + t * b 0 l).re := by
    intro t
    obtain ⟨-, -, h3⟩ := hE t
    rw [(hP1 t).2, (hP2 t).2] at h3
    rw [← h3, hA, hC, hW]
    simp only [mul_add, Complex.add_re]
    ring
  have hk1 := hkey 1
  have hkm := hkey (-1)
  have hkI := hkey I
  have hk0 := hkey 0
  simp only [norm_one, norm_neg, Complex.norm_I, one_pow, one_mul, neg_mul, zero_mul, norm_zero,
    Complex.add_re, Complex.neg_re, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.zero_re,
    zero_add, add_zero] at hk1 hkm hkI hk0
  refine ⟨hA1, hA2, Complex.ext ?_ ?_⟩
  · linarith
  · linarith

/-- `√(π(n+1)) √((n+1)/π) = n + 1`. -/
theorem s310_sqrt_id (n : ℕ) :
    (Real.sqrt (π * ((n : ℝ) + 1)) : ℂ) * (Real.sqrt (((n : ℝ) + 1) / π) : ℂ) = (n : ℂ) + 1 := by
  have hπ : 0 < π := Real.pi_pos
  rw [← Complex.ofReal_mul, ← Real.sqrt_mul (by positivity)]
  rw [show π * ((n : ℝ) + 1) * (((n : ℝ) + 1) / π) = ((n : ℝ) + 1) ^ 2 by field_simp]
  rw [Real.sqrt_sq (by positivity)]
  push_cast
  ring

/-- **(P6, series of `w₁`)** `f'/f - 1/z = Σ_n y_n e_n(z)` on `𝔻 \ {0}`, `y_n = -√(π(n+1)) b_{-(n+1),0}`. -/
theorem s310_w1_series {f g : ℂ → ℂ} (h : IsNormalizedDisjointPair f g) {u : ℂ} (hu : u ∈ unitDisc)
    (hu0 : u ≠ 0) :
    HasSum (fun n : ℕ => -(Real.sqrt (π * ((n : ℝ) + 1)) : ℂ) * grunsky f g (-((n : ℤ) + 1)) 0 * basisE n u)
      (deriv f u / f u - 1 / u) := by
  set b := grunsky f g with hb
  have hspec := (grunsky_spec h).1
  have hf0 : f 0 = 0 := h.2.2.1
  set c : ℕ → ℂ := fun n => if n = 0 then 0 else b (-(n : ℤ)) 0 with hc
  -- the power series of `log (f(z)/z)` (with a minus sign)
  have hser : ∀ z ∈ unitDisc, z ≠ 0 → ∃ D, HasSum (fun n => c n * z ^ n) D ∧ f z / z = exp (-D) := by
    intro z hz hz0
    obtain ⟨S, hS, he⟩ := hspec.2.2.2.1 z hz 0 (mem_ball_self one_pos) hz0
    simp only [← hb] at hS he
    have hT : HasSum (fun n : ℕ => b (-(n : ℤ)) 0 * z ^ n) S := by
      refine hS.prod_fiberwise (fun n => ?_)
      apply (hasSum_ite_eq (0 : ℕ) (b (-(n : ℤ)) 0 * z ^ n)).congr_fun
      intro m
      by_cases hm : m = 0
      · subst hm; simp
      · simp [hm]
    refine ⟨S - b 0 0, ?_, ?_⟩
    · have h1 := hT.sub (hasSum_ite_eq (0 : ℕ) (b 0 0))
      refine h1.congr_fun (fun n => ?_)
      by_cases hn : n = 0
      · subst hn; simp [hc]
      · simp [hc, hn]
    · rw [hf0, sub_zero, sub_zero] at he
      rw [he]
      congr 1
      ring
  have hH : ∀ z ∈ unitDisc, HasSum (fun n => c n * z ^ n) (∑' n, c n * z ^ n) := by
    intro z hz
    by_cases hz0 : z = 0
    · subst hz0
      have h0 : (fun n => c n * (0 : ℂ) ^ n) = fun _ => 0 := by
        funext n
        by_cases hn : n = 0
        · subst hn; simp [hc]
        · simp [zero_pow hn]
      rw [h0]
      simpa using (hasSum_zero : HasSum (fun _ : ℕ => (0 : ℂ)) 0)
    · obtain ⟨D, hD, -⟩ := hser z hz hz0
      exact hD.summable.hasSum
  set H : ℂ → ℂ := fun z => ∑' n, c n * z ^ n with hHdef
  have hfH : ∀ z ∈ unitDisc, f z = z * exp (-H z) := by
    intro z hz
    by_cases hz0 : z = 0
    · subst hz0; rw [hf0, zero_mul]
    · obtain ⟨D, hD, he⟩ := hser z hz hz0
      rw [hHdef]
      dsimp only
      rw [hD.tsum_eq, ← he]
      field_simp
  have hHd : DifferentiableOn ℂ H unitDisc := differentiableOn_of_powerSeries hH
  have hHu : DifferentiableAt ℂ H u := hHd.differentiableAt (isOpen_ball.mem_nhds hu)
  have hder := faber_powerSeries_deriv hH hu
  -- `f'/f - 1/z = -H'`
  have hev : f =ᶠ[𝓝 u] fun z => z * exp (-H z) := by
    filter_upwards [isOpen_ball.mem_nhds hu] with z hz
    exact hfH z hz
  have hfd : HasDerivAt (fun z => z * exp (-H z)) (1 * exp (-H u) + u * (exp (-H u) * -deriv H u)) u :=
    (hasDerivAt_id u).mul (hHu.hasDerivAt.neg.cexp)
  have hval : deriv f u / f u - 1 / u = -deriv H u := by
    rw [hev.deriv_eq, hfd.deriv, hfH u hu]
    have he0 : exp (-H u) ≠ 0 := exp_ne_zero _
    field_simp
    ring
  rw [hval]
  refine hder.neg.congr_fun (fun n => ?_)
  simp only [hc, show n + 1 ≠ 0 by omega, if_false, basisE]
  have hs := s310_sqrt_id n
  push_cast at hs ⊢
  rw [show (-((n : ℤ) + 1)) = -(((n + 1 : ℕ) : ℤ)) by push_cast; ring]
  linear_combination (-(b (-(((n + 1 : ℕ) : ℤ))) 0 * u ^ n)) * hs

/-- **(P6, series of `w₂`)** `-(g'/g - 1/z) = Σ_n y'_n f_n(z)` on `𝔻*`, `y'_n = -√(π(n+1)) b_{n+1,0}`. -/
theorem s310_w2_series {f g : ℂ → ℂ} (h : IsNormalizedDisjointPair f g) {w : ℂ} (hw : w ∈ unitDiscExterior) :
    HasSum (fun n : ℕ => -(Real.sqrt (π * ((n : ℝ) + 1)) : ℂ) * grunsky f g ((n : ℤ) + 1) 0 * basisF n w)
      (-(deriv g w / g w - 1 / w)) := by
  set b := grunsky f g with hb
  have hspec := (grunsky_spec h).1
  have hf0 : f 0 = 0 := h.2.2.1
  have hEo : IsOpen unitDiscExterior := isOpen_lt continuous_const continuous_norm
  have hE0 : ∀ v ∈ unitDiscExterior, v ≠ 0 := fun v hv h0 => by
    have h1 : (1 : ℝ) < ‖v‖ := hv
    rw [h0, norm_zero] at h1
    linarith
  set c : ℕ → ℂ := fun m => b ((m : ℤ) + 1) 0 with hc
  have hT : ∀ v ∈ unitDiscExterior, HasSum (fun m : ℕ => c m * v ^ (-((m : ℤ) + 1)))
      (∑' m : ℕ, c m * v ^ (-((m : ℤ) + 1))) := by
    intro v hv
    obtain ⟨T, hT, -⟩ := FB.fb_axis_exp hspec hf0 hv
    simp only [← hb] at hT
    exact hT.summable.hasSum
  set T : ℂ → ℂ := fun v => ∑' m : ℕ, c m * v ^ (-((m : ℤ) + 1)) with hTdef
  have hgT : ∀ v ∈ unitDiscExterior, g v = derivAtInfty g * v * exp (-T v) := by
    intro v hv
    obtain ⟨T', hT', he⟩ := FB.fb_axis_exp hspec hf0 hv
    simp only [← hb] at hT'
    rw [he, hTdef]
    dsimp only
    rw [hT'.tsum_eq]
  have hβ : derivAtInfty g ≠ 0 := by rw [← hspec.1]; exact exp_ne_zero _
  -- differentiability of `T` through the disc series `G(x) = T(1/x)`
  set d : ℕ → ℂ := fun n => if n = 0 then 0 else c (n - 1) with hd
  set G : ℂ → ℂ := fun x => if x = 0 then 0 else T x⁻¹ with hG
  have hD : ∀ x ∈ unitDisc, HasSum (fun n => d n * x ^ n) (G x) := by
    intro x hx
    by_cases hx0 : x = 0
    · subst x
      rw [show G 0 = 0 by simp [hG]]
      apply (hasSum_zero : HasSum (fun _ : ℕ => (0 : ℂ)) 0).congr_fun
      intro n
      by_cases hn : n = 0 <;> simp [hd, hn]
    · have hS := hT x⁻¹ (a21_inv_punctured ⟨hx, hx0⟩)
      have hshift : HasSum (fun n => d (n + 1) * x ^ (n + 1)) (G x) := by
        simpa only [hd, hG, hTdef, Nat.add_sub_cancel, show ∀ n : ℕ, ¬n + 1 = 0 by omega, if_false,
          g1_zpow_neg_succ, inv_inv, hx0] using hS
      simpa [hd] using (hasSum_nat_add_iff (f := fun n => d n * x ^ n) 1).mp hshift
  have hw0 := hE0 w hw
  have hwi := a21_inv_exterior hw
  have hGd : DifferentiableAt ℂ G w⁻¹ :=
    (differentiableOn_of_powerSeries hD).differentiableAt (isOpen_ball.mem_nhds hwi.1)
  have heT : (fun v => G v⁻¹) =ᶠ[𝓝 w] T := by
    filter_upwards [eventually_ne_nhds hw0] with v hv
    simp [hG, inv_ne_zero hv]
  have hTd : DifferentiableAt ℂ T w :=
    ((hGd.hasDerivAt.comp w (hasDerivAt_inv hw0)).congr_of_eventuallyEq heT.symm).differentiableAt
  have hder := faber_exteriorSeries_deriv hT hw
  -- `-(g'/g - 1/z) = T'`
  have hev : g =ᶠ[𝓝 w] fun v => derivAtInfty g * v * exp (-T v) := by
    filter_upwards [hEo.mem_nhds hw] with v hv
    exact hgT v hv
  have hgd : HasDerivAt (fun v => derivAtInfty g * v * exp (-T v))
      (derivAtInfty g * 1 * exp (-T w) + derivAtInfty g * w * (exp (-T w) * -deriv T w)) w :=
    (((hasDerivAt_id w).const_mul (derivAtInfty g)).mul (hTd.hasDerivAt.neg.cexp))
  have hval : -(deriv g w / g w - 1 / w) = deriv T w := by
    rw [hev.deriv_eq, hgd.deriv, hgT w hw]
    have he0 : exp (-T w) ≠ 0 := exp_ne_zero _
    field_simp
    ring
  rw [hval]
  refine hder.congr_fun (fun n => ?_)
  simp only [hc, basisF]
  have hs := s310_sqrt_id n
  have hz : w ^ (-((n : ℤ) + 2)) = w ^ (-(n : ℤ) - 2) := by congr 1; ring
  rw [hz]
  push_cast at hs ⊢
  linear_combination (-(b ((n : ℤ) + 1) 0 * w ^ (-(n : ℤ) - 2))) * hs

/-- Interchange of the two sums in `Σ_n (Σ_p M_{np} e_p) ȳ_n` for a matrix with columns of `ℓ²`-norm `≤ 1`,
`e ∈ ℓ¹` and `y ∈ ℓ²`. -/
theorem s310_swap {M : ℕ → ℕ → ℂ} {e y : ℕ → ℂ}
    (hM : ∀ p, Summable (fun n => ‖M n p‖ ^ 2) ∧ (∑' n, ‖M n p‖ ^ 2) ≤ 1)
    (he : Summable (fun p => ‖e p‖)) (hy : Summable (fun n => ‖y n‖ ^ 2)) :
    Summable (fun p => e p * ∑' n, M n p * conj (y n)) ∧
      HasSum (fun n => (∑' p, M n p * e p) * conj (y n)) (∑' p, e p * ∑' n, M n p * conj (y n)) := by
  set Y := ∑' n, ‖y n‖ ^ 2 with hY
  set G : ℕ × ℕ → ℝ := fun q => ‖e q.1‖ * ((‖M q.2 q.1‖ ^ 2 + ‖y q.2‖ ^ 2) / 2) with hG
  have hG0 : 0 ≤ G := fun q => by positivity
  have hfib : ∀ p, HasSum (fun n => G (p, n)) (‖e p‖ * (((∑' n, ‖M n p‖ ^ 2) + Y) / 2)) := by
    intro p
    have h1 := ((((hM p).1.hasSum.add hy.hasSum).div_const 2).mul_left ‖e p‖)
    exact h1
  have hGs : Summable G := by
    refine (summable_prod_of_nonneg hG0).mpr ⟨fun p => (hfib p).summable, ?_⟩
    refine Summable.of_nonneg_of_le (fun p => tsum_nonneg (fun n => hG0 _)) (fun p => ?_)
      (he.mul_right ((1 + Y) / 2))
    rw [(hfib p).tsum_eq]
    have hY0 : 0 ≤ Y := tsum_nonneg (fun n => by positivity)
    exact mul_le_mul_of_nonneg_left (by linarith [(hM p).2]) (norm_nonneg _)
  set F : ℕ × ℕ → ℂ := fun q => M q.2 q.1 * e q.1 * conj (y q.2) with hFdef
  have hFb : ∀ q, ‖F q‖ ≤ G q := by
    intro q
    simp only [hFdef, hG, norm_mul, RCLike.norm_conj]
    have h := two_mul_le_add_sq ‖M q.2 q.1‖ ‖y q.2‖
    nlinarith [norm_nonneg (e q.1), norm_nonneg (M q.2 q.1), norm_nonneg (y q.2)]
  have hFs : Summable F := Summable.of_norm_bounded hGs hFb
  -- fibres over `p`
  have hp : ∀ p, HasSum (fun n => F (p, n)) (e p * ∑' n, M n p * conj (y n)) := by
    intro p
    have hs : Summable (fun n => F (p, n)) := hFs.prod_factor p
    have h1 := hs.hasSum
    convert h1 using 1
    rw [← tsum_mul_left]
    exact tsum_congr (fun n => by simp only [hFdef]; ring)
  have htot := hFs.hasSum.prod_fiberwise hp
  -- fibres over `n`
  have hFs' : Summable (F ∘ Prod.swap) := (Equiv.prodComm ℕ ℕ).summable_iff.mpr hFs
  have hn : ∀ n, HasSum (fun p => (F ∘ Prod.swap) (n, p)) ((∑' p, M n p * e p) * conj (y n)) := by
    intro n
    have hs : Summable (fun p => (F ∘ Prod.swap) (n, p)) := hFs'.prod_factor n
    have h1 := hs.hasSum
    convert h1 using 1
    rw [← tsum_mul_right]
    rfl
  have htot' := hFs'.hasSum.prod_fiberwise hn
  have hval : ∑' q, (F ∘ Prod.swap) q = ∑' q, F q := (Equiv.prodComm ℕ ℕ).tsum_eq F
  rw [hval, ← htot.tsum_eq] at htot'
  exact ⟨htot.summable, htot'⟩

/-- `√((n+1)(p+1)) √(π(n+1)) = √π √(p+1) (n+1)`. -/
theorem s310_sqrt_term (n p : ℕ) :
    (Real.sqrt (((n : ℝ) + 1) * ((p : ℝ) + 1)) : ℂ) * (Real.sqrt (π * ((n : ℝ) + 1)) : ℂ) =
      (Real.sqrt π * Real.sqrt ((p : ℝ) + 1) : ℝ) * (((n + 1 : ℕ) : ℝ) : ℂ) := by
  have hn : (0 : ℝ) ≤ (n : ℝ) + 1 := by positivity
  rw [← Complex.ofReal_mul, ← Complex.ofReal_mul]
  congr 1
  rw [Real.sqrt_mul hn, Real.sqrt_mul Real.pi_pos.le]
  have h := Real.mul_self_sqrt hn
  push_cast
  linear_combination (Real.sqrt π * Real.sqrt ((p : ℝ) + 1)) * h

/-- **(P6, coefficients, disc)** `Σ_n B₁_{np} ȳ_n + Σ_n B₃_{np} ȳ'_n = y_p`. -/
theorem s310_coef_disc {f g : ℂ → ℂ} (h : IsNormalizedDisjointPair f g)
    (hF : volume ((f '' unitDisc ∪ g '' unitDiscExterior)ᶜ) = 0) (p : ℕ) :
    (∑' n, B1 (grunsky f g) n p * conj (-(Real.sqrt (π * ((n : ℝ) + 1)) : ℂ) * grunsky f g (-((n : ℤ) + 1)) 0)) +
      (∑' n, B3 (grunsky f g) n p * conj (-(Real.sqrt (π * ((n : ℝ) + 1)) : ℂ) * grunsky f g ((n : ℤ) + 1) 0)) =
      -(Real.sqrt (π * ((p : ℝ) + 1)) : ℂ) * grunsky f g (-((p : ℤ) + 1)) 0 := by
  set b := grunsky f g with hb
  set l : ℤ := -((p : ℤ) + 1) with hl
  have hl0 : l ≠ 0 := by omega
  obtain ⟨-, -, hcol⟩ := s310_col0 h hF hl0
  simp only [← hb] at hcol
  set c : ℂ := ((Real.sqrt π * Real.sqrt ((p : ℝ) + 1) : ℝ) : ℂ) with hc
  have e1 : ∀ n : ℕ, B1 b n p * conj (-(Real.sqrt (π * ((n : ℝ) + 1)) : ℂ) * b (-((n : ℤ) + 1)) 0) =
      -c * ((((n + 1 : ℕ) : ℝ) : ℂ) * (b (-((n : ℤ) + 1)) l * conj (b (-((n : ℤ) + 1)) 0))) := by
    intro n
    have hs := s310_sqrt_term n p
    simp only [B1, map_mul, map_neg, Complex.conj_ofReal, hl]
    push_cast at hs ⊢
    rw [hc]
    push_cast
    linear_combination (-(b (-((n : ℤ) + 1)) (-((p : ℤ) + 1)) * conj (b (-((n : ℤ) + 1)) 0))) * hs
  have e3 : ∀ n : ℕ, B3 b n p * conj (-(Real.sqrt (π * ((n : ℝ) + 1)) : ℂ) * b ((n : ℤ) + 1) 0) =
      -c * ((((n + 1 : ℕ) : ℝ) : ℂ) * (b ((n : ℤ) + 1) l * conj (b ((n : ℤ) + 1) 0))) := by
    intro n
    have hs := s310_sqrt_term n p
    simp only [B3, map_mul, map_neg, Complex.conj_ofReal, hl]
    push_cast at hs ⊢
    rw [hc]
    push_cast
    linear_combination (-(b ((n : ℤ) + 1) (-((p : ℤ) + 1)) * conj (b ((n : ℤ) + 1) 0))) * hs
  rw [tsum_congr e1, tsum_congr e3, tsum_mul_left, tsum_mul_left, ← mul_add, add_comm, hcol]
  have hsym := ((grunsky_spec h).2 0 (p + 1)).2
  simp only [← hb, Nat.cast_zero, neg_zero, Nat.cast_add, Nat.cast_one] at hsym
  rw [hl, hsym, hc]
  have hsq : Real.sqrt (π * ((p : ℝ) + 1)) = Real.sqrt π * Real.sqrt ((p : ℝ) + 1) :=
    Real.sqrt_mul Real.pi_pos.le _
  rw [hsq]

/-- **(P6, coefficients, exterior)** `Σ_n B₂_{nq} ȳ_n + Σ_n B₄_{nq} ȳ'_n = y'_q`. -/
theorem s310_coef_ext {f g : ℂ → ℂ} (h : IsNormalizedDisjointPair f g)
    (hF : volume ((f '' unitDisc ∪ g '' unitDiscExterior)ᶜ) = 0) (p : ℕ) :
    (∑' n, B2 (grunsky f g) n p * conj (-(Real.sqrt (π * ((n : ℝ) + 1)) : ℂ) * grunsky f g (-((n : ℤ) + 1)) 0)) +
      (∑' n, B4 (grunsky f g) n p * conj (-(Real.sqrt (π * ((n : ℝ) + 1)) : ℂ) * grunsky f g ((n : ℤ) + 1) 0)) =
      -(Real.sqrt (π * ((p : ℝ) + 1)) : ℂ) * grunsky f g ((p : ℤ) + 1) 0 := by
  set b := grunsky f g with hb
  set l : ℤ := (p : ℤ) + 1 with hl
  have hl0 : l ≠ 0 := by omega
  obtain ⟨-, -, hcol⟩ := s310_col0 h hF hl0
  simp only [← hb] at hcol
  set c : ℂ := ((Real.sqrt π * Real.sqrt ((p : ℝ) + 1) : ℝ) : ℂ) with hc
  have e2 : ∀ n : ℕ, B2 b n p * conj (-(Real.sqrt (π * ((n : ℝ) + 1)) : ℂ) * b (-((n : ℤ) + 1)) 0) =
      -c * ((((n + 1 : ℕ) : ℝ) : ℂ) * (b (-((n : ℤ) + 1)) l * conj (b (-((n : ℤ) + 1)) 0))) := by
    intro n
    have hs := s310_sqrt_term n p
    simp only [B2, map_mul, map_neg, Complex.conj_ofReal, hl]
    push_cast at hs ⊢
    rw [hc]
    push_cast
    linear_combination (-(b (-((n : ℤ) + 1)) ((p : ℤ) + 1) * conj (b (-((n : ℤ) + 1)) 0))) * hs
  have e4 : ∀ n : ℕ, B4 b n p * conj (-(Real.sqrt (π * ((n : ℝ) + 1)) : ℂ) * b ((n : ℤ) + 1) 0) =
      -c * ((((n + 1 : ℕ) : ℝ) : ℂ) * (b ((n : ℤ) + 1) l * conj (b ((n : ℤ) + 1) 0))) := by
    intro n
    have hs := s310_sqrt_term n p
    simp only [B4, map_mul, map_neg, Complex.conj_ofReal, hl]
    push_cast at hs ⊢
    rw [hc]
    push_cast
    linear_combination (-(b ((n : ℤ) + 1) ((p : ℤ) + 1) * conj (b ((n : ℤ) + 1) 0))) * hs
  rw [tsum_congr e2, tsum_congr e4, tsum_mul_left, tsum_mul_left, ← mul_add, add_comm, hcol]
  have hsym := (grunsky_spec h).1.2.2.2.2 0 p
  simp only [← hb, Nat.cast_zero, neg_zero] at hsym
  rw [hl, hsym, hc]
  have hsq : Real.sqrt (π * ((p : ℝ) + 1)) = Real.sqrt π * Real.sqrt ((p : ℝ) + 1) :=
    Real.sqrt_mul Real.pi_pos.le _
  rw [hsq]

/-- Square summability of the coefficients of `w₁` and `w₂`. -/
theorem s310_y_summable {f g : ℂ → ℂ} (h : IsNormalizedDisjointPair f g)
    (hF : volume ((f '' unitDisc ∪ g '' unitDiscExterior)ᶜ) = 0) :
    Summable (fun n : ℕ => ‖-(Real.sqrt (π * ((n : ℝ) + 1)) : ℂ) * grunsky f g (-((n : ℤ) + 1)) 0‖ ^ 2) ∧
      Summable (fun n : ℕ => ‖-(Real.sqrt (π * ((n : ℝ) + 1)) : ℂ) * grunsky f g ((n : ℤ) + 1) 0‖ ^ 2) := by
  obtain ⟨hA1, hA2, -⟩ := s310_col0 h hF (l := 1) one_ne_zero
  have e : ∀ (n : ℕ) (a : ℂ), ‖-(Real.sqrt (π * ((n : ℝ) + 1)) : ℂ) * a‖ ^ 2 =
      π * (((n + 1 : ℕ) : ℝ) * ‖a‖ ^ 2) := by
    intro n a
    rw [norm_mul, norm_neg, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _), mul_pow,
      Real.sq_sqrt (by positivity)]
    push_cast
    ring
  refine ⟨?_, ?_⟩
  · simp only [e]; exact hA2.mul_left π
  · simp only [e]; exact hA1.mul_left π

/-- The rows `K₁(z, ·)`, `K₂(z, ·)` (`z ∈ 𝔻`) in the Bergman bases, with `ℓ²` coefficients. -/
theorem s310_rows_disc {f g : ℂ → ℂ} (h : IsNormalizedDisjointPair f g)
    (hF : volume ((f '' unitDisc ∪ g '' unitDiscExterior)ᶜ) = 0) {z : ℂ} (hz : z ∈ unitDisc) :
    Summable (fun n => ‖∑' p, B1 (grunsky f g) n p * basisE p z‖ ^ 2) ∧
      Summable (fun n => ‖∑' p, B3 (grunsky f g) n p * basisE p z‖ ^ 2) ∧
      (∀ u ∈ unitDisc, z ≠ u →
        HasSum (fun n => (∑' m, B1 (grunsky f g) n m * basisE m z) * basisE n u) (kerK1 f z u)) ∧
      ∀ u ∈ unitDiscExterior,
        HasSum (fun q => (∑' p, B3 (grunsky f g) q p * basisE p z) * basisF q u) (kerK2 f g z u) := by
  obtain ⟨-, -, -, -, -, hA1, hA2, hA3, hA4⟩ := mg_eq_2_2_core h hF (B1 := B1 (grunsky f g))
    (B2 := B2 (grunsky f g)) (B3 := B3 (grunsky f g)) (B4 := B4 (grunsky f g))
    (fun m n => rfl) (fun m n => rfl) (fun m n => rfl) (fun m n => rfl)
  obtain ⟨hsy, hcol1, -, -⟩ := mg_unitary_core h hF (B1 := B1 (grunsky f g))
    (B2 := B2 (grunsky f g)) (B3 := B3 (grunsky f g)) (B4 := B4 (grunsky f g))
    (fun m n => rfl) (fun m n => rfl) (fun m n => rfl) (fun m n => rfl)
  have hcolA : ∀ m n : ℕ, (∑' k, (conj (B1 (grunsky f g) k m) * B1 (grunsky f g) k n +
      conj (B3 (grunsky f g) k m) * B3 (grunsky f g) k n)) = if m = n then 1 else 0 := hcol1
  have hv := e24_absE hz
  obtain ⟨hx1, hx3⟩ := e24_pair_sq (v := fun p => basisE p z) hcolA hv
  have hconv1 : ∀ (u : ℂ), u ∈ unitDisc → ∀ n, Summable (fun m => B1 (grunsky f g) n m * basisE m u) :=
    fun u hu n => (bergman_pair_summable (hA1 n) (basisE_sq_summable hu)).of_norm
  have hconv3 : ∀ (u : ℂ), u ∈ unitDisc → ∀ n, Summable (fun m => B3 (grunsky f g) n m * basisE m u) :=
    fun u hu n => (bergman_pair_summable (hA3 n) (basisE_sq_summable hu)).of_norm
  have hK1exp : ∀ u ∈ unitDisc, z ≠ u →
      HasSum (fun n => (∑' m, B1 (grunsky f g) n m * basisE m z) * basisE n u) (kerK1 f z u) :=
    fun u hu hne => g2c_kernel_row_series (fun m n => (hsy m n).1) (e24_hK1 h) hz hu hne (hconv1 z hz)
  have hK2exp : ∀ u ∈ unitDiscExterior,
      HasSum (fun q => (∑' p, B3 (grunsky f g) q p * basisE p z) * basisF q u) (kerK2 f g z u) := by
    intro u hu
    have hs := (Equiv.prodComm ℕ ℕ).hasSum_iff.mpr (e24_K2_series h hz hu)
    refine hs.prod_fiberwise (fun q => ?_)
    refine ((hconv3 z hz q).hasSum.mul_right (basisF q u)).congr_fun (fun p => ?_)
    simp only [Function.comp_apply, Equiv.prodComm_apply, Prod.fst_swap, Prod.snd_swap]
    rw [(hsy q p).2.2]
  exact ⟨hx1, hx3, hK1exp, hK2exp⟩

/-- **(P6, disc)** `K₁w̄₁ + K₂w̄₂ = w₁` on `𝔻 \ {0}` (generalized Grunsky equality). -/
theorem s310_Kw_disc {f g : ℂ → ℂ} (h : IsNormalizedDisjointPair f g)
    (hF : volume ((f '' unitDisc ∪ g '' unitDiscExterior)ᶜ) = 0) {z : ℂ} (hz : z ∈ unitDisc) (hz0 : z ≠ 0) :
    (∫ u in unitDisc, kerK1 f z u * conj (deriv f u / f u - 1 / u)) +
      (∫ u in unitDiscExterior, kerK2 f g z u * conj (-(deriv g u / g u - 1 / u))) =
      deriv f z / f z - 1 / z := by
  obtain ⟨hx1, hx3, hK1exp, hK2exp⟩ := s310_rows_disc h hF hz
  obtain ⟨-, hcol1, -, -⟩ := mg_unitary_core h hF (B1 := B1 (grunsky f g))
    (B2 := B2 (grunsky f g)) (B3 := B3 (grunsky f g)) (B4 := B4 (grunsky f g))
    (fun m n => rfl) (fun m n => rfl) (fun m n => rfl) (fun m n => rfl)
  have hcolA : ∀ m n : ℕ, (∑' k, (conj (B1 (grunsky f g) k m) * B1 (grunsky f g) k n +
      conj (B3 (grunsky f g) k m) * B3 (grunsky f g) k n)) = if m = n then 1 else 0 := hcol1
  have hv := e24_absE hz
  obtain ⟨hyE, hyF⟩ := s310_y_summable h hF
  have hI1 := e24_int_pair hx1 hyE (E := {z, 0}) ((Set.toFinite _).measure_zero volume)
    (fun u hu hn => hK1exp u hu (fun h0 => hn (by simp [h0])))
    (fun u hu hn => s310_w1_series h hu (fun h0 => hn (by simp [h0])))
  have hI2 := e24_ext_pair hx3 hyF (E := ∅) Set.finite_empty
    (fun u hu _ => hK2exp u hu) (fun u hu _ => s310_w2_series h hu)
  have hS1 := s310_swap (M := B1 (grunsky f g)) (fun p => (e24_col hcolA p).1) hv hyE
  have hS3 := s310_swap (M := B3 (grunsky f g)) (fun p => (e24_col hcolA p).2) hv hyF
  rw [hI1.unique hS1.2, hI2.unique hS3.2, ← hS1.1.tsum_add hS3.1, ← (s310_w1_series h hz hz0).tsum_eq]
  refine tsum_congr (fun p => ?_)
  rw [← mul_add, s310_coef_disc h hF p]
  ring

/-- The rows `K₃(z, ·)`, `K₄(z, ·)` (`z ∈ 𝔻*`) in the Bergman bases, with `ℓ²` coefficients. -/
theorem s310_rows_ext {f g : ℂ → ℂ} (h : IsNormalizedDisjointPair f g)
    (hF : volume ((f '' unitDisc ∪ g '' unitDiscExterior)ᶜ) = 0) {z : ℂ} (hz : z ∈ unitDiscExterior) :
    Summable (fun n => ‖∑' p, B2 (grunsky f g) n p * basisF p z‖ ^ 2) ∧
      Summable (fun n => ‖∑' p, B4 (grunsky f g) n p * basisF p z‖ ^ 2) ∧
      (∀ u ∈ unitDisc,
        HasSum (fun n => (∑' q, B2 (grunsky f g) n q * basisF q z) * basisE n u) (kerK3 f g z u)) ∧
      ∀ u ∈ unitDiscExterior, z ≠ u →
        HasSum (fun q => (∑' p, B4 (grunsky f g) q p * basisF p z) * basisF q u) (kerK4 g z u) := by
  obtain ⟨-, -, -, -, -, hA1, hA2, hA3, hA4⟩ := mg_eq_2_2_core h hF (B1 := B1 (grunsky f g))
    (B2 := B2 (grunsky f g)) (B3 := B3 (grunsky f g)) (B4 := B4 (grunsky f g))
    (fun m n => rfl) (fun m n => rfl) (fun m n => rfl) (fun m n => rfl)
  obtain ⟨hsy, -, hcol2, -⟩ := mg_unitary_core h hF (B1 := B1 (grunsky f g))
    (B2 := B2 (grunsky f g)) (B3 := B3 (grunsky f g)) (B4 := B4 (grunsky f g))
    (fun m n => rfl) (fun m n => rfl) (fun m n => rfl) (fun m n => rfl)
  have hcolB : ∀ m n : ℕ, (∑' k, (conj (B2 (grunsky f g) k m) * B2 (grunsky f g) k n +
      conj (B4 (grunsky f g) k m) * B4 (grunsky f g) k n)) = if m = n then 1 else 0 := hcol2
  have hv := e24_absF hz
  obtain ⟨hx2, hx4⟩ := e24_pair_sq (v := fun p => basisF p z) hcolB hv
  have hconv2 : ∀ (u : ℂ), u ∈ unitDiscExterior → ∀ n,
      Summable (fun m => B2 (grunsky f g) n m * basisF m u) :=
    fun u hu n => (bergman_pair_summable (hA2 n) (e24_sq_of_abs (e24_absF hu))).of_norm
  have hconv4 : ∀ (u : ℂ), u ∈ unitDiscExterior → ∀ n,
      Summable (fun m => B4 (grunsky f g) n m * basisF m u) :=
    fun u hu n => (bergman_pair_summable (hA4 n) (e24_sq_of_abs (e24_absF hu))).of_norm
  have hK3exp : ∀ u ∈ unitDisc,
      HasSum (fun n => (∑' q, B2 (grunsky f g) n q * basisF q z) * basisE n u) (kerK3 f g z u) := by
    intro u hu
    rw [e24_K3_eq]
    refine (e24_K2_series h hu hz).prod_fiberwise (fun n => ?_)
    refine ((hconv2 z hz n).hasSum.mul_right (basisE n u)).congr_fun (fun q => ?_)
    ring
  have hK4exp : ∀ u ∈ unitDiscExterior, z ≠ u →
      HasSum (fun q => (∑' p, B4 (grunsky f g) q p * basisF p z) * basisF q u) (kerK4 g z u) := by
    intro u hu hne
    have hs := (Equiv.prodComm ℕ ℕ).hasSum_iff.mpr (e24_hK4 h hF z hz u hu hne)
    refine hs.prod_fiberwise (fun q => ?_)
    refine ((hconv4 z hz q).hasSum.mul_right (basisF q u)).congr_fun (fun p => ?_)
    simp only [Function.comp_apply, Equiv.prodComm_apply, Prod.fst_swap, Prod.snd_swap]
    rw [(hsy q p).2.1]
  exact ⟨hx2, hx4, hK3exp, hK4exp⟩

/-- **(P6, exterior)** `K₃w̄₁ + K₄w̄₂ = w₂` on `𝔻*` (generalized Grunsky equality). -/
theorem s310_Kw_ext {f g : ℂ → ℂ} (h : IsNormalizedDisjointPair f g)
    (hF : volume ((f '' unitDisc ∪ g '' unitDiscExterior)ᶜ) = 0) {z : ℂ} (hz : z ∈ unitDiscExterior) :
    (∫ u in unitDisc, kerK3 f g z u * conj (deriv f u / f u - 1 / u)) +
      (∫ u in unitDiscExterior, kerK4 g z u * conj (-(deriv g u / g u - 1 / u))) =
      -(deriv g z / g z - 1 / z) := by
  obtain ⟨hx2, hx4, hK3exp, hK4exp⟩ := s310_rows_ext h hF hz
  obtain ⟨-, -, hcol2, -⟩ := mg_unitary_core h hF (B1 := B1 (grunsky f g))
    (B2 := B2 (grunsky f g)) (B3 := B3 (grunsky f g)) (B4 := B4 (grunsky f g))
    (fun m n => rfl) (fun m n => rfl) (fun m n => rfl) (fun m n => rfl)
  have hcolB : ∀ m n : ℕ, (∑' k, (conj (B2 (grunsky f g) k m) * B2 (grunsky f g) k n +
      conj (B4 (grunsky f g) k m) * B4 (grunsky f g) k n)) = if m = n then 1 else 0 := hcol2
  have hv := e24_absF hz
  obtain ⟨hyE, hyF⟩ := s310_y_summable h hF
  have hI3 := e24_int_pair hx2 hyE (E := {0}) (measure_singleton 0)
    (fun u hu _ => hK3exp u hu)
    (fun u hu hn => s310_w1_series h hu (fun h0 => hn (by simp [h0])))
  have hI4 := e24_ext_pair hx4 hyF (E := {z}) (Set.finite_singleton z)
    (fun u hu hn => hK4exp u hu (fun h0 => hn (by simp [h0])))
    (fun u hu _ => s310_w2_series h hu)
  have hS2 := s310_swap (M := B2 (grunsky f g)) (fun p => (e24_col hcolB p).1) hv hyE
  have hS4 := s310_swap (M := B4 (grunsky f g)) (fun p => (e24_col hcolB p).2) hv hyF
  rw [hI3.unique hS2.2, hI4.unique hS4.2, ← hS2.1.tsum_add hS4.1, ← (s310_w2_series h hz).tsum_eq]
  refine tsum_congr (fun p => ?_)
  rw [← mul_add, s310_coef_ext h hF p]
  ring

/-- **(P2)** Integrability of `k · ψ̄` when `k`, `ψ` agree a.e. with functions of `A₂¹(D)`. -/
theorem s310_int_ae {D : Set ℂ} (hD : MeasurableSet D) {F G φ ψ : ℂ → ℂ} (hφ : φ ∈ A21fun D)
    (hψ : ψ ∈ A21fun D) (hF : ∀ᵐ u ∂(volume.restrict D), F u = φ u)
    (hG : ∀ᵐ u ∂(volume.restrict D), G u = ψ u) :
    Integrable (fun u => F u * conj (G u)) (volume.restrict D) := by
  refine (s3pk_A21_pair_integrable hD hφ hψ).congr ?_
  filter_upwards [hF, hG] with u h1 h2
  rw [h1, h2]

/-- A series in the Bergman basis of `𝔻` that holds off a null set agrees a.e. with an element of `A₂¹(𝔻)`. -/
theorem s310_ae_seriesE {F : ℂ → ℂ} {x : ℕ → ℂ} (hx : Summable (fun n => ‖x n‖ ^ 2)) {E : Set ℂ}
    (hE : volume E = 0) (hF : ∀ u ∈ unitDisc, u ∉ E → HasSum (fun n => x n * basisE n u) (F u)) :
    (fun u => ∑' n, x n * basisE n u) ∈ A21fun unitDisc ∧
      ∀ᵐ u ∂(volume.restrict unitDisc), F u = ∑' n, x n * basisE n u := by
  refine ⟨(bergman_ell2_series hx).1, ?_⟩
  filter_upwards [ae_restrict_mem (show MeasurableSet unitDisc from measurableSet_ball),
    ae_restrict_of_ae (measure_eq_zero_iff_ae_notMem.mp hE)] with u hu hn
  exact ((hF u hu hn).tsum_eq).symm

/-- A series in the Bergman basis of `𝔻*` that holds off a null set agrees a.e. with an element of `A₂¹(𝔻*)`. -/
theorem s310_ae_seriesF {F : ℂ → ℂ} {x : ℕ → ℂ} (hx : Summable (fun n => ‖x n‖ ^ 2)) {E : Set ℂ}
    (hE : volume E = 0) (hF : ∀ u ∈ unitDiscExterior, u ∉ E → HasSum (fun n => x n * basisF n u) (F u)) :
    (fun u => ∑' n, x n * basisF n u) ∈ A21fun unitDiscExterior ∧
      ∀ᵐ u ∂(volume.restrict unitDiscExterior), F u = ∑' n, x n * basisF n u := by
  have hEo : IsOpen unitDiscExterior := isOpen_lt continuous_const continuous_norm
  refine ⟨e212_ext_series hx, ?_⟩
  filter_upwards [ae_restrict_mem hEo.measurableSet,
    ae_restrict_of_ae (measure_eq_zero_iff_ae_notMem.mp hE)] with u hu hn
  exact ((hF u hu hn).tsum_eq).symm

/-- Splitting `∫ k ā` along `a = v - 2w` (a.e.). -/
theorem s310_split {D : Set ℂ} {k a v w : ℂ → ℂ}
    (hv : Integrable (fun u => k u * conj (v u)) (volume.restrict D))
    (hw : Integrable (fun u => k u * conj (w u)) (volume.restrict D))
    (ha : ∀ᵐ u ∂(volume.restrict D), a u = v u - 2 * w u) :
    ∫ u in D, k u * conj (a u) = (∫ u in D, k u * conj (v u)) - 2 * ∫ u in D, k u * conj (w u) := by
  have he : (fun u => k u * conj (a u)) =ᵐ[volume.restrict D]
      fun u => k u * conj (v u) - 2 * (k u * conj (w u)) := by
    filter_upwards [ha] with u hu
    rw [hu, map_sub, map_mul, map_ofNat]
    ring
  rw [integral_congr_ae he, integral_sub hv (hw.const_mul 2), integral_const_mul]

/-- **Remark 3.10** (TT:5206–5248), the copy proved here (statement identical to `remark_3_10`). -/
theorem s310_remark_3_10 {p : T1} (hp : p ∈ T01) :
    let μ : LinfStar := (Quotient.out p : LinfStarBall)
    let f := fsans μ
    let g := gsans μ
    let u₁ : ℂ → ℂ := fun z => preSchwarzian (fun ζ => 1 / f (1 / ζ)) (1 / z) * (-1 / z ^ 2)
    let u₂ : ℂ → ℂ := fun z => -(preSchwarzian (fun ζ => 1 / g (1 / ζ)) (1 / z) * (-1 / z ^ 2))
    let v₁ : ℂ → ℂ := preSchwarzian f
    let v₂ : ℂ → ℂ := fun z => -preSchwarzian g z
    let w₁ : ℂ → ℂ := fun z => deriv f z / f z - 1 / z
    let w₂ : ℂ → ℂ := fun z => -(deriv g z / g z - 1 / z)
    let K : (ℂ → ℂ) → (ℂ → ℂ) → ℂ → ℂ := fun a b z =>
      if z ∈ unitDisc then (∫ w in unitDisc, kerK1 f z w * conj (a w)) + ∫ w in unitDiscExterior, kerK2 f g z w * conj (b w)
      else (∫ w in unitDisc, kerK3 f g z w * conj (a w)) + ∫ w in unitDiscExterior, kerK4 g z w * conj (b w)
    (∀ z ∈ unitDisc, z ≠ 0 → K u₁ u₂ z = -v₁ z ∧ K v₁ v₂ z = -u₁ z ∧ K w₁ w₂ z = w₁ z ∧ u₁ z = v₁ z - 2 * w₁ z) ∧
      ∀ z ∈ unitDiscExterior, K u₁ u₂ z = -v₂ z ∧ K v₁ v₂ z = -u₂ z ∧ K w₁ w₂ z = w₂ z ∧ u₂ z = v₂ z - 2 * w₂ z := by
  intro μ
  dsimp only
  have hμ : μ ∈ LinfStarBall := (Quotient.out p).2
  have hμT : Phi ⟨μ, hμ⟩ ∈ T01 := by
    rw [show Phi ⟨μ, hμ⟩ = p from Quotient.out_eq p]
    exact hp
  obtain ⟨hpair, hF, -⟩ := remark_2_2 hμ
  obtain ⟨hvA, hvB⟩ := s3pk_representative_A21 hμ hμT
  have hEo : IsOpen unitDiscExterior := isOpen_lt continuous_const continuous_norm
  have hEm : MeasurableSet unitDiscExterior := hEo.measurableSet
  have hDm : MeasurableSet unitDisc := measurableSet_ball
  obtain ⟨hyE, hyF⟩ := s310_y_summable hpair hF
  -- `w₁`, `w₂` are a.e. elements of `A₂¹`
  obtain ⟨hw1A, hw1ae⟩ := s310_ae_seriesE hyE (E := {0}) (measure_singleton 0)
    (fun u hu hn => s310_w1_series hpair hu (fun h0 => hn (by simp [h0])))
  obtain ⟨hw2A, hw2ae⟩ := s310_ae_seriesF hyF (E := ∅) measure_empty
    (fun u hu _ => s310_w2_series hpair hu)
  have hrefl : ∀ {D : Set ℂ} (φ : ℂ → ℂ), ∀ᵐ u ∂(volume.restrict D), φ u = φ u :=
    fun φ => Eventually.of_forall fun _ => rfl
  -- `u = v - 2w` a.e.
  have hud : ∀ᵐ u ∂(volume.restrict unitDisc),
      preSchwarzian (fun ζ => 1 / fsans μ (1 / ζ)) (1 / u) * (-1 / u ^ 2) =
        preSchwarzian (fsans μ) u - 2 * (deriv (fsans μ) u / fsans μ u - 1 / u) := by
    filter_upwards [ae_restrict_mem hDm, ae_restrict_of_ae (compl_mem_ae_iff.mpr (measure_singleton (0 : ℂ)))]
      with u hu hu0
    exact s310_uvw_disc hμ hu hu0
  have hue : ∀ᵐ u ∂(volume.restrict unitDiscExterior),
      -(preSchwarzian (fun ζ => 1 / gsans μ (1 / ζ)) (1 / u) * (-1 / u ^ 2)) =
        -preSchwarzian (gsans μ) u - 2 * (-(deriv (gsans μ) u / gsans μ u - 1 / u)) := by
    filter_upwards [ae_restrict_mem hEm] with u hu
    exact s310_uvw_ext hμ hu
  have hneg : ∀ {D : Set ℂ} {k : ℂ → ℂ},
      Integrable (fun u => k u * conj (preSchwarzian (gsans μ) u)) (volume.restrict D) →
      Integrable (fun u => k u * conj (-preSchwarzian (gsans μ) u)) (volume.restrict D) := by
    intro D k hk
    refine hk.neg.congr (Eventually.of_forall fun u => ?_)
    simp only [map_neg, Pi.neg_apply]
    ring
  refine ⟨fun z hz hz0 => ?_, fun z hz => ?_⟩
  · simp only [if_pos hz]
    obtain ⟨hx1, hx3, hK1, hK2⟩ := s310_rows_disc hpair hF hz
    obtain ⟨hk1A, hk1ae⟩ := s310_ae_seriesE hx1 (E := {z}) (measure_singleton z)
      (fun u hu hn => hK1 u hu (fun h0 => hn (by simp [h0])))
    obtain ⟨hk2A, hk2ae⟩ := s310_ae_seriesF hx3 (E := ∅) measure_empty (fun u hu _ => hK2 u hu)
    have i1v : Integrable (fun u => kerK1 (fsans μ) z u * conj (preSchwarzian (fsans μ) u))
        (volume.restrict unitDisc) := s310_int_ae hDm hk1A hvA hk1ae (hrefl _)
    have i1w : Integrable (fun u => kerK1 (fsans μ) z u * conj (deriv (fsans μ) u / fsans μ u - 1 / u))
        (volume.restrict unitDisc) := s310_int_ae hDm hk1A hw1A hk1ae hw1ae
    have i2v : Integrable (fun u => kerK2 (fsans μ) (gsans μ) z u * conj (-preSchwarzian (gsans μ) u))
        (volume.restrict unitDiscExterior) := hneg (s310_int_ae hEm hk2A hvB hk2ae (hrefl _))
    have i2w : Integrable (fun u => kerK2 (fsans μ) (gsans μ) z u *
        conj (-(deriv (gsans μ) u / gsans μ u - 1 / u))) (volume.restrict unitDiscExterior) :=
      s310_int_ae hEm hk2A hw2A hk2ae hw2ae
    have hd := s310_uvw_disc hμ hz hz0
    have hc := s36l_core hμ hμT hz hz0
    have hw := s310_Kw_disc hpair hF hz hz0
    have e1 := s310_split i1v i1w hud
    have e2 := s310_split i2v i2w hue
    refine ⟨?_, ?_, hw, hd⟩
    · rw [e1, e2]
      linear_combination hc - 2 * hw
    · rw [hc, hd]
      ring
  · have hzD : z ∉ unitDisc := by
      intro h
      have h1 : (1 : ℝ) < ‖z‖ := hz
      have h2 : ‖z‖ < 1 := mem_ball_zero_iff.mp h
      linarith
    simp only [if_neg hzD]
    obtain ⟨hx2, hx4, hK3, hK4⟩ := s310_rows_ext hpair hF hz
    obtain ⟨hk3A, hk3ae⟩ := s310_ae_seriesE hx2 (E := ∅) measure_empty (fun u hu _ => hK3 u hu)
    obtain ⟨hk4A, hk4ae⟩ := s310_ae_seriesF hx4 (E := {z}) (measure_singleton z)
      (fun u hu hn => hK4 u hu (fun h0 => hn (by simp [h0])))
    have i3v : Integrable (fun u => kerK3 (fsans μ) (gsans μ) z u * conj (preSchwarzian (fsans μ) u))
        (volume.restrict unitDisc) := s310_int_ae hDm hk3A hvA hk3ae (hrefl _)
    have i3w : Integrable (fun u => kerK3 (fsans μ) (gsans μ) z u *
        conj (deriv (fsans μ) u / fsans μ u - 1 / u)) (volume.restrict unitDisc) :=
      s310_int_ae hDm hk3A hw1A hk3ae hw1ae
    have i4v : Integrable (fun u => kerK4 (gsans μ) z u * conj (-preSchwarzian (gsans μ) u))
        (volume.restrict unitDiscExterior) := hneg (s310_int_ae hEm hk4A hvB hk4ae (hrefl _))
    have i4w : Integrable (fun u => kerK4 (gsans μ) z u * conj (-(deriv (gsans μ) u / gsans μ u - 1 / u)))
        (volume.restrict unitDiscExterior) := s310_int_ae hEm hk4A hw2A hk4ae hw2ae
    have hd := s310_uvw_ext hμ hz
    have hu := s310_ext_Ku hp hz
    dsimp only at hu
    have hw := s310_Kw_ext hpair hF hz
    have e3 := s310_split i3v i3w hud
    have e4 := s310_split i4v i4w hue
    refine ⟨?_, ?_, hw, hd⟩
    · rw [hu, neg_neg]
    · rw [hd]
      rw [e3, e4] at hu
      linear_combination hu + 2 * hw

/-- **Remark 3.10** (TT:5206–5248). For the pair `(f, g) = (𝖿^μ, 𝗀_μ)` of `[μ] ∈ T₀(1)`, let
- `u₁ = 𝒜(ι ∘ f ∘ ι) ∘ ι · ι'` on `𝔻` and `u₂ = -𝒜(ι ∘ g ∘ ι) ∘ ι · ι'` on `𝔻*`;
- `v₁ = 𝒜(f)` and `v₂ = -𝒜(g)`;
- `w₁ = (log(f/z))'` and `w₂ = -(log(g/z))'`.

With `𝐊 = (K₁ K₂; K₃ K₄)` acting by `(K ψ̄)(z) = ∬ K(z, w) \overline{ψ(w)} d²w`, we have:
- `𝐊 ū = -v`;
- `𝐊 v̄ = -u`;
- `𝐊 w̄ = w`;
- `u = v - 2w`. -/
theorem remark_3_10 {p : T1} (hp : p ∈ T01) :
    let μ : LinfStar := (Quotient.out p : LinfStarBall)
    let f := fsans μ
    let g := gsans μ
    let u₁ : ℂ → ℂ := fun z => preSchwarzian (fun ζ => 1 / f (1 / ζ)) (1 / z) * (-1 / z ^ 2)
    let u₂ : ℂ → ℂ := fun z => -(preSchwarzian (fun ζ => 1 / g (1 / ζ)) (1 / z) * (-1 / z ^ 2))
    let v₁ : ℂ → ℂ := preSchwarzian f
    let v₂ : ℂ → ℂ := fun z => -preSchwarzian g z
    let w₁ : ℂ → ℂ := fun z => deriv f z / f z - 1 / z
    let w₂ : ℂ → ℂ := fun z => -(deriv g z / g z - 1 / z)
    let K : (ℂ → ℂ) → (ℂ → ℂ) → ℂ → ℂ := fun a b z =>
      if z ∈ unitDisc then (∫ w in unitDisc, kerK1 f z w * conj (a w)) + ∫ w in unitDiscExterior, kerK2 f g z w * conj (b w)
      else (∫ w in unitDisc, kerK3 f g z w * conj (a w)) + ∫ w in unitDiscExterior, kerK4 g z w * conj (b w)
    (∀ z ∈ unitDisc, z ≠ 0 → K u₁ u₂ z = -v₁ z ∧ K v₁ v₂ z = -u₁ z ∧ K w₁ w₂ z = w₁ z ∧ u₁ z = v₁ z - 2 * w₁ z) ∧
      ∀ z ∈ unitDiscExterior, K u₁ u₂ z = -v₂ z ∧ K v₁ v₂ z = -u₂ z ∧ K w₁ w₂ z = w₂ z ∧ u₂ z = v₂ z - 2 * w₂ z := by
  exact s310_remark_3_10 hp

end TakhtajanTeo.Ch2
