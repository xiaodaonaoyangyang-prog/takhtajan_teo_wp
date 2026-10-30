import TakhtajanTeo.Ch1.S1_3_Fuchsian
import TakhtajanTeo.Ch1.PattersonUnfold

/-!
# Lemma 1.9, conditional on the ball-average mixing statement (`s19m_` prefix)

`lemma_1_9` (S1_3) is proved from the hypothesis `hcore` (CORE): for `f` bounded measurable `Γ`-automorphic on `𝔻*` and
`g` with `g ρ` integrable on the fundamental domain `F`, the pairing over `F` of the hyperbolic ball average
`M_s f(z) = (1/A_s) ∬_{B(z,s)} f ρ` with `g` tends to `(∬_F f ρ)(∬_F g ρ)/A(Γ\𝔻*)` as `s → 1⁻`.

Balls are pseudo-hyperbolic: `B(z, s) = {w ∈ 𝔻* : ‖w - z‖ ≤ s ‖w z̄ - 1‖}` (the image of the pseudo-hyperbolic ball of
`𝔻` under `w ↦ 1/w`), of hyperbolic area `A_s = 4π s²/(1 - s²)` for every centre. The ball of radius `s` about `∞`
is `𝔻*_{1/s} = discExteriorR (1/s)`.

Route (the reduction approved by the leader, W-MIX skeleton):
- (T) for `‖z'‖ ≥ 1/t` the pseudo-hyperbolic triangle inequality nests
  `𝔻*_{(1-st)/(s-t)} ⊆ B(z', s) ⊆ 𝔻*_{(1+st)/(s+t)}`, so replacing the centre `∞` by `z'` costs
  `≤ C (A_{s⊕t} - A_{s⊖t})`, which is `O(t) A_s` as `s → 1`;
- (U) averaging over `z' ∈ U = 𝔻*_{1/t}` and unfolding over `F` gives `∬_U M_s f ρ = ∬_F M_s f g_U ρ` with
  `g_U ρ ∈ L¹(F)`, `∬_F g_U ρ = A_t`;
- CORE gives the limit `A_t ∬_F fρ / A(F)`; let `t → 0`.
-/

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal ComplexConjugate Classical Real Matrix

noncomputable section

namespace TakhtajanTeo

open LiZhongQC

/-- `ρ` is measurable. -/
theorem s19m_rho_measurable : Measurable rho := by
  unfold rho
  fun_prop

/-- The pseudo-hyperbolic ball `B(z, s)` is measurable. -/
theorem s19m_ball_measurable (z : ℂ) (s : ℝ) :
    MeasurableSet {w | w ∈ unitDiscExterior ∧ ‖w - z‖ ≤ s * ‖w * conj z - 1‖} :=
  (isOpen_lt continuous_const continuous_norm).measurableSet.inter
    (measurableSet_le (continuous_norm.comp (continuous_id.sub continuous_const)).measurable
      (continuous_const.mul (continuous_norm.comp ((continuous_id.mul continuous_const).sub continuous_const))).measurable)

/-- A bounded measurable `f` times `ρ` is integrable on any measurable subset of some `𝔻*_r`. -/
theorem s19m_bdd_integrableOn {f : ℂ → ℂ} (hfm : AEStronglyMeasurable f (volume.restrict unitDiscExterior))
    {C : ℝ} (hC : ∀ᵐ z ∂(volume.restrict unitDiscExterior), ‖f z‖ ≤ C) {S : Set ℂ} (_hS : MeasurableSet S)
    {r : ℝ} (hr : 1 < r) (hSr : S ⊆ discExteriorR r) :
    IntegrableOn (fun w => f w * (rho w : ℂ)) S := by
  have hS1 : S ⊆ unitDiscExterior := fun w hw => (hSr hw).1
  have hρi : IntegrableOn rho S := (pat_rho_integrable hr).mono_set hSr
  refine Integrable.mono' (hρi.const_mul C) ((hfm.mono_measure (Measure.restrict_mono hS1 le_rfl)).mul
    (Complex.continuous_ofReal.measurable.comp s19m_rho_measurable).aestronglyMeasurable) ?_
  have hC' : ∀ᵐ z ∂(volume.restrict S), ‖f z‖ ≤ C := ae_restrict_of_ae_restrict_of_subset hS1 hC
  filter_upwards [hC'] with z hz
  have hρ0 : 0 ≤ rho z := div_nonneg (by norm_num) (sq_nonneg _)
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hρ0]
  exact mul_le_mul_of_nonneg_right hz hρ0

/-- `4π/(σ⁻² - 1) = 4πσ²/(1 - σ²)`. -/
theorem s19m_area_conv {σ : ℝ} (h0 : 0 < σ) (h1 : σ < 1) :
    4 * π / ((σ⁻¹) ^ 2 - 1) = 4 * π * σ ^ 2 / (1 - σ ^ 2) := by
  have h2 : 1 - σ ^ 2 ≠ 0 := by nlinarith
  have h3 : σ⁻¹ ^ 2 - 1 = (1 - σ ^ 2) / σ ^ 2 := by field_simp
  rw [h3]
  field_simp

/-- `ρ` is invariant under an `SU(1,1)` Möbius map of `𝔻*`: `|γ'(w)|² ρ(γ w) = ρ(w)`. -/
theorem s19m_rho_pull {g : SL2C} (hg : IsSU11 g) {w : ℂ} (hw : 1 < ‖w‖) (hD : g 1 0 * w + g 1 1 ≠ 0) :
    ‖deriv (mob g) w‖ ^ 2 * rho (mob g w) = rho w := by
  have hd := hasDerivAt_mobius (a := g 0 0) (b := g 0 1) hD
  rw [fd_det g] at hd
  have hd' : deriv (mob g) w = 1 / (g 1 0 * w + g 1 1) ^ 2 := hd.deriv
  have hn := fd_mob_norm hg hw hD
  have hDn : 0 < ‖g 1 0 * w + g 1 1‖ := norm_pos_iff.mpr hD
  have hw2 : 0 < ‖w‖ ^ 2 - 1 := by nlinarith
  have e : (1 - ‖mob g w‖ ^ 2) ^ 2 = ((‖w‖ ^ 2 - 1) / ‖g 1 0 * w + g 1 1‖ ^ 2) ^ 2 := by
    rw [← hn]; ring
  rw [hd', norm_div, norm_one, norm_pow]
  unfold rho
  have e2 : (1 - ‖w‖ ^ 2) ^ 2 = (‖w‖ ^ 2 - 1) ^ 2 := by ring
  have hne : ‖w‖ ^ 2 - 1 ≠ 0 := hw2.ne'
  have hDne : ‖g 1 0 * w + g 1 1‖ ≠ 0 := hDn.ne'
  rw [e, e2]
  field_simp

/-- `|w z̄ - 1|² - |w - z|² = (|w|² - 1)(|z|² - 1)`. -/
theorem s19m_pseudo_ident (w z : ℂ) :
    ‖w * conj z - 1‖ ^ 2 - ‖w - z‖ ^ 2 = (‖w‖ ^ 2 - 1) * (‖z‖ ^ 2 - 1) := by
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.mul_re,
    Complex.mul_im, Complex.conj_re, Complex.conj_im, Complex.one_re, Complex.one_im]
  ring

/-- Inclusion of the small ball about `∞` into `B(z', s)`. -/
theorem s19m_nest_left {z' w : ℂ} {s t : ℝ} (ht0 : 0 < t) (hts : t < s) (hs1 : s < 1)
    (hz' : 1 ≤ t * ‖z'‖) (hw : w ∈ discExteriorR ((1 - s * t) / (s - t))) :
    w ∈ unitDiscExterior ∧ ‖w - z'‖ ≤ s * ‖w * conj z' - 1‖ := by
  obtain ⟨hw1, hwr⟩ := hw
  refine ⟨hw1, ?_⟩
  have hw1' : 1 < ‖w‖ := hw1
  set p := ‖w‖ with hp
  set q := ‖z'‖ with hq
  have hst : 0 < s - t := by linarith
  have hP : 1 - s * t ≤ p * (s - t) := by rwa [div_le_iff₀ hst] at hwr
  have hq1 : 1 < q := by nlinarith
  have hsq : 1 ≤ s * q := by nlinarith
  -- `p + q ≤ s (p q + 1)`
  have hg : p + q ≤ s * (p * q + 1) := by
    nlinarith [mul_nonneg (show 0 ≤ s * q - 1 by linarith) (show 0 ≤ p * (s - t) - (1 - s * t) by linarith),
      mul_nonneg (show 0 ≤ t * q - 1 by linarith) (show (0 : ℝ) ≤ 1 - s ^ 2 by nlinarith)]
  have htri : ‖w - z'‖ ≤ p + q := norm_sub_le _ _
  have hid := s19m_pseudo_ident w z'
  rw [← hp, ← hq] at hid
  have hX0 : 0 ≤ ‖w - z'‖ := norm_nonneg _
  have hD0 : 0 ≤ ‖w * conj z' - 1‖ := norm_nonneg _
  have hs0 : 0 < s := by linarith
  have hsq2 : ‖w - z'‖ ^ 2 ≤ (s * ‖w * conj z' - 1‖) ^ 2 := by
    have h1 : ‖w - z'‖ ^ 2 * (1 - s ^ 2) ≤ s ^ 2 * ((p ^ 2 - 1) * (q ^ 2 - 1)) := by
      have hpq : (p + q) ^ 2 * (1 - s ^ 2) ≤ s ^ 2 * ((p ^ 2 - 1) * (q ^ 2 - 1)) := by
        have : (p + q) ^ 2 ≤ s ^ 2 * (p * q + 1) ^ 2 := by
          have h0 : 0 ≤ p + q := by linarith
          nlinarith
        nlinarith
      have hX : ‖w - z'‖ ^ 2 ≤ (p + q) ^ 2 := pow_le_pow_left₀ hX0 htri 2
      have h1s : (0 : ℝ) ≤ 1 - s ^ 2 := by nlinarith
      linarith [mul_le_mul_of_nonneg_right hX h1s]
    nlinarith
  have hb : 0 ≤ s * ‖w * conj z' - 1‖ := mul_nonneg hs0.le hD0
  exact (pow_le_pow_iff_left₀ hX0 hb two_ne_zero).mp hsq2

/-- Inclusion of `B(z', s)` into the large ball about `∞`. -/
theorem s19m_nest_right {z' w : ℂ} {s t : ℝ} (ht0 : 0 < t) (hts : t < s) (hs1 : s < 1)
    (hz' : 1 ≤ t * ‖z'‖) (hw : w ∈ unitDiscExterior) (hb : ‖w - z'‖ ≤ s * ‖w * conj z' - 1‖) :
    w ∈ discExteriorR ((1 + s * t) / (s + t)) := by
  refine ⟨hw, ?_⟩
  have hw1 : 1 < ‖w‖ := hw
  set p := ‖w‖ with hp
  set q := ‖z'‖ with hq
  have hs0 : 0 < s := by linarith
  have hq1 : 1 < q := by nlinarith
  have hid := s19m_pseudo_ident w z'
  rw [← hp, ← hq] at hid
  have hX0 : 0 ≤ ‖w - z'‖ := norm_nonneg _
  have hDlow : p * q - 1 ≤ ‖w * conj z' - 1‖ := by
    have h1 : ‖w * conj z'‖ = p * q := by rw [norm_mul, Complex.norm_conj]
    have h2 := norm_sub_norm_le (w * conj z') 1
    rw [h1, norm_one] at h2
    exact h2
  have hpq1 : 0 ≤ p * q - 1 := by nlinarith
  -- `(p - q)² ≤ s² (p q - 1)²`
  have hsq : ‖w - z'‖ ^ 2 ≤ s ^ 2 * ‖w * conj z' - 1‖ ^ 2 := by
    have := pow_le_pow_left₀ hX0 hb 2
    nlinarith
  have hkey : (q - p) ^ 2 ≤ s ^ 2 * (p * q - 1) ^ 2 := by
    have hD2 : (p * q - 1) ^ 2 ≤ ‖w * conj z' - 1‖ ^ 2 := pow_le_pow_left₀ hpq1 hDlow 2
    have h1s : 0 ≤ 1 - s ^ 2 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hD2 h1s]
  have hlin : q - p ≤ s * (p * q - 1) := by
    have hr : 0 ≤ s * (p * q - 1) := mul_nonneg hs0.le hpq1
    nlinarith [abs_le_of_sq_le_sq' (show (q - p) ^ 2 ≤ (s * (p * q - 1)) ^ 2 by nlinarith) hr]
  have hst : 0 < s + t := by linarith
  rw [div_le_iff₀ hst]
  have hsq1 : 0 < 1 + s * q := by nlinarith
  -- `p (1 + s q) ≥ q + s` and `(q + s)(s + t) ≥ (1 + s t)(1 + s q)`
  have h1 : q + s ≤ p * (1 + s * q) := by nlinarith
  have h2 : (1 + s * t) * (1 + s * q) ≤ (q + s) * (s + t) := by
    nlinarith [mul_nonneg (show 0 ≤ t * q - 1 by linarith) (show (0 : ℝ) ≤ 1 - s ^ 2 by nlinarith)]
  have h3 : (1 + s * t) * (1 + s * q) ≤ p * (s + t) * (1 + s * q) := by nlinarith
  exact le_of_mul_le_mul_right h3 hsq1

/-- Hyperbolic area of the pseudo-hyperbolic ball `B(z, s)` in `𝔻*`: `4π s²/(1 - s²)`, for every centre. -/
theorem s19m_area_ball {z : ℂ} (hz : z ∈ unitDiscExterior) {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) :
    ∫⁻ w in {w | w ∈ unitDiscExterior ∧ ‖w - z‖ ≤ s * ‖w * conj z - 1‖}, ENNReal.ofReal (rho w) =
      ENNReal.ofReal (4 * π * s ^ 2 / (1 - s ^ 2)) := by
  have hz1 : 1 < ‖z‖ := hz
  set c : ℝ := √(‖z‖ ^ 2 - 1) with hcdef
  have hc : 0 < c := Real.sqrt_pos.mpr (by nlinarith)
  have hc2 : c ^ 2 = ‖z‖ ^ 2 - 1 := Real.sq_sqrt (by nlinarith)
  have hcC : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hc.ne'
  have hzz : conj z * z - 1 = ((‖z‖ ^ 2 - 1 : ℝ) : ℂ) := by
    rw [Complex.conj_mul']
    push_cast
    ring
  have hcc : (c : ℂ) ^ 2 = ((‖z‖ ^ 2 - 1 : ℝ) : ℂ) := by
    rw [← hc2]
    push_cast
    ring
  have hM : (!![conj z / (c : ℂ), -1 / (c : ℂ); -1 / (c : ℂ), z / (c : ℂ)] : Matrix (Fin 2) (Fin 2) ℂ).det = 1 := by
    rw [Matrix.det_fin_two_of]
    have e : conj z / (c : ℂ) * (z / c) - (-1 / c) * (-1 / c) = (conj z * z - 1) / (c : ℂ) ^ 2 := by ring
    rw [e, hzz, hcc, div_self (Complex.ofReal_ne_zero.mpr (by nlinarith))]
  set h : SL2C := ⟨_, hM⟩ with hhdef
  have h00 : h 0 0 = conj z / (c : ℂ) := rfl
  have h01 : h 0 1 = -1 / (c : ℂ) := rfl
  have h10 : h 1 0 = -1 / (c : ℂ) := rfl
  have h11 : h 1 1 = z / (c : ℂ) := rfl
  have hh : IsSU11 h := by
    refine ⟨?_, ?_⟩
    · rw [h10, h01, map_div₀, map_neg, map_one, Complex.conj_ofReal]
    · rw [h11, h00, map_div₀, Complex.conj_conj, Complex.conj_ofReal]
  have hmob : ∀ u, mob h u = (u * conj z - 1) / (z - u) := by
    intro u
    unfold mob
    rw [h00, h01, h10, h11, show conj z / (c : ℂ) * u + -1 / c = (u * conj z - 1) / c by ring,
      show -1 / (c : ℂ) * u + z / c = (z - u) / c by ring, div_div_div_cancel_right₀ hcC]
  have hs1' : 1 < 1 / s := by rw [one_lt_div hs0]; exact hs1
  set F := discExteriorR (1 / s) with hF
  have hFm : MeasurableSet F := pat_discExteriorR_measurable _
  have hFe : F ⊆ unitDiscExterior := fun w hw => hw.1
  have key := fd_tile_lintegral hFm hFe h hh (fun w => ENNReal.ofReal (rho w))
  have hR : ∫⁻ w in F, ENNReal.ofReal (‖deriv (mob h⁻¹) w‖ ^ 2) * ENNReal.ofReal (rho (mob h⁻¹ w)) =
      ∫⁻ w in F, ENNReal.ofReal (rho w) := by
    apply setLIntegral_congr_fun_ae hFm
    have hnull := (fd_denom_finite h⁻¹).measure_zero volume
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp hnull] with w hw hwF
    rw [← ENNReal.ofReal_mul (sq_nonneg _), s19m_rho_pull (isSU11_inv hh) (hFe hwF) hw]
  have hset : {u : ℂ | 1 < ‖u‖ ∧ mob h u ∈ F} =ᵐ[volume]
      {w | w ∈ unitDiscExterior ∧ ‖w - z‖ ≤ s * ‖w * conj z - 1‖} := by
    refine eventuallyEqSet_iff.mpr ?_
    filter_upwards [compl_mem_ae_iff.mpr (measure_singleton z)] with u hu
    have hu' : z - u ≠ 0 := sub_ne_zero.mpr fun e => hu (e ▸ rfl)
    have hpos : 0 < ‖z - u‖ := norm_pos_iff.mpr hu'
    have e1 : ‖mob h u‖ = ‖u * conj z - 1‖ / ‖z - u‖ := by rw [hmob, norm_div]
    have hequiv : 1 / s ≤ ‖mob h u‖ ↔ ‖u - z‖ ≤ s * ‖u * conj z - 1‖ := by
      rw [e1, div_le_div_iff₀ hs0 hpos, norm_sub_rev u z]
      constructor <;> intro hh' <;> linarith
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1, hequiv.mp h2.2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h1, lt_of_lt_of_le hs1' (hequiv.mpr h2), hequiv.mpr h2⟩
  rw [← setLIntegral_congr hset, key, hR, ← ofReal_integral_eq_lintegral_ofReal (pat_rho_integrable hs1')
    (Eventually.of_forall fun z => div_nonneg (by norm_num) (sq_nonneg _)), pat_rho_integral hs1', one_div,
    s19m_area_conv hs0 hs1]

/-- Hyperbolic area of `𝔻*_r` (the ball of pseudo-hyperbolic radius `1/r` about `∞`): `4π/(r² - 1)`. -/
theorem s19m_area_infty {r : ℝ} (hr : 1 < r) :
    ∫⁻ w in discExteriorR r, ENNReal.ofReal (rho w) = ENNReal.ofReal (4 * π / (r ^ 2 - 1)) := by
  rw [← ofReal_integral_eq_lintegral_ofReal (pat_rho_integrable hr)
    (Eventually.of_forall fun z => div_nonneg (by norm_num) (sq_nonneg _)), pat_rho_integral hr]

/-- (T) Nesting: if `‖z'‖ ≥ 1/t` then `𝔻*_{(1-st)/(s-t)} ⊆ B(z', s) ⊆ 𝔻*_{(1+st)/(s+t)}`. -/
theorem s19m_nest {z' : ℂ} {s t : ℝ} (ht0 : 0 < t) (hts : t < s) (hs1 : s < 1) (hz' : 1 ≤ t * ‖z'‖) :
    discExteriorR ((1 - s * t) / (s - t)) ⊆ {w | w ∈ unitDiscExterior ∧ ‖w - z'‖ ≤ s * ‖w * conj z' - 1‖} ∧
      {w | w ∈ unitDiscExterior ∧ ‖w - z'‖ ≤ s * ‖w * conj z' - 1‖} ⊆ discExteriorR ((1 + s * t) / (s + t)) := by
  refine ⟨fun w hw => s19m_nest_left ht0 hts hs1 hz' hw, fun w hw => s19m_nest_right ht0 hts hs1 hz' hw.1 hw.2⟩

/-- (T) Moving the centre from `∞` to `z'` with `‖z'‖ ≥ 1/t` changes `∬_{B} f ρ` by at most
`C (A_{s⊕t} - A_{s⊖t})`, `s ⊕ t = (s + t)/(1 + st)`, `s ⊖ t = (s - t)/(1 - st)`. -/
theorem s19m_thicken {f : ℂ → ℂ} (hfm : AEStronglyMeasurable f (volume.restrict unitDiscExterior)) {C : ℝ}
    (hC : ∀ᵐ z ∂(volume.restrict unitDiscExterior), ‖f z‖ ≤ C) {z' : ℂ} {s t : ℝ} (ht0 : 0 < t) (hts : t < s)
    (hs1 : s < 1) (hz' : 1 ≤ t * ‖z'‖) :
    ‖(∫ w in discExteriorR (1 / s), f w * rho w) -
        ∫ w in {w | w ∈ unitDiscExterior ∧ ‖w - z'‖ ≤ s * ‖w * conj z' - 1‖}, f w * rho w‖ ≤
      C * (4 * π * ((s + t) / (1 + s * t)) ^ 2 / (1 - ((s + t) / (1 + s * t)) ^ 2) -
        4 * π * ((s - t) / (1 - s * t)) ^ 2 / (1 - ((s - t) / (1 - s * t)) ^ 2)) := by
  have hs0 : 0 < s := by linarith
  set B₀ := discExteriorR (1 / s) with hB₀
  set B := {w | w ∈ unitDiscExterior ∧ ‖w - z'‖ ≤ s * ‖w * conj z' - 1‖} with hB
  set rO := (1 + s * t) / (s + t) with hrO
  set rL := (1 - s * t) / (s - t) with hrL
  set O := discExteriorR rO with hO
  set L := discExteriorR rL with hL
  have hst : 0 < s - t := by linarith
  have hst' : 0 < s + t := by linarith
  have hrO1 : 1 < rO := by rw [hrO, one_lt_div hst']; nlinarith
  have hrL1 : 1 < rL := by rw [hrL, one_lt_div hst]; nlinarith
  have hs1' : 1 < 1 / s := by rw [one_lt_div hs0]; exact hs1
  have hLB₀ : L ⊆ B₀ := by
    intro w hw
    refine ⟨hw.1, le_trans ?_ hw.2⟩
    rw [hrL, div_le_div_iff₀ hs0 hst]
    nlinarith [mul_pos ht0 (show 0 < 1 - s ^ 2 by nlinarith)]
  have hB₀O : B₀ ⊆ O := by
    intro w hw
    refine ⟨hw.1, le_trans ?_ hw.2⟩
    rw [hrO, div_le_div_iff₀ hst' hs0]
    nlinarith [mul_pos ht0 (show 0 < 1 - s ^ 2 by nlinarith)]
  obtain ⟨hLB, hBO⟩ := s19m_nest (z' := z') ht0 hts hs1 hz'
  have hmB₀ : MeasurableSet B₀ := pat_discExteriorR_measurable _
  have hmB : MeasurableSet B := s19m_ball_measurable z' s
  have hmO : MeasurableSet O := pat_discExteriorR_measurable _
  have hmL : MeasurableSet L := pat_discExteriorR_measurable _
  have hiB₀ := s19m_bdd_integrableOn hfm hC hmB₀ hrO1 hB₀O
  have hiB := s19m_bdd_integrableOn hfm hC hmB hrO1 hBO
  have hCx : ∀ᵐ x ∂volume, x ∈ unitDiscExterior → ‖f x‖ ≤ C :=
    (ae_restrict_iff' (isOpen_lt continuous_const continuous_norm).measurableSet).mp hC
  have hρO : IntegrableOn rho O := pat_rho_integrable hrO1
  have hbound : Integrable (fun x => C * (O \ L).indicator rho x) :=
    ((integrable_indicator_iff (hmO.diff hmL)).mpr (hρO.mono_set sdiff_subset)).const_mul C
  rw [← integral_indicator hmB₀, ← integral_indicator hmB,
    ← integral_sub ((integrable_indicator_iff hmB₀).mpr hiB₀) ((integrable_indicator_iff hmB).mpr hiB)]
  refine (norm_integral_le_of_norm_le hbound ?_).trans_eq ?_
  · filter_upwards [hCx] with x hx
    by_cases hxO : x ∈ O
    · have hfx := hx hxO.1
      have hρx : 0 ≤ rho x := div_nonneg (by norm_num) (sq_nonneg _)
      by_cases hxL : x ∈ L
      · rw [indicator_of_mem (hLB₀ hxL), indicator_of_mem (hLB hxL), sub_self, norm_zero,
          indicator_of_notMem (fun h => h.2 hxL), mul_zero]
      · rw [indicator_of_mem (show x ∈ O \ L from ⟨hxO, hxL⟩)]
        have hg : ‖f x * (rho x : ℂ)‖ ≤ C * rho x := by
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hρx]
          exact mul_le_mul_of_nonneg_right hfx hρx
        have h0 : 0 ≤ C * rho x := (norm_nonneg _).trans hg
        by_cases h1 : x ∈ B₀ <;> by_cases h2 : x ∈ B <;>
          simp only [indicator_of_mem, indicator_of_notMem, h1, h2, not_false_eq_true, sub_self, norm_zero,
            sub_zero, zero_sub, norm_neg] <;> first | exact h0 | exact hg
    · rw [indicator_of_notMem (fun h => hxO (hB₀O h)), indicator_of_notMem (fun h => hxO (hBO h)),
        indicator_of_notMem (fun h => hxO h.1), sub_self, norm_zero, mul_zero]
  · rw [integral_const_mul, integral_indicator (hmO.diff hmL), setIntegral_sdiff hmL hρO
      (fun w hw => ⟨hw.1, le_trans (by
        rw [hrO, hrL, div_le_div_iff₀ hst' hst]
        nlinarith [mul_pos ht0 (show 0 < 1 - s ^ 2 by nlinarith)]) hw.2⟩),
      pat_rho_integral hrO1, pat_rho_integral hrL1]
    have hP0 : 0 < (s + t) / (1 + s * t) := div_pos hst' (by nlinarith)
    have hP1 : (s + t) / (1 + s * t) < 1 := by rw [div_lt_one (by nlinarith)]; nlinarith
    have hM0 : 0 < (s - t) / (1 - s * t) := div_pos hst (by nlinarith)
    have hM1 : (s - t) / (1 - s * t) < 1 := by rw [div_lt_one (by nlinarith)]; nlinarith
    have eO : rO = ((s + t) / (1 + s * t))⁻¹ := by rw [hrO, inv_div]
    have eL : rL = ((s - t) / (1 - s * t))⁻¹ := by rw [hrL, inv_div]
    rw [eO, eL, s19m_area_conv hP0 hP1, s19m_area_conv hM0 hM1]

/-- `SU(1,1)` Möbius maps preserve the pseudo-hyperbolic quantities. -/
theorem s19m_su11_pseudo {g : SL2C} (hg : IsSU11 g) {u v : ℂ} (hu : g 1 0 * u + g 1 1 ≠ 0)
    (hv : g 1 0 * v + g 1 1 ≠ 0) :
    ‖mob g u - mob g v‖ = ‖u - v‖ / (‖g 1 0 * u + g 1 1‖ * ‖g 1 0 * v + g 1 1‖) ∧
      ‖mob g u * conj (mob g v) - 1‖ = ‖u * conj v - 1‖ / (‖g 1 0 * u + g 1 1‖ * ‖g 1 0 * v + g 1 1‖) := by
  have hdet := fd_det g
  have hvc : conj (g 1 0 * v + g 1 1) ≠ 0 := (map_ne_zero _).mpr hv
  constructor
  · have e1 : mob g u - mob g v = (u - v) / ((g 1 0 * u + g 1 1) * (g 1 0 * v + g 1 1)) := by
      unfold mob
      rw [div_sub_div _ _ hu hv]
      congr 1
      linear_combination (u - v) * hdet
    rw [e1, norm_div, norm_mul]
  · have e2 : mob g u * conj (mob g v) - 1 =
        (u * conj v - 1) / ((g 1 0 * u + g 1 1) * conj (g 1 0 * v + g 1 1)) := by
      unfold mob
      rw [map_div₀, div_mul_div_comm, div_sub_one (mul_ne_zero hu hvc)]
      congr 1
      have hdet' : g 0 0 * conj (g 0 0) - g 0 1 * conj (g 0 1) = 1 := by
        rw [hg.1, hg.2] at hdet
        linear_combination hdet
      rw [hg.1, hg.2]
      simp only [map_add, map_mul, Complex.conj_conj]
      linear_combination (u * conj v - 1) * hdet'
    rw [e2, norm_div, norm_mul, Complex.norm_conj]

/-- The pole set of a Möbius map is null. -/
theorem s19m_pole_ae (g : SL2C) : ∀ᵐ w ∂volume, g 1 0 * w + g 1 1 ≠ 0 :=
  measure_eq_zero_iff_ae_notMem.mp ((fd_denom_finite g).measure_zero volume)

/-- Ball integrals of a measurable `Γ`-automorphic function are automorphic in the centre. -/
theorem s19m_ball_aut {g : SL2C} (hg : IsSU11 g) {k : ℂ → ℂ}
    (hk : ∀ᵐ w ∂(volume.restrict unitDiscExterior), k (mob g w) = k w) {z : ℂ}
    (hDz : g 1 0 * z + g 1 1 ≠ 0) (s : ℝ) :
    (∫ w in {w | w ∈ unitDiscExterior ∧ ‖w - mob g z‖ ≤ s * ‖w * conj (mob g z) - 1‖}, k w * rho w) =
      ∫ w in {w | w ∈ unitDiscExterior ∧ ‖w - z‖ ≤ s * ‖w * conj z - 1‖}, k w * rho w := by
  set B := {w | w ∈ unitDiscExterior ∧ ‖w - z‖ ≤ s * ‖w * conj z - 1‖} with hB
  set B' := {w | w ∈ unitDiscExterior ∧ ‖w - mob g z‖ ≤ s * ‖w * conj (mob g z) - 1‖} with hB'
  set S := B ∩ {w | g 1 0 * w + g 1 1 ≠ 0} with hS
  have hSm : MeasurableSet S := (s19m_ball_measurable z s).inter (fd_measurableSet_gen g)
  have hgen : ∀ w ∈ S, g 1 0 * w + g 1 1 ≠ 0 := fun w hw => hw.2
  have hDzn : 0 < ‖g 1 0 * z + g 1 1‖ := norm_pos_iff.mpr hDz
  -- membership transport
  have hmem : ∀ w, w ∈ unitDiscExterior → g 1 0 * w + g 1 1 ≠ 0 →
      (mob g w ∈ B' ↔ w ∈ B) := by
    intro w hw hDw
    obtain ⟨p1, p2⟩ := s19m_su11_pseudo hg hDw hDz
    have hDwn : 0 < ‖g 1 0 * w + g 1 1‖ := norm_pos_iff.mpr hDw
    have hpos : 0 < ‖g 1 0 * w + g 1 1‖ * ‖g 1 0 * z + g 1 1‖ := mul_pos hDwn hDzn
    have hext : mob g w ∈ unitDiscExterior := fd_mob_exterior hg hw hDw
    constructor
    · rintro ⟨-, h2⟩
      refine ⟨hw, ?_⟩
      rw [p1, p2, ← mul_div_assoc, div_le_div_iff_of_pos_right hpos] at h2
      exact h2
    · rintro ⟨-, h2⟩
      refine ⟨hext, ?_⟩
      rw [p1, p2, ← mul_div_assoc, div_le_div_iff_of_pos_right hpos]
      exact h2
  have hinj : InjOn (mob g) S := fun w1 h1 w2 h2 he => by
    rw [← (fd_inv_step g (hgen w1 h1)).2, ← (fd_inv_step g (hgen w2 h2)).2, he]
  have himg : mob g '' S =ᵐ[volume] B' := by
    refine eventuallyEqSet_iff.mpr ?_
    filter_upwards [s19m_pole_ae g⁻¹] with u hu
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact (hmem w hw.1.1 hw.2).mpr hw.1
    · intro huB
      have hstep := fd_inv_step g⁻¹ hu
      rw [inv_inv] at hstep
      have hwext : mob g⁻¹ u ∈ unitDiscExterior := fd_mob_exterior (isSU11_inv hg) huB.1 hu
      refine ⟨mob g⁻¹ u, ⟨(hmem _ hwext hstep.1).mp (by rw [hstep.2]; exact huB), hstep.1⟩, hstep.2⟩
  have hcv := integral_image_eq_integral_abs_det_fderiv_smul volume hSm
    (f' := fun x => (ContinuousLinearMap.toSpanSingleton ℂ (deriv (mob g) x)).restrictScalars ℝ)
    (fun x hx => ((fd_mob_differentiableAt g (hgen x hx)).hasDerivAt.hasFDerivAt.restrictScalars ℝ).hasFDerivWithinAt)
    hinj (fun w => k w * (rho w : ℂ))
  rw [← setIntegral_congr_set himg, hcv]
  have hSB : S =ᵐ[volume] B := by
    refine eventuallyEqSet_iff.mpr ?_
    filter_upwards [s19m_pole_ae g] with w hw
    exact ⟨fun h => h.1, fun h => ⟨h, hw⟩⟩
  rw [← setIntegral_congr_set hSB]
  have hext : MeasurableSet unitDiscExterior := (isOpen_lt continuous_const continuous_norm).measurableSet
  have hk' : ∀ᵐ w ∂volume, w ∈ unitDiscExterior → k (mob g w) = k w := (ae_restrict_iff' hext).mp hk
  refine setIntegral_congr_ae hSm ?_
  filter_upwards [hk'] with w hw hwS
  have hw1 : w ∈ unitDiscExterior := hwS.1.1
  rw [det_restrictScalars_toSpanSingleton, abs_of_nonneg (sq_nonneg _), hw hw1, Complex.real_smul,
    mul_left_comm, ← Complex.ofReal_mul, s19m_rho_pull hg hw1 (hgen w hwS)]

/-- `ρ` is integrable on every ball `B(z, s)`, `z ∈ 𝔻*`, and `∬_{B(z,s)} ρ = A_s`. -/
theorem s19m_rho_ball {z : ℂ} (hz : z ∈ unitDiscExterior) {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) :
    IntegrableOn rho {w | w ∈ unitDiscExterior ∧ ‖w - z‖ ≤ s * ‖w * conj z - 1‖} ∧
      (∫ w in {w | w ∈ unitDiscExterior ∧ ‖w - z‖ ≤ s * ‖w * conj z - 1‖}, rho w) =
        4 * π * s ^ 2 / (1 - s ^ 2) := by
  have hnn : 0 ≤ᵐ[volume.restrict {w | w ∈ unitDiscExterior ∧ ‖w - z‖ ≤ s * ‖w * conj z - 1‖}] rho :=
    Eventually.of_forall fun w => div_nonneg (by norm_num) (sq_nonneg _)
  have hA : 0 ≤ 4 * π * s ^ 2 / (1 - s ^ 2) := div_nonneg (by positivity) (by nlinarith)
  refine ⟨⟨s19m_rho_measurable.aestronglyMeasurable, ?_⟩, ?_⟩
  · rw [hasFiniteIntegral_iff_ofReal hnn, s19m_area_ball hz hs0 hs1]
    exact ENNReal.ofReal_lt_top
  · rw [integral_eq_lintegral_of_nonneg_ae hnn s19m_rho_measurable.aestronglyMeasurable,
      s19m_area_ball hz hs0 hs1, ENNReal.toReal_ofReal hA]

/-- The ball average of a bounded function is bounded by `C A_s`. -/
theorem s19m_ball_bound {k : ℂ → ℂ} {C : ℝ} (hC : ∀ᵐ w ∂(volume.restrict unitDiscExterior), ‖k w‖ ≤ C)
    {z : ℂ} (hz : z ∈ unitDiscExterior) {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) :
    ‖∫ w in {w | w ∈ unitDiscExterior ∧ ‖w - z‖ ≤ s * ‖w * conj z - 1‖}, k w * rho w‖ ≤
      C * (4 * π * s ^ 2 / (1 - s ^ 2)) := by
  obtain ⟨hi, he⟩ := s19m_rho_ball hz hs0 hs1
  have hsub : {w | w ∈ unitDiscExterior ∧ ‖w - z‖ ≤ s * ‖w * conj z - 1‖} ⊆ unitDiscExterior := fun w hw => hw.1
  have hC' := ae_restrict_of_ae_restrict_of_subset hsub hC
  refine (norm_integral_le_of_norm_le (hi.const_mul C) ?_).trans_eq ?_
  · filter_upwards [hC'] with w hw
    have hρ0 : 0 ≤ rho w := div_nonneg (by norm_num) (sq_nonneg _)
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hρ0]
    exact mul_le_mul_of_nonneg_right hw hρ0
  · rw [integral_const_mul, he]

/-- The ball integral of a measurable function is measurable in the centre. -/
theorem s19m_ball_fun_measurable {k : ℂ → ℂ} (hk : Measurable k) (s : ℝ) :
    Measurable fun z => ∫ w in {w | w ∈ unitDiscExterior ∧ ‖w - z‖ ≤ s * ‖w * conj z - 1‖}, k w * rho w := by
  have hext : MeasurableSet unitDiscExterior := (isOpen_lt continuous_const continuous_norm).measurableSet
  set E : Set (ℂ × ℂ) := {p | p.2 ∈ unitDiscExterior ∧ ‖p.2 - p.1‖ ≤ s * ‖p.2 * conj p.1 - 1‖} with hEdef
  have hE : MeasurableSet E :=
    (hext.preimage measurable_snd).inter (measurableSet_le
      (continuous_norm.comp (continuous_snd.sub continuous_fst)).measurable
      (continuous_const.mul (continuous_norm.comp ((continuous_snd.mul
        (Complex.continuous_conj.comp continuous_fst)).sub continuous_const))).measurable)
  have hg : Measurable fun p : ℂ × ℂ => k p.2 * (rho p.2 : ℂ) :=
    (hk.comp measurable_snd).mul (Complex.continuous_ofReal.measurable.comp (s19m_rho_measurable.comp measurable_snd))
  have hsm := StronglyMeasurable.integral_prod_right (ν := volume)
    (f := fun z w => E.indicator (fun p : ℂ × ℂ => k p.2 * (rho p.2 : ℂ)) (z, w))
    (hg.indicator hE).stronglyMeasurable
  have heq : (fun z => ∫ w, E.indicator (fun p : ℂ × ℂ => k p.2 * (rho p.2 : ℂ)) (z, w)) =
      fun z => ∫ w in {w | w ∈ unitDiscExterior ∧ ‖w - z‖ ≤ s * ‖w * conj z - 1‖}, k w * rho w := by
    funext z
    rw [← integral_indicator (s19m_ball_measurable z s)]
    rfl
  rw [← heq]
  exact hsm.measurable

/-- (U) Averaging the centre over `U = 𝔻*_{1/t}` and unfolding over the fundamental domain: there is `g_U` with
`g_U ρ ∈ L¹(F)`, `∬_F g_U ρ = A_t`, and `∬_U (∬_{B(z, s)} f ρ) ρ(z) = ∬_F (∬_{B(z, s)} f ρ) g_U(z) ρ(z)` for every
bounded measurable automorphic `f`. -/
theorem s19m_unfold {Γ : Subgroup SL2C} (hΓ : IsCofinite Γ) {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    ∃ gU : ℂ → ℂ, IntegrableOn (fun z => gU z * rho z) (fundDomain Γ) ∧
      (∫ z in fundDomain Γ, gU z * rho z) = ((4 * π * t ^ 2 / (1 - t ^ 2) : ℝ) : ℂ) ∧
      ∀ f : ℂ → ℂ, AEStronglyMeasurable f (volume.restrict unitDiscExterior) →
        (∃ C, ∀ᵐ z ∂(volume.restrict unitDiscExterior), ‖f z‖ ≤ C) →
        (∀ g ∈ Γ, ∀ᵐ z ∂(volume.restrict unitDiscExterior), f (mob g z) = f z) →
        ∀ s : ℝ, 0 < s → s < 1 →
          (∫ z in discExteriorR (1 / t),
              (∫ w in {w | w ∈ unitDiscExterior ∧ ‖w - z‖ ≤ s * ‖w * conj z - 1‖}, f w * rho w) * rho z) =
            ∫ z in fundDomain Γ,
              (∫ w in {w | w ∈ unitDiscExterior ∧ ‖w - z‖ ≤ s * ‖w * conj z - 1‖}, f w * rho w) * gU z * rho z := by
  have hr : 1 < 1 / t := by rw [one_lt_div ht0]; exact ht1
  have hext : MeasurableSet unitDiscExterior := (isOpen_lt continuous_const continuous_norm).measurableSet
  have hFm := fundDomain_measurable Γ
  have hdens : ∀ z ∈ fundDomain Γ, (patOrbitCount Γ (1 / t) z : ℂ) * (rho z : ℂ) =
      ((patOrbitDensity Γ (1 / t) z).toReal : ℂ) := by
    intro z hz
    have hρ0 : 0 ≤ rho z := div_nonneg (by norm_num) (sq_nonneg _)
    rw [pat_orbit_density_eq_count hΓ.1 hr (fundDomain_subset Γ hz), ENNReal.toReal_mul,
      ENNReal.toReal_ofReal hρ0, ENNReal.toReal_natCast]
    push_cast
    ring
  refine ⟨fun z => (patOrbitCount Γ (1 / t) z : ℂ), ?_, ?_, ?_⟩
  · exact (pat_orbit_real_integrable hΓ.1 hr).ofReal.congr_fun (fun z hz => (hdens z hz).symm) hFm
  · rw [setIntegral_congr_fun hFm hdens]
    have h1 := pat_complex_unfold hΓ.1 hr (h := fun _ => (1 : ℂ)) (C := 1) measurable_const
      (Eventually.of_forall fun _ => by simp) (fun _ _ => Eventually.of_forall fun _ => rfl)
    simp only [one_mul] at h1
    rw [← h1, integral_complex_ofReal, pat_rho_integral hr, one_div, s19m_area_conv ht0 ht1]
  · intro f hfm hfb hfa s hs0 hs1
    obtain ⟨k, hkm, hke, hka⟩ := pat_measurable_automorphic_representative hΓ.1 hfm hfa
    obtain ⟨C, hC⟩ := hfb
    have hall : ∀ᵐ w ∂volume, w ∈ unitDiscExterior → k w = f w := (ae_restrict_iff' hext).mp hke
    have hkb : ∀ᵐ w ∂(volume.restrict unitDiscExterior), ‖k w‖ ≤ C := by
      filter_upwards [hke, hC] with w h1 h2
      rw [h1]
      exact h2
    have hΦ : ∀ z, (∫ w in {w | w ∈ unitDiscExterior ∧ ‖w - z‖ ≤ s * ‖w * conj z - 1‖}, f w * rho w) =
        ∫ w in {w | w ∈ unitDiscExterior ∧ ‖w - z‖ ≤ s * ‖w * conj z - 1‖}, k w * rho w := by
      intro z
      refine setIntegral_congr_ae (s19m_ball_measurable z s) ?_
      filter_upwards [hall] with w hw hwB
      rw [hw hwB.1]
    simp only [hΦ]
    have hΦm := s19m_ball_fun_measurable hkm s
    have hΦb : ∀ᵐ z ∂(volume.restrict unitDiscExterior),
        ‖∫ w in {w | w ∈ unitDiscExterior ∧ ‖w - z‖ ≤ s * ‖w * conj z - 1‖}, k w * rho w‖ ≤
          C * (4 * π * s ^ 2 / (1 - s ^ 2)) :=
      ae_restrict_of_forall_mem hext fun z hz => s19m_ball_bound hkb hz hs0 hs1
    have hΦa : ∀ g ∈ Γ, ∀ᵐ z ∂(volume.restrict unitDiscExterior),
        (∫ w in {w | w ∈ unitDiscExterior ∧ ‖w - mob g z‖ ≤ s * ‖w * conj (mob g z) - 1‖}, k w * rho w) =
          ∫ w in {w | w ∈ unitDiscExterior ∧ ‖w - z‖ ≤ s * ‖w * conj z - 1‖}, k w * rho w := by
      intro g hg
      filter_upwards [ae_restrict_of_ae (s19m_pole_ae g)] with z hD
      exact s19m_ball_aut (hΓ.1.1 g hg) (hka g hg) hD s
    rw [pat_complex_unfold hΓ.1 hr hΦm hΦb hΦa]
    refine setIntegral_congr_fun hFm fun z hz => ?_
    rw [mul_assoc, hdens z hz]

/-- The ball integral of an a.e.-measurable function is measurable in the centre. -/
theorem s19m_ball_fun_measurable' {f : ℂ → ℂ} (hfm : AEStronglyMeasurable f (volume.restrict unitDiscExterior))
    (s : ℝ) :
    Measurable fun z => ∫ w in {w | w ∈ unitDiscExterior ∧ ‖w - z‖ ≤ s * ‖w * conj z - 1‖}, f w * rho w := by
  have hext : MeasurableSet unitDiscExterior := (isOpen_lt continuous_const continuous_norm).measurableSet
  have hall : ∀ᵐ w ∂volume, w ∈ unitDiscExterior → hfm.mk f w = f w :=
    (ae_restrict_iff' hext).mp hfm.ae_eq_mk.symm
  have heq : (fun z => ∫ w in {w | w ∈ unitDiscExterior ∧ ‖w - z‖ ≤ s * ‖w * conj z - 1‖}, hfm.mk f w * rho w) =
      fun z => ∫ w in {w | w ∈ unitDiscExterior ∧ ‖w - z‖ ≤ s * ‖w * conj z - 1‖}, f w * rho w := by
    funext z
    refine setIntegral_congr_ae (s19m_ball_measurable z s) ?_
    filter_upwards [hall] with w hw hwB
    rw [hw hwB.1]
  rw [← heq]
  exact s19m_ball_fun_measurable hfm.stronglyMeasurable_mk.measurable s

/-- `A_{s⊕t} - A_{s⊖t} = 16π s t/((1 - s²)(1 - t²))`. -/
theorem s19m_E_eq {s t : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (ht0 : 0 < t) (ht1 : t < 1) :
    4 * π * ((s + t) / (1 + s * t)) ^ 2 / (1 - ((s + t) / (1 + s * t)) ^ 2) -
        4 * π * ((s - t) / (1 - s * t)) ^ 2 / (1 - ((s - t) / (1 - s * t)) ^ 2) =
      16 * π * s * t / ((1 - s ^ 2) * (1 - t ^ 2)) := by
  have h1 : 1 + s * t ≠ 0 := by nlinarith
  have h2 : 1 - s * t ≠ 0 := by nlinarith
  have h3 : 1 - s ^ 2 ≠ 0 := by nlinarith
  have h4 : 1 - t ^ 2 ≠ 0 := by nlinarith
  have e1 : 1 - ((s + t) / (1 + s * t)) ^ 2 = (1 - s ^ 2) * (1 - t ^ 2) / (1 + s * t) ^ 2 := by
    field_simp
    ring
  have e2 : 1 - ((s - t) / (1 - s * t)) ^ 2 = (1 - s ^ 2) * (1 - t ^ 2) / (1 - s * t) ^ 2 := by
    field_simp
    ring
  rw [e1, e2]
  field_simp
  ring

/-- Averaging the centre over `U = 𝔻*_{1/t}`: `‖A_t ∬_{𝔻*_{1/s}} hρ - ∬_U (∬_{B(z,s)} hρ) ρ(z)‖ ≤ C E A_t`,
rewritten over `F` by the unfolding identity. -/
theorem s19m_avg {h : ℂ → ℂ} (hmeas : AEStronglyMeasurable h (volume.restrict unitDiscExterior)) {C : ℝ}
    (hC : ∀ᵐ z ∂(volume.restrict unitDiscExterior), ‖h z‖ ≤ C) {t s : ℝ} (ht0 : 0 < t) (hts : t < s) (hs1 : s < 1)
    {F : Set ℂ} {gU : ℂ → ℂ}
    (hU : (∫ z in discExteriorR (1 / t),
        (∫ w in {w | w ∈ unitDiscExterior ∧ ‖w - z‖ ≤ s * ‖w * conj z - 1‖}, h w * rho w) * rho z) =
      ∫ z in F, (∫ w in {w | w ∈ unitDiscExterior ∧ ‖w - z‖ ≤ s * ‖w * conj z - 1‖}, h w * rho w) * gU z * rho z) :
    ‖((4 * π * t ^ 2 / (1 - t ^ 2) : ℝ) : ℂ) * (∫ w in discExteriorR (1 / s), h w * rho w) -
        ∫ z in F, (∫ w in {w | w ∈ unitDiscExterior ∧ ‖w - z‖ ≤ s * ‖w * conj z - 1‖}, h w * rho w) * gU z * rho z‖ ≤
      C * (16 * π * s * t / ((1 - s ^ 2) * (1 - t ^ 2))) * (4 * π * t ^ 2 / (1 - t ^ 2)) := by
  have hs0 : 0 < s := by linarith
  have ht1 : t < 1 := by linarith
  have hr : 1 < 1 / t := by rw [one_lt_div ht0]; exact ht1
  have hext : MeasurableSet unitDiscExterior := (isOpen_lt continuous_const continuous_norm).measurableSet
  have hUm : MeasurableSet (discExteriorR (1 / t)) := pat_discExteriorR_measurable _
  have hAt : (∫ z in discExteriorR (1 / t), rho z) = 4 * π * t ^ 2 / (1 - t ^ 2) := by
    rw [pat_rho_integral hr, one_div, s19m_area_conv ht0 ht1]
  set Iinf := ∫ w in discExteriorR (1 / s), h w * rho w with hI
  have hconst : ((4 * π * t ^ 2 / (1 - t ^ 2) : ℝ) : ℂ) * Iinf = ∫ z in discExteriorR (1 / t), Iinf * (rho z : ℂ) := by
    rw [integral_const_mul, integral_complex_ofReal, hAt]
    ring
  have hi1 : IntegrableOn (fun z => Iinf * (rho z : ℂ)) (discExteriorR (1 / t)) :=
    (pat_rho_integrable hr).ofReal.const_mul Iinf
  have hi2 : IntegrableOn (fun z => (∫ w in {w | w ∈ unitDiscExterior ∧ ‖w - z‖ ≤ s * ‖w * conj z - 1‖},
      h w * rho w) * (rho z : ℂ)) (discExteriorR (1 / t)) :=
    s19m_bdd_integrableOn (s19m_ball_fun_measurable' hmeas s).aestronglyMeasurable
      (ae_restrict_of_forall_mem hext fun z hz => s19m_ball_bound hC hz hs0 hs1) hUm hr subset_rfl
  rw [← hU, hconst, ← integral_sub hi1 hi2]
  have hρi : IntegrableOn rho (discExteriorR (1 / t)) := pat_rho_integrable hr
  refine (norm_integral_le_of_norm_le
    (hρi.const_mul (C * (16 * π * s * t / ((1 - s ^ 2) * (1 - t ^ 2))))) ?_).trans_eq ?_
  · filter_upwards [ae_restrict_mem hUm] with z hz
    have hρ0 : 0 ≤ rho z := div_nonneg (by norm_num) (sq_nonneg _)
    have hz' : 1 ≤ t * ‖z‖ := by
      have := hz.2
      rw [div_le_iff₀ ht0] at this
      linarith
    have hth := s19m_thicken hmeas hC ht0 hts hs1 hz'
    rw [s19m_E_eq hs0 hs1 ht0 ht1] at hth
    rw [← sub_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hρ0]
    exact mul_le_mul_of_nonneg_right hth hρ0
  · rw [integral_const_mul, hAt]

/-- **Lemma 1.9 from CORE.** `hcore` is the ball-average mixing statement for `Γ` (stage 2 of W-MIX). -/
theorem s19m_lemma_1_9_of_core {Γ : Subgroup SL2C} (hΓ : IsCofinite Γ) {h : ℂ → ℂ}
    (hmeas : AEStronglyMeasurable h (volume.restrict unitDiscExterior))
    (hbdd : ∃ C, ∀ᵐ z ∂(volume.restrict unitDiscExterior), ‖h z‖ ≤ C)
    (haut : ∀ g ∈ Γ, ∀ᵐ z ∂(volume.restrict unitDiscExterior), h (mob g z) = h z)
    (hcore : ∀ f g : ℂ → ℂ, AEStronglyMeasurable f (volume.restrict unitDiscExterior) →
      (∃ C, ∀ᵐ z ∂(volume.restrict unitDiscExterior), ‖f z‖ ≤ C) →
      (∀ γ ∈ Γ, ∀ᵐ z ∂(volume.restrict unitDiscExterior), f (mob γ z) = f z) →
      IntegrableOn (fun z => g z * rho z) (fundDomain Γ) →
      Tendsto (fun s : ℝ => ∫ z in fundDomain Γ,
          ((∫ w in {w | w ∈ unitDiscExterior ∧ ‖w - z‖ ≤ s * ‖w * conj z - 1‖}, f w * rho w) /
            ((4 * π * s ^ 2 / (1 - s ^ 2) : ℝ) : ℂ)) * g z * rho z)
        (𝓝[<] 1)
        (𝓝 ((∫ z in fundDomain Γ, f z * rho z) * (∫ z in fundDomain Γ, g z * rho z) /
          ((hypArea Γ).toReal : ℂ)))) :
    Tendsto (fun r : ℝ => ((hypArea Γ).toReal / (∫ z in discExteriorR r, rho z) : ℂ) *
        ∫ z in discExteriorR r, h z * rho z)
      (𝓝[>] 1) (𝓝 (quotientIntegral Γ fun z => h z * rho z)) := by
  obtain ⟨C0, hC0⟩ := hbdd
  set C := max C0 0 with hCdef
  have hC : ∀ᵐ z ∂(volume.restrict unitDiscExterior), ‖h z‖ ≤ C := by
    filter_upwards [hC0] with z hz
    exact hz.trans (le_max_left _ _)
  have hC0' : 0 ≤ C := le_max_right _ _
  set A := (hypArea Γ).toReal with hAdef
  have hA : 0 < A := pat_hypArea_toReal_pos hΓ
  set L := ∫ z in fundDomain Γ, h z * rho z with hLdef
  show Tendsto _ _ (𝓝 L)
  rw [Metric.tendsto_nhds]
  intro ε hε
  -- the radius `t` of the averaging ball
  set t := min (1 / 4) (ε / (32 * (A * C + 1))) with htdef
  have hAC : 0 ≤ A * C := mul_nonneg hA.le hC0'
  have ht0 : 0 < t := lt_min (by norm_num) (div_pos hε (by positivity))
  have ht4 : t ≤ 1 / 4 := min_le_left _ _
  have htε : t ≤ ε / (32 * (A * C + 1)) := min_le_right _ _
  have ht1 : t < 1 := by linarith
  set At := 4 * π * t ^ 2 / (1 - t ^ 2) with hAtdef
  have hAt : 0 < At := div_pos (by positivity) (by nlinarith)
  obtain ⟨gU, hgi, hgA, hgU⟩ := s19m_unfold hΓ ht0 ht1
  have hJ := hcore h gU hmeas ⟨C, hC⟩ haut hgi
  rw [hgA] at hJ
  -- `r ↦ r⁻¹` maps `𝓝[>] 1` to `𝓝[<] 1`
  have hinv : Tendsto (fun r : ℝ => r⁻¹) (𝓝[>] 1) (𝓝[<] 1) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have := tendsto_inv₀ (one_ne_zero : (1 : ℝ) ≠ 0)
      simpa using this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with r hr
      exact inv_lt_one_of_one_lt₀ (mem_Ioi.mp hr)
  have hJ' := ((hJ.comp hinv).const_mul ((A : ℂ) / (At : ℂ)))
  have hlim : (A : ℂ) / (At : ℂ) * (L * (At : ℂ) / (A : ℂ)) = L := by
    have h1 : (A : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hA.ne'
    have h2 : (At : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hAt.ne'
    field_simp
  rw [hlim, Metric.tendsto_nhds] at hJ'
  have hev := hJ' (ε / 2) (half_pos hε)
  have hr2 : ∀ᶠ r in 𝓝[>] (1 : ℝ), r < 2 :=
    nhdsWithin_le_nhds (Iio_mem_nhds (by norm_num : (1 : ℝ) < 2))
  filter_upwards [hev, hr2, self_mem_nhdsWithin] with r hJr hr2 hr1
  have hr1' : 1 < r := hr1
  set s := r⁻¹ with hsdef
  have hs0 : 0 < s := inv_pos.mpr (by linarith)
  have hs1 : s < 1 := inv_lt_one_of_one_lt₀ hr1'
  have hs2 : 1 / 2 < s := by rw [hsdef]; exact (inv_lt_inv₀ (by norm_num) (by linarith)).mpr hr2 |>.trans_eq' (by norm_num)
  have hts : t < s := by linarith
  have hsr : 1 / s = r := by rw [hsdef, one_div, inv_inv]
  set As := 4 * π * s ^ 2 / (1 - s ^ 2) with hAsdef
  have hAs : 0 < As := div_pos (by positivity) (by nlinarith)
  have hρr : (∫ z in discExteriorR r, rho z) = As := by
    rw [pat_rho_integral hr1', hAsdef, ← s19m_area_conv hs0 hs1, hsdef, inv_inv]
  set Iinf := ∫ z in discExteriorR r, h z * rho z with hIdef
  set J' := ∫ z in fundDomain Γ,
    (∫ w in {w | w ∈ unitDiscExterior ∧ ‖w - z‖ ≤ s * ‖w * conj z - 1‖}, h w * rho w) * gU z * rho z with hJ'def
  have havg := s19m_avg hmeas hC ht0 hts hs1 (hgU h hmeas ⟨C, hC⟩ haut s hs0 hs1)
  rw [hsr] at havg
  -- the core average at `s` is `J'/A_s`
  have hJs : (∫ z in fundDomain Γ,
      ((∫ w in {w | w ∈ unitDiscExterior ∧ ‖w - z‖ ≤ s * ‖w * conj z - 1‖}, h w * rho w) /
        ((As : ℝ) : ℂ)) * gU z * rho z) = J' / (As : ℂ) := by
    rw [hJ'def, ← integral_div]
    congr 1
    funext z
    ring
  have hJr' : dist ((A : ℂ) / (At : ℂ) * (J' / (As : ℂ))) L < ε / 2 := by
    have := hJr
    simp only [Function.comp] at this
    rw [← hsdef, hJs] at this
    exact this
  -- decomposition
  set K : ℝ := A / (At * As) with hKdef
  have hK0 : 0 ≤ K := div_nonneg hA.le (mul_pos hAt hAs).le
  have hdec : ((A : ℂ) / ((As : ℝ) : ℂ)) * Iinf - L =
      (K : ℂ) * ((At : ℂ) * Iinf - J') + ((A : ℂ) / (At : ℂ) * (J' / (As : ℂ)) - L) := by
    have h1 : (At : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hAt.ne'
    have h2 : (As : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hAs.ne'
    rw [hKdef]
    push_cast
    field_simp
    ring
  have hbound1 : ‖(K : ℂ) * ((At : ℂ) * Iinf - J')‖ ≤ 9 * (A * C) * t := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hK0]
    refine (mul_le_mul_of_nonneg_left havg hK0).trans ?_
    have e : K * (C * (16 * π * s * t / ((1 - s ^ 2) * (1 - t ^ 2))) * At) =
        A * C * (4 * t / (s * (1 - t ^ 2))) := by
      rw [hKdef, hAtdef, hAsdef]
      have : 1 - s ^ 2 ≠ 0 := by nlinarith
      have : 1 - t ^ 2 ≠ 0 := by nlinarith
      field_simp
      ring
    have hq : 4 * t / (s * (1 - t ^ 2)) ≤ 9 * t := by
      have ht2 : t ^ 2 ≤ 1 / 16 := by nlinarith
      have h15 : 15 / 32 ≤ s * (1 - t ^ 2) := by
        nlinarith [mul_nonneg (show (0 : ℝ) ≤ s - 1 / 2 by linarith) (show (0 : ℝ) ≤ 1 - t ^ 2 by linarith)]
      rw [div_le_iff₀ (by linarith)]
      nlinarith [mul_le_mul_of_nonneg_left h15 (by positivity : (0 : ℝ) ≤ 9 * t)]
    rw [e]
    exact (mul_le_mul_of_nonneg_left hq hAC).trans_eq (by ring)
  rw [dist_eq_norm]
  show ‖((A : ℂ) / ((∫ z in discExteriorR r, rho z : ℝ) : ℂ)) * Iinf - L‖ < ε
  rw [hρr, hdec]
  have h9 : 9 * (A * C) * t < ε / 2 := by
    have hpos : 0 < 32 * (A * C + 1) := by positivity
    have := mul_le_mul_of_nonneg_left htε (show (0 : ℝ) ≤ 9 * (A * C) by positivity)
    have e : 9 * (A * C) * (ε / (32 * (A * C + 1))) ≤ 9 * ε / 32 := by
      rw [mul_div_assoc', div_le_div_iff₀ hpos (by norm_num)]
      nlinarith
    linarith
  rw [dist_eq_norm] at hJr'
  calc _ ≤ ‖(K : ℂ) * ((At : ℂ) * Iinf - J')‖ + ‖(A : ℂ) / (At : ℂ) * (J' / (As : ℂ)) - L‖ := norm_add_le _ _
    _ < ε / 2 + ε / 2 := add_lt_add_of_le_of_lt (hbound1.trans h9.le) hJr'
    _ = ε := add_halves ε

end TakhtajanTeo
