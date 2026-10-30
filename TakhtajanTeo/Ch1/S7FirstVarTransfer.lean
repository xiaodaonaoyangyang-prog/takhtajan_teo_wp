import TakhtajanTeo.Ch1.WPChangeOfVariables
import LiZhongQC.Ch04.S16_Quasicircles

/-!
# Program G, F1 piece R3: weighted transfer through a `K`-q.c. plane map (下属1)

`s7g_transfer`: `∫_𝕌 |m|² J_W / d_{W(𝕌)}(W)² ≤ C(K) ∫_𝕌 |m|² ρ_𝕌` for every `K`-q.c. map `W` of `ℂ` onto `ℂ` and every
harmonic `m = (u - ū)²/2 · φ̄` on `𝕌`, with `C` depending only on `K`. Proof:
* `s7g_r3_maxp`: maximum principle for plane homeomorphisms;
* `s7g_r3_wqs`: weak quasisymmetry from Teichmüller's circle distortion `tp_a_circle`;
* `s7g_r3_dist`, `s7g_r3_cell`: Whitney distortion and the cell bound `∫_B J/d² ≤ π λ(K)²`;
* `s7g_r3_mean`: mean value of `|φ|²` on Whitney balls; Tonelli.
-/

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal NNReal ComplexConjugate Classical Real
noncomputable section
namespace TakhtajanTeo
open LiZhongQC

/-- Maximum principle for a homeomorphism of the plane: a point of the closed disc `B̄(v, r)` is not farther
from `e v` than some point of the circle `|s - v| = r` (intermediate value along the ray from `e v`). -/
theorem s7g_r3_maxp (e : ℂ ≃ₜ ℂ) (v t : ℂ) {r : ℝ} (hr : 0 < r) (ht : ‖t - v‖ ≤ r) :
    ∃ s : ℂ, ‖s - v‖ = r ∧ ‖e t - e v‖ ≤ ‖e s - e v‖ := by
  by_cases htv : t = v
  · refine ⟨v + r, by simp [abs_of_pos hr], ?_⟩
    rw [htv, sub_self, norm_zero]
    exact norm_nonneg _
  have hac : e t - e v ≠ 0 := sub_ne_zero.2 fun h => htv (e.injective h)
  have hn : 0 < ‖e t - e v‖ := norm_pos_iff.2 hac
  obtain ⟨C, hC⟩ := ((isCompact_closedBall v r).image e.continuous).isBounded.exists_norm_le
  set T : ℝ := (|C| + ‖e v‖ + 1) / ‖e t - e v‖ + 1 with hTd
  have hT0 : 0 ≤ (|C| + ‖e v‖ + 1) / ‖e t - e v‖ := by positivity
  have hT1 : 1 ≤ T := by linarith
  have hγ : ∀ τ : ℝ, 0 ≤ τ → ‖(e v + (τ : ℂ) * (e t - e v)) - e v‖ = τ * ‖e t - e v‖ := by
    intro τ hτ
    rw [add_sub_cancel_left, norm_mul, Complex.norm_real, Real.norm_of_nonneg hτ]
  have hcont : Continuous fun τ : ℝ => ‖e.symm (e v + (τ : ℂ) * (e t - e v)) - v‖ := by
    have hc : Continuous fun τ : ℝ => e v + (τ : ℂ) * (e t - e v) := by fun_prop
    exact continuous_norm.comp ((e.symm.continuous.comp hc).sub continuous_const)
  have h1 : ‖e.symm (e v + ((1 : ℝ) : ℂ) * (e t - e v)) - v‖ ≤ r := by
    rw [Complex.ofReal_one, one_mul, add_sub_cancel, e.symm_apply_apply]
    exact ht
  have hTr : r ≤ ‖e.symm (e v + (T : ℂ) * (e t - e v)) - v‖ := by
    by_contra hlt
    push Not at hlt
    have hmem : e v + (T : ℂ) * (e t - e v) ∈ e '' closedBall v r :=
      ⟨e.symm (e v + (T : ℂ) * (e t - e v)), mem_closedBall.2 (by rw [dist_eq_norm]; exact hlt.le),
        e.apply_symm_apply _⟩
    have hb := hC _ hmem
    have hg := hγ T (by linarith)
    have hle : ‖(e v + (T : ℂ) * (e t - e v)) - e v‖ ≤ |C| + ‖e v‖ :=
      (norm_sub_le _ _).trans (by linarith [le_abs_self C])
    rw [hg] at hle
    have hTn : T * ‖e t - e v‖ = |C| + ‖e v‖ + 1 + ‖e t - e v‖ := by
      rw [hTd, add_mul, div_mul_cancel₀ _ hn.ne', one_mul]
    linarith
  obtain ⟨τ, hτ, hτr⟩ := intermediate_value_Icc hT1 hcont.continuousOn ⟨h1, hTr⟩
  refine ⟨e.symm (e v + (τ : ℂ) * (e t - e v)), hτr, ?_⟩
  rw [e.apply_symm_apply, hγ τ (by linarith [hτ.1])]
  nlinarith [hτ.1]

/-- Weak quasisymmetry of a `K`-q.c. plane map, from Teichmüller's circle distortion and `s7g_r3_maxp`:
`|t - v| ≤ |s - v|` implies `|W t - W v| ≤ λ(K) |W s - W v|`. -/
theorem s7g_r3_wqs {W : ℂ → ℂ} {K : ℝ} (hW : IsKQC W univ K) (hs : W '' univ = univ) {v t s : ℂ}
    (hts : ‖t - v‖ ≤ ‖s - v‖) (hsv : 0 < ‖s - v‖) :
    ‖W t - W v‖ ≤ lambdaInv K * ‖W s - W v‖ := by
  obtain ⟨e, he⟩ := t1_homeomorph hW hs
  obtain ⟨s', hs', hle⟩ := s7g_r3_maxp e v t hsv hts
  rw [he] at hle
  exact hle.trans (tp_a_circle hW hs hsv hs' rfl)

/-- Whitney distortion: on `B = B(v, Im v / 7)`, `|W t' - W t| ≤ λ(K) d_{W(𝕌)}(W t)`. -/
theorem s7g_r3_dist {W : ℂ → ℂ} {K : ℝ} (hW : IsKQC W univ K) (hs : W '' univ = univ) {v t t' : ℂ}
    (hv : v ∈ upperHalf) (ht : t ∈ ball v (v.im / 7)) (ht' : t' ∈ ball v (v.im / 7)) :
    ‖W t' - W t‖ ≤ lambdaInv K * infDist (W t) (W '' upperHalf)ᶜ := by
  have hinj : Function.Injective W := fun a b hab => hW.2.2.1.2.1 (mem_univ a) (mem_univ b) hab
  have hlam : 0 < lambdaInv K := zero_lt_one.trans_le (td_one_le_lambdaInv hW.2.1)
  have hvim : 0 < v.im := hv
  have htv : ‖t - v‖ < v.im / 7 := by simpa [dist_eq_norm] using ht
  have ht'v : ‖t' - v‖ < v.im / 7 := by simpa [dist_eq_norm] using ht'
  have htim : 6 * v.im / 7 < t.im := by
    have := abs_lt.1 ((abs_im_le_norm (t - v)).trans_lt htv)
    simp only [Complex.sub_im] at this
    linarith [this.1]
  have hne : ((W '' upperHalf)ᶜ).Nonempty := by
    refine ⟨W (-I), fun hmem => ?_⟩
    obtain ⟨x, hx, hxe⟩ := hmem
    have := hinj hxe
    rw [this] at hx
    have h0 : (0 : ℝ) < (-I).im := hx
    simp only [Complex.neg_im, Complex.I_im] at h0
    linarith
  have hmain : ‖W t' - W t‖ / lambdaInv K ≤ infDist (W t) (W '' upperHalf)ᶜ := by
    rw [le_infDist hne]
    intro p hp
    obtain ⟨s, -, rfl⟩ : p ∈ W '' univ := by rw [hs]; exact mem_univ p
    have hsU : ¬ (0 < s.im) := fun h => hp ⟨s, h, rfl⟩
    have hst : t.im ≤ ‖s - t‖ := by
      have := abs_le.1 ((abs_im_le_norm (s - t)))
      simp only [Complex.sub_im] at this
      linarith [this.1]
    have ht't : ‖t' - t‖ ≤ ‖s - t‖ := by
      have : ‖t' - t‖ ≤ ‖t' - v‖ + ‖t - v‖ := by
        calc ‖t' - t‖ = ‖(t' - v) - (t - v)‖ := by ring_nf
          _ ≤ ‖t' - v‖ + ‖t - v‖ := norm_sub_le _ _
      linarith
    have hpos : 0 < ‖s - t‖ := by linarith
    have hq := s7g_r3_wqs hW hs ht't hpos
    rw [div_le_iff₀ hlam, dist_eq_norm, norm_sub_rev (W t) (W s)]
    linarith
  rwa [div_le_iff₀ hlam, mul_comm] at hmain

/-- Whitney cell bound: `∫_B J_W / d_{W(𝕌)}(W)² ≤ π λ(K)²` on `B = B(v, Im v / 7)`. -/
theorem s7g_r3_cell {W : ℂ → ℂ} {K : ℝ} (hW : IsKQC W univ K) (hs : W '' univ = univ) {v : ℂ}
    (hv : v ∈ upperHalf) :
    (∫⁻ u in ball v (v.im / 7), ENNReal.ofReal (jacobian W u) /
        ENNReal.ofReal (infDist (W u) (W '' upperHalf)ᶜ) ^ 2) ≤
      ENNReal.ofReal (lambdaInv K ^ 2) * NNReal.pi := by
  set B : Set ℂ := ball v (v.im / 7) with hB
  set A : ℝ≥0∞ := volume (W '' B) with hAd
  set c : ℝ≥0∞ := ENNReal.ofReal (lambdaInv K ^ 2) * NNReal.pi with hc
  have hlam : 0 < lambdaInv K := zero_lt_one.trans_le (td_one_le_lambdaInv hW.2.1)
  have hvim : 0 < v.im := hv
  have hBK : IsKQC W B K := nx_isKQC_restrict hW isOpen_ball (subset_univ _)
  have hJ : (∫⁻ u in B, ENNReal.ofReal (jacobian W u)) = A := by
    have h := QCV.qcv_lintegral_image_eq hBK (fun _ => (1 : ℝ≥0∞))
    simp only [mul_one, setLIntegral_one] at h
    exact h.symm
  obtain ⟨e, he⟩ := t1_homeomorph hW hs
  have hA0 : A ≠ 0 := by
    have hopen : IsOpen (W '' B) := by rw [← he]; exact e.isOpenMap _ isOpen_ball
    have hne : (W '' B).Nonempty := ⟨W v, v, mem_ball_self (by positivity), rfl⟩
    exact (hopen.measure_pos volume hne).ne'
  have hpt : ∀ u ∈ B, A ≤ c * ENNReal.ofReal (infDist (W u) (W '' upperHalf)ᶜ) ^ 2 := by
    intro u hu
    have hsub : W '' B ⊆ closedBall (W u) (lambdaInv K * infDist (W u) (W '' upperHalf)ᶜ) := by
      rintro _ ⟨t', ht', rfl⟩
      rw [mem_closedBall, dist_eq_norm]
      exact s7g_r3_dist hW hs hv hu ht'
    calc A ≤ volume (closedBall (W u) (lambdaInv K * infDist (W u) (W '' upperHalf)ᶜ)) := measure_mono hsub
      _ = c * ENNReal.ofReal (infDist (W u) (W '' upperHalf)ᶜ) ^ 2 := by
        rw [Complex.volume_closedBall, hc, ENNReal.ofReal_mul hlam.le, mul_pow,
          ENNReal.ofReal_pow hlam.le]
        ring
  have hAt : A ≠ ∞ := by
    refine ne_top_of_le_ne_top ?_ (hpt v (mem_ball_self (by positivity)))
    exact ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.coe_ne_top)
      (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
  have hct : c ≠ ∞ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.coe_ne_top
  have hkey : ∀ u ∈ B, ENNReal.ofReal (jacobian W u) / ENNReal.ofReal (infDist (W u) (W '' upperHalf)ᶜ) ^ 2 ≤
      ENNReal.ofReal (jacobian W u) * (A⁻¹ * c) := by
    intro u hu
    set x := ENNReal.ofReal (infDist (W u) (W '' upperHalf)ᶜ) ^ 2 with hx
    have hAx : A / x ≤ c := ENNReal.div_le_of_le_mul (hpt u hu)
    have hinv : x⁻¹ ≤ A⁻¹ * c := by
      calc x⁻¹ = A⁻¹ * (A / x) := by
            rw [div_eq_mul_inv, ← mul_assoc, ENNReal.inv_mul_cancel hA0 hAt, one_mul]
        _ ≤ A⁻¹ * c := by gcongr
    rw [div_eq_mul_inv]
    gcongr
  calc (∫⁻ u in B, ENNReal.ofReal (jacobian W u) / ENNReal.ofReal (infDist (W u) (W '' upperHalf)ᶜ) ^ 2)
      ≤ ∫⁻ u in B, ENNReal.ofReal (jacobian W u) * (A⁻¹ * c) := setLIntegral_mono' measurableSet_ball hkey
    _ = A * (A⁻¹ * c) := by
        rw [lintegral_mul_const' _ _ (ENNReal.mul_ne_top (ENNReal.inv_ne_top.2 hA0) hct), hJ]
    _ = c := by rw [← mul_assoc, ENNReal.mul_inv_cancel hA0 hAt, one_mul]

/-- `|(w - w̄)²/2 · ā| = 2 (Im w)² |a|`. -/
theorem s7g_r3_norm_m (w a : ℂ) : ‖(w - conj w) ^ 2 / 2 * conj a‖ = 2 * w.im ^ 2 * ‖a‖ := by
  have h : w - conj w = ((2 * w.im : ℝ) : ℂ) * I := by
    rw [Complex.sub_conj]
  rw [h, norm_mul, norm_div, norm_pow, norm_mul, Complex.norm_real, Complex.norm_I, Complex.norm_conj,
    Real.norm_eq_abs, mul_one, sq_abs, show ‖(2 : ℂ)‖ = 2 by norm_num]
  ring

/-- Mean value on Whitney balls: `|m(u)|² ≤ (12288/(49π)) ∫_{B(u, Im u/8)} |m|² ρ_𝕌`. -/
theorem s7g_r3_mean {m φ : ℂ → ℂ} (hφ : DifferentiableOn ℂ φ upperHalf)
    (hm : ∀ u ∈ upperHalf, m u = (u - conj u) ^ 2 / 2 * conj (φ u)) {u : ℂ} (hu : u ∈ upperHalf) :
    ‖m u‖ₑ ^ 2 ≤ ENNReal.ofReal (12288 / (49 * π)) *
      ∫⁻ w in ball u (u.im / 8), ‖m w‖ₑ ^ 2 * ENNReal.ofReal (rhoU w) := by
  have hy : 0 < u.im := hu
  set s : ℝ := u.im / 8 with hsd
  have hs : 0 < s := by positivity
  have hwim : ∀ w ∈ ball u s, 7 * u.im / 8 < w.im := by
    intro w hw
    have hw' : ‖w - u‖ < s := by simpa [dist_eq_norm] using hw
    have := abs_lt.1 ((abs_im_le_norm (w - u)).trans_lt hw')
    simp only [Complex.sub_im] at this
    linarith [this.1]
  have hsub : ball u s ⊆ upperHalf := by
    intro w hw
    show 0 < w.im
    linarith [hwim w hw]
  set F : ℂ → ℂ := fun ζ => φ (u + ζ) with hF
  have hFd : DifferentiableOn ℂ F (ball (0 : ℂ) s) := by
    refine hφ.comp (by fun_prop) fun ζ hζ => hsub ?_
    simpa [dist_eq_norm] using hζ
  have hmv := WPCV.wpcv_mean_value_sq hs hFd
  have htr : (∫⁻ ζ in ball (0 : ℂ) s, (‖F ζ‖₊ : ℝ≥0∞) ^ 2) = ∫⁻ w in ball u s, (‖φ w‖₊ : ℝ≥0∞) ^ 2 := by
    rw [← lintegral_indicator measurableSet_ball, ← lintegral_indicator measurableSet_ball,
      ← lintegral_add_left_eq_self (fun w => (ball u s).indicator (fun w => (‖φ w‖₊ : ℝ≥0∞) ^ 2) w) u]
    congr 1
    funext ζ
    by_cases hζ : ζ ∈ ball (0 : ℂ) s
    · have h2 : u + ζ ∈ ball u s := by simpa [dist_eq_norm] using hζ
      rw [indicator_of_mem hζ, indicator_of_mem h2]
    · have h2 : u + ζ ∉ ball u s := by simpa [dist_eq_norm] using hζ
      rw [indicator_of_notMem hζ, indicator_of_notMem h2]
  rw [htr] at hmv
  simp only [hF, add_zero] at hmv
  have hpt : ∀ w ∈ ball u s, (‖φ w‖₊ : ℝ≥0∞) ^ 2 ≤
      ENNReal.ofReal (16 / (49 * u.im ^ 2)) * (‖m w‖ₑ ^ 2 * ENNReal.ofReal (rhoU w)) := by
    intro w hw
    have hw0 := hwim w hw
    have hwpos : 0 < w.im := by linarith
    have hmw : ‖m w‖ₑ ^ 2 = ENNReal.ofReal ((2 * w.im ^ 2 * ‖φ w‖) ^ 2) := by
      rw [hm w (hsub hw), ← ofReal_norm, s7g_r3_norm_m, ENNReal.ofReal_pow (by positivity)]
    have hφw : (‖φ w‖₊ : ℝ≥0∞) ^ 2 = ENNReal.ofReal (‖φ w‖ ^ 2) := by
      rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
      rfl
    rw [hmw, hφw, ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    unfold rhoU
    have hq : (7 * u.im / 8) ^ 2 ≤ w.im ^ 2 := by nlinarith
    rw [show 16 / (49 * u.im ^ 2) * ((2 * w.im ^ 2 * ‖φ w‖) ^ 2 * (w.im ^ 2)⁻¹) =
      ‖φ w‖ ^ 2 * (w.im ^ 2 / (7 * u.im / 8) ^ 2) by field_simp; ring]
    have h1 : 1 ≤ w.im ^ 2 / (7 * u.im / 8) ^ 2 := by
      rw [le_div_iff₀ (by positivity)]; linarith
    nlinarith [sq_nonneg ‖φ w‖]
  have hint : (∫⁻ w in ball u s, (‖φ w‖₊ : ℝ≥0∞) ^ 2) ≤ ENNReal.ofReal (16 / (49 * u.im ^ 2)) *
      ∫⁻ w in ball u s, ‖m w‖ₑ ^ 2 * ENNReal.ofReal (rhoU w) := by
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    exact setLIntegral_mono' measurableSet_ball hpt
  have hmu : ‖m u‖ₑ ^ 2 = ENNReal.ofReal (4 * u.im ^ 4) * (‖φ u‖₊ : ℝ≥0∞) ^ 2 := by
    have hφu : (‖φ u‖₊ : ℝ≥0∞) ^ 2 = ENNReal.ofReal (‖φ u‖ ^ 2) := by
      rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
      rfl
    rw [hm u hu, ← ofReal_norm, s7g_r3_norm_m, ← ENNReal.ofReal_pow (by positivity), hφu,
      ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    ring
  have hc : ENNReal.ofReal (4 * u.im ^ 4) * ENNReal.ofReal (16 / (49 * u.im ^ 2)) =
      ENNReal.ofReal (12288 / (49 * π)) * ENNReal.ofReal (π * s ^ 2 / 3) := by
    rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    rw [hsd]
    field_simp
    ring
  have hpos : ENNReal.ofReal (π * s ^ 2 / 3) ≠ 0 := by
    rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]; positivity
  have hstep : (‖φ u‖₊ : ℝ≥0∞) ^ 2 ≤ (ENNReal.ofReal (π * s ^ 2 / 3))⁻¹ *
      ∫⁻ w in ball u s, (‖φ w‖₊ : ℝ≥0∞) ^ 2 := by
    calc (‖φ u‖₊ : ℝ≥0∞) ^ 2 = (ENNReal.ofReal (π * s ^ 2 / 3))⁻¹ *
          (ENNReal.ofReal (π * s ^ 2 / 3) * (‖φ u‖₊ : ℝ≥0∞) ^ 2) := by
          rw [← mul_assoc, ENNReal.inv_mul_cancel hpos ENNReal.ofReal_ne_top, one_mul]
      _ ≤ _ := by gcongr
  calc ‖m u‖ₑ ^ 2 = ENNReal.ofReal (4 * u.im ^ 4) * (‖φ u‖₊ : ℝ≥0∞) ^ 2 := hmu
    _ ≤ ENNReal.ofReal (4 * u.im ^ 4) * ((ENNReal.ofReal (π * s ^ 2 / 3))⁻¹ *
          (ENNReal.ofReal (16 / (49 * u.im ^ 2)) * ∫⁻ w in ball u s, ‖m w‖ₑ ^ 2 * ENNReal.ofReal (rhoU w))) :=
        by gcongr; exact hstep.trans (by gcongr)
    _ = ENNReal.ofReal (12288 / (49 * π)) * ∫⁻ w in ball u s, ‖m w‖ₑ ^ 2 * ENNReal.ofReal (rhoU w) := by
        calc _ = (ENNReal.ofReal (4 * u.im ^ 4) * ENNReal.ofReal (16 / (49 * u.im ^ 2))) *
              (ENNReal.ofReal (π * s ^ 2 / 3))⁻¹ *
                ∫⁻ w in ball u s, ‖m w‖ₑ ^ 2 * ENNReal.ofReal (rhoU w) := by ring
          _ = _ := by
            rw [hc, mul_assoc (ENNReal.ofReal (12288 / (49 * π))),
              ENNReal.mul_inv_cancel hpos ENNReal.ofReal_ne_top, mul_one]

/-- For `w ∈ 𝕌`, the Whitney balls `B(u, Im u/8)` containing `w` have centres in `B(w, Im w/7)`. -/
theorem s7g_r3_near {u w : ℂ} (hu : u ∈ upperHalf) (huw : ‖w - u‖ < u.im / 8) : u ∈ ball w (w.im / 7) := by
  have hy : 0 < u.im := hu
  have := abs_lt.1 ((abs_im_le_norm (w - u)).trans_lt huw)
  simp only [Complex.sub_im] at this
  rw [mem_ball, dist_eq_norm, norm_sub_rev]
  linarith [this.1]

/-- Measurability of the weight `J_W / d_{W(𝕌)}(W)²`. -/
theorem s7g_r3_Wl_meas {W : ℂ → ℂ} (hWc : Continuous W) :
    Measurable fun u => ENNReal.ofReal (jacobian W u) / ENNReal.ofReal (infDist (W u) (W '' upperHalf)ᶜ) ^ 2 := by
  have hJ : Measurable fun u => jacobian W u := by
    unfold jacobian
    exact ((measurable_dz W).norm.pow_const 2).sub ((measurable_dzbar W).norm.pow_const 2)
  have hd : Measurable fun u => infDist (W u) (W '' upperHalf)ᶜ :=
    ((continuous_infDist_pt _).comp hWc).measurable
  exact (ENNReal.measurable_ofReal.comp hJ).div ((ENNReal.measurable_ofReal.comp hd).pow_const 2)

/-- Measurability of `|m|² ρ_𝕌` on `𝕌`. -/
theorem s7g_r3_N_meas {m φ : ℂ → ℂ} (hφ : DifferentiableOn ℂ φ upperHalf)
    (hm : ∀ u ∈ upperHalf, m u = (u - conj u) ^ 2 / 2 * conj (φ u)) :
    AEMeasurable (fun w => ‖m w‖ₑ ^ 2 * ENNReal.ofReal (rhoU w)) (volume.restrict upperHalf) := by
  have hU : MeasurableSet upperHalf := (isOpen_lt continuous_const Complex.continuous_im).measurableSet
  have hc : ContinuousOn (fun u : ℂ => (u - conj u) ^ 2 / 2 * conj (φ u)) upperHalf :=
    ((continuous_id.sub Complex.continuous_conj).pow 2 |>.div_const 2).continuousOn.mul
      (Complex.continuous_conj.comp_continuousOn hφ.continuousOn)
  have hmA : AEMeasurable m (volume.restrict upperHalf) := by
    refine (hc.aemeasurable hU).congr ?_
    filter_upwards [ae_restrict_mem hU] with u hu
    exact (hm u hu).symm
  have hr : Measurable fun w : ℂ => ENNReal.ofReal (rhoU w) := by
    unfold rhoU
    fun_prop
  exact (hmA.enorm.pow_const 2).mul hr.aemeasurable

/-- **R3** (stub `s7g_transfer`). -/
theorem s7g_transfer {K : ℝ} (hK : 1 ≤ K) : ∃ C : ℝ≥0∞, C < ∞ ∧ ∀ W : ℂ → ℂ, IsKQC W univ K →
    W '' univ = univ → ContDiffOn ℝ 1 W upperHalf → ∀ m φ : ℂ → ℂ, DifferentiableOn ℂ φ upperHalf →
      (∀ u ∈ upperHalf, m u = (u - conj u) ^ 2 / 2 * conj (φ u)) →
      (∫⁻ u in upperHalf, ‖m u‖ₑ ^ 2 * ENNReal.ofReal (jacobian W u) /
          ENNReal.ofReal (infDist (W u) (W '' upperHalf)ᶜ) ^ 2) ≤
        C * ∫⁻ u in upperHalf, ‖m u‖ₑ ^ 2 * ENNReal.ofReal (rhoU u) := by
  -- `hK` is not needed: `IsKQC W univ K` already contains `1 ≤ K`.
  have _hK := hK
  set C0 : ℝ≥0∞ := ENNReal.ofReal (12288 / (49 * π)) with hC0
  set c : ℝ≥0∞ := ENNReal.ofReal (lambdaInv K ^ 2) * NNReal.pi with hc
  refine ⟨C0 * c, ENNReal.mul_lt_top ENNReal.ofReal_lt_top
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.coe_lt_top), ?_⟩
  -- `ContDiffOn` is not needed: the area formula `qcv_lintegral_image_eq` holds for every q.c. map.
  intro W hW hs _hWs m φ hφ hm
  have hU : MeasurableSet upperHalf := (isOpen_lt continuous_const Complex.continuous_im).measurableSet
  have hWc : Continuous W := continuousOn_univ.1 hW.2.2.1.1
  set Wl : ℂ → ℝ≥0∞ := fun u =>
    ENNReal.ofReal (jacobian W u) / ENNReal.ofReal (infDist (W u) (W '' upperHalf)ᶜ) ^ 2 with hWld
  set N : ℂ → ℝ≥0∞ := fun w => ‖m w‖ₑ ^ 2 * ENNReal.ofReal (rhoU w) with hNd
  set S : Set (ℂ × ℂ) := {p | ‖p.2 - p.1‖ < p.1.im / 8} with hSd
  have hS : MeasurableSet S := (isOpen_lt (by fun_prop) (by fun_prop)).measurableSet
  have hWl : Measurable Wl := s7g_r3_Wl_meas hWc
  have hN : AEMeasurable N (volume.restrict upperHalf) := s7g_r3_N_meas hφ hm
  set G : ℂ → ℂ → ℝ≥0∞ := fun u w => S.indicator (fun _ => (1 : ℝ≥0∞)) (u, w) * N w * Wl u with hGd
  have hGm : AEMeasurable (Function.uncurry G) ((volume.restrict upperHalf).prod (volume.restrict upperHalf)) := by
    have h1 : Measurable fun p : ℂ × ℂ => S.indicator (fun _ => (1 : ℝ≥0∞)) p := measurable_const.indicator hS
    exact (h1.aemeasurable.mul hN.comp_snd).mul (hWl.comp measurable_fst).aemeasurable
  -- the ball integral as an integral over `𝕌`
  have hball : ∀ u ∈ upperHalf, (∫⁻ w in ball u (u.im / 8), N w) = ∫⁻ w in upperHalf,
      S.indicator (fun _ => (1 : ℝ≥0∞)) (u, w) * N w := by
    intro u hu
    have hsub : ball u (u.im / 8) ⊆ upperHalf := by
      intro w hw
      have hw' : ‖w - u‖ < u.im / 8 := by simpa [dist_eq_norm] using hw
      have := abs_lt.1 ((abs_im_le_norm (w - u)).trans_lt hw')
      simp only [Complex.sub_im] at this
      have hy : 0 < u.im := hu
      show 0 < w.im
      linarith [this.1]
    have he : ∀ w, S.indicator (fun _ => (1 : ℝ≥0∞)) (u, w) * N w = (ball u (u.im / 8)).indicator N w := by
      intro w
      by_cases hw : w ∈ ball u (u.im / 8)
      · have hS' : (u, w) ∈ S := by simpa [hSd, dist_eq_norm] using hw
        rw [indicator_of_mem hS', indicator_of_mem hw, one_mul]
      · have hS' : (u, w) ∉ S := by simpa [hSd, dist_eq_norm] using hw
        rw [indicator_of_notMem hS', indicator_of_notMem hw, zero_mul]
    simp_rw [he]
    rw [lintegral_indicator measurableSet_ball, Measure.restrict_restrict measurableSet_ball,
      inter_eq_left.2 hsub]
  -- the inner `u`-integral is bounded by the cell bound
  have hinner : ∀ w ∈ upperHalf, (∫⁻ u in upperHalf, S.indicator (fun _ => (1 : ℝ≥0∞)) (u, w) * Wl u) ≤ c := by
    intro w hw
    calc (∫⁻ u in upperHalf, S.indicator (fun _ => (1 : ℝ≥0∞)) (u, w) * Wl u)
        ≤ ∫⁻ u in upperHalf, (ball w (w.im / 7)).indicator Wl u := by
          refine setLIntegral_mono' hU fun u hu => ?_
          by_cases hS' : (u, w) ∈ S
          · have hb : u ∈ ball w (w.im / 7) := s7g_r3_near hu hS'
            rw [indicator_of_mem hS', indicator_of_mem hb, one_mul]
          · rw [indicator_of_notMem hS', zero_mul]
            exact zero_le
      _ ≤ ∫⁻ u, (ball w (w.im / 7)).indicator Wl u := setLIntegral_le_lintegral _ _
      _ = ∫⁻ u in ball w (w.im / 7), Wl u := lintegral_indicator measurableSet_ball _
      _ ≤ c := s7g_r3_cell hW hs hw
  calc (∫⁻ u in upperHalf, ‖m u‖ₑ ^ 2 * ENNReal.ofReal (jacobian W u) /
          ENNReal.ofReal (infDist (W u) (W '' upperHalf)ᶜ) ^ 2)
      = ∫⁻ u in upperHalf, ‖m u‖ₑ ^ 2 * Wl u := by
        simp only [hWld, mul_div_assoc]
    _ ≤ ∫⁻ u in upperHalf, (C0 * ∫⁻ w in ball u (u.im / 8), N w) * Wl u := by
        refine setLIntegral_mono' hU fun u hu => ?_
        gcongr
        exact s7g_r3_mean hφ hm hu
    _ = C0 * ∫⁻ u in upperHalf, ∫⁻ w in upperHalf, G u w := by
        rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        refine setLIntegral_congr_fun hU fun u hu => ?_
        have h1 : Measurable fun w : ℂ => S.indicator (fun _ => (1 : ℝ≥0∞)) (u, w) :=
          (measurable_const.indicator hS).comp (measurable_const.prodMk measurable_id)
        have hAE : AEMeasurable (fun w => S.indicator (fun _ => (1 : ℝ≥0∞)) (u, w) * N w)
            (volume.restrict upperHalf) := h1.aemeasurable.mul hN
        rw [hball u hu, mul_assoc, ← lintegral_mul_const'' _ hAE]
    _ = C0 * ∫⁻ w in upperHalf, ∫⁻ u in upperHalf, G u w := by rw [lintegral_lintegral_swap hGm]
    _ ≤ C0 * ∫⁻ w in upperHalf, N w * c := by
        gcongr C0 * ?_
        refine setLIntegral_mono' hU fun w hw => ?_
        calc (∫⁻ u in upperHalf, G u w) = N w * ∫⁻ u in upperHalf,
              S.indicator (fun _ => (1 : ℝ≥0∞)) (u, w) * Wl u := by
              have h2 : Measurable fun u : ℂ => S.indicator (fun _ => (1 : ℝ≥0∞)) (u, w) :=
                (measurable_const.indicator hS).comp (measurable_id.prodMk measurable_const)
              have hAE2 : AEMeasurable (fun u => S.indicator (fun _ => (1 : ℝ≥0∞)) (u, w) * Wl u)
                  (volume.restrict upperHalf) := (h2.mul hWl).aemeasurable
              rw [← lintegral_const_mul'' _ hAE2]
              congr 1
              funext u
              simp only [hGd]
              ring
          _ ≤ N w * c := by gcongr; exact hinner w hw
    _ = C0 * c * ∫⁻ w in upperHalf, N w := by
        rw [lintegral_mul_const' _ _ (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.coe_ne_top)]
        ring

end TakhtajanTeo
