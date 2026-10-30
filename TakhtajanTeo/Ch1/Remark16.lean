import TakhtajanTeo.Ch1.S1_2_Homogeneous
import TakhtajanTeo.Ch1.WRegFoundation

/-!
# Remark 1.6 (TT:724)  [下属2, Program F]

For harmonic `μ = Λφ`, the map `f = ι ∘ (λ_c ∘ w^μ) ∘ ι` (`c = f^μ''(0)/2`) is, in the `ι`-chart of `Lemma15`,
`f(z) = z + T ω(z)` with `ω` the hydrodynamic solution of `ν^{[1]}` (`r16_W_inv`, `r16_chart`).  `f(0) = 0` is
`l15_core`.  For `f_z(0) = 1`:
* the circle integrals `E_R(t) = (2πi)⁻¹ ∮_{|z|=R} G_t z⁻²` of the normalized solutions `G_t` of `ν^{[t]}` are
  holomorphic in `t` and obey the same rotation law as `Q_2 = E_2`, so `E_R/Q_2` is a rotation-invariant holomorphic
  function, hence constant `= 1`; in hydrodynamic terms `∮_{|z|=R} T ω_t z⁻² = 0` for `|t| < 1` (`r16_family_circle`);
* `t = r_n ↑ 1` by uniform convergence (`r16_one_circle`);
* `T ω` is real-differentiable at `0` (W-REG D2b, `wr_ns2_z_regular`: the coefficient is smooth on `𝔻`)
  (`r16_regular`), and for such `g` the vanishing of `∮_{|z|=R} g z⁻²` for small `R` gives `∂_z g(0) = 0`
  (`r16_dz_of_circle`).
All helpers are prefixed `r16_`.
-/

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal NNReal ComplexConjugate Classical Real
noncomputable section
namespace TakhtajanTeo
open LiZhongQC

/-- (S1) A holomorphic function on the unit disc invariant under all rotations is constant. -/
theorem r16_rot_const {P : ℂ → ℂ} (hP : DifferentiableOn ℂ P (ball (0 : ℂ) 1))
    (hrot : ∀ l : ℂ, ‖l‖ = 1 → ∀ t ∈ ball (0 : ℂ) 1, P (l * t) = P t) :
    ∀ t ∈ ball (0 : ℂ) 1, P t = P 0 := by
  intro t ht
  by_cases ht0 : t = 0
  · rw [ht0]
  have hs : 0 < ‖t‖ := norm_pos_iff.2 ht0
  have hs1 : ‖t‖ < 1 := mem_ball_zero_iff.1 ht
  have hdc : DiffContOnCl ℂ P (ball (0 : ℂ) ‖t‖) := by
    refine DifferentiableOn.diffContOnCl ?_
    rw [closure_ball _ hs.ne']
    exact hP.mono (closedBall_subset_ball hs1)
  have hcif := hdc.circleIntegral_sub_inv_smul (mem_ball_self hs)
  have hconst : ∮ z in C(0, ‖t‖), (z - 0)⁻¹ • P z = ∮ z in C(0, ‖t‖), (z - 0)⁻¹ • P t := by
    refine circleIntegral.integral_congr hs.le fun z hz => ?_
    have hz : ‖z‖ = ‖t‖ := by simpa using hz
    have hz0 : z ≠ 0 := by
      intro h0; rw [h0, norm_zero] at hz; exact hs.ne' hz.symm
    have hl : ‖z / t‖ = 1 := by rw [norm_div, hz, div_self hs.ne']
    have := hrot (z / t) hl t ht
    rw [div_mul_cancel₀ z ht0] at this
    rw [this]
  rw [hconst, circleIntegral.integral_smul_const,
    circleIntegral.integral_sub_inv_of_mem_ball (mem_ball_self hs)] at hcif
  have hπ : (2 * π * I : ℂ) ≠ 0 := by
    have : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 Real.pi_ne_zero
    exact mul_ne_zero (mul_ne_zero two_ne_zero this) Complex.I_ne_zero
  simp only [smul_eq_mul] at hcif
  exact mul_left_cancel₀ hπ hcif

/-- (S2) Rescaling a circle integral from `|z| = R` to `|z| = 2`. -/
theorem r16_circle_scale (F : ℂ → ℂ) {R : ℝ} (hR : 0 < R) :
    ∮ z in C(0, R), F z / z ^ 2 = (2 / R : ℂ) * ∮ z in C(0, 2), F ((R / 2 : ℂ) * z) / z ^ 2 := by
  have hR' : (R : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hR.ne'
  have hc : ∀ θ : ℝ, circleMap 0 R θ = (R / 2 : ℂ) * circleMap 0 2 θ := by
    intro θ
    simp only [circleMap, zero_add]
    push_cast
    ring
  unfold circleIntegral
  simp only [deriv_circleMap]
  rw [← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun θ _ => ?_
  simp only [smul_eq_mul, hc θ]
  have hcn : circleMap 0 2 θ ≠ 0 := circleMap_ne_center (by norm_num)
  field_simp

/-- (S3) **Family identity.**  For `|t| < 1` and `0 < R ≤ 2` the hydrodynamic solution `ω` of `ν^{[t]}` satisfies
`∮_{|z|=R} T ω(z) z⁻² dz = 0` (holomorphy + rotation law of `E_R / Q_2`, `r16_rot_const`). -/
theorem r16_family_circle {h : ℂ → ℂ} (hh : DifferentiableOn ℂ h unitDisc) {k : ℝ} (hk0 : 0 ≤ k) (hk1 : k < 1)
    (hbd : ∀ w ∈ unitDisc, (1 - ‖w‖ ^ 2) ^ 2 * ‖h w‖ ≤ k)
    {nu : ℂ → ℂ → ℂ}
    (hnu : ∀ t w, nu t w = if ‖w‖ < 1 then (1 - ‖w‖ ^ 2) ^ 2 * t ^ 2 * conj (h (conj t * w)) else 0)
    {p : ℝ} (hp : 2 < p) (hkp : k * hilbertNorm p < 1) {t : ℂ} (ht : ‖t‖ < 1)
    {ω : ℂ → ℂ} (hω : MemLp ω (ENNReal.ofReal p))
    (hs : ω =ᵐ[volume] fun z => nu t z * hilbertH ω z + nu t z) {R : ℝ} (hR0 : 0 < R) (hR2 : R ≤ 2) :
    ∮ z in C(0, R), cauchyT ω z / z ^ 2 = 0 := by
  have hGex : ∀ t : ℂ, ‖t‖ ≤ 1 → ∃ g : ℂ → ℂ, IsNormalizedSolution g (nu t) := fun t ht => by
    obtain ⟨hb, -, -⟩ := l15_nu_beltrami hh hk0 hk1 hbd hnu ht
    obtain ⟨g, hg, -, -⟩ := thm13_7_normalized_existence hk0 hk1 hb
    exact ⟨g, hg⟩
  have hΩex : ∀ t : ℂ, ‖t‖ ≤ 1 → ∃ ω' : ℂ → ℂ, MemLp ω' (ENNReal.ofReal p) ∧
      (ω' =ᵐ[volume] fun z => nu t z * hilbertH ω' z + nu t z) := fun t ht => by
    obtain ⟨hb, -, -⟩ := l15_nu_beltrami hh hk0 hk1 hbd hnu ht
    have hμmem : MemLp (nu t) (ENNReal.ofReal p) :=
      (l15_nu_Lp hh hk0 hk1 hbd hnu ht (by linarith)).1
    obtain ⟨ω', hω', hsol, -⟩ := eq12_1_solution hk0 hb hp hkp hμmem
    exact ⟨ω', hω', hsol⟩
  choose! G hG using hGex
  choose! Ω hΩ using hΩex
  have hGb : ∀ t ∈ ball (0 : ℂ) 1, IsNormalizedSolution (G t) (nu t) := fun t ht =>
    hG t (mem_ball_zero_iff.1 ht).le
  have hπ : (2 * π * I : ℂ) ≠ 0 := by
    have : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 Real.pi_ne_zero
    exact mul_ne_zero (mul_ne_zero two_ne_zero this) Complex.I_ne_zero
  have hR' : (R : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hR0.ne'
  -- circle integral of a hydrodynamic normalization
  have hcirc : ∀ R' : ℝ, 0 < R' → ∀ (G' r : ℂ → ℂ) (D : ℂ), (∀ z, G' z = D⁻¹ * (z + r z - r 0)) →
      ContinuousOn r (sphere (0 : ℂ) R') →
      ∮ z in C(0, R'), G' z / z ^ 2 = D⁻¹ * (2 * π * I + ∮ z in C(0, R'), r z / z ^ 2) := by
    intro R' hR'0 G' r D hGs hrc
    have hsph : ∀ z ∈ sphere (0 : ℂ) R', z ≠ 0 := fun z hz h0 => by
      rw [mem_sphere_zero_iff_norm, h0, norm_zero] at hz; linarith
    have hci : ∀ g : ℂ → ℂ, ContinuousOn g (sphere (0 : ℂ) R') → CircleIntegrable g 0 R' := fun g hg =>
      hg.circleIntegrable hR'0.le
    have hz0 : ContinuousOn (fun z : ℂ => (z - 0)⁻¹) (sphere (0 : ℂ) R') := by
      refine ContinuousOn.inv₀ (by fun_prop) fun z hz => ?_
      simpa using hsph z hz
    have hz2 : ContinuousOn (fun z : ℂ => (z - 0) ^ (-2 : ℤ)) (sphere (0 : ℂ) R') := by
      refine ContinuousOn.zpow₀ (by fun_prop) _ fun z hz => Or.inl ?_
      simpa using hsph z hz
    have hrz : ContinuousOn (fun z : ℂ => r z / z ^ 2) (sphere (0 : ℂ) R') :=
      hrc.div (by fun_prop) fun z hz => pow_ne_zero _ (hsph z hz)
    have heq : ∮ z in C(0, R'), G' z / z ^ 2 =
        ∮ z in C(0, R'), D⁻¹ * ((z - 0)⁻¹ + r z / z ^ 2 - r 0 * (z - 0) ^ (-2 : ℤ)) := by
      refine circleIntegral.integral_congr hR'0.le fun z hz => ?_
      have := hsph z hz
      simp only [hGs, sub_zero, zpow_neg, zpow_ofNat]
      field_simp
    have i1 : CircleIntegrable (fun z : ℂ => (z - 0)⁻¹) 0 R' := hci _ hz0
    have i2 : CircleIntegrable (fun z : ℂ => r z / z ^ 2) 0 R' := hci _ hrz
    have i3 : CircleIntegrable (fun z : ℂ => r 0 * (z - 0) ^ (-2 : ℤ)) 0 R' :=
      hci _ (continuousOn_const.mul hz2)
    have i12 : CircleIntegrable (fun z : ℂ => (z - 0)⁻¹ + r z / z ^ 2) 0 R' := hci _ (hz0.add hrz)
    have hinv : ∮ z in C(0, R'), (z - 0)⁻¹ = 2 * π * I :=
      circleIntegral.integral_sub_inv_of_mem_ball (mem_ball_self hR'0)
    have hinv2 : ∮ z in C(0, R'), (z - 0) ^ (-2 : ℤ) = 0 :=
      circleIntegral.integral_sub_zpow_of_ne (by norm_num) _ _ _
    rw [heq, circleIntegral.integral_const_mul, circleIntegral.integral_sub i12 i3,
      circleIntegral.integral_add i1 i2, circleIntegral.integral_const_mul, hinv, hinv2]
    ring
  -- the value of `E_R / Q_2` through any hydrodynamic solution
  set Q2 : ℂ → ℂ := fun t => (2 * π * I)⁻¹ * ∮ z in C(0, 2), G t z / z ^ 2 with hQ2
  set E : ℂ → ℂ := fun t => (2 * π * I)⁻¹ * ∮ z in C(0, R), G t z / z ^ 2 with hE
  have hval : ∀ t ∈ ball (0 : ℂ) 1, ∀ ω' : ℂ → ℂ, MemLp ω' (ENNReal.ofReal p) →
      (ω' =ᵐ[volume] fun z => nu t z * hilbertH ω' z + nu t z) →
      Q2 t ≠ 0 ∧ E t / Q2 t = 1 + (2 * π * I)⁻¹ * ∮ z in C(0, R), cauchyT ω' z / z ^ 2 := by
    intro t ht ω' hω' hs'
    obtain ⟨hb, hsupp, -⟩ := l15_nu_beltrami hh hk0 hk1 hbd hnu (mem_ball_zero_iff.1 ht).le
    obtain ⟨D, hD, hGf⟩ := l15_G_formula hk0 hk1 hp hkp hb hsupp hω' hs' (hGb t ht)
    obtain ⟨hKqc, -, -⟩ := l15_hydro_data hk0 hk1 hp hkp hb hsupp hω' hs'
    have hfc : Continuous fun z => z + cauchyT ω' z := continuousOn_univ.mp hKqc.2.2.1.1
    have hrc : Continuous (cauchyT ω') := by
      refine (hfc.sub continuous_id).congr fun z => ?_
      simp
    have hω0 : ω' =ᵐ[volume] (closedBall (0 : ℂ) 1).indicator ω' :=
      t2_omega_ae_eq_indicator (fun z hz => hsupp z hz.le) hs'
    obtain ⟨hdiffr, C, R₁, hCR⟩ := l15_cauchyT_outside hp hω' hω0
    have hr2 := l15_contour_zero hdiffr hCR 2 (by norm_num)
    have h2 := hcirc 2 two_pos (G t) (cauchyT ω') D hGf hrc.continuousOn
    have hRr := hcirc R hR0 (G t) (cauchyT ω') D hGf hrc.continuousOn
    rw [hr2, add_zero] at h2
    have hQv : Q2 t = D⁻¹ := by
      simp only [hQ2]; rw [h2]; field_simp
    have hEv : E t = D⁻¹ * (1 + (2 * π * I)⁻¹ * ∮ z in C(0, R), cauchyT ω' z / z ^ 2) := by
      simp only [hE]; rw [hRr]; field_simp
    refine ⟨by rw [hQv]; exact inv_ne_zero hD, ?_⟩
    rw [hEv, hQv]
    field_simp
  -- holomorphy of `P = E / Q₂`
  obtain ⟨M, hM⟩ := l15_G_bound hh hk0 hk1 hbd hnu hGb
  have hholG := thm13_8_ahlfors_bers_holomorphic isOpen_ball hk0 hk1
    (fun t ht => (l15_nu_beltrami hh hk0 hk1 hbd hnu (mem_ball_zero_iff.1 ht).le).1)
    (l15_nu_hol hh hnu) hGb
  have hGc : ∀ t ∈ ball (0 : ℂ) 1, Continuous (G t) := fun t ht => by
    obtain ⟨⟨K, hK⟩, -⟩ := hGb t ht
    exact continuousOn_univ.mp hK.2.2.1.1
  have hRn : ‖(R / 2 : ℂ)‖ = R / 2 := by
    rw [show (R / 2 : ℂ) = ((R / 2 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
      Real.norm_of_nonneg (by positivity)]
  have hEs : ∀ t, E t = (2 / R : ℂ) * ((2 * π * I)⁻¹ * ∮ z in C(0, 2), G t ((R / 2 : ℂ) * z) / z ^ 2) := by
    intro t; simp only [hE]; rw [r16_circle_scale _ hR0]; ring
  have hEh : DifferentiableOn ℂ E (ball (0 : ℂ) 1) := by
    have h1 := l15_param_circle (Gf := fun t z => G t ((R / 2 : ℂ) * z)) (M := M) 2
      (fun t ht => (hGc t ht).comp (continuous_const.mul continuous_id))
      (fun z => hholG ((R / 2 : ℂ) * z))
      (fun t ht z hz => hM t ht _ (by rw [norm_mul, hRn]; nlinarith [norm_nonneg z]))
    exact (h1.const_mul (2 / R : ℂ)).congr fun t _ => hEs t
  have hQh : DifferentiableOn ℂ Q2 (ball (0 : ℂ) 1) := l15_QS_hol hh hk0 hk1 hbd hnu hGb 2
  have hne : ∀ t ∈ ball (0 : ℂ) 1, Q2 t ≠ 0 := fun t ht => by
    obtain ⟨hω', hs'⟩ := hΩ t (mem_ball_zero_iff.1 ht).le
    exact (hval t ht (Ω t) hω' hs').1
  set P : ℂ → ℂ := fun t => E t / Q2 t with hP
  have hPh : DifferentiableOn ℂ P (ball (0 : ℂ) 1) := hEh.div hQh hne
  -- rotation law
  have hrotR : ∀ (F : ℂ → ℂ) (l : ℂ), ‖l‖ = 1 →
      ∮ z in C(0, R), F (l * z) / z ^ 2 = l * ∮ z in C(0, R), F z / z ^ 2 := by
    intro F l hl
    have hl0 : l ≠ 0 := by
      intro h0; rw [h0, norm_zero] at hl; exact zero_ne_one hl
    rw [r16_circle_scale _ hR0, r16_circle_scale _ hR0]
    have hrot := l15_circle_rot (fun w => F ((R / 2 : ℂ) * w)) hl 2
    have e : (fun z => F (l * ((R / 2 : ℂ) * z)) / z ^ 2) =
        fun z => (fun w => F ((R / 2 : ℂ) * w)) (l * z) / z ^ 2 := by
      funext z; rw [mul_left_comm]
    rw [e, hrot, show l ^ 2 * l⁻¹ = l by field_simp]
    beta_reduce
    ring
  have hGl : ∀ t ∈ ball (0 : ℂ) 1, ∀ l : ℂ, ‖l‖ = 1 → G t l ≠ 0 := by
    intro t ht l hl he
    obtain ⟨⟨K, hK⟩, -, h0, -, -⟩ := hGb t ht
    have hl0 : l ≠ 0 := by
      intro h0'; rw [h0', norm_zero] at hl; exact zero_ne_one hl
    exact hl0 (hK.2.2.1.2.1 (mem_univ _) (mem_univ _) (he.trans h0.symm))
  have hProt : ∀ l : ℂ, ‖l‖ = 1 → ∀ t ∈ ball (0 : ℂ) 1, P (l * t) = P t := by
    intro l hl t ht
    have hl' : ‖conj l‖ = 1 := by rw [Complex.norm_conj, hl]
    have hl'0 : conj l ≠ 0 := by
      intro h0; rw [h0, norm_zero] at hl'; exact zero_ne_one hl'
    have hlt : l * t = conj (conj l) * t := by rw [Complex.conj_conj]
    have hQ : Q2 (conj (conj l) * t) = conj l ^ (2 - 1) * Q2 t / G t (conj l) :=
      l15_QS_rot hh hk0 hk1 hbd hnu hGb 2 (by norm_num) hl' (mem_ball_zero_iff.1 ht)
    have hEr : E (conj (conj l) * t) = conj l * E t / G t (conj l) := by
      simp only [hE]
      have hfun : (fun z => G (conj (conj l) * t) z / z ^ 2) =
          fun z => (G t (conj l))⁻¹ * (G t (conj l * z) / z ^ 2) := by
        funext z; rw [l15_G_rot hh hk0 hk1 hbd hnu hGb hl' (mem_ball_zero_iff.1 ht) z]; ring
      rw [hfun, circleIntegral.integral_const_mul, hrotR (G t) (conj l) hl']
      ring
    have hGt := hGl t ht (conj l) hl'
    have hQt := hne t ht
    simp only [hP]
    rw [hlt, hEr, hQ]
    norm_num
    field_simp
  -- value at `t = 0`
  have hP0 : P 0 = 1 := by
    obtain ⟨hω00, hs00⟩ := hΩ 0 (by simp)
    have hv0 := (hval 0 (mem_ball_self one_pos) (Ω 0) hω00 hs00).2
    have hz : Ω 0 =ᵐ[volume] fun _ => (0 : ℂ) := by
      filter_upwards [hs00] with z hz
      rw [hz, hnu]
      split_ifs <;> simp
    have hT : cauchyT (Ω 0) = fun _ => 0 := by
      rw [cauchyT_congr_ae hz]; funext z; simp [cauchyT]
    rw [hT] at hv0
    have h00 : ∮ z in C(0, R), (fun _ : ℂ => (0 : ℂ)) z / z ^ 2 = 0 := by simp [circleIntegral]
    rw [h00, mul_zero, add_zero] at hv0
    exact hv0
  have hfin := r16_rot_const hPh hProt t (mem_ball_zero_iff.2 ht)
  have hvt := (hval t (mem_ball_zero_iff.2 ht) ω hω hs).2
  rw [hP0] at hfin
  simp only [hP] at hfin
  rw [hvt] at hfin
  have h1 : (2 * π * I)⁻¹ * ∮ z in C(0, R), cauchyT ω z / z ^ 2 = 0 := by linear_combination hfin
  rcases mul_eq_zero.1 h1 with h | h
  · exact absurd h (inv_ne_zero hπ)
  · exact h

/-- (S4) The family identity at `t = 1` (`r_n ↑ 1`, `eq12_1_solution_tendsto_cauchyT`). -/
theorem r16_one_circle {h : ℂ → ℂ} (hh : DifferentiableOn ℂ h unitDisc) {k : ℝ} (hk0 : 0 ≤ k) (hk1 : k < 1)
    (hbd : ∀ w ∈ unitDisc, (1 - ‖w‖ ^ 2) ^ 2 * ‖h w‖ ≤ k)
    {nu : ℂ → ℂ → ℂ}
    (hnu : ∀ t w, nu t w = if ‖w‖ < 1 then (1 - ‖w‖ ^ 2) ^ 2 * t ^ 2 * conj (h (conj t * w)) else 0)
    {p : ℝ} (hp : 2 < p) (hkp : k * hilbertNorm p < 1)
    {ω : ℂ → ℂ} (hω : MemLp ω (ENNReal.ofReal p))
    (hs : ω =ᵐ[volume] fun z => nu 1 z * hilbertH ω z + nu 1 z) {R : ℝ} (hR0 : 0 < R) (hR2 : R ≤ 2) :
    ∮ z in C(0, R), cauchyT ω z / z ^ 2 = 0 := by
  set r : ℕ → ℝ := fun n => 1 - 1 / ((n : ℝ) + 1) with hrdef
  have hr0 : ∀ n, 0 ≤ r n := fun n => by
    simp only [hrdef]
    have : 1 / ((n : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]; linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    linarith
  have hr1 : ∀ n, r n < 1 := fun n => by
    simp only [hrdef]
    have : 0 < 1 / ((n : ℝ) + 1) := by positivity
    linarith
  have hr : Tendsto r atTop (𝓝 1) := by
    have h1 := (tendsto_const_nhds (x := (1 : ℝ))).sub tendsto_one_div_add_atTop_nhds_zero_nat
    simpa [hrdef] using h1
  have hnorm : ∀ n, ‖((r n : ℝ) : ℂ)‖ < 1 := fun n => by
    rw [Complex.norm_real, Real.norm_of_nonneg (hr0 n)]; exact hr1 n
  have hΩex : ∀ n : ℕ, ∃ ω' : ℂ → ℂ, MemLp ω' (ENNReal.ofReal p) ∧
      (ω' =ᵐ[volume] fun z => nu (r n) z * hilbertH ω' z + nu (r n) z) := fun n => by
    obtain ⟨hb, -, -⟩ := l15_nu_beltrami hh hk0 hk1 hbd hnu (hnorm n).le
    obtain ⟨ω', hω', hsol, -⟩ := eq12_1_solution hk0 hb hp hkp
      (l15_nu_Lp hh hk0 hk1 hbd hnu (hnorm n).le (by linarith)).1
    exact ⟨ω', hω', hsol⟩
  choose Ω hΩ using hΩex
  have hzero : ∀ n, ∮ z in C(0, R), cauchyT (Ω n) z / z ^ 2 = 0 := fun n =>
    r16_family_circle hh hk0 hk1 hbd hnu hp hkp (hnorm n) (hΩ n).1 (hΩ n).2 hR0 hR2
  -- continuity of the Cauchy transforms
  have hcT : ∀ t : ℂ, ‖t‖ ≤ 1 → ∀ ω' : ℂ → ℂ, MemLp ω' (ENNReal.ofReal p) →
      (ω' =ᵐ[volume] fun z => nu t z * hilbertH ω' z + nu t z) → Continuous (cauchyT ω') := by
    intro t ht ω' hω' hs'
    obtain ⟨hb, hsupp, -⟩ := l15_nu_beltrami hh hk0 hk1 hbd hnu ht
    obtain ⟨hKqc, -, -⟩ := l15_hydro_data hk0 hk1 hp hkp hb hsupp hω' hs'
    have hfc : Continuous fun z => z + cauchyT ω' z := continuousOn_univ.mp hKqc.2.2.1.1
    refine (hfc.sub continuous_id).congr fun z => ?_
    simp
  have hc1 : Continuous (cauchyT ω) := hcT 1 (by simp) ω hω hs
  have hcn : ∀ n, Continuous (cauchyT (Ω n)) := fun n => hcT _ (hnorm n).le _ (hΩ n).1 (hΩ n).2
  -- uniform convergence (as in `l15_limit`)
  have hbn : ∀ n, IsBeltramiCoeff (nu (r n)) univ k ∧ (∀ w : ℂ, 1 ≤ ‖w‖ → nu (r n) w = 0) := fun n => by
    have := l15_nu_beltrami hh hk0 hk1 hbd hnu (hnorm n).le
    exact ⟨this.1, this.2.1⟩
  have hb1 : IsBeltramiCoeff (nu 1) univ k ∧ (∀ w : ℂ, 1 ≤ ‖w‖ → nu 1 w = 0) := by
    have := l15_nu_beltrami hh hk0 hk1 hbd hnu (t := 1) (by simp)
    exact ⟨this.1, this.2.1⟩
  have hlim : ∀ᵐ z, Tendsto (fun n => nu (r n) z) atTop (𝓝 (nu 1 z)) := by
    refine Filter.Eventually.of_forall fun z => ?_
    by_cases hz : ‖z‖ < 1
    · have hz' : z ∈ unitDisc := mem_ball_zero_iff.2 hz
      have hcont : ContinuousAt (fun s : ℂ => (1 - (‖z‖ : ℂ) ^ 2) ^ 2 * s ^ 2 * conj (h (conj s * z))) 1 := by
        have h1 : ContinuousAt (fun s : ℂ => h (conj s * z)) 1 := by
          have hc : ContinuousAt h (conj (1 : ℂ) * z) := by
            have : conj (1 : ℂ) * z ∈ unitDisc := by simpa using hz'
            exact (hh.differentiableAt (isOpen_ball.mem_nhds this)).continuousAt
          exact hc.comp (f := fun s : ℂ => conj s * z) ((Complex.continuous_conj.mul continuous_const).continuousAt)
        exact (continuousAt_const.mul (continuousAt_id.pow 2)).mul (Complex.continuous_conj.continuousAt.comp h1)
      have hr' : Tendsto (fun n => ((r n : ℝ) : ℂ)) atTop (𝓝 1) := by
        have := (Complex.continuous_ofReal.tendsto 1).comp hr
        rw [Complex.ofReal_one] at this
        exact this
      have := hcont.tendsto.comp hr'
      refine (this.congr fun n => ?_).trans ?_
      · simp only [Function.comp, hnu, if_pos hz]
      · rw [hnu, if_pos hz]
    · have h0 : ∀ t, nu t z = 0 := fun t => by rw [hnu, if_neg hz]
      simp only [h0]
      exact tendsto_const_nhds
  have hsupp' : ∀ n z, 1 < ‖z‖ → nu (r n) z = 0 := fun n z hz => (hbn n).2 z hz.le
  have hu := eq12_1_solution_tendsto_cauchyT (μn := fun n => nu (r n)) (μ := nu 1) (k := k) (p := p) (R := 1)
    hk0 hp hkp (fun n => (hbn n).1) hb1.1 hsupp' (fun z hz => hb1.2 z hz.le) hlim (fun n => (hΩ n).1)
    (fun n => (hΩ n).2) hω hs
  -- passing to the limit in the circle integral
  set J := ∮ z in C(0, R), cauchyT ω z / z ^ 2 with hJ
  have hsph : ∀ z ∈ sphere (0 : ℂ) R, ‖z‖ = R := fun z hz => by simpa using hz
  have hsph0 : ∀ z ∈ sphere (0 : ℂ) R, z ≠ 0 := fun z hz h0 => by
    have := hsph z hz; rw [h0, norm_zero] at this; linarith
  have hint : ∀ f : ℂ → ℂ, Continuous f → CircleIntegrable (fun z => f z / z ^ 2) 0 R := fun f hf =>
    (hf.continuousOn.div (by fun_prop) fun z hz => pow_ne_zero _ (hsph0 z hz)).circleIntegrable hR0.le
  have hsmall : ∀ δ : ℝ, 0 < δ → ‖J‖ ≤ 2 * π * R * (δ / R ^ 2) := by
    intro δ hδ
    obtain ⟨n, hn⟩ := (Metric.tendstoUniformly_iff.1 hu δ hδ).exists
    have hdiff : J = ∮ z in C(0, R), (cauchyT ω z / z ^ 2 - cauchyT (Ω n) z / z ^ 2) := by
      rw [circleIntegral.integral_sub (hint _ hc1) (hint _ (hcn n)), hzero n, sub_zero]
    rw [hdiff]
    refine circleIntegral.norm_integral_le_of_norm_le_const hR0.le fun z hz => ?_
    rw [← sub_div, norm_div, norm_pow, hsph z hz]
    have := hn z
    rw [dist_eq_norm] at this
    exact div_le_div_of_nonneg_right this.le (by positivity)
  by_contra hne
  have hpos : 0 < ‖J‖ := norm_pos_iff.2 hne
  have hpi : 0 < π := Real.pi_pos
  have := hsmall (‖J‖ * R / (4 * π)) (by positivity)
  have e : 2 * π * R * (‖J‖ * R / (4 * π) / R ^ 2) = ‖J‖ / 2 := by field_simp; ring
  rw [e] at this
  linarith

/-- (S5) If `g` is continuous near `0`, real-differentiable at `0`, and `∮_{|z|=R} g(z) z⁻² dz = 0` for all
`0 < R < ε`, then `∂_z g(0) = 0`. -/
theorem r16_dz_of_circle {g : ℂ → ℂ} (hg : DifferentiableAt ℝ g 0) {ε : ℝ} (hε : 0 < ε)
    (hgc : ContinuousOn g (ball (0 : ℂ) ε))
    (hc : ∀ R : ℝ, 0 < R → R < ε → ∮ z in C(0, R), g z / z ^ 2 = 0) : dz g 0 = 0 := by
  set A := dz g 0 with hA
  set B := dzbar g 0 with hB
  set L := fderiv ℝ g 0 with hLdef
  have hL : ∀ v, L v = A * v + B * conj v := fun v => fderiv_eq_dz_dzbar hg v
  have ho := hasFDerivAt_iff_isLittleO_nhds_zero.1 hg.hasFDerivAt
  have hπn : ‖(2 * π * I : ℂ)‖ = 2 * π := by
    rw [norm_mul, norm_mul, Complex.norm_I, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le]
    simp
  have hbound : ∀ c : ℝ, 0 < c → ‖A‖ ≤ c := by
    intro c hc0
    obtain ⟨δ, hδ, hδb⟩ := Metric.eventually_nhds_iff.1 (ho.def hc0)
    set R := min δ ε / 2 with hR
    have hm : 0 < min δ ε := lt_min hδ hε
    have hR0 : 0 < R := by rw [hR]; positivity
    have hRδ : R < δ := by
      have := min_le_left δ ε
      rw [hR]; linarith
    have hRε : R < ε := by
      have := min_le_right δ ε
      rw [hR]; linarith
    set ρ : ℂ → ℂ := fun z => g z - g 0 - L z with hρ
    have hsph : ∀ z ∈ sphere (0 : ℂ) R, z ≠ 0 := fun z hz h0 => by
      rw [mem_sphere_zero_iff_norm, h0, norm_zero] at hz; linarith
    have hnz : ∀ z ∈ sphere (0 : ℂ) R, ‖z‖ = R := fun z hz => by simpa using hz
    have hρb : ∀ z ∈ sphere (0 : ℂ) R, ‖ρ z‖ ≤ c * R := fun z hz => by
      have h1 := hδb (show dist z 0 < δ by rw [dist_zero_right, hnz z hz]; exact hRδ)
      rw [zero_add, hnz z hz] at h1
      exact h1
    have hsub : sphere (0 : ℂ) R ⊆ ball (0 : ℂ) ε := fun z hz => by
      rw [mem_ball_zero_iff, hnz z hz]; exact hRε
    have hgR : ContinuousOn g (sphere (0 : ℂ) R) := hgc.mono hsub
    have hci : ∀ f : ℂ → ℂ, ContinuousOn f (sphere (0 : ℂ) R) → CircleIntegrable f 0 R := fun f hf =>
      hf.circleIntegrable hR0.le
    have hzp : ∀ n : ℤ, ContinuousOn (fun z : ℂ => (z - 0) ^ n) (sphere (0 : ℂ) R) := fun n => by
      refine ContinuousOn.zpow₀ (by fun_prop) _ fun z hz => Or.inl ?_
      simpa using hsph z hz
    have hz1 : ContinuousOn (fun z : ℂ => (z - 0)⁻¹) (sphere (0 : ℂ) R) := by
      refine ContinuousOn.inv₀ (by fun_prop) fun z hz => ?_
      simpa using hsph z hz
    have hρc : ContinuousOn (fun z => ρ z / z ^ 2) (sphere (0 : ℂ) R) :=
      ((hgR.sub continuousOn_const).sub L.continuous.continuousOn).div (by fun_prop)
        fun z hz => pow_ne_zero _ (hsph z hz)
    have hpt : ∀ z ∈ sphere (0 : ℂ) R, g z / z ^ 2 = ((g 0 * (z - 0) ^ (-2 : ℤ) + A * (z - 0)⁻¹) +
        (B * (R : ℂ) ^ 2) * (z - 0) ^ (-3 : ℤ)) + ρ z / z ^ 2 := by
      intro z hz
      have hz0 := hsph z hz
      have hcz : conj z = (R : ℂ) ^ 2 / z := by
        rw [eq_div_iff hz0, mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, hnz z hz]
        push_cast; ring
      simp only [hρ, hL, hcz, sub_zero, zpow_neg, zpow_ofNat]
      field_simp
      ring
    have i1 : CircleIntegrable (fun z : ℂ => g 0 * (z - 0) ^ (-2 : ℤ)) 0 R :=
      hci _ (continuousOn_const.mul (hzp _))
    have i2 : CircleIntegrable (fun z : ℂ => A * (z - 0)⁻¹) 0 R := hci _ (continuousOn_const.mul hz1)
    have i3 : CircleIntegrable (fun z : ℂ => (B * (R : ℂ) ^ 2) * (z - 0) ^ (-3 : ℤ)) 0 R :=
      hci _ (continuousOn_const.mul (hzp _))
    have i12 : CircleIntegrable (fun z : ℂ => g 0 * (z - 0) ^ (-2 : ℤ) + A * (z - 0)⁻¹) 0 R :=
      hci _ ((continuousOn_const.mul (hzp _)).add (continuousOn_const.mul hz1))
    have i123 : CircleIntegrable (fun z : ℂ => (g 0 * (z - 0) ^ (-2 : ℤ) + A * (z - 0)⁻¹) +
        (B * (R : ℂ) ^ 2) * (z - 0) ^ (-3 : ℤ)) 0 R :=
      hci _ (((continuousOn_const.mul (hzp _)).add (continuousOn_const.mul hz1)).add
        (continuousOn_const.mul (hzp _)))
    have i4 : CircleIntegrable (fun z => ρ z / z ^ 2) 0 R := hci _ hρc
    have hinv : ∮ z in C(0, R), (z - 0)⁻¹ = 2 * π * I :=
      circleIntegral.integral_sub_inv_of_mem_ball (mem_ball_self hR0)
    have hinv2 : ∮ z in C(0, R), (z - 0) ^ (-2 : ℤ) = 0 :=
      circleIntegral.integral_sub_zpow_of_ne (by norm_num) _ _ _
    have hinv3 : ∮ z in C(0, R), (z - 0) ^ (-3 : ℤ) = 0 :=
      circleIntegral.integral_sub_zpow_of_ne (by norm_num) _ _ _
    have hI : ∮ z in C(0, R), g z / z ^ 2 = A * (2 * π * I) + ∮ z in C(0, R), ρ z / z ^ 2 := by
      rw [circleIntegral.integral_congr hR0.le hpt, circleIntegral.integral_add i123 i4,
        circleIntegral.integral_add i12 i3, circleIntegral.integral_add i1 i2,
        circleIntegral.integral_const_mul, circleIntegral.integral_const_mul,
        circleIntegral.integral_const_mul, hinv, hinv2, hinv3]
      ring
    rw [hc R hR0 hRε] at hI
    have hJ : ‖∮ z in C(0, R), ρ z / z ^ 2‖ ≤ 2 * π * R * (c * R / R ^ 2) := by
      refine circleIntegral.norm_integral_le_of_norm_le_const hR0.le fun z hz => ?_
      rw [norm_div, norm_pow, hnz z hz]
      exact div_le_div_of_nonneg_right (hρb z hz) (by positivity)
    have hX : A * (2 * π * I) = -∮ z in C(0, R), ρ z / z ^ 2 := by linear_combination (-1 : ℂ) * hI
    have hN : ‖A‖ * (2 * π) ≤ 2 * π * c := by
      have := congrArg norm hX
      rw [norm_mul, hπn, norm_neg] at this
      rw [this]
      calc ‖∮ z in C(0, R), ρ z / z ^ 2‖ ≤ 2 * π * R * (c * R / R ^ 2) := hJ
        _ = 2 * π * c := by field_simp
    have hpi : 0 < 2 * π := by positivity
    nlinarith
  by_contra hne
  have hpos : 0 < ‖A‖ := norm_pos_iff.2 hne
  have := hbound (‖A‖ / 2) (by positivity)
  linarith

/-- (S6) **Regularity** (W-REG D2b): the hydrodynamic solution of `ν^{[1]}` is real-differentiable at `0`, since
`ν^{[1]}` is smooth on `𝔻`; it is continuous (`l15_hydro_data`). -/
theorem r16_regular {h : ℂ → ℂ} (hh : DifferentiableOn ℂ h unitDisc) {k : ℝ} (hk0 : 0 ≤ k) (hk1 : k < 1)
    (hbd : ∀ w ∈ unitDisc, (1 - ‖w‖ ^ 2) ^ 2 * ‖h w‖ ≤ k)
    {nu : ℂ → ℂ → ℂ}
    (hnu : ∀ t w, nu t w = if ‖w‖ < 1 then (1 - ‖w‖ ^ 2) ^ 2 * t ^ 2 * conj (h (conj t * w)) else 0)
    {p : ℝ} (hp : 2 < p) (hkp : k * hilbertNorm p < 1)
    {ω : ℂ → ℂ} (hω : MemLp ω (ENNReal.ofReal p))
    (hs : ω =ᵐ[volume] fun z => nu 1 z * hilbertH ω z + nu 1 z) :
    DifferentiableAt ℝ (cauchyT ω) 0 ∧ Continuous (cauchyT ω) := by
  obtain ⟨hb1, hsupp, hbd1⟩ := l15_nu_beltrami hh hk0 hk1 hbd hnu (t := 1) (by simp)
  -- the coefficient is smooth on `𝔻`
  have hsq : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun w : ℂ => (1 - (‖w‖ : ℂ) ^ 2) ^ 2) := by
    have e : (fun w : ℂ => (1 - (‖w‖ : ℂ) ^ 2) ^ 2) = fun w : ℂ => (1 - ((‖w‖ ^ 2 : ℝ) : ℂ)) ^ 2 := by
      funext w; push_cast; ring
    rw [e]
    exact (contDiff_const.sub (Complex.ofRealCLM.contDiff.comp (contDiff_norm_sq ℝ))).pow 2
  have hcj : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun w : ℂ => conj (h w)) (ball (0 : ℂ) 1) := by
    have h1 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) h (ball (0 : ℂ) 1) :=
      ((hh.contDiffOn isOpen_ball) : ContDiffOn ℂ ((⊤ : ℕ∞) : WithTop ℕ∞) h unitDisc).restrict_scalars ℝ
    exact Complex.conjCLE.contDiff.comp_contDiffOn h1
  have hs₁ : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (nu 1) (ball (0 : ℂ) 1) := by
    refine ((hsq.contDiffOn.mul (contDiffOn_const (c := ((1 : ℂ) ^ 2)))).mul hcj).congr fun w hw => ?_
    rw [hnu, if_pos (mem_ball_zero_iff.1 hw)]
    simp
  have hm₂ : IsBeltramiCoeff (fun _ : ℂ => (0 : ℂ)) univ 0 :=
    ⟨aestronglyMeasurable_const, Filter.Eventually.of_forall fun _ => by simp⟩
  set δ : ℝ := (1 - k) / 2 with hδ
  have hδ0 : 0 < δ := by rw [hδ]; linarith
  have hWk : ∀ P ∈ ball ((1 : ℂ), (0 : ℂ)) δ, ∃ k' < 1,
      IsBeltramiCoeff (fun u => P.1 * nu 1 u + P.2 * (fun _ : ℂ => (0 : ℂ)) u) univ k' := by
    intro P hP
    have hP1 : ‖P.1‖ ≤ 1 + δ := by
      have h1 : dist P.1 1 < δ := by
        have h0 := mem_ball.1 hP
        rw [Prod.dist_eq] at h0
        exact lt_of_le_of_lt (le_max_left _ _) h0
      rw [dist_eq_norm] at h1
      have h2 : ‖P.1‖ ≤ ‖(1 : ℂ)‖ + ‖P.1 - 1‖ := by
        calc ‖P.1‖ = ‖1 + (P.1 - 1)‖ := by congr 1; ring
          _ ≤ ‖(1 : ℂ)‖ + ‖P.1 - 1‖ := norm_add_le _ _
      rw [norm_one] at h2
      linarith
    refine ⟨(1 + δ) * k, ?_, ?_, ?_⟩
    · rw [hδ]; nlinarith
    · exact (aestronglyMeasurable_const.mul hb1.1).add aestronglyMeasurable_const
    · filter_upwards [hb1.2] with u hu
      simp only [mul_zero, add_zero, norm_mul]
      exact mul_le_mul hP1 hu (norm_nonneg _) (by linarith)
  have hmem : ((1 : ℂ), (0 : ℂ)) ∈ ball ((1 : ℂ), (0 : ℂ)) δ := mem_ball_self hδ0
  obtain ⟨hz, -⟩ := wr_ns2_z_regular hb1 hm₂ isOpen_ball hs₁ contDiffOn_const isOpen_ball hWk
  have hC3 := hz _ hmem
  have hfun : (fun u => ((1 : ℂ), (0 : ℂ)).1 * nu 1 u + ((1 : ℂ), (0 : ℂ)).2 * (fun _ : ℂ => (0 : ℂ)) u) = nu 1 := by
    funext u; simp
  rw [hfun] at hC3
  -- the normalized solution in hydrodynamic form
  have hex : ∃ g : ℂ → ℂ, IsNormalizedSolution g (nu 1) := by
    obtain ⟨g, hg, -, -⟩ := thm13_7_normalized_existence hk0 hk1 hb1
    exact ⟨g, hg⟩
  have hN : IsNormalizedSolution (normalizedSolution (nu 1)) (nu 1) := by
    rw [normalizedSolution, dif_pos hex]; exact hex.choose_spec
  obtain ⟨D, -, hGf⟩ := l15_G_formula hk0 hk1 hp hkp hb1 hsupp hω hs hN
  have hrep : cauchyT ω = fun z => D * normalizedSolution (nu 1) z - z + cauchyT ω 0 := by
    funext z
    rw [hGf z]
    have hD : D ≠ 0 := by
      intro h0
      have h1 := hN.2.2.2.1
      rw [hGf 1, h0, inv_zero, zero_mul] at h1
      exact zero_ne_one h1
    field_simp
    ring
  have hNd : DifferentiableAt ℝ (normalizedSolution (nu 1)) 0 :=
    (hC3.differentiableOn (by norm_num)).differentiableAt (isOpen_ball.mem_nhds (mem_ball_self one_pos))
  refine ⟨?_, ?_⟩
  · rw [hrep]
    exact ((hNd.const_mul D).sub differentiableAt_id).add_const _
  · obtain ⟨hKqc, -, -⟩ := l15_hydro_data hk0 hk1 hp hkp hb1 hsupp hω hs
    have hfc : Continuous fun z => z + cauchyT ω z := continuousOn_univ.mp hKqc.2.2.1.1
    refine (hfc.sub continuous_id).congr fun z => ?_
    simp

/-- (S7a) The plane solution `W` of `extB (Λφ)` in the `ι`-chart: `1/W(u) = W'(0)⁻¹ (1/u + T ω(1/u))`, with `ω` the
hydrodynamic solution of `ν^{[1]}` (`l15_G_formula`, `l15_core`, and `W'(0) = D` from the decay of `T ω` at `∞`). -/
theorem r16_W_inv {φ : AInf unitDisc} (hμ : Lambda φ ∈ LinfStarBall) {p : ℝ} (hp : 2 < p)
    (hkp : ‖φ‖ / 2 * hilbertNorm p < 1) {nu : ℂ → ℂ → ℂ}
    (hnu : ∀ t w, nu t w = if ‖w‖ < 1 then (1 - ‖w‖ ^ 2) ^ 2 * t ^ 2 *
      conj ((fun w => -(1 / 2 : ℂ) * conj (AInf.toFun φ (conj w))) (conj t * w)) else 0)
    {ω : ℂ → ℂ} (hω : MemLp ω (ENNReal.ofReal p))
    (hs : ω =ᵐ[volume] fun z => nu 1 z * hilbertH ω z + nu 1 z)
    {W : ℂ → ℂ} (hW : IsNormalizedSolution W (extB (Lambda φ))) :
    deriv W 0 ≠ 0 ∧ ∀ u : ℂ, u ≠ 0 → (W u)⁻¹ = (deriv W 0)⁻¹ * (u⁻¹ + cauchyT ω u⁻¹) := by
  set k := ‖φ‖ / 2 with hk
  have hk0 : 0 ≤ k := by positivity
  have hLn : ‖Lambda φ‖ = k := Lambda_norm_eq φ
  have hk1 : k < 1 := by
    have h' : ‖Lambda φ‖ < 1 := by simpa [LinfStarBall] using hμ
    linarith
  set h : ℂ → ℂ := fun w => -(1 / 2 : ℂ) * conj (AInf.toFun φ (conj w)) with hhdef
  have hh1 : DifferentiableOn ℂ h unitDisc := l15_phi_hol φ
  have hbd : ∀ w ∈ unitDisc, (1 - ‖w‖ ^ 2) ^ 2 * ‖h w‖ ≤ k := l15_phi_bound φ
  obtain ⟨hb1, hs1, -⟩ := l15_nu_beltrami hh1 hk0 hk1 hbd hnu (t := 1) (by simp)
  have hcore : cauchyT ω 0 = 0 := l15_core hh1 hk0 hk1 hbd hnu hp hkp hω hs
  obtain ⟨hβ, hβ0⟩ := l15_extB_beltrami (Lambda φ)
  rw [hLn] at hβ
  have hGn := ahI_invConj_isNormalizedSolution hk0 hk1 hβ hβ0 hW
  have hae : ∀ᵐ w, nxMu2t (extB (Lambda φ)) w = nu 1 w := l15_nu_ae φ hnu
  have hG1 : IsNormalizedSolution (nxInvConj W) (nu 1) :=
    ⟨hGn.1, hGn.2.1, hGn.2.2.1, hGn.2.2.2.1, by
      filter_upwards [hGn.2.2.2.2, hae] with z a b; rw [a, b]⟩
  obtain ⟨D, hD, hGform⟩ := l15_G_formula hk0 hk1 hp hkp hb1 hs1 hω hs hG1
  have hω0 : ω =ᵐ[volume] (closedBall (0 : ℂ) 1).indicator ω :=
    t2_omega_ae_eq_indicator (fun z hz => hs1 z hz.le) hs
  obtain ⟨-, C, R, hCR⟩ := l15_cauchyT_outside hp hω hω0
  set r : ℂ → ℂ := cauchyT ω with hr
  have hr0 : r 0 = 0 := hcore
  have hW0 : W 0 = 0 := hW.2.2.1
  have hWd : DifferentiableOn ℂ W unitDisc := extB_solution_holomorphic hW
  have h0mem : (0 : ℂ) ∈ unitDisc := by simp [unitDisc]
  have hnb : unitDisc ∈ 𝓝 (0 : ℂ) := isOpen_ball.mem_nhds h0mem
  have hWinj : InjOn W univ := hW.1.choose_spec.2.2.1.2.1
  set V : ℂ → ℂ := dslope W 0 with hV
  have hVd : DifferentiableOn ℂ V unitDisc := (differentiableOn_dslope hnb).2 hWd
  have hVu : ∀ u : ℂ, u ≠ 0 → V u = W u / u := by
    intro u hu
    rw [hV, dslope_of_ne _ hu, slope_def_field, hW0, sub_zero, sub_zero]
  have hWne : ∀ u : ℂ, u ≠ 0 → W u ≠ 0 := fun u hu he =>
    hu (hWinj (mem_univ _) (mem_univ _) (he.trans hW0.symm))
  have hWform : ∀ u : ℂ, u ≠ 0 → (W u)⁻¹ = D⁻¹ * (u⁻¹ + r u⁻¹) := by
    intro u hu
    have h1 := hGform u⁻¹
    simp only [nxInvConj, inv_inv] at h1
    rw [h1, hr0, sub_zero]
  set R' : ℝ := max R 1 with hR'
  have hR'0 : 0 < R' := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hsb : ∀ u : ℂ, u ≠ 0 → ‖u‖ < 1 / R' → ‖r u⁻¹‖ ≤ C * ‖u‖ := by
    intro u hu hub
    have hun : 0 < ‖u‖ := norm_pos_iff.2 hu
    have hbig : R < ‖u⁻¹‖ := by
      rw [norm_inv]
      have : R' < ‖u‖⁻¹ := by
        rw [lt_inv_comm₀ hR'0 hun]; rwa [one_div] at hub
      exact lt_of_le_of_lt (le_max_left _ _) this
    have := hCR u⁻¹ hbig
    rwa [norm_inv, div_inv_eq_mul] at this
  have hs0 : Tendsto (fun u : ℂ => r u⁻¹) (𝓝[≠] 0) (𝓝 0) := by
    have hb : Tendsto (fun u : ℂ => |C| * ‖u‖) (𝓝[≠] 0) (𝓝 0) := by
      have : Tendsto (fun u : ℂ => |C| * ‖u‖) (𝓝 0) (𝓝 (|C| * ‖(0 : ℂ)‖)) :=
        (continuous_const.mul continuous_norm).tendsto 0
      simpa using this.mono_left nhdsWithin_le_nhds
    refine squeeze_zero_norm' ?_ hb
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (ball_mem_nhds (0 : ℂ) (one_div_pos.2 hR'0))]
      with u hu1 hu2
    have hu0 : u ≠ 0 := hu1
    have := hsb u hu0 (by simpa using hu2)
    exact this.trans (mul_le_mul_of_nonneg_right (le_abs_self C) (norm_nonneg _))
  have hε0 : Tendsto (fun u : ℂ => u * r u⁻¹) (𝓝[≠] 0) (𝓝 0) := by
    have h1 : Tendsto (fun u : ℂ => u) (𝓝[≠] 0) (𝓝 0) := tendsto_nhdsWithin_of_tendsto_nhds tendsto_id
    simpa using h1.mul hs0
  have hVform : ∀ᶠ u in 𝓝[≠] (0 : ℂ), V u = D / (1 + u * r u⁻¹) := by
    filter_upwards [self_mem_nhdsWithin] with u hu
    have hu0 : u ≠ 0 := hu
    have hX : u⁻¹ + r u⁻¹ ≠ 0 := by
      intro hX
      have := hWform u hu0
      rw [hX, mul_zero] at this
      exact hWne u hu0 (inv_eq_zero.1 this)
    have h1 : W u = D * (u⁻¹ + r u⁻¹)⁻¹ := by
      have := hWform u hu0
      rw [← inv_inv (W u), this, mul_inv, inv_inv]
    have h2 : 1 + u * r u⁻¹ = u * (u⁻¹ + r u⁻¹) := by field_simp
    rw [hVu u hu0, h1, h2]
    field_simp
  have hVcont : ContinuousAt V 0 := (hVd.differentiableAt hnb).continuousAt
  have hV0 : V 0 = D := by
    have h1 : Tendsto V (𝓝[≠] 0) (𝓝 (V 0)) := hVcont.tendsto.mono_left nhdsWithin_le_nhds
    have h2 : Tendsto (fun u : ℂ => D / (1 + u * r u⁻¹)) (𝓝[≠] 0) (𝓝 (D / (1 + 0))) :=
      tendsto_const_nhds.div (tendsto_const_nhds.add hε0) (by simp)
    rw [add_zero, div_one] at h2
    exact tendsto_nhds_unique h1 (h2.congr' (hVform.mono fun u hu => hu.symm))
  have hd : deriv W 0 = D := by rw [← hV0, hV, dslope_same]
  refine ⟨by rw [hd]; exact hD, fun u hu => ?_⟩
  rw [hd]
  exact hWform u hu

/-- (S7b) **Chart identity.**  The map of Remark 1.6 is `z ↦ z + T ω(z)`. -/
theorem r16_chart {φ : AInf unitDisc} (hμ : Lambda φ ∈ LinfStarBall) (hh : Lambda φ ∈ harmonicBeltrami)
    {p : ℝ} (hp : 2 < p) (hkp : ‖φ‖ / 2 * hilbertNorm p < 1) {nu : ℂ → ℂ → ℂ}
    (hnu : ∀ t w, nu t w = if ‖w‖ < 1 then (1 - ‖w‖ ^ 2) ^ 2 * t ^ 2 *
      conj ((fun w => -(1 / 2 : ℂ) * conj (AInf.toFun φ (conj w))) (conj t * w)) else 0)
    {ω : ℂ → ℂ} (hω : MemLp ω (ENNReal.ofReal p))
    (hs : ω =ᵐ[volume] fun z => nu 1 z * hilbertH ω z + nu 1 z) :
    (fun z : ℂ => finPart (inversion (mobiusExt 1 0 (deriv (deriv (fB (Lambda φ))) 0 / 2) 1
      (wB (Lambda φ) (inversion z))))) = fun z => z + cauchyT ω z := by
  -- `cauchyT ω 0 = 0`
  have hcore : cauchyT ω 0 = 0 := by
    set k := ‖φ‖ / 2 with hk
    have hk0 : 0 ≤ k := by positivity
    have hLn : ‖Lambda φ‖ = k := Lambda_norm_eq φ
    have hk1 : k < 1 := by
      have h' : ‖Lambda φ‖ < 1 := by simpa [LinfStarBall] using hμ
      linarith
    exact l15_core (l15_phi_hol φ) hk0 hk1 (l15_phi_bound φ) hnu hp hkp hω hs
  have hconj2 := l15_conj2 hμ hh
  -- the Möbius data of `w^μ` (as in `l15_fB_jets`)
  obtain ⟨hB, -⟩ := wB_spec hμ
  obtain ⟨M, hM, W, hW, hfin, hinf, f, hf, hf0, hf1, hfp⟩ := hB
  obtain ⟨a, b, c, d, hdet, rfl⟩ := hM
  obtain ⟨hw1ne, hWinv⟩ := r16_W_inv hμ hp hkp hnu hω hs hW
  have hW2 := l15_W_second hμ hh hW
  have hhol : DifferentiableOn ℂ W unitDisc := extB_solution_holomorphic hW
  have h0mem : (0 : ℂ) ∈ unitDisc := by simp [unitDisc]
  have hWan : AnalyticAt ℂ W 0 := hhol.analyticOnNhd isOpen_ball 0 h0mem
  have hW0 : W 0 = 0 := hW.2.2.1
  have hden : ∀ z ∈ unitDisc, c * W z + d ≠ 0 := by
    intro z hz he
    have hfin' := (hfin z).symm.trans (hf z hz)
    rw [mobiusExt_coe_of_eq_zero he] at hfin'
    exact OnePoint.infty_ne_coe _ hfin'
  have hrep : EqOn (fB (Lambda φ)) (fun z => mobiusFn a b c d (W z)) unitDisc := by
    intro z hz
    rw [fB, hfin z, mobiusExt_coe (hden z hz)]
    rfl
  have hnhds : unitDisc ∈ 𝓝 (0 : ℂ) := isOpen_ball.mem_nhds h0mem
  have hev : fB (Lambda φ) =ᶠ[𝓝 (0 : ℂ)] fun z => mobiusFn a b c d (W z) :=
    Filter.eventuallyEq_of_mem hnhds hrep
  obtain ⟨hF0, hF1, -⟩ := fB_normalization (Lambda φ)
  have hd0 : c * W 0 + d ≠ 0 := hden 0 h0mem
  rw [hW0, mul_zero, zero_add] at hd0
  obtain ⟨j1, j2⟩ := mobius_comp_first_second (a := a) (b := b) (c := c) (d := d) hWan
    (by rw [hW0, mul_zero, zero_add]; exact hd0)
  have e0 : fB (Lambda φ) 0 = b / d := by
    rw [hev.eq_of_nhds]
    simp [mobiusFn, hW0]
  have hb : b = 0 := by
    rw [hF0] at e0
    have := e0.symm
    rw [div_eq_zero_iff] at this
    exact this.resolve_right hd0
  subst hb
  have e1 : deriv (fB (Lambda φ)) 0 = (a * d / d ^ 2) * deriv W 0 := by
    rw [hev.deriv_eq, j1, hW0]
    simp
  have e2 : deriv (deriv (fB (Lambda φ))) 0 = (-(2 * c * (a * d - 0 * c)) / (c * 0 + d) ^ 3) * (deriv W 0) ^ 2 +
      ((a * d - 0 * c) / (c * 0 + d) ^ 2) * deriv (deriv W) 0 := by
    rw [hev.deriv.deriv_eq, j2, hW0]
  rw [hW2] at e2
  set w1 := deriv W 0 with hw1
  have hd : d ≠ 0 := hd0
  have h1 : a * w1 = d := by
    have := e1.symm.trans hF1
    field_simp at this
    linear_combination this
  have ha : a ≠ 0 := by
    intro ha0; rw [ha0, zero_mul] at h1; exact hd h1.symm
  have hc' : deriv (deriv (fB (Lambda φ))) 0 / 2 = -c / a := by
    rw [e2, show w1 = d / a by rw [eq_div_iff ha, mul_comm]; exact h1]
    simp only [mul_zero, zero_mul, add_zero, zero_add, sub_zero]
    field_simp
  rw [hc']
  funext z
  by_cases hz : z = 0
  · subst hz
    have hinv0 : inversion ((0 : ℂ) : ExtPlane) = extInf := by
      unfold inversion; exact mobiusExt_coe_of_eq_zero (by ring)
    rw [hinv0, ← hc', hconj2, hcore, add_zero]
    unfold inversion
    rw [mobiusExt_infty_of_ne one_ne_zero]
    simp [finPart]
  · have hinvz : inversion (z : ExtPlane) = ((z⁻¹ : ℂ) : ExtPlane) := by
      unfold inversion
      rw [mobiusExt_coe (by simpa using hz)]
      simp [mobiusFn]
    have hzi : z⁻¹ ≠ 0 := inv_ne_zero hz
    have hWinj : InjOn W univ := hW.1.choose_spec.2.2.1.2.1
    set u := W z⁻¹ with hu
    have hu0 : u ≠ 0 := fun he => hzi (hWinj (mem_univ _) (mem_univ _) (he.trans hW0.symm))
    have hkey : finPart (inversion (mobiusExt 1 0 (-c / a) 1 (mobiusExt a 0 c d (u : ExtPlane)))) =
        d / (a * u) := by
      unfold inversion
      by_cases hcu : c * u + d = 0
      · have hc0 : c ≠ 0 := by
          intro hc0; rw [hc0, zero_mul, zero_add] at hcu; exact hd hcu
        have hca : -c / a ≠ 0 := div_ne_zero (neg_ne_zero.2 hc0) ha
        rw [mobiusExt_coe_of_eq_zero hcu, mobiusExt_infty_of_ne hca]
        have hx : (1 / (-c / a) : ℂ) ≠ 0 := one_div_ne_zero hca
        rw [mobiusExt_coe (by simpa using hx)]
        simp only [finPart, mobiusFn, OnePoint.elim_some, id_eq]
        have hdu : d = -(c * u) := by linear_combination hcu
        rw [hdu]
        field_simp
        simp only [zero_mul, neg_zero, zero_add, add_zero]
        rw [div_neg, mul_div_cancel_left₀ c ha]
      · rw [mobiusExt_coe hcu]
        have hq : -c / a * mobiusFn a 0 c d u + 1 = d / (c * u + d) := by
          simp only [mobiusFn]
          field_simp
          ring
        have hden2 : -c / a * mobiusFn a 0 c d u + 1 ≠ 0 := by
          rw [hq]; exact div_ne_zero hd hcu
        rw [mobiusExt_coe hden2]
        have hv : mobiusFn 1 0 (-c / a) 1 (mobiusFn a 0 c d u) = a * u / d := by
          rw [show mobiusFn 1 0 (-c / a) 1 (mobiusFn a 0 c d u) =
            (1 * mobiusFn a 0 c d u + 0) / (-c / a * mobiusFn a 0 c d u + 1) from rfl, hq]
          have hcu' : u * c + d ≠ 0 := by rwa [mul_comm]
          simp only [mobiusFn]
          field_simp
          ring
        have hne : 1 * mobiusFn 1 0 (-c / a) 1 (mobiusFn a 0 c d u) + 0 ≠ 0 := by
          rw [hv, one_mul, add_zero]; exact div_ne_zero (mul_ne_zero ha hu0) hd
        rw [mobiusExt_coe hne]
        simp only [finPart, OnePoint.elim_some, id_eq]
        rw [show mobiusFn 0 1 1 0 (mobiusFn 1 0 (-c / a) 1 (mobiusFn a 0 c d u)) =
          (0 * mobiusFn 1 0 (-c / a) 1 (mobiusFn a 0 c d u) + 1) /
            (1 * mobiusFn 1 0 (-c / a) 1 (mobiusFn a 0 c d u) + 0) from rfl, hv]
        field_simp
        ring
    rw [hinvz, hfin z⁻¹, ← hu, hkey]
    have hW1 := hWinv z⁻¹ hzi
    rw [inv_inv, ← hu] at hW1
    have hdiv : d / (a * u) = w1 * u⁻¹ := by
      rw [← h1]; field_simp
    rw [hdiv, hW1]
    field_simp

/-- Assembly of `remark_1_6` (body for `S1_2_Homogeneous.remark_1_6`, relocated here at round end). -/
theorem r16_remark_1_6 {μ : LinfStar} (hμ : μ ∈ LinfStarBall) (hh : μ ∈ harmonicBeltrami) :
    finPart (inversion (mobiusExt 1 0 (deriv (deriv (fB μ)) 0 / 2) 1 (wB μ (inversion (0 : ℂ))))) = 0 ∧
      dz (fun z : ℂ => finPart (inversion
        (mobiusExt 1 0 (deriv (deriv (fB μ)) 0 / 2) 1 (wB μ (inversion z))))) 0 = 1 := by
  obtain ⟨φ, rfl⟩ := Lambda_surjective_harmonic hh
  set k := ‖φ‖ / 2 with hk
  have hk0 : 0 ≤ k := by positivity
  have hLn : ‖Lambda φ‖ = k := Lambda_norm_eq φ
  have hk1 : k < 1 := by
    have h' : ‖Lambda φ‖ < 1 := by simpa [LinfStarBall] using hμ
    linarith
  set h : ℂ → ℂ := fun w => -(1 / 2 : ℂ) * conj (AInf.toFun φ (conj w)) with hhdef
  have hh1 : DifferentiableOn ℂ h unitDisc := l15_phi_hol φ
  have hbd : ∀ w ∈ unitDisc, (1 - ‖w‖ ^ 2) ^ 2 * ‖h w‖ ≤ k := l15_phi_bound φ
  set nu : ℂ → ℂ → ℂ := fun t w => if ‖w‖ < 1 then (1 - ‖w‖ ^ 2) ^ 2 * t ^ 2 * conj (h (conj t * w)) else 0
    with hnudef
  have hnu : ∀ t w, nu t w = if ‖w‖ < 1 then (1 - ‖w‖ ^ 2) ^ 2 * t ^ 2 * conj (h (conj t * w)) else 0 :=
    fun _ _ => rfl
  obtain ⟨p, hp, -, hkp⟩ := eq12_1_exists_exponent hk1 (show (2 : ℝ) < 3 by norm_num)
  obtain ⟨hb1, -, -⟩ := l15_nu_beltrami hh1 hk0 hk1 hbd hnu (t := 1) (by simp)
  obtain ⟨ω, hω, hsol, -⟩ := eq12_1_solution hk0 hb1 hp hkp
    (l15_nu_Lp hh1 hk0 hk1 hbd hnu (t := 1) (by simp) (by linarith)).1
  have hc := r16_chart hμ hh hp hkp hnu hω hsol
  have h0 : cauchyT ω 0 = 0 := l15_core hh1 hk0 hk1 hbd hnu hp hkp hω hsol
  obtain ⟨hreg, hcont⟩ := r16_regular hh1 hk0 hk1 hbd hnu hp hkp hω hsol
  have hdz : dz (cauchyT ω) 0 = 0 := r16_dz_of_circle hreg one_pos hcont.continuousOn fun R hR0 hR1 =>
    r16_one_circle hh1 hk0 hk1 hbd hnu hp hkp hω hsol hR0 (by linarith)
  refine ⟨?_, ?_⟩
  · have := congrFun hc 0
    rw [this, h0, add_zero]
  · rw [hc]
    have hd : fderiv ℝ (fun z : ℂ => z + cauchyT ω z) 0 =
        ContinuousLinearMap.id ℝ ℂ + fderiv ℝ (cauchyT ω) 0 := by
      exact ((hasFDerivAt_id (0 : ℂ)).add hreg.hasFDerivAt).fderiv
    have hdz' := hdz
    unfold dz at hdz' ⊢
    rw [hd]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.id_apply]
    linear_combination hdz' - (1 / 2 : ℂ) * I_sq

/-- **Remark 1.6** (TT:724). For harmonic `μ`, with `c = (f^μ)''(0)/2`, the map `f = ι ∘ (λ_c ∘ f^μ) ∘ ι` satisfies
`f(0) = 0` and `f_z(0) = 1`.
- **[CORRECTION 2026-10-25]** The renormalization `λ_c` is inserted (it is the identity for TT's normalization).
- **[CORRECTION 2026-10-26]** `f_z` is the Wirtinger derivative `dz`: `f` is only quasiconformal at `0` (its Beltrami
  coefficient is `ι^*μ`, nonzero at `0` in general), so the complex derivative `deriv` is the junk value `0` (found by 下属2). -/
theorem remark_1_6 {μ : LinfStar} (hμ : μ ∈ LinfStarBall) (hh : μ ∈ harmonicBeltrami) :
    finPart (inversion (mobiusExt 1 0 (deriv (deriv (fB μ)) 0 / 2) 1 (wB μ (inversion (0 : ℂ))))) = 0 ∧
      dz (fun z : ℂ => finPart (inversion
        (mobiusExt 1 0 (deriv (deriv (fB μ)) 0 / 2) 1 (wB μ (inversion z))))) 0 = 1 :=
  r16_remark_1_6 hμ hh

end TakhtajanTeo
