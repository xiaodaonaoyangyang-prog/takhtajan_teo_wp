import TakhtajanTeo.Appendix.AppACor4

/-!
# Appendix A, Corollary A.6 (`a6_`, 下属2, Program G)

Host: new module `Appendix/AppACor6.lean`. The leader relocates `cor_A_6` here, with body `a6_cor_A_6 hp hw hq hv hlim`.

Route.
- Clause (i), T1 (`a6_ext_schwarzian_tendsto`), a Radon–Riesz argument on `A₂(𝔻*)` (`a6_RR`):
  - `wₙ → v` comes from `tcg_fibre_parameter_continuous` (`a6_w_tendsto`).
  - `weldG(μₙ, wₙ) → weldG(μ, v)` locally uniformly on `𝔻*` (`a6_weldG_LU`): joint continuity of the welding
    (`tcg_welding_class_continuous_family`) and of Möbius maps in their coefficients (`a6_mob_tendsto`). Weierstrass
    then gives locally uniform convergence of the Schwarzians (`a6_S_LU`).
  - `‖𝒮(weldG μ w)‖ = ‖𝒮(𝗀_μ)‖ = ‖β([μ]⁻¹)‖` (`appa2_normA2_schwarzian_weldG`, `ab112_normA2_G`, `a6_normS_gMu`), and
    `invT` is continuous on `T₀(1)` (Ch1 `thm_3_8`), so the norms converge (`a6_norm_tendsto`).
- Clause (ii), T2 (`a6_ext_inverse`): the inverse function theorem for `Ψ*` on `Ã₂¹(𝔻*)` (Lemma A.5).
  - Inversion `q(ζ) = -ψ(1/ζ)/ζ²` turns `Ψ*` into `q ↦ q' - ½q² + 2q/ζ` on `{q ∈ A₂¹(𝔻) | q(0) = 0}` (`a55_refl`,
    `a55_inv_normA21`, `a55_refl_norm`).
  - Coordinates are `q' ∈ A2 unitDisc` (complete). The derivative `h ↦ h' - q₀h + 2h/ζ` is bijective
    (`a6_linear_bij`): the explicit solution `ζ⁻²E⁻¹∫₀^ζ s²Eϕ`, with energy control from boundary smallness
    (`a6_energy`).
  - The local inverse is identified by global injectivity (`a6_K_injective`), as in `a4_inverse`.
-/

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal NNReal ComplexConjugate Classical Real

noncomputable section

namespace TakhtajanTeo

open LiZhongQC Ch2

namespace AppA

/-! ### T2 support -/

/-- `q ↦ q/ζ` is bounded `A₂¹(𝔻) → A₂(𝔻)` on functions vanishing at `0` (Parseval). -/
theorem a6_dslope_A2 {q : ℂ → ℂ} (hq : q ∈ A21fun unitDisc) (hq0 : q 0 = 0) :
    dslope q 0 ∈ A2fun unitDisc ∧ normA2 unitDisc (dslope q 0) ≤ normA21 unitDisc q := by
  let c : ℕ → ℂ := fun n => (n.factorial : ℂ)⁻¹ * iteratedDeriv n q 0
  have hqs : ∀ z ∈ unitDisc, HasSum (fun n => c n * z ^ n) (q z) := by
    intro z hz
    have h' := Complex.hasSum_taylorSeries_on_ball (c := 0) (r := 1) hq.1 hz
    refine h'.congr_fun fun n => ?_
    simp only [c, sub_zero, smul_eq_mul]
    ring
  have hc0 : c 0 = 0 := by simp [c, hq0]
  have hFs : ∀ z ∈ unitDisc \ {0}, HasSum (fun n => c (n + 1) * z ^ n) (dslope q 0 z) := by
    intro z hz
    have hz0 : z ≠ 0 := hz.2
    rw [dslope_of_ne q hz0, slope_def_field, hq0, sub_zero, sub_zero]
    have h := (hasSum_nat_add_iff' 1).mpr (hqs z hz.1)
    simp only [Finset.range_one, Finset.sum_singleton, hc0, zero_mul, sub_zero] at h
    have h2 := h.div_const z
    refine h2.congr_fun fun n => ?_
    field_simp
    ring
  have hd : DifferentiableOn ℂ (dslope q 0) unitDisc :=
    (Complex.differentiableOn_dslope (isOpen_ball.mem_nhds (mem_ball_self one_pos))).mpr hq.1
  have hW := a55_weighted_le hFs
  have hpars := s2c_area_parseval_lintegral hqs
  have hqsq : (∫⁻ z in unitDisc, ENNReal.ofReal (‖q z‖ ^ 2)) = normA21 unitDisc q ^ 2 := by
    rw [a55_normA21_sq]
    exact lintegral_congr fun z => a55_ofReal_sq _
  have hL : normA2 unitDisc (dslope q 0) ^ 2 =
      ∫⁻ z in unitDisc, ENNReal.ofReal (‖dslope q 0 z‖ ^ 2 * (rho z)⁻¹) := by
    rw [a55_normA2_sq]
    refine setLIntegral_congr_fun measurableSet_ball fun z _ => ?_
    rw [ENNReal.ofReal_mul (sq_nonneg _), a55_ofReal_sq]
  have hcoef : ∀ n : ℕ, ENNReal.ofReal ((π / 2) * (‖c (n + 1)‖ ^ 2 /
      (((n : ℝ) + 1) * ((n : ℝ) + 2) * ((n : ℝ) + 3)))) ≤
      ENNReal.ofReal (π * ‖c (n + 1)‖ ^ 2 / (((n + 1 : ℕ) : ℝ) + 1)) := by
    intro n
    apply ENNReal.ofReal_le_ofReal
    rw [Nat.cast_add, Nat.cast_one]
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have hx : 0 ≤ ‖c (n + 1)‖ ^ 2 := sq_nonneg _
    rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_nonneg hx hn, mul_nonneg (mul_nonneg hx hn) hn, Real.pi_pos,
      mul_nonneg Real.pi_pos.le hx, mul_nonneg (mul_nonneg Real.pi_pos.le hx) hn,
      mul_nonneg (mul_nonneg (mul_nonneg Real.pi_pos.le hx) hn) hn]
  have hshift : (∑' n : ℕ, ENNReal.ofReal (π * ‖c (n + 1)‖ ^ 2 / (((n + 1 : ℕ) : ℝ) + 1))) ≤
      ∑' n, ENNReal.ofReal (π * ‖c n‖ ^ 2 / ((n : ℝ) + 1)) :=
    le_add_self.trans
      (tsum_eq_zero_add' (f := fun n : ℕ => ENNReal.ofReal (π * ‖c n‖ ^ 2 / ((n : ℝ) + 1))) ENNReal.summable).ge
  have hle : normA2 unitDisc (dslope q 0) ^ 2 ≤ normA21 unitDisc q ^ 2 := by
    rw [hL, ← hqsq, hpars]
    exact hW.trans ((ENNReal.tsum_le_tsum hcoef).trans hshift)
  have hle' := a55_le_of_sq_le hle
  exact ⟨⟨hd, hle'.trans_lt hq.2⟩, hle'⟩

/-- The energy estimate of `linearized_Psi_solution_A21_of_boundary_small`, with the equation required only near the
boundary (the coefficient may be singular inside). -/
theorem a6_energy {ψ φ ϕ : ℂ → ℂ} {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (hφ : DifferentiableOn ℂ φ unitDisc) (hϕ : ϕ ∈ A2fun unitDisc)
    (heq : ∀ z ∈ unitDisc, s < ‖z‖ → deriv φ z - ψ z * φ z = ϕ z)
    (hs : ∀ z ∈ unitDisc, s < ‖z‖ → (1 - ‖z‖ ^ 2) * ‖ψ z‖ ≤ 1 / 4) : φ ∈ A21fun unitDisc := by
  let H : ℂ → ℝ := fun z => (1 - ‖z‖ ^ 2) ^ 2 * ‖deriv φ z‖ ^ 2
  have hH : ContinuousOn H unitDisc :=
    (by fun_prop : ContinuousOn (fun z : ℂ => (1 - ‖z‖ ^ 2) ^ 2) unitDisc).mul
      ((hφ.deriv isOpen_ball).continuousOn.norm.pow 2)
  have hsub (r : ℝ) (hr : r < 1) : closedBall (0 : ℂ) r ⊆ unitDisc := by
    intro z hz
    exact mem_ball_zero_iff.mpr ((mem_closedBall_zero_iff.mp hz).trans_lt hr)
  obtain ⟨B, hB⟩ := (isCompact_closedBall (0 : ℂ) s).exists_bound_of_continuousOn
    (hH.mono (hsub s hs1))
  let J : ℂ → ℝ := fun z => 8 * (‖ϕ z‖ ^ 2 * (rho z)⁻¹) + max B 0
  have hJi : IntegrableOn J unitDisc :=
    ((A2fun.integrable_weighted_sq (D := unitDisc) isOpen_ball hϕ).const_mul 8).add
      (integrableOn_const (show volume unitDisc ≠ ∞ from measure_ball_lt_top.ne))
  have hJ0 (z : ℂ) : 0 ≤ J z := by dsimp [J, rho]; positivity
  have hpoint (z : ℂ) (hz : z ∈ unitDisc) : H z ≤ J z + (1 / 4) * ‖φ z‖ ^ 2 := by
    by_cases hzs : ‖z‖ ≤ s
    · have hb := hB z (mem_closedBall_zero_iff.mpr hzs)
      have hH0 : 0 ≤ H z := by dsimp [H]; positivity
      rw [Real.norm_eq_abs, abs_of_nonneg hH0] at hb
      have hpos : 0 ≤ 8 * (‖ϕ z‖ ^ 2 * (rho z)⁻¹) := by unfold rho; positivity
      dsimp [J]
      nlinarith [le_max_left B 0, sq_nonneg ‖φ z‖]
    · have hz1 : ‖z‖ < 1 := mem_ball_zero_iff.mp hz
      have hzs' : s < ‖z‖ := lt_of_not_ge hzs
      have hw : 0 ≤ 1 - ‖z‖ ^ 2 := by nlinarith [norm_nonneg z]
      have hψsq := pow_le_pow_left₀ (mul_nonneg hw (norm_nonneg _)) (hs z hz hzs') 2
      rw [mul_pow] at hψsq
      have hψscaled := mul_le_mul_of_nonneg_right hψsq (sq_nonneg ‖φ z‖)
      have hd : deriv φ z = ψ z * φ z + ϕ z := by
        have he := heq z hz hzs'
        linear_combination he
      have hn : ‖deriv φ z‖ ≤ ‖ψ z‖ * ‖φ z‖ + ‖ϕ z‖ := by
        rw [hd]
        simpa only [norm_mul] using norm_add_le (ψ z * φ z) (ϕ z)
      have hdSq : ‖deriv φ z‖ ^ 2 ≤ 2 * (‖ψ z‖ ^ 2 * ‖φ z‖ ^ 2) + 2 * ‖ϕ z‖ ^ 2 := by
        nlinarith [sq_nonneg (‖ψ z‖ * ‖φ z‖ - ‖ϕ z‖),
          mul_nonneg (sub_nonneg.mpr hn)
            (by positivity : 0 ≤ ‖ψ z‖ * ‖φ z‖ + ‖ϕ z‖ + ‖deriv φ z‖)]
      have hm := mul_le_mul_of_nonneg_left hdSq (sq_nonneg (1 - ‖z‖ ^ 2))
      dsimp [H, J, rho]
      rw [inv_div]
      nlinarith [hm, hψscaled, le_max_right B 0, sq_nonneg ‖φ z‖]
  apply a21_of_uniform_disk_mass hφ
  refine ⟨4 * (∫ z in unitDisc, J z) + 2 * π * ‖φ 0‖ ^ 2, ?_⟩
  intro r hr0 hr1
  have hφi : IntegrableOn (fun z => ‖φ z‖ ^ 2) (ball (0 : ℂ) r) :=
    (((hφ.continuousOn.norm.pow 2).mono (hsub r hr1)).integrableOn_compact
      (isCompact_closedBall (0 : ℂ) r)).mono_set ball_subset_closedBall
  have hHi : IntegrableOn H (ball (0 : ℂ) r) :=
    ((hH.mono (hsub r hr1)).integrableOn_compact
      (isCompact_closedBall (0 : ℂ) r)).mono_set ball_subset_closedBall
  have hrd : ball (0 : ℂ) r ⊆ unitDisc := ball_subset_ball hr1.le
  have hJr := hJi.mono_set hrd
  have hupper : (∫ z in ball (0 : ℂ) r, H z) ≤
      (∫ z in unitDisc, J z) + (1 / 4) * ∫ z in ball (0 : ℂ) r, ‖φ z‖ ^ 2 := by
    have hi := setIntegral_mono_on hHi (hJr.add (hφi.const_mul (1 / 4))) measurableSet_ball
      (fun z hz => hpoint z (hrd hz))
    simp only [Pi.add_apply] at hi
    rw [integral_add hJr (hφi.const_mul (1 / 4)), integral_const_mul] at hi
    have hJle := setIntegral_mono_set hJi (Eventually.of_forall hJ0) (Eventually.of_forall hrd)
    linarith
  have hlower := eq_1_2_of_differentiable hφ hr0 hr1
  change (1 / 2) * (∫ z in ball (0 : ℂ) r, ‖φ z‖ ^ 2) - π / 2 * ‖φ 0‖ ^ 2 * r ^ 2 ≤
    ∫ z in ball (0 : ℂ) r, H z at hlower
  have hr2 : r ^ 2 ≤ 1 := by nlinarith
  have herror := mul_le_mul_of_nonneg_left hr2 (show 0 ≤ π / 2 * ‖φ 0‖ ^ 2 by positivity)
  nlinarith

/-- **Bijectivity of the inverted linearized `Ψ*`** (Lemma A.5 at an arbitrary base point). For every
`q₀ ∈ A₂¹(𝔻)` and `ϕ ∈ A₂(𝔻)` the equation `h' - q₀h + 2h/ζ = ϕ` (with `h/ζ` written `dslope h 0`) has a solution
`h ∈ A₂¹(𝔻)` with `h(0) = 0`, namely `h = (ζ²E)⁻¹∫₀^ζ s²Eϕ`, `E = exp ∫q₀`; and the homogeneous equation has only
the zero solution with `h(0) = 0` (multiply by `ζ²`). -/
theorem a6_linear_bij {q₀ : ℂ → ℂ} (hq₀ : q₀ ∈ A21fun unitDisc) :
    (∀ ϕ ∈ A2fun unitDisc, ∃ h ∈ A21fun unitDisc, h 0 = 0 ∧
      EqOn (fun z => deriv h z - q₀ z * h z + 2 * dslope h 0 z) ϕ unitDisc) ∧
    (∀ h : ℂ → ℂ, DifferentiableOn ℂ h unitDisc → h 0 = 0 →
      EqOn (fun z => deriv h z - q₀ z * h z + 2 * dslope h 0 z) 0 unitDisc → EqOn h 0 unitDisc) := by
  have h0D : (0 : ℂ) ∈ unitDisc := mem_ball_self one_pos
  refine ⟨?_, ?_⟩
  · intro ϕ hϕ
    obtain ⟨H, hH⟩ := hq₀.1.isExactOn_ball
    let E : ℂ → ℂ := fun z => Complex.exp (H z)
    have hE : ∀ z ∈ unitDisc, HasDerivAt E (q₀ z * E z) z := fun z hz => by
      have := (hH z hz).cexp
      simpa only [E, mul_comm] using this
    have hEd : DifferentiableOn ℂ E unitDisc := fun z hz => (hE z hz).differentiableAt.differentiableWithinAt
    have hE0 : ∀ z, E z ≠ 0 := fun z => Complex.exp_ne_zero _
    let Q : ℂ → ℂ := fun s => s ^ 2 * ϕ s / E s
    have hQ : DifferentiableOn ℂ Q unitDisc :=
      ((differentiableOn_id.pow 2).mul hϕ.1).div hEd (fun z _ => hE0 z)
    let P : ℂ → ℂ := fun z => ∫ t in (0 : ℝ)..1, Q ((t : ℂ) * z) * z
    have hP : ∀ z ∈ unitDisc, HasDerivAt P (Q z) z := fun z hz => disk_segment_integral_hasDerivAt hQ hz
    let F : ℂ → ℂ := fun z => E z * P z
    have hF : ∀ z ∈ unitDisc, HasDerivAt F (q₀ z * F z + z ^ 2 * ϕ z) z := by
      intro z hz
      have := (hE z hz).mul (hP z hz)
      convert this using 1
      simp only [F, Q]
      field_simp [hE0 z]
    let h : ℂ → ℂ := fun z => if z = 0 then 0 else F z / z ^ 2
    have hh0 : h 0 = 0 := by simp [h]
    have hhne : ∀ z, z ≠ 0 → h z = F z / z ^ 2 := fun z hz => by simp [h, hz]
    -- the bound `‖P z‖ ≤ M‖z‖³` near `0`
    have hsub : closedBall (0 : ℂ) (1 / 2) ⊆ unitDisc := closedBall_subset_ball (by norm_num)
    obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : ℂ) (1 / 2)).exists_bound_of_continuousOn
      ((hϕ.1.div hEd (fun z _ => hE0 z)).continuousOn.mono hsub)
    have hPb : ∀ z : ℂ, ‖z‖ ≤ 1 / 2 → ‖P z‖ ≤ M * ‖z‖ ^ 3 := by
      intro z hz
      have hb : ∀ t ∈ Set.uIoc (0 : ℝ) 1, ‖Q ((t : ℂ) * z) * z‖ ≤ M * ‖z‖ ^ 3 := by
        intro t ht
        rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht
        have htz : ‖(t : ℂ) * z‖ ≤ ‖z‖ := by
          rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg ht.1.le]
          exact mul_le_of_le_one_left (norm_nonneg z) ht.2
        have hm := hM ((t : ℂ) * z) (mem_closedBall_zero_iff.mpr (htz.trans hz))
        have hQe : Q ((t : ℂ) * z) = ((t : ℂ) * z) ^ 2 * (ϕ ((t : ℂ) * z) / E ((t : ℂ) * z)) := by
          simp only [Q]; ring
        rw [hQe, norm_mul, norm_mul, norm_pow]
        have hM0 : 0 ≤ M := (norm_nonneg _).trans hm
        calc ‖(t : ℂ) * z‖ ^ 2 * ‖ϕ ((t : ℂ) * z) / E ((t : ℂ) * z)‖ * ‖z‖ ≤ ‖z‖ ^ 2 * M * ‖z‖ := by
              gcongr
              exact hm
          _ = M * ‖z‖ ^ 3 := by ring
      have := intervalIntegral.norm_integral_le_of_norm_le_const hb
      rw [sub_zero, abs_one, mul_one] at this
      exact this
    -- continuity of `h` at `0`
    have hcont : ContinuousAt h 0 := by
      have hEc : ContinuousAt E 0 := (hE 0 h0D).continuousAt
      have hlim : Tendsto (fun z => ‖E z‖ * M * ‖z‖) (𝓝 0) (𝓝 0) := by
        have hc : ContinuousAt (fun z => ‖E z‖ * M * ‖z‖) 0 :=
          (hEc.norm.mul continuousAt_const).mul continuous_norm.continuousAt
        simpa using hc.tendsto
      rw [ContinuousAt, hh0]
      refine squeeze_zero_norm' ?_ hlim
      filter_upwards [Metric.ball_mem_nhds (0 : ℂ) (by norm_num : (0 : ℝ) < 1 / 2)] with z hz
      have hz' : ‖z‖ < 1 / 2 := mem_ball_zero_iff.mp hz
      by_cases hz0 : z = 0
      · simp [hz0, hh0]
      · rw [hhne z hz0, norm_div, norm_pow]
        have hzp : 0 < ‖z‖ := norm_pos_iff.mpr hz0
        rw [div_le_iff₀ (by positivity)]
        simp only [F, norm_mul]
        calc ‖E z‖ * ‖P z‖ ≤ ‖E z‖ * (M * ‖z‖ ^ 3) := by gcongr; exact hPb z hz'.le
          _ = ‖E z‖ * M * ‖z‖ * ‖z‖ ^ 2 := by ring
    -- `h` off `0`
    have hFd : ∀ z ∈ unitDisc, z ≠ 0 →
        HasDerivAt h (((q₀ z * F z + z ^ 2 * ϕ z) * z ^ 2 - F z * (2 * z)) / (z ^ 2) ^ 2) z := by
      intro z hz hz0
      have hd := (hF z hz).div (hasDerivAt_pow 2 z) (pow_ne_zero 2 hz0)
      have hev : h =ᶠ[𝓝 z] fun w => F w / w ^ 2 := by
        filter_upwards [isOpen_ne.mem_nhds hz0] with w hw
        exact hhne w hw
      have hd' : HasDerivAt (fun w => F w / w ^ 2)
          (((q₀ z * F z + z ^ 2 * ϕ z) * z ^ 2 - F z * (2 * z)) / (z ^ 2) ^ 2) z := by
        convert hd using 1
        push_cast
        ring
      exact hd'.congr_of_eventuallyEq hev
    have hhd : DifferentiableOn ℂ h unitDisc := by
      refine (Complex.differentiableOn_compl_singleton_and_continuousAt_iff (isOpen_ball.mem_nhds h0D)).mp
        ⟨fun z hz => (hFd z hz.1 hz.2).differentiableAt.differentiableWithinAt, hcont⟩
    have hdsl : ∀ z, z ≠ 0 → dslope h 0 z = h z / z := fun z hz0 => by
      rw [dslope_of_ne h hz0, slope_def_field, hh0, sub_zero, sub_zero]
    have heq' : ∀ z ∈ unitDisc, z ≠ 0 → deriv h z - q₀ z * h z + 2 * dslope h 0 z = ϕ z := by
      intro z hz hz0
      rw [(hFd z hz hz0).deriv, hdsl z hz0, hhne z hz0]
      field_simp
      ring
    -- the equation at `0`, by continuity
    have hL : ContinuousAt (fun z => deriv h z - q₀ z * h z + 2 * dslope h 0 z) 0 := by
      have h1 : ContinuousAt (deriv h) 0 :=
        ((hhd.deriv isOpen_ball).differentiableAt (isOpen_ball.mem_nhds h0D)).continuousAt
      have h2 : ContinuousAt q₀ 0 := (hq₀.1.differentiableAt (isOpen_ball.mem_nhds h0D)).continuousAt
      have h3 : ContinuousAt (dslope h 0) 0 :=
        (((Complex.differentiableOn_dslope (isOpen_ball.mem_nhds h0D)).mpr hhd).differentiableAt
          (isOpen_ball.mem_nhds h0D)).continuousAt
      exact (h1.sub (h2.mul hcont)).add (continuousAt_const.mul h3)
    have hϕc : ContinuousAt ϕ 0 := (hϕ.1.differentiableAt (isOpen_ball.mem_nhds h0D)).continuousAt
    have hat0 : deriv h 0 - q₀ 0 * h 0 + 2 * dslope h 0 0 = ϕ 0 := by
      have t1 := hL.tendsto.mono_left (nhdsWithin_le_nhds (s := {(0 : ℂ)}ᶜ))
      have t2 : Tendsto (fun z => deriv h z - q₀ z * h z + 2 * dslope h 0 z) (𝓝[≠] 0) (𝓝 (ϕ 0)) := by
        refine (hϕc.tendsto.mono_left nhdsWithin_le_nhds).congr' ?_
        filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (isOpen_ball.mem_nhds h0D)] with z hz hzD
        exact (heq' z hzD hz).symm
      exact tendsto_nhds_unique t1 t2
    have heq : EqOn (fun z => deriv h z - q₀ z * h z + 2 * dslope h 0 z) ϕ unitDisc := by
      intro z hz
      by_cases hz0 : z = 0
      · subst hz0; exact hat0
      · exact heq' z hz hz0
    -- `h ∈ A₂¹` by the energy estimate
    obtain ⟨s₁, hs₁0, hs₁1, hs₁⟩ := boundary_small_of_weighted_tendsto_zero
      (cor_1_4 (Or.inl rfl) (a21_const_mul measurableSet_ball hq₀ 8))
    set s : ℝ := max s₁ (99 / 100) with hsdef
    have hs0 : 0 < s := lt_of_lt_of_le hs₁0 (le_max_left _ _)
    have hs1 : s < 1 := max_lt hs₁1 (by norm_num)
    refine ⟨h, a6_energy (ψ := fun z => q₀ z - 2 / z) hs0 hs1 hhd hϕ ?_ ?_, hh0, heq⟩
    · intro z hz hzs
      have hz0 : z ≠ 0 := by
        rintro rfl
        simp at hzs
        linarith
      have e := heq' z hz hz0
      rw [hdsl z hz0] at e
      rw [← e]
      field_simp
      ring
    · intro z hz hzs
      have hz1 : ‖z‖ < 1 := mem_ball_zero_iff.mp hz
      have hzs1 : s₁ < ‖z‖ := lt_of_le_of_lt (le_max_left _ _) hzs
      have hz99 : 99 / 100 < ‖z‖ := lt_of_le_of_lt (le_max_right _ _) hzs
      have hzp : 0 < ‖z‖ := by linarith
      have hw : 0 ≤ 1 - ‖z‖ ^ 2 := by nlinarith
      have hq := hs₁ z hz hzs1
      rw [norm_mul, Complex.norm_ofNat] at hq
      have hq' : (1 - ‖z‖ ^ 2) * ‖q₀ z‖ ≤ 1 / 16 := by nlinarith
      have h2 : ‖(2 : ℂ) / z‖ = 2 / ‖z‖ := by rw [norm_div, Complex.norm_ofNat]
      have htri : ‖q₀ z - 2 / z‖ ≤ ‖q₀ z‖ + 2 / ‖z‖ := by
        rw [← h2]; exact norm_sub_le _ _
      have hb : (1 - ‖z‖ ^ 2) * (2 / ‖z‖) ≤ 3 / 16 := by
        rw [mul_div_assoc', div_le_iff₀ hzp]
        nlinarith
      calc (1 - ‖z‖ ^ 2) * ‖q₀ z - 2 / z‖ ≤ (1 - ‖z‖ ^ 2) * (‖q₀ z‖ + 2 / ‖z‖) :=
            mul_le_mul_of_nonneg_left htri hw
        _ = (1 - ‖z‖ ^ 2) * ‖q₀ z‖ + (1 - ‖z‖ ^ 2) * (2 / ‖z‖) := by ring
        _ ≤ 1 / 4 := by linarith
  · intro h hd h0 heq
    let F : ℂ → ℂ := fun z => z ^ 2 * h z
    have hdsl : ∀ z, z * dslope h 0 z = h z := fun z => by
      have := sub_smul_dslope h 0 z
      simpa [h0, smul_eq_mul] using this
    have hF : ∀ z ∈ unitDisc, HasDerivAt F (2 * z * h z + z ^ 2 * deriv h z) z := by
      intro z hz
      have hh := (hd.differentiableAt (isOpen_ball.mem_nhds hz)).hasDerivAt
      have := (hasDerivAt_pow 2 z).mul hh
      convert this using 1
      push_cast
      ring
    have hFd : DifferentiableOn ℂ F unitDisc := fun z hz => (hF z hz).differentiableAt.differentiableWithinAt
    have hFeq : EqOn (fun z => deriv F z - q₀ z * F z) 0 unitDisc := by
      intro z hz
      have e : deriv h z - q₀ z * h z + 2 * dslope h 0 z = 0 := heq hz
      show deriv F z - q₀ z * F z = 0
      rw [(hF z hz).deriv]
      calc 2 * z * h z + z ^ 2 * deriv h z - q₀ z * F z
          = 2 * z * (z * dslope h 0 z) + z ^ 2 * deriv h z - q₀ z * (z ^ 2 * h z) := by rw [hdsl]
        _ = z ^ 2 * (deriv h z - q₀ z * h z + 2 * dslope h 0 z) := by ring
        _ = 0 := by rw [e, mul_zero]
    have hF0 := linearized_Psi_injective hq₀.1 hFd hFeq (by simp [F])
    intro z hz
    by_cases hz0 : z = 0
    · simp [hz0, h0]
    · have := hF0 hz
      simp only [F, Pi.zero_apply] at this ⊢
      exact (mul_eq_zero.mp this).resolve_left (pow_ne_zero 2 hz0)

theorem a6_dslope_add {f g : ℂ → ℂ} (hf : DifferentiableAt ℂ f 0) (hg : DifferentiableAt ℂ g 0) (z : ℂ) :
    dslope (fun w => f w + g w) 0 z = dslope f 0 z + dslope g 0 z := by
  by_cases hz : z = 0
  · subst hz
    rw [dslope_same, dslope_same, dslope_same]
    exact (hf.hasDerivAt.add hg.hasDerivAt).deriv
  · rw [dslope_of_ne _ hz, dslope_of_ne _ hz, dslope_of_ne _ hz, slope_def_field, slope_def_field,
      slope_def_field]
    field_simp
    ring

theorem a6_dslope_const_mul {f : ℂ → ℂ} (hf : DifferentiableAt ℂ f 0) (c z : ℂ) :
    dslope (fun w => c * f w) 0 z = c * dslope f 0 z := by
  by_cases hz : z = 0
  · subst hz
    rw [dslope_same, dslope_same, deriv_const_mul _ hf]
  · rw [dslope_of_ne _ hz, dslope_of_ne _ hz, slope_def_field, slope_def_field]
    field_simp

theorem a6_dslope_congr {f g : ℂ → ℂ} (h : EqOn f g unitDisc) : EqOn (dslope f 0) (dslope g 0) unitDisc := by
  have h0D : (0 : ℂ) ∈ unitDisc := mem_ball_self one_pos
  intro z hz
  by_cases hz0 : z = 0
  · subst hz0
    rw [dslope_same, dslope_same]
    have hev : f =ᶠ[𝓝 0] g := by
      filter_upwards [isOpen_ball.mem_nhds h0D] with w hw
      exact h hw
    exact hev.deriv_eq
  · rw [dslope_of_ne _ hz0, dslope_of_ne _ hz0, slope_def_field, slope_def_field, h hz, h h0D]

/-- The inverted `Ψ*`, `K(q) = q' - ½q² + 2q/ζ`, is injective on holomorphic `q` with `q(0) = 0`. -/
theorem a6_K_injective {q₁ q₂ : ℂ → ℂ} (h₁ : DifferentiableOn ℂ q₁ unitDisc) (h₂ : DifferentiableOn ℂ q₂ unitDisc)
    (h₁0 : q₁ 0 = 0) (h₂0 : q₂ 0 = 0)
    (hK : EqOn (fun z => deriv q₁ z - 1 / 2 * q₁ z ^ 2 + 2 * dslope q₁ 0 z)
      (fun z => deriv q₂ z - 1 / 2 * q₂ z ^ 2 + 2 * dslope q₂ 0 z) unitDisc) :
    EqOn q₁ q₂ unitDisc := by
  have heq : ∀ z ∈ unitDisc \ {0}, PsiOp q₁ z + 2 * q₁ z / z = PsiOp q₂ z + 2 * q₂ z / z := by
    intro z hz
    have e := hK hz.1
    have hz0 : z ≠ 0 := hz.2
    simp only [dslope_of_ne _ hz0, slope_def_field, h₁0, h₂0, sub_zero] at e
    simp only [PsiOp]
    linear_combination e
  obtain ⟨hode, hF0⟩ := inverted_Psi_difference_linear_ode h₁ h₂ heq
  have hFd : DifferentiableOn ℂ (fun z => z ^ 2 * (q₁ z - q₂ z)) unitDisc :=
    (differentiableOn_id.pow 2).mul (h₁.sub h₂)
  have hF := linearized_Psi_injective ((h₁.add h₂).div_const 2) hFd hode hF0
  intro z hz
  by_cases hz0 : z = 0
  · subst hz0; rw [h₁0, h₂0]
  · have := hF hz
    simp only [Pi.zero_apply] at this
    exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left (pow_ne_zero 2 hz0))

/-! #### The primitive `R(a) = ∫₀^ζ a` with value `0` -/

theorem a6_R_hasDerivAt (a : A2 unitDisc) {z : ℂ} (hz : z ∈ unitDisc) :
    HasDerivAt (fun z : ℂ => ∫ t in (0 : ℝ)..1, A2.toFun a ((t : ℂ) * z) * z) (A2.toFun a z) z :=
  disk_segment_integral_hasDerivAt (A2.toFun_spec a).1 hz

theorem a6_R_diff (a : A2 unitDisc) :
    DifferentiableOn ℂ (fun z : ℂ => ∫ t in (0 : ℝ)..1, A2.toFun a ((t : ℂ) * z) * z) unitDisc :=
  fun _ hz => (a6_R_hasDerivAt a hz).differentiableAt.differentiableWithinAt

theorem a6_R_deriv (a : A2 unitDisc) :
    EqOn (deriv fun z : ℂ => ∫ t in (0 : ℝ)..1, A2.toFun a ((t : ℂ) * z) * z) (A2.toFun a) unitDisc :=
  fun _ hz => (a6_R_hasDerivAt a hz).deriv

theorem a6_R_zero (a : A2 unitDisc) :
    (fun z : ℂ => ∫ t in (0 : ℝ)..1, A2.toFun a ((t : ℂ) * z) * z) 0 = 0 := by
  simp

theorem a6_R_mem (a : A2 unitDisc) :
    (fun z : ℂ => ∫ t in (0 : ℝ)..1, A2.toFun a ((t : ℂ) * z) * z) ∈ A21fun unitDisc :=
  disk_segment_integral_A21 (A2.toFun_mem a)

theorem a6_R_normReal (a : A2 unitDisc) :
    (normA21 unitDisc (fun z : ℂ => ∫ t in (0 : ℝ)..1, A2.toFun a ((t : ℂ) * z) * z)).toReal ≤ 3 * ‖a‖ := by
  have hS := disk_segment_integral_norm_bound (A2.toFun_mem a)
  rw [A2.norm_toFun] at hS
  have h8 : Real.sqrt 8 ≤ 3 := by
    rw [Real.sqrt_le_left (by norm_num)]; norm_num
  apply ENNReal.toReal_le_of_le_ofReal (by positivity)
  refine hS.trans ?_
  rw [show ((‖a‖₊ : ℝ≥0) : ℝ≥0∞) = ENNReal.ofReal ‖a‖ from (ofReal_norm a).symm.trans rfl,
    ← ENNReal.ofReal_mul (Real.sqrt_nonneg _)]
  exact ENNReal.ofReal_le_ofReal (by nlinarith [norm_nonneg a])

theorem a6_R_lin (a b : A2 unitDisc) (c d : ℂ) :
    EqOn (fun z : ℂ => ∫ t in (0 : ℝ)..1, A2.toFun (c • a + d • b) ((t : ℂ) * z) * z)
      (fun z => c * (∫ t in (0 : ℝ)..1, A2.toFun a ((t : ℂ) * z) * z) +
        d * (∫ t in (0 : ℝ)..1, A2.toFun b ((t : ℂ) * z) * z)) unitDisc := by
  apply a4_eqOn_of_deriv (a6_R_diff _) (((a6_R_diff a).const_mul c).add ((a6_R_diff b).const_mul d))
  · intro z hz
    have hd := ((a6_R_hasDerivAt a hz).const_mul c).add ((a6_R_hasDerivAt b hz).const_mul d)
    rw [a6_R_deriv _ hz, hd.deriv, A2.toFun_add (D := unitDisc) isOpen_ball a4_circle _ _ hz, Pi.add_apply,
      A2.toFun_smul (D := unitDisc) isOpen_ball a4_circle _ _ hz,
      A2.toFun_smul (D := unitDisc) isOpen_ball a4_circle _ _ hz, Pi.smul_apply, Pi.smul_apply,
      smul_eq_mul, smul_eq_mul]
  · simp

theorem a6_R_norm (a : A2 unitDisc) :
    normA21 unitDisc (fun z : ℂ => ∫ t in (0 : ℝ)..1, A2.toFun a ((t : ℂ) * z) * z) ≤ ENNReal.ofReal (3 * ‖a‖) :=
  (ENNReal.le_ofReal_iff_toReal_le (a6_R_mem a).2.ne (by positivity)).mpr (a6_R_normReal a)

/-- The inverse function theorem for the inverted `Ψ*`, `K(q) = q' - ½q² + 2q/ζ`, on `{q ∈ A₂¹(𝔻) | q(0) = 0}`. -/
theorem a6_disk_inverse {q₀ : ℂ → ℂ} (hq₀ : q₀ ∈ A21fun unitDisc) (hq₀0 : q₀ 0 = 0) {q : ℕ → ℂ → ℂ}
    (hq : ∀ n, q n ∈ A21fun unitDisc) (hq0 : ∀ n, q n 0 = 0)
    (hK : Tendsto (fun n => normA2 unitDisc (fun z =>
      (deriv (q n) z - 1 / 2 * q n z ^ 2 + 2 * dslope (q n) 0 z) -
        (deriv q₀ z - 1 / 2 * q₀ z ^ 2 + 2 * dslope q₀ 0 z))) atTop (𝓝 0)) :
    Tendsto (fun n => normA21 unitDisc (fun z => q n z - q₀ z)) atTop (𝓝 0) := by
  have h0D : (0 : ℂ) ∈ unitDisc := mem_ball_self one_pos
  set R : A2 unitDisc → ℂ → ℂ := fun a z => ∫ t in (0 : ℝ)..1, A2.toFun a ((t : ℂ) * z) * z with hRdef
  have hRmem : ∀ a, R a ∈ A21fun unitDisc := a6_R_mem
  have hR0 : ∀ a, R a 0 = 0 := a6_R_zero
  have hRd0 : ∀ a, DifferentiableAt ℂ (R a) 0 := fun a => (a6_R_hasDerivAt a h0D).differentiableAt
  have hadd : ∀ a b, EqOn (R (a + b)) (fun z => R a z + R b z) unitDisc := by
    intro a b z hz
    have := a6_R_lin a b 1 1 hz
    simp only [one_smul, one_mul] at this
    exact this
  have hsmul : ∀ (c : ℂ) a, EqOn (R (c • a)) (fun z => c * R a z) unitDisc := by
    intro c a z hz
    have := a6_R_lin a 0 c 0 hz
    simp only [zero_smul, add_zero, zero_mul] at this
    exact this
  have hPR : ∀ a, (fun z => q₀ z * R a z) ∈ A2fun unitDisc := fun a => a4_A2_mul hq₀ (hRmem a)
  have hDR : ∀ a, dslope (R a) 0 ∈ A2fun unitDisc := fun a => (a6_dslope_A2 (hRmem a) (hR0 a)).1
  have hRR : ∀ a, (fun z => (1 / 2 : ℂ) * (R a z * R a z)) ∈ A2fun unitDisc :=
    fun a => a4_A2_const_mul (a4_A2_mul (hRmem a) (hRmem a)) (1 / 2)
  have hLmem : ∀ a, (fun z => A2.toFun a z - q₀ z * R a z + 2 * dslope (R a) 0 z) ∈ A2fun unitDisc :=
    fun a => a4_A2_add (a4_A2_sub (A2.toFun_mem a) (hPR a)) (a4_A2_const_mul (hDR a) 2)
  obtain ⟨C, hC0, hC⟩ := a4_mul_le
  set NP := (normA21 unitDisc q₀).toReal with hNP
  have hNP0 : 0 ≤ NP := ENNReal.toReal_nonneg
  -- the linear part
  let ℓ : A2 unitDisc →ₗ[ℂ] A2 unitDisc :=
    { toFun := fun a => a - toA2 unitDisc (fun z => q₀ z * R a z) + (2 : ℂ) • toA2 unitDisc (dslope (R a) 0)
      map_add' := by
        intro a b
        have e1 : toA2 unitDisc (fun z => q₀ z * R (a + b) z) =
            toA2 unitDisc (fun z => q₀ z * R a z) + toA2 unitDisc (fun z => q₀ z * R b z) := by
          rw [← a4_toA2_add (hPR a) (hPR b)]
          apply a4_toA2_congr (hPR _)
          intro z hz
          show q₀ z * R (a + b) z = q₀ z * R a z + q₀ z * R b z
          rw [show R (a + b) z = R a z + R b z from hadd a b hz]
          ring
        have e2 : toA2 unitDisc (dslope (R (a + b)) 0) =
            toA2 unitDisc (dslope (R a) 0) + toA2 unitDisc (dslope (R b) 0) := by
          rw [← a4_toA2_add (hDR a) (hDR b)]
          apply a4_toA2_congr (hDR _)
          intro z hz
          rw [a6_dslope_congr (hadd a b) hz]
          exact a6_dslope_add (hRd0 a) (hRd0 b) z
        show (a + b) - toA2 unitDisc (fun z => q₀ z * R (a + b) z) + (2 : ℂ) • toA2 unitDisc (dslope (R (a + b)) 0) =
          (a - toA2 unitDisc (fun z => q₀ z * R a z) + (2 : ℂ) • toA2 unitDisc (dslope (R a) 0)) +
            (b - toA2 unitDisc (fun z => q₀ z * R b z) + (2 : ℂ) • toA2 unitDisc (dslope (R b) 0))
        rw [e1, e2, smul_add]
        abel
      map_smul' := by
        intro c a
        have e1 : toA2 unitDisc (fun z => q₀ z * R (c • a) z) = c • toA2 unitDisc (fun z => q₀ z * R a z) := by
          rw [← a4_toA2_smul (hPR a) c]
          apply a4_toA2_congr (hPR _)
          intro z hz
          show q₀ z * R (c • a) z = c * (q₀ z * R a z)
          rw [show R (c • a) z = c * R a z from hsmul c a hz]
          ring
        have e2 : toA2 unitDisc (dslope (R (c • a)) 0) = c • toA2 unitDisc (dslope (R a) 0) := by
          rw [← a4_toA2_smul (hDR a) c]
          apply a4_toA2_congr (hDR _)
          intro z hz
          rw [a6_dslope_congr (hsmul c a) hz]
          exact a6_dslope_const_mul (hRd0 a) c z
        show c • a - toA2 unitDisc (fun z => q₀ z * R (c • a) z) + (2 : ℂ) • toA2 unitDisc (dslope (R (c • a)) 0) =
          c • (a - toA2 unitDisc (fun z => q₀ z * R a z) + (2 : ℂ) • toA2 unitDisc (dslope (R a) 0))
        rw [e1, e2, smul_add, smul_sub, smul_comm (2 : ℂ) c] }
  have hℓfun : ∀ a, ℓ a = toA2 unitDisc (fun z => A2.toFun a z - q₀ z * R a z + 2 * dslope (R a) 0 z) := by
    intro a
    apply A2.ext_of_toFun_eqOn (D := unitDisc) measurableSet_ball
    intro z hz
    rw [a4_toA2_eqOn (hLmem a) hz]
    show A2.toFun (a - toA2 unitDisc (fun z => q₀ z * R a z) + (2 : ℂ) • toA2 unitDisc (dslope (R a) 0)) z = _
    rw [A2.toFun_add (D := unitDisc) isOpen_ball a4_circle _ _ hz, Pi.add_apply,
      A2.toFun_sub (D := unitDisc) isOpen_ball a4_circle _ _ hz, Pi.sub_apply,
      A2.toFun_smul (D := unitDisc) isOpen_ball a4_circle _ _ hz, Pi.smul_apply, smul_eq_mul,
      a4_toA2_eqOn (hPR a) hz, a4_toA2_eqOn (hDR a) hz]
  have hDb : ∀ a, ‖toA2 unitDisc (dslope (R a) 0)‖ ≤ 3 * ‖a‖ := by
    intro a
    have e : ‖toA2 unitDisc (dslope (R a) 0)‖ = (normA2 unitDisc (dslope (R a) 0)).toReal := by
      rw [← a4_toA2_norm (hDR a)]; rfl
    rw [e]
    exact (ENNReal.toReal_mono (hRmem a).2.ne (a6_dslope_A2 (hRmem a) (hR0 a)).2).trans (a6_R_normReal a)
  have hℓb : ∀ a, ‖ℓ a‖ ≤ (7 + 3 * C * NP) * ‖a‖ := by
    intro a
    have h1 : ‖toA2 unitDisc (fun z => q₀ z * R a z)‖ ≤ 3 * C * NP * ‖a‖ := by
      refine (hC q₀ hq₀ (R a) (hRmem a)).trans ?_
      calc C * NP * (normA21 unitDisc (R a)).toReal ≤ C * NP * (3 * ‖a‖) := by
            gcongr; exact a6_R_normReal a
        _ = 3 * C * NP * ‖a‖ := by ring
    have h2 := hDb a
    show ‖a - toA2 unitDisc (fun z => q₀ z * R a z) + (2 : ℂ) • toA2 unitDisc (dslope (R a) 0)‖ ≤ _
    calc _ ≤ ‖a - toA2 unitDisc (fun z => q₀ z * R a z)‖ + ‖(2 : ℂ) • toA2 unitDisc (dslope (R a) 0)‖ :=
          norm_add_le _ _
      _ ≤ (‖a‖ + ‖toA2 unitDisc (fun z => q₀ z * R a z)‖) + 2 * ‖toA2 unitDisc (dslope (R a) 0)‖ := by
          rw [norm_smul, Complex.norm_ofNat]
          gcongr
          exact norm_sub_le _ _
      _ ≤ _ := by nlinarith [norm_nonneg a]
  let ℓc : A2 unitDisc →L[ℂ] A2 unitDisc := LinearMap.mkContinuous ℓ (7 + 3 * C * NP) hℓb
  -- the nonlinear map
  let N : A2 unitDisc → A2 unitDisc := fun a => toA2 unitDisc (fun z => (1 / 2 : ℂ) * (R a z * R a z))
  let G : A2 unitDisc → A2 unitDisc := fun a => ℓc a - N a
  have hNdiff : ∀ a b, ‖N a - N b‖ ≤ 5 * C * ‖a - b‖ * (‖a‖ + ‖b‖) := by
    intro a b
    have hsub : EqOn (R (a - b)) (fun z => R a z - R b z) unitDisc := by
      intro z hz
      have e : a - b = (1 : ℂ) • a + (-1 : ℂ) • b := by rw [one_smul, neg_one_smul ℂ b, ← sub_eq_add_neg]
      have := a6_R_lin a b 1 (-1) hz
      simp only at this
      show R (a - b) z = R a z - R b z
      rw [e]
      refine this.trans ?_
      ring
    have he : N a - N b = (1 / 2 : ℂ) • toA2 unitDisc (fun z => R (a - b) z * R (a + b) z) := by
      rw [← a4_toA2_sub (hRR a) (hRR b), ← a4_toA2_smul (a4_A2_mul (hRmem _) (hRmem _))]
      apply a4_toA2_congr (a4_A2_sub (hRR a) (hRR b))
      intro z hz
      show (1 / 2 : ℂ) * (R a z * R a z) - (1 / 2 : ℂ) * (R b z * R b z) =
        (1 / 2 : ℂ) * (R (a - b) z * R (a + b) z)
      rw [hsub hz, show R (a + b) z = R a z + R b z from hadd a b hz]
      ring
    rw [he, norm_smul]
    have hb := hC _ (hRmem (a - b)) _ (hRmem (a + b))
    have h1 := a6_R_normReal (a - b)
    have h2 := a6_R_normReal (a + b)
    have h3 : ‖a + b‖ ≤ ‖a‖ + ‖b‖ := norm_add_le a b
    have hn : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by norm_num
    rw [hn]
    have h4 : C * (normA21 unitDisc (R (a - b))).toReal * (normA21 unitDisc (R (a + b))).toReal ≤
        C * (3 * ‖a - b‖) * (3 * (‖a‖ + ‖b‖)) :=
      mul_le_mul (mul_le_mul_of_nonneg_left h1 hC0) (by linarith) ENNReal.toReal_nonneg (by positivity)
    nlinarith [norm_nonneg (toA2 unitDisc (fun z => R (a - b) z * R (a + b) z)),
      mul_nonneg (mul_nonneg hC0 (norm_nonneg (a - b))) (add_nonneg (norm_nonneg a) (norm_nonneg b))]
  have hG : HasStrictFDerivAt G ℓc 0 := by
    rw [hasStrictFDerivAt_iff_isLittleO]
    refine Asymptotics.isLittleO_iff.2 fun c hc => ?_
    have hδ : 0 < c / (10 * C + 1) := by positivity
    filter_upwards [Metric.ball_mem_nhds ((0 : A2 unitDisc), (0 : A2 unitDisc)) hδ] with p hp
    have hp' : ‖p‖ < c / (10 * C + 1) := by
      rw [Metric.mem_ball, Prod.mk_zero_zero, dist_zero_right] at hp
      exact hp
    have hp1 : ‖p.1‖ ≤ ‖p‖ := norm_fst_le p
    have hp2 : ‖p.2‖ ≤ ‖p‖ := norm_snd_le p
    have he : G p.1 - G p.2 - ℓc (p.1 - p.2) = N p.2 - N p.1 := by
      simp only [G, map_sub]
      abel
    rw [he]
    have hN := hNdiff p.2 p.1
    rw [norm_sub_rev p.2 p.1] at hN
    have hsum : ‖p.2‖ + ‖p.1‖ ≤ 2 * ‖p‖ := by linarith
    have hpc : (10 * C + 1) * ‖p‖ ≤ c := by
      rw [lt_div_iff₀ (by positivity)] at hp'
      linarith
    calc ‖N p.2 - N p.1‖ ≤ 5 * C * ‖p.1 - p.2‖ * (‖p.2‖ + ‖p.1‖) := hN
      _ ≤ 5 * C * ‖p.1 - p.2‖ * (2 * ‖p‖) := by gcongr
      _ = ‖p.1 - p.2‖ * (10 * C * ‖p‖) := by ring
      _ ≤ ‖p.1 - p.2‖ * c := by
          gcongr
          nlinarith [norm_nonneg p]
      _ = c * ‖p.1 - p.2‖ := by ring
  -- bijectivity (`a6_linear_bij`)
  obtain ⟨hsolve, huniq⟩ := a6_linear_bij hq₀
  have hinj : ∀ a, ℓc a = 0 → a = 0 := by
    intro a ha
    have ha' : ℓ a = 0 := ha
    rw [hℓfun a] at ha'
    have hzero : toA2 unitDisc (fun z => A2.toFun a z - q₀ z * R a z + 2 * dslope (R a) 0 z) =
        toA2 unitDisc (fun _ => (0 : ℂ)) := by
      rw [ha']
      exact (t31_toA2_zero (fun z _ => rfl)).symm
    have hE := (a4_toA2_ext (hLmem a) ⟨differentiableOn_const 0, by simp [normA2]⟩).mp hzero
    have heq : EqOn (fun z => deriv (R a) z - q₀ z * R a z + 2 * dslope (R a) 0 z) 0 unitDisc := by
      intro z hz
      have := hE hz
      simp only at this
      show deriv (R a) z - q₀ z * R a z + 2 * dslope (R a) 0 z = 0
      rw [a6_R_deriv a hz]
      exact this
    have hRz := huniq (R a) (hRmem a).1 (hR0 a) heq
    apply A2.ext_of_toFun_eqOn (D := unitDisc) measurableSet_ball
    intro z hz
    rw [a4_toFun_zero hz, ← a6_R_deriv a hz]
    have hev : R a =ᶠ[𝓝 z] fun _ => 0 := by
      filter_upwards [isOpen_ball.mem_nhds hz] with w hw
      exact hRz hw
    rw [hev.deriv_eq, deriv_const]
    rfl
  have hsurj : ∀ b, ∃ a, ℓc a = b := by
    intro b
    obtain ⟨h, hh, hh0, hheq⟩ := hsolve (A2.toFun b) (A2.toFun_mem b)
    have hDh := (a6_dslope_A2 hh hh0).1
    have hh' : deriv h ∈ A2fun unitDisc := by
      refine a4_A2_congr (a4_A2_sub (a4_A2_add (A2.toFun_mem b) (a4_A2_mul hq₀ hh)) (a4_A2_const_mul hDh 2)) ?_
      intro z hz
      have e := hheq hz
      simp only at e
      show A2.toFun b z + q₀ z * h z - 2 * dslope h 0 z = deriv h z
      rw [← e]
      ring
    refine ⟨toA2 unitDisc (deriv h), ?_⟩
    set a := toA2 unitDisc (deriv h) with hadef
    have hRa : EqOn (R a) h unitDisc :=
      a4_eqOn_of_deriv (a6_R_diff a) hh.1 (fun z hz => by rw [a6_R_deriv a hz]; exact a4_toA2_eqOn hh' hz)
        ((hR0 a).trans hh0.symm)
    show ℓ a = b
    rw [hℓfun a]
    have hcong : EqOn (fun z => A2.toFun a z - q₀ z * R a z + 2 * dslope (R a) 0 z) (A2.toFun b) unitDisc := by
      intro z hz
      show A2.toFun a z - q₀ z * R a z + 2 * dslope (R a) 0 z = A2.toFun b z
      rw [a4_toA2_eqOn hh' hz, hRa hz, a6_dslope_congr hRa hz]
      exact hheq hz
    rw [a4_toA2_congr (hLmem a) hcong]
    exact toA2_toFun (D := unitDisc) isOpen_ball a4_circle b
  have hker := (LinearMap.ker_eq_bot' (f := (ℓc : A2 unitDisc →ₗ[ℂ] A2 unitDisc))).mpr hinj
  have hran := (LinearMap.range_eq_top (f := (ℓc : A2 unitDisc →ₗ[ℂ] A2 unitDisc))).mpr hsurj
  let e := ContinuousLinearEquiv.ofBijective ℓc hker hran
  have hG' : HasStrictFDerivAt G (e : A2 unitDisc →L[ℂ] A2 unitDisc) 0 := by
    rw [ContinuousLinearEquiv.coe_ofBijective]
    exact hG
  have hG0 : G 0 = 0 := by
    have hN0 : N 0 = 0 := by
      apply t31_toA2_zero
      intro z hz
      show (1 / 2 : ℂ) * (R 0 z * R 0 z) = 0
      rw [show R 0 z = 0 by simpa using hsmul 0 0 hz]
      ring
    show ℓc 0 - N 0 = 0
    rw [map_zero, hN0, sub_zero]
  -- the data
  set Kf : (ℂ → ℂ) → ℂ → ℂ := fun g z => deriv g z - 1 / 2 * g z ^ 2 + 2 * dslope g 0 z with hKf
  have hKd : ∀ g ∈ A21fun unitDisc, DifferentiableOn ℂ (Kf g) unitDisc := fun g hg =>
    ((hg.1.deriv isOpen_ball).sub ((hg.1.pow 2).const_mul _)).add
      (((Complex.differentiableOn_dslope (isOpen_ball.mem_nhds h0D)).mpr hg.1).const_mul 2)
  have hΔ : ∀ᶠ n in atTop, (fun z => Kf (q n) z - Kf q₀ z) ∈ A2fun unitDisc := by
    filter_upwards [(tendsto_order.1 hK).2 ⊤ ENNReal.zero_lt_top] with n hn
    exact ⟨(hKd _ (hq n)).sub (hKd _ hq₀), hn⟩
  let y : ℕ → A2 unitDisc := fun n => toA2 unitDisc (fun z => Kf (q n) z - Kf q₀ z)
  have hy : Tendsto y atTop (𝓝 (G 0)) := by
    rw [hG0, tendsto_zero_iff_norm_tendsto_zero]
    have ht := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hK
    rw [ENNReal.toReal_zero] at ht
    refine ht.congr' ?_
    filter_upwards [hΔ] with n hn
    show (normA2 unitDisc _).toReal = ‖toA2 unitDisc _‖
    rw [← a4_toA2_norm hn]
    rfl
  set Linv := hG'.localInverse G e 0 with hLinv
  have hxt : Tendsto (fun n => Linv (y n)) atTop (𝓝 0) := by
    have h := hG'.localInverse_continuousAt.tendsto.comp hy
    rwa [hG'.localInverse_apply_image] at h
  have hev : ∀ᶠ n in atTop, G (Linv (y n)) = y n := hy.eventually hG'.eventually_right_inverse
  have hup : Tendsto (fun n => ENNReal.ofReal (3 * ‖Linv (y n)‖)) atTop (𝓝 0) := by
    have := ENNReal.tendsto_ofReal ((hxt.norm).const_mul 3)
    simpa using this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup
    (Eventually.of_forall fun _ => bot_le) ?_
  filter_upwards [hev, hΔ] with n hn hΔn
  set a := Linv (y n) with hadef
  have e1 : ℓ a - N a = toA2 unitDisc (fun z => Kf (q n) z - Kf q₀ z) := hn
  rw [hℓfun a, ← a4_toA2_sub (hLmem a) (hRR a)] at e1
  have hE := (a4_toA2_ext (a4_A2_sub (hLmem a) (hRR a)) hΔn).mp e1
  have hKeq : EqOn (Kf (fun z => q₀ z + R a z)) (Kf (q n)) unitDisc := by
    intro z hz
    have h := hE hz
    simp only [hKf] at h ⊢
    have hd : HasDerivAt (fun w => q₀ w + R a w) (deriv q₀ z + A2.toFun a z) z :=
      (hq₀.1.differentiableAt (isOpen_ball.mem_nhds hz)).hasDerivAt.add (a6_R_hasDerivAt a hz)
    rw [hd.deriv, a6_dslope_add (hq₀.1.differentiableAt (isOpen_ball.mem_nhds h0D)) (hRd0 a) z]
    linear_combination h
  have hEq := a6_K_injective (hq₀.1.add (hRmem a).1) (hq n).1 (by simp [hq₀0, hR0 a]) (hq0 n) hKeq
  rw [a4_normA21_congr (g := R a) (fun z hz => by
    show q n z - q₀ z = R a z
    rw [← hEq hz, Pi.add_apply]
    ring)]
  exact a6_R_norm a

/-- The reflection `f ↦ (y ↦ \overline{f(\bar y)})` preserves the `A₂(𝔻)` norm. -/
theorem a6_conj_normA2 (f : ℂ → ℂ) : normA2 unitDisc (fun y => conj (f (conj y))) = normA2 unitDisc f := by
  unfold normA2
  congr 1
  have hemb : MeasurableEmbedding (⇑Complex.conjLIE) := Complex.conjLIE.toHomeomorph.measurableEmbedding
  have hpre : (⇑Complex.conjLIE) ⁻¹' unitDisc = unitDisc := by
    ext w
    simp [unitDisc]
  have h := (Complex.conjLIE.measurePreserving).setLIntegral_comp_preimage_emb hemb
    (fun w => (‖f w‖₊ : ℝ≥0∞) ^ 2 * ENNReal.ofReal (rho w)⁻¹) unitDisc
  rw [hpre] at h
  rw [← h]
  refine lintegral_congr (fun w => ?_)
  simp [rho]

/-- **T2 (inverse function theorem for `Ψ*` on `Ã₂¹(𝔻*)`).** `A₂(𝔻*)` convergence of `Ψ*(ψₙ)` forces `A₂¹(𝔻*)`
convergence of `ψₙ` within `Ã₂¹(𝔻*)`. -/
theorem a6_ext_inverse {ψ₀ : ℂ → ℂ} (h₀ : ψ₀ ∈ A21tildeExt) {ψ : ℕ → ℂ → ℂ} (hψ : ∀ n, ψ n ∈ A21tildeExt)
    (hS : Tendsto (fun n => normA2 unitDiscExterior (fun z => PsiOp (ψ n) z - PsiOp ψ₀ z)) atTop (𝓝 0)) :
    Tendsto (fun n => normA21 unitDiscExterior (fun z => ψ n z - ψ₀ z)) atTop (𝓝 0) := by
  obtain ⟨q₀, hq₀, hq₀0, hq₀e, hq₀P⟩ := A21tildeExt.inverted_extension h₀
  choose q hq hq0 hqe hqP using fun n => A21tildeExt.inverted_extension (hψ n)
  have hA : ∀ n, normA21 unitDisc (fun z => q n z - q₀ z) =
      normA21 unitDiscExterior (fun z => ψ n z - ψ₀ z) := by
    intro n
    apply a55_inv_normA21
    intro z hz
    show q n z - q₀ z = -(ψ n z⁻¹ - ψ₀ z⁻¹) / z ^ 2
    rw [hqe n hz, hq₀e hz]
    ring
  have hKval : ∀ g : ℂ → ℂ, g 0 = 0 → ∀ z ∈ unitDisc \ {0},
      deriv g z - 1 / 2 * g z ^ 2 + 2 * dslope g 0 z = PsiOp g z + 2 * g z / z := by
    intro g hg0 z hz
    rw [dslope_of_ne _ hz.2, slope_def_field, hg0, sub_zero, sub_zero]
    simp only [PsiOp]
    ring
  have hKS : ∀ n, normA2 unitDisc (fun z =>
      (deriv (q n) z - 1 / 2 * q n z ^ 2 + 2 * dslope (q n) 0 z) -
        (deriv q₀ z - 1 / 2 * q₀ z ^ 2 + 2 * dslope q₀ 0 z)) =
      normA2 unitDiscExterior (fun z => PsiOp (ψ n) z - PsiOp ψ₀ z) := by
    intro n
    have e1 := a55_refl_norm
      (K₁ := fun z => deriv (q n) z - 1 / 2 * q n z ^ 2 + 2 * dslope (q n) 0 z)
      (K₂ := fun z => deriv q₀ z - 1 / 2 * q₀ z ^ 2 + 2 * dslope q₀ 0 z)
      (S₁ := PsiOp (ψ n)) (S₂ := PsiOp ψ₀)
      (fun s hs => by rw [hKval _ (hq0 n) s hs, hqP n s hs])
      (fun s hs => by rw [hKval _ hq₀0 s hs, hq₀P s hs])
    rw [← e1, ← a6_conj_normA2]
    congr 1
    funext y
    simp only [map_sub]
  have h := a6_disk_inverse hq₀ hq₀0 hq hq0 (hS.congr fun n => (hKS n).symm)
  exact h.congr hA

/-! ### T1 support: a Radon–Riesz lemma on `A₂(𝔻*)` -/

theorem a6_ext_open : IsOpen unitDiscExterior := isOpen_lt continuous_const continuous_norm

theorem a6_sq_eq {D : Set ℂ} (hD : IsOpen D) {f : ℂ → ℂ} (hf : f ∈ A2fun D) :
    normA2 D f ^ 2 = ENNReal.ofReal (∫ z in D, ‖f z‖ ^ 2 * (rho z)⁻¹) := by
  rw [a55_normA2_sq, ofReal_integral_eq_lintegral_ofReal (A2fun.integrable_weighted_sq hD hf)
    (Eventually.of_forall fun z => by simp only [rho]; positivity)]
  refine setLIntegral_congr_fun hD.measurableSet fun z _ => ?_
  rw [ENNReal.ofReal_mul (sq_nonneg _), a55_ofReal_sq]

theorem a6_tendsto_of_sq {a : ℕ → ℝ≥0∞} (h : Tendsto (fun n => a n ^ 2) atTop (𝓝 0)) :
    Tendsto a atTop (𝓝 0) := by
  refine tendsto_order.2 ⟨fun b hb => absurd hb not_lt_zero, fun b hb => ?_⟩
  filter_upwards [(tendsto_order.1 h).2 (b ^ 2) (ENNReal.pow_pos hb 2)] with n hn
  by_contra hc
  exact absurd hn (not_lt.mpr (pow_le_pow_left₀ bot_le (not_lt.mp hc) 2))

theorem a6_A2_sub_ext {f g : ℂ → ℂ} (hf : f ∈ A2fun unitDiscExterior) (hg : g ∈ A2fun unitDiscExterior) :
    (fun z => f z - g z) ∈ A2fun unitDiscExterior := by
  have hm : ∀ {u : ℂ → ℂ}, u ∈ A2fun unitDiscExterior →
      AEStronglyMeasurable u (volume.restrict unitDiscExterior) :=
    fun hu => hu.1.continuousOn.aestronglyMeasurable a6_ext_open.measurableSet
  have h1 := a55_normA2_add_le (hm hf) ((hm hg).const_mul (-1))
  refine ⟨hf.1.sub hg.1, ?_⟩
  have he : (fun z => f z - g z) = fun z => f z + -1 * g z := funext fun z => by ring
  rw [he]
  refine h1.trans_lt (ENNReal.add_lt_top.2 ⟨hf.2, ?_⟩)
  rw [normA2_const_mul]
  exact ENNReal.mul_lt_top ENNReal.coe_lt_top hg.2

/-- **Radon–Riesz on `A₂(𝔻*)`.** Locally uniform convergence together with convergence of the norms gives norm
convergence. -/
theorem a6_RR {f : ℕ → ℂ → ℂ} {g : ℂ → ℂ} (hf : ∀ n, f n ∈ A2fun unitDiscExterior)
    (hg : g ∈ A2fun unitDiscExterior) (hloc : TendstoLocallyUniformlyOn f g atTop unitDiscExterior)
    (hnorm : Tendsto (fun n => normA2 unitDiscExterior (f n)) atTop (𝓝 (normA2 unitDiscExterior g))) :
    Tendsto (fun n => normA2 unitDiscExterior (fun z => f n z - g z)) atTop (𝓝 0) := by
  set E := unitDiscExterior with hEdef
  have hE : IsOpen E := a6_ext_open
  have hEm : MeasurableSet E := hE.measurableSet
  set W : ℂ → ℝ := fun z => (rho z)⁻¹ with hWdef
  have hW0 : ∀ z, 0 ≤ W z := fun z => by simp only [W, rho]; positivity
  have hWc : Continuous W := by simp only [W, rho, inv_div]; fun_prop
  set I : (ℂ → ℂ) → ℝ := fun h => ∫ z in E, ‖h z‖ ^ 2 * W z with hIdef
  have hfg : ∀ n, (fun z => f n z - g z) ∈ A2fun E := fun n => a6_A2_sub_ext (hf n) hg
  have hint : ∀ h ∈ A2fun E, IntegrableOn (fun z => ‖h z‖ ^ 2 * W z) E :=
    fun h hh => A2fun.integrable_weighted_sq hE hh
  have hI0 : ∀ h, 0 ≤ I h := fun h => setIntegral_nonneg hEm fun z _ => mul_nonneg (sq_nonneg _) (hW0 z)
  have hIn : Tendsto (fun n => I (f n)) atTop (𝓝 (I g)) := by
    have h2 := ((ENNReal.continuous_pow 2).tendsto _).comp hnorm
    have hfin : normA2 E g ^ 2 ≠ ⊤ := ENNReal.pow_ne_top hg.2.ne
    have h3 := (ENNReal.tendsto_toReal hfin).comp h2
    rw [a6_sq_eq hE hg, ENNReal.toReal_ofReal (hI0 g)] at h3
    refine h3.congr fun n => ?_
    show (normA2 E (f n) ^ 2).toReal = I (f n)
    rw [a6_sq_eq hE (hf n), ENNReal.toReal_ofReal (hI0 _)]
  suffices hmain : Tendsto (fun n => I (fun z => f n z - g z)) atTop (𝓝 0) by
    apply a6_tendsto_of_sq
    have := ENNReal.tendsto_ofReal hmain
    rw [ENNReal.ofReal_zero] at this
    exact this.congr fun n => (a6_sq_eq hE (hfg n)).symm
  -- compact annuli exhausting `𝔻*`
  let A : ℕ → Set ℂ := fun k => {z | 1 + 1 / ((k : ℝ) + 1) ≤ ‖z‖ ∧ ‖z‖ ≤ (k : ℝ) + 2}
  have hAm : ∀ k, MeasurableSet (A k) := fun k =>
    (measurableSet_le measurable_const measurable_norm).inter (measurableSet_le measurable_norm measurable_const)
  have hAsub : ∀ k, A k ⊆ E := by
    intro k z hz
    show 1 < ‖z‖
    have : 0 < 1 / ((k : ℝ) + 1) := by positivity
    linarith [hz.1]
  have hAc : ∀ k, IsCompact (A k) := by
    intro k
    refine (isCompact_closedBall (0 : ℂ) ((k : ℝ) + 2)).of_isClosed_subset ?_ ?_
    · exact (isClosed_le continuous_const continuous_norm).inter (isClosed_le continuous_norm continuous_const)
    · intro z hz
      exact mem_closedBall_zero_iff.mpr hz.2
  have hanti : Antitone fun k => E \ A k := by
    intro i j hij z hz
    refine ⟨hz.1, fun hA => hz.2 ⟨?_, ?_⟩⟩
    · have hij' : (i : ℝ) ≤ j := by exact_mod_cast hij
      have : 1 / ((j : ℝ) + 1) ≤ 1 / ((i : ℝ) + 1) :=
        one_div_le_one_div_of_le (by positivity) (by linarith)
      linarith [hA.1]
    · have hij' : (i : ℝ) ≤ j := by exact_mod_cast hij
      linarith [hA.2]
  have hinter : (⋂ k, E \ A k) = ∅ := by
    ext z
    constructor
    · intro hz
      have hz' := mem_iInter.mp hz
      have hzE : z ∈ E := (hz' 0).1
      have hz1 : 1 < ‖z‖ := hzE
      have hpos : 0 < ‖z‖ - 1 := by linarith
      obtain ⟨N₁, hN₁⟩ := exists_nat_gt (1 / (‖z‖ - 1))
      obtain ⟨N₂, hN₂⟩ := exists_nat_gt ‖z‖
      refine absurd ⟨?_, ?_⟩ (hz' (N₁ + N₂)).2
      · have h1 : 1 < (N₁ : ℝ) * (‖z‖ - 1) := (div_lt_iff₀ hpos).mp hN₁
        have h2 : 1 / (((N₁ + N₂ : ℕ) : ℝ) + 1) ≤ ‖z‖ - 1 := by
          rw [div_le_iff₀ (by positivity)]
          push_cast
          have : (0 : ℝ) ≤ N₂ := Nat.cast_nonneg _
          nlinarith
        linarith
      · push_cast
        have : (0 : ℝ) ≤ N₁ := Nat.cast_nonneg _
        linarith
    · intro h
      exact absurd h (notMem_empty z)
  have htail : Tendsto (fun k => ∫ z in E \ A k, ‖g z‖ ^ 2 * W z) atTop (𝓝 0) := by
    have h := tendsto_setIntegral_of_antitone (μ := volume) (fun k => hEm.diff (hAm k)) hanti
      ⟨0, (hint g hg).mono_set sdiff_subset⟩
    rw [hinter, Measure.restrict_empty, integral_zero_measure] at h
    exact h
  -- the main estimate
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨k, hk⟩ := (Metric.tendsto_atTop.mp htail) (ε / 16) (by positivity)
  have hk' : ∫ z in E \ A k, ‖g z‖ ^ 2 * W z < ε / 16 := by
    have := hk k le_rfl
    rw [Real.dist_eq, sub_zero] at this
    exact (le_abs_self _).trans_lt this
  set K := A k with hKdef
  have hKs : K ⊆ E := hAsub k
  have hKm : MeasurableSet K := hAm k
  have hU : TendstoUniformlyOn f g atTop K :=
    (tendstoLocallyUniformlyOn_iff_forall_isCompact hE).1 hloc K hKs (hAc k)
  obtain ⟨B, hB⟩ := (hAc k).exists_bound_of_continuousOn (hg.1.continuousOn.mono hKs)
  obtain ⟨MW, hMW⟩ := (hAc k).exists_bound_of_continuousOn hWc.continuousOn
  have hvol : volume K < ⊤ := (hAc k).measure_lt_top
  set V := volume.real K with hVdef
  have hV0 : 0 ≤ V := measureReal_nonneg
  set B' := max B 0 with hB'def
  set MW' := max MW 0 with hMW'def
  have hB'0 : 0 ≤ B' := le_max_right _ _
  have hMW'0 : 0 ≤ MW' := le_max_right _ _
  set δ := min 1 (ε / (16 * ((2 * B' + 1) * (MW' * V + 1)))) with hδdef
  have hP : 0 < (2 * B' + 1) * (MW' * V + 1) := by positivity
  have hδ0 : 0 < δ := lt_min one_pos (by positivity)
  have hδ1 : δ ≤ 1 := min_le_left _ _
  have hδε : δ * ((2 * B' + 1) * (MW' * V + 1)) ≤ ε / 16 := by
    have h := min_le_right (1 : ℝ) (ε / (16 * ((2 * B' + 1) * (MW' * V + 1))))
    calc δ * ((2 * B' + 1) * (MW' * V + 1)) ≤ ε / (16 * ((2 * B' + 1) * (MW' * V + 1))) *
          ((2 * B' + 1) * (MW' * V + 1)) := mul_le_mul_of_nonneg_right h hP.le
      _ = ε / 16 := by field_simp
  have hev := (Metric.tendstoUniformlyOn_iff.mp hU δ hδ0).and
    (Metric.tendsto_nhds.mp hIn (ε / 16) (by positivity))
  obtain ⟨N, hN⟩ := eventually_atTop.mp hev
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨hun, hIdist⟩ := hN n hn
  rw [Real.dist_eq] at hIdist
  have hWz : ∀ z ∈ K, W z ≤ MW' := fun z hz =>
    (le_abs_self _).trans ((Real.norm_eq_abs (W z) ▸ hMW z hz).trans (le_max_left _ _))
  have hd : ∀ z ∈ K, ‖f n z - g z‖ < δ := fun z hz => by
    rw [← dist_eq_norm, dist_comm]; exact hun z hz
  -- (a) the compact part of the difference
  have ha : ∫ z in K, ‖f n z - g z‖ ^ 2 * W z ≤ ε / 16 := by
    have hb : ∀ z ∈ K, ‖‖f n z - g z‖ ^ 2 * W z‖ ≤ δ * MW' := by
      intro z hz
      rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) (hW0 z))]
      have hsq : ‖f n z - g z‖ ^ 2 ≤ δ := by
        have := pow_le_pow_left₀ (norm_nonneg _) (hd z hz).le 2
        nlinarith
      exact mul_le_mul hsq (hWz z hz) (hW0 z) hδ0.le
    have h := norm_setIntegral_le_of_norm_le_const hvol hb
    have hle : δ * MW' * V ≤ δ * ((2 * B' + 1) * (MW' * V + 1)) := by
      have h1 : MW' * V ≤ (2 * B' + 1) * (MW' * V + 1) := by nlinarith [mul_nonneg hMW'0 hV0]
      nlinarith
    calc ∫ z in K, ‖f n z - g z‖ ^ 2 * W z ≤ ‖∫ z in K, ‖f n z - g z‖ ^ 2 * W z‖ := Real.le_norm_self _
      _ ≤ δ * MW' * V := h
      _ ≤ ε / 16 := hle.trans hδε
  -- (b) the compact parts of the squared norms
  have hFK : IntegrableOn (fun z => ‖f n z‖ ^ 2 * W z) K := (hint _ (hf n)).mono_set hKs
  have hGK : IntegrableOn (fun z => ‖g z‖ ^ 2 * W z) K := (hint _ hg).mono_set hKs
  have hbb : |(∫ z in K, ‖f n z‖ ^ 2 * W z) - ∫ z in K, ‖g z‖ ^ 2 * W z| ≤ ε / 16 := by
    rw [← integral_sub hFK hGK]
    have hbd : ∀ z ∈ K, ‖‖f n z‖ ^ 2 * W z - ‖g z‖ ^ 2 * W z‖ ≤ δ * (2 * B' + 1) * MW' := by
      intro z hz
      have hgz : ‖g z‖ ≤ B' := (hB z hz).trans (le_max_left _ _)
      have h1 := hd z hz
      have habs : |‖f n z‖ - ‖g z‖| ≤ ‖f n z - g z‖ := abs_norm_sub_norm_le _ _
      have hfz : ‖f n z‖ ≤ B' + 1 := by
        have : ‖f n z‖ ≤ ‖g z‖ + ‖f n z - g z‖ := by
          calc ‖f n z‖ = ‖g z + (f n z - g z)‖ := by congr 1; ring
            _ ≤ _ := norm_add_le _ _
        linarith
      have hprod : |‖f n z‖ ^ 2 - ‖g z‖ ^ 2| ≤ δ * (2 * B' + 1) := by
        have e : ‖f n z‖ ^ 2 - ‖g z‖ ^ 2 = (‖f n z‖ - ‖g z‖) * (‖f n z‖ + ‖g z‖) := by ring
        rw [e, abs_mul, abs_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))]
        exact mul_le_mul (habs.trans h1.le) (by linarith) (by positivity) hδ0.le
      rw [← sub_mul, Real.norm_eq_abs, abs_mul, abs_of_nonneg (hW0 z)]
      exact mul_le_mul hprod (hWz z hz) (hW0 z) (by positivity)
    have h := norm_setIntegral_le_of_norm_le_const hvol hbd
    rw [Real.norm_eq_abs] at h
    refine h.trans ?_
    have hle : δ * (2 * B' + 1) * MW' * V ≤ δ * ((2 * B' + 1) * (MW' * V + 1)) := by
      have : 0 ≤ δ * (2 * B' + 1) := by positivity
      nlinarith
    exact hle.trans hδε
  -- splitting off the compact part
  have hsplit : ∀ h ∈ A2fun E, I h = (∫ z in K, ‖h z‖ ^ 2 * W z) + ∫ z in E \ K, ‖h z‖ ^ 2 * W z := by
    intro h hh
    have := integral_inter_add_sdiff hKm (hint h hh)
    rw [inter_eq_right.mpr hKs] at this
    exact this.symm
  have hF := hsplit _ (hf n)
  have hG := hsplit _ hg
  have hD := hsplit _ (hfg n)
  -- the tails
  have htd : ∫ z in E \ K, ‖f n z - g z‖ ^ 2 * W z ≤
      2 * (∫ z in E \ K, ‖f n z‖ ^ 2 * W z) + 2 * ∫ z in E \ K, ‖g z‖ ^ 2 * W z := by
    have hFT := (hint _ (hf n)).mono_set (sdiff_subset : E \ K ⊆ E)
    have hGT := (hint _ hg).mono_set (sdiff_subset : E \ K ⊆ E)
    rw [← integral_const_mul, ← integral_const_mul, ← integral_add (hFT.const_mul 2) (hGT.const_mul 2)]
    refine setIntegral_mono_on ((hint _ (hfg n)).mono_set sdiff_subset) ((hFT.const_mul 2).add (hGT.const_mul 2))
      (hEm.diff hKm) fun z _ => ?_
    have h2 : ‖f n z - g z‖ ^ 2 ≤ 2 * ‖f n z‖ ^ 2 + 2 * ‖g z‖ ^ 2 := by
      have h1 := norm_sub_le (f n z) (g z)
      nlinarith [norm_nonneg (f n z - g z), norm_nonneg (f n z), norm_nonneg (g z),
        sq_nonneg (‖f n z‖ - ‖g z‖)]
    have := mul_le_mul_of_nonneg_right h2 (hW0 z)
    linarith
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (hI0 _)]
  rw [abs_le] at hbb
  rw [abs_lt] at hIdist
  have hDval : I (fun z => f n z - g z) =
      (∫ z in K, ‖f n z - g z‖ ^ 2 * W z) + ∫ z in E \ K, ‖f n z - g z‖ ^ 2 * W z := hD
  linarith [hF, hG]

/-! ### T1 support: the base points converge -/

theorem a6_ext_mem {w : ℂ} (hw : w ∈ unitDiscExterior) : (w : ExtPlane) ∈ extDiscExterior :=
  Or.inl (mem_image_of_mem _ hw)

theorem a6_gMu_coe {μ : LinfStar} (hμ : μ ∈ LinfStarBall) {w : ℂ} (hw : w ∈ unitDiscExterior) :
    ((gMu μ w : ℂ) : ExtPlane) = normalizedWeldingSphere μ (w : ExtPlane) := by
  rw [gMu_eq_normalizedWeldingExterior hμ hw, normalizedWeldingExterior_coe hμ]

theorem a6_inv_nws {μ : LinfStar} (hμ : μ ∈ LinfStarBall) {w : ℂ} (hw : w ∈ unitDiscExterior) :
    Function.invFun (normalizedWeldingSphere μ) ((gMu μ w : ℂ) : ExtPlane) = (w : ExtPlane) := by
  rw [a6_gMu_coe hμ hw]
  exact Function.leftInverse_invFun (normalizedWeldingSphere_bijective μ).1 _

theorem a6_TCurve_mem (p : T1) {w : ℂ} (hw : w ∈ unitDiscExterior) :
    (p, ((gMu (Quotient.out p : LinfStarBall) w : ℂ) : ExtPlane)) ∈ TCurve := by
  show _ ∈ wB (Quotient.out p : LinfStarBall) '' extDiscExterior
  rw [← tcg_welding_image (Quotient.out p : LinfStarBall).2, a6_gMu_coe (Quotient.out p : LinfStarBall).2 hw]
  exact mem_image_of_mem _ (a6_ext_mem hw)

/-- **L2.** Convergence in the Teichmüller curve forces convergence of the base points `wₙ → v`. -/
theorem a6_w_tendsto {p : ℕ → T1} {w : ℕ → ℂ} {q : T1} {v : ℂ}
    (hw : ∀ n, w n ∈ unitDiscExterior) (hv : v ∈ unitDiscExterior)
    (hlim : @Tendsto _ _ (fun n => (p n, ((gMu (Quotient.out (p n) : LinfStarBall) (w n) : ℂ) : ExtPlane))) atTop
      (@nhds _ (@instTopologicalSpaceProd _ _ hilbertTopology inferInstance)
        (q, ((gMu (Quotient.out q : LinfStarBall) v : ℂ) : ExtPlane)))) :
    Tendsto w atTop (𝓝 v) := by
  let _ : TopologicalSpace T1 := hilbertTopology
  have hT := (tcg_fibre_parameter_continuous _ (a6_TCurve_mem q hv)).tendsto.comp
    (tendsto_nhdsWithin_iff.2 ⟨hlim, Eventually.of_forall fun n => a6_TCurve_mem (p n) (hw n)⟩)
  have hT' : Tendsto (fun n => Function.invFun (normalizedWeldingSphere (Quotient.out (p n) : LinfStarBall))
      ((gMu (Quotient.out (p n) : LinfStarBall) (w n) : ℂ) : ExtPlane)) atTop
      (𝓝 (Function.invFun (normalizedWeldingSphere (Quotient.out q : LinfStarBall))
        ((gMu (Quotient.out q : LinfStarBall) v : ℂ) : ExtPlane))) := hT
  rw [a6_inv_nws (Quotient.out q : LinfStarBall).2 hv] at hT'
  have h2 : Tendsto (fun n => (w n : ExtPlane)) atTop (𝓝 (v : ExtPlane)) :=
    hT'.congr fun n => a6_inv_nws (Quotient.out (p n) : LinfStarBall).2 (hw n)
  exact OnePoint.isOpenEmbedding_coe.isInducing.tendsto_nhds_iff.2 h2

/-! ### T1 support: the norms converge -/

theorem a6_origin_mul (x : T1) : mulT originT x = x := by
  have h0 : invT originT = originT := by
    have := gtr_c_inv_mul_self originT
    rwa [gtr_c_mul_one] at this
  calc mulT originT x = invT (invT (mulT originT x)) := (grp_invT_invT _).symm
    _ = invT (mulT (invT x) (invT originT)) := by rw [gtr_c_inv_mul_rev]
    _ = x := by rw [h0, gtr_c_mul_one, grp_invT_invT]

/-- `‖𝒮(𝗀^p)‖_{A₂(𝔻*)} = ‖β(p⁻¹)‖_{A₂(𝔻)}`. -/
theorem a6_normS_gMu (p : T1) :
    normA2 unitDiscExterior (schwarzianHol (gMu (Quotient.out p : LinfStarBall))) =
      normA2 unitDisc (AInf.toFun (bers (invT p))) := by
  set r := invT p with hr
  have hμ := (Quotient.out r : LinfStarBall).2
  have hcl : Phi ⟨beltramiInv ((Quotient.out r : LinfStarBall) : LinfStar), grp_inv_mem hμ⟩ = p := by
    have h1 : Phi (Quotient.out r) = r := Quotient.out_eq r
    have h2 := gtp_invT_phi (Quotient.out r : LinfStarBall)
    rw [h1] at h2
    rw [← h2, hr, grp_invT_invT]
  have hrel : teichSetoid (⟨beltramiInv ((Quotient.out r : LinfStarBall) : LinfStar), grp_inv_mem hμ⟩ : LinfStarBall)
      (Quotient.out p : LinfStarBall) :=
    Quotient.exact (hcl.trans (Quotient.out_eq p).symm)
  have hG := (s2c_class_pair hrel).2
  have hopenE : IsOpen unitDiscExterior := a6_ext_open
  rw [← S2C.s2c_gsans_eq (Quotient.out p : LinfStarBall).2,
    ← normA2_congr hopenE.measurableSet (a55_schwarzian_congr hopenE hG), ab112_normA2_G hμ]
  refine normA2_congr measurableSet_ball fun y hy => ?_
  obtain ⟨hfd, hfi⟩ := fB_holomorphic_injective hμ
  rw [S2C.s2c_fsans_eq hμ]
  exact ((schwarzianHol_AInf_spec hfd hfi).1 y hy).symm

/-- **L5.** The `A₂(𝔻*)` norms of `𝒮(𝗀^{p_n})` converge. -/
theorem a6_norm_tendsto {p : ℕ → T1} {q : T1} (hp : ∀ n, p n ∈ T01) (hq : q ∈ T01)
    (hpq : @Tendsto _ _ p atTop (@nhds _ hilbertTopology q)) :
    Tendsto (fun n => normA2 unitDiscExterior (schwarzianHol (gMu (Quotient.out (p n) : LinfStarBall)))) atTop
      (𝓝 (normA2 unitDiscExterior (schwarzianHol (gMu (Quotient.out q : LinfStarBall))))) := by
  let _ : TopologicalSpace T1 := hilbertTopology
  have hinv : Tendsto (fun n => invT (p n)) atTop (𝓝 (invT q)) := by
    have hc := (thm_3_8 (originT, q) ⟨lemma_3_4.1, hq⟩).tendsto.comp
      (tendsto_nhdsWithin_iff.2 ⟨tendsto_const_nhds.prodMk_nhds hpq,
        Eventually.of_forall fun n => ⟨lemma_3_4.1, hp n⟩⟩)
    simpa only [Function.comp_def, a6_origin_mul] using hc
  have hp' : ∀ n, invT (p n) ∈ T01 := fun n => lemma_3_4.2.2 _ (hp n)
  have hq' := lemma_3_4.2.2 _ hq
  have hx := (tcg_A2_bers_continuous _ hq').tendsto.comp
    (tendsto_nhdsWithin_iff.2 ⟨hinv, Eventually.of_forall hp'⟩)
  have hn := (ENNReal.continuous_coe.tendsto _).comp ((continuous_nnnorm.tendsto _).comp hx)
  have e : ∀ r ∈ T01, ((‖toA2 unitDisc (AInf.toFun (bers r))‖₊ : ℝ≥0) : ℝ≥0∞) =
      normA2 unitDisc (AInf.toFun (bers r)) := fun r hr => by
    rw [cor_3_2] at hr
    exact a4_toA2_norm hr
  simp only [a6_normS_gMu]
  rw [← e _ hq']
  exact hn.congr fun n => e _ (hp' n)

/-! ### T1 support: Möbius maps depend continuously on their coefficients -/

theorem a6_finPart_contAt (z : ℂ) : ContinuousAt finPart (z : ExtPlane) := by
  rw [ContinuousAt, OnePoint.nhds_coe_eq, tendsto_map'_iff]
  exact tendsto_id

/-- At a finite point with nonzero denominator. -/
theorem a6_mob_fin {ι : Type*} {l : Filter ι} {a b c d : ι → ℂ} {x : ι → ExtPlane} {a₀ b₀ c₀ d₀ z₀ : ℂ}
    (ha : Tendsto a l (𝓝 a₀)) (hb : Tendsto b l (𝓝 b₀)) (hc : Tendsto c l (𝓝 c₀)) (hd : Tendsto d l (𝓝 d₀))
    (hx : Tendsto x l (𝓝 (z₀ : ExtPlane))) (hz : c₀ * z₀ + d₀ ≠ 0) :
    Tendsto (fun i => mobiusExt (a i) (b i) (c i) (d i) (x i)) l (𝓝 (mobiusExt a₀ b₀ c₀ d₀ (z₀ : ExtPlane))) := by
  have hfin : ∀ᶠ i in l, x i ≠ extInf := hx.eventually (compl_singleton_mem_nhds (OnePoint.coe_ne_infty z₀))
  have hz' : Tendsto (fun i => finPart (x i)) l (𝓝 z₀) := (a6_finPart_contAt z₀).tendsto.comp hx
  have hden : Tendsto (fun i => c i * finPart (x i) + d i) l (𝓝 (c₀ * z₀ + d₀)) := (hc.mul hz').add hd
  have hne : ∀ᶠ i in l, c i * finPart (x i) + d i ≠ 0 := hden.eventually_ne hz
  have hval : Tendsto (fun i => (a i * finPart (x i) + b i) / (c i * finPart (x i) + d i)) l
      (𝓝 ((a₀ * z₀ + b₀) / (c₀ * z₀ + d₀))) := ((ha.mul hz').add hb).div hden hz
  rw [mobiusExt_coe hz]
  refine ((OnePoint.continuous_coe.tendsto _).comp hval).congr' ?_
  filter_upwards [hfin, hne] with i h1 h2
  show (((a i * finPart (x i) + b i) / (c i * finPart (x i) + d i) : ℂ) : ExtPlane) =
    mobiusExt (a i) (b i) (c i) (d i) (x i)
  conv_rhs => rw [← coe_finPart_of_ne h1]
  rw [mobiusExt_coe h2]
  rfl

/-- `M(x) = M'(1/x)` with the swapped coefficients. -/
theorem a6_mob_swap (a b c d : ℂ) (x : ExtPlane) :
    mobiusExt a b c d x = mobiusExt b a d c (mobiusExt 0 1 1 0 x) := by
  induction x using OnePoint.rec with
  | infty =>
    show mobiusExt a b c d extInf = mobiusExt b a d c (mobiusExt 0 1 1 0 extInf)
    rw [mobiusExt_infty_of_ne one_ne_zero, zero_div]
    by_cases hc : c = 0
    · rw [mobiusExt_infty_of_eq hc, mobiusExt_coe_of_eq_zero (by simp [hc])]
    · rw [mobiusExt_infty_of_ne hc, mobiusExt_coe (by simpa using hc)]
      simp [mobiusFn]
  | coe u =>
    by_cases hu : u = 0
    · subst hu
      rw [mobiusExt_coe_of_eq_zero (a := 0) (b := 1) (by simp)]
      by_cases hd : d = 0
      · rw [mobiusExt_infty_of_eq hd, mobiusExt_coe_of_eq_zero (by simp [hd])]
      · rw [mobiusExt_infty_of_ne hd, mobiusExt_coe (by simpa using hd)]
        simp [mobiusFn]
    · rw [mobiusExt_coe (a := 0) (b := 1) (c := 1) (d := 0) (by simpa using hu)]
      have e : d * mobiusFn 0 1 1 0 u + c = (c * u + d) / u := by
        simp only [mobiusFn, zero_mul, zero_add, one_mul, add_zero]; field_simp; try ring
      by_cases h : c * u + d = 0
      · rw [mobiusExt_coe_of_eq_zero h, mobiusExt_coe_of_eq_zero (by rw [e, h, zero_div])]
      · rw [mobiusExt_coe h, mobiusExt_coe (by rw [e]; exact div_ne_zero h hu)]
        congr 1
        simp only [mobiusFn, zero_mul, zero_add, one_mul, add_zero]
        field_simp
        try ring

/-- `M(x) = 1/M''(x)` with the rows swapped. -/
theorem a6_mob_recip {a b c d : ℂ} (h : a * d - b * c ≠ 0) (x : ExtPlane) :
    mobiusExt a b c d x = mobiusExt 0 1 1 0 (mobiusExt c d a b x) := by
  induction x using OnePoint.rec with
  | infty =>
    show mobiusExt a b c d extInf = mobiusExt 0 1 1 0 (mobiusExt c d a b extInf)
    by_cases ha : a = 0
    · have hc : c ≠ 0 := by rintro rfl; apply h; simp [ha]
      rw [mobiusExt_infty_of_eq ha, mobiusExt_infty_of_ne one_ne_zero, mobiusExt_infty_of_ne hc, ha, zero_div,
        zero_div]
    · rw [mobiusExt_infty_of_ne ha]
      by_cases hc : c = 0
      · rw [mobiusExt_infty_of_eq hc, hc, zero_div, mobiusExt_coe_of_eq_zero (by simp)]
      · rw [mobiusExt_infty_of_ne hc, mobiusExt_coe (by simpa using div_ne_zero hc ha)]
        congr 1
        simp only [mobiusFn, zero_mul, zero_add, one_mul, add_zero]
        field_simp
        try ring
  | coe z =>
    by_cases hN : a * z + b = 0
    · have hD : c * z + d ≠ 0 := by
        intro hD; apply h; linear_combination a * hD - c * hN
      rw [mobiusExt_coe_of_eq_zero hN, mobiusExt_infty_of_ne one_ne_zero, mobiusExt_coe hD]
      simp [mobiusFn, hN]
    · rw [mobiusExt_coe hN]
      by_cases hD : c * z + d = 0
      · rw [mobiusExt_coe_of_eq_zero hD, mobiusExt_coe_of_eq_zero (by simp [mobiusFn, hD])]
      · rw [mobiusExt_coe hD, mobiusExt_coe (by simpa [mobiusFn] using div_ne_zero hD hN)]
        congr 1
        simp only [mobiusFn, zero_mul, zero_add, one_mul, add_zero]
        field_simp
        try ring

/-- **Joint continuity** of `(a, b, c, d, x) ↦ M_{abcd}(x)` at nondegenerate coefficients with `c ≠ 0`. -/
theorem a6_mob_tendsto {ι : Type*} {l : Filter ι} {a b c d : ι → ℂ} {x : ι → ExtPlane} {a₀ b₀ c₀ d₀ : ℂ}
    {x₀ : ExtPlane} (ha : Tendsto a l (𝓝 a₀)) (hb : Tendsto b l (𝓝 b₀)) (hc : Tendsto c l (𝓝 c₀))
    (hd : Tendsto d l (𝓝 d₀)) (hx : Tendsto x l (𝓝 x₀)) (hc₀ : c₀ ≠ 0) (hdet : a₀ * d₀ - b₀ * c₀ ≠ 0) :
    Tendsto (fun i => mobiusExt (a i) (b i) (c i) (d i) (x i)) l (𝓝 (mobiusExt a₀ b₀ c₀ d₀ x₀)) := by
  have hJ : Continuous (mobiusExt 0 1 1 0) := continuous_mobiusExt (by norm_num)
  induction x₀ using OnePoint.rec with
  | infty =>
    have hy : Tendsto (fun i => mobiusExt 0 1 1 0 (x i)) l (𝓝 ((0 : ℂ) : ExtPlane)) := by
      have := (hJ.tendsto _).comp hx
      rwa [Function.comp_def, show mobiusExt 0 1 1 0 (OnePoint.infty : ExtPlane) = ((0 : ℂ) : ExtPlane) from by
        rw [show (OnePoint.infty : ExtPlane) = extInf from rfl, mobiusExt_infty_of_ne one_ne_zero, zero_div]] at this
    have h := a6_mob_fin hb ha hd hc hy (by simpa using hc₀)
    rw [a6_mob_swap a₀ b₀ c₀ d₀]
    rw [show mobiusExt 0 1 1 0 (OnePoint.infty : ExtPlane) = ((0 : ℂ) : ExtPlane) from by
        rw [show (OnePoint.infty : ExtPlane) = extInf from rfl, mobiusExt_infty_of_ne one_ne_zero, zero_div]]
    exact h.congr fun i => (a6_mob_swap _ _ _ _ _).symm
  | coe z₀ =>
    by_cases hz : c₀ * z₀ + d₀ = 0
    · have hN : a₀ * z₀ + b₀ ≠ 0 := by
        intro hN; apply hdet; linear_combination a₀ * hz - c₀ * hN
      have hdetl : Tendsto (fun i => a i * d i - b i * c i) l (𝓝 (a₀ * d₀ - b₀ * c₀)) :=
        (ha.mul hd).sub (hb.mul hc)
      have h := (hJ.tendsto _).comp (a6_mob_fin hc hd ha hb hx hN)
      rw [a6_mob_recip hdet]
      refine h.congr' ?_
      filter_upwards [hdetl.eventually_ne hdet] with i hi
      exact (a6_mob_recip hi _).symm
    · exact a6_mob_fin ha hb hc hd hx hz

/-! ### T1 support: the welded maps converge locally uniformly -/

theorem a6_sigmaInv_mem {w z : ℂ} (hw : w ∈ unitDiscExterior) (hz : z ∈ unitDiscExterior) :
    sigmaInvSphere (w : ExtPlane) (z : ExtPlane) ∈ extDiscExterior := by
  obtain ⟨-, hkey⟩ := appa2_sigmaInv_coeffs (w := w)
  have hw1 : 1 < ‖w‖ := hw
  have hz1 : 1 < ‖z‖ := hz
  have hw0 : w ≠ 1 := by rintro rfl; simp at hw1
  have h1 : 0 < ‖1 - w‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (Ne.symm hw0))
  have hpos : 0 < ‖1 - w‖ ^ 2 * (‖w‖ ^ 2 - 1) * (‖z‖ ^ 2 - 1) := by
    have : 1 < ‖w‖ ^ 2 := by nlinarith
    have : 1 < ‖z‖ ^ 2 := by nlinarith
    have : 0 < ‖1 - w‖ ^ 2 := by positivity
    have : 0 < ‖1 - w‖ ^ 2 * (‖w‖ ^ 2 - 1) := by nlinarith
    nlinarith
  show mobiusExt (-w * (1 - conj w)) (-(1 - w)) (-(1 - conj w)) (-(1 - w) * conj w) (z : ExtPlane) ∈ _
  by_cases h : -(1 - conj w) * z + -(1 - w) * conj w = 0
  · rw [mobiusExt_coe_of_eq_zero h]
    exact Or.inr rfl
  · rw [mobiusExt_coe h]
    refine Or.inl ⟨_, ?_, rfl⟩
    show 1 < ‖mobiusFn (-w * (1 - conj w)) (-(1 - w)) (-(1 - conj w)) (-(1 - w) * conj w) z‖
    have hk := hkey z
    have hlt : ‖-(1 - conj w) * z + -(1 - w) * conj w‖ ^ 2 < ‖-w * (1 - conj w) * z + -(1 - w)‖ ^ 2 := by linarith
    have hlt' := lt_of_pow_lt_pow_left₀ 2 (norm_nonneg _) hlt
    rw [mobiusFn, norm_div, one_lt_div (norm_pos_iff.mpr h)]
    exact hlt'

theorem a6_weldG_fin {μ : LinfStar} (hμ : μ ∈ LinfStarBall) {v z : ℂ} (hv : v ∈ unitDiscExterior) :
    mobiusExt 1 0 (-1 / gMu μ v) 1 (normalizedWeldingSphere μ (sigmaInvSphere (v : ExtPlane) (z : ExtPlane))) ≠
      extInf := by
  have hg0 := gMu_exterior_ne_zero hμ hv
  have hc0 : -1 / gMu μ v ≠ 0 := div_ne_zero (neg_ne_zero.mpr one_ne_zero) hg0
  intro h
  set Y := normalizedWeldingSphere μ (sigmaInvSphere (v : ExtPlane) (z : ExtPlane)) with hYdef
  by_cases hY : Y = extInf
  · rw [hY, mobiusExt_infty_of_ne hc0] at h
    exact OnePoint.coe_ne_infty _ h
  · have hY' := coe_finPart_of_ne hY
    rw [← hY'] at h
    by_cases hden : -1 / gMu μ v * finPart Y + 1 = 0
    · have h2 : gMu μ v * (-1 / gMu μ v * finPart Y + 1) = gMu μ v - finPart Y := by
        field_simp
        try ring
      rw [hden, mul_zero] at h2
      have hy : finPart Y = gMu μ v := by linear_combination h2
      have hYv : normalizedWeldingSphere μ (sigmaInvSphere (v : ExtPlane) (z : ExtPlane)) =
          normalizedWeldingSphere μ (v : ExtPlane) := by
        rw [← a6_gMu_coe hμ hv, ← hy]
        exact hY'.symm
      have hs := (normalizedWeldingSphere_bijective μ).1 hYv
      have hs2 : sigmaInvSphere (v : ExtPlane) (z : ExtPlane) = sigmaInvSphere (v : ExtPlane) extInf :=
        hs.trans (sigmaInvSphere_infty hv).symm
      obtain ⟨a, b, c, d, hd, he⟩ := sigmaInvSphere_isMobius hv
      rw [he] at hs2
      exact OnePoint.coe_ne_infty _
        ((mobiusHomeomorph a b c d hd).injective (by simpa only [mobiusHomeomorph_apply] using hs2))
    · rw [mobiusExt_coe hden] at h
      exact OnePoint.coe_ne_infty _ h

theorem a6_sigmaInv_eq (w : ℂ) :
    sigmaInvSphere (w : ExtPlane) = mobiusExt (-w * (1 - conj w)) (-(1 - w)) (-(1 - conj w)) (-(1 - w) * conj w) :=
  rfl

theorem a6_sigmaInv_tendsto {ι : Type*} {l : Filter ι} {u y : ι → ℂ} {v z₀ : ℂ} (hv : v ∈ unitDiscExterior)
    (hu : Tendsto u l (𝓝 v)) (hy : Tendsto y l (𝓝 z₀)) :
    Tendsto (fun i => sigmaInvSphere (u i : ExtPlane) (y i : ExtPlane)) l
      (𝓝 (sigmaInvSphere (v : ExtPlane) (z₀ : ExtPlane))) := by
  have hv1 : 1 < ‖v‖ := hv
  have hv0 : v ≠ 1 := by rintro rfl; simp at hv1
  have hC0 : -(1 - conj v) ≠ 0 := by
    rw [neg_ne_zero, sub_ne_zero]
    intro h
    apply hv0
    have := congrArg conj h
    simpa using this.symm
  have hκ : 0 < ‖1 - v‖ ^ 2 * (‖v‖ ^ 2 - 1) := by
    have h1 : 0 < ‖1 - v‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (Ne.symm hv0))
    have h2 : 1 < ‖v‖ ^ 2 := by nlinarith
    have : 0 < ‖1 - v‖ ^ 2 := by positivity
    nlinarith
  have hdet : (-v * (1 - conj v)) * (-(1 - v) * conj v) - (-(1 - v)) * (-(1 - conj v)) ≠ 0 := by
    rw [(appa2_sigmaInv_coeffs (w := v)).1]
    exact_mod_cast hκ.ne'
  have hcj : Tendsto (fun i => conj (u i)) l (𝓝 (conj v)) := (Complex.continuous_conj.tendsto v).comp hu
  have h := a6_mob_tendsto (a := fun i => -u i * (1 - conj (u i))) (b := fun i => -(1 - u i))
    (c := fun i => -(1 - conj (u i))) (d := fun i => -(1 - u i) * conj (u i)) (x := fun i => (y i : ExtPlane))
    (hu.neg.mul (tendsto_const_nhds.sub hcj)) (tendsto_const_nhds.sub hu).neg
    (tendsto_const_nhds.sub hcj).neg ((tendsto_const_nhds.sub hu).neg.mul hcj)
    ((OnePoint.continuous_coe.tendsto _).comp hy) hC0 hdet
  simp only [a6_sigmaInv_eq]
  exact h

theorem a6_nws_tendsto {ι : Type*} {l : Filter ι} {P : ι → T1} {X : ι → ExtPlane} {q : T1} {X₀ : ExtPlane}
    (hP : @Tendsto _ _ P l (@nhds _ hilbertTopology q)) (hX : Tendsto X l (𝓝 X₀))
    (hXm : ∀ᶠ i in l, X i ∈ extDiscExterior) (hX₀ : X₀ ∈ extDiscExterior) :
    Tendsto (fun i => normalizedWeldingSphere (Quotient.out (P i) : LinfStarBall) (X i)) l
      (𝓝 (normalizedWeldingSphere (Quotient.out q : LinfStarBall) X₀)) := by
  let _ : TopologicalSpace T1 := hilbertTopology
  have hΦ : ContinuousOn (fun r : T1 × ExtPlane => normalizedWeldingSphere (Quotient.out r.1 : LinfStarBall) r.2)
      {r | r.2 ∈ extDiscExterior} := by
    refine continuousOn_iff_continuous_domRestrict.2 ?_
    exact tcg_welding_class_continuous_family (X := {r : T1 × ExtPlane | r.2 ∈ extDiscExterior})
      (fun r => r.1.1) (fun r => r.1.2) (continuous_fst.comp continuous_subtype_val)
      (continuous_snd.comp continuous_subtype_val) (fun r => r.2)
  have hmem : (q, X₀) ∈ {r : T1 × ExtPlane | r.2 ∈ extDiscExterior} := hX₀
  have h2 : ∀ᶠ i in l, (P i, X i) ∈ {r : T1 × ExtPlane | r.2 ∈ extDiscExterior} := hXm.mono fun i hi => hi
  have h3 : Tendsto (fun i => (P i, X i)) l (𝓝[{r : T1 × ExtPlane | r.2 ∈ extDiscExterior}] (q, X₀)) :=
    tendsto_inf.2 ⟨hP.prodMk_nhds hX, tendsto_principal.2 h2⟩
  have h4 := (hΦ _ hmem).tendsto.comp h3
  exact h4

/-- **L3 (joint form).** `(n, z) ↦ weldG(μₙ, wₙ)(z)` converges at every point of `𝔻*`. -/
theorem a6_weldG_joint {p : ℕ → T1} {w : ℕ → ℂ} {q : T1} {v : ℂ}
    (hw : ∀ n, w n ∈ unitDiscExterior) (hv : v ∈ unitDiscExterior)
    (hlim : @Tendsto _ _ (fun n => (p n, ((gMu (Quotient.out (p n) : LinfStarBall) (w n) : ℂ) : ExtPlane))) atTop
      (@nhds _ (@instTopologicalSpaceProd _ _ hilbertTopology inferInstance)
        (q, ((gMu (Quotient.out q : LinfStarBall) v : ℂ) : ExtPlane))))
    {z₀ : ℂ} (hz₀ : z₀ ∈ unitDiscExterior) :
    Tendsto (fun r : ℕ × ℂ => weldG (Quotient.out (p r.1) : LinfStarBall) (w r.1) r.2) (atTop ×ˢ 𝓝 z₀)
      (𝓝 (weldG (Quotient.out q : LinfStarBall) v z₀)) := by
  let _ : TopologicalSpace T1 := hilbertTopology
  have hwv := a6_w_tendsto hw hv hlim
  have hpq : Tendsto p atTop (𝓝 q) := (continuous_fst.tendsto _).comp hlim
  have hw1 : Tendsto (fun r : ℕ × ℂ => w r.1) (atTop ×ˢ 𝓝 z₀) (𝓝 v) := hwv.comp tendsto_fst
  have hp1 : Tendsto (fun r : ℕ × ℂ => p r.1) (atTop ×ˢ 𝓝 z₀) (𝓝 q) := hpq.comp tendsto_fst
  have hz : Tendsto (fun r : ℕ × ℂ => r.2) (atTop ×ˢ 𝓝 z₀) (𝓝 z₀) := tendsto_snd
  have hX := a6_sigmaInv_tendsto hv hw1 hz
  have hXmem : ∀ᶠ r in atTop ×ˢ 𝓝 z₀, sigmaInvSphere (w r.1 : ExtPlane) (r.2 : ExtPlane) ∈ extDiscExterior := by
    filter_upwards [tendsto_snd.eventually (a6_ext_open.mem_nhds hz₀)] with r hr
    exact a6_sigmaInv_mem (hw r.1) hr
  have hY := a6_nws_tendsto hp1 hX hXmem (a6_sigmaInv_mem hv hz₀)
  have hg : Tendsto (fun n => gMu (Quotient.out (p n) : LinfStarBall) (w n)) atTop
      (𝓝 (gMu (Quotient.out q : LinfStarBall) v)) :=
    OnePoint.isOpenEmbedding_coe.isInducing.tendsto_nhds_iff.2 ((continuous_snd.tendsto _).comp hlim)
  have hg0 := gMu_exterior_ne_zero (Quotient.out q : LinfStarBall).2 hv
  have hc : Tendsto (fun r : ℕ × ℂ => -1 / gMu (Quotient.out (p r.1) : LinfStarBall) (w r.1)) (atTop ×ˢ 𝓝 z₀)
      (𝓝 (-1 / gMu (Quotient.out q : LinfStarBall) v)) :=
    tendsto_const_nhds.div (hg.comp tendsto_fst) hg0
  have hZ := a6_mob_tendsto (a := fun _ => (1 : ℂ)) (b := fun _ => (0 : ℂ)) (d := fun _ => (1 : ℂ))
    tendsto_const_nhds tendsto_const_nhds hc tendsto_const_nhds hY
    (div_ne_zero (neg_ne_zero.mpr one_ne_zero) hg0) (by simp)
  have hfin := a6_weldG_fin (Quotient.out q : LinfStarBall).2 (z := z₀) hv
  have hcont := a6_finPart_contAt (finPart (mobiusExt 1 0 (-1 / gMu (Quotient.out q : LinfStarBall) v) 1
    (normalizedWeldingSphere (Quotient.out q : LinfStarBall) (sigmaInvSphere (v : ExtPlane) (z₀ : ExtPlane)))))
  rw [coe_finPart_of_ne hfin] at hcont
  have h4 := hcont.tendsto.comp hZ
  exact h4

/-- **L3.** `weldG(μₙ, wₙ) → weldG(μ, v)` locally uniformly on `𝔻*`. -/
theorem a6_weldG_LU {p : ℕ → T1} {w : ℕ → ℂ} {q : T1} {v : ℂ}
    (hw : ∀ n, w n ∈ unitDiscExterior) (hv : v ∈ unitDiscExterior)
    (hlim : @Tendsto _ _ (fun n => (p n, ((gMu (Quotient.out (p n) : LinfStarBall) (w n) : ℂ) : ExtPlane))) atTop
      (@nhds _ (@instTopologicalSpaceProd _ _ hilbertTopology inferInstance)
        (q, ((gMu (Quotient.out q : LinfStarBall) v : ℂ) : ExtPlane)))) :
    TendstoLocallyUniformlyOn (fun n => weldG (Quotient.out (p n) : LinfStarBall) (w n))
      (weldG (Quotient.out q : LinfStarBall) v) atTop unitDiscExterior := by
  rw [tendstoLocallyUniformlyOn_iff_filter]
  intro z₀ hz₀
  rw [tendstoUniformlyOnFilter_iff_tendsto]
  have hj := (a6_weldG_joint hw hv hlim hz₀).mono_left (Filter.prod_mono le_rfl (nhdsWithin_le_nhds (s := unitDiscExterior)))
  have hf : Tendsto (fun r : ℕ × ℂ => weldG (Quotient.out q : LinfStarBall) v r.2)
      (atTop ×ˢ 𝓝[unitDiscExterior] z₀) (𝓝 (weldG (Quotient.out q : LinfStarBall) v z₀)) :=
    ((appa2_weldG_univalent (Quotient.out q : LinfStarBall).2 hv).1.continuousOn z₀ hz₀).tendsto.comp tendsto_snd
  exact (hf.prodMk_nhds hj).mono_right (nhds_le_uniformity _)

/-! ### T1 support: Weierstrass for the Schwarzian -/

theorem a6_LU_const (c : ℂ) {U : Set ℂ} :
    TendstoLocallyUniformlyOn (fun (_ : ℕ) (_ : ℂ) => c) (fun _ => c) atTop U :=
  fun _ hu _ _ => ⟨univ, univ_mem, Eventually.of_forall fun _ _ _ => refl_mem_uniformity hu⟩

/-- **L4.** Locally uniform convergence of locally univalent maps gives locally uniform convergence of their
Schwarzians. -/
theorem a6_S_LU {F : ℕ → ℂ → ℂ} {f : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hF : ∀ n, DifferentiableOn ℂ (F n) U) (hF' : ∀ n, ∀ z ∈ U, deriv (F n) z ≠ 0)
    (hf : DifferentiableOn ℂ f U) (hf' : ∀ z ∈ U, deriv f z ≠ 0)
    (hL : TendstoLocallyUniformlyOn F f atTop U) :
    TendstoLocallyUniformlyOn (fun n => schwarzianHol (F n)) (schwarzianHol f) atTop U := by
  have h1 : TendstoLocallyUniformlyOn (fun n => deriv (F n)) (deriv f) atTop U :=
    hL.deriv (Eventually.of_forall hF) hU
  have h2 : TendstoLocallyUniformlyOn (fun n => deriv (deriv (F n))) (deriv (deriv f)) atTop U :=
    h1.deriv (Eventually.of_forall fun n => (hF n).deriv hU) hU
  have hd1 := hf.deriv hU
  have hd2 := hd1.deriv hU
  have hQ : TendstoLocallyUniformlyOn (fun n w => deriv (deriv (F n)) w / deriv (F n) w)
      (fun w => deriv (deriv f) w / deriv f w) atTop U :=
    h2.div₀ h1 hd2.continuousOn hd1.continuousOn hf'
  have hqd : DifferentiableOn ℂ (fun w => deriv (deriv f) w / deriv f w) U := hd2.div hd1 hf'
  have hQd : ∀ n, DifferentiableOn ℂ (fun w => deriv (deriv (F n)) w / deriv (F n) w) U := fun n =>
    (((hF n).deriv hU).deriv hU).div ((hF n).deriv hU) (hF' n)
  have h3 : TendstoLocallyUniformlyOn (fun n => deriv (fun w => deriv (deriv (F n)) w / deriv (F n) w))
      (deriv (fun w => deriv (deriv f) w / deriv f w)) atTop U :=
    hQ.deriv (Eventually.of_forall hQd) hU
  have h4 : TendstoLocallyUniformlyOn (fun n w => deriv (deriv (F n)) w / deriv (F n) w *
      (deriv (deriv (F n)) w / deriv (F n) w) / 2)
      (fun w => deriv (deriv f) w / deriv f w * (deriv (deriv f) w / deriv f w) / 2) atTop U :=
    (hQ.mul₀ hQ hqd.continuousOn hqd.continuousOn).div₀ (a6_LU_const 2)
      (hqd.continuousOn.mul hqd.continuousOn) continuousOn_const (fun _ _ => two_ne_zero)
  refine ((h3.sub h4).congr fun n z _ => ?_).congr_right fun z _ => ?_
  · show deriv (fun w => deriv (deriv (F n)) w / deriv (F n) w) z -
        deriv (deriv (F n)) z / deriv (F n) z * (deriv (deriv (F n)) z / deriv (F n) z) / 2 =
      deriv (fun w => deriv (deriv (F n)) w / deriv (F n) w) z -
        1 / 2 * (deriv (deriv (F n)) z / deriv (F n) z) ^ 2
    ring
  · show deriv (fun w => deriv (deriv f) w / deriv f w) z -
        deriv (deriv f) z / deriv f z * (deriv (deriv f) z / deriv f z) / 2 =
      deriv (fun w => deriv (deriv f) w / deriv f w) z - 1 / 2 * (deriv (deriv f) z / deriv f z) ^ 2
    ring

/-- **T1.** Clause (i) of Corollary A.6: convergence in `𝒯₀(1)` gives `𝒮(gₙ) → 𝒮(g)` in `A₂(𝔻*)`. -/
theorem a6_ext_schwarzian_tendsto {p : ℕ → T1} {w : ℕ → ℂ} {q : T1} {v : ℂ} (hp : ∀ n, p n ∈ T01)
    (hw : ∀ n, w n ∈ unitDiscExterior) (hq : q ∈ T01) (hv : v ∈ unitDiscExterior)
    (hlim : @Tendsto _ _ (fun n => (p n, ((gMu (Quotient.out (p n) : LinfStarBall) (w n) : ℂ) : ExtPlane))) atTop
      (@nhds _ (@instTopologicalSpaceProd _ _ hilbertTopology inferInstance)
        (q, ((gMu (Quotient.out q : LinfStarBall) v : ℂ) : ExtPlane)))) :
    Tendsto (fun n => normA2 unitDiscExterior (fun z =>
        schwarzianHol (weldG (Quotient.out (p n) : LinfStarBall) (w n)) z -
          schwarzianHol (weldG (Quotient.out q : LinfStarBall) v) z)) atTop (𝓝 0) := by
  have hpq : @Tendsto _ _ p atTop (@nhds _ hilbertTopology q) := by
    let _ : TopologicalSpace T1 := hilbertTopology
    exact (continuous_fst.tendsto _).comp hlim
  have hμ : ∀ n, ((Quotient.out (p n) : LinfStarBall) : LinfStar) ∈ LinfStarBall := fun n =>
    (Quotient.out (p n) : LinfStarBall).2
  have hU := fun n => appa2_weldG_univalent (hμ n) (hw n)
  have hUq := appa2_weldG_univalent (Quotient.out q : LinfStarBall).2 hv
  have hopen := a6_ext_open
  have hd : ∀ {g : ℂ → ℂ}, IsUnivalentAtInfty g → ∀ z ∈ unitDiscExterior, deriv g z ≠ 0 :=
    fun hg z hz => deriv_ne_zero_of_injOn hopen hg.1 hg.2.1 hz
  refine a6_RR (fun n => (appa2_betaStar_spec (hp n) (hw n)).2) (appa2_betaStar_spec hq hv).2
    (a6_S_LU hopen (fun n => (hU n).1) (fun n => hd (hU n)) hUq.1 (hd hUq) (a6_weldG_LU hw hv hlim)) ?_
  rw [appa2_normA2_schwarzian_weldG (Quotient.out q : LinfStarBall).2 hv]
  exact (a6_norm_tendsto hp hq hpq).congr fun n => (appa2_normA2_schwarzian_weldG (hμ n) (hw n)).symm

/-- Byte-identical copy of `cor_A_6` (assembly). -/
theorem a6_cor_A_6 {p : ℕ → T1} {w : ℕ → ℂ} {q : T1} {v : ℂ} (hp : ∀ n, p n ∈ T01)
    (hw : ∀ n, w n ∈ unitDiscExterior) (hq : q ∈ T01) (hv : v ∈ unitDiscExterior)
    (hlim : @Tendsto _ _ (fun n => (p n, ((gMu (Quotient.out (p n) : LinfStarBall) (w n) : ℂ) : ExtPlane))) atTop
      (@nhds _ (@instTopologicalSpaceProd _ _ hilbertTopology inferInstance)
        (q, ((gMu (Quotient.out q : LinfStarBall) v : ℂ) : ExtPlane)))) :
    Tendsto (fun n => normA2 unitDiscExterior (fun z =>
        schwarzianHol (weldG (Quotient.out (p n) : LinfStarBall) (w n)) z -
          schwarzianHol (weldG (Quotient.out q : LinfStarBall) v) z)) atTop (𝓝 0) ∧
      Tendsto (fun n => normA21 unitDiscExterior (fun z => betaHatStar (p n) (w n) z - betaHatStar q v z)) atTop
        (𝓝 0) := by
  have h1 := a6_ext_schwarzian_tendsto hp hw hq hv hlim
  refine ⟨h1, a6_ext_inverse (appa2_lemma_A_5_clause q hq v hv).1
    (fun n => (appa2_lemma_A_5_clause (p n) (hp n) (w n) (hw n)).1) (h1.congr fun n => ?_)⟩
  apply normA2_congr (D := unitDiscExterior) (isOpen_lt continuous_const continuous_norm).measurableSet
  intro z hz
  exact congrArg₂ (· - ·) ((appa2_betaStar_spec (hp n) (hw n)).1 hz) ((appa2_betaStar_spec hq hv).1 hz)

/-- **Corollary A.6** (TT:5928–5948). If `γ_n → γ` in `𝒯₀(1)`, then `𝒮(g_n) → 𝒮(g)` in `A₂(𝔻*)` and
`𝒜(g_n) → 𝒜(g)` in `A₂¹(𝔻*)`. -/
theorem cor_A_6 {p : ℕ → T1} {w : ℕ → ℂ} {q : T1} {v : ℂ} (hp : ∀ n, p n ∈ T01)
    (hw : ∀ n, w n ∈ unitDiscExterior) (hq : q ∈ T01) (hv : v ∈ unitDiscExterior)
    (hlim : @Tendsto _ _ (fun n => (p n, ((gMu (Quotient.out (p n) : LinfStarBall) (w n) : ℂ) : ExtPlane))) atTop
      (@nhds _ (@instTopologicalSpaceProd _ _ hilbertTopology inferInstance)
        (q, ((gMu (Quotient.out q : LinfStarBall) v : ℂ) : ExtPlane)))) :
    Tendsto (fun n => normA2 unitDiscExterior (fun z =>
        schwarzianHol (weldG (Quotient.out (p n) : LinfStarBall) (w n)) z -
          schwarzianHol (weldG (Quotient.out q : LinfStarBall) v) z)) atTop (𝓝 0) ∧
      Tendsto (fun n => normA21 unitDiscExterior (fun z => betaHatStar (p n) (w n) z - betaHatStar q v z)) atTop
        (𝓝 0) := by
  exact a6_cor_A_6 hp hw hq hv hlim

end AppA

end TakhtajanTeo
