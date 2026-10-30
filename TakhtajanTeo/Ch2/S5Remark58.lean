import TakhtajanTeo.Ch2.S5Cor
import TakhtajanTeo.Ch2.PeriodGrunskyBounds
import TakhtajanTeo.Ch2.S2_MixedHook

/-!
# `remark_5_8` (`s5r58_`, 下属5, Program G): the Schottky locus `Π₀(T₀(1)) ⊂ 𝔇_∞⁰`

Host: new module `TakhtajanTeo/Ch2/S5Remark58.lean` (scouts `collaboration/下属6/R58_SCOUT.md`,
`collaboration/下属5/SCOUT_R58.md`). The target `s5r58_remark_5_8` has the statement of `remark_5_8`.
Let `b = grunsky (fsans μ) (gsans μ)`, `C = B1 b = kyns [μ]` (`s5c_kyns_eq`) and `D = B4 b`.

(⇒)
* F1 S1: the identity for `h = 1/f`. `G = exp(-mixed part)` comes from clause 4 of `IsGrunskyCoeff`. The Laurent
  coefficients of `1/f` are `b_{-m,-1}` (`∂_ζ` at `0`).
* F2 S3: the same for `g` at `∞`. The constant `e^{b₀₀}` cancels.
* F3 S2: `B = B2`, from `grunsky_unitary` and the symmetries. `D ∈ 𝔇_∞⁰` by `pgb_norm_lt_one.2`, `pgb_bounded` and
  `cor_2_9.2`. All `∑'` are row-`ℓ²` products, so they are summable.

(⇐) S1 alone suffices.
* Q1: `h = 1/z + Σ C_{m0}/√(m+1) z^{m+1}` is injective, since `exp ≠ 0`. `f = 1/h` is univalent and normalized, with
  mixed coefficients `C/√`.
* W-QD: `C ∈ 𝔇_∞⁰` gives Grunsky norm `κ = ‖C‖ < 1` (HS ⇒ compact, strict contraction). Then `f` has a q.c. extension
  to `ℂ` (Pommerenke 1975 Lem 9.9, 9.10, Thm 9.12 ⇒ bounded turning ⇒ `thm18_1` ⇒ q.c. reflection / welding ⇒ extension).
  This is the wall; its sub-interface comes after the forward module.
* Q4: the extension gives `μ` and `p = [μ]`. Then `fsans (out p) = f ∘` a Möbius normalization (`k24_normalize`),
  `B1` is invariant, so `kyns p = C`. Finally `p ∈ T01` by `s5c_cor_5_4`.

All `∑'` in the statement are absolutely summable on the stated domains: `C, D ∈ 𝔇_∞⁰` have bounded entries. They
are proved summable, not assumed.
-/

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal ComplexConjugate Classical Real

noncomputable section

namespace TakhtajanTeo

namespace Ch2

open LiZhongQC

/-- The row `m ↦ c_{m0} x^{m+1}` of a representation is summable at every `x ∈ 𝔻 \ {0}`. -/
theorem s5r58_row_summable {φ : ℂ → ℂ} {c : ℕ → ℕ → ℂ}
    (hrep : ∀ s ∈ unitDisc, ∀ t ∈ unitDisc, s ≠ 0 → t ≠ 0 → s ≠ t → ∃ M,
      HasSum (fun q : ℕ × ℕ => c q.1 q.2 * s ^ (q.1 + 1) * t ^ (q.2 + 1)) M ∧
      (φ s - φ t) * s * t = (s - t) * φ s * φ t * exp (-M))
    {x : ℂ} (hx : x ∈ unitDisc) (hx0 : x ≠ 0) :
    Summable (fun m : ℕ => c m 0 * x ^ (m + 1)) := by
  have hx1 : ‖x‖ < 1 := mem_ball_zero_iff.mp hx
  have hh : x / 2 ∈ unitDisc := mem_ball_zero_iff.mpr (by rw [norm_div]; norm_num; linarith [norm_nonneg x])
  have hh0 : x / 2 ≠ 0 := div_ne_zero hx0 two_ne_zero
  have hne : x ≠ x / 2 := by intro h; apply hx0; linear_combination 2 * h
  obtain ⟨M, hM, -⟩ := hrep x hx (x / 2) hh hx0 hh0 hne
  have h1 := hM.summable.prod_symm.prod_factor 0
  have h2 := h1.mul_right (x / 2)⁻¹
  refine h2.congr fun m => ?_
  simp only [Prod.swap_prod_mk, zero_add, pow_one]
  field_simp

/-- **Core of S1** (for any univalent normalized `φ` on `𝔻` with a mixed exponential representation `c`): the row
`c_{m0}` gives the Laurent coefficients of `1/φ`, and S1 holds. -/
theorem s5r58_core {φ : ℂ → ℂ} (hd : DifferentiableOn ℂ φ unitDisc) (hi : InjOn φ unitDisc) (h0 : φ 0 = 0)
    (h1 : deriv φ 0 = 1) {c : ℕ → ℕ → ℂ}
    (hrep : ∀ s ∈ unitDisc, ∀ t ∈ unitDisc, s ≠ 0 → t ≠ 0 → s ≠ t → ∃ M,
      HasSum (fun q : ℕ × ℕ => c q.1 q.2 * s ^ (q.1 + 1) * t ^ (q.2 + 1)) M ∧
      (φ s - φ t) * s * t = (s - t) * φ s * φ t * exp (-M)) :
    ∀ s ∈ unitDisc, ∀ t ∈ unitDisc, s ≠ 0 → t ≠ 0 → s ≠ t →
      1 + ∑' m : ℕ, c m 0 * ((s ^ (m + 1) - t ^ (m + 1)) / (s⁻¹ - t⁻¹)) =
        exp (-∑' q : ℕ × ℕ, c q.1 q.2 * s ^ (q.1 + 1) * t ^ (q.2 + 1)) := by
  have h0D : (0 : ℂ) ∈ unitDisc := mem_ball_self one_pos
  have hφ0 : ∀ x ∈ unitDisc, x ≠ 0 → φ x ≠ 0 := fun x hx hx0 h => hx0 (hi hx h0D (h.trans h0.symm))
  have hφd0 : HasDerivAt φ 1 0 := by
    rw [← h1]; exact (hd.differentiableAt (isOpen_ball.mem_nhds h0D)).hasDerivAt
  have hds : DifferentiableOn ℂ (dslope φ 0) unitDisc := (differentiableOn_dslope (isOpen_ball.mem_nhds h0D)).mpr hd
  set D : ℂ := deriv (dslope φ 0) 0 with hD
  have hDd : HasDerivAt (dslope φ 0) D 0 := (hds.differentiableAt (isOpen_ball.mem_nhds h0D)).hasDerivAt
  have hds0 : dslope φ 0 0 = 1 := by rw [dslope_same, h1]
  -- the Laurent coefficients of `1/φ`
  have hkey : ∀ x ∈ unitDisc, x ≠ 0 → ∑' m : ℕ, c m 0 * x ^ (m + 1) = 1 / φ x - 1 / x + D := by
    intro x hx hx0
    have hx1 : ‖x‖ < 1 := mem_ball_zero_iff.mp hx
    have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx0
    set r : ℝ := ‖x‖ / 2 with hr
    have hrpos : 0 < r := by positivity
    have hball : ∀ τ ∈ ball (0 : ℂ) r, τ ∈ unitDisc ∧ τ ≠ x := by
      intro τ hτ
      have hτr : ‖τ‖ < r := mem_ball_zero_iff.mp hτ
      refine ⟨mem_ball_zero_iff.mpr (by linarith), fun h => ?_⟩
      rw [h] at hτr; linarith
    set Mf : ℂ → ℂ := fun τ => ∑' q : ℕ × ℕ, c q.1 q.2 * x ^ (q.1 + 1) * τ ^ (q.2 + 1) with hMf
    set e : ℕ → ℂ := fun n => if n = 0 then 0 else ∑' m : ℕ, c m (n - 1) * x ^ (m + 1) with he
    have hser : ∀ τ ∈ ball (0 : ℂ) r, HasSum (fun n => τ ^ n • e n) (Mf τ) := by
      intro τ hτ
      by_cases hτ0 : τ = 0
      · subst hτ0
        have hM0 : Mf 0 = 0 := by simp [hMf]
        rw [hM0]
        convert hasSum_zero with n
        rcases n with _ | n <;> simp [he]
      · obtain ⟨hτD, hτx⟩ := hball τ hτ
        obtain ⟨M, hM, -⟩ := hrep x hx τ hτD hx0 hτ0 hτx.symm
        have hMeq : Mf τ = M := hM.tsum_eq
        rw [hMeq]
        have hsw := (Equiv.prodComm ℕ ℕ).hasSum_iff.mpr hM
        have hfib := hsw.prod_fiberwise fun n => (hM.summable.prod_symm.prod_factor n).hasSum
        have hfib' : HasSum (fun n : ℕ => τ ^ (n + 1) • e (n + 1)) M := by
          refine hfib.congr_fun fun n => ?_
          simp only [he, Nat.add_one_ne_zero, if_false, Nat.add_sub_cancel, smul_eq_mul, Function.comp_def,
            Equiv.prodComm_apply, Prod.swap_prod_mk]
          rw [← tsum_mul_left]
          refine tsum_congr fun m => ?_
          ring
        have h' : HasSum (fun n => τ ^ (n + 1) • e (n + 1)) (M - ∑ i ∈ Finset.range 1, τ ^ i • e i) := by
          convert hfib' using 1
          simp [he]
        exact (hasSum_nat_add_iff' 1).mp h'
    have hfps : HasFPowerSeriesAt Mf (FormalMultilinearSeries.ofScalars ℂ e) 0 := by
      apply hasFPowerSeriesAt_iff.mpr
      filter_upwards [ball_mem_nhds (0 : ℂ) hrpos] with τ hτ
      simpa only [FormalMultilinearSeries.coeff_ofScalars, zero_add] using hser τ hτ
    have hMd : HasDerivAt Mf (∑' m : ℕ, c m 0 * x ^ (m + 1)) 0 := by
      have := hfps.hasDerivAt
      simpa [FormalMultilinearSeries.ofScalars, he] using this
    have hM0 : Mf 0 = 0 := by simp [hMf]
    -- the kernel as an analytic function of `τ`
    set Q : ℂ → ℂ := fun τ => (φ x - φ τ) / (x - τ) with hQ
    have hQd : HasDerivAt Q ((φ x - x) / x ^ 2) 0 := by
      have h := ((hasDerivAt_const (0 : ℂ) (φ x)).sub hφd0).div ((hasDerivAt_const (0 : ℂ) x).sub
        (hasDerivAt_id (0 : ℂ))) (by simpa using hx0)
      refine h.congr_deriv ?_
      simp [h0]
      field_simp
      ring
    have hK : HasDerivAt (fun τ => x * Q τ * (dslope φ 0 τ)⁻¹ / φ x)
        (x * ((φ x - x) / x ^ 2 * (dslope φ 0 0)⁻¹ + Q 0 * (-D / dslope φ 0 0 ^ 2)) / φ x) 0 :=
      (((hQd.const_mul x).mul (hDd.inv (by rw [hds0]; exact one_ne_zero))).div_const (φ x)).congr_deriv
        (by simp only [Pi.inv_apply]; ring)
    have hE : HasDerivAt (fun τ => exp (-Mf τ)) (exp (-Mf 0) * -(∑' m : ℕ, c m 0 * x ^ (m + 1))) 0 :=
      (hMd.neg).cexp
    have hev : (fun τ => x * Q τ * (dslope φ 0 τ)⁻¹ / φ x) =ᶠ[𝓝 (0 : ℂ)] fun τ => exp (-Mf τ) := by
      filter_upwards [ball_mem_nhds (0 : ℂ) hrpos] with τ hτ
      by_cases hτ0 : τ = 0
      · subst hτ0
        rw [hM0, neg_zero, exp_zero, hds0]
        simp only [hQ, h0, sub_zero, inv_one, mul_one]
        field_simp [hφ0 x hx hx0]
      · obtain ⟨hτD, hτx⟩ := hball τ hτ
        obtain ⟨M, hM, hrel⟩ := hrep x hx τ hτD hx0 hτ0 hτx.symm
        rw [show Mf τ = M from hM.tsum_eq, dslope_of_ne _ hτ0, slope_def_field, h0, sub_zero, sub_zero]
        have hxτ : x - τ ≠ 0 := sub_ne_zero.mpr hτx.symm
        have hp1 := hφ0 x hx hx0
        have hp2 := hφ0 τ hτD hτ0
        simp only [hQ]
        field_simp
        linear_combination hrel
    have huniq := hK.unique (hE.congr_of_eventuallyEq hev)
    rw [hM0, neg_zero, exp_zero, one_mul, hds0] at huniq
    have hp1 := hφ0 x hx hx0
    have hq0 : Q 0 = φ x / x := by simp [hQ, h0]
    rw [hq0] at huniq
    have hA : (∑' m : ℕ, c m 0 * x ^ (m + 1)) =
        -(x * ((φ x - x) / x ^ 2 * 1⁻¹ + φ x / x * (-D / 1 ^ 2)) / φ x) := by
      linear_combination huniq
    rw [hA]
    field_simp
    ring
  -- assembly
  intro s hs t ht hs0 ht0 hst
  obtain ⟨M, hM, hrel⟩ := hrep s hs t ht hs0 ht0 hst
  rw [hM.tsum_eq]
  have hss := s5r58_row_summable hrep hs hs0
  have hts := s5r58_row_summable hrep ht ht0
  have hΔ : s⁻¹ - t⁻¹ ≠ 0 := by
    intro h; apply hst; have := sub_eq_zero.mp h; exact inv_injective this
  have hsplit : ∑' m : ℕ, c m 0 * ((s ^ (m + 1) - t ^ (m + 1)) / (s⁻¹ - t⁻¹)) =
      ((∑' m : ℕ, c m 0 * s ^ (m + 1)) - ∑' m : ℕ, c m 0 * t ^ (m + 1)) / (s⁻¹ - t⁻¹) := by
    rw [← hss.tsum_sub hts, ← tsum_div_const]
    refine tsum_congr fun m => ?_
    ring
  rw [hsplit, hkey s hs hs0, hkey t ht ht0]
  have hp1 := hφ0 s hs hs0
  have hp2 := hφ0 t ht ht0
  have hst' : s - t ≠ 0 := sub_ne_zero.mpr hst
  have hE : exp (-M) = (φ s - φ t) * s * t / ((s - t) * φ s * φ t) := by
    field_simp
    linear_combination -hrel
  rw [hE]
  field_simp
  ring

/-- `√(mn)`-weights cancel: `B₁/√((m+1)(n+1)) = b_{-(m+1),-(n+1)}`. -/
theorem s5r58_B1_div (b : ℤ → ℤ → ℂ) (m n : ℕ) :
    B1 b m n / (Real.sqrt ((m + 1) * (n + 1)) : ℂ) = b (-(m + 1 : ℤ)) (-(n + 1 : ℤ)) := by
  have h : (Real.sqrt ((m + 1) * (n + 1)) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_ne_zero'.mpr (by positivity))
  unfold B1
  field_simp

/-- `B₄/√((m+1)(n+1)) = b_{m+1,n+1}`. -/
theorem s5r58_B4_div (b : ℤ → ℤ → ℂ) (m n : ℕ) :
    B4 b m n / (Real.sqrt ((m + 1) * (n + 1)) : ℂ) = b (m + 1) (n + 1) := by
  have h : (Real.sqrt ((m + 1) * (n + 1)) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_ne_zero'.mpr (by positivity))
  unfold B4
  field_simp

/-- The `n = 0` column weight: `√((m+1)·1) = √(m+1)`. -/
theorem s5r58_sqrt_col (m : ℕ) : (Real.sqrt (m + 1) : ℂ) = (Real.sqrt ((m + 1) * ((0 : ℕ) + 1)) : ℂ) := by
  simp

/-- Clause 4 of `IsGrunskyCoeff`, with the pure terms removed: the mixed exponential representation of `f`. -/
theorem s5r58_mixed_rep {f g : ℂ → ℂ} {b : ℤ → ℤ → ℂ} (hb : IsGrunskyCoeff f g b) (hf0 : f 0 = 0) :
    ∀ s ∈ unitDisc, ∀ t ∈ unitDisc, s ≠ 0 → t ≠ 0 → s ≠ t → ∃ M,
      HasSum (fun q : ℕ × ℕ => b (-(q.1 + 1 : ℤ)) (-(q.2 + 1 : ℤ)) * s ^ (q.1 + 1) * t ^ (q.2 + 1)) M ∧
      (f s - f t) * s * t = (s - t) * f s * f t * exp (-M) := by
  intro s hs t ht hs0 ht0 hst
  have h0D : (0 : ℂ) ∈ unitDisc := mem_ball_self one_pos
  obtain ⟨S12, h12, e12⟩ := hb.2.2.2.1 s hs t ht hst
  obtain ⟨S10, h10, e10⟩ := hb.2.2.2.1 s hs 0 h0D hs0
  obtain ⟨S02, h02, e02⟩ := hb.2.2.2.1 0 h0D t ht ht0.symm
  set F : ℕ × ℕ → ℂ := fun p => b (-(p.1 : ℤ)) (-(p.2 : ℤ)) * s ^ p.1 * t ^ p.2 with hF
  have hδ : HasSum (fun p : ℕ × ℕ => if p = (0, 0) then b 0 0 else 0) (b 0 0) := hasSum_ite_eq _ _
  have hall := ((h12.sub h10).sub h02).add hδ
  set ι : ℕ × ℕ → ℕ × ℕ := fun q => (q.1 + 1, q.2 + 1) with hι
  have hinj : Function.Injective ι := by
    intro p q h
    simp only [hι, Prod.mk.injEq] at h
    exact Prod.ext (by omega) (by omega)
  have hcomb : ∀ p : ℕ × ℕ,
      (b (-(p.1 : ℤ)) (-(p.2 : ℤ)) * s ^ p.1 * t ^ p.2 - b (-(p.1 : ℤ)) (-(p.2 : ℤ)) * s ^ p.1 * 0 ^ p.2 -
        b (-(p.1 : ℤ)) (-(p.2 : ℤ)) * 0 ^ p.1 * t ^ p.2 + if p = (0, 0) then b 0 0 else 0) =
      if p.1 ≠ 0 ∧ p.2 ≠ 0 then F p else 0 := by
    rintro ⟨m, n⟩
    rcases Nat.eq_zero_or_pos m with rfl | hm <;> rcases Nat.eq_zero_or_pos n with rfl | hn <;>
      simp [hF, *, Nat.pos_iff_ne_zero.mp, zero_pow, Nat.ne_of_gt] <;> ring
  set M : ℂ := S12 - S10 - S02 + b 0 0 with hM
  have hsum : HasSum (fun p : ℕ × ℕ => if p.1 ≠ 0 ∧ p.2 ≠ 0 then F p else 0) M := by
    refine hall.congr_fun fun p => ?_
    rw [← hcomb p]
  have hsum' : HasSum ((fun p : ℕ × ℕ => if p.1 ≠ 0 ∧ p.2 ≠ 0 then F p else 0) ∘ ι) M := by
    refine (hinj.hasSum_iff ?_).mpr hsum
    rintro ⟨m, n⟩ hp
    by_cases h : m ≠ 0 ∧ n ≠ 0
    · exact absurd ⟨(m - 1, n - 1), by simp only [hι]; exact Prod.ext (by omega) (by omega)⟩ hp
    · simp [h]
  refine ⟨M, hsum'.congr_fun fun q => ?_, ?_⟩
  · simp only [Function.comp_apply, hι, hF, Nat.add_one_ne_zero, ne_eq, not_false_eq_true, and_self, if_true]
    push_cast
    ring_nf
  · have hst' : s - t ≠ 0 := sub_ne_zero.mpr hst
    rw [hf0, sub_zero, sub_zero] at e10
    rw [hf0, zero_sub, zero_sub, neg_div_neg_eq] at e02
    have hexp : exp (-M) * exp (b 0 0 - S10) * exp (b 0 0 - S02) = exp (b 0 0 - S12) := by
      rw [← Complex.exp_add, ← Complex.exp_add]
      congr 1
      rw [hM]
      ring
    rw [← e10, ← e02, ← e12] at hexp
    field_simp at hexp
    linear_combination -hexp

/-- **Stub F1.** S1 for `C = B₁(b)` of `[μ]`. -/
theorem s5r58_S1 {μ : LinfStar} (hμ : μ ∈ LinfStarBall) :
    ∀ z₁ ∈ unitDisc, ∀ z₂ ∈ unitDisc, z₁ ≠ 0 → z₂ ≠ 0 → z₁ ≠ z₂ →
      1 + ∑' m : ℕ, B1 (grunsky (fsans μ) (gsans μ)) m 0 / Real.sqrt (m + 1) *
          ((z₁ ^ (m + 1) - z₂ ^ (m + 1)) / (z₁⁻¹ - z₂⁻¹)) =
        exp (-∑' q : ℕ × ℕ, B1 (grunsky (fsans μ) (gsans μ)) q.1 q.2 / Real.sqrt ((q.1 + 1) * (q.2 + 1)) *
          z₁ ^ (q.1 + 1) * z₂ ^ (q.2 + 1)) := by
  have hpair := AppB.b8_welding_normalized_pair hμ
  obtain ⟨hfd, hfi, hf0, hf1, -, -⟩ := id hpair
  have hb := (grunsky_spec hpair).1
  have hcore := s5r58_core (c := fun m n => grunsky (fsans μ) (gsans μ) (-(m + 1 : ℤ)) (-(n + 1 : ℤ)))
    hfd hfi hf0 hf1 (s5r58_mixed_rep hb hf0)
  intro z₁ hz₁ z₂ hz₂ h1 h2 h12
  have h := hcore z₁ hz₁ z₂ hz₂ h1 h2 h12
  simp only [s5r58_sqrt_col, s5r58_B1_div]
  exact h

/-- **Stub F2.** S3 for `D = B₄(b)` of `[μ]`. -/
theorem s5r58_S3 {μ : LinfStar} (hμ : μ ∈ LinfStarBall) :
    ∀ z₁ ∈ unitDiscExterior, ∀ z₂ ∈ unitDiscExterior, z₁ ≠ z₂ →
      1 + ∑' m : ℕ, B4 (grunsky (fsans μ) (gsans μ)) m 0 / Real.sqrt (m + 1) *
          ((z₁ ^ (-(m + 1 : ℤ)) - z₂ ^ (-(m + 1 : ℤ))) / (z₁ - z₂)) =
        exp (-∑' q : ℕ × ℕ, B4 (grunsky (fsans μ) (gsans μ)) q.1 q.2 / Real.sqrt ((q.1 + 1) * (q.2 + 1)) *
          z₁ ^ (-(q.1 + 1 : ℤ)) * z₂ ^ (-(q.2 + 1 : ℤ))) := by
  have hpair := AppB.b8_welding_normalized_pair hμ
  obtain ⟨φ, b', hφd, hφi, hφ0, hφ1, hb'0, hder, hgφ⟩ := g1_inverted_exterior hpair
  have hb := (grunsky_spec hpair).1
  have hexpb : exp (grunsky (fsans μ) (gsans μ) 0 0) = b' := hb.1.trans hder
  have hinvD : ∀ s ∈ unitDisc, s ≠ 0 → 1 / s ∈ unitDiscExterior := by
    intro s hs hs0
    have hsn : ‖s‖ < 1 := mem_ball_zero_iff.mp hs
    have hpos : 0 < ‖s‖ := norm_pos_iff.mpr hs0
    show 1 < ‖1 / s‖
    rw [norm_div, norm_one, lt_div_iff₀ hpos]
    linarith
  have hrep : ∀ s ∈ unitDisc, ∀ t ∈ unitDisc, s ≠ 0 → t ≠ 0 → s ≠ t → ∃ M,
      HasSum (fun q : ℕ × ℕ => grunsky (fsans μ) (gsans μ) (q.1 + 1) (q.2 + 1) * s ^ (q.1 + 1) * t ^ (q.2 + 1)) M ∧
      (φ s - φ t) * s * t = (s - t) * φ s * φ t * exp (-M) := by
    intro s hs t ht hs0 ht0 hst
    have hne : 1 / s ≠ 1 / t := by
      intro h; apply hst; simpa using h
    obtain ⟨S, hS, he⟩ := hb.2.1 (1 / s) (hinvD s hs hs0) (1 / t) (hinvD t ht ht0) hne
    refine ⟨S, hS.congr_fun fun q => ?_, ?_⟩
    · simp only [g1_zpow_neg_succ, one_div, inv_inv]
    · have hφs : φ s ≠ 0 := fun h => hs0 (hφi hs (mem_ball_self one_pos) (h.trans hφ0.symm))
      have hφt : φ t ≠ 0 := fun h => ht0 (hφi ht (mem_ball_self one_pos) (h.trans hφ0.symm))
      have hst' : s - t ≠ 0 := sub_ne_zero.mpr hst
      rw [hgφ s hs hs0, hgφ t ht ht0, Complex.exp_sub, hexpb] at he
      field_simp at he
      have hE : exp S * exp (-S) = 1 := by rw [← Complex.exp_add]; simp
      linear_combination (-exp (-S)) * he - (φ s - φ t) * s * t * hE
  have hcore := s5r58_core (c := fun m n => grunsky (fsans μ) (gsans μ) (m + 1) (n + 1)) hφd hφi hφ0 hφ1 hrep
  intro z₁ hz₁ z₂ hz₂ h12
  have hz1 : 1 < ‖z₁‖ := hz₁
  have hz2 : 1 < ‖z₂‖ := hz₂
  have hz10 : z₁ ≠ 0 := by rintro rfl; simp at hz1; linarith
  have hz20 : z₂ ≠ 0 := by rintro rfl; simp at hz2; linarith
  have hD1 : z₁⁻¹ ∈ unitDisc := mem_ball_zero_iff.mpr (by rw [norm_inv]; exact inv_lt_one_of_one_lt₀ hz1)
  have hD2 : z₂⁻¹ ∈ unitDisc := mem_ball_zero_iff.mpr (by rw [norm_inv]; exact inv_lt_one_of_one_lt₀ hz2)
  have h := hcore z₁⁻¹ hD1 z₂⁻¹ hD2 (inv_ne_zero hz10) (inv_ne_zero hz20) (fun h => h12 (inv_injective h))
  rw [inv_inv, inv_inv] at h
  simp only [s5r58_sqrt_col, s5r58_B4_div, g1_zpow_neg_succ]
  exact h

/-- `Σ_k a_k b̄_k` converges for `a, b ∈ ℓ²`. -/
theorem s5r58_l2_mul {a b : ℕ → ℂ} (ha : IsL2 a) (hb : IsL2 b) : Summable (fun k => a k * conj (b k)) := by
  refine Summable.of_norm_bounded (ha.add hb) fun k => ?_
  rw [norm_mul, Complex.norm_conj]
  nlinarith [norm_nonneg (a k), norm_nonneg (b k), sq_nonneg (‖a k‖ - ‖b k‖)]

/-- `δ̄ = δ`. -/
theorem s5r58_conj_kron (m n : ℕ) : conj (kron m n) = kron m n := by
  unfold kron; split_ifs <;> simp

/-- **Stub F3.** S2 with `D = B₄(b)` and `B = B₂(b)`, for `[μ] ∈ T₀(1)`. -/
theorem s5r58_S2 {μ : LinfStar} (hμ : μ ∈ LinfStarBall) (hT : Phi ⟨μ, hμ⟩ ∈ T01) :
    B4 (grunsky (fsans μ) (gsans μ)) ∈ siegelDisk0 ∧ IsBoundedMat (B2 (grunsky (fsans μ) (gsans μ))) ∧
      (∀ m n, kron m n - (∑' k, B1 (grunsky (fsans μ) (gsans μ)) m k * conj (B1 (grunsky (fsans μ) (gsans μ)) k n)) =
        mulAdj (B2 (grunsky (fsans μ) (gsans μ))) (B2 (grunsky (fsans μ) (gsans μ))) m n) ∧
      ∀ m n, kron m n - (∑' k, B4 (grunsky (fsans μ) (gsans μ)) m k * conj (B4 (grunsky (fsans μ) (gsans μ)) k n)) =
        ∑' k, B2 (grunsky (fsans μ) (gsans μ)) k m * conj (B2 (grunsky (fsans μ) (gsans μ)) k n) := by
  have hpair := AppB.b8_welding_normalized_pair hμ
  obtain ⟨hsym, hcol1, hcol2, -⟩ := grunsky_unitary hpair (r22_complement_null hμ)
  have hB1 : IsBoundedMat (B1 (grunsky (fsans μ) (gsans μ))) := pgb_bounded hμ (by simp)
  have hB2 : IsBoundedMat (B2 (grunsky (fsans μ) (gsans μ))) := pgb_bounded hμ (by simp)
  have hB3 : IsBoundedMat (B3 (grunsky (fsans μ) (gsans μ))) := pgb_bounded hμ (by simp)
  have hB4 : IsBoundedMat (B4 (grunsky (fsans μ) (gsans μ))) := pgb_bounded hμ (by simp)
  -- `D = B₄ ∈ 𝔇_∞⁰`
  have hD : B4 (grunsky (fsans μ) (gsans μ)) ∈ siegelDisk0 := by
    have hn : ‖gopOp (B4 (grunsky (fsans μ) (gsans μ)))‖ < 1 := (pgb_norm_lt_one hμ).2
    refine ⟨⟨fun m n => (hsym m n).2.1, hB4, ?_⟩, ?_⟩
    · intro x hx hx0
      let X : ell2 := ⟨x, gop_mem_of_summable hx⟩
      have hX : X ≠ 0 := by
        intro h
        apply hx0
        funext n
        exact congrArg (fun y : ell2 => y n) h
      have ht : ‖gopOp (B4 (grunsky (fsans μ) (gsans μ))) X‖ < ‖X‖ :=
        (ContinuousLinearMap.le_opNorm _ X).trans_lt
          (by simpa using mul_lt_mul_of_pos_right hn (norm_pos_iff.mpr hX))
      have hs : ‖gopOp (B4 (grunsky (fsans μ) (gsans μ))) X‖ ^ 2 < ‖X‖ ^ 2 := by
        nlinarith [norm_nonneg (gopOp (B4 (grunsky (fsans μ) (gsans μ))) X)]
      simpa only [gop_norm_sq, pmb_apply hB4, sqSum, X] using hs
    · have hg : grunsky (fsans (Quotient.out (Phi ⟨μ, hμ⟩) : LinfStarBall))
          (gsans (Quotient.out (Phi ⟨μ, hμ⟩) : LinfStarBall)) = grunsky (fsans μ) (gsans μ) := by
        apply FB.fb_grunsky_class (Quotient.out (Phi ⟨μ, hμ⟩)).2 hμ
        exact Quotient.exact (Quotient.out_eq (Phi ⟨μ, hμ⟩))
      have h29 := ((cor_2_9 (Phi ⟨μ, hμ⟩)).2).mp hT
      rwa [hg] at h29
  refine ⟨hD, hB2, fun m n => ?_, fun m n => ?_⟩
  · have h := congrArg conj (hcol1 m n)
    rw [Complex.conj_tsum, s5r58_conj_kron] at h
    have hA : Summable fun k => B1 (grunsky (fsans μ) (gsans μ)) m k * conj (B1 (grunsky (fsans μ) (gsans μ)) k n) := by
      refine (s5r58_l2_mul (isBoundedMat_row_isL2 hB1 m) (isBoundedMat_row_isL2 hB1 n)).congr fun k => ?_
      rw [(hsym k n).1]
    have hB : Summable fun k => B2 (grunsky (fsans μ) (gsans μ)) m k * conj (B2 (grunsky (fsans μ) (gsans μ)) n k) :=
      s5r58_l2_mul (isBoundedMat_row_isL2 hB2 m) (isBoundedMat_row_isL2 hB2 n)
    have hsplit : (∑' k, conj (conj (B1 (grunsky (fsans μ) (gsans μ)) k m) * B1 (grunsky (fsans μ) (gsans μ)) k n +
        conj (B3 (grunsky (fsans μ) (gsans μ)) k m) * B3 (grunsky (fsans μ) (gsans μ)) k n)) =
        (∑' k, B1 (grunsky (fsans μ) (gsans μ)) m k * conj (B1 (grunsky (fsans μ) (gsans μ)) k n)) +
          ∑' k, B2 (grunsky (fsans μ) (gsans μ)) m k * conj (B2 (grunsky (fsans μ) (gsans μ)) n k) := by
      rw [← hA.tsum_add hB]
      refine tsum_congr fun k => ?_
      rw [map_add, map_mul, map_mul, Complex.conj_conj, Complex.conj_conj, (hsym k m).1, (hsym k m).2.2,
        (hsym k n).2.2]
    rw [hsplit] at h
    unfold mulAdj
    linear_combination -h
  · have h := congrArg conj (hcol2 m n)
    rw [Complex.conj_tsum, s5r58_conj_kron] at h
    have hA : Summable fun k => B4 (grunsky (fsans μ) (gsans μ)) m k * conj (B4 (grunsky (fsans μ) (gsans μ)) k n) := by
      refine (s5r58_l2_mul (isBoundedMat_row_isL2 hB4 m) (isBoundedMat_row_isL2 hB4 n)).congr fun k => ?_
      rw [(hsym k n).2.1]
    have hB : Summable fun k => B2 (grunsky (fsans μ) (gsans μ)) k m * conj (B2 (grunsky (fsans μ) (gsans μ)) k n) := by
      refine (s5r58_l2_mul (isBoundedMat_row_isL2 hB3 m) (isBoundedMat_row_isL2 hB3 n)).congr fun k => ?_
      rw [(hsym m k).2.2, (hsym n k).2.2]
    have hsplit : (∑' k, conj (conj (B2 (grunsky (fsans μ) (gsans μ)) k m) * B2 (grunsky (fsans μ) (gsans μ)) k n +
        conj (B4 (grunsky (fsans μ) (gsans μ)) k m) * B4 (grunsky (fsans μ) (gsans μ)) k n)) =
        (∑' k, B4 (grunsky (fsans μ) (gsans μ)) m k * conj (B4 (grunsky (fsans μ) (gsans μ)) k n)) +
          ∑' k, B2 (grunsky (fsans μ) (gsans μ)) k m * conj (B2 (grunsky (fsans μ) (gsans μ)) k n) := by
      rw [← hA.tsum_add hB]
      refine tsum_congr fun k => ?_
      rw [map_add, map_mul, map_mul, Complex.conj_conj, Complex.conj_conj, (hsym k m).2.1]
      ring
    rw [hsplit] at h
    linear_combination -h

/-- A Hilbert–Schmidt matrix has bounded `√`-weighted entries. -/
theorem s5r58_entry_bd {C : ℕ → ℕ → ℂ} (hC : C ∈ siegelDisk0) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ m n : ℕ, ‖C m n / (Real.sqrt ((m + 1) * (n + 1)) : ℂ)‖ ≤ K := by
  refine ⟨1 + ∑' q : ℕ × ℕ, ‖C q.1 q.2‖ ^ 2, by positivity, fun m n => ?_⟩
  have h1 : ‖C m n‖ ^ 2 ≤ ∑' q : ℕ × ℕ, ‖C q.1 q.2‖ ^ 2 :=
    hC.2.le_tsum (m, n) (fun j _ => by positivity)
  have hx : (1 : ℝ) ≤ (m + 1) * (n + 1) := by
    nlinarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m), (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have hs : (1 : ℝ) ≤ Real.sqrt ((m + 1) * (n + 1)) := by
    simpa using Real.sqrt_le_sqrt hx
  rw [norm_div, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _)]
  have h2 : ‖C m n‖ / Real.sqrt ((m + 1) * (n + 1)) ≤ ‖C m n‖ := div_le_self (norm_nonneg _) hs
  nlinarith [sq_nonneg (‖C m n‖ - 1), norm_nonneg (C m n)]

/-- The algebra of the `f = 1/(ψ - e)` representation. -/
theorem s5r58_alg {u v z₁ z₂ : ℂ} (hu : u ≠ 0) (hv : v ≠ 0) (h1 : z₁ ≠ 0) (h2 : z₂ ≠ 0)
    (hd : z₁⁻¹ - z₂⁻¹ ≠ 0) :
    (u⁻¹ - v⁻¹) * z₁ * z₂ = (z₁ - z₂) * u⁻¹ * v⁻¹ * ((u - v) / (z₁⁻¹ - z₂⁻¹)) := by
  have e1 := mul_inv_cancel₀ h1
  have e2 := mul_inv_cancel₀ h2
  have eu := mul_inv_cancel₀ hu
  have ev := mul_inv_cancel₀ hv
  have hk : z₁ - z₂ = -(z₁ * z₂) * (z₁⁻¹ - z₂⁻¹) := by linear_combination z₂ * e1 - z₁ * e2
  have hk2 : (z₁ - z₂) / (z₁⁻¹ - z₂⁻¹) = -(z₁ * z₂) := by rw [hk, mul_div_assoc, div_self hd, mul_one]
  have huv : u⁻¹ - v⁻¹ = (v - u) * u⁻¹ * v⁻¹ := by linear_combination v⁻¹ * eu - u⁻¹ * ev
  rw [huv, show (z₁ - z₂) * u⁻¹ * v⁻¹ * ((u - v) / (z₁⁻¹ - z₂⁻¹)) =
    (z₁ - z₂) / (z₁⁻¹ - z₂⁻¹) * (u⁻¹ * v⁻¹ * (u - v)) by ring, hk2]
  ring

/-- **Stub Q1.** S1 for `C ∈ 𝔇_∞⁰` defines a univalent normalized `f` on `𝔻` whose mixed Grunsky coefficients are
`C/√`. -/
theorem s5r58_f_of_S1 {C : ℕ → ℕ → ℂ} (hC : C ∈ siegelDisk0)
    (hS1 : ∀ z₁ ∈ unitDisc, ∀ z₂ ∈ unitDisc, z₁ ≠ 0 → z₂ ≠ 0 → z₁ ≠ z₂ →
      1 + ∑' m : ℕ, C m 0 / Real.sqrt (m + 1) * ((z₁ ^ (m + 1) - z₂ ^ (m + 1)) / (z₁⁻¹ - z₂⁻¹)) =
        exp (-∑' q : ℕ × ℕ, C q.1 q.2 / Real.sqrt ((q.1 + 1) * (q.2 + 1)) * z₁ ^ (q.1 + 1) * z₂ ^ (q.2 + 1))) :
    ∃ f : ℂ → ℂ, DifferentiableOn ℂ f unitDisc ∧ InjOn f unitDisc ∧ f 0 = 0 ∧ deriv f 0 = 1 ∧
      ∀ z₁ ∈ unitDisc, ∀ z₂ ∈ unitDisc, z₁ ≠ 0 → z₂ ≠ 0 → z₁ ≠ z₂ → ∃ S,
        HasSum (fun q : ℕ × ℕ => C q.1 q.2 / Real.sqrt ((q.1 + 1) * (q.2 + 1)) * z₁ ^ (q.1 + 1) * z₂ ^ (q.2 + 1)) S ∧
        (f z₁ - f z₂) * z₁ * z₂ = (z₁ - z₂) * f z₁ * f z₂ * exp (-S) := by
  obtain ⟨K, hK0, hK⟩ := s5r58_entry_bd hC
  have hK' : ∀ m : ℕ, ‖C m 0 / (Real.sqrt (m + 1) : ℂ)‖ ≤ K := fun m => by
    rw [s5r58_sqrt_col]; exact hK m 0
  have hDo : IsOpen unitDisc := Metric.isOpen_ball
  have h0D : (0 : ℂ) ∈ unitDisc := mem_ball_self one_pos
  -- the column series `P(w) = Σ C_{m0}/√(m+1) w^{m+1}`
  have hsumP : ∀ w : ℂ, ‖w‖ < 1 → Summable fun m : ℕ => C m 0 / (Real.sqrt (m + 1) : ℂ) * w ^ (m + 1) := by
    intro w hw
    refine Summable.of_norm_bounded ((summable_geometric_of_lt_one (norm_nonneg w) hw).mul_left K) fun m => ?_
    rw [norm_mul, norm_pow]
    calc ‖C m 0 / (Real.sqrt (m + 1) : ℂ)‖ * ‖w‖ ^ (m + 1) ≤ K * (‖w‖ ^ m * 1) := by
          rw [pow_succ]
          exact mul_le_mul (hK' m) (mul_le_mul_of_nonneg_left hw.le (pow_nonneg (norm_nonneg _) _))
            (by positivity) hK0
      _ = K * ‖w‖ ^ m := by ring
  obtain ⟨P, hP⟩ : ∃ P : ℂ → ℂ, P = fun w => ∑' m : ℕ, C m 0 / (Real.sqrt (m + 1) : ℂ) * w ^ (m + 1) :=
    ⟨_, rfl⟩
  have hPd : DifferentiableOn ℂ P unitDisc := by
    intro z hz
    have hz' : ‖z‖ < 1 := mem_ball_zero_iff.mp hz
    have hr1 : (‖z‖ + 1) / 2 < 1 := by linarith
    have hr0 : 0 ≤ (‖z‖ + 1) / 2 := by positivity
    have hU : DifferentiableOn ℂ P (Metric.ball 0 ((‖z‖ + 1) / 2)) := by
      rw [hP]
      refine differentiableOn_tsum_of_summable_norm (F := fun m w => C m 0 / (Real.sqrt (m + 1) : ℂ) * w ^ (m + 1))
        (u := fun m => K * ((‖z‖ + 1) / 2) ^ m) ((summable_geometric_of_lt_one hr0 hr1).mul_left K)
        (fun m => by fun_prop) Metric.isOpen_ball (fun m w hw => ?_)
      have hw' : ‖w‖ ≤ (‖z‖ + 1) / 2 := (mem_ball_zero_iff.mp hw).le
      rw [norm_mul, norm_pow]
      calc ‖C m 0 / (Real.sqrt (m + 1) : ℂ)‖ * ‖w‖ ^ (m + 1) ≤ K * (((‖z‖ + 1) / 2) ^ m * 1) := by
            rw [pow_succ]
            exact mul_le_mul (hK' m) (mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hw' m) (hw'.trans hr1.le)
              (norm_nonneg _) (pow_nonneg hr0 _)) (by positivity) hK0
        _ = K * ((‖z‖ + 1) / 2) ^ m := by ring
    exact (hU.differentiableAt (Metric.isOpen_ball.mem_nhds (by rw [mem_ball_zero_iff]; linarith))).differentiableWithinAt
  have hdiff : ∀ s t : ℂ, ‖s‖ < 1 → ‖t‖ < 1 → ∀ d : ℂ,
      (∑' m : ℕ, C m 0 / (Real.sqrt (m + 1) : ℂ) * ((s ^ (m + 1) - t ^ (m + 1)) / d)) = (P s - P t) / d := by
    intro s t hs ht d
    rw [hP]
    dsimp only
    rw [← (hsumP s hs).tsum_sub (hsumP t ht), ← tsum_div_const]
    exact tsum_congr fun m => by ring
  -- `ψ(z) = 1/z + P(z)`, univalent on `𝔻 ∖ {0}` by S1
  obtain ⟨ψ, hψ⟩ : ∃ ψ : ℂ → ℂ, ψ = fun z => z⁻¹ + P z := ⟨_, rfl⟩
  have hq : ∀ s t : ℂ, s⁻¹ - t⁻¹ ≠ 0 → 1 + (P s - P t) / (s⁻¹ - t⁻¹) = (ψ s - ψ t) / (s⁻¹ - t⁻¹) := by
    intro s t hd
    rw [hψ]
    dsimp only
    rw [show s⁻¹ + P s - (t⁻¹ + P t) = (s⁻¹ - t⁻¹) + (P s - P t) by ring, add_div, div_self hd]
  have hinvne : ∀ s t : ℂ, s ≠ t → s⁻¹ - t⁻¹ ≠ 0 := fun s t h => sub_ne_zero.mpr fun h' => h (inv_injective h')
  have hS1' : ∀ s ∈ unitDisc, ∀ t ∈ unitDisc, s ≠ 0 → t ≠ 0 → s ≠ t →
      (ψ s - ψ t) / (s⁻¹ - t⁻¹) = exp (-∑' q : ℕ × ℕ, C q.1 q.2 / Real.sqrt ((q.1 + 1) * (q.2 + 1)) *
        s ^ (q.1 + 1) * t ^ (q.2 + 1)) := by
    intro s hs t ht hs0 ht0 hst
    have h := hS1 s hs t ht hs0 ht0 hst
    rw [hdiff s t (mem_ball_zero_iff.mp hs) (mem_ball_zero_iff.mp ht), hq s t (hinvne s t hst)] at h
    exact h
  have hψd : DifferentiableOn ℂ ψ (unitDisc \ {0}) := by
    rw [hψ]
    exact (differentiableOn_id.inv fun z hz => hz.2).add (hPd.mono sdiff_subset)
  have hψi : InjOn ψ (unitDisc \ {0}) := by
    intro s hs t ht hst
    by_contra hne
    have h := hS1' s hs.1 t ht.1 hs.2 ht.2 hne
    rw [hst, sub_self, zero_div] at h
    exact Complex.exp_ne_zero _ h.symm
  -- an omitted value `e` of `ψ` (Liouville); `ψ` itself may vanish in `𝔻`
  obtain ⟨e, he⟩ := knr_exists_omitted (hDo.sdiff isClosed_singleton) sdiff_subset hψd hψi
  have hne : ∀ z ∈ unitDisc, z ≠ 0 → ψ z - e ≠ 0 := fun z hz hz0 => sub_ne_zero.mpr (he z ⟨hz, hz0⟩)
  obtain ⟨Dn, hDn⟩ : ∃ Dn : ℂ → ℂ, Dn = fun z => 1 + z * P z - e * z := ⟨_, rfl⟩
  have hD0 : Dn 0 = 1 := by simp only [hDn]; ring
  have hDz : ∀ z : ℂ, z ≠ 0 → Dn z = z * (ψ z - e) := by
    intro z hz0
    have := mul_inv_cancel₀ hz0
    simp only [hDn, hψ]
    linear_combination -this
  have hDne : ∀ z ∈ unitDisc, Dn z ≠ 0 := by
    intro z hz
    by_cases hz0 : z = 0
    · rw [hz0, hD0]; exact one_ne_zero
    · rw [hDz z hz0]; exact mul_ne_zero hz0 (hne z hz hz0)
  have hDd : DifferentiableOn ℂ Dn unitDisc := by
    rw [hDn]
    exact ((differentiableOn_const 1).add (differentiableOn_id.mul hPd)).sub
      ((differentiableOn_const e).mul differentiableOn_id)
  have hfψ : ∀ z : ℂ, z ≠ 0 → z / Dn z = (ψ z - e)⁻¹ := by
    intro z hz0
    rw [hDz z hz0, ← div_div, div_self hz0, one_div]
  -- `f = z / (1 + z P(z) - e z) = 1/(ψ - e)`: the denominator never vanishes on `𝔻`
  refine ⟨fun z => z / Dn z, differentiableOn_id.div hDd hDne, ?_, zero_div _, ?_, ?_⟩
  · intro z hz w hw hzw
    simp only at hzw
    by_cases hz0 : z = 0
    · rw [hz0, zero_div, eq_comm, div_eq_zero_iff] at hzw
      rw [hz0]
      exact (hzw.resolve_right (hDne w hw)).symm
    by_cases hw0 : w = 0
    · rw [hw0, zero_div, div_eq_zero_iff] at hzw
      exact absurd (hzw.resolve_right (hDne z hz)) hz0
    rw [hfψ z hz0, hfψ w hw0] at hzw
    exact hψi ⟨hz, hz0⟩ ⟨hw, hw0⟩ (sub_left_inj.mp (inv_injective hzw))
  · have hDA : DifferentiableAt ℂ Dn 0 := hDd.differentiableAt (hDo.mem_nhds h0D)
    have h : HasDerivAt (fun z => z / Dn z) _ 0 :=
      (hasDerivAt_id' (0 : ℂ)).div hDA.hasDerivAt (by rw [hD0]; exact one_ne_zero)
    rw [h.deriv, hD0]
    simp
  · intro z₁ hz₁ z₂ hz₂ h1 h2 h12
    have hn1 : ‖z₁‖ < 1 := mem_ball_zero_iff.mp hz₁
    have hn2 : ‖z₂‖ < 1 := mem_ball_zero_iff.mp hz₂
    have hg : ∀ w : ℂ, ‖w‖ < 1 → Summable fun m : ℕ => ‖‖w‖ ^ (m + 1)‖ := by
      intro w hw
      exact ((summable_nat_add_iff 1).mpr (summable_geometric_of_lt_one (norm_nonneg w) hw)).congr
        fun m => (Real.norm_of_nonneg (pow_nonneg (norm_nonneg w) _)).symm
    have hsum := ((summable_mul_of_summable_norm (hg z₁ hn1) (hg z₂ hn2)).mul_left K)
    refine ⟨_, (Summable.of_norm_bounded hsum fun q => ?_).hasSum, ?_⟩
    · rw [norm_mul, norm_mul, norm_pow, norm_pow]
      have hq := hK q.1 q.2
      have p1 := pow_nonneg (norm_nonneg z₁) (q.1 + 1)
      have p2 := pow_nonneg (norm_nonneg z₂) (q.2 + 1)
      nlinarith [mul_nonneg (sub_nonneg.mpr hq) (mul_nonneg p1 p2)]
    · have h := hS1' z₁ hz₁ z₂ hz₂ h1 h2 h12
      rw [show ψ z₁ - ψ z₂ = (ψ z₁ - e) - (ψ z₂ - e) by ring] at h
      show (z₁ / Dn z₁ - z₂ / Dn z₂) * z₁ * z₂ = (z₁ - z₂) * (z₁ / Dn z₁) * (z₂ / Dn z₂) * _
      rw [hfψ z₁ h1, hfψ z₂ h2, ← h]
      exact s5r58_alg (hne z₁ hz₁ h1) (hne z₂ hz₂ h2) h1 h2 (hinvne z₁ z₂ h12)

/-- Cauchy–Schwarz for a square-summable row against `x ∈ ℓ²`. -/
theorem s5r58_row_cs {a : ℕ → ℂ} (ha : Summable fun n => ‖a n‖ ^ 2) (x : ell2) :
    ‖∑' n, a n * x n‖ ^ 2 ≤ (∑' n, ‖a n‖ ^ 2) * ‖x‖ ^ 2 := by
  let A : ell2 := ⟨fun n => conj (a n), gop_mem_of_summable (by simpa only [Complex.norm_conj] using ha)⟩
  have hin : inner ℂ A x = ∑' n, a n * x n := by
    rw [lp.inner_eq_tsum]
    refine tsum_congr fun n => ?_
    rw [gop_inner_apply]
    show conj (conj (a n)) * x n = _
    rw [Complex.conj_conj]
  have hA : ‖A‖ ^ 2 = ∑' n, ‖a n‖ ^ 2 := by
    rw [gop_norm_sq]
    exact tsum_congr fun n => by
      show ‖conj (a n)‖ ^ 2 = _
      rw [Complex.norm_conj]
  rw [← hin, ← hA, ← mul_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) (norm_inner_le_norm A x) 2

/-- `‖y‖²` of `y ∈ ℓ²` is a convergent sum. -/
theorem s5r58_ell2_summable (y : ell2) : Summable fun n => ‖y n‖ ^ 2 := by
  have h := lp.hasSum_norm (p := 2) (by norm_num) y
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using h.summable

/-- A bounded Hilbert–Schmidt matrix acts as a compact operator: the row truncations `Q_N T` are finite rank and
`‖T - Q_N T‖² ≤ Σ_{m ≥ N} Σ_n |C_{mn}|² → 0`. -/
theorem s5r58_gop_compact {C : ℕ → ℕ → ℂ} (hB : IsBoundedMat C)
    (hHS : Summable fun q : ℕ × ℕ => ‖C q.1 q.2‖ ^ 2) : IsCompactOperator (gopOp C) := by
  have hr : Summable fun m => ∑' n, ‖C m n‖ ^ 2 := hHS.prod
  obtain ⟨F, hF⟩ : ∃ F : ℕ → (ell2 →L[ℂ] ell2), F = fun N => ∑ m ∈ Finset.range N,
      (ContinuousLinearMap.toSpanSingleton ℂ (lp.single 2 m (1 : ℂ))).comp
        ((lp.evalCLM ℂ (fun _ : ℕ => ℂ) 2 m).comp (gopOp C)) := ⟨_, rfl⟩
  have hterm : ∀ k : ℕ, IsCompactOperator ⇑((ContinuousLinearMap.toSpanSingleton ℂ
      (lp.single (E := fun _ : ℕ => ℂ) 2 k (1 : ℂ))).comp
      ((lp.evalCLM ℂ (fun _ : ℕ => ℂ) 2 k).comp (gopOp C))) := fun k => by
    rw [ContinuousLinearMap.coe_comp]
    exact (isCompactOperator_of_locallyCompactSpace_dom _).clm_comp _
  have hFc : ∀ N, IsCompactOperator (F N) := by
    intro N
    rw [hF]
    dsimp only
    induction N with
    | zero => rw [Finset.sum_range_zero]; exact isCompactOperator_zero
    | succ N ih =>
      rw [Finset.sum_range_succ]
      exact IsCompactOperator.add ih (hterm N)
  have hFapp : ∀ N (x : ell2) (m : ℕ), (F N x) m = if m < N then gopOp C x m else 0 := by
    intro N x m
    have hev : ∀ (i : ℕ) (y : ell2), lp.evalCLM ℂ (fun _ : ℕ => ℂ) 2 i y = y i := fun i y => rfl
    rw [hF]
    simp only [ContinuousLinearMap.sum_apply, lp.coeFn_sum, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.toSpanSingleton_apply, hev, lp.coeFn_smul]
    rw [Finset.sum_apply]
    simp [lp.single_apply, Pi.single_apply]
  have hrow : ∀ (x : ell2) (m : ℕ), ‖gopOp C x m‖ ^ 2 ≤ (∑' n, ‖C m n‖ ^ 2) * ‖x‖ ^ 2 := by
    intro x m
    rw [pmb_apply hB]
    exact s5r58_row_cs (isBoundedMat_row_isL2 hB m) x
  have hbd : ∀ N (x : ell2), ‖(gopOp C - F N) x‖ ^ 2 ≤ (∑' k, ∑' n, ‖C (k + N) n‖ ^ 2) * ‖x‖ ^ 2 := by
    intro N x
    have hrn : ∀ m, 0 ≤ (∑' n, ‖C m n‖ ^ 2) * ‖x‖ ^ 2 :=
      fun m => mul_nonneg (tsum_nonneg fun n => by positivity) (by positivity)
    have hg : Summable fun m => if m < N then (0 : ℝ) else (∑' n, ‖C m n‖ ^ 2) * ‖x‖ ^ 2 :=
      Summable.of_nonneg_of_le (fun m => by split_ifs; exacts [le_rfl, hrn m])
        (fun m => by split_ifs; exacts [hrn m, le_rfl]) (hr.mul_right _)
    have e : ∀ m, ((gopOp C - F N) x) m = if m < N then 0 else gopOp C x m := by
      intro m
      rw [sub_apply, lp.coeFn_sub, Pi.sub_apply, hFapp]
      split_ifs <;> simp
    rw [gop_norm_sq]
    calc ∑' m, ‖((gopOp C - F N) x) m‖ ^ 2
        ≤ ∑' m, (if m < N then (0 : ℝ) else (∑' n, ‖C m n‖ ^ 2) * ‖x‖ ^ 2) := by
          refine Summable.tsum_le_tsum (fun m => ?_) (s5r58_ell2_summable _) hg
          rw [e]
          split_ifs
          · simp
          · exact hrow x m
      _ = ∑' k, (if k + N < N then (0 : ℝ) else (∑' n, ‖C (k + N) n‖ ^ 2) * ‖x‖ ^ 2) := by
          rw [← hg.sum_add_tsum_nat_add N, Finset.sum_eq_zero (fun i hi => by
            rw [if_pos (Finset.mem_range.mp hi)]), zero_add]
      _ = (∑' k, ∑' n, ‖C (k + N) n‖ ^ 2) * ‖x‖ ^ 2 := by
          rw [← tsum_mul_right]
          exact tsum_congr fun k => by rw [if_neg (by omega)]
  have htail : Tendsto (fun N => Real.sqrt (∑' k, ∑' n, ‖C (k + N) n‖ ^ 2)) atTop (𝓝 0) := by
    have h := (Real.continuous_sqrt.tendsto 0).comp (tendsto_sum_nat_add fun m => ∑' n, ‖C m n‖ ^ 2)
    simpa only [Real.sqrt_zero, Function.comp_def] using h
  have hlim : Tendsto F atTop (𝓝 (gopOp C)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun N => norm_nonneg _) (fun N => ?_) htail
    rw [norm_sub_rev]
    refine ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _) fun x => ?_
    have h := hbd N x
    have hs : (Real.sqrt (∑' k, ∑' n, ‖C (k + N) n‖ ^ 2) * ‖x‖) ^ 2 =
        (∑' k, ∑' n, ‖C (k + N) n‖ ^ 2) * ‖x‖ ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (tsum_nonneg fun k => tsum_nonneg fun n => by positivity)]
    rw [← hs] at h
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp h
  exact isCompactOperator_of_tendsto hlim (Eventually.of_forall hFc)

/-- The weighted geometric sequence `z^{m+1}/√(m+1)` is in `ℓ²` for `|z| < 1`. -/
theorem s5r58_geom_ell2 {z : ℂ} (hz : ‖z‖ < 1) :
    Summable fun m : ℕ => ‖z ^ (m + 1) / (Real.sqrt (m + 1) : ℂ)‖ ^ 2 := by
  have hg : Summable fun m : ℕ => (‖z‖ ^ 2) ^ (m + 1) :=
    (summable_nat_add_iff 1).mpr (summable_geometric_of_lt_one (by positivity)
      (by nlinarith [norm_nonneg z]))
  refine Summable.of_nonneg_of_le (fun m => by positivity) (fun m => ?_) hg
  have hs : (1 : ℝ) ≤ Real.sqrt (m + 1) := by
    simpa using Real.sqrt_le_sqrt (by linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)] : (1 : ℝ) ≤ m + 1)
  rw [norm_div, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _), norm_pow]
  calc (‖z‖ ^ (m + 1) / Real.sqrt (m + 1)) ^ 2 ≤ (‖z‖ ^ (m + 1)) ^ 2 := by
        gcongr
        exact div_le_self (by positivity) hs
    _ = (‖z‖ ^ 2) ^ (m + 1) := by ring

/-- `Σ_m \overline{z^{m+1}/√(m+1)} · w^{m+1}/√(m+1) = -log(1 - z̄ w)`. -/
theorem s5r58_inner_geom {z w : ℂ} (hz : ‖z‖ < 1) (hw : ‖w‖ < 1) :
    HasSum (fun m : ℕ => conj (z ^ (m + 1) / (Real.sqrt (m + 1) : ℂ)) * (w ^ (m + 1) / (Real.sqrt (m + 1) : ℂ)))
      (-log (1 - conj z * w)) := by
  have hzw : ‖conj z * w‖ < 1 := by
    rw [norm_mul, Complex.norm_conj]; nlinarith [norm_nonneg z, norm_nonneg w]
  refine (Complex.hasSum_taylorSeries_neg_log' hzw).congr_fun fun m => ?_
  have hs : ((Real.sqrt (m + 1) : ℂ)) * (Real.sqrt (m + 1) : ℂ) = (m : ℂ) + 1 := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by positivity)]; push_cast; ring
  have hs0 : (Real.sqrt (m + 1) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_ne_zero'.mpr (by positivity))
  rw [map_div₀, Complex.conj_ofReal, map_pow, div_mul_div_comm, hs, mul_pow]

/-- Entries of a bounded matrix with `‖C‖ ≤ κ` are at most `κ`. -/
theorem s5r58_entry_le {C : ℕ → ℕ → ℂ} (hB : IsBoundedMat C) {κ : ℝ} (hκ : 0 ≤ κ)
    (hCκ : ∀ x : ℕ → ℂ, IsL2 x → sqSum (matApply C x) ≤ κ ^ 2 * sqSum x) (m n : ℕ) : ‖C m n‖ ≤ κ := by
  classical
  let x : ℕ → ℂ := fun k => if k = n then 1 else 0
  have hx : IsL2 x := summable_of_ne_finset_zero (s := {n}) fun k hk => by
    simp [x, Finset.mem_singleton.not.mp hk]
  have hax : ∀ i, matApply C x i = C i n := fun i => by
    show ∑' k, C i k * x k = _
    simp only [x, mul_ite, mul_one, mul_zero]
    exact tsum_ite_eq n _
  have hsx : sqSum x = 1 := by
    show ∑' k, ‖x k‖ ^ 2 = 1
    simp only [x, apply_ite (fun c : ℂ => ‖c‖ ^ 2), norm_one, one_pow, norm_zero, ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true, zero_pow]
    exact tsum_ite_eq n _
  obtain ⟨K, hK⟩ := hB
  have hL := (hK x hx).1
  have h1 : ‖C m n‖ ^ 2 ≤ sqSum (matApply C x) := by
    show ‖C m n‖ ^ 2 ≤ ∑' k, ‖matApply C x k‖ ^ 2
    rw [← hax m]
    exact hL.le_tsum m (fun j _ => by positivity)
  have h2 := h1.trans (hCκ x hx)
  rw [hsx, mul_one] at h2
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) hκ two_ne_zero).mp h2

/-- The mixed series as a bilinear form: `S(z,w) = ⟨\bar V_z, C V_w⟩`, `V_z = (z^{m+1}/√(m+1))_m`. -/
theorem s5r58_S_eq_inner {C : ℕ → ℕ → ℂ} (hB : IsBoundedMat C) {K : ℝ} (hK : ∀ m n, ‖C m n‖ ≤ K)
    {z w : ℂ} (hz : ‖z‖ < 1) (hw : ‖w‖ < 1) :
    (∑' q : ℕ × ℕ, C q.1 q.2 / Real.sqrt ((q.1 + 1) * (q.2 + 1)) * z ^ (q.1 + 1) * w ^ (q.2 + 1)) =
      inner ℂ (star (⟨fun m => z ^ (m + 1) / (Real.sqrt (m + 1) : ℂ), gop_mem_of_summable (s5r58_geom_ell2 hz)⟩ : ell2))
        (gopOp C ⟨fun m => w ^ (m + 1) / (Real.sqrt (m + 1) : ℂ), gop_mem_of_summable (s5r58_geom_ell2 hw)⟩) := by
  have hgn : ∀ u : ℂ, ‖u‖ < 1 → Summable fun m : ℕ => ‖‖u‖ ^ (m + 1)‖ := fun u hu =>
    ((summable_nat_add_iff 1).mpr (summable_geometric_of_lt_one (norm_nonneg u) hu)).congr
      fun m => (Real.norm_of_nonneg (pow_nonneg (norm_nonneg u) _)).symm
  have hK0 : 0 ≤ K := (norm_nonneg _).trans (hK 0 0)
  have hsq1 : ∀ k : ℕ, (1 : ℝ) ≤ Real.sqrt (k + 1) := fun k => by
    simpa using Real.sqrt_le_sqrt (by linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)] : (1 : ℝ) ≤ k + 1)
  have hsplit : ∀ m n : ℕ, (Real.sqrt ((m + 1) * (n + 1)) : ℂ) = (Real.sqrt (m + 1) : ℂ) * (Real.sqrt (n + 1) : ℂ) :=
    fun m n => by rw [Real.sqrt_mul (by positivity), Complex.ofReal_mul]
  have hne : ∀ k : ℕ, (Real.sqrt (k + 1) : ℂ) ≠ 0 := fun k =>
    Complex.ofReal_ne_zero.mpr (Real.sqrt_ne_zero'.mpr (by positivity))
  have hsum : Summable fun q : ℕ × ℕ =>
      C q.1 q.2 / Real.sqrt ((q.1 + 1) * (q.2 + 1)) * z ^ (q.1 + 1) * w ^ (q.2 + 1) := by
    refine Summable.of_norm_bounded ((summable_mul_of_summable_norm (hgn z hz) (hgn w hw)).mul_left K) fun q => ?_
    rw [norm_mul, norm_mul, norm_pow, norm_pow, norm_div, Complex.norm_real,
      Real.norm_of_nonneg (Real.sqrt_nonneg _)]
    have hs : (1 : ℝ) ≤ Real.sqrt ((q.1 + 1) * (q.2 + 1)) := by
      rw [Real.sqrt_mul (by positivity)]
      nlinarith [hsq1 q.1, hsq1 q.2]
    have h1 : ‖C q.1 q.2‖ / Real.sqrt ((q.1 + 1) * (q.2 + 1)) ≤ K :=
      (div_le_self (norm_nonneg _) hs).trans (hK _ _)
    calc ‖C q.1 q.2‖ / Real.sqrt ((q.1 + 1) * (q.2 + 1)) * ‖z‖ ^ (q.1 + 1) * ‖w‖ ^ (q.2 + 1)
        ≤ K * ‖z‖ ^ (q.1 + 1) * ‖w‖ ^ (q.2 + 1) := by gcongr
      _ = K * (‖z‖ ^ (q.1 + 1) * ‖w‖ ^ (q.2 + 1)) := by ring
  rw [hsum.tsum_prod, lp.inner_eq_tsum]
  refine tsum_congr fun m => ?_
  rw [gop_inner_apply, pmb_apply hB, lp.star_apply]
  show _ = conj (star (z ^ (m + 1) / (Real.sqrt (m + 1) : ℂ))) *
    ∑' n, C m n * (w ^ (n + 1) / (Real.sqrt (n + 1) : ℂ))
  rw [Complex.star_def, Complex.conj_conj, ← tsum_mul_left]
  refine tsum_congr fun n => ?_
  rw [hsplit]
  ring

/-- The mixed series `w ↦ S(z, w)` is continuous on every closed disc `|w| ≤ ρ < 1` (bounded entries). -/
theorem s5r58_S_contOn {C : ℕ → ℕ → ℂ} {K : ℝ} (hK : ∀ m n, ‖C m n‖ ≤ K) {z : ℂ} (hz : ‖z‖ < 1)
    {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ : ρ < 1) :
    ContinuousOn (fun w : ℂ => ∑' q : ℕ × ℕ, C q.1 q.2 / Real.sqrt ((q.1 + 1) * (q.2 + 1)) * z ^ (q.1 + 1) *
      w ^ (q.2 + 1)) (closedBall 0 ρ) := by
  have hgz : Summable fun m : ℕ => ‖‖z‖ ^ (m + 1)‖ :=
    ((summable_nat_add_iff 1).mpr (summable_geometric_of_lt_one (norm_nonneg z) hz)).congr
      fun m => (Real.norm_of_nonneg (pow_nonneg (norm_nonneg z) _)).symm
  have hgρ : Summable fun m : ℕ => ‖ρ ^ (m + 1)‖ :=
    ((summable_nat_add_iff 1).mpr (summable_geometric_of_lt_one hρ0 hρ)).congr
      fun m => (Real.norm_of_nonneg (pow_nonneg hρ0 _)).symm
  have hsq1 : ∀ k : ℕ, (1 : ℝ) ≤ Real.sqrt (k + 1) := fun k => by
    simpa using Real.sqrt_le_sqrt (by linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)] : (1 : ℝ) ≤ k + 1)
  refine continuousOn_tsum (u := fun q : ℕ × ℕ => K * (‖z‖ ^ (q.1 + 1) * ρ ^ (q.2 + 1)))
    (fun q => by fun_prop) ((summable_mul_of_summable_norm hgz hgρ).mul_left K) fun q w hw => ?_
  have hw' : ‖w‖ ≤ ρ := mem_closedBall_zero_iff.mp hw
  rw [norm_mul, norm_mul, norm_pow, norm_pow, norm_div, Complex.norm_real,
    Real.norm_of_nonneg (Real.sqrt_nonneg _)]
  have hs : (1 : ℝ) ≤ Real.sqrt ((q.1 + 1) * (q.2 + 1)) := by
    rw [Real.sqrt_mul (by positivity)]
    nlinarith [hsq1 q.1, hsq1 q.2]
  have h1 : ‖C q.1 q.2‖ / Real.sqrt ((q.1 + 1) * (q.2 + 1)) ≤ K :=
    (div_le_self (norm_nonneg _) hs).trans (hK _ _)
  have h2 : ‖w‖ ^ (q.2 + 1) ≤ ρ ^ (q.2 + 1) := pow_le_pow_left₀ (norm_nonneg _) hw' _
  calc ‖C q.1 q.2‖ / Real.sqrt ((q.1 + 1) * (q.2 + 1)) * ‖z‖ ^ (q.1 + 1) * ‖w‖ ^ (q.2 + 1)
      ≤ K * ‖z‖ ^ (q.1 + 1) * ρ ^ (q.2 + 1) :=
        mul_le_mul (mul_le_mul_of_nonneg_right h1 (by positivity)) h2 (by positivity)
          (mul_nonneg ((norm_nonneg _).trans (hK 0 0)) (by positivity))
    _ = K * (‖z‖ ^ (q.1 + 1) * ρ ^ (q.2 + 1)) := by ring

/-- The derivative of `1/f` from the mixed representation: `(1/f)'(z) = -z⁻² e^{-S(z,z)}`
(`1/f(w) - 1/f(z) = (1/w - 1/z) e^{-S(z,w)}`, and `S` is continuous). -/
theorem s5r58_psi_deriv {C : ℕ → ℕ → ℂ} {K : ℝ} (hK : ∀ m n, ‖C m n‖ ≤ K) {f : ℂ → ℂ}
    (hfd : DifferentiableOn ℂ f unitDisc) (hfi : InjOn f unitDisc) (hf0 : f 0 = 0)
    (hrep : ∀ z₁ ∈ unitDisc, ∀ z₂ ∈ unitDisc, z₁ ≠ 0 → z₂ ≠ 0 → z₁ ≠ z₂ → ∃ S,
      HasSum (fun q : ℕ × ℕ => C q.1 q.2 / Real.sqrt ((q.1 + 1) * (q.2 + 1)) * z₁ ^ (q.1 + 1) * z₂ ^ (q.2 + 1)) S ∧
      (f z₁ - f z₂) * z₁ * z₂ = (z₁ - z₂) * f z₁ * f z₂ * exp (-S))
    {z : ℂ} (hz : z ∈ unitDisc) (hz0 : z ≠ 0) :
    HasDerivAt (fun w => (f w)⁻¹) (-(z * z)⁻¹ * exp (-∑' q : ℕ × ℕ,
      C q.1 q.2 / Real.sqrt ((q.1 + 1) * (q.2 + 1)) * z ^ (q.1 + 1) * z ^ (q.2 + 1))) z := by
  have hO : IsOpen unitDisc := Metric.isOpen_ball
  have hz1 : ‖z‖ < 1 := mem_ball_zero_iff.mp hz
  have hfne : ∀ w ∈ unitDisc, w ≠ 0 → f w ≠ 0 := fun w hw hw0 h =>
    hw0 (hfi hw (Metric.mem_ball_self one_pos) (h.trans hf0.symm))
  have hd : HasDerivAt (fun w => (f w)⁻¹) (deriv (fun w => (f w)⁻¹) z) z :=
    (((hfd z hz).differentiableAt (hO.mem_nhds hz)).inv (hfne z hz hz0)).hasDerivAt
  obtain ⟨G, hG⟩ : ∃ G : ℂ → ℂ, G = fun w => -(z * w)⁻¹ * exp (-∑' q : ℕ × ℕ,
      C q.1 q.2 / Real.sqrt ((q.1 + 1) * (q.2 + 1)) * z ^ (q.1 + 1) * w ^ (q.2 + 1)) := ⟨_, rfl⟩
  have hρ0 : 0 ≤ (1 + ‖z‖) / 2 := by positivity
  have hρ1 : (1 + ‖z‖) / 2 < 1 := by linarith
  have hball : closedBall (0 : ℂ) ((1 + ‖z‖) / 2) ∈ 𝓝 z := by
    refine closedBall_mem_nhds_of_mem ?_
    rw [mem_ball_zero_iff]
    linarith [norm_nonneg z]
  have hSc := ((s5r58_S_contOn hK hz1 hρ0 hρ1).continuousAt hball)
  have hGc : ContinuousAt G z := by
    rw [hG]
    have hk : ContinuousAt (fun w : ℂ => z * w) z := continuousAt_const.mul continuousAt_id
    exact (hk.inv₀ (mul_ne_zero hz0 hz0)).neg.mul
      (Complex.continuous_exp.continuousAt.comp hSc.neg)
  have hev : slope (fun w => (f w)⁻¹) z =ᶠ[𝓝[≠] z] G := by
    have h1 : ∀ᶠ w in 𝓝[≠] z, w ∈ unitDisc := nhdsWithin_le_nhds (hO.mem_nhds hz)
    have h2 : ∀ᶠ w in 𝓝[≠] z, w ≠ 0 := nhdsWithin_le_nhds (isOpen_ne.mem_nhds hz0)
    have h3 : ∀ᶠ w in 𝓝[≠] z, w ≠ z := self_mem_nhdsWithin
    filter_upwards [h1, h2, h3] with w hw hw0 hwz
    obtain ⟨S, hS, heq⟩ := hrep z hz w hw hz0 hw0 (Ne.symm hwz)
    have hfz := hfne z hz hz0
    have hfw := hfne w hw hw0
    have key : (f w)⁻¹ - (f z)⁻¹ = (z - w) * exp (-S) / (z * w) := by
      rw [inv_sub_inv hfw hfz, div_eq_div_iff (mul_ne_zero hfw hfz) (mul_ne_zero hz0 hw0)]
      linear_combination heq
    have hwz' : w - z ≠ 0 := sub_ne_zero.mpr hwz
    rw [slope_def_field, key]
    simp only [hG]
    rw [hS.tsum_eq]
    first
      | (field_simp; ring)
      | field_simp
  have ht : Tendsto (slope (fun w => (f w)⁻¹) z) (𝓝[≠] z) (𝓝 (G z)) :=
    (hGc.tendsto.mono_left nhdsWithin_le_nhds).congr' hev.symm
  have heq := tendsto_nhds_unique hd.tendsto_slope ht
  rw [heq] at hd
  rw [hG] at hd
  exact hd

/-- `|e^{-S}| ≤ (1 - r)^{-κ}` when `|S| ≤ κ log (1/(1 - r²))` (the `n = 1` Golusin bound at `|z| = r`). -/
theorem s5r58_exp_bd {S : ℂ} {κ r : ℝ} (hκ : 0 ≤ κ) (hr0 : 0 ≤ r) (hr : r < 1)
    (hS : ‖S‖ ≤ κ * Real.log (1 / (1 - r ^ 2))) : ‖exp (-S)‖ ≤ (1 - r) ^ (-κ) := by
  have h1r : 0 < 1 - r := by linarith
  have h1r2 : 0 < 1 - r ^ 2 := by nlinarith
  rw [Complex.norm_exp, Complex.neg_re]
  have hre : -S.re ≤ ‖S‖ := (neg_le_abs _).trans (Complex.abs_re_le_norm S)
  have hle : 1 / (1 - r ^ 2) ≤ 1 / (1 - r) := one_div_le_one_div_of_le h1r (by nlinarith)
  have hlog : Real.log (1 / (1 - r ^ 2)) ≤ Real.log (1 / (1 - r)) := Real.log_le_log (by positivity) hle
  rw [Real.rpow_def_of_pos h1r]
  refine Real.exp_le_exp.mpr (hre.trans (hS.trans ?_))
  have hlog' : Real.log (1 / (1 - r)) = -Real.log (1 - r) := by rw [one_div, Real.log_inv]
  rw [hlog'] at hlog
  nlinarith [mul_le_mul_of_nonneg_left hlog hκ]

/-- Radial Hardy–Littlewood estimate: `|g'(z)| ≤ 4 (1 - |z|)^{-κ}` on `1/2 ≤ |z| < 1` gives
`|g(tu) - g(su)| ≤ 4/(1 - κ) (1 - s)^{1 - κ}` for `|u| = 1`, `1/2 ≤ s ≤ t < 1`. -/
theorem s5r58_radial {g : ℂ → ℂ} {κ : ℝ} (hκ1 : κ < 1)
    (hd : ∀ z : ℂ, 1 / 2 ≤ ‖z‖ → ‖z‖ < 1 → ∃ g', HasDerivAt g g' z ∧ ‖g'‖ ≤ 4 * (1 - ‖z‖) ^ (-κ))
    {u : ℂ} (hu : ‖u‖ = 1) {s t : ℝ} (hs : 1 / 2 ≤ s) (hst : s ≤ t) (ht : t < 1) :
    ‖g ((t : ℂ) * u) - g ((s : ℂ) * u)‖ ≤ 4 / (1 - κ) * (1 - s) ^ (1 - κ) := by
  choose! G hG hGb using hd
  have hn : ∀ x : ℝ, 0 ≤ x → ‖(x : ℂ) * u‖ = x := fun x hx => by
    rw [norm_mul, hu, mul_one, Complex.norm_real, Real.norm_of_nonneg hx]
  have hκ' : 0 < 1 - κ := by linarith
  have hder : ∀ x : ℝ, 1 / 2 ≤ x → x < 1 →
      HasDerivAt (fun y : ℝ => g ((y : ℂ) * u) - g ((s : ℂ) * u)) (G ((x : ℂ) * u) * u) x := by
    intro x hx1 hx2
    have hx0 : 0 ≤ x := by linarith
    have h1 : HasDerivAt g (G ((x : ℂ) * u)) ((x : ℂ) * u) :=
      hG _ (by rw [hn x hx0]; exact hx1) (by rw [hn x hx0]; exact hx2)
    have h2 : HasDerivAt (fun w : ℂ => g (w * u)) (G ((x : ℂ) * u) * u) (x : ℂ) :=
      h1.comp (x : ℂ) (hasDerivAt_mul_const u)
    exact h2.comp_ofReal.sub_const _
  have hBd : ∀ x : ℝ, x < 1 → HasDerivAt (fun y : ℝ => 4 / (1 - κ) * ((1 - s) ^ (1 - κ) - (1 - y) ^ (1 - κ)))
      (4 * (1 - x) ^ (-κ)) x := by
    intro x hx
    have h1 : HasDerivAt (fun y : ℝ => (1 - y) ^ (1 - κ)) (-1 * (1 - κ) * (1 - x) ^ (1 - κ - 1)) x :=
      ((hasDerivAt_id x).const_sub 1).rpow_const (Or.inl (sub_pos.mpr hx).ne')
    have h2 := (h1.const_sub ((1 - s) ^ (1 - κ))).const_mul (4 / (1 - κ))
    refine h2.congr_deriv ?_
    have hκne : 1 - κ ≠ 0 := hκ'.ne'
    rw [show 1 - κ - 1 = -κ by ring]
    first
      | (field_simp; ring)
      | field_simp
  have key := image_norm_le_of_norm_deriv_right_le_deriv_boundary'
    (f := fun y : ℝ => g ((y : ℂ) * u) - g ((s : ℂ) * u)) (a := s) (b := t)
    (f' := fun x => G ((x : ℂ) * u) * u)
    (B := fun y : ℝ => 4 / (1 - κ) * ((1 - s) ^ (1 - κ) - (1 - y) ^ (1 - κ)))
    (B' := fun x => 4 * (1 - x) ^ (-κ))
    (fun x hx => (hder x (hs.trans hx.1) (hx.2.trans_lt ht)).continuousAt.continuousWithinAt)
    (fun x hx => (hder x (hs.trans hx.1) (hx.2.trans ht)).hasDerivWithinAt)
    (by simp)
    (fun x hx => (hBd x (hx.2.trans_lt ht)).continuousAt.continuousWithinAt)
    (fun x hx => (hBd x (hx.2.trans ht)).hasDerivWithinAt)
    (fun x hx => by
      have hx0 : 0 ≤ x := by linarith [hx.1]
      show ‖G ((x : ℂ) * u) * u‖ ≤ 4 * (1 - x) ^ (-κ)
      rw [norm_mul, hu, mul_one]
      have := hGb ((x : ℂ) * u) (by rw [hn x hx0]; linarith [hx.1]) (by rw [hn x hx0]; linarith [hx.2])
      rwa [hn x hx0] at this)
    (show t ∈ Icc s t from ⟨hst, le_rfl⟩)
  refine key.trans ?_
  have h0 : 0 ≤ (1 - t) ^ (1 - κ) := Real.rpow_nonneg (by linarith) _
  have h4 : 0 < 4 / (1 - κ) := by positivity
  show 4 / (1 - κ) * ((1 - s) ^ (1 - κ) - (1 - t) ^ (1 - κ)) ≤ 4 / (1 - κ) * (1 - s) ^ (1 - κ)
  nlinarith [mul_nonneg h4.le h0]

/-- `∫_ρ^1 (1 - r)^{-κ} dr = (1 - ρ)^{1-κ}/(1 - κ)` for `κ < 1`. -/
theorem s5r58q_int_rpow {κ ρ : ℝ} (hκ1 : κ < 1) (hρ : ρ ≤ 1) :
    IntervalIntegrable (fun r : ℝ => (1 - r) ^ (-κ)) volume ρ 1 ∧
      ∫ r in ρ..1, (1 - r) ^ (-κ) = (1 - ρ) ^ (1 - κ) / (1 - κ) := by
  have hr : -1 < -κ := by linarith
  constructor
  · have h := (intervalIntegral.intervalIntegrable_rpow' (a := 1 - ρ) (b := 0) hr).comp_sub_left 1
    simpa using h
  · rw [intervalIntegral.integral_comp_sub_left (fun x => x ^ (-κ)) 1, sub_self,
      integral_rpow (Or.inl hr), Real.zero_rpow (by linarith)]
    ring_nf

/-- Radial facts for `k` on `1/2 ≤ |z| < 1` with `|k'| ≤ 4 (1 - |z|)^{-κ}`: integrability of `|k'(r u)|` on
`[ρ, 1]`, the bound of its integral, the radial FTC bound `|k(u) - k(ρ u)| ≤ ∫_ρ^1 |k'(r u)| dr`, and positivity. -/
theorem s5r58q_radial {k : ℂ → ℂ} {κ : ℝ} (hκ1 : κ < 1)
    (hc : ContinuousOn k (closedBall 0 1 \ {0}))
    (hdiff : ∀ z : ℂ, 1 / 2 ≤ ‖z‖ → ‖z‖ < 1 → DifferentiableAt ℂ k z)
    (hne : ∀ z : ℂ, 1 / 2 ≤ ‖z‖ → ‖z‖ < 1 → deriv k z ≠ 0)
    (hub : ∀ z : ℂ, 1 / 2 ≤ ‖z‖ → ‖z‖ < 1 → ‖deriv k z‖ ≤ 4 * (1 - ‖z‖) ^ (-κ))
    {u : ℂ} (hu : ‖u‖ = 1) {ρ : ℝ} (hρ : 1 / 2 ≤ ρ) (hρ1 : ρ ≤ 1) :
    IntervalIntegrable (fun r : ℝ => ‖deriv k ((r : ℂ) * u)‖) volume ρ 1 ∧
      (∫ r in ρ..1, ‖deriv k ((r : ℂ) * u)‖) ≤ 4 * ((1 - ρ) ^ (1 - κ) / (1 - κ)) ∧
      ‖k u - k ((ρ : ℂ) * u)‖ ≤ ∫ r in ρ..1, ‖deriv k ((r : ℂ) * u)‖ ∧
      (ρ < 1 → 0 < ∫ r in ρ..1, ‖deriv k ((r : ℂ) * u)‖) := by
  have hn : ∀ x : ℝ, 0 ≤ x → ‖(x : ℂ) * u‖ = x := fun x hx => by
    rw [norm_mul, hu, mul_one, Complex.norm_real, Real.norm_of_nonneg hx]
  have hmeas : Measurable fun r : ℝ => deriv k ((r : ℂ) * u) :=
    (measurable_deriv k).comp (Complex.measurable_ofReal.mul_const u)
  have hin : ∀ r ∈ Ioo ρ 1, 1 / 2 ≤ ‖(r : ℂ) * u‖ ∧ ‖(r : ℂ) * u‖ < 1 := fun r hr => by
    rw [hn r (by linarith [hr.1])]
    exact ⟨by linarith [hr.1], hr.2⟩
  have hbd : ∀ r ∈ Ioo ρ 1, ‖deriv k ((r : ℂ) * u)‖ ≤ 4 * (1 - r) ^ (-κ) := fun r hr => by
    have h := hub _ (hin r hr).1 (hin r hr).2
    rwa [hn r (by linarith [hr.1])] at h
  obtain ⟨hI, hIv⟩ := s5r58q_int_rpow hκ1 hρ1
  have hdom : IntervalIntegrable (fun r : ℝ => 4 * (1 - r) ^ (-κ)) volume ρ 1 := hI.const_mul 4
  have hII : IntervalIntegrable (fun r : ℝ => deriv k ((r : ℂ) * u)) volume ρ 1 := by
    rw [intervalIntegrable_iff_integrableOn_Ioo_of_le hρ1]
    exact Integrable.mono' ((intervalIntegrable_iff_integrableOn_Ioo_of_le hρ1).mp hdom)
      hmeas.aestronglyMeasurable ((ae_restrict_mem measurableSet_Ioo).mono fun r hr => hbd r hr)
  have hIn : IntervalIntegrable (fun r : ℝ => ‖deriv k ((r : ℂ) * u)‖) volume ρ 1 := hII.norm
  refine ⟨hIn, ?_, ?_, ?_⟩
  · refine (intervalIntegral.integral_mono_on_of_le_Ioo hρ1 hIn hdom fun r hr => hbd r hr).trans (le_of_eq ?_)
    rw [intervalIntegral.integral_const_mul, hIv]
  · have hcont : ContinuousOn (fun r : ℝ => k ((r : ℂ) * u)) (Icc ρ 1) := by
      refine hc.comp (Complex.continuous_ofReal.mul continuous_const).continuousOn fun r hr => ?_
      have hr0 : 0 ≤ r := by linarith [hr.1]
      refine ⟨?_, ?_⟩
      · rw [mem_closedBall_zero_iff, hn r hr0]
        exact hr.2
      · intro h
        have h' := congrArg norm (show (r : ℂ) * u = 0 from h)
        rw [hn r hr0, norm_zero] at h'
        linarith [hr.1]
    have hderiv : ∀ r ∈ Ioo ρ 1, HasDerivAt (fun r : ℝ => k ((r : ℂ) * u)) (deriv k ((r : ℂ) * u) * u) r := by
      intro r hr
      have h1 : HasDerivAt (fun w : ℂ => k (w * u)) (deriv k ((r : ℂ) * u) * u) (r : ℂ) := by
        have h2 := (hdiff _ (hin r hr).1 (hin r hr).2).hasDerivAt.comp (r : ℂ) ((hasDerivAt_id (r : ℂ)).mul_const u)
        simpa [Function.comp_def] using h2
      exact h1.comp_ofReal
    have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hρ1 hcont hderiv (hII.mul_const u)
    have h1u : ((1 : ℝ) : ℂ) * u = u := by simp
    rw [h1u] at hftc
    rw [← hftc]
    refine (intervalIntegral.norm_integral_le_integral_norm hρ1).trans (le_of_eq ?_)
    congr 1
    funext r
    rw [norm_mul, hu, mul_one]
  · intro hlt
    exact intervalIntegral.intervalIntegral_pos_of_pos_on hIn
      (fun r hr => norm_pos_iff.mpr (hne _ (hin r hr).1 (hin r hr).2)) hlt

/-- `ρ ↦ ∫_ρ^1 g` is antitone for `g ≥ 0`. -/
theorem s5r58q_antitone {g : ℝ → ℝ} {ρ r : ℝ} (hρr : ρ ≤ r) (hr1 : r ≤ 1)
    (hg : IntervalIntegrable g volume ρ 1) (hg0 : ∀ x, 0 ≤ g x) :
    (∫ x in r..1, g x) ≤ ∫ x in ρ..1, g x := by
  have h1 : IntervalIntegrable g volume ρ r := hg.mono_set (by
    rw [uIcc_of_le hρr, uIcc_of_le (hρr.trans hr1)]
    exact Icc_subset_Icc_right hr1)
  have h2 : IntervalIntegrable g volume r 1 := hg.mono_set (by
    rw [uIcc_of_le hr1, uIcc_of_le (hρr.trans hr1)]
    exact Icc_subset_Icc_left hρr)
  rw [← intervalIntegral.integral_add_adjacent_intervals h1 h2]
  linarith [intervalIntegral.integral_nonneg (μ := volume) hρr fun x _ => hg0 x]

/-- The box integration (Pommerenke (9.4.12)): a product bound on `(ρ₁, 1) × (ρ₂, 1)` integrates to the product of
the radial integrals. -/
theorem s5r58q_box {g₁ g₂ : ℝ → ℝ} {κ c ρ₁ ρ₂ : ℝ} (hκ1 : κ < 1) (hρ₁ : ρ₁ ≤ 1) (hρ₂ : ρ₂ ≤ 1)
    (h1 : IntervalIntegrable g₁ volume ρ₁ 1) (h2 : IntervalIntegrable g₂ volume ρ₂ 1)
    (hb : ∀ r₁ ∈ Ioo ρ₁ 1, ∀ r₂ ∈ Ioo ρ₂ 1, g₁ r₁ * g₂ r₂ ≤ c * (1 - r₁) ^ (-κ) * (1 - r₂) ^ (-κ)) :
    (∫ r in ρ₁..1, g₁ r) * (∫ r in ρ₂..1, g₂ r) ≤
      c * ((1 - ρ₁) ^ (1 - κ) / (1 - κ)) * ((1 - ρ₂) ^ (1 - κ) / (1 - κ)) := by
  obtain ⟨hI₁, hv₁⟩ := s5r58q_int_rpow hκ1 hρ₁
  obtain ⟨hI₂, hv₂⟩ := s5r58q_int_rpow hκ1 hρ₂
  have hin : ∀ r₂ ∈ Ioo ρ₂ 1, (∫ r in ρ₁..1, g₁ r) * g₂ r₂ ≤
      c * ((1 - ρ₁) ^ (1 - κ) / (1 - κ)) * (1 - r₂) ^ (-κ) := by
    intro r₂ hr₂
    rw [← intervalIntegral.integral_mul_const]
    refine (intervalIntegral.integral_mono_on_of_le_Ioo hρ₁ (h1.mul_const _)
      ((hI₁.const_mul c).mul_const ((1 - r₂) ^ (-κ))) fun r₁ hr₁ => hb r₁ hr₁ r₂ hr₂).trans (le_of_eq ?_)
    rw [intervalIntegral.integral_mul_const, intervalIntegral.integral_const_mul, hv₁]
  rw [← intervalIntegral.integral_const_mul]
  refine (intervalIntegral.integral_mono_on_of_le_Ioo hρ₂ (h2.const_mul _) (hI₂.const_mul _) hin).trans
    (le_of_eq ?_)
  rw [intervalIntegral.integral_const_mul, hv₂]

/-- **Circle injectivity from a two-point bound** (Pommerenke Thm 9.12, (9.4.11)–(9.4.13), for one pair). Let `k`
be continuous on `𝔻̄ ∖ 0`, holomorphic with `k' ≠ 0` and `|k'| ≤ 4 (1 - |z|)^{-κ}` on `1/2 ≤ |z| < 1`, and satisfy
the two-point bound `|k'(z₁) k'(z₂)| |z₁ - z₂|² ≤ A (1 - |z₁|)^{-κ} (1 - |z₂|)^{-κ} |k(z₁) - k(z₂)|²` there, with
`κ < 1`. Then `k` is injective on `S¹`. (Radial integration over a box `[ρ₁, 1) × [ρ₂, 1)` with equal radial
lengths `ε`; `ε → 0` contradicts `k(u₁) = k(u₂)`.) -/
theorem s5r58q_core {k : ℂ → ℂ} {κ A : ℝ} (hκ0 : 0 ≤ κ) (hκ1 : κ < 1) (hA : 0 ≤ A)
    (hc : ContinuousOn k (closedBall 0 1 \ {0}))
    (hdiff : ∀ z : ℂ, 1 / 2 ≤ ‖z‖ → ‖z‖ < 1 → DifferentiableAt ℂ k z)
    (hne : ∀ z : ℂ, 1 / 2 ≤ ‖z‖ → ‖z‖ < 1 → deriv k z ≠ 0)
    (hub : ∀ z : ℂ, 1 / 2 ≤ ‖z‖ → ‖z‖ < 1 → ‖deriv k z‖ ≤ 4 * (1 - ‖z‖) ^ (-κ))
    (htp : ∀ z₁ z₂ : ℂ, 1 / 2 ≤ ‖z₁‖ → ‖z₁‖ < 1 → 1 / 2 ≤ ‖z₂‖ → ‖z₂‖ < 1 → z₁ ≠ z₂ →
      ‖deriv k z₁‖ * ‖deriv k z₂‖ * ‖z₁ - z₂‖ ^ 2 ≤
        A * (1 - ‖z₁‖) ^ (-κ) * (1 - ‖z₂‖) ^ (-κ) * ‖k z₁ - k z₂‖ ^ 2)
    {u₁ u₂ : ℂ} (hu₁ : ‖u₁‖ = 1) (hu₂ : ‖u₂‖ = 1) (h12 : u₁ ≠ u₂) : k u₁ ≠ k u₂ := by
  intro heq
  have hκ' : 0 < 1 - κ := by linarith
  have hδ : 0 < ‖u₁ - u₂‖ := norm_pos_iff.mpr (sub_ne_zero.mpr h12)
  obtain ⟨δ, hδdef⟩ : ∃ δ, δ = ‖u₁ - u₂‖ := ⟨_, rfl⟩
  rw [← hδdef] at hδ
  obtain ⟨ρs, hρs⟩ : ∃ ρs : ℝ, ρs = max (1 / 2) (1 - δ / 4) := ⟨_, rfl⟩
  have hρs1 : 1 / 2 ≤ ρs := hρs ▸ le_max_left _ _
  have hρs2 : 1 - δ / 4 ≤ ρs := hρs ▸ le_max_right _ _
  have hρs3 : ρs < 1 := by rw [hρs]; exact max_lt (by norm_num) (by linarith)
  have hn : ∀ (x : ℝ) (u : ℂ), ‖u‖ = 1 → 0 ≤ x → ‖(x : ℂ) * u‖ = x := fun x u hu hx => by
    rw [norm_mul, hu, mul_one, Complex.norm_real, Real.norm_of_nonneg hx]
  have hdist : ∀ (x : ℝ) (u : ℂ), ‖u‖ = 1 → x ≤ 1 → ‖(x : ℂ) * u - u‖ = 1 - x := fun x u hu hx => by
    have : (x : ℂ) * u - u = ((x - 1 : ℝ) : ℂ) * u := by push_cast; ring
    rw [this, norm_mul, hu, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (by linarith)]
    ring
  have R₁ := fun ρ (h1 : 1 / 2 ≤ ρ) (h2 : ρ ≤ 1) => s5r58q_radial hκ1 hc hdiff hne hub hu₁ h1 h2
  have R₂ := fun ρ (h1 : 1 / 2 ≤ ρ) (h2 : ρ ≤ 1) => s5r58q_radial hκ1 hc hdiff hne hub hu₂ h1 h2
  -- the target radial length
  obtain ⟨b2s, hb2s⟩ : ∃ b, b = ∫ r in ρs..1, ‖deriv k ((r : ℂ) * u₂)‖ := ⟨_, rfl⟩
  have hb2s0 : 0 < b2s := hb2s ▸ (R₂ ρs hρs1 hρs3.le).2.2.2 hρs3
  obtain ⟨η, hη⟩ : ∃ η : ℝ, η = min (b2s * (1 - κ) / 4) (δ ^ 2 * (1 - κ) ^ 2 / (16 * A + 1)) := ⟨_, rfl⟩
  have hη0 : 0 < η := by rw [hη]; exact lt_min (by positivity) (by positivity)
  -- choose `ρ₁` near `1`
  have hcont1 : Continuous fun x : ℝ => (1 - x) ^ (1 - κ) :=
    (continuous_const.sub continuous_id).rpow_const fun _ => Or.inr hκ'.le
  have htend : Tendsto (fun x : ℝ => (1 - x) ^ (1 - κ)) (𝓝[<] 1) (𝓝 0) := by
    have h := hcont1.continuousAt (x := (1 : ℝ))
    rw [ContinuousAt, sub_self, Real.zero_rpow hκ'.ne'] at h
    exact h.mono_left nhdsWithin_le_nhds
  obtain ⟨ρ₁, hρ₁η, hρ₁⟩ := ((htend.eventually (gt_mem_nhds hη0)).and (Ioo_mem_nhdsLT hρs3)).exists
  have hρ₁a : 1 / 2 ≤ ρ₁ := hρs1.trans hρ₁.1.le
  obtain ⟨hI₁, hB₁, -, hP₁⟩ := R₁ ρ₁ hρ₁a hρ₁.2.le
  obtain ⟨ε, hε⟩ : ∃ ε, ε = ∫ r in ρ₁..1, ‖deriv k ((r : ℂ) * u₁)‖ := ⟨_, rfl⟩
  have hε0 : 0 < ε := hε ▸ hP₁ hρ₁.2
  have hεle : ε ≤ b2s := by
    rw [hε]
    refine hB₁.trans ?_
    have : (1 - ρ₁) ^ (1 - κ) ≤ b2s * (1 - κ) / 4 := hρ₁η.le.trans (hη ▸ min_le_left _ _)
    rw [mul_div_assoc']
    rw [div_le_iff₀ hκ']
    linarith
  -- choose `ρ₂` with the same radial length (IVT)
  obtain ⟨hI₂s, -, -, -⟩ := R₂ ρs hρs1 hρs3.le
  have hcb : ContinuousOn (fun x => ∫ r in x..1, ‖deriv k ((r : ℂ) * u₂)‖) (Icc ρs 1) := by
    have h := intervalIntegral.continuousOn_primitive_interval_left (μ := volume)
      (f := fun r : ℝ => ‖deriv k ((r : ℂ) * u₂)‖) (a := ρs) (b := 1)
      ((intervalIntegrable_iff_integrableOn_Icc_of_le hρs3.le).mp hI₂s |>.mono_set (by rw [uIcc_of_le hρs3.le]))
    rwa [uIcc_of_le hρs3.le] at h
  obtain ⟨ρ₂, hρ₂, hρ₂ε⟩ := intermediate_value_Icc' hρs3.le hcb
    (show ε ∈ Icc (∫ r in (1 : ℝ)..1, ‖deriv k ((r : ℂ) * u₂)‖) (∫ r in ρs..1, ‖deriv k ((r : ℂ) * u₂)‖) by
      rw [intervalIntegral.integral_same, ← hb2s]
      exact ⟨hε0.le, hεle⟩)
  beta_reduce at hρ₂ε
  have hρ₂1 : ρ₂ < 1 := by
    rcases hρ₂.2.lt_or_eq with h | h
    · exact h
    · rw [h, intervalIntegral.integral_same] at hρ₂ε
      linarith
  obtain ⟨hI₂, -, -, -⟩ := R₂ ρ₂ (hρs1.trans hρ₂.1) hρ₂.2
  -- the pointwise box bound
  have hbox : ∀ r₁ ∈ Ioo ρ₁ 1, ∀ r₂ ∈ Ioo ρ₂ 1,
      ‖deriv k ((r₁ : ℂ) * u₁)‖ * ‖deriv k ((r₂ : ℂ) * u₂)‖ ≤
        16 * A * ε ^ 2 / δ ^ 2 * (1 - r₁) ^ (-κ) * (1 - r₂) ^ (-κ) := by
    intro r₁ hr₁ r₂ hr₂
    have hr₁a : 1 / 2 ≤ r₁ := hρ₁a.trans hr₁.1.le
    have hr₂a : 1 / 2 ≤ r₂ := (hρs1.trans hρ₂.1).trans hr₂.1.le
    have hn₁ := hn r₁ u₁ hu₁ (by linarith)
    have hn₂ := hn r₂ u₂ hu₂ (by linarith)
    -- separation of the two radial points
    have hsep : δ / 2 ≤ ‖(r₁ : ℂ) * u₁ - (r₂ : ℂ) * u₂‖ := by
      have e1 := hdist r₁ u₁ hu₁ hr₁.2.le
      have e2 := hdist r₂ u₂ hu₂ hr₂.2.le
      have ht : ‖u₁ - u₂‖ ≤ ‖(r₁ : ℂ) * u₁ - u₁‖ + ‖(r₁ : ℂ) * u₁ - (r₂ : ℂ) * u₂‖ + ‖(r₂ : ℂ) * u₂ - u₂‖ := by
        calc ‖u₁ - u₂‖ = ‖-((r₁ : ℂ) * u₁ - u₁) + ((r₁ : ℂ) * u₁ - (r₂ : ℂ) * u₂) + ((r₂ : ℂ) * u₂ - u₂)‖ := by
              congr 1; ring
          _ ≤ ‖-((r₁ : ℂ) * u₁ - u₁)‖ + ‖(r₁ : ℂ) * u₁ - (r₂ : ℂ) * u₂‖ + ‖(r₂ : ℂ) * u₂ - u₂‖ :=
              norm_add₃_le
          _ = _ := by rw [norm_neg]
      have hr₁b : 1 - r₁ ≤ δ / 4 := by linarith [hρ₁.1, hr₁.1]
      have hr₂b : 1 - r₂ ≤ δ / 4 := by linarith [hρ₂.1, hr₂.1]
      rw [← hδdef, e1, e2] at ht
      linarith
    have hne12 : (r₁ : ℂ) * u₁ ≠ (r₂ : ℂ) * u₂ := by
      intro h
      rw [h, sub_self, norm_zero] at hsep
      linarith
    -- the values are `2ε`-close
    have hval : ‖k ((r₁ : ℂ) * u₁) - k ((r₂ : ℂ) * u₂)‖ ≤ 2 * ε := by
      obtain ⟨-, -, hF₁, -⟩ := R₁ r₁ hr₁a hr₁.2.le
      obtain ⟨-, -, hF₂, -⟩ := R₂ r₂ hr₂a hr₂.2.le
      have hm₁ := s5r58q_antitone hr₁.1.le hr₁.2.le hI₁ fun x => norm_nonneg _
      have hm₂ := s5r58q_antitone hr₂.1.le hr₂.2.le hI₂ fun x => norm_nonneg _
      calc ‖k ((r₁ : ℂ) * u₁) - k ((r₂ : ℂ) * u₂)‖
          = ‖-(k u₁ - k ((r₁ : ℂ) * u₁)) + (k u₂ - k ((r₂ : ℂ) * u₂))‖ := by rw [heq]; congr 1; ring
        _ ≤ ‖k u₁ - k ((r₁ : ℂ) * u₁)‖ + ‖k u₂ - k ((r₂ : ℂ) * u₂)‖ := by
            refine (norm_add_le _ _).trans ?_; rw [norm_neg]
        _ ≤ ε + ε := by
            refine add_le_add ?_ ?_
            · rw [hε]; exact hF₁.trans hm₁
            · rw [← hρ₂ε]; exact hF₂.trans hm₂
        _ = 2 * ε := by ring
    have h := htp _ _ (by rw [hn₁]; exact hr₁a) (by rw [hn₁]; exact hr₁.2) (by rw [hn₂]; exact hr₂a)
      (by rw [hn₂]; exact hr₂.2) hne12
    rw [hn₁, hn₂] at h
    have hP : 0 ≤ (1 - r₁) ^ (-κ) * (1 - r₂) ^ (-κ) :=
      mul_nonneg (Real.rpow_nonneg (by linarith [hr₁.2]) _) (Real.rpow_nonneg (by linarith [hr₂.2]) _)
    have hg0 : 0 ≤ ‖deriv k ((r₁ : ℂ) * u₁)‖ * ‖deriv k ((r₂ : ℂ) * u₂)‖ := by positivity
    have h1 : ‖deriv k ((r₁ : ℂ) * u₁)‖ * ‖deriv k ((r₂ : ℂ) * u₂)‖ * (δ ^ 2 / 4) ≤
        A * ((1 - r₁) ^ (-κ) * (1 - r₂) ^ (-κ)) * (4 * ε ^ 2) := by
      have hs2 : δ ^ 2 / 4 ≤ ‖(r₁ : ℂ) * u₁ - (r₂ : ℂ) * u₂‖ ^ 2 := by
        have := pow_le_pow_left₀ (by positivity) hsep 2
        linarith [show (δ / 2) ^ 2 = δ ^ 2 / 4 by ring]
      have hv2 : ‖k ((r₁ : ℂ) * u₁) - k ((r₂ : ℂ) * u₂)‖ ^ 2 ≤ 4 * ε ^ 2 := by
        have := pow_le_pow_left₀ (norm_nonneg _) hval 2
        linarith [show (2 * ε) ^ 2 = 4 * ε ^ 2 by ring]
      calc _ ≤ ‖deriv k ((r₁ : ℂ) * u₁)‖ * ‖deriv k ((r₂ : ℂ) * u₂)‖ *
            ‖(r₁ : ℂ) * u₁ - (r₂ : ℂ) * u₂‖ ^ 2 := mul_le_mul_of_nonneg_left hs2 hg0
        _ ≤ A * (1 - r₁) ^ (-κ) * (1 - r₂) ^ (-κ) * ‖k ((r₁ : ℂ) * u₁) - k ((r₂ : ℂ) * u₂)‖ ^ 2 := h
        _ = A * ((1 - r₁) ^ (-κ) * (1 - r₂) ^ (-κ)) * ‖k ((r₁ : ℂ) * u₁) - k ((r₂ : ℂ) * u₂)‖ ^ 2 := by ring
        _ ≤ A * ((1 - r₁) ^ (-κ) * (1 - r₂) ^ (-κ)) * (4 * ε ^ 2) :=
            mul_le_mul_of_nonneg_left hv2 (mul_nonneg hA hP)
    have hδ4 : 0 < δ ^ 2 / 4 := by positivity
    refine le_of_mul_le_mul_right (h1.trans (le_of_eq ?_)) hδ4
    field_simp
    ring
  -- integrate over the box and conclude
  have hfin := s5r58q_box hκ1 hρ₁.2.le hρ₂.2 hI₁ hI₂ hbox
  rw [← hε, hρ₂ε] at hfin
  obtain ⟨X, hX⟩ : ∃ X, X = (1 - ρ₁) ^ (1 - κ) := ⟨_, rfl⟩
  have hX0 : 0 ≤ X := hX ▸ Real.rpow_nonneg (by linarith [hρ₁.2]) _
  have hXη : X < δ ^ 2 * (1 - κ) ^ 2 / (16 * A + 1) := hX ▸ hρ₁η.trans_le (hη ▸ min_le_right _ _)
  have hY : (1 - ρ₂) ^ (1 - κ) ≤ 1 := Real.rpow_le_one (by linarith) (by linarith [hρ₂.1, hρs1]) hκ'.le
  rw [← hX] at hfin
  have hc0 : 0 ≤ 16 * A * ε ^ 2 / δ ^ 2 := by positivity
  have h2 : ε * ε ≤ 16 * A * ε ^ 2 / δ ^ 2 * (X / (1 - κ)) * (1 / (1 - κ)) :=
    hfin.trans (mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hY hκ'.le)
      (mul_nonneg hc0 (div_nonneg hX0 hκ'.le)))
  have h3 : 16 * A * ε ^ 2 / δ ^ 2 * (X / (1 - κ)) * (1 / (1 - κ)) =
      ε ^ 2 * (16 * A * X / (δ ^ 2 * (1 - κ) ^ 2)) := by
    field_simp
  have h4 : 16 * A * X / (δ ^ 2 * (1 - κ) ^ 2) < 1 := by
    rw [div_lt_one (by positivity)]
    rw [lt_div_iff₀ (by positivity)] at hXη
    nlinarith
  rw [h3] at h2
  nlinarith [mul_pos hε0 hε0]

/-- `exp(κ log (1/(1 - r²))) ≤ (1 - r)^{-κ}` for `0 ≤ r < 1`, `0 ≤ κ` (via `s5r58_exp_bd`). -/
theorem s5r58q_explog {κ r : ℝ} (hκ : 0 ≤ κ) (hr0 : 0 ≤ r) (hr : r < 1) :
    Real.exp (κ * Real.log (1 / (1 - r ^ 2))) ≤ (1 - r) ^ (-κ) := by
  have hl : 0 ≤ Real.log (1 / (1 - r ^ 2)) :=
    Real.log_nonneg (by rw [le_div_iff₀ (by nlinarith)]; nlinarith)
  have h := s5r58_exp_bd (S := -((κ * Real.log (1 / (1 - r ^ 2)) : ℝ) : ℂ)) hκ hr0 hr (by
    rw [norm_neg, Complex.norm_real, Real.norm_of_nonneg (mul_nonneg hκ hl)])
  rwa [neg_neg, Complex.norm_exp, Complex.ofReal_re] at h

/-- The `n = 1` Golusin bound gives the diagonal estimate `|S(z,z)| ≤ κ log (1/(1 - |z|²))`. -/
theorem s5r58q_diag {C : ℕ → ℕ → ℂ} {κ : ℝ}
    (hgol : ∀ (n : ℕ) (z γ : Fin n → ℂ), (∀ ν, z ν ∈ unitDisc) →
      ‖∑ μ, ∑ ν, γ μ * γ ν * ∑' q : ℕ × ℕ, C q.1 q.2 / Real.sqrt ((q.1 + 1) * (q.2 + 1)) *
          z μ ^ (q.1 + 1) * z ν ^ (q.2 + 1)‖ ≤
        κ * (∑ μ, ∑ ν, γ μ * conj (γ ν) * Complex.log (1 / (1 - z μ * conj (z ν)))).re)
    {z : ℂ} (hz : ‖z‖ < 1) :
    ‖∑' q : ℕ × ℕ, C q.1 q.2 / Real.sqrt ((q.1 + 1) * (q.2 + 1)) * z ^ (q.1 + 1) * z ^ (q.2 + 1)‖ ≤
      κ * Real.log (1 / (1 - ‖z‖ ^ 2)) := by
  have hg := hgol 1 (fun _ => z) (fun _ => 1) (fun _ => mem_ball_zero_iff.mpr hz)
  simp only [Fin.sum_univ_one, one_mul, mul_one, map_one] at hg
  have hz2 : ‖z‖ ^ 2 < 1 := by nlinarith [norm_nonneg z]
  have hl : (Complex.log (1 / (1 - z * conj z))).re = Real.log (1 / (1 - ‖z‖ ^ 2)) := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
    have hc : (1 : ℂ) / (1 - ((‖z‖ ^ 2 : ℝ) : ℂ)) = ((1 / (1 - ‖z‖ ^ 2) : ℝ) : ℂ) := by push_cast; ring
    rw [hc, ← Complex.ofReal_log (div_nonneg zero_le_one (by linarith))]
    exact Complex.ofReal_re _
  rwa [hl] at hg

/-- The Golusin constant is nonnegative (the `n = 1` inequality at `z = 1/2`). -/
theorem s5r58q_kappa_nonneg {C : ℕ → ℕ → ℂ} {κ : ℝ}
    (hgol : ∀ (n : ℕ) (z γ : Fin n → ℂ), (∀ ν, z ν ∈ unitDisc) →
      ‖∑ μ, ∑ ν, γ μ * γ ν * ∑' q : ℕ × ℕ, C q.1 q.2 / Real.sqrt ((q.1 + 1) * (q.2 + 1)) *
          z μ ^ (q.1 + 1) * z ν ^ (q.2 + 1)‖ ≤
        κ * (∑ μ, ∑ ν, γ μ * conj (γ ν) * Complex.log (1 / (1 - z μ * conj (z ν)))).re) : 0 ≤ κ := by
  have h := s5r58q_diag hgol (z := (1 / 2 : ℂ)) (by norm_num)
  have hl : 0 < Real.log (1 / (1 - ‖(1 / 2 : ℂ)‖ ^ 2)) := Real.log_pos (by norm_num)
  by_contra hk
  push_neg at hk
  have := mul_neg_of_neg_of_pos hk hl
  linarith [norm_nonneg (∑' q : ℕ × ℕ, C q.1 q.2 / Real.sqrt ((q.1 + 1) * (q.2 + 1)) *
    (1 / 2 : ℂ) ^ (q.1 + 1) * (1 / 2 : ℂ) ^ (q.2 + 1))]

/-- The `n = 2`, `γ = (1, -1)` Golusin bound: with `Q = S₁₁ + S₂₂ - S₁₂ - S₂₁`,
`|Q| ≤ κ (log 1/(1-|z₁|²) + log 1/(1-|z₂|²) + 2 log 2)`. -/
theorem s5r58q_two {C : ℕ → ℕ → ℂ} {κ : ℝ} (hκ : 0 ≤ κ)
    (hgol : ∀ (n : ℕ) (z γ : Fin n → ℂ), (∀ ν, z ν ∈ unitDisc) →
      ‖∑ μ, ∑ ν, γ μ * γ ν * ∑' q : ℕ × ℕ, C q.1 q.2 / Real.sqrt ((q.1 + 1) * (q.2 + 1)) *
          z μ ^ (q.1 + 1) * z ν ^ (q.2 + 1)‖ ≤
        κ * (∑ μ, ∑ ν, γ μ * conj (γ ν) * Complex.log (1 / (1 - z μ * conj (z ν)))).re)
    {z₁ z₂ : ℂ} (hz₁ : ‖z₁‖ < 1) (hz₂ : ‖z₂‖ < 1) :
    ‖(∑' q : ℕ × ℕ, C q.1 q.2 / Real.sqrt ((q.1 + 1) * (q.2 + 1)) * z₁ ^ (q.1 + 1) * z₁ ^ (q.2 + 1)) +
      (∑' q : ℕ × ℕ, C q.1 q.2 / Real.sqrt ((q.1 + 1) * (q.2 + 1)) * z₂ ^ (q.1 + 1) * z₂ ^ (q.2 + 1)) -
      (∑' q : ℕ × ℕ, C q.1 q.2 / Real.sqrt ((q.1 + 1) * (q.2 + 1)) * z₁ ^ (q.1 + 1) * z₂ ^ (q.2 + 1)) -
      (∑' q : ℕ × ℕ, C q.1 q.2 / Real.sqrt ((q.1 + 1) * (q.2 + 1)) * z₂ ^ (q.1 + 1) * z₁ ^ (q.2 + 1))‖ ≤
      κ * (Real.log (1 / (1 - ‖z₁‖ ^ 2)) + Real.log (1 / (1 - ‖z₂‖ ^ 2)) + 2 * Real.log 2) := by
  have hg := hgol 2 ![z₁, z₂] ![1, -1] (by
    intro ν; fin_cases ν
    · exact mem_ball_zero_iff.mpr hz₁
    · exact mem_ball_zero_iff.mpr hz₂)
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, one_mul, mul_one,
    map_one, map_neg, neg_mul, mul_neg, neg_neg] at hg
  have hre : ∀ z : ℂ, ‖z‖ < 1 → (Complex.log (1 / (1 - z * conj z))).re = Real.log (1 / (1 - ‖z‖ ^ 2)) := by
    intro z hz
    have hz2 : ‖z‖ ^ 2 < 1 := by nlinarith [norm_nonneg z]
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
    have hc : (1 : ℂ) / (1 - ((‖z‖ ^ 2 : ℝ) : ℂ)) = ((1 / (1 - ‖z‖ ^ 2) : ℝ) : ℂ) := by push_cast; ring
    rw [hc, ← Complex.ofReal_log (div_nonneg zero_le_one (by linarith))]
    exact Complex.ofReal_re _
  have hW : 0 < ‖1 - z₁ * conj z₂‖ := by
    refine norm_pos_iff.mpr fun h => ?_
    have h1 : z₁ * conj z₂ = 1 := by linear_combination -h
    have h2 := congrArg norm h1
    rw [norm_mul, Complex.norm_conj, norm_one] at h2
    nlinarith [norm_nonneg z₁, norm_nonneg z₂, mul_lt_mul'' hz₁ hz₂ (norm_nonneg _) (norm_nonneg _)]
  have hW2 : ‖1 - z₁ * conj z₂‖ ≤ 2 := by
    refine (norm_sub_le _ _).trans ?_
    rw [norm_one, norm_mul, Complex.norm_conj]
    nlinarith [norm_nonneg z₁, norm_nonneg z₂, mul_lt_mul'' hz₁ hz₂ (norm_nonneg _) (norm_nonneg _)]
  have hconj : 1 - z₂ * conj z₁ = conj (1 - z₁ * conj z₂) := by
    simp only [map_sub, map_one, map_mul, Complex.conj_conj]; ring
  have hoff : ∀ w : ℂ, 0 < ‖w‖ → (Complex.log (1 / w)).re = -Real.log ‖w‖ := by
    intro w hw
    rw [Complex.log_re, one_div, norm_inv, Real.log_inv]
  have hL : (Complex.log (1 / (1 - z₁ * conj z₁)) + -Complex.log (1 / (1 - z₁ * conj z₂)) +
      (-Complex.log (1 / (1 - z₂ * conj z₁)) + Complex.log (1 / (1 - z₂ * conj z₂)))).re =
      Real.log (1 / (1 - ‖z₁‖ ^ 2)) + Real.log (1 / (1 - ‖z₂‖ ^ 2)) + 2 * Real.log ‖1 - z₁ * conj z₂‖ := by
    simp only [Complex.add_re, Complex.neg_re]
    rw [hre z₁ hz₁, hre z₂ hz₂, hoff _ hW, hconj, hoff _ (by rwa [Complex.norm_conj]), Complex.norm_conj]
    ring
  have hQ : (∑' q : ℕ × ℕ, C q.1 q.2 / Real.sqrt ((q.1 + 1) * (q.2 + 1)) * z₁ ^ (q.1 + 1) * z₁ ^ (q.2 + 1)) +
      (∑' q : ℕ × ℕ, C q.1 q.2 / Real.sqrt ((q.1 + 1) * (q.2 + 1)) * z₂ ^ (q.1 + 1) * z₂ ^ (q.2 + 1)) -
      (∑' q : ℕ × ℕ, C q.1 q.2 / Real.sqrt ((q.1 + 1) * (q.2 + 1)) * z₁ ^ (q.1 + 1) * z₂ ^ (q.2 + 1)) -
      (∑' q : ℕ × ℕ, C q.1 q.2 / Real.sqrt ((q.1 + 1) * (q.2 + 1)) * z₂ ^ (q.1 + 1) * z₁ ^ (q.2 + 1)) =
      (∑' q : ℕ × ℕ, C q.1 q.2 / Real.sqrt ((q.1 + 1) * (q.2 + 1)) * z₁ ^ (q.1 + 1) * z₁ ^ (q.2 + 1)) +
        -(∑' q : ℕ × ℕ, C q.1 q.2 / Real.sqrt ((q.1 + 1) * (q.2 + 1)) * z₁ ^ (q.1 + 1) * z₂ ^ (q.2 + 1)) +
        (-(∑' q : ℕ × ℕ, C q.1 q.2 / Real.sqrt ((q.1 + 1) * (q.2 + 1)) * z₂ ^ (q.1 + 1) * z₁ ^ (q.2 + 1)) +
          ∑' q : ℕ × ℕ, C q.1 q.2 / Real.sqrt ((q.1 + 1) * (q.2 + 1)) * z₂ ^ (q.1 + 1) * z₂ ^ (q.2 + 1)) := by
    ring
  rw [hQ]
  refine hg.trans ?_
  rw [hL]
  have hlog : Real.log ‖1 - z₁ * conj z₂‖ ≤ Real.log 2 := Real.log_le_log hW hW2
  nlinarith

/-- **Two-point bound for `Ψ = 1/f`** (Pommerenke (9.4.11) in the disc picture):
`|Ψ'(z₁) Ψ'(z₂)| |z₁ - z₂|² = |e^{-Q}| |Ψ(z₁) - Ψ(z₂)|²` with `|e^{-Q}| ≤ 4 (1-|z₁|)^{-κ} (1-|z₂|)^{-κ}`. -/
theorem s5r58q_tp {C : ℕ → ℕ → ℂ} {K κ : ℝ} (hK : ∀ m n, ‖C m n‖ ≤ K) (hκ0 : 0 ≤ κ) (hκ1 : κ < 1) {f : ℂ → ℂ}
    (hfd : DifferentiableOn ℂ f unitDisc) (hfi : InjOn f unitDisc) (hf0 : f 0 = 0)
    (hrep : ∀ z₁ ∈ unitDisc, ∀ z₂ ∈ unitDisc, z₁ ≠ 0 → z₂ ≠ 0 → z₁ ≠ z₂ → ∃ S,
      HasSum (fun q : ℕ × ℕ => C q.1 q.2 / Real.sqrt ((q.1 + 1) * (q.2 + 1)) * z₁ ^ (q.1 + 1) * z₂ ^ (q.2 + 1)) S ∧
      (f z₁ - f z₂) * z₁ * z₂ = (z₁ - z₂) * f z₁ * f z₂ * exp (-S))
    (hgol : ∀ (n : ℕ) (z γ : Fin n → ℂ), (∀ ν, z ν ∈ unitDisc) →
      ‖∑ μ, ∑ ν, γ μ * γ ν * ∑' q : ℕ × ℕ, C q.1 q.2 / Real.sqrt ((q.1 + 1) * (q.2 + 1)) *
          z μ ^ (q.1 + 1) * z ν ^ (q.2 + 1)‖ ≤
        κ * (∑ μ, ∑ ν, γ μ * conj (γ ν) * Complex.log (1 / (1 - z μ * conj (z ν)))).re)
    {z₁ z₂ : ℂ} (hz₁ : z₁ ∈ unitDisc) (hz₂ : z₂ ∈ unitDisc) (hz₁0 : z₁ ≠ 0) (hz₂0 : z₂ ≠ 0) (h12 : z₁ ≠ z₂) :
    ‖-(z₁ * z₁)⁻¹ * exp (-∑' q : ℕ × ℕ, C q.1 q.2 / Real.sqrt ((q.1 + 1) * (q.2 + 1)) * z₁ ^ (q.1 + 1) *
        z₁ ^ (q.2 + 1))‖ *
      ‖-(z₂ * z₂)⁻¹ * exp (-∑' q : ℕ × ℕ, C q.1 q.2 / Real.sqrt ((q.1 + 1) * (q.2 + 1)) * z₂ ^ (q.1 + 1) *
        z₂ ^ (q.2 + 1))‖ * ‖z₁ - z₂‖ ^ 2 ≤
      4 * (1 - ‖z₁‖) ^ (-κ) * (1 - ‖z₂‖) ^ (-κ) * ‖(f z₁)⁻¹ - (f z₂)⁻¹‖ ^ 2 := by
  have _hK := hK
  have _hfd := hfd
  have hfne : ∀ z ∈ unitDisc, z ≠ 0 → f z ≠ 0 := fun z hz hz0 h =>
    hz0 (hfi hz (Metric.mem_ball_self one_pos) (h.trans hf0.symm))
  obtain ⟨S₁₂, hS₁₂, e₁₂⟩ := hrep z₁ hz₁ z₂ hz₂ hz₁0 hz₂0 h12
  obtain ⟨S₂₁, hS₂₁, e₂₁⟩ := hrep z₂ hz₂ z₁ hz₁ hz₂0 hz₁0 h12.symm
  obtain ⟨S₁₁, hS₁₁⟩ : ∃ S, S = ∑' q : ℕ × ℕ, C q.1 q.2 / Real.sqrt ((q.1 + 1) * (q.2 + 1)) * z₁ ^ (q.1 + 1) *
      z₁ ^ (q.2 + 1) := ⟨_, rfl⟩
  obtain ⟨S₂₂, hS₂₂⟩ : ∃ S, S = ∑' q : ℕ × ℕ, C q.1 q.2 / Real.sqrt ((q.1 + 1) * (q.2 + 1)) * z₂ ^ (q.1 + 1) *
      z₂ ^ (q.2 + 1) := ⟨_, rfl⟩
  have hn₁ : ‖z₁‖ < 1 := mem_ball_zero_iff.mp hz₁
  have hn₂ : ‖z₂‖ < 1 := mem_ball_zero_iff.mp hz₂
  have hQ := s5r58q_two hκ0 hgol hn₁ hn₂
  rw [← hS₁₁, ← hS₂₂, hS₁₂.tsum_eq, hS₂₁.tsum_eq] at hQ
  rw [← hS₁₁, ← hS₂₂]
  have hf₁ := hfne z₁ hz₁ hz₁0
  have hf₂ := hfne z₂ hz₂ hz₂0
  -- the identity `Ψ'₁ Ψ'₂ (z₁ - z₂)² = (Ψ₁ - Ψ₂)² e^{-Q}`
  have hd₁ : (f z₁)⁻¹ - (f z₂)⁻¹ = -(z₁ - z₂) * exp (-S₁₂) / (z₁ * z₂) := by
    rw [inv_sub_inv hf₁ hf₂, div_eq_div_iff (mul_ne_zero hf₁ hf₂) (mul_ne_zero hz₁0 hz₂0)]
    linear_combination (-1 : ℂ) * e₁₂
  have hd₂ : (f z₁)⁻¹ - (f z₂)⁻¹ = -(z₁ - z₂) * exp (-S₂₁) / (z₁ * z₂) := by
    rw [inv_sub_inv hf₁ hf₂, div_eq_div_iff (mul_ne_zero hf₁ hf₂) (mul_ne_zero hz₁0 hz₂0)]
    linear_combination e₂₁
  have hid : (-(z₁ * z₁)⁻¹ * exp (-S₁₁)) * (-(z₂ * z₂)⁻¹ * exp (-S₂₂)) * (z₁ - z₂) ^ 2 =
      ((f z₁)⁻¹ - (f z₂)⁻¹) ^ 2 * exp (-(S₁₁ + S₂₂ - S₁₂ - S₂₁)) := by
    have hsq : ((f z₁)⁻¹ - (f z₂)⁻¹) ^ 2 = (z₁ - z₂) ^ 2 * exp (-S₁₂) * exp (-S₂₁) / (z₁ * z₂) ^ 2 := by
      calc ((f z₁)⁻¹ - (f z₂)⁻¹) ^ 2 = ((f z₁)⁻¹ - (f z₂)⁻¹) * ((f z₁)⁻¹ - (f z₂)⁻¹) := pow_two _
        _ = (-(z₁ - z₂) * exp (-S₁₂) / (z₁ * z₂)) * (-(z₁ - z₂) * exp (-S₂₁) / (z₁ * z₂)) :=
            congrArg₂ HMul.hMul hd₁ hd₂
        _ = _ := by ring
    have hexp : exp (-(S₁₁ + S₂₂ - S₁₂ - S₂₁)) * (exp (-S₁₂) * exp (-S₂₁)) = exp (-S₁₁) * exp (-S₂₂) := by
      rw [← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add]
      congr 1
      ring
    rw [hsq]
    have hr : (z₁ - z₂) ^ 2 * exp (-S₁₂) * exp (-S₂₁) / (z₁ * z₂) ^ 2 * exp (-(S₁₁ + S₂₂ - S₁₂ - S₂₁)) =
        (z₁ - z₂) ^ 2 / (z₁ * z₂) ^ 2 * (exp (-(S₁₁ + S₂₂ - S₁₂ - S₂₁)) * (exp (-S₁₂) * exp (-S₂₁))) := by ring
    rw [hr, hexp]
    ring
  have hnorm := congrArg norm hid
  simp only [norm_mul, norm_pow] at hnorm
  -- the bound on `|e^{-Q}|`
  have hE : ‖exp (-(S₁₁ + S₂₂ - S₁₂ - S₂₁))‖ ≤ 4 * (1 - ‖z₁‖) ^ (-κ) * (1 - ‖z₂‖) ^ (-κ) := by
    rw [Complex.norm_exp]
    have h1 : (-(S₁₁ + S₂₂ - S₁₂ - S₂₁)).re ≤ ‖S₁₁ + S₂₂ - S₁₂ - S₂₁‖ :=
      (Complex.re_le_norm _).trans (le_of_eq (norm_neg _))
    refine (Real.exp_le_exp.mpr (h1.trans hQ)).trans ?_
    rw [mul_add, mul_add, Real.exp_add, Real.exp_add]
    have e1 := s5r58q_explog hκ0 (norm_nonneg z₁) hn₁
    have e2 := s5r58q_explog hκ0 (norm_nonneg z₂) hn₂
    have e3 : Real.exp (κ * (2 * Real.log 2)) ≤ 4 := by
      have : κ * (2 * Real.log 2) ≤ 2 * Real.log 2 := by
        have := Real.log_pos (by norm_num : (1 : ℝ) < 2)
        nlinarith
      refine (Real.exp_le_exp.mpr this).trans (le_of_eq ?_)
      rw [← Real.log_rpow (by norm_num), Real.exp_log (by norm_num)]
      norm_num
    have p1 : 0 ≤ (1 - ‖z₁‖) ^ (-κ) := Real.rpow_nonneg (by linarith) _
    have p2 : 0 ≤ (1 - ‖z₂‖) ^ (-κ) := Real.rpow_nonneg (by linarith) _
    calc Real.exp (κ * Real.log (1 / (1 - ‖z₁‖ ^ 2))) * Real.exp (κ * Real.log (1 / (1 - ‖z₂‖ ^ 2))) *
          Real.exp (κ * (2 * Real.log 2))
        ≤ (1 - ‖z₁‖) ^ (-κ) * (1 - ‖z₂‖) ^ (-κ) * 4 := by
          gcongr
      _ = 4 * (1 - ‖z₁‖) ^ (-κ) * (1 - ‖z₂‖) ^ (-κ) := by ring
  have _hκ1 := hκ1
  calc ‖-(z₁ * z₁)⁻¹ * exp (-S₁₁)‖ * ‖-(z₂ * z₂)⁻¹ * exp (-S₂₂)‖ * ‖z₁ - z₂‖ ^ 2
      = ‖(f z₁)⁻¹ - (f z₂)⁻¹‖ ^ 2 * ‖exp (-(S₁₁ + S₂₂ - S₁₂ - S₂₁))‖ := by
        simp only [norm_mul]; exact hnorm
    _ ≤ ‖(f z₁)⁻¹ - (f z₂)⁻¹‖ ^ 2 * (4 * (1 - ‖z₁‖) ^ (-κ) * (1 - ‖z₂‖) ^ (-κ)) :=
        mul_le_mul_of_nonneg_left hE (by positivity)
    _ = _ := by ring

/-- The punctured unit disc is connected (polar image of `(0, 1) × ℝ`). -/
theorem s5r58_punct_conn : IsConnected (ball (0 : ℂ) 1 \ {0}) := by
  have h : (fun p : ℝ × ℝ => (p.1 : ℂ) * exp (p.2 * I)) '' (Ioo (0 : ℝ) 1 ×ˢ univ) = ball (0 : ℂ) 1 \ {0} := by
    ext z
    constructor
    · rintro ⟨p, ⟨hp1, -⟩, rfl⟩
      have hn : ‖(p.1 : ℂ) * exp (p.2 * I)‖ = p.1 := by
        rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
          Real.norm_of_nonneg hp1.1.le]
      refine ⟨mem_ball_zero_iff.mpr (by rw [hn]; exact hp1.2), fun h0 => ?_⟩
      have := congrArg norm (mem_singleton_iff.mp h0)
      rw [hn, norm_zero] at this
      linarith [hp1.1]
    · rintro ⟨hz1, hz0⟩
      refine ⟨(‖z‖, arg z), ⟨⟨norm_pos_iff.mpr hz0, mem_ball_zero_iff.mp hz1⟩, mem_univ _⟩, ?_⟩
      exact norm_mul_exp_arg_mul_I z
  rw [← h]
  refine (isConnected_Ioo (by norm_num : (0 : ℝ) < 1)).prod isConnected_univ |>.image _ ?_
  exact (Continuous.mul (Complex.continuous_ofReal.comp continuous_fst)
    (Complex.continuous_exp.comp ((Complex.continuous_ofReal.comp continuous_snd).mul continuous_const))).continuousOn

/-- `1/f` is unbounded on the punctured disc (`f(z) → f(0) = 0`). -/
theorem s5r58_psi_unbdd {f Ψ : ℂ → ℂ} (hfd : DifferentiableOn ℂ f unitDisc) (hfi : InjOn f unitDisc)
    (hf0 : f 0 = 0) (he : ∀ z ∈ unitDisc, z ≠ 0 → Ψ z = (f z)⁻¹) :
    ¬ Bornology.IsBounded (Ψ '' (ball (0 : ℂ) 1 \ {0})) := by
  intro hb
  obtain ⟨R₀, hR₀⟩ := isBounded_iff_forall_norm_le.mp hb
  have h0 : (0 : ℂ) ∈ unitDisc := Metric.mem_ball_self one_pos
  have hfc : ContinuousAt f 0 :=
    ((hfd 0 h0).differentiableAt (Metric.isOpen_ball.mem_nhds h0)).continuousAt
  have hpos : 0 < 1 / (|R₀| + 1) := by positivity
  obtain ⟨δ, hδ, hδf⟩ := Metric.continuousAt_iff.mp hfc _ hpos
  obtain ⟨t, ht⟩ : ∃ t : ℝ, t = min (δ / 2) (1 / 2) := ⟨_, rfl⟩
  have ht0 : 0 < t := by rw [ht]; positivity
  have ht1 : t < 1 := by rw [ht]; exact (min_le_right _ _).trans_lt (by norm_num)
  have htδ : t < δ := by rw [ht]; exact (min_le_left _ _).trans_lt (by linarith)
  have hzD : ((t : ℝ) : ℂ) ∈ unitDisc := mem_ball_zero_iff.mpr (by
    rw [Complex.norm_real, Real.norm_of_nonneg ht0.le]; exact ht1)
  have hz0 : ((t : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht0.ne'
  have hfz : f t ≠ 0 := fun h => hz0 (hfi hzD h0 (h.trans hf0.symm))
  have h1 := hδf (show dist ((t : ℝ) : ℂ) 0 < δ by
    rw [dist_zero_right, Complex.norm_real, Real.norm_of_nonneg ht0.le]; exact htδ)
  rw [hf0, dist_zero_right] at h1
  have h2 := hR₀ (Ψ t) ⟨t, ⟨hzD, hz0⟩, rfl⟩
  rw [he _ hzD hz0, norm_inv] at h2
  have hfn : 0 < ‖f t‖ := norm_pos_iff.mpr hfz
  have h3 : |R₀| + 1 < ‖f t‖⁻¹ := by
    rw [lt_inv_comm₀ (by positivity) hfn]
    rwa [one_div] at h1
  linarith [le_abs_self R₀]

/-- **WQ4 step 1.** The bounded-turning curve `J = Ψ(S¹)` is a quasicircle; with `A₁` the component of `∞` (which
contains `Ψ(𝔻 ∖ 0)`) and `A₂` the bounded component (Jordan curve theorem), `thm16_2` gives a q.c. reflection. -/
theorem s5r58_wq4_refl {f Ψ : ℂ → ℂ} (hfd : DifferentiableOn ℂ f unitDisc) (hfi : InjOn f unitDisc)
    (hf0 : f 0 = 0) (hc : ContinuousOn Ψ (closedBall 0 1 \ {0})) (hi : InjOn Ψ (closedBall 0 1 \ {0}))
    (he : ∀ z ∈ unitDisc, z ≠ 0 → Ψ z = (f z)⁻¹) {M : ℝ}
    (hbt : IsBoundedTurning (toExt (Ψ '' sphere (0 : ℂ) 1)) M) :
    ∃ A₁ A₂ : Set ExtPlane, ∃ R : ExtPlane → ExtPlane,
      LiZhongQC.IsQCReflection (toExt (Ψ '' sphere (0 : ℂ) 1)) A₁ A₂ R ∧ Disjoint A₁ A₂ ∧
        Disjoint A₂ (toExt (Ψ '' sphere (0 : ℂ) 1)) ∧ extInf ∈ A₁ ∧
        ∀ z ∈ ball (0 : ℂ) 1, z ≠ 0 → ((Ψ z : ℂ) : ExtPlane) ∈ A₁ := by
  obtain ⟨J₀, hJ₀⟩ : ∃ J₀ : Set ℂ, J₀ = Ψ '' sphere (0 : ℂ) 1 := ⟨_, rfl⟩
  rw [← hJ₀] at hbt ⊢
  have hJ : IsJordanCurve (toExt J₀) := hbt.1
  have hJinf : extInf ∉ toExt J₀ := wd_n_infty_notMem_toExt
  obtain ⟨K, hK⟩ := thm18_1_quasicircle_of_boundedTurning hbt.2.1
  have hq : IsQuasicircle (toExt J₀) := ⟨K, hK _ hbt⟩
  obtain ⟨A, B, hA, hB, hAc, hBc, hAB, hAC, hBC, huniv, hAb, -⟩ := jordan_curve_theorem_complex_bounded hJ
  obtain ⟨a, ha⟩ := hAc.nonempty
  have hK' : IsCompact (A ∪ J₀) := by
    refine Metric.isCompact_of_isClosed_isBounded ?_ (hAb.union (isCompact_of_isJordanCurve_toExt hJ).isBounded)
    have hcompl : (A ∪ J₀)ᶜ = B := by
      ext z
      constructor
      · intro hz
        have hz' : z ∈ A ∪ B ∪ J₀ := huniv ▸ mem_univ z
        rcases hz' with (h' | h') | h'
        · exact absurd (Or.inl h') hz
        · exact h'
        · exact absurd (Or.inr h') hz
      · rintro hz (h' | h')
        · exact disjoint_left.1 hAB h' hz
        · exact disjoint_left.1 hBC hz h'
    rw [← isOpen_compl_iff, hcompl]
    exact hB
  have hUo : IsOpen (toExt A) := OnePoint.isOpen_image_coe.2 hA
  have hVo : IsOpen (toExt (A ∪ J₀))ᶜ := OnePoint.isOpen_compl_image_coe.2 ⟨hK'.isClosed, hK'⟩
  have hUV : Disjoint (toExt A) (toExt (A ∪ J₀))ᶜ := by
    rw [disjoint_compl_right_iff_subset]
    exact image_mono subset_union_left
  have hcov : (toExt J₀)ᶜ ⊆ toExt A ∪ (toExt (A ∪ J₀))ᶜ := by
    intro p hp
    by_cases hpK : p ∈ toExt (A ∪ J₀)
    · obtain ⟨z, hz, rfl⟩ := hpK
      rcases hz with hz | hz
      · exact Or.inl ⟨z, hz, rfl⟩
      · exact absurd ⟨z, hz, rfl⟩ hp
    · exact Or.inr hpK
  have haJ : ((a : ℂ) : ExtPlane) ∈ (toExt J₀)ᶜ := fun h' =>
    disjoint_left.1 hAC ha (coe_mem_toExt_iff.1 h')
  have hcomp : connectedComponentIn (toExt J₀)ᶜ extInf ⊆ (toExt (A ∪ J₀))ᶜ :=
    isPreconnected_connectedComponentIn.subset_right_of_subset_union hUo hVo hUV
      ((connectedComponentIn_subset _ _).trans hcov)
      ⟨extInf, mem_connectedComponentIn hJinf, wd_n_infty_notMem_toExt⟩
  have hne : connectedComponentIn (toExt J₀)ᶜ extInf ≠ connectedComponentIn (toExt J₀)ᶜ (a : ExtPlane) := by
    intro h'
    have h2 := hcomp (h' ▸ mem_connectedComponentIn haJ)
    exact h2 ⟨a, Or.inl ha, rfl⟩
  have hC : LiZhongQC.AreComplementaryComponents (toExt J₀) (connectedComponentIn (toExt J₀)ᶜ extInf)
      (connectedComponentIn (toExt J₀)ᶜ (a : ExtPlane)) :=
    ⟨hJ, extInf, hJinf, (a : ExtPlane), haJ, rfl, rfl, hne⟩
  obtain ⟨R, hR⟩ := (LiZhongQC.thm16_2 hC).1 hq
  obtain ⟨-, -, -, -, -, hA₂C, hA₁₂⟩ := s16p_basic hC
  refine ⟨_, _, R, hR, hA₁₂, hA₂C, mem_connectedComponentIn hJinf, ?_⟩
  -- `Ψ(𝔻 ∖ 0) ∪ {∞}` is a preconnected subset of `Jᶜ` containing `∞`
  have hPc := s5r58_punct_conn
  have hPsub : ball (0 : ℂ) 1 \ {0} ⊆ closedBall 0 1 \ {0} := sdiff_subset_sdiff_left ball_subset_closedBall
  have hS₀ : IsPreconnected (toExt (Ψ '' (ball (0 : ℂ) 1 \ {0}))) := by
    have h := (hPc.image Ψ (hc.mono hPsub)).image ((↑) : ℂ → ExtPlane) OnePoint.continuous_coe.continuousOn
    exact h.isPreconnected
  have hinfcl : extInf ∈ closure (toExt (Ψ '' (ball (0 : ℂ) 1 \ {0}))) :=
    extInf_mem_closure_toExt_of_not_isBounded (s5r58_psi_unbdd hfd hfi hf0 he)
  have hS : IsPreconnected (insert extInf (toExt (Ψ '' (ball (0 : ℂ) 1 \ {0})))) :=
    hS₀.subset_closure (subset_insert _ _) (insert_subset hinfcl subset_closure)
  have hSJ : insert extInf (toExt (Ψ '' (ball (0 : ℂ) 1 \ {0}))) ⊆ (toExt J₀)ᶜ := by
    rintro p (rfl | ⟨w, ⟨z, hz, rfl⟩, rfl⟩)
    · exact hJinf
    · rintro ⟨w', hw', hww⟩
      rw [hJ₀] at hw'
      obtain ⟨ζ, hζ, rfl⟩ := hw'
      have hΨ := OnePoint.coe_injective hww
      have hζs : ζ ∈ closedBall (0 : ℂ) 1 \ {0} := ⟨sphere_subset_closedBall hζ, fun h0 => by
        rw [mem_singleton_iff.mp h0, mem_sphere_zero_iff_norm, norm_zero] at hζ
        exact zero_ne_one hζ⟩
      have := hi hζs (hPsub hz) hΨ
      have h1 : ‖ζ‖ = 1 := mem_sphere_zero_iff_norm.mp hζ
      have h2 : ‖z‖ < 1 := mem_ball_zero_iff.mp hz.1
      rw [this] at h1
      linarith
  have hsub := hS.subset_connectedComponentIn (mem_insert _ _) hSJ
  intro z hz hz0
  exact hsub (mem_insert_of_mem _ ⟨Ψ z, ⟨z, ⟨hz, hz0⟩, rfl⟩, rfl⟩)

/-- Distinct angles less than `2π` apart give distinct points of `S¹`. -/
theorem s5r58_exp_ne {s t : ℝ} (h1 : 0 < s - t) (h2 : s - t < 2 * π) : exp (s * I) ≠ exp (t * I) := by
  intro h
  have h' : exp (((s - t : ℝ) : ℂ) * I) = 1 := by
    rw [Complex.ofReal_sub, sub_mul, Complex.exp_sub, h, div_self (Complex.exp_ne_zero _)]
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp h'
  have him := congrArg Complex.im hn
  simp at him
  have hπ := Real.pi_pos
  have hn0 : (0 : ℝ) < n := by
    by_contra hc
    push_neg at hc
    nlinarith
  have hn1 : (n : ℝ) < 1 := by
    by_contra hc
    push_neg at hc
    nlinarith
  have hn0' : (0 : ℤ) < n := by exact_mod_cast hn0
  have hn1' : n < (1 : ℤ) := by exact_mod_cast hn1
  omega

/-- Every point of `S¹` is `e^{it}` with `t ∈ [a, a + 2π)`. -/
theorem s5r58_angle_rep (a : ℝ) {e : ℂ} (he : ‖e‖ = 1) : ∃ t ∈ Ico a (a + 2 * π), exp (t * I) = e := by
  refine ⟨toIcoMod Real.two_pi_pos a (arg e), toIcoMod_mem_Ico _ _ _, ?_⟩
  rw [← self_sub_toIcoDiv_zsmul, zsmul_eq_mul]
  have h1 : exp ((arg e : ℂ) * I) = e := by
    have h := norm_mul_exp_arg_mul_I e
    rwa [he, Complex.ofReal_one, one_mul] at h
  have h2 : exp ((((toIcoDiv Real.two_pi_pos a (arg e) : ℤ) : ℝ) * (2 * π) : ℝ) * I) = 1 :=
    Complex.exp_eq_one_iff.mpr ⟨toIcoDiv Real.two_pi_pos a (arg e), by push_cast; ring⟩
  rw [Complex.ofReal_sub, sub_mul, Complex.exp_sub, h1, h2, div_one]

/-- **WQ3 translation.** A cross-ratio lower bound on the boundary values of `Ψ` (for angles in cyclic order) gives
bounded turning of `Ψ(S¹)` in the sense of `IsBoundedTurning` (Pommerenke Lemma 9.8 (⇐) in arc form): of the two
arcs between `w₁ = Ψ(u₁)` and `w₃ = Ψ(u₃)`, one lies in the disc of radius `(2 + 4/c₀)|w₁ - w₃|` about `w₃`. -/
theorem s5r58_bt_of_cross {Ψ : ℂ → ℂ} (hc : ContinuousOn Ψ (closedBall 0 1 \ {0}))
    (hi : InjOn Ψ (closedBall 0 1 \ {0})) {c₀ : ℝ} (hc₀ : 0 < c₀)
    (hcr : ∀ t₁ t₂ t₃ t₄ : ℝ, t₁ < t₂ → t₂ < t₃ → t₃ < t₄ → t₄ < t₁ + 2 * π →
      c₀ * ‖(Ψ (exp (t₂ * I)) - Ψ (exp (t₃ * I))) * (Ψ (exp (t₁ * I)) - Ψ (exp (t₄ * I)))‖ ≤
        ‖(Ψ (exp (t₁ * I)) - Ψ (exp (t₃ * I))) * (Ψ (exp (t₂ * I)) - Ψ (exp (t₄ * I)))‖) :
    ∃ M : ℝ, IsBoundedTurning (toExt (Ψ '' sphere (0 : ℂ) 1)) M := by
  have hπ := Real.pi_pos
  have hE1 : ∀ t : ℝ, ‖exp (t * I)‖ = 1 := fun t => Complex.norm_exp_ofReal_mul_I t
  have hsS : sphere (0 : ℂ) 1 ⊆ closedBall 0 1 \ {0} := fun e he => ⟨sphere_subset_closedBall he, fun h0 => by
    rw [mem_singleton_iff.mp h0, mem_sphere_zero_iff_norm, norm_zero] at he
    exact zero_ne_one he⟩
  have hES : ∀ t : ℝ, exp (t * I) ∈ closedBall (0 : ℂ) 1 \ {0} := fun t =>
    hsS (mem_sphere_zero_iff_norm.mpr (hE1 t))
  have hEinj : ∀ s t : ℝ, Ψ (exp (s * I)) = Ψ (exp (t * I)) → exp (s * I) = exp (t * I) :=
    fun s t h => hi (hES s) (hES t) h
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = 2 + 4 / c₀ := ⟨_, rfl⟩
  have hK2 : 2 ≤ K := by rw [hK]; linarith [div_pos (by norm_num : (0 : ℝ) < 4) hc₀]
  refine ⟨2 * K, iod_isJordanCurve_image_sphere one_pos (hc.mono hsS) (hi.mono hsS), by linarith, ?_⟩
  intro z₁ z₂ hz₁ hz₂ hne
  obtain ⟨e₁, he₁, rfl⟩ := coe_mem_toExt_iff.mp hz₁
  obtain ⟨e₃, he₃, rfl⟩ := coe_mem_toExt_iff.mp hz₂
  obtain ⟨a, -, ha⟩ := s5r58_angle_rep 0 (mem_sphere_zero_iff_norm.mp he₁)
  obtain ⟨b, hb, hbe⟩ := s5r58_angle_rep a (mem_sphere_zero_iff_norm.mp he₃)
  have hab : a < b := by
    rcases hb.1.lt_or_eq with h | h
    · exact h
    · exfalso
      apply hne
      rw [← ha, ← hbe, h]
  have hb2 : b < a + 2 * π := hb.2
  obtain ⟨d, hd⟩ : ∃ d : ℝ, d = ‖Ψ e₁ - Ψ e₃‖ := ⟨_, rfl⟩
  have hd0 : 0 < d := by rw [hd]; exact norm_pos_iff.mpr (sub_ne_zero.mpr hne)
  -- one of the two arcs stays in `closedBall (Ψ e₃) (K d)`
  have hclaim : (∀ t ∈ Ioo a b, ‖Ψ (exp (t * I)) - Ψ e₃‖ ≤ K * d) ∨
      (∀ t ∈ Ioo b (a + 2 * π), ‖Ψ (exp (t * I)) - Ψ e₃‖ ≤ K * d) := by
    by_contra hcon
    push_neg at hcon
    obtain ⟨⟨t₂, ht₂, h2⟩, ⟨t₄, ht₄, h4⟩⟩ := hcon
    have h := hcr a t₂ b t₄ ht₂.1 ht₂.2 ht₄.1 ht₄.2
    rw [ha, hbe, norm_mul, norm_mul] at h
    obtain ⟨x, hx⟩ : ∃ x : ℝ, x = ‖Ψ (exp (t₂ * I)) - Ψ e₃‖ := ⟨_, rfl⟩
    obtain ⟨y, hy⟩ : ∃ y : ℝ, y = ‖Ψ (exp (t₄ * I)) - Ψ e₃‖ := ⟨_, rfl⟩
    have hy1 : y - d ≤ ‖Ψ e₁ - Ψ (exp (t₄ * I))‖ := by
      have := norm_sub_le_norm_sub_add_norm_sub (Ψ (exp (t₄ * I))) (Ψ e₁) (Ψ e₃)
      rw [norm_sub_rev (Ψ (exp (t₄ * I))) (Ψ e₁)] at this
      rw [hy, hd]
      linarith
    have hxy : ‖Ψ (exp (t₂ * I)) - Ψ (exp (t₄ * I))‖ ≤ x + y := by
      have := norm_sub_le_norm_sub_add_norm_sub (Ψ (exp (t₂ * I))) (Ψ e₃) (Ψ (exp (t₄ * I)))
      rw [norm_sub_rev (Ψ e₃) (Ψ (exp (t₄ * I)))] at this
      rw [hx, hy]
      exact this
    rw [← hx, ← hd] at h
    rw [← hx] at h2
    rw [← hy] at h4
    have hKd : 2 * d ≤ K * d := by nlinarith [mul_nonneg (sub_nonneg.mpr hK2) hd0.le]
    have hx0 : 0 ≤ x := by rw [hx]; exact norm_nonneg _
    have hy0 : 0 < y := by linarith
    have hyd : 0 ≤ y - d := by linarith
    have hm : c₀ * x * (y - d) ≤ d * (x + y) := by
      calc c₀ * x * (y - d) ≤ c₀ * x * ‖Ψ e₁ - Ψ (exp (t₄ * I))‖ :=
            mul_le_mul_of_nonneg_left hy1 (mul_nonneg hc₀.le hx0)
        _ = c₀ * (x * ‖Ψ e₁ - Ψ (exp (t₄ * I))‖) := by ring
        _ ≤ d * ‖Ψ (exp (t₂ * I)) - Ψ (exp (t₄ * I))‖ := h
        _ ≤ d * (x + y) := mul_le_mul_of_nonneg_left hxy hd0.le
    have h4c : 4 / c₀ * c₀ = 4 := div_mul_cancel₀ _ hc₀.ne'
    have h5 : K * d * c₀ = 2 * d * c₀ + 4 * d := by
      rw [hK]
      calc (2 + 4 / c₀) * d * c₀ = 2 * d * c₀ + 4 / c₀ * c₀ * d := by ring
        _ = 2 * d * c₀ + 4 * d := by rw [h4c]
    rcases le_total x y with hxy' | hxy'
    · -- `y - d ≥ y/2`, so `c₀ x ≤ 4 d`
      have h1 : c₀ * x * y ≤ 4 * d * y := by
        nlinarith [mul_nonneg (mul_nonneg hc₀.le hx0) (by linarith : (0 : ℝ) ≤ y - d - y / 2)]
      have h3 : c₀ * x ≤ 4 * d := le_of_mul_le_mul_right h1 hy0
      nlinarith [mul_pos hc₀ (sub_pos.mpr h2)]
    · have hxp : 0 < x := by linarith
      have h1 : c₀ * (y - d) ≤ 2 * d := by
        have h' : c₀ * (y - d) * x ≤ 2 * d * x := by nlinarith
        exact le_of_mul_le_mul_right h' hxp
      nlinarith [mul_pos hc₀ (sub_pos.mpr h4)]
  -- the component of a point of the good arc lies on that arc
  have hgen : ∀ l r : ℝ, l < r → r < l + 2 * π →
      ((exp (l * I) = e₁ ∧ exp (r * I) = e₃) ∨ (exp (l * I) = e₃ ∧ exp (r * I) = e₁)) →
      (∀ t ∈ Ioo l r, ‖Ψ (exp (t * I)) - Ψ e₃‖ ≤ K * d) →
      ∃ p ∈ toExt (Ψ '' sphere (0 : ℂ) 1) \ {((Ψ e₁ : ℂ) : ExtPlane), ((Ψ e₃ : ℂ) : ExtPlane)},
        extInf ∉ connectedComponentIn (toExt (Ψ '' sphere (0 : ℂ) 1) \
          {((Ψ e₁ : ℂ) : ExtPlane), ((Ψ e₃ : ℂ) : ExtPlane)}) p ∧
        Metric.ediam {z : ℂ | (z : ExtPlane) ∈ connectedComponentIn (toExt (Ψ '' sphere (0 : ℂ) 1) \
          {((Ψ e₁ : ℂ) : ExtPlane), ((Ψ e₃ : ℂ) : ExtPlane)}) p} ≤
            ENNReal.ofReal (2 * K * ‖Ψ e₁ - Ψ e₃‖) := by
    intro l r hlr hr2 hends hgood
    have hlr' : exp (l * I) = e₁ ∨ exp (l * I) = e₃ := by rcases hends with h | h <;> simp [h.1]
    have hrr' : exp (r * I) = e₁ ∨ exp (r * I) = e₃ := by rcases hends with h | h <;> simp [h.2]
    -- compact closed arcs
    have hcpt : ∀ x y : ℝ, IsCompact (Ψ '' ((fun t : ℝ => exp (t * I)) '' Icc x y)) := fun x y =>
      ((isCompact_Icc.image (by fun_prop)).image_of_continuousOn
        (hc.mono (by rintro e ⟨t, -, rfl⟩; exact hES t)))
    obtain ⟨u, hu⟩ : ∃ u : Set ExtPlane, u = (toExt (Ψ '' ((fun t : ℝ => exp (t * I)) '' Icc r (l + 2 * π))))ᶜ :=
      ⟨_, rfl⟩
    obtain ⟨v, hv⟩ : ∃ v : Set ExtPlane, v = (toExt (Ψ '' ((fun t : ℝ => exp (t * I)) '' Icc l r)))ᶜ := ⟨_, rfl⟩
    have huo : IsOpen u := by
      rw [hu]
      exact OnePoint.isOpen_compl_image_coe.2 ⟨(hcpt _ _).isClosed, hcpt _ _⟩
    have hvo : IsOpen v := by
      rw [hv]
      exact OnePoint.isOpen_compl_image_coe.2 ⟨(hcpt _ _).isClosed, hcpt _ _⟩
    -- classification of the points of `J ∖ {w₁, w₃}`
    have hclass : ∀ q ∈ toExt (Ψ '' sphere (0 : ℂ) 1) \ {((Ψ e₁ : ℂ) : ExtPlane), ((Ψ e₃ : ℂ) : ExtPlane)},
        (q ∈ u ∧ q ∉ v ∧ ∃ t ∈ Ioo l r, q = ((Ψ (exp (t * I)) : ℂ) : ExtPlane)) ∨ (q ∈ v ∧ q ∉ u) := by
      rintro q ⟨⟨w, ⟨e, he, rfl⟩, rfl⟩, hq⟩
      obtain ⟨t, ht, rfl⟩ := s5r58_angle_rep l (mem_sphere_zero_iff_norm.mp he)
      have hne1 : exp (t * I) ≠ e₁ := fun h => hq (by rw [h]; simp)
      have hne3 : exp (t * I) ≠ e₃ := fun h => hq (by rw [h]; simp)
      have htl : t ≠ l := fun h => by
        rw [h] at hne1 hne3
        rcases hlr' with h' | h'
        · exact hne1 h'
        · exact hne3 h'
      have htr : t ≠ r := fun h => by
        rw [h] at hne1 hne3
        rcases hrr' with h' | h'
        · exact hne1 h'
        · exact hne3 h'
      have htl' : l < t := lt_of_le_of_ne ht.1 (Ne.symm htl)
      rcases lt_or_gt_of_ne htr with h | h
      · refine Or.inl ⟨?_, fun hv' => ?_, t, ⟨htl', h⟩, rfl⟩
        · rw [hu]
          rintro ⟨w', ⟨e', ⟨s, hs, rfl⟩, rfl⟩, hw'⟩
          have := hEinj _ _ (OnePoint.coe_injective hw')
          exact s5r58_exp_ne (by linarith [hs.1]) (by linarith [hs.2]) this
        · rw [hv] at hv'
          exact hv' ⟨_, ⟨_, ⟨t, ⟨htl'.le, h.le⟩, rfl⟩, rfl⟩, rfl⟩
      · refine Or.inr ⟨?_, fun hu' => ?_⟩
        · rw [hv]
          rintro ⟨w', ⟨e', ⟨s, hs, rfl⟩, rfl⟩, hw'⟩
          have := hEinj _ _ (OnePoint.coe_injective hw')
          exact s5r58_exp_ne (by linarith [hs.2]) (by linarith [hs.1, ht.2]) this.symm
        · rw [hu] at hu'
          exact hu' ⟨_, ⟨_, ⟨t, ⟨h.le, ht.2.le⟩, rfl⟩, rfl⟩, rfl⟩
    -- the midpoint of the good arc
    obtain ⟨m, hm⟩ : ∃ m : ℝ, m = (l + r) / 2 := ⟨_, rfl⟩
    have hm1 : l < m := by rw [hm]; linarith
    have hm2 : m < r := by rw [hm]; linarith
    have hmne : ∀ s : ℝ, (s = l ∨ s = r) → exp (m * I) ≠ exp (s * I) := by
      rintro s (rfl | rfl)
      · exact s5r58_exp_ne (by linarith) (by linarith)
      · exact fun h => s5r58_exp_ne (by linarith) (by linarith) h.symm
    have hpm : ((Ψ (exp (m * I)) : ℂ) : ExtPlane) ∈ toExt (Ψ '' sphere (0 : ℂ) 1) \
        {((Ψ e₁ : ℂ) : ExtPlane), ((Ψ e₃ : ℂ) : ExtPlane)} := by
      refine ⟨⟨_, ⟨_, mem_sphere_zero_iff_norm.mpr (hE1 m), rfl⟩, rfl⟩, ?_⟩
      rintro (h | h)
      · have h' := hi (hES m) (hsS he₁) (OnePoint.coe_injective h)
        rcases hends with ⟨h1, -⟩ | ⟨-, h1⟩
        · exact hmne l (Or.inl rfl) (h'.trans h1.symm)
        · exact hmne r (Or.inr rfl) (h'.trans h1.symm)
      · have h' := hi (hES m) (hsS he₃) (OnePoint.coe_injective h)
        rcases hends with ⟨-, h1⟩ | ⟨h1, -⟩
        · exact hmne r (Or.inr rfl) (h'.trans h1.symm)
        · exact hmne l (Or.inl rfl) (h'.trans h1.symm)
    refine ⟨_, hpm, fun hinf => ?_, ?_⟩
    · obtain ⟨⟨w, -, hw⟩, -⟩ := connectedComponentIn_subset _ _ hinf
      exact OnePoint.coe_ne_infty w hw
    -- the component lies in `u`
    have hsub : connectedComponentIn (toExt (Ψ '' sphere (0 : ℂ) 1) \
        {((Ψ e₁ : ℂ) : ExtPlane), ((Ψ e₃ : ℂ) : ExtPlane)}) ((Ψ (exp (m * I)) : ℂ) : ExtPlane) ⊆ u := by
      have hpc := (isPreconnected_connectedComponentIn (F := toExt (Ψ '' sphere (0 : ℂ) 1) \
        {((Ψ e₁ : ℂ) : ExtPlane), ((Ψ e₃ : ℂ) : ExtPlane)}) (x := ((Ψ (exp (m * I)) : ℂ) : ExtPlane)))
      rcases isPreconnected_iff_subset_of_disjoint.mp hpc u v huo hvo
        (fun q hq => by
          rcases hclass q (connectedComponentIn_subset _ _ hq) with h | h
          · exact Or.inl h.1
          · exact Or.inr h.1)
        (by
          ext q
          simp only [mem_inter_iff, mem_empty_iff_false, iff_false, not_and]
          intro hq hqu hqv
          rcases hclass q (connectedComponentIn_subset _ _ hq) with h | h
          · exact h.2.1 hqv
          · exact h.2 hqu) with h | h
      · exact h
      · exfalso
        have hpv := h (mem_connectedComponentIn hpm)
        rw [hv] at hpv
        exact hpv ⟨_, ⟨_, ⟨m, ⟨hm1.le, hm2.le⟩, rfl⟩, rfl⟩, rfl⟩
    -- every point of the component is within `K d` of `w₃`
    have hball : ∀ z : ℂ, (z : ExtPlane) ∈ connectedComponentIn (toExt (Ψ '' sphere (0 : ℂ) 1) \
        {((Ψ e₁ : ℂ) : ExtPlane), ((Ψ e₃ : ℂ) : ExtPlane)}) ((Ψ (exp (m * I)) : ℂ) : ExtPlane) →
        ‖z - Ψ e₃‖ ≤ K * d := by
      intro z hz
      rcases hclass _ (connectedComponentIn_subset _ _ hz) with ⟨-, -, t, ht, htz⟩ | ⟨-, hzu⟩
      · rw [OnePoint.coe_injective htz]
        exact hgood t ht
      · exact absurd (hsub hz) hzu
    refine Metric.ediam_le fun z hz z' hz' => ?_
    rw [edist_dist, dist_eq_norm]
    apply ENNReal.ofReal_le_ofReal
    have h1 := hball z hz
    have h2 := hball z' hz'
    have := norm_sub_le_norm_sub_add_norm_sub z (Ψ e₃) z'
    rw [norm_sub_rev (Ψ e₃) z'] at this
    rw [← hd]
    linarith
  rcases hclaim with h | h
  · exact hgen a b hab hb2 (Or.inl ⟨ha, hbe⟩) h
  · have h2π : exp (((a + 2 * π : ℝ) : ℂ) * I) = e₁ := by
      rw [Complex.ofReal_add, add_mul, Complex.exp_add, ha]
      have : exp (((2 * π : ℝ) : ℂ) * I) = 1 := Complex.exp_eq_one_iff.mpr ⟨1, by push_cast; ring⟩
      rw [this, mul_one]
    exact hgen b (a + 2 * π) hb2 (by linarith) (Or.inr ⟨hbe, h2π⟩) h

/-- IVT for a radial length: if `0 < β ≤ ∫_a^1 g` with `g ≥ 0` integrable, some `ρ ∈ [a, 1)` has `∫_ρ^1 g = β`. -/
theorem s5r58q_ivt {g : ℝ → ℝ} {a β : ℝ} (ha : a ≤ 1) (hI : IntervalIntegrable g volume a 1)
    (hβ0 : 0 < β) (hβ : β ≤ ∫ r in a..1, g r) :
    ∃ ρ ∈ Icc a 1, ρ < 1 ∧ ∫ r in ρ..1, g r = β := by
  have hcb : ContinuousOn (fun x => ∫ r in x..1, g r) (Icc a 1) := by
    have h := intervalIntegral.continuousOn_primitive_interval_left (μ := volume) (f := g) (a := a) (b := 1)
      ((intervalIntegrable_iff_integrableOn_Icc_of_le ha).mp hI |>.mono_set (by rw [uIcc_of_le ha]))
    rwa [uIcc_of_le ha] at h
  obtain ⟨ρ, hρ, hρβ⟩ := intermediate_value_Icc' ha hcb
    (show β ∈ Icc (∫ r in (1 : ℝ)..1, g r) (∫ r in a..1, g r) by
      rw [intervalIntegral.integral_same]
      exact ⟨hβ0.le, hβ⟩)
  beta_reduce at hρβ
  refine ⟨ρ, hρ, ?_, hρβ⟩
  rcases hρ.2.lt_or_eq with h | h
  · exact h
  · rw [h, intervalIntegral.integral_same] at hρβ
    linarith

/-- The lower radial bound: `|k'| ≥ (1 - |z|)^κ` gives `∫_ρ^1 |k'(r u)| dr ≥ (1 - ρ)^{1+κ}/(1 + κ)`. -/
theorem s5r58q_lowint {k : ℂ → ℂ} {κ : ℝ} (hκ0 : 0 ≤ κ)
    (hlb : ∀ z : ℂ, 1 / 2 ≤ ‖z‖ → ‖z‖ < 1 → (1 - ‖z‖) ^ κ ≤ ‖deriv k z‖)
    {u : ℂ} (hu : ‖u‖ = 1) {ρ : ℝ} (hρ : 1 / 2 ≤ ρ) (hρ1 : ρ ≤ 1)
    (hI : IntervalIntegrable (fun r : ℝ => ‖deriv k ((r : ℂ) * u)‖) volume ρ 1) :
    (1 - ρ) ^ (1 + κ) / (1 + κ) ≤ ∫ r in ρ..1, ‖deriv k ((r : ℂ) * u)‖ := by
  obtain ⟨hJ, hJv⟩ := s5r58q_int_rpow (κ := -κ) (by linarith) hρ1
  simp only [neg_neg, sub_neg_eq_add] at hJ hJv
  rw [← hJv]
  refine intervalIntegral.integral_mono_on_of_le_Ioo hρ1 hJ hI fun r hr => ?_
  have hn : ‖(r : ℂ) * u‖ = r := by
    rw [norm_mul, hu, mul_one, Complex.norm_real, Real.norm_of_nonneg (by linarith [hr.1])]
  have h := hlb _ (by rw [hn]; linarith [hr.1]) (by rw [hn]; exact hr.2)
  rwa [hn] at h

/-- **Uniform separation (Pommerenke (9.4.13), disc form).** For `0 ≤ κ < 1`, `A ≥ 0` there is `c > 0` such that
every `k` continuous on `𝔻̄ ∖ 0` with `(1 - |z|)^κ ≤ |k'| ≤ 4 (1 - |z|)^{-κ}` and the two-point bound (constant `A`)
on `1/2 ≤ |z| < 1` separates circle points at distance `≥ √2`: `|k(u₁) - k(u₂)| ≥ c`. -/
theorem s5r58q_sep {κ A : ℝ} (hκ0 : 0 ≤ κ) (hκ1 : κ < 1) (hA : 0 ≤ A) :
    ∃ c : ℝ, 0 < c ∧ ∀ k : ℂ → ℂ, ContinuousOn k (closedBall 0 1 \ {0}) →
      (∀ z : ℂ, 1 / 2 ≤ ‖z‖ → ‖z‖ < 1 → DifferentiableAt ℂ k z) →
      (∀ z : ℂ, 1 / 2 ≤ ‖z‖ → ‖z‖ < 1 → (1 - ‖z‖) ^ κ ≤ ‖deriv k z‖) →
      (∀ z : ℂ, 1 / 2 ≤ ‖z‖ → ‖z‖ < 1 → ‖deriv k z‖ ≤ 4 * (1 - ‖z‖) ^ (-κ)) →
      (∀ z₁ z₂ : ℂ, 1 / 2 ≤ ‖z₁‖ → ‖z₁‖ < 1 → 1 / 2 ≤ ‖z₂‖ → ‖z₂‖ < 1 → z₁ ≠ z₂ →
        ‖deriv k z₁‖ * ‖deriv k z₂‖ * ‖z₁ - z₂‖ ^ 2 ≤
          A * (1 - ‖z₁‖) ^ (-κ) * (1 - ‖z₂‖) ^ (-κ) * ‖k z₁ - k z₂‖ ^ 2) →
      ∀ u₁ u₂ : ℂ, ‖u₁‖ = 1 → ‖u₂‖ = 1 → 2 ≤ ‖u₁ - u₂‖ ^ 2 → c ≤ ‖k u₁ - k u₂‖ := by
  have hκ' : 0 < 1 - κ := by linarith
  have hκ1' : 0 < 1 + κ := by linarith
  obtain ⟨L, hL⟩ : ∃ L : ℝ, L = (1 / 2 : ℝ) ^ (1 + κ) / (1 + κ) := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B : ℝ, B = 225 * A / (4 * (1 - κ) ^ 2) + 1 := ⟨_, rfl⟩
  have hB1 : 1 ≤ B := by rw [hB]; have : 0 ≤ 225 * A / (4 * (1 - κ) ^ 2) := by positivity
                         linarith
  obtain ⟨e, he⟩ : ∃ e : ℝ, e = 2 * (1 - κ) := ⟨_, rfl⟩
  have he0 : 0 < e := by rw [he]; linarith
  obtain ⟨c₁, hc₁⟩ : ∃ c₁ : ℝ, c₁ = (B⁻¹ ^ e⁻¹) ^ (1 + κ) / (1 + κ) := ⟨_, rfl⟩
  have hL0 : 0 < L := by rw [hL]; positivity
  have hc₁0 : 0 < c₁ := by
    rw [hc₁]
    have : 0 < B⁻¹ ^ e⁻¹ := Real.rpow_pos_of_pos (inv_pos.mpr (by linarith)) _
    positivity
  refine ⟨min L c₁, lt_min hL0 hc₁0, fun k hc hdiff hlb hub htp u₁ u₂ hu₁ hu₂ hd => ?_⟩
  have hne : ∀ z : ℂ, 1 / 2 ≤ ‖z‖ → ‖z‖ < 1 → deriv k z ≠ 0 := fun z h1 h2 h0 => by
    have := hlb z h1 h2
    rw [h0, norm_zero] at this
    have : 0 < (1 - ‖z‖) ^ κ := Real.rpow_pos_of_pos (by linarith) _
    linarith
  have h12 : u₁ ≠ u₂ := fun h => by rw [h, sub_self, norm_zero] at hd; norm_num at hd
  obtain ⟨b, hb⟩ : ∃ b, b = ‖k u₁ - k u₂‖ := ⟨_, rfl⟩
  have hb0 : 0 < b := hb ▸ norm_pos_iff.mpr (sub_ne_zero.mpr (s5r58q_core hκ0 hκ1 hA hc hdiff hne hub htp hu₁ hu₂ h12))
  rw [← hb]
  by_cases hbL : L ≤ b
  · exact (min_le_left _ _).trans hbL
  push_neg at hbL
  refine (min_le_right _ _).trans ?_
  have hn : ∀ (x : ℝ) (u : ℂ), ‖u‖ = 1 → 0 ≤ x → ‖(x : ℂ) * u‖ = x := fun x u hu hx => by
    rw [norm_mul, hu, mul_one, Complex.norm_real, Real.norm_of_nonneg hx]
  have hdist : ∀ (x : ℝ) (u : ℂ), ‖u‖ = 1 → x ≤ 1 → ‖(x : ℂ) * u - u‖ = 1 - x := fun x u hu hx => by
    have : (x : ℂ) * u - u = ((x - 1 : ℝ) : ℂ) * u := by push_cast; ring
    rw [this, norm_mul, hu, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (by linarith)]
    ring
  -- equal radial lengths `b` on both rays
  have hhalf : (1 / 2 : ℝ) ≤ 1 := by norm_num
  obtain ⟨hIh₁, -, -, -⟩ := s5r58q_radial hκ1 hc hdiff hne hub hu₁ (le_refl _) hhalf
  obtain ⟨hIh₂, -, -, -⟩ := s5r58q_radial hκ1 hc hdiff hne hub hu₂ (le_refl _) hhalf
  have hLh : ∀ u : ℂ, ‖u‖ = 1 → IntervalIntegrable (fun r : ℝ => ‖deriv k ((r : ℂ) * u)‖) volume (1 / 2) 1 →
      L ≤ ∫ r in (1 / 2 : ℝ)..1, ‖deriv k ((r : ℂ) * u)‖ := fun u hu hI => by
    have h := s5r58q_lowint hκ0 hlb hu (le_refl _) hhalf hI
    rw [hL]
    convert h using 2
    norm_num
  obtain ⟨ρ₁, hρ₁, hρ₁1, hρ₁b⟩ := s5r58q_ivt hhalf hIh₁ hb0 (hbL.le.trans (hLh u₁ hu₁ hIh₁))
  obtain ⟨ρ₂, hρ₂, hρ₂1, hρ₂b⟩ := s5r58q_ivt hhalf hIh₂ hb0 (hbL.le.trans (hLh u₂ hu₂ hIh₂))
  obtain ⟨hI₁, -, -, -⟩ := s5r58q_radial hκ1 hc hdiff hne hub hu₁ hρ₁.1 hρ₁.2
  obtain ⟨hI₂, -, -, -⟩ := s5r58q_radial hκ1 hc hdiff hne hub hu₂ hρ₂.1 hρ₂.2
  have hu7 : 7 / 5 ≤ ‖u₁ - u₂‖ := by nlinarith [norm_nonneg (u₁ - u₂)]
  -- the box bound
  have hbox : ∀ r₁ ∈ Ioo ρ₁ 1, ∀ r₂ ∈ Ioo ρ₂ 1,
      ‖deriv k ((r₁ : ℂ) * u₁)‖ * ‖deriv k ((r₂ : ℂ) * u₂)‖ ≤
        225 * A * b ^ 2 / 4 * (1 - r₁) ^ (-κ) * (1 - r₂) ^ (-κ) := by
    intro r₁ hr₁ r₂ hr₂
    have hr₁a : 1 / 2 ≤ r₁ := hρ₁.1.trans hr₁.1.le
    have hr₂a : 1 / 2 ≤ r₂ := hρ₂.1.trans hr₂.1.le
    have hn₁ := hn r₁ u₁ hu₁ (by linarith)
    have hn₂ := hn r₂ u₂ hu₂ (by linarith)
    have hsep : 2 / 5 ≤ ‖(r₁ : ℂ) * u₁ - (r₂ : ℂ) * u₂‖ := by
      have e1 := hdist r₁ u₁ hu₁ hr₁.2.le
      have e2 := hdist r₂ u₂ hu₂ hr₂.2.le
      have ht : ‖u₁ - u₂‖ ≤ ‖(r₁ : ℂ) * u₁ - u₁‖ + ‖(r₁ : ℂ) * u₁ - (r₂ : ℂ) * u₂‖ + ‖(r₂ : ℂ) * u₂ - u₂‖ := by
        calc ‖u₁ - u₂‖ = ‖-((r₁ : ℂ) * u₁ - u₁) + ((r₁ : ℂ) * u₁ - (r₂ : ℂ) * u₂) + ((r₂ : ℂ) * u₂ - u₂)‖ := by
              congr 1; ring
          _ ≤ ‖-((r₁ : ℂ) * u₁ - u₁)‖ + ‖(r₁ : ℂ) * u₁ - (r₂ : ℂ) * u₂‖ + ‖(r₂ : ℂ) * u₂ - u₂‖ :=
              norm_add₃_le
          _ = _ := by rw [norm_neg]
      rw [e1, e2] at ht
      linarith
    have hne12 : (r₁ : ℂ) * u₁ ≠ (r₂ : ℂ) * u₂ := by
      intro h
      rw [h, sub_self, norm_zero] at hsep
      linarith
    have hval : ‖k ((r₁ : ℂ) * u₁) - k ((r₂ : ℂ) * u₂)‖ ≤ 3 * b := by
      obtain ⟨-, -, hF₁, -⟩ := s5r58q_radial hκ1 hc hdiff hne hub hu₁ hr₁a hr₁.2.le
      obtain ⟨-, -, hF₂, -⟩ := s5r58q_radial hκ1 hc hdiff hne hub hu₂ hr₂a hr₂.2.le
      have hm₁ := s5r58q_antitone hr₁.1.le hr₁.2.le hI₁ fun x => norm_nonneg _
      have hm₂ := s5r58q_antitone hr₂.1.le hr₂.2.le hI₂ fun x => norm_nonneg _
      calc ‖k ((r₁ : ℂ) * u₁) - k ((r₂ : ℂ) * u₂)‖
          = ‖-(k u₁ - k ((r₁ : ℂ) * u₁)) + (k u₁ - k u₂) + (k u₂ - k ((r₂ : ℂ) * u₂))‖ := by congr 1; ring
        _ ≤ ‖-(k u₁ - k ((r₁ : ℂ) * u₁))‖ + ‖k u₁ - k u₂‖ + ‖k u₂ - k ((r₂ : ℂ) * u₂)‖ := norm_add₃_le
        _ ≤ b + b + b := by
            rw [norm_neg, ← hb]
            refine add_le_add (add_le_add ?_ le_rfl) ?_
            · rw [← hρ₁b]; exact hF₁.trans hm₁
            · rw [← hρ₂b]; exact hF₂.trans hm₂
        _ = 3 * b := by ring
    have h := htp _ _ (by rw [hn₁]; exact hr₁a) (by rw [hn₁]; exact hr₁.2) (by rw [hn₂]; exact hr₂a)
      (by rw [hn₂]; exact hr₂.2) hne12
    rw [hn₁, hn₂] at h
    have hP : 0 ≤ (1 - r₁) ^ (-κ) * (1 - r₂) ^ (-κ) :=
      mul_nonneg (Real.rpow_nonneg (by linarith [hr₁.2]) _) (Real.rpow_nonneg (by linarith [hr₂.2]) _)
    have hg0 : 0 ≤ ‖deriv k ((r₁ : ℂ) * u₁)‖ * ‖deriv k ((r₂ : ℂ) * u₂)‖ := by positivity
    have h1 : ‖deriv k ((r₁ : ℂ) * u₁)‖ * ‖deriv k ((r₂ : ℂ) * u₂)‖ * (4 / 25) ≤
        A * ((1 - r₁) ^ (-κ) * (1 - r₂) ^ (-κ)) * (9 * b ^ 2) := by
      have hs2 : 4 / 25 ≤ ‖(r₁ : ℂ) * u₁ - (r₂ : ℂ) * u₂‖ ^ 2 := by
        have := pow_le_pow_left₀ (by norm_num) hsep 2
        linarith [show ((2 : ℝ) / 5) ^ 2 = 4 / 25 by norm_num]
      have hv2 : ‖k ((r₁ : ℂ) * u₁) - k ((r₂ : ℂ) * u₂)‖ ^ 2 ≤ 9 * b ^ 2 := by
        have := pow_le_pow_left₀ (norm_nonneg _) hval 2
        linarith [show (3 * b) ^ 2 = 9 * b ^ 2 by ring]
      calc _ ≤ ‖deriv k ((r₁ : ℂ) * u₁)‖ * ‖deriv k ((r₂ : ℂ) * u₂)‖ *
            ‖(r₁ : ℂ) * u₁ - (r₂ : ℂ) * u₂‖ ^ 2 := mul_le_mul_of_nonneg_left hs2 hg0
        _ ≤ A * (1 - r₁) ^ (-κ) * (1 - r₂) ^ (-κ) * ‖k ((r₁ : ℂ) * u₁) - k ((r₂ : ℂ) * u₂)‖ ^ 2 := h
        _ = A * ((1 - r₁) ^ (-κ) * (1 - r₂) ^ (-κ)) * ‖k ((r₁ : ℂ) * u₁) - k ((r₂ : ℂ) * u₂)‖ ^ 2 := by ring
        _ ≤ A * ((1 - r₁) ^ (-κ) * (1 - r₂) ^ (-κ)) * (9 * b ^ 2) :=
            mul_le_mul_of_nonneg_left hv2 (mul_nonneg hA hP)
    refine le_of_mul_le_mul_right (h1.trans (le_of_eq ?_)) (by norm_num : (0 : ℝ) < 4 / 25)
    ring
  have hfin := s5r58q_box hκ1 hρ₁.2 hρ₂.2 hI₁ hI₂ hbox
  rw [hρ₁b, hρ₂b] at hfin
  -- `1 ≤ B X₁ X₂`
  obtain ⟨X₁, hX₁⟩ : ∃ X, X = (1 - ρ₁) ^ (1 - κ) := ⟨_, rfl⟩
  obtain ⟨X₂, hX₂⟩ : ∃ X, X = (1 - ρ₂) ^ (1 - κ) := ⟨_, rfl⟩
  rw [← hX₁, ← hX₂] at hfin
  have hX₁0 : 0 ≤ X₁ := hX₁ ▸ Real.rpow_nonneg (by linarith) _
  have hX₂0 : 0 ≤ X₂ := hX₂ ▸ Real.rpow_nonneg (by linarith) _
  have hkey : 1 ≤ B * (X₁ * X₂) := by
    have h2 : b * b ≤ b ^ 2 * (225 * A / (4 * (1 - κ) ^ 2) * (X₁ * X₂)) := by
      refine hfin.trans (le_of_eq ?_)
      field_simp
    have h3 : 1 ≤ 225 * A / (4 * (1 - κ) ^ 2) * (X₁ * X₂) := by
      have hb2 : 0 < b ^ 2 := by positivity
      nlinarith
    rw [hB]
    nlinarith [mul_nonneg hX₁0 hX₂0]
  -- the larger of `1 - ρ₁`, `1 - ρ₂`
  have hfinal : ∀ (x : ℝ) (ρ : ℝ) (u : ℂ), ‖u‖ = 1 → x = 1 - ρ → 1 / 2 ≤ ρ → ρ ≤ 1 →
      IntervalIntegrable (fun r : ℝ => ‖deriv k ((r : ℂ) * u)‖) volume ρ 1 →
      (∫ r in ρ..1, ‖deriv k ((r : ℂ) * u)‖) = b → 1 ≤ B * x ^ e → c₁ ≤ b := by
    intro x ρ u hu hx hρa hρb hI hbρ hBx
    have hx0 : 0 ≤ x := by rw [hx]; linarith
    have hlow := s5r58q_lowint hκ0 hlb hu hρa hρb hI
    rw [hbρ, ← hx] at hlow
    refine le_trans ?_ hlow
    rw [hc₁]
    refine div_le_div_of_nonneg_right ?_ hκ1'.le
    refine Real.rpow_le_rpow (Real.rpow_nonneg (by positivity) _) ?_ hκ1'.le
    have h1 : B⁻¹ ≤ x ^ e := by
      rw [inv_le_iff_one_le_mul₀ (by linarith), mul_comm]
      exact hBx
    calc B⁻¹ ^ e⁻¹ ≤ (x ^ e) ^ e⁻¹ := Real.rpow_le_rpow (by positivity) h1 (inv_nonneg.mpr he0.le)
      _ = x := Real.rpow_rpow_inv hx0 he0.ne'
  have hpow : ∀ x : ℝ, 0 ≤ x → x ^ (1 - κ) * x ^ (1 - κ) = x ^ e := fun x hx => by
    rw [← Real.rpow_add' hx (by linarith), he]
    ring_nf
  rcases le_total (1 - ρ₁) (1 - ρ₂) with h | h
  · refine hfinal (1 - ρ₂) ρ₂ u₂ hu₂ rfl hρ₂.1 hρ₂.2 hI₂ hρ₂b ?_
    have hm : X₁ ≤ X₂ := by rw [hX₁, hX₂]; exact Real.rpow_le_rpow (by linarith) h hκ'.le
    rw [← hpow _ (by linarith), ← hX₂]
    have := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hm hX₂0) (by linarith : (0 : ℝ) ≤ B)
    linarith
  · refine hfinal (1 - ρ₁) ρ₁ u₁ hu₁ rfl hρ₁.1 hρ₁.2 hI₁ hρ₁b ?_
    have hm : X₂ ≤ X₁ := by rw [hX₁, hX₂]; exact Real.rpow_le_rpow (by linarith) h hκ'.le
    rw [← hpow _ (by linarith), ← hX₁]
    have := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hm hX₁0) (by linarith : (0 : ℝ) ≤ B)
    linarith

/-- **Diameter bound** (replaces the area theorem): with `|k'| ≤ 4 (1 - |z|)^{-κ}` on `1/2 ≤ |z| < 1`,
`|k(u₁) - k(u₂)| ≤ 8/(1 - κ) + 24π` on `S¹` (radially to `|z| = 3/4`, then around that circle). -/
theorem s5r58q_diam {k : ℂ → ℂ} {κ : ℝ} (hκ0 : 0 ≤ κ) (hκ1 : κ < 1)
    (hc : ContinuousOn k (closedBall 0 1 \ {0}))
    (hdiff : ∀ z : ℂ, 1 / 2 ≤ ‖z‖ → ‖z‖ < 1 → DifferentiableAt ℂ k z)
    (hne : ∀ z : ℂ, 1 / 2 ≤ ‖z‖ → ‖z‖ < 1 → deriv k z ≠ 0)
    (hub : ∀ z : ℂ, 1 / 2 ≤ ‖z‖ → ‖z‖ < 1 → ‖deriv k z‖ ≤ 4 * (1 - ‖z‖) ^ (-κ))
    {u₁ u₂ : ℂ} (hu₁ : ‖u₁‖ = 1) (hu₂ : ‖u₂‖ = 1) :
    ‖k u₁ - k u₂‖ ≤ 8 / (1 - κ) + 24 * π := by
  have hκ' : 0 < 1 - κ := by linarith
  -- radial part
  have hrad : ∀ u : ℂ, ‖u‖ = 1 → ‖k u - k (((3 / 4 : ℝ) : ℂ) * u)‖ ≤ 4 / (1 - κ) := by
    intro u hu
    obtain ⟨-, hB, hF, -⟩ := s5r58q_radial hκ1 hc hdiff hne hub hu (by norm_num : (1 / 2 : ℝ) ≤ 3 / 4)
      (by norm_num)
    refine hF.trans (hB.trans ?_)
    have h1 : (1 - (3 / 4 : ℝ)) ^ (1 - κ) ≤ 1 := Real.rpow_le_one (by norm_num) (by norm_num) hκ'.le
    rw [mul_div_assoc']
    exact div_le_div_of_nonneg_right (by linarith) hκ'.le
  -- arc part on `|z| = 3/4`
  obtain ⟨φ, hφ⟩ : ∃ φ : ℝ → ℂ, φ = fun t : ℝ => k ((3 / 4 : ℂ) * exp ((t : ℂ) * I)) := ⟨_, rfl⟩
  have hn : ∀ t : ℝ, ‖(3 / 4 : ℂ) * exp (t * I)‖ = 3 / 4 := fun t => by
    rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one]
    norm_num
  have hder : ∀ t : ℝ, HasDerivAt φ (deriv k ((3 / 4 : ℂ) * exp (t * I)) * ((3 / 4 : ℂ) * (exp (t * I) * I))) t := by
    intro t
    have h1 : HasDerivAt (fun s : ℝ => (3 / 4 : ℂ) * exp (s * I)) ((3 / 4 : ℂ) * (exp (t * I) * I)) t := by
      have h2 := ((hasDerivAt_id (t : ℂ)).mul_const I).cexp.comp_ofReal (z := t)
      simpa using h2.const_mul (3 / 4 : ℂ)
    have h3 := (hdiff ((3 / 4 : ℂ) * exp (t * I)) (by rw [hn]; norm_num) (by rw [hn]; norm_num)).hasDerivAt.comp t h1
    rw [hφ]
    exact h3
  have hbd : ∀ t : ℝ, ‖deriv k ((3 / 4 : ℂ) * exp (t * I)) * ((3 / 4 : ℂ) * (exp (t * I) * I))‖ ≤ 12 := by
    intro t
    have h := hub ((3 / 4 : ℂ) * exp (t * I)) (by rw [hn]; norm_num) (by rw [hn]; norm_num)
    rw [hn] at h
    have h4 : (1 - (3 / 4 : ℝ)) ^ (-κ) ≤ 4 := by
      rw [show (1 - (3 / 4 : ℝ)) = 4⁻¹ by norm_num, Real.inv_rpow (by norm_num), Real.rpow_neg (by norm_num), inv_inv]
      calc (4 : ℝ) ^ κ ≤ 4 ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
        _ = 4 := Real.rpow_one 4
    rw [norm_mul, norm_mul, norm_mul, Complex.norm_exp_ofReal_mul_I, Complex.norm_I]
    have : ‖(3 / 4 : ℂ)‖ = 3 / 4 := by norm_num
    rw [this]
    nlinarith [norm_nonneg (deriv k ((3 / 4 : ℂ) * exp (t * I))), h, h4]
  have harc : ∀ s t : ℝ, ‖φ t - φ s‖ ≤ 12 * ‖t - s‖ := fun s t =>
    convex_univ.norm_image_sub_le_of_norm_hasDerivWithin_le (fun x _ => (hder x).hasDerivWithinAt)
      (fun x _ => hbd x) (mem_univ _) (mem_univ _)
  have hrep : ∀ u : ℂ, ‖u‖ = 1 → (((3 / 4 : ℝ) : ℂ) * u) = (3 / 4 : ℂ) * exp ((arg u : ℂ) * I) := by
    intro u hu
    have h := norm_mul_exp_arg_mul_I u
    rw [hu, Complex.ofReal_one, one_mul] at h
    rw [h]
    push_cast
    ring
  have hargs : ‖arg u₂ - arg u₁‖ ≤ 2 * π := by
    rw [Real.norm_eq_abs, abs_le]
    constructor <;> linarith [Complex.neg_pi_lt_arg u₁, Complex.arg_le_pi u₁, Complex.neg_pi_lt_arg u₂,
      Complex.arg_le_pi u₂]
  have hmid : ‖k (((3 / 4 : ℝ) : ℂ) * u₁) - k (((3 / 4 : ℝ) : ℂ) * u₂)‖ ≤ 24 * π := by
    rw [hrep u₁ hu₁, hrep u₂ hu₂]
    have h := harc (arg u₂) (arg u₁)
    rw [hφ] at h
    simp only at h
    rw [norm_sub_rev (arg u₁ : ℝ)] at h
    linarith [mul_le_mul_of_nonneg_left hargs (by norm_num : (0 : ℝ) ≤ 12)]
  calc ‖k u₁ - k u₂‖ = ‖(k u₁ - k (((3 / 4 : ℝ) : ℂ) * u₁)) +
        (k (((3 / 4 : ℝ) : ℂ) * u₁) - k (((3 / 4 : ℝ) : ℂ) * u₂)) - (k u₂ - k (((3 / 4 : ℝ) : ℂ) * u₂))‖ := by
        congr 1; ring
    _ ≤ ‖k u₁ - k (((3 / 4 : ℝ) : ℂ) * u₁)‖ + ‖k (((3 / 4 : ℝ) : ℂ) * u₁) - k (((3 / 4 : ℝ) : ℂ) * u₂)‖ +
        ‖k u₂ - k (((3 / 4 : ℝ) : ℂ) * u₂)‖ := norm_sub_le_of_le (norm_add_le _ _) le_rfl
    _ ≤ 4 / (1 - κ) + 24 * π + 4 / (1 - κ) := add_le_add (add_le_add (hrad u₁ hu₁) hmid) (hrad u₂ hu₂)
    _ = 8 / (1 - κ) + 24 * π := by ring

/-- **Hyperbolic two-point Golusin bound** (`n = 2`, `γ = (1, -1)`): with `Q = S₁₁ + S₂₂ - S₁₂ - S₂₁`,
`|Q| ≤ κ log (|1 - z₁ z̄₂|² / ((1 - |z₁|²)(1 - |z₂|²)))` (the Möbius-invariant `log 1/(1 - ρ²)`). -/
theorem s5r58q_twoh {C : ℕ → ℕ → ℂ} {κ : ℝ} (hκ : 0 ≤ κ)
    (hgol : ∀ (n : ℕ) (z γ : Fin n → ℂ), (∀ ν, z ν ∈ unitDisc) →
      ‖∑ μ, ∑ ν, γ μ * γ ν * ∑' q : ℕ × ℕ, C q.1 q.2 / Real.sqrt ((q.1 + 1) * (q.2 + 1)) *
          z μ ^ (q.1 + 1) * z ν ^ (q.2 + 1)‖ ≤
        κ * (∑ μ, ∑ ν, γ μ * conj (γ ν) * Complex.log (1 / (1 - z μ * conj (z ν)))).re)
    {z₁ z₂ : ℂ} (hz₁ : ‖z₁‖ < 1) (hz₂ : ‖z₂‖ < 1) :
    ‖(∑' q : ℕ × ℕ, C q.1 q.2 / Real.sqrt ((q.1 + 1) * (q.2 + 1)) * z₁ ^ (q.1 + 1) * z₁ ^ (q.2 + 1)) +
      (∑' q : ℕ × ℕ, C q.1 q.2 / Real.sqrt ((q.1 + 1) * (q.2 + 1)) * z₂ ^ (q.1 + 1) * z₂ ^ (q.2 + 1)) -
      (∑' q : ℕ × ℕ, C q.1 q.2 / Real.sqrt ((q.1 + 1) * (q.2 + 1)) * z₁ ^ (q.1 + 1) * z₂ ^ (q.2 + 1)) -
      (∑' q : ℕ × ℕ, C q.1 q.2 / Real.sqrt ((q.1 + 1) * (q.2 + 1)) * z₂ ^ (q.1 + 1) * z₁ ^ (q.2 + 1))‖ ≤
      κ * Real.log (‖1 - z₁ * conj z₂‖ ^ 2 / ((1 - ‖z₁‖ ^ 2) * (1 - ‖z₂‖ ^ 2))) := by
  have hg := hgol 2 ![z₁, z₂] ![1, -1] (by
    intro ν; fin_cases ν
    · exact mem_ball_zero_iff.mpr hz₁
    · exact mem_ball_zero_iff.mpr hz₂)
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, one_mul, mul_one,
    map_one, map_neg, neg_mul, mul_neg, neg_neg] at hg
  have hre : ∀ z : ℂ, ‖z‖ < 1 → (Complex.log (1 / (1 - z * conj z))).re = Real.log (1 / (1 - ‖z‖ ^ 2)) := by
    intro z hz
    have hz2 : ‖z‖ ^ 2 < 1 := by nlinarith [norm_nonneg z]
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
    have hc : (1 : ℂ) / (1 - ((‖z‖ ^ 2 : ℝ) : ℂ)) = ((1 / (1 - ‖z‖ ^ 2) : ℝ) : ℂ) := by push_cast; ring
    rw [hc, ← Complex.ofReal_log (div_nonneg zero_le_one (by linarith))]
    exact Complex.ofReal_re _
  have hW : 0 < ‖1 - z₁ * conj z₂‖ := by
    refine norm_pos_iff.mpr fun h => ?_
    have h1 : z₁ * conj z₂ = 1 := by linear_combination -h
    have h2 := congrArg norm h1
    rw [norm_mul, Complex.norm_conj, norm_one] at h2
    nlinarith [norm_nonneg z₁, norm_nonneg z₂, mul_lt_mul'' hz₁ hz₂ (norm_nonneg _) (norm_nonneg _)]
  have hW2 : ‖1 - z₁ * conj z₂‖ ≤ 2 := by
    refine (norm_sub_le _ _).trans ?_
    rw [norm_one, norm_mul, Complex.norm_conj]
    nlinarith [norm_nonneg z₁, norm_nonneg z₂, mul_lt_mul'' hz₁ hz₂ (norm_nonneg _) (norm_nonneg _)]
  have hconj : 1 - z₂ * conj z₁ = conj (1 - z₁ * conj z₂) := by
    simp only [map_sub, map_one, map_mul, Complex.conj_conj]; ring
  have hoff : ∀ w : ℂ, 0 < ‖w‖ → (Complex.log (1 / w)).re = -Real.log ‖w‖ := by
    intro w hw
    rw [Complex.log_re, one_div, norm_inv, Real.log_inv]
  have hL : (Complex.log (1 / (1 - z₁ * conj z₁)) + -Complex.log (1 / (1 - z₁ * conj z₂)) +
      (-Complex.log (1 / (1 - z₂ * conj z₁)) + Complex.log (1 / (1 - z₂ * conj z₂)))).re =
      Real.log (1 / (1 - ‖z₁‖ ^ 2)) + Real.log (1 / (1 - ‖z₂‖ ^ 2)) + 2 * Real.log ‖1 - z₁ * conj z₂‖ := by
    simp only [Complex.add_re, Complex.neg_re]
    rw [hre z₁ hz₁, hre z₂ hz₂, hoff _ hW, hconj, hoff _ (by rwa [Complex.norm_conj]), Complex.norm_conj]
    ring
  have hQ : (∑' q : ℕ × ℕ, C q.1 q.2 / Real.sqrt ((q.1 + 1) * (q.2 + 1)) * z₁ ^ (q.1 + 1) * z₁ ^ (q.2 + 1)) +
      (∑' q : ℕ × ℕ, C q.1 q.2 / Real.sqrt ((q.1 + 1) * (q.2 + 1)) * z₂ ^ (q.1 + 1) * z₂ ^ (q.2 + 1)) -
      (∑' q : ℕ × ℕ, C q.1 q.2 / Real.sqrt ((q.1 + 1) * (q.2 + 1)) * z₁ ^ (q.1 + 1) * z₂ ^ (q.2 + 1)) -
      (∑' q : ℕ × ℕ, C q.1 q.2 / Real.sqrt ((q.1 + 1) * (q.2 + 1)) * z₂ ^ (q.1 + 1) * z₁ ^ (q.2 + 1)) =
      (∑' q : ℕ × ℕ, C q.1 q.2 / Real.sqrt ((q.1 + 1) * (q.2 + 1)) * z₁ ^ (q.1 + 1) * z₁ ^ (q.2 + 1)) +
        -(∑' q : ℕ × ℕ, C q.1 q.2 / Real.sqrt ((q.1 + 1) * (q.2 + 1)) * z₁ ^ (q.1 + 1) * z₂ ^ (q.2 + 1)) +
        (-(∑' q : ℕ × ℕ, C q.1 q.2 / Real.sqrt ((q.1 + 1) * (q.2 + 1)) * z₂ ^ (q.1 + 1) * z₁ ^ (q.2 + 1)) +
          ∑' q : ℕ × ℕ, C q.1 q.2 / Real.sqrt ((q.1 + 1) * (q.2 + 1)) * z₂ ^ (q.1 + 1) * z₂ ^ (q.2 + 1)) := by
    ring
  rw [hQ]
  refine hg.trans ?_
  rw [hL]
  have hp₁ : 0 < 1 - ‖z₁‖ ^ 2 := by nlinarith [norm_nonneg z₁]
  have hp₂ : 0 < 1 - ‖z₂‖ ^ 2 := by nlinarith [norm_nonneg z₂]
  have _hW2 := hW2
  have hW0 : 0 < ‖1 - z₁ * conj z₂‖ ^ 2 := by positivity
  have hlog : Real.log (‖1 - z₁ * conj z₂‖ ^ 2 / ((1 - ‖z₁‖ ^ 2) * (1 - ‖z₂‖ ^ 2))) =
      Real.log (1 / (1 - ‖z₁‖ ^ 2)) + Real.log (1 / (1 - ‖z₂‖ ^ 2)) + 2 * Real.log ‖1 - z₁ * conj z₂‖ := by
    rw [Real.log_div (x := ‖1 - z₁ * conj z₂‖ ^ 2) hW0.ne' (mul_pos hp₁ hp₂).ne', Real.log_mul hp₁.ne' hp₂.ne',
      Real.log_pow, one_div, one_div, Real.log_inv, Real.log_inv]
    push_cast
    ring
  rw [hlog]

/-- The diagonal value: `f'(z) z² / f(z)² = e^{-S(z,z)}` for `z ∈ 𝔻 ∖ 0` (from `s5r58_psi_deriv`). -/
theorem s5r58q_fder {C : ℕ → ℕ → ℂ} {K : ℝ} (hK : ∀ m n, ‖C m n‖ ≤ K) {f : ℂ → ℂ}
    (hfd : DifferentiableOn ℂ f unitDisc) (hfi : InjOn f unitDisc) (hf0 : f 0 = 0)
    (hrep : ∀ z₁ ∈ unitDisc, ∀ z₂ ∈ unitDisc, z₁ ≠ 0 → z₂ ≠ 0 → z₁ ≠ z₂ → ∃ S,
      HasSum (fun q : ℕ × ℕ => C q.1 q.2 / Real.sqrt ((q.1 + 1) * (q.2 + 1)) * z₁ ^ (q.1 + 1) * z₂ ^ (q.2 + 1)) S ∧
      (f z₁ - f z₂) * z₁ * z₂ = (z₁ - z₂) * f z₁ * f z₂ * exp (-S))
    {z : ℂ} (hz : z ∈ unitDisc) (hz0 : z ≠ 0) :
    deriv f z * z ^ 2 / f z ^ 2 = exp (-∑' q : ℕ × ℕ, C q.1 q.2 / Real.sqrt ((q.1 + 1) * (q.2 + 1)) *
      z ^ (q.1 + 1) * z ^ (q.2 + 1)) := by
  have hfz : f z ≠ 0 := fun h => hz0 (hfi hz (Metric.mem_ball_self one_pos) (h.trans hf0.symm))
  have h1 := s5r58_psi_deriv hK hfd hfi hf0 hrep hz hz0
  have h2 : HasDerivAt (fun w => (f w)⁻¹) (-deriv f z / f z ^ 2) z :=
    ((hfd z hz).differentiableAt (Metric.isOpen_ball.mem_nhds hz)).hasDerivAt.inv hfz
  have h3 := h2.unique h1
  field_simp at h3 ⊢
  linear_combination -h3

/-- **Two-point bounds for `f`** on all of `𝔻`: with `E = f'(z₁) f'(z₂) (z₁ - z₂)² / (f(z₁) - f(z₂))²` and
`H = |1 - z₁ z̄₂|² / ((1 - |z₁|²)(1 - |z₂|²))`, `e^{-κ log H} ≤ |E| ≤ e^{κ log H}`. -/
theorem s5r58q_Ef {C : ℕ → ℕ → ℂ} {K κ : ℝ} (hK : ∀ m n, ‖C m n‖ ≤ K) (hκ0 : 0 ≤ κ) {f : ℂ → ℂ}
    (hfd : DifferentiableOn ℂ f unitDisc) (hfi : InjOn f unitDisc) (hf0 : f 0 = 0) (hf1 : deriv f 0 = 1)
    (hrep : ∀ z₁ ∈ unitDisc, ∀ z₂ ∈ unitDisc, z₁ ≠ 0 → z₂ ≠ 0 → z₁ ≠ z₂ → ∃ S,
      HasSum (fun q : ℕ × ℕ => C q.1 q.2 / Real.sqrt ((q.1 + 1) * (q.2 + 1)) * z₁ ^ (q.1 + 1) * z₂ ^ (q.2 + 1)) S ∧
      (f z₁ - f z₂) * z₁ * z₂ = (z₁ - z₂) * f z₁ * f z₂ * exp (-S))
    (hgol : ∀ (n : ℕ) (z γ : Fin n → ℂ), (∀ ν, z ν ∈ unitDisc) →
      ‖∑ μ, ∑ ν, γ μ * γ ν * ∑' q : ℕ × ℕ, C q.1 q.2 / Real.sqrt ((q.1 + 1) * (q.2 + 1)) *
          z μ ^ (q.1 + 1) * z ν ^ (q.2 + 1)‖ ≤
        κ * (∑ μ, ∑ ν, γ μ * conj (γ ν) * Complex.log (1 / (1 - z μ * conj (z ν)))).re)
    {z₁ z₂ : ℂ} (hz₁ : z₁ ∈ unitDisc) (hz₂ : z₂ ∈ unitDisc) (h12 : z₁ ≠ z₂) :
    Real.exp (-(κ * Real.log (‖1 - z₁ * conj z₂‖ ^ 2 / ((1 - ‖z₁‖ ^ 2) * (1 - ‖z₂‖ ^ 2))))) ≤
        ‖deriv f z₁ * deriv f z₂ * (z₁ - z₂) ^ 2 / (f z₁ - f z₂) ^ 2‖ ∧
      ‖deriv f z₁ * deriv f z₂ * (z₁ - z₂) ^ 2 / (f z₁ - f z₂) ^ 2‖ ≤
        Real.exp (κ * Real.log (‖1 - z₁ * conj z₂‖ ^ 2 / ((1 - ‖z₁‖ ^ 2) * (1 - ‖z₂‖ ^ 2)))) := by
  have hn₁ : ‖z₁‖ < 1 := mem_ball_zero_iff.mp hz₁
  have hn₂ : ‖z₂‖ < 1 := mem_ball_zero_iff.mp hz₂
  have hfne : ∀ z ∈ unitDisc, z ≠ 0 → f z ≠ 0 := fun z hz hz0 h =>
    hz0 (hfi hz (Metric.mem_ball_self one_pos) (h.trans hf0.symm))
  have hS0 : ∀ w : ℂ, (∑' q : ℕ × ℕ, C q.1 q.2 / Real.sqrt ((q.1 + 1) * (q.2 + 1)) * w ^ (q.1 + 1) *
      (0 : ℂ) ^ (q.2 + 1)) = 0 ∧ (∑' q : ℕ × ℕ, C q.1 q.2 / Real.sqrt ((q.1 + 1) * (q.2 + 1)) *
      (0 : ℂ) ^ (q.1 + 1) * w ^ (q.2 + 1)) = 0 := fun w => by
    constructor <;> simp
  -- `E = e^{-Q}` with the hyperbolic Golusin bound on `Q`
  obtain ⟨Q, hEQ, hQ⟩ : ∃ Q : ℂ, deriv f z₁ * deriv f z₂ * (z₁ - z₂) ^ 2 / (f z₁ - f z₂) ^ 2 = exp (-Q) ∧
      ‖Q‖ ≤ κ * Real.log (‖1 - z₁ * conj z₂‖ ^ 2 / ((1 - ‖z₁‖ ^ 2) * (1 - ‖z₂‖ ^ 2))) := by
    refine ⟨_, ?_, s5r58q_twoh hκ0 hgol hn₁ hn₂⟩
    by_cases hz₁0 : z₁ = 0
    · subst hz₁0
      have hz₂0 : z₂ ≠ 0 := fun h => h12 h.symm
      have hd := s5r58q_fder hK hfd hfi hf0 hrep hz₂ hz₂0
      rw [(hS0 z₂).1, (hS0 z₂).2, (hS0 0).1, hf0, hf1]
      have hf₂ := hfne z₂ hz₂ hz₂0
      simp only [add_zero, sub_zero, zero_add, zero_sub]
      rw [← hd, neg_sq, neg_sq]
      ring
    by_cases hz₂0 : z₂ = 0
    · subst hz₂0
      have hd := s5r58q_fder hK hfd hfi hf0 hrep hz₁ hz₁0
      rw [(hS0 z₁).1, (hS0 z₁).2, (hS0 0).1, hf0, hf1]
      have hf₁ := hfne z₁ hz₁ hz₁0
      simp only [add_zero, sub_zero, zero_add, zero_sub]
      rw [← hd]
      ring
    obtain ⟨S₁₂, hS₁₂, e₁₂⟩ := hrep z₁ hz₁ z₂ hz₂ hz₁0 hz₂0 h12
    obtain ⟨S₂₁, hS₂₁, e₂₁⟩ := hrep z₂ hz₂ z₁ hz₁ hz₂0 hz₁0 h12.symm
    rw [hS₁₂.tsum_eq, hS₂₁.tsum_eq]
    have hd₁ := s5r58q_fder hK hfd hfi hf0 hrep hz₁ hz₁0
    have hd₂ := s5r58q_fder hK hfd hfi hf0 hrep hz₂ hz₂0
    obtain ⟨S₁₁, hS₁₁⟩ : ∃ S, S = ∑' q : ℕ × ℕ, C q.1 q.2 / Real.sqrt ((q.1 + 1) * (q.2 + 1)) * z₁ ^ (q.1 + 1) *
        z₁ ^ (q.2 + 1) := ⟨_, rfl⟩
    obtain ⟨S₂₂, hS₂₂⟩ : ∃ S, S = ∑' q : ℕ × ℕ, C q.1 q.2 / Real.sqrt ((q.1 + 1) * (q.2 + 1)) * z₂ ^ (q.1 + 1) *
        z₂ ^ (q.2 + 1) := ⟨_, rfl⟩
    rw [← hS₁₁] at hd₁ ⊢
    rw [← hS₂₂] at hd₂ ⊢
    have hf₁ := hfne z₁ hz₁ hz₁0
    have hf₂ := hfne z₂ hz₂ hz₂0
    have hdf : f z₁ - f z₂ ≠ 0 := sub_ne_zero.mpr fun h => h12 (hfi hz₁ hz₂ h)
    have hdz : z₁ - z₂ ≠ 0 := sub_ne_zero.mpr h12
    have hD₁ : deriv f z₁ = exp (-S₁₁) * f z₁ ^ 2 / z₁ ^ 2 := by
      rw [← hd₁]; field_simp
    have hD₂ : deriv f z₂ = exp (-S₂₂) * f z₂ ^ 2 / z₂ ^ 2 := by
      rw [← hd₂]; field_simp
    have hsq : (f z₁ - f z₂) ^ 2 * (z₁ * z₂) ^ 2 = (z₁ - z₂) ^ 2 * f z₁ ^ 2 * f z₂ ^ 2 * exp (-S₁₂) * exp (-S₂₁) := by
      have e₂₁' : (f z₁ - f z₂) * z₁ * z₂ = (z₁ - z₂) * f z₁ * f z₂ * exp (-S₂₁) := by linear_combination (-1 : ℂ) * e₂₁
      calc (f z₁ - f z₂) ^ 2 * (z₁ * z₂) ^ 2 = ((f z₁ - f z₂) * z₁ * z₂) * ((f z₁ - f z₂) * z₁ * z₂) := by ring
        _ = ((z₁ - z₂) * f z₁ * f z₂ * exp (-S₁₂)) * ((z₁ - z₂) * f z₁ * f z₂ * exp (-S₂₁)) := by
          rw [← e₁₂, ← e₂₁']
        _ = _ := by ring
    have hexp : exp (-(S₁₁ + S₂₂ - S₁₂ - S₂₁)) * (exp (-S₁₂) * exp (-S₂₁)) = exp (-S₁₁) * exp (-S₂₂) := by
      rw [← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add]
      congr 1
      ring
    rw [hD₁, hD₂, div_eq_iff (pow_ne_zero 2 hdf)]
    have hz12 : (z₁ * z₂) ^ 2 ≠ 0 := pow_ne_zero 2 (mul_ne_zero hz₁0 hz₂0)
    apply mul_right_cancel₀ hz12
    calc exp (-S₁₁) * f z₁ ^ 2 / z₁ ^ 2 * (exp (-S₂₂) * f z₂ ^ 2 / z₂ ^ 2) * (z₁ - z₂) ^ 2 * (z₁ * z₂) ^ 2
        = (z₁ - z₂) ^ 2 * f z₁ ^ 2 * f z₂ ^ 2 * (exp (-S₁₁) * exp (-S₂₂)) := by field_simp
      _ = (z₁ - z₂) ^ 2 * f z₁ ^ 2 * f z₂ ^ 2 * (exp (-(S₁₁ + S₂₂ - S₁₂ - S₂₁)) * (exp (-S₁₂) * exp (-S₂₁))) := by
          rw [hexp]
      _ = exp (-(S₁₁ + S₂₂ - S₁₂ - S₂₁)) * ((f z₁ - f z₂) ^ 2 * (z₁ * z₂) ^ 2) := by rw [hsq]; ring
      _ = _ := by ring
  rw [hEQ, Complex.norm_exp]
  have h1 : -‖Q‖ ≤ (-Q).re := by rw [Complex.neg_re]; linarith [Complex.re_le_norm Q]
  have h2 : (-Q).re ≤ ‖Q‖ := (Complex.re_le_norm _).trans (le_of_eq (norm_neg Q))
  exact ⟨Real.exp_le_exp.mpr (by linarith), Real.exp_le_exp.mpr (by linarith)⟩

/-- Algebra of a disc automorphism `τ z = (a z + b)/(b̄ z + ā)`, `|b| < |a|`, with `Δ = |a|² - |b|²` and
`d(z) = b̄ z + ā`: `d ≠ 0` on `𝔻̄`, the difference quotient, the derivative, and the identities
`1 - |τ z|² = Δ (1 - |z|²)/|d(z)|²`, `1 - τ z₁ conj (τ z₂) = Δ (1 - z₁ z̄₂)/(d(z₁) conj d(z₂))`. -/
theorem s5r58q_aut {a b : ℂ} (hab : ‖b‖ < ‖a‖) :
    (∀ z : ℂ, ‖z‖ ≤ 1 → conj b * z + conj a ≠ 0) ∧
    (∀ z₁ z₂ : ℂ, conj b * z₁ + conj a ≠ 0 → conj b * z₂ + conj a ≠ 0 →
      (a * z₁ + b) / (conj b * z₁ + conj a) - (a * z₂ + b) / (conj b * z₂ + conj a) =
        ((‖a‖ ^ 2 - ‖b‖ ^ 2 : ℝ) : ℂ) * (z₁ - z₂) / ((conj b * z₁ + conj a) * (conj b * z₂ + conj a))) ∧
    (∀ z : ℂ, conj b * z + conj a ≠ 0 → HasDerivAt (fun w => (a * w + b) / (conj b * w + conj a))
      (((‖a‖ ^ 2 - ‖b‖ ^ 2 : ℝ) : ℂ) / (conj b * z + conj a) ^ 2) z) ∧
    (∀ z : ℂ, conj b * z + conj a ≠ 0 →
      1 - ‖(a * z + b) / (conj b * z + conj a)‖ ^ 2 = (‖a‖ ^ 2 - ‖b‖ ^ 2) * (1 - ‖z‖ ^ 2) / ‖conj b * z + conj a‖ ^ 2) ∧
    (∀ z₁ z₂ : ℂ, conj b * z₁ + conj a ≠ 0 → conj b * z₂ + conj a ≠ 0 →
      1 - (a * z₁ + b) / (conj b * z₁ + conj a) * conj ((a * z₂ + b) / (conj b * z₂ + conj a)) =
        ((‖a‖ ^ 2 - ‖b‖ ^ 2 : ℝ) : ℂ) * (1 - z₁ * conj z₂) /
          ((conj b * z₁ + conj a) * conj (conj b * z₂ + conj a))) := by
  have hΔ : (((‖a‖ ^ 2 - ‖b‖ ^ 2 : ℝ) : ℂ)) = a * conj a - b * conj b := by
    push_cast
    rw [Complex.mul_conj', Complex.mul_conj']
  refine ⟨fun z hz h => ?_, fun z₁ z₂ h₁ h₂ => ?_, fun z h => ?_, fun z h => ?_, fun z₁ z₂ h₁ h₂ => ?_⟩
  · have h1 : ‖conj b * z‖ < ‖conj a‖ := by
      rw [norm_mul, Complex.norm_conj, Complex.norm_conj]
      calc ‖b‖ * ‖z‖ ≤ ‖b‖ * 1 := mul_le_mul_of_nonneg_left hz (norm_nonneg _)
        _ < ‖a‖ := by rw [mul_one]; exact hab
    have h2 : conj a = -(conj b * z) := by linear_combination h
    rw [h2, norm_neg] at h1
    exact lt_irrefl _ h1
  · rw [hΔ, div_sub_div _ _ h₁ h₂]
    congr 1
    ring
  · have h1 : HasDerivAt (fun w => a * w + b) a z := by
      simpa using ((hasDerivAt_id z).const_mul a).add_const b
    have h2 : HasDerivAt (fun w => conj b * w + conj a) (conj b) z := by
      simpa using ((hasDerivAt_id z).const_mul (conj b)).add_const (conj a)
    convert h1.div h2 h using 1
    rw [hΔ]
    ring
  · have hd : 0 < ‖conj b * z + conj a‖ := norm_pos_iff.mpr h
    rw [norm_div, div_pow, eq_div_iff (by positivity), sub_mul, one_mul, div_mul_cancel₀ _ (by positivity)]
    simp only [Complex.sq_norm, Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.mul_re,
      Complex.mul_im, Complex.conj_re, Complex.conj_im]
    ring
  · rw [hΔ]
    simp only [map_div₀, map_add, map_mul, Complex.conj_conj]
    have h₂' : b * conj z₂ + a ≠ 0 := by
      intro h
      apply h₂
      have := congrArg conj h
      simpa [map_add, map_mul, Complex.conj_conj] using this
    have h₁' : z₁ * conj b + conj a ≠ 0 := by rwa [mul_comm]
    have h₂'' : conj z₂ * b + a ≠ 0 := by rwa [mul_comm]
    rw [eq_div_iff (mul_ne_zero h₁ h₂'), div_mul_div_comm, sub_mul, one_mul, div_mul_cancel₀ _ (mul_ne_zero h₁ h₂')]
    ring

/-- `exp (-(κ log (1/(1 - r²)))) ≥ (1 - r)^κ` and `exp (κ log H) ≤ 4 (1 - r₁)^{-κ} (1 - r₂)^{-κ}`. -/
theorem s5r58q_Hbound {κ : ℝ} (hκ0 : 0 ≤ κ) (hκ1 : κ < 1) {z₁ z₂ : ℂ} (h₁ : ‖z₁‖ < 1) (h₂ : ‖z₂‖ < 1) :
    Real.exp (κ * Real.log (‖1 - z₁ * conj z₂‖ ^ 2 / ((1 - ‖z₁‖ ^ 2) * (1 - ‖z₂‖ ^ 2)))) ≤
      4 * (1 - ‖z₁‖) ^ (-κ) * (1 - ‖z₂‖) ^ (-κ) := by
  have hp₁ : 0 < 1 - ‖z₁‖ ^ 2 := by nlinarith [norm_nonneg z₁]
  have hp₂ : 0 < 1 - ‖z₂‖ ^ 2 := by nlinarith [norm_nonneg z₂]
  have hW0 : 0 < ‖1 - z₁ * conj z₂‖ := by
    refine norm_pos_iff.mpr fun h => ?_
    have h1 : z₁ * conj z₂ = 1 := by linear_combination -h
    have h2 := congrArg norm h1
    rw [norm_mul, Complex.norm_conj, norm_one] at h2
    nlinarith [norm_nonneg z₁, norm_nonneg z₂, mul_lt_mul'' h₁ h₂ (norm_nonneg _) (norm_nonneg _)]
  have hW2 : ‖1 - z₁ * conj z₂‖ ≤ 2 := by
    refine (norm_sub_le _ _).trans ?_
    rw [norm_one, norm_mul, Complex.norm_conj]
    nlinarith [norm_nonneg z₁, norm_nonneg z₂, mul_lt_mul'' h₁ h₂ (norm_nonneg _) (norm_nonneg _)]
  have hlog : Real.log (‖1 - z₁ * conj z₂‖ ^ 2 / ((1 - ‖z₁‖ ^ 2) * (1 - ‖z₂‖ ^ 2))) ≤
      Real.log (1 / (1 - ‖z₁‖ ^ 2)) + Real.log (1 / (1 - ‖z₂‖ ^ 2)) + 2 * Real.log 2 := by
    rw [Real.log_div (x := ‖1 - z₁ * conj z₂‖ ^ 2) (by positivity) (mul_pos hp₁ hp₂).ne',
      Real.log_mul hp₁.ne' hp₂.ne', Real.log_pow, one_div, one_div, Real.log_inv, Real.log_inv]
    have := Real.log_le_log hW0 hW2
    push_cast
    linarith
  have e1 := s5r58q_explog hκ0 (norm_nonneg z₁) h₁
  have e2 := s5r58q_explog hκ0 (norm_nonneg z₂) h₂
  have e3 : Real.exp (κ * (2 * Real.log 2)) ≤ 4 := by
    have : κ * (2 * Real.log 2) ≤ 2 * Real.log 2 := by
      have := Real.log_pos (by norm_num : (1 : ℝ) < 2)
      nlinarith
    refine (Real.exp_le_exp.mpr this).trans (le_of_eq ?_)
    rw [← Real.log_rpow (by norm_num), Real.exp_log (by norm_num)]
    norm_num
  have p1 : 0 ≤ (1 - ‖z₁‖) ^ (-κ) := Real.rpow_nonneg (by linarith) _
  have p2 : 0 ≤ (1 - ‖z₂‖) ^ (-κ) := Real.rpow_nonneg (by linarith) _
  calc Real.exp (κ * Real.log (‖1 - z₁ * conj z₂‖ ^ 2 / ((1 - ‖z₁‖ ^ 2) * (1 - ‖z₂‖ ^ 2))))
      ≤ Real.exp (κ * Real.log (1 / (1 - ‖z₁‖ ^ 2)) + κ * Real.log (1 / (1 - ‖z₂‖ ^ 2)) +
          κ * (2 * Real.log 2)) := Real.exp_le_exp.mpr (by nlinarith [mul_le_mul_of_nonneg_left hlog hκ0])
    _ = Real.exp (κ * Real.log (1 / (1 - ‖z₁‖ ^ 2))) * Real.exp (κ * Real.log (1 / (1 - ‖z₂‖ ^ 2))) *
          Real.exp (κ * (2 * Real.log 2)) := by rw [Real.exp_add, Real.exp_add]
    _ ≤ (1 - ‖z₁‖) ^ (-κ) * (1 - ‖z₂‖) ^ (-κ) * 4 := by gcongr
    _ = 4 * (1 - ‖z₁‖) ^ (-κ) * (1 - ‖z₂‖) ^ (-κ) := by ring

/-- Möbius invariance of the hyperbolic two-point quantity `H(z₁, z₂) = |1 - z₁ z̄₂|²/((1 - |z₁|²)(1 - |z₂|²))`. -/
theorem s5r58q_Hinv {a b : ℂ} (hab : ‖b‖ < ‖a‖) {z₁ z₂ : ℂ} (h₁ : ‖z₁‖ < 1) (h₂ : ‖z₂‖ < 1) :
    ‖1 - (a * z₁ + b) / (conj b * z₁ + conj a) * conj ((a * z₂ + b) / (conj b * z₂ + conj a))‖ ^ 2 /
        ((1 - ‖(a * z₁ + b) / (conj b * z₁ + conj a)‖ ^ 2) * (1 - ‖(a * z₂ + b) / (conj b * z₂ + conj a)‖ ^ 2)) =
      ‖1 - z₁ * conj z₂‖ ^ 2 / ((1 - ‖z₁‖ ^ 2) * (1 - ‖z₂‖ ^ 2)) := by
  obtain ⟨hd, -, -, hn, hx⟩ := s5r58q_aut hab
  have hd₁ := hd z₁ h₁.le
  have hd₂ := hd z₂ h₂.le
  have hΔ : 0 < ‖a‖ ^ 2 - ‖b‖ ^ 2 := by nlinarith [norm_nonneg b]
  rw [hx z₁ z₂ hd₁ hd₂, hn z₁ hd₁, hn z₂ hd₂, norm_div, norm_mul, norm_mul, Complex.norm_conj, Complex.norm_real,
    Real.norm_of_nonneg hΔ.le]
  have p₁ : ‖conj b * z₁ + conj a‖ ≠ 0 := norm_ne_zero_iff.mpr hd₁
  have p₂ : ‖conj b * z₂ + conj a‖ ≠ 0 := norm_ne_zero_iff.mpr hd₂
  have q₁ : 1 - ‖z₁‖ ^ 2 ≠ 0 := by nlinarith [norm_nonneg z₁]
  have q₂ : 1 - ‖z₂‖ ^ 2 ≠ 0 := by nlinarith [norm_nonneg z₂]
  have hΔ' : ‖a‖ ^ 2 - ‖b‖ ^ 2 ≠ 0 := hΔ.ne'
  rw [div_pow, mul_pow, div_mul_div_comm, div_div_div_eq, div_eq_div_iff (by positivity) (by positivity)]
  ring

/-- **Renormalization (Pommerenke Lemma 9.10, two-point form).** For a disc automorphism
`τ z = (a z + b)/(b̄ z + ā)` (`|b| < |a|`), `α = τ 0`, the function `k = λ/(f ∘ τ - f(α))` (`λ = f'(α) τ'(0)`;
on `S¹`, `k = λ Ψ∘τ/(1 - f(α) Ψ∘τ)`) is continuous on `𝔻̄ ∖ 0` and satisfies, on `1/2 ≤ |z| < 1`,
`(1 - |z|)^κ ≤ |k'| ≤ 4 (1 - |z|)^{-κ}` and the two-point bound with `A = 4`, uniformly in `τ`. -/
theorem s5r58q_renorm {C : ℕ → ℕ → ℂ} {K κ : ℝ} (hK : ∀ m n, ‖C m n‖ ≤ K) (hκ0 : 0 ≤ κ) (hκ1 : κ < 1)
    {f Ψ : ℂ → ℂ} (hfd : DifferentiableOn ℂ f unitDisc) (hfi : InjOn f unitDisc) (hf0 : f 0 = 0)
    (hf1 : deriv f 0 = 1)
    (hrep : ∀ z₁ ∈ unitDisc, ∀ z₂ ∈ unitDisc, z₁ ≠ 0 → z₂ ≠ 0 → z₁ ≠ z₂ → ∃ S,
      HasSum (fun q : ℕ × ℕ => C q.1 q.2 / Real.sqrt ((q.1 + 1) * (q.2 + 1)) * z₁ ^ (q.1 + 1) * z₂ ^ (q.2 + 1)) S ∧
      (f z₁ - f z₂) * z₁ * z₂ = (z₁ - z₂) * f z₁ * f z₂ * exp (-S))
    (hgol : ∀ (n : ℕ) (z γ : Fin n → ℂ), (∀ ν, z ν ∈ unitDisc) →
      ‖∑ μ, ∑ ν, γ μ * γ ν * ∑' q : ℕ × ℕ, C q.1 q.2 / Real.sqrt ((q.1 + 1) * (q.2 + 1)) *
          z μ ^ (q.1 + 1) * z ν ^ (q.2 + 1)‖ ≤
        κ * (∑ μ, ∑ ν, γ μ * conj (γ ν) * Complex.log (1 / (1 - z μ * conj (z ν)))).re)
    (hc : ContinuousOn Ψ (closedBall 0 1 \ {0})) (hi : InjOn Ψ (closedBall 0 1 \ {0}))
    (he : ∀ z ∈ unitDisc, z ≠ 0 → Ψ z = (f z)⁻¹) {a b : ℂ} (hab : ‖b‖ < ‖a‖) :
    ∃ k : ℂ → ℂ, ∃ c : ℂ, c ≠ 0 ∧ ContinuousOn k (closedBall 0 1 \ {0}) ∧
      (∀ z : ℂ, 1 / 2 ≤ ‖z‖ → ‖z‖ < 1 → DifferentiableAt ℂ k z) ∧
      (∀ z : ℂ, 1 / 2 ≤ ‖z‖ → ‖z‖ < 1 → (1 - ‖z‖) ^ κ ≤ ‖deriv k z‖) ∧
      (∀ z : ℂ, 1 / 2 ≤ ‖z‖ → ‖z‖ < 1 → ‖deriv k z‖ ≤ 4 * (1 - ‖z‖) ^ (-κ)) ∧
      (∀ z₁ z₂ : ℂ, 1 / 2 ≤ ‖z₁‖ → ‖z₁‖ < 1 → 1 / 2 ≤ ‖z₂‖ → ‖z₂‖ < 1 → z₁ ≠ z₂ →
        ‖deriv k z₁‖ * ‖deriv k z₂‖ * ‖z₁ - z₂‖ ^ 2 ≤
          4 * (1 - ‖z₁‖) ^ (-κ) * (1 - ‖z₂‖) ^ (-κ) * ‖k z₁ - k z₂‖ ^ 2) ∧
      ∀ ζ : ℂ, ‖ζ‖ = 1 → 1 - f (b / conj a) * Ψ ((a * ζ + b) / (conj b * ζ + conj a)) ≠ 0 ∧
        k ζ = c * Ψ ((a * ζ + b) / (conj b * ζ + conj a)) /
          (1 - f (b / conj a) * Ψ ((a * ζ + b) / (conj b * ζ + conj a))) := by
  obtain ⟨hd, hdiff, hder, hn, -⟩ := s5r58q_aut hab
  obtain ⟨τ, hτ⟩ : ∃ τ : ℂ → ℂ, τ = fun z => (a * z + b) / (conj b * z + conj a) := ⟨_, rfl⟩
  have hτz : ∀ z, τ z = (a * z + b) / (conj b * z + conj a) := fun z => by rw [hτ]
  obtain ⟨Δ, hΔ⟩ : ∃ Δ : ℝ, Δ = ‖a‖ ^ 2 - ‖b‖ ^ 2 := ⟨_, rfl⟩
  have hΔ0 : 0 < Δ := by rw [hΔ]; nlinarith [norm_nonneg b]
  have ha0 : a ≠ 0 := fun h => by rw [h, norm_zero] at hab; exact (norm_nonneg b).not_gt hab
  have hca : conj a ≠ 0 := by rwa [map_ne_zero]
  have hα : τ 0 = b / conj a := by rw [hτz]; simp
  obtain ⟨α, hαdef⟩ : ∃ α, α = b / conj a := ⟨_, rfl⟩
  rw [← hαdef] at hα ⊢
  -- `τ` maps `𝔻̄` to `𝔻̄`, `𝔻` to `𝔻`, `S¹` to `S¹`; injective
  have hτn : ∀ z : ℂ, ‖z‖ ≤ 1 → 1 - ‖τ z‖ ^ 2 = Δ * (1 - ‖z‖ ^ 2) / ‖conj b * z + conj a‖ ^ 2 := fun z hz => by
    rw [hτz, hn z (hd z hz), hΔ]
  have hτD : ∀ z : ℂ, ‖z‖ < 1 → ‖τ z‖ < 1 := fun z hz => by
    have h := hτn z hz.le
    have hp : 0 < Δ * (1 - ‖z‖ ^ 2) / ‖conj b * z + conj a‖ ^ 2 := by
      have := norm_pos_iff.mpr (hd z hz.le)
      have : 0 < 1 - ‖z‖ ^ 2 := by nlinarith [norm_nonneg z]
      positivity
    nlinarith [norm_nonneg (τ z)]
  have hτS : ∀ z : ℂ, ‖z‖ = 1 → ‖τ z‖ = 1 := fun z hz => by
    have h := hτn z hz.le
    rw [hz] at h
    simp only [one_pow, sub_self, mul_zero, zero_div] at h
    have : ‖τ z‖ ^ 2 = 1 := by linarith
    nlinarith [norm_nonneg (τ z)]
  have hτinj : ∀ z₁ z₂ : ℂ, ‖z₁‖ ≤ 1 → ‖z₂‖ ≤ 1 → τ z₁ = τ z₂ → z₁ = z₂ := fun z₁ z₂ h₁ h₂ h => by
    have h' := hdiff z₁ z₂ (hd z₁ h₁) (hd z₂ h₂)
    rw [← hτz, ← hτz, h, sub_self] at h'
    have hΔc : ((‖a‖ ^ 2 - ‖b‖ ^ 2 : ℝ) : ℂ) ≠ 0 := by rw [← hΔ]; exact_mod_cast hΔ0.ne'
    have := h'.symm
    rw [div_eq_zero_iff] at this
    rcases this with h3 | h3
    · exact sub_eq_zero.mp ((mul_eq_zero.mp h3).resolve_left hΔc)
    · exact absurd h3 (mul_ne_zero (hd z₁ h₁) (hd z₂ h₂))
  have hαD : ‖α‖ < 1 := by rw [← hα]; exact hτD 0 (by simp)
  have hαmem : α ∈ unitDisc := mem_ball_zero_iff.mpr hαD
  have hmem : ∀ z : ℂ, ‖z‖ < 1 → z ∈ unitDisc := fun z hz => mem_ball_zero_iff.mpr hz
  -- `f'(α) ≠ 0`
  have hfα : deriv f α ≠ 0 := by
    by_cases hα0 : α = 0
    · rw [hα0, hf1]; exact one_ne_zero
    · intro h0
      have := s5r58q_fder hK hfd hfi hf0 hrep hαmem hα0
      rw [h0, zero_mul, zero_div] at this
      exact Complex.exp_ne_zero _ this.symm
  obtain ⟨c, hc'⟩ : ∃ c, c = deriv f α * (((Δ : ℝ) : ℂ) / (conj a) ^ 2) := ⟨_, rfl⟩
  have hc0 : c ≠ 0 := by
    rw [hc']
    exact mul_ne_zero hfα (div_ne_zero (by exact_mod_cast hΔ0.ne') (pow_ne_zero 2 hca))
  -- the renormalized function
  obtain ⟨k, hk⟩ : ∃ k : ℂ → ℂ, k = fun ζ => if ‖ζ‖ < 1 then c / (f (τ ζ) - f α) else
      c * Ψ (τ ζ) / (1 - f α * Ψ (τ ζ)) := ⟨_, rfl⟩
  have hkin : ∀ ζ : ℂ, ‖ζ‖ < 1 → k ζ = c / (f (τ ζ) - f α) := fun ζ hζ => by rw [hk]; simp [hζ]
  have hden : ∀ ζ : ℂ, ‖ζ‖ < 1 → ζ ≠ 0 → f (τ ζ) - f α ≠ 0 := fun ζ hζ h0 h => by
    have h1 := hfi (hmem _ (hτD ζ hζ)) hαmem (sub_eq_zero.mp h)
    rw [← hα] at h1
    exact h0 (hτinj ζ 0 hζ.le (by simp) h1)
  -- derivative of `k` in the open disc
  have hτd : ∀ ζ : ℂ, ‖ζ‖ ≤ 1 → HasDerivAt τ (((Δ : ℝ) : ℂ) / (conj b * ζ + conj a) ^ 2) ζ := fun ζ hζ => by
    have h := hder ζ (hd ζ hζ)
    rw [← hΔ, ← hτ] at h
    exact h
  have hkd : ∀ ζ : ℂ, ‖ζ‖ < 1 → ζ ≠ 0 → HasDerivAt k
      (-(c * (deriv f (τ ζ) * (((Δ : ℝ) : ℂ) / (conj b * ζ + conj a) ^ 2))) / (f (τ ζ) - f α) ^ 2) ζ := by
    intro ζ hζ h0
    have hev : k =ᶠ[𝓝 ζ] fun w => c * (f (τ w) - f α)⁻¹ := by
      filter_upwards [Metric.isOpen_ball.mem_nhds (mem_ball_zero_iff.mpr hζ)] with w hw
      rw [hkin w (mem_ball_zero_iff.mp hw), div_eq_mul_inv]
    have hf' : HasDerivAt f (deriv f (τ ζ)) (τ ζ) :=
      ((hfd _ (hmem _ (hτD ζ hζ))).differentiableAt (Metric.isOpen_ball.mem_nhds (hmem _ (hτD ζ hζ)))).hasDerivAt
    have hF : HasDerivAt (fun w => f (τ w) - f α) (deriv f (τ ζ) * (((Δ : ℝ) : ℂ) / (conj b * ζ + conj a) ^ 2)) ζ :=
      (hf'.comp ζ (hτd ζ hζ.le)).sub_const (f α)
    have h2 := (hF.inv (hden ζ hζ h0)).const_mul c
    refine (h2.congr_of_eventuallyEq hev).congr_deriv ?_
    ring
  have hτ0 : ∀ ζ : ℂ, ‖ζ‖ ≤ 1 → τ ζ - α = ((Δ : ℝ) : ℂ) * ζ / ((conj b * ζ + conj a) * conj a) := fun ζ hζ => by
    have h := hdiff ζ 0 (hd ζ hζ) (hd 0 (by simp))
    rw [← hτz, ← hτz, hα, ← hΔ] at h
    rw [h]
    simp
  -- `ζ² k'(ζ) = -E_f(τ ζ, α)`
  have hE1 : ∀ ζ : ℂ, ‖ζ‖ < 1 → ζ ≠ 0 → deriv k ζ * ζ ^ 2 =
      -(deriv f (τ ζ) * deriv f α * (τ ζ - α) ^ 2 / (f (τ ζ) - f α) ^ 2) := by
    intro ζ hζ h0
    rw [(hkd ζ hζ h0).deriv, hτ0 ζ hζ.le, hc']
    have h1 := hden ζ hζ h0
    have h2 := hd ζ hζ.le
    field_simp
  -- `k'(ζ₁) k'(ζ₂) (ζ₁ - ζ₂)² = E_f(τ ζ₁, τ ζ₂) (k ζ₁ - k ζ₂)²`
  have hE2 : ∀ ζ₁ ζ₂ : ℂ, ‖ζ₁‖ < 1 → ‖ζ₂‖ < 1 → ζ₁ ≠ 0 → ζ₂ ≠ 0 → ζ₁ ≠ ζ₂ →
      deriv k ζ₁ * deriv k ζ₂ * (ζ₁ - ζ₂) ^ 2 =
        deriv f (τ ζ₁) * deriv f (τ ζ₂) * (τ ζ₁ - τ ζ₂) ^ 2 / (f (τ ζ₁) - f (τ ζ₂)) ^ 2 * (k ζ₁ - k ζ₂) ^ 2 := by
    intro ζ₁ ζ₂ h₁ h₂ h₁0 h₂0 h12
    have hτ12 : τ ζ₁ - τ ζ₂ = ((Δ : ℝ) : ℂ) * (ζ₁ - ζ₂) / ((conj b * ζ₁ + conj a) * (conj b * ζ₂ + conj a)) := by
      have h := hdiff ζ₁ ζ₂ (hd ζ₁ h₁.le) (hd ζ₂ h₂.le)
      rw [← hτz, ← hτz, ← hΔ] at h
      exact h
    have hf12 : f (τ ζ₁) - f (τ ζ₂) ≠ 0 := sub_ne_zero.mpr fun h =>
      h12 (hτinj ζ₁ ζ₂ h₁.le h₂.le (hfi (hmem _ (hτD ζ₁ h₁)) (hmem _ (hτD ζ₂ h₂)) h))
    rw [(hkd ζ₁ h₁ h₁0).deriv, (hkd ζ₂ h₂ h₂0).deriv, hkin ζ₁ h₁, hkin ζ₂ h₂, hτ12]
    have d₁ := hden ζ₁ h₁ h₁0
    have d₂ := hden ζ₂ h₂ h₂0
    have e₁ := hd ζ₁ h₁.le
    have e₂ := hd ζ₂ h₂.le
    have hz : ζ₁ - ζ₂ ≠ 0 := sub_ne_zero.mpr h12
    have hΔc : ((Δ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hΔ0.ne'
    have hsub : c / (f (τ ζ₁) - f α) - c / (f (τ ζ₂) - f α) =
        c * (f (τ ζ₂) - f (τ ζ₁)) / ((f (τ ζ₁) - f α) * (f (τ ζ₂) - f α)) := by
      rw [div_sub_div _ _ d₁ d₂]; ring
    rw [hsub]
    field_simp
    ring
  -- the hyperbolic quantity at `(τ ζ, α)` is that at `(ζ, 0)`
  have hHζ : ∀ ζ : ℂ, ‖ζ‖ < 1 →
      ‖1 - τ ζ * conj α‖ ^ 2 / ((1 - ‖τ ζ‖ ^ 2) * (1 - ‖α‖ ^ 2)) = 1 / (1 - ‖ζ‖ ^ 2) := fun ζ hζ => by
    have h := s5r58q_Hinv hab (z₁ := ζ) (z₂ := 0) hζ (by simp)
    rw [← hτz, ← hτz, hα] at h
    rw [h]
    simp
  have hdenS : ∀ w : ℂ, ‖w‖ ≤ 1 → w ≠ 0 → τ w ≠ 0 → 1 - f α * Ψ (τ w) ≠ 0 := by
    intro w hw hw0 hτw h
    by_cases hα0 : α = 0
    · rw [hα0, hf0, zero_mul, sub_zero] at h; exact one_ne_zero h
    have hfα0 : f α ≠ 0 := fun h0 => hα0 (hfi hαmem (Metric.mem_ball_self one_pos) (h0.trans hf0.symm))
    have h1 : Ψ (τ w) = Ψ α := by
      rw [he α hαmem hα0]
      field_simp
      linear_combination -h
    have h2 := hi ⟨mem_closedBall_zero_iff.mpr (by
        rcases hw.lt_or_eq with h | h
        · exact (hτD w h).le
        · exact (hτS w h).le), hτw⟩
      ⟨mem_closedBall_zero_iff.mpr hαD.le, hα0⟩ h1
    rw [← hα] at h2
    exact hw0 (hτinj w 0 hw (by simp) h2)
  refine ⟨k, c, hc0, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- continuity
    intro ζ hζ
    have hζ1 : ‖ζ‖ ≤ 1 := mem_closedBall_zero_iff.mp hζ.1
    have hζ0 : ζ ≠ 0 := hζ.2
    rcases hζ1.lt_or_eq with hlt | heq
    · exact (hkd ζ hlt hζ0).continuousAt.continuousWithinAt
    · -- on `S¹`: `k = c Ψ∘τ/(1 - f(α) Ψ∘τ)` near `ζ` (away from `0` and `τ⁻¹(0)`)
      have hτζ := hτS ζ heq
      obtain ⟨T, hT⟩ : ∃ T : Set ℂ, T = closedBall 0 1 \ {0} ∩ {w | τ w ≠ 0} := ⟨_, rfl⟩
      have hτcont : ContinuousOn τ (closedBall 0 1) := fun w hw =>
        (hτd w (mem_closedBall_zero_iff.mp hw)).continuousAt.continuousWithinAt
      have hmaps : MapsTo τ T (closedBall 0 1 \ {0}) := fun w hw => by
        rw [hT] at hw
        refine ⟨mem_closedBall_zero_iff.mpr ?_, hw.2⟩
        rcases (mem_closedBall_zero_iff.mp hw.1.1).lt_or_eq with h | h
        · exact (hτD w h).le
        · exact (hτS w h).le
      have hΨτ : ContinuousWithinAt (fun w => Ψ (τ w)) T ζ :=
        (hc.comp (hτcont.mono (by rw [hT]; exact fun w hw => hw.1.1)) hmaps) ζ (by
          rw [hT]; exact ⟨hζ, by rw [Set.mem_setOf_eq, ← norm_ne_zero_iff, hτζ]; exact one_ne_zero⟩)
      have hG : ContinuousWithinAt (fun w => c * Ψ (τ w) / (1 - f α * Ψ (τ w))) T ζ :=
        (continuousWithinAt_const.mul hΨτ).div (continuousWithinAt_const.sub (continuousWithinAt_const.mul hΨτ))
          (hdenS ζ hζ1 hζ0 (by rw [← norm_ne_zero_iff, hτζ]; exact one_ne_zero))
      have heqT : EqOn k (fun w => c * Ψ (τ w) / (1 - f α * Ψ (τ w))) T := by
        intro w hw
        rw [hT] at hw
        have hw1 := mem_closedBall_zero_iff.mp hw.1.1
        have hw0 : w ≠ 0 := hw.1.2
        have hτw : τ w ≠ 0 := hw.2
        rcases hw1.lt_or_eq with h | h
        · show k w = c * Ψ (τ w) / (1 - f α * Ψ (τ w))
          rw [hkin w h]
          have hτwD := hmem _ (hτD w h)
          rw [he _ hτwD hτw]
          have hfτ : f (τ w) ≠ 0 := fun h0 => hτw (hfi hτwD (Metric.mem_ball_self one_pos) (h0.trans hf0.symm))
          have d := hden w h hw0
          field_simp
        · simp only [hk, h, lt_irrefl, if_false]
      have hζT : ζ ∈ T := by
        rw [hT]; exact ⟨hζ, by rw [Set.mem_setOf_eq, ← norm_ne_zero_iff, hτζ]; exact one_ne_zero⟩
      have hkT : ContinuousWithinAt k T ζ := hG.congr heqT (heqT hζT)
      refine hkT.mono_of_mem_nhdsWithin ?_
      rw [hT]
      refine inter_mem_nhdsWithin _ ?_
      exact (hτd ζ hζ1).continuousAt.eventually_ne (by rw [← norm_ne_zero_iff, hτζ]; exact one_ne_zero)
  · exact fun z h1 h2 => (hkd z h2 (fun h => by rw [h, norm_zero] at h1; norm_num at h1)).differentiableAt
  · intro z h1 h2
    have hz0 : z ≠ 0 := fun h => by rw [h, norm_zero] at h1; norm_num at h1
    have hτzD := hmem _ (hτD z h2)
    have hτα : τ z ≠ α := fun h => hz0 (hτinj z 0 h2.le (by simp) (h.trans hα.symm))
    obtain ⟨hlo, -⟩ := s5r58q_Ef hK hκ0 hfd hfi hf0 hf1 hrep hgol hτzD hαmem hτα
    rw [hHζ z h2] at hlo
    have h3 := congrArg norm (hE1 z h2 hz0)
    rw [norm_neg, norm_mul, norm_pow] at h3
    have hr : 0 < 1 - ‖z‖ ^ 2 := by nlinarith [norm_nonneg z]
    have hx : Real.exp (-(κ * Real.log (1 / (1 - ‖z‖ ^ 2)))) = (1 - ‖z‖ ^ 2) ^ κ := by
      rw [one_div, Real.log_inv, mul_neg, neg_neg, Real.rpow_def_of_pos hr, mul_comm]
    rw [hx] at hlo
    have hm : (1 - ‖z‖) ^ κ ≤ (1 - ‖z‖ ^ 2) ^ κ :=
      Real.rpow_le_rpow (by linarith) (by nlinarith [norm_nonneg z]) hκ0
    have hz2 : ‖z‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg z]
    have hd0 : 0 ≤ ‖deriv k z‖ := norm_nonneg _
    nlinarith
  · intro z h1 h2
    have hz0 : z ≠ 0 := fun h => by rw [h, norm_zero] at h1; norm_num at h1
    have hτzD := hmem _ (hτD z h2)
    have hτα : τ z ≠ α := fun h => hz0 (hτinj z 0 h2.le (by simp) (h.trans hα.symm))
    obtain ⟨-, hup⟩ := s5r58q_Ef hK hκ0 hfd hfi hf0 hf1 hrep hgol hτzD hαmem hτα
    rw [hHζ z h2] at hup
    have h3 := congrArg norm (hE1 z h2 hz0)
    rw [norm_neg, norm_mul, norm_pow] at h3
    have he := s5r58q_explog hκ0 (norm_nonneg z) h2
    have hz2 : 1 / 4 ≤ ‖z‖ ^ 2 := by nlinarith
    have hp : 0 ≤ (1 - ‖z‖) ^ (-κ) := Real.rpow_nonneg (by linarith) _
    nlinarith [norm_nonneg (deriv k z)]
  · intro z₁ z₂ h₁1 h₁2 h₂1 h₂2 h12
    have hz₁0 : z₁ ≠ 0 := fun h => by rw [h, norm_zero] at h₁1; norm_num at h₁1
    have hz₂0 : z₂ ≠ 0 := fun h => by rw [h, norm_zero] at h₂1; norm_num at h₂1
    have hτ12 : τ z₁ ≠ τ z₂ := fun h => h12 (hτinj z₁ z₂ h₁2.le h₂2.le h)
    obtain ⟨-, hup⟩ := s5r58q_Ef hK hκ0 hfd hfi hf0 hf1 hrep hgol (hmem _ (hτD z₁ h₁2)) (hmem _ (hτD z₂ h₂2)) hτ12
    have hH := s5r58q_Hinv hab (z₁ := z₁) (z₂ := z₂) h₁2 h₂2
    rw [← hτz, ← hτz] at hH
    rw [hH] at hup
    have hb := s5r58q_Hbound hκ0 hκ1 h₁2 h₂2
    have h3 := congrArg norm (hE2 z₁ z₂ h₁2 h₂2 hz₁0 hz₂0 h12)
    simp only [norm_mul, norm_pow] at h3
    rw [h3]
    have hq : 0 ≤ ‖k z₁ - k z₂‖ ^ 2 := by positivity
    calc ‖deriv f (τ z₁) * deriv f (τ z₂) * (τ z₁ - τ z₂) ^ 2 / (f (τ z₁) - f (τ z₂)) ^ 2‖ * ‖k z₁ - k z₂‖ ^ 2
        ≤ 4 * (1 - ‖z₁‖) ^ (-κ) * (1 - ‖z₂‖) ^ (-κ) * ‖k z₁ - k z₂‖ ^ 2 :=
          mul_le_mul_of_nonneg_right (hup.trans hb) hq
      _ = _ := rfl
  · intro ζ hζ
    have hτζ := hτS ζ hζ
    have h1 := hdenS ζ hζ.le (fun h => by rw [h, norm_zero] at hζ; exact zero_ne_one hζ)
      (by rw [← norm_ne_zero_iff, hτζ]; exact one_ne_zero)
    rw [hτz] at h1
    refine ⟨h1, ?_⟩
    rw [hk]
    simp only [hζ, lt_irrefl, if_false, hτz]

/-- The Cayley parametrization of `S¹`: `(1 + i tan θ)/(1 - i tan θ) = e^{2iθ}` for `cos θ > 0`. -/
theorem s5r58q_cayley {θ : ℝ} (hc : 0 < Real.cos θ) :
    (1 + I * (Real.tan θ : ℂ)) / (1 - I * (Real.tan θ : ℂ)) = exp ((2 * θ : ℝ) * I) := by
  have hd : (1 : ℂ) - I * (Real.tan θ : ℂ) ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
  have hc' : Complex.cos (θ : ℂ) ≠ 0 := by rw [← Complex.ofReal_cos]; exact_mod_cast hc.ne'
  rw [Complex.ofReal_tan, Complex.tan_eq_sin_div_cos] at hd ⊢
  rw [show ((2 * θ : ℝ) : ℂ) * I = (θ : ℂ) * I + (θ : ℂ) * I by push_cast; ring, Complex.exp_add,
    Complex.exp_mul_I, div_eq_iff hd]
  have hpy := Complex.sin_sq_add_cos_sq (θ : ℂ)
  have key : (Complex.cos θ + Complex.sin θ * I) * (Complex.cos θ + Complex.sin θ * I) *
      (Complex.cos θ - I * Complex.sin θ) = Complex.cos θ + I * Complex.sin θ := by
    linear_combination (Complex.cos θ + Complex.sin θ * I) * hpy -
      (Complex.cos θ + Complex.sin θ * I) * Complex.sin θ ^ 2 * Complex.I_sq
  have e1 : 1 - I * (Complex.sin θ / Complex.cos θ) = (Complex.cos θ - I * Complex.sin θ) / Complex.cos θ := by
    field_simp
  have e2 : 1 + I * (Complex.sin θ / Complex.cos θ) = (Complex.cos θ + I * Complex.sin θ) / Complex.cos θ := by
    field_simp
  rw [e1, e2, ← key]
  ring

/-- The Cayley conjugate of a real Möbius map `g(y) = (p y + q)/(r y + s)` (`p s - q r > 0`) is the disc
automorphism `(a' z + b')/(b̄' z + ā')`, `a' = -(p + s) + i (r - q)`, `b' = (p - s) - i (r + q)`. -/
theorem s5r58q_conj_cayley {p q r s : ℝ} (hdet : 0 < p * s - q * r) :
    ‖((p - s : ℝ) : ℂ) - ((r + q : ℝ) : ℂ) * I‖ < ‖((-(p + s) : ℝ) : ℂ) + ((r - q : ℝ) : ℂ) * I‖ ∧
    (∀ y : ℝ, r * y + s ≠ 0 →
      ((((-(p + s) : ℝ) : ℂ) + ((r - q : ℝ) : ℂ) * I) * ((1 + I * (y : ℂ)) / (1 - I * (y : ℂ))) +
          (((p - s : ℝ) : ℂ) - ((r + q : ℝ) : ℂ) * I)) /
        (conj (((p - s : ℝ) : ℂ) - ((r + q : ℝ) : ℂ) * I) * ((1 + I * (y : ℂ)) / (1 - I * (y : ℂ))) +
          conj (((-(p + s) : ℝ) : ℂ) + ((r - q : ℝ) : ℂ) * I)) =
        (1 + I * (((p * y + q) / (r * y + s) : ℝ) : ℂ)) / (1 - I * (((p * y + q) / (r * y + s) : ℝ) : ℂ))) ∧
    (r ≠ 0 → ((((-(p + s) : ℝ) : ℂ) + ((r - q : ℝ) : ℂ) * I) * (-1) + (((p - s : ℝ) : ℂ) - ((r + q : ℝ) : ℂ) * I)) /
        (conj (((p - s : ℝ) : ℂ) - ((r + q : ℝ) : ℂ) * I) * (-1) + conj (((-(p + s) : ℝ) : ℂ) + ((r - q : ℝ) : ℂ) * I)) =
        (1 + I * ((p / r : ℝ) : ℂ)) / (1 - I * ((p / r : ℝ) : ℂ))) := by
  have hcb : conj (((p - s : ℝ) : ℂ) - ((r + q : ℝ) : ℂ) * I) = ((p - s : ℝ) : ℂ) + ((r + q : ℝ) : ℂ) * I := by
    simp [map_sub, map_mul, Complex.conj_ofReal, Complex.conj_I]
  have hca : conj (((-(p + s) : ℝ) : ℂ) + ((r - q : ℝ) : ℂ) * I) = ((-(p + s) : ℝ) : ℂ) - ((r - q : ℝ) : ℂ) * I := by
    simp [map_add, map_mul, Complex.conj_ofReal, Complex.conj_I]; ring
  have hnorm : ∀ x y : ℝ, ‖(x : ℂ) + (y : ℂ) * I‖ ^ 2 = x ^ 2 + y ^ 2 := fun x y => by
    rw [Complex.sq_norm, Complex.normSq_apply]; simp; ring
  have hnorm' : ∀ x y : ℝ, ‖(x : ℂ) - (y : ℂ) * I‖ ^ 2 = x ^ 2 + y ^ 2 := fun x y => by
    rw [Complex.sq_norm, Complex.normSq_apply]; simp; ring
  have hlt : ‖((p - s : ℝ) : ℂ) - ((r + q : ℝ) : ℂ) * I‖ < ‖((-(p + s) : ℝ) : ℂ) + ((r - q : ℝ) : ℂ) * I‖ := by
    have h1 : ‖((p - s : ℝ) : ℂ) - ((r + q : ℝ) : ℂ) * I‖ ^ 2 < ‖((-(p + s) : ℝ) : ℂ) + ((r - q : ℝ) : ℂ) * I‖ ^ 2 := by
      rw [hnorm, hnorm']; nlinarith
    exact lt_of_pow_lt_pow_left₀ 2 (norm_nonneg _) h1
  have hd1 : ∀ y : ℝ, (1 : ℂ) - I * (y : ℂ) ≠ 0 := fun y h => by
    have := congrArg Complex.re h; simp at this
  refine ⟨hlt, fun y hy => ?_, fun hr => ?_⟩
  · have hden := (s5r58q_aut hlt).1 ((1 + I * (y : ℂ)) / (1 - I * (y : ℂ))) (by
      rw [norm_div]
      have hcj : conj ((1 : ℂ) + I * (y : ℂ)) = 1 - I * (y : ℂ) := by
        simp only [map_add, map_mul, map_one, Complex.conj_I, Complex.conj_ofReal]; ring
      have : ‖(1 : ℂ) + I * (y : ℂ)‖ = ‖(1 : ℂ) - I * (y : ℂ)‖ := by
        rw [← Complex.norm_conj ((1 : ℂ) + I * (y : ℂ)), hcj]
      rw [this, div_self (norm_ne_zero_iff.mpr (hd1 y))])
    have hy' : ((r * y + s : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hy
    have hg : (1 : ℂ) - I * (((p * y + q) / (r * y + s) : ℝ) : ℂ) ≠ 0 := hd1 _
    rw [hcb, hca] at hden ⊢
    rw [div_eq_div_iff hden hg]
    have hd1y := hd1 y
    push_cast at hy' ⊢
    field_simp
    linear_combination (-4 * (q : ℂ) * r * y * I - 4 * (p : ℂ) * r * y ^ 2 * I) * Complex.I_sq
  · have hr' : (r : ℂ) ≠ 0 := by exact_mod_cast hr
    rw [hcb, hca]
    have hden : (((p - s : ℝ) : ℂ) + ((r + q : ℝ) : ℂ) * I) * (-1) + (((-(p + s) : ℝ) : ℂ) - ((r - q : ℝ) : ℂ) * I) ≠ 0 := by
      have := (s5r58q_aut hlt).1 (-1) (by simp)
      rwa [hcb, hca] at this
    rw [div_eq_div_iff hden (hd1 _)]
    push_cast
    field_simp
    linear_combination (4 * (p : ℂ) * r) * Complex.I_sq

/-- Cross-ratio transfer through `k = c w/(1 - β w)`: separation `≥ cs` of the pairs `(1,3)`, `(2,4)` and
diameter `≤ D` of the pairs `(2,3)`, `(1,4)` give `(cs/D)² |(w₂-w₃)(w₁-w₄)| ≤ |(w₁-w₃)(w₂-w₄)|`. -/
theorem s5r58q_crossalg {c β w₁ w₂ w₃ w₄ : ℂ} {cs D : ℝ} (hc : c ≠ 0) (hcs : 0 ≤ cs) (hD : 0 < D)
    (d₁ : 1 - β * w₁ ≠ 0) (d₂ : 1 - β * w₂ ≠ 0) (d₃ : 1 - β * w₃ ≠ 0) (d₄ : 1 - β * w₄ ≠ 0)
    (h13 : cs ≤ ‖c * w₁ / (1 - β * w₁) - c * w₃ / (1 - β * w₃)‖)
    (h24 : cs ≤ ‖c * w₂ / (1 - β * w₂) - c * w₄ / (1 - β * w₄)‖)
    (h23 : ‖c * w₂ / (1 - β * w₂) - c * w₃ / (1 - β * w₃)‖ ≤ D)
    (h14 : ‖c * w₁ / (1 - β * w₁) - c * w₄ / (1 - β * w₄)‖ ≤ D) :
    cs ^ 2 / D ^ 2 * ‖(w₂ - w₃) * (w₁ - w₄)‖ ≤ ‖(w₁ - w₃) * (w₂ - w₄)‖ := by
  have hdiff : ∀ {wi wj : ℂ}, 1 - β * wi ≠ 0 → 1 - β * wj ≠ 0 →
      c * wi / (1 - β * wi) - c * wj / (1 - β * wj) = c * (wi - wj) / ((1 - β * wi) * (1 - β * wj)) :=
    fun hi hj => by rw [div_sub_div _ _ hi hj]; congr 1; ring
  rw [hdiff d₁ d₃] at h13
  rw [hdiff d₂ d₄] at h24
  rw [hdiff d₂ d₃] at h23
  rw [hdiff d₁ d₄] at h14
  obtain ⟨P, hP⟩ : ∃ P : ℝ, P = ‖(1 - β * w₁) * (1 - β * w₂) * (1 - β * w₃) * (1 - β * w₄)‖ := ⟨_, rfl⟩
  have hP0 : 0 < P := by rw [hP]; exact norm_pos_iff.mpr (by positivity)
  have hc0 : 0 < ‖c‖ := norm_pos_iff.mpr hc
  have hnum : ‖c * (w₁ - w₃) / ((1 - β * w₁) * (1 - β * w₃))‖ * ‖c * (w₂ - w₄) / ((1 - β * w₂) * (1 - β * w₄))‖ =
      ‖c‖ ^ 2 / P * ‖(w₁ - w₃) * (w₂ - w₄)‖ := by
    rw [hP]; simp only [norm_mul, norm_div]; field_simp
  have hden : ‖c * (w₂ - w₃) / ((1 - β * w₂) * (1 - β * w₃))‖ * ‖c * (w₁ - w₄) / ((1 - β * w₁) * (1 - β * w₄))‖ =
      ‖c‖ ^ 2 / P * ‖(w₂ - w₃) * (w₁ - w₄)‖ := by
    rw [hP]; simp only [norm_mul, norm_div]; field_simp
  have hΛ : 0 < ‖c‖ ^ 2 / P := by positivity
  have hlo : cs ^ 2 ≤ ‖c‖ ^ 2 / P * ‖(w₁ - w₃) * (w₂ - w₄)‖ := by
    rw [← hnum, pow_two]; exact mul_le_mul h13 h24 hcs (norm_nonneg _)
  have hhi : ‖c‖ ^ 2 / P * ‖(w₂ - w₃) * (w₁ - w₄)‖ ≤ D ^ 2 := by
    rw [← hden, pow_two]; exact mul_le_mul h23 h14 (norm_nonneg _) hD.le
  have h1 : cs ^ 2 / D ^ 2 * (‖c‖ ^ 2 / P * ‖(w₂ - w₃) * (w₁ - w₄)‖) ≤ cs ^ 2 := by
    calc cs ^ 2 / D ^ 2 * (‖c‖ ^ 2 / P * ‖(w₂ - w₃) * (w₁ - w₄)‖) ≤ cs ^ 2 / D ^ 2 * D ^ 2 :=
          mul_le_mul_of_nonneg_left hhi (by positivity)
      _ = cs ^ 2 := by field_simp
  have h2 : ‖c‖ ^ 2 / P * (cs ^ 2 / D ^ 2 * ‖(w₂ - w₃) * (w₁ - w₄)‖) ≤
      ‖c‖ ^ 2 / P * ‖(w₁ - w₃) * (w₂ - w₄)‖ := by nlinarith
  exact le_of_mul_le_mul_left h2 hΛ

/-- `‖(1 + i y)/(1 - i y)‖ = 1` and `(1 + i y)/(1 - i y) + 1 = 2/(1 - i y)` for real `y`. -/
theorem s5r58q_cayley_norm (y : ℝ) :
    ‖(1 + I * (y : ℂ)) / (1 - I * (y : ℂ))‖ = 1 ∧ ‖(1 + I * (y : ℂ)) / (1 - I * (y : ℂ)) + 1‖ ^ 2 = 4 / (1 + y ^ 2) := by
  have hd : (1 : ℂ) - I * (y : ℂ) ≠ 0 := fun h => by have := congrArg Complex.re h; simp at this
  have hcj : conj ((1 : ℂ) + I * (y : ℂ)) = 1 - I * (y : ℂ) := by
    simp only [map_add, map_mul, map_one, Complex.conj_I, Complex.conj_ofReal]; ring
  have hn : ‖(1 : ℂ) - I * (y : ℂ)‖ ^ 2 = 1 + y ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; simp; ring
  refine ⟨?_, ?_⟩
  · rw [norm_div, ← Complex.norm_conj ((1 : ℂ) + I * (y : ℂ)), hcj, div_self (norm_ne_zero_iff.mpr hd)]
  · have e : (1 + I * (y : ℂ)) / (1 - I * (y : ℂ)) + 1 = 2 / (1 - I * (y : ℂ)) := by field_simp; ring
    rw [e, norm_div, div_pow, hn]
    norm_num

/-- **Cross-ratio lower bound on `S¹`** (Pommerenke §9.4, after (9.4.13)). With the entry bound `K` of the Grunsky
matrix (WQ0 + `s5r58_entry_le`), for cyclically ordered
`t₁ < t₂ < t₃ < t₄ < t₁ + 2π`, with `w_k = Ψ(e^{i t_k})`, `c₀ |(w₂-w₃)(w₁-w₄)| ≤ |(w₁-w₃)(w₂-w₄)|`. -/
theorem s5r58q_cross {C : ℕ → ℕ → ℂ} {K : ℝ} (hK : ∀ m n, ‖C m n‖ ≤ K) {κ : ℝ} (hκ1 : κ < 1) {f Ψ : ℂ → ℂ}
    (hfd : DifferentiableOn ℂ f unitDisc) (hfi : InjOn f unitDisc) (hf0 : f 0 = 0) (hf1 : deriv f 0 = 1)
    (hrep : ∀ z₁ ∈ unitDisc, ∀ z₂ ∈ unitDisc, z₁ ≠ 0 → z₂ ≠ 0 → z₁ ≠ z₂ → ∃ S,
      HasSum (fun q : ℕ × ℕ => C q.1 q.2 / Real.sqrt ((q.1 + 1) * (q.2 + 1)) * z₁ ^ (q.1 + 1) * z₂ ^ (q.2 + 1)) S ∧
      (f z₁ - f z₂) * z₁ * z₂ = (z₁ - z₂) * f z₁ * f z₂ * exp (-S))
    (hgol : ∀ (n : ℕ) (z γ : Fin n → ℂ), (∀ ν, z ν ∈ unitDisc) →
      ‖∑ μ, ∑ ν, γ μ * γ ν * ∑' q : ℕ × ℕ, C q.1 q.2 / Real.sqrt ((q.1 + 1) * (q.2 + 1)) *
          z μ ^ (q.1 + 1) * z ν ^ (q.2 + 1)‖ ≤
        κ * (∑ μ, ∑ ν, γ μ * conj (γ ν) * Complex.log (1 / (1 - z μ * conj (z ν)))).re)
    (hc : ContinuousOn Ψ (closedBall 0 1 \ {0})) (hi : InjOn Ψ (closedBall 0 1 \ {0}))
    (he : ∀ z ∈ unitDisc, z ≠ 0 → Ψ z = (f z)⁻¹) :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ t₁ t₂ t₃ t₄ : ℝ, t₁ < t₂ → t₂ < t₃ → t₃ < t₄ → t₄ < t₁ + 2 * π →
      c₀ * ‖(Ψ (exp (t₂ * I)) - Ψ (exp (t₃ * I))) * (Ψ (exp (t₁ * I)) - Ψ (exp (t₄ * I)))‖ ≤
        ‖(Ψ (exp (t₁ * I)) - Ψ (exp (t₃ * I))) * (Ψ (exp (t₂ * I)) - Ψ (exp (t₄ * I)))‖ := by
  have hκ0 : 0 ≤ κ := s5r58q_kappa_nonneg hgol
  have hκ' : 0 < 1 - κ := by linarith
  obtain ⟨cs, hcs, hsep⟩ := s5r58q_sep hκ0 hκ1 (A := 4) (by norm_num)
  obtain ⟨D, hD⟩ : ∃ D : ℝ, D = 8 / (1 - κ) + 24 * π := ⟨_, rfl⟩
  have hD0 : 0 < D := by rw [hD]; positivity
  refine ⟨cs ^ 2 / D ^ 2, by positivity, fun t₁ t₂ t₃ t₄ h12 h23 h34 h41 => ?_⟩
  -- angles in `(-π/2, π/2)` after the rotation by `m`
  obtain ⟨m, hm⟩ : ∃ m : ℝ, m = (t₁ + t₄) / 2 := ⟨_, rfl⟩
  have hθ : ∀ t : ℝ, t₁ ≤ t → t ≤ t₄ → (t - m) / 2 ∈ Ioo (-(π / 2)) (π / 2) := fun t h1 h2 => by
    rw [hm]; constructor <;> linarith [Real.pi_pos]
  have hθ₁ := hθ t₁ le_rfl (by linarith)
  have hθ₂ := hθ t₂ h12.le (by linarith)
  have hθ₃ := hθ t₃ (by linarith) h34.le
  have hθ₄ := hθ t₄ (by linarith) le_rfl
  obtain ⟨x₁, hx₁⟩ : ∃ x, x = Real.tan ((t₁ - m) / 2) := ⟨_, rfl⟩
  obtain ⟨x₂, hx₂⟩ : ∃ x, x = Real.tan ((t₂ - m) / 2) := ⟨_, rfl⟩
  obtain ⟨x₃, hx₃⟩ : ∃ x, x = Real.tan ((t₃ - m) / 2) := ⟨_, rfl⟩
  obtain ⟨x₄, hx₄⟩ : ∃ x, x = Real.tan ((t₄ - m) / 2) := ⟨_, rfl⟩
  have h12x : x₁ < x₂ := by rw [hx₁, hx₂]; exact Real.strictMonoOn_tan hθ₁ hθ₂ (by linarith)
  have h23x : x₂ < x₃ := by rw [hx₂, hx₃]; exact Real.strictMonoOn_tan hθ₂ hθ₃ (by linarith)
  have h34x : x₃ < x₄ := by rw [hx₃, hx₄]; exact Real.strictMonoOn_tan hθ₃ hθ₄ (by linarith)
  have hu : ∀ (t x : ℝ), (t - m) / 2 ∈ Ioo (-(π / 2)) (π / 2) → x = Real.tan ((t - m) / 2) →
      exp ((t : ℂ) * I) = exp ((m : ℂ) * I) * ((1 + I * (x : ℂ)) / (1 - I * (x : ℂ))) := by
    intro t x ht hx
    rw [hx, s5r58q_cayley (Real.cos_pos_of_mem_Ioo ht), ← Complex.exp_add]
    congr 1
    push_cast
    ring
  -- the real Möbius map `h : (x₁, x₃, x₄) ↦ (-1, 1, ∞)` and its inverse `g`
  obtain ⟨α₁, hα₁⟩ : ∃ α : ℝ, α = (x₁ + x₃ - 2 * x₄) / (x₃ - x₁) := ⟨_, rfl⟩
  obtain ⟨β₁, hβ₁⟩ : ∃ β : ℝ, β = x₄ - x₁ - α₁ * x₁ := ⟨_, rfl⟩
  have h31 : 0 < x₃ - x₁ := by linarith
  have hdet : 0 < -x₄ * α₁ - (-β₁) * (-1) := by
    have : -x₄ * α₁ - (-β₁) * (-1) = 2 * (x₄ - x₁) * (x₄ - x₃) / (x₃ - x₁) := by
      rw [hβ₁, hα₁]; field_simp; ring
    rw [this]
    have : 0 < x₄ - x₁ := by linarith
    have : 0 < x₄ - x₃ := by linarith
    positivity
  obtain ⟨hlt, hmap, hneg⟩ := s5r58q_conj_cayley hdet
  -- `g (h x) = x` and `r h(x) + s ≠ 0` for `x ≠ x₄`
  have hinv : ∀ x : ℝ, x ≠ x₄ → (-1) * ((α₁ * x + β₁) / (x - x₄)) + α₁ ≠ 0 ∧
      (-x₄ * ((α₁ * x + β₁) / (x - x₄)) + -β₁) / ((-1) * ((α₁ * x + β₁) / (x - x₄)) + α₁) = x := by
    intro x hx
    have hx' : x - x₄ ≠ 0 := sub_ne_zero.mpr hx
    have hd' : -x₄ * α₁ - β₁ ≠ 0 := by linarith
    have e : (-1) * ((α₁ * x + β₁) / (x - x₄)) + α₁ = (-x₄ * α₁ - β₁) / (x - x₄) := by field_simp; ring
    refine ⟨by rw [e]; exact div_ne_zero hd' hx', ?_⟩
    rw [e, div_eq_iff (div_ne_zero hd' hx')]
    field_simp
    ring
  have hh₁ : (α₁ * x₁ + β₁) / (x₁ - x₄) = -1 := by
    rw [hβ₁, div_eq_iff (by linarith : x₁ - x₄ ≠ 0)]; ring
  have hh₃ : (α₁ * x₃ + β₁) / (x₃ - x₄) = 1 := by
    rw [hβ₁, hα₁, div_eq_iff (by linarith : x₃ - x₄ ≠ 0)]; field_simp; ring
  have hh₂ : ((α₁ * x₂ + β₁) / (x₂ - x₄)) ^ 2 ≤ 1 := by
    have e1 : 1 - (α₁ * x₂ + β₁) / (x₂ - x₄) = 2 * (x₄ - x₁) * (x₃ - x₂) / ((x₃ - x₁) * (x₄ - x₂)) := by
      rw [hβ₁, hα₁]; field_simp [show x₂ - x₄ ≠ 0 by linarith, show x₄ - x₂ ≠ 0 by linarith]; ring
    have e2 : 1 + (α₁ * x₂ + β₁) / (x₂ - x₄) = 2 * (x₄ - x₃) * (x₂ - x₁) / ((x₃ - x₁) * (x₄ - x₂)) := by
      rw [hβ₁, hα₁]; field_simp [show x₂ - x₄ ≠ 0 by linarith, show x₄ - x₂ ≠ 0 by linarith]; ring
    have p1 : 0 ≤ 1 - (α₁ * x₂ + β₁) / (x₂ - x₄) := by
      rw [e1]; have : 0 < x₄ - x₂ := by linarith
      have : 0 < x₄ - x₁ := by linarith
      have : 0 < x₃ - x₂ := by linarith
      positivity
    have p2 : 0 ≤ 1 + (α₁ * x₂ + β₁) / (x₂ - x₄) := by
      rw [e2]; have : 0 < x₄ - x₂ := by linarith
      have : 0 < x₄ - x₃ := by linarith
      have : 0 < x₂ - x₁ := by linarith
      positivity
    nlinarith
  -- the disc automorphism `τ = e^{im} τ'`
  obtain ⟨a', ha'⟩ : ∃ a' : ℂ, a' = ((-(-x₄ + α₁) : ℝ) : ℂ) + (((-1) - (-β₁) : ℝ) : ℂ) * I := ⟨_, rfl⟩
  obtain ⟨b', hb'⟩ : ∃ b' : ℂ, b' = ((-x₄ - α₁ : ℝ) : ℂ) - (((-1) + (-β₁) : ℝ) : ℂ) * I := ⟨_, rfl⟩
  rw [← ha', ← hb'] at hlt hmap hneg
  obtain ⟨E, hE⟩ : ∃ E : ℂ, E = exp (((m / 2 : ℝ) : ℂ) * I) := ⟨_, rfl⟩
  have hEn : ‖E‖ = 1 := by rw [hE]; exact Complex.norm_exp_ofReal_mul_I _
  have hE0 : E ≠ 0 := by rw [hE]; exact Complex.exp_ne_zero _
  have hEc : conj E = E⁻¹ := by
    rw [hE, ← Complex.exp_conj, ← Complex.exp_neg]
    congr 1
    simp [map_mul, map_div₀, map_ofNat, Complex.conj_ofReal, Complex.conj_I]
  have hEE : E * E = exp ((m : ℂ) * I) := by
    rw [hE, ← Complex.exp_add]; congr 1; push_cast; ring
  have hab : ‖E * b'‖ < ‖E * a'‖ := by rw [norm_mul, norm_mul, hEn, one_mul, one_mul]; exact hlt
  have hrot : ∀ z : ℂ, conj b' * z + conj a' ≠ 0 →
      (E * a' * z + E * b') / (conj (E * b') * z + conj (E * a')) =
        exp ((m : ℂ) * I) * ((a' * z + b') / (conj b' * z + conj a')) := by
    intro z hz
    rw [map_mul, map_mul, hEc, ← hEE]
    field_simp
  have hden' := (s5r58q_aut hlt).1
  have hCn : ∀ y : ℝ, ‖(1 + I * (y : ℂ)) / (1 - I * (y : ℂ))‖ ≤ 1 := fun y => (s5r58q_cayley_norm y).1.le
  -- the four normalized points `v = (C(h x₁), C(h x₂), C(h x₃), -1)` map to `u`
  have hpt : ∀ (t x : ℝ), (t - m) / 2 ∈ Ioo (-(π / 2)) (π / 2) → x = Real.tan ((t - m) / 2) → x ≠ x₄ →
      (E * a' * ((1 + I * (((α₁ * x + β₁) / (x - x₄) : ℝ) : ℂ)) / (1 - I * (((α₁ * x + β₁) / (x - x₄) : ℝ) : ℂ))) +
          E * b') /
        (conj (E * b') * ((1 + I * (((α₁ * x + β₁) / (x - x₄) : ℝ) : ℂ)) /
          (1 - I * (((α₁ * x + β₁) / (x - x₄) : ℝ) : ℂ))) + conj (E * a')) = exp ((t : ℂ) * I) := by
    intro t x ht hx hx4
    obtain ⟨hne, hg⟩ := hinv x hx4
    rw [hrot _ (hden' _ (hCn _)), hmap _ hne, hg, hu t x ht hx]
  have hpt4 : (E * a' * (-1) + E * b') / (conj (E * b') * (-1) + conj (E * a')) = exp ((t₄ : ℂ) * I) := by
    rw [hrot _ (hden' _ (by simp)), hneg (by norm_num), hu t₄ x₄ hθ₄ hx₄]
    congr 3 <;> norm_num
  -- the renormalized `k` for `τ`
  obtain ⟨k, c, hc0, hkc, hkd, hlb, hub, htp, hcirc⟩ :=
    s5r58q_renorm hK hκ0 hκ1 hfd hfi hf0 hf1 hrep hgol hc hi he hab
  have hkne : ∀ z : ℂ, 1 / 2 ≤ ‖z‖ → ‖z‖ < 1 → deriv k z ≠ 0 := fun z h1 h2 h0 => by
    have := hlb z h1 h2
    rw [h0, norm_zero] at this
    have : 0 < (1 - ‖z‖) ^ κ := Real.rpow_pos_of_pos (by linarith) _
    linarith
  have hsep' := hsep k hkc hkd hlb hub htp
  have hdiam := fun u₁ u₂ (h₁ : ‖u₁‖ = 1) (h₂ : ‖u₂‖ = 1) => s5r58q_diam hκ0 hκ1 hkc hkd hkne hub h₁ h₂
  rw [← hD] at hdiam
  obtain ⟨v₁, hv₁⟩ : ∃ v : ℂ, v = (1 + I * (((α₁ * x₁ + β₁) / (x₁ - x₄) : ℝ) : ℂ)) /
      (1 - I * (((α₁ * x₁ + β₁) / (x₁ - x₄) : ℝ) : ℂ)) := ⟨_, rfl⟩
  obtain ⟨v₂, hv₂⟩ : ∃ v : ℂ, v = (1 + I * (((α₁ * x₂ + β₁) / (x₂ - x₄) : ℝ) : ℂ)) /
      (1 - I * (((α₁ * x₂ + β₁) / (x₂ - x₄) : ℝ) : ℂ)) := ⟨_, rfl⟩
  obtain ⟨v₃, hv₃⟩ : ∃ v : ℂ, v = (1 + I * (((α₁ * x₃ + β₁) / (x₃ - x₄) : ℝ) : ℂ)) /
      (1 - I * (((α₁ * x₃ + β₁) / (x₃ - x₄) : ℝ) : ℂ)) := ⟨_, rfl⟩
  have hn₁ : ‖v₁‖ = 1 := hv₁ ▸ (s5r58q_cayley_norm _).1
  have hn₂ : ‖v₂‖ = 1 := hv₂ ▸ (s5r58q_cayley_norm _).1
  have hn₃ : ‖v₃‖ = 1 := hv₃ ▸ (s5r58q_cayley_norm _).1
  have hn₄ : ‖(-1 : ℂ)‖ = 1 := by simp
  have hτ₁ := hpt t₁ x₁ hθ₁ hx₁ (by linarith)
  have hτ₂ := hpt t₂ x₂ hθ₂ hx₂ (by linarith)
  have hτ₃ := hpt t₃ x₃ hθ₃ hx₃ (by linarith)
  rw [← hv₁] at hτ₁
  rw [← hv₂] at hτ₂
  rw [← hv₃] at hτ₃
  obtain ⟨d₁, k₁⟩ := hcirc v₁ hn₁
  obtain ⟨d₂, k₂⟩ := hcirc v₂ hn₂
  obtain ⟨d₃, k₃⟩ := hcirc v₃ hn₃
  obtain ⟨d₄, k₄⟩ := hcirc (-1) hn₄
  rw [hτ₁] at d₁ k₁
  rw [hτ₂] at d₂ k₂
  rw [hτ₃] at d₃ k₃
  rw [hpt4] at d₄ k₄
  -- separations and diameters
  have hs13 : 2 ≤ ‖v₁ - v₃‖ ^ 2 := by
    have e1 : v₁ = -I := by
      rw [hv₁, hh₁]; push_cast
      rw [div_eq_iff (by intro h; have := congrArg Complex.im h; simp at this)]
      linear_combination Complex.I_sq
    have e3 : v₃ = I := by
      rw [hv₃, hh₃]; push_cast
      rw [div_eq_iff (by intro h; have := congrArg Complex.im h; simp at this)]
      linear_combination Complex.I_sq
    rw [e1, e3, show -I - I = (-2 : ℂ) * I by ring, norm_mul, Complex.norm_I]
    norm_num
  have hs24 : 2 ≤ ‖v₂ - (-1)‖ ^ 2 := by
    rw [sub_neg_eq_add, hv₂, (s5r58q_cayley_norm _).2]
    rw [le_div_iff₀ (by positivity)]
    nlinarith
  have c13 := hsep' v₁ v₃ hn₁ hn₃ hs13
  have c24 := hsep' v₂ (-1) hn₂ hn₄ hs24
  have D23 := hdiam v₂ v₃ hn₂ hn₃
  have D14 := hdiam v₁ (-1) hn₁ hn₄
  rw [k₁, k₃] at c13
  rw [k₂, k₄] at c24
  rw [k₂, k₃] at D23
  rw [k₁, k₄] at D14
  exact s5r58q_crossalg hc0 hcs.le hD0 d₁ d₂ d₃ d₄ c13 c24 D23 D14

/-- **Sub-stub WQ0** (audit note 2). `𝔇_∞⁰` matrices are uniform strict contractions: `‖C‖ ≤ κ < 1`. The `siegelDisk`
clause is only pointwise (`‖Cx‖ < ‖x‖`); Hilbert–Schmidt (compactness) makes the operator norm attained, hence `< 1`. -/
theorem s5r58_wqd_opnorm {C : ℕ → ℕ → ℂ} (hC : C ∈ siegelDisk0) :
    ∃ κ : ℝ, 0 ≤ κ ∧ κ < 1 ∧ ∀ x : ℕ → ℂ, IsL2 x → sqSum (matApply C x) ≤ κ ^ 2 * sqSum x := by
  obtain ⟨⟨-, hB, hstr⟩, hHS⟩ := hC
  have hTx : ∀ x : ell2, ‖gopOp C x‖ ^ 2 = sqSum (matApply C x) := by
    intro x
    rw [gop_norm_sq]
    simp only [pmb_apply hB, sqSum]
  have hstrict : ∀ x : ell2, x ≠ 0 → ‖gopOp C x‖ < ‖x‖ := by
    intro x hx
    have hx' : (x : ℕ → ℂ) ≠ 0 := fun h => hx (lp.ext h)
    have h := hstr x (s5r58_ell2_summable x) hx'
    rw [← hTx] at h
    have h2 : sqSum (x : ℕ → ℂ) = ‖x‖ ^ 2 := (gop_norm_sq x).symm
    rw [h2] at h
    exact lt_of_pow_lt_pow_left₀ 2 (norm_nonneg _) h
  have hT1 : ‖gopOp C‖ ≤ 1 := by
    refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => ?_
    by_cases hx : x = 0
    · simp [hx]
    · rw [one_mul]; exact (hstrict x hx).le
  -- `A = T* T`: compact, without eigenvalue `1`
  have hAin : ∀ x : ell2, inner ℂ ((ContinuousLinearMap.adjoint (gopOp C)).comp (gopOp C) x) x =
      ((‖gopOp C x‖ ^ 2 : ℝ) : ℂ) := by
    intro x
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_left, inner_self_eq_norm_sq_to_K]
    push_cast
    rfl
  have hAc : IsCompactOperator ((ContinuousLinearMap.adjoint (gopOp C)).comp (gopOp C)) :=
    (s5r58_gop_compact hB hHS).clm_comp (ContinuousLinearMap.adjoint (gopOp C))
  have hnoeig : ¬ Module.End.HasEigenvalue
      (((ContinuousLinearMap.adjoint (gopOp C)).comp (gopOp C) : ell2 →L[ℂ] ell2) : Module.End ℂ ell2) 1 := by
    intro h
    obtain ⟨v, hv⟩ := h.exists_hasEigenvector
    have hAv := hv.apply_eq_smul
    rw [one_smul] at hAv
    have hi := hAin v
    change inner ℂ ((ContinuousLinearMap.adjoint (gopOp C)).comp (gopOp C) v) v = _ at hi
    have hAv' : (ContinuousLinearMap.adjoint (gopOp C)).comp (gopOp C) v = v := hAv
    rw [hAv'] at hi
    have hn : ‖v‖ ^ 2 = ‖gopOp C v‖ ^ 2 := by
      rw [← inner_self_eq_norm_sq (𝕜 := ℂ), hi]
      exact Complex.ofReal_re _
    have hlt := hstrict v hv.2
    nlinarith [norm_nonneg (gopOp C v), norm_nonneg v]
  obtain ⟨c, hc0, hc⟩ := antilipschitzWith_iff_exists_mul_le_norm.mp
    (IsCompactOperator.antilipschitz_of_not_hasEigenvalue hAc one_ne_zero hnoeig)
  -- `c‖x‖ ≤ ‖Ax - x‖` and `‖x - Ax‖² ≤ ‖x‖² - ‖Tx‖²`
  have hkey : ∀ x : ell2, c ^ 2 * ‖x‖ ^ 2 ≤ ‖x‖ ^ 2 - ‖gopOp C x‖ ^ 2 := by
    intro x
    have h1 := hc x
    have hsub : ((ContinuousLinearMap.adjoint (gopOp C)).comp (gopOp C) - (1 : ℂ) • 1) x =
        (ContinuousLinearMap.adjoint (gopOp C)).comp (gopOp C) x - x := by
      simp
    rw [hsub, norm_sub_rev] at h1
    have hA : ‖(ContinuousLinearMap.adjoint (gopOp C)).comp (gopOp C) x‖ ≤ ‖gopOp C x‖ := by
      rw [ContinuousLinearMap.comp_apply]
      calc ‖ContinuousLinearMap.adjoint (gopOp C) (gopOp C x)‖
          ≤ ‖ContinuousLinearMap.adjoint (gopOp C)‖ * ‖gopOp C x‖ := ContinuousLinearMap.le_opNorm _ _
        _ ≤ 1 * ‖gopOp C x‖ := by
            gcongr
            rw [LinearIsometryEquiv.norm_map]
            exact hT1
        _ = ‖gopOp C x‖ := one_mul _
    have hre : RCLike.re (inner ℂ x ((ContinuousLinearMap.adjoint (gopOp C)).comp (gopOp C) x)) =
        ‖gopOp C x‖ ^ 2 := by
      rw [← inner_conj_symm, hAin, Complex.conj_ofReal]
      exact Complex.ofReal_re _
    have hsq := norm_sub_sq (𝕜 := ℂ) x ((ContinuousLinearMap.adjoint (gopOp C)).comp (gopOp C) x)
    rw [hre] at hsq
    have h1' : (c * ‖x‖) ^ 2 ≤ ‖x - (ContinuousLinearMap.adjoint (gopOp C)).comp (gopOp C) x‖ ^ 2 :=
      pow_le_pow_left₀ (by positivity) h1 2
    nlinarith [norm_nonneg ((ContinuousLinearMap.adjoint (gopOp C)).comp (gopOp C) x),
      norm_nonneg (gopOp C x), mul_le_mul hA hA (norm_nonneg _) (norm_nonneg _)]
  -- `κ = √(1 - c'²)`, `c' = min c 1`
  have hc1 : 0 < min c 1 := lt_min hc0 one_pos
  have hc2 : min c 1 ≤ 1 := min_le_right _ _
  have hc3 : min c 1 ≤ c := min_le_left _ _
  have hκ2 : Real.sqrt (1 - min c 1 ^ 2) ^ 2 = 1 - min c 1 ^ 2 := Real.sq_sqrt (by nlinarith)
  refine ⟨Real.sqrt (1 - min c 1 ^ 2), Real.sqrt_nonneg _, ?_, fun x hx => ?_⟩
  · rw [Real.sqrt_lt' one_pos]; nlinarith
  · let X : ell2 := ⟨x, gop_mem_of_summable hx⟩
    have h1 := hkey X
    have hX : ‖X‖ ^ 2 = sqSum x := gop_norm_sq X
    rw [← hTx X, hκ2]
    show ‖gopOp C X‖ ^ 2 ≤ (1 - min c 1 ^ 2) * sqSum x
    rw [← hX]
    nlinarith [pow_le_pow_left₀ hc1.le hc3 2, sq_nonneg ‖X‖]

/-- **Sub-stub WQ1** (Pommerenke Lemma 9.9 (⇒), disc form; a pure series estimate). With `‖C‖ ≤ κ`, the mixed series
`S(z,w) = Σ C_{mn}/√((m+1)(n+1)) z^{m+1} w^{n+1}` satisfies the Golusin inequality
`|Σ_{μν} γ_μ γ_ν S(z_μ, z_ν)| ≤ κ Re Σ_{μν} γ_μ γ̄_ν log (1/(1 - z_μ z̄_ν))` (`X_m = Σ_μ γ_μ z_μ^{m+1}/√(m+1)`,
`|Xᵀ C X| ≤ κ ‖X‖²`, `‖X‖² = Σ γ γ̄ Σ (z w̄)^{m+1}/(m+1)`). -/
theorem s5r58_wqd_golusin {C : ℕ → ℕ → ℂ} (hB : IsBoundedMat C) {κ : ℝ} (hκ : 0 ≤ κ)
    (hCκ : ∀ x : ℕ → ℂ, IsL2 x → sqSum (matApply C x) ≤ κ ^ 2 * sqSum x) {n : ℕ} (z γ : Fin n → ℂ)
    (hz : ∀ ν, z ν ∈ unitDisc) :
    ‖∑ μ, ∑ ν, γ μ * γ ν * ∑' q : ℕ × ℕ, C q.1 q.2 / Real.sqrt ((q.1 + 1) * (q.2 + 1)) *
        z μ ^ (q.1 + 1) * z ν ^ (q.2 + 1)‖ ≤
      κ * (∑ μ, ∑ ν, γ μ * conj (γ ν) * Complex.log (1 / (1 - z μ * conj (z ν)))).re := by
  have hzn : ∀ ν, ‖z ν‖ < 1 := fun ν => mem_ball_zero_iff.mp (hz ν)
  obtain ⟨V, hV⟩ : ∃ V : Fin n → ell2, V = fun ν => ⟨fun m => z ν ^ (m + 1) / (Real.sqrt (m + 1) : ℂ),
      gop_mem_of_summable (s5r58_geom_ell2 (hzn ν))⟩ := ⟨_, rfl⟩
  have hK := s5r58_entry_le hB hκ hCκ
  have hS : ∀ μ ν, (∑' q : ℕ × ℕ, C q.1 q.2 / Real.sqrt ((q.1 + 1) * (q.2 + 1)) *
      z μ ^ (q.1 + 1) * z ν ^ (q.2 + 1)) = inner ℂ (star (V μ)) (gopOp C (V ν)) := fun μ ν => by
    rw [hV]; exact s5r58_S_eq_inner hB hK (hzn μ) (hzn ν)
  have hG : ∀ μ ν, inner ℂ (V μ) (V ν) = -log (1 - conj (z μ) * z ν) := fun μ ν => by
    rw [hV, lp.inner_eq_tsum]
    exact ((s5r58_inner_geom (hzn μ) (hzn ν)).congr_fun fun m => gop_inner_apply _ _).tsum_eq
  have hL : ∀ μ ν, log (1 / (1 - z μ * conj (z ν))) = -log (1 - conj (z ν) * z μ) := fun μ ν => by
    have hu : ‖z μ * conj (z ν)‖ < 1 := by
      rw [norm_mul, Complex.norm_conj]; nlinarith [norm_nonneg (z μ), norm_nonneg (z ν), hzn μ, hzn ν]
    have harg : (1 - z μ * conj (z ν)).arg ≠ π := by
      rw [Ne, Complex.arg_eq_pi_iff]
      intro h
      have := Complex.re_le_norm (z μ * conj (z ν))
      simp only [Complex.sub_re, Complex.one_re] at h
      linarith [h.1]
    rw [one_div, Complex.log_inv _ harg, mul_comm (z μ)]
  obtain ⟨X, hX⟩ : ∃ X : ell2, X = ∑ ν, γ ν • V ν := ⟨_, rfl⟩
  have hstarX : star X = ∑ μ, conj (γ μ) • star (V μ) := by
    rw [hX, star_sum]
    exact Finset.sum_congr rfl fun μ _ => by rw [star_smul, Complex.star_def]
  have hLHS : (∑ μ, ∑ ν, γ μ * γ ν * ∑' q : ℕ × ℕ, C q.1 q.2 / Real.sqrt ((q.1 + 1) * (q.2 + 1)) *
      z μ ^ (q.1 + 1) * z ν ^ (q.2 + 1)) = inner ℂ (star X) (gopOp C X) := by
    rw [hstarX, hX, map_sum, sum_inner]
    refine Finset.sum_congr rfl fun μ _ => ?_
    rw [inner_sum]
    refine Finset.sum_congr rfl fun ν _ => ?_
    rw [map_smul, inner_smul_left, inner_smul_right, hS, Complex.conj_conj]
    ring
  have hXX : inner ℂ X X = ∑ μ, ∑ ν, γ μ * conj (γ ν) * log (1 / (1 - z μ * conj (z ν))) := by
    rw [Finset.sum_comm, hX, sum_inner]
    refine Finset.sum_congr rfl fun ν _ => ?_
    rw [inner_sum]
    refine Finset.sum_congr rfl fun μ _ => ?_
    rw [inner_smul_left, inner_smul_right, hG, hL]
    ring
  have hre : (inner ℂ X X).re = ‖X‖ ^ 2 := inner_self_eq_norm_sq (𝕜 := ℂ) X
  have hTX : ‖gopOp C X‖ ≤ κ * ‖X‖ := by
    have h1 : ‖gopOp C X‖ ^ 2 = sqSum (matApply C X) := by
      rw [gop_norm_sq]; simp only [pmb_apply hB, sqSum]
    have h2 := hCκ X (s5r58_ell2_summable X)
    have h3 : sqSum (X : ℕ → ℂ) = ‖X‖ ^ 2 := (gop_norm_sq X).symm
    rw [← h1, h3, ← mul_pow] at h2
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp h2
  rw [hLHS, ← hXX, hre]
  calc ‖inner ℂ (star X) (gopOp C X)‖ ≤ ‖star X‖ * ‖gopOp C X‖ := norm_inner_le_norm _ _
    _ ≤ ‖X‖ * (κ * ‖X‖) := by rw [norm_star]; gcongr
    _ = κ * ‖X‖ ^ 2 := by ring

/-- **Sub-stub WQ2i** (Pommerenke Thm 9.12, boundary injectivity). Any continuous extension `Ψ` of `1/f` to `𝔻̄ ∖ 0` is
injective on `S¹` (circle × circle; the disc × disc and disc × circle cases are elementary, proved in WQ2). -/
theorem s5r58_wqd_bdry_inj {C : ℕ → ℕ → ℂ} (hC : C ∈ siegelDisk0) {κ : ℝ} (hκ1 : κ < 1) {f Ψ : ℂ → ℂ}
    (hfd : DifferentiableOn ℂ f unitDisc) (hfi : InjOn f unitDisc) (hf0 : f 0 = 0) (hf1 : deriv f 0 = 1)
    (hrep : ∀ z₁ ∈ unitDisc, ∀ z₂ ∈ unitDisc, z₁ ≠ 0 → z₂ ≠ 0 → z₁ ≠ z₂ → ∃ S,
      HasSum (fun q : ℕ × ℕ => C q.1 q.2 / Real.sqrt ((q.1 + 1) * (q.2 + 1)) * z₁ ^ (q.1 + 1) * z₂ ^ (q.2 + 1)) S ∧
      (f z₁ - f z₂) * z₁ * z₂ = (z₁ - z₂) * f z₁ * f z₂ * exp (-S))
    (hgol : ∀ (n : ℕ) (z γ : Fin n → ℂ), (∀ ν, z ν ∈ unitDisc) →
      ‖∑ μ, ∑ ν, γ μ * γ ν * ∑' q : ℕ × ℕ, C q.1 q.2 / Real.sqrt ((q.1 + 1) * (q.2 + 1)) *
          z μ ^ (q.1 + 1) * z ν ^ (q.2 + 1)‖ ≤
        κ * (∑ μ, ∑ ν, γ μ * conj (γ ν) * Complex.log (1 / (1 - z μ * conj (z ν)))).re)
    (hc : ContinuousOn Ψ (closedBall 0 1 \ {0})) (he : ∀ z ∈ unitDisc, z ≠ 0 → Ψ z = (f z)⁻¹) :
    InjOn Ψ (sphere (0 : ℂ) 1) := by
  -- `hC` enters only through the entry bound `K` (WQ0); the Golusin constant `κ` is taken from `hgol`
  obtain ⟨K, hK0, -, hKC⟩ := s5r58_wqd_opnorm hC
  have hK := s5r58_entry_le hC.1.2.1 hK0 hKC
  have hκ0 : 0 ≤ κ := s5r58q_kappa_nonneg hgol
  have hmem : ∀ z : ℂ, ‖z‖ < 1 → z ∈ unitDisc := fun z hz => mem_ball_zero_iff.mpr hz
  have hz0 : ∀ z : ℂ, 1 / 2 ≤ ‖z‖ → z ≠ 0 := fun z hz h => by
    rw [h, norm_zero] at hz
    norm_num at hz
  -- `Ψ = 1/f` near every point of the annulus, hence `Ψ' = -z⁻² e^{-S(z,z)}`
  have hder : ∀ z : ℂ, 1 / 2 ≤ ‖z‖ → ‖z‖ < 1 → HasDerivAt Ψ (-(z * z)⁻¹ * exp (-∑' q : ℕ × ℕ,
      C q.1 q.2 / Real.sqrt ((q.1 + 1) * (q.2 + 1)) * z ^ (q.1 + 1) * z ^ (q.2 + 1))) z := by
    intro z hz1 hz2
    have hev : Ψ =ᶠ[𝓝 z] fun w => (f w)⁻¹ := by
      have hO : IsOpen (unitDisc \ {(0 : ℂ)}) := Metric.isOpen_ball.sdiff isClosed_singleton
      filter_upwards [hO.mem_nhds ⟨hmem z hz2, hz0 z hz1⟩] with w hw
      exact he w hw.1 hw.2
    exact (s5r58_psi_deriv hK hfd hfi hf0 hrep (hmem z hz2) (hz0 z hz1)).congr_of_eventuallyEq hev
  have hdeq : ∀ z : ℂ, 1 / 2 ≤ ‖z‖ → ‖z‖ < 1 → deriv Ψ z = -(z * z)⁻¹ * exp (-∑' q : ℕ × ℕ,
      C q.1 q.2 / Real.sqrt ((q.1 + 1) * (q.2 + 1)) * z ^ (q.1 + 1) * z ^ (q.2 + 1)) :=
    fun z hz1 hz2 => (hder z hz1 hz2).deriv
  have hval : ∀ z : ℂ, 1 / 2 ≤ ‖z‖ → ‖z‖ < 1 → Ψ z = (f z)⁻¹ :=
    fun z hz1 hz2 => he z (hmem z hz2) (hz0 z hz1)
  refine fun u₁ hu₁ u₂ hu₂ heq => by_contra fun hne => s5r58q_core hκ0 hκ1 (by norm_num : (0 : ℝ) ≤ 4) hc
    (fun z hz1 hz2 => (hder z hz1 hz2).differentiableAt) ?_ ?_ ?_ (mem_sphere_zero_iff_norm.mp hu₁)
    (mem_sphere_zero_iff_norm.mp hu₂) hne heq
  · intro z hz1 hz2
    rw [hdeq z hz1 hz2]
    exact mul_ne_zero (neg_ne_zero.mpr (inv_ne_zero (mul_ne_zero (hz0 z hz1) (hz0 z hz1)))) (Complex.exp_ne_zero _)
  · intro z hz1 hz2
    rw [hdeq z hz1 hz2]
    have hS := s5r58q_diag hgol hz2
    have hE := s5r58_exp_bd hκ0 (norm_nonneg z) hz2 hS
    have hzz : ‖(z * z)⁻¹‖ ≤ 4 := by
      rw [norm_inv, norm_mul]
      exact inv_le_of_inv_le₀ (by norm_num) (by nlinarith)
    rw [norm_mul, norm_neg]
    exact mul_le_mul hzz hE (norm_nonneg _) (by norm_num)
  · intro z₁ z₂ hz₁1 hz₁2 hz₂1 hz₂2 h12
    rw [hdeq z₁ hz₁1 hz₁2, hdeq z₂ hz₂1 hz₂2, hval z₁ hz₁1 hz₁2, hval z₂ hz₂1 hz₂2]
    exact s5r58q_tp hK hκ0 hκ1 hfd hfi hf0 hrep hgol (hmem z₁ hz₁2) (hmem z₂ hz₂2) (hz0 z₁ hz₁1) (hz0 z₂ hz₂1) h12

/-- **Sub-stub WQ2** (Pommerenke Thm 9.12, first half, disc form). Golusin with `κ < 1` (`n = 1`: `|(1/f)'|` bounds, Hölder
estimate (9.4.10); `n = 2`: the separation (9.4.13)) gives a continuous injective extension `Ψ` of `1/f` to `𝔻̄ ∖ 0`
(`g(ζ) = 1/f(1/ζ) ∈ Σ` extends homeomorphically to `|ζ| ≥ 1`; `f` itself need not extend, `z/(1 - z)`). -/
theorem s5r58_wqd_boundary {C : ℕ → ℕ → ℂ} (hC : C ∈ siegelDisk0) {κ : ℝ} (hκ1 : κ < 1) {f : ℂ → ℂ}
    (hfd : DifferentiableOn ℂ f unitDisc) (hfi : InjOn f unitDisc) (hf0 : f 0 = 0) (hf1 : deriv f 0 = 1)
    (hrep : ∀ z₁ ∈ unitDisc, ∀ z₂ ∈ unitDisc, z₁ ≠ 0 → z₂ ≠ 0 → z₁ ≠ z₂ → ∃ S,
      HasSum (fun q : ℕ × ℕ => C q.1 q.2 / Real.sqrt ((q.1 + 1) * (q.2 + 1)) * z₁ ^ (q.1 + 1) * z₂ ^ (q.2 + 1)) S ∧
      (f z₁ - f z₂) * z₁ * z₂ = (z₁ - z₂) * f z₁ * f z₂ * exp (-S))
    (hgol : ∀ (n : ℕ) (z γ : Fin n → ℂ), (∀ ν, z ν ∈ unitDisc) →
      ‖∑ μ, ∑ ν, γ μ * γ ν * ∑' q : ℕ × ℕ, C q.1 q.2 / Real.sqrt ((q.1 + 1) * (q.2 + 1)) *
          z μ ^ (q.1 + 1) * z ν ^ (q.2 + 1)‖ ≤
        κ * (∑ μ, ∑ ν, γ μ * conj (γ ν) * Complex.log (1 / (1 - z μ * conj (z ν)))).re) :
    ∃ Ψ : ℂ → ℂ, ContinuousOn Ψ (closedBall 0 1 \ {0}) ∧ InjOn Ψ (closedBall 0 1 \ {0}) ∧
      ∀ z ∈ unitDisc, z ≠ 0 → Ψ z = (f z)⁻¹ := by
  obtain ⟨K, hK0, -, hKC⟩ := s5r58_wqd_opnorm hC
  have hK := s5r58_entry_le hC.1.2.1 hK0 hKC
  have hO : IsOpen unitDisc := Metric.isOpen_ball
  have hmem : ∀ z : ℂ, ‖z‖ < 1 → z ∈ unitDisc := fun z hz => mem_ball_zero_iff.mpr hz
  have hfne : ∀ z ∈ unitDisc, z ≠ 0 → f z ≠ 0 := fun z hz hz0 h =>
    hz0 (hfi hz (Metric.mem_ball_self one_pos) (h.trans hf0.symm))
  obtain ⟨κ₀, hκ₀, hκ₀1, hκle⟩ : ∃ κ₀ : ℝ, 0 ≤ κ₀ ∧ κ₀ < 1 ∧ κ ≤ κ₀ :=
    ⟨max κ 0, le_max_right _ _, max_lt hκ1 one_pos, le_max_left _ _⟩
  -- (a) derivative bound on the annulus `1/2 ≤ |z| < 1`
  have hd : ∀ z : ℂ, 1 / 2 ≤ ‖z‖ → ‖z‖ < 1 →
      ∃ g', HasDerivAt (fun w => (f w)⁻¹) g' z ∧ ‖g'‖ ≤ 4 * (1 - ‖z‖) ^ (-κ₀) := by
    intro z hz1 hz2
    have hzD := hmem z hz2
    have hz0 : z ≠ 0 := by
      rintro rfl
      norm_num at hz1
    refine ⟨_, s5r58_psi_deriv hK hfd hfi hf0 hrep hzD hz0, ?_⟩
    have hg := hgol 1 (fun _ => z) (fun _ => 1) (fun _ => hzD)
    simp only [Fin.sum_univ_one, one_mul, mul_one, map_one] at hg
    have hz2' : ‖z‖ ^ 2 < 1 := by nlinarith [norm_nonneg z]
    have hl : (Complex.log (1 / (1 - z * conj z))).re = Real.log (1 / (1 - ‖z‖ ^ 2)) := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
      have hc : (1 : ℂ) / (1 - ((‖z‖ ^ 2 : ℝ) : ℂ)) = ((1 / (1 - ‖z‖ ^ 2) : ℝ) : ℂ) := by
        first
          | (push_cast; ring)
          | push_cast
          | norm_num
      rw [hc, ← Complex.ofReal_log (div_nonneg zero_le_one (by linarith))]
      exact Complex.ofReal_re _
    rw [hl] at hg
    have hlog0 : 0 ≤ Real.log (1 / (1 - ‖z‖ ^ 2)) :=
      Real.log_nonneg (by rw [le_div_iff₀ (by linarith)]; nlinarith [norm_nonneg z])
    have hS := hg.trans (mul_le_mul_of_nonneg_right hκle hlog0)
    have he := s5r58_exp_bd hκ₀ (norm_nonneg z) hz2 hS
    have hzz : ‖(z * z)⁻¹‖ ≤ 4 := by
      rw [norm_inv, norm_mul]
      exact inv_le_of_inv_le₀ (by norm_num) (by nlinarith)
    rw [norm_mul, norm_neg]
    exact mul_le_mul hzz he (norm_nonneg _) (by norm_num)
  -- (b) radial estimate
  obtain ⟨T, hT⟩ : ∃ T : ℝ → ℝ, T = fun s => 4 / (1 - κ₀) * (1 - s) ^ (1 - κ₀) := ⟨_, rfl⟩
  have hrad : ∀ u : ℂ, ‖u‖ = 1 → ∀ s t : ℝ, 1 / 2 ≤ s → s ≤ t → t < 1 →
      ‖(f ((t : ℂ) * u))⁻¹ - (f ((s : ℂ) * u))⁻¹‖ ≤ T s := fun u hu s t hs hst ht => by
    rw [hT]
    exact s5r58_radial (g := fun w => (f w)⁻¹) hκ₀1 hd hu hs hst ht
  obtain ⟨r, hr⟩ : ∃ r : ℕ → ℝ, r = fun n : ℕ => 1 - 1 / ((n : ℝ) + 1) / 2 := ⟨_, rfl⟩
  have ha : ∀ n : ℕ, 0 < 1 / ((n : ℝ) + 1) ∧ 1 / ((n : ℝ) + 1) ≤ 1 := fun n =>
    ⟨by positivity, (div_le_one (by positivity)).mpr (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)])⟩
  have hr1 : ∀ n, 1 / 2 ≤ r n := fun n => by
    simp only [hr]
    linarith [(ha n).2]
  have hr2 : ∀ n, r n < 1 := fun n => by
    simp only [hr]
    linarith [(ha n).1]
  have hrmono : Monotone r := fun n m hnm => by
    simp only [hr]
    have : 1 / ((m : ℝ) + 1) ≤ 1 / ((n : ℝ) + 1) :=
      one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hnm 1)
    linarith
  have h0lim : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1) / 2) atTop (𝓝 0) := by
    simpa using tendsto_one_div_add_atTop_nhds_zero_nat.div_const (2 : ℝ)
  have hrlim : Tendsto r atTop (𝓝 1) := by
    rw [hr]
    simpa using h0lim.const_sub (1 : ℝ)
  have hTr : ∀ n, T (r n) = 4 / (1 - κ₀) * (1 / ((n : ℝ) + 1) / 2) ^ (1 - κ₀) := fun n => by
    simp only [hT, hr, sub_sub_cancel]
  have hTlim : Tendsto (fun n => T (r n)) atTop (𝓝 0) := by
    simp only [hTr]
    have h := (h0lim.rpow_const (Or.inr (by linarith : (0 : ℝ) ≤ 1 - κ₀))).const_mul (4 / (1 - κ₀))
    rwa [Real.zero_rpow (by linarith : (1 - κ₀) ≠ 0), mul_zero] at h
  -- (c) the radial limits
  have hL : ∀ u : ℂ, ‖u‖ = 1 → Tendsto (fun n => (f ((r n : ℂ) * u))⁻¹) atTop
      (𝓝 (limUnder atTop fun n => (f ((r n : ℂ) * u))⁻¹)) := by
    intro u hu
    apply tendsto_nhds_limUnder
    apply cauchySeq_tendsto_of_complete
    refine cauchySeq_of_le_tendsto_0' (fun n => T (r n)) (fun n m hnm => ?_) hTlim
    rw [dist_comm, dist_eq_norm]
    exact hrad u hu (r n) (r m) (hr1 n) (hrmono hnm) (hr2 m)
  have hLb : ∀ u : ℂ, ‖u‖ = 1 → ∀ s : ℝ, 1 / 2 ≤ s → s < 1 →
      ‖(limUnder atTop fun n => (f ((r n : ℂ) * u))⁻¹) - (f ((s : ℂ) * u))⁻¹‖ ≤ T s := by
    intro u hu s hs1 hs2
    refine le_of_tendsto ((hL u hu).sub_const ((f ((s : ℂ) * u))⁻¹)).norm ?_
    filter_upwards [hrlim.eventually_const_lt hs2] with n hn
    exact hrad u hu s (r n) hs1 hn.le (hr2 n)
  obtain ⟨Ψ, hΨ⟩ : ∃ Ψ : ℂ → ℂ, Ψ = fun z =>
      if ‖z‖ < 1 then (f z)⁻¹ else limUnder atTop fun n => (f ((r n : ℂ) * z))⁻¹ := ⟨_, rfl⟩
  have hΨin : ∀ z : ℂ, ‖z‖ < 1 → Ψ z = (f z)⁻¹ := fun z h => by
    rw [hΨ]
    exact if_pos h
  have hΨout : ∀ z : ℂ, ¬ ‖z‖ < 1 → Ψ z = limUnder atTop fun n => (f ((r n : ℂ) * z))⁻¹ := fun z h => by
    rw [hΨ]
    exact if_neg h
  -- (d) `|Ψ z - Ψ(s z/|z|)| ≤ T s` for `s ≤ |z| ≤ 1`
  have hG : ∀ z : ℂ, ∀ s : ℝ, 1 / 2 ≤ s → s < 1 → s ≤ ‖z‖ → ‖z‖ ≤ 1 →
      ‖Ψ z - (f ((s : ℂ) * (z / (‖z‖ : ℂ))))⁻¹‖ ≤ T s := by
    intro z s hs1 hs2 hsz hz1
    have hzr : ‖z‖ ≠ 0 := by linarith
    have hzc : ((‖z‖ : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hzr
    have hu : ‖z / (‖z‖ : ℂ)‖ = 1 := by
      rw [norm_div, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _), div_self hzr]
    rcases hz1.lt_or_eq with h | h
    · rw [hΨin z h]
      have hzz : ((‖z‖ : ℝ) : ℂ) * (z / (‖z‖ : ℂ)) = z := by field_simp
      have := hrad (z / (‖z‖ : ℂ)) hu s ‖z‖ hs1 hsz h
      rwa [hzz] at this
    · rw [hΨout z (by rw [h]; exact lt_irrefl _)]
      have hz' : z / (‖z‖ : ℂ) = z := by
        rw [h]
        simp
      rw [hz']
      exact hLb z h s hs1 hs2
  have hΨ₀c : ∀ z : ℂ, ‖z‖ < 1 → z ≠ 0 → ContinuousAt (fun w => (f w)⁻¹) z := fun z h hz0 =>
    ((hfd z (hmem z h)).differentiableAt (hO.mem_nhds (hmem z h))).continuousAt.inv₀ (hfne z (hmem z h) hz0)
  -- (e) continuity
  have hc : ContinuousOn Ψ (closedBall 0 1 \ {0}) := by
    intro z hz
    have hz1 : ‖z‖ ≤ 1 := mem_closedBall_zero_iff.mp hz.1
    have hz0 : z ≠ 0 := hz.2
    rcases hz1.lt_or_eq with h | h
    · refine ((hΨ₀c z h hz0).congr ?_).continuousWithinAt
      filter_upwards [(isOpen_lt continuous_norm continuous_const).mem_nhds (show ‖z‖ < 1 from h)] with w hw
      exact (hΨin w hw).symm
    · rw [Metric.continuousWithinAt_iff]
      intro ε hε
      obtain ⟨n, hn⟩ := (hTlim.eventually (gt_mem_nhds (by positivity : (0 : ℝ) < ε / 3))).exists
      obtain ⟨s, hs1, hs2, hsT⟩ : ∃ s : ℝ, 1 / 2 ≤ s ∧ s < 1 ∧ T s < ε / 3 := ⟨r n, hr1 n, hr2 n, hn⟩
      have hzc : ((‖z‖ : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by rw [h]; exact one_ne_zero)
      have hz' : z / (‖z‖ : ℂ) = z := by
        rw [h]
        simp
      have hp : ContinuousAt (fun w : ℂ => (s : ℂ) * (w / (‖w‖ : ℂ))) z :=
        continuousAt_const.mul (continuousAt_id.div
          (Complex.continuous_ofReal.comp continuous_norm).continuousAt hzc)
      have hsz : ‖(s : ℂ) * (z / (‖z‖ : ℂ))‖ = s := by
        rw [hz', norm_mul, h, mul_one, Complex.norm_real, Real.norm_of_nonneg (by linarith)]
      have hq : ContinuousAt (fun w : ℂ => (f ((s : ℂ) * (w / (‖w‖ : ℂ))))⁻¹) z :=
        (hΨ₀c _ (by rw [hsz]; exact hs2) (by
          intro h0
          have := congrArg norm h0
          rw [hsz, norm_zero] at this
          linarith)).comp hp
      obtain ⟨δ, hδ, hδq⟩ := Metric.continuousAt_iff.mp hq (ε / 3) (by positivity)
      refine ⟨min δ (1 - s), lt_min hδ (by linarith), fun {w} hw hwz => ?_⟩
      have hw1 : ‖w‖ ≤ 1 := mem_closedBall_zero_iff.mp hw.1
      have hwz' : ‖w - z‖ < 1 - s := by
        have := hwz.trans_le (min_le_right _ _)
        rwa [dist_eq_norm] at this
      have hsw : s ≤ ‖w‖ := by
        have := norm_sub_norm_le z w
        rw [norm_sub_rev] at this
        linarith
      have e1 := hG w s hs1 hs2 hsw hw1
      have e2 := hG z s hs1 hs2 (by linarith) hz1
      have e3 : ‖(f ((s : ℂ) * (w / (‖w‖ : ℂ))))⁻¹ - (f ((s : ℂ) * (z / (‖z‖ : ℂ))))⁻¹‖ < ε / 3 := by
        have := hδq (hwz.trans_le (min_le_left _ _))
        rwa [dist_eq_norm] at this
      rw [dist_eq_norm]
      calc ‖Ψ w - Ψ z‖ = ‖(Ψ w - (f ((s : ℂ) * (w / (‖w‖ : ℂ))))⁻¹) +
            ((f ((s : ℂ) * (w / (‖w‖ : ℂ))))⁻¹ - (f ((s : ℂ) * (z / (‖z‖ : ℂ))))⁻¹) -
            (Ψ z - (f ((s : ℂ) * (z / (‖z‖ : ℂ))))⁻¹)‖ := by congr 1; ring
        _ ≤ ‖Ψ w - (f ((s : ℂ) * (w / (‖w‖ : ℂ))))⁻¹‖ +
            ‖(f ((s : ℂ) * (w / (‖w‖ : ℂ))))⁻¹ - (f ((s : ℂ) * (z / (‖z‖ : ℂ))))⁻¹‖ +
            ‖Ψ z - (f ((s : ℂ) * (z / (‖z‖ : ℂ))))⁻¹‖ := norm_sub_le_of_le (norm_add_le _ _) le_rfl
        _ < ε := by linarith
  have he : ∀ z ∈ unitDisc, z ≠ 0 → Ψ z = (f z)⁻¹ := fun z hz _ => hΨin z (mem_ball_zero_iff.mp hz)
  -- (f) disc × circle: an interior value is never a boundary value (open mapping)
  have hmix : ∀ a ζ : ℂ, ‖a‖ < 1 → a ≠ 0 → ‖ζ‖ = 1 → Ψ a ≠ Ψ ζ := by
    intro a ζ ha ha0 hζ hae
    have hD0 : unitDisc \ {0} ∈ 𝓝 a := (hO.sdiff isClosed_singleton).mem_nhds ⟨hmem a ha, ha0⟩
    have hdiff : DifferentiableOn ℂ (fun w => (f w)⁻¹) (unitDisc \ {0}) :=
      (hfd.mono sdiff_subset).inv fun w hw => hfne w hw.1 hw.2
    have hAn : AnalyticAt ℂ (fun w => (f w)⁻¹) a := hdiff.analyticAt hD0
    have hinj : ∀ v w : ℂ, ‖v‖ < 1 → ‖w‖ < 1 → (f v)⁻¹ = (f w)⁻¹ → v = w := fun v w hv hw h =>
      hfi (hmem v hv) (hmem w hw) (inv_inj.mp h)
    rcases hAn.eventually_constant_or_nhds_le_map_nhds with hconst | hopen
    · obtain ⟨ε, hε, hεb⟩ := Metric.eventually_nhds_iff.mp
        (hconst.and ((isOpen_lt continuous_norm continuous_const).mem_nhds (show ‖a‖ < 1 from ha)))
      have hw : dist (a + (ε / 2 : ℝ)) a < ε := by
        rw [dist_eq_norm, add_sub_cancel_left, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
        linarith
      obtain ⟨h1, h2⟩ := hεb hw
      have := hinj _ _ h2 ha h1
      have h3 : ((ε / 2 : ℝ) : ℂ) = 0 := by linear_combination this
      rw [Complex.ofReal_eq_zero] at h3
      linarith
    · obtain ⟨δ, hδ⟩ : ∃ δ : ℝ, δ = (1 - ‖a‖) / 2 := ⟨_, rfl⟩
      have hδ0 : 0 < δ := by rw [hδ]; linarith
      have hU : (fun w => (f w)⁻¹) '' ball a δ ∈ 𝓝 (Ψ ζ) := by
        rw [← hae, hΨin a ha]
        exact hopen (image_mem_map (ball_mem_nhds a hδ0))
      have hwt : Tendsto (fun n => (r n : ℂ) * ζ) atTop (𝓝 ζ) := by
        have := ((Complex.continuous_ofReal.tendsto 1).comp hrlim).mul_const ζ
        simpa using this
      have hws : ∀ n, (r n : ℂ) * ζ ∈ closedBall (0 : ℂ) 1 \ {0} := fun n => by
        have hn : ‖(r n : ℂ) * ζ‖ = r n := by
          rw [norm_mul, hζ, mul_one, Complex.norm_real, Real.norm_of_nonneg (by linarith [hr1 n])]
        refine ⟨mem_closedBall_zero_iff.mpr (by rw [hn]; exact (hr2 n).le), fun h0 => ?_⟩
        have h0' : ‖(r n : ℂ) * ζ‖ = 0 := by rw [Set.mem_singleton_iff.mp h0, norm_zero]
        rw [hn] at h0'
        linarith [hr1 n]
      have hζs : ζ ∈ closedBall (0 : ℂ) 1 \ {0} := ⟨mem_closedBall_zero_iff.mpr hζ.le, fun h0 => by
        rw [Set.mem_singleton_iff.mp h0, norm_zero] at hζ
        exact zero_ne_one hζ⟩
      have hΨt : Tendsto (fun n => Ψ ((r n : ℂ) * ζ)) atTop (𝓝 (Ψ ζ)) :=
        (hc ζ hζs).tendsto.comp (tendsto_nhdsWithin_iff.mpr ⟨hwt, Filter.Eventually.of_forall hws⟩)
      obtain ⟨n, hn1, hn2⟩ := ((hΨt.eventually hU).and
        (hrlim.eventually_const_lt (show ‖a‖ + δ < 1 by rw [hδ]; linarith))).exists
      have hrn : ‖(r n : ℂ) * ζ‖ = r n := by
        rw [norm_mul, hζ, mul_one, Complex.norm_real, Real.norm_of_nonneg (by linarith [hr1 n])]
      obtain ⟨v, hv, hvw⟩ := hn1
      have hv1 : ‖v‖ < ‖a‖ + δ := by
        have := norm_le_norm_add_norm_sub' v a
        rw [mem_ball, dist_eq_norm] at hv
        linarith [norm_sub_rev v a]
      rw [hΨin _ (by rw [hrn]; exact hr2 n)] at hvw
      have := hinj v _ (by linarith) (by rw [hrn]; exact hr2 n) hvw
      rw [this, hrn] at hv1
      linarith
  refine ⟨Ψ, hc, ?_, he⟩
  intro a ha b hb hab
  have ha1 : ‖a‖ ≤ 1 := mem_closedBall_zero_iff.mp ha.1
  have hb1 : ‖b‖ ≤ 1 := mem_closedBall_zero_iff.mp hb.1
  rcases ha1.lt_or_eq with h1 | h1 <;> rcases hb1.lt_or_eq with h2 | h2
  · rw [hΨin a h1, hΨin b h2] at hab
    exact hfi (hmem a h1) (hmem b h2) (inv_inj.mp hab)
  · exact absurd hab (hmix a b h1 ha.2 h2)
  · exact absurd hab.symm (hmix b a h2 hb.2 h1)
  · exact s5r58_wqd_bdry_inj hC hκ1 hfd hfi hf0 hf1 hrep hgol hc he
      (mem_sphere_zero_iff_norm.mpr h1) (mem_sphere_zero_iff_norm.mpr h2) hab

/-- **Sub-stub WQ3** (Pommerenke Thm 9.12, second half, + Lemma 9.8 (⇐), disc form). The bounded boundary curve `Ψ(S¹)`
has bounded turning: Möbius invariance of Golusin (Lemma 9.10, the `n + 1` trick) and (9.4.13) give a lower cross-ratio
bound, and the cross-ratio condition implies the arc condition. -/
theorem s5r58_wqd_turning {C : ℕ → ℕ → ℂ} (hC : C ∈ siegelDisk0) {κ : ℝ} (hκ1 : κ < 1) {f Ψ : ℂ → ℂ}
    (hfd : DifferentiableOn ℂ f unitDisc) (hfi : InjOn f unitDisc) (hf0 : f 0 = 0) (hf1 : deriv f 0 = 1)
    (hrep : ∀ z₁ ∈ unitDisc, ∀ z₂ ∈ unitDisc, z₁ ≠ 0 → z₂ ≠ 0 → z₁ ≠ z₂ → ∃ S,
      HasSum (fun q : ℕ × ℕ => C q.1 q.2 / Real.sqrt ((q.1 + 1) * (q.2 + 1)) * z₁ ^ (q.1 + 1) * z₂ ^ (q.2 + 1)) S ∧
      (f z₁ - f z₂) * z₁ * z₂ = (z₁ - z₂) * f z₁ * f z₂ * exp (-S))
    (hgol : ∀ (n : ℕ) (z γ : Fin n → ℂ), (∀ ν, z ν ∈ unitDisc) →
      ‖∑ μ, ∑ ν, γ μ * γ ν * ∑' q : ℕ × ℕ, C q.1 q.2 / Real.sqrt ((q.1 + 1) * (q.2 + 1)) *
          z μ ^ (q.1 + 1) * z ν ^ (q.2 + 1)‖ ≤
        κ * (∑ μ, ∑ ν, γ μ * conj (γ ν) * Complex.log (1 / (1 - z μ * conj (z ν)))).re)
    (hc : ContinuousOn Ψ (closedBall 0 1 \ {0})) (hi : InjOn Ψ (closedBall 0 1 \ {0}))
    (he : ∀ z ∈ unitDisc, z ≠ 0 → Ψ z = (f z)⁻¹) :
    ∃ M : ℝ, IsBoundedTurning (toExt (Ψ '' sphere (0 : ℂ) 1)) M := by
  obtain ⟨K, hK0, -, hKC⟩ := s5r58_wqd_opnorm hC
  have hK := s5r58_entry_le hC.1.2.1 hK0 hKC
  obtain ⟨c₀, hc₀, hcr⟩ := s5r58q_cross hK hκ1 hfd hfi hf0 hf1 hrep hgol hc hi he
  exact s5r58_bt_of_cross hc hi hc₀ hcr

/-- **Sub-stub WQ4** (quasidisc ⇒ q.c. extension). If `1/f` extends homeomorphically to `𝔻̄ ∖ 0` with a bounded-turning
boundary curve `J`, then for `-c` inside `J` the bounded map `f/(1 + c f) = 1/(1/f + c)` extends to a q.c. homeomorphism
of `ℂ` (`thm18_1`, `thm16_2` reflection across the quasicircle, gluing on `S¹`, `∞ ↦ ∞`). -/
theorem s5r58_wqd_extend {f Ψ : ℂ → ℂ} (hfd : DifferentiableOn ℂ f unitDisc) (hfi : InjOn f unitDisc)
    (hf0 : f 0 = 0) (hc : ContinuousOn Ψ (closedBall 0 1 \ {0})) (hi : InjOn Ψ (closedBall 0 1 \ {0}))
    (he : ∀ z ∈ unitDisc, z ≠ 0 → Ψ z = (f z)⁻¹) {M : ℝ}
    (hbt : IsBoundedTurning (toExt (Ψ '' sphere (0 : ℂ) 1)) M) :
    ∃ c : ℂ, (∀ z ∈ unitDisc, 1 + c * f z ≠ 0) ∧ ∃ F : ℂ → ℂ, IsQuasiconformal F univ ∧ F '' univ = univ ∧
      ∀ z ∈ unitDisc, F z = f z / (1 + c * f z) := by
  classical
  obtain ⟨A₁, A₂, R, hR, h12, h2J, hinfA, hΨA⟩ := s5r58_wq4_refl hfd hfi hf0 hc hi he hbt
  obtain ⟨hRc, hRi, hRA, hRJ, Kq, hQ⟩ := hR
  have hO : IsOpen unitDisc := Metric.isOpen_ball
  have hfne : ∀ z ∈ unitDisc, z ≠ 0 → f z ≠ 0 := fun z hz hz0 h =>
    hz0 (hfi hz (Metric.mem_ball_self one_pos) (h.trans hf0.symm))
  -- membership facts
  have hmemJ : ∀ z : ℂ, ‖z‖ = 1 → ((Ψ z : ℂ) : ExtPlane) ∈ toExt (Ψ '' sphere (0 : ℂ) 1) := fun z h =>
    ⟨Ψ z, ⟨z, mem_sphere_zero_iff_norm.mpr h, rfl⟩, rfl⟩
  have hmem1 : ∀ z : ℂ, ‖z‖ < 1 → z ≠ 0 → ((Ψ z : ℂ) : ExtPlane) ∈ A₁ := fun z h h0 =>
    hΨA z (mem_ball_zero_iff.mpr h) h0
  have hmemAJ : ∀ z : ℂ, z ≠ 0 → ‖z‖ ≤ 1 →
      ((Ψ z : ℂ) : ExtPlane) ∈ A₁ ∪ toExt (Ψ '' sphere (0 : ℂ) 1) := fun z h0 h1 => by
    rcases h1.lt_or_eq with h | h
    · exact Or.inl (hmem1 z h h0)
    · exact Or.inr (hmemJ z h)
  have hRA2 : ∀ p ∈ A₁, R p ∈ A₂ := fun p hp => hRA ▸ mem_image_of_mem R hp
  have hinfA2 : extInf ∉ A₂ := fun h => disjoint_left.1 h12 hinfA h
  have hRfin : ∀ p ∈ A₁, R p ≠ extInf := fun p hp h => hinfA2 (h ▸ hRA2 p hp)
  have hcoe : ∀ p : ExtPlane, p ≠ extInf → ((extToC p : ℂ) : ExtPlane) = p := by
    intro p hp
    obtain ⟨w, rfl⟩ := OnePoint.ne_infty_iff_exists.1 hp
    rfl
  obtain ⟨c, hcdef⟩ : ∃ c : ℂ, c = -extToC (R extInf) := ⟨_, rfl⟩
  have hRinf : R extInf = ((-c : ℂ) : ExtPlane) := by rw [hcdef, neg_neg, hcoe _ (hRfin _ hinfA)]
  have hmc : ((-c : ℂ) : ExtPlane) ∈ A₂ := hRinf ▸ hRA2 _ hinfA
  have hΨc : ∀ z : ℂ, z ≠ 0 → ‖z‖ ≤ 1 → Ψ z + c ≠ 0 := fun z h0 h1 h => by
    have he' : ((Ψ z : ℂ) : ExtPlane) = ((-c : ℂ) : ExtPlane) := by rw [eq_neg_of_add_eq_zero_left h]
    have hA : ((Ψ z : ℂ) : ExtPlane) ∈ A₂ := by rw [he']; exact hmc
    rcases hmemAJ z h0 h1 with h' | h'
    · exact disjoint_left.1 h12 h' hA
    · exact disjoint_left.1 h2J hA h'
  -- the reflection `τ z = 1 / z̄`
  have hτn : ∀ z : ℂ, ‖(conj z)⁻¹‖ = ‖z‖⁻¹ := fun z => by rw [norm_inv, Complex.norm_conj]
  have hτ0 : ∀ z : ℂ, z ≠ 0 → (conj z)⁻¹ ≠ 0 := fun z hz =>
    inv_ne_zero ((map_ne_zero _).mpr hz)
  have hτ1 : ∀ z : ℂ, ‖z‖ = 1 → (conj z)⁻¹ = z := fun z h => by
    apply inv_eq_of_mul_eq_one_right
    rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, h]
    norm_num
  have hτD : ∀ z : ℂ, 1 < ‖z‖ → ‖(conj z)⁻¹‖ < 1 ∧ (conj z)⁻¹ ≠ 0 := fun z h =>
    ⟨by rw [hτn]; exact inv_lt_one_of_one_lt₀ h, hτ0 z (norm_pos_iff.mp (by linarith))⟩
  have hτS : ∀ z : ℂ, 1 ≤ ‖z‖ → (conj z)⁻¹ ∈ closedBall (0 : ℂ) 1 \ {0} := fun z h =>
    ⟨mem_closedBall_zero_iff.mpr (by rw [hτn]; exact inv_le_one_of_one_le₀ h),
      hτ0 z (norm_pos_iff.mp (by linarith))⟩
  -- the exterior values
  have hExtAJ : ∀ z : ℂ, 1 ≤ ‖z‖ →
      ((Ψ (conj z)⁻¹ : ℂ) : ExtPlane) ∈ A₁ ∪ toExt (Ψ '' sphere (0 : ℂ) 1) := fun z h =>
    hmemAJ _ (hτS z h).2 (mem_closedBall_zero_iff.mp (hτS z h).1)
  have hExtfin : ∀ z : ℂ, 1 ≤ ‖z‖ → R ((Ψ (conj z)⁻¹ : ℂ) : ExtPlane) ≠ extInf := fun z h => by
    rcases hExtAJ z h with h' | h'
    · exact hRfin _ h'
    · rw [hRJ _ h']
      exact OnePoint.coe_ne_infty _
  have hExtc : ∀ z : ℂ, 1 ≤ ‖z‖ → extToC (R ((Ψ (conj z)⁻¹ : ℂ) : ExtPlane)) + c ≠ 0 := fun z h h0 => by
    have h1 : R ((Ψ (conj z)⁻¹ : ℂ) : ExtPlane) = R extInf := by
      rw [hRinf, ← hcoe _ (hExtfin z h), eq_neg_of_add_eq_zero_left h0]
    exact OnePoint.coe_ne_infty _ (hRi (hExtAJ z h) (Or.inl hinfA) h1)
  -- the map
  obtain ⟨F, hF⟩ : ∃ F : ℂ → ℂ, F = fun z => if ‖z‖ ≤ 1 then (if z = 0 then 0 else (Ψ z + c)⁻¹)
      else (extToC (R ((Ψ (conj z)⁻¹ : ℂ) : ExtPlane)) + c)⁻¹ := ⟨_, rfl⟩
  have hF0 : F 0 = 0 := by
    rw [hF]
    simp
  have hFin : ∀ z : ℂ, ‖z‖ ≤ 1 → z ≠ 0 → F z = (Ψ z + c)⁻¹ := fun z h h0 => by
    rw [hF]
    simp only [if_pos h, if_neg h0]
  have hFout : ∀ z : ℂ, 1 ≤ ‖z‖ → F z = (extToC (R ((Ψ (conj z)⁻¹ : ℂ) : ExtPlane)) + c)⁻¹ := fun z h => by
    rcases h.lt_or_eq with h' | h'
    · rw [hF]
      simp only [if_neg (not_le.mpr h')]
    · have hz0 : z ≠ 0 := norm_pos_iff.mp (by linarith)
      rw [hFin z h'.symm.le hz0, hτ1 z h'.symm, hRJ _ (hmemJ z h'.symm)]
      rfl
  have h1c : ∀ z ∈ unitDisc, 1 + c * f z ≠ 0 := by
    intro z hz
    by_cases hz0 : z = 0
    · rw [hz0, hf0, mul_zero, add_zero]
      exact one_ne_zero
    · have hfz := hfne z hz hz0
      have hk : 1 + c * f z = f z * (Ψ z + c) := by
        rw [he z hz hz0, mul_add, mul_inv_cancel₀ hfz, mul_comm]
      rw [hk]
      exact mul_ne_zero hfz (hΨc z hz0 (mem_ball_zero_iff.mp hz).le)
  have hFdisc : ∀ z ∈ unitDisc, F z = f z / (1 + c * f z) := by
    intro z hz
    by_cases hz0 : z = 0
    · rw [hz0, hF0, hf0, zero_div]
    · have hfz := hfne z hz hz0
      rw [hFin z (mem_ball_zero_iff.mp hz).le hz0, he z hz hz0]
      have key : (f z)⁻¹ + c = (1 + c * f z) * (f z)⁻¹ := by
        rw [add_mul, one_mul, mul_assoc, mul_inv_cancel₀ hfz, mul_one]
      rw [key, mul_inv, inv_inv, div_eq_mul_inv, mul_comm]
  -- continuity of the exterior formula on `{1 ≤ |z|}`
  have hFoW : ∀ z : ℂ, 1 ≤ ‖z‖ → ContinuousWithinAt
      (fun w : ℂ => (extToC (R ((Ψ (conj w)⁻¹ : ℂ) : ExtPlane)) + c)⁻¹) {w : ℂ | 1 ≤ ‖w‖} z := by
    intro z hz
    have hz0 : z ≠ 0 := norm_pos_iff.mp (by linarith)
    have hτc : ContinuousWithinAt (fun w : ℂ => (conj w)⁻¹) {w : ℂ | 1 ≤ ‖w‖} z :=
      (Complex.continuous_conj.continuousAt.inv₀ ((map_ne_zero _).mpr hz0)).continuousWithinAt
    have hΨ1 := ContinuousWithinAt.comp (g := Ψ) (f := fun w : ℂ => (conj w)⁻¹)
      (hc _ (hτS z hz)) hτc fun w hw => hτS w hw
    have hΨ2 := ContinuousAt.comp_continuousWithinAt (g := ((↑) : ℂ → ExtPlane))
      OnePoint.continuous_coe.continuousAt hΨ1
    have hΨw : ContinuousWithinAt (fun w : ℂ => ((Ψ (conj w)⁻¹ : ℂ) : ExtPlane)) {w : ℂ | 1 ≤ ‖w‖} z := hΨ2
    have hR1 := ContinuousWithinAt.comp (g := R) (f := fun w : ℂ => ((Ψ (conj w)⁻¹ : ℂ) : ExtPlane))
      (hRc _ (hExtAJ z hz)) hΨw fun w hw => hExtAJ w hw
    have hRw : ContinuousWithinAt (fun w : ℂ => R ((Ψ (conj w)⁻¹ : ℂ) : ExtPlane)) {w : ℂ | 1 ≤ ‖w‖} z := hR1
    have hE : ContinuousAt extToC (R ((Ψ (conj z)⁻¹ : ℂ) : ExtPlane)) := by
      have h := s16p_continuousAt_extToC (extToC (R ((Ψ (conj z)⁻¹ : ℂ) : ExtPlane)))
      rwa [hcoe _ (hExtfin z hz)] at h
    have hE1 := ContinuousAt.comp_continuousWithinAt (g := extToC)
      (f := fun w : ℂ => R ((Ψ (conj w)⁻¹ : ℂ) : ExtPlane)) hE hRw
    exact (hE1.add continuousWithinAt_const).inv₀ (hExtc z hz)
  have hFcont : Continuous F := by
    refine continuous_iff_continuousAt.mpr fun z => ?_
    rcases lt_trichotomy ‖z‖ 1 with h | h | h
    · have hzD : z ∈ unitDisc := mem_ball_zero_iff.mpr h
      have hg : ContinuousAt (fun w => f w / (1 + c * f w)) z :=
        (((hfd z hzD).differentiableAt (hO.mem_nhds hzD)).continuousAt).div
          (continuousAt_const.add (continuousAt_const.mul
            ((hfd z hzD).differentiableAt (hO.mem_nhds hzD)).continuousAt)) (h1c z hzD)
      refine hg.congr ?_
      filter_upwards [hO.mem_nhds hzD] with w hw
      exact (hFdisc w hw).symm
    · have hz0 : z ≠ 0 := norm_pos_iff.mp (by linarith)
      have hS₁ : ContinuousWithinAt F (closedBall 0 1 \ {0}) z := by
        refine ContinuousWithinAt.congr (((hc z ⟨mem_closedBall_zero_iff.mpr h.le, hz0⟩).add
          continuousWithinAt_const).inv₀ (hΨc z hz0 h.le)) (fun w hw => ?_) ?_
        · exact hFin w (mem_closedBall_zero_iff.mp hw.1) hw.2
        · exact hFin z h.le hz0
      have hS₂ : ContinuousWithinAt F {w : ℂ | 1 ≤ ‖w‖} z :=
        (hFoW z h.ge).congr (fun w hw => hFout w hw) (hFout z h.ge)
      have hU : (closedBall 0 1 \ {0}) ∪ {w : ℂ | 1 ≤ ‖w‖} ∈ 𝓝 z := by
        refine mem_of_superset (isOpen_ne.mem_nhds hz0) fun w hw => ?_
        by_cases hw1 : ‖w‖ ≤ 1
        · exact Or.inl ⟨mem_closedBall_zero_iff.mpr hw1, hw⟩
        · exact Or.inr (not_le.mp hw1).le
      exact (hS₁.union hS₂).continuousAt hU
    · have hU : {w : ℂ | 1 ≤ ‖w‖} ∈ 𝓝 z :=
        mem_of_superset ((isOpen_lt continuous_const continuous_norm).mem_nhds h) fun w hw => show 1 ≤ ‖w‖ from le_of_lt hw
      exact ((hFoW z h.le).congr (fun w hw => hFout w hw) (hFout z h.le)).continuousAt hU
  -- injectivity
  have hFne : ∀ z : ℂ, z ≠ 0 → F z ≠ 0 := by
    intro z hz0
    by_cases h : ‖z‖ ≤ 1
    · rw [hFin z h hz0]
      exact inv_ne_zero (hΨc z hz0 h)
    · rw [hFout z (not_le.mp h).le]
      exact inv_ne_zero (hExtc z (not_le.mp h).le)
  have hFinj : Function.Injective F := by
    intro a b hab
    by_cases ha0 : a = 0
    · by_contra hne
      have hb0 : b ≠ 0 := fun h => hne (ha0.trans h.symm)
      exact hFne b hb0 (hab ▸ ha0 ▸ hF0)
    by_cases hb0 : b = 0
    · exact absurd (hab.trans (hb0 ▸ hF0)) (hFne a ha0)
    by_cases ha : ‖a‖ ≤ 1 <;> by_cases hb : ‖b‖ ≤ 1
    · rw [hFin a ha ha0, hFin b hb hb0, inv_inj, add_left_inj] at hab
      exact hi ⟨mem_closedBall_zero_iff.mpr ha, ha0⟩ ⟨mem_closedBall_zero_iff.mpr hb, hb0⟩ hab
    · exfalso
      have hb' := (not_le.mp hb).le
      rw [hFin a ha ha0, hFout b hb', inv_inj, add_left_inj] at hab
      have h1 : ((Ψ a : ℂ) : ExtPlane) = R ((Ψ (conj b)⁻¹ : ℂ) : ExtPlane) := by
        rw [hab, hcoe _ (hExtfin b hb')]
      have h2 : R ((Ψ (conj b)⁻¹ : ℂ) : ExtPlane) ∈ A₂ := hRA2 _ (hmem1 _ (hτD b (not_le.mp hb)).1
        (hτD b (not_le.mp hb)).2)
      rw [← h1] at h2
      rcases hmemAJ a ha0 ha with h' | h'
      · exact disjoint_left.1 h12 h' h2
      · exact disjoint_left.1 h2J h2 h'
    · exfalso
      have ha' := (not_le.mp ha).le
      rw [hFin b hb hb0, hFout a ha', inv_inj, add_left_inj] at hab
      have h1 : ((Ψ b : ℂ) : ExtPlane) = R ((Ψ (conj a)⁻¹ : ℂ) : ExtPlane) := by
        rw [← hab, hcoe _ (hExtfin a ha')]
      have h2 : R ((Ψ (conj a)⁻¹ : ℂ) : ExtPlane) ∈ A₂ := hRA2 _ (hmem1 _ (hτD a (not_le.mp ha)).1
        (hτD a (not_le.mp ha)).2)
      rw [← h1] at h2
      rcases hmemAJ b hb0 hb with h' | h'
      · exact disjoint_left.1 h12 h' h2
      · exact disjoint_left.1 h2J h2 h'
    · have ha' := (not_le.mp ha).le
      have hb' := (not_le.mp hb).le
      rw [hFout a ha', hFout b hb', inv_inj, add_left_inj] at hab
      have h1 : R ((Ψ (conj a)⁻¹ : ℂ) : ExtPlane) = R ((Ψ (conj b)⁻¹ : ℂ) : ExtPlane) := by
        rw [← hcoe _ (hExtfin a ha'), ← hcoe _ (hExtfin b hb'), hab]
      have h2 := OnePoint.coe_injective (hRi (hExtAJ a ha') (hExtAJ b hb') h1)
      have h3 := hi (hτS a ha') (hτS b hb') h2
      rw [inv_inj] at h3
      exact (RingHom.injective _ h3 : a = b)
  -- properness
  have hcob : (Bornology.cobounded ℂ) = cocompact ℂ := Metric.cobounded_eq_cocompact
  have hτt : Tendsto (fun z : ℂ => (conj z)⁻¹) (cocompact ℂ) (𝓝[ball (0 : ℂ) 1 \ {0}] 0) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · have h := (Complex.continuous_conj.tendsto 0).comp (tendsto_inv₀_cobounded (α := ℂ))
      rw [hcob, map_zero] at h
      refine h.congr fun z => ?_
      simp [Function.comp]
    · filter_upwards [tendsto_norm_cocompact_atTop.eventually (eventually_gt_atTop 1)] with z hz
      exact ⟨mem_ball_zero_iff.mpr (hτD z hz).1, (hτD z hz).2⟩
  have h0D : (0 : ℂ) ∈ unitDisc := Metric.mem_ball_self one_pos
  have hft : Tendsto f (𝓝[ball (0 : ℂ) 1 \ {0}] 0) (𝓝[≠] 0) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · have h := ((hfd 0 h0D).differentiableAt (hO.mem_nhds h0D)).continuousAt.tendsto
      rw [hf0] at h
      exact h.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with u hu
      exact hfne u hu.1 hu.2
  have hΨt : Tendsto (fun u : ℂ => ((Ψ u : ℂ) : ExtPlane)) (𝓝[ball (0 : ℂ) 1 \ {0}] 0) (𝓝 extInf) := by
    have h := (tendsto_inv₀_nhdsNE_zero (α := ℂ)).comp hft
    rw [hcob, ← Filter.coclosedCompact_eq_cocompact] at h
    refine (OnePoint.tendsto_coe_infty.comp h).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with u hu
    simp only [Function.comp_apply, he u hu.1 hu.2]
  have hRt : Tendsto (fun z : ℂ => R ((Ψ (conj z)⁻¹ : ℂ) : ExtPlane)) (cocompact ℂ) (𝓝 (R extInf)) := by
    refine (hRc extInf (Or.inl hinfA)).tendsto.comp (tendsto_nhdsWithin_iff.mpr ⟨hΨt.comp hτt, ?_⟩)
    filter_upwards [tendsto_norm_cocompact_atTop.eventually (eventually_ge_atTop 1)] with z hz
    exact hExtAJ z hz
  have hEt : Tendsto (fun z : ℂ => extToC (R ((Ψ (conj z)⁻¹ : ℂ) : ExtPlane)) + c) (cocompact ℂ) (𝓝[≠] 0) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · have h := ((s16p_continuousAt_extToC (-c)).tendsto.comp (hRinf ▸ hRt)).add_const c
      have h' : extToC ((-c : ℂ) : ExtPlane) + c = 0 := by
        show -c + c = 0
        ring
      rwa [h'] at h
    · filter_upwards [tendsto_norm_cocompact_atTop.eventually (eventually_ge_atTop 1)] with z hz
      exact hExtc z hz
  have hprop : Tendsto F (cocompact ℂ) (cocompact ℂ) := by
    have h := (tendsto_inv₀_nhdsNE_zero (α := ℂ)).comp hEt
    rw [hcob] at h
    refine h.congr' ?_
    filter_upwards [tendsto_norm_cocompact_atTop.eventually (eventually_ge_atTop 1)] with z hz
    exact (hFout z hz).symm
  obtain ⟨e, he'⟩ := lemma12_1 hFcont hprop fun _ => ⟨univ, univ_mem, hFinj.injOn⟩
  have hFhom : IsHomeomorphOnto F univ univ := by
    rw [← he']
    exact nxI1_isHomeomorphOnto_of_homeomorph e
  have hFs : F '' univ = univ := hFhom.2.2.1
  -- quasiconformality off the circle
  have hKq : 1 ≤ Kq := hQ.2.1
  have hdisc : IsKQC F (ball (0 : ℂ) 1) Kq := by
    have h := isKQC_one_of_conformal (f := fun w => f w / (1 + c * f w)) Metric.isOpen_ball
      ⟨hfd.div ((differentiableOn_const 1).add ((differentiableOn_const c).mul hfd)) h1c,
        fun a ha b hb hab => by
          have h' : f a / (1 + c * f a) = f b / (1 + c * f b) := hab
          rw [div_eq_div_iff (h1c a ha) (h1c b hb)] at h'
          exact hfi ha hb (by linear_combination h'), rfl⟩
    exact ad_isKQC_congr (h.mono hKq) fun w hw => hFdisc w hw
  obtain ⟨D, hD⟩ : ∃ D : Set ℂ, D = ball (0 : ℂ) 1 \ {0} := ⟨_, rfl⟩
  have hDo : IsOpen D := by rw [hD]; exact Metric.isOpen_ball.sdiff isClosed_singleton
  have hΨD : IsKQC Ψ D 1 := by
    refine isKQC_one_of_conformal hDo ⟨?_, ?_, rfl⟩
    · refine ((hfd.mono fun w hw => (hD ▸ hw).1).inv fun w hw => hfne w (hD ▸ hw).1 (hD ▸ hw).2).congr ?_
      intro w hw
      exact he w (hD ▸ hw).1 (hD ▸ hw).2
    · refine hi.mono fun w hw => ?_
      rw [hD] at hw
      exact ⟨ball_subset_closedBall hw.1, hw.2⟩
  have hsub1 : Ψ '' D ⊆ {z : ℂ | (z : ExtPlane) ∈ A₁ ∧ R z ≠ extInf} := by
    rintro _ ⟨u, hu, rfl⟩
    rw [hD] at hu
    exact ⟨hΨA u hu.1 hu.2, hRfin _ (hΨA u hu.1 hu.2)⟩
  have h1 := thm7_1_comp hΨD hQ hsub1
  have hsub2 : ((fun z : ℂ => conj (extToC (R z))) ∘ Ψ) '' D ⊆ {-conj c}ᶜ := by
    rintro _ ⟨u, hu, rfl⟩ hq
    rw [hD] at hu
    have hq' : conj (extToC (R ((Ψ u : ℂ) : ExtPlane))) = -conj c := hq
    have hq'' : extToC (R ((Ψ u : ℂ) : ExtPlane)) = -c := by
      have := congrArg conj hq'
      simpa using this
    have hA := hΨA u hu.1 hu.2
    have h' : R ((Ψ u : ℂ) : ExtPlane) = R extInf := by
      rw [hRinf, ← hq'', hcoe _ (hRfin _ hA)]
    exact OnePoint.coe_ne_infty _ (hRi (Or.inl hA) (Or.inl hinfA) h')
  have h2 := thm7_1_comp h1 (b4_qc_invShift_isKQC (-conj c)) hsub2
  have h3 := abR_x_isKQC_conj h2
  obtain ⟨U, hU⟩ : ∃ U : Set ℂ, U = {w : ℂ | 1 < ‖w‖} := ⟨_, rfl⟩
  have hUo : IsOpen U := by rw [hU]; exact isOpen_lt continuous_const continuous_norm
  have hinvU : IsKQC (fun z : ℂ => z⁻¹) U 1 := by
    refine isKQC_one_of_conformal hUo ⟨fun w hw => ?_, fun a _ b _ hab => inv_injective hab, rfl⟩
    have hw0 : w ≠ 0 := norm_pos_iff.mp (by rw [hU] at hw; exact lt_trans one_pos hw)
    exact (differentiableAt_inv hw0).differentiableWithinAt
  have hsub3 : (fun z : ℂ => z⁻¹) '' U ⊆ conj ⁻¹' D := by
    rintro _ ⟨z, hz, rfl⟩
    rw [hU] at hz
    show conj z⁻¹ ∈ D
    rw [hD, map_inv₀]
    exact ⟨mem_ball_zero_iff.mpr (hτD z hz).1, (hτD z hz).2⟩
  have h4 := thm7_1_comp hinvU h3 hsub3
  have hext : IsKQC F U Kq := by
    refine ad_isKQC_congr (h4.mono (le_of_eq (by ring))) fun z hz => ?_
    rw [hU] at hz
    rw [hFout z hz.le]
    simp only [Function.comp_apply, map_inv₀, map_add, map_neg, Complex.conj_conj, sub_neg_eq_add]
  -- gluing across the circle
  have hkey : ∀ x y : ℝ, (x : ℂ) + (y : ℂ) * I ∈ sphere (0 : ℂ) 1 → x ^ 2 + y ^ 2 = 1 := by
    intro x y h
    have h1 := mem_sphere_zero_iff_norm.mp h
    have h2 : ‖(x : ℂ) + (y : ℂ) * I‖ ^ 2 = x ^ 2 + y ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_add_mul_I]
    rw [h1] at h2
    linarith
  have hroots : ∀ a b : ℝ, a ^ 2 + b ^ 2 = 1 → b = Real.sqrt (1 - a ^ 2) ∨ b = -Real.sqrt (1 - a ^ 2) := by
    intro a b h
    have hs : Real.sqrt (1 - a ^ 2) ^ 2 = 1 - a ^ 2 := Real.sq_sqrt (by nlinarith)
    exact sq_eq_sq_iff_eq_or_eq_neg.mp (by rw [hs]; linarith)
  have hFhom' : IsHomeomorphOnto F univ (F '' univ) := by
    rw [hFs]
    exact hFhom
  have hqc : IsKQC F univ Kq := by
    refine s13x_removable (L := sphere (0 : ℂ) 1) isOpen_univ hKq hFhom' (Measure.addHaar_sphere volume 0 1)
      (Filter.Eventually.of_forall fun x => ?_) (Filter.Eventually.of_forall fun y => ?_) fun z hz => ?_
    · refine (((countable_singleton (-Real.sqrt (1 - x ^ 2))).insert (Real.sqrt (1 - x ^ 2))).mono
        fun y hy => ?_)
      rcases hroots x y (hkey x y hy) with h | h
      · exact Or.inl h
      · exact Or.inr h
    · refine (((countable_singleton (-Real.sqrt (1 - y ^ 2))).insert (Real.sqrt (1 - y ^ 2))).mono
        fun x hx => ?_)
      rcases hroots y x (by linarith [hkey x y hx]) with h | h
      · exact Or.inl h
      · exact Or.inr h
    · have hz1 : ‖z‖ ≠ 1 := fun h => hz.2 (mem_sphere_zero_iff_norm.mpr h)
      rcases lt_or_gt_of_ne hz1 with h | h
      · exact ⟨ball 0 1, Metric.isOpen_ball, mem_ball_zero_iff.mpr h, subset_univ _, hdisc⟩
      · exact ⟨U, hUo, by rw [hU]; exact h, subset_univ _, hext⟩
  exact ⟨c, h1c, F, ⟨Kq, hqc⟩, hFs, hFdisc⟩

/-- **Stub W-QD.** A univalent normalized `f` on `𝔻` whose Grunsky matrix `C` lies in `𝔇_∞⁰` (so `‖C‖ < 1`) has, after
the renormalization `f/(1 + c f)` (which makes `f(𝔻)` bounded; `f(𝔻)` itself may be unbounded, e.g. `z/(1 - z)`), a q.c.
extension to `ℂ` (Pommerenke 1975 Thm 9.12, then the LiZhongQC quasicircle theory). -/
theorem s5r58_qc_ext {C : ℕ → ℕ → ℂ} (hC : C ∈ siegelDisk0) {f : ℂ → ℂ}
    (hfd : DifferentiableOn ℂ f unitDisc) (hfi : InjOn f unitDisc) (hf0 : f 0 = 0) (hf1 : deriv f 0 = 1)
    (hrep : ∀ z₁ ∈ unitDisc, ∀ z₂ ∈ unitDisc, z₁ ≠ 0 → z₂ ≠ 0 → z₁ ≠ z₂ → ∃ S,
      HasSum (fun q : ℕ × ℕ => C q.1 q.2 / Real.sqrt ((q.1 + 1) * (q.2 + 1)) * z₁ ^ (q.1 + 1) * z₂ ^ (q.2 + 1)) S ∧
      (f z₁ - f z₂) * z₁ * z₂ = (z₁ - z₂) * f z₁ * f z₂ * exp (-S)) :
    ∃ c : ℂ, (∀ z ∈ unitDisc, 1 + c * f z ≠ 0) ∧ ∃ F : ℂ → ℂ, IsQuasiconformal F univ ∧ F '' univ = univ ∧
      ∀ z ∈ unitDisc, F z = f z / (1 + c * f z) := by
  obtain ⟨κ, hκ0, hκ1, hκ⟩ := s5r58_wqd_opnorm hC
  have hgol := fun n z γ hz => s5r58_wqd_golusin hC.1.2.1 (n := n) hκ0 hκ z γ hz
  obtain ⟨Ψ, hc, hi, he⟩ := s5r58_wqd_boundary hC hκ1 hfd hfi hf0 hf1 hrep hgol
  obtain ⟨M, hbt⟩ := s5r58_wqd_turning hC hκ1 hfd hfi hf0 hf1 hrep hgol hc hi he
  exact s5r58_wqd_extend hfd hfi hf0 hc hi he hbt

/-- **Stub RN.** The renormalization `f/(1 + c f)` (i.e. `1/f ↦ 1/f + c`) keeps univalence, the normalization at `0`
and the mixed representation with the same coefficients. -/
theorem s5r58_renorm {C : ℕ → ℕ → ℂ} {f : ℂ → ℂ}
    (hfd : DifferentiableOn ℂ f unitDisc) (hfi : InjOn f unitDisc) (hf0 : f 0 = 0) (hf1 : deriv f 0 = 1)
    (hrep : ∀ z₁ ∈ unitDisc, ∀ z₂ ∈ unitDisc, z₁ ≠ 0 → z₂ ≠ 0 → z₁ ≠ z₂ → ∃ S,
      HasSum (fun q : ℕ × ℕ => C q.1 q.2 / Real.sqrt ((q.1 + 1) * (q.2 + 1)) * z₁ ^ (q.1 + 1) * z₂ ^ (q.2 + 1)) S ∧
      (f z₁ - f z₂) * z₁ * z₂ = (z₁ - z₂) * f z₁ * f z₂ * exp (-S))
    {c : ℂ} (hc : ∀ z ∈ unitDisc, 1 + c * f z ≠ 0) :
    DifferentiableOn ℂ (fun z => f z / (1 + c * f z)) unitDisc ∧ InjOn (fun z => f z / (1 + c * f z)) unitDisc ∧
      f 0 / (1 + c * f 0) = 0 ∧ deriv (fun z => f z / (1 + c * f z)) 0 = 1 ∧
      ∀ z₁ ∈ unitDisc, ∀ z₂ ∈ unitDisc, z₁ ≠ 0 → z₂ ≠ 0 → z₁ ≠ z₂ → ∃ S,
        HasSum (fun q : ℕ × ℕ => C q.1 q.2 / Real.sqrt ((q.1 + 1) * (q.2 + 1)) * z₁ ^ (q.1 + 1) * z₂ ^ (q.2 + 1)) S ∧
        (f z₁ / (1 + c * f z₁) - f z₂ / (1 + c * f z₂)) * z₁ * z₂ =
          (z₁ - z₂) * (f z₁ / (1 + c * f z₁)) * (f z₂ / (1 + c * f z₂)) * exp (-S) := by
  have hO : IsOpen unitDisc := Metric.isOpen_ball
  have h0 : (0 : ℂ) ∈ unitDisc := Metric.mem_ball_self one_pos
  refine ⟨hfd.div ((differentiableOn_const 1).add ((differentiableOn_const c).mul hfd)) hc, ?_, ?_, ?_, ?_⟩
  · intro z₁ hz₁ z₂ hz₂ h
    have h' : f z₁ / (1 + c * f z₁) = f z₂ / (1 + c * f z₂) := h
    rw [div_eq_div_iff (hc z₁ hz₁) (hc z₂ hz₂)] at h'
    exact hfi hz₁ hz₂ (by linear_combination h')
  · rw [hf0, zero_div]
  · have hfa : HasDerivAt f 1 0 := by
      rw [← hf1]
      exact ((hfd 0 h0).differentiableAt (hO.mem_nhds h0)).hasDerivAt
    have hD : HasDerivAt (fun z => 1 + c * f z) (c * 1) 0 := (hfa.const_mul c).const_add 1
    have hD0 : 1 + c * f 0 ≠ 0 := by rw [hf0, mul_zero, add_zero]; exact one_ne_zero
    have h : HasDerivAt (fun z => f z / (1 + c * f z)) ((1 * (1 + c * f 0) - f 0 * (c * 1)) / (1 + c * f 0) ^ 2) 0 :=
      hfa.div hD hD0
    rw [h.deriv, hf0]
    simp
  · intro z₁ hz₁ z₂ hz₂ hz₁0 hz₂0 hne
    obtain ⟨S, hS, h⟩ := hrep z₁ hz₁ z₂ hz₂ hz₁0 hz₂0 hne
    refine ⟨S, hS, ?_⟩
    have hD₁ := hc z₁ hz₁
    have hD₂ := hc z₂ hz₂
    have e₁ : (f z₁ / (1 + c * f z₁) - f z₂ / (1 + c * f z₂)) * z₁ * z₂ =
        (f z₁ - f z₂) * z₁ * z₂ / ((1 + c * f z₁) * (1 + c * f z₂)) := by
      rw [div_sub_div _ _ hD₁ hD₂]
      ring
    have e₂ : (z₁ - z₂) * (f z₁ / (1 + c * f z₁)) * (f z₂ / (1 + c * f z₂)) * exp (-S) =
        (z₁ - z₂) * f z₁ * f z₂ * exp (-S) / ((1 + c * f z₁) * (1 + c * f z₂)) := by
      simp only [div_eq_mul_inv, mul_inv]
      ring
    rw [e₁, e₂, h]

/-- Summability at `(1/2, -1/2)` bounds the coefficients of a mixed double series. -/
theorem s5r58_coeff_bd {a : ℕ → ℕ → ℂ}
    (h : Summable fun q : ℕ × ℕ => a q.1 q.2 * (1 / 2 : ℂ) ^ (q.1 + 1) * (-1 / 2 : ℂ) ^ (q.2 + 1)) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ q : ℕ × ℕ, ‖a q.1 q.2‖ * (1 / 2 : ℝ) ^ (q.1 + 1) * (1 / 2 : ℝ) ^ (q.2 + 1) ≤ M := by
  have ht := h.tendsto_cofinite_zero.norm
  rw [norm_zero] at ht
  obtain ⟨M, hM⟩ := ht.bddAbove_range_of_cofinite
  have hq : ∀ q : ℕ × ℕ, ‖a q.1 q.2 * (1 / 2 : ℂ) ^ (q.1 + 1) * (-1 / 2 : ℂ) ^ (q.2 + 1)‖ =
      ‖a q.1 q.2‖ * (1 / 2 : ℝ) ^ (q.1 + 1) * (1 / 2 : ℝ) ^ (q.2 + 1) := by
    intro q
    rw [norm_mul, norm_mul, norm_pow, norm_pow]
    norm_num
  refine ⟨M, (norm_nonneg _).trans (hM ⟨(0, 0), rfl⟩), fun q => ?_⟩
  rw [← hq]
  exact hM ⟨q, rfl⟩

/-- The rescaled coefficients `a_{mn} ρ^{m+1} ρ^{n+1}`, `ρ = δ/2`, are dominated by `M δ² 2^{-m} 2^{-n}`. -/
theorem s5r58_resc_bd {a : ℕ → ℕ → ℂ} {Ma M δ : ℝ}
    (hMa : ∀ q : ℕ × ℕ, ‖a q.1 q.2‖ * (1 / 2 : ℝ) ^ (q.1 + 1) * (1 / 2 : ℝ) ^ (q.2 + 1) ≤ Ma) (hM : Ma ≤ M)
    (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 2) (m n : ℕ) :
    ‖a m n * ((1 / 2 * δ : ℝ) : ℂ) ^ (m + 1) * ((1 / 2 * δ : ℝ) : ℂ) ^ (n + 1)‖ ≤
      M * δ ^ 2 * ((1 / 2 : ℝ) ^ m * (1 / 2 : ℝ) ^ n) := by
  have hM0 : 0 ≤ M := ((by positivity : (0 : ℝ) ≤ ‖a 0 0‖ * (1 / 2 : ℝ) ^ (0 + 1) * (1 / 2 : ℝ) ^ (0 + 1)).trans
    (hMa (0, 0))).trans hM
  have hA : ‖a m n‖ * (1 / 2 : ℝ) ^ (m + 1) * (1 / 2 : ℝ) ^ (n + 1) ≤ M := (hMa (m, n)).trans hM
  have hρ0 : (0 : ℝ) ≤ 1 / 2 * δ := by positivity
  have hp : ∀ k : ℕ, δ ^ (k + 1) ≤ δ * (1 / 2 : ℝ) ^ k := fun k => by
    rw [pow_succ']
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hδ0.le hδ1 k) hδ0.le
  have e : ‖a m n * ((1 / 2 * δ : ℝ) : ℂ) ^ (m + 1) * ((1 / 2 * δ : ℝ) : ℂ) ^ (n + 1)‖ =
      (‖a m n‖ * (1 / 2 : ℝ) ^ (m + 1) * (1 / 2 : ℝ) ^ (n + 1)) * (δ ^ (m + 1) * δ ^ (n + 1)) := by
    simp only [norm_mul, norm_pow, Complex.norm_of_nonneg hρ0]
    rw [mul_pow, mul_pow]
    ring
  rw [e]
  calc (‖a m n‖ * (1 / 2 : ℝ) ^ (m + 1) * (1 / 2 : ℝ) ^ (n + 1)) * (δ ^ (m + 1) * δ ^ (n + 1))
      ≤ M * (δ ^ (m + 1) * δ ^ (n + 1)) := mul_le_mul_of_nonneg_right hA (by positivity)
    _ ≤ M * ((δ * (1 / 2 : ℝ) ^ m) * (δ * (1 / 2 : ℝ) ^ n)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul (hp m) (hp n) (by positivity) (by positivity)) hM0
    _ = M * δ ^ 2 * ((1 / 2 : ℝ) ^ m * (1 / 2 : ℝ) ^ n) := by ring

/-- Two functions continuous on an open set that agree off two points agree everywhere on it. -/
theorem s5r58_eq_of_punct {f g : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U) (hf : ContinuousOn f U)
    (hg : ContinuousOn g U) {p₁ p₂ : ℂ} (h : ∀ z ∈ U, z ≠ p₁ → z ≠ p₂ → f z = g z) :
    ∀ z ∈ U, f z = g z := by
  intro z hz
  have hne : ∀ p : ℂ, ∀ᶠ y in 𝓝[≠] z, y ≠ p := by
    intro p
    by_cases hp : p = z
    · rw [hp]; exact self_mem_nhdsWithin
    · exact nhdsWithin_le_nhds (eventually_ne_nhds (Ne.symm hp))
  have hev : f =ᶠ[𝓝[≠] z] g := by
    filter_upwards [nhdsWithin_le_nhds (hU.mem_nhds hz), hne p₁, hne p₂] with y hy h1 h2
    exact h y hy h1 h2
  have hfl := ((hf z hz).continuousAt (hU.mem_nhds hz)).tendsto.mono_left
    (nhdsWithin_le_nhds (s := {z}ᶜ))
  have hgl := ((hg z hz).continuousAt (hU.mem_nhds hz)).tendsto.mono_left
    (nhdsWithin_le_nhds (s := {z}ᶜ))
  exact tendsto_nhds_unique (hfl.congr' hev) hgl

/-- Uniqueness of mixed Grunsky coefficients: two mixed double series whose exponentials agree on
`(𝔻 ∖ 0)²` off the diagonal have the same coefficients (the `2πiℤ` ambiguity is removed on a small bidisc). -/
theorem s5r58_coeff_unique {a b : ℕ → ℕ → ℂ}
    (h : ∀ z₁ ∈ unitDisc, ∀ z₂ ∈ unitDisc, z₁ ≠ 0 → z₂ ≠ 0 → z₁ ≠ z₂ → ∃ S S' : ℂ,
      HasSum (fun q : ℕ × ℕ => a q.1 q.2 * z₁ ^ (q.1 + 1) * z₂ ^ (q.2 + 1)) S ∧
      HasSum (fun q : ℕ × ℕ => b q.1 q.2 * z₁ ^ (q.1 + 1) * z₂ ^ (q.2 + 1)) S' ∧ exp (-S) = exp (-S')) :
    a = b := by
  have hDo : IsOpen unitDisc := Metric.isOpen_ball
  have hhalf : (1 / 2 : ℂ) ∈ unitDisc := by norm_num [unitDisc, mem_ball, dist_zero_right]
  have hmhalf : (-1 / 2 : ℂ) ∈ unitDisc := by norm_num [unitDisc, mem_ball, dist_zero_right]
  obtain ⟨S₀, S₀', hA0, hB0, -⟩ := h _ hhalf _ hmhalf (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨Ma, hMa0, hMa⟩ := s5r58_coeff_bd hA0.summable
  obtain ⟨Mb, hMb0, hMb⟩ := s5r58_coeff_bd hB0.summable
  obtain ⟨δ, hδ⟩ : ∃ δ : ℝ, δ = 1 / (2 * (Ma + Mb + 1)) := ⟨_, rfl⟩
  have hδ0 : 0 < δ := by rw [hδ]; positivity
  have hδM : δ * (2 * (Ma + Mb + 1)) = 1 := by rw [hδ]; field_simp
  have hδ1 : δ ≤ 1 / 2 := by nlinarith
  have hMδ : (Ma + Mb) * δ ^ 2 ≤ 1 / 4 := by
    have h1 : (Ma + Mb) * δ ≤ 1 / 2 := by nlinarith
    nlinarith [mul_le_mul h1 hδ1 hδ0.le (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  have hρ0 : (0 : ℝ) < 1 / 2 * δ := by positivity
  have hρ : ((1 / 2 * δ : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hρ0.ne'
  obtain ⟨α, hα⟩ : ∃ α : ℕ → ℕ → ℂ,
      α = fun m n => a m n * ((1 / 2 * δ : ℝ) : ℂ) ^ (m + 1) * ((1 / 2 * δ : ℝ) : ℂ) ^ (n + 1) := ⟨_, rfl⟩
  obtain ⟨β, hβ⟩ : ∃ β : ℕ → ℕ → ℂ,
      β = fun m n => b m n * ((1 / 2 * δ : ℝ) : ℂ) ^ (m + 1) * ((1 / 2 * δ : ℝ) : ℂ) ^ (n + 1) := ⟨_, rfl⟩
  have hαb : ∀ m n, ‖α m n‖ ≤ (Ma + Mb) * δ ^ 2 * ((1 / 2 : ℝ) ^ m * (1 / 2 : ℝ) ^ n) := fun m n => by
    rw [hα]; exact s5r58_resc_bd hMa (by linarith) hδ0 hδ1 m n
  have hβb : ∀ m n, ‖β m n‖ ≤ (Ma + Mb) * δ ^ 2 * ((1 / 2 : ℝ) ^ m * (1 / 2 : ℝ) ^ n) := fun m n => by
    rw [hβ]; exact s5r58_resc_bd hMb (by linarith) hδ0 hδ1 m n
  -- the dominating series
  have hsn : Summable fun n : ℕ => ‖(1 / 2 : ℝ) ^ n‖ :=
    summable_geometric_two.congr fun n => (Real.norm_of_nonneg (by positivity)).symm
  have hg2 : HasSum (fun q : ℕ × ℕ => (1 / 2 : ℝ) ^ q.1 * (1 / 2 : ℝ) ^ q.2) (2 * 2) :=
    hasSum_geometric_two.mul hasSum_geometric_two (summable_mul_of_summable_norm hsn hsn)
  have hG := hg2.mul_left ((Ma + Mb) * δ ^ 2)
  have hterm : ∀ c : ℕ → ℕ → ℂ, (∀ m n, ‖c m n‖ ≤ (Ma + Mb) * δ ^ 2 * ((1 / 2 : ℝ) ^ m * (1 / 2 : ℝ) ^ n)) →
      ∀ z w : ℂ, ‖z‖ ≤ 1 → ‖w‖ ≤ 1 → ∀ q : ℕ × ℕ,
        ‖c q.1 q.2 * z ^ q.1 * w ^ q.2‖ ≤ (Ma + Mb) * δ ^ 2 * ((1 / 2 : ℝ) ^ q.1 * (1 / 2 : ℝ) ^ q.2) := by
    intro c hc z w hz hw q
    rw [norm_mul, norm_mul, norm_pow, norm_pow]
    calc ‖c q.1 q.2‖ * ‖z‖ ^ q.1 * ‖w‖ ^ q.2 ≤ ‖c q.1 q.2‖ * 1 * 1 := by
          gcongr
          · exact pow_le_one₀ (norm_nonneg _) hz
          · exact pow_le_one₀ (norm_nonneg _) hw
      _ ≤ _ := by rw [mul_one, mul_one]; exact hc q.1 q.2
  have hsum : ∀ c : ℕ → ℕ → ℂ, (∀ m n, ‖c m n‖ ≤ (Ma + Mb) * δ ^ 2 * ((1 / 2 : ℝ) ^ m * (1 / 2 : ℝ) ^ n)) →
      ∀ z w : ℂ, ‖z‖ ≤ 1 → ‖w‖ ≤ 1 → Summable fun q : ℕ × ℕ => c q.1 q.2 * z ^ q.1 * w ^ q.2 :=
    fun c hc z w hz hw => Summable.of_norm_bounded hG.summable (hterm c hc z w hz hw)
  have hnD : ∀ z ∈ unitDisc, ‖z‖ ≤ 1 := fun z hz => (mem_ball_zero_iff.mp hz).le
  -- off the axes and the diagonal, the divided series agree
  have h0 : ∀ z ∈ unitDisc, ∀ w ∈ unitDisc, z ≠ 0 → w ≠ 0 → z ≠ w →
      (∑' q : ℕ × ℕ, α q.1 q.2 * z ^ q.1 * w ^ q.2) = ∑' q : ℕ × ℕ, β q.1 q.2 * z ^ q.1 * w ^ q.2 := by
    intro z hz w hw hz0 hw0 hzw
    have hρD : ∀ x ∈ unitDisc, ((1 / 2 * δ : ℝ) : ℂ) * x ∈ unitDisc := by
      intro x hx
      rw [unitDisc, mem_ball_zero_iff, norm_mul, Complex.norm_of_nonneg hρ0.le]
      have := mem_ball_zero_iff.mp hx
      nlinarith [norm_nonneg x]
    obtain ⟨S, S', hS, hS', he⟩ := h _ (hρD z hz) _ (hρD w hw) (mul_ne_zero hρ hz0) (mul_ne_zero hρ hw0)
      (fun h' => hzw (mul_left_cancel₀ hρ h'))
    have hGa := (hsum α hαb z w (hnD z hz) (hnD w hw)).hasSum
    have hGb := (hsum β hβb z w (hnD z hz) (hnD w hw)).hasSum
    have eS : S = z * w * ∑' q : ℕ × ℕ, α q.1 q.2 * z ^ q.1 * w ^ q.2 := by
      refine hS.unique ((hGa.mul_left (z * w)).congr_fun fun q => ?_)
      rw [hα]; ring
    have eS' : S' = z * w * ∑' q : ℕ × ℕ, β q.1 q.2 * z ^ q.1 * w ^ q.2 := by
      refine hS'.unique ((hGb.mul_left (z * w)).congr_fun fun q => ?_)
      rw [hβ]; ring
    have hb1 : ∀ T : ℂ, ‖T‖ ≤ (Ma + Mb) * δ ^ 2 * (2 * 2) → ‖z * w * T‖ ≤ 1 := by
      intro T hT
      rw [norm_mul, norm_mul]
      have := hnD z hz
      have := hnD w hw
      calc ‖z‖ * ‖w‖ * ‖T‖ ≤ 1 * 1 * ((Ma + Mb) * δ ^ 2 * (2 * 2)) := by gcongr
        _ ≤ 1 := by nlinarith
    have hSn : ‖S‖ ≤ 1 := by
      rw [eS]; exact hb1 _ (hGa.norm_le_of_bounded hG (hterm α hαb z w (hnD z hz) (hnD w hw)))
    have hSn' : ‖S'‖ ≤ 1 := by
      rw [eS']; exact hb1 _ (hGb.norm_le_of_bounded hG (hterm β hβb z w (hnD z hz) (hnD w hw)))
    obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp he
    have hnorm : ‖(n : ℂ) * (2 * π * I)‖ ≤ 2 := by
      rw [show (n : ℂ) * (2 * π * I) = S' - S by linear_combination -hn]
      exact (norm_sub_le _ _).trans (by linarith)
    have hn0 : n = 0 := by
      by_contra hne
      have h1 : (1 : ℝ) ≤ |(n : ℝ)| := by exact_mod_cast Int.one_le_abs hne
      simp [abs_of_pos Real.pi_pos] at hnorm
      nlinarith [Real.pi_gt_three]
    rw [hn0, Int.cast_zero, zero_mul, add_zero, neg_inj] at hn
    rw [hn, eS'] at eS
    exact (mul_left_cancel₀ (mul_ne_zero hz0 hw0) eS).symm
  -- fill in `z ∈ {0, w}` (continuity in `z`), then `w = 0` (continuity in `w`)
  have hcz : ∀ c : ℕ → ℕ → ℂ, (∀ m n, ‖c m n‖ ≤ (Ma + Mb) * δ ^ 2 * ((1 / 2 : ℝ) ^ m * (1 / 2 : ℝ) ^ n)) →
      ∀ w ∈ unitDisc, ContinuousOn (fun z => ∑' q : ℕ × ℕ, c q.1 q.2 * z ^ q.1 * w ^ q.2) unitDisc :=
    fun c hc w hw => continuousOn_tsum (fun q => by fun_prop) hG.summable
      (fun q z hz => hterm c hc z w (hnD z hz) (hnD w hw) q)
  have hcw : ∀ c : ℕ → ℕ → ℂ, (∀ m n, ‖c m n‖ ≤ (Ma + Mb) * δ ^ 2 * ((1 / 2 : ℝ) ^ m * (1 / 2 : ℝ) ^ n)) →
      ∀ z ∈ unitDisc, ContinuousOn (fun w => ∑' q : ℕ × ℕ, c q.1 q.2 * z ^ q.1 * w ^ q.2) unitDisc :=
    fun c hc z hz => continuousOn_tsum (fun q => by fun_prop) hG.summable
      (fun q w hw => hterm c hc z w (hnD z hz) (hnD w hw) q)
  have h1 : ∀ w ∈ unitDisc, w ≠ 0 → ∀ z ∈ unitDisc,
      (∑' q : ℕ × ℕ, α q.1 q.2 * z ^ q.1 * w ^ q.2) = ∑' q : ℕ × ℕ, β q.1 q.2 * z ^ q.1 * w ^ q.2 :=
    fun w hw hw0 => s5r58_eq_of_punct hDo (hcz α hαb w hw) (hcz β hβb w hw)
      (fun z hz hz0 hzw => h0 z hz w hw hz0 hw0 hzw)
  have h2 : ∀ z ∈ unitDisc, ∀ w ∈ unitDisc,
      (∑' q : ℕ × ℕ, α q.1 q.2 * z ^ q.1 * w ^ q.2) = ∑' q : ℕ × ℕ, β q.1 q.2 * z ^ q.1 * w ^ q.2 :=
    fun z hz => s5r58_eq_of_punct (p₁ := 0) (p₂ := 0) hDo (hcw α hαb z hz) (hcw β hβb z hz)
      (fun w hw hw0 _ => h1 w hw hw0 z hz)
  have hαβ : α = β := double_powerSeries_coeff_unique
    (F := fun z w => ∑' q : ℕ × ℕ, α q.1 q.2 * z ^ q.1 * w ^ q.2)
    (fun z hz w hw => (hsum α hαb z w (hnD z hz) (hnD w hw)).hasSum)
    (fun z hz w hw => by rw [h2 z hz w hw]; exact (hsum β hβb z w (hnD z hz) (hnD w hw)).hasSum)
  funext m n
  have e := congrFun (congrFun hαβ m) n
  simp only [hα, hβ] at e
  exact mul_right_cancel₀ (pow_ne_zero _ hρ) (mul_right_cancel₀ (pow_ne_zero _ hρ) e)

/-- Model B through any normalized solution: for a normalized plane solution `W` of `extB μ`, `f^μ` is a Möbius
image of `W` on `𝔻` (the construction of `exists_isNormalizedB`, then uniqueness `wB_spec`). -/
theorem s5r58_fB_mobius {μ : LinfStar} (hμ : μ ∈ LinfStarBall) {W : ℂ → ℂ}
    (hW : IsNormalizedSolution W (extB μ)) :
    ∃ γ : ℂ, ∀ z ∈ unitDisc, γ * W z + 1 ≠ 0 ∧ fB μ z = mobiusFn (deriv W 0)⁻¹ 0 γ 1 (W z) := by
  obtain ⟨K, hK⟩ := hW.1
  have hWi : Function.Injective W :=
    fun _ _ he => hK.2.2.1.2.1 (mem_univ _) (mem_univ _) he
  have hz0 : (0 : ℂ) ∈ unitDisc := mem_ball_self one_pos
  have hW0 : W 0 = 0 := hW.2.2.1
  have hd : deriv W 0 ≠ 0 :=
    deriv_ne_zero_of_injOn Metric.isOpen_ball (extB_solution_holomorphic hW) hWi.injOn hz0
  have hWa : AnalyticAt ℂ W 0 :=
    (extB_solution_holomorphic hW).analyticAt (Metric.isOpen_ball.mem_nhds hz0)
  have hpD : ∀ z : ℂ, ‖z‖ < 1 → Function.invFun (wAS μ) extInf ≠ (z : ExtPlane) :=
    fun z hz => wAS_pole_notin_disc hμ hz
  obtain ⟨hpole, hden⟩ := modelB_pole_data hWi hW0 hpD (deriv W 0)⁻¹
  obtain ⟨γ, hγ⟩ : ∃ γ : ℂ, γ = -(finPart (OnePoint.map W (Function.invFun (wAS μ) extInf)))⁻¹ :=
    ⟨_, rfl⟩
  rw [← hγ] at hpole hden
  have hden0 : γ * W 0 + 1 ≠ 0 := hden 0 (by simp)
  have hcomp := (hasDerivAt_mobius (a := (deriv W 0)⁻¹) (b := 0) hden0).comp (0 : ℂ)
    hWa.differentiableAt.hasDerivAt
  have hw : IsNormalizedB μ (mobiusExt (deriv W 0)⁻¹ 0 γ 1 ∘ OnePoint.map W) := by
    refine ⟨mobiusExt (deriv W 0)⁻¹ 0 γ 1,
      ⟨(deriv W 0)⁻¹, 0, γ, 1, by simpa using inv_ne_zero hd, rfl⟩, W, hW, fun z => rfl, rfl,
      mobiusFn (deriv W 0)⁻¹ 0 γ 1 ∘ W, ?_, ?_, ?_, ?_⟩
    · intro z hz
      show mobiusExt (deriv W 0)⁻¹ 0 γ 1 ((W z : ℂ) : ExtPlane) = _
      rw [mobiusExt_coe (by simpa using hden z (mem_ball_zero_iff.mp hz))]
      rfl
    · show ((deriv W 0)⁻¹ * W 0 + 0) / (γ * W 0 + 1) = 0
      rw [hW0]
      simp
    · have hd' := hcomp.deriv
      change deriv (mobiusFn (deriv W 0)⁻¹ 0 γ 1 ∘ W) 0 = _ at hd'
      rw [hd', hW0]
      simp
      field_simp
    · show mobiusExt (deriv W 0)⁻¹ 0 γ 1 (OnePoint.map W (Function.invFun (wAS μ) extInf)) = extInf
      exact hpole
  have heq := (wB_spec hμ).2 _ hw
  refine ⟨γ, fun z hz => ⟨hden z (mem_ball_zero_iff.mp hz), ?_⟩⟩
  show finPart (wB μ (z : ExtPlane)) = _
  rw [← heq]
  show finPart (mobiusExt (deriv W 0)⁻¹ 0 γ 1 ((W z : ℂ) : ExtPlane)) = _
  rw [mobiusExt_coe (by simpa using hden z (mem_ball_zero_iff.mp hz))]
  rfl

/-- The mixed representation only sees `1/f` up to an additive constant. -/
theorem s5r58_rep_inv {u₁ u₂ v₁ v₂ z₁ z₂ κ E : ℂ} (hu₁ : u₁ ≠ 0) (hu₂ : u₂ ≠ 0) (hv₁ : v₁ ≠ 0)
    (hv₂ : v₂ ≠ 0) (e₁ : v₁⁻¹ = u₁⁻¹ + κ) (e₂ : v₂⁻¹ = u₂⁻¹ + κ)
    (h : (u₁ - u₂) * z₁ * z₂ = (z₁ - z₂) * u₁ * u₂ * E) :
    (v₁ - v₂) * z₁ * z₂ = (z₁ - z₂) * v₁ * v₂ * E := by
  have k : (v₁ - v₂) / (v₂ * v₁) = (u₁ - u₂) / (u₂ * u₁) := by
    rw [← inv_sub_inv hv₂ hv₁, ← inv_sub_inv hu₂ hu₁, e₁, e₂]
    ring
  have hv : v₁ - v₂ = v₂ * v₁ * ((u₁ - u₂) / (u₂ * u₁)) := by
    rw [← k]
    field_simp
  rw [hv]
  calc v₂ * v₁ * ((u₁ - u₂) / (u₂ * u₁)) * z₁ * z₂ = v₂ * v₁ * ((u₁ - u₂) * z₁ * z₂) / (u₂ * u₁) := by ring
    _ = v₂ * v₁ * ((z₁ - z₂) * u₁ * u₂ * E) / (u₂ * u₁) := by rw [h]
    _ = (z₁ - z₂) * v₁ * v₂ * E * ((u₁ * u₂) / (u₂ * u₁)) := by ring
    _ = (z₁ - z₂) * v₁ * v₂ * E := by rw [mul_comm u₁ u₂, div_self (mul_ne_zero hu₂ hu₁), mul_one]

/-- **Stub Q4.** A univalent normalized `f` with a q.c. extension and mixed Grunsky coefficients `C/√` comes from a
point of `T(1)`: `kyns p = C`. -/
theorem s5r58_kyns_of_ext {C : ℕ → ℕ → ℂ} {f F : ℂ → ℂ}
    (hfd : DifferentiableOn ℂ f unitDisc) (hfi : InjOn f unitDisc) (hf0 : f 0 = 0) (hf1 : deriv f 0 = 1)
    (hrep : ∀ z₁ ∈ unitDisc, ∀ z₂ ∈ unitDisc, z₁ ≠ 0 → z₂ ≠ 0 → z₁ ≠ z₂ → ∃ S,
      HasSum (fun q : ℕ × ℕ => C q.1 q.2 / Real.sqrt ((q.1 + 1) * (q.2 + 1)) * z₁ ^ (q.1 + 1) * z₂ ^ (q.2 + 1)) S ∧
      (f z₁ - f z₂) * z₁ * z₂ = (z₁ - z₂) * f z₁ * f z₂ * exp (-S))
    (hF : IsQuasiconformal F univ) (hFs : F '' univ = univ) (hFf : EqOn F f unitDisc) :
    ∃ p : T1, kyns p = C := by
  obtain ⟨K, hK⟩ := hF
  have hDo : IsOpen unitDisc := Metric.isOpen_ball
  have h0D : (0 : ℂ) ∈ unitDisc := mem_ball_self one_pos
  have hmeasE : MeasurableSet unitDiscExterior := (isOpen_lt continuous_const continuous_norm).measurableSet
  have hFinj : Function.Injective F := fun _ _ he => hK.2.2.1.2.1 (mem_univ _) (mem_univ _) he
  have hF0 : F 0 = 0 := (hFf h0D).trans hf0
  have hF1 : F 1 ≠ 0 := fun h => one_ne_zero (hFinj (h.trans hF0.symm))
  -- (a) `μ = μ_F|𝔻*`, with `‖μ‖∞ ≤ (K-1)/(K+1) < 1` from the `K`-q.c. bound
  have hK1 : (1 : ℝ) ≤ K := hK.2.1
  have hk1 : (K - 1) / (K + 1) < 1 := by rw [div_lt_one (by linarith)]; linarith
  have hk0 : 0 ≤ (K - 1) / (K + 1) := div_nonneg (by linarith) (by linarith)
  have hbd : ∀ᵐ z ∂(volume.restrict unitDiscExterior), ‖complexDilatation F z‖ ≤ (K - 1) / (K + 1) := by
    have h := (isKQC_maxDilatation_le hK).2
    rw [Measure.restrict_univ] at h
    exact ae_restrict_of_ae h
  have hmem : MemLp (complexDilatation F) ∞ (volume.restrict unitDiscExterior) :=
    memLp_top_of_bound ((measurable_dzbar _).div (measurable_dz _)).aestronglyMeasurable _ hbd
  obtain ⟨μ, hμdef⟩ : ∃ μ : LinfStar, μ = toLinf (complexDilatation F) := ⟨_, rfl⟩
  have hμ : μ ∈ LinfStarBall := by
    have h := (norm_toLinf_le_of_ae_bound hk0 hbd).trans_lt hk1
    rw [← hμdef] at h
    simpa [LinfStarBall] using h
  have hμae : (μ : ℂ → ℂ) =ᵐ[volume.restrict unitDiscExterior] complexDilatation F := by
    have h : toLinf (complexDilatation F) = hmem.toLp _ := dif_pos hmem
    rw [hμdef, h]
    exact hmem.coeFn_toLp
  -- (b) `W = F/F(1)` is the normalized solution of `extB μ` (`μ_F = 0` on `𝔻`, `S¹` null)
  obtain ⟨W, hWdef⟩ : ∃ W : ℂ → ℂ, W = fun ζ => (F ζ - 0) / F 1 := ⟨_, rfl⟩
  have hW : IsNormalizedSolution W (extB μ) := by
    obtain ⟨hWK, hWs⟩ := bB_l_affine_isKQC hK hFs 0 hF1
    rw [hWdef]
    refine ⟨⟨K, hWK⟩, hWs, by simp [hF0], by simp [hF1], ?_⟩
    have hsph : ∀ᵐ z ∂(volume : Measure ℂ), z ∈ (Metric.sphere (0 : ℂ) 1)ᶜ :=
      compl_mem_ae_iff.mpr (Measure.addHaar_sphere _ _ _)
    have hE := (ae_restrict_iff' hmeasE).mp hμae
    filter_upwards [hsph, hE] with z hz1 hz2
    rw [nxE_complexDilatation_affine hF1 z]
    show complexDilatation F z = unitDiscExterior.indicator (μ : ℂ → ℂ) z
    by_cases hzE : z ∈ unitDiscExterior
    · rw [Set.indicator_of_mem hzE]; exact (hz2 hzE).symm
    · rw [Set.indicator_of_notMem hzE]
      have hlt : ¬ 1 < ‖z‖ := hzE
      have hne : ‖z‖ ≠ 1 := fun h => hz1 (mem_sphere_zero_iff_norm.mpr h)
      have hzD : z ∈ unitDisc := mem_ball_zero_iff.mpr (lt_of_le_of_ne (not_lt.mp hlt) hne)
      have hev : F =ᶠ[𝓝 z] f := Filter.eventuallyEq_of_mem (hDo.mem_nhds hzD) hFf
      exact complexDilatation_eq_zero_of_diffAt
        (((hfd z hzD).differentiableAt (hDo.mem_nhds hzD)).congr_of_eventuallyEq hev)
  obtain ⟨γ, hγ⟩ := s5r58_fB_mobius hμ hW
  have hWz : ∀ z ∈ unitDisc, W z = f z / F 1 := fun z hz => by
    rw [hWdef]; simp only [hFf hz, sub_zero]
  have hWd : deriv W 0 = 1 / F 1 := by
    have hev : W =ᶠ[𝓝 0] fun ζ => f ζ / F 1 := Filter.eventuallyEq_of_mem (hDo.mem_nhds h0D) hWz
    rw [hev.deriv_eq, deriv_div_const, hf1]
  -- `𝖿 = λ_c ∘ f^μ` and `f^μ = λ_{γ/F(1)} ∘ f` on `𝔻`: `1/𝖿 = 1/f + κ` (the normalizations differ)
  have hpair := AppB.b8_welding_normalized_pair hμ
  obtain ⟨-, hgi, hg0, -, -, -⟩ := id hpair
  have hb := (grunsky_spec hpair).1
  have hinv : ∀ z ∈ unitDisc, z ≠ 0 →
      fsans μ z ≠ 0 ∧ f z ≠ 0 ∧ (fsans μ z)⁻¹ = (f z)⁻¹ + (weldConst μ + γ / F 1) := by
    intro z hz hz0
    have hfz : f z ≠ 0 := fun h => hz0 (hfi hz h0D (h.trans hf0.symm))
    have hsz : fsans μ z ≠ 0 := fun h => hz0 (hgi hz h0D (h.trans hg0.symm))
    have hfs : fsans μ z = fB μ z / (weldConst μ * fB μ z + 1) := rfl
    have hfBz : fB μ z ≠ 0 := by intro h; apply hsz; rw [hfs, h, zero_div]
    have hfB' : fB μ z = f z / (γ * (f z / F 1) + 1) := by
      rw [(hγ z hz).2, hWz z hz, hWd]
      show ((1 / F 1)⁻¹ * (f z / F 1) + 0) / (γ * (f z / F 1) + 1) = _
      congr 1
      rw [add_zero]
      field_simp
    refine ⟨hsz, hfz, ?_⟩
    rw [hfs, inv_div, add_div, mul_div_assoc, div_self hfBz, mul_one, hfB', one_div_div]
    field_simp
    ring
  -- (c)+(d) the two mixed representations of `𝖿` have the same coefficients
  have hab := s5r58_coeff_unique (a := fun m n : ℕ => C m n / (Real.sqrt ((m + 1) * (n + 1)) : ℂ))
    (b := fun m n : ℕ => grunsky (fsans μ) (gsans μ) (-(m + 1 : ℤ)) (-(n + 1 : ℤ))) (by
      intro z₁ hz₁ z₂ hz₂ h1 h2 h12
      obtain ⟨S, hS, hSe⟩ := hrep z₁ hz₁ z₂ hz₂ h1 h2 h12
      obtain ⟨M, hM, hMe⟩ := s5r58_mixed_rep hb hg0 z₁ hz₁ z₂ hz₂ h1 h2 h12
      refine ⟨S, M, hS, hM, ?_⟩
      obtain ⟨hs1, hf1', e1⟩ := hinv z₁ hz₁ h1
      obtain ⟨hs2, hf2', e2⟩ := hinv z₂ hz₂ h2
      have hT := s5r58_rep_inv hf1' hf2' hs1 hs2 e1 e2 hSe
      exact mul_left_cancel₀ (mul_ne_zero (mul_ne_zero (sub_ne_zero.mpr h12) hs1) hs2) (hT.symm.trans hMe))
  -- (e) `p = [μ]`
  refine ⟨Phi ⟨μ, hμ⟩, ?_⟩
  rw [s5c_kyns_eq]
  have hcl : grunsky (fsans (Quotient.out (Phi ⟨μ, hμ⟩) : LinfStarBall))
      (gsans (Quotient.out (Phi ⟨μ, hμ⟩) : LinfStarBall)) = grunsky (fsans μ) (gsans μ) := by
    apply FB.fb_grunsky_class (Quotient.out (Phi ⟨μ, hμ⟩)).2 hμ
    exact Quotient.exact (Quotient.out_eq (Phi ⟨μ, hμ⟩))
  show B1 (grunsky (fsans (Quotient.out (Phi ⟨μ, hμ⟩) : LinfStarBall))
    (gsans (Quotient.out (Phi ⟨μ, hμ⟩) : LinfStarBall))) = C
  rw [hcl]
  funext m n
  have e := (s5r58_B1_div (grunsky (fsans μ) (gsans μ)) m n).trans (congrFun (congrFun hab m) n).symm
  have hs : (Real.sqrt ((m + 1) * (n + 1)) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_ne_zero'.mpr (by positivity))
  exact (div_left_inj' hs).mp e

/-- **Remark 5.8** (assembled). -/
theorem s5r58_remark_5_8 {C : ℕ → ℕ → ℂ} (hC : C ∈ siegelDisk0) :
    C ∈ kyns '' T01 ↔
      (∀ z₁ ∈ unitDisc, ∀ z₂ ∈ unitDisc, z₁ ≠ 0 → z₂ ≠ 0 → z₁ ≠ z₂ →
        1 + ∑' m : ℕ, C m 0 / Real.sqrt (m + 1) * ((z₁ ^ (m + 1) - z₂ ^ (m + 1)) / (z₁⁻¹ - z₂⁻¹)) =
          exp (-∑' q : ℕ × ℕ, C q.1 q.2 / Real.sqrt ((q.1 + 1) * (q.2 + 1)) * z₁ ^ (q.1 + 1) * z₂ ^ (q.2 + 1))) ∧
        ∃ D ∈ siegelDisk0, ∃ B : ℕ → ℕ → ℂ, IsBoundedMat B ∧
          (∀ m n, kron m n - (∑' k, C m k * conj (C k n)) = mulAdj B B m n) ∧
          (∀ m n, kron m n - (∑' k, D m k * conj (D k n)) = ∑' k, B k m * conj (B k n)) ∧
          ∀ z₁ ∈ unitDiscExterior, ∀ z₂ ∈ unitDiscExterior, z₁ ≠ z₂ →
            1 + ∑' m : ℕ, D m 0 / Real.sqrt (m + 1) * ((z₁ ^ (-(m + 1 : ℤ)) - z₂ ^ (-(m + 1 : ℤ))) / (z₁ - z₂)) =
              exp (-∑' q : ℕ × ℕ,
                D q.1 q.2 / Real.sqrt ((q.1 + 1) * (q.2 + 1)) * z₁ ^ (-(q.1 + 1 : ℤ)) * z₂ ^ (-(q.2 + 1 : ℤ))) := by
  constructor
  · rintro ⟨p, hp, rfl⟩
    have hμ : ((Quotient.out p : LinfStarBall) : LinfStar) ∈ LinfStarBall := (Quotient.out p : LinfStarBall).2
    have hpe : Phi ⟨_, hμ⟩ = p := Quotient.out_eq p
    have hk : kyns p = B1 (grunsky (fsans ((Quotient.out p : LinfStarBall) : LinfStar))
        (gsans ((Quotient.out p : LinfStarBall) : LinfStar))) := s5c_kyns_eq p
    obtain ⟨hD, hB, h2a, h2b⟩ := s5r58_S2 hμ (by rw [hpe]; exact hp)
    rw [hk]
    exact ⟨s5r58_S1 hμ, _, hD, _, hB, h2a, h2b, s5r58_S3 hμ⟩
  · rintro ⟨hS1, -⟩
    obtain ⟨f, hfd, hfi, hf0, hf1, hrep⟩ := s5r58_f_of_S1 hC hS1
    obtain ⟨c, hc, F, hF, hFs, hFf⟩ := s5r58_qc_ext hC hfd hfi hf0 hf1 hrep
    obtain ⟨hgd, hgi, hg0, hg1, hgrep⟩ := s5r58_renorm hfd hfi hf0 hf1 hrep hc
    obtain ⟨p, hp⟩ := s5r58_kyns_of_ext hgd hgi hg0 hg1 hgrep hF hFs hFf
    exact ⟨p, (s5c_cor_5_4 p).1 (hp ▸ hC), hp⟩

/-- **Remark 5.8** (TT:5702–5750, [Teo03]): the Schottky locus `Π₀(T₀(1)) ⊂ 𝔇_∞⁰`. `C ∈ 𝔇_∞⁰` lies in it iff the
following hold.
- S1 (on `𝔻`): `1 + Σ_m C_{m1}/√m (z₁^m - z₂^m)/(z₁⁻¹ - z₂⁻¹) = exp(-Σ_{m,n} C_{mn}/√(mn) z₁^m z₂^n)`.
- S2: there are `D ∈ 𝔇_∞⁰` and a bounded `B` with `I - CC̄ = BB*` and `I - DD̄ = B̄*B̄`.
- S3 (on `𝔻*`): `1 + Σ_m D_{m1}/√m (z₁^{-m} - z₂^{-m})/(z₁ - z₂) = exp(-Σ_{m,n} D_{mn}/√(mn) z₁^{-m} z₂^{-n})`.

S1 and S3 are the dispersionless Hirota equations. -/
theorem remark_5_8 {C : ℕ → ℕ → ℂ} (hC : C ∈ siegelDisk0) :
    C ∈ kyns '' T01 ↔
      (∀ z₁ ∈ unitDisc, ∀ z₂ ∈ unitDisc, z₁ ≠ 0 → z₂ ≠ 0 → z₁ ≠ z₂ →
        1 + ∑' m : ℕ, C m 0 / Real.sqrt (m + 1) * ((z₁ ^ (m + 1) - z₂ ^ (m + 1)) / (z₁⁻¹ - z₂⁻¹)) =
          exp (-∑' q : ℕ × ℕ, C q.1 q.2 / Real.sqrt ((q.1 + 1) * (q.2 + 1)) * z₁ ^ (q.1 + 1) * z₂ ^ (q.2 + 1))) ∧
        ∃ D ∈ siegelDisk0, ∃ B : ℕ → ℕ → ℂ, IsBoundedMat B ∧
          (∀ m n, kron m n - (∑' k, C m k * conj (C k n)) = mulAdj B B m n) ∧
          (∀ m n, kron m n - (∑' k, D m k * conj (D k n)) = ∑' k, B k m * conj (B k n)) ∧
          ∀ z₁ ∈ unitDiscExterior, ∀ z₂ ∈ unitDiscExterior, z₁ ≠ z₂ →
            1 + ∑' m : ℕ, D m 0 / Real.sqrt (m + 1) * ((z₁ ^ (-(m + 1 : ℤ)) - z₂ ^ (-(m + 1 : ℤ))) / (z₁ - z₂)) =
              exp (-∑' q : ℕ × ℕ,
                D q.1 q.2 / Real.sqrt ((q.1 + 1) * (q.2 + 1)) * z₁ ^ (-(q.1 + 1 : ℤ)) * z₂ ^ (-(q.2 + 1 : ℤ))) := by
  exact s5r58_remark_5_8 hC

end Ch2

end TakhtajanTeo
