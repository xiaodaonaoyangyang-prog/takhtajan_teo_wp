import TakhtajanTeo.Ch1.Eq124General

/-!
# Chapter 1, §6 — (6.4), its regularization, Proposition 6.3 (`e64_`, 下属2 + 下属1)

`e64_eq_6_4`, `e64_eq_6_4_regular`, `e64_prop_6_3` are byte-identical copies of `eq_6_4`, `eq_6_4_regular`,
`prop_6_3` (S6; relocated by the leader).

**Route (holomorphic two-parameter extension).** `h(ε) = ∂_ε̄ ρ^{εμ}(z) = (4/π) PV_v μ̄(v) K_ε(z, v̄) K_ε(v̄, z̄)`
(`eq_6_1`, `eq_1_25`). Replace `(ε, ε̄)` by an independent pair `P = (P₁, P₂)`: with
`W_P = w^{P₁ m₁ + P₂ m₂}` (`m₁ = μ` on `𝕌`, `m₂ = μ̄∘conj` on `𝕃`), the integrand `Φ(P)(v)` below is holomorphic
in `P` (Ahlfors–Bers, `wr_ns2_diffAt`) and equals the `ε`-integrand on the diagonal `P = (ε, ε̄)` (`e64_phi_diag`).
Cauchy's formula on a torus (`wr_cauchy_bidisc`) then gives `∂_ε` at `0` as a torus integral of **values**
(`e64_torus_dz`), so the `ε`-derivative of the principal value needs only
* an `L¹` bound for `Φ(q)` on `𝕌 ∖ B(z, δ)`, uniform in `q` (`e64_tail_bound`, change of variables `ζ = W_q(v̄)`),
* uniform convergence in `q` of the truncated integrals (`e64_param_pv`, the anisotropic diagonal control).

No pointwise bound on `∂_ε` of `(w_ε)_z` near `∂𝕌` is needed: `w_ε` is only quasiconformal across `ℝ`, and the tree
has no such bound.
-/

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal ComplexConjugate Classical Real
noncomputable section
namespace TakhtajanTeo
open LiZhongQC

/-! ### Torus calculus (abstract) -/

/-- Continuity of `a ↦ ∮_b H(a, b)` on the circle, for `H` continuous on the torus. -/
theorem e64_circ_param_cont {H : ℂ × ℂ → ℂ} {r : ℝ} (hr : 0 < r)
    (hH : ContinuousOn H (sphere (0 : ℂ) r ×ˢ sphere (0 : ℂ) r)) :
    ContinuousOn (fun a => ∮ b in C(0, r), H (a, b)) (sphere (0 : ℂ) r) := by
  have h := wr_param_circ_cont (S := sphere (0 : ℂ) r) (h := fun a b => H (a, b)) hr
    (hH.congr fun p _ => rfl) 0
  have hm : MapsTo (fun a : ℂ => (a, (0 : ℂ))) (sphere (0 : ℂ) r) (sphere (0 : ℂ) r ×ˢ ball (0 : ℂ) r) :=
    fun a ha => ⟨ha, mem_ball_self hr⟩
  refine (h.comp (continuous_id.prodMk continuous_const).continuousOn hm).congr fun a _ => ?_
  simp only [Function.comp_apply, zpow_zero, one_smul]
  rfl

/-- The double circle integral is additive on functions continuous on the torus. -/
theorem e64_torus_add {H₁ H₂ : ℂ → ℂ → ℂ} {r : ℝ} (hr : 0 < r)
    (h₁ : ContinuousOn (fun q : ℂ × ℂ => H₁ q.1 q.2) (sphere (0 : ℂ) r ×ˢ sphere (0 : ℂ) r))
    (h₂ : ContinuousOn (fun q : ℂ × ℂ => H₂ q.1 q.2) (sphere (0 : ℂ) r ×ˢ sphere (0 : ℂ) r)) :
    (∮ a in C(0, r), ∮ b in C(0, r), (H₁ a b + H₂ a b)) =
      (∮ a in C(0, r), ∮ b in C(0, r), H₁ a b) + ∮ a in C(0, r), ∮ b in C(0, r), H₂ a b := by
  have hin : ∀ {H : ℂ → ℂ → ℂ}, ContinuousOn (fun q : ℂ × ℂ => H q.1 q.2) (sphere (0 : ℂ) r ×ˢ sphere (0 : ℂ) r) →
      ∀ a ∈ sphere (0 : ℂ) r, CircleIntegrable (fun b => H a b) 0 r := by
    intro H hH a ha
    refine ContinuousOn.circleIntegrable hr.le ?_
    exact hH.comp (continuous_const.prodMk continuous_id).continuousOn fun b hb => ⟨ha, hb⟩
  have hc : EqOn (fun a => ∮ b in C(0, r), (H₁ a b + H₂ a b))
      (fun a => (∮ b in C(0, r), H₁ a b) + ∮ b in C(0, r), H₂ a b) (sphere (0 : ℂ) r) :=
    fun a ha => circleIntegral.integral_add (hin h₁ a ha) (hin h₂ a ha)
  rw [circleIntegral.integral_congr hr.le hc]
  exact circleIntegral.integral_add ((e64_circ_param_cont (H := fun q => H₁ q.1 q.2) hr h₁).circleIntegrable hr.le)
    ((e64_circ_param_cont (H := fun q => H₂ q.1 q.2) hr h₂).circleIntegrable hr.le)

/-- Constants pull out of the double circle integral. -/
theorem e64_torus_const_mul (H : ℂ → ℂ → ℂ) (c : ℂ) (r : ℝ) :
    (∮ a in C(0, r), ∮ b in C(0, r), c * H a b) = c * ∮ a in C(0, r), ∮ b in C(0, r), H a b := by
  have e : (fun a => ∮ b in C(0, r), c * H a b) = fun a => c • ∮ b in C(0, r), H a b := by
    funext a
    rw [← circleIntegral.integral_smul]
    rfl
  rw [e, circleIntegral.integral_smul]
  rfl

/-- Pointwise congruence on the torus. -/
theorem e64_torus_congr {H₁ H₂ : ℂ → ℂ → ℂ} {r : ℝ} (hr : 0 < r)
    (h : ∀ a ∈ sphere (0 : ℂ) r, ∀ b ∈ sphere (0 : ℂ) r, H₁ a b = H₂ a b) :
    (∮ a in C(0, r), ∮ b in C(0, r), H₁ a b) = ∮ a in C(0, r), ∮ b in C(0, r), H₂ a b :=
  circleIntegral.integral_congr hr.le fun a ha =>
    circleIntegral.integral_congr hr.le fun b hb => h a ha b hb

/-- Norm bound for the double circle integral. -/
theorem e64_torus_norm_le {H : ℂ → ℂ → ℂ} {r C : ℝ} (hr : 0 < r)
    (h : ∀ a ∈ sphere (0 : ℂ) r, ∀ b ∈ sphere (0 : ℂ) r, ‖H a b‖ ≤ C) :
    ‖∮ a in C(0, r), ∮ b in C(0, r), H a b‖ ≤ 2 * π * r * (2 * π * r * C) :=
  circleIntegral.norm_integral_le_of_norm_le_const hr.le fun a ha =>
    circleIntegral.norm_integral_le_of_norm_le_const hr.le fun b hb => h a ha b hb

/-- The second-order remainder of the Cauchy kernel: for `|a| = |b| = r` and `‖ε‖ ≤ r/2`,
`|1/((a-ε)(b-ε̄)) - 1/(ab) - ε/(a²b) - ε̄/(ab²)| ≤ 24 ‖ε‖²/r⁴`. -/
theorem e64_kernel_rem {a b ε : ℂ} {r : ℝ} (hr : 0 < r) (ha : ‖a‖ = r) (hb : ‖b‖ = r) (hε : ‖ε‖ ≤ r / 2) :
    ‖1 / ((a - ε) * (b - conj ε)) - 1 / (a * b) - ε / (a ^ 2 * b) - conj ε / (a * b ^ 2)‖ ≤
      24 * ‖ε‖ ^ 2 / r ^ 4 := by
  have ha0 : a ≠ 0 := by rintro rfl; rw [norm_zero] at ha; linarith
  have hb0 : b ≠ 0 := by rintro rfl; rw [norm_zero] at hb; linarith
  set x : ℂ := ε / a with hx
  set y : ℂ := conj ε / b with hy
  have hxn : ‖x‖ = ‖ε‖ / r := by rw [hx, norm_div, ha]
  have hyn : ‖y‖ = ‖ε‖ / r := by rw [hy, norm_div, RCLike.norm_conj, hb]
  have hx2 : ‖x‖ ≤ 1 / 2 := by rw [hxn, div_le_iff₀ hr]; linarith
  have hy2 : ‖y‖ ≤ 1 / 2 := by rw [hyn, div_le_iff₀ hr]; linarith
  have h1x : 1 / 2 ≤ ‖1 - x‖ := by
    have := norm_sub_norm_le (1 : ℂ) x
    rw [norm_one] at this
    linarith
  have h1y : 1 / 2 ≤ ‖1 - y‖ := by
    have := norm_sub_norm_le (1 : ℂ) y
    rw [norm_one] at this
    linarith
  have hx1 : 1 - x ≠ 0 := by intro h; rw [h, norm_zero] at h1x; linarith
  have hy1 : 1 - y ≠ 0 := by intro h; rw [h, norm_zero] at h1y; linarith
  have hae : a - ε = a * (1 - x) := by rw [hx]; field_simp
  have hbe : b - conj ε = b * (1 - y) := by rw [hy]; field_simp
  have key : 1 / ((a - ε) * (b - conj ε)) - 1 / (a * b) - ε / (a ^ 2 * b) - conj ε / (a * b ^ 2) =
      1 / (a * b) * (((x + y) ^ 2 - x * y * (1 + x + y)) / ((1 - x) * (1 - y))) := by
    rw [hae, hbe]
    have e1 : ε = a * x := by rw [hx]; field_simp
    have e2 : conj ε = b * y := by rw [hy]; field_simp
    rw [e2, e1]
    field_simp
    ring
  rw [key, norm_mul, norm_div, norm_div, norm_one, norm_mul, ha, hb, norm_mul]
  have hnum : ‖(x + y) ^ 2 - x * y * (1 + x + y)‖ ≤ 6 * (‖ε‖ / r) ^ 2 := by
    have t1 : ‖(x + y) ^ 2‖ ≤ (‖x‖ + ‖y‖) ^ 2 := by
      rw [norm_pow]; exact pow_le_pow_left₀ (norm_nonneg _) (norm_add_le _ _) 2
    have t2 : ‖x * y * (1 + x + y)‖ ≤ ‖x‖ * ‖y‖ * (1 + ‖x‖ + ‖y‖) := by
      rw [norm_mul, norm_mul]
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      calc ‖1 + x + y‖ ≤ ‖1 + x‖ + ‖y‖ := norm_add_le _ _
        _ ≤ ‖(1 : ℂ)‖ + ‖x‖ + ‖y‖ := by gcongr; exact norm_add_le _ _
        _ = 1 + ‖x‖ + ‖y‖ := by rw [norm_one]
    have t3 := norm_sub_le ((x + y) ^ 2) (x * y * (1 + x + y))
    rw [hxn, hyn] at t1 t2
    have hs : 0 ≤ ‖ε‖ / r := by positivity
    have hs2 : ‖ε‖ / r ≤ 1 / 2 := by rw [← hxn]; exact hx2
    nlinarith
  have hden : 1 / 4 ≤ ‖1 - x‖ * ‖1 - y‖ := by nlinarith
  have hr4 : (0 : ℝ) < r * r := by positivity
  calc 1 / (r * r) * (‖(x + y) ^ 2 - x * y * (1 + x + y)‖ / (‖1 - x‖ * ‖1 - y‖))
      ≤ 1 / (r * r) * (6 * (‖ε‖ / r) ^ 2 / (1 / 4)) := by
        gcongr
    _ = 24 * ‖ε‖ ^ 2 / r ^ 4 := by field_simp; ring

/-- **(E1)** If `g(ε) = G̃(ε, ε̄)` near `0`, where `G̃` is the bidisc Cauchy integral of a function `G` continuous on
the torus `|a| = |b| = r`, then `∂_ε g(0)` is the `(1, 0)` Cauchy coefficient. -/
theorem e64_torus_dz {G : ℂ × ℂ → ℂ} {g : ℂ → ℂ} {r : ℝ} (hr : 0 < r)
    (hG : ContinuousOn G (sphere (0 : ℂ) r ×ˢ sphere (0 : ℂ) r))
    (hg : ∀ᶠ ε in 𝓝 (0 : ℂ), g ε = ((2 * π * I)⁻¹) ^ 2 *
      ∮ a in C(0, r), ∮ b in C(0, r), G (a, b) / ((a - ε) * (b - conj ε))) :
    dz g 0 = ((2 * π * I)⁻¹) ^ 2 * ∮ a in C(0, r), ∮ b in C(0, r), G (a, b) / (a ^ 2 * b) := by
  set c : ℂ := ((2 * π * I)⁻¹) ^ 2 with hc
  set A₀ : ℂ := ∮ a in C(0, r), ∮ b in C(0, r), G (a, b) / (a * b) with hA₀
  set A₁ : ℂ := ∮ a in C(0, r), ∮ b in C(0, r), G (a, b) / (a ^ 2 * b) with hA₁
  set A₂ : ℂ := ∮ a in C(0, r), ∮ b in C(0, r), G (a, b) / (a * b ^ 2) with hA₂
  obtain ⟨M, hM⟩ : ∃ M, ∀ q ∈ sphere (0 : ℂ) r ×ˢ sphere (0 : ℂ) r, ‖G q‖ ≤ M := by
    obtain ⟨M, hM⟩ := ((isCompact_sphere 0 r).prod (isCompact_sphere 0 r)).exists_bound_of_continuousOn hG
    exact ⟨M, hM⟩
  have hT : ∀ q ∈ sphere (0 : ℂ) r ×ˢ sphere (0 : ℂ) r, q.1 ≠ 0 ∧ q.2 ≠ 0 := by
    intro q hq
    have h1 : ‖q.1‖ = r := by simpa using hq.1
    have h2 : ‖q.2‖ = r := by simpa using hq.2
    exact ⟨fun h => by rw [h, norm_zero] at h1; linarith, fun h => by rw [h, norm_zero] at h2; linarith⟩
  -- continuity of the pieces on the torus
  have hcK : ∀ (n m : ℕ), ContinuousOn (fun q : ℂ × ℂ => G q / (q.1 ^ n * q.2 ^ m))
      (sphere (0 : ℂ) r ×ˢ sphere (0 : ℂ) r) := fun n m =>
    hG.div ((continuous_fst.pow n).mul (continuous_snd.pow m)).continuousOn fun q hq =>
      mul_ne_zero (pow_ne_zero _ (hT q hq).1) (pow_ne_zero _ (hT q hq).2)
  have hcR : ∀ ε : ℂ, ‖ε‖ ≤ r / 2 → ContinuousOn (fun q : ℂ × ℂ => G q *
      (1 / ((q.1 - ε) * (q.2 - conj ε)) - 1 / (q.1 * q.2) - ε / (q.1 ^ 2 * q.2) - conj ε / (q.1 * q.2 ^ 2)))
      (sphere (0 : ℂ) r ×ˢ sphere (0 : ℂ) r) := by
    intro ε hε
    have hne : ∀ q ∈ sphere (0 : ℂ) r ×ˢ sphere (0 : ℂ) r, (q.1 - ε) * (q.2 - conj ε) ≠ 0 := by
      intro q hq
      have h1 : ‖q.1‖ = r := by simpa using hq.1
      have h2 : ‖q.2‖ = r := by simpa using hq.2
      refine mul_ne_zero (fun h => ?_) (fun h => ?_)
      · rw [sub_eq_zero] at h; rw [h] at h1; linarith
      · rw [sub_eq_zero] at h; rw [h, RCLike.norm_conj] at h2; linarith
    refine hG.mul ?_
    refine (((continuousOn_const.div (((continuous_fst.sub continuous_const).mul
      (continuous_snd.sub continuous_const)).continuousOn) hne).sub
      (continuousOn_const.div (continuous_fst.mul continuous_snd).continuousOn
        fun q hq => mul_ne_zero (hT q hq).1 (hT q hq).2)).sub
      (continuousOn_const.div ((continuous_fst.pow 2).mul continuous_snd).continuousOn
        fun q hq => mul_ne_zero (pow_ne_zero _ (hT q hq).1) (hT q hq).2)).sub
      (continuousOn_const.div (continuous_fst.mul (continuous_snd.pow 2)).continuousOn
        fun q hq => mul_ne_zero (hT q hq).1 (pow_ne_zero _ (hT q hq).2))
  -- the expansion `g ε = c (A₀ + ε A₁ + ε̄ A₂ + ∮∮ G R_ε)`
  have hexp : ∀ ε : ℂ, ‖ε‖ ≤ r / 2 → (∮ a in C(0, r), ∮ b in C(0, r), G (a, b) / ((a - ε) * (b - conj ε))) =
      A₀ + ε * A₁ + conj ε * A₂ + ∮ a in C(0, r), ∮ b in C(0, r), G (a, b) *
        (1 / ((a - ε) * (b - conj ε)) - 1 / (a * b) - ε / (a ^ 2 * b) - conj ε / (a * b ^ 2)) := by
    intro ε hε
    have hp : ∀ a ∈ sphere (0 : ℂ) r, ∀ b ∈ sphere (0 : ℂ) r,
        G (a, b) / ((a - ε) * (b - conj ε)) =
          ((G (a, b) / (a ^ 1 * b ^ 1) + ε * (G (a, b) / (a ^ 2 * b ^ 1))) + conj ε * (G (a, b) / (a ^ 1 * b ^ 2))) +
            G (a, b) * (1 / ((a - ε) * (b - conj ε)) - 1 / (a * b) - ε / (a ^ 2 * b) - conj ε / (a * b ^ 2)) := by
      intro a _ b _
      simp only [pow_one]
      ring
    rw [e64_torus_congr hr hp]
    have c1 := hcK 1 1
    have c2 := (hcK 2 1).const_smul ε
    have c3 := (hcK 1 2).const_smul (conj ε)
    rw [e64_torus_add hr ((c1.add c2).add c3) (hcR ε hε), e64_torus_add hr (c1.add c2) c3,
      e64_torus_add hr c1 c2, e64_torus_const_mul, e64_torus_const_mul]
    simp only [pow_one, hA₀, hA₁, hA₂]
  -- the remainder is `O(‖ε‖²)`
  have hrem : ∀ ε : ℂ, ‖ε‖ ≤ r / 2 → ‖∮ a in C(0, r), ∮ b in C(0, r), G (a, b) *
      (1 / ((a - ε) * (b - conj ε)) - 1 / (a * b) - ε / (a ^ 2 * b) - conj ε / (a * b ^ 2))‖ ≤
        2 * π * r * (2 * π * r * (M * (24 * ‖ε‖ ^ 2 / r ^ 4))) := by
    intro ε hε
    refine e64_torus_norm_le hr fun a ha b hb => ?_
    have h1 : ‖a‖ = r := by simpa using ha
    have h2 : ‖b‖ = r := by simpa using hb
    rw [norm_mul]
    exact mul_le_mul (hM (a, b) ⟨ha, hb⟩) (e64_kernel_rem hr h1 h2 hε) (norm_nonneg _)
      ((norm_nonneg _).trans (hM (a, b) ⟨ha, hb⟩))
  -- the derivative
  set L : ℂ →L[ℝ] ℂ := (c * A₁) • ContinuousLinearMap.id ℝ ℂ + (c * A₂) • Complex.conjCLE.toContinuousLinearMap
    with hL
  have hLapp : ∀ h : ℂ, L h = c * A₁ * h + c * A₂ * conj h := by
    intro h
    simp [hL, smul_eq_mul]
  have hD : HasFDerivAt g L 0 := by
    rw [hasFDerivAt_iff_isLittleO_nhds_zero]
    have hbig : (fun h : ℂ => g (0 + h) - g 0 - L h) =O[𝓝 0] fun h : ℂ => ‖h‖ ^ 2 := by
      refine Asymptotics.IsBigO.of_bound (‖c‖ * (2 * π * r * (2 * π * r * (M * (24 / r ^ 4))))) ?_
      have hball : ∀ᶠ h : ℂ in 𝓝 0, ‖h‖ ≤ r / 2 := by
        filter_upwards [ball_mem_nhds (0 : ℂ) (by positivity : 0 < r / 2)] with h hh
        rw [mem_ball_zero_iff] at hh
        exact hh.le
      filter_upwards [hball, hg, hg.self_of_nhds |> fun _ => hball] with h hh hgh _
      have hg0 : g 0 = c * A₀ := by
        rw [hg.self_of_nhds, hexp 0 (by simp; positivity)]
        simp only [map_zero, zero_mul, add_zero, sub_zero]
        have hz : (∮ a in C(0, r), ∮ b in C(0, r), G (a, b) *
            (1 / (a * b) - 1 / (a * b) - 0 / (a ^ 2 * b) - 0 / (a * b ^ 2))) = 0 := by
          simp [circleIntegral]
        rw [hz, add_zero]
      rw [zero_add, hgh, hg0, hexp h hh, hLapp]
      have e : c * (A₀ + h * A₁ + conj h * A₂ + ∮ a in C(0, r), ∮ b in C(0, r), G (a, b) *
            (1 / ((a - h) * (b - conj h)) - 1 / (a * b) - h / (a ^ 2 * b) - conj h / (a * b ^ 2))) -
          c * A₀ - (c * A₁ * h + c * A₂ * conj h) = c * ∮ a in C(0, r), ∮ b in C(0, r), G (a, b) *
            (1 / ((a - h) * (b - conj h)) - 1 / (a * b) - h / (a ^ 2 * b) - conj h / (a * b ^ 2)) := by ring
      rw [e, norm_mul, Real.norm_of_nonneg (by positivity)]
      calc ‖c‖ * ‖∮ a in C(0, r), ∮ b in C(0, r), G (a, b) *
            (1 / ((a - h) * (b - conj h)) - 1 / (a * b) - h / (a ^ 2 * b) - conj h / (a * b ^ 2))‖
          ≤ ‖c‖ * (2 * π * r * (2 * π * r * (M * (24 * ‖h‖ ^ 2 / r ^ 4)))) :=
            mul_le_mul_of_nonneg_left (hrem h hh) (norm_nonneg _)
        _ = ‖c‖ * (2 * π * r * (2 * π * r * (M * (24 / r ^ 4)))) * ‖h‖ ^ 2 := by ring
    exact hbig.trans_isLittleO (Asymptotics.isLittleO_norm_pow_id one_lt_two)
  have hfd := hD.fderiv
  show (fderiv ℝ g 0 1 - I * fderiv ℝ g 0 I) / 2 = c * A₁
  rw [hfd, hLapp, hLapp]
  simp only [map_one, Complex.conj_I]
  ring_nf
  rw [Complex.I_sq]
  ring

/-- Fubini between one circle integral and a set integral, under a domination uniform on the circle. -/
theorem e64_circ_swap {H : ℂ → ℂ → ℂ} {S : Set ℂ} (hS : MeasurableSet S) {r : ℝ} (hr : 0 < r)
    (hc : ContinuousOn (fun p : ℂ × ℂ => H p.1 p.2) (sphere (0 : ℂ) r ×ˢ S))
    {g : ℂ → ℝ} (hg : IntegrableOn g S) (hb : ∀ a ∈ sphere (0 : ℂ) r, ∀ v ∈ S, ‖H a v‖ ≤ g v) :
    IntegrableOn (fun v => ∮ a in C(0, r), H a v) S ∧
      ∫ v in S, (∮ a in C(0, r), H a v) = ∮ a in C(0, r), ∫ v in S, H a v := by
  set Φ : ℝ × ℂ → ℂ := fun p => deriv (circleMap 0 r) p.1 • H (circleMap 0 r p.1) p.2 with hΦ
  have h2π : (0 : ℝ) ≤ 2 * π := by positivity
  have hcm : ∀ θ : ℝ, circleMap 0 r θ ∈ sphere (0 : ℂ) r := fun θ => circleMap_mem_sphere 0 hr.le θ
  have hΦc : ContinuousOn Φ (univ ×ˢ S) := by
    have hd : Continuous fun p : ℝ × ℂ => deriv (circleMap 0 r) p.1 := by
      simp only [deriv_circleMap]
      exact ((continuous_circleMap 0 r).comp continuous_fst).mul continuous_const
    have hH : ContinuousOn (fun p : ℝ × ℂ => H (circleMap 0 r p.1) p.2) (univ ×ˢ S) :=
      hc.comp (((continuous_circleMap 0 r).comp continuous_fst).prodMk continuous_snd).continuousOn
        fun p hp => ⟨hcm p.1, hp.2⟩
    exact hd.continuousOn.smul hH
  have hΦb : ∀ p ∈ (univ : Set ℝ) ×ˢ S, ‖Φ p‖ ≤ r * g p.2 := by
    intro p hp
    simp only [hΦ, deriv_circleMap, norm_smul, norm_mul, norm_circleMap_zero, norm_I, mul_one, abs_of_pos hr]
    exact mul_le_mul_of_nonneg_left (hb _ (hcm p.1) p.2 hp.2) hr.le
  set ν : Measure ℝ := volume.restrict (Ioc 0 (2 * π)) with hν
  have hprod : ν.prod (volume.restrict S) = (volume.prod volume).restrict (Ioc 0 (2 * π) ×ˢ S) := by
    rw [hν, Measure.prod_restrict]
  have hΦi : Integrable Φ (ν.prod (volume.restrict S)) := by
    have hmaj : Integrable (fun p : ℝ × ℂ => (fun _ : ℝ => r) p.1 * g p.2) (ν.prod (volume.restrict S)) := by
      haveI : IsFiniteMeasure ν := by
        rw [hν]
        exact (isFiniteMeasure_restrict (μ := (volume : Measure ℝ)) (s := Ioc 0 (2 * π))).mpr measure_Ioc_lt_top.ne
      exact (integrable_const (μ := ν) r).mul_prod hg
    refine hmaj.mono' ?_ ?_
    · rw [hprod]
      exact (hΦc.mono (prod_mono (subset_univ _) subset_rfl)).aestronglyMeasurable
        (measurableSet_Ioc.prod hS)
    · rw [hprod]
      filter_upwards [ae_restrict_mem (measurableSet_Ioc.prod hS)] with p hp
      exact hΦb p ⟨mem_univ _, hp.2⟩
  have hswap := integral_integral_swap (f := fun θ v => Φ (θ, v)) hΦi
  have hcirc : ∀ v, (∮ a in C(0, r), H a v) = ∫ θ in Ioc 0 (2 * π), Φ (θ, v) := by
    intro v
    rw [circleIntegral, intervalIntegral.integral_of_le h2π]
  have hcirc2 : (∮ a in C(0, r), ∫ v in S, H a v) = ∫ θ in Ioc 0 (2 * π), ∫ v in S, Φ (θ, v) := by
    rw [circleIntegral, intervalIntegral.integral_of_le h2π]
    refine integral_congr_ae (Eventually.of_forall fun θ => ?_)
    simp only [hΦ]
    rw [integral_smul]
  refine ⟨?_, ?_⟩
  · have hi : Integrable (fun v => ∫ θ, Φ (θ, v) ∂ν) (volume.restrict S) :=
      MeasureTheory.Integrable.integral_prod_right hΦi
    refine hi.congr (Eventually.of_forall fun v => ?_)
    exact (hcirc v).symm
  · rw [hcirc2]
    simp only [hcirc]
    exact hswap.symm

/-- **(E1b)** Fubini between a torus integral and a set integral, under a domination uniform on the torus. -/
theorem e64_torus_swap {F : ℂ × ℂ → ℂ → ℂ} {S : Set ℂ} (hS : MeasurableSet S) {r : ℝ} (hr : 0 < r)
    {K : ℂ × ℂ → ℂ} (hK : ContinuousOn K (sphere (0 : ℂ) r ×ˢ sphere (0 : ℂ) r))
    (hc : ContinuousOn (fun p : (ℂ × ℂ) × ℂ => F p.1 p.2) ((sphere (0 : ℂ) r ×ˢ sphere (0 : ℂ) r) ×ˢ S))
    {g : ℂ → ℝ} (hg : IntegrableOn g S)
    (hb : ∀ q ∈ sphere (0 : ℂ) r ×ˢ sphere (0 : ℂ) r, ∀ v ∈ S, ‖F q v‖ ≤ g v) :
    IntegrableOn (fun v => ∮ a in C(0, r), ∮ b in C(0, r), K (a, b) * F (a, b) v) S ∧
      ∫ v in S, (∮ a in C(0, r), ∮ b in C(0, r), K (a, b) * F (a, b) v) =
        ∮ a in C(0, r), ∮ b in C(0, r), K (a, b) * ∫ v in S, F (a, b) v := by
  obtain ⟨B, hB⟩ := ((isCompact_sphere (0 : ℂ) r).prod (isCompact_sphere (0 : ℂ) r)).exists_bound_of_continuousOn hK
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB (r, r) ⟨by simp [abs_of_pos hr], by simp [abs_of_pos hr]⟩)
  -- the inner swap, for each `a` on the circle
  have hin : ∀ a ∈ sphere (0 : ℂ) r,
      IntegrableOn (fun v => ∮ b in C(0, r), K (a, b) * F (a, b) v) S ∧
        ∫ v in S, (∮ b in C(0, r), K (a, b) * F (a, b) v) = ∮ b in C(0, r), ∫ v in S, K (a, b) * F (a, b) v := by
    intro a ha
    refine e64_circ_swap (H := fun b v => K (a, b) * F (a, b) v) hS hr ?_ (hg.const_mul B) ?_
    · have h1 : ContinuousOn (fun p : ℂ × ℂ => K (a, p.1)) (sphere (0 : ℂ) r ×ˢ S) :=
        hK.comp (continuous_const.prodMk continuous_fst).continuousOn fun p hp => ⟨ha, hp.1⟩
      have h2 : ContinuousOn (fun p : ℂ × ℂ => F (a, p.1) p.2) (sphere (0 : ℂ) r ×ˢ S) :=
        hc.comp ((continuous_const.prodMk continuous_fst).prodMk continuous_snd).continuousOn
          fun p hp => ⟨⟨ha, hp.1⟩, hp.2⟩
      exact h1.mul h2
    · intro b hb' v hv
      rw [norm_mul]
      exact mul_le_mul (hB _ ⟨ha, hb'⟩) (hb _ ⟨ha, hb'⟩ v hv) (norm_nonneg _) hB0
  -- the outer swap
  have hout := e64_circ_swap (H := fun a v => ∮ b in C(0, r), K (a, b) * F (a, b) v) hS hr ?_
    (hg.const_mul (2 * π * r * B)) ?_
  · refine ⟨hout.1, ?_⟩
    rw [hout.2]
    refine circleIntegral.integral_congr hr.le fun a ha => ?_
    show (∫ v in S, ∮ b in C(0, r), K (a, b) * F (a, b) v) = ∮ b in C(0, r), K (a, b) * ∫ v in S, F (a, b) v
    rw [(hin a ha).2]
    refine circleIntegral.integral_congr hr.le fun b _ => ?_
    exact integral_const_mul (K (a, b)) (fun v => F (a, b) v)
  · -- joint continuity of the inner circle integral in `(a, v)`
    have h := wr_param_circ_cont (S := sphere (0 : ℂ) r ×ˢ S)
      (h := fun p : ℂ × ℂ => fun b => K (p.1, b) * F (p.1, b) p.2) (c := 0) hr ?_ 0
    · have hm : MapsTo (fun p : ℂ × ℂ => (p, (0 : ℂ))) (sphere (0 : ℂ) r ×ˢ S)
          ((sphere (0 : ℂ) r ×ˢ S) ×ˢ ball (0 : ℂ) r) := fun p hp => ⟨hp, mem_ball_self hr⟩
      refine (h.comp (continuous_id.prodMk continuous_const).continuousOn hm).congr fun p _ => ?_
      simp only [Function.comp_apply, zpow_zero, one_smul]
      rfl
    · have h1 : ContinuousOn (fun p : (ℂ × ℂ) × ℂ => K (p.1.1, p.2)) ((sphere (0 : ℂ) r ×ˢ S) ×ˢ sphere (0 : ℂ) r) :=
        hK.comp ((continuous_fst.comp continuous_fst).prodMk continuous_snd).continuousOn
          fun p hp => ⟨hp.1.1, hp.2⟩
      have h2 : ContinuousOn (fun p : (ℂ × ℂ) × ℂ => F (p.1.1, p.2) p.1.2)
          ((sphere (0 : ℂ) r ×ˢ S) ×ˢ sphere (0 : ℂ) r) :=
        hc.comp (((continuous_fst.comp continuous_fst).prodMk continuous_snd).prodMk
          (continuous_snd.comp continuous_fst)).continuousOn fun p hp => ⟨⟨hp.1.1, hp.2⟩, hp.1.2⟩
      exact h1.mul h2
  · intro a ha v hv
    show ‖∮ b in C(0, r), K (a, b) * F (a, b) v‖ ≤ 2 * π * r * B * g v
    have hle := circleIntegral.norm_integral_le_of_norm_le_const (f := fun b => K (a, b) * F (a, b) v)
      (c := 0) (C := B * g v) hr.le fun b hb' => by
        show ‖K (a, b) * F (a, b) v‖ ≤ B * g v
        rw [norm_mul]
        exact mul_le_mul (hB _ ⟨ha, hb'⟩) (hb _ ⟨ha, hb'⟩ v hv) (norm_nonneg _) hB0
    calc _ ≤ 2 * π * r * (B * g v) := hle
      _ = 2 * π * r * B * g v := by ring

/-! ### The holomorphic extension `Φ(P)(v)`

Throughout, `W P = w^{P₁ m₁ + P₂ m₂}` and `Φ P v = μ̄(v) K̂_P(z, v̄) K̂_P(v̄, z̄)`, with the holomorphic kernel
`K̂_P(a, b) = (W_P)_a(a) (W_P)_b(b)/(W_P(a) - W_P(b))²`. -/

/-- The coefficients `m₁ = μ·1_𝕌`, `m₂ = μ̄∘conj·1_𝕃` are smooth off `ℝ`. -/
theorem e64_m_smooth {μ : ℂ → ℂ} (hμs : ContDiffOn ℝ (⊤ : ℕ∞) μ upperHalf) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun u => if 0 < u.im then μ u else 0) {u : ℂ | u.im ≠ 0} ∧
      ContDiffOn ℝ (⊤ : ℕ∞) (fun u => if u.im < 0 then conj (μ (conj u)) else 0) {u : ℂ | u.im ≠ 0} := by
  have hU : IsOpen upperHalf := isOpen_lt continuous_const Complex.continuous_im
  have hL : IsOpen {u : ℂ | u.im < 0} := isOpen_lt Complex.continuous_im continuous_const
  have hμa : ∀ u ∈ upperHalf, ContDiffAt ℝ (⊤ : ℕ∞) μ u := fun u hu => hμs.contDiffAt (hU.mem_nhds hu)
  constructor
  · intro u hu
    refine ContDiffAt.contDiffWithinAt ?_
    rcases lt_or_gt_of_ne (show u.im ≠ 0 from hu) with h | h
    · refine (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq ?_
      filter_upwards [hL.mem_nhds h] with x hx
      have : ¬ (0 < x.im) := not_lt.mpr (le_of_lt hx)
      simp only [this, ↓reduceIte]
    · refine (hμa u h).congr_of_eventuallyEq ?_
      filter_upwards [hU.mem_nhds h] with x hx
      have : 0 < x.im := hx
      simp only [this, ↓reduceIte]
  · intro u hu
    refine ContDiffAt.contDiffWithinAt ?_
    rcases lt_or_gt_of_ne (show u.im ≠ 0 from hu) with h | h
    · have hc : conj u ∈ upperHalf := by show 0 < (conj u).im; rw [Complex.conj_im]; linarith
      have h1 : ContDiffAt ℝ (⊤ : ℕ∞) (fun x : ℂ => conj (μ (conj x))) u :=
        Complex.conjCLE.contDiff.contDiffAt.comp u
          ((hμa _ hc).comp u Complex.conjCLE.contDiff.contDiffAt)
      refine h1.congr_of_eventuallyEq ?_
      filter_upwards [hL.mem_nhds h] with x hx
      have : x.im < 0 := hx
      simp only [this, ↓reduceIte]
    · refine (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq ?_
      filter_upwards [hU.mem_nhds h] with x hx
      have : ¬ (x.im < 0) := not_lt.mpr (le_of_lt hx)
      simp only [this, ↓reduceIte]

/-- Basic facts on `W_P`: joint `C³` on `{max ‖Pᵢ‖ k < 1} × {Im ≠ 0}`, injectivity, holomorphy in `P`. -/
theorem e64_W_basic {μ : ℂ → ℂ} {k : ℝ} (hk : 0 ≤ k) (hμk : IsBeltramiCoeff μ upperHalf k)
    (hμs : ContDiffOn ℝ (⊤ : ℕ∞) μ upperHalf)
    {W : ℂ × ℂ → ℂ → ℂ} (hW : W = fun P => normalizedSolution fun u =>
      P.1 * (if 0 < u.im then μ u else 0) + P.2 * (if u.im < 0 then conj (μ (conj u)) else 0)) :
    ContDiffOn ℝ 3 (fun q : (ℂ × ℂ) × ℂ => W q.1 q.2)
        ({P : ℂ × ℂ | max ‖P.1‖ ‖P.2‖ * k < 1} ×ˢ {u : ℂ | u.im ≠ 0}) ∧
      (∀ P ∈ {P : ℂ × ℂ | max ‖P.1‖ ‖P.2‖ * k < 1}, Function.Injective (W P)) ∧
      ∀ y : ℂ, ∀ P ∈ {P : ℂ × ℂ | max ‖P.1‖ ‖P.2‖ * k < 1}, DifferentiableAt ℂ (fun Q => W Q y) P := by
  obtain ⟨hm₁, hm₂, -, -, hcomb⟩ := wr_U_coeffs hk hμk hμs
  obtain ⟨hs₁, hs₂⟩ := e64_m_smooth hμs
  have hΩ : IsOpen {u : ℂ | u.im ≠ 0} := isOpen_ne_fun Complex.continuous_im continuous_const
  have hWo : IsOpen {P : ℂ × ℂ | max ‖P.1‖ ‖P.2‖ * k < 1} :=
    isOpen_lt (((continuous_norm.comp continuous_fst).max (continuous_norm.comp continuous_snd)).mul
      continuous_const) continuous_const
  subst hW
  refine ⟨wr_local_joint_contDiff hm₁ hm₂ hΩ hs₁ hs₂ hWo (fun P hP => hcomb P.1 P.2 hP), ?_, ?_⟩
  · intro P hP
    obtain ⟨k', hk', hP'⟩ := hcomb P.1 P.2 hP
    obtain ⟨h0, hk0, hk1⟩ := wr_coeff_nonneg hk' hP'
    have h := wr_ns_qc hk0 hk1 h0 le_rfl
    obtain ⟨e, he⟩ := t1_homeomorph h.1 h.2.1
    intro x y hxy
    apply e.injective
    rw [he]
    exact hxy
  · intro y P hP
    obtain ⟨k', hk', hP'⟩ := hcomb P.1 P.2 hP
    exact wr_ns2_diffAt hm₁ hm₂ hk' hP' y

/-- `∂_y W_P(y)` through the joint derivative, and its joint continuity. -/
theorem e64_dzW_cont {μ : ℂ → ℂ} {k : ℝ} (hk : 0 ≤ k) (hμk : IsBeltramiCoeff μ upperHalf k)
    (hμs : ContDiffOn ℝ (⊤ : ℕ∞) μ upperHalf)
    {W : ℂ × ℂ → ℂ → ℂ} (hW : W = fun P => normalizedSolution fun u =>
      P.1 * (if 0 < u.im then μ u else 0) + P.2 * (if u.im < 0 then conj (μ (conj u)) else 0)) :
    ContinuousOn (fun q : (ℂ × ℂ) × ℂ => W q.1 q.2)
        ({P : ℂ × ℂ | max ‖P.1‖ ‖P.2‖ * k < 1} ×ˢ {u : ℂ | u.im ≠ 0}) ∧
      ContinuousOn (fun q : (ℂ × ℂ) × ℂ => dz (W q.1) q.2)
        ({P : ℂ × ℂ | max ‖P.1‖ ‖P.2‖ * k < 1} ×ˢ {u : ℂ | u.im ≠ 0}) := by
  obtain ⟨hC, -, -⟩ := e64_W_basic hk hμk hμs hW
  have hΩ : IsOpen {u : ℂ | u.im ≠ 0} := isOpen_ne_fun Complex.continuous_im continuous_const
  have hWo : IsOpen {P : ℂ × ℂ | max ‖P.1‖ ‖P.2‖ * k < 1} :=
    isOpen_lt (((continuous_norm.comp continuous_fst).max (continuous_norm.comp continuous_snd)).mul
      continuous_const) continuous_const
  have hO := hWo.prod hΩ
  set F : (ℂ × ℂ) × ℂ → ℂ := fun q => W q.1 q.2 with hF
  have hfd : ContinuousOn (fderiv ℝ F) _ := hC.continuousOn_fderiv_of_isOpen hO (by norm_num)
  have hpart : ∀ q ∈ ({P : ℂ × ℂ | max ‖P.1‖ ‖P.2‖ * k < 1} ×ˢ {u : ℂ | u.im ≠ 0}), ∀ v : ℂ,
      fderiv ℝ (W q.1) q.2 v = fderiv ℝ F q (0, v) := by
    intro q hq v
    have hFd : DifferentiableAt ℝ F (q.1, q.2) :=
      (hC.contDiffAt (hO.mem_nhds hq)).differentiableAt (by norm_num)
    have hi : HasFDerivAt (fun y : ℂ => (q.1, y)) (ContinuousLinearMap.inr ℝ (ℂ × ℂ) ℂ) q.2 :=
      hasFDerivAt_prodMk_right q.1 q.2
    have hcomp := hFd.hasFDerivAt.comp q.2 hi
    have he : (fun y => W q.1 y) = F ∘ fun y : ℂ => (q.1, y) := rfl
    rw [show W q.1 = fun y => W q.1 y from rfl, he, hcomp.fderiv]
    rfl
  refine ⟨hC.continuousOn, ?_⟩
  have h2 : ContinuousOn (fun q : (ℂ × ℂ) × ℂ =>
      (fderiv ℝ F q ((0 : ℂ × ℂ), (1 : ℂ)) - I * fderiv ℝ F q ((0 : ℂ × ℂ), I)) / 2)
      ({P : ℂ × ℂ | max ‖P.1‖ ‖P.2‖ * k < 1} ×ˢ {u : ℂ | u.im ≠ 0}) :=
    ((hfd.clm_apply continuousOn_const).sub (continuousOn_const.mul (hfd.clm_apply continuousOn_const))).div_const _
  refine h2.congr fun q hq => ?_
  show (fderiv ℝ (W q.1) q.2 1 - I * fderiv ℝ (W q.1) q.2 I) / 2 = _
  rw [hpart q hq, hpart q hq]

/-- Separate holomorphy of `P ↦ ∂_y W_P(y)` off `ℝ` (mixed partials, `l613_wirt_comm`). -/
theorem e64_dzW_holo {μ : ℂ → ℂ} {k : ℝ} (hk : 0 ≤ k) (hμk : IsBeltramiCoeff μ upperHalf k)
    (hμs : ContDiffOn ℝ (⊤ : ℕ∞) μ upperHalf)
    {W : ℂ × ℂ → ℂ → ℂ} (hW : W = fun P => normalizedSolution fun u =>
      P.1 * (if 0 < u.im then μ u else 0) + P.2 * (if u.im < 0 then conj (μ (conj u)) else 0))
    {P : ℂ × ℂ} (hP : P ∈ {P : ℂ × ℂ | max ‖P.1‖ ‖P.2‖ * k < 1}) {y : ℂ} (hy : y.im ≠ 0) :
    DifferentiableAt ℂ (fun a => dz (W (a, P.2)) y) P.1 ∧ DifferentiableAt ℂ (fun b => dz (W (P.1, b)) y) P.2 := by
  obtain ⟨hC, -, hhol⟩ := e64_W_basic hk hμk hμs hW
  have hΩ : IsOpen {u : ℂ | u.im ≠ 0} := isOpen_ne_fun Complex.continuous_im continuous_const
  have hWo : IsOpen {P : ℂ × ℂ | max ‖P.1‖ ‖P.2‖ * k < 1} :=
    isOpen_lt (((continuous_norm.comp continuous_fst).max (continuous_norm.comp continuous_snd)).mul
      continuous_const) continuous_const
  have hO := hWo.prod hΩ
  have hCa : ContDiffAt ℝ 3 (fun q : (ℂ × ℂ) × ℂ => W q.1 q.2) (P, y) := hC.contDiffAt (hO.mem_nhds ⟨hP, hy⟩)
  have hhol' : ∀ y', DifferentiableAt ℂ (fun Q => W Q y') P := fun y' => hhol y' P hP
  constructor
  · set G : ℂ × ℂ → ℂ := fun p => W (p.1, P.2) p.2 with hG
    have hGa : ContDiffAt ℝ 2 G (P.1, y) := by
      have hm : ContDiffAt ℝ 3 (fun p : ℂ × ℂ => ((p.1, P.2), p.2)) (P.1, y) :=
        ((contDiffAt_fst.prodMk contDiffAt_const).prodMk contDiffAt_snd)
      exact (ContDiffAt.comp (g := fun q : (ℂ × ℂ) × ℂ => W q.1 q.2) (P.1, y) hCa hm).of_le (by norm_num)
    obtain ⟨hd, -, hbar⟩ := l613_wirt_comm hGa
    have h0 : (fun w' => dzbar (fun e' => G (e', w')) P.1) = fun _ => (0 : ℂ) := by
      funext w'
      have hc : DifferentiableAt ℂ (fun e' : ℂ => W (e', P.2) w') P.1 :=
        DifferentiableAt.comp (g := fun Q => W Q w') P.1 (hhol' w') (by fun_prop)
      exact (cauchyRiemann_iff.1 hc).2
    rw [h0] at hbar
    have hz : dz (fun _ : ℂ => (0 : ℂ)) y = 0 := by simp [dz]
    rw [hz] at hbar
    exact cauchyRiemann_iff.2 ⟨hd, hbar⟩
  · set G : ℂ × ℂ → ℂ := fun p => W (P.1, p.1) p.2 with hG
    have hGa : ContDiffAt ℝ 2 G (P.2, y) := by
      have hm : ContDiffAt ℝ 3 (fun p : ℂ × ℂ => ((P.1, p.1), p.2)) (P.2, y) :=
        ((contDiffAt_const.prodMk contDiffAt_fst).prodMk contDiffAt_snd)
      exact (ContDiffAt.comp (g := fun q : (ℂ × ℂ) × ℂ => W q.1 q.2) (P.2, y) hCa hm).of_le (by norm_num)
    obtain ⟨hd, -, hbar⟩ := l613_wirt_comm hGa
    have h0 : (fun w' => dzbar (fun e' => G (e', w')) P.2) = fun _ => (0 : ℂ) := by
      funext w'
      have hc : DifferentiableAt ℂ (fun e' : ℂ => W (P.1, e') w') P.2 :=
        DifferentiableAt.comp (g := fun Q => W Q w') P.2 (hhol' w') (by fun_prop)
      exact (cauchyRiemann_iff.1 hc).2
    rw [h0] at hbar
    have hz : dz (fun _ : ℂ => (0 : ℂ)) y = 0 := by simp [dz]
    rw [hz] at hbar
    exact cauchyRiemann_iff.2 ⟨hd, hbar⟩

/-- The closed polydisc of radius `R` (`Rk < 1`) lies in the parameter domain. -/
theorem e64_polydisc_sub {k R : ℝ} (hk : 0 ≤ k) (hRk : R * k < 1) :
    closedBall (0 : ℂ) R ×ˢ closedBall (0 : ℂ) R ⊆ {P : ℂ × ℂ | max ‖P.1‖ ‖P.2‖ * k < 1} := by
  intro P hP
  have h1 : ‖P.1‖ ≤ R := by simpa using hP.1
  have h2 : ‖P.2‖ ≤ R := by simpa using hP.2
  show max ‖P.1‖ ‖P.2‖ * k < 1
  calc max ‖P.1‖ ‖P.2‖ * k ≤ R * k := mul_le_mul_of_nonneg_right (max_le h1 h2) hk
    _ < 1 := hRk

/-- **(E2)** Joint continuity of `Φ` on `closed polydisc × (𝕌 ∖ {z})` (W-REG D2 on `{Im ≠ 0}`, injectivity). -/
theorem e64_phi_cont {μ : ℂ → ℂ} {k : ℝ} (hk : 0 ≤ k) (hμk : IsBeltramiCoeff μ upperHalf k)
    (hμs : ContDiffOn ℝ (⊤ : ℕ∞) μ upperHalf) {z : ℂ} (hz : z ∈ upperHalf) {R : ℝ} (hRk : R * k < 1)
    {W : ℂ × ℂ → ℂ → ℂ} (hW : W = fun P => normalizedSolution fun u =>
      P.1 * (if 0 < u.im then μ u else 0) + P.2 * (if u.im < 0 then conj (μ (conj u)) else 0))
    {Φ : ℂ × ℂ → ℂ → ℂ} (hΦ : Φ = fun P v => conj (μ v) *
      (dz (W P) z * dz (W P) (conj v) / (W P z - W P (conj v)) ^ 2) *
      (dz (W P) (conj v) * dz (W P) (conj z) / (W P (conj v) - W P (conj z)) ^ 2)) :
    ContinuousOn (fun p : (ℂ × ℂ) × ℂ => Φ p.1 p.2)
      ((closedBall (0 : ℂ) R ×ˢ closedBall (0 : ℂ) R) ×ˢ (upperHalf \ {z})) := by
  obtain ⟨-, hinj, -⟩ := e64_W_basic hk hμk hμs hW
  obtain ⟨hWc, hDc⟩ := e64_dzW_cont hk hμk hμs hW
  have hsub := e64_polydisc_sub hk hRk
  obtain ⟨T, hT⟩ : ∃ T : Set ((ℂ × ℂ) × ℂ), T = (closedBall (0 : ℂ) R ×ˢ closedBall (0 : ℂ) R) ×ˢ (upperHalf \ {z}) :=
    ⟨_, rfl⟩
  rw [← hT]
  have hmem : ∀ p ∈ T, p.1 ∈ closedBall (0 : ℂ) R ×ˢ closedBall (0 : ℂ) R ∧ 0 < p.2.im ∧ p.2 ≠ z := by
    rw [hT]
    rintro p ⟨h1, h2, h3⟩
    exact ⟨h1, h2, h3⟩
  have hzim : 0 < z.im := hz
  -- the three evaluation points
  have hcomp : ∀ g : (ℂ × ℂ) × ℂ → ℂ, Continuous g → (∀ p ∈ T, (g p).im ≠ 0) →
      ContinuousOn (fun p => W p.1 (g p)) T ∧ ContinuousOn (fun p => dz (W p.1) (g p)) T := by
    intro g hg hgi
    have hm : MapsTo (fun p : (ℂ × ℂ) × ℂ => (p.1, g p)) T
        ({P : ℂ × ℂ | max ‖P.1‖ ‖P.2‖ * k < 1} ×ˢ {u : ℂ | u.im ≠ 0}) :=
      fun p hp => ⟨hsub (hmem p hp).1, hgi p hp⟩
    have hc : Continuous fun p : (ℂ × ℂ) × ℂ => (p.1, g p) := continuous_fst.prodMk hg
    have h1 := hWc.comp hc.continuousOn hm
    have h2 := hDc.comp hc.continuousOn hm
    simp only [Function.comp_def] at h1 h2
    exact ⟨h1, h2⟩
  have hvim : ∀ p ∈ T, 0 < p.2.im := fun p hp => (hmem p hp).2.1
  obtain ⟨hWz, hDz⟩ := hcomp (fun _ => z) continuous_const fun _ _ => (hzim.ne' : z.im ≠ 0)
  obtain ⟨hWv, hDv⟩ := hcomp (fun p => conj p.2) (Complex.continuous_conj.comp continuous_snd) fun p hp => by
    rw [Complex.conj_im]; linarith [hvim p hp]
  obtain ⟨hWzb, hDzb⟩ := hcomp (fun _ => conj z) continuous_const fun _ _ => by
    rw [Complex.conj_im]; linarith
  have hμc : ContinuousOn (fun p : (ℂ × ℂ) × ℂ => conj (μ p.2)) T :=
    Complex.continuous_conj.comp_continuousOn (hμs.continuousOn.comp continuous_snd.continuousOn
      fun p hp => (hmem p hp).2.1)
  have hne1 : ∀ p ∈ T, (W p.1 z - W p.1 (conj p.2)) ^ 2 ≠ 0 := by
    intro p hp
    refine pow_ne_zero 2 (sub_ne_zero.mpr fun h => ?_)
    have := hinj p.1 (hsub (hmem p hp).1) h
    have h2 : z.im = (conj p.2).im := by rw [this]
    rw [Complex.conj_im] at h2
    linarith [hvim p hp]
  have hne2 : ∀ p ∈ T, (W p.1 (conj p.2) - W p.1 (conj z)) ^ 2 ≠ 0 := by
    intro p hp
    refine pow_ne_zero 2 (sub_ne_zero.mpr fun h => ?_)
    have := hinj p.1 (hsub (hmem p hp).1) h
    have h2 : p.2 = z := by simpa using congrArg conj this
    exact (hmem p hp).2.2 h2
  rw [hΦ]
  exact (hμc.mul ((hDz.mul hDv).div ((hWz.sub hWv).pow 2) hne1)).mul
    ((hDv.mul hDzb).div ((hWv.sub hWzb).pow 2) hne2)

/-- **(E3)** Separate holomorphy of `P ↦ Φ(P)(v)` (`wr_ns2_diffAt`; `∂_y` commutes with `∂_P` by joint `C³`). -/
theorem e64_phi_holo {μ : ℂ → ℂ} {k : ℝ} (hk : 0 ≤ k) (hμk : IsBeltramiCoeff μ upperHalf k)
    (hμs : ContDiffOn ℝ (⊤ : ℕ∞) μ upperHalf) {z : ℂ} (hz : z ∈ upperHalf) {R : ℝ} (hRk : R * k < 1)
    {W : ℂ × ℂ → ℂ → ℂ} (hW : W = fun P => normalizedSolution fun u =>
      P.1 * (if 0 < u.im then μ u else 0) + P.2 * (if u.im < 0 then conj (μ (conj u)) else 0))
    {Φ : ℂ × ℂ → ℂ → ℂ} (hΦ : Φ = fun P v => conj (μ v) *
      (dz (W P) z * dz (W P) (conj v) / (W P z - W P (conj v)) ^ 2) *
      (dz (W P) (conj v) * dz (W P) (conj z) / (W P (conj v) - W P (conj z)) ^ 2))
    {v : ℂ} (hv : v ∈ upperHalf) (hvz : v ≠ z) :
    (∀ b ∈ closedBall (0 : ℂ) R, DifferentiableOn ℂ (fun a => Φ (a, b) v) (ball (0 : ℂ) R)) ∧
      ∀ a ∈ closedBall (0 : ℂ) R, DifferentiableOn ℂ (fun b => Φ (a, b) v) (ball (0 : ℂ) R) := by
  obtain ⟨-, hinj, hhol⟩ := e64_W_basic hk hμk hμs hW
  have hsub := e64_polydisc_sub hk hRk
  have hzim : 0 < z.im := hz
  have hvim : 0 < v.im := hv
  have hy1 : z.im ≠ 0 := hzim.ne'
  have hy2 : (conj v).im ≠ 0 := by rw [Complex.conj_im]; linarith
  have hy3 : (conj z).im ≠ 0 := by rw [Complex.conj_im]; linarith
  have hne1 : ∀ P ∈ {P : ℂ × ℂ | max ‖P.1‖ ‖P.2‖ * k < 1}, (W P z - W P (conj v)) ^ 2 ≠ 0 := by
    intro P hP
    refine pow_ne_zero 2 (sub_ne_zero.mpr fun h => ?_)
    have := hinj P hP h
    have h2 : z.im = (conj v).im := by rw [this]
    rw [Complex.conj_im] at h2
    linarith
  have hne2 : ∀ P ∈ {P : ℂ × ℂ | max ‖P.1‖ ‖P.2‖ * k < 1}, (W P (conj v) - W P (conj z)) ^ 2 ≠ 0 := by
    intro P hP
    refine pow_ne_zero 2 (sub_ne_zero.mpr fun h => ?_)
    have := hinj P hP h
    exact hvz (by simpa using congrArg conj this)
  -- along any holomorphic curve in the parameter domain
  have hcurve : ∀ (c : ℂ → ℂ × ℂ) (t : ℂ), c t ∈ {P : ℂ × ℂ | max ‖P.1‖ ‖P.2‖ * k < 1} →
      (∀ y, DifferentiableAt ℂ (fun t' => W (c t') y) t) →
      (∀ y, y.im ≠ 0 → DifferentiableAt ℂ (fun t' => dz (W (c t')) y) t) →
      DifferentiableAt ℂ (fun t' => Φ (c t') v) t := by
    intro c t hct hWy hDy
    rw [hΦ]
    exact (differentiableAt_const _ |>.mul (((hDy z hy1).mul (hDy _ hy2)).div
      (((hWy z).sub (hWy (conj v))).pow 2) (hne1 _ hct))).mul
      (((hDy _ hy2).mul (hDy _ hy3)).div (((hWy (conj v)).sub (hWy (conj z))).pow 2) (hne2 _ hct))
  constructor
  · intro b hb a ha
    have hP : (a, b) ∈ {P : ℂ × ℂ | max ‖P.1‖ ‖P.2‖ * k < 1} := hsub ⟨ball_subset_closedBall ha, hb⟩
    refine (hcurve (fun t => (t, b)) a hP (fun y => ?_) (fun y hy => ?_)).differentiableWithinAt
    · exact DifferentiableAt.comp (g := fun Q => W Q y) a (hhol y _ hP) (by fun_prop)
    · exact (e64_dzW_holo hk hμk hμs hW hP hy).1
  · intro a ha b hb
    have hP : (a, b) ∈ {P : ℂ × ℂ | max ‖P.1‖ ‖P.2‖ * k < 1} := hsub ⟨ha, ball_subset_closedBall hb⟩
    refine (hcurve (fun t => (a, t)) b hP (fun y => ?_) (fun y hy => ?_)).differentiableWithinAt
    · exact DifferentiableAt.comp (g := fun Q => W Q y) b (hhol y _ hP) (by fun_prop)
    · exact (e64_dzW_holo hk hμk hμs hW hP hy).2

/-- **(E4)** On the diagonal `P = (ε, ε̄)`, `Φ` is the integrand of `eq_1_25` at `u = z` (`wr_wU_eq`; the symmetry
`w_ε(ȳ) = \overline{w_ε(y)}`, `(w_ε)_y(ȳ) = \overline{(w_ε)_y(y)}`). -/
theorem e64_phi_diag {μ : ℂ → ℂ} {k : ℝ} (hk : 0 ≤ k) (hμk : IsBeltramiCoeff μ upperHalf k)
    (hμs : ContDiffOn ℝ (⊤ : ℕ∞) μ upperHalf) {z : ℂ} (hz : z ∈ upperHalf)
    {W : ℂ × ℂ → ℂ → ℂ} (hW : W = fun P => normalizedSolution fun u =>
      P.1 * (if 0 < u.im then μ u else 0) + P.2 * (if u.im < 0 then conj (μ (conj u)) else 0))
    {Φ : ℂ × ℂ → ℂ → ℂ} (hΦ : Φ = fun P v => conj (μ v) *
      (dz (W P) z * dz (W P) (conj v) / (W P z - W P (conj v)) ^ 2) *
      (dz (W P) (conj v) * dz (W P) (conj z) / (W P (conj v) - W P (conj z)) ^ 2))
    {ε : ℂ} (hε : ‖ε‖ * k < 1) {v : ℂ} (hv : v ∈ upperHalf) :
    Φ (ε, conj ε) v = conj (μ v) * kernelKbar (fun y => ε * μ y) z v * kernelKbarbar (fun y => ε * μ y) v z := by
  have _hz := hz
  have _hv := hv
  have _hs := hμs
  have hWe : W (ε, conj ε) = wU (fun y => ε * μ y) := by rw [hW, wr_wU_eq]
  set f := wU (fun y => ε * μ y) with hf
  have hν : IsBeltramiCoeff (fun y => ε * μ y) upperHalf (‖ε‖ * k) :=
    ⟨hμk.1.const_mul ε, hμk.2.mono fun z hz => by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left hz (norm_nonneg _)⟩
  have hsym : ∀ x, f (conj x) = conj (f x) := by
    rw [hf, e124_wU_eq_fMuSym hk hμk hε]
    exact (fMuSym_upperHalf (by positivity) hε hν).2.2.1
  have hdsym : ∀ x, dz f (conj x) = conj (dz f x) := QCV.qcv_dz_conj_sym hsym
  rw [hΦ]
  simp only [hWe]
  unfold kernelKbar kernelKbarbar kernelK
  rw [← hf, map_div₀, map_mul, map_pow, map_sub, ← hsym v, ← hsym z, ← hdsym v, ← hdsym z]

/-- Pointwise Beltrami equation and positive Jacobian of `W_q` on `𝕃` (continuity plus the a.e. equation). -/
theorem e64_t5_beltrami {μ : ℂ → ℂ} {k : ℝ} (hk : 0 ≤ k) (hμk : IsBeltramiCoeff μ upperHalf k)
    (hμs : ContDiffOn ℝ (⊤ : ℕ∞) μ upperHalf)
    {W : ℂ × ℂ → ℂ → ℂ} (hW : W = fun P => normalizedSolution fun u =>
      P.1 * (if 0 < u.im then μ u else 0) + P.2 * (if u.im < 0 then conj (μ (conj u)) else 0))
    {q : ℂ × ℂ} (hq : q ∈ {P : ℂ × ℂ | max ‖P.1‖ ‖P.2‖ * k < 1}) {y : ℂ} (hy : y.im < 0) :
    dzbar (W q) y = q.2 * conj (μ (conj y)) * dz (W q) y ∧ 0 < jacobian (W q) y := by
  obtain ⟨hC, -, -⟩ := e64_W_basic hk hμk hμs hW
  obtain ⟨hm₁, hm₂, -, -, hcomb⟩ := wr_U_coeffs hk hμk hμs
  obtain ⟨hs₁, hs₂⟩ := e64_m_smooth hμs
  have hΩ : IsOpen {u : ℂ | u.im ≠ 0} := isOpen_ne_fun Complex.continuous_im continuous_const
  have hL : IsOpen {u : ℂ | u.im < 0} := isOpen_lt Complex.continuous_im continuous_const
  have hLΩ : {u : ℂ | u.im < 0} ⊆ {u : ℂ | u.im ≠ 0} := fun u hu => ne_of_lt hu
  have hJ : ∀ x ∈ {u : ℂ | u.im < 0}, 0 < jacobian (W q) x := by
    intro x hx
    rw [hW]
    exact wr_local_jacobian_pos hm₁ hm₂ hΩ hs₁ hs₂ (hcomb q.1 q.2 hq) (hLΩ hx)
  refine ⟨?_, hJ y hy⟩
  set f := W q with hf
  have hCf : ContDiffOn ℝ 3 f {u : ℂ | u.im < 0} := by
    have h := hC.comp (s := {u : ℂ | u.im < 0}) (contDiffOn_const.prodMk contDiffOn_id)
      (fun x hx => ⟨hq, hLΩ hx⟩)
    exact h
  have hdz0 : ∀ x ∈ {u : ℂ | u.im < 0}, dz f x ≠ 0 := by
    intro x hx h0
    have := hJ x hx
    unfold jacobian at this
    rw [h0, norm_zero] at this
    nlinarith [norm_nonneg (dzbar f x)]
  have hfd : ContinuousOn (fderiv ℝ f) {u : ℂ | u.im < 0} := hCf.continuousOn_fderiv_of_isOpen hL (by norm_num)
  have hdzc : ContinuousOn (dz f) {u : ℂ | u.im < 0} := by
    unfold dz
    exact (((hfd.clm_apply continuousOn_const).sub (continuousOn_const.mul
      (hfd.clm_apply continuousOn_const)))).div_const _
  have hdzbc : ContinuousOn (dzbar f) {u : ℂ | u.im < 0} := by
    unfold dzbar
    exact (((hfd.clm_apply continuousOn_const).add (continuousOn_const.mul
      (hfd.clm_apply continuousOn_const)))).div_const _
  have hcd : ContinuousOn (complexDilatation f) {u : ℂ | u.im < 0} := hdzbc.div hdzc hdz0
  have hcm : ContinuousOn (fun x => q.2 * conj (μ (conj x))) {u : ℂ | u.im < 0} := by
    refine continuousOn_const.mul (Complex.continuous_conj.comp_continuousOn
      (hμs.continuousOn.comp Complex.continuous_conj.continuousOn fun x hx => ?_))
    show 0 < (conj x).im
    rw [Complex.conj_im]
    have : x.im < 0 := hx
    linarith
  obtain ⟨k', hk', hP'⟩ := hcomb q.1 q.2 hq
  obtain ⟨h0, hk0, hk1⟩ := wr_coeff_nonneg hk' hP'
  have hns := QCV.qcv_ns_spec hk0 hk1 h0
  have hae : complexDilatation f =ᵐ[volume.restrict {u : ℂ | u.im < 0}] fun x => q.2 * conj (μ (conj x)) := by
    filter_upwards [ae_restrict_of_ae hns.2.2.2.2, ae_restrict_mem hL.measurableSet] with x hx hxL
    rw [hf, hW]
    rw [hx]
    have h1 : ¬ (0 < x.im) := not_lt.mpr (le_of_lt hxL)
    have h2 : x.im < 0 := hxL
    simp only [h1, h2, ↓reduceIte, mul_zero, zero_add]
  have heq := Measure.eqOn_open_of_ae_eq hae hL hcd hcm hy
  have e : dzbar f y = complexDilatation f y * dz f y := (div_mul_cancel₀ _ (hdz0 y hy)).symm
  rw [e, heq]

/-- Uniform separation: `W_q` moves points at distance `≥ δ` from `c` at least `η` away from `W_q(c)`, uniformly
over the closed polydisc (normal families via `wr_ns2_cont`, `wr_ns2_inv_cont`). -/
theorem e64_t5_sep {μ : ℂ → ℂ} {k : ℝ} (hk : 0 ≤ k) (hμk : IsBeltramiCoeff μ upperHalf k)
    (hμs : ContDiffOn ℝ (⊤ : ℕ∞) μ upperHalf) {R : ℝ} (hRk : R * k < 1)
    {W : ℂ × ℂ → ℂ → ℂ} (hW : W = fun P => normalizedSolution fun u =>
      P.1 * (if 0 < u.im then μ u else 0) + P.2 * (if u.im < 0 then conj (μ (conj u)) else 0))
    (c : ℂ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ η > 0, ∀ q ∈ closedBall (0 : ℂ) R ×ˢ closedBall (0 : ℂ) R, ∀ y : ℂ, δ ≤ ‖y - c‖ → η ≤ ‖W q y - W q c‖ := by
  obtain ⟨-, hinj, -⟩ := e64_W_basic hk hμk hμs hW
  obtain ⟨hm₁, hm₂, -, -, hcomb⟩ := wr_U_coeffs hk hμk hμs
  have hsub := e64_polydisc_sub hk hRk
  have hWo : IsOpen {P : ℂ × ℂ | max ‖P.1‖ ‖P.2‖ * k < 1} :=
    isOpen_lt (((continuous_norm.comp continuous_fst).max (continuous_norm.comp continuous_snd)).mul
      continuous_const) continuous_const
  have hWk : ∀ P ∈ {P : ℂ × ℂ | max ‖P.1‖ ‖P.2‖ * k < 1}, ∃ k' < 1, IsBeltramiCoeff
      (fun u => P.1 * (if 0 < u.im then μ u else 0) + P.2 * (if u.im < 0 then conj (μ (conj u)) else 0)) univ k' :=
    fun P hP => hcomb P.1 P.2 hP
  have hcont : ContinuousOn (fun q : (ℂ × ℂ) × ℂ => W q.1 q.2) ({P : ℂ × ℂ | max ‖P.1‖ ‖P.2‖ * k < 1} ×ˢ univ) := by
    rw [hW]; exact wr_ns2_cont hm₁ hm₂ hWo hWk
  have hicont : ContinuousOn (fun q : (ℂ × ℂ) × ℂ => Function.invFun (W q.1) q.2)
      ({P : ℂ × ℂ | max ‖P.1‖ ‖P.2‖ * k < 1} ×ˢ univ) := by
    rw [hW]; exact wr_ns2_inv_cont hm₁ hm₂ hWo hWk
  by_contra hcon
  push Not at hcon
  have hseq : ∀ n : ℕ, ∃ q ∈ closedBall (0 : ℂ) R ×ˢ closedBall (0 : ℂ) R, ∃ y : ℂ,
      δ ≤ ‖y - c‖ ∧ ‖W q y - W q c‖ < 1 / ((n : ℝ) + 1) := fun n => hcon _ (by positivity)
  choose qs hqs ys hys using hseq
  have hK : IsCompact (closedBall (0 : ℂ) R ×ˢ closedBall (0 : ℂ) R) :=
    (isCompact_closedBall 0 R).prod (isCompact_closedBall 0 R)
  obtain ⟨q₀, hq₀, φ, hφ, hlim⟩ := hK.tendsto_subseq hqs
  have hq₀W := hsub hq₀
  have hWc : Tendsto (fun n => W (qs (φ n)) c) atTop (𝓝 (W q₀ c)) := by
    have h := (hcont (q₀, c) ⟨hq₀W, mem_univ _⟩).tendsto.comp (x := atTop)
      (f := fun n => (qs (φ n), c)) (tendsto_nhdsWithin_iff.mpr ⟨hlim.prodMk_nhds tendsto_const_nhds,
        Eventually.of_forall fun n => ⟨hsub (hqs (φ n)), mem_univ _⟩⟩)
    exact h
  have hsmall : Tendsto (fun n => W (qs (φ n)) (ys (φ n)) - W (qs (φ n)) c) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero (fun n => norm_nonneg _) (fun n => (hys (φ n)).2.le) ?_
    have h1 : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
    exact h1.comp hφ.tendsto_atTop
  have hζ : Tendsto (fun n => W (qs (φ n)) (ys (φ n))) atTop (𝓝 (W q₀ c)) := by
    have := hsmall.add hWc
    simpa using this
  have hy : Tendsto (fun n => ys (φ n)) atTop (𝓝 c) := by
    have h := (hicont (q₀, W q₀ c) ⟨hq₀W, mem_univ _⟩).tendsto.comp (x := atTop)
      (f := fun n => (qs (φ n), W (qs (φ n)) (ys (φ n)))) (tendsto_nhdsWithin_iff.mpr
        ⟨hlim.prodMk_nhds hζ, Eventually.of_forall fun n => ⟨hsub (hqs (φ n)), mem_univ _⟩⟩)
    have e1 : ∀ n, Function.invFun (W (qs (φ n))) (W (qs (φ n)) (ys (φ n))) = ys (φ n) := fun n =>
      Function.leftInverse_invFun (hinj _ (hsub (hqs (φ n)))) _
    have e0 : Function.invFun (W q₀) (W q₀ c) = c := Function.leftInverse_invFun (hinj _ hq₀W) _
    simp only [Function.comp_def, e1, e0] at h
    exact h
  have hfar : ∀ n, δ ≤ ‖ys (φ n) - c‖ := fun n => (hys (φ n)).1
  have hn := (hy.sub_const c).norm
  simp only [sub_self, norm_zero] at hn
  exact absurd (ge_of_tendsto hn (Eventually.of_forall hfar)) (not_le.mpr hδ)

/-- `1/(X²Y²) ≤ ((1+η)/η)⁴ ((1+X)⁻⁴ + (1+Y)⁻⁴)` for `X, Y ≥ η > 0`. -/
theorem e64_t5_inv4 {X Y η : ℝ} (hη : 0 < η) (hX : η ≤ X) (hY : η ≤ Y) :
    1 / (X ^ 2 * Y ^ 2) ≤ ((1 + η) / η) ^ 4 * (((1 + X) ^ 4)⁻¹ + ((1 + Y) ^ 4)⁻¹) := by
  have hX0 : 0 < X := hη.trans_le hX
  have hY0 : 0 < Y := hη.trans_le hY
  have hamgm : 1 / (X ^ 2 * Y ^ 2) ≤ 1 / X ^ 4 + 1 / Y ^ 4 := by
    rw [div_add_div _ _ (by positivity) (by positivity), div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [sq_nonneg (X ^ 2 - Y ^ 2), sq_nonneg (X * Y), pow_pos hX0 4, pow_pos hY0 4,
      mul_pos (pow_pos hX0 2) (pow_pos hY0 2)]
  have hone : ∀ T : ℝ, η ≤ T → 1 / T ^ 4 ≤ ((1 + η) / η) ^ 4 * ((1 + T) ^ 4)⁻¹ := by
    intro T hT
    have hT0 : 0 < T := hη.trans_le hT
    have hr : (1 + T) / T ≤ (1 + η) / η := by
      rw [div_le_div_iff₀ hT0 hη]; nlinarith
    have e : 1 / T ^ 4 = ((1 + T) / T) ^ 4 * ((1 + T) ^ 4)⁻¹ := by field_simp
    rw [e]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hr 4) (by positivity)
  calc 1 / (X ^ 2 * Y ^ 2) ≤ 1 / X ^ 4 + 1 / Y ^ 4 := hamgm
    _ ≤ ((1 + η) / η) ^ 4 * ((1 + X) ^ 4)⁻¹ + ((1 + η) / η) ^ 4 * ((1 + Y) ^ 4)⁻¹ :=
        add_le_add (hone X hX) (hone Y hY)
    _ = _ := by ring

/-- The majorant `(1 + |ζ - a|)⁻⁴` is integrable on `ℂ`, with integral independent of `a`. -/
theorem e64_t5_maj (a : ℂ) :
    Integrable (fun ζ : ℂ => ((1 + ‖ζ - a‖) ^ 4)⁻¹) ∧
      ∫ ζ : ℂ, ((1 + ‖ζ - a‖) ^ 4)⁻¹ = ∫ ζ : ℂ, ((1 + ‖ζ‖) ^ 4)⁻¹ := by
  have h0 : Integrable (fun ζ : ℂ => ((1 + ‖ζ‖) ^ 4)⁻¹) := by
    have h := integrable_one_add_norm (E := ℂ) (μ := volume) (r := 4)
      (by rw [Complex.finrank_real_complex]; norm_num)
    refine h.congr (Eventually.of_forall fun ζ => ?_)
    show (1 + ‖ζ‖) ^ (-(4 : ℝ)) = ((1 + ‖ζ‖) ^ 4)⁻¹
    rw [Real.rpow_neg (by positivity), show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  exact ⟨h0.comp_sub_right a, integral_sub_right_eq_self (fun ζ : ℂ => ((1 + ‖ζ‖) ^ 4)⁻¹) a⟩

/-- The Jacobian of `v ↦ W_q(v̄)`: `|det| = J_{W_q}(v̄)`. -/
theorem e64_t5_det {f : ℂ → ℂ} {y : ℂ} (hJ : 0 < jacobian f y) (hd : DifferentiableAt ℝ f y) :
    |((fderiv ℝ f y).comp (Complex.conjCLE : ℂ →L[ℝ] ℂ)).det| = jacobian f y := by
  have hc : ((Complex.conjCLE : ℂ →L[ℝ] ℂ) : ℂ →ₗ[ℝ] ℂ) = Complex.conjAe.toLinearMap :=
    LinearMap.ext fun x => rfl
  show |LinearMap.det ((fderiv ℝ f y : ℂ →ₗ[ℝ] ℂ).comp ((Complex.conjCLE : ℂ →L[ℝ] ℂ) : ℂ →ₗ[ℝ] ℂ))| = _
  rw [LinearMap.det_comp, hc, Complex.det_conjAe, det_fderiv_eq_jacobian hd,
    mul_neg_one, abs_neg, abs_of_pos hJ]

/-- **(E5) Tail bound.** For `δ > 0`, `Φ(q)` is integrable on `𝕌 ∖ B(z, δ)` with an `L¹` bound uniform over the
closed polydisc. Route: `|μ| |(W_q)_y|² ≤ k J/(1 - (Rk)²)` on `𝕃` (pointwise Beltrami equation there), change of
variables `ζ = W_q(v̄)`, and `|ζ - W_q(z)|, |ζ - W_q(z̄)| ≥ η` uniformly in `q` (joint continuity of the inverses,
`wr_ns2_inv_cont`, on a compact set); then `∫_{|ζ-a|,|ζ-b| ≥ η} |ζ-a|⁻²|ζ-b|⁻² ≤ π/η²`. -/
theorem e64_tail_bound {μ : ℂ → ℂ} {k : ℝ} (hk : 0 ≤ k) (hμk : IsBeltramiCoeff μ upperHalf k)
    (hμs : ContDiffOn ℝ (⊤ : ℕ∞) μ upperHalf) {z : ℂ} (hz : z ∈ upperHalf) {R : ℝ} (hRk : R * k < 1)
    {W : ℂ × ℂ → ℂ → ℂ} (hW : W = fun P => normalizedSolution fun u =>
      P.1 * (if 0 < u.im then μ u else 0) + P.2 * (if u.im < 0 then conj (μ (conj u)) else 0))
    {Φ : ℂ × ℂ → ℂ → ℂ} (hΦ : Φ = fun P v => conj (μ v) *
      (dz (W P) z * dz (W P) (conj v) / (W P z - W P (conj v)) ^ 2) *
      (dz (W P) (conj v) * dz (W P) (conj z) / (W P (conj v) - W P (conj z)) ^ 2))
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ M : ℝ, ∀ q ∈ closedBall (0 : ℂ) R ×ˢ closedBall (0 : ℂ) R,
      IntegrableOn (Φ q) (upperHalf \ ball z δ) ∧ ∫ v in upperHalf \ ball z δ, ‖Φ q v‖ ≤ M := by
  obtain ⟨hC, hinj, -⟩ := e64_W_basic hk hμk hμs hW
  obtain ⟨-, hDc⟩ := e64_dzW_cont hk hμk hμs hW
  obtain ⟨hm₁, -, -, -, -⟩ := wr_U_coeffs hk hμk hμs
  obtain ⟨hs₁, -⟩ := e64_m_smooth hμs
  have hcΦ := e64_phi_cont hk hμk hμs hz hRk hW hΦ
  have hsub := e64_polydisc_sub hk hRk
  have hU : IsOpen upperHalf := isOpen_lt continuous_const Complex.continuous_im
  have hΩ : IsOpen {u : ℂ | u.im ≠ 0} := isOpen_ne_fun Complex.continuous_im continuous_const
  have hWo : IsOpen {P : ℂ × ℂ | max ‖P.1‖ ‖P.2‖ * k < 1} :=
    isOpen_lt (((continuous_norm.comp continuous_fst).max (continuous_norm.comp continuous_snd)).mul
      continuous_const) continuous_const
  have hzim : 0 < z.im := hz
  have hK : IsCompact (closedBall (0 : ℂ) R ×ˢ closedBall (0 : ℂ) R) :=
    (isCompact_closedBall 0 R).prod (isCompact_closedBall 0 R)
  -- `|μ| ≤ k` on `𝕌`
  have hμb : ∀ v ∈ upperHalf, ‖μ v‖ ≤ k := by
    intro v hv
    have hc : ContinuousOn (fun u => if 0 < u.im then μ u else 0) upperHalf :=
      hs₁.continuousOn.mono fun u hu => ne_of_gt hu
    have h := wr_ae_bound_on hU hc (by simpa only [Measure.restrict_univ] using hm₁.2) v hv
    have hv' : 0 < v.im := hv
    simpa only [hv', ↓reduceIte] using h
  -- uniform bounds for `∂W` at `z` and `z̄`
  have hbd : ∀ c : ℂ, c.im ≠ 0 → ∃ A : ℝ, 0 ≤ A ∧ ∀ q ∈ closedBall (0 : ℂ) R ×ˢ closedBall (0 : ℂ) R,
      ‖dz (W q) c‖ ≤ A := by
    intro c hc
    have hco : ContinuousOn (fun q : ℂ × ℂ => dz (W q) c) (closedBall (0 : ℂ) R ×ˢ closedBall (0 : ℂ) R) := by
      have h := hDc.comp (continuous_id.prodMk continuous_const).continuousOn
        (fun q hq => (⟨hsub hq, hc⟩ : (q, c) ∈ {P : ℂ × ℂ | max ‖P.1‖ ‖P.2‖ * k < 1} ×ˢ {u : ℂ | u.im ≠ 0}))
      simpa only [Function.comp_def, id] using h
    obtain ⟨A, hA⟩ := hK.exists_bound_of_continuousOn hco
    exact ⟨max A 0, le_max_right _ _, fun q hq => (hA q hq).trans (le_max_left _ _)⟩
  obtain ⟨A, hA0, hA⟩ := hbd z hzim.ne'
  obtain ⟨B, hB0, hB⟩ := hbd (conj z) (by rw [Complex.conj_im]; linarith)
  -- uniform separation
  obtain ⟨η₁, hη₁, hsep₁⟩ := e64_t5_sep hk hμk hμs hRk hW (conj z) hδ
  obtain ⟨η₂, hη₂, hsep₂⟩ := e64_t5_sep hk hμk hμs hRk hW z hzim
  set η := min η₁ η₂ with hηd
  have hη : 0 < η := lt_min hη₁ hη₂
  set Cη : ℝ := ((1 + η) / η) ^ 4 with hCη
  set I0 : ℝ := ∫ ζ : ℂ, ((1 + ‖ζ‖) ^ 4)⁻¹ with hI0
  refine ⟨k * A * B / (1 - (R * k) ^ 2) * (Cη * (I0 + I0)), fun q hq => ?_⟩
  have hR0 : 0 ≤ R := (norm_nonneg q.1).trans (by simpa using hq.1)
  have hRk0 : 0 ≤ R * k := mul_nonneg hR0 hk
  have hden : 0 < 1 - (R * k) ^ 2 := by nlinarith
  have hK0 : 0 ≤ k * A * B / (1 - (R * k) ^ 2) := by positivity
  have hqW := hsub hq
  set f := W q with hf
  set S := upperHalf \ ball z δ with hS
  have hSm : MeasurableSet S := hU.measurableSet.diff measurableSet_ball
  have hconjL : ∀ v ∈ S, (conj v).im < 0 := by
    intro v hv
    have : 0 < v.im := hv.1
    rw [Complex.conj_im]
    linarith
  have hfd : ∀ v ∈ S, DifferentiableAt ℝ f (conj v) := by
    intro v hv
    have hm : (q, conj v) ∈ {P : ℂ × ℂ | max ‖P.1‖ ‖P.2‖ * k < 1} ×ˢ {u : ℂ | u.im ≠ 0} :=
      ⟨hqW, ne_of_lt (hconjL v hv)⟩
    have h3 : ContDiffAt ℝ 3 (fun y => W q y) (conj v) :=
      ContDiffAt.comp (g := fun p : (ℂ × ℂ) × ℂ => W p.1 p.2) (conj v) (hC.contDiffAt ((hWo.prod hΩ).mem_nhds hm))
        (contDiffAt_const.prodMk contDiffAt_id)
    exact h3.differentiableAt (by norm_num)
  set h : ℂ → ℂ := fun v => f (conj v) with hh
  set h' : ℂ → ℂ →L[ℝ] ℂ := fun v => (fderiv ℝ f (conj v)).comp (Complex.conjCLE : ℂ →L[ℝ] ℂ) with hh'
  have hder : ∀ v ∈ S, HasFDerivWithinAt h (h' v) S v := fun v hv =>
    ((hfd v hv).hasFDerivAt.comp v Complex.conjCLE.hasFDerivAt).hasFDerivWithinAt
  have hinjS : InjOn h S := by
    intro x _ y _ hxy
    have := hinj q hqW hxy
    simpa using congrArg conj this
  set G2 : ℂ → ℝ := fun ζ => Cη * (((1 + ‖ζ - f z‖) ^ 4)⁻¹ + ((1 + ‖ζ - f (conj z)‖) ^ 4)⁻¹) with hG2
  have hG2i : Integrable G2 := ((e64_t5_maj (f z)).1.add (e64_t5_maj (f (conj z))).1).const_mul Cη
  have hG2v : ∫ ζ, G2 ζ = Cη * (I0 + I0) := by
    rw [hG2, integral_const_mul, integral_add (e64_t5_maj (f z)).1 (e64_t5_maj (f (conj z))).1,
      (e64_t5_maj _).2, (e64_t5_maj _).2]
  have hG2n : ∀ ζ, 0 ≤ G2 ζ := fun ζ => by positivity
  have hRi : IntegrableOn (fun v => |(h' v).det| • G2 (h v)) S :=
    (integrableOn_image_iff_integrableOn_abs_det_fderiv_smul volume hSm hder hinjS G2).mp hG2i.integrableOn
  -- the pointwise bound
  have hpt : ∀ v ∈ S, ‖Φ q v‖ ≤ k * A * B / (1 - (R * k) ^ 2) * (|(h' v).det| • G2 (h v)) := by
    intro v hv
    obtain ⟨hbel, hJ⟩ := e64_t5_beltrami hk hμk hμs hW hqW (hconjL v hv)
    have hv' : 0 < v.im := hv.1
    have hvz : δ ≤ ‖v - z‖ := by
      have := hv.2
      rw [mem_ball, dist_eq_norm, not_lt] at this
      exact this
    have hX2 : η ≤ ‖f (conj v) - f (conj z)‖ := by
      refine (min_le_left _ _).trans (hsep₁ q hq (conj v) ?_)
      rw [← map_sub, RCLike.norm_conj]
      exact hvz
    have hX1 : η ≤ ‖f (conj v) - f z‖ := by
      refine (min_le_right _ _).trans (hsep₂ q hq (conj v) ?_)
      have h1 := Complex.abs_im_le_norm (conj v - z)
      have h2 : (conj v - z).im = -v.im - z.im := by simp
      rw [h2, abs_of_neg (by linarith)] at h1
      linarith
    have hX1p : 0 < ‖f (conj v) - f z‖ := hη.trans_le hX1
    have hX2p : 0 < ‖f (conj v) - f (conj z)‖ := hη.trans_le hX2
    -- `|∂W|² ≤ J/(1 - (Rk)²)`
    have hD2 : ‖dz f (conj v)‖ ^ 2 ≤ jacobian f (conj v) / (1 - (R * k) ^ 2) := by
      have hbar : ‖dzbar f (conj v)‖ ≤ R * k * ‖dz f (conj v)‖ := by
        rw [hbel, norm_mul, norm_mul, RCLike.norm_conj, Complex.conj_conj]
        have hq2 : ‖q.2‖ ≤ R := by simpa using hq.2
        exact mul_le_mul_of_nonneg_right (mul_le_mul hq2 (hμb v hv.1) (norm_nonneg _) hR0) (norm_nonneg _)
      have hsq := pow_le_pow_left₀ (norm_nonneg _) hbar 2
      rw [le_div_iff₀ hden]
      unfold jacobian
      nlinarith
    have hinv := e64_t5_inv4 hη hX1 hX2
    have hdv : |(h' v).det| = jacobian f (conj v) := e64_t5_det hJ (hfd v hv)
    rw [hdv, smul_eq_mul]
    rw [hΦ]
    simp only [norm_mul, norm_div, norm_pow, RCLike.norm_conj]
    rw [norm_sub_rev (f z) (f (conj v))]
    set X1 := ‖f (conj v) - f z‖
    set X2 := ‖f (conj v) - f (conj z)‖
    set Dd := ‖dz f (conj v)‖
    have hma : ‖μ v‖ * ‖dz f z‖ * ‖dz f (conj z)‖ ≤ k * A * B :=
      mul_le_mul (mul_le_mul (hμb v hv.1) (hA q hq) (norm_nonneg _) hk) (hB q hq) (norm_nonneg _)
        (mul_nonneg hk hA0)
    have e : ‖μ v‖ * (‖dz f z‖ * Dd / X1 ^ 2) * (Dd * ‖dz f (conj z)‖ / X2 ^ 2) =
        (‖μ v‖ * ‖dz f z‖ * ‖dz f (conj z)‖) * Dd ^ 2 * (1 / (X1 ^ 2 * X2 ^ 2)) := by
      field_simp
    rw [e]
    calc (‖μ v‖ * ‖dz f z‖ * ‖dz f (conj z)‖) * Dd ^ 2 * (1 / (X1 ^ 2 * X2 ^ 2))
        ≤ (k * A * B) * (jacobian f (conj v) / (1 - (R * k) ^ 2)) *
            (Cη * (((1 + X1) ^ 4)⁻¹ + ((1 + X2) ^ 4)⁻¹)) := by
          refine mul_le_mul (mul_le_mul hma hD2 (by positivity) (by positivity)) hinv (by positivity)
            (mul_nonneg (by positivity) (div_nonneg hJ.le hden.le))
      _ = k * A * B / (1 - (R * k) ^ 2) * (jacobian f (conj v) * G2 (h v)) := by
          simp only [hG2, hh]
          ring
  have hcS : ContinuousOn (Φ q) S := by
    have h1 := hcΦ.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun v (hv : v ∈ S) => (⟨hq, hv.1, fun e => hv.2 (by have e' : v = z := mem_singleton_iff.mp e; rw [e']; exact mem_ball_self hδ)⟩ :
        (q, v) ∈ (closedBall (0 : ℂ) R ×ˢ closedBall (0 : ℂ) R) ×ˢ (upperHalf \ {z})))
    simpa only [Function.comp_def, id] using h1
  have hΦi : IntegrableOn (Φ q) S := by
    refine (hRi.const_mul (k * A * B / (1 - (R * k) ^ 2))).mono' (hcS.aestronglyMeasurable hSm) ?_
    filter_upwards [ae_restrict_mem hSm] with v hv
    exact hpt v hv
  refine ⟨hΦi, ?_⟩
  calc ∫ v in S, ‖Φ q v‖ ≤ ∫ v in S, k * A * B / (1 - (R * k) ^ 2) * (|(h' v).det| • G2 (h v)) :=
        setIntegral_mono_on hΦi.norm (hRi.const_mul _) hSm hpt
    _ = k * A * B / (1 - (R * k) ^ 2) * ∫ v in S, |(h' v).det| • G2 (h v) := integral_const_mul _ _
    _ = k * A * B / (1 - (R * k) ^ 2) * ∫ ζ in h '' S, G2 ζ := by
        rw [integral_image_eq_integral_abs_det_fderiv_smul volume hSm hder hinjS G2]
    _ ≤ k * A * B / (1 - (R * k) ^ 2) * ∫ ζ, G2 ζ :=
        mul_le_mul_of_nonneg_left (setIntegral_le_integral hG2i (Eventually.of_forall hG2n)) hK0
    _ = k * A * B / (1 - (R * k) ^ 2) * (Cη * (I0 + I0)) := by rw [hG2v]

/-- The torus integral is bounded by `r²` times the integral of the norm over `[0, 2π]²`. -/
theorem e64_t6_norm {F : ℂ → ℂ → ℂ} {r : ℝ} (hr : 0 < r)
    (hF : ContinuousOn (fun q : ℂ × ℂ => F q.1 q.2) (sphere (0 : ℂ) r ×ˢ sphere (0 : ℂ) r)) :
    ‖∮ a in C(0, r), ∮ b in C(0, r), F a b‖ ≤
      r ^ 2 * ∫ θ : ℝ × ℝ, ‖F (circleMap 0 r θ.1) (circleMap 0 r θ.2)‖ ∂((volume.restrict (Ioc 0 (2 * π))).prod
        (volume.restrict (Ioc 0 (2 * π)))) := by
  set ν : Measure ℝ := volume.restrict (Ioc 0 (2 * π)) with hν
  haveI : IsFiniteMeasure ν := by
    rw [hν]
    exact (isFiniteMeasure_restrict (μ := (volume : Measure ℝ)) (s := Ioc 0 (2 * π))).mpr measure_Ioc_lt_top.ne
  have h2π : (0 : ℝ) ≤ 2 * π := by positivity
  have hcm : ∀ θ : ℝ, circleMap 0 r θ ∈ sphere (0 : ℂ) r := fun θ => circleMap_mem_sphere 0 hr.le θ
  have hFc : Continuous fun θ : ℝ × ℝ => F (circleMap 0 r θ.1) (circleMap 0 r θ.2) :=
    hF.comp_continuous (((continuous_circleMap 0 r).comp continuous_fst).prodMk
      ((continuous_circleMap 0 r).comp continuous_snd)) fun θ => ⟨hcm θ.1, hcm θ.2⟩
  obtain ⟨Bd, hB⟩ := ((isCompact_sphere (0 : ℂ) r).prod (isCompact_sphere (0 : ℂ) r)).exists_bound_of_continuousOn hF
  have hint2 : Integrable (fun θ : ℝ × ℝ => ‖F (circleMap 0 r θ.1) (circleMap 0 r θ.2)‖) (ν.prod ν) := by
    refine (integrable_const Bd).mono' hFc.norm.aestronglyMeasurable (Eventually.of_forall fun θ => ?_)
    rw [Real.norm_of_nonneg (norm_nonneg _)]
    exact hB (circleMap 0 r θ.1, circleMap 0 r θ.2) ⟨hcm θ.1, hcm θ.2⟩
  have hone : ∀ G : ℂ → ℂ, ‖∮ a in C(0, r), G a‖ ≤ r * ∫ θ, ‖G (circleMap 0 r θ)‖ ∂ν := by
    intro G
    rw [circleIntegral, intervalIntegral.integral_of_le h2π]
    refine (norm_integral_le_integral_norm _).trans_eq ?_
    rw [← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun θ => ?_)
    simp only [deriv_circleMap, norm_smul, norm_mul, norm_circleMap_zero, norm_I, mul_one, abs_of_pos hr]
  have hGc : Continuous fun θ₁ => ∮ b in C(0, r), F (circleMap 0 r θ₁) b := by
    have h := e64_circ_param_cont (H := fun q => F q.1 q.2) hr hF
    exact h.comp_continuous (continuous_circleMap 0 r) hcm
  have hGi : Integrable (fun θ₁ => ‖∮ b in C(0, r), F (circleMap 0 r θ₁) b‖) ν := by
    refine (integrable_const (2 * π * r * Bd)).mono' hGc.norm.aestronglyMeasurable
      (Eventually.of_forall fun θ₁ => ?_)
    rw [Real.norm_of_nonneg (norm_nonneg _)]
    exact circleIntegral.norm_integral_le_of_norm_le_const hr.le fun b hb =>
      hB (circleMap 0 r θ₁, b) ⟨hcm θ₁, hb⟩
  calc ‖∮ a in C(0, r), ∮ b in C(0, r), F a b‖
      ≤ r * ∫ θ₁, ‖∮ b in C(0, r), F (circleMap 0 r θ₁) b‖ ∂ν := hone _
    _ ≤ r * ∫ θ₁, r * ∫ θ₂, ‖F (circleMap 0 r θ₁) (circleMap 0 r θ₂)‖ ∂ν ∂ν :=
        mul_le_mul_of_nonneg_left (integral_mono hGi (hint2.integral_prod_left.const_mul r)
          fun θ₁ => hone _) hr.le
    _ = r ^ 2 * ∫ θ : ℝ × ℝ, ‖F (circleMap 0 r θ.1) (circleMap 0 r θ.2)‖ ∂(ν.prod ν) := by
        rw [integral_prod _ hint2, integral_const_mul]
        ring

/-- **(E6) Domination.** On a smaller closed polydisc, `|Φ(P)(v)|` has an integrable majorant on `𝕌 ∖ B(z, δ)`
(Cauchy's formula on the torus of radius `R` (E2, E3, `wr_cauchy_bidisc`), Tonelli and E5). -/
theorem e64_dominate {μ : ℂ → ℂ} {k : ℝ} (hk : 0 ≤ k) (hμk : IsBeltramiCoeff μ upperHalf k)
    (hμs : ContDiffOn ℝ (⊤ : ℕ∞) μ upperHalf) {z : ℂ} (hz : z ∈ upperHalf) {r R : ℝ} (hr : 0 < r) (hrR : r < R)
    (hRk : R * k < 1)
    {W : ℂ × ℂ → ℂ → ℂ} (hW : W = fun P => normalizedSolution fun u =>
      P.1 * (if 0 < u.im then μ u else 0) + P.2 * (if u.im < 0 then conj (μ (conj u)) else 0))
    {Φ : ℂ × ℂ → ℂ → ℂ} (hΦ : Φ = fun P v => conj (μ v) *
      (dz (W P) z * dz (W P) (conj v) / (W P z - W P (conj v)) ^ 2) *
      (dz (W P) (conj v) * dz (W P) (conj z) / (W P (conj v) - W P (conj z)) ^ 2))
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ g : ℂ → ℝ, IntegrableOn g (upperHalf \ ball z δ) ∧
      ∀ P ∈ closedBall (0 : ℂ) r ×ˢ closedBall (0 : ℂ) r, ∀ v ∈ upperHalf \ ball z δ, ‖Φ P v‖ ≤ g v := by
  have hR : 0 < R := hr.trans hrR
  obtain ⟨M, hM⟩ := e64_tail_bound hk hμk hμs hz hRk hW hΦ hδ
  have hcΦ := e64_phi_cont hk hμk hμs hz hRk hW hΦ
  have hU : IsOpen upperHalf := isOpen_lt continuous_const Complex.continuous_im
  set S := upperHalf \ ball z δ with hS
  have hSm : MeasurableSet S := hU.measurableSet.diff measurableSet_ball
  have hSz : ∀ v ∈ S, v ∈ upperHalf \ {z} := fun v hv =>
    ⟨hv.1, fun e => hv.2 (by have e' : v = z := mem_singleton_iff.mp e; rw [e']; exact mem_ball_self hδ)⟩
  set ν : Measure ℝ := volume.restrict (Ioc 0 (2 * π)) with hν
  haveI : IsFiniteMeasure ν := by
    rw [hν]
    exact (isFiniteMeasure_restrict (μ := (volume : Measure ℝ)) (s := Ioc 0 (2 * π))).mpr measure_Ioc_lt_top.ne
  have hcm : ∀ θ : ℝ, circleMap 0 R θ ∈ closedBall (0 : ℂ) R := fun θ =>
    sphere_subset_closedBall (circleMap_mem_sphere 0 hR.le θ)
  set Ψ : (ℝ × ℝ) × ℂ → ℝ := fun p => ‖Φ (circleMap 0 R p.1.1, circleMap 0 R p.1.2) p.2‖ with hΨ
  have hΨc : ContinuousOn Ψ (univ ×ˢ S) := by
    have h := hcΦ.comp ((((continuous_circleMap 0 R).comp (continuous_fst.comp continuous_fst)).prodMk
      ((continuous_circleMap 0 R).comp (continuous_snd.comp continuous_fst))).prodMk continuous_snd).continuousOn
      (fun p (hp : p ∈ (univ : Set (ℝ × ℝ)) ×ˢ S) => (⟨⟨hcm p.1.1, hcm p.1.2⟩, hSz p.2 hp.2⟩ :
        ((circleMap 0 R p.1.1, circleMap 0 R p.1.2), p.2) ∈
          (closedBall (0 : ℂ) R ×ˢ closedBall (0 : ℂ) R) ×ˢ (upperHalf \ {z})))
    exact h.norm
  have hprod : (ν.prod ν).prod (volume.restrict S) =
      ((volume.prod volume).prod volume).restrict ((Ioc 0 (2 * π) ×ˢ Ioc 0 (2 * π)) ×ˢ S) := by
    rw [hν, Measure.prod_restrict, Measure.prod_restrict]
  have hΨm : AEStronglyMeasurable Ψ ((ν.prod ν).prod (volume.restrict S)) := by
    rw [hprod]
    exact (hΨc.mono (prod_mono (subset_univ _) subset_rfl)).aestronglyMeasurable
      ((measurableSet_Ioc.prod measurableSet_Ioc).prod hSm)
  have hΨi : Integrable Ψ ((ν.prod ν).prod (volume.restrict S)) := by
    refine (integrable_prod_iff hΨm).2 ⟨Eventually.of_forall fun θ => ?_, ?_⟩
    · have hq : (circleMap 0 R θ.1, circleMap 0 R θ.2) ∈ closedBall (0 : ℂ) R ×ˢ closedBall (0 : ℂ) R :=
        ⟨hcm θ.1, hcm θ.2⟩
      exact (hM _ hq).1.norm
    · refine (integrable_const M).mono' hΨm.norm.integral_prod_right' (Eventually.of_forall fun θ => ?_)
      have hq : (circleMap 0 R θ.1, circleMap 0 R θ.2) ∈ closedBall (0 : ℂ) R ×ˢ closedBall (0 : ℂ) R :=
        ⟨hcm θ.1, hcm θ.2⟩
      rw [Real.norm_of_nonneg (integral_nonneg fun v => norm_nonneg _)]
      simpa only [hΨ, norm_norm] using (hM _ hq).2
  set C : ℝ := ‖((2 * π * I)⁻¹ : ℂ) ^ 2‖ * (R ^ 2 * (1 / (R - r) ^ 2)) with hC
  refine ⟨fun v => C * ∫ θ, Ψ (θ, v) ∂(ν.prod ν), hΨi.integral_prod_right.const_mul C, fun P hP v hv => ?_⟩
  have hP1 : ‖P.1‖ ≤ r := by simpa using hP.1
  have hP2 : ‖P.2‖ ≤ r := by simpa using hP.2
  have hPin : P ∈ ball ((0, 0) : ℂ × ℂ).1 R ×ˢ ball ((0, 0) : ℂ × ℂ).2 R :=
    ⟨by simpa using hP1.trans_lt hrR, by simpa using hP2.trans_lt hrR⟩
  obtain ⟨hv1, hvz⟩ := hSz v hv
  have hcv : ContinuousOn (fun q : ℂ × ℂ => Φ q v) (closedBall ((0, 0) : ℂ × ℂ).1 R ×ˢ closedBall ((0, 0) : ℂ × ℂ).2 R) := by
    have h := hcΦ.comp (continuous_id.prodMk continuous_const).continuousOn
      (fun q hq => (⟨hq, hv1, hvz⟩ : (q, v) ∈ (closedBall (0 : ℂ) R ×ˢ closedBall (0 : ℂ) R) ×ˢ (upperHalf \ {z})))
    simpa only [Function.comp_def, id] using h
  obtain ⟨h1, h2⟩ := e64_phi_holo hk hμk hμs hz hRk hW hΦ hv1 (fun e => hvz (mem_singleton_iff.mpr e))
  have hrep := wr_cauchy_bidisc (f := fun q => Φ q v) (c := ((0, 0) : ℂ × ℂ)) hR hR hcv h1 h2 hPin
  simp only at hrep
  rw [hrep, norm_mul]
  -- the kernel bound on the torus
  have hden : ∀ a ∈ sphere (0 : ℂ) R, ∀ b ∈ sphere (0 : ℂ) R, R - r ≤ ‖a - P.1‖ ∧ R - r ≤ ‖b - P.2‖ := by
    intro a ha b hb
    have ha' : ‖a‖ = R := by simpa using ha
    have hb' : ‖b‖ = R := by simpa using hb
    constructor
    · have := norm_sub_norm_le a P.1; linarith
    · have := norm_sub_norm_le b P.2; linarith
  have hFc : ContinuousOn (fun q : ℂ × ℂ => Φ (q.1, q.2) v / ((q.1 - P.1) * (q.2 - P.2)))
      (sphere (0 : ℂ) R ×ˢ sphere (0 : ℂ) R) := by
    refine (hcv.mono (prod_mono sphere_subset_closedBall sphere_subset_closedBall)).div
      (((continuous_fst.sub continuous_const).mul (continuous_snd.sub continuous_const)).continuousOn) ?_
    intro q hq
    obtain ⟨d1, d2⟩ := hden q.1 hq.1 q.2 hq.2
    refine mul_ne_zero (fun h => ?_) (fun h => ?_)
    · rw [h, norm_zero] at d1; linarith
    · rw [h, norm_zero] at d2; linarith
  have hnorm := e64_t6_norm (F := fun a b => Φ (a, b) v / ((a - P.1) * (b - P.2))) hR hFc
  have hpt : ∀ θ : ℝ × ℝ, ‖Φ (circleMap 0 R θ.1, circleMap 0 R θ.2) v /
      ((circleMap 0 R θ.1 - P.1) * (circleMap 0 R θ.2 - P.2))‖ ≤ (1 / (R - r) ^ 2) * Ψ (θ, v) := by
    intro θ
    obtain ⟨d1, d2⟩ := hden _ (circleMap_mem_sphere 0 hR.le θ.1) _ (circleMap_mem_sphere 0 hR.le θ.2)
    have hRr : 0 < R - r := by linarith
    rw [norm_div, norm_mul, div_eq_mul_inv, mul_comm]
    refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
    rw [one_div, sq]
    exact inv_anti₀ (by positivity) (mul_le_mul d1 d2 hRr.le (norm_nonneg _))
  obtain ⟨Bv, hBv⟩ := ((isCompact_closedBall (0 : ℂ) R).prod (isCompact_closedBall (0 : ℂ) R)).exists_bound_of_continuousOn hcv
  have hΨθ : Integrable (fun θ : ℝ × ℝ => Ψ (θ, v)) (ν.prod ν) := by
    have hcont : Continuous fun θ : ℝ × ℝ => Ψ (θ, v) := by
      have := hcv.comp_continuous (((continuous_circleMap 0 R).comp continuous_fst).prodMk
        ((continuous_circleMap 0 R).comp continuous_snd)) (fun θ => ⟨hcm θ.1, hcm θ.2⟩)
      exact this.norm
    refine (integrable_const Bv).mono' hcont.aestronglyMeasurable (Eventually.of_forall fun θ => ?_)
    rw [Real.norm_of_nonneg (norm_nonneg _)]
    exact hBv _ ⟨hcm θ.1, hcm θ.2⟩
  have hmono : ∫ θ, ‖Φ (circleMap 0 R θ.1, circleMap 0 R θ.2) v /
        ((circleMap 0 R θ.1 - P.1) * (circleMap 0 R θ.2 - P.2))‖ ∂(ν.prod ν) ≤
      ∫ θ, (1 / (R - r) ^ 2) * Ψ (θ, v) ∂(ν.prod ν) :=
    integral_mono_of_nonneg (Eventually.of_forall fun θ => norm_nonneg _) (hΨθ.const_mul _)
      (Eventually.of_forall hpt)
  rw [integral_const_mul] at hmono
  beta_reduce at hnorm
  calc ‖((2 * π * I)⁻¹ : ℂ) ^ 2‖ * ‖∮ a in C(0, R), ∮ b in C(0, R), Φ (a, b) v / ((a - P.1) * (b - P.2))‖
      ≤ ‖((2 * π * I)⁻¹ : ℂ) ^ 2‖ * (R ^ 2 * ((1 / (R - r) ^ 2) * ∫ θ, Ψ (θ, v) ∂(ν.prod ν))) :=
        mul_le_mul_of_nonneg_left (hnorm.trans (mul_le_mul_of_nonneg_left hmono (by positivity))) (norm_nonneg _)
    _ = C * ∫ θ, Ψ (θ, v) ∂(ν.prod ν) := by rw [hC]; ring

/-! ### E7 helpers (下属1) -/

/-- A Beltrami bound on `univ` is nonnegative. -/
theorem e64_k_nonneg {m : ℂ → ℂ} {k : ℝ} (hm : IsBeltramiCoeff m univ k) : 0 ≤ k := by
  by_contra hneg
  push Not at hneg
  have h0 := hm.2
  rw [Measure.restrict_univ] at h0
  have hb : (volume : Measure ℂ) = 0 :=
    ae_eq_bot.mp (eventually_false_iff_eq_bot.mp (h0.mono fun u hu => by linarith [norm_nonneg (m u)]))
  exact (NeZero.ne (volume : Measure ℂ)) hb

/-- Both coefficients of `extU` are smooth off the real axis. -/
theorem e64_coeff_smooth {μ : ℂ → ℂ} (hμs : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) μ upperHalf) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun u => if 0 < u.im then μ u else 0) {u : ℂ | u.im ≠ 0} ∧
      ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun u => if u.im < 0 then conj (μ (conj u)) else 0)
        {u : ℂ | u.im ≠ 0} := by
  have hU : IsOpen upperHalf := isOpen_lt continuous_const Complex.continuous_im
  have hL : IsOpen {u : ℂ | u.im < 0} := isOpen_lt Complex.continuous_im continuous_const
  have hg : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun u => conj (μ (conj u))) {u : ℂ | u.im < 0} :=
    Complex.conjCLE.contDiff.comp_contDiffOn (hμs.comp Complex.conjCLE.contDiff.contDiffOn (fun u hu => by
      show 0 < (conj u).im
      rw [Complex.conj_im]
      have : u.im < 0 := hu
      linarith))
  constructor
  · refine contDiffOn_of_locally_contDiffOn fun x hx => ?_
    rcases (show x.im ≠ 0 from hx).lt_or_gt with h | h
    · refine ⟨{u : ℂ | u.im < 0}, hL, h, (contDiffOn_const (c := (0 : ℂ))).congr fun u hu => ?_⟩
      have : ¬ 0 < u.im := by have : u.im < 0 := hu.2; linarith
      simp only [this, ↓reduceIte]
    · refine ⟨upperHalf, hU, h, (hμs.mono inter_subset_right).congr fun u hu => ?_⟩
      have : 0 < u.im := hu.2
      simp only [this, ↓reduceIte]
  · refine contDiffOn_of_locally_contDiffOn fun x hx => ?_
    rcases (show x.im ≠ 0 from hx).lt_or_gt with h | h
    · refine ⟨{u : ℂ | u.im < 0}, hL, h, (hg.mono inter_subset_right).congr fun u hu => ?_⟩
      have : u.im < 0 := hu.2
      simp only [this, ↓reduceIte]
    · refine ⟨upperHalf, hU, h, (contDiffOn_const (c := (0 : ℂ))).congr fun u hu => ?_⟩
      have : ¬ u.im < 0 := by have : (0 : ℝ) < u.im := hu.2; linarith
      simp only [this, ↓reduceIte]

/-- Uniform Lipschitz bound in the second variable for a jointly `C¹` map, over a compact parameter set. -/
theorem e64_lip_slice {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {F : (ℂ × ℂ) × ℂ → E}
    {U : Set ((ℂ × ℂ) × ℂ)} (hU : IsOpen U) (hF : ContDiffOn ℝ 1 F U) {S : Set (ℂ × ℂ)} (hS : IsCompact S)
    {c : ℂ} {ρ : ℝ} (hSU : S ×ˢ closedBall c ρ ⊆ U) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ q ∈ S, ∀ x ∈ closedBall c ρ, ∀ y ∈ closedBall c ρ,
      ‖F (q, x) - F (q, y)‖ ≤ L * ‖x - y‖ := by
  have hK : IsCompact (S ×ˢ closedBall c ρ) := hS.prod (isCompact_closedBall c ρ)
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn ((hF.continuousOn_fderiv_of_isOpen hU le_rfl).mono hSU)
  refine ⟨max M 0, le_max_right _ _, fun q hq x hx y hy => ?_⟩
  have hd : ∀ w ∈ closedBall c ρ, HasFDerivWithinAt (fun w => F (q, w))
      ((fderiv ℝ F (q, w)).comp (ContinuousLinearMap.inr ℝ (ℂ × ℂ) ℂ)) (closedBall c ρ) w := by
    intro w hw
    have hdiff : DifferentiableAt ℝ F (q, w) :=
      (hF.differentiableOn (by norm_num) (q, w) (hSU ⟨hq, hw⟩)).differentiableAt (hU.mem_nhds (hSU ⟨hq, hw⟩))
    exact (hdiff.hasFDerivAt.comp w (hasFDerivAt_prodMk_right q w)).hasFDerivWithinAt
  have hb : ∀ w ∈ closedBall c ρ,
      ‖(fderiv ℝ F (q, w)).comp (ContinuousLinearMap.inr ℝ (ℂ × ℂ) ℂ)‖ ≤ max M 0 := by
    intro w hw
    refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
    calc _ ≤ ‖fderiv ℝ F (q, w)‖ * 1 :=
          mul_le_mul_of_nonneg_left (ContinuousLinearMap.norm_inr_le_one ℝ (ℂ × ℂ) ℂ) (norm_nonneg _)
      _ ≤ max M 0 := by rw [mul_one]; exact (hM _ ⟨hq, hw⟩).trans (le_max_left _ _)
  exact (convex_closedBall c ρ).norm_image_sub_le_of_norm_hasFDerivWithin_le hd hb hy hx

/-- Uniform second-order Taylor bound in the second variable for a jointly `C²` map. -/
theorem e64_taylor_slice {F : (ℂ × ℂ) × ℂ → ℂ} {U : Set ((ℂ × ℂ) × ℂ)} (hU : IsOpen U)
    (hF : ContDiffOn ℝ 2 F U) {S : Set (ℂ × ℂ)} (hS : IsCompact S) {c : ℂ} {ρ : ℝ}
    (hSU : S ×ˢ closedBall c ρ ⊆ U) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ q ∈ S, ∀ h : ℂ, ‖h‖ ≤ ρ →
      ‖F (q, c + h) - F (q, c) - fderiv ℝ F (q, c) (0, h)‖ ≤ L * ‖h‖ ^ 2 := by
  obtain ⟨L, hL0, hL⟩ := e64_lip_slice hU (hF.fderiv_of_isOpen hU (by norm_num)) hS hSU
  refine ⟨L, hL0, fun q hq h hh => ?_⟩
  have hs : closedBall c ‖h‖ ⊆ closedBall c ρ := closedBall_subset_closedBall hh
  have hc : c ∈ closedBall c ρ := mem_closedBall_self ((norm_nonneg h).trans hh)
  set D := (fderiv ℝ F (q, c)).comp (ContinuousLinearMap.inr ℝ (ℂ × ℂ) ℂ) with hDd
  have hder : ∀ w ∈ closedBall c ‖h‖, HasFDerivWithinAt (fun w => F (q, w) - D w)
      ((fderiv ℝ F (q, w)).comp (ContinuousLinearMap.inr ℝ (ℂ × ℂ) ℂ) - D) (closedBall c ‖h‖) w := by
    intro w hw
    have hw' := hs hw
    have hdiff : DifferentiableAt ℝ F (q, w) :=
      (hF.differentiableOn (by norm_num) (q, w) (hSU ⟨hq, hw'⟩)).differentiableAt (hU.mem_nhds (hSU ⟨hq, hw'⟩))
    exact ((hdiff.hasFDerivAt.comp w (hasFDerivAt_prodMk_right q w)).sub D.hasFDerivAt).hasFDerivWithinAt
  have hbd : ∀ w ∈ closedBall c ‖h‖,
      ‖(fderiv ℝ F (q, w)).comp (ContinuousLinearMap.inr ℝ (ℂ × ℂ) ℂ) - D‖ ≤ L * ‖h‖ := by
    intro w hw
    have e : (fderiv ℝ F (q, w)).comp (ContinuousLinearMap.inr ℝ (ℂ × ℂ) ℂ) - D =
        (fderiv ℝ F (q, w) - fderiv ℝ F (q, c)).comp (ContinuousLinearMap.inr ℝ (ℂ × ℂ) ℂ) := by
      rw [hDd, ContinuousLinearMap.sub_comp]
    rw [e]
    refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
    have h1 := hL q hq w (hs hw) c hc
    have h2 : ‖w - c‖ ≤ ‖h‖ := by rw [← dist_eq_norm]; exact hw
    calc _ ≤ ‖fderiv ℝ F (q, w) - fderiv ℝ F (q, c)‖ * 1 :=
          mul_le_mul_of_nonneg_left (ContinuousLinearMap.norm_inr_le_one ℝ (ℂ × ℂ) ℂ) (norm_nonneg _)
      _ ≤ L * ‖h‖ := by rw [mul_one]; exact h1.trans (mul_le_mul_of_nonneg_left h2 hL0)
  have hm : c + h ∈ closedBall c ‖h‖ := by
    rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left]
  have := (convex_closedBall c ‖h‖).norm_image_sub_le_of_norm_hasFDerivWithin_le hder hbd
    (mem_closedBall_self (norm_nonneg h)) hm
  rw [add_sub_cancel_left] at this
  have e2 : F (q, c + h) - F (q, c) - fderiv ℝ F (q, c) (0, h) = (F (q, c + h) - D (c + h)) - (F (q, c) - D c) := by
    have : D (c + h) - D c = fderiv ℝ F (q, c) (0, h) := by
      rw [← map_sub, add_sub_cancel_left, hDd]
      rfl
    rw [← this]
    ring
  rw [e2]
  calc _ ≤ L * ‖h‖ * ‖h‖ := this
    _ = L * ‖h‖ ^ 2 := by ring

/-- The anisotropic model estimate: `S/D² - S₀/(α \overline{h + κh̄})² = O(1/|h|)`, written with the model as
`\overline{c (h + κh̄)⁻²}`, `c = \overline{S₀/α²}`. -/
theorem e64_model_est {S S0 D α κ h : ℂ} {L1 L2 B A c0 : ℝ} (hc0 : 0 < c0) (hcα : c0 ≤ ‖α‖ * (1 - ‖κ‖))
    (hκ : ‖κ‖ < 1) (hαA : ‖α‖ ≤ A) (hL1 : 0 ≤ L1) (hL2 : 0 ≤ L2) (hB : ‖S0‖ ≤ B) (hh0 : 0 < ‖h‖)
    (h4 : L1 * ‖h‖ ≤ c0 / 2) (hE : ‖D - α * conj (h + κ * conj h)‖ ≤ L1 * ‖h‖ ^ 2)
    (hS : ‖S - S0‖ ≤ L2 * ‖h‖) :
    ‖S / D ^ 2 - conj (conj (S0 / α ^ 2) * ((h + κ * conj h) ^ 2)⁻¹)‖ ≤
      (4 * L2 / c0 ^ 2 + 20 * B * L1 * A / c0 ^ 4) / ‖h‖ := by
  set t := ‖h‖ with htd
  set X := h + κ * conj h with hXd
  set M := α * conj X with hMd
  obtain ⟨hXlo, hXhi⟩ := e124p_Lb hκ h
  have hκ1 : 0 < 1 - ‖κ‖ := by linarith
  have hαp : 0 < ‖α‖ := by
    by_contra hn
    push Not at hn
    have : ‖α‖ * (1 - ‖κ‖) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hn hκ1.le
    linarith
  have hα : α ≠ 0 := norm_pos_iff.mp hαp
  have hc0α : c0 ≤ ‖α‖ := hcα.trans (by nlinarith [norm_nonneg κ])
  have hc0A : c0 ≤ A := hc0α.trans hαA
  have hX0 : X ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le (mul_pos hκ1 hh0) hXlo)
  have hcX : conj X ≠ 0 := (map_ne_zero (starRingEnd ℂ)).mpr hX0
  have hMlo : c0 * t ≤ ‖M‖ := by
    rw [hMd, norm_mul, Complex.norm_conj]
    calc c0 * t ≤ ‖α‖ * (1 - ‖κ‖) * t := mul_le_mul_of_nonneg_right hcα hh0.le
      _ = ‖α‖ * ((1 - ‖κ‖) * t) := by ring
      _ ≤ ‖α‖ * ‖X‖ := mul_le_mul_of_nonneg_left hXlo (norm_nonneg _)
  have hMhi : ‖M‖ ≤ 2 * A * t := by
    rw [hMd, norm_mul, Complex.norm_conj]
    calc ‖α‖ * ‖X‖ ≤ A * (2 * t) := mul_le_mul hαA hXhi (norm_nonneg _) (hαp.le.trans hαA)
      _ = 2 * A * t := by ring
  have hEs : ‖D - M‖ ≤ c0 / 2 * t :=
    hE.trans (by rw [pow_two, ← mul_assoc]; exact mul_le_mul_of_nonneg_right h4 hh0.le)
  have hDlo : c0 / 2 * t ≤ ‖D‖ := by
    have := norm_sub_norm_le M D
    rw [norm_sub_rev] at this
    linarith
  have hSum : ‖M + D‖ ≤ 5 * A * t := by
    have := norm_add_le (2 * M) (D - M)
    rw [show 2 * M + (D - M) = M + D by ring, norm_mul, show ‖(2 : ℂ)‖ = 2 by norm_num] at this
    have h3 : c0 / 2 * t ≤ A * t := mul_le_mul_of_nonneg_right (by linarith) hh0.le
    linarith
  have hinv := e124p_inv_sq (e := L1 * t ^ 2) (A := 5 * A * t) hh0 hc0 hDlo hMlo
    (by rw [norm_sub_rev]; exact hE) hSum
  have hinv' : ‖1 / D ^ 2 - 1 / M ^ 2‖ ≤ 20 * L1 * A / c0 ^ 4 / t := by
    refine hinv.trans (le_of_eq ?_)
    field_simp
    ring
  have hh1 : 0 < c0 / 2 * t := mul_pos (half_pos hc0) hh0
  have hXb : ‖1 / D ^ 2‖ ≤ 1 / (c0 / 2 * t) ^ 2 := by
    rw [norm_div, norm_one, norm_pow]
    exact one_div_le_one_div_of_le (pow_pos hh1 2) (pow_le_pow_left₀ hh1.le hDlo 2)
  have hmod : conj (conj (S0 / α ^ 2) * (X ^ 2)⁻¹) = S0 * (1 / M ^ 2) := by
    simp only [map_mul, map_inv₀, map_pow, Complex.conj_conj, hMd]
    field_simp
  rw [hmod]
  have hdec : S / D ^ 2 - S0 * (1 / M ^ 2) = (S - S0) * (1 / D ^ 2) + S0 * (1 / D ^ 2 - 1 / M ^ 2) := by ring
  rw [hdec]
  have hT1 : ‖(S - S0) * (1 / D ^ 2)‖ ≤ 4 * L2 / c0 ^ 2 / t := by
    rw [norm_mul]
    calc _ ≤ (L2 * t) * (1 / (c0 / 2 * t) ^ 2) := mul_le_mul hS hXb (norm_nonneg _) (by positivity)
      _ = 4 * L2 / c0 ^ 2 / t := by field_simp; ring
  have hT2 : ‖S0 * (1 / D ^ 2 - 1 / M ^ 2)‖ ≤ 20 * B * L1 * A / c0 ^ 4 / t := by
    rw [norm_mul]
    have hB0 : 0 ≤ B := (norm_nonneg _).trans hB
    calc _ ≤ B * (20 * L1 * A / c0 ^ 4 / t) := mul_le_mul hB hinv' (norm_nonneg _) hB0
      _ = 20 * B * L1 * A / c0 ^ 4 / t := by ring
  have he : (4 * L2 / c0 ^ 2 + 20 * B * L1 * A / c0 ^ 4) / t =
      4 * L2 / c0 ^ 2 / t + 20 * B * L1 * A / c0 ^ 4 / t := by ring
  rw [he]
  exact (norm_add_le _ _).trans (add_le_add hT1 hT2)

/-- The conjugated model term has integral `0` on every annulus around `z` (`e124p_model_zero`). -/
theorem e64_conj_model_zero (c κ z : ℂ) (hκ : ‖κ‖ < 1) {δ r : ℝ} (hδ : 0 < δ) (hδr : δ ≤ r) :
    IntegrableOn (fun v => conj (c * ((v - z + κ * conj (v - z)) ^ 2)⁻¹)) (ball z r \ ball z δ) ∧
      ∫ v in ball z r \ ball z δ, conj (c * ((v - z + κ * conj (v - z)) ^ 2)⁻¹) = 0 := by
  obtain ⟨hi, h0⟩ := e124p_model_zero c κ z hκ hδ hδr
  refine ⟨?_, by rw [integral_conj, h0, map_zero]⟩
  exact (Complex.conjCLE.toContinuousLinearMap.integrable_comp hi).congr (Eventually.of_forall fun v => by simp)

/-- `∫_{B(z,δ)} |v - z|⁻¹ → 0` as `δ → 0⁺`. -/
theorem e64_ball_small (z : ℂ) :
    Tendsto (fun δ : ℝ => ∫ v in ball z δ, ‖v - z‖⁻¹) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hg := e124p_invnorm_int z 1
  have hnn : ∀ v : ℂ, 0 ≤ ‖v - z‖⁻¹ := fun v => inv_nonneg.mpr (norm_nonneg _)
  have e : ∀ δ ≤ 1, ∫ v in ball z δ, ‖v - z‖⁻¹ =
      ∫ v in ball z 1, (ball z δ).indicator (fun v => ‖v - z‖⁻¹) v := by
    intro δ hδ
    rw [setIntegral_indicator measurableSet_ball, inter_eq_right.mpr (ball_subset_ball hδ)]
  have hT : Tendsto (fun δ : ℝ => ∫ v in ball z 1, (ball z δ).indicator (fun v => ‖v - z‖⁻¹) v) (𝓝[>] 0)
      (𝓝 (∫ _v in ball z 1, (0 : ℝ))) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun v => ‖v - z‖⁻¹)
      (Eventually.of_forall fun δ => hg.aestronglyMeasurable.indicator measurableSet_ball)
      (Eventually.of_forall fun δ => Eventually.of_forall fun v => ?_) hg ?_
    · rw [Real.norm_eq_abs, abs_of_nonneg (indicator_nonneg (fun v _ => hnn v) v)]
      exact indicator_le_self' (fun v _ => hnn v) v
    · filter_upwards [ae_restrict_of_ae (compl_mem_ae_iff.mpr (measure_singleton z))] with v hv
      have hp : 0 < ‖v - z‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hv)
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [Ioo_mem_nhdsGT hp] with δ hδ
      rw [indicator_of_notMem]
      rw [mem_ball, dist_eq_norm, not_lt]
      exact hδ.2.le
  rw [integral_zero] at hT
  refine hT.congr' ?_
  filter_upwards [Ioo_mem_nhdsGT one_pos] with δ hδ
  exact (e δ hδ.2.le).symm

/-- Uniformly Cauchy truncations converge uniformly. -/
theorem e64_unif_of_cauchy {I : ℝ → ℂ × ℂ → ℂ} {s : Set (ℂ × ℂ)}
    (h : ∀ η > 0, ∃ δ₁ > 0, ∀ δ ∈ Ioo 0 δ₁, ∀ δ' ∈ Ioo 0 δ₁, ∀ q ∈ s, ‖I δ q - I δ' q‖ ≤ η) :
    ∃ L : ℂ × ℂ → ℂ, TendstoUniformlyOn I L (𝓝[>] (0 : ℝ)) s := by
  have hU : UniformCauchySeqOn I (𝓝[>] (0 : ℝ)) s := by
    intro u hu
    obtain ⟨η, hη, hηu⟩ := Metric.mem_uniformity_dist.mp hu
    obtain ⟨δ₁, hδ₁, hc⟩ := h (η / 2) (half_pos hη)
    have hm : Ioo 0 δ₁ ×ˢ Ioo 0 δ₁ ∈ 𝓝[>] (0 : ℝ) ×ˢ 𝓝[>] (0 : ℝ) :=
      prod_mem_prod (Ioo_mem_nhdsGT hδ₁) (Ioo_mem_nhdsGT hδ₁)
    filter_upwards [hm] with m hm' q hq
    apply hηu
    rw [dist_eq_norm]
    exact (hc _ hm'.1 _ hm'.2 q hq).trans_lt (half_lt_self hη)
  refine ⟨fun q => limUnder (𝓝[>] (0 : ℝ)) (fun δ => I δ q), hU.tendstoUniformlyOn_of_tendsto fun q hq => ?_⟩
  obtain ⟨y, hy⟩ := CompleteSpace.complete (hU.cauchy_map hq)
  exact tendsto_nhds_limUnder ⟨y, hy⟩

/-- One truncation step: `|I_{δ'} - I_δ| ≤ C ∫_{B(z,δ)} |v - z|⁻¹` once the integrand is the conjugated model up to
`C/|h|` on `B(z, ρ)`. -/
theorem e64_annulus_est {F : ℂ → ℂ} {z c κ : ℂ} (hκ : ‖κ‖ < 1) {ρ C δ δ' : ℝ} (hC : 0 ≤ C)
    (hball : ball z ρ ⊆ upperHalf) (hδ' : 0 < δ') (hδδ : δ' ≤ δ) (hδρ : δ ≤ ρ)
    (hI : IntegrableOn F (upperHalf \ ball z δ'))
    (hloc : ∀ h : ℂ, 0 < ‖h‖ → ‖h‖ < ρ → ‖F (z + h) - conj (c * ((h + κ * conj h) ^ 2)⁻¹)‖ ≤ C / ‖h‖) :
    ‖(∫ v in upperHalf \ ball z δ', F v) - ∫ v in upperHalf \ ball z δ, F v‖ ≤
      C * ∫ v in ball z δ, ‖v - z‖⁻¹ := by
  have hA : MeasurableSet (ball z δ \ ball z δ') := measurableSet_ball.diff measurableSet_ball
  have hsplit : upperHalf \ ball z δ' = (upperHalf \ ball z δ) ∪ (ball z δ \ ball z δ') := by
    ext v
    constructor
    · rintro ⟨hvU, hvδ⟩
      by_cases hvr : v ∈ ball z δ
      · exact Or.inr ⟨hvr, hvδ⟩
      · exact Or.inl ⟨hvU, hvr⟩
    · rintro (⟨hvU, hvr⟩ | ⟨hvr, hvδ⟩)
      · exact ⟨hvU, fun h => hvr (ball_subset_ball hδδ h)⟩
      · exact ⟨hball (ball_subset_ball hδρ hvr), hvδ⟩
  have hdisj : Disjoint (upperHalf \ ball z δ) (ball z δ \ ball z δ') :=
    disjoint_left.mpr fun v h1 h2 => h1.2 h2.1
  rw [hsplit] at hI
  rw [hsplit, setIntegral_union hdisj hA (hI.mono_set subset_union_left) (hI.mono_set subset_union_right),
    add_sub_cancel_left]
  obtain ⟨hmi, hm0⟩ := e64_conj_model_zero c κ z hκ hδ' hδδ
  have hFA : IntegrableOn F (ball z δ \ ball z δ') := hI.mono_set subset_union_right
  have e1 : ∫ v in ball z δ \ ball z δ', F v =
      ∫ v in ball z δ \ ball z δ', (F v - conj (c * ((v - z + κ * conj (v - z)) ^ 2)⁻¹)) := by
    rw [integral_sub hFA hmi, hm0, sub_zero]
  rw [e1]
  have hgb : IntegrableOn (fun v => C * ‖v - z‖⁻¹) (ball z δ) := (e124p_invnorm_int z δ).const_mul C
  calc _ ≤ ∫ v in ball z δ \ ball z δ', C * ‖v - z‖⁻¹ := by
        refine norm_integral_le_of_norm_le (hgb.mono_set sdiff_subset) ?_
        filter_upwards [ae_restrict_mem hA] with v hv
        have hvδ : ‖v - z‖ < δ := by have := hv.1; rwa [mem_ball, dist_eq_norm] at this
        have hvδ' : δ' ≤ ‖v - z‖ := by have := hv.2; rwa [mem_ball, dist_eq_norm, not_lt] at this
        have := hloc (v - z) (hδ'.trans_le hvδ') (hvδ.trans_le hδρ)
        rw [add_sub_cancel] at this
        rw [← div_eq_mul_inv]
        exact this
    _ ≤ ∫ v in ball z δ, C * ‖v - z‖⁻¹ :=
        setIntegral_mono_set hgb (Eventually.of_forall fun v => mul_nonneg hC (inv_nonneg.mpr (norm_nonneg _)))
          sdiff_subset.eventuallyLE
    _ = C * ∫ v in ball z δ, ‖v - z‖⁻¹ := integral_const_mul C _

/-- The local anisotropic expansion of `Φ(q)` at `v = z`, with constants uniform over the closed polydisc
(W-REG D2 joint `C³` on `{Im ≠ 0}`, `wr_local_jacobian_pos`, compactness). -/
theorem e64_local_unif {μ : ℂ → ℂ} {k : ℝ} (hk : 0 ≤ k) (hμk : IsBeltramiCoeff μ upperHalf k)
    (hμs : ContDiffOn ℝ (⊤ : ℕ∞) μ upperHalf) {z : ℂ} (hz : z ∈ upperHalf) {r : ℝ} (hrk : r * k < 1)
    {W : ℂ × ℂ → ℂ → ℂ} (hW : W = fun P => normalizedSolution fun u =>
      P.1 * (if 0 < u.im then μ u else 0) + P.2 * (if u.im < 0 then conj (μ (conj u)) else 0))
    {Φ : ℂ × ℂ → ℂ → ℂ} (hΦ : Φ = fun P v => conj (μ v) *
      (dz (W P) z * dz (W P) (conj v) / (W P z - W P (conj v)) ^ 2) *
      (dz (W P) (conj v) * dz (W P) (conj z) / (W P (conj v) - W P (conj z)) ^ 2)) :
    ∃ ρ > 0, ∃ C : ℝ, 0 ≤ C ∧ ball z ρ ⊆ upperHalf ∧ ∀ q ∈ closedBall (0 : ℂ) r ×ˢ closedBall (0 : ℂ) r,
      ∃ c κ : ℂ, ‖κ‖ < 1 ∧ ∀ h : ℂ, 0 < ‖h‖ → ‖h‖ < ρ →
        ‖Φ q (z + h) - conj (c * ((h + κ * conj h) ^ 2)⁻¹)‖ ≤ C / ‖h‖ := by
  have hμs' : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) μ upperHalf := hμs
  have hzim : 0 < z.im := hz
  have hρ₀p : 0 < z.im / 2 := half_pos hzim
  have hB0 : closedBall z (z.im / 2) ⊆ upperHalf := fun v hv => by
    show 0 < v.im
    have h1 : |v.im - z.im| ≤ ‖v - z‖ := by rw [← Complex.sub_im]; exact Complex.abs_im_le_norm _
    rw [mem_closedBall, dist_eq_norm] at hv
    have := (abs_le.mp (h1.trans hv)).1
    linarith
  have hBL : closedBall (conj z) (z.im / 2) ⊆ {u : ℂ | u.im ≠ 0} := fun v hv => by
    show v.im ≠ 0
    have h1 : |v.im - (conj z).im| ≤ ‖v - conj z‖ := by rw [← Complex.sub_im]; exact Complex.abs_im_le_norm _
    rw [mem_closedBall, dist_eq_norm] at hv
    have := (abs_le.mp (h1.trans hv)).2
    rw [Complex.conj_im] at this
    linarith
  rcases lt_or_ge r 0 with hr | hr
  · refine ⟨z.im / 2, hρ₀p, 0, le_rfl, ball_subset_closedBall.trans hB0, fun q hq => ?_⟩
    exact absurd (dist_nonneg.trans (mem_closedBall.mp hq.1)) (not_le.mpr hr)
  obtain ⟨hm₁, hm₂, -, -, hcomb⟩ := wr_U_coeffs hk hμk hμs'
  obtain ⟨hs₁, hs₂⟩ := e64_coeff_smooth hμs'
  have hΩ : IsOpen {u : ℂ | u.im ≠ 0} := isOpen_ne_fun Complex.continuous_im continuous_const
  have hUo : IsOpen upperHalf := isOpen_lt continuous_const Complex.continuous_im
  have hWo : IsOpen {P : ℂ × ℂ | max ‖P.1‖ ‖P.2‖ * k < 1} :=
    isOpen_lt (((continuous_norm.comp continuous_fst).max (continuous_norm.comp continuous_snd)).mul
      continuous_const) continuous_const
  have hD := wr_local_joint_contDiff hm₁ hm₂ hΩ hs₁ hs₂ hWo (fun P hP => hcomb P.1 P.2 hP)
  set Wset : Set (ℂ × ℂ) := {P : ℂ × ℂ | max ‖P.1‖ ‖P.2‖ * k < 1} with hWsetd
  set Ω : Set ℂ := {u : ℂ | u.im ≠ 0} with hΩd
  obtain ⟨F, hFd⟩ : ∃ F : (ℂ × ℂ) × ℂ → ℂ, F = fun p => W p.1 p.2 := ⟨_, rfl⟩
  have hWF : ∀ q y, W q y = F (q, y) := fun q y => by rw [hFd]
  have hF3 : ContDiffOn ℝ 3 F (Wset ×ˢ Ω) := by rw [hFd, hW]; exact hD
  have hU3 : IsOpen (Wset ×ˢ Ω) := hWo.prod hΩ
  have hKc : IsCompact (closedBall (0 : ℂ) r ×ˢ closedBall (0 : ℂ) r) :=
    (isCompact_closedBall 0 r).prod (isCompact_closedBall 0 r)
  have hKW : closedBall (0 : ℂ) r ×ˢ closedBall (0 : ℂ) r ⊆ Wset := fun q hq => by
    show max ‖q.1‖ ‖q.2‖ * k < 1
    have h1 : ‖q.1‖ ≤ r := by simpa using hq.1
    have h2 : ‖q.2‖ ≤ r := by simpa using hq.2
    calc max ‖q.1‖ ‖q.2‖ * k ≤ r * k := mul_le_mul_of_nonneg_right (max_le h1 h2) hk
      _ < 1 := hrk
  have hzΩ : z ∈ Ω := hzim.ne'
  have hczΩ : conj z ∈ Ω := by show (conj z).im ≠ 0; rw [Complex.conj_im]; exact neg_ne_zero.mpr hzim.ne'
  have hcvΩ : ∀ v ∈ upperHalf, conj v ∈ Ω := fun v hv => by
    show (conj v).im ≠ 0
    rw [Complex.conj_im]
    exact neg_ne_zero.mpr (show (0 : ℝ) < v.im from hv).ne'
  -- injectivity
  have hinj : ∀ q ∈ Wset, Function.Injective (W q) := by
    intro q hq
    obtain ⟨k', hk', hb⟩ := hcomb q.1 q.2 hq
    obtain ⟨⟨K, hK⟩, hs, -⟩ := QCV.qcv_ns_spec (e64_k_nonneg hb) hk' hb
    obtain ⟨e, he⟩ := t1_homeomorph hK hs
    rw [hW]
    beta_reduce
    rw [← he]
    exact e.injective
  -- the Wirtinger derivatives as joint functions
  obtain ⟨Gd, hGd⟩ : ∃ G : (ℂ × ℂ) × ℂ → ℂ,
      G = fun p => (fderiv ℝ F p (0, 1) - I * fderiv ℝ F p (0, I)) / 2 := ⟨_, rfl⟩
  obtain ⟨Gb, hGb⟩ : ∃ G : (ℂ × ℂ) × ℂ → ℂ,
      G = fun p => (fderiv ℝ F p (0, 1) + I * fderiv ℝ F p (0, I)) / 2 := ⟨_, rfl⟩
  have hF' : ContDiffOn ℝ 2 (fderiv ℝ F) (Wset ×ˢ Ω) := hF3.fderiv_of_isOpen hU3 (by norm_num)
  have hGd2 : ContDiffOn ℝ 2 Gd (Wset ×ˢ Ω) := by
    rw [hGd]
    exact ((hF'.clm_apply contDiffOn_const).sub (contDiffOn_const.mul (hF'.clm_apply contDiffOn_const))).div_const 2
  have hGb2 : ContDiffOn ℝ 2 Gb (Wset ×ˢ Ω) := by
    rw [hGb]
    exact ((hF'.clm_apply contDiffOn_const).add (contDiffOn_const.mul (hF'.clm_apply contDiffOn_const))).div_const 2
  have hsl : ∀ q y, (q, y) ∈ Wset ×ˢ Ω →
      fderiv ℝ (W q) y = (fderiv ℝ F (q, y)).comp (ContinuousLinearMap.inr ℝ (ℂ × ℂ) ℂ) := by
    intro q y hp
    have hdF : DifferentiableAt ℝ F (q, y) :=
      (hF3.differentiableOn (by norm_num) (q, y) hp).differentiableAt (hU3.mem_nhds hp)
    have e1 : W q = fun y => F (q, y) := funext fun y => hWF q y
    rw [e1]
    exact (hdF.hasFDerivAt.comp y (hasFDerivAt_prodMk_right q y)).fderiv
  have hdz : ∀ q y, (q, y) ∈ Wset ×ˢ Ω → dz (W q) y = Gd (q, y) := by
    intro q y hp
    rw [hGd]
    show (fderiv ℝ (W q) y 1 - I * fderiv ℝ (W q) y I) / 2 = _
    rw [hsl q y hp]
    rfl
  have hdzb : ∀ q y, (q, y) ∈ Wset ×ˢ Ω → dzbar (W q) y = Gb (q, y) := by
    intro q y hp
    rw [hGb]
    show (fderiv ℝ (W q) y 1 + I * fderiv ℝ (W q) y I) / 2 = _
    rw [hsl q y hp]
    rfl
  -- the regular part `S`
  have hc : ContDiff ℝ 1 (fun u : ℂ => conj u) := Complex.conjCLE.contDiff
  obtain ⟨Sj, hSjd⟩ : ∃ S : (ℂ × ℂ) × ℂ → ℂ, S = fun p => conj (μ p.2) *
      (Gd (p.1, z) * Gd (p.1, conj p.2) / (F (p.1, z) - F (p.1, conj p.2)) ^ 2) * Gd (p.1, conj p.2) *
        Gd (p.1, conj z) := ⟨_, rfl⟩
  have hVo : IsOpen (Wset ×ˢ upperHalf) := hWo.prod hUo
  have hm1 : MapsTo (fun p : (ℂ × ℂ) × ℂ => (p.1, z)) (Wset ×ˢ upperHalf) (Wset ×ˢ Ω) :=
    fun p hp => ⟨hp.1, hzΩ⟩
  have hm2 : MapsTo (fun p : (ℂ × ℂ) × ℂ => (p.1, conj p.2)) (Wset ×ˢ upperHalf) (Wset ×ˢ Ω) :=
    fun p hp => ⟨hp.1, hcvΩ p.2 hp.2⟩
  have hm3 : MapsTo (fun p : (ℂ × ℂ) × ℂ => (p.1, conj z)) (Wset ×ˢ upperHalf) (Wset ×ˢ Ω) :=
    fun p hp => ⟨hp.1, hczΩ⟩
  have hφ1 : ContDiff ℝ 1 (fun p : (ℂ × ℂ) × ℂ => (p.1, z)) := contDiff_fst.prodMk contDiff_const
  have hφ2 : ContDiff ℝ 1 (fun p : (ℂ × ℂ) × ℂ => (p.1, conj p.2)) := contDiff_fst.prodMk (hc.comp contDiff_snd)
  have hφ3 : ContDiff ℝ 1 (fun p : (ℂ × ℂ) × ℂ => (p.1, conj z)) := contDiff_fst.prodMk contDiff_const
  have hGd1 : ContDiffOn ℝ 1 Gd (Wset ×ˢ Ω) := hGd2.of_le (by norm_num)
  have hF1 : ContDiffOn ℝ 1 F (Wset ×ˢ Ω) := hF3.of_le (by norm_num)
  have hne : ∀ p ∈ Wset ×ˢ upperHalf, F (p.1, z) - F (p.1, conj p.2) ≠ 0 := by
    intro p hp heq
    rw [← hWF, ← hWF, sub_eq_zero] at heq
    have := congrArg Complex.im (hinj p.1 hp.1 heq)
    rw [Complex.conj_im] at this
    have h2 : (0 : ℝ) < p.2.im := hp.2
    linarith
  have hSj : ContDiffOn ℝ 1 Sj (Wset ×ˢ upperHalf) := by
    have hμc : ContDiffOn ℝ 1 (fun p : (ℂ × ℂ) × ℂ => conj (μ p.2)) (Wset ×ˢ upperHalf) :=
      hc.comp_contDiffOn ((hμs'.of_le (by exact_mod_cast le_top)).comp contDiff_snd.contDiffOn
        (fun p hp => hp.2))
    have hA1 := hGd1.comp hφ1.contDiffOn hm1
    have hA2 := hGd1.comp hφ2.contDiffOn hm2
    have hA3 := hGd1.comp hφ3.contDiffOn hm3
    have hF1' := hF1.comp hφ1.contDiffOn hm1
    have hF2' := hF1.comp hφ2.contDiffOn hm2
    rw [hSjd]
    refine (((hμc.mul ((hA1.mul hA2).mul (((hF1'.sub hF2').pow 2).inv (fun p hp => pow_ne_zero 2 (hne p hp))))).mul
      hA2).mul hA3).congr fun p _ => ?_
    simp only [Pi.inv_apply, Function.comp_apply, div_eq_mul_inv]
  have hΦS : ∀ q ∈ Wset, ∀ v ∈ upperHalf,
      Φ q v = Sj (q, v) / (F (q, conj v) - F (q, conj z)) ^ 2 := by
    intro q hq v hv
    rw [hΦ]
    beta_reduce
    rw [hdz q z ⟨hq, hzΩ⟩, hdz q (conj v) ⟨hq, hcvΩ v hv⟩, hdz q (conj z) ⟨hq, hczΩ⟩, hWF q z, hWF q (conj v),
      hWF q (conj z), hSjd]
    ring
  -- uniform constants
  obtain ⟨L2, hL20, hL2⟩ := e64_lip_slice hVo hSj hKc (c := z) (ρ := z.im / 2) (prod_mono hKW hB0)
  obtain ⟨L1, hL10, hL1⟩ := e64_taylor_slice hU3 (hF3.of_le (by norm_num)) hKc (c := conj z) (ρ := z.im / 2)
    (prod_mono hKW hBL)
  have hSc : ContinuousOn (fun q => Sj (q, z)) (closedBall (0 : ℂ) r ×ˢ closedBall (0 : ℂ) r) :=
    hSj.continuousOn.comp (continuous_id.prodMk continuous_const).continuousOn (fun q hq => ⟨hKW hq, hz⟩)
  have hαc : ContinuousOn (fun q => Gd (q, conj z)) (closedBall (0 : ℂ) r ×ˢ closedBall (0 : ℂ) r) :=
    hGd2.continuousOn.comp (continuous_id.prodMk continuous_const).continuousOn (fun q hq => ⟨hKW hq, hczΩ⟩)
  have hβc : ContinuousOn (fun q => Gb (q, conj z)) (closedBall (0 : ℂ) r ×ˢ closedBall (0 : ℂ) r) :=
    hGb2.continuousOn.comp (continuous_id.prodMk continuous_const).continuousOn (fun q hq => ⟨hKW hq, hczΩ⟩)
  obtain ⟨B, hB⟩ := hKc.exists_bound_of_continuousOn hSc
  obtain ⟨A, hA⟩ := hKc.exists_bound_of_continuousOn hαc
  have hJ : ∀ q ∈ closedBall (0 : ℂ) r ×ˢ closedBall (0 : ℂ) r, ‖Gb (q, conj z)‖ < ‖Gd (q, conj z)‖ := by
    intro q hq
    have h := wr_local_jacobian_pos hm₁ hm₂ hΩ hs₁ hs₂ (hcomb q.1 q.2 (hKW hq)) hczΩ
    have e : (normalizedSolution fun u => q.1 * (if 0 < u.im then μ u else 0) +
        q.2 * (if u.im < 0 then conj (μ (conj u)) else 0)) = W q := by rw [hW]
    rw [e, hdz q (conj z) ⟨hKW hq, hczΩ⟩, hdzb q (conj z) ⟨hKW hq, hczΩ⟩] at h
    exact lt_of_pow_lt_pow_left₀ 2 (norm_nonneg _) (by linarith)
  have hKne : (closedBall (0 : ℂ) r ×ˢ closedBall (0 : ℂ) r).Nonempty :=
    ⟨(0, 0), mem_closedBall_self hr, mem_closedBall_self hr⟩
  have hαne : ∀ q ∈ closedBall (0 : ℂ) r ×ˢ closedBall (0 : ℂ) r, ‖Gd (q, conj z)‖ ≠ 0 := fun q hq =>
    ((norm_nonneg _).trans_lt (hJ q hq)).ne'
  obtain ⟨q₁, hq₁, hmin⟩ := hKc.exists_isMinOn hKne hαc.norm
  obtain ⟨q₂, hq₂, hmax⟩ := hKc.exists_isMaxOn hKne (hβc.norm.div hαc.norm hαne)
  set a0 := ‖Gd (q₁, conj z)‖ with ha0d
  set κ0 := ‖Gb (q₂, conj z)‖ / ‖Gd (q₂, conj z)‖ with hκ0d
  have ha0 : 0 < a0 := (norm_nonneg _).trans_lt (hJ q₁ hq₁)
  have hκ0 : κ0 < 1 := (div_lt_one ((norm_nonneg _).trans_lt (hJ q₂ hq₂))).mpr (hJ q₂ hq₂)
  set c0 := a0 * (1 - κ0) with hc0d
  have hc0 : 0 < c0 := mul_pos ha0 (by linarith)
  have hB0' : 0 ≤ B := (norm_nonneg _).trans (hB q₁ hq₁)
  have hA0 : 0 ≤ A := (norm_nonneg _).trans (hA q₁ hq₁)
  refine ⟨min (z.im / 2) (c0 / (2 * (L1 + 1))), lt_min hρ₀p (by positivity),
    4 * L2 / c0 ^ 2 + 20 * B * L1 * A / c0 ^ 4, by positivity,
    (ball_subset_ball (min_le_left _ _)).trans (ball_subset_closedBall.trans hB0), fun q hq => ?_⟩
  have hαβ := hJ q hq
  have hαp : 0 < ‖Gd (q, conj z)‖ := (norm_nonneg _).trans_lt hαβ
  have hα0 : Gd (q, conj z) ≠ 0 := norm_pos_iff.mp hαp
  have hκn : ‖conj (Gb (q, conj z) / Gd (q, conj z))‖ = ‖Gb (q, conj z)‖ / ‖Gd (q, conj z)‖ := by
    rw [Complex.norm_conj, norm_div]
  refine ⟨conj (Sj (q, z) / Gd (q, conj z) ^ 2), conj (Gb (q, conj z) / Gd (q, conj z)), ?_, fun h hh0 hhρ => ?_⟩
  · rw [hκn]; exact (div_lt_one hαp).mpr hαβ
  have hh₀ : ‖h‖ < z.im / 2 := hhρ.trans_le (min_le_left _ _)
  have hh4 : L1 * ‖h‖ ≤ c0 / 2 := by
    have h5 : ‖h‖ ≤ c0 / (2 * (L1 + 1)) := hhρ.le.trans (min_le_right _ _)
    have h6 : (L1 + 1) * ‖h‖ ≤ c0 / 2 := by
      rw [le_div_iff₀ (by positivity : (0 : ℝ) < 2 * (L1 + 1))] at h5
      linarith
    nlinarith [norm_nonneg h]
  have hzh : z + h ∈ upperHalf := hB0 (by rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left]; exact hh₀.le)
  -- Taylor at `z̄`
  have hT := hL1 q hq (conj h) (by rw [Complex.norm_conj]; exact hh₀.le)
  rw [Complex.norm_conj] at hT
  have hlin : fderiv ℝ F (q, conj z) (0, conj h) = Gd (q, conj z) * conj h + Gb (q, conj z) * h := by
    calc fderiv ℝ F (q, conj z) (0, conj h) = fderiv ℝ (W q) (conj z) (conj h) := by
          rw [hsl q (conj z) ⟨hKW hq, hczΩ⟩]; rfl
      _ = dz (W q) (conj z) * conj h + dzbar (W q) (conj z) * h := by
          have e2 := e124p_wirt (fderiv ℝ (W q) (conj z)) (conj h)
          rw [Complex.conj_conj] at e2
          exact e2
      _ = Gd (q, conj z) * conj h + Gb (q, conj z) * h := by
          rw [hdz q (conj z) ⟨hKW hq, hczΩ⟩, hdzb q (conj z) ⟨hKW hq, hczΩ⟩]
  have hmodl : Gd (q, conj z) * conj (h + conj (Gb (q, conj z) / Gd (q, conj z)) * conj h) =
      Gd (q, conj z) * conj h + Gb (q, conj z) * h := by
    rw [map_add, map_mul, Complex.conj_conj, Complex.conj_conj]
    field_simp
  have hE : ‖(F (q, conj (z + h)) - F (q, conj z)) - Gd (q, conj z) *
      conj (h + conj (Gb (q, conj z) / Gd (q, conj z)) * conj h)‖ ≤ L1 * ‖h‖ ^ 2 := by
    rw [hmodl, ← hlin, map_add]
    exact hT
  have hS := hL2 q hq (z + h) (by rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left]; exact hh₀.le) z
    (mem_closedBall_self hρ₀p.le)
  rw [add_sub_cancel_left] at hS
  have hcα : c0 ≤ ‖Gd (q, conj z)‖ * (1 - ‖conj (Gb (q, conj z) / Gd (q, conj z))‖) := by
    rw [hκn]
    have h1 : a0 ≤ ‖Gd (q, conj z)‖ := hmin hq
    have h2 : ‖Gb (q, conj z)‖ / ‖Gd (q, conj z)‖ ≤ κ0 := hmax hq
    rw [hc0d]
    exact mul_le_mul h1 (by linarith) (by linarith) (norm_nonneg _)
  rw [hΦS q (hKW hq) (z + h) hzh]
  exact e64_model_est hc0 hcα (by rw [hκn]; exact (div_lt_one hαp).mpr hαβ) (hA q hq) hL10 hL20 (hB q hq) hh0 hh4
    hE hS

/-- **(E7) Parametric principal value** (the W-PVPARAM lemma). The truncated integrals of `Φ(q)` converge as
`δ → 0⁺`, uniformly over the closed polydisc.

Paper proof. Put `y₀ = z̄ ∈ 𝕃`, `h = v - z`, `α_q = (W_q)_y(y₀)`, `β_q = (W_q)_ȳ(y₀)`. On the compact set
`D̄_r × B̄(y₀, ρ₀)` (`B̄(y₀, ρ₀) ⊂ 𝕃`) `W` is jointly `C³` (W-REG D2), so uniformly in `q`:
`|W_q(y₀ + h̄) - W_q(y₀) - (α_q h̄ + β_q h)| ≤ C|h|²`, `|α_q| ≥ a₀ > 0`, `|β_q| ≤ κ₀|α_q|` with `κ₀ < 1`
(`J > 0`, `wr_local_jacobian_pos`, and compactness), and `Φ(q)(v) = S_q(v)/(W_q(v̄) - W_q(y₀))²` with `S_q` jointly
`C¹`. Hence, for `0 < |h| < ρ₁`,
`|Φ(q)(v) - S_q(z) α_q⁻² \overline{((h + κ_q h̄)²)⁻¹}| ≤ C'/|h|`, `κ_q = \overline{β_q/α_q}`, `|κ_q| ≤ κ₀`
(`α h̄ + β h = α \overline{h + κ h̄}`). The model term has integral `0` on every annulus around `z`
(`e124p_model_zero`, conjugated): the circle averages of `(h + κh̄)⁻²` vanish because only the Fourier modes
`e^{-2i(1+j)θ}`, `j ≥ 0`, occur when `|κ| < 1`. So for `δ' < δ ≤ ρ₁`,
`|I_{δ'}(q) - I_δ(q)| ≤ ∫_{B(z,δ)} C'/|h| = 2πC'δ`, uniformly in `q`. -/
theorem e64_param_pv {μ : ℂ → ℂ} {k : ℝ} (hk : 0 ≤ k) (hμk : IsBeltramiCoeff μ upperHalf k)
    (hμs : ContDiffOn ℝ (⊤ : ℕ∞) μ upperHalf) {z : ℂ} (hz : z ∈ upperHalf) {r : ℝ} (hrk : r * k < 1)
    {W : ℂ × ℂ → ℂ → ℂ} (hW : W = fun P => normalizedSolution fun u =>
      P.1 * (if 0 < u.im then μ u else 0) + P.2 * (if u.im < 0 then conj (μ (conj u)) else 0))
    {Φ : ℂ × ℂ → ℂ → ℂ} (hΦ : Φ = fun P v => conj (μ v) *
      (dz (W P) z * dz (W P) (conj v) / (W P z - W P (conj v)) ^ 2) *
      (dz (W P) (conj v) * dz (W P) (conj z) / (W P (conj v) - W P (conj z)) ^ 2)) :
    ∃ L : ℂ × ℂ → ℂ, TendstoUniformlyOn (fun δ : ℝ => fun q => ∫ v in upperHalf \ ball z δ, Φ q v) L
      (𝓝[>] (0 : ℝ)) (closedBall (0 : ℂ) r ×ˢ closedBall (0 : ℂ) r) := by
  obtain ⟨ρ, hρ, C, hC, hball, hloc⟩ := e64_local_unif hk hμk hμs hz hrk hW hΦ
  apply e64_unif_of_cauchy
  intro η hη
  have hT := (tendsto_const_nhds (x := C)).mul (e64_ball_small z)
  rw [mul_zero] at hT
  obtain ⟨δ₁, hδ₁e, hδ₁p⟩ := ((hT.eventually (gt_mem_nhds hη)).and (Ioo_mem_nhdsGT hρ)).exists
  refine ⟨δ₁, hδ₁p.1, fun δ hδ δ' hδ' q hq => ?_⟩
  have key : ∀ a b : ℝ, 0 < a → a ≤ b → b < δ₁ →
      ‖(∫ v in upperHalf \ ball z a, Φ q v) - ∫ v in upperHalf \ ball z b, Φ q v‖ ≤ η := by
    intro a b ha hab hb
    obtain ⟨c, κ, hκ, hl⟩ := hloc q hq
    obtain ⟨M, hM⟩ := e64_tail_bound hk hμk hμs hz hrk hW hΦ ha
    have h1 := e64_annulus_est hκ hC hball ha hab (hb.le.trans hδ₁p.2.le) (hM q hq).1 hl
    have h2 : ∫ v in ball z b, ‖v - z‖⁻¹ ≤ ∫ v in ball z δ₁, ‖v - z‖⁻¹ :=
      setIntegral_mono_set (e124p_invnorm_int z δ₁)
        (Eventually.of_forall fun v => inv_nonneg.mpr (norm_nonneg _)) (ball_subset_ball hb.le).eventuallyLE
    exact h1.trans ((mul_le_mul_of_nonneg_left h2 hC).trans hδ₁e.le)
  rcases le_total δ δ' with h | h
  · exact key δ δ' hδ.1 h hδ'.2
  · rw [norm_sub_rev]; exact key δ' δ hδ'.1 h hδ.2

/-! ### The `ε`-derivative of the principal value -/

/-- The double circle integral is subtractive on functions continuous on the torus. -/
theorem e64_torus_sub {H₁ H₂ : ℂ → ℂ → ℂ} {r : ℝ} (hr : 0 < r)
    (h₁ : ContinuousOn (fun q : ℂ × ℂ => H₁ q.1 q.2) (sphere (0 : ℂ) r ×ˢ sphere (0 : ℂ) r))
    (h₂ : ContinuousOn (fun q : ℂ × ℂ => H₂ q.1 q.2) (sphere (0 : ℂ) r ×ˢ sphere (0 : ℂ) r)) :
    (∮ a in C(0, r), ∮ b in C(0, r), (H₁ a b - H₂ a b)) =
      (∮ a in C(0, r), ∮ b in C(0, r), H₁ a b) - ∮ a in C(0, r), ∮ b in C(0, r), H₂ a b := by
  have hin : ∀ {H : ℂ → ℂ → ℂ}, ContinuousOn (fun q : ℂ × ℂ => H q.1 q.2) (sphere (0 : ℂ) r ×ˢ sphere (0 : ℂ) r) →
      ∀ a ∈ sphere (0 : ℂ) r, CircleIntegrable (fun b => H a b) 0 r := by
    intro H hH a ha
    refine ContinuousOn.circleIntegrable hr.le ?_
    exact hH.comp (continuous_const.prodMk continuous_id).continuousOn fun b hb => ⟨ha, hb⟩
  have hc : EqOn (fun a => ∮ b in C(0, r), (H₁ a b - H₂ a b))
      (fun a => (∮ b in C(0, r), H₁ a b) - ∮ b in C(0, r), H₂ a b) (sphere (0 : ℂ) r) :=
    fun a ha => circleIntegral.integral_sub (hin h₁ a ha) (hin h₂ a ha)
  rw [circleIntegral.integral_congr hr.le hc]
  exact circleIntegral.integral_sub ((e64_circ_param_cont (H := fun q => H₁ q.1 q.2) hr h₁).circleIntegrable hr.le)
    ((e64_circ_param_cont (H := fun q => H₂ q.1 q.2) hr h₂).circleIntegrable hr.le)

/-- Uniform convergence on the torus passes through the double circle integral against a continuous kernel. -/
theorem e64_t8_lim {F : ℝ → ℂ × ℂ → ℂ} {G K : ℂ × ℂ → ℂ} {r : ℝ} (hr : 0 < r)
    (hu : TendstoUniformlyOn F G (𝓝[>] (0 : ℝ)) (sphere (0 : ℂ) r ×ˢ sphere (0 : ℂ) r))
    (hF : ∀ᶠ δ in 𝓝[>] (0 : ℝ), ContinuousOn (F δ) (sphere (0 : ℂ) r ×ˢ sphere (0 : ℂ) r))
    (hG : ContinuousOn G (sphere (0 : ℂ) r ×ˢ sphere (0 : ℂ) r))
    (hK : ContinuousOn K (sphere (0 : ℂ) r ×ˢ sphere (0 : ℂ) r)) :
    Tendsto (fun δ => ∮ a in C(0, r), ∮ b in C(0, r), K (a, b) * F δ (a, b)) (𝓝[>] (0 : ℝ))
      (𝓝 (∮ a in C(0, r), ∮ b in C(0, r), K (a, b) * G (a, b))) := by
  obtain ⟨B, hB⟩ := ((isCompact_sphere (0 : ℂ) r).prod (isCompact_sphere (0 : ℂ) r)).exists_bound_of_continuousOn hK
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB (r, r) ⟨by simp [abs_of_pos hr], by simp [abs_of_pos hr]⟩)
  rw [Metric.tendsto_nhds]
  intro ε hε
  set η : ℝ := ε / (2 * (2 * π * r * (2 * π * r * (B + 1)))) with hη
  have hη0 : 0 < η := by positivity
  filter_upwards [Metric.tendstoUniformlyOn_iff.1 hu η hη0, hF] with δ hδ hFδ
  have hKF : ContinuousOn (fun q : ℂ × ℂ => K (q.1, q.2) * F δ (q.1, q.2)) (sphere (0 : ℂ) r ×ˢ sphere (0 : ℂ) r) :=
    hK.mul hFδ
  have hKG : ContinuousOn (fun q : ℂ × ℂ => K (q.1, q.2) * G (q.1, q.2)) (sphere (0 : ℂ) r ×ˢ sphere (0 : ℂ) r) :=
    hK.mul hG
  rw [dist_eq_norm, ← e64_torus_sub (H₁ := fun a b => K (a, b) * F δ (a, b)) (H₂ := fun a b => K (a, b) * G (a, b))
    hr hKF hKG]
  have hle := e64_torus_norm_le (H := fun a b => K (a, b) * F δ (a, b) - K (a, b) * G (a, b)) (C := B * η) hr
    fun a ha b hb => by
      show ‖K (a, b) * F δ (a, b) - K (a, b) * G (a, b)‖ ≤ B * η
      rw [← mul_sub, norm_mul]
      have h1 := hδ (a, b) ⟨ha, hb⟩
      rw [dist_eq_norm, norm_sub_rev] at h1
      exact mul_le_mul (hB _ ⟨ha, hb⟩) h1.le (norm_nonneg _) hB0
  refine lt_of_le_of_lt hle ?_
  have hpos : 0 < 2 * π * r * (2 * π * r * (B + 1)) := by positivity
  calc 2 * π * r * (2 * π * r * (B * η)) ≤ 2 * π * r * (2 * π * r * ((B + 1) * η)) := by
        gcongr; linarith
    _ = ε / 2 := by rw [hη]; field_simp
    _ < ε := by linarith

/-- `∂_ε̄ (c g) = c ∂_ε̄ g` for a constant `c`, without a differentiability hypothesis. -/
theorem e64_t8_dzbar_cmul {g : ℂ → ℂ} {c : ℂ} (hc : c ≠ 0) (ε : ℂ) :
    dzbar (fun e => c * g e) ε = c * dzbar g ε := by
  by_cases hg : DifferentiableAt ℝ g ε
  · have h := (hg.hasFDerivAt.const_mul c).fderiv
    show (fderiv ℝ (fun e => c * g e) ε 1 + I * fderiv ℝ (fun e => c * g e) ε I) / 2 =
      c * ((fderiv ℝ g ε 1 + I * fderiv ℝ g ε I) / 2)
    rw [h]
    simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
    ring
  · have hcg : ¬ DifferentiableAt ℝ (fun e => c * g e) ε := by
      intro h
      apply hg
      have h2 := h.const_mul c⁻¹
      refine h2.congr_of_eventuallyEq (Eventually.of_forall fun e => ?_)
      show g e = c⁻¹ * (c * g e)
      rw [← mul_assoc, inv_mul_cancel₀ hc, one_mul]
    show (fderiv ℝ (fun e => c * g e) ε 1 + I * fderiv ℝ (fun e => c * g e) ε I) / 2 =
      c * ((fderiv ℝ g ε 1 + I * fderiv ℝ g ε I) / 2)
    rw [fderiv_zero_of_not_differentiableAt hg, fderiv_zero_of_not_differentiableAt hcg]
    simp

/-- **(E8) Core.** `∂_ε` at `0` passes under the principal value of `eq_1_25` at `u = z`:
`(π/4) ∂_ε ∂_ε̄ ρ^{εμ}(z)|₀ = lim_{δ→0} ∫_{𝕌∖B(z,δ)} ∂_ε|₀ [μ̄(v) K_ε(z, v̄) K_ε(v̄, z̄)] d²v`.
Assembly of E1–E7 with `eq_6_1`, `e124_eq_1_25` (radii `r < R`, `Rk < 1`):
* `I_δ(P) = ∫_{𝕌∖B(z,δ)} Φ(P)` is continuous on `D̄_r` and equals its torus Cauchy integral (E2, E3,
  `wr_cauchy_bidisc` pointwise in `v`, E1b with E6); the uniform limit `L` (E7) inherits both;
* `∂_ε̄ ρ^{εμ}(z) = (4/π) L(ε, ε̄)` for `|ε| < r` (`eq_6_1`, `e124_eq_1_25`, E4, `limUnder` of a limit);
* E1 for `L` and for each `Φ(·)(v)`, E1b with E6, and the uniform convergence on the torus. -/
theorem e64_core {μ : ℂ → ℂ} {k : ℝ} (hk : 0 ≤ k) (hμk : IsBeltramiCoeff μ upperHalf k)
    (hμs : ContDiffOn ℝ (⊤ : ℕ∞) μ upperHalf) {z : ℂ} (hz : z ∈ upperHalf) :
    (∀ δ : ℝ, 0 < δ → IntegrableOn (fun v => dz (fun e => conj (μ v) * kernelKbar (fun y => e * μ y) z v *
        kernelKbarbar (fun y => e * μ y) v z) 0) (upperHalf \ ball z δ)) ∧
      Tendsto (fun δ : ℝ => ∫ v in upperHalf \ ball z δ, dz (fun e => conj (μ v) * kernelKbar (fun y => e * μ y) z v *
        kernelKbarbar (fun y => e * μ y) v z) 0) (𝓝[>] 0) (𝓝 ((π / 4) * dz (dzbar fun ε => rhoVar μ ε z) 0)) := by
  set c0 : ℂ := ((2 * π * I)⁻¹) ^ 2 with hc0
  obtain ⟨W, hW⟩ : ∃ W : ℂ × ℂ → ℂ → ℂ, W = fun P => normalizedSolution fun u =>
      P.1 * (if 0 < u.im then μ u else 0) + P.2 * (if u.im < 0 then conj (μ (conj u)) else 0) := ⟨_, rfl⟩
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : ℂ × ℂ → ℂ → ℂ, Φ = fun P v => conj (μ v) *
      (dz (W P) z * dz (W P) (conj v) / (W P z - W P (conj v)) ^ 2) *
      (dz (W P) (conj v) * dz (W P) (conj z) / (W P (conj v) - W P (conj z)) ^ 2) := ⟨_, rfl⟩
  set R : ℝ := 1 / (k + 1) with hRd
  have hR : 0 < R := by positivity
  have hRk : R * k < 1 := by
    rw [hRd, div_mul_eq_mul_div, one_mul, div_lt_one (by positivity)]; linarith
  set r : ℝ := R / 2 with hrd
  have hr : 0 < r := by positivity
  have hrR : r < R := by linarith
  have hrk : r * k < 1 := lt_of_le_of_lt (mul_le_mul_of_nonneg_right hrR.le hk) hRk
  have hU : IsOpen upperHalf := isOpen_lt continuous_const Complex.continuous_im
  have hzim : 0 < z.im := hz
  set T := sphere (0 : ℂ) r ×ˢ sphere (0 : ℂ) r with hTd
  set D := closedBall (0 : ℂ) r ×ˢ closedBall (0 : ℂ) r with hDd
  have hTD : T ⊆ D := prod_mono sphere_subset_closedBall sphere_subset_closedBall
  have hTne : ∀ q ∈ T, q.1 ≠ 0 ∧ q.2 ≠ 0 := by
    intro q hq
    have h1 : ‖q.1‖ = r := by simpa using hq.1
    have h2 : ‖q.2‖ = r := by simpa using hq.2
    exact ⟨fun h => by rw [h, norm_zero] at h1; linarith, fun h => by rw [h, norm_zero] at h2; linarith⟩
  have hSm : ∀ δ : ℝ, MeasurableSet (upperHalf \ ball z δ) := fun δ => hU.measurableSet.diff measurableSet_ball
  have hSz : ∀ δ : ℝ, 0 < δ → ∀ v ∈ upperHalf \ ball z δ, v ∈ upperHalf \ {z} := fun δ hδ v hv =>
    ⟨hv.1, fun e => hv.2 (by have e' : v = z := mem_singleton_iff.mp e; rw [e']; exact mem_ball_self hδ)⟩
  have hcΦ := e64_phi_cont hk hμk hμs hz hrk hW hΦ
  -- continuity of `q ↦ Φ q v` on the closed polydisc
  have hcv : ∀ v ∈ upperHalf \ {z}, ContinuousOn (fun q : ℂ × ℂ => Φ q v) D := by
    intro v hv
    have h := hcΦ.comp (continuous_id.prodMk continuous_const).continuousOn
      (fun q (hq : q ∈ D) => (⟨hq, hv⟩ : (q, v) ∈ (closedBall (0 : ℂ) r ×ˢ closedBall (0 : ℂ) r) ×ˢ (upperHalf \ {z})))
    simpa only [Function.comp_def, id] using h
  -- (b) the pointwise Cauchy formula
  have hcauchy : ∀ v ∈ upperHalf \ {z}, ∀ P ∈ ball (0 : ℂ) r ×ˢ ball (0 : ℂ) r,
      Φ P v = c0 * ∮ a in C(0, r), ∮ b in C(0, r), Φ (a, b) v / ((a - P.1) * (b - P.2)) := by
    intro v hv P hP
    obtain ⟨h1, h2⟩ := e64_phi_holo hk hμk hμs hz hrk hW hΦ hv.1 (fun e => hv.2 (mem_singleton_iff.mpr e))
    have h := wr_cauchy_bidisc (f := fun q => Φ q v) (c := ((0, 0) : ℂ × ℂ)) hr hr (hcv v hv) h1 h2 hP
    exact h
  -- (h) `D(v)` is a torus coefficient
  have hTc : ∀ v ∈ upperHalf \ {z}, ContinuousOn (fun q : ℂ × ℂ => Φ q v) T := fun v hv => (hcv v hv).mono hTD
  have hD : ∀ v ∈ upperHalf \ {z}, dz (fun e => conj (μ v) * kernelKbar (fun y => e * μ y) z v *
      kernelKbarbar (fun y => e * μ y) v z) 0 = c0 * ∮ a in C(0, r), ∮ b in C(0, r), Φ (a, b) v / (a ^ 2 * b) := by
    intro v hv
    refine e64_torus_dz (G := fun q => Φ q v) hr (hTc v hv) ?_
    filter_upwards [ball_mem_nhds (0 : ℂ) hr] with ε hε
    have hεr : ‖ε‖ < r := by simpa using hε
    have hεk : ‖ε‖ * k < 1 := lt_of_le_of_lt (mul_le_mul_of_nonneg_right hεr.le hk) hrk
    show conj (μ v) * kernelKbar (fun y => ε * μ y) z v * kernelKbarbar (fun y => ε * μ y) v z = _
    rw [← e64_phi_diag hk hμk hμs hz hW hΦ hεk hv.1,
      hcauchy v hv (ε, conj ε) ⟨by simpa using hεr, by simpa [RCLike.norm_conj] using hεr⟩]
  -- (a) domination and continuity of `I_δ`
  set I : ℝ → ℂ × ℂ → ℂ := fun δ q => ∫ v in upperHalf \ ball z δ, Φ q v with hId
  have hIc : ∀ δ : ℝ, 0 < δ → ContinuousOn (I δ) D := by
    intro δ hδ
    obtain ⟨g, hg, hgb⟩ := e64_dominate hk hμk hμs hz hr hrR hRk hW hΦ hδ
    refine continuousOn_of_dominated (bound := g) (fun P hP => ?_) (fun P hP => ?_) hg ?_
    · obtain ⟨M, hM⟩ := e64_tail_bound hk hμk hμs hz hrk hW hΦ hδ
      exact (hM P hP).1.aestronglyMeasurable
    · filter_upwards [ae_restrict_mem (hSm δ)] with v hv
      exact hgb P hP v hv
    · filter_upwards [ae_restrict_mem (hSm δ)] with v hv
      exact hcv v (hSz δ hδ v hv)
  -- (d) the uniform limit
  obtain ⟨L, hL⟩ := e64_param_pv hk hμk hμs hz hrk hW hΦ
  have hIev : ∀ᶠ δ in 𝓝[>] (0 : ℝ), ContinuousOn (I δ) D := by
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    exact hIc δ hδ
  have hLc : ContinuousOn L D := hL.continuousOn hIev.frequently
  have hLT := hL.mono hTD
  have hIevT : ∀ᶠ δ in 𝓝[>] (0 : ℝ), ContinuousOn (I δ) T := hIev.mono fun δ h => h.mono hTD
  -- (c) the Cauchy formula for `I_δ`, and (e) for `L`
  have hKP : ∀ P ∈ ball (0 : ℂ) r ×ˢ ball (0 : ℂ) r,
      ContinuousOn (fun q : ℂ × ℂ => 1 / ((q.1 - P.1) * (q.2 - P.2))) T := by
    intro P hP
    refine continuousOn_const.div (((continuous_fst.sub continuous_const).mul
      (continuous_snd.sub continuous_const)).continuousOn) fun q hq => mul_ne_zero ?_ ?_
    · intro h
      have h1 : ‖q.1‖ = r := by simpa using hq.1
      have h2 : ‖P.1‖ < r := by simpa using hP.1
      rw [sub_eq_zero] at h; rw [h] at h1; linarith
    · intro h
      have h1 : ‖q.2‖ = r := by simpa using hq.2
      have h2 : ‖P.2‖ < r := by simpa using hP.2
      rw [sub_eq_zero] at h; rw [h] at h1; linarith
  have hswapP : ∀ δ : ℝ, 0 < δ → ∀ K : ℂ × ℂ → ℂ, ContinuousOn K T →
      IntegrableOn (fun v => ∮ a in C(0, r), ∮ b in C(0, r), K (a, b) * Φ (a, b) v) (upperHalf \ ball z δ) ∧
        ∫ v in upperHalf \ ball z δ, (∮ a in C(0, r), ∮ b in C(0, r), K (a, b) * Φ (a, b) v) =
          ∮ a in C(0, r), ∮ b in C(0, r), K (a, b) * I δ (a, b) := by
    intro δ hδ K hK
    obtain ⟨g, hg, hgb⟩ := e64_dominate hk hμk hμs hz hr hrR hRk hW hΦ hδ
    have hc : ContinuousOn (fun p : (ℂ × ℂ) × ℂ => Φ p.1 p.2) (T ×ˢ (upperHalf \ ball z δ)) :=
      hcΦ.mono (prod_mono hTD fun v hv => hSz δ hδ v hv)
    exact e64_torus_swap (hSm δ) hr hK hc hg fun q hq v hv => hgb q (hTD hq) v hv
  have hIcauchy : ∀ δ : ℝ, 0 < δ → ∀ P ∈ ball (0 : ℂ) r ×ˢ ball (0 : ℂ) r,
      I δ P = c0 * ∮ a in C(0, r), ∮ b in C(0, r), 1 / ((a - P.1) * (b - P.2)) * I δ (a, b) := by
    intro δ hδ P hP
    obtain ⟨-, hsw⟩ := hswapP δ hδ (fun q => 1 / ((q.1 - P.1) * (q.2 - P.2))) (hKP P hP)
    rw [← hsw, ← integral_const_mul]
    refine setIntegral_congr_fun (hSm δ) fun v hv => ?_
    rw [hcauchy v (hSz δ hδ v hv) P hP]
    congr 1
    refine e64_torus_congr hr fun a _ b _ => ?_
    ring
  have hLcauchy : ∀ P ∈ ball (0 : ℂ) r ×ˢ ball (0 : ℂ) r,
      L P = c0 * ∮ a in C(0, r), ∮ b in C(0, r), 1 / ((a - P.1) * (b - P.2)) * L (a, b) := by
    intro P hP
    have hPD : P ∈ D := ⟨ball_subset_closedBall hP.1, ball_subset_closedBall hP.2⟩
    have t1 : Tendsto (fun δ => I δ P) (𝓝[>] (0 : ℝ)) (𝓝 (L P)) := hL.tendsto_at hPD
    have t2 := (e64_t8_lim hr hLT hIevT (hLc.mono hTD) (hKP P hP)).const_mul c0
    refine tendsto_nhds_unique t1 (t2.congr' ?_)
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    exact (hIcauchy δ hδ P hP).symm
  -- (f) `∂_ε̄ ρ^{εμ}(z) = (4/π) L(ε, ε̄)`
  have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 Real.pi_ne_zero
  have hh : ∀ ε : ℂ, ‖ε‖ < r → dzbar (fun e => rhoVar μ e z) ε = (4 / π) * L (ε, conj ε) := by
    intro ε hεr
    have hεk : ‖ε‖ * k < 1 := lt_of_le_of_lt (mul_le_mul_of_nonneg_right hεr.le hk) hrk
    have hPD : (ε, conj ε) ∈ D := ⟨by simpa using hεr.le, by simpa [RCLike.norm_conj] using hεr.le⟩
    have hfun : (fun e => rhoVar μ e z) = fun e => (-4 : ℂ) * kernelKbar (fun y => e * μ y) z z :=
      funext fun e => eq_6_1 μ e z
    rw [hfun, e64_t8_dzbar_cmul (by norm_num) ε, (e124_eq_1_25 hk hμk hμs hεk hz hz).2]
    have hlim : Tendsto (fun δ : ℝ => ∫ v in upperHalf \ (ball z δ ∪ ball z δ), conj (μ v) *
        kernelKbar (fun y => ε * μ y) z v * kernelKbarbar (fun y => ε * μ y) v z) (𝓝[>] (0 : ℝ))
        (𝓝 (L (ε, conj ε))) := by
      refine (hL.tendsto_at hPD).congr' (Eventually.of_forall fun δ => ?_)
      simp only [union_self]
      exact setIntegral_congr_fun (hSm δ) fun v hv => e64_phi_diag hk hμk hμs hz hW hΦ hεk hv.1
    show (-4 : ℂ) * (-(1 / π) * limUnder (𝓝[>] (0 : ℝ)) _) = _
    rw [hlim.limUnder_eq]
    ring
  -- (g) E1 for `L`
  have hdzh : dz (dzbar fun e => rhoVar μ e z) 0 =
      c0 * ∮ a in C(0, r), ∮ b in C(0, r), (4 / (π : ℂ)) * L (a, b) / (a ^ 2 * b) := by
    refine e64_torus_dz (G := fun q => (4 / (π : ℂ)) * L q) hr (continuousOn_const.mul (hLc.mono hTD)) ?_
    filter_upwards [ball_mem_nhds (0 : ℂ) hr] with ε hε
    have hεr : ‖ε‖ < r := by simpa using hε
    have hpull : (∮ a in C(0, r), ∮ b in C(0, r), (4 / (π : ℂ)) * L (a, b) / ((a - ε) * (b - conj ε))) =
        (4 / (π : ℂ)) * ∮ a in C(0, r), ∮ b in C(0, r), 1 / ((a - ε) * (b - conj ε)) * L (a, b) := by
      rw [← e64_torus_const_mul]
      exact e64_torus_congr hr fun a _ b _ => by ring
    show dzbar (fun e => rhoVar μ e z) ε = c0 * ∮ a in C(0, r), ∮ b in C(0, r),
      (4 / (π : ℂ)) * L (a, b) / ((a - ε) * (b - conj ε))
    rw [hh ε hεr, hLcauchy (ε, conj ε) ⟨by simpa using hεr, by simpa [RCLike.norm_conj] using hεr⟩, hpull]
    ring
  -- (h), (i)
  have hKab : ContinuousOn (fun q : ℂ × ℂ => 1 / (q.1 ^ 2 * q.2)) T :=
    continuousOn_const.div ((continuous_fst.pow 2).mul continuous_snd).continuousOn fun q hq =>
      mul_ne_zero (pow_ne_zero _ (hTne q hq).1) (hTne q hq).2
  have hDeq : ∀ δ : ℝ, 0 < δ → ∀ v ∈ upperHalf \ ball z δ,
      dz (fun e => conj (μ v) * kernelKbar (fun y => e * μ y) z v * kernelKbarbar (fun y => e * μ y) v z) 0 =
        c0 * ∮ a in C(0, r), ∮ b in C(0, r), 1 / (a ^ 2 * b) * Φ (a, b) v := by
    intro δ hδ v hv
    rw [hD v (hSz δ hδ v hv)]
    congr 1
    refine e64_torus_congr hr fun a _ b _ => ?_
    ring
  refine ⟨fun δ hδ => ?_, ?_⟩
  · obtain ⟨hi, -⟩ := hswapP δ hδ (fun q => 1 / (q.1 ^ 2 * q.2)) hKab
    have hi2 : IntegrableOn (fun v => c0 * ∮ a in C(0, r), ∮ b in C(0, r), 1 / (a ^ 2 * b) * Φ (a, b) v)
        (upperHalf \ ball z δ) := hi.const_mul c0
    exact hi2.congr_fun (fun v hv => (hDeq δ hδ v hv).symm) (hSm δ)
  · have t := (e64_t8_lim hr hLT hIevT (hLc.mono hTD) hKab).const_mul c0
    have htarget : (π / 4 : ℂ) * dz (dzbar fun ε => rhoVar μ ε z) 0 =
        c0 * ∮ a in C(0, r), ∮ b in C(0, r), 1 / (a ^ 2 * b) * L (a, b) := by
      rw [hdzh]
      have e1 : (∮ a in C(0, r), ∮ b in C(0, r), (4 / (π : ℂ)) * L (a, b) / (a ^ 2 * b)) =
          (4 / (π : ℂ)) * ∮ a in C(0, r), ∮ b in C(0, r), 1 / (a ^ 2 * b) * L (a, b) := by
        rw [← e64_torus_const_mul]
        refine e64_torus_congr hr fun a _ b _ => ?_
        ring
      rw [e1]
      field_simp
    rw [htarget]
    refine t.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    obtain ⟨-, hsw⟩ := hswapP δ hδ (fun q => 1 / (q.1 ^ 2 * q.2)) hKab
    rw [← hsw, ← integral_const_mul]
    exact (setIntegral_congr_fun (hSm δ) fun v hv => hDeq δ hδ v hv).symm

/-! ### The `u`-integrals at `ε = 0` -/

/-- `d ≥ t`, `d ≥ x - A` give `d ≥ t (1 + x)/(1 + A + t)` (`t > 0`, `A, x ≥ 0`). -/
theorem e64_t10_alg {d t A x : ℝ} (ht : 0 < t) (hA : 0 ≤ A) (hx : 0 ≤ x) (h1 : t ≤ d) (h2 : x - A ≤ d) :
    t / (1 + A + t) * (1 + x) ≤ d := by
  have hpos : 0 < 1 + A + t := by linarith
  rw [div_mul_eq_mul_div, div_le_iff₀ hpos]
  by_cases hxA : x ≤ A + t
  · nlinarith
  · push Not at hxA
    nlinarith

/-- Distance from a point `a` with `t ≤ ‖u - a‖` for all relevant `u`: a linear lower bound in `1 + ‖u‖`. -/
theorem e64_t10_lower {u a : ℂ} {t : ℝ} (ht : 0 < t) (h : t ≤ ‖u - a‖) :
    t / (1 + ‖a‖ + t) * (1 + ‖u‖) ≤ ‖u - a‖ := by
  refine e64_t10_alg ht (norm_nonneg a) (norm_nonneg u) h ?_
  have := norm_sub_norm_le u a
  linarith

/-- `‖1/((u - a)^m (u - b)^n)‖ ≤ (cₐ^m c_b^n)⁻¹ (1 + ‖u‖)^{-(m+n)}` under linear lower bounds. -/
theorem e64_t10_rat {u a b : ℂ} {ca cb : ℝ} (hca : 0 < ca) (hcb : 0 < cb)
    (ha : ca * (1 + ‖u‖) ≤ ‖u - a‖) (hb : cb * (1 + ‖u‖) ≤ ‖u - b‖) (m n : ℕ) :
    ‖1 / ((u - a) ^ m * (u - b) ^ n)‖ ≤ (ca ^ m * cb ^ n)⁻¹ * ((1 + ‖u‖) ^ (m + n))⁻¹ := by
  have hu : 0 < 1 + ‖u‖ := by positivity
  rw [norm_div, norm_one, norm_mul, norm_pow, norm_pow, one_div, pow_add, ← mul_inv]
  refine inv_anti₀ (by positivity) ?_
  calc ca ^ m * cb ^ n * ((1 + ‖u‖) ^ m * (1 + ‖u‖) ^ n) = (ca * (1 + ‖u‖)) ^ m * (cb * (1 + ‖u‖)) ^ n := by
        rw [mul_pow ca, mul_pow cb]; ring
    _ ≤ ‖u - a‖ ^ m * ‖u - b‖ ^ n :=
        mul_le_mul (pow_le_pow_left₀ (by positivity) ha m) (pow_le_pow_left₀ (by positivity) hb n)
          (by positivity) (by positivity)

/-- Points of `𝕌` stay at distance `≥ -Im a` from a point `a` of `𝕃`. -/
theorem e64_t10_im {u a : ℂ} (hu : 0 < u.im) (ha : a.im < 0) : -a.im ≤ ‖u - a‖ := by
  have h1 := Complex.abs_im_le_norm (u - a)
  have h2 : (u - a).im = u.im - a.im := by simp
  rw [h2, abs_of_pos (by linarith)] at h1
  linarith

/-- The three `u`-integrability facts behind (E10). -/
theorem e64_t10_int {μ φ : ℂ → ℂ} (hμ : IsHarmonicU μ φ) {z : ℂ} (hz : z ∈ upperHalf) {v : ℂ}
    (hv : v ∈ upperHalf) :
    IntegrableOn (fun u => μ u * conj (μ v) *
        (1 / ((u - conj v) ^ 2 * (z - conj v) ^ 2 * (u - conj z) ^ 2) +
          (z - conj z) / ((u - conj z) ^ 3 * (u - conj v) * (z - conj v) ^ 3))) upperHalf ∧
      IntegrableOn (fun u => μ u / ((u - z) * (u - conj z) ^ 3)) upperHalf ∧
      ∀ δ : ℝ, 0 < δ → IntegrableOn (fun u => μ u / ((u - z) ^ 2 * (u - conj z) ^ 2)) (upperHalfPunct z δ) := by
  obtain ⟨M, hM0, hM⟩ := harmonicU_bounded hμ
  have hμc := harmonicU_continuousOn hμ
  have hU := measurableSet_upperHalf_aux
  have hzim : 0 < z.im := hz
  have hvim : 0 < v.im := hv
  have hzb : (conj z).im < 0 := by rw [Complex.conj_im]; linarith
  have hvb : (conj v).im < 0 := by rw [Complex.conj_im]; linarith
  set cz : ℝ := -(conj z).im / (1 + ‖conj z‖ + -(conj z).im) with hcz
  set cv : ℂ → ℝ := fun _ => -(conj v).im / (1 + ‖conj v‖ + -(conj v).im) with hcv
  have hcz0 : 0 < cz := by rw [hcz]; have := norm_nonneg (conj z); exact div_pos (by linarith) (by linarith)
  have hcv0 : 0 < cv 0 := by
    simp only [hcv]; have := norm_nonneg (conj v); exact div_pos (by linarith) (by linarith)
  have hlz : ∀ u ∈ upperHalf, cz * (1 + ‖u‖) ≤ ‖u - conj z‖ := fun u hu =>
    e64_t10_lower (by linarith) (e64_t10_im hu hzb)
  have hlv : ∀ u ∈ upperHalf, cv 0 * (1 + ‖u‖) ≤ ‖u - conj v‖ := fun u hu =>
    e64_t10_lower (by linarith) (e64_t10_im hu hvb)
  have hmaj := (e64_t5_maj 0).1
  simp only [sub_zero] at hmaj
  have hne_zb : ∀ u ∈ upperHalf, u - conj z ≠ 0 := fun u hu h => by
    have := hlz u hu; rw [h, norm_zero] at this; nlinarith [norm_nonneg u]
  have hne_vb : ∀ u ∈ upperHalf, u - conj v ≠ 0 := fun u hu h => by
    have := hlv u hu; rw [h, norm_zero] at this; nlinarith [norm_nonneg u]
  refine ⟨?_, ?_, ?_⟩
  · -- the regular integrand: `O((1 + |u|)⁻⁴)`
    set K : ℝ := M * ‖conj (μ v)‖ * (‖1 / (z - conj v) ^ 2‖ * ((cv 0) ^ 2 * cz ^ 2)⁻¹ +
      ‖(z - conj z) / (z - conj v) ^ 3‖ * (cz ^ 3 * (cv 0) ^ 1)⁻¹) with hK
    refine (hmaj.const_mul K).integrableOn.mono' ?_ ?_
    · refine ContinuousOn.aestronglyMeasurable ?_ hU
      refine (hμc.mul continuousOn_const).mul ((continuousOn_const.div ?_ ?_).add (continuousOn_const.div ?_ ?_))
      · fun_prop
      · intro u hu
        exact mul_ne_zero (mul_ne_zero (pow_ne_zero _ (hne_vb u hu))
          (pow_ne_zero _ (sub_ne_zero.mpr fun h => by
            have := congrArg Complex.im h; rw [Complex.conj_im] at this; linarith))) (pow_ne_zero _ (hne_zb u hu))
      · fun_prop
      · intro u hu
        exact mul_ne_zero (mul_ne_zero (pow_ne_zero _ (hne_zb u hu)) (hne_vb u hu))
          (pow_ne_zero _ (sub_ne_zero.mpr fun h => by
            have := congrArg Complex.im h; rw [Complex.conj_im] at this; linarith))
    · filter_upwards [ae_restrict_mem hU] with u hu
      have r1 := e64_t10_rat hcv0 hcz0 (hlv u hu) (hlz u hu) 2 2
      have r2 := e64_t10_rat hcz0 hcv0 (hlz u hu) (hlv u hu) 3 1
      have e1 : 1 / ((u - conj v) ^ 2 * (z - conj v) ^ 2 * (u - conj z) ^ 2) =
          1 / (z - conj v) ^ 2 * (1 / ((u - conj v) ^ 2 * (u - conj z) ^ 2)) := by
        rw [one_div_mul_one_div]; ring_nf
      have e2 : (z - conj z) / ((u - conj z) ^ 3 * (u - conj v) * (z - conj v) ^ 3) =
          (z - conj z) / (z - conj v) ^ 3 * (1 / ((u - conj z) ^ 3 * (u - conj v) ^ 1)) := by
        rw [pow_one, div_mul_div_comm, mul_one]; ring_nf
      rw [e1, e2, norm_mul, norm_mul]
      have hu4 : (2 + 2 : ℕ) = 4 := rfl
      have hu4' : (3 + 1 : ℕ) = 4 := rfl
      rw [hu4] at r1
      rw [hu4'] at r2
      have hn := norm_add_le (1 / (z - conj v) ^ 2 * (1 / ((u - conj v) ^ 2 * (u - conj z) ^ 2)))
        ((z - conj z) / (z - conj v) ^ 3 * (1 / ((u - conj z) ^ 3 * (u - conj v) ^ 1)))
      rw [norm_mul, norm_mul] at hn
      have hμu : ‖μ u‖ ≤ M := hM u hu
      have hX : 0 < ((1 + ‖u‖) ^ 4)⁻¹ := by positivity
      calc ‖μ u‖ * ‖conj (μ v)‖ * ‖1 / (z - conj v) ^ 2 * (1 / ((u - conj v) ^ 2 * (u - conj z) ^ 2)) +
            (z - conj z) / (z - conj v) ^ 3 * (1 / ((u - conj z) ^ 3 * (u - conj v) ^ 1))‖
          ≤ M * ‖conj (μ v)‖ * (‖1 / (z - conj v) ^ 2‖ * ((cv 0 ^ 2 * cz ^ 2)⁻¹ * ((1 + ‖u‖) ^ 4)⁻¹) +
              ‖(z - conj z) / (z - conj v) ^ 3‖ * ((cz ^ 3 * cv 0 ^ 1)⁻¹ * ((1 + ‖u‖) ^ 4)⁻¹)) := by
            refine mul_le_mul (mul_le_mul_of_nonneg_right hμu (norm_nonneg _)) (hn.trans (add_le_add
              (mul_le_mul_of_nonneg_left r1 (norm_nonneg _)) (mul_le_mul_of_nonneg_left r2 (norm_nonneg _))))
              (norm_nonneg _) (by positivity)
        _ = K * ((1 + ‖u‖) ^ 4)⁻¹ := by rw [hK]; ring
  · -- `μ/((u - z)(u - z̄)³)`: `O(1/|u - z|)` near `z`, `O((1 + |u|)⁻⁴)` away
    set ρ : ℝ := z.im / 2 with hρ
    have hρ0 : 0 < ρ := by positivity
    have hcont : ContinuousOn (fun u => μ u / ((u - z) * (u - conj z) ^ 3)) (upperHalf \ {z}) := by
      refine (hμc.mono sdiff_subset).div (by fun_prop) fun u hu => mul_ne_zero (sub_ne_zero.mpr hu.2)
        (pow_ne_zero _ (hne_zb u hu.1))
    have hUz : MeasurableSet (upperHalf \ {z}) := hU.diff (measurableSet_singleton z)
    have hnull : (upperHalf \ {z} : Set ℂ) =ᵐ[volume] upperHalf := by
      exact sdiff_null_ae_eq_self (μ := volume) (s := upperHalf) (measure_singleton z)
    rw [← integrableOn_congr_set_ae hnull]
    have hfar : IntegrableOn (fun u => μ u / ((u - z) * (u - conj z) ^ 3)) ((upperHalf \ {z}) \ ball z ρ) := by
      set cρ : ℝ := ρ / (1 + ‖z‖ + ρ) with hcρ
      have hcρ0 : 0 < cρ := by rw [hcρ]; have := norm_nonneg z; exact div_pos hρ0 (by linarith)
      refine (hmaj.const_mul (M * (cρ ^ 1 * cz ^ 3)⁻¹)).integrableOn.mono' ?_ ?_
      · exact (hcont.mono sdiff_subset).aestronglyMeasurable (hUz.diff measurableSet_ball)
      · filter_upwards [ae_restrict_mem (hUz.diff measurableSet_ball)] with u hu
        have hd : ρ ≤ ‖u - z‖ := by
          have := hu.2; rw [mem_ball, dist_eq_norm, not_lt] at this; exact this
        have r := e64_t10_rat hcρ0 hcz0 (e64_t10_lower hρ0 hd) (hlz u hu.1.1) 1 3
        rw [show (1 + 3 : ℕ) = 4 from rfl, pow_one] at r
        rw [div_eq_mul_one_div, norm_mul]
        calc ‖μ u‖ * ‖1 / ((u - z) * (u - conj z) ^ 3)‖ ≤ M * ((cρ ^ 1 * cz ^ 3)⁻¹ * ((1 + ‖u‖) ^ 4)⁻¹) :=
              mul_le_mul (hM u hu.1.1) (by simpa only [pow_one] using r) (norm_nonneg _) hM0
          _ = M * (cρ ^ 1 * cz ^ 3)⁻¹ * ((1 + ‖u‖) ^ 4)⁻¹ := by ring
    have hnear : IntegrableOn (fun u => μ u / ((u - z) * (u - conj z) ^ 3)) ((upperHalf \ {z}) ∩ ball z ρ) := by
      have hb : IntegrableOn (fun u => M * (z.im ^ 3)⁻¹ * ‖u - z‖⁻¹) (ball z ρ) :=
        (e124p_invnorm_int z ρ).const_mul (M * (z.im ^ 3)⁻¹)
      refine (hb.mono_set inter_subset_right).mono' ?_ ?_
      · exact (hcont.mono inter_subset_left).aestronglyMeasurable (hUz.inter measurableSet_ball)
      · filter_upwards [ae_restrict_mem (hUz.inter measurableSet_ball)] with u hu
        have hz3 : z.im ≤ ‖u - conj z‖ := by
          have := e64_t10_im hu.1.1 hzb; rw [Complex.conj_im, neg_neg] at this; exact this
        have huz : 0 < ‖u - z‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hu.1.2)
        rw [norm_div, norm_mul, norm_pow]
        calc ‖μ u‖ / (‖u - z‖ * ‖u - conj z‖ ^ 3) ≤ M / (‖u - z‖ * z.im ^ 3) :=
              div_le_div₀ hM0 (hM u hu.1.1) (by positivity)
                (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hzim.le hz3 3) huz.le)
          _ = M * (z.im ^ 3)⁻¹ * ‖u - z‖⁻¹ := by field_simp
    have hU' : (upperHalf \ {z} : Set ℂ) = ((upperHalf \ {z}) \ ball z ρ) ∪ ((upperHalf \ {z}) ∩ ball z ρ) :=
      (sdiff_union_inter _ _).symm
    rw [hU']
    exact hfar.union hnear
  · intro δ hδ
    set cδ : ℝ := δ / (1 + ‖z‖ + δ) with hcδ
    have hcδ0 : 0 < cδ := by rw [hcδ]; have := norm_nonneg z; exact div_pos hδ (by linarith)
    have hPm : MeasurableSet (upperHalfPunct z δ) := hU.diff measurableSet_ball
    refine (hmaj.const_mul (M * (cδ ^ 2 * cz ^ 2)⁻¹)).integrableOn.mono' ?_ ?_
    · refine ContinuousOn.aestronglyMeasurable ?_ hPm
      refine (hμc.mono sdiff_subset).div (by fun_prop) fun u hu => mul_ne_zero (pow_ne_zero _ (sub_ne_zero.mpr ?_))
        (pow_ne_zero _ (hne_zb u hu.1))
      intro h
      apply hu.2
      rw [h]
      exact mem_ball_self hδ
    · filter_upwards [ae_restrict_mem hPm] with u hu
      have hd : δ ≤ ‖u - z‖ := by
        have := hu.2; rw [mem_ball, dist_eq_norm, not_lt] at this; exact this
      have r := e64_t10_rat hcδ0 hcz0 (e64_t10_lower hδ hd) (hlz u hu.1) 2 2
      rw [show (2 + 2 : ℕ) = 4 from rfl] at r
      rw [div_eq_mul_one_div, norm_mul]
      calc ‖μ u‖ * ‖1 / ((u - z) ^ 2 * (u - conj z) ^ 2)‖ ≤ M * ((cδ ^ 2 * cz ^ 2)⁻¹ * ((1 + ‖u‖) ^ 4)⁻¹) :=
            mul_le_mul (hM u hu.1) r (norm_nonneg _) hM0
        _ = M * (cδ ^ 2 * cz ^ 2)⁻¹ * ((1 + ‖u‖) ^ 4)⁻¹ := by ring

/-- **(E10) Regularization in `u`** (`eq_6_5_four_terms`): for `v ≠ z` the truncations converge, and the third and
fourth terms drop out (`eq_6_3`, `cor_1_15`). -/
theorem e64_inner_regular {μ φ : ℂ → ℂ} (hμ : IsHarmonicU μ φ) {z : ℂ} (hz : z ∈ upperHalf) {v : ℂ}
    (hv : v ∈ upperHalf) (hvz : v ≠ z) :
    Tendsto (fun δ : ℝ => ∫ u in upperHalfPunct z δ, μ u * conj (μ v) *
        (1 / ((u - conj v) ^ 2 * (z - conj v) ^ 2 * (u - conj z) ^ 2) +
          1 / ((u - z) ^ 2 * (u - conj v) ^ 2 * (conj z - conj v) ^ 2))) (𝓝[>] 0)
      (𝓝 (2 * ∫ u in upperHalf, μ u * conj (μ v) *
        (1 / ((u - conj v) ^ 2 * (z - conj v) ^ 2 * (u - conj z) ^ 2) +
          (z - conj z) / ((u - conj z) ^ 3 * (u - conj v) * (z - conj v) ^ 3)))) := by
  obtain ⟨hI1, hI2, hI3⟩ := e64_t10_int hμ hz hv
  have hU := measurableSet_upperHalf_aux
  have hzim : 0 < z.im := hz
  have hvim : 0 < v.im := hv
  set c := conj (μ v) with hc
  set H : ℂ → ℂ := fun u => μ u * c *
    (1 / ((u - conj v) ^ 2 * (z - conj v) ^ 2 * (u - conj z) ^ 2) +
      (z - conj z) / ((u - conj z) ^ 3 * (u - conj v) * (z - conj v) ^ 3)) with hH
  set K3 : ℂ := c * ((z - conj z) ^ 2 / ((z - conj v) ^ 2 * (conj z - conj v) ^ 2)) with hK3
  set K4 : ℂ := c * (2 * (z - conj z) ^ 2 / ((z - conj v) ^ 3 * (conj z - conj v))) with hK4
  have hpt : ∀ u ∈ upperHalf, u ≠ z → μ u * c *
      (1 / ((u - conj v) ^ 2 * (z - conj v) ^ 2 * (u - conj z) ^ 2) +
        1 / ((u - z) ^ 2 * (u - conj v) ^ 2 * (conj z - conj v) ^ 2)) =
      2 * H u + K3 * (μ u / ((u - z) ^ 2 * (u - conj z) ^ 2)) + K4 * (μ u / ((u - z) * (u - conj z) ^ 3)) := by
    intro u hu huz
    have hu' : 0 < u.im := hu
    have h1 : u - conj v ≠ 0 := fun h => by
      have := congrArg Complex.im h; simp at this; linarith
    have h2 : u - conj z ≠ 0 := fun h => by
      have := congrArg Complex.im h; simp at this; linarith
    have h3 : z - conj v ≠ 0 := fun h => by
      have := congrArg Complex.im h; simp at this; linarith
    have h4 : conj z - conj v ≠ 0 := fun h => hvz (by
      have e := congrArg conj (sub_eq_zero.mp h); simp only [Complex.conj_conj] at e; exact e.symm)
    rw [eq_6_5_four_terms (sub_ne_zero.mpr huz) h1 h2 h3 h4]
    simp only [hH, hK3, hK4]
    have h5 : u - z ≠ 0 := sub_ne_zero.mpr huz
    field_simp
    ring
  have hsplit : ∀ δ : ℝ, 0 < δ → (∫ u in upperHalfPunct z δ, μ u * c *
      (1 / ((u - conj v) ^ 2 * (z - conj v) ^ 2 * (u - conj z) ^ 2) +
        1 / ((u - z) ^ 2 * (u - conj v) ^ 2 * (conj z - conj v) ^ 2))) =
      2 * (∫ u in upperHalfPunct z δ, H u) + K3 * (∫ u in upperHalfPunct z δ, μ u / ((u - z) ^ 2 * (u - conj z) ^ 2)) +
        K4 * ∫ u in upperHalfPunct z δ, μ u / ((u - z) * (u - conj z) ^ 3) := by
    intro δ hδ
    have hPm : MeasurableSet (upperHalfPunct z δ) := hU.diff measurableSet_ball
    have hsub : upperHalfPunct z δ ⊆ upperHalf := sdiff_subset
    have i1 : IntegrableOn (fun u => 2 * H u) (upperHalfPunct z δ) := (hI1.mono_set hsub).const_mul 2
    have i2 : IntegrableOn (fun u => K3 * (μ u / ((u - z) ^ 2 * (u - conj z) ^ 2))) (upperHalfPunct z δ) :=
      (hI3 δ hδ).const_mul K3
    have i3 : IntegrableOn (fun u => K4 * (μ u / ((u - z) * (u - conj z) ^ 3))) (upperHalfPunct z δ) :=
      (hI2.mono_set hsub).const_mul K4
    have i12 : IntegrableOn (fun u => 2 * H u + K3 * (μ u / ((u - z) ^ 2 * (u - conj z) ^ 2)))
        (upperHalfPunct z δ) := i1.add i2
    rw [setIntegral_congr_fun hPm (fun u hu => hpt u hu.1 (fun h => hu.2 (by rw [h]; exact mem_ball_self hδ))),
      integral_add i12 i3, integral_add i1 i2, integral_const_mul, integral_const_mul, integral_const_mul]
  have hpunct : ∀ δ : ℝ, upperHalfPunct z δ = upperHalf \ (ball z δ ∪ ball z δ) := fun δ => by
    rw [union_self]; rfl
  have t1 : Tendsto (fun δ : ℝ => ∫ u in upperHalfPunct z δ, H u) (𝓝[>] 0) (𝓝 (∫ u in upperHalf, H u)) := by
    simpa only [hpunct] using e124a_reg2 z z hI1
  have t2 := eq_6_3 hμ hz
  have t3 : Tendsto (fun δ : ℝ => ∫ u in upperHalfPunct z δ, μ u / ((u - z) * (u - conj z) ^ 3)) (𝓝[>] 0) (𝓝 0) := by
    have h := e124a_reg2 z z hI2
    rw [cor_1_15 hμ hz] at h
    simpa only [hpunct] using h
  have hlim := ((t1.const_mul 2).add (t2.const_mul K3)).add (t3.const_mul K4)
  simp only [mul_zero, add_zero] at hlim
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  exact (hsplit δ hδ).symm

/-- Wirtinger product rule. -/
theorem e64_t9_dz_mul {u v : ℂ → ℂ} {z : ℂ} (hu : DifferentiableAt ℝ u z) (hv : DifferentiableAt ℝ v z) :
    dz (fun w => u w * v w) z = u z * dz v z + v z * dz u z := by
  simp only [dz, fderiv_fun_mul hu hv, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.coe_smul', Pi.smul_apply, smul_eq_mul]
  ring

/-- `w_0 = id`. -/
theorem e64_t9_w0 (μ : ℂ → ℂ) : wU (fun y => (0 : ℂ) * μ y) = id := by
  have h0 : (fun y => (0 : ℂ) * μ y) = (0 : ℂ → ℂ) := by funext y; simp
  rw [h0, rhoVar_wU_zero]

/-- The kernels at `ε = 0` (`w_0 = id`). -/
theorem e64_t9_K0 (μ : ℂ → ℂ) (a b : ℂ) :
    kernelK (fun y => (0 : ℂ) * μ y) a b = 1 / (a - b) ^ 2 ∧
      kernelKbar (fun y => (0 : ℂ) * μ y) a b = 1 / (a - conj b) ^ 2 ∧
      kernelKbarbar (fun y => (0 : ℂ) * μ y) a b = 1 / (conj a - conj b) ^ 2 := by
  have h0 : (fun y => (0 : ℂ) * μ y) = (0 : ℂ → ℂ) := by funext y; simp
  unfold kernelKbarbar kernelKbar kernelK
  rw [h0, rhoVar_wU_zero]
  simp only [rhoVar_dz_id, id, map_one, mul_one, map_div₀, map_pow, map_sub]
  refine ⟨?_, ?_, ?_⟩ <;> first | trivial | rfl

/-- Integrability of `μ(u)/((u - v̄)²(u - z̄)²)` on `𝕌`, and of `μ(u)/((z - u)²(u - v̄)²)` off a disc at `z`. -/
theorem e64_t9_int {μ φ : ℂ → ℂ} (hμ : IsHarmonicU μ φ) {z : ℂ} (hz : z ∈ upperHalf) {v : ℂ}
    (hv : v ∈ upperHalf) :
    IntegrableOn (fun u => μ u / ((u - conj v) ^ 2 * (u - conj z) ^ 2)) upperHalf ∧
      ∀ δ : ℝ, 0 < δ → IntegrableOn (fun u => μ u * (1 / (z - u) ^ 2) * (1 / (u - conj v) ^ 2))
        (upperHalf \ ball z δ) := by
  obtain ⟨M, hM0, hM⟩ := harmonicU_bounded hμ
  have hμc := harmonicU_continuousOn hμ
  have hU := measurableSet_upperHalf_aux
  have hzim : 0 < z.im := hz
  have hvim : 0 < v.im := hv
  have hzb : (conj z).im < 0 := by rw [Complex.conj_im]; linarith
  have hvb : (conj v).im < 0 := by rw [Complex.conj_im]; linarith
  set cz : ℝ := -(conj z).im / (1 + ‖conj z‖ + -(conj z).im) with hcz
  set cv : ℝ := -(conj v).im / (1 + ‖conj v‖ + -(conj v).im) with hcv
  have hcz0 : 0 < cz := by rw [hcz]; have := norm_nonneg (conj z); exact div_pos (by linarith) (by linarith)
  have hcv0 : 0 < cv := by rw [hcv]; have := norm_nonneg (conj v); exact div_pos (by linarith) (by linarith)
  have hlz : ∀ u ∈ upperHalf, cz * (1 + ‖u‖) ≤ ‖u - conj z‖ := fun u hu =>
    e64_t10_lower (by linarith) (e64_t10_im hu hzb)
  have hlv : ∀ u ∈ upperHalf, cv * (1 + ‖u‖) ≤ ‖u - conj v‖ := fun u hu =>
    e64_t10_lower (by linarith) (e64_t10_im hu hvb)
  have hmaj := (e64_t5_maj 0).1
  simp only [sub_zero] at hmaj
  have hne_zb : ∀ u ∈ upperHalf, u - conj z ≠ 0 := fun u hu h => by
    have := hlz u hu; rw [h, norm_zero] at this; nlinarith [norm_nonneg u]
  have hne_vb : ∀ u ∈ upperHalf, u - conj v ≠ 0 := fun u hu h => by
    have := hlv u hu; rw [h, norm_zero] at this; nlinarith [norm_nonneg u]
  refine ⟨?_, ?_⟩
  · refine (hmaj.const_mul (M * (cv ^ 2 * cz ^ 2)⁻¹)).integrableOn.mono' ?_ ?_
    · exact ContinuousOn.aestronglyMeasurable (hμc.div (by fun_prop) fun u hu =>
        mul_ne_zero (pow_ne_zero _ (hne_vb u hu)) (pow_ne_zero _ (hne_zb u hu))) hU
    · filter_upwards [ae_restrict_mem hU] with u hu
      have r := e64_t10_rat hcv0 hcz0 (hlv u hu) (hlz u hu) 2 2
      rw [show (2 + 2 : ℕ) = 4 from rfl] at r
      rw [div_eq_mul_one_div, norm_mul]
      calc ‖μ u‖ * ‖1 / ((u - conj v) ^ 2 * (u - conj z) ^ 2)‖ ≤ M * ((cv ^ 2 * cz ^ 2)⁻¹ * ((1 + ‖u‖) ^ 4)⁻¹) :=
            mul_le_mul (hM u hu) r (norm_nonneg _) hM0
        _ = M * (cv ^ 2 * cz ^ 2)⁻¹ * ((1 + ‖u‖) ^ 4)⁻¹ := by ring
  · intro δ hδ
    set cδ : ℝ := δ / (1 + ‖z‖ + δ) with hcδ
    have hcδ0 : 0 < cδ := by rw [hcδ]; have := norm_nonneg z; exact div_pos hδ (by linarith)
    have hPm : MeasurableSet (upperHalf \ ball z δ) := hU.diff measurableSet_ball
    refine (hmaj.const_mul (M * (cδ ^ 2 * cv ^ 2)⁻¹)).integrableOn.mono' ?_ ?_
    · refine ContinuousOn.aestronglyMeasurable ?_ hPm
      refine ((hμc.mono sdiff_subset).mul (continuousOn_const.div (by fun_prop) fun u hu => ?_)).mul
        (continuousOn_const.div (by fun_prop) fun u hu => pow_ne_zero _ (hne_vb u hu.1))
      refine pow_ne_zero _ (sub_ne_zero.mpr fun h => hu.2 ?_)
      rw [← h]
      exact mem_ball_self hδ
    · filter_upwards [ae_restrict_mem hPm] with u hu
      have hd : δ ≤ ‖u - z‖ := by
        have := hu.2; rw [mem_ball, dist_eq_norm, not_lt] at this; exact this
      have r := e64_t10_rat hcδ0 hcv0 (e64_t10_lower hδ hd) (hlv u hu.1) 2 2
      rw [show (2 + 2 : ℕ) = 4 from rfl] at r
      have e : μ u * (1 / (z - u) ^ 2) * (1 / (u - conj v) ^ 2) = μ u * (1 / ((u - z) ^ 2 * (u - conj v) ^ 2)) := by
        rw [show (z - u) ^ 2 = (u - z) ^ 2 by ring, mul_assoc, one_div_mul_one_div]
      rw [e, norm_mul]
      calc ‖μ u‖ * ‖1 / ((u - z) ^ 2 * (u - conj v) ^ 2)‖ ≤ M * ((cδ ^ 2 * cv ^ 2)⁻¹ * ((1 + ‖u‖) ^ 4)⁻¹) :=
            mul_le_mul (hM u hu.1) r (norm_nonneg _) hM0
        _ = M * (cδ ^ 2 * cv ^ 2)⁻¹ * ((1 + ‖u‖) ^ 4)⁻¹ := by ring

/-- **(E9)** `∂_ε` at `0` of the `eq_1_25` integrand, at a fixed `v ≠ z`, is `-(1/π)` times the inner principal
value of (6.4) (`e124_eq_1_25`, `e124_eq_1_24` at `ε = 0`, `w_0 = id`; E10 for existence of the limit). -/
theorem e64_dz_pointwise {μ φ : ℂ → ℂ} (hμ : IsHarmonicU μ φ) {z : ℂ} (hz : z ∈ upperHalf) {v : ℂ}
    (hv : v ∈ upperHalf) (hvz : v ≠ z) :
    dz (fun e => conj (μ v) * kernelKbar (fun y => e * μ y) z v * kernelKbarbar (fun y => e * μ y) v z) 0 =
      -(1 / π) * limUnder (𝓝[>] (0 : ℝ)) fun δ => ∫ u in upperHalfPunct z δ,
        μ u * conj (μ v) * (1 / ((u - conj v) ^ 2 * (z - conj v) ^ 2 * (u - conj z) ^ 2) +
          1 / ((u - z) ^ 2 * (u - conj v) ^ 2 * (conj z - conj v) ^ 2)) := by
  obtain ⟨M, hM0, hM⟩ := harmonicU_bounded hμ
  have hU := measurableSet_upperHalf_aux
  have hm : AEStronglyMeasurable μ (volume.restrict upperHalf) :=
    (harmonicU_continuousOn hμ).aestronglyMeasurable hU
  have hμb : IsBeltramiCoeff μ upperHalf M := ⟨hm, (ae_restrict_mem hU).mono fun u hu => hM u hu⟩
  have hμs := wr_isHarmonicU_contDiffOn hμ
  have hε0 : ‖(0 : ℂ)‖ * M < 1 := by simp
  have hzim : 0 < z.im := hz
  have hvim : 0 < v.im := hv
  have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 Real.pi_ne_zero
  have hzv : z - conj v ≠ 0 := fun h => by
    have := congrArg Complex.im h; simp at this; linarith
  have hzv' : conj z - conj v ≠ 0 := fun h => hvz (by
    have e := congrArg conj (sub_eq_zero.mp h); simp only [Complex.conj_conj] at e; exact e.symm)
  have hvz' : conj v - conj z ≠ 0 := fun h => hzv' (by rw [← neg_sub, h, neg_zero])
  set c := conj (μ v) with hc
  by_cases hc0 : c = 0
  · have hl : (fun e => c * kernelKbar (fun y => e * μ y) z v * kernelKbarbar (fun y => e * μ y) v z) =
        fun _ => (0 : ℂ) := by funext e; rw [hc0]; ring
    have hr : (fun δ : ℝ => ∫ u in upperHalfPunct z δ, μ u * c *
        (1 / ((u - conj v) ^ 2 * (z - conj v) ^ 2 * (u - conj z) ^ 2) +
          1 / ((u - z) ^ 2 * (u - conj v) ^ 2 * (conj z - conj v) ^ 2))) = fun _ => (0 : ℂ) := by
      funext δ; rw [hc0]; simp
    rw [hl, hr, tendsto_const_nhds.limUnder_eq, (e124_dz_eventuallyConst (Eventually.of_forall fun _ => rfl)).1]
    ring
  -- differentiability of the two kernels at `0`
  have hw0 := e64_t9_w0 μ
  obtain ⟨hwz, hdz⟩ := e124_E2_diff hM0 hμb hμs hε0 hz
  obtain ⟨hwv, hdv⟩ := e124_E2_diff hM0 hμb hμs hε0 hv
  have hdv' : DifferentiableAt ℝ (fun e => conj (dz (wU fun y => e * μ y) v)) 0 :=
    Complex.conjCLE.differentiableAt.comp 0 hdv
  have hwv' : DifferentiableAt ℝ (fun e => conj (wU (fun x => e * μ x) v)) 0 :=
    Complex.conjCLE.differentiableAt.comp 0 hwv
  have hKb : DifferentiableAt ℝ (fun e => kernelKbar (fun y => e * μ y) z v) 0 := by
    unfold kernelKbar
    have hn : DifferentiableAt ℝ (fun e => dz (wU fun y => e * μ y) z * conj (dz (wU fun y => e * μ y) v)) 0 :=
      hdz.mul hdv'
    have hd : DifferentiableAt ℝ (fun e => (wU (fun y => e * μ y) z - conj (wU (fun y => e * μ y) v)) ^ 2) 0 :=
      (hwz.sub hwv').pow 2
    refine (hn.mul (hd.inv ?_)).congr_of_eventuallyEq (Eventually.of_forall fun e => div_eq_mul_inv _ _)
    simp only [hw0, id]
    exact pow_ne_zero 2 hzv
  have hK : DifferentiableAt ℝ (fun e => kernelK (fun y => e * μ y) v z) 0 := by
    unfold kernelK
    have hn : DifferentiableAt ℝ (fun e => dz (wU fun y => e * μ y) v * dz (wU fun y => e * μ y) z) 0 :=
      hdv.mul hdz
    have hd : DifferentiableAt ℝ (fun e => (wU (fun y => e * μ y) v - wU (fun y => e * μ y) z) ^ 2) 0 :=
      (hwv.sub hwz).pow 2
    refine (hn.mul (hd.inv ?_)).congr_of_eventuallyEq (Eventually.of_forall fun e => div_eq_mul_inv _ _)
    simp only [hw0, id]
    exact pow_ne_zero 2 (sub_ne_zero.mpr hvz)
  have hKbb : DifferentiableAt ℝ (fun e => kernelKbarbar (fun y => e * μ y) v z) 0 := by
    unfold kernelKbarbar
    exact Complex.conjCLE.differentiableAt.comp 0 hK
  have hcK : DifferentiableAt ℝ (fun e => c * kernelKbar (fun y => e * μ y) z v) 0 :=
    (differentiableAt_const c).mul hKb
  have d1 := (e124_eq_1_25 hM0 hμb hμs hε0 hz hv).1
  have d2 : dz (fun e => kernelKbarbar (fun y => e * μ y) v z) 0 =
      conj (dzbar (fun e => kernelK (fun y => e * μ y) v z) 0) := by
    unfold kernelKbarbar
    exact dz_conj hK
  rw [(e124_eq_1_24 hM0 hμb hμs hε0 hv hz hvz).2] at d2
  have hdc : dz (fun e => c * kernelKbar (fun y => e * μ y) z v) 0 =
      c * dz (fun e => kernelKbar (fun y => e * μ y) z v) 0 := by
    rw [e64_t9_dz_mul (differentiableAt_const c) hKb, (e124_dz_eventuallyConst (Eventually.of_forall fun _ => rfl)).1]
    ring
  rw [e64_t9_dz_mul hcK hKbb, hdc, d1, d2]
  -- values at `0`
  obtain ⟨-, hKb0, -⟩ := e64_t9_K0 μ z v
  obtain ⟨-, -, hKbb0⟩ := e64_t9_K0 μ v z
  rw [hKb0, hKbb0]
  have hf1 : (fun u => μ u * kernelK (fun y => (0 : ℂ) * μ y) z u * kernelKbar (fun y => (0 : ℂ) * μ y) u v) =
      fun u => μ u * (1 / (z - u) ^ 2) * (1 / (u - conj v) ^ 2) := by
    funext u; rw [(e64_t9_K0 μ z u).1, (e64_t9_K0 μ u v).2.1]
  have hf2 : (fun u => conj (μ u) * kernelKbar (fun y => (0 : ℂ) * μ y) v u * kernelKbar (fun y => (0 : ℂ) * μ y) z u) =
      fun u => conj (μ u) * (1 / (v - conj u) ^ 2) * (1 / (z - conj u) ^ 2) := by
    funext u; rw [(e64_t9_K0 μ v u).2.1, (e64_t9_K0 μ z u).2.1]
  rw [hf1, hf2]
  -- the integrability facts
  obtain ⟨hI1, hI2⟩ := e64_t9_int hμ hz hv
  set I1 : ℂ := ∫ u in upperHalf, μ u / ((u - conj v) ^ 2 * (u - conj z) ^ 2) with hI1d
  have hP2i : IntegrableOn (fun u => conj (μ u) * (1 / (v - conj u) ^ 2) * (1 / (z - conj u) ^ 2)) upperHalf := by
    refine (e124a_conj_int hI1).congr_fun (fun u hu => ?_) hU
    have hu' : 0 < u.im := hu
    have n1 : u - conj v ≠ 0 := fun h => by have := congrArg Complex.im h; simp at this; linarith
    have n2 : u - conj z ≠ 0 := fun h => by have := congrArg Complex.im h; simp at this; linarith
    have n3 : conj u - v ≠ 0 := fun h => by have := congrArg Complex.im h; simp at this; linarith
    have n4 : conj u - z ≠ 0 := fun h => by have := congrArg Complex.im h; simp at this; linarith
    simp only [map_div₀, map_mul, map_pow, map_sub, Complex.conj_conj]
    have n5 : v - conj u ≠ 0 := fun h => n3 (by rw [← neg_sub, h, neg_zero])
    have n6 : z - conj u ≠ 0 := fun h => n4 (by rw [← neg_sub, h, neg_zero])
    field_simp
    ring
  have hP2 : pv2 (fun u => conj (μ u) * (1 / (v - conj u) ^ 2) * (1 / (z - conj u) ^ 2)) v z =
      ∫ u in upperHalf, conj (μ u) * (1 / (v - conj u) ^ 2) * (1 / (z - conj u) ^ 2) :=
    (e124a_reg2 v z hP2i).limUnder_eq
  have hcP2 : conj (∫ u in upperHalf, conj (μ u) * (1 / (v - conj u) ^ 2) * (1 / (z - conj u) ^ 2)) = I1 := by
    rw [← integral_conj]
    refine setIntegral_congr_fun hU (fun u hu => ?_)
    have hu' : 0 < u.im := hu
    have n1 : u - conj v ≠ 0 := fun h => by have := congrArg Complex.im h; simp at this; linarith
    have n2 : u - conj z ≠ 0 := fun h => by have := congrArg Complex.im h; simp at this; linarith
    have n3 : conj u - v ≠ 0 := fun h => by have := congrArg Complex.im h; simp at this; linarith
    have n4 : conj u - z ≠ 0 := fun h => by have := congrArg Complex.im h; simp at this; linarith
    simp only [map_div₀, map_mul, map_pow, map_sub, map_one, Complex.conj_conj]
    have n7 : conj v - u ≠ 0 := fun h => n1 (by rw [← neg_sub, h, neg_zero])
    have n8 : conj z - u ≠ 0 := fun h => n2 (by rw [← neg_sub, h, neg_zero])
    field_simp
    ring
  -- `P1` via (E10)
  have hE := e64_inner_regular hμ hz hv hvz
  set Y : ℂ := ∫ u in upperHalf, μ u * c *
    (1 / ((u - conj v) ^ 2 * (z - conj v) ^ 2 * (u - conj z) ^ 2) +
      (z - conj z) / ((u - conj z) ^ 3 * (u - conj v) * (z - conj v) ^ 3)) with hYd
  have hpunct : ∀ δ : ℝ, upperHalfPunct z δ = upperHalf \ (ball z δ ∪ ball z δ) := fun δ => by
    rw [union_self]; rfl
  have tI1 : Tendsto (fun δ : ℝ => ∫ u in upperHalfPunct z δ, μ u / ((u - conj v) ^ 2 * (u - conj z) ^ 2))
      (𝓝[>] 0) (𝓝 I1) := by
    simpa only [hpunct] using e124a_reg2 z z hI1
  have hsplit : ∀ δ : ℝ, 0 < δ → (∫ u in upperHalfPunct z δ, μ u * c *
      (1 / ((u - conj v) ^ 2 * (z - conj v) ^ 2 * (u - conj z) ^ 2) +
        1 / ((u - z) ^ 2 * (u - conj v) ^ 2 * (conj z - conj v) ^ 2))) =
      c / (z - conj v) ^ 2 * (∫ u in upperHalfPunct z δ, μ u / ((u - conj v) ^ 2 * (u - conj z) ^ 2)) +
        c / (conj z - conj v) ^ 2 * ∫ u in upperHalf \ ball z δ, μ u * (1 / (z - u) ^ 2) * (1 / (u - conj v) ^ 2) := by
    intro δ hδ
    have hPm : MeasurableSet (upperHalfPunct z δ) := hU.diff measurableSet_ball
    have ia : IntegrableOn (fun u => c / (z - conj v) ^ 2 * (μ u / ((u - conj v) ^ 2 * (u - conj z) ^ 2)))
        (upperHalfPunct z δ) := (hI1.mono_set sdiff_subset).const_mul _
    have ib : IntegrableOn (fun u => c / (conj z - conj v) ^ 2 * (μ u * (1 / (z - u) ^ 2) * (1 / (u - conj v) ^ 2)))
        (upperHalfPunct z δ) := (hI2 δ hδ).const_mul _
    have hpt : ∀ u ∈ upperHalfPunct z δ, μ u * c *
        (1 / ((u - conj v) ^ 2 * (z - conj v) ^ 2 * (u - conj z) ^ 2) +
          1 / ((u - z) ^ 2 * (u - conj v) ^ 2 * (conj z - conj v) ^ 2)) =
        c / (z - conj v) ^ 2 * (μ u / ((u - conj v) ^ 2 * (u - conj z) ^ 2)) +
          c / (conj z - conj v) ^ 2 * (μ u * (1 / (z - u) ^ 2) * (1 / (u - conj v) ^ 2)) := by
      intro u hu0
      have hu : u ∈ upperHalf := hu0.1
      have hu' : 0 < u.im := hu
      have n1 : u - conj v ≠ 0 := fun h => by have := congrArg Complex.im h; simp at this; linarith
      have n2 : u - conj z ≠ 0 := fun h => by have := congrArg Complex.im h; simp at this; linarith
      have n3 : conj u - v ≠ 0 := fun h => by have := congrArg Complex.im h; simp at this; linarith
      have n4 : conj u - z ≠ 0 := fun h => by have := congrArg Complex.im h; simp at this; linarith
      have n9 : z - u ≠ 0 := fun h => hu0.2 (by rw [← sub_eq_zero.mp h]; exact mem_ball_self hδ)
      have n10 : u - z ≠ 0 := fun h => n9 (by rw [← neg_sub, h, neg_zero])
      field_simp
      ring
    rw [setIntegral_congr_fun hPm hpt, integral_add ia ib, integral_const_mul, integral_const_mul]
    rfl
  set L1 : ℂ := (conj z - conj v) ^ 2 / c * (2 * Y - c / (z - conj v) ^ 2 * I1) with hL1
  have tg : Tendsto (fun δ : ℝ => ∫ u in upperHalf \ ball z δ, μ u * (1 / (z - u) ^ 2) * (1 / (u - conj v) ^ 2))
      (𝓝[>] 0) (𝓝 L1) := by
    refine (((hE.sub (tI1.const_mul (c / (z - conj v) ^ 2))).const_mul ((conj z - conj v) ^ 2 / c))).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    rw [hsplit δ hδ]
    field_simp
    ring
  have hP1 : pv2 (fun u => μ u * (1 / (z - u) ^ 2) * (1 / (u - conj v) ^ 2)) z v = L1 :=
    (e124a_pv1 (fun h => hvz h.symm) tg fun δ hδ => hI2 δ hδ).limUnder_eq
  rw [hP1, hP2, hE.limUnder_eq]
  have hc' : conj (-(1 / (π : ℂ)) * ∫ u in upperHalf, conj (μ u) * (1 / (v - conj u) ^ 2) * (1 / (z - conj u) ^ 2)) =
      -(1 / (π : ℂ)) * I1 := by
    rw [map_mul, hcP2]
    simp [Complex.conj_ofReal]
  rw [hc', hL1]
  have hvzsq : (conj v - conj z) ^ 2 = (conj z - conj v) ^ 2 := by ring
  rw [hvzsq]
  field_simp
  ring

/-! ### E11 helpers (下属1) -/

/-- Separation of `𝕌` from a bounded part of `{Im ≤ -s}`, with linear growth in `|u|`. -/
theorem e64_sep {u w : ℂ} {s R : ℝ} (hs : 0 < s) (hR : 0 ≤ R) (hu : 0 ≤ u.im) (hw : w.im ≤ -s) (hwR : ‖w‖ ≤ R) :
    s / (1 + R + s) * (1 + ‖u‖) ≤ ‖u - w‖ := by
  have h1 : s ≤ ‖u - w‖ := by
    have h := Complex.abs_im_le_norm (u - w)
    rw [Complex.sub_im] at h
    have := le_abs_self (u.im - w.im)
    linarith
  have h2 : ‖u‖ - R ≤ ‖u - w‖ := by have := norm_sub_norm_le u w; linarith
  rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
  rcases le_total ‖u‖ (R + s) with h | h
  · nlinarith [mul_nonneg hs.le (sub_nonneg.mpr h),
      mul_le_mul_of_nonneg_right h1 (by positivity : (0 : ℝ) ≤ 1 + R + s)]
  · nlinarith [mul_nonneg (sub_nonneg.mpr h) (by positivity : (0 : ℝ) ≤ 1 + R),
      mul_le_mul_of_nonneg_right h2 (by positivity : (0 : ℝ) ≤ 1 + R + s)]

/-- Pointwise majorant of the regularized `(6.4)` integrand. -/
theorem e64_nc_pt {a b X Y Z w : ℂ} {M c t y0 : ℝ} (hc : 0 < c) (ht : 0 < t) (hy0 : 0 < y0)
    (ha : ‖a‖ ≤ M) (hb : ‖b‖ ≤ M) (hX : c * t ≤ ‖X‖) (hY : y0 ≤ ‖Y‖) (hZ : c * t ≤ ‖Z‖) :
    ‖a * conj b * (1 / (X ^ 2 * Y ^ 2 * Z ^ 2) + w / (Z ^ 3 * X * Y ^ 3))‖ ≤
      M * M * (1 / (c ^ 4 * y0 ^ 2) + ‖w‖ / (c ^ 4 * y0 ^ 3)) * (t ^ 4)⁻¹ := by
  have hct : 0 < c * t := mul_pos hc ht
  have h1 : ‖1 / (X ^ 2 * Y ^ 2 * Z ^ 2)‖ ≤ 1 / (c ^ 4 * y0 ^ 2) * (t ^ 4)⁻¹ := by
    rw [norm_div, norm_one, norm_mul, norm_mul, norm_pow, norm_pow, norm_pow]
    rw [show 1 / (c ^ 4 * y0 ^ 2) * (t ^ 4)⁻¹ = 1 / ((c * t) ^ 2 * y0 ^ 2 * (c * t) ^ 2) by field_simp]
    apply one_div_le_one_div_of_le (by positivity)
    exact mul_le_mul (mul_le_mul (pow_le_pow_left₀ hct.le hX 2) (pow_le_pow_left₀ hy0.le hY 2) (by positivity)
      (by positivity)) (pow_le_pow_left₀ hct.le hZ 2) (by positivity) (by positivity)
  have h2 : ‖w / (Z ^ 3 * X * Y ^ 3)‖ ≤ ‖w‖ / (c ^ 4 * y0 ^ 3) * (t ^ 4)⁻¹ := by
    rw [norm_div, norm_mul, norm_mul, norm_pow, norm_pow]
    rw [show ‖w‖ / (c ^ 4 * y0 ^ 3) * (t ^ 4)⁻¹ = ‖w‖ / ((c * t) ^ 3 * (c * t) * y0 ^ 3) by field_simp]
    exact div_le_div_of_nonneg_left (norm_nonneg _) (by positivity)
      (mul_le_mul (mul_le_mul (pow_le_pow_left₀ hct.le hZ 3) hX hct.le (by positivity))
        (pow_le_pow_left₀ hy0.le hY 3) (by positivity) (by positivity))
  have hM : 0 ≤ M := (norm_nonneg _).trans ha
  rw [norm_mul, norm_mul, Complex.norm_conj]
  calc _ ≤ M * M * (1 / (c ^ 4 * y0 ^ 2) * (t ^ 4)⁻¹ + ‖w‖ / (c ^ 4 * y0 ^ 3) * (t ^ 4)⁻¹) :=
        mul_le_mul (mul_le_mul ha hb (norm_nonneg _) hM) ((norm_add_le _ _).trans (add_le_add h1 h2))
          (norm_nonneg _) (mul_nonneg hM hM)
    _ = _ := by ring

/-- **(E11)** The regularized inner integral is continuous in `v` on `𝕌` (dominated convergence; `|u - v̄| ≥ Im v`). -/
theorem e64_near_cont {μ φ : ℂ → ℂ} (hμ : IsHarmonicU μ φ) {z : ℂ} (hz : z ∈ upperHalf) :
    ContinuousOn (fun v => ∫ u in upperHalf, μ u * conj (μ v) *
        (1 / ((u - conj v) ^ 2 * (z - conj v) ^ 2 * (u - conj z) ^ 2) +
          (z - conj z) / ((u - conj z) ^ 3 * (u - conj v) * (z - conj v) ^ 3))) upperHalf := by
  obtain ⟨M, hM0, hM⟩ := harmonicU_bounded hμ
  have hU := measurableSet_upperHalf_aux
  have hUo : IsOpen upperHalf := isOpen_lt continuous_const Complex.continuous_im
  have hμc := harmonicU_continuousOn hμ
  have hm : AEStronglyMeasurable μ (volume.restrict upperHalf) := hμc.aestronglyMeasurable hU
  have hcm : Measurable (conj : ℂ → ℂ) := Complex.continuous_conj.measurable
  have hzim : 0 < z.im := hz
  intro v₀ hv₀
  have hv₀im : 0 < v₀.im := hv₀
  refine ContinuousAt.continuousWithinAt ?_
  set s := min (v₀.im / 2) z.im with hsd
  set R := ‖v₀‖ + v₀.im + ‖z‖ with hRd
  have hs : 0 < s := lt_min (half_pos hv₀im) hzim
  have hR : 0 ≤ R := by positivity
  set c := s / (1 + R + s) with hcd
  have hc : 0 < c := by positivity
  set K := M * M * (1 / (c ^ 4 * z.im ^ 2) + ‖z - conj z‖ / (c ^ 4 * z.im ^ 3)) with hKd
  have hint : Integrable (fun u : ℂ => K * (1 + ‖u‖) ^ (-(4 : ℝ))) (volume.restrict upperHalf) :=
    ((integrable_one_add_norm (by rw [Complex.finrank_real_complex]; norm_num)).const_mul K).integrableOn
  have hmeas : ∀ᶠ v in 𝓝 v₀, AEStronglyMeasurable (fun u => μ u * conj (μ v) *
      (1 / ((u - conj v) ^ 2 * (z - conj v) ^ 2 * (u - conj z) ^ 2) +
        (z - conj z) / ((u - conj z) ^ 3 * (u - conj v) * (z - conj v) ^ 3))) (volume.restrict upperHalf) :=
    Eventually.of_forall fun v => (hm.mul_const (conj (μ v))).mul (Measurable.aestronglyMeasurable (by fun_prop))
  have hbound : ∀ᶠ v in 𝓝 v₀, ∀ᵐ u ∂(volume.restrict upperHalf), ‖μ u * conj (μ v) *
      (1 / ((u - conj v) ^ 2 * (z - conj v) ^ 2 * (u - conj z) ^ 2) +
        (z - conj z) / ((u - conj z) ^ 3 * (u - conj v) * (z - conj v) ^ 3))‖ ≤
        K * (1 + ‖u‖) ^ (-(4 : ℝ)) := by
    filter_upwards [ball_mem_nhds v₀ (half_pos hv₀im)] with v hv
    filter_upwards [ae_restrict_mem hU] with u hu
    have huim : 0 < u.im := hu
    have hvd : ‖v - v₀‖ < v₀.im / 2 := by rwa [mem_ball, dist_eq_norm] at hv
    have hvim : v₀.im / 2 ≤ v.im := by
      have h := Complex.abs_im_le_norm (v - v₀)
      rw [Complex.sub_im] at h
      have := neg_abs_le (v.im - v₀.im)
      linarith
    have hvR : ‖conj v‖ ≤ R := by
      rw [Complex.norm_conj]
      have := norm_le_insert' v v₀
      linarith [norm_nonneg z]
    have hvU : v ∈ upperHalf := show 0 < v.im by linarith
    have hcv : (conj v).im ≤ -s := by rw [Complex.conj_im]; linarith [min_le_left (v₀.im / 2) z.im]
    have hcz : (conj z).im ≤ -s := by rw [Complex.conj_im]; linarith [min_le_right (v₀.im / 2) z.im]
    have hzR : ‖conj z‖ ≤ R := by rw [Complex.norm_conj]; linarith [norm_nonneg v₀]
    have hY : z.im ≤ ‖z - conj v‖ := by
      have h := Complex.abs_im_le_norm (z - conj v)
      rw [Complex.sub_im, Complex.conj_im] at h
      have := le_abs_self (z.im - -v.im)
      linarith
    have hp : (1 + ‖u‖) ^ (-(4 : ℝ)) = ((1 + ‖u‖) ^ 4)⁻¹ := by
      rw [Real.rpow_neg (by positivity), show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    rw [hp, hKd]
    exact e64_nc_pt hc (by positivity) hzim (hM u hu) (hM v hvU) (e64_sep hs hR huim.le hcv hvR) hY
      (e64_sep hs hR huim.le hcz hzR)
  have hcont : ∀ᵐ u ∂(volume.restrict upperHalf), ContinuousAt (fun v => μ u * conj (μ v) *
      (1 / ((u - conj v) ^ 2 * (z - conj v) ^ 2 * (u - conj z) ^ 2) +
        (z - conj z) / ((u - conj z) ^ 3 * (u - conj v) * (z - conj v) ^ 3))) v₀ := by
    filter_upwards [ae_restrict_mem hU] with u hu
    have huim : 0 < u.im := hu
    have hμv : ContinuousAt μ v₀ := hμc.continuousAt (hUo.mem_nhds hv₀)
    have hcc : Continuous (fun v : ℂ => conj v) := Complex.continuous_conj
    have h1 : u - conj v₀ ≠ 0 := fun h => by
      have := congrArg Complex.im h
      rw [Complex.sub_im, Complex.conj_im, Complex.zero_im] at this
      linarith
    have h2 : z - conj v₀ ≠ 0 := fun h => by
      have := congrArg Complex.im h
      rw [Complex.sub_im, Complex.conj_im, Complex.zero_im] at this
      linarith
    have h3 : u - conj z ≠ 0 := fun h => by
      have := congrArg Complex.im h
      rw [Complex.sub_im, Complex.conj_im, Complex.zero_im] at this
      linarith
    have hA : Continuous (fun v : ℂ => (u - conj v) ^ 2 * (z - conj v) ^ 2 * (u - conj z) ^ 2) :=
      (((continuous_const.sub hcc).pow 2).mul ((continuous_const.sub hcc).pow 2)).mul continuous_const
    have hB : Continuous (fun v : ℂ => (u - conj z) ^ 3 * (u - conj v) * (z - conj v) ^ 3) :=
      (continuous_const.mul (continuous_const.sub hcc)).mul ((continuous_const.sub hcc).pow 3)
    have hAne : (u - conj v₀) ^ 2 * (z - conj v₀) ^ 2 * (u - conj z) ^ 2 ≠ 0 :=
      mul_ne_zero (mul_ne_zero (pow_ne_zero 2 h1) (pow_ne_zero 2 h2)) (pow_ne_zero 2 h3)
    have hBne : (u - conj z) ^ 3 * (u - conj v₀) * (z - conj v₀) ^ 3 ≠ 0 :=
      mul_ne_zero (mul_ne_zero (pow_ne_zero 3 h3) h1) (pow_ne_zero 3 h2)
    have hD1 : ContinuousAt (fun v : ℂ => 1 / ((u - conj v) ^ 2 * (z - conj v) ^ 2 * (u - conj z) ^ 2)) v₀ :=
      continuousAt_const.div hA.continuousAt hAne
    have hD2 : ContinuousAt (fun v : ℂ => (z - conj z) / ((u - conj z) ^ 3 * (u - conj v) * (z - conj v) ^ 3)) v₀ :=
      continuousAt_const.div hB.continuousAt hBne
    have hC : ContinuousAt (fun v : ℂ => μ u * conj (μ v)) v₀ :=
      continuousAt_const.mul (Complex.continuous_conj.continuousAt.comp hμv)
    exact hC.mul (hD1.add hD2)
  exact continuousAt_of_dominated hmeas hbound hint hcont

/-! ### The original statements (byte-identical copies) -/

/-- **(6.4)** (TT:2619). The singular integral representation of the second variation, for `μ ∈ Ω^{-1,1}(𝕌)` and
`z ∈ 𝕌`: `L_μ L_{μ̄} ρ(z)` equals
`-(4/π²) ∬∬_{𝕌×𝕌} μ(u) \overline{μ(v)} (1/((u - v̄)²(z - v̄)²(u - z̄)²) + 1/((u - z)²(u - v̄)²(z̄ - v̄)²)) d²u d²v`.
The `u`-integral is a principal value at `u = z`. -/
theorem e64_eq_6_4 {μ φ : ℂ → ℂ} (hμ : IsHarmonicU μ φ) {z : ℂ} (hz : z ∈ upperHalf) :
    dz (dzbar fun ε => rhoVar μ ε z) 0 =
      -(4 / π ^ 2) * ∫ v in upperHalf, limUnder (𝓝[>] (0 : ℝ)) fun δ => ∫ u in upperHalfPunct z δ,
        μ u * conj (μ v) * (1 / ((u - conj v) ^ 2 * (z - conj v) ^ 2 * (u - conj z) ^ 2) +
          1 / ((u - z) ^ 2 * (u - conj v) ^ 2 * (conj z - conj v) ^ 2)) := by
  obtain ⟨M, hM0, hM⟩ := harmonicU_bounded hμ
  have hU := measurableSet_upperHalf_aux
  have hm : AEStronglyMeasurable μ (volume.restrict upperHalf) :=
    (harmonicU_continuousOn hμ).aestronglyMeasurable hU
  have hμb : IsBeltramiCoeff μ upperHalf M := ⟨hm, (ae_restrict_mem hU).mono fun u hu => hM u hu⟩
  have hμs := wr_isHarmonicU_contDiffOn hμ
  have hUo : IsOpen upperHalf := isOpen_lt continuous_const Complex.continuous_im
  obtain ⟨hint, hlim⟩ := e64_core hM0 hμb hμs hz
  set X : ℂ → ℂ := fun v => limUnder (𝓝[>] (0 : ℝ)) fun δ => ∫ u in upperHalfPunct z δ,
    μ u * conj (μ v) * (1 / ((u - conj v) ^ 2 * (z - conj v) ^ 2 * (u - conj z) ^ 2) +
      1 / ((u - z) ^ 2 * (u - conj v) ^ 2 * (conj z - conj v) ^ 2)) with hX
  set Y : ℂ → ℂ := fun v => ∫ u in upperHalf, μ u * conj (μ v) *
    (1 / ((u - conj v) ^ 2 * (z - conj v) ^ 2 * (u - conj z) ^ 2) +
      (z - conj z) / ((u - conj z) ^ 3 * (u - conj v) * (z - conj v) ^ 3)) with hY
  set D : ℂ → ℂ := fun v => dz (fun e => conj (μ v) * kernelKbar (fun y => e * μ y) z v *
    kernelKbarbar (fun y => e * μ y) v z) 0 with hD
  have hXY : ∀ v ∈ upperHalf, v ≠ z → X v = 2 * Y v := fun v hv hvz =>
    (e64_inner_regular hμ hz hv hvz).limUnder_eq
  have hDX : ∀ v ∈ upperHalf, v ≠ z → D v = -(1 / π) * X v := fun v hv hvz =>
    e64_dz_pointwise hμ hz hv hvz
  have hzim : 0 < z.im := hz
  -- a closed disc around `z` inside `𝕌`
  set ρ : ℝ := z.im / 2 with hρ
  have hρ0 : 0 < ρ := by positivity
  have hcb : closedBall z ρ ⊆ upperHalf := by
    intro v hv
    have h1 : |(v - z).im| ≤ ‖v - z‖ := Complex.abs_im_le_norm _
    rw [mem_closedBall, dist_eq_norm] at hv
    have h2 : (v - z).im = v.im - z.im := by simp
    rw [h2] at h1
    show 0 < v.im
    have := neg_abs_le (v.im - z.im)
    linarith
  -- `X` is integrable on `𝕌`
  have hnull : ∀ᵐ v ∂(volume : Measure ℂ), v ≠ z := compl_mem_ae_iff.mpr (measure_singleton z)
  have hXfar : IntegrableOn X (upperHalf \ ball z ρ) := by
    have hDi : IntegrableOn (fun v => -(π : ℂ) * D v) (upperHalf \ ball z ρ) :=
      (hint ρ hρ0).const_mul (-(π : ℂ))
    refine IntegrableOn.congr_fun hDi (fun v hv => ?_) (hU.diff measurableSet_ball)
    have hvz : v ≠ z := fun h => hv.2 (h ▸ mem_ball_self hρ0)
    show -(π : ℂ) * D v = X v
    rw [hDX v hv.1 hvz]
    have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 Real.pi_ne_zero
    field_simp
  have hXnear : IntegrableOn X (closedBall z ρ) := by
    have hYc : ContinuousOn Y (closedBall z ρ) := (e64_near_cont hμ hz).mono hcb
    have hYi : IntegrableOn (fun v => 2 * Y v) (closedBall z ρ) :=
      ((hYc.const_smul (2 : ℂ)).integrableOn_compact (isCompact_closedBall z ρ))
    refine hYi.congr_fun_ae ?_
    filter_upwards [ae_restrict_mem measurableSet_closedBall, ae_restrict_of_ae hnull] with v hv hvz
    exact (hXY v (hcb hv) hvz).symm
  have hXi : IntegrableOn X upperHalf := by
    have hsplit : upperHalf ⊆ (upperHalf \ ball z ρ) ∪ closedBall z ρ := by
      intro v hv
      by_cases h : v ∈ ball z ρ
      · exact Or.inr (ball_subset_closedBall h)
      · exact Or.inl ⟨hv, h⟩
    exact (hXfar.union hXnear).mono_set hsplit
  -- the truncations of `X` converge to `∫ X`, and to `-π (π/4) L`
  have hT1 : Tendsto (fun δ : ℝ => ∫ v in upperHalf \ ball z δ, X v) (𝓝[>] 0) (𝓝 (∫ v in upperHalf, X v)) := by
    have h := e124a_reg2 z z hXi
    simpa only [union_self] using h
  have hT2 : Tendsto (fun δ : ℝ => ∫ v in upperHalf \ ball z δ, X v) (𝓝[>] 0)
      (𝓝 (-(π : ℂ) * ((π / 4) * dz (dzbar fun ε => rhoVar μ ε z) 0))) := by
    refine (hlim.const_mul (-(π : ℂ))).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    rw [← integral_const_mul]
    refine setIntegral_congr_fun (hU.diff measurableSet_ball) (fun v hv => ?_)
    have hvz : v ≠ z := fun h => hv.2 (h ▸ mem_ball_self hδ)
    show -(π : ℂ) * D v = X v
    rw [hDX v hv.1 hvz]
    have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 Real.pi_ne_zero
    field_simp
  have he := tendsto_nhds_unique hT2 hT1
  have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 Real.pi_ne_zero
  show dz (dzbar fun ε => rhoVar μ ε z) 0 = -(4 / (π : ℂ) ^ 2) * ∫ v in upperHalf, X v
  rw [← he]
  field_simp

/-- (TT:2637) The regularized representation (ordinary integrals), for `μ ∈ Ω^{-1,1}(𝕌)` and `z ∈ 𝕌`:
`L_μ L_{μ̄} ρ(z)` equals
`-(8/π²) ∬∬ μ(u) \overline{μ(v)} (1/((u - v̄)²(z - v̄)²(u - z̄)²) + (z - z̄)/((u - z̄)³(u - v̄)(z - v̄)³)) d²u d²v`. -/
theorem e64_eq_6_4_regular {μ φ : ℂ → ℂ} (hμ : IsHarmonicU μ φ) {z : ℂ} (hz : z ∈ upperHalf) :
    dz (dzbar fun ε => rhoVar μ ε z) 0 =
      -(8 / π ^ 2) * ∫ v in upperHalf, ∫ u in upperHalf, μ u * conj (μ v) *
        (1 / ((u - conj v) ^ 2 * (z - conj v) ^ 2 * (u - conj z) ^ 2) +
          (z - conj z) / ((u - conj z) ^ 3 * (u - conj v) * (z - conj v) ^ 3)) := by
  have hU := measurableSet_upperHalf_aux
  have hnull : ∀ᵐ v ∂(volume : Measure ℂ), v ≠ z := compl_mem_ae_iff.mpr (measure_singleton z)
  rw [e64_eq_6_4 hμ hz]
  have hcongr : (∫ v in upperHalf, limUnder (𝓝[>] (0 : ℝ)) fun δ => ∫ u in upperHalfPunct z δ,
        μ u * conj (μ v) * (1 / ((u - conj v) ^ 2 * (z - conj v) ^ 2 * (u - conj z) ^ 2) +
          1 / ((u - z) ^ 2 * (u - conj v) ^ 2 * (conj z - conj v) ^ 2))) =
      ∫ v in upperHalf, 2 * ∫ u in upperHalf, μ u * conj (μ v) *
        (1 / ((u - conj v) ^ 2 * (z - conj v) ^ 2 * (u - conj z) ^ 2) +
          (z - conj z) / ((u - conj z) ^ 3 * (u - conj v) * (z - conj v) ^ 3)) := by
    refine setIntegral_congr_ae hU ?_
    filter_upwards [hnull] with v hvz hv
    exact (e64_inner_regular hμ hz hv hvz).limUnder_eq
  rw [hcongr, integral_const_mul]
  ring

/-- **Proposition 6.3** (TT:2584–2588). For every `μ ∈ Ω^{-1,1}(𝕌)`,
`L_μ L_{μ̄} ρ = ∂²/∂ε∂ε̄|_{ε=0} ρ^{εμ} = ρ G(|μ|²)` on `𝕌`. -/
theorem e64_prop_6_3 {μ φ : ℂ → ℂ} (hμ : IsHarmonicU μ φ) {z : ℂ} (hz : z ∈ upperHalf) :
    dz (dzbar fun ε => rhoVar μ ε z) 0 = rhoU z * resolventOpU (fun u => (‖μ u‖ ^ 2 : ℝ)) z := by
  have hf : (fun u => ((‖μ u‖ ^ 2 : ℝ) : ℂ)) = fun u => μ u * conj (μ u) := by
    funext u
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have hne : z - conj z ≠ 0 := by
    rw [Complex.sub_conj]
    have hy : 0 < z.im := hz
    exact mul_ne_zero (Complex.ofReal_ne_zero.mpr (by positivity)) I_ne_zero
  have hin : ∀ v : ℂ, (∫ u in upperHalf, μ u * conj (μ v) *
        ((z - conj z) ^ 2 / ((u - conj v) ^ 2 * (z - conj v) ^ 2 * (u - conj z) ^ 2) +
          (z - conj z) ^ 3 / ((u - conj z) ^ 3 * (u - conj v) * (z - conj v) ^ 3))) =
      (z - conj z) ^ 2 * ∫ u in upperHalf, μ u * conj (μ v) *
        (1 / ((u - conj v) ^ 2 * (z - conj v) ^ 2 * (u - conj z) ^ 2) +
          (z - conj z) / ((u - conj z) ^ 3 * (u - conj v) * (z - conj v) ^ 3)) := by
    intro v
    rw [← integral_const_mul]
    congr 1
    funext u
    ring
  have hout : (∫ v in upperHalf, ∫ u in upperHalf, μ u * conj (μ v) *
        ((z - conj z) ^ 2 / ((u - conj v) ^ 2 * (z - conj v) ^ 2 * (u - conj z) ^ 2) +
          (z - conj z) ^ 3 / ((u - conj z) ^ 3 * (u - conj v) * (z - conj v) ^ 3))) =
      (z - conj z) ^ 2 * ∫ v in upperHalf, ∫ u in upperHalf, μ u * conj (μ v) *
        (1 / ((u - conj v) ^ 2 * (z - conj v) ^ 2 * (u - conj z) ^ 2) +
          (z - conj z) / ((u - conj z) ^ 3 * (u - conj v) * (z - conj v) ^ 3)) := by
    rw [← integral_const_mul]
    congr 1
    funext v
    exact hin v
  rw [e64_eq_6_4_regular hμ hz, hf, cor_6_4 hμ hμ hz, rhoU_complex, hout]
  have hne2 : (z - conj z) ^ 2 ≠ 0 := pow_ne_zero 2 hne
  have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 Real.pi_ne_zero
  have hsc : ∀ J : ℂ, -(8 / (π : ℂ) ^ 2) * J = -4 / (z - conj z) ^ 2 * (2 / (π : ℂ) ^ 2 * ((z - conj z) ^ 2 * J)) := by
    intro J
    field_simp
    ring
  exact hsc _

/-- **(6.4)** (TT:2619). The singular integral representation of the second variation, for `μ ∈ Ω^{-1,1}(𝕌)` and
`z ∈ 𝕌`: `L_μ L_{μ̄} ρ(z)` equals
`-(4/π²) ∬∬_{𝕌×𝕌} μ(u) \overline{μ(v)} (1/((u - v̄)²(z - v̄)²(u - z̄)²) + 1/((u - z)²(u - v̄)²(z̄ - v̄)²)) d²u d²v`.
The `u`-integral is a principal value at `u = z`. -/
theorem eq_6_4 {μ φ : ℂ → ℂ} (hμ : IsHarmonicU μ φ) {z : ℂ} (hz : z ∈ upperHalf) :
    dz (dzbar fun ε => rhoVar μ ε z) 0 =
      -(4 / π ^ 2) * ∫ v in upperHalf, limUnder (𝓝[>] (0 : ℝ)) fun δ => ∫ u in upperHalfPunct z δ,
        μ u * conj (μ v) * (1 / ((u - conj v) ^ 2 * (z - conj v) ^ 2 * (u - conj z) ^ 2) +
          1 / ((u - z) ^ 2 * (u - conj v) ^ 2 * (conj z - conj v) ^ 2)) :=
  e64_eq_6_4 hμ hz

/-- (TT:2637) The regularized representation (ordinary integrals), for `μ ∈ Ω^{-1,1}(𝕌)` and `z ∈ 𝕌`:
`L_μ L_{μ̄} ρ(z)` equals
`-(8/π²) ∬∬ μ(u) \overline{μ(v)} (1/((u - v̄)²(z - v̄)²(u - z̄)²) + (z - z̄)/((u - z̄)³(u - v̄)(z - v̄)³)) d²u d²v`. -/
theorem eq_6_4_regular {μ φ : ℂ → ℂ} (hμ : IsHarmonicU μ φ) {z : ℂ} (hz : z ∈ upperHalf) :
    dz (dzbar fun ε => rhoVar μ ε z) 0 =
      -(8 / π ^ 2) * ∫ v in upperHalf, ∫ u in upperHalf, μ u * conj (μ v) *
        (1 / ((u - conj v) ^ 2 * (z - conj v) ^ 2 * (u - conj z) ^ 2) +
          (z - conj z) / ((u - conj z) ^ 3 * (u - conj v) * (z - conj v) ^ 3)) :=
  e64_eq_6_4_regular hμ hz

/-- **Proposition 6.3** (TT:2584–2588). For every `μ ∈ Ω^{-1,1}(𝕌)`,
`L_μ L_{μ̄} ρ = ∂²/∂ε∂ε̄|_{ε=0} ρ^{εμ} = ρ G(|μ|²)` on `𝕌`. -/
theorem prop_6_3 {μ φ : ℂ → ℂ} (hμ : IsHarmonicU μ φ) {z : ℂ} (hz : z ∈ upperHalf) :
    dz (dzbar fun ε => rhoVar μ ε z) 0 = rhoU z * resolventOpU (fun u => (‖μ u‖ ^ 2 : ℝ)) z :=
  e64_prop_6_3 hμ hz

end TakhtajanTeo
