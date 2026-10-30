import TakhtajanTeo.Ch1.S7First
import TakhtajanTeo.Ch1.L112

/-!
# Chapter 1, §7.1 — (7.4) (`s74_`, 下属6 + helpers)

`s74_eq_7_4` is a byte-identical copy of `eq_7_4` (S7; relocated by the leader).

**Route** (EQ74 re-triage, 2026-10-28). Write `T_δ(μ, ν)` for the symmetric cut-off integral and
`L(μ, ν) = ∬_𝕌 μ(u)/(u - z̄)² PV_v[ν(v)/((u - v)²(v - z̄)²)] d²u` for its limit (`s71_bridge72`, for all `A∞` data).
1. `T_δ(μ, ν) = T_δ(ν, μ)` (swap), so `L(μ, ν) = L(ν, μ)` (A).
2. **Nice data** (`|φ|, |ψ| ≤ K (1 + |u|)⁻⁴` on `𝕌`): the four-term split is genuine. For the half `I₁ + I₂` the
   `u`-integrals are exactly `0` when `closedBall v δ ⊆ 𝕌` (`l112_punct_zero`). On the strip `Im v ≤ δ`,
   `|ν(v)| ≤ 2K δ² (1 + |v|)⁻⁴` with `|F_δ| ≲ δ⁻²` and, using `|μ(u)| ≤ 2K Im(u)² ≤ 8K |u - v|²`, `|G_δ| ≲ δ⁻¹`; so the
   `v`-integrand is `O((1 + |v|)⁻⁴)` uniformly and eventually `0` pointwise: dominated convergence (B1). The half
   `I₃ + I₄` is `I₁ + I₂` for `(ν, μ)` after the swap (B2).
3. **Continuity of `L` in the first slot** under bounded pointwise convergence on `𝕌` (C2): dominated convergence with a
   constant-weight copy of the C2 majorant (C1).
4. **Approximation** (D): `φₙ(u) = φ(u + i/(n+1)) ((n+1) i/(u + (n+1) i))⁴` is nice, has the same `A∞` bound, and
   converges to `φ` on `𝕌`.
5. Assembly: `L(ν, μₙ) = lim_m L(νₘ, μₙ) = 0`, so `L(μₙ, ν) = 0` by (A), and `L(μ, ν) = lim_n L(μₙ, ν) = 0`.

No four-term splitting of a Bochner integral is used for general `A∞` data, and no uniform Cauchy estimate in `δ`.
-/

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal ComplexConjugate Classical Real
noncomputable section
namespace TakhtajanTeo
open LiZhongQC

/-! ### (A) Symmetry -/

/-- The cut-off domain `D_δ = (𝕌 × 𝕌) ∩ {δ ≤ |u - v|}` is swap invariant: `∬_{D_δ} F ∘ swap = ∬_{D_δ} F`, and
integrability on `D_δ` passes to `F ∘ swap`. -/
theorem s74_swapD (F : ℂ × ℂ → ℂ) (δ : ℝ) :
    (∫ p in (upperHalf ×ˢ upperHalf) ∩ {p : ℂ × ℂ | δ ≤ ‖p.1 - p.2‖}, F p.swap) =
        (∫ p in (upperHalf ×ˢ upperHalf) ∩ {p : ℂ × ℂ | δ ≤ ‖p.1 - p.2‖}, F p) ∧
      (IntegrableOn F ((upperHalf ×ˢ upperHalf) ∩ {p : ℂ × ℂ | δ ≤ ‖p.1 - p.2‖}) →
        IntegrableOn (fun p => F p.swap) ((upperHalf ×ˢ upperHalf) ∩ {p : ℂ × ℂ | δ ≤ ‖p.1 - p.2‖})) := by
  have hU := measurableSet_upperHalf_aux
  have hDm : MeasurableSet ((upperHalf ×ˢ upperHalf) ∩ {p : ℂ × ℂ | δ ≤ ‖p.1 - p.2‖}) :=
    (hU.prod hU).inter (isClosed_le continuous_const ((continuous_fst.sub continuous_snd).norm)).measurableSet
  have hsw : ∀ p : ℂ × ℂ, p.swap ∈ (upperHalf ×ˢ upperHalf) ∩ {p : ℂ × ℂ | δ ≤ ‖p.1 - p.2‖} ↔
      p ∈ (upperHalf ×ˢ upperHalf) ∩ {p : ℂ × ℂ | δ ≤ ‖p.1 - p.2‖} := by
    intro p
    simp only [mem_inter_iff, mem_prod, mem_setOf_eq, Prod.fst_swap, Prod.snd_swap]
    rw [norm_sub_rev]
    tauto
  have hind : (fun p => ((upperHalf ×ˢ upperHalf) ∩ {p : ℂ × ℂ | δ ≤ ‖p.1 - p.2‖}).indicator F p.swap) =
      ((upperHalf ×ˢ upperHalf) ∩ {p : ℂ × ℂ | δ ≤ ‖p.1 - p.2‖}).indicator (fun p => F p.swap) := by
    funext p
    by_cases hp : p ∈ (upperHalf ×ˢ upperHalf) ∩ {p : ℂ × ℂ | δ ≤ ‖p.1 - p.2‖}
    · rw [indicator_of_mem ((hsw p).2 hp), indicator_of_mem hp]
    · rw [indicator_of_notMem (fun h => hp ((hsw p).1 h)), indicator_of_notMem hp]
  refine ⟨?_, fun h => ?_⟩
  · rw [← integral_indicator hDm, ← integral_indicator hDm, ← hind, Measure.volume_eq_prod]
    exact integral_prod_swap _
  · refine (integrable_indicator_iff hDm).1 ?_
    rw [← hind, Measure.volume_eq_prod]
    have h' := (integrable_indicator_iff hDm).2 h
    rw [Measure.volume_eq_prod] at h'
    exact h'.swap

/-- **(A)** `[W6]` The symmetric cut-off integral is symmetric in `(μ, ν)` (swap `(u, v) ↦ (v, u)`; the domain and the
kernel are swap invariant). No hypotheses. -/
theorem s74_sym (μ ν : ℂ → ℂ) (z : ℂ) (δ : ℝ) :
    (∫ p in (upperHalf ×ˢ upperHalf) ∩ {p : ℂ × ℂ | δ ≤ ‖p.1 - p.2‖},
        μ p.1 * ν p.2 / ((p.1 - conj z) ^ 2 * (p.1 - p.2) ^ 2 * (p.2 - conj z) ^ 2)) =
      ∫ p in (upperHalf ×ˢ upperHalf) ∩ {p : ℂ × ℂ | δ ≤ ‖p.1 - p.2‖},
        ν p.1 * μ p.2 / ((p.1 - conj z) ^ 2 * (p.1 - p.2) ^ 2 * (p.2 - conj z) ^ 2) := by
  rw [← (s74_swapD (fun p : ℂ × ℂ => ν p.1 * μ p.2 /
    ((p.1 - conj z) ^ 2 * (p.1 - p.2) ^ 2 * (p.2 - conj z) ^ 2)) δ).1]
  congr 1
  funext p
  simp only [Prod.fst_swap, Prod.snd_swap]
  rw [show (p.2 - p.1) ^ 2 = (p.1 - p.2) ^ 2 by ring]
  ring

/-! ### (B) Nice data -/

/-- Nice data: `|μ(u)| ≤ 2K (Im u)² (1 + |u|)⁻⁴` on `𝕌`, with `K ≥ 0`. -/
theorem s74_nice_bd {μ φ : ℂ → ℂ} (hμ : IsHarmonicU μ φ)
    (hφn : ∃ K : ℝ, ∀ u ∈ upperHalf, ‖φ u‖ ≤ K * ((1 + ‖u‖) ^ 4)⁻¹) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ u ∈ upperHalf, ‖μ u‖ ≤ 2 * K * u.im ^ 2 * ((1 + ‖u‖) ^ 4)⁻¹ := by
  obtain ⟨K, hK⟩ := hφn
  have hI : I ∈ upperHalf := by
    show (0 : ℝ) < I.im
    simp
  have hK0 : 0 ≤ K := by
    by_contra hneg
    push Not at hneg
    have h1 : K * ((1 + ‖I‖) ^ 4)⁻¹ < 0 := mul_neg_of_neg_of_pos hneg (by positivity)
    linarith [(norm_nonneg _).trans (hK I hI)]
  refine ⟨K, hK0, fun u hu => ?_⟩
  rw [hμ.2.2 u hu, s71c2_A, norm_mul, Complex.norm_conj, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonpos (by nlinarith [sq_nonneg u.im])]
  have h1 := mul_le_mul_of_nonneg_left (hK u hu) (by positivity : (0 : ℝ) ≤ 2 * u.im ^ 2)
  nlinarith [h1]

/-- `(1 + |x|)^{-k}` is integrable on `ℂ` for `k ≥ 3`. -/
theorem s74_scal (k : ℕ) (hk : 3 ≤ k) : Integrable (fun x : ℂ => ((1 + ‖x‖) ^ k)⁻¹) := by
  have h := integrable_one_add_norm (E := ℂ) (μ := volume) (r := (k : ℝ))
    (by rw [Complex.finrank_real_complex]; exact_mod_cast (by omega : 2 < k))
  refine h.congr (Eventually.of_forall fun x => ?_)
  show (1 + ‖x‖) ^ (-(k : ℝ)) = ((1 + ‖x‖) ^ k)⁻¹
  rw [Real.rpow_neg (by positivity), Real.rpow_natCast]

/-- `x⁻ᵏ ≤ 2ᵏ δ⁻ᵏ (1 + x/δ)⁻ᵏ` for `0 < δ ≤ x`. -/
theorem s74_tail_pt (k : ℕ) {δ x : ℝ} (hδ : 0 < δ) (hx : δ ≤ x) :
    (x ^ k)⁻¹ ≤ 2 ^ k * (δ ^ k)⁻¹ * ((1 + x / δ) ^ k)⁻¹ := by
  have hx0 : 0 < x := hδ.trans_le hx
  have e1 : δ * (1 + x / δ) = δ + x := by field_simp
  calc (x ^ k)⁻¹ ≤ (((δ + x) / 2) ^ k)⁻¹ :=
        inv_anti₀ (by positivity) (pow_le_pow_left₀ (by positivity) (by linarith) k)
    _ = 2 ^ k * (δ ^ k)⁻¹ * ((1 + x / δ) ^ k)⁻¹ := by
        rw [← e1, div_pow, mul_pow, inv_div]
        field_simp

/-- **Tail integrals** `∬_{|u - a| ≥ δ} |u - a|⁻ᵏ ≤ C δ^{2-k}` (`k ≥ 3`; scaling `u - a = δ w`). -/
theorem s74_tail (k : ℕ) (hk : 3 ≤ k) : ∃ C : ℝ, 0 ≤ C ∧ ∀ a : ℂ, ∀ δ : ℝ, 0 < δ →
    IntegrableOn (fun u : ℂ => (‖u - a‖ ^ k)⁻¹) {u : ℂ | δ ≤ ‖u - a‖} ∧
      ∫ u in {u : ℂ | δ ≤ ‖u - a‖}, (‖u - a‖ ^ k)⁻¹ ≤ C * (δ ^ (k - 2))⁻¹ := by
  have hg := s74_scal k hk
  refine ⟨2 ^ k * ∫ x : ℂ, ((1 + ‖x‖) ^ k)⁻¹,
    mul_nonneg (by positivity) (integral_nonneg fun x => by positivity), fun a δ hδ => ?_⟩
  have hS : MeasurableSet {u : ℂ | δ ≤ ‖u - a‖} := measurableSet_le measurable_const (by fun_prop)
  have hn : ∀ u : ℂ, ‖δ⁻¹ • (u - a)‖ = ‖u - a‖ / δ := fun u => by
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hδ, inv_mul_eq_div]
  have hGi : Integrable (fun u : ℂ => 2 ^ k * (δ ^ k)⁻¹ * ((1 + ‖δ⁻¹ • (u - a)‖) ^ k)⁻¹) :=
    ((hg.comp_smul (inv_ne_zero hδ.ne')).comp_sub_right a).const_mul _
  have hpt : ∀ u ∈ {u : ℂ | δ ≤ ‖u - a‖},
      (‖u - a‖ ^ k)⁻¹ ≤ 2 ^ k * (δ ^ k)⁻¹ * ((1 + ‖δ⁻¹ • (u - a)‖) ^ k)⁻¹ := by
    intro u hu
    rw [hn u]
    exact s74_tail_pt k hδ hu
  have hmeas : AEStronglyMeasurable (fun u : ℂ => (‖u - a‖ ^ k)⁻¹) (volume.restrict {u : ℂ | δ ≤ ‖u - a‖}) :=
    (Measurable.aestronglyMeasurable (by fun_prop))
  have hI : IntegrableOn (fun u : ℂ => (‖u - a‖ ^ k)⁻¹) {u : ℂ | δ ≤ ‖u - a‖} :=
    hGi.integrableOn.mono' hmeas (ae_restrict_of_forall_mem hS fun u hu => by
      rw [Real.norm_of_nonneg (by positivity)]
      exact hpt u hu)
  refine ⟨hI, ?_⟩
  have hval : ∫ u : ℂ, 2 ^ k * (δ ^ k)⁻¹ * ((1 + ‖δ⁻¹ • (u - a)‖) ^ k)⁻¹ =
      2 ^ k * (∫ x : ℂ, ((1 + ‖x‖) ^ k)⁻¹) * (δ ^ (k - 2))⁻¹ := by
    rw [integral_const_mul, integral_sub_right_eq_self (fun u : ℂ => ((1 + ‖δ⁻¹ • u‖) ^ k)⁻¹) a,
      Measure.integral_comp_smul volume (fun x : ℂ => ((1 + ‖x‖) ^ k)⁻¹) δ⁻¹, Complex.finrank_real_complex, smul_eq_mul,
      inv_pow, inv_inv, abs_of_pos (by positivity)]
    have hk2 : δ ^ k = δ ^ (k - 2) * δ ^ 2 := by rw [← pow_add]; congr 1; omega
    rw [hk2]
    field_simp
  calc ∫ u in {u : ℂ | δ ≤ ‖u - a‖}, (‖u - a‖ ^ k)⁻¹
      ≤ ∫ u in {u : ℂ | δ ≤ ‖u - a‖}, 2 ^ k * (δ ^ k)⁻¹ * ((1 + ‖δ⁻¹ • (u - a)‖) ^ k)⁻¹ :=
        setIntegral_mono_on hI hGi.integrableOn hS hpt
    _ ≤ ∫ u : ℂ, 2 ^ k * (δ ^ k)⁻¹ * ((1 + ‖δ⁻¹ • (u - a)‖) ^ k)⁻¹ :=
        setIntegral_le_integral hGi (Eventually.of_forall fun u => by positivity)
    _ = 2 ^ k * (∫ x : ℂ, ((1 + ‖x‖) ^ k)⁻¹) * (δ ^ (k - 2))⁻¹ := hval

/-- The `u`-pieces of `I₁ + I₂` are integrable off `B(v, δ)`. -/
theorem s74_inner_int {μ φ : ℂ → ℂ} (hμ : IsHarmonicU μ φ) (v : ℂ) {δ : ℝ} (hδ : 0 < δ) (k : ℕ) (hk : 4 ≤ k) :
    IntegrableOn (fun u => μ u / (u - v) ^ k) (upperHalfPunct v δ) := by
  have hU := measurableSet_upperHalf_aux
  obtain ⟨M, hM0, hM⟩ := harmonicU_bounded hμ
  obtain ⟨C, -, hT⟩ := s74_tail k (by omega)
  have hsub : upperHalfPunct v δ ⊆ {u : ℂ | δ ≤ ‖u - v‖} := fun u hu => by
    have := hu.2
    rwa [mem_ball, dist_eq_norm, not_lt] at this
  have hPm : MeasurableSet (upperHalfPunct v δ) := hU.diff measurableSet_ball
  have hne : ∀ u ∈ upperHalfPunct v δ, (u - v) ^ k ≠ 0 := fun u hu => pow_ne_zero _ (by
    intro h
    have h1 := hsub hu
    simp only [mem_setOf_eq, h, norm_zero] at h1
    linarith)
  refine (((hT v δ hδ).1.mono_set hsub).const_mul M).mono' ?_ ?_
  · exact (((harmonicU_continuousOn hμ).mono sdiff_subset).div (Continuous.continuousOn (by fun_prop))
      hne).aestronglyMeasurable hPm
  · refine ae_restrict_of_forall_mem hPm fun u hu => ?_
    rw [norm_div, norm_pow, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right (hM u hu.1) (by positivity)

/-- **(B1)** `[W6]` For nice `μ, ν` the half `I₁ + I₂` of (7.4) is integrable on the cut-off domain and tends to `0`
(`l112_punct_zero` off the strip `Im v ≤ δ`, the strip bounds above, dominated convergence in `v`). -/
theorem s74_half {μ ν φ ψ : ℂ → ℂ} (hμ : IsHarmonicU μ φ) (hν : IsHarmonicU ν ψ)
    (hφn : ∃ K : ℝ, ∀ u ∈ upperHalf, ‖φ u‖ ≤ K * ((1 + ‖u‖) ^ 4)⁻¹)
    (hψn : ∃ K : ℝ, ∀ u ∈ upperHalf, ‖ψ u‖ ≤ K * ((1 + ‖u‖) ^ 4)⁻¹) {z : ℂ} (hz : z ∈ upperHalf) :
    (∀ δ : ℝ, 0 < δ → IntegrableOn (fun p : ℂ × ℂ =>
        (1 / ((p.1 - p.2) ^ 4 * (p.2 - conj z) ^ 2) - 2 / ((p.1 - p.2) ^ 5 * (p.2 - conj z))) * μ p.1 * ν p.2)
        ((upperHalf ×ˢ upperHalf) ∩ {p : ℂ × ℂ | δ ≤ ‖p.1 - p.2‖})) ∧
      Tendsto (fun δ : ℝ => ∫ p in (upperHalf ×ˢ upperHalf) ∩ {p : ℂ × ℂ | δ ≤ ‖p.1 - p.2‖},
        (1 / ((p.1 - p.2) ^ 4 * (p.2 - conj z) ^ 2) - 2 / ((p.1 - p.2) ^ 5 * (p.2 - conj z))) * μ p.1 * ν p.2)
        (𝓝[>] 0) (𝓝 0) := by
  have hU := measurableSet_upperHalf_aux
  have hzi : 0 < z.im := hz
  obtain ⟨Mμ, hMμ0, hMμ⟩ := harmonicU_bounded hμ
  obtain ⟨Kφ, hKφ0, hKφ⟩ := s74_nice_bd hμ hφn
  obtain ⟨Kψ, hKψ0, hKψ⟩ := s74_nice_bd hν hψn
  have hμc := harmonicU_continuousOn hμ
  have hνc := harmonicU_continuousOn hν
  obtain ⟨c, hc, hlow⟩ := s71c2_lower hz
  obtain ⟨C4, hC40, hT4⟩ := s74_tail 4 (by norm_num)
  obtain ⟨C3, hC30, hT3⟩ := s74_tail 3 (by norm_num)
  have hDm : ∀ δ : ℝ, MeasurableSet ((upperHalf ×ˢ upperHalf) ∩ {p : ℂ × ℂ | δ ≤ ‖p.1 - p.2‖}) := fun δ =>
    (hU.prod hU).inter (isClosed_le continuous_const ((continuous_fst.sub continuous_snd).norm)).measurableSet
  have hmem : ∀ δ : ℝ, ∀ u v : ℂ, (u, v) ∈ (upperHalf ×ˢ upperHalf) ∩ {p : ℂ × ℂ | δ ≤ ‖p.1 - p.2‖} ↔
      v ∈ upperHalf ∧ u ∈ upperHalfPunct v δ := by
    intro δ u v
    simp only [upperHalfPunct, mem_inter_iff, mem_prod, mem_setOf_eq, Set.mem_sdiff, mem_ball, dist_eq_norm, not_lt]
    tauto
  have hsub : ∀ v : ℂ, ∀ δ : ℝ, upperHalfPunct v δ ⊆ {u : ℂ | δ ≤ ‖u - v‖} := fun v δ u hu => by
    have := hu.2
    rwa [mem_ball, dist_eq_norm, not_lt] at this
  have hzc : ∀ v ∈ upperHalf, c ≤ ‖v - conj z‖ := fun v hv => by
    have := hlow v hv
    nlinarith [norm_nonneg v]
  -- the integrand and its inner integral at fixed `v`
  obtain ⟨f, hf⟩ : ∃ f : ℂ × ℂ → ℂ, f = fun p =>
      (1 / ((p.1 - p.2) ^ 4 * (p.2 - conj z) ^ 2) - 2 / ((p.1 - p.2) ^ 5 * (p.2 - conj z))) * μ p.1 * ν p.2 :=
    ⟨_, rfl⟩
  obtain ⟨E, hE⟩ : ∃ E : ℝ → ℂ → ℂ, E = fun δ v =>
      1 / (v - conj z) ^ 2 * (∫ u in upperHalfPunct v δ, μ u / (u - v) ^ 4) -
        2 / (v - conj z) * ∫ u in upperHalfPunct v δ, μ u / (u - v) ^ 5 := ⟨_, rfl⟩
  -- (i) integrability on `D_δ`
  have hInt : ∀ δ : ℝ, 0 < δ →
      IntegrableOn f ((upperHalf ×ˢ upperHalf) ∩ {p : ℂ × ℂ | δ ≤ ‖p.1 - p.2‖}) := by
    intro δ hδ
    set B : ℝ := Mμ * (2 * Kψ) * (2 ^ 4 * (δ ^ 4)⁻¹) * ((c ^ 2)⁻¹ + 2 * δ⁻¹ * c⁻¹) with hB
    have hΦ : Integrable (fun p : ℂ × ℂ => B * (((1 + ‖δ⁻¹ • (p.1 - p.2)‖) ^ 4)⁻¹ * ((1 + ‖p.2‖) ^ 3)⁻¹))
        ((volume : Measure ℂ).prod volume) := by
      refine Integrable.const_mul ?_ B
      have hm : AEStronglyMeasurable (fun p : ℂ × ℂ => ((1 + ‖δ⁻¹ • (p.1 - p.2)‖) ^ 4)⁻¹ *
          ((1 + ‖p.2‖) ^ 3)⁻¹) ((volume : Measure ℂ).prod volume) :=
        Measurable.aestronglyMeasurable (by fun_prop)
      rw [integrable_prod_iff' hm]
      have hin : ∀ v : ℂ, Integrable (fun u : ℂ => ((1 + ‖δ⁻¹ • (u - v)‖) ^ 4)⁻¹) :=
        fun v => ((s74_scal 4 (by norm_num)).comp_smul (inv_ne_zero hδ.ne')).comp_sub_right v
      refine ⟨Eventually.of_forall fun v => (hin v).mul_const ((1 + ‖v‖) ^ 3)⁻¹, ?_⟩
      have e : (fun v : ℂ => ∫ u : ℂ, ‖((1 + ‖δ⁻¹ • ((u, v).1 - (u, v).2)‖) ^ 4)⁻¹ * ((1 + ‖(u, v).2‖) ^ 3)⁻¹‖) =
          fun v => (∫ u : ℂ, ((1 + ‖δ⁻¹ • u‖) ^ 4)⁻¹) * ((1 + ‖v‖) ^ 3)⁻¹ := by
        funext v
        have e2 : (fun u : ℂ => ‖((1 + ‖δ⁻¹ • ((u, v).1 - (u, v).2)‖) ^ 4)⁻¹ * ((1 + ‖(u, v).2‖) ^ 3)⁻¹‖) =
            fun u => ((1 + ‖δ⁻¹ • (u - v)‖) ^ 4)⁻¹ * ((1 + ‖v‖) ^ 3)⁻¹ := by
          funext u
          exact Real.norm_of_nonneg (by positivity)
        rw [e2, integral_mul_const, integral_sub_right_eq_self (fun u : ℂ => ((1 + ‖δ⁻¹ • u‖) ^ 4)⁻¹) v]
      rw [e]
      exact (s74_scal 3 (by norm_num)).const_mul _
    have hfc : ContinuousOn f ((upperHalf ×ˢ upperHalf) ∩ {p : ℂ × ℂ | δ ≤ ‖p.1 - p.2‖}) := by
      have hne1 : ∀ p ∈ (upperHalf ×ˢ upperHalf) ∩ {p : ℂ × ℂ | δ ≤ ‖p.1 - p.2‖}, p.1 - p.2 ≠ 0 := by
        intro p hp h
        have h1 : δ ≤ ‖p.1 - p.2‖ := hp.2
        rw [h, norm_zero] at h1
        linarith
      have hne2 : ∀ p ∈ (upperHalf ×ˢ upperHalf) ∩ {p : ℂ × ℂ | δ ≤ ‖p.1 - p.2‖}, p.2 - conj z ≠ 0 :=
        fun p hp => eq_7_4_sub_conj_ne_zero hp.1.2 hz
      rw [hf]
      refine (ContinuousOn.mul ?_ (hμc.comp continuousOn_fst fun p hp => hp.1.1)).mul
        (hνc.comp continuousOn_snd fun p hp => hp.1.2)
      refine ContinuousOn.sub ?_ ?_
      · exact continuousOn_const.div (Continuous.continuousOn (by fun_prop)) fun p hp =>
          mul_ne_zero (pow_ne_zero _ (hne1 p hp)) (pow_ne_zero _ (hne2 p hp))
      · exact continuousOn_const.div (Continuous.continuousOn (by fun_prop)) fun p hp =>
          mul_ne_zero (pow_ne_zero _ (hne1 p hp)) (hne2 p hp)
    refine hΦ.integrableOn.mono' (hfc.aestronglyMeasurable (hDm δ)) (ae_restrict_of_forall_mem (hDm δ) ?_)
    intro p hp
    obtain ⟨⟨hu, hv⟩, hd⟩ := hp
    have hd' : δ ≤ ‖p.1 - p.2‖ := hd
    have hw : 0 < ‖p.1 - p.2‖ := hδ.trans_le hd'
    have hX : (0 : ℝ) < 1 + ‖p.2‖ := by positivity
    have hvi : 0 < p.2.im := hv
    have hyX : p.2.im ≤ 1 + ‖p.2‖ := by linarith [Complex.im_le_norm p.2]
    have hzv := hlow p.2 hv
    have hcX : 0 < c * (1 + ‖p.2‖) := by positivity
    -- the pieces
    have h4 := s74_tail_pt 4 hδ hd'
    have hn : ‖δ⁻¹ • (p.1 - p.2)‖ = ‖p.1 - p.2‖ / δ := by
      rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hδ, inv_mul_eq_div]
    rw [← hn] at h4
    have hν' : ‖ν p.2‖ ≤ 2 * Kψ * ((1 + ‖p.2‖) ^ 2)⁻¹ := by
      refine (hKψ p.2 hv).trans ?_
      have hy2 : p.2.im ^ 2 ≤ (1 + ‖p.2‖) ^ 2 := pow_le_pow_left₀ hvi.le hyX 2
      calc 2 * Kψ * p.2.im ^ 2 * ((1 + ‖p.2‖) ^ 4)⁻¹ ≤ 2 * Kψ * (1 + ‖p.2‖) ^ 2 * ((1 + ‖p.2‖) ^ 4)⁻¹ := by
            gcongr
        _ = 2 * Kψ * ((1 + ‖p.2‖) ^ 2)⁻¹ := by field_simp
    have hk1 : ‖1 / ((p.1 - p.2) ^ 4 * (p.2 - conj z) ^ 2)‖ ≤
        (‖p.1 - p.2‖ ^ 4)⁻¹ * ((c ^ 2)⁻¹ * (1 + ‖p.2‖)⁻¹) := by
      rw [norm_div, norm_one, norm_mul, norm_pow, norm_pow, one_div, mul_inv]
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      calc (‖p.2 - conj z‖ ^ 2)⁻¹ ≤ ((c * (1 + ‖p.2‖)) ^ 2)⁻¹ :=
            inv_anti₀ (by positivity) (pow_le_pow_left₀ hcX.le hzv 2)
        _ ≤ (c ^ 2)⁻¹ * (1 + ‖p.2‖)⁻¹ := by
            rw [mul_pow, mul_inv]
            refine mul_le_mul_of_nonneg_left (inv_anti₀ hX ?_) (by positivity)
            nlinarith [norm_nonneg p.2]
    have hk2 : ‖2 / ((p.1 - p.2) ^ 5 * (p.2 - conj z))‖ ≤
        (‖p.1 - p.2‖ ^ 4)⁻¹ * (2 * δ⁻¹ * c⁻¹ * (1 + ‖p.2‖)⁻¹) := by
      rw [norm_div, norm_mul, norm_pow, Complex.norm_ofNat]
      have h5 : (‖p.1 - p.2‖ ^ 5)⁻¹ ≤ (‖p.1 - p.2‖ ^ 4)⁻¹ * δ⁻¹ := by
        rw [pow_succ, mul_inv]
        exact mul_le_mul_of_nonneg_left (inv_anti₀ hδ hd') (by positivity)
      have h6 : (‖p.2 - conj z‖)⁻¹ ≤ c⁻¹ * (1 + ‖p.2‖)⁻¹ := by
        rw [← mul_inv]
        exact inv_anti₀ hcX hzv
      calc 2 / (‖p.1 - p.2‖ ^ 5 * ‖p.2 - conj z‖) = 2 * (‖p.1 - p.2‖ ^ 5)⁻¹ * (‖p.2 - conj z‖)⁻¹ := by
            rw [div_eq_mul_inv, mul_inv, mul_assoc]
        _ ≤ 2 * ((‖p.1 - p.2‖ ^ 4)⁻¹ * δ⁻¹) * (c⁻¹ * (1 + ‖p.2‖)⁻¹) := by gcongr
        _ = (‖p.1 - p.2‖ ^ 4)⁻¹ * (2 * δ⁻¹ * c⁻¹ * (1 + ‖p.2‖)⁻¹) := by ring
    have hX3 : ((1 + ‖p.2‖) ^ 2)⁻¹ * (1 + ‖p.2‖)⁻¹ = ((1 + ‖p.2‖) ^ 3)⁻¹ := by
      rw [← mul_inv, ← pow_succ]
    rw [hf]
    simp only
    rw [norm_mul, norm_mul]
    calc ‖1 / ((p.1 - p.2) ^ 4 * (p.2 - conj z) ^ 2) - 2 / ((p.1 - p.2) ^ 5 * (p.2 - conj z))‖ * ‖μ p.1‖ *
          ‖ν p.2‖
        ≤ ((‖p.1 - p.2‖ ^ 4)⁻¹ * ((c ^ 2)⁻¹ * (1 + ‖p.2‖)⁻¹) +
            (‖p.1 - p.2‖ ^ 4)⁻¹ * (2 * δ⁻¹ * c⁻¹ * (1 + ‖p.2‖)⁻¹)) * Mμ * (2 * Kψ * ((1 + ‖p.2‖) ^ 2)⁻¹) := by
          gcongr
          · exact (norm_sub_le _ _).trans (add_le_add hk1 hk2)
          · exact hMμ p.1 hu
      _ = Mμ * (2 * Kψ) * (‖p.1 - p.2‖ ^ 4)⁻¹ * ((c ^ 2)⁻¹ + 2 * δ⁻¹ * c⁻¹) *
            (((1 + ‖p.2‖) ^ 2)⁻¹ * (1 + ‖p.2‖)⁻¹) := by ring
      _ ≤ Mμ * (2 * Kψ) * (2 ^ 4 * (δ ^ 4)⁻¹ * ((1 + ‖δ⁻¹ • (p.1 - p.2)‖) ^ 4)⁻¹) *
            ((c ^ 2)⁻¹ + 2 * δ⁻¹ * c⁻¹) * (((1 + ‖p.2‖) ^ 2)⁻¹ * (1 + ‖p.2‖)⁻¹) := by gcongr
      _ = B * (((1 + ‖δ⁻¹ • (p.1 - p.2)‖) ^ 4)⁻¹ * ((1 + ‖p.2‖) ^ 3)⁻¹) := by rw [← hX3, hB]; ring
  refine ⟨fun δ hδ => by rw [← hf]; exact hInt δ hδ, ?_⟩
  rw [← hf]
  -- (ii) Fubini: the inner `u`-integral at fixed `v`
  have hinner : ∀ δ : ℝ, 0 < δ → ∀ v : ℂ,
      (∫ u, ((upperHalf ×ˢ upperHalf) ∩ {p : ℂ × ℂ | δ ≤ ‖p.1 - p.2‖}).indicator f (u, v)) =
        upperHalf.indicator (fun v => ν v * E δ v) v := by
    intro δ hδ v
    by_cases hv : v ∈ upperHalf
    · rw [indicator_of_mem hv]
      have e : (fun u => ((upperHalf ×ˢ upperHalf) ∩ {p : ℂ × ℂ | δ ≤ ‖p.1 - p.2‖}).indicator f (u, v)) =
          (upperHalfPunct v δ).indicator (fun u => f (u, v)) := by
        funext u
        by_cases hu : u ∈ upperHalfPunct v δ
        · rw [indicator_of_mem ((hmem δ u v).2 ⟨hv, hu⟩), indicator_of_mem hu]
        · rw [indicator_of_notMem (fun h => hu ((hmem δ u v).1 h).2), indicator_of_notMem hu]
      have hPm : MeasurableSet (upperHalfPunct v δ) := hU.diff measurableSet_ball
      rw [e, integral_indicator hPm]
      have hpt : ∀ u ∈ upperHalfPunct v δ, f (u, v) =
          ν v * (1 / (v - conj z) ^ 2 * (μ u / (u - v) ^ 4) - 2 / (v - conj z) * (μ u / (u - v) ^ 5)) := by
        intro u hu
        rw [hf]
        dsimp only
        generalize u - v = a
        generalize v - conj z = b
        ring
      rw [setIntegral_congr_fun hPm hpt, integral_const_mul,
        integral_sub ((s74_inner_int hμ v hδ 4 le_rfl).const_mul _)
          ((s74_inner_int hμ v hδ 5 (by norm_num)).const_mul _),
        integral_const_mul, integral_const_mul, hE]
    · rw [indicator_of_notMem hv]
      have e : (fun u => ((upperHalf ×ˢ upperHalf) ∩ {p : ℂ × ℂ | δ ≤ ‖p.1 - p.2‖}).indicator f (u, v)) =
          fun _ => 0 := funext fun u => indicator_of_notMem (fun h => hv ((hmem δ u v).1 h).1) _
      rw [e, integral_zero]
  have hfub : ∀ δ : ℝ, 0 < δ →
      (∫ p in (upperHalf ×ˢ upperHalf) ∩ {p : ℂ × ℂ | δ ≤ ‖p.1 - p.2‖}, f p) =
        ∫ v, upperHalf.indicator (fun v => ν v * E δ v) v := by
    intro δ hδ
    have hI := (integrable_indicator_iff (hDm δ)).2 (hInt δ hδ)
    rw [Measure.volume_eq_prod] at hI
    rw [← integral_indicator (hDm δ), Measure.volume_eq_prod, integral_prod_symm _ hI]
    exact integral_congr_ae (Eventually.of_forall fun v => hinner δ hδ v)
  -- (iii) vanishing off the strip and the strip bound
  have hzero : ∀ v ∈ upperHalf, ∀ δ : ℝ, 0 < δ → δ < v.im → E δ v = 0 := by
    intro v hv δ hδ hδv
    have hB : closedBall v δ ⊆ upperHalf := by
      intro w hw
      rw [mem_closedBall, dist_eq_norm] at hw
      have := Complex.abs_im_le_norm (w - v)
      rw [Complex.sub_im] at this
      show 0 < w.im
      linarith [(abs_le.1 this).1]
    rw [hE]
    simp only
    rw [l112_punct_zero hμ hδ hB (by norm_num), l112_punct_zero hμ hδ hB (by norm_num), mul_zero, mul_zero,
      sub_zero]
  set B : ℝ := 2 * Kψ * ((c ^ 2)⁻¹ * (Mμ * C4) + 2 * c⁻¹ * (8 * Kφ * C3)) with hB
  have hbound : ∀ v ∈ upperHalf, ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ‖ν v * E δ v‖ ≤ B * ((1 + ‖v‖) ^ 4)⁻¹ := by
    intro v hv δ hδ hδ1
    have hX : (0 : ℝ) < 1 + ‖v‖ := by positivity
    by_cases hδv : δ < v.im
    · rw [hzero v hv δ hδ hδv, mul_zero, norm_zero]
      have : 0 ≤ B := by rw [hB]; positivity
      positivity
    push Not at hδv
    have hvi : 0 < v.im := hv
    have hPm : MeasurableSet (upperHalfPunct v δ) := hU.diff measurableSet_ball
    have hSm : MeasurableSet {u : ℂ | δ ≤ ‖u - v‖} := measurableSet_le measurable_const (by fun_prop)
    -- `F_δ`
    have hF : ‖∫ u in upperHalfPunct v δ, μ u / (u - v) ^ 4‖ ≤ Mμ * C4 * (δ ^ 2)⁻¹ := by
      have hg : IntegrableOn (fun u : ℂ => Mμ * (‖u - v‖ ^ 4)⁻¹) {u : ℂ | δ ≤ ‖u - v‖} :=
        (hT4 v δ hδ).1.const_mul Mμ
      refine (norm_integral_le_of_norm_le (hg.mono_set (hsub v δ))
        (ae_restrict_of_forall_mem hPm fun u hu => ?_)).trans ?_
      · rw [norm_div, norm_pow, div_eq_mul_inv]
        exact mul_le_mul_of_nonneg_right (hMμ u hu.1) (by positivity)
      · calc ∫ u in upperHalfPunct v δ, Mμ * (‖u - v‖ ^ 4)⁻¹ ≤ ∫ u in {u : ℂ | δ ≤ ‖u - v‖}, Mμ * (‖u - v‖ ^ 4)⁻¹ :=
              setIntegral_mono_set hg (ae_restrict_of_forall_mem hSm fun u _ => by positivity)
                (Eventually.of_forall (hsub v δ))
          _ = Mμ * ∫ u in {u : ℂ | δ ≤ ‖u - v‖}, (‖u - v‖ ^ 4)⁻¹ := integral_const_mul _ _
          _ ≤ Mμ * (C4 * (δ ^ (4 - 2))⁻¹) := mul_le_mul_of_nonneg_left (hT4 v δ hδ).2 hMμ0
          _ = Mμ * C4 * (δ ^ 2)⁻¹ := by norm_num; ring
    -- `G_δ`, with `|μ(u)| ≤ 8K |u - v|²` on the strip
    have hG : ‖∫ u in upperHalfPunct v δ, μ u / (u - v) ^ 5‖ ≤ 8 * Kφ * C3 * δ⁻¹ := by
      have hg : IntegrableOn (fun u : ℂ => 8 * Kφ * (‖u - v‖ ^ 3)⁻¹) {u : ℂ | δ ≤ ‖u - v‖} :=
        (hT3 v δ hδ).1.const_mul _
      refine (norm_integral_le_of_norm_le (hg.mono_set (hsub v δ))
        (ae_restrict_of_forall_mem hPm fun u hu => ?_)).trans ?_
      · have hd : δ ≤ ‖u - v‖ := hsub v δ hu
        have hw : 0 < ‖u - v‖ := hδ.trans_le hd
        have hui : 0 < u.im := hu.1
        have him : u.im ≤ 2 * ‖u - v‖ := by
          have := Complex.abs_im_le_norm (u - v)
          rw [Complex.sub_im] at this
          linarith [(abs_le.1 this).2]
        have hμu : ‖μ u‖ ≤ 8 * Kφ * ‖u - v‖ ^ 2 := by
          refine (hKφ u hu.1).trans ?_
          have h1 : ((1 + ‖u‖) ^ 4)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ (by linarith [norm_nonneg u]))
          have h2 : u.im ^ 2 ≤ (2 * ‖u - v‖) ^ 2 := pow_le_pow_left₀ hui.le him 2
          calc 2 * Kφ * u.im ^ 2 * ((1 + ‖u‖) ^ 4)⁻¹ ≤ 2 * Kφ * (2 * ‖u - v‖) ^ 2 * 1 := by gcongr
            _ = 8 * Kφ * ‖u - v‖ ^ 2 := by ring
        rw [norm_div, norm_pow]
        calc ‖μ u‖ / ‖u - v‖ ^ 5 ≤ 8 * Kφ * ‖u - v‖ ^ 2 / ‖u - v‖ ^ 5 := by gcongr
          _ = 8 * Kφ * (‖u - v‖ ^ 3)⁻¹ := by field_simp
      · calc ∫ u in upperHalfPunct v δ, 8 * Kφ * (‖u - v‖ ^ 3)⁻¹
            ≤ ∫ u in {u : ℂ | δ ≤ ‖u - v‖}, 8 * Kφ * (‖u - v‖ ^ 3)⁻¹ :=
              setIntegral_mono_set hg (ae_restrict_of_forall_mem hSm fun u _ => by positivity)
                (Eventually.of_forall (hsub v δ))
          _ = 8 * Kφ * ∫ u in {u : ℂ | δ ≤ ‖u - v‖}, (‖u - v‖ ^ 3)⁻¹ := integral_const_mul _ _
          _ ≤ 8 * Kφ * (C3 * (δ ^ (3 - 2))⁻¹) := mul_le_mul_of_nonneg_left (hT3 v δ hδ).2 (by positivity)
          _ = 8 * Kφ * C3 * δ⁻¹ := by norm_num; ring
    have hc2 : ‖1 / (v - conj z) ^ 2‖ ≤ (c ^ 2)⁻¹ := by
      rw [norm_div, norm_one, norm_pow, one_div]
      exact inv_anti₀ (by positivity) (pow_le_pow_left₀ hc.le (hzc v hv) 2)
    have hc1 : ‖2 / (v - conj z)‖ ≤ 2 * c⁻¹ := by
      rw [norm_div, Complex.norm_ofNat, div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_left (inv_anti₀ hc (hzc v hv)) (by norm_num)
    have hνv : ‖ν v‖ ≤ 2 * Kψ * δ ^ 2 * ((1 + ‖v‖) ^ 4)⁻¹ := by
      refine (hKψ v hv).trans ?_
      gcongr
    rw [hE]
    simp only
    rw [norm_mul]
    calc ‖ν v‖ * ‖1 / (v - conj z) ^ 2 * (∫ u in upperHalfPunct v δ, μ u / (u - v) ^ 4) -
          2 / (v - conj z) * ∫ u in upperHalfPunct v δ, μ u / (u - v) ^ 5‖
        ≤ (2 * Kψ * δ ^ 2 * ((1 + ‖v‖) ^ 4)⁻¹) *
            ((c ^ 2)⁻¹ * (Mμ * C4 * (δ ^ 2)⁻¹) + 2 * c⁻¹ * (8 * Kφ * C3 * δ⁻¹)) := by
          refine mul_le_mul hνv ((norm_sub_le _ _).trans (add_le_add ?_ ?_)) (norm_nonneg _) (by positivity)
          · rw [norm_mul]; exact mul_le_mul hc2 hF (norm_nonneg _) (by positivity)
          · rw [norm_mul]; exact mul_le_mul hc1 hG (norm_nonneg _) (by positivity)
      _ = 2 * Kψ * ((c ^ 2)⁻¹ * (Mμ * C4) + 2 * c⁻¹ * (8 * Kφ * C3) * δ) * ((1 + ‖v‖) ^ 4)⁻¹ := by
          field_simp
      _ ≤ B * ((1 + ‖v‖) ^ 4)⁻¹ := by
          have hb0 : 0 ≤ 2 * c⁻¹ * (8 * Kφ * C3) := by positivity
          have hδb : 2 * c⁻¹ * (8 * Kφ * C3) * δ ≤ 2 * c⁻¹ * (8 * Kφ * C3) := by nlinarith
          rw [hB]
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          linarith
  -- (iv) dominated convergence in `v`
  have hmaj := (e64_t5_maj 0).1
  simp only [sub_zero] at hmaj
  have key : Tendsto (fun δ : ℝ => ∫ v, upperHalf.indicator (fun v => ν v * E δ v) v) (𝓝[>] 0)
      (𝓝 (∫ v : ℂ, (0 : ℂ))) := by
    refine tendsto_integral_filter_of_dominated_convergence
      (upperHalf.indicator fun v => B * ((1 + ‖v‖) ^ 4)⁻¹) ?_ ?_ ((hmaj.const_mul B).indicator hU) ?_
    · filter_upwards [self_mem_nhdsWithin] with δ hδ
      have hI := (integrable_indicator_iff (hDm δ)).2 (hInt δ hδ)
      rw [Measure.volume_eq_prod] at hI
      exact (hI.integral_prod_right.aestronglyMeasurable).congr
        (Eventually.of_forall fun v => hinner δ hδ v)
    · filter_upwards [Ioc_mem_nhdsGT one_pos] with δ hδ
      refine Eventually.of_forall fun v => ?_
      by_cases hv : v ∈ upperHalf
      · rw [indicator_of_mem hv, indicator_of_mem hv]
        exact hbound v hv δ hδ.1 hδ.2
      · rw [indicator_of_notMem hv, indicator_of_notMem hv, norm_zero]
    · refine Eventually.of_forall fun v => ?_
      by_cases hv : v ∈ upperHalf
      · have hvi : 0 < v.im := hv
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [Ioo_mem_nhdsGT hvi] with δ hδ
        rw [indicator_of_mem hv, hzero v hv δ hδ.1 hδ.2, mul_zero]
      · simp only [indicator_of_notMem hv]
        exact tendsto_const_nhds
  rw [integral_zero] at key
  refine key.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  exact (hfub δ hδ).symm

/-- **(B2)** `[W6]` For nice `μ, ν` the cut-off integrals of (7.2) tend to `0`: the four-term split
(`eq_7_4_integral_identity`), `s74_half` for `(μ, ν)`, and for `(ν, μ)` after the swap. -/
theorem s74_nice {μ ν φ ψ : ℂ → ℂ} (hμ : IsHarmonicU μ φ) (hν : IsHarmonicU ν ψ)
    (hφn : ∃ K : ℝ, ∀ u ∈ upperHalf, ‖φ u‖ ≤ K * ((1 + ‖u‖) ^ 4)⁻¹)
    (hψn : ∃ K : ℝ, ∀ u ∈ upperHalf, ‖ψ u‖ ≤ K * ((1 + ‖u‖) ^ 4)⁻¹) {z : ℂ} (hz : z ∈ upperHalf) :
    Tendsto (fun δ : ℝ => ∫ p in (upperHalf ×ˢ upperHalf) ∩ {p : ℂ × ℂ | δ ≤ ‖p.1 - p.2‖},
      μ p.1 * ν p.2 / ((p.1 - conj z) ^ 2 * (p.1 - p.2) ^ 2 * (p.2 - conj z) ^ 2)) (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨h12i, h12⟩ := s74_half hμ hν hφn hψn hz
  obtain ⟨h34i, h34⟩ := s74_half hν hμ hψn hφn hz
  have hlim := h12.add (h34.congr fun δ => ((s74_swapD (fun q : ℂ × ℂ =>
    (1 / ((q.1 - q.2) ^ 4 * (q.2 - conj z) ^ 2) - 2 / ((q.1 - q.2) ^ 5 * (q.2 - conj z))) * ν q.1 * μ q.2) δ).1).symm)
  rw [add_zero] at hlim
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  have hδ0 : 0 < δ := hδ
  rw [eq_7_4_integral_identity μ ν hz hδ0, ← integral_add (h12i δ hδ0) ((s74_swapD (fun q : ℂ × ℂ =>
    (1 / ((q.1 - q.2) ^ 4 * (q.2 - conj z) ^ 2) - 2 / ((q.1 - q.2) ^ 5 * (q.2 - conj z))) * ν q.1 * μ q.2) δ).2
      (h34i δ hδ0))]
  congr 1
  funext p
  simp only [Prod.fst_swap, Prod.snd_swap]
  rw [show p.2 - p.1 = -(p.1 - p.2) by ring]
  generalize p.1 - p.2 = a
  generalize p.1 - conj z = b
  generalize p.2 - conj z = c
  ring

/-! ### (C) Continuity of the limit -/

/-- **(C1)** `[W?]` The C2 majorant (`s71_v_unif`) with constant weight: `g/|u - z̄|²` is integrable on `𝕌`. (The `g`
of `s71_v_unif` does not depend on `μ`; this is its proof with the weight `|μ|` removed.) -/
theorem s74_v_unif0 {ν ψ : ℂ → ℂ} (hν : IsHarmonicU ν ψ) {z : ℂ} (hz : z ∈ upperHalf) :
    ∃ g : ℂ → ℝ, IntegrableOn (fun u => g u / ‖u - conj z‖ ^ 2) upperHalf ∧
      ∀ u ∈ upperHalf, ∀ δ : ℝ, 0 < δ → δ ≤ 1 →
        ‖∫ v in upperHalf \ ball u δ, ν v / ((u - v) ^ 2 * (v - conj z) ^ 2)‖ ≤ g u := by
  have hνc := harmonicU_continuousOn hν
  obtain ⟨hdψ, ⟨C, hC⟩, h3⟩ := hν
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC z hz)
  obtain ⟨N, hN0, hN⟩ := harmonicU_bounded ⟨hdψ, ⟨C, hC⟩, h3⟩
  obtain ⟨c, hc, hlow⟩ := s71c2_lower hz
  obtain ⟨C₁, hC₁0, hT⟩ := s71_t_conv
  have hmU : MeasurableSet upperHalf := isOpen_upperHalf.measurableSet
  have hz0 : 0 < z.im := hz
  set g : ℂ → ℝ := fun u => 612 * C * π * (c ^ 2)⁻¹ * ((1 + ‖u‖) ^ 2)⁻¹ +
    N * (c ^ 2)⁻¹ * 2 * u.im ^ (-(1 / 2 : ℝ)) * (C₁ * (1 + ‖u‖) ^ (-(1 / 2 : ℝ))) with hg
  refine ⟨g, ?_, fun u hu δ hδ _ => ?_⟩
  · -- integrability: domination by `s71_t_half`
    set K : ℝ := (c ^ 2)⁻¹ * (612 * C * π * (c ^ 2)⁻¹ + N * (c ^ 2)⁻¹ * 2 * C₁) with hK
    have hmeas : Measurable fun u : ℂ => g u / ‖u - conj z‖ ^ 2 := by rw [hg]; fun_prop
    refine Integrable.mono' (s71_t_half.const_mul K) hmeas.aestronglyMeasurable
      (ae_restrict_of_forall_mem hmU fun u hu => ?_)
    obtain ⟨w1, w2⟩ := s71c2_weights hu
    have hl := hlow u hu
    have hB : (‖u - conj z‖ ^ 2)⁻¹ ≤ (c ^ 2)⁻¹ * ((1 + ‖u‖) ^ 2)⁻¹ := by
      rw [← mul_inv, ← mul_pow]
      exact inv_anti₀ (by positivity) (pow_le_pow_left₀ (by positivity) hl 2)
    have hg0 : 0 ≤ g u := by
      have hr := Real.rpow_nonneg (le_of_lt (show (0 : ℝ) < u.im from hu)) (-(1 / 2 : ℝ))
      simp only [hg]
      positivity
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg hg0 (by positivity)), div_eq_mul_inv, mul_comm]
    calc (‖u - conj z‖ ^ 2)⁻¹ * g u ≤ (c ^ 2)⁻¹ * ((1 + ‖u‖) ^ 2)⁻¹ * g u :=
          mul_le_mul_of_nonneg_right hB hg0
      _ = (c ^ 2)⁻¹ * (612 * C * π * (c ^ 2)⁻¹ * (((1 + ‖u‖) ^ 2)⁻¹ * ((1 + ‖u‖) ^ 2)⁻¹) +
          N * (c ^ 2)⁻¹ * 2 * C₁ * (((1 + ‖u‖) ^ 2)⁻¹ * (1 + ‖u‖) ^ (-(1 / 2 : ℝ))) * u.im ^ (-(1 / 2 : ℝ))) := by
          rw [hg]; ring
      _ ≤ (c ^ 2)⁻¹ * (612 * C * π * (c ^ 2)⁻¹ * ((1 + ‖u‖) ^ (-(5 / 2 : ℝ)) * u.im ^ (-(1 / 2 : ℝ))) +
          N * (c ^ 2)⁻¹ * 2 * C₁ * (1 + ‖u‖) ^ (-(5 / 2 : ℝ)) * u.im ^ (-(1 / 2 : ℝ))) := by
          rw [w2]; gcongr
      _ = K * ((1 + ‖u‖) ^ (-(5 / 2 : ℝ)) * u.im ^ (-(1 / 2 : ℝ))) := by rw [hK]; ring
  · -- the uniform bound
    have ht : 0 < u.im := hu
    have hBu : u.im ≤ ‖u - conj z‖ := by
      have := Complex.abs_im_le_norm (u - conj z)
      rw [Complex.sub_im, Complex.conj_im, abs_of_pos (by linarith)] at this
      linarith
    have hmeas : AEStronglyMeasurable (fun v => ν v / ((u - v) ^ 2 * (v - conj z) ^ 2))
        (volume.restrict upperHalf) := by
      have h1 : AEStronglyMeasurable ν (volume.restrict upperHalf) := hνc.aestronglyMeasurable hmU
      have h2 : Measurable fun v : ℂ => ((u - v) ^ 2 * (v - conj z) ^ 2)⁻¹ := by fun_prop
      simpa only [div_eq_mul_inv, Pi.mul_def] using h1.mul h2.aestronglyMeasurable
    by_cases hδr : δ < u.im / 2
    · have hball : ball u (u.im / 2) ⊆ upperHalf := by
        intro v hv
        rw [mem_ball, dist_eq_norm] at hv
        have := Complex.abs_im_le_norm (v - u)
        rw [Complex.sub_im] at this
        show 0 < v.im
        linarith [(abs_le.1 this).1]
      have hL : ∀ v ∈ ball u (u.im / 2), ‖ν v / (v - conj z) ^ 2 - ν u / (u - conj z) ^ 2‖ ≤
          612 * C / (u.im * ‖u - conj z‖ ^ 2) * ‖v - u‖ := by
        intro v hv
        rw [h3 v (hball hv), h3 u hu]
        exact s71c2_F_lip hdψ hC0 hC hu hBu hv
      have hFm : AEStronglyMeasurable (fun v => ν v / (v - conj z) ^ 2) (volume.restrict (ball u (u.im / 2))) := by
        have h1 : AEStronglyMeasurable ν (volume.restrict (ball u (u.im / 2))) :=
          (hνc.aestronglyMeasurable hmU).mono_measure (Measure.restrict_mono hball le_rfl)
        have h2 : Measurable fun v : ℂ => ((v - conj z) ^ 2)⁻¹ := by fun_prop
        simpa only [div_eq_mul_inv, Pi.mul_def] using h1.mul h2.aestronglyMeasurable
      obtain ⟨hNi, hNb⟩ := s71c2_near (F := fun v => ν v / (v - conj z) ^ 2) hδ hδr.le (by positivity) hL hFm
      have hconv : (fun v => ν v / (v - conj z) ^ 2 / (u - v) ^ 2) =
          fun v => ν v / ((u - v) ^ 2 * (v - conj z) ^ 2) := by
        funext v
        rw [div_div, mul_comm]
      rw [hconv] at hNi hNb
      obtain ⟨hFi, hFb⟩ := s71c2_far (S := upperHalf \ ball u (u.im / 2)) hc hlow hN hu (hT u) hmeas
        (hmU.diff measurableSet_ball) sdiff_subset (fun v hv => by
          have := hv.2
          rwa [mem_ball, dist_eq_norm, not_lt] at this)
      have hsplit : upperHalf \ ball u δ = (ball u (u.im / 2) \ ball u δ) ∪ (upperHalf \ ball u (u.im / 2)) := by
        ext v
        simp only [Set.mem_sdiff, mem_union]
        constructor
        · rintro ⟨hv, hvδ⟩
          by_cases h : v ∈ ball u (u.im / 2)
          · exact Or.inl ⟨h, hvδ⟩
          · exact Or.inr ⟨hv, h⟩
        · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
          · exact ⟨hball h1, h2⟩
          · exact ⟨h1, fun h => h2 (ball_subset_ball hδr.le h)⟩
      have hdisj : Disjoint (ball u (u.im / 2) \ ball u δ) (upperHalf \ ball u (u.im / 2)) :=
        disjoint_left.2 fun v h1 h2 => h2.2 h1.1
      have hBinv : (‖u - conj z‖ ^ 2)⁻¹ ≤ (c ^ 2)⁻¹ * ((1 + ‖u‖) ^ 2)⁻¹ := by
        rw [← mul_inv, ← mul_pow]
        exact inv_anti₀ (by positivity) (pow_le_pow_left₀ (by positivity) (hlow u hu) 2)
      have hB0 : 0 < ‖u - conj z‖ := by linarith
      have e : 612 * C / (u.im * ‖u - conj z‖ ^ 2) * (2 * π * (u.im / 2)) = 612 * C * π * (‖u - conj z‖ ^ 2)⁻¹ := by
        field_simp
      have hm := mul_le_mul_of_nonneg_left hBinv (by positivity : (0 : ℝ) ≤ 612 * C * π)
      rw [hsplit, setIntegral_union hdisj (hmU.diff measurableSet_ball) hNi hFi]
      refine (norm_add_le _ _).trans ((add_le_add hNb hFb).trans ?_)
      rw [e]
      simp only [hg]
      linear_combination hm
    · obtain ⟨-, hFb⟩ := s71c2_far (S := upperHalf \ ball u δ) hc hlow hN hu (hT u) hmeas
        (hmU.diff measurableSet_ball) sdiff_subset (fun v hv => by
          have := hv.2
          rw [mem_ball, dist_eq_norm, not_lt] at this
          linarith)
      refine hFb.trans ?_
      simp only [hg]
      exact le_add_of_nonneg_left (by positivity)

/-- **(C2)** `[W6]` `L(·, ν)` is continuous under bounded pointwise convergence on `𝕌` (dominated convergence with
`s74_v_unif0`; the principal value is measurable as a limit of the truncations, `s71_v_trunc`). -/
theorem s74_cont {μs φs : ℕ → ℂ → ℂ} {μ ν φ ψ : ℂ → ℂ} (hμs : ∀ n, IsHarmonicU (μs n) (φs n))
    (hμ : IsHarmonicU μ φ) (hν : IsHarmonicU ν ψ) {M : ℝ} (hM : ∀ n, ∀ u ∈ upperHalf, ‖μs n u‖ ≤ M)
    (hlim : ∀ u ∈ upperHalf, Tendsto (fun n => μs n u) atTop (𝓝 (μ u))) {z : ℂ} (hz : z ∈ upperHalf) :
    Tendsto (fun n => ∫ u in upperHalf, μs n u / (u - conj z) ^ 2 *
        pv2 (fun v => ν v / ((u - v) ^ 2 * (v - conj z) ^ 2)) u z) atTop
      (𝓝 (∫ u in upperHalf, μ u / (u - conj z) ^ 2 * pv2 (fun v => ν v / ((u - v) ^ 2 * (v - conj z) ^ 2)) u z)) := by
  have hU := measurableSet_upperHalf_aux
  obtain ⟨g, hgI, hgb⟩ := s74_v_unif0 hν hz
  have hνc := harmonicU_continuousOn hν
  have hI : I ∈ upperHalf := by
    show (0 : ℝ) < I.im
    simp
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0 I hI)
  obtain ⟨P, hP⟩ : ∃ P : ℂ → ℂ, P = fun u => pv2 (fun v => ν v / ((u - v) ^ 2 * (v - conj z) ^ 2)) u z :=
    ⟨_, rfl⟩
  have hPu : ∀ u, pv2 (fun v => ν v / ((u - v) ^ 2 * (v - conj z) ^ 2)) u z = P u := fun u => by rw [hP]
  simp only [hPu]
  -- the principal value is bounded by the majorant
  have hPb : ∀ u ∈ upperHalf, ‖P u‖ ≤ g u := by
    intro u hu
    rw [← hPu]
    refine le_of_tendsto (s71_v_trunc hν hz hu).norm ?_
    filter_upwards [Ioc_mem_nhdsGT one_pos] with δ hδ
    exact hgb u hu δ hδ.1 hδ.2
  -- measurability of the truncations in `u`, hence of their limit
  have hTm : ∀ δ : ℝ, AEStronglyMeasurable
      (fun u => ∫ v in upperHalf \ ball u δ, ν v / ((u - v) ^ 2 * (v - conj z) ^ 2)) (volume.restrict upperHalf) := by
    intro δ
    have hνm : AEStronglyMeasurable (upperHalf.indicator ν) volume :=
      (aestronglyMeasurable_indicator_iff hU).2 (hνc.aestronglyMeasurable hU)
    have hSm : MeasurableSet {p : ℂ × ℂ | p.2 ∈ upperHalf ∧ δ ≤ ‖p.2 - p.1‖} :=
      (measurable_snd hU).inter (measurableSet_le measurable_const
        (show Measurable (fun p : ℂ × ℂ => ‖p.2 - p.1‖) by fun_prop))
    have hF : AEStronglyMeasurable (fun p : ℂ × ℂ => {p : ℂ × ℂ | p.2 ∈ upperHalf ∧ δ ≤ ‖p.2 - p.1‖}.indicator
        (fun p => upperHalf.indicator ν p.2 * ((p.1 - p.2) ^ 2 * (p.2 - conj z) ^ 2)⁻¹) p)
        ((volume.restrict upperHalf).prod volume) :=
      ((hνm.comp_snd (μ := volume.restrict upperHalf)).mul
        (Measurable.aestronglyMeasurable (by fun_prop))).indicator hSm
    refine hF.integral_prod_right'.congr (Eventually.of_forall fun u => ?_)
    simp only
    rw [← integral_indicator (hU.diff measurableSet_ball)]
    congr 1
    funext v
    by_cases hv : v ∈ upperHalf \ ball u δ
    · have hp : (u, v) ∈ {p : ℂ × ℂ | p.2 ∈ upperHalf ∧ δ ≤ ‖p.2 - p.1‖} := ⟨hv.1, by
        have := hv.2
        rwa [mem_ball, dist_eq_norm, not_lt] at this⟩
      rw [indicator_of_mem hp, indicator_of_mem hv, indicator_of_mem hv.1, div_eq_mul_inv]
    · have hp : (u, v) ∉ {p : ℂ × ℂ | p.2 ∈ upperHalf ∧ δ ≤ ‖p.2 - p.1‖} := fun hp => hv ⟨hp.1, by
        rw [mem_ball, dist_eq_norm, not_lt]
        exact hp.2⟩
      rw [indicator_of_notMem hp, indicator_of_notMem hv]
  have hPm : AEStronglyMeasurable P (volume.restrict upperHalf) := by
    refine aestronglyMeasurable_of_tendsto_ae atTop
      (f := fun (m : ℕ) u => ∫ v in upperHalf \ ball u (1 / ((m : ℝ) + 1)), ν v / ((u - v) ^ 2 * (v - conj z) ^ 2))
      (fun m => hTm _) ?_
    filter_upwards [ae_restrict_mem hU] with u hu
    have hseq : Tendsto (fun m : ℕ => 1 / ((m : ℝ) + 1)) atTop (𝓝[>] 0) :=
      tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ tendsto_one_div_add_atTop_nhds_zero_nat
        (Eventually.of_forall fun m => by
          show (0 : ℝ) < 1 / ((m : ℝ) + 1)
          positivity)
    rw [← hPu]
    exact (s71_v_trunc hν hz hu).comp hseq
  -- dominated convergence
  have hne : ∀ u ∈ upperHalf, (u - conj z) ^ 2 ≠ 0 := fun u hu => pow_ne_zero _ (eq_7_4_sub_conj_ne_zero hu hz)
  refine tendsto_integral_of_dominated_convergence (fun u => M * (g u / ‖u - conj z‖ ^ 2)) (fun n => ?_)
    (hgI.const_mul M) (fun n => ?_) ?_
  · exact (((harmonicU_continuousOn (hμs n)).div (Continuous.continuousOn (by fun_prop)) hne).aestronglyMeasurable
      hU).mul hPm
  · refine ae_restrict_of_forall_mem hU fun u hu => ?_
    rw [norm_mul, norm_div, norm_pow]
    calc ‖μs n u‖ / ‖u - conj z‖ ^ 2 * ‖P u‖ ≤ M / ‖u - conj z‖ ^ 2 * g u :=
          mul_le_mul (div_le_div_of_nonneg_right (hM n u hu) (by positivity)) (hPb u hu) (norm_nonneg _)
            (div_nonneg hM0 (by positivity))
      _ = M * (g u / ‖u - conj z‖ ^ 2) := by ring
  · refine ae_restrict_of_forall_mem hU fun u hu => ?_
    exact ((hlim u hu).div_const _).mul_const _

/-! ### (D) Approximation -/

/-- Pointwise estimates for the approximant `φ(u + i/a) (a i/(u + a i))⁴`, `a ≥ 1` (helper for (D)). -/
theorem s74_approx_pt {φ : ℂ → ℂ} {C : ℝ} (hC : ∀ w ∈ upperHalf, w.im ^ 2 * ‖φ w‖ ≤ C) {a : ℝ} (ha : 1 ≤ a)
    {u : ℂ} (hu : u ∈ upperHalf) :
    u + ((1 / a : ℝ) : ℂ) * I ∈ upperHalf ∧ u + (a : ℂ) * I ≠ 0 ∧
      u.im ^ 2 * ‖φ (u + ((1 / a : ℝ) : ℂ) * I) * ((a : ℂ) * I / (u + (a : ℂ) * I)) ^ 4‖ ≤ C ∧
      ‖φ (u + ((1 / a : ℝ) : ℂ) * I) * ((a : ℂ) * I / (u + (a : ℂ) * I)) ^ 4‖ ≤
        4 * C * a ^ 6 * ((1 + ‖u‖) ^ 4)⁻¹ := by
  have hy : (0 : ℝ) < u.im := hu
  have ha0 : 0 < a := by linarith
  have hwim : (u + ((1 / a : ℝ) : ℂ) * I).im = u.im + 1 / a := by simp
  have hw : u + ((1 / a : ℝ) : ℂ) * I ∈ upperHalf := by
    show (0 : ℝ) < _; rw [hwim]; positivity
  have hvim : (u + (a : ℂ) * I).im = u.im + a := by simp
  have hvre : (u + (a : ℂ) * I).re = u.re := by simp
  have hv : u + (a : ℂ) * I ≠ 0 := fun h => by
    have := congrArg Complex.im h
    rw [hvim, Complex.zero_im] at this
    linarith
  have hvn : u.im + a ≤ ‖u + (a : ℂ) * I‖ := by
    have := Complex.abs_im_le_norm (u + (a : ℂ) * I)
    rwa [hvim, abs_of_pos (by linarith)] at this
  have hqn : ‖(a : ℂ) * I / (u + (a : ℂ) * I)‖ = a / ‖u + (a : ℂ) * I‖ := by
    rw [norm_div, norm_mul, Complex.norm_real, Complex.norm_I, mul_one, Real.norm_of_nonneg ha0.le]
  have hq : ‖(a : ℂ) * I / (u + (a : ℂ) * I)‖ ≤ 1 := by
    rw [hqn, div_le_one (by linarith)]; linarith
  have hq4 : ‖((a : ℂ) * I / (u + (a : ℂ) * I)) ^ 4‖ ≤ 1 := by
    rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hq
  have hφw := hC _ hw
  rw [hwim] at hφw
  have hE : ‖φ (u + ((1 / a : ℝ) : ℂ) * I) * ((a : ℂ) * I / (u + (a : ℂ) * I)) ^ 4‖ ≤
      ‖φ (u + ((1 / a : ℝ) : ℂ) * I)‖ := by
    rw [norm_mul]; exact mul_le_of_le_one_right (norm_nonneg _) hq4
  have h1a : 0 < 1 / a := by positivity
  refine ⟨hw, hv, ?_, ?_⟩
  · have hsq : u.im ^ 2 ≤ (u.im + 1 / a) ^ 2 := pow_le_pow_left₀ hy.le (by linarith) 2
    calc u.im ^ 2 * ‖φ (u + ((1 / a : ℝ) : ℂ) * I) * ((a : ℂ) * I / (u + (a : ℂ) * I)) ^ 4‖
        ≤ (u.im + 1 / a) ^ 2 * ‖φ (u + ((1 / a : ℝ) : ℂ) * I)‖ :=
          mul_le_mul hsq hE (norm_nonneg _) (by positivity)
      _ ≤ C := hφw
  · have h1 : (1 / a) ^ 2 * ‖φ (u + ((1 / a : ℝ) : ℂ) * I)‖ ≤ C :=
      le_trans (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ h1a.le (by linarith) 2) (norm_nonneg _)) hφw
    have hφa : ‖φ (u + ((1 / a : ℝ) : ℂ) * I)‖ ≤ C * a ^ 2 := by
      have e : ‖φ (u + ((1 / a : ℝ) : ℂ) * I)‖ = (1 / a) ^ 2 * ‖φ (u + ((1 / a : ℝ) : ℂ) * I)‖ * a ^ 2 := by
        field_simp
      rw [e]
      exact mul_le_mul_of_nonneg_right h1 (by positivity)
    obtain ⟨X, hXd⟩ : ∃ X : ℝ, X = ‖u + (a : ℂ) * I‖ := ⟨_, rfl⟩
    obtain ⟨P, hPd⟩ : ∃ P : ℝ, P = 1 + ‖u‖ := ⟨_, rfl⟩
    have hX : 0 < X := by rw [hXd]; linarith
    have hP : 0 < P := by rw [hPd]; positivity
    have hX2 : ‖u‖ ^ 2 + 1 ≤ X ^ 2 := by
      rw [hXd, Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply, hvre, hvim]
      nlinarith
    have hP2 : P ^ 2 ≤ 2 * X ^ 2 := by
      rw [hPd]; nlinarith [sq_nonneg (1 - ‖u‖)]
    have hPX : P ^ 4 ≤ 4 * X ^ 4 := by
      have := pow_le_pow_left₀ (by positivity) hP2 2
      nlinarith [this]
    have hC0 : 0 ≤ C := (by positivity : (0 : ℝ) ≤ (1 / a) ^ 2 * ‖φ (u + ((1 / a : ℝ) : ℂ) * I)‖).trans h1
    rw [norm_mul, norm_pow, hqn, ← hXd, ← hPd]
    calc ‖φ (u + ((1 / a : ℝ) : ℂ) * I)‖ * (a / X) ^ 4 ≤ C * a ^ 2 * (a / X) ^ 4 :=
          mul_le_mul_of_nonneg_right hφa (by positivity)
      _ = C * a ^ 6 / X ^ 4 := by field_simp
      _ ≤ 4 * C * a ^ 6 * (P ^ 4)⁻¹ := by
          rw [div_le_iff₀ (by positivity)]
          have hm : C * a ^ 6 * P ^ 4 ≤ C * a ^ 6 * (4 * X ^ 4) := mul_le_mul_of_nonneg_left hPX (by positivity)
          have e : 4 * C * a ^ 6 * (P ^ 4)⁻¹ * X ^ 4 = C * a ^ 6 * (4 * X ^ 4) / P ^ 4 := by
            field_simp
          rw [e, le_div_iff₀ (by positivity)]
          exact hm

/-- **(D)** `[W?]` Every `μ ∈ Ω^{-1,1}(𝕌)` is a bounded pointwise limit on `𝕌` of nice ones:
`φₙ(u) = φ(u + i/(n+1)) ((n+1) i/(u + (n+1) i))⁴`, `μₙ = ((u - ū)²/2) \overline{φₙ}`. -/
theorem s74_approx {μ φ : ℂ → ℂ} (hμ : IsHarmonicU μ φ) :
    ∃ μs φs : ℕ → ℂ → ℂ, ∃ M : ℝ, (∀ n, IsHarmonicU (μs n) (φs n)) ∧
      (∀ n, ∃ K : ℝ, ∀ u ∈ upperHalf, ‖φs n u‖ ≤ K * ((1 + ‖u‖) ^ 4)⁻¹) ∧
      (∀ n, ∀ u ∈ upperHalf, ‖μs n u‖ ≤ M) ∧ ∀ u ∈ upperHalf, Tendsto (fun n => μs n u) atTop (𝓝 (μ u)) := by
  obtain ⟨hφd, ⟨C, hC⟩, hμφ⟩ := hμ
  have hU : IsOpen upperHalf := isOpen_lt continuous_const Complex.continuous_im
  have hC' : ∀ w ∈ upperHalf, w.im ^ 2 * ‖φ w‖ ≤ C := fun w hw => by
    have h := hC w hw
    simpa [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_pow, sq_abs] using h
  have ha : ∀ n : ℕ, (1 : ℝ) ≤ (n : ℝ) + 1 := fun n => by
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  refine ⟨fun n u => (u - conj u) ^ 2 / 2 * conj (φ (u + ((1 / ((n : ℝ) + 1) : ℝ) : ℂ) * I) *
      ((((n : ℝ) + 1 : ℝ) : ℂ) * I / (u + (((n : ℝ) + 1 : ℝ) : ℂ) * I)) ^ 4),
    fun n u => φ (u + ((1 / ((n : ℝ) + 1) : ℝ) : ℂ) * I) *
      ((((n : ℝ) + 1 : ℝ) : ℂ) * I / (u + (((n : ℝ) + 1 : ℝ) : ℂ) * I)) ^ 4,
    2 * C, fun n => ⟨?_, ⟨C, fun u hu => ?_⟩, fun u _ => rfl⟩,
    fun n => ⟨4 * C * ((n : ℝ) + 1) ^ 6, fun u hu => (s74_approx_pt hC' (ha n) hu).2.2.2⟩,
    fun n u hu => ?_, fun u hu => ?_⟩
  · have hw : MapsTo (fun u : ℂ => u + ((1 / ((n : ℝ) + 1) : ℝ) : ℂ) * I) upperHalf upperHalf :=
      fun u hu => (s74_approx_pt hC' (ha n) hu).1
    exact (hφd.comp (differentiableOn_id.add_const _) hw).mul
      (((differentiableOn_const _).div (differentiableOn_id.add_const _)
        fun u hu => (s74_approx_pt hC' (ha n) hu).2.1).pow 4)
  · have h := (s74_approx_pt hC' (ha n) hu).2.2.1
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
    exact h
  · have h := (s74_approx_pt hC' (ha n) hu).2.2.1
    have hy : (0 : ℝ) < u.im := hu
    rw [norm_mul, norm_div, norm_pow, wp_upperHalf_reflection_norm hu, RCLike.norm_conj, Complex.norm_two]
    calc (2 * u.im) ^ 2 / 2 * ‖φ (u + ((1 / ((n : ℝ) + 1) : ℝ) : ℂ) * I) *
          ((((n : ℝ) + 1 : ℝ) : ℂ) * I / (u + (((n : ℝ) + 1 : ℝ) : ℂ) * I)) ^ 4‖
        = 2 * (u.im ^ 2 * ‖φ (u + ((1 / ((n : ℝ) + 1) : ℝ) : ℂ) * I) *
          ((((n : ℝ) + 1 : ℝ) : ℂ) * I / (u + (((n : ℝ) + 1 : ℝ) : ℂ) * I)) ^ 4‖) := by ring
      _ ≤ 2 * C := by linarith
  · rw [hμφ u hu]
    have hcont : ContinuousAt φ u := hφd.continuousOn.continuousAt (hU.mem_nhds hu)
    have ht : Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1)) atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
    have h0 : Tendsto (fun n : ℕ => (((1 / ((n : ℝ) + 1) : ℝ) : ℂ))) atTop (𝓝 0) := by
      have := (Complex.continuous_ofReal.tendsto 0).comp ht
      rw [Complex.ofReal_zero] at this
      exact this
    have hwl : Tendsto (fun n : ℕ => u + ((1 / ((n : ℝ) + 1) : ℝ) : ℂ) * I) atTop (𝓝 u) := by
      have := tendsto_const_nhds (x := u) |>.add (h0.mul_const I)
      simpa using this
    have hφl := hcont.tendsto.comp hwl
    -- `a i/(u + a i) = 1 - u/(u + a i) → 1`
    have hr : Tendsto (fun n : ℕ => u / (u + (((n : ℝ) + 1 : ℝ) : ℂ) * I)) atTop (𝓝 0) := by
      refine squeeze_zero_norm (fun n => ?_) (by simpa using ht.const_mul ‖u‖)
      have hv := (s74_approx_pt hC' (ha n) hu).2.1
      have hvn : (n : ℝ) + 1 ≤ ‖u + (((n : ℝ) + 1 : ℝ) : ℂ) * I‖ := by
        have := Complex.abs_im_le_norm (u + (((n : ℝ) + 1 : ℝ) : ℂ) * I)
        have hy : (0 : ℝ) < u.im := hu
        have him : (u + (((n : ℝ) + 1 : ℝ) : ℂ) * I).im = u.im + ((n : ℝ) + 1) := by simp
        rw [him, abs_of_pos (by linarith [ha n])] at this
        linarith
      rw [norm_div, div_le_iff₀ (norm_pos_iff.mpr hv)]
      calc ‖u‖ = ‖u‖ * ((n : ℝ) + 1)⁻¹ * ((n : ℝ) + 1) := by field_simp
        _ ≤ ‖u‖ * ((n : ℝ) + 1)⁻¹ * ‖u + (((n : ℝ) + 1 : ℝ) : ℂ) * I‖ :=
          mul_le_mul_of_nonneg_left hvn (by positivity)
    have hq : Tendsto (fun n : ℕ => (((n : ℝ) + 1 : ℝ) : ℂ) * I / (u + (((n : ℝ) + 1 : ℝ) : ℂ) * I)) atTop
        (𝓝 1) := by
      have := (tendsto_const_nhds (x := (1 : ℂ))).sub hr
      rw [sub_zero] at this
      refine this.congr fun n => ?_
      have hv := (s74_approx_pt hC' (ha n) hu).2.1
      field_simp
      ring
    have hlim := hφl.mul (hq.pow 4)
    rw [one_pow, mul_one] at hlim
    exact tendsto_const_nhds.mul ((Complex.continuous_conj.tendsto _).comp hlim)


/-! ### The original statement (byte-identical copy) -/

/-- **(7.4)** (TT:2729) and the vanishing of the holomorphic variation. For `μ, ν ∈ Ω^{-1,1}(𝕌)`, the principal value
integral of (7.2) equals `lim_{ε → 0} ∬∬_{|u - v| ≥ ε} (I₁ + I₂ + I₃ + I₄)` with
`(1/((u - v)⁴(v - z̄)²) - 2/((u - v)⁵(v - z̄)) + 2/((u - v)⁵(u - z̄)) + 1/((u - v)⁴(u - z̄)²)) μ(u)ν(v)`, and each of the
four terms vanishes in the limit, so (7.2) is `0`. -/
theorem s74_eq_7_4 {μ ν φ ψ : ℂ → ℂ} (hμ : IsHarmonicU μ φ) (hν : IsHarmonicU ν ψ) {z : ℂ} (hz : z ∈ upperHalf) :
    Tendsto (fun δ : ℝ => ∫ p in (upperHalf ×ˢ upperHalf) ∩ {p : ℂ × ℂ | δ ≤ ‖p.1 - p.2‖},
        μ p.1 * ν p.2 / ((p.1 - conj z) ^ 2 * (p.1 - p.2) ^ 2 * (p.2 - conj z) ^ 2)) (𝓝[>] 0) (𝓝 0) ∧
      ∀ δ > 0, ∫ p in (upperHalf ×ˢ upperHalf) ∩ {p : ℂ × ℂ | δ ≤ ‖p.1 - p.2‖},
          μ p.1 * ν p.2 / ((p.1 - conj z) ^ 2 * (p.1 - p.2) ^ 2 * (p.2 - conj z) ^ 2) =
        ∫ p in (upperHalf ×ˢ upperHalf) ∩ {p : ℂ × ℂ | δ ≤ ‖p.1 - p.2‖},
          (1 / ((p.1 - p.2) ^ 4 * (p.2 - conj z) ^ 2) - 2 / ((p.1 - p.2) ^ 5 * (p.2 - conj z)) +
            2 / ((p.1 - p.2) ^ 5 * (p.1 - conj z)) + 1 / ((p.1 - p.2) ^ 4 * (p.1 - conj z) ^ 2)) * μ p.1 * ν p.2 := by
  refine ⟨?_, fun δ hδ => eq_7_4_integral_identity μ ν hz hδ⟩
  -- the limit functional `L` of `s71_bridge72` vanishes on nice pairs and is symmetric
  have hL0 : ∀ {a b α β : ℂ → ℂ}, IsHarmonicU a α → IsHarmonicU b β →
      (∃ K : ℝ, ∀ u ∈ upperHalf, ‖α u‖ ≤ K * ((1 + ‖u‖) ^ 4)⁻¹) →
      (∃ K : ℝ, ∀ u ∈ upperHalf, ‖β u‖ ≤ K * ((1 + ‖u‖) ^ 4)⁻¹) →
      (∫ u in upperHalf, a u / (u - conj z) ^ 2 * pv2 (fun v => b v / ((u - v) ^ 2 * (v - conj z) ^ 2)) u z) = 0 :=
    fun ha hb hα hβ => tendsto_nhds_unique (s71_bridge72 ha hb hz) (s74_nice ha hb hα hβ hz)
  have hLs : ∀ {a b α β : ℂ → ℂ}, IsHarmonicU a α → IsHarmonicU b β →
      (∫ u in upperHalf, a u / (u - conj z) ^ 2 * pv2 (fun v => b v / ((u - v) ^ 2 * (v - conj z) ^ 2)) u z) =
        ∫ u in upperHalf, b u / (u - conj z) ^ 2 * pv2 (fun v => a v / ((u - v) ^ 2 * (v - conj z) ^ 2)) u z := by
    intro a b α β ha hb
    have h1 := s71_bridge72 ha hb hz
    simp only [s74_sym a b z] at h1
    exact tendsto_nhds_unique h1 (s71_bridge72 hb ha hz)
  obtain ⟨μs, φs, Mμ, hμs, hμn, hμM, hμl⟩ := s74_approx hμ
  obtain ⟨νs, ψs, Mν, hνs, hνn, hνM, hνl⟩ := s74_approx hν
  have h1 : ∀ n, (∫ u in upperHalf, ν u / (u - conj z) ^ 2 *
      pv2 (fun v => μs n v / ((u - v) ^ 2 * (v - conj z) ^ 2)) u z) = 0 := fun n =>
    tendsto_nhds_unique (s74_cont hνs hν (hμs n) hνM hνl hz)
      (tendsto_const_nhds.congr fun m => (hL0 (hνs m) (hμs n) (hνn m) (hμn n)).symm)
  have h2 : (∫ u in upperHalf, μ u / (u - conj z) ^ 2 *
      pv2 (fun v => ν v / ((u - v) ^ 2 * (v - conj z) ^ 2)) u z) = 0 :=
    tendsto_nhds_unique (s74_cont hμs hμ hν hμM hμl hz)
      (tendsto_const_nhds.congr fun n => ((hLs (hμs n) hν).trans (h1 n)).symm)
  have hb := s71_bridge72 hμ hν hz
  rw [h2] at hb
  exact hb

/-- **(7.4)** (TT:2729) and the vanishing of the holomorphic variation. For `μ, ν ∈ Ω^{-1,1}(𝕌)`, the principal value
integral of (7.2) equals `lim_{ε → 0} ∬∬_{|u - v| ≥ ε} (I₁ + I₂ + I₃ + I₄)` with
`(1/((u - v)⁴(v - z̄)²) - 2/((u - v)⁵(v - z̄)) + 2/((u - v)⁵(u - z̄)) + 1/((u - v)⁴(u - z̄)²)) μ(u)ν(v)`, and each of the
four terms vanishes in the limit, so (7.2) is `0`. -/
theorem eq_7_4 {μ ν φ ψ : ℂ → ℂ} (hμ : IsHarmonicU μ φ) (hν : IsHarmonicU ν ψ) {z : ℂ} (hz : z ∈ upperHalf) :
    Tendsto (fun δ : ℝ => ∫ p in (upperHalf ×ˢ upperHalf) ∩ {p : ℂ × ℂ | δ ≤ ‖p.1 - p.2‖},
        μ p.1 * ν p.2 / ((p.1 - conj z) ^ 2 * (p.1 - p.2) ^ 2 * (p.2 - conj z) ^ 2)) (𝓝[>] 0) (𝓝 0) ∧
      ∀ δ > 0, ∫ p in (upperHalf ×ˢ upperHalf) ∩ {p : ℂ × ℂ | δ ≤ ‖p.1 - p.2‖},
          μ p.1 * ν p.2 / ((p.1 - conj z) ^ 2 * (p.1 - p.2) ^ 2 * (p.2 - conj z) ^ 2) =
        ∫ p in (upperHalf ×ˢ upperHalf) ∩ {p : ℂ × ℂ | δ ≤ ‖p.1 - p.2‖},
          (1 / ((p.1 - p.2) ^ 4 * (p.2 - conj z) ^ 2) - 2 / ((p.1 - p.2) ^ 5 * (p.2 - conj z)) +
            2 / ((p.1 - p.2) ^ 5 * (p.1 - conj z)) + 1 / ((p.1 - p.2) ^ 4 * (p.1 - conj z) ^ 2)) * μ p.1 * ν p.2 :=
  s74_eq_7_4 hμ hν hz

end TakhtajanTeo
