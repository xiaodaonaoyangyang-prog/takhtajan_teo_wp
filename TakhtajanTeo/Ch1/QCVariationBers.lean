import TakhtajanTeo.Ch1.QCVariation

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal ComplexConjugate Real BoundedContinuousFunction

noncomputable section

namespace TakhtajanTeo
namespace QCV

open LiZhongQC


/-- Closed forms of the `ζ`-derivatives of the Ahlfors–Bers kernel `ahKer ζ u = ζ(ζ-1)/(u(u-1)(u-ζ))`. -/
def kerD1 (ζ u : ℂ) : ℂ := -1 / (u * (u - 1)) + 1 / (u - ζ) ^ 2
def kerD2 (ζ u : ℂ) : ℂ := 2 / (u - ζ) ^ 3
def kerD3 (ζ u : ℂ) : ℂ := 6 / (u - ζ) ^ 4

theorem qcv_ahKer_split {ζ u : ℂ} (h0 : u ≠ 0) (h1 : u ≠ 1) (hζ : u ≠ ζ) :
    ahKer ζ u = -(ζ + (u - 1)) / (u * (u - 1)) + 1 / (u - ζ) := by
  have h1' : u - 1 ≠ 0 := sub_ne_zero.2 h1
  have h2' : u - ζ ≠ 0 := sub_ne_zero.2 hζ
  unfold ahKer
  field_simp
  ring

theorem qcv_hasDerivAt_ahKer {ζ u : ℂ} (h0 : u ≠ 0) (h1 : u ≠ 1) (hζ : u ≠ ζ) :
    HasDerivAt (fun x => ahKer x u) (kerD1 ζ u) ζ := by
  have h2' : u - ζ ≠ 0 := sub_ne_zero.2 hζ
  have hev : (fun x => ahKer x u) =ᶠ[𝓝 ζ] fun x => -(x + (u - 1)) / (u * (u - 1)) + 1 / (u - x) := by
    have : ∀ᶠ x in 𝓝 ζ, x ≠ u := eventually_ne_nhds hζ.symm
    filter_upwards [this] with x hx using qcv_ahKer_split h0 h1 hx.symm
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  have hA : HasDerivAt (fun x : ℂ => -(x + (u - 1)) / (u * (u - 1))) (-1 / (u * (u - 1))) ζ :=
    (((hasDerivAt_id' ζ).add_const (u - 1)).neg).div_const (u * (u - 1))
  have hB : HasDerivAt (fun x : ℂ => 1 / (u - x)) (1 / (u - ζ) ^ 2) ζ := by
    have h := ((hasDerivAt_id' ζ).const_sub u).inv h2'
    simp only [one_div]
    exact h.congr_deriv (by ring)
  exact hA.add hB

theorem qcv_hasDerivAt_kerD1 {ζ u : ℂ} (hζ : u ≠ ζ) :
    HasDerivAt (fun x => kerD1 x u) (kerD2 ζ u) ζ := by
  have h2' : u - ζ ≠ 0 := sub_ne_zero.2 hζ
  have h := (((hasDerivAt_id ζ).const_sub u).pow 2).inv (by simpa using pow_ne_zero 2 h2')
  have h' := h.const_add (-1 / (u * (u - 1)))
  convert h' using 1
  · funext x; simp [kerD1, one_div]
  · simp [kerD2]; field_simp

theorem qcv_hasDerivAt_kerD2 {ζ u : ℂ} (hζ : u ≠ ζ) :
    HasDerivAt (fun x => kerD2 x u) (kerD3 ζ u) ζ := by
  have h2' : u - ζ ≠ 0 := sub_ne_zero.2 hζ
  have h := ((((hasDerivAt_id ζ).const_sub u).pow 3).inv (by simpa using pow_ne_zero 3 h2')).const_mul 2
  convert h using 1
  · funext x; simp [kerD2, div_eq_mul_inv]
  · simp [kerD3]; field_simp; ring



theorem qcv_tlu_iter {ι : Type*} {l : Filter ι} [l.NeBot] {U : Set ℂ} (hU : IsOpen U) (j : ℕ) :
    ∀ {G : ι → ℂ → ℂ} {g : ℂ → ℂ}, TendstoLocallyUniformlyOn G g l U →
      (∀ᶠ i in l, DifferentiableOn ℂ (G i) U) →
      TendstoLocallyUniformlyOn (fun i => iteratedDeriv j (G i)) (iteratedDeriv j g) l U := by
  induction j with
  | zero => intro G g h _; simpa using h
  | succ j ih =>
    intro G g h hG
    simp only [iteratedDeriv_succ']
    exact ih (G := fun i => deriv (G i)) (g := deriv g) (h.deriv hG hU)
      (hG.mono fun i hi => hi.deriv hU)

theorem qcv_param_hasDerivAt_iter (j : ℕ) {F : ℂ → ℂ → ℂ} {c : ℂ} {r R M : ℝ} (hr : 0 < r) (hR : 0 < R)
    (hζ : ∀ t ∈ ball (0 : ℂ) r, DifferentiableOn ℂ (F t) (ball c R))
    (ht : ∀ ζ ∈ ball c R, DifferentiableOn ℂ (fun t => F t ζ) (ball (0 : ℂ) r))
    (hM : ∀ t ∈ ball (0 : ℂ) r, ∀ ζ ∈ ball c R, ‖F t ζ‖ ≤ M) :
    HasDerivAt (fun t => iteratedDeriv j (F t) c)
      (iteratedDeriv j (fun ζ => deriv (fun t => F t ζ) 0) c) 0 := by
  have hcR : c ∈ ball c R := mem_ball_self hR
  have h0r : (0 : ℂ) ∈ ball (0 : ℂ) r := mem_ball_self hr
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0 h0r c hcR)
  set V : ℂ → ℂ := fun ζ => deriv (fun t => F t ζ) 0 with hV
  set ρ : ℝ := r / 2 with hρ
  have hρpos : 0 < ρ := by positivity
  have hρsub : closedBall (0 : ℂ) ρ ⊆ ball (0 : ℂ) r := by
    intro t ht'
    simp only [mem_closedBall, dist_zero_right, mem_ball] at ht' ⊢
    linarith
  have hbound : ∀ ζ ∈ ball c R, ∀ t : ℂ, t ∈ closedBall (0 : ℂ) ρ → t ≠ 0 →
      ‖(F t ζ - F 0 ζ) / t - V ζ‖ ≤ 4 * M * ‖t‖ / ρ ^ 2 := by
    intro ζ hζ' t htρ htne
    have := (qcv_taylor2 (φ := fun s => F s ζ) hρpos ((ht ζ hζ').mono hρsub)
      (fun s hs => hM s (hρsub hs) ζ hζ')).2.2 t htρ
    have hn : 0 < ‖t‖ := norm_pos_iff.2 htne
    have e : (F t ζ - F 0 ζ) / t - V ζ = (F t ζ - F 0 ζ - t • deriv (fun s => F s ζ) 0) / t := by
      simp only [hV, smul_eq_mul]; field_simp
    rw [e, norm_div]
    rw [div_le_iff₀ hn]
    calc ‖F t ζ - F 0 ζ - t • deriv (fun s => F s ζ) 0‖ ≤ 4 * M * ‖t‖ ^ 2 / ρ ^ 2 := this
      _ = 4 * M * ‖t‖ / ρ ^ 2 * ‖t‖ := by ring
  have hQ : TendstoUniformlyOn (fun t ζ => (F t ζ - F 0 ζ) / t) V (𝓝[≠] (0 : ℂ)) (ball c R) := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    set δ : ℝ := min ρ (ε * ρ ^ 2 / (4 * M + 1)) with hδ
    have hδpos : 0 < δ := lt_min hρpos (by positivity)
    have hev : ∀ᶠ t in 𝓝[≠] (0 : ℂ), t ∈ ball (0 : ℂ) δ ∧ t ≠ 0 :=
      eventually_nhdsWithin_of_eventually_nhds (ball_mem_nhds _ hδpos) |>.and self_mem_nhdsWithin
    filter_upwards [hev] with t ht'
    intro ζ hζ'
    obtain ⟨htδ, htne⟩ := ht'
    have htn : ‖t‖ < δ := by simpa using htδ
    have htρ : t ∈ closedBall (0 : ℂ) ρ := by
      simp only [mem_closedBall, dist_zero_right]
      exact (htn.trans_le (min_le_left _ _)).le
    have h1 := hbound ζ hζ' t htρ htne
    rw [dist_comm, dist_eq_norm]
    refine h1.trans_lt ?_
    rw [div_lt_iff₀ (by positivity)]
    have h2 : ‖t‖ < ε * ρ ^ 2 / (4 * M + 1) := htn.trans_le (min_le_right _ _)
    rw [lt_div_iff₀ (by positivity)] at h2
    nlinarith [norm_nonneg t]
  have hlu := hQ.tendstoLocallyUniformlyOn
  have hdiff : ∀ᶠ t in 𝓝[≠] (0 : ℂ), DifferentiableOn ℂ (fun ζ => (F t ζ - F 0 ζ) / t) (ball c R) := by
    have : ∀ᶠ t in 𝓝[≠] (0 : ℂ), t ∈ ball (0 : ℂ) r :=
      eventually_nhdsWithin_of_eventually_nhds (ball_mem_nhds _ hr)
    filter_upwards [this] with t htr
    exact ((hζ t htr).sub (hζ 0 h0r)).div_const t
  have hit := (qcv_tlu_iter isOpen_ball j hlu hdiff).tendsto_at hcR
  rw [hasDerivAt_iff_tendsto_slope]
  refine hit.congr' ?_
  have : ∀ᶠ t in 𝓝[≠] (0 : ℂ), t ∈ ball (0 : ℂ) r :=
    eventually_nhdsWithin_of_eventually_nhds (ball_mem_nhds _ hr)
  filter_upwards [this, self_mem_nhdsWithin] with t htr htne
  have hc1 : ContDiffAt ℂ j (F t) c :=
    ((hζ t htr).contDiffOn isOpen_ball).contDiffAt (isOpen_ball.mem_nhds hcR)
  have hc0 : ContDiffAt ℂ j (F 0) c :=
    ((hζ 0 h0r).contDiffOn isOpen_ball).contDiffAt (isOpen_ball.mem_nhds hcR)
  have e : (fun ζ => (F t ζ - F 0 ζ) / t) = fun ζ => (F t - F 0) ζ / t := rfl
  rw [e, iteratedDeriv_div_const, iteratedDeriv_sub hc1 hc0]
  simp only [slope_def_field, sub_zero]


/-! ### Kernel majorants -/

theorem qcv_r0 {N a e x q : ℝ} (hN : N ≤ 2) (hN0 : 0 ≤ N) (ha : 0 < a) (he : 0 < e) (hq : 0 < q)
    (hx : q * a ≤ x) : N / (a * e * x) ≤ (2 / q) * (1 / (a ^ 2 * e)) := by
  have hx0 : 0 < x := lt_of_lt_of_le (by positivity) hx
  rw [div_le_iff₀ (by positivity)]
  have : (2 / q) * (1 / (a ^ 2 * e)) * (a * e * x) = 2 * x / (q * a) := by field_simp
  rw [this, le_div_iff₀ (by positivity)]
  nlinarith

theorem qcv_r1 {N a e x q : ℝ} (hN : N ≤ 4 * a) (hN0 : 0 ≤ N) (ha : 0 < a) (he : 0 < e) (hq : 0 < q)
    (hx : q * a ≤ x) : N / (a * e * x ^ 2) ≤ (4 / q ^ 2) * (1 / (a ^ 2 * e)) := by
  have hx0 : 0 < x := lt_of_lt_of_le (by positivity) hx
  rw [div_le_iff₀ (by positivity)]
  have : (4 / q ^ 2) * (1 / (a ^ 2 * e)) * (a * e * x ^ 2) = 4 * x ^ 2 / (q ^ 2 * a) := by field_simp
  rw [this, le_div_iff₀ (by positivity)]
  have h2 : (q * a) ^ 2 ≤ x ^ 2 := pow_le_pow_left₀ (by positivity) hx 2
  nlinarith [mul_nonneg hq.le ha.le]

theorem qcv_r2 {a e x q : ℝ} (ha : 1 < a) (he : 0 < e) (hea : e ≤ 2 * a) (hq : 0 < q)
    (hx : q * a ≤ x) : 2 / x ^ 3 ≤ (4 / q ^ 3) * (1 / (a ^ 2 * e)) := by
  have ha0 : 0 < a := by linarith
  have hx0 : 0 < x := lt_of_lt_of_le (by positivity) hx
  have h3 : (q * a) ^ 3 ≤ x ^ 3 := pow_le_pow_left₀ (by positivity) hx 3
  rw [div_le_iff₀ (by positivity)]
  have : (4 / q ^ 3) * (1 / (a ^ 2 * e)) * x ^ 3 = 4 * x ^ 3 / (q ^ 3 * (a ^ 2 * e)) := by field_simp
  rw [this, le_div_iff₀ (by positivity)]
  have h4 : q ^ 3 * a ^ 3 ≤ x ^ 3 := by simpa [mul_pow] using h3
  have h5 : 0 < q ^ 3 := by positivity
  have h6 : a ^ 2 * e ≤ 2 * a ^ 3 := by nlinarith [sq_nonneg a]
  nlinarith [mul_nonneg h5.le (sq_nonneg a)]

theorem qcv_r3 {a e x q : ℝ} (ha : 1 < a) (he : 0 < e) (hea : e ≤ 2 * a) (hq : 0 < q)
    (hx : q * a ≤ x) : 6 / x ^ 4 ≤ (12 / q ^ 4) * (1 / (a ^ 2 * e)) := by
  have ha0 : 0 < a := by linarith
  have hx0 : 0 < x := lt_of_lt_of_le (by positivity) hx
  have h3 : (q * a) ^ 4 ≤ x ^ 4 := pow_le_pow_left₀ (by positivity) hx 4
  rw [div_le_iff₀ (by positivity)]
  have : (12 / q ^ 4) * (1 / (a ^ 2 * e)) * x ^ 4 = 12 * x ^ 4 / (q ^ 4 * (a ^ 2 * e)) := by field_simp
  rw [this, le_div_iff₀ (by positivity)]
  have h4 : q ^ 4 * a ^ 4 ≤ x ^ 4 := by simpa [mul_pow] using h3
  have h5 : 0 < q ^ 4 := by positivity
  have h6 : a ^ 2 * e ≤ 2 * a ^ 3 := by nlinarith [sq_nonneg a]
  have h7 : a ^ 3 ≤ a ^ 4 := pow_le_pow_right₀ ha.le (by norm_num)
  nlinarith [mul_nonneg h5.le (sq_nonneg a), mul_pos h5 (pow_pos ha0 3)]

theorem qcv_ker_majorant {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ : ρ < 1) {ζ u : ℂ} (hζ : ‖ζ‖ ≤ ρ)
    (hu : 1 < ‖u‖) :
    ‖ahKer ζ u‖ ≤ 12 / (1 - ρ) ^ 4 * ‖ahKer (-1) u‖ ∧
    ‖kerD1 ζ u‖ ≤ 12 / (1 - ρ) ^ 4 * ‖ahKer (-1) u‖ ∧
    ‖kerD2 ζ u‖ ≤ 12 / (1 - ρ) ^ 4 * ‖ahKer (-1) u‖ ∧
    ‖kerD3 ζ u‖ ≤ 12 / (1 - ρ) ^ 4 * ‖ahKer (-1) u‖ := by
  set a : ℝ := ‖u‖ with ha
  set q : ℝ := 1 - ρ with hq
  have hq0 : 0 < q := by rw [hq]; linarith
  have hq1 : q ≤ 1 := by rw [hq]; linarith
  have ha0 : 0 < a := by linarith
  have hu0 : u ≠ 0 := norm_pos_iff.1 ha0
  have hu1 : u - 1 ≠ 0 := by
    intro h; have : u = 1 := by linear_combination h
    have h1 : a = 1 := by rw [ha, this]; simp
    linarith
  have hu2 : u + 1 ≠ 0 := by
    intro h; have : u = -1 := by linear_combination h
    have h1 : a = 1 := by rw [ha, this]; simp
    linarith
  set e : ℝ := ‖u - 1‖ with he
  have he0 : 0 < e := norm_pos_iff.2 hu1
  have hea : e ≤ 2 * a := by
    have := norm_sub_le u 1
    rw [norm_one] at this; linarith
  have hf : ‖u + 1‖ ≤ 2 * a := by
    have := norm_add_le u 1
    rw [norm_one] at this; linarith
  have hf0 : 0 < ‖u + 1‖ := norm_pos_iff.2 hu2
  have hda : q * a ≤ ‖u - ζ‖ := by
    have := norm_sub_norm_le u ζ
    rw [hq]; nlinarith
  have hxne : u - ζ ≠ 0 := norm_pos_iff.1 (lt_of_lt_of_le (by positivity) hda)
  have hnorm : ‖ahKer (-1) u‖ = 2 / (a * e * ‖u + 1‖) := by
    unfold ahKer
    have : (-1 : ℂ) * (-1 - 1) = 2 := by norm_num
    rw [this, norm_div, norm_mul, norm_mul]
    simp [ha, he, sub_neg_eq_add]
  have hkey : 1 / (a ^ 2 * e) ≤ ‖ahKer (-1) u‖ := by
    rw [hnorm, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_pos ha0 he0]
  have hC : ∀ c : ℝ, 0 ≤ c → ∀ X : ℝ, X ≤ c * (1 / (a ^ 2 * e)) → c ≤ 12 / q ^ 4 →
      X ≤ 12 / q ^ 4 * ‖ahKer (-1) u‖ := by
    intro c hc X hX hcC
    calc X ≤ c * (1 / (a ^ 2 * e)) := hX
      _ ≤ 12 / q ^ 4 * (1 / (a ^ 2 * e)) := by gcongr
      _ ≤ 12 / q ^ 4 * ‖ahKer (-1) u‖ := by gcongr
  have hq4 : 0 < q ^ 4 := by positivity
  have hcmp : ∀ k : ℕ, 1 ≤ k → k ≤ 4 → ∀ c : ℝ, 0 ≤ c → c ≤ 12 → c / q ^ k ≤ 12 / q ^ 4 := by
    intro k hk1 hk4 c hc hc12
    rw [div_le_div_iff₀ (by positivity) hq4]
    have : q ^ 4 ≤ q ^ k := pow_le_pow_of_le_one hq0.le hq1 hk4
    nlinarith [pow_pos hq0 k]
  have hζ1 : ‖ζ‖ ≤ 1 := by linarith
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- ahKer ζ u
    have h1 : ‖ahKer ζ u‖ = (‖ζ‖ * ‖ζ - 1‖) / (a * e * ‖u - ζ‖) := by
      unfold ahKer; simp [norm_div, norm_mul, ha, he]
    have hN : ‖ζ‖ * ‖ζ - 1‖ ≤ 2 := by
      have : ‖ζ - 1‖ ≤ 2 := by
        have := norm_sub_le ζ 1; rw [norm_one] at this; linarith
      nlinarith [norm_nonneg ζ, norm_nonneg (ζ - 1)]
    refine hC (2 / q) (by positivity) _ ?_ ?_
    · rw [h1]; exact qcv_r0 hN (by positivity) ha0 he0 hq0 hda
    · have := hcmp 1 le_rfl (by norm_num) 2 (by norm_num) (by norm_num); simpa using this
  · -- kerD1
    have hid : kerD1 ζ u = (2 * ζ * u - ζ ^ 2 - u) / (u * (u - 1) * (u - ζ) ^ 2) := by
      unfold kerD1; field_simp; ring
    have h1 : ‖kerD1 ζ u‖ = ‖2 * ζ * u - ζ ^ 2 - u‖ / (a * e * ‖u - ζ‖ ^ 2) := by
      rw [hid]; simp [norm_div, norm_mul, norm_pow, ha, he]
    have hN : ‖2 * ζ * u - ζ ^ 2 - u‖ ≤ 4 * a := by
      have h2 := norm_sub_le (2 * ζ * u - ζ ^ 2) u
      have h3 := norm_sub_le (2 * ζ * u) (ζ ^ 2)
      have h4 : ‖2 * ζ * u‖ = 2 * ‖ζ‖ * a := by simp [norm_mul, ha]
      have h5 : ‖ζ ^ 2‖ = ‖ζ‖ ^ 2 := norm_pow _ _
      have h6 : ‖ζ‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg ζ]
      nlinarith [norm_nonneg ζ]
    refine hC (4 / q ^ 2) (by positivity) _ ?_ ?_
    · rw [h1]; exact qcv_r1 hN (norm_nonneg _) ha0 he0 hq0 hda
    · exact hcmp 2 (by norm_num) (by norm_num) 4 (by norm_num) (by norm_num)
  · -- kerD2
    have h1 : ‖kerD2 ζ u‖ = 2 / ‖u - ζ‖ ^ 3 := by
      unfold kerD2; simp [norm_div, norm_pow]
    refine hC (4 / q ^ 3) (by positivity) _ ?_ ?_
    · rw [h1]; exact qcv_r2 hu he0 hea hq0 hda
    · exact hcmp 3 (by norm_num) (by norm_num) 4 (by norm_num) (by norm_num)
  · -- kerD3
    have h1 : ‖kerD3 ζ u‖ = 6 / ‖u - ζ‖ ^ 4 := by
      unfold kerD3; simp [norm_div, norm_pow]
    refine hC (12 / q ^ 4) (by positivity) _ ?_ le_rfl
    rw [h1]; exact qcv_r3 hu he0 hea hq0 hda

/-! ### Differentiation under the integral over `𝔻*` -/

theorem qcv_hasDerivAt_extIntegral (ν : LinfStar) {A B : ℂ → ℂ → ℂ} {ζ₀ : ℂ} {ρ Cc : ℝ}
    (hρ : ‖ζ₀‖ < ρ) (hρ1 : ρ < 1)
    (hAm : ∀ ζ, ‖ζ‖ ≤ ρ → Measurable (A ζ)) (hBm : Measurable (B ζ₀))
    (hAb : ∀ ζ, ‖ζ‖ ≤ ρ → ∀ u, 1 < ‖u‖ → ‖A ζ u‖ ≤ Cc * ‖ahKer (-1) u‖)
    (hBb : ∀ ζ, ‖ζ‖ ≤ ρ → ∀ u, 1 < ‖u‖ → ‖B ζ u‖ ≤ Cc * ‖ahKer (-1) u‖)
    (hd : ∀ ζ, ‖ζ‖ ≤ ρ → ∀ u, 1 < ‖u‖ → HasDerivAt (fun x => A x u) (B ζ u) ζ) :
    HasDerivAt (fun ζ => ∫ u in unitDiscExterior, ν u * A ζ u)
      (∫ u in unitDiscExterior, ν u * B ζ₀ u) ζ₀ := by
  have hmeas : MeasurableSet unitDiscExterior := (isOpen_lt continuous_const continuous_norm).measurableSet
  set μ : Measure ℂ := volume.restrict unitDiscExterior with hμ
  have hmem : ∀ᵐ u ∂μ, 1 < ‖u‖ := by
    filter_upwards [ae_restrict_mem hmeas] with u hu using hu
  have hnu := LinfStar_ae_norm_le ν
  have hκ : Integrable (fun u => ‖ν‖ * (Cc * ‖ahKer (-1) u‖)) μ :=
    (((ah_ker_integrable (-1)).norm.const_mul Cc).const_mul ‖ν‖).integrableOn
  have hνm : AEStronglyMeasurable (fun u => ν u) μ := Lp.aestronglyMeasurable ν
  have hball : ∀ ζ, ζ ∈ ball ζ₀ (ρ - ‖ζ₀‖) → ‖ζ‖ ≤ ρ := by
    intro ζ hζ
    simp only [mem_ball, dist_eq_norm] at hζ
    have := norm_le_norm_add_norm_sub' ζ ζ₀
    linarith
  have hζ₀ : ‖ζ₀‖ ≤ ρ := hρ.le
  have hFint : ∀ ζ, ‖ζ‖ ≤ ρ → Integrable (fun u => ν u * A ζ u) μ := by
    intro ζ hζ
    refine hκ.mono' (hνm.mul (hAm ζ hζ).aestronglyMeasurable) ?_
    filter_upwards [hnu, hmem] with u h1 h2
    rw [norm_mul]
    exact mul_le_mul h1 (hAb ζ hζ u h2) (norm_nonneg _) (norm_nonneg _)
  have := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ) (x₀ := ζ₀)
    (F := fun ζ u => ν u * A ζ u) (F' := fun ζ u => ν u * B ζ u)
    (bound := fun u => ‖ν‖ * (Cc * ‖ahKer (-1) u‖))
    (ball_mem_nhds ζ₀ (sub_pos.2 hρ))
    (by
      filter_upwards [ball_mem_nhds ζ₀ (sub_pos.2 hρ)] with ζ hζ
      exact (hFint ζ (hball ζ hζ)).aestronglyMeasurable)
    (hFint ζ₀ hζ₀)
    (hνm.mul hBm.aestronglyMeasurable)
    (by
      filter_upwards [hnu, hmem] with u h1 h2 ζ hζ
      rw [norm_mul]
      exact mul_le_mul h1 (hBb ζ (hball ζ hζ) u h2) (norm_nonneg _) (norm_nonneg _))
    hκ
    (by
      filter_upwards [hmem] with u h2 ζ hζ
      exact (hd ζ (hball ζ hζ) u h2).const_mul (ν u))
  exact this.2

theorem qcv_extK_deriv (ν : LinfStar) {ζ : ℂ} (hζ : ‖ζ‖ < 1) :
    HasDerivAt (fun x => ∫ u in unitDiscExterior, ν u * ahKer x u)
      (∫ u in unitDiscExterior, ν u * kerD1 ζ u) ζ ∧
    HasDerivAt (fun x => ∫ u in unitDiscExterior, ν u * kerD1 x u)
      (∫ u in unitDiscExterior, ν u * kerD2 ζ u) ζ ∧
    HasDerivAt (fun x => ∫ u in unitDiscExterior, ν u * kerD2 x u)
      (∫ u in unitDiscExterior, ν u * kerD3 ζ u) ζ := by
  set ρ : ℝ := (1 + ‖ζ‖) / 2 with hρdef
  have hρ : ‖ζ‖ < ρ := by rw [hρdef]; linarith
  have hρ1 : ρ < 1 := by rw [hρdef]; linarith
  have hρ0 : 0 ≤ ρ := by rw [hρdef]; positivity
  have hmaj := fun {x u : ℂ} (hx : ‖x‖ ≤ ρ) (hu : 1 < ‖u‖) => qcv_ker_majorant hρ0 hρ1 hx hu
  have hne : ∀ {x u : ℂ}, ‖x‖ ≤ ρ → 1 < ‖u‖ → u ≠ 0 ∧ u ≠ 1 ∧ u ≠ x := by
    intro x u hx hu
    refine ⟨?_, ?_, ?_⟩
    · intro h; rw [h] at hu; simp at hu; linarith
    · intro h; rw [h] at hu; simp at hu
    · intro h; rw [h] at hu; linarith
  have mAh : ∀ x : ℂ, Measurable (fun u => ahKer x u) := fun x => by unfold ahKer; fun_prop
  have m1 : ∀ x : ℂ, Measurable (fun u => kerD1 x u) := fun x => by unfold kerD1; fun_prop
  have m2 : ∀ x : ℂ, Measurable (fun u => kerD2 x u) := fun x => by unfold kerD2; fun_prop
  have m3 : ∀ x : ℂ, Measurable (fun u => kerD3 x u) := fun x => by unfold kerD3; fun_prop
  refine ⟨?_, ?_, ?_⟩
  · refine qcv_hasDerivAt_extIntegral ν (A := fun x u => ahKer x u) (B := fun x u => kerD1 x u)
      (Cc := 12 / (1 - ρ) ^ 4) hρ hρ1 (fun x _ => mAh x) (m1 ζ)
      (fun x hx u hu => (hmaj hx hu).1) (fun x hx u hu => (hmaj hx hu).2.1) ?_
    intro x hx u hu
    obtain ⟨h0, h1, h2⟩ := hne hx hu
    exact qcv_hasDerivAt_ahKer h0 h1 h2
  · refine qcv_hasDerivAt_extIntegral ν (A := fun x u => kerD1 x u) (B := fun x u => kerD2 x u)
      (Cc := 12 / (1 - ρ) ^ 4) hρ hρ1 (fun x _ => m1 x) (m2 ζ)
      (fun x hx u hu => (hmaj hx hu).2.1) (fun x hx u hu => (hmaj hx hu).2.2.1) ?_
    intro x hx u hu
    exact qcv_hasDerivAt_kerD1 (hne hx hu).2.2
  · refine qcv_hasDerivAt_extIntegral ν (A := fun x u => kerD2 x u) (B := fun x u => kerD3 x u)
      (Cc := 12 / (1 - ρ) ^ 4) hρ hρ1 (fun x _ => m2 x) (m3 ζ)
      (fun x hx u hu => (hmaj hx hu).2.2.1) (fun x hx u hu => (hmaj hx hu).2.2.2) ?_
    intro x hx u hu
    exact qcv_hasDerivAt_kerD2 (hne hx hu).2.2

theorem qcv_extK_iter3 (ν : LinfStar) {z : ℂ} (hz : ‖z‖ < 1) :
    iteratedDeriv 3 (fun x => ∫ u in unitDiscExterior, ν u * ahKer x u) z =
      ∫ u in unitDiscExterior, ν u * kerD3 z u := by
  have hnhds : ball (0 : ℂ) 1 ∈ 𝓝 z := isOpen_ball.mem_nhds (by simpa using hz)
  have e1 : deriv (fun x => ∫ u in unitDiscExterior, ν u * ahKer x u) =ᶠ[𝓝 z]
      fun x => ∫ u in unitDiscExterior, ν u * kerD1 x u := by
    filter_upwards [hnhds] with x hx
    exact (qcv_extK_deriv ν (by simpa using hx)).1.deriv
  have e2 : deriv (fun x => ∫ u in unitDiscExterior, ν u * kerD1 x u) =ᶠ[𝓝 z]
      fun x => ∫ u in unitDiscExterior, ν u * kerD2 x u := by
    filter_upwards [hnhds] with x hx
    exact (qcv_extK_deriv ν (by simpa using hx)).2.1.deriv
  have e3 := (qcv_extK_deriv ν hz).2.2.deriv
  rw [iteratedDeriv_succ', iteratedDeriv_succ', iteratedDeriv_succ', iteratedDeriv_zero]
  exact (e1.deriv.trans e2).deriv_eq.trans e3

/-! ### First variation of the plane solution at `0` -/

theorem qcv_extB_smul_ae (t : ℂ) (ν : LinfStar) : extB (t • ν) =ᵐ[volume] fun u => t * extB ν u := by
  have hmeas : MeasurableSet unitDiscExterior := (isOpen_lt continuous_const continuous_norm).measurableSet
  have h := Lp.coeFn_smul t ν
  have h' := (ae_restrict_iff' hmeas).1 h
  filter_upwards [h'] with u hu
  by_cases hm : u ∈ unitDiscExterior
  · have e1 := hu hm
    simp [extB, Set.indicator_of_mem hm, e1]
  · simp [extB, Set.indicator_of_notMem hm]

theorem qcv_W_hasDerivAt (ν : LinfStar) (ζ : ℂ) :
    HasDerivAt (fun t : ℂ => normalizedSolution (extB (t • ν)) ζ)
      (-(1 / π : ℂ) * ∫ u in unitDiscExterior, ν u * ahKer ζ u) 0 := by
  have hg0 : IsBeltramiCoeff (0 : ℂ → ℂ) univ 0 :=
    ⟨aestronglyMeasurable_zero, Filter.Eventually.of_forall fun u => by simp⟩
  have hf0 : IsNormalizedSolution id (0 : ℂ → ℂ) := by
    have := qcv_ns_spec le_rfl zero_lt_one hg0
    rwa [bB_l_normalizedSolution_zero] at this
  have hext := extB_isBeltramiCoeff ν
  have hT : ∀ t : ℂ, IsBeltramiCoeff (fun u => t * extB ν u) univ (‖ν‖ * ‖t‖) := by
    intro t
    refine ⟨hext.1.const_mul t, ?_⟩
    filter_upwards [hext.2] with u hu
    rw [norm_mul, mul_comm ‖ν‖]
    exact mul_le_mul_of_nonneg_left hu (norm_nonneg t)
  have hTlin : ∀ (a : ℂ) (v₁ v₂ : ℂ), (fun u => (a • v₁ + v₂) * extB ν u) =ᵐ[volume]
      fun u => a * (v₁ * extB ν u) + v₂ * extB ν u := by
    intro a v₁ v₂
    exact Filter.Eventually.of_forall fun u => by simp only [smul_eq_mul]; ring
  obtain ⟨L, hL1, hL⟩ := qcv_plane_hasFDerivAt (E := ℂ) (g₀ := (0 : ℂ → ℂ)) (f₀ := id) (k := 0)
    le_rfl zero_lt_one hg0 hf0 (fun t => fun u => t * extB ν u) (norm_nonneg ν) hT hTlin ζ
  have hd := hL.hasDerivAt
  have hev : (fun t : ℂ => normalizedSolution (extB (t • ν)) ζ) =ᶠ[𝓝 (0 : ℂ)]
      fun t : ℂ => normalizedSolution (fun u => (0 : ℂ → ℂ) u + t * extB ν u) ζ := by
    filter_upwards [ball_mem_nhds (0 : ℂ) (show 0 < 1 / (‖ν‖ + 1) by positivity)] with t ht
    have htn : ‖t‖ < 1 / (‖ν‖ + 1) := by simpa using ht
    have hk : ‖t • ν‖ < 1 := by
      rw [norm_smul]
      rw [lt_div_iff₀ (by positivity)] at htn
      nlinarith [norm_nonneg ν, norm_nonneg t]
    have := qcv_ns_congr_ae (norm_nonneg _) hk (extB_isBeltramiCoeff (t • ν)) (qcv_extB_smul_ae t ν)
    simp only [Pi.zero_apply, zero_add]
    rw [this]
  refine (hd.congr_of_eventuallyEq hev).congr_deriv ?_
  rw [hL1 1]
  have hh : IsBeltramiCoeff (fun u => (1 : ℂ) * extB ν u) univ (‖ν‖ * ‖(1 : ℂ)‖) := hT 1
  rw [qcv_var_source le_rfl zero_lt_one hg0 hf0 hh]
  have hdz : ∀ u, dz (id : ℂ → ℂ) u = 1 := by intro u; simp [dz]
  have hmeas : MeasurableSet unitDiscExterior := (isOpen_lt continuous_const continuous_norm).measurableSet
  have hind : ∀ u, (fun u => (1 : ℂ) * extB ν u) u * ahKer ζ (id u) * dz id u ^ 2 =
      Set.indicator unitDiscExterior (fun u => ν u * ahKer ζ u) u := by
    intro u
    by_cases hm : u ∈ unitDiscExterior
    · simp [hdz, extB, Set.indicator_of_mem hm]
    · simp [hdz, extB, Set.indicator_of_notMem hm]
  simp only [id_eq] at hind ⊢
  rw [show (∫ u, (fun u => (1 : ℂ) * extB ν u) u * ahKer ζ u * dz id u ^ 2) =
      ∫ u, Set.indicator unitDiscExterior (fun u => ν u * ahKer ζ u) u from integral_congr_ae
        (Filter.Eventually.of_forall hind), integral_indicator hmeas]

/-! ### The `-6/π` kernel -/

theorem qcv_W_zero (ν : LinfStar) : normalizedSolution (extB ((0 : ℂ) • ν)) = id := by
  have hk : ‖(0 : ℂ) • ν‖ < 1 := by simp
  have hae : extB ((0 : ℂ) • ν) =ᵐ[volume] (0 : ℂ → ℂ) := by
    filter_upwards [qcv_extB_smul_ae 0 ν] with u hu
    simpa using hu
  have := qcv_ns_congr_ae (norm_nonneg _) hk (extB_isBeltramiCoeff ((0 : ℂ) • ν)) hae
  rw [this, bB_l_normalizedSolution_zero]

theorem qcv_schwarzian_fB_variation_origin (ν : LinfStar)
    {z : ℂ} (hz : z ∈ unitDisc) :
    HasDerivAt (fun t : ℂ => schwarzianHol (fB (t • ν)) z)
      (-(6 / π) * ∫ u in unitDiscExterior, ν u / (u - z) ^ 4) 0 := by
  have hz1 : ‖z‖ < 1 := mem_ball_zero_iff.mp hz
  set r₀ : ℝ := 1 / (‖ν‖ + 1) with hr₀
  have hr₀pos : 0 < r₀ := by positivity
  set r : ℝ := r₀ / 2 with hr
  have hrpos : 0 < r := by positivity
  have hnorm : ∀ t ∈ ball (0 : ℂ) r₀, ‖t • ν‖ < 1 := by
    intro t ht
    have htn : ‖t‖ < 1 / (‖ν‖ + 1) := by
      have : ‖t‖ < r₀ := by simpa using ht
      rwa [hr₀] at this
    rw [norm_smul]
    rw [lt_div_iff₀ (by positivity)] at htn
    nlinarith [norm_nonneg ν, norm_nonneg t]
  have hball : ∀ t ∈ ball (0 : ℂ) r₀, t • ν ∈ LinfStarBall := fun t ht => by
    simpa [LinfStarBall] using hnorm t ht
  let W : ℂ → ℂ → ℂ := fun t ζ => normalizedSolution (extB (t • ν)) ζ
  have hWt : ∀ ζ, DifferentiableOn ℂ (fun t => W t ζ) (ball (0 : ℂ) r₀) := by
    intro ζ
    have hc : DifferentiableOn ℂ (fun t : ℂ => t • ν) (ball (0 : ℂ) r₀) :=
      differentiableOn_id.smul_const ν
    exact (qcv_planeB_differentiableOn ζ).comp hc hball
  have hrsub : closedBall (0 : ℂ) r ⊆ ball 0 r₀ := by
    intro t ht
    simp only [mem_closedBall, dist_zero_right, mem_ball] at ht ⊢
    linarith
  obtain ⟨B, hB⟩ : ∃ B : ℝ, ∀ t ∈ closedBall (0 : ℂ) r, ‖W t 2‖ ≤ B :=
    (isCompact_closedBall (0 : ℂ) r).exists_bound_of_continuousOn
      ((hWt 2).continuousOn.mono hrsub)
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0 (mem_closedBall_self hrpos.le))
  set R : ℝ := (1 - ‖z‖) / 2 with hRdef
  have hRpos : 0 < R := by have := sub_pos.2 hz1; positivity
  set ρ : ℝ := (1 + ‖z‖) / 2 with hρdef
  have hρ1 : ρ < 1 := by rw [hρdef]; linarith
  have hballsub : ball z R ⊆ unitDisc := by
    intro p hp
    simp only [mem_ball, dist_eq_norm] at hp
    refine mem_ball_zero_iff.mpr ?_
    have := norm_le_norm_add_norm_sub' p z
    linarith
  have hM : ∀ t ∈ ball (0 : ℂ) r, ∀ ζ ∈ ball z R, ‖W t ζ‖ ≤ 4 * B * (ρ / (1 - ρ) ^ 2) := by
    intro t ht ζ hζ
    have htr₀ : t ∈ ball (0 : ℂ) r₀ := hrsub (ball_subset_closedBall ht)
    have hζ1 : ‖ζ‖ < 1 := mem_ball_zero_iff.mp (hballsub hζ)
    have hζρ : ‖ζ‖ ≤ ρ := by
      simp only [mem_ball, dist_eq_norm] at hζ
      have := norm_le_norm_add_norm_sub' ζ z
      rw [hρdef]; linarith
    refine (qcv_W_koebe (hnorm t htr₀) hζ1).trans ?_
    have hm := qcv_mono_koebe (norm_nonneg ζ) hζρ hρ1
    have hBt := hB t (ball_subset_closedBall ht)
    calc 4 * ‖normalizedSolution (extB (t • ν)) 2‖ * (‖ζ‖ / (1 - ‖ζ‖) ^ 2)
        ≤ 4 * B * (‖ζ‖ / (1 - ‖ζ‖) ^ 2) := by gcongr
      _ ≤ 4 * B * (ρ / (1 - ρ) ^ 2) := by gcongr
  have hζdiff : ∀ t ∈ ball (0 : ℂ) r, DifferentiableOn ℂ (W t) (ball z R) := fun t ht =>
    (qcv_W_props (hnorm t (hrsub (ball_subset_closedBall ht)))).2.1.mono hballsub
  have htdiff : ∀ ζ ∈ ball z R, DifferentiableOn ℂ (fun t => W t ζ) (ball (0 : ℂ) r) := fun ζ _ =>
    (hWt ζ).mono (ball_subset_ball (by linarith))
  -- the variation `V`
  set V : ℂ → ℂ := fun ζ => deriv (fun t => W t ζ) 0 with hV
  have hVeq : V = fun ζ => -(1 / π : ℂ) * ∫ u in unitDiscExterior, ν u * ahKer ζ u := by
    funext ζ
    exact (qcv_W_hasDerivAt ν ζ).deriv
  have hj := fun j => qcv_param_hasDerivAt_iter j (F := W) (c := z) (r := r) (R := R)
    (M := 4 * B * (ρ / (1 - ρ) ^ 2)) hrpos hRpos hζdiff htdiff hM
  have hW0 : W 0 = id := qcv_W_zero ν
  -- values at `t = 0`
  have i1 : iteratedDeriv 1 (W 0) z = 1 := by rw [hW0]; simp
  have i2 : iteratedDeriv 2 (W 0) z = 0 := by rw [hW0]; simp [iteratedDeriv_succ']
  have i3 : iteratedDeriv 3 (W 0) z = 0 := by rw [hW0]; simp [iteratedDeriv_succ']
  have d1 := hj 1
  have d2 := hj 2
  have d3 := hj 3
  have hq1 : HasDerivAt (fun t => iteratedDeriv 3 (W t) z / iteratedDeriv 1 (W t) z)
      (iteratedDeriv 3 V z) 0 := by
    have h := d3.div d1 (by rw [i1]; exact one_ne_zero)
    refine h.congr_deriv ?_
    rw [i1, i3]; ring
  have hq2 : HasDerivAt (fun t => iteratedDeriv 2 (W t) z / iteratedDeriv 1 (W t) z)
      (iteratedDeriv 2 V z) 0 := by
    have h := d2.div d1 (by rw [i1]; exact one_ne_zero)
    refine h.congr_deriv ?_
    rw [i1, i2]; ring
  have hq2' : HasDerivAt (fun t => (iteratedDeriv 2 (W t) z / iteratedDeriv 1 (W t) z) ^ 2) 0 0 := by
    have h := hq2.pow 2
    refine h.congr_deriv ?_
    have : iteratedDeriv 2 (W 0) z / iteratedDeriv 1 (W 0) z = 0 := by rw [i1, i2]; simp
    simp only [this]; simp
  have hS := hq1.sub (hq2'.const_mul (3 / 2 : ℂ))
  have hev : (fun t : ℂ => schwarzianHol (fB (t • ν)) z) =ᶠ[𝓝 (0 : ℂ)]
      fun t => iteratedDeriv 3 (W t) z / iteratedDeriv 1 (W t) z -
        3 / 2 * (iteratedDeriv 2 (W t) z / iteratedDeriv 1 (W t) z) ^ 2 := by
    filter_upwards [ball_mem_nhds (0 : ℂ) hr₀pos] with t ht
    obtain ⟨-, hd, hi, -⟩ := qcv_W_props (hnorm t ht)
    have hder1 : deriv (W t) z ≠ 0 := deriv_ne_zero_of_injOn isOpen_ball hd (hi.mono (subset_univ _)) hz
    have hWa : AnalyticAt ℂ (W t) z := hd.analyticAt (isOpen_ball.mem_nhds hz)
    rw [qcv_schwarzian_fB_eq (hball t ht) hz, qcv_schwarzianHol_iter hWa hder1, iteratedDeriv_one]
  refine (hS.congr_of_eventuallyEq hev).congr_deriv ?_
  rw [hVeq, iteratedDeriv_const_mul_field, qcv_extK_iter3 ν hz1]
  have hI : ∫ u in unitDiscExterior, ν u * kerD3 z u = 6 * ∫ u in unitDiscExterior, ν u / (u - z) ^ 4 := by
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    simp only [kerD3]; ring
  rw [hI]; ring

/-! ### `eq_1_4`: the differential of the Bers map at the origin -/

theorem qcv_eq_1_4 (μ : LinfStar) (z : ℂ) (hz : z ∈ unitDisc) :
    AInf.toFun (fderiv ℂ bersPhi 0 μ) z = -(6 / π) * ∫ ζ in unitDiscExterior, μ ζ / (ζ - z) ^ 4 := by
  have h0 : (0 : LinfStar) ∈ LinfStarBall := by simp [LinfStarBall]
  have hD : HasFDerivAt bersPhi (fderiv ℂ bersPhi 0) 0 :=
    ((qcv_bersPhi_differentiableOn.differentiableAt (isOpen_ball.mem_nhds h0))).hasFDerivAt
  have hline : HasDerivAt (fun t : ℂ => bersPhi (t • μ)) (fderiv ℂ bersPhi 0 μ) 0 := by
    have h1 : HasDerivAt (fun t : ℂ => t • μ) μ 0 := by
      simpa using (hasDerivAt_id (0 : ℂ)).smul_const μ
    have hD' : HasFDerivAt bersPhi (fderiv ℂ bersPhi 0) ((fun t : ℂ => t • μ) 0) := by simpa using hD
    exact hD'.comp_hasDerivAt (0 : ℂ) h1
  set ev : AInf unitDisc →L[ℂ] ℂ :=
    ((1 - ‖z‖ ^ 2) ^ 2 : ℂ)⁻¹ • ((BoundedContinuousFunction.evalCLM ℂ (⟨z, hz⟩ : unitDisc)).comp
      (Submodule.subtypeL _)) with hev
  have hevz : ∀ φ : AInf unitDisc, ev φ = AInf.toFun φ z := by
    intro φ
    simp [hev, AInf.toFun, unweight, dif_pos hz, div_eq_inv_mul]
  have h2 : HasDerivAt (fun t : ℂ => AInf.toFun (bersPhi (t • μ)) z) (AInf.toFun (fderiv ℂ bersPhi 0 μ) z) 0 := by
    have : HasDerivAt (fun t : ℂ => ev (bersPhi (t • μ))) (ev (fderiv ℂ bersPhi 0 μ)) 0 :=
      ev.hasFDerivAt.comp_hasDerivAt (0 : ℂ) hline
    simp only [hevz] at this
    exact this
  have hz1 : z ∈ unitDisc := hz
  have h3 := qcv_schwarzian_fB_variation_origin μ hz
  have hev2 : (fun t : ℂ => schwarzianHol (fB (t • μ)) z) =ᶠ[𝓝 (0 : ℂ)]
      fun t : ℂ => AInf.toFun (bersPhi (t • μ)) z := by
    filter_upwards [ball_mem_nhds (0 : ℂ) (show 0 < 1 / (‖μ‖ + 1) by positivity)] with t ht
    have htn : ‖t‖ < 1 / (‖μ‖ + 1) := by simpa using ht
    have hk : t • μ ∈ LinfStarBall := by
      rw [lt_div_iff₀ (by positivity)] at htn
      simp only [LinfStarBall, mem_ball_zero_iff, norm_smul]
      nlinarith [norm_nonneg μ, norm_nonneg t]
    exact ((bersPhi_spec hk).1 z hz).symm
  exact (h2.unique (h3.congr_of_eventuallyEq hev2.symm))

end QCV
end TakhtajanTeo
