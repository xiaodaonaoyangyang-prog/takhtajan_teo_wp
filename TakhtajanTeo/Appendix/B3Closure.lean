import TakhtajanTeo.Appendix.B2Closure
import TakhtajanTeo.Appendix.AppACor4
import TakhtajanTeo.Ch2.S1_Remark19

/-!
# Remark B.3: the Hilbert closure of `Möb(S¹)\Diff₊(S¹)` is `T₀(1)` (Program G, 下属6)

Host of `remark_B_3` (TT:6046).
- (⊆) `T₀(1)` is a connected component of the Hilbert manifold topology, hence closed. Smooth classes lie in `T₀(1)`
  by Remark 1.9 (C³ diffeomorphisms).
- (⊇) The dilation approximants of `B2Closure` are smooth classes. In `T₀(1)`, Hilbert convergence is `A₂(𝔻)`
  convergence of the Schwarzians (`a4_T01_tendsto_iff`), and the dilations `s²φ(s·)` of `φ ∈ A₂(𝔻)` converge to `φ`
  in `A₂(𝔻)`.
- The second conjunct is `b3d_diffT_subset`.

* H1 `b3h_T01_closed`: `T₀(1)` is closed.
* H2 `b3h_diffT_T01`: `diffT ⊆ T₀(1)`.
* H3 `b3h_dil_A2`: dilations converge in `A₂(𝔻)`.
* H4 `b3h_approx`: every point of `T₀(1)` is a Hilbert limit of smooth classes.
-/

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal ComplexConjugate Classical Real

noncomputable section

namespace TakhtajanTeo

open LiZhongQC Ch2

namespace AppB

/-- H1. `T₀(1)` is closed in the Hilbert manifold topology. -/
theorem b3h_T01_closed : @IsClosed T1 hilbertTopology T01 := by
  exact @isClosed_connectedComponent T1 hilbertTopology _

/-- H2. Smooth classes lie in `T₀(1)`. -/
theorem b3h_diffT_T01 : diffT ⊆ T01 := by
  intro p hp
  obtain ⟨u, hu, hpos, hper, he⟩ := hp
  exact (remark_1_9 p).2 ⟨u, hu.of_le (by first | exact WithTop.coe_le_coe.mpr (le_top : (3 : ℕ∞) ≤ ⊤) | norm_num | decide | simp), hpos, hper, he⟩

/-- The `A₂` integrand as a real `ofReal`. -/
theorem b3h_E_eq (x z : ℂ) :
    (‖x‖₊ : ℝ≥0∞) ^ 2 * ENNReal.ofReal (rho z)⁻¹ = ENNReal.ofReal (‖x‖ ^ 2 * (rho z)⁻¹) := by
  rw [ENNReal.ofReal_mul (sq_nonneg _), d2_nnnorm_sq]

theorem b3h_rho_inv (z : ℂ) : (rho z)⁻¹ = (1 - ‖z‖ ^ 2) ^ 2 / 4 := by
  unfold rho
  rw [inv_div]

/-- Scaling in the plane: `∫ F(r z) = r⁻² ∫ F`. -/
theorem b3h_scale {F : ℂ → ℝ≥0∞} (hF : Measurable F) {r : ℝ} (hr : 0 < r) :
    ∫⁻ z, F ((r : ℂ) * z) = ENNReal.ofReal (r ^ 2)⁻¹ * ∫⁻ z, F z := by
  calc ∫⁻ z, F ((r : ℂ) * z) = ∫⁻ z, F z ∂(Measure.map (fun x : ℂ => r • x) volume) := by
        rw [lintegral_map hF (measurable_const_smul r)]
        simp only [Complex.real_smul]
    _ = ENNReal.ofReal (r ^ 2)⁻¹ * ∫⁻ z, F z := by
        rw [Measure.map_addHaar_smul volume hr.ne', lintegral_smul_measure, Complex.finrank_real_complex,
          smul_eq_mul, abs_of_pos (by positivity)]

/-- Tail bound for the dilation: `∫_{R ≤ |z| < 1} |s² φ(s z)|² ρ⁻¹ ≤ ∫_{sR ≤ |w| < 1} |φ|² ρ⁻¹`. -/
theorem b3h_tail_dil {φ : ℂ → ℂ} (hm : Measurable φ) {s R : ℝ} (hs0 : 0 < s) (hs1 : s ≤ 1) :
    ∫⁻ z in {z : ℂ | R ≤ ‖z‖ ∧ ‖z‖ < 1}, ENNReal.ofReal (‖(s : ℂ) ^ 2 * φ ((s : ℂ) * z)‖ ^ 2 * (rho z)⁻¹) ≤
      ∫⁻ w in {z : ℂ | s * R ≤ ‖z‖ ∧ ‖z‖ < 1}, ENNReal.ofReal (‖φ w‖ ^ 2 * (rho w)⁻¹) := by
  have hA : MeasurableSet {z : ℂ | R ≤ ‖z‖ ∧ ‖z‖ < 1} :=
    (measurableSet_le measurable_const measurable_norm).inter (measurableSet_lt measurable_norm measurable_const)
  have hA' : MeasurableSet {z : ℂ | s * R ≤ ‖z‖ ∧ ‖z‖ < 1} :=
    (measurableSet_le measurable_const measurable_norm).inter (measurableSet_lt measurable_norm measurable_const)
  have hF : Measurable ({z : ℂ | s * R ≤ ‖z‖ ∧ ‖z‖ < 1}.indicator
      fun w => ENNReal.ofReal (‖φ w‖ ^ 2 * (rho w)⁻¹)) := by
    refine Measurable.indicator ?_ hA'
    unfold rho
    fun_prop
  rw [← lintegral_indicator hA, ← lintegral_indicator hA']
  calc ∫⁻ z, {z : ℂ | R ≤ ‖z‖ ∧ ‖z‖ < 1}.indicator
          (fun z => ENNReal.ofReal (‖(s : ℂ) ^ 2 * φ ((s : ℂ) * z)‖ ^ 2 * (rho z)⁻¹)) z
        ≤ ∫⁻ z, ENNReal.ofReal (s ^ 2) * {z : ℂ | s * R ≤ ‖z‖ ∧ ‖z‖ < 1}.indicator
          (fun w => ENNReal.ofReal (‖φ w‖ ^ 2 * (rho w)⁻¹)) ((s : ℂ) * z) := by
        refine lintegral_mono fun z => ?_
        by_cases hz : z ∈ {z : ℂ | R ≤ ‖z‖ ∧ ‖z‖ < 1}
        · have hn : ‖(s : ℂ) * z‖ = s * ‖z‖ := by
            rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hs0.le]
          have hsz : (s : ℂ) * z ∈ {z : ℂ | s * R ≤ ‖z‖ ∧ ‖z‖ < 1} := by
            refine ⟨?_, ?_⟩
            · rw [hn]
              exact mul_le_mul_of_nonneg_left hz.1 hs0.le
            · rw [hn]
              calc s * ‖z‖ ≤ 1 * ‖z‖ := mul_le_mul_of_nonneg_right hs1 (norm_nonneg _)
                _ < 1 := by rw [one_mul]; exact hz.2
          rw [indicator_of_mem hz, indicator_of_mem hsz, ← ENNReal.ofReal_mul (by positivity)]
          apply ENNReal.ofReal_le_ofReal
          rw [b3h_rho_inv, b3h_rho_inv, norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hs0.le, hn]
          have ht1 : ‖z‖ < 1 := hz.2
          have ht0 := norm_nonneg z
          have key : s * (1 - ‖z‖ ^ 2) ≤ 1 - (s * ‖z‖) ^ 2 := by nlinarith [mul_nonneg hs0.le (sq_nonneg ‖z‖)]
          have k0 : 0 ≤ s * (1 - ‖z‖ ^ 2) := mul_nonneg hs0.le (by nlinarith)
          have k2 : (s * (1 - ‖z‖ ^ 2)) ^ 2 ≤ (1 - (s * ‖z‖) ^ 2) ^ 2 := pow_le_pow_left₀ k0 key 2
          have k3 := mul_le_mul_of_nonneg_left k2 (by positivity : (0 : ℝ) ≤ s ^ 2 * ‖φ ((s : ℂ) * z)‖ ^ 2 / 4)
          nlinarith [k3]
        · rw [indicator_of_notMem hz]
          exact bot_le
    _ = ENNReal.ofReal (s ^ 2) * (ENNReal.ofReal (s ^ 2)⁻¹ * ∫⁻ z, {z : ℂ | s * R ≤ ‖z‖ ∧ ‖z‖ < 1}.indicator
          (fun w => ENNReal.ofReal (‖φ w‖ ^ 2 * (rho w)⁻¹)) z) := by
        have h := lintegral_const_mul' (μ := volume) (ENNReal.ofReal (s ^ 2))
          (fun z => {z : ℂ | s * R ≤ ‖z‖ ∧ ‖z‖ < 1}.indicator
            (fun w => ENNReal.ofReal (‖φ w‖ ^ 2 * (rho w)⁻¹)) ((s : ℂ) * z)) ENNReal.ofReal_ne_top
        rw [h, b3h_scale hF hs0]
    _ = ∫⁻ z, {z : ℂ | s * R ≤ ‖z‖ ∧ ‖z‖ < 1}.indicator
          (fun w => ENNReal.ofReal (‖φ w‖ ^ 2 * (rho w)⁻¹)) z := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity), mul_inv_cancel₀ (by positivity), ENNReal.ofReal_one,
          one_mul]

/-- The tail `∫_{R ≤ |z| < 1} |φ|² ρ⁻¹` of a finite integral is small for `R` close to `1`. -/
theorem b3h_tail_small {φ : ℂ → ℂ}
    (hfin : ∫⁻ z in unitDisc, ENNReal.ofReal (‖φ z‖ ^ 2 * (rho z)⁻¹) ≠ ∞) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ R : ℝ, 0 < R ∧ R < 1 ∧
      ∫⁻ z in {z : ℂ | R ≤ ‖z‖ ∧ ‖z‖ < 1}, ENNReal.ofReal (‖φ z‖ ^ 2 * (rho z)⁻¹) < ε := by
  set A : ℕ → Set ℂ := fun k => {z : ℂ | 1 - 1 / ((k : ℝ) + 2) ≤ ‖z‖ ∧ ‖z‖ < 1} with hAdef
  have hAm : ∀ k, MeasurableSet (A k) := fun k =>
    (measurableSet_le measurable_const measurable_norm).inter (measurableSet_lt measurable_norm measurable_const)
  set ν : Measure ℂ := volume.withDensity fun z => ENNReal.ofReal (‖φ z‖ ^ 2 * (rho z)⁻¹) with hν
  have hνA : ∀ k, ν (A k) = ∫⁻ z in A k, ENNReal.ofReal (‖φ z‖ ^ 2 * (rho z)⁻¹) := fun k =>
    withDensity_apply _ (hAm k)
  have hanti : Antitone A := by
    intro k l hkl z hz
    refine ⟨le_trans ?_ hz.1, hz.2⟩
    have hk : (k : ℝ) ≤ l := by exact_mod_cast hkl
    have : 1 / ((l : ℝ) + 2) ≤ 1 / ((k : ℝ) + 2) := one_div_le_one_div_of_le (by positivity) (by linarith)
    linarith
  have hsub : ∀ k, A k ⊆ unitDisc := fun k z hz => mem_ball_zero_iff.mpr hz.2
  have hfin0 : ∃ k, ν (A k) ≠ ∞ := ⟨0, by
    rw [hνA]
    exact ne_top_of_le_ne_top hfin (lintegral_mono_set (hsub 0))⟩
  have hempty : (⋂ k, A k) = ∅ := by
    ext z
    simp only [mem_iInter, mem_empty_iff_false, iff_false]
    intro h
    have h1 : ‖z‖ < 1 := (h 0).2
    obtain ⟨k, hk⟩ := exists_nat_one_div_lt (show 0 < 1 - ‖z‖ by linarith)
    have hk2 := (h k).1
    have : 1 / ((k : ℝ) + 2) < 1 / ((k : ℝ) + 1) := one_div_lt_one_div_of_lt (by positivity) (by linarith)
    linarith
  have ht := tendsto_measure_iInter_atTop (fun k => (hAm k).nullMeasurableSet) hanti hfin0
  rw [hempty, measure_empty] at ht
  obtain ⟨k, hk⟩ := (ht.eventually (gt_mem_nhds hε)).exists
  refine ⟨1 - 1 / ((k : ℝ) + 2), ?_, ?_, ?_⟩
  · have : 1 / ((k : ℝ) + 2) < 1 := (div_lt_one (by positivity)).mpr (by linarith)
    linarith
  · have : 0 < 1 / ((k : ℝ) + 2) := by positivity
    linarith
  · have h := hk
    simp only [Function.comp_apply] at h
    rw [hνA] at h
    exact h

/-- Dominated convergence on a smaller disc. -/
theorem b3h_core {φ : ℂ → ℂ} (hm : Measurable φ) (hc : ContinuousOn φ unitDisc) {R : ℝ} (hR1 : R < 1)
    {s : ℕ → ℝ} (hs0 : ∀ n, 0 ≤ s n) (hs1 : ∀ n, s n ≤ 1) (hlim : Tendsto s atTop (𝓝 1)) :
    Tendsto (fun n => ∫⁻ z in ball (0 : ℂ) R,
      ENNReal.ofReal (‖(s n : ℂ) ^ 2 * φ ((s n : ℂ) * z) - φ z‖ ^ 2 * (rho z)⁻¹)) atTop (𝓝 0) := by
  obtain ⟨C0, hC0'⟩ := (isCompact_closedBall (0 : ℂ) R).exists_bound_of_continuousOn
    (hc.mono (closedBall_subset_ball hR1))
  set C : ℝ := max C0 0 with hCdef
  have hC : ∀ x ∈ closedBall (0 : ℂ) R, ‖φ x‖ ≤ C := fun x hx => (hC0' x hx).trans (le_max_left _ _)
  have h0 : (0 : ℝ≥0∞) = ∫⁻ z in ball (0 : ℂ) R, 0 := by simp
  rw [h0]
  refine tendsto_lintegral_of_dominated_convergence (fun _ => ENNReal.ofReal ((C + C) ^ 2)) (fun n => ?_)
    (fun n => ?_) ?_ ?_
  · unfold rho
    fun_prop
  · filter_upwards [ae_restrict_mem measurableSet_ball] with z hz
    apply ENNReal.ofReal_le_ofReal
    have hz1 : ‖z‖ < R := mem_ball_zero_iff.mp hz
    have hsz : (s n : ℂ) * z ∈ closedBall (0 : ℂ) R := by
      rw [mem_closedBall_zero_iff, norm_mul, Complex.norm_real, Real.norm_of_nonneg (hs0 n)]
      calc s n * ‖z‖ ≤ 1 * ‖z‖ := mul_le_mul_of_nonneg_right (hs1 n) (norm_nonneg _)
        _ ≤ R := by rw [one_mul]; exact hz1.le
    have hb : ‖(s n : ℂ) ^ 2 * φ ((s n : ℂ) * z) - φ z‖ ≤ C + C := by
      refine (norm_sub_le _ _).trans (add_le_add ?_ (hC z (ball_subset_closedBall hz)))
      rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg (hs0 n)]
      calc s n ^ 2 * ‖φ ((s n : ℂ) * z)‖ ≤ 1 * C :=
            mul_le_mul (pow_le_one₀ (hs0 n) (hs1 n)) (hC _ hsz) (norm_nonneg _) zero_le_one
        _ = C := one_mul C
    have hw0 : 0 ≤ (rho z)⁻¹ := by rw [b3h_rho_inv]; positivity
    have hw1 : (rho z)⁻¹ ≤ 1 := by
      rw [b3h_rho_inv]
      have h1 : ‖z‖ < 1 := hz1.trans hR1
      have h2 : 0 ≤ 1 - ‖z‖ ^ 2 := by nlinarith [norm_nonneg z]
      have h3 : 1 - ‖z‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg z]
      have h4 : (1 - ‖z‖ ^ 2) ^ 2 ≤ 1 := by nlinarith
      linarith
    have hsq : ‖(s n : ℂ) ^ 2 * φ ((s n : ℂ) * z) - φ z‖ ^ 2 ≤ (C + C) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hb 2
    calc ‖(s n : ℂ) ^ 2 * φ ((s n : ℂ) * z) - φ z‖ ^ 2 * (rho z)⁻¹ ≤ (C + C) ^ 2 * 1 :=
          mul_le_mul hsq hw1 hw0 (sq_nonneg _)
      _ = (C + C) ^ 2 := mul_one _
  · rw [setLIntegral_const]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top measure_ball_lt_top.ne
  · filter_upwards [ae_restrict_mem measurableSet_ball] with z hz
    have hzD : z ∈ unitDisc := mem_ball_zero_iff.mpr ((mem_ball_zero_iff.mp hz).trans hR1)
    have hcz : ContinuousAt φ z := hc.continuousAt (isOpen_ball.mem_nhds hzD)
    have h1 : Tendsto (fun n => (s n : ℂ)) atTop (𝓝 1) := by
      have h := (Complex.continuous_ofReal.tendsto 1).comp hlim
      rw [Complex.ofReal_one] at h
      exact h
    have h2 : Tendsto (fun n => φ ((s n : ℂ) * z)) atTop (𝓝 (φ z)) :=
      hcz.tendsto.comp (by simpa using h1.mul_const z)
    have h3 := ((((h1.pow 2).mul h2).sub (tendsto_const_nhds (x := φ z))).norm.pow 2).mul_const (rho z)⁻¹
    have h4 := ENNReal.tendsto_ofReal h3
    simpa using h4

/-- H3. The dilations `s²φ(s·)`, `s = n/(n+1)`, of `φ ∈ A₂(𝔻)` converge to `φ` in `A₂(𝔻)`. -/
theorem b3h_dil_A2 {φ : ℂ → ℂ} (hφ : φ ∈ A2fun unitDisc) :
    Tendsto (fun n : ℕ => normA2 unitDisc
      (fun z => ((n : ℝ) / (n + 1) : ℂ) ^ 2 * φ (((n : ℝ) / (n + 1) : ℂ) * z) - φ z)) atTop (𝓝 0) := by
  obtain ⟨hd, hfinA⟩ := hφ
  obtain ⟨ψ, hψ⟩ : ∃ ψ : ℂ → ℂ, ψ = unitDisc.piecewise φ 0 := ⟨_, rfl⟩
  have hψm : Measurable ψ := by
    rw [hψ]
    exact ContinuousOn.measurable_piecewise hd.continuousOn continuousOn_const isOpen_ball.measurableSet
  have hψe : EqOn ψ φ unitDisc := by
    intro z hz
    rw [hψ]
    exact piecewise_eq_of_mem _ _ _ hz
  have hψc : ContinuousOn ψ unitDisc := hd.continuousOn.congr hψe
  -- the scale factors
  set s : ℕ → ℝ := fun n => (n : ℝ) / (n + 1) with hsdef
  have hs0 : ∀ n, 0 ≤ s n := fun n => by positivity
  have hs1 : ∀ n, s n ≤ 1 := fun n => (div_le_one (by positivity)).mpr (by linarith)
  have hlim : Tendsto s atTop (𝓝 1) := tendsto_natCast_div_add_atTop (1 : ℝ)
  have hcast : ∀ n : ℕ, ((n : ℝ) / (n + 1) : ℂ) = ((s n : ℝ) : ℂ) := fun n => by
    simp only [hsdef]
    push_cast
    ring
  have hsD : ∀ n, ∀ z ∈ unitDisc, ((s n : ℝ) : ℂ) * z ∈ unitDisc := fun n z hz => by
    refine mem_ball_zero_iff.mpr ?_
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hs0 n)]
    calc s n * ‖z‖ ≤ 1 * ‖z‖ := mul_le_mul_of_nonneg_right (hs1 n) (norm_nonneg _)
      _ < 1 := by rw [one_mul]; exact mem_ball_zero_iff.mp hz
  -- the A₂ integral of `ψ` is finite
  have hfinψ : ∫⁻ z in unitDisc, ENNReal.ofReal (‖ψ z‖ ^ 2 * (rho z)⁻¹) ≠ ∞ := by
    have h := (ENNReal.rpow_lt_top_iff_of_pos (by norm_num : (0 : ℝ) < 1 / 2)).mp hfinA
    refine (lt_of_eq_of_lt ?_ h).ne
    refine setLIntegral_congr_fun isOpen_ball.measurableSet fun z hz => ?_
    rw [b3h_E_eq, hψe hz]
  -- reduce to the integral of `ψ`
  set I : ℕ → ℝ≥0∞ := fun n => ∫⁻ z in unitDisc,
    ENNReal.ofReal (‖((s n : ℝ) : ℂ) ^ 2 * ψ (((s n : ℝ) : ℂ) * z) - ψ z‖ ^ 2 * (rho z)⁻¹) with hIdef
  have hnorm : ∀ n : ℕ, normA2 unitDisc
      (fun z => ((n : ℝ) / (n + 1) : ℂ) ^ 2 * φ (((n : ℝ) / (n + 1) : ℂ) * z) - φ z) = I n ^ (1 / 2 : ℝ) := by
    intro n
    unfold normA2
    congr 1
    refine setLIntegral_congr_fun isOpen_ball.measurableSet fun z hz => ?_
    simp only [hIdef]
    rw [b3h_E_eq, hcast n, hψe hz, hψe (hsD n z hz)]
  simp_rw [hnorm]
  have hI : Tendsto I atTop (𝓝 0) := by
    rw [ENNReal.tendsto_nhds_zero]
    intro ε hε
    have hε2 : 0 < ε / 2 := ENNReal.half_pos hε.ne'
    have hε8 : 0 < ε / 2 / 4 := ENNReal.div_pos hε2.ne' (by norm_num)
    obtain ⟨R0, hR00, hR01, hT⟩ := b3h_tail_small hfinψ hε8
    set R : ℝ := (1 + R0) / 2 with hRdef
    have hR1 : R < 1 := by rw [hRdef]; linarith
    have hRR0 : R0 < R := by rw [hRdef]; linarith
    have hcore := b3h_core hψm hψc hR1 hs0 hs1 hlim
    have hev1 := (ENNReal.tendsto_nhds_zero.mp hcore) (ε / 2) hε2
    have hev2 : ∀ᶠ n in atTop, R0 ≤ s n * R := by
      have h := hlim.mul_const R
      rw [one_mul] at h
      exact (h.eventually (lt_mem_nhds hRR0)).mono fun n hn => hn.le
    have hev3 : ∀ᶠ n in atTop, 0 < s n := (hlim.eventually (lt_mem_nhds one_pos)).mono fun n hn => by
      linarith
    filter_upwards [hev1, hev2, hev3] with n hn1 hn2 hn3
    -- split `𝔻` into the small disc and the collar
    have hcover : unitDisc ⊆ ball (0 : ℂ) R ∪ {z : ℂ | R ≤ ‖z‖ ∧ ‖z‖ < 1} := by
      intro z hz
      by_cases h : ‖z‖ < R
      · exact Or.inl (mem_ball_zero_iff.mpr h)
      · exact Or.inr ⟨not_lt.mp h, mem_ball_zero_iff.mp hz⟩
    have hA : MeasurableSet {z : ℂ | R ≤ ‖z‖ ∧ ‖z‖ < 1} :=
      (measurableSet_le measurable_const measurable_norm).inter (measurableSet_lt measurable_norm measurable_const)
    have hTmono : ∀ R' : ℝ, R0 ≤ R' →
        ∫⁻ z in {z : ℂ | R' ≤ ‖z‖ ∧ ‖z‖ < 1}, ENNReal.ofReal (‖ψ z‖ ^ 2 * (rho z)⁻¹) ≤ ε / 2 / 4 := by
      intro R' hR'
      refine le_trans (lintegral_mono_set (show {z : ℂ | R' ≤ ‖z‖ ∧ ‖z‖ < 1} ⊆ {z : ℂ | R0 ≤ ‖z‖ ∧ ‖z‖ < 1} from
        fun z hz => ⟨hR'.trans hz.1, hz.2⟩)) hT.le
    have hcollar : ∫⁻ z in {z : ℂ | R ≤ ‖z‖ ∧ ‖z‖ < 1},
        ENNReal.ofReal (‖((s n : ℝ) : ℂ) ^ 2 * ψ (((s n : ℝ) : ℂ) * z) - ψ z‖ ^ 2 * (rho z)⁻¹) ≤ ε / 2 := by
      calc _ ≤ ∫⁻ z in {z : ℂ | R ≤ ‖z‖ ∧ ‖z‖ < 1},
            (2 * ENNReal.ofReal (‖((s n : ℝ) : ℂ) ^ 2 * ψ (((s n : ℝ) : ℂ) * z)‖ ^ 2 * (rho z)⁻¹) +
              2 * ENNReal.ofReal (‖ψ z‖ ^ 2 * (rho z)⁻¹)) := by
            refine lintegral_mono fun z => ?_
            have hw0 : 0 ≤ (rho z)⁻¹ := by rw [b3h_rho_inv]; positivity
            rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by norm_num, ← ENNReal.ofReal_mul (by norm_num),
              ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_add (by positivity) (by positivity)]
            apply ENNReal.ofReal_le_ofReal
            have h1 := norm_sub_le (((s n : ℝ) : ℂ) ^ 2 * ψ (((s n : ℝ) : ℂ) * z)) (ψ z)
            have h2 : ‖((s n : ℝ) : ℂ) ^ 2 * ψ (((s n : ℝ) : ℂ) * z) - ψ z‖ ^ 2 ≤
                2 * ‖((s n : ℝ) : ℂ) ^ 2 * ψ (((s n : ℝ) : ℂ) * z)‖ ^ 2 + 2 * ‖ψ z‖ ^ 2 := by
              nlinarith [norm_nonneg (((s n : ℝ) : ℂ) ^ 2 * ψ (((s n : ℝ) : ℂ) * z) - ψ z),
                sq_nonneg (‖((s n : ℝ) : ℂ) ^ 2 * ψ (((s n : ℝ) : ℂ) * z)‖ - ‖ψ z‖)]
            nlinarith [mul_le_mul_of_nonneg_right h2 hw0]
        _ = 2 * (∫⁻ z in {z : ℂ | R ≤ ‖z‖ ∧ ‖z‖ < 1},
              ENNReal.ofReal (‖((s n : ℝ) : ℂ) ^ 2 * ψ (((s n : ℝ) : ℂ) * z)‖ ^ 2 * (rho z)⁻¹)) +
            2 * (∫⁻ z in {z : ℂ | R ≤ ‖z‖ ∧ ‖z‖ < 1}, ENNReal.ofReal (‖ψ z‖ ^ 2 * (rho z)⁻¹)) := by
            rw [lintegral_add_left (by unfold rho; fun_prop), lintegral_const_mul' _ _ (by norm_num),
              lintegral_const_mul' _ _ (by norm_num)]
        _ ≤ 2 * (ε / 2 / 4) + 2 * (ε / 2 / 4) := by
            gcongr
            · exact (b3h_tail_dil hψm hn3 (hs1 n)).trans (hTmono _ hn2)
            · exact hTmono R hRR0.le
        _ ≤ ε / 2 := by
            rw [← two_mul, ← mul_assoc, show (2 : ℝ≥0∞) * 2 = 4 by norm_num,
              ENNReal.mul_div_cancel (by norm_num) (by norm_num)]
    calc I n ≤ ∫⁻ z in ball (0 : ℂ) R ∪ {z : ℂ | R ≤ ‖z‖ ∧ ‖z‖ < 1},
          ENNReal.ofReal (‖((s n : ℝ) : ℂ) ^ 2 * ψ (((s n : ℝ) : ℂ) * z) - ψ z‖ ^ 2 * (rho z)⁻¹) :=
          lintegral_mono_set hcover
      _ ≤ _ + _ := lintegral_union_le _ _ _
      _ ≤ ε / 2 + ε / 2 := add_le_add hn1 hcollar
      _ = ε := ENNReal.add_halves ε
  have h := (ENNReal.continuous_rpow_const (y := (1 / 2 : ℝ))).tendsto 0 |>.comp hI
  rw [ENNReal.zero_rpow_of_pos (by norm_num)] at h
  exact h

/-- The Schwarzian of the dilation: `𝒮(dilateF f n)(z) = s² 𝒮f(s z)`, `s = n/(n+1)`. -/
theorem b3h_dilate_schwarzian {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f unitDisc) (hi : InjOn f unitDisc) {n : ℕ}
    (hn : 1 ≤ n) {z : ℂ} (hz : z ∈ unitDisc) :
    schwarzianHol (dilateF f n) z =
      ((n : ℝ) / (n + 1) : ℂ) ^ 2 * schwarzianHol f (((n : ℝ) / (n + 1) : ℂ) * z) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hr0 : (0 : ℝ) < (n : ℝ) / (n + 1) := div_pos hn0 (by positivity)
  have hr1 : (n : ℝ) / (n + 1) < 1 := (div_lt_one (by positivity)).mpr (by linarith)
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn0.ne'
  have hs0 : (((n : ℝ) / (n + 1) : ℂ)) ≠ 0 := by
    have h := b2c_smul_eq n 1
    intro h0
    rw [h0, zero_mul, Complex.real_smul, mul_one] at h
    exact hr0.ne' (by exact_mod_cast h.symm)
  have hsz' : (0 + ((n : ℝ) / (n + 1) : ℂ) * z) ∈ unitDisc := by
    rw [zero_add]
    refine mem_ball_zero_iff.mpr ?_
    rw [b2c_norm_smul]
    have hz' : ‖z‖ < 1 := mem_ball_zero_iff.mp hz
    calc ((n : ℝ) / (n + 1)) * ‖z‖ ≤ 1 * ‖z‖ := mul_le_mul_of_nonneg_right hr1.le (norm_nonneg _)
      _ < 1 := by rw [one_mul]; exact hz'
  have hfa : AnalyticAt ℂ f (0 + ((n : ℝ) / (n + 1) : ℂ) * z) := hf.analyticAt (isOpen_ball.mem_nhds hsz')
  have hfd' : deriv f (0 + ((n : ℝ) / (n + 1) : ℂ) * z) ≠ 0 := deriv_ne_zero_of_injOn isOpen_ball hf hi hsz'
  have hdil : dilateF f n = fun t => (f (0 + ((n : ℝ) / (n + 1) : ℂ) * t) - 0) / ((n : ℝ) / (n + 1) : ℂ) := by
    funext t
    unfold dilateF
    rw [zero_add, sub_zero, eq_div_iff hs0]
    push_cast
    field_simp [hnC]
  rw [hdil, cbs_affine_schwarzian hs0 hs0 hfa hfd', zero_add]

/-- H4. Every point of `T₀(1)` is a Hilbert limit of smooth classes. -/
theorem b3h_approx {p : T1} (hp : p ∈ T01) :
    ∃ q : ℕ → T1, (∀ n, q n ∈ diffT) ∧ @Tendsto _ _ q atTop (@nhds _ hilbertTopology p) := by
  have hμ : ((Quotient.out p : LinfStarBall) : LinfStar) ∈ LinfStarBall := (Quotient.out p : LinfStarBall).2
  choose ν hν0 hν using fun n : ℕ => b2c_scaled hμ (Nat.le_add_left 1 n)
  have hq : ∀ n, Phi ⟨ν n, hν0 n⟩ ∈ diffT := fun n => by
    have hr : teichSetoid.r (Phi ⟨ν n, hν0 n⟩).out ⟨ν n, hν0 n⟩ := Quotient.mk_out (s := teichSetoid) _
    obtain ⟨U, hU, hS, hd, hi⟩ := b2c_wA_holo hμ (Nat.le_add_left 1 n) (hν0 n) (hν n)
    obtain ⟨u, hu, hpos, hp2, he⟩ := b2c_circle_diffeo hU hS hd hi (wA_circle_sensePreserving (hν0 n))
    show IsCircleDiffeo (wA ((Quotient.out (Phi ⟨ν n, hν0 n⟩) : LinfStarBall) : LinfStar))
    refine ⟨u, hu, hpos, hp2, fun t => ?_⟩
    have hc : exp (t * I) ∈ unitCircle := by
      show ‖exp (t * I)‖ = 1
      exact Complex.norm_exp_ofReal_mul_I t
    rw [hr (exp (t * I)) hc]
    exact he t
  refine ⟨fun n => Phi ⟨ν n, hν0 n⟩, hq, ?_⟩
  refine (AppA.a4_T01_tendsto_iff (fun n => b3h_diffT_T01 (hq n)) hp).mpr ?_
  obtain ⟨hfd, hfi⟩ := fB_holomorphic_injective hμ
  have hA := (ab112_i p).mp hp
  rw [e13_fsans_eq hμ] at hA
  refine ((b3h_dil_A2 hA).comp (tendsto_add_atTop_nat 1)).congr fun n => ?_
  simp only [Function.comp_apply]
  obtain ⟨hR, hdd, hdi⟩ := dilateF_extension (show IsUnivalentDisc (fB ((Quotient.out p : LinfStarBall) : LinfStar))
    from ⟨hfd, hfi⟩) (Nat.le_add_left 1 n)
  have hsub : unitDisc ⊆ ball (0 : ℂ) (((n + 1 : ℕ) + 1 : ℝ) / (n + 1 : ℕ)) := ball_subset_ball hR.le
  have hout : ((Quotient.out (Phi ⟨ν n, hν0 n⟩) : LinfStarBall) : LinfStar) ∈ LinfStarBall :=
    (Quotient.out (Phi ⟨ν n, hν0 n⟩) : LinfStarBall).2
  unfold normA2
  congr 1
  refine setLIntegral_congr_fun isOpen_ball.measurableSet (fun z hz => ?_)
  have e1 : schwarzianHol (fsans ((Quotient.out (Phi ⟨ν n, hν0 n⟩) : LinfStarBall) : LinfStar)) z =
      (((n + 1 : ℕ) : ℝ) / ((n + 1 : ℕ) + 1) : ℂ) ^ 2 * schwarzianHol (fB ((Quotient.out p : LinfStarBall) : LinfStar))
        ((((n + 1 : ℕ) : ℝ) / ((n + 1 : ℕ) + 1) : ℂ) * z) := by
    rw [e13_fsans_eq hout, ← (bersPhi_spec hout).1 z hz]
    change AInf.toFun (bers (Phi ⟨ν n, hν0 n⟩)) z = _
    rw [bers_Phi, b2c_bers_dilate hμ (Nat.le_add_left 1 n) (hν0 n) (hν n),
      (schwarzianHol_AInf_spec (hdd.mono hsub) (hdi.mono hsub)).1 z hz,
      b3h_dilate_schwarzian hfd hfi (Nat.le_add_left 1 n) hz]
  simp only
  rw [e1, e13_fsans_eq hμ]

/-- **Remark B.3** (TT:6046) (with Theorem A.1 of Part I). The closure of `Möb(S¹)\Diff₊(S¹)` in the Banach manifold
topology is `S`. In the Hilbert manifold topology it is `T₀(1)`. -/
theorem b3h_remark_B_3 : @closure T1 hilbertTopology diffT = T01 ∧ diffT ⊆ symmetricT := by
  let _ : TopologicalSpace T1 := hilbertTopology
  refine ⟨subset_antisymm (closure_minimal b3h_diffT_T01 b3h_T01_closed) fun p hp => ?_, b3d_diffT_subset⟩
  obtain ⟨q, hq, ht⟩ := b3h_approx hp
  exact mem_closure_of_tendsto ht (Eventually.of_forall hq)

/-- **Remark B.3** (TT:6046) (with Theorem A.1 of Part I). The closure of `Möb(S¹)\Diff₊(S¹)` in the Banach manifold
topology is `S`. In the Hilbert manifold topology it is `T₀(1)`. -/
theorem remark_B_3 : @closure T1 hilbertTopology diffT = T01 ∧ diffT ⊆ symmetricT := by
  exact b3h_remark_B_3

end AppB

end TakhtajanTeo
