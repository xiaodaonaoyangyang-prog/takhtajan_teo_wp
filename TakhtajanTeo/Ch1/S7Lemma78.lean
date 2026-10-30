import TakhtajanTeo.Ch1.S7Prop71
import TakhtajanTeo.Ch1.S7SecondVarGeneric
import TakhtajanTeo.Ch1.S7EnergyCompleted
import TakhtajanTeo.Ch1.L613
import TakhtajanTeo.Ch2.S2_Completed5
import TakhtajanTeo.Ch1.S7SecondVariation

/-!
# `lemma_7_8` (`s7l8_`, 下属3, Program G)

Host of `lemma_7_8` (TT:2905–2985); the original statement in `S7_Curvature` is relocated by the leader. Frozen
interface `collaboration/下属3/S7L78/INTERFACE.lean` (md5 9d4cd51c, 7 stubs); all stubs proved here.

Route, in the model `𝕌`, with `K_e(u, z) = kernelKbar (e ν) u z` (so `K_0(u, z) = 1/(u - z̄)²`):
* (A) `Q̈ = (12/π) J̈/ρ - μ G(|ν|²)` from `ρ^{εν} Q = (12/π) J` (`s71_eq_7_1`), `ρ̇ = 0` (`lemma_6_1`),
  `ρ̈ = ρ G(|ν|²)` (`prop_6_3`); `J̈` passes under the integral by `s7g_f2_Jdd`.
* (B1) `∂∂̄[K²] = 2 K₀ M + 2 D₁ D̄₁` with `D₁ = ∂_e K`, `D̄₁ = ∂_ē K`, `M = ∂_e∂_ē K` at `0`.
* (B2) `M` from (1.25) differentiated once more at `0` (two-point core `s7l8_core2`).
* (D1) `I₁ = ρ⁻¹ ∫ μ D₁ D̄₁ ∈ L²(ρ)`: Cauchy–Schwarz, Tonelli, the local identification of the Beurling
  transform `s7l8_hilbertH_local` and its isometry.
* (D23) `I₂ + I₃ = ρ⁻¹ ∫ μ K₀ M ∈ L²(ρ)`: `M(w, z) = \overline{M(z, w)}` and (B2) give the paper-order form
  (`s7l8_R1`); the second-variable form of `D₁` is regularized by the `prop_6_3` partial fractions (`s7l8_R2`,
  the `I₅`/`I₆` split); then `M(w, z) = H g_z(w) - (1/π) ∫ b_z C(·, w)` a.e. (`s7l8_M_ae`), the `H g_z` part
  by the isometry, the `C` part by Fubini (`s7l8_Yswap`) and the off-support pairing (`s7l8_pair_off`).
* (D4) `μ G(|ν|²) ∈ L²(ρ)` (RK3).
* (E) Cayley transport `𝕌 → 𝔻*` (`p71_wm_Q`, `s7g_l3_cov`, `s7g_l3_L2fin`).

`L²` norms: the stubs (D1), (D23), (D4) state the genuine weighted norm in its `lintegral` form
`∫⁻ z in 𝕌, ‖f z‖ₑ² ρ(z) < ∞` (with an `AEMeasurable` conjunct), never a Bochner integral; `lemma_7_8` concludes
`normL2 𝔻* (…) < ∞`, the `lintegral` norm of `S2_HilbertManifold`.
-/

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal ComplexConjugate Classical Real

noncomputable section

namespace TakhtajanTeo

open LiZhongQC

/-- `1/|ζ - v|² ∈ L²` away from `v`. -/
theorem s7l8_kernel_memLp (v : ℂ) {d : ℝ} (hd : 0 < d) :
    MemLp ({ζ : ℂ | d ≤ ‖ζ - v‖}.indicator fun ζ => (((‖ζ - v‖ ^ 2)⁻¹ : ℝ) : ℂ)) 2 volume := by
  have hS : MeasurableSet {ζ : ℂ | d ≤ ‖ζ - v‖} :=
    measurableSet_le measurable_const (measurable_id.sub_const v).norm
  have hmeas : AEStronglyMeasurable ({ζ : ℂ | d ≤ ‖ζ - v‖}.indicator fun ζ => (((‖ζ - v‖ ^ 2)⁻¹ : ℝ) : ℂ))
      volume :=
    ((Complex.continuous_ofReal.measurable.comp
      (((measurable_id.sub_const v).norm.pow_const 2).inv)).indicator hS).aestronglyMeasurable
  rw [memLp_two_iff_integrable_sq_norm hmeas]
  refine ((Ch2.s2c_l4_outside_ball v hd).1.integrable_indicator hS).congr (Eventually.of_forall fun ζ => ?_)
  by_cases hζ : ζ ∈ {ζ : ℂ | d ≤ ‖ζ - v‖}
  · have hpos : 0 < ‖ζ - v‖ := lt_of_lt_of_le hd hζ
    simp only [Set.indicator_of_mem hζ, Complex.norm_real, Real.norm_eq_abs]
    rw [abs_of_nonneg (by positivity)]
    field_simp
  · simp [Set.indicator_of_notMem hζ]

/-- `h/(ζ - v)²` is integrable when `h ∈ L²` vanishes on `ball v d`. -/
theorem s7l8_far_integrable {h : ℂ → ℂ} (hm : AEStronglyMeasurable h volume) (h2 : MemLp h 2 volume) {v : ℂ}
    {d : ℝ} (hd : 0 < d) (hz : ∀ ζ ∈ ball v d, h ζ = 0) :
    Integrable (fun ζ => h ζ / (ζ - v) ^ 2) := by
  have hk := s7l8_kernel_memLp v hd
  have hint := hk.integrable_mul h2
  refine hint.mono (hm.aemeasurable.div ((measurable_id.sub_const v).pow_const 2).aemeasurable).aestronglyMeasurable
    (Eventually.of_forall fun ζ => ?_)
  rw [Pi.mul_apply]
  by_cases hζ : ζ ∈ ball v d
  · simp [hz ζ hζ]
  · have hζ' : ζ ∈ {ζ : ℂ | d ≤ ‖ζ - v‖} := by
      simpa [mem_ball, dist_eq_norm, not_lt] using hζ
    have hpos : 0 < ‖ζ - v‖ := lt_of_lt_of_le hd hζ'
    rw [Set.indicator_of_mem hζ', norm_mul, norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by positivity)]
    field_simp
    rfl

/-- **Local identification of the Hilbert (Beurling) transform.** If `g ∈ L²` is smooth on an open `U` and its
truncated integrals `∫_{|ζ - v| > r} g/(ζ - v)²` converge to `Λ(v)` at every `v ∈ U`, then `H g = -(1/π) Λ`
a.e. on `U`. -/
theorem s7l8_hilbertH_local {g : ℂ → ℂ} (hgm : Measurable g) (hg2 : MemLp g 2 volume) {U : Set ℂ}
    (hU : IsOpen U) (hgs : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g U) {Λ : ℂ → ℂ}
    (hΛ : ∀ v ∈ U, Tendsto (fun r : ℝ => ∫ ζ in {ζ : ℂ | r < ‖ζ - v‖}, g ζ / (ζ - v) ^ 2) (𝓝[>] 0)
      (𝓝 (Λ v))) :
    ∀ᵐ v ∂(volume.restrict U), hilbertH g v = -(1 / π : ℂ) * Λ v := by
  -- the local statement
  have hloc : ∀ x ∈ U, ∃ R : ℝ, 0 < R ∧ ball x R ⊆ U ∧
      ∀ᵐ v ∂(volume.restrict (ball x R)), hilbertH g v = -(1 / π : ℂ) * Λ v := by
    intro x hx
    obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.mp hU x hx
    set R : ℝ := ε / 3 with hRdef
    have hR : 0 < R := by positivity
    let χ : ContDiffBump x := ⟨R, 2 * R, hR, by linarith⟩
    have hχc : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (χ : ℂ → ℝ) := χ.contDiff
    have hχ1 : ∀ ζ ∈ ball x R, χ ζ = 1 := fun ζ hζ => χ.one_of_mem_closedBall (ball_subset_closedBall hζ)
    have hχs : Function.support (χ : ℂ → ℝ) = ball x (2 * R) := χ.support_eq
    set gχ : ℂ → ℂ := fun ζ => ((χ ζ : ℝ) : ℂ) * g ζ with hgχ
    set h : ℂ → ℂ := fun ζ => ((1 - χ ζ : ℝ) : ℂ) * g ζ with hhdef
    have hsplit : g = gχ + h := by
      funext ζ; simp only [hgχ, hhdef, Pi.add_apply]; push_cast; ring
    have hcl : closedBall x (2 * R) ⊆ U := (closedBall_subset_ball (by linarith)).trans hεU
    -- `gχ` is smooth with compact support
    have hgχs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) gχ := by
      rw [contDiff_iff_contDiffAt]
      intro y
      by_cases hy : y ∈ U
      · exact ((Complex.ofRealCLM.contDiff.comp hχc).contDiffAt).mul (hgs.contDiffAt (hU.mem_nhds hy))
      · have hyc : y ∉ closedBall x (2 * R) := fun h => hy (hcl h)
        have hev : gχ =ᶠ[𝓝 y] fun _ => (0 : ℂ) := by
          filter_upwards [isClosed_closedBall.isOpen_compl.mem_nhds hyc] with ζ hζ
          have : χ ζ = 0 := by
            by_contra h0
            have hm : ζ ∈ Function.support (χ : ℂ → ℝ) := h0
            rw [hχs] at hm
            exact hζ (ball_subset_closedBall hm)
          simp [hgχ, this]
        exact contDiffAt_const.congr_of_eventuallyEq hev
    have hgχc : HasCompactSupport gχ := by
      refine HasCompactSupport.intro (isCompact_closedBall x (2 * R)) fun ζ hζ => ?_
      have : χ ζ = 0 := by
        by_contra h0
        have hm : ζ ∈ Function.support (χ : ℂ → ℝ) := h0
        rw [hχs] at hm
        exact hζ (ball_subset_closedBall hm)
      simp [hgχ, this]
    have hgχ2 : MemLp gχ 2 volume := hgχs.continuous.memLp_of_hasCompactSupport hgχc
    -- `h` is `L²` and vanishes on `ball x R`
    have hhm : Measurable h :=
      (Complex.continuous_ofReal.measurable.comp (measurable_const.sub hχc.continuous.measurable)).mul hgm
    have hh2 : MemLp h 2 volume := by
      refine hg2.of_le hhm.aestronglyMeasurable (Eventually.of_forall fun ζ => ?_)
      simp only [hhdef, norm_mul, Complex.norm_real, Real.norm_eq_abs]
      have h0 := χ.nonneg (x := ζ)
      have h1 := χ.le_one (x := ζ)
      rw [abs_of_nonneg (by linarith)]
      nlinarith [norm_nonneg (g ζ)]
    have hh0 : ∀ ζ ∈ ball x R, h ζ = 0 := fun ζ hζ => by simp [hhdef, hχ1 ζ hζ]
    -- the off-support formula for `h`, by truncation
    have hhoff : ∀ᵐ v ∂(volume.restrict (ball x R)), hilbertH h v = ∫ ζ, -(1 / π : ℂ) * h ζ / (ζ - v) ^ 2 := by
      set hn : ℕ → ℂ → ℂ := fun n => (closedBall (0 : ℂ) (n : ℝ)).indicator h with hndef
      have hnm : ∀ n, Measurable (hn n) := fun n => hhm.indicator measurableSet_closedBall
      have hn2 : ∀ n, MemLp (hn n) 2 volume := fun n => hh2.indicator measurableSet_closedBall
      have hnc : ∀ n, HasCompactSupport (hn n) := fun n =>
        HasCompactSupport.intro (isCompact_closedBall 0 (n : ℝ)) fun ζ hζ => Set.indicator_of_notMem hζ _
      have hnsupp : ∀ n, ball x R ⊆ (tsupport (hn n))ᶜ := by
        intro n ζ hζ hmem
        have hsub : tsupport (hn n) ⊆ (ball x R)ᶜ := by
          refine closure_minimal (fun y hy => ?_) isOpen_ball.isClosed_compl
          intro hyb
          apply hy
          simp [hndef, Set.indicator_apply, hh0 y hyb]
        exact hsub hmem hζ
      have hoff : ∀ n, ∀ᵐ v ∂(volume.restrict (ball x R)),
          hilbertH (hn n) v = ∫ ζ, -(1 / π : ℂ) * hn n ζ / (ζ - v) ^ 2 := fun n =>
        ae_restrict_of_ae_restrict_of_subset (hnsupp n)
          (hilbertH_eq_integral_ae_off_support (hnm n) (hn2 n) (hnc n))
      -- `H hn → H h` in `L²`, hence a.e. along a subsequence
      have hL2 : Tendsto (fun n => eLpNorm (hilbertH (hn n) - hilbertH h) 2 volume) atTop (𝓝 0) := by
        have he : ∀ n, eLpNorm (hilbertH (hn n) - hilbertH h) 2 volume =
            eLpNorm ((closedBall (0 : ℂ) (n : ℝ))ᶜ.indicator h) 2 volume := by
          intro n
          rw [hilbertH_eLpNorm_sub_eq (hn2 n) hh2, ← eLpNorm_neg]
          congr 1
          funext ζ
          by_cases hζ : ζ ∈ closedBall (0 : ℂ) (n : ℝ)
          · simp [hndef, hζ]
          · simp [hndef, hζ]
        simp_rw [he]
        have h2' : MemLp h (ENNReal.ofReal 2) volume := by simpa using hh2
        simpa using eLpNorm_indicator_compl_closedBall_tendsto_zero (by norm_num : (0 : ℝ) < 2) h2'
      obtain ⟨ns, hnsm, hns⟩ := (tendstoInMeasure_of_tendsto_eLpNorm (by norm_num) hL2).exists_seq_tendsto_ae
      have hns' : ∀ᵐ v ∂(volume.restrict (ball x R)), Tendsto (fun i => hilbertH (hn (ns i)) v) atTop
          (𝓝 (hilbertH h v)) := ae_restrict_of_ae hns
      filter_upwards [hns', ae_all_iff.2 hoff, ae_restrict_mem measurableSet_ball] with v hv hvo hvb
      -- the integrals converge by dominated convergence
      have hd : 0 < R - dist v x := sub_pos.2 (mem_ball.1 hvb)
      have hzero : ∀ ζ ∈ ball v (R - dist v x), h ζ = 0 := fun ζ hζ => hh0 ζ (by
        rw [mem_ball] at hζ ⊢
        linarith [dist_triangle ζ v x])
      have hint := s7l8_far_integrable hhm.aestronglyMeasurable hh2 hd hzero
      have hlim : Tendsto (fun i => ∫ ζ, -(1 / π : ℂ) * hn (ns i) ζ / (ζ - v) ^ 2) atTop
          (𝓝 (∫ ζ, -(1 / π : ℂ) * h ζ / (ζ - v) ^ 2)) := by
        refine tendsto_integral_of_dominated_convergence (fun ζ => ‖(1 / π : ℂ)‖ * ‖h ζ / (ζ - v) ^ 2‖)
          (fun i => ((((hnm (ns i)).const_mul _).div (by fun_prop))).aestronglyMeasurable)
          (hint.norm.const_mul _) (fun i => Eventually.of_forall fun ζ => ?_) (Eventually.of_forall fun ζ => ?_)
        · by_cases hζ : ζ ∈ closedBall (0 : ℂ) ((ns i : ℕ) : ℝ)
          · simp [hndef, hζ, mul_div_assoc]
          · simp only [hndef, Set.indicator_of_notMem hζ, mul_zero, zero_div, norm_zero]
            positivity
        · have hev : ∀ᶠ i in atTop, hn (ns i) ζ = h ζ := by
            obtain ⟨N, hN⟩ := exists_nat_ge ‖ζ‖
            filter_upwards [(StrictMono.tendsto_atTop hnsm).eventually_ge_atTop N] with i hi
            have : ζ ∈ closedBall (0 : ℂ) ((ns i : ℕ) : ℝ) := by
              rw [mem_closedBall_zero_iff]
              exact hN.trans (by exact_mod_cast hi)
            simp [hndef, this]
          refine tendsto_const_nhds.congr' ?_
          filter_upwards [hev] with i hi
          rw [hi]
      exact tendsto_nhds_unique (hv.congr fun i => hvo (ns i)) hlim
    -- assemble on `ball x (R/2)`... here on `ball x R`
    refine ⟨R, hR, (ball_subset_ball (by linarith)).trans hεU, ?_⟩
    have hadd : hilbertH g =ᵐ[volume] hilbertH gχ + hilbertH h := by
      rw [hsplit]; exact hilbertH_add_ae hgχ2 hh2
    filter_upwards [ae_restrict_of_ae hadd, ae_restrict_of_ae (hilbertH_eq_ae_smooth hgχs hgχc), hhoff,
      ae_restrict_mem measurableSet_ball] with v h1 h2 h3 hvb
    have hvU : v ∈ U := hεU ((ball_subset_ball (by linarith)) hvb)
    have hd : 0 < R - dist v x := sub_pos.2 (mem_ball.1 hvb)
    have hzero : ∀ ζ ∈ ball v (R - dist v x), h ζ = 0 := fun ζ hζ => hh0 ζ (by
      rw [mem_ball] at hζ ⊢
      linarith [dist_triangle ζ v x])
    have hint := s7l8_far_integrable hhm.aestronglyMeasurable hh2 hd hzero
    -- the truncated integrals of `gχ`
    have hgχlim : Tendsto (fun r : ℝ => -(1 / π : ℂ) * ∫ ζ in {ζ : ℂ | r < ‖ζ - v‖}, gχ ζ / (ζ - v) ^ 2)
        (𝓝[>] 0) (𝓝 (-(1 / π : ℂ) * (Λ v - ∫ ζ, h ζ / (ζ - v) ^ 2))) := by
      refine ((hΛ v hvU).sub tendsto_const_nhds).const_mul _ |>.congr' ?_
      filter_upwards [Ioo_mem_nhdsGT hd] with r hr
      have hS : MeasurableSet {ζ : ℂ | r < ‖ζ - v‖} :=
        measurableSet_lt measurable_const (measurable_id.sub_const v).norm
      have hgχi : IntegrableOn (fun ζ => gχ ζ / (ζ - v) ^ 2) {ζ : ℂ | r < ‖ζ - v‖} := by
        have hgi : Integrable gχ := hgχs.continuous.integrable_of_hasCompactSupport hgχc
        refine Integrable.mono' ((hgi.norm.mul_const ((r ^ 2)⁻¹)).integrableOn)
          ((hgχs.continuous.measurable.div (by fun_prop)).aestronglyMeasurable)
          ((ae_restrict_mem hS).mono fun ζ hζ => ?_)
        have hpos : r < ‖ζ - v‖ := hζ
        have hr0 : 0 < r := hr.1
        rw [norm_div, norm_pow, div_eq_mul_inv]
        gcongr
      have hhS : ∫ ζ in {ζ : ℂ | r < ‖ζ - v‖}, h ζ / (ζ - v) ^ 2 = ∫ ζ, h ζ / (ζ - v) ^ 2 := by
        refine setIntegral_eq_integral_of_forall_compl_eq_zero fun ζ hζ => ?_
        have hb : ζ ∈ ball v (R - dist v x) := by
          rw [mem_ball, dist_eq_norm]
          simp only [Set.mem_ofPred_eq, not_lt] at hζ
          linarith [hr.2]
        simp [hzero ζ hb]
      have hsum : ∫ ζ in {ζ : ℂ | r < ‖ζ - v‖}, g ζ / (ζ - v) ^ 2 =
          (∫ ζ in {ζ : ℂ | r < ‖ζ - v‖}, gχ ζ / (ζ - v) ^ 2) + ∫ ζ in {ζ : ℂ | r < ‖ζ - v‖}, h ζ / (ζ - v) ^ 2 := by
        rw [← integral_add hgχi hint.integrableOn]
        refine setIntegral_congr_fun hS fun ζ _ => ?_
        rw [hsplit]
        simp only [Pi.add_apply]
        ring
      rw [hsum, hhS]
      ring
    have hsm : hilbertHSmooth gχ v = -(1 / π : ℂ) * (Λ v - ∫ ζ, h ζ / (ζ - v) ^ 2) := by
      unfold hilbertHSmooth
      exact hgχlim.limUnder_eq
    rw [h1, Pi.add_apply, h2, hsm, h3]
    have : ∫ ζ, -(1 / π : ℂ) * h ζ / (ζ - v) ^ 2 = -(1 / π : ℂ) * ∫ ζ, h ζ / (ζ - v) ^ 2 := by
      rw [← integral_const_mul]
      congr 1
      funext ζ
      ring
    rw [this]
    ring
  -- countable cover
  choose! R hR hRU hRae using hloc
  obtain ⟨T, hTc, hTU⟩ := TopologicalSpace.isOpen_iUnion_countable (fun x : U => ball (x : ℂ) (R x))
    fun x => isOpen_ball
  have hcover : U = ⋃ x ∈ T, ball (x : ℂ) (R x) := by
    rw [hTU]
    ext y
    simp only [mem_iUnion]
    constructor
    · intro hy
      exact ⟨⟨y, hy⟩, mem_ball_self (hR y hy)⟩
    · rintro ⟨x, hx⟩
      exact hRU x x.2 hx
  rw [hcover, ae_restrict_biUnion_iff _ hTc]
  intro x _
  exact hRae x x.2

theorem s7l8_phi_cont {μ : ℂ → ℂ} {k : ℝ} (hk : 0 ≤ k) (hμk : IsBeltramiCoeff μ upperHalf k)
    (hμs : ContDiffOn ℝ (⊤ : ℕ∞) μ upperHalf) {z : ℂ} (hz : z ∈ upperHalf) {ξ : ℂ} (hξ : ξ ∈ upperHalf) {R : ℝ} (hRk : R * k < 1)
    {W : ℂ × ℂ → ℂ → ℂ} (hW : W = fun P => normalizedSolution fun u =>
      P.1 * (if 0 < u.im then μ u else 0) + P.2 * (if u.im < 0 then conj (μ (conj u)) else 0))
    {Φ : ℂ × ℂ → ℂ → ℂ} (hΦ : Φ = fun P v => conj (μ v) *
      (dz (W P) ξ * dz (W P) (conj v) / (W P ξ - W P (conj v)) ^ 2) *
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
  obtain ⟨hWz, hDz⟩ := hcomp (fun _ => ξ) continuous_const fun _ _ => ((show 0 < ξ.im from hξ).ne' : ξ.im ≠ 0)
  obtain ⟨hWv, hDv⟩ := hcomp (fun p => conj p.2) (Complex.continuous_conj.comp continuous_snd) fun p hp => by
    rw [Complex.conj_im]; linarith [hvim p hp, show 0 < ξ.im from hξ]
  obtain ⟨hWzb, hDzb⟩ := hcomp (fun _ => conj z) continuous_const fun _ _ => by
    rw [Complex.conj_im]; linarith
  have hμc : ContinuousOn (fun p : (ℂ × ℂ) × ℂ => conj (μ p.2)) T :=
    Complex.continuous_conj.comp_continuousOn (hμs.continuousOn.comp continuous_snd.continuousOn
      fun p hp => (hmem p hp).2.1)
  have hne1 : ∀ p ∈ T, (W p.1 ξ - W p.1 (conj p.2)) ^ 2 ≠ 0 := by
    intro p hp
    refine pow_ne_zero 2 (sub_ne_zero.mpr fun h => ?_)
    have := hinj p.1 (hsub (hmem p hp).1) h
    have h2 : ξ.im = (conj p.2).im := by rw [this]
    rw [Complex.conj_im] at h2
    linarith [hvim p hp, show 0 < ξ.im from hξ]
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
theorem s7l8_phi_holo {μ : ℂ → ℂ} {k : ℝ} (hk : 0 ≤ k) (hμk : IsBeltramiCoeff μ upperHalf k)
    (hμs : ContDiffOn ℝ (⊤ : ℕ∞) μ upperHalf) {z : ℂ} (hz : z ∈ upperHalf) {ξ : ℂ} (hξ : ξ ∈ upperHalf) {R : ℝ} (hRk : R * k < 1)
    {W : ℂ × ℂ → ℂ → ℂ} (hW : W = fun P => normalizedSolution fun u =>
      P.1 * (if 0 < u.im then μ u else 0) + P.2 * (if u.im < 0 then conj (μ (conj u)) else 0))
    {Φ : ℂ × ℂ → ℂ → ℂ} (hΦ : Φ = fun P v => conj (μ v) *
      (dz (W P) ξ * dz (W P) (conj v) / (W P ξ - W P (conj v)) ^ 2) *
      (dz (W P) (conj v) * dz (W P) (conj z) / (W P (conj v) - W P (conj z)) ^ 2))
    {v : ℂ} (hv : v ∈ upperHalf) (hvz : v ≠ z) :
    (∀ b ∈ closedBall (0 : ℂ) R, DifferentiableOn ℂ (fun a => Φ (a, b) v) (ball (0 : ℂ) R)) ∧
      ∀ a ∈ closedBall (0 : ℂ) R, DifferentiableOn ℂ (fun b => Φ (a, b) v) (ball (0 : ℂ) R) := by
  obtain ⟨-, hinj, hhol⟩ := e64_W_basic hk hμk hμs hW
  have hsub := e64_polydisc_sub hk hRk
  have hzim : 0 < z.im := hz
  have hvim : 0 < v.im := hv
  have hy1 : ξ.im ≠ 0 := (show 0 < ξ.im from hξ).ne'
  have hy2 : (conj v).im ≠ 0 := by rw [Complex.conj_im]; linarith
  have hy3 : (conj z).im ≠ 0 := by rw [Complex.conj_im]; linarith
  have hne1 : ∀ P ∈ {P : ℂ × ℂ | max ‖P.1‖ ‖P.2‖ * k < 1}, (W P ξ - W P (conj v)) ^ 2 ≠ 0 := by
    intro P hP
    refine pow_ne_zero 2 (sub_ne_zero.mpr fun h => ?_)
    have := hinj P hP h
    have h2 : ξ.im = (conj v).im := by rw [this]
    rw [Complex.conj_im] at h2
    linarith [show 0 < ξ.im from hξ]
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
    exact (differentiableAt_const _ |>.mul (((hDy ξ hy1).mul (hDy _ hy2)).div
      (((hWy ξ).sub (hWy (conj v))).pow 2) (hne1 _ hct))).mul
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
theorem s7l8_phi_diag {μ : ℂ → ℂ} {k : ℝ} (hk : 0 ≤ k) (hμk : IsBeltramiCoeff μ upperHalf k)
    (hμs : ContDiffOn ℝ (⊤ : ℕ∞) μ upperHalf) {z : ℂ} (hz : z ∈ upperHalf) {ξ : ℂ} (hξ : ξ ∈ upperHalf)
    {W : ℂ × ℂ → ℂ → ℂ} (hW : W = fun P => normalizedSolution fun u =>
      P.1 * (if 0 < u.im then μ u else 0) + P.2 * (if u.im < 0 then conj (μ (conj u)) else 0))
    {Φ : ℂ × ℂ → ℂ → ℂ} (hΦ : Φ = fun P v => conj (μ v) *
      (dz (W P) ξ * dz (W P) (conj v) / (W P ξ - W P (conj v)) ^ 2) *
      (dz (W P) (conj v) * dz (W P) (conj z) / (W P (conj v) - W P (conj z)) ^ 2))
    {ε : ℂ} (hε : ‖ε‖ * k < 1) {v : ℂ} (hv : v ∈ upperHalf) :
    Φ (ε, conj ε) v = conj (μ v) * kernelKbar (fun y => ε * μ y) ξ v * kernelKbarbar (fun y => ε * μ y) v z := by
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
theorem s7l8_tail_bound {μ : ℂ → ℂ} {k : ℝ} (hk : 0 ≤ k) (hμk : IsBeltramiCoeff μ upperHalf k)
    (hμs : ContDiffOn ℝ (⊤ : ℕ∞) μ upperHalf) {z : ℂ} (hz : z ∈ upperHalf) {ξ : ℂ} (hξ : ξ ∈ upperHalf) {R : ℝ} (hRk : R * k < 1)
    {W : ℂ × ℂ → ℂ → ℂ} (hW : W = fun P => normalizedSolution fun u =>
      P.1 * (if 0 < u.im then μ u else 0) + P.2 * (if u.im < 0 then conj (μ (conj u)) else 0))
    {Φ : ℂ × ℂ → ℂ → ℂ} (hΦ : Φ = fun P v => conj (μ v) *
      (dz (W P) ξ * dz (W P) (conj v) / (W P ξ - W P (conj v)) ^ 2) *
      (dz (W P) (conj v) * dz (W P) (conj z) / (W P (conj v) - W P (conj z)) ^ 2))
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ M : ℝ, ∀ q ∈ closedBall (0 : ℂ) R ×ˢ closedBall (0 : ℂ) R,
      IntegrableOn (Φ q) (upperHalf \ ball z δ) ∧ ∫ v in upperHalf \ ball z δ, ‖Φ q v‖ ≤ M := by
  obtain ⟨hC, hinj, -⟩ := e64_W_basic hk hμk hμs hW
  obtain ⟨-, hDc⟩ := e64_dzW_cont hk hμk hμs hW
  obtain ⟨hm₁, -, -, -, -⟩ := wr_U_coeffs hk hμk hμs
  obtain ⟨hs₁, -⟩ := e64_m_smooth hμs
  have hcΦ := s7l8_phi_cont hk hμk hμs hz hξ hRk hW hΦ
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
  obtain ⟨A, hA0, hA⟩ := hbd ξ (show 0 < ξ.im from hξ).ne'
  obtain ⟨B, hB0, hB⟩ := hbd (conj z) (by rw [Complex.conj_im]; linarith)
  -- uniform separation
  obtain ⟨η₁, hη₁, hsep₁⟩ := e64_t5_sep hk hμk hμs hRk hW (conj z) hδ
  obtain ⟨η₂, hη₂, hsep₂⟩ := e64_t5_sep hk hμk hμs hRk hW ξ hξ
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
  set G2 : ℂ → ℝ := fun ζ => Cη * (((1 + ‖ζ - f ξ‖) ^ 4)⁻¹ + ((1 + ‖ζ - f (conj z)‖) ^ 4)⁻¹) with hG2
  have hG2i : Integrable G2 := ((e64_t5_maj (f ξ)).1.add (e64_t5_maj (f (conj z))).1).const_mul Cη
  have hG2v : ∫ ζ, G2 ζ = Cη * (I0 + I0) := by
    rw [hG2, integral_const_mul, integral_add (e64_t5_maj (f ξ)).1 (e64_t5_maj (f (conj z))).1,
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
    have hX1 : η ≤ ‖f (conj v) - f ξ‖ := by
      refine (min_le_right _ _).trans (hsep₂ q hq (conj v) ?_)
      have h1 := Complex.abs_im_le_norm (conj v - ξ)
      have h2 : (conj v - ξ).im = -v.im - ξ.im := by simp
      rw [h2, abs_of_neg (by linarith [show 0 < ξ.im from hξ])] at h1
      linarith
    have hX1p : 0 < ‖f (conj v) - f ξ‖ := hη.trans_le hX1
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
    rw [norm_sub_rev (f ξ) (f (conj v))]
    set X1 := ‖f (conj v) - f ξ‖
    set X2 := ‖f (conj v) - f (conj z)‖
    set Dd := ‖dz f (conj v)‖
    have hma : ‖μ v‖ * ‖dz f ξ‖ * ‖dz f (conj z)‖ ≤ k * A * B :=
      mul_le_mul (mul_le_mul (hμb v hv.1) (hA q hq) (norm_nonneg _) hk) (hB q hq) (norm_nonneg _)
        (mul_nonneg hk hA0)
    have e : ‖μ v‖ * (‖dz f ξ‖ * Dd / X1 ^ 2) * (Dd * ‖dz f (conj z)‖ / X2 ^ 2) =
        (‖μ v‖ * ‖dz f ξ‖ * ‖dz f (conj z)‖) * Dd ^ 2 * (1 / (X1 ^ 2 * X2 ^ 2)) := by
      field_simp
    rw [e]
    calc (‖μ v‖ * ‖dz f ξ‖ * ‖dz f (conj z)‖) * Dd ^ 2 * (1 / (X1 ^ 2 * X2 ^ 2))
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
theorem s7l8_dominate {μ : ℂ → ℂ} {k : ℝ} (hk : 0 ≤ k) (hμk : IsBeltramiCoeff μ upperHalf k)
    (hμs : ContDiffOn ℝ (⊤ : ℕ∞) μ upperHalf) {z : ℂ} (hz : z ∈ upperHalf) {ξ : ℂ} (hξ : ξ ∈ upperHalf) {r R : ℝ} (hr : 0 < r) (hrR : r < R)
    (hRk : R * k < 1)
    {W : ℂ × ℂ → ℂ → ℂ} (hW : W = fun P => normalizedSolution fun u =>
      P.1 * (if 0 < u.im then μ u else 0) + P.2 * (if u.im < 0 then conj (μ (conj u)) else 0))
    {Φ : ℂ × ℂ → ℂ → ℂ} (hΦ : Φ = fun P v => conj (μ v) *
      (dz (W P) ξ * dz (W P) (conj v) / (W P ξ - W P (conj v)) ^ 2) *
      (dz (W P) (conj v) * dz (W P) (conj z) / (W P (conj v) - W P (conj z)) ^ 2))
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ g : ℂ → ℝ, IntegrableOn g (upperHalf \ ball z δ) ∧
      ∀ P ∈ closedBall (0 : ℂ) r ×ˢ closedBall (0 : ℂ) r, ∀ v ∈ upperHalf \ ball z δ, ‖Φ P v‖ ≤ g v := by
  have hR : 0 < R := hr.trans hrR
  obtain ⟨M, hM⟩ := s7l8_tail_bound hk hμk hμs hz hξ hRk hW hΦ hδ
  have hcΦ := s7l8_phi_cont hk hμk hμs hz hξ hRk hW hΦ
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
  obtain ⟨h1, h2⟩ := s7l8_phi_holo hk hμk hμs hz hξ hRk hW hΦ hv1 (fun e => hvz (mem_singleton_iff.mpr e))
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

theorem s7l8_local_unif {μ : ℂ → ℂ} {k : ℝ} (hk : 0 ≤ k) (hμk : IsBeltramiCoeff μ upperHalf k)
    (hμs : ContDiffOn ℝ (⊤ : ℕ∞) μ upperHalf) {z : ℂ} (hz : z ∈ upperHalf) {ξ : ℂ} (hξ : ξ ∈ upperHalf) {r : ℝ} (hrk : r * k < 1)
    {W : ℂ × ℂ → ℂ → ℂ} (hW : W = fun P => normalizedSolution fun u =>
      P.1 * (if 0 < u.im then μ u else 0) + P.2 * (if u.im < 0 then conj (μ (conj u)) else 0))
    {Φ : ℂ × ℂ → ℂ → ℂ} (hΦ : Φ = fun P v => conj (μ v) *
      (dz (W P) ξ * dz (W P) (conj v) / (W P ξ - W P (conj v)) ^ 2) *
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
  have hξΩ : ξ ∈ Ω := (show (0 : ℝ) < ξ.im from hξ).ne'
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
      (Gd (p.1, ξ) * Gd (p.1, conj p.2) / (F (p.1, ξ) - F (p.1, conj p.2)) ^ 2) * Gd (p.1, conj p.2) *
        Gd (p.1, conj z) := ⟨_, rfl⟩
  have hVo : IsOpen (Wset ×ˢ upperHalf) := hWo.prod hUo
  have hm1 : MapsTo (fun p : (ℂ × ℂ) × ℂ => (p.1, ξ)) (Wset ×ˢ upperHalf) (Wset ×ˢ Ω) :=
    fun p hp => ⟨hp.1, hξΩ⟩
  have hm2 : MapsTo (fun p : (ℂ × ℂ) × ℂ => (p.1, conj p.2)) (Wset ×ˢ upperHalf) (Wset ×ˢ Ω) :=
    fun p hp => ⟨hp.1, hcvΩ p.2 hp.2⟩
  have hm3 : MapsTo (fun p : (ℂ × ℂ) × ℂ => (p.1, conj z)) (Wset ×ˢ upperHalf) (Wset ×ˢ Ω) :=
    fun p hp => ⟨hp.1, hczΩ⟩
  have hφ1 : ContDiff ℝ 1 (fun p : (ℂ × ℂ) × ℂ => (p.1, ξ)) := contDiff_fst.prodMk contDiff_const
  have hφ2 : ContDiff ℝ 1 (fun p : (ℂ × ℂ) × ℂ => (p.1, conj p.2)) := contDiff_fst.prodMk (hc.comp contDiff_snd)
  have hφ3 : ContDiff ℝ 1 (fun p : (ℂ × ℂ) × ℂ => (p.1, conj z)) := contDiff_fst.prodMk contDiff_const
  have hGd1 : ContDiffOn ℝ 1 Gd (Wset ×ˢ Ω) := hGd2.of_le (by norm_num)
  have hF1 : ContDiffOn ℝ 1 F (Wset ×ˢ Ω) := hF3.of_le (by norm_num)
  have hne : ∀ p ∈ Wset ×ˢ upperHalf, F (p.1, ξ) - F (p.1, conj p.2) ≠ 0 := by
    intro p hp heq
    rw [← hWF, ← hWF, sub_eq_zero] at heq
    have := congrArg Complex.im (hinj p.1 hp.1 heq)
    rw [Complex.conj_im] at this
    have h2 : (0 : ℝ) < p.2.im := hp.2
    linarith [show (0 : ℝ) < ξ.im from hξ]
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
    rw [hdz q ξ ⟨hq, hξΩ⟩, hdz q (conj v) ⟨hq, hcvΩ v hv⟩, hdz q (conj z) ⟨hq, hczΩ⟩, hWF q ξ, hWF q (conj v),
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
theorem s7l8_param_pv {μ : ℂ → ℂ} {k : ℝ} (hk : 0 ≤ k) (hμk : IsBeltramiCoeff μ upperHalf k)
    (hμs : ContDiffOn ℝ (⊤ : ℕ∞) μ upperHalf) {z : ℂ} (hz : z ∈ upperHalf) {ξ : ℂ} (hξ : ξ ∈ upperHalf) {r : ℝ} (hrk : r * k < 1)
    {W : ℂ × ℂ → ℂ → ℂ} (hW : W = fun P => normalizedSolution fun u =>
      P.1 * (if 0 < u.im then μ u else 0) + P.2 * (if u.im < 0 then conj (μ (conj u)) else 0))
    {Φ : ℂ × ℂ → ℂ → ℂ} (hΦ : Φ = fun P v => conj (μ v) *
      (dz (W P) ξ * dz (W P) (conj v) / (W P ξ - W P (conj v)) ^ 2) *
      (dz (W P) (conj v) * dz (W P) (conj z) / (W P (conj v) - W P (conj z)) ^ 2)) :
    ∃ L : ℂ × ℂ → ℂ, TendstoUniformlyOn (fun δ : ℝ => fun q => ∫ v in upperHalf \ ball z δ, Φ q v) L
      (𝓝[>] (0 : ℝ)) (closedBall (0 : ℂ) r ×ˢ closedBall (0 : ℂ) r) := by
  obtain ⟨ρ, hρ, C, hC, hball, hloc⟩ := s7l8_local_unif hk hμk hμs hz hξ hrk hW hΦ
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
    obtain ⟨M, hM⟩ := s7l8_tail_bound hk hμk hμs hz hξ hrk hW hΦ ha
    have h1 := e64_annulus_est hκ hC hball ha hab (hb.le.trans hδ₁p.2.le) (hM q hq).1 hl
    have h2 : ∫ v in ball z b, ‖v - z‖⁻¹ ≤ ∫ v in ball z δ₁, ‖v - z‖⁻¹ :=
      setIntegral_mono_set (e124p_invnorm_int z δ₁)
        (Eventually.of_forall fun v => inv_nonneg.mpr (norm_nonneg _)) (ball_subset_ball hb.le).eventuallyLE
    exact h1.trans ((mul_le_mul_of_nonneg_left h2 hC).trans hδ₁e.le)
  rcases le_total δ δ' with h | h
  · exact key δ δ' hδ.1 h hδ'.2
  · rw [norm_sub_rev]; exact key δ' δ hδ'.1 h hδ.2


/-- **Two-point `e64_core`.** For `ξ ≠ z` in `𝕌`, the truncated integrals of `∂_e[μ̄ K_e(ξ, v̄) K̄̄_e(v, z)]₀` over
`𝕌 \ B(z, δ)` converge to `-π ∂_e∂_ē K_e(ξ, z̄)|₀`. -/
theorem s7l8_core2 {μ : ℂ → ℂ} {k : ℝ} (hk : 0 ≤ k) (hμk : IsBeltramiCoeff μ upperHalf k)
    (hμs : ContDiffOn ℝ (⊤ : ℕ∞) μ upperHalf) {z : ℂ} (hz : z ∈ upperHalf) {ξ : ℂ} (hξ : ξ ∈ upperHalf)
    (hξz : ξ ≠ z) :
    (∀ δ : ℝ, 0 < δ → IntegrableOn (fun v => dz (fun e => conj (μ v) * kernelKbar (fun y => e * μ y) ξ v *
        kernelKbarbar (fun y => e * μ y) v z) 0) (upperHalf \ ball z δ)) ∧
      Tendsto (fun δ : ℝ => ∫ v in upperHalf \ ball z δ, dz (fun e => conj (μ v) * kernelKbar (fun y => e * μ y) ξ v *
        kernelKbarbar (fun y => e * μ y) v z) 0) (𝓝[>] 0) (𝓝 (-(π : ℂ) * dz (dzbar fun e => kernelKbar (fun y => e * μ y) ξ z) 0)) := by
  set c0 : ℂ := ((2 * π * I)⁻¹) ^ 2 with hc0
  obtain ⟨W, hW⟩ : ∃ W : ℂ × ℂ → ℂ → ℂ, W = fun P => normalizedSolution fun u =>
      P.1 * (if 0 < u.im then μ u else 0) + P.2 * (if u.im < 0 then conj (μ (conj u)) else 0) := ⟨_, rfl⟩
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : ℂ × ℂ → ℂ → ℂ, Φ = fun P v => conj (μ v) *
      (dz (W P) ξ * dz (W P) (conj v) / (W P ξ - W P (conj v)) ^ 2) *
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
  have hcΦ := s7l8_phi_cont hk hμk hμs hz hξ hrk hW hΦ
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
    obtain ⟨h1, h2⟩ := s7l8_phi_holo hk hμk hμs hz hξ hrk hW hΦ hv.1 (fun e => hv.2 (mem_singleton_iff.mpr e))
    have h := wr_cauchy_bidisc (f := fun q => Φ q v) (c := ((0, 0) : ℂ × ℂ)) hr hr (hcv v hv) h1 h2 hP
    exact h
  -- (h) `D(v)` is a torus coefficient
  have hTc : ∀ v ∈ upperHalf \ {z}, ContinuousOn (fun q : ℂ × ℂ => Φ q v) T := fun v hv => (hcv v hv).mono hTD
  have hD : ∀ v ∈ upperHalf \ {z}, dz (fun e => conj (μ v) * kernelKbar (fun y => e * μ y) ξ v *
      kernelKbarbar (fun y => e * μ y) v z) 0 = c0 * ∮ a in C(0, r), ∮ b in C(0, r), Φ (a, b) v / (a ^ 2 * b) := by
    intro v hv
    refine e64_torus_dz (G := fun q => Φ q v) hr (hTc v hv) ?_
    filter_upwards [ball_mem_nhds (0 : ℂ) hr] with ε hε
    have hεr : ‖ε‖ < r := by simpa using hε
    have hεk : ‖ε‖ * k < 1 := lt_of_le_of_lt (mul_le_mul_of_nonneg_right hεr.le hk) hrk
    show conj (μ v) * kernelKbar (fun y => ε * μ y) ξ v * kernelKbarbar (fun y => ε * μ y) v z = _
    rw [← s7l8_phi_diag hk hμk hμs hz hξ hW hΦ hεk hv.1,
      hcauchy v hv (ε, conj ε) ⟨by simpa using hεr, by simpa [RCLike.norm_conj] using hεr⟩]
  -- (a) domination and continuity of `I_δ`
  set I : ℝ → ℂ × ℂ → ℂ := fun δ q => ∫ v in upperHalf \ ball z δ, Φ q v with hId
  have hIc : ∀ δ : ℝ, 0 < δ → ContinuousOn (I δ) D := by
    intro δ hδ
    obtain ⟨g, hg, hgb⟩ := s7l8_dominate hk hμk hμs hz hξ hr hrR hRk hW hΦ hδ
    refine continuousOn_of_dominated (bound := g) (fun P hP => ?_) (fun P hP => ?_) hg ?_
    · obtain ⟨M, hM⟩ := s7l8_tail_bound hk hμk hμs hz hξ hrk hW hΦ hδ
      exact (hM P hP).1.aestronglyMeasurable
    · filter_upwards [ae_restrict_mem (hSm δ)] with v hv
      exact hgb P hP v hv
    · filter_upwards [ae_restrict_mem (hSm δ)] with v hv
      exact hcv v (hSz δ hδ v hv)
  -- (d) the uniform limit
  obtain ⟨L, hL⟩ := s7l8_param_pv hk hμk hμs hz hξ hrk hW hΦ
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
    obtain ⟨g, hg, hgb⟩ := s7l8_dominate hk hμk hμs hz hξ hr hrR hRk hW hΦ hδ
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
  -- (f) `∂_ε̄ K_ε(ξ, z̄) = -(1/π) L(ε, ε̄)` (the ball around `ξ` in `pv2` is negligible)
  have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 Real.pi_ne_zero
  have hξim : 0 < ξ.im := hξ
  set ρ0 : ℝ := min (ξ.im / 2) (‖ξ - z‖ / 2) with hρ0d
  have hξzn : 0 < ‖ξ - z‖ := norm_pos_iff.2 (sub_ne_zero.2 hξz)
  have hρ0 : 0 < ρ0 := lt_min (by linarith) (by linarith)
  have hBξ : closedBall ξ ρ0 ⊆ upperHalf \ {z} := by
    intro v hv
    rw [mem_closedBall, dist_eq_norm] at hv
    refine ⟨?_, fun hvz => ?_⟩
    · show 0 < v.im
      have h1 : |v.im - ξ.im| ≤ ‖v - ξ‖ := by rw [← Complex.sub_im]; exact Complex.abs_im_le_norm _
      have h2 := (abs_le.mp (h1.trans (hv.trans (min_le_left _ _)))).1
      linarith
    · rw [mem_singleton_iff] at hvz
      rw [hvz, norm_sub_rev] at hv
      have := hv.trans (min_le_right _ _)
      linarith
  have hh : ∀ ε : ℂ, ‖ε‖ < r → dzbar (fun e => kernelKbar (fun y => e * μ y) ξ z) ε =
      -(1 / π) * L (ε, conj ε) := by
    intro ε hεr
    have hεk : ‖ε‖ * k < 1 := lt_of_le_of_lt (mul_le_mul_of_nonneg_right hεr.le hk) hrk
    have hPD : (ε, conj ε) ∈ D := ⟨by simpa using hεr.le, by simpa [RCLike.norm_conj] using hεr.le⟩
    rw [(e124_eq_1_25 hk hμk hμs hεk hξ hz).2]
    congr 1
    -- `Φ(ε, ε̄)` is bounded near `ξ`
    have hcont : ContinuousOn (fun v => Φ (ε, conj ε) v) (closedBall ξ ρ0) := by
      have h := hcΦ.comp (continuous_const.prodMk continuous_id).continuousOn
        (fun v (hv : v ∈ closedBall ξ ρ0) =>
          (⟨hPD, hBξ hv⟩ : ((ε, conj ε), v) ∈ (closedBall (0 : ℂ) r ×ˢ closedBall (0 : ℂ) r) ×ˢ (upperHalf \ {z})))
      simpa only [Function.comp_def, id] using h
    obtain ⟨M, hM⟩ := (isCompact_closedBall ξ ρ0).exists_bound_of_continuousOn hcont
    have hsmall : Tendsto (fun δ : ℝ => ∫ v in (upperHalf \ ball z δ) ∩ ball ξ δ, Φ (ε, conj ε) v) (𝓝[>] 0)
        (𝓝 0) := by
      have hb : Tendsto (fun δ : ℝ => max M 0 * (δ ^ 2 * π)) (𝓝[>] 0) (𝓝 0) := by
        have : Tendsto (fun δ : ℝ => max M 0 * (δ ^ 2 * π)) (𝓝 0) (𝓝 (max M 0 * (0 ^ 2 * π))) :=
          (continuous_const.mul ((continuous_pow 2).mul continuous_const)).tendsto 0
        simpa using this.mono_left nhdsWithin_le_nhds
      refine squeeze_zero_norm' ?_ hb
      filter_upwards [Ioo_mem_nhdsGT hρ0] with δ hδ
      have hsub : (upperHalf \ ball z δ) ∩ ball ξ δ ⊆ closedBall ξ ρ0 := fun v hv =>
        ball_subset_closedBall (ball_subset_ball hδ.2.le hv.2)
      have hfin : volume ((upperHalf \ ball z δ) ∩ ball ξ δ) < ∞ :=
        (measure_mono inter_subset_right).trans_lt measure_ball_lt_top
      refine (norm_setIntegral_le_of_norm_le_const hfin fun v hv =>
        (hM v (hsub hv)).trans (le_max_left M 0)).trans ?_
      have hle : volume.real ((upperHalf \ ball z δ) ∩ ball ξ δ) ≤ volume.real (ball ξ δ) :=
        measureReal_mono inter_subset_right measure_ball_lt_top.ne
      have hball : volume.real (ball ξ δ) = δ ^ 2 * π := by
        rw [Measure.real, Complex.volume_ball, ENNReal.toReal_mul, ENNReal.toReal_pow,
          ENNReal.toReal_ofReal hδ.1.le]
        simp
      rw [← hball]
      exact mul_le_mul_of_nonneg_left hle (le_max_right _ _)
    have hlim0 : Tendsto (fun δ => ∫ v in upperHalf \ ball z δ, Φ (ε, conj ε) v) (𝓝[>] (0 : ℝ))
        (𝓝 (L (ε, conj ε))) := hL.tendsto_at hPD
    have hlim : Tendsto (fun δ : ℝ => ∫ v in upperHalf \ (ball ξ δ ∪ ball z δ), conj (μ v) *
        kernelKbar (fun y => ε * μ y) ξ v * kernelKbarbar (fun y => ε * μ y) v z) (𝓝[>] (0 : ℝ))
        (𝓝 (L (ε, conj ε))) := by
      have h2 := hlim0.sub hsmall
      rw [sub_zero] at h2
      refine h2.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with δ hδ
      have hδ0 : (0 : ℝ) < δ := hδ
      have hint : IntegrableOn (fun v => Φ (ε, conj ε) v) (upperHalf \ ball z δ) := by
        obtain ⟨M', hM'⟩ := s7l8_tail_bound hk hμk hμs hz hξ hrk hW hΦ hδ0
        exact (hM' (ε, conj ε) hPD).1
      have hset : upperHalf \ (ball ξ δ ∪ ball z δ) =
          (upperHalf \ ball z δ) \ ((upperHalf \ ball z δ) ∩ ball ξ δ) := by
        ext v; simp only [mem_diff, mem_union, mem_inter_iff]; tauto
      rw [hset, ← setIntegral_congr_fun ((hSm δ).diff ((hSm δ).inter measurableSet_ball))
        (fun v hv => s7l8_phi_diag hk hμk hμs hz hξ hW hΦ hεk hv.1.1),
        setIntegral_diff ((hSm δ).inter measurableSet_ball) hint inter_subset_left]
    exact hlim.limUnder_eq
  -- (g) E1 for `L`
  have hdzh : dz (dzbar fun e => kernelKbar (fun y => e * μ y) ξ z) 0 =
      c0 * ∮ a in C(0, r), ∮ b in C(0, r), (-(1 / π : ℂ)) * L (a, b) / (a ^ 2 * b) := by
    refine e64_torus_dz (G := fun q => (-(1 / π : ℂ)) * L q) hr (continuousOn_const.mul (hLc.mono hTD)) ?_
    filter_upwards [ball_mem_nhds (0 : ℂ) hr] with ε hε
    have hεr : ‖ε‖ < r := by simpa using hε
    have hpull : (∮ a in C(0, r), ∮ b in C(0, r), (-(1 / π : ℂ)) * L (a, b) / ((a - ε) * (b - conj ε))) =
        (-(1 / π : ℂ)) * ∮ a in C(0, r), ∮ b in C(0, r), 1 / ((a - ε) * (b - conj ε)) * L (a, b) := by
      rw [← e64_torus_const_mul]
      exact e64_torus_congr hr fun a _ b _ => by ring
    show dzbar (fun e => kernelKbar (fun y => e * μ y) ξ z) ε = c0 * ∮ a in C(0, r), ∮ b in C(0, r),
      (-(1 / π : ℂ)) * L (a, b) / ((a - ε) * (b - conj ε))
    rw [hh ε hεr, hLcauchy (ε, conj ε) ⟨by simpa using hεr, by simpa [RCLike.norm_conj] using hεr⟩, hpull]
    ring
  -- (h), (i)
  have hKab : ContinuousOn (fun q : ℂ × ℂ => 1 / (q.1 ^ 2 * q.2)) T :=
    continuousOn_const.div ((continuous_fst.pow 2).mul continuous_snd).continuousOn fun q hq =>
      mul_ne_zero (pow_ne_zero _ (hTne q hq).1) (hTne q hq).2
  have hDeq : ∀ δ : ℝ, 0 < δ → ∀ v ∈ upperHalf \ ball z δ,
      dz (fun e => conj (μ v) * kernelKbar (fun y => e * μ y) ξ v * kernelKbarbar (fun y => e * μ y) v z) 0 =
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
    have htarget : -(π : ℂ) * dz (dzbar fun e => kernelKbar (fun y => e * μ y) ξ z) 0 =
        c0 * ∮ a in C(0, r), ∮ b in C(0, r), 1 / (a ^ 2 * b) * L (a, b) := by
      rw [hdzh]
      have e1 : (∮ a in C(0, r), ∮ b in C(0, r), (-(1 / π : ℂ)) * L (a, b) / (a ^ 2 * b)) =
          (-(1 / π : ℂ)) * ∮ a in C(0, r), ∮ b in C(0, r), 1 / (a ^ 2 * b) * L (a, b) := by
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

/-- `e ↦ K_e(u, z̄)` is `C²` near `0`: it is `Ψ(e, ē)` for the holomorphic family `Ψ(P) = K_{W_P}(u, z̄)`
(`s7g_h_contDiffOn`). -/
theorem s7l8_K_C2 {ν ψ : ℂ → ℂ} (hν : IsHarmonicU ν ψ) {u z : ℂ} (hu : u ∈ upperHalf) (hz : z ∈ upperHalf) :
    ∃ r > 0, ContDiffOn ℝ 2 (fun e => kernelKbar (fun y => e * ν y) u z) (ball (0 : ℂ) r) := by
  obtain ⟨M, hM0, hM⟩ := harmonicU_bounded hν
  have hU := measurableSet_upperHalf_aux
  have hm : AEStronglyMeasurable ν (volume.restrict upperHalf) :=
    (harmonicU_continuousOn hν).aestronglyMeasurable hU
  have hνb : IsBeltramiCoeff ν upperHalf M := ⟨hm, (ae_restrict_mem hU).mono fun u hu => hM u hu⟩
  have hνs := wr_isHarmonicU_contDiffOn hν
  obtain ⟨W, hW⟩ : ∃ W : ℂ × ℂ → ℂ → ℂ, W = fun P => normalizedSolution fun u =>
      P.1 * (if 0 < u.im then ν u else 0) + P.2 * (if u.im < 0 then conj (ν (conj u)) else 0) := ⟨_, rfl⟩
  obtain ⟨-, hinj, hhol⟩ := e64_W_basic hM0 hνb hνs hW
  obtain ⟨hWc, hDc⟩ := e64_dzW_cont hM0 hνb hνs hW
  set Wset : Set (ℂ × ℂ) := {P : ℂ × ℂ | max ‖P.1‖ ‖P.2‖ * M < 1} with hWsetd
  have hWo : IsOpen Wset := isOpen_lt ((continuous_fst.norm.max continuous_snd.norm).mul continuous_const)
    continuous_const
  have huim : 0 < u.im := hu
  have hzim : 0 < z.im := hz
  have hy1 : u.im ≠ 0 := huim.ne'
  have hy3 : (conj z).im ≠ 0 := by rw [Complex.conj_im]; linarith
  set Ψ : ℂ × ℂ → ℂ := fun P => dz (W P) u * dz (W P) (conj z) / (W P u - W P (conj z)) ^ 2 with hΨd
  have hne : ∀ P ∈ Wset, (W P u - W P (conj z)) ^ 2 ≠ 0 := by
    intro P hP
    refine pow_ne_zero 2 (sub_ne_zero.mpr fun h => ?_)
    have := hinj P hP h
    have h2 : u.im = (conj z).im := by rw [this]
    rw [Complex.conj_im] at h2
    linarith
  -- separate holomorphy
  have hcurve : ∀ (c : ℂ → ℂ × ℂ) (t : ℂ), c t ∈ Wset →
      (∀ y, DifferentiableAt ℂ (fun t' => W (c t') y) t) →
      (∀ y, y.im ≠ 0 → DifferentiableAt ℂ (fun t' => dz (W (c t')) y) t) →
      DifferentiableAt ℂ (fun t' => Ψ (c t')) t := by
    intro c t hct hWy hDy
    exact ((hDy u hy1).mul (hDy _ hy3)).div (((hWy u).sub (hWy (conj z))).pow 2) (hne _ hct)
  have h1 : ∀ p ∈ Wset, DifferentiableAt ℂ (fun a => Ψ (a, p.2)) p.1 := by
    intro p hp
    refine hcurve (fun t => (t, p.2)) p.1 hp (fun y => ?_) (fun y hy => (e64_dzW_holo hM0 hνb hνs hW hp hy).1)
    exact DifferentiableAt.comp (g := fun Q => W Q y) p.1 (hhol y _ hp) (by fun_prop)
  have h2 : ∀ p ∈ Wset, DifferentiableAt ℂ (fun b => Ψ (p.1, b)) p.2 := by
    intro p hp
    refine hcurve (fun t => (p.1, t)) p.2 hp (fun y => ?_) (fun y hy => (e64_dzW_holo hM0 hνb hνs hW hp hy).2)
    exact DifferentiableAt.comp (g := fun Q => W Q y) p.2 (hhol y _ hp) (by fun_prop)
  -- continuity, hence local boundedness
  have hcomp : ∀ y : ℂ, y.im ≠ 0 → ContinuousOn (fun P => W P y) Wset ∧ ContinuousOn (fun P => dz (W P) y) Wset := by
    intro y hy
    have hm' : MapsTo (fun P : ℂ × ℂ => (P, y)) Wset (Wset ×ˢ {u : ℂ | u.im ≠ 0}) := fun P hP => ⟨hP, hy⟩
    have hc : Continuous fun P : ℂ × ℂ => (P, y) := continuous_id.prodMk continuous_const
    exact ⟨by simpa [Function.comp_def] using hWc.comp hc.continuousOn hm',
      by simpa [Function.comp_def] using hDc.comp hc.continuousOn hm'⟩
  obtain ⟨hWu, hDu⟩ := hcomp u hy1
  obtain ⟨hWz, hDz⟩ := hcomp (conj z) hy3
  have hΨc : ContinuousOn Ψ Wset := (hDu.mul hDz).div ((hWu.sub hWz).pow 2) hne
  have hb : ∀ p ∈ Wset, ∃ ρ > 0, ∃ C : ℝ, ∀ q ∈ ball p ρ, ‖Ψ q‖ ≤ C := by
    intro p hp
    have hca : ContinuousAt Ψ p := hΨc.continuousAt (hWo.mem_nhds hp)
    obtain ⟨ρ, hρ, hρb⟩ := Metric.continuousAt_iff.mp hca 1 one_pos
    refine ⟨ρ, hρ, ‖Ψ p‖ + 1, fun q hq => ?_⟩
    have := hρb hq
    rw [dist_eq_norm] at this
    have h3 := norm_le_norm_add_norm_sub' (Ψ q) (Ψ p)
    linarith [norm_sub_rev (Ψ q) (Ψ p)]
  have hΨ : ContDiffOn ℂ 2 Ψ Wset := s7g_h_contDiffOn hWo 2 Ψ h1 h2 hb
  -- the diagonal
  set r : ℝ := 1 / (M + 1) with hrd
  have hr : 0 < r := by positivity
  have hrM : ∀ e : ℂ, e ∈ ball (0 : ℂ) r → ‖e‖ * M < 1 := by
    intro e he
    have he' : ‖e‖ < r := by simpa using he
    calc ‖e‖ * M ≤ r * M := mul_le_mul_of_nonneg_right he'.le hM0
      _ < 1 := by rw [hrd, div_mul_eq_mul_div, one_mul, div_lt_one (by positivity)]; linarith
  have hdiag : ∀ e ∈ ball (0 : ℂ) r, kernelKbar (fun y => e * ν y) u z = Ψ (e, conj e) := by
    intro e he
    have hε := hrM e he
    have hWe : W (e, conj e) = wU (fun y => e * ν y) := by rw [hW, wr_wU_eq]
    set f := wU (fun y => e * ν y) with hf
    have hνe : IsBeltramiCoeff (fun y => e * ν y) upperHalf (‖e‖ * M) :=
      ⟨hνb.1.const_mul e, hνb.2.mono fun z hz => by
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left hz (norm_nonneg _)⟩
    have hsym : ∀ x, f (conj x) = conj (f x) := by
      rw [hf, e124_wU_eq_fMuSym hM0 hνb hε]
      exact (fMuSym_upperHalf (by positivity) hε hνe).2.2.1
    have hdsym : ∀ x, dz f (conj x) = conj (dz f x) := QCV.qcv_dz_conj_sym hsym
    simp only [hΨd, hWe]
    unfold kernelKbar
    rw [← hf, ← hsym z, ← hdsym z]
  have hmap : MapsTo (fun e : ℂ => (e, conj e)) (ball (0 : ℂ) r) Wset := by
    intro e he
    have hε := hrM e he
    show max ‖e‖ ‖conj e‖ * M < 1
    rw [RCLike.norm_conj, max_self]
    exact hε
  have hsm : ContDiff ℝ 2 (fun e : ℂ => (e, conj e)) := contDiff_id.prodMk Complex.conjCLE.contDiff
  refine ⟨r, hr, ((hΨ.restrict_scalars ℝ).comp hsm.contDiffOn hmap).congr fun e he => hdiag e he⟩

/-- The first variation of the kernel at `0` in principal-value form (`(1.25)` at `ε = 0`). -/
theorem s7l8_D1_formula {ν ψ : ℂ → ℂ} (hν : IsHarmonicU ν ψ) {u z : ℂ} (hu : u ∈ upperHalf) (hz : z ∈ upperHalf) :
    dz (fun e => kernelKbar (fun y => e * ν y) u z) 0 =
      -(1 / π) * pv2 (fun v => ν v / ((u - v) ^ 2 * (v - conj z) ^ 2)) u z := by
  obtain ⟨M, hM0, hM⟩ := harmonicU_bounded hν
  have hU := measurableSet_upperHalf_aux
  have hm : AEStronglyMeasurable ν (volume.restrict upperHalf) :=
    (harmonicU_continuousOn hν).aestronglyMeasurable hU
  have hνb : IsBeltramiCoeff ν upperHalf M := ⟨hm, (ae_restrict_mem hU).mono fun u hu => hM u hu⟩
  have hνs := wr_isHarmonicU_contDiffOn hν
  have hε0 : ‖(0 : ℂ)‖ * M < 1 := by simp
  rw [(e124_eq_1_25 hM0 hνb hνs hε0 hu hz).1]
  congr 2
  funext v
  rw [(e64_t9_K0 ν u v).1, (e64_t9_K0 ν v z).2.1]
  simp only [one_div, div_eq_mul_inv, mul_inv]
  ring

/-- Kernel symmetry: `K_e(z, ū) = \overline{K_e(u, z̄)}`, so `D̄₁(u, z) = \overline{D₁(z, u)}`. -/
theorem s7l8_D1b_conj (ν : ℂ → ℂ) (u z : ℂ) :
    dzbar (fun e => kernelKbar (fun y => e * ν y) u z) 0 =
      conj (dz (fun e => kernelKbar (fun y => e * ν y) z u) 0) := by
  have h : (fun e => kernelKbar (fun y => e * ν y) u z) =
      fun e => conj (kernelKbar (fun y => e * ν y) z u) := by
    funext e
    unfold kernelKbar
    rw [map_div₀, map_mul, map_pow, map_sub, Complex.conj_conj, Complex.conj_conj]
    ring
  rw [h, p71r_dzbar_conj]

/-- The extended coefficient `g_z = 1_𝕌 ν/(· - z̄)²`: measurable, smooth on `𝕌`, and `∫ |g_z|² ≤ M² π/(Im z)²`. -/
theorem s7l8_g_data {ν ψ : ℂ → ℂ} (hν : IsHarmonicU ν ψ) {M : ℝ} (hM : ∀ v ∈ upperHalf, ‖ν v‖ ≤ M)
    {z : ℂ} (hz : z ∈ upperHalf) :
    Measurable (upperHalf.indicator fun v => ν v / (v - conj z) ^ 2) ∧
      ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (upperHalf.indicator fun v => ν v / (v - conj z) ^ 2) upperHalf ∧
      MemLp (upperHalf.indicator fun v => ν v / (v - conj z) ^ 2) 2 volume ∧
      (∫⁻ v, ‖upperHalf.indicator (fun v => ν v / (v - conj z) ^ 2) v‖ₑ ^ 2) ≤
        ENNReal.ofReal (M ^ 2 * (π / z.im ^ 2)) := by
  have hU := measurableSet_upperHalf_aux
  have hUo : IsOpen upperHalf := isOpen_lt continuous_const Complex.continuous_im
  have hzim : 0 < z.im := hz
  have hne : ∀ v ∈ upperHalf, v - conj z ≠ 0 := fun v hv h => by
    have := congrArg Complex.im h
    simp only [Complex.sub_im, Complex.conj_im, Complex.zero_im] at this
    have : 0 < v.im := hv
    linarith
  have hνc := harmonicU_continuousOn hν
  have hF : ContinuousOn (fun v => ν v / (v - conj z) ^ 2) upperHalf :=
    hνc.div (by fun_prop) fun v hv => pow_ne_zero 2 (hne v hv)
  set g := upperHalf.indicator fun v => ν v / (v - conj z) ^ 2 with hgd
  have hgm : Measurable g := by
    rw [hgd, ← Set.piecewise_eq_indicator]
    exact hF.measurable_piecewise continuousOn_const hU
  have hgs : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g upperHalf := by
    have hs : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun v => ν v / (v - conj z) ^ 2) upperHalf := by
      have h1 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ν upperHalf := wr_isHarmonicU_contDiffOn hν
      have h2 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun v : ℂ => (v - conj z) ^ 2) upperHalf :=
        ((contDiff_id.sub contDiff_const).pow 2).contDiffOn
      refine (h1.mul (h2.inv fun v hv => pow_ne_zero 2 (hne v hv))).congr fun v _ => ?_
      simp only [Pi.inv_apply, div_eq_mul_inv]
    exact hs.congr fun v hv => Set.indicator_of_mem hv _
  -- the majorant
  set S : Set ℂ := {w : ℂ | z.im ≤ ‖w - conj z‖} with hSd
  have hS : MeasurableSet S := measurableSet_le measurable_const (measurable_id.sub_const _).norm
  obtain ⟨hSi, hSv⟩ := Ch2.s2c_l4_outside_ball (conj z) hzim
  have hUS : upperHalf ⊆ S := by
    intro v hv
    show z.im ≤ ‖v - conj z‖
    have h1 := Complex.abs_im_le_norm (v - conj z)
    have h2 : (v - conj z).im = v.im + z.im := by simp
    have : 0 < v.im := hv
    rw [h2, abs_of_pos (by linarith)] at h1
    linarith
  have hpt : ∀ v, ‖g v‖ ^ 2 ≤ M ^ 2 * S.indicator (fun w : ℂ => (‖w - conj z‖ ^ 4)⁻¹) v := by
    intro v
    by_cases hv : v ∈ upperHalf
    · rw [hgd, Set.indicator_of_mem hv, Set.indicator_of_mem (hUS hv), norm_div, norm_pow, div_pow]
      have hp : 0 < ‖v - conj z‖ := norm_pos_iff.2 (hne v hv)
      have hM0 : 0 ≤ ‖ν v‖ := norm_nonneg _
      rw [← pow_mul, div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hM0 (hM v hv) 2) (by positivity)
    · rw [hgd, Set.indicator_of_notMem hv, norm_zero]
      have : 0 ≤ S.indicator (fun w : ℂ => (‖w - conj z‖ ^ 4)⁻¹) v :=
        Set.indicator_nonneg (fun w _ => by positivity) v
      nlinarith [sq_nonneg M]
  have hmaj : Integrable (fun v => M ^ 2 * S.indicator (fun w : ℂ => (‖w - conj z‖ ^ 4)⁻¹) v) :=
    (hSi.integrable_indicator hS).const_mul _
  have hsq : Integrable (fun v => ‖g v‖ ^ 2) :=
    hmaj.mono' ((hgm.norm.pow_const 2).aestronglyMeasurable) (Eventually.of_forall fun v => by
      rw [Real.norm_of_nonneg (by positivity)]; exact hpt v)
  have hg2 : MemLp g 2 volume := (memLp_two_iff_integrable_sq_norm hgm.aestronglyMeasurable).2 hsq
  refine ⟨hgm, hgs, hg2, ?_⟩
  calc (∫⁻ v, ‖g v‖ₑ ^ 2) = ∫⁻ v, ENNReal.ofReal (‖g v‖ ^ 2) := by
        refine lintegral_congr fun v => ?_
        rw [← ofReal_norm, ENNReal.ofReal_pow (norm_nonneg _)]
    _ ≤ ∫⁻ v, ENNReal.ofReal (M ^ 2 * S.indicator (fun w : ℂ => (‖w - conj z‖ ^ 4)⁻¹) v) :=
        lintegral_mono fun v => ENNReal.ofReal_le_ofReal (hpt v)
    _ = ENNReal.ofReal (∫ v, M ^ 2 * S.indicator (fun w : ℂ => (‖w - conj z‖ ^ 4)⁻¹) v) :=
        (ofReal_integral_eq_lintegral_ofReal hmaj (Eventually.of_forall fun v =>
          mul_nonneg (sq_nonneg _) (Set.indicator_nonneg (fun w _ => by positivity) v))).symm
    _ = ENNReal.ofReal (M ^ 2 * (π / z.im ^ 2)) := by
        rw [integral_const_mul, integral_indicator hS, hSv]

/-- The truncated integrals of `g_z/(· - u)²` converge to the principal value of `(1.25)`. -/
theorem s7l8_g_trunc {ν ψ : ℂ → ℂ} (hν : IsHarmonicU ν ψ) {z : ℂ} (hz : z ∈ upperHalf) {u : ℂ}
    (hu : u ∈ upperHalf) :
    Tendsto (fun r : ℝ => ∫ ζ in {ζ : ℂ | r < ‖ζ - u‖},
        (upperHalf.indicator fun v => ν v / (v - conj z) ^ 2) ζ / (ζ - u) ^ 2) (𝓝[>] 0)
      (𝓝 (pv2 (fun v => ν v / ((u - v) ^ 2 * (v - conj z) ^ 2)) u z)) := by
  have hU := measurableSet_upperHalf_aux
  refine (s71_v_trunc hν hz hu).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with r hr
  have hr0 : (0 : ℝ) < r := hr
  have hS : MeasurableSet {ζ : ℂ | r < ‖ζ - u‖} := measurableSet_lt measurable_const (measurable_id.sub_const u).norm
  have hpt : (fun ζ => (upperHalf.indicator fun v => ν v / (v - conj z) ^ 2) ζ / (ζ - u) ^ 2) =
      upperHalf.indicator fun v => ν v / ((u - v) ^ 2 * (v - conj z) ^ 2) := by
    funext ζ
    by_cases hζ : ζ ∈ upperHalf
    · rw [Set.indicator_of_mem hζ, Set.indicator_of_mem hζ]
      rw [show (u - ζ) ^ 2 = (ζ - u) ^ 2 by ring]
      field_simp
    · rw [Set.indicator_of_notMem hζ, Set.indicator_of_notMem hζ, zero_div]
  rw [hpt, setIntegral_indicator hU]
  refine setIntegral_congr_set ?_
  rw [ae_eq_set]
  constructor
  · refine measure_mono_null (fun ζ hζ => ?_) (Measure.addHaar_sphere volume u r)
    have h1 : ζ ∉ ball u r := hζ.1.2
    rw [mem_ball, dist_eq_norm, not_lt] at h1
    have h2 : ¬ (r < ‖ζ - u‖) := fun h => hζ.2 ⟨h, hζ.1.1⟩
    rw [mem_sphere, dist_eq_norm]
    exact le_antisymm (not_lt.1 h2) h1
  · refine measure_mono_null (fun ζ hζ => ?_) (measure_empty (μ := volume))
    exact hζ.2 ⟨hζ.1.2, fun hb => absurd hζ.1.1 (not_lt.2 (le_of_lt (by simpa [dist_eq_norm] using hb)))⟩

/-- **`L²` bound of `D₁(·, z)`** by the Beurling isometry: `∫_𝕌 |D₁(u, z)|² ≤ M² π/(Im z)²`. -/
theorem s7l8_D1_L2 {ν ψ : ℂ → ℂ} (hν : IsHarmonicU ν ψ) {M : ℝ} (hM : ∀ v ∈ upperHalf, ‖ν v‖ ≤ M)
    {z : ℂ} (hz : z ∈ upperHalf) :
    (∫⁻ u in upperHalf, ‖dz (fun e => kernelKbar (fun y => e * ν y) u z) 0‖ₑ ^ 2) ≤
      ENNReal.ofReal (M ^ 2 * (π / z.im ^ 2)) := by
  have hUo : IsOpen upperHalf := isOpen_lt continuous_const Complex.continuous_im
  obtain ⟨hgm, hgs, hg2, hgb⟩ := s7l8_g_data hν hM hz
  have hH := s7l8_hilbertH_local hgm hg2 hUo hgs (Λ := fun u => pv2 (fun v => ν v / ((u - v) ^ 2 *
    (v - conj z) ^ 2)) u z) fun u hu => s7l8_g_trunc hν hz hu
  have hae : ∀ᵐ u ∂(volume.restrict upperHalf), ‖dz (fun e => kernelKbar (fun y => e * ν y) u z) 0‖ₑ ^ 2 =
      ‖hilbertH (upperHalf.indicator fun v => ν v / (v - conj z) ^ 2) u‖ₑ ^ 2 := by
    filter_upwards [hH, ae_restrict_mem measurableSet_upperHalf_aux] with u h hu
    rw [h, s7l8_D1_formula hν hu hz]
  rw [lintegral_congr_ae hae]
  refine (setLIntegral_le_lintegral _ _).trans (le_trans (le_of_eq ?_) hgb)
  have hiso := (hilbertH_memLp_two hg2)
  have e1 := eLpNorm_nnreal_pow_eq_lintegral (p := 2) (by norm_num) hiso.1.aestronglyMeasurable
  have e2 := eLpNorm_nnreal_pow_eq_lintegral (p := 2) (by norm_num) hg2.aestronglyMeasurable
  simp only [NNReal.coe_ofNat, ENNReal.coe_ofNat] at e1 e2
  rw [hiso.2] at e1
  have e3 : (∫⁻ x, ‖hilbertH (upperHalf.indicator fun v => ν v / (v - conj z) ^ 2) x‖ₑ ^ (2 : ℝ)) =
      ∫⁻ x, ‖hilbertH (upperHalf.indicator fun v => ν v / (v - conj z) ^ 2) x‖ₑ ^ (2 : ℕ) :=
    lintegral_congr fun x => by rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, ENNReal.rpow_natCast]
  have e4 : (∫⁻ x, ‖(upperHalf.indicator fun v => ν v / (v - conj z) ^ 2) x‖ₑ ^ (2 : ℝ)) =
      ∫⁻ x, ‖(upperHalf.indicator fun v => ν v / (v - conj z) ^ 2) x‖ₑ ^ (2 : ℕ) :=
    lintegral_congr fun x => by rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, ENNReal.rpow_natCast]
  exact e3.symm.trans ((e1.symm.trans e2).trans e4)

/-- **Joint continuity of `D₁`** on `𝕌 × 𝕌` (from the joint `C³` regularity of `(ε, u) ↦ w_{εν}(u)`). -/
theorem s7l8_D1_cont {ν ψ : ℂ → ℂ} (hν : IsHarmonicU ν ψ) :
    ContinuousOn (fun p : ℂ × ℂ => dz (fun e => kernelKbar (fun y => e * ν y) p.1 p.2) 0)
      (upperHalf ×ˢ upperHalf) := by
  obtain ⟨M, hM0, hM⟩ := harmonicU_bounded hν
  have hU := measurableSet_upperHalf_aux
  have hUo : IsOpen upperHalf := isOpen_lt continuous_const Complex.continuous_im
  have hm : AEStronglyMeasurable ν (volume.restrict upperHalf) :=
    (harmonicU_continuousOn hν).aestronglyMeasurable hU
  have hνb : IsBeltramiCoeff ν upperHalf M := ⟨hm, (ae_restrict_mem hU).mono fun u hu => hM u hu⟩
  have hνs := wr_isHarmonicU_contDiffOn hν
  set Ue : Set ℂ := {e : ℂ | ‖e‖ * M < 1} with hUed
  have hUeo : IsOpen Ue := isOpen_lt (continuous_norm.mul continuous_const) continuous_const
  have h0Ue : (0 : ℂ) ∈ Ue := by simp [hUed]
  set F : ℂ × ℂ → ℂ := fun q => wU (fun u => q.1 * ν u) q.2 with hFd
  have hF3 : ContDiffOn ℝ 3 F (Ue ×ˢ upperHalf) := wr_joint_contDiff_U hM0 hνb hνs
  have hO : IsOpen (Ue ×ˢ upperHalf) := hUeo.prod hUo
  set G : ℂ × ℂ → ℂ := fun q => (fderiv ℝ F q (0, 1) - I * fderiv ℝ F q (0, I)) / 2 with hGd
  have hF' : ContDiffOn ℝ 2 (fderiv ℝ F) (Ue ×ˢ upperHalf) := hF3.fderiv_of_isOpen hO (by norm_num)
  have hG2 : ContDiffOn ℝ 2 G (Ue ×ˢ upperHalf) :=
    ((hF'.clm_apply contDiffOn_const).sub (contDiffOn_const.mul (hF'.clm_apply contDiffOn_const))).div_const 2
  have hGdz : ∀ q ∈ Ue ×ˢ upperHalf, dz (wU fun u => q.1 * ν u) q.2 = G q := by
    intro q hq
    have hdF : DifferentiableAt ℝ F q := (hF3.differentiableOn (by norm_num) q hq).differentiableAt (hO.mem_nhds hq)
    have hsl : fderiv ℝ (wU fun u => q.1 * ν u) q.2 = (fderiv ℝ F q).comp (ContinuousLinearMap.inr ℝ ℂ ℂ) := by
      have e1 : (wU fun u => q.1 * ν u) = fun y => F (q.1, y) := rfl
      rw [e1]
      exact (hdF.hasFDerivAt.comp q.2 (hasFDerivAt_prodMk_right (𝕜 := ℝ) q.1 q.2)).fderiv
    show (fderiv ℝ (wU fun u => q.1 * ν u) q.2 1 - I * fderiv ℝ (wU fun u => q.1 * ν u) q.2 I) / 2 = _
    rw [hsl]
    rfl
  -- the joint kernel
  set S : Set (ℂ × ℂ × ℂ) := Ue ×ˢ (upperHalf ×ˢ upperHalf) with hSd
  have hSo : IsOpen S := hUeo.prod (hUo.prod hUo)
  set Φ : ℂ × ℂ × ℂ → ℂ := fun x => kernelKbar (fun y => x.1 * ν y) x.2.1 x.2.2 with hΦd
  have hm1 : MapsTo (fun x : ℂ × ℂ × ℂ => (x.1, x.2.1)) S (Ue ×ˢ upperHalf) := fun x hx => ⟨hx.1, hx.2.1⟩
  have hm2 : MapsTo (fun x : ℂ × ℂ × ℂ => (x.1, x.2.2)) S (Ue ×ˢ upperHalf) := fun x hx => ⟨hx.1, hx.2.2⟩
  have hs1 : ContDiff ℝ 2 (fun x : ℂ × ℂ × ℂ => (x.1, x.2.1)) := contDiff_fst.prodMk (contDiff_fst.comp contDiff_snd)
  have hs2 : ContDiff ℝ 2 (fun x : ℂ × ℂ × ℂ => (x.1, x.2.2)) := contDiff_fst.prodMk (contDiff_snd.comp contDiff_snd)
  have hc : ContDiff ℝ 2 (fun u : ℂ => conj u) := Complex.conjCLE.contDiff
  have hGa := hG2.comp hs1.contDiffOn hm1
  have hGb := hc.comp_contDiffOn (hG2.comp hs2.contDiffOn hm2)
  have hFa := (hF3.of_le (by norm_num)).comp hs1.contDiffOn hm1
  have hFb := hc.comp_contDiffOn ((hF3.of_le (by norm_num)).comp hs2.contDiffOn hm2)
  have hden : ∀ x ∈ S, (F (x.1, x.2.1) - conj (F (x.1, x.2.2))) ^ 2 ≠ 0 := by
    intro x hx
    obtain ⟨-, hbij, hsym, -⟩ := p71_V_facts hM0 hνb hx.1
    refine pow_ne_zero 2 (sub_ne_zero.mpr fun h => ?_)
    have h1 : F (x.1, x.2.1) = F (x.1, conj x.2.2) := by
      rw [h]
      exact (hsym x.2.2).symm
    have h2 : x.2.1 = conj x.2.2 := hbij.1 h1
    have h3 := congrArg Complex.im h2
    rw [Complex.conj_im] at h3
    have : 0 < x.2.1.im := hx.2.1
    have : 0 < x.2.2.im := hx.2.2
    linarith
  have hΦ : ContDiffOn ℝ 2 Φ S := by
    refine ((hGa.mul hGb).mul (((hFa.sub hFb).pow 2).inv hden)).congr fun x hx => ?_
    simp only [hΦd, Function.comp_apply]
    unfold kernelKbar
    rw [hGdz (x.1, x.2.1) (hm1 hx), hGdz (x.1, x.2.2) (hm2 hx), div_eq_mul_inv]
    rfl
  -- the `e`-derivative at `0` through `fderiv Φ`
  have hΦ' : ContinuousOn (fderiv ℝ Φ) S := hΦ.continuousOn_fderiv_of_isOpen hSo (by norm_num)
  have hD : ∀ p ∈ upperHalf ×ˢ upperHalf, dz (fun e => kernelKbar (fun y => e * ν y) p.1 p.2) 0 =
      (fderiv ℝ Φ (0, p) (1, 0) - I * fderiv ℝ Φ (0, p) (I, 0)) / 2 := by
    intro p hp
    have hmem : ((0 : ℂ), p) ∈ S := ⟨h0Ue, hp⟩
    have hdΦ : DifferentiableAt ℝ Φ (0, p) :=
      (hΦ.differentiableOn (by norm_num) _ hmem).differentiableAt (hSo.mem_nhds hmem)
    have hsl : fderiv ℝ (fun e => kernelKbar (fun y => e * ν y) p.1 p.2) 0 =
        (fderiv ℝ Φ (0, p)).comp (ContinuousLinearMap.inl ℝ ℂ (ℂ × ℂ)) := by
      have e1 : (fun e => kernelKbar (fun y => e * ν y) p.1 p.2) = fun e => Φ (e, p) := rfl
      rw [e1]
      exact (hdΦ.hasFDerivAt.comp (0 : ℂ) (hasFDerivAt_prodMk_left (𝕜 := ℝ) (0 : ℂ) p)).fderiv
    show (fderiv ℝ (fun e => kernelKbar (fun y => e * ν y) p.1 p.2) 0 1 -
      I * fderiv ℝ (fun e => kernelKbar (fun y => e * ν y) p.1 p.2) 0 I) / 2 = _
    rw [hsl]
    rfl
  have hcont : ContinuousOn (fun p : ℂ × ℂ => (fderiv ℝ Φ (0, p) (1, 0) - I * fderiv ℝ Φ (0, p) (I, 0)) / 2)
      (upperHalf ×ˢ upperHalf) := by
    have hcm : ContinuousOn (fun p : ℂ × ℂ => fderiv ℝ Φ (0, p)) (upperHalf ×ˢ upperHalf) :=
      hΦ'.comp (continuous_const.prodMk continuous_id).continuousOn fun p hp => (⟨h0Ue, hp⟩ : ((0 : ℂ), p) ∈ S)
    exact ((hcm.clm_apply continuousOn_const).sub (continuousOn_const.mul (hcm.clm_apply continuousOn_const))).div_const 2
  exact hcont.congr fun p hp => hD p hp

/-- Cauchy–Schwarz for `∫⁻` (as `cui_lintegral_cauchy_schwarz`, outside this closure). -/
theorem s7l8_cs {α : Type*} [MeasurableSpace α] (μ : Measure α)
    {A B : α → ℝ≥0∞} (hA : AEMeasurable A μ) (hB : AEMeasurable B μ) :
    (∫⁻ w, A w * B w ∂μ) ^ 2 ≤ (∫⁻ w, A w ^ 2 ∂μ) * (∫⁻ w, B w ^ 2 ∂μ) := by
  have hh := ENNReal.lintegral_mul_le_Lp_mul_Lq μ Real.HolderConjugate.two_two hA hB
  have hh2 := pow_le_pow_left₀ zero_le hh 2
  simp only [Pi.mul_apply, ENNReal.rpow_two, mul_pow, ← ENNReal.rpow_natCast,
    ← ENNReal.rpow_mul] at hh2 ⊢
  norm_num at hh2 ⊢
  exact hh2

/-- `ε ↦ Q_U(μ, εν)(z)` is `C²` near `0` (`Q = (12/π) J/ρ^{εν}` with `J`, `ρ^{εν}` of class `C²`). -/
theorem s7l8_Q_C2 {μ φ ν ψ : ℂ → ℂ} (hμ : IsHarmonicU μ φ) (hν : IsHarmonicU ν ψ) {z : ℂ}
    (hz : z ∈ upperHalf) :
    ∃ r > 0, ContDiffOn ℝ 2 (fun e => QfunU μ (fun u => e * ν u) z) (ball 0 r) := by
  obtain ⟨C, hC0, hmB, hms⟩ := s71_harm_setup hν
  obtain ⟨W, hW⟩ : ∃ W : ℂ × ℂ → ℂ → ℂ, W = fun P => normalizedSolution fun u =>
      P.1 * (if 0 < u.im then ν u else 0) + P.2 * (if u.im < 0 then conj (ν (conj u)) else 0) := ⟨_, rfl⟩
  have hC1 : 0 < C + 1 := by linarith
  have hR0p : 0 < 1 / (C + 1) := by positivity
  have hR0k : 1 / (C + 1) * C < 1 := by
    rw [div_mul_eq_mul_div, one_mul, div_lt_one hC1]
    linarith
  set r1 := min (1 / (C + 1)) (1 / (C + 1)) with hr1d
  have hr1 : 0 < r1 := lt_min hR0p hR0p
  have hJ := s7g_f2_Jreg hμ hC0 hmB hms hR0p hR0k hW hz
  have hDr := s7g_f2_Dreg hC0 hmB hms hR0k hW hz
  have hD0 : rhoVar ν 0 z = rhoU z := (rhoVar_pullback ν 0 hz).2
  have hρ0 : (rhoU z : ℂ) ≠ 0 := by
    rw [Complex.ofReal_ne_zero]
    have him : 0 < z.im := hz
    unfold rhoU
    positivity
  have hDc : ContinuousAt (fun e => rhoVar ν e z) 0 :=
    hDr.continuousOn.continuousAt (ball_mem_nhds 0 hr1)
  have hev : ∀ᶠ e in 𝓝 (0 : ℂ), rhoVar ν e z ≠ 0 ∧ e ∈ ball (0 : ℂ) r1 :=
    (hDc.eventually_ne (show rhoVar ν 0 z ≠ 0 by rw [hD0]; exact hρ0)).and (ball_mem_nhds 0 hr1)
  obtain ⟨r, hr, hrr⟩ := Metric.eventually_nhds_iff.1 hev
  have hball : ∀ e ∈ ball (0 : ℂ) r, rhoVar ν e z ≠ 0 ∧ e ∈ ball (0 : ℂ) r1 := fun e he =>
    hrr (by rwa [mem_ball] at he)
  have hsub : ball (0 : ℂ) r ⊆ ball (0 : ℂ) r1 := fun e he => (hball e he).2
  have hεk : ∀ e ∈ ball (0 : ℂ) r, ‖e‖ * C < 1 := by
    intro e he
    have h := lt_of_lt_of_le (mem_ball_zero_iff.1 (hsub he)) (min_le_right _ _)
    rw [lt_div_iff₀ hC1] at h
    nlinarith [norm_nonneg e]
  refine ⟨r, hr, (((contDiffOn_const (c := (12 / π : ℂ))).mul (hJ.mono hsub)).mul
    ((hDr.mono hsub).inv fun e he => (hball e he).1)).congr fun e he => ?_⟩
  rw [Pi.inv_apply, ← div_eq_mul_inv, eq_div_iff (hball e he).1,
    ← s71_eq_7_1 hμ hν hC0 hmB (hεk e he) hz]
  ring

/-- Second-order `ε`-bookkeeping: if `F(ε) = c · \overline{G(ε̄)}` near `0` with `G` of class `C²`, then
`∂_ε∂_ε̄ F(0) = c · \overline{∂_ε̄∂_ε G(0)}`. -/
theorem s7l8_eps2 {F G : ℂ → ℂ} {c : ℂ} {r : ℝ} (hr : 0 < r) (hG : ContDiffOn ℝ 2 G (ball 0 r))
    (hFG : F =ᶠ[𝓝 (0 : ℂ)] fun ε => c * conj (G (conj ε))) :
    dz (dzbar F) 0 = c * conj (dzbar (dz G) 0) := by
  have hGc : ContDiffOn ℝ 2 (fun e => G (conj e)) (ball 0 r) :=
    hG.comp Complex.conjCLE.contDiff.contDiffOn fun e he => by
      rw [mem_ball_zero_iff] at he ⊢
      rw [Complex.norm_conj]
      exact he
  have hK : ContDiffOn ℝ 2 (fun e => conj (G (conj e))) (ball 0 r) :=
    (Complex.conjCLE.contDiff.comp_contDiffOn hGc).congr fun e _ => rfl
  have hH : ContDiffOn ℝ 2 (fun e => c * conj (G (conj e))) (ball 0 r) := contDiffOn_const.mul hK
  have e1 : dz (dzbar F) 0 = dz (dzbar fun e => c * conj (G (conj e))) 0 := s7g_f2_germ2 hFG
  have e2 : dz (dzbar fun e => c * conj (G (conj e))) 0 = dzbar (dz fun e => c * conj (G (conj e))) 0 :=
    wp_wirtinger_comm (hH.contDiffAt (ball_mem_nhds 0 hr))
  have e3 : dzbar (dz fun e => c * conj (G (conj e))) 0 = c * dzbar (dz fun e => conj (G (conj e))) 0 :=
    s7g_f2_wconst hr hK c
  have e4 : dzbar (dz fun e => conj (G (conj e))) 0 = conj (dz (dzbar fun e => G (conj e)) 0) :=
    s7g_f2_conjW _ 0
  have e5 : dz (dzbar fun e => G (conj e)) 0 = dzbar (dz G) 0 := s7g_f2_conjflip hr hG
  rw [e1, e2, e3, e4, e5]

/-- Dropping a harmless ball: if `f` is integrable off every ball at `z` and `v ≠ z`, the two-ball truncations at
`z, v` have the same limit as the one-ball truncations at `z`. -/
theorem s7l8_pv_drop {f : ℂ → ℂ} {z v : ℂ} (hv : v ∈ upperHalf) (hvz : v ≠ z)
    (hfi : ∀ δ : ℝ, 0 < δ → IntegrableOn f (upperHalf \ ball z δ)) {L : ℂ}
    (hL : Tendsto (fun δ : ℝ => ∫ x in upperHalf \ ball z δ, f x) (𝓝[>] 0) (𝓝 L)) :
    Tendsto (fun δ : ℝ => ∫ x in upperHalf \ (ball z δ ∪ ball v δ), f x) (𝓝[>] 0) (𝓝 L) := by
  have hU := measurableSet_upperHalf_aux
  have hvim : 0 < v.im := hv
  have hvzn : 0 < ‖v - z‖ := norm_pos_iff.2 (sub_ne_zero.2 hvz)
  set δ0 : ℝ := min (‖v - z‖ / 2) (v.im / 2) with hδ0d
  have hδ0 : 0 < δ0 := lt_min (by linarith) (by linarith)
  have hballA : ∀ δ : ℝ, 0 < δ → δ < δ0 → ball v δ ⊆ upperHalf \ ball z δ ∧ ball v δ ⊆ upperHalf \ ball z δ0 := by
    intro δ hδ hδδ
    suffices key : ∀ x ∈ ball v δ, x ∈ upperHalf ∧ ∀ d, d ≤ δ0 → x ∉ ball z d from
      ⟨fun x hx => ⟨(key x hx).1, (key x hx).2 δ hδδ.le⟩, fun x hx => ⟨(key x hx).1, (key x hx).2 δ0 le_rfl⟩⟩
    intro x hx
    rw [mem_ball, dist_eq_norm] at hx
    have hxU : x ∈ upperHalf := by
      show 0 < x.im
      have h1 : |x.im - v.im| ≤ ‖x - v‖ := by rw [← Complex.sub_im]; exact Complex.abs_im_le_norm _
      have h2 := (abs_le.mp h1).1
      have : δ0 ≤ v.im / 2 := min_le_right _ _
      linarith
    refine ⟨hxU, ?_⟩
    · intro d hd hxz
      rw [mem_ball, dist_eq_norm] at hxz
      have h3 : ‖v - z‖ ≤ ‖v - x‖ + ‖x - z‖ := norm_sub_le_norm_sub_add_norm_sub v x z
      rw [norm_sub_rev v x] at h3
      have : δ0 ≤ ‖v - z‖ / 2 := min_le_left _ _
      linarith
  have hsmall : Tendsto (fun δ : ℝ => ∫ x in (upperHalf \ ball z δ) ∩ ball v δ, f x) (𝓝[>] 0) (𝓝 0) := by
    have hne : ∀ᵐ a ∂(volume.restrict (upperHalf \ ball z δ0)), a ≠ v :=
      ae_restrict_of_ae (by simp [ae_iff, measure_singleton])
    have hdc : Tendsto (fun δ : ℝ => ∫ x in upperHalf \ ball z δ0, (ball v δ).indicator f x) (𝓝[>] 0)
        (𝓝 (∫ x in upperHalf \ ball z δ0, (0 : ℂ))) := by
      refine tendsto_integral_filter_of_dominated_convergence (fun x => ‖f x‖)
        (Eventually.of_forall fun δ => ((hfi δ0 hδ0).aestronglyMeasurable.indicator measurableSet_ball))
        (Eventually.of_forall fun δ => Eventually.of_forall fun x => ?_) (hfi δ0 hδ0).norm ?_
      · by_cases hx : x ∈ ball v δ
        · simp [Set.indicator_of_mem hx]
        · simp [Set.indicator_of_notMem hx]
      · filter_upwards [hne] with x hx
        have hp : 0 < ‖x - v‖ := norm_pos_iff.2 (sub_ne_zero.2 hx)
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [Ioo_mem_nhdsGT hp] with δ hδ
        have : x ∉ ball v δ := by rw [mem_ball, dist_eq_norm, not_lt]; exact hδ.2.le
        simp [Set.indicator_of_notMem this]
    rw [integral_zero] at hdc
    refine hdc.congr' ?_
    filter_upwards [Ioo_mem_nhdsGT hδ0] with δ hδ
    obtain ⟨h1, h2⟩ := hballA δ hδ.1 hδ.2
    rw [setIntegral_indicator measurableSet_ball, inter_eq_right.2 h2, inter_eq_right.2 h1]
  have h2 := hL.sub hsmall
  rw [sub_zero] at h2
  refine h2.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  have hδ' : (0 : ℝ) < δ := hδ
  have hset : upperHalf \ (ball z δ ∪ ball v δ) =
      (upperHalf \ ball z δ) \ ((upperHalf \ ball z δ) ∩ ball v δ) := by
    ext x; simp only [mem_diff, mem_union, mem_inter_iff]; tauto
  rw [hset, setIntegral_diff ((hU.diff measurableSet_ball).inter measurableSet_ball) (hfi δ hδ')
    inter_subset_left]

/-- **(R2) Regularization** of the second-variable form of `D₁` (the partial fractions of `prop_6_3`, the two
singular terms dropping out by `eq_6_3` and `cor_1_15`): for `v ≠ z` in `𝕌`,
`PV ∬ ν(x)/((z - x)²(x - v̄)²) = (z̄ - v̄)² ∬ ν(x) (1/((x - v̄)²(z - v̄)²(x - z̄)²) + 2(z - z̄)/((x - z̄)³(x - v̄)(z - v̄)³))`,
an ordinary integral. -/
theorem s7l8_R2 {ν ψ : ℂ → ℂ} (hν : IsHarmonicU ν ψ) {z v : ℂ} (hz : z ∈ upperHalf) (hv : v ∈ upperHalf)
    (hvz : v ≠ z) :
    pv2 (fun x => ν x / ((z - x) ^ 2 * (x - conj v) ^ 2)) z v =
      (conj z - conj v) ^ 2 * ∫ x in upperHalf, ν x * (1 / ((x - conj v) ^ 2 * (z - conj v) ^ 2 * (x - conj z) ^ 2) +
        2 * ((z - conj z) / ((x - conj z) ^ 3 * (x - conj v) * (z - conj v) ^ 3))) := by
  have hU := measurableSet_upperHalf_aux
  have hzim : 0 < z.im := hz
  have hvim : 0 < v.im := hv
  obtain ⟨-, hB, hA⟩ := e64_t10_int hν hz hv
  obtain ⟨hI1, hfar⟩ := e64_t9_int hν hz hv
  have hne_v : ∀ x ∈ upperHalf, x - conj v ≠ 0 := fun x hx h => by
    have h' := congrArg Complex.im h
    have hx' : 0 < x.im := hx
    simp at h'
    linarith
  have hne_z : ∀ x ∈ upperHalf, x - conj z ≠ 0 := fun x hx h => by
    have h' := congrArg Complex.im h
    have hx' : 0 < x.im := hx
    simp at h'
    linarith
  have h3 : z - conj v ≠ 0 := hne_v z hz
  have h4 : conj z - conj v ≠ 0 := fun h => hvz (by
    have e := congrArg conj (sub_eq_zero.mp h); simp only [Complex.conj_conj] at e; exact e.symm)
  have hratio : ∀ x ∈ upperHalf, ‖(x - conj v) / (x - conj z)‖ ≤ 1 + ‖conj z - conj v‖ / z.im := by
    intro x hx
    have hxz : z.im ≤ ‖x - conj z‖ := by
      have := e64_t10_im (a := conj z) hx (by rw [Complex.conj_im]; linarith)
      rwa [Complex.conj_im, neg_neg] at this
    rw [show x - conj v = (x - conj z) + (conj z - conj v) by ring, add_div, div_self (hne_z x hx)]
    refine (norm_add_le _ _).trans ?_
    rw [norm_one, norm_div]
    gcongr
  have hI6 : IntegrableOn (fun x => ν x / ((x - conj z) ^ 3 * (x - conj v))) upperHalf := by
    have hm : AEStronglyMeasurable (fun x : ℂ => (x - conj v) / (x - conj z)) (volume.restrict upperHalf) :=
      ((measurable_id.sub_const _).aemeasurable.div (measurable_id.sub_const _).aemeasurable).aestronglyMeasurable
    have hb : ∀ᵐ x ∂(volume.restrict upperHalf), ‖(x - conj v) / (x - conj z)‖ ≤ 1 + ‖conj z - conj v‖ / z.im := by
      filter_upwards [ae_restrict_mem hU] with x hx
      exact hratio x hx
    refine (IntegrableOn.congr_fun (Integrable.bdd_mul hI1 hm hb) (fun x hx => ?_) hU)
    have e1 := hne_v x hx
    have e2 := hne_z x hx
    beta_reduce
    field_simp
  set c1 : ℂ := 1 / (z - conj v) ^ 2 with hc1
  set c2 : ℂ := 2 * ((z - conj z) / (z - conj v) ^ 3) with hc2
  have hH : IntegrableOn (fun x => ν x * (1 / ((x - conj v) ^ 2 * (z - conj v) ^ 2 * (x - conj z) ^ 2) +
      2 * ((z - conj z) / ((x - conj z) ^ 3 * (x - conj v) * (z - conj v) ^ 3)))) upperHalf := by
    refine IntegrableOn.congr_fun ((hI1.const_mul c1).add (hI6.const_mul c2)) (fun x hx => ?_) hU
    have e1 := hne_v x hx
    have e2 := hne_z x hx
    simp only [Pi.add_apply, hc1, hc2]
    field_simp
  set K3 : ℂ := (z - conj z) ^ 2 / (z - conj v) ^ 2 with hK3
  set K4 : ℂ := 2 * (z - conj z) ^ 2 * (conj z - conj v) / (z - conj v) ^ 3 with hK4
  have hpt : ∀ x ∈ upperHalf, x ≠ z → ν x / ((z - x) ^ 2 * (x - conj v) ^ 2) =
      (conj z - conj v) ^ 2 * (ν x * (1 / ((x - conj v) ^ 2 * (z - conj v) ^ 2 * (x - conj z) ^ 2) +
        2 * ((z - conj z) / ((x - conj z) ^ 3 * (x - conj v) * (z - conj v) ^ 3)))) +
      K3 * (ν x / ((x - z) ^ 2 * (x - conj z) ^ 2)) + K4 * (ν x / ((x - z) * (x - conj z) ^ 3)) := by
    intro x hx hxz
    have e1 := hne_v x hx
    have e2 := hne_z x hx
    have e5 : x - z ≠ 0 := sub_ne_zero.mpr hxz
    have e6 : z - x ≠ 0 := fun h => e5 (by linear_combination -h)
    simp only [hK3, hK4]
    field_simp
    ring
  have hfi : ∀ δ : ℝ, 0 < δ → IntegrableOn (fun x => ν x / ((z - x) ^ 2 * (x - conj v) ^ 2))
      (upperHalf \ ball z δ) := fun δ hδ =>
    (hfar δ hδ).congr_fun (fun x _ => by simp only [div_eq_mul_inv, one_mul, mul_inv, mul_assoc]) (hU.diff measurableSet_ball)
  have hpunct : ∀ δ : ℝ, upperHalfPunct z δ = upperHalf \ (ball z δ ∪ ball z δ) := fun δ => by
    rw [union_self]; rfl
  have hsplit : ∀ δ : ℝ, 0 < δ → (∫ x in upperHalf \ ball z δ, ν x / ((z - x) ^ 2 * (x - conj v) ^ 2)) =
      (conj z - conj v) ^ 2 * (∫ x in upperHalf \ ball z δ, ν x *
        (1 / ((x - conj v) ^ 2 * (z - conj v) ^ 2 * (x - conj z) ^ 2) +
          2 * ((z - conj z) / ((x - conj z) ^ 3 * (x - conj v) * (z - conj v) ^ 3)))) +
      K3 * (∫ x in upperHalfPunct z δ, ν x / ((x - z) ^ 2 * (x - conj z) ^ 2)) +
      K4 * ∫ x in upperHalf \ ball z δ, ν x / ((x - z) * (x - conj z) ^ 3) := by
    intro δ hδ
    have hPm : MeasurableSet (upperHalf \ ball z δ) := hU.diff measurableSet_ball
    have hsub : upperHalf \ ball z δ ⊆ upperHalf := sdiff_subset
    have i1 := (hH.mono_set hsub).const_mul ((conj z - conj v) ^ 2)
    have i2 : IntegrableOn (fun x => K3 * (ν x / ((x - z) ^ 2 * (x - conj z) ^ 2))) (upperHalf \ ball z δ) :=
      (hA δ hδ).const_mul K3
    have i3 := (hB.mono_set hsub).const_mul K4
    have i12 : IntegrableOn (fun x => (conj z - conj v) ^ 2 * (ν x *
        (1 / ((x - conj v) ^ 2 * (z - conj v) ^ 2 * (x - conj z) ^ 2) +
          2 * ((z - conj z) / ((x - conj z) ^ 3 * (x - conj v) * (z - conj v) ^ 3)))) +
        K3 * (ν x / ((x - z) ^ 2 * (x - conj z) ^ 2))) (upperHalf \ ball z δ) := i1.add i2
    rw [setIntegral_congr_fun hPm (fun x hx => hpt x hx.1 (fun h => hx.2 (by rw [h]; exact mem_ball_self hδ))),
      integral_add i12 i3, integral_add i1 i2, integral_const_mul, integral_const_mul, integral_const_mul]
    rfl
  have t1 : Tendsto (fun δ : ℝ => ∫ x in upperHalf \ ball z δ, ν x *
      (1 / ((x - conj v) ^ 2 * (z - conj v) ^ 2 * (x - conj z) ^ 2) +
        2 * ((z - conj z) / ((x - conj z) ^ 3 * (x - conj v) * (z - conj v) ^ 3)))) (𝓝[>] 0)
      (𝓝 (∫ x in upperHalf, ν x * (1 / ((x - conj v) ^ 2 * (z - conj v) ^ 2 * (x - conj z) ^ 2) +
        2 * ((z - conj z) / ((x - conj z) ^ 3 * (x - conj v) * (z - conj v) ^ 3))))) := by
    simpa only [union_self] using e124a_reg2 z z hH
  have t2 := eq_6_3 hν hz
  have t3 : Tendsto (fun δ : ℝ => ∫ x in upperHalf \ ball z δ, ν x / ((x - z) * (x - conj z) ^ 3)) (𝓝[>] 0)
      (𝓝 0) := by
    have h := e124a_reg2 z z hB
    rw [cor_1_15 hν hz] at h
    simpa only [union_self] using h
  have hlim := ((t1.const_mul ((conj z - conj v) ^ 2)).add (t2.const_mul K3)).add (t3.const_mul K4)
  simp only [mul_zero, add_zero] at hlim
  have hL : Tendsto (fun δ : ℝ => ∫ x in upperHalf \ ball z δ, ν x / ((z - x) ^ 2 * (x - conj v) ^ 2)) (𝓝[>] 0)
      (𝓝 ((conj z - conj v) ^ 2 * ∫ x in upperHalf, ν x *
        (1 / ((x - conj v) ^ 2 * (z - conj v) ^ 2 * (x - conj z) ^ 2) +
          2 * ((z - conj z) / ((x - conj z) ^ 3 * (x - conj v) * (z - conj v) ^ 3))))) := by
    refine hlim.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    exact (hsplit δ hδ).symm
  exact (s7l8_pv_drop hv hvz hfi hL).limUnder_eq

/-- **Off-support Beurling transform.** If `h ∈ L²` vanishes on an open `V`, then on `V` the (absolutely
convergent) integral `∫ h(ζ)/(ζ - v)²` is `-π H h(v)` a.e. -/
theorem s7l8_off_ae {h : ℂ → ℂ} (hm : Measurable h) (h2 : MemLp h 2 volume) {V : Set ℂ} (hV : IsOpen V)
    (h0 : ∀ x ∈ V, h x = 0) :
    ∀ᵐ v ∂(volume.restrict V), ∫ ζ, h ζ / (ζ - v) ^ 2 = -(π : ℂ) * hilbertH h v := by
  have hs : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) h V :=
    (contDiffOn_const (c := (0 : ℂ))).congr fun x hx => h0 x hx
  have hT : ∀ v ∈ V, Tendsto (fun r => ∫ ζ in {ζ | r < ‖ζ - v‖}, h ζ / (ζ - v) ^ 2) (𝓝[>] 0)
      (𝓝 (∫ ζ, h ζ / (ζ - v) ^ 2)) := by
    intro v hv
    obtain ⟨d, hd, hdV⟩ := Metric.isOpen_iff.1 hV v hv
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [Ioo_mem_nhdsGT hd] with r hr
    symm
    refine setIntegral_eq_integral_of_forall_compl_eq_zero fun ζ hζ => ?_
    have hζ' : ζ ∈ ball v d := by
      rw [mem_ball, dist_eq_norm]
      have : ¬ r < ‖ζ - v‖ := hζ
      linarith [hr.2]
    rw [h0 ζ (hdV hζ'), zero_div]
  have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 Real.pi_ne_zero
  filter_upwards [s7l8_hilbertH_local hm h2 hV hs hT] with v hv
  rw [hv]
  field_simp

/-- `L²` bound for the off-support Beurling transform: `∫_V |∫ h/(ζ - v)²|² ≤ π² ∫ |h|²`. -/
theorem s7l8_off_L2 {h : ℂ → ℂ} (hm : Measurable h) (h2 : MemLp h 2 volume) {V : Set ℂ} (hV : IsOpen V)
    (h0 : ∀ x ∈ V, h x = 0) :
    (∫⁻ v in V, ‖∫ ζ, h ζ / (ζ - v) ^ 2‖ₑ ^ 2) ≤ ENNReal.ofReal (π ^ 2) * ∫⁻ ζ, ‖h ζ‖ₑ ^ 2 := by
  have hae := s7l8_off_ae hm h2 hV h0
  have e : ∀ᵐ v ∂(volume.restrict V), ‖∫ ζ, h ζ / (ζ - v) ^ 2‖ₑ ^ 2 =
      ENNReal.ofReal (π ^ 2) * ‖hilbertH h v‖ₑ ^ 2 := by
    filter_upwards [hae] with v hv
    rw [hv, enorm_mul, mul_pow, enorm_neg, ← ofReal_norm (π : ℂ), Complex.norm_real,
      Real.norm_of_nonneg Real.pi_pos.le, ← ENNReal.ofReal_pow Real.pi_pos.le]
  rw [lintegral_congr_ae e, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine mul_le_mul_right ((setLIntegral_le_lintegral _ _).trans (le_of_eq ?_)) _
  have hiso := hilbertH_memLp_two h2
  have e1 := eLpNorm_nnreal_pow_eq_lintegral (p := 2) (by norm_num) hiso.1.aestronglyMeasurable
  have e2 := eLpNorm_nnreal_pow_eq_lintegral (p := 2) (by norm_num) h2.aestronglyMeasurable
  simp only [NNReal.coe_ofNat, ENNReal.coe_ofNat] at e1 e2
  rw [hiso.2] at e1
  have e3 : (∫⁻ x, ‖hilbertH h x‖ₑ ^ (2 : ℝ)) = ∫⁻ x, ‖hilbertH h x‖ₑ ^ (2 : ℕ) :=
    lintegral_congr fun x => by rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, ENNReal.rpow_natCast]
  have e4 : (∫⁻ x, ‖h x‖ₑ ^ (2 : ℝ)) = ∫⁻ x, ‖h x‖ₑ ^ (2 : ℕ) :=
    lintegral_congr fun x => by rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, ENNReal.rpow_natCast]
  exact e3.symm.trans ((e1.symm.trans e2).trans e4)

/-- `1_𝕌 ν/(· - z̄)³`: measurable, `L²`, `∫ |·|² ≤ M² π/(Im z)⁴`. -/
theorem s7l8_g3_data {ν ψ : ℂ → ℂ} (hν : IsHarmonicU ν ψ) {M : ℝ} (hM : ∀ v ∈ upperHalf, ‖ν v‖ ≤ M)
    {z : ℂ} (hz : z ∈ upperHalf) :
    Measurable (upperHalf.indicator fun v => ν v / (v - conj z) ^ 3) ∧
      MemLp (upperHalf.indicator fun v => ν v / (v - conj z) ^ 3) 2 volume ∧
      (∫⁻ v, ‖upperHalf.indicator (fun v => ν v / (v - conj z) ^ 3) v‖ₑ ^ 2) ≤
        ENNReal.ofReal (M ^ 2 * (π / z.im ^ 2) / z.im ^ 2) := by
  have hU := measurableSet_upperHalf_aux
  have hzim : 0 < z.im := hz
  have hne : ∀ v ∈ upperHalf, v - conj z ≠ 0 := fun v hv h => by
    have := congrArg Complex.im h
    simp only [Complex.sub_im, Complex.conj_im, Complex.zero_im] at this
    have : 0 < v.im := hv
    linarith
  have hνc := harmonicU_continuousOn hν
  have hF : ContinuousOn (fun v => ν v / (v - conj z) ^ 3) upperHalf :=
    hνc.div (by fun_prop) fun v hv => pow_ne_zero 3 (hne v hv)
  set g := upperHalf.indicator fun v => ν v / (v - conj z) ^ 3 with hgd
  have hgm : Measurable g := by
    rw [hgd, ← Set.piecewise_eq_indicator]
    exact hF.measurable_piecewise continuousOn_const hU
  set S : Set ℂ := {w : ℂ | z.im ≤ ‖w - conj z‖} with hSd
  have hS : MeasurableSet S := measurableSet_le measurable_const (measurable_id.sub_const _).norm
  obtain ⟨hSi, hSv⟩ := Ch2.s2c_l4_outside_ball (conj z) hzim
  have hUS : upperHalf ⊆ S := by
    intro v hv
    show z.im ≤ ‖v - conj z‖
    have h1 := Complex.abs_im_le_norm (v - conj z)
    have h2 : (v - conj z).im = v.im + z.im := by simp
    have : 0 < v.im := hv
    rw [h2, abs_of_pos (by linarith)] at h1
    linarith
  have hpt : ∀ v, ‖g v‖ ^ 2 ≤ M ^ 2 / z.im ^ 2 * S.indicator (fun w : ℂ => (‖w - conj z‖ ^ 4)⁻¹) v := by
    intro v
    by_cases hv : v ∈ upperHalf
    · rw [hgd, Set.indicator_of_mem hv, Set.indicator_of_mem (hUS hv), norm_div, norm_pow, div_pow]
      have hp : 0 < ‖v - conj z‖ := norm_pos_iff.2 (hne v hv)
      have hd : z.im ≤ ‖v - conj z‖ := hUS hv
      have hM0 : 0 ≤ ‖ν v‖ := norm_nonneg _
      have h1 : ‖ν v‖ ^ 2 ≤ M ^ 2 := pow_le_pow_left₀ hM0 (hM v hv) 2
      have h2 : z.im ^ 2 * ‖v - conj z‖ ^ 4 ≤ (‖v - conj z‖ ^ 3) ^ 2 := by
        have : z.im ^ 2 ≤ ‖v - conj z‖ ^ 2 := pow_le_pow_left₀ hzim.le hd 2
        nlinarith [pow_pos hp 4]
      rw [div_le_iff₀ (by positivity)]
      calc ‖ν v‖ ^ 2 ≤ M ^ 2 := h1
        _ = M ^ 2 / z.im ^ 2 * (‖v - conj z‖ ^ 4)⁻¹ * (z.im ^ 2 * ‖v - conj z‖ ^ 4) := by field_simp
        _ ≤ M ^ 2 / z.im ^ 2 * (‖v - conj z‖ ^ 4)⁻¹ * (‖v - conj z‖ ^ 3) ^ 2 :=
            mul_le_mul_of_nonneg_left h2 (by positivity)
    · rw [hgd, Set.indicator_of_notMem hv, norm_zero]
      have : 0 ≤ S.indicator (fun w : ℂ => (‖w - conj z‖ ^ 4)⁻¹) v :=
        Set.indicator_nonneg (fun w _ => by positivity) v
      have : 0 ≤ M ^ 2 / z.im ^ 2 := by positivity
      nlinarith
  have hmaj : Integrable (fun v => M ^ 2 / z.im ^ 2 * S.indicator (fun w : ℂ => (‖w - conj z‖ ^ 4)⁻¹) v) :=
    (hSi.integrable_indicator hS).const_mul _
  have hsq : Integrable (fun v => ‖g v‖ ^ 2) :=
    hmaj.mono' ((hgm.norm.pow_const 2).aestronglyMeasurable) (Eventually.of_forall fun v => by
      rw [Real.norm_of_nonneg (by positivity)]; exact hpt v)
  have hg2 : MemLp g 2 volume := (memLp_two_iff_integrable_sq_norm hgm.aestronglyMeasurable).2 hsq
  refine ⟨hgm, hg2, ?_⟩
  calc (∫⁻ v, ‖g v‖ₑ ^ 2) = ∫⁻ v, ENNReal.ofReal (‖g v‖ ^ 2) := by
        refine lintegral_congr fun v => ?_
        rw [← ofReal_norm, ENNReal.ofReal_pow (norm_nonneg _)]
    _ ≤ ∫⁻ v, ENNReal.ofReal (M ^ 2 / z.im ^ 2 * S.indicator (fun w : ℂ => (‖w - conj z‖ ^ 4)⁻¹) v) :=
        lintegral_mono fun v => ENNReal.ofReal_le_ofReal (hpt v)
    _ = ENNReal.ofReal (∫ v, M ^ 2 / z.im ^ 2 * S.indicator (fun w : ℂ => (‖w - conj z‖ ^ 4)⁻¹) v) :=
        (ofReal_integral_eq_lintegral_ofReal hmaj (Eventually.of_forall fun v =>
          mul_nonneg (by positivity) (Set.indicator_nonneg (fun w _ => by positivity) v))).symm
    _ = ENNReal.ofReal (M ^ 2 * (π / z.im ^ 2) / z.im ^ 2) := by
        rw [integral_const_mul, integral_indicator hS, hSv]
        congr 1
        ring

/-- **Second-variable form of `D₁`**: for `v ≠ z` in `𝕌`, `D₁(z, v)` is a combination of the off-support
transforms `B_k(ζ) = ∫ 1_𝕌 ν/(· - z̄)^k /(· - ζ)²` at `ζ = v̄` (from `s7l8_R2`). -/
theorem s7l8_Dsnd_eq {ν ψ : ℂ → ℂ} (hν : IsHarmonicU ν ψ) {z v : ℂ} (hz : z ∈ upperHalf) (hv : v ∈ upperHalf)
    (hvz : v ≠ z) :
    dz (fun e => kernelKbar (fun y => e * ν y) z v) 0 = -(1 / π) * (conj z - conj v) ^ 2 *
      ((1 / (z - conj v) ^ 2 + 2 * (z - conj z) / (z - conj v) ^ 3) *
          (∫ x, upperHalf.indicator (fun x => ν x / (x - conj z) ^ 2) x / (x - conj v) ^ 2) +
        2 * (z - conj z) * (conj z - conj v) / (z - conj v) ^ 3 *
          (∫ x, upperHalf.indicator (fun x => ν x / (x - conj z) ^ 3) x / (x - conj v) ^ 2)) := by
  have hU := measurableSet_upperHalf_aux
  have hzim : 0 < z.im := hz
  have hvim : 0 < v.im := hv
  obtain ⟨hI1, -⟩ := e64_t9_int hν hz hv
  have hne_v : ∀ x ∈ upperHalf, x - conj v ≠ 0 := fun x hx h => by
    have h' := congrArg Complex.im h
    have hx' : 0 < x.im := hx
    simp at h'
    linarith
  have hne_z : ∀ x ∈ upperHalf, x - conj z ≠ 0 := fun x hx h => by
    have h' := congrArg Complex.im h
    have hx' : 0 < x.im := hx
    simp at h'
    linarith
  have h3 : z - conj v ≠ 0 := hne_v z hz
  have hI3 : IntegrableOn (fun x => ν x / ((x - conj v) ^ 2 * (x - conj z) ^ 3)) upperHalf := by
    have hm : AEStronglyMeasurable (fun x : ℂ => 1 / (x - conj z)) (volume.restrict upperHalf) :=
      (measurable_const.div (measurable_id.sub_const _)).aestronglyMeasurable
    have hb : ∀ᵐ x ∂(volume.restrict upperHalf), ‖1 / (x - conj z)‖ ≤ 1 / z.im := by
      filter_upwards [ae_restrict_mem hU] with x hx
      have hxz : z.im ≤ ‖x - conj z‖ := by
        have := e64_t10_im (a := conj z) hx (by rw [Complex.conj_im]; linarith)
        rwa [Complex.conj_im, neg_neg] at this
      rw [norm_div, norm_one]
      exact one_div_le_one_div_of_le hzim hxz
    refine (IntegrableOn.congr_fun (Integrable.bdd_mul hI1 hm hb) (fun x hx => ?_) hU)
    have e1 := hne_v x hx
    have e2 := hne_z x hx
    beta_reduce
    field_simp
  have hR := s7l8_R2 hν hz hv hvz
  have hind : ∀ k : ℕ, (∫ x in upperHalf, ν x / ((x - conj v) ^ 2 * (x - conj z) ^ k)) =
      ∫ x, upperHalf.indicator (fun x => ν x / (x - conj z) ^ k) x / (x - conj v) ^ 2 := by
    intro k
    rw [← integral_indicator hU]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    by_cases hx : x ∈ upperHalf
    · simp only [Set.indicator_of_mem hx]
      rw [div_div, mul_comm]
    · simp only [Set.indicator_of_notMem hx, zero_div]
  have hsplit : (∫ x in upperHalf, ν x * (1 / ((x - conj v) ^ 2 * (z - conj v) ^ 2 * (x - conj z) ^ 2) +
      2 * ((z - conj z) / ((x - conj z) ^ 3 * (x - conj v) * (z - conj v) ^ 3)))) =
      (1 / (z - conj v) ^ 2 + 2 * (z - conj z) / (z - conj v) ^ 3) *
          (∫ x in upperHalf, ν x / ((x - conj v) ^ 2 * (x - conj z) ^ 2)) +
        2 * (z - conj z) * (conj z - conj v) / (z - conj v) ^ 3 *
          (∫ x in upperHalf, ν x / ((x - conj v) ^ 2 * (x - conj z) ^ 3)) := by
    rw [← integral_const_mul, ← integral_const_mul, ← integral_add (hI1.const_mul _) (hI3.const_mul _)]
    refine setIntegral_congr_fun hU fun x hx => ?_
    have e1 := hne_v x hx
    have e2 := hne_z x hx
    beta_reduce
    field_simp
    ring
  rw [s7l8_D1_formula hν hz hv, hR, hsplit, hind 2, hind 3]
  ring

/-- Measurability of a parameter integral `ζ ↦ ∫ h(x)/(x - ζ)²`. -/
theorem s7l8_B_meas {h : ℂ → ℂ} (hm : Measurable h) : Measurable fun ζ : ℂ => ∫ x, h x / (x - ζ) ^ 2 := by
  have hF : Measurable (fun p : ℂ × ℂ => h p.2 / (p.2 - p.1) ^ 2) :=
    (hm.comp measurable_snd).div ((measurable_snd.sub measurable_fst).pow_const 2)
  exact (hF.stronglyMeasurable.integral_prod_right' (ν := volume)).measurable

/-- Conjugation carries `𝕌` onto the lower half-plane: `∫_𝕌 F(v̄) = ∫_𝕃 F`. -/
theorem s7l8_conj_lint (F : ℂ → ℝ≥0∞) :
    ∫⁻ v in upperHalf, F (conj v) = ∫⁻ ζ in {ζ : ℂ | ζ.im < 0}, F ζ := by
  have hLm : MeasurableSet {ζ : ℂ | ζ.im < 0} := measurableSet_lt Complex.measurable_im measurable_const
  have hpre : (fun v : ℂ => conj v) ⁻¹' {ζ : ℂ | ζ.im < 0} = upperHalf := by
    ext v
    simp [upperHalf]
  have hmp : MeasurePreserving (fun v : ℂ => conj v) (volume.restrict upperHalf)
      (volume.restrict {ζ : ℂ | ζ.im < 0}) := by
    have := gzE_conj_measurePreserving.restrict_preimage hLm
    rwa [hpre] at this
  have hemb : MeasurableEmbedding (fun v : ℂ => conj v) := Complex.conjCLE.toHomeomorph.measurableEmbedding
  exact hmp.lintegral_comp_emb hemb F

/-- **`D₁` in its second variable is `L²`**: `∫_𝕌 |D₁(z, v)|² d²v ≤ 82 π M²/(Im z)²` (`s7l8_Dsnd_eq`, off-support
Beurling bounds on the lower half-plane). -/
theorem s7l8_Dsnd_L2 {ν ψ : ℂ → ℂ} (hν : IsHarmonicU ν ψ) {M : ℝ} (hM : ∀ v ∈ upperHalf, ‖ν v‖ ≤ M)
    {z : ℂ} (hz : z ∈ upperHalf) :
    (∫⁻ v in upperHalf, ‖dz (fun e => kernelKbar (fun y => e * ν y) z v) 0‖ₑ ^ 2) ≤
      ENNReal.ofReal (82 * π * M ^ 2 / z.im ^ 2) := by
  have hU := measurableSet_upperHalf_aux
  have hzim : 0 < z.im := hz
  have hπ := Real.pi_pos
  obtain ⟨h2m, -, h22, h2b⟩ := s7l8_g_data hν hM hz
  obtain ⟨h3m, h32, h3b⟩ := s7l8_g3_data hν hM hz
  set h2 := upperHalf.indicator fun x => ν x / (x - conj z) ^ 2 with hh2
  set h3 := upperHalf.indicator fun x => ν x / (x - conj z) ^ 3 with hh3
  set B2 : ℂ → ℂ := fun ζ => ∫ x, h2 x / (x - ζ) ^ 2 with hB2
  set B3 : ℂ → ℂ := fun ζ => ∫ x, h3 x / (x - ζ) ^ 2 with hB3
  have hLo : IsOpen {ζ : ℂ | ζ.im < 0} := isOpen_lt Complex.continuous_im continuous_const
  have h20 : ∀ x ∈ {ζ : ℂ | ζ.im < 0}, h2 x = 0 := fun x hx => by
    rw [hh2]
    refine Set.indicator_of_notMem (fun h => ?_) _
    have h1 : 0 < x.im := h
    have h2' : x.im < 0 := hx
    linarith
  have h30 : ∀ x ∈ {ζ : ℂ | ζ.im < 0}, h3 x = 0 := fun x hx => by
    rw [hh3]
    refine Set.indicator_of_notMem (fun h => ?_) _
    have h1 : 0 < x.im := h
    have h2' : x.im < 0 := hx
    linarith
  have hL2 := s7l8_off_L2 h2m h22 hLo h20
  have hL3 := s7l8_off_L2 h3m h32 hLo h30
  -- the pointwise bound
  have hpt : ∀ v ∈ upperHalf, v ≠ z → ‖dz (fun e => kernelKbar (fun y => e * ν y) z v) 0‖ₑ ^ 2 ≤
      ENNReal.ofReal (50 / π ^ 2) * ‖B2 (conj v)‖ₑ ^ 2 +
        ENNReal.ofReal (32 * z.im ^ 2 / π ^ 2) * ‖B3 (conj v)‖ₑ ^ 2 := by
    intro v hv hvz
    have hvim : 0 < v.im := hv
    have hd : z.im ≤ ‖z - conj v‖ := by
      have h1 := Complex.abs_im_le_norm (z - conj v)
      have h2 : (z - conj v).im = z.im + v.im := by simp
      rw [h2, abs_of_pos (by linarith)] at h1
      linarith
    have hdp : 0 < ‖z - conj v‖ := lt_of_lt_of_le hzim hd
    have he : ‖conj z - conj v‖ ≤ ‖z - conj v‖ := by
      rw [← map_sub, Complex.norm_conj, Complex.norm_eq_sqrt_sq_add_sq, Complex.norm_eq_sqrt_sq_add_sq]
      refine Real.sqrt_le_sqrt ?_
      simp only [Complex.sub_re, Complex.sub_im, Complex.conj_re, Complex.conj_im]
      nlinarith
    have hzz : ‖z - conj z‖ = 2 * z.im := by
      rw [Complex.sub_conj, norm_mul, Complex.norm_real, Complex.norm_I, Real.norm_of_nonneg (by positivity), mul_one]
    set d := ‖z - conj v‖ with hdd
    set w := ‖conj z - conj v‖ with hwd
    have hw0 : 0 ≤ w := norm_nonneg _
    have hα : ‖(conj z - conj v) ^ 2 * (1 / (z - conj v) ^ 2 + 2 * (z - conj z) / (z - conj v) ^ 3)‖ ≤ 5 := by
      have h1 : ‖(conj z - conj v) ^ 2 * (1 / (z - conj v) ^ 2 + 2 * (z - conj z) / (z - conj v) ^ 3)‖ ≤
          w ^ 2 * (1 / d ^ 2 + 2 * (2 * z.im) / d ^ 3) := by
        rw [norm_mul, norm_pow]
        refine mul_le_mul_of_nonneg_left ((norm_add_le _ _).trans (le_of_eq ?_)) (by positivity)
        rw [norm_div, norm_div, norm_one, norm_pow, norm_mul, hzz, norm_pow, Complex.norm_ofNat]
      refine h1.trans ?_
      have hwd' : w ^ 2 ≤ d ^ 2 := pow_le_pow_left₀ hw0 he 2
      have e1 : w ^ 2 * (1 / d ^ 2 + 2 * (2 * z.im) / d ^ 3) ≤ d ^ 2 * (1 / d ^ 2 + 2 * (2 * z.im) / d ^ 3) :=
        mul_le_mul_of_nonneg_right hwd' (by positivity)
      have e2 : d ^ 2 * (1 / d ^ 2 + 2 * (2 * z.im) / d ^ 3) = 1 + 4 * (z.im / d) := by
        field_simp
        ring
      have e3 : z.im / d ≤ 1 := (div_le_one hdp).2 hd
      linarith
    have hβ : ‖(conj z - conj v) ^ 2 * (2 * (z - conj z) * (conj z - conj v) / (z - conj v) ^ 3)‖ ≤ 4 * z.im := by
      rw [norm_mul, norm_pow, norm_div, norm_mul, norm_mul, norm_pow, Complex.norm_ofNat, hzz]
      have hw3 : w ^ 3 ≤ d ^ 3 := pow_le_pow_left₀ hw0 he 3
      have : w ^ 2 * (2 * (2 * z.im) * w / d ^ 3) = 4 * z.im * (w ^ 3 / d ^ 3) := by ring
      rw [this]
      have : w ^ 3 / d ^ 3 ≤ 1 := (div_le_one (by positivity)).2 hw3
      nlinarith
    have heq := s7l8_Dsnd_eq hν hz hv hvz
    have hn : ‖dz (fun e => kernelKbar (fun y => e * ν y) z v) 0‖ ≤
        1 / π * (5 * ‖B2 (conj v)‖ + 4 * z.im * ‖B3 (conj v)‖) := by
      rw [heq]
      have hr : -(1 / π : ℂ) * (conj z - conj v) ^ 2 *
          ((1 / (z - conj v) ^ 2 + 2 * (z - conj z) / (z - conj v) ^ 3) * B2 (conj v) +
            2 * (z - conj z) * (conj z - conj v) / (z - conj v) ^ 3 * B3 (conj v)) =
          -(1 / π : ℂ) * (((conj z - conj v) ^ 2 * (1 / (z - conj v) ^ 2 + 2 * (z - conj z) / (z - conj v) ^ 3)) *
            B2 (conj v) + ((conj z - conj v) ^ 2 * (2 * (z - conj z) * (conj z - conj v) / (z - conj v) ^ 3)) *
              B3 (conj v)) := by ring
      rw [hr, norm_mul, norm_neg, norm_div, norm_one, Complex.norm_real, Real.norm_of_nonneg hπ.le]
      refine mul_le_mul_of_nonneg_left ((norm_add_le _ _).trans ?_) (by positivity)
      exact add_le_add ((norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right hα (norm_nonneg _)))
        ((norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right hβ (norm_nonneg _)))
    have hsq : ‖dz (fun e => kernelKbar (fun y => e * ν y) z v) 0‖ ^ 2 ≤
        50 / π ^ 2 * ‖B2 (conj v)‖ ^ 2 + 32 * z.im ^ 2 / π ^ 2 * ‖B3 (conj v)‖ ^ 2 := by
      have h0 : 0 ≤ ‖dz (fun e => kernelKbar (fun y => e * ν y) z v) 0‖ := norm_nonneg _
      have h1 := pow_le_pow_left₀ h0 hn 2
      refine h1.trans ?_
      have ha := norm_nonneg (B2 (conj v))
      have hb := norm_nonneg (B3 (conj v))
      have : (1 / π * (5 * ‖B2 (conj v)‖ + 4 * z.im * ‖B3 (conj v)‖)) ^ 2 =
          (25 * ‖B2 (conj v)‖ ^ 2 + 40 * z.im * ‖B2 (conj v)‖ * ‖B3 (conj v)‖ +
            16 * z.im ^ 2 * ‖B3 (conj v)‖ ^ 2) / π ^ 2 := by
        field_simp
        ring
      rw [this, div_le_iff₀ (by positivity)]
      have : 50 / π ^ 2 * ‖B2 (conj v)‖ ^ 2 + 32 * z.im ^ 2 / π ^ 2 * ‖B3 (conj v)‖ ^ 2 =
          (50 * ‖B2 (conj v)‖ ^ 2 + 32 * z.im ^ 2 * ‖B3 (conj v)‖ ^ 2) / π ^ 2 := by ring
      rw [this, div_mul_cancel₀ _ (by positivity)]
      nlinarith [sq_nonneg (5 * ‖B2 (conj v)‖ - 4 * z.im * ‖B3 (conj v)‖)]
    calc ‖dz (fun e => kernelKbar (fun y => e * ν y) z v) 0‖ₑ ^ 2
        = ENNReal.ofReal (‖dz (fun e => kernelKbar (fun y => e * ν y) z v) 0‖ ^ 2) := by
          rw [← ofReal_norm, ENNReal.ofReal_pow (norm_nonneg _)]
      _ ≤ ENNReal.ofReal (50 / π ^ 2 * ‖B2 (conj v)‖ ^ 2 + 32 * z.im ^ 2 / π ^ 2 * ‖B3 (conj v)‖ ^ 2) :=
          ENNReal.ofReal_le_ofReal hsq
      _ = _ := by
          rw [ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_mul (by positivity),
            ENNReal.ofReal_mul (by positivity), ← ofReal_norm, ← ofReal_norm, ENNReal.ofReal_pow (norm_nonneg _),
            ENNReal.ofReal_pow (norm_nonneg _)]
  have hne : ∀ᵐ v ∂(volume.restrict upperHalf), v ≠ z :=
    ae_restrict_of_ae (by simp [ae_iff, measure_singleton])
  have hB2m : Measurable fun v => B2 (conj v) := (s7l8_B_meas h2m).comp Complex.continuous_conj.measurable
  calc (∫⁻ v in upperHalf, ‖dz (fun e => kernelKbar (fun y => e * ν y) z v) 0‖ₑ ^ 2)
      ≤ ∫⁻ v in upperHalf, (ENNReal.ofReal (50 / π ^ 2) * ‖B2 (conj v)‖ₑ ^ 2 +
          ENNReal.ofReal (32 * z.im ^ 2 / π ^ 2) * ‖B3 (conj v)‖ₑ ^ 2) := by
        refine lintegral_mono_ae ?_
        filter_upwards [ae_restrict_mem hU, hne] with v hv hvz
        exact hpt v hv hvz
    _ = ENNReal.ofReal (50 / π ^ 2) * (∫⁻ v in upperHalf, ‖B2 (conj v)‖ₑ ^ 2) +
          ENNReal.ofReal (32 * z.im ^ 2 / π ^ 2) * ∫⁻ v in upperHalf, ‖B3 (conj v)‖ₑ ^ 2 := by
        rw [lintegral_add_left' (((hB2m.enorm.pow_const 2).const_mul (ENNReal.ofReal (50 / π ^ 2))).aemeasurable),
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ ≤ ENNReal.ofReal (50 / π ^ 2) * (ENNReal.ofReal (π ^ 2) * ENNReal.ofReal (M ^ 2 * (π / z.im ^ 2))) +
          ENNReal.ofReal (32 * z.im ^ 2 / π ^ 2) *
            (ENNReal.ofReal (π ^ 2) * ENNReal.ofReal (M ^ 2 * (π / z.im ^ 2) / z.im ^ 2)) := by
        rw [s7l8_conj_lint (fun ζ => ‖B2 ζ‖ₑ ^ 2), s7l8_conj_lint (fun ζ => ‖B3 ζ‖ₑ ^ 2)]
        gcongr
        · exact hL2.trans (mul_le_mul_right h2b _)
        · exact hL3.trans (mul_le_mul_right h3b _)
    _ = ENNReal.ofReal (82 * π * M ^ 2 / z.im ^ 2) := by
        rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        field_simp
        ring

/-- The off-support transforms `B_k(ζ) = ∫ 1_𝕌 ν/(· - z̄)^k /(· - ζ)²` (`k ≥ 2`) are holomorphic on the lower
half-plane (`s7g_f2_param`, majorant `(1 + |x|)⁻⁴`). -/
theorem s7l8_B_holo {ν ψ : ℂ → ℂ} (hν : IsHarmonicU ν ψ) {z : ℂ} (hz : z ∈ upperHalf) {k : ℕ} (hk : 2 ≤ k) :
    DifferentiableOn ℂ (fun ζ => ∫ x, upperHalf.indicator (fun x => ν x / (x - conj z) ^ k) x / (x - ζ) ^ 2)
      {ζ : ℂ | ζ.im < 0} := by
  obtain ⟨Mν, hMν0, hMν⟩ := harmonicU_bounded hν
  have hνc := harmonicU_continuousOn hν
  have hU := measurableSet_upperHalf_aux
  have hzim : 0 < z.im := hz
  have hind : (fun ζ => ∫ x, upperHalf.indicator (fun x => ν x / (x - conj z) ^ k) x / (x - ζ) ^ 2) =
      fun ζ => ∫ x in upperHalf, ν x / (x - conj z) ^ k / (x - ζ) ^ 2 := by
    funext ζ
    rw [← integral_indicator hU]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    by_cases hx : x ∈ upperHalf
    · simp only [Set.indicator_of_mem hx]
    · simp only [Set.indicator_of_notMem hx, zero_div]
  rw [hind]
  intro ζ0 hζ0
  have hζ0' : ζ0.im < 0 := hζ0
  set R : ℝ := -ζ0.im / 2 with hRd
  have hR : 0 < R := by rw [hRd]; linarith
  have him : ∀ a ∈ closedBall ζ0 R, a.im ≤ -R := by
    intro a ha
    have h1 : |a.im - ζ0.im| ≤ ‖a - ζ0‖ := by rw [← Complex.sub_im]; exact Complex.abs_im_le_norm _
    have h2 := (abs_le.mp h1).2
    have h3 : ‖a - ζ0‖ ≤ R := by rw [← dist_eq_norm]; exact ha
    rw [hRd] at h3 ⊢
    linarith
  have hne_a : ∀ a ∈ closedBall ζ0 R, ∀ x ∈ upperHalf, x - a ≠ 0 := fun a ha x hx h => by
    have h' := congrArg Complex.im h
    have hx' : 0 < x.im := hx
    have := him a ha
    simp only [Complex.sub_im, Complex.zero_im] at h'
    linarith
  have hne_z : ∀ x ∈ upperHalf, x - conj z ≠ 0 := fun x hx h => by
    have h' := congrArg Complex.im h
    have hx' : 0 < x.im := hx
    simp at h'
    linarith
  have hc : ContinuousOn (fun p : ℂ × ℂ => ν p.2 / (p.2 - conj z) ^ k / (p.2 - p.1) ^ 2)
      (closedBall ζ0 R ×ˢ upperHalf) := by
    refine ((hνc.comp continuous_snd.continuousOn fun p hp => hp.2).div ?_ ?_).div ?_ ?_
    · exact ((continuous_snd.sub continuous_const).pow k).continuousOn
    · exact fun p hp => pow_ne_zero k (hne_z p.2 hp.2)
    · exact ((continuous_snd.sub continuous_fst).pow 2).continuousOn
    · exact fun p hp => pow_ne_zero 2 (hne_a p.1 hp.1 p.2 hp.2)
  have hhol : ∀ x ∈ upperHalf, DifferentiableOn ℂ (fun a => ν x / (x - conj z) ^ k / (x - a) ^ 2) (ball ζ0 R) :=
    fun x hx => (differentiableOn_const _).div ((differentiableOn_const _).sub differentiableOn_id |>.pow 2)
      fun a ha => pow_ne_zero 2 (hne_a a (ball_subset_closedBall ha) x hx)
  -- the uniform majorant
  set ca : ℝ := R / (1 + ‖ζ0‖ + 2 * R) with hcad
  have hca : 0 < ca := by rw [hcad]; have := norm_nonneg ζ0; exact div_pos hR (by linarith)
  set cb : ℝ := z.im / (1 + ‖conj z‖ + z.im) with hcbd
  have hcb : 0 < cb := by rw [hcbd]; have := norm_nonneg (conj z); exact div_pos hzim (by linarith)
  have hla : ∀ a ∈ closedBall ζ0 R, ∀ x ∈ upperHalf, ca * (1 + ‖x‖) ≤ ‖x - a‖ := by
    intro a ha x hx
    have h1 : R ≤ ‖x - a‖ := by
      have := e64_t10_im (u := x) (a := a) hx (by have := him a ha; linarith)
      have := him a ha
      linarith
    have h2 := e64_t10_lower hR h1
    have hna : ‖a‖ ≤ ‖ζ0‖ + R := by
      have := norm_le_norm_add_norm_sub' a ζ0
      have h3 : ‖a - ζ0‖ ≤ R := by rw [← dist_eq_norm]; exact ha
      linarith
    refine le_trans ?_ h2
    refine mul_le_mul_of_nonneg_right ?_ (by positivity)
    rw [hcad]
    exact div_le_div_of_nonneg_left hR.le (by positivity) (by linarith)
  have hlb : ∀ x ∈ upperHalf, cb * (1 + ‖x‖) ≤ ‖x - conj z‖ := by
    intro x hx
    have h1 : z.im ≤ ‖x - conj z‖ := by
      have := e64_t10_im (u := x) (a := conj z) hx (by rw [Complex.conj_im]; linarith)
      rwa [Complex.conj_im, neg_neg] at this
    exact e64_t10_lower hzim h1
  set K : ℝ := Mν * (ca ^ 2 * cb ^ k)⁻¹ with hKd
  have hmaj := (e64_t5_maj 0).1
  simp only [sub_zero] at hmaj
  have hpt : ∀ a ∈ closedBall ζ0 R, ∀ x ∈ upperHalf,
      ‖ν x / (x - conj z) ^ k / (x - a) ^ 2‖ ≤ K * ((1 + ‖x‖) ^ 4)⁻¹ := by
    intro a ha x hx
    have r := e64_t10_rat hca hcb (hla a ha x hx) (hlb x hx) 2 k
    have e : ν x / (x - conj z) ^ k / (x - a) ^ 2 = ν x * (1 / ((x - a) ^ 2 * (x - conj z) ^ k)) := by
      rw [div_div, mul_comm ((x - conj z) ^ k), div_eq_mul_one_div]
    have h4 : ((1 + ‖x‖) ^ (2 + k))⁻¹ ≤ ((1 + ‖x‖) ^ 4)⁻¹ :=
      inv_anti₀ (by positivity) (pow_le_pow_right₀ (by linarith [norm_nonneg x]) (by omega))
    rw [e, norm_mul]
    calc ‖ν x‖ * ‖1 / ((x - a) ^ 2 * (x - conj z) ^ k)‖
        ≤ Mν * ((ca ^ 2 * cb ^ k)⁻¹ * ((1 + ‖x‖) ^ (2 + k))⁻¹) :=
          mul_le_mul (hMν x hx) r (norm_nonneg _) hMν0
      _ ≤ Mν * ((ca ^ 2 * cb ^ k)⁻¹ * ((1 + ‖x‖) ^ 4)⁻¹) := by gcongr
      _ = K * ((1 + ‖x‖) ^ 4)⁻¹ := by rw [hKd]; ring
  have hMb : ∀ a ∈ closedBall ζ0 R, ∫⁻ x in upperHalf, ‖ν x / (x - conj z) ^ k / (x - a) ^ 2‖ₑ ≤
      ENNReal.ofReal (∫ x : ℂ, K * ((1 + ‖x‖) ^ 4)⁻¹) := by
    intro a ha
    rw [ofReal_integral_eq_lintegral_ofReal (hmaj.const_mul K)
      (Eventually.of_forall fun x => by positivity)]
    calc ∫⁻ x in upperHalf, ‖ν x / (x - conj z) ^ k / (x - a) ^ 2‖ₑ
        ≤ ∫⁻ x in upperHalf, ENNReal.ofReal (K * ((1 + ‖x‖) ^ 4)⁻¹) :=
          setLIntegral_mono' hU fun x hx => by
            rw [← ofReal_norm]
            exact ENNReal.ofReal_le_ofReal (hpt a ha x hx)
      _ ≤ _ := setLIntegral_le_lintegral _ _
  have hd := s7g_f2_param (m := volume) hU hc hhol hMb
  exact ((hd ζ0 (mem_ball_self hR)).differentiableAt (isOpen_ball.mem_nhds (mem_ball_self hR))).differentiableWithinAt

/-- **Smoothness of `v ↦ \overline{D₁(z, v)}` on `𝕌 ∖ {z}`** (antiholomorphic in `v` by `s7l8_Dsnd_eq`). -/
theorem s7l8_Dsnd_smooth {ν ψ : ℂ → ℂ} (hν : IsHarmonicU ν ψ) {z : ℂ} (hz : z ∈ upperHalf) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun v => conj (dz (fun e => kernelKbar (fun y => e * ν y) z v) 0))
      (upperHalf \ {z}) := by
  have hzim : 0 < z.im := hz
  set L : Set ℂ := {ζ : ℂ | ζ.im < 0} with hLd
  have hLo : IsOpen L := isOpen_lt Complex.continuous_im continuous_const
  have hzne : ∀ ζ ∈ L, z - ζ ≠ 0 := fun ζ hζ h => by
    have h' := congrArg Complex.im h
    have : ζ.im < 0 := hζ
    simp only [Complex.sub_im, Complex.zero_im] at h'
    linarith
  have hB2 := s7l8_B_holo hν hz (k := 2) le_rfl
  have hB3 := s7l8_B_holo hν hz (k := 3) (by norm_num)
  set G : ℂ → ℂ := fun ζ => -(1 / π) * (conj z - ζ) ^ 2 *
      ((1 / (z - ζ) ^ 2 + 2 * (z - conj z) / (z - ζ) ^ 3) *
          (∫ x, upperHalf.indicator (fun x => ν x / (x - conj z) ^ 2) x / (x - ζ) ^ 2) +
        2 * (z - conj z) * (conj z - ζ) / (z - ζ) ^ 3 *
          (∫ x, upperHalf.indicator (fun x => ν x / (x - conj z) ^ 3) x / (x - ζ) ^ 2)) with hGd
  have hGd' : DifferentiableOn ℂ G L := by
    have hq : ∀ n : ℕ, DifferentiableOn ℂ (fun ζ : ℂ => (z - ζ) ^ n) L := fun n =>
      ((differentiableOn_const _).sub differentiableOn_id).pow n
    refine ((differentiableOn_const _).mul (((differentiableOn_const _).sub differentiableOn_id).pow 2)).mul
      ((((differentiableOn_const _).div (hq 2) fun ζ hζ => pow_ne_zero 2 (hzne ζ hζ)).add
        ((differentiableOn_const _).div (hq 3) fun ζ hζ => pow_ne_zero 3 (hzne ζ hζ))).mul hB2 |>.add
      ((((differentiableOn_const _).mul ((differentiableOn_const _).sub differentiableOn_id)).div (hq 3)
        fun ζ hζ => pow_ne_zero 3 (hzne ζ hζ)).mul hB3))
  have hGs : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) G L := (hGd'.contDiffOn hLo).restrict_scalars ℝ
  have hmap : MapsTo (fun v : ℂ => conj v) (upperHalf \ {z}) L := fun v hv => by
    show (conj v).im < 0
    rw [Complex.conj_im]
    have : 0 < v.im := hv.1
    linarith
  have hc : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun v : ℂ => conj v) := Complex.conjCLE.contDiff
  refine ((hc.comp_contDiffOn (hGs.comp hc.contDiffOn hmap))).congr fun v hv => ?_
  show conj (dz (fun e => kernelKbar (fun y => e * ν y) z v) 0) = conj (G (conj v))
  rw [s7l8_Dsnd_eq hν hz hv.1 hv.2]

/-- The principal-value limit behind (B2) (the truncations converge). -/
theorem s7l8_B2_lim {ν ψ : ℂ → ℂ} (hν : IsHarmonicU ν ψ) {u z : ℂ} (hu : u ∈ upperHalf)
    (hz : z ∈ upperHalf) (huz : u ≠ z) :
    Tendsto (fun δ : ℝ => ∫ v in upperHalf \ (ball u δ ∪ ball z δ), conj (ν v) *
        (dz (fun e => kernelKbar (fun y => e * ν y) u v) 0 * (1 / (conj v - conj z) ^ 2) +
          1 / (u - conj v) ^ 2 * dz (fun e => kernelKbarbar (fun y => e * ν y) v z) 0)) (𝓝[>] 0)
      (𝓝 (-(π : ℂ) * dz (dzbar fun e => kernelKbar (fun y => e * ν y) u z) 0)) := by
  obtain ⟨M, hM0, hM⟩ := harmonicU_bounded hν
  have hU := measurableSet_upperHalf_aux
  have hm : AEStronglyMeasurable ν (volume.restrict upperHalf) :=
    (harmonicU_continuousOn hν).aestronglyMeasurable hU
  have hνb : IsBeltramiCoeff ν upperHalf M := ⟨hm, (ae_restrict_mem hU).mono fun u hu => hM u hu⟩
  have hνs := wr_isHarmonicU_contDiffOn hν
  have hε0 : ‖(0 : ℂ)‖ * M < 1 := by simp
  have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 Real.pi_ne_zero
  obtain ⟨hint, hlim⟩ := s7l8_core2 hM0 hνb hνs hz hu huz
  set g : ℂ → ℂ := fun v => conj (ν v) * (dz (fun e => kernelKbar (fun y => e * ν y) u v) 0 *
    (1 / (conj v - conj z) ^ 2) + 1 / (u - conj v) ^ 2 * dz (fun e => kernelKbarbar (fun y => e * ν y) v z) 0)
    with hg
  -- the product rule at `0`
  have hpt : ∀ v ∈ upperHalf, v ≠ z → dz (fun e => conj (ν v) * kernelKbar (fun y => e * ν y) u v *
      kernelKbarbar (fun y => e * ν y) v z) 0 = g v := by
    intro v hv hvz
    have hw0 := e64_t9_w0 ν
    obtain ⟨hwz, hdz⟩ := e124_E2_diff hM0 hνb hνs hε0 hz
    obtain ⟨hwv, hdv⟩ := e124_E2_diff hM0 hνb hνs hε0 hv
    have hKb : DifferentiableAt ℝ (fun e => kernelKbar (fun y => e * ν y) u v) 0 := s71_K_diffAt hν hu hv
    have hK : DifferentiableAt ℝ (fun e => kernelK (fun y => e * ν y) v z) 0 := by
      unfold kernelK
      have hn : DifferentiableAt ℝ (fun e => dz (wU fun y => e * ν y) v * dz (wU fun y => e * ν y) z) 0 :=
        hdv.mul hdz
      have hd : DifferentiableAt ℝ (fun e => (wU (fun y => e * ν y) v - wU (fun y => e * ν y) z) ^ 2) 0 :=
        (hwv.sub hwz).pow 2
      refine (hn.mul (hd.inv ?_)).congr_of_eventuallyEq (Eventually.of_forall fun e => div_eq_mul_inv _ _)
      simp only [hw0, id]
      exact pow_ne_zero 2 (sub_ne_zero.mpr hvz)
    have hKbb : DifferentiableAt ℝ (fun e => kernelKbarbar (fun y => e * ν y) v z) 0 := by
      unfold kernelKbarbar
      exact Complex.conjCLE.differentiableAt.comp 0 hK
    have hcK : DifferentiableAt ℝ (fun e => conj (ν v) * kernelKbar (fun y => e * ν y) u v) 0 :=
      (differentiableAt_const _).mul hKb
    rw [e64_t9_dz_mul hcK hKbb, e64_t9_dz_mul (differentiableAt_const _) hKb,
      (e124_dz_eventuallyConst (Eventually.of_forall fun _ => rfl)).1]
    have h0 := (e64_t9_K0 ν u v).2.1
    have h1 := (e64_t9_K0 ν v z).2.2
    simp only [hg, h0, h1]
    ring
  have hmemz : ∀ δ : ℝ, 0 < δ → ∀ v ∈ upperHalf \ ball z δ, v ≠ z := fun δ hδ v hv hvz =>
    hv.2 (by rw [hvz]; exact mem_ball_self hδ)
  have hgi : ∀ δ : ℝ, 0 < δ → IntegrableOn g (upperHalf \ ball z δ) := fun δ hδ =>
    (hint δ hδ).congr_fun (fun v hv => hpt v hv.1 (hmemz δ hδ v hv)) (hU.diff measurableSet_ball)
  have hlimg : Tendsto (fun δ : ℝ => ∫ v in upperHalf \ ball z δ, g v) (𝓝[>] 0)
      (𝓝 (-(π : ℂ) * dz (dzbar fun e => kernelKbar (fun y => e * ν y) u z) 0)) := by
    refine hlim.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    exact setIntegral_congr_fun (hU.diff measurableSet_ball) fun v hv => hpt v hv.1 (hmemz δ hδ v hv)
  -- the ball around `u` is negligible
  have huim : 0 < u.im := hu
  have huzn : 0 < ‖u - z‖ := norm_pos_iff.2 (sub_ne_zero.2 huz)
  set δ0 : ℝ := min (‖u - z‖ / 2) (u.im / 2) with hδ0d
  have hδ0 : 0 < δ0 := lt_min (by linarith) (by linarith)
  have hballA : ∀ δ : ℝ, 0 < δ → δ < δ0 → ball u δ ⊆ upperHalf \ ball z δ ∧ ball u δ ⊆ upperHalf \ ball z δ0 := by
    intro δ hδ hδδ
    suffices key : ∀ v ∈ ball u δ, v ∈ upperHalf ∧ ∀ d, d ≤ δ0 → v ∉ ball z d from
      ⟨fun v hv => ⟨(key v hv).1, (key v hv).2 δ hδδ.le⟩, fun v hv => ⟨(key v hv).1, (key v hv).2 δ0 le_rfl⟩⟩
    intro v hv
    rw [mem_ball, dist_eq_norm] at hv
    have hvU : v ∈ upperHalf := by
      show 0 < v.im
      have h1 : |v.im - u.im| ≤ ‖v - u‖ := by rw [← Complex.sub_im]; exact Complex.abs_im_le_norm _
      have h2 := (abs_le.mp h1).1
      have : δ0 ≤ u.im / 2 := min_le_right _ _
      linarith
    refine ⟨hvU, ?_⟩
    · intro d hd hvz
      rw [mem_ball, dist_eq_norm] at hvz
      have h3 : ‖u - z‖ ≤ ‖u - v‖ + ‖v - z‖ := norm_sub_le_norm_sub_add_norm_sub u v z
      rw [norm_sub_rev u v] at h3
      have : δ0 ≤ ‖u - z‖ / 2 := min_le_left _ _
      linarith
  have hsmall : Tendsto (fun δ : ℝ => ∫ v in (upperHalf \ ball z δ) ∩ ball u δ, g v) (𝓝[>] 0) (𝓝 0) := by
    have hne : ∀ᵐ a ∂(volume.restrict (upperHalf \ ball z δ0)), a ≠ u :=
      ae_restrict_of_ae (by simp [ae_iff, measure_singleton])
    have hdc : Tendsto (fun δ : ℝ => ∫ v in upperHalf \ ball z δ0, (ball u δ).indicator g v) (𝓝[>] 0)
        (𝓝 (∫ v in upperHalf \ ball z δ0, (0 : ℂ))) := by
      refine tendsto_integral_filter_of_dominated_convergence (fun v => ‖g v‖)
        (Eventually.of_forall fun δ => ((hgi δ0 hδ0).aestronglyMeasurable.indicator measurableSet_ball))
        (Eventually.of_forall fun δ => Eventually.of_forall fun v => ?_) (hgi δ0 hδ0).norm ?_
      · by_cases hv : v ∈ ball u δ
        · simp [Set.indicator_of_mem hv]
        · simp [Set.indicator_of_notMem hv]
      · filter_upwards [hne] with v hv
        have hp : 0 < ‖v - u‖ := norm_pos_iff.2 (sub_ne_zero.2 hv)
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [Ioo_mem_nhdsGT hp] with δ hδ
        have : v ∉ ball u δ := by rw [mem_ball, dist_eq_norm, not_lt]; exact hδ.2.le
        simp [Set.indicator_of_notMem this]
    rw [integral_zero] at hdc
    refine hdc.congr' ?_
    filter_upwards [Ioo_mem_nhdsGT hδ0] with δ hδ
    obtain ⟨h1, h2⟩ := hballA δ hδ.1 hδ.2
    rw [setIntegral_indicator measurableSet_ball, inter_eq_right.2 h2, inter_eq_right.2 h1]
  have hpv : Tendsto (fun δ : ℝ => ∫ v in upperHalf \ (ball u δ ∪ ball z δ), g v) (𝓝[>] 0)
      (𝓝 (-(π : ℂ) * dz (dzbar fun e => kernelKbar (fun y => e * ν y) u z) 0)) := by
    have h2 := hlimg.sub hsmall
    rw [sub_zero] at h2
    refine h2.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    have hδ' : (0 : ℝ) < δ := hδ
    have hset : upperHalf \ (ball u δ ∪ ball z δ) =
        (upperHalf \ ball z δ) \ ((upperHalf \ ball z δ) ∩ ball u δ) := by
      ext v; simp only [mem_diff, mem_union, mem_inter_iff]; tauto
    rw [hset, setIntegral_diff ((hU.diff measurableSet_ball).inter measurableSet_ball) (hgi δ hδ')
      inter_subset_left]
  exact hpv

/-- Conjugate symmetry of the mixed kernel variation: `M(w, z) = \overline{M(z, w)}`. -/
theorem s7l8_M_conj {ν ψ : ℂ → ℂ} (hν : IsHarmonicU ν ψ) {w z : ℂ} (hw : w ∈ upperHalf) (hz : z ∈ upperHalf) :
    dz (dzbar fun e => kernelKbar (fun y => e * ν y) w z) 0 =
      conj (dz (dzbar fun e => kernelKbar (fun y => e * ν y) z w) 0) := by
  have hK : (fun e => kernelKbar (fun y => e * ν y) w z) =
      fun e => conj (kernelKbar (fun y => e * ν y) z w) := by
    funext e
    unfold kernelKbar
    rw [map_div₀, map_mul, map_pow, map_sub, Complex.conj_conj, Complex.conj_conj]
    ring
  obtain ⟨r, hr, hC⟩ := s7l8_K_C2 hν hz hw
  have hCa : ContDiffAt ℝ 2 (fun e => kernelKbar (fun y => e * ν y) z w) 0 :=
    hC.contDiffAt (ball_mem_nhds 0 hr)
  have h1 : (dzbar fun e => conj (kernelKbar (fun y => e * ν y) z w)) =
      fun x => conj (dz (fun e => kernelKbar (fun y => e * ν y) z w) x) :=
    funext fun x => p71r_dzbar_conj _ x
  rw [hK, h1, s7g_f2_dz_conj, wp_wirtinger_comm hCa]

/-- **(R1) Paper-order form of `M`**: for `w ≠ z` in `𝕌`, the truncations of
`ν(v) [\overline{D₁(z, v)}/(v - w)² + \overline{∂_e K̄̄_e(v, w)|₀}/(z̄ - v)²]` converge to `-π M(w, z)`
(conjugate of (B2) at `(z, w)`). -/
theorem s7l8_R1 {ν ψ : ℂ → ℂ} (hν : IsHarmonicU ν ψ) {w z : ℂ} (hw : w ∈ upperHalf) (hz : z ∈ upperHalf)
    (hwz : w ≠ z) :
    Tendsto (fun δ : ℝ => ∫ v in upperHalf \ (ball z δ ∪ ball w δ), ν v *
        (conj (dz (fun e => kernelKbar (fun y => e * ν y) z v) 0) * (1 / (v - w) ^ 2) +
          1 / (conj z - v) ^ 2 * conj (dz (fun e => kernelKbarbar (fun y => e * ν y) v w) 0))) (𝓝[>] 0)
      (𝓝 (-(π : ℂ) * dz (dzbar fun e => kernelKbar (fun y => e * ν y) w z) 0)) := by
  have h := s7l8_B2_lim hν hz hw (Ne.symm hwz)
  have hc := (Complex.continuous_conj.tendsto _).comp h
  rw [s7l8_M_conj hν hw hz]
  have e : conj (-(π : ℂ) * dz (dzbar fun e => kernelKbar (fun y => e * ν y) z w) 0) =
      -(π : ℂ) * conj (dz (dzbar fun e => kernelKbar (fun y => e * ν y) z w) 0) := by
    rw [map_mul, map_neg, Complex.conj_ofReal]
  rw [e] at hc
  refine hc.congr fun δ => ?_
  simp only [Function.comp_apply]
  rw [← integral_conj]
  refine integral_congr_ae (Eventually.of_forall fun v => ?_)
  simp only [map_mul, map_add, map_div₀, map_one, map_pow, map_sub, Complex.conj_conj]

/-- Conjugation `𝕌 → 𝕃` is measure preserving and a measurable embedding. -/
theorem s7l8_conj_mp :
    MeasurePreserving (fun v : ℂ => conj v) (volume.restrict upperHalf) (volume.restrict {ζ : ℂ | ζ.im < 0}) ∧
      MeasurableEmbedding (fun v : ℂ => conj v) := by
  have hLm : MeasurableSet {ζ : ℂ | ζ.im < 0} := measurableSet_lt Complex.measurable_im measurable_const
  have hpre : (fun v : ℂ => conj v) ⁻¹' {ζ : ℂ | ζ.im < 0} = upperHalf := by
    ext v
    simp [upperHalf]
  refine ⟨?_, Complex.conjCLE.toHomeomorph.measurableEmbedding⟩
  have := gzE_conj_measurePreserving.restrict_preimage hLm
  rwa [hpre] at this

/-- The reflected weight `k_w = 1_𝕃 \overline{ν(ζ̄)}/(ζ - w)²`: measurable, `L²`, `∫ |k_w|² ≤ M² π/(Im w)²`. -/
theorem s7l8_kL_data {ν ψ : ℂ → ℂ} (hν : IsHarmonicU ν ψ) {M : ℝ} (hM : ∀ v ∈ upperHalf, ‖ν v‖ ≤ M)
    {w : ℂ} (hw : w ∈ upperHalf) :
    Measurable ({ζ : ℂ | ζ.im < 0}.indicator fun ξ => conj (ν (conj ξ)) / (ξ - w) ^ 2) ∧
      MemLp ({ζ : ℂ | ζ.im < 0}.indicator fun ξ => conj (ν (conj ξ)) / (ξ - w) ^ 2) 2 volume ∧
      (∫⁻ ξ, ‖{ζ : ℂ | ζ.im < 0}.indicator (fun ξ => conj (ν (conj ξ)) / (ξ - w) ^ 2) ξ‖ₑ ^ 2) ≤
        ENNReal.ofReal (M ^ 2 * (π / w.im ^ 2)) := by
  have hwim : 0 < w.im := hw
  set L : Set ℂ := {ζ : ℂ | ζ.im < 0} with hLd
  have hLm : MeasurableSet L := measurableSet_lt Complex.measurable_im measurable_const
  have hne : ∀ ξ ∈ L, ξ - w ≠ 0 := fun ξ hξ h => by
    have h' := congrArg Complex.im h
    have : ξ.im < 0 := hξ
    simp only [Complex.sub_im, Complex.zero_im] at h'
    linarith
  have hcU : ∀ ξ ∈ L, conj ξ ∈ upperHalf := fun ξ hξ => by
    show 0 < (conj ξ).im
    rw [Complex.conj_im]
    have : ξ.im < 0 := hξ
    linarith
  have hνc := harmonicU_continuousOn hν
  have hF : ContinuousOn (fun ξ => conj (ν (conj ξ)) / (ξ - w) ^ 2) L :=
    (Complex.continuous_conj.comp_continuousOn (hνc.comp Complex.continuous_conj.continuousOn hcU)).div
      (by fun_prop) fun ξ hξ => pow_ne_zero 2 (hne ξ hξ)
  set g := L.indicator fun ξ => conj (ν (conj ξ)) / (ξ - w) ^ 2 with hgd
  have hgm : Measurable g := by
    rw [hgd, ← Set.piecewise_eq_indicator]
    exact hF.measurable_piecewise continuousOn_const hLm
  set S : Set ℂ := {ζ : ℂ | w.im ≤ ‖ζ - w‖} with hSd
  have hS : MeasurableSet S := measurableSet_le measurable_const (measurable_id.sub_const _).norm
  obtain ⟨hSi, hSv⟩ := Ch2.s2c_l4_outside_ball w hwim
  have hLS : L ⊆ S := by
    intro ξ hξ
    show w.im ≤ ‖ξ - w‖
    have h1 := Complex.abs_im_le_norm (ξ - w)
    have h2 : (ξ - w).im = ξ.im - w.im := by simp
    have : ξ.im < 0 := hξ
    rw [h2, abs_of_neg (by linarith)] at h1
    linarith
  have hpt : ∀ ξ, ‖g ξ‖ ^ 2 ≤ M ^ 2 * S.indicator (fun ζ : ℂ => (‖ζ - w‖ ^ 4)⁻¹) ξ := by
    intro ξ
    by_cases hξ : ξ ∈ L
    · rw [hgd, Set.indicator_of_mem hξ, Set.indicator_of_mem (hLS hξ), norm_div, norm_pow, div_pow,
        Complex.norm_conj]
      have hM0 : 0 ≤ ‖ν (conj ξ)‖ := norm_nonneg _
      rw [← pow_mul, div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hM0 (hM _ (hcU ξ hξ)) 2) (by positivity)
    · rw [hgd, Set.indicator_of_notMem hξ, norm_zero]
      have : 0 ≤ S.indicator (fun ζ : ℂ => (‖ζ - w‖ ^ 4)⁻¹) ξ :=
        Set.indicator_nonneg (fun ζ _ => by positivity) ξ
      nlinarith [sq_nonneg M]
  have hmaj : Integrable (fun ξ => M ^ 2 * S.indicator (fun ζ : ℂ => (‖ζ - w‖ ^ 4)⁻¹) ξ) :=
    (hSi.integrable_indicator hS).const_mul _
  have hsq : Integrable (fun ξ => ‖g ξ‖ ^ 2) :=
    hmaj.mono' ((hgm.norm.pow_const 2).aestronglyMeasurable) (Eventually.of_forall fun ξ => by
      rw [Real.norm_of_nonneg (by positivity)]; exact hpt ξ)
  have hg2 : MemLp g 2 volume := (memLp_two_iff_integrable_sq_norm hgm.aestronglyMeasurable).2 hsq
  refine ⟨hgm, hg2, ?_⟩
  calc (∫⁻ ξ, ‖g ξ‖ₑ ^ 2) = ∫⁻ ξ, ENNReal.ofReal (‖g ξ‖ ^ 2) := by
        refine lintegral_congr fun ξ => ?_
        rw [← ofReal_norm, ENNReal.ofReal_pow (norm_nonneg _)]
    _ ≤ ∫⁻ ξ, ENNReal.ofReal (M ^ 2 * S.indicator (fun ζ : ℂ => (‖ζ - w‖ ^ 4)⁻¹) ξ) :=
        lintegral_mono fun ξ => ENNReal.ofReal_le_ofReal (hpt ξ)
    _ = ENNReal.ofReal (∫ ξ, M ^ 2 * S.indicator (fun ζ : ℂ => (‖ζ - w‖ ^ 4)⁻¹) ξ) :=
        (ofReal_integral_eq_lintegral_ofReal hmaj (Eventually.of_forall fun ξ =>
          mul_nonneg (sq_nonneg _) (Set.indicator_nonneg (fun ζ _ => by positivity) ξ))).symm
    _ = ENNReal.ofReal (M ^ 2 * (π / w.im ^ 2)) := by
        rw [integral_const_mul, integral_indicator hS, hSv]

/-- **The `I₃` kernel** `C(v, w) = \overline{∂_e K̄̄_e(v, w)|₀} = ∂_ē K_e(v, w)|₀` (`e124_eq_1_24`) as an
off-support transform: `C(v, w) = -(1/π) ∫ k_w(ξ)/(ξ - v)²`, for `v ≠ w` in `𝕌`. -/
theorem s7l8_C_eq {ν ψ : ℂ → ℂ} (hν : IsHarmonicU ν ψ) {v w : ℂ} (hv : v ∈ upperHalf) (hw : w ∈ upperHalf)
    (hvw : v ≠ w) :
    conj (dz (fun e => kernelKbarbar (fun y => e * ν y) v w) 0) =
      -(1 / π) * ∫ ξ, {ζ : ℂ | ζ.im < 0}.indicator (fun ξ => conj (ν (conj ξ)) / (ξ - w) ^ 2) ξ / (ξ - v) ^ 2 := by
  obtain ⟨M, hM0, hνb, hνs⟩ := s71_harm_setup hν
  have hU := measurableSet_upperHalf_aux
  have hε0 : ‖(0 : ℂ)‖ * M < 1 := by simp
  have h1 : conj (dz (fun e => kernelKbarbar (fun y => e * ν y) v w) 0) =
      dzbar (fun e => kernelK (fun y => e * ν y) v w) 0 := by
    have : (fun e => kernelKbarbar (fun y => e * ν y) v w) = fun e => conj (kernelK (fun y => e * ν y) v w) := rfl
    rw [this, s7g_f2_dz_conj, Complex.conj_conj]
  have hfun : (fun x => conj (ν x) * kernelKbar (fun y => (0 : ℂ) * ν y) v x *
      kernelKbar (fun y => (0 : ℂ) * ν y) w x) = fun x => conj (ν x) * (1 / (v - conj x) ^ 2) * (1 / (w - conj x) ^ 2) :=
    funext fun x => by rw [(e64_t9_K0 ν v x).2.1, (e64_t9_K0 ν w x).2.1]
  obtain ⟨hI0, -⟩ := e64_t9_int hν hw hv
  have hInt : IntegrableOn (fun x => conj (ν x) * (1 / (v - conj x) ^ 2) * (1 / (w - conj x) ^ 2)) upperHalf := by
    have hc : IntegrableOn (fun x => conj (ν x / ((x - conj v) ^ 2 * (x - conj w) ^ 2))) upperHalf :=
      Integrable.mono hI0 (Complex.continuous_conj.comp_aestronglyMeasurable hI0.aestronglyMeasurable)
        (Eventually.of_forall fun x => le_of_eq (Complex.norm_conj _))
    refine hc.congr_fun (fun x _ => ?_) hU
    simp only [one_div, mul_inv, div_eq_mul_inv, map_mul, map_inv₀, map_pow, map_sub, Complex.conj_conj]
    ring
  have hpv : pv2 (fun x => conj (ν x) * (1 / (v - conj x) ^ 2) * (1 / (w - conj x) ^ 2)) v w =
      ∫ x in upperHalf, conj (ν x) * (1 / (v - conj x) ^ 2) * (1 / (w - conj x) ^ 2) := by
    unfold pv2
    exact (e124a_reg2 v w hInt).limUnder_eq
  obtain ⟨hmp, hemb⟩ := s7l8_conj_mp
  have hLm : MeasurableSet {ζ : ℂ | ζ.im < 0} := measurableSet_lt Complex.measurable_im measurable_const
  have hcv : (∫ ξ, {ζ : ℂ | ζ.im < 0}.indicator (fun ξ => conj (ν (conj ξ)) / (ξ - w) ^ 2) ξ / (ξ - v) ^ 2) =
      ∫ x in upperHalf, conj (ν x) * (1 / (v - conj x) ^ 2) * (1 / (w - conj x) ^ 2) := by
    have e1 : (fun ξ => {ζ : ℂ | ζ.im < 0}.indicator (fun ξ => conj (ν (conj ξ)) / (ξ - w) ^ 2) ξ / (ξ - v) ^ 2) =
        {ζ : ℂ | ζ.im < 0}.indicator (fun ξ => conj (ν (conj ξ)) / (ξ - w) ^ 2 / (ξ - v) ^ 2) := by
      funext ξ
      by_cases hξ : ξ ∈ {ζ : ℂ | ζ.im < 0}
      · simp only [Set.indicator_of_mem hξ]
      · simp only [Set.indicator_of_notMem hξ, zero_div]
    rw [e1, integral_indicator hLm, ← hmp.integral_comp hemb]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [Complex.conj_conj]
    ring
  rw [h1, (e124_eq_1_24 hM0 hνb hνs hε0 hv hw hvw).2, hfun, hpv, hcv]

/-- `L²` bound of `C(·, w)` on `𝕌`: `∫_𝕌 |∫ k_w/(ξ - v)²|² ≤ π² M² π/(Im w)²`. -/
theorem s7l8_C_L2 {ν ψ : ℂ → ℂ} (hν : IsHarmonicU ν ψ) {M : ℝ} (hM : ∀ v ∈ upperHalf, ‖ν v‖ ≤ M)
    {w : ℂ} (hw : w ∈ upperHalf) :
    (∫⁻ v in upperHalf, ‖∫ ξ, {ζ : ℂ | ζ.im < 0}.indicator (fun ξ => conj (ν (conj ξ)) / (ξ - w) ^ 2) ξ /
      (ξ - v) ^ 2‖ₑ ^ 2) ≤ ENNReal.ofReal (π ^ 2) * ENNReal.ofReal (M ^ 2 * (π / w.im ^ 2)) := by
  obtain ⟨hkm, hk2, hkb⟩ := s7l8_kL_data hν hM hw
  have hUo : IsOpen upperHalf := isOpen_lt continuous_const Complex.continuous_im
  have h0 : ∀ x ∈ upperHalf, {ζ : ℂ | ζ.im < 0}.indicator (fun ξ => conj (ν (conj ξ)) / (ξ - w) ^ 2) x = 0 :=
    fun x hx => Set.indicator_of_notMem (fun h => by
      have h1 : x.im < 0 := h
      have h2 : 0 < x.im := hx
      linarith) _
  exact (s7l8_off_L2 hkm hk2 hUo h0).trans (mul_le_mul_right hkb _)

/-- `L²` from a finite `∫⁻ ‖g‖²`. -/
theorem s7l8_memLp2 {g : ℂ → ℂ} {m : Measure ℂ} (hg : AEStronglyMeasurable g m) (h : (∫⁻ x, ‖g x‖ₑ ^ 2 ∂m) < ∞) :
    MemLp g 2 m := by
  rw [memLp_two_iff_integrable_sq_norm hg]
  refine ⟨hg.norm.pow 2, ?_⟩
  show (∫⁻ x, ‖‖g x‖ ^ 2‖ₑ ∂m) < ∞
  have e : ∀ x, ‖‖g x‖ ^ 2‖ₑ = ‖g x‖ₑ ^ 2 := fun x => by
    rw [Real.enorm_eq_ofReal (by positivity), ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
  simpa only [e] using h

/-- The two-ball and one-ball truncations differ by the integral over `(𝕌 ∖ B(z, δ)) ∩ B(v, δ)`, which tends to
`0` (`f` integrable off every ball at `z`, `v ≠ z`). -/
theorem s7l8_pv_small {f : ℂ → ℂ} {z v : ℂ} (hv : v ∈ upperHalf) (hvz : v ≠ z)
    (hfi : ∀ δ : ℝ, 0 < δ → IntegrableOn f (upperHalf \ ball z δ)) :
    Tendsto (fun δ : ℝ => ∫ x in (upperHalf \ ball z δ) ∩ ball v δ, f x) (𝓝[>] 0) (𝓝 0) := by
  have hvim : 0 < v.im := hv
  have hvzn : 0 < ‖v - z‖ := norm_pos_iff.2 (sub_ne_zero.2 hvz)
  set δ0 : ℝ := min (‖v - z‖ / 2) (v.im / 2) with hδ0d
  have hδ0 : 0 < δ0 := lt_min (by linarith) (by linarith)
  have hballA : ∀ δ : ℝ, 0 < δ → δ < δ0 → ball v δ ⊆ upperHalf \ ball z δ ∧ ball v δ ⊆ upperHalf \ ball z δ0 := by
    intro δ hδ hδδ
    suffices key : ∀ x ∈ ball v δ, x ∈ upperHalf ∧ ∀ d, d ≤ δ0 → x ∉ ball z d from
      ⟨fun x hx => ⟨(key x hx).1, (key x hx).2 δ hδδ.le⟩, fun x hx => ⟨(key x hx).1, (key x hx).2 δ0 le_rfl⟩⟩
    intro x hx
    rw [mem_ball, dist_eq_norm] at hx
    have hxU : x ∈ upperHalf := by
      show 0 < x.im
      have h1 : |x.im - v.im| ≤ ‖x - v‖ := by rw [← Complex.sub_im]; exact Complex.abs_im_le_norm _
      have h2 := (abs_le.mp h1).1
      have : δ0 ≤ v.im / 2 := min_le_right _ _
      linarith
    refine ⟨hxU, ?_⟩
    · intro d hd hxz
      rw [mem_ball, dist_eq_norm] at hxz
      have h3 : ‖v - z‖ ≤ ‖v - x‖ + ‖x - z‖ := norm_sub_le_norm_sub_add_norm_sub v x z
      rw [norm_sub_rev v x] at h3
      have : δ0 ≤ ‖v - z‖ / 2 := min_le_left _ _
      linarith
  have hne : ∀ᵐ a ∂(volume.restrict (upperHalf \ ball z δ0)), a ≠ v :=
    ae_restrict_of_ae (by simp [ae_iff, measure_singleton])
  have hdc : Tendsto (fun δ : ℝ => ∫ x in upperHalf \ ball z δ0, (ball v δ).indicator f x) (𝓝[>] 0)
      (𝓝 (∫ x in upperHalf \ ball z δ0, (0 : ℂ))) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun x => ‖f x‖)
      (Eventually.of_forall fun δ => ((hfi δ0 hδ0).aestronglyMeasurable.indicator measurableSet_ball))
      (Eventually.of_forall fun δ => Eventually.of_forall fun x => ?_) (hfi δ0 hδ0).norm ?_
    · by_cases hx : x ∈ ball v δ
      · simp [Set.indicator_of_mem hx]
      · simp [Set.indicator_of_notMem hx]
    · filter_upwards [hne] with x hx
      have hp : 0 < ‖x - v‖ := norm_pos_iff.2 (sub_ne_zero.2 hx)
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [Ioo_mem_nhdsGT hp] with δ hδ
      have : x ∉ ball v δ := by rw [mem_ball, dist_eq_norm, not_lt]; exact hδ.2.le
      simp [Set.indicator_of_notMem this]
  rw [integral_zero] at hdc
  refine hdc.congr' ?_
  filter_upwards [Ioo_mem_nhdsGT hδ0] with δ hδ
  obtain ⟨h1, h2⟩ := hballA δ hδ.1 hδ.2
  rw [setIntegral_indicator measurableSet_ball, inter_eq_right.2 h2, inter_eq_right.2 h1]

/-- Converse of `s7l8_pv_drop`: two-ball truncation limits at `z, v` are one-ball limits at `z`. -/
theorem s7l8_pv_lift {f : ℂ → ℂ} {z v : ℂ} (hv : v ∈ upperHalf) (hvz : v ≠ z)
    (hfi : ∀ δ : ℝ, 0 < δ → IntegrableOn f (upperHalf \ ball z δ)) {L : ℂ}
    (hL : Tendsto (fun δ : ℝ => ∫ x in upperHalf \ (ball z δ ∪ ball v δ), f x) (𝓝[>] 0) (𝓝 L)) :
    Tendsto (fun δ : ℝ => ∫ x in upperHalf \ ball z δ, f x) (𝓝[>] 0) (𝓝 L) := by
  have hU := measurableSet_upperHalf_aux
  have h2 := hL.add (s7l8_pv_small hv hvz hfi)
  rw [add_zero] at h2
  refine h2.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  have hδ' : (0 : ℝ) < δ := hδ
  have hset : upperHalf \ (ball z δ ∪ ball v δ) =
      (upperHalf \ ball z δ) \ ((upperHalf \ ball z δ) ∩ ball v δ) := by
    ext x; simp only [mem_diff, mem_union, mem_inter_iff]; tauto
  rw [hset, setIntegral_diff ((hU.diff measurableSet_ball).inter measurableSet_ball) (hfi δ hδ')
    inter_subset_left]
  ring

/-- One-ball truncations over `ℂ` of `1_𝕌 G/(· - w)²` are the truncations over `𝕌 ∖ B(w, r)` (the sphere is
null). -/
theorem s7l8_ball_trunc (G : ℂ → ℂ) (w : ℂ) (r : ℝ) :
    (∫ ζ in {ζ : ℂ | r < ‖ζ - w‖}, upperHalf.indicator G ζ / (ζ - w) ^ 2) =
      ∫ ζ in upperHalf \ ball w r, G ζ / (ζ - w) ^ 2 := by
  have hU := measurableSet_upperHalf_aux
  have e1 : (fun ζ => upperHalf.indicator G ζ / (ζ - w) ^ 2) = upperHalf.indicator fun ζ => G ζ / (ζ - w) ^ 2 := by
    funext ζ
    by_cases hζ : ζ ∈ upperHalf
    · simp only [Set.indicator_of_mem hζ]
    · simp only [Set.indicator_of_notMem hζ, zero_div]
  rw [e1, setIntegral_indicator hU]
  refine setIntegral_congr_set ?_
  refine (ae_eq_set).2 ⟨measure_mono_null ?_ (Measure.addHaar_sphere volume w r),
    measure_mono_null ?_ (Measure.addHaar_sphere volume w r)⟩
  · intro ζ hζ
    exfalso
    obtain ⟨⟨h1, h2⟩, h3⟩ := hζ
    apply h3
    refine ⟨h2, fun hb => ?_⟩
    have h1' : r < ‖ζ - w‖ := h1
    rw [mem_ball, dist_eq_norm] at hb
    linarith
  · intro ζ hζ
    obtain ⟨⟨h1, h2⟩, h3⟩ := hζ
    rw [mem_sphere, dist_eq_norm]
    have h4 : ¬ ‖ζ - w‖ < r := fun h => h2 (by rw [mem_ball, dist_eq_norm]; exact h)
    have h5 : ¬ r < ‖ζ - w‖ := fun h => h3 ⟨h, h1⟩
    push_neg at h4 h5
    linarith

/-- Measurability of `1_𝕌 G` for `G` continuous on `𝕌`. -/
theorem s7l8_ind_meas {G : ℂ → ℂ} (hG : ContinuousOn G upperHalf) : Measurable (upperHalf.indicator G) := by
  rw [← Set.piecewise_eq_indicator]
  exact hG.measurable_piecewise continuousOn_const measurableSet_upperHalf_aux

/-- `∫⁻ |1_𝕌 G|² = ∫⁻_𝕌 |G|²`. -/
theorem s7l8_ind_lint (G : ℂ → ℂ) :
    (∫⁻ v, ‖upperHalf.indicator G v‖ₑ ^ 2) = ∫⁻ v in upperHalf, ‖G v‖ₑ ^ 2 := by
  rw [← lintegral_indicator measurableSet_upperHalf_aux]
  refine lintegral_congr fun v => ?_
  by_cases hv : v ∈ upperHalf
  · simp only [Set.indicator_of_mem hv]
  · simp only [Set.indicator_of_notMem hv, enorm_zero]
    norm_num

/-- `G/(· - w)²` is integrable on `𝕌 ∖ B(w, δ)` when `1_𝕌 G ∈ L²`. -/
theorem s7l8_far_on {G : ℂ → ℂ} (hgm : Measurable (upperHalf.indicator G))
    (hg2 : MemLp (upperHalf.indicator G) 2 volume) (w : ℂ) {δ : ℝ} (hδ : 0 < δ) :
    IntegrableOn (fun v => G v / (v - w) ^ 2) (upperHalf \ ball w δ) := by
  have hU := measurableSet_upperHalf_aux
  have hhm : AEStronglyMeasurable ((ball w δ)ᶜ.indicator (upperHalf.indicator G)) volume :=
    (hgm.indicator measurableSet_ball.compl).aestronglyMeasurable
  have hh2 : MemLp ((ball w δ)ᶜ.indicator (upperHalf.indicator G)) 2 volume :=
    hg2.indicator measurableSet_ball.compl
  have hfar := s7l8_far_integrable hhm hh2 hδ fun ζ hζ => Set.indicator_of_notMem (fun h' : ζ ∈ (ball w δ)ᶜ => h' hζ) _
  refine (hfar.integrableOn (s := upperHalf \ ball w δ)).congr_fun (fun v hv => ?_) (hU.diff measurableSet_ball)
  simp only
  rw [Set.indicator_of_mem (show v ∈ (ball w δ)ᶜ from hv.2), Set.indicator_of_mem hv.1]

/-- Continuity of `v ↦ D₁(z, v)` on `𝕌`. -/
theorem s7l8_Dz_cont {ν ψ : ℂ → ℂ} (hν : IsHarmonicU ν ψ) {z : ℂ} (hz : z ∈ upperHalf) :
    ContinuousOn (fun v => dz (fun e => kernelKbar (fun y => e * ν y) z v) 0) upperHalf := by
  obtain ⟨D, hD⟩ : ∃ D : ℂ → ℂ → ℂ, D = fun a b => dz (fun e => kernelKbar (fun y => e * ν y) a b) 0 := ⟨_, rfl⟩
  have h0 : ContinuousOn (fun p : ℂ × ℂ => D p.1 p.2) (upperHalf ×ˢ upperHalf) := by
    rw [hD]
    exact s7l8_D1_cont hν
  have h1 : ContinuousOn (fun v => D z v) upperHalf :=
    h0.comp (continuous_const.prodMk continuous_id).continuousOn fun v hv => ⟨hz, hv⟩
  rw [hD] at h1
  exact h1

/-- Smoothness of `g_z` on `𝕌 ∖ {z}`. -/
theorem s7l8_gz_smooth {ν ψ : ℂ → ℂ} (hν : IsHarmonicU ν ψ) {z : ℂ} (hz : z ∈ upperHalf) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (upperHalf.indicator fun v => ν v * conj (dz (fun e => kernelKbar (fun y => e * ν y) z v) 0))
      (upperHalf \ {z}) := by
  have h1 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ν (upperHalf \ {z}) :=
    (wr_isHarmonicU_contDiffOn hν).mono sdiff_subset
  have h2 := h1.mul (s7l8_Dsnd_smooth hν hz)
  refine h2.congr fun v hv => ?_
  rw [Set.indicator_of_mem hv.1]

/-- `∫_𝕌 |ν \overline{D₁(z, ·)}|² < ∞`. -/
theorem s7l8_gz_L2 {ν ψ : ℂ → ℂ} (hν : IsHarmonicU ν ψ) {z : ℂ} (hz : z ∈ upperHalf) :
    (∫⁻ v in upperHalf, ‖ν v * conj (dz (fun e => kernelKbar (fun y => e * ν y) z v) 0)‖ₑ ^ 2) < ∞ := by
  obtain ⟨M, hM0, hM⟩ := harmonicU_bounded hν
  have hU := measurableSet_upperHalf_aux
  have hle : ∀ v ∈ upperHalf, ‖ν v * conj (dz (fun e => kernelKbar (fun y => e * ν y) z v) 0)‖ₑ ^ 2 ≤
      ENNReal.ofReal (M ^ 2) * ‖dz (fun e => kernelKbar (fun y => e * ν y) z v) 0‖ₑ ^ 2 := by
    intro v hv
    rw [enorm_mul, mul_pow, RCLike.enorm_conj, ← ofReal_norm (ν v), ← ENNReal.ofReal_pow (norm_nonneg _)]
    exact mul_le_mul_left (ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (norm_nonneg _) (hM v hv) 2)) _
  refine lt_of_le_of_lt (setLIntegral_mono' hU hle) ?_
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top ((s7l8_Dsnd_L2 hν hM hz).trans_lt ENNReal.ofReal_lt_top)

/-- `g_z = 1_𝕌 ν \overline{D₁(z, ·)}`: measurable, `L²`, smooth on `𝕌 ∖ {z}`. -/
theorem s7l8_gz {ν ψ : ℂ → ℂ} (hν : IsHarmonicU ν ψ) {z : ℂ} (hz : z ∈ upperHalf) :
    Measurable (upperHalf.indicator fun v => ν v * conj (dz (fun e => kernelKbar (fun y => e * ν y) z v) 0)) ∧
      MemLp (upperHalf.indicator fun v => ν v * conj (dz (fun e => kernelKbar (fun y => e * ν y) z v) 0)) 2
        volume ∧
      ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (upperHalf.indicator fun v => ν v * conj (dz (fun e => kernelKbar (fun y => e * ν y) z v) 0))
        (upperHalf \ {z}) := by
  have hνc := harmonicU_continuousOn hν
  have hDc := s7l8_Dz_cont hν hz
  have hDc' : ContinuousOn (fun v => conj (dz (fun e => kernelKbar (fun y => e * ν y) z v) 0)) upperHalf :=
    Complex.continuous_conj.comp_continuousOn hDc
  have hGc : ContinuousOn (fun v => ν v * conj (dz (fun e => kernelKbar (fun y => e * ν y) z v) 0)) upperHalf :=
    hνc.mul hDc'
  have hgm : Measurable (upperHalf.indicator fun v => ν v * conj (dz (fun e => kernelKbar (fun y => e * ν y) z v) 0)) :=
    s7l8_ind_meas hGc
  have hgb : (∫⁻ v, ‖upperHalf.indicator (fun v => ν v * conj (dz (fun e => kernelKbar (fun y => e * ν y) z v) 0))
      v‖ₑ ^ 2) < ∞ := by
    rw [s7l8_ind_lint]
    exact s7l8_gz_L2 hν hz
  have hg2 : MemLp (upperHalf.indicator fun v => ν v * conj (dz (fun e => kernelKbar (fun y => e * ν y) z v) 0)) 2
      volume := s7l8_memLp2 hgm.aestronglyMeasurable hgb
  exact ⟨hgm, hg2, s7l8_gz_smooth hν hz⟩

/-- The `I₃` integrand `ν(v)/(z̄ - v)² \overline{∂_e K̄̄(v, w)}` is integrable on `𝕌`, and equals `b_z C(·, w)` a.e. -/
theorem s7l8_Yint {ν ψ : ℂ → ℂ} (hν : IsHarmonicU ν ψ) {z w : ℂ} (hz : z ∈ upperHalf) (hw : w ∈ upperHalf) :
    IntegrableOn (fun v => ν v * (1 / (conj z - v) ^ 2 *
      conj (dz (fun e => kernelKbarbar (fun y => e * ν y) v w) 0))) upperHalf ∧
    (∫ v in upperHalf, ν v * (1 / (conj z - v) ^ 2 * conj (dz (fun e => kernelKbarbar (fun y => e * ν y) v w) 0))) =
      ∫ v in upperHalf, ν v * (1 / (conj z - v) ^ 2) *
        (-(1 / π) * ∫ ξ, {ζ : ℂ | ζ.im < 0}.indicator (fun ξ => conj (ν (conj ξ)) / (ξ - w) ^ 2) ξ / (ξ - v) ^ 2) := by
  obtain ⟨M, hM0, hM⟩ := harmonicU_bounded hν
  have hU := measurableSet_upperHalf_aux
  have hYC : ∀ᵐ v ∂(volume.restrict upperHalf), ν v * (1 / (conj z - v) ^ 2 *
      conj (dz (fun e => kernelKbarbar (fun y => e * ν y) v w) 0)) = ν v * (1 / (conj z - v) ^ 2) *
        (-(1 / π) * ∫ ξ, {ζ : ℂ | ζ.im < 0}.indicator (fun ξ => conj (ν (conj ξ)) / (ξ - w) ^ 2) ξ / (ξ - v) ^ 2) := by
    filter_upwards [ae_restrict_mem hU, ae_restrict_of_ae (Measure.ae_ne volume w)] with v hv hvw
    rw [s7l8_C_eq hν hv hw hvw]
    ring
  refine ⟨?_, integral_congr_ae hYC⟩
  obtain ⟨hbm, -, hb2, -⟩ := s7l8_g_data hν hM hz
  obtain ⟨hkm, -, -⟩ := s7l8_kL_data hν hM hw
  have hCm : Measurable (fun v : ℂ => (-(1 / π : ℂ)) * ∫ ξ, {ζ : ℂ | ζ.im < 0}.indicator
      (fun ξ => conj (ν (conj ξ)) / (ξ - w) ^ 2) ξ / (ξ - v) ^ 2) :=
    measurable_const.mul (s7l8_B_meas hkm)
  have hC2 : MemLp (fun v : ℂ => (-(1 / π : ℂ)) * ∫ ξ, {ζ : ℂ | ζ.im < 0}.indicator
      (fun ξ => conj (ν (conj ξ)) / (ξ - w) ^ 2) ξ / (ξ - v) ^ 2) 2 (volume.restrict upperHalf) := by
    refine s7l8_memLp2 hCm.aestronglyMeasurable ?_
    have hc : ‖(-(1 / π) : ℂ)‖ₑ ^ 2 = ENNReal.ofReal ((1 / π) ^ 2) := by
      rw [enorm_neg, ← ofReal_norm, show ((1 / π : ℂ)) = ((1 / π : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
        Real.norm_of_nonneg (by positivity), ← ENNReal.ofReal_pow (by positivity)]
    simp only [enorm_mul, mul_pow, hc]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top ((s7l8_C_L2 hν hM hw).trans_lt
      (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top))
  have hb2' : MemLp (fun v => ν v * (1 / (conj z - v) ^ 2)) 2 (volume.restrict upperHalf) := by
    refine (hb2.restrict upperHalf).ae_eq ?_
    filter_upwards [ae_restrict_mem hU] with v hv
    rw [Set.indicator_of_mem hv]
    ring
  exact (hb2'.integrable_mul hC2).congr (by
    filter_upwards [hYC] with v hv
    rw [hv]
    rfl)

/-- The one-ball truncations of `g_z/(· - w)²` converge to `Λ(w) = -π M(w, z) - ∫ Y` for `w ∈ 𝕌 ∖ {z}`. -/
theorem s7l8_Lam {ν ψ : ℂ → ℂ} (hν : IsHarmonicU ν ψ) {z w : ℂ} (hz : z ∈ upperHalf) (hw : w ∈ upperHalf)
    (hwz : w ≠ z) :
    Tendsto (fun r : ℝ => ∫ ζ in {ζ : ℂ | r < ‖ζ - w‖},
        upperHalf.indicator (fun v => ν v * conj (dz (fun e => kernelKbar (fun y => e * ν y) z v) 0)) ζ /
          (ζ - w) ^ 2) (𝓝[>] 0)
      (𝓝 (-(π : ℂ) * dz (dzbar fun e => kernelKbar (fun y => e * ν y) w z) 0 -
        ∫ v in upperHalf, ν v * (1 / (conj z - v) ^ 2 *
          conj (dz (fun e => kernelKbarbar (fun y => e * ν y) v w) 0)))) := by
  have hU := measurableSet_upperHalf_aux
  obtain ⟨hgm, hg2, -⟩ := s7l8_gz hν hz
  obtain ⟨hYi, -⟩ := s7l8_Yint hν hz hw
  have hXi : ∀ δ : ℝ, 0 < δ → IntegrableOn
      (fun v => ν v * conj (dz (fun e => kernelKbar (fun y => e * ν y) z v) 0) / (v - w) ^ 2)
      (upperHalf \ ball w δ) := fun δ hδ => s7l8_far_on hgm hg2 w hδ
  have hR := s7l8_R1 hν hw hz hwz
  have hY := e124a_reg2 z w hYi
  have hX : Tendsto (fun δ : ℝ => ∫ v in upperHalf \ (ball w δ ∪ ball z δ),
      ν v * conj (dz (fun e => kernelKbar (fun y => e * ν y) z v) 0) / (v - w) ^ 2) (𝓝[>] 0)
      (𝓝 (-(π : ℂ) * dz (dzbar fun e => kernelKbar (fun y => e * ν y) w z) 0 -
        ∫ v in upperHalf, ν v * (1 / (conj z - v) ^ 2 *
          conj (dz (fun e => kernelKbarbar (fun y => e * ν y) v w) 0)))) := by
    refine (hR.sub hY).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    have hδ' : (0 : ℝ) < δ := hδ
    have hsub : upperHalf \ (ball z δ ∪ ball w δ) ⊆ upperHalf \ ball w δ := fun v hv =>
      ⟨hv.1, fun h => hv.2 (Or.inr h)⟩
    have iX := (hXi δ hδ').mono_set hsub
    have iY := hYi.mono_set (show upperHalf \ (ball z δ ∪ ball w δ) ⊆ upperHalf from sdiff_subset)
    have iXY : IntegrableOn (fun v => ν v * conj (dz (fun e => kernelKbar (fun y => e * ν y) z v) 0) / (v - w) ^ 2 +
        ν v * (1 / (conj z - v) ^ 2 * conj (dz (fun e => kernelKbarbar (fun y => e * ν y) v w) 0)))
        (upperHalf \ (ball z δ ∪ ball w δ)) := iX.add iY
    have hm : MeasurableSet (upperHalf \ (ball z δ ∪ ball w δ)) := hU.diff (measurableSet_ball.union measurableSet_ball)
    rw [union_comm (ball w δ), ← integral_sub (iXY.congr_fun (fun v _ => by ring) hm) iY]
    refine setIntegral_congr_fun hm fun v _ => ?_
    ring
  have hL := s7l8_pv_lift hz (Ne.symm hwz) hXi hX
  exact hL.congr fun r => (s7l8_ball_trunc _ w r).symm

/-- **(D23) a.e. decomposition of `M`**: for `z ∈ 𝕌` and a.e. `w ∈ 𝕌`,
`M(w, z) = H g_z(w) - (1/π) ∫_𝕌 ν(v)/(z̄ - v)² C(v, w)` with `g_z = 1_𝕌 ν \overline{D₁(z, ·)}` and
`C(v, w) = -(1/π) ∫ k_w/(ξ - v)²`. -/
theorem s7l8_M_ae {ν ψ : ℂ → ℂ} (hν : IsHarmonicU ν ψ) {z : ℂ} (hz : z ∈ upperHalf) :
    ∀ᵐ w ∂(volume.restrict upperHalf), dz (dzbar fun e => kernelKbar (fun y => e * ν y) w z) 0 =
      hilbertH (upperHalf.indicator fun v => ν v * conj (dz (fun e => kernelKbar (fun y => e * ν y) z v) 0)) w -
        (1 / π) * ∫ v in upperHalf, ν v * (1 / (conj z - v) ^ 2) *
          (-(1 / π) * ∫ ξ, {ζ : ℂ | ζ.im < 0}.indicator (fun ξ => conj (ν (conj ξ)) / (ξ - w) ^ 2) ξ /
            (ξ - v) ^ 2) := by
  have hU := measurableSet_upperHalf_aux
  have hUo : IsOpen upperHalf := isOpen_lt continuous_const Complex.continuous_im
  have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 Real.pi_ne_zero
  obtain ⟨hgm, hg2, hgs⟩ := s7l8_gz hν hz
  have hU'o : IsOpen (upperHalf \ {z}) := hUo.sdiff isClosed_singleton
  have hHl := s7l8_hilbertH_local hgm hg2 hU'o hgs (fun w hw => s7l8_Lam hν hz hw.1 hw.2)
  have hnull : (upperHalf \ {z} : Set ℂ) =ᵐ[volume] upperHalf := sdiff_null_ae_eq_self (measure_singleton z)
  rw [Measure.restrict_congr_set hnull] at hHl
  filter_upwards [hHl, ae_restrict_mem hU] with w hw hwU
  rw [hw, ← (s7l8_Yint hν hz hwU).2]
  field_simp
  ring

/-- **Joint continuity of `M`** on `𝕌 × 𝕌` (second `e`-derivatives of the jointly `C²` kernel). -/
theorem s7l8_M_cont {ν ψ : ℂ → ℂ} (hν : IsHarmonicU ν ψ) :
    ContinuousOn (fun p : ℂ × ℂ => dz (dzbar fun e => kernelKbar (fun y => e * ν y) p.1 p.2) 0)
      (upperHalf ×ˢ upperHalf) := by
  obtain ⟨M, hM0, hM⟩ := harmonicU_bounded hν
  have hU := measurableSet_upperHalf_aux
  have hUo : IsOpen upperHalf := isOpen_lt continuous_const Complex.continuous_im
  have hm : AEStronglyMeasurable ν (volume.restrict upperHalf) :=
    (harmonicU_continuousOn hν).aestronglyMeasurable hU
  have hνb : IsBeltramiCoeff ν upperHalf M := ⟨hm, (ae_restrict_mem hU).mono fun u hu => hM u hu⟩
  have hνs := wr_isHarmonicU_contDiffOn hν
  set Ue : Set ℂ := {e : ℂ | ‖e‖ * M < 1} with hUed
  have hUeo : IsOpen Ue := isOpen_lt (continuous_norm.mul continuous_const) continuous_const
  have h0Ue : (0 : ℂ) ∈ Ue := by simp [hUed]
  set F : ℂ × ℂ → ℂ := fun q => wU (fun u => q.1 * ν u) q.2 with hFd
  have hF3 : ContDiffOn ℝ 3 F (Ue ×ˢ upperHalf) := wr_joint_contDiff_U hM0 hνb hνs
  have hO : IsOpen (Ue ×ˢ upperHalf) := hUeo.prod hUo
  set G : ℂ × ℂ → ℂ := fun q => (fderiv ℝ F q (0, 1) - I * fderiv ℝ F q (0, I)) / 2 with hGd
  have hF' : ContDiffOn ℝ 2 (fderiv ℝ F) (Ue ×ˢ upperHalf) := hF3.fderiv_of_isOpen hO (by norm_num)
  have hG2 : ContDiffOn ℝ 2 G (Ue ×ˢ upperHalf) :=
    ((hF'.clm_apply contDiffOn_const).sub (contDiffOn_const.mul (hF'.clm_apply contDiffOn_const))).div_const 2
  have hGdz : ∀ q ∈ Ue ×ˢ upperHalf, dz (wU fun u => q.1 * ν u) q.2 = G q := by
    intro q hq
    have hdF : DifferentiableAt ℝ F q := (hF3.differentiableOn (by norm_num) q hq).differentiableAt (hO.mem_nhds hq)
    have hsl : fderiv ℝ (wU fun u => q.1 * ν u) q.2 = (fderiv ℝ F q).comp (ContinuousLinearMap.inr ℝ ℂ ℂ) := by
      have e1 : (wU fun u => q.1 * ν u) = fun y => F (q.1, y) := rfl
      rw [e1]
      exact (hdF.hasFDerivAt.comp q.2 (hasFDerivAt_prodMk_right (𝕜 := ℝ) q.1 q.2)).fderiv
    show (fderiv ℝ (wU fun u => q.1 * ν u) q.2 1 - I * fderiv ℝ (wU fun u => q.1 * ν u) q.2 I) / 2 = _
    rw [hsl]
    rfl
  -- the joint kernel
  set S : Set (ℂ × ℂ × ℂ) := Ue ×ˢ (upperHalf ×ˢ upperHalf) with hSd
  have hSo : IsOpen S := hUeo.prod (hUo.prod hUo)
  set Φ : ℂ × ℂ × ℂ → ℂ := fun x => kernelKbar (fun y => x.1 * ν y) x.2.1 x.2.2 with hΦd
  have hm1 : MapsTo (fun x : ℂ × ℂ × ℂ => (x.1, x.2.1)) S (Ue ×ˢ upperHalf) := fun x hx => ⟨hx.1, hx.2.1⟩
  have hm2 : MapsTo (fun x : ℂ × ℂ × ℂ => (x.1, x.2.2)) S (Ue ×ˢ upperHalf) := fun x hx => ⟨hx.1, hx.2.2⟩
  have hs1 : ContDiff ℝ 2 (fun x : ℂ × ℂ × ℂ => (x.1, x.2.1)) := contDiff_fst.prodMk (contDiff_fst.comp contDiff_snd)
  have hs2 : ContDiff ℝ 2 (fun x : ℂ × ℂ × ℂ => (x.1, x.2.2)) := contDiff_fst.prodMk (contDiff_snd.comp contDiff_snd)
  have hc : ContDiff ℝ 2 (fun u : ℂ => conj u) := Complex.conjCLE.contDiff
  have hGa := hG2.comp hs1.contDiffOn hm1
  have hGb := hc.comp_contDiffOn (hG2.comp hs2.contDiffOn hm2)
  have hFa := (hF3.of_le (by norm_num)).comp hs1.contDiffOn hm1
  have hFb := hc.comp_contDiffOn ((hF3.of_le (by norm_num)).comp hs2.contDiffOn hm2)
  have hden : ∀ x ∈ S, (F (x.1, x.2.1) - conj (F (x.1, x.2.2))) ^ 2 ≠ 0 := by
    intro x hx
    obtain ⟨-, hbij, hsym, -⟩ := p71_V_facts hM0 hνb hx.1
    refine pow_ne_zero 2 (sub_ne_zero.mpr fun h => ?_)
    have h1 : F (x.1, x.2.1) = F (x.1, conj x.2.2) := by
      rw [h]
      exact (hsym x.2.2).symm
    have h2 : x.2.1 = conj x.2.2 := hbij.1 h1
    have h3 := congrArg Complex.im h2
    rw [Complex.conj_im] at h3
    have : 0 < x.2.1.im := hx.2.1
    have : 0 < x.2.2.im := hx.2.2
    linarith
  have hΦ : ContDiffOn ℝ 2 Φ S := by
    refine ((hGa.mul hGb).mul (((hFa.sub hFb).pow 2).inv hden)).congr fun x hx => ?_
    simp only [hΦd, Function.comp_apply]
    unfold kernelKbar
    rw [hGdz (x.1, x.2.1) (hm1 hx), hGdz (x.1, x.2.2) (hm2 hx), div_eq_mul_inv]
    rfl
  have hΦ1 : ContDiffOn ℝ 1 (fderiv ℝ Φ) S := hΦ.fderiv_of_isOpen hSo (by norm_num)
  set Ψ : ℂ × ℂ × ℂ → ℂ := fun q => (fderiv ℝ Φ q (1, 0) + I * fderiv ℝ Φ q (I, 0)) / 2 with hΨd
  have hΨ : ContDiffOn ℝ 1 Ψ S :=
    ((hΦ1.clm_apply contDiffOn_const).add (contDiffOn_const.mul (hΦ1.clm_apply contDiffOn_const))).div_const 2
  have hΨ' : ContinuousOn (fderiv ℝ Ψ) S := hΨ.continuousOn_fderiv_of_isOpen hSo le_rfl
  have hD : ∀ p ∈ upperHalf ×ˢ upperHalf, dz (dzbar fun e => kernelKbar (fun y => e * ν y) p.1 p.2) 0 =
      (fderiv ℝ Ψ (0, p) (1, 0) - I * fderiv ℝ Ψ (0, p) (I, 0)) / 2 := by
    intro p hp
    have hev : (dzbar fun e => kernelKbar (fun y => e * ν y) p.1 p.2) =ᶠ[𝓝 (0 : ℂ)] fun e => Ψ (e, p) := by
      filter_upwards [hUeo.mem_nhds h0Ue] with e he
      have hmem : (e, p) ∈ S := ⟨he, hp⟩
      have hdΦ : DifferentiableAt ℝ Φ (e, p) :=
        (hΦ.differentiableOn (by norm_num) _ hmem).differentiableAt (hSo.mem_nhds hmem)
      have hsl : fderiv ℝ (fun e' => kernelKbar (fun y => e' * ν y) p.1 p.2) e =
          (fderiv ℝ Φ (e, p)).comp (ContinuousLinearMap.inl ℝ ℂ (ℂ × ℂ)) := by
        have e1 : (fun e' => kernelKbar (fun y => e' * ν y) p.1 p.2) = fun e' => Φ (e', p) := rfl
        rw [e1]
        exact (hdΦ.hasFDerivAt.comp e (hasFDerivAt_prodMk_left (𝕜 := ℝ) e p)).fderiv
      show (fderiv ℝ (fun e' => kernelKbar (fun y => e' * ν y) p.1 p.2) e 1 +
        I * fderiv ℝ (fun e' => kernelKbar (fun y => e' * ν y) p.1 p.2) e I) / 2 = _
      rw [hsl]
      rfl
    rw [s7g_f2_dz_congr hev]
    have hmem : ((0 : ℂ), p) ∈ S := ⟨h0Ue, hp⟩
    have hdΨ : DifferentiableAt ℝ Ψ (0, p) :=
      (hΨ.differentiableOn one_ne_zero _ hmem).differentiableAt (hSo.mem_nhds hmem)
    have hsl : fderiv ℝ (fun e => Ψ (e, p)) 0 = (fderiv ℝ Ψ (0, p)).comp (ContinuousLinearMap.inl ℝ ℂ (ℂ × ℂ)) := by
      have e1 : (fun e => Ψ (e, p)) = Ψ ∘ fun e => (e, p) := rfl
      rw [e1]
      exact (hdΨ.hasFDerivAt.comp (0 : ℂ) (hasFDerivAt_prodMk_left (𝕜 := ℝ) (0 : ℂ) p)).fderiv
    show (fderiv ℝ (fun e => Ψ (e, p)) 0 1 - I * fderiv ℝ (fun e => Ψ (e, p)) 0 I) / 2 = _
    rw [hsl]
    rfl
  have hcont : ContinuousOn (fun p : ℂ × ℂ => (fderiv ℝ Ψ (0, p) (1, 0) - I * fderiv ℝ Ψ (0, p) (I, 0)) / 2)
      (upperHalf ×ˢ upperHalf) := by
    have hcm : ContinuousOn (fun p : ℂ × ℂ => fderiv ℝ Ψ (0, p)) (upperHalf ×ˢ upperHalf) :=
      hΨ'.comp (continuous_const.prodMk continuous_id).continuousOn fun p hp => (⟨h0Ue, hp⟩ : ((0 : ℂ), p) ∈ S)
    exact ((hcm.clm_apply continuousOn_const).sub (continuousOn_const.mul (hcm.clm_apply continuousOn_const))).div_const 2
  exact hcont.congr fun p hp => hD p hp

/-- **Off-support pairing.** For `f ∈ L²` vanishing off `𝕌` and `g ∈ L²` vanishing off `𝕃`:
`∫ f(w) ∫ g(ξ)/(ξ - w)² = ∫ g(ξ) ∫ f(w)/(w - ξ)²` (both inner integrals are `-π H`, `hilbertH_pairing_symm_L2`). -/
theorem s7l8_pair_off {f g : ℂ → ℂ} (hfm : Measurable f) (hf2 : MemLp f 2 volume)
    (hf0 : ∀ x, x ∉ upperHalf → f x = 0) (hgm : Measurable g) (hg2 : MemLp g 2 volume)
    (hg0 : ∀ x, x ∉ {ζ : ℂ | ζ.im < 0} → g x = 0) :
    (∫ w, f w * ∫ ξ, g ξ / (ξ - w) ^ 2) = ∫ ξ, g ξ * ∫ w, f w / (w - ξ) ^ 2 := by
  have hUo : IsOpen upperHalf := isOpen_lt continuous_const Complex.continuous_im
  have hLo : IsOpen {ζ : ℂ | ζ.im < 0} := isOpen_lt Complex.continuous_im continuous_const
  have hU := measurableSet_upperHalf_aux
  have hLm : MeasurableSet {ζ : ℂ | ζ.im < 0} := measurableSet_lt Complex.measurable_im measurable_const
  have hg0U : ∀ x ∈ upperHalf, g x = 0 := fun x hx => hg0 x fun h => by
    have h1 : x.im < 0 := h
    have h2 : 0 < x.im := hx
    linarith
  have hf0L : ∀ x ∈ {ζ : ℂ | ζ.im < 0}, f x = 0 := fun x hx => hf0 x fun h => by
    have h1 : x.im < 0 := hx
    have h2 : 0 < x.im := h
    linarith
  have h1 := (ae_restrict_iff' hU).1 (s7l8_off_ae hgm hg2 hUo hg0U)
  have h2 := (ae_restrict_iff' hLm).1 (s7l8_off_ae hfm hf2 hLo hf0L)
  have e1 : (∫ w, f w * ∫ ξ, g ξ / (ξ - w) ^ 2) = ∫ w, f w * (-(π : ℂ) * hilbertH g w) := by
    refine integral_congr_ae ?_
    filter_upwards [h1] with w hw
    by_cases hwU : w ∈ upperHalf
    · rw [hw hwU]
    · rw [hf0 w hwU, zero_mul, zero_mul]
  have e2 : (∫ ξ, g ξ * ∫ w, f w / (w - ξ) ^ 2) = ∫ ξ, g ξ * (-(π : ℂ) * hilbertH f ξ) := by
    refine integral_congr_ae ?_
    filter_upwards [h2] with ξ hξ
    by_cases hξL : ξ ∈ {ζ : ℂ | ζ.im < 0}
    · rw [hξ hξL]
    · rw [hg0 ξ hξL, zero_mul, zero_mul]
  have hp := hilbertH_pairing_symm_L2 hf2 hg2
  have e3 : (∫ w, f w * (-(π : ℂ) * hilbertH g w)) = -(π : ℂ) * ∫ w, f w * hilbertH g w := by
    rw [← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun w => ?_)
    ring
  have e4 : (∫ ξ, g ξ * (-(π : ℂ) * hilbertH f ξ)) = -(π : ℂ) * ∫ ξ, hilbertH f ξ * g ξ := by
    rw [← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun w => ?_)
    ring
  rw [e1, e2, e3, e4, hp]

/-- **Inner `w`-integral of the `I₃` kernel**: for `v ∈ 𝕌`,
`∫_𝕌 μ(w)/(w - z̄)² C(v, w) d²w = -(1/π) ∫ F_z(ξ)/(ξ - v)²` with
`F_z = 1_𝕃 \overline{ν(ξ̄)} · ∫ 1_𝕌 μ/(· - z̄)² /(· - ξ)²`. -/
theorem s7l8_Yinner {μ φ ν ψ : ℂ → ℂ} (hμ : IsHarmonicU μ φ) (hν : IsHarmonicU ν ψ) {z v : ℂ}
    (hz : z ∈ upperHalf) (hv : v ∈ upperHalf) :
    (∫ w in upperHalf, μ w * (1 / (w - conj z) ^ 2) *
      (-(1 / π) * ∫ ξ, {ζ : ℂ | ζ.im < 0}.indicator (fun ξ => conj (ν (conj ξ)) / (ξ - w) ^ 2) ξ / (ξ - v) ^ 2)) =
      -(1 / π) * ∫ ξ, {ζ : ℂ | ζ.im < 0}.indicator (fun ξ => conj (ν (conj ξ))) ξ *
        (∫ w, upperHalf.indicator (fun w => μ w / (w - conj z) ^ 2) w / (w - ξ) ^ 2) / (ξ - v) ^ 2 := by
  obtain ⟨Mμ, hMμ0, hMμ⟩ := harmonicU_bounded hμ
  obtain ⟨Mν, hMν0, hMν⟩ := harmonicU_bounded hν
  have hU := measurableSet_upperHalf_aux
  obtain ⟨ham, -, ha2, -⟩ := s7l8_g_data hμ hMμ hz
  obtain ⟨hkm, hk2, -⟩ := s7l8_kL_data hν hMν hv
  have ha0 : ∀ x, x ∉ upperHalf → upperHalf.indicator (fun w => μ w / (w - conj z) ^ 2) x = 0 :=
    fun x hx => Set.indicator_of_notMem hx _
  have hk0 : ∀ x, x ∉ {ζ : ℂ | ζ.im < 0} →
      {ζ : ℂ | ζ.im < 0}.indicator (fun ξ => conj (ν (conj ξ)) / (ξ - v) ^ 2) x = 0 :=
    fun x hx => Set.indicator_of_notMem hx _
  have hP := s7l8_pair_off ham ha2 ha0 hkm hk2 hk0
  -- symmetry of the kernel in `(v, w)`
  have hsym : ∀ w ξ, {ζ : ℂ | ζ.im < 0}.indicator (fun ξ => conj (ν (conj ξ)) / (ξ - w) ^ 2) ξ / (ξ - v) ^ 2 =
      {ζ : ℂ | ζ.im < 0}.indicator (fun ξ => conj (ν (conj ξ)) / (ξ - v) ^ 2) ξ / (ξ - w) ^ 2 := by
    intro w ξ
    by_cases hξ : ξ ∈ {ζ : ℂ | ζ.im < 0}
    · simp only [Set.indicator_of_mem hξ]
      ring
    · simp only [Set.indicator_of_notMem hξ, zero_div]
  have eL : (∫ w in upperHalf, μ w * (1 / (w - conj z) ^ 2) *
      (-(1 / π) * ∫ ξ, {ζ : ℂ | ζ.im < 0}.indicator (fun ξ => conj (ν (conj ξ)) / (ξ - w) ^ 2) ξ / (ξ - v) ^ 2)) =
      -(1 / π) * ∫ w, upperHalf.indicator (fun w => μ w / (w - conj z) ^ 2) w *
        ∫ ξ, {ζ : ℂ | ζ.im < 0}.indicator (fun ξ => conj (ν (conj ξ)) / (ξ - v) ^ 2) ξ / (ξ - w) ^ 2 := by
    rw [← integral_const_mul, ← integral_indicator hU]
    refine integral_congr_ae (Eventually.of_forall fun w => ?_)
    have hf : (fun ξ => {ζ : ℂ | ζ.im < 0}.indicator (fun ξ => conj (ν (conj ξ)) / (ξ - w) ^ 2) ξ / (ξ - v) ^ 2) =
        fun ξ => {ζ : ℂ | ζ.im < 0}.indicator (fun ξ => conj (ν (conj ξ)) / (ξ - v) ^ 2) ξ / (ξ - w) ^ 2 :=
      funext (hsym w)
    by_cases hw : w ∈ upperHalf
    · simp only [Set.indicator_of_mem hw]
      rw [hf]
      ring
    · simp only [Set.indicator_of_notMem hw]
      ring
  rw [eL, hP]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
  by_cases hξ : ξ ∈ {ζ : ℂ | ζ.im < 0}
  · simp only [Set.indicator_of_mem hξ]
    ring
  · simp only [Set.indicator_of_notMem hξ]
    ring

/-- `∫_S |x - c|⁻⁴ ≤ π/t²` when `S` stays at distance `≥ t` from `c` (`Ch2.s2c_l4_outside_ball`). -/
theorem s7l8_l4 (c : ℂ) {t : ℝ} (ht : 0 < t) {S : Set ℂ} (hS : ∀ x ∈ S, t ≤ ‖x - c‖) :
    (∫⁻ x in S, ‖1 / (x - c) ^ 2‖ₑ ^ 2) ≤ ENNReal.ofReal (π / t ^ 2) := by
  obtain ⟨hi, hv⟩ := Ch2.s2c_l4_outside_ball c ht
  have hT : MeasurableSet {ω : ℂ | t ≤ ‖ω - c‖} := measurableSet_le measurable_const (measurable_id.sub_const _).norm
  calc (∫⁻ x in S, ‖1 / (x - c) ^ 2‖ₑ ^ 2) ≤ ∫⁻ x in {ω : ℂ | t ≤ ‖ω - c‖}, ‖1 / (x - c) ^ 2‖ₑ ^ 2 :=
        lintegral_mono_set fun x hx => hS x hx
    _ = ∫⁻ x in {ω : ℂ | t ≤ ‖ω - c‖}, ENNReal.ofReal ((‖x - c‖ ^ 4)⁻¹) := by
        refine setLIntegral_congr_fun hT fun x _ => ?_
        rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _), norm_div, norm_one, norm_pow, one_div, inv_pow,
          ← pow_mul]
    _ = ENNReal.ofReal (∫ x in {ω : ℂ | t ≤ ‖ω - c‖}, (‖x - c‖ ^ 4)⁻¹) :=
        (ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall fun x => by positivity)).symm
    _ = ENNReal.ofReal (π / t ^ 2) := by rw [hv]

/-- `‖p‖ ‖q‖ ≤ ‖p‖²/(2s) + s ‖q‖²/2` in `ℝ≥0∞`. -/
theorem s7l8_amgm (p q : ℂ) {s : ℝ} (hs : 0 < s) :
    ‖p‖ₑ * ‖q‖ₑ ≤ ENNReal.ofReal (1 / (2 * s)) * ‖p‖ₑ ^ 2 + ENNReal.ofReal (s / 2) * ‖q‖ₑ ^ 2 := by
  rw [← ofReal_norm p, ← ofReal_norm q, ← ENNReal.ofReal_mul (norm_nonneg _), ← ENNReal.ofReal_pow (norm_nonneg _),
    ← ENNReal.ofReal_pow (norm_nonneg _), ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_add (by positivity) (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [show 1 / (2 * s) * ‖p‖ ^ 2 + s / 2 * ‖q‖ ^ 2 = (‖p‖ ^ 2 + s ^ 2 * ‖q‖ ^ 2) / (2 * s) by field_simp,
    le_div_iff₀ (by positivity)]
  nlinarith [sq_nonneg (‖p‖ - s * ‖q‖)]

/-- Joint measurability of the `I₃` kernel `(w, v) ↦ ∫ k_w(ξ)/(ξ - v)²`. -/
theorem s7l8_Cf_meas {ν ψ : ℂ → ℂ} (hν : IsHarmonicU ν ψ) :
    Measurable (fun p : ℂ × ℂ => ∫ ξ, {ζ : ℂ | ζ.im < 0}.indicator
      (fun ξ => conj (ν (conj ξ)) / (ξ - p.1) ^ 2) ξ / (ξ - p.2) ^ 2) := by
  have hLm : MeasurableSet {ζ : ℂ | ζ.im < 0} := measurableSet_lt Complex.measurable_im measurable_const
  have hcU : ∀ ξ ∈ {ζ : ℂ | ζ.im < 0}, conj ξ ∈ upperHalf := fun ξ hξ => by
    show 0 < (conj ξ).im
    rw [Complex.conj_im]
    have : ξ.im < 0 := hξ
    linarith
  have hνc := harmonicU_continuousOn hν
  have hnc : ContinuousOn (fun ξ => conj (ν (conj ξ))) {ζ : ℂ | ζ.im < 0} :=
    Complex.continuous_conj.comp_continuousOn (hνc.comp Complex.continuous_conj.continuousOn hcU)
  have hnm : Measurable ({ζ : ℂ | ζ.im < 0}.indicator fun ξ => conj (ν (conj ξ))) := by
    rw [← Set.piecewise_eq_indicator]
    exact hnc.measurable_piecewise continuousOn_const hLm
  have he : (fun p : ℂ × ℂ => ∫ ξ, {ζ : ℂ | ζ.im < 0}.indicator
      (fun ξ => conj (ν (conj ξ)) / (ξ - p.1) ^ 2) ξ / (ξ - p.2) ^ 2) = fun p : ℂ × ℂ => ∫ ξ,
        {ζ : ℂ | ζ.im < 0}.indicator (fun ξ => conj (ν (conj ξ))) ξ / (ξ - p.1) ^ 2 / (ξ - p.2) ^ 2 := by
    funext p
    refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
    by_cases hξ : ξ ∈ {ζ : ℂ | ζ.im < 0}
    · simp only [Set.indicator_of_mem hξ]
    · simp only [Set.indicator_of_notMem hξ, zero_div]
  rw [he]
  have hF : Measurable (fun q : (ℂ × ℂ) × ℂ => {ζ : ℂ | ζ.im < 0}.indicator (fun ξ => conj (ν (conj ξ))) q.2 /
      (q.2 - q.1.1) ^ 2 / (q.2 - q.1.2) ^ 2) :=
    ((hnm.comp measurable_snd).div ((measurable_snd.sub (measurable_fst.comp measurable_fst)).pow_const 2)).div
      ((measurable_snd.sub (measurable_snd.comp measurable_fst)).pow_const 2)
  exact (hF.stronglyMeasurable.integral_prod_right' (ν := volume)).measurable

/-- **Fubini for `I₃`**: `(w, v) ↦ μ(w)/(w - z̄)² · ν(v)/(z̄ - v)² · C(v, w)` is integrable on `𝕌 × 𝕌`
(Cauchy–Schwarz in `v`, `‖C(·, w)‖₂ ≲ 1/Im w`, then `|μ|/Im w ∈ L²` against `|w - z̄|⁻²`). -/
theorem s7l8_Yswap {μ φ ν ψ : ℂ → ℂ} (hμ : IsHarmonicU μ φ)
    (hμ2 : (∫⁻ u in upperHalf, ‖μ u‖ₑ ^ 2 * ENNReal.ofReal (rhoU u)) < ∞) (hν : IsHarmonicU ν ψ) {z : ℂ}
    (hz : z ∈ upperHalf) :
    Integrable (fun p : ℂ × ℂ => μ p.1 * (1 / (p.1 - conj z) ^ 2) * (ν p.2 * (1 / (conj z - p.2) ^ 2) *
      (-(1 / π) * ∫ ξ, {ζ : ℂ | ζ.im < 0}.indicator (fun ξ => conj (ν (conj ξ)) / (ξ - p.1) ^ 2) ξ /
        (ξ - p.2) ^ 2))) ((volume.restrict upperHalf).prod (volume.restrict upperHalf)) := by
  obtain ⟨Mν, hMν0, hMν⟩ := harmonicU_bounded hν
  have hU := measurableSet_upperHalf_aux
  have hzim : 0 < z.im := hz
  have hμc := harmonicU_continuousOn hμ
  have hνc := harmonicU_continuousOn hν
  have hneU : ∀ w ∈ upperHalf, w - conj z ≠ 0 := fun w hw h => by
    have h' := congrArg Complex.im h
    have : 0 < w.im := hw
    simp at h'
    linarith
  have hneU' : ∀ w ∈ upperHalf, conj z - w ≠ 0 := fun w hw h => hneU w hw (by linear_combination -h)
  have hAc : ContinuousOn (fun w => μ w * (1 / (w - conj z) ^ 2)) upperHalf :=
    hμc.mul (continuousOn_const.div (by fun_prop) fun w hw => pow_ne_zero 2 (hneU w hw))
  have hBc : ContinuousOn (fun v => ν v * (1 / (conj z - v) ^ 2)) upperHalf :=
    hνc.mul (continuousOn_const.div (by fun_prop) fun w hw => pow_ne_zero 2 (hneU' w hw))
  have hprod : (volume.restrict upperHalf).prod (volume.restrict upperHalf) =
      (volume.prod volume).restrict (upperHalf ×ˢ upperHalf) := Measure.prod_restrict _ _
  have hCm := (measurable_const (a := (-(1 / π : ℂ)))).mul (s7l8_Cf_meas hν)
  have hfm : AEStronglyMeasurable (fun p : ℂ × ℂ => μ p.1 * (1 / (p.1 - conj z) ^ 2) *
      (ν p.2 * (1 / (conj z - p.2) ^ 2) * (-(1 / π) * ∫ ξ, {ζ : ℂ | ζ.im < 0}.indicator
        (fun ξ => conj (ν (conj ξ)) / (ξ - p.1) ^ 2) ξ / (ξ - p.2) ^ 2)))
      ((volume.restrict upperHalf).prod (volume.restrict upperHalf)) := by
    rw [hprod]
    have hA : AEStronglyMeasurable (fun p : ℂ × ℂ => μ p.1 * (1 / (p.1 - conj z) ^ 2))
        ((volume.prod volume).restrict (upperHalf ×ˢ upperHalf)) :=
      (hAc.comp continuous_fst.continuousOn fun p hp => hp.1).aestronglyMeasurable (hU.prod hU)
    have hB : AEStronglyMeasurable (fun p : ℂ × ℂ => ν p.2 * (1 / (conj z - p.2) ^ 2))
        ((volume.prod volume).restrict (upperHalf ×ˢ upperHalf)) :=
      (hBc.comp continuous_snd.continuousOn fun p hp => hp.2).aestronglyMeasurable (hU.prod hU)
    exact hA.mul (hB.mul hCm.aestronglyMeasurable)
  refine ⟨hfm, ?_⟩
  show (∫⁻ p, ‖μ p.1 * (1 / (p.1 - conj z) ^ 2) * (ν p.2 * (1 / (conj z - p.2) ^ 2) *
      (-(1 / π) * ∫ ξ, {ζ : ℂ | ζ.im < 0}.indicator (fun ξ => conj (ν (conj ξ)) / (ξ - p.1) ^ 2) ξ /
        (ξ - p.2) ^ 2))‖ₑ ∂((volume.restrict upperHalf).prod (volume.restrict upperHalf))) < ∞
  rw [lintegral_prod _ hfm.aemeasurable.enorm]
  -- the `v`-integral
  obtain ⟨-, -, -, hbb⟩ := s7l8_g_data hν hMν hz
  have hBb : (∫⁻ v in upperHalf, ‖ν v * (1 / (conj z - v) ^ 2)‖ₑ ^ 2) ≤
      ENNReal.ofReal (Mν ^ 2 * (π / z.im ^ 2)) := by
    refine le_trans (le_of_eq ?_) hbb
    rw [s7l8_ind_lint]
    refine setLIntegral_congr_fun hU fun v hv => ?_
    congr 2
    have := hneU v hv
    have := hneU' v hv
    field_simp
    ring
  have hinner : ∀ w ∈ upperHalf, (∫⁻ v in upperHalf, ‖ν v * (1 / (conj z - v) ^ 2)‖ₑ *
      ‖-(1 / π : ℂ) * ∫ ξ, {ζ : ℂ | ζ.im < 0}.indicator (fun ξ => conj (ν (conj ξ)) / (ξ - w) ^ 2) ξ /
        (ξ - v) ^ 2‖ₑ) ≤ ENNReal.ofReal ((Mν ^ 2 * (π / z.im ^ 2) + Mν ^ 2 * π) / 2 / w.im) := by
    intro w hw
    have hwim : 0 < w.im := hw
    have hCL := s7l8_C_L2 hν hMν hw
    have hc : ‖(-(1 / π) : ℂ)‖ₑ ^ 2 = ENNReal.ofReal ((1 / π) ^ 2) := by
      rw [enorm_neg, ← ofReal_norm, show ((1 / π : ℂ)) = ((1 / π : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
        Real.norm_of_nonneg (by positivity), ← ENNReal.ofReal_pow (by positivity)]
    have hbm : AEMeasurable (fun v => ENNReal.ofReal (1 / (2 * w.im)) * ‖ν v * (1 / (conj z - v) ^ 2)‖ₑ ^ 2)
        (volume.restrict upperHalf) :=
      ((hBc.aemeasurable hU).enorm.pow_const 2).const_mul _
    calc _ ≤ ∫⁻ v in upperHalf, (ENNReal.ofReal (1 / (2 * w.im)) * ‖ν v * (1 / (conj z - v) ^ 2)‖ₑ ^ 2 +
          ENNReal.ofReal (w.im / 2) * ‖-(1 / π : ℂ) * ∫ ξ, {ζ : ℂ | ζ.im < 0}.indicator
            (fun ξ => conj (ν (conj ξ)) / (ξ - w) ^ 2) ξ / (ξ - v) ^ 2‖ₑ ^ 2) :=
          lintegral_mono fun v => s7l8_amgm _ _ hwim
      _ = ENNReal.ofReal (1 / (2 * w.im)) * (∫⁻ v in upperHalf, ‖ν v * (1 / (conj z - v) ^ 2)‖ₑ ^ 2) +
          ENNReal.ofReal (w.im / 2) * (ENNReal.ofReal ((1 / π) ^ 2) * ∫⁻ v in upperHalf,
            ‖∫ ξ, {ζ : ℂ | ζ.im < 0}.indicator (fun ξ => conj (ν (conj ξ)) / (ξ - w) ^ 2) ξ / (ξ - v) ^ 2‖ₑ ^ 2) := by
          rw [lintegral_add_left' hbm, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
            lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
          simp only [enorm_mul, mul_pow, hc]
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      _ ≤ ENNReal.ofReal (1 / (2 * w.im)) * ENNReal.ofReal (Mν ^ 2 * (π / z.im ^ 2)) +
          ENNReal.ofReal (w.im / 2) * (ENNReal.ofReal ((1 / π) ^ 2) *
            (ENNReal.ofReal (π ^ 2) * ENNReal.ofReal (Mν ^ 2 * (π / w.im ^ 2)))) := by
          gcongr
      _ = ENNReal.ofReal ((Mν ^ 2 * (π / z.im ^ 2) + Mν ^ 2 * π) / 2 / w.im) := by
          rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
            ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
            ← ENNReal.ofReal_add (by positivity) (by positivity)]
          congr 1
          field_simp
  set K : ℝ := (Mν ^ 2 * (π / z.im ^ 2) + Mν ^ 2 * π) / 2 with hKd
  have hK0 : 0 ≤ K := by positivity
  have hpt : ∀ w ∈ upperHalf, (∫⁻ v in upperHalf, ‖μ w * (1 / (w - conj z) ^ 2) *
      (ν v * (1 / (conj z - v) ^ 2) * (-(1 / π) * ∫ ξ, {ζ : ℂ | ζ.im < 0}.indicator
        (fun ξ => conj (ν (conj ξ)) / (ξ - w) ^ 2) ξ / (ξ - v) ^ 2))‖ₑ) ≤
      ENNReal.ofReal (K / 2) * (‖μ w‖ₑ ^ 2 * ENNReal.ofReal (rhoU w) + ‖1 / (w - conj z) ^ 2‖ₑ ^ 2) := by
    intro w hw
    have hwim : 0 < w.im := hw
    simp only [enorm_mul]
    rw [lintegral_const_mul' _ _ (ENNReal.mul_ne_top enorm_ne_top enorm_ne_top)]
    calc ‖μ w‖ₑ * ‖1 / (w - conj z) ^ 2‖ₑ * ∫⁻ v in upperHalf, ‖ν v‖ₑ * ‖1 / (conj z - v) ^ 2‖ₑ *
          (‖-(1 / π : ℂ)‖ₑ * ‖∫ ξ, {ζ : ℂ | ζ.im < 0}.indicator
            (fun ξ => conj (ν (conj ξ)) / (ξ - w) ^ 2) ξ / (ξ - v) ^ 2‖ₑ)
        ≤ ‖μ w‖ₑ * ‖1 / (w - conj z) ^ 2‖ₑ * ENNReal.ofReal (K / w.im) := by
          refine mul_le_mul_right ?_ _
          refine le_trans (le_of_eq ?_) (hinner w hw)
          refine lintegral_congr fun v => ?_
          rw [enorm_mul, enorm_mul]
      _ ≤ _ := by
          have h1 : ‖μ w‖ₑ * ‖1 / (w - conj z) ^ 2‖ₑ * ENNReal.ofReal (K / w.im) =
              ENNReal.ofReal K * (‖(μ w) * (1 / w.im : ℝ)‖ₑ * ‖1 / (w - conj z) ^ 2‖ₑ) := by
            rw [enorm_mul, ← ofReal_norm ((1 / w.im : ℝ) : ℂ), Complex.norm_real,
              Real.norm_of_nonneg (by positivity), div_eq_mul_one_div K, ENNReal.ofReal_mul hK0]
            ring
          rw [h1]
          have h2 := s7l8_amgm ((μ w) * (1 / w.im : ℝ)) (1 / (w - conj z) ^ 2) (s := 1) one_pos
          have h3 : ‖(μ w) * (1 / w.im : ℝ)‖ₑ ^ 2 = ‖μ w‖ₑ ^ 2 * ENNReal.ofReal (rhoU w) := by
            rw [enorm_mul, mul_pow, ← ofReal_norm ((1 / w.im : ℝ) : ℂ), Complex.norm_real,
              Real.norm_of_nonneg (by positivity), ← ENNReal.ofReal_pow (by positivity)]
            congr 2
            unfold rhoU
            field_simp
          rw [h3] at h2
          calc ENNReal.ofReal K * (‖(μ w) * (1 / w.im : ℝ)‖ₑ * ‖1 / (w - conj z) ^ 2‖ₑ)
              ≤ ENNReal.ofReal K * (ENNReal.ofReal (1 / (2 * 1)) * (‖μ w‖ₑ ^ 2 * ENNReal.ofReal (rhoU w)) +
                  ENNReal.ofReal (1 / 2) * ‖1 / (w - conj z) ^ 2‖ₑ ^ 2) := mul_le_mul_right h2 _
            _ = _ := by
                rw [show (1 / (2 * 1) : ℝ) = 1 / 2 by norm_num, ← mul_add, ← mul_assoc,
                  ← ENNReal.ofReal_mul hK0]
                congr 2
                ring
  have hzl : (∫⁻ w in upperHalf, ‖1 / (w - conj z) ^ 2‖ₑ ^ 2) ≤ ENNReal.ofReal (π / z.im ^ 2) := by
    refine s7l8_l4 (conj z) hzim fun w hw => ?_
    have h1 := Complex.abs_im_le_norm (w - conj z)
    have h2 : (w - conj z).im = w.im + z.im := by simp
    have : 0 < w.im := hw
    rw [h2, abs_of_pos (by linarith)] at h1
    linarith
  have hmμ : AEMeasurable (fun w => ‖μ w‖ₑ ^ 2 * ENNReal.ofReal (rhoU w)) (volume.restrict upperHalf) :=
    ((hμc.aemeasurable hU).enorm.pow_const 2).mul (by unfold rhoU; fun_prop)
  calc (∫⁻ w in upperHalf, ∫⁻ v in upperHalf, _) ≤
      ∫⁻ w in upperHalf, ENNReal.ofReal (K / 2) * (‖μ w‖ₑ ^ 2 * ENNReal.ofReal (rhoU w) +
        ‖1 / (w - conj z) ^ 2‖ₑ ^ 2) := setLIntegral_mono' hU hpt
    _ = ENNReal.ofReal (K / 2) * ((∫⁻ w in upperHalf, ‖μ w‖ₑ ^ 2 * ENNReal.ofReal (rhoU w)) +
        ∫⁻ w in upperHalf, ‖1 / (w - conj z) ^ 2‖ₑ ^ 2) := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_add_left' hmμ]
    _ < ∞ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top
        (ENNReal.add_lt_top.2 ⟨hμ2, hzl.trans_lt ENNReal.ofReal_lt_top⟩)

/-- `∫_𝕌 ∫_𝕌 |μ(u)|²/|u - z̄|⁴ d²u d²z ≤ π ‖μ‖²_{L²(ρ)}`. -/
theorem s7l8_TA {μ φ : ℂ → ℂ} (hμ : IsHarmonicU μ φ) :
    (∫⁻ z in upperHalf, ∫⁻ u in upperHalf, ‖μ u * (1 / (u - conj z) ^ 2)‖ₑ ^ 2) ≤
      ENNReal.ofReal π * ∫⁻ u in upperHalf, ‖μ u‖ₑ ^ 2 * ENNReal.ofReal (rhoU u) := by
  have hU := measurableSet_upperHalf_aux
  have hμc := harmonicU_continuousOn hμ
  have hprod : (volume.restrict upperHalf).prod (volume.restrict upperHalf) =
      (volume.prod volume).restrict (upperHalf ×ˢ upperHalf) := Measure.prod_restrict _ _
  have hne : ∀ p ∈ upperHalf ×ˢ upperHalf, (p.2 - conj p.1 : ℂ) ≠ 0 := fun p hp h => by
    have h' := congrArg Complex.im h
    have h1 : 0 < p.1.im := hp.1
    have h2 : 0 < p.2.im := hp.2
    simp at h'
    linarith
  have hc : ContinuousOn (fun p : ℂ × ℂ => μ p.2 * (1 / (p.2 - conj p.1) ^ 2)) (upperHalf ×ˢ upperHalf) :=
    (hμc.comp continuous_snd.continuousOn fun p hp => hp.2).mul
      (continuousOn_const.div (by fun_prop) fun p hp => pow_ne_zero 2 (hne p hp))
  have hm : AEMeasurable (Function.uncurry fun z u => ‖μ u * (1 / (u - conj z) ^ 2)‖ₑ ^ 2)
      ((volume.restrict upperHalf).prod (volume.restrict upperHalf)) := by
    rw [hprod]
    exact ((hc.aemeasurable (hU.prod hU)).enorm.pow_const 2)
  rw [lintegral_lintegral_swap hm]
  have hpt : ∀ u ∈ upperHalf, (∫⁻ z in upperHalf, ‖μ u * (1 / (u - conj z) ^ 2)‖ₑ ^ 2) ≤
      ENNReal.ofReal π * (‖μ u‖ₑ ^ 2 * ENNReal.ofReal (rhoU u)) := by
    intro u hu
    have huim : 0 < u.im := hu
    have e : ∀ z, ‖μ u * (1 / (u - conj z) ^ 2)‖ₑ ^ 2 = ‖μ u‖ₑ ^ 2 * ‖1 / (z - conj u) ^ 2‖ₑ ^ 2 := fun z => by
      rw [enorm_mul, mul_pow]
      congr 2
      rw [← ofReal_norm, ← ofReal_norm, norm_div, norm_div, norm_pow, norm_pow,
        show u - conj z = conj (conj u - z) by simp, Complex.norm_conj, norm_sub_rev]
    simp only [e]
    rw [lintegral_const_mul' _ _ (ENNReal.pow_ne_top enorm_ne_top)]
    have hl := s7l8_l4 (conj u) huim (S := upperHalf) fun z hz => by
      have h1 := Complex.abs_im_le_norm (z - conj u)
      have h2 : (z - conj u).im = z.im + u.im := by simp
      have : 0 < z.im := hz
      rw [h2, abs_of_pos (by linarith)] at h1
      linarith
    calc ‖μ u‖ₑ ^ 2 * ∫⁻ z in upperHalf, ‖1 / (z - conj u) ^ 2‖ₑ ^ 2 ≤ ‖μ u‖ₑ ^ 2 * ENNReal.ofReal (π / u.im ^ 2) :=
          mul_le_mul_right hl _
      _ = _ := by
          rw [show π / u.im ^ 2 = π * rhoU u by unfold rhoU; ring, ENNReal.ofReal_mul Real.pi_pos.le]
          ring
  calc _ ≤ ∫⁻ u in upperHalf, ENNReal.ofReal π * (‖μ u‖ₑ ^ 2 * ENNReal.ofReal (rhoU u)) := setLIntegral_mono' hU hpt
    _ = _ := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

/-- `1_𝕌 μ/(· - ξ)²` for `ξ ∈ 𝕃`: measurable, `L²`, `∫ |·|² = ∫_𝕌 |μ|² |· - ξ|⁻⁴`. -/
theorem s7l8_hxi {μ φ : ℂ → ℂ} (hμ : IsHarmonicU μ φ) {ξ : ℂ} (hξ : ξ.im < 0) :
    Measurable (upperHalf.indicator fun w => μ w / (w - ξ) ^ 2) ∧
      MemLp (upperHalf.indicator fun w => μ w / (w - ξ) ^ 2) 2 volume ∧
      (∫⁻ w, ‖upperHalf.indicator (fun w => μ w / (w - ξ) ^ 2) w‖ₑ ^ 2) =
        ∫⁻ w in upperHalf, ‖μ w‖ₑ ^ 2 * ‖1 / (w - ξ) ^ 2‖ₑ ^ 2 := by
  obtain ⟨M, hM0, hM⟩ := harmonicU_bounded hμ
  have hU := measurableSet_upperHalf_aux
  have hμc := harmonicU_continuousOn hμ
  have hne : ∀ w ∈ upperHalf, w - ξ ≠ 0 := fun w hw h => by
    have h' := congrArg Complex.im h
    have : 0 < w.im := hw
    simp only [Complex.sub_im, Complex.zero_im] at h'
    linarith
  have hm := s7l8_ind_meas (hμc.div (by fun_prop) fun w hw => pow_ne_zero 2 (hne w hw))
  have he : (∫⁻ w, ‖upperHalf.indicator (fun w => μ w / (w - ξ) ^ 2) w‖ₑ ^ 2) =
      ∫⁻ w in upperHalf, ‖μ w‖ₑ ^ 2 * ‖1 / (w - ξ) ^ 2‖ₑ ^ 2 := by
    rw [s7l8_ind_lint]
    refine setLIntegral_congr_fun hU fun w _ => ?_
    rw [div_eq_mul_one_div, enorm_mul, mul_pow]
  refine ⟨hm, s7l8_memLp2 hm.aestronglyMeasurable ?_, he⟩
  rw [he]
  have hl := s7l8_l4 ξ (t := -ξ.im) (by linarith) (S := upperHalf) fun w hw => by
    have h1 := Complex.abs_im_le_norm (w - ξ)
    have h2 : (w - ξ).im = w.im - ξ.im := by simp
    have : 0 < w.im := hw
    rw [h2, abs_of_pos (by linarith)] at h1
    linarith
  calc (∫⁻ w in upperHalf, ‖μ w‖ₑ ^ 2 * ‖1 / (w - ξ) ^ 2‖ₑ ^ 2)
      ≤ ∫⁻ w in upperHalf, ENNReal.ofReal (M ^ 2) * ‖1 / (w - ξ) ^ 2‖ₑ ^ 2 := by
        refine setLIntegral_mono' hU fun w hw => ?_
        refine mul_le_mul_left ?_ _
        rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _)]
        exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (norm_nonneg _) (hM w hw) 2)
    _ = ENNReal.ofReal (M ^ 2) * ∫⁻ w in upperHalf, ‖1 / (w - ξ) ^ 2‖ₑ ^ 2 :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ < ∞ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top (hl.trans_lt ENNReal.ofReal_lt_top)

/-- `∫_𝕌 ∫_𝕃 |E_z(ξ)|² d²ξ d²z ≤ π³ ‖μ‖²_{L²(ρ)}` with `E_z(ξ) = ∫ 1_𝕌 μ/(· - z̄)² /(· - ξ)²` (off-support
Beurling bounds in `z̄`, then in `ξ`). -/
theorem s7l8_TE {μ φ : ℂ → ℂ} (hμ : IsHarmonicU μ φ) :
    (∫⁻ z in upperHalf, ∫⁻ ξ in {ζ : ℂ | ζ.im < 0},
      ‖∫ w, upperHalf.indicator (fun w => μ w / (w - conj z) ^ 2) w / (w - ξ) ^ 2‖ₑ ^ 2) ≤
      ENNReal.ofReal (π ^ 2) * (ENNReal.ofReal π * ∫⁻ u in upperHalf, ‖μ u‖ₑ ^ 2 * ENNReal.ofReal (rhoU u)) := by
  have hU := measurableSet_upperHalf_aux
  have hLm : MeasurableSet {ζ : ℂ | ζ.im < 0} := measurableSet_lt Complex.measurable_im measurable_const
  have hLo : IsOpen {ζ : ℂ | ζ.im < 0} := isOpen_lt Complex.continuous_im continuous_const
  have hμc := harmonicU_continuousOn hμ
  have hμm : Measurable (upperHalf.indicator μ) := s7l8_ind_meas hμc
  -- joint measurability of `E`
  have hEe : ∀ z ξ : ℂ, (∫ w, upperHalf.indicator (fun w => μ w / (w - conj z) ^ 2) w / (w - ξ) ^ 2) =
      ∫ w, upperHalf.indicator μ w / (w - conj z) ^ 2 / (w - ξ) ^ 2 := fun z ξ => by
    refine integral_congr_ae (Eventually.of_forall fun w => ?_)
    by_cases hw : w ∈ upperHalf
    · simp only [Set.indicator_of_mem hw]
    · simp only [Set.indicator_of_notMem hw, zero_div]
  have hEm : Measurable (fun p : ℂ × ℂ => ∫ w, upperHalf.indicator μ w / (w - conj p.1) ^ 2 / (w - p.2) ^ 2) := by
    have hF : Measurable (fun q : (ℂ × ℂ) × ℂ => upperHalf.indicator μ q.2 / (q.2 - conj q.1.1) ^ 2 /
        (q.2 - q.1.2) ^ 2) :=
      ((hμm.comp measurable_snd).div ((measurable_snd.sub
        (Complex.continuous_conj.measurable.comp (measurable_fst.comp measurable_fst))).pow_const 2)).div
        ((measurable_snd.sub (measurable_snd.comp measurable_fst)).pow_const 2)
    exact (hF.stronglyMeasurable.integral_prod_right' (ν := volume)).measurable
  simp only [hEe]
  have hm : AEMeasurable (Function.uncurry fun z ξ =>
      ‖∫ w, upperHalf.indicator μ w / (w - conj z) ^ 2 / (w - ξ) ^ 2‖ₑ ^ 2)
      ((volume.restrict upperHalf).prod (volume.restrict {ζ : ℂ | ζ.im < 0})) :=
    (hEm.enorm.pow_const 2).aemeasurable
  rw [lintegral_lintegral_swap hm]
  -- fixed `ξ ∈ 𝕃`
  have hpt : ∀ ξ ∈ {ζ : ℂ | ζ.im < 0},
      (∫⁻ z in upperHalf, ‖∫ w, upperHalf.indicator μ w / (w - conj z) ^ 2 / (w - ξ) ^ 2‖ₑ ^ 2) ≤
        ENNReal.ofReal (π ^ 2) * ∫⁻ w in upperHalf, ‖μ w‖ₑ ^ 2 * ‖1 / (w - ξ) ^ 2‖ₑ ^ 2 := by
    intro ξ hξ
    have hξ' : ξ.im < 0 := hξ
    obtain ⟨hhm, hh2, hhe⟩ := s7l8_hxi hμ hξ'
    have h0 : ∀ x ∈ {ζ : ℂ | ζ.im < 0}, upperHalf.indicator (fun w => μ w / (w - ξ) ^ 2) x = 0 :=
      fun x hx => Set.indicator_of_notMem (fun h => by
        have h1 : x.im < 0 := hx
        have h2 : 0 < x.im := h
        linarith) _
    have hL2 := s7l8_off_L2 hhm hh2 hLo h0
    have e : ∀ z, (∫ w, upperHalf.indicator μ w / (w - conj z) ^ 2 / (w - ξ) ^ 2) =
        ∫ w, upperHalf.indicator (fun w => μ w / (w - ξ) ^ 2) w / (w - conj z) ^ 2 := fun z => by
      refine integral_congr_ae (Eventually.of_forall fun w => ?_)
      by_cases hw : w ∈ upperHalf
      · simp only [Set.indicator_of_mem hw]
        ring
      · simp only [Set.indicator_of_notMem hw, zero_div]
    simp only [e]
    rw [s7l8_conj_lint (fun η => ‖∫ w, upperHalf.indicator (fun w => μ w / (w - ξ) ^ 2) w / (w - η) ^ 2‖ₑ ^ 2)]
    rw [← hhe]
    exact hL2
  have hprod2 : (volume.restrict {ζ : ℂ | ζ.im < 0}).prod (volume.restrict upperHalf) =
      (volume.prod volume).restrict ({ζ : ℂ | ζ.im < 0} ×ˢ upperHalf) := Measure.prod_restrict _ _
  have hne : ∀ p ∈ {ζ : ℂ | ζ.im < 0} ×ˢ upperHalf, (p.2 - p.1 : ℂ) ≠ 0 := fun p hp h => by
    have h' := congrArg Complex.im h
    have h1 : p.1.im < 0 := hp.1
    have h2 : 0 < p.2.im := hp.2
    simp only [Complex.sub_im, Complex.zero_im] at h'
    linarith
  have h1 : ContinuousOn (fun p : ℂ × ℂ => μ p.2) ({ζ : ℂ | ζ.im < 0} ×ˢ upperHalf) :=
    hμc.comp continuous_snd.continuousOn fun p hp => hp.2
  have h2 : ContinuousOn (fun p : ℂ × ℂ => 1 / (p.2 - p.1) ^ 2) ({ζ : ℂ | ζ.im < 0} ×ˢ upperHalf) :=
    continuousOn_const.div (by fun_prop) fun p hp => pow_ne_zero 2 (hne p hp)
  have hm2 : AEMeasurable (Function.uncurry fun ξ w => ‖μ w‖ₑ ^ 2 * ‖1 / (w - ξ) ^ 2‖ₑ ^ 2)
      ((volume.restrict {ζ : ℂ | ζ.im < 0}).prod (volume.restrict upperHalf)) := by
    rw [hprod2]
    exact ((h1.aemeasurable (hLm.prod hU)).enorm.pow_const 2).mul
      ((h2.aemeasurable (hLm.prod hU)).enorm.pow_const 2)
  calc _ ≤ ∫⁻ ξ in {ζ : ℂ | ζ.im < 0}, ENNReal.ofReal (π ^ 2) *
        ∫⁻ w in upperHalf, ‖μ w‖ₑ ^ 2 * ‖1 / (w - ξ) ^ 2‖ₑ ^ 2 := setLIntegral_mono' hLm hpt
    _ = ENNReal.ofReal (π ^ 2) * ∫⁻ w in upperHalf, ∫⁻ ξ in {ζ : ℂ | ζ.im < 0},
        ‖μ w‖ₑ ^ 2 * ‖1 / (w - ξ) ^ 2‖ₑ ^ 2 := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_lintegral_swap hm2]
    _ ≤ ENNReal.ofReal (π ^ 2) * ∫⁻ w in upperHalf, ENNReal.ofReal π * (‖μ w‖ₑ ^ 2 * ENNReal.ofReal (rhoU w)) := by
        refine mul_le_mul_right (setLIntegral_mono' hU fun w hw => ?_) _
        have hwim : 0 < w.im := hw
        rw [lintegral_const_mul' _ _ (ENNReal.pow_ne_top enorm_ne_top)]
        have e : ∀ ξ, ‖1 / (w - ξ) ^ 2‖ₑ ^ 2 = ‖1 / (ξ - w) ^ 2‖ₑ ^ 2 := fun ξ => by rw [← neg_sub, neg_sq]
        simp only [e]
        have hl := s7l8_l4 w hwim (S := {ζ : ℂ | ζ.im < 0}) fun ξ hξ => by
          have h1 := Complex.abs_im_le_norm (ξ - w)
          have h2 : (ξ - w).im = ξ.im - w.im := by simp
          have : ξ.im < 0 := hξ
          rw [h2, abs_of_neg (by linarith)] at h1
          linarith
        calc ‖μ w‖ₑ ^ 2 * ∫⁻ ξ in {ζ : ℂ | ζ.im < 0}, ‖1 / (ξ - w) ^ 2‖ₑ ^ 2
            ≤ ‖μ w‖ₑ ^ 2 * ENNReal.ofReal (π / w.im ^ 2) := mul_le_mul_right hl _
          _ = _ := by
              rw [show π / w.im ^ 2 = π * rhoU w by unfold rhoU; ring, ENNReal.ofReal_mul Real.pi_pos.le]
              ring
    _ = _ := by rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]

/-- `(a + b)² ≤ 2 (a² + b²)` in `ℝ≥0∞`. -/
theorem s7l8_sq2 (x y : ℝ≥0∞) : (x + y) ^ 2 ≤ 2 * (x ^ 2 + y ^ 2) := by
  have h := ENNReal.rpow_add_le_mul_rpow_add_rpow x y (p := 2) (by norm_num)
  have e : ∀ t : ℝ≥0∞, t ^ (2 : ℝ) = t ^ 2 := fun t => by
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, ENNReal.rpow_natCast]
  have e2 : (2 : ℝ≥0∞) ^ ((2 : ℝ) - 1) = 2 := by norm_num
  rwa [e, e, e, e2] at h

/-- Explicit bound `∫ |1_𝕌 ν \overline{D₁(z, ·)}|² ≤ M² · 82 π M²/(Im z)²`. -/
theorem s7l8_gz_bd {ν ψ : ℂ → ℂ} (hν : IsHarmonicU ν ψ) {M : ℝ} (hM : ∀ v ∈ upperHalf, ‖ν v‖ ≤ M)
    {z : ℂ} (hz : z ∈ upperHalf) :
    (∫⁻ v, ‖upperHalf.indicator (fun v => ν v * conj (dz (fun e => kernelKbar (fun y => e * ν y) z v) 0)) v‖ₑ ^ 2) ≤
      ENNReal.ofReal (M ^ 2) * ENNReal.ofReal (82 * π * M ^ 2 / z.im ^ 2) := by
  have hU := measurableSet_upperHalf_aux
  rw [s7l8_ind_lint]
  have hle : ∀ v ∈ upperHalf, ‖ν v * conj (dz (fun e => kernelKbar (fun y => e * ν y) z v) 0)‖ₑ ^ 2 ≤
      ENNReal.ofReal (M ^ 2) * ‖dz (fun e => kernelKbar (fun y => e * ν y) z v) 0‖ₑ ^ 2 := by
    intro v hv
    rw [enorm_mul, mul_pow, RCLike.enorm_conj, ← ofReal_norm (ν v), ← ENNReal.ofReal_pow (norm_nonneg _)]
    exact mul_le_mul_left (ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (norm_nonneg _) (hM v hv) 2)) _
  refine (setLIntegral_mono' hU hle).trans ?_
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  exact mul_le_mul_right (s7l8_Dsnd_L2 hν hM hz) _

/-- **(D23) pointwise decomposition**: integrability of `μ K₀ M(·, z)` on `𝕌` and
`∫ μ K₀ M = ∫ μ K₀ H g_z - (1/π) ∫ μ K₀ Y_z`. -/
theorem s7l8_pt_dec {μ φ ν ψ : ℂ → ℂ} (hμ : IsHarmonicU μ φ)
    (hμ2 : (∫⁻ u in upperHalf, ‖μ u‖ₑ ^ 2 * ENNReal.ofReal (rhoU u)) < ∞) (hν : IsHarmonicU ν ψ) {z : ℂ}
    (hz : z ∈ upperHalf) :
    IntegrableOn (fun u => μ u *
      (1 / (u - conj z) ^ 2 * dz (dzbar fun e => kernelKbar (fun y => e * ν y) u z) 0)) upperHalf ∧
    (∫ u in upperHalf, μ u * (1 / (u - conj z) ^ 2 * dz (dzbar fun e => kernelKbar (fun y => e * ν y) u z) 0)) =
      (∫ u in upperHalf, μ u * (1 / (u - conj z) ^ 2) *
        hilbertH (upperHalf.indicator fun v => ν v * conj (dz (fun e => kernelKbar (fun y => e * ν y) z v) 0)) u) -
      (1 / π : ℂ) * ∫ u in upperHalf, μ u * (1 / (u - conj z) ^ 2) * ∫ v in upperHalf, ν v * (1 / (conj z - v) ^ 2) *
        (-(1 / π : ℂ) * ∫ ξ, {ζ : ℂ | ζ.im < 0}.indicator (fun ξ => conj (ν (conj ξ)) / (ξ - u) ^ 2) ξ / (ξ - v) ^ 2) := by
  obtain ⟨Mμ, hMμ0, hMμ⟩ := harmonicU_bounded hμ
  have hU := measurableSet_upperHalf_aux
  obtain ⟨-, -, ha2, -⟩ := s7l8_g_data hμ hMμ hz
  obtain ⟨-, hg2, -⟩ := s7l8_gz hν hz
  have hH2 := (hilbertH_memLp_two hg2).1
  have hX : IntegrableOn (fun u => μ u * (1 / (u - conj z) ^ 2) *
      hilbertH (upperHalf.indicator fun v => ν v * conj (dz (fun e => kernelKbar (fun y => e * ν y) z v) 0)) u)
      upperHalf := by
    refine ((ha2.integrable_mul hH2).integrableOn).congr_fun (fun u hu => ?_) hU
    rw [Pi.mul_apply, Set.indicator_of_mem hu]
    ring
  have hY : IntegrableOn (fun u => μ u * (1 / (u - conj z) ^ 2) * ∫ v in upperHalf, ν v * (1 / (conj z - v) ^ 2) *
      (-(1 / π : ℂ) * ∫ ξ, {ζ : ℂ | ζ.im < 0}.indicator (fun ξ => conj (ν (conj ξ)) / (ξ - u) ^ 2) ξ / (ξ - v) ^ 2))
      upperHalf := by
    refine (s7l8_Yswap hμ hμ2 hν hz).integral_prod_left.congr (Eventually.of_forall fun w => ?_)
    simp only []
    rw [← integral_const_mul]
  have hdec : ∀ᵐ u ∂(volume.restrict upperHalf), μ u *
      (1 / (u - conj z) ^ 2 * dz (dzbar fun e => kernelKbar (fun y => e * ν y) u z) 0) =
      μ u * (1 / (u - conj z) ^ 2) *
        hilbertH (upperHalf.indicator fun v => ν v * conj (dz (fun e => kernelKbar (fun y => e * ν y) z v) 0)) u -
      (1 / π : ℂ) * (μ u * (1 / (u - conj z) ^ 2) * ∫ v in upperHalf, ν v * (1 / (conj z - v) ^ 2) *
        (-(1 / π : ℂ) * ∫ ξ, {ζ : ℂ | ζ.im < 0}.indicator (fun ξ => conj (ν (conj ξ)) / (ξ - u) ^ 2) ξ / (ξ - v) ^ 2)) := by
    filter_upwards [s7l8_M_ae hν hz] with u hu
    rw [hu]
    ring
  refine ⟨(hX.sub (hY.const_mul (1 / π))).congr (by
    filter_upwards [hdec] with u hu
    rw [hu]
    rfl), ?_⟩
  rw [integral_congr_ae hdec, integral_sub hX (hY.const_mul _), integral_const_mul]

/-- **(D23) the `I₃` part after Fubini** (`s7l8_Yswap`, `s7l8_Yinner`). -/
theorem s7l8_pt_Y {μ φ ν ψ : ℂ → ℂ} (hμ : IsHarmonicU μ φ)
    (hμ2 : (∫⁻ u in upperHalf, ‖μ u‖ₑ ^ 2 * ENNReal.ofReal (rhoU u)) < ∞) (hν : IsHarmonicU ν ψ) {z : ℂ}
    (hz : z ∈ upperHalf) :
    (∫ u in upperHalf, μ u * (1 / (u - conj z) ^ 2) * ∫ v in upperHalf, ν v * (1 / (conj z - v) ^ 2) *
        (-(1 / π : ℂ) * ∫ ξ, {ζ : ℂ | ζ.im < 0}.indicator (fun ξ => conj (ν (conj ξ)) / (ξ - u) ^ 2) ξ / (ξ - v) ^ 2)) =
      ∫ v in upperHalf, ν v * (1 / (conj z - v) ^ 2) * (-(1 / π : ℂ) * ∫ ξ,
        {ζ : ℂ | ζ.im < 0}.indicator (fun ξ => conj (ν (conj ξ))) ξ *
          (∫ w, upperHalf.indicator (fun w => μ w / (w - conj z) ^ 2) w / (w - ξ) ^ 2) / (ξ - v) ^ 2) := by
  have hU := measurableSet_upperHalf_aux
  have hS := s7l8_Yswap hμ hμ2 hν hz
  have e1 : (∫ u in upperHalf, μ u * (1 / (u - conj z) ^ 2) * ∫ v in upperHalf, ν v * (1 / (conj z - v) ^ 2) *
      (-(1 / π : ℂ) * ∫ ξ, {ζ : ℂ | ζ.im < 0}.indicator (fun ξ => conj (ν (conj ξ)) / (ξ - u) ^ 2) ξ / (ξ - v) ^ 2)) =
      ∫ u in upperHalf, ∫ v in upperHalf, μ u * (1 / (u - conj z) ^ 2) * (ν v * (1 / (conj z - v) ^ 2) *
        (-(1 / π : ℂ) * ∫ ξ, {ζ : ℂ | ζ.im < 0}.indicator (fun ξ => conj (ν (conj ξ)) / (ξ - u) ^ 2) ξ /
          (ξ - v) ^ 2)) := by
    refine integral_congr_ae (Eventually.of_forall fun u => ?_)
    simp only []
    rw [← integral_const_mul]
  rw [e1, integral_integral_swap hS]
  refine setIntegral_congr_fun hU fun v hv => ?_
  rw [← s7l8_Yinner hμ hν hz hv, ← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun u => ?_)
  ring

/-- **(D23) pointwise bound**: for `z ∈ 𝕌` with `∫_𝕃 |E_z|² < ∞`,
`|∫ μ K₀ M(·, z)|² ≤ 4 (A(z) M² 82πM²/(Im z)² + π⁻⁴ (M²π/(Im z)²) π² M² ∫_𝕃 |E_z|²)`. -/
theorem s7l8_pt_bd {μ φ ν ψ : ℂ → ℂ} (hμ : IsHarmonicU μ φ)
    (hμ2 : (∫⁻ u in upperHalf, ‖μ u‖ₑ ^ 2 * ENNReal.ofReal (rhoU u)) < ∞) (hν : IsHarmonicU ν ψ) {M : ℝ}
    (hM : ∀ v ∈ upperHalf, ‖ν v‖ ≤ M) {z : ℂ} (hz : z ∈ upperHalf)
    (hE : (∫⁻ ξ in {ζ : ℂ | ζ.im < 0},
      ‖∫ w, upperHalf.indicator (fun w => μ w / (w - conj z) ^ 2) w / (w - ξ) ^ 2‖ₑ ^ 2) < ∞) :
    ‖∫ u in upperHalf, μ u * (1 / (u - conj z) ^ 2 * dz (dzbar fun e => kernelKbar (fun y => e * ν y) u z) 0)‖ₑ ^ 2 ≤
      4 * ((∫⁻ u in upperHalf, ‖μ u * (1 / (u - conj z) ^ 2)‖ₑ ^ 2) *
          (ENNReal.ofReal (M ^ 2) * ENNReal.ofReal (82 * π * M ^ 2 / z.im ^ 2)) +
        ENNReal.ofReal ((1 / π ^ 2) ^ 2) * (ENNReal.ofReal (M ^ 2 * (π / z.im ^ 2)) *
          (ENNReal.ofReal (π ^ 2) * (ENNReal.ofReal (M ^ 2) * ∫⁻ ξ in {ζ : ℂ | ζ.im < 0},
            ‖∫ w, upperHalf.indicator (fun w => μ w / (w - conj z) ^ 2) w / (w - ξ) ^ 2‖ₑ ^ 2)))) := by
  obtain ⟨Mμ, hMμ0, hMμ⟩ := harmonicU_bounded hμ
  have hU := measurableSet_upperHalf_aux
  have hUo : IsOpen upperHalf := isOpen_lt continuous_const Complex.continuous_im
  have hLm : MeasurableSet {ζ : ℂ | ζ.im < 0} := measurableSet_lt Complex.measurable_im measurable_const
  have hzim : 0 < z.im := hz
  have hπ := Real.pi_pos
  obtain ⟨ham, -, ha2, -⟩ := s7l8_g_data hμ hMμ hz
  obtain ⟨hgm, hg2, -⟩ := s7l8_gz hν hz
  obtain ⟨hbm, -, hb2, hbb⟩ := s7l8_g_data hν hM hz
  have hH := hilbertH_memLp_two hg2
  obtain ⟨hdecI, hdec⟩ := s7l8_pt_dec hμ hμ2 hν hz
  rw [hdec, s7l8_pt_Y hμ hμ2 hν hz]
  -- abbreviations
  obtain ⟨A, hA⟩ : ∃ A : ℂ → ℂ, A = fun u => μ u * (1 / (u - conj z) ^ 2) := ⟨_, rfl⟩
  obtain ⟨Hg, hHg⟩ : ∃ Hg : ℂ → ℂ, Hg = hilbertH (upperHalf.indicator fun v => ν v *
      conj (dz (fun e => kernelKbar (fun y => e * ν y) z v) 0)) := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B : ℂ → ℂ, B = fun v => ν v * (1 / (conj z - v) ^ 2) := ⟨_, rfl⟩
  obtain ⟨F, hF⟩ : ∃ F : ℂ → ℂ, F = fun ξ => {ζ : ℂ | ζ.im < 0}.indicator (fun ξ => conj (ν (conj ξ))) ξ *
      (∫ w, upperHalf.indicator (fun w => μ w / (w - conj z) ^ 2) w / (w - ξ) ^ 2) := ⟨_, rfl⟩
  have eX : (∫ u in upperHalf, μ u * (1 / (u - conj z) ^ 2) *
      hilbertH (upperHalf.indicator fun v => ν v * conj (dz (fun e => kernelKbar (fun y => e * ν y) z v) 0)) u) =
      ∫ u in upperHalf, A u * Hg u := by rw [hA, hHg]
  have eY : (∫ v in upperHalf, ν v * (1 / (conj z - v) ^ 2) * (-(1 / π) * ∫ ξ,
      {ζ : ℂ | ζ.im < 0}.indicator (fun ξ => conj (ν (conj ξ))) ξ *
        (∫ w, upperHalf.indicator (fun w => μ w / (w - conj z) ^ 2) w / (w - ξ) ^ 2) / (ξ - v) ^ 2)) =
      -(1 / π) * ∫ v in upperHalf, B v * ∫ ξ, F ξ / (ξ - v) ^ 2 := by
    rw [hB, hF, ← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun v => ?_)
    simp only []
    ring
  rw [eX, eY]
  -- the `L²` data of `F`
  have hnc : ContinuousOn (fun ξ => conj (ν (conj ξ))) {ζ : ℂ | ζ.im < 0} :=
    Complex.continuous_conj.comp_continuousOn ((harmonicU_continuousOn hν).comp
      Complex.continuous_conj.continuousOn fun ξ hξ => by
        show 0 < (conj ξ).im
        rw [Complex.conj_im]
        have : ξ.im < 0 := hξ
        linarith)
  have hnm : Measurable ({ζ : ℂ | ζ.im < 0}.indicator fun ξ => conj (ν (conj ξ))) := by
    rw [← Set.piecewise_eq_indicator]
    exact hnc.measurable_piecewise continuousOn_const hLm
  have hFm : Measurable F := by
    rw [hF]
    exact hnm.mul (s7l8_B_meas ham)
  have hFb : (∫⁻ ξ, ‖F ξ‖ₑ ^ 2) ≤ ENNReal.ofReal (M ^ 2) * ∫⁻ ξ in {ζ : ℂ | ζ.im < 0},
      ‖∫ w, upperHalf.indicator (fun w => μ w / (w - conj z) ^ 2) w / (w - ξ) ^ 2‖ₑ ^ 2 := by
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ← lintegral_indicator hLm]
    refine lintegral_mono fun ξ => ?_
    by_cases hξ : ξ ∈ {ζ : ℂ | ζ.im < 0}
    · rw [Set.indicator_of_mem hξ, hF]
      simp only [Set.indicator_of_mem hξ]
      rw [enorm_mul, mul_pow, RCLike.enorm_conj, ← ofReal_norm (ν (conj ξ)), ← ENNReal.ofReal_pow (norm_nonneg _)]
      refine mul_le_mul_left (ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (norm_nonneg _) (hM _ ?_) 2)) _
      show 0 < (conj ξ).im
      rw [Complex.conj_im]
      have : ξ.im < 0 := hξ
      linarith
    · rw [Set.indicator_of_notMem hξ, hF]
      simp only [Set.indicator_of_notMem hξ, zero_mul, enorm_zero]
      norm_num
  have hF2 : MemLp F 2 volume := s7l8_memLp2 hFm.aestronglyMeasurable
    (hFb.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hE))
  have hF0 : ∀ x ∈ upperHalf, F x = 0 := fun x hx => by
    rw [hF]
    simp only []
    rw [Set.indicator_of_notMem (fun h => by
      have h1 : x.im < 0 := h
      have h2 : 0 < x.im := hx
      linarith), zero_mul]
  have hGL := s7l8_off_L2 hFm hF2 hUo hF0
  -- Cauchy–Schwarz for both terms
  have hcs : ∀ f g : ℂ → ℂ, AEMeasurable f (volume.restrict upperHalf) → AEMeasurable g (volume.restrict upperHalf) →
      ‖∫ u in upperHalf, f u * g u‖ₑ ^ 2 ≤ (∫⁻ u in upperHalf, ‖f u‖ₑ ^ 2) * ∫⁻ u in upperHalf, ‖g u‖ₑ ^ 2 := by
    intro f g hf hg
    refine (pow_le_pow_left₀ zero_le (enorm_integral_le_lintegral_enorm _) 2).trans ?_
    simp only [enorm_mul]
    exact s7l8_cs _ hf.enorm hg.enorm
  have hAm : AEMeasurable A (volume.restrict upperHalf) := by
    rw [hA]
    refine ((harmonicU_continuousOn hμ).mul (continuousOn_const.div (by fun_prop) fun u hu => ?_)).aemeasurable hU
    refine pow_ne_zero 2 fun h => ?_
    have h' := congrArg Complex.im h
    have : 0 < u.im := hu
    simp at h'
    linarith
  have hHm : AEMeasurable Hg (volume.restrict upperHalf) := by
    rw [hHg]; exact hH.1.aestronglyMeasurable.aemeasurable.restrict
  have hBm : AEMeasurable B (volume.restrict upperHalf) := by
    rw [hB]
    refine ((harmonicU_continuousOn hν).mul (continuousOn_const.div (by fun_prop) fun u hu => ?_)).aemeasurable hU
    refine pow_ne_zero 2 fun h => ?_
    have h' := congrArg Complex.im h
    have : 0 < u.im := hu
    simp at h'
    linarith
  have hGm : AEMeasurable (fun v => ∫ ξ, F ξ / (ξ - v) ^ 2) (volume.restrict upperHalf) :=
    (s7l8_B_meas hFm).aemeasurable
  have h1 := hcs A Hg hAm hHm
  have h2 := hcs B (fun v => ∫ ξ, F ξ / (ξ - v) ^ 2) hBm hGm
  have hHb : (∫⁻ u in upperHalf, ‖Hg u‖ₑ ^ 2) ≤ ENNReal.ofReal (M ^ 2) * ENNReal.ofReal (82 * π * M ^ 2 / z.im ^ 2) := by
    refine (setLIntegral_le_lintegral _ _).trans (le_trans (le_of_eq ?_) (s7l8_gz_bd hν hM hz))
    rw [hHg]
    have e1 := eLpNorm_nnreal_pow_eq_lintegral (p := 2) (by norm_num) hH.1.aestronglyMeasurable
    have e2 := eLpNorm_nnreal_pow_eq_lintegral (p := 2) (by norm_num) hg2.aestronglyMeasurable
    simp only [NNReal.coe_ofNat, ENNReal.coe_ofNat] at e1 e2
    rw [hH.2] at e1
    have e3 : ∀ f : ℂ → ℂ, (∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ)) = ∫⁻ x, ‖f x‖ₑ ^ (2 : ℕ) := fun f =>
      lintegral_congr fun x => by rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, ENNReal.rpow_natCast]
    rw [← e3, ← e3]
    exact e1.symm.trans e2
  have hBb : (∫⁻ v in upperHalf, ‖B v‖ₑ ^ 2) ≤ ENNReal.ofReal (M ^ 2 * (π / z.im ^ 2)) := by
    refine le_trans (le_of_eq ?_) hbb
    rw [s7l8_ind_lint, hB]
    refine setLIntegral_congr_fun hU fun v hv => ?_
    have hne : v - conj z ≠ 0 := fun h => by
      have h' := congrArg Complex.im h
      have : 0 < v.im := hv
      simp at h'
      linarith
    have hne' : conj z - v ≠ 0 := fun h => hne (by linear_combination -h)
    congr 2
    field_simp
    ring
  have hAe : (∫⁻ u in upperHalf, ‖A u‖ₑ ^ 2) = ∫⁻ u in upperHalf, ‖μ u * (1 / (u - conj z) ^ 2)‖ₑ ^ 2 := by rw [hA]
  -- combine
  have hc : ‖(1 / π : ℂ)‖ₑ = ENNReal.ofReal (1 / π) := by
    rw [← ofReal_norm, show ((1 / π : ℂ)) = ((1 / π : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
      Real.norm_of_nonneg (by positivity)]
  have htri : ‖(∫ u in upperHalf, A u * Hg u) - 1 / π * (-(1 / π) * ∫ v in upperHalf, B v * ∫ ξ, F ξ / (ξ - v) ^ 2)‖ₑ ≤
      ‖∫ u in upperHalf, A u * Hg u‖ₑ + ENNReal.ofReal (1 / π ^ 2) * ‖∫ v in upperHalf, B v * ∫ ξ, F ξ / (ξ - v) ^ 2‖ₑ := by
    refine (enorm_sub_le).trans (le_of_eq ?_)
    rw [enorm_mul, enorm_mul, enorm_neg, hc, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
    congr 3
    ring
  calc _ ≤ (‖∫ u in upperHalf, A u * Hg u‖ₑ +
        ENNReal.ofReal (1 / π ^ 2) * ‖∫ v in upperHalf, B v * ∫ ξ, F ξ / (ξ - v) ^ 2‖ₑ) ^ 2 :=
        pow_le_pow_left₀ zero_le htri 2
    _ ≤ 4 * (‖∫ u in upperHalf, A u * Hg u‖ₑ ^ 2 +
        (ENNReal.ofReal (1 / π ^ 2) * ‖∫ v in upperHalf, B v * ∫ ξ, F ξ / (ξ - v) ^ 2‖ₑ) ^ 2) :=
        (s7l8_sq2 _ _).trans (mul_le_mul_left (by norm_num) _)
    _ ≤ _ := by
        rw [mul_pow, ← ENNReal.ofReal_pow (by positivity)]
        gcongr
        · refine h1.trans ?_
          rw [hAe]
          exact mul_le_mul_right hHb _
        · refine h2.trans ?_
          exact mul_le_mul' hBb (hGL.trans (mul_le_mul_right hFb _))

/-- Measurability of `z ↦ ∫_𝕃 |E_z|²`. -/
theorem s7l8_EL_meas {μ φ : ℂ → ℂ} (hμ : IsHarmonicU μ φ) :
    Measurable (fun z => ∫⁻ ξ in {ζ : ℂ | ζ.im < 0},
      ‖∫ w, upperHalf.indicator (fun w => μ w / (w - conj z) ^ 2) w / (w - ξ) ^ 2‖ₑ ^ 2) := by
  have hμm : Measurable (upperHalf.indicator μ) := s7l8_ind_meas (harmonicU_continuousOn hμ)
  have hEe : ∀ z ξ : ℂ, (∫ w, upperHalf.indicator (fun w => μ w / (w - conj z) ^ 2) w / (w - ξ) ^ 2) =
      ∫ w, upperHalf.indicator μ w / (w - conj z) ^ 2 / (w - ξ) ^ 2 := fun z ξ => by
    refine integral_congr_ae (Eventually.of_forall fun w => ?_)
    by_cases hw : w ∈ upperHalf
    · simp only [Set.indicator_of_mem hw]
    · simp only [Set.indicator_of_notMem hw, zero_div]
  have hEm : Measurable (fun p : ℂ × ℂ => ∫ w, upperHalf.indicator μ w / (w - conj p.1) ^ 2 / (w - p.2) ^ 2) := by
    have hF : Measurable (fun q : (ℂ × ℂ) × ℂ => upperHalf.indicator μ q.2 / (q.2 - conj q.1.1) ^ 2 /
        (q.2 - q.1.2) ^ 2) :=
      ((hμm.comp measurable_snd).div ((measurable_snd.sub
        (Complex.continuous_conj.measurable.comp (measurable_fst.comp measurable_fst))).pow_const 2)).div
        ((measurable_snd.sub (measurable_snd.comp measurable_fst)).pow_const 2)
    exact (hF.stronglyMeasurable.integral_prod_right' (ν := volume)).measurable
  have h := (hEm.enorm.pow_const 2).lintegral_prod_right' (ν := volume.restrict {ζ : ℂ | ζ.im < 0})
  have e : (fun z => ∫⁻ ξ in {ζ : ℂ | ζ.im < 0},
      ‖∫ w, upperHalf.indicator (fun w => μ w / (w - conj z) ^ 2) w / (w - ξ) ^ 2‖ₑ ^ 2) =
      fun z => ∫⁻ ξ in {ζ : ℂ | ζ.im < 0},
        ‖∫ w, upperHalf.indicator μ w / (w - conj z) ^ 2 / (w - ξ) ^ 2‖ₑ ^ 2 := by
    funext z
    simp only [hEe]
  rw [e]
  exact h

/-- The weight: `|ρ⁻¹ I|² ρ = (Im z)² |I|²`. -/
theorem s7l8_rho_w {z : ℂ} (hz : z ∈ upperHalf) (I : ℂ) :
    ‖(rhoU z : ℂ)⁻¹ * I‖ₑ ^ 2 * ENNReal.ofReal (rhoU z) = ENNReal.ofReal (z.im ^ 2) * ‖I‖ₑ ^ 2 := by
  have hzi : 0 < z.im := hz
  have hz2 : z.im ^ 2 ≠ 0 := by positivity
  have hr : (rhoU z : ℂ)⁻¹ = ((z.im ^ 2 : ℝ) : ℂ) := by
    unfold rhoU
    push_cast
    rw [inv_inv]
  rw [hr, enorm_mul, mul_pow, ← ofReal_norm (((z.im ^ 2 : ℝ) : ℂ)), Complex.norm_real,
    Real.norm_of_nonneg (by positivity), mul_right_comm, ← ENNReal.ofReal_pow (by positivity),
    ← ENNReal.ofReal_mul (by positivity),
    show (z.im ^ 2) ^ 2 * rhoU z = z.im ^ 2 by unfold rhoU; field_simp]

/-- (D23) measurability: joint continuity of `μ(u) K₀(u, z) M(u, z)` on `𝕌 × 𝕌` (`s7l8_M_cont`). -/
theorem s7l8_D23_meas {μ φ ν ψ : ℂ → ℂ} (hμ : IsHarmonicU μ φ) (hν : IsHarmonicU ν ψ) :
    AEMeasurable (fun z => (rhoU z : ℂ)⁻¹ * ∫ u in upperHalf, μ u *
      (1 / (u - conj z) ^ 2 * dz (dzbar fun e => kernelKbar (fun y => e * ν y) u z) 0)) (volume.restrict upperHalf) := by
  have hU := measurableSet_upperHalf_aux
  have hμc := harmonicU_continuousOn hμ
  have hprod : (volume.restrict upperHalf).prod (volume.restrict upperHalf) =
      (volume.prod volume).restrict (upperHalf ×ˢ upperHalf) := Measure.prod_restrict _ _
  obtain ⟨Mf, hMf⟩ : ∃ Mf : ℂ → ℂ → ℂ, Mf = fun a b => dz (dzbar fun e => kernelKbar (fun y => e * ν y) a b) 0 :=
    ⟨_, rfl⟩
  have hMc : ContinuousOn (fun p : ℂ × ℂ => Mf p.1 p.2) (upperHalf ×ˢ upperHalf) := by
    rw [hMf]
    exact s7l8_M_cont hν
  have hne : ∀ p ∈ upperHalf ×ˢ upperHalf, (p.2 - conj p.1 : ℂ) ≠ 0 := fun p hp h => by
    have h' := congrArg Complex.im h
    have h1 : 0 < p.1.im := hp.1
    have h2 : 0 < p.2.im := hp.2
    simp at h'
    linarith
  have hsw : ContinuousOn (fun p : ℂ × ℂ => Mf p.2 p.1) (upperHalf ×ˢ upperHalf) :=
    hMc.comp continuous_swap.continuousOn fun p hp => ⟨hp.2, hp.1⟩
  have hFc : ContinuousOn (fun p : ℂ × ℂ => μ p.2 * (1 / (p.2 - conj p.1) ^ 2 * Mf p.2 p.1))
      (upperHalf ×ˢ upperHalf) :=
    (hμc.comp continuous_snd.continuousOn fun p hp => hp.2).mul
      ((continuousOn_const.div (by fun_prop) fun p hp => pow_ne_zero 2 (hne p hp)).mul hsw)
  have hFm : AEStronglyMeasurable (fun p : ℂ × ℂ => μ p.2 * (1 / (p.2 - conj p.1) ^ 2 * Mf p.2 p.1))
      ((volume.restrict upperHalf).prod (volume.restrict upperHalf)) := by
    rw [hprod]
    exact hFc.aestronglyMeasurable (hU.prod hU)
  have hrm : Measurable fun z : ℂ => ((rhoU z : ℝ) : ℂ)⁻¹ := by unfold rhoU; fun_prop
  have hres := hrm.aemeasurable.mul hFm.integral_prod_right'.aemeasurable
  rw [hMf] at hres
  exact hres

/-- `z ↦ ∫_𝕌 |μ(u)|²/|u - z̄|⁴` is a.e.-measurable. -/
theorem s7l8_A_meas {μ φ : ℂ → ℂ} (hμ : IsHarmonicU μ φ) :
    AEMeasurable (fun z => ∫⁻ u in upperHalf, ‖μ u * (1 / (u - conj z) ^ 2)‖ₑ ^ 2) (volume.restrict upperHalf) := by
  have hU := measurableSet_upperHalf_aux
  have hμc := harmonicU_continuousOn hμ
  have hprod : (volume.restrict upperHalf).prod (volume.restrict upperHalf) =
      (volume.prod volume).restrict (upperHalf ×ˢ upperHalf) := Measure.prod_restrict _ _
  have hne : ∀ p ∈ upperHalf ×ˢ upperHalf, (p.2 - conj p.1 : ℂ) ≠ 0 := fun p hp h => by
    have h' := congrArg Complex.im h
    have h1 : 0 < p.1.im := hp.1
    have h2 : 0 < p.2.im := hp.2
    simp at h'
    linarith
  have hc : ContinuousOn (fun p : ℂ × ℂ => μ p.2 * (1 / (p.2 - conj p.1) ^ 2)) (upperHalf ×ˢ upperHalf) :=
    (hμc.comp continuous_snd.continuousOn fun p hp => hp.2).mul
      (continuousOn_const.div (by fun_prop) fun p hp => pow_ne_zero 2 (hne p hp))
  have hm : AEMeasurable (fun p : ℂ × ℂ => ‖μ p.2 * (1 / (p.2 - conj p.1) ^ 2)‖ₑ ^ 2)
      ((volume.restrict upperHalf).prod (volume.restrict upperHalf)) := by
    rw [hprod]
    exact (hc.aemeasurable (hU.prod hU)).enorm.pow_const 2
  exact hm.lintegral_prod_right'

/-- (D23) the pointwise weighted bound `|ρ⁻¹ ∫ μ K₀ M|² ρ ≤ 328π M⁴ A(z) + (4M⁴/π) ∫_𝕃 |E_z|²`. -/
theorem s7l8_D23_pt2 {μ φ ν ψ : ℂ → ℂ} (hμ : IsHarmonicU μ φ)
    (hμ2 : (∫⁻ u in upperHalf, ‖μ u‖ₑ ^ 2 * ENNReal.ofReal (rhoU u)) < ∞) (hν : IsHarmonicU ν ψ) {M : ℝ}
    (hM0 : 0 ≤ M) (hM : ∀ v ∈ upperHalf, ‖ν v‖ ≤ M) {z : ℂ} (hz : z ∈ upperHalf)
    (hE : (∫⁻ ξ in {ζ : ℂ | ζ.im < 0},
      ‖∫ w, upperHalf.indicator (fun w => μ w / (w - conj z) ^ 2) w / (w - ξ) ^ 2‖ₑ ^ 2) < ∞) :
    ‖(rhoU z : ℂ)⁻¹ * ∫ u in upperHalf, μ u *
        (1 / (u - conj z) ^ 2 * dz (dzbar fun e => kernelKbar (fun y => e * ν y) u z) 0)‖ₑ ^ 2 *
          ENNReal.ofReal (rhoU z) ≤
      4 * ENNReal.ofReal (82 * π * M ^ 4) * (∫⁻ u in upperHalf, ‖μ u * (1 / (u - conj z) ^ 2)‖ₑ ^ 2) +
      4 * ENNReal.ofReal (M ^ 4 / π) * ∫⁻ ξ in {ζ : ℂ | ζ.im < 0},
        ‖∫ w, upperHalf.indicator (fun w => μ w / (w - conj z) ^ 2) w / (w - ξ) ^ 2‖ₑ ^ 2 := by
  have hzi : 0 < z.im := hz
  have hπ := Real.pi_pos
  rw [s7l8_rho_w hz]
  refine (mul_le_mul_right (s7l8_pt_bd hμ hμ2 hν hM hz hE) _).trans (le_of_eq ?_)
  have e1 : ENNReal.ofReal (z.im ^ 2) * (ENNReal.ofReal (M ^ 2) * ENNReal.ofReal (82 * π * M ^ 2 / z.im ^ 2)) =
      ENNReal.ofReal (82 * π * M ^ 4) := by
    rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    field_simp
  have e2 : ENNReal.ofReal (z.im ^ 2) * (ENNReal.ofReal ((1 / π ^ 2) ^ 2) * (ENNReal.ofReal (M ^ 2 * (π / z.im ^ 2)) *
      (ENNReal.ofReal (π ^ 2) * ENNReal.ofReal (M ^ 2)))) = ENNReal.ofReal (M ^ 4 / π) := by
    rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    field_simp
  rw [← e1, ← e2]
  ring

/-- **(A) Pointwise second variation of `Q` in `𝕌`.** Both orders of the mixed derivative agree with
`(12/π) ρ⁻¹ ∫ μ(u) ∂∂̄[K_e(u, z)²]₀ - μ(z) G(|ν|²)(z)`. -/
theorem s7l8_A_pointwise {μ φ ν ψ : ℂ → ℂ} (hμ : IsHarmonicU μ φ) (hν : IsHarmonicU ν ψ) {z : ℂ}
    (hz : z ∈ upperHalf) :
    dz (dzbar fun ε => QfunU μ (fun u => ε * ν u) z) 0 =
        (12 / π : ℂ) * (∫ u in upperHalf, μ u * dz (dzbar fun e => kernelKbar (fun y => e * ν y) u z ^ 2) 0) /
          (rhoU z : ℂ) - μ z * resolventOpU (fun u => ((‖ν u‖ ^ 2 : ℝ) : ℂ)) z ∧
      dzbar (dz fun ε => QfunU μ (fun u => ε * ν u) z) 0 =
        (12 / π : ℂ) * (∫ u in upperHalf, μ u * dz (dzbar fun e => kernelKbar (fun y => e * ν y) u z ^ 2) 0) /
          (rhoU z : ℂ) - μ z * resolventOpU (fun u => ((‖ν u‖ ^ 2 : ℝ) : ℂ)) z := by
  obtain ⟨C, hC0, hmB, hms⟩ := s71_harm_setup hν
  obtain ⟨Mμ, hMμ0, hμb⟩ := harmonicU_bounded hμ
  have hU := measurableSet_upperHalf_aux
  obtain ⟨W, hW⟩ : ∃ W : ℂ × ℂ → ℂ → ℂ, W = fun P => normalizedSolution fun u =>
      P.1 * (if 0 < u.im then ν u else 0) + P.2 * (if u.im < 0 then conj (ν (conj u)) else 0) := ⟨_, rfl⟩
  have hC1 : 0 < C + 1 := by linarith
  have hR0p : 0 < 1 / (C + 1) := by positivity
  have hR0k : 1 / (C + 1) * C < 1 := by
    rw [div_mul_eq_mul_div, one_mul, div_lt_one hC1]
    linarith
  set r1 := min (1 / (C + 1)) (1 / (C + 1)) with hr1d
  have hr1 : 0 < r1 := lt_min hR0p hR0p
  have hJ := s7g_f2_Jreg hμ hC0 hmB hms hR0p hR0k hW hz
  have hDr := s7g_f2_Dreg hC0 hmB hms hR0k hW hz
  have hD0 : rhoVar ν 0 z = rhoU z := (rhoVar_pullback ν 0 hz).2
  have hρ0 : (rhoU z : ℂ) ≠ 0 := by
    rw [Complex.ofReal_ne_zero]
    have him : 0 < z.im := hz
    unfold rhoU
    positivity
  have hDc : ContinuousAt (fun e => rhoVar ν e z) 0 :=
    hDr.continuousOn.continuousAt (ball_mem_nhds 0 hr1)
  have hev : ∀ᶠ e in 𝓝 (0 : ℂ), rhoVar ν e z ≠ 0 ∧ e ∈ ball (0 : ℂ) r1 :=
    (hDc.eventually_ne (show rhoVar ν 0 z ≠ 0 by rw [hD0]; exact hρ0)).and (ball_mem_nhds 0 hr1)
  obtain ⟨r, hr, hrr⟩ := Metric.eventually_nhds_iff.1 hev
  have hball : ∀ e ∈ ball (0 : ℂ) r, rhoVar ν e z ≠ 0 ∧ e ∈ ball (0 : ℂ) r1 := fun e he =>
    hrr (by rwa [mem_ball] at he)
  have hsub : ball (0 : ℂ) r ⊆ ball (0 : ℂ) r1 := fun e he => (hball e he).2
  have hεk : ∀ e ∈ ball (0 : ℂ) r, ‖e‖ * C < 1 := by
    intro e he
    have h := lt_of_lt_of_le (mem_ball_zero_iff.1 (hsub he)) (min_le_right _ _)
    rw [lt_div_iff₀ hC1] at h
    nlinarith [norm_nonneg e]
  have heq : ∀ e ∈ ball (0 : ℂ) r, (12 / π : ℂ) * (∫ t in upperHalf, μ t * kernelKbar (fun y => e * ν y) t z ^ 2) =
      rhoVar ν e z * QfunU μ (fun u => e * ν u) z := fun e he =>
    (s71_eq_7_1 hμ hν hC0 hmB (hεk e he) hz).symm
  have hQr : ContDiffOn ℝ 2 (fun e => QfunU μ (fun u => e * ν u) z) (ball 0 r) := by
    refine (((contDiffOn_const (c := (12 / π : ℂ))).mul (hJ.mono hsub)).mul
      ((hDr.mono hsub).inv fun e he => (hball e he).1)).congr fun e he => ?_
    rw [Pi.inv_apply, ← div_eq_mul_inv, eq_div_iff (hball e he).1, heq e he]
    ring
  have hDr' := hDr.mono hsub
  -- the factor `ρ^{εν}(z)`
  have hDreal : (fun e => rhoVar ν e z) = fun e => conj (rhoVar ν e z) :=
    funext fun e => (s71_rho_real ν e z).symm
  have hDd1 : dz (fun e => rhoVar ν e z) 0 = 0 := lemma_6_1 hν hz
  have hDd2 : dzbar (fun e => rhoVar ν e z) 0 = 0 := by
    rw [hDreal, p71r_dzbar_conj, hDd1, map_zero]
  have hDdd : dzbar (dz fun e => rhoVar ν e z) 0 = rhoU z * resolventOpU (fun u => (‖ν u‖ ^ 2 : ℝ)) z := by
    rw [hDreal, s7g_f2_conjW, prop_6_3 hν hz, map_mul, Complex.conj_ofReal,
      s7g_f2_res_real (fun u => ‖ν u‖ ^ 2)]
  -- `L̈((12/π) J) = L̈(ρ^{εν} Q)`
  have hballn : ball (0 : ℂ) r ∈ 𝓝 (0 : ℂ) := ball_mem_nhds 0 hr
  have hT : (12 / π : ℂ) * dzbar (dz fun e => ∫ t in upperHalf, μ t * kernelKbar (fun y => e * ν y) t z ^ 2) 0 =
      dzbar (dz fun e => rhoVar ν e z * QfunU μ (fun u => e * ν u) z) 0 := by
    rw [← s7g_f2_wconst hr (hJ.mono hsub)]
    exact s7g_f2_germ (Filter.eventually_of_mem hballn heq)
  rw [s7g_f2_wmul hr hDr' hQr, hDd1, hDd2, hDdd, hD0, s7g_f2_Q0 hμ hz] at hT
  -- `J̈` under the integral
  set S : Set ℂ := upperHalf \ {I} with hSdef
  have hSm : MeasurableSet S := hU.diff (measurableSet_singleton I)
  have hSU : S ⊆ upperHalf := sdiff_subset
  have hnull : (S : Set ℂ) =ᵐ[volume] upperHalf := sdiff_null_ae_eq_self (measure_singleton I)
  obtain ⟨hJ1, hJ2, -⟩ := s7g_f2_Jdd hC0 hmB hms (harmonicU_continuousOn hμ) hMμ0 hμb hR0p hR0k hW hz
  have hpt : ∀ t ∈ S, deriv (fun b => deriv (fun a => μ t *
      (dz (W (a, b)) t * dz (W (a, b)) (conj z) / (W (a, b) t - W (a, b) (conj z)) ^ 2) ^ 2) 0) 0 =
      μ t * dz (dzbar fun e => kernelKbar (fun y => e * ν y) t z ^ 2) 0 := by
    intro t ht
    have hH := (s7g_f2_Kreg hC0 hmB hms hW (hSU ht) hz hR0k).pow 2
    have hdd := (s7g_f2_ddpartial hR0p hH).2
    have hge : (fun e => kernelKbar (fun y => e * ν y) t z ^ 2) =ᶠ[𝓝 (0 : ℂ)]
        fun e => (dz (W (e, conj e)) t * dz (W (e, conj e)) (conj z) /
          (W (e, conj e) t - W (e, conj e) (conj z)) ^ 2) ^ 2 := by
      filter_upwards [ball_mem_nhds (0 : ℂ) hr] with e he
      rw [s7g_f2_Kdiag hC0 hmB hW (hεk e he) t z]
    simp only [deriv_const_mul_field']
    rw [s7g_f2_germ2 hge, hdd]
  have hJint : dzbar (dz fun e => ∫ t in upperHalf, μ t * kernelKbar (fun y => e * ν y) t z ^ 2) 0 =
      ∫ u in upperHalf, μ u * dz (dzbar fun e => kernelKbar (fun y => e * ν y) u z ^ 2) 0 := by
    rw [hJ2, hJ1, ← setIntegral_congr_set hnull]
    exact setIntegral_congr_fun hSm hpt
  have hQdd : dzbar (dz fun ε => QfunU μ (fun u => ε * ν u) z) 0 =
      (12 / π : ℂ) * (∫ u in upperHalf, μ u * dz (dzbar fun e => kernelKbar (fun y => e * ν y) u z ^ 2) 0) /
        (rhoU z : ℂ) - μ z * resolventOpU (fun u => ((‖ν u‖ ^ 2 : ℝ) : ℂ)) z := by
    rw [← hJint, eq_sub_iff_add_eq, eq_div_iff hρ0]
    linear_combination -hT
  refine ⟨?_, hQdd⟩
  rw [wp_wirtinger_comm (hQr.contDiffAt hballn)]
  exact hQdd

/-- **(B1) Product rule.** `∂∂̄[K²]₀ = 2 K₀ M + 2 D₁ D̄₁`, `K₀(u, z) = 1/(u - z̄)²`. -/
theorem s7l8_B_product {ν ψ : ℂ → ℂ} (hν : IsHarmonicU ν ψ) {u z : ℂ} (hu : u ∈ upperHalf)
    (hz : z ∈ upperHalf) :
    dz (dzbar fun e => kernelKbar (fun y => e * ν y) u z ^ 2) 0 =
      2 * (1 / (u - conj z) ^ 2) * dz (dzbar fun e => kernelKbar (fun y => e * ν y) u z) 0 +
        2 * (dz (fun e => kernelKbar (fun y => e * ν y) u z) 0 *
          dzbar (fun e => kernelKbar (fun y => e * ν y) u z) 0) := by
  obtain ⟨r, hr, hC⟩ := s7l8_K_C2 hν hu hz
  set f : ℂ → ℂ := fun e => kernelKbar (fun y => e * ν y) u z with hf
  have hB : ball (0 : ℂ) r ∈ 𝓝 (0 : ℂ) := ball_mem_nhds 0 hr
  have hfd : ∀ e ∈ ball (0 : ℂ) r, DifferentiableAt ℝ f e := fun e he =>
    (hC.differentiableOn (by norm_num) e he).differentiableAt (isOpen_ball.mem_nhds he)
  have hfd' : ContDiffOn ℝ 1 (fderiv ℝ f) (ball 0 r) := hC.fderiv_of_isOpen isOpen_ball (by norm_num)
  have hdb : DifferentiableAt ℝ (dzbar f) 0 := by
    have hd := (hfd'.differentiableOn (by norm_num) 0 (mem_ball_self hr)).differentiableAt hB
    have hA : DifferentiableAt ℝ (fun e => fderiv ℝ f e 1) 0 := hd.clm_apply (differentiableAt_const 1)
    have hA' : DifferentiableAt ℝ (fun e => fderiv ℝ f e I) 0 := hd.clm_apply (differentiableAt_const I)
    have hs : DifferentiableAt ℝ (fun e => fderiv ℝ f e 1 + I * fderiv ℝ f e I) 0 :=
      hA.add ((differentiableAt_const I).mul hA')
    have h2 : DifferentiableAt ℝ (fun e => (fderiv ℝ f e 1 + I * fderiv ℝ f e I) * (2 : ℂ)⁻¹) 0 :=
      hs.mul_const _
    refine h2.congr_of_eventuallyEq (Eventually.of_forall fun e => ?_)
    show (fderiv ℝ f e 1 + I * fderiv ℝ f e I) / 2 = _
    rw [div_eq_mul_inv]
  have hsq : dzbar (fun e => f e ^ 2) =ᶠ[𝓝 0] fun e => 2 * (f e * dzbar f e) := by
    filter_upwards [hB] with e he
    have h := s71_dzbar_mul (hfd e he) (hfd e he)
    rw [show (fun e => f e ^ 2) = fun w => f w * f w from funext fun w => sq _, h]
    ring
  have hf0 := hfd 0 (mem_ball_self hr)
  rw [s7g_f2_dz_congr hsq, e64_t9_dz_mul (u := fun _ => (2 : ℂ)) (v := fun e => f e * dzbar f e)
      (differentiableAt_const _) (hf0.mul hdb), e64_t9_dz_mul (u := f) (v := dzbar f) hf0 hdb,
    (e124_dz_eventuallyConst (Eventually.of_forall fun _ => rfl)).1]
  have h0 : f 0 = 1 / (u - conj z) ^ 2 := (e64_t9_K0 ν u z).2.1
  rw [h0]
  ring

/-- **(B2) The mixed second variation of the kernel** (used in (D23)): `(1.25)` differentiated once more at `0`,
`M(u, z) = -(1/π) PV ∬ ν̄(v) [D₁(u, v) K̄̄₀(v, z) + K̄₀(u, v) ∂_e K̄̄_e(v, z)|₀] d²v`. -/
theorem s7l8_B_mixed {ν ψ : ℂ → ℂ} (hν : IsHarmonicU ν ψ) {u z : ℂ} (hu : u ∈ upperHalf)
    (hz : z ∈ upperHalf) (huz : u ≠ z) :
    dz (dzbar fun e => kernelKbar (fun y => e * ν y) u z) 0 =
      -(1 / π) * pv2 (fun v => conj (ν v) *
        (dz (fun e => kernelKbar (fun y => e * ν y) u v) 0 * (1 / (conj v - conj z) ^ 2) +
          1 / (u - conj v) ^ 2 * dz (fun e => kernelKbarbar (fun y => e * ν y) v z) 0)) u z := by
  have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 Real.pi_ne_zero
  unfold pv2
  rw [(s7l8_B2_lim hν hu hz huz).limUnder_eq]
  field_simp

/-- **(D1)** `I₁ = ρ⁻¹ ∫ μ D₁ D̄₁ ∈ L²(𝕌, ρ)` (Cauchy–Schwarz, `∬ |w - z̄|⁻⁴ = (π/4) ρ(z)`, Beurling isometry). -/
theorem s7l8_D1 {μ φ ν ψ : ℂ → ℂ} (hμ : IsHarmonicU μ φ)
    (hμ2 : (∫⁻ u in upperHalf, ‖μ u‖ₑ ^ 2 * ENNReal.ofReal (rhoU u)) < ∞) (hν : IsHarmonicU ν ψ) :
    (∀ᵐ z ∂(volume.restrict upperHalf), IntegrableOn (fun u => μ u *
      (dz (fun e => kernelKbar (fun y => e * ν y) u z) 0 * dzbar (fun e => kernelKbar (fun y => e * ν y) u z) 0))
        upperHalf) ∧
    AEMeasurable (fun z => (rhoU z : ℂ)⁻¹ * ∫ u in upperHalf, μ u *
      (dz (fun e => kernelKbar (fun y => e * ν y) u z) 0 * dzbar (fun e => kernelKbar (fun y => e * ν y) u z) 0))
        (volume.restrict upperHalf) ∧
    (∫⁻ z in upperHalf, ‖(rhoU z : ℂ)⁻¹ * ∫ u in upperHalf, μ u *
      (dz (fun e => kernelKbar (fun y => e * ν y) u z) 0 * dzbar (fun e => kernelKbar (fun y => e * ν y) u z) 0)‖ₑ ^ 2 *
        ENNReal.ofReal (rhoU z)) < ∞ := by
  obtain ⟨M, hM0, hM⟩ := harmonicU_bounded hν
  have hU := measurableSet_upperHalf_aux
  obtain ⟨D, hD⟩ : ∃ D : ℂ → ℂ → ℂ, D = fun u z => dz (fun e => kernelKbar (fun y => e * ν y) u z) 0 :=
    ⟨_, rfl⟩
  have eD : ∀ u z, dz (fun e => kernelKbar (fun y => e * ν y) u z) 0 = D u z := fun u z => by rw [hD]
  have eDb : ∀ u z, dzbar (fun e => kernelKbar (fun y => e * ν y) u z) 0 = conj (D z u) := fun u z => by
    rw [s7l8_D1b_conj, eD]
  simp only [eDb, eD]
  have hDc : ContinuousOn (fun p : ℂ × ℂ => D p.1 p.2) (upperHalf ×ˢ upperHalf) := by
    rw [hD]; exact s7l8_D1_cont hν
  have hμc := harmonicU_continuousOn hμ
  have hsl1 : ∀ z ∈ upperHalf, ContinuousOn (fun u => D u z) upperHalf := fun z hz =>
    hDc.comp (continuous_id.prodMk continuous_const).continuousOn fun u hu => ⟨hu, hz⟩
  have hsl2 : ∀ z ∈ upperHalf, ContinuousOn (fun u => D z u) upperHalf := fun z hz =>
    hDc.comp (continuous_const.prodMk continuous_id).continuousOn fun u hu => ⟨hz, hu⟩
  -- pointwise Cauchy–Schwarz, with the Beurling bound on `∫ |D₁(·, z)|²`
  have hF : ∀ z ∈ upperHalf, (∫⁻ u in upperHalf, ‖μ u * (D u z * conj (D z u))‖ₑ) ^ 2 ≤
      ENNReal.ofReal (M ^ 2 * (π / z.im ^ 2)) * ∫⁻ u in upperHalf, ‖μ u‖ₑ ^ 2 * ‖D z u‖ₑ ^ 2 := by
    intro z hz
    have hA : AEMeasurable (fun u => ‖D u z‖ₑ) (volume.restrict upperHalf) :=
      ((hsl1 z hz).aemeasurable hU).enorm
    have hB : AEMeasurable (fun u => ‖μ u‖ₑ * ‖D z u‖ₑ) (volume.restrict upperHalf) :=
      (hμc.aemeasurable hU).enorm.mul ((hsl2 z hz).aemeasurable hU).enorm
    have hcs := s7l8_cs (volume.restrict upperHalf) hA hB
    have hL := s7l8_D1_L2 hν hM hz
    simp only [eD] at hL
    calc (∫⁻ u in upperHalf, ‖μ u * (D u z * conj (D z u))‖ₑ) ^ 2
        = (∫⁻ u in upperHalf, ‖D u z‖ₑ * (‖μ u‖ₑ * ‖D z u‖ₑ)) ^ 2 := by
          congr 1
          refine lintegral_congr fun u => ?_
          rw [enorm_mul, enorm_mul, RCLike.enorm_conj, mul_left_comm]
      _ ≤ (∫⁻ u in upperHalf, ‖D u z‖ₑ ^ 2) * ∫⁻ u in upperHalf, (‖μ u‖ₑ * ‖D z u‖ₑ) ^ 2 := hcs
      _ ≤ _ := by
          simp only [mul_pow]
          exact mul_le_mul_left hL _
  -- the weight
  have hρ : ∀ z ∈ upperHalf, ∀ I : ℂ, ‖(rhoU z : ℂ)⁻¹ * I‖ₑ ^ 2 * ENNReal.ofReal (rhoU z) =
      ENNReal.ofReal (z.im ^ 2) * ‖I‖ₑ ^ 2 := by
    intro z hz I
    have hzi : 0 < z.im := hz
    have hz2 : z.im ^ 2 ≠ 0 := by positivity
    have hr : (rhoU z : ℂ)⁻¹ = ((z.im ^ 2 : ℝ) : ℂ) := by
      unfold rhoU
      push_cast
      rw [inv_inv]
    rw [hr, enorm_mul, mul_pow, ← ofReal_norm (((z.im ^ 2 : ℝ) : ℂ)), Complex.norm_real,
      Real.norm_of_nonneg (by positivity), mul_right_comm, ← ENNReal.ofReal_pow (by positivity),
      ← ENNReal.ofReal_mul (by positivity),
      show (z.im ^ 2) ^ 2 * rhoU z = z.im ^ 2 by unfold rhoU; field_simp]
  have hpt : ∀ z ∈ upperHalf, ‖(rhoU z : ℂ)⁻¹ * ∫ u in upperHalf, μ u * (D u z * conj (D z u))‖ₑ ^ 2 *
      ENNReal.ofReal (rhoU z) ≤ ENNReal.ofReal (M ^ 2 * π) *
        ∫⁻ u in upperHalf, ‖μ u‖ₑ ^ 2 * ‖D z u‖ₑ ^ 2 := by
    intro z hz
    have hzi : 0 < z.im := hz
    have hz2 : z.im ^ 2 ≠ 0 := by positivity
    rw [hρ z hz]
    calc ENNReal.ofReal (z.im ^ 2) * ‖∫ u in upperHalf, μ u * (D u z * conj (D z u))‖ₑ ^ 2
        ≤ ENNReal.ofReal (z.im ^ 2) * (ENNReal.ofReal (M ^ 2 * (π / z.im ^ 2)) *
            ∫⁻ u in upperHalf, ‖μ u‖ₑ ^ 2 * ‖D z u‖ₑ ^ 2) := by
          refine mul_le_mul_right ?_ _
          exact (pow_le_pow_left₀ zero_le (enorm_integral_le_lintegral_enorm _) 2).trans (hF z hz)
      _ = _ := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity),
            show z.im ^ 2 * (M ^ 2 * (π / z.im ^ 2)) = M ^ 2 * π by field_simp]
  -- Tonelli
  have hprod : (volume.restrict upperHalf).prod (volume.restrict upperHalf) =
      (volume.prod volume).restrict (upperHalf ×ˢ upperHalf) := Measure.prod_restrict _ _
  have hKm : AEMeasurable (fun p : ℂ × ℂ => ‖μ p.2‖ₑ ^ 2 * ‖D p.1 p.2‖ₑ ^ 2)
      ((volume.restrict upperHalf).prod (volume.restrict upperHalf)) := by
    rw [hprod]
    have h1 : AEMeasurable (fun p : ℂ × ℂ => μ p.2) ((volume.prod volume).restrict (upperHalf ×ˢ upperHalf)) :=
      (hμc.comp continuous_snd.continuousOn fun p hp => hp.2).aemeasurable (hU.prod hU)
    exact (h1.enorm.pow_const 2).mul ((hDc.aemeasurable (hU.prod hU)).enorm.pow_const 2)
  have hHm : AEMeasurable (fun z => ∫⁻ u in upperHalf, ‖μ u‖ₑ ^ 2 * ‖D z u‖ₑ ^ 2)
      (volume.restrict upperHalf) := hKm.lintegral_prod_right'
  have hHint : (∫⁻ z in upperHalf, ∫⁻ u in upperHalf, ‖μ u‖ₑ ^ 2 * ‖D z u‖ₑ ^ 2) < ∞ := by
    rw [lintegral_lintegral_swap (f := fun z u => ‖μ u‖ₑ ^ 2 * ‖D z u‖ₑ ^ 2) hKm]
    calc (∫⁻ u in upperHalf, ∫⁻ z in upperHalf, ‖μ u‖ₑ ^ 2 * ‖D z u‖ₑ ^ 2)
        = ∫⁻ u in upperHalf, ‖μ u‖ₑ ^ 2 * ∫⁻ z in upperHalf, ‖D z u‖ₑ ^ 2 :=
          lintegral_congr fun u => lintegral_const_mul' _ _ (ENNReal.pow_ne_top enorm_ne_top)
      _ ≤ ∫⁻ u in upperHalf, ENNReal.ofReal (M ^ 2 * π) * (‖μ u‖ₑ ^ 2 * ENNReal.ofReal (rhoU u)) := by
          refine setLIntegral_mono' hU fun u hu => ?_
          have hL := s7l8_D1_L2 hν hM hu
          simp only [eD] at hL
          calc _ ≤ ‖μ u‖ₑ ^ 2 * ENNReal.ofReal (M ^ 2 * (π / u.im ^ 2)) := mul_le_mul_right hL _
            _ = _ := by
              rw [show M ^ 2 * (π / u.im ^ 2) = M ^ 2 * π * rhoU u by unfold rhoU; ring,
                ENNReal.ofReal_mul (by positivity)]
              ring
      _ = ENNReal.ofReal (M ^ 2 * π) * ∫⁻ u in upperHalf, ‖μ u‖ₑ ^ 2 * ENNReal.ofReal (rhoU u) :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ < ∞ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hμ2
  have hHfin := ae_lt_top' hHm hHint.ne
  refine ⟨?_, ?_, ?_⟩
  · filter_upwards [hHfin, ae_restrict_mem hU] with z hHz hz
    refine ⟨(hμc.mul ((hsl1 z hz).mul (Complex.continuous_conj.comp_continuousOn (hsl2 z hz)))).aestronglyMeasurable
      hU, ?_⟩
    have hlt : (∫⁻ u in upperHalf, ‖μ u * (D u z * conj (D z u))‖ₑ) ^ 2 < ∞ :=
      (hF z hz).trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hHz)
    show (∫⁻ u in upperHalf, ‖μ u * (D u z * conj (D z u))‖ₑ) < ∞
    exact lt_top_iff_ne_top.2 fun h => by rw [h] at hlt; simp at hlt
  · have hFm : AEStronglyMeasurable (fun p : ℂ × ℂ => μ p.2 * (D p.2 p.1 * conj (D p.1 p.2)))
        ((volume.restrict upperHalf).prod (volume.restrict upperHalf)) := by
      rw [hprod]
      refine ContinuousOn.aestronglyMeasurable ?_ (hU.prod hU)
      have hsw : ContinuousOn (fun p : ℂ × ℂ => D p.2 p.1) (upperHalf ×ˢ upperHalf) :=
        hDc.comp continuous_swap.continuousOn fun p hp => ⟨hp.2, hp.1⟩
      exact (hμc.comp continuous_snd.continuousOn fun p hp => hp.2).mul
        (hsw.mul (Complex.continuous_conj.comp_continuousOn hDc))
    have hrm : Measurable fun z : ℂ => ((rhoU z : ℝ) : ℂ)⁻¹ := by unfold rhoU; fun_prop
    exact hrm.aemeasurable.mul hFm.integral_prod_right'.aemeasurable
  · refine lt_of_le_of_lt (setLIntegral_mono' hU hpt) ?_
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hHint

/-- **(D23)** `I₂ + I₃ = ρ⁻¹ ∫ μ K₀ M ∈ L²(𝕌, ρ)` (via (B2); the `I₂ = I₅ + I₆` split of the paper, the two
dropped terms vanishing as in `prop_6_3`). -/
theorem s7l8_D23 {μ φ ν ψ : ℂ → ℂ} (hμ : IsHarmonicU μ φ)
    (hμ2 : (∫⁻ u in upperHalf, ‖μ u‖ₑ ^ 2 * ENNReal.ofReal (rhoU u)) < ∞) (hν : IsHarmonicU ν ψ) :
    (∀ᵐ z ∂(volume.restrict upperHalf), IntegrableOn (fun u => μ u *
      (1 / (u - conj z) ^ 2 * dz (dzbar fun e => kernelKbar (fun y => e * ν y) u z) 0)) upperHalf) ∧
    AEMeasurable (fun z => (rhoU z : ℂ)⁻¹ * ∫ u in upperHalf, μ u *
      (1 / (u - conj z) ^ 2 * dz (dzbar fun e => kernelKbar (fun y => e * ν y) u z) 0)) (volume.restrict upperHalf) ∧
    (∫⁻ z in upperHalf, ‖(rhoU z : ℂ)⁻¹ * ∫ u in upperHalf, μ u *
      (1 / (u - conj z) ^ 2 * dz (dzbar fun e => kernelKbar (fun y => e * ν y) u z) 0)‖ₑ ^ 2 *
        ENNReal.ofReal (rhoU z)) < ∞ := by
  obtain ⟨M, hM0, hM⟩ := harmonicU_bounded hν
  have hU := measurableSet_upperHalf_aux
  have hTEf := (s7l8_TE hμ).trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hμ2))
  have hEfin := ae_lt_top' (s7l8_EL_meas hμ).aemeasurable hTEf.ne
  refine ⟨?_, s7l8_D23_meas hμ hν, ?_⟩
  · filter_upwards [ae_restrict_mem hU] with z hz
    exact (s7l8_pt_dec hμ hμ2 hν hz).1
  · have hpt := fun z (hz : z ∈ upperHalf) hEz => s7l8_D23_pt2 hμ hμ2 hν hM0 hM hz hEz
    have hc1 : (4 * ENNReal.ofReal (82 * π * M ^ 4)) ≠ ∞ := ENNReal.mul_ne_top (by norm_num) ENNReal.ofReal_ne_top
    have hc2 : (4 * ENNReal.ofReal (M ^ 4 / π)) ≠ ∞ := ENNReal.mul_ne_top (by norm_num) ENNReal.ofReal_ne_top
    refine lt_of_le_of_lt (lintegral_mono_ae (g := fun z => 4 * ENNReal.ofReal (82 * π * M ^ 4) *
        (∫⁻ u in upperHalf, ‖μ u * (1 / (u - conj z) ^ 2)‖ₑ ^ 2) +
        4 * ENNReal.ofReal (M ^ 4 / π) * ∫⁻ ξ in {ζ : ℂ | ζ.im < 0},
          ‖∫ w, upperHalf.indicator (fun w => μ w / (w - conj z) ^ 2) w / (w - ξ) ^ 2‖ₑ ^ 2) ?_) ?_
    · filter_upwards [ae_restrict_mem hU, hEfin] with z hz hEz
      exact hpt z hz hEz
    · rw [lintegral_add_left' ((s7l8_A_meas hμ).const_mul _), lintegral_const_mul' _ _ hc1,
        lintegral_const_mul' _ _ hc2]
      exact ENNReal.add_lt_top.2 ⟨ENNReal.mul_lt_top (lt_top_iff_ne_top.2 hc1)
        ((s7l8_TA hμ).trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hμ2)),
        ENNReal.mul_lt_top (lt_top_iff_ne_top.2 hc2) hTEf⟩

/-- **(D4)** `I₄ = μ G(|ν|²) ∈ L²(𝕌, ρ)` (RK3: `|G(|ν|²)| ≤ ‖ν‖²_∞/2`). -/
theorem s7l8_D4 {μ φ ν ψ : ℂ → ℂ} (hμ : IsHarmonicU μ φ)
    (hμ2 : (∫⁻ u in upperHalf, ‖μ u‖ₑ ^ 2 * ENNReal.ofReal (rhoU u)) < ∞) (hν : IsHarmonicU ν ψ) :
    AEMeasurable (fun z => μ z * resolventOpU (fun u => ((‖ν u‖ ^ 2 : ℝ) : ℂ)) z) (volume.restrict upperHalf) ∧
    (∫⁻ z in upperHalf, ‖μ z * resolventOpU (fun u => ((‖ν u‖ ^ 2 : ℝ) : ℂ)) z‖ₑ ^ 2 *
        ENNReal.ofReal (rhoU z)) < ∞ := by
  obtain ⟨M, hM0, hM⟩ := harmonicU_bounded hν
  have hU := measurableSet_upperHalf_aux
  have hb : ∀ w ∈ upperHalf, ‖(((‖ν w‖ ^ 2 : ℝ) : ℂ))‖ ≤ M ^ 2 := fun w hw => by
    rw [Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    exact pow_le_pow_left₀ (norm_nonneg _) (hM w hw) 2
  have hνc := harmonicU_continuousOn hν
  have hfc : ContinuousOn (fun w => (((‖ν w‖ ^ 2 : ℝ) : ℂ))) upperHalf :=
    Complex.continuous_ofReal.comp_continuousOn (hνc.norm.pow 2)
  have hGc := resolventOpU_continuousOn_of_continuous_bounded hfc hb
  refine ⟨((harmonicU_continuousOn hμ).mul hGc).aemeasurable hU, ?_⟩
  have hpt : ∀ z ∈ upperHalf, ‖μ z * resolventOpU (fun u => ((‖ν u‖ ^ 2 : ℝ) : ℂ)) z‖ₑ ^ 2 *
      ENNReal.ofReal (rhoU z) ≤ ENNReal.ofReal ((M ^ 2) ^ 2) * (‖μ z‖ₑ ^ 2 * ENNReal.ofReal (rhoU z)) := by
    intro z hz
    have hG : ‖resolventOpU (fun u => ((‖ν u‖ ^ 2 : ℝ) : ℂ)) z‖ₑ ^ 2 ≤ ENNReal.ofReal ((M ^ 2) ^ 2) := by
      rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _)]
      exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (norm_nonneg _) (resolventOpU_norm_le hb hz) 2)
    rw [enorm_mul, mul_pow]
    calc ‖μ z‖ₑ ^ 2 * ‖resolventOpU (fun u => ((‖ν u‖ ^ 2 : ℝ) : ℂ)) z‖ₑ ^ 2 * ENNReal.ofReal (rhoU z)
        ≤ ‖μ z‖ₑ ^ 2 * ENNReal.ofReal ((M ^ 2) ^ 2) * ENNReal.ofReal (rhoU z) := by gcongr
      _ = _ := by ring
  refine lt_of_le_of_lt (setLIntegral_mono' hU hpt) ?_
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hμ2

/-- **(E) Cayley transport.** The `𝕌`-statement for all harmonic data gives `lemma_7_8` on `𝔻*`. -/
theorem s7l8_transport {μ : ℂ → ℂ} (hμ : μ ∈ harmonicL2 unitDiscExterior) {ν : LinfStar}
    (hν : ν ∈ harmonicBeltrami)
    (hU : ∀ {m φ n ψ : ℂ → ℂ}, IsHarmonicU m φ →
      (∫⁻ u in upperHalf, ‖m u‖ₑ ^ 2 * ENNReal.ofReal (rhoU u)) < ∞ → IsHarmonicU n ψ →
      (∫⁻ z in upperHalf, ‖dzbar (dz fun ε => QfunU m (fun u => ε * n u) z) 0‖ₑ ^ 2 *
        ENNReal.ofReal (rhoU z)) < ∞) :
    normL2 unitDiscExterior (fun z => dz (dzbar fun ε => Qfun (toLinf μ) (ε • ν) z) 0) < ∞ := by
  obtain ⟨Cc, hCc⟩ := harmonicL2_subset_harmonic
  have hμL := (hCc μ hμ).1
  obtain ⟨gν, hgνs, hgν⟩ := wr_harm_rep hν
  have hgνc : ContinuousOn gν unitDiscExterior := hgνs.continuousOn
  have hμc := wp_harmonic_continuousOn hμ
  have hμae := wp_harmonic_toLinf_ae hμ
  obtain ⟨mμ, φμ, hμh, hμf⟩ := p71_wm_harm hμL hμc hμae
  obtain ⟨mν, φν, hνh, hνf⟩ := p71_wm_harm hν hgνc hgν
  have hfin := hU hμh (s7g_l3_L2fin hμ (s7g_f2_mnorm hμf)) hνh
  have hUm := measurableSet_upperHalf_aux
  -- pointwise transport at `z = S(η̄)`
  have hpt : ∀ η ∈ upperHalf, η ≠ I →
      ‖dz (dzbar fun ε => Qfun (toLinf μ) (ε • ν) (cayley (conj η))) 0‖ₑ =
        ‖dzbar (dz fun ε => QfunU mμ (fun u => ε * mν u) η) 0‖ₑ := by
    intro η hη hηI
    have hc : conj η + I ≠ 0 := s7g_l3_cne hηI
    have hz : cayley (conj η) ∈ unitDiscExterior := by
      have h1 : (conj η).im < 0 := by
        rw [Complex.conj_im]
        exact neg_neg_of_pos hη
      exact p71_cay_ext h1 hc
    have hci : cayleyInv (cayley (conj η)) = conj η := p71_cinv_cay hc
    have hy : conj (cayleyInv (cayley (conj η))) = η := by rw [hci, Complex.conj_conj]
    have hQ := p71_wm_Q hμL hν hμc hμae hgνc hgν hμf hνf hz
    rw [hy, hci] at hQ
    obtain ⟨r, hr, hG⟩ := s7l8_Q_C2 hμh hνh hη
    rw [s7l8_eps2 (F := fun ε => Qfun (toLinf μ) (ε • ν) (cayley (conj η)))
      (G := fun e => QfunU mμ (fun u => e * mν u) η) hr hG hQ, enorm_mul, RCLike.enorm_conj]
    have hd : 2 * I / (conj η + I) ^ 2 ≠ 0 :=
      div_ne_zero (mul_ne_zero two_ne_zero I_ne_zero) (pow_ne_zero _ hc)
    have h1 : ‖2 * I / (conj η + I) ^ 2 / conj (2 * I / (conj η + I) ^ 2)‖ₑ = 1 := by
      rw [← ofReal_norm, norm_div, Complex.norm_conj, div_self (norm_ne_zero_iff.mpr hd), ENNReal.ofReal_one]
    rw [h1, one_mul]
  -- change of variables `ζ = S(η̄)`
  have hnull : (upperHalf \ {I} : Set ℂ) =ᵐ[volume] upperHalf := sdiff_null_ae_eq_self (measure_singleton I)
  have hlin : (∫⁻ z in unitDiscExterior,
      (‖dz (dzbar fun ε => Qfun (toLinf μ) (ε • ν) z) 0‖₊ : ℝ≥0∞) ^ 2 * ENNReal.ofReal (rho z)) < ∞ := by
    rw [s7g_l3_cov]
    refine lt_of_le_of_lt (le_of_eq ?_) hfin
    rw [← setLIntegral_congr hnull, ← setLIntegral_congr hnull]
    refine setLIntegral_congr_fun (hUm.diff (measurableSet_singleton I)) fun η hη => ?_
    have hrho := (p71r_iso hη.1 hη.1 hη.2 hη.2).2
    have hr0 : 0 ≤ rho (cayley (conj η)) := by unfold rho; positivity
    rw [← enorm_eq_nnnorm, hpt η hη.1 hη.2, ← hrho, ENNReal.ofReal_mul hr0]
    ring
  show (∫⁻ z in unitDiscExterior,
      (‖dz (dzbar fun ε => Qfun (toLinf μ) (ε • ν) z) 0‖₊ : ℝ≥0∞) ^ 2 * ENNReal.ofReal (rho z)) ^ (1 / 2 : ℝ) < ∞
  exact ENNReal.rpow_lt_top_of_nonneg (by norm_num) hlin.ne

/-- `(a + b + c)² ≤ 4 (a² + b² + c²)` in `ℝ≥0∞`. -/
theorem s7l8_sq3 (a b c : ℝ≥0∞) : (a + b + c) ^ 2 ≤ 4 * (a ^ 2 + b ^ 2 + c ^ 2) := by
  have key : ∀ x y : ℝ≥0∞, (x + y) ^ 2 ≤ 2 * (x ^ 2 + y ^ 2) := by
    intro x y
    have h := ENNReal.rpow_add_le_mul_rpow_add_rpow x y (p := 2) (by norm_num)
    have e : ∀ t : ℝ≥0∞, t ^ (2 : ℝ) = t ^ 2 := fun t => by
      rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, ENNReal.rpow_natCast]
    have e2 : (2 : ℝ≥0∞) ^ ((2 : ℝ) - 1) = 2 := by norm_num
    rwa [e, e, e, e2] at h
  calc (a + b + c) ^ 2 ≤ 2 * ((a + b) ^ 2 + c ^ 2) := key _ _
    _ ≤ 2 * (2 * (a ^ 2 + b ^ 2) + c ^ 2) := by gcongr; exact key _ _
    _ ≤ 2 * (2 * (a ^ 2 + b ^ 2) + 2 * c ^ 2) := by gcongr; exact le_mul_of_one_le_left' (by norm_num)
    _ = 4 * (a ^ 2 + b ^ 2 + c ^ 2) := by ring

/-- Finiteness of `∫⁻ ‖f‖ₑ² ρ` for `f = c₁ f₁ + c₂ f₂ - f₃` a.e., each `f_i` a.e.-measurable with finite norm. -/
theorem s7l8_l2_comb {f f₁ f₂ f₃ : ℂ → ℂ} (c₁ c₂ : ℂ)
    (hf : ∀ᵐ z ∂(volume.restrict upperHalf), f z = c₁ * f₁ z + c₂ * f₂ z - f₃ z)
    (hm₁ : AEMeasurable f₁ (volume.restrict upperHalf)) (hm₂ : AEMeasurable f₂ (volume.restrict upperHalf))
    (hm₃ : AEMeasurable f₃ (volume.restrict upperHalf))
    (h₁ : (∫⁻ z in upperHalf, ‖f₁ z‖ₑ ^ 2 * ENNReal.ofReal (rhoU z)) < ∞)
    (h₂ : (∫⁻ z in upperHalf, ‖f₂ z‖ₑ ^ 2 * ENNReal.ofReal (rhoU z)) < ∞)
    (h₃ : (∫⁻ z in upperHalf, ‖f₃ z‖ₑ ^ 2 * ENNReal.ofReal (rhoU z)) < ∞) :
    (∫⁻ z in upperHalf, ‖f z‖ₑ ^ 2 * ENNReal.ofReal (rhoU z)) < ∞ := by
  have hρ : AEMeasurable (fun z : ℂ => ENNReal.ofReal (rhoU z)) (volume.restrict upperHalf) :=
    (ENNReal.measurable_ofReal.comp (by unfold rhoU; fun_prop)).aemeasurable
  have hle : ∀ᵐ z ∂(volume.restrict upperHalf), ‖f z‖ₑ ^ 2 * ENNReal.ofReal (rhoU z) ≤
      4 * (‖c₁‖ₑ ^ 2 * (‖f₁ z‖ₑ ^ 2 * ENNReal.ofReal (rhoU z)) + ‖c₂‖ₑ ^ 2 * (‖f₂ z‖ₑ ^ 2 * ENNReal.ofReal (rhoU z)) +
        ‖f₃ z‖ₑ ^ 2 * ENNReal.ofReal (rhoU z)) := by
    filter_upwards [hf] with z hz
    have he : ‖f z‖ₑ ≤ ‖c₁‖ₑ * ‖f₁ z‖ₑ + ‖c₂‖ₑ * ‖f₂ z‖ₑ + ‖f₃ z‖ₑ := by
      rw [hz, ← enorm_mul, ← enorm_mul]
      exact (enorm_sub_le).trans (add_le_add (enorm_add_le _ _) le_rfl)
    calc ‖f z‖ₑ ^ 2 * ENNReal.ofReal (rhoU z)
        ≤ (‖c₁‖ₑ * ‖f₁ z‖ₑ + ‖c₂‖ₑ * ‖f₂ z‖ₑ + ‖f₃ z‖ₑ) ^ 2 * ENNReal.ofReal (rhoU z) := by gcongr
      _ ≤ 4 * ((‖c₁‖ₑ * ‖f₁ z‖ₑ) ^ 2 + (‖c₂‖ₑ * ‖f₂ z‖ₑ) ^ 2 + ‖f₃ z‖ₑ ^ 2) * ENNReal.ofReal (rhoU z) := by
          gcongr; exact s7l8_sq3 _ _ _
      _ = _ := by ring
  refine lt_of_le_of_lt (lintegral_mono_ae hle) ?_
  have hA₁ : AEMeasurable (fun z => ‖c₁‖ₑ ^ 2 * (‖f₁ z‖ₑ ^ 2 * ENNReal.ofReal (rhoU z)))
      (volume.restrict upperHalf) := aemeasurable_const.mul ((hm₁.enorm.pow_const 2).mul hρ)
  have hA₂ : AEMeasurable (fun z => ‖c₂‖ₑ ^ 2 * (‖f₂ z‖ₑ ^ 2 * ENNReal.ofReal (rhoU z)))
      (volume.restrict upperHalf) := aemeasurable_const.mul ((hm₂.enorm.pow_const 2).mul hρ)
  have hAB : AEMeasurable (fun z => ‖c₁‖ₑ ^ 2 * (‖f₁ z‖ₑ ^ 2 * ENNReal.ofReal (rhoU z)) +
      ‖c₂‖ₑ ^ 2 * (‖f₂ z‖ₑ ^ 2 * ENNReal.ofReal (rhoU z))) (volume.restrict upperHalf) := hA₁.add hA₂
  rw [lintegral_const_mul' _ _ (by norm_num), lintegral_add_left' hAB, lintegral_add_left' hA₁,
    lintegral_const_mul' _ _ (by simp), lintegral_const_mul' _ _ (by simp)]
  refine ENNReal.mul_lt_top (by norm_num) ?_
  exact ENNReal.add_lt_top.2 ⟨ENNReal.add_lt_top.2 ⟨ENNReal.mul_lt_top (by simp) h₁,
    ENNReal.mul_lt_top (by simp) h₂⟩, h₃⟩

/-- **Assembly in `𝕌`.** `Q̈ ∈ L²(𝕌, ρ)` (both orders). -/
theorem s7l8_U {μ φ ν ψ : ℂ → ℂ} (hμ : IsHarmonicU μ φ)
    (hμ2 : (∫⁻ u in upperHalf, ‖μ u‖ₑ ^ 2 * ENNReal.ofReal (rhoU u)) < ∞) (hν : IsHarmonicU ν ψ) :
    (∫⁻ z in upperHalf, ‖dz (dzbar fun ε => QfunU μ (fun u => ε * ν u) z) 0‖ₑ ^ 2 *
        ENNReal.ofReal (rhoU z)) < ∞ ∧
      (∫⁻ z in upperHalf, ‖dzbar (dz fun ε => QfunU μ (fun u => ε * ν u) z) 0‖ₑ ^ 2 *
        ENNReal.ofReal (rhoU z)) < ∞ := by
  obtain ⟨hI1, hm1, hT1⟩ := s7l8_D1 hμ hμ2 hν
  obtain ⟨hI23, hm23, hT23⟩ := s7l8_D23 hμ hμ2 hν
  obtain ⟨hm4, hT4⟩ := s7l8_D4 hμ hμ2 hν
  have hU := measurableSet_upperHalf_aux
  -- the a.e. decomposition `(12/π) J̈/ρ = (24/π) I₂₃ + (24/π) I₁`
  have hJ : ∀ᵐ z ∂(volume.restrict upperHalf),
      (12 / π : ℂ) * (∫ u in upperHalf, μ u * dz (dzbar fun e => kernelKbar (fun y => e * ν y) u z ^ 2) 0) /
          (rhoU z : ℂ) - μ z * resolventOpU (fun u => ((‖ν u‖ ^ 2 : ℝ) : ℂ)) z =
        (24 / π : ℂ) * ((rhoU z : ℂ)⁻¹ * ∫ u in upperHalf, μ u *
            (1 / (u - conj z) ^ 2 * dz (dzbar fun e => kernelKbar (fun y => e * ν y) u z) 0)) +
          (24 / π : ℂ) * ((rhoU z : ℂ)⁻¹ * ∫ u in upperHalf, μ u *
            (dz (fun e => kernelKbar (fun y => e * ν y) u z) 0 *
              dzbar (fun e => kernelKbar (fun y => e * ν y) u z) 0)) -
          μ z * resolventOpU (fun u => ((‖ν u‖ ^ 2 : ℝ) : ℂ)) z := by
    filter_upwards [hI1, hI23, ae_restrict_mem hU] with z h1 h23 hz
    have hcongr : (∫ u in upperHalf, μ u * dz (dzbar fun e => kernelKbar (fun y => e * ν y) u z ^ 2) 0) =
        ∫ u in upperHalf, (2 * (μ u * (1 / (u - conj z) ^ 2 *
            dz (dzbar fun e => kernelKbar (fun y => e * ν y) u z) 0)) +
          2 * (μ u * (dz (fun e => kernelKbar (fun y => e * ν y) u z) 0 *
            dzbar (fun e => kernelKbar (fun y => e * ν y) u z) 0))) := by
      refine setIntegral_congr_fun hU fun u hu => ?_
      rw [s7l8_B_product hν hu hz]
      ring
    rw [hcongr, integral_add (h23.const_mul 2) (h1.const_mul 2), integral_const_mul, integral_const_mul]
    have hρ : (rhoU z : ℂ) ≠ 0 := by
      have : 0 < z.im := hz
      unfold rhoU
      exact_mod_cast (inv_pos.mpr (pow_pos this 2)).ne'
    field_simp
    ring
  have hfin := fun (f : ℂ → ℂ) (hf : ∀ z ∈ upperHalf, f z =
      (12 / π : ℂ) * (∫ u in upperHalf, μ u * dz (dzbar fun e => kernelKbar (fun y => e * ν y) u z ^ 2) 0) /
          (rhoU z : ℂ) - μ z * resolventOpU (fun u => ((‖ν u‖ ^ 2 : ℝ) : ℂ)) z) =>
    s7l8_l2_comb (f := f) (24 / π) (24 / π)
      (by filter_upwards [hJ, ae_restrict_mem hU] with z hz hzU; rw [hf z hzU, hz]) hm23 hm1 hm4 hT23 hT1 hT4
  exact ⟨hfin _ fun z hz => (s7l8_A_pointwise hμ hν hz).1, hfin _ fun z hz => (s7l8_A_pointwise hμ hν hz).2⟩

/-- **Lemma 7.8** (TT:2892–2896). For `μ ∈ H^{-1,1}(𝔻*)` and `ν ∈ Ω^{-1,1}(𝔻*)`:
`∂²/∂ε∂ε̄ Q(μ, εν)|_{ε=0} ∈ L²(𝔻*, ρ d²z)`. -/
theorem s7l8_lemma_7_8 {μ : ℂ → ℂ} (hμ : μ ∈ harmonicL2 unitDiscExterior) {ν : LinfStar} (hν : ν ∈ harmonicBeltrami) :
    normL2 unitDiscExterior (fun z => dz (dzbar fun ε => Qfun (toLinf μ) (ε • ν) z) 0) < ∞ :=
  s7l8_transport hμ hν fun hm hm2 hn => (s7l8_U hm hm2 hn).2

/-- **Lemma 7.8** (TT:2892–2896). For `μ ∈ H^{-1,1}(𝔻*)` and `ν ∈ Ω^{-1,1}(𝔻*)`:
`∂²/∂ε∂ε̄ Q(μ, εν)|_{ε=0} ∈ L²(𝔻*, ρ d²z)`. -/
theorem lemma_7_8 {μ : ℂ → ℂ} (hμ : μ ∈ harmonicL2 unitDiscExterior) {ν : LinfStar} (hν : ν ∈ harmonicBeltrami) :
    normL2 unitDiscExterior (fun z => dz (dzbar fun ε => Qfun (toLinf μ) (ε • ν) z) 0) < ∞ := by
  exact s7l8_lemma_7_8 hμ hν

end TakhtajanTeo
