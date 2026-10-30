import TakhtajanTeo.Ch1.S1_5_Variational
import TakhtajanTeo.Ch1.GroupInverseLimit

/-!
# W-REG foundation: joint regularity of the Beltrami solution in (parameter, point)

Interface for the new host `TakhtajanTeo/Ch1/WRegFoundation.lean`, prefix `wr_`. Drafted by 下属1 on 2026-10-27;
all stubs are now proved; see the delivery report for the owners of each block. Owners are marked `[W1]` = 下属1, `[W4]` = 下属4 and `[W5]` = 下属5.

**Route** (no Sobolev spaces, no Schauder estimates):
* **Parameters.** `P = (a, b) ∈ ℂ²` with coefficient `a·m₁ + b·m₂`, so that `extU (ε μ) = ε·m₁ + ε̄·m₂`.
  `P ↦ w_P(z)` is separately holomorphic in `a` and in `b` (thm13_8) and jointly continuous in `(P, z)` (normal
  families). The two-variable Cauchy formula (B2) then writes `w_P(z)` as a torus integral of `w_Q(z)` against a
  kernel smooth in `P`.
* **Local factorization at `z₀ ∈ Ω`, where `m₁, m₂` are smooth.** Take a cutoff `χ ∈ C_c^∞(Ω)` with `χ = 1` near
  `z₀`, and let `G_Q` be the solution with the compactly supported smooth coefficient `χ·(q₁m₁ + q₂m₂)`. By
  `same_dilatation_conformal` (LiZhongQC S13:3616), `H_Q = w_Q ∘ G_Q⁻¹` is holomorphic near `G_Q(z₀)`. Cauchy's
  formula on a fixed circle gives `w_Q(z) = (2πi)⁻¹ ∮ H_Q(ξ)/(ξ - G_Q(z)) dξ`.
* **Combining.** `w_P(z) = ∭ H_Q(ξ) · k(ξ, G_Q(z)) · K(Q, P)`. Only the **z-derivatives of `G_Q` with continuous
  dependence on `Q`** are needed, plus continuity of `H`. Differentiation under the integral sign (B1) gives joint
  `C³` in `(P, z)`.
* **Smooth compactly supported case (A3).** Neumann series `ω_Q = Σ (ν_Q H)^n ν_Q`. Every term is `C_c^∞`, and
  `∂^α` commutes with `H`. The weighted norm `Σ_{|α|≤3} δ^{|α|}‖∂^α f‖_p`, with small `δ`, makes `f ↦ ν_Q H f` a
  contraction whenever `sup|ν_Q| · Λ_p < 1`, so no smallness of the derivatives of `ν` is needed. `T` maps
  `L^p` functions with support in a fixed ball to `C⁰` with a sup bound (A2), so the derivatives of
  `G_Q = z + T ω_Q + affine` converge uniformly.

**Import note.** `Appendix/AppACont` transitively imports S6/S7/S8, so this host cannot import it if S6/S7 are
to import this host. The plane-inverse continuity C3 is therefore restated (`[W5]`). Alternatively, the leader
moves `acc_inv_cont`/`acc_mob_cont` to a low module.
-/

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal ComplexConjugate Classical Real

noncomputable section

namespace TakhtajanTeo

open LiZhongQC

/-- `ζ ↦ Dω(ζ) w` has derivative `v ↦ D²ω(ζ) v w`. -/
theorem wr_hasFDerivAt_fderiv_apply {ω : ℂ → ℂ} {ζ : ℂ} (hd : DifferentiableAt ℝ (fderiv ℝ ω) ζ) (w : ℂ) :
    HasFDerivAt (fun x => fderiv ℝ ω x w)
      ((ContinuousLinearMap.apply ℝ ℂ w).comp (fderiv ℝ (fderiv ℝ ω) ζ)) ζ :=
  (ContinuousLinearMap.apply ℝ ℂ w).hasFDerivAt.comp ζ hd.hasFDerivAt

/-- The derivative of `dz ω` in direction `v`, in terms of `D²ω`. -/
theorem wr_fderiv_dz_apply {ω : ℂ → ℂ} {ζ : ℂ} (hd : DifferentiableAt ℝ (fderiv ℝ ω) ζ) (v : ℂ) :
    fderiv ℝ (dz ω) ζ v =
      (fderiv ℝ (fderiv ℝ ω) ζ v 1 - I * fderiv ℝ (fderiv ℝ ω) ζ v I) / 2 := by
  have h1 := wr_hasFDerivAt_fderiv_apply hd 1
  have hI := wr_hasFDerivAt_fderiv_apply hd I
  have h := HasFDerivAt.const_mul (HasFDerivAt.sub h1 (hI.const_mul I)) (2 : ℂ)⁻¹
  have heq : dz ω = fun x => (2 : ℂ)⁻¹ * (fderiv ℝ ω x 1 - I * fderiv ℝ ω x I) := by
    funext x
    show (fderiv ℝ ω x 1 - I * fderiv ℝ ω x I) / 2 = _
    rw [div_eq_inv_mul]
  rw [heq, show (fun x => (2 : ℂ)⁻¹ * (fderiv ℝ ω x 1 - I * fderiv ℝ ω x I)) =
      (fun y => (2 : ℂ)⁻¹ * ((fun x => fderiv ℝ ω x 1) - fun y => I * fderiv ℝ ω y I) y) from rfl, h.fderiv]
  simp [div_eq_inv_mul]

/-- `dz` of a directional derivative, in terms of `D²ω`. -/
theorem wr_dz_fderiv_apply {ω : ℂ → ℂ} {ζ : ℂ} (hd : DifferentiableAt ℝ (fderiv ℝ ω) ζ) (v : ℂ) :
    dz (fun x => fderiv ℝ ω x v) ζ =
      (fderiv ℝ (fderiv ℝ ω) ζ 1 v - I * fderiv ℝ (fderiv ℝ ω) ζ I v) / 2 := by
  show (fderiv ℝ (fun x => fderiv ℝ ω x v) ζ 1 - I * fderiv ℝ (fun x => fderiv ℝ ω x v) ζ I) / 2 = _
  rw [(wr_hasFDerivAt_fderiv_apply hd v).fderiv]
  simp

theorem wr_cauchyT_contDiff_top {ω : ℂ → ℂ} (hω : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ω)
    (hc : HasCompactSupport ω) : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (cauchyT ω) := by
  rw [cauchyT_eq_convolution]
  exact hc.contDiff_convolution_right _ locallyIntegrable_cauchyKernel hω

theorem wr_dz_contDiff_top {ω : ℂ → ℂ} (hω : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ω) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (dz ω) := by
  have hD : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fderiv ℝ ω) := hω.fderiv_right (by simp)
  have heq : dz ω = fun x => (fderiv ℝ ω x 1 - I * fderiv ℝ ω x I) / 2 := rfl
  rw [heq]
  exact ((hD.clm_apply contDiff_const).sub (contDiff_const.mul (hD.clm_apply contDiff_const))).div_const 2

theorem wr_dz_hasCompactSupport {ω : ℂ → ℂ} (hc : HasCompactSupport ω) : HasCompactSupport (dz ω) := by
  apply (hc.fderiv (𝕜 := ℝ)).mono
  intro z hz
  contrapose hz
  simp only [Function.mem_support, not_not] at hz ⊢
  show (fderiv ℝ ω z 1 - I * fderiv ℝ ω z I) / 2 = 0
  rw [hz]
  simp

theorem wr_fderiv_apply_contDiff_top {ω : ℂ → ℂ} (hω : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ω) (v : ℂ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun ζ => fderiv ℝ ω ζ v) :=
  (hω.fderiv_right (m := ((⊤ : ℕ∞) : WithTop ℕ∞)) (by simp)).clm_apply contDiff_const

theorem wr_fderiv_apply_hasCompactSupport {ω : ℂ → ℂ} (hc : HasCompactSupport ω) (v : ℂ) :
    HasCompactSupport (fun ζ => fderiv ℝ ω ζ v) := by
  apply (hc.fderiv (𝕜 := ℝ)).mono
  intro z hz
  contrapose hz
  simp only [Function.mem_support, not_not] at hz ⊢
  rw [hz]
  simp

/-- (A1) `[W1]` The Hilbert transform of a `C_c^∞` function is smooth and commutes with real directional
derivatives. -/
theorem wr_hilbertSmooth_fderiv {ω : ℂ → ℂ} (hω : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ω)
    (hc : HasCompactSupport ω) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (hilbertHSmooth ω) ∧
      ∀ z v : ℂ, fderiv ℝ (hilbertHSmooth ω) z v = hilbertHSmooth (fun ζ => fderiv ℝ ω ζ v) z := by
  have hH := (i1_hilbertH_eq_cauchyT_dz hω hc).1
  have hdz := wr_dz_contDiff_top hω
  have hdzc := wr_dz_hasCompactSupport hc
  refine ⟨?_, fun z v => ?_⟩
  · rw [hH]
    exact wr_cauchyT_contDiff_top hdz hdzc
  · rw [hH, fderiv_cauchyT_apply (hdz.of_le (by simp)) hdzc,
      (i1_hilbertH_eq_cauchyT_dz (wr_fderiv_apply_contDiff_top hω v) (wr_fderiv_apply_hasCompactSupport hc v)).1]
    congr 1
    funext ζ
    have hd : DifferentiableAt ℝ (fderiv ℝ ω) ζ :=
      ((hω.fderiv_right (m := ((⊤ : ℕ∞) : WithTop ℕ∞)) (by simp)).differentiable (by simp)) ζ
    have hsymm := (hω.contDiffAt (x := ζ)).isSymmSndFDerivAt (by simp)
    rw [wr_fderiv_dz_apply hd, wr_dz_fderiv_apply hd, hsymm v 1, hsymm v I]

/-- (E1) `[W1]` `extU (ε μ) = ε·m₁ + ε̄·m₂`. -/
theorem wr_extU_smul (μ : ℂ → ℂ) (ε : ℂ) :
    extU (fun u => ε * μ u) = fun u => ε * (if 0 < u.im then μ u else 0) +
      conj ε * (if u.im < 0 then conj (μ (conj u)) else 0) := by
  funext u
  unfold extU
  by_cases h1 : 0 < u.im
  · have h2 : ¬ u.im < 0 := by linarith
    simp only [h1, h2, ↓reduceIte, mul_zero, add_zero]
  · by_cases h2 : u.im < 0
    · simp only [h1, h2, ↓reduceIte, mul_zero, zero_add, map_mul]
    · simp only [h1, h2, ↓reduceIte, mul_zero, add_zero]

/-- (E4) `[W1]` Harmonic Beltrami differentials on `𝕌` are smooth there (feeds E2 for the `IsHarmonicU` items). -/
theorem wr_isHarmonicU_contDiffOn {μ φ : ℂ → ℂ} (hμ : IsHarmonicU μ φ) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) μ upperHalf := by
  have hU : IsOpen upperHalf := isOpen_lt continuous_const Complex.continuous_im
  have hφ : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ upperHalf :=
    (hμ.1.contDiffOn hU).restrict_scalars ℝ
  have hc : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z => conj (φ z)) upperHalf :=
    Complex.conjCLE.contDiff.comp_contDiffOn hφ
  have hpoly : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : ℂ => (z - conj z) ^ 2 / 2) :=
    ((contDiff_id.sub Complex.conjCLE.contDiff).pow 2).div_const 2
  exact (hpoly.contDiffOn.mul hc).congr fun z hz => hμ.2.2 z hz


/-- (A2) `[W1]` Sup bound of the Cauchy transform on `L^p` functions (`p > 2`) supported in a fixed ball. -/
theorem wr_cauchyT_sup_le {p R : ℝ} (hp : 2 < p) (hR : 0 < R) :
    ∃ C : ℝ, ∀ ω : ℂ → ℂ, MemLp ω (ENNReal.ofReal p) → Function.support ω ⊆ closedBall 0 R →
      ∀ z ∈ closedBall (0 : ℂ) R, ‖cauchyT ω z‖ ≤ C * (eLpNorm ω (ENNReal.ofReal p)).toReal := by
  obtain ⟨M, hM⟩ := lemma11_1 hp hR
  refine ⟨M, fun ω hω hs z _ => hM ω hω (fun y hy => ?_) z⟩
  by_contra h
  have hy' := hs h
  rw [mem_closedBall_zero_iff] at hy'
  linarith

/-- `L^p` bound of the smooth Hilbert transform on `C_c^∞`. -/
theorem wr_hS_eLpNorm_le {p : ℝ} (hp : 1 < p) {φ : ℂ → ℂ} (hφ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ)
    (hc : HasCompactSupport φ) :
    eLpNorm (hilbertHSmooth φ) (ENNReal.ofReal p) ≤
      ENNReal.ofReal (hilbertNorm p) * eLpNorm φ (ENNReal.ofReal p) := by
  have hm : MemLp φ (ENNReal.ofReal p) := hφ.continuous.memLp_of_hasCompactSupport hc
  rw [← eLpNorm_congr_ae (hilbertH_eq_ae_smooth hφ hc)]
  exact eq11_16_eLpNorm hp hm

/-- `L^p` bound of `c · H φ` for a bounded measurable `c`. -/
theorem wr_mul_hS_eLpNorm_le {p : ℝ} (hp : 1 < p) {c φ : ℂ → ℂ} {K : ℝ} (hK : 0 ≤ K)
    (hcm : AEStronglyMeasurable c volume) (hcK : ∀ z, ‖c z‖ ≤ K)
    (hφ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ) (hc : HasCompactSupport φ) :
    eLpNorm (fun z => c z * hilbertHSmooth φ z) (ENNReal.ofReal p) ≤
      ENNReal.ofReal (K * hilbertNorm p) * eLpNorm φ (ENNReal.ofReal p) := by
  have hHc : Continuous (hilbertHSmooth φ) := (wr_hilbertSmooth_fderiv hφ hc).1.continuous
  have h1 : eLpNorm (fun z => c z * hilbertHSmooth φ z) (ENNReal.ofReal p) ≤
      ENNReal.ofReal K * eLpNorm (hilbertHSmooth φ) (ENNReal.ofReal p) := by
    refine eLpNorm_le_mul_eLpNorm_of_ae_le_mul (hcm.mul hHc.aestronglyMeasurable) ?_ _
    filter_upwards with z
    show ‖c z * hilbertHSmooth φ z‖ ≤ K * ‖hilbertHSmooth φ z‖
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (hcK z) (norm_nonneg _)
  refine h1.trans ?_
  rw [ENNReal.ofReal_mul hK, mul_assoc]
  exact mul_le_mul_right (wr_hS_eLpNorm_le hp hφ hc) _

/-- Real form of the previous bound. -/
theorem wr_mul_hS_norm_le {p : ℝ} (hp : 1 < p) {c φ : ℂ → ℂ} {K : ℝ} (hK : 0 ≤ K)
    (hcm : AEStronglyMeasurable c volume) (hcK : ∀ z, ‖c z‖ ≤ K)
    (hφ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ) (hc : HasCompactSupport φ) :
    (eLpNorm (fun z => c z * hilbertHSmooth φ z) (ENNReal.ofReal p)).toReal ≤
      K * hilbertNorm p * (eLpNorm φ (ENNReal.ofReal p)).toReal := by
  have hm : MemLp φ (ENNReal.ofReal p) := hφ.continuous.memLp_of_hasCompactSupport hc
  have hfin : ENNReal.ofReal (K * hilbertNorm p) * eLpNorm φ (ENNReal.ofReal p) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hm.eLpNorm_ne_top
  have h := ENNReal.toReal_mono hfin (wr_mul_hS_eLpNorm_le hp hK hcm hcK hφ hc)
  rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal (mul_nonneg hK (hilbertNorm_nonneg p))] at h

/-- Triangle inequality for the real `L^p` norm. -/
theorem wr_norm_add_le {p : ℝ} (hp : 1 ≤ p) {f g : ℂ → ℂ} (hf : MemLp f (ENNReal.ofReal p))
    (hg : MemLp g (ENNReal.ofReal p)) :
    (eLpNorm (fun z => f z + g z) (ENNReal.ofReal p)).toReal ≤
      (eLpNorm f (ENNReal.ofReal p)).toReal + (eLpNorm g (ENNReal.ofReal p)).toReal := by
  have h1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by simpa using ENNReal.ofReal_le_ofReal hp
  have h : eLpNorm (f + g) (ENNReal.ofReal p) ≤ eLpNorm f (ENNReal.ofReal p) + eLpNorm g (ENNReal.ofReal p) :=
    eLpNorm_add_le h1
  have hfin : eLpNorm f (ENNReal.ofReal p) + eLpNorm g (ENNReal.ofReal p) ≠ ⊤ :=
    ENNReal.add_ne_top.2 ⟨hf.eLpNorm_ne_top, hg.eLpNorm_ne_top⟩
  have h' := ENNReal.toReal_mono hfin h
  rw [ENNReal.toReal_add hf.eLpNorm_ne_top hg.eLpNorm_ne_top] at h'
  exact h'

/-- Geometric bound for a forced linear recursion `b (n+1) ≤ r b n + A ρ^n`, `0 ≤ r < ρ`. -/
theorem wr_geom_bound {b : ℕ → ℝ} {r ρ A : ℝ} (hr : 0 ≤ r) (hrρ : r < ρ) (_hA : 0 ≤ A)
    (hrec : ∀ n, b (n + 1) ≤ r * b n + A * ρ ^ n) :
    ∀ n, b n ≤ max (b 0) (A / (ρ - r)) * ρ ^ n := by
  have hρr : 0 < ρ - r := sub_pos.2 hrρ
  have hρ : 0 ≤ ρ := hr.trans hrρ.le
  set C := max (b 0) (A / (ρ - r)) with hC
  have hCA : A ≤ (ρ - r) * C := by
    have : A / (ρ - r) ≤ C := le_max_right _ _
    rw [div_le_iff₀ hρr] at this
    linarith
  intro n
  induction n with
  | zero => simp [hC]
  | succ n ih =>
    calc b (n + 1) ≤ r * b n + A * ρ ^ n := hrec n
      _ ≤ r * (C * ρ ^ n) + A * ρ ^ n := by gcongr
      _ ≤ r * (C * ρ ^ n) + (ρ - r) * C * ρ ^ n := by gcongr
      _ = C * ρ ^ (n + 1) := by ring

/-- **Forced Neumann iteration.** If `x (n+1) = ν · H(x n) + F n` with `|ν| ≤ k`, `‖F n‖_p ≤ A ρ^n` and
`k Λ_p < ρ`, then `‖x n‖_p ≤ C ρ^n`. -/
theorem wr_level {p : ℝ} (hp : 1 < p) {ν : ℂ → ℂ} {k : ℝ} (hk : 0 ≤ k) (hνm : AEStronglyMeasurable ν volume)
    (hνk : ∀ z, ‖ν z‖ ≤ k) {x F : ℕ → ℂ → ℂ} (hx : ∀ n, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (x n))
    (hxc : ∀ n, HasCompactSupport (x n)) (hF : ∀ n, MemLp (F n) (ENNReal.ofReal p))
    (hrec : ∀ n, x (n + 1) = fun z => ν z * hilbertHSmooth (x n) z + F n z)
    {ρ A : ℝ} (hρ : k * hilbertNorm p < ρ) (hA : 0 ≤ A)
    (hFb : ∀ n, (eLpNorm (F n) (ENNReal.ofReal p)).toReal ≤ A * ρ ^ n) :
    ∀ n, (eLpNorm (x n) (ENNReal.ofReal p)).toReal ≤
      max (eLpNorm (x 0) (ENNReal.ofReal p)).toReal (A / (ρ - k * hilbertNorm p)) * ρ ^ n := by
  refine wr_geom_bound (b := fun n => (eLpNorm (x n) (ENNReal.ofReal p)).toReal)
    (mul_nonneg hk (hilbertNorm_nonneg p)) hρ hA (fun n => ?_)
  have hHc : Continuous (hilbertHSmooth (x n)) := (wr_hilbertSmooth_fderiv (hx n) (hxc n)).1.continuous
  have hxm : MemLp (x n) (ENNReal.ofReal p) := (hx n).continuous.memLp_of_hasCompactSupport (hxc n)
  have hm1 : MemLp (fun z => ν z * hilbertHSmooth (x n) z) (ENNReal.ofReal p) := by
    exact lt_of_le_of_lt (wr_mul_hS_eLpNorm_le hp hk hνm hνk (hx n) (hxc n))
      (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hxm.eLpNorm_lt_top)
  have e1 := wr_norm_add_le hp.le hm1 (hF n)
  have e2 := wr_mul_hS_norm_le hp hk hνm hνk (hx n) (hxc n)
  have e3 := hFb n
  have hb : (eLpNorm (x (n + 1)) (ENNReal.ofReal p)).toReal ≤
      (eLpNorm (fun z => ν z * hilbertHSmooth (x n) z) (ENNReal.ofReal p)).toReal +
        (eLpNorm (F n) (ENNReal.ofReal p)).toReal := by
    rw [hrec n]
    exact e1
  exact hb.trans (by linarith)


/-- `c · H y` is `C_c^∞` when `c` and `y` are. -/
theorem wr_mul_hS_smooth {c y : ℂ → ℂ} (hc : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) c) (hcc : HasCompactSupport c)
    (hy : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) y) (hyc : HasCompactSupport y) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z => c z * hilbertHSmooth y z) ∧
      HasCompactSupport (fun z => c z * hilbertHSmooth y z) :=
  ⟨hc.mul (wr_hilbertSmooth_fderiv hy hyc).1, hcc.mul_right⟩

/-- Leibniz rule for `c · H y`, with `∂` commuting with `H`. -/
theorem wr_D_mul_hS {c y : ℂ → ℂ} (hc : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) c)
    (hy : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) y) (hyc : HasCompactSupport y) (v : ℂ) :
    (fun z => fderiv ℝ (fun z => c z * hilbertHSmooth y z) z v) =
      fun z => fderiv ℝ c z v * hilbertHSmooth y z + c z * hilbertHSmooth (fun z => fderiv ℝ y z v) z := by
  have hH := wr_hilbertSmooth_fderiv hy hyc
  funext z
  rw [fderiv_fun_mul (hc.differentiable (by simp) z) (hH.1.differentiable (by simp) z)]
  simp only [FunLike.coe_add, FunLike.coe_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul, hH.2 z v]
  ring

/-- `∂_v` of a sum of smooth functions. -/
theorem wr_D_add {f g : ℂ → ℂ} (hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f)
    (hg : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g) (v : ℂ) :
    (fun z => fderiv ℝ (fun z => f z + g z) z v) = fun z => fderiv ℝ f z v + fderiv ℝ g z v := by
  funext z
  rw [fderiv_fun_add (hf.differentiable (by simp) z) (hg.differentiable (by simp) z)]
  rfl

/-- The Neumann terms are `C_c^∞`. -/
theorem wr_iter_smooth {ν : ℂ → ℂ} (hν : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ν) (hνc : HasCompactSupport ν)
    {s : ℕ → ℂ → ℂ} (hs0 : s 0 = ν) (hs : ∀ n, s (n + 1) = fun z => ν z * hilbertHSmooth (s n) z) (n : ℕ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (s n) ∧ HasCompactSupport (s n) := by
  induction n with
  | zero =>
    exact (congrArg (fun f => ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f ∧ HasCompactSupport f) hs0).mpr ⟨hν, hνc⟩
  | succ n ih =>
    exact (congrArg (fun f => ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f ∧ HasCompactSupport f) (hs n)).mpr
      (wr_mul_hS_smooth hν hνc ih.1 ih.2)

/-- `C_c^∞` functions are in `L^p`. -/
theorem wr_memLp {f : ℂ → ℂ} (hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f) (hfc : HasCompactSupport f) (p : ℝ) :
    MemLp f (ENNReal.ofReal p) :=
  hf.continuous.memLp_of_hasCompactSupport hfc

/-- Bound of one forcing term `c · H(y n)`. -/
theorem wr_term_bound {p : ℝ} (hp : 1 < p) {c : ℂ → ℂ} {y : ℕ → ℂ → ℂ} {B C ρ : ℝ} (hB : 0 ≤ B)
    (hc : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) c) (hcB : ∀ z, ‖c z‖ ≤ B)
    (hy : ∀ n, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (y n)) (hyc : ∀ n, HasCompactSupport (y n))
    (hyb : ∀ n, (eLpNorm (y n) (ENNReal.ofReal p)).toReal ≤ C * ρ ^ n) (n : ℕ) :
    (eLpNorm (fun z => c z * hilbertHSmooth (y n) z) (ENNReal.ofReal p)).toReal ≤
      B * hilbertNorm p * C * ρ ^ n := by
  have h := wr_mul_hS_norm_le hp hB hc.continuous.aestronglyMeasurable hcB (hy n) (hyc n)
  have hBΛ : 0 ≤ B * hilbertNorm p := mul_nonneg hB (hilbertNorm_nonneg p)
  have h2 : B * hilbertNorm p * (eLpNorm (y n) (ENNReal.ofReal p)).toReal ≤ B * hilbertNorm p * (C * ρ ^ n) :=
    mul_le_mul_of_nonneg_left (hyb n) hBΛ
  have h3 : B * hilbertNorm p * (C * ρ ^ n) = B * hilbertNorm p * C * ρ ^ n := by ring
  exact h.trans (h2.trans h3.le)

/-- Finishing step of a level: from `wr_level` and the initial bound. -/
theorem wr_level_finish {a L A ρ r G E : ℝ} (hL : 0 ≤ L) (_hrρ : r < ρ) (ha : a ≤ L) (hρ : 0 ≤ ρ)
    (hAG : A / (ρ - r) ≤ G * E) (hLE : L ≤ E) (hG : 0 ≤ G) {b : ℝ} (n : ℕ)
    (hb : b ≤ max a (A / (ρ - r)) * ρ ^ n) : b ≤ E * (1 + G) * ρ ^ n := by
  have hE : 0 ≤ E := hL.trans hLE
  have hm : max a (A / (ρ - r)) ≤ E * (1 + G) := by
    apply max_le
    · nlinarith
    · nlinarith
  calc b ≤ max a (A / (ρ - r)) * ρ ^ n := hb
    _ ≤ E * (1 + G) * ρ ^ n := mul_le_mul_of_nonneg_right hm (pow_nonneg hρ n)


/-- Smooth compact support is preserved by directional derivatives. -/
theorem wr_D_sc {f : ℂ → ℂ} (hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f ∧ HasCompactSupport f) (v : ℂ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z => fderiv ℝ f z v) ∧
      HasCompactSupport (fun z => fderiv ℝ f z v) :=
  ⟨wr_fderiv_apply_contDiff_top hf.1 v, wr_fderiv_apply_hasCompactSupport hf.2 v⟩

/-- Triangle inequality for three `C_c^∞` summands. -/
theorem wr_norm_add3_le {p : ℝ} (hp : 1 ≤ p) {f g h : ℂ → ℂ}
    (hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f ∧ HasCompactSupport f)
    (hg : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g ∧ HasCompactSupport g)
    (hh : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) h ∧ HasCompactSupport h) :
    (eLpNorm (fun z => f z + (g z + h z)) (ENNReal.ofReal p)).toReal ≤
      (eLpNorm f (ENNReal.ofReal p)).toReal + (eLpNorm g (ENNReal.ofReal p)).toReal +
        (eLpNorm h (ENNReal.ofReal p)).toReal := by
  have hgh : MemLp (fun z => g z + h z) (ENNReal.ofReal p) :=
    wr_memLp (hg.1.add hh.1) (hg.2.add hh.2) p
  have e1 := wr_norm_add_le hp (wr_memLp hf.1 hf.2 p) hgh
  have e2 := wr_norm_add_le hp (wr_memLp hg.1 hg.2 p) (wr_memLp hh.1 hh.2 p)
  linarith

/-- **Level 0**: `‖s n‖_p ≤ L ρ^n`. -/
theorem wr_lv0 {p : ℝ} (hp : 1 < p) {ν : ℂ → ℂ} (hν : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ν)
    (hνc : HasCompactSupport ν) {k : ℝ} (hk : 0 ≤ k) (hνk : ∀ z, ‖ν z‖ ≤ k) {ρ L : ℝ}
    (hρ : k * hilbertNorm p < ρ) (hL : 0 ≤ L) (hνL : (eLpNorm ν (ENNReal.ofReal p)).toReal ≤ L)
    {s : ℕ → ℂ → ℂ} (hs0 : s 0 = ν) (hs : ∀ n, s (n + 1) = fun z => ν z * hilbertHSmooth (s n) z) (n : ℕ) :
    (eLpNorm (s n) (ENNReal.ofReal p)).toReal ≤ L * ρ ^ n := by
  have hsc := wr_iter_smooth hν hνc hs0 hs
  have hrec : ∀ n, s (n + 1) = fun z => ν z * hilbertHSmooth (s n) z + (fun _ : ℂ => (0 : ℂ)) z := by
    intro n
    refine (hs n).trans ?_
    funext z
    simp only [add_zero]
  have h := wr_level hp hk hν.continuous.aestronglyMeasurable hνk (fun n => (hsc n).1) (fun n => (hsc n).2)
    (fun _ => (by simp [MemLp] : MemLp (fun _ : ℂ => (0 : ℂ)) (ENNReal.ofReal p))) hrec hρ le_rfl
    (fun n => by simp) n
  have h0 : (eLpNorm (s 0) (ENNReal.ofReal p)).toReal ≤ L := by rw [hs0]; exact hνL
  have hρ0 : 0 ≤ ρ := (mul_nonneg hk (hilbertNorm_nonneg p)).trans hρ.le
  refine h.trans (mul_le_mul_of_nonneg_right ?_ (pow_nonneg hρ0 n))
  exact max_le h0 (by simp [hL])


/-- Constant bookkeeping for the levels. -/
theorem wr_hAG {B Λ E d m Γ : ℝ} (hB : 0 ≤ B) (hΛ : 0 ≤ Λ) (hE : 0 ≤ E) (hd : 0 < d) (hm : m ≤ 7)
    (hΓ : 7 * B * Λ / d ≤ Γ) : m * (B * Λ * E) / d ≤ Γ * E := by
  have hX : 0 ≤ B * Λ * E := mul_nonneg (mul_nonneg hB hΛ) hE
  have h1 : m * (B * Λ * E) / d ≤ 7 * B * Λ / d * E := by
    rw [div_mul_eq_mul_div]
    apply div_le_div_of_nonneg_right _ hd.le
    nlinarith
  exact h1.trans (mul_le_mul_of_nonneg_right hΓ hE)

/-- Recursion for `∂_v s`. -/
theorem wr_rec1 {ν : ℂ → ℂ} (hν : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ν) (hνc : HasCompactSupport ν)
    {s : ℕ → ℂ → ℂ} (hs0 : s 0 = ν) (hs : ∀ n, s (n + 1) = fun z => ν z * hilbertHSmooth (s n) z)
    (v : ℂ) (n : ℕ) :
    (fun z => fderiv ℝ (s (n + 1)) z v) = fun z => ν z * hilbertHSmooth (fun z => fderiv ℝ (s n) z v) z +
      (fun z => fderiv ℝ ν z v * hilbertHSmooth (s n) z) z := by
  have hsc := wr_iter_smooth hν hνc hs0 hs n
  have e1 := congrArg (fun f : ℂ → ℂ => fun z => fderiv ℝ f z v) (hs n)
  refine e1.trans ((wr_D_mul_hS hν hsc.1 hsc.2 v).trans ?_)
  funext z
  beta_reduce
  ring

/-- Recursion for `∂_u ∂_v s`. -/
theorem wr_rec2 {ν : ℂ → ℂ} (hν : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ν) (hνc : HasCompactSupport ν)
    {s : ℕ → ℂ → ℂ} (hs0 : s 0 = ν) (hs : ∀ n, s (n + 1) = fun z => ν z * hilbertHSmooth (s n) z)
    (u v : ℂ) (n : ℕ) :
    (fun z => fderiv ℝ (fun z => fderiv ℝ (s (n + 1)) z v) z u) = fun z =>
      ν z * hilbertHSmooth (fun z => fderiv ℝ (fun z => fderiv ℝ (s n) z v) z u) z +
      (fun z => fderiv ℝ ν z u * hilbertHSmooth (fun z => fderiv ℝ (s n) z v) z +
        (fderiv ℝ (fun z => fderiv ℝ ν z v) z u * hilbertHSmooth (s n) z +
          fderiv ℝ ν z v * hilbertHSmooth (fun z => fderiv ℝ (s n) z u) z)) z := by
  have hsc := wr_iter_smooth hν hνc hs0 hs n
  have hd := wr_D_sc hsc v
  have hνv := wr_D_sc ⟨hν, hνc⟩ v
  have e1 := congrArg (fun f : ℂ → ℂ => fun z => fderiv ℝ f z u) (wr_rec1 hν hνc hs0 hs v n)
  have hadd := wr_D_add (f := fun z => ν z * hilbertHSmooth (fun z => fderiv ℝ (s n) z v) z)
    (g := fun z => fderiv ℝ ν z v * hilbertHSmooth (s n) z)
    (wr_mul_hS_smooth hν hνc hd.1 hd.2).1 (wr_mul_hS_smooth hνv.1 hνv.2 hsc.1 hsc.2).1 u
  have m1 := wr_D_mul_hS hν hd.1 hd.2 u
  have m2 := wr_D_mul_hS hνv.1 hsc.1 hsc.2 u
  refine e1.trans (hadd.trans ?_)
  funext z
  have m1z := congrFun m1 z
  have m2z := congrFun m2 z
  beta_reduce at m1z m2z ⊢
  rw [m1z, m2z]
  ring

/-- **Level 1**: `‖∂_v s n‖_p ≤ L (1 + Γ) ρ^n`. -/
theorem wr_lv1 {p : ℝ} (hp : 1 < p) {ν : ℂ → ℂ} (hν : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ν)
    (hνc : HasCompactSupport ν) {k : ℝ} (hk : 0 ≤ k) (hνk : ∀ z, ‖ν z‖ ≤ k) {ρ L B Γ : ℝ}
    (hρ : k * hilbertNorm p < ρ) (hL : 0 ≤ L) (hB : 0 ≤ B)
    (hΓ : 7 * B * hilbertNorm p / (ρ - k * hilbertNorm p) ≤ Γ)
    (hνL : (eLpNorm ν (ENNReal.ofReal p)).toReal ≤ L)
    {s : ℕ → ℂ → ℂ} (hs0 : s 0 = ν) (hs : ∀ n, s (n + 1) = fun z => ν z * hilbertHSmooth (s n) z)
    {v : ℂ} (hDB : ∀ z, ‖fderiv ℝ ν z v‖ ≤ B)
    (hDL : (eLpNorm (fun z => fderiv ℝ ν z v) (ENNReal.ofReal p)).toReal ≤ L) (n : ℕ) :
    (eLpNorm (fun z => fderiv ℝ (s n) z v) (ENNReal.ofReal p)).toReal ≤ L * (1 + Γ) * ρ ^ n := by
  have hsc := wr_iter_smooth hν hνc hs0 hs
  have h0 := wr_lv0 hp hν hνc hk hνk hρ hL hνL hs0 hs
  have hνv := wr_D_sc ⟨hν, hνc⟩ v
  have hΛ := hilbertNorm_nonneg p
  have hr0 : 0 ≤ k * hilbertNorm p := mul_nonneg hk hΛ
  have hd : 0 < ρ - k * hilbertNorm p := sub_pos.2 hρ
  have hFb : ∀ n, (eLpNorm (fun z => fderiv ℝ ν z v * hilbertHSmooth (s n) z) (ENNReal.ofReal p)).toReal ≤
      1 * (B * hilbertNorm p * L) * ρ ^ n := fun n =>
    (wr_term_bound hp hB hνv.1 hDB (fun n => (hsc n).1) (fun n => (hsc n).2) h0 n).trans (le_of_eq (by ring))
  have h := wr_level (x := fun n => fun z => fderiv ℝ (s n) z v)
    (F := fun n => fun z => fderiv ℝ ν z v * hilbertHSmooth (s n) z) hp hk hν.continuous.aestronglyMeasurable
    hνk (fun n => (wr_D_sc (hsc n) v).1) (fun n => (wr_D_sc (hsc n) v).2)
    (fun n => wr_memLp (wr_mul_hS_smooth hνv.1 hνv.2 (hsc n).1 (hsc n).2).1
      (wr_mul_hS_smooth hνv.1 hνv.2 (hsc n).1 (hsc n).2).2 p)
    (wr_rec1 hν hνc hs0 hs v) hρ (by positivity) hFb n
  have ha : (eLpNorm (fun z => fderiv ℝ (s 0) z v) (ENNReal.ofReal p)).toReal ≤ L := by rw [hs0]; exact hDL
  exact wr_level_finish hL hρ ha (hr0.trans hρ.le) (wr_hAG hB hΛ hL hd (by norm_num) hΓ) le_rfl
    ((div_nonneg (by positivity) hd.le).trans hΓ) n h


/-- **Level 2**: `‖∂_u ∂_v s n‖_p ≤ L (1 + Γ)² ρ^n`. -/
theorem wr_lv2 {p : ℝ} (hp : 1 < p) {ν : ℂ → ℂ} (hν : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ν)
    (hνc : HasCompactSupport ν) {k : ℝ} (hk : 0 ≤ k) (hνk : ∀ z, ‖ν z‖ ≤ k) {ρ L B Γ : ℝ}
    (hρ : k * hilbertNorm p < ρ) (hL : 0 ≤ L) (hB : 0 ≤ B)
    (hΓ : 7 * B * hilbertNorm p / (ρ - k * hilbertNorm p) ≤ Γ)
    (hνL : (eLpNorm ν (ENNReal.ofReal p)).toReal ≤ L)
    {s : ℕ → ℂ → ℂ} (hs0 : s 0 = ν) (hs : ∀ n, s (n + 1) = fun z => ν z * hilbertHSmooth (s n) z)
    {u v : ℂ} (hDBu : ∀ z, ‖fderiv ℝ ν z u‖ ≤ B) (hDBv : ∀ z, ‖fderiv ℝ ν z v‖ ≤ B)
    (hDBuv : ∀ z, ‖fderiv ℝ (fun z => fderiv ℝ ν z v) z u‖ ≤ B)
    (hDLu : (eLpNorm (fun z => fderiv ℝ ν z u) (ENNReal.ofReal p)).toReal ≤ L)
    (hDLv : (eLpNorm (fun z => fderiv ℝ ν z v) (ENNReal.ofReal p)).toReal ≤ L)
    (hDLuv : (eLpNorm (fun z => fderiv ℝ (fun z => fderiv ℝ ν z v) z u) (ENNReal.ofReal p)).toReal ≤ L)
    (n : ℕ) :
    (eLpNorm (fun z => fderiv ℝ (fun z => fderiv ℝ (s n) z v) z u) (ENNReal.ofReal p)).toReal ≤
      L * (1 + Γ) * (1 + Γ) * ρ ^ n := by
  have hsc := wr_iter_smooth hν hνc hs0 hs
  have hΛ := hilbertNorm_nonneg p
  have hr0 : 0 ≤ k * hilbertNorm p := mul_nonneg hk hΛ
  have hd : 0 < ρ - k * hilbertNorm p := sub_pos.2 hρ
  have hG : 0 ≤ Γ := (div_nonneg (by positivity) hd.le).trans hΓ
  have hE1 : L ≤ L * (1 + Γ) := by nlinarith
  have hρ0 : 0 ≤ ρ := hr0.trans hρ.le
  have h0 := wr_lv0 hp hν hνc hk hνk hρ hL hνL hs0 hs
  have h1u := wr_lv1 hp hν hνc hk hνk hρ hL hB hΓ hνL hs0 hs hDBu hDLu
  have h1v := wr_lv1 hp hν hνc hk hνk hρ hL hB hΓ hνL hs0 hs hDBv hDLv
  have hνu := wr_D_sc ⟨hν, hνc⟩ u
  have hνv := wr_D_sc ⟨hν, hνc⟩ v
  have hνuv := wr_D_sc hνv u
  have hdv : ∀ n, _ := fun n => wr_D_sc (hsc n) v
  have hdu : ∀ n, _ := fun n => wr_D_sc (hsc n) u
  have t1 := wr_term_bound hp hB hνu.1 hDBu (fun n => (hdv n).1) (fun n => (hdv n).2) h1v
  have t2 := wr_term_bound hp hB hνuv.1 hDBuv (fun n => (hsc n).1) (fun n => (hsc n).2) h0
  have t3 := wr_term_bound hp hB hνv.1 hDBv (fun n => (hdu n).1) (fun n => (hdu n).2) h1u
  have hFb : ∀ n, (eLpNorm (fun z => fderiv ℝ ν z u * hilbertHSmooth (fun z => fderiv ℝ (s n) z v) z +
      (fderiv ℝ (fun z => fderiv ℝ ν z v) z u * hilbertHSmooth (s n) z +
        fderiv ℝ ν z v * hilbertHSmooth (fun z => fderiv ℝ (s n) z u) z)) (ENNReal.ofReal p)).toReal ≤
      3 * (B * hilbertNorm p * (L * (1 + Γ))) * ρ ^ n := by
    intro n
    have e := wr_norm_add3_le hp.le (wr_mul_hS_smooth hνu.1 hνu.2 (hdv n).1 (hdv n).2)
      (wr_mul_hS_smooth hνuv.1 hνuv.2 (hsc n).1 (hsc n).2) (wr_mul_hS_smooth hνv.1 hνv.2 (hdu n).1 (hdu n).2)
    have a1 := t1 n
    have a2 := t2 n
    have a3 := t3 n
    have hBΛ : 0 ≤ B * hilbertNorm p := mul_nonneg hB hΛ
    have hp0 : 0 ≤ ρ ^ n := pow_nonneg hρ0 n
    have : B * hilbertNorm p * L * ρ ^ n ≤ B * hilbertNorm p * (L * (1 + Γ)) * ρ ^ n := by
      apply mul_le_mul_of_nonneg_right _ hp0
      exact mul_le_mul_of_nonneg_left hE1 hBΛ
    nlinarith
  have hmem : ∀ n, MemLp (fun z => fderiv ℝ ν z u * hilbertHSmooth (fun z => fderiv ℝ (s n) z v) z +
      (fderiv ℝ (fun z => fderiv ℝ ν z v) z u * hilbertHSmooth (s n) z +
        fderiv ℝ ν z v * hilbertHSmooth (fun z => fderiv ℝ (s n) z u) z)) (ENNReal.ofReal p) := by
    intro n
    have a := wr_mul_hS_smooth hνu.1 hνu.2 (hdv n).1 (hdv n).2
    have b := wr_mul_hS_smooth hνuv.1 hνuv.2 (hsc n).1 (hsc n).2
    have c := wr_mul_hS_smooth hνv.1 hνv.2 (hdu n).1 (hdu n).2
    exact wr_memLp (a.1.add (b.1.add c.1)) (a.2.add (b.2.add c.2)) p
  have h := wr_level (x := fun n => fun z => fderiv ℝ (fun z => fderiv ℝ (s n) z v) z u)
    (F := fun n => fun z => fderiv ℝ ν z u * hilbertHSmooth (fun z => fderiv ℝ (s n) z v) z +
      (fderiv ℝ (fun z => fderiv ℝ ν z v) z u * hilbertHSmooth (s n) z +
        fderiv ℝ ν z v * hilbertHSmooth (fun z => fderiv ℝ (s n) z u) z))
    hp hk hν.continuous.aestronglyMeasurable hνk (fun n => (wr_D_sc (hdv n) u).1)
    (fun n => (wr_D_sc (hdv n) u).2) hmem (wr_rec2 hν hνc hs0 hs u v) hρ (by positivity) hFb n
  have ha : (eLpNorm (fun z => fderiv ℝ (fun z => fderiv ℝ (s 0) z v) z u) (ENNReal.ofReal p)).toReal ≤ L := by
    rw [hs0]; exact hDLuv
  exact wr_level_finish hL hρ ha hρ0 (wr_hAG hB hΛ (hL.trans hE1) hd (by norm_num) hΓ) hE1 hG n h


/-- Recursion for `∂_t ∂_u ∂_v s`. -/
theorem wr_rec3 {ν : ℂ → ℂ} (hν : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ν) (hνc : HasCompactSupport ν)
    {s : ℕ → ℂ → ℂ} (hs0 : s 0 = ν) (hs : ∀ n, s (n + 1) = fun z => ν z * hilbertHSmooth (s n) z)
    (t u v : ℂ) (n : ℕ) :
    (fun z => fderiv ℝ (fun z => fderiv ℝ (fun z => fderiv ℝ (s (n + 1)) z v) z u) z t) = fun z =>
      ν z * hilbertHSmooth (fun z => fderiv ℝ (fun z => fderiv ℝ (fun z => fderiv ℝ (s n) z v) z u) z t) z +
      (fun z => fderiv ℝ ν z t * hilbertHSmooth (fun z => fderiv ℝ (fun z => fderiv ℝ (s n) z v) z u) z +
        ((fderiv ℝ (fun z => fderiv ℝ ν z u) z t * hilbertHSmooth (fun z => fderiv ℝ (s n) z v) z +
            fderiv ℝ ν z u * hilbertHSmooth (fun z => fderiv ℝ (fun z => fderiv ℝ (s n) z v) z t) z) +
          ((fderiv ℝ (fun z => fderiv ℝ (fun z => fderiv ℝ ν z v) z u) z t * hilbertHSmooth (s n) z +
              fderiv ℝ (fun z => fderiv ℝ ν z v) z u * hilbertHSmooth (fun z => fderiv ℝ (s n) z t) z) +
            (fderiv ℝ (fun z => fderiv ℝ ν z v) z t * hilbertHSmooth (fun z => fderiv ℝ (s n) z u) z +
              fderiv ℝ ν z v * hilbertHSmooth (fun z => fderiv ℝ (fun z => fderiv ℝ (s n) z u) z t) z)))) z := by
  have hsc := wr_iter_smooth hν hνc hs0 hs n
  have hdv := wr_D_sc hsc v
  have hdu := wr_D_sc hsc u
  have he := wr_D_sc hdv u
  have hνu := wr_D_sc ⟨hν, hνc⟩ u
  have hνv := wr_D_sc ⟨hν, hνc⟩ v
  have hνuv := wr_D_sc hνv u
  have T1 := wr_mul_hS_smooth hνu.1 hνu.2 hdv.1 hdv.2
  have T2 := wr_mul_hS_smooth hνuv.1 hνuv.2 hsc.1 hsc.2
  have T3 := wr_mul_hS_smooth hνv.1 hνv.2 hdu.1 hdu.2
  have e1 := congrArg (fun f : ℂ → ℂ => fun z => fderiv ℝ f z t) (wr_rec2 hν hνc hs0 hs u v n)
  have hadd := wr_D_add (f := fun z => ν z * hilbertHSmooth (fun z => fderiv ℝ (fun z => fderiv ℝ (s n) z v) z u) z)
    (g := fun z => fderiv ℝ ν z u * hilbertHSmooth (fun z => fderiv ℝ (s n) z v) z +
        (fderiv ℝ (fun z => fderiv ℝ ν z v) z u * hilbertHSmooth (s n) z +
          fderiv ℝ ν z v * hilbertHSmooth (fun z => fderiv ℝ (s n) z u) z))
    (wr_mul_hS_smooth hν hνc he.1 he.2).1 (T1.1.add (T2.1.add T3.1)) t
  have hadd2 := wr_D_add (f := fun z => fderiv ℝ ν z u * hilbertHSmooth (fun z => fderiv ℝ (s n) z v) z)
    (g := fun z => fderiv ℝ (fun z => fderiv ℝ ν z v) z u * hilbertHSmooth (s n) z +
          fderiv ℝ ν z v * hilbertHSmooth (fun z => fderiv ℝ (s n) z u) z) T1.1 (T2.1.add T3.1) t
  have hadd3 := wr_D_add (f := fun z => fderiv ℝ (fun z => fderiv ℝ ν z v) z u * hilbertHSmooth (s n) z)
    (g := fun z => fderiv ℝ ν z v * hilbertHSmooth (fun z => fderiv ℝ (s n) z u) z) T2.1 T3.1 t
  have m1 := wr_D_mul_hS hν he.1 he.2 t
  have m2 := wr_D_mul_hS hνu.1 hdv.1 hdv.2 t
  have m3 := wr_D_mul_hS hνuv.1 hsc.1 hsc.2 t
  have m4 := wr_D_mul_hS hνv.1 hdu.1 hdu.2 t
  refine e1.trans (hadd.trans ?_)
  funext z
  have a2 := congrFun hadd2 z
  have a3 := congrFun hadd3 z
  have b1 := congrFun m1 z
  have b2 := congrFun m2 z
  have b3 := congrFun m3 z
  have b4 := congrFun m4 z
  beta_reduce at a2 a3 b1 b2 b3 b4 ⊢
  rw [a2, a3, b1, b2, b3, b4]
  ring


/-- Triangle inequality for `C_c^∞` summands. -/
theorem wr_norm_add_sc {p : ℝ} (hp : 1 ≤ p) {f g : ℂ → ℂ}
    (hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f ∧ HasCompactSupport f)
    (hg : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g ∧ HasCompactSupport g) :
    (eLpNorm (fun z => f z + g z) (ENNReal.ofReal p)).toReal ≤
      (eLpNorm f (ENNReal.ofReal p)).toReal + (eLpNorm g (ENNReal.ofReal p)).toReal :=
  wr_norm_add_le hp (wr_memLp hf.1 hf.2 p) (wr_memLp hg.1 hg.2 p)

/-- Sum of `C_c^∞` functions. -/
theorem wr_sc_add {f g : ℂ → ℂ} (hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f ∧ HasCompactSupport f)
    (hg : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g ∧ HasCompactSupport g) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z => f z + g z) ∧ HasCompactSupport (fun z => f z + g z) :=
  ⟨hf.1.add hg.1, hf.2.add hg.2⟩

/-- **Level 3**: `‖∂_t ∂_u ∂_v s n‖_p ≤ L (1 + Γ)³ ρ^n`. -/
theorem wr_lv3 {p : ℝ} (hp : 1 < p) {ν : ℂ → ℂ} (hν : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ν)
    (hνc : HasCompactSupport ν) {k : ℝ} (hk : 0 ≤ k) (hνk : ∀ z, ‖ν z‖ ≤ k) {ρ L B Γ : ℝ}
    (hρ : k * hilbertNorm p < ρ) (hL : 0 ≤ L) (hB : 0 ≤ B)
    (hΓ : 7 * B * hilbertNorm p / (ρ - k * hilbertNorm p) ≤ Γ)
    (hνL : (eLpNorm ν (ENNReal.ofReal p)).toReal ≤ L)
    {s : ℕ → ℂ → ℂ} (hs0 : s 0 = ν) (hs : ∀ n, s (n + 1) = fun z => ν z * hilbertHSmooth (s n) z)
    {t u v : ℂ} (hBt : ∀ z, ‖fderiv ℝ ν z t‖ ≤ B) (hBu : ∀ z, ‖fderiv ℝ ν z u‖ ≤ B)
    (hBv : ∀ z, ‖fderiv ℝ ν z v‖ ≤ B)
    (hBtu : ∀ z, ‖fderiv ℝ (fun z => fderiv ℝ ν z u) z t‖ ≤ B)
    (hBtv : ∀ z, ‖fderiv ℝ (fun z => fderiv ℝ ν z v) z t‖ ≤ B)
    (hBuv : ∀ z, ‖fderiv ℝ (fun z => fderiv ℝ ν z v) z u‖ ≤ B)
    (hBtuv : ∀ z, ‖fderiv ℝ (fun z => fderiv ℝ (fun z => fderiv ℝ ν z v) z u) z t‖ ≤ B)
    (hLt : (eLpNorm (fun z => fderiv ℝ ν z t) (ENNReal.ofReal p)).toReal ≤ L)
    (hLu : (eLpNorm (fun z => fderiv ℝ ν z u) (ENNReal.ofReal p)).toReal ≤ L)
    (hLv : (eLpNorm (fun z => fderiv ℝ ν z v) (ENNReal.ofReal p)).toReal ≤ L)
    (hLtu : (eLpNorm (fun z => fderiv ℝ (fun z => fderiv ℝ ν z u) z t) (ENNReal.ofReal p)).toReal ≤ L)
    (hLtv : (eLpNorm (fun z => fderiv ℝ (fun z => fderiv ℝ ν z v) z t) (ENNReal.ofReal p)).toReal ≤ L)
    (hLuv : (eLpNorm (fun z => fderiv ℝ (fun z => fderiv ℝ ν z v) z u) (ENNReal.ofReal p)).toReal ≤ L)
    (hLtuv : (eLpNorm (fun z => fderiv ℝ (fun z => fderiv ℝ (fun z => fderiv ℝ ν z v) z u) z t)
      (ENNReal.ofReal p)).toReal ≤ L) (n : ℕ) :
    (eLpNorm (fun z => fderiv ℝ (fun z => fderiv ℝ (fun z => fderiv ℝ (s n) z v) z u) z t)
      (ENNReal.ofReal p)).toReal ≤ L * (1 + Γ) * (1 + Γ) * (1 + Γ) * ρ ^ n := by
  have hsc := wr_iter_smooth hν hνc hs0 hs
  have hΛ := hilbertNorm_nonneg p
  have hr0 : 0 ≤ k * hilbertNorm p := mul_nonneg hk hΛ
  have hd : 0 < ρ - k * hilbertNorm p := sub_pos.2 hρ
  have hG : 0 ≤ Γ := (div_nonneg (by positivity) hd.le).trans hΓ
  have hρ0 : 0 ≤ ρ := hr0.trans hρ.le
  have hE1 : L ≤ L * (1 + Γ) := by nlinarith
  have hE2 : L * (1 + Γ) ≤ L * (1 + Γ) * (1 + Γ) := by nlinarith
  have h0 := wr_lv0 hp hν hνc hk hνk hρ hL hνL hs0 hs
  have h1t := wr_lv1 hp hν hνc hk hνk hρ hL hB hΓ hνL hs0 hs hBt hLt
  have h1u := wr_lv1 hp hν hνc hk hνk hρ hL hB hΓ hνL hs0 hs hBu hLu
  have h1v := wr_lv1 hp hν hνc hk hνk hρ hL hB hΓ hνL hs0 hs hBv hLv
  have h2uv := wr_lv2 hp hν hνc hk hνk hρ hL hB hΓ hνL hs0 hs hBu hBv hBuv hLu hLv hLuv
  have h2tv := wr_lv2 hp hν hνc hk hνk hρ hL hB hΓ hνL hs0 hs hBt hBv hBtv hLt hLv hLtv
  have h2tu := wr_lv2 hp hν hνc hk hνk hρ hL hB hΓ hνL hs0 hs hBt hBu hBtu hLt hLu hLtu
  have hνt := wr_D_sc ⟨hν, hνc⟩ t
  have hνu := wr_D_sc ⟨hν, hνc⟩ u
  have hνv := wr_D_sc ⟨hν, hνc⟩ v
  have hνtu := wr_D_sc hνu t
  have hνtv := wr_D_sc hνv t
  have hνuv := wr_D_sc hνv u
  have hνtuv := wr_D_sc hνuv t
  have hdt : ∀ n, _ := fun n => wr_D_sc (hsc n) t
  have hdu : ∀ n, _ := fun n => wr_D_sc (hsc n) u
  have hdv : ∀ n, _ := fun n => wr_D_sc (hsc n) v
  have he : ∀ n, _ := fun n => wr_D_sc (hdv n) u
  have hetv : ∀ n, _ := fun n => wr_D_sc (hdv n) t
  have hetu : ∀ n, _ := fun n => wr_D_sc (hdu n) t
  have ta := wr_term_bound hp hB hνt.1 hBt (fun n => (he n).1) (fun n => (he n).2) h2uv
  have tb := wr_term_bound hp hB hνtu.1 hBtu (fun n => (hdv n).1) (fun n => (hdv n).2) h1v
  have tc := wr_term_bound hp hB hνu.1 hBu (fun n => (hetv n).1) (fun n => (hetv n).2) h2tv
  have td := wr_term_bound hp hB hνtuv.1 hBtuv (fun n => (hsc n).1) (fun n => (hsc n).2) h0
  have te := wr_term_bound hp hB hνuv.1 hBuv (fun n => (hdt n).1) (fun n => (hdt n).2) h1t
  have tf := wr_term_bound hp hB hνtv.1 hBtv (fun n => (hdu n).1) (fun n => (hdu n).2) h1u
  have tg := wr_term_bound hp hB hνv.1 hBv (fun n => (hetu n).1) (fun n => (hetu n).2) h2tu
  have Sa : ∀ n, _ := fun n => wr_mul_hS_smooth hνt.1 hνt.2 (he n).1 (he n).2
  have Sb : ∀ n, _ := fun n => wr_mul_hS_smooth hνtu.1 hνtu.2 (hdv n).1 (hdv n).2
  have Sc : ∀ n, _ := fun n => wr_mul_hS_smooth hνu.1 hνu.2 (hetv n).1 (hetv n).2
  have Sd : ∀ n, _ := fun n => wr_mul_hS_smooth hνtuv.1 hνtuv.2 (hsc n).1 (hsc n).2
  have Se : ∀ n, _ := fun n => wr_mul_hS_smooth hνuv.1 hνuv.2 (hdt n).1 (hdt n).2
  have Sf : ∀ n, _ := fun n => wr_mul_hS_smooth hνtv.1 hνtv.2 (hdu n).1 (hdu n).2
  have Sg : ∀ n, _ := fun n => wr_mul_hS_smooth hνv.1 hνv.2 (hetu n).1 (hetu n).2
  have Sall : ∀ n, _ := fun n =>
    wr_sc_add (Sa n) (wr_sc_add (wr_sc_add (Sb n) (Sc n)) (wr_sc_add (wr_sc_add (Sd n) (Se n))
      (wr_sc_add (Sf n) (Sg n))))
  have hFb : ∀ n, (eLpNorm (fun z => fderiv ℝ ν z t *
        hilbertHSmooth (fun z => fderiv ℝ (fun z => fderiv ℝ (s n) z v) z u) z +
      ((fderiv ℝ (fun z => fderiv ℝ ν z u) z t * hilbertHSmooth (fun z => fderiv ℝ (s n) z v) z +
          fderiv ℝ ν z u * hilbertHSmooth (fun z => fderiv ℝ (fun z => fderiv ℝ (s n) z v) z t) z) +
        ((fderiv ℝ (fun z => fderiv ℝ (fun z => fderiv ℝ ν z v) z u) z t * hilbertHSmooth (s n) z +
            fderiv ℝ (fun z => fderiv ℝ ν z v) z u * hilbertHSmooth (fun z => fderiv ℝ (s n) z t) z) +
          (fderiv ℝ (fun z => fderiv ℝ ν z v) z t * hilbertHSmooth (fun z => fderiv ℝ (s n) z u) z +
            fderiv ℝ ν z v * hilbertHSmooth (fun z => fderiv ℝ (fun z => fderiv ℝ (s n) z u) z t) z))))
        (ENNReal.ofReal p)).toReal ≤
      7 * (B * hilbertNorm p * (L * (1 + Γ) * (1 + Γ))) * ρ ^ n := by
    intro n
    have q1 := wr_norm_add_sc hp.le (Sa n)
      (wr_sc_add (wr_sc_add (Sb n) (Sc n)) (wr_sc_add (wr_sc_add (Sd n) (Se n)) (wr_sc_add (Sf n) (Sg n))))
    have q2 := wr_norm_add_sc hp.le (wr_sc_add (Sb n) (Sc n))
      (wr_sc_add (wr_sc_add (Sd n) (Se n)) (wr_sc_add (Sf n) (Sg n)))
    have q3 := wr_norm_add_sc hp.le (Sb n) (Sc n)
    have q4 := wr_norm_add_sc hp.le (wr_sc_add (Sd n) (Se n)) (wr_sc_add (Sf n) (Sg n))
    have q5 := wr_norm_add_sc hp.le (Sd n) (Se n)
    have q6 := wr_norm_add_sc hp.le (Sf n) (Sg n)
    have a1 := ta n
    have a2 := tb n
    have a3 := tc n
    have a4 := td n
    have a5 := te n
    have a6 := tf n
    have a7 := tg n
    have hBΛ : 0 ≤ B * hilbertNorm p := mul_nonneg hB hΛ
    have hp0 : 0 ≤ ρ ^ n := pow_nonneg hρ0 n
    have x1 : B * hilbertNorm p * (L * (1 + Γ)) * ρ ^ n ≤
        B * hilbertNorm p * (L * (1 + Γ) * (1 + Γ)) * ρ ^ n :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hE2 hBΛ) hp0
    have x0 : B * hilbertNorm p * L * ρ ^ n ≤ B * hilbertNorm p * (L * (1 + Γ) * (1 + Γ)) * ρ ^ n :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hE1.trans hE2) hBΛ) hp0
    linarith
  have h := wr_level (x := fun n => fun z => fderiv ℝ (fun z => fderiv ℝ (fun z => fderiv ℝ (s n) z v) z u) z t)
    (F := fun n => fun z => fderiv ℝ ν z t *
        hilbertHSmooth (fun z => fderiv ℝ (fun z => fderiv ℝ (s n) z v) z u) z +
      ((fderiv ℝ (fun z => fderiv ℝ ν z u) z t * hilbertHSmooth (fun z => fderiv ℝ (s n) z v) z +
          fderiv ℝ ν z u * hilbertHSmooth (fun z => fderiv ℝ (fun z => fderiv ℝ (s n) z v) z t) z) +
        ((fderiv ℝ (fun z => fderiv ℝ (fun z => fderiv ℝ ν z v) z u) z t * hilbertHSmooth (s n) z +
            fderiv ℝ (fun z => fderiv ℝ ν z v) z u * hilbertHSmooth (fun z => fderiv ℝ (s n) z t) z) +
          (fderiv ℝ (fun z => fderiv ℝ ν z v) z t * hilbertHSmooth (fun z => fderiv ℝ (s n) z u) z +
            fderiv ℝ ν z v * hilbertHSmooth (fun z => fderiv ℝ (fun z => fderiv ℝ (s n) z u) z t) z))))
    hp hk hν.continuous.aestronglyMeasurable hνk (fun n => (wr_D_sc (he n) t).1)
    (fun n => (wr_D_sc (he n) t).2) (fun n => wr_memLp (Sall n).1 (Sall n).2 p)
    (wr_rec3 hν hνc hs0 hs t u v) hρ (by positivity) hFb n
  have ha : (eLpNorm (fun z => fderiv ℝ (fun z => fderiv ℝ (fun z => fderiv ℝ (s 0) z v) z u) z t)
      (ENNReal.ofReal p)).toReal ≤ L := by
    rw [hs0]; exact hLtuv
  exact wr_level_finish hL hρ ha hρ0 (wr_hAG hB hΛ (hL.trans (hE1.trans hE2)) hd le_rfl hΓ)
    (hE1.trans hE2) hG n h

/-- Unit-direction bounds on the derivatives of order `≤ 3` of a smooth function bound its iterated derivatives. -/
theorem wr_iter_bound {f : ℂ → ℂ} (hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f) {M : ℝ}
    (h0 : ∀ z, ‖f z‖ ≤ M) (h1 : ∀ z a, ‖a‖ ≤ 1 → ‖fderiv ℝ f z a‖ ≤ M)
    (h2 : ∀ z a b, ‖a‖ ≤ 1 → ‖b‖ ≤ 1 → ‖fderiv ℝ (fun y => fderiv ℝ f y b) z a‖ ≤ M)
    (h3 : ∀ z a b c, ‖a‖ ≤ 1 → ‖b‖ ≤ 1 → ‖c‖ ≤ 1 →
      ‖fderiv ℝ (fun y => fderiv ℝ (fun w => fderiv ℝ f w c) y b) z a‖ ≤ M) :
    ∀ k ≤ 3, ∀ z, ‖iteratedFDeriv ℝ k f z‖ ≤ M := by
  have hM : 0 ≤ M := (norm_nonneg _).trans (h0 0)
  let i1 : NormedAddCommGroup (ℂ →L[ℝ] ℂ) := inferInstance
  let i2 : NormedSpace ℝ (ℂ →L[ℝ] ℂ) := inferInstance
  let i3 : NormedAddCommGroup (ℂ →L[ℝ] ℂ →L[ℝ] ℂ) := inferInstance
  let i4 : NormedSpace ℝ (ℂ →L[ℝ] ℂ →L[ℝ] ℂ) := inferInstance
  let i5 : NormedAddCommGroup (ℂ →L[ℝ] ℂ →L[ℝ] ℂ →L[ℝ] ℂ) := inferInstance
  have hd1 := contDiff_infty_iff_fderiv.mp hf
  have hd2 := contDiff_infty_iff_fderiv.mp hd1.2
  have hd3 := contDiff_infty_iff_fderiv.mp hd2.2
  have e2 : ∀ z a b, fderiv ℝ (fun y => fderiv ℝ f y b) z a = fderiv ℝ (fderiv ℝ f) z a b := by
    intro z a b
    rw [(wr_hasFDerivAt_fderiv_apply (hd2.1 z) b).fderiv]
    rfl
  have e3 : ∀ z a b c, fderiv ℝ (fun y => fderiv ℝ (fun w => fderiv ℝ f w c) y b) z a =
      fderiv ℝ (fderiv ℝ (fderiv ℝ f)) z a b c := by
    intro z a b c
    have hfun : (fun y => fderiv ℝ (fun w => fderiv ℝ f w c) y b) = fun y => fderiv ℝ (fderiv ℝ f) y b c := by
      funext y
      exact e2 y b c
    rw [hfun]
    let L : (ℂ →L[ℝ] ℂ →L[ℝ] ℂ) →L[ℝ] ℂ :=
      (ContinuousLinearMap.apply ℝ ℂ c).comp (ContinuousLinearMap.apply ℝ (ℂ →L[ℝ] ℂ) b)
    have hL0 := L.hasFDerivAt.comp z (hd3.1 z).hasFDerivAt
    have hL : HasFDerivAt (fun y => fderiv ℝ (fderiv ℝ f) y b c)
        (L.comp (fderiv ℝ (fderiv ℝ (fderiv ℝ f)) z)) z := hL0
    rw [hL.fderiv]
    rfl
  have n1 : ∀ z, ‖fderiv ℝ f z‖ ≤ M := fun z =>
    ContinuousLinearMap.opNorm_le_of_unit_norm hM fun a ha => h1 z a ha.le
  have n2 : ∀ z, ‖fderiv ℝ (fderiv ℝ f) z‖ ≤ M := fun z =>
    ContinuousLinearMap.opNorm_le_of_unit_norm hM fun a ha =>
      ContinuousLinearMap.opNorm_le_of_unit_norm hM fun b hb => by
        rw [← e2]
        exact h2 z a b ha.le hb.le
  have n3 : ∀ z, ‖fderiv ℝ (fderiv ℝ (fderiv ℝ f)) z‖ ≤ M := fun z =>
    ContinuousLinearMap.opNorm_le_of_unit_norm hM fun a ha =>
      ContinuousLinearMap.opNorm_le_of_unit_norm hM fun b hb =>
        ContinuousLinearMap.opNorm_le_of_unit_norm hM fun c hc => by
          rw [← e3]
          exact h3 z a b c ha.le hb.le hc.le
  intro k hk z
  interval_cases k
  · rw [norm_iteratedFDeriv_zero]
    exact h0 z
  · calc ‖iteratedFDeriv ℝ 1 f z‖ = ‖iteratedFDeriv ℝ 0 (fderiv ℝ f) z‖ := by
          rw [norm_iteratedFDeriv_fderiv]
      _ = ‖fderiv ℝ f z‖ := norm_iteratedFDeriv_zero
      _ ≤ M := n1 z
  · calc ‖iteratedFDeriv ℝ 2 f z‖ = ‖iteratedFDeriv ℝ 0 (fderiv ℝ (fderiv ℝ f)) z‖ := by
          rw [norm_iteratedFDeriv_fderiv, norm_iteratedFDeriv_fderiv]
      _ = ‖fderiv ℝ (fderiv ℝ f) z‖ := norm_iteratedFDeriv_zero
      _ ≤ M := n2 z
  · calc ‖iteratedFDeriv ℝ 3 f z‖ = ‖iteratedFDeriv ℝ 0 (fderiv ℝ (fderiv ℝ (fderiv ℝ f))) z‖ := by
          rw [norm_iteratedFDeriv_fderiv, norm_iteratedFDeriv_fderiv, norm_iteratedFDeriv_fderiv]
      _ = ‖fderiv ℝ (fderiv ℝ (fderiv ℝ f)) z‖ := norm_iteratedFDeriv_zero
      _ ≤ M := n3 z

/-- (A3-S1) `[W4]` **C³ of a series from directional bounds, with parameter continuity.** Each term `g x n` is
smooth. Unit-direction derivatives of order `≤ 3` are bounded by a summable `u n`, uniformly for `x ∈ S`. The
`z`-iterated derivatives of each term are jointly continuous. Then the sum is `C³` in `z`, and its `z`-iterated
derivatives are jointly continuous on `S ×ˢ univ`. -/
theorem wr_tsum_contDiff {X : Type*} [TopologicalSpace X] {S : Set X} {g : X → ℕ → ℂ → ℂ}
    (hg : ∀ x n, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (g x n)) {u : ℕ → ℝ} (hu : Summable u)
    (h0 : ∀ x ∈ S, ∀ n z, ‖g x n z‖ ≤ u n)
    (h1 : ∀ x ∈ S, ∀ n z a, ‖a‖ ≤ 1 → ‖fderiv ℝ (g x n) z a‖ ≤ u n)
    (h2 : ∀ x ∈ S, ∀ n z a b, ‖a‖ ≤ 1 → ‖b‖ ≤ 1 →
      ‖fderiv ℝ (fun y => fderiv ℝ (g x n) y b) z a‖ ≤ u n)
    (h3 : ∀ x ∈ S, ∀ n z a b c, ‖a‖ ≤ 1 → ‖b‖ ≤ 1 → ‖c‖ ≤ 1 →
      ‖fderiv ℝ (fun y => fderiv ℝ (fun w => fderiv ℝ (g x n) w c) y b) z a‖ ≤ u n)
    (hc : ∀ n, ∀ j ≤ 3, ContinuousOn (fun q : X × ℂ => iteratedFDeriv ℝ j (g q.1 n) q.2) (S ×ˢ univ)) :
    (∀ x ∈ S, ContDiff ℝ 3 (fun z => ∑' n, g x n z)) ∧
      ∀ j ≤ 3, ContinuousOn (fun q : X × ℂ => iteratedFDeriv ℝ j (fun z => ∑' n, g q.1 n z) q.2)
        (S ×ˢ univ) := by
  have hB : ∀ x ∈ S, ∀ n, ∀ k ≤ 3, ∀ z, ‖iteratedFDeriv ℝ k (g x n) z‖ ≤ u n := fun x hx n =>
    wr_iter_bound (hg x n) (h0 x hx n) (h1 x hx n) (h2 x hx n) (h3 x hx n)
  have hg3 : ∀ x n, ContDiff ℝ ((3 : ℕ∞) : WithTop ℕ∞) (g x n) := fun x n =>
    (hg x n).of_le (WithTop.coe_le_coe.mpr le_top)
  have hT : ∀ x ∈ S, ∀ k ≤ 3, iteratedFDeriv ℝ k (fun z => ∑' n, g x n z) =
      fun z => ∑' n, iteratedFDeriv ℝ k (g x n) z := fun x hx k hk =>
    iteratedFDeriv_tsum (N := 3) (v := fun _ n => u n) (hg3 x) (fun _ _ => hu)
      (fun k' n z hk' => hB x hx n k' (by exact_mod_cast hk') z) (by exact_mod_cast hk)
  refine ⟨fun x hx => ?_, fun j hj => ?_⟩
  · have h := contDiff_tsum (N := 3) (v := fun _ n => u n) (hg3 x) (fun _ _ => hu)
      (fun k n z hk => hB x hx n k (by exact_mod_cast hk) z)
    exact_mod_cast h
  · have he : EqOn (fun q : X × ℂ => iteratedFDeriv ℝ j (fun z => ∑' n, g q.1 n z) q.2)
        (fun q => ∑' n, iteratedFDeriv ℝ j (g q.1 n) q.2) (S ×ˢ univ) := by
      intro q hq
      show iteratedFDeriv ℝ j (fun z => ∑' n, g q.1 n z) q.2 = ∑' n, iteratedFDeriv ℝ j (g q.1 n) q.2
      rw [hT q.1 hq.1 j hj]
    refine ContinuousOn.congr ?_ he
    exact continuousOn_tsum (fun n => hc n j hj) hu (fun n q hq => hB q.1 hq.1 n j hj q.2)

/-- The Cauchy kernel against a `C_c^∞` function is integrable. -/
theorem wr_s2_kernel_int {c : ℂ → ℂ} (hc : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) c) (hcc : HasCompactSupport c)
    (z : ℂ) : Integrable (fun ζ => c ζ / (ζ - z)) volume := by
  obtain ⟨R, hR⟩ := hcc.isCompact.isBounded.subset_closedBall 0
  have hsupp : ∀ w, max R 1 < ‖w‖ → c w = 0 := by
    intro w hw
    by_contra hne
    have := hR (subset_tsupport _ hne)
    rw [mem_closedBall, dist_zero_right] at this
    linarith [le_max_left R 1]
  exact integrable_cauchyT_kernel (p := 3) (by norm_num) (lt_of_lt_of_le one_pos (le_max_right R 1))
    (wr_memLp hc hcc 3) hsupp z

/-- `T` of a finite combination of `C_c^∞` functions. -/
theorem wr_s2_cauchyT_sum {ι : Type} (t : Finset ι) (a : ι → ℂ) (c : ι → ℂ → ℂ)
    (hc : ∀ i, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (c i) ∧ HasCompactSupport (c i)) :
    cauchyT (fun z => ∑ i ∈ t, a i * c i z) = fun z => ∑ i ∈ t, a i * cauchyT (c i) z := by
  funext z
  show -(1 / π : ℂ) * ∫ ζ, (∑ i ∈ t, a i * c i ζ) / (ζ - z) =
    ∑ i ∈ t, a i * (-(1 / π : ℂ) * ∫ ζ, c i ζ / (ζ - z))
  have hint : ∀ i ∈ t, Integrable (fun ζ => a i * c i ζ / (ζ - z)) volume := fun i _ => by
    have := (wr_s2_kernel_int (hc i).1 (hc i).2 z).const_mul (a i)
    refine this.congr (Eventually.of_forall fun ζ => ?_)
    show a i * (c i ζ / (ζ - z)) = a i * c i ζ / (ζ - z)
    ring
  have hsum : (fun ζ => (∑ i ∈ t, a i * c i ζ) / (ζ - z)) = fun ζ => ∑ i ∈ t, a i * c i ζ / (ζ - z) := by
    funext ζ
    rw [Finset.sum_div]
  rw [hsum, integral_finset_sum t hint, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have : ∫ ζ, a i * c i ζ / (ζ - z) = a i * ∫ ζ, c i ζ / (ζ - z) := by
    rw [← integral_const_mul]
    congr 1
    funext ζ
    ring
  rw [this]
  ring

/-- `H` of a finite combination of `C_c^∞` functions (and the combination is `C_c^∞`). -/
theorem wr_s2_hS_sum {ι : Type} (t : Finset ι) (a : ι → ℂ) (c : ι → ℂ → ℂ)
    (hc : ∀ i, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (c i) ∧ HasCompactSupport (c i)) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z => ∑ i ∈ t, a i * c i z) ∧
      HasCompactSupport (fun z => ∑ i ∈ t, a i * c i z) ∧
      hilbertHSmooth (fun z => ∑ i ∈ t, a i * c i z) = fun z => ∑ i ∈ t, a i * hilbertHSmooth (c i) z := by
  induction t using Finset.induction_on with
  | empty =>
    have h0 := hilbertHSmooth_smul 0 (φ := fun _ => (0 : ℂ)) contDiff_const HasCompactSupport.zero
    simp only [zero_mul] at h0
    simp only [Finset.sum_empty]
    exact ⟨contDiff_const, HasCompactSupport.zero, h0⟩
  | insert i t hi ih =>
    obtain ⟨ih1, ih2, ih3⟩ := ih
    have hm1 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z => a i * c i z) := contDiff_const.mul (hc i).1
    have hm2 : HasCompactSupport (fun z => a i * c i z) := (hc i).2.mul_left
    simp only [Finset.sum_insert hi]
    refine ⟨hm1.add ih1, hm2.add ih2, ?_⟩
    rw [hilbertHSmooth_add hm1 hm2 ih1 ih2, hilbertHSmooth_smul (a i) (hc i).1 (hc i).2, ih3]

/-- `ν_P = P.1 ν₁ + P.2 ν₂` with real coefficients `Re Pₖ`, `Im Pₖ` and `C_c^∞` functions `νₖ`, `i νₖ`. -/
theorem wr_s2_nu (ν₁ ν₂ : ℂ → ℂ) (P : ℂ × ℂ) (z : ℂ) :
    P.1 * ν₁ z + P.2 * ν₂ z = ∑ b : Bool × Bool,
      ((cond b.2 (cond b.1 P.1 P.2).re (cond b.1 P.1 P.2).im : ℝ) : ℂ) * (cond b.2 1 I * cond b.1 (ν₁ z) (ν₂ z)) := by
  rw [Fintype.sum_prod_type, Fintype.sum_bool, Fintype.sum_bool, Fintype.sum_bool]
  simp only [cond]
  conv_lhs => rw [← Complex.re_add_im P.1, ← Complex.re_add_im P.2]
  ring

/-- The Neumann term `s P n` is a finite combination `Σ aᵢ(P) cᵢ` with continuous real `aᵢ` and `C_c^∞` `cᵢ`. -/
theorem wr_s2_rep {ν₁ ν₂ : ℂ → ℂ} (h₁ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ν₁) (hc₁ : HasCompactSupport ν₁)
    (h₂ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ν₂) (hc₂ : HasCompactSupport ν₂) {s : ℂ × ℂ → ℕ → ℂ → ℂ}
    (hs0 : ∀ P, s P 0 = fun z => P.1 * ν₁ z + P.2 * ν₂ z)
    (hs : ∀ P n, s P (n + 1) = fun z => (P.1 * ν₁ z + P.2 * ν₂ z) * hilbertHSmooth (s P n) z) (n : ℕ) :
    ∃ (ι : Type) (_ : Fintype ι) (a : ι → ℂ × ℂ → ℝ) (c : ι → ℂ → ℂ), (∀ i, Continuous (a i)) ∧
      (∀ i, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (c i) ∧ HasCompactSupport (c i)) ∧
      ∀ P, s P n = fun z => ∑ i, (a i P : ℂ) * c i z := by
  have he : ∀ b : Bool × Bool, Continuous fun P : ℂ × ℂ => cond b.2 (cond b.1 P.1 P.2).re (cond b.1 P.1 P.2).im := by
    rintro ⟨b1, b2⟩
    cases b1 <;> cases b2
    · exact Complex.continuous_im.comp continuous_snd
    · exact Complex.continuous_re.comp continuous_snd
    · exact Complex.continuous_im.comp continuous_fst
    · exact Complex.continuous_re.comp continuous_fst
  have hd : ∀ b : Bool × Bool, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z => cond b.2 1 I * cond b.1 (ν₁ z) (ν₂ z)) ∧
      HasCompactSupport (fun z => cond b.2 1 I * cond b.1 (ν₁ z) (ν₂ z)) := by
    rintro ⟨b1, b2⟩
    cases b1
    · exact ⟨contDiff_const.mul h₂, hc₂.mul_left⟩
    · exact ⟨contDiff_const.mul h₁, hc₁.mul_left⟩
  induction n with
  | zero =>
    refine ⟨Bool × Bool, inferInstance, fun b P => cond b.2 (cond b.1 P.1 P.2).re (cond b.1 P.1 P.2).im,
      fun b z => cond b.2 1 I * cond b.1 (ν₁ z) (ν₂ z), he, hd, fun P => ?_⟩
    rw [hs0 P]
    funext z
    exact wr_s2_nu ν₁ ν₂ P z
  | succ n ih =>
    obtain ⟨ι, hι, a, c, ha, hc, hrep⟩ := ih
    refine ⟨(Bool × Bool) × ι, inferInstance,
      fun bi P => cond bi.1.2 (cond bi.1.1 P.1 P.2).re (cond bi.1.1 P.1 P.2).im * a bi.2 P,
      fun bi z => (cond bi.1.2 1 I * cond bi.1.1 (ν₁ z) (ν₂ z)) * hilbertHSmooth (c bi.2) z, ?_, ?_, ?_⟩
    · rintro ⟨b, i⟩
      exact (he b).mul (ha i)
    · rintro ⟨b, i⟩
      exact wr_mul_hS_smooth (hd b).1 (hd b).2 (hc i).1 (hc i).2
    · intro P
      rw [hs P n, hrep P, (wr_s2_hS_sum Finset.univ (fun i => (a i P : ℂ)) c hc).2.2]
      funext z
      rw [wr_s2_nu ν₁ ν₂ P z, Finset.sum_mul_sum, ← Finset.sum_product', Finset.univ_product_univ]
      apply Finset.sum_congr rfl
      rintro ⟨b, i⟩ _
      push_cast
      ring

/-- (A3-S2) `[W2]` **Continuity of each Neumann term in the parameter.** For the two-parameter coefficient
`ν_P = P.1 ν₁ + P.2 ν₂` (`C_c^∞`), the `n`-th smooth Neumann term `s P n` is a polynomial in `P` with `C_c^∞`
coefficients. Hence the `z`-iterated derivatives of `cauchyT (s P n)` are jointly continuous in `(P, z)`. -/
theorem wr_iter_term_cont {ν₁ ν₂ : ℂ → ℂ} (h₁ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ν₁) (hc₁ : HasCompactSupport ν₁)
    (h₂ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ν₂) (hc₂ : HasCompactSupport ν₂) {s : ℂ × ℂ → ℕ → ℂ → ℂ}
    (hs0 : ∀ P, s P 0 = fun z => P.1 * ν₁ z + P.2 * ν₂ z)
    (hs : ∀ P n, s P (n + 1) = fun z => (P.1 * ν₁ z + P.2 * ν₂ z) * hilbertHSmooth (s P n) z) (n j : ℕ) :
    Continuous (fun q : (ℂ × ℂ) × ℂ => iteratedFDeriv ℝ j (cauchyT (s q.1 n)) q.2) := by
  obtain ⟨ι, hι, a, c, ha, hc, hrep⟩ := wr_s2_rep h₁ hc₁ h₂ hc₂ hs0 hs n
  have hT : ∀ i, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (cauchyT (c i)) := fun i =>
    wr_cauchyT_contDiff_top (hc i).1 (hc i).2
  have hTj : ∀ i, ContDiff ℝ j (cauchyT (c i)) := fun i => (hT i).of_le (by exact_mod_cast le_top)
  have key : ∀ q : (ℂ × ℂ) × ℂ, iteratedFDeriv ℝ j (cauchyT (s q.1 n)) q.2 =
      ∑ i, a i q.1 • iteratedFDeriv ℝ j (cauchyT (c i)) q.2 := by
    intro q
    rw [hrep q.1, wr_s2_cauchyT_sum Finset.univ (fun i => (a i q.1 : ℂ)) c hc]
    have hfun : (fun z => ∑ i, (a i q.1 : ℂ) * cauchyT (c i) z) = ∑ i, fun z => a i q.1 • cauchyT (c i) z := by
      funext z
      rw [Finset.sum_apply]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Complex.real_smul]
    rw [hfun, iteratedFDeriv_sum_apply fun i _ => ((hTj i).const_smul (a i q.1)).contDiffAt]
    refine Finset.sum_congr rfl fun i _ => ?_
    exact iteratedFDeriv_const_smul_apply' (hTj i).contDiffAt
  rw [show (fun q : (ℂ × ℂ) × ℂ => iteratedFDeriv ℝ j (cauchyT (s q.1 n)) q.2) =
    fun q => ∑ i, a i q.1 • iteratedFDeriv ℝ j (cauchyT (c i)) q.2 from funext key]
  refine continuous_finsetSum _ fun i _ => ((ha i).comp continuous_fst).smul ?_
  exact ((hT i).continuous_iteratedFDeriv (by exact_mod_cast le_top)).comp continuous_snd
/-! ### (S3, A4) series representation and Jacobian of the normalized solution, smooth case (下属3) -/

/-- A `C_c^∞` coefficient with `sup |ν| ≤ k` is a compactly supported Beltrami coefficient. -/
theorem wr_compactBeltrami {ν : ℂ → ℂ} (hν : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ν) (hνc : HasCompactSupport ν)
    {k : ℝ} (hνk : ∀ z, ‖ν z‖ ≤ k) : IsCompactBeltramiCoeff ν k := by
  refine ⟨⟨hν.continuous.aestronglyMeasurable, Eventually.of_forall hνk⟩, ?_⟩
  obtain ⟨R, hR⟩ := hνc.isCompact.isBounded.subset_closedBall 0
  refine ⟨R, fun z hz => image_eq_zero_of_notMem_tsupport fun h => ?_⟩
  have := mem_closedBall_zero_iff.mp (hR h)
  linarith

/-- A sequence with `‖x n‖ ≤ C rⁿ`, `r < 1`, is summable. -/
theorem wr_summable_geom {x : ℕ → ℂ} {C r : ℝ} (hr : r < 1) (h : ∀ n, ‖x n‖ ≤ C * r ^ n) : Summable x := by
  by_cases hr0 : 0 ≤ r
  · exact Summable.of_norm_bounded ((summable_geometric_of_lt_one hr0 hr).mul_left C) h
  · -- `r < 0`: the bounds at `n = 0, 1` force `C = 0`, hence `x = 0`
    have h0 := h 0
    have h1 := h 1
    simp only [pow_zero, mul_one, pow_one] at h0 h1
    have hC : C = 0 := by
      have a := norm_nonneg (x 0)
      have b := norm_nonneg (x 1)
      nlinarith
    have hx : x = 0 := by
      funext n
      have := h n
      rw [hC, zero_mul] at this
      exact norm_le_zero_iff.mp this
    rw [hx]
    exact summable_zero

/-- Normalization at `0, 1` of a q.c. plane homeomorphism `w` with dilatation `ν` gives `f_ν`. -/
theorem wr_ns_eq_affine {ν w : ℂ → ℂ} {K : ℝ} (hw : IsKQC w univ K) (hws : ∃ e : ℂ ≃ₜ ℂ, ⇑e = w)
    (hdil : ∀ᵐ z, complexDilatation w z = ν z) :
    w 1 - w 0 ≠ 0 ∧ normalizedSolution ν = fun z => (w z - w 0) / (w 1 - w 0) := by
  obtain ⟨e, he⟩ := hws
  have hne : w 1 - w 0 ≠ 0 := by
    intro h
    have h' : e 1 = e 0 := by rw [he]; exact sub_eq_zero.mp h
    exact one_ne_zero (e.injective h')
  set g : ℂ → ℂ := fun u => (u - w 0) / (w 1 - w 0) with hgd
  have hgc : IsConformalOnto g univ (g '' univ) := by
    refine ⟨fun u _ => ((differentiableAt_id.sub_const _).div_const _).differentiableWithinAt, ?_, rfl⟩
    intro a _ b _ hab
    have := (div_left_inj' hne).mp hab
    exact sub_left_inj.mp this
  have hgK : IsKQC g univ 1 := isKQC_one_of_conformal isOpen_univ hgc
  have hF : IsNormalizedSolution (g ∘ w) ν := by
    refine ⟨⟨K * 1, thm7_1_comp hw hgK (subset_univ _)⟩, ?_, ?_, ?_, ?_⟩
    · rw [image_comp, show w '' univ = univ by rw [← he, image_univ, e.surjective.range_eq]]
      apply eq_univ_of_forall
      intro v
      refine ⟨v * (w 1 - w 0) + w 0, mem_univ _, ?_⟩
      show (v * (w 1 - w 0) + w 0 - w 0) / (w 1 - w 0) = v
      rw [add_sub_cancel_right, mul_div_cancel_right₀ _ hne]
    · show (w 0 - w 0) / (w 1 - w 0) = 0
      rw [sub_self, zero_div]
    · show (w 1 - w 0) / (w 1 - w 0) = 1
      exact div_self hne
    · filter_upwards [hdil] with z hz
      rw [← hz]
      exact nxE_complexDilatation_affine hne z
  refine ⟨hne, ?_⟩
  show (if h : ∃ f : ℂ → ℂ, IsNormalizedSolution f ν then h.choose else id) = g ∘ w
  have hex : ∃ f : ℂ → ℂ, IsNormalizedSolution f ν := ⟨_, hF⟩
  rw [dif_pos hex]
  exact vz_plane_solution_unique hex.choose_spec hF

/-- (A3-S3) `[W3]` **Series representation of the normalized solution** for a `C_c^∞` coefficient with
`sup |ν| ≤ k < 1`. Here `s n` are the smooth Neumann terms (`s 0 = ν`, `s (n+1) = ν · H_smooth(s n)`). The
proof goes through `thm13_1_representation`; `beltramiIter ν n` is a.e. equal to `s n`, by
`hilbertH_eq_ae_smooth` and `hilbertH_congr_ae`. Then `thm12_1`/`thm12_2` and the normalization at `0, 1`. -/
theorem wr_ns_series {ν : ℂ → ℂ} (hν : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ν) (hνc : HasCompactSupport ν)
    {k : ℝ} (hk0 : 0 ≤ k) (hk : k < 1) (hνk : ∀ z, ‖ν z‖ ≤ k) {s : ℕ → ℂ → ℂ} (hs0 : s 0 = ν)
    (hs : ∀ n, s (n + 1) = fun z => ν z * hilbertHSmooth (s n) z) :
    (∀ z, Summable fun n => cauchyT (s n) z) ∧
      (1 + ∑' n, cauchyT (s n) 1) - ∑' n, cauchyT (s n) 0 ≠ 0 ∧
      normalizedSolution ν = fun z =>
        ((z + ∑' n, cauchyT (s n) z) - ∑' n, cauchyT (s n) 0) /
          ((1 + ∑' n, cauchyT (s n) 1) - ∑' n, cauchyT (s n) 0) := by
  have hcb := wr_compactBeltrami hν hνc hνk
  obtain ⟨p, hp, hkp, ω, hω, hsol, hgen, -⟩ := thm12_1 hk0 hk hcb
  obtain ⟨⟨C, r, hr, hbd⟩, hconv⟩ := thm13_1_representation hk0 hk hcb hp hkp hω hsol
  -- the `L^p` Neumann iterates are a.e. the smooth ones
  have hae : ∀ n, beltramiIter ν n =ᵐ[volume] s n := by
    intro n
    induction n with
    | zero =>
      rw [hs0]
      rfl
    | succ n ih =>
      obtain ⟨hsm, hsc⟩ := wr_iter_smooth hν hνc hs0 hs n
      have h1 : hilbertH (beltramiIter ν n) = hilbertH (s n) := hilbertH_congr_ae ih
      rw [rep_beltramiIter_succ, hs n, h1]
      filter_upwards [hilbertH_eq_ae_smooth hsm hsc] with z hz
      rw [hz]
  have hiter : ∀ n, cauchyT (beltramiIter ν n) = cauchyT (s n) := fun n => cauchyT_congr_ae (hae n)
  have hsum : ∀ z, Summable fun n => cauchyT (s n) z := fun z =>
    wr_summable_geom hr (fun n => by rw [← hiter n]; exact hbd n z)
  have htsum : ∀ z, ∑' n, cauchyT (s n) z = cauchyT ω z := by
    intro z
    have h1 : Tendsto (fun N => ∑ n ∈ Finset.range N, cauchyT (s n) z) atTop (𝓝 (cauchyT ω z)) := by
      have h := (hconv.tendsto_at z).sub_const z
      simp only [add_sub_cancel_left, hiter] at h
      exact h
    exact tendsto_nhds_unique (hsum z).hasSum.tendsto_sum_nat h1
  obtain ⟨hkqc, e, he⟩ := thm12_1_isKQC hk0 hk hcb hp hkp hω hsol
  obtain ⟨hne, hN⟩ := wr_ns_eq_affine hkqc ⟨e, he⟩ (t2_complexDilatation_ae hkqc hp hgen)
  simp only [zero_add] at hne hN
  refine ⟨hsum, ?_, ?_⟩
  · rw [htsum, htsum]
    exact hne
  · rw [hN]
    funext z
    rw [htsum, htsum, htsum]

/-- (A4) `[W1]` Positive Jacobian in the smooth compactly supported case (from `thm12_1_smooth_case` and the
normalization). -/
theorem wr_smooth_jacobian_pos {ν : ℂ → ℂ} (hν : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ν) (hc : HasCompactSupport ν)
    {k : ℝ} (hk : k < 1) (hνk : ∀ z, ‖ν z‖ ≤ k) (z : ℂ) :
    0 < ‖dz (normalizedSolution ν) z‖ ^ 2 - ‖dzbar (normalizedSolution ν) z‖ ^ 2 := by
  have hk0 : 0 ≤ k := (norm_nonneg _).trans (hνk 0)
  have hcb := wr_compactBeltrami hν hc hνk
  obtain ⟨p, hp, hkp, ω, hω, hsol, hgen, -⟩ := thm12_1 hk0 hk hcb
  obtain ⟨hkqc, e, he⟩ := thm12_1_isKQC hk0 hk hcb hp hkp hω hsol
  obtain ⟨hne, hN⟩ := wr_ns_eq_affine hkqc ⟨e, he⟩ (t2_complexDilatation_ae hkqc hp hgen)
  obtain ⟨a, hCD, -, hJ, -⟩ := thm12_1_smooth_case hk hν hc hνk hp hkp hω hsol
  set w : ℂ → ℂ := fun z => z + cauchyT ω z with hwd
  have hwz : DifferentiableAt ℝ w z := by
    have h := ((hCD.differentiable (by norm_num)) z).sub_const a
    simpa only [add_sub_cancel_right] using h
  set g : ℂ → ℂ := fun u => (u - w 0) / (w 1 - w 0) with hgd
  have hg : DifferentiableAt ℂ g (w z) := (differentiableAt_id.sub_const _).div_const _
  have hgd' : deriv g (w z) = 1 / (w 1 - w 0) := (((hasDerivAt_id _).sub_const _).div_const _).deriv
  obtain ⟨h1, h2⟩ := eq6_5 hwz hg
  rw [hN]
  show 0 < ‖dz (g ∘ w) z‖ ^ 2 - ‖dzbar (g ∘ w) z‖ ^ 2
  rw [h1, h2, hgd', norm_mul, norm_mul, mul_pow, mul_pow, ← mul_sub]
  exact mul_pos (pow_pos (norm_pos_iff.mpr (one_div_ne_zero hne)) 2) (hJ z)


/-! ### A3 assembly helpers (下属1) -/

/-- `∂_a` of a complex linear combination. -/
theorem wr_D_lin {f g : ℂ → ℂ} (hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f)
    (hg : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g) (c d a : ℂ) :
    (fun z => fderiv ℝ (fun z => c * f z + d * g z) z a) = fun z => c * fderiv ℝ f z a + d * fderiv ℝ g z a := by
  funext z
  have h : HasFDerivAt (fun z => c * f z + d * g z) (c • fderiv ℝ f z + d • fderiv ℝ g z) z :=
    ((hf.differentiable (by simp) z).hasFDerivAt.const_mul c).add
      ((hg.differentiable (by simp) z).hasFDerivAt.const_mul d)
  rw [h.fderiv]
  simp

/-- Second-order directional derivatives through `fderiv (fderiv f)`. -/
theorem wr_D2_eq {f : ℂ → ℂ} (hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f) (a b z : ℂ) :
    fderiv ℝ (fun z => fderiv ℝ f z b) z a = fderiv ℝ (fderiv ℝ f) z a b := by
  have hd : DifferentiableAt ℝ (fderiv ℝ f) z :=
    ((hf.fderiv_right (m := ((⊤ : ℕ∞) : WithTop ℕ∞)) (by simp)).differentiable (by simp)) z
  rw [(wr_hasFDerivAt_fderiv_apply hd b).fderiv]
  rfl



/-- Real `L^p` norm of a function dominated pointwise by an `L^p` function. -/
theorem wr_norm_mono {p : ℝ} {f : ℂ → ℂ} {g : ℂ → ℝ} (hf : Continuous f) (hg : MemLp g (ENNReal.ofReal p))
    (h : ∀ z, ‖f z‖ ≤ g z) :
    (eLpNorm f (ENNReal.ofReal p)).toReal ≤ (eLpNorm g (ENNReal.ofReal p)).toReal := by
  have hle : eLpNorm f (ENNReal.ofReal p) ≤ eLpNorm g (ENNReal.ofReal p) :=
    eLpNorm_mono_real hf.aestronglyMeasurable h
  exact ENNReal.toReal_mono hg.eLpNorm_ne_top hle

/-- The innermost direction decomposes along `1, I`. -/
theorem wr_D_basis (f : ℂ → ℂ) (c : ℂ) :
    (fun z => fderiv ℝ f z c) = fun z => (c.re : ℂ) * fderiv ℝ f z 1 + (c.im : ℂ) * fderiv ℝ f z I := by
  funext z
  have hc : c = c.re • (1 : ℂ) + c.im • I := by
    apply Complex.ext <;> simp
  conv_lhs => rw [hc]
  rw [map_add, map_smul, map_smul, Complex.real_smul, Complex.real_smul]

/-- `‖x.re · u + x.im · v‖ ≤ ‖u‖ + ‖v‖` for `‖x‖ ≤ 1`. -/
theorem wr_reim_le {x : ℂ} (hx : ‖x‖ ≤ 1) (u v : ℂ) : ‖(x.re : ℂ) * u + (x.im : ℂ) * v‖ ≤ ‖u‖ + ‖v‖ := by
  have hre : ‖(x.re : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs]; exact (Complex.abs_re_le_norm x).trans hx
  have him : ‖(x.im : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs]; exact (Complex.abs_im_le_norm x).trans hx
  calc ‖(x.re : ℂ) * u + (x.im : ℂ) * v‖ ≤ ‖(x.re : ℂ)‖ * ‖u‖ + ‖(x.im : ℂ)‖ * ‖v‖ := by
        rw [← norm_mul, ← norm_mul]; exact norm_add_le _ _
    _ ≤ ‖u‖ + ‖v‖ := by nlinarith [norm_nonneg u, norm_nonneg v, norm_nonneg (x.re : ℂ), norm_nonneg (x.im : ℂ)]

/-- Outer direction: `‖∂_a h‖ ≤ ‖∂_1 h‖ + ‖∂_I h‖`. -/
theorem wr_D_le1 (h : ℂ → ℂ) {a : ℂ} (ha : ‖a‖ ≤ 1) (z : ℂ) :
    ‖fderiv ℝ h z a‖ ≤ ‖fderiv ℝ h z 1‖ + ‖fderiv ℝ h z I‖ := by
  have e := congrFun (wr_D_basis h a) z
  beta_reduce at e
  rw [e]
  exact wr_reim_le ha _ _

/-- Middle direction: `‖∂_e ∂_b g‖ ≤ ‖∂_e ∂_1 g‖ + ‖∂_e ∂_I g‖`. -/
theorem wr_D_mid {g : ℂ → ℂ} (hg : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g) {b : ℂ} (hb : ‖b‖ ≤ 1) (e z : ℂ) :
    ‖fderiv ℝ (fun z => fderiv ℝ g z b) z e‖ ≤
      ‖fderiv ℝ (fun z => fderiv ℝ g z 1) z e‖ + ‖fderiv ℝ (fun z => fderiv ℝ g z I) z e‖ := by
  have l := congrFun (wr_D_lin (wr_fderiv_apply_contDiff_top hg 1) (wr_fderiv_apply_contDiff_top hg I)
    (b.re : ℂ) (b.im : ℂ) e) z
  beta_reduce at l
  rw [wr_D_basis g b, l]
  exact wr_reim_le hb _ _

/-- Inner direction: `‖∂_e ∂_e' ∂_c f‖ ≤ ‖∂_e ∂_e' ∂_1 f‖ + ‖∂_e ∂_e' ∂_I f‖`. -/
theorem wr_D_inner {f : ℂ → ℂ} (hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f) {c : ℂ} (hc : ‖c‖ ≤ 1) (e e' z : ℂ) :
    ‖fderiv ℝ (fun z => fderiv ℝ (fun z => fderiv ℝ f z c) z e') z e‖ ≤
      ‖fderiv ℝ (fun z => fderiv ℝ (fun z => fderiv ℝ f z 1) z e') z e‖ +
        ‖fderiv ℝ (fun z => fderiv ℝ (fun z => fderiv ℝ f z I) z e') z e‖ := by
  have g1 := wr_fderiv_apply_contDiff_top hf 1
  have gI := wr_fderiv_apply_contDiff_top hf I
  have l1 := wr_D_lin g1 gI (c.re : ℂ) (c.im : ℂ) e'
  have l2 := congrFun (wr_D_lin (wr_fderiv_apply_contDiff_top g1 e') (wr_fderiv_apply_contDiff_top gI e')
    (c.re : ℂ) (c.im : ℂ) e) z
  beta_reduce at l2
  rw [wr_D_basis f c, l1, l2]
  exact wr_reim_le hc _ _

/-- A `C_c^∞` function is bounded. -/
theorem wr_sc_bound {g : ℂ → ℂ} (hg : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g ∧ HasCompactSupport g) :
    ∃ C, 0 ≤ C ∧ ∀ z, ‖g z‖ ≤ C := by
  obtain ⟨C, hC⟩ := hg.1.continuous.bounded_above_of_compact_support hg.2
  exact ⟨C, (norm_nonneg _).trans (hC 0), hC⟩

/-- Uniform bounds (sup and `L^p`) for the directional derivatives of order `≤ 3`, over unit directions, of a
`C_c^∞` function. -/
theorem wr_word_bounds {f : ℂ → ℂ} (hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f) (hfc : HasCompactSupport f)
    (p : ℝ) :
    ∃ β : ℝ, 0 ≤ β ∧ ∀ a b c : ℂ, ‖a‖ ≤ 1 → ‖b‖ ≤ 1 → ‖c‖ ≤ 1 →
      (∀ z, ‖fderiv ℝ f z a‖ ≤ β ∧ ‖fderiv ℝ (fun z => fderiv ℝ f z b) z a‖ ≤ β ∧
        ‖fderiv ℝ (fun z => fderiv ℝ (fun z => fderiv ℝ f z c) z b) z a‖ ≤ β) ∧
      (eLpNorm f (ENNReal.ofReal p)).toReal ≤ β ∧
      (eLpNorm (fun z => fderiv ℝ f z a) (ENNReal.ofReal p)).toReal ≤ β ∧
      (eLpNorm (fun z => fderiv ℝ (fun z => fderiv ℝ f z b) z a) (ENNReal.ofReal p)).toReal ≤ β ∧
      (eLpNorm (fun z => fderiv ℝ (fun z => fderiv ℝ (fun z => fderiv ℝ f z c) z b) z a)
        (ENNReal.ofReal p)).toReal ≤ β := by
  have S : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f ∧ HasCompactSupport f := ⟨hf, hfc⟩
  -- order 1 basis functions
  set d1 := fun z => fderiv ℝ f z 1 with hd1
  set dI := fun z => fderiv ℝ f z I with hdI
  have S1 := wr_D_sc S 1
  have SI := wr_D_sc S I
  -- order 2
  have S11 := wr_D_sc S1 1
  have SI1 := wr_D_sc S1 I
  have S1I := wr_D_sc SI 1
  have SII := wr_D_sc SI I
  -- order 3
  have S111 := wr_D_sc S11 1
  have SI11 := wr_D_sc S11 I
  have S1I1 := wr_D_sc SI1 1
  have SII1 := wr_D_sc SI1 I
  have S11I := wr_D_sc S1I 1
  have SI1I := wr_D_sc S1I I
  have S1II := wr_D_sc SII 1
  have SIII := wr_D_sc SII I
  -- dominating functions
  set g1 : ℂ → ℝ := fun z => ‖fderiv ℝ f z 1‖ + ‖fderiv ℝ f z I‖ with hg1
  set g2 : ℂ → ℝ := fun z =>
    ‖fderiv ℝ (fun z => fderiv ℝ f z 1) z 1‖ + ‖fderiv ℝ (fun z => fderiv ℝ f z I) z 1‖ +
      (‖fderiv ℝ (fun z => fderiv ℝ f z 1) z I‖ + ‖fderiv ℝ (fun z => fderiv ℝ f z I) z I‖) with hg2
  set g3 : ℂ → ℝ := fun z =>
    ‖fderiv ℝ (fun z => fderiv ℝ (fun z => fderiv ℝ f z 1) z 1) z 1‖ +
        ‖fderiv ℝ (fun z => fderiv ℝ (fun z => fderiv ℝ f z I) z 1) z 1‖ +
      (‖fderiv ℝ (fun z => fderiv ℝ (fun z => fderiv ℝ f z 1) z I) z 1‖ +
        ‖fderiv ℝ (fun z => fderiv ℝ (fun z => fderiv ℝ f z I) z I) z 1‖) +
      (‖fderiv ℝ (fun z => fderiv ℝ (fun z => fderiv ℝ f z 1) z 1) z I‖ +
          ‖fderiv ℝ (fun z => fderiv ℝ (fun z => fderiv ℝ f z I) z 1) z I‖ +
        (‖fderiv ℝ (fun z => fderiv ℝ (fun z => fderiv ℝ f z 1) z I) z I‖ +
          ‖fderiv ℝ (fun z => fderiv ℝ (fun z => fderiv ℝ f z I) z I) z I‖)) with hg3
  have P1 : ∀ a, ‖a‖ ≤ 1 → ∀ z, ‖fderiv ℝ f z a‖ ≤ g1 z := fun a ha z => wr_D_le1 f ha z
  have P2 : ∀ a b, ‖a‖ ≤ 1 → ‖b‖ ≤ 1 → ∀ z, ‖fderiv ℝ (fun z => fderiv ℝ f z b) z a‖ ≤ g2 z := by
    intro a b ha hb z
    have h1 := wr_D_le1 (fun z => fderiv ℝ f z b) ha z
    have h2 := wr_D_mid hf hb 1 z
    have h3 := wr_D_mid hf hb I z
    simp only [hg2]
    linarith
  have P3 : ∀ a b c, ‖a‖ ≤ 1 → ‖b‖ ≤ 1 → ‖c‖ ≤ 1 → ∀ z,
      ‖fderiv ℝ (fun z => fderiv ℝ (fun z => fderiv ℝ f z c) z b) z a‖ ≤ g3 z := by
    intro a b c ha hb hc z
    have h1 := wr_D_le1 (fun z => fderiv ℝ (fun z => fderiv ℝ f z c) z b) ha z
    have hcs := wr_fderiv_apply_contDiff_top hf c
    have m1 := wr_D_mid hcs hb 1 z
    have m2 := wr_D_mid hcs hb I z
    have i1 := wr_D_inner hf hc 1 1 z
    have i2 := wr_D_inner hf hc 1 I z
    have i3 := wr_D_inner hf hc I 1 z
    have i4 := wr_D_inner hf hc I I z
    simp only [hg3]
    linarith
  have hc1 : Continuous g1 := (S1.1.continuous.norm.add SI.1.continuous.norm)
  have hc2 : Continuous g2 :=
    (S11.1.continuous.norm.add S1I.1.continuous.norm).add (SI1.1.continuous.norm.add SII.1.continuous.norm)
  have hc3 : Continuous g3 :=
    ((S111.1.continuous.norm.add S11I.1.continuous.norm).add (S1I1.1.continuous.norm.add S1II.1.continuous.norm)).add
      ((SI11.1.continuous.norm.add SI1I.1.continuous.norm).add (SII1.1.continuous.norm.add SIII.1.continuous.norm))
  have hs1 : HasCompactSupport g1 := S1.2.norm.add SI.2.norm
  have hs2 : HasCompactSupport g2 := (S11.2.norm.add S1I.2.norm).add (SI1.2.norm.add SII.2.norm)
  have hs3 : HasCompactSupport g3 :=
    ((S111.2.norm.add S11I.2.norm).add (S1I1.2.norm.add S1II.2.norm)).add
      ((SI11.2.norm.add SI1I.2.norm).add (SII1.2.norm.add SIII.2.norm))
  obtain ⟨C1, hC1⟩ := hc1.bounded_above_of_compact_support hs1
  obtain ⟨C2, hC2⟩ := hc2.bounded_above_of_compact_support hs2
  obtain ⟨C3, hC3⟩ := hc3.bounded_above_of_compact_support hs3
  have hC1' : ∀ z, g1 z ≤ C1 := fun z => (Real.le_norm_self _).trans (hC1 z)
  have hC2' : ∀ z, g2 z ≤ C2 := fun z => (Real.le_norm_self _).trans (hC2 z)
  have hC3' : ∀ z, g3 z ≤ C3 := fun z => (Real.le_norm_self _).trans (hC3 z)
  have hC1n : 0 ≤ C1 := (norm_nonneg _).trans (hC1 0)
  have hC2n : 0 ≤ C2 := (norm_nonneg _).trans (hC2 0)
  have hC3n : 0 ≤ C3 := (norm_nonneg _).trans (hC3 0)
  have m1 : MemLp g1 (ENNReal.ofReal p) := hc1.memLp_of_hasCompactSupport hs1
  have m2 : MemLp g2 (ENNReal.ofReal p) := hc2.memLp_of_hasCompactSupport hs2
  have m3 : MemLp g3 (ENNReal.ofReal p) := hc3.memLp_of_hasCompactSupport hs3
  obtain ⟨N0, hN0, hN0e⟩ : ∃ N, 0 ≤ N ∧ (eLpNorm f (ENNReal.ofReal p)).toReal = N :=
    ⟨_, ENNReal.toReal_nonneg, rfl⟩
  obtain ⟨N1, hN1, hN1e⟩ : ∃ N, 0 ≤ N ∧ (eLpNorm g1 (ENNReal.ofReal p)).toReal = N :=
    ⟨_, ENNReal.toReal_nonneg, rfl⟩
  obtain ⟨N2, hN2, hN2e⟩ : ∃ N, 0 ≤ N ∧ (eLpNorm g2 (ENNReal.ofReal p)).toReal = N :=
    ⟨_, ENNReal.toReal_nonneg, rfl⟩
  obtain ⟨N3, hN3, hN3e⟩ : ∃ N, 0 ≤ N ∧ (eLpNorm g3 (ENNReal.ofReal p)).toReal = N :=
    ⟨_, ENNReal.toReal_nonneg, rfl⟩
  refine ⟨C1 + C2 + C3 + N0 + N1 + N2 + N3, by linarith, fun a b c ha hb hc => ?_⟩
  have q1 := wr_norm_mono (wr_D_sc S a).1.continuous m1 (P1 a ha)
  have q2 := wr_norm_mono (wr_D_sc (wr_D_sc S b) a).1.continuous m2 (P2 a b ha hb)
  have q3 := wr_norm_mono (wr_D_sc (wr_D_sc (wr_D_sc S c) b) a).1.continuous m3 (P3 a b c ha hb hc)
  rw [hN1e] at q1
  rw [hN2e] at q2
  rw [hN3e] at q3
  refine ⟨fun z => ⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · have := (P1 a ha z).trans (hC1' z); linarith
  · have := (P2 a b ha hb z).trans (hC2' z); linarith
  · have := (P3 a b c ha hb hc z).trans (hC3' z); linarith
  · rw [hN0e]; linarith
  · linarith
  · linarith
  · linarith

/-- Directional derivatives of `T g` are `T` of the directional derivatives. -/
theorem wr_D_cauchyT {g : ℂ → ℂ} (hg : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g) (hgc : HasCompactSupport g) (a : ℂ) :
    (fun z => fderiv ℝ (cauchyT g) z a) = cauchyT (fun z => fderiv ℝ g z a) := by
  funext z
  exact fderiv_cauchyT_apply (hg.of_le (by simp)) hgc z a

/-- Directional derivatives do not enlarge the topological support. -/
theorem wr_tsupport_D {g : ℂ → ℂ} (a : ℂ) : tsupport (fun z => fderiv ℝ g z a) ⊆ tsupport g := by
  refine (tsupport_comp_subset (g := fun L : ℂ →L[ℝ] ℂ => L a) (by simp) (fderiv ℝ g)).trans ?_
  exact tsupport_fderiv_subset ℝ


/-- `‖c X + d Y‖_p ≤ |c| ‖X‖_p + |d| ‖Y‖_p`. -/
theorem wr_norm_lin {p : ℝ} (hp : 1 ≤ p) {X Y : ℂ → ℂ} (hX : MemLp X (ENNReal.ofReal p))
    (hY : MemLp Y (ENNReal.ofReal p)) (c d : ℂ) :
    (eLpNorm (fun z => c * X z + d * Y z) (ENNReal.ofReal p)).toReal ≤
      ‖c‖ * (eLpNorm X (ENNReal.ofReal p)).toReal + ‖d‖ * (eLpNorm Y (ENNReal.ofReal p)).toReal := by
  have ec : eLpNorm (fun z => c * X z) (ENNReal.ofReal p) = ‖c‖ₑ * eLpNorm X (ENNReal.ofReal p) :=
    eLpNorm_const_smul c X _ _
  have ed : eLpNorm (fun z => d * Y z) (ENNReal.ofReal p) = ‖d‖ₑ * eLpNorm Y (ENNReal.ofReal p) :=
    eLpNorm_const_smul d Y _ _
  have mc : MemLp (fun z => c * X z) (ENNReal.ofReal p) := by
    show eLpNorm (fun z => c * X z) (ENNReal.ofReal p) < ⊤
    rw [ec]; exact ENNReal.mul_lt_top enorm_lt_top hX
  have md : MemLp (fun z => d * Y z) (ENNReal.ofReal p) := by
    show eLpNorm (fun z => d * Y z) (ENNReal.ofReal p) < ⊤
    rw [ed]; exact ENNReal.mul_lt_top enorm_lt_top hY
  have h := wr_norm_add_le hp mc md
  rw [ec, ed, ENNReal.toReal_mul, ENNReal.toReal_mul, show ‖c‖ₑ.toReal = ‖c‖ by simp,
    show ‖d‖ₑ.toReal = ‖d‖ by simp] at h
  exact h

/-- Word bounds for a linear combination `c ν₁ + d ν₂`. -/
theorem wr_lin_bounds {ν₁ ν₂ : ℂ → ℂ} (h₁ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ν₁) (hc₁ : HasCompactSupport ν₁)
    (h₂ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ν₂) (hc₂ : HasCompactSupport ν₂) {p β₁ β₂ R : ℝ} (hp : 1 ≤ p)
    (hb₁ : ∀ a b c : ℂ, ‖a‖ ≤ 1 → ‖b‖ ≤ 1 → ‖c‖ ≤ 1 →
      (∀ z, ‖fderiv ℝ ν₁ z a‖ ≤ β₁ ∧ ‖fderiv ℝ (fun z => fderiv ℝ ν₁ z b) z a‖ ≤ β₁ ∧
        ‖fderiv ℝ (fun z => fderiv ℝ (fun z => fderiv ℝ ν₁ z c) z b) z a‖ ≤ β₁) ∧
      (eLpNorm ν₁ (ENNReal.ofReal p)).toReal ≤ β₁ ∧
      (eLpNorm (fun z => fderiv ℝ ν₁ z a) (ENNReal.ofReal p)).toReal ≤ β₁ ∧
      (eLpNorm (fun z => fderiv ℝ (fun z => fderiv ℝ ν₁ z b) z a) (ENNReal.ofReal p)).toReal ≤ β₁ ∧
      (eLpNorm (fun z => fderiv ℝ (fun z => fderiv ℝ (fun z => fderiv ℝ ν₁ z c) z b) z a)
        (ENNReal.ofReal p)).toReal ≤ β₁)
    (hb₂ : ∀ a b c : ℂ, ‖a‖ ≤ 1 → ‖b‖ ≤ 1 → ‖c‖ ≤ 1 →
      (∀ z, ‖fderiv ℝ ν₂ z a‖ ≤ β₂ ∧ ‖fderiv ℝ (fun z => fderiv ℝ ν₂ z b) z a‖ ≤ β₂ ∧
        ‖fderiv ℝ (fun z => fderiv ℝ (fun z => fderiv ℝ ν₂ z c) z b) z a‖ ≤ β₂) ∧
      (eLpNorm ν₂ (ENNReal.ofReal p)).toReal ≤ β₂ ∧
      (eLpNorm (fun z => fderiv ℝ ν₂ z a) (ENNReal.ofReal p)).toReal ≤ β₂ ∧
      (eLpNorm (fun z => fderiv ℝ (fun z => fderiv ℝ ν₂ z b) z a) (ENNReal.ofReal p)).toReal ≤ β₂ ∧
      (eLpNorm (fun z => fderiv ℝ (fun z => fderiv ℝ (fun z => fderiv ℝ ν₂ z c) z b) z a)
        (ENNReal.ofReal p)).toReal ≤ β₂)
    {c d : ℂ} (hc : ‖c‖ ≤ R) (hd : ‖d‖ ≤ R) :
    ∀ a b e : ℂ, ‖a‖ ≤ 1 → ‖b‖ ≤ 1 → ‖e‖ ≤ 1 →
      (∀ z, ‖fderiv ℝ (fun z => c * ν₁ z + d * ν₂ z) z a‖ ≤ R * (β₁ + β₂) ∧
        ‖fderiv ℝ (fun z => fderiv ℝ (fun z => c * ν₁ z + d * ν₂ z) z b) z a‖ ≤ R * (β₁ + β₂) ∧
        ‖fderiv ℝ (fun z => fderiv ℝ (fun z => fderiv ℝ (fun z => c * ν₁ z + d * ν₂ z) z e) z b) z a‖ ≤
          R * (β₁ + β₂)) ∧
      (eLpNorm (fun z => c * ν₁ z + d * ν₂ z) (ENNReal.ofReal p)).toReal ≤ R * (β₁ + β₂) ∧
      (eLpNorm (fun z => fderiv ℝ (fun z => c * ν₁ z + d * ν₂ z) z a) (ENNReal.ofReal p)).toReal ≤
        R * (β₁ + β₂) ∧
      (eLpNorm (fun z => fderiv ℝ (fun z => fderiv ℝ (fun z => c * ν₁ z + d * ν₂ z) z b) z a)
        (ENNReal.ofReal p)).toReal ≤ R * (β₁ + β₂) ∧
      (eLpNorm (fun z => fderiv ℝ (fun z => fderiv ℝ (fun z => fderiv ℝ (fun z => c * ν₁ z + d * ν₂ z) z e) z b) z a)
        (ENNReal.ofReal p)).toReal ≤ R * (β₁ + β₂) := by
  intro a b e ha hb he
  obtain ⟨s1, n01, n11, n21, n31⟩ := hb₁ a b e ha hb he
  obtain ⟨s2, n02, n12, n22, n32⟩ := hb₂ a b e ha hb he
  have S1 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ν₁ ∧ HasCompactSupport ν₁ := ⟨h₁, hc₁⟩
  have S2 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ν₂ ∧ HasCompactSupport ν₂ := ⟨h₂, hc₂⟩
  have hR : 0 ≤ R := (norm_nonneg _).trans hc
  -- identities
  have e1 : (fun z => fderiv ℝ (fun z => c * ν₁ z + d * ν₂ z) z a) =
      fun z => c * fderiv ℝ ν₁ z a + d * fderiv ℝ ν₂ z a := wr_D_lin h₁ h₂ c d a
  have e2 : (fun z => fderiv ℝ (fun z => fderiv ℝ (fun z => c * ν₁ z + d * ν₂ z) z b) z a) =
      fun z => c * fderiv ℝ (fun z => fderiv ℝ ν₁ z b) z a + d * fderiv ℝ (fun z => fderiv ℝ ν₂ z b) z a := by
    exact (congrArg (fun f : ℂ → ℂ => fun z => fderiv ℝ f z a) (wr_D_lin h₁ h₂ c d b)).trans
      (wr_D_lin (wr_D_sc S1 b).1 (wr_D_sc S2 b).1 c d a)
  have e3 : (fun z => fderiv ℝ (fun z => fderiv ℝ (fun z => fderiv ℝ (fun z => c * ν₁ z + d * ν₂ z) z e) z b) z a) =
      fun z => c * fderiv ℝ (fun z => fderiv ℝ (fun z => fderiv ℝ ν₁ z e) z b) z a +
        d * fderiv ℝ (fun z => fderiv ℝ (fun z => fderiv ℝ ν₂ z e) z b) z a := by
    exact (congrArg (fun f : ℂ → ℂ => fun z => fderiv ℝ f z a)
      ((congrArg (fun f : ℂ → ℂ => fun z => fderiv ℝ f z b) (wr_D_lin h₁ h₂ c d e)).trans
        (wr_D_lin (wr_D_sc S1 e).1 (wr_D_sc S2 e).1 c d b))).trans
      (wr_D_lin (wr_D_sc (wr_D_sc S1 e) b).1 (wr_D_sc (wr_D_sc S2 e) b).1 c d a)
  have pt : ∀ x y : ℂ, ‖x‖ ≤ β₁ → ‖y‖ ≤ β₂ → ‖c * x + d * y‖ ≤ R * (β₁ + β₂) := by
    intro x y hx hy
    calc ‖c * x + d * y‖ ≤ ‖c‖ * ‖x‖ + ‖d‖ * ‖y‖ := by
          rw [← norm_mul, ← norm_mul]; exact norm_add_le _ _
      _ ≤ R * β₁ + R * β₂ := by
          gcongr
      _ = R * (β₁ + β₂) := by ring
  have nl : ∀ X Y : ℂ → ℂ, (ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) X ∧ HasCompactSupport X) →
      (ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Y ∧ HasCompactSupport Y) →
      (eLpNorm X (ENNReal.ofReal p)).toReal ≤ β₁ → (eLpNorm Y (ENNReal.ofReal p)).toReal ≤ β₂ →
      (eLpNorm (fun z => c * X z + d * Y z) (ENNReal.ofReal p)).toReal ≤ R * (β₁ + β₂) := by
    intro X Y hX hY hXb hYb
    have h := wr_norm_lin hp (wr_memLp hX.1 hX.2 p) (wr_memLp hY.1 hY.2 p) c d
    have hXn : 0 ≤ (eLpNorm X (ENNReal.ofReal p)).toReal := ENNReal.toReal_nonneg
    have hYn : 0 ≤ (eLpNorm Y (ENNReal.ofReal p)).toReal := ENNReal.toReal_nonneg
    have h2 : ‖c‖ * (eLpNorm X (ENNReal.ofReal p)).toReal + ‖d‖ * (eLpNorm Y (ENNReal.ofReal p)).toReal ≤
        R * β₁ + R * β₂ := add_le_add (mul_le_mul hc hXb hXn hR) (mul_le_mul hd hYb hYn hR)
    exact h.trans (h2.trans (le_of_eq (by ring)))
  refine ⟨fun z => ⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · rw [show fderiv ℝ (fun z => c * ν₁ z + d * ν₂ z) z a = c * fderiv ℝ ν₁ z a + d * fderiv ℝ ν₂ z a from
      congrFun e1 z]
    exact pt _ _ (s1 z).1 (s2 z).1
  · rw [show fderiv ℝ (fun z => fderiv ℝ (fun z => c * ν₁ z + d * ν₂ z) z b) z a =
        c * fderiv ℝ (fun z => fderiv ℝ ν₁ z b) z a + d * fderiv ℝ (fun z => fderiv ℝ ν₂ z b) z a from
      congrFun e2 z]
    exact pt _ _ (s1 z).2.1 (s2 z).2.1
  · rw [show fderiv ℝ (fun z => fderiv ℝ (fun z => fderiv ℝ (fun z => c * ν₁ z + d * ν₂ z) z e) z b) z a =
        c * fderiv ℝ (fun z => fderiv ℝ (fun z => fderiv ℝ ν₁ z e) z b) z a +
          d * fderiv ℝ (fun z => fderiv ℝ (fun z => fderiv ℝ ν₂ z e) z b) z a from congrFun e3 z]
    exact pt _ _ (s1 z).2.2 (s2 z).2.2
  · exact nl ν₁ ν₂ S1 S2 n01 n02
  · rw [e1]; exact nl _ _ (wr_D_sc S1 a) (wr_D_sc S2 a) n11 n12
  · rw [e2]; exact nl _ _ (wr_D_sc (wr_D_sc S1 b) a) (wr_D_sc (wr_D_sc S2 b) a) n21 n22
  · rw [e3]
    exact nl _ _ (wr_D_sc (wr_D_sc (wr_D_sc S1 e) b) a) (wr_D_sc (wr_D_sc (wr_D_sc S2 e) b) a) n31 n32

/-- All four levels at once, with the common constant `E = L (1 + Γ)³`. -/
theorem wr_all_levels {p : ℝ} (hp : 1 < p) {ν : ℂ → ℂ} (hν : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ν)
    (hνc : HasCompactSupport ν) {k : ℝ} (hk : 0 ≤ k) (hνk : ∀ z, ‖ν z‖ ≤ k) {ρ L B Γ : ℝ}
    (hρ : k * hilbertNorm p < ρ) (hL : 0 ≤ L) (hB : 0 ≤ B)
    (hΓ : 7 * B * hilbertNorm p / (ρ - k * hilbertNorm p) ≤ Γ) (hΓ0 : 0 ≤ Γ)
    (hw : ∀ a b c : ℂ, ‖a‖ ≤ 1 → ‖b‖ ≤ 1 → ‖c‖ ≤ 1 →
      (∀ z, ‖fderiv ℝ ν z a‖ ≤ B ∧ ‖fderiv ℝ (fun z => fderiv ℝ ν z b) z a‖ ≤ B ∧
        ‖fderiv ℝ (fun z => fderiv ℝ (fun z => fderiv ℝ ν z c) z b) z a‖ ≤ B) ∧
      (eLpNorm ν (ENNReal.ofReal p)).toReal ≤ L ∧
      (eLpNorm (fun z => fderiv ℝ ν z a) (ENNReal.ofReal p)).toReal ≤ L ∧
      (eLpNorm (fun z => fderiv ℝ (fun z => fderiv ℝ ν z b) z a) (ENNReal.ofReal p)).toReal ≤ L ∧
      (eLpNorm (fun z => fderiv ℝ (fun z => fderiv ℝ (fun z => fderiv ℝ ν z c) z b) z a)
        (ENNReal.ofReal p)).toReal ≤ L)
    {s : ℕ → ℂ → ℂ} (hs0 : s 0 = ν) (hs : ∀ n, s (n + 1) = fun z => ν z * hilbertHSmooth (s n) z)
    {a b c : ℂ} (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) (hc : ‖c‖ ≤ 1) (n : ℕ) :
    (eLpNorm (s n) (ENNReal.ofReal p)).toReal ≤ L * (1 + Γ) * (1 + Γ) * (1 + Γ) * ρ ^ n ∧
    (eLpNorm (fun z => fderiv ℝ (s n) z a) (ENNReal.ofReal p)).toReal ≤
      L * (1 + Γ) * (1 + Γ) * (1 + Γ) * ρ ^ n ∧
    (eLpNorm (fun z => fderiv ℝ (fun z => fderiv ℝ (s n) z b) z a) (ENNReal.ofReal p)).toReal ≤
      L * (1 + Γ) * (1 + Γ) * (1 + Γ) * ρ ^ n ∧
    (eLpNorm (fun z => fderiv ℝ (fun z => fderiv ℝ (fun z => fderiv ℝ (s n) z c) z b) z a)
      (ENNReal.ofReal p)).toReal ≤ L * (1 + Γ) * (1 + Γ) * (1 + Γ) * ρ ^ n := by
  have w1 := hw a b c ha hb hc
  have w2 := hw b c c hb hc hc
  have w3 := hw c c c hc hc hc
  have w4 := hw a c c ha hc hc
  have hνL := w1.2.1
  have hρ0 : 0 ≤ ρ := (mul_nonneg hk (hilbertNorm_nonneg p)).trans hρ.le
  have hp0 : 0 ≤ ρ ^ n := pow_nonneg hρ0 n
  have g1 : L ≤ L * (1 + Γ) := by nlinarith
  have g2 : L * (1 + Γ) ≤ L * (1 + Γ) * (1 + Γ) := by nlinarith
  have g3 : L * (1 + Γ) * (1 + Γ) ≤ L * (1 + Γ) * (1 + Γ) * (1 + Γ) := by nlinarith
  have l0 := wr_lv0 hp hν hνc hk hνk hρ hL hνL hs0 hs n
  have l1 := wr_lv1 hp hν hνc hk hνk hρ hL hB hΓ hνL hs0 hs (fun z => ((w1.1 z).1)) w1.2.2.1 n
  have l2 := wr_lv2 hp hν hνc hk hνk hρ hL hB hΓ hνL hs0 hs (fun z => (w1.1 z).1) (fun z => (w2.1 z).1)
    (fun z => (w1.1 z).2.1) w1.2.2.1 w2.2.2.1 w1.2.2.2.1 n
  have l3 := wr_lv3 hp hν hνc hk hνk hρ hL hB hΓ hνL hs0 hs (fun z => (w1.1 z).1) (fun z => (w2.1 z).1)
    (fun z => (w3.1 z).1) (fun z => (w1.1 z).2.1) (fun z => (w4.1 z).2.1) (fun z => (w2.1 z).2.1)
    (fun z => (w1.1 z).2.2) w1.2.2.1 w2.2.2.1 w3.2.2.1 w1.2.2.2.1 w4.2.2.2.1 w2.2.2.2.1 w1.2.2.2.2 n
  refine ⟨?_, ?_, ?_, l3⟩
  · exact l0.trans (mul_le_mul_of_nonneg_right ((g1.trans g2).trans g3) hp0)
  · exact l1.trans (mul_le_mul_of_nonneg_right (g2.trans g3) hp0)
  · exact l2.trans (mul_le_mul_of_nonneg_right g3 hp0)

/-- Derivatives vanish where the function vanishes on an open set. -/
theorem wr_D_zero_on {g : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U) (hg : ∀ y ∈ U, g y = 0) (v : ℂ) :
    ∀ y ∈ U, fderiv ℝ g y v = 0 := by
  intro y hy
  have h : g =ᶠ[𝓝 y] fun _ => (0 : ℂ) := by
    filter_upwards [hU.mem_nhds hy] with x hx
    exact hg x hx
  rw [h.fderiv_eq]
  simp


/-- Joint continuity of the `z`-derivatives survives the affine normalization `(z + F z − c₀)/D`. -/
theorem wr_affine_iter_cont {X : Type*} [TopologicalSpace X] {S : Set X} {F : X → ℂ → ℂ} {c0 D : X → ℂ}
    (hF : ∀ x ∈ S, ContDiff ℝ 3 (F x))
    (hFc : ∀ j ≤ 3, ContinuousOn (fun q : X × ℂ => iteratedFDeriv ℝ j (F q.1) q.2) (S ×ˢ univ))
    (hc0 : ContinuousOn c0 S) (hD : ContinuousOn D S) (hD0 : ∀ x ∈ S, D x ≠ 0) :
    ∀ j ≤ 3, ContinuousOn (fun q : X × ℂ => iteratedFDeriv ℝ j (fun z => ((z + F q.1 z) - c0 q.1) / D q.1) q.2)
      (S ×ˢ univ) := by
  have hfst : ContinuousOn (fun q : X × ℂ => q.1) (S ×ˢ univ) := continuous_fst.continuousOn
  have hmaps : MapsTo (fun q : X × ℂ => q.1) (S ×ˢ univ) S := fun q hq => hq.1
  have hc0' : ContinuousOn (fun q : X × ℂ => c0 q.1) (S ×ˢ univ) := hc0.comp hfst hmaps
  have hD' : ContinuousOn (fun q : X × ℂ => D q.1) (S ×ˢ univ) := hD.comp hfst hmaps
  have hFv : ContinuousOn (fun q : X × ℂ => F q.1 q.2) (S ×ˢ univ) := by
    have h0 := hFc 0 (by norm_num)
    refine ((continuousMultilinearCurryFin0 ℝ ℂ ℂ).continuous.comp_continuousOn h0).congr ?_
    intro q _
    simp [iteratedFDeriv_zero_eq_comp]
  intro j hj
  rcases Nat.eq_zero_or_pos j with rfl | hj0
  · have hval : ContinuousOn (fun q : X × ℂ => ((q.2 + F q.1 q.2) - c0 q.1) / D q.1) (S ×ˢ univ) :=
      ((continuous_snd.continuousOn.add hFv).sub hc0').div hD' (fun q hq => hD0 q.1 hq.1)
    refine ((continuousMultilinearCurryFin0 ℝ ℂ ℂ).symm.continuous.comp_continuousOn hval).congr ?_
    intro q _
    simp [iteratedFDeriv_zero_eq_comp]
  · have : ContinuousSMul ℂ (ContinuousMultilinearMap ℝ (fun _ : Fin j => ℂ) ℂ) := IsBoundedSMul.continuousSMul
    have hjn : ((j : ℕ) : WithTop ℕ∞) ≤ 3 := by exact_mod_cast hj
    have hid : Continuous (fun z : ℂ => iteratedFDeriv ℝ j (fun z : ℂ => z) z) :=
      (contDiff_id (n := ((⊤ : ℕ∞) : WithTop ℕ∞))).continuous_iteratedFDeriv (WithTop.coe_le_coe.2 le_top)
    have htarget : ContinuousOn (fun q : X × ℂ => (D q.1)⁻¹ •
        (iteratedFDeriv ℝ j (fun z : ℂ => z) q.2 + iteratedFDeriv ℝ j (F q.1) q.2)) (S ×ˢ univ) :=
      (hD'.inv₀ (fun q hq => hD0 q.1 hq.1)).smul ((hid.comp continuous_snd).continuousOn.add (hFc j hj))
    refine htarget.congr ?_
    intro q hq
    have hx := hq.1
    have hFj : ContDiff ℝ j (F q.1) := (hF q.1 hx).of_le hjn
    have e : (fun z => ((z + F q.1 z) - c0 q.1) / D q.1) =
        (D q.1)⁻¹ • ((fun z : ℂ => z) + F q.1) + fun _ => -(c0 q.1 / D q.1) := by
      funext z
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      field_simp [hD0 q.1 hx]
      ring
    have hG : ContDiff ℝ j ((fun z : ℂ => z) + F q.1) := contDiff_id.add hFj
    have hs : ContDiffAt ℝ j ((D q.1)⁻¹ • ((fun z : ℂ => z) + F q.1)) q.2 := (hG.const_smul (D q.1)⁻¹).contDiffAt
    have hk : ContDiffAt ℝ j (fun _ : ℂ => -(c0 q.1 / D q.1)) q.2 := contDiff_const.contDiffAt
    have hi : ContDiffAt ℝ j (fun z : ℂ => z) q.2 := contDiff_id.contDiffAt
    beta_reduce
    rw [e, iteratedFDeriv_add_apply hs hk,
      iteratedFDeriv_const_smul_apply hG.contDiffAt,
      iteratedFDeriv_add_apply hi hFj.contDiffAt,
      iteratedFDeriv_const_of_ne (Nat.pos_iff_ne_zero.1 hj0)]
    simp


/-- A complex linear combination of `C_c^∞` functions is `C_c^∞`. -/
theorem wr_lin_sc {ν₁ ν₂ : ℂ → ℂ} (h₁ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ν₁) (hc₁ : HasCompactSupport ν₁)
    (h₂ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ν₂) (hc₂ : HasCompactSupport ν₂) (c d : ℂ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z => c * ν₁ z + d * ν₂ z) ∧
      HasCompactSupport (fun z => c * ν₁ z + d * ν₂ z) := by
  refine ⟨(contDiff_const.mul h₁).add (contDiff_const.mul h₂), ?_⟩
  refine HasCompactSupport.intro (hc₁.isCompact.union hc₂.isCompact) (fun x hx => ?_)
  have h1 : ν₁ x = 0 := image_eq_zero_of_notMem_tsupport (fun h => hx (Or.inl h))
  have h2 : ν₂ x = 0 := image_eq_zero_of_notMem_tsupport (fun h => hx (Or.inr h))
  show c * ν₁ x + d * ν₂ x = 0
  rw [h1, h2]; ring

/-- Local version of A3 at a parameter `P₀ ∈ W`: on a small ball the series `Σ' T(s P n)` is `C³` in `z` with
jointly continuous `z`-derivatives. -/
theorem wr_A3_local {ν₁ ν₂ : ℂ → ℂ} (h₁ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ν₁) (hc₁ : HasCompactSupport ν₁)
    (h₂ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ν₂) (hc₂ : HasCompactSupport ν₂) {W : Set (ℂ × ℂ)} (hW : IsOpen W)
    (hWk : ∀ P ∈ W, ∃ k < 1, ∀ z, ‖P.1 * ν₁ z + P.2 * ν₂ z‖ ≤ k) {s : ℂ × ℂ → ℕ → ℂ → ℂ}
    (hs0 : ∀ P, s P 0 = fun z => P.1 * ν₁ z + P.2 * ν₂ z)
    (hs : ∀ P n, s P (n + 1) = fun z => (P.1 * ν₁ z + P.2 * ν₂ z) * hilbertHSmooth (s P n) z)
    {P₀ : ℂ × ℂ} (hP₀ : P₀ ∈ W) :
    ∃ δ > 0, ball P₀ δ ⊆ W ∧ (∀ P ∈ ball P₀ δ, ContDiff ℝ 3 (fun z => ∑' n, cauchyT (s P n) z)) ∧
      ∀ j ≤ 3, ContinuousOn (fun q : (ℂ × ℂ) × ℂ => iteratedFDeriv ℝ j (fun z => ∑' n, cauchyT (s q.1 n) z) q.2)
        (ball P₀ δ ×ˢ univ) := by
  have S1 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ν₁ ∧ HasCompactSupport ν₁ := ⟨h₁, hc₁⟩
  have S2 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ν₂ ∧ HasCompactSupport ν₂ := ⟨h₂, hc₂⟩
  have SP : ∀ P : ℂ × ℂ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z => P.1 * ν₁ z + P.2 * ν₂ z) ∧
      HasCompactSupport (fun z => P.1 * ν₁ z + P.2 * ν₂ z) := fun P => wr_lin_sc h₁ hc₁ h₂ hc₂ P.1 P.2
  have hsc : ∀ P n, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (s P n) ∧ HasCompactSupport (s P n) := fun P n =>
    wr_iter_smooth (SP P).1 (SP P).2 (hs0 P) (hs P) n
  obtain ⟨k₀, hk₀1, hk₀⟩ := hWk P₀ hP₀
  have hk₀0 : 0 ≤ k₀ := (norm_nonneg _).trans (hk₀ 0)
  obtain ⟨M₁, hM₁0, hM₁⟩ := wr_sc_bound S1
  obtain ⟨M₂, hM₂0, hM₂⟩ := wr_sc_bound S2
  obtain ⟨δ₁, hδ₁, hball⟩ := Metric.isOpen_iff.1 hW P₀ hP₀
  obtain ⟨δ, hδ, hδ1, hδ2⟩ : ∃ δ : ℝ, 0 < δ ∧ δ ≤ δ₁ ∧ δ * (M₁ + M₂ + 1) ≤ (1 - k₀) / 2 := by
    refine ⟨min δ₁ ((1 - k₀) / (2 * (M₁ + M₂ + 1))), lt_min hδ₁ (div_pos (by linarith) (by positivity)),
      min_le_left _ _, ?_⟩
    have h := min_le_right δ₁ ((1 - k₀) / (2 * (M₁ + M₂ + 1)))
    rw [le_div_iff₀ (by positivity)] at h
    linarith
  obtain ⟨k', hk'def⟩ : ∃ k' : ℝ, k' = (k₀ + 1) / 2 := ⟨_, rfl⟩
  have hk'1 : k' < 1 := by rw [hk'def]; linarith
  have hk'0 : 0 ≤ k' := by rw [hk'def]; positivity
  have hcomp : ∀ P ∈ ball P₀ δ, ‖P.1 - P₀.1‖ < δ ∧ ‖P.2 - P₀.2‖ < δ := by
    intro P hP
    rw [mem_ball, Prod.dist_eq] at hP
    have h1 : dist P.1 P₀.1 < δ := (le_max_left _ _).trans_lt hP
    have h2 : dist P.2 P₀.2 < δ := (le_max_right _ _).trans_lt hP
    rw [dist_eq_norm] at h1 h2
    exact ⟨h1, h2⟩
  have hνP : ∀ P ∈ ball P₀ δ, ∀ z, ‖P.1 * ν₁ z + P.2 * ν₂ z‖ ≤ k' := by
    intro P hP z
    obtain ⟨h1, h2⟩ := hcomp P hP
    have e : P.1 * ν₁ z + P.2 * ν₂ z =
        (P₀.1 * ν₁ z + P₀.2 * ν₂ z) + ((P.1 - P₀.1) * ν₁ z + (P.2 - P₀.2) * ν₂ z) := by ring
    rw [e]
    have t1 := norm_add_le (P₀.1 * ν₁ z + P₀.2 * ν₂ z) ((P.1 - P₀.1) * ν₁ z + (P.2 - P₀.2) * ν₂ z)
    have t2 := norm_add_le ((P.1 - P₀.1) * ν₁ z) ((P.2 - P₀.2) * ν₂ z)
    rw [norm_mul, norm_mul] at t2
    have t3 : ‖P.1 - P₀.1‖ * ‖ν₁ z‖ ≤ δ * M₁ := mul_le_mul h1.le (hM₁ z) (norm_nonneg _) hδ.le
    have t4 : ‖P.2 - P₀.2‖ * ‖ν₂ z‖ ≤ δ * M₂ := mul_le_mul h2.le (hM₂ z) (norm_nonneg _) hδ.le
    have t5 := hk₀ z
    have t6 : δ * M₁ + δ * M₂ ≤ δ * (M₁ + M₂ + 1) := by nlinarith
    rw [hk'def]
    linarith
  obtain ⟨R, hRdef⟩ : ∃ R : ℝ, R = ‖P₀.1‖ + ‖P₀.2‖ + δ := ⟨_, rfl⟩
  have hR0 : 0 ≤ R := by rw [hRdef]; positivity
  have hR : ∀ P ∈ ball P₀ δ, ‖P.1‖ ≤ R ∧ ‖P.2‖ ≤ R := by
    intro P hP
    obtain ⟨h1, h2⟩ := hcomp P hP
    have e1 : P.1 = P₀.1 + (P.1 - P₀.1) := by ring
    have e2 : P.2 = P₀.2 + (P.2 - P₀.2) := by ring
    have n1 := norm_add_le P₀.1 (P.1 - P₀.1)
    have n2 := norm_add_le P₀.2 (P.2 - P₀.2)
    rw [← e1] at n1
    rw [← e2] at n2
    have := norm_nonneg P₀.1
    have := norm_nonneg P₀.2
    rw [hRdef]
    constructor <;> linarith
  obtain ⟨p, hp2, -, hkp⟩ := eq12_1_exists_exponent hk'1 (p₁ := 3) (by norm_num)
  have hp1 : 1 < p := by linarith
  have hΛ := hilbertNorm_nonneg p
  obtain ⟨ρ, hρdef⟩ : ∃ ρ : ℝ, ρ = (k' * hilbertNorm p + 1) / 2 := ⟨_, rfl⟩
  have hρ : k' * hilbertNorm p < ρ := by rw [hρdef]; linarith
  have hρ1 : ρ < 1 := by rw [hρdef]; linarith
  have hρ0 : 0 ≤ ρ := (mul_nonneg hk'0 hΛ).trans hρ.le
  obtain ⟨β₁, hβ₁0, hβ₁⟩ := wr_word_bounds h₁ hc₁ p
  obtain ⟨β₂, hβ₂0, hβ₂⟩ := wr_word_bounds h₂ hc₂ p
  obtain ⟨B, hBdef⟩ : ∃ B : ℝ, B = R * (β₁ + β₂) := ⟨_, rfl⟩
  have hB0 : 0 ≤ B := by rw [hBdef]; positivity
  obtain ⟨Γ, hΓdef⟩ : ∃ Γ : ℝ, Γ = 7 * B * hilbertNorm p / (ρ - k' * hilbertNorm p) := ⟨_, rfl⟩
  have hΓ0 : 0 ≤ Γ := by rw [hΓdef]; exact div_nonneg (by positivity) (by linarith)
  obtain ⟨E, hEdef⟩ : ∃ E : ℝ, E = B * (1 + Γ) * (1 + Γ) * (1 + Γ) := ⟨_, rfl⟩
  have hE0 : 0 ≤ E := by rw [hEdef]; positivity
  have hwP : ∀ P ∈ ball P₀ δ, ∀ a b e : ℂ, ‖a‖ ≤ 1 → ‖b‖ ≤ 1 → ‖e‖ ≤ 1 →
      (∀ z, ‖fderiv ℝ (fun z => P.1 * ν₁ z + P.2 * ν₂ z) z a‖ ≤ B ∧
        ‖fderiv ℝ (fun z => fderiv ℝ (fun z => P.1 * ν₁ z + P.2 * ν₂ z) z b) z a‖ ≤ B ∧
        ‖fderiv ℝ (fun z => fderiv ℝ (fun z => fderiv ℝ (fun z => P.1 * ν₁ z + P.2 * ν₂ z) z e) z b) z a‖ ≤ B) ∧
      (eLpNorm (fun z => P.1 * ν₁ z + P.2 * ν₂ z) (ENNReal.ofReal p)).toReal ≤ B ∧
      (eLpNorm (fun z => fderiv ℝ (fun z => P.1 * ν₁ z + P.2 * ν₂ z) z a) (ENNReal.ofReal p)).toReal ≤ B ∧
      (eLpNorm (fun z => fderiv ℝ (fun z => fderiv ℝ (fun z => P.1 * ν₁ z + P.2 * ν₂ z) z b) z a)
        (ENNReal.ofReal p)).toReal ≤ B ∧
      (eLpNorm (fun z => fderiv ℝ (fun z => fderiv ℝ (fun z => fderiv ℝ (fun z => P.1 * ν₁ z + P.2 * ν₂ z) z e) z b) z a)
        (ENNReal.ofReal p)).toReal ≤ B := by
    intro P hP
    rw [hBdef]
    exact wr_lin_bounds h₁ hc₁ h₂ hc₂ hp1.le hβ₁ hβ₂ (hR P hP).1 (hR P hP).2
  have hΓ : 7 * B * hilbertNorm p / (ρ - k' * hilbertNorm p) ≤ Γ := hΓdef.ge
  have hlev : ∀ P ∈ ball P₀ δ, ∀ a b c : ℂ, ‖a‖ ≤ 1 → ‖b‖ ≤ 1 → ‖c‖ ≤ 1 → ∀ n,
      (eLpNorm (s P n) (ENNReal.ofReal p)).toReal ≤ E * ρ ^ n ∧
      (eLpNorm (fun z => fderiv ℝ (s P n) z a) (ENNReal.ofReal p)).toReal ≤ E * ρ ^ n ∧
      (eLpNorm (fun z => fderiv ℝ (fun z => fderiv ℝ (s P n) z b) z a) (ENNReal.ofReal p)).toReal ≤ E * ρ ^ n ∧
      (eLpNorm (fun z => fderiv ℝ (fun z => fderiv ℝ (fun z => fderiv ℝ (s P n) z c) z b) z a)
        (ENNReal.ofReal p)).toReal ≤ E * ρ ^ n := by
    intro P hP a b c ha hb hc n
    rw [hEdef]
    exact wr_all_levels hp1 (SP P).1 (SP P).2 hk'0 (hνP P hP) hρ hB0 hB0 hΓ hΓ0 (hwP P hP) (hs0 P) (hs P)
      ha hb hc n
  -- supports
  have hK : IsCompact (tsupport ν₁ ∪ tsupport ν₂) := hc₁.isCompact.union hc₂.isCompact
  obtain ⟨r, hr⟩ := hK.isBounded.subset_closedBall (0 : ℂ)
  obtain ⟨R₀, hR₀def⟩ : ∃ R₀ : ℝ, R₀ = max r 1 := ⟨_, rfl⟩
  have hR₀ : 0 < R₀ := by rw [hR₀def]; exact lt_of_lt_of_le one_pos (le_max_right _ _)
  have hU : IsOpen (tsupport ν₁ ∪ tsupport ν₂)ᶜ := ((isClosed_tsupport _).union (isClosed_tsupport _)).isOpen_compl
  have hout : ∀ y : ℂ, R₀ < ‖y‖ → y ∈ (tsupport ν₁ ∪ tsupport ν₂)ᶜ := by
    intro y hy hyK
    have h := hr hyK
    rw [mem_closedBall_zero_iff] at h
    have : r ≤ R₀ := by rw [hR₀def]; exact le_max_left _ _
    linarith
  have hνz : ∀ P : ℂ × ℂ, ∀ y ∈ (tsupport ν₁ ∪ tsupport ν₂)ᶜ, P.1 * ν₁ y + P.2 * ν₂ y = 0 := by
    intro P y hy
    have h1 : ν₁ y = 0 := image_eq_zero_of_notMem_tsupport (fun h => hy (Or.inl h))
    have h2 : ν₂ y = 0 := image_eq_zero_of_notMem_tsupport (fun h => hy (Or.inr h))
    rw [h1, h2]; ring
  have hz : ∀ P n, ∀ y ∈ (tsupport ν₁ ∪ tsupport ν₂)ᶜ, s P n y = 0 := by
    intro P n
    induction n with
    | zero =>
      intro y hy
      have e := congrFun (hs0 P) y
      beta_reduce at e
      rw [e]; exact hνz P y hy
    | succ n ih =>
      intro y hy
      have e := congrFun (hs P n) y
      beta_reduce at e
      rw [e, hνz P y hy, zero_mul]
  have hz1 : ∀ P n a, ∀ y ∈ (tsupport ν₁ ∪ tsupport ν₂)ᶜ, fderiv ℝ (s P n) y a = 0 :=
    fun P n a => wr_D_zero_on hU (hz P n) a
  have hz2 : ∀ P n a b, ∀ y ∈ (tsupport ν₁ ∪ tsupport ν₂)ᶜ,
      fderiv ℝ (fun z => fderiv ℝ (s P n) z b) y a = 0 :=
    fun P n a b => wr_D_zero_on hU (hz1 P n b) a
  have hz3 : ∀ P n a b c, ∀ y ∈ (tsupport ν₁ ∪ tsupport ν₂)ᶜ,
      fderiv ℝ (fun z => fderiv ℝ (fun z => fderiv ℝ (s P n) z c) z b) y a = 0 :=
    fun P n a b c => wr_D_zero_on hU (hz2 P n b c) a
  obtain ⟨M, hM⟩ := lemma11_1 hp2 hR₀
  have hM'0 : 0 ≤ max M 0 := le_max_right _ _
  have hTb : ∀ ω : ℂ → ℂ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ω → HasCompactSupport ω →
      (∀ y ∈ (tsupport ν₁ ∪ tsupport ν₂)ᶜ, ω y = 0) → ∀ z,
      ‖cauchyT ω z‖ ≤ max M 0 * (eLpNorm ω (ENNReal.ofReal p)).toReal := by
    intro ω hω hωc hωU z
    have h := hM ω (wr_memLp hω hωc p) (fun y hy => hωU y (hout y hy)) z
    exact h.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) ENNReal.toReal_nonneg)
  have hfin : ∀ {N : ℝ} (n : ℕ), N ≤ E * ρ ^ n → max M 0 * N ≤ max M 0 * E * ρ ^ n := by
    intro N n hN
    have := mul_le_mul_of_nonneg_left hN hM'0
    linarith [this, show max M 0 * (E * ρ ^ n) = max M 0 * E * ρ ^ n by ring]
  have hT1 : ∀ P n a, (fun z => fderiv ℝ (cauchyT (s P n)) z a) = cauchyT (fun z => fderiv ℝ (s P n) z a) :=
    fun P n a => wr_D_cauchyT (hsc P n).1 (hsc P n).2 a
  have hT2 : ∀ P n a b, (fun z => fderiv ℝ (fun y => fderiv ℝ (cauchyT (s P n)) y b) z a) =
      cauchyT (fun z => fderiv ℝ (fun z => fderiv ℝ (s P n) z b) z a) := fun P n a b =>
    (congrArg (fun f : ℂ → ℂ => fun z => fderiv ℝ f z a) (hT1 P n b)).trans
      (wr_D_cauchyT (wr_D_sc (hsc P n) b).1 (wr_D_sc (hsc P n) b).2 a)
  have hT3 : ∀ P n a b c, (fun z => fderiv ℝ (fun y => fderiv ℝ (fun w => fderiv ℝ (cauchyT (s P n)) w c) y b) z a) =
      cauchyT (fun z => fderiv ℝ (fun z => fderiv ℝ (fun z => fderiv ℝ (s P n) z c) z b) z a) := fun P n a b c =>
    (congrArg (fun f : ℂ → ℂ => fun z => fderiv ℝ f z a) (hT2 P n b c)).trans
      (wr_D_cauchyT (wr_D_sc (wr_D_sc (hsc P n) c) b).1 (wr_D_sc (wr_D_sc (hsc P n) c) b).2 a)
  have hu : Summable (fun n : ℕ => max M 0 * E * ρ ^ n) :=
    (summable_geometric_of_lt_one hρ0 hρ1).mul_left (max M 0 * E)
  have one1 : ‖(1 : ℂ)‖ ≤ 1 := by simp
  obtain ⟨hcd, hcont⟩ := wr_tsum_contDiff (X := ℂ × ℂ) (S := ball P₀ δ) (g := fun P n => cauchyT (s P n))
    (fun P n => wr_cauchyT_contDiff_top (hsc P n).1 (hsc P n).2) hu
    (fun P hP n z => (hTb _ (hsc P n).1 (hsc P n).2 (hz P n) z).trans
      (hfin n (hlev P hP 1 1 1 one1 one1 one1 n).1))
    (fun P hP n z a ha => by
      rw [show fderiv ℝ (cauchyT (s P n)) z a = cauchyT (fun z => fderiv ℝ (s P n) z a) z from congrFun (hT1 P n a) z]
      exact (hTb _ (wr_D_sc (hsc P n) a).1 (wr_D_sc (hsc P n) a).2 (hz1 P n a) z).trans
        (hfin n (hlev P hP a 1 1 ha one1 one1 n).2.1))
    (fun P hP n z a b ha hb => by
      rw [show fderiv ℝ (fun y => fderiv ℝ (cauchyT (s P n)) y b) z a =
          cauchyT (fun z => fderiv ℝ (fun z => fderiv ℝ (s P n) z b) z a) z from congrFun (hT2 P n a b) z]
      exact (hTb _ (wr_D_sc (wr_D_sc (hsc P n) b) a).1 (wr_D_sc (wr_D_sc (hsc P n) b) a).2 (hz2 P n a b) z).trans
        (hfin n (hlev P hP a b 1 ha hb one1 n).2.2.1))
    (fun P hP n z a b c ha hb hc => by
      rw [show fderiv ℝ (fun y => fderiv ℝ (fun w => fderiv ℝ (cauchyT (s P n)) w c) y b) z a =
          cauchyT (fun z => fderiv ℝ (fun z => fderiv ℝ (fun z => fderiv ℝ (s P n) z c) z b) z a) z from
        congrFun (hT3 P n a b c) z]
      exact (hTb _ (wr_D_sc (wr_D_sc (wr_D_sc (hsc P n) c) b) a).1
        (wr_D_sc (wr_D_sc (wr_D_sc (hsc P n) c) b) a).2 (hz3 P n a b c) z).trans
        (hfin n (hlev P hP a b c ha hb hc n).2.2.2))
    (fun n j _ => (wr_iter_term_cont h₁ hc₁ h₂ hc₂ hs0 hs n j).continuousOn)
  exact ⟨δ, hδ, (ball_subset_ball hδ1).trans hball, hcd, hcont⟩

/-- (A3) `[W1]` **Smooth compactly supported two-parameter family.** On an open parameter set `W` where the
coefficient has sup norm `< 1`, every normalized solution is `C³` in `z`, and its `z`-derivatives of order `≤ 3`
are jointly continuous in `(P, z)`. -/
theorem wr_smooth_family {ν₁ ν₂ : ℂ → ℂ} (h₁ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ν₁) (hc₁ : HasCompactSupport ν₁)
    (h₂ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ν₂) (hc₂ : HasCompactSupport ν₂) {W : Set (ℂ × ℂ)} (hW : IsOpen W)
    (hWk : ∀ P ∈ W, ∃ k < 1, ∀ z, ‖P.1 * ν₁ z + P.2 * ν₂ z‖ ≤ k) :
    (∀ P ∈ W, ContDiff ℝ 3 (normalizedSolution fun u => P.1 * ν₁ u + P.2 * ν₂ u)) ∧
      ∀ j ≤ 3, ContinuousOn (fun q : (ℂ × ℂ) × ℂ =>
        iteratedFDeriv ℝ j (normalizedSolution fun u => q.1.1 * ν₁ u + q.1.2 * ν₂ u) q.2) (W ×ˢ univ) := by
  obtain ⟨s, hs0, hs⟩ : ∃ s : ℂ × ℂ → ℕ → ℂ → ℂ, (∀ P, s P 0 = fun z => P.1 * ν₁ z + P.2 * ν₂ z) ∧
      ∀ P n, s P (n + 1) = fun z => (P.1 * ν₁ z + P.2 * ν₂ z) * hilbertHSmooth (s P n) z :=
    ⟨fun P n => Nat.rec (motive := fun _ => ℂ → ℂ) (fun z => P.1 * ν₁ z + P.2 * ν₂ z)
      (fun _ g => fun z => (P.1 * ν₁ z + P.2 * ν₂ z) * hilbertHSmooth g z) n, fun _ => rfl, fun _ _ => rfl⟩
  have SP : ∀ P : ℂ × ℂ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z => P.1 * ν₁ z + P.2 * ν₂ z) ∧
      HasCompactSupport (fun z => P.1 * ν₁ z + P.2 * ν₂ z) := fun P => wr_lin_sc h₁ hc₁ h₂ hc₂ P.1 P.2
  have hrep : ∀ P ∈ W, (∀ z, Summable fun n => cauchyT (s P n) z) ∧
      (1 + ∑' n, cauchyT (s P n) 1) - ∑' n, cauchyT (s P n) 0 ≠ 0 ∧
      (normalizedSolution fun u => P.1 * ν₁ u + P.2 * ν₂ u) = fun z =>
        ((z + ∑' n, cauchyT (s P n) z) - ∑' n, cauchyT (s P n) 0) /
          ((1 + ∑' n, cauchyT (s P n) 1) - ∑' n, cauchyT (s P n) 0) := by
    intro P hP
    obtain ⟨k, hk1, hk⟩ := hWk P hP
    exact wr_ns_series (SP P).1 (SP P).2 ((norm_nonneg _).trans (hk 0)) hk1 hk (hs0 P) (hs P)
  refine ⟨fun P hP => ?_, fun j hj => ?_⟩
  · obtain ⟨δ, hδ, -, hcd, -⟩ := wr_A3_local h₁ hc₁ h₂ hc₂ hW hWk hs0 hs hP
    rw [(hrep P hP).2.2]
    exact ((contDiff_id.add (hcd P (mem_ball_self hδ))).sub contDiff_const).div_const _
  · intro q hq
    obtain ⟨δ, hδ, hsub, hcd, hcont⟩ := wr_A3_local h₁ hc₁ h₂ hc₂ hW hWk hs0 hs hq.1
    have hFv : ContinuousOn (fun q : (ℂ × ℂ) × ℂ => ∑' n, cauchyT (s q.1 n) q.2) (ball q.1 δ ×ˢ univ) := by
      refine ((continuousMultilinearCurryFin0 ℝ ℂ ℂ).continuous.comp_continuousOn (hcont 0 (by norm_num))).congr ?_
      intro q' _
      simp [iteratedFDeriv_zero_eq_comp]
    have hpt : ∀ w : ℂ, ContinuousOn (fun P : ℂ × ℂ => ∑' n, cauchyT (s P n) w) (ball q.1 δ) := fun w =>
      hFv.comp (continuous_id.prodMk continuous_const).continuousOn (fun P hP => ⟨hP, mem_univ _⟩)
    have hDc : ContinuousOn (fun P : ℂ × ℂ => (1 + ∑' n, cauchyT (s P n) 1) - ∑' n, cauchyT (s P n) 0)
        (ball q.1 δ) := (continuousOn_const.add (hpt 1)).sub (hpt 0)
    have haff := wr_affine_iter_cont (S := ball q.1 δ) (F := fun P z => ∑' n, cauchyT (s P n) z)
      (c0 := fun P => ∑' n, cauchyT (s P n) 0) (D := fun P => (1 + ∑' n, cauchyT (s P n) 1) - ∑' n, cauchyT (s P n) 0)
      hcd hcont (hpt 0) hDc (fun P hP => (hrep P (hsub hP)).2.1) j hj
    have hnhds : ball q.1 δ ×ˢ (univ : Set ℂ) ∈ 𝓝 q :=
      (isOpen_ball.prod isOpen_univ).mem_nhds ⟨mem_ball_self hδ, mem_univ _⟩
    refine ((haff.congr ?_).continuousAt hnhds).continuousWithinAt
    intro q' hq'
    show iteratedFDeriv ℝ j (normalizedSolution fun u => q'.1.1 * ν₁ u + q'.1.2 * ν₂ u) q'.2 = _
    rw [(hrep q'.1 (hsub hq'.1)).2.2]



/-! ## Part B — analysis tools `[W4]` -/

/-- (B1) `[W4]` Differentiation under the integral sign, `C^n` version: a finite-measure family that is `C^n` on
an open set, with `j`-th derivatives (`j ≤ n`) bounded on compacts uniformly in the parameter and measurable in the
parameter, has a `C^n` integral. -/
theorem wr_contDiffOn_integral {α : Type*} [MeasurableSpace α] {ρ : Measure α} [IsFiniteMeasure ρ]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] {U : Set E} (hU : IsOpen U)
    {F : α → E → ℂ} {n : ℕ} (hF : ∀ x, ContDiffOn ℝ n (F x) U)
    (hmeas : ∀ j ≤ n, ∀ y ∈ U, AEStronglyMeasurable (fun x => iteratedFDeriv ℝ j (F x) y) ρ)
    (hbd : ∀ j ≤ n, ∀ K ⊆ U, IsCompact K → ∃ C, ∀ x, ∀ y ∈ K, ‖iteratedFDeriv ℝ j (F x) y‖ ≤ C) :
    ContDiffOn ℝ n (fun y => ∫ x, F x y ∂ρ) U := by
  have hUD : UniqueDiffOn ℝ U := hU.uniqueDiffOn
  -- uniform bounds on a closed ball around each point
  have hloc : ∀ j ≤ n, ∀ y ∈ U, ∃ ε > 0, closedBall y ε ⊆ U ∧
      ∃ C, ∀ x, ∀ z ∈ closedBall y ε, ‖iteratedFDeriv ℝ j (F x) z‖ ≤ C := by
    intro j hj y hy
    obtain ⟨ε, hε, hsub⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hU.mem_nhds hy)
    obtain ⟨C, hC⟩ := hbd j hj _ hsub (isCompact_closedBall y ε)
    exact ⟨ε, hε, hsub, C, hC⟩
  -- regularity of each integrand's derivatives
  have hdiff : ∀ j < n, ∀ x, ∀ z ∈ U,
      HasFDerivAt (iteratedFDeriv ℝ j (F x)) (fderiv ℝ (iteratedFDeriv ℝ j (F x)) z) z := by
    intro j hj x z hz
    have h1 := (hF x).differentiableOn_iteratedFDerivWithin (m := j) (by exact_mod_cast hj) hUD
    have h2 : DifferentiableOn ℝ (iteratedFDeriv ℝ j (F x)) U :=
      h1.congr fun w hw => (iteratedFDerivWithin_of_isOpen j hU hw).symm
    exact ((h2 z hz).differentiableAt (hU.mem_nhds hz)).hasFDerivAt
  have hcont : ∀ j ≤ n, ∀ x, ∀ z ∈ U, ContinuousAt (iteratedFDeriv ℝ j (F x)) z := by
    intro j hj x z hz
    have h1 := (hF x).continuousOn_iteratedFDerivWithin (m := j) (by exact_mod_cast hj) hUD
    have h2 : ContinuousOn (iteratedFDeriv ℝ j (F x)) U :=
      h1.congr fun w hw => (iteratedFDerivWithin_of_isOpen j hU hw).symm
    exact h2.continuousAt (hU.mem_nhds hz)
  have hint : ∀ j ≤ n, ∀ y ∈ U, Integrable (fun x => iteratedFDeriv ℝ j (F x) y) ρ := by
    intro j hj y hy
    obtain ⟨C, hC⟩ := hbd j hj {y} (singleton_subset_iff.mpr hy) isCompact_singleton
    exact Integrable.of_bound (hmeas j hj y hy) C (ae_of_all _ fun x => hC x y rfl)
  have hmeas' : ∀ j < n, ∀ y ∈ U,
      AEStronglyMeasurable (fun x => fderiv ℝ (iteratedFDeriv ℝ j (F x)) y) ρ := by
    intro j hj y hy
    let L := continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (j + 1) => E) ℂ
    have e : (fun x => fderiv ℝ (iteratedFDeriv ℝ j (F x)) y) =
        fun x => L (iteratedFDeriv ℝ (j + 1) (F x) y) := by
      funext x
      rw [iteratedFDeriv_succ_eq_comp_left, Function.comp_apply, LinearIsometryEquiv.apply_symm_apply]
    rw [e]
    exact L.continuous.comp_aestronglyMeasurable (hmeas (j + 1) (by omega) y hy)
  -- differentiation under the integral sign, one order at a time
  have hD : ∀ j < n, ∀ y ∈ U, HasFDerivAt (fun y => ∫ x, iteratedFDeriv ℝ j (F x) y ∂ρ)
      (∫ x, fderiv ℝ (iteratedFDeriv ℝ j (F x)) y ∂ρ) y := by
    intro j hj y hy
    obtain ⟨ε, hε, hsub, C, hC⟩ := hloc (j + 1) (by omega) y hy
    have hs : ball y ε ∈ 𝓝 y := ball_mem_nhds y hε
    refine hasFDerivAt_integral_of_dominated_of_fderiv_le (bound := fun _ => C)
      (F := fun z x => iteratedFDeriv ℝ j (F x) z) (F' := fun z x => fderiv ℝ (iteratedFDeriv ℝ j (F x)) z) hs ?_
      (hint j hj.le y hy) (hmeas' j hj y hy) ?_ (integrable_const C) ?_
    · filter_upwards [hs] with z hz using hmeas j hj.le z (hsub (ball_subset_closedBall hz))
    · exact ae_of_all _ fun x z hz => by
        rw [norm_fderiv_iteratedFDeriv]
        exact hC x z (ball_subset_closedBall hz)
    · exact ae_of_all _ fun x z hz => hdiff j hj x z (hsub (ball_subset_closedBall hz))
  -- the iterated derivatives of the integral are the integrals of the iterated derivatives
  have hEq : ∀ m ≤ n, EqOn (iteratedFDerivWithin ℝ m (fun y => ∫ x, F x y ∂ρ) U)
      (fun y => ∫ x, iteratedFDeriv ℝ m (F x) y ∂ρ) U := by
    intro m
    induction m with
    | zero =>
      intro _ y _
      rw [iteratedFDerivWithin_zero_eq_comp]
      simp only [Function.comp_apply, iteratedFDeriv_zero_eq_comp]
      exact ((continuousMultilinearCurryFin0 ℝ E ℂ).symm.toLinearIsometry.integral_comp_comm _).symm
    | succ m ih =>
      intro hm y hy
      rw [iteratedFDerivWithin_succ_eq_comp_left]
      simp only [Function.comp_apply, iteratedFDeriv_succ_eq_comp_left]
      have hfd : fderivWithin ℝ (iteratedFDerivWithin ℝ m (fun y => ∫ x, F x y ∂ρ) U) U y =
          ∫ x, fderiv ℝ (iteratedFDeriv ℝ m (F x)) y ∂ρ := by
        rw [fderivWithin_of_isOpen hU hy]
        have hev : iteratedFDerivWithin ℝ m (fun y => ∫ x, F x y ∂ρ) U =ᶠ[𝓝 y]
            fun y => ∫ x, iteratedFDeriv ℝ m (F x) y ∂ρ :=
          Filter.eventually_of_mem (hU.mem_nhds hy) (ih (by omega))
        rw [hev.fderiv_eq]
        exact (hD m (by omega) y hy).fderiv
      rw [hfd]
      exact (LinearIsometry.integral_comp_comm
        (X := α) (μ := ρ) (𝕜 := ℝ) (E := E →L[ℝ] ContinuousMultilinearMap ℝ (fun _ : Fin m => E) ℂ)
        (F := ContinuousMultilinearMap ℝ (fun _ : Fin (m + 1) => E) ℂ)
        (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (m + 1) => E) ℂ).symm.toLinearIsometry _).symm
  have key := contDiffOn_of_continuousOn_differentiableOn (𝕜 := ℝ) (f := fun y => ∫ x, F x y ∂ρ) (s := U)
    (n := (n : ℕ∞)) ?_ ?_
  · exact_mod_cast key
  · intro m hm
    have hm' : m ≤ n := by exact_mod_cast hm
    refine ContinuousOn.congr ?_ (hEq m hm')
    intro y hy
    apply ContinuousAt.continuousWithinAt
    obtain ⟨ε, hε, hsub, C, hC⟩ := hloc m hm' y hy
    have hs : closedBall y ε ∈ 𝓝 y := closedBall_mem_nhds y hε
    exact continuousAt_of_dominated (bound := fun _ => C)
      (by filter_upwards [hs] with z hz using hmeas m hm' z (hsub hz))
      (by filter_upwards [hs] with z hz using ae_of_all _ fun x => hC x z hz)
      (integrable_const C) (ae_of_all _ fun x => hcont m hm' x y hy)
  · intro m hm
    have hm' : m < n := by exact_mod_cast hm
    refine DifferentiableOn.congr ?_ (hEq m hm'.le)
    intro y hy
    exact (hD m hm' y hy).differentiableAt.differentiableWithinAt

/-- (B2) `[W4]` Two-variable Cauchy formula on a closed bidisc, from **separate** holomorphy and joint
continuity (no Osgood or Hartogs needed). -/
theorem wr_cauchy_bidisc {f : ℂ × ℂ → ℂ} {c : ℂ × ℂ} {R₁ R₂ : ℝ} (hR₁ : 0 < R₁) (hR₂ : 0 < R₂)
    (hcont : ContinuousOn f (closedBall c.1 R₁ ×ˢ closedBall c.2 R₂))
    (h₁ : ∀ b ∈ closedBall c.2 R₂, DifferentiableOn ℂ (fun a => f (a, b)) (ball c.1 R₁))
    (h₂ : ∀ a ∈ closedBall c.1 R₁, DifferentiableOn ℂ (fun b => f (a, b)) (ball c.2 R₂))
    {p : ℂ × ℂ} (hp : p ∈ ball c.1 R₁ ×ˢ ball c.2 R₂) :
    f p = ((2 * π * I)⁻¹) ^ 2 * ∮ a in C(c.1, R₁), ∮ b in C(c.2, R₂), f (a, b) / ((a - p.1) * (b - p.2)) := by
  have _hR₂ := hR₂
  obtain ⟨hp1, hp2⟩ := hp
  -- the inner (second-variable) Cauchy formula, for every `a` in the closed disc
  have hin : ∀ a ∈ closedBall c.1 R₁,
      f (a, p.2) = (2 * π * I)⁻¹ * ∮ b in C(c.2, R₂), (b - p.2)⁻¹ * f (a, b) := by
    intro a ha
    have hc : ContinuousOn (fun b => f (a, b)) (closedBall c.2 R₂) :=
      hcont.comp (Continuous.continuousOn (by fun_prop)) fun b hb => ⟨ha, hb⟩
    have hd : ∀ x ∈ ball c.2 R₂ \ (∅ : Set ℂ), DifferentiableAt ℂ (fun b => f (a, b)) x :=
      fun x hx => (h₂ a ha x hx.1).differentiableAt (isOpen_ball.mem_nhds hx.1)
    have h := two_pi_I_inv_smul_circleIntegral_sub_inv_smul_of_differentiable_on_off_countable
      Set.countable_empty hp2 hc hd
    simpa only [smul_eq_mul] using h.symm
  -- the outer (first-variable) Cauchy formula at `b = p.2`
  have hout : f p = (2 * π * I)⁻¹ * ∮ a in C(c.1, R₁), (a - p.1)⁻¹ * f (a, p.2) := by
    have hb : p.2 ∈ closedBall c.2 R₂ := ball_subset_closedBall hp2
    have hc : ContinuousOn (fun a => f (a, p.2)) (closedBall c.1 R₁) :=
      hcont.comp (Continuous.continuousOn (by fun_prop)) fun a ha => ⟨ha, hb⟩
    have hd : ∀ x ∈ ball c.1 R₁ \ (∅ : Set ℂ), DifferentiableAt ℂ (fun a => f (a, p.2)) x :=
      fun x hx => (h₁ p.2 hb x hx.1).differentiableAt (isOpen_ball.mem_nhds hx.1)
    have h := two_pi_I_inv_smul_circleIntegral_sub_inv_smul_of_differentiable_on_off_countable
      Set.countable_empty hp1 hc hd
    calc f p = f (p.1, p.2) := rfl
      _ = _ := by simpa only [smul_eq_mul] using h.symm
  rw [hout]
  have hcongr : EqOn (fun a => (a - p.1)⁻¹ * f (a, p.2))
      (fun a => (2 * π * I)⁻¹ * ∮ b in C(c.2, R₂), f (a, b) / ((a - p.1) * (b - p.2))) (sphere c.1 R₁) := by
    intro a ha
    simp only
    rw [hin a (sphere_subset_closedBall ha)]
    have e : (∮ b in C(c.2, R₂), f (a, b) / ((a - p.1) * (b - p.2))) =
        (a - p.1)⁻¹ * ∮ b in C(c.2, R₂), (b - p.2)⁻¹ * f (a, b) := by
      rw [← smul_eq_mul ((a - p.1)⁻¹), ← circleIntegral.integral_smul]
      congr 1
      funext b
      rw [smul_eq_mul, div_eq_mul_inv, mul_inv]
      ring
    rw [e]
    ring
  rw [circleIntegral.integral_congr hR₁.le hcongr]
  have h3 := circleIntegral.integral_smul ((2 * π * I)⁻¹)
    (fun a => ∮ b in C(c.2, R₂), f (a, b) / ((a - p.1) * (b - p.2))) c.1 R₁
  simp only [smul_eq_mul] at h3
  rw [h3]
  ring


/-! ### Helpers for Part C (下属5) -/

/-- The linear part `v ↦ v₁m₁ + v₂m₂` is bounded by `(|k₁| + |k₂|)‖v‖`. -/
theorem wr_coeff_lin {m₁ m₂ : ℂ → ℂ} {k₁ k₂ : ℝ} (hm₁ : IsBeltramiCoeff m₁ univ k₁)
    (hm₂ : IsBeltramiCoeff m₂ univ k₂) (v : ℂ × ℂ) :
    IsBeltramiCoeff (fun u => v.1 * m₁ u + v.2 * m₂ u) univ ((|k₁| + |k₂|) * ‖v‖) := by
  refine ⟨(hm₁.1.const_mul v.1).add (hm₂.1.const_mul v.2), ?_⟩
  filter_upwards [hm₁.2, hm₂.2] with u h₁ h₂
  have hv1 : ‖v.1‖ ≤ ‖v‖ := norm_fst_le v
  have hv2 : ‖v.2‖ ≤ ‖v‖ := norm_snd_le v
  calc ‖v.1 * m₁ u + v.2 * m₂ u‖ ≤ ‖v.1‖ * ‖m₁ u‖ + ‖v.2‖ * ‖m₂ u‖ := by
        rw [← norm_mul, ← norm_mul]; exact norm_add_le _ _
    _ ≤ ‖v‖ * |k₁| + ‖v‖ * |k₂| :=
        add_le_add (mul_le_mul hv1 (h₁.trans (le_abs_self _)) (norm_nonneg _) (norm_nonneg _))
          (mul_le_mul hv2 (h₂.trans (le_abs_self _)) (norm_nonneg _) (norm_nonneg _))
    _ = (|k₁| + |k₂|) * ‖v‖ := by ring

theorem wr_coeff_nonneg {m : ℂ → ℂ} {k : ℝ} (hk : k < 1) (hm : IsBeltramiCoeff m univ k) :
    IsBeltramiCoeff m univ (max k 0) ∧ 0 ≤ max k 0 ∧ max k 0 < 1 :=
  ⟨⟨hm.1, hm.2.mono fun _ hu => hu.trans (le_max_left _ _)⟩, le_max_right _ _, max_lt hk one_pos⟩

/-- The normalized solution of a coefficient bounded by `k < 1` is `K`-qc for `K ≥ (1 + k)/(1 - k)`. -/
theorem wr_ns_qc {m : ℂ → ℂ} {k : ℝ} (hk0 : 0 ≤ k) (hk1 : k < 1) (hm : IsBeltramiCoeff m univ k) {K : ℝ}
    (hK : (1 + k) / (1 - k) ≤ K) : IsKQCNormalizedPlane (normalizedSolution m) K := by
  obtain ⟨f, hf, hfK, -⟩ := thm13_7_normalized_existence hk0 hk1 hm
  rw [QCV.qcv_ns_eq hk0 hk1 hm hf]
  exact ⟨hfK.mono hK, hf.2.1, hf.2.2.1, hf.2.2.2.1⟩

/-- Joint complex differentiability in `P = (a, b)` at a point where the coefficient is bounded by `k < 1`. -/
theorem wr_ns2_diffAt {m₁ m₂ : ℂ → ℂ} {k₁ k₂ : ℝ} (hm₁ : IsBeltramiCoeff m₁ univ k₁)
    (hm₂ : IsBeltramiCoeff m₂ univ k₂) {P₀ : ℂ × ℂ} {k : ℝ} (hk : k < 1)
    (hP₀ : IsBeltramiCoeff (fun u => P₀.1 * m₁ u + P₀.2 * m₂ u) univ k) (z : ℂ) :
    DifferentiableAt ℂ (fun p : ℂ × ℂ => normalizedSolution (fun u => p.1 * m₁ u + p.2 * m₂ u) z) P₀ := by
  obtain ⟨h0, hk0, hk1⟩ := wr_coeff_nonneg hk hP₀
  obtain ⟨L, hL, -⟩ := QCV.qcv_plane_two_param_general (by positivity) hk0 hk1 h0 (wr_coeff_lin hm₁ hm₂) z
  exact hL.differentiableAt

/-- Locally uniform bound `k < 1` near a parameter where the coefficient is bounded by `k₀ < 1`. -/
theorem wr_loc_unif {m₁ m₂ : ℂ → ℂ} {k₁ k₂ : ℝ} (hm₁ : IsBeltramiCoeff m₁ univ k₁)
    (hm₂ : IsBeltramiCoeff m₂ univ k₂) {P₀ : ℂ × ℂ} {k₀ : ℝ} (hk₀ : k₀ < 1)
    (h₀ : IsBeltramiCoeff (fun u => P₀.1 * m₁ u + P₀.2 * m₂ u) univ k₀) :
    ∃ δ > 0, ∃ k : ℝ, 0 ≤ k ∧ k < 1 ∧ ∀ P : ℂ × ℂ, dist P P₀ < δ →
      IsBeltramiCoeff (fun u => P.1 * m₁ u + P.2 * m₂ u) univ k := by
  obtain ⟨h0, hk0, hk1⟩ := wr_coeff_nonneg hk₀ h₀
  have hM : 0 < |k₁| + |k₂| + 1 := by positivity
  have hδ : 0 < (1 - max k₀ 0) / (2 * (|k₁| + |k₂| + 1)) := div_pos (by linarith) (by positivity)
  obtain ⟨δ, hδdef⟩ : ∃ δ : ℝ, δ = (1 - max k₀ 0) / (2 * (|k₁| + |k₂| + 1)) := ⟨_, rfl⟩
  rw [← hδdef] at hδ
  have hMδ : (|k₁| + |k₂| + 1) * δ = (1 - max k₀ 0) / 2 := by
    rw [hδdef, mul_div_assoc', mul_comm (2 : ℝ), mul_div_mul_left _ _ hM.ne']
  refine ⟨δ, hδ, max k₀ 0 + (|k₁| + |k₂|) * δ, add_nonneg hk0 (mul_nonneg (by positivity) hδ.le), ?_,
    fun P hP => ?_⟩
  · have : (|k₁| + |k₂|) * δ ≤ (|k₁| + |k₂| + 1) * δ := mul_le_mul_of_nonneg_right (by linarith) hδ.le
    linarith
  · have hT := wr_coeff_lin hm₁ hm₂ (P - P₀)
    refine ⟨(hm₁.1.const_mul P.1).add (hm₂.1.const_mul P.2), ?_⟩
    filter_upwards [h0.2, hT.2] with u h1 h2
    have he : P.1 * m₁ u + P.2 * m₂ u =
        (P₀.1 * m₁ u + P₀.2 * m₂ u) + ((P - P₀).1 * m₁ u + (P - P₀).2 * m₂ u) := by
      simp only [Prod.fst_sub, Prod.snd_sub]; ring
    rw [he]
    have hn : ‖P - P₀‖ ≤ δ := by rw [← dist_eq_norm]; exact hP.le
    calc _ ≤ _ := norm_add_le _ _
      _ ≤ max k₀ 0 + (|k₁| + |k₂|) * δ :=
          add_le_add h1 (h2.trans (mul_le_mul_of_nonneg_left hn (by positivity)))

/-- Locally uniform convergence of the normalized solutions along `Pₙ → P₀ ∈ W`. -/
theorem wr_ns2_luc {m₁ m₂ : ℂ → ℂ} {k₁ k₂ : ℝ} (hm₁ : IsBeltramiCoeff m₁ univ k₁)
    (hm₂ : IsBeltramiCoeff m₂ univ k₂) {W : Set (ℂ × ℂ)}
    (hWk : ∀ P ∈ W, ∃ k < 1, IsBeltramiCoeff (fun u => P.1 * m₁ u + P.2 * m₂ u) univ k)
    {P₀ : ℂ × ℂ} (hP₀ : P₀ ∈ W) {Ps : ℕ → ℂ × ℂ} (hlim : Tendsto Ps atTop (𝓝 P₀)) :
    TendstoLocallyUniformly (fun n => normalizedSolution (fun u => (Ps n).1 * m₁ u + (Ps n).2 * m₂ u))
      (normalizedSolution (fun u => P₀.1 * m₁ u + P₀.2 * m₂ u)) atTop := by
  obtain ⟨k₀, hk₀, h₀⟩ := hWk _ hP₀
  obtain ⟨δ, hδ, k, hk0, hk1, hP⟩ := wr_loc_unif hm₁ hm₂ hk₀ h₀
  have hpt : ∀ z, Tendsto (fun n => normalizedSolution (fun u => (Ps n).1 * m₁ u + (Ps n).2 * m₂ u) z) atTop
      (𝓝 (normalizedSolution (fun u => P₀.1 * m₁ u + P₀.2 * m₂ u) z)) := fun z =>
    (wr_ns2_diffAt hm₁ hm₂ hk₀ h₀ z).continuousAt.tendsto.comp hlim
  have hqc : ∀ᶠ n in atTop, IsKQCNormalizedPlane
      (normalizedSolution (fun u => (Ps n).1 * m₁ u + (Ps n).2 * m₂ u)) ((1 + k) / (1 - k)) := by
    filter_upwards [hlim.eventually (ball_mem_nhds P₀ hδ)] with n hn
    exact wr_ns_qc hk0 hk1 (hP _ hn) le_rfl
  rw [tendstoLocallyUniformly_iff_forall_isCompact]
  intro S hS
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  by_contra hcon
  rw [not_eventually] at hcon
  obtain ⟨N, hN⟩ := eventually_atTop.1 hqc
  obtain ⟨φ, hφ, hbad⟩ := extraction_of_frequently_atTop (hcon.and_eventually (eventually_ge_atTop N))
  have hK' : ∀ n, IsKQCNormalizedPlane
      (normalizedSolution (fun u => (Ps (φ n)).1 * m₁ u + (Ps (φ n)).2 * m₂ u)) ((1 + k) / (1 - k)) :=
    fun n => hN _ (hbad n).2
  obtain ⟨ψ, hψ, G, hG⟩ := UniversalTeichmuller.ut2_nf_extract hK'
  have hGeq : G = normalizedSolution (fun u => P₀.1 * m₁ u + P₀.2 * m₂ u) := by
    funext w
    exact tendsto_nhds_unique
      ((tendstoLocallyUniformly_iff_forall_isCompact.1 hG {w} isCompact_singleton).tendsto_at (mem_singleton w))
      ((hpt w).comp (hφ.tendsto_atTop.comp hψ.tendsto_atTop))
  rw [hGeq] at hG
  have hU := Metric.tendstoUniformlyOn_iff.1 (tendstoLocallyUniformly_iff_forall_isCompact.1 hG S hS) ε hε
  obtain ⟨n, hn⟩ := hU.exists
  exact (hbad (ψ n)).1 hn

/-! ## Part C — two-parameter normalized family: holomorphy, continuity, inverse `[W5]` -/

/-- (C1) `[W5]` Separate holomorphy in each parameter (via `thm13_8_ahlfors_bers_holomorphic`, locally uniform `k`). -/
theorem wr_ns2_holo {m₁ m₂ : ℂ → ℂ} {k₁ k₂ : ℝ} (hm₁ : IsBeltramiCoeff m₁ univ k₁) (hm₂ : IsBeltramiCoeff m₂ univ k₂)
    {W : Set (ℂ × ℂ)} (hW : IsOpen W)
    (hWk : ∀ P ∈ W, ∃ k < 1, IsBeltramiCoeff (fun u => P.1 * m₁ u + P.2 * m₂ u) univ k) (z : ℂ) :
    (∀ b : ℂ, DifferentiableOn ℂ (fun a => normalizedSolution (fun u => a * m₁ u + b * m₂ u) z) {a | (a, b) ∈ W}) ∧
      ∀ a : ℂ, DifferentiableOn ℂ (fun b => normalizedSolution (fun u => a * m₁ u + b * m₂ u) z) {b | (a, b) ∈ W} := by
  -- `hW` is not needed: the proof gives complex differentiability at every point of `W`
  -- (`qcv_plane_two_param_general`), not only on its interior.
  have _hW := hW
  refine ⟨fun b a ha => ?_, fun a b hb => ?_⟩
  · obtain ⟨k, hk, hP⟩ := hWk _ ha
    have hf : DifferentiableAt ℂ (fun t : ℂ => (t, b)) a := by fun_prop
    exact (DifferentiableAt.comp (g := fun p : ℂ × ℂ =>
      normalizedSolution (fun u => p.1 * m₁ u + p.2 * m₂ u) z) a (wr_ns2_diffAt hm₁ hm₂ hk hP z)
      hf).differentiableWithinAt
  · obtain ⟨k, hk, hP⟩ := hWk _ hb
    have hf : DifferentiableAt ℂ (fun t : ℂ => (a, t)) b := by fun_prop
    exact (DifferentiableAt.comp (g := fun p : ℂ × ℂ =>
      normalizedSolution (fun u => p.1 * m₁ u + p.2 * m₂ u) z) b (wr_ns2_diffAt hm₁ hm₂ hk hP z)
      hf).differentiableWithinAt

/-- (C2) `[W5]` Joint continuity in `(P, z)` (pointwise continuity plus normal families, as in `acc_WB_luc`). -/
theorem wr_ns2_cont {m₁ m₂ : ℂ → ℂ} {k₁ k₂ : ℝ} (hm₁ : IsBeltramiCoeff m₁ univ k₁) (hm₂ : IsBeltramiCoeff m₂ univ k₂)
    {W : Set (ℂ × ℂ)} (hW : IsOpen W)
    (hWk : ∀ P ∈ W, ∃ k < 1, IsBeltramiCoeff (fun u => P.1 * m₁ u + P.2 * m₂ u) univ k) :
    ContinuousOn (fun q : (ℂ × ℂ) × ℂ => normalizedSolution (fun u => q.1.1 * m₁ u + q.1.2 * m₂ u) q.2)
      (W ×ˢ univ) := by
  -- `hW` is not needed (continuity within `W ×ˢ univ` holds at every point of `W`).
  have _hW := hW
  rintro ⟨P₀, z₀⟩ ⟨hP₀, -⟩
  show Tendsto _ (𝓝[W ×ˢ univ] (P₀, z₀)) _
  rw [Filter.tendsto_iff_seq_tendsto]
  intro x hx
  have hx' := tendsto_nhdsWithin_iff.mp hx
  have h1 : Tendsto (fun n => (x n).1) atTop (𝓝 P₀) := (continuous_fst.tendsto _).comp hx'.1
  have h2 : Tendsto (fun n => (x n).2) atTop (𝓝 z₀) := (continuous_snd.tendsto _).comp hx'.1
  have hL := wr_ns2_luc hm₁ hm₂ hWk hP₀ h1
  obtain ⟨k₀, hk₀, h₀⟩ := hWk _ hP₀
  obtain ⟨h0, hk0, hk1⟩ := wr_coeff_nonneg hk₀ h₀
  have hc : Continuous (normalizedSolution (fun u => P₀.1 * m₁ u + P₀.2 * m₂ u)) :=
    continuousOn_univ.1 (wr_ns_qc hk0 hk1 h0 le_rfl).1.2.2.1.1
  exact hL.tendsto_comp hc.continuousAt h2

/-- `invFun` of a function realized by a homeomorphism is the inverse homeomorphism. -/
theorem wr_invFun_eq {f : ℂ → ℂ} {e : ℂ ≃ₜ ℂ} (he : ⇑e = f) (y : ℂ) : Function.invFun f y = e.symm y := by
  subst he
  apply e.injective
  rw [Homeomorph.apply_symm_apply]
  exact Function.invFun_eq (e.surjective y)

/-- (C3) `[W5]` Joint continuity of the inverse maps. -/
theorem wr_ns2_inv_cont {m₁ m₂ : ℂ → ℂ} {k₁ k₂ : ℝ} (hm₁ : IsBeltramiCoeff m₁ univ k₁)
    (hm₂ : IsBeltramiCoeff m₂ univ k₂) {W : Set (ℂ × ℂ)} (hW : IsOpen W)
    (hWk : ∀ P ∈ W, ∃ k < 1, IsBeltramiCoeff (fun u => P.1 * m₁ u + P.2 * m₂ u) univ k) :
    ContinuousOn (fun q : (ℂ × ℂ) × ℂ =>
      Function.invFun (normalizedSolution fun u => q.1.1 * m₁ u + q.1.2 * m₂ u) q.2) (W ×ˢ univ) := by
  -- `hW` is not needed (continuity within `W ×ˢ univ` holds at every point of `W`).
  have _hW := hW
  rintro ⟨P₀, z₀⟩ ⟨hP₀, -⟩
  show Tendsto _ (𝓝[W ×ˢ univ] (P₀, z₀)) _
  rw [Filter.tendsto_iff_seq_tendsto]
  intro x hx
  have hx' := tendsto_nhdsWithin_iff.mp hx
  have h1 : Tendsto (fun n => (x n).1) atTop (𝓝 P₀) := (continuous_fst.tendsto _).comp hx'.1
  have h2 : Tendsto (fun n => (x n).2) atTop (𝓝 z₀) := (continuous_snd.tendsto _).comp hx'.1
  have hL := wr_ns2_luc hm₁ hm₂ hWk hP₀ h1
  obtain ⟨N, hN⟩ := eventually_atTop.1 hx'.2
  have he : ∀ n, ∃ e : ℂ ≃ₜ ℂ,
      ⇑e = normalizedSolution (fun u => (x (n + N)).1.1 * m₁ u + (x (n + N)).1.2 * m₂ u) := by
    intro n
    obtain ⟨k, hk, hP⟩ := hWk _ (hN (n + N) (by omega)).1
    obtain ⟨h0, hk0, hk1⟩ := wr_coeff_nonneg hk hP
    have h := wr_ns_qc hk0 hk1 h0 le_rfl
    exact t1_homeomorph h.1 h.2.1
  choose E hE using he
  obtain ⟨k₀, hk₀, h₀⟩ := hWk _ hP₀
  obtain ⟨h0, hk0, hk1⟩ := wr_coeff_nonneg hk₀ h₀
  have hW0 := wr_ns_qc hk0 hk1 h0 le_rfl
  obtain ⟨e₀, he₀⟩ := t1_homeomorph hW0.1 hW0.2.1
  have hLE : TendstoLocallyUniformly (fun n => ⇑(E n)) ⇑e₀ atTop := by
    rw [tendstoLocallyUniformly_iff_forall_isCompact] at hL ⊢
    intro K hK
    have h := hL K hK
    rw [Metric.tendstoUniformlyOn_iff] at h ⊢
    intro ε hε
    filter_upwards [(tendsto_add_atTop_nat N).eventually (h ε hε)] with n hn
    intro z hz
    rw [he₀, hE n]
    exact hn z hz
  have hinv := kn6_inverse_locallyUniform hLE
  have h2' : Tendsto (fun n => (x (n + N)).2) atTop (𝓝 z₀) := (tendsto_add_atTop_iff_nat N).2 h2
  have hlim := hinv.tendsto_comp e₀.symm.continuous.continuousAt h2'
  have hval : Function.invFun (normalizedSolution fun u => P₀.1 * m₁ u + P₀.2 * m₂ u) z₀ = e₀.symm z₀ :=
    wr_invFun_eq he₀ z₀
  show Tendsto (fun n => Function.invFun (normalizedSolution fun u => (x n).1.1 * m₁ u + (x n).1.2 * m₂ u)
    (x n).2) atTop (𝓝 (Function.invFun (normalizedSolution fun u => P₀.1 * m₁ u + P₀.2 * m₂ u) z₀))
  rw [hval, ← tendsto_add_atTop_iff_nat N]
  refine hlim.congr fun n => ?_
  show (E n).symm (x (n + N)).2 = _
  rw [wr_invFun_eq (hE n)]

/-! ### Pointwise regularity in the parameter (下属5) -/

theorem wr_kernel_contDiffAt {w : ℂ × ℂ} (h1 : w.1 ≠ 0) (h2 : w.2 ≠ 0) :
    ContDiffAt ℝ 3 (fun w : ℂ × ℂ => (w.1 * w.2)⁻¹) w :=
  (contDiff_fst.mul contDiff_snd).contDiffAt.inv (mul_ne_zero h1 h2)

/-- A function on a closed bidisc that is jointly continuous and separately holomorphic is real `C³` on the
concentric bidisc of half the radius (Cauchy's formula `wr_cauchy_bidisc`, then `wr_contDiffOn_integral`). -/
theorem wr_bidisc_contDiffOn {f : ℂ × ℂ → ℂ} {c : ℂ × ℂ} {R : ℝ} (hR : 0 < R)
    (hcont : ContinuousOn f (closedBall c.1 R ×ˢ closedBall c.2 R))
    (h₁ : ∀ b ∈ closedBall c.2 R, DifferentiableOn ℂ (fun a => f (a, b)) (ball c.1 R))
    (h₂ : ∀ a ∈ closedBall c.1 R, DifferentiableOn ℂ (fun b => f (a, b)) (ball c.2 R)) :
    ContDiffOn ℝ 3 f (ball c (R / 2)) := by
  -- the kernel `k(w) = 1/(w₁w₂)` on `O = {w₁ ≠ 0, w₂ ≠ 0}`
  have hO : IsOpen {w : ℂ × ℂ | w.1 ≠ 0 ∧ w.2 ≠ 0} :=
    (isOpen_ne_fun continuous_fst continuous_const).inter (isOpen_ne_fun continuous_snd continuous_const)
  have hk : ContDiffOn ℝ 3 (fun w : ℂ × ℂ => (w.1 * w.2)⁻¹) {w : ℂ × ℂ | w.1 ≠ 0 ∧ w.2 ≠ 0} :=
    fun w hw => (wr_kernel_contDiffAt hw.1 hw.2).contDiffWithinAt
  have hkc : ∀ j ≤ 3, ContinuousOn (iteratedFDeriv ℝ j (fun w : ℂ × ℂ => (w.1 * w.2)⁻¹))
      {w : ℂ × ℂ | w.1 ≠ 0 ∧ w.2 ≠ 0} := fun j hj =>
    (hk.continuousOn_iteratedFDerivWithin (by exact_mod_cast hj) hO.uniqueDiffOn).congr
      fun w hw => (iteratedFDerivWithin_of_isOpen j hO hw).symm
  -- the torus parametrization
  have hd : ∀ (a : ℂ) (θ : ℝ), deriv (circleMap a R) θ = circleMap 0 R θ * I := fun a θ => deriv_circleMap a R θ
  have hqc : Continuous fun x : ℝ × ℝ => (circleMap c.1 R x.1, circleMap c.2 R x.2) :=
    ((continuous_circleMap _ _).comp continuous_fst).prodMk ((continuous_circleMap _ _).comp continuous_snd)
  have hqT : ∀ x : ℝ × ℝ, (circleMap c.1 R x.1, circleMap c.2 R x.2) ∈ sphere c.1 R ×ˢ sphere c.2 R :=
    fun x => ⟨circleMap_mem_sphere _ hR.le _, circleMap_mem_sphere _ hR.le _⟩
  have hqB : ∀ x : ℝ × ℝ, (circleMap c.1 R x.1, circleMap c.2 R x.2) ∈ closedBall c.1 R ×ˢ closedBall c.2 R :=
    fun x => ⟨sphere_subset_closedBall (hqT x).1, sphere_subset_closedBall (hqT x).2⟩
  obtain ⟨Mf, hMf⟩ := (isCompact_closedBall c.1 R).prod (isCompact_closedBall c.2 R)
    |>.exists_bound_of_continuousOn hcont
  -- the weight `A(θ, η) = γ₁'(θ) γ₂'(η) f(γ(θ, η))`
  have hAc : Continuous fun x : ℝ × ℝ => circleMap 0 R x.1 * I * (circleMap 0 R x.2 * I) *
      f (circleMap c.1 R x.1, circleMap c.2 R x.2) :=
    ((((continuous_circleMap 0 R).comp continuous_fst).mul continuous_const).mul
      (((continuous_circleMap 0 R).comp continuous_snd).mul continuous_const)).mul
      (hcont.comp_continuous hqc hqB)
  have hAb : ∀ x : ℝ × ℝ, ‖circleMap 0 R x.1 * I * (circleMap 0 R x.2 * I) *
      f (circleMap c.1 R x.1, circleMap c.2 R x.2)‖ ≤ |R| * |R| * Mf := by
    intro x
    simp only [norm_mul, norm_circleMap_zero, Complex.norm_I, mul_one]
    exact mul_le_mul_of_nonneg_left (hMf _ (hqB x)) (by positivity)
  -- geometry: for `y` in the half bidisc and `q` on the torus, `y - q ∈ O`
  have hmemU : ∀ y ∈ ball c (R / 2), dist y.1 c.1 < R / 2 ∧ dist y.2 c.2 < R / 2 := by
    intro y hy
    rw [mem_ball, Prod.dist_eq, max_lt_iff] at hy
    exact hy
  have hTO : ∀ y ∈ ball c (R / 2), ∀ q ∈ sphere c.1 R ×ˢ sphere c.2 R,
      y - q ∈ {w : ℂ × ℂ | w.1 ≠ 0 ∧ w.2 ≠ 0} := by
    intro y hy q hq
    obtain ⟨hy1, hy2⟩ := hmemU y hy
    have hq1 : dist q.1 c.1 = R := hq.1
    have hq2 : dist q.2 c.2 = R := hq.2
    refine ⟨fun h => ?_, fun h => ?_⟩
    · have : y.1 = q.1 := sub_eq_zero.mp h
      rw [this, hq1] at hy1; linarith
    · have : y.2 = q.2 := sub_eq_zero.mp h
      rw [this, hq2] at hy2; linarith
  -- compact images of `K × torus` under subtraction
  have hTc : ∀ K ⊆ ball c (R / 2), IsCompact K →
      ∀ j ≤ 3, ∃ C, ∀ y ∈ K, ∀ q ∈ sphere c.1 R ×ˢ sphere c.2 R,
        ‖iteratedFDeriv ℝ j (fun w : ℂ × ℂ => (w.1 * w.2)⁻¹) (y - q)‖ ≤ C := by
    intro K hK hKc j hj
    have hT : IsCompact ((fun p : (ℂ × ℂ) × (ℂ × ℂ) => p.1 - p.2) '' (K ×ˢ (sphere c.1 R ×ˢ sphere c.2 R))) :=
      (hKc.prod ((isCompact_sphere _ _).prod (isCompact_sphere _ _))).image (continuous_fst.sub continuous_snd)
    have hTsub : (fun p : (ℂ × ℂ) × (ℂ × ℂ) => p.1 - p.2) '' (K ×ˢ (sphere c.1 R ×ˢ sphere c.2 R)) ⊆
        {w : ℂ × ℂ | w.1 ≠ 0 ∧ w.2 ≠ 0} := by
      rintro _ ⟨p, hp, rfl⟩
      exact hTO p.1 (hK hp.1) p.2 hp.2
    obtain ⟨C, hC⟩ := hT.exists_bound_of_continuousOn ((hkc j hj).mono hTsub)
    exact ⟨C, fun y hy q hq => hC _ ⟨(y, q), ⟨hy, hq⟩, rfl⟩⟩
  -- the integrand
  set F : ℝ × ℝ → ℂ × ℂ → ℂ := fun x p => circleMap 0 R x.1 * I * (circleMap 0 R x.2 * I) *
      f (circleMap c.1 R x.1, circleMap c.2 R x.2) *
      ((p - (circleMap c.1 R x.1, circleMap c.2 R x.2)).1 *
        (p - (circleMap c.1 R x.1, circleMap c.2 R x.2)).2)⁻¹ with hFdef
  have hkcd : ∀ x : ℝ × ℝ, ∀ y ∈ ball c (R / 2), ContDiffAt ℝ 3
      (fun p : ℂ × ℂ => ((p - (circleMap c.1 R x.1, circleMap c.2 R x.2)).1 *
        (p - (circleMap c.1 R x.1, circleMap c.2 R x.2)).2)⁻¹) y := by
    intro x y hy
    have h := hTO y hy _ (hqT x)
    exact ContDiffAt.comp (g := fun w : ℂ × ℂ => (w.1 * w.2)⁻¹)
      (f := fun p : ℂ × ℂ => p - (circleMap c.1 R x.1, circleMap c.2 R x.2)) y
      (wr_kernel_contDiffAt h.1 h.2) (contDiffAt_id.sub contDiffAt_const)
  have hform : ∀ j ≤ 3, ∀ x : ℝ × ℝ, ∀ y ∈ ball c (R / 2), iteratedFDeriv ℝ j (F x) y =
      (circleMap 0 R x.1 * I * (circleMap 0 R x.2 * I) * f (circleMap c.1 R x.1, circleMap c.2 R x.2)) •
        iteratedFDeriv ℝ j (fun w : ℂ × ℂ => (w.1 * w.2)⁻¹) (y - (circleMap c.1 R x.1, circleMap c.2 R x.2)) := by
    intro j hj x y hy
    show iteratedFDeriv ℝ j (fun p : ℂ × ℂ =>
      (circleMap 0 R x.1 * I * (circleMap 0 R x.2 * I) * f (circleMap c.1 R x.1, circleMap c.2 R x.2)) •
        (fun w : ℂ × ℂ => (w.1 * w.2)⁻¹) (p - (circleMap c.1 R x.1, circleMap c.2 R x.2))) y = _
    have hs := iteratedFDeriv_comp_sub (𝕜 := ℝ) (f := fun w : ℂ × ℂ => (w.1 * w.2)⁻¹) j
      (circleMap c.1 R x.1, circleMap c.2 R x.2) y
    rw [iteratedFDeriv_const_smul_apply' ((hkcd x y hy).of_le (by exact_mod_cast hj)), hs]
  -- the measure
  set μI : Measure ℝ := volume.restrict (Ioc 0 (2 * π)) with hμI
  have : IsFiniteMeasure μI := isFiniteMeasure_restrict.mpr measure_Ioc_lt_top.ne
  have hU : IsOpen (ball c (R / 2)) := isOpen_ball
  have hI : ContDiffOn ℝ ((3 : ℕ) : WithTop ℕ∞) (fun y => ∫ x, F x y ∂(μI.prod μI)) (ball c (R / 2)) := by
    refine wr_contDiffOn_integral hU (fun x y hy => ?_) (fun j hj y hy => ?_) (fun j hj K hK hKc => ?_)
    · exact (contDiffAt_const.mul (hkcd x y hy)).contDiffWithinAt
    · have hj' : j ≤ 3 := hj
      refine Continuous.aestronglyMeasurable ?_ |>.congr (Eventually.of_forall fun x => (hform j hj' x y hy).symm)
      haveI : ContinuousSMul ℂ (ContinuousMultilinearMap ℝ (fun _ : Fin j => ℂ × ℂ) ℂ) :=
        IsBoundedSMul.continuousSMul
      exact hAc.smul ((hkc j hj').comp_continuous (continuous_const.sub hqc) fun x => hTO y hy _ (hqT x))
    · have hj' : j ≤ 3 := hj
      obtain ⟨C, hC⟩ := hTc K hK hKc j hj'
      refine ⟨|R| * |R| * Mf * C, fun x y hy => ?_⟩
      rw [hform j hj' x y (hK hy), norm_smul]
      exact mul_le_mul (hAb x) (hC y hy _ (hqT x)) (norm_nonneg _) (by
        have := hAb x; have := norm_nonneg (circleMap 0 R x.1 * I * (circleMap 0 R x.2 * I) *
          f (circleMap c.1 R x.1, circleMap c.2 R x.2)); linarith)
  -- Cauchy's formula as an integral over the torus
  have h2π : (0 : ℝ) ≤ 2 * π := by positivity
  have hrep : ∀ p ∈ ball c (R / 2), f p = ((2 * π * I)⁻¹) ^ 2 * ∫ x, F x p ∂(μI.prod μI) := by
    intro p hp
    obtain ⟨hp1, hp2⟩ := hmemU p hp
    have hp' : p ∈ ball c.1 R ×ˢ ball c.2 R := ⟨by rw [mem_ball]; linarith, by rw [mem_ball]; linarith⟩
    rw [wr_cauchy_bidisc hR hR hcont h₁ h₂ hp']
    congr 1
    have hint : Integrable (fun x => F x p) (μI.prod μI) := by
      obtain ⟨C, hC⟩ := hTc {p} (singleton_subset_iff.mpr hp) isCompact_singleton 0 (by norm_num)
      refine Integrable.of_bound ?_ (|R| * |R| * Mf * C) (Eventually.of_forall fun x => ?_)
      · refine Continuous.aestronglyMeasurable ?_
        refine hAc.mul ?_
        exact (hk.continuousOn.comp_continuous (continuous_const.sub hqc) fun x => hTO p hp _ (hqT x))
      · have h0 := hC p rfl _ (hqT x)
        rw [norm_iteratedFDeriv_zero] at h0
        show ‖_ * _‖ ≤ _
        rw [norm_mul]
        exact mul_le_mul (hAb x) h0 (norm_nonneg _) (by
          have := hAb x; have := norm_nonneg (circleMap 0 R x.1 * I * (circleMap 0 R x.2 * I) *
            f (circleMap c.1 R x.1, circleMap c.2 R x.2)); linarith)
    rw [integral_prod _ hint]
    simp only [circleIntegral, smul_eq_mul, hd]
    rw [intervalIntegral.integral_of_le h2π]
    refine integral_congr_ae (Eventually.of_forall fun θ => ?_)
    simp only
    rw [intervalIntegral.integral_of_le h2π, ← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun η => ?_)
    simp only [hFdef, Prod.fst_sub, Prod.snd_sub]
    rw [show (p.1 - circleMap c.1 R θ) * (p.2 - circleMap c.2 R η) =
      (circleMap c.1 R θ - p.1) * (circleMap c.2 R η - p.2) by ring]
    ring
  exact (contDiffOn_const.mul (by exact_mod_cast hI)).congr hrep

/-- Pointwise in `z`, the normalized solution is real `C³` in the parameter `P` on `W`. -/
theorem wr_ns2_param_contDiffOn {m₁ m₂ : ℂ → ℂ} {k₁ k₂ : ℝ} (hm₁ : IsBeltramiCoeff m₁ univ k₁)
    (hm₂ : IsBeltramiCoeff m₂ univ k₂) {W : Set (ℂ × ℂ)} (hW : IsOpen W)
    (hWk : ∀ P ∈ W, ∃ k < 1, IsBeltramiCoeff (fun u => P.1 * m₁ u + P.2 * m₂ u) univ k) (z : ℂ) :
    ContDiffOn ℝ 3 (fun P : ℂ × ℂ => normalizedSolution (fun u => P.1 * m₁ u + P.2 * m₂ u) z) W := by
  refine contDiffOn_of_locally_contDiffOn fun P₀ hP₀ => ?_
  obtain ⟨R, hR, hRW⟩ := Metric.isOpen_iff.1 hW P₀ hP₀
  have hsub : closedBall P₀.1 (R / 2) ×ˢ closedBall P₀.2 (R / 2) ⊆ W := by
    intro P hP
    apply hRW
    rw [mem_ball, Prod.dist_eq, max_lt_iff]
    exact ⟨lt_of_le_of_lt hP.1 (by linarith), lt_of_le_of_lt hP.2 (by linarith)⟩
  have hC2 := wr_ns2_cont hm₁ hm₂ hW hWk
  have hcont : ContinuousOn (fun P : ℂ × ℂ => normalizedSolution (fun u => P.1 * m₁ u + P.2 * m₂ u) z)
      (closedBall P₀.1 (R / 2) ×ˢ closedBall P₀.2 (R / 2)) := by
    have h := ContinuousOn.comp (g := fun q : (ℂ × ℂ) × ℂ =>
        normalizedSolution (fun u => q.1.1 * m₁ u + q.1.2 * m₂ u) q.2)
      (f := fun P : ℂ × ℂ => (P, z)) hC2 (continuous_id.prodMk continuous_const).continuousOn
      (fun P hP => ⟨hsub hP, mem_univ _⟩)
    exact h
  have hH := wr_ns2_holo hm₁ hm₂ hW hWk z
  have h₁ : ∀ b ∈ closedBall P₀.2 (R / 2), DifferentiableOn ℂ
      (fun a => normalizedSolution (fun u => a * m₁ u + b * m₂ u) z) (ball P₀.1 (R / 2)) :=
    fun b hb => (hH.1 b).mono fun a ha => hsub ⟨ball_subset_closedBall ha, hb⟩
  have h₂ : ∀ a ∈ closedBall P₀.1 (R / 2), DifferentiableOn ℂ
      (fun b => normalizedSolution (fun u => a * m₁ u + b * m₂ u) z) (ball P₀.2 (R / 2)) :=
    fun a ha => (hH.2 a).mono fun b hb => hsub ⟨ha, ball_subset_closedBall hb⟩
  refine ⟨ball P₀ (R / 4), isOpen_ball, mem_ball_self (by positivity), ?_⟩
  exact (wr_bidisc_contDiffOn (c := P₀) (by positivity) hcont h₁ h₂).mono
    (inter_subset_right.trans (ball_subset_ball (le_of_eq (by ring))))

/-! ## Part D stubs (frozen, WR_INTERFACE 547f19d7) -/

/-! ### Helpers for D1 (下属4) -/

/-- A cutoff times a coefficient smooth on `Ω`, with the cutoff supported in `Ω`, is smooth on `ℂ`. -/
theorem wr_cutoff_mul_contDiff {Ω : Set ℂ} (hΩ : IsOpen Ω) {m : ℂ → ℂ}
    (hs : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) m Ω) {χ : ℂ → ℝ} (hχ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ)
    (hsupp : tsupport χ ⊆ Ω) : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z => (χ z : ℂ) * m z) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x ∈ Ω
  · have h1 : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z => (χ z : ℂ)) x :=
      (ofRealCLM.contDiff.comp hχ).contDiffAt
    exact h1.mul (hs.contDiffAt (hΩ.mem_nhds hx))
  · have hx' : x ∉ tsupport χ := fun h => hx (hsupp h)
    have hev : (fun z => (χ z : ℂ) * m z) =ᶠ[𝓝 x] fun _ => 0 := by
      filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hx'] with z hz
      simp only [Pi.zero_apply] at hz
      simp [hz]
    exact contDiffAt_const.congr_of_eventuallyEq hev

/-- An a.e. bound of a function continuous on an open set holds everywhere on it. -/
theorem wr_ae_bound_on {μ : ℂ → ℂ} {Ω : Set ℂ} (hΩ : IsOpen Ω) (hc : ContinuousOn μ Ω) {k : ℝ}
    (h : ∀ᵐ z, ‖μ z‖ ≤ k) : ∀ z ∈ Ω, ‖μ z‖ ≤ k := by
  intro z hz
  by_contra hlt
  have hlt' : k < ‖μ z‖ := not_le.mp hlt
  have hca : ContinuousAt (fun y => ‖μ y‖) z :=
    continuous_norm.continuousAt.comp (hc.continuousAt (hΩ.mem_nhds hz))
  have hev : {y | k < ‖μ y‖} ∈ 𝓝 z := hca.eventually (eventually_gt_nhds hlt')
  have hpos := Measure.measure_pos_of_mem_nhds volume hev
  have hzero : volume {y | ¬ ‖μ y‖ ≤ k} = 0 := ae_iff.mp h
  simp only [not_le] at hzero
  exact hpos.ne' hzero

/-- Restriction of a Beltrami coefficient on `ℂ` to a subset. -/
theorem wr_bc_restrict {m : ℂ → ℂ} {k : ℝ} (hm : IsBeltramiCoeff m univ k) (D : Set ℂ) :
    IsBeltramiCoeff m D k :=
  ⟨hm.1.mono_measure (Measure.restrict_mono (subset_univ D) le_rfl),
    hm.2.filter_mono (ae_mono (Measure.restrict_mono (subset_univ D) le_rfl))⟩

/-- The normalized solution of `m` is a generalized homeomorphic solution on an open `D` for every `μ`
that agrees with `m` on `D`. -/
theorem wr_ns_genHomeo {m μ : ℂ → ℂ} {k : ℝ} (hk : k < 1) (hm : IsBeltramiCoeff m univ k) {D : Set ℂ}
    (hD : IsOpen D) (hmμ : EqOn m μ D) : IsGenHomeoSolution (normalizedSolution m) μ D 2 := by
  obtain ⟨h0, hk0, hk1⟩ := wr_coeff_nonneg hk hm
  obtain ⟨f, hf, -, -⟩ := thm13_7_normalized_existence hk0 hk1 h0
  have hns := QCV.qcv_ns_eq hk0 hk1 h0 hf
  have hq := (wr_ns_qc hk0 hk1 h0 le_rfl).1
  have hqD := ac_t_isKQC_restrict hq hD (subset_univ _)
  have h2 := (thm10_2_genHomeoSolution_of_isKQC hqD).2
  refine nxS_genHomeoSolution_congr h2 ?_
  have hae : ∀ᵐ z, complexDilatation (normalizedSolution m) z = m z := by
    rw [hns]
    exact hf.2.2.2.2
  filter_upwards [ae_restrict_of_ae hae, ae_restrict_mem hD.measurableSet] with z hz hzD
  rw [hz, hmμ hzD]

/-- The Cauchy representation at one parameter: `w = H ∘ G` near the point, with `H` holomorphic. -/
theorem wr_d1_cauchy {μ ν : ℂ → ℂ} {D : Set ℂ} (hD : IsOpen D) {k : ℝ} (hk : k < 1)
    (hb : IsBeltramiCoeff μ univ k) {kν : ℝ} (hkν : kν < 1) (hbν : IsBeltramiCoeff ν univ kν) (hEq : EqOn ν μ D)
    {c : ℂ} {R : ℝ} (hR : 0 < R)
    (hmemD : ∀ ξ ∈ closedBall c R, Function.invFun (normalizedSolution ν) ξ ∈ D) {z : ℂ} (hzD : z ∈ D)
    (hw : normalizedSolution ν z ∈ ball c R) :
    normalizedSolution μ z = (2 * π * I)⁻¹ * ∮ ξ in C(c, R),
      normalizedSolution μ (Function.invFun (normalizedSolution ν) ξ) / (ξ - normalizedSolution ν z) := by
  obtain ⟨hb', hk0, hk1⟩ := wr_coeff_nonneg hk hb
  obtain ⟨hbν', hkν0, hkν1⟩ := wr_coeff_nonneg hkν hbν
  obtain ⟨e, he⟩ : ∃ e : ℂ ≃ₜ ℂ, ⇑e = normalizedSolution ν := by
    have h := wr_ns_qc hkν0 hkν1 hbν' le_rfl
    exact t1_homeomorph h.1 h.2.1
  have hright : ∀ ξ, normalizedSolution ν (Function.invFun (normalizedSolution ν) ξ) = ξ := by
    intro ξ
    rw [wr_invFun_eq he, ← he]
    exact e.apply_symm_apply ξ
  have hf := wr_ns_genHomeo hkν hbν hD hEq
  have hg := wr_ns_genHomeo hk1 hb' hD (fun u _ => rfl)
  obtain ⟨φ, ⟨hφd, -, -⟩, hφ⟩ := same_dilatation_conformal hD hk1 (wr_bc_restrict hb' _) hf hg
  have hopen : IsOpen (normalizedSolution ν '' D) := by
    rw [← he]
    exact e.isOpenMap _ hD
  have hcl : closedBall c R ⊆ normalizedSolution ν '' D := fun ξ hξ => ⟨_, hmemD ξ hξ, hright ξ⟩
  have hcauchy := two_pi_I_inv_smul_circleIntegral_sub_inv_smul_of_differentiable_on_off_countable
    Set.countable_empty hw (hφd.continuousOn.mono hcl)
    (fun x hx => hφd.differentiableAt (hopen.mem_nhds (hcl (ball_subset_closedBall hx.1))))
  rw [hφ z hzD, ← hcauchy, smul_eq_mul]
  congr 1
  refine circleIntegral.integral_congr hR.le fun ξ hξ => ?_
  show (ξ - normalizedSolution ν z)⁻¹ • φ ξ =
    normalizedSolution μ (Function.invFun (normalizedSolution ν) ξ) / (ξ - normalizedSolution ν z)
  rw [hφ _ (hmemD ξ (sphere_subset_closedBall hξ)), hright ξ, smul_eq_mul, div_eq_mul_inv, mul_comm]

/-- (D1) `[W1]` Local Cauchy representation through the smooth compactly supported comparison family `G`. -/
theorem wr_local_cauchy {m₁ m₂ : ℂ → ℂ} {k₁ k₂ : ℝ} (hm₁ : IsBeltramiCoeff m₁ univ k₁)
    (hm₂ : IsBeltramiCoeff m₂ univ k₂) {Ω : Set ℂ} (hΩ : IsOpen Ω)
    (hs₁ : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) m₁ Ω) (hs₂ : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) m₂ Ω)
    {W : Set (ℂ × ℂ)} (hW : IsOpen W)
    (hWk : ∀ P ∈ W, ∃ k < 1, IsBeltramiCoeff (fun u => P.1 * m₁ u + P.2 * m₂ u) univ k)
    {P₀ : ℂ × ℂ} (hP₀ : P₀ ∈ W) {z₀ : ℂ} (hz₀ : z₀ ∈ Ω) :
    ∃ V ∈ 𝓝 P₀, V ⊆ W ∧ ∃ ρ > 0, ∃ G : ℂ × ℂ → ℂ → ℂ, ∃ c : ℂ, ∃ R > 0,
      (∀ P ∈ V, ContDiff ℝ 3 (G P)) ∧
      (∀ j ≤ 3, ContinuousOn (fun q : (ℂ × ℂ) × ℂ => iteratedFDeriv ℝ j (G q.1) q.2) (V ×ˢ univ)) ∧
      ContinuousOn (fun q : (ℂ × ℂ) × ℂ =>
        normalizedSolution (fun u => q.1.1 * m₁ u + q.1.2 * m₂ u) (Function.invFun (G q.1) q.2))
        (V ×ˢ sphere c R) ∧
      ∀ P ∈ V, ∀ z ∈ ball z₀ ρ, G P z ∈ ball c (R / 2) ∧
        normalizedSolution (fun u => P.1 * m₁ u + P.2 * m₂ u) z =
          (2 * π * I)⁻¹ * ∮ ξ in C(c, R),
            normalizedSolution (fun u => P.1 * m₁ u + P.2 * m₂ u) (Function.invFun (G P) ξ) / (ξ - G P z) := by
  -- the cutoff
  obtain ⟨r, hr, hrΩ⟩ : ∃ r > 0, closedBall z₀ (3 * r) ⊆ Ω := by
    obtain ⟨ε, hε, hsub⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hΩ.mem_nhds hz₀)
    refine ⟨ε / 3, by positivity, ?_⟩
    rwa [mul_div_cancel₀ _ (by norm_num : (3 : ℝ) ≠ 0)]
  let χ : ContDiffBump z₀ := ⟨2 * r, 3 * r, by positivity, by linarith⟩
  have hχs : tsupport χ ⊆ Ω := by
    rw [χ.tsupport_eq]
    exact hrΩ
  have hχ1 : ∀ z ∈ ball z₀ (2 * r), (χ z : ℂ) = 1 := by
    intro z hz
    have h : χ z = 1 := χ.one_of_mem_closedBall (ball_subset_closedBall hz)
    rw [h, Complex.ofReal_one]
  have hχn : ∀ z, ‖(χ z : ℂ)‖ ≤ 1 := by
    intro z
    rw [Complex.norm_real, Real.norm_of_nonneg χ.nonneg]
    exact χ.le_one
  have hχ0 : ∀ z, z ∉ Ω → (χ z : ℂ) = 0 := by
    intro z hz
    rw [image_eq_zero_of_notMem_tsupport fun h => hz (hχs h), Complex.ofReal_zero]
  obtain ⟨ν₁, hν₁d⟩ : ∃ ν₁ : ℂ → ℂ, ν₁ = fun z => (χ z : ℂ) * m₁ z := ⟨_, rfl⟩
  obtain ⟨ν₂, hν₂d⟩ : ∃ ν₂ : ℂ → ℂ, ν₂ = fun z => (χ z : ℂ) * m₂ z := ⟨_, rfl⟩
  have hν₁ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ν₁ := hν₁d ▸ wr_cutoff_mul_contDiff hΩ hs₁ χ.contDiff hχs
  have hν₂ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ν₂ := hν₂d ▸ wr_cutoff_mul_contDiff hΩ hs₂ χ.contDiff hχs
  have hcs : HasCompactSupport (fun z => (χ z : ℂ)) := χ.hasCompactSupport.comp_left Complex.ofReal_zero
  have hc₁ : HasCompactSupport ν₁ := hν₁d ▸ hcs.mul_right
  have hc₂ : HasCompactSupport ν₂ := hν₂d ▸ hcs.mul_right
  have hνP : ∀ (P : ℂ × ℂ) z, P.1 * ν₁ z + P.2 * ν₂ z = (χ z : ℂ) * (P.1 * m₁ z + P.2 * m₂ z) := by
    intro P z
    rw [hν₁d, hν₂d]
    ring
  -- the comparison coefficients are bounded everywhere
  have hνk : ∀ P ∈ W, ∃ k < 1, ∀ z, ‖P.1 * ν₁ z + P.2 * ν₂ z‖ ≤ k := by
    intro P hP
    obtain ⟨k, hk, hb⟩ := hWk P hP
    obtain ⟨hb', hk0, hk1⟩ := wr_coeff_nonneg hk hb
    refine ⟨max k 0, hk1, fun z => ?_⟩
    rw [hνP, norm_mul]
    by_cases hz : z ∈ Ω
    · have hcont : ContinuousOn (fun u => P.1 * m₁ u + P.2 * m₂ u) Ω :=
        (continuousOn_const.mul hs₁.continuousOn).add (continuousOn_const.mul hs₂.continuousOn)
      have hae : ∀ᵐ u, ‖P.1 * m₁ u + P.2 * m₂ u‖ ≤ max k 0 := by
        simpa only [Measure.restrict_univ] using hb'.2
      exact (mul_le_of_le_one_left (norm_nonneg _) (hχn z)).trans (wr_ae_bound_on hΩ hcont hae z hz)
    · rw [hχ0 z hz, norm_zero, zero_mul]
      exact hk0
  have hBν : ∀ P ∈ W, ∃ k < 1, IsBeltramiCoeff (fun u => P.1 * ν₁ u + P.2 * ν₂ u) univ k := by
    intro P hP
    obtain ⟨k, hk, hb⟩ := hνk P hP
    exact ⟨k, hk, ((continuous_const.mul hν₁.continuous).add
      (continuous_const.mul hν₂.continuous)).aestronglyMeasurable, ae_of_all _ hb⟩
  have hBν₁ : IsBeltramiCoeff ν₁ univ k₁ := by
    refine ⟨hν₁.continuous.aestronglyMeasurable, hm₁.2.mono fun z hz => ?_⟩
    rw [hν₁d]
    show ‖(χ z : ℂ) * m₁ z‖ ≤ k₁
    rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) (hχn z)).trans hz
  have hBν₂ : IsBeltramiCoeff ν₂ univ k₂ := by
    refine ⟨hν₂.continuous.aestronglyMeasurable, hm₂.2.mono fun z hz => ?_⟩
    rw [hν₂d]
    show ‖(χ z : ℂ) * m₂ z‖ ≤ k₂
    rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) (hχn z)).trans hz
  -- the comparison family and its properties
  obtain ⟨hGsm, hGcont⟩ := wr_smooth_family hν₁ hc₁ hν₂ hc₂ hW hνk
  have hGc := wr_ns2_cont hBν₁ hBν₂ hW hBν
  have hGi := wr_ns2_inv_cont hBν₁ hBν₂ hW hBν
  have hMc := wr_ns2_cont hm₁ hm₂ hW hWk
  have hhom : ∀ P ∈ W, ∃ e : ℂ ≃ₜ ℂ, ⇑e = normalizedSolution (fun u => P.1 * ν₁ u + P.2 * ν₂ u) := by
    intro P hP
    obtain ⟨k, hk, hP'⟩ := hBν P hP
    obtain ⟨h0, hk0, hk1⟩ := wr_coeff_nonneg hk hP'
    have h := wr_ns_qc hk0 hk1 h0 le_rfl
    exact t1_homeomorph h.1 h.2.1
  have hleft : ∀ P ∈ W, ∀ z, Function.invFun (normalizedSolution (fun u => P.1 * ν₁ u + P.2 * ν₂ u))
      (normalizedSolution (fun u => P.1 * ν₁ u + P.2 * ν₂ u) z) = z := by
    intro P hP z
    obtain ⟨e, he⟩ := hhom P hP
    rw [wr_invFun_eq he, ← he]
    exact e.symm_apply_apply z
  have hright : ∀ P ∈ W, ∀ ξ, normalizedSolution (fun u => P.1 * ν₁ u + P.2 * ν₂ u)
      (Function.invFun (normalizedSolution (fun u => P.1 * ν₁ u + P.2 * ν₂ u)) ξ) = ξ := by
    intro P hP ξ
    obtain ⟨e, he⟩ := hhom P hP
    rw [wr_invFun_eq he, ← he]
    exact e.apply_symm_apply ξ
  have hWn : W ×ˢ (univ : Set ℂ) ∈ 𝓝 (P₀, z₀) := prod_mem_nhds (hW.mem_nhds hP₀) Filter.univ_mem
  -- uniform geometry: the inverse maps a fixed closed disc around `c` into `B(z₀, 2r)`
  obtain ⟨c, hcd⟩ : ∃ c : ℂ, c = normalizedSolution (fun u => P₀.1 * ν₁ u + P₀.2 * ν₂ u) z₀ := ⟨_, rfl⟩
  have hWc : W ×ˢ (univ : Set ℂ) ∈ 𝓝 (P₀, c) := prod_mem_nhds (hW.mem_nhds hP₀) Filter.univ_mem
  have hev1 : ∀ᶠ q in 𝓝 (P₀, c), Function.invFun (normalizedSolution
      (fun u => q.1.1 * ν₁ u + q.1.2 * ν₂ u)) q.2 ∈ ball z₀ (2 * r) := by
    refine (hGi.continuousAt hWc).eventually (isOpen_ball.mem_nhds ?_)
    show Function.invFun (normalizedSolution (fun u => P₀.1 * ν₁ u + P₀.2 * ν₂ u)) c ∈ ball z₀ (2 * r)
    rw [hcd, hleft P₀ hP₀ z₀]
    exact mem_ball_self (by positivity)
  obtain ⟨u₁, hu₁, v₁, hv₁, huv₁⟩ := mem_nhds_prod_iff.mp hev1
  obtain ⟨R₀, hR₀, hR₀v⟩ := Metric.mem_nhds_iff.mp hv₁
  have hR : 0 < R₀ / 2 := by positivity
  have hRsub : closedBall c (R₀ / 2) ⊆ v₁ :=
    (closedBall_subset_ball (by linarith)).trans hR₀v
  -- `G_P` maps a small ball around `z₀` into `B(c, R/2)`
  have hev2 : ∀ᶠ q in 𝓝 (P₀, z₀), normalizedSolution
      (fun u => q.1.1 * ν₁ u + q.1.2 * ν₂ u) q.2 ∈ ball c (R₀ / 2 / 2) := by
    refine (hGc.continuousAt hWn).eventually (isOpen_ball.mem_nhds ?_)
    show normalizedSolution (fun u => P₀.1 * ν₁ u + P₀.2 * ν₂ u) z₀ ∈ ball c (R₀ / 2 / 2)
    rw [← hcd]
    exact mem_ball_self (by positivity)
  obtain ⟨u₂, hu₂, v₂, hv₂, huv₂⟩ := mem_nhds_prod_iff.mp hev2
  obtain ⟨ρ₀, hρ₀, hρ₀v⟩ := Metric.mem_nhds_iff.mp hv₂
  refine ⟨u₁ ∩ u₂ ∩ W, inter_mem (inter_mem hu₁ hu₂) (hW.mem_nhds hP₀), inter_subset_right,
    min ρ₀ (2 * r), lt_min hρ₀ (by positivity), fun P => normalizedSolution (fun u => P.1 * ν₁ u + P.2 * ν₂ u),
    c, R₀ / 2, hR, ?_, ?_, ?_, ?_⟩
  · intro P hP
    exact hGsm P hP.2
  · intro j hj
    exact (hGcont j hj).mono (prod_mono inter_subset_right subset_rfl)
  · have hf : ContinuousOn (fun q : (ℂ × ℂ) × ℂ => (q.1, Function.invFun (normalizedSolution
        (fun u => q.1.1 * ν₁ u + q.1.2 * ν₂ u)) q.2)) ((u₁ ∩ u₂ ∩ W) ×ˢ sphere c (R₀ / 2)) :=
      continuousOn_fst.prodMk (hGi.mono (prod_mono inter_subset_right (subset_univ _)))
    exact hMc.comp hf fun q hq => ⟨hq.1.2, mem_univ _⟩
  · intro P hP z hz
    have hPW : P ∈ W := hP.2
    have hzv₂ : z ∈ v₂ := hρ₀v (ball_subset_ball (min_le_left _ _) hz)
    have hGz := huv₂ (show (P, z) ∈ u₂ ×ˢ v₂ from ⟨hP.1.2, hzv₂⟩)
    simp only [mem_ofPred_eq] at hGz
    refine ⟨hGz, ?_⟩
    have hzD : z ∈ ball z₀ (2 * r) := ball_subset_ball (min_le_right _ _) hz
    obtain ⟨k, hk, hbP⟩ := hWk P hPW
    obtain ⟨kν, hkν, hbν⟩ := hBν P hPW
    have hEq : EqOn (fun u => P.1 * ν₁ u + P.2 * ν₂ u) (fun u => P.1 * m₁ u + P.2 * m₂ u) (ball z₀ (2 * r)) := by
      intro u hu
      show P.1 * ν₁ u + P.2 * ν₂ u = P.1 * m₁ u + P.2 * m₂ u
      rw [hνP, hχ1 u hu, one_mul]
    have hmemD : ∀ ξ ∈ closedBall c (R₀ / 2),
        Function.invFun (normalizedSolution (fun u => P.1 * ν₁ u + P.2 * ν₂ u)) ξ ∈ ball z₀ (2 * r) :=
      fun ξ hξ => by
        have h := huv₁ (show (P, ξ) ∈ u₁ ×ˢ v₁ from ⟨hP.1.1, hRsub hξ⟩)
        simp only [mem_ofPred_eq] at h
        exact h
    exact wr_d1_cauchy isOpen_ball hk hbP hkν hbν hEq hR hmemD hzD (ball_subset_ball (by linarith) hGz)

/-- A `K`-q.c. plane map whose dilatation is `μ` a.e. is a generalized homeomorphic solution for `μ` on any open `D`. -/
theorem wr_d3_gen {f μ : ℂ → ℂ} {K : ℝ} (hf : IsKQC f univ K) {D : Set ℂ} (hD : IsOpen D)
    (hd : ∀ᵐ z ∂(volume.restrict D), complexDilatation f z = μ z) : IsGenHomeoSolution f μ D 2 := by
  obtain ⟨-, hhom, g, h, hp, heq⟩ := thm10_2_genHomeoSolution_of_isKQC (t3b_isKQC_restrict hf hD (subset_univ D))
  refine ⟨hhom, g, h, hp, ?_⟩
  filter_upwards [heq, hd] with z hz hz'
  rw [hz, hz']

/-- A continuous function on an open set with an a.e. bound satisfies the bound everywhere on the set. -/
theorem wr_d3_bound {ν : ℂ → ℂ} {Ω : Set ℂ} (hΩ : IsOpen Ω) (hc : ContinuousOn ν Ω) {k : ℝ}
    (hk : ∀ᵐ z, ‖ν z‖ ≤ k) : ∀ u ∈ Ω, ‖ν u‖ ≤ k := by
  intro u hu
  by_contra hlt
  push_neg at hlt
  have hU : IsOpen (Ω ∩ ν ⁻¹' {y | k < ‖y‖}) :=
    hc.isOpen_inter_preimage hΩ (isOpen_lt continuous_const continuous_norm)
  have hpos := hU.measure_pos volume ⟨u, hu, hlt⟩
  have hnull : volume (Ω ∩ ν ⁻¹' {y | k < ‖y‖}) = 0 := by
    refine measure_mono_null (fun z hz => ?_) (ae_iff.1 hk)
    exact not_le.2 hz.2
  rw [hnull] at hpos
  exact lt_irrefl _ hpos

/-- (D3) `[W1]` Positive Jacobian on the smoothness set (`w = H ∘ G` locally, with `H' ≠ 0` and `J_G > 0`). -/
theorem wr_local_jacobian_pos {m₁ m₂ : ℂ → ℂ} {k₁ k₂ : ℝ} (hm₁ : IsBeltramiCoeff m₁ univ k₁)
    (hm₂ : IsBeltramiCoeff m₂ univ k₂) {Ω : Set ℂ} (hΩ : IsOpen Ω)
    (hs₁ : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) m₁ Ω) (hs₂ : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) m₂ Ω)
    {P : ℂ × ℂ} (hP : ∃ k < 1, IsBeltramiCoeff (fun u => P.1 * m₁ u + P.2 * m₂ u) univ k) {z : ℂ} (hz : z ∈ Ω) :
    0 < ‖dz (normalizedSolution fun u => P.1 * m₁ u + P.2 * m₂ u) z‖ ^ 2 -
      ‖dzbar (normalizedSolution fun u => P.1 * m₁ u + P.2 * m₂ u) z‖ ^ 2 := by
  -- `hm₁`, `hm₂` are not needed: the bound comes from `hP`, the regularity from `hs₁`, `hs₂`.
  have _h₁ := hm₁
  have _h₂ := hm₂
  set ν : ℂ → ℂ := fun u => P.1 * m₁ u + P.2 * m₂ u with hνdef
  obtain ⟨k₀, hk₀, hν₀⟩ := hP
  obtain ⟨hν, hk0, hk1⟩ := wr_coeff_nonneg hk₀ hν₀
  set k := max k₀ 0 with hkdef
  have hνs : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ν Ω :=
    (contDiffOn_const.mul hs₁).add (contDiffOn_const.mul hs₂)
  have hνae : ∀ᵐ u, ‖ν u‖ ≤ k := by
    have h := hν.2
    rwa [Measure.restrict_univ] at h
  have hνb := wr_d3_bound hΩ hνs.continuousOn hνae
  -- the cutoff
  obtain ⟨R, hR, hRΩ⟩ := Metric.isOpen_iff.1 hΩ z hz
  let b : ContDiffBump z := ⟨R / 4, R / 2, by positivity, by linarith⟩
  set χ : ℂ → ℂ := fun u => ((b u : ℝ) : ℂ) with hχ
  have hχs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ := Complex.ofRealCLM.contDiff.comp b.contDiff
  have hχc : HasCompactSupport χ := b.hasCompactSupport.comp_left Complex.ofReal_zero
  have hχΩ : ∀ u ∉ Ω, χ u = 0 := by
    intro u hu
    have : u ∉ Function.support b := by
      rw [b.support_eq]
      intro hb
      exact hu (hRΩ (ball_subset_ball (show b.rOut ≤ R by show R / 2 ≤ R; linarith) hb))
    rw [Function.notMem_support] at this
    simp [hχ, this]
  set ν' : ℂ → ℂ := fun u => χ u * ν u with hν'
  have hν's : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ν' := by
    refine contDiff_iff_contDiffAt.2 fun u => ?_
    by_cases hu : u ∈ tsupport χ
    · have huΩ : u ∈ Ω := by
        have hts : tsupport χ ⊆ closedBall z (R / 2) := by
          refine (tsupport_comp_subset Complex.ofReal_zero b).trans ?_
          rw [b.tsupport_eq]
        exact hRΩ (closedBall_subset_ball (by linarith) (hts hu))
      exact hχs.contDiffAt.mul (hνs.contDiffAt (hΩ.mem_nhds huΩ))
    · have hev : ν' =ᶠ[𝓝 u] fun _ => 0 := by
        filter_upwards [notMem_tsupport_iff_eventuallyEq.1 hu] with y hy
        simp [hν', hy]
      exact contDiffAt_const.congr_of_eventuallyEq hev
  have hν'c : HasCompactSupport ν' := hχc.mul_right
  have hν'b : ∀ u, ‖ν' u‖ ≤ k := by
    intro u
    by_cases hu : u ∈ Ω
    · show ‖χ u * ν u‖ ≤ k
      rw [norm_mul]
      have h1 : ‖χ u‖ ≤ 1 := by
        rw [hχ, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg b.nonneg]
        exact b.le_one
      calc ‖χ u‖ * ‖ν u‖ ≤ 1 * k := mul_le_mul h1 (hνb u hu) (norm_nonneg _) zero_le_one
        _ = k := one_mul k
    · show ‖χ u * ν u‖ ≤ k
      rw [hχΩ u hu, zero_mul, norm_zero]
      exact hk0
  -- the comparison map
  have hJG := wr_smooth_jacobian_pos hν's hν'c hk1 hν'b z
  have hGd : DifferentiableAt ℝ (normalizedSolution ν') z := by
    by_contra hnd
    have h0 : fderiv ℝ (normalizedSolution ν') z = 0 := fderiv_zero_of_not_differentiableAt hnd
    have hdz : dz (normalizedSolution ν') z = 0 := by
      show (fderiv ℝ (normalizedSolution ν') z 1 - I * fderiv ℝ (normalizedSolution ν') z I) / 2 = 0
      rw [h0]
      simp
    have hdzb : dzbar (normalizedSolution ν') z = 0 := by
      show (fderiv ℝ (normalizedSolution ν') z 1 + I * fderiv ℝ (normalizedSolution ν') z I) / 2 = 0
      rw [h0]
      simp
    rw [hdz, hdzb] at hJG
    simp at hJG
  -- both maps solve the same equation on `D`
  set D := ball z (R / 4) with hD
  have hDo : IsOpen D := isOpen_ball
  have hzD : z ∈ D := mem_ball_self (by positivity)
  have hχ1 : ∀ u ∈ D, ν' u = ν u := by
    intro u hu
    show χ u * ν u = ν u
    rw [hχ]
    simp only
    rw [b.one_of_mem_closedBall (ball_subset_closedBall hu)]
    simp
  have hν'B : IsBeltramiCoeff ν' univ k :=
    ⟨hν's.continuous.aestronglyMeasurable, Eventually.of_forall fun u => hν'b u⟩
  obtain ⟨f, hf, hfK, -⟩ := thm13_7_normalized_existence hk0 hk1 hν
  obtain ⟨F, hF, hFK, -⟩ := thm13_7_normalized_existence hk0 hk1 hν'B
  have hw : normalizedSolution ν = f := QCV.qcv_ns_eq hk0 hk1 hν hf
  have hG : normalizedSolution ν' = F := QCV.qcv_ns_eq hk0 hk1 hν'B hF
  have hwgen : IsGenHomeoSolution f ν D 2 := wr_d3_gen hfK hDo (ae_restrict_of_ae hf.2.2.2.2)
  have hGgen : IsGenHomeoSolution F ν D 2 := by
    refine wr_d3_gen hFK hDo ?_
    filter_upwards [ae_restrict_of_ae hF.2.2.2.2, ae_restrict_mem hDo.measurableSet] with u h1 h2
    rw [h1, hχ1 u h2]
  have hμD : IsBeltramiCoeff ν D k := by
    have hm := hν.1
    rw [Measure.restrict_univ] at hm
    exact ⟨hm.restrict, ae_restrict_of_ae hνae⟩
  obtain ⟨φ, ⟨hφd, hφi, -⟩, hφ⟩ := same_dilatation_conformal hDo hk1 hμD hGgen hwgen
  have hFo : IsOpen (F '' D) := isOpen_image_of_isKQC (t3b_isKQC_restrict hFK hDo (subset_univ _))
  have hFz : F z ∈ F '' D := mem_image_of_mem F hzD
  have hφa : DifferentiableAt ℂ φ (F z) := hφd.differentiableAt (hFo.mem_nhds hFz)
  have hφ' : deriv φ (F z) ≠ 0 := deriv_ne_zero_of_injOn hFo hφd hφi hFz
  have hev : f =ᶠ[𝓝 z] φ ∘ F := Filter.eventually_of_mem (hDo.mem_nhds hzD) fun u hu => hφ u hu
  have hfd : fderiv ℝ f z = fderiv ℝ (φ ∘ F) z := hev.fderiv_eq
  rw [hG] at hGd hJG
  obtain ⟨e1, e2⟩ := eq6_5 hGd hφa
  have hdz : dz f z = dz (φ ∘ F) z := by
    show (fderiv ℝ f z 1 - I * fderiv ℝ f z I) / 2 = (fderiv ℝ (φ ∘ F) z 1 - I * fderiv ℝ (φ ∘ F) z I) / 2
    rw [hfd]
  have hdzb : dzbar f z = dzbar (φ ∘ F) z := by
    show (fderiv ℝ f z 1 + I * fderiv ℝ f z I) / 2 = (fderiv ℝ (φ ∘ F) z 1 + I * fderiv ℝ (φ ∘ F) z I) / 2
    rw [hfd]
  rw [hw, hdz, hdzb, e1, e2, norm_mul, norm_mul, mul_pow, mul_pow, ← mul_sub]
  exact mul_pos (pow_pos (norm_pos_iff.2 hφ') 2) hJG


/-! ## D2 split (2026-10-27): frozen sub-stubs D2a, D2b, and D2 assembled from them. -/

/-- Continuity of the `0`-th iterated derivative is continuity of the map. -/
theorem wr_d2a_zero {X E F : Type} [TopologicalSpace X] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {S : Set X} {U : Set E} {a : X → E → F}
    (h : ContinuousOn (fun p : X × E => iteratedFDeriv ℝ 0 (a p.1) p.2) (S ×ˢ U)) :
    ContinuousOn (fun p : X × E => a p.1 p.2) (S ×ˢ U) := by
  refine ((continuousMultilinearCurryFin0 ℝ E F).continuous.comp_continuousOn h).congr fun p _ => ?_
  show a p.1 p.2 = continuousMultilinearCurryFin0 ℝ E F (iteratedFDeriv ℝ 0 (a p.1) p.2)
  rw [iteratedFDeriv_zero_eq_comp]
  simp

/-- From the iterated derivatives of `a x` to those of `L ∘ D(a x)`, jointly continuous in the parameter. -/
theorem wr_d2a_der {X E F H : Type} [TopologicalSpace X] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup H] [NormedSpace ℝ H] {S : Set X} {U : Set E}
    (hU : IsOpen U) {a : X → E → F} {n : ℕ} (ha : ∀ x ∈ S, ContDiffOn ℝ (n + 1 : ℕ) (a x) U)
    (hac : ∀ i ≤ n + 1, ContinuousOn (fun p : X × E => iteratedFDeriv ℝ i (a p.1) p.2) (S ×ˢ U))
    (L : (E →L[ℝ] F) →L[ℝ] H) :
    (∀ x ∈ S, ContDiffOn ℝ n (fun y => L (fderiv ℝ (a x) y)) U) ∧
      ∀ i ≤ n, ContinuousOn (fun p : X × E => iteratedFDeriv ℝ i (fun y => L (fderiv ℝ (a p.1) y)) p.2)
        (S ×ˢ U) := by
  have hd : ∀ x ∈ S, ContDiffOn ℝ n (fderiv ℝ (a x)) U := fun x hx =>
    (ha x hx).fderiv_of_isOpen hU (by push_cast; exact le_rfl)
  refine ⟨fun x hx => L.contDiff.comp_contDiffOn (hd x hx), fun i hi => ?_⟩
  have hc := hac (i + 1) (by omega)
  have hE := ((ContinuousLinearMap.compContinuousMultilinearMapL ℝ (fun _ : Fin i => E) _ H L).continuous.comp
    (continuousMultilinearCurryRightEquiv' ℝ i E F).continuous).comp_continuousOn hc
  refine hE.congr fun p hp => ?_
  have hat : ContDiffAt ℝ n (fderiv ℝ (a p.1)) p.2 := (hd p.1 hp.1).contDiffAt (hU.mem_nhds hp.2)
  show iteratedFDeriv ℝ i (L ∘ fderiv ℝ (a p.1)) p.2 =
    L.compContinuousMultilinearMap ((continuousMultilinearCurryRightEquiv' ℝ i E F)
      (iteratedFDeriv ℝ (i + 1) (a p.1) p.2))
  rw [L.iteratedFDeriv_comp_left hat (by exact_mod_cast hi), iteratedFDeriv_succ_eq_comp_right,
    Function.comp_apply]
  exact congrArg _ ((continuousMultilinearCurryRightEquiv' ℝ i E F).apply_symm_apply _).symm

/-- **Separate variables.** If the iterated derivatives of `a x` and `b x` are jointly continuous in the parameter,
so are those of `y ↦ B (a x y.1) (b x y.2)`. -/
theorem wr_d2a_sep {X : Type} [TopologicalSpace X] {S : Set X} {E₁ E₂ : Type} [NormedAddCommGroup E₁]
    [NormedSpace ℝ E₁] [NormedAddCommGroup E₂] [NormedSpace ℝ E₂] {U₁ : Set E₁} {U₂ : Set E₂} (hU₁ : IsOpen U₁)
    (hU₂ : IsOpen U₂) (n : ℕ) :
    ∀ {F₁ F₂ G : Type} [NormedAddCommGroup F₁] [NormedSpace ℝ F₁] [NormedAddCommGroup F₂] [NormedSpace ℝ F₂]
      [NormedAddCommGroup G] [NormedSpace ℝ G] (B : F₁ →L[ℝ] F₂ →L[ℝ] G) {a : X → E₁ → F₁} {b : X → E₂ → F₂},
      (∀ x ∈ S, ContDiffOn ℝ n (a x) U₁) → (∀ x ∈ S, ContDiffOn ℝ n (b x) U₂) →
      (∀ i ≤ n, ContinuousOn (fun p : X × E₁ => iteratedFDeriv ℝ i (a p.1) p.2) (S ×ˢ U₁)) →
      (∀ i ≤ n, ContinuousOn (fun p : X × E₂ => iteratedFDeriv ℝ i (b p.1) p.2) (S ×ˢ U₂)) →
      ContinuousOn (fun p : X × (E₁ × E₂) => iteratedFDeriv ℝ n (fun y : E₁ × E₂ => B (a p.1 y.1) (b p.1 y.2)) p.2)
        (S ×ˢ (U₁ ×ˢ U₂)) := by
  induction n with
  | zero =>
    intro F₁ F₂ G _ _ _ _ _ _ B a b _ _ hac hbc
    have h1 := wr_d2a_zero (hac 0 le_rfl)
    have h2 := wr_d2a_zero (hbc 0 le_rfl)
    have h1' : ContinuousOn (fun p : X × (E₁ × E₂) => a p.1 p.2.1) (S ×ˢ (U₁ ×ˢ U₂)) :=
      h1.comp (continuous_fst.prodMk (continuous_fst.comp continuous_snd)).continuousOn
        fun p hp => ⟨hp.1, hp.2.1⟩
    have h2' : ContinuousOn (fun p : X × (E₁ × E₂) => b p.1 p.2.2) (S ×ˢ (U₁ ×ˢ U₂)) :=
      h2.comp (continuous_fst.prodMk (continuous_snd.comp continuous_snd)).continuousOn
        fun p hp => ⟨hp.1, hp.2.2⟩
    have hB : ContinuousOn (fun p : X × (E₁ × E₂) => B (a p.1 p.2.1) (b p.1 p.2.2)) (S ×ˢ (U₁ ×ˢ U₂)) :=
      (B.continuous₂.comp_continuousOn (h1'.prodMk h2'))
    exact ((continuousMultilinearCurryFin0 ℝ (E₁ × E₂) G).symm.continuous.comp_continuousOn hB).congr
      fun p _ => rfl
  | succ n ih =>
    intro F₁ F₂ G _ _ _ _ _ _ B a b ha hb hac hbc
    set L₁ : (E₁ →L[ℝ] F₁) →L[ℝ] (E₁ × E₂ →L[ℝ] F₁) :=
      (ContinuousLinearMap.compL ℝ (E₁ × E₂) E₁ F₁).flip (ContinuousLinearMap.fst ℝ E₁ E₂) with hL₁
    set L₂ : (E₂ →L[ℝ] F₂) →L[ℝ] (E₁ × E₂ →L[ℝ] F₂) :=
      (ContinuousLinearMap.compL ℝ (E₁ × E₂) E₂ F₂).flip (ContinuousLinearMap.snd ℝ E₁ E₂) with hL₂
    obtain ⟨ha', hac'⟩ := wr_d2a_der hU₁ ha hac L₁
    obtain ⟨hb', hbc'⟩ := wr_d2a_der hU₂ hb hbc L₂
    have han : ∀ x ∈ S, ContDiffOn ℝ n (a x) U₁ := fun x hx => (ha x hx).of_le (by exact_mod_cast Nat.le_succ n)
    have hbn : ∀ x ∈ S, ContDiffOn ℝ n (b x) U₂ := fun x hx => (hb x hx).of_le (by exact_mod_cast Nat.le_succ n)
    have hacn : ∀ i ≤ n, ContinuousOn (fun p : X × E₁ => iteratedFDeriv ℝ i (a p.1) p.2) (S ×ˢ U₁) :=
      fun i hi => hac i (by omega)
    have hbcn : ∀ i ≤ n, ContinuousOn (fun p : X × E₂ => iteratedFDeriv ℝ i (b p.1) p.2) (S ×ˢ U₂) :=
      fun i hi => hbc i (by omega)
    have I1 := ih (B.precompR (E₁ × E₂)) (a := a) (b := fun x y => L₂ (fderiv ℝ (b x) y)) han hb' hacn hbc'
    have I2 := ih (B.precompL (E₁ × E₂)) (a := fun x y => L₁ (fderiv ℝ (a x) y)) (b := b) ha' hbn hac' hbcn
    refine ((continuousMultilinearCurryRightEquiv' ℝ n (E₁ × E₂) G).symm.continuous.comp_continuousOn
      (I1.add I2)).congr fun p hp => ?_
    obtain ⟨hpS, hp1, hp2⟩ := hp
    have hda : ∀ y ∈ U₁ ×ˢ U₂, HasFDerivAt (fun y : E₁ × E₂ => a p.1 y.1) (L₁ (fderiv ℝ (a p.1) y.1)) y := by
      intro y hy
      have h := ((ha p.1 hpS).differentiableOn (by simp) y.1 hy.1).differentiableAt (hU₁.mem_nhds hy.1)
      exact h.hasFDerivAt.comp y (hasFDerivAt_fst)
    have hdb : ∀ y ∈ U₁ ×ˢ U₂, HasFDerivAt (fun y : E₁ × E₂ => b p.1 y.2) (L₂ (fderiv ℝ (b p.1) y.2)) y := by
      intro y hy
      have h := ((hb p.1 hpS).differentiableOn (by simp) y.2 hy.2).differentiableAt (hU₂.mem_nhds hy.2)
      exact h.hasFDerivAt.comp y (hasFDerivAt_snd)
    have hev : (fun y => fderiv ℝ (fun y : E₁ × E₂ => B (a p.1 y.1) (b p.1 y.2)) y) =ᶠ[𝓝 p.2]
        fun y => B.precompR (E₁ × E₂) (a p.1 y.1) (L₂ (fderiv ℝ (b p.1) y.2)) +
          B.precompL (E₁ × E₂) (L₁ (fderiv ℝ (a p.1) y.1)) (b p.1 y.2) := by
      filter_upwards [(hU₁.prod hU₂).mem_nhds ⟨hp1, hp2⟩] with y hy
      rw [B.fderiv_of_bilinear (hda y hy).differentiableAt (hdb y hy).differentiableAt, (hda y hy).fderiv,
        (hdb y hy).fderiv]
    have hA : ∀ {F' : Type} [NormedAddCommGroup F'] [NormedSpace ℝ F'] {c : E₁ → F'},
        ContDiffOn ℝ n c U₁ → ContDiffAt ℝ n (fun y : E₁ × E₂ => c y.1) p.2 := fun hc =>
      (hc.contDiffAt (hU₁.mem_nhds hp1)).comp p.2 contDiffAt_fst
    have hB' : ∀ {F' : Type} [NormedAddCommGroup F'] [NormedSpace ℝ F'] {c : E₂ → F'},
        ContDiffOn ℝ n c U₂ → ContDiffAt ℝ n (fun y : E₁ × E₂ => c y.2) p.2 := fun hc =>
      (hc.contDiffAt (hU₂.mem_nhds hp2)).comp p.2 contDiffAt_snd
    have hc1 : ContDiffAt ℝ n (fun y : E₁ × E₂ => B.precompR (E₁ × E₂) (a p.1 y.1) (L₂ (fderiv ℝ (b p.1) y.2))) p.2 :=
      (B.precompR (E₁ × E₂)).isBoundedBilinearMap.contDiff.contDiffAt.comp p.2
        ((hA (han p.1 hpS)).prodMk (hB' (hb' p.1 hpS)))
    have hpair : ContDiffAt ℝ n (fun y : E₁ × E₂ => (L₁ (fderiv ℝ (a p.1) y.1), b p.1 y.2)) p.2 :=
      (hA (ha' p.1 hpS)).prodMk (hB' (hbn p.1 hpS))
    have hbil : ContDiff ℝ n (fun q : (E₁ × E₂ →L[ℝ] F₁) × F₂ => B.precompL (E₁ × E₂) q.1 q.2) :=
      (B.precompL (E₁ × E₂)).isBoundedBilinearMap.contDiff
    have hc2 : ContDiffAt ℝ n (fun y : E₁ × E₂ => B.precompL (E₁ × E₂) (L₁ (fderiv ℝ (a p.1) y.1)) (b p.1 y.2)) p.2 :=
      ContDiffAt.comp (g := fun q : (E₁ × E₂ →L[ℝ] F₁) × F₂ => B.precompL (E₁ × E₂) q.1 q.2)
        (f := fun y : E₁ × E₂ => (L₁ (fderiv ℝ (a p.1) y.1), b p.1 y.2)) p.2 hbil.contDiffAt hpair
    show iteratedFDeriv ℝ (n + 1) (fun y : E₁ × E₂ => B (a p.1 y.1) (b p.1 y.2)) p.2 = _
    rw [iteratedFDeriv_succ_eq_comp_right, Function.comp_apply, (hev.iteratedFDeriv ℝ n).eq_of_nhds,
      fun_iteratedFDeriv_add_apply hc1 hc2]
    rfl

/-- The Cauchy-kernel factor `a(q, P) = A(q) · ((P - q).1 (P - q).2)⁻¹`, for `q` on the torus and `P` in the half
bidisc: smooth in `P`, with `P`-iterated derivatives jointly continuous. -/
theorem wr_d2a_kernel {c : ℂ × ℂ} {r : ℝ} (hr : 0 < r) (A : ℂ × ℂ → ℂ) (hA : Continuous A) (j : ℕ) :
    (∀ q ∈ sphere c.1 r ×ˢ sphere c.2 r, ContDiffOn ℝ j (fun P : ℂ × ℂ => A q * ((P - q).1 * (P - q).2)⁻¹)
      (ball c (r / 2))) ∧
    ∀ i ≤ j, ContinuousOn (fun p : (ℂ × ℂ) × (ℂ × ℂ) =>
      iteratedFDeriv ℝ i (fun P : ℂ × ℂ => A p.1 * ((P - p.1).1 * (P - p.1).2)⁻¹) p.2)
      ((sphere c.1 r ×ˢ sphere c.2 r) ×ˢ ball c (r / 2)) := by
  have _hr := hr
  have hO : IsOpen {w : ℂ × ℂ | w.1 ≠ 0 ∧ w.2 ≠ 0} :=
    (isOpen_ne_fun continuous_fst continuous_const).inter (isOpen_ne_fun continuous_snd continuous_const)
  have hk : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun w : ℂ × ℂ => (w.1 * w.2)⁻¹)
      {w : ℂ × ℂ | w.1 ≠ 0 ∧ w.2 ≠ 0} :=
    fun w hw => ((contDiff_fst.mul contDiff_snd).contDiffAt.inv (mul_ne_zero hw.1 hw.2)).contDiffWithinAt
  have hkc : ∀ i : ℕ, ContinuousOn (iteratedFDeriv ℝ i (fun w : ℂ × ℂ => (w.1 * w.2)⁻¹))
      {w : ℂ × ℂ | w.1 ≠ 0 ∧ w.2 ≠ 0} := fun i =>
    (hk.continuousOn_iteratedFDerivWithin (by exact_mod_cast le_top) hO.uniqueDiffOn).congr
      fun w hw => (iteratedFDerivWithin_of_isOpen i hO hw).symm
  have hTO : ∀ q ∈ sphere c.1 r ×ˢ sphere c.2 r, ∀ P ∈ ball c (r / 2),
      P - q ∈ {w : ℂ × ℂ | w.1 ≠ 0 ∧ w.2 ≠ 0} := by
    intro q hq P hP
    rw [mem_ball, Prod.dist_eq, max_lt_iff] at hP
    have hq1 : dist q.1 c.1 = r := hq.1
    have hq2 : dist q.2 c.2 = r := hq.2
    refine ⟨fun h => ?_, fun h => ?_⟩
    · have : P.1 = q.1 := sub_eq_zero.mp h
      rw [this, hq1] at hP; linarith [hP.1]
    · have : P.2 = q.2 := sub_eq_zero.mp h
      rw [this, hq2] at hP; linarith [hP.2]
  have hkd : ∀ q ∈ sphere c.1 r ×ˢ sphere c.2 r, ∀ P ∈ ball c (r / 2),
      ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun P : ℂ × ℂ => ((P - q).1 * (P - q).2)⁻¹) P := by
    intro q hq P hP
    have h := hTO q hq P hP
    exact ContDiffAt.comp (g := fun w : ℂ × ℂ => (w.1 * w.2)⁻¹) (f := fun P : ℂ × ℂ => P - q) P
      ((contDiff_fst.mul contDiff_snd).contDiffAt.inv (mul_ne_zero h.1 h.2)) (contDiffAt_id.sub contDiffAt_const)
  have hform : ∀ i : ℕ, ∀ q ∈ sphere c.1 r ×ˢ sphere c.2 r, ∀ P ∈ ball c (r / 2),
      iteratedFDeriv ℝ i (fun P : ℂ × ℂ => A q * ((P - q).1 * (P - q).2)⁻¹) P =
        A q • iteratedFDeriv ℝ i (fun w : ℂ × ℂ => (w.1 * w.2)⁻¹) (P - q) := by
    intro i q hq P hP
    show iteratedFDeriv ℝ i (fun P : ℂ × ℂ => A q • (fun w : ℂ × ℂ => (w.1 * w.2)⁻¹) (P - q)) P = _
    have hs := iteratedFDeriv_comp_sub (𝕜 := ℝ) (f := fun w : ℂ × ℂ => (w.1 * w.2)⁻¹) i q P
    rw [iteratedFDeriv_const_smul_apply' ((hkd q hq P hP).of_le (by exact_mod_cast le_top)), hs]
  refine ⟨fun q hq P hP =>
    (contDiffAt_const.mul ((hkd q hq P hP).of_le (by exact_mod_cast le_top))).contDiffWithinAt, fun i _ => ?_⟩
  haveI : ContinuousSMul ℂ (ContinuousMultilinearMap ℝ (fun _ : Fin i => ℂ × ℂ) ℂ) :=
    IsBoundedSMul.continuousSMul
  have h1 : ContinuousOn (fun p : (ℂ × ℂ) × (ℂ × ℂ) =>
      A p.1 • iteratedFDeriv ℝ i (fun w : ℂ × ℂ => (w.1 * w.2)⁻¹) (p.2 - p.1))
      ((sphere c.1 r ×ˢ sphere c.2 r) ×ˢ ball c (r / 2)) :=
    (hA.comp continuous_fst).continuousOn.smul ((hkc i).comp (continuous_snd.sub continuous_fst).continuousOn
      fun p hp => hTO p.1 hp.1 p.2 hp.2)
  exact h1.congr fun p hp => hform i p.1 hp.1 p.2 hp.2

/-- (D2a) `[W2]` **Joint `C³` from holomorphy in the parameter and `z`-regularity.** Suppose `u(P, z)`
- is separately holomorphic in `P.1` and in `P.2` on the slices of `W`,
- is jointly continuous on `W ×ˢ Ω`,
- is `C³` in `z` on `Ω` for each `P`, with `z`-iterated derivatives of order `≤ 3` jointly continuous.

Then `u` is jointly `C³` on `W ×ˢ Ω`. Route: the bidisc Cauchy formula in `P` (B2, `wr_bidisc_contDiffOn`), then
differentiation under the torus integral of `K(Q, P) · u(Q, z)`. -/
theorem wr_joint_of_holo_param {u : ℂ × ℂ → ℂ → ℂ} {W : Set (ℂ × ℂ)} (hW : IsOpen W) {Ω : Set ℂ}
    (hΩ : IsOpen Ω)
    (h₁ : ∀ z ∈ Ω, ∀ b : ℂ, DifferentiableOn ℂ (fun a => u (a, b) z) {a | (a, b) ∈ W})
    (h₂ : ∀ z ∈ Ω, ∀ a : ℂ, DifferentiableOn ℂ (fun b => u (a, b) z) {b | (a, b) ∈ W})
    (hc : ContinuousOn (fun q : (ℂ × ℂ) × ℂ => u q.1 q.2) (W ×ˢ Ω))
    (hz : ∀ P ∈ W, ContDiffOn ℝ 3 (u P) Ω)
    (hzc : ∀ j ≤ 3, ContinuousOn (fun q : (ℂ × ℂ) × ℂ => iteratedFDeriv ℝ j (u q.1) q.2) (W ×ˢ Ω)) :
    ContDiffOn ℝ 3 (fun q : (ℂ × ℂ) × ℂ => u q.1 q.2) (W ×ˢ Ω) := by
  refine contDiffOn_of_locally_contDiffOn fun q₀ hq₀ => ?_
  obtain ⟨hP₀, hz₀⟩ := hq₀
  set c := q₀.1 with hcdef
  obtain ⟨R, hR, hRW⟩ := Metric.isOpen_iff.1 hW c hP₀
  set r := R / 2 with hrdef
  have hr : 0 < r := by positivity
  have hsub : closedBall c.1 r ×ˢ closedBall c.2 r ⊆ W := by
    intro P hP
    apply hRW
    rw [mem_ball, Prod.dist_eq, max_lt_iff]
    exact ⟨lt_of_le_of_lt hP.1 (by linarith), lt_of_le_of_lt hP.2 (by linarith)⟩
  set T := sphere c.1 r ×ˢ sphere c.2 r with hTdef
  have hTW : T ⊆ W := fun q hq => hsub ⟨sphere_subset_closedBall hq.1, sphere_subset_closedBall hq.2⟩
  have hTc : IsCompact T := (isCompact_sphere _ _).prod (isCompact_sphere _ _)
  set U₁ := ball c (r / 2) with hU₁
  set U := U₁ ×ˢ Ω with hUdef
  have hUo : IsOpen U := isOpen_ball.prod hΩ
  -- the integrand `Φ q (P, z) = (A q · k(P - q)) · u(q, z)`
  set A : ℂ × ℂ → ℂ := fun q => (q.1 - c.1) * I * ((q.2 - c.2) * I) with hAdef
  have hA : Continuous A := by
    rw [hAdef]
    fun_prop
  set a : ℂ × ℂ → ℂ × ℂ → ℂ := fun q P => A q * ((P - q).1 * (P - q).2)⁻¹ with hadef
  have hK := fun j => wr_d2a_kernel (c := c) hr A hA j
  have hsep : ∀ j ≤ 3, ContinuousOn (fun p : (ℂ × ℂ) × ((ℂ × ℂ) × ℂ) =>
      iteratedFDeriv ℝ j (fun y : (ℂ × ℂ) × ℂ => ContinuousLinearMap.mul ℝ ℂ (a p.1 y.1) (u p.1 y.2)) p.2)
      (T ×ˢ U) := by
    intro j hj
    exact wr_d2a_sep (S := T) isOpen_ball hΩ j (ContinuousLinearMap.mul ℝ ℂ) (a := a) (b := u) (hK j).1
      (fun q hq => (hz q (hTW hq)).of_le (by exact_mod_cast hj)) (hK j).2
      (fun i hi => (hzc i (hi.trans hj)).mono (prod_mono hTW subset_rfl))
  -- the torus parametrization
  set qm : ℝ × ℝ → ℂ × ℂ := fun x => (circleMap c.1 r x.1, circleMap c.2 r x.2) with hqm
  have hqc : Continuous qm := ((continuous_circleMap _ _).comp continuous_fst).prodMk
    ((continuous_circleMap _ _).comp continuous_snd)
  have hqT : ∀ x, qm x ∈ T := fun x => ⟨circleMap_mem_sphere _ hr.le _, circleMap_mem_sphere _ hr.le _⟩
  set F : ℝ × ℝ → (ℂ × ℂ) × ℂ → ℂ := fun x y => ContinuousLinearMap.mul ℝ ℂ (a (qm x) y.1) (u (qm x) y.2)
    with hFdef
  set μI : Measure ℝ := volume.restrict (Ioc 0 (2 * π)) with hμI
  have : IsFiniteMeasure μI := isFiniteMeasure_restrict.mpr measure_Ioc_lt_top.ne
  have hI : ContDiffOn ℝ ((3 : ℕ) : WithTop ℕ∞) (fun y => ∫ x, F x y ∂(μI.prod μI)) U := by
    refine wr_contDiffOn_integral hUo (fun x => ?_) (fun j hj y hy => ?_) (fun j hj K hK' hKc => ?_)
    · have h1 : ContDiffOn ℝ 3 (fun y : (ℂ × ℂ) × ℂ => a (qm x) y.1) U :=
        ((hK 3).1 _ (hqT x)).comp contDiff_fst.contDiffOn fun y hy => hy.1
      have h2 : ContDiffOn ℝ 3 (fun y : (ℂ × ℂ) × ℂ => u (qm x) y.2) U :=
        (hz _ (hTW (hqT x))).comp contDiff_snd.contDiffOn fun y hy => hy.2
      exact h1.mul h2
    · have hj' : j ≤ 3 := hj
      exact ((hsep j hj').comp_continuous (hqc.prodMk continuous_const)
        fun x => ⟨hqT x, hy⟩).aestronglyMeasurable
    · have hj' : j ≤ 3 := hj
      obtain ⟨C, hC⟩ := (hTc.prod hKc).exists_bound_of_continuousOn
        ((hsep j hj').mono (prod_mono subset_rfl hK'))
      exact ⟨C, fun x y hy => hC (qm x, y) ⟨hqT x, hy⟩⟩
  -- the Cauchy representation
  have h2π : (0 : ℝ) ≤ 2 * π := by positivity
  have hd : ∀ (a' : ℂ) (θ : ℝ), deriv (circleMap a' r) θ = circleMap 0 r θ * I := fun a' θ => deriv_circleMap a' r θ
  have hcont0 := wr_d2a_zero (S := T) (U := U)
    (a := fun q (y : (ℂ × ℂ) × ℂ) => ContinuousLinearMap.mul ℝ ℂ (a q y.1) (u q y.2)) (hsep 0 (by norm_num))
  have hrep : ∀ y ∈ U, u y.1 y.2 = ((2 * π * I)⁻¹) ^ 2 * ∫ x, F x y ∂(μI.prod μI) := by
    rintro y ⟨hy1, hy2⟩
    have hy1' := hy1
    rw [hU₁, mem_ball, Prod.dist_eq, max_lt_iff] at hy1'
    have hp' : y.1 ∈ ball c.1 r ×ˢ ball c.2 r :=
      ⟨by rw [mem_ball]; linarith [hy1'.1], by rw [mem_ball]; linarith [hy1'.2]⟩
    have hcB : ContinuousOn (fun P : ℂ × ℂ => u P y.2) (closedBall c.1 r ×ˢ closedBall c.2 r) :=
      hc.comp (continuous_id.prodMk continuous_const).continuousOn fun P hP => ⟨hsub hP, hy2⟩
    rw [wr_cauchy_bidisc (f := fun P : ℂ × ℂ => u P y.2) hr hr hcB
      (fun b hb => (h₁ y.2 hy2 b).mono fun a' ha' => hsub ⟨ball_subset_closedBall ha', hb⟩)
      (fun a' ha' => (h₂ y.2 hy2 a').mono fun b hb => hsub ⟨ha', ball_subset_closedBall hb⟩) hp']
    congr 1
    have hint : Integrable (fun x => F x y) (μI.prod μI) := by
      obtain ⟨C, hC⟩ := (hTc.prod (isCompact_singleton (x := y))).exists_bound_of_continuousOn
        (hcont0.mono (prod_mono subset_rfl (singleton_subset_iff.2 ⟨hy1, hy2⟩)))
      refine Integrable.of_bound ((hcont0.comp_continuous (hqc.prodMk continuous_const)
        fun x => ⟨hqT x, hy1, hy2⟩).aestronglyMeasurable) C (Eventually.of_forall fun x => ?_)
      exact hC (qm x, y) ⟨hqT x, rfl⟩
    rw [integral_prod _ hint]
    simp only [circleIntegral, smul_eq_mul, hd]
    rw [intervalIntegral.integral_of_le h2π]
    refine integral_congr_ae (Eventually.of_forall fun θ => ?_)
    simp only
    rw [intervalIntegral.integral_of_le h2π, ← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun η => ?_)
    simp only [hFdef, hadef, hAdef, hqm, ContinuousLinearMap.mul_apply', Prod.fst_sub, Prod.snd_sub,
      circleMap_sub_center]
    rw [show (y.1.1 - circleMap c.1 r θ) * (y.1.2 - circleMap c.2 r η) =
      (circleMap c.1 r θ - y.1.1) * (circleMap c.2 r η - y.1.2) by ring]
    ring
  refine ⟨U, hUo, ⟨mem_ball_self (by positivity), hz₀⟩, ?_⟩
  exact ((contDiffOn_const.mul (by exact_mod_cast hI)).congr hrep).mono inter_subset_right


/-! ### D2b helpers: Cauchy-type integrals (下属1) -/

/-- Points of the open disc are off the circle. -/
theorem wr_ball_not_sphere {c ζ : ℂ} {R : ℝ} (hζ : ζ ∈ ball c R) : ζ ∉ sphere c |R| := by
  intro h
  rw [mem_sphere] at h
  rw [mem_ball] at hζ
  have hR : 0 < R := (dist_nonneg).trans_lt hζ
  rw [abs_of_pos hR] at h
  linarith

/-- Derivatives of all orders of a Cauchy-type integral, inside the disc. -/
theorem wr_cauchy_iteratedDeriv {h : ℂ → ℂ} {c : ℂ} {R : ℝ} (hR : 0 < R) (hh : ContinuousOn h (sphere c R))
    (k : ℕ) {ζ : ℂ} (hζ : ζ ∈ ball c R) :
    iteratedDeriv k (fun ζ => ∮ ξ in C(c, R), (ξ - ζ) ^ (-1 : ℤ) • h ξ) ζ =
      ((k.factorial : ℕ) : ℂ) • ∮ ξ in C(c, R), (ξ - ζ) ^ (-((k : ℤ) + 1)) • h ξ := by
  have hci : CircleIntegrable h c R := hh.circleIntegrable hR.le
  induction k generalizing ζ with
  | zero => simp
  | succ k ih =>
    rw [iteratedDeriv_succ]
    have hev : iteratedDeriv k (fun ζ => ∮ ξ in C(c, R), (ξ - ζ) ^ (-1 : ℤ) • h ξ) =ᶠ[𝓝 ζ]
        fun ζ => ((k.factorial : ℕ) : ℂ) • ∮ ξ in C(c, R), (ξ - ζ) ^ (-((k : ℤ) + 1)) • h ξ := by
      filter_upwards [isOpen_ball.mem_nhds hζ] with y hy
      exact ih hy
    rw [hev.deriv_eq]
    have hd : HasDerivAt (fun ζ => ((k.factorial : ℕ) : ℂ) • ∮ ξ in C(c, R), (ξ - ζ) ^ (-((k : ℤ) + 1)) • h ξ)
        (((k.factorial : ℕ) : ℂ) • ((-(((-((k : ℤ) + 1) : ℤ)) : ℂ)) •
          ∮ ξ in C(c, R), (ξ - ζ) ^ (-((k : ℤ) + 1) - 1) • h ξ)) ζ :=
      (hasDerivAt_circleIntegral_sub_zpow_smul (n := -((k : ℤ) + 1)) hci
        (wr_ball_not_sphere hζ)).const_smul (((k.factorial : ℕ) : ℂ))
    rw [hd.deriv]
    have e : -((k : ℤ) + 1) - 1 = -(((k + 1 : ℕ) : ℤ) + 1) := by push_cast; ring
    rw [e, smul_smul]
    congr 1
    push_cast [Nat.factorial_succ]
    ring

/-- A Cauchy-type integral is holomorphic inside the disc. -/
theorem wr_cauchy_diffOn {h : ℂ → ℂ} {c : ℂ} {R : ℝ} (hR : 0 < R) (hh : ContinuousOn h (sphere c R)) :
    DifferentiableOn ℂ (fun ζ => ∮ ξ in C(c, R), (ξ - ζ) ^ (-1 : ℤ) • h ξ) (ball c R) := fun ζ hζ =>
  (hasDerivAt_circleIntegral_sub_zpow_smul (hh.circleIntegrable hR.le)
    (wr_ball_not_sphere hζ)).differentiableAt.differentiableWithinAt

/-- Joint continuity of parametric Cauchy-type integrals inside the disc. -/
theorem wr_param_circ_cont {X : Type*} [TopologicalSpace X] {S : Set X} {h : X → ℂ → ℂ} {c : ℂ} {R : ℝ}
    (hR : 0 < R) (hh : ContinuousOn (fun p : X × ℂ => h p.1 p.2) (S ×ˢ sphere c R)) (n : ℤ) :
    ContinuousOn (fun p : X × ℂ => ∮ ξ in C(c, R), (ξ - p.2) ^ n • h p.1 ξ) (S ×ˢ ball c R) := by
  rw [continuousOn_iff_continuous_domRestrict]
  simp only [circleIntegral]
  apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
  have hne : ∀ (x : ↥(S ×ˢ ball c R)) (θ : ℝ), circleMap c R θ - (x : X × ℂ).2 ≠ 0 := by
    intro x θ heq
    have hx := x.2.2
    rw [mem_ball] at hx
    have hc : dist (circleMap c R θ) c = R := by
      rw [dist_eq_norm, circleMap_sub_center, norm_circleMap_zero, abs_of_pos hR]
    rw [sub_eq_zero] at heq
    rw [← heq] at hx
    linarith
  have hhc : Continuous (fun q : ↥(S ×ˢ ball c R) × ℝ => h (q.1 : X × ℂ).1 (circleMap c R q.2)) := by
    have hmap : Continuous (fun q : ↥(S ×ˢ ball c R) × ℝ => ((q.1 : X × ℂ).1, circleMap c R q.2)) :=
      (continuous_fst.comp (continuous_subtype_val.comp continuous_fst)).prodMk
        ((continuous_circleMap c R).comp continuous_snd)
    exact hh.comp_continuous hmap (fun q => ⟨q.1.2.1, circleMap_mem_sphere c hR.le q.2⟩)
  have hz : Continuous (fun q : ↥(S ×ˢ ball c R) × ℝ => (circleMap c R q.2 - (q.1 : X × ℂ).2) ^ n) := by
    refine Continuous.zpow₀ (((continuous_circleMap c R).comp continuous_snd).sub
      (continuous_snd.comp (continuous_subtype_val.comp continuous_fst))) n (fun q => Or.inl (hne q.1 q.2))
  have hd : Continuous (fun q : ↥(S ×ˢ ball c R) × ℝ => deriv (circleMap c R) q.2) := by
    simp only [deriv_circleMap]
    exact ((continuous_circleMap 0 R).comp continuous_snd).mul continuous_const
  exact hd.smul (hz.smul hhc)

/-- Real iterated derivatives of a parametric Cauchy-type integral are jointly continuous inside the disc. -/
theorem wr_param_cauchy_iter_cont {X : Type*} [TopologicalSpace X] {S : Set X} {h : X → ℂ → ℂ} {c : ℂ} {R : ℝ}
    (hR : 0 < R) (hh : ContinuousOn (fun p : X × ℂ => h p.1 p.2) (S ×ˢ sphere c R)) (k : ℕ) :
    ContinuousOn (fun p : X × ℂ =>
      iteratedFDeriv ℝ k (fun ζ => ∮ ξ in C(c, R), (ξ - ζ) ^ (-1 : ℤ) • h p.1 ξ) p.2) (S ×ˢ ball c R) := by
  have hhx : ∀ x ∈ S, ContinuousOn (h x) (sphere c R) := fun x hx =>
    hh.comp (continuous_const.prodMk continuous_id).continuousOn (fun y hy => ⟨hx, hy⟩)
  have hI := wr_param_circ_cont hR hh (-((k : ℤ) + 1))
  have hI' : ContinuousOn (fun p : X × ℂ =>
      ((k.factorial : ℕ) : ℂ) • ∮ ξ in C(c, R), (ξ - p.2) ^ (-((k : ℤ) + 1)) • h p.1 ξ) (S ×ˢ ball c R) :=
    hI.const_smul (((k.factorial : ℕ) : ℂ))
  have hT : ContinuousOn (fun p : X × ℂ => (ContinuousMultilinearMap.restrictScalarsₗᵢ ℝ)
      (ContinuousMultilinearMap.piFieldEquiv ℂ (Fin k) ℂ
        (((k.factorial : ℕ) : ℂ) • ∮ ξ in C(c, R), (ξ - p.2) ^ (-((k : ℤ) + 1)) • h p.1 ξ)))
      (S ×ˢ ball c R) :=
    (ContinuousMultilinearMap.restrictScalarsₗᵢ ℝ).continuous.comp_continuousOn
      ((ContinuousMultilinearMap.piFieldEquiv ℂ (Fin k) ℂ).continuous.comp_continuousOn
        hI')
  refine hT.congr ?_
  intro p hp
  have hcd : ContDiffAt ℂ k (fun ζ => ∮ ξ in C(c, R), (ξ - ζ) ^ (-1 : ℤ) • h p.1 ξ) p.2 :=
    ((wr_cauchy_diffOn hR (hhx p.1 hp.1)).contDiffOn isOpen_ball).contDiffAt (isOpen_ball.mem_nhds hp.2)
  show iteratedFDeriv ℝ k (fun ζ => ∮ ξ in C(c, R), (ξ - ζ) ^ (-1 : ℤ) • h p.1 ξ) p.2 = _
  rw [← hcd.restrictScalars_iteratedFDeriv, Function.comp_apply, iteratedFDeriv_eq_equiv_comp,
    Function.comp_apply, wr_cauchy_iteratedDeriv hR (hhx p.1 hp.1) k hp.2]
  rfl


/-- Rewriting the Cauchy integral of D1 in the `zpow • ` form. -/
theorem wr_cauchy_form (g : ℂ → ℂ) (c ζ : ℂ) (R : ℝ) :
    (2 * π * I)⁻¹ * ∮ ξ in C(c, R), g ξ / (ξ - ζ) =
      ∮ ξ in C(c, R), (ξ - ζ) ^ (-1 : ℤ) • ((2 * π * I)⁻¹ * g ξ) := by
  have e : (fun ξ => (ξ - ζ) ^ (-1 : ℤ) • ((2 * π * I)⁻¹ * g ξ)) =
      fun ξ => (2 * π * I)⁻¹ • (g ξ / (ξ - ζ)) := by
    funext ξ
    simp only [zpow_neg_one, smul_eq_mul]
    ring
  rw [e, circleIntegral.integral_smul, smul_eq_mul]

/-- Joint continuity of the `z`-derivatives of `H ∘ G` through Faà di Bruno, for a family `H` with jointly
continuous derivatives and a family `G` with jointly continuous `z`-derivatives. -/
theorem wr_comp_iter_cont {X : Type*} [TopologicalSpace X] {S : Set X} {U T : Set ℂ} {H G : X → ℂ → ℂ} {j : ℕ}
    (hH : ∀ k ≤ j, ContinuousOn (fun p : X × ℂ => iteratedFDeriv ℝ k (H p.1) p.2) (S ×ˢ T))
    (hG : ∀ k ≤ j, ContinuousOn (fun p : X × ℂ => iteratedFDeriv ℝ k (G p.1) p.2) (S ×ˢ U))
    (hGv : ContinuousOn (fun p : X × ℂ => G p.1 p.2) (S ×ˢ U))
    (hmaps : ∀ p ∈ S ×ˢ U, G p.1 p.2 ∈ T) :
    ContinuousOn (fun p : X × ℂ => ∑ c : OrderedFinpartition j,
      c.compAlongOrderedFinpartition (iteratedFDeriv ℝ c.length (H p.1) (G p.1 p.2))
        (fun m => iteratedFDeriv ℝ (c.partSize m) (G p.1) p.2)) (S ×ˢ U) := by
  apply continuousOn_finset_sum
  intro c _
  have hA : ContinuousOn (fun p : X × ℂ => iteratedFDeriv ℝ c.length (H p.1) (G p.1 p.2)) (S ×ˢ U) := by
    have hmap : ContinuousOn (fun p : X × ℂ => (p.1, G p.1 p.2)) (S ×ˢ U) :=
      continuous_fst.continuousOn.prodMk hGv
    exact (hH c.length c.length_le).comp hmap (fun p hp => ⟨hp.1, hmaps p hp⟩)
  have hP : ContinuousOn (fun p : X × ℂ => fun m => iteratedFDeriv ℝ (c.partSize m) (G p.1) p.2) (S ×ˢ U) :=
    continuousOn_pi.2 fun m => hG (c.partSize m) (c.partSize_le m)
  have hL := ((c.compAlongOrderedFinpartitionL ℝ ℂ ℂ ℂ).continuous.comp_continuousOn hA)
  exact (continuous_eval.comp_continuousOn (hL.prodMk hP)).congr
    (fun p _ => rfl)

/-- (D2b) `[W1]` **`z`-regularity of the two-parameter solution on the smoothness set**: `C³` in `z` on `Ω`, with
`z`-iterated derivatives jointly continuous. Route: D1 gives `w_P = H_P ∘ G_P`, with `H_P` a Cauchy integral,
holomorphic in `ζ`; the chain rule then holds with complex derivatives of `H`, whose derivatives are jointly
continuous as parametric circle integrals; the derivatives of `G` are jointly continuous by A3. -/
theorem wr_ns2_z_regular {m₁ m₂ : ℂ → ℂ} {k₁ k₂ : ℝ} (hm₁ : IsBeltramiCoeff m₁ univ k₁)
    (hm₂ : IsBeltramiCoeff m₂ univ k₂) {Ω : Set ℂ} (hΩ : IsOpen Ω)
    (hs₁ : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) m₁ Ω) (hs₂ : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) m₂ Ω)
    {W : Set (ℂ × ℂ)} (hW : IsOpen W)
    (hWk : ∀ P ∈ W, ∃ k < 1, IsBeltramiCoeff (fun u => P.1 * m₁ u + P.2 * m₂ u) univ k) :
    (∀ P ∈ W, ContDiffOn ℝ 3 (normalizedSolution fun u => P.1 * m₁ u + P.2 * m₂ u) Ω) ∧
      ∀ j ≤ 3, ContinuousOn (fun q : (ℂ × ℂ) × ℂ =>
        iteratedFDeriv ℝ j (normalizedSolution fun u => q.1.1 * m₁ u + q.1.2 * m₂ u) q.2) (W ×ˢ Ω) := by
  obtain ⟨F, hF⟩ : ∃ F : ℂ × ℂ → ℂ → ℂ, F = fun P => normalizedSolution fun u => P.1 * m₁ u + P.2 * m₂ u :=
    ⟨_, rfl⟩
  have loc : ∀ P₀ ∈ W, ∀ z₀ ∈ Ω, ∃ r > 0, ∃ ρ > 0, ball z₀ ρ ⊆ Ω ∧
      (∀ P ∈ ball P₀ r, ContDiffOn ℝ 3 (F P) (ball z₀ ρ)) ∧
      ∀ j ≤ 3, ContinuousOn (fun q : (ℂ × ℂ) × ℂ => iteratedFDeriv ℝ j (F q.1) q.2)
        (ball P₀ r ×ˢ ball z₀ ρ) := by
    intro P₀ hP₀ z₀ hz₀
    obtain ⟨V, hV, -, ρ, hρ, G, c, R, hR, hG3, hGc, hhc0, hrep0⟩ :=
      wr_local_cauchy hm₁ hm₂ hΩ hs₁ hs₂ hW hWk hP₀ hz₀
    have hhc : ContinuousOn (fun q : (ℂ × ℂ) × ℂ => F q.1 (Function.invFun (G q.1) q.2)) (V ×ˢ sphere c R) := by
      rw [hF]; exact hhc0
    have hrep : ∀ P ∈ V, ∀ z ∈ ball z₀ ρ, G P z ∈ ball c (R / 2) ∧
        F P z = (2 * π * I)⁻¹ * ∮ ξ in C(c, R), F P (Function.invFun (G P) ξ) / (ξ - G P z) := by
      rw [hF]; exact hrep0
    obtain ⟨r, hr, hrV⟩ := Metric.mem_nhds_iff.1 hV
    obtain ⟨ρ', hρ', hρ'Ω⟩ := Metric.isOpen_iff.1 hΩ z₀ hz₀
    obtain ⟨ρ₁, hρ₁def⟩ : ∃ ρ₁ : ℝ, ρ₁ = min ρ ρ' := ⟨_, rfl⟩
    have hρ₁ : 0 < ρ₁ := by rw [hρ₁def]; exact lt_min hρ hρ'
    have hρ₁ρ : ball z₀ ρ₁ ⊆ ball z₀ ρ := ball_subset_ball (by rw [hρ₁def]; exact min_le_left _ _)
    have hρ₁Ω : ball z₀ ρ₁ ⊆ Ω := (ball_subset_ball (by rw [hρ₁def]; exact min_le_right _ _)).trans hρ'Ω
    have hballV : ball P₀ r ⊆ V := hrV
    obtain ⟨h, hh⟩ : ∃ h : ℂ × ℂ → ℂ → ℂ, h = fun P ξ => (2 * π * I)⁻¹ * F P (Function.invFun (G P) ξ) :=
      ⟨_, rfl⟩
    have hhcont : ContinuousOn (fun p : (ℂ × ℂ) × ℂ => h p.1 p.2) (ball P₀ r ×ˢ sphere c R) := by
      rw [hh]; exact (continuousOn_const.mul hhc).mono (prod_mono hballV subset_rfl)
    have hhx : ∀ P ∈ ball P₀ r, ContinuousOn (h P) (sphere c R) :=
      fun P hP => hhcont.comp (continuous_const.prodMk continuous_id).continuousOn (fun y hy => ⟨hP, hy⟩)
    have hHcont := wr_param_cauchy_iter_cont hR hhcont
    have hHsm : ∀ P ∈ ball P₀ r, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun ζ => ∮ ξ in C(c, R), (ξ - ζ) ^ (-1 : ℤ) • h P ξ) (ball c R) := fun P hP =>
      ((wr_cauchy_diffOn hR (hhx P hP)).contDiffOn isOpen_ball).restrict_scalars ℝ
    have hmaps : ∀ P ∈ ball P₀ r, ∀ z ∈ ball z₀ ρ₁, G P z ∈ ball c R := fun P hP z hz =>
      ball_subset_ball (by linarith) (hrep P (hballV hP) z (hρ₁ρ hz)).1
    have hrep' : ∀ P ∈ ball P₀ r, ∀ z ∈ ball z₀ ρ₁,
        F P z = (fun ζ => ∮ ξ in C(c, R), (ξ - ζ) ^ (-1 : ℤ) • h P ξ) (G P z) := by
      intro P hP z hz
      rw [(hrep P (hballV hP) z (hρ₁ρ hz)).2, wr_cauchy_form, hh]
    have hGv : ContinuousOn (fun p : (ℂ × ℂ) × ℂ => G p.1 p.2) (ball P₀ r ×ˢ ball z₀ ρ₁) := by
      refine (((continuousMultilinearCurryFin0 ℝ ℂ ℂ).continuous.comp_continuousOn
        (hGc 0 (by norm_num))).mono (prod_mono hballV (subset_univ _))).congr ?_
      intro q _
      simp [iteratedFDeriv_zero_eq_comp]
    refine ⟨r, hr, ρ₁, hρ₁, hρ₁Ω, fun P hP => ?_, fun j hj => ?_⟩
    · refine ((hHsm P hP).of_le (by norm_cast)).comp ((hG3 P (hballV hP)).contDiffOn)
        (fun z hz => hmaps P hP z hz) |>.congr ?_
      intro z hz
      exact hrep' P hP z hz
    · have hcomp := wr_comp_iter_cont (S := ball P₀ r) (U := ball z₀ ρ₁) (T := ball c R) (j := j)
        (H := fun P ζ => ∮ ξ in C(c, R), (ξ - ζ) ^ (-1 : ℤ) • h P ξ)
        (G := G) (fun k _ => hHcont k)
        (fun k hk => (hGc k (hk.trans hj)).mono (prod_mono hballV (subset_univ _))) hGv
        (fun p hp => hmaps p.1 hp.1 p.2 hp.2)
      refine hcomp.congr ?_
      intro q hq
      have hqP := hq.1
      have hqz := hq.2
      have hev : F q.1 =ᶠ[𝓝 q.2] (fun ζ => ∮ ξ in C(c, R), (ξ - ζ) ^ (-1 : ℤ) • h q.1 ξ) ∘ G q.1 := by
        filter_upwards [isOpen_ball.mem_nhds hqz] with z hz
        exact hrep' q.1 hqP z hz
      have hHa : ContDiffAt ℝ 3 (fun ζ => ∮ ξ in C(c, R), (ξ - ζ) ^ (-1 : ℤ) • h q.1 ξ) (G q.1 q.2) :=
        ((hHsm q.1 hqP).of_le (by norm_cast)).contDiffAt (isOpen_ball.mem_nhds (hmaps q.1 hqP q.2 hqz))
      have hGa : ContDiffAt ℝ 3 (G q.1) q.2 := (hG3 q.1 (hballV hqP)).contDiffAt
      show iteratedFDeriv ℝ j (F q.1) q.2 = _
      rw [(hev.iteratedFDeriv ℝ j).self_of_nhds, iteratedFDeriv_comp hHa hGa (by exact_mod_cast hj)]
      rfl
  refine ⟨fun P hP => ?_, fun j hj => ?_⟩
  · have key : ContDiffOn ℝ 3 (F P) Ω := by
      apply contDiffOn_of_locally_contDiffOn
      intro z hz
      obtain ⟨r, hr, ρ, hρ, -, hcd, -⟩ := loc P hP z hz
      exact ⟨ball z ρ, isOpen_ball, mem_ball_self hρ, (hcd P (mem_ball_self hr)).mono inter_subset_right⟩
    rw [hF] at key
    exact key
  · have key : ContinuousOn (fun q : (ℂ × ℂ) × ℂ => iteratedFDeriv ℝ j (F q.1) q.2) (W ×ˢ Ω) := by
      intro q hq
      obtain ⟨r, hr, ρ, hρ, -, -, hc⟩ := loc q.1 hq.1 q.2 hq.2
      have hn : ball q.1 r ×ˢ ball q.2 ρ ∈ 𝓝 q :=
        (isOpen_ball.prod isOpen_ball).mem_nhds ⟨mem_ball_self hr, mem_ball_self hρ⟩
      exact ((hc j hj).continuousAt hn).continuousWithinAt
    rw [hF] at key
    exact key

/-- (D2) `[W1]` **Generic joint `C³`**: the two-parameter normalized solution is jointly `C³` on `W ×ˢ Ω`
wherever both coefficients are smooth on `Ω`. -/
theorem wr_local_joint_contDiff {m₁ m₂ : ℂ → ℂ} {k₁ k₂ : ℝ} (hm₁ : IsBeltramiCoeff m₁ univ k₁)
    (hm₂ : IsBeltramiCoeff m₂ univ k₂) {Ω : Set ℂ} (hΩ : IsOpen Ω)
    (hs₁ : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) m₁ Ω) (hs₂ : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) m₂ Ω)
    {W : Set (ℂ × ℂ)} (hW : IsOpen W)
    (hWk : ∀ P ∈ W, ∃ k < 1, IsBeltramiCoeff (fun u => P.1 * m₁ u + P.2 * m₂ u) univ k) :
    ContDiffOn ℝ 3 (fun q : (ℂ × ℂ) × ℂ => normalizedSolution (fun u => q.1.1 * m₁ u + q.1.2 * m₂ u) q.2)
      (W ×ˢ Ω) := by
  obtain ⟨hz, hzc⟩ := wr_ns2_z_regular hm₁ hm₂ hΩ hs₁ hs₂ hW hWk
  exact wr_joint_of_holo_param (u := fun P => normalizedSolution fun u => P.1 * m₁ u + P.2 * m₂ u) hW hΩ
    (fun z _ => (wr_ns2_holo hm₁ hm₂ hW hWk z).1) (fun z _ => (wr_ns2_holo hm₁ hm₂ hW hWk z).2)
    ((wr_ns2_cont hm₁ hm₂ hW hWk).mono (prod_mono subset_rfl (subset_univ _))) hz hzc




/-! ### Part E assembly helpers (下属1) -/

/-- The coefficient data of `extU (ε μ) = ε·m₁ + ε̄·m₂` for `μ` smooth on `𝕌` with `|μ| ≤ k`. -/
theorem wr_U_coeffs {μ : ℂ → ℂ} {k : ℝ} (hk : 0 ≤ k) (hμk : IsBeltramiCoeff μ upperHalf k)
    (hμs : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) μ upperHalf) :
    IsBeltramiCoeff (fun u => if 0 < u.im then μ u else 0) univ k ∧
    IsBeltramiCoeff (fun u => if u.im < 0 then conj (μ (conj u)) else 0) univ k ∧
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun u => if 0 < u.im then μ u else 0) upperHalf ∧
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun u => if u.im < 0 then conj (μ (conj u)) else 0) upperHalf ∧
    ∀ a b : ℂ, max ‖a‖ ‖b‖ * k < 1 → ∃ k' < 1, IsBeltramiCoeff (fun u => a * (if 0 < u.im then μ u else 0) +
      b * (if u.im < 0 then conj (μ (conj u)) else 0)) univ k' := by
  have hU : IsOpen upperHalf := isOpen_lt continuous_const Complex.continuous_im
  have hL : IsOpen {u : ℂ | u.im < 0} := isOpen_lt Complex.continuous_im continuous_const
  have hae := (ae_restrict_iff' hU.measurableSet).1 hμk.2
  -- pointwise bound on `𝕌`
  have hb : ∀ z ∈ upperHalf, ‖μ z‖ ≤ k := by
    intro z hz
    have hc : ContinuousOn (fun u => if 0 < u.im then μ u else 0) upperHalf :=
      hμs.continuousOn.congr (fun u hu => by
        have : (0 : ℝ) < u.im := hu
        simp only [this, ↓reduceIte])
    have hae' : ∀ᵐ u, ‖(fun u => if 0 < u.im then μ u else 0) u‖ ≤ k := by
      filter_upwards [hae] with u hu
      by_cases h : 0 < u.im
      · simp only [h, ↓reduceIte]; exact hu h
      · simp only [h, ↓reduceIte, norm_zero]; exact hk
    have h := wr_ae_bound_on hU hc hae' z hz
    have hz' : (0 : ℝ) < z.im := hz
    simpa only [hz', ↓reduceIte] using h
  have hb1 : ∀ z, ‖(fun u => if 0 < u.im then μ u else 0) z‖ ≤ k := by
    intro z
    by_cases h : 0 < z.im
    · simp only [h, ↓reduceIte]; exact hb z h
    · simp only [h, ↓reduceIte, norm_zero]; exact hk
  have hb2 : ∀ z, ‖(fun u => if u.im < 0 then conj (μ (conj u)) else 0) z‖ ≤ k := by
    intro z
    by_cases h : z.im < 0
    · simp only [h, ↓reduceIte, RCLike.norm_conj]
      exact hb (conj z) (by show 0 < (conj z).im; rw [Complex.conj_im]; linarith)
    · simp only [h, ↓reduceIte, norm_zero]; exact hk
  -- measurability
  have hm1 : AEStronglyMeasurable (fun u => if 0 < u.im then μ u else 0) volume := by
    have h := (aestronglyMeasurable_indicator_iff (μ := volume) hU.measurableSet).2
      (hμs.continuousOn.aestronglyMeasurable (μ := volume) hU.measurableSet)
    refine h.congr (Filter.Eventually.of_forall fun u => ?_)
    by_cases hu : 0 < u.im
    · simp [Set.indicator, upperHalf, hu]
    · simp [Set.indicator, upperHalf, hu]
  have hgc : ContinuousOn (fun u => conj (μ (conj u))) {u : ℂ | u.im < 0} :=
    Complex.continuous_conj.comp_continuousOn (hμs.continuousOn.comp Complex.continuous_conj.continuousOn
      (fun u hu => by
        show 0 < (conj u).im
        rw [Complex.conj_im]
        have : u.im < 0 := hu
        linarith))
  have hm2 : AEStronglyMeasurable (fun u => if u.im < 0 then conj (μ (conj u)) else 0) volume := by
    have h := (aestronglyMeasurable_indicator_iff (μ := volume) hL.measurableSet).2 (hgc.aestronglyMeasurable (μ := volume) hL.measurableSet)
    refine h.congr (Filter.Eventually.of_forall fun u => ?_)
    by_cases hu : u.im < 0
    · simp [Set.indicator, hu]
    · simp [Set.indicator, hu]
  refine ⟨⟨by rw [Measure.restrict_univ]; exact hm1, by
      rw [Measure.restrict_univ]; exact Filter.Eventually.of_forall hb1⟩,
    ⟨by rw [Measure.restrict_univ]; exact hm2, by
      rw [Measure.restrict_univ]; exact Filter.Eventually.of_forall hb2⟩, ?_, ?_, ?_⟩
  · exact hμs.congr (fun u hu => by
      have : (0 : ℝ) < u.im := hu
      simp only [this, ↓reduceIte])
  · exact (contDiffOn_const (c := (0 : ℂ))).congr (fun u hu => by
      have : ¬ u.im < 0 := by have : (0 : ℝ) < u.im := hu; linarith
      simp only [this, ↓reduceIte])
  · intro a b hab
    refine ⟨max ‖a‖ ‖b‖ * k, hab, ?_, ?_⟩
    · rw [Measure.restrict_univ]
      exact (hm1.const_mul a).add (hm2.const_mul b)
    · rw [Measure.restrict_univ]
      refine Filter.Eventually.of_forall fun z => ?_
      by_cases h1 : 0 < z.im
      · have h2 : ¬ z.im < 0 := by linarith
        have := hb1 z
        simp only [h1, h2, ↓reduceIte, mul_zero, add_zero] at this ⊢
        rw [norm_mul]
        exact mul_le_mul (le_max_left _ _) this (norm_nonneg _) ((norm_nonneg _).trans (le_max_left _ _))
      · by_cases h2 : z.im < 0
        · have := hb2 z
          simp only [h1, h2, ↓reduceIte, mul_zero, zero_add] at this ⊢
          rw [norm_mul]
          exact mul_le_mul (le_max_right _ _) this (norm_nonneg _) ((norm_nonneg _).trans (le_max_left _ _))
        · simp only [h1, h2, ↓reduceIte, mul_zero, add_zero, norm_zero]
          exact mul_nonneg ((norm_nonneg _).trans (le_max_left _ _)) hk

/-- `wU (ε μ)` as a two-parameter normalized solution. -/
theorem wr_wU_eq (μ : ℂ → ℂ) (ε : ℂ) :
    (wU fun u => ε * μ u) = normalizedSolution (fun u => ε * (if 0 < u.im then μ u else 0) +
      conj ε * (if u.im < 0 then conj (μ (conj u)) else 0)) := by
  show normalizedSolution (extU fun u => ε * μ u) = _
  rw [wr_extU_smul]

/-- (E2) `[W1]` **W-REG, model `𝕌`.** For `μ` smooth on `𝕌` with `|μ| ≤ k` there, `(ε, z) ↦ w_{εμ}(z)` is jointly
`C³` on `{‖ε‖ k < 1} × 𝕌`. This covers `eq_1_24`/`eq_1_25` (smooth `μ`) and every `IsHarmonicU` item. -/
theorem wr_joint_contDiff_U {μ : ℂ → ℂ} {k : ℝ} (hk : 0 ≤ k) (hμk : IsBeltramiCoeff μ upperHalf k)
    (hμs : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) μ upperHalf) :
    ContDiffOn ℝ 3 (fun p : ℂ × ℂ => wU (fun u => p.1 * μ u) p.2) ({ε : ℂ | ‖ε‖ * k < 1} ×ˢ upperHalf) := by
  obtain ⟨hm₁, hm₂, hs₁, hs₂, hcomb⟩ := wr_U_coeffs hk hμk hμs
  have hU : IsOpen upperHalf := isOpen_lt continuous_const Complex.continuous_im
  have hW : IsOpen {P : ℂ × ℂ | max ‖P.1‖ ‖P.2‖ * k < 1} :=
    isOpen_lt (((continuous_norm.comp continuous_fst).max (continuous_norm.comp continuous_snd)).mul
      continuous_const) continuous_const
  have hD := wr_local_joint_contDiff hm₁ hm₂ hU hs₁ hs₂ hW (fun P hP => hcomb P.1 P.2 hP)
  have hφ : ContDiff ℝ 3 (fun p : ℂ × ℂ => ((p.1, conj p.1), p.2)) :=
    (contDiff_fst.prodMk (Complex.conjCLE.contDiff.comp contDiff_fst)).prodMk contDiff_snd
  refine (hD.comp hφ.contDiffOn (fun p hp => ⟨?_, hp.2⟩)).congr (fun p _ => ?_)
  · show max ‖p.1‖ ‖conj p.1‖ * k < 1
    rw [RCLike.norm_conj, max_self]
    exact hp.1
  · show wU (fun u => p.1 * μ u) p.2 = _
    rw [wr_wU_eq]
    rfl

/-- (E3) `[W1]` Positive Jacobian (so `dz w ≠ 0`, and `kernelK` has no `0/0` junk on `𝕌`). -/
theorem wr_jacobian_pos_U {μ : ℂ → ℂ} {k : ℝ} (hk : 0 ≤ k) (hμk : IsBeltramiCoeff μ upperHalf k)
    (hμs : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) μ upperHalf) {ε : ℂ} (hε : ‖ε‖ * k < 1) {z : ℂ}
    (hz : z ∈ upperHalf) :
    0 < ‖dz (wU fun u => ε * μ u) z‖ ^ 2 - ‖dzbar (wU fun u => ε * μ u) z‖ ^ 2 := by
  obtain ⟨hm₁, hm₂, hs₁, hs₂, hcomb⟩ := wr_U_coeffs hk hμk hμs
  have hU : IsOpen upperHalf := isOpen_lt continuous_const Complex.continuous_im
  have hε' : max ‖ε‖ ‖conj ε‖ * k < 1 := by rw [RCLike.norm_conj, max_self]; exact hε
  have h := wr_local_jacobian_pos (P := (ε, conj ε)) hm₁ hm₂ hU hs₁ hs₂ (hcomb ε (conj ε) hε') hz
  rw [wr_wU_eq]
  exact h

/-! ### Helpers for E5 (下属5) -/

/-- Model A coefficient of `εν` splits as `ε·m₁ + ε̄·m₂` (`m₁ = ν` on `𝔻*`, `m₂` its reflection on `𝔻`). -/
theorem wr_extA_smul (ε : ℂ) (ν : LinfStar) :
    extA (ε • ν) =ᵐ[volume] fun z => ε * (if 1 < ‖z‖ then ν z else 0) +
      conj ε * (if ‖z‖ < 1 then conj (ν (refl z)) * z ^ 2 / conj z ^ 2 else 0) := by
  have hms : MeasurableSet unitDiscExterior := (isOpen_lt continuous_const continuous_norm).measurableSet
  have hs := Lp.coeFn_smul ε ν
  have hP : ∀ᵐ z : ℂ, z ∈ unitDiscExterior → (ε • ν) z = ε * ν z := by
    have := (ae_restrict_iff' hms).1 hs
    filter_upwards [this] with z hz hzm
    simpa using hz hzm
  have hP' := ae_refl hP
  have hne : ∀ᵐ z : ℂ, z ≠ 0 := compl_mem_ae_iff.2 (measure_singleton 0)
  filter_upwards [hP, hP', hne] with z h1 h2 hz0
  unfold extA
  by_cases hz1 : 1 < ‖z‖
  · have hz1' : ¬ ‖z‖ < 1 := by linarith
    rw [if_pos hz1, if_pos hz1, if_neg hz1', h1 hz1]
    ring
  · rw [if_neg hz1, if_neg hz1]
    by_cases hz2 : ‖z‖ < 1
    · rw [if_pos hz2, if_pos hz2]
      have hr : refl z ∈ unitDiscExterior := by
        show 1 < ‖refl z‖
        rw [refl, norm_inv, Complex.norm_conj]
        exact one_lt_inv_iff₀.mpr ⟨norm_pos_iff.mpr hz0, hz2⟩
      rw [h2 hr, map_mul]
      ring
    · rw [if_neg hz2, if_neg hz2]
      ring

/-- The harmonic Beltrami differential `ν` has a representative smooth on `𝔻*`. -/
theorem wr_harm_rep {ν : LinfStar} (hν : ν ∈ harmonicBeltrami) :
    ∃ g : ℂ → ℂ, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g unitDiscExterior ∧
      ∀ᵐ z ∂(volume.restrict unitDiscExterior), ν z = g z := by
  obtain ⟨φ, hφ⟩ := (mem_harmonicBeltrami_iff ν).1 hν
  refine ⟨fun z => (1 - ‖z‖ ^ 2) ^ 2 * conj (AInf.toFun φ z), ?_, hφ⟩
  have ho : IsOpen unitDiscExterior := isOpen_lt continuous_const continuous_norm
  have hhol : ContDiffOn ℂ ((⊤ : ℕ∞) : WithTop ℕ∞) (AInf.toFun φ) unitDiscExterior :=
    (φ.2 : DifferentiableOn ℂ (AInf.toFun φ) unitDiscExterior).contDiffOn ho
  have hconj : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z => conj (AInf.toFun φ z)) unitDiscExterior :=
    Complex.conjCLE.toContinuousLinearMap.contDiff.comp_contDiffOn (hhol.restrict_scalars ℝ)
  have hn : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : ℂ => ((1 - ‖z‖ ^ 2) ^ 2 : ℂ)) := by
    have h : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : ℂ => (1 - ‖z‖ ^ 2) ^ 2) :=
      (contDiff_const.sub (contDiff_norm_sq ℝ)).pow 2
    convert Complex.ofRealCLM.contDiff.comp h using 1
    funext z
    simp
  exact hn.contDiffOn.mul hconj

theorem wr_isBC_congr {m m' : ℂ → ℂ} {k : ℝ} (h : IsBeltramiCoeff m univ k) (he : m =ᵐ[volume] m') :
    IsBeltramiCoeff m' univ k := by
  obtain ⟨h1, h2⟩ := h
  rw [Measure.restrict_univ] at h1 h2
  refine ⟨?_, ?_⟩ <;> rw [Measure.restrict_univ]
  · exact h1.congr he
  · exact (h2.and he).mono fun u hu => hu.2 ▸ hu.1

/-- Three-point normalization: the Möbius map sending `w₁, w₂, 1` to `-1, -i, 1`, with explicit coefficients
(`S⁻¹ ∘ T`, `T = (w₁, w₂, 1 ↦ 0, 1, ∞)`, `S = (-1, -i, 1 ↦ 0, 1, ∞)`). -/
theorem wr_three_point {M : ExtPlane → ExtPlane} (hM : IsMobius M) {w₁ w₂ : ℂ}
    (h12 : w₁ ≠ w₂) (h13 : w₁ ≠ 1) (h23 : w₂ ≠ 1)
    (e₁ : M (w₁ : ExtPlane) = ((-1 : ℂ) : ExtPlane)) (e₂ : M (w₂ : ExtPlane) = ((-I : ℂ) : ExtPlane))
    (e₃ : M ((1 : ℂ) : ExtPlane) = ((1 : ℂ) : ExtPlane)) :
    M = mobiusExt
      (-(1 * (-I - -1)) * (w₂ - 1) + -(-((-1) * (-I - 1))) * (w₂ - w₁))
      (-(1 * (-I - -1)) * (-(w₁ * (w₂ - 1))) + -(-((-1) * (-I - 1))) * (-(1 * (w₂ - w₁))))
      (-(-I - -1) * (w₂ - 1) + (-I - 1) * (w₂ - w₁))
      (-(-I - -1) * (-(w₁ * (w₂ - 1))) + (-I - 1) * (-(1 * (w₂ - w₁)))) := by
  have hm1 : (-1 : ℂ) ≠ -I := by
    intro h; have := congrArg Complex.im h; simp at this
  have hm2 : (-1 : ℂ) ≠ 1 := by norm_num
  have hm3 : (-I : ℂ) ≠ 1 := by
    intro h; have := congrArg Complex.re h; simp at this
  obtain ⟨hT1, hT2, hT3⟩ := mobius_three_point_eval h12 h13 h23
  obtain ⟨hS1, hS2, hS3⟩ := mobius_three_point_eval hm1 hm2 hm3
  have hdetT : (w₂ - 1) * (-(1 * (w₂ - w₁))) - (-(w₁ * (w₂ - 1))) * (w₂ - w₁) ≠ 0 := by
    have e : (w₂ - 1) * (-(1 * (w₂ - w₁))) - (-(w₁ * (w₂ - 1))) * (w₂ - w₁) =
        (w₂ - 1) * (w₂ - w₁) * (w₁ - 1) := by ring
    rw [e]
    exact mul_ne_zero (mul_ne_zero (sub_ne_zero.2 h23) (sub_ne_zero.2 h12.symm)) (sub_ne_zero.2 h13)
  have hdetS : (-I - 1) * (-(1 * (-I - -1))) - (-((-1) * (-I - 1))) * (-I - -1) ≠ 0 := by
    have e : (-I - 1) * (-(1 * (-I - -1))) - (-((-1) * (-I - 1))) * (-I - -1) =
        (-I - 1) * (-I - -1) * (-1 - 1) := by ring
    rw [e]
    exact mul_ne_zero (mul_ne_zero (sub_ne_zero.2 hm3) (sub_ne_zero.2 hm1.symm)) (sub_ne_zero.2 hm2)
  have hinv := mobiusExt_inv_apply hdetS
  have hN : ∀ w, mobiusExt (-(1 * (-I - -1))) (-(-((-1) * (-I - 1)))) (-(-I - -1)) (-I - 1)
      (mobiusExt (w₂ - 1) (-(w₁ * (w₂ - 1))) (w₂ - w₁) (-(1 * (w₂ - w₁))) w) = mobiusExt
      (-(1 * (-I - -1)) * (w₂ - 1) + -(-((-1) * (-I - 1))) * (w₂ - w₁))
      (-(1 * (-I - -1)) * (-(w₁ * (w₂ - 1))) + -(-((-1) * (-I - 1))) * (-(1 * (w₂ - w₁))))
      (-(-I - -1) * (w₂ - 1) + (-I - 1) * (w₂ - w₁))
      (-(-I - -1) * (-(w₁ * (w₂ - 1))) + (-I - 1) * (-(1 * (w₂ - w₁)))) w :=
    fun w => s16p_mobiusExt_comp hdetT w
  have hdetN : (-(1 * (-I - -1)) * (w₂ - 1) + -(-((-1) * (-I - 1))) * (w₂ - w₁)) *
      (-(-I - -1) * (-(w₁ * (w₂ - 1))) + (-I - 1) * (-(1 * (w₂ - w₁)))) -
      (-(1 * (-I - -1)) * (-(w₁ * (w₂ - 1))) + -(-((-1) * (-I - 1))) * (-(1 * (w₂ - w₁)))) *
      (-(-I - -1) * (w₂ - 1) + (-I - 1) * (w₂ - w₁)) ≠ 0 := by
    have e : (-(1 * (-I - -1)) * (w₂ - 1) + -(-((-1) * (-I - 1))) * (w₂ - w₁)) *
        (-(-I - -1) * (-(w₁ * (w₂ - 1))) + (-I - 1) * (-(1 * (w₂ - w₁)))) -
        (-(1 * (-I - -1)) * (-(w₁ * (w₂ - 1))) + -(-((-1) * (-I - 1))) * (-(1 * (w₂ - w₁)))) *
        (-(-I - -1) * (w₂ - 1) + (-I - 1) * (w₂ - w₁)) =
        ((-I - 1) * (-(1 * (-I - -1))) - (-((-1) * (-I - 1))) * (-I - -1)) *
        ((w₂ - 1) * (-(1 * (w₂ - w₁))) - (-(w₁ * (w₂ - 1))) * (w₂ - w₁)) := by ring
    rw [e]
    exact mul_ne_zero hdetS hdetT
  refine mobius_eq_of_three_points hM ⟨_, _, _, _, hdetN, rfl⟩ h12 h13 h23 ?_ ?_ ?_
  · rw [e₁, ← hN, hT1, ← hS1, hinv]
  · rw [e₂, ← hN, hT2, ← hS2, hinv]
  · rw [e₃, ← hN, hT3, ← hS3, hinv]

/-- (E5) `[W5]` **W-REG, Model A** (for S7 §7.1 `Qfun`/`RnmFun` and S8): for `ν ∈ Ω^{-1,1}(𝔻*)`,
`(ε, z) ↦ w_A(εν)(z)` is jointly `C³` on `{‖ε‖‖ν‖ < 1} × 𝔻*` **off the pole** of `wAS (εν)`, where `wA` takes
its junk value `0`. For small `ε` the pole lies near `∞`, so every point `(0, z)` with `z ∈ 𝔻*` is in the set.
Proof: D2, with `ν` replaced by its smooth representative (normalized solutions see the coefficient only a.e.),
plus the Möbius normalization of `wAS`. -/
theorem wr_joint_contDiff_A {ν : LinfStar} (hν : ν ∈ harmonicBeltrami) :
    ContDiffOn ℝ 3 (fun p : ℂ × ℂ => wA (p.1 • ν) p.2)
      {p : ℂ × ℂ | ‖p.1‖ * ‖ν‖ < 1 ∧ p.2 ∈ unitDiscExterior ∧ wAS (p.1 • ν) (p.2 : ExtPlane) ≠ extInf} := by
  obtain ⟨g, hg, hνg⟩ := wr_harm_rep hν
  have hΩ : IsOpen unitDiscExterior := isOpen_lt continuous_const continuous_norm
  have hms : MeasurableSet unitDiscExterior := hΩ.measurableSet
  have hb : ∀ᵐ z : ℂ, z ∈ unitDiscExterior → ν z = g z := (ae_restrict_iff' hms).1 hνg
  have hne : ∀ᵐ z : ℂ, z ≠ 0 := compl_mem_ae_iff.2 (measure_singleton 0)
  -- the smooth coefficients `m₁` (on `𝔻*`) and `m₂` (its reflection on `𝔻`)
  set m₁ : ℂ → ℂ := fun u => if 1 < ‖u‖ then g u else 0 with hm₁def
  set m₂ : ℂ → ℂ := fun u => if ‖u‖ < 1 then conj (g (refl u)) * u ^ 2 / conj u ^ 2 else 0 with hm₂def
  have hν₁ : ∀ᵐ u : ℂ, (if 1 < ‖u‖ then ν u else 0) = m₁ u := by
    filter_upwards [hb] with u hu
    by_cases h : 1 < ‖u‖
    · rw [if_pos h, hu h]; exact (if_pos h).symm
    · rw [if_neg h]; exact (if_neg h).symm
  have hν₂ : ∀ᵐ u : ℂ, (if ‖u‖ < 1 then conj (ν (refl u)) * u ^ 2 / conj u ^ 2 else 0) = m₂ u := by
    filter_upwards [ae_refl hb, hne] with u hu hu0
    by_cases h : ‖u‖ < 1
    · rw [if_pos h, hu ((refl_mem_exterior_iff hu0).mpr (mem_ball_zero_iff.mpr h))]
      exact (if_pos h).symm
    · rw [if_neg h]; exact (if_neg h).symm
  have he₁ : m₁ =ᵐ[volume] {u : ℂ | 1 < ‖u‖}.indicator (extA ν) := by
    filter_upwards [hν₁] with u hu
    rw [← hu, Set.indicator_apply]
    by_cases h : 1 < ‖u‖
    · rw [if_pos h, if_pos (show u ∈ {u : ℂ | 1 < ‖u‖} from h), extA_eq_on_exterior ν h]
    · rw [if_neg h, if_neg (show u ∉ {u : ℂ | 1 < ‖u‖} from h)]
  have he₂ : m₂ =ᵐ[volume] {u : ℂ | ‖u‖ < 1}.indicator (extA ν) := by
    filter_upwards [hν₂] with u hu
    rw [← hu, Set.indicator_apply]
    by_cases h : ‖u‖ < 1
    · rw [if_pos h, if_pos (show u ∈ {u : ℂ | ‖u‖ < 1} from h)]
      show _ = if 1 < ‖u‖ then ν u else if ‖u‖ < 1 then conj (ν (refl u)) * u ^ 2 / conj u ^ 2 else 0
      rw [if_neg (not_lt.2 h.le), if_pos h]
    · rw [if_neg h, if_neg (show u ∉ {u : ℂ | ‖u‖ < 1} from h)]
  have hEm := extA_isBeltramiCoeff ν
  have hind : ∀ s : Set ℂ, MeasurableSet s → IsBeltramiCoeff (s.indicator (extA ν)) univ ‖ν‖ := fun s hs =>
    ⟨hEm.1.indicator hs, hEm.2.mono fun u hu => (norm_indicator_le_norm_self _ _).trans hu⟩
  have hm₁ : IsBeltramiCoeff m₁ univ ‖ν‖ :=
    wr_isBC_congr (hind _ (isOpen_lt continuous_const continuous_norm).measurableSet) he₁.symm
  have hm₂ : IsBeltramiCoeff m₂ univ ‖ν‖ :=
    wr_isBC_congr (hind _ (isOpen_lt continuous_norm continuous_const).measurableSet) he₂.symm
  -- the coefficient of `P` is bounded by `‖P‖ ‖ν‖` (disjoint supports)
  have hV : ∀ P : ℂ × ℂ, IsBeltramiCoeff (fun u => P.1 * m₁ u + P.2 * m₂ u) univ (‖P‖ * ‖ν‖) := by
    intro P
    refine ⟨(hm₁.1.const_mul P.1).add (hm₂.1.const_mul P.2), ?_⟩
    rw [Measure.restrict_univ]
    filter_upwards [he₁, he₂, extA_ae_norm_le ν] with u h1 h2 h3
    show ‖P.1 * m₁ u + P.2 * m₂ u‖ ≤ ‖P‖ * ‖ν‖
    rw [h1, h2, Set.indicator_apply, Set.indicator_apply]
    by_cases h : 1 < ‖u‖
    · rw [if_pos (show u ∈ {u : ℂ | 1 < ‖u‖} from h),
        if_neg (show u ∉ {u : ℂ | ‖u‖ < 1} from not_lt.2 h.le), mul_zero, add_zero, norm_mul]
      exact mul_le_mul (norm_fst_le P) h3 (norm_nonneg _) (norm_nonneg _)
    · rw [if_neg (show u ∉ {u : ℂ | 1 < ‖u‖} from h), mul_zero, zero_add]
      by_cases h' : ‖u‖ < 1
      · rw [if_pos (show u ∈ {u : ℂ | ‖u‖ < 1} from h'), norm_mul]
        exact mul_le_mul (norm_snd_le P) h3 (norm_nonneg _) (norm_nonneg _)
      · rw [if_neg (show u ∉ {u : ℂ | ‖u‖ < 1} from h'), mul_zero, norm_zero]
        positivity
  have hVo : IsOpen {P : ℂ × ℂ | ‖P‖ * ‖ν‖ < 1} :=
    isOpen_lt (continuous_norm.mul continuous_const) continuous_const
  have hVk : ∀ P ∈ {P : ℂ × ℂ | ‖P‖ * ‖ν‖ < 1}, ∃ k < 1,
      IsBeltramiCoeff (fun u => P.1 * m₁ u + P.2 * m₂ u) univ k := fun P hP => ⟨_, hP, hV P⟩
  -- `extA (εν) = ε m₁ + ε̄ m₂` a.e.
  have hcoef : ∀ ε : ℂ, extA (ε • ν) =ᵐ[volume] fun u => ε * m₁ u + conj ε * m₂ u := by
    intro ε
    filter_upwards [wr_extA_smul ε ν, hν₁, hν₂] with u h1 h2 h3
    rw [h1]
    show ε * _ + conj ε * _ = ε * m₁ u + conj ε * m₂ u
    rw [h2, h3]
  -- smoothness on `𝔻*`
  have hs₁ : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) m₁ unitDiscExterior := hg.congr fun u hu => if_pos hu
  have hs₂ : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) m₂ unitDiscExterior :=
    contDiffOn_const.congr fun u hu => if_neg (not_lt.2 (le_of_lt hu))
  have hD2 := wr_local_joint_contDiff hm₁ hm₂ hΩ hs₁ hs₂ hVo hVk
  -- restriction to the real slice `P = (ε, ε̄)`
  have hnormε : ∀ ε : ℂ, ‖((ε, conj ε) : ℂ × ℂ)‖ = ‖ε‖ := by
    intro ε; rw [Prod.norm_mk, Complex.norm_conj, max_self]
  have hconj : ContDiff ℝ 3 (fun p : ℂ × ℂ => conj p.1) :=
    Complex.conjCLE.toContinuousLinearMap.contDiff.comp contDiff_fst
  have hJ : ContDiffOn ℝ 3 (fun p : ℂ × ℂ =>
      normalizedSolution (fun u => p.1 * m₁ u + conj p.1 * m₂ u) p.2)
      {p : ℂ × ℂ | ‖p.1‖ * ‖ν‖ < 1 ∧ p.2 ∈ unitDiscExterior} := by
    have h := ContDiffOn.comp (g := fun q : (ℂ × ℂ) × ℂ =>
        normalizedSolution (fun u => q.1.1 * m₁ u + q.1.2 * m₂ u) q.2)
      (f := fun p : ℂ × ℂ => ((p.1, conj p.1), p.2)) hD2
      ((contDiff_fst.prodMk hconj).prodMk contDiff_snd).contDiffOn
      (fun (p : ℂ × ℂ) (hp : p ∈ {p : ℂ × ℂ | ‖p.1‖ * ‖ν‖ < 1 ∧ p.2 ∈ unitDiscExterior}) => ⟨show ‖((p.1, conj p.1) : ℂ × ℂ)‖ * ‖ν‖ < 1 by rw [hnormε]; exact hp.1, hp.2⟩)
    exact h
  have hval : ∀ z : ℂ, ContDiffOn ℝ 3 (fun p : ℂ × ℂ =>
      normalizedSolution (fun u => p.1 * m₁ u + conj p.1 * m₂ u) z)
      {p : ℂ × ℂ | ‖p.1‖ * ‖ν‖ < 1 ∧ p.2 ∈ unitDiscExterior} := by
    intro z
    have h := ContDiffOn.comp (g := fun P : ℂ × ℂ => normalizedSolution (fun u => P.1 * m₁ u + P.2 * m₂ u) z)
      (f := fun p : ℂ × ℂ => (p.1, conj p.1)) (wr_ns2_param_contDiffOn hm₁ hm₂ hVo hVk z)
      (contDiff_fst.prodMk hconj).contDiffOn
      (fun (p : ℂ × ℂ) (hp : p ∈ {p : ℂ × ℂ | ‖p.1‖ * ‖ν‖ < 1 ∧ p.2 ∈ unitDiscExterior}) => show ‖((p.1, conj p.1) : ℂ × ℂ)‖ * ‖ν‖ < 1 by rw [hnormε]; exact hp.1)
    exact h
  -- the Möbius representation off the pole
  have hrep : ∀ p ∈ {p : ℂ × ℂ | ‖p.1‖ * ‖ν‖ < 1 ∧ p.2 ∈ unitDiscExterior ∧
      wAS (p.1 • ν) (p.2 : ExtPlane) ≠ extInf},
      ((-(-I - -1) * (normalizedSolution (fun u => p.1 * m₁ u + conj p.1 * m₂ u) (-I) - 1) +
          (-I - 1) * (normalizedSolution (fun u => p.1 * m₁ u + conj p.1 * m₂ u) (-I) -
            normalizedSolution (fun u => p.1 * m₁ u + conj p.1 * m₂ u) (-1))) *
          normalizedSolution (fun u => p.1 * m₁ u + conj p.1 * m₂ u) p.2 +
        (-(-I - -1) * (-(normalizedSolution (fun u => p.1 * m₁ u + conj p.1 * m₂ u) (-1) *
            (normalizedSolution (fun u => p.1 * m₁ u + conj p.1 * m₂ u) (-I) - 1))) +
          (-I - 1) * (-(1 * (normalizedSolution (fun u => p.1 * m₁ u + conj p.1 * m₂ u) (-I) -
            normalizedSolution (fun u => p.1 * m₁ u + conj p.1 * m₂ u) (-1)))))) ≠ 0 ∧
      wA (p.1 • ν) p.2 =
        ((-(1 * (-I - -1)) * (normalizedSolution (fun u => p.1 * m₁ u + conj p.1 * m₂ u) (-I) - 1) +
            -(-((-1) * (-I - 1))) * (normalizedSolution (fun u => p.1 * m₁ u + conj p.1 * m₂ u) (-I) -
              normalizedSolution (fun u => p.1 * m₁ u + conj p.1 * m₂ u) (-1))) *
            normalizedSolution (fun u => p.1 * m₁ u + conj p.1 * m₂ u) p.2 +
          (-(1 * (-I - -1)) * (-(normalizedSolution (fun u => p.1 * m₁ u + conj p.1 * m₂ u) (-1) *
              (normalizedSolution (fun u => p.1 * m₁ u + conj p.1 * m₂ u) (-I) - 1))) +
            -(-((-1) * (-I - 1))) * (-(1 * (normalizedSolution (fun u => p.1 * m₁ u + conj p.1 * m₂ u) (-I) -
              normalizedSolution (fun u => p.1 * m₁ u + conj p.1 * m₂ u) (-1)))))) /
        ((-(-I - -1) * (normalizedSolution (fun u => p.1 * m₁ u + conj p.1 * m₂ u) (-I) - 1) +
            (-I - 1) * (normalizedSolution (fun u => p.1 * m₁ u + conj p.1 * m₂ u) (-I) -
              normalizedSolution (fun u => p.1 * m₁ u + conj p.1 * m₂ u) (-1))) *
            normalizedSolution (fun u => p.1 * m₁ u + conj p.1 * m₂ u) p.2 +
          (-(-I - -1) * (-(normalizedSolution (fun u => p.1 * m₁ u + conj p.1 * m₂ u) (-1) *
              (normalizedSolution (fun u => p.1 * m₁ u + conj p.1 * m₂ u) (-I) - 1))) +
            (-I - 1) * (-(1 * (normalizedSolution (fun u => p.1 * m₁ u + conj p.1 * m₂ u) (-I) -
              normalizedSolution (fun u => p.1 * m₁ u + conj p.1 * m₂ u) (-1)))))) := by
    intro p hp
    obtain ⟨h1, -, hpole⟩ := hp
    have hk : ‖p.1 • ν‖ < 1 := by rw [norm_smul]; exact h1
    have hμ : p.1 • ν ∈ LinfStarBall := by simpa [LinfStarBall] using hk
    obtain ⟨M, hM, W', hW', hfin, -, hm1, hmi, hp1⟩ := wA_spec hμ
    have hWeq : W' = normalizedSolution (fun u => p.1 * m₁ u + conj p.1 * m₂ u) :=
      (QCV.qcv_ns_eq (norm_nonneg _) hk (extA_isBeltramiCoeff _) hW').symm.trans
        (QCV.qcv_ns_congr_ae (norm_nonneg _) hk (extA_isBeltramiCoeff _) (hcoef p.1))
    subst hWeq
    obtain ⟨K, hK⟩ := hW'.1
    obtain ⟨e, he⟩ := t1_homeomorph hK hW'.2.1
    have hinj : Function.Injective (normalizedSolution (fun u => p.1 * m₁ u + conj p.1 * m₂ u)) := by
      rw [← he]; exact e.injective
    have hW1 : normalizedSolution (fun u => p.1 * m₁ u + conj p.1 * m₂ u) 1 = 1 := hW'.2.2.2.1
    have hm1I : (-1 : ℂ) ≠ -I := by
      intro h; have := congrArg Complex.im h; simp at this
    have hmI1 : (-I : ℂ) ≠ 1 := by
      intro h; have := congrArg Complex.re h; simp at this
    have h12 := hinj.ne hm1I
    have h13 : normalizedSolution (fun u => p.1 * m₁ u + conj p.1 * m₂ u) (-1) ≠ 1 := by
      have h := hinj.ne (show (-1 : ℂ) ≠ 1 by norm_num)
      rwa [hW1] at h
    have h23 : normalizedSolution (fun u => p.1 * m₁ u + conj p.1 * m₂ u) (-I) ≠ 1 := by
      have h := hinj.ne hmI1
      rwa [hW1] at h
    have e₁ := (hfin (-1)).symm.trans hm1
    have e₂ := (hfin (-I)).symm.trans hmi
    have e₃ : M ((1 : ℂ) : ExtPlane) = ((1 : ℂ) : ExtPlane) := by
      have h := (hfin 1).symm.trans hp1
      rwa [hW1] at h
    have hMN := wr_three_point hM h12 h13 h23 e₁ e₂ e₃
    have hz := hfin p.2
    rw [hMN] at hz
    have hden : ((-(-I - -1) * (normalizedSolution (fun u => p.1 * m₁ u + conj p.1 * m₂ u) (-I) - 1) +
          (-I - 1) * (normalizedSolution (fun u => p.1 * m₁ u + conj p.1 * m₂ u) (-I) -
            normalizedSolution (fun u => p.1 * m₁ u + conj p.1 * m₂ u) (-1))) *
          normalizedSolution (fun u => p.1 * m₁ u + conj p.1 * m₂ u) p.2 +
        (-(-I - -1) * (-(normalizedSolution (fun u => p.1 * m₁ u + conj p.1 * m₂ u) (-1) *
            (normalizedSolution (fun u => p.1 * m₁ u + conj p.1 * m₂ u) (-I) - 1))) +
          (-I - 1) * (-(1 * (normalizedSolution (fun u => p.1 * m₁ u + conj p.1 * m₂ u) (-I) -
            normalizedSolution (fun u => p.1 * m₁ u + conj p.1 * m₂ u) (-1)))))) ≠ 0 := by
      intro h0
      rw [mobiusExt_coe_of_eq_zero h0] at hz
      exact hpole hz
    refine ⟨hden, ?_⟩
    show finPart (wAS (p.1 • ν) (p.2 : ExtPlane)) = _
    rw [hz, mobiusExt_coe hden]
    rfl
  -- regularity of the coefficients and of the quotient
  have hsub : {p : ℂ × ℂ | ‖p.1‖ * ‖ν‖ < 1 ∧ p.2 ∈ unitDiscExterior ∧
      wAS (p.1 • ν) (p.2 : ExtPlane) ≠ extInf} ⊆ {p : ℂ × ℂ | ‖p.1‖ * ‖ν‖ < 1 ∧ p.2 ∈ unitDiscExterior} :=
    fun p hp => ⟨hp.1, hp.2.1⟩
  obtain ⟨w₁, hw₁⟩ : ∃ F : ℂ × ℂ → ℂ,
      F = fun p => normalizedSolution (fun u => p.1 * m₁ u + conj p.1 * m₂ u) (-1) := ⟨_, rfl⟩
  obtain ⟨w₂, hw₂⟩ : ∃ F : ℂ × ℂ → ℂ,
      F = fun p => normalizedSolution (fun u => p.1 * m₁ u + conj p.1 * m₂ u) (-I) := ⟨_, rfl⟩
  obtain ⟨Wz, hWz⟩ : ∃ F : ℂ × ℂ → ℂ,
      F = fun p => normalizedSolution (fun u => p.1 * m₁ u + conj p.1 * m₂ u) p.2 := ⟨_, rfl⟩
  have hw1 : ContDiffOn ℝ 3 w₁ {p : ℂ × ℂ | ‖p.1‖ * ‖ν‖ < 1 ∧ p.2 ∈ unitDiscExterior} := by
    rw [hw₁]; exact hval (-1)
  have hw2 : ContDiffOn ℝ 3 w₂ {p : ℂ × ℂ | ‖p.1‖ * ‖ν‖ < 1 ∧ p.2 ∈ unitDiscExterior} := by
    rw [hw₂]; exact hval (-I)
  have hWc : ContDiffOn ℝ 3 Wz {p : ℂ × ℂ | ‖p.1‖ * ‖ν‖ < 1 ∧ p.2 ∈ unitDiscExterior} := by
    rw [hWz]; exact hJ
  have hnum : ContDiffOn ℝ 3 (fun p => (-(1 * (-I - -1)) * (w₂ p - 1) + -(-((-1) * (-I - 1))) * (w₂ p - w₁ p)) *
      Wz p + (-(1 * (-I - -1)) * (-(w₁ p * (w₂ p - 1))) + -(-((-1) * (-I - 1))) * (-(1 * (w₂ p - w₁ p)))))
      {p : ℂ × ℂ | ‖p.1‖ * ‖ν‖ < 1 ∧ p.2 ∈ unitDiscExterior} :=
    (((contDiffOn_const.mul (hw2.sub contDiffOn_const)).add (contDiffOn_const.mul (hw2.sub hw1))).mul hWc).add
      ((contDiffOn_const.mul (hw1.mul (hw2.sub contDiffOn_const)).neg).add
        (contDiffOn_const.mul (contDiffOn_const.mul (hw2.sub hw1)).neg))
  have hden : ContDiffOn ℝ 3 (fun p => (-(-I - -1) * (w₂ p - 1) + (-I - 1) * (w₂ p - w₁ p)) * Wz p +
      (-(-I - -1) * (-(w₁ p * (w₂ p - 1))) + (-I - 1) * (-(1 * (w₂ p - w₁ p)))))
      {p : ℂ × ℂ | ‖p.1‖ * ‖ν‖ < 1 ∧ p.2 ∈ unitDiscExterior} :=
    (((contDiffOn_const.mul (hw2.sub contDiffOn_const)).add (contDiffOn_const.mul (hw2.sub hw1))).mul hWc).add
      ((contDiffOn_const.mul (hw1.mul (hw2.sub contDiffOn_const)).neg).add
        (contDiffOn_const.mul (contDiffOn_const.mul (hw2.sub hw1)).neg))
  have hden0 : ∀ p ∈ {p : ℂ × ℂ | ‖p.1‖ * ‖ν‖ < 1 ∧ p.2 ∈ unitDiscExterior ∧
      wAS (p.1 • ν) (p.2 : ExtPlane) ≠ extInf},
      (-(-I - -1) * (w₂ p - 1) + (-I - 1) * (w₂ p - w₁ p)) * Wz p +
        (-(-I - -1) * (-(w₁ p * (w₂ p - 1))) + (-I - 1) * (-(1 * (w₂ p - w₁ p)))) ≠ 0 := by
    intro p hp
    subst hw₁ hw₂ hWz
    exact (hrep p hp).1
  refine ((hnum.mono hsub).mul ((hden.mono hsub).inv hden0)).congr fun p hp => ?_
  rw [(hrep p hp).2, div_eq_mul_inv]
  subst hw₁ hw₂ hWz
  rfl

end TakhtajanTeo
