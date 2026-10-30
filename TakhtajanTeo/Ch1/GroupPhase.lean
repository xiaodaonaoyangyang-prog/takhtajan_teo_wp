import TakhtajanTeo.Ch1.GroupBaseCompleted
import TakhtajanTeo.Ch1.GroupCov
import TakhtajanTeo.Ch1.GroupOrigin

/-!
# Group topology: `w_ν → id` and the phase `conj (dz w_ν) / dz w_ν → 1` (TT:2030)

Proves the three frozen stubs `gph_near_id`, `gph_phase`, `gph_preimage` (S3phase interface c89d199d) for the
proof of Lemma 3.5.
* `gph_near_id` / `gph_near_id_all`: `w_ν → id` uniformly on balls, for all small `ν ∈ L∞(𝔻*)₁`; proved from
  the plane-normalized solutions `W_n → id` (`grp25b_normalized_tendsto`) and the three-point Möbius
  normalizations `M_n → id` (`gph_mobius_seq`).
* `gph_preimage`: preimages of an annulus stay in an annulus (via `w_ν⁻¹ = w_{ν⁻¹}`).
* `gph_phase`: reflection `z ↔ 1/z̄`, base-point covariance (`grp25c_comparison`: `w_μ ∘ T_a = S ∘ w_μ'`, `S` a
  disc automorphism) and a Cauchy estimate on `S_n - T_n` reduce the phase at `a ∈ 𝔻` to the derivative of
  `w_{μ'}` at the origin, `dz w_{μ'}(0) → 1` (`gph_origin_dz`: the `hWdz` step of `grp25b_density_limit` times
  `M_n'(0) → 1`).
Copies of internal steps (named in their docstrings): `gph_origin_dz`, `gph_transport_dz`, `gph_cov`,
`gph_refl_dz`.
-/

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal NNReal ComplexConjugate Classical Real
noncomputable section
namespace TakhtajanTeo
open LiZhongQC

/-! ### Möbius maps with three nearly fixed points tend to the identity -/

theorem gph_mob_coeffs {p₁ p₂ p₃ : ℂ} (h12 : p₁ ≠ p₂) (h13 : p₁ ≠ p₃) (h23 : p₂ ≠ p₃)
    {M : ExtPlane → ExtPlane} (hM : IsMobius M)
    (e1 : M (p₁ : ExtPlane) = ((-1 : ℂ) : ExtPlane)) (e2 : M (p₂ : ExtPlane) = ((-I : ℂ) : ExtPlane))
    (e3 : M (p₃ : ExtPlane) = ((1 : ℂ) : ExtPlane)) :
    M = mobiusExt ((I - 1) * (p₂ - p₃) + (I + 1) * (p₂ - p₁))
      ((I - 1) * (-p₁ * (p₂ - p₃)) + (I + 1) * (-p₃ * (p₂ - p₁)))
      ((I - 1) * (p₂ - p₃) + (-I - 1) * (p₂ - p₁))
      ((I - 1) * (-p₁ * (p₂ - p₃)) + (-I - 1) * (-p₃ * (p₂ - p₁))) := by
  have d12 : p₂ - p₁ ≠ 0 := sub_ne_zero.2 h12.symm
  have d13 : p₁ - p₃ ≠ 0 := sub_ne_zero.2 h13
  have d23 : p₂ - p₃ ≠ 0 := sub_ne_zero.2 h23
  have hdet : ((I - 1) * (p₂ - p₃) + (I + 1) * (p₂ - p₁)) *
      ((I - 1) * (-p₁ * (p₂ - p₃)) + (-I - 1) * (-p₃ * (p₂ - p₁))) -
      ((I - 1) * (-p₁ * (p₂ - p₃)) + (I + 1) * (-p₃ * (p₂ - p₁))) *
      ((I - 1) * (p₂ - p₃) + (-I - 1) * (p₂ - p₁)) = 4 * ((p₂ - p₃) * (p₂ - p₁) * (p₁ - p₃)) := by
    ring_nf
    try simp only [Complex.I_sq]
    try ring
  have hdet0 : ((I - 1) * (p₂ - p₃) + (I + 1) * (p₂ - p₁)) *
      ((I - 1) * (-p₁ * (p₂ - p₃)) + (-I - 1) * (-p₃ * (p₂ - p₁))) -
      ((I - 1) * (-p₁ * (p₂ - p₃)) + (I + 1) * (-p₃ * (p₂ - p₁))) *
      ((I - 1) * (p₂ - p₃) + (-I - 1) * (p₂ - p₁)) ≠ 0 := by
    rw [hdet]
    exact mul_ne_zero (by norm_num) (mul_ne_zero (mul_ne_zero d23 d12) d13)
  -- the explicit map sends `p₁, p₂, p₃` to `-1, -I, 1`
  have n1 : ((I - 1) * (p₂ - p₃) + (-I - 1) * (p₂ - p₁)) * p₁ +
      ((I - 1) * (-p₁ * (p₂ - p₃)) + (-I - 1) * (-p₃ * (p₂ - p₁))) ≠ 0 := by
    have : ((I - 1) * (p₂ - p₃) + (-I - 1) * (p₂ - p₁)) * p₁ +
      ((I - 1) * (-p₁ * (p₂ - p₃)) + (-I - 1) * (-p₃ * (p₂ - p₁))) =
        (-I - 1) * ((p₂ - p₁) * (p₁ - p₃)) := by ring
    rw [this]
    exact mul_ne_zero (by
      intro h
      have := congrArg Complex.re h
      norm_num at this) (mul_ne_zero d12 d13)
  have n2 : ((I - 1) * (p₂ - p₃) + (-I - 1) * (p₂ - p₁)) * p₂ +
      ((I - 1) * (-p₁ * (p₂ - p₃)) + (-I - 1) * (-p₃ * (p₂ - p₁))) ≠ 0 := by
    have : ((I - 1) * (p₂ - p₃) + (-I - 1) * (p₂ - p₁)) * p₂ +
      ((I - 1) * (-p₁ * (p₂ - p₃)) + (-I - 1) * (-p₃ * (p₂ - p₁))) =
        (-2) * ((p₂ - p₃) * (p₂ - p₁)) := by
      ring_nf
      try simp only [Complex.I_sq]
      try ring
    rw [this]
    exact mul_ne_zero (by
      intro h
      have := congrArg Complex.re h
      norm_num at this) (mul_ne_zero d23 d12)
  have n3 : ((I - 1) * (p₂ - p₃) + (-I - 1) * (p₂ - p₁)) * p₃ +
      ((I - 1) * (-p₁ * (p₂ - p₃)) + (-I - 1) * (-p₃ * (p₂ - p₁))) ≠ 0 := by
    have : ((I - 1) * (p₂ - p₃) + (-I - 1) * (p₂ - p₁)) * p₃ +
      ((I - 1) * (-p₁ * (p₂ - p₃)) + (-I - 1) * (-p₃ * (p₂ - p₁))) =
        (I - 1) * ((p₂ - p₃) * (p₃ - p₁)) := by
      ring_nf
      try simp only [Complex.I_sq]
      try ring
    rw [this]
    exact mul_ne_zero (by
      intro h
      have := congrArg Complex.re h
      norm_num at this) (mul_ne_zero d23 (sub_ne_zero.2 h13.symm))
  have f1 : mobiusExt ((I - 1) * (p₂ - p₃) + (I + 1) * (p₂ - p₁))
      ((I - 1) * (-p₁ * (p₂ - p₃)) + (I + 1) * (-p₃ * (p₂ - p₁)))
      ((I - 1) * (p₂ - p₃) + (-I - 1) * (p₂ - p₁))
      ((I - 1) * (-p₁ * (p₂ - p₃)) + (-I - 1) * (-p₃ * (p₂ - p₁))) (p₁ : ExtPlane) =
        ((-1 : ℂ) : ExtPlane) := by
    rw [mobiusExt_coe n1]
    congr 1
    rw [mobiusFn, div_eq_iff n1]
    ring_nf
    try simp only [Complex.I_sq]
    try ring
  have f2 : mobiusExt ((I - 1) * (p₂ - p₃) + (I + 1) * (p₂ - p₁))
      ((I - 1) * (-p₁ * (p₂ - p₃)) + (I + 1) * (-p₃ * (p₂ - p₁)))
      ((I - 1) * (p₂ - p₃) + (-I - 1) * (p₂ - p₁))
      ((I - 1) * (-p₁ * (p₂ - p₃)) + (-I - 1) * (-p₃ * (p₂ - p₁))) (p₂ : ExtPlane) =
        ((-I : ℂ) : ExtPlane) := by
    rw [mobiusExt_coe n2]
    congr 1
    rw [mobiusFn, div_eq_iff n2]
    ring_nf
    try simp only [Complex.I_sq]
    try ring
  have f3 : mobiusExt ((I - 1) * (p₂ - p₃) + (I + 1) * (p₂ - p₁))
      ((I - 1) * (-p₁ * (p₂ - p₃)) + (I + 1) * (-p₃ * (p₂ - p₁)))
      ((I - 1) * (p₂ - p₃) + (-I - 1) * (p₂ - p₁))
      ((I - 1) * (-p₁ * (p₂ - p₃)) + (-I - 1) * (-p₃ * (p₂ - p₁))) (p₃ : ExtPlane) =
        ((1 : ℂ) : ExtPlane) := by
    rw [mobiusExt_coe n3]
    congr 1
    rw [mobiusFn, div_eq_iff n3]
    ring_nf
    try simp only [Complex.I_sq]
    try ring
  exact mobius_eq_of_three_points hM ⟨_, _, _, _, hdet0, rfl⟩ h12 h13 h23 (e1.trans f1.symm)
    (e2.trans f2.symm) (e3.trans f3.symm)

theorem gph_mobius_seq {M : ℕ → ExtPlane → ExtPlane} (hM : ∀ n, IsMobius (M n))
    {p₁ p₂ p₃ : ℕ → ℂ}
    (e1 : ∀ n, M n (p₁ n : ExtPlane) = ((-1 : ℂ) : ExtPlane))
    (e2 : ∀ n, M n (p₂ n : ExtPlane) = ((-I : ℂ) : ExtPlane))
    (e3 : ∀ n, M n (p₃ n : ExtPlane) = ((1 : ℂ) : ExtPlane))
    (t1 : Tendsto p₁ atTop (𝓝 (-1))) (t2 : Tendsto p₂ atTop (𝓝 (-I))) (t3 : Tendsto p₃ atTop (𝓝 1))
    {x : ℕ → ℂ} {x₀ : ℂ} (hx : Tendsto x atTop (𝓝 x₀)) :
    (∀ᶠ n in atTop, M n (x n : ExtPlane) = ((finPart (M n (x n : ExtPlane)) : ℂ) : ExtPlane) ∧
        HasDerivAt (fun z : ℂ => finPart (M n (z : ExtPlane)))
          (deriv (fun z : ℂ => finPart (M n (z : ExtPlane))) (x n)) (x n)) ∧
      Tendsto (fun n => finPart (M n (x n : ExtPlane))) atTop (𝓝 x₀) ∧
      Tendsto (fun n => deriv (fun z : ℂ => finPart (M n (z : ExtPlane))) (x n)) atTop (𝓝 1) := by
  have ne12 : (-1 : ℂ) ≠ -I := by
    intro h
    have := congrArg Complex.re h
    norm_num at this
  have ne13 : (-1 : ℂ) ≠ 1 := by norm_num
  have ne23 : (-I : ℂ) ≠ 1 := by
    intro h
    have := congrArg Complex.re h
    norm_num at this
  have d12 : ∀ᶠ n in atTop, p₁ n ≠ p₂ n :=
    (t1.prodMk_nhds t2).eventually (isOpen_ne_fun continuous_fst continuous_snd |>.mem_nhds ne12)
  have d13 : ∀ᶠ n in atTop, p₁ n ≠ p₃ n :=
    (t1.prodMk_nhds t3).eventually (isOpen_ne_fun continuous_fst continuous_snd |>.mem_nhds ne13)
  have d23 : ∀ᶠ n in atTop, p₂ n ≠ p₃ n :=
    (t2.prodMk_nhds t3).eventually (isOpen_ne_fun continuous_fst continuous_snd |>.mem_nhds ne23)
  set A : ℕ → ℂ := fun n => (I - 1) * (p₂ n - p₃ n) + (I + 1) * (p₂ n - p₁ n) with hAd
  set B : ℕ → ℂ := fun n => (I - 1) * (-p₁ n * (p₂ n - p₃ n)) + (I + 1) * (-p₃ n * (p₂ n - p₁ n)) with hBd
  set C : ℕ → ℂ := fun n => (I - 1) * (p₂ n - p₃ n) + (-I - 1) * (p₂ n - p₁ n) with hCd
  set D : ℕ → ℂ := fun n => (I - 1) * (-p₁ n * (p₂ n - p₃ n)) + (-I - 1) * (-p₃ n * (p₂ n - p₁ n)) with hDd
  have cA : Tendsto A atTop (𝓝 4) := by
    have h := ((t2.sub t3).const_mul (I - 1)).add ((t2.sub t1).const_mul (I + 1))
    have e : (I - 1) * (-I - 1) + (I + 1) * (-I - -1) = 4 := by
      ring_nf
      try simp only [Complex.I_sq]
      try ring
    rwa [e] at h
  have cB : Tendsto B atTop (𝓝 0) := by
    have h := (((t1.neg).mul (t2.sub t3)).const_mul (I - 1)).add
      (((t3.neg).mul (t2.sub t1)).const_mul (I + 1))
    have e : (I - 1) * (-(-1) * (-I - 1)) + (I + 1) * (-1 * (-I - -1)) = 0 := by
      ring_nf
      try simp only [Complex.I_sq]
      try ring
    rwa [e] at h
  have cC : Tendsto C atTop (𝓝 0) := by
    have h := ((t2.sub t3).const_mul (I - 1)).add ((t2.sub t1).const_mul (-I - 1))
    have e : (I - 1) * (-I - 1) + (-I - 1) * (-I - -1) = 0 := by
      ring_nf
      try simp only [Complex.I_sq]
      try ring
    rwa [e] at h
  have cD : Tendsto D atTop (𝓝 4) := by
    have h := (((t1.neg).mul (t2.sub t3)).const_mul (I - 1)).add
      (((t3.neg).mul (t2.sub t1)).const_mul (-I - 1))
    have e : (I - 1) * (-(-1) * (-I - 1)) + (-I - 1) * (-1 * (-I - -1)) = 4 := by
      ring_nf
      try simp only [Complex.I_sq]
      try ring
    rwa [e] at h
  have cden : Tendsto (fun n => C n * x n + D n) atTop (𝓝 4) := by
    have h := (cC.mul hx).add cD
    rwa [zero_mul, zero_add] at h
  have cnum : Tendsto (fun n => A n * x n + B n) atTop (𝓝 (4 * x₀)) := by
    have h := (cA.mul hx).add cB
    rwa [add_zero] at h
  have hne : ∀ᶠ n in atTop, C n * x n + D n ≠ 0 :=
    cden.eventually_ne (by norm_num)
  have hMeq : ∀ᶠ n in atTop, M n = mobiusExt (A n) (B n) (C n) (D n) := by
    filter_upwards [d12, d13, d23] with n h1 h2 h3
    exact gph_mob_coeffs h1 h2 h3 (hM n) (e1 n) (e2 n) (e3 n)
  have hfp : ∀ᶠ n in atTop, ∀ z : ℂ, C n * z + D n ≠ 0 →
      finPart (M n (z : ExtPlane)) = (A n * z + B n) / (C n * z + D n) := by
    filter_upwards [hMeq] with n hn z hz
    rw [hn, mobiusExt_coe hz]
    rfl
  have hder : ∀ᶠ n in atTop, HasDerivAt (fun z : ℂ => finPart (M n (z : ExtPlane)))
      ((A n * (C n * x n + D n) - (A n * x n + B n) * C n) / (C n * x n + D n) ^ 2) (x n) := by
    filter_upwards [hfp, hne] with n hn hne'
    have hc : Continuous (fun z : ℂ => C n * z + D n) := by fun_prop
    have hev : (fun z : ℂ => (A n * z + B n) / (C n * z + D n)) =ᶠ[𝓝 (x n)]
        fun z : ℂ => finPart (M n (z : ExtPlane)) := by
      filter_upwards [hc.continuousAt.eventually_ne hne'] with z hz
      exact (hn z hz).symm
    have h1 : HasDerivAt (fun z : ℂ => A n * z + B n) (A n) (x n) := by
      simpa using ((hasDerivAt_id (x n)).const_mul (A n)).add_const (B n)
    have h2 : HasDerivAt (fun z : ℂ => C n * z + D n) (C n) (x n) := by
      simpa using ((hasDerivAt_id (x n)).const_mul (C n)).add_const (D n)
    have h3 := h1.div h2 hne'
    exact (h3.congr_of_eventuallyEq hev.symm)
  refine ⟨?_, ?_, ?_⟩
  · filter_upwards [hMeq, hfp, hne, hder] with n hn hfn hne' hd
    refine ⟨?_, hd.differentiableAt.hasDerivAt⟩
    rw [hfn (x n) hne', hn, mobiusExt_coe hne']
    rfl
  · have hq : Tendsto (fun n => (A n * x n + B n) / (C n * x n + D n)) atTop (𝓝 (4 * x₀ / 4)) :=
      cnum.div cden (by norm_num)
    rw [mul_div_cancel_left₀ _ (by norm_num : (4 : ℂ) ≠ 0)] at hq
    refine hq.congr' ?_
    filter_upwards [hfp, hne] with n hn hne'
    exact (hn (x n) hne').symm
  · have hq : Tendsto (fun n => (A n * (C n * x n + D n) - (A n * x n + B n) * C n) /
        (C n * x n + D n) ^ 2) atTop (𝓝 ((4 * 4 - 4 * x₀ * 0) / 4 ^ 2)) :=
      ((cA.mul cden).sub (cnum.mul cC)).div (cden.pow 2) (by norm_num)
    have e : ((4 : ℂ) * 4 - 4 * x₀ * 0) / 4 ^ 2 = 1 := by norm_num
    rw [e] at hq
    refine hq.congr' ?_
    filter_upwards [hder] with n hd
    exact hd.deriv.symm

/-! ### The plane-normalized solutions and the Möbius normalizations along a sequence `ν_n → 0` -/

theorem gph_seq_pkg {ν : ℕ → LinfStar} (hb : ∀ n, ν n ∈ LinfStarBall) (hs : ∀ n, ‖ν n‖ < 1 / 4)
    (hlim : Tendsto (fun n => ‖ν n‖) atTop (𝓝 0)) :
    ∃ (W : ℕ → ℂ → ℂ) (M : ℕ → ExtPlane → ExtPlane),
      (∀ n, IsNormalizedSolution (W n) (extA (ν n))) ∧ (∀ n, IsMobius (M n)) ∧
      (∀ n (z : ℂ), wAS (ν n) (z : ExtPlane) = M n ((W n z : ℂ) : ExtPlane)) ∧
      TendstoLocallyUniformly W id atTop ∧
      (∀ n, M n ((W n (-1) : ℂ) : ExtPlane) = ((-1 : ℂ) : ExtPlane)) ∧
      (∀ n, M n ((W n (-I) : ℂ) : ExtPlane) = ((-I : ℂ) : ExtPlane)) ∧
      (∀ n, M n ((W n 1 : ℂ) : ExtPlane) = ((1 : ℂ) : ExtPlane)) := by
  have hex : ∀ n, ∃ W : ℂ → ℂ, IsNormalizedSolution W (extA (ν n)) ∧
      IsKQC W univ ((1 + ‖ν n‖) / (1 - ‖ν n‖)) ∧ ∃ M : ExtPlane → ExtPlane, IsMobius M ∧
      (∀ z : ℂ, wAS (ν n) (z : ExtPlane) = M ((W z : ℂ) : ExtPlane)) ∧
      wAS (ν n) ((-1 : ℂ) : ExtPlane) = ((-1 : ℂ) : ExtPlane) ∧
      wAS (ν n) ((-I : ℂ) : ExtPlane) = ((-I : ℂ) : ExtPlane) ∧
      wAS (ν n) ((1 : ℂ) : ExtPlane) = ((1 : ℂ) : ExtPlane) := by
    intro n
    obtain ⟨W, hW, hK, huniq⟩ := extA_normalized_plane_exists (hb n)
    obtain ⟨M, hM, W', hW', hfin, -, h1, h2, h3⟩ := wA_spec (hb n)
    have hWW : W' = W := huniq W' hW'
    subst hWW
    exact ⟨W', hW', hK, M, hM, hfin, h1, h2, h3⟩
  choose W hW hK M hM hfin hw1 hw2 hw3 using hex
  refine ⟨W, M, hW, hM, hfin, ?_, ?_, ?_, ?_⟩
  · let Kn : ℕ → ℝ := fun n => (1 + ‖ν n‖) / (1 - ‖ν n‖)
    have hKbound : ∀ n, Kn n ≤ 3 := by
      intro n
      dsimp only [Kn]
      rw [div_le_iff₀ (by linarith [hs n] : 0 < 1 - ‖ν n‖)]
      linarith [hs n]
    have hKlim : Tendsto Kn atTop (𝓝 1) := by
      have hc : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
      have he : Kn = ((fun n => 1 + ‖ν n‖) / (fun n => 1 - ‖ν n‖)) := by
        funext n
        rfl
      rw [he]
      simpa only [add_zero, sub_zero, div_one] using
        (hc.add hlim).div (hc.sub hlim) (by norm_num : (1 : ℝ) - 0 ≠ 0)
    exact grp25b_normalized_tendsto (Kn := Kn) (Kbar := 3) hK hKbound
      (fun n => ⟨(hW n).2.1, (hW n).2.2.1, (hW n).2.2.2.1⟩) hKlim
  · intro n
    have := hfin n (-1)
    rw [hw1 n] at this
    exact this.symm
  · intro n
    have := hfin n (-I)
    rw [hw2 n] at this
    exact this.symm
  · intro n
    have := hfin n 1
    rw [hw3 n] at this
    exact this.symm

theorem gph_near_id_seq {ν : ℕ → LinfStar} (hb : ∀ n, ν n ∈ LinfStarBall) (hs : ∀ n, ‖ν n‖ < 1 / 4)
    (hlim : Tendsto (fun n => ‖ν n‖) atTop (𝓝 0)) {z : ℕ → ℂ} {z₀ : ℂ} (hz : Tendsto z atTop (𝓝 z₀)) :
    (∀ᶠ n in atTop, wAS (ν n) (z n : ExtPlane) ≠ extInf) ∧
      Tendsto (fun n => wA (ν n) (z n)) atTop (𝓝 z₀) := by
  obtain ⟨W, M, hW, hM, hfin, hWlim, h1, h2, h3⟩ := gph_seq_pkg hb hs hlim
  have hp : ∀ p : ℂ, Tendsto (fun n => W n p) atTop (𝓝 p) := fun p =>
    hWlim.tendstoLocallyUniformlyOn.tendsto_at (mem_univ p)
  have hx : Tendsto (fun n => W n (z n)) atTop (𝓝 z₀) :=
    hWlim.tendsto_comp continuous_id.continuousAt hz
  obtain ⟨hev, hy, -⟩ := gph_mobius_seq hM h1 h2 h3 (hp (-1)) (hp (-I)) (hp 1) hx
  refine ⟨?_, ?_⟩
  · filter_upwards [hev] with n hn
    rw [hfin n (z n), hn.1]
    exact OnePoint.coe_ne_infty _
  · refine hy.congr' ?_
    filter_upwards [hev] with n hn
    show finPart (M n ((W n (z n) : ℂ) : ExtPlane)) = finPart (wAS (ν n) (z n : ExtPlane))
    rw [hfin n (z n)]

/-- `w_ν → id` on all balls `|z| ≤ R`, uniformly over all `ν ∈ L∞(𝔻*)₁` with `‖ν‖∞` small (finite values:
the pole of `w_ν` has escaped). -/
theorem gph_near_id_all {R ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ ν ∈ LinfStarBall, ‖ν‖ < δ → ∀ z : ℂ, ‖z‖ ≤ R →
      wAS ν (z : ExtPlane) ≠ extInf ∧ ‖wA ν z - z‖ < ε := by
  by_contra hcon
  push_neg at hcon
  choose ν hνb hνlt z hzR hbad using fun n : ℕ =>
    hcon (min (1 / 5) (1 / ((n : ℝ) + 1))) (lt_min (by norm_num) (by positivity))
  have hs : ∀ n, ‖ν n‖ < 1 / 4 := fun n =>
    lt_of_lt_of_le ((hνlt n).trans_le (min_le_left _ _)) (by norm_num)
  have hlim : Tendsto (fun n => ‖ν n‖) atTop (𝓝 0) :=
    squeeze_zero (fun n => norm_nonneg _) (fun n => ((hνlt n).trans_le (min_le_right _ _)).le)
      tendsto_one_div_add_atTop_nhds_zero_nat
  obtain ⟨z₀, -, φ, hφ, hzφ⟩ := tendsto_subseq_of_bounded (Metric.isBounded_closedBall (x := (0 : ℂ)) (r := R))
    (fun n => mem_closedBall_zero_iff.2 (hzR n))
  obtain ⟨hev, hlimw⟩ := gph_near_id_seq (fun n => hνb (φ n)) (fun n => hs (φ n))
    (hlim.comp hφ.tendsto_atTop) hzφ
  have hd : Tendsto (fun n => wA (ν (φ n)) (z (φ n)) - z (φ n)) atTop (𝓝 0) := by
    simpa using hlimw.sub hzφ
  have hsmall : ∀ᶠ n in atTop, ‖wA (ν (φ n)) (z (φ n)) - z (φ n)‖ < ε :=
    (tendsto_zero_iff_norm_tendsto_zero.1 hd).eventually (gt_mem_nhds hε)
  obtain ⟨n, hn1, hn2⟩ := (hev.and hsmall).exists
  exact absurd (hbad (φ n) hn1) (not_le.2 hn2)

/-- `w_ν → id` on the closed annuli `r ≤ |z| ≤ R` of `𝔻*`, uniformly over all `ν ∈ L∞(𝔻*)₁` with `‖ν‖∞`
small (finite values: the pole of `w_ν` has escaped). -/
theorem gph_near_id {r R ε : ℝ} (hr : 1 < r) (hε : 0 < ε) :
    ∃ δ > 0, ∀ ν ∈ LinfStarBall, ‖ν‖ < δ → ∀ z : ℂ, r ≤ ‖z‖ → ‖z‖ ≤ R →
      wAS ν (z : ExtPlane) ≠ extInf ∧ ‖wA ν z - z‖ < ε := by
  obtain ⟨δ, hδ, h⟩ := gph_near_id_all (R := R) hε
  exact ⟨δ, hδ, fun ν hν hνδ z _ hzR => h ν hν hνδ z hzR⟩

/-- Preimages of a compact annulus of `𝔻*` under `w_ν` stay in a fixed compact annulus (the substitute for the
use of Mori's theorem in TT:2010–2014; follows from `gph_near_id` applied to `ν⁻¹`). -/
theorem gph_preimage {r R : ℝ} (hr : 1 < r) :
    ∃ r' R' δ : ℝ, 1 < r' ∧ 0 < δ ∧ ∀ ν ∈ LinfStarBall, ‖ν‖ < δ → ∀ z : ℂ, 1 < ‖z‖ →
      wAS ν (z : ExtPlane) ≠ extInf → r ≤ ‖wA ν z‖ → ‖wA ν z‖ ≤ R → r' ≤ ‖z‖ ∧ ‖z‖ ≤ R' := by
  have hε : 0 < (r - 1) / 2 := by linarith
  obtain ⟨δ, hδ, hnear⟩ := gph_near_id (R := R) hr hε
  refine ⟨r - (r - 1) / 2, R + (r - 1) / 2, δ, by linarith, hδ, ?_⟩
  intro ν hν hνδ z _ hne hr1 hR1
  have hi := bc_beltramiInv_mem_ball hν
  have hlt : ‖beltramiInv ν‖ < δ := lt_of_le_of_lt (bc_beltramiInv_norm_le hν) hνδ
  have hw : wAS ν (z : ExtPlane) = ((wA ν z : ℂ) : ExtPlane) := by
    obtain ⟨u, hu⟩ := OnePoint.ne_infty_iff_exists.1 hne
    rw [← hu]
    show _ = (((finPart (wAS ν (z : ExtPlane))) : ℂ) : ExtPlane)
    rw [← hu]
    rfl
  obtain ⟨-, hclose⟩ := hnear (beltramiInv ν) hi hlt (wA ν z) hr1 hR1
  have hinv := bg_inverse_left_sphere hν (z : ExtPlane)
  rw [hw] at hinv
  have hz : wA (beltramiInv ν) (wA ν z) = z := by
    show finPart (wAS (beltramiInv ν) ((wA ν z : ℂ) : ExtPlane)) = z
    rw [hinv]
    rfl
  rw [hz] at hclose
  have h1 : ‖wA ν z‖ - ‖z‖ ≤ ‖z - wA ν z‖ := by
    have := norm_sub_norm_le (wA ν z) z
    rwa [norm_sub_rev] at this
  have h2 : ‖z‖ - ‖wA ν z‖ ≤ ‖z - wA ν z‖ := norm_sub_norm_le z (wA ν z)
  constructor <;> linarith [norm_sub_rev z (wA ν z)]

/-! ### The derivative of `w_ν` at the origin tends to `1` (with phase) -/

/-- Copy of the proof of `grp25b_small_sequence` and of the `hWdz` step of `grp25b_density_limit` (both internal
there): for harmonic `ν_n → 0`, the complex derivative `dz (w_{ν_n}) 0 → 1`. -/
theorem gph_origin_dz {ν : ℕ → LinfStar} (hh : ∀ n, ν n ∈ harmonicBeltrami) (hs : ∀ n, ‖ν n‖ < 1 / 4)
    (hlim : Tendsto (fun n => ‖ν n‖) atTop (𝓝 0)) :
    Tendsto (fun n => dz (wA (ν n)) 0) atTop (𝓝 1) := by
  have hball : ∀ n, ν n ∈ LinfStarBall := fun n => by
    simpa [LinfStarBall] using (show ‖ν n‖ < 1 by linarith [hs n])
  choose φ hφ using (fun n => Lambda_surjective_harmonic (hh n))
  have hnorm : ∀ n, ‖φ n‖ / 2 = ‖ν n‖ := by
    intro n
    rw [← Lambda_norm_eq, hφ n]
  let Kn : ℕ → ℝ := fun n => (1 + ‖ν n‖) / (1 - ‖ν n‖)
  have hKbound : ∀ n, Kn n ≤ 3 := by
    intro n
    dsimp only [Kn]
    rw [div_le_iff₀ (by linarith [hs n] : 0 < 1 - ‖ν n‖)]
    linarith [hs n]
  have hKlim : Tendsto Kn atTop (𝓝 1) := by
    have hc : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
    have he : Kn = ((fun n => 1 + ‖ν n‖) / (fun n => 1 - ‖ν n‖)) := by
      funext n
      rfl
    rw [he]
    simpa only [add_zero, sub_zero, div_one] using
      (hc.add hlim).div (hc.sub hlim) (by norm_num : (1 : ℝ) - 0 ≠ 0)
  have hex : ∀ n, ∃ e : ℂ ≃ₜ ℂ, IsKQC (e : ℂ → ℂ) univ (Kn n) ∧ e 0 = 0 ∧ e 1 = 1 ∧
      DifferentiableOn ℂ (e : ℂ → ℂ) lowerHalf ∧
      (∀ z ∈ upperHalf, complexDilatation (e : ℂ → ℂ) z = -2 * (z.im : ℂ) ^ 2 * awPhi (φ n) (conj z)) ∧
      (∀ z ∈ upperHalf, ContDiffAt ℝ 1 (e : ℂ → ℂ) z ∧ dz (e : ℂ → ℂ) z ≠ 0) ∧
      ∀ z ∈ upperHalf, dz (e : ℂ → ℂ) z = deriv (e : ℂ → ℂ) (conj z) /
        (1 - (z - conj z) * deriv (deriv (e : ℂ → ℂ)) (conj z) /
          (2 * deriv (e : ℂ → ℂ) (conj z))) ^ 2 := by
    intro n
    obtain ⟨H, hHK, hHs, hH0, hH1, hHd, hHμ, hHr, hHj⟩ :=
      grp25b_core (s := ‖φ n‖ / 4) (by positivity) (by linarith [hnorm n, hs n])
        (aw_phi_diff (φ n)) (fun z hz => aw_phi_bound (φ n) hz)
    have he : 4 * (‖φ n‖ / 4) / 2 = ‖ν n‖ := by linarith [hnorm n]
    have hHK' : IsKQC H univ (Kn n) := by simpa only [he] using hHK
    obtain ⟨e, rfl⟩ := t1_homeomorph hHK' hHs
    exact ⟨e, hHK', hH0, hH1, hHd, hHμ, hHr, hHj⟩
  choose H hHK hH0 hH1 hHhol hHμ hHreg hHjet using hex
  have hHlim : TendstoLocallyUniformly (fun n => (H n : ℂ → ℂ)) id atTop :=
    grp25b_normalized_tendsto hHK hKbound (fun n => ⟨by
      rw [image_univ]; exact Set.range_eq_univ.mpr (H n).surjective, hH0 n, hH1 n⟩) hKlim
  have hHdz : Tendsto (fun n => dz (H n : ℂ → ℂ) I) atTop (𝓝 1) :=
    grp25b_aw_dz_tendsto hHhol hHlim (fun n => hHjet n I (by simp [upperHalf]))
  choose F τ hFK hF0 hF1 hFdil hτcd hτ0 hτdz hτrel using
    (fun n => grp25b_chart (H n) (hHK n) (hHhol n) (hHμ n) (hHreg n))
  have hFlim : TendstoLocallyUniformly (fun n => (F n : ℂ → ℂ)) id atTop :=
    grp25b_normalized_tendsto hFK hKbound (fun n => ⟨by
      rw [image_univ]; exact Set.range_eq_univ.mpr (F n).surjective, hF0 n, hF1 n⟩) hKlim
  have hWex : ∀ n, ∃ W : ℂ ≃ₜ ℂ, IsNormalizedSolution (W : ℂ → ℂ) (extA (ν n)) ∧
      IsKQC (W : ℂ → ℂ) univ (Kn n) ∧ ∃ M : ExtPlane → ExtPlane, IsMobius M ∧
      (∀ z : ℂ, wAS (ν n) (z : ExtPlane) = M ((W z : ℂ) : ExtPlane)) ∧
      M (((W (-1) : ℂ)) : ExtPlane) = ((-1 : ℂ) : ExtPlane) ∧
      M (((W (-I) : ℂ)) : ExtPlane) = ((-I : ℂ) : ExtPlane) ∧
      M (((W 1 : ℂ)) : ExtPlane) = ((1 : ℂ) : ExtPlane) := by
    intro n
    obtain ⟨M, hM, W, hW, hfin, -, h1, h2, h3⟩ := wA_spec (hball n)
    obtain ⟨K, hWK⟩ := hW.1
    have hsol := nxS_genHomeoSolution_congr (thm10_2_genHomeoSolution_of_isKQC hWK).2
      (by simpa only [Measure.restrict_univ] using hW.2.2.2.2)
    have hWK' : IsKQC W univ (Kn n) := thm10_2_isKQC_of_genHomeoSolution isOpen_univ
      (norm_nonneg _) (by linarith [hs n]) (extA_isBeltramiCoeff (ν n)) hsol
    obtain ⟨e, rfl⟩ := t1_homeomorph hWK' hW.2.1
    refine ⟨e, hW, hWK', M, hM, hfin, ?_, ?_, ?_⟩
    · have := hfin (-1)
      rw [h1] at this
      exact this.symm
    · have := hfin (-I)
      rw [h2] at this
      exact this.symm
    · have := hfin 1
      rw [h3] at this
      exact this.symm
  choose W hW hWK M hM hfin hm1 hm2 hm3 using hWex
  have hWlim : TendstoLocallyUniformly (fun n => (W n : ℂ → ℂ)) id atTop :=
    grp25b_normalized_tendsto hWK hKbound (fun n => ⟨(hW n).2.1, (hW n).2.2.1, (hW n).2.2.2.1⟩) hKlim
  have hE : IsOpen unitDiscExterior := isOpen_lt continuous_const continuous_norm
  have hψex : ∀ n, ∃ ψ : ℂ → ℂ,
      IsConformalOnto ψ (F n '' unitDiscExterior) (W n '' unitDiscExterior) ∧
        ∀ z ∈ unitDiscExterior, W n z = ψ (F n z) := by
    intro n
    apply grp_stoilow hE ⟨Kn n, nx_isKQC_restrict (hFK n) hE (subset_univ _)⟩
      ⟨Kn n, nx_isKQC_restrict (hWK n) hE (subset_univ _)⟩
    filter_upwards [hFdil n, ae_restrict_of_ae (hW n).2.2.2.2,
      ae_restrict_mem hE.measurableSet] with z hz₁ hz₂ hzE
    rw [hz₁, hz₂, hφ n]
    exact (extA_eq_on_exterior _ hzE).symm
  choose ψ hψ hrel using hψex
  have hHI : Tendsto (fun n => H n I) atTop (𝓝 I) :=
    hHlim.tendstoLocallyUniformlyOn.tendsto_at (mem_univ I)
  have hHm : Tendsto (fun n => H n (-I)) atTop (𝓝 (-I)) :=
    hHlim.tendstoLocallyUniformlyOn.tendsto_at (mem_univ (-I))
  have hτlim : Tendsto (fun n => dz (τ n) 0) atTop (𝓝 1) := by
    have hc : Tendsto (fun _ : ℕ => 2 * I) atTop (𝓝 (2 * I)) := tendsto_const_nhds
    have hne : I - -I ≠ 0 := by intro hh; have := congrArg Complex.im hh; norm_num at this
    have hh := (hHdz.mul hc).div (hHI.sub hHm) hne
    have he : 1 * (2 * I) / (I - -I) = (1 : ℂ) := by
      rw [show I - -I = 2 * I by ring]
      norm_num
    rw [he] at hh
    exact hh.congr (fun n => (hτdz n).symm)
  -- the step `hWdz` of `grp25b_density_limit`
  let ξ : ℕ → ℂ → ℂ := fun n t => (W n ((F n).symm t⁻¹))⁻¹
  have hbound := grp25b_eventually_disc_bound hFlim
  have hdiff : ∀ᶠ n in atTop, DifferentiableOn ℂ (ξ n) (ball 0 (1 / 3)) := by
    filter_upwards [hbound] with n hn
    exact grp25b_transition_analytic (F n) (W n) (hF0 n) (hW n).2.2.1 (hψ n) (hrel n) hn
  have hξlim : TendstoLocallyUniformlyOn ξ id atTop (ball (0 : ℂ) (1 / 3) \ {0}) :=
    (grp_transition_reciprocal_tendsto hFlim hWlim).mono (fun _ hx => hx.2)
  obtain ⟨N, hN⟩ := eventually_atTop.mp hdiff
  have htail : TendstoLocallyUniformlyOn (fun n => ξ (n + N)) id atTop
      (ball (0 : ℂ) (1 / 3) \ {0}) := by
    intro u hu x hx
    obtain ⟨s, hs', hh'⟩ := hξlim u hu x hx
    exact ⟨s, hs', (tendsto_add_atTop_nat N).eventually hh'⟩
  have hder : Tendsto (fun n => deriv (ξ n) 0) atTop (𝓝 (1 : ℂ)) := by
    apply (tendsto_add_atTop_iff_nat N).mp
    simpa using grp25h_deriv_center (by norm_num : (0 : ℝ) < 1 / 3)
      (fun n => hN (n + N) (Nat.le_add_left N n)) differentiableOn_id htail
  have hpoint : ∀ᶠ n in atTop, ContDiffAt ℝ 1 (W n : ℂ → ℂ) 0 ∧
      dz (W n : ℂ → ℂ) 0 = conj (deriv (ξ n) 0 * dz (τ n) 0) := by
    filter_upwards [hdiff] with n hn
    exact grp25b_transition_dz (F n) (W n) (hF0 n) (hW n) (hτcd n) (hτ0 n) (hτrel n)
      (hn.analyticOnNhd isOpen_ball 0 (mem_ball_self (by norm_num)))
  have hWdz : Tendsto (fun n => dz (W n : ℂ → ℂ) 0) atTop (𝓝 (1 : ℂ)) := by
    have hh := (Complex.continuous_conj.tendsto (1 * 1)).comp (hder.mul hτlim)
    have hh' : Tendsto (fun n => conj (deriv (ξ n) 0 * dz (τ n) 0)) atTop (𝓝 (1 : ℂ)) := by
      simpa only [Function.comp_def, mul_one, map_one] using hh
    exact hh'.congr' (hpoint.mono (fun n hn => hn.2.symm))
  -- the Möbius normalization
  have hp : ∀ p : ℂ, Tendsto (fun n => W n p) atTop (𝓝 p) := fun p =>
    hWlim.tendstoLocallyUniformlyOn.tendsto_at (mem_univ p)
  obtain ⟨hev, -, hmlim⟩ := gph_mobius_seq (x := fun n => W n 0) (x₀ := 0) hM hm1 hm2 hm3 (hp (-1)) (hp (-I))
    (hp 1) (hp 0)
  have hfinp : ∀ n, wA (ν n) = fun z => finPart (M n (((W n z : ℂ)) : ExtPlane)) := by
    intro n
    funext z
    show finPart (wAS (ν n) (z : ExtPlane)) = _
    rw [hfin n z]
  have hlast : ∀ᶠ n in atTop, dz (wA (ν n)) 0 =
      deriv (fun w : ℂ => finPart (M n (w : ExtPlane))) (W n 0) * dz (W n : ℂ → ℂ) 0 := by
    filter_upwards [hev, hpoint] with n hn hp'
    have hd := hn.2.differentiableAt
    obtain ⟨-, hdz⟩ := grp_dz_comp_holo (f := (W n : ℂ → ℂ)) (g := fun w : ℂ => finPart (M n (w : ExtPlane)))
      (z := 0) (hp'.1.differentiableAt (by norm_num)) hd
    rw [hfinp n]
    exact hdz
  have hprod := hmlim.mul hWdz
  rw [one_mul] at hprod
  exact hprod.congr' (hlast.mono fun n hn => hn.symm)

/-! ### Base-point transport of the derivative (complex form) -/

/-- Complex form of `grp25c_transport` (copy of its first half, internal there): from
`F ∘ T_a = S ∘ G` on `𝔻` one gets `dz F a · (1 - |a|²) = S'(G 0) · dz G 0`. -/
theorem gph_transport_dz {F G S : ℂ → ℂ} {a : ℂ} (ha : a ∈ unitDisc)
    (hS : IsConformalOnto S unitDisc unitDisc) (hG0 : G 0 ∈ unitDisc)
    (he : EqOn (fun z => F (blaschke (-a) z)) (fun z => S (G z)) unitDisc)
    (hG : ContDiffAt ℝ 1 G 0) :
    ContDiffAt ℝ 1 F a ∧ dz F a * ((1 - ‖a‖ ^ 2 : ℝ) : ℂ) = deriv S (G 0) * dz G 0 := by
  have han : ‖a‖ < 1 := mem_ball_zero_iff.mp ha
  have hna : ‖-a‖ < 1 := by simpa using han
  have hD : IsOpen unitDisc := isOpen_ball
  have h0 : (0 : ℂ) ∈ unitDisc := mem_ball_self one_pos
  have hSg : ContDiffAt ℝ 1 S (G 0) :=
    ((hS.1.contDiffOn hD).contDiffAt (hD.mem_nhds hG0)).restrict_scalars ℝ
  have hSG := hSg.comp 0 hG
  have hBa : ContDiffAt ℝ 1 (blaschke a) a :=
    (((differentiableOn_blaschke han).contDiffOn hD).contDiffAt (hD.mem_nhds ha)).restrict_scalars ℝ
  have hBaa : blaschke a a = 0 := by simp [blaschke]
  have hFa : ContDiffAt ℝ 1 F a := by
    have hcomp : ContDiffAt ℝ 1 (fun z => S (G (blaschke a z))) a := by
      have hSG' : ContDiffAt ℝ 1 (fun z => S (G z)) (blaschke a a) := by rwa [hBaa]
      exact hSG'.comp a hBa
    apply hcomp.congr_of_eventuallyEq
    filter_upwards [hD.mem_nhds ha] with z hz
    have hBz : blaschke a z ∈ unitDisc :=
      mem_ball_zero_iff.mpr (blaschke_mem_unitDisc han (mem_ball_zero_iff.mp hz))
    have hh := he hBz
    dsimp only at hh
    rwa [blaschke_neg_blaschke han (mem_ball_zero_iff.mp hz)] at hh
  have hT0 : blaschke (-a) 0 = a := by simp [blaschke]
  have hFdiff : DifferentiableAt ℝ F a := hFa.differentiableAt (by norm_num)
  have hGdiff : DifferentiableAt ℝ G 0 := hG.differentiableAt (by norm_num)
  have hTdiff : DifferentiableAt ℂ (blaschke (-a)) 0 :=
    (differentiableOn_blaschke hna).differentiableAt (hD.mem_nhds h0)
  have hdF := (eq6_4 hTdiff (by simpa only [hT0] using hFdiff)).1
  have hdG := (eq6_5 hGdiff (hS.1.differentiableAt (hD.mem_nhds hG0))).1
  have hev : (F ∘ blaschke (-a)) =ᶠ[𝓝 0] (S ∘ G) := by
    filter_upwards [hD.mem_nhds h0] with z hz
    exact he hz
  have hd := (t203_c1_dz_congr hev).1
  rw [hdF, hdG, hT0] at hd
  have hder : deriv (blaschke (-a)) 0 = ((1 - ‖a‖ ^ 2 : ℝ) : ℂ) := by
    rw [(hasDerivAt_blaschke hna (by simp)).deriv]
    simp only [map_neg, neg_mul_neg, mul_zero, sub_zero, one_pow, div_one, Complex.mul_conj']
    push_cast
    rfl
  rw [hder] at hd
  exact ⟨hFa, hd⟩

/-! ### A holomorphic self-map of the disc close (in sup norm) to a Möbius map has close derivative -/

theorem gph_deriv_bound {S : ℂ → ℂ} (hS : IsConformalOnto S unitDisc unitDisc) {x : ℂ} (hx : ‖x‖ ≤ 3 / 4) :
    ‖deriv S x‖ ≤ 8 := by
  have hD : IsOpen unitDisc := isOpen_ball
  have hsub : closedBall x (1 / 8) ⊆ unitDisc := by
    intro y hy
    rw [mem_closedBall, dist_eq_norm] at hy
    apply mem_ball_zero_iff.mpr
    calc ‖y‖ = ‖x + (y - x)‖ := by ring_nf
      _ ≤ ‖x‖ + ‖y - x‖ := norm_add_le _ _
      _ < 1 := by linarith
  have hd : DiffContOnCl ℂ S (ball x (1 / 8)) := by
    refine DifferentiableOn.diffContOnCl ?_
    rw [closure_ball x (by norm_num)]
    exact hS.1.mono hsub
  have hb : ∀ z ∈ sphere x (1 / 8), ‖S z‖ ≤ 1 := by
    intro z hz
    have hz' : z ∈ unitDisc := hsub (sphere_subset_closedBall hz)
    have : S z ∈ unitDisc := by
      rw [← hS.2.2]
      exact mem_image_of_mem S hz'
    exact (mem_ball_zero_iff.mp this).le
  have := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (by norm_num : (0 : ℝ) < 1 / 8) hd hb
  calc ‖deriv S x‖ ≤ 1 / (1 / 8) := this
    _ = 8 := by norm_num

theorem gph_blaschke_deriv {a g : ℂ} (ha : ‖a‖ < 1) (hg : ‖g‖ ≤ 1 / 8) :
    HasDerivAt (blaschke (-a)) (deriv (blaschke (-a)) g) g ∧
      ‖deriv (blaschke (-a)) g - ((1 - ‖a‖ ^ 2 : ℝ) : ℂ)‖ ≤ 3 * ‖g‖ := by
  have hna : ‖-a‖ < 1 := by simpa using ha
  have hg1 : ‖g‖ < 1 := by linarith
  have hd := hasDerivAt_blaschke hna hg1
  refine ⟨hd.differentiableAt.hasDerivAt, ?_⟩
  rw [hd.deriv]
  set u : ℂ := conj a * g with hu
  have hun : ‖u‖ ≤ ‖g‖ := by
    rw [hu, norm_mul, Complex.norm_conj]
    nlinarith [norm_nonneg a, norm_nonneg g]
  have e1 : (1 - -a * conj (-a) : ℂ) = ((1 - ‖a‖ ^ 2 : ℝ) : ℂ) := by
    simp only [map_neg, neg_mul_neg, Complex.mul_conj']
    push_cast
    ring
  have e2 : (1 - conj (-a) * g : ℂ) = 1 + u := by
    simp only [map_neg, neg_mul, sub_neg_eq_add, hu]
  rw [e1, e2]
  have hu8 : ‖u‖ ≤ 1 / 8 := hun.trans hg
  have h1u : 7 / 8 ≤ ‖1 + u‖ := by
    have := norm_sub_le (1 + u) u
    simp only [add_sub_cancel_right, norm_one] at this
    linarith
  have hne : 1 + u ≠ 0 := by
    intro h
    rw [h, norm_zero] at h1u
    linarith
  have hc0 : (0 : ℝ) ≤ 1 - ‖a‖ ^ 2 := by nlinarith [norm_nonneg a]
  have hc1 : 1 - ‖a‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg a]
  have key : ((1 - ‖a‖ ^ 2 : ℝ) : ℂ) / (1 + u) ^ 2 - ((1 - ‖a‖ ^ 2 : ℝ) : ℂ) =
      ((1 - ‖a‖ ^ 2 : ℝ) : ℂ) * (-u * (2 + u) / (1 + u) ^ 2) := by
    field_simp
    ring
  rw [key, norm_mul, Complex.norm_real, Real.norm_of_nonneg hc0, norm_div, norm_mul, norm_neg, norm_pow]
  have h2u : ‖2 + u‖ ≤ 17 / 8 := by
    calc ‖2 + u‖ ≤ ‖(2 : ℂ)‖ + ‖u‖ := norm_add_le _ _
      _ ≤ 17 / 8 := by norm_num; linarith
  have hden : (49 / 64 : ℝ) ≤ ‖1 + u‖ ^ 2 := by nlinarith
  have hnum : ‖u‖ * ‖2 + u‖ ≤ ‖u‖ * (17 / 8) := mul_le_mul_of_nonneg_left h2u (norm_nonneg _)
  have hfrac : ‖u‖ * ‖2 + u‖ / ‖1 + u‖ ^ 2 ≤ 3 * ‖u‖ := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith [norm_nonneg u]
  calc (1 - ‖a‖ ^ 2) * (‖u‖ * ‖2 + u‖ / ‖1 + u‖ ^ 2) ≤ 1 * (3 * ‖u‖) :=
        mul_le_mul hc1 hfrac (by positivity) zero_le_one
    _ ≤ 3 * ‖g‖ := by linarith

theorem gph_S_deriv {S F G : ℕ → ℂ → ℂ} {a : ℕ → ℂ}
    (hS : ∀ n, IsConformalOnto (S n) unitDisc unitDisc) (ha : ∀ n, ‖a n‖ < 1)
    (he : ∀ n, EqOn (fun z => F n (blaschke (-a n) z)) (fun z => S n (G n z)) unitDisc)
    (hF : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ∀ z : ℂ, ‖z‖ ≤ 1 → ‖F n z - z‖ < ε)
    (hG : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ∀ z : ℂ, ‖z‖ ≤ 1 / 2 → ‖G n z - z‖ < ε) :
    Tendsto (fun n => deriv (S n) (G n 0) - ((1 - ‖a n‖ ^ 2 : ℝ) : ℂ)) atTop (𝓝 0) := by
  refine Metric.tendsto_nhds.2 (fun η hη => ?_)
  set ε : ℝ := min (1 / 8) (η / 40) with hε
  have hε0 : 0 < ε := lt_min (by norm_num) (by positivity)
  have hε8 : ε ≤ 1 / 8 := min_le_left _ _
  have hεη : ε ≤ η / 40 := min_le_right _ _
  filter_upwards [hF ε hε0, hG ε hε0] with n hFn hGn
  have hD : IsOpen unitDisc := isOpen_ball
  have hna : ‖-a n‖ < 1 := by simpa using ha n
  have hTd : DifferentiableOn ℂ (blaschke (-a n)) unitDisc := differentiableOn_blaschke hna
  have hHd : DifferentiableOn ℂ (fun z => S n z - blaschke (-a n) z) unitDisc := (hS n).1.sub hTd
  have hg : ‖G n 0‖ < ε := by simpa using hGn 0 (by norm_num)
  have hg8 : ‖G n 0‖ ≤ 1 / 8 := (hg.trans_le hε8).le
  -- sup bound for `S - T` on the ball of radius 1/2
  have hbound : ∀ w : ℂ, ‖w‖ ≤ 1 / 2 → ‖S n w - blaschke (-a n) w‖ ≤ 9 * ε := by
    intro w hw
    have hwD : w ∈ unitDisc := mem_ball_zero_iff.2 (by linarith)
    have hTw : ‖blaschke (-a n) w‖ < 1 := blaschke_mem_unitDisc hna (mem_ball_zero_iff.1 hwD)
    have h1 : ‖S n (G n w) - blaschke (-a n) w‖ < ε := by
      have := he n hwD
      simp only at this
      rw [← this]
      exact hFn _ hTw.le
    have hGw : ‖G n w - w‖ < ε := hGn w hw
    have hGw3 : ‖G n w‖ ≤ 3 / 4 := by
      have := norm_le_norm_add_norm_sub' (G n w) w
      linarith
    have hLip : ‖S n (G n w) - S n w‖ ≤ 8 * ‖G n w - w‖ :=
      Convex.norm_image_sub_le_of_norm_deriv_le (s := closedBall (0 : ℂ) (3 / 4))
        (fun x hx => (hS n).1.differentiableAt (hD.mem_nhds (mem_ball_zero_iff.2
          (lt_of_le_of_lt (mem_closedBall_zero_iff.1 hx) (by norm_num)))))
        (fun x hx => gph_deriv_bound (hS n) (mem_closedBall_zero_iff.1 hx))
        (convex_closedBall _ _) (mem_closedBall_zero_iff.2 (by linarith)) (mem_closedBall_zero_iff.2 hGw3)
    calc ‖S n w - blaschke (-a n) w‖ = ‖(S n w - S n (G n w)) + (S n (G n w) - blaschke (-a n) w)‖ := by
          ring_nf
      _ ≤ ‖S n w - S n (G n w)‖ + ‖S n (G n w) - blaschke (-a n) w‖ := norm_add_le _ _
      _ ≤ 8 * ‖G n w - w‖ + ε := by
          rw [norm_sub_rev (S n w)]
          linarith
      _ ≤ 9 * ε := by linarith
  -- Cauchy estimate for the derivative of the difference at `G n 0`
  have hcl : closedBall (G n 0) (1 / 4) ⊆ closedBall (0 : ℂ) (1 / 2) := by
    intro z hz
    rw [mem_closedBall_zero_iff]
    have := mem_closedBall_iff_norm.1 hz
    calc ‖z‖ = ‖(z - G n 0) + G n 0‖ := by ring_nf
      _ ≤ ‖z - G n 0‖ + ‖G n 0‖ := norm_add_le _ _
      _ ≤ 1 / 2 := by linarith
  have hclD : closedBall (G n 0) (1 / 4) ⊆ unitDisc := by
    intro z hz
    exact mem_ball_zero_iff.2 (lt_of_le_of_lt (mem_closedBall_zero_iff.1 (hcl hz)) (by norm_num))
  have hdc : DiffContOnCl ℂ (fun z => S n z - blaschke (-a n) z) (ball (G n 0) (1 / 4)) := by
    refine DifferentiableOn.diffContOnCl ?_
    rw [closure_ball _ (by norm_num)]
    exact hHd.mono hclD
  have hcauchy := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (by norm_num : (0 : ℝ) < 1 / 4) hdc
    (fun z hz => hbound z (mem_closedBall_zero_iff.1 (hcl (sphere_subset_closedBall hz))))
  have hg1 : G n 0 ∈ unitDisc := mem_ball_zero_iff.2 (by linarith)
  have hSd : DifferentiableAt ℂ (S n) (G n 0) := (hS n).1.differentiableAt (hD.mem_nhds hg1)
  have hTd' : DifferentiableAt ℂ (blaschke (-a n)) (G n 0) := hTd.differentiableAt (hD.mem_nhds hg1)
  have hsplit : deriv (S n) (G n 0) = deriv (fun z => S n z - blaschke (-a n) z) (G n 0) +
      deriv (blaschke (-a n)) (G n 0) := by
    have := deriv_sub hSd hTd'
    have e : (fun z => S n z - blaschke (-a n) z) = S n - blaschke (-a n) := rfl
    rw [e, this]
    ring
  obtain ⟨-, hTb⟩ := gph_blaschke_deriv (a := a n) (ha n) hg8
  rw [dist_zero_right, hsplit]
  have hfin : ‖deriv (fun z => S n z - blaschke (-a n) z) (G n 0) +
      (deriv (blaschke (-a n)) (G n 0) - ((1 - ‖a n‖ ^ 2 : ℝ) : ℂ))‖ < η := by
    calc _ ≤ ‖deriv (fun z => S n z - blaschke (-a n) z) (G n 0)‖ +
          ‖deriv (blaschke (-a n)) (G n 0) - ((1 - ‖a n‖ ^ 2 : ℝ) : ℂ)‖ := norm_add_le _ _
      _ ≤ 9 * ε / (1 / 4) + 3 * ‖G n 0‖ := add_le_add hcauchy hTb
      _ < η := by nlinarith
  convert hfin using 2
  ring

/-! ### Base-point covariance with the conformal comparison map exposed -/

/-- Copy of the body of `grp25_cov` (internal there), keeping the disc automorphism `S` with
`w_μ ∘ T_a = S ∘ w_μ'` on `𝔻`. -/
theorem gph_cov {μ : LinfStar} (hμ : μ ∈ harmonicBeltrami) (hμ1 : ‖μ‖ < 1) {a : ℂ} (ha : a ∈ unitDisc)
    (ha0 : a ≠ 0) :
    ∃ μ' ∈ harmonicBeltrami, ‖μ'‖ ≤ ‖μ‖ ∧ ∃ S : ℂ → ℂ, IsConformalOnto S unitDisc unitDisc ∧
      wA μ' 0 ∈ unitDisc ∧
      EqOn (fun z => wA μ (blaschke (-a) z)) (fun z => S (wA μ' z)) unitDisc := by
  have hna : ‖-a‖ < 1 := by simpa only [norm_neg] using mem_ball_zero_iff.mp ha
  have hna0 : -a ≠ 0 := neg_ne_zero.mpr ha0
  let μ' := toLinf (fun z => μ (blaschke (-a) z) *
    (conj (deriv (blaschke (-a)) z) / deriv (blaschke (-a)) z))
  have hdata := grp25c_exterior hna hna0
  have hTm : Measurable (blaschke (-a)) := by unfold blaschke; fun_prop
  have hnorm : ‖μ'‖ ≤ ‖μ‖ := (grp25c_pullback_memLp μ hTm hdata.2.1).2
  have hμ'h : μ' ∈ harmonicBeltrami := tv_pullback_harmonic hμ hdata.1 hdata.2.1 hdata.2.2
  have hμB : μ ∈ LinfStarBall := by simpa only [LinfStarBall, mem_ball_zero_iff] using hμ1
  have hμ'B : μ' ∈ LinfStarBall := by
    simpa only [LinfStarBall, mem_ball_zero_iff] using hnorm.trans_lt hμ1
  obtain ⟨S, hS, hG0, he⟩ := grp25c_comparison hμB hμ'B hna (grp25c_ext_pullback μ hna hna0)
  exact ⟨μ', hμ'h, hnorm, S, hS, hG0, he⟩

/-! ### The derivative of `w_ν` at points of a compact subset of `𝔻` tends to `1` -/

theorem gph_dz_seq {ν : ℕ → LinfStar} (hh : ∀ n, ν n ∈ harmonicBeltrami) (hs : ∀ n, ‖ν n‖ < 1 / 4)
    (hlim : Tendsto (fun n => ‖ν n‖) atTop (𝓝 0)) {a : ℕ → ℂ} {ρ : ℝ} (hρ : ρ < 1)
    (ha : ∀ n, ‖a n‖ ≤ ρ) (ha0 : ∀ n, a n ≠ 0) :
    (∀ n, ContDiffAt ℝ 1 (wA (ν n)) (a n)) ∧
      Tendsto (fun n => dz (wA (ν n)) (a n)) atTop (𝓝 1) := by
  have haD : ∀ n, a n ∈ unitDisc := fun n => mem_ball_zero_iff.2 ((ha n).trans_lt hρ)
  have hball : ∀ n, ν n ∈ LinfStarBall := fun n => by
    simpa [LinfStarBall] using (show ‖ν n‖ < 1 by linarith [hs n])
  have hex : ∀ n, ∃ μ' ∈ harmonicBeltrami, ‖μ'‖ ≤ ‖ν n‖ ∧ ∃ S : ℂ → ℂ,
      IsConformalOnto S unitDisc unitDisc ∧ wA μ' 0 ∈ unitDisc ∧
      EqOn (fun z => wA (ν n) (blaschke (-a n) z)) (fun z => S (wA μ' z)) unitDisc :=
    fun n => gph_cov (hh n) (by linarith [hs n]) (haD n) (ha0 n)
  choose μ' hμ'h hμ'n S hS hG0 he using hex
  have hs' : ∀ n, ‖μ' n‖ < 1 / 4 := fun n => (hμ'n n).trans_lt (hs n)
  have hlim' : Tendsto (fun n => ‖μ' n‖) atTop (𝓝 0) :=
    squeeze_zero (fun n => norm_nonneg _) hμ'n hlim
  have hdzG := gph_origin_dz hμ'h hs' hlim'
  -- closeness to the identity on the unit ball
  have hFnear : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ∀ z : ℂ, ‖z‖ ≤ 1 → ‖wA (ν n) z - z‖ < ε := by
    intro ε hε
    obtain ⟨δ, hδ, hnear⟩ := gph_near_id_all (R := 1) hε
    filter_upwards [hlim.eventually (gt_mem_nhds hδ)] with n hn z hz
    exact (hnear (ν n) (hball n) hn z hz).2
  have hGnear : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ∀ z : ℂ, ‖z‖ ≤ 1 / 2 → ‖wA (μ' n) z - z‖ < ε := by
    intro ε hε
    obtain ⟨δ, hδ, hnear⟩ := gph_near_id_all (R := 1 / 2) hε
    filter_upwards [hlim'.eventually (gt_mem_nhds hδ)] with n hn z hz
    exact (hnear (μ' n) (by simpa [LinfStarBall] using (show ‖μ' n‖ < 1 by linarith [hs' n])) hn z hz).2
  have hSd := gph_S_deriv (S := S) (F := fun n => wA (ν n)) (G := fun n => wA (μ' n)) (a := a) hS
    (fun n => (ha n).trans_lt hρ) he hFnear hGnear
  -- transport
  have hreg : ∀ n, ContDiffAt ℝ 1 (wA (μ' n)) 0 := fun n =>
    (grp25_regular_zero (hμ'h n) (by linarith [hs' n])).1
  have htr := fun n => gph_transport_dz (haD n) (hS n) (hG0 n) (he n) (hreg n)
  refine ⟨fun n => (htr n).1, ?_⟩
  set c : ℕ → ℝ := fun n => 1 - ‖a n‖ ^ 2 with hc
  have hcpos : ∀ n, 1 - ρ ^ 2 ≤ c n := by
    intro n
    have h1 : ‖a n‖ ^ 2 ≤ ρ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (ha n) 2
    simp only [hc]
    linarith
  have hρ2 : 0 < 1 - ρ ^ 2 := by
    have hρ0 : 0 ≤ ρ := (norm_nonneg _).trans (ha 0)
    nlinarith
  have hc0 : ∀ n, (c n : ℂ) ≠ 0 := fun n => by
    have := (hcpos n).trans_lt' hρ2
    exact_mod_cast this.ne'
  have hquot : Tendsto (fun n => (deriv (S n) (wA (μ' n) 0) - (c n : ℂ)) / (c n : ℂ)) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero] at hSd ⊢
    have hb := hSd.div_const (1 - ρ ^ 2)
    rw [zero_div] at hb
    refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) hb
    rw [norm_div, Complex.norm_real, Real.norm_of_nonneg (by linarith [hcpos n, hρ2])]
    exact div_le_div_of_nonneg_left (norm_nonneg _) hρ2 (hcpos n)
  have hfin : Tendsto (fun n => ((deriv (S n) (wA (μ' n) 0) - (c n : ℂ)) / (c n : ℂ) + 1) *
      dz (wA (μ' n)) 0) atTop (𝓝 ((0 + 1) * 1)) := (hquot.add_const 1).mul hdzG
  rw [zero_add, one_mul] at hfin
  refine hfin.congr (fun n => ?_)
  have h := (htr n).2
  have hcn := hc0 n
  show _ = dz (wA (ν n)) (a n)
  have : dz (wA (ν n)) (a n) = deriv (S n) (wA (μ' n) 0) * dz (wA (μ' n)) 0 / (c n : ℂ) := by
    rw [eq_div_iff hcn]
    exact h
  rw [this]
  field_simp
  ring

/-! ### Reflection to the exterior and the phase lemma -/

/-- Copy of the reflection step of `grp25_reflect` (internal there), for the complex derivative:
`dz w_μ (z) = conj (dz w_μ (1/z̄)) / (z² conj (w_μ (1/z̄))²)` for `z ∈ 𝔻*` away from the pole. -/
theorem gph_refl_dz {μ : LinfStar} (hμb : μ ∈ LinfStarBall) {z : ℂ} (hzn : 1 < ‖z‖)
    (hne : wAS μ (z : ExtPlane) ≠ extInf) (hd : DifferentiableAt ℝ (wA μ) (refl z))
    (hw : wA μ (refl z) ≠ 0) :
    DifferentiableAt ℝ (wA μ) z ∧
      dz (wA μ) z = conj (dz (wA μ) (refl z)) / (z ^ 2 * conj (wA μ (refl z)) ^ 2) := by
  have hz0 : z ≠ 0 := by
    intro h
    rw [h] at hzn
    simp at hzn
    linarith
  have hDo : IsOpen unitDiscExterior := isOpen_lt continuous_const continuous_norm
  have hz : z ∈ unitDiscExterior := hzn
  have hev : wA μ =ᶠ[nhds z] fun y => refl (wA μ (refl y)) := by
    filter_upwards [(wA_finite_domain_open hμb).mem_nhds hne, hDo.mem_nhds hz] with y hy1 hy2
    have hy2' : 1 < ‖y‖ := hy2
    have hy0 : y ≠ 0 := by
      intro h
      rw [h] at hy2'
      simp at hy2'
      linarith
    have hyfin : wAS μ (y : ExtPlane) ≠ extInf := hy1
    obtain ⟨u, hu1, hu⟩ : ∃ u : ℂ, 1 < ‖u‖ ∧ wAS μ (y : ExtPlane) = (u : ExtPlane) := by
      rcases wAS_maps_ext hμb hy2' with h | ⟨u, h1, h2⟩
      · exact absurd h hyfin
      · exact ⟨u, h1, h2⟩
    have hgy : wA μ y = u := by
      show finPart (wAS μ (y : ExtPlane)) = u
      rw [hu]
      rfl
    have hu0 : u ≠ 0 := by
      intro h
      rw [h, norm_zero] at hu1
      linarith
    have h := eq_1_2 hμb hy0 (by rw [hgy]; exact hu0)
    show wA μ y = (conj (wA μ (refl y)))⁻¹
    rw [← h, one_div, inv_inv]
  obtain ⟨hH1, hH2⟩ := grp_refl_dz hz0 hd hw
  refine ⟨hH1.congr_of_eventuallyEq hev, ?_⟩
  rw [(t203_c1_dz_congr hev).1]
  exact hH2

/-- The phase lemma (TT:2030, "`(w_ν)_z → 1`"): for harmonic `ν` of small sup norm, `w_ν` is differentiable with
`dz ≠ 0` on the annulus and `conj(dz w_ν)/dz w_ν → 1` uniformly there. -/
theorem gph_phase {r R ε : ℝ} (hr : 1 < r) (hε : 0 < ε) :
    ∃ δ > 0, ∀ ν ∈ harmonicBeltrami, ‖ν‖ < δ → ∀ z : ℂ, r ≤ ‖z‖ → ‖z‖ ≤ R →
      DifferentiableAt ℝ (wA ν) z ∧ dz (wA ν) z ≠ 0 ∧ ‖conj (dz (wA ν) z) / dz (wA ν) z - 1‖ < ε := by
  by_contra hcon
  push_neg at hcon
  choose ν hνh hνlt z hzr hzR hbad using fun n : ℕ =>
    hcon (min (1 / 5) (1 / ((n : ℝ) + 1))) (lt_min (by norm_num) (by positivity))
  have hs : ∀ n, ‖ν n‖ < 1 / 4 := fun n =>
    lt_of_lt_of_le ((hνlt n).trans_le (min_le_left _ _)) (by norm_num)
  have hlim : Tendsto (fun n => ‖ν n‖) atTop (𝓝 0) :=
    squeeze_zero (fun n => norm_nonneg _) (fun n => ((hνlt n).trans_le (min_le_right _ _)).le)
      tendsto_one_div_add_atTop_nhds_zero_nat
  have hball : ∀ n, ν n ∈ LinfStarBall := fun n => by
    simpa [LinfStarBall] using (show ‖ν n‖ < 1 by linarith [hs n])
  have hR0 : 0 < R := lt_of_lt_of_le (by linarith) ((hzr 0).trans (hzR 0))
  have hz1 : ∀ n, 1 < ‖z n‖ := fun n => lt_of_lt_of_le hr (hzr n)
  have hz0 : ∀ n, z n ≠ 0 := fun n h => by
    have := hz1 n
    rw [h, norm_zero] at this
    linarith
  set a : ℕ → ℂ := fun n => refl (z n) with hadef
  have hnorm_a : ∀ n, ‖a n‖ = (‖z n‖)⁻¹ := fun n => by
    show ‖(conj (z n))⁻¹‖ = _
    rw [norm_inv, Complex.norm_conj]
  have ha_le : ∀ n, ‖a n‖ ≤ 1 / r := fun n => by
    rw [hnorm_a, one_div]
    exact inv_anti₀ (by linarith) (hzr n)
  have ha_ge : ∀ n, 1 / R ≤ ‖a n‖ := fun n => by
    rw [hnorm_a, one_div]
    exact inv_anti₀ (by have := hz1 n; linarith) (hzR n)
  have hρ : 1 / r < 1 := by rw [div_lt_one (by linarith)]; exact hr
  have ha0 : ∀ n, a n ≠ 0 := fun n h => by
    have := ha_ge n
    rw [h, norm_zero] at this
    have : 0 < 1 / R := by positivity
    linarith
  obtain ⟨hreg, hP⟩ := gph_dz_seq hνh hs hlim hρ ha_le ha0
  -- the values `w_n = w_{ν_n}(a_n)` are close to `a_n`, relatively
  have hrat : Tendsto (fun n => wA (ν n) (a n) / a n) atTop (𝓝 1) := by
    rw [Metric.tendsto_nhds]
    intro η hη
    obtain ⟨δ, hδ, hnear⟩ := gph_near_id_all (R := 1) (ε := η / R) (by positivity)
    filter_upwards [hlim.eventually (gt_mem_nhds hδ)] with n hn
    have hwa : ‖wA (ν n) (a n) - a n‖ < η / R :=
      (hnear (ν n) (hball n) hn (a n) ((ha_le n).trans ((div_le_one (by linarith)).2 hr.le))).2
    have han := ha_ge n
    have hapos : 0 < ‖a n‖ := lt_of_lt_of_le (by positivity) han
    rw [dist_eq_norm]
    have e : wA (ν n) (a n) / a n - 1 = (wA (ν n) (a n) - a n) / a n := by
      field_simp [ha0 n]
    rw [e, norm_div, div_lt_iff₀ hapos]
    calc ‖wA (ν n) (a n) - a n‖ < η / R := hwa
      _ = η * (1 / R) := by ring
      _ ≤ η * ‖a n‖ := mul_le_mul_of_nonneg_left han hη.le
  -- finiteness at `z_n`, eventually
  have hfin : ∀ᶠ n in atTop, wAS (ν n) (z n : ExtPlane) ≠ extInf := by
    obtain ⟨δ, hδ, hnear⟩ := gph_near_id_all (R := R) (ε := 1) one_pos
    filter_upwards [hlim.eventually (gt_mem_nhds hδ)] with n hn
    exact (hnear (ν n) (hball n) hn (z n) (hzR n)).1
  have hw0 : ∀ᶠ n in atTop, wA (ν n) (a n) ≠ 0 := by
    filter_upwards [hrat.eventually_ne (by norm_num : (1 : ℂ) ≠ 0)] with n hn h
    apply hn
    rw [h, zero_div]
  have hP0 : ∀ᶠ n in atTop, dz (wA (ν n)) (a n) ≠ 0 :=
    hP.eventually_ne (by norm_num)
  -- the formula for `dz w_{ν_n}` at `z_n`
  have hform : ∀ᶠ n in atTop, DifferentiableAt ℝ (wA (ν n)) (z n) ∧
      dz (wA (ν n)) (z n) = conj (dz (wA (ν n)) (a n)) / (z n ^ 2 * conj (wA (ν n) (a n)) ^ 2) := by
    filter_upwards [hfin, hw0] with n hn1 hn2
    exact gph_refl_dz (hball n) (hz1 n) hn1 ((hreg n).differentiableAt (by norm_num)) hn2
  -- the phase
  have hconjrat : Tendsto (fun n => conj (wA (ν n) (a n) / a n)) atTop (𝓝 1) := by
    have := (Complex.continuous_conj.tendsto 1).comp hrat
    simpa [Function.comp_def] using this
  have hPP : Tendsto (fun n => dz (wA (ν n)) (a n) / conj (dz (wA (ν n)) (a n))) atTop (𝓝 1) := by
    have hcP : Tendsto (fun n => conj (dz (wA (ν n)) (a n))) atTop (𝓝 1) := by
      simpa [Function.comp_def] using (Complex.continuous_conj.tendsto 1).comp hP
    have h := hP.div hcP one_ne_zero
    rw [div_one] at h
    exact h
  have htau : Tendsto (fun n => dz (wA (ν n)) (a n) / conj (dz (wA (ν n)) (a n)) *
      (conj (wA (ν n) (a n) / a n) / (wA (ν n) (a n) / a n)) ^ 2) atTop (𝓝 1) := by
    have h1 := (hconjrat.div hrat (by norm_num)).pow 2
    have := hPP.mul h1
    simpa using this
  have hz2 : ∀ n, z n = (conj (a n))⁻¹ := fun n => by
    show z n = (conj (refl (z n)))⁻¹
    show z n = (conj ((conj (z n))⁻¹))⁻¹
    simp
  have hident : ∀ᶠ n in atTop, conj (dz (wA (ν n)) (z n)) / dz (wA (ν n)) (z n) =
      dz (wA (ν n)) (a n) / conj (dz (wA (ν n)) (a n)) *
        (conj (wA (ν n) (a n) / a n) / (wA (ν n) (a n) / a n)) ^ 2 := by
    filter_upwards [hform, hw0, hP0] with n hn hw hP'
    rw [hn.2]
    have han := ha0 n
    have hza : z n = (conj (a n))⁻¹ := hz2 n
    have hcan : conj (a n) ≠ 0 := (map_ne_zero _).2 han
    have hcw : conj (wA (ν n) (a n)) ≠ 0 := (map_ne_zero _).2 hw
    have hcP : conj (dz (wA (ν n)) (a n)) ≠ 0 := (map_ne_zero _).2 hP'
    rw [hza]
    simp only [map_div₀, map_mul, map_pow, map_inv₀, Complex.conj_conj]
    field_simp
  have hlimtau : Tendsto (fun n => conj (dz (wA (ν n)) (z n)) / dz (wA (ν n)) (z n)) atTop (𝓝 1) :=
    htau.congr' (hident.mono fun n hn => hn.symm)
  have hnz : ∀ᶠ n in atTop, dz (wA (ν n)) (z n) ≠ 0 := by
    filter_upwards [hform, hw0, hP0] with n hn hw hP'
    rw [hn.2]
    have hcw : conj (wA (ν n) (a n)) ≠ 0 := (map_ne_zero _).2 hw
    have hcP : conj (dz (wA (ν n)) (a n)) ≠ 0 := (map_ne_zero _).2 hP'
    exact div_ne_zero hcP (mul_ne_zero (pow_ne_zero 2 (hz0 n)) (pow_ne_zero 2 hcw))
  have hsmall : ∀ᶠ n in atTop, ‖conj (dz (wA (ν n)) (z n)) / dz (wA (ν n)) (z n) - 1‖ < ε := by
    have h0 : Tendsto (fun n => conj (dz (wA (ν n)) (z n)) / dz (wA (ν n)) (z n) - 1) atTop (𝓝 0) := by
      simpa using hlimtau.sub_const 1
    exact (tendsto_zero_iff_norm_tendsto_zero.1 h0).eventually (gt_mem_nhds hε)
  obtain ⟨n, hn1, hn2, hn3⟩ := (hform.and (hnz.and hsmall)).exists
  exact absurd (hbad n hn1.1 hn2) (not_le.2 hn3)

end TakhtajanTeo
