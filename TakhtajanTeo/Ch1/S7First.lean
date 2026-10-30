import TakhtajanTeo.Ch1.S7_Curvature
import TakhtajanTeo.Ch1.S6Eq64

/-!
# Chapter 1, §7.1 — (7.1), (7.2), (7.3), (7.5) (`s71_`, 下属1 + 下属2 + 下属6)

`s71_eq_7_1`, `s71_eq_7_2`, `s71_eq_7_3`, `s71_eq_7_5` are byte-identical copies of `eq_7_1`, `eq_7_2`, `eq_7_3`
(as corrected 2026-10-28), `eq_7_5` (S7; relocated by the leader). Owners: `[W1]` 下属1, `[W2]` 下属2, `[W6]` 下属6.

**Route.** `Q(μ, εν)(z) = (12/π) J(ε)/ρ^{εν}(z)` with `J(ε) = ∬_𝕌 μ(u) K_{εν}(u, z̄)² d²u` (7.1). Both derivatives of
`ρ^{εν}(z)` vanish at `0` (`lemma_6_1`), so `∂Q(0) = (12/π) ∂J(0)/ρ(z)` (B3). The `u`-integrand of `J` is not singular
(`z̄ ∈ 𝕃`), so `∂` passes under `∫_u` by the E64 holomorphic extension and torus Cauchy (B2), and the pointwise
derivatives come from (1.25) at `ε = 0` (B4): an inner principal value in `v`, at `v = u` for `∂_ε` and at `v = z`
for `∂_ε̄`. (7.2) then needs the bridge to the symmetric cut-off `|u - v| ≥ δ` (C1–C3); (7.3) the swap to the outer
principal value at `v = z` (D1); (7.5) the regularization (D2). (7.2) is proved without (7.4): it is literally
`∂_ε Q(0) = c · lim`, whatever the value of the limit.

No four-term splitting of a Bochner integral is used for (7.2) (each term alone is not integrable for bounded
harmonic data; 下属6, EQ74 triage).
-/

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal ComplexConjugate Classical Real
noncomputable section
namespace TakhtajanTeo
open LiZhongQC

/-! ### (7.1) `[W6]` -/

/-! ### (7.1) helpers `[W6]` -/

/-- The A∞ Beltrami representative, extended by zero off `𝕌`, is a bounded coefficient on `ℂ`. -/
theorem s71_indicator_coeff {μ φ : ℂ → ℂ} (hμ : IsHarmonicU μ φ) :
    ∃ C : ℝ, 0 ≤ C ∧ IsBeltramiCoeff (upperHalf.indicator μ) univ C := by
  obtain ⟨C, hC0, hC⟩ := harmonicU_bounded hμ
  have hU : MeasurableSet upperHalf := measurableSet_lt measurable_const Complex.measurable_im
  refine ⟨C, hC0, vf_zero_extension_coeff hC0 ⟨?_, ?_⟩⟩
  · exact (harmonicU_continuousOn hμ).aestronglyMeasurable hU
  · exact (ae_restrict_iff' hU).2 (Eventually.of_forall hC)

/-- The change of variables `η = w(u)`, `w = w_{εν}`, in the integral of `P` (1.23) applied to `R(μ, εν)` (1.6):
`∬_𝕌 R(μ, εν)(η)/(η - c)⁴ d²η = ∬_𝕌 μ(u) (w_u)²/(w(u) - c)⁴ d²u` (TT:2703). -/
theorem s71_cov {μ φ ν : ℂ → ℂ} (hμ : IsHarmonicU μ φ) {k : ℝ} (hk : 0 ≤ k)
    (hνk : IsBeltramiCoeff ν upperHalf k) (hνs : ContDiffOn ℝ (⊤ : ℕ∞) ν upperHalf) {ε : ℂ}
    (hε : ‖ε‖ * k < 1) (c : ℂ) :
    (∫ η in upperHalf, RnmFunU μ (fun y => ε * ν y) η / (η - c) ^ 4) =
      ∫ u in upperHalf, μ u * (1 / (wU (fun y => ε * ν y) u - c) ^ 4) * dz (wU (fun y => ε * ν y)) u ^ 2 := by
  have hU : MeasurableSet upperHalf := measurableSet_lt measurable_const Complex.measurable_im
  obtain ⟨hns, -, -, -⟩ := e124c_setup hk hνk hνs hε rfl
  obtain ⟨C, hC0, hh⟩ := s71_indicator_coeff hμ
  have hKm : Measurable (fun η : ℂ => 1 / (η - c) ^ 4) := by fun_prop
  have hcov := e124c_cov (by positivity) hε (e124c_extU_beltrami hk hνk ε) hns hh hKm
  have hνε : IsBeltramiCoeff (fun y => ε * ν y) upperHalf (‖ε‖ * k) :=
    ⟨hνk.1.const_mul ε, hνk.2.mono fun z hz => by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left hz (norm_nonneg _)⟩
  have himg : wU (fun y => ε * ν y) '' upperHalf = upperHalf := by
    rw [e124_wU_eq_fMuSym hk hνk hε]
    exact (fMuSym_upperHalf (by positivity) hε hνε).1
  obtain ⟨⟨K₀, hK⟩, himgU, -, -, -⟩ := hns
  have hinj : InjOn (wU (fun y => ε * ν y)) univ := hK.2.2.1.2.1
  have hsurj : ∀ η, wU (fun y => ε * ν y) (Function.invFunOn (wU (fun y => ε * ν y)) univ η) = η := by
    intro η
    have hex : ∃ x ∈ (univ : Set ℂ), wU (fun y => ε * ν y) x = η := by
      have : η ∈ wU (fun y => ε * ν y) '' univ := by rw [himgU]; exact mem_univ η
      obtain ⟨x, -, hx⟩ := this
      exact ⟨x, mem_univ x, hx⟩
    exact Function.invFunOn_eq hex
  have hpt : ∀ η, upperHalf.indicator (fun η => RnmFunU μ (fun y => ε * ν y) η / (η - c) ^ 4) η =
      ahT_dot (upperHalf.indicator μ) (extU fun y => ε * ν y) (wU fun y => ε * ν y) η * (1 / (η - c) ^ 4) := by
    intro η
    have hfx := hsurj η
    by_cases hη : η ∈ upperHalf
    · rw [indicator_of_mem hη]
      have hx : Function.invFunOn (wU (fun y => ε * ν y)) univ η ∈ upperHalf := by
        rw [← himg] at hη
        obtain ⟨y, hy, hyη⟩ := hη
        have he : Function.invFunOn (wU (fun y => ε * ν y)) univ η = y :=
          hinj (mem_univ _) (mem_univ _) (by rw [hfx, hyη])
        rw [he]
        exact hy
      have hinv : Function.invFun (wU (fun y => ε * ν y)) η =
          Function.invFunOn (wU (fun y => ε * ν y)) univ η :=
        hinj (mem_univ _) (mem_univ _) (by rw [hfx]; exact Function.invFun_eq ⟨_, hfx⟩)
      have hxi : 0 < (Function.invFunOn (wU (fun y => ε * ν y)) univ η).im := hx
      unfold RnmFunU ahT_dot
      rw [hinv, indicator_of_mem hx]
      simp only [extU, hxi, ↓reduceIte, Complex.conj_mul']
      ring
    · rw [indicator_of_notMem hη]
      have hx : Function.invFunOn (wU (fun y => ε * ν y)) univ η ∉ upperHalf := by
        intro hx
        apply hη
        rw [← hfx, ← himg]
        exact mem_image_of_mem _ hx
      unfold ahT_dot
      rw [indicator_of_notMem hx, zero_div, zero_mul, zero_mul]
  rw [← integral_indicator hU]
  simp only [hpt]
  rw [hcov, ← integral_indicator hU]
  congr 1
  funext u
  by_cases hu : u ∈ upperHalf
  · rw [indicator_of_mem hu, indicator_of_mem hu]
  · rw [indicator_of_notMem hu, indicator_of_notMem hu, zero_mul, zero_mul]

/-- **(7.1)** (TT:2703). In the model `𝕌`, for `μ, ν ∈ Ω^{-1,1}(𝕌)` and small `ε`:
`ρ^{εν}(z) Q(μ, εν)(z) = (12/π) ∬_𝕌 μ(u) K_{εν}(u, z̄)² d²u`. -/
theorem s71_eq_7_1 {μ ν φ ψ : ℂ → ℂ} (hμ : IsHarmonicU μ φ) (hν : IsHarmonicU ν ψ) {k : ℝ} (hk : 0 ≤ k)
    (hνk : IsBeltramiCoeff ν upperHalf k) {ε : ℂ} (hε : ‖ε‖ * k < 1) {z : ℂ} (hz : z ∈ upperHalf) :
    rhoVar ν ε z * QfunU μ (fun u => ε * ν u) z =
      (12 / π) * ∫ u in upperHalf, μ u * kernelKbar (fun y => ε * ν y) u z ^ 2 := by
  have hνs : ContDiffOn ℝ (⊤ : ℕ∞) ν upperHalf := wr_isHarmonicU_contDiffOn hν
  obtain ⟨-, -, hJ, -⟩ := e124c_setup hk hνk hνs hε rfl
  have hd : dz (wU fun y => ε * ν y) z ≠ 0 := by
    intro h0
    have h1 := hJ z hz
    unfold jacobian at h1
    rw [h0, norm_zero] at h1
    nlinarith [sq_nonneg ‖dzbar (wU fun y => ε * ν y) z‖]
  have hζ := e124_ne_conj hk hνk hε hz hz
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hcov := s71_cov hμ hk hνk hνs hε (conj (wU (fun y => ε * ν y) z))
  have hR : (∫ u in upperHalf, μ u * kernelKbar (fun y => ε * ν y) u z ^ 2) =
      conj (dz (wU fun y => ε * ν y) z) ^ 2 * ∫ u in upperHalf, μ u *
        (1 / (wU (fun y => ε * ν y) u - conj (wU (fun y => ε * ν y) z)) ^ 4) * dz (wU (fun y => ε * ν y)) u ^ 2 := by
    rw [← integral_const_mul]
    congr 1
    funext u
    unfold kernelKbar
    set e := wU (fun y => ε * ν y) u - conj (wU (fun y => ε * ν y) z)
    clear_value e
    ring
  rw [hR, ← hcov]
  unfold rhoVar QfunU harmonicProjU
  have hn : ((‖dz (wU fun y => ε * ν y) z‖ ^ 2 : ℝ) : ℂ) =
      dz (wU fun y => ε * ν y) z * conj (dz (wU fun y => ε * ν y) z) := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  rw [hn]
  field_simp
  ring

/-! ### Small facts at `ε = 0` -/

/-! ### Helpers (下属1) -/

/-- Product rule for the antiholomorphic Wirtinger derivative. -/
theorem s71_dzbar_mul {u v : ℂ → ℂ} {z : ℂ} (hu : DifferentiableAt ℝ u z) (hv : DifferentiableAt ℝ v z) :
    dzbar (fun w => u w * v w) z = u z * dzbar v z + v z * dzbar u z := by
  simp only [dzbar, fderiv_fun_mul hu hv, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.coe_smul', Pi.smul_apply, smul_eq_mul]
  ring

/-- `ρ^{εν}(z)` is real. -/
theorem s71_rho_real (ν : ℂ → ℂ) (ε z : ℂ) : conj (rhoVar ν ε z) = rhoVar ν ε z := by
  unfold rhoVar
  simp only [map_div₀, map_mul, map_neg, map_pow, map_sub, Complex.conj_conj, Complex.conj_ofReal, map_ofNat]
  ring

/-- The harmonic `ν` as a Beltrami coefficient on `𝕌`, with its smoothness. -/
theorem s71_harm_setup {ν ψ : ℂ → ℂ} (hν : IsHarmonicU ν ψ) :
    ∃ M : ℝ, 0 ≤ M ∧ IsBeltramiCoeff ν upperHalf M ∧ ContDiffOn ℝ (⊤ : ℕ∞) ν upperHalf := by
  obtain ⟨M, hM0, hM⟩ := harmonicU_bounded hν
  have hU := measurableSet_upperHalf_aux
  have hm : AEStronglyMeasurable ν (volume.restrict upperHalf) :=
    (harmonicU_continuousOn hν).aestronglyMeasurable hU
  exact ⟨M, hM0, ⟨hm, (ae_restrict_mem hU).mono fun u hu => hM u hu⟩, wr_isHarmonicU_contDiffOn hν⟩

/-- **(A1)** `[W1]` `ρ^{0}(z) = -4/(z - z̄)²` (`w_0 = id`, `rhoVar_wU_zero`, `rhoVar_dz_id`). -/
theorem s71_rho0 (ν : ℂ → ℂ) (z : ℂ) : rhoVar ν 0 z = -4 / (z - conj z) ^ 2 := by
  unfold rhoVar
  rw [e64_t9_w0]
  simp only [rhoVar_dz_id, id, norm_one, one_pow, Complex.ofReal_one, mul_one]

/-! ### The `J`-block: `J(ε) = ∬_𝕌 μ(u) K_{εν}(u, z̄)² d²u` -/

/-- **(B1)** `[W2]` Real differentiability at `ε = 0` of `ε ↦ K_{εν}(u, w̄)` for `u, w ∈ 𝕌`. Route: the holomorphic
two-parameter extension of E64 (`W_P`, `e64_W_basic`, `e64_dzW_cont`, `e64_dzW_holo`): on the diagonal
`P = (ε, ε̄)` the kernel is `dzW_P(u) dzW_P(w̄)/(W_P(u) - W_P(w̄))²` (symmetry `w_ε(ȳ) = \overline{w_ε(y)}`, as in
`e64_phi_diag`), jointly `C¹` in `P` near `0`, composed with the real-linear `ε ↦ (ε, ε̄)`. With `u = w = z` this gives
the differentiability of `ρ^{εν}(z) = -4 K_{εν}(z, z̄)` (`eq_6_1`). -/
theorem s71_K_diffAt {ν ψ : ℂ → ℂ} (hν : IsHarmonicU ν ψ) {u w : ℂ} (hu : u ∈ upperHalf) (hw : w ∈ upperHalf) :
    DifferentiableAt ℝ (fun e => kernelKbar (fun y => e * ν y) u w) 0 := by
  obtain ⟨M, hM0, hM⟩ := harmonicU_bounded hν
  have hU := measurableSet_upperHalf_aux
  have hm : AEStronglyMeasurable ν (volume.restrict upperHalf) :=
    (harmonicU_continuousOn hν).aestronglyMeasurable hU
  have hνb : IsBeltramiCoeff ν upperHalf M := ⟨hm, (ae_restrict_mem hU).mono fun u hu => hM u hu⟩
  have hνs := wr_isHarmonicU_contDiffOn hν
  have hε0 : ‖(0 : ℂ)‖ * M < 1 := by simp
  have hw0 := e64_t9_w0 ν
  have huw : u - conj w ≠ 0 := by
    have hu' : 0 < u.im := hu
    have hw' : 0 < w.im := hw
    intro h
    have := congrArg Complex.im h
    simp only [Complex.sub_im, Complex.conj_im, Complex.zero_im] at this
    linarith
  obtain ⟨hwu, hdu⟩ := e124_E2_diff hM0 hνb hνs hε0 hu
  obtain ⟨hww, hdw⟩ := e124_E2_diff hM0 hνb hνs hε0 hw
  have hdw' : DifferentiableAt ℝ (fun e => conj (dz (wU fun y => e * ν y) w)) 0 :=
    Complex.conjCLE.differentiableAt.comp 0 hdw
  have hww' : DifferentiableAt ℝ (fun e => conj (wU (fun x => e * ν x) w)) 0 :=
    Complex.conjCLE.differentiableAt.comp 0 hww
  unfold kernelKbar
  have hn : DifferentiableAt ℝ (fun e => dz (wU fun y => e * ν y) u * conj (dz (wU fun y => e * ν y) w)) 0 :=
    hdu.mul hdw'
  have hd : DifferentiableAt ℝ (fun e => (wU (fun y => e * ν y) u - conj (wU (fun y => e * ν y) w)) ^ 2) 0 :=
    (hwu.sub hww').pow 2
  refine (hn.mul (hd.inv ?_)).congr_of_eventuallyEq (Eventually.of_forall fun e => div_eq_mul_inv _ _)
  simp only [hw0, id]
  exact pow_ne_zero 2 huw

/-! ### Shared 2D kernel estimates (下属2) -/

/-- (T2) `|u − v̄|⁻² ≤ (Im v)^(−1/2) |u − v̄|^(−3/2)` for `Im u ≥ 0 < Im v`. -/
theorem s71_t_im {u v : ℂ} (hu : 0 ≤ u.im) (hv : 0 < v.im) :
    1 / ‖u - conj v‖ ^ 2 ≤ v.im ^ (-(1 / 2 : ℝ)) * ‖u - conj v‖ ^ (-(3 / 2 : ℝ)) := by
  set d := ‖u - conj v‖ with hd
  have hdv : v.im ≤ d := by
    have h1 := Complex.abs_im_le_norm (u - conj v)
    have h2 : (u - conj v).im = u.im + v.im := by simp
    rw [h2, abs_of_pos (by linarith)] at h1
    linarith
  have hd0 : 0 < d := hv.trans_le hdv
  have e : 1 / d ^ 2 = d ^ (-(1 / 2 : ℝ)) * d ^ (-(3 / 2 : ℝ)) := by
    rw [← Real.rpow_add hd0, show (-(1 / 2 : ℝ)) + -(3 / 2) = -((2 : ℕ) : ℝ) by norm_num, Real.rpow_neg hd0.le,
      Real.rpow_natCast, one_div]
  rw [e]
  exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_nonpos hv hdv (by norm_num)) (Real.rpow_nonneg hd0.le _)

/-- Pointwise inequality behind (T1): with `x = 1 + |w|`, `y = |w − b|`, `B = 1 + |b| ≤ x (1 + y)`. -/
theorem s71_t_pt {x y B : ℝ} (hx : 1 ≤ x) (hy : 0 < y) (hB : 0 ≤ B) (hBxy : B ≤ x * (1 + y)) :
    B ^ (1 / 2 : ℝ) * ((x ^ 2)⁻¹ * y ^ (-(3 / 2 : ℝ))) ≤
      (2 : ℝ) ^ (1 / 2 : ℝ) * ((if y < 1 then y ^ (-(3 / 2 : ℝ)) else 0) + x ^ (-(5 / 2 : ℝ)) +
        (2 : ℝ) ^ (5 / 2 : ℝ) * (1 + y) ^ (-(5 / 2 : ℝ))) := by
  have hx0 : 0 < x := by linarith
  have hy1 : 0 < 1 + y := by linarith
  have hs2 : 0 ≤ (2 : ℝ) ^ (1 / 2 : ℝ) := Real.rpow_nonneg (by norm_num) _
  have hB' : B ^ (1 / 2 : ℝ) ≤ x ^ (1 / 2 : ℝ) * (1 + y) ^ (1 / 2 : ℝ) :=
    (Real.rpow_le_rpow hB hBxy (by norm_num)).trans_eq (Real.mul_rpow hx0.le hy1.le)
  have hx2 : (x ^ 2)⁻¹ = x ^ (-(2 : ℝ)) := by
    rw [Real.rpow_neg hx0.le, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  set a := x ^ (-(3 / 2 : ℝ)) with ha
  have hxa : x ^ (1 / 2 : ℝ) * x ^ (-(2 : ℝ)) = a := by
    rw [← Real.rpow_add hx0]; norm_num [ha]
  have hstep : B ^ (1 / 2 : ℝ) * ((x ^ 2)⁻¹ * y ^ (-(3 / 2 : ℝ))) ≤ a * (1 + y) ^ (1 / 2 : ℝ) * y ^ (-(3 / 2 : ℝ)) := by
    rw [hx2]
    calc B ^ (1 / 2 : ℝ) * (x ^ (-(2 : ℝ)) * y ^ (-(3 / 2 : ℝ)))
        ≤ x ^ (1 / 2 : ℝ) * (1 + y) ^ (1 / 2 : ℝ) * (x ^ (-(2 : ℝ)) * y ^ (-(3 / 2 : ℝ))) :=
          mul_le_mul_of_nonneg_right hB' (by positivity)
      _ = (x ^ (1 / 2 : ℝ) * x ^ (-(2 : ℝ))) * (1 + y) ^ (1 / 2 : ℝ) * y ^ (-(3 / 2 : ℝ)) := by ring
      _ = a * (1 + y) ^ (1 / 2 : ℝ) * y ^ (-(3 / 2 : ℝ)) := by rw [hxa]
  refine hstep.trans ?_
  have ha0 : 0 ≤ a := Real.rpow_nonneg hx0.le _
  have hy32 : 0 ≤ y ^ (-(3 / 2 : ℝ)) := Real.rpow_nonneg hy.le _
  have hx52 : 0 ≤ x ^ (-(5 / 2 : ℝ)) := Real.rpow_nonneg hx0.le _
  have hk52 : 0 ≤ (2 : ℝ) ^ (5 / 2 : ℝ) * (1 + y) ^ (-(5 / 2 : ℝ)) :=
    mul_nonneg (Real.rpow_nonneg (by norm_num) _) (Real.rpow_nonneg hy1.le _)
  by_cases hy1' : y < 1
  · rw [if_pos hy1']
    have h1 : (1 + y) ^ (1 / 2 : ℝ) ≤ (2 : ℝ) ^ (1 / 2 : ℝ) := Real.rpow_le_rpow hy1.le (by linarith) (by norm_num)
    have h2 : a ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hx (by norm_num)
    calc a * (1 + y) ^ (1 / 2 : ℝ) * y ^ (-(3 / 2 : ℝ)) ≤ 1 * (2 : ℝ) ^ (1 / 2 : ℝ) * y ^ (-(3 / 2 : ℝ)) :=
          mul_le_mul_of_nonneg_right (mul_le_mul h2 h1 (Real.rpow_nonneg hy1.le _) zero_le_one) hy32
      _ ≤ _ := by nlinarith
  · rw [if_neg hy1']
    push Not at hy1'
    have h1 : (1 + y) ^ (1 / 2 : ℝ) ≤ (2 : ℝ) ^ (1 / 2 : ℝ) * y ^ (1 / 2 : ℝ) :=
      (Real.rpow_le_rpow hy1.le (by linarith : 1 + y ≤ 2 * y) (by norm_num)).trans_eq
        (Real.mul_rpow (by norm_num) hy.le)
    have hyy : y ^ (1 / 2 : ℝ) * y ^ (-(3 / 2 : ℝ)) = y ^ (-(1 : ℝ)) := by
      rw [← Real.rpow_add hy]; norm_num
    have hmain : a * y ^ (-(1 : ℝ)) ≤ x ^ (-(5 / 2 : ℝ)) + (2 : ℝ) ^ (5 / 2 : ℝ) * (1 + y) ^ (-(5 / 2 : ℝ)) := by
      by_cases hxy : x ≤ y
      · have h3 : y ^ (-(1 : ℝ)) ≤ x ^ (-(1 : ℝ)) := Real.rpow_le_rpow_of_nonpos hx0 hxy (by norm_num)
        have h4 : a * x ^ (-(1 : ℝ)) = x ^ (-(5 / 2 : ℝ)) := by
          rw [ha, ← Real.rpow_add hx0]; norm_num
        nlinarith [mul_le_mul_of_nonneg_left h3 ha0]
      · push Not at hxy
        have h3 : a ≤ y ^ (-(3 / 2 : ℝ)) := Real.rpow_le_rpow_of_nonpos hy hxy.le (by norm_num)
        have h4 : y ^ (-(3 / 2 : ℝ)) * y ^ (-(1 : ℝ)) = y ^ (-(5 / 2 : ℝ)) := by
          rw [← Real.rpow_add hy]; norm_num
        have h5 : y ^ (-(5 / 2 : ℝ)) ≤ (2 : ℝ) ^ (5 / 2 : ℝ) * (1 + y) ^ (-(5 / 2 : ℝ)) := by
          have h6 : (1 + y) ^ (5 / 2 : ℝ) ≤ (2 : ℝ) ^ (5 / 2 : ℝ) * y ^ (5 / 2 : ℝ) :=
            (Real.rpow_le_rpow hy1.le (by linarith : 1 + y ≤ 2 * y) (by norm_num)).trans_eq
              (Real.mul_rpow (by norm_num) hy.le)
          have hp1 : 0 < (1 + y) ^ (5 / 2 : ℝ) := Real.rpow_pos_of_pos hy1 _
          have hp2 : 0 < y ^ (5 / 2 : ℝ) := Real.rpow_pos_of_pos hy _
          rw [Real.rpow_neg hy.le, Real.rpow_neg hy1.le, ← div_eq_mul_inv, inv_le_iff_one_le_mul₀ hp2,
            mul_comm, ← mul_div_assoc, le_div_iff₀ hp1, one_mul, mul_comm]
          exact h6
        have hy1n : 0 ≤ y ^ (-(1 : ℝ)) := Real.rpow_nonneg hy.le _
        calc a * y ^ (-(1 : ℝ)) ≤ y ^ (-(3 / 2 : ℝ)) * y ^ (-(1 : ℝ)) := mul_le_mul_of_nonneg_right h3 hy1n
          _ = y ^ (-(5 / 2 : ℝ)) := h4
          _ ≤ _ := by linarith
    calc a * (1 + y) ^ (1 / 2 : ℝ) * y ^ (-(3 / 2 : ℝ))
        ≤ a * ((2 : ℝ) ^ (1 / 2 : ℝ) * y ^ (1 / 2 : ℝ)) * y ^ (-(3 / 2 : ℝ)) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 ha0) hy32
      _ = (2 : ℝ) ^ (1 / 2 : ℝ) * (a * (y ^ (1 / 2 : ℝ) * y ^ (-(3 / 2 : ℝ)))) := by ring
      _ = (2 : ℝ) ^ (1 / 2 : ℝ) * (a * y ^ (-(1 : ℝ))) := by rw [hyy]
      _ ≤ (2 : ℝ) ^ (1 / 2 : ℝ) * (0 + x ^ (-(5 / 2 : ℝ)) + (2 : ℝ) ^ (5 / 2 : ℝ) * (1 + y) ^ (-(5 / 2 : ℝ))) := by
          rw [zero_add]; exact mul_le_mul_of_nonneg_left hmain hs2

/-- (T1) `∫_ℂ (1+|w|)⁻² |w−b|^(−3/2) ≲ (1+|b|)^(−1/2)`, uniformly in `b`. -/
theorem s71_t_conv : ∃ C : ℝ, 0 ≤ C ∧ ∀ b : ℂ,
    Integrable (fun w : ℂ => ((1 + ‖w‖) ^ 2)⁻¹ * ‖w - b‖ ^ (-(3 / 2 : ℝ))) ∧
      ∫ w : ℂ, ((1 + ‖w‖) ^ 2)⁻¹ * ‖w - b‖ ^ (-(3 / 2 : ℝ)) ≤ C * (1 + ‖b‖) ^ (-(1 / 2 : ℝ)) := by
  have hfin : (Module.finrank ℝ ℂ : ℝ) = 2 := by rw [Complex.finrank_real_complex]; norm_num
  have hA0 : IntegrableOn (fun x : ℂ => ‖x‖ ^ (-(3 / 2 : ℝ))) (ball 0 1) := by
    refine integrableOn_ball_of_norm_le_rpow (μ := volume) (C := 1) (α := 3 / 2)
      (by rw [Complex.finrank_real_complex]; norm_num) (by rw [hfin]; norm_num)
      (Eventually.of_forall fun x => ?_) ?_
    · rw [Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _), one_mul]
    · exact (measurable_norm.pow_const _).aestronglyMeasurable
  set I0 : ℂ → ℝ := (ball (0 : ℂ) 1).indicator (fun x : ℂ => ‖x‖ ^ (-(3 / 2 : ℝ))) with hI0d
  have hI0 : Integrable I0 := (integrable_indicator_iff measurableSet_ball).2 hA0
  have hE1 : Integrable (fun w : ℂ => (1 + ‖w‖) ^ (-(5 / 2 : ℝ))) :=
    integrable_one_add_norm (by rw [hfin]; norm_num)
  set s2 : ℝ := (2 : ℝ) ^ (1 / 2 : ℝ) with hs2
  set K2 : ℝ := (2 : ℝ) ^ (5 / 2 : ℝ) with hK2
  have hs20 : 0 ≤ s2 := Real.rpow_nonneg (by norm_num) _
  have hK20 : 0 ≤ K2 := Real.rpow_nonneg (by norm_num) _
  set C : ℝ := s2 * ((∫ x, I0 x) + (∫ x : ℂ, (1 + ‖x‖) ^ (-(5 / 2 : ℝ))) +
    K2 * ∫ x : ℂ, (1 + ‖x‖) ^ (-(5 / 2 : ℝ))) with hC
  have hI0n : ∀ x, 0 ≤ I0 x := fun x => by
    rw [hI0d]; exact Set.indicator_nonneg (fun y _ => Real.rpow_nonneg (norm_nonneg _) _) x
  have hC0 : 0 ≤ C := by
    have h1 : 0 ≤ ∫ x, I0 x := integral_nonneg hI0n
    have h2 : 0 ≤ ∫ x : ℂ, (1 + ‖x‖) ^ (-(5 / 2 : ℝ)) := integral_nonneg fun x => Real.rpow_nonneg (by positivity) _
    positivity
  refine ⟨C, hC0, fun b => ?_⟩
  set m : ℂ → ℝ := fun w => s2 * (I0 (w - b) + (1 + ‖w‖) ^ (-(5 / 2 : ℝ)) + K2 * (1 + ‖w - b‖) ^ (-(5 / 2 : ℝ)))
    with hm
  have hmi : Integrable m :=
    (((hI0.comp_sub_right b).add hE1).add ((hE1.comp_sub_right b).const_mul K2)).const_mul s2
  have i1 : Integrable (fun w => I0 (w - b)) := hI0.comp_sub_right b
  have i3 : Integrable (fun w : ℂ => K2 * (1 + ‖w - b‖) ^ (-(5 / 2 : ℝ))) := (hE1.comp_sub_right b).const_mul K2
  have i12 : Integrable (fun w : ℂ => I0 (w - b) + (1 + ‖w‖) ^ (-(5 / 2 : ℝ))) := i1.add hE1
  have t1 := integral_sub_right_eq_self (μ := (volume : Measure ℂ)) (fun x => I0 x) b
  have t2 := integral_sub_right_eq_self (μ := (volume : Measure ℂ)) (fun x : ℂ => (1 + ‖x‖) ^ (-(5 / 2 : ℝ))) b
  have hmv : ∫ w, m w = C := by
    rw [hm, integral_const_mul, integral_add i12 i3, integral_add i1 hE1, integral_const_mul, t1, t2]
  set Bb : ℝ := 1 + ‖b‖ with hBb
  have hBb0 : 0 < Bb := by positivity
  have hpt : ∀ w : ℂ, ((1 + ‖w‖) ^ 2)⁻¹ * ‖w - b‖ ^ (-(3 / 2 : ℝ)) ≤ Bb ^ (-(1 / 2 : ℝ)) * m w := by
    intro w
    by_cases hwb : w = b
    · have : ‖w - b‖ ^ (-(3 / 2 : ℝ)) = 0 := by
        rw [hwb, sub_self, norm_zero, Real.zero_rpow (by norm_num)]
      rw [this, mul_zero]
      refine mul_nonneg (Real.rpow_nonneg hBb0.le _) ?_
      rw [hm]
      exact mul_nonneg hs20 (add_nonneg (add_nonneg (hI0n _) (Real.rpow_nonneg (by positivity) _))
        (mul_nonneg hK20 (Real.rpow_nonneg (by positivity) _)))
    · have hy : 0 < ‖w - b‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hwb)
      have hBxy : Bb ≤ (1 + ‖w‖) * (1 + ‖w - b‖) := by
        have := norm_sub_norm_le b w
        rw [norm_sub_rev] at this
        nlinarith [norm_nonneg w, norm_nonneg (w - b)]
      have hp := s71_t_pt (x := 1 + ‖w‖) (y := ‖w - b‖) (B := Bb) (by linarith [norm_nonneg w]) hy hBb0.le hBxy
      have hif : (if ‖w - b‖ < 1 then ‖w - b‖ ^ (-(3 / 2 : ℝ)) else 0) = I0 (w - b) := by
        rw [hI0d]
        by_cases h : ‖w - b‖ < 1
        · rw [if_pos h, Set.indicator_of_mem (by simpa using h)]
        · rw [if_neg h, Set.indicator_of_notMem (by simpa using h)]
      rw [hif] at hp
      have hBi : Bb ^ (-(1 / 2 : ℝ)) * Bb ^ (1 / 2 : ℝ) = 1 := by
        rw [← Real.rpow_add hBb0]; norm_num
      calc ((1 + ‖w‖) ^ 2)⁻¹ * ‖w - b‖ ^ (-(3 / 2 : ℝ))
          = Bb ^ (-(1 / 2 : ℝ)) * (Bb ^ (1 / 2 : ℝ) * (((1 + ‖w‖) ^ 2)⁻¹ * ‖w - b‖ ^ (-(3 / 2 : ℝ)))) := by
            rw [← mul_assoc, hBi, one_mul]
        _ ≤ Bb ^ (-(1 / 2 : ℝ)) * m w := mul_le_mul_of_nonneg_left hp (Real.rpow_nonneg hBb0.le _)
  have hfm : AEStronglyMeasurable (fun w : ℂ => ((1 + ‖w‖) ^ 2)⁻¹ * ‖w - b‖ ^ (-(3 / 2 : ℝ))) volume := by
    have h1 : Measurable fun w : ℂ => ((1 + ‖w‖) ^ 2)⁻¹ := by fun_prop
    have h2 : Measurable fun w : ℂ => ‖w - b‖ ^ (-(3 / 2 : ℝ)) :=
      ((measurable_id.sub_const b).norm).pow_const _
    exact (h1.mul h2).aestronglyMeasurable
  have hfn : ∀ w : ℂ, 0 ≤ ((1 + ‖w‖) ^ 2)⁻¹ * ‖w - b‖ ^ (-(3 / 2 : ℝ)) := fun w =>
    mul_nonneg (by positivity) (Real.rpow_nonneg (norm_nonneg _) _)
  have hfi : Integrable (fun w : ℂ => ((1 + ‖w‖) ^ 2)⁻¹ * ‖w - b‖ ^ (-(3 / 2 : ℝ))) :=
    (hmi.const_mul (Bb ^ (-(1 / 2 : ℝ)))).mono' hfm (Eventually.of_forall fun w => by
      rw [Real.norm_of_nonneg (hfn w)]; exact hpt w)
  refine ⟨hfi, ?_⟩
  calc ∫ w : ℂ, ((1 + ‖w‖) ^ 2)⁻¹ * ‖w - b‖ ^ (-(3 / 2 : ℝ)) ≤ ∫ w, Bb ^ (-(1 / 2 : ℝ)) * m w :=
        integral_mono hfi (hmi.const_mul _) hpt
    _ = C * Bb ^ (-(1 / 2 : ℝ)) := by rw [integral_const_mul, hmv, mul_comm]

/-- (T3) `(1+|v|)^(−5/2) (Im v)^(−1/2)` is integrable on `𝕌`. -/
theorem s71_t_half :
    IntegrableOn (fun v : ℂ => (1 + ‖v‖) ^ (-(5 / 2 : ℝ)) * v.im ^ (-(1 / 2 : ℝ))) upperHalf := by
  have hf : Integrable (fun x : ℝ => (1 + ‖x‖) ^ (-(5 / 4 : ℝ))) :=
    integrable_one_add_norm (by rw [Module.finrank_self]; norm_num)
  set g : ℝ → ℝ := (Ioi (0 : ℝ)).indicator (fun y => (1 + y) ^ (-(5 / 4 : ℝ)) * y ^ (-(1 / 2 : ℝ))) with hgd
  have hg : Integrable g := by
    rw [hgd, integrable_indicator_iff measurableSet_Ioi]
    have hc : ContinuousOn (fun y : ℝ => (1 + y) ^ (-(5 / 4 : ℝ)) * y ^ (-(1 / 2 : ℝ))) (Ioi 0) := by
      refine ContinuousOn.mul ?_ ?_
      · exact fun y hy => ((continuousAt_const.add continuousAt_id).rpow_const
          (Or.inl (ne_of_gt (by show (0 : ℝ) < 1 + y; have : (0 : ℝ) < y := hy; linarith)))).continuousWithinAt
      · exact fun y hy => (continuousAt_id.rpow_const (Or.inl (ne_of_gt hy))).continuousWithinAt
    have h1 : IntegrableOn (fun y : ℝ => (1 + y) ^ (-(5 / 4 : ℝ)) * y ^ (-(1 / 2 : ℝ))) (Ioo 0 1) := by
      refine ((intervalIntegral.integrableOn_Ioo_rpow_iff one_pos).2 (by norm_num : (-1 : ℝ) < -(1 / 2))).mono' ?_ ?_
      · exact (hc.mono Ioo_subset_Ioi_self).aestronglyMeasurable measurableSet_Ioo
      · filter_upwards [ae_restrict_mem measurableSet_Ioo] with y hy
        have hy0 : 0 < y := hy.1
        rw [Real.norm_of_nonneg (mul_nonneg (Real.rpow_nonneg (by linarith) _) (Real.rpow_nonneg hy0.le _))]
        have : (1 + y) ^ (-(5 / 4 : ℝ)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by norm_num)
        nlinarith [Real.rpow_nonneg hy0.le (-(1 / 2 : ℝ))]
    have h2 : IntegrableOn (fun y : ℝ => (1 + y) ^ (-(5 / 4 : ℝ)) * y ^ (-(1 / 2 : ℝ))) (Ici 1) := by
      refine hf.integrableOn.mono' ?_ ?_
      · exact (hc.mono fun y (hy : 1 ≤ y) => (by show (0 : ℝ) < y; linarith)).aestronglyMeasurable measurableSet_Ici
      · filter_upwards [ae_restrict_mem measurableSet_Ici] with y hy
        have hy1 : (1 : ℝ) ≤ y := hy
        rw [Real.norm_of_nonneg (mul_nonneg (Real.rpow_nonneg (by linarith) _) (Real.rpow_nonneg (by linarith) _)),
          Real.norm_of_nonneg (by linarith : (0 : ℝ) ≤ y)]
        have : y ^ (-(1 / 2 : ℝ)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hy1 (by norm_num)
        nlinarith [Real.rpow_nonneg (by linarith : (0 : ℝ) ≤ 1 + y) (-(5 / 4 : ℝ))]
    refine (h1.union h2).mono_set fun y (hy : 0 < y) => ?_
    by_cases h : y < 1
    · exact Or.inl ⟨hy, h⟩
    · exact Or.inr (not_lt.mp h)
  have hprod : Integrable (fun p : ℝ × ℝ => (1 + ‖p.1‖) ^ (-(5 / 4 : ℝ)) * g p.2) (volume.prod volume) :=
    hf.mul_prod hg
  have hC : Integrable (fun v : ℂ => (1 + ‖v.re‖) ^ (-(5 / 4 : ℝ)) * g v.im) := by
    have h := (Complex.volume_preserving_equiv_real_prod.integrable_comp_emb
      Complex.measurableEquivRealProd.measurableEmbedding).2 hprod
    exact h
  refine hC.integrableOn.mono' ?_ ?_
  · refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_upperHalf_aux
    refine ContinuousOn.mul ?_ ?_
    · exact (continuous_const.add continuous_norm).continuousOn.rpow_const fun v _ => Or.inl (ne_of_gt (by have := norm_nonneg v; show (0:ℝ) < 1 + ‖v‖; linarith))
    · exact fun v hv => ((Complex.continuous_im.continuousAt).rpow_const
        (Or.inl (ne_of_gt (show (0 : ℝ) < v.im from hv)))).continuousWithinAt
  · filter_upwards [ae_restrict_mem measurableSet_upperHalf_aux] with v hv
    have hv0 : 0 < v.im := hv
    have hgv : g v.im = (1 + v.im) ^ (-(5 / 4 : ℝ)) * v.im ^ (-(1 / 2 : ℝ)) := by
      rw [hgd, Set.indicator_of_mem (show v.im ∈ Ioi (0 : ℝ) from hv0)]
    rw [hgv, Real.norm_of_nonneg (mul_nonneg (Real.rpow_nonneg (by positivity) _) (Real.rpow_nonneg hv0.le _))]
    have hre : ‖v.re‖ ≤ ‖v‖ := by rw [Real.norm_eq_abs]; exact Complex.abs_re_le_norm v
    have him : v.im ≤ ‖v‖ := (le_abs_self _).trans (Complex.abs_im_le_norm v)
    have hprod' : (1 + ‖v.re‖) * (1 + v.im) ≤ (1 + ‖v‖) ^ 2 := by
      nlinarith [norm_nonneg v.re, norm_nonneg v]
    have hkey : (1 + ‖v‖) ^ (-(5 / 2 : ℝ)) ≤ (1 + ‖v.re‖) ^ (-(5 / 4 : ℝ)) * (1 + v.im) ^ (-(5 / 4 : ℝ)) := by
      rw [← Real.mul_rpow (by positivity) (by linarith)]
      have e : (1 + ‖v‖) ^ (-(5 / 2 : ℝ)) = ((1 + ‖v‖) ^ 2) ^ (-(5 / 4 : ℝ)) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]; norm_num
      rw [e]
      exact Real.rpow_le_rpow_of_nonpos (by positivity) hprod' (by norm_num)
    calc (1 + ‖v‖) ^ (-(5 / 2 : ℝ)) * v.im ^ (-(1 / 2 : ℝ))
        ≤ (1 + ‖v.re‖) ^ (-(5 / 4 : ℝ)) * (1 + v.im) ^ (-(5 / 4 : ℝ)) * v.im ^ (-(1 / 2 : ℝ)) :=
          mul_le_mul_of_nonneg_right hkey (Real.rpow_nonneg hv0.le _)
      _ = (1 + ‖v.re‖) ^ (-(5 / 4 : ℝ)) * ((1 + v.im) ^ (-(5 / 4 : ℝ)) * v.im ^ (-(1 / 2 : ℝ))) := by ring

/-! ### The `J`-block helpers (下属2) -/

/-- The torus calculus of `e64_torus_dz` with both Wirtinger derivatives and differentiability. -/
theorem s71_b2_torus_d {G : ℂ × ℂ → ℂ} {g : ℂ → ℂ} {r : ℝ} (hr : 0 < r)
    (hG : ContinuousOn G (sphere (0 : ℂ) r ×ˢ sphere (0 : ℂ) r))
    (hg : ∀ᶠ ε in 𝓝 (0 : ℂ), g ε = ((2 * π * I)⁻¹) ^ 2 *
      ∮ a in C(0, r), ∮ b in C(0, r), G (a, b) / ((a - ε) * (b - conj ε))) :
    DifferentiableAt ℝ g 0 ∧
      dz g 0 = ((2 * π * I)⁻¹) ^ 2 * ∮ a in C(0, r), ∮ b in C(0, r), G (a, b) / (a ^ 2 * b) ∧
      dzbar g 0 = ((2 * π * I)⁻¹) ^ 2 * ∮ a in C(0, r), ∮ b in C(0, r), G (a, b) / (a * b ^ 2) := by
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
  refine ⟨hD.differentiableAt, ?_, ?_⟩
  · show (fderiv ℝ g 0 1 - I * fderiv ℝ g 0 I) / 2 = c * A₁
    rw [hfd, hLapp, hLapp]
    simp only [map_one, Complex.conj_I]
    ring_nf
    rw [Complex.I_sq]
    ring
  · show (fderiv ℝ g 0 1 + I * fderiv ℝ g 0 I) / 2 = c * A₂
    rw [hfd, hLapp, hLapp]
    simp only [map_one, Complex.conj_I]
    ring_nf
    rw [Complex.I_sq]
    ring

/-- Pointwise Beltrami equation and positive Jacobian of `W_q` on `𝕌`. -/
theorem s71_b2_beltrami {ν : ℂ → ℂ} {k : ℝ} (hk : 0 ≤ k) (hνk : IsBeltramiCoeff ν upperHalf k)
    (hνs : ContDiffOn ℝ (⊤ : ℕ∞) ν upperHalf)
    {W : ℂ × ℂ → ℂ → ℂ} (hW : W = fun P => normalizedSolution fun u =>
      P.1 * (if 0 < u.im then ν u else 0) + P.2 * (if u.im < 0 then conj (ν (conj u)) else 0))
    {q : ℂ × ℂ} (hq : q ∈ {P : ℂ × ℂ | max ‖P.1‖ ‖P.2‖ * k < 1}) {y : ℂ} (hy : y ∈ upperHalf) :
    dzbar (W q) y = q.1 * ν y * dz (W q) y ∧ 0 < jacobian (W q) y := by
  obtain ⟨hC, -, -⟩ := e64_W_basic hk hνk hνs hW
  obtain ⟨hm₁, hm₂, -, -, hcomb⟩ := wr_U_coeffs hk hνk hνs
  obtain ⟨hs₁, hs₂⟩ := e64_m_smooth hνs
  have hΩ : IsOpen {u : ℂ | u.im ≠ 0} := isOpen_ne_fun Complex.continuous_im continuous_const
  have hU : IsOpen upperHalf := isOpen_lt continuous_const Complex.continuous_im
  have hUΩ : upperHalf ⊆ {u : ℂ | u.im ≠ 0} := fun u hu => ne_of_gt hu
  have hJ : ∀ x ∈ upperHalf, 0 < jacobian (W q) x := by
    intro x hx
    rw [hW]
    exact wr_local_jacobian_pos hm₁ hm₂ hΩ hs₁ hs₂ (hcomb q.1 q.2 hq) (hUΩ hx)
  refine ⟨?_, hJ y hy⟩
  set f := W q with hf
  have hCf : ContDiffOn ℝ 3 f upperHalf := by
    have h := hC.comp (s := upperHalf) (contDiffOn_const.prodMk contDiffOn_id) (fun x hx => ⟨hq, hUΩ hx⟩)
    exact h
  have hdz0 : ∀ x ∈ upperHalf, dz f x ≠ 0 := by
    intro x hx h0
    have := hJ x hx
    unfold jacobian at this
    rw [h0, norm_zero] at this
    nlinarith [norm_nonneg (dzbar f x)]
  have hfd : ContinuousOn (fderiv ℝ f) upperHalf := hCf.continuousOn_fderiv_of_isOpen hU (by norm_num)
  have hdzc : ContinuousOn (dz f) upperHalf := by
    unfold dz
    exact (((hfd.clm_apply continuousOn_const).sub (continuousOn_const.mul
      (hfd.clm_apply continuousOn_const)))).div_const _
  have hdzbc : ContinuousOn (dzbar f) upperHalf := by
    unfold dzbar
    exact (((hfd.clm_apply continuousOn_const).add (continuousOn_const.mul
      (hfd.clm_apply continuousOn_const)))).div_const _
  have hcd : ContinuousOn (complexDilatation f) upperHalf := hdzbc.div hdzc hdz0
  have hcm : ContinuousOn (fun x => q.1 * ν x) upperHalf := continuousOn_const.mul hνs.continuousOn
  obtain ⟨k', hk', hP'⟩ := hcomb q.1 q.2 hq
  obtain ⟨h0, hk0, hk1⟩ := wr_coeff_nonneg hk' hP'
  have hns := QCV.qcv_ns_spec hk0 hk1 h0
  have hae : complexDilatation f =ᵐ[volume.restrict upperHalf] fun x => q.1 * ν x := by
    filter_upwards [ae_restrict_of_ae hns.2.2.2.2, ae_restrict_mem hU.measurableSet] with x hx hxU
    rw [hf, hW]
    rw [hx]
    have h1 : 0 < x.im := hxU
    have h2 : ¬ (x.im < 0) := not_lt.mpr (le_of_lt h1)
    simp only [h1, h2, ↓reduceIte, mul_zero, add_zero]
  have heq := Measure.eqOn_open_of_ae_eq hae hU hcd hcm hy
  have e : dzbar f y = complexDilatation f y * dz f y := (div_mul_cancel₀ _ (hdz0 y hy)).symm
  rw [e, heq]

/-- Joint continuity of `Ψ` on `closed polydisc × 𝕌`. -/
theorem s71_b2_cont {μ ν : ℂ → ℂ} {k : ℝ} (hk : 0 ≤ k) (hνk : IsBeltramiCoeff ν upperHalf k)
    (hνs : ContDiffOn ℝ (⊤ : ℕ∞) ν upperHalf) (hμc : ContinuousOn μ upperHalf) {z : ℂ} (hz : z ∈ upperHalf)
    {R : ℝ} (hRk : R * k < 1)
    {W : ℂ × ℂ → ℂ → ℂ} (hW : W = fun P => normalizedSolution fun u =>
      P.1 * (if 0 < u.im then ν u else 0) + P.2 * (if u.im < 0 then conj (ν (conj u)) else 0))
    {Ψ : ℂ × ℂ → ℂ → ℂ} (hΨ : Ψ = fun P u => μ u * (dz (W P) u * dz (W P) (conj z) / (W P u - W P (conj z)) ^ 2) ^ 2) :
    ContinuousOn (fun p : (ℂ × ℂ) × ℂ => Ψ p.1 p.2) ((closedBall (0 : ℂ) R ×ˢ closedBall (0 : ℂ) R) ×ˢ upperHalf) := by
  obtain ⟨-, hinj, -⟩ := e64_W_basic hk hνk hνs hW
  obtain ⟨hWc, hDc⟩ := e64_dzW_cont hk hνk hνs hW
  have hsub := e64_polydisc_sub hk hRk
  obtain ⟨T, hT⟩ : ∃ T : Set ((ℂ × ℂ) × ℂ), T = (closedBall (0 : ℂ) R ×ˢ closedBall (0 : ℂ) R) ×ˢ upperHalf :=
    ⟨_, rfl⟩
  rw [← hT]
  have hmem : ∀ p ∈ T, p.1 ∈ closedBall (0 : ℂ) R ×ˢ closedBall (0 : ℂ) R ∧ 0 < p.2.im := by
    rw [hT]
    rintro p ⟨h1, h2⟩
    exact ⟨h1, h2⟩
  have hzim : 0 < z.im := hz
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
  obtain ⟨hWu, hDu⟩ := hcomp (fun p => p.2) continuous_snd fun p hp => ne_of_gt (hmem p hp).2
  obtain ⟨hWzb, hDzb⟩ := hcomp (fun _ => conj z) continuous_const fun _ _ => by
    rw [Complex.conj_im]; linarith
  have hμc' : ContinuousOn (fun p : (ℂ × ℂ) × ℂ => μ p.2) T :=
    hμc.comp continuous_snd.continuousOn fun p hp => (hmem p hp).2
  have hne : ∀ p ∈ T, (W p.1 p.2 - W p.1 (conj z)) ^ 2 ≠ 0 := by
    intro p hp
    refine pow_ne_zero 2 (sub_ne_zero.mpr fun h => ?_)
    have := hinj p.1 (hsub (hmem p hp).1) h
    have h2 : p.2.im = (conj z).im := by rw [this]
    rw [Complex.conj_im] at h2
    linarith [(hmem p hp).2]
  rw [hΨ]
  exact hμc'.mul (((hDu.mul hDzb).div ((hWu.sub hWzb).pow 2) hne).pow 2)

/-- Separate holomorphy of `P ↦ Ψ(P)(u)`. -/
theorem s71_b2_holo {μ ν : ℂ → ℂ} {k : ℝ} (hk : 0 ≤ k) (hνk : IsBeltramiCoeff ν upperHalf k)
    (hνs : ContDiffOn ℝ (⊤ : ℕ∞) ν upperHalf) {z : ℂ} (hz : z ∈ upperHalf) {R : ℝ} (hRk : R * k < 1)
    {W : ℂ × ℂ → ℂ → ℂ} (hW : W = fun P => normalizedSolution fun u =>
      P.1 * (if 0 < u.im then ν u else 0) + P.2 * (if u.im < 0 then conj (ν (conj u)) else 0))
    {Ψ : ℂ × ℂ → ℂ → ℂ} (hΨ : Ψ = fun P u => μ u * (dz (W P) u * dz (W P) (conj z) / (W P u - W P (conj z)) ^ 2) ^ 2)
    {u : ℂ} (hu : u ∈ upperHalf) :
    (∀ b ∈ closedBall (0 : ℂ) R, DifferentiableOn ℂ (fun a => Ψ (a, b) u) (ball (0 : ℂ) R)) ∧
      ∀ a ∈ closedBall (0 : ℂ) R, DifferentiableOn ℂ (fun b => Ψ (a, b) u) (ball (0 : ℂ) R) := by
  obtain ⟨-, hinj, hhol⟩ := e64_W_basic hk hνk hνs hW
  have hsub := e64_polydisc_sub hk hRk
  have hzim : 0 < z.im := hz
  have huim : 0 < u.im := hu
  have hy1 : u.im ≠ 0 := huim.ne'
  have hy3 : (conj z).im ≠ 0 := by rw [Complex.conj_im]; linarith
  have hne : ∀ P ∈ {P : ℂ × ℂ | max ‖P.1‖ ‖P.2‖ * k < 1}, (W P u - W P (conj z)) ^ 2 ≠ 0 := by
    intro P hP
    refine pow_ne_zero 2 (sub_ne_zero.mpr fun h => ?_)
    have := hinj P hP h
    have h2 : u.im = (conj z).im := by rw [this]
    rw [Complex.conj_im] at h2
    linarith
  have hcurve : ∀ (c : ℂ → ℂ × ℂ) (t : ℂ), c t ∈ {P : ℂ × ℂ | max ‖P.1‖ ‖P.2‖ * k < 1} →
      (∀ y, DifferentiableAt ℂ (fun t' => W (c t') y) t) →
      (∀ y, y.im ≠ 0 → DifferentiableAt ℂ (fun t' => dz (W (c t')) y) t) →
      DifferentiableAt ℂ (fun t' => Ψ (c t') u) t := by
    intro c t hct hWy hDy
    rw [hΨ]
    exact (differentiableAt_const _).mul ((((hDy u hy1).mul (hDy _ hy3)).div
      (((hWy u).sub (hWy (conj z))).pow 2) (hne _ hct)).pow 2)
  constructor
  · intro b hb a ha
    have hP : (a, b) ∈ {P : ℂ × ℂ | max ‖P.1‖ ‖P.2‖ * k < 1} := hsub ⟨ball_subset_closedBall ha, hb⟩
    refine (hcurve (fun t => (t, b)) a hP (fun y => ?_) (fun y hy => ?_)).differentiableWithinAt
    · exact DifferentiableAt.comp (g := fun Q => W Q y) a (hhol y _ hP) (by fun_prop)
    · exact (e64_dzW_holo hk hνk hνs hW hP hy).1
  · intro a ha b hb
    have hP : (a, b) ∈ {P : ℂ × ℂ | max ‖P.1‖ ‖P.2‖ * k < 1} := hsub ⟨ha, ball_subset_closedBall hb⟩
    refine (hcurve (fun t => (a, t)) b hP (fun y => ?_) (fun y hy => ?_)).differentiableWithinAt
    · exact DifferentiableAt.comp (g := fun Q => W Q y) b (hhol y _ hP) (by fun_prop)
    · exact (e64_dzW_holo hk hνk hνs hW hP hy).2

/-- On the diagonal `P = (ε, ε̄)`, `Ψ` is the integrand of `J`. -/
theorem s71_b2_diag {μ ν : ℂ → ℂ} {k : ℝ} (hk : 0 ≤ k) (hνk : IsBeltramiCoeff ν upperHalf k) {z : ℂ}
    {W : ℂ × ℂ → ℂ → ℂ} (hW : W = fun P => normalizedSolution fun u =>
      P.1 * (if 0 < u.im then ν u else 0) + P.2 * (if u.im < 0 then conj (ν (conj u)) else 0))
    {Ψ : ℂ × ℂ → ℂ → ℂ} (hΨ : Ψ = fun P u => μ u * (dz (W P) u * dz (W P) (conj z) / (W P u - W P (conj z)) ^ 2) ^ 2)
    {ε : ℂ} (hε : ‖ε‖ * k < 1) (u : ℂ) :
    Ψ (ε, conj ε) u = μ u * kernelKbar (fun y => ε * ν y) u z ^ 2 := by
  have hWe : W (ε, conj ε) = wU (fun y => ε * ν y) := by rw [hW, wr_wU_eq]
  set f := wU (fun y => ε * ν y) with hf
  have hνε : IsBeltramiCoeff (fun y => ε * ν y) upperHalf (‖ε‖ * k) :=
    ⟨hνk.1.const_mul ε, hνk.2.mono fun z hz => by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left hz (norm_nonneg _)⟩
  have hsym : ∀ x, f (conj x) = conj (f x) := by
    rw [hf, e124_wU_eq_fMuSym hk hνk hε]
    exact (fMuSym_upperHalf (by positivity) hε hνε).2.2.1
  have hdsym : ∀ x, dz f (conj x) = conj (dz f x) := QCV.qcv_dz_conj_sym hsym
  rw [hΨ]
  simp only [hWe]
  unfold kernelKbar
  rw [← hf, hsym z, hdsym z]

/-- **Uniform `L¹(𝕌)` bound** for `Ψ(q)` over the closed polydisc (E5 simplified). -/
theorem s71_b2_L1 {μ ν : ℂ → ℂ} {k Mμ : ℝ} (hk : 0 ≤ k) (hνk : IsBeltramiCoeff ν upperHalf k)
    (hνs : ContDiffOn ℝ (⊤ : ℕ∞) ν upperHalf) (hμc : ContinuousOn μ upperHalf) (hMμ : 0 ≤ Mμ)
    (hμb : ∀ u ∈ upperHalf, ‖μ u‖ ≤ Mμ) {z : ℂ} (hz : z ∈ upperHalf) {R : ℝ} (hRk : R * k < 1)
    {W : ℂ × ℂ → ℂ → ℂ} (hW : W = fun P => normalizedSolution fun u =>
      P.1 * (if 0 < u.im then ν u else 0) + P.2 * (if u.im < 0 then conj (ν (conj u)) else 0))
    {Ψ : ℂ × ℂ → ℂ → ℂ} (hΨ : Ψ = fun P u => μ u * (dz (W P) u * dz (W P) (conj z) / (W P u - W P (conj z)) ^ 2) ^ 2) :
    ∃ M : ℝ, ∀ q ∈ closedBall (0 : ℂ) R ×ˢ closedBall (0 : ℂ) R,
      IntegrableOn (Ψ q) upperHalf ∧ ∫ u in upperHalf, ‖Ψ q u‖ ≤ M := by
  obtain ⟨hC, hinj, -⟩ := e64_W_basic hk hνk hνs hW
  obtain ⟨-, hDc⟩ := e64_dzW_cont hk hνk hνs hW
  obtain ⟨hm₁, -, -, -, -⟩ := wr_U_coeffs hk hνk hνs
  obtain ⟨hs₁, -⟩ := e64_m_smooth hνs
  have hcΨ := s71_b2_cont hk hνk hνs hμc hz hRk hW hΨ
  have hsub := e64_polydisc_sub hk hRk
  have hU : IsOpen upperHalf := isOpen_lt continuous_const Complex.continuous_im
  have hUm : MeasurableSet upperHalf := hU.measurableSet
  have hΩ : IsOpen {u : ℂ | u.im ≠ 0} := isOpen_ne_fun Complex.continuous_im continuous_const
  have hWo : IsOpen {P : ℂ × ℂ | max ‖P.1‖ ‖P.2‖ * k < 1} :=
    isOpen_lt (((continuous_norm.comp continuous_fst).max (continuous_norm.comp continuous_snd)).mul
      continuous_const) continuous_const
  have hzim : 0 < z.im := hz
  have hK : IsCompact (closedBall (0 : ℂ) R ×ˢ closedBall (0 : ℂ) R) :=
    (isCompact_closedBall 0 R).prod (isCompact_closedBall 0 R)
  have hνb : ∀ v ∈ upperHalf, ‖ν v‖ ≤ k := by
    intro v hv
    have hc : ContinuousOn (fun u => if 0 < u.im then ν u else 0) upperHalf :=
      hs₁.continuousOn.mono fun u hu => ne_of_gt hu
    have h := wr_ae_bound_on hU hc (by simpa only [Measure.restrict_univ] using hm₁.2) v hv
    have hv' : 0 < v.im := hv
    simpa only [hv', ↓reduceIte] using h
  -- uniform bound for `∂W` at `z̄`
  obtain ⟨B, hB0, hB⟩ : ∃ B : ℝ, 0 ≤ B ∧ ∀ q ∈ closedBall (0 : ℂ) R ×ˢ closedBall (0 : ℂ) R,
      ‖dz (W q) (conj z)‖ ≤ B := by
    have hc : (conj z).im ≠ 0 := by rw [Complex.conj_im]; linarith
    have hco : ContinuousOn (fun q : ℂ × ℂ => dz (W q) (conj z)) (closedBall (0 : ℂ) R ×ˢ closedBall (0 : ℂ) R) := by
      have h := hDc.comp (continuous_id.prodMk continuous_const).continuousOn
        (fun q hq => (⟨hsub hq, hc⟩ : (q, conj z) ∈ {P : ℂ × ℂ | max ‖P.1‖ ‖P.2‖ * k < 1} ×ˢ {u : ℂ | u.im ≠ 0}))
      simpa only [Function.comp_def, id] using h
    obtain ⟨A, hA⟩ := hK.exists_bound_of_continuousOn hco
    exact ⟨max A 0, le_max_right _ _, fun q hq => (hA q hq).trans (le_max_left _ _)⟩
  obtain ⟨η, hη, hsep⟩ := e64_t5_sep hk hνk hνs hRk hW (conj z) hzim
  set Cη : ℝ := ((1 + η) / η) ^ 4 with hCη
  set I0 : ℝ := ∫ ζ : ℂ, ((1 + ‖ζ‖) ^ 4)⁻¹ with hI0
  refine ⟨Mμ * B ^ 2 / (1 - (R * k) ^ 2) * (Cη * (I0 + I0)), fun q hq => ?_⟩
  have hR0 : 0 ≤ R := (norm_nonneg q.1).trans (by simpa using hq.1)
  have hRk0 : 0 ≤ R * k := mul_nonneg hR0 hk
  have hden : 0 < 1 - (R * k) ^ 2 := by nlinarith
  have hK0 : 0 ≤ Mμ * B ^ 2 / (1 - (R * k) ^ 2) := by positivity
  have hqW := hsub hq
  set f := W q with hf
  have hfd : ∀ u ∈ upperHalf, DifferentiableAt ℝ f u := by
    intro u hu
    have hm : (q, u) ∈ {P : ℂ × ℂ | max ‖P.1‖ ‖P.2‖ * k < 1} ×ˢ {u : ℂ | u.im ≠ 0} := ⟨hqW, ne_of_gt hu⟩
    have h3 : ContDiffAt ℝ 3 (fun y => W q y) u :=
      ContDiffAt.comp (g := fun p : (ℂ × ℂ) × ℂ => W p.1 p.2) u (hC.contDiffAt ((hWo.prod hΩ).mem_nhds hm))
        (contDiffAt_const.prodMk contDiffAt_id)
    exact h3.differentiableAt (by norm_num)
  have hder : ∀ u ∈ upperHalf, HasFDerivWithinAt f (fderiv ℝ f u) upperHalf u := fun u hu =>
    (hfd u hu).hasFDerivAt.hasFDerivWithinAt
  have hinjS : InjOn f upperHalf := fun x _ y _ hxy => hinj q hqW hxy
  set G2 : ℂ → ℝ := fun ζ => Cη * (((1 + ‖ζ - f (conj z)‖) ^ 4)⁻¹ + ((1 + ‖ζ - f (conj z)‖) ^ 4)⁻¹) with hG2
  have hG2i : Integrable G2 :=
    ((e64_t5_maj (f (conj z))).1.add (e64_t5_maj (f (conj z))).1).const_mul Cη
  have hG2v : ∫ ζ, G2 ζ = Cη * (I0 + I0) := by
    rw [hG2, integral_const_mul, integral_add (e64_t5_maj (f (conj z))).1 (e64_t5_maj (f (conj z))).1,
      (e64_t5_maj _).2]
  have hG2n : ∀ ζ, 0 ≤ G2 ζ := fun ζ => by positivity
  have hRi : IntegrableOn (fun u => |(fderiv ℝ f u).det| • G2 (f u)) upperHalf :=
    (integrableOn_image_iff_integrableOn_abs_det_fderiv_smul volume hUm hder hinjS G2).mp hG2i.integrableOn
  have hpt : ∀ u ∈ upperHalf, ‖Ψ q u‖ ≤ Mμ * B ^ 2 / (1 - (R * k) ^ 2) * (|(fderiv ℝ f u).det| • G2 (f u)) := by
    intro u hu
    obtain ⟨hbel, hJ⟩ := s71_b2_beltrami hk hνk hνs hW hqW hu
    have hu' : 0 < u.im := hu
    have hX : η ≤ ‖f u - f (conj z)‖ := by
      refine hsep q hq u ?_
      have := e64_t10_im hu' (show (conj z).im < 0 by rw [Complex.conj_im]; linarith)
      rwa [Complex.conj_im, neg_neg] at this
    have hXp : 0 < ‖f u - f (conj z)‖ := hη.trans_le hX
    have hD2 : ‖dz f u‖ ^ 2 ≤ jacobian f u / (1 - (R * k) ^ 2) := by
      have hbar : ‖dzbar f u‖ ≤ R * k * ‖dz f u‖ := by
        rw [hbel, norm_mul, norm_mul]
        have hq1 : ‖q.1‖ ≤ R := by simpa using hq.1
        exact mul_le_mul_of_nonneg_right (mul_le_mul hq1 (hνb u hu) (norm_nonneg _) hR0) (norm_nonneg _)
      have hsq := pow_le_pow_left₀ (norm_nonneg _) hbar 2
      rw [le_div_iff₀ hden]
      unfold jacobian
      nlinarith
    have hinv := e64_t5_inv4 hη hX hX
    have hdv : |(fderiv ℝ f u).det| = jacobian f u := by
      rw [show (fderiv ℝ f u).det = jacobian f u from det_fderiv_eq_jacobian (hfd u hu), abs_of_pos hJ]
    rw [hdv, smul_eq_mul, hΨ]
    simp only [norm_mul, norm_div, norm_pow]
    set X := ‖f u - f (conj z)‖
    set Dd := ‖dz f u‖
    have hBq := hB q hq
    have e : ‖μ u‖ * (Dd * ‖dz f (conj z)‖ / X ^ 2) ^ 2 = (‖μ u‖ * ‖dz f (conj z)‖ ^ 2) * Dd ^ 2 * (1 / (X ^ 2 * X ^ 2)) := by
      field_simp
    rw [e]
    have hma : ‖μ u‖ * ‖dz f (conj z)‖ ^ 2 ≤ Mμ * B ^ 2 :=
      mul_le_mul (hμb u hu) (pow_le_pow_left₀ (norm_nonneg _) hBq 2) (by positivity) hMμ
    calc (‖μ u‖ * ‖dz f (conj z)‖ ^ 2) * Dd ^ 2 * (1 / (X ^ 2 * X ^ 2))
        ≤ (Mμ * B ^ 2) * (jacobian f u / (1 - (R * k) ^ 2)) * (Cη * (((1 + X) ^ 4)⁻¹ + ((1 + X) ^ 4)⁻¹)) := by
          refine mul_le_mul (mul_le_mul hma hD2 (by positivity) (by positivity)) hinv (by positivity)
            (mul_nonneg (by positivity) (div_nonneg hJ.le hden.le))
      _ = Mμ * B ^ 2 / (1 - (R * k) ^ 2) * (jacobian f u * G2 (f u)) := by
          simp only [hG2]
          ring
  have hcS : ContinuousOn (Ψ q) upperHalf := by
    have h1 := hcΨ.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun v (hv : v ∈ upperHalf) => (⟨hq, hv⟩ :
        (q, v) ∈ (closedBall (0 : ℂ) R ×ˢ closedBall (0 : ℂ) R) ×ˢ upperHalf))
    simpa only [Function.comp_def, id] using h1
  have hΨi : IntegrableOn (Ψ q) upperHalf := by
    refine (hRi.const_mul (Mμ * B ^ 2 / (1 - (R * k) ^ 2))).mono' (hcS.aestronglyMeasurable hUm) ?_
    filter_upwards [ae_restrict_mem hUm] with v hv
    exact hpt v hv
  refine ⟨hΨi, ?_⟩
  calc ∫ u in upperHalf, ‖Ψ q u‖ ≤ ∫ u in upperHalf, Mμ * B ^ 2 / (1 - (R * k) ^ 2) * (|(fderiv ℝ f u).det| • G2 (f u)) :=
        setIntegral_mono_on hΨi.norm (hRi.const_mul _) hUm hpt
    _ = Mμ * B ^ 2 / (1 - (R * k) ^ 2) * ∫ u in upperHalf, |(fderiv ℝ f u).det| • G2 (f u) := integral_const_mul _ _
    _ = Mμ * B ^ 2 / (1 - (R * k) ^ 2) * ∫ ζ in f '' upperHalf, G2 ζ := by
        rw [integral_image_eq_integral_abs_det_fderiv_smul volume hUm hder hinjS G2]
    _ ≤ Mμ * B ^ 2 / (1 - (R * k) ^ 2) * ∫ ζ, G2 ζ :=
        mul_le_mul_of_nonneg_left (setIntegral_le_integral hG2i (Eventually.of_forall hG2n)) hK0
    _ = Mμ * B ^ 2 / (1 - (R * k) ^ 2) * (Cη * (I0 + I0)) := by rw [hG2v]

/-- Domination of `Ψ(P)` on a smaller closed polydisc by an integrable majorant on `𝕌` (as `e64_dominate`). -/
theorem s71_b2_dom {μ ν : ℂ → ℂ} {k Mμ : ℝ} (hk : 0 ≤ k) (hνk : IsBeltramiCoeff ν upperHalf k)
    (hνs : ContDiffOn ℝ (⊤ : ℕ∞) ν upperHalf) (hμc : ContinuousOn μ upperHalf) (hMμ : 0 ≤ Mμ)
    (hμb : ∀ u ∈ upperHalf, ‖μ u‖ ≤ Mμ) {z : ℂ} (hz : z ∈ upperHalf) {r R : ℝ} (hr : 0 < r) (hrR : r < R)
    (hRk : R * k < 1)
    {W : ℂ × ℂ → ℂ → ℂ} (hW : W = fun P => normalizedSolution fun u =>
      P.1 * (if 0 < u.im then ν u else 0) + P.2 * (if u.im < 0 then conj (ν (conj u)) else 0))
    {Ψ : ℂ × ℂ → ℂ → ℂ} (hΨ : Ψ = fun P u => μ u * (dz (W P) u * dz (W P) (conj z) / (W P u - W P (conj z)) ^ 2) ^ 2) :
    ∃ g : ℂ → ℝ, IntegrableOn g upperHalf ∧
      ∀ P ∈ closedBall (0 : ℂ) r ×ˢ closedBall (0 : ℂ) r, ∀ u ∈ upperHalf, ‖Ψ P u‖ ≤ g u := by
  have hR : 0 < R := hr.trans hrR
  obtain ⟨M, hM⟩ := s71_b2_L1 hk hνk hνs hμc hMμ hμb hz hRk hW hΨ
  have hcΨ := s71_b2_cont hk hνk hνs hμc hz hRk hW hΨ
  have hU : IsOpen upperHalf := isOpen_lt continuous_const Complex.continuous_im
  have hSm : MeasurableSet upperHalf := hU.measurableSet
  set ν' : Measure ℝ := volume.restrict (Ioc 0 (2 * π)) with hν'
  haveI : IsFiniteMeasure ν' := by
    rw [hν']
    exact (isFiniteMeasure_restrict (μ := (volume : Measure ℝ)) (s := Ioc 0 (2 * π))).mpr measure_Ioc_lt_top.ne
  have hcm : ∀ θ : ℝ, circleMap 0 R θ ∈ closedBall (0 : ℂ) R := fun θ =>
    sphere_subset_closedBall (circleMap_mem_sphere 0 hR.le θ)
  set Φ' : (ℝ × ℝ) × ℂ → ℝ := fun p => ‖Ψ (circleMap 0 R p.1.1, circleMap 0 R p.1.2) p.2‖ with hΦ'
  have hΦc : ContinuousOn Φ' (univ ×ˢ upperHalf) := by
    have h := hcΨ.comp ((((continuous_circleMap 0 R).comp (continuous_fst.comp continuous_fst)).prodMk
      ((continuous_circleMap 0 R).comp (continuous_snd.comp continuous_fst))).prodMk continuous_snd).continuousOn
      (fun p (hp : p ∈ (univ : Set (ℝ × ℝ)) ×ˢ upperHalf) => (⟨⟨hcm p.1.1, hcm p.1.2⟩, hp.2⟩ :
        ((circleMap 0 R p.1.1, circleMap 0 R p.1.2), p.2) ∈
          (closedBall (0 : ℂ) R ×ˢ closedBall (0 : ℂ) R) ×ˢ upperHalf))
    exact h.norm
  have hprod : (ν'.prod ν').prod (volume.restrict upperHalf) =
      ((volume.prod volume).prod volume).restrict ((Ioc 0 (2 * π) ×ˢ Ioc 0 (2 * π)) ×ˢ upperHalf) := by
    rw [hν', Measure.prod_restrict, Measure.prod_restrict]
  have hΦm : AEStronglyMeasurable Φ' ((ν'.prod ν').prod (volume.restrict upperHalf)) := by
    rw [hprod]
    exact (hΦc.mono (prod_mono (subset_univ _) subset_rfl)).aestronglyMeasurable
      ((measurableSet_Ioc.prod measurableSet_Ioc).prod hSm)
  have hΦi : Integrable Φ' ((ν'.prod ν').prod (volume.restrict upperHalf)) := by
    refine (integrable_prod_iff hΦm).2 ⟨Eventually.of_forall fun θ => ?_, ?_⟩
    · have hq : (circleMap 0 R θ.1, circleMap 0 R θ.2) ∈ closedBall (0 : ℂ) R ×ˢ closedBall (0 : ℂ) R :=
        ⟨hcm θ.1, hcm θ.2⟩
      exact (hM _ hq).1.norm
    · refine (integrable_const M).mono' hΦm.norm.integral_prod_right' (Eventually.of_forall fun θ => ?_)
      rw [Real.norm_of_nonneg (integral_nonneg fun v => norm_nonneg _)]
      have hq : (circleMap 0 R θ.1, circleMap 0 R θ.2) ∈ closedBall (0 : ℂ) R ×ˢ closedBall (0 : ℂ) R :=
        ⟨hcm θ.1, hcm θ.2⟩
      simpa only [hΦ', norm_norm] using (hM _ hq).2
  set C : ℝ := ‖((2 * π * I)⁻¹ : ℂ) ^ 2‖ * (R ^ 2 * (1 / (R - r) ^ 2)) with hC
  refine ⟨fun v => C * ∫ θ, Φ' (θ, v) ∂(ν'.prod ν'), hΦi.integral_prod_right.const_mul C, fun P hP v hv => ?_⟩
  have hP1 : ‖P.1‖ ≤ r := by simpa using hP.1
  have hP2 : ‖P.2‖ ≤ r := by simpa using hP.2
  have hPin : P ∈ ball ((0, 0) : ℂ × ℂ).1 R ×ˢ ball ((0, 0) : ℂ × ℂ).2 R :=
    ⟨by simpa using hP1.trans_lt hrR, by simpa using hP2.trans_lt hrR⟩
  have hcv : ContinuousOn (fun q : ℂ × ℂ => Ψ q v) (closedBall ((0, 0) : ℂ × ℂ).1 R ×ˢ closedBall ((0, 0) : ℂ × ℂ).2 R) := by
    have h := hcΨ.comp (continuous_id.prodMk continuous_const).continuousOn
      (fun q hq => (⟨hq, hv⟩ : (q, v) ∈ (closedBall (0 : ℂ) R ×ˢ closedBall (0 : ℂ) R) ×ˢ upperHalf))
    simpa only [Function.comp_def, id] using h
  obtain ⟨h1, h2⟩ := s71_b2_holo hk hνk hνs hz hRk hW hΨ hv
  have hrep := wr_cauchy_bidisc (f := fun q => Ψ q v) (c := ((0, 0) : ℂ × ℂ)) hR hR hcv h1 h2 hPin
  simp only at hrep
  rw [hrep, norm_mul]
  have hden : ∀ a ∈ sphere (0 : ℂ) R, ∀ b ∈ sphere (0 : ℂ) R, R - r ≤ ‖a - P.1‖ ∧ R - r ≤ ‖b - P.2‖ := by
    intro a ha b hb
    have ha' : ‖a‖ = R := by simpa using ha
    have hb' : ‖b‖ = R := by simpa using hb
    constructor
    · have := norm_sub_norm_le a P.1; linarith
    · have := norm_sub_norm_le b P.2; linarith
  have hFc : ContinuousOn (fun q : ℂ × ℂ => Ψ (q.1, q.2) v / ((q.1 - P.1) * (q.2 - P.2)))
      (sphere (0 : ℂ) R ×ˢ sphere (0 : ℂ) R) := by
    refine (hcv.mono (prod_mono sphere_subset_closedBall sphere_subset_closedBall)).div
      (((continuous_fst.sub continuous_const).mul (continuous_snd.sub continuous_const)).continuousOn) ?_
    intro q hq
    obtain ⟨d1, d2⟩ := hden q.1 hq.1 q.2 hq.2
    refine mul_ne_zero (fun h => ?_) (fun h => ?_)
    · rw [h, norm_zero] at d1; linarith
    · rw [h, norm_zero] at d2; linarith
  have hnorm := e64_t6_norm (F := fun a b => Ψ (a, b) v / ((a - P.1) * (b - P.2))) hR hFc
  have hpt : ∀ θ : ℝ × ℝ, ‖Ψ (circleMap 0 R θ.1, circleMap 0 R θ.2) v /
      ((circleMap 0 R θ.1 - P.1) * (circleMap 0 R θ.2 - P.2))‖ ≤ (1 / (R - r) ^ 2) * Φ' (θ, v) := by
    intro θ
    obtain ⟨d1, d2⟩ := hden _ (circleMap_mem_sphere 0 hR.le θ.1) _ (circleMap_mem_sphere 0 hR.le θ.2)
    have hRr : 0 < R - r := by linarith
    rw [norm_div, norm_mul, div_eq_mul_inv, mul_comm]
    refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
    rw [one_div, sq]
    exact inv_anti₀ (by positivity) (mul_le_mul d1 d2 hRr.le (norm_nonneg _))
  obtain ⟨Bv, hBv⟩ := ((isCompact_closedBall (0 : ℂ) R).prod (isCompact_closedBall (0 : ℂ) R)).exists_bound_of_continuousOn hcv
  have hΦθ : Integrable (fun θ : ℝ × ℝ => Φ' (θ, v)) (ν'.prod ν') := by
    have hcont : Continuous fun θ : ℝ × ℝ => Φ' (θ, v) := by
      have := hcv.comp_continuous (((continuous_circleMap 0 R).comp continuous_fst).prodMk
        ((continuous_circleMap 0 R).comp continuous_snd)) (fun θ => ⟨hcm θ.1, hcm θ.2⟩)
      exact this.norm
    refine (integrable_const Bv).mono' hcont.aestronglyMeasurable (Eventually.of_forall fun θ => ?_)
    rw [Real.norm_of_nonneg (norm_nonneg _)]
    exact hBv _ ⟨hcm θ.1, hcm θ.2⟩
  have hmono : ∫ θ, ‖Ψ (circleMap 0 R θ.1, circleMap 0 R θ.2) v /
        ((circleMap 0 R θ.1 - P.1) * (circleMap 0 R θ.2 - P.2))‖ ∂(ν'.prod ν') ≤
      ∫ θ, (1 / (R - r) ^ 2) * Φ' (θ, v) ∂(ν'.prod ν') :=
    integral_mono_of_nonneg (Eventually.of_forall fun θ => norm_nonneg _) (hΦθ.const_mul _)
      (Eventually.of_forall hpt)
  rw [integral_const_mul] at hmono
  beta_reduce at hnorm
  calc ‖((2 * π * I)⁻¹ : ℂ) ^ 2‖ * ‖∮ a in C(0, R), ∮ b in C(0, R), Ψ (a, b) v / ((a - P.1) * (b - P.2))‖
      ≤ ‖((2 * π * I)⁻¹ : ℂ) ^ 2‖ * (R ^ 2 * ((1 / (R - r) ^ 2) * ∫ θ, Φ' (θ, v) ∂(ν'.prod ν'))) :=
        mul_le_mul_of_nonneg_left (hnorm.trans (mul_le_mul_of_nonneg_left hmono (by positivity))) (norm_nonneg _)
    _ = C * ∫ θ, Φ' (θ, v) ∂(ν'.prod ν') := by rw [hC]; ring

/-- **(B2)** `[W2]` **Differentiation of `J` under the integral sign at `ε = 0`.** `J` is differentiable at `0` and
`∂_ε J(0)`, `∂_ε̄ J(0)` are the integrals of the pointwise derivatives. Route (E64, simpler: the integrand is not
singular in `u`, since `z̄ ∈ 𝕃`): the integrand `Ψ(P)(u) = μ(u) [dzW_P(u) dzW_P(z̄)/(W_P(u) - W_P(z̄))²]²` is holomorphic
in `P` (as `e64_phi_holo`, `e64_phi_cont`); an `L¹(𝕌)` bound uniform on a closed polydisc (E5 simplified:
`|μ| |(W_q)_u|² ≤ C J_{W_q}`, change of variables `ζ = W_q(u)`, `|ζ - W_q(z̄)| ≥ η` uniformly, `∫_{|ζ - b| ≥ η} |ζ - b|⁻⁴`);
domination on a smaller polydisc (`e64_dominate`); then `e64_torus_dz` and `e64_torus_swap`. -/
theorem s71_J_deriv {μ ν φ ψ : ℂ → ℂ} (hμ : IsHarmonicU μ φ) (hν : IsHarmonicU ν ψ) {z : ℂ} (hz : z ∈ upperHalf) :
    DifferentiableAt ℝ (fun ε => ∫ u in upperHalf, μ u * kernelKbar (fun y => ε * ν y) u z ^ 2) 0 ∧
      dz (fun ε => ∫ u in upperHalf, μ u * kernelKbar (fun y => ε * ν y) u z ^ 2) 0 =
        ∫ u in upperHalf, dz (fun e => μ u * kernelKbar (fun y => e * ν y) u z ^ 2) 0 ∧
      dzbar (fun ε => ∫ u in upperHalf, μ u * kernelKbar (fun y => ε * ν y) u z ^ 2) 0 =
        ∫ u in upperHalf, dzbar (fun e => μ u * kernelKbar (fun y => e * ν y) u z ^ 2) 0 := by
  -- data
  obtain ⟨Mμ, hMμ, hμb⟩ := harmonicU_bounded hμ
  have hμc := harmonicU_continuousOn hμ
  obtain ⟨k, hk, hνbd⟩ := harmonicU_bounded hν
  have hU := measurableSet_upperHalf_aux
  have hνm : AEStronglyMeasurable ν (volume.restrict upperHalf) :=
    (harmonicU_continuousOn hν).aestronglyMeasurable hU
  have hνk : IsBeltramiCoeff ν upperHalf k := ⟨hνm, (ae_restrict_mem hU).mono fun u hu => hνbd u hu⟩
  have hνs := wr_isHarmonicU_contDiffOn hν
  set c0 : ℂ := ((2 * π * I)⁻¹) ^ 2 with hc0
  obtain ⟨W, hW⟩ : ∃ W : ℂ × ℂ → ℂ → ℂ, W = fun P => normalizedSolution fun u =>
      P.1 * (if 0 < u.im then ν u else 0) + P.2 * (if u.im < 0 then conj (ν (conj u)) else 0) := ⟨_, rfl⟩
  obtain ⟨Ψ, hΨ⟩ : ∃ Ψ : ℂ × ℂ → ℂ → ℂ,
      Ψ = fun P u => μ u * (dz (W P) u * dz (W P) (conj z) / (W P u - W P (conj z)) ^ 2) ^ 2 := ⟨_, rfl⟩
  set R : ℝ := 1 / (k + 1) with hRd
  have hR : 0 < R := by positivity
  have hRk : R * k < 1 := by
    rw [hRd, div_mul_eq_mul_div, one_mul, div_lt_one (by positivity)]; linarith
  set r : ℝ := R / 2 with hrd
  have hr : 0 < r := by positivity
  have hrR : r < R := by linarith
  have hrk : r * k < 1 := lt_of_le_of_lt (mul_le_mul_of_nonneg_right hrR.le hk) hRk
  set T := sphere (0 : ℂ) r ×ˢ sphere (0 : ℂ) r with hTd
  set D := closedBall (0 : ℂ) r ×ˢ closedBall (0 : ℂ) r with hDd
  have hTD : T ⊆ D := prod_mono sphere_subset_closedBall sphere_subset_closedBall
  have hTne : ∀ q ∈ T, q.1 ≠ 0 ∧ q.2 ≠ 0 := by
    intro q hq
    have h1 : ‖q.1‖ = r := by simpa using hq.1
    have h2 : ‖q.2‖ = r := by simpa using hq.2
    exact ⟨fun h => by rw [h, norm_zero] at h1; linarith, fun h => by rw [h, norm_zero] at h2; linarith⟩
  have hcΨ := s71_b2_cont hk hνk hνs hμc hz hrk hW hΨ
  have hcv : ∀ u ∈ upperHalf, ContinuousOn (fun q : ℂ × ℂ => Ψ q u) D := by
    intro u hu
    have h := hcΨ.comp (continuous_id.prodMk continuous_const).continuousOn
      (fun q (hq : q ∈ D) => (⟨hq, hu⟩ : (q, u) ∈ (closedBall (0 : ℂ) r ×ˢ closedBall (0 : ℂ) r) ×ˢ upperHalf))
    simpa only [Function.comp_def, id] using h
  -- the pointwise Cauchy formula
  have hcauchy : ∀ u ∈ upperHalf, ∀ P ∈ ball (0 : ℂ) r ×ˢ ball (0 : ℂ) r,
      Ψ P u = c0 * ∮ a in C(0, r), ∮ b in C(0, r), Ψ (a, b) u / ((a - P.1) * (b - P.2)) := by
    intro u hu P hP
    obtain ⟨h1, h2⟩ := s71_b2_holo hk hνk hνs hz hrk hW hΨ hu
    exact wr_cauchy_bidisc (f := fun q => Ψ q u) (c := ((0, 0) : ℂ × ℂ)) hr hr (hcv u hu) h1 h2 hP
  have hTc : ∀ u ∈ upperHalf, ContinuousOn (fun q : ℂ × ℂ => Ψ q u) T := fun u hu => (hcv u hu).mono hTD
  -- the pointwise derivatives as torus coefficients
  have hpw : ∀ u ∈ upperHalf,
      dz (fun e => μ u * kernelKbar (fun y => e * ν y) u z ^ 2) 0 =
          c0 * ∮ a in C(0, r), ∮ b in C(0, r), Ψ (a, b) u / (a ^ 2 * b) ∧
        dzbar (fun e => μ u * kernelKbar (fun y => e * ν y) u z ^ 2) 0 =
          c0 * ∮ a in C(0, r), ∮ b in C(0, r), Ψ (a, b) u / (a * b ^ 2) := by
    intro u hu
    obtain ⟨-, h1, h2⟩ := s71_b2_torus_d (G := fun q => Ψ q u) (g := fun e => μ u * kernelKbar (fun y => e * ν y) u z ^ 2)
      hr (hTc u hu) (by
        filter_upwards [ball_mem_nhds (0 : ℂ) hr] with ε hε
        have hεr : ‖ε‖ < r := by simpa using hε
        have hεk : ‖ε‖ * k < 1 := lt_of_le_of_lt (mul_le_mul_of_nonneg_right hεr.le hk) hrk
        show μ u * kernelKbar (fun y => ε * ν y) u z ^ 2 = _
        rw [← s71_b2_diag hk hνk hW hΨ hεk u,
          hcauchy u hu (ε, conj ε) ⟨by simpa using hεr, by simpa [RCLike.norm_conj] using hεr⟩])
    exact ⟨h1, h2⟩
  -- domination, continuity and the Cauchy formula of `I(P) = ∫_𝕌 Ψ(P)`
  obtain ⟨g, hg, hgb⟩ := s71_b2_dom hk hνk hνs hμc hMμ hμb hz hr hrR hRk hW hΨ
  set Iq : ℂ × ℂ → ℂ := fun q => ∫ u in upperHalf, Ψ q u with hIq
  obtain ⟨M, hM⟩ := s71_b2_L1 hk hνk hνs hμc hMμ hμb hz hrk hW hΨ
  have hIc : ContinuousOn Iq D := by
    refine continuousOn_of_dominated (bound := g) (fun P hP => (hM P hP).1.aestronglyMeasurable)
      (fun P hP => ?_) hg ?_
    · filter_upwards [ae_restrict_mem hU] with v hv
      exact hgb P hP v hv
    · filter_upwards [ae_restrict_mem hU] with v hv
      exact hcv v hv
  have hswap : ∀ K : ℂ × ℂ → ℂ, ContinuousOn K T →
      IntegrableOn (fun u => ∮ a in C(0, r), ∮ b in C(0, r), K (a, b) * Ψ (a, b) u) upperHalf ∧
        ∫ u in upperHalf, (∮ a in C(0, r), ∮ b in C(0, r), K (a, b) * Ψ (a, b) u) =
          ∮ a in C(0, r), ∮ b in C(0, r), K (a, b) * Iq (a, b) := by
    intro K hK
    have hc : ContinuousOn (fun p : (ℂ × ℂ) × ℂ => Ψ p.1 p.2) (T ×ˢ upperHalf) :=
      hcΨ.mono (prod_mono hTD subset_rfl)
    exact e64_torus_swap hU hr hK hc hg fun q hq v hv => hgb q (hTD hq) v hv
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
  have hIcauchy : ∀ P ∈ ball (0 : ℂ) r ×ˢ ball (0 : ℂ) r,
      Iq P = c0 * ∮ a in C(0, r), ∮ b in C(0, r), 1 / ((a - P.1) * (b - P.2)) * Iq (a, b) := by
    intro P hP
    obtain ⟨-, hsw⟩ := hswap (fun q => 1 / ((q.1 - P.1) * (q.2 - P.2))) (hKP P hP)
    rw [← hsw, ← integral_const_mul]
    refine setIntegral_congr_fun hU fun v hv => ?_
    rw [hcauchy v hv P hP]
    congr 1
    refine e64_torus_congr hr fun a _ b _ => ?_
    ring
  -- `J` on a neighbourhood of `0`
  have hJ : ∀ᶠ ε in 𝓝 (0 : ℂ), (∫ u in upperHalf, μ u * kernelKbar (fun y => ε * ν y) u z ^ 2) =
      c0 * ∮ a in C(0, r), ∮ b in C(0, r), Iq (a, b) / ((a - ε) * (b - conj ε)) := by
    filter_upwards [ball_mem_nhds (0 : ℂ) hr] with ε hε
    have hεr : ‖ε‖ < r := by simpa using hε
    have hεk : ‖ε‖ * k < 1 := lt_of_le_of_lt (mul_le_mul_of_nonneg_right hεr.le hk) hrk
    have hPin : (ε, conj ε) ∈ ball (0 : ℂ) r ×ˢ ball (0 : ℂ) r :=
      ⟨by simpa using hεr, by simpa [RCLike.norm_conj] using hεr⟩
    have e1 : (∫ u in upperHalf, μ u * kernelKbar (fun y => ε * ν y) u z ^ 2) = Iq (ε, conj ε) :=
      setIntegral_congr_fun hU fun u _ => (s71_b2_diag hk hνk hW hΨ hεk u).symm
    rw [e1, hIcauchy _ hPin]
    congr 1
    refine e64_torus_congr hr fun a _ b _ => ?_
    simp only
    ring
  obtain ⟨hdiff, hdz, hdzb⟩ := s71_b2_torus_d hr (hIc.mono hTD) hJ
  have hKab : ContinuousOn (fun q : ℂ × ℂ => 1 / (q.1 ^ 2 * q.2)) T :=
    continuousOn_const.div ((continuous_fst.pow 2).mul continuous_snd).continuousOn fun q hq =>
      mul_ne_zero (pow_ne_zero _ (hTne q hq).1) (hTne q hq).2
  have hKab' : ContinuousOn (fun q : ℂ × ℂ => 1 / (q.1 * q.2 ^ 2)) T :=
    continuousOn_const.div (continuous_fst.mul (continuous_snd.pow 2)).continuousOn fun q hq =>
      mul_ne_zero (hTne q hq).1 (pow_ne_zero _ (hTne q hq).2)
  refine ⟨hdiff, ?_, ?_⟩
  · rw [hdz]
    obtain ⟨-, hsw⟩ := hswap _ hKab
    rw [setIntegral_congr_fun hU fun u hu => (hpw u hu).1, integral_const_mul]
    have e1 : (∫ u in upperHalf, ∮ a in C(0, r), ∮ b in C(0, r), Ψ (a, b) u / (a ^ 2 * b)) =
        ∫ u in upperHalf, ∮ a in C(0, r), ∮ b in C(0, r), 1 / (a ^ 2 * b) * Ψ (a, b) u :=
      integral_congr_ae (Eventually.of_forall fun u => e64_torus_congr hr fun a _ b _ => by ring)
    rw [e1, hsw]
    congr 1
    refine e64_torus_congr hr fun a _ b _ => ?_
    ring
  · rw [hdzb]
    obtain ⟨-, hsw⟩ := hswap _ hKab'
    rw [setIntegral_congr_fun hU fun u hu => (hpw u hu).2, integral_const_mul]
    have e2 : (∫ u in upperHalf, ∮ a in C(0, r), ∮ b in C(0, r), Ψ (a, b) u / (a * b ^ 2)) =
        ∫ u in upperHalf, ∮ a in C(0, r), ∮ b in C(0, r), 1 / (a * b ^ 2) * Ψ (a, b) u :=
      integral_congr_ae (Eventually.of_forall fun u => e64_torus_congr hr fun a _ b _ => by ring)
    rw [e2, hsw]
    congr 1
    refine e64_torus_congr hr fun a _ b _ => ?_
    ring

/-- **(B3)** `[W1]` **Quotient.** `∂Q(0) = (12/π) ∂J(0)/ρ(z)` for `∂ = ∂_ε, ∂_ε̄`. Route: `Q = (12/π) J/ρ^{εν}(z)` near
`ε = 0` (`s71_eq_7_1`); `J` and `ρ^{εν}(z)` are differentiable at `0` (B2; B1 with `eq_6_1`); `ρ^{0}(z) ≠ 0` (A1);
`∂_ε ρ^{εν}(z)|₀ = 0` (`lemma_6_1`), and `∂_ε̄ ρ^{εν}(z)|₀ = \overline{∂_ε ρ^{εν}(z)|₀} = 0` since `ρ^{εν}(z)` is real. -/
theorem s71_Q_quot {μ ν φ ψ : ℂ → ℂ} (hμ : IsHarmonicU μ φ) (hν : IsHarmonicU ν ψ) {z : ℂ} (hz : z ∈ upperHalf) :
    dz (fun ε => QfunU μ (fun u => ε * ν u) z) 0 =
        12 / π * dz (fun ε => ∫ u in upperHalf, μ u * kernelKbar (fun y => ε * ν y) u z ^ 2) 0 / rhoVar ν 0 z ∧
      dzbar (fun ε => QfunU μ (fun u => ε * ν u) z) 0 =
        12 / π * dzbar (fun ε => ∫ u in upperHalf, μ u * kernelKbar (fun y => ε * ν y) u z ^ 2) 0 / rhoVar ν 0 z := by
  obtain ⟨M, hM0, hνb, -⟩ := s71_harm_setup hν
  have hzim : 0 < z.im := hz
  have hz0 : z - conj z ≠ 0 := by
    intro h
    have := congrArg Complex.im h
    rw [Complex.sub_im, Complex.conj_im, Complex.zero_im] at this
    linarith
  obtain ⟨hJd, -, -⟩ := s71_J_deriv hμ hν hz
  set J : ℂ → ℂ := fun ε => ∫ u in upperHalf, μ u * kernelKbar (fun y => ε * ν y) u z ^ 2 with hJdef
  set R : ℂ → ℂ := fun ε => rhoVar ν ε z with hRdef
  have hRe : R = fun ε => -4 * kernelKbar (fun u => ε * ν u) z z := funext fun ε => eq_6_1 ν ε z
  have hRd : DifferentiableAt ℝ R 0 := by
    rw [hRe]; exact (s71_K_diffAt hν hz hz).const_mul (-4)
  have hR0 : R 0 ≠ 0 := by
    show rhoVar ν 0 z ≠ 0
    rw [s71_rho0]
    exact div_ne_zero (by norm_num) (pow_ne_zero 2 hz0)
  have hRi : DifferentiableAt ℝ (fun ε => (R ε)⁻¹) 0 := hRd.inv hR0
  -- `Q = (12/π) J R⁻¹` near `0`
  have hev : (fun ε => QfunU μ (fun u => ε * ν u) z) =ᶠ[𝓝 0] fun ε => 12 / π * J ε * (R ε)⁻¹ := by
    have h1 : {ε : ℂ | ‖ε‖ * M < 1} ∈ 𝓝 (0 : ℂ) :=
      (isOpen_lt (continuous_norm.mul continuous_const) continuous_const).mem_nhds (by simp)
    filter_upwards [h1, hRd.continuousAt.eventually_ne hR0] with ε hε hRε
    have h := s71_eq_7_1 hμ hν hM0 hνb hε hz
    show QfunU μ (fun u => ε * ν u) z = 12 / π * J ε * (R ε)⁻¹
    rw [hJdef, hRdef]
    beta_reduce
    have hRε' : rhoVar ν ε z ≠ 0 := hRε
    rw [← h]
    field_simp
  have hJ12 : DifferentiableAt ℝ (fun ε => 12 / π * J ε) 0 := hJd.const_mul _
  -- `∂ρ^{εν}(z)|₀ = 0`
  have hdR : dz R 0 = 0 := lemma_6_1 hν hz
  have hRr : (fun ε => conj (R ε)) = R := funext fun ε => s71_rho_real ν ε z
  have hdbR : dzbar R 0 = 0 := by
    have h := dzbar_conj hRd
    rw [hRr, hdR, map_zero] at h
    exact h
  have hRir : (fun ε => conj ((R ε)⁻¹)) = fun ε => (R ε)⁻¹ := funext fun ε => by
    rw [map_inv₀, s71_rho_real]
  have hdRi : dz (fun ε => (R ε)⁻¹) 0 = 0 := by
    rw [wp_dz_inv hRd hR0, hdR, mul_zero]
  have hdbRi : dzbar (fun ε => (R ε)⁻¹) 0 = 0 := by
    have h := dzbar_conj hRi
    rw [hRir, hdRi, map_zero] at h
    exact h
  have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 Real.pi_ne_zero
  constructor
  · rw [wp_dz_congr_of_eventuallyEq hev, e64_t9_dz_mul hJ12 hRi, hdRi, wp_dz_const_mul hJd]
    show 12 / π * J 0 * 0 + (R 0)⁻¹ * (12 / π * dz J 0) = 12 / π * dz J 0 / R 0
    field_simp
    ring
  · have hevb : dzbar (fun ε => QfunU μ (fun u => ε * ν u) z) 0 =
        dzbar (fun ε => 12 / π * J ε * (R ε)⁻¹) 0 := by
      simp only [dzbar, hev.fderiv_eq]
    rw [hevb, s71_dzbar_mul hJ12 hRi, hdbRi, wp_dzbar_const_mul hJd]
    show 12 / π * J 0 * 0 + (R 0)⁻¹ * (12 / π * dzbar J 0) = 12 / π * dzbar J 0 / R 0
    field_simp
    ring

/-- **(B4)** `[W1]` **Pointwise derivatives** (`eq_1_25` at `ε = 0`, `e64_t9_K0`, `e64_t9_dz_mul`, B1): for `u ∈ 𝕌`,
`∂_ε [μ(u) K_{εν}(u, z̄)²]₀ = -(2/π) μ(u)/(u - z̄)² PV ∬ ν(v)/((u - v)²(v - z̄)²)` and
`∂_ε̄ [μ(u) K_{εν}(u, z̄)²]₀ = -(2/π) μ(u)/(u - z̄)² PV ∬ \overline{ν(v)}/((u - v̄)²(v̄ - z̄)²)`. -/
theorem s71_pointwise {μ ν φ ψ : ℂ → ℂ} (hμ : IsHarmonicU μ φ) (hν : IsHarmonicU ν ψ) {z : ℂ} (hz : z ∈ upperHalf)
    {u : ℂ} (hu : u ∈ upperHalf) :
    dz (fun e => μ u * kernelKbar (fun y => e * ν y) u z ^ 2) 0 =
        -(2 / π) * (μ u / (u - conj z) ^ 2 * pv2 (fun v => ν v / ((u - v) ^ 2 * (v - conj z) ^ 2)) u z) ∧
      dzbar (fun e => μ u * kernelKbar (fun y => e * ν y) u z ^ 2) 0 =
        -(2 / π) * (μ u / (u - conj z) ^ 2 *
          pv2 (fun v => conj (ν v) / ((u - conj v) ^ 2 * (conj v - conj z) ^ 2)) u z) := by
  obtain ⟨M, hM0, hνb, hνs⟩ := s71_harm_setup hν
  have hε0 : ‖(0 : ℂ)‖ * M < 1 := by simp
  have hK := s71_K_diffAt hν hu hz
  have hK2 : DifferentiableAt ℝ (fun e => kernelKbar (fun y => e * ν y) u z ^ 2) 0 := hK.pow 2
  obtain ⟨d1, d2⟩ := e124_eq_1_25 hM0 hνb hνs hε0 hu hz
  have hK0 : kernelKbar (fun y => (0 : ℂ) * ν y) u z = 1 / (u - conj z) ^ 2 := (e64_t9_K0 ν u z).2.1
  have e1 : (fun v => ν v * kernelK (fun y => (0 : ℂ) * ν y) u v * kernelKbar (fun y => (0 : ℂ) * ν y) v z) =
      fun v => ν v / ((u - v) ^ 2 * (v - conj z) ^ 2) := by
    funext v
    rw [(e64_t9_K0 ν u v).1, (e64_t9_K0 ν v z).2.1, mul_assoc, one_div_mul_one_div, mul_one_div]
  have e2 : (fun v => conj (ν v) * kernelKbar (fun y => (0 : ℂ) * ν y) u v *
      kernelKbarbar (fun y => (0 : ℂ) * ν y) v z) =
      fun v => conj (ν v) / ((u - conj v) ^ 2 * (conj v - conj z) ^ 2) := by
    funext v
    rw [(e64_t9_K0 ν u v).2.1, (e64_t9_K0 ν v z).2.2, mul_assoc, one_div_mul_one_div, mul_one_div]
  constructor
  · rw [wp_dz_const_mul hK2, wp_dz_pow hK 2, d1, e1]
    beta_reduce
    rw [hK0]
    push_cast
    ring
  · rw [wp_dzbar_const_mul hK2, wp_dzbar_pow hK 2, d2, e2]
    beta_reduce
    rw [hK0]
    push_cast
    ring

/-! ### (7.2): from `∫_u PV_v` to the symmetric cut-off `|u - v| ≥ δ` -/

/-- Linear growth of `|v - u|` off a disc around `u`. -/
theorem s71_sep2 {u v : ℂ} {r : ℝ} (hr : 0 < r) (hv : r ≤ ‖v - u‖) :
    r / (1 + ‖u‖ + r) * (1 + ‖v‖) ≤ ‖v - u‖ := by
  have h2 : ‖v‖ - ‖u‖ ≤ ‖v - u‖ := by have := norm_sub_norm_le v u; linarith
  rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
  rcases le_total ‖v‖ (‖u‖ + r) with h | h
  · nlinarith [mul_nonneg hr.le (sub_nonneg.mpr h),
      mul_le_mul_of_nonneg_right hv (by positivity : (0 : ℝ) ≤ 1 + ‖u‖ + r), norm_nonneg u]
  · nlinarith [mul_nonneg (sub_nonneg.mpr h) (by positivity : (0 : ℝ) ≤ 1 + ‖u‖),
      mul_le_mul_of_nonneg_right h2 (by positivity : (0 : ℝ) ≤ 1 + ‖u‖ + r)]

/-- **One-point principal value of `g(v)/(v - u)²`** for `g` Lipschitz at `u` (model `g(u)/(v - u)²` with mean zero on
annuli, `e124p_model_zero` with `κ = 0`; the remainder is `O(1/|v - u|)`). -/
theorem s71_pv_exists {g : ℂ → ℂ} {u : ℂ} {r L : ℝ} (hr : 0 < r) (hball : ball u r ⊆ upperHalf)
    (hgc : ContinuousOn g (ball u r)) (hgL : ∀ v ∈ ball u r, ‖g v - g u‖ ≤ L * ‖v - u‖)
    (hfar : IntegrableOn (fun v => g v / (v - u) ^ 2) (upperHalf \ ball u r)) :
    (∀ δ : ℝ, 0 < δ → IntegrableOn (fun v => g v / (v - u) ^ 2) (upperHalf \ ball u δ)) ∧
      ∃ Lim : ℂ, Tendsto (fun δ : ℝ => ∫ v in upperHalf \ ball u δ, g v / (v - u) ^ 2) (𝓝[>] 0) (𝓝 Lim) := by
  have hcm : Measurable (conj : ℂ → ℂ) := Complex.continuous_conj.measurable
  set F : ℂ → ℂ := fun v => g v / (v - u) ^ 2 with hFd
  set rem : ℂ → ℂ := fun v => F v - g u * ((v - u + 0 * conj (v - u)) ^ 2)⁻¹ with hremd
  have hgm : AEStronglyMeasurable g (volume.restrict (ball u r)) := hgc.aestronglyMeasurable measurableSet_ball
  have hFm : AEStronglyMeasurable F (volume.restrict (ball u r)) :=
    hgm.mul (Measurable.aestronglyMeasurable (by fun_prop))
  have hrem : IntegrableOn rem (ball u r) := by
    have hmod : Measurable fun v => g u * ((v - u + 0 * conj (v - u)) ^ 2)⁻¹ := by fun_prop
    refine ((e124p_invnorm_int u r).const_mul L).mono' (hFm.sub hmod.aestronglyMeasurable) ?_
    filter_upwards [ae_restrict_mem measurableSet_ball,
      ae_restrict_of_ae (compl_mem_ae_iff.mpr (measure_singleton u))] with v hv hvu
    have hvu' : v - u ≠ 0 := sub_ne_zero.mpr hvu
    have hp : 0 < ‖v - u‖ := norm_pos_iff.mpr hvu'
    have e : rem v = (g v - g u) / (v - u) ^ 2 := by
      simp only [hremd, hFd, zero_mul, add_zero]
      field_simp
    rw [e, norm_div, norm_pow]
    calc ‖g v - g u‖ / ‖v - u‖ ^ 2 ≤ L * ‖v - u‖ / ‖v - u‖ ^ 2 :=
          div_le_div_of_nonneg_right (hgL v hv) (by positivity)
      _ = L * ‖v - u‖⁻¹ := by field_simp
  have hann : ∀ δ : ℝ, 0 < δ → δ ≤ r → IntegrableOn F (ball u r \ ball u δ) := by
    intro δ hδ hδr
    obtain ⟨hmi, -⟩ := e124p_model_zero (g u) 0 u (by simp) hδ hδr
    have h := (hrem.mono_set sdiff_subset).add hmi
    refine h.congr_fun (fun v _ => ?_) (measurableSet_ball.diff measurableSet_ball)
    rw [Pi.add_apply]
    simp only [hremd]
    ring
  have hsplit : ∀ δ : ℝ, δ ≤ r → upperHalf \ ball u δ = (upperHalf \ ball u r) ∪ (ball u r \ ball u δ) := by
    intro δ hδr
    ext v
    constructor
    · rintro ⟨hvU, hvδ⟩
      by_cases hvr : v ∈ ball u r
      · exact Or.inr ⟨hvr, hvδ⟩
      · exact Or.inl ⟨hvU, hvr⟩
    · rintro (⟨hvU, hvr⟩ | ⟨hvr, hvδ⟩)
      · exact ⟨hvU, fun h => hvr (ball_subset_ball hδr h)⟩
      · exact ⟨hball hvr, hvδ⟩
  have hint : ∀ δ : ℝ, 0 < δ → IntegrableOn F (upperHalf \ ball u δ) := by
    intro δ hδ
    rcases le_total δ r with h | h
    · rw [hsplit δ h]; exact hfar.union (hann δ hδ h)
    · exact hfar.mono_set (sdiff_subset_sdiff_right (ball_subset_ball h))
  refine ⟨hint, (∫ v in upperHalf \ ball u r, F v) + ∫ v in ball u r, rem v, ?_⟩
  have hT := e124p_rem_tendsto hrem (X := fun δ => ball u δ) (fun δ => measurableSet_ball) (fun v hv => by
    have hp : 0 < ‖v - u‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hv)
    filter_upwards [Ioo_mem_nhdsGT hp] with δ hδ
    rw [mem_ball, dist_eq_norm, not_lt]
    exact hδ.2.le)
  refine (tendsto_const_nhds.add hT).congr' ?_
  filter_upwards [Ioo_mem_nhdsGT hr] with δ hδ
  have hdisj : Disjoint (upperHalf \ ball u r) (ball u r \ ball u δ) :=
    disjoint_left.mpr fun v h1 h2 => h1.2 h2.1
  obtain ⟨hmi, hm0⟩ := e124p_model_zero (g u) 0 u (by simp) hδ.1 hδ.2.le
  have hFa := hann δ hδ.1 hδ.2.le
  show _ = ∫ v in upperHalf \ ball u δ, F v
  rw [hsplit δ hδ.2.le, setIntegral_union hdisj (measurableSet_ball.diff measurableSet_ball) hfar hFa]
  congr 1
  have e : ∫ v in ball u r \ ball u δ, rem v =
      (∫ v in ball u r \ ball u δ, F v) - ∫ v in ball u r \ ball u δ, g u * ((v - u + 0 * conj (v - u)) ^ 2)⁻¹ :=
    integral_sub hFa hmi
  rw [e, hm0, sub_zero]

/-- **(C1)** `[W1]` For `u ∈ 𝕌` the one-disc truncations in `v` converge to the `pv2` value (the integrand is
`O(|v - u|⁻²)` with mean-zero model `c/(v - u)²` (`e124p_model_zero`, `κ = 0`); the extra disc `B(z, δ)` of `pv2`
carries a bounded integrand off `u = z`, and for `u = z` the two discs coincide). -/
theorem s71_v_trunc {ν ψ : ℂ → ℂ} (hν : IsHarmonicU ν ψ) {z : ℂ} (hz : z ∈ upperHalf) {u : ℂ} (hu : u ∈ upperHalf) :
    Tendsto (fun δ : ℝ => ∫ v in upperHalf \ ball u δ, ν v / ((u - v) ^ 2 * (v - conj z) ^ 2)) (𝓝[>] 0)
      (𝓝 (pv2 (fun v => ν v / ((u - v) ^ 2 * (v - conj z) ^ 2)) u z)) := by
  obtain ⟨M, hM0, hM⟩ := harmonicU_bounded hν
  have hUo : IsOpen upperHalf := isOpen_lt continuous_const Complex.continuous_im
  have hU := measurableSet_upperHalf_aux
  have hzim : 0 < z.im := hz
  have huim : 0 < u.im := hu
  have hνs := wr_isHarmonicU_contDiffOn hν
  have hνc := harmonicU_continuousOn hν
  have hden : ∀ v ∈ upperHalf, v - conj z ≠ 0 := fun v hv => eq_7_4_sub_conj_ne_zero hv hz
  set g : ℂ → ℂ := fun v => ν v / (v - conj z) ^ 2 with hgd
  have hfeq : (fun v => ν v / ((u - v) ^ 2 * (v - conj z) ^ 2)) = fun v => g v / (v - u) ^ 2 := by
    funext v
    rw [hgd, div_div, show (u - v) ^ 2 = (v - u) ^ 2 by ring, mul_comm]
  -- `g` is `C¹` at `u`
  have hcj : ContDiff ℝ 1 (fun v : ℂ => conj v) := Complex.conjCLE.contDiff
  have hgs : ContDiffOn ℝ 1 g upperHalf := by
    have h1 : ContDiffOn ℝ 1 ν upperHalf := hνs.of_le (by exact_mod_cast le_top)
    have h2 : ContDiffOn ℝ 1 (fun v : ℂ => (v - conj z) ^ 2) upperHalf :=
      ((contDiff_id.sub contDiff_const).pow 2).contDiffOn
    refine (h1.mul (h2.inv fun v hv => pow_ne_zero 2 (hden v hv))).congr fun v _ => ?_
    simp only [hgd, Pi.inv_apply, div_eq_mul_inv]
  obtain ⟨ρ, hρ, L, -, hL⟩ := e124p_lip (hgs.contDiffAt (hUo.mem_nhds hu))
  set r := min ρ (u.im / 2) with hrd
  have hr : 0 < r := lt_min hρ (half_pos huim)
  have hball : ball u r ⊆ upperHalf := fun v hv => by
    show 0 < v.im
    have h1 : |v.im - u.im| ≤ ‖v - u‖ := by rw [← Complex.sub_im]; exact Complex.abs_im_le_norm _
    rw [mem_ball, dist_eq_norm] at hv
    have := (abs_le.mp (h1.trans (hv.trans_le (min_le_right _ _)).le)).1
    linarith
  have hgc : ContinuousOn g (ball u r) := hgs.continuousOn.mono hball
  have hgL : ∀ v ∈ ball u r, ‖g v - g u‖ ≤ L * ‖v - u‖ := fun v hv =>
    hL v (ball_subset_ball (min_le_left _ _) hv) u (mem_ball_self hρ)
  -- the far part is integrable (majorant `K (1 + |v|)⁻⁴`)
  set c1 := z.im / (1 + ‖z‖ + z.im) with hc1d
  set c2 := r / (1 + ‖u‖ + r) with hc2d
  have hc1 : 0 < c1 := by positivity
  have hc2 : 0 < c2 := by positivity
  have hfar : IntegrableOn (fun v => g v / (v - u) ^ 2) (upperHalf \ ball u r) := by
    have hmaj : Integrable (fun v : ℂ => M / (c1 ^ 2 * c2 ^ 2) * (1 + ‖v‖) ^ (-(4 : ℝ))) :=
      (integrable_one_add_norm (by rw [Complex.finrank_real_complex]; norm_num)).const_mul _
    have hgm : AEStronglyMeasurable (fun v => g v / (v - u) ^ 2) (volume.restrict (upperHalf \ ball u r)) := by
      have hνm : AEStronglyMeasurable ν (volume.restrict (upperHalf \ ball u r)) :=
        (hνc.mono sdiff_subset).aestronglyMeasurable (hU.diff measurableSet_ball)
      refine (hνm.mul (Measurable.aestronglyMeasurable (f := fun v : ℂ => ((v - conj z) ^ 2)⁻¹ * ((v - u) ^ 2)⁻¹)
        (by fun_prop))).congr (Eventually.of_forall fun v => ?_)
      simp only [hgd, div_eq_mul_inv, Pi.mul_apply]
      ring
    refine hmaj.integrableOn.mono' hgm ?_
    filter_upwards [ae_restrict_mem (hU.diff measurableSet_ball)] with v hv
    have hvim : 0 < v.im := hv.1
    have hvr : r ≤ ‖v - u‖ := by
      have := hv.2
      rwa [mem_ball, dist_eq_norm, not_lt] at this
    have h1 : c1 * (1 + ‖v‖) ≤ ‖v - conj z‖ :=
      e64_sep hzim (norm_nonneg z) hvim.le (by rw [Complex.conj_im]) (by rw [Complex.norm_conj])
    have h2 : c2 * (1 + ‖v‖) ≤ ‖v - u‖ := s71_sep2 hr hvr
    have ht : 0 < 1 + ‖v‖ := by positivity
    have hp : (1 + ‖v‖) ^ (-(4 : ℝ)) = ((1 + ‖v‖) ^ 4)⁻¹ := by
      rw [Real.rpow_neg ht.le, show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    rw [hp, hgd]
    simp only [norm_div, norm_pow]
    have hν1 : ‖ν v‖ ≤ M := hM v hv.1
    have hA : 0 < c1 * (1 + ‖v‖) := by positivity
    have hB : 0 < c2 * (1 + ‖v‖) := by positivity
    calc ‖ν v‖ / ‖v - conj z‖ ^ 2 / ‖v - u‖ ^ 2 ≤ M / (c1 * (1 + ‖v‖)) ^ 2 / (c2 * (1 + ‖v‖)) ^ 2 := by
          gcongr
      _ = M / (c1 ^ 2 * c2 ^ 2) * ((1 + ‖v‖) ^ 4)⁻¹ := by field_simp
  obtain ⟨hi, Lim, hT⟩ := s71_pv_exists hr hball hgc hgL hfar
  have h2 := e124a_pv1g (u := z) hT hi
  rw [hfeq]
  unfold pv2
  rw [h2.limUnder_eq]
  exact hT

/-- `|ψ(x)| ≤ C/(Im x)²` from `|(Im x)² ψ(x)| ≤ C`. -/
theorem s71c2_psi_bd {ψ : ℂ → ℂ} {C : ℝ} (hC : ∀ x ∈ upperHalf, ‖(x.im : ℂ) ^ 2 * ψ x‖ ≤ C) {x : ℂ}
    (hx : x ∈ upperHalf) : ‖ψ x‖ ≤ C / x.im ^ 2 := by
  have h0 : 0 < x.im := hx
  rw [le_div_iff₀ (by positivity)]
  have := hC x hx
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs] at this
  linarith [mul_comm (‖ψ x‖) (x.im ^ 2)]

/-- Cauchy estimate + mean value: `ψ` is `64C/(Im u)³`-Lipschitz on `B(u, Im u/2)`. -/
theorem s71c2_psi_lip {ψ : ℂ → ℂ} (hd : DifferentiableOn ℂ ψ upperHalf) {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ x ∈ upperHalf, ‖(x.im : ℂ) ^ 2 * ψ x‖ ≤ C) {u : ℂ} (hu : u ∈ upperHalf) {v : ℂ}
    (hv : v ∈ ball u (u.im / 2)) : ‖ψ v - ψ u‖ ≤ 64 * C / u.im ^ 3 * ‖v - u‖ := by
  have ht : 0 < u.im := hu
  have hsub : ∀ w ∈ ball u (u.im / 2), ∀ x : ℂ, ‖x - w‖ ≤ u.im / 4 → u.im / 4 ≤ x.im := by
    intro w hw x hx
    rw [mem_ball, dist_eq_norm] at hw
    have h1 := Complex.abs_im_le_norm (x - w)
    have h2 := Complex.abs_im_le_norm (w - u)
    rw [Complex.sub_im] at h1 h2
    linarith [(abs_le.1 h1).1, (abs_le.1 h2).1]
  refine Convex.norm_image_sub_le_of_norm_deriv_le (s := ball u (u.im / 2)) (fun w hw => ?_)
    (fun w hw => ?_) (convex_ball _ _) (mem_ball_self (by positivity)) hv
  · have := hsub w hw w (by simp; positivity)
    exact hd.differentiableAt (isOpen_upperHalf.mem_nhds (show 0 < w.im by linarith))
  · have hR : 0 < u.im / 4 := by positivity
    have hcl : DiffContOnCl ℂ ψ (ball w (u.im / 4)) := by
      apply DifferentiableOn.diffContOnCl
      rw [closure_ball w hR.ne']
      refine hd.mono (fun x hx => ?_)
      rw [mem_closedBall, dist_eq_norm] at hx
      have := hsub w hw x hx
      show 0 < x.im
      linarith
    have hb := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hR hcl
      (C := 16 * C / u.im ^ 2) (fun x hx => by
        rw [mem_sphere, dist_eq_norm] at hx
        have hxim := hsub w hw x hx.le
        have hx0 : 0 < x.im := by linarith
        refine (s71c2_psi_bd hC hx0).trans ?_
        rw [div_le_div_iff₀ (pow_pos hx0 2) (pow_pos ht 2)]
        have h4 : u.im ^ 2 ≤ 16 * x.im ^ 2 := by nlinarith
        nlinarith [mul_le_mul_of_nonneg_left h4 hC0])
    calc ‖deriv ψ w‖ ≤ 16 * C / u.im ^ 2 / (u.im / 4) := hb
      _ = 64 * C / u.im ^ 3 := by field_simp; ring

/-- `(x - x̄)²/2 = -2 (Im x)²`. -/
theorem s71c2_A (x : ℂ) : (x - conj x) ^ 2 / 2 = ((-2 * x.im ^ 2 : ℝ) : ℂ) := by
  rw [Complex.sub_conj]
  push_cast
  linear_combination (2 * (x.im : ℂ) ^ 2) * I_sq

/-- Lipschitz bound for `F(v) = ν(v)/(v - a)²` on `B(u, Im u/2)`, `ν = (v - v̄)²/2 · \overline{ψ(v)}`. -/
theorem s71c2_F_lip {ψ : ℂ → ℂ} (hd : DifferentiableOn ℂ ψ upperHalf) {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ x ∈ upperHalf, ‖(x.im : ℂ) ^ 2 * ψ x‖ ≤ C) {u a : ℂ} (hu : u ∈ upperHalf) (ha : u.im ≤ ‖u - a‖)
    {v : ℂ} (hv : v ∈ ball u (u.im / 2)) :
    ‖(v - conj v) ^ 2 / 2 * conj (ψ v) / (v - a) ^ 2 - (u - conj u) ^ 2 / 2 * conj (ψ u) / (u - a) ^ 2‖ ≤
      612 * C / (u.im * ‖u - a‖ ^ 2) * ‖v - u‖ := by
  have ht : 0 < u.im := hu
  set t := u.im with htd
  set B := ‖u - a‖ with hBd
  set d := ‖v - u‖ with hdd
  have hB : 0 < B := by linarith
  have hdv : d < t / 2 := by rw [mem_ball, dist_eq_norm] at hv; exact hv
  have hd0 : 0 ≤ d := norm_nonneg _
  have him : |v.im - t| ≤ d := by
    have := Complex.abs_im_le_norm (v - u)
    rwa [Complex.sub_im] at this
  have hv1 : t / 2 < v.im := by linarith [(abs_le.1 him).1]
  have hv2 : v.im ≤ t + d := by linarith [(abs_le.1 him).2]
  have hvU : v ∈ upperHalf := show 0 < v.im by linarith
  have hXv : ‖ψ v‖ ≤ 4 * C / t ^ 2 := by
    refine (s71c2_psi_bd hC hvU).trans ?_
    rw [div_le_div_iff₀ (pow_pos (show (0 : ℝ) < v.im by linarith) 2) (pow_pos ht 2)]
    have h4 : t ^ 2 ≤ 4 * v.im ^ 2 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left h4 hC0]
  have hXu : ‖ψ u‖ ≤ C / t ^ 2 := s71c2_psi_bd hC hu
  have hψl := s71c2_psi_lip hd hC0 hC hu hv
  have hva : B / 2 ≤ ‖v - a‖ := by
    have := norm_sub_le_norm_sub_add_norm_sub u v a
    rw [norm_sub_rev u v] at this
    linarith
  have hva0 : 0 < ‖v - a‖ := by linarith
  have hua0 : u - a ≠ 0 := norm_ne_zero_iff.mp hB.ne'
  have hva0' : v - a ≠ 0 := norm_ne_zero_iff.mp hva0.ne'
  have hYv : ‖((v - a) ^ 2)⁻¹‖ ≤ 4 / B ^ 2 := by
    rw [norm_inv, norm_pow, show 4 / B ^ 2 = ((B / 2) ^ 2)⁻¹ by field_simp; ring]
    exact inv_anti₀ (by positivity) (pow_le_pow_left₀ (by positivity) hva 2)
  have hYu : ‖((u - a) ^ 2)⁻¹‖ = (B ^ 2)⁻¹ := by rw [norm_inv, norm_pow]
  have hYd : ‖((v - a) ^ 2)⁻¹ - ((u - a) ^ 2)⁻¹‖ ≤ 10 * d / (t * B ^ 2) := by
    have he : ((v - a) ^ 2)⁻¹ - ((u - a) ^ 2)⁻¹ =
        (u - v) * (2 * (u - a) + (v - u)) * (((v - a) ^ 2)⁻¹ * ((u - a) ^ 2)⁻¹) := by
      field_simp
      ring
    have hs : ‖2 * (u - a) + (v - u)‖ ≤ 5 * B / 2 := by
      refine (norm_add_le _ _).trans ?_
      rw [norm_mul, show ‖(2 : ℂ)‖ = 2 by norm_num]
      linarith
    rw [he, norm_mul, norm_mul, norm_mul, norm_sub_rev u v, hYu]
    calc d * ‖2 * (u - a) + (v - u)‖ * (‖((v - a) ^ 2)⁻¹‖ * (B ^ 2)⁻¹)
        ≤ d * (5 * B / 2) * (4 / B ^ 2 * (B ^ 2)⁻¹) := by gcongr
      _ = 10 * d / (B * B ^ 2) := by field_simp; ring
      _ ≤ 10 * d / (t * B ^ 2) := by
        apply div_le_div_of_nonneg_left (by positivity) (by positivity)
        exact mul_le_mul_of_nonneg_right ha (by positivity)
  have hAd : ‖(v - conj v) ^ 2 / 2 - (u - conj u) ^ 2 / 2‖ ≤ 5 * t * d := by
    rw [s71c2_A, s71c2_A, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_le]
    constructor <;> nlinarith [(abs_le.1 him).1, (abs_le.1 him).2]
  have hAu : ‖(u - conj u) ^ 2 / 2‖ = 2 * t ^ 2 := by
    rw [s71c2_A, Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (by nlinarith)]
    ring
  have hsplit : (v - conj v) ^ 2 / 2 * conj (ψ v) / (v - a) ^ 2 - (u - conj u) ^ 2 / 2 * conj (ψ u) / (u - a) ^ 2 =
      ((v - conj v) ^ 2 / 2 - (u - conj u) ^ 2 / 2) * conj (ψ v) * ((v - a) ^ 2)⁻¹ +
        (u - conj u) ^ 2 / 2 * conj (ψ v - ψ u) * ((v - a) ^ 2)⁻¹ +
        (u - conj u) ^ 2 / 2 * conj (ψ u) * (((v - a) ^ 2)⁻¹ - ((u - a) ^ 2)⁻¹) := by
    rw [map_sub]
    simp only [div_eq_mul_inv]
    ring
  rw [hsplit]
  refine norm_add₃_le.trans ?_
  simp only [norm_mul, Complex.norm_conj]
  rw [hAu]
  calc ‖(v - conj v) ^ 2 / 2 - (u - conj u) ^ 2 / 2‖ * ‖ψ v‖ * ‖((v - a) ^ 2)⁻¹‖ +
        2 * t ^ 2 * ‖ψ v - ψ u‖ * ‖((v - a) ^ 2)⁻¹‖ + 2 * t ^ 2 * ‖ψ u‖ * ‖((v - a) ^ 2)⁻¹ - ((u - a) ^ 2)⁻¹‖
      ≤ 5 * t * d * (4 * C / t ^ 2) * (4 / B ^ 2) + 2 * t ^ 2 * (64 * C / t ^ 3 * d) * (4 / B ^ 2) +
        2 * t ^ 2 * (C / t ^ 2) * (10 * d / (t * B ^ 2)) := by gcongr
    _ = 612 * C / (t * B ^ 2) * d := by field_simp; ring

/-- `∫_{B(u, r)} |v - u|⁻¹ = 2πr`. -/
theorem s71c2_ball_inv (u : ℂ) {r : ℝ} (hr : 0 < r) : ∫ v in ball u r, ‖v - u‖⁻¹ = 2 * π * r := by
  rw [← integral_indicator measurableSet_ball]
  have he : (ball u r).indicator (fun v => ‖v - u‖⁻¹) = fun v => (Iio r).indicator (fun y : ℝ => y⁻¹) ‖v - u‖ := by
    funext v
    simp only [indicator, mem_ball, dist_eq_norm, mem_Iio]
  rw [he, integral_sub_right_eq_self (fun x : ℂ => (Iio r).indicator (fun y : ℝ => y⁻¹) ‖x‖) u,
    integral_fun_norm_addHaar, Complex.finrank_real_complex]
  have hb : volume.real (ball (0 : ℂ) 1) = π := by simp [Measure.real, Complex.volume_ball]
  rw [hb]
  have hc : EqOn (fun y : ℝ => y ^ (2 - 1) • (Iio r).indicator (fun y : ℝ => y⁻¹) y)
      ((Ioo 0 r).indicator fun _ => (1 : ℝ)) (Ioi 0) := by
    intro y hy
    have hy0 : (0 : ℝ) < y := hy
    by_cases hyr : y < r
    · simp only [indicator, mem_Iio, mem_Ioo, hyr, hy0, true_and, ite_true, show (2 : ℕ) - 1 = 1 from rfl, pow_one,
        smul_eq_mul]
      field_simp
    · simp [indicator, hyr]
  rw [setIntegral_congr_fun measurableSet_Ioi hc, setIntegral_indicator measurableSet_Ioo,
    Ioi_inter_Ioo, max_self]
  simp [hr.le]
  ring

/-- **Near part.** Model subtraction (`e124p_model_zero`, `κ = 0`) and the Lipschitz bound. -/
theorem s71c2_near {F : ℂ → ℂ} {u : ℂ} {r δ L : ℝ} (hδ : 0 < δ) (hδr : δ ≤ r) (hL0 : 0 ≤ L)
    (hL : ∀ v ∈ ball u r, ‖F v - F u‖ ≤ L * ‖v - u‖) (hm : AEStronglyMeasurable F (volume.restrict (ball u r))) :
    IntegrableOn (fun v => F v / (u - v) ^ 2) (ball u r \ ball u δ) ∧
      ‖∫ v in ball u r \ ball u δ, F v / (u - v) ^ 2‖ ≤ L * (2 * π * r) := by
  have hr : 0 < r := hδ.trans_le hδr
  have hA : MeasurableSet (ball u r \ ball u δ) := measurableSet_ball.diff measurableSet_ball
  obtain ⟨hmi, hm0⟩ := e124p_model_zero (F u) 0 u (by simp) hδ hδr
  have hinv := e124p_invnorm_int u r
  have hdm : AEStronglyMeasurable (fun v => F v / (u - v) ^ 2 - F u * ((v - u + 0 * conj (v - u)) ^ 2)⁻¹)
      (volume.restrict (ball u r \ ball u δ)) := by
    have h1 : AEStronglyMeasurable (fun v => F v * ((u - v) ^ 2)⁻¹) (volume.restrict (ball u r \ ball u δ)) :=
      (hm.mono_measure (Measure.restrict_mono sdiff_subset le_rfl)).mul
        (by fun_prop : Measurable fun v : ℂ => ((u - v) ^ 2)⁻¹).aestronglyMeasurable
    have h2 : Measurable fun v : ℂ => F u * ((v - u + 0 * conj (v - u)) ^ 2)⁻¹ := by fun_prop
    simpa only [div_eq_mul_inv, Pi.sub_def] using h1.sub h2.aestronglyMeasurable
  have hpt : ∀ v ∈ ball u r \ ball u δ,
      ‖F v / (u - v) ^ 2 - F u * ((v - u + 0 * conj (v - u)) ^ 2)⁻¹‖ ≤ L * ‖v - u‖⁻¹ := by
    intro v hv
    have hvδ : δ ≤ ‖v - u‖ := by
      have := hv.2
      rwa [mem_ball, dist_eq_norm, not_lt] at this
    have hn : 0 < ‖v - u‖ := hδ.trans_le hvδ
    have hne : v - u ≠ 0 := norm_ne_zero_iff.mp hn.ne'
    have he : F v / (u - v) ^ 2 - F u * ((v - u + 0 * conj (v - u)) ^ 2)⁻¹ = (F v - F u) / (v - u) ^ 2 := by
      have : (u - v) ^ 2 = (v - u) ^ 2 := by ring
      rw [this, zero_mul, add_zero]
      field_simp
    rw [he, norm_div, norm_pow]
    calc ‖F v - F u‖ / ‖v - u‖ ^ 2 ≤ L * ‖v - u‖ / ‖v - u‖ ^ 2 := by gcongr; exact hL v hv.1
      _ = L * ‖v - u‖⁻¹ := by field_simp
  have hdi : IntegrableOn (fun v => F v / (u - v) ^ 2 - F u * ((v - u + 0 * conj (v - u)) ^ 2)⁻¹)
      (ball u r \ ball u δ) :=
    Integrable.mono' ((hinv.mono_set sdiff_subset).const_mul L) hdm (ae_restrict_of_forall_mem hA hpt)
  have hhi : IntegrableOn (fun v => F v / (u - v) ^ 2) (ball u r \ ball u δ) := by
    have := hdi.add hmi
    simpa only [Pi.add_def, sub_add_cancel] using this
  refine ⟨hhi, ?_⟩
  have hsplit := integral_sub hhi hmi
  rw [hm0, sub_zero] at hsplit
  rw [← hsplit]
  calc ‖∫ v in ball u r \ ball u δ, (F v / (u - v) ^ 2 - F u * ((v - u + 0 * conj (v - u)) ^ 2)⁻¹)‖
      ≤ ∫ v in ball u r \ ball u δ, ‖F v / (u - v) ^ 2 - F u * ((v - u + 0 * conj (v - u)) ^ 2)⁻¹‖ :=
        norm_integral_le_integral_norm _
    _ ≤ ∫ v in ball u r \ ball u δ, L * ‖v - u‖⁻¹ :=
        setIntegral_mono_on hdi.norm ((hinv.mono_set sdiff_subset).const_mul L) hA hpt
    _ ≤ ∫ v in ball u r, L * ‖v - u‖⁻¹ :=
        setIntegral_mono_set (hinv.const_mul L) (ae_of_all _ fun v => by positivity)
          sdiff_subset.eventuallyLE
    _ = L * (2 * π * r) := by rw [integral_const_mul, s71c2_ball_inv u hr]

/-- `|v - z̄| ≥ c (1 + |v|)` on `𝕌`. -/
theorem s71c2_lower {z : ℂ} (hz : z ∈ upperHalf) :
    ∃ c : ℝ, 0 < c ∧ ∀ v ∈ upperHalf, c * (1 + ‖v‖) ≤ ‖v - conj z‖ := by
  have hz0 : 0 < z.im := hz
  refine ⟨z.im / (z.im + 1 + ‖z‖), by positivity, fun v hv => ?_⟩
  have hv0 : 0 < v.im := hv
  have h1 : z.im ≤ ‖v - conj z‖ := by
    have := Complex.abs_im_le_norm (v - conj z)
    rw [Complex.sub_im, Complex.conj_im, abs_of_pos (by linarith)] at this
    linarith
  have h2 : ‖v‖ - ‖z‖ ≤ ‖v - conj z‖ := by
    have := norm_sub_norm_le v (conj z)
    rwa [Complex.norm_conj] at this
  rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
  nlinarith [mul_le_mul_of_nonneg_left h1 (norm_nonneg z), mul_le_mul_of_nonneg_left h2 hz0.le,
    norm_nonneg (v - conj z)]

/-- `p⁻¹ᐟ² ≤ 2 t⁻¹ᐟ²` for `t ≤ 4p`. -/
theorem s71c2_half {p t : ℝ} (hp : 0 < p) (ht : 0 < t) (h : t ≤ 4 * p) :
    p ^ (-(1 / 2 : ℝ)) ≤ 2 * t ^ (-(1 / 2 : ℝ)) := by
  rw [Real.rpow_neg hp.le, Real.rpow_neg ht.le, ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow]
  have h1 : √t ≤ 2 * √p := by
    rw [show (2 : ℝ) = √4 by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)],
      ← Real.sqrt_mul (by norm_num)]
    exact Real.sqrt_le_sqrt h
  have hp' : 0 < √p := Real.sqrt_pos.2 hp
  have ht' : 0 < √t := Real.sqrt_pos.2 ht
  calc (√p)⁻¹ = (2 * √p)⁻¹ * 2 := by field_simp
    _ ≤ (√t)⁻¹ * 2 := mul_le_mul_of_nonneg_right (inv_anti₀ ht' h1) (by norm_num)
    _ = 2 * (√t)⁻¹ := mul_comm _ _

/-- `(p²)⁻¹ ≤ 2 t^{-1/2} p^{-3/2}` for `t ≤ 2p`. -/
theorem s71c2_split {p t : ℝ} (ht : 0 < t) (h : t ≤ 2 * p) :
    (p ^ 2)⁻¹ ≤ 2 * t ^ (-(1 / 2 : ℝ)) * p ^ (-(3 / 2 : ℝ)) := by
  have hp : 0 < p := by linarith
  have he : (p ^ 2)⁻¹ = p ^ (-(1 / 2 : ℝ)) * p ^ (-(3 / 2 : ℝ)) := by
    rw [← Real.rpow_add hp, show -(1 / 2 : ℝ) + -(3 / 2) = -2 by norm_num, Real.rpow_neg hp.le, Real.rpow_two]
  rw [he]
  exact mul_le_mul_of_nonneg_right (s71c2_half hp ht (by linarith)) (by positivity)

/-- **Far part.** `|ν| ≤ N`, `|v - u| ≥ Im u/2`, `|v - z̄| ≥ c(1 + |v|)`, then `s71_t_conv` at `b = u`. -/
theorem s71c2_far {ν : ℂ → ℂ} {N c C₁ : ℝ} {z u : ℂ} (hc : 0 < c)
    (hlow : ∀ v ∈ upperHalf, c * (1 + ‖v‖) ≤ ‖v - conj z‖) (hN : ∀ v ∈ upperHalf, ‖ν v‖ ≤ N)
    (hu : u ∈ upperHalf)
    (hT : Integrable (fun w : ℂ => ((1 + ‖w‖) ^ 2)⁻¹ * ‖w - u‖ ^ (-(3 / 2 : ℝ))) ∧
      ∫ w : ℂ, ((1 + ‖w‖) ^ 2)⁻¹ * ‖w - u‖ ^ (-(3 / 2 : ℝ)) ≤ C₁ * (1 + ‖u‖) ^ (-(1 / 2 : ℝ)))
    (hmeas : AEStronglyMeasurable (fun v => ν v / ((u - v) ^ 2 * (v - conj z) ^ 2)) (volume.restrict upperHalf))
    {S : Set ℂ} (hSm : MeasurableSet S) (hSU : S ⊆ upperHalf) (hSr : ∀ v ∈ S, u.im / 2 ≤ ‖v - u‖) :
    IntegrableOn (fun v => ν v / ((u - v) ^ 2 * (v - conj z) ^ 2)) S ∧
      ‖∫ v in S, ν v / ((u - v) ^ 2 * (v - conj z) ^ 2)‖ ≤
        N * (c ^ 2)⁻¹ * 2 * u.im ^ (-(1 / 2 : ℝ)) * (C₁ * (1 + ‖u‖) ^ (-(1 / 2 : ℝ))) := by
  have ht : 0 < u.im := hu
  have hN0 : 0 ≤ N := (norm_nonneg _).trans (hN u hu)
  set K : ℝ := N * (c ^ 2)⁻¹ * 2 * u.im ^ (-(1 / 2 : ℝ)) with hK
  have hK0 : 0 ≤ K := by positivity
  have hpt : ∀ v ∈ S, ‖ν v / ((u - v) ^ 2 * (v - conj z) ^ 2)‖ ≤
      K * (((1 + ‖v‖) ^ 2)⁻¹ * ‖v - u‖ ^ (-(3 / 2 : ℝ))) := by
    intro v hv
    have hvU := hSU hv
    have hr := hSr v hv
    have hp : 0 < ‖v - u‖ := by linarith
    have hl := hlow v hvU
    have hq : 0 < ‖v - conj z‖ := lt_of_lt_of_le (by positivity) hl
    rw [norm_div, norm_mul, norm_pow, norm_pow, norm_sub_rev u v]
    have h1 := s71c2_split ht (show u.im ≤ 2 * ‖v - u‖ by linarith)
    have h2 : (‖v - conj z‖ ^ 2)⁻¹ ≤ (c ^ 2)⁻¹ * ((1 + ‖v‖) ^ 2)⁻¹ := by
      rw [← mul_inv, ← mul_pow]
      exact inv_anti₀ (by positivity) (pow_le_pow_left₀ (by positivity) hl 2)
    calc ‖ν v‖ / (‖v - u‖ ^ 2 * ‖v - conj z‖ ^ 2) = ‖ν v‖ * ((‖v - u‖ ^ 2)⁻¹ * (‖v - conj z‖ ^ 2)⁻¹) := by
          rw [div_eq_mul_inv, mul_inv]
      _ ≤ N * ((2 * u.im ^ (-(1 / 2 : ℝ)) * ‖v - u‖ ^ (-(3 / 2 : ℝ))) *
          ((c ^ 2)⁻¹ * ((1 + ‖v‖) ^ 2)⁻¹)) := by gcongr; exact hN v hvU
      _ = K * (((1 + ‖v‖) ^ 2)⁻¹ * ‖v - u‖ ^ (-(3 / 2 : ℝ))) := by rw [hK]; ring
  have hint : IntegrableOn (fun v => ν v / ((u - v) ^ 2 * (v - conj z) ^ 2)) S :=
    Integrable.mono' (hT.1.integrableOn.const_mul K) (hmeas.mono_measure (Measure.restrict_mono hSU le_rfl))
      (ae_restrict_of_forall_mem hSm hpt)
  refine ⟨hint, ?_⟩
  calc ‖∫ v in S, ν v / ((u - v) ^ 2 * (v - conj z) ^ 2)‖
      ≤ ∫ v in S, ‖ν v / ((u - v) ^ 2 * (v - conj z) ^ 2)‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ v in S, K * (((1 + ‖v‖) ^ 2)⁻¹ * ‖v - u‖ ^ (-(3 / 2 : ℝ))) :=
        setIntegral_mono_on hint.norm (hT.1.integrableOn.const_mul K) hSm hpt
    _ ≤ ∫ v, K * (((1 + ‖v‖) ^ 2)⁻¹ * ‖v - u‖ ^ (-(3 / 2 : ℝ))) :=
        setIntegral_le_integral (hT.1.const_mul K) (ae_of_all _ fun v => by positivity)
    _ ≤ K * (C₁ * (1 + ‖u‖) ^ (-(1 / 2 : ℝ))) := by
        rw [integral_const_mul]
        exact mul_le_mul_of_nonneg_left hT.2 hK0

/-- Weight comparisons on `𝕌`: `(1 + |u|)⁻⁴ ≤ (1 + |u|)^{-5/2} (Im u)^{-1/2}` and
`(1 + |u|)⁻² (1 + |u|)^{-1/2} = (1 + |u|)^{-5/2}`. -/
theorem s71c2_weights {u : ℂ} (hu : u ∈ upperHalf) :
    ((1 + ‖u‖) ^ 2)⁻¹ * ((1 + ‖u‖) ^ 2)⁻¹ ≤ (1 + ‖u‖) ^ (-(5 / 2 : ℝ)) * u.im ^ (-(1 / 2 : ℝ)) ∧
      ((1 + ‖u‖) ^ 2)⁻¹ * (1 + ‖u‖) ^ (-(1 / 2 : ℝ)) = (1 + ‖u‖) ^ (-(5 / 2 : ℝ)) := by
  have ht : 0 < u.im := hu
  have hx : 1 ≤ 1 + ‖u‖ := by linarith [norm_nonneg u]
  have hx0 : 0 < 1 + ‖u‖ := by linarith
  have hyx : u.im ≤ 1 + ‖u‖ := by
    have := Complex.im_le_norm u
    linarith
  have h2 : ((1 + ‖u‖) ^ 2)⁻¹ = (1 + ‖u‖) ^ (-2 : ℝ) := by rw [Real.rpow_neg hx0.le, Real.rpow_two]
  constructor
  · rw [h2, ← Real.rpow_add hx0, show (-2 : ℝ) + -2 = -(5 / 2) + -(3 / 2) by norm_num, Real.rpow_add hx0]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    calc (1 + ‖u‖) ^ (-(3 / 2 : ℝ)) ≤ (1 + ‖u‖) ^ (-(1 / 2 : ℝ)) :=
          Real.rpow_le_rpow_of_exponent_le hx (by norm_num)
      _ ≤ u.im ^ (-(1 / 2 : ℝ)) := Real.rpow_le_rpow_of_nonpos ht hyx (by norm_num)
  · rw [h2, ← Real.rpow_add hx0]
    norm_num

/-- **(C2)** `[W?]` **Uniform bound on the moving truncations.** A majorant of the `v`-truncations at `u`, uniform in
`δ ∈ (0, 1]`, integrable against `|μ(u)|/|u - z̄|²` on `𝕌`. Paper bound: on `B(u, Im u/2)` the mean-zero model and the
`C¹` constant `|∇(ν(v)/(v - z̄)²)| ≲ 1/Im v` (Cauchy estimates for `ψ`, `|Im² ψ| ≤ C`) give `O(1)`; on the rest,
`|ν| ≤ C` gives `O(1 + log⁺(1/Im u))`; for `|u| → ∞`, `O(log |u|/|u|²)`. -/
theorem s71_v_unif {μ ν φ ψ : ℂ → ℂ} (hμ : IsHarmonicU μ φ) (hν : IsHarmonicU ν ψ) {z : ℂ} (hz : z ∈ upperHalf) :
    ∃ g : ℂ → ℝ, IntegrableOn (fun u => ‖μ u‖ / ‖u - conj z‖ ^ 2 * g u) upperHalf ∧
      ∀ u ∈ upperHalf, ∀ δ : ℝ, 0 < δ → δ ≤ 1 →
        ‖∫ v in upperHalf \ ball u δ, ν v / ((u - v) ^ 2 * (v - conj z) ^ 2)‖ ≤ g u := by
  have hνc := harmonicU_continuousOn hν
  obtain ⟨hdψ, ⟨C, hC⟩, h3⟩ := hν
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC z hz)
  obtain ⟨Mμ, hM0, hMμ⟩ := harmonicU_bounded hμ
  obtain ⟨N, hN0, hN⟩ := harmonicU_bounded ⟨hdψ, ⟨C, hC⟩, h3⟩
  obtain ⟨c, hc, hlow⟩ := s71c2_lower hz
  obtain ⟨C₁, hC₁0, hT⟩ := s71_t_conv
  have hmU : MeasurableSet upperHalf := isOpen_upperHalf.measurableSet
  have hz0 : 0 < z.im := hz
  set g : ℂ → ℝ := fun u => 612 * C * π * (c ^ 2)⁻¹ * ((1 + ‖u‖) ^ 2)⁻¹ +
    N * (c ^ 2)⁻¹ * 2 * u.im ^ (-(1 / 2 : ℝ)) * (C₁ * (1 + ‖u‖) ^ (-(1 / 2 : ℝ))) with hg
  refine ⟨g, ?_, fun u hu δ hδ _ => ?_⟩
  · -- integrability: domination by `s71_t_half`
    set K : ℝ := Mμ * (c ^ 2)⁻¹ * (612 * C * π * (c ^ 2)⁻¹ + N * (c ^ 2)⁻¹ * 2 * C₁) with hK
    have hmeas : AEStronglyMeasurable (fun u => ‖μ u‖ / ‖u - conj z‖ ^ 2 * g u) (volume.restrict upperHalf) := by
      have h1 : AEStronglyMeasurable (fun u => ‖μ u‖) (volume.restrict upperHalf) :=
        (harmonicU_continuousOn hμ).norm.aestronglyMeasurable hmU
      have h2 : Measurable fun u : ℂ => (‖u - conj z‖ ^ 2)⁻¹ * g u := by rw [hg]; fun_prop
      have := h1.mul h2.aestronglyMeasurable
      simpa only [div_eq_mul_inv, mul_assoc, Pi.mul_def] using this
    refine Integrable.mono' (s71_t_half.const_mul K) hmeas (ae_restrict_of_forall_mem hmU fun u hu => ?_)
    obtain ⟨w1, w2⟩ := s71c2_weights hu
    have hl := hlow u hu
    have hB : (‖u - conj z‖ ^ 2)⁻¹ ≤ (c ^ 2)⁻¹ * ((1 + ‖u‖) ^ 2)⁻¹ := by
      rw [← mul_inv, ← mul_pow]
      exact inv_anti₀ (by positivity) (pow_le_pow_left₀ (by positivity) hl 2)
    have hg0 : 0 ≤ g u := by
      have hr := Real.rpow_nonneg (le_of_lt (show (0 : ℝ) < u.im from hu)) (-(1 / 2 : ℝ))
      simp only [hg]
      positivity
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (div_nonneg (norm_nonneg _) (by positivity)) hg0),
      div_eq_mul_inv]
    calc ‖μ u‖ * (‖u - conj z‖ ^ 2)⁻¹ * g u ≤ Mμ * ((c ^ 2)⁻¹ * ((1 + ‖u‖) ^ 2)⁻¹) * g u :=
          mul_le_mul_of_nonneg_right (mul_le_mul (hMμ u hu) hB (by positivity) hM0) hg0
      _ = Mμ * (c ^ 2)⁻¹ * (612 * C * π * (c ^ 2)⁻¹ * (((1 + ‖u‖) ^ 2)⁻¹ * ((1 + ‖u‖) ^ 2)⁻¹) +
          N * (c ^ 2)⁻¹ * 2 * C₁ * (((1 + ‖u‖) ^ 2)⁻¹ * (1 + ‖u‖) ^ (-(1 / 2 : ℝ))) * u.im ^ (-(1 / 2 : ℝ))) := by
          rw [hg]; ring
      _ ≤ Mμ * (c ^ 2)⁻¹ * (612 * C * π * (c ^ 2)⁻¹ * ((1 + ‖u‖) ^ (-(5 / 2 : ℝ)) * u.im ^ (-(1 / 2 : ℝ))) +
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

/-- `(x²)⁻¹ ≤ δ^(-1/2) x^(-3/2)` for `0 < δ ≤ x`. -/
theorem s71_inv_sq_le {x δ : ℝ} (hδ : 0 < δ) (h : δ ≤ x) :
    (x ^ 2)⁻¹ ≤ δ ^ (-(1 / 2 : ℝ)) * x ^ (-(3 / 2 : ℝ)) := by
  have hx : 0 < x := hδ.trans_le h
  have e : (x ^ 2)⁻¹ = x ^ (-(1 / 2 : ℝ)) * x ^ (-(3 / 2 : ℝ)) := by
    rw [← Real.rpow_add hx, show -(1 / 2 : ℝ) + -(3 / 2) = -((2 : ℕ) : ℝ) by norm_num, Real.rpow_neg hx.le,
      Real.rpow_natCast]
  rw [e]
  exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_nonpos hδ h (by norm_num)) (by positivity)

/-- The majorant `(1+|u|)⁻² (1+|v|)⁻² |v - u|^(-3/2)` is integrable on `ℂ × ℂ` (`s71_t_conv`, Tonelli). -/
theorem s71_maj_int :
    Integrable (fun p : ℂ × ℂ => ((1 + ‖p.1‖) ^ 2)⁻¹ * (((1 + ‖p.2‖) ^ 2)⁻¹ * ‖p.2 - p.1‖ ^ (-(3 / 2 : ℝ))))
      ((volume : Measure ℂ).prod volume) := by
  obtain ⟨C, hC0, hC⟩ := s71_t_conv
  have hm : AEStronglyMeasurable
      (fun p : ℂ × ℂ => ((1 + ‖p.1‖) ^ 2)⁻¹ * (((1 + ‖p.2‖) ^ 2)⁻¹ * ‖p.2 - p.1‖ ^ (-(3 / 2 : ℝ))))
      ((volume : Measure ℂ).prod volume) := Measurable.aestronglyMeasurable (by fun_prop)
  rw [integrable_prod_iff hm]
  refine ⟨Eventually.of_forall fun u => (hC u).1.const_mul ((1 + ‖u‖) ^ 2)⁻¹, ?_⟩
  have hmaj : Integrable (fun u : ℂ => C * (1 + ‖u‖) ^ (-(5 / 2 : ℝ))) :=
    (integrable_one_add_norm (by rw [Complex.finrank_real_complex]; norm_num)).const_mul C
  refine hmaj.mono' hm.norm.integral_prod_right' (Eventually.of_forall fun u => ?_)
  have ht : 0 < 1 + ‖u‖ := by positivity
  have e : (fun v => ‖((1 + ‖(u, v).1‖) ^ 2)⁻¹ * (((1 + ‖(u, v).2‖) ^ 2)⁻¹ * ‖(u, v).2 - (u, v).1‖ ^
      (-(3 / 2 : ℝ)))‖) = fun v => ((1 + ‖u‖) ^ 2)⁻¹ * (((1 + ‖v‖) ^ 2)⁻¹ * ‖v - u‖ ^ (-(3 / 2 : ℝ))) := by
    funext v
    exact Real.norm_of_nonneg (by positivity)
  rw [e, integral_const_mul]
  have hI : 0 ≤ ∫ v : ℂ, ((1 + ‖v‖) ^ 2)⁻¹ * ‖v - u‖ ^ (-(3 / 2 : ℝ)) :=
    integral_nonneg fun v => by positivity
  rw [Real.norm_of_nonneg (mul_nonneg (by positivity) hI)]
  have e2 : ((1 + ‖u‖) ^ 2)⁻¹ * (C * (1 + ‖u‖) ^ (-(1 / 2 : ℝ))) = C * (1 + ‖u‖) ^ (-(5 / 2 : ℝ)) := by
    rw [show ((1 + ‖u‖) ^ 2)⁻¹ = (1 + ‖u‖) ^ (-((2 : ℕ) : ℝ)) by rw [Real.rpow_neg ht.le, Real.rpow_natCast]]
    rw [mul_left_comm, ← Real.rpow_add ht]
    norm_num
  rw [← e2]
  exact mul_le_mul_of_nonneg_left (hC u).2 (by positivity)

/-- **(C3)** `[W1]` **Bridge for (7.2).** The symmetric cut-off integrals converge to the iterated integral with inner
principal value. Route: for each `δ > 0` the cut-off integrand is integrable on `𝕌 × 𝕌` (decay `|u|⁻⁴ log` at `∞`, no
singularity near `∂𝕌` since `z̄ ∈ 𝕃`), Fubini (the `v`-slice of `{|u - v| ≥ δ}` is `𝕌 ∖ B(u, δ)`), then dominated
convergence in `u` with C1, C2. -/
theorem s71_bridge72 {μ ν φ ψ : ℂ → ℂ} (hμ : IsHarmonicU μ φ) (hν : IsHarmonicU ν ψ) {z : ℂ} (hz : z ∈ upperHalf) :
    Tendsto (fun δ : ℝ => ∫ p in (upperHalf ×ˢ upperHalf) ∩ {p : ℂ × ℂ | δ ≤ ‖p.1 - p.2‖},
        μ p.1 * ν p.2 / ((p.1 - conj z) ^ 2 * (p.1 - p.2) ^ 2 * (p.2 - conj z) ^ 2)) (𝓝[>] 0)
      (𝓝 (∫ u in upperHalf, μ u / (u - conj z) ^ 2 * pv2 (fun v => ν v / ((u - v) ^ 2 * (v - conj z) ^ 2)) u z)) := by
  obtain ⟨Mμ, hMμ0, hMμ⟩ := harmonicU_bounded hμ
  obtain ⟨Mν, hMν0, hMν⟩ := harmonicU_bounded hν
  have hU := measurableSet_upperHalf_aux
  have hcm : Measurable (conj : ℂ → ℂ) := Complex.continuous_conj.measurable
  have hzim : 0 < z.im := hz
  set c := z.im / (1 + ‖z‖ + z.im) with hcd
  have hc : 0 < c := by positivity
  have hsep : ∀ w ∈ upperHalf, c * (1 + ‖w‖) ≤ ‖w - conj z‖ := fun w hw =>
    e64_sep hzim (norm_nonneg z) (show (0 : ℝ) < w.im from hw).le (by rw [Complex.conj_im])
      (by rw [Complex.norm_conj])
  set F2 : ℂ × ℂ → ℂ := fun p => μ p.1 * ν p.2 / ((p.1 - conj z) ^ 2 * (p.1 - p.2) ^ 2 * (p.2 - conj z) ^ 2)
    with hF2
  set S : ℝ → Set (ℂ × ℂ) := fun δ => (upperHalf ×ˢ upperHalf) ∩ {p : ℂ × ℂ | δ ≤ ‖p.1 - p.2‖} with hSd
  have hSm : ∀ δ, MeasurableSet (S δ) := fun δ =>
    (hU.prod hU).inter (isClosed_le continuous_const ((continuous_fst.sub continuous_snd).norm)).measurableSet
  have hμm : AEStronglyMeasurable (upperHalf.indicator μ) volume :=
    (aestronglyMeasurable_indicator_iff hU).2 ((harmonicU_continuousOn hμ).aestronglyMeasurable hU)
  have hνm : AEStronglyMeasurable (upperHalf.indicator ν) volume :=
    (aestronglyMeasurable_indicator_iff hU).2 ((harmonicU_continuousOn hν).aestronglyMeasurable hU)
  have hKm : Measurable fun p : ℂ × ℂ => ((p.1 - conj z) ^ 2 * (p.1 - p.2) ^ 2 * (p.2 - conj z) ^ 2)⁻¹ := by
    fun_prop
  have hFm : ∀ δ, AEStronglyMeasurable ((S δ).indicator F2) ((volume : Measure ℂ).prod volume) := by
    intro δ
    have h : AEStronglyMeasurable (fun p : ℂ × ℂ => upperHalf.indicator μ p.1 * upperHalf.indicator ν p.2 *
        ((p.1 - conj z) ^ 2 * (p.1 - p.2) ^ 2 * (p.2 - conj z) ^ 2)⁻¹) ((volume : Measure ℂ).prod volume) :=
      (((hμm.comp_fst (ν := volume)).mul (hνm.comp_snd (μ := volume))).mul hKm.aestronglyMeasurable)
    refine (h.indicator (hSm δ)).congr (Eventually.of_forall fun p => ?_)
    by_cases hp : p ∈ S δ
    · rw [indicator_of_mem hp, indicator_of_mem hp, indicator_of_mem hp.1.1, indicator_of_mem hp.1.2]
      simp only [hF2, div_eq_mul_inv]
    · rw [indicator_of_notMem hp, indicator_of_notMem hp]
  have hΦ := s71_maj_int
  have hInt : ∀ δ : ℝ, 0 < δ → Integrable ((S δ).indicator F2) ((volume : Measure ℂ).prod volume) := by
    intro δ hδ
    refine (hΦ.const_mul (Mμ * Mν * (c ^ 4)⁻¹ * δ ^ (-(1 / 2 : ℝ)))).mono' (hFm δ)
      (Eventually.of_forall fun p => ?_)
    by_cases hp : p ∈ S δ
    · rw [indicator_of_mem hp]
      obtain ⟨⟨hu, hv⟩, hd⟩ := hp
      have hd' : δ ≤ ‖p.1 - p.2‖ := hd
      have h1 := hsep _ hu
      have h2 := hsep _ hv
      have hq := s71_inv_sq_le hδ hd'
      rw [norm_sub_rev p.1 p.2] at hq
      have hu1 : 0 < c * (1 + ‖p.1‖) := by positivity
      have hv1 : 0 < c * (1 + ‖p.2‖) := by positivity
      calc ‖F2 p‖ = ‖μ p.1‖ * ‖ν p.2‖ * ((‖p.1 - conj z‖ ^ 2)⁻¹ * ((‖p.2 - conj z‖ ^ 2)⁻¹ *
            (‖p.2 - p.1‖ ^ 2)⁻¹)) := by
            rw [hF2]
            simp only [norm_div, norm_mul, norm_pow]
            rw [norm_sub_rev p.1 p.2]
            ring
        _ ≤ Mμ * Mν * (((c * (1 + ‖p.1‖)) ^ 2)⁻¹ * (((c * (1 + ‖p.2‖)) ^ 2)⁻¹ *
            (δ ^ (-(1 / 2 : ℝ)) * ‖p.2 - p.1‖ ^ (-(3 / 2 : ℝ))))) := by
            gcongr
            all_goals first | exact hMμ _ hu | exact hMν _ hv | exact h1 | exact h2 | exact hq
        _ = Mμ * Mν * (c ^ 4)⁻¹ * δ ^ (-(1 / 2 : ℝ)) * (((1 + ‖p.1‖) ^ 2)⁻¹ * (((1 + ‖p.2‖) ^ 2)⁻¹ *
            ‖p.2 - p.1‖ ^ (-(3 / 2 : ℝ)))) := by
            rw [mul_pow, mul_pow, mul_inv, mul_inv]
            ring
    · rw [indicator_of_notMem hp, norm_zero]
      positivity
  -- Fubini: the inner integral is the one-disc truncation
  set T : ℂ → ℝ → ℂ := fun u δ => ∫ v in upperHalf \ ball u δ, ν v / ((u - v) ^ 2 * (v - conj z) ^ 2) with hTd
  set hh : ℂ → ℂ := fun u => μ u / (u - conj z) ^ 2 with hhd
  have hin : ∀ δ u, (∫ v, (S δ).indicator F2 (u, v)) = upperHalf.indicator (fun u => hh u * T u δ) u := by
    intro δ u
    by_cases hu : u ∈ upperHalf
    · rw [indicator_of_mem hu]
      have e : (fun v => (S δ).indicator F2 (u, v)) = fun v => hh u *
          (upperHalf \ ball u δ).indicator (fun v => ν v / ((u - v) ^ 2 * (v - conj z) ^ 2)) v := by
        funext v
        by_cases hv : v ∈ upperHalf \ ball u δ
        · have hp : (u, v) ∈ S δ := ⟨⟨hu, hv.1⟩, by
            have := hv.2
            rw [mem_ball, dist_eq_norm, not_lt, norm_sub_rev] at this
            exact this⟩
          rw [indicator_of_mem hp, indicator_of_mem hv]
          simp only [hF2, hhd]
          rw [div_mul_div_comm, ← mul_assoc]
        · have hp : (u, v) ∉ S δ := fun hp => hv ⟨hp.1.2, by
            rw [mem_ball, dist_eq_norm, not_lt, norm_sub_rev]
            exact hp.2⟩
          rw [indicator_of_notMem hp, indicator_of_notMem hv, mul_zero]
      rw [e, integral_const_mul, integral_indicator (hU.diff measurableSet_ball)]
    · rw [indicator_of_notMem hu]
      have e : (fun v => (S δ).indicator F2 (u, v)) = fun _ => 0 :=
        funext fun v => indicator_of_notMem (fun hp => hu hp.1.1) _
      rw [e, integral_zero]
  have hfub : ∀ δ : ℝ, 0 < δ → ∫ p in S δ, F2 p = ∫ u, upperHalf.indicator (fun u => hh u * T u δ) u := by
    intro δ hδ
    rw [← integral_indicator (hSm δ), Measure.volume_eq_prod, integral_prod _ (hInt δ hδ)]
    exact integral_congr_ae (Eventually.of_forall fun u => hin δ u)
  -- dominated convergence in `u`
  obtain ⟨g, hgI, hgb⟩ := s71_v_unif hμ hν hz
  have key : Tendsto (fun δ : ℝ => ∫ u, upperHalf.indicator (fun u => hh u * T u δ) u) (𝓝[>] 0)
      (𝓝 (∫ u, upperHalf.indicator
        (fun u => hh u * pv2 (fun v => ν v / ((u - v) ^ 2 * (v - conj z) ^ 2)) u z) u)) := by
    refine tendsto_integral_filter_of_dominated_convergence
      (upperHalf.indicator fun u => ‖μ u‖ / ‖u - conj z‖ ^ 2 * g u) ?_ ?_ ((integrable_indicator_iff hU).2 hgI) ?_
    · filter_upwards [self_mem_nhdsWithin] with δ hδ
      exact ((hInt δ hδ).integral_prod_left.aestronglyMeasurable).congr
        (Eventually.of_forall fun u => hin δ u)
    · filter_upwards [Ioc_mem_nhdsGT one_pos] with δ hδ
      refine Eventually.of_forall fun u => ?_
      by_cases hu : u ∈ upperHalf
      · rw [indicator_of_mem hu, indicator_of_mem hu, norm_mul]
        simp only [hhd, norm_div, norm_pow]
        exact mul_le_mul_of_nonneg_left (hgb u hu δ hδ.1 hδ.2) (by positivity)
      · rw [indicator_of_notMem hu, indicator_of_notMem hu, norm_zero]
    · refine Eventually.of_forall fun u => ?_
      by_cases hu : u ∈ upperHalf
      · simp only [indicator_of_mem hu]
        exact (s71_v_trunc hν hz hu).const_mul (hh u)
      · simp only [indicator_of_notMem hu]
        exact tendsto_const_nhds
  rw [integral_indicator hU] at key
  refine key.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  exact (hfub δ hδ).symm

/-! ### (7.3), (7.5): the principal value in `v` at `z` outside -/

/-- (D1) Real-power bookkeeping: `X⁻² X^{-1/2} = X^{-5/2}`, and `X⁻⁴ ≤ X^{-5/2} y^{-1/2}` for `0 < y ≤ X`, `1 ≤ X`. -/
theorem s71_d1_alg {X y : ℝ} (hX : 1 ≤ X) (hy : 0 < y) (hyX : y ≤ X) :
    (X ^ 2)⁻¹ * X ^ (-(1 / 2 : ℝ)) = X ^ (-(5 / 2 : ℝ)) ∧
      (X ^ 2)⁻¹ * (X ^ 2)⁻¹ ≤ X ^ (-(5 / 2 : ℝ)) * y ^ (-(1 / 2 : ℝ)) := by
  have hX0 : 0 < X := by linarith
  have e2 : (X ^ 2)⁻¹ = X ^ (-(2 : ℝ)) := by
    rw [Real.rpow_neg hX0.le, Real.rpow_two]
  have h1 : (X ^ 2)⁻¹ * X ^ (-(1 / 2 : ℝ)) = X ^ (-(5 / 2 : ℝ)) := by
    rw [e2, ← Real.rpow_add hX0]; norm_num
  refine ⟨h1, ?_⟩
  have hy' : X ^ (-(1 / 2 : ℝ)) ≤ y ^ (-(1 / 2 : ℝ)) := Real.rpow_le_rpow_of_nonpos hy hyX (by norm_num)
  have h3 : (X ^ 2)⁻¹ ≤ X ^ (-(1 / 2 : ℝ)) * X ^ (-(1 / 2 : ℝ)) := by
    rw [e2, ← Real.rpow_add hX0]
    exact Real.rpow_le_rpow_of_exponent_le hX (by norm_num)
  calc (X ^ 2)⁻¹ * (X ^ 2)⁻¹ ≤ (X ^ 2)⁻¹ * (X ^ (-(1 / 2 : ℝ)) * X ^ (-(1 / 2 : ℝ))) :=
        mul_le_mul_of_nonneg_left h3 (by positivity)
    _ = (X ^ 2)⁻¹ * X ^ (-(1 / 2 : ℝ)) * X ^ (-(1 / 2 : ℝ)) := by ring
    _ = X ^ (-(5 / 2 : ℝ)) * X ^ (-(1 / 2 : ℝ)) := by rw [h1]
    _ ≤ X ^ (-(5 / 2 : ℝ)) * y ^ (-(1 / 2 : ℝ)) := mul_le_mul_of_nonneg_left hy' (by positivity)

/-- (D1) The outer weight: `|μ(u)/(u - z̄)²| ≤ M (1 + |u|)⁻²` on `𝕌`. -/
theorem s71_d1_cu {μ φ : ℂ → ℂ} (hμ : IsHarmonicU μ φ) {z : ℂ} (hz : z ∈ upperHalf) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ u ∈ upperHalf, ‖μ u / (u - conj z) ^ 2‖ ≤ M * ((1 + ‖u‖) ^ 2)⁻¹ := by
  obtain ⟨Mμ, hMμ, hb⟩ := harmonicU_bounded hμ
  have hz0 : 0 < z.im := hz
  have hc0 : 0 < z.im / (1 + ‖conj z‖ + z.im) := div_pos hz0 (by linarith [norm_nonneg (conj z)])
  refine ⟨Mμ * ((z.im / (1 + ‖conj z‖ + z.im)) ^ 2)⁻¹, by positivity, fun u hu => ?_⟩
  have hu0 : 0 < u.im := hu
  have him := e64_t10_im (a := conj z) hu0 (by rw [Complex.conj_im]; linarith)
  rw [Complex.conj_im, neg_neg] at him
  have hl := e64_t10_lower hz0 him
  have hX : 0 < z.im / (1 + ‖conj z‖ + z.im) * (1 + ‖u‖) := by positivity
  rw [norm_div, norm_pow, div_eq_mul_inv]
  calc ‖μ u‖ * (‖u - conj z‖ ^ 2)⁻¹
      ≤ Mμ * ((z.im / (1 + ‖conj z‖ + z.im) * (1 + ‖u‖)) ^ 2)⁻¹ :=
        mul_le_mul (hb u hu) (inv_anti₀ (by positivity) (pow_le_pow_left₀ hX.le hl 2)) (by positivity) hMμ
    _ = Mμ * ((z.im / (1 + ‖conj z‖ + z.im)) ^ 2)⁻¹ * ((1 + ‖u‖) ^ 2)⁻¹ := by rw [mul_pow, mul_inv]; ring

/-- (D1) The `v`-kernel off a disc: for `δ > 0` and `u ∈ 𝕌`, `\overline{ν(v)}/((u - v̄)²(v̄ - z̄)²)` is integrable on
`𝕌 ∖ B(z, δ)`, with `L¹` norm `≤ K (Im u)^{-1/2} (1 + |u|)^{-1/2}` (`s71_t_im` with the roles of `u, v` swapped,
then `s71_t_conv` at `b = ū`). -/
theorem s71_d1_far {ν ψ : ℂ → ℂ} (hν : IsHarmonicU ν ψ) {z : ℂ} {δ : ℝ} (hδ : 0 < δ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ u ∈ upperHalf,
      IntegrableOn (fun v => conj (ν v) / ((u - conj v) ^ 2 * (conj v - conj z) ^ 2)) (upperHalf \ ball z δ) ∧
        ∫ v in upperHalf \ ball z δ, ‖conj (ν v) / ((u - conj v) ^ 2 * (conj v - conj z) ^ 2)‖ ≤
          K * (u.im ^ (-(1 / 2 : ℝ)) * (1 + ‖u‖) ^ (-(1 / 2 : ℝ))) := by
  obtain ⟨Mν, hMν, hb⟩ := harmonicU_bounded hν
  obtain ⟨C, hC, hconv⟩ := s71_t_conv
  have hmU := measurableSet_upperHalf_aux
  have hmS : MeasurableSet (upperHalf \ ball z δ) := hmU.diff measurableSet_ball
  have hc0 : 0 < δ / (1 + ‖z‖ + δ) := div_pos hδ (by positivity)
  refine ⟨Mν * ((δ / (1 + ‖z‖ + δ)) ^ 2)⁻¹ * C, by positivity, fun u hu => ?_⟩
  have hu0 : 0 < u.im := hu
  have hA : 0 ≤ Mν * ((δ / (1 + ‖z‖ + δ)) ^ 2)⁻¹ * u.im ^ (-(1 / 2 : ℝ)) :=
    mul_nonneg (by positivity) (Real.rpow_nonneg hu0.le _)
  have hGi : Integrable (fun v : ℂ => Mν * ((δ / (1 + ‖z‖ + δ)) ^ 2)⁻¹ * u.im ^ (-(1 / 2 : ℝ)) *
      (((1 + ‖v‖) ^ 2)⁻¹ * ‖v - conj u‖ ^ (-(3 / 2 : ℝ)))) := ((hconv (conj u)).1).const_mul _
  have hne : ∀ v ∈ upperHalf \ ball z δ, 0 < ‖v - conj u‖ ∧ δ ≤ ‖v - z‖ := by
    intro v hv
    have hv0 : 0 < v.im := hv.1
    have := e64_t10_im (a := conj u) hv0 (by rw [Complex.conj_im]; linarith)
    rw [Complex.conj_im] at this
    refine ⟨by linarith, ?_⟩
    have := hv.2; rwa [mem_ball, dist_eq_norm, not_lt] at this
  have e1 : ∀ v : ℂ, ‖conj v - conj z‖ = ‖v - z‖ := fun v => by rw [← map_sub, Complex.norm_conj]
  have e2 : ∀ v : ℂ, ‖u - conj v‖ = ‖v - conj u‖ := fun v => by
    rw [← Complex.norm_conj (u - conj v), map_sub, Complex.conj_conj, norm_sub_rev]
  have hbd : ∀ v ∈ upperHalf \ ball z δ,
      ‖conj (ν v) / ((u - conj v) ^ 2 * (conj v - conj z) ^ 2)‖ ≤
        Mν * ((δ / (1 + ‖z‖ + δ)) ^ 2)⁻¹ * u.im ^ (-(1 / 2 : ℝ)) *
          (((1 + ‖v‖) ^ 2)⁻¹ * ‖v - conj u‖ ^ (-(3 / 2 : ℝ))) := by
    intro v hv
    obtain ⟨hP, hvz⟩ := hne v hv
    have hl : δ / (1 + ‖z‖ + δ) * (1 + ‖v‖) ≤ ‖v - z‖ := e64_t10_lower hδ hvz
    have hX : 0 < δ / (1 + ‖z‖ + δ) * (1 + ‖v‖) := by positivity
    have hti := s71_t_im (u := v) (v := u) (le_of_lt hv.1) hu0
    rw [one_div] at hti
    rw [norm_div, Complex.norm_conj, norm_mul, norm_pow, norm_pow, e1, e2, div_eq_mul_inv, mul_inv]
    have hq : (‖v - z‖ ^ 2)⁻¹ ≤ ((δ / (1 + ‖z‖ + δ)) ^ 2)⁻¹ * ((1 + ‖v‖) ^ 2)⁻¹ := by
      rw [← mul_inv, ← mul_pow]; exact inv_anti₀ (by positivity) (pow_le_pow_left₀ hX.le hl 2)
    calc ‖ν v‖ * ((‖v - conj u‖ ^ 2)⁻¹ * (‖v - z‖ ^ 2)⁻¹)
        ≤ Mν * ((u.im ^ (-(1 / 2 : ℝ)) * ‖v - conj u‖ ^ (-(3 / 2 : ℝ))) *
            (((δ / (1 + ‖z‖ + δ)) ^ 2)⁻¹ * ((1 + ‖v‖) ^ 2)⁻¹)) :=
          mul_le_mul (hb v hv.1) (mul_le_mul hti hq (by positivity)
            (mul_nonneg (Real.rpow_nonneg hu0.le _) (by positivity))) (by positivity) hMν
      _ = _ := by ring
  have hcont : ContinuousOn (fun v => conj (ν v) / ((u - conj v) ^ 2 * (conj v - conj z) ^ 2))
      (upperHalf \ ball z δ) := by
    refine ContinuousOn.div ?_ ?_ ?_
    · exact Complex.continuous_conj.comp_continuousOn ((harmonicU_continuousOn hν).mono sdiff_subset)
    · exact (by fun_prop : Continuous fun v : ℂ => (u - conj v) ^ 2 * (conj v - conj z) ^ 2).continuousOn
    · intro v hv
      obtain ⟨hP, hvz⟩ := hne v hv
      refine mul_ne_zero (pow_ne_zero _ ?_) (pow_ne_zero _ ?_)
      · rw [← norm_pos_iff, e2]; exact hP
      · rw [← norm_pos_iff, e1]; linarith
  have hint : IntegrableOn (fun v => conj (ν v) / ((u - conj v) ^ 2 * (conj v - conj z) ^ 2))
      (upperHalf \ ball z δ) := by
    refine Integrable.mono' hGi.integrableOn (hcont.aestronglyMeasurable hmS) ?_
    filter_upwards [ae_restrict_mem hmS] with v hv
    exact hbd v hv
  refine ⟨hint, ?_⟩
  calc ∫ v in upperHalf \ ball z δ, ‖conj (ν v) / ((u - conj v) ^ 2 * (conj v - conj z) ^ 2)‖
      ≤ ∫ v in upperHalf \ ball z δ, Mν * ((δ / (1 + ‖z‖ + δ)) ^ 2)⁻¹ * u.im ^ (-(1 / 2 : ℝ)) *
          (((1 + ‖v‖) ^ 2)⁻¹ * ‖v - conj u‖ ^ (-(3 / 2 : ℝ))) :=
        setIntegral_mono_on hint.norm hGi.integrableOn hmS hbd
    _ ≤ ∫ v, Mν * ((δ / (1 + ‖z‖ + δ)) ^ 2)⁻¹ * u.im ^ (-(1 / 2 : ℝ)) *
          (((1 + ‖v‖) ^ 2)⁻¹ * ‖v - conj u‖ ^ (-(3 / 2 : ℝ))) :=
        setIntegral_le_integral hGi (Eventually.of_forall fun v => mul_nonneg hA (by positivity))
    _ = Mν * ((δ / (1 + ‖z‖ + δ)) ^ 2)⁻¹ * u.im ^ (-(1 / 2 : ℝ)) *
          ∫ v, ((1 + ‖v‖) ^ 2)⁻¹ * ‖v - conj u‖ ^ (-(3 / 2 : ℝ)) := integral_const_mul _ _
    _ ≤ Mν * ((δ / (1 + ‖z‖ + δ)) ^ 2)⁻¹ * u.im ^ (-(1 / 2 : ℝ)) * (C * (1 + ‖conj u‖) ^ (-(1 / 2 : ℝ))) :=
        mul_le_mul_of_nonneg_left (hconv (conj u)).2 hA
    _ = _ := by rw [Complex.norm_conj]; ring

/-- (D1) Algebra of the Lipschitz bound: `|a A⁻² - b B⁻²| ≤ (L c⁻² + 2M c⁻³) X⁻² d` when `|A|, |B| ≥ cX`, `X ≥ 1`,
`|a - b| ≤ L d`, `|b| ≤ M`, `|B - A| = d`. -/
theorem s71_d1_lipalg {a b A B : ℂ} {c X L M d : ℝ} (hc : 0 < c) (hX : 1 ≤ X) (hA : c * X ≤ ‖A‖)
    (hB : c * X ≤ ‖B‖) (hab : ‖a - b‖ ≤ L * d) (hb : ‖b‖ ≤ M) (hBA : ‖B - A‖ = d) (hL : 0 ≤ L) (hM : 0 ≤ M) :
    ‖a * (A ^ 2)⁻¹ - b * (B ^ 2)⁻¹‖ ≤ (L * (c ^ 2)⁻¹ + 2 * M * (c ^ 3)⁻¹) * (X ^ 2)⁻¹ * d := by
  have hX0 : 0 < c * X := mul_pos hc (by linarith)
  have hA0 : A ≠ 0 := norm_pos_iff.mp (hX0.trans_le hA)
  have hB0 : B ≠ 0 := norm_pos_iff.mp (hX0.trans_le hB)
  have hAe : ‖A‖⁻¹ ≤ (c * X)⁻¹ := inv_anti₀ hX0 hA
  have hBe : ‖B‖⁻¹ ≤ (c * X)⁻¹ := inv_anti₀ hX0 hB
  have hd : 0 ≤ d := hBA ▸ norm_nonneg _
  have he : 0 ≤ (c * X)⁻¹ := inv_nonneg.mpr hX0.le
  have key : a * (A ^ 2)⁻¹ - b * (B ^ 2)⁻¹ =
      (a - b) * (A⁻¹ * A⁻¹) + b * ((B - A) * (A⁻¹ * B⁻¹)) * (A⁻¹ + B⁻¹) := by
    field_simp; ring
  rw [key]
  have n1 : ‖(a - b) * (A⁻¹ * A⁻¹)‖ ≤ L * d * ((c * X)⁻¹ * (c * X)⁻¹) := by
    rw [norm_mul, norm_mul, norm_inv]
    exact mul_le_mul hab (mul_le_mul hAe hAe (by positivity) he) (by positivity) (by positivity)
  have n2 : ‖b * ((B - A) * (A⁻¹ * B⁻¹)) * (A⁻¹ + B⁻¹)‖ ≤
      M * (d * ((c * X)⁻¹ * (c * X)⁻¹)) * ((c * X)⁻¹ + (c * X)⁻¹) := by
    rw [norm_mul, norm_mul, norm_mul, norm_mul, norm_inv, norm_inv, hBA]
    refine mul_le_mul (mul_le_mul hb (mul_le_mul_of_nonneg_left
      (mul_le_mul hAe hBe (by positivity) he) hd) (by positivity) hM) ?_ (norm_nonneg _) (by positivity)
    refine (norm_add_le _ _).trans ?_
    rw [norm_inv, norm_inv]
    exact add_le_add hAe hBe
  have he2 : (c * X)⁻¹ * (c * X)⁻¹ = (c ^ 2)⁻¹ * (X ^ 2)⁻¹ := by simp only [mul_inv]; ring
  have he3 : (c * X)⁻¹ * (c * X)⁻¹ * (c * X)⁻¹ ≤ (c ^ 3)⁻¹ * (X ^ 2)⁻¹ := by
    have : (c * X)⁻¹ * (c * X)⁻¹ * (c * X)⁻¹ = (c ^ 3)⁻¹ * (X ^ 3)⁻¹ := by simp only [mul_inv]; ring
    rw [this]
    exact mul_le_mul_of_nonneg_left (inv_anti₀ (by positivity) (pow_le_pow_right₀ hX (by norm_num)))
      (by positivity)
  calc ‖(a - b) * (A⁻¹ * A⁻¹) + b * ((B - A) * (A⁻¹ * B⁻¹)) * (A⁻¹ + B⁻¹)‖
      ≤ L * d * ((c * X)⁻¹ * (c * X)⁻¹) + M * (d * ((c * X)⁻¹ * (c * X)⁻¹)) * ((c * X)⁻¹ + (c * X)⁻¹) :=
        (norm_add_le _ _).trans (add_le_add n1 n2)
    _ = L * d * ((c * X)⁻¹ * (c * X)⁻¹) + 2 * M * d * ((c * X)⁻¹ * (c * X)⁻¹ * (c * X)⁻¹) := by ring
    _ ≤ L * d * ((c ^ 2)⁻¹ * (X ^ 2)⁻¹) + 2 * M * d * ((c ^ 3)⁻¹ * (X ^ 2)⁻¹) := by
        exact add_le_add (le_of_eq (by rw [he2])) (mul_le_mul_of_nonneg_left he3 (by positivity))
    _ = _ := by ring

/-- (D1) Near `z`: after removing the mean-zero model `\overline{ν(z)}(u - z̄)⁻² \overline{(v - z)⁻²}`, the `v`-kernel is
`O((1 + |u|)⁻² |v - z|⁻¹)` on a disc `B(z, ρ) ⊆ 𝕌`, uniformly in `u ∈ 𝕌` (`ν` is `C¹` at `z`, `e124p_lip`). -/
theorem s71_d1_near {ν ψ : ℂ → ℂ} (hν : IsHarmonicU ν ψ) {z : ℂ} (hz : z ∈ upperHalf) :
    ∃ ρ : ℝ, 0 < ρ ∧ ball z ρ ⊆ upperHalf ∧ ∃ K : ℝ, 0 ≤ K ∧ ∀ u ∈ upperHalf, ∀ v ∈ ball z ρ,
      ‖conj (ν v) / ((u - conj v) ^ 2 * (conj v - conj z) ^ 2) -
          conj (ν z) * ((u - conj z) ^ 2)⁻¹ * conj (((v - z) ^ 2)⁻¹)‖ ≤
        K * ((1 + ‖u‖) ^ 2)⁻¹ * ‖v - z‖⁻¹ := by
  have hz0 : 0 < z.im := hz
  have hU : IsOpen upperHalf := isOpen_lt continuous_const Complex.continuous_im
  have hc1 : ContDiffAt ℝ 1 ν z :=
    ((wr_isHarmonicU_contDiffOn hν).contDiffAt (hU.mem_nhds hz)).of_le (by exact_mod_cast le_top)
  obtain ⟨ρ0, hρ0, L, hL, hlip⟩ := e124p_lip hc1
  obtain ⟨Mν, hMν, hb⟩ := harmonicU_bounded hν
  have ht0 : 0 < z.im / 2 := half_pos hz0
  have hρ : 0 < min ρ0 (z.im / 2) := lt_min hρ0 ht0
  have hc0 : 0 < z.im / 2 / (1 + (‖z‖ + z.im / 2) + z.im / 2) := div_pos ht0 (by positivity)
  have him : ∀ v ∈ ball z (min ρ0 (z.im / 2)), z.im / 2 ≤ v.im ∧ ‖v‖ ≤ ‖z‖ + z.im / 2 := by
    intro v hv
    rw [mem_ball, dist_eq_norm] at hv
    have hv' : ‖v - z‖ < z.im / 2 := hv.trans_le (min_le_right _ _)
    have h1 := Complex.abs_im_le_norm (v - z)
    rw [Complex.sub_im] at h1
    have h2 := neg_abs_le (v.im - z.im)
    have h3 := norm_sub_norm_le v z
    constructor <;> linarith
  have hlow : ∀ u ∈ upperHalf, ∀ w : ℂ, z.im / 2 ≤ w.im → ‖w‖ ≤ ‖z‖ + z.im / 2 →
      z.im / 2 / (1 + (‖z‖ + z.im / 2) + z.im / 2) * (1 + ‖u‖) ≤ ‖u - conj w‖ := by
    intro u hu w hw1 hw2
    have hu0 : 0 < u.im := hu
    have h1 := e64_t10_im (a := conj w) hu0 (by rw [Complex.conj_im]; linarith)
    rw [Complex.conj_im, neg_neg] at h1
    have h2 := e64_t10_lower ht0 (hw1.trans h1)
    rw [Complex.norm_conj] at h2
    refine le_trans (mul_le_mul_of_nonneg_right ?_ (by positivity)) h2
    exact div_le_div_of_nonneg_left ht0.le (by positivity) (by linarith)
  refine ⟨min ρ0 (z.im / 2), hρ, fun v hv => ?_, L * ((z.im / 2 / (1 + (‖z‖ + z.im / 2) + z.im / 2)) ^ 2)⁻¹ +
    2 * Mν * ((z.im / 2 / (1 + (‖z‖ + z.im / 2) + z.im / 2)) ^ 3)⁻¹, by positivity, fun u hu v hv => ?_⟩
  · show 0 < v.im
    linarith [(him v hv).1]
  have e1 : ‖conj v - conj z‖ = ‖v - z‖ := by rw [← map_sub, Complex.norm_conj]
  have em : conj (((v - z) ^ 2)⁻¹) = ((conj v - conj z) ^ 2)⁻¹ := by rw [map_inv₀, map_pow, map_sub]
  have hv0 : v ∈ ball z ρ0 := ball_subset_ball (min_le_left _ _) hv
  have hll := s71_d1_lipalg (a := conj (ν v)) (b := conj (ν z)) hc0 (by linarith [norm_nonneg u] : 1 ≤ 1 + ‖u‖)
    (hlow u hu v (him v hv).1 (him v hv).2)
    (hlow u hu z (by linarith) (by linarith))
    (by rw [← map_sub, Complex.norm_conj]; exact hlip v hv0 z (mem_ball_self hρ0))
    (by rw [Complex.norm_conj]; exact hb z hz)
    (by rw [sub_sub_sub_cancel_left, e1]) hL hMν
  rw [em, div_eq_mul_inv, mul_inv, ← mul_assoc, ← sub_mul, norm_mul, norm_inv, norm_pow, e1]
  have hdd : ‖v - z‖ * (‖v - z‖ ^ 2)⁻¹ = ‖v - z‖⁻¹ := by
    rcases eq_or_ne ‖v - z‖ 0 with h0 | h0
    · rw [h0]; simp
    · field_simp
  calc ‖conj (ν v) * ((u - conj v) ^ 2)⁻¹ - conj (ν z) * ((u - conj z) ^ 2)⁻¹‖ * (‖v - z‖ ^ 2)⁻¹
      ≤ (L * ((z.im / 2 / (1 + (‖z‖ + z.im / 2) + z.im / 2)) ^ 2)⁻¹ +
          2 * Mν * ((z.im / 2 / (1 + (‖z‖ + z.im / 2) + z.im / 2)) ^ 3)⁻¹) * ((1 + ‖u‖) ^ 2)⁻¹ * ‖v - z‖ *
          (‖v - z‖ ^ 2)⁻¹ := mul_le_mul_of_nonneg_right hll (by positivity)
    _ = (L * ((z.im / 2 / (1 + (‖z‖ + z.im / 2) + z.im / 2)) ^ 2)⁻¹ +
          2 * Mν * ((z.im / 2 / (1 + (‖z‖ + z.im / 2) + z.im / 2)) ^ 3)⁻¹) * ((1 + ‖u‖) ^ 2)⁻¹ *
          (‖v - z‖ * (‖v - z‖ ^ 2)⁻¹) := by ring
    _ = _ := by rw [hdd]

/-- (D1) Fubini on `𝕌 × (𝕌 ∖ B(z, δ))`: the truncation of (7.3) at `δ > 0` is `∫_u μ(u)/(u - z̄)² ∫_{𝕌∖B(z,δ)} …`,
and the outer integrand is integrable. -/
theorem s71_d1_fub {μ ν φ ψ : ℂ → ℂ} (hμ : IsHarmonicU μ φ) (hν : IsHarmonicU ν ψ) {z : ℂ} (hz : z ∈ upperHalf)
    {δ : ℝ} (hδ : 0 < δ) :
    Integrable (fun u => μ u / (u - conj z) ^ 2 *
        ∫ v in upperHalf \ ball z δ, conj (ν v) / ((u - conj v) ^ 2 * (conj v - conj z) ^ 2))
        (volume.restrict upperHalf) ∧
      ∫ v in upperHalfPunct z δ, ∫ u in upperHalf,
          μ u * conj (ν v) / ((u - conj z) ^ 2 * (u - conj v) ^ 2 * (conj v - conj z) ^ 2) =
        ∫ u in upperHalf, μ u / (u - conj z) ^ 2 *
          ∫ v in upperHalf \ ball z δ, conj (ν v) / ((u - conj v) ^ 2 * (conj v - conj z) ^ 2) := by
  obtain ⟨M, hM, hcu⟩ := s71_d1_cu hμ hz
  obtain ⟨K, hK, hfar⟩ := s71_d1_far hν (z := z) hδ
  have hmU := measurableSet_upperHalf_aux
  have hmS : MeasurableSet (upperHalf \ ball z δ) := hmU.diff measurableSet_ball
  have hFe : ∀ u v : ℂ, μ u * conj (ν v) / ((u - conj z) ^ 2 * (u - conj v) ^ 2 * (conj v - conj z) ^ 2) =
      μ u / (u - conj z) ^ 2 * (conj (ν v) / ((u - conj v) ^ 2 * (conj v - conj z) ^ 2)) := by
    intro u v; rw [div_mul_div_comm, mul_assoc ((u - conj z) ^ 2)]
  have hm : AEStronglyMeasurable (Function.uncurry fun u v : ℂ =>
      μ u * conj (ν v) / ((u - conj z) ^ 2 * (u - conj v) ^ 2 * (conj v - conj z) ^ 2))
      ((volume.restrict upperHalf).prod (volume.restrict (upperHalf \ ball z δ))) := by
    have h1 : AEStronglyMeasurable μ (volume.restrict upperHalf) :=
      (harmonicU_continuousOn hμ).aestronglyMeasurable hmU
    have h2 : AEStronglyMeasurable (fun v => conj (ν v)) (volume.restrict (upperHalf \ ball z δ)) :=
      (Complex.continuous_conj.comp_continuousOn ((harmonicU_continuousOn hν).mono sdiff_subset)).aestronglyMeasurable
        hmS
    have h3 : Measurable fun p : ℂ × ℂ =>
        ((p.1 - conj z) ^ 2 * (p.1 - conj p.2) ^ 2 * (conj p.2 - conj z) ^ 2)⁻¹ := by fun_prop
    refine ((h1.comp_fst.mul h2.comp_snd).mul h3.aestronglyMeasurable).congr (Eventually.of_forall fun p => ?_)
    simp only [Function.uncurry, Pi.mul_apply, div_eq_mul_inv]
  have hint : Integrable (Function.uncurry fun u v : ℂ =>
      μ u * conj (ν v) / ((u - conj z) ^ 2 * (u - conj v) ^ 2 * (conj v - conj z) ^ 2))
      ((volume.restrict upperHalf).prod (volume.restrict (upperHalf \ ball z δ))) := by
    rw [integrable_prod_iff hm]
    constructor
    · filter_upwards [ae_restrict_mem hmU] with u hu
      refine ((hfar u hu).1.const_mul (μ u / (u - conj z) ^ 2)).congr (Eventually.of_forall fun v => ?_)
      exact (hFe u v).symm
    · refine Integrable.mono' (s71_t_half.const_mul (M * K)) hm.norm.integral_prod_right' ?_
      filter_upwards [ae_restrict_mem hmU] with u hu
      have hu0 : 0 < u.im := hu
      have e : ∫ v in upperHalf \ ball z δ, ‖Function.uncurry (fun u v : ℂ =>
          μ u * conj (ν v) / ((u - conj z) ^ 2 * (u - conj v) ^ 2 * (conj v - conj z) ^ 2)) (u, v)‖ =
          ‖μ u / (u - conj z) ^ 2‖ *
            ∫ v in upperHalf \ ball z δ, ‖conj (ν v) / ((u - conj v) ^ 2 * (conj v - conj z) ^ 2)‖ := by
        rw [← integral_const_mul]
        refine integral_congr_ae (Eventually.of_forall fun v => ?_)
        simp only [Function.uncurry]
        rw [hFe, norm_mul]
      rw [Real.norm_of_nonneg (integral_nonneg fun v => norm_nonneg _), e]
      obtain ⟨h1, -⟩ := s71_d1_alg (X := 1 + ‖u‖) (y := u.im) (by linarith [norm_nonneg u]) hu0
        ((Complex.im_le_norm u).trans (by linarith))
      calc ‖μ u / (u - conj z) ^ 2‖ *
            ∫ v in upperHalf \ ball z δ, ‖conj (ν v) / ((u - conj v) ^ 2 * (conj v - conj z) ^ 2)‖
          ≤ M * ((1 + ‖u‖) ^ 2)⁻¹ * (K * (u.im ^ (-(1 / 2 : ℝ)) * (1 + ‖u‖) ^ (-(1 / 2 : ℝ)))) :=
            mul_le_mul (hcu u hu) (hfar u hu).2 (integral_nonneg fun v => norm_nonneg _) (by positivity)
        _ = M * K * (((1 + ‖u‖) ^ 2)⁻¹ * (1 + ‖u‖) ^ (-(1 / 2 : ℝ))) * u.im ^ (-(1 / 2 : ℝ)) := by ring
        _ = M * K * ((1 + ‖u‖) ^ (-(5 / 2 : ℝ)) * u.im ^ (-(1 / 2 : ℝ))) := by rw [h1]; ring
  have hsw := integral_integral_swap hint
  have hout := hint.integral_prod_left
  have e2 : ∀ u : ℂ, ∫ v in upperHalf \ ball z δ, Function.uncurry (fun u v : ℂ =>
      μ u * conj (ν v) / ((u - conj z) ^ 2 * (u - conj v) ^ 2 * (conj v - conj z) ^ 2)) (u, v) =
      μ u / (u - conj z) ^ 2 *
        ∫ v in upperHalf \ ball z δ, conj (ν v) / ((u - conj v) ^ 2 * (conj v - conj z) ^ 2) := by
    intro u
    rw [← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun v => ?_)
    simp only [Function.uncurry]
    rw [hFe]
  refine ⟨hout.congr (Eventually.of_forall e2), ?_⟩
  show ∫ v in upperHalf \ ball z δ, ∫ u in upperHalf,
      μ u * conj (ν v) / ((u - conj z) ^ 2 * (u - conj v) ^ 2 * (conj v - conj z) ^ 2) = _
  rw [← hsw]
  refine integral_congr_ae (Eventually.of_forall fun u => ?_)
  exact e2 u

/-- **(D1)** `[W2]` **Order swap for (7.3).** `PV_v ∫_u = ∫_u PV_v`. Route: the disc `B(z, δ)` does not depend on `u`, so
Fubini on `𝕌 × (𝕌 ∖ B(z, δ))` (integrable majorants as in E10); then dominated convergence in `u`: the singularity
`\overline{ν(v)}/(v̄ - z̄)²` is isotropic with mean zero on annuli (`e124p_model_zero`, `κ = 0`, conjugated), so the
`v`-truncations are bounded by `C (1 + |u|)⁻²` times a local `C¹` constant, uniformly in `δ`. -/
theorem s71_swap73 {μ ν φ ψ : ℂ → ℂ} (hμ : IsHarmonicU μ φ) (hν : IsHarmonicU ν ψ) {z : ℂ} (hz : z ∈ upperHalf) :
    Tendsto (fun δ : ℝ => ∫ v in upperHalfPunct z δ, ∫ u in upperHalf,
        μ u * conj (ν v) / ((u - conj z) ^ 2 * (u - conj v) ^ 2 * (conj v - conj z) ^ 2)) (𝓝[>] 0)
      (𝓝 (∫ u in upperHalf, μ u / (u - conj z) ^ 2 *
        pv2 (fun v => conj (ν v) / ((u - conj v) ^ 2 * (conj v - conj z) ^ 2)) u z)) := by
  obtain ⟨M, hM, hcu⟩ := s71_d1_cu hμ hz
  obtain ⟨ρ, hρ, hρU, K', hK', hnear⟩ := s71_d1_near hν hz
  obtain ⟨Kρ, hKρ, hfarρ⟩ := s71_d1_far hν (z := z) hρ
  have hmU := measurableSet_upperHalf_aux
  have hI := e124p_invnorm_int z ρ
  have hI0 : 0 ≤ ∫ v in ball z ρ, ‖v - z‖⁻¹ := integral_nonneg fun v => inv_nonneg.mpr (norm_nonneg _)
  -- the mean-zero model `m(v) = \overline{(v - z)⁻²}` on annuli
  have hmod : ∀ δ : ℝ, 0 < δ → δ ≤ ρ →
      IntegrableOn (fun v => conj (((v - z) ^ 2)⁻¹)) (ball z ρ \ ball z δ) ∧
        ∫ v in ball z ρ \ ball z δ, conj (((v - z) ^ 2)⁻¹) = 0 := by
    intro δ hδ hδρ
    obtain ⟨h1, h2⟩ := e124p_model_zero 1 0 z (by simp) hδ hδρ
    simp only [zero_mul, add_zero, one_mul] at h1 h2
    refine ⟨e124a_conj_int h1, ?_⟩
    rw [integral_conj, h2, map_zero]
  -- per-`u` facts
  have hkm : ∀ u : ℂ, AEStronglyMeasurable (fun v => conj (ν v) / ((u - conj v) ^ 2 * (conj v - conj z) ^ 2) -
      conj (ν z) * ((u - conj z) ^ 2)⁻¹ * conj (((v - z) ^ 2)⁻¹)) (volume.restrict (ball z ρ)) := by
    intro u
    have h1 : AEStronglyMeasurable (fun v => conj (ν v)) (volume.restrict (ball z ρ)) :=
      (Complex.continuous_conj.comp_continuousOn ((harmonicU_continuousOn hν).mono hρU)).aestronglyMeasurable
        measurableSet_ball
    have h2 : Measurable fun v : ℂ => ((u - conj v) ^ 2 * (conj v - conj z) ^ 2)⁻¹ := by fun_prop
    have h3 : Measurable fun v : ℂ => conj (ν z) * ((u - conj z) ^ 2)⁻¹ * conj (((v - z) ^ 2)⁻¹) := by fun_prop
    refine ((h1.mul h2.aestronglyMeasurable).sub h3.aestronglyMeasurable).congr
      (Eventually.of_forall fun v => ?_)
    simp only [Pi.mul_apply, Pi.sub_apply, div_eq_mul_inv]
  have hkint : ∀ u ∈ upperHalf, IntegrableOn (fun v => conj (ν v) / ((u - conj v) ^ 2 * (conj v - conj z) ^ 2) -
      conj (ν z) * ((u - conj z) ^ 2)⁻¹ * conj (((v - z) ^ 2)⁻¹)) (ball z ρ) := by
    intro u hu
    refine Integrable.mono' (hI.const_mul (K' * ((1 + ‖u‖) ^ 2)⁻¹)) (hkm u) ?_
    filter_upwards [ae_restrict_mem measurableSet_ball] with v hv
    exact hnear u hu v hv
  have hkbd : ∀ u ∈ upperHalf, ∫ v in ball z ρ, ‖conj (ν v) / ((u - conj v) ^ 2 * (conj v - conj z) ^ 2) -
      conj (ν z) * ((u - conj z) ^ 2)⁻¹ * conj (((v - z) ^ 2)⁻¹)‖ ≤
        K' * ((1 + ‖u‖) ^ 2)⁻¹ * ∫ v in ball z ρ, ‖v - z‖⁻¹ := by
    intro u hu
    rw [← integral_const_mul]
    exact setIntegral_mono_on (hkint u hu).norm (hI.const_mul _) measurableSet_ball (hnear u hu)
  have hfarδ : ∀ u ∈ upperHalf, ∀ δ : ℝ, 0 < δ →
      IntegrableOn (fun v => conj (ν v) / ((u - conj v) ^ 2 * (conj v - conj z) ^ 2)) (upperHalf \ ball z δ) := by
    intro u hu δ hδ
    obtain ⟨K, -, hK⟩ := s71_d1_far hν (z := z) hδ
    exact (hK u hu).1
  -- the decomposition `H_δ = Far + ∫_{B(z,ρ)∖B(z,δ)} k`
  have hpt : ∀ u ∈ upperHalf, ∀ δ : ℝ, 0 < δ → δ ≤ ρ →
      ∫ v in upperHalf \ ball z δ, conj (ν v) / ((u - conj v) ^ 2 * (conj v - conj z) ^ 2) =
        (∫ v in upperHalf \ ball z ρ, conj (ν v) / ((u - conj v) ^ 2 * (conj v - conj z) ^ 2)) +
          ∫ v in ball z ρ \ ball z δ, (conj (ν v) / ((u - conj v) ^ 2 * (conj v - conj z) ^ 2) -
            conj (ν z) * ((u - conj z) ^ 2)⁻¹ * conj (((v - z) ^ 2)⁻¹)) := by
    intro u hu δ hδ hδρ
    have hset : upperHalf \ ball z δ = (upperHalf \ ball z ρ) ∪ (ball z ρ \ ball z δ) := by
      ext v
      simp only [Set.mem_sdiff, mem_union]
      constructor
      · rintro ⟨hv, hvδ⟩
        by_cases hvρ : v ∈ ball z ρ
        · exact Or.inr ⟨hvρ, hvδ⟩
        · exact Or.inl ⟨hv, hvρ⟩
      · rintro (⟨hv, hvρ⟩ | ⟨hvρ, hvδ⟩)
        · exact ⟨hv, fun h => hvρ (ball_subset_ball hδρ h)⟩
        · exact ⟨hρU hvρ, hvδ⟩
    have hdis : Disjoint (upperHalf \ ball z ρ) (ball z ρ \ ball z δ) :=
      Set.disjoint_left.mpr fun v h1 h2 => h1.2 h2.1
    have hsub : ball z ρ \ ball z δ ⊆ upperHalf \ ball z δ := fun v hv => ⟨hρU hv.1, hv.2⟩
    rw [hset, setIntegral_union hdis (measurableSet_ball.diff measurableSet_ball) (hfarρ u hu).1
      ((hfarδ u hu δ hδ).mono_set (hset ▸ subset_union_right))]
    congr 1
    obtain ⟨hm1, hm2⟩ := hmod δ hδ hδρ
    rw [integral_sub ((hfarδ u hu δ hδ).mono_set hsub) (hm1.const_mul _), integral_const_mul, hm2, mul_zero,
      sub_zero]
  -- pointwise limit and identification with `pv2`
  have hlim : ∀ u ∈ upperHalf, Tendsto (fun δ : ℝ =>
      ∫ v in upperHalf \ ball z δ, conj (ν v) / ((u - conj v) ^ 2 * (conj v - conj z) ^ 2)) (𝓝[>] 0)
      (𝓝 ((∫ v in upperHalf \ ball z ρ, conj (ν v) / ((u - conj v) ^ 2 * (conj v - conj z) ^ 2)) +
        ∫ v in ball z ρ, (conj (ν v) / ((u - conj v) ^ 2 * (conj v - conj z) ^ 2) -
          conj (ν z) * ((u - conj z) ^ 2)⁻¹ * conj (((v - z) ^ 2)⁻¹)))) := by
    intro u hu
    have ht := e124p_rem_tendsto (hkint u hu) (X := fun δ => ball z δ) (fun δ => measurableSet_ball)
      (fun v hv => e124a_far hv)
    refine (tendsto_const_nhds.add ht).congr' ?_
    filter_upwards [Ioo_mem_nhdsGT hρ] with δ hδ
    exact (hpt u hu δ hδ.1 hδ.2.le).symm
  have hpv : ∀ u ∈ upperHalf,
      pv2 (fun v => conj (ν v) / ((u - conj v) ^ 2 * (conj v - conj z) ^ 2)) u z =
        (∫ v in upperHalf \ ball z ρ, conj (ν v) / ((u - conj v) ^ 2 * (conj v - conj z) ^ 2)) +
          ∫ v in ball z ρ, (conj (ν v) / ((u - conj v) ^ 2 * (conj v - conj z) ^ 2) -
            conj (ν z) * ((u - conj z) ^ 2)⁻¹ * conj (((v - z) ^ 2)⁻¹)) := by
    intro u hu
    have t2 := e124a_pv1g (u := u) (hlim u hu) (hfarδ u hu)
    simp only [union_comm (ball z _) (ball u _)] at t2
    exact t2.limUnder_eq
  -- dominated convergence in `u`
  have hdct : Tendsto (fun δ : ℝ => ∫ u in upperHalf, μ u / (u - conj z) ^ 2 *
      ∫ v in upperHalf \ ball z δ, conj (ν v) / ((u - conj v) ^ 2 * (conj v - conj z) ^ 2)) (𝓝[>] 0)
      (𝓝 (∫ u in upperHalf, μ u / (u - conj z) ^ 2 *
        pv2 (fun v => conj (ν v) / ((u - conj v) ^ 2 * (conj v - conj z) ^ 2)) u z)) := by
    refine tendsto_integral_filter_of_dominated_convergence
      (fun u => (M * Kρ + M * K' * ∫ v in ball z ρ, ‖v - z‖⁻¹) *
        ((1 + ‖u‖) ^ (-(5 / 2 : ℝ)) * u.im ^ (-(1 / 2 : ℝ)))) ?_ ?_ (s71_t_half.const_mul _) ?_
    · filter_upwards [self_mem_nhdsWithin] with δ hδ
      exact (s71_d1_fub hμ hν hz hδ).1.aestronglyMeasurable
    · filter_upwards [Ioo_mem_nhdsGT hρ] with δ hδ
      filter_upwards [ae_restrict_mem hmU] with u hu
      have hu0 : 0 < u.im := hu
      obtain ⟨h1, h2⟩ := s71_d1_alg (X := 1 + ‖u‖) (y := u.im) (by linarith [norm_nonneg u]) hu0
        ((Complex.im_le_norm u).trans (by linarith))
      have hsub : ball z ρ \ ball z δ ⊆ ball z ρ := sdiff_subset
      have hN : ‖∫ v in ball z ρ \ ball z δ, (conj (ν v) / ((u - conj v) ^ 2 * (conj v - conj z) ^ 2) -
          conj (ν z) * ((u - conj z) ^ 2)⁻¹ * conj (((v - z) ^ 2)⁻¹))‖ ≤
            K' * ((1 + ‖u‖) ^ 2)⁻¹ * ∫ v in ball z ρ, ‖v - z‖⁻¹ :=
        (norm_integral_le_integral_norm _).trans ((setIntegral_mono_set (hkint u hu).norm
          (Eventually.of_forall fun v => norm_nonneg _) hsub.eventuallyLE).trans (hkbd u hu))
      have hF : ‖∫ v in upperHalf \ ball z ρ, conj (ν v) / ((u - conj v) ^ 2 * (conj v - conj z) ^ 2)‖ ≤
          Kρ * (u.im ^ (-(1 / 2 : ℝ)) * (1 + ‖u‖) ^ (-(1 / 2 : ℝ))) :=
        (norm_integral_le_integral_norm _).trans (hfarρ u hu).2
      rw [hpt u hu δ hδ.1 hδ.2.le, norm_mul]
      have hA := (norm_add_le _ _).trans (add_le_add hF hN)
      calc ‖μ u / (u - conj z) ^ 2‖ * ‖(∫ v in upperHalf \ ball z ρ,
            conj (ν v) / ((u - conj v) ^ 2 * (conj v - conj z) ^ 2)) +
            ∫ v in ball z ρ \ ball z δ, (conj (ν v) / ((u - conj v) ^ 2 * (conj v - conj z) ^ 2) -
              conj (ν z) * ((u - conj z) ^ 2)⁻¹ * conj (((v - z) ^ 2)⁻¹))‖
          ≤ M * ((1 + ‖u‖) ^ 2)⁻¹ * (Kρ * (u.im ^ (-(1 / 2 : ℝ)) * (1 + ‖u‖) ^ (-(1 / 2 : ℝ))) +
              K' * ((1 + ‖u‖) ^ 2)⁻¹ * ∫ v in ball z ρ, ‖v - z‖⁻¹) :=
            mul_le_mul (hcu u hu) hA (norm_nonneg _) (by positivity)
        _ = M * Kρ * (((1 + ‖u‖) ^ 2)⁻¹ * (1 + ‖u‖) ^ (-(1 / 2 : ℝ))) * u.im ^ (-(1 / 2 : ℝ)) +
              M * K' * (∫ v in ball z ρ, ‖v - z‖⁻¹) * (((1 + ‖u‖) ^ 2)⁻¹ * ((1 + ‖u‖) ^ 2)⁻¹) := by ring
        _ ≤ M * Kρ * (1 + ‖u‖) ^ (-(5 / 2 : ℝ)) * u.im ^ (-(1 / 2 : ℝ)) +
              M * K' * (∫ v in ball z ρ, ‖v - z‖⁻¹) * ((1 + ‖u‖) ^ (-(5 / 2 : ℝ)) * u.im ^ (-(1 / 2 : ℝ))) := by
            rw [h1]
            exact add_le_add le_rfl (mul_le_mul_of_nonneg_left h2 (by positivity))
        _ = _ := by ring
    · filter_upwards [ae_restrict_mem hmU] with u hu
      rw [hpv u hu]
      exact tendsto_const_nhds.mul (hlim u hu)
  refine hdct.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  exact ((s71_d1_fub hμ hν hz hδ).2).symm

/-! ### (D2) helpers `[W6]` -/

/-- The four-term identity behind (7.5) (TT:2735, from (6.5)). -/
theorem s71_r75_four {u v z : ℂ} (h1 : u - conj z ≠ 0) (h2 : u - conj v ≠ 0) (h3 : conj v - conj z ≠ 0)
    (h4 : conj v - z ≠ 0) :
    1 / ((u - conj z) ^ 2 * (u - conj v) ^ 2 * (conj v - conj z) ^ 2) =
      (u - z) ^ 2 / ((u - conj z) ^ 4 * (conj v - z) ^ 2 * (u - conj v) ^ 2) +
        (z - conj z) ^ 2 / ((u - conj z) ^ 4 * (conj v - conj z) ^ 2 * (conj v - z) ^ 2) +
        2 * (z - conj z) ^ 2 * (z - u) / ((u - conj z) ^ 5 * (z - conj v) ^ 3 * (conj v - conj z)) +
        2 * (z - conj z) * (z - u) ^ 2 / ((u - conj z) ^ 5 * (z - conj v) ^ 3 * (u - conj v)) := by
  have h5 : z - conj v ≠ 0 := fun h => h4 (by linear_combination -h)
  field_simp
  ring

/-- `|u - z| ≤ |u - z̄|` for `u, z ∈ 𝕌`. -/
theorem s71_r75_le_conj {u z : ℂ} (hu : u ∈ upperHalf) (hz : z ∈ upperHalf) : ‖u - z‖ ≤ ‖u - conj z‖ := by
  have hu' : 0 < u.im := hu
  have hz' : 0 < z.im := hz
  rw [← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _), ← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq]
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.conj_re, Complex.conj_im]
  nlinarith [mul_pos hu' hz']

/-- A linear lower bound `c (1 + |u|) ≤ |u - a|` on `𝕌` for a point `a` of `𝕃`. -/
theorem s71_r75_lower {a : ℂ} (ha : a.im < 0) :
    ∃ c : ℝ, 0 < c ∧ ∀ u ∈ upperHalf, c * (1 + ‖u‖) ≤ ‖u - a‖ := by
  refine ⟨-a.im / (1 + ‖a‖ + -a.im), div_pos (by linarith) (by have := norm_nonneg a; linarith), fun u hu => ?_⟩
  exact e64_t10_lower (by linarith) (e64_t10_im hu ha)

/-- A function continuous on `𝕌` and `O((1 + |u|)⁻⁴)` there is integrable on `𝕌`. -/
theorem s71_r75_int4 {f : ℂ → ℂ} (hf : ContinuousOn f upperHalf) {K : ℝ}
    (hK : ∀ u ∈ upperHalf, ‖f u‖ ≤ K * ((1 + ‖u‖) ^ 4)⁻¹) : IntegrableOn f upperHalf := by
  have hU := measurableSet_upperHalf_aux
  have hmaj := (e64_t5_maj 0).1
  simp only [sub_zero] at hmaj
  refine (hmaj.const_mul K).integrableOn.mono' (hf.aestronglyMeasurable hU) ?_
  filter_upwards [ae_restrict_mem hU] with u hu
  exact hK u hu

/-- The real inequality behind `s71_r75_pbd`. -/
theorem s71_r75_real {p a b w₁ w₂ s d X Y c : ℝ} (hp : 0 ≤ p) (hpa : p ≤ a) (hc : 0 < c) (hX : 1 ≤ X)
    (ha : c * X ≤ a) (hb : 0 < b) (hba : b ≤ a + d) (hw₁ : 0 < w₁) (hw₂ : 0 < w₂) (hs : 0 ≤ s) (hd : 0 ≤ d)
    (hY : 1 / b ^ 2 ≤ Y) :
    p ^ 2 / (a ^ 4 * w₁ ^ 2 * b ^ 2) + 2 * s * p ^ 2 / (a ^ 5 * w₂ ^ 3 * b) ≤
      ((c ^ 2)⁻¹ * (w₁ ^ 2)⁻¹ + 2 * s * (w₂ ^ 3)⁻¹ * ((c ^ 2)⁻¹ + d * (c ^ 3)⁻¹)) * (Y * (X ^ 2)⁻¹) := by
  have hX0 : 0 < X := by linarith
  have hcX : 0 < c * X := by positivity
  have ha0 : 0 < a := lt_of_lt_of_le hcX ha
  have hY0 : 0 ≤ Y := le_trans (by positivity) hY
  have hpa2 : p ^ 2 ≤ a ^ 2 := pow_le_pow_left₀ hp hpa 2
  -- the two inverse powers of `a`
  have hA2 : (a ^ 2)⁻¹ ≤ (c ^ 2)⁻¹ * (X ^ 2)⁻¹ := by
    rw [← mul_inv, ← mul_pow]
    exact inv_anti₀ (by positivity) (pow_le_pow_left₀ hcX.le ha 2)
  have hA3 : (a ^ 3)⁻¹ ≤ (c ^ 3)⁻¹ * (X ^ 2)⁻¹ := by
    have h1 : (a ^ 3)⁻¹ ≤ ((c * X) ^ 3)⁻¹ := inv_anti₀ (by positivity) (pow_le_pow_left₀ hcX.le ha 3)
    have h2 : ((c * X) ^ 3)⁻¹ ≤ (c ^ 3)⁻¹ * (X ^ 2)⁻¹ := by
      rw [mul_pow, mul_inv]
      refine mul_le_mul_of_nonneg_left (inv_anti₀ (by positivity) ?_) (by positivity)
      nlinarith [pow_pos hX0 2]
    exact h1.trans h2
  have hT1 : p ^ 2 / (a ^ 4 * w₁ ^ 2 * b ^ 2) ≤ (a ^ 2)⁻¹ * (w₁ ^ 2)⁻¹ * (1 / b ^ 2) := by
    rw [div_le_iff₀ (by positivity)]
    calc p ^ 2 ≤ a ^ 2 := hpa2
      _ = (a ^ 2)⁻¹ * (w₁ ^ 2)⁻¹ * (1 / b ^ 2) * (a ^ 4 * w₁ ^ 2 * b ^ 2) := by field_simp
  have hinvb : 1 / b ≤ (a + d) * Y := by
    calc 1 / b = b * (1 / b ^ 2) := by field_simp
      _ ≤ (a + d) * Y := mul_le_mul hba hY (by positivity) (by linarith)
  have hT4 : 2 * s * p ^ 2 / (a ^ 5 * w₂ ^ 3 * b) ≤
      2 * s * (w₂ ^ 3)⁻¹ * ((a ^ 2)⁻¹ + d * (a ^ 3)⁻¹) * Y := by
    calc 2 * s * p ^ 2 / (a ^ 5 * w₂ ^ 3 * b) ≤ 2 * s * a ^ 2 / (a ^ 5 * w₂ ^ 3 * b) := by gcongr
      _ = 2 * s * (w₂ ^ 3)⁻¹ * (a ^ 3)⁻¹ * (1 / b) := by field_simp
      _ ≤ 2 * s * (w₂ ^ 3)⁻¹ * (a ^ 3)⁻¹ * ((a + d) * Y) := by gcongr
      _ = 2 * s * (w₂ ^ 3)⁻¹ * ((a ^ 2)⁻¹ + d * (a ^ 3)⁻¹) * Y := by field_simp
  calc p ^ 2 / (a ^ 4 * w₁ ^ 2 * b ^ 2) + 2 * s * p ^ 2 / (a ^ 5 * w₂ ^ 3 * b)
      ≤ (a ^ 2)⁻¹ * (w₁ ^ 2)⁻¹ * Y + 2 * s * (w₂ ^ 3)⁻¹ * ((a ^ 2)⁻¹ + d * (a ^ 3)⁻¹) * Y := by
        refine add_le_add (hT1.trans ?_) hT4
        exact mul_le_mul_of_nonneg_left hY (by positivity)
    _ ≤ (c ^ 2)⁻¹ * (X ^ 2)⁻¹ * (w₁ ^ 2)⁻¹ * Y +
          2 * s * (w₂ ^ 3)⁻¹ * ((c ^ 2)⁻¹ * (X ^ 2)⁻¹ + d * ((c ^ 3)⁻¹ * (X ^ 2)⁻¹)) * Y := by
        gcongr
    _ = ((c ^ 2)⁻¹ * (w₁ ^ 2)⁻¹ + 2 * s * (w₂ ^ 3)⁻¹ * ((c ^ 2)⁻¹ + d * (c ^ 3)⁻¹)) * (Y * (X ^ 2)⁻¹) := by
        ring

/-- **Pointwise bound** for the regular kernel `T₁ + T₄` of (7.5), in the form of `s71_t_im`/`s71_t_conv`:
`|T₁ + T₄| ≤ E(v) (Im v)^{-1/2} (1 + |u|)⁻² |u - v̄|^{-3/2}`. -/
theorem s71_r75_pbd {z : ℂ} (hz : z ∈ upperHalf) {c : ℝ} (hc : 0 < c)
    (hlz : ∀ u ∈ upperHalf, c * (1 + ‖u‖) ≤ ‖u - conj z‖) {u v : ℂ} (hu : u ∈ upperHalf) (hv : v ∈ upperHalf) :
    ‖(u - z) ^ 2 / ((u - conj z) ^ 4 * (conj v - z) ^ 2 * (u - conj v) ^ 2) +
        2 * (z - conj z) * (z - u) ^ 2 / ((u - conj z) ^ 5 * (z - conj v) ^ 3 * (u - conj v))‖ ≤
      ((c ^ 2)⁻¹ * (‖conj v - z‖ ^ 2)⁻¹ + 2 * ‖z - conj z‖ * (‖z - conj v‖ ^ 3)⁻¹ *
        ((c ^ 2)⁻¹ + ‖z - v‖ * (c ^ 3)⁻¹)) *
        (v.im ^ (-(1 / 2 : ℝ)) * ‖u - conj v‖ ^ (-(3 / 2 : ℝ)) * ((1 + ‖u‖) ^ 2)⁻¹) := by
  have hvi : 0 < v.im := hv
  have hb : 0 < ‖u - conj v‖ := norm_pos_iff.2 (eq_7_4_sub_conj_ne_zero hu hv)
  have hw₁ : 0 < ‖conj v - z‖ :=
    norm_pos_iff.2 fun h => eq_7_4_sub_conj_ne_zero hz hv (by linear_combination -h)
  have hw₂ : 0 < ‖z - conj v‖ := norm_pos_iff.2 (eq_7_4_sub_conj_ne_zero hz hv)
  have hba : ‖u - conj v‖ ≤ ‖u - conj z‖ + ‖z - v‖ := by
    calc ‖u - conj v‖ = ‖(u - conj z) + conj (z - v)‖ := by rw [map_sub]; ring_nf
      _ ≤ ‖u - conj z‖ + ‖conj (z - v)‖ := norm_add_le _ _
      _ = ‖u - conj z‖ + ‖z - v‖ := by rw [Complex.norm_conj]
  have hpa : ‖z - u‖ ≤ ‖u - conj z‖ := by rw [norm_sub_rev]; exact s71_r75_le_conj hu hz
  have hY := s71_t_im (le_of_lt hu) hv
  refine (norm_add_le _ _).trans ?_
  have e1 : ‖(u - z) ^ 2 / ((u - conj z) ^ 4 * (conj v - z) ^ 2 * (u - conj v) ^ 2)‖ =
      ‖z - u‖ ^ 2 / (‖u - conj z‖ ^ 4 * ‖conj v - z‖ ^ 2 * ‖u - conj v‖ ^ 2) := by
    rw [norm_sub_rev z u]; simp only [norm_div, norm_mul, norm_pow]
  have e2 : ‖2 * (z - conj z) * (z - u) ^ 2 / ((u - conj z) ^ 5 * (z - conj v) ^ 3 * (u - conj v))‖ =
      2 * ‖z - conj z‖ * ‖z - u‖ ^ 2 / (‖u - conj z‖ ^ 5 * ‖z - conj v‖ ^ 3 * ‖u - conj v‖) := by
    simp only [norm_div, norm_mul, norm_pow, Complex.norm_ofNat]
  rw [e1, e2]
  have h := s71_r75_real (norm_nonneg (z - u)) hpa hc (by linarith [norm_nonneg u]) (hlz u hu) hb hba hw₁ hw₂
    (norm_nonneg (z - conj z)) (norm_nonneg (z - v)) hY
  refine h.trans (le_of_eq ?_)
  ring

/-- `v ↦ ∫_𝕌 μ(u) \overline{ν(v)} (T₁ + T₄)` is integrable on `𝕌` (it is `O(log(1/Im v))` near `∂𝕌`): the bound
`s71_r75_pbd`, `s71_t_conv` in `u`, and `s71_t_half` in `v`. Also the `u`-integrability for each `v`. -/
theorem s71_r75_Hint {μ ν φ ψ : ℂ → ℂ} (hμ : IsHarmonicU μ φ) (hν : IsHarmonicU ν ψ) {z : ℂ}
    (hz : z ∈ upperHalf) :
    (∀ v ∈ upperHalf, IntegrableOn (fun u => μ u * conj (ν v) *
        ((u - z) ^ 2 / ((u - conj z) ^ 4 * (conj v - z) ^ 2 * (u - conj v) ^ 2) +
          2 * (z - conj z) * (z - u) ^ 2 / ((u - conj z) ^ 5 * (z - conj v) ^ 3 * (u - conj v)))) upperHalf) ∧
      IntegrableOn (fun v => ∫ u in upperHalf, μ u * conj (ν v) *
        ((u - z) ^ 2 / ((u - conj z) ^ 4 * (conj v - z) ^ 2 * (u - conj v) ^ 2) +
          2 * (z - conj z) * (z - u) ^ 2 / ((u - conj z) ^ 5 * (z - conj v) ^ 3 * (u - conj v)))) upperHalf := by
  have hU := measurableSet_upperHalf_aux
  obtain ⟨M, hM0, hM⟩ := harmonicU_bounded hμ
  obtain ⟨N, hN0, hN⟩ := harmonicU_bounded hν
  have hμc := harmonicU_continuousOn hμ
  have hνc := harmonicU_continuousOn hν
  have hzi : 0 < z.im := hz
  obtain ⟨c, hc, hlz⟩ := s71_r75_lower (a := conj z) (by rw [Complex.conj_im]; linarith)
  obtain ⟨Ct, hCt0, hCt⟩ := s71_t_conv
  -- the kernel and its `v`-coefficient
  obtain ⟨T, hT⟩ : ∃ T : ℂ → ℂ → ℂ, T = fun u v =>
      (u - z) ^ 2 / ((u - conj z) ^ 4 * (conj v - z) ^ 2 * (u - conj v) ^ 2) +
        2 * (z - conj z) * (z - u) ^ 2 / ((u - conj z) ^ 5 * (z - conj v) ^ 3 * (u - conj v)) := ⟨_, rfl⟩
  obtain ⟨E, hE⟩ : ∃ E : ℂ → ℝ, E = fun v => (c ^ 2)⁻¹ * (‖conj v - z‖ ^ 2)⁻¹ + 2 * ‖z - conj z‖ *
      (‖z - conj v‖ ^ 3)⁻¹ * ((c ^ 2)⁻¹ + ‖z - v‖ * (c ^ 3)⁻¹) := ⟨_, rfl⟩
  have hE0 : ∀ v, 0 ≤ E v := fun v => by rw [hE]; positivity
  have hpbd : ∀ u ∈ upperHalf, ∀ v ∈ upperHalf, ‖T u v‖ ≤
      E v * (v.im ^ (-(1 / 2 : ℝ)) * ‖u - conj v‖ ^ (-(3 / 2 : ℝ)) * ((1 + ‖u‖) ^ 2)⁻¹) := by
    intro u hu v hv
    rw [hT, hE]
    exact s71_r75_pbd hz hc hlz hu hv
  have hne : ∀ u ∈ upperHalf, ∀ v ∈ upperHalf,
      (u - conj z) ^ 4 * (conj v - z) ^ 2 * (u - conj v) ^ 2 ≠ 0 ∧
        (u - conj z) ^ 5 * (z - conj v) ^ 3 * (u - conj v) ≠ 0 := by
    intro u hu v hv
    have h1 := eq_7_4_sub_conj_ne_zero hu hz
    have h2 := eq_7_4_sub_conj_ne_zero hu hv
    have h3 := eq_7_4_sub_conj_ne_zero hz hv
    have h4 : conj v - z ≠ 0 := fun h => h3 (by linear_combination -h)
    exact ⟨by positivity, by positivity⟩
  -- the `u`-majorant at fixed `v`
  have hgint : ∀ v : ℂ, IntegrableOn (fun u => ((1 + ‖u‖) ^ 2)⁻¹ * ‖u - conj v‖ ^ (-(3 / 2 : ℝ))) upperHalf :=
    fun v => ((hCt (conj v)).1).integrableOn
  have hFu : ∀ v ∈ upperHalf, IntegrableOn (fun u => μ u * conj (ν v) * T u v) upperHalf := by
    intro v hv
    refine (((hgint v).const_mul (M * N * E v * v.im ^ (-(1 / 2 : ℝ))))).mono' ?_ ?_
    · refine ContinuousOn.aestronglyMeasurable ?_ hU
      refine (hμc.mul continuousOn_const).mul ?_
      rw [hT]
      refine ContinuousOn.add ?_ ?_
      · exact (Continuous.continuousOn (by fun_prop)).div (Continuous.continuousOn (by fun_prop))
          fun u hu => (hne u hu v hv).1
      · exact (Continuous.continuousOn (by fun_prop)).div (Continuous.continuousOn (by fun_prop))
          fun u hu => (hne u hu v hv).2
    · filter_upwards [ae_restrict_mem hU] with u hu
      rw [norm_mul, norm_mul, Complex.norm_conj]
      calc ‖μ u‖ * ‖ν v‖ * ‖T u v‖ ≤ M * N * (E v * (v.im ^ (-(1 / 2 : ℝ)) * ‖u - conj v‖ ^ (-(3 / 2 : ℝ)) *
            ((1 + ‖u‖) ^ 2)⁻¹)) :=
          mul_le_mul (mul_le_mul (hM u hu) (hN v hv) (norm_nonneg _) hM0) (hpbd u hu v hv) (norm_nonneg _)
            (by positivity)
        _ = M * N * E v * v.im ^ (-(1 / 2 : ℝ)) * (((1 + ‖u‖) ^ 2)⁻¹ * ‖u - conj v‖ ^ (-(3 / 2 : ℝ))) := by ring
  refine ⟨fun v hv => by simpa only [hT] using hFu v hv, ?_⟩
  suffices key : IntegrableOn (fun v => ∫ u in upperHalf, μ u * conj (ν v) * T u v) upperHalf by
    simpa only [hT] using key
  -- measurability of the parametric integral
  have hmeas : AEStronglyMeasurable (fun v => ∫ u in upperHalf, μ u * conj (ν v) * T u v)
      (volume.restrict upperHalf) := by
    have hF : ContinuousOn (fun p : ℂ × ℂ => μ p.2 * conj (ν p.1) * T p.2 p.1) (upperHalf ×ˢ upperHalf) := by
      have h1 : ContinuousOn (fun p : ℂ × ℂ => μ p.2) (upperHalf ×ˢ upperHalf) :=
        hμc.comp continuousOn_snd fun p hp => hp.2
      have h2 : ContinuousOn (fun p : ℂ × ℂ => conj (ν p.1)) (upperHalf ×ˢ upperHalf) :=
        Complex.continuous_conj.comp_continuousOn (hνc.comp continuousOn_fst fun p hp => hp.1)
      refine (h1.mul h2).mul ?_
      rw [hT]
      refine ContinuousOn.add ?_ ?_
      · exact (Continuous.continuousOn (by fun_prop)).div (Continuous.continuousOn (by fun_prop))
          fun p hp => (hne p.2 hp.2 p.1 hp.1).1
      · exact (Continuous.continuousOn (by fun_prop)).div (Continuous.continuousOn (by fun_prop))
          fun p hp => (hne p.2 hp.2 p.1 hp.1).2
    have h' : AEStronglyMeasurable (fun p : ℂ × ℂ => μ p.2 * conj (ν p.1) * T p.2 p.1)
        ((volume.restrict upperHalf).prod (volume.restrict upperHalf)) := by
      rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
      exact hF.aestronglyMeasurable (hU.prod hU)
    exact h'.integral_prod_right'
  -- the `v`-majorant
  set E₀ : ℝ := (c ^ 2)⁻¹ * (c ^ 2)⁻¹ + 2 * ‖z - conj z‖ * (c ^ 3)⁻¹ * ((c ^ 2)⁻¹ + (1 + ‖z‖) * (c ^ 3)⁻¹)
    with hE₀
  have hEv : ∀ v ∈ upperHalf, E v ≤ E₀ * ((1 + ‖v‖) ^ 2)⁻¹ := by
    intro v hv
    have hX : 1 ≤ 1 + ‖v‖ := by linarith [norm_nonneg v]
    have hw : c * (1 + ‖v‖) ≤ ‖conj v - z‖ := by
      calc c * (1 + ‖v‖) ≤ ‖v - conj z‖ := hlz v hv
        _ = ‖conj v - z‖ := by rw [← Complex.norm_conj (v - conj z), map_sub, Complex.conj_conj]
    have hw' : c * (1 + ‖v‖) ≤ ‖z - conj v‖ := by rw [norm_sub_rev]; exact hw
    have hd : ‖z - v‖ ≤ (1 + ‖z‖) * (1 + ‖v‖) := by
      have := norm_sub_le z v
      nlinarith [norm_nonneg z, norm_nonneg v]
    have hcX : 0 < c * (1 + ‖v‖) := by positivity
    have i2 : (‖conj v - z‖ ^ 2)⁻¹ ≤ (c ^ 2)⁻¹ * ((1 + ‖v‖) ^ 2)⁻¹ := by
      rw [← mul_inv, ← mul_pow]; exact inv_anti₀ (by positivity) (pow_le_pow_left₀ hcX.le hw 2)
    have i3 : (‖z - conj v‖ ^ 3)⁻¹ ≤ (c ^ 3)⁻¹ * ((1 + ‖v‖) ^ 3)⁻¹ := by
      rw [← mul_inv, ← mul_pow]; exact inv_anti₀ (by positivity) (pow_le_pow_left₀ hcX.le hw' 3)
    have i32 : ((1 + ‖v‖) ^ 3)⁻¹ ≤ ((1 + ‖v‖) ^ 2)⁻¹ :=
      inv_anti₀ (by positivity) (pow_le_pow_right₀ hX (by norm_num))
    have i31 : ((1 + ‖v‖) ^ 3)⁻¹ * ‖z - v‖ ≤ (1 + ‖z‖) * ((1 + ‖v‖) ^ 2)⁻¹ := by
      have hp : (0 : ℝ) < 1 + ‖v‖ := by linarith
      rw [show ((1 + ‖v‖) ^ 3)⁻¹ * ‖z - v‖ = ‖z - v‖ / (1 + ‖v‖) ^ 3 by ring,
        div_le_iff₀ (by positivity)]
      calc ‖z - v‖ ≤ (1 + ‖z‖) * (1 + ‖v‖) := hd
        _ = (1 + ‖z‖) * ((1 + ‖v‖) ^ 2)⁻¹ * (1 + ‖v‖) ^ 3 := by field_simp
    rw [hE]
    calc (c ^ 2)⁻¹ * (‖conj v - z‖ ^ 2)⁻¹ + 2 * ‖z - conj z‖ * (‖z - conj v‖ ^ 3)⁻¹ *
          ((c ^ 2)⁻¹ + ‖z - v‖ * (c ^ 3)⁻¹)
        ≤ (c ^ 2)⁻¹ * ((c ^ 2)⁻¹ * ((1 + ‖v‖) ^ 2)⁻¹) + 2 * ‖z - conj z‖ * ((c ^ 3)⁻¹ * ((1 + ‖v‖) ^ 3)⁻¹) *
          ((c ^ 2)⁻¹ + ‖z - v‖ * (c ^ 3)⁻¹) := by gcongr
      _ = (c ^ 2)⁻¹ * (c ^ 2)⁻¹ * ((1 + ‖v‖) ^ 2)⁻¹ + 2 * ‖z - conj z‖ * (c ^ 3)⁻¹ *
          ((c ^ 2)⁻¹ * ((1 + ‖v‖) ^ 3)⁻¹ + (((1 + ‖v‖) ^ 3)⁻¹ * ‖z - v‖) * (c ^ 3)⁻¹) := by ring
      _ ≤ (c ^ 2)⁻¹ * (c ^ 2)⁻¹ * ((1 + ‖v‖) ^ 2)⁻¹ + 2 * ‖z - conj z‖ * (c ^ 3)⁻¹ *
          ((c ^ 2)⁻¹ * ((1 + ‖v‖) ^ 2)⁻¹ + ((1 + ‖z‖) * ((1 + ‖v‖) ^ 2)⁻¹) * (c ^ 3)⁻¹) := by gcongr
      _ = E₀ * ((1 + ‖v‖) ^ 2)⁻¹ := by rw [hE₀]; ring
  have hhalf := s71_t_half
  refine (hhalf.const_mul (M * N * E₀ * Ct)).mono' hmeas ?_
  filter_upwards [ae_restrict_mem hU] with v hv
  have hvi : 0 < v.im := hv
  have hX : (0 : ℝ) < 1 + ‖v‖ := by linarith [norm_nonneg v]
  have hI : ‖∫ u in upperHalf, μ u * conj (ν v) * T u v‖ ≤
      M * N * E v * v.im ^ (-(1 / 2 : ℝ)) * (Ct * (1 + ‖v‖) ^ (-(1 / 2 : ℝ))) := by
    refine (norm_integral_le_of_norm_le (((hgint v).const_mul (M * N * E v * v.im ^ (-(1 / 2 : ℝ)))))
      ?_).trans ?_
    · filter_upwards [ae_restrict_mem hU] with u hu
      rw [norm_mul, norm_mul, Complex.norm_conj]
      calc ‖μ u‖ * ‖ν v‖ * ‖T u v‖ ≤ M * N * (E v * (v.im ^ (-(1 / 2 : ℝ)) * ‖u - conj v‖ ^ (-(3 / 2 : ℝ)) *
            ((1 + ‖u‖) ^ 2)⁻¹)) :=
          mul_le_mul (mul_le_mul (hM u hu) (hN v hv) (norm_nonneg _) hM0) (hpbd u hu v hv) (norm_nonneg _)
            (by positivity)
        _ = M * N * E v * v.im ^ (-(1 / 2 : ℝ)) * (((1 + ‖u‖) ^ 2)⁻¹ * ‖u - conj v‖ ^ (-(3 / 2 : ℝ))) := by ring
    · rw [integral_const_mul]
      refine mul_le_mul_of_nonneg_left ?_ (by have := hE0 v; positivity)
      calc (∫ u in upperHalf, ((1 + ‖u‖) ^ 2)⁻¹ * ‖u - conj v‖ ^ (-(3 / 2 : ℝ)))
          ≤ ∫ u, ((1 + ‖u‖) ^ 2)⁻¹ * ‖u - conj v‖ ^ (-(3 / 2 : ℝ)) :=
            setIntegral_le_integral (hCt (conj v)).1 (Eventually.of_forall fun u => by positivity)
        _ ≤ Ct * (1 + ‖conj v‖) ^ (-(1 / 2 : ℝ)) := (hCt (conj v)).2
        _ = Ct * (1 + ‖v‖) ^ (-(1 / 2 : ℝ)) := by rw [Complex.norm_conj]
  have hpow : ((1 + ‖v‖) ^ 2)⁻¹ * (1 + ‖v‖) ^ (-(1 / 2 : ℝ)) = (1 + ‖v‖) ^ (-(5 / 2 : ℝ)) := by
    rw [show ((1 + ‖v‖) ^ 2)⁻¹ = (1 + ‖v‖) ^ (-(2 : ℝ)) by
      rw [Real.rpow_neg hX.le, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast],
      ← Real.rpow_add hX]
    norm_num
  calc ‖∫ u in upperHalf, μ u * conj (ν v) * T u v‖
      ≤ M * N * E v * v.im ^ (-(1 / 2 : ℝ)) * (Ct * (1 + ‖v‖) ^ (-(1 / 2 : ℝ))) := hI
    _ ≤ M * N * (E₀ * ((1 + ‖v‖) ^ 2)⁻¹) * v.im ^ (-(1 / 2 : ℝ)) * (Ct * (1 + ‖v‖) ^ (-(1 / 2 : ℝ))) := by
        gcongr
        exact hEv v hv
    _ = M * N * E₀ * Ct * ((((1 + ‖v‖) ^ 2)⁻¹ * (1 + ‖v‖) ^ (-(1 / 2 : ℝ))) * v.im ^ (-(1 / 2 : ℝ))) := by ring
    _ = M * N * E₀ * Ct * ((1 + ‖v‖) ^ (-(5 / 2 : ℝ)) * v.im ^ (-(1 / 2 : ℝ))) := by rw [hpow]

/-- **(D2)** `[W1]` **Regularization (7.5).** The four-term identity (TT:2735, from (6.5)); for `v ≠ z` every inner
`u`-integral is an ordinary integral (kernels `O(|u|⁻⁴)`, no singularity on `𝕌`); the second term contributes
`c₁ · PV_v \overline{ν(v)}/((v̄ - z̄)²(v̄ - z)²) = c₁ \overline{(eq_6_3)} = 0`, the third `c₂ ∫_v \overline{ν}/((z - v̄)³(v̄ - z̄))
= c₂ \overline{(cor_1_15)} = 0`; the first and fourth give integrable `v`-functions (`O(log(1/Im v))` near `∂𝕌`,
`O(|v|⁻⁴ log |v|)` at `∞`), so their truncations converge to the full integrals (as `e64_inner_regular`). -/
theorem s71_reg75 {μ ν φ ψ : ℂ → ℂ} (hμ : IsHarmonicU μ φ) (hν : IsHarmonicU ν ψ) {z : ℂ} (hz : z ∈ upperHalf) :
    Tendsto (fun δ : ℝ => ∫ v in upperHalfPunct z δ, ∫ u in upperHalf,
        μ u * conj (ν v) / ((u - conj z) ^ 2 * (u - conj v) ^ 2 * (conj v - conj z) ^ 2)) (𝓝[>] 0)
      (𝓝 (∫ v in upperHalf, ∫ u in upperHalf, μ u * conj (ν v) *
        ((u - z) ^ 2 / ((u - conj z) ^ 4 * (conj v - z) ^ 2 * (u - conj v) ^ 2) +
          2 * (z - conj z) * (z - u) ^ 2 / ((u - conj z) ^ 5 * (z - conj v) ^ 3 * (u - conj v))))) := by
  have hU := measurableSet_upperHalf_aux
  have hzi : 0 < z.im := hz
  obtain ⟨hFu, hH⟩ := s71_r75_Hint hμ hν hz
  obtain ⟨M, hM0, hM⟩ := harmonicU_bounded hμ
  have hμc := harmonicU_continuousOn hμ
  obtain ⟨c, hc, hlz⟩ := s71_r75_lower (a := conj z) (by rw [Complex.conj_im]; linarith)
  -- the two `u`-constants
  set I₄ : ℂ := ∫ u in upperHalf, μ u / (u - conj z) ^ 4 with hI₄
  set I₅ : ℂ := ∫ u in upperHalf, μ u * (z - u) / (u - conj z) ^ 5 with hI₅
  have hne : ∀ u ∈ upperHalf, u - conj z ≠ 0 := fun u hu => eq_7_4_sub_conj_ne_zero hu hz
  have hcu : ∀ u ∈ upperHalf, (0 : ℝ) < c * (1 + ‖u‖) := fun u hu => by positivity
  have hi4 : IntegrableOn (fun u => μ u / (u - conj z) ^ 4) upperHalf := by
    refine s71_r75_int4 (hμc.div (Continuous.continuousOn (by fun_prop)) fun u hu => pow_ne_zero _ (hne u hu))
      (K := M * (c ^ 4)⁻¹) fun u hu => ?_
    rw [norm_div, norm_pow, div_eq_mul_inv, mul_assoc, ← mul_inv, ← mul_pow]
    exact mul_le_mul (hM u hu) (inv_anti₀ (by have := hcu u hu; positivity)
      (pow_le_pow_left₀ (hcu u hu).le (hlz u hu) 4)) (by positivity) hM0
  have hi5 : IntegrableOn (fun u => μ u * (z - u) / (u - conj z) ^ 5) upperHalf := by
    refine s71_r75_int4 ((hμc.mul (Continuous.continuousOn (by fun_prop))).div
      (Continuous.continuousOn (by fun_prop)) fun u hu => pow_ne_zero _ (hne u hu))
      (K := M * (c ^ 4)⁻¹) fun u hu => ?_
    have ha : 0 < ‖u - conj z‖ := norm_pos_iff.2 (hne u hu)
    have hzu : ‖z - u‖ ≤ ‖u - conj z‖ := by rw [norm_sub_rev]; exact s71_r75_le_conj hu hz
    rw [norm_div, norm_mul, norm_pow]
    calc ‖μ u‖ * ‖z - u‖ / ‖u - conj z‖ ^ 5 ≤ M * ‖u - conj z‖ / ‖u - conj z‖ ^ 5 := by
          gcongr
          exact hM u hu
      _ = M * (‖u - conj z‖ ^ 4)⁻¹ := by field_simp
      _ ≤ M * ((c ^ 4)⁻¹ * ((1 + ‖u‖) ^ 4)⁻¹) := by
          rw [← mul_inv, ← mul_pow]
          exact mul_le_mul_of_nonneg_left (inv_anti₀ (by have := hcu u hu; positivity)
            (pow_le_pow_left₀ (hcu u hu).le (hlz u hu) 4)) hM0
      _ = M * (c ^ 4)⁻¹ * ((1 + ‖u‖) ^ 4)⁻¹ := by ring
  -- the `v`-functions of the second and third terms
  obtain ⟨-, hJ5, hJ4⟩ := e64_t10_int hν hz hz
  set A : ℂ → ℂ := fun v => (z - conj z) ^ 2 * I₄ * conj (ν v / ((v - z) ^ 2 * (v - conj z) ^ 2)) with hA
  set B : ℂ → ℂ := fun v => -(2 * (z - conj z) ^ 2 * I₅) * conj (ν v / ((v - z) * (v - conj z) ^ 3)) with hB
  set H : ℂ → ℂ := fun v => ∫ u in upperHalf, μ u * conj (ν v) *
    ((u - z) ^ 2 / ((u - conj z) ^ 4 * (conj v - z) ^ 2 * (u - conj v) ^ 2) +
      2 * (z - conj z) * (z - u) ^ 2 / ((u - conj z) ^ 5 * (z - conj v) ^ 3 * (u - conj v))) with hHd
  -- the pointwise split of the inner integral for `v ∈ 𝕌`, `v ≠ z`
  have hsplit : ∀ v ∈ upperHalf, v ≠ z → (∫ u in upperHalf,
      μ u * conj (ν v) / ((u - conj z) ^ 2 * (u - conj v) ^ 2 * (conj v - conj z) ^ 2)) = H v + A v + B v := by
    intro v hv hvz
    have h3 : conj v - conj z ≠ 0 := fun h => hvz (by
      have := congrArg conj h; simp only [map_sub, Complex.conj_conj, map_zero] at this
      exact sub_eq_zero.1 this)
    have h4 : conj v - z ≠ 0 := fun h => eq_7_4_sub_conj_ne_zero hz hv (by linear_combination -h)
    have h5 : z - conj v ≠ 0 := eq_7_4_sub_conj_ne_zero hz hv
    have h6 : v - z ≠ 0 := sub_ne_zero.2 hvz
    have h7 : v - conj z ≠ 0 := eq_7_4_sub_conj_ne_zero hv hz
    set k₂ : ℂ := conj (ν v) * ((z - conj z) ^ 2 / ((conj v - conj z) ^ 2 * (conj v - z) ^ 2)) with hk₂
    set k₃ : ℂ := conj (ν v) * (2 * (z - conj z) ^ 2 / ((z - conj v) ^ 3 * (conj v - conj z))) with hk₃
    have hpt : ∀ u ∈ upperHalf,
        μ u * conj (ν v) / ((u - conj z) ^ 2 * (u - conj v) ^ 2 * (conj v - conj z) ^ 2) =
          μ u * conj (ν v) * ((u - z) ^ 2 / ((u - conj z) ^ 4 * (conj v - z) ^ 2 * (u - conj v) ^ 2) +
            2 * (z - conj z) * (z - u) ^ 2 / ((u - conj z) ^ 5 * (z - conj v) ^ 3 * (u - conj v))) +
          k₂ * (μ u / (u - conj z) ^ 4) + k₃ * (μ u * (z - u) / (u - conj z) ^ 5) := by
      intro u hu
      have h1 := hne u hu
      have h2 := eq_7_4_sub_conj_ne_zero hu hv
      rw [div_eq_mul_one_div (μ u * conj (ν v)), s71_r75_four h1 h2 h3 h4, hk₂, hk₃]
      field_simp
      ring
    rw [setIntegral_congr_fun hU hpt, integral_add (f := fun u => μ u * conj (ν v) *
        ((u - z) ^ 2 / ((u - conj z) ^ 4 * (conj v - z) ^ 2 * (u - conj v) ^ 2) +
          2 * (z - conj z) * (z - u) ^ 2 / ((u - conj z) ^ 5 * (z - conj v) ^ 3 * (u - conj v))) +
        k₂ * (μ u / (u - conj z) ^ 4)) (by exact (hFu v hv).add (hi4.const_mul k₂)) (hi5.const_mul k₃),
      integral_add (hFu v hv) (hi4.const_mul k₂), integral_const_mul, integral_const_mul]
    have eA : k₂ * I₄ = A v := by
      rw [hk₂, hA]
      simp only [map_div₀, map_mul, map_pow, map_sub, Complex.conj_conj]
      field_simp
    have eB : k₃ * I₅ = B v := by
      rw [hk₃, hB]
      simp only [map_div₀, map_mul, map_pow, map_sub, Complex.conj_conj]
      field_simp
      ring
    rw [← hI₄, ← hI₅, eA, eB]
  -- integrability of the three `v`-functions on the punctured sets
  have hHp : ∀ δ, IntegrableOn H (upperHalfPunct z δ) := fun δ => hH.mono_set sdiff_subset
  have hAp : ∀ δ, 0 < δ → IntegrableOn A (upperHalfPunct z δ) := fun δ hδ =>
    (e124a_conj_int (hJ4 δ hδ)).const_mul _
  have hBi : IntegrableOn B upperHalf := (e124a_conj_int hJ5).const_mul _
  -- the limits
  have hlimH : Tendsto (fun δ => ∫ v in upperHalfPunct z δ, H v) (𝓝[>] 0) (𝓝 (∫ v in upperHalf, H v)) :=
    e124p_rem_tendsto hH (fun δ => measurableSet_ball) fun v hvz => by
      filter_upwards [Ioo_mem_nhdsGT (dist_pos.2 hvz)] with δ hδ
      exact fun h => (lt_irrefl _ ((mem_ball.1 h).trans hδ.2))
  have hlimB : Tendsto (fun δ => ∫ v in upperHalfPunct z δ, B v) (𝓝[>] 0) (𝓝 0) := by
    have h := e124p_rem_tendsto hBi (fun δ => measurableSet_ball (x := z)) fun v hvz => by
      filter_upwards [Ioo_mem_nhdsGT (dist_pos.2 hvz)] with δ hδ
      exact fun h => (lt_irrefl _ ((mem_ball.1 h).trans hδ.2))
    have h0 : (∫ v in upperHalf, B v) = 0 := by
      rw [hB, integral_const_mul, integral_conj, l613_cor_1_15 hν hz, map_zero, mul_zero]
    rw [h0] at h
    exact h
  have hlimA : Tendsto (fun δ => ∫ v in upperHalfPunct z δ, A v) (𝓝[>] 0) (𝓝 0) := by
    have h := ((Complex.continuous_conj.tendsto 0).comp (eq_6_3 hν hz)).const_mul ((z - conj z) ^ 2 * I₄)
    rw [map_zero, mul_zero] at h
    refine h.congr fun δ => ?_
    simp only [Function.comp_apply, hA]
    rw [integral_const_mul, integral_conj]
  -- assembly
  have hlim := (hlimH.add hlimA).add hlimB
  rw [add_zero, add_zero] at hlim
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  have hδ0 : 0 < δ := hδ
  have hm : MeasurableSet (upperHalfPunct z δ) := hU.diff measurableSet_ball
  rw [← integral_add (hHp δ) (hAp δ hδ0),
    ← integral_add (f := fun v => H v + A v) ((hHp δ).add (hAp δ hδ0)) (hBi.mono_set sdiff_subset)]
  refine setIntegral_congr_fun hm fun v hv => ?_
  have hvz : v ≠ z := fun h => hv.2 (by rw [h]; exact mem_ball_self hδ0)
  exact (hsplit v hv.1 hvz).symm

/-! ### The original statements (byte-identical copies) -/

/-- **(7.2)** (TT:2709). `∂/∂ε|_{ε=0} Q(μ, εν)(z) = (6(z - z̄)²/π²) ∬∬_{𝕌×𝕌} μ(u)ν(v)/((u - z̄)²(u - v)²(v - z̄)²)`. The
double integral is a principal value on the diagonal `u = v`. -/
theorem s71_eq_7_2 {μ ν φ ψ : ℂ → ℂ} (hμ : IsHarmonicU μ φ) (hν : IsHarmonicU ν ψ) {z : ℂ} (hz : z ∈ upperHalf) :
    dz (fun ε => QfunU μ (fun u => ε * ν u) z) 0 =
      6 * (z - conj z) ^ 2 / π ^ 2 * limUnder (𝓝[>] (0 : ℝ)) fun δ =>
        ∫ p in (upperHalf ×ˢ upperHalf) ∩ {p : ℂ × ℂ | δ ≤ ‖p.1 - p.2‖},
          μ p.1 * ν p.2 / ((p.1 - conj z) ^ 2 * (p.1 - p.2) ^ 2 * (p.2 - conj z) ^ 2) := by
  obtain ⟨-, hJ, -⟩ := s71_J_deriv hμ hν hz
  have hzim : 0 < z.im := hz
  have hz0 : z - conj z ≠ 0 := by
    intro h
    have := congrArg Complex.im h
    rw [Complex.sub_im, Complex.conj_im, Complex.zero_im] at this
    linarith
  have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 Real.pi_ne_zero
  rw [(s71_bridge72 hμ hν hz).limUnder_eq, (s71_Q_quot hμ hν hz).1, hJ, s71_rho0,
    setIntegral_congr_fun measurableSet_upperHalf_aux (fun u hu => (s71_pointwise hμ hν hz hu).1),
    integral_const_mul]
  field_simp
  ring

/-- **(7.3)** (TT:2715). `∂/∂ε̄|_{ε=0} Q(μ, εν)(z)` equals
`(6(z - z̄)²/π²) ∬∬_{𝕌×𝕌} μ(u)\overline{ν(v)}/((u - z̄)²(u - v̄)²(v̄ - z̄)²) d²u d²v`.
[CORRECTION 2026-10-28, leader] The outer `v`-integral is a principal value at `v = z` (TT:2717: "understood in the
principal value sense"). As a plain Bochner integral it is junk `0`: the inner `u`-integral at `v = z` is
`∫ μ/(u - z̄)⁴ = (π/12) ρ(z) μ(z)` (by (7.1) at `ε = 0`), so the `v`-integrand is of size `|v - z|⁻²` there. -/
theorem s71_eq_7_3 {μ ν φ ψ : ℂ → ℂ} (hμ : IsHarmonicU μ φ) (hν : IsHarmonicU ν ψ) {z : ℂ} (hz : z ∈ upperHalf) :
    dzbar (fun ε => QfunU μ (fun u => ε * ν u) z) 0 =
      6 * (z - conj z) ^ 2 / π ^ 2 * limUnder (𝓝[>] (0 : ℝ)) fun δ => ∫ v in upperHalfPunct z δ, ∫ u in upperHalf,
        μ u * conj (ν v) / ((u - conj z) ^ 2 * (u - conj v) ^ 2 * (conj v - conj z) ^ 2) := by
  obtain ⟨-, -, hJ⟩ := s71_J_deriv hμ hν hz
  have hzim : 0 < z.im := hz
  have hz0 : z - conj z ≠ 0 := by
    intro h
    have := congrArg Complex.im h
    rw [Complex.sub_im, Complex.conj_im, Complex.zero_im] at this
    linarith
  have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 Real.pi_ne_zero
  rw [(s71_swap73 hμ hν hz).limUnder_eq, (s71_Q_quot hμ hν hz).2, hJ, s71_rho0,
    setIntegral_congr_fun measurableSet_upperHalf_aux (fun u hu => (s71_pointwise hμ hν hz hu).2),
    integral_const_mul]
  field_simp
  ring

/-- **(7.5)** (TT:2751). The regularized form of (7.3): `∂/∂ε̄|_{ε=0} Q(μ, εν)(z)` equals
`(6(z - z̄)²/π²) ∬∬ μ(u)\overline{ν(v)} ((u - z)²/((u - z̄)⁴(v̄ - z)²(u - v̄)²) + 2(z - z̄)(z - u)²/((u - z̄)⁵(z - v̄)³(u - v̄)))`. -/
theorem s71_eq_7_5 {μ ν φ ψ : ℂ → ℂ} (hμ : IsHarmonicU μ φ) (hν : IsHarmonicU ν ψ) {z : ℂ} (hz : z ∈ upperHalf) :
    dzbar (fun ε => QfunU μ (fun u => ε * ν u) z) 0 =
      6 * (z - conj z) ^ 2 / π ^ 2 * ∫ v in upperHalf, ∫ u in upperHalf, μ u * conj (ν v) *
        ((u - z) ^ 2 / ((u - conj z) ^ 4 * (conj v - z) ^ 2 * (u - conj v) ^ 2) +
          2 * (z - conj z) * (z - u) ^ 2 / ((u - conj z) ^ 5 * (z - conj v) ^ 3 * (u - conj v))) := by
  rw [s71_eq_7_3 hμ hν hz, (s71_reg75 hμ hν hz).limUnder_eq]

/-- **(7.1)** (TT:2703). In the model `𝕌`, for `μ, ν ∈ Ω^{-1,1}(𝕌)` and small `ε`:
`ρ^{εν}(z) Q(μ, εν)(z) = (12/π) ∬_𝕌 μ(u) K_{εν}(u, z̄)² d²u`. -/
theorem eq_7_1 {μ ν φ ψ : ℂ → ℂ} (hμ : IsHarmonicU μ φ) (hν : IsHarmonicU ν ψ) {k : ℝ} (hk : 0 ≤ k)
    (hνk : IsBeltramiCoeff ν upperHalf k) {ε : ℂ} (hε : ‖ε‖ * k < 1) {z : ℂ} (hz : z ∈ upperHalf) :
    rhoVar ν ε z * QfunU μ (fun u => ε * ν u) z =
      (12 / π) * ∫ u in upperHalf, μ u * kernelKbar (fun y => ε * ν y) u z ^ 2 :=
  s71_eq_7_1 hμ hν hk hνk hε hz

/-- **(7.2)** (TT:2709). `∂/∂ε|_{ε=0} Q(μ, εν)(z) = (6(z - z̄)²/π²) ∬∬_{𝕌×𝕌} μ(u)ν(v)/((u - z̄)²(u - v)²(v - z̄)²)`. The
double integral is a principal value on the diagonal `u = v`. -/
theorem eq_7_2 {μ ν φ ψ : ℂ → ℂ} (hμ : IsHarmonicU μ φ) (hν : IsHarmonicU ν ψ) {z : ℂ} (hz : z ∈ upperHalf) :
    dz (fun ε => QfunU μ (fun u => ε * ν u) z) 0 =
      6 * (z - conj z) ^ 2 / π ^ 2 * limUnder (𝓝[>] (0 : ℝ)) fun δ =>
        ∫ p in (upperHalf ×ˢ upperHalf) ∩ {p : ℂ × ℂ | δ ≤ ‖p.1 - p.2‖},
          μ p.1 * ν p.2 / ((p.1 - conj z) ^ 2 * (p.1 - p.2) ^ 2 * (p.2 - conj z) ^ 2) :=
  s71_eq_7_2 hμ hν hz

/-- **(7.3)** (TT:2715). `∂/∂ε̄|_{ε=0} Q(μ, εν)(z)` equals
`(6(z - z̄)²/π²) ∬∬_{𝕌×𝕌} μ(u)\overline{ν(v)}/((u - z̄)²(u - v̄)²(v̄ - z̄)²) d²u d²v`.
[CORRECTION 2026-10-28, leader] The outer `v`-integral is a principal value at `v = z` (TT:2717: "understood in the
principal value sense"). As a plain Bochner integral it is junk `0`: the inner `u`-integral at `v = z` is
`∫ μ/(u - z̄)⁴ = (π/12) ρ(z) μ(z)` (by (7.1) at `ε = 0`), so the `v`-integrand is of size `|v - z|⁻²` there. -/
theorem eq_7_3 {μ ν φ ψ : ℂ → ℂ} (hμ : IsHarmonicU μ φ) (hν : IsHarmonicU ν ψ) {z : ℂ} (hz : z ∈ upperHalf) :
    dzbar (fun ε => QfunU μ (fun u => ε * ν u) z) 0 =
      6 * (z - conj z) ^ 2 / π ^ 2 * limUnder (𝓝[>] (0 : ℝ)) fun δ => ∫ v in upperHalfPunct z δ, ∫ u in upperHalf,
        μ u * conj (ν v) / ((u - conj z) ^ 2 * (u - conj v) ^ 2 * (conj v - conj z) ^ 2) :=
  s71_eq_7_3 hμ hν hz

/-- **(7.5)** (TT:2751). The regularized form of (7.3): `∂/∂ε̄|_{ε=0} Q(μ, εν)(z)` equals
`(6(z - z̄)²/π²) ∬∬ μ(u)\overline{ν(v)} ((u - z)²/((u - z̄)⁴(v̄ - z)²(u - v̄)²) + 2(z - z̄)(z - u)²/((u - z̄)⁵(z - v̄)³(u - v̄)))`. -/
theorem eq_7_5 {μ ν φ ψ : ℂ → ℂ} (hμ : IsHarmonicU μ φ) (hν : IsHarmonicU ν ψ) {z : ℂ} (hz : z ∈ upperHalf) :
    dzbar (fun ε => QfunU μ (fun u => ε * ν u) z) 0 =
      6 * (z - conj z) ^ 2 / π ^ 2 * ∫ v in upperHalf, ∫ u in upperHalf, μ u * conj (ν v) *
        ((u - z) ^ 2 / ((u - conj z) ^ 4 * (conj v - z) ^ 2 * (u - conj v) ^ 2) +
          2 * (z - conj z) * (z - u) ^ 2 / ((u - conj z) ^ 5 * (z - conj v) ^ 3 * (u - conj v))) :=
  s71_eq_7_5 hμ hν hz

end TakhtajanTeo
