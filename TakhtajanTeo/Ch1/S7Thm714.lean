import TakhtajanTeo.Ch1.S7Cor79

/-!
# Program G, F3: `thm_7_14` (下属1)

Proof of the sub-interface `F3_714_SUBINTERFACE` (7567f249): stubs IM, EXP, HOLO, PSD, STRICT are proved
below and `s7g_thm_7_14` is assembled as in the interface.

Notation: for real `u, v`, `B(u, v) = (u, G v)` (real, symmetric); `f = μ̄ ν = α + iβ`, `a = |μ|²`, `b = |ν|²`.
* (EXP) by `cor_7_9` for the four terms, `R = 2B(f, f) + 2B(f̄, f̄) - 2B(f, f̄) - 2B(a, b) = 2B(α, α) - 6B(β, β) - 2B(a, b)`;
* (IM) `(u, G v)` is real for real `u, v`;
* (PSD) `B(β, β) ≥ 0`: `G` is positive semidefinite on sign-changing real data. Route: `F = 2Δh + h` with
  `h = G F` (`RK3`), so `(F, G F) = 2(Δh, h) + ‖h‖²`; `(Δh, h) ≥ 0` is a first-energy identity
  `(Δh, h) = c ∫|∂̄h|² d²z`, proved like `s7ei_second_energy` (cutoff graph approximation); transported from `𝔻` to
  `𝔻*` by inversion as in `s7et_*`;
* (STRICT) `B(α, α) < B(a, b)` for ℝ-independent restrictions: with `p = |μ||ν|`,
  `B(a, b) - B(α, α) = ½∬ G (|μ(z)||ν(w)| - |ν(z)||μ(w)|)² ρρ + B(p - α, p + α)`, both `≥ 0` (`G > 0` off the
  diagonal, `|α| ≤ p`); if both vanish, continuity gives `|μ| = c|ν|` and `α = ±p`, so `ν = ±cμ` on `𝔻*`;
* (HOLO) `R_{μμ̄μμ̄} = -2(|μ|², G|μ|²)`, negative by `wp_harmonic_resolvent_energy_pos`;
* `sectionalDen > 0` is `sectionalDen_pos_of_restriction_linearIndependent`.
-/

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal NNReal ComplexConjugate Classical Real
noncomputable section
namespace TakhtajanTeo
open LiZhongQC

/-- STUB IM. The pairing of real data with the resolvent of real data is real. -/
theorem s7g_f3_im (f g : ℂ → ℝ) :
    (l2Inner (fun z => (f z : ℂ)) (resolventStar fun z => (g z : ℂ))).im = 0 := by
  unfold l2Inner
  have e : (fun z => (f z : ℂ) * conj (resolventStar (fun z => (g z : ℂ)) z) * rho z) =
      fun z => ((f z * (∫ w in unitDiscExterior, resolventKernel z w * g w * rho w) * rho z : ℝ) : ℂ) := by
    funext z
    unfold resolventStar
    rw [wp_resolvent_ofReal, Complex.conj_ofReal]
    push_cast
    ring
  rw [e, integral_complex_ofReal, Complex.ofReal_im]

/-- `G` commutes with scalars. -/
theorem s7g_f3_Gsmul (h : ℂ → ℂ) (c z : ℂ) : resolventStar (fun w => c * h w) z = c * resolventStar h z := by
  unfold resolventStar resolventOp
  rw [← integral_const_mul]
  congr 1
  funext w
  ring

/-- Scalars in the pairing. -/
theorem s7g_f3_l2smul (c d : ℂ) (h k : ℂ → ℂ) :
    l2Inner (fun z => c * h z) (fun z => d * k z) = c * conj d * l2Inner h k := by
  unfold l2Inner
  rw [← integral_const_mul]
  congr 1
  funext z
  simp only [map_mul]
  ring

/-- STUB EXP. The sectional numerator in terms of `B(α, α)`, `B(β, β)`, `B(|μ|², |ν|²)`, `μ̄ ν = α + iβ`. -/
theorem s7g_f3_expand {μ ν : ℂ → ℂ} (hμ : μ ∈ harmonicL2 unitDiscExterior) (hν : ν ∈ harmonicL2 unitDiscExterior) :
    sectionalNum μ ν =
      2 * l2Inner (fun z => ((conj (μ z) * ν z).re : ℂ)) (resolventStar fun z => ((conj (μ z) * ν z).re : ℂ)) -
        6 * l2Inner (fun z => ((conj (μ z) * ν z).im : ℂ)) (resolventStar fun z => ((conj (μ z) * ν z).im : ℂ)) -
        2 * l2Inner (fun z => ((‖μ z‖ ^ 2 : ℝ) : ℂ)) (resolventStar fun z => ((‖ν z‖ ^ 2 : ℝ) : ℂ)) := by
  obtain ⟨Cc, hCc⟩ := harmonicL2_subset_harmonic
  have hm : MeasurableSet unitDiscExterior := wp_exterior_isOpen.measurableSet
  have aμ := s7pol_harmonic_measurable hμ
  have aν := s7pol_harmonic_measurable hν
  have aeK := wp_harmonic_toLinf_ae hμ
  have aeL := wp_harmonic_toLinf_ae hν
  have pf := s7pol_potential_data hν (hCc μ hμ).1
  have pfb := s7pol_potential_data hμ (hCc ν hν).1
  have hμn : normL2 unitDiscExterior μ < ∞ := by
    obtain ⟨-, -, -, h⟩ := hμ
    exact h
  have hνn : normL2 unitDiscExterior ν < ∞ := by
    obtain ⟨-, -, -, h⟩ := hν
    exact h
  -- the two products and their potentials
  have hGf : resolventStar (fun z => ν z * conj (μ z)) = resolventStar (fun w => ν w * conj (toLinf μ w)) :=
    s7g_c79_Gcongr (by filter_upwards [aeK] with z hz; rw [hz])
  have hGfb : resolventStar (fun z => μ z * conj (ν z)) = resolventStar (fun w => μ w * conj (toLinf ν w)) :=
    s7g_c79_Gcongr (by filter_upwards [aeL] with z hz; rw [hz])
  have af : AEStronglyMeasurable (fun z => ν z * conj (μ z)) (volume.restrict unitDiscExterior) :=
    aν.mul (Complex.continuous_conj.comp_aestronglyMeasurable aμ)
  have afb : AEStronglyMeasurable (fun z => μ z * conj (ν z)) (volume.restrict unitDiscExterior) :=
    aμ.mul (Complex.continuous_conj.comp_aestronglyMeasurable aν)
  have fn : normL2 unitDiscExterior (fun z => ν z * conj (μ z)) < ∞ := by
    refine s7ed_product_finite hνn (M := (Real.sqrt (12 / π) / 4) * (normL2 unitDiscExterior μ).toReal) ?_
    filter_upwards [ae_restrict_mem hm] with z hz
    exact wp_harmonic_pointwise_bound hμ hz
  have fbn : normL2 unitDiscExterior (fun z => μ z * conj (ν z)) < ∞ := by
    refine s7ed_product_finite hμn (M := (Real.sqrt (12 / π) / 4) * (normL2 unitDiscExterior ν).toReal) ?_
    filter_upwards [ae_restrict_mem hm] with z hz
    exact wp_harmonic_pointwise_bound hν hz
  have aGf : AEStronglyMeasurable (resolventStar fun z => ν z * conj (μ z)) (volume.restrict unitDiscExterior) := by
    rw [hGf]
    exact pf.1.1.continuousOn.aestronglyMeasurable hm
  have aGfb : AEStronglyMeasurable (resolventStar fun z => μ z * conj (ν z)) (volume.restrict unitDiscExterior) := by
    rw [hGfb]
    exact pfb.1.1.continuousOn.aestronglyMeasurable hm
  have Gfn : normL2 unitDiscExterior (resolventStar fun z => ν z * conj (μ z)) < ∞ := by
    rw [hGf]
    exact pf.2.1
  have Gfbn : normL2 unitDiscExterior (resolventStar fun z => μ z * conj (ν z)) < ∞ := by
    rw [hGfb]
    exact pfb.2.1
  have iF : ∀ z ∈ unitDiscExterior,
      Integrable (fun w => (resolventKernel z w : ℂ) * (ν w * conj (μ w)) * rho w) (volume.restrict unitDiscExterior) :=
    fun z hz => (pf.2.2 z hz).congr (by filter_upwards [aeK] with w hw; rw [hw])
  have iFb : ∀ z ∈ unitDiscExterior,
      Integrable (fun w => (resolventKernel z w : ℂ) * (μ w * conj (ν w)) * rho w) (volume.restrict unitDiscExterior) :=
    fun z hz => (pfb.2.2 z hz).congr (by filter_upwards [aeL] with w hw; rw [hw])
  -- the real and imaginary parts of `μ̄ν`
  have hlin : ∀ c d : ℂ, l2Inner (fun z => c * (ν z * conj (μ z) + d * (μ z * conj (ν z))))
      (resolventStar fun z => c * (ν z * conj (μ z) + d * (μ z * conj (ν z)))) =
      c * conj c * (l2Inner (fun z => ν z * conj (μ z)) (resolventStar fun z => ν z * conj (μ z)) +
        conj d * l2Inner (fun z => ν z * conj (μ z)) (resolventStar fun z => μ z * conj (ν z)) +
        d * l2Inner (fun z => μ z * conj (ν z)) (resolventStar fun z => ν z * conj (μ z)) +
        (d * conj d) * l2Inner (fun z => μ z * conj (ν z)) (resolventStar fun z => μ z * conj (ν z))) := by
    intro c d
    have hG : (resolventStar fun z => c * (ν z * conj (μ z) + d * (μ z * conj (ν z)))) =ᵐ[volume.restrict unitDiscExterior]
        fun z => c * ((resolventStar fun z => ν z * conj (μ z)) z + d * (resolventStar fun z => μ z * conj (ν z)) z) := by
      filter_upwards [ae_restrict_mem hm] with z hz
      rw [s7g_f3_Gsmul (fun z => ν z * conj (μ z) + d * (μ z * conj (ν z))), s7g_c79_G2 (iF z hz) (iFb z hz)]
    rw [s7pol_pair_congr EventuallyEq.rfl hG, s7g_f3_l2smul,
      s7pol_pair_comb af afb aGf aGfb fn fbn Gfn Gfbn d]
  have eα : (fun z => ((conj (μ z) * ν z).re : ℂ)) = fun z => (1 / 2 : ℂ) * (ν z * conj (μ z) + 1 * (μ z * conj (ν z))) :=
    funext fun z => by
      rw [Complex.re_eq_add_conj, map_mul, Complex.conj_conj]
      ring
  have eβ : (fun z => ((conj (μ z) * ν z).im : ℂ)) =
      fun z => (1 / (2 * I)) * (ν z * conj (μ z) + (-1) * (μ z * conj (ν z))) :=
    funext fun z => by
      rw [Complex.im_eq_sub_conj, map_mul, Complex.conj_conj]
      ring
  rw [eα, eβ, hlin, hlin]
  -- the four curvature terms
  unfold sectionalNum
  rw [s7g_cor_7_9 hν hμ hμ hν, s7g_cor_7_9 hμ hν hν hμ, s7g_cor_7_9 hμ hν hμ hν, s7g_cor_7_9 hν hμ hν hμ]
  have e1 : (fun z => conj (μ z) * ν z) = fun z => ν z * conj (μ z) := funext fun z => mul_comm _ _
  have e2 : (fun z => conj (ν z) * μ z) = fun z => μ z * conj (ν z) := funext fun z => mul_comm _ _
  have e3 : (fun z => conj (μ z) * μ z) = fun z => ((‖μ z‖ ^ 2 : ℝ) : ℂ) :=
    funext fun z => by rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have e4 : (fun z => conj (ν z) * ν z) = fun z => ((‖ν z‖ ^ 2 : ℝ) : ℂ) :=
    funext fun z => by rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have hS := s7g_c79_sym hν hν hμ hμ
  have e5 : (fun z => ν z * conj (ν z)) = fun z => ((‖ν z‖ ^ 2 : ℝ) : ℂ) :=
    funext fun z => by rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have e6 : (fun z => μ z * conj (μ z)) = fun z => ((‖μ z‖ ^ 2 : ℝ) : ℂ) :=
    funext fun z => by rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  rw [e3, e4, e5, e6] at hS
  rw [e1, e2, e3, e4, hS]
  have c1 : (1 / (2 * I)) * conj (1 / (2 * I)) = (1 / 4 : ℂ) := by
    rw [map_div₀, map_one, map_mul, Complex.conj_I, map_ofNat]
    field_simp
    ring_nf
    rw [Complex.I_sq]
    norm_num
  have c2 : (1 / 2 : ℂ) * conj (1 / 2 : ℂ) = 1 / 4 := by
    rw [map_div₀, map_one, map_ofNat]
    norm_num
  rw [c1, c2]
  simp only [map_one, map_neg, one_mul, mul_one, neg_mul, mul_neg, neg_neg]
  ring

/-- STUB HOLO. The holomorphic sectional numerator: `R_{μμ̄μμ̄} = -2(|μ|², G|μ|²)`. -/
theorem s7g_f3_holo {μ : ℂ → ℂ} (hμ : μ ∈ harmonicL2 unitDiscExterior) :
    riemannR μ μ μ μ =
      -2 * l2Inner (fun z => ((‖μ z‖ ^ 2 : ℝ) : ℂ)) (resolventStar fun z => ((‖μ z‖ ^ 2 : ℝ) : ℂ)) := by
  rw [s7g_cor_7_9 hμ hμ hμ hμ]
  have e1 : (fun z => μ z * conj (μ z)) = fun z => ((‖μ z‖ ^ 2 : ℝ) : ℂ) :=
    funext fun z => by rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have e2 : (fun z => conj (μ z) * μ z) = fun z => ((‖μ z‖ ^ 2 : ℝ) : ℂ) :=
    funext fun z => by rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  rw [e1, e2]
  ring

/-- Monotonicity of the weighted `L²` norm. -/
theorem s7g_f3_nmono {D : Set ℂ} {f g : ℂ → ℂ} (h : ∀ z, ‖f z‖ ≤ ‖g z‖) : normL2 D f ≤ normL2 D g := by
  unfold normL2
  refine ENNReal.rpow_le_rpow (lintegral_mono fun z => ?_) (by norm_num)
  gcongr
  exact_mod_cast h z

/-- The real part of a pairing `(h, h)` is nonnegative. -/
theorem s7g_f3_self_re {D : Set ℂ} {h : ℂ → ℂ}
    (hi : Integrable (fun z => h z * conj (h z) * rho z) (volume.restrict D)) :
    0 ≤ (∫ z in D, h z * conj (h z) * rho z).re := by
  have e := integral_re hi
  simp only [RCLike.re_to_complex] at e
  rw [← e]
  refine integral_nonneg fun z => ?_
  rw [Complex.mul_conj, ← Complex.ofReal_mul, Complex.ofReal_re]
  exact mul_nonneg (Complex.normSq_nonneg _) (wp_rho_nonneg z)

/-- **First energy**: `Re (h, Δh) ≥ 0` on `𝔻` for `h ∈ L²(ρ)` smooth with `Δh ∈ L²(ρ)` (`Δ = laplace0`, the positive
Laplacian). Compact approximants `χₙ h` (`s7ga_graph_approximation`) satisfy `(k, Δk) = ∫ |∂̄k|²` (`s7cg_green`),
and the pairing passes to the limit (`s7pc_pairing_tendsto`). -/
theorem s7g_f3_fe {h : ℂ → ℂ} (hh : ContDiffOn ℝ (⊤ : ℕ∞) h unitDisc)
    (hL : normL2 unitDisc h < ∞) (hDL : normL2 unitDisc (laplace0 h) < ∞) :
    0 ≤ (∫ z in unitDisc, h z * conj (laplace0 h z) * rho z).re := by
  obtain ⟨hk, hkh, hkl⟩ := s7ga_graph_approximation hh hL hDL
  have hkm : ∀ n : ℕ, AEStronglyMeasurable (fun z => (s7dc_cutoff n z : ℂ) * h z) (volume.restrict unitDisc) :=
    fun n => (hk n).1.continuous.aestronglyMeasurable
  have hlm : ∀ n : ℕ, AEStronglyMeasurable (laplace0 fun z => (s7dc_cutoff n z : ℂ) * h z)
      (volume.restrict unitDisc) := fun n => (s7el_laplace_measurable _).aestronglyMeasurable
  have hkn : ∀ n : ℕ, normL2 unitDisc (fun z => (s7dc_cutoff n z : ℂ) * h z) < ∞ :=
    fun n => s7gn_compact_normL2_finite (hk n).1 (hk n).2.1 (hk n).2.2
  have hln : ∀ n : ℕ, normL2 unitDisc (laplace0 fun z => (s7dc_cutoff n z : ℂ) * h z) < ∞ := fun n =>
    s7gn_compact_normL2_finite (s7gb_laplace_smooth (hk n).1)
      ((hk n).2.1.of_isClosed_subset (isClosed_tsupport _) (s7gb_laplace_support _))
      ((s7gb_laplace_support _).trans (hk n).2.2)
  have hm : AEStronglyMeasurable h (volume.restrict unitDisc) :=
    hh.continuousOn.aestronglyMeasurable measurableSet_ball
  have hDm : AEStronglyMeasurable (laplace0 h) (volume.restrict unitDisc) :=
    (s7el_laplace_measurable _).aestronglyMeasurable
  have ht := s7pc_pairing_tendsto hkm hlm hm hDm hkn hln hL hDL hkh hkl
  have hnn : ∀ n : ℕ, 0 ≤ (∫ z in unitDisc, (s7dc_cutoff n z : ℂ) * h z *
      conj (laplace0 (fun w => (s7dc_cutoff n w : ℂ) * h w) z) * rho z).re := by
    intro n
    obtain ⟨-, hI, hG⟩ := s7cg_green (Or.inl rfl) ((hk n).1.of_le (by simp)).contDiffOn ((hk n).1.of_le (by simp))
      (hk n).2.1 (hk n).2.2
    rw [← s7ei_pair_disk (hk n).2.2, hG]
    have e := integral_re hI
    simp only [RCLike.re_to_complex] at e
    rw [← e]
    refine integral_nonneg fun z => ?_
    rw [Complex.mul_conj, Complex.ofReal_re]
    exact Complex.normSq_nonneg _
  exact ge_of_tendsto ((Complex.continuous_re.tendsto _).comp ht) (Eventually.of_forall hnn)

/-- `G` is positive semidefinite on `𝔻`: `Re (F, G F) ≥ 0` for `F ∈ BCinf(𝔻) ∩ L²(ρ)`. With `h = G F`,
`F = 2Δh + h` (`RK3`), so `(F, h) = 2(Δh, h) + (h, h)`. -/
theorem s7g_f3_dpsd {F : ℂ → ℂ} (hF : F ∈ BCinf unitDisc) (hFn : normL2 unitDisc F < ∞) :
    0 ≤ (∫ z in unitDisc, F z * conj (resolventOp unitDisc F z) * rho z).re := by
  have hh : resolventOp unitDisc F ∈ BCinf unitDisc := RK3_output_BCinf_disc hF
  have hL : normL2 unitDisc (resolventOp unitDisc F) < ∞ := s7rl_finite (Or.inl rfl) hF hFn
  have hDL : normL2 unitDisc (laplace0 (resolventOp unitDisc F)) < ∞ := s7re_resolvent_laplace_finite hF hFn
  have hhm : AEStronglyMeasurable (resolventOp unitDisc F) (volume.restrict unitDisc) :=
    hh.1.continuousOn.aestronglyMeasurable measurableSet_ball
  have hDm : AEStronglyMeasurable (laplace0 (resolventOp unitDisc F)) (volume.restrict unitDisc) :=
    (s7el_laplace_measurable _).aestronglyMeasurable
  have hP : ∀ z ∈ unitDisc, F z = 2 * laplace0 (resolventOp unitDisc F) z + resolventOp unitDisc F z := by
    intro z hz
    have hp := RK3_output_equation_disc hF z hz
    linear_combination -hp
  have i1 := s7pc_pairing_integrable hDm hhm hDL hL
  have i2 := s7pc_pairing_integrable hhm hhm hL hL
  have e : (∫ z in unitDisc, F z * conj (resolventOp unitDisc F z) * rho z) =
      2 * (∫ z in unitDisc, laplace0 (resolventOp unitDisc F) z * conj (resolventOp unitDisc F z) * rho z) +
        ∫ z in unitDisc, resolventOp unitDisc F z * conj (resolventOp unitDisc F z) * rho z := by
    rw [← integral_const_mul, ← integral_add (i1.const_mul 2) i2]
    refine setIntegral_congr_fun measurableSet_ball fun z hz => ?_
    show F z * _ * _ = _
    rw [hP z hz]
    ring
  have hfe := s7g_f3_fe hh.1 hL hDL
  have hc : (∫ z in unitDisc, laplace0 (resolventOp unitDisc F) z * conj (resolventOp unitDisc F z) * rho z) =
      conj (∫ z in unitDisc, resolventOp unitDisc F z * conj (laplace0 (resolventOp unitDisc F) z) * rho z) :=
    (s7re_pair_conj _ _ _).symm
  rw [e, Complex.add_re, Complex.mul_re, hc, Complex.conj_re]
  have := s7g_f3_self_re i2
  norm_num
  linarith

/-- STUB PSD. `G` is positive semidefinite on the sign-changing real datum `β = Im(μ̄ ν)`. -/
theorem s7g_f3_psd {μ ν : ℂ → ℂ} (hμ : μ ∈ harmonicL2 unitDiscExterior) (hν : ν ∈ harmonicL2 unitDiscExterior) :
    0 ≤ (l2Inner (fun z => ((conj (μ z) * ν z).im : ℂ))
      (resolventStar fun z => ((conj (μ z) * ν z).im : ℂ))).re := by
  obtain ⟨Cc, hCc⟩ := harmonicL2_subset_harmonic
  obtain ⟨F₁, hF₁, hF₁n, he₁, -, -, -⟩ := s7et_forcing_potential_bridge hμ (hCc ν hν).1
  obtain ⟨C, hC⟩ := hF₁.2
  have hcj : ContDiff ℝ (⊤ : ℕ∞) (fun v : ℂ => conj v) := Complex.conjCLE.contDiff
  have hβ : ∀ X : ℂ, ((conj X).im : ℂ) = (conj X - X) / (2 * I) := fun X => by
    rw [Complex.im_eq_sub_conj, Complex.conj_conj]
  obtain ⟨F, hFdef⟩ : ∃ F : ℂ → ℂ, F = fun w => (conj (F₁ w) - F₁ w) / (2 * I) := ⟨_, rfl⟩
  have hF : F ∈ BCinf unitDisc := by
    rw [hFdef]
    refine ⟨((hcj.comp_contDiffOn hF₁.1).sub hF₁.1).div_const _, C, fun z hz => ?_⟩
    show ‖(conj (F₁ z) - F₁ z) / (2 * I)‖ ≤ C
    rw [← hβ, Complex.norm_real, Real.norm_eq_abs]
    exact (Complex.abs_im_le_norm _).trans (by rw [Complex.norm_conj]; exact hC z hz)
  have hFn : normL2 unitDisc F < ∞ := by
    refine lt_of_le_of_lt (s7g_f3_nmono fun w => ?_) hF₁n
    rw [hFdef]
    show ‖(conj (F₁ w) - F₁ w) / (2 * I)‖ ≤ _
    rw [← hβ, Complex.norm_real, Real.norm_eq_abs, ← Complex.norm_conj (F₁ w)]
    exact Complex.abs_im_le_norm _
  have hae : (fun z => ((conj (μ z) * ν z).im : ℂ)) =ᵐ[volume.restrict unitDiscExterior] fun z => F z⁻¹ := by
    filter_upwards [he₁, wp_harmonic_toLinf_ae hν] with z h1 h2
    have h1' : μ z * conj (ν z) = F₁ z⁻¹ := by rw [← h2]; exact h1
    rw [hFdef]
    show ((conj (μ z) * ν z).im : ℂ) = (conj (F₁ z⁻¹) - F₁ z⁻¹) / (2 * I)
    rw [← h1', ← hβ, map_mul, Complex.conj_conj]
  have hG : (resolventStar fun z => ((conj (μ z) * ν z).im : ℂ)) =ᵐ[volume.restrict unitDiscExterior]
      fun z => resolventOp unitDisc F z⁻¹ := by
    rw [s7g_c79_Gcongr hae]
    filter_upwards [ae_restrict_mem resolvent_exterior_isOpen.measurableSet] with z hz
    exact s7et_resolvent_inv F hz
  rw [s7et_pairing_transport_ae hae hG]
  exact s7g_f3_dpsd hF hFn

/-- The pairing of real data as a double integral over `𝔻* × 𝔻*` (bounded `v`, `u ρ` integrable). -/
theorem s7g_f3_dbl {u v : ℂ → ℝ} (hu : ContinuousOn u unitDiscExterior) (hv : ContinuousOn v unitDiscExterior)
    {C : ℝ} (hvb : ∀ w ∈ unitDiscExterior, |v w| ≤ C) (hui : IntegrableOn (fun z => u z * rho z) unitDiscExterior) :
    Integrable (fun p : ℂ × ℂ => resolventKernel p.1 p.2 * v p.2 * rho p.2 * (u p.1 * rho p.1))
        ((volume.restrict unitDiscExterior).prod (volume.restrict unitDiscExterior)) ∧
      (l2Inner (fun z => (u z : ℂ)) (resolventStar fun z => (v z : ℂ))).re =
        ∫ p, resolventKernel p.1 p.2 * v p.2 * rho p.2 * (u p.1 * rho p.1)
          ∂((volume.restrict unitDiscExterior).prod (volume.restrict unitDiscExterior)) := by
  have hm : MeasurableSet unitDiscExterior := wp_exterior_isOpen.measurableSet
  have hvc := Complex.continuous_ofReal.comp_continuousOn hv
  have huc := Complex.continuous_ofReal.comp_continuousOn hu
  have hbc : ∀ w ∈ unitDiscExterior, ‖((v w : ℝ) : ℂ)‖ ≤ C := fun w hw => by
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact hvb w hw
  have hψi : IntegrableOn (fun z => ((u z : ℝ) : ℂ) * (rho z : ℂ)) unitDiscExterior := by
    exact (hui.ofReal (𝕜 := ℂ)).congr (Eventually.of_forall fun z => by simp)
  have hI := resolvent_bilinear_integrable (Or.inr rfl) (hvc.aestronglyMeasurable hm) (huc.aestronglyMeasurable hm)
    hbc hψi
  have hR : Integrable (fun p : ℂ × ℂ => resolventKernel p.1 p.2 * v p.2 * rho p.2 * (u p.1 * rho p.1))
      ((volume.restrict unitDiscExterior).prod (volume.restrict unitDiscExterior)) := by
    refine hI.re.congr (Eventually.of_forall fun p => ?_)
    show (((resolventKernel p.1 p.2 : ℂ) * ((v p.2 : ℝ) : ℂ) * (rho p.2 : ℂ)) *
      (((u p.1 : ℝ) : ℂ) * (rho p.1 : ℂ))).re = _
    simp only [← Complex.ofReal_mul, Complex.ofReal_re]
  refine ⟨hR, ?_⟩
  unfold l2Inner
  have e : (fun z => ((u z : ℝ) : ℂ) * conj (resolventStar (fun z => ((v z : ℝ) : ℂ)) z) * rho z) =
      fun z => ((u z * (∫ w in unitDiscExterior, resolventKernel z w * v w * rho w) * rho z : ℝ) : ℂ) := by
    funext z
    unfold resolventStar
    rw [wp_resolvent_ofReal, Complex.conj_ofReal]
    push_cast
    ring
  rw [e, integral_complex_ofReal, Complex.ofReal_re, integral_prod _ hR]
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  show u z * (∫ w in unitDiscExterior, resolventKernel z w * v w * rho w) * rho z =
    ∫ w in unitDiscExterior, resolventKernel z w * v w * rho w * (u z * rho z)
  rw [integral_mul_const]
  ring

/-- The equality case: if the symmetrized integrand vanishes off the diagonal, `μ, ν` are `ℝ`-dependent on `𝔻*`. -/
theorem s7g_f3_dep {μ ν : ℂ → ℂ} (hμc : ContinuousOn μ unitDiscExterior)
    (h1 : ∀ z ∈ unitDiscExterior, ∀ w ∈ unitDiscExterior, z ≠ w → ‖μ z‖ * ‖ν w‖ = ‖ν z‖ * ‖μ w‖)
    (h2 : ∀ z ∈ unitDiscExterior, ∀ w ∈ unitDiscExterior, z ≠ w →
      (‖μ z‖ * ‖ν z‖) * (‖μ w‖ * ‖ν w‖) = (conj (μ z) * ν z).re * (conj (μ w) * ν w).re) :
    ¬ LinearIndependent ℝ ![(fun z : unitDiscExterior => μ z), (fun z : unitDiscExterior => ν z)] := by
  intro hli
  rw [LinearIndependent.pair_iff] at hli
  have hA : ∀ z, |(conj (μ z) * ν z).re| ≤ ‖μ z‖ * ‖ν z‖ := fun z => by
    have := Complex.abs_re_le_norm (conj (μ z) * ν z)
    rwa [norm_mul, Complex.norm_conj] at this
  by_cases h0 : ∀ z ∈ unitDiscExterior, μ z = 0
  · have := hli 1 0 (by
      funext z
      simp [h0 z z.2])
    norm_num at this
  push_neg at h0
  obtain ⟨z0, hz0, hμ0⟩ := h0
  have hg0 : 0 < ‖μ z0‖ := norm_pos_iff.2 hμ0
  set c := ‖ν z0‖ / ‖μ z0‖ with hcdef
  have hc0 : 0 ≤ c := by positivity
  have hhc : ∀ w ∈ unitDiscExterior, ‖ν w‖ = c * ‖μ w‖ := by
    intro w hw
    by_cases hwz : w = z0
    · rw [hwz, hcdef]
      field_simp
    · have := h1 z0 hz0 w hw (Ne.symm hwz)
      rw [hcdef]
      field_simp
      linarith
  by_cases hc : c = 0
  · have := hli 0 1 (by
      funext z
      have h := hhc z z.2
      rw [hc, zero_mul, norm_eq_zero] at h
      simp [h])
    norm_num at this
  have hcp : 0 < c := lt_of_le_of_ne hc0 (Ne.symm hc)
  -- a second point near `z0` where `μ ≠ 0`
  have hev1 : ∀ᶠ w in 𝓝 z0, w ∈ unitDiscExterior := wp_exterior_isOpen.mem_nhds hz0
  have hev : ∀ᶠ w in 𝓝[≠] z0, w ∈ unitDiscExterior ∧ μ w ≠ 0 :=
    nhdsWithin_le_nhds (hev1.and ((hμc.continuousAt (wp_exterior_isOpen.mem_nhds hz0)).eventually_ne hμ0))
  obtain ⟨w1, ⟨hw1, hμ1⟩, hw1z⟩ := (hev.and self_mem_nhdsWithin).exists
  obtain ⟨P, hPdef⟩ : ∃ P : ℂ → ℝ, P = fun z => ‖μ z‖ * ‖ν z‖ := ⟨_, rfl⟩
  obtain ⟨A, hAdef⟩ : ∃ A : ℂ → ℝ, A = fun z => (conj (μ z) * ν z).re := ⟨_, rfl⟩
  have hPv : ∀ z, P z = ‖μ z‖ * ‖ν z‖ := fun z => by rw [hPdef]
  have hAv : ∀ z, A z = (conj (μ z) * ν z).re := fun z => by rw [hAdef]
  have hP0 : 0 < P z0 := by
    rw [hPv, hhc z0 hz0]
    positivity
  have hP1 : 0 < P w1 := by
    rw [hPv, hhc w1 hw1]
    have := norm_pos_iff.2 hμ1
    positivity
  have hPA : ∀ z ∈ unitDiscExterior, ∀ w ∈ unitDiscExterior, z ≠ w → P z * P w = A z * A w := by
    intro z hz w hw hzw
    rw [hPv, hPv, hAv, hAv]
    exact h2 z hz w hw hzw
  have e01 : P z0 * P w1 = A z0 * A w1 := hPA z0 hz0 w1 hw1 (Ne.symm hw1z)
  have hA0 : |A z0| ≤ P z0 := by rw [hAv, hPv]; exact hA z0
  have hA1 : |A w1| ≤ P w1 := by rw [hAv, hPv]; exact hA w1
  have habs : |A z0| = P z0 := by
    have h := congrArg abs e01
    rw [abs_mul, abs_mul, abs_of_pos hP0, abs_of_pos hP1] at h
    nlinarith [abs_nonneg (A z0), abs_nonneg (A w1)]
  have hsq : A z0 ^ 2 = P z0 ^ 2 := by rw [← sq_abs, habs]
  have hA0ne : A z0 ≠ 0 := by
    intro h
    rw [h, abs_zero] at habs
    linarith
  have hall : ∀ w ∈ unitDiscExterior, A w = A z0 / P z0 * P w := by
    intro w hw
    by_cases hwz : w = z0
    · rw [hwz]
      field_simp
    · have h' := hPA z0 hz0 w hw (Ne.symm hwz)
      rw [div_mul_eq_mul_div, eq_div_iff hP0.ne']
      apply mul_left_cancel₀ hA0ne
      linear_combination (-P z0) * h' + (-P w) * hsq
  set s := A z0 / P z0 with hsdef
  have hs2 : s ^ 2 = 1 := by rw [hsdef, div_pow, hsq, div_self (pow_ne_zero 2 hP0.ne')]
  have hν : ∀ w ∈ unitDiscExterior, ν w = ((s * c : ℝ) : ℂ) * μ w := by
    intro w hw
    by_cases hμw : μ w = 0
    · have h := hhc w hw
      rw [hμw, norm_zero, mul_zero, norm_eq_zero] at h
      rw [h, hμw, mul_zero]
    · have hre : (conj (μ w) * ν w).re = s * P w := by rw [← hAv]; exact hall w hw
      have hnorm : ‖conj (μ w) * ν w‖ = P w := by rw [norm_mul, Complex.norm_conj, hPv]
      have him : (conj (μ w) * ν w).im = 0 := by
        have h1 := Complex.sq_norm (conj (μ w) * ν w)
        rw [Complex.normSq_apply, hnorm, hre] at h1
        nlinarith [sq_nonneg (conj (μ w) * ν w).im]
      have hX1 : conj (μ w) * ν w = ((s * P w : ℝ) : ℂ) :=
        Complex.ext (by rw [Complex.ofReal_re]; exact hre) (by rw [Complex.ofReal_im]; exact him)
      have hX2 : ((s * P w : ℝ) : ℂ) = ((s * c : ℝ) : ℂ) * (conj (μ w) * μ w) := by
        rw [hPv, hhc w hw, mul_comm (conj (μ w)), Complex.mul_conj, Complex.normSq_eq_norm_sq]
        push_cast
        ring
      have hcμ : conj (μ w) ≠ 0 := by rwa [map_ne_zero]
      have h3 : conj (μ w) * ν w = conj (μ w) * (((s * c : ℝ) : ℂ) * μ w) := by
        rw [hX1, hX2]
        ring
      exact mul_left_cancel₀ hcμ h3
  have := hli (s * c) (-1) (by
    funext z
    simp only [Pi.add_apply, Pi.smul_apply, Matrix.cons_val_one, Matrix.head_cons,
      Pi.zero_apply]
    rw [hν z z.2, Complex.real_smul, Complex.real_smul]
    push_cast
    ring)
  norm_num at this

/-- The symmetrized integrand: `(g₁²h₂² + h₁²g₂²)/2 - a₁a₂ = (g₁h₂ - h₁g₂)²/2 + (g₁h₁g₂h₂ - a₁a₂)`, the last term
`≥ 0` when `|aᵢ| ≤ gᵢhᵢ`. -/
theorem s7g_f3_qpt {g₁ h₁ g₂ h₂ a₁ a₂ : ℝ} (hg₁ : 0 ≤ g₁) (hh₁ : 0 ≤ h₁) (ha₁ : |a₁| ≤ g₁ * h₁)
    (ha₂ : |a₂| ≤ g₂ * h₂) :
    (g₁ ^ 2 * h₂ ^ 2 + h₁ ^ 2 * g₂ ^ 2) / 2 - a₁ * a₂ = (g₁ * h₂ - h₁ * g₂) ^ 2 / 2 + (g₁ * h₁ * (g₂ * h₂) - a₁ * a₂) ∧
      0 ≤ g₁ * h₁ * (g₂ * h₂) - a₁ * a₂ := by
  refine ⟨by ring, ?_⟩
  have h := mul_le_mul ha₁ ha₂ (abs_nonneg _) (by positivity)
  rw [← abs_mul] at h
  linarith [le_abs_self (a₁ * a₂)]

/-- STUB STRICT. `B(α, α) < B(|μ|², |ν|²)` for `μ, ν` with ℝ-independent restrictions to `𝔻*`. -/
theorem s7g_f3_strict {μ ν : ℂ → ℂ} (hμ : μ ∈ harmonicL2 unitDiscExterior) (hν : ν ∈ harmonicL2 unitDiscExterior)
    (hli : LinearIndependent ℝ ![(fun z : unitDiscExterior => μ z), (fun z : unitDiscExterior => ν z)]) :
    (l2Inner (fun z => ((conj (μ z) * ν z).re : ℂ)) (resolventStar fun z => ((conj (μ z) * ν z).re : ℂ))).re <
      (l2Inner (fun z => ((‖μ z‖ ^ 2 : ℝ) : ℂ)) (resolventStar fun z => ((‖ν z‖ ^ 2 : ℝ) : ℂ))).re := by
  have hm : MeasurableSet unitDiscExterior := wp_exterior_isOpen.measurableSet
  have hμc := wp_harmonic_continuousOn hμ
  have hνc := wp_harmonic_continuousOn hν
  have hbμ : ∀ w ∈ unitDiscExterior, ‖μ w‖ ≤ (Real.sqrt (12 / π) / 4) * (normL2 unitDiscExterior μ).toReal :=
    fun w hw => wp_harmonic_pointwise_bound hμ hw
  have hbν : ∀ w ∈ unitDiscExterior, ‖ν w‖ ≤ (Real.sqrt (12 / π) / 4) * (normL2 unitDiscExterior ν).toReal :=
    fun w hw => wp_harmonic_pointwise_bound hν hw
  have hac : ContinuousOn (fun z => ‖μ z‖ ^ 2) unitDiscExterior := hμc.norm.pow 2
  have hbc : ContinuousOn (fun z => ‖ν z‖ ^ 2) unitDiscExterior := hνc.norm.pow 2
  have hαc : ContinuousOn (fun z => (conj (μ z) * ν z).re) unitDiscExterior :=
    Complex.continuous_re.comp_continuousOn ((Complex.continuous_conj.comp_continuousOn hμc).mul hνc)
  have hαle : ∀ z, |(conj (μ z) * ν z).re| ≤ ‖μ z‖ * ‖ν z‖ := fun z => by
    have := Complex.abs_re_le_norm (conj (μ z) * ν z)
    rwa [norm_mul, Complex.norm_conj] at this
  have bA : ∀ w ∈ unitDiscExterior, |‖μ w‖ ^ 2| ≤ ((Real.sqrt (12 / π) / 4) * (normL2 unitDiscExterior μ).toReal) ^ 2 :=
    fun w hw => by
      rw [abs_of_nonneg (sq_nonneg _)]
      exact pow_le_pow_left₀ (norm_nonneg _) (hbμ w hw) 2
  have bB : ∀ w ∈ unitDiscExterior, |‖ν w‖ ^ 2| ≤ ((Real.sqrt (12 / π) / 4) * (normL2 unitDiscExterior ν).toReal) ^ 2 :=
    fun w hw => by
      rw [abs_of_nonneg (sq_nonneg _)]
      exact pow_le_pow_left₀ (norm_nonneg _) (hbν w hw) 2
  have bα : ∀ w ∈ unitDiscExterior, |(conj (μ w) * ν w).re| ≤
      ((Real.sqrt (12 / π) / 4) * (normL2 unitDiscExterior μ).toReal) *
        ((Real.sqrt (12 / π) / 4) * (normL2 unitDiscExterior ν).toReal) :=
    fun w hw => (hαle w).trans (mul_le_mul (hbμ w hw) (hbν w hw) (norm_nonneg _) ((norm_nonneg _).trans (hbμ w hw)))
  have iA := wp_integrable_sq hμ
  have iB := wp_integrable_sq hν
  have hρm : Measurable rho := by unfold rho; fun_prop
  have iα : IntegrableOn (fun z => (conj (μ z) * ν z).re * rho z) unitDiscExterior := by
    refine (iA.add iB).mono' ((hαc.aestronglyMeasurable hm).mul hρm.aestronglyMeasurable) ?_
    filter_upwards with z
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (wp_rho_nonneg z)]
    have h1 := hαle z
    have h2 : ‖μ z‖ * ‖ν z‖ ≤ ‖μ z‖ ^ 2 + ‖ν z‖ ^ 2 := by
      nlinarith [sq_nonneg (‖μ z‖ - ‖ν z‖), norm_nonneg (μ z), norm_nonneg (ν z)]
    show |(conj (μ z) * ν z).re| * rho z ≤ ‖μ z‖ ^ 2 * rho z + ‖ν z‖ ^ 2 * rho z
    nlinarith [wp_rho_nonneg z]
  obtain ⟨Iab, Eab⟩ := s7g_f3_dbl hac hbc bB iA
  obtain ⟨Iba, Eba⟩ := s7g_f3_dbl hbc hac bA iB
  obtain ⟨Iαα, Eαα⟩ := s7g_f3_dbl hαc hαc bα iα
  -- symmetry of the pairing
  have hS := s7g_c79_sym hν hν hμ hμ
  have e5 : (fun z => ν z * conj (ν z)) = fun z => ((‖ν z‖ ^ 2 : ℝ) : ℂ) :=
    funext fun z => by rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have e6 : (fun z => μ z * conj (μ z)) = fun z => ((‖μ z‖ ^ 2 : ℝ) : ℂ) :=
    funext fun z => by rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have e3 : (fun z => conj (μ z) * μ z) = fun z => ((‖μ z‖ ^ 2 : ℝ) : ℂ) :=
    funext fun z => by rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have e4 : (fun z => conj (ν z) * ν z) = fun z => ((‖ν z‖ ^ 2 : ℝ) : ℂ) :=
    funext fun z => by rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  rw [e3, e4, e5, e6] at hS
  have hsym := congrArg Complex.re hS
  rw [Eba, Eab] at hsym
  rw [Eαα, Eab]
  -- the measure on `𝔻* × 𝔻*`
  set M := (volume.restrict unitDiscExterior).prod (volume.restrict unitDiscExterior) with hMdef
  have hM : M = volume.restrict (unitDiscExterior ×ˢ unitDiscExterior) := by
    rw [hMdef, Measure.prod_restrict, ← Measure.volume_eq_prod]
  set Q : ℂ → ℂ → ℝ := fun z w => (‖μ z‖ ^ 2 * ‖ν w‖ ^ 2 + ‖ν z‖ ^ 2 * ‖μ w‖ ^ 2) / 2 -
    (conj (μ z) * ν z).re * (conj (μ w) * ν w).re with hQdef
  set E : ℂ × ℂ → ℝ := fun p =>
    (resolventKernel p.1 p.2 * ‖ν p.2‖ ^ 2 * rho p.2 * (‖μ p.1‖ ^ 2 * rho p.1) +
      resolventKernel p.1 p.2 * ‖μ p.2‖ ^ 2 * rho p.2 * (‖ν p.1‖ ^ 2 * rho p.1)) / 2 -
      resolventKernel p.1 p.2 * (conj (μ p.2) * ν p.2).re * rho p.2 * ((conj (μ p.1) * ν p.1).re * rho p.1)
    with hEdef
  have hEi : Integrable E M := ((Iab.add Iba).div_const 2).sub Iαα
  have hEQ : ∀ p : ℂ × ℂ, E p = resolventKernel p.1 p.2 * rho p.1 * rho p.2 * Q p.1 p.2 := fun p => by
    rw [hEdef, hQdef]
    ring
  have hint : ∫ p, E p ∂M =
      ((∫ p, resolventKernel p.1 p.2 * ‖ν p.2‖ ^ 2 * rho p.2 * (‖μ p.1‖ ^ 2 * rho p.1) ∂M) +
        ∫ p, resolventKernel p.1 p.2 * ‖μ p.2‖ ^ 2 * rho p.2 * (‖ν p.1‖ ^ 2 * rho p.1) ∂M) / 2 -
        ∫ p, resolventKernel p.1 p.2 * (conj (μ p.2) * ν p.2).re * rho p.2 * ((conj (μ p.1) * ν p.1).re * rho p.1) ∂M := by
    have h1 : Integrable (fun p : ℂ × ℂ => (resolventKernel p.1 p.2 * ‖ν p.2‖ ^ 2 * rho p.2 * (‖μ p.1‖ ^ 2 * rho p.1) +
        resolventKernel p.1 p.2 * ‖μ p.2‖ ^ 2 * rho p.2 * (‖ν p.1‖ ^ 2 * rho p.1)) / 2) M :=
      (Iab.add Iba).div_const 2
    simp only [hEdef]
    rw [integral_sub h1 Iαα, integral_div, integral_add Iab Iba]
  -- pointwise facts off the diagonal
  have hQpt : ∀ z w, (Q z w = (‖μ z‖ * ‖ν w‖ - ‖ν z‖ * ‖μ w‖) ^ 2 / 2 +
      (‖μ z‖ * ‖ν z‖ * (‖μ w‖ * ‖ν w‖) - (conj (μ z) * ν z).re * (conj (μ w) * ν w).re)) ∧
      0 ≤ ‖μ z‖ * ‖ν z‖ * (‖μ w‖ * ‖ν w‖) - (conj (μ z) * ν z).re * (conj (μ w) * ν w).re := by
    intro z w
    have h := s7g_f3_qpt (norm_nonneg (μ z)) (norm_nonneg (ν z)) (hαle z) (hαle w)
      (g₂ := ‖μ w‖) (h₂ := ‖ν w‖)
    rw [hQdef]
    simpa only [mul_pow] using h
  have hQnn : ∀ z w, 0 ≤ Q z w := fun z w => by
    rw [(hQpt z w).1]
    have := (hQpt z w).2
    positivity
  have hdiag : ∀ᵐ p ∂(volume : Measure (ℂ × ℂ)), p.1 ≠ p.2 := by
    have h0 : (volume : Measure (ℂ × ℂ)) (Set.diagonal ℂ) = 0 := by
      rw [Measure.volume_eq_prod, Measure.measure_prod_null measurableSet_diagonal]
      refine Eventually.of_forall fun z => ?_
      have hs : Prod.mk z ⁻¹' Set.diagonal ℂ = {z} := by
        ext w
        simp [Set.diagonal, eq_comm]
      show volume (Prod.mk z ⁻¹' Set.diagonal ℂ) = 0
      rw [hs, measure_singleton]
    have h0' : ∀ᵐ p ∂(volume : Measure (ℂ × ℂ)), p ∉ Set.diagonal ℂ := by
      rw [ae_iff]
      simp only [not_not, Set.setOf_mem_eq]
      exact h0
    filter_upwards [h0'] with p hp
    exact hp
  have hS2 : MeasurableSet (unitDiscExterior ×ˢ unitDiscExterior) := hm.prod hm
  have hnn : 0 ≤ᵐ[volume.restrict (unitDiscExterior ×ˢ unitDiscExterior)] E := by
    filter_upwards [ae_restrict_mem hS2, ae_restrict_of_ae hdiag] with p hp hne
    show 0 ≤ E p
    rw [hEQ]
    have hK := RK2 hne (Or.inr ⟨hp.1, hp.2⟩)
    have := hQnn p.1 p.2
    have := wp_rho_nonneg p.1
    have := wp_rho_nonneg p.2
    positivity
  -- strict positivity, or the equality case
  have hpos : 0 < ∫ p, E p ∂M := by
    by_cases hQ : ∃ z₀ ∈ unitDiscExterior, ∃ w₀ ∈ unitDiscExterior, z₀ ≠ w₀ ∧ 0 < Q z₀ w₀
    · obtain ⟨z₀, hz₀, w₀, hw₀, hzw, hq⟩ := hQ
      rw [hM]
      have hEi' : IntegrableOn E (unitDiscExterior ×ˢ unitDiscExterior) := by
        show Integrable E (volume.restrict (unitDiscExterior ×ˢ unitDiscExterior))
        rw [← hM]
        exact hEi
      refine (setIntegral_pos_iff_support_of_nonneg_ae hnn hEi').mpr ?_
      have hO : IsOpen ((unitDiscExterior ×ˢ unitDiscExterior) ∩ {p : ℂ × ℂ | p.1 ≠ p.2}) :=
        (wp_exterior_isOpen.prod wp_exterior_isOpen).inter (isOpen_ne_fun continuous_fst continuous_snd)
      have hQc : ContinuousOn (fun p : ℂ × ℂ => Q p.1 p.2) ((unitDiscExterior ×ˢ unitDiscExterior) ∩ {p : ℂ × ℂ | p.1 ≠ p.2}) := by
        have m1 : MapsTo (fun p : ℂ × ℂ => p.1) ((unitDiscExterior ×ˢ unitDiscExterior) ∩ {p : ℂ × ℂ | p.1 ≠ p.2})
            unitDiscExterior := fun p hp => hp.1.1
        have m2 : MapsTo (fun p : ℂ × ℂ => p.2) ((unitDiscExterior ×ˢ unitDiscExterior) ∩ {p : ℂ × ℂ | p.1 ≠ p.2})
            unitDiscExterior := fun p hp => hp.1.2
        rw [hQdef]
        exact ((((hac.comp continuousOn_fst m1).mul (hbc.comp continuousOn_snd m2)).add
          ((hbc.comp continuousOn_fst m1).mul (hac.comp continuousOn_snd m2))).div_const 2).sub
          ((hαc.comp continuousOn_fst m1).mul (hαc.comp continuousOn_snd m2))
      have hU := hQc.isOpen_inter_preimage hO (isOpen_Ioi (a := (0 : ℝ)))
      have hmeas : 0 < volume (((unitDiscExterior ×ˢ unitDiscExterior) ∩ {p : ℂ × ℂ | p.1 ≠ p.2}) ∩
          (fun p : ℂ × ℂ => Q p.1 p.2) ⁻¹' Ioi 0) :=
        hU.measure_pos volume ⟨(z₀, w₀), ⟨⟨hz₀, hw₀⟩, hzw⟩, hq⟩
      refine lt_of_lt_of_le hmeas (measure_mono fun p hp => ⟨?_, hp.1.1⟩)
      show E p ≠ 0
      rw [hEQ]
      have hK := RK2 hp.1.2 (Or.inr ⟨hp.1.1.1, hp.1.1.2⟩)
      have h1 := rho_pos_of_norm_ne_one (ne_of_gt hp.1.1.1)
      have h2 := rho_pos_of_norm_ne_one (ne_of_gt hp.1.1.2)
      have h3 : 0 < Q p.1 p.2 := hp.2
      positivity
    · exfalso
      push_neg at hQ
      refine s7g_f3_dep hμc (fun z hz w hw hzw => ?_) (fun z hz w hw hzw => ?_) hli
      · have hle := hQ z hz w hw hzw
        rw [(hQpt z w).1] at hle
        have h0 := (hQpt z w).2
        have hsq : (‖μ z‖ * ‖ν w‖ - ‖ν z‖ * ‖μ w‖) ^ 2 = 0 := by
          nlinarith [sq_nonneg (‖μ z‖ * ‖ν w‖ - ‖ν z‖ * ‖μ w‖)]
        have := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 hsq
        linarith
      · have hle := hQ z hz w hw hzw
        rw [(hQpt z w).1] at hle
        have h0 := (hQpt z w).2
        nlinarith [sq_nonneg (‖μ z‖ * ‖ν w‖ - ‖ν z‖ * ‖μ w‖)]
  rw [hint] at hpos
  linarith

/-- `thm_7_14`, assembled from the stubs. -/
theorem s7g_thm_7_14 :
    (∀ μ ∈ harmonicL2 unitDiscExterior, ∀ ν ∈ harmonicL2 unitDiscExterior,
      LinearIndependent ℝ ![(fun z : unitDiscExterior => μ z), (fun z : unitDiscExterior => ν z)] →
      0 < sectionalDen μ ν ∧ (sectionalNum μ ν).im = 0 ∧ (sectionalNum μ ν).re < 0) ∧
      ∀ μ ∈ harmonicL2 unitDiscExterior, (∃ z ∈ unitDiscExterior, μ z ≠ 0) →
        (riemannR μ μ μ μ).im = 0 ∧ (riemannR μ μ μ μ).re < 0 := by
  refine ⟨fun μ hμ ν hν hli => ?_, fun μ hμ hne => ?_⟩
  · have i1 := s7g_f3_im (fun z => (conj (μ z) * ν z).re) (fun z => (conj (μ z) * ν z).re)
    have i2 := s7g_f3_im (fun z => (conj (μ z) * ν z).im) (fun z => (conj (μ z) * ν z).im)
    have i3 := s7g_f3_im (fun z => ‖μ z‖ ^ 2) (fun z => ‖ν z‖ ^ 2)
    have h1 := s7g_f3_psd hμ hν
    have h2 := s7g_f3_strict hμ hν hli
    rw [s7g_f3_expand hμ hν]
    generalize l2Inner (fun z => ((conj (μ z) * ν z).re : ℂ)) (resolventStar fun z => ((conj (μ z) * ν z).re : ℂ)) = A
      at i1 h2 ⊢
    generalize l2Inner (fun z => ((conj (μ z) * ν z).im : ℂ)) (resolventStar fun z => ((conj (μ z) * ν z).im : ℂ)) = Bb
      at i2 h1 ⊢
    generalize l2Inner (fun z => ((‖μ z‖ ^ 2 : ℝ) : ℂ)) (resolventStar fun z => ((‖ν z‖ ^ 2 : ℝ) : ℂ)) = C at i3 h2 ⊢
    refine ⟨sectionalDen_pos_of_restriction_linearIndependent hμ hν hli, ?_, ?_⟩
    · simp [i1, i2, i3]
    · simp only [Complex.sub_re, Complex.mul_re, i1, i2, i3]
      norm_num
      linarith
  · have i4 := s7g_f3_im (fun z => ‖μ z‖ ^ 2) (fun z => ‖μ z‖ ^ 2)
    have h := wp_harmonic_resolvent_energy_pos hμ hne
    rw [s7g_f3_holo hμ]
    generalize l2Inner (fun z => ((‖μ z‖ ^ 2 : ℝ) : ℂ)) (resolventStar fun z => ((‖μ z‖ ^ 2 : ℝ) : ℂ)) = X at i4 h ⊢
    refine ⟨by simp [i4], ?_⟩
    simp only [Complex.mul_re, i4]
    norm_num
    exact h

/-- **Theorem 7.14** (TT:3128–3156). The sectional and holomorphic sectional curvatures of `T(1)` are negative.
- For `μ, ν ∈ H^{-1,1}(𝔻*)` linearly independent over `ℝ`: `g > 0` and `R < 0` (`R` is real).
- For `μ ≠ 0`, the holomorphic sectional curvature `R_{μμ̄μμ̄}` is negative.

[CORRECTION 2026-10-25] Linear independence is required of the restrictions to `𝔻*`, where the metric lives. With
independence of the raw functions on `ℂ`, two functions supported at `0` gave `sectionalDen = 0` (lean6,
`collaboration/lean6/CurvatureStatementIssue.lean`). -/
theorem thm_7_14 :
    (∀ μ ∈ harmonicL2 unitDiscExterior, ∀ ν ∈ harmonicL2 unitDiscExterior,
      LinearIndependent ℝ ![(fun z : unitDiscExterior => μ z), (fun z : unitDiscExterior => ν z)] →
      0 < sectionalDen μ ν ∧ (sectionalNum μ ν).im = 0 ∧ (sectionalNum μ ν).re < 0) ∧
      ∀ μ ∈ harmonicL2 unitDiscExterior, (∃ z ∈ unitDiscExterior, μ z ≠ 0) →
        (riemannR μ μ μ μ).im = 0 ∧ (riemannR μ μ μ μ).re < 0 := by
  exact s7g_thm_7_14

end TakhtajanTeo
