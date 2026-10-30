import TakhtajanTeo.Ch2.S1_BP78Completed

/-!
# The explicit Becker–Pommerenke chain and extension (BP78 (1.6)–(1.9))

Explicit computations for the Löwner-chain proof of Theorem 1.6 (iii) ⇒ (i) (`ab16_iii_imp_i`, 下属1):
* `ab16x_chain_pde`: the chain `f_t(z) = f(e^{-t}z) + (e^t - e^{-t}) z f'(e^{-t}z)` satisfies `∂_t f_t = z p f_t'`
  in the form `f_t' = e^t f'(w)(1 - q)`, `∂_t f_t = z e^t f'(w)(1 + q)`;
* `ab16x_q_bound`: `|q| ≤ 1/2` on `(0, α] × 𝔻̄` under (iii);
* `ab16x_ext_dilatation`, `ab16x_dilatation_tendsto`: the extension `f(1/z̄) + (z - 1/z̄) f'(1/z̄)` off `𝔻̄` and its
  complex dilatation.
-/

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal ComplexConjugate Classical Real
noncomputable section
namespace TakhtajanTeo
open LiZhongQC
namespace Ch2

theorem ab16xe_exp_rel (t : ℝ) :
    (Real.exp t : ℂ) * (Real.exp (-t) : ℂ) = 1 ∧ (Real.exp (-(2 * t)) : ℂ) = (Real.exp (-t) : ℂ) ^ 2 := by
  refine ⟨?_, ?_⟩
  · rw [← Complex.ofReal_mul, ← Real.exp_add, add_neg_cancel, Real.exp_zero, Complex.ofReal_one]
  · rw [← Complex.ofReal_pow, ← Real.exp_nat_mul]
    congr 2
    push_cast
    ring

theorem ab16xe_mem {t : ℝ} {z : ℂ} (hz : ‖z‖ < Real.exp t) : (Real.exp (-t) : ℂ) * z ∈ unitDisc := by
  apply mem_ball_zero_iff.mpr
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
  have h1 : Real.exp (-t) * Real.exp t = 1 := by rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  calc Real.exp (-t) * ‖z‖ < Real.exp (-t) * Real.exp t := mul_lt_mul_of_pos_left hz (Real.exp_pos _)
    _ = 1 := h1

/-- The BP78 chain satisfies the Löwner PDE (BP78 (1.9)), with `f_t' = e^t f'(w)(1 - q)`, `w = e^{-t} z`. -/
theorem ab16x_chain_pde {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f unitDisc) (hinj : InjOn f unitDisc) {t : ℝ} (ht : 0 < t) {z : ℂ}
    (hz : ‖z‖ < Real.exp t) :
    let w : ℂ := (Real.exp (-t) : ℂ) * z
    let q : ℂ := -(1 - (Real.exp (-(2 * t)) : ℂ)) * w * preSchwarzian f w
    deriv (fun u => f ((Real.exp (-t) : ℂ) * u) +
        ((Real.exp t : ℂ) - (Real.exp (-t) : ℂ)) * u * deriv f ((Real.exp (-t) : ℂ) * u)) z =
        (Real.exp t : ℂ) * deriv f w * (1 - q) ∧
      HasDerivAt (fun σ : ℝ => f ((Real.exp (-σ) : ℂ) * z) +
          ((Real.exp σ : ℂ) - (Real.exp (-σ) : ℂ)) * z * deriv f ((Real.exp (-σ) : ℂ) * z))
        (z * ((Real.exp t : ℂ) * deriv f w * (1 + q))) t := by
  intro w q
  -- `0 < t` is not needed: the identities hold for every `t` with `|e^{-t} z| < 1`
  have _ht := ht
  have hw : w ∈ unitDisc := ab16xe_mem hz
  have hU : IsOpen unitDisc := isOpen_ball
  have hf1 : HasDerivAt f (deriv f w) w := (hf.differentiableAt (hU.mem_nhds hw)).hasDerivAt
  have hf2 : HasDerivAt (deriv f) (deriv (deriv f) w) w :=
    ((hf.deriv hU).differentiableAt (hU.mem_nhds hw)).hasDerivAt
  have hne : deriv f w ≠ 0 := deriv_ne_zero_of_injOn hU hf hinj hw
  obtain ⟨he1, he2⟩ := ab16xe_exp_rel t
  set a : ℂ := (Real.exp (-t) : ℂ) with ha
  set e : ℂ := (Real.exp t : ℂ) with he
  have hwz : w = a * z := rfl
  have hq : q = -(1 - a ^ 2) * w * (deriv (deriv f) w / deriv f w) := by
    simp only [q, he2, preSchwarzian]
  have hDD : deriv f w * (deriv (deriv f) w / deriv f w) = deriv (deriv f) w := mul_div_cancel₀ _ hne
  refine ⟨?_, ?_⟩
  · -- the `z`-derivative
    have hlin : HasDerivAt (fun u : ℂ => a * u) a z := by simpa using (hasDerivAt_id z).const_mul a
    have h1 : HasDerivAt (fun u => f (a * u)) (deriv f w * a) z := hf1.comp z hlin
    have h2 : HasDerivAt (fun u => deriv f (a * u)) (deriv (deriv f) w * a) z :=
      HasDerivAt.comp (h₂ := deriv f) z hf2 hlin
    have h3 : HasDerivAt (fun u => (e - a) * u * deriv f (a * u))
        ((e - a) * deriv f w + (e - a) * z * (deriv (deriv f) w * a)) z := by
      have hm := ((hasDerivAt_id z).const_mul (e - a)).mul h2
      simp only [id, mul_one] at hm
      convert hm using 1
    have h4 : HasDerivAt (fun u => f (a * u) + (e - a) * u * deriv f (a * u))
        (deriv f w * a + ((e - a) * deriv f w + (e - a) * z * (deriv (deriv f) w * a))) z := h1.add h3
    rw [h4.deriv, hq, show e * deriv f w * (1 - -(1 - a ^ 2) * w * (deriv (deriv f) w / deriv f w)) =
      e * deriv f w + e * (1 - a ^ 2) * w * (deriv f w * (deriv (deriv f) w / deriv f w)) by ring, hDD, hwz]
    linear_combination (a ^ 2 * z * deriv (deriv f) w) * he1
  · -- the `t`-derivative
    have hA : HasDerivAt (fun σ : ℝ => (Real.exp (-σ) : ℂ)) (-a) t := by
      have h := ((Real.hasDerivAt_exp (-t)).comp t (hasDerivAt_neg t)).ofReal_comp
      simpa [Function.comp_def, ha] using h
    have hE : HasDerivAt (fun σ : ℝ => (Real.exp σ : ℂ)) e t := by
      have h := (Real.hasDerivAt_exp t).ofReal_comp
      simpa [Function.comp_def, he] using h
    have hlin : HasDerivAt (fun σ : ℝ => (Real.exp (-σ) : ℂ) * z) (-a * z) t := hA.mul_const z
    have h1 : HasDerivAt (fun σ : ℝ => f ((Real.exp (-σ) : ℂ) * z)) (deriv f w * (-a * z)) t :=
      hf1.comp t hlin
    have h2 : HasDerivAt (fun σ : ℝ => deriv f ((Real.exp (-σ) : ℂ) * z)) (deriv (deriv f) w * (-a * z)) t :=
      HasDerivAt.comp (h₂ := deriv f) t hf2 hlin
    have h3 : HasDerivAt (fun σ : ℝ => ((Real.exp σ : ℂ) - (Real.exp (-σ) : ℂ)) * z)
        ((e - -a) * z) t := (hE.sub hA).mul_const z
    have h5 : HasDerivAt (fun σ : ℝ => ((Real.exp σ : ℂ) - (Real.exp (-σ) : ℂ)) * z *
        deriv f ((Real.exp (-σ) : ℂ) * z))
        ((e - -a) * z * deriv f w + (e - a) * z * (deriv (deriv f) w * (-a * z))) t := h3.mul h2
    have h4 := h1.add h5
    refine h4.congr_deriv ?_
    rw [hq, show z * (e * deriv f w * (1 + -(1 - a ^ 2) * w * (deriv (deriv f) w / deriv f w))) =
      z * e * deriv f w - z * e * (1 - a ^ 2) * w * (deriv f w * (deriv (deriv f) w / deriv f w)) by ring,
      hDD, hwz]
    linear_combination (-(a ^ 2 * z ^ 2 * deriv (deriv f) w)) * he1

/-- (BP78 (1.7)) Under (iii) the chain is a Löwner chain with `|q| ≤ 1/2` on `(0, α] × 𝔻̄`. -/
theorem ab16x_q_bound {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f unitDisc) (hinj : InjOn f unitDisc)
    (hA : Tendsto (fun z => ((1 - ‖z‖ ^ 2) : ℂ) * preSchwarzian f z)
      (comap (fun z : ℂ => ‖z‖) (𝓝[<] 1)) (𝓝 0)) :
    ∃ α > 0, ∀ t ∈ Ioc 0 α, ∀ z ∈ closedBall (0 : ℂ) 1,
      ‖(1 - (Real.exp (-(2 * t)) : ℂ)) * ((Real.exp (-t) : ℂ) * z) *
        preSchwarzian f ((Real.exp (-t) : ℂ) * z)‖ ≤ 1 / 2 := by
  have hU : IsOpen unitDisc := isOpen_ball
  obtain ⟨r, hr1, hr⟩ := (ab16_tendsto_iff.mp hA) (1 / 2) (by norm_num)
  set r' : ℝ := max r (1 / 2) with hr'
  have hr'1 : r' < 1 := max_lt hr1 (by norm_num)
  have hr'0 : 0 ≤ r' := le_max_of_le_right (by norm_num)
  have hsub : closedBall (0 : ℂ) r' ⊆ unitDisc := closedBall_subset_ball hr'1
  -- `𝒜f` is continuous on `𝔻`
  have hcont : ContinuousOn (preSchwarzian f) unitDisc := by
    have h1 : ContinuousOn (deriv (deriv f)) unitDisc := ((hf.deriv hU).deriv hU).continuousOn
    have h2 : ContinuousOn (deriv f) unitDisc := (hf.deriv hU).continuousOn
    exact h1.div h2 (fun w hw => deriv_ne_zero_of_injOn hU hf hinj hw)
  obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : ℂ) r').exists_bound_of_continuousOn (hcont.mono hsub)
  have hM0 : 0 ≤ M := le_trans (norm_nonneg _) (hM 0 (mem_closedBall_self hr'0))
  refine ⟨1 / (4 * (M + 1)), by positivity, fun t ht z hz => ?_⟩
  have ht0 : 0 < t := ht.1
  obtain ⟨-, he2⟩ := ab16xe_exp_rel t
  set a : ℝ := Real.exp (-t) with ha
  have ha0 : 0 < a := Real.exp_pos _
  have ha1 : a < 1 := by rw [ha]; exact Real.exp_lt_one_iff.mpr (by linarith)
  have hz1 : ‖z‖ ≤ 1 := mem_closedBall_zero_iff.mp hz
  set w : ℂ := (a : ℂ) * z with hwdef
  have hwn : ‖w‖ = a * ‖z‖ := by rw [hwdef, norm_mul, Complex.norm_real, Real.norm_of_nonneg ha0.le]
  have hwa : ‖w‖ ≤ a := by rw [hwn]; nlinarith [norm_nonneg z]
  have h1a : 0 ≤ 1 - a ^ 2 := by nlinarith
  rw [he2, mul_assoc, ab16_norm_mul h1a, norm_mul, ← mul_assoc]
  by_cases hw : ‖w‖ ≤ r'
  · -- small `|w|`: `1 - e^{-2t} ≤ 2t`
    have hb := hM w (mem_closedBall_zero_iff.mpr hw)
    have h2t : 1 - a ^ 2 ≤ 2 * t := by
      have : a ^ 2 = Real.exp (-(2 * t)) := by rw [ha, ← Real.exp_nat_mul]; push_cast; ring_nf
      rw [this]
      linarith [Real.add_one_le_exp (-(2 * t))]
    have htα : t ≤ 1 / (4 * (M + 1)) := ht.2
    have hw1 : ‖w‖ ≤ 1 := hwa.trans ha1.le
    calc (1 - a ^ 2) * ‖w‖ * ‖preSchwarzian f w‖ ≤ (2 * t) * 1 * M := by
          apply mul_le_mul (mul_le_mul h2t hw1 (norm_nonneg _) (by linarith)) hb (norm_nonneg _)
            (by positivity)
      _ ≤ 2 * (1 / (4 * (M + 1))) * 1 * M := by gcongr
      _ ≤ 1 / 2 := by
          rw [show 2 * (1 / (4 * (M + 1))) * 1 * M = M / (2 * (M + 1)) by field_simp; ring]
          rw [div_le_iff₀ (by positivity)]
          linarith
  · -- `|w|` close to `1`: `1 - e^{-2t} ≤ 1 - |w|²`
    rw [not_le] at hw
    have hrw : r < ‖w‖ := lt_of_le_of_lt (le_max_left _ _) hw
    have hw1 : ‖w‖ < 1 := lt_of_le_of_lt hwa ha1
    have hb := hr w hrw hw1
    have h1w : 0 ≤ 1 - ‖w‖ ^ 2 := by nlinarith [norm_nonneg w]
    have hle : 1 - a ^ 2 ≤ 1 - ‖w‖ ^ 2 := by nlinarith [norm_nonneg w]
    have hnorm : ‖((1 - ‖w‖ ^ 2 : ℝ) : ℂ) * preSchwarzian f w‖ = (1 - ‖w‖ ^ 2) * ‖preSchwarzian f w‖ := by
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg h1w]
    have hb' : (1 - ‖w‖ ^ 2) * ‖preSchwarzian f w‖ < 1 / 2 := by
      rw [← hnorm]; push_cast; exact hb
    calc (1 - a ^ 2) * ‖w‖ * ‖preSchwarzian f w‖ ≤ (1 - ‖w‖ ^ 2) * 1 * ‖preSchwarzian f w‖ := by
          apply mul_le_mul_of_nonneg_right (mul_le_mul hle hw1.le (norm_nonneg _) h1w) (norm_nonneg _)
      _ ≤ 1 / 2 := by rw [mul_one]; exact hb'.le

/-- The real derivative of the explicit extension `F(u) = f(1/ū) + (u - 1/ū) f'(1/ū)` at `|z| > 1`:
`dF(h) = f'(ζ) h - (z - ζ) f''(ζ) h̄ / z̄²`, `ζ = 1/z̄`. -/
theorem ab16xe_hasFDerivAt {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f unitDisc) {z : ℂ} (hz : 1 < ‖z‖) :
    HasFDerivAt (fun u : ℂ => f (conj u)⁻¹ + (u - (conj u)⁻¹) * deriv f (conj u)⁻¹)
      (deriv f (conj z)⁻¹ • (1 : ℂ →L[ℝ] ℂ) +
        (-(z - (conj z)⁻¹) * deriv (deriv f) (conj z)⁻¹ / conj z ^ 2) • Complex.conjCLE.toContinuousLinearMap) z := by
  have hU : IsOpen unitDisc := isOpen_ball
  have hz0 : z ≠ 0 := by intro h; rw [h, norm_zero] at hz; linarith
  have hc0 : conj z ≠ 0 := (map_ne_zero _).mpr hz0
  have hζ : (conj z)⁻¹ ∈ unitDisc := by
    apply mem_ball_zero_iff.mpr
    rw [norm_inv, Complex.norm_conj]
    exact inv_lt_one_of_one_lt₀ hz
  -- `ζ(u) = (conj u)⁻¹`
  have hinv : HasFDerivAt (fun x : ℂ => x⁻¹) ((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) (-(conj z ^ 2)⁻¹)).restrictScalars ℝ) (conj z) :=
    (hasDerivAt_inv hc0).hasFDerivAt.restrictScalars ℝ
  have hconj : HasFDerivAt (fun u : ℂ => conj u) Complex.conjCLE.toContinuousLinearMap z :=
    Complex.conjCLE.hasFDerivAt
  have hζd := hinv.comp z hconj
  have hf1 := ((hf.differentiableAt (hU.mem_nhds hζ)).hasFDerivAt.restrictScalars ℝ).comp z hζd
  have hf2 := (((hf.deriv hU).differentiableAt (hU.mem_nhds hζ)).hasFDerivAt.restrictScalars ℝ).comp z hζd
  have hsub := (hasFDerivAt_id (𝕜 := ℝ) z).sub hζd
  have h := hf1.add (hsub.mul hf2)
  refine h.congr_fderiv ?_
  ext1 v
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_restrictScalars',
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.one_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply, ContinuousLinearEquiv.coe_coe,
    Complex.conjCLE_apply, smul_eq_mul, Function.comp_apply]
  rw [(hf.differentiableAt (hU.mem_nhds hζ)).hasDerivAt.hasFDerivAt.fderiv,
    ((hf.deriv hU).differentiableAt (hU.mem_nhds hζ)).hasDerivAt.hasFDerivAt.fderiv]
  simp only [ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul, Pi.sub_apply, Function.comp_apply, id]
  field_simp
  ring

/-- The explicit extension off `𝔻̄` (BP78 (1.6)): `C¹`, `F_z = f'(1/z̄)`, `μ = -(z - 1/z̄) 𝒜f(1/z̄)/z̄²`. -/
theorem ab16x_ext_dilatation {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f unitDisc) (hinj : InjOn f unitDisc)
    {z : ℂ} (hz : 1 < ‖z‖) :
    ContDiffAt ℝ 1 (fun u : ℂ => f (conj u)⁻¹ + (u - (conj u)⁻¹) * deriv f (conj u)⁻¹) z ∧
      dz (fun u : ℂ => f (conj u)⁻¹ + (u - (conj u)⁻¹) * deriv f (conj u)⁻¹) z = deriv f (conj z)⁻¹ ∧
      complexDilatation (fun u : ℂ => f (conj u)⁻¹ + (u - (conj u)⁻¹) * deriv f (conj u)⁻¹) z =
        -(z - (conj z)⁻¹) * preSchwarzian f (conj z)⁻¹ / conj z ^ 2 := by
  have hU : IsOpen unitDisc := isOpen_ball
  have hz0 : z ≠ 0 := by intro h; rw [h, norm_zero] at hz; linarith
  have hc0 : conj z ≠ 0 := (map_ne_zero _).mpr hz0
  have hζ : (conj z)⁻¹ ∈ unitDisc := by
    apply mem_ball_zero_iff.mpr
    rw [norm_inv, Complex.norm_conj]
    exact inv_lt_one_of_one_lt₀ hz
  have hne : deriv f (conj z)⁻¹ ≠ 0 := deriv_ne_zero_of_injOn hU hf hinj hζ
  have hD := (ab16xe_hasFDerivAt hf hz).fderiv
  have hdz : dz (fun u : ℂ => f (conj u)⁻¹ + (u - (conj u)⁻¹) * deriv f (conj u)⁻¹) z = deriv f (conj z)⁻¹ := by
    unfold dz
    rw [hD]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.one_apply,
      ContinuousLinearEquiv.coe_coe, Complex.conjCLE_apply, smul_eq_mul, map_one, Complex.conj_I]
    ring_nf
    rw [Complex.I_sq]
    ring
  refine ⟨?_, hdz, ?_⟩
  · -- `C¹`
    have hζc : ContDiffAt ℝ 1 (fun u : ℂ => (conj u)⁻¹) z :=
      (contDiffAt_inv ℝ hc0).comp z Complex.conjCLE.contDiff.contDiffAt
    have hfc : ContDiffAt ℝ 1 f (conj z)⁻¹ :=
      ((hf.contDiffOn hU).contDiffAt (hU.mem_nhds hζ)).restrict_scalars ℝ
    have hgc : ContDiffAt ℝ 1 (deriv f) (conj z)⁻¹ :=
      (((hf.deriv hU).contDiffOn hU).contDiffAt (hU.mem_nhds hζ)).restrict_scalars ℝ
    exact (ContDiffAt.comp (g := f) z hfc hζc).add ((contDiffAt_id.sub hζc).mul (ContDiffAt.comp (g := deriv f) z hgc hζc))
  · unfold complexDilatation dzbar
    rw [hdz, hD]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.one_apply,
      ContinuousLinearEquiv.coe_coe, Complex.conjCLE_apply, smul_eq_mul, map_one, Complex.conj_I]
    unfold preSchwarzian
    field_simp
    ring_nf
    rw [Complex.I_sq]
    ring

/-- Off `𝔻̄` the glued map agrees with the explicit extension near `z`, so their dilatations agree. -/
theorem ab16xe_glue_dilatation {f fh : ℂ → ℂ} {z : ℂ} (hz : 1 < ‖z‖) :
    complexDilatation (fun z : ℂ => if ‖z‖ ≤ 1 then fh z else
        f (conj z)⁻¹ + (z - (conj z)⁻¹) * deriv f (conj z)⁻¹) z =
      complexDilatation (fun u : ℂ => f (conj u)⁻¹ + (u - (conj u)⁻¹) * deriv f (conj u)⁻¹) z := by
  have hev : (fun z : ℂ => if ‖z‖ ≤ 1 then fh z else
        f (conj z)⁻¹ + (z - (conj z)⁻¹) * deriv f (conj z)⁻¹) =ᶠ[𝓝 z]
      (fun u : ℂ => f (conj u)⁻¹ + (u - (conj u)⁻¹) * deriv f (conj u)⁻¹) := by
    filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds hz] with u hu
    have hu' : ¬ ‖u‖ ≤ 1 := not_le.mpr hu
    simp only [hu', if_false]
  unfold complexDilatation dzbar dz
  rw [hev.fderiv_eq]

theorem ab16xe_norm_sub {z : ℂ} (hz : 1 < ‖z‖) :
    ‖z - (conj z)⁻¹‖ = ‖z‖ * (1 - (‖z‖ ^ 2)⁻¹) := by
  have hn : (conj z)⁻¹ = z * (((‖z‖ ^ 2)⁻¹ : ℝ) : ℂ) := by
    rw [Complex.inv_def, Complex.conj_conj, Complex.normSq_conj, Complex.normSq_eq_norm_sq]
  have h1 : 0 ≤ 1 - (‖z‖ ^ 2)⁻¹ := by
    have : (‖z‖ ^ 2)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by nlinarith)
    linarith
  rw [hn, show z - z * (((‖z‖ ^ 2)⁻¹ : ℝ) : ℂ) = z * ((1 - (‖z‖ ^ 2)⁻¹ : ℝ) : ℂ) by push_cast; ring,
    norm_mul, Complex.norm_real, Real.norm_of_nonneg h1]

/-- (BP78 (1.6) ⇒ (5)) The dilatation of the glued map tends to `0` as `|z| → 1⁺`. -/
theorem ab16x_dilatation_tendsto {f fh : ℂ → ℂ} (hf : DifferentiableOn ℂ f unitDisc) (hinj : InjOn f unitDisc)
    (hA : Tendsto (fun z => ((1 - ‖z‖ ^ 2) : ℂ) * preSchwarzian f z)
      (comap (fun z : ℂ => ‖z‖) (𝓝[<] 1)) (𝓝 0)) :
    Tendsto (complexDilatation (fun z : ℂ => if ‖z‖ ≤ 1 then fh z else
        f (conj z)⁻¹ + (z - (conj z)⁻¹) * deriv f (conj z)⁻¹))
      (comap (fun z : ℂ => ‖z‖) (𝓝[>] 1)) (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨r, hr1, hr⟩ := (ab16_tendsto_iff.mp hA) ε hε
  set r' : ℝ := max r (1 / 2) with hr'
  have hr'1 : r' < 1 := max_lt hr1 (by norm_num)
  have hr'0 : 0 < r' := lt_of_lt_of_le (by norm_num) (le_max_right _ _)
  have hR : (1 : ℝ) < 1 / r' := by rw [lt_div_iff₀ hr'0]; linarith
  rw [Filter.eventually_comap]
  filter_upwards [Ioo_mem_nhdsGT hR] with s hs z hzs
  have hz : 1 < ‖z‖ := hzs ▸ hs.1
  have hzR : ‖z‖ < 1 / r' := hzs ▸ hs.2
  have hzpos : 0 < ‖z‖ := by linarith
  rw [ab16xe_glue_dilatation hz, (ab16x_ext_dilatation hf hinj hz).2.2, dist_zero_right]
  set ζ : ℂ := (conj z)⁻¹ with hζ
  have hζn : ‖ζ‖ = ‖z‖⁻¹ := by rw [hζ, norm_inv, Complex.norm_conj]
  have hζ1 : ‖ζ‖ < 1 := by rw [hζn]; exact inv_lt_one_of_one_lt₀ hz
  have hζr : r < ‖ζ‖ := by
    have : r' < ‖ζ‖ := by
      rw [hζn, lt_inv_comm₀ hr'0 hzpos, ← one_div]
      exact hzR
    exact lt_of_le_of_lt (le_max_left _ _) this
  have hb := hr ζ hζr hζ1
  have h1ζ : 0 ≤ 1 - ‖ζ‖ ^ 2 := by nlinarith [norm_nonneg ζ]
  have hnb : ‖((1 - ‖ζ‖ ^ 2 : ℝ) : ℂ) * preSchwarzian f ζ‖ = (1 - ‖ζ‖ ^ 2) * ‖preSchwarzian f ζ‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg h1ζ]
  have hb' : (1 - ‖ζ‖ ^ 2) * ‖preSchwarzian f ζ‖ < ε := by
    rw [← hnb]; push_cast; exact hb
  have hμ : ‖-(z - ζ) * preSchwarzian f ζ / conj z ^ 2‖ = (1 - ‖ζ‖ ^ 2) * ‖preSchwarzian f ζ‖ / ‖z‖ := by
    rw [norm_div, norm_mul, norm_neg, ab16xe_norm_sub hz, norm_pow, Complex.norm_conj, hζn]
    field_simp
  rw [hμ]
  calc (1 - ‖ζ‖ ^ 2) * ‖preSchwarzian f ζ‖ / ‖z‖ ≤ (1 - ‖ζ‖ ^ 2) * ‖preSchwarzian f ζ‖ := by
        apply div_le_self (by positivity) hz.le
    _ < ε := hb'

end Ch2
end TakhtajanTeo
