import TakhtajanTeo.Ch1.L55
import TakhtajanTeo.Ch1.TS2
import Mathlib.Analysis.Normed.Lp.lpHolder
import Mathlib.Analysis.InnerProductSpace.Calculus

/-! Coefficient Hilbert-space second variation for the corrected equations (5.3)–(5.4). -/
open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal ComplexConjugate Classical Real
noncomputable section
namespace TakhtajanTeo
open LiZhongQC

theorem s5cv_lp_norm_sq (a : lp (fun _ : ℕ => ℂ) 2) :
    ‖a‖ ^ 2 = ∑' n, ‖a n‖ ^ 2 := by
  simpa using lp.norm_rpow_eq_tsum (p := 2) (by norm_num) a

theorem s5cv_log_norm_second {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    {C : ℝ → E} {D : ℝ → F} (hC : ContDiff ℝ 2 C) (hD : ContDiff ℝ 2 D)
    (hC0 : C 0 = 0) (hD0 : D 0 = 0) :
    HasDerivAt (fun t => Real.log (1 + ‖C t‖ ^ 2 + ‖D t‖ ^ 2) / 2) 0 0 ∧
      deriv (deriv fun t => Real.log (1 + ‖C t‖ ^ 2 + ‖D t‖ ^ 2) / 2) 0 =
        ‖deriv C 0‖ ^ 2 + ‖deriv D 0‖ ^ 2 := by
  have hCd (t : ℝ) := (hC.differentiable (by norm_num) t).hasDerivAt
  have hDd (t : ℝ) := (hD.differentiable (by norm_num) t).hasDerivAt
  let e : ℝ → ℝ := fun t => 1 + ‖C t‖ ^ 2 + ‖D t‖ ^ 2
  let v : ℝ → ℝ := fun t =>
    2 * inner ℝ (C t) (deriv C t) + 2 * inner ℝ (D t) (deriv D t)
  have he (t : ℝ) : HasDerivAt e (v t) t := by
    convert! (((hCd t).norm_sq.const_add 1).add (hDd t).norm_sq) using 1
  have hepos (t : ℝ) : 0 < e t := by dsimp [e]; positivity
  have he0 : e 0 = 1 := by simp [e, hC0, hD0]
  have hv0 : v 0 = 0 := by simp [v, hC0, hD0]
  have hv : HasDerivAt v (2 * ‖deriv C 0‖ ^ 2 + 2 * ‖deriv D 0‖ ^ 2) 0 := by
    convert!
      (((hCd 0).inner ℝ (hC.differentiable_deriv_two 0).hasDerivAt).const_mul 2).add
        (((hDd 0).inner ℝ (hD.differentiable_deriv_two 0).hasDerivAt).const_mul 2) using 1
    simp [hC0, hD0]
  have hlog (t : ℝ) : HasDerivAt (fun t => Real.log (e t) / 2) (v t / e t / 2) t :=
    ((he t).log (hepos t).ne').div_const 2
  refine ⟨by simpa [e, he0, hv0] using hlog 0, ?_⟩
  have hd : (deriv fun t => Real.log (e t) / 2) = fun t => v t / e t / 2 :=
    funext fun t => (hlog t).deriv
  change deriv (deriv fun t => Real.log (e t) / 2) 0 = _
  rw [hd]
  have hh := ((hv.div (he 0) (hepos 0).ne').div_const 2).deriv
  simpa [he0, hv0, add_div, mul_div_cancel_left₀] using hh

theorem s5cv_energy {u : ℝ → ℝ} {F G : ℝ → ℂ → ℂ}
    (hc : IsWeldingCurve u F G) {A B : ℝ → lp (fun _ : ℕ => ℂ) 2}
    (hA : ∀ t, ∀ z ∈ unitDisc,
      HasSum (fun n : ℕ => A t n / (Real.sqrt ((n : ℝ) + 1) : ℂ) * z ^ (n + 1)) (F t z))
    (hB : ∀ t, ∀ z ∈ unitDiscExterior,
      HasSum (fun n : ℕ => B t n / (Real.sqrt ((n : ℝ) + 1) : ℂ) * z ^ (-(n : ℤ)))
        (G t z - derivAtInfty (G t) * z)) (t : ℝ) :
    ‖derivAtInfty (G t)‖ ^ 2 = ‖A t‖ ^ 2 +
      ∑' n : ℕ, (n : ℝ) / ((n : ℝ) + 1) * ‖B t n‖ ^ 2 := by
  let b : ℕ → ℂ := fun n => match n with
    | 0 => derivAtInfty (G t)
    | n + 1 => B t n / (Real.sqrt ((n : ℝ) + 1) : ℂ)
  have hb : ∀ z ∈ unitDiscExterior,
      HasSum (fun n : ℕ => b n * z ^ (1 - (n : ℤ))) (G t z) := by
    intro z hz
    apply (hasSum_nat_add_iff' 1).mp
    simpa [b, sub_sub, sub_add_cancel, add_sub_cancel_left] using hB t z hz
  obtain ⟨h, hh, hw⟩ := hc.1 t
  have he := lemma_5_5 hh hw (hA t) hb
  change ‖derivAtInfty (G t)‖ ^ 2 = _ at he
  rw [s5cv_lp_norm_sq]
  convert he using 1
  congr 1
  · apply tsum_congr
    intro n
    have hs : (Real.sqrt ((n : ℝ) + 1)) ^ 2 = (n : ℝ) + 1 := Real.sq_sqrt (by positivity)
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), div_pow, hs]
    push_cast
    field_simp
  · apply tsum_congr
    intro n
    dsimp [b]
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), div_pow,
      Real.sq_sqrt (by positivity : 0 ≤ (n : ℝ) + 1)]
    ring

theorem s5cv_eval_hasSum {z : ℂ} (hz : z ∈ unitDisc) :
    ∃ E : lp (fun _ : ℕ => ℂ) 2 →L[ℂ] ℂ, ∀ a,
      HasSum (fun n : ℕ => a n / (Real.sqrt ((n : ℝ) + 1) : ℂ) * z ^ n) (E a) := by
  let T : ℕ → lp (fun _ : ℕ => ℂ) 2 →L[ℂ] ℂ := fun n =>
    (z ^ n / (Real.sqrt ((n : ℝ) + 1) : ℂ)) • lp.evalCLM ℂ (fun _ : ℕ => ℂ) 2 n
  have hT : ∀ n, ‖T n‖ ≤ ‖z‖ ^ n := by
    intro n
    have hev : ‖lp.evalCLM ℂ (fun _ : ℕ => ℂ) 2 n‖ ≤ 1 := by
      apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
      intro a
      change ‖a n‖ ≤ 1 * ‖a‖
      simpa using lp.norm_apply_le_norm (by norm_num : (2 : ℝ≥0∞) ≠ 0) a n
    have hs : 1 ≤ Real.sqrt ((n : ℝ) + 1) := by
      simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt
        (show (1 : ℝ) ≤ (n : ℝ) + 1 from le_add_of_nonneg_left (Nat.cast_nonneg n))
    calc
      ‖T n‖ = ‖z‖ ^ n / Real.sqrt ((n : ℝ) + 1) *
          ‖lp.evalCLM ℂ (fun _ : ℕ => ℂ) 2 n‖ := by
        simp [T, norm_smul, norm_pow, abs_of_nonneg (Real.sqrt_nonneg _)]
      _ ≤ ‖z‖ ^ n := by
        calc
          _ ≤ ‖z‖ ^ n / Real.sqrt ((n : ℝ) + 1) * 1 :=
            mul_le_mul_of_nonneg_left hev (by positivity)
          _ ≤ ‖z‖ ^ n := by simpa using div_le_self (by positivity : 0 ≤ ‖z‖ ^ n) hs
  have hs : Summable T := .of_norm_bounded
    (summable_geometric_of_lt_one (norm_nonneg z) (mem_ball_zero_iff.mp hz)) hT
  refine ⟨∑' n, T n, fun a => ?_⟩
  convert hasSum_apply hs.hasSum a using 1
  ext n
  change a n / (Real.sqrt ((n : ℝ) + 1) : ℂ) * z ^ n =
    (z ^ n / (Real.sqrt ((n : ℝ) + 1) : ℂ)) * a n
  ring

theorem s5cv_series_unique_succ {f : ℂ → ℂ} {a b : ℕ → ℂ}
    (ha : ∀ z ∈ unitDisc, HasSum (fun n => a n * z ^ (n + 1)) (f z))
    (hb : ∀ z ∈ unitDisc, HasSum (fun n => b n * z ^ (n + 1)) (f z)) : a = b := by
  let a' : ℕ → ℂ := fun n => match n with | 0 => 0 | n + 1 => a n
  let b' : ℕ → ℂ := fun n => match n with | 0 => 0 | n + 1 => b n
  have ha' : ∀ z ∈ unitDisc, HasSum (fun n => a' n * z ^ n) (f z) := by
    intro z hz
    apply (hasSum_nat_add_iff' 1).mp
    simpa [a'] using ha z hz
  have hb' : ∀ z ∈ unitDisc, HasSum (fun n => b' n * z ^ n) (f z) := by
    intro z hz
    apply (hasSum_nat_add_iff' 1).mp
    simpa [b'] using hb z hz
  funext n
  exact ts2_series_coeff_unique ha' hb' (n + 1)

theorem s5cv_series_unique_nezero {f : ℂ → ℂ} {a b : ℕ → ℂ}
    (ha : ∀ z ∈ unitDisc, z ≠ 0 → HasSum (fun n => a n * z ^ n) (f z))
    (hb : ∀ z ∈ unitDisc, z ≠ 0 → HasSum (fun n => b n * z ^ n) (f z)) : a = b := by
  let fa : ℂ → ℂ := fun z => if z = 0 then a 0 else f z
  let fb : ℂ → ℂ := fun z => if z = 0 then b 0 else f z
  have ha' : ∀ z ∈ unitDisc, HasSum (fun n => a n * z ^ n) (fa z) := by
    intro z hz
    by_cases h : z = 0
    · subst z
      convert (hasSum_ite_eq (0 : ℕ) (a 0)) using 1
      · funext n; by_cases hn : n = 0 <;> simp [hn]
      · simp [fa]
    · simpa [fa, h] using ha z hz h
  have hb' : ∀ z ∈ unitDisc, HasSum (fun n => b n * z ^ n) (fb z) := by
    intro z hz
    by_cases h : z = 0
    · subst z
      convert (hasSum_ite_eq (0 : ℕ) (b 0)) using 1
      · funext n; by_cases hn : n = 0 <;> simp [hn]
      · simp [fb]
    · simpa [fb, h] using hb z hz h
  funext n
  have ea := ts2_circle_coeff_series ha' (r := 1 / 2) (by norm_num) (by norm_num) (n : ℤ)
  have eb := ts2_circle_coeff_series hb' (r := 1 / 2) (by norm_num) (by norm_num) (n : ℤ)
  have hi : (∫ θ in (0 : ℝ)..2 * π,
      fa (((1 / 2 : ℝ) : ℂ) * exp (θ * I)) * exp (-((n : ℂ) * θ * I))) =
      ∫ θ in (0 : ℝ)..2 * π,
      fb (((1 / 2 : ℝ) : ℂ) * exp (θ * I)) * exp (-((n : ℂ) * θ * I)) := by
    apply intervalIntegral.integral_congr
    intro θ _
    simp [fa, fb]
  simp only [Int.cast_natCast] at ea eb
  rw [ea, eb] at hi
  simp only [Int.natCast_nonneg, ite_true, Int.toNat_natCast] at hi
  exact mul_right_cancel₀ (pow_ne_zero n (by norm_num : ((1 / 2 : ℝ) : ℂ) ≠ 0))
    (mul_left_cancel₀ (by simp [Real.pi_ne_zero] : (2 * π : ℂ) ≠ 0) hi)

theorem s5cv_derivAtInfty_origin {u : ℝ → ℝ} {F G : ℝ → ℂ → ℂ}
    (hc : IsWeldingCurve u F G) : derivAtInfty (G 0) = 1 := by
  apply Tendsto.limUnder_eq
  apply tendsto_const_nhds.congr'
  filter_upwards [(isCompact_closedBall (0 : ℂ) 1).compl_mem_cocompact] with z hz
  have hz' : z ∈ unitDiscExterior := by simpa [unitDiscExterior] using hz
  have hne : z ≠ 0 := by intro h; norm_num [h, unitDiscExterior] at hz'
  simp [hc.2.2.1 z hz', hne]

theorem s5cv_first_coefficient {f : ℂ → ℂ} {a : ℕ → ℂ}
    (hd : DifferentiableOn ℂ f unitDisc) (h0 : f 0 = 0) (h1 : deriv f 0 = 1)
    (ha : ∀ z ∈ unitDisc, HasSum (fun n => a n * z ^ (n + 1)) (f z)) : a 0 = 1 := by
  have hb : ∀ z ∈ unitDisc, HasSum
      (fun n : ℕ => (Nat.factorial (n + 1) : ℂ)⁻¹ * iteratedDeriv (n + 1) f 0 * z ^ (n + 1)) (f z) := by
    intro z hz
    simpa [h0] using (hasSum_nat_add_iff' 1).mpr (ts2_taylor_hasSum hd hz)
  have he := congrFun (s5cv_series_unique_succ ha hb) 0
  simpa [h1] using he

theorem s5cv_initial_coefficients {u : ℝ → ℝ} {F G : ℝ → ℂ → ℂ}
    (hc : IsWeldingCurve u F G) {A B : ℝ → lp (fun _ : ℕ => ℂ) 2}
    (hA : ∀ t, ∀ z ∈ unitDisc,
      HasSum (fun n : ℕ => A t n / (Real.sqrt ((n : ℝ) + 1) : ℂ) * z ^ (n + 1)) (F t z))
    (hB : ∀ t, ∀ z ∈ unitDiscExterior,
      HasSum (fun n : ℕ => B t n / (Real.sqrt ((n : ℝ) + 1) : ℂ) * z ^ (-(n : ℤ)))
        (G t z - derivAtInfty (G t) * z)) :
    (∀ t, A t 0 = 1) ∧ A 0 = lp.single 2 0 1 ∧ B 0 = 0 := by
  have hnorm : ∀ t, A t 0 = 1 := by
    intro t
    obtain ⟨h, _, hw⟩ := hc.1 t
    simpa using s5cv_first_coefficient hw.2.1 hw.2.2.2.1 hw.2.2.2.2.1 (hA t)
  refine ⟨hnorm, ?_, ?_⟩
  · have hs : ∀ z ∈ unitDisc,
        HasSum (fun n : ℕ => (if n = 0 then (1 : ℂ) else 0) * z ^ (n + 1)) (F 0 z) := by
      intro z hz
      rw [hc.2.1 z hz]
      convert hasSum_ite_eq (0 : ℕ) z using 1
      funext n; by_cases hn : n = 0 <;> simp [hn]
    have he := s5cv_series_unique_succ (hA 0) hs
    ext n
    have hn := congrFun he n
    have hnz : (Real.sqrt ((n : ℝ) + 1) : ℂ) ≠ 0 := by
      exact_mod_cast (Real.sqrt_pos.2 (by positivity : 0 < (n : ℝ) + 1)).ne'
    by_cases h : n = 0
    · subst n; simpa using hnorm 0
    · simpa [h, lp.single_apply, div_eq_zero_iff, hnz] using hn
  · have hs : ∀ z ∈ unitDisc, z ≠ 0 → HasSum
        (fun n : ℕ => B 0 n / (Real.sqrt ((n : ℝ) + 1) : ℂ) * z ^ n) (0 : ℂ) := by
      intro z hz hn
      have hi : z⁻¹ ∈ unitDiscExterior := by
        change 1 < ‖z⁻¹‖
        rw [norm_inv, one_lt_inv₀ (norm_pos_iff.mpr hn)]
        exact mem_ball_zero_iff.mp hz
      simpa [hc.2.2.1 z⁻¹ hi, s5cv_derivAtInfty_origin hc, zpow_neg, zpow_natCast] using hB 0 z⁻¹ hi
    have he := s5cv_series_unique_nezero (b := fun _ => 0) hs (fun z _ _ => by simp)
    ext n
    have hn := congrFun he n
    have hnz : (Real.sqrt ((n : ℝ) + 1) : ℂ) ≠ 0 := by
      exact_mod_cast (Real.sqrt_pos.2 (by positivity : 0 < (n : ℝ) + 1)).ne'
    simpa [div_eq_zero_iff, hnz] using hn

theorem s5cv_velocity_series {u : ℝ → ℝ} {F G : ℝ → ℂ → ℂ}
    (hc : IsWeldingCurve u F G) {A B : ℝ → lp (fun _ : ℕ => ℂ) 2}
    (hAd : DifferentiableAt ℝ A 0) (hBd : DifferentiableAt ℝ B 0)
    (hA : ∀ t, ∀ z ∈ unitDisc,
      HasSum (fun n : ℕ => A t n / (Real.sqrt ((n : ℝ) + 1) : ℂ) * z ^ (n + 1)) (F t z))
    (hB : ∀ t, ∀ z ∈ unitDiscExterior,
      HasSum (fun n : ℕ => B t n / (Real.sqrt ((n : ℝ) + 1) : ℂ) * z ^ (-(n : ℤ)))
        (G t z - derivAtInfty (G t) * z)) :
    (∀ z ∈ unitDisc, HasSum
      (fun n : ℕ => deriv A 0 n / (Real.sqrt ((n : ℝ) + 1) : ℂ) * z ^ (n + 1)) (uPlus u z)) ∧
    ∀ z ∈ unitDisc, z ≠ 0 → HasSum
      (fun n : ℕ => deriv B 0 n / (Real.sqrt ((n : ℝ) + 1) : ℂ) * z ^ n) (-uMinus u z⁻¹) := by
  constructor
  · intro z hz
    obtain ⟨E, hE⟩ := s5cv_eval_hasSum hz
    have hi : (fun t => F t z) = fun t => E (A t) * z := by
      funext t
      exact (hA t z hz).unique (by simpa [pow_succ, mul_assoc] using (hE (A t)).mul_right z)
    have hd : HasDerivAt (fun t => F t z) (E (deriv A 0) * z) 0 := by
      rw [hi]
      exact ((E.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0 hAd.hasDerivAt).mul_const z
    have hv := hd.unique (hc.2.2.2.2.2.1 z hz)
    simpa [pow_succ, mul_assoc, hv] using (hE (deriv A 0)).mul_right z
  · intro z hz hn
    obtain ⟨E, hE⟩ := s5cv_eval_hasSum hz
    have hz' : z⁻¹ ∈ unitDiscExterior := by
      change 1 < ‖z⁻¹‖
      rw [norm_inv, one_lt_inv₀ (norm_pos_iff.mpr hn)]
      exact mem_ball_zero_iff.mp hz
    have hi : (fun t => G t z⁻¹ - derivAtInfty (G t) * z⁻¹) = fun t => E (B t) := by
      funext t
      exact (hB t z⁻¹ hz').unique (by simpa [zpow_neg, zpow_natCast] using hE (B t))
    have hd : HasDerivAt (fun t => G t z⁻¹ - derivAtInfty (G t) * z⁻¹) (E (deriv B 0)) 0 := by
      rw [hi]
      exact (E.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0 hBd.hasDerivAt
    have hv := hd.unique (hc.2.2.2.2.2.2 z⁻¹ hz')
    simpa [hv] using hE (deriv B 0)

theorem s5cv_norm_div_sqrt {x y : ℂ} {r : ℝ} (hr : 0 < r)
    (h : x / (Real.sqrt r : ℂ) = y) : ‖x‖ ^ 2 = r * ‖y‖ ^ 2 := by
  have hn : (Real.sqrt r : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr hr).ne'
  rw [div_eq_iff hn] at h
  rw [h, norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt hr.le]
  ring

theorem s5cv_velocity_energy {u : ℝ → ℝ} (hu : u ∈ tangentQS)
    {a b : lp (fun _ : ℕ => ℂ) 2}
    (ha : ∀ z ∈ unitDisc, HasSum
      (fun n : ℕ => a n / (Real.sqrt ((n : ℝ) + 1) : ℂ) * z ^ (n + 1)) (uPlus u z))
    (hb : ∀ z ∈ unitDisc, z ≠ 0 → HasSum
      (fun n : ℕ => b n / (Real.sqrt ((n : ℝ) + 1) : ℂ) * z ^ n) (-uMinus u z⁻¹)) :
    ‖a‖ ^ 2 + (∑' n : ℕ, (n : ℝ) / ((n : ℝ) + 1) * ‖b n‖ ^ 2) =
      2 * vkNormSqOrigin (fourierCoeff fun θ => (u θ : ℂ)) := by
  let c : ℤ → ℂ := fourierCoeff fun θ => (u θ : ℂ)
  have hplus : ∀ z ∈ unitDisc, HasSum
      (fun n : ℕ => (if n = 0 then (0 : ℂ) else I * c n) * z ^ (n + 1)) (uPlus u z) := by
    intro z hz
    have hh := (hasSum_nat_add_iff' 1).mpr ((ts2_uPlus_props hu).2 z hz)
    convert hh using 1
    · funext n
      by_cases hn : n = 0
      · simp [hn]
      · simp [show ¬ n + 1 < 2 by omega, hn, c]
    · simp
  have hea := s5cv_series_unique_succ ha hplus
  have ha0 : a 0 = 0 := by simpa using congrFun hea 0
  have han (n : ℕ) : ‖a (n + 1)‖ ^ 2 = ((n : ℝ) + 2) * ‖c (n + 1)‖ ^ 2 := by
    have hh := s5cv_norm_div_sqrt (by positivity : 0 < ((n + 1 : ℕ) : ℝ) + 1) (congrFun hea (n + 1))
    simpa [norm_mul, norm_I, c, add_assoc, one_add_one_eq_two] using hh
  have hcs : Summable (fun n : ℕ => ‖c (-(n + 1))‖) :=
    (tangentQS_fourier_summable hu).comp_injective (fun a b h => by omega)
  have hminus : ∀ z ∈ unitDisc, z ≠ 0 → HasSum
      (fun n : ℕ => (-I * c (-(n + 1))) * z ^ n) (-uMinus u z⁻¹) := by
    intro z hz _
    have hs : Summable (fun n : ℕ => c (-(n + 1)) * z ^ n) := by
      apply Summable.of_norm_bounded hcs
      intro n
      rw [norm_mul, norm_pow]
      exact mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) (mem_ball_zero_iff.mp hz).le)
    simpa [uMinus, zpow_neg, zpow_natCast, c, mul_assoc] using hs.hasSum.mul_left (-I)
  have heb := s5cv_series_unique_nezero hb hminus
  have hbn (n : ℕ) : (n : ℝ) / ((n : ℝ) + 1) * ‖b n‖ ^ 2 = (n : ℝ) * ‖c (n + 1)‖ ^ 2 := by
    have hh := s5cv_norm_div_sqrt (by positivity : 0 < (n : ℝ) + 1) (congrFun heb n)
    simp only [norm_mul, norm_neg, norm_I, one_mul, c, fourierCoeff_neg_real, norm_conj] at hh
    rw [hh]
    dsimp [c]
    field_simp
  have has : Summable (fun n : ℕ => ‖a n‖ ^ 2) := by
    simpa using (lp.memℓp a).summable (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
  have hbs : Summable (fun n : ℕ => (n : ℝ) * ‖c (n + 1)‖ ^ 2) := by
    apply Summable.of_nonneg_of_le (fun _ => by positivity) _ (vkNormSqOrigin_summable hu)
    intro n
    dsimp [c]
    gcongr
    norm_num
  rw [s5cv_lp_norm_sq, has.tsum_eq_zero_add, ha0, norm_zero, zero_pow (by norm_num : 2 ≠ 0), zero_add]
  simp_rw [han, hbn]
  rw [← Summable.tsum_add (has.comp_injective Nat.succ_injective |>.congr han) hbs,
    vkNormSqOrigin, ← tsum_mul_left]
  apply tsum_congr
  intro n
  dsimp [c]
  push_cast
  ring

theorem s5cv_weight_operator :
    ∃ T : lp (fun _ : ℕ => ℂ) 2 →L[ℝ] lp (fun _ : ℕ => ℂ) 2,
      ∀ a, ‖T a‖ ^ 2 = ∑' n : ℕ, (n : ℝ) / ((n : ℝ) + 1) * ‖a n‖ ^ 2 := by
  let W : ℕ → ℂ →L[ℝ] ℂ := fun n =>
    Real.sqrt ((n : ℝ) / ((n : ℝ) + 1)) • ContinuousLinearMap.id ℝ ℂ
  have hW : ∀ n, ‖W n‖ ≤ 1 := by
    intro n
    have hs : Real.sqrt ((n : ℝ) / ((n : ℝ) + 1)) ≤ 1 := by
      rw [Real.sqrt_le_one]
      exact div_le_one_of_le₀ (by linarith) (by positivity)
    simpa [W, norm_smul, abs_of_nonneg (Real.sqrt_nonneg _)] using hs
  let T := lp.mapCLM 2 W zero_le_one hW
  refine ⟨T, fun a => ?_⟩
  rw [s5cv_lp_norm_sq]
  apply tsum_congr
  intro n
  change ‖Real.sqrt ((n : ℝ) / ((n : ℝ) + 1)) • a n‖ ^ 2 = _
  rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, Real.sq_sqrt (by positivity)]

theorem s5cv_remove_first (a : lp (fun _ : ℕ => ℂ) 2) (ha : a 0 = 1) :
    ‖a‖ ^ 2 = 1 + ‖a - lp.single 2 0 (1 : ℂ)‖ ^ 2 := by
  have hh := norm_sub_sq_real a (lp.single 2 0 (1 : ℂ))
  rw [lp.inner_single_right, ha, real_inner_self_eq_norm_sq,
    lp.norm_single (by norm_num : (0 : ℝ≥0∞) < 2)] at hh
  norm_num at hh
  linarith

theorem s5cv_eq_5_3_5_4 {u : ℝ → ℝ} (hu : u ∈ tangentQS) {F G : ℝ → ℂ → ℂ} (hc : IsWeldingCurve u F G)
    (hreg : ∃ A B : ℝ → lp (fun _ : ℕ => ℂ) 2, ContDiff ℝ 2 A ∧ ContDiff ℝ 2 B ∧
      (∀ t, ∀ z ∈ unitDisc,
        HasSum (fun n : ℕ => A t n / (Real.sqrt ((n : ℝ) + 1) : ℂ) * z ^ (n + 1)) (F t z)) ∧
      ∀ t, ∀ z ∈ unitDiscExterior,
        HasSum (fun n : ℕ => B t n / (Real.sqrt ((n : ℝ) + 1) : ℂ) * z ^ (-(n : ℤ)))
          (G t z - derivAtInfty (G t) * z)) :
    HasDerivAt (fun t => Real.log ‖derivAtInfty (G t)‖) 0 0 ∧
      deriv (deriv fun t => Real.log ‖derivAtInfty (G t)‖) 0 =
        2 * vkNormSqOrigin (fourierCoeff fun θ => (u θ : ℂ)) := by
  obtain ⟨A, B, hAd, hBd, hA, hB⟩ := hreg
  obtain ⟨hA0, hAz, hBz⟩ := s5cv_initial_coefficients hc hA hB
  obtain ⟨T, hT⟩ := s5cv_weight_operator
  let C : ℝ → lp (fun _ : ℕ => ℂ) 2 := fun t => A t - lp.single 2 0 1
  let D : ℝ → lp (fun _ : ℕ => ℂ) 2 := fun t => T (B t)
  have hC : ContDiff ℝ 2 C := hAd.sub contDiff_const
  have hD : ContDiff ℝ 2 D := T.contDiff.comp hBd
  have hC0 : C 0 = 0 := by simp [C, hAz]
  have hD0 : D 0 = 0 := by simp [D, hBz]
  have he (t : ℝ) : ‖derivAtInfty (G t)‖ ^ 2 = 1 + ‖C t‖ ^ 2 + ‖D t‖ ^ 2 := by
    rw [s5cv_energy hc hA hB, s5cv_remove_first (A t) (hA0 t), ← hT]
  have hl : (fun t => Real.log ‖derivAtInfty (G t)‖) =
      fun t => Real.log (1 + ‖C t‖ ^ 2 + ‖D t‖ ^ 2) / 2 := by
    funext t
    rw [← he t, Real.log_pow]
    ring
  rw [hl]
  obtain ⟨hfirst, hsecond⟩ := s5cv_log_norm_second hC hD hC0 hD0
  refine ⟨hfirst, hsecond.trans ?_⟩
  have hda : DifferentiableAt ℝ A 0 := hAd.differentiable (by norm_num) 0
  have hdb : DifferentiableAt ℝ B 0 := hBd.differentiable (by norm_num) 0
  have hdc : deriv C 0 = deriv A 0 := (hda.hasDerivAt.sub_const _).deriv
  have hdd : deriv D 0 = T (deriv B 0) := (T.hasFDerivAt.comp_hasDerivAt 0 hdb.hasDerivAt).deriv
  rw [hdc, hdd, hT]
  obtain ⟨hva, hvb⟩ := s5cv_velocity_series hc hda hdb hA hB
  exact s5cv_velocity_energy hu hva hvb

/-- **(5.3)** and the second variation (TT:2354–2390).
- Along a smooth welding curve tangent to `u ∈ T₀^ℝ 𝒯(1)`, `ḃ₀ + \overline{ḃ₀} = 0`, where `b₀(t) = g_t'(∞)`.
- Therefore `d/dt log|g_t'(∞)| = 0` at `t = 0`.
- `d²/dt² log|g_t'(∞)| |_{t=0} = 2 Σ_{n ≥ 1} n |ȧ_n|² = 2 Σ_{n ≥ 1} n |c_n|²` (since `ȧ_n = i c_n` by TS1).
- With (1.16) this gives (5.4): `(∂∂̄K)(v, v̄) = Σ_{n ≥ 1} n |c_n|² = ‖v‖²_VK` at the origin.
- **[CORRECTION 2026-10-28, user-approved]** The curve is smooth in the Hilbert manifold, as TT's termwise
  differentiation of (5.2) needs (`hreg`): the coefficients `√(n+1) a_n(t)` of `f^t` and `√(n+1) b_{n+1}(t)` of
  `g_t - g_t'(∞) z` are `C²` curves in `ℓ²`. With `C²` only on the open sets `ℝ × 𝔻`, `ℝ × 𝔻*` (`IsWeldingCurve`),
  high-frequency boundary wiggles are invisible on compacts. Sketch with `u = 0`:
  `f^t = z + Σ_k ψ_k(t) (t/√N_k) z^{N_k}` with `Σ ψ_k² = 1`, `ψ_k` supported at `t ≍ 2^{-k}`, `N_k ≍ 4^k/k²`.
  Then (5.2) gives `|b₀(t)|² ≥ 1 + t²`, so the second derivative is `≥ 1`, not `0`. The first clause needs no `hreg`. -/
theorem eq_5_3_5_4 {u : ℝ → ℝ} (hu : u ∈ tangentQS) {F G : ℝ → ℂ → ℂ} (hc : IsWeldingCurve u F G)
    (hreg : ∃ A B : ℝ → lp (fun _ : ℕ => ℂ) 2, ContDiff ℝ 2 A ∧ ContDiff ℝ 2 B ∧
      (∀ t, ∀ z ∈ unitDisc,
        HasSum (fun n : ℕ => A t n / (Real.sqrt ((n : ℝ) + 1) : ℂ) * z ^ (n + 1)) (F t z)) ∧
      ∀ t, ∀ z ∈ unitDiscExterior,
        HasSum (fun n : ℕ => B t n / (Real.sqrt ((n : ℝ) + 1) : ℂ) * z ^ (-(n : ℤ)))
          (G t z - derivAtInfty (G t) * z)) :
    HasDerivAt (fun t => Real.log ‖derivAtInfty (G t)‖) 0 0 ∧
      deriv (deriv fun t => Real.log ‖derivAtInfty (G t)‖) 0 =
        2 * vkNormSqOrigin (fourierCoeff fun θ => (u θ : ℂ)) := s5cv_eq_5_3_5_4 hu hc hreg

end TakhtajanTeo
