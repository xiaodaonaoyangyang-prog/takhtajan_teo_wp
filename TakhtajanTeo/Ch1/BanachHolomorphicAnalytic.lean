import TakhtajanTeo.Ch1.BanachHolomorphic
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Complex.TaylorSeries

/-! # Cauchy estimates towards Banach-domain holomorphy implies analyticity

The estimates are proved for arbitrary complex normed codomains. The final
power-series theorem is constructed downstream in this module; the intermediate
estimates alone are not an assertion of Banach-domain analyticity.
-/
open Complex Set Metric Filter Topology MeasureTheory
open scoped NNReal ENNReal Real Topology
noncomputable section
namespace TakhtajanTeo

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

-- H1
theorem bha_fderiv_bound {f : E → F} {a x : E} {r R M : ℝ} (hR : 0 < R)
    (hf : DifferentiableOn ℂ f (ball a (r + R)))
    (hb : ∀ y ∈ ball a (r + R), ‖f y‖ ≤ M) (hx : x ∈ ball a r) :
    ‖fderiv ℂ f x‖ ≤ M / R := by
  have hx' : x ∈ ball a (r + R) := ball_subset_ball (by linarith) hx
  have hM : 0 ≤ M := (norm_nonneg _).trans (hb x hx')
  apply ContinuousLinearMap.opNorm_le_bound _ (div_nonneg hM hR.le)
  intro v
  by_cases hv : v = 0
  · simp [hv]
  have hv0 : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have hp : ∀ ζ : ℂ, ‖ζ‖ ≤ R / ‖v‖ → x + ζ • v ∈ ball a (r + R) := by
    intro ζ hζ
    have hs : ‖ζ • v‖ ≤ R := by
      rw [norm_smul]
      exact (mul_le_mul_of_nonneg_right hζ hv0.le).trans_eq (div_mul_cancel₀ _ hv0.ne')
    have hx0 : ‖x - a‖ < r := by simpa only [mem_ball, dist_eq_norm] using hx
    rw [mem_ball, dist_eq_norm, show x + ζ • v - a = (x - a) + ζ • v by abel]
    exact (norm_add_le _ _).trans_lt (by linarith)
  have h := bh_line_deriv_le (div_pos hR hv0)
    (fun ζ hζ => hf.differentiableAt (isOpen_ball.mem_nhds (hp ζ (by simpa using hζ))))
    (fun ζ hζ => hb _ (hp ζ (by simpa using hζ.le)))
  apply h.trans_eq
  field_simp

-- H2
theorem bha_lipschitz_bound {f : E → F} {a x y : E} {r R M : ℝ} (hR : 0 < R)
    (hf : DifferentiableOn ℂ f (ball a (r + R)))
    (hb : ∀ z ∈ ball a (r + R), ‖f z‖ ≤ M)
    (hx : x ∈ ball a r) (hy : y ∈ ball a r) :
    ‖f y - f x‖ ≤ M / R * ‖y - x‖ := by
  exact Convex.norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℂ)
    (fun z hz => hf.differentiableAt (isOpen_ball.mem_nhds
      (ball_subset_ball (by linarith) hz)))
    (fun z hz => bha_fderiv_bound hR hf hb hz) (convex_ball a r) hx hy

-- H3
theorem bha_fderiv_lipschitz {f : E → F} {a x y : E} {R M : ℝ} (hR : 0 < R)
    (hf : DifferentiableOn ℂ f (ball a (4 * R)))
    (hb : ∀ z ∈ ball a (4 * R), ‖f z‖ ≤ M)
    (hx : x ∈ ball a R) (hy : y ∈ ball a R) :
    ‖fderiv ℂ f y - fderiv ℂ f x‖ ≤ M / R ^ 2 * ‖y - x‖ := by
  have hM : 0 ≤ M := (norm_nonneg _).trans (hb a (mem_ball_self (by positivity)))
  have hd : ∀ z ∈ ball a (4 * R), DifferentiableAt ℂ f z :=
    fun z hz => hf.differentiableAt (isOpen_ball.mem_nhds hz)
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro v
  by_cases hv : v = 0
  · simp [hv]
  have hv0 : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have hs : ∀ ζ : ℂ, ‖ζ‖ ≤ R / ‖v‖ → ‖ζ • v‖ ≤ R := by
    intro ζ hζ
    rw [norm_smul]
    exact (mul_le_mul_of_nonneg_right hζ hv0.le).trans_eq (div_mul_cancel₀ _ hv0.ne')
  have hm : ∀ b ∈ ball a R, ∀ ζ : ℂ, ‖ζ‖ ≤ R / ‖v‖ → b + ζ • v ∈ ball a (2 * R) := by
    intro b hb' ζ hζ
    have hb0 : ‖b - a‖ < R := by simpa only [mem_ball, dist_eq_norm] using hb'
    rw [mem_ball, dist_eq_norm, show b + ζ • v - a = (b - a) + ζ • v by abel]
    exact (norm_add_le _ _).trans_lt (by linarith [hs ζ hζ])
  let φ : E → F := fun w => f (w + (y - x)) - f w
  have he (ζ : ℂ) : x + ζ • v + (y - x) = y + ζ • v := by abel
  have hφd : ∀ ζ ∈ closedBall (0 : ℂ) (R / ‖v‖), DifferentiableAt ℂ φ (x + ζ • v) := by
    intro ζ hζ
    have hζ0 : ‖ζ‖ ≤ R / ‖v‖ := by simpa using hζ
    have hxζ := hd _ (ball_subset_ball (by linarith) (hm x hx ζ hζ0))
    have hyζ := hd _ (ball_subset_ball (by linarith) (hm y hy ζ hζ0))
    have hd' : DifferentiableAt ℂ f (x + ζ • v + (y - x)) := by rw [he]; exact hyζ
    exact (hd'.comp (x + ζ • v) (differentiableAt_id.add_const (y - x))).sub hxζ
  have hφb : ∀ ζ ∈ sphere (0 : ℂ) (R / ‖v‖), ‖φ (x + ζ • v)‖ ≤ M / R * ‖y - x‖ := by
    intro ζ hζ
    have hζ0 : ‖ζ‖ ≤ R / ‖v‖ := by simpa using hζ.le
    have hh := bha_lipschitz_bound (r := 2 * R) hR
      (hf.mono (ball_subset_ball (by linarith)))
      (fun z hz => hb z (ball_subset_ball (by linarith) hz))
      (hm x hx ζ hζ0) (hm y hy ζ hζ0)
    simpa only [φ, he, add_sub_add_right_eq_sub] using hh
  have hxD := hd x (ball_subset_ball (by linarith) hx)
  have hyD := hd y (ball_subset_ball (by linarith) hy)
  have hfd : fderiv ℂ φ x = fderiv ℂ f y - fderiv ℂ f x := by
    have h1 : DifferentiableAt ℂ (fun w => f (w + (y - x))) x :=
      (show DifferentiableAt ℂ f (x + (y - x)) by simpa using hyD).comp x
        (differentiableAt_id.add_const _)
    simp only [φ]
    rw [fderiv_fun_sub h1 hxD, fderiv_comp_add_right]
    simp
  have hc := bh_line_deriv_le (div_pos hR hv0) hφd hφb
  rw [hfd] at hc
  apply hc.trans_eq
  field_simp

-- H4
theorem bha_continuousOn_fderiv {f : E → F} {U : Set E}
    (hU : IsOpen U) (hf : DifferentiableOn ℂ f U) :
    ContinuousOn (fderiv ℂ f) U := by
  intro x hx
  apply ContinuousAt.continuousWithinAt
  obtain ⟨r0, hr0, hsub⟩ := Metric.isOpen_iff.mp hU x hx
  have hc : ContinuousAt f x := (hf.differentiableAt (hU.mem_nhds hx)).continuousAt
  obtain ⟨r1, hr1, hbound⟩ := Metric.eventually_nhds_iff_ball.mp
    (hc.norm.eventually (gt_mem_nhds (by linarith : ‖f x‖ < ‖f x‖ + 1)))
  let R := min r0 r1 / 4
  have hR : 0 < R := by dsimp [R]; positivity
  have hR0 : 4 * R ≤ r0 := by dsimp [R]; linarith [min_le_left r0 r1]
  have hR1 : 4 * R ≤ r1 := by dsimp [R]; linarith [min_le_right r0 r1]
  have hd := hf.mono ((ball_subset_ball hR0).trans hsub)
  have hb : ∀ z ∈ ball x (4 * R), ‖f z‖ ≤ ‖f x‖ + 1 :=
    fun z hz => (hbound z (ball_subset_ball hR1 hz)).le
  let K := (‖f x‖ + 1) / R ^ 2
  have hK : 0 ≤ K := by dsimp [K]; positivity
  rw [Metric.continuousAt_iff]
  intro ε hε
  refine ⟨min R (ε / (K + 1)), lt_min hR (by positivity), fun y hy => ?_⟩
  have hyR : y ∈ ball x R := lt_of_lt_of_le hy (min_le_left _ _)
  have hye : ‖y - x‖ < ε / (K + 1) := by
    simpa only [dist_eq_norm] using lt_of_lt_of_le hy (min_le_right _ _)
  have hh := bha_fderiv_lipschitz hR hd hb (mem_ball_self hR) hyR
  rw [dist_eq_norm]
  calc ‖fderiv ℂ f y - fderiv ℂ f x‖ ≤ K * ‖y - x‖ := hh
    _ ≤ (K + 1) * ‖y - x‖ := by nlinarith [norm_nonneg (y - x)]
    _ < ε := by
      rw [lt_div_iff₀ (by positivity)] at hye
      linarith

-- H5a
theorem bha_directional_differentiableAt [CompleteSpace F]
    {f : E → F} {a : E} {R M : ℝ} (hR : 0 < R)
    (hf : DifferentiableOn ℂ f (ball a (4 * R)))
    (hb : ∀ z ∈ ball a (4 * R), ‖f z‖ ≤ M) (v : E) :
    DifferentiableAt ℂ (fun x => fderiv ℂ f x v) a := by
  by_cases hv : v = 0
  · simp only [hv, map_zero]
    exact differentiableAt_const _
  have hv0 : 0 < ‖v‖ := norm_pos_iff.mpr hv
  let τ : ℝ := R / ‖v‖
  have hτ : 0 < τ := div_pos hR hv0
  let q : ℝ → ℂ := circleMap 0 τ
  let c : ℝ → ℂ := fun θ => (q θ * I) / (q θ) ^ 2
  have hqn : ∀ θ, ‖q θ‖ = τ := fun θ => by
    simp only [q, norm_circleMap_zero, abs_of_pos hτ]
  have hq0 : ∀ θ, q θ ≠ 0 := fun θ => norm_ne_zero_iff.mp (by rw [hqn]; exact hτ.ne')
  have hqc : Continuous q := continuous_circleMap 0 τ
  have hcc : Continuous c := (hqc.mul continuous_const).div (hqc.pow 2)
    (fun θ => pow_ne_zero 2 (hq0 θ))
  have hcn : ∀ θ, ‖c θ‖ = τ⁻¹ := by
    intro θ
    simp only [c, norm_div, norm_mul, norm_I, mul_one, norm_pow, hqn]
    field_simp
  have hpt : ∀ y ∈ ball a R, ∀ ζ : ℂ, ‖ζ‖ ≤ τ → y + ζ • v ∈ ball a (2 * R) := by
    intro y hy ζ hζ
    have hy0 : ‖y - a‖ < R := by simpa only [mem_ball, dist_eq_norm] using hy
    have hs : ‖ζ • v‖ ≤ R := by
      rw [norm_smul]
      exact (mul_le_mul_of_nonneg_right hζ hv0.le).trans_eq (div_mul_cancel₀ _ hv0.ne')
    rw [mem_ball, dist_eq_norm, show y + ζ • v - a = (y - a) + ζ • v by abel]
    exact (norm_add_le _ _).trans_lt (by linarith)
  have hptq : ∀ y ∈ ball a R, ∀ θ, y + q θ • v ∈ ball a (4 * R) :=
    fun y hy θ => ball_subset_ball (by linarith) (hpt y hy (q θ) (hqn θ).le)
  let G : E → ℝ → F := fun y θ => c θ • f (y + q θ • v)
  let D : E → ℝ → E →L[ℂ] F := fun y θ => c θ • fderiv ℂ f (y + q θ • v)
  let σ : Measure ℝ := volume.restrict (Ioc 0 (2 * Real.pi))
  let J : E → F := fun y => ∫ θ, G y θ ∂σ
  have hGc : ∀ y ∈ ball a R, Continuous (G y) := by
    intro y hy
    exact hcc.smul (hf.continuousOn.comp_continuous
      (continuous_const.add (hqc.smul continuous_const)) (hptq y hy))
  have hDc : ∀ y ∈ ball a R, Continuous (D y) := by
    intro y hy
    exact hcc.smul ((bha_continuousOn_fderiv isOpen_ball hf).comp_continuous
      (continuous_const.add (hqc.smul continuous_const)) (hptq y hy))
  have ha : a ∈ ball a R := mem_ball_self hR
  have hInt : DifferentiableAt ℂ J a := by
    apply HasFDerivAt.differentiableAt
    apply hasFDerivAt_integral_of_dominated_of_fderiv_le
      (F' := D) (bound := fun _ => τ⁻¹ * (M / R)) (ball_mem_nhds a hR)
    · filter_upwards [ball_mem_nhds a hR] with y hy
      exact (hGc y hy).aestronglyMeasurable
    · change IntegrableOn (G a) (Ioc 0 (2 * Real.pi))
      exact (hGc a ha).integrableOn_Icc.mono_set Ioc_subset_Icc_self
    · exact (hDc a ha).aestronglyMeasurable
    · filter_upwards with θ y hy
      change ‖c θ • fderiv ℂ f (y + q θ • v)‖ ≤ _
      rw [norm_smul, hcn]
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hτ.le)
      exact bha_fderiv_bound (r := 2 * R) hR
        (hf.mono (ball_subset_ball (by linarith)))
        (fun z hz => hb z (ball_subset_ball (by linarith) hz))
        (hpt y hy (q θ) (hqn θ).le)
    · exact integrable_const _
    · filter_upwards with θ y hy
      have h := (hf.differentiableAt (isOpen_ball.mem_nhds (hptq y hy θ))).hasFDerivAt
      simpa only [G, D, Function.comp_def, Pi.smul_def, id_eq, ContinuousLinearMap.comp_id] using
        (h.comp y ((hasFDerivAt_id y).add_const (q θ • v))).const_smul (c θ)
  have he : ∀ y ∈ ball a R, (2 * Real.pi * I : ℂ)⁻¹ • J y = fderiv ℂ f y v := by
    intro y hy
    let g : ℂ → F := fun ζ => f (y + ζ • v)
    have hg : ∀ ζ ∈ closedBall (0 : ℂ) τ,
        HasDerivAt g (fderiv ℂ f (y + ζ • v) v) ζ := by
      intro ζ hζ
      apply (hf.differentiableAt (isOpen_ball.mem_nhds
        (ball_subset_ball (by linarith) (hpt y hy ζ (by simpa using hζ))))).hasFDerivAt.comp_hasDerivAt
      simpa using ((hasDerivAt_id ζ).smul_const v).const_add y
    have hdg : DifferentiableOn ℂ g (closedBall 0 τ) :=
      fun ζ hζ => (hg ζ hζ).differentiableAt.differentiableWithinAt
    have h0 : deriv g 0 = fderiv ℂ f y v := by
      simpa only [zero_smul, add_zero] using (hg 0 (mem_closedBall_self hτ.le)).deriv
    have hc := hdg.deriv_eq_smul_circleIntegral hτ
    rw [h0] at hc
    have hJ : J y = ∮ ζ in C(0, τ), (1 / (ζ - 0) ^ 2) • g ζ := by
      simp only [J, G, σ, c, q, g, circleIntegral, deriv_circleMap, sub_zero,
        intervalIntegral.integral_of_le (by positivity : (0 : ℝ) ≤ 2 * Real.pi),
        div_eq_mul_inv, one_mul, smul_smul]
    rw [hJ, hc, smul_smul, inv_mul_cancel₀ (by
      exact mul_ne_zero (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) I_ne_zero),
      one_smul]
  exact (hInt.const_smul (2 * Real.pi * I : ℂ)⁻¹).congr_of_eventuallyEq
    (Filter.eventuallyEq_of_mem (ball_mem_nhds a hR) fun y hy => (he y hy).symm)

-- H5b
theorem bha_directional_differentiableOn [CompleteSpace F]
    {f : E → F} {U : Set E} (hU : IsOpen U) (hf : DifferentiableOn ℂ f U) (v : E) :
    DifferentiableOn ℂ (fun x => fderiv ℂ f x v) U := by
  intro x hx
  obtain ⟨r0, hr0, hsub⟩ := Metric.isOpen_iff.mp hU x hx
  have hc : ContinuousAt f x := (hf.differentiableAt (hU.mem_nhds hx)).continuousAt
  obtain ⟨r1, hr1, hbound⟩ := Metric.eventually_nhds_iff_ball.mp
    (hc.norm.eventually (gt_mem_nhds (by linarith : ‖f x‖ < ‖f x‖ + 1)))
  let R := min r0 r1 / 4
  have hR : 0 < R := by dsimp [R]; positivity
  have hR0 : 4 * R ≤ r0 := by dsimp [R]; linarith [min_le_left r0 r1]
  have hR1 : 4 * R ≤ r1 := by dsimp [R]; linarith [min_le_right r0 r1]
  exact (bha_directional_differentiableAt hR
    (hf.mono ((ball_subset_ball hR0).trans hsub))
    (fun z hz => (hbound z (ball_subset_ball hR1 hz)).le) v).differentiableWithinAt

/-- Iterated directional derivatives. Holomorphy of every intermediate
function is proved below before these values are used as Taylor coefficients. -/
def bha_iterated (f : E → F) : (n : ℕ) → (Fin n → E) → E → F
  | 0, _, x => f x
  | n + 1, v, x => fderiv ℂ (bha_iterated f n (Fin.tail v)) x (v 0)

-- H6a
theorem bha_iterated_holomorphic [CompleteSpace F] {f : E → F} {U : Set E}
    (hU : IsOpen U) (hf : DifferentiableOn ℂ f U) (n : ℕ) (v : Fin n → E) :
    DifferentiableOn ℂ (bha_iterated f n v) U := by
  induction n with
  | zero => exact hf
  | succ n ih => exact bha_directional_differentiableOn hU (ih (Fin.tail v)) (v 0)

-- H6b
theorem bha_iterated_update_add [CompleteSpace F] {f : E → F} {U : Set E}
    (hU : IsOpen U) (hf : DifferentiableOn ℂ f U) (n : ℕ) :
    ∀ a ∈ U, ∀ (v : Fin n → E) (i : Fin n) (b c : E),
      bha_iterated f n (Function.update v i (b + c)) a =
        bha_iterated f n (Function.update v i b) a + bha_iterated f n (Function.update v i c) a := by
  induction n with
  | zero => intro a ha v i; exact Fin.elim0 i
  | succ n ih =>
    intro a ha v i b c
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [bha_iterated, Fin.tail_update_zero, Function.update_self, map_add]
    · simp only [bha_iterated, Fin.tail_update_succ,
        Function.update_of_ne (Ne.symm (Fin.succ_ne_zero j))]
      have he : bha_iterated f n (Function.update (Fin.tail v) j (b + c)) =ᶠ[𝓝 a]
          (fun x => bha_iterated f n (Function.update (Fin.tail v) j b) x +
            bha_iterated f n (Function.update (Fin.tail v) j c) x) :=
        Filter.eventuallyEq_of_mem (hU.mem_nhds ha) fun x hx => ih x hx _ j b c
      rw [he.fderiv_eq, fderiv_fun_add
        ((bha_iterated_holomorphic hU hf n _).differentiableAt (hU.mem_nhds ha))
        ((bha_iterated_holomorphic hU hf n _).differentiableAt (hU.mem_nhds ha))]
      rfl

-- H6c
theorem bha_iterated_update_smul [CompleteSpace F] {f : E → F} {U : Set E}
    (hU : IsOpen U) (hf : DifferentiableOn ℂ f U) (n : ℕ) :
    ∀ a ∈ U, ∀ (v : Fin n → E) (i : Fin n) (c : ℂ) (b : E),
      bha_iterated f n (Function.update v i (c • b)) a =
        c • bha_iterated f n (Function.update v i b) a := by
  induction n with
  | zero => intro a ha v i; exact Fin.elim0 i
  | succ n ih =>
    intro a ha v i c b
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [bha_iterated, Fin.tail_update_zero, Function.update_self, map_smul]
    · simp only [bha_iterated, Fin.tail_update_succ,
        Function.update_of_ne (Ne.symm (Fin.succ_ne_zero j))]
      have he : bha_iterated f n (Function.update (Fin.tail v) j (c • b)) =ᶠ[𝓝 a]
          (c • bha_iterated f n (Function.update (Fin.tail v) j b)) :=
        Filter.eventuallyEq_of_mem (hU.mem_nhds ha) fun x hx => ih x hx _ j c b
      rw [he.fderiv_eq, fderiv_const_smul
        ((bha_iterated_holomorphic hU hf n _).differentiableAt (hU.mem_nhds ha))]
      rfl

-- H6d
theorem bha_iterated_bound [CompleteSpace F] {f : E → F} (n : ℕ) :
    ∀ {a x : E} {r δ M : ℝ}, 0 < δ →
      DifferentiableOn ℂ f (ball a (r + n * δ)) →
      (∀ z ∈ ball a (r + n * δ), ‖f z‖ ≤ M) → x ∈ ball a r →
      ∀ v : Fin n → E, ‖bha_iterated f n v x‖ ≤ M / δ ^ n * ∏ i, ‖v i‖ := by
  induction n with
  | zero =>
    intro a x r δ M hδ hf hb hx v
    simpa [bha_iterated] using hb x (by simpa using hx)
  | succ n ih =>
    intro a x r δ M hδ hf hb hx v
    have he : r + (↑(n + 1) : ℝ) * δ = (r + δ) + n * δ := by push_cast; ring
    have hg : DifferentiableOn ℂ (bha_iterated f n (Fin.tail v)) (ball a (r + δ)) :=
      (bha_iterated_holomorphic isOpen_ball hf n _).mono (ball_subset_ball (by
        have hn : (0 : ℝ) ≤ n := by positivity
        rw [he]
        nlinarith))
    have hgb : ∀ z ∈ ball a (r + δ), ‖bha_iterated f n (Fin.tail v) z‖ ≤
        M / δ ^ n * ∏ i, ‖Fin.tail v i‖ := by
      intro z hz
      apply ih hδ
      · rwa [he] at hf
      · rwa [he] at hb
      · exact hz
    have hD := bha_fderiv_bound hδ hg hgb hx
    calc ‖bha_iterated f (n + 1) v x‖
        ≤ ‖fderiv ℂ (bha_iterated f n (Fin.tail v)) x‖ * ‖v 0‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ ≤ ((M / δ ^ n * ∏ i, ‖Fin.tail v i‖) / δ) * ‖v 0‖ :=
        mul_le_mul_of_nonneg_right hD (norm_nonneg _)
      _ = M / δ ^ (n + 1) * ∏ i, ‖v i‖ := by
        rw [Fin.prod_univ_succ, pow_succ]
        simp only [Fin.tail]
        field_simp

/-- The algebraic multilinear map of actual iterated directional derivatives. -/
def bha_multilinear [CompleteSpace F] {f : E → F} {U : Set E}
    (hU : IsOpen U) (hf : DifferentiableOn ℂ f U) {a : E} (ha : a ∈ U) (n : ℕ) :
    MultilinearMap ℂ (fun _ : Fin n => E) F where
  toFun := fun v => bha_iterated f n v a
  map_update_add' := by
    intro inst v i b c
    have hi : inst = instDecidableEqFin n := Subsingleton.elim _ _
    subst inst
    exact bha_iterated_update_add hU hf n a ha v i b c
  map_update_smul' := by
    intro inst v i c b
    have hi : inst = instDecidableEqFin n := Subsingleton.elim _ _
    subst inst
    exact bha_iterated_update_smul hU hf n a ha v i c b

-- H7a
theorem bha_coefficients [CompleteSpace F] {f : E → F} {a : E} {R M : ℝ} (hR : 0 < R)
    (hf : DifferentiableOn ℂ f (ball a R)) (hb : ∀ z ∈ ball a R, ‖f z‖ ≤ M) :
    ∃ p : FormalMultilinearSeries ℂ E F,
      (∀ n v, p n v = (n.factorial : ℂ)⁻¹ • bha_iterated f n v a) ∧
        ENNReal.ofReal (R / Real.exp 1) ≤ p.radius := by
  have hM : 0 ≤ M := (norm_nonneg _).trans (hb a (mem_ball_self hR))
  let δ : ℕ → ℝ := fun n => R / ((n : ℝ) + 1)
  have hδ : ∀ n, 0 < δ n := fun n => div_pos hR (by positivity)
  have hrad : ∀ n, δ n + n * δ n = R := by
    intro n
    dsimp [δ]
    field_simp
    <;> ring
  have hiter : ∀ n (v : Fin n → E), ‖bha_iterated f n v a‖ ≤ M / δ n ^ n * ∏ i, ‖v i‖ := by
    intro n v
    apply bha_iterated_bound n (hδ n)
    · rwa [hrad]
    · rwa [hrad]
    · exact mem_ball_self (hδ n)
  let L := fun n => bha_multilinear isOpen_ball hf (mem_ball_self hR) n
  let p : FormalMultilinearSeries ℂ E F := fun n => (n.factorial : ℂ)⁻¹ •
    (L n).mkContinuous (M / δ n ^ n) (hiter n)
  have hpn : ∀ n, ‖p n‖ ≤ (n.factorial : ℝ)⁻¹ * (M / δ n ^ n) := by
    intro n
    dsimp only [p]
    rw [norm_smul, norm_inv, Complex.norm_natCast]
    exact mul_le_mul_of_nonneg_left
      ((L n).mkContinuous_norm_le (by positivity) (hiter n)) (by positivity)
  refine ⟨p, fun n v => rfl, ?_⟩
  change (Real.toNNReal (R / Real.exp 1) : ℝ≥0∞) ≤ p.radius
  apply p.le_radius_of_bound (M * Real.exp 1)
  intro n
  rw [Real.coe_toNNReal', max_eq_left (div_nonneg hR.le (Real.exp_pos 1).le)]
  have hf0 : (n.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  calc ‖p n‖ * (R / Real.exp 1) ^ n
      ≤ ((n.factorial : ℝ)⁻¹ * (M / δ n ^ n)) * (R / Real.exp 1) ^ n :=
        mul_le_mul_of_nonneg_right (hpn n) (by positivity)
    _ = M * (((n : ℝ) + 1) ^ n / (n.factorial : ℝ)) / Real.exp 1 ^ n := by
      dsimp [δ]
      simp only [div_pow]
      field_simp [hR.ne', hf0, (Real.exp_pos 1).ne', show (n : ℝ) + 1 ≠ 0 by positivity]
      <;> ring
    _ ≤ M * Real.exp ((n : ℝ) + 1) / Real.exp 1 ^ n :=
      div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left (Real.pow_div_factorial_le_exp ((n : ℝ) + 1) (by positivity) n) hM)
        (by positivity)
    _ = M * Real.exp 1 := by
      rw [Real.exp_add, show Real.exp (n : ℝ) = Real.exp 1 ^ n by
        simpa only [mul_one] using Real.exp_nat_mul 1 n]
      field_simp

-- H7b
theorem bha_iterated_line [CompleteSpace F] {f : E → F} {U : Set E}
    (hU : IsOpen U) (hf : DifferentiableOn ℂ f U) (a v : E)
    {V : Set ℂ} (hV : IsOpen V) (hline : ∀ z ∈ V, a + z • v ∈ U) (n : ℕ) :
    ∀ z ∈ V, iteratedDeriv n (fun t : ℂ => f (a + t • v)) z =
      bha_iterated f n (fun _ => v) (a + z • v) := by
  induction n with
  | zero => intro z hz; rfl
  | succ n ih =>
    intro z hz
    have he : iteratedDeriv n (fun t : ℂ => f (a + t • v)) =ᶠ[𝓝 z]
        (fun t => bha_iterated f n (fun _ => v) (a + t • v)) :=
      Filter.eventuallyEq_of_mem (hV.mem_nhds hz) fun t ht => ih t ht
    rw [iteratedDeriv_succ, he.deriv_eq]
    have hd := (bha_iterated_holomorphic hU hf n (fun _ => v)).differentiableAt
      (hU.mem_nhds (hline z hz))
    have hl : HasDerivAt (fun t : ℂ => a + t • v) v z := by
      simpa using ((hasDerivAt_id z).smul_const v).const_add a
    exact (hd.hasFDerivAt.comp_hasDerivAt z hl).deriv

-- H7c
theorem bha_line_hasSum [CompleteSpace F] {f : E → F} {a h : E} {R : ℝ}
    (hR : 0 < R) (hf : DifferentiableOn ℂ f (ball a R)) (hh : ‖h‖ < R) :
    HasSum (fun n : ℕ => (n.factorial : ℂ)⁻¹ • bha_iterated f n (fun _ => h) a) (f (a + h)) := by
  obtain ⟨ρ, hρ1, hρR⟩ : ∃ ρ : ℝ, 1 < ρ ∧ ρ * ‖h‖ < R := by
    by_cases hh0 : h = 0
    · exact ⟨2, by norm_num, by simpa [hh0] using hR⟩
    · have hp : 0 < ‖h‖ := norm_pos_iff.mpr hh0
      have hq : 1 < R / ‖h‖ := (lt_div_iff₀ hp).mpr (by simpa using hh)
      obtain ⟨ρ, hρ1, hρ2⟩ := exists_between hq
      exact ⟨ρ, hρ1, (lt_div_iff₀ hp).mp hρ2⟩
  have hline : ∀ z ∈ ball (0 : ℂ) ρ, a + z • h ∈ ball a R := by
    intro z hz
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul]
    exact (mul_le_mul_of_nonneg_right (mem_ball_zero_iff.mp hz).le (norm_nonneg _)).trans_lt hρR
  have hg : DifferentiableOn ℂ (fun z : ℂ => f (a + z • h)) (ball 0 ρ) := by
    intro z hz
    exact ((hf.differentiableAt (isOpen_ball.mem_nhds (hline z hz))).comp z
      ((differentiableAt_const a).add (differentiableAt_id.smul_const h))).differentiableWithinAt
  have hs := Complex.hasSum_taylorSeries_on_ball hg
    (show (1 : ℂ) ∈ ball 0 ρ by simpa only [mem_ball_zero_iff, norm_one] using hρ1)
  simp only [sub_zero, one_pow, one_smul] at hs
  have he : ∀ n, iteratedDeriv n (fun z : ℂ => f (a + z • h)) 0 =
      bha_iterated f n (fun _ => h) a := by
    intro n
    simpa only [zero_smul, add_zero] using bha_iterated_line isOpen_ball hf a h
      isOpen_ball hline n 0 (mem_ball_self (by linarith : 0 < ρ))
  simpa only [he] using hs

-- H8
theorem bha_analyticAt_of_ball [CompleteSpace F] {f : E → F} {a : E} {R M : ℝ}
    (hR : 0 < R) (hf : DifferentiableOn ℂ f (ball a R))
    (hb : ∀ z ∈ ball a R, ‖f z‖ ≤ M) : AnalyticAt ℂ f a := by
  obtain ⟨p, hp, hr⟩ := bha_coefficients hR hf hb
  refine ⟨p, ENNReal.ofReal (R / Real.exp 1), hr,
    ENNReal.ofReal_pos.mpr (div_pos hR (Real.exp_pos 1)), ?_⟩
  intro y hy
  have hy' : ‖y‖ < R / Real.exp 1 := by
    simpa only [Metric.eball_ofReal, mem_ball_zero_iff] using hy
  have hs := bha_line_hasSum hR hf (hy'.trans_le (div_le_self hR.le (Real.one_le_exp (by norm_num))))
  simpa only [hp] using hs

-- H0 (complete target)
theorem bha_analyticOnNhd [CompleteSpace F] {f : E → F} {U : Set E}
    (hU : IsOpen U) (hf : DifferentiableOn ℂ f U) : AnalyticOnNhd ℂ f U := by
  intro a ha
  obtain ⟨r0, hr0, hsub⟩ := Metric.isOpen_iff.mp hU a ha
  have hc : ContinuousAt f a := (hf.differentiableAt (hU.mem_nhds ha)).continuousAt
  obtain ⟨r1, hr1, hb⟩ := Metric.eventually_nhds_iff_ball.mp
    (hc.norm.eventually (gt_mem_nhds (by linarith : ‖f a‖ < ‖f a‖ + 1)))
  exact bha_analyticAt_of_ball (lt_min hr0 hr1)
    (hf.mono ((ball_subset_ball (min_le_left r0 r1)).trans hsub))
    (fun z hz => (hb z (ball_subset_ball (min_le_right r0 r1) hz)).le)

end TakhtajanTeo
