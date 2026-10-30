import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Topology.UniformSpace.HeineCantor

/-!
# Löwner chains: subordination and small-time univalence

General results behind Becker–Pommerenke [BP78] §3 (`loew_` prefix):
* `loew_flow_subordination`: a solution of the Löwner PDE `∂_t f = z p f'` with `Re p ≥ δ > 0` satisfies
  `f_s = f_t ∘ φ` on `𝔻̄`, `φ` the flow map of `ẇ = -w p(w, ·)` (continuous, injective, contracting).
* `loew_injOn_small_time`: BP78's compactness argument for univalence of `f_t` on `𝔻̄` for small `t`.
No Hölder estimates (Becker 1972) are needed.
-/

open Complex Set Metric Filter Topology
open scoped ComplexConjugate NNReal

noncomputable section

namespace TakhtajanTeo

/-- The radial retraction `w ↦ w / max 1 |w|` onto `𝔻̄` is `2`-Lipschitz. -/
theorem loew_retract_lipschitz :
    LipschitzWith 2 (fun w : ℂ => ((max 1 ‖w‖ : ℝ) : ℂ)⁻¹ * w) := by
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  simp only [dist_eq_norm, NNReal.coe_ofNat]
  set mx : ℝ := max 1 ‖x‖ with hmxd
  set my : ℝ := max 1 ‖y‖ with hmyd
  have hmx : 1 ≤ mx := le_max_left _ _
  have hmy : 1 ≤ my := le_max_left _ _
  have hmx0 : (mx : ℂ) ≠ 0 := by exact_mod_cast (show mx ≠ 0 by linarith)
  have hmy0 : (my : ℂ) ≠ 0 := by exact_mod_cast (show my ≠ 0 by linarith)
  have hyle : ‖y‖ ≤ my := le_max_right _ _
  have hdiff : |my - mx| ≤ ‖x - y‖ := by
    calc |my - mx| ≤ |‖y‖ - ‖x‖| := by
          rw [hmxd, hmyd, max_comm 1 ‖y‖, max_comm 1 ‖x‖]
          exact abs_max_sub_max_le_abs _ _ _
      _ ≤ ‖y - x‖ := abs_norm_sub_norm_le y x
      _ = ‖x - y‖ := norm_sub_rev y x
  have key : (mx : ℂ)⁻¹ * x - (my : ℂ)⁻¹ * y =
      (mx : ℂ)⁻¹ * (x - y) + y * (((my - mx) / (mx * my) : ℝ) : ℂ) := by
    push_cast
    field_simp
    ring
  rw [key]
  have h1 : ‖(mx : ℂ)⁻¹ * (x - y)‖ ≤ ‖x - y‖ := by
    rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg (by linarith)]
    exact mul_le_of_le_one_left (norm_nonneg _) (inv_le_one_of_one_le₀ hmx)
  have h2 : ‖y * (((my - mx) / (mx * my) : ℝ) : ℂ)‖ ≤ ‖x - y‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_div,
      abs_of_pos (by positivity : (0 : ℝ) < mx * my)]
    have hq1 : ‖y‖ / my ≤ 1 := (div_le_one (by linarith)).mpr hyle
    have hq2 : |my - mx| / mx ≤ ‖x - y‖ := (div_le_self (abs_nonneg _) hmx).trans hdiff
    calc ‖y‖ * (|my - mx| / (mx * my)) = (‖y‖ / my) * (|my - mx| / mx) := by
          field_simp
      _ ≤ 1 * ‖x - y‖ := mul_le_mul hq1 hq2 (by positivity) zero_le_one
      _ = ‖x - y‖ := one_mul _
  linarith [norm_add_le ((mx : ℂ)⁻¹ * (x - y)) (y * (((my - mx) / (mx * my) : ℝ) : ℂ))]

/-- Uniform bounds for `p` on `[s, t] × 𝔻̄`: a sup bound and a Lipschitz constant in `z`. -/
theorem loew_pbounds {p : ℝ → ℂ → ℂ} {s t a b ρ : ℝ} (has : a < s) (htb : t < b) (hρ : 1 < ρ)
    (hp : ContDiffOn ℝ 1 (fun q : ℝ × ℂ => p q.1 q.2) (Ioo a b ×ˢ ball (0 : ℂ) ρ)) :
    ∃ M Lp : ℝ≥0, (∀ τ ∈ Icc s t, ∀ w ∈ closedBall (0 : ℂ) 1, ‖p τ w‖ ≤ M) ∧
      ∀ τ ∈ Icc s t, LipschitzOnWith Lp (p τ) (closedBall (0 : ℂ) 1) := by
  have hO : IsOpen (Ioo a b ×ˢ ball (0 : ℂ) ρ) := isOpen_Ioo.prod isOpen_ball
  have hK : IsCompact (Icc s t ×ˢ closedBall (0 : ℂ) 1) := isCompact_Icc.prod (isCompact_closedBall _ _)
  have hsub : Icc s t ×ˢ closedBall (0 : ℂ) 1 ⊆ Ioo a b ×ˢ ball (0 : ℂ) ρ := by
    rintro ⟨τ, w⟩ ⟨hτ, hw⟩
    exact ⟨⟨has.trans_le hτ.1, hτ.2.trans_lt htb⟩,
      mem_ball_zero_iff.mpr ((mem_closedBall_zero_iff.mp hw).trans_lt hρ)⟩
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn (hp.continuousOn.mono hsub)
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn
    ((hp.continuousOn_fderiv_of_isOpen hO le_rfl).mono hsub)
  refine ⟨M.toNNReal, C.toNNReal, fun τ hτ w hw => (hM (τ, w) ⟨hτ, hw⟩).trans (Real.le_coe_toNNReal M),
    fun τ hτ => ?_⟩
  have hd : ∀ w ∈ closedBall (0 : ℂ) 1, HasFDerivAt (p τ)
      ((fderiv ℝ (fun q : ℝ × ℂ => p q.1 q.2) (τ, w)).comp
        ((0 : ℂ →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ ℂ))) w := by
    intro w hw
    have hPd : DifferentiableAt ℝ (fun q : ℝ × ℂ => p q.1 q.2) (τ, w) :=
      (hp.differentiableOn one_ne_zero).differentiableAt (hO.mem_nhds (hsub ⟨hτ, hw⟩))
    exact hPd.hasFDerivAt.comp w ((hasFDerivAt_const τ w).prodMk (hasFDerivAt_id w))
  refine (convex_closedBall (0 : ℂ) 1).lipschitzOnWith_of_nnnorm_hasFDerivWithin_le
    (fun w hw => (hd w hw).hasFDerivWithinAt) (fun w hw => ?_)
  rw [← NNReal.coe_le_coe, coe_nnnorm]
  refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
  have hpr : ‖(0 : ℂ →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ ℂ)‖ ≤ 1 := by
    refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v => ?_
    rw [ContinuousLinearMap.prod_apply]
    simp [Prod.norm_def]
  calc ‖fderiv ℝ (fun q : ℝ × ℂ => p q.1 q.2) (τ, w)‖ *
        ‖(0 : ℂ →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ ℂ)‖
      ≤ C * 1 := mul_le_mul (hC (τ, w) ⟨hτ, hw⟩) hpr (norm_nonneg _)
          ((norm_nonneg _).trans (hC (τ, w) ⟨hτ, hw⟩))
    _ ≤ (C.toNNReal : ℝ) := by rw [mul_one]; exact Real.le_coe_toNNReal C

/-- **Löwner subordination** (BP78 (3.1)–(3.2); Pommerenke 1975 §6.1). If `∂_t f = z p f'` on a
neighbourhood of `[s, t] × 𝔻̄` with `Re p ≥ δ > 0` on `[s, t] × 𝔻̄`, then `f_s = f_t ∘ φ` on `𝔻̄` for the
flow map `φ` of `ẇ = -w p(w, ·)` from time `s` to `t`: `φ` is continuous, injective and contracts by
`e^{-δ(t-s)}`. -/
theorem loew_flow_subordination {f p : ℝ → ℂ → ℂ} {s t a b ρ δ : ℝ} (hst : s ≤ t) (has : a < s)
    (htb : t < b) (hρ : 1 < ρ) (hδ : 0 < δ)
    (hf : ContDiffOn ℝ 1 (fun q : ℝ × ℂ => f q.1 q.2) (Ioo a b ×ˢ ball (0 : ℂ) ρ))
    (hfz : ∀ τ ∈ Ioo a b, DifferentiableOn ℂ (f τ) (ball (0 : ℂ) ρ))
    (hp : ContDiffOn ℝ 1 (fun q : ℝ × ℂ => p q.1 q.2) (Ioo a b ×ˢ ball (0 : ℂ) ρ))
    (hpde : ∀ τ ∈ Ioo a b, ∀ z ∈ ball (0 : ℂ) ρ,
      HasDerivAt (fun σ => f σ z) (z * p τ z * deriv (f τ) z) τ)
    (hRe : ∀ τ ∈ Icc s t, ∀ z ∈ closedBall (0 : ℂ) 1, δ ≤ (p τ z).re) :
    ∃ φ : ℂ → ℂ, ContinuousOn φ (closedBall (0 : ℂ) 1) ∧ InjOn φ (closedBall (0 : ℂ) 1) ∧
      (∀ z ∈ closedBall (0 : ℂ) 1, ‖φ z‖ ≤ Real.exp (-(δ * (t - s))) * ‖z‖) ∧
      ∀ z ∈ closedBall (0 : ℂ) 1, f s z = f t (φ z) := by
  obtain ⟨M, Lp, hM, hLp⟩ := loew_pbounds has htb hρ hp
  have hIcc : ∀ τ ∈ Icc s t, τ ∈ Ioo a b := fun τ hτ => ⟨has.trans_le hτ.1, hτ.2.trans_lt htb⟩
  set R : ℂ → ℂ := fun w => ((max 1 ‖w‖ : ℝ) : ℂ)⁻¹ * w with hR
  have hRl : LipschitzWith 2 R := loew_retract_lipschitz
  have hRn : ∀ w, R w ∈ closedBall (0 : ℂ) 1 := by
    intro w
    rw [mem_closedBall_zero_iff, hR]
    simp only
    rw [norm_mul, norm_inv, Complex.norm_real,
      Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ max 1 ‖w‖)]
    rw [inv_mul_le_iff₀ (by positivity : (0 : ℝ) < max 1 ‖w‖), mul_one]
    exact le_max_right _ _
  have hRid : ∀ w ∈ closedBall (0 : ℂ) 1, R w = w := by
    intro w hw
    have h1 : max 1 ‖w‖ = 1 := max_eq_left (mem_closedBall_zero_iff.mp hw)
    simp only [hR, h1, Complex.ofReal_one, inv_one, one_mul]
  -- the field `v = -w p` on `𝔻̄` and its retracted extension `V`
  have hvL : ∀ τ ∈ Icc s t, LipschitzOnWith (M + Lp) (fun w => -(w * p τ w)) (closedBall (0 : ℂ) 1) := by
    intro τ hτ
    refine LipschitzOnWith.of_dist_le_mul fun x hx y hy => ?_
    rw [dist_eq_norm, dist_eq_norm, neg_sub_neg]
    have hpxy : ‖p τ y - p τ x‖ ≤ Lp * ‖y - x‖ := by
      have := (hLp τ hτ).dist_le_mul y hy x hx
      rwa [dist_eq_norm, dist_eq_norm] at this
    have hy1 : ‖x‖ ≤ 1 := mem_closedBall_zero_iff.mp hx
    have e : y * p τ y - x * p τ x = (y - x) * p τ y + x * (p τ y - p τ x) := by ring
    rw [e, norm_sub_rev x y]
    calc ‖(y - x) * p τ y + x * (p τ y - p τ x)‖
        ≤ ‖y - x‖ * ‖p τ y‖ + ‖x‖ * ‖p τ y - p τ x‖ := by
          refine (norm_add_le _ _).trans ?_
          rw [norm_mul, norm_mul]
      _ ≤ ‖y - x‖ * M + 1 * (Lp * ‖y - x‖) := by
          gcongr
          · exact hM τ hτ y hy
      _ = ((M + Lp : ℝ≥0) : ℝ) * ‖y - x‖ := by push_cast; ring
  set V : ℝ → ℂ → ℂ := fun τ w => -(R w * p τ (R w)) with hV
  have hVL : ∀ τ ∈ Icc s t, LipschitzWith ((M + Lp) * 2) (V τ) := by
    intro τ hτ
    rw [← lipschitzOnWith_univ]
    exact (hvL τ hτ).comp hRl.lipschitzOnWith (fun w _ => hRn w)
  have hVb : ∀ τ ∈ Icc s t, ∀ w, ‖V τ w‖ ≤ M := by
    intro τ hτ w
    simp only [hV, norm_neg, norm_mul]
    calc ‖R w‖ * ‖p τ (R w)‖ ≤ 1 * M :=
          mul_le_mul (mem_closedBall_zero_iff.mp (hRn w)) (hM τ hτ _ (hRn w)) (norm_nonneg _) zero_le_one
      _ = M := one_mul _
  have hVc : ∀ w, ContinuousOn (fun τ => V τ w) (Icc s t) := by
    intro w
    have hc : ContinuousOn (fun τ => p τ (R w)) (Icc s t) :=
      hp.continuousOn.comp (continuousOn_id.prodMk continuousOn_const)
        (fun τ hτ => ⟨hIcc τ hτ, mem_ball_zero_iff.mpr
          ((mem_closedBall_zero_iff.mp (hRn w)).trans_lt hρ)⟩)
    exact (continuousOn_const.mul hc).neg
  -- Picard–Lindelöf on `[s, t]`
  have hPL : IsPicardLindelof V (tmin := s) (tmax := t) ⟨s, left_mem_Icc.mpr hst⟩ (0 : ℂ)
      (1 + M * (t - s).toNNReal) 1 M ((M + Lp) * 2) :=
    { lipschitzOnWith := fun τ hτ => (hVL τ hτ).lipschitzOnWith
      continuousOn := fun x _ => hVc x
      norm_le := fun τ hτ x _ => hVb τ hτ x
      mul_max_le := by
        simp only [NNReal.coe_add, NNReal.coe_one, NNReal.coe_mul,
          Real.coe_toNNReal _ (sub_nonneg.mpr hst), sub_self]
        rw [max_eq_left (sub_nonneg.mpr hst)]
        linarith }
  obtain ⟨α, hα, L', hαL⟩ := hPL.exists_forall_mem_closedBall_eq_hasDerivWithinAt_lipschitzOnWith
  have hα0 : ∀ x ∈ closedBall (0 : ℂ) 1, α x s = x := fun x hx => (hα x hx).1
  have hαd : ∀ x ∈ closedBall (0 : ℂ) 1, ∀ τ ∈ Icc s t,
      HasDerivWithinAt (α x) (V τ (α x τ)) (Icc s t) τ := fun x hx => (hα x hx).2
  -- the inner product estimate `⟨y, V y⟩ ≤ -δ |y|²/max 1 |y|`
  have hinner : ∀ τ ∈ Icc s t, ∀ y : ℂ,
      inner ℝ y (V τ y) ≤ -(δ * ‖y‖ ^ 2 / max 1 ‖y‖) := by
    intro τ hτ y
    have hm : (0 : ℝ) < max 1 ‖y‖ := lt_of_lt_of_le one_pos (le_max_left _ _)
    have he : V τ y * conj y = -(((‖y‖ ^ 2 / max 1 ‖y‖ : ℝ) : ℂ) * p τ (R y)) := by
      simp only [hV, hR]
      rw [show (-(((max 1 ‖y‖ : ℝ) : ℂ)⁻¹ * y * p τ (((max 1 ‖y‖ : ℝ) : ℂ)⁻¹ * y)) * conj y) =
        -(((max 1 ‖y‖ : ℝ) : ℂ)⁻¹ * (y * conj y) * p τ (((max 1 ‖y‖ : ℝ) : ℂ)⁻¹ * y)) by ring,
        Complex.mul_conj']
      push_cast
      ring
    rw [Complex.inner, he, Complex.neg_re, Complex.re_ofReal_mul]
    have hre := hRe τ hτ (R y) (hRn y)
    have hnn : 0 ≤ ‖y‖ ^ 2 / max 1 ‖y‖ := by positivity
    have : δ * ‖y‖ ^ 2 / max 1 ‖y‖ = ‖y‖ ^ 2 / max 1 ‖y‖ * δ := by ring
    rw [this]
    exact neg_le_neg (mul_le_mul_of_nonneg_left hre hnn)
  -- decay `|φ_τ(x)| ≤ e^{-δ(τ-s)} |x|`
  have hdecay : ∀ x ∈ closedBall (0 : ℂ) 1, ∀ τ ∈ Icc s t,
      ‖α x τ‖ ≤ Real.exp (-(δ * (τ - s))) * ‖x‖ := by
    intro x hx
    have hx1 : ‖x‖ ≤ 1 := mem_closedBall_zero_iff.mp hx
    have hNd : ∀ τ ∈ Icc s t, HasDerivWithinAt (fun σ => ‖α x σ‖ ^ 2)
        (2 * inner ℝ (α x τ) (V τ (α x τ))) (Icc s t) τ := fun τ hτ => (hαd x hx τ hτ).norm_sq
    have hNc : ContinuousOn (fun σ => ‖α x σ‖ ^ 2) (Icc s t) := fun τ hτ =>
      (hNd τ hτ).continuousWithinAt
    have hNsq : ∀ τ ∈ Icc s t, ‖α x τ‖ ^ 2 ≤ Real.exp (-(2 * δ * (τ - s))) * ‖x‖ ^ 2 := by
      intro τ hτ
      have hE : ∀ σ : ℝ, -(2 * δ * (σ - s)) = -(2 * δ) * (σ - s) := fun σ => by ring
      rw [hE]
      refine le_of_forall_pos_lt_add fun ε hε => ?_
      have hB : ∀ σ, HasDerivAt (fun σ => Real.exp (-(2 * δ) * (σ - s)) * ‖x‖ ^ 2 +
          ε / 2 * Real.exp (δ * (σ - t)))
          (-(2 * δ) * Real.exp (-(2 * δ) * (σ - s)) * ‖x‖ ^ 2 +
            ε / 2 * (δ * Real.exp (δ * (σ - t)))) σ := by
        intro σ
        have h1 := ((hasDerivAt_id' σ).sub_const s).const_mul (-(2 * δ))
        have h2 := ((hasDerivAt_id' σ).sub_const t).const_mul δ
        have := ((h1.exp.mul_const (‖x‖ ^ 2)).add (h2.exp.const_mul (ε / 2)))
        convert this using 1
        ring
      have hle := image_le_of_deriv_right_lt_deriv_boundary hNc
        (fun σ hσ => (hNd σ (Ico_subset_Icc_self hσ)).mono_of_mem_nhdsWithin
          (Icc_mem_nhdsGE_of_mem hσ))
        (by
          simp only [sub_self, mul_zero, Real.exp_zero, one_mul, hα0 x hx]
          have := Real.exp_pos (δ * (s - t))
          nlinarith)
        hB (by
          intro σ hσ heq
          have hσ' := Ico_subset_Icc_self hσ
          have hi := hinner σ hσ' (α x σ)
          have hc : 0 < δ * (ε / 2 * Real.exp (δ * (σ - t))) := by positivity
          have he2 : Real.exp (-(2 * δ) * (σ - s)) ≤ 1 :=
            Real.exp_le_one_iff.mpr (by nlinarith [hσ'.1])
          have hN : δ * ‖α x σ‖ ^ 2 =
              δ * (Real.exp (-(2 * δ) * (σ - s)) * ‖x‖ ^ 2) + δ * (ε / 2 * Real.exp (δ * (σ - t))) := by
            rw [heq]
            ring
          by_cases hy : ‖α x σ‖ ≤ 1
          · have hm : max 1 ‖α x σ‖ = 1 := max_eq_left hy
            rw [hm, div_one] at hi
            linarith
          · rw [not_le] at hy
            have hm : max 1 ‖α x σ‖ = ‖α x σ‖ := max_eq_right hy.le
            rw [hm] at hi
            have hn0 : 0 < ‖α x σ‖ := by linarith
            have hq : ‖α x σ‖ ^ 2 / ‖α x σ‖ = ‖α x σ‖ := by field_simp
            have hi' : inner ℝ (α x σ) (V σ (α x σ)) ≤ -(δ * ‖α x σ‖) := by
              rw [mul_div_assoc, hq] at hi
              exact hi
            have hxx : Real.exp (-(2 * δ) * (σ - s)) * ‖x‖ ^ 2 ≤ 1 := by
              have : ‖x‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg x]
              nlinarith [Real.exp_pos (-(2 * δ) * (σ - s))]
            have h3 : δ * 1 < δ * ‖α x σ‖ := mul_lt_mul_of_pos_left hy hδ
            have h4 : δ * (Real.exp (-(2 * δ) * (σ - s)) * ‖x‖ ^ 2) ≤ δ * 1 :=
              mul_le_mul_of_nonneg_left hxx hδ.le
            linarith) hτ
      have h5 : Real.exp (δ * (τ - t)) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [hτ.2])
      have h6 : ε / 2 * Real.exp (δ * (τ - t)) ≤ ε / 2 := by nlinarith
      linarith
    intro τ hτ
    have h := hNsq τ hτ
    have hsq : Real.exp (-(2 * δ * (τ - s))) * ‖x‖ ^ 2 = (Real.exp (-(δ * (τ - s))) * ‖x‖) ^ 2 := by
      rw [mul_pow, ← Real.exp_nat_mul]
      ring_nf
    rw [hsq] at h
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp h
  have hin : ∀ x ∈ closedBall (0 : ℂ) 1, ∀ τ ∈ Icc s t, α x τ ∈ closedBall (0 : ℂ) 1 := by
    intro x hx τ hτ
    rw [mem_closedBall_zero_iff]
    refine (hdecay x hx τ hτ).trans ?_
    have h1 : Real.exp (-(δ * (τ - s))) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by nlinarith [hτ.1])
    calc Real.exp (-(δ * (τ - s))) * ‖x‖ ≤ 1 * 1 :=
          mul_le_mul h1 (mem_closedBall_zero_iff.mp hx) (norm_nonneg _) zero_le_one
      _ = 1 := one_mul 1
  -- conservation of `f_τ(φ_τ(x))`
  have hcons : ∀ x ∈ closedBall (0 : ℂ) 1, f s x = f t (α x t) := by
    intro x hx
    have hΦ : ∀ τ ∈ Icc s t, HasDerivWithinAt (fun σ => f σ (α x σ)) 0 (Icc s t) τ := by
      intro τ hτ
      have hy := hin x hx τ hτ
      have hyb : α x τ ∈ ball (0 : ℂ) ρ :=
        mem_ball_zero_iff.mpr ((mem_closedBall_zero_iff.mp hy).trans_lt hρ)
      have hO : (τ, α x τ) ∈ Ioo a b ×ˢ ball (0 : ℂ) ρ := ⟨hIcc τ hτ, hyb⟩
      have hFd : HasFDerivAt (fun q : ℝ × ℂ => f q.1 q.2)
          (fderiv ℝ (fun q : ℝ × ℂ => f q.1 q.2) (τ, α x τ)) (τ, α x τ) :=
        ((hf.differentiableOn one_ne_zero).differentiableAt
          ((isOpen_Ioo.prod isOpen_ball).mem_nhds hO)).hasFDerivAt
      set F' := fderiv ℝ (fun q : ℝ × ℂ => f q.1 q.2) (τ, α x τ) with hF'
      have h1 : F' (1, 0) = α x τ * p τ (α x τ) * deriv (f τ) (α x τ) := by
        have h := hFd.comp_hasDerivAt τ ((hasDerivAt_id τ).prodMk (hasDerivAt_const τ (α x τ)))
        exact h.unique (hpde τ (hIcc τ hτ) (α x τ) hyb)
      have h2 : ∀ v : ℂ, F' (0, v) = deriv (f τ) (α x τ) * v := by
        have hz : HasFDerivAt (f τ) (F'.comp ((0 : ℂ →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ ℂ)))
            (α x τ) := hFd.comp (α x τ) ((hasFDerivAt_const τ _).prodMk (hasFDerivAt_id _))
        have hz' := (((hfz τ (hIcc τ hτ)).differentiableAt (isOpen_ball.mem_nhds hyb)).hasDerivAt
          ).hasFDerivAt.restrictScalars ℝ
        intro v
        have := congrArg (fun L : ℂ →L[ℝ] ℂ => L v) (hz.unique hz')
        simpa [mul_comm] using this
      have hcomp := hFd.comp_hasDerivWithinAt τ ((hasDerivWithinAt_id τ (Icc s t)).prodMk (hαd x hx τ hτ))
      have hcomp' : HasDerivWithinAt (fun σ => f σ (α x σ)) (F' ((1 : ℝ), V τ (α x τ))) (Icc s t) τ :=
        hcomp
      convert hcomp' using 1
      have hsplit : ((1 : ℝ), V τ (α x τ)) = ((1 : ℝ), (0 : ℂ)) + ((0 : ℝ), V τ (α x τ)) := by simp
      rw [hsplit, map_add, h1, h2]
      simp only [hV, hRid _ hy]
      ring
    have hcont : ContinuousOn (fun σ => f σ (α x σ)) (Icc s t) := fun τ hτ => (hΦ τ hτ).continuousWithinAt
    have hconst := constant_of_has_deriv_right_zero hcont
      (fun τ hτ => (hΦ τ (Ico_subset_Icc_self hτ)).mono_of_mem_nhdsWithin (Icc_mem_nhdsGE_of_mem hτ))
      t (right_mem_Icc.mpr hst)
    simp only [hα0 x hx] at hconst
    exact hconst.symm
  -- injectivity of the flow map (backward uniqueness)
  have hinj : InjOn (fun x => α x t) (closedBall (0 : ℂ) 1) := by
    intro x hx y hy hxy
    have hcx : ContinuousOn (α x) (Icc s t) := fun τ hτ => (hαd x hx τ hτ).continuousWithinAt
    have hcy : ContinuousOn (α y) (Icc s t) := fun τ hτ => (hαd y hy τ hτ).continuousWithinAt
    have heq := ODE_solution_unique_of_mem_Icc_left (v := V) (s := fun _ => univ)
      (K := (M + Lp) * 2) (fun τ hτ => (hVL τ (Ioc_subset_Icc_self hτ)).lipschitzOnWith) hcx
      (fun τ hτ => (hαd x hx τ (Ioc_subset_Icc_self hτ)).mono_of_mem_nhdsWithin (Icc_mem_nhdsLE_of_mem hτ))
      (fun _ _ => mem_univ _) hcy
      (fun τ hτ => (hαd y hy τ (Ioc_subset_Icc_self hτ)).mono_of_mem_nhdsWithin (Icc_mem_nhdsLE_of_mem hτ))
      (fun _ _ => mem_univ _) hxy
    have h := heq (left_mem_Icc.mpr hst)
    rwa [hα0 x hx, hα0 y hy] at h
  exact ⟨fun x => α x t, (hαL t (right_mem_Icc.mpr hst)).continuousOn, hinj,
    fun x hx => hdecay x hx t (right_mem_Icc.mpr hst), hcons⟩

/-- A continuous `g` that separates the pairs of a compact `K` at distances in `[c₁, c₂]` separates them
uniformly. -/
theorem loew_uniform_sep {K : Set ℂ} (hK : IsCompact K) {g : ℂ → ℂ} (hg : ContinuousOn g K)
    {c₁ c₂ : ℝ} (hne : ∀ u ∈ K, ∀ v ∈ K, c₁ ≤ dist u v → dist u v ≤ c₂ → g u ≠ g v) :
    ∃ m > 0, ∀ u ∈ K, ∀ v ∈ K, c₁ ≤ dist u v → dist u v ≤ c₂ → m ≤ ‖g u - g v‖ := by
  set Q : Set (ℂ × ℂ) := (K ×ˢ K) ∩ {q | c₁ ≤ dist q.1 q.2 ∧ dist q.1 q.2 ≤ c₂} with hQ
  have hQc : IsCompact Q := (hK.prod hK).inter_right
    ((isClosed_le continuous_const (continuous_fst.dist continuous_snd)).inter
      (isClosed_le (continuous_fst.dist continuous_snd) continuous_const))
  have hh : ContinuousOn (fun q : ℂ × ℂ => ‖g q.1 - g q.2‖) Q :=
    ((hg.comp continuous_fst.continuousOn fun q hq => hq.1.1).sub
      (hg.comp continuous_snd.continuousOn fun q hq => hq.1.2)).norm
  rcases Q.eq_empty_or_nonempty with hQe | hQn
  · refine ⟨1, one_pos, fun u hu v hv h1 h2 => ?_⟩
    have : (u, v) ∈ Q := ⟨⟨hu, hv⟩, h1, h2⟩
    rw [hQe] at this
    simp at this
  obtain ⟨q₀, hq₀, hmin⟩ := hQc.exists_isMinOn hQn hh
  refine ⟨‖g q₀.1 - g q₀.2‖, norm_pos_iff.mpr (sub_ne_zero.mpr
    (hne _ hq₀.1.1 _ hq₀.1.2 hq₀.2.1 hq₀.2.2)), fun u hu v hv h1 h2 => ?_⟩
  exact hmin (show (u, v) ∈ Q from ⟨⟨hu, hv⟩, h1, h2⟩)

/-- Uniform local injectivity of a holomorphic `G` with `G' ≠ 0` on a closed disc. -/
theorem loew_unif_locinj {G : ℂ → ℂ} {r₀ ρ : ℝ} (hr₀ : r₀ < ρ) (hG : DifferentiableOn ℂ G (ball (0 : ℂ) ρ))
    (hG' : ∀ w ∈ closedBall (0 : ℂ) r₀, deriv G w ≠ 0) :
    ∃ η > 0, ∀ x ∈ closedBall (0 : ℂ) r₀, ∀ y ∈ closedBall (0 : ℂ) r₀, dist x y < η → G x = G y → x = y := by
  have hloc : ∀ c : closedBall (0 : ℂ) r₀, ∃ U : Set ℂ, IsOpen U ∧ (c : ℂ) ∈ U ∧ InjOn G U := by
    rintro ⟨c, hc⟩
    have hcb : c ∈ ball (0 : ℂ) ρ :=
      mem_ball_zero_iff.mpr ((mem_closedBall_zero_iff.mp hc).trans_lt hr₀)
    have hA : AnalyticAt ℂ G c := hG.analyticAt (isOpen_ball.mem_nhds hcb)
    have hS := hA.hasStrictDerivAt
    obtain ⟨U, hUsub, hUo, hcU⟩ := _root_.mem_nhds_iff.mp (hS.eventually_left_inverse (hG' c hc))
    refine ⟨U, hUo, hcU, fun x hx y hy hxy => ?_⟩
    have hx' := hUsub hx
    have hy' := hUsub hy
    simp only [mem_ofPred_eq] at hx' hy'
    rw [← hx', ← hy', hxy]
  choose U hUo hcU hUi using hloc
  obtain ⟨η, hη, hleb⟩ := lebesgue_number_lemma_of_metric (isCompact_closedBall (0 : ℂ) r₀) hUo
    (fun c hc => mem_iUnion.mpr ⟨⟨c, hc⟩, hcU ⟨c, hc⟩⟩)
  refine ⟨η, hη, fun x hx y hy hxy he => ?_⟩
  obtain ⟨i, hi⟩ := hleb x hx
  exact hUi i (hi (mem_ball_self hη)) (hi (by rw [mem_ball, dist_comm]; exact hxy)) he

/-- **Small-time univalence** (BP78 §3, p. 79). Let `F_t → F₀` uniformly on `𝔻̄` as `t → 0⁺`, with `F₀`
continuous and injective on `𝔻̄`, and `F_t = G ∘ φ_t` on `𝔻̄` with `φ_t` continuous, injective, mapping
`𝔻̄` into `{|w| ≤ r₀}`, `r₀ < 1`, and `G` holomorphic with `G' ≠ 0` near `{|w| ≤ r₀}`. Then every `F_t`,
`0 < t ≤ τ`, is injective on `𝔻̄`. -/
theorem loew_injOn_small_time {F φ : ℝ → ℂ → ℂ} {F₀ G : ℂ → ℂ} {τ₀ r₀ ρ : ℝ} (hτ₀ : 0 < τ₀)
    (hr₀ : r₀ < ρ) (h0c : ContinuousOn F₀ (closedBall (0 : ℂ) 1))
    (h0i : InjOn F₀ (closedBall (0 : ℂ) 1))
    (hunif : TendstoUniformlyOn F F₀ (𝓝[>] 0) (closedBall (0 : ℂ) 1))
    (hG : DifferentiableOn ℂ G (ball (0 : ℂ) ρ)) (hG' : ∀ w ∈ closedBall (0 : ℂ) r₀, deriv G w ≠ 0)
    (hφc : ∀ t ∈ Ioc 0 τ₀, ContinuousOn (φ t) (closedBall (0 : ℂ) 1))
    (hφi : ∀ t ∈ Ioc 0 τ₀, InjOn (φ t) (closedBall (0 : ℂ) 1))
    (hφm : ∀ t ∈ Ioc 0 τ₀, MapsTo (φ t) (closedBall (0 : ℂ) 1) (closedBall (0 : ℂ) r₀))
    (hfac : ∀ t ∈ Ioc 0 τ₀, ∀ z ∈ closedBall (0 : ℂ) 1, F t z = G (φ t z)) :
    ∃ τ ∈ Ioc 0 τ₀, ∀ t ∈ Ioc 0 τ, InjOn (F t) (closedBall (0 : ℂ) 1) := by
  set D : Set ℂ := closedBall (0 : ℂ) 1 with hD
  set K : Set ℂ := closedBall (0 : ℂ) r₀ with hKd
  have hDc : IsCompact D := isCompact_closedBall _ _
  have hDconv : Convex ℝ D := convex_closedBall _ _
  -- uniform local injectivity of `G` on `K`, and the separation `m` at distance `η/2`
  obtain ⟨η, hη, hinjG⟩ := loew_unif_locinj hr₀ hG hG'
  have hGc : ContinuousOn G K := hG.continuousOn.mono fun w hw =>
    mem_ball_zero_iff.mpr ((mem_closedBall_zero_iff.mp hw).trans_lt hr₀)
  obtain ⟨m, hm, hsepG⟩ := loew_uniform_sep (isCompact_closedBall (0 : ℂ) r₀) hGc
    (c₁ := η / 2) (c₂ := η / 2) (fun u hu v hv h1 h2 he => by
      have := hinjG u hu v hv (by linarith) he
      rw [this, dist_self] at h1
      linarith)
  -- uniform continuity of `F₀` on `𝔻̄`
  obtain ⟨κ, hκ, hucF⟩ := Metric.uniformContinuousOn_iff.mp
    (hDc.uniformContinuousOn_of_continuous h0c) (m / 3) (by positivity)
  -- uniform continuity of `F₀⁻¹`: pairs at distance `≥ κ` are separated by `ε₀`
  obtain ⟨ε₀, hε₀, hsepF⟩ := loew_uniform_sep hDc h0c (c₁ := κ) (c₂ := 3) (fun u hu v hv h1 _ he => by
    have := h0i hu hv he
    rw [this, dist_self] at h1
    linarith)
  -- uniform closeness of `F_t` and `F₀`
  set ε : ℝ := min (m / 3) (ε₀ / 3) with hε
  have hεpos : 0 < ε := lt_min (by positivity) (by positivity)
  have hev := Metric.tendstoUniformlyOn_iff.mp hunif ε hεpos
  obtain ⟨τ₁, hτ₁, hτ₁s⟩ := (mem_nhdsGT_iff_exists_Ioo_subset).mp hev
  refine ⟨min τ₀ ((τ₁ : ℝ) / 2), ⟨lt_min hτ₀ (by have : (0 : ℝ) < τ₁ := hτ₁; linarith), min_le_left _ _⟩,
    fun t ht z hz z' hz' hzz => ?_⟩
  have htτ₀ : t ∈ Ioc 0 τ₀ := ⟨ht.1, ht.2.trans (min_le_left _ _)⟩
  have hclose : ∀ w ∈ D, dist (F₀ w) (F t w) < ε := by
    have : t ∈ Ioo 0 τ₁ := ⟨ht.1, ht.2.trans_lt ((min_le_right _ _).trans_lt (by have : (0 : ℝ) < τ₁ := hτ₁; linarith))⟩
    exact hτ₁s this
  -- `z, z'` are close
  have hFz : ‖F₀ z - F₀ z'‖ < ε₀ := by
    have h1 := hclose z hz
    have h2 := hclose z' hz'
    rw [dist_eq_norm] at h1 h2
    have : F₀ z - F₀ z' = (F₀ z - F t z) - (F₀ z' - F t z') := by rw [hzz]; ring
    rw [this]
    calc ‖(F₀ z - F t z) - (F₀ z' - F t z')‖ ≤ ‖F₀ z - F t z‖ + ‖F₀ z' - F t z'‖ := norm_sub_le _ _
      _ < ε + ε := add_lt_add h1 h2
      _ ≤ ε₀ / 3 + ε₀ / 3 := add_le_add (min_le_right _ _) (min_le_right _ _)
      _ < ε₀ := by linarith
  have hzz' : dist z z' < κ := by
    by_contra hcon
    rw [not_lt] at hcon
    have hd3 : dist z z' ≤ 3 := by
      have h1 : dist z 0 ≤ 1 := mem_closedBall.mp hz
      have h2 : dist 0 z' ≤ 1 := by rw [dist_comm]; exact mem_closedBall.mp hz'
      linarith [dist_triangle z 0 z']
    exact absurd (hsepF z hz z' hz' hcon hd3) (not_le.mpr hFz)
  -- `F_t` moves little along the segment `[z, z']`
  set γ : ℝ → ℂ := fun l => z + (l : ℂ) * (z' - z) with hγ
  have hγD : ∀ l ∈ Icc (0 : ℝ) 1, γ l ∈ D := by
    intro l hl
    have := hDconv.add_smul_sub_mem hz hz' hl
    simpa [γ, smul_eq_mul] using this
  have hγz : ∀ l ∈ Icc (0 : ℝ) 1, dist (γ l) z < κ := by
    intro l hl
    have he : γ l - z = (l : ℂ) * (z' - z) := by simp [γ]
    rw [dist_eq_norm, he, norm_mul, Complex.norm_real, Real.norm_of_nonneg hl.1, ← dist_eq_norm,
      dist_comm]
    exact lt_of_le_of_lt (mul_le_of_le_one_left dist_nonneg hl.2) hzz'
  have hsmall : ∀ l ∈ Icc (0 : ℝ) 1, ‖F t (γ l) - F t z‖ < m := by
    intro l hl
    have h1 := hclose (γ l) (hγD l hl)
    have h2 := hclose z hz
    have h3 := hucF (γ l) (hγD l hl) z hz (hγz l hl)
    rw [dist_eq_norm] at h1 h2 h3
    have : F t (γ l) - F t z = (F₀ (γ l) - F₀ z) - (F₀ (γ l) - F t (γ l)) + (F₀ z - F t z) := by ring
    rw [this]
    calc ‖(F₀ (γ l) - F₀ z) - (F₀ (γ l) - F t (γ l)) + (F₀ z - F t z)‖
        ≤ ‖F₀ (γ l) - F₀ z‖ + ‖F₀ (γ l) - F t (γ l)‖ + ‖F₀ z - F t z‖ :=
          (norm_add_le _ _).trans
            (by linarith [norm_sub_le (F₀ (γ l) - F₀ z) (F₀ (γ l) - F t (γ l))])
      _ < m / 3 + ε + ε := by linarith
      _ ≤ m / 3 + m / 3 + m / 3 := by linarith [min_le_left (m / 3) (ε₀ / 3)]
      _ = m := by ring
  -- the image of the segment under `φ_t` stays within `η/2` of `φ_t z`
  have hφK : ∀ w ∈ D, φ t w ∈ K := fun w hw => hφm t htτ₀ hw
  by_contra hne
  have hφne : φ t z ≠ φ t z' := fun h => hne (hφi t htτ₀ hz hz' h)
  by_cases hfar : dist (φ t z') (φ t z) < η
  · apply hφne
    refine (hinjG _ (hφK z hz) _ (hφK z' hz') (by rw [dist_comm]; exact hfar) ?_)
    rw [← hfac t htτ₀ z hz, ← hfac t htτ₀ z' hz', hzz]
  · rw [not_lt] at hfar
    -- intermediate value: some point of the segment has `φ_t`-distance exactly `η/2` from `φ_t z`
    have hcont : ContinuousOn (fun l : ℝ => dist (φ t (γ l)) (φ t z)) (Icc 0 1) := by
      have hγc : Continuous γ := by fun_prop
      have hc1 : ContinuousOn (fun l => φ t (γ l)) (Icc 0 1) :=
        (hφc t htτ₀).comp hγc.continuousOn (fun l hl => hγD l hl)
      exact (hc1.sub continuousOn_const).norm.congr fun l _ => dist_eq_norm _ _
    have h0 : (fun l : ℝ => dist (φ t (γ l)) (φ t z)) 0 = 0 := by simp [γ]
    have h1 : (fun l : ℝ => dist (φ t (γ l)) (φ t z)) 1 = dist (φ t z') (φ t z) := by simp [γ]
    obtain ⟨l, hl, hlv⟩ := intermediate_value_Icc zero_le_one hcont
      (show η / 2 ∈ Icc ((fun l : ℝ => dist (φ t (γ l)) (φ t z)) 0)
        ((fun l : ℝ => dist (φ t (γ l)) (φ t z)) 1) by
        rw [h0, h1]
        exact ⟨by linarith, by linarith⟩)
    have hsep := hsepG _ (hφK _ (hγD l hl)) _ (hφK z hz) hlv.ge hlv.le
    rw [← hfac t htτ₀ _ (hγD l hl), ← hfac t htτ₀ z hz] at hsep
    exact absurd (hsmall l hl) (not_lt.mpr hsep)


end TakhtajanTeo

