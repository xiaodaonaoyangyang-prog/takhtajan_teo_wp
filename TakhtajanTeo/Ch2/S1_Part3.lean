import TakhtajanTeo.Ch2.S1_UnivalentFunctions
import TakhtajanTeo.Ch1.HomogeneousCompleted
import TakhtajanTeo.Ch1.FiberSphereWelding

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal ComplexConjugate Classical Real

noncomputable section

namespace TakhtajanTeo

open LiZhongQC

namespace Ch2

/-! ## Ch2 §1 items proved downstream of `S1_UnivalentFunctions` (`w3_` prefix) -/

theorem w3_bers_curve_factorization {μ : LinfStar} (hμ : μ ∈ LinfStarBall) {w : ℂ}
    (hw : w ∈ unitDiscExterior) :
    let f : ℂ → ℂ := fun z => lambdaW (-1 / gMu μ w) (fB μ z)
    (∀ z ∈ unitDisc, PsiOp (preSchwarzian f) z = AInf.toFun (bersPhi μ) z) ∧
      (1 / 2) * preSchwarzian f 0 = (1 / 2) * deriv (deriv (fB μ)) 0 + 1 / gMu μ w := by
  intro f
  set c : ℂ := -1 / gMu μ w with hc
  obtain ⟨hd, hi⟩ := fB_holomorphic_injective hμ
  have hden : ∀ z ∈ unitDisc, c * fB μ z + 1 ≠ 0 := fun z hz =>
    (fiberWeldingExterior_closed_identity hμ hw (ball_subset_closedBall hz)).2
  refine ⟨fun z hz => ?_, ?_⟩
  · have han : AnalyticAt ℂ (fB μ) z := hd.analyticAt (isOpen_ball.mem_nhds hz)
    have hder : deriv (fB μ) z ≠ 0 := deriv_ne_zero_of_injOn isOpen_ball hd hi hz
    have hfeq : f = fun w => (1 * fB μ w + 0) / (c * fB μ w + 1) := by
      funext v; simp only [f, lambdaW, one_mul, add_zero, hc]
    have hfan : AnalyticAt ℂ f z := by
      rw [hfeq]
      exact ((analyticAt_const.mul han).add analyticAt_const).div
        ((analyticAt_const.mul han).add analyticAt_const) (hden z hz)
    have h1 := schwarzian_mobius_comp_of_ne han hder (a := 1) (b := 0) (c := c) (d := 1)
      (by norm_num) (by simpa using hden z hz)
    have h2 : schwarzianHol f z = schwarzianHol (fB μ) z := by
      rw [← schwarzian_of_analyticAt hfan, ← schwarzian_of_analyticAt han, hfeq]
      exact h1
    calc PsiOp (preSchwarzian f) z = schwarzianHol f z := rfl
      _ = schwarzianHol (fB μ) z := h2
      _ = AInf.toFun (bersPhi μ) z := ((bersPhi_spec hμ).1 z hz).symm
  · obtain ⟨-, -, hcc⟩ := fiber_welding hμ hw
    obtain ⟨hF0, hF1, -⟩ := fB_normalization μ
    have hd0 : DifferentiableAt ℂ (fB μ) 0 :=
      hd.differentiableAt (isOpen_ball.mem_nhds (by simp [unitDisc]))
    have hfd : deriv f 0 = 1 := by
      have hne : c * fB μ 0 + 1 ≠ 0 := by rw [hF0]; simp
      have hl : HasDerivAt (fun v : ℂ => v / (c * v + 1)) (1 / (c * (fB μ 0) + 1) ^ 2) (fB μ 0) := by
        have h := (hasDerivAt_id' (fB μ 0)).div
          (((hasDerivAt_id' (fB μ 0)).const_mul c).add_const 1) hne
        convert h using 1
        rw [hF0]; simp
      have hcomp := hl.comp 0 hd0.hasDerivAt
      have : deriv f 0 = 1 / (c * fB μ 0 + 1) ^ 2 * deriv (fB μ) 0 := by
        change deriv (fun z => lambdaW c (fB μ z)) 0 = _
        exact hcomp.deriv
      rw [this, hF0, hF1]; simp
    have hcc' : c = -(1 / 2) * (deriv (deriv f) 0 - deriv (deriv (fB μ)) 0) / deriv f 0 := hcc
    rw [hfd] at hcc'
    have hA : preSchwarzian f 0 = deriv (deriv f) 0 := by
      simp [preSchwarzian, hfd]
    rw [hA]
    have hg : 1 / gMu μ w = -c := by rw [hc]; ring
    rw [hg]
    have : deriv (deriv f) 0 = deriv (deriv (fB μ)) 0 - 2 * c := by
      field_simp at hcc'
      linear_combination hcc'
    rw [this]; ring

/-- A `C¹` circle diffeomorphism lift with positive derivative is asymptotically symmetric. -/
theorem w3_asym_of_C1 {u : ℝ → ℝ} (hu : ContDiff ℝ 1 u) (hpos : ∀ t, 0 < deriv u t)
    (hper : ∀ t, u (t + 2 * π) = u t + 2 * π) :
    ∀ ε > 0, ∃ δ > 0, ∀ x t : ℝ, 0 < t → t < δ →
      |(u (x + t) - u x) / (u x - u (x - t)) - 1| < ε := by
  have hdiff : ∀ x, HasDerivAt u (deriv u x) x := fun x => (hu.differentiable one_ne_zero x).hasDerivAt
  have hc : Continuous (deriv u) := hu.continuous_deriv le_rfl
  have hperd : Function.Periodic (deriv u) (2 * π) := by
    intro t
    have h1 : (fun s => u (s + 2 * π)) = fun s => u s + 2 * π := funext hper
    have h2 : deriv (fun s => u (s + 2 * π)) t = deriv u (t + 2 * π) := deriv_comp_add_const _ _ _
    rw [← h2, h1, deriv_add_const]
  have h2π : (2 * π) ≠ 0 := by positivity
  have hK : IsCompact (Set.range (deriv u)) := hperd.compact_of_continuous h2π hc
  obtain ⟨y, ⟨t₀, rfl⟩, hy⟩ := hK.exists_isMinOn (Set.range_nonempty _) continuous_id.continuousOn
  set m : ℝ := deriv u t₀ with hm
  have hm0 : 0 < m := hpos t₀
  have hlow : ∀ t, m ≤ deriv u t := fun t => hy ⟨t, rfl⟩
  have huc : ∀ ε' > 0, ∃ η > 0, ∀ a b : ℝ, dist a b < η → |deriv u a - deriv u b| < ε' := by
    intro ε' hε'
    have hcpt : UniformContinuousOn (deriv u) (Set.Icc (-(2 * π)) (4 * π)) :=
      isCompact_Icc.uniformContinuousOn_of_continuous hc.continuousOn
    obtain ⟨η0, hη0, h0⟩ := Metric.uniformContinuousOn_iff.mp hcpt ε' hε'
    refine ⟨min η0 π, lt_min hη0 Real.pi_pos, fun a b hab => ?_⟩
    have hab1 : dist a b < η0 := lt_of_lt_of_le hab (min_le_left _ _)
    have hab2 : dist a b < π := lt_of_lt_of_le hab (min_le_right _ _)
    set k : ℤ := ⌊a / (2 * π)⌋ with hk
    have hk1 : (k : ℝ) ≤ a / (2 * π) := Int.floor_le _
    have hk2 : a / (2 * π) < k + 1 := Int.lt_floor_add_one _
    have hπ : 0 < 2 * π := by positivity
    have e1 : (k : ℝ) * (2 * π) ≤ a := by
      have := (le_div_iff₀ hπ).mp hk1; linarith
    have e2 : a < ((k : ℝ) + 1) * (2 * π) := by
      have := (div_lt_iff₀ hπ).mp hk2; linarith
    have ha' : a - k * (2 * π) ∈ Set.Icc (-(2 * π)) (4 * π) := ⟨by linarith, by nlinarith⟩
    have hdab : |a - b| < π := by rwa [Real.dist_eq] at hab2
    have hb' : b - k * (2 * π) ∈ Set.Icc (-(2 * π)) (4 * π) := by
      rw [abs_lt] at hdab
      constructor <;> nlinarith [Real.pi_pos]
    have := h0 _ ha' _ hb' (by rw [Real.dist_eq]; rw [Real.dist_eq] at hab1; convert hab1 using 2; ring)
    rw [Real.dist_eq] at this
    rwa [hperd.sub_int_mul_eq, hperd.sub_int_mul_eq] at this
  intro ε hε
  obtain ⟨η, hη, hηc⟩ := huc (ε * m) (by positivity)
  refine ⟨η / 2, by positivity, fun x t ht0 htδ => ?_⟩
  obtain ⟨ξ₁, hξ₁, e₁⟩ := exists_hasDerivAt_eq_slope u (deriv u) (by linarith : x < x + t)
    hu.continuous.continuousOn (fun s _ => hdiff s)
  obtain ⟨ξ₂, hξ₂, e₂⟩ := exists_hasDerivAt_eq_slope u (deriv u) (by linarith : x - t < x)
    hu.continuous.continuousOn (fun s _ => hdiff s)
  have hx1 : x + t - x = t := by ring
  have hx2 : x - (x - t) = t := by ring
  rw [hx1] at e₁
  rw [hx2] at e₂
  have n1 : u (x + t) - u x = deriv u ξ₁ * t := by rw [e₁]; field_simp
  have n2 : u x - u (x - t) = deriv u ξ₂ * t := by rw [e₂]; field_simp
  have hd2 : 0 < deriv u ξ₂ := hpos ξ₂
  have hdist : dist ξ₁ ξ₂ < η := by
    rw [Real.dist_eq, abs_lt]
    constructor <;> linarith [hξ₁.1, hξ₁.2, hξ₂.1, hξ₂.2]
  have hclose := hηc ξ₁ ξ₂ hdist
  rw [n1, n2, mul_div_mul_right _ _ ht0.ne', div_sub_one hd2.ne', abs_div, abs_of_pos hd2]
  rw [div_lt_iff₀ hd2]
  calc |deriv u ξ₁ - deriv u ξ₂| < ε * m := hclose
    _ ≤ ε * deriv u ξ₂ := by gcongr; exact hlow ξ₂

/-- **Remark 1.9**, clause 1 (TT:3660): `C¹` circle diffeomorphisms are symmetric. -/
theorem w3_remark_1_9_clause1 (p : T1) :
    (∃ u : ℝ → ℝ, ContDiff ℝ 1 u ∧ (∀ t, 0 < deriv u t) ∧ (∀ t, u (t + 2 * π) = u t + 2 * π) ∧
        ∀ t : ℝ, wA (Quotient.out p : LinfStarBall) (exp (t * I)) = exp (u t * I)) → p ∈ symmetricT := by
  rintro ⟨u, hu, hpos, hper, hh⟩
  refine ⟨u, hu.continuous, strictMono_of_deriv_pos hpos, hper, hh, w3_asym_of_C1 hu hpos hper⟩

/-! ### Original relocated (2026-10-26) -/

/-- (TT:3532–3542, [Teo04]) The Bers coordinates of `𝒯(1)` factor through `γ = g⁻¹ ∘ f ↦ 𝒜(f) ∈ A∞¹(𝔻)` followed by
`ψ ↦ (ψ_z - ½ψ², ½ψ(0))`.
- At `([μ], g_μ(w))` the welding function is `f = λ_w ∘ f^μ` (`fiber_welding`).
- `Ψ(𝒜(f)) = 𝒮(f) = β([μ])` on `𝔻`, and `½𝒜(f)(0) = ½(f^μ)''(0) + 1/g_μ(w)`.

[CORRECTION 2026-10-25] Model B is now normalized by `w^μ(∞) = ∞` (user-approved), so `(f^μ)''(0)` need not vanish.
Under TT's normalization `f''(0) = 0` the extra term is `0`, and `½𝒜(f)(0)` is the fiber coordinate `1/z`. -/
theorem bers_curve_factorization {μ : LinfStar} (hμ : μ ∈ LinfStarBall) {w : ℂ} (hw : w ∈ unitDiscExterior) :
    let f : ℂ → ℂ := fun z => lambdaW (-1 / gMu μ w) (fB μ z)
    (∀ z ∈ unitDisc, PsiOp (preSchwarzian f) z = AInf.toFun (bersPhi μ) z) ∧
      (1 / 2) * preSchwarzian f 0 = (1 / 2) * deriv (deriv (fB μ)) 0 + 1 / gMu μ w :=
  w3_bers_curve_factorization hμ hw

end Ch2

end TakhtajanTeo
