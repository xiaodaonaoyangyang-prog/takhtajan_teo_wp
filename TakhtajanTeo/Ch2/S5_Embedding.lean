import TakhtajanTeo.Ch2.FaberBoundary
import TakhtajanTeo.Ch2.S2_Cor29

/-!
# The embedding `ℰ([μ]) = W_μ` into the Segal–Wilson Grassmannian (TT:5664–5672)

`s5e_embedding_spec`: the boundary Fourier coefficients of `w_n = Q_n(𝖿^μ)/√n` on `S¹`. With `F(ζ) = Q_n(1/𝖿(1/ζ))`,
the Faber expansion on `𝔻` becomes an expansion `F(ζ) = ζⁿ + Σ_m c_m ζ^{-m}` on `𝔻*`, so the exterior boundary lemma
`FB.fb_coeff_boundary` applies; `𝖿 = f_B` is continuous on the closed disc (the pole of `w^μ` lies in the open `𝔻*`).
The last clause is Corollary 2.9.
-/

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal ComplexConjugate Classical Real
noncomputable section
namespace TakhtajanTeo
open LiZhongQC
namespace Ch2

/-- `w^μ` is finite on the closed unit disc: its pole `(w_μ)⁻¹(∞)` lies in `𝔻*`. -/
theorem s5e_wB_finite {μ : LinfStar} (hμ : μ ∈ LinfStarBall) {z : ℂ} (hz : ‖z‖ ≤ 1) :
    wB μ (z : ExtPlane) ≠ extInf := by
  intro h
  have hp := (fB_normalization μ).2.2 ⟨wB μ, (wB_spec hμ).1⟩
  have he : (z : ExtPlane) = Function.invFun (wAS μ) extInf := (wB_bijective μ).1 (h.trans hp.symm)
  have hinf : wAS μ (z : ExtPlane) = extInf := by
    rw [he]
    exact Function.invFun_eq ((wAS_bijective μ).2 extInf)
  rcases hz.lt_or_eq with h1 | h1
  · obtain ⟨u, -, hu⟩ := wAS_maps_disc hμ h1
    rw [hu] at hinf
    exact OnePoint.coe_ne_infty u hinf
  · obtain ⟨u, -, hu⟩ := wAS_maps_circle hμ h1
    rw [hu] at hinf
    exact OnePoint.coe_ne_infty u hinf

theorem s5e_fB_continuousAt {μ : LinfStar} (hμ : μ ∈ LinfStarBall) {z : ℂ} (hz : ‖z‖ ≤ 1) :
    ContinuousAt (fB μ) z := by
  obtain ⟨v, hv⟩ := grp_exists_coe (s5e_wB_finite hμ hz)
  have hfin : ContinuousAt finPart (wB μ (z : ExtPlane)) := by
    rw [hv]
    exact OnePoint.isOpenEmbedding_coe.continuousAt_iff.mp (continuousAt_id : ContinuousAt (fun x : ℂ => x) v)
  exact ContinuousAt.comp (g := finPart) (f := fun x : ℂ => wB μ (x : ExtPlane)) hfin
    ((wB_continuous hμ).comp OnePoint.continuous_coe).continuousAt

theorem s5e_fB_ne_zero {μ : LinfStar} (hμ : μ ∈ LinfStarBall) {z : ℂ} (hz : ‖z‖ ≤ 1) (hz0 : z ≠ 0) :
    fB μ z ≠ 0 := by
  intro h0
  have h00 : fB μ 0 = 0 := (fB_normalization μ).1
  have hw0 : wB μ ((0 : ℂ) : ExtPlane) ≠ extInf := s5e_wB_finite hμ (by simp)
  have e1 : wB μ (z : ExtPlane) = ((fB μ z : ℂ) : ExtPlane) := (coe_finPart_of_ne (s5e_wB_finite hμ hz)).symm
  have e2 : wB μ ((0 : ℂ) : ExtPlane) = ((fB μ 0 : ℂ) : ExtPlane) := (coe_finPart_of_ne hw0).symm
  have he : wB μ (z : ExtPlane) = wB μ ((0 : ℂ) : ExtPlane) := by rw [e1, e2, h0, h00]
  exact hz0 (OnePoint.coe_injective ((wB_bijective μ).1 he))

/-- Reflection `θ ↦ -θ` of circle Fourier coefficients. -/
theorem s5e_circleCoeff_inv (G : ℂ → ℂ) (k : ℤ) :
    circleCoeff (fun z => G z⁻¹) k = circleCoeff G (-k) := by
  unfold circleCoeff fourierCoeff
  congr 1
  set φ : ℝ → ℂ := fun t => G (exp (t * I)) * exp (-((-k : ℤ) * t * I)) with hφ
  have hl : (fun θ : ℝ => G (exp (θ * I))⁻¹ * exp (-((k : ℂ) * θ * I))) = fun θ => φ (-θ) := by
    funext θ
    simp only [hφ]
    rw [← Complex.exp_neg]
    congr 2
    · push_cast; ring
    · push_cast; ring
  have hper : Function.Periodic φ (2 * π) := by
    intro t
    simp only [hφ]
    have h1 : exp (((t + 2 * π : ℝ) : ℂ) * I) = exp ((t : ℂ) * I) := by
      rw [show (((t + 2 * π : ℝ) : ℂ) * I) = (t : ℂ) * I + 2 * π * I by push_cast; ring, Complex.exp_add,
        Complex.exp_two_pi_mul_I, mul_one]
    have h2 : exp (-(((-k : ℤ) : ℂ) * ((t + 2 * π : ℝ) : ℂ) * I)) = exp (-(((-k : ℤ) : ℂ) * (t : ℂ) * I)) := by
      rw [show -(((-k : ℤ) : ℂ) * ((t + 2 * π : ℝ) : ℂ) * I) =
          -(((-k : ℤ) : ℂ) * (t : ℂ) * I) + (k : ℤ) * (2 * π * I) by push_cast; ring,
        Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
    rw [h1, h2]
  rw [hl, intervalIntegral.integral_comp_neg]
  have h3 := hper.intervalIntegral_add_eq (-(2 * π)) 0
  simp only [neg_add_cancel, zero_add] at h3
  rw [neg_zero]
  exact h3

theorem s5e_norm_mul_sqrt (n m : ℕ) :
    (Real.sqrt (((n : ℝ) + 1) * ((m : ℝ) + 1)) : ℂ) =
      (Real.sqrt ((n : ℝ) + 1) : ℂ) * (Real.sqrt ((m : ℝ) + 1) : ℂ) := by
  rw [Real.sqrt_mul (by positivity)]; push_cast; ring

/-- (TT:5664–5672) The subspace `W_μ = ℰ([μ])`, `[μ] ∈ T₀(1)`, is spanned by `w_n = Q_n(𝖿^μ)/√n` on `S¹`, where `Q_n` are
the Faber polynomials of `(𝖿^μ, 𝗀_μ)`.
- `w_n = f_n + Σ_m √(nm) b_{-n,-m} e_m`, so `W_μ` is the graph of `B₁` over `V₊ = W₋`: `pr₊w = I`, `pr₋w = B₁`.
- `B₁` is Hilbert–Schmidt (Corollary 2.9), so `W_μ ∈ Gr(𝓗_ℂ)`.
Proved here as `s5e_embedding_spec`; statement identical to `embedding_spec`. -/
theorem s5e_embedding_spec {p : T1} (hp : p ∈ T01) {P Q : ℕ → Polynomial ℂ}
    (hPQ : IsFaber (fsans (Quotient.out p : LinfStarBall)) (gsans (Quotient.out p : LinfStarBall)) P Q) :
    let μ : LinfStar := (Quotient.out p : LinfStarBall)
    let b := grunsky (fsans μ) (gsans μ)
    let w : ℕ → ℂ → ℂ := fun n z => (Q (n + 1)).eval (fsans μ z)⁻¹ / Real.sqrt (n + 1)
    (∀ n m : ℕ, circleCoeff (w n) (-(m + 1 : ℤ)) * Real.sqrt (m + 1) = kron m n) ∧
      (∀ n m : ℕ, circleCoeff (w n) (m + 1) * Real.sqrt (m + 1) = B1 b n m) ∧ (∀ n, circleCoeff (w n) 0 = 0) ∧
      Summable fun q : ℕ × ℕ => ‖B1 b q.1 q.2‖ ^ 2 := by
  intro μ b w
  have hμ : μ ∈ LinfStarBall := (Quotient.out p : LinfStarBall).2
  have hfB : fsans μ = fB μ := e13_fsans_eq hμ
  let G : ℕ → ℂ → ℂ := fun n ζ => (Q (n + 1)).eval (fsans μ ζ⁻¹)⁻¹
  have hcoef : ∀ n : ℕ, ∀ k : ℤ, circleCoeff (G n) k =
      (if k = ((n + 1 : ℕ) : ℤ) then 1 else 0) +
        (if k < 0 then ((n + 1 : ℕ) : ℂ) * b (-(n + 1 : ℤ)) (-((k.natAbs - 1 : ℕ) + 1 : ℕ)) else 0) := by
    intro n k
    have hF : ContinuousOn (G n) {z | 1 ≤ ‖z‖} := by
      intro ζ hζ
      have hζ1 : 1 ≤ ‖ζ‖ := hζ
      have hζ0 : ζ ≠ 0 := by intro h; rw [h, norm_zero] at hζ1; linarith
      have hin : ‖ζ⁻¹‖ ≤ 1 := by rw [norm_inv]; exact inv_le_one_of_one_le₀ hζ1
      have hin0 : ζ⁻¹ ≠ 0 := inv_ne_zero hζ0
      have h1 : ContinuousAt (fun ζ : ℂ => fsans μ ζ⁻¹) ζ := by
        rw [hfB]
        exact (s5e_fB_continuousAt hμ hin).comp (continuousAt_inv₀ hζ0)
      have h2 : fsans μ ζ⁻¹ ≠ 0 := by rw [hfB]; exact s5e_fB_ne_zero hμ hin hin0
      exact ((Polynomial.continuous _).continuousAt.comp (h1.inv₀ h2)).continuousWithinAt
    have hsum : ∀ z ∈ unitDiscExterior, HasSum
        (fun m : ℕ => (((n + 1 : ℕ) : ℂ) * b (-(n + 1 : ℤ)) (-(m + 1 : ℤ))) * z ^ (-(m + 1 : ℤ)))
        (G n z - z ^ (n + 1)) := by
      intro ζ hζ
      have hζ1 : 1 < ‖ζ‖ := hζ
      have hζ0 : ζ ≠ 0 := by intro h; rw [h, norm_zero] at hζ1; linarith
      have hz : ζ⁻¹ ∈ unitDisc :=
        mem_ball_zero_iff.mpr (by rw [norm_inv]; exact inv_lt_one_of_one_lt₀ hζ1)
      have h := hPQ.2.2 n ζ⁻¹ hz (inv_ne_zero hζ0)
      convert h using 1
      · funext m
        simp only [b, μ]
        rw [inv_pow, ← zpow_natCast, ← zpow_neg]
        push_cast
        ring_nf
      · show G n ζ - ζ ^ (n + 1) = _
        rw [inv_zpow', neg_neg, show (((n : ℤ) + 1)) = ((n + 1 : ℕ) : ℤ) by push_cast; rfl, zpow_natCast]
    have := FB.fb_coeff_boundary hF hsum k
    rw [this]
    congr 2
  have hw : ∀ n : ℕ, ∀ k : ℤ, circleCoeff (w n) k = circleCoeff (G n) (-k) / (Real.sqrt (n + 1) : ℝ) := by
    intro n k
    have he : w n = fun z => (fun ζ => G n ζ⁻¹) z / (Real.sqrt (n + 1) : ℝ) := by
      funext z
      simp only [w, G, inv_inv]
    rw [he, circleCoeff_div_const, s5e_circleCoeff_inv]
  have hsq : ∀ n : ℕ, (Real.sqrt ((n : ℝ) + 1) : ℂ) ≠ 0 := fun n => by
    exact_mod_cast (Real.sqrt_pos.2 (by positivity)).ne'
  refine ⟨fun n m => ?_, fun n m => ?_, fun n => ?_, (s29_cor_2_9 p).1.mp hp⟩
  · rw [hw, hcoef]
    have h0 : ¬ (-(-((m : ℤ) + 1)) < 0) := by omega
    simp only [h0, if_false, add_zero]
    unfold kron
    by_cases hmn : m = n
    · subst hmn
      have hk : -(-((m : ℤ) + 1)) = ((m + 1 : ℕ) : ℤ) := by push_cast; ring
      rw [if_pos hk, if_pos rfl]
      exact div_mul_cancel₀ _ (hsq m)
    · have : ¬ (-(-((m : ℤ) + 1)) = ((n + 1 : ℕ) : ℤ)) := by omega
      simp [hmn]
  · rw [hw, hcoef]
    have h1 : ¬ (-((m : ℤ) + 1) = ((n + 1 : ℕ) : ℤ)) := by omega
    have h2 : -((m : ℤ) + 1) < 0 := by omega
    have h3 : (-((m : ℤ) + 1)).natAbs - 1 = m := by omega
    have hneg : -(((m + 1 : ℕ) : ℤ)) = -((m : ℤ) + 1) := by push_cast; rfl
    rw [show ((m : ℤ) + 1 : ℤ) = ((m + 1 : ℕ) : ℤ) by push_cast; rfl, hneg]
    simp only [h1, h2, if_false, if_true, zero_add, h3]
    unfold B1
    rw [s5e_norm_mul_sqrt]
    have hn2 : (((n + 1 : ℕ) : ℂ)) = (Real.sqrt ((n : ℝ) + 1) : ℂ) ^ 2 := by
      rw [← Complex.ofReal_pow, Real.sq_sqrt (by positivity)]; push_cast; ring
    have hb : b (-((n : ℤ) + 1)) (-(((m : ℕ) + 1 : ℕ) : ℤ)) = b (-((n : ℤ) + 1)) (-((m : ℤ) + 1)) := by
      push_cast; rfl
    rw [hn2, hb]
    have hs1 := hsq n
    field_simp
  · rw [hw, hcoef]
    have h1 : ¬ ((-(0 : ℤ)) = ((n + 1 : ℕ) : ℤ)) := by omega
    have h2 : ¬ ((-(0 : ℤ)) < 0) := by omega
    simp only [h1, h2, if_false, add_zero, zero_div]

/-- (TT:5664–5672) The subspace `W_μ = ℰ([μ])`, `[μ] ∈ T₀(1)`, is spanned by `w_n = Q_n(𝖿^μ)/√n` on `S¹`, where `Q_n` are
the Faber polynomials of `(𝖿^μ, 𝗀_μ)`.
- `w_n = f_n + Σ_m √(nm) b_{-n,-m} e_m`, so `W_μ` is the graph of `B₁` over `V₊ = W₋`: `pr₊w = I`, `pr₋w = B₁`.
- `B₁` is Hilbert–Schmidt (Corollary 2.9), so `W_μ ∈ Gr(𝓗_ℂ)`. -/
theorem embedding_spec {p : T1} (hp : p ∈ T01) {P Q : ℕ → Polynomial ℂ}
    (hPQ : IsFaber (fsans (Quotient.out p : LinfStarBall)) (gsans (Quotient.out p : LinfStarBall)) P Q) :
    let μ : LinfStar := (Quotient.out p : LinfStarBall)
    let b := grunsky (fsans μ) (gsans μ)
    let w : ℕ → ℂ → ℂ := fun n z => (Q (n + 1)).eval (fsans μ z)⁻¹ / Real.sqrt (n + 1)
    (∀ n m : ℕ, circleCoeff (w n) (-(m + 1 : ℤ)) * Real.sqrt (m + 1) = kron m n) ∧
      (∀ n m : ℕ, circleCoeff (w n) (m + 1) * Real.sqrt (m + 1) = B1 b n m) ∧ (∀ n, circleCoeff (w n) 0 = 0) ∧
      Summable fun q : ℕ × ℕ => ‖B1 b q.1 q.2‖ ^ 2 :=
  s5e_embedding_spec hp hPQ

end Ch2
end TakhtajanTeo
