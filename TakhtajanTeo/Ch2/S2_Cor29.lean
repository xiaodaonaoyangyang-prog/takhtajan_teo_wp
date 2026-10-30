import TakhtajanTeo.Ch2.S1_Theorem112Completed
import TakhtajanTeo.Ch2.FaberBoundary
import TakhtajanTeo.Ch2.S2_Completed
import TakhtajanTeo.Ch2.S2_Thm26

/-!
# Corollary 2.9: `B₁`, `B₄` are Hilbert–Schmidt iff `[μ] ∈ T₀(1)`

`T₀(1) ⇒ HS` is Theorem 2.6 (`thm_2_6`, the trace-class kernels) through Lemma 2.5. `HS ⇒ T₀(1)`: for `B₁`, Lemma 2.5
gives `𝒮(𝖿^μ) ∈ A₂(𝔻)` and Theorem 1.12 (i) concludes; for `B₄`, `B₄([μ]) = \overline{B₁([μ]⁻¹)}` (Remark 5.7) reduces
it to `B₁` at `[μ]⁻¹`.
-/

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal ComplexConjugate Classical Real
noncomputable section
namespace TakhtajanTeo
open LiZhongQC
namespace Ch2

theorem s29_norm_sq (x : ℝ) (hx : 0 ≤ x) (c : ℂ) : ‖(Real.sqrt x : ℂ) * c‖ ^ 2 = x * ‖c‖ ^ 2 := by
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg x), mul_pow,
    Real.sq_sqrt hx]

/-- The `B₁` half of Corollary 2.9, at every point. -/
theorem s29_B1 (p : T1) :
    let b := grunsky (fsans (Quotient.out p : LinfStarBall)) (gsans (Quotient.out p : LinfStarBall))
    p ∈ T01 ↔ Summable fun q : ℕ × ℕ => ‖B1 b q.1 q.2‖ ^ 2 := by
  intro b
  have hμ := (Quotient.out p : LinfStarBall).2
  have L := s2c_lemma_2_5 (AppB.b8_welding_normalized_pair hμ) (r22_complement_null hμ)
  have hs : (Summable fun q : ℕ × ℕ => ‖B1 b q.1 q.2‖ ^ 2) ↔
      Summable fun q : ℕ × ℕ => ((q.1 + 1) * (q.2 + 1) : ℝ) * ‖b (-(q.1 + 1 : ℤ)) (-(q.2 + 1 : ℤ))‖ ^ 2 := by
    refine summable_congr (fun q => ?_)
    unfold B1
    exact s29_norm_sq _ (by positivity) _
  rw [hs]
  constructor
  · intro hp
    exact L.1.mp (thm_2_6 hp).1
  · intro hsum
    exact ((thm_1_12 p).1).mpr (L.2.1 (L.1.mpr hsum)).2.2

/-- **Corollary 2.9** (TT:4188). The Grunsky operators `B₁`, `B₄` of `(𝖿^μ, 𝗀_μ)`, `[μ] ∈ T(1)`, are Hilbert–Schmidt iff
`[μ] ∈ T₀(1)`. -/
theorem s29_cor_2_9 (p : T1) :
    let b := grunsky (fsans (Quotient.out p : LinfStarBall)) (gsans (Quotient.out p : LinfStarBall))
    (p ∈ T01 ↔ Summable fun q : ℕ × ℕ => ‖B1 b q.1 q.2‖ ^ 2) ∧ (p ∈ T01 ↔ Summable fun q : ℕ × ℕ => ‖B4 b q.1 q.2‖ ^ 2) := by
  intro b
  refine ⟨s29_B1 p, ?_⟩
  have hμ := (Quotient.out p : LinfStarBall).2
  have L := s2c_lemma_2_5 (AppB.b8_welding_normalized_pair hμ) (r22_complement_null hμ)
  constructor
  · intro hp
    have h4 := L.2.2.2.mp (thm_2_6 hp).2
    refine (summable_congr (fun q => ?_)).mpr h4
    unfold B4
    exact s29_norm_sq _ (by positivity) _
  · intro hsum
    have hc := FB.fb_clause3 p
    have hinv : Summable fun q : ℕ × ℕ => ‖periodP (invT p) q.1 q.2‖ ^ 2 := by
      refine (summable_congr (fun q => ?_)).mp hsum
      rw [hc q.1 q.2, norm_conj]
    have hT := (s29_B1 (invT p)).mpr hinv
    have h2 := TakhtajanTeo.lemma_3_4.2.2 _ hT
    rwa [grp_invT_invT] at h2

/-- **Corollary 2.9** (TT:4188). The Grunsky operators `B₁`, `B₄` of `(𝖿^μ, 𝗀_μ)`, `[μ] ∈ T(1)`, are Hilbert–Schmidt iff
`[μ] ∈ T₀(1)`. -/
theorem cor_2_9 (p : T1) :
    let b := grunsky (fsans (Quotient.out p : LinfStarBall)) (gsans (Quotient.out p : LinfStarBall))
    (p ∈ T01 ↔ Summable fun q : ℕ × ℕ => ‖B1 b q.1 q.2‖ ^ 2) ∧ (p ∈ T01 ↔ Summable fun q : ℕ × ℕ => ‖B4 b q.1 q.2‖ ^ 2) :=
  s29_cor_2_9 p

end Ch2
end TakhtajanTeo
