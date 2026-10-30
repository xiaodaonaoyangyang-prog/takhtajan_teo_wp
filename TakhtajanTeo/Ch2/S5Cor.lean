import TakhtajanTeo.Ch2.S5Prop51
import TakhtajanTeo.Ch2.S2_Cor29
import TakhtajanTeo.Ch2.S2_DetF
import TakhtajanTeo.Ch2.S2_Eq212

/-!
# Corollaries 5.2, 5.4 and Remark 5.5 (Program G, 下属6)

By Proposition 5.1, `Z = B₁` is a bounded solution of `Z𝔄̄ = 𝔅` (using `B₁ = B₁ᵗ`), and `𝔄̄` has the bounded right
inverse `B₃`, so every bounded solution equals `𝔅B₃`. Hence `Π([μ]) = B₁ = 𝒫̂([μ])` (`s5c_kyns_eq`); Corollary 5.4
is then Corollary 2.9, and Remark 5.5 is the definition of `S₂` through `detF`.
-/

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal NNReal ComplexConjugate Classical Real

noncomputable section

namespace TakhtajanTeo.Ch2

open LiZhongQC

/-- Two bounded solutions of `Y X = B`, where `X` has a bounded right inverse, coincide. -/
theorem s5c_unique {Z Z' X B R : ℕ → ℕ → ℂ} (hZ : IsBoundedMat Z) (hZ' : IsBoundedMat Z') (hX : IsBoundedMat X)
    (hB : IsBoundedMat B) (h : ∀ m n, mulMat Z X m n = B m n) (h' : ∀ m n, mulMat Z' X m n = B m n)
    (hinv : gopOp X * gopOp R = 1) : Z = Z' := by
  have e (Y : ℕ → ℕ → ℂ) (hY : IsBoundedMat Y) (hYe : ∀ m n, mulMat Y X m n = B m n) :
      gopOp Y = gopOp B * gopOp R := by
    rw [← s5p51_op_mul hY hX hB hYe, mul_assoc, hinv, mul_one]
  funext m n
  rw [← pmb_entry hZ, ← pmb_entry hZ', e Z hZ h, e Z' hZ' h']

/-- The KYNS period mapping is `B₁`: `Π([μ]) = 𝒫̂([μ])`. -/
theorem s5c_kyns_eq (p : T1) : kyns p = periodP p := by
  have hμ : ((Quotient.out p : LinfStarBall) : LinfStar) ∈ LinfStarBall := (Quotient.out p : LinfStarBall).2
  have hγ : IsQSCircleHomeo (wA ((Quotient.out p : LinfStarBall) : LinfStar)) :=
    ⟨wA_circle_sensePreserving hμ, wA_circle_quasisymmetric hμ⟩
  obtain ⟨-, hB, -, hAc⟩ := s5ca_bounded_matrices hγ
  obtain ⟨-, -, h3, -, -, -, -⟩ := s5p51_grunsky_facts hμ
  have P := prop_5_1 p
  simp only at P
  obtain ⟨-, c2, c3, -⟩ := P
  obtain ⟨hsym, hZ, -⟩ := pgb_period_siegel p
  have hinv := s5p51_op_one hAc h3 fun m n => (c2 m n).2
  have hsol : ∀ m n, mulMat (periodP p) (fun k l => conj (matA (wA ((Quotient.out p : LinfStarBall) : LinfStar)) k l))
      m n = matB (wA ((Quotient.out p : LinfStarBall) : LinfStar)) m n := by
    intro m n
    rw [← c3 n m]
    unfold mulMat
    apply tsum_congr
    intro k
    rw [hsym m k, mul_comm]
    rfl
  simp only [kyns]
  split_ifs with h
  · exact s5c_unique h.choose_spec.1 hZ hAc hB h.choose_spec.2 hsol hinv
  · exact absurd ⟨_, hZ, hsol⟩ h

/-- **Corollary 5.2** (TT:5612). The KYNS period mapping coincides with `𝒫̂` of Remark 2.11: `Π([μ]) = B₁(𝖿^μ)` for
every `[μ] ∈ T(1)`. It takes values in the Siegel disk. -/
theorem s5c_cor_5_2 (p : T1) : kyns p = periodP p ∧ kyns p ∈ siegelDisk := by
  rw [s5c_kyns_eq]
  exact ⟨rfl, pgb_period_siegel p⟩

/-- **Corollary 5.4** (TT:5628). `Π([μ]) ∈ 𝔇_∞⁰` iff `[μ] ∈ T₀(1)`. -/
theorem s5c_cor_5_4 (p : T1) : kyns p ∈ siegelDisk0 ↔ p ∈ T01 := by
  rw [s5c_kyns_eq]
  constructor
  · intro h
    exact ((cor_2_9 p).1).mpr h.2
  · intro hp
    exact ⟨pgb_period_siegel p, ((cor_2_9 p).1).mp hp⟩

/-- **Remark 5.5** (TT:5636–5648). On `T₀(1)`, `S₂ = log Det(I - ZZ̄)` with `Z = Π₀([μ])`: the Fredholm determinant
`∏ (1 - λ_n²)` over the singular values of `Z`. So the pull-back by `Π₀` of the Kähler metric of `𝔇_∞⁰` with potential
`log Det(I - ZZ̄)` is a constant multiple of the Weil–Petersson metric. -/
theorem s5c_remark_5_5 {p : T1} (hp : p ∈ T01) :
    (∃ lam, IsSingularSeq (kyns p) lam) ∧
      ∀ lam, IsSingularSeq (kyns p) lam → liouvilleS2 p = Real.log (∏' n, (1 - lam n ^ 2)) := by
  rw [s5c_kyns_eq]
  have hD := detF_spec hp
  simp only at hD
  obtain ⟨lam, hl, -⟩ := eq_2_12 hp
  refine ⟨⟨lam, hl⟩, fun lam' hl' => ?_⟩
  rw [(hD.2.1 lam' hl').2]
  rfl

/-- **Corollary 5.2** (TT:5612). The KYNS period mapping coincides with `𝒫̂` of Remark 2.11: `Π([μ]) = B₁(𝖿^μ)` for
every `[μ] ∈ T(1)`. It takes values in the Siegel disk. -/
theorem cor_5_2 (p : T1) : kyns p = periodP p ∧ kyns p ∈ siegelDisk := by
  exact s5c_cor_5_2 p

/-- **Corollary 5.4** (TT:5628). `Π([μ]) ∈ 𝔇_∞⁰` iff `[μ] ∈ T₀(1)`. -/
theorem cor_5_4 (p : T1) : kyns p ∈ siegelDisk0 ↔ p ∈ T01 := by
  exact s5c_cor_5_4 p

/-- **Remark 5.5** (TT:5636–5648). On `T₀(1)`, `S₂ = log Det(I - ZZ̄)` with `Z = Π₀([μ])`: the Fredholm determinant
`∏ (1 - λ_n²)` over the singular values of `Z`. So the pull-back by `Π₀` of the Kähler metric of `𝔇_∞⁰` with potential
`log Det(I - ZZ̄)` is a constant multiple of the Weil–Petersson metric. -/
theorem remark_5_5 {p : T1} (hp : p ∈ T01) :
    (∃ lam, IsSingularSeq (kyns p) lam) ∧
      ∀ lam, IsSingularSeq (kyns p) lam → liouvilleS2 p = Real.log (∏' n, (1 - lam n ^ 2)) := by
  exact s5c_remark_5_5 hp

end TakhtajanTeo.Ch2
