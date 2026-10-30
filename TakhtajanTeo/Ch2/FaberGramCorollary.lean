import TakhtajanTeo.Ch2.FaberGramBlocks
import TakhtajanTeo.Ch2.FaberGramInversion

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal ComplexConjugate Classical Real
noncomputable section
namespace TakhtajanTeo.Ch2
open LiZhongQC

/-- The first remaining block identity in the original Corollary 2.16. -/
theorem cor_2_16_block_positive {f g : ℂ → ℂ} (h : IsNormalizedDisjointPair f g)
    (hF : volume ((f '' unitDisc ∪ g '' unitDiscExterior)ᶜ)=0)
    {P Q : ℕ → Polynomial ℂ} (hPQ : IsFaber f g P Q) (m n : ℕ) :
    mulAdj (B3 (grunsky f g)) (B3 (grunsky f g)) m n=
      kron m n-mulAdj (B4 (grunsky f g)) (B4 (grunsky f g)) m n := by
  obtain ⟨φ,b,hφd,hφi,hφ0,hφ1,hb,hbg,hg⟩ := g1_inverted_exterior h
  obtain ⟨d,hd0,hd'⟩ := disk_axis_coefficients_exist hφd hφi hφ1 0
  have hd : ∀ s∈unitDisc, ∃ S : ℂ, HasSum (fun j => d j*s^j) S ∧ exp (-S)=dslope φ 0 s := by
    intro s hs
    simpa only [zero_sub] using hd' s hs
  obtain ⟨η,hη,hη0⟩ := g2_phi_exists hφd hφ0
  let a := faberFillAxes (fun j k => grunsky f g (j+1) (k+1)) d
  have hsym : ∀ j k, a j k=a k j :=
    faberFillAxes_symm d (fun j k => ((grunsky_spec h).2 j k).1)
  have hexp := faber_inverted_full_series h hφd hφi hφ0 hφ1 hb hbg hg hd
  have hG := faber_polynomial_gram_complement hφd hφi hφ0 hsym hexp hη hη0 m n
  have hPm := hPQ.positive_polynomial_eq h hφd hφi hφ0 hφ1 hb hbg hg hd hη hη0 m
  have hPn := hPQ.positive_polynomial_eq h hφd hφi hφ0 hφ1 hb hbg hg hd hη hη0 n
  have hT := faber_scaled_gram_complement hφd hφi hφ0 hb hg hPm hPn
    (Real.sqrt (π*((m : ℝ)+1))) (Real.sqrt (π*((n : ℝ)+1)))
  have hF' : volume ((g '' unitDiscExterior ∪ f '' unitDisc)ᶜ)=0 := by
    simpa only [union_comm] using hF
  have hM := faber_complement_measure h.2.2.2.2.2.symm hF'
  rw [hM] at hT
  rw [← cor_2_16_gram_disc h hPQ n m]
  exact hT.trans (by simpa only [a,faberFillAxes_succ,mulAdj,B4,Nat.cast_add,Nat.cast_one] using hG)

/-- **Corollary 2.16** (TT:4538–4580). Let `(f, g)` be a normalized disjoint pair with `F` null and `B₁`, `B₄`
Hilbert–Schmidt.
- `α_n = P_n'/√(πn)` and `β_n = Q_n'/√(πn)` are bases of `A₂¹(Ω)`, `A₂¹(Ω*)`.
- Their Gram (period) matrices are `N_Ω = B₃B₃*` and `N_{Ω*} = B₂B₂*`.
- By (2.2) these are `I - B₄B₄*` and `I - B₁B₁*`, so `det N_Ω = det N_{Ω*} = Det_F(𝒞)`. -/
theorem cor_2_16 {f g : ℂ → ℂ} (h : IsNormalizedDisjointPair f g)
    (hF : volume ((f '' unitDisc ∪ g '' unitDiscExterior)ᶜ) = 0) {P Q : ℕ → Polynomial ℂ} (hPQ : IsFaber f g P Q)
    (hHS : Summable (fun q : ℕ × ℕ => ‖B1 (grunsky f g) q.1 q.2‖ ^ 2) ∧
      Summable (fun q : ℕ × ℕ => ‖B4 (grunsky f g) q.1 q.2‖ ^ 2)) :
    let b := grunsky f g
    (∀ m n, (∫ z in f '' unitDisc, (P (n + 1)).derivative.eval z / Real.sqrt (π * (n + 1)) *
        conj ((P (m + 1)).derivative.eval z / Real.sqrt (π * (m + 1)))) = mulAdj (B3 b) (B3 b) n m) ∧
      (∀ m n, (∫ z in g '' unitDiscExterior, deriv (fun w => (Q (n + 1)).eval w⁻¹) z / Real.sqrt (π * (n + 1)) *
        conj (deriv (fun w => (Q (m + 1)).eval w⁻¹) z / Real.sqrt (π * (m + 1)))) = mulAdj (B2 b) (B2 b) n m) ∧
      (∀ m n, mulAdj (B3 b) (B3 b) m n = kron m n - mulAdj (B4 b) (B4 b) m n) ∧
      ∀ m n, mulAdj (B2 b) (B2 b) m n = kron m n - mulAdj (B1 b) (B1 b) m n := by
  dsimp only
  exact ⟨cor_2_16_gram_disc h hPQ, cor_2_16_gram_exterior h hPQ,
    cor_2_16_block_positive h hF hPQ, cor_2_16_block_negative h hF hPQ⟩

end TakhtajanTeo.Ch2
