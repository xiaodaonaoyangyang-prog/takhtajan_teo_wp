import TakhtajanTeo.Ch2.S2_Grunsky
import TakhtajanTeo.Ch2.S2_MixedB
open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal ComplexConjugate Classical Real
noncomputable section
namespace TakhtajanTeo
open LiZhongQC
namespace Ch2

theorem hook_eq_2_2 {f g : ℂ → ℂ} (h : IsNormalizedDisjointPair f g)
    (hF : volume ((f '' unitDisc ∪ g '' unitDiscExterior)ᶜ) = 0) :
    let b := grunsky f g
    (∀ m n, mulAdj (B1 b) (B1 b) m n + mulAdj (B2 b) (B2 b) m n = kron m n) ∧
      (∀ m n, mulAdj (B3 b) (B1 b) m n + mulAdj (B4 b) (B2 b) m n = 0) ∧
      (∀ m n, mulAdj (B1 b) (B3 b) m n + mulAdj (B2 b) (B4 b) m n = 0) ∧
      (∀ m n, mulAdj (B3 b) (B3 b) m n + mulAdj (B4 b) (B4 b) m n = kron m n) ∧
      ∀ (A : ℕ → ℕ → ℂ), A ∈ ({B1 b, B2 b, B3 b, B4 b} : Set (ℕ → ℕ → ℂ)) → ∀ x : ℕ → ℂ,
        Summable (fun n => ‖x n‖ ^ 2) → ∑' m, ‖∑' n, A m n * x n‖ ^ 2 ≤ ∑' n, ‖x n‖ ^ 2 := by
  intro b
  obtain ⟨i1, i2, i3, i4, hb, -⟩ :=
    mg_eq_2_2_core h hF (B1 := B1 b) (B2 := B2 b) (B3 := B3 b) (B4 := B4 b)
      (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
  refine ⟨i1, i2, i3, i4, ?_⟩
  intro A hA x hx
  rcases hA with rfl | rfl | rfl | rfl
  · exact (hb x hx).1
  · exact (hb x hx).2.1
  · exact (hb x hx).2.2.1
  · exact (hb x hx).2.2.2

theorem hook_unitary {f g : ℂ → ℂ} (h : IsNormalizedDisjointPair f g)
    (hF : volume ((f '' unitDisc ∪ g '' unitDiscExterior)ᶜ) = 0) :
    let b := grunsky f g
    (∀ m n, B1 b m n = B1 b n m ∧ B4 b m n = B4 b n m ∧ B3 b m n = B2 b n m) ∧
      (∀ m n, (∑' k, (conj (B1 b k m) * B1 b k n + conj (B3 b k m) * B3 b k n)) = kron m n) ∧
      (∀ m n, (∑' k, (conj (B2 b k m) * B2 b k n + conj (B4 b k m) * B4 b k n)) = kron m n) ∧
      ∀ m n, (∑' k, (conj (B1 b k m) * B2 b k n + conj (B3 b k m) * B4 b k n)) = 0 :=
  mg_unitary_core h hF (B1 := B1 (grunsky f g)) (B2 := B2 (grunsky f g)) (B3 := B3 (grunsky f g))
    (B4 := B4 (grunsky f g)) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)

/-! ### Original relocated (2026-10-26) -/

/-- **(2.2)** (TT:3874–3894). If `F` is a null set, the matrices `B_l` define bounded operators on `ℓ²` (rows
square-summable, uniformly), and:
- `B₁B₁* + B₂B₂* = I`;
- `B₃B₁* + B₄B₂* = 0`;
- `B₁B₃* + B₂B₄* = 0`;
- `B₃B₃* + B₄B₄* = I`.

Hence `‖B_l‖ ≤ 1`. -/
theorem eq_2_2 {f g : ℂ → ℂ} (h : IsNormalizedDisjointPair f g)
    (hF : volume ((f '' unitDisc ∪ g '' unitDiscExterior)ᶜ) = 0) :
    let b := grunsky f g
    (∀ m n, mulAdj (B1 b) (B1 b) m n + mulAdj (B2 b) (B2 b) m n = kron m n) ∧
      (∀ m n, mulAdj (B3 b) (B1 b) m n + mulAdj (B4 b) (B2 b) m n = 0) ∧
      (∀ m n, mulAdj (B1 b) (B3 b) m n + mulAdj (B2 b) (B4 b) m n = 0) ∧
      (∀ m n, mulAdj (B3 b) (B3 b) m n + mulAdj (B4 b) (B4 b) m n = kron m n) ∧
      ∀ (A : ℕ → ℕ → ℂ), A ∈ ({B1 b, B2 b, B3 b, B4 b} : Set (ℕ → ℕ → ℂ)) → ∀ x : ℕ → ℂ,
        Summable (fun n => ‖x n‖ ^ 2) → ∑' m, ‖∑' n, A m n * x n‖ ^ 2 ≤ ∑' n, ‖x n‖ ^ 2 :=
  hook_eq_2_2 h hF

/-- (TT:3916–3936) The symmetry of the Grunsky coefficients is `𝐁* = 𝐉𝐁𝐉`, with `J` the conjugation (2.3):
`B₁ᵗ = B₁`, `B₄ᵗ = B₄`, `B₃ᵗ = B₂`. Together with (2.2) this gives `𝐁*𝐁 = 𝐈`, so `𝐁` is unitary on `ℓ² ⊕ ℓ²`:
`B₁*B₁ + B₃*B₃ = I`, `B₂*B₂ + B₄*B₄ = I`, `B₁*B₂ + B₃*B₄ = 0`. -/
theorem grunsky_unitary {f g : ℂ → ℂ} (h : IsNormalizedDisjointPair f g)
    (hF : volume ((f '' unitDisc ∪ g '' unitDiscExterior)ᶜ) = 0) :
    let b := grunsky f g
    (∀ m n, B1 b m n = B1 b n m ∧ B4 b m n = B4 b n m ∧ B3 b m n = B2 b n m) ∧
      (∀ m n, (∑' k, (conj (B1 b k m) * B1 b k n + conj (B3 b k m) * B3 b k n)) = kron m n) ∧
      (∀ m n, (∑' k, (conj (B2 b k m) * B2 b k n + conj (B4 b k m) * B4 b k n)) = kron m n) ∧
      ∀ m n, (∑' k, (conj (B1 b k m) * B2 b k n + conj (B3 b k m) * B4 b k n)) = 0 :=
  hook_unitary h hF

end Ch2
end TakhtajanTeo
