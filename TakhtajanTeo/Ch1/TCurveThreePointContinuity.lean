import TakhtajanTeo.Ch1.TCurveSigmaCoordinates

open Complex Set Metric Filter Topology
open scoped ComplexConjugate Classical
noncomputable section
namespace TakhtajanTeo
open LiZhongQC

/-- A Mobius family is jointly continuous when its values at a continuously
moving distinct triple are another continuously moving distinct triple. -/
theorem tcg_mobius_three_continuous {X : Type*} [TopologicalSpace X]
    (B : X → ExtPlane → ExtPlane) (hB : ∀ x, IsMobius (B x))
    (p₁ p₂ p₃ q₁ q₂ q₃ : X → ℂ)
    (hp₁ : Continuous p₁) (hp₂ : Continuous p₂) (hp₃ : Continuous p₃)
    (hq₁ : Continuous q₁) (hq₂ : Continuous q₂) (hq₃ : Continuous q₃)
    (hp12 : ∀ x, p₁ x ≠ p₂ x) (hp13 : ∀ x, p₁ x ≠ p₃ x) (hp23 : ∀ x, p₂ x ≠ p₃ x)
    (hq12 : ∀ x, q₁ x ≠ q₂ x) (hq13 : ∀ x, q₁ x ≠ q₃ x) (hq23 : ∀ x, q₂ x ≠ q₃ x)
    (he₁ : ∀ x, B x (p₁ x : ExtPlane) = (q₁ x : ExtPlane))
    (he₂ : ∀ x, B x (p₂ x : ExtPlane) = (q₂ x : ExtPlane))
    (he₃ : ∀ x, B x (p₃ x : ExtPlane) = (q₃ x : ExtPlane))
    (w : X → ExtPlane) (hw : Continuous w) : Continuous (fun x => B x (w x)) := by
  let P : X → ℂ × ℂ × ℂ × ℂ := fun x =>
    (p₂ x - p₃ x, -(p₁ x * (p₂ x - p₃ x)), p₂ x - p₁ x, -(p₃ x * (p₂ x - p₁ x)))
  let Q : X → ℂ × ℂ × ℂ × ℂ := fun x =>
    (q₂ x - q₃ x, -(q₁ x * (q₂ x - q₃ x)), q₂ x - q₁ x, -(q₃ x * (q₂ x - q₁ x)))
  have hdet : ∀ r₁ r₂ r₃ : ℂ, r₁ ≠ r₂ → r₁ ≠ r₃ → r₂ ≠ r₃ →
      (r₂ - r₃) * -(r₃ * (r₂ - r₁)) - -(r₁ * (r₂ - r₃)) * (r₂ - r₁) ≠ 0 := by
    intro r₁ r₂ r₃ h12 h13 h23
    rw [show (r₂ - r₃) * -(r₃ * (r₂ - r₁)) - -(r₁ * (r₂ - r₃)) * (r₂ - r₁) =
      (r₂ - r₃) * (r₂ - r₁) * (r₁ - r₃) by ring]
    exact mul_ne_zero (mul_ne_zero (sub_ne_zero.mpr h23) (sub_ne_zero.mpr h12.symm))
      (sub_ne_zero.mpr h13)
  have hP : ∀ x, (P x).1 * (P x).2.2.2 - (P x).2.1 * (P x).2.2.1 ≠ 0 :=
    fun x => hdet _ _ _ (hp12 x) (hp13 x) (hp23 x)
  have hQ : ∀ x, (Q x).1 * (Q x).2.2.2 - (Q x).2.1 * (Q x).2.2.1 ≠ 0 :=
    fun x => hdet _ _ _ (hq12 x) (hq13 x) (hq23 x)
  have hQi : ∀ x, (Q x).2.2.2 * (Q x).1 - (-(Q x).2.1) * (-(Q x).2.2.1) ≠ 0 := by
    intro x
    convert hQ x using 1 <;> ring
  have heq : (fun x => B x (w x)) = (fun x =>
      mobiusExt (Q x).2.2.2 (-(Q x).2.1) (-(Q x).2.2.1) (Q x).1
        (mobiusExt (P x).1 (P x).2.1 (P x).2.2.1 (P x).2.2.2 (w x))) := by
    funext x
    let NP := mobiusExt (P x).1 (P x).2.1 (P x).2.2.1 (P x).2.2.2
    let NQ := mobiusExt (Q x).1 (Q x).2.1 (Q x).2.2.1 (Q x).2.2.2
    have hNP : IsMobius NP := ⟨_, _, _, _, hP x, rfl⟩
    have hNQ : IsMobius NQ := ⟨_, _, _, _, hQ x, rfl⟩
    obtain ⟨hP1, hP2, hP3⟩ := mobius_three_point_eval (hp12 x) (hp13 x) (hp23 x)
    obtain ⟨hQ1, hQ2, hQ3⟩ := mobius_three_point_eval (hq12 x) (hq13 x) (hq23 x)
    have he : (fun z => NQ (B x z)) = NP :=
      mobius_eq_of_three_points (isMobius_comp (hB x) hNQ) hNP (hp12 x) (hp13 x) (hp23 x)
        (by rw [he₁]; exact hQ1.trans hP1.symm)
        (by rw [he₂]; exact hQ2.trans hP2.symm)
        (by rw [he₃]; exact hQ3.trans hP3.symm)
    change B x (w x) = mobiusExt (Q x).2.2.2 (-(Q x).2.1) (-(Q x).2.2.1) (Q x).1 (NP (w x))
    rw [← he]
    exact (mobiusExt_inv_apply (hQ x) (B x (w x))).symm
  rw [heq]
  have hPc : Continuous P := by dsimp [P]; fun_prop
  have hQc : Continuous Q := by dsimp [Q]; fun_prop
  have hinner : Continuous (fun x => mobiusExt (P x).1 (P x).2.1 (P x).2.2.1 (P x).2.2.2 (w x)) :=
    AppA.acc_mob_cont.comp_continuous (f := fun x => (P x, w x)) (hPc.prodMk hw)
      (fun x => ⟨hP x, mem_univ _⟩)
  have hQic : Continuous (fun x : X => ((Q x).2.2.2, -(Q x).2.1, -(Q x).2.2.1, (Q x).1)) := by
    fun_prop
  exact AppA.acc_mob_cont.comp_continuous
    (f := fun x => (((Q x).2.2.2, -(Q x).2.1, -(Q x).2.2.1, (Q x).1),
      mobiusExt (P x).1 (P x).2.1 (P x).2.2.1 (P x).2.2.2 (w x)))
    (hQic.prodMk hinner) (fun x => ⟨hQi x, mem_univ _⟩)

#print axioms tcg_mobius_three_continuous
end TakhtajanTeo
