import LiZhongQC.Lemmas.Mobius
import Mathlib.Topology.Maps.Proper.Basic

/-!
# Joint continuity on the extended plane (Möbius action, inverses)

Generic results moved from `Appendix/AppACont` (names and statements unchanged) so that low modules can use them:
`acc_mob_cont` (the Möbius action is jointly continuous in the coefficients) and `acc_inv_cont` (inverses of a jointly
continuous family of bijections of `ℂ̄` are jointly continuous, by the closed graph theorem for the compact codomain).
-/

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal ComplexConjugate Classical Real
noncomputable section
namespace TakhtajanTeo
open LiZhongQC
namespace AppA

/-! ### Generic Möbius and inverse continuity (下属1) -/

/-- Off the pole of `mobiusExt 0 1 1 0`-conjugation: when `a z + b ≠ 0`,
`mobiusExt a b c d z = ι((c z + d)/(a z + b))` with `ι = mobiusExt 0 1 1 0`. -/
theorem acc_mob_eq_inv {a b c d z : ℂ} (h : a * z + b ≠ 0) :
    mobiusExt a b c d (z : ExtPlane) =
      mobiusExt 0 1 1 0 (((c * z + d) / (a * z + b) : ℂ) : ExtPlane) := by
  by_cases hc : c * z + d = 0
  · rw [mobiusExt_coe_of_eq_zero hc, hc, zero_div,
      mobiusExt_coe_of_eq_zero (show (1 : ℂ) * 0 + 0 = 0 by ring)]
  · have hu : (1 : ℂ) * ((c * z + d) / (a * z + b)) + 0 ≠ 0 := by
      rw [one_mul, add_zero]; exact div_ne_zero hc h
    rw [mobiusExt_coe hc, mobiusExt_coe hu]
    congr 1
    show (a * z + b) / (c * z + d) =
      (0 * ((c * z + d) / (a * z + b)) + 1) / (1 * ((c * z + d) / (a * z + b)) + 0)
    rw [zero_mul, zero_add, one_mul, add_zero, one_div, inv_div]

/-- `mobiusExt a b c d ∘ ι = mobiusExt b a d c` with `ι = mobiusExt 0 1 1 0`. -/
theorem acc_mob_swap_inv (a b c d : ℂ) (u : ExtPlane) :
    mobiusExt a b c d (mobiusExt 0 1 1 0 u) = mobiusExt b a d c u := by
  induction u using OnePoint.rec with
  | infty =>
    show mobiusExt a b c d (mobiusExt 0 1 1 0 extInf) = mobiusExt b a d c extInf
    rw [mobiusExt_infty_of_ne one_ne_zero, zero_div]
    by_cases hd : d = 0
    · rw [mobiusExt_coe_of_eq_zero (show c * 0 + d = 0 by rw [hd]; ring), mobiusExt_infty_of_eq hd]
    · rw [mobiusExt_coe (show c * 0 + d ≠ 0 by rwa [mul_zero, zero_add]), mobiusExt_infty_of_ne hd]
      congr 1
      show (a * 0 + b) / (c * 0 + d) = b / d
      rw [mul_zero, zero_add, mul_zero, zero_add]
  | coe z =>
    by_cases hz : z = 0
    · subst hz
      rw [mobiusExt_coe_of_eq_zero (show (1 : ℂ) * 0 + 0 = 0 by ring)]
      by_cases hc : c = 0
      · rw [mobiusExt_infty_of_eq hc, mobiusExt_coe_of_eq_zero (show d * 0 + c = 0 by rw [hc]; ring)]
      · rw [mobiusExt_infty_of_ne hc, mobiusExt_coe (show d * 0 + c ≠ 0 by rwa [mul_zero, zero_add])]
        congr 1
        show a / c = (b * 0 + a) / (d * 0 + c)
        rw [mul_zero, zero_add, mul_zero, zero_add]
    · rw [mobiusExt_coe (show (1 : ℂ) * z + 0 ≠ 0 by rwa [one_mul, add_zero])]
      have hw : mobiusFn 0 1 1 0 z = z⁻¹ := by
        show (0 * z + 1) / (1 * z + 0) = z⁻¹
        rw [zero_mul, zero_add, one_mul, add_zero, one_div]
      rw [hw]
      have hden : c * z⁻¹ + d = (d * z + c) * z⁻¹ := by
        rw [add_mul, mul_assoc, mul_inv_cancel₀ hz, mul_one, add_comm]
      have hnum : a * z⁻¹ + b = (b * z + a) * z⁻¹ := by
        rw [add_mul, mul_assoc, mul_inv_cancel₀ hz, mul_one, add_comm]
      by_cases h : d * z + c = 0
      · rw [mobiusExt_coe_of_eq_zero (show c * z⁻¹ + d = 0 by rw [hden, h, zero_mul]),
          mobiusExt_coe_of_eq_zero h]
      · have h1 : c * z⁻¹ + d ≠ 0 := by rw [hden]; exact mul_ne_zero h (inv_ne_zero hz)
        rw [mobiusExt_coe h1, mobiusExt_coe h]
        congr 1
        show (a * z⁻¹ + b) / (c * z⁻¹ + d) = (b * z + a) / (d * z + c)
        rw [hnum, hden, mul_div_mul_right _ _ (inv_ne_zero hz)]

/-- Joint continuity of `(a,b,c,d,w) ↦ mobiusExt a b c d w` at a finite point `w = z₀` where the
denominator or the numerator does not vanish. -/
theorem acc_mob_coe_cont {x₀ : ℂ × ℂ × ℂ × ℂ} {z₀ : ℂ}
    (h : x₀.2.2.1 * z₀ + x₀.2.2.2 ≠ 0 ∨ x₀.1 * z₀ + x₀.2.1 ≠ 0) :
    ContinuousAt (fun q : (ℂ × ℂ × ℂ × ℂ) × ExtPlane => mobiusExt q.1.1 q.1.2.1 q.1.2.2.1 q.1.2.2.2 q.2)
      (x₀, (z₀ : ExtPlane)) := by
  have he : IsOpenEmbedding (Prod.map (id : ℂ × ℂ × ℂ × ℂ → ℂ × ℂ × ℂ × ℂ) ((↑) : ℂ → ExtPlane)) :=
    IsOpenEmbedding.id.prodMap OnePoint.isOpenEmbedding_coe
  rw [show ((x₀, (z₀ : ExtPlane)) : (ℂ × ℂ × ℂ × ℂ) × ExtPlane) =
      Prod.map (id : ℂ × ℂ × ℂ × ℂ → ℂ × ℂ × ℂ × ℂ) ((↑) : ℂ → ExtPlane) (x₀, z₀) from rfl,
    ← he.continuousAt_iff]
  have hden : ContinuousAt (fun p : (ℂ × ℂ × ℂ × ℂ) × ℂ => p.1.2.2.1 * p.2 + p.1.2.2.2) (x₀, z₀) := by
    fun_prop
  have hnum : ContinuousAt (fun p : (ℂ × ℂ × ℂ × ℂ) × ℂ => p.1.1 * p.2 + p.1.2.1) (x₀, z₀) := by
    fun_prop
  rcases h with h | h
  · refine ContinuousAt.congr (f := fun p : (ℂ × ℂ × ℂ × ℂ) × ℂ =>
        (((p.1.1 * p.2 + p.1.2.1) / (p.1.2.2.1 * p.2 + p.1.2.2.2) : ℂ) : ExtPlane)) ?_ ?_
    · exact OnePoint.continuous_coe.continuousAt.comp (hnum.div hden h)
    · filter_upwards [hden.eventually_ne h] with p hp
      exact (mobiusExt_coe hp).symm
  · have hι : Continuous (mobiusExt 0 1 1 0) := continuous_mobiusExt (by norm_num)
    refine ContinuousAt.congr (f := fun p : (ℂ × ℂ × ℂ × ℂ) × ℂ =>
        mobiusExt 0 1 1 0 (((p.1.2.2.1 * p.2 + p.1.2.2.2) / (p.1.1 * p.2 + p.1.2.1) : ℂ) : ExtPlane))
      ?_ ?_
    · exact hι.continuousAt.comp (OnePoint.continuous_coe.continuousAt.comp (hden.div hnum h))
    · filter_upwards [hnum.eventually_ne h] with p hp
      exact (acc_mob_eq_inv hp).symm

/-- The action `(a, b, c, d, w) ↦ (aw + b)/(cw + d)` on `ℂ̄` is jointly continuous where `ad - bc ≠ 0`. -/
theorem acc_mob_cont :
    ContinuousOn (fun q : (ℂ × ℂ × ℂ × ℂ) × ExtPlane => mobiusExt q.1.1 q.1.2.1 q.1.2.2.1 q.1.2.2.2 q.2)
      ({x : ℂ × ℂ × ℂ × ℂ | x.1 * x.2.2.2 - x.2.1 * x.2.2.1 ≠ 0} ×ˢ univ) := by
  intro q hq
  apply ContinuousAt.continuousWithinAt
  obtain ⟨x₀, w₀⟩ := q
  have hdet : x₀.1 * x₀.2.2.2 - x₀.2.1 * x₀.2.2.1 ≠ 0 := hq.1
  clear hq
  induction w₀ using OnePoint.rec with
  | infty =>
    have hι : Continuous (mobiusExt 0 1 1 0) := continuous_mobiusExt (by norm_num)
    have h0 : mobiusExt 0 1 1 0 extInf = ((0 : ℂ) : ExtPlane) := by
      show mobiusExt 0 1 1 0 extInf = ((0 : ℂ) : ExtPlane)
      rw [mobiusExt_infty_of_ne one_ne_zero, zero_div]
    have hσ : x₀.2.2.2 * 0 + x₀.2.2.1 ≠ 0 ∨ x₀.2.1 * 0 + x₀.1 ≠ 0 := by
      by_cases h1 : x₀.2.2.2 * 0 + x₀.2.2.1 = 0
      · right
        intro h2
        apply hdet
        rw [show x₀.1 * x₀.2.2.2 - x₀.2.1 * x₀.2.2.1 =
            (x₀.2.1 * 0 + x₀.1) * x₀.2.2.2 - x₀.2.1 * (x₀.2.2.2 * 0 + x₀.2.2.1) by ring, h1, h2]
        ring
      · exact Or.inl h1
    have hF := acc_mob_coe_cont (x₀ := (x₀.2.1, x₀.1, x₀.2.2.2, x₀.2.2.1)) hσ
    have hG : ContinuousAt (fun q : (ℂ × ℂ × ℂ × ℂ) × ExtPlane =>
        mobiusExt q.1.2.1 q.1.1 q.1.2.2.2 q.1.2.2.1 q.2) (x₀, mobiusExt 0 1 1 0 extInf) := by
      rw [h0]
      exact ContinuousAt.comp
        (g := fun q : (ℂ × ℂ × ℂ × ℂ) × ExtPlane => mobiusExt q.1.1 q.1.2.1 q.1.2.2.1 q.1.2.2.2 q.2)
        (f := fun q : (ℂ × ℂ × ℂ × ℂ) × ExtPlane => ((q.1.2.1, q.1.1, q.1.2.2.2, q.1.2.2.1), q.2))
        hF (by fun_prop)
    refine (ContinuousAt.comp
      (g := fun q : (ℂ × ℂ × ℂ × ℂ) × ExtPlane => mobiusExt q.1.2.1 q.1.1 q.1.2.2.2 q.1.2.2.1 q.2)
      (f := fun q : (ℂ × ℂ × ℂ × ℂ) × ExtPlane => (q.1, mobiusExt 0 1 1 0 q.2))
      hG (continuous_fst.prodMk (hι.comp continuous_snd)).continuousAt).congr
        (Eventually.of_forall fun q => ?_)
    exact acc_mob_swap_inv q.1.2.1 q.1.1 q.1.2.2.2 q.1.2.2.1 q.2
  | coe z₀ =>
    have hor : x₀.2.2.1 * z₀ + x₀.2.2.2 ≠ 0 ∨ x₀.1 * z₀ + x₀.2.1 ≠ 0 := by
      by_cases h1 : x₀.2.2.1 * z₀ + x₀.2.2.2 = 0
      · right
        intro h2
        apply hdet
        rw [show x₀.1 * x₀.2.2.2 - x₀.2.1 * x₀.2.2.1 =
            x₀.1 * (x₀.2.2.1 * z₀ + x₀.2.2.2) - x₀.2.2.1 * (x₀.1 * z₀ + x₀.2.1) by ring, h1, h2]
        ring
      · exact Or.inl h1
    exact acc_mob_coe_cont hor

/-- Inverses of a jointly continuous family of bijections of `ℂ̄` are jointly continuous (closed graph theorem). -/
theorem acc_inv_cont {X : Type*} [TopologicalSpace X] {Φ : X → ExtPlane → ExtPlane} {U : Set X}
    (hΦ : ContinuousOn (fun p : X × ExtPlane => Φ p.1 p.2) (U ×ˢ univ))
    (hb : ∀ x ∈ U, Function.Bijective (Φ x)) :
    ContinuousOn (fun p : X × ExtPlane => Function.invFun (Φ p.1) p.2) (U ×ˢ univ) := by
  rw [continuousOn_iff_continuous_domRestrict]
  apply continuous_of_isClosed_graph
  have hc : Continuous (fun q : (U ×ˢ (univ : Set ExtPlane)) × ExtPlane =>
      Φ (q.1 : X × ExtPlane).1 q.2) :=
    hΦ.comp_continuous
      (f := fun q : (U ×ˢ (univ : Set ExtPlane)) × ExtPlane => ((q.1 : X × ExtPlane).1, q.2))
      (by fun_prop) (fun q => ⟨q.1.2.1, mem_univ _⟩)
  have hg : Function.graph ((U ×ˢ (univ : Set ExtPlane)).domRestrict
      (fun p : X × ExtPlane => Function.invFun (Φ p.1) p.2)) =
      {q : (U ×ˢ (univ : Set ExtPlane)) × ExtPlane | Φ (q.1 : X × ExtPlane).1 q.2 = (q.1 : X × ExtPlane).2} := by
    ext q
    have hbq := hb _ q.1.2.1
    show Function.invFun (Φ (q.1 : X × ExtPlane).1) (q.1 : X × ExtPlane).2 = q.2 ↔
      Φ (q.1 : X × ExtPlane).1 q.2 = (q.1 : X × ExtPlane).2
    constructor
    · intro h
      rw [← h]
      exact Function.rightInverse_invFun hbq.2 _
    · intro h
      apply hbq.1
      rw [Function.rightInverse_invFun hbq.2, h]
  rw [hg]
  exact isClosed_eq hc (by fun_prop)

end AppA
end TakhtajanTeo
