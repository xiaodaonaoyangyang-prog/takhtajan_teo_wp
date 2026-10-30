import TakhtajanTeo.Basic
import LiZhongQC.Ch10.S33_BersEmbedding

/-!
# Chapter 1, §1.1 — Teichmüller theory (TT:336–586)

* §1.1.1 Model A (`w_μ`, reflection (1.2)) and Model B (`w^μ`), `T(1) = L∞(𝔻*)₁/∼`, their equivalence; the projection
  `Φ`; real-analytic representatives; `ker D₀Φ = 𝓝(𝔻*)`; the decomposition (1.3)
* §1.1.2 the group law `λ = ν * μ⁻¹`, right translations `R_[μ]`, discontinuity of left translations,
  `ker D_μΦ`
* §1.1.3 the Bers embedding `β([μ]) = 𝒮(w^μ|𝔻)`, the Kraus–Nehari bound, (1.4), `Λ = (D₀β)⁻¹`, Ahlfors–Weill
* §1.1.4 the Bers charts `h_μ`, the atlas, Remark 1.2, (1.5)–(1.7), Remark 1.3
* §1.1.5 the universal Teichmüller curve (1.8)

**Modelling** (see `ARCHITECTURE.md`).
- The complex Banach manifold structure of `T(1)` is expressed through Bers coordinates: holomorphy of maps between
  `L∞(𝔻*)`, `A∞(𝔻)` and their open subsets, read through `β` and the charts `h_μ`.
- No `ChartedSpace` instance is built.

**Reading of the zero section (TT:568).**
- The memoir writes the zero section of `𝒯(1) → T(1)` as `[μ] ↦ ([μ], ∞)`.
- `w^μ` is normalized at `0` and need not fix `∞`. For example, an odd univalent map of `𝔻` onto an unbounded
  quasidisk sends a point of `S¹` to `∞`, so `∞ ∉ w^μ(𝔻*)`. Lemma 1.5 proves `w^μ(∞) = ∞` only for harmonic `μ`.
- The section is therefore stated as `[μ] ↦ ([μ], w^μ(∞))`. This is the image of `z = ∞` under the isomorphism
  `T(1) × 𝔻* ≅ 𝒯(1)` of TT:571, which is how the memoir uses it.
-/

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal ComplexConjugate BoundedContinuousFunction Classical Real

noncomputable section

namespace TakhtajanTeo

open LiZhongQC

/-! ## Reflection and extension facts used by the models -/

/-- Reflection in the unit circle is an involution, including the chosen junk
value at zero (TT:342). -/
theorem refl_involutive : Function.Involutive refl := by
  intro z
  simp [refl]

/-- The norm under reflection is the reciprocal norm (TT:342). -/
theorem norm_refl (z : ℂ) : ‖refl z‖ = ‖z‖⁻¹ := by
  simp [refl]

/-- Reflection exchanges the punctured disk and its exterior (TT:342). -/
theorem refl_mem_disc_iff {z : ℂ} (hz : z ≠ 0) :
    refl z ∈ unitDisc ↔ z ∈ unitDiscExterior := by
  simp only [unitDisc, mem_ball_zero_iff, unitDiscExterior, mem_setOf_eq]
  rw [norm_refl]
  exact inv_lt_one₀ (norm_pos_iff.mpr hz)

/-- Reflection takes the exterior to the punctured disk and conversely (TT:342). -/
theorem refl_mem_exterior_iff {z : ℂ} (hz : z ≠ 0) :
    refl z ∈ unitDiscExterior ↔ z ∈ unitDisc := by
  simp only [unitDisc, mem_ball_zero_iff, unitDiscExterior, mem_setOf_eq]
  rw [norm_refl]
  exact one_lt_inv₀ (norm_pos_iff.mpr hz)

/-- The Model A extension agrees with its original coefficient on the exterior
as required in (1.1) (TT:342–346). -/
theorem extA_eq_on_exterior (μ : LinfStar) : EqOn (extA μ) μ unitDiscExterior := by
  intro z hz
  exact if_pos hz

/-- The reflected coefficient has the same pointwise norm as the original
coefficient at the reflected point, away from zero (1.1, TT:342–346). -/
theorem norm_extA_on_disc (μ : LinfStar) {z : ℂ} (hz : z ∈ unitDisc) (hz0 : z ≠ 0) :
    ‖extA μ z‖ = ‖μ (refl z)‖ := by
  have hz' : ‖z‖ < 1 := mem_ball_zero_iff.mp hz
  have hn : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz0
  simp only [extA, if_neg (not_lt.mpr hz'.le), if_pos hz', norm_div,
    norm_mul, norm_pow, norm_conj]
  exact mul_div_cancel_right₀ _ (pow_ne_zero 2 hn)

/-- An L-infinity coefficient is bounded almost everywhere by its norm
(TT:340), on the exterior measure defining LinfStar. -/
theorem LinfStar_ae_norm_le (μ : LinfStar) :
    ∀ᵐ z ∂(volume.restrict unitDiscExterior), ‖μ z‖ ≤ ‖μ‖ := by
  simpa only [Lp.norm_def, toReal_eLpNorm] using ae_le_lpNorm_exponent_top (Lp.memLp μ)

/-- Extension by zero gives a measurable plane Beltrami coefficient with
the same essential bound (Model B, TT:355). -/
theorem extB_isBeltramiCoeff (μ : LinfStar) : IsBeltramiCoeff (extB μ) univ ‖μ‖ := by
  have hmeas : MeasurableSet unitDiscExterior :=
    (isOpen_lt continuous_const continuous_norm).measurableSet
  have hm : AEStronglyMeasurable (extB μ) volume :=
    (aestronglyMeasurable_indicator_iff hmeas).mpr (Lp.aestronglyMeasurable μ)
  refine ⟨by simpa only [Measure.restrict_univ] using hm, ?_⟩
  rw [Measure.restrict_univ]
  filter_upwards [(ae_restrict_iff' hmeas).mp (LinfStar_ae_norm_le μ)] with z hz
  by_cases h : z ∈ unitDiscExterior
  · simpa only [extB, indicator_of_mem h] using hz h
  · simp only [extB, indicator_of_notMem h, norm_zero]
    exact norm_nonneg μ

/-- The zero extension admits the normalized plane solution used to construct
Model B (TT:355), with the sharp dilatation bound and uniqueness supplied by
the proved measurable Riemann mapping theorem. -/
theorem extB_normalized_plane_exists {μ : LinfStar} (hμ : μ ∈ LinfStarBall) :
    ∃ W : ℂ → ℂ, IsNormalizedSolution W (extB μ) ∧
      IsKQC W univ ((1 + ‖μ‖) / (1 - ‖μ‖)) ∧
      ∀ V : ℂ → ℂ, IsNormalizedSolution V (extB μ) → V = W := by
  exact thm13_7_normalized_existence (norm_nonneg μ) (mem_ball_zero_iff.mp hμ)
    (extB_isBeltramiCoeff μ)

/-- Reflection transports plane almost-everywhere statements (TT:342). -/
theorem ae_refl {P : ℂ → Prop} (h : ∀ᵐ z, P z) : ∀ᵐ z, P (refl z) :=
  abT_ae_conj_inv h

/-- Reflection of a measurable plane function remains measurable
modulo null sets (TT:342). -/
theorem aestronglyMeasurable_comp_refl {f : ℂ → ℂ} (hf : AEStronglyMeasurable f volume) :
    AEStronglyMeasurable (fun z => f (refl z)) volume := by
  have hr : Measurable refl := measurable_inv.comp Complex.continuous_conj.measurable
  have hm : AEStronglyMeasurable (hf.mk f ∘ refl) volume :=
    (hf.stronglyMeasurable_mk.comp_measurable hr).aestronglyMeasurable
  apply hm.congr
  filter_upwards [ae_refl hf.ae_eq_mk] with z hz
  exact hz.symm

/-- The reflection extension has the original essential bound (TT:342–346). -/
theorem extA_ae_norm_le (μ : LinfStar) : ∀ᵐ z, ‖extA μ z‖ ≤ ‖μ‖ := by
  have hE : MeasurableSet unitDiscExterior :=
    (isOpen_lt continuous_const continuous_norm).measurableSet
  have hb : ∀ᵐ z, z ∈ unitDiscExterior → ‖μ z‖ ≤ ‖μ‖ :=
    (ae_restrict_iff' hE).mp (LinfStar_ae_norm_le μ)
  filter_upwards [hb, ae_refl hb] with z hz hr
  by_cases hzE : 1 < ‖z‖
  · simpa only [extA, if_pos hzE] using hz hzE
  · by_cases hzD : ‖z‖ < 1
    · by_cases hz0 : z = 0
      · norm_num [extA, hz0, norm_nonneg μ]
      · rw [norm_extA_on_disc μ (mem_ball_zero_iff.mpr hzD) hz0]
        exact hr ((refl_mem_exterior_iff hz0).mpr (mem_ball_zero_iff.mpr hzD))
    · simpa only [extA, if_neg hzE, if_neg hzD, norm_zero] using norm_nonneg μ

/-- The reflection extension is an admissible plane Beltrami coefficient
with the sharp essential bound (Model A, TT:342–346). -/
theorem extA_isBeltramiCoeff (μ : LinfStar) : IsBeltramiCoeff (extA μ) univ ‖μ‖ := by
  have hE : MeasurableSet unitDiscExterior :=
    (isOpen_lt continuous_const continuous_norm).measurableSet
  have hB : AEStronglyMeasurable (extB μ) volume := by
    simpa only [Measure.restrict_univ] using (extB_isBeltramiCoeff μ).1
  let g : ℂ → ℂ := fun z => conj (extB μ (refl z)) * z ^ 2 / conj z ^ 2
  have hg : AEStronglyMeasurable g volume := by
    exact ((Complex.continuous_conj.comp_aestronglyMeasurable
      (aestronglyMeasurable_comp_refl hB)).mul
      (by fun_prop : AEStronglyMeasurable (fun z : ℂ => z ^ 2) volume)).div₀
      (by fun_prop : AEStronglyMeasurable (fun z : ℂ => conj z ^ 2) volume)
  have he : extA μ = fun z => extB μ z + unitDisc.indicator g z := by
    funext z
    by_cases hzE : z ∈ unitDiscExterior
    · have hzEN : 1 < ‖z‖ := hzE
      have hzD : z ∉ unitDisc := by
        intro h
        exact (not_lt_of_ge (le_of_lt hzE)) (mem_ball_zero_iff.mp h)
      simp [extA, extB, hzE, hzEN, hzD]
    · have hzEN : ¬ 1 < ‖z‖ := hzE
      by_cases hzD : z ∈ unitDisc
      · have hzN := mem_ball_zero_iff.mp hzD
        by_cases hz0 : z = 0
        · subst z
          norm_num [extA, extB, g, unitDiscExterior, unitDisc, refl]
        · have hr := (refl_mem_exterior_iff hz0).mpr hzD
          simp [extA, extB, g, hzE, hzEN, hzD, hzN, hr]
      · have hzN : ¬ ‖z‖ < 1 := fun h => hzD (mem_ball_zero_iff.mpr h)
        simp [extA, extB, hzE, hzEN, hzD, hzN]
  have hm : AEStronglyMeasurable (extA μ) volume := by
    rw [he]
    exact hB.add (hg.indicator isOpen_ball.measurableSet)
  exact ⟨by simpa only [Measure.restrict_univ] using hm,
    by simpa only [Measure.restrict_univ] using extA_ae_norm_le μ⟩

/-- The reflected coefficient admits the normalized plane solution from
the measurable Riemann mapping theorem (TT:342–346). The disk-boundary
three-point normalization is a separate assertion. -/
theorem extA_normalized_plane_exists {μ : LinfStar} (hμ : μ ∈ LinfStarBall) :
    ∃ W : ℂ → ℂ, IsNormalizedSolution W (extA μ) ∧
      IsKQC W univ ((1 + ‖μ‖) / (1 - ‖μ‖)) ∧
      ∀ V : ℂ → ℂ, IsNormalizedSolution V (extA μ) → V = W := by
  exact thm13_7_normalized_existence (norm_nonneg μ) (mem_ball_zero_iff.mp hμ)
    (extA_isBeltramiCoeff μ)

/-! ## Finite part and three-point Möbius facts -/

/-- Finite part of a point of `ℂ̄` (`∞ ↦ 0`, a junk value used only off `𝔻` for Model B, and at the pole of `w_μ`
for Model A). -/
def finPart (w : ExtPlane) : ℂ := OnePoint.elim w 0 id

/-- The fractional linear map with matrix `[[p₂-p₃, -p₁(p₂-p₃)], [p₂-p₁, -p₃(p₂-p₁)]]` sends the distinct points
`p₁, p₂, p₃` to `0, 1, ∞`. -/
theorem mobius_three_point_eval {p₁ p₂ p₃ : ℂ} (h12 : p₁ ≠ p₂) (h13 : p₁ ≠ p₃) (h23 : p₂ ≠ p₃) :
    mobiusExt (p₂ - p₃) (-(p₁ * (p₂ - p₃))) (p₂ - p₁) (-(p₃ * (p₂ - p₁))) (p₁ : ExtPlane) = ((0 : ℂ) : ExtPlane) ∧
      mobiusExt (p₂ - p₃) (-(p₁ * (p₂ - p₃))) (p₂ - p₁) (-(p₃ * (p₂ - p₁))) (p₂ : ExtPlane) = ((1 : ℂ) : ExtPlane) ∧
      mobiusExt (p₂ - p₃) (-(p₁ * (p₂ - p₃))) (p₂ - p₁) (-(p₃ * (p₂ - p₁))) (p₃ : ExtPlane) = extInf := by
  have hd12 : p₂ - p₁ ≠ 0 := sub_ne_zero.2 h12.symm
  have hd13 : p₁ - p₃ ≠ 0 := sub_ne_zero.2 h13
  have hd23 : p₂ - p₃ ≠ 0 := sub_ne_zero.2 h23
  refine ⟨?_, ?_, ?_⟩
  · have hz : (p₂ - p₁) * p₁ + -(p₃ * (p₂ - p₁)) ≠ 0 := by
      have e : (p₂ - p₁) * p₁ + -(p₃ * (p₂ - p₁)) = (p₂ - p₁) * (p₁ - p₃) := by ring
      rw [e]
      exact mul_ne_zero hd12 hd13
    rw [mobiusExt_coe hz]
    congr 1
    have e : (p₂ - p₃) * p₁ + -(p₁ * (p₂ - p₃)) = 0 := by ring
    rw [mobiusFn, e, zero_div]
  · have hz : (p₂ - p₁) * p₂ + -(p₃ * (p₂ - p₁)) ≠ 0 := by
      have e : (p₂ - p₁) * p₂ + -(p₃ * (p₂ - p₁)) = (p₂ - p₁) * (p₂ - p₃) := by ring
      rw [e]
      exact mul_ne_zero hd12 hd23
    rw [mobiusExt_coe hz]
    congr 1
    rw [mobiusFn, div_eq_one_iff_eq hz]
    ring
  · apply mobiusExt_coe_of_eq_zero
    ring

/-- A fractional linear map fixing three distinct finite points is the identity. -/
theorem mobius_fixes_three {A B C D p₁ p₂ p₃ : ℂ} (hdet : A * D - B * C ≠ 0)
    (h12 : p₁ ≠ p₂) (h13 : p₁ ≠ p₃) (h23 : p₂ ≠ p₃)
    (f₁ : mobiusExt A B C D (p₁ : ExtPlane) = (p₁ : ExtPlane))
    (f₂ : mobiusExt A B C D (p₂ : ExtPlane) = (p₂ : ExtPlane))
    (f₃ : mobiusExt A B C D (p₃ : ExtPlane) = (p₃ : ExtPlane)) :
    mobiusExt A B C D = id := by
  have key : ∀ p : ℂ, mobiusExt A B C D (p : ExtPlane) = (p : ExtPlane) →
      C * p ^ 2 + (D - A) * p - B = 0 := by
    intro p hp
    by_cases hz : C * p + D = 0
    · rw [mobiusExt_coe_of_eq_zero hz] at hp
      exact absurd hp.symm (OnePoint.coe_ne_infty p)
    · rw [mobiusExt_coe hz] at hp
      have hp' : (A * p + B) / (C * p + D) = p := OnePoint.coe_injective hp
      rw [div_eq_iff hz] at hp'
      linear_combination -hp'
  have e1 := key p₁ f₁
  have e2 := key p₂ f₂
  have e3 := key p₃ f₃
  have d12 : p₁ - p₂ ≠ 0 := sub_ne_zero.2 h12
  have d13 : p₁ - p₃ ≠ 0 := sub_ne_zero.2 h13
  have d23 : p₂ - p₃ ≠ 0 := sub_ne_zero.2 h23
  have s12 : C * (p₁ + p₂) + (D - A) = 0 := by
    apply mul_left_cancel₀ d12
    linear_combination e1 - e2
  have s13 : C * (p₁ + p₃) + (D - A) = 0 := by
    apply mul_left_cancel₀ d13
    linear_combination e1 - e3
  have hC : C = 0 := by
    apply mul_left_cancel₀ d23
    linear_combination s12 - s13
  have hDA : D = A := by
    rw [hC] at s12
    linear_combination s12
  have hB : B = 0 := by
    rw [hC, hDA] at e1
    linear_combination -e1
  subst hC hDA hB
  have hA : D ≠ 0 := by
    intro h
    apply hdet
    rw [h]
    ring
  funext p
  induction p using OnePoint.rec with
  | infty => exact mobiusExt_infty_of_eq rfl
  | coe z =>
    have hz : (0 : ℂ) * z + D ≠ 0 := by simpa using hA
    rw [mobiusExt_coe hz]
    show ((mobiusFn D 0 0 D z : ℂ) : ExtPlane) = (z : ExtPlane)
    congr 1
    simp only [mobiusFn, mul_zero, zero_mul, add_zero, zero_add]
    exact mul_div_cancel_left₀ z hA

/-- Three distinct finite points can be sent to three distinct finite points by a fractional linear map. -/
theorem exists_mobius_three_points {p₁ p₂ p₃ q₁ q₂ q₃ : ℂ} (hp12 : p₁ ≠ p₂) (hp13 : p₁ ≠ p₃)
    (hp23 : p₂ ≠ p₃) (hq12 : q₁ ≠ q₂) (hq13 : q₁ ≠ q₃) (hq23 : q₂ ≠ q₃) :
    ∃ M : ExtPlane → ExtPlane, IsMobius M ∧ M (p₁ : ExtPlane) = (q₁ : ExtPlane) ∧
      M (p₂ : ExtPlane) = (q₂ : ExtPlane) ∧ M (p₃ : ExtPlane) = (q₃ : ExtPlane) := by
  obtain ⟨hA1, hA2, hA3⟩ := mobius_three_point_eval hp12 hp13 hp23
  obtain ⟨hB1, hB2, hB3⟩ := mobius_three_point_eval hq12 hq13 hq23
  have hdetP : ∀ r₁ r₂ r₃ : ℂ, r₁ ≠ r₂ → r₁ ≠ r₃ → r₂ ≠ r₃ →
      (r₂ - r₃) * (-(r₃ * (r₂ - r₁))) - (-(r₁ * (r₂ - r₃))) * (r₂ - r₁) ≠ 0 := by
    intro r₁ r₂ r₃ h12 h13 h23
    have e : (r₂ - r₃) * (-(r₃ * (r₂ - r₁))) - (-(r₁ * (r₂ - r₃))) * (r₂ - r₁) =
        (r₂ - r₃) * (r₂ - r₁) * (r₁ - r₃) := by ring
    rw [e]
    exact mul_ne_zero (mul_ne_zero (sub_ne_zero.2 h23) (sub_ne_zero.2 h12.symm)) (sub_ne_zero.2 h13)
  have key : ∀ a b c d a' b' c' d' : ℂ, a * d - b * c ≠ 0 → a' * d' - b' * c' ≠ 0 →
      mobiusExt a b c d (p₁ : ExtPlane) = mobiusExt a' b' c' d' (q₁ : ExtPlane) →
      mobiusExt a b c d (p₂ : ExtPlane) = mobiusExt a' b' c' d' (q₂ : ExtPlane) →
      mobiusExt a b c d (p₃ : ExtPlane) = mobiusExt a' b' c' d' (q₃ : ExtPlane) →
      ∃ M : ExtPlane → ExtPlane, IsMobius M ∧ M (p₁ : ExtPlane) = (q₁ : ExtPlane) ∧
        M (p₂ : ExtPlane) = (q₂ : ExtPlane) ∧ M (p₃ : ExtPlane) = (q₃ : ExtPlane) := by
    intro a b c d a' b' c' d' hdet hdet' g1 g2 g3
    have hinv : ∀ q : ExtPlane, mobiusExt d' (-b') (-c') a' (mobiusExt a' b' c' d' q) = q :=
      mobiusExt_inv_apply hdet'
    have hdetM : (d' * a + -b' * c) * (-c' * b + a' * d) - (d' * b + -b' * d) * (-c' * a + a' * c) ≠ 0 := by
      have e : (d' * a + -b' * c) * (-c' * b + a' * d) - (d' * b + -b' * d) * (-c' * a + a' * c) =
          (a' * d' - b' * c') * (a * d - b * c) := by ring
      rw [e]
      exact mul_ne_zero hdet' hdet
    refine ⟨fun w => mobiusExt d' (-b') (-c') a' (mobiusExt a b c d w),
      ⟨_, _, _, _, hdetM, funext fun w => s16p_mobiusExt_comp hdet w⟩, ?_, ?_, ?_⟩
    · show mobiusExt d' (-b') (-c') a' (mobiusExt a b c d (p₁ : ExtPlane)) = _
      rw [g1]
      exact hinv _
    · show mobiusExt d' (-b') (-c') a' (mobiusExt a b c d (p₂ : ExtPlane)) = _
      rw [g2]
      exact hinv _
    · show mobiusExt d' (-b') (-c') a' (mobiusExt a b c d (p₃ : ExtPlane)) = _
      rw [g3]
      exact hinv _
  exact key _ _ _ _ _ _ _ _ (hdetP p₁ p₂ p₃ hp12 hp13 hp23) (hdetP q₁ q₂ q₃ hq12 hq13 hq23)
    (hA1.trans hB1.symm) (hA2.trans hB2.symm) (hA3.trans hB3.symm)

/-- Two fractional linear maps that agree at three distinct finite points are equal. -/
theorem mobius_eq_of_three_points {M N : ExtPlane → ExtPlane} (hM : IsMobius M) (hN : IsMobius N)
    {p₁ p₂ p₃ : ℂ} (h12 : p₁ ≠ p₂) (h13 : p₁ ≠ p₃) (h23 : p₂ ≠ p₃)
    (e₁ : M (p₁ : ExtPlane) = N (p₁ : ExtPlane)) (e₂ : M (p₂ : ExtPlane) = N (p₂ : ExtPlane))
    (e₃ : M (p₃ : ExtPlane) = N (p₃ : ExtPlane)) : M = N := by
  obtain ⟨a, b, c, d, hdet, rfl⟩ := hM
  obtain ⟨a', b', c', d', hdet', rfl⟩ := hN
  have hinv : ∀ q : ExtPlane, mobiusExt d' (-b') (-c') a' (mobiusExt a' b' c' d' q) = q :=
    mobiusExt_inv_apply hdet'
  have hdetK : (d' * a + -b' * c) * (-c' * b + a' * d) - (d' * b + -b' * d) * (-c' * a + a' * c) ≠ 0 := by
    have e : (d' * a + -b' * c) * (-c' * b + a' * d) - (d' * b + -b' * d) * (-c' * a + a' * c) =
        (a' * d' - b' * c') * (a * d - b * c) := by ring
    rw [e]
    exact mul_ne_zero hdet' hdet
  have hK : ∀ w : ExtPlane, mobiusExt d' (-b') (-c') a' (mobiusExt a b c d w) =
      mobiusExt (d' * a + -b' * c) (d' * b + -b' * d) (-c' * a + a' * c) (-c' * b + a' * d) w :=
    fun w => s16p_mobiusExt_comp hdet w
  have hfix : mobiusExt (d' * a + -b' * c) (d' * b + -b' * d) (-c' * a + a' * c) (-c' * b + a' * d) = id := by
    apply mobius_fixes_three hdetK h12 h13 h23
    · rw [← hK, e₁]
      exact hinv _
    · rw [← hK, e₂]
      exact hinv _
    · rw [← hK, e₃]
      exact hinv _
  have hinv' : ∀ q : ExtPlane, mobiusExt a' b' c' d' (mobiusExt d' (-b') (-c') a' q) = q := by
    intro q
    have h := mobiusExt_inv_apply (a := d') (b := -b') (c := -c') (d := a')
      (by intro h; apply hdet'; linear_combination h) q
    simpa only [neg_neg] using h
  funext w
  have h1 : mobiusExt d' (-b') (-c') a' (mobiusExt a b c d w) = w := by
    rw [hK, hfix]
    rfl
  calc mobiusExt a b c d w
      = mobiusExt a' b' c' d' (mobiusExt d' (-b') (-c') a' (mobiusExt a b c d w)) := (hinv' _).symm
    _ = mobiusExt a' b' c' d' w := by rw [h1]

/-! ## §1.1.1 Main definitions -/

/-- **Model A** (TT:342–351). `w : ℂ̄ → ℂ̄` is the normalized quasiconformal mapping of the Riemann sphere for
`μ ∈ L∞(𝔻*)`, with complex dilatation the reflection extension `extA μ` (1.1), fixing `-1`, `-i` and `1`.
- The quasiconformal self-maps of `ℂ̄` with complex dilatation `extA μ` are exactly the maps `M ∘ W`, where `W` is a
  normalized plane solution (`LiZhongQC.IsNormalizedSolution`, fixing `0, 1, ∞`) and `M` is a Möbius map.
- **[CORRECTION 2026-10-25]** `w_μ` is a map of the sphere, as in the memoir. The previous version asked for a
  homeomorphism of `ℂ` onto `ℂ` (so `w(∞) = ∞`) fixing `-1, -i, 1`. By the reflection symmetry (1.2),
  `w(0) = refl (w(∞))`, so such a `w` fixes `0, 1, ∞` and equals `W`; then `W(-1) = -1` and `W(-i) = -i` would be
  forced, which fails in general (radial extension of a circle diffeomorphism with `g(π) ≠ π`). In general
  `w_μ(∞) = refl (w_μ(0))` is a finite point of `𝔻*`. -/
def IsNormalizedA (μ : LinfStar) (w : ExtPlane → ExtPlane) : Prop :=
  ∃ M : ExtPlane → ExtPlane, IsMobius M ∧ ∃ W : ℂ → ℂ, IsNormalizedSolution W (extA μ) ∧
    (∀ z : ℂ, w z = M (W z)) ∧ w extInf = M extInf ∧
    w ((-1 : ℂ) : ExtPlane) = ((-1 : ℂ) : ExtPlane) ∧ w ((-I : ℂ) : ExtPlane) = ((-I : ℂ) : ExtPlane) ∧
    w ((1 : ℂ) : ExtPlane) = ((1 : ℂ) : ExtPlane)

/-- The normalized quasiconformal mapping `w_μ : ℂ̄ → ℂ̄` of Model A (TT:346). The junk value `id` is used only
when no solution exists; `wA_spec` shows that a solution exists for `μ ∈ L∞(𝔻*)₁`. -/
def wAS (μ : LinfStar) : ExtPlane → ExtPlane :=
  if h : ∃ w, IsNormalizedA μ w then h.choose else id

/-- `w_μ` at finite points (junk value `0` at its pole, a point of `𝔻*` when `w_μ(∞) ≠ ∞`). -/
def wA (μ : LinfStar) (z : ℂ) : ℂ := finPart (wAS μ z)

/-- The chosen Model A map is bijective (TT:346). This follows from its defining predicate when a solution exists;
the fallback identity is bijective as well. -/
theorem wAS_bijective (μ : LinfStar) : Function.Bijective (wAS μ) := by
  unfold wAS
  split_ifs with h
  · obtain ⟨M, hM, W, hW, hfinite, hinfty, _⟩ := h.choose_spec
    obtain ⟨K, hK⟩ := hW.1
    have hWi : Function.Injective W :=
      fun _ _ he => hK.2.2.1.2.1 (mem_univ _) (mem_univ _) he
    have hWs : Function.Surjective W :=
      Set.range_eq_univ.mp (by simpa only [Set.image_univ] using hW.2.1)
    have hMi : Function.Bijective M := by
      obtain ⟨a, b, c, d, hdet, rfl⟩ := hM
      exact (mobiusHomeomorph a b c d hdet).bijective
    have heq : h.choose = M ∘ OnePoint.map W := by
      funext z
      induction z using OnePoint.rec with
      | infty => exact hinfty
      | coe z => exact hfinite z
    rw [heq]
    exact hMi.comp (Equiv.optionCongr (Equiv.ofBijective W ⟨hWi, hWs⟩)).bijective
  · exact Function.bijective_id

/-- Existence (TT:346, "the unique q.c. mapping"): for `μ ∈ L∞(𝔻*)₁`, `w_μ` is the normalized solution. The plane
solution `W` of `extA μ` fixing `0, 1, ∞` is composed with the fractional linear map sending `W(-1), W(-i), W(1)` to
`-1, -i, 1`. -/
theorem wA_spec {μ : LinfStar} (hμ : μ ∈ LinfStarBall) : IsNormalizedA μ (wAS μ) := by
  have hex : ∃ w, IsNormalizedA μ w := by
    obtain ⟨W, hW, -, -⟩ := extA_normalized_plane_exists hμ
    obtain ⟨K, hK⟩ := hW.1
    have hWi : Function.Injective W :=
      fun _ _ he => hK.2.2.1.2.1 (mem_univ _) (mem_univ _) he
    have n12 : (-1 : ℂ) ≠ -I := by
      intro h
      have := congrArg Complex.re h
      norm_num at this
    have n13 : (-1 : ℂ) ≠ 1 := by norm_num
    have n23 : (-I : ℂ) ≠ 1 := by
      intro h
      have := congrArg Complex.re h
      norm_num at this
    obtain ⟨M, hM, m1, m2, m3⟩ := exists_mobius_three_points
      (fun h => n12 (hWi h)) (fun h => n13 (hWi h)) (fun h => n23 (hWi h)) n12 n13 n23
    exact ⟨M ∘ OnePoint.map W, M, hM, W, hW, fun z => rfl, rfl, m1, m2, m3⟩
  simpa only [wAS, dif_pos hex] using hex.choose_spec

/-- Uniqueness (TT:346): the normalized solution of Model A is unique. Plane uniqueness identifies the plane
solutions, and two fractional linear maps that agree at `W(-1), W(-i), W(1)` are equal. -/
theorem wA_unique {μ : LinfStar} (hμ : μ ∈ LinfStarBall) {w : ExtPlane → ExtPlane}
    (hw : IsNormalizedA μ w) : w = wAS μ := by
  have hA := wA_spec hμ
  obtain ⟨M, hM, W, hW, hwf, hwi, hm1, hmI, hm2⟩ := hw
  obtain ⟨N, hN, V, hV, hvf, hvi, hn1, hnI, hn2⟩ := hA
  have hVW : V = W := by
    apply thm13_5_uniqueness_plane hV.1 hW.1 hV.2.1 hW.2.1 ?_
      hV.2.2.1 hV.2.2.2.1 hW.2.2.1 hW.2.2.2.1
    filter_upwards [hV.2.2.2.2, hW.2.2.2.2] with z hz hz'
    exact hz.trans hz'.symm
  subst V
  obtain ⟨K, hK⟩ := hW.1
  have hWi : Function.Injective W :=
    fun _ _ he => hK.2.2.1.2.1 (mem_univ _) (mem_univ _) he
  have n12 : (-1 : ℂ) ≠ -I := by
    intro h
    have := congrArg Complex.re h
    norm_num at this
  have n13 : (-1 : ℂ) ≠ 1 := by norm_num
  have n23 : (-I : ℂ) ≠ 1 := by
    intro h
    have := congrArg Complex.re h
    norm_num at this
  have e1 : M ((W (-1) : ℂ) : ExtPlane) = N ((W (-1) : ℂ) : ExtPlane) :=
    (hwf (-1)).symm.trans (hm1.trans (hn1.symm.trans (hvf (-1))))
  have e2 : M ((W (-I) : ℂ) : ExtPlane) = N ((W (-I) : ℂ) : ExtPlane) :=
    (hwf (-I)).symm.trans (hmI.trans (hnI.symm.trans (hvf (-I))))
  have e3 : M ((W 1 : ℂ) : ExtPlane) = N ((W 1 : ℂ) : ExtPlane) :=
    (hwf 1).symm.trans (hm2.trans (hn2.symm.trans (hvf 1)))
  have hMN : M = N := mobius_eq_of_three_points hM hN (fun h => n12 (hWi h)) (fun h => n13 (hWi h))
    (fun h => n23 (hWi h)) e1 e2 e3
  funext z
  induction z using OnePoint.rec with
  | infty => rw [hwi, hvi, hMN]
  | coe z => rw [hwf z, hvf z, hMN]

/-- The three Model B jet normalizations determine a Möbius map uniquely
at the identity (TT:357). -/
theorem mobius_eq_id_of_normalized_jet {a b c d : ℂ} (hd : d ≠ 0)
    (h0 : mobiusFn a b c d 0 = 0)
    (h1 : deriv (mobiusFn a b c d) 0 = 1)
    (h2 : deriv (deriv (mobiusFn a b c d)) 0 = 0) :
    mobiusExt a b c d = id := by
  have hb : b = 0 := by
    have he : b / d = 0 := by simpa only [mobiusFn, mul_zero, zero_add] using h0
    exact (div_eq_zero_iff.mp he).resolve_right hd
  have hden : c * (0 : ℂ) + d ≠ 0 := by simpa using hd
  have hfirst := (hasDerivAt_mobius (a := a) (b := b) hden).deriv
  change deriv (mobiusFn a b c d) 0 = _ at hfirst
  rw [h1, hb] at hfirst
  have ha : a = d := by
    simp only [mul_zero, sub_zero, zero_add] at hfirst
    have he := (eq_div_iff (pow_ne_zero 2 hd)).mp hfirst
    apply mul_right_cancel₀ hd
    linear_combination -he
  have hnear : ∀ᶠ z : ℂ in 𝓝 0, c * z + d ≠ 0 := by
    exact ((continuousAt_const.mul continuousAt_id).add continuousAt_const).eventually_ne hden
  have hder : deriv (mobiusFn a b c d) =ᶠ[𝓝 (0 : ℂ)]
      (fun z => (a * d - b * c) / (c * z + d) ^ 2) := by
    filter_upwards [hnear] with z hz
    exact (hasDerivAt_mobius hz).deriv
  have hsecond := hder.deriv_eq.trans (hasDerivAt_mobius_deriv hden).deriv
  rw [h2, hb, ha] at hsecond
  have hc : c = 0 := by
    simp only [mul_zero, sub_zero, zero_add] at hsecond
    have he := (div_eq_zero_iff.mp hsecond.symm).resolve_right (pow_ne_zero 3 hd)
    have he' : c * d ^ 2 = 0 := by linear_combination -(1 / 2 : ℂ) * he
    exact (mul_eq_zero.mp he').resolve_right (pow_ne_zero 2 hd)
  subst a
  subst b
  subst c
  funext p
  induction p using OnePoint.rec with
  | infty => simp [mobiusExt]
  | coe z => simp [mobiusExt, hd]

/-- **Model B** (TT:355–363). `w : ℂ̄ → ℂ̄` is the normalized quasiconformal mapping of the Riemann sphere for
`μ ∈ L∞(𝔻*)`, with `μ` extended by zero outside `𝔻*`.
- The quasiconformal self-maps of `ℂ̄` with complex dilatation `extB μ` are exactly the maps `M ∘ W`, where `W` is a
  normalized plane solution (`LiZhongQC.IsNormalizedSolution`, fixing `0, 1, ∞`) and `M` is a Möbius map.
- The normalization is the welding normalization: `f = w|𝔻` is a (finite-valued) holomorphic function with
  `f(0) = 0`, `f'(0) = 1`, and `w` sends the pole `p_μ = w_μ⁻¹(∞)` of Model A to `∞`.
- **[CORRECTION 2026-10-25, user-approved]** The memoir normalizes by `f''(0) = 0`. That normalization can force the
  pole of the Möbius map into `w(𝔻)`: the univalent function `z(1 - 3z/4)/(1 - 1249 z²/1296)` has `f''(0) = -3/2` and
  takes the forced pole value `4/3` at `z = 9/10` (`collaboration/lean2_normalization_pole_diagnostic.lean`), and its
  analytic boundary makes a q.c. extension very likely. The normalization `w(∞) = ∞` is not a function of the class
  `[μ]` (`w_μ(∞)` is finite in general). With `w(p_μ) = ∞` the normalization always exists (`p_μ ∉ 𝔻̄`) and depends
  only on `w_μ|S¹`; for harmonic `μ`, `p_μ = ∞` (Lemma 1.5) and it agrees with the memoir. -/
def IsNormalizedB (μ : LinfStar) (w : ExtPlane → ExtPlane) : Prop :=
  ∃ M : ExtPlane → ExtPlane, IsMobius M ∧ ∃ W : ℂ → ℂ, IsNormalizedSolution W (extB μ) ∧
    (∀ z : ℂ, w z = M (W z)) ∧ w extInf = M extInf ∧
    ∃ f : ℂ → ℂ, (∀ z ∈ unitDisc, w z = (f z : ExtPlane)) ∧ f 0 = 0 ∧ deriv f 0 = 1 ∧
      w (Function.invFun (wAS μ) extInf) = extInf

/-- The normalized quasiconformal mapping `w^μ : ℂ̄ → ℂ̄` of Model B (TT:355). Junk value `id` when no solution
exists. -/
def wB (μ : LinfStar) : ExtPlane → ExtPlane :=
  if h : ∃ w, IsNormalizedB μ w then h.choose else id

/-- The chosen Model B map is bijective (TT:355): its defining predicate writes
it as a Möbius map after the sphere extension of a plane homeomorphism.
The fallback identity has the same property. -/
theorem wB_bijective (μ : LinfStar) : Function.Bijective (wB μ) := by
  unfold wB
  split_ifs with h
  · obtain ⟨M, hM, W, hW, hfinite, hinfty, _⟩ := h.choose_spec
    obtain ⟨K, hK⟩ := hW.1
    have hWi : Function.Injective W :=
      fun _ _ he => hK.2.2.1.2.1 (mem_univ _) (mem_univ _) he
    have hWs : Function.Surjective W :=
      Set.range_eq_univ.mp (by simpa only [Set.image_univ] using hW.2.1)
    have hMi : Function.Bijective M := by
      obtain ⟨a, b, c, d, hdet, rfl⟩ := hM
      exact (mobiusHomeomorph a b c d hdet).bijective
    have heq : h.choose = M ∘ OnePoint.map W := by
      funext z
      induction z using OnePoint.rec with
      | infty => exact hinfty
      | coe z => exact hfinite z
    rw [heq]
    exact hMi.comp (Equiv.optionCongr (Equiv.ofBijective W ⟨hWi, hWs⟩)).bijective
  · exact Function.bijective_id

/-- `f = w^μ|𝔻` as a function `ℂ → ℂ` (TT:357). Only its values on `𝔻` are meaningful. -/
def fB (μ : LinfStar) (z : ℂ) : ℂ := finPart (wB μ z)

/-- First and second derivatives after Möbius normalization of an analytic
germ (TT:357). The denominator is required nonzero at the basepoint. -/
theorem mobius_comp_first_second {F : ℂ → ℂ} {x a b c d : ℂ}
    (hF : AnalyticAt ℂ F x) (hd : c * F x + d ≠ 0) :
    deriv (fun z => mobiusFn a b c d (F z)) x =
        ((a * d - b * c) / (c * F x + d) ^ 2) * deriv F x ∧
      deriv (deriv (fun z => mobiusFn a b c d (F z))) x =
        (-(2 * c * (a * d - b * c)) / (c * F x + d) ^ 3) * (deriv F x) ^ 2 +
        ((a * d - b * c) / (c * F x + d) ^ 2) * deriv (deriv F) x := by
  have hfirst := (hasDerivAt_mobius (a := a) (b := b) hd).comp x hF.differentiableAt.hasDerivAt
  refine ⟨hfirst.deriv, ?_⟩
  have hnear : ∀ᶠ z in 𝓝 x, c * F z + d ≠ 0 :=
    (hF.continuousAt.const_mul c |>.add_const d).eventually_ne hd
  have he : deriv (fun z => mobiusFn a b c d (F z)) =ᶠ[𝓝 x]
      (fun z => ((a * d - b * c) / (c * F z + d) ^ 2) * deriv F z) := by
    filter_upwards [hF.eventually_analyticAt, hnear] with z hz hd'
    exact ((hasDerivAt_mobius hd').comp z hz.differentiableAt.hasDerivAt).deriv
  have hm := (hasDerivAt_mobius_deriv (a := a) (b := b) hd).comp x
    hF.differentiableAt.hasDerivAt
  have hp := hm.mul hF.deriv.differentiableAt.hasDerivAt
  calc
    _ = deriv (fun z => ((a * d - b * c) / (c * F z + d) ^ 2) * deriv F z) x := he.deriv_eq
    _ = _ := by
      convert hp.deriv using 1
      · rfl
      · dsimp only [Function.comp_apply]
        ring

/-- The Model B normalizations determine the ratios of the Möbius
coefficients from the first two derivatives of the plane solution (TT:357). -/
theorem normalized_mobius_comp_parameters {F : ℂ → ℂ} {a b c d : ℂ}
    (hF : AnalyticAt ℂ F 0) (hF0 : F 0 = 0) (hd : d ≠ 0)
    (h0 : mobiusFn a b c d (F 0) = 0)
    (h1 : deriv (fun z => mobiusFn a b c d (F z)) 0 = 1)
    (h2 : deriv (deriv (fun z => mobiusFn a b c d (F z))) 0 = 0) :
    b = 0 ∧ a * deriv F 0 = d ∧
      2 * c * (deriv F 0) ^ 2 = d * deriv (deriv F) 0 := by
  have hb : b = 0 := by
    have he : b / d = 0 := by simpa only [hF0, mobiusFn, mul_zero, zero_add] using h0
    exact (div_eq_zero_iff.mp he).resolve_right hd
  have hden : c * F 0 + d ≠ 0 := by simpa [hF0] using hd
  obtain ⟨he1, he2⟩ := mobius_comp_first_second (a := a) (b := b) hF hden
  rw [h1, hF0, hb] at he1
  rw [h2, hF0, hb] at he2
  simp only [mul_zero, zero_mul, sub_zero, zero_add] at he1 he2
  have hquot : a * d / d ^ 2 = a / d := by field_simp
  rw [hquot] at he1
  have ha : a * deriv F 0 = d := by
    calc
      _ = (a / d * deriv F 0) * d := by field_simp
      _ = d := by rw [← he1, one_mul]
  have ha0 : a ≠ 0 := by
    intro he
    apply hd
    simpa [he] using ha.symm
  have hfact : -(2 * c * (a * d)) / d ^ 3 * deriv F 0 ^ 2 +
      (a * d / d ^ 2) * deriv (deriv F) 0 =
      (a / d ^ 2) * (d * deriv (deriv F) 0 - 2 * c * deriv F 0 ^ 2) := by
    field_simp
    <;> ring
  rw [hfact] at he2
  have hz : d * deriv (deriv F) 0 - 2 * c * deriv F 0 ^ 2 = 0 :=
    (mul_eq_zero.mp he2.symm).resolve_left (div_ne_zero ha0 (pow_ne_zero 2 hd))
  exact ⟨hb, ha, (sub_eq_zero.mp hz).symm⟩

/-- Normalize the lower-right Möbius coefficient to one without changing
the sphere map (TT:357). -/
theorem mobius_div_normalization {a b c d : ℂ} (hd : d ≠ 0) :
    mobiusExt a b c d = mobiusExt (a / d) (b / d) (c / d) 1 := by
  funext p
  induction p using OnePoint.rec with
  | infty =>
    by_cases hc : c = 0
    · simp [mobiusExt, hc]
    · rw [mobiusExt_infty_of_ne hc, mobiusExt_infty_of_ne (div_ne_zero hc hd)]
      congr 1
      field_simp
  | coe z =>
    have he : c / d * z + 1 = (c * z + d) / d := by field_simp
    by_cases hz : c * z + d = 0
    · rw [mobiusExt_coe_of_eq_zero hz, mobiusExt_coe_of_eq_zero (by rw [he, hz, zero_div])]
    · have hz' : c / d * z + 1 ≠ 0 := by rw [he]; exact div_ne_zero hz hd
      rw [mobiusExt_coe hz, mobiusExt_coe hz']
      congr 1
      dsimp [mobiusFn]
      rw [he]
      field_simp
      <;> ring

/-- Two Möbius postcompositions of the same analytic germ with the Model B
normalizations coincide on the entire sphere (TT:357). -/
theorem normalized_mobius_comp_unique {F : ℂ → ℂ} {a b c d a' b' c' d' : ℂ}
    (hF : AnalyticAt ℂ F 0) (hF0 : F 0 = 0) (hd : d ≠ 0) (hd' : d' ≠ 0)
    (h0 : mobiusFn a b c d (F 0) = 0)
    (h1 : deriv (fun z => mobiusFn a b c d (F z)) 0 = 1)
    (h2 : deriv (deriv (fun z => mobiusFn a b c d (F z))) 0 = 0)
    (h0' : mobiusFn a' b' c' d' (F 0) = 0)
    (h1' : deriv (fun z => mobiusFn a' b' c' d' (F z)) 0 = 1)
    (h2' : deriv (deriv (fun z => mobiusFn a' b' c' d' (F z))) 0 = 0) :
    mobiusExt a b c d = mobiusExt a' b' c' d' := by
  obtain ⟨hb, ha, hc⟩ := normalized_mobius_comp_parameters hF hF0 hd h0 h1 h2
  obtain ⟨hb', ha', hc'⟩ := normalized_mobius_comp_parameters hF hF0 hd' h0' h1' h2'
  have hp : deriv F 0 ≠ 0 := by
    intro he
    apply hd
    simpa [he] using ha.symm
  rw [mobius_div_normalization hd, mobius_div_normalization hd', hb, hb', zero_div]
  simp only [zero_div]
  congr 1
  · apply (div_eq_div_iff hd hd').mpr
    apply mul_right_cancel₀ hp
    linear_combination d' * ha - d * ha'
  · apply (div_eq_div_iff hd hd').mpr
    apply mul_right_cancel₀ (mul_ne_zero (by norm_num : (2 : ℂ) ≠ 0) (pow_ne_zero 2 hp))
    linear_combination d' * hc - d * hc'

/-- A plane solution of the zero extension is holomorphic on the disk
(Model B, TT:355–357). -/
theorem extB_solution_holomorphic {μ : LinfStar} {W : ℂ → ℂ}
    (hW : IsNormalizedSolution W (extB μ)) : DifferentiableOn ℂ W unitDisc := by
  obtain ⟨⟨K, hK⟩, _, _, _, hchar⟩ := hW
  have hzero : ∀ᵐ z ∂(volume.restrict unitDisc), complexDilatation W z = 0 := by
    filter_upwards [ae_restrict_of_ae hchar,
      self_mem_ae_restrict (show MeasurableSet unitDisc from isOpen_ball.measurableSet)]
      with z hz hzD
    rw [hz, extB]
    apply indicator_of_notMem
    intro hzE
    have hlt : ‖z‖ < 1 := mem_ball_zero_iff.mp hzD
    have hgt : 1 < ‖z‖ := hzE
    linarith
  exact nx_differentiableOn_of_dilatation_zero
    (nx_isKQC_restrict hK isOpen_ball (subset_univ _)) hzero

/-- With the welding normalization (`w` sends the point `p` to `∞`, `f(0) = 0`, `f'(0) = 1`), the Möbius map of
Model B is determined by the plane solution `W` and `p`: it is `z ↦ z / (W'(0) (1 - z / W(p)))` (TT:357, corrected
normalization; `-(finPart ∞)⁻¹ = 0` covers `W(p) = ∞`). -/
theorem modelB_mobius_pole {W : ℂ → ℂ} (hWa : AnalyticAt ℂ W 0) (hW0 : W 0 = 0) {a b c d : ℂ}
    (hdet : a * d - b * c ≠ 0) {w : ExtPlane → ExtPlane} {f : ℂ → ℂ} {p : ExtPlane}
    (hwf : ∀ z : ℂ, w z = mobiusExt a b c d (W z)) (hwi : w extInf = mobiusExt a b c d extInf)
    (hf : ∀ z ∈ unitDisc, w z = (f z : ExtPlane)) (hf0 : f 0 = 0) (hf1 : deriv f 0 = 1)
    (hp : w p = extInf) :
    deriv W 0 ≠ 0 ∧ mobiusExt a b c d =
      mobiusExt (deriv W 0)⁻¹ 0 (-(finPart (OnePoint.map W p))⁻¹) 1 := by
  have hz0 : (0 : ℂ) ∈ unitDisc := by simp [unitDisc]
  have h0 := (hwf 0).symm.trans (hf 0 hz0)
  rw [hW0, hf0] at h0
  have hd : d ≠ 0 := by
    intro hd0
    rw [mobiusExt_coe_of_eq_zero (by simpa using hd0)] at h0
    exact OnePoint.infty_ne_coe _ h0
  have hb : b = 0 := by
    rw [mobiusExt_coe (by simpa using hd)] at h0
    have h' : mobiusFn a b c d 0 = 0 := OnePoint.coe_injective h0
    simp only [mobiusFn, mul_zero, zero_add] at h'
    exact (div_eq_zero_iff.mp h').resolve_right hd
  have hM : mobiusExt a b c d = mobiusExt (a / d) 0 (c / d) 1 := by
    rw [mobius_div_normalization hd, hb, zero_div]
  generalize a / d = a' at hM
  generalize c / d = c' at hM
  have hwf' : ∀ z : ℂ, w z = mobiusExt a' 0 c' 1 (W z) := fun z => by rw [hwf z, hM]
  have hwi' : w extInf = mobiusExt a' 0 c' 1 extInf := by rw [hwi, hM]
  have hnd : ∀ z ∈ unitDisc, c' * W z + 1 ≠ 0 := by
    intro z hz he
    have h := (hwf' z).symm.trans (hf z hz)
    rw [mobiusExt_coe_of_eq_zero he] at h
    exact OnePoint.infty_ne_coe _ h
  have hev : f =ᶠ[𝓝 (0 : ℂ)] (mobiusFn a' 0 c' 1 ∘ W) := by
    filter_upwards [isOpen_ball.mem_nhds hz0] with z hz
    have h := (hwf' z).symm.trans (hf z hz)
    rw [mobiusExt_coe (hnd z hz)] at h
    exact (OnePoint.coe_injective h).symm
  have hden0 : c' * W 0 + 1 ≠ 0 := hnd 0 hz0
  have hcomp := (hasDerivAt_mobius (a := a') (b := 0) hden0).comp (0 : ℂ)
    hWa.differentiableAt.hasDerivAt
  have hderiv : a' * deriv W 0 = 1 := by
    have h3 : deriv f 0 = a' * deriv W 0 := by
      have hd := hcomp.deriv
      change deriv (mobiusFn a' 0 c' 1 ∘ W) 0 = _ at hd
      rw [hev.deriv_eq, hd, hW0]
      simp
    rw [← h3, hf1]
  have hne : deriv W 0 ≠ 0 := by
    intro h
    rw [h, mul_zero] at hderiv
    exact zero_ne_one hderiv
  have ha' : a' = (deriv W 0)⁻¹ := eq_inv_of_mul_eq_one_left hderiv
  have hq : mobiusExt a' 0 c' 1 (OnePoint.map W p) = extInf := by
    revert hp
    induction p using OnePoint.rec with
    | infty =>
      intro hp
      show mobiusExt a' 0 c' 1 extInf = extInf
      rw [← hwi', hp]
    | coe z =>
      intro hp
      show mobiusExt a' 0 c' 1 ((W z : ℂ) : ExtPlane) = extInf
      rw [← hwf' z, hp]
  refine ⟨hne, ?_⟩
  generalize OnePoint.map W p = q at hq ⊢
  rw [hM, ha']
  induction q using OnePoint.rec with
  | infty =>
    have hc : c' = 0 := by
      by_contra hc
      rw [mobiusExt_infty_of_ne hc] at hq
      exact OnePoint.coe_ne_infty _ hq
    subst hc
    simp [finPart]
  | coe x =>
    have hx : c' * x + 1 = 0 := by
      by_contra hx
      rw [mobiusExt_coe hx] at hq
      exact OnePoint.coe_ne_infty _ hq
    have hx0 : x ≠ 0 := by
      rintro rfl
      simp at hx
    have hc : c' = -(x)⁻¹ := by
      field_simp
      linear_combination hx
    rw [hc]
    simp [finPart]

/-- Uniqueness of Model B whenever two normalized solutions exist
(TT:355–357). The proof uses plane uniqueness and the welding normalization, which makes the Möbius postcomposition
`z ↦ z / (W'(0) (1 - z / W(p)))` determined by `W` and the pole `p` of `w_μ`. -/
theorem IsNormalizedB.unique {μ : LinfStar} {w v : ExtPlane → ExtPlane}
    (hw : IsNormalizedB μ w) (hv : IsNormalizedB μ v) : w = v := by
  obtain ⟨M, hM, W, hW, hwf, hwi, f, hf, hf0, hf1, hfp⟩ := hw
  obtain ⟨N, hN, V, hV, hvf, hvi, g, hg, hg0, hg1, hgp⟩ := hv
  have hVW : V = W := by
    apply thm13_5_uniqueness_plane hV.1 hW.1 hV.2.1 hW.2.1 ?_
      hV.2.2.1 hV.2.2.2.1 hW.2.2.1 hW.2.2.2.1
    filter_upwards [hV.2.2.2.2, hW.2.2.2.2] with z hz hz'
    exact hz.trans hz'.symm
  subst V
  obtain ⟨a, b, c, d, hdet, rfl⟩ := hM
  obtain ⟨a', b', c', d', hdet', rfl⟩ := hN
  have hz0 : (0 : ℂ) ∈ unitDisc := by simp [unitDisc]
  have hW0 : W 0 = 0 := hW.2.2.1
  have hWa : AnalyticAt ℂ W 0 :=
    (extB_solution_holomorphic hW).analyticAt (isOpen_ball.mem_nhds hz0)
  have h1 := modelB_mobius_pole hWa hW0 hdet hwf hwi hf hf0 hf1 hfp
  have h2 := modelB_mobius_pole hWa hW0 hdet' hvf hvi hg hg0 hg1 hgp
  funext z
  induction z using OnePoint.rec with
  | infty => rw [hwi, hvi, h1.2, h2.2]
  | coe z => rw [hwf z, hvf z, h1.2, h2.2]

/-- Any normalized Model B solution equals the chosen one (TT:355–357).
The hypothesis supplies existence; this does not invoke `wB_spec`. -/
theorem wB_unique {μ : LinfStar} {w : ExtPlane → ExtPlane}
    (hw : IsNormalizedB μ w) : w = wB μ := by
  have hex : ∃ v, IsNormalizedB μ v := ⟨w, hw⟩
  have hB : IsNormalizedB μ (wB μ) := by
    simpa only [wB, dif_pos hex] using hex.choose_spec
  exact hw.unique hB

/-! ## Reflection symmetry of Model A and existence of Model B -/

/-- The reflection extension is symmetric: `extA μ z = conj (extA μ (refl z)) z² / conj z²` off `S¹` and `0`
(1.1, TT:342–346). -/
theorem extA_refl_symm (μ : LinfStar) {z : ℂ} (h1 : ‖z‖ ≠ 1) (h0 : z ≠ 0) :
    conj (extA μ (refl z)) * z ^ 2 / conj z ^ 2 = extA μ z := by
  have hcz : conj z ≠ 0 := (map_ne_zero conj).mpr h0
  have hn : ‖refl z‖ = ‖z‖⁻¹ := norm_refl z
  rcases lt_or_gt_of_ne h1 with hlt | hgt
  · -- `z ∈ 𝔻`: the reflected point lies in `𝔻*`
    have hr : 1 < ‖refl z‖ := by
      rw [hn]
      exact one_lt_inv₀ (norm_pos_iff.mpr h0) |>.mpr hlt
    have hnot : ¬ 1 < ‖z‖ := not_lt.mpr hlt.le
    simp only [extA, if_pos hr, if_neg hnot, if_pos hlt]
  · -- `z ∈ 𝔻*`
    have hr : ‖refl z‖ < 1 := by
      rw [hn]
      exact inv_lt_one_of_one_lt₀ hgt
    have hnot : ¬ 1 < ‖refl z‖ := not_lt.mpr hr.le
    simp only [extA, if_pos hgt, if_neg hnot, if_pos hr]
    have hrr : refl (refl z) = z := refl_involutive z
    rw [hrr]
    simp only [refl, map_div₀, map_mul, map_pow, Complex.conj_conj, map_inv₀]
    field_simp

/-- The plane solution of the symmetric coefficient `extA μ` normalized at `0, 1, ∞` commutes with the reflection
`refl` (uniqueness applied to `refl ∘ W ∘ refl`; TT:346–350). -/
theorem normalized_solution_refl_comm {μ : LinfStar} {W : ℂ → ℂ} (hW : IsNormalizedSolution W (extA μ))
    (z : ℂ) : W (refl z) = refl (W z) := by
  obtain ⟨⟨K, hK⟩, hs, h0, h1, hd⟩ := hW
  set f₁ : ℂ → ℂ := fun w => conj (W (conj w)) with hf₁
  have hf₁K : IsKQC f₁ univ K := by
    have h := abR_x_isKQC_conj hK
    rwa [preimage_univ] at h
  have hf₁s : f₁ '' univ = univ := by
    refine eq_univ_of_forall fun w => ?_
    have hw : conj w ∈ W '' univ := by
      rw [hs]
      exact mem_univ _
    obtain ⟨v, -, hv⟩ := hw
    exact ⟨conj v, mem_univ _, by simp only [hf₁, Complex.conj_conj, hv]⟩
  have hf₁0 : f₁ 0 = 0 := by simp [hf₁, h0]
  have hf₁1 : f₁ 1 = 1 := by simp [hf₁, h1]
  have hf₁i : Function.Injective f₁ := fun a b hab =>
    hf₁K.2.2.1.2.1 (mem_univ a) (mem_univ b) hab
  have hf₁c : Continuous f₁ := continuousOn_univ.1 hf₁K.2.2.1.1
  have hGh := bg2_m1_isHomeomorphOnto hf₁K hf₁s 0 1 0 one_ne_zero
  have hGK0 := bg2_m1_isKQC hf₁K 0 1 0 one_ne_zero
  set G : ℂ → ℂ := fun z => (f₁ (0 + 1 * (z + 0)⁻¹) - f₁ 0)⁻¹ with hG
  have hGK : IsKQC G univ K := b4_isKQC_univ_of_punctured hGh hGK0
  have hGs : G '' univ = univ := hGh.2.2.1
  have hG0 : G 0 = 0 := by simp [hG, hf₁0]
  have hG1 : G 1 = 1 := by simp [hG, hf₁1, hf₁0]
  have heq : G = (fun w : ℂ => w⁻¹) ∘ (f₁ ∘ fun w : ℂ => w⁻¹) := by
    funext w
    simp [hG, hf₁0]
  have hinvd : ∀ x : ℂ, x ≠ 0 → DifferentiableAt ℂ (fun w : ℂ => w⁻¹) x :=
    fun x hx => differentiableAt_inv hx
  have hGd : ∀ᵐ z, complexDilatation G z = extA μ z := by
    have hrefl : ∀ᵐ z, complexDilatation W (refl z) = extA μ (refl z) := ae_refl hd
    have hcirc : ∀ᵐ z : ℂ, ‖z‖ ≠ 1 := by
      have hnull : volume (sphere (0 : ℂ) 1) = 0 := Measure.addHaar_sphere volume 0 1
      filter_upwards [measure_eq_zero_iff_ae_notMem.1 hnull] with z hz
      exact fun h => hz (by simpa using h)
    filter_upwards [hrefl, hcirc, compl_mem_ae_iff.mpr (measure_singleton (0 : ℂ))] with z hz h1' h0'
    have h0'' : z ≠ 0 := h0'
    have hgz : f₁ z⁻¹ ≠ 0 := by
      intro h
      exact inv_ne_zero h0'' (hf₁i (h.trans hf₁0.symm))
    have hc1 : complexDilatation G z = complexDilatation (f₁ ∘ fun w : ℂ => w⁻¹) z := by
      rw [heq]
      exact s23_dilatation_comp_left (g := f₁ ∘ fun w : ℂ => w⁻¹) (h := fun w : ℂ => w⁻¹)
        (k := fun w : ℂ => w⁻¹) (hf₁c.continuousAt.comp (continuousAt_inv₀ h0''))
        (hinvd _ hgz) (hinvd _ (inv_ne_zero hgz)) (Eventually.of_forall inv_inv)
    have hc2 : complexDilatation (f₁ ∘ fun w : ℂ => w⁻¹) z =
        complexDilatation f₁ z⁻¹ * (conj (deriv (fun w : ℂ => w⁻¹) z) / deriv (fun w : ℂ => w⁻¹) z) :=
      s23_dilatation_comp_right (g := f₁) (T := fun w : ℂ => w⁻¹) (S := fun w : ℂ => w⁻¹)
        (hinvd z h0'') (hinvd _ (inv_ne_zero h0'')) (Eventually.of_forall inv_inv)
        (Eventually.of_forall inv_inv)
    have hc3 : complexDilatation f₁ z⁻¹ = conj (extA μ (refl z)) := by
      have := bg_dilatation_conj W z⁻¹
      rw [← hz]
      simpa [hf₁, refl] using this
    rw [hc1, hc2, hc3, deriv_inv, ← extA_refl_symm μ h1' h0'']
    simp only [map_neg, map_inv₀, map_pow]
    field_simp
  have hGW : G = W := by
    refine thm13_5_uniqueness_plane ⟨K, hGK⟩ ⟨K, hK⟩ hGs hs ?_ hG0 hG1 h0 h1
    filter_upwards [hGd, hd] with z a b
    exact a.trans b.symm
  have hz' : W z = refl (W (refl z)) := by
    have h := congrFun hGW z
    simp only [hG, hf₁0, sub_zero, zero_add, one_mul, add_zero] at h
    rw [← h]
    simp [hf₁, refl]
  rw [hz']
  exact (refl_involutive _).symm

theorem normalized_solution_injective {μ : LinfStar} {W : ℂ → ℂ} (hW : IsNormalizedSolution W (extA μ)) :
    Function.Injective W := by
  obtain ⟨⟨K, hK⟩, -⟩ := hW
  exact fun _ _ he => hK.2.2.1.2.1 (mem_univ _) (mem_univ _) he

theorem normalized_solution_continuous {μ : LinfStar} {W : ℂ → ℂ} (hW : IsNormalizedSolution W (extA μ)) :
    Continuous W := by
  obtain ⟨⟨K, hK⟩, -⟩ := hW
  exact continuousOn_univ.1 hK.2.2.1.1

theorem normalized_solution_ne_zero {μ : LinfStar} {W : ℂ → ℂ} (hW : IsNormalizedSolution W (extA μ))
    {z : ℂ} (hz : z ≠ 0) : W z ≠ 0 := by
  intro h
  exact hz (normalized_solution_injective hW (h.trans hW.2.2.1.symm))

/-- `W` maps the unit circle into itself (TT:350). -/
theorem normalized_solution_circle {μ : LinfStar} {W : ℂ → ℂ} (hW : IsNormalizedSolution W (extA μ))
    {z : ℂ} (hz : ‖z‖ = 1) : ‖W z‖ = 1 := by
  have hz0 : z ≠ 0 := norm_ne_zero_iff.mp (by rw [hz]; exact one_ne_zero)
  have hrz : refl z = z := abR_t_inv_conj_of_norm_one hz
  have h := normalized_solution_refl_comm hW z
  rw [hrz] at h
  have hw0 : W z ≠ 0 := normalized_solution_ne_zero hW hz0
  have hcw : conj (W z) ≠ 0 := (map_ne_zero conj).mpr hw0
  have h1 : W z * conj (W z) = 1 := by
    have h' : W z = (conj (W z))⁻¹ := h
    nth_rewrite 1 [h']
    exact inv_mul_cancel₀ hcw
  rw [Complex.mul_conj'] at h1
  have h2 : ‖W z‖ ^ 2 = 1 := by exact_mod_cast h1
  have h3 := norm_nonneg (W z)
  nlinarith

/-- A point is on the unit circle iff its image is (TT:350). -/
theorem normalized_solution_circle_iff {μ : LinfStar} {W : ℂ → ℂ} (hW : IsNormalizedSolution W (extA μ))
    {z : ℂ} (hz : ‖W z‖ = 1) : ‖z‖ = 1 := by
  have hz0 : z ≠ 0 := by
    rintro rfl
    rw [hW.2.2.1, norm_zero] at hz
    exact zero_ne_one hz
  have hrw : refl (W z) = W z := abR_t_inv_conj_of_norm_one hz
  have h := normalized_solution_refl_comm hW z
  rw [hrw] at h
  have h' : refl z = z := normalized_solution_injective hW h
  have hn : ‖z‖⁻¹ = ‖z‖ := by
    have := congrArg norm h'
    rwa [norm_refl] at this
  have hpos : 0 < ‖z‖ := norm_pos_iff.mpr hz0
  have : ‖z‖ ^ 2 = 1 := by
    field_simp at hn
    linarith
  nlinarith

/-- `W` maps the unit disk into itself (TT:350). -/
theorem normalized_solution_disc {μ : LinfStar} {W : ℂ → ℂ} (hW : IsNormalizedSolution W (extA μ))
    {z : ℂ} (hz : ‖z‖ < 1) : ‖W z‖ < 1 := by
  by_contra hge
  push_neg at hge
  have hconn : IsPreconnected (ball (0 : ℂ) 1) := (convex_ball (0 : ℂ) 1).isPreconnected
  have hcont : ContinuousOn (fun y => ‖W y‖) (ball (0 : ℂ) 1) :=
    (normalized_solution_continuous hW).norm.continuousOn
  have hz' : z ∈ ball (0 : ℂ) 1 := mem_ball_zero_iff.mpr hz
  have h0 : (0 : ℂ) ∈ ball (0 : ℂ) 1 := mem_ball_self one_pos
  have hmem : (1 : ℝ) ∈ Icc ‖W 0‖ ‖W z‖ := by
    refine ⟨?_, hge⟩
    rw [hW.2.2.1, norm_zero]
    exact zero_le_one
  obtain ⟨y, hy, hyW⟩ := hconn.intermediate_value h0 hz' hcont hmem
  have := normalized_solution_circle_iff hW hyW
  have hy' := mem_ball_zero_iff.mp hy
  linarith

/-- `W` maps the exterior of the unit disk into itself (TT:350). -/
theorem normalized_solution_exterior {μ : LinfStar} {W : ℂ → ℂ} (hW : IsNormalizedSolution W (extA μ))
    {z : ℂ} (hz : 1 < ‖z‖) : 1 < ‖W z‖ := by
  have hz0 : z ≠ 0 := norm_ne_zero_iff.mp (by linarith)
  have hr : ‖refl z‖ < 1 := by
    rw [norm_refl]
    exact inv_lt_one_of_one_lt₀ hz
  have h1 := normalized_solution_disc hW hr
  rw [normalized_solution_refl_comm hW z, norm_refl] at h1
  have hw0 : 0 < ‖W z‖ := norm_pos_iff.mpr (normalized_solution_ne_zero hW hz0)
  by_contra hle
  push_neg at hle
  have := one_le_inv₀ hw0 |>.mpr hle
  linarith

theorem inv_sub_one_re {s : ℂ} (hs : ‖s‖ = 1) (h1 : s ≠ 1) : ((s - 1)⁻¹).re = -1 / 2 := by
  have hn : s.re ^ 2 + s.im ^ 2 = 1 := by
    have h := Complex.sq_norm s
    rw [Complex.normSq_apply, hs] at h
    nlinarith
  have hre : s.re ≠ 1 := by
    intro h
    apply h1
    have him : s.im = 0 := by nlinarith
    exact Complex.ext (by simp [h]) (by simp [him])
  have hd : (s.re - 1) * (s.re - 1) + s.im * s.im = 2 - 2 * s.re := by nlinarith [hn]
  have hne : (2 : ℝ) - 2 * s.re ≠ 0 := by
    intro h
    exact hre (by linarith)
  rw [Complex.inv_re, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im, sub_zero]
  rw [hd, div_eq_iff hne]
  ring

theorem kappa_eq {s : ℂ} (hs : s ≠ 1) : I * (1 + s) / (1 - s) = -2 * I * (s - 1)⁻¹ - I := by
  have h1 : s - 1 ≠ 0 := sub_ne_zero.mpr hs
  have h2 : 1 - s ≠ 0 := sub_ne_zero.mpr hs.symm
  field_simp
  ring

/-- Orientation of the boundary values of `W` (TT:346, normalization of Model A): the Cayley images
`κ(W(-1))`, `κ(W(-i))` are real and in increasing order, `κ(s) = i(1 + s)/(1 - s)`. -/
theorem normalized_solution_orient {μ : LinfStar} {W : ℂ → ℂ} (hW : IsNormalizedSolution W (extA μ)) :
    ∃ t : ℝ, 0 < t ∧
      I * (1 + W (-I)) / (1 - W (-I)) - I * (1 + W (-1)) / (1 - W (-1)) = ((2 * t : ℝ) : ℂ) := by
  have hinj := normalized_solution_injective hW
  have hW1 : W 1 = 1 := hW.2.2.2.1
  have hW0 : W 0 = 0 := hW.2.2.1
  obtain ⟨⟨K, hK⟩, hs, -, -, -⟩ := id hW
  have hs1 : ‖W (-1)‖ = 1 := normalized_solution_circle hW (by simp)
  have hs2 : ‖W (-I)‖ = 1 := normalized_solution_circle hW (by simp)
  have hne1 : W (-1) ≠ 1 := by
    intro h
    have := hinj (h.trans hW1.symm)
    norm_num at this
  have hne2 : W (-I) ≠ 1 := by
    intro h
    have := congrArg Complex.re (hinj (h.trans hW1.symm))
    norm_num at this
  have hq : (-2 * I : ℂ) ≠ 0 := mul_ne_zero (by norm_num) Complex.I_ne_zero
  have hGh := bg2_m1_isHomeomorphOnto hK hs 1 (-2 * I) I hq
  have hGK0 := bg2_m1_isKQC hK 1 (-2 * I) I hq
  set G : ℂ → ℂ := fun z => (W (1 + (-2 * I) * (z + I)⁻¹) - W 1)⁻¹ with hG
  have hGK : IsKQC G univ K := b4_isKQC_univ_of_punctured hGh hGK0
  have hGs : G '' univ = univ := hGh.2.2.1
  have hGinj : Function.Injective G := fun a b hab => hGh.2.1 (mem_univ a) (mem_univ b) hab
  have e0 : (1 : ℂ) + (-2 * I) * (0 + I)⁻¹ = -1 := by
    rw [zero_add, Complex.inv_I]
    linear_combination 2 * Complex.I_sq
  have e1 : (1 : ℂ) + (-2 * I) * (1 + I)⁻¹ = -I := by
    have h : (1 + I) * ((1 - I) / 2) = 1 := by linear_combination (-1 / 2 : ℂ) * Complex.I_sq
    rw [inv_eq_of_mul_eq_one_right h]
    linear_combination Complex.I_sq
  have eI : (1 : ℂ) + (-2 * I) * (I + I)⁻¹ = 0 := by
    have h2I : (I + I : ℂ) ≠ 0 := by
      rw [← two_mul]
      exact mul_ne_zero two_ne_zero Complex.I_ne_zero
    field_simp
    ring
  have hG0 : G 0 = (W (-1) - 1)⁻¹ := by
    show (W (1 + (-2 * I) * (0 + I)⁻¹) - W 1)⁻¹ = _
    rw [e0, hW1]
  have hG1 : G 1 = (W (-I) - 1)⁻¹ := by
    show (W (1 + (-2 * I) * (1 + I)⁻¹) - W 1)⁻¹ = _
    rw [e1, hW1]
  have hGI : G I = -1 := by
    show (W (1 + (-2 * I) * (I + I)⁻¹) - W 1)⁻¹ = _
    rw [eI, hW0, hW1]
    norm_num
  have hGmI : G (-I) = 0 := by
    show (W (1 + (-2 * I) * (-I + I)⁻¹) - W 1)⁻¹ = _
    simp [hW1]
  have hG0re : (G 0).re = -1 / 2 := by rw [hG0]; exact inv_sub_one_re hs1 hne1
  have hG1re : (G 1).re = -1 / 2 := by rw [hG1]; exact inv_sub_one_re hs2 hne2
  have hD : G 1 - G 0 ≠ 0 := by
    intro h
    have := hGinj (sub_eq_zero.mp h)
    norm_num at this
  have hDre : (G 1 - G 0).re = 0 := by rw [Complex.sub_re, hG1re, hG0re]; ring
  obtain ⟨t, ht⟩ : ∃ t : ℝ, t = (G 1 - G 0).im := ⟨_, rfl⟩
  have hDeq : G 1 - G 0 = (t : ℂ) * I := Complex.ext (by simp [hDre]) (by simp [ht])
  have hc0 : conj (G 0) = -1 - G 0 :=
    Complex.ext (by simp [hG0re]; ring) (by simp)
  have hcD : conj (G 1 - G 0) = -(G 1 - G 0) :=
    Complex.ext (by simp [hG0re, hG1re] <;> ring) (by simp <;> ring)
  have hGsym : ∀ z, G (conj z) = -1 - conj (G z) := by
    intro z
    by_cases hzI : z = I
    · subst hzI
      rw [Complex.conj_I, hGmI, hGI]
      simp
    by_cases hzmI : z = -I
    · subst hzmI
      rw [map_neg, Complex.conj_I, neg_neg, hGI, hGmI]
      simp
    have hz1 : z + I ≠ 0 := fun h => hzmI (eq_neg_of_add_eq_zero_left h)
    have hz2 : conj z + I ≠ 0 := by
      intro h
      apply hzI
      have h' := Complex.ext_iff.mp h
      simp at h'
      exact Complex.ext (by simp [h'.1]) (by simp; linarith [h'.2])
    have hz3 : conj z - I ≠ 0 := by
      intro h
      apply hzmI
      have h' := Complex.ext_iff.mp h
      simp at h'
      exact Complex.ext (by simp [h'.1]) (by simp; linarith [h'.2])
    have hz3' : conj z + -I ≠ 0 := by rwa [← sub_eq_add_neg]
    set u : ℂ := 1 + (-2 * I) * (z + I)⁻¹ with hu
    have hu' : u = (z - I) / (z + I) := by
      rw [hu]
      field_simp
      ring
    have hu0 : u ≠ 0 := by
      rw [hu']
      exact div_ne_zero (sub_ne_zero.mpr hzI) hz1
    have hu1 : u ≠ 1 := by
      rw [hu']
      intro h
      rw [div_eq_one_iff_eq hz1] at h
      have : (I : ℂ) = -I := by linear_combination -h
      exact Complex.I_ne_zero (by linear_combination (1 / 2 : ℂ) * this)
    have hru : 1 + (-2 * I) * (conj z + I)⁻¹ = refl u := by
      rw [hu']
      simp only [refl, map_div₀, map_sub, map_add, Complex.conj_conj, Complex.conj_I]
      field_simp
      linear_combination (-(conj z - I)) * (mul_inv_cancel₀ hz2)
    have hv0 : W u ≠ 0 := normalized_solution_ne_zero hW hu0
    have hv1 : W u ≠ 1 := fun h => hu1 (hinj (h.trans hW1.symm))
    have hcv0 : conj (W u) ≠ 0 := (map_ne_zero conj).mpr hv0
    have hcv1' : 1 - conj (W u) ≠ 0 := by
      intro h
      apply hv1
      have := congrArg conj (sub_eq_zero.mp h).symm
      simpa using this
    have hcv1 : conj (W u) - 1 ≠ 0 := by
      intro h
      apply hv1
      have := congrArg conj (sub_eq_zero.mp h)
      simpa using this
    show (W (1 + (-2 * I) * (conj z + I)⁻¹) - W 1)⁻¹ = -1 - conj ((W u - W 1)⁻¹)
    rw [hru, normalized_solution_refl_comm hW u, hW1]
    simp only [refl, map_inv₀, map_sub, map_one]
    field_simp
    ring
  obtain ⟨hΨK, hΨs⟩ := bB_l_affine_isKQC hGK hGs (G 0) hD
  have hΨsym : ∀ z, (fun ζ => (G ζ - G 0) / (G 1 - G 0)) (conj z) =
      conj ((fun ζ => (G ζ - G 0) / (G 1 - G 0)) z) := by
    intro z
    show (G (conj z) - G 0) / (G 1 - G 0) = conj ((G z - G 0) / (G 1 - G 0))
    rw [hGsym, map_div₀, map_sub, hcD, hc0]
    field_simp
    ring
  have himage := bg_s_image_upperHalf hΨK hΨs (by simp) (by simp [div_self hD]) hΨsym
  have hmem : (fun ζ => (G ζ - G 0) / (G 1 - G 0)) I ∈ upperHalf := by
    have h : (fun ζ => (G ζ - G 0) / (G 1 - G 0)) I ∈
        (fun ζ => (G ζ - G 0) / (G 1 - G 0)) '' upperHalf :=
      ⟨I, show 0 < (I : ℂ).im by simp, rfl⟩
    rwa [himage] at h
  have hmem' : 0 < ((G I - G 0) / (G 1 - G 0)).im := hmem
  have hkey : ((G I - G 0) / (G 1 - G 0)).im = 1 / (2 * t) := by
    rw [hDeq, hGI]
    have hG0re' : (-1 - G 0).re = -1 / 2 := by rw [Complex.sub_re]; simp [hG0re]; ring
    have ht0 : t ≠ 0 := by
      intro h0
      apply hD
      rw [hDeq, h0]
      simp
    have hw_re : ((t : ℂ) * I).re = 0 := by simp
    have hw_im : ((t : ℂ) * I).im = t := by simp
    have hns : Complex.normSq ((t : ℂ) * I) = t ^ 2 := by
      rw [Complex.normSq_apply, hw_re, hw_im]
      ring
    rw [Complex.div_im, hw_re, hw_im, hns, hG0re']
    field_simp
    ring
  have htpos : 0 < t := by
    rw [hkey] at hmem'
    exact (one_div_pos.mp hmem') |> fun h => by linarith
  refine ⟨t, htpos, ?_⟩
  rw [kappa_eq hne2, kappa_eq hne1]
  have h := hDeq
  rw [hG1, hG0] at h
  push_cast
  linear_combination (-2 * I) * h + (-2 * (t : ℂ)) * Complex.I_sq

theorem isMobius_comp {F G : ExtPlane → ExtPlane} (hF : IsMobius F) (hG : IsMobius G) :
    IsMobius (fun w => G (F w)) := by
  obtain ⟨a, b, c, d, hdet, rfl⟩ := hF
  obtain ⟨a', b', c', d', hdet', rfl⟩ := hG
  refine ⟨a' * a + b' * c, a' * b + b' * d, c' * a + d' * c, c' * b + d' * d, ?_, ?_⟩
  · have e : (a' * a + b' * c) * (c' * b + d' * d) - (a' * b + b' * d) * (c' * a + d' * c) =
        (a' * d' - b' * c') * (a * d - b * c) := by ring
    rw [e]
    exact mul_ne_zero hdet' hdet
  · funext w
    exact s16p_mobiusExt_comp hdet w

theorem kappa_form {s : ℂ} (hs : s ≠ 1) : mobiusFn I I (-1) 1 s = I * (1 + s) / (1 - s) := by
  have h2 : 1 - s ≠ 0 := sub_ne_zero.mpr hs.symm
  have h3 : (-1 : ℂ) * s + 1 ≠ 0 := by
    intro h
    exact h2 (by linear_combination h)
  unfold mobiusFn
  rw [div_eq_div_iff h3 h2]
  ring

theorem kappa_im_pos {v : ℂ} (hv : ‖v‖ < 1) : 0 < (I * (1 + v) / (1 - v)).im := by
  have hn : v.re ^ 2 + v.im ^ 2 < 1 := by
    have h := Complex.sq_norm v
    rw [Complex.normSq_apply] at h
    have h0 := norm_nonneg v
    nlinarith
  have hv1 : v ≠ 1 := by
    rintro rfl
    simp at hv
  have hd : 0 < (1 - v.re) * (1 - v.re) + v.im * v.im := by
    have : (1 - v.re) * (1 - v.re) + v.im * v.im = 2 - 2 * v.re + (v.re ^ 2 + v.im ^ 2) - 1 + 0 := by
      ring
    nlinarith [sq_nonneg v.im, sq_nonneg (1 - v.re), sq_nonneg v.re]
  rw [Complex.div_im]
  have hns : Complex.normSq (1 - v) = (1 - v.re) * (1 - v.re) + v.im * v.im := by
    rw [Complex.normSq_apply]
    simp
  rw [hns]
  simp only [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.add_re, Complex.add_im,
    Complex.one_re, Complex.one_im, Complex.sub_re, Complex.sub_im]
  have : (0 * (1 + v.re) - 1 * (0 + v.im)) = -v.im := by ring
  rw [← sub_div]
  apply div_pos _ hd
  nlinarith

/-- The Model A Möbius map sends the unit disk into the unit disk: it is `κ⁻¹ ∘ A ∘ κ` with `κ` the Cayley map and
`A` an increasing real affine map (`normalized_solution_orient`). -/
theorem modelA_mobius_disc {μ : LinfStar} {W : ℂ → ℂ} (hW : IsNormalizedSolution W (extA μ))
    {M : ExtPlane → ExtPlane} (hM : IsMobius M)
    (hm1 : M ((W (-1) : ℂ) : ExtPlane) = ((-1 : ℂ) : ExtPlane))
    (hmI : M ((W (-I) : ℂ) : ExtPlane) = ((-I : ℂ) : ExtPlane))
    (hm2 : M ((W 1 : ℂ) : ExtPlane) = ((1 : ℂ) : ExtPlane)) {v : ℂ} (hv : ‖v‖ < 1) :
    ∃ u : ℂ, ‖u‖ < 1 ∧ M (v : ExtPlane) = (u : ExtPlane) := by
  have hinj := normalized_solution_injective hW
  have hW1 : W 1 = 1 := hW.2.2.2.1
  obtain ⟨t, ht, hκ⟩ := normalized_solution_orient hW
  have hs1 : ‖W (-1)‖ = 1 := normalized_solution_circle hW (by simp)
  have hne1 : W (-1) ≠ 1 := by
    intro h
    have := hinj (h.trans hW1.symm)
    norm_num at this
  have hne2 : W (-I) ≠ 1 := by
    intro h
    have := congrArg Complex.re (hinj (h.trans hW1.symm))
    norm_num at this
  have hn12 : W (-1) ≠ W (-I) := by
    intro h
    have := congrArg Complex.re (hinj h)
    norm_num at this
  rw [hW1] at hm2
  obtain ⟨x₁, hx₁⟩ : ∃ x₁ : ℂ, x₁ = I * (1 + W (-1)) / (1 - W (-1)) := ⟨_, rfl⟩
  obtain ⟨x₂, hx₂⟩ : ∃ x₂ : ℂ, x₂ = I * (1 + W (-I)) / (1 - W (-I)) := ⟨_, rfl⟩
  obtain ⟨r, hr⟩ : ∃ r : ℂ, r = ((2 * t : ℝ) : ℂ) := ⟨_, rfl⟩
  have hr0 : r ≠ 0 := by
    rw [hr]
    exact_mod_cast (by positivity : (2 * t : ℝ) ≠ 0)
  have hx₁im : x₁.im = 0 := by
    have hg := inv_sub_one_re hs1 hne1
    rw [hx₁, kappa_eq hne1]
    simp [Complex.sub_im, Complex.mul_im, hg] <;> norm_num
  have hx₂₁ : x₂ = x₁ + r := by
    rw [hx₂, hx₁, hr]
    linear_combination hκ
  set K : ExtPlane → ExtPlane := mobiusExt I I (-1) 1 with hK
  set A : ExtPlane → ExtPlane := mobiusExt 1 (-x₁) 0 r with hA
  set Ki : ExtPlane → ExtPlane := mobiusExt 1 (-I) 1 I with hKi
  have hKM : IsMobius K := ⟨I, I, -1, 1, by
    intro h
    apply Complex.I_ne_zero
    linear_combination (1 / 2 : ℂ) * h, rfl⟩
  have hAM : IsMobius A := ⟨1, -x₁, 0, r, by simpa using hr0, rfl⟩
  have hKiM : IsMobius Ki := ⟨1, -I, 1, I, by
    intro h
    apply Complex.I_ne_zero
    linear_combination (1 / 2 : ℂ) * h, rfl⟩
  have hM' : IsMobius (fun w => Ki (A (K w))) :=
    isMobius_comp (isMobius_comp hKM hAM) hKiM
  have hKs : ∀ s : ℂ, s ≠ 1 → K (s : ExtPlane) = ((I * (1 + s) / (1 - s) : ℂ) : ExtPlane) := by
    intro s hs
    have h3 : (-1 : ℂ) * s + 1 ≠ 0 := by
      intro h
      exact hs (by linear_combination -h)
    rw [hK, mobiusExt_coe h3, kappa_form hs]
  have hAs : ∀ y : ℂ, A (y : ExtPlane) = (((y - x₁) / r : ℂ) : ExtPlane) := by
    intro y
    rw [hA, mobiusExt_coe (by simpa using hr0)]
    congr 1
    simp [mobiusFn, sub_eq_add_neg]
  have hKis : ∀ y : ℂ, y + I ≠ 0 → Ki (y : ExtPlane) = (((y - I) / (y + I) : ℂ) : ExtPlane) := by
    intro y hy
    rw [hKi, mobiusExt_coe (by simpa using hy)]
    congr 1
    simp [mobiusFn, sub_eq_add_neg]
  have e₁ : M ((W (-1) : ℂ) : ExtPlane) = Ki (A (K ((W (-1) : ℂ) : ExtPlane))) := by
    rw [hm1, hKs _ hne1, ← hx₁, hAs, sub_self, zero_div, hKis 0 (by simpa using Complex.I_ne_zero)]
    congr 1
    simp
  have e₂ : M ((W (-I) : ℂ) : ExtPlane) = Ki (A (K ((W (-I) : ℂ) : ExtPlane))) := by
    rw [hmI, hKs _ hne2, ← hx₂, hAs, hx₂₁, add_sub_cancel_left, div_self hr0]
    have h1I : (1 : ℂ) + I ≠ 0 := by
      intro h
      have := congrArg Complex.re h
      simp at this
    rw [hKis 1 h1I]
    congr 1
    field_simp
    linear_combination (-1 : ℂ) * Complex.I_sq
  have e₃ : M (((1 : ℂ)) : ExtPlane) = Ki (A (K (((1 : ℂ)) : ExtPlane))) := by
    rw [hm2, hK, mobiusExt_coe_of_eq_zero (by norm_num), hA, mobiusExt_infty_of_eq rfl, hKi,
      mobiusExt_infty_of_ne one_ne_zero, one_div_one]
  have hMM' : M = fun w => Ki (A (K w)) :=
    mobius_eq_of_three_points hM hM' hn12 hne1 hne2 e₁ e₂ e₃
  have hv1 : v ≠ 1 := by
    rintro rfl
    simp at hv
  have hyim : 0 < (I * (1 + v) / (1 - v)).im := kappa_im_pos hv
  have hy'im : 0 < ((I * (1 + v) / (1 - v) - x₁) / r).im := by
    rw [hr, Complex.div_ofReal_im, Complex.sub_im, hx₁im, sub_zero]
    exact div_pos hyim (by positivity)
  obtain ⟨y', hy'⟩ : ∃ y' : ℂ, y' = (I * (1 + v) / (1 - v) - x₁) / r := ⟨_, rfl⟩
  rw [← hy'] at hy'im
  have hyI : y' + I ≠ 0 := by
    intro h
    have := congrArg Complex.im h
    simp at this
    linarith
  refine ⟨(y' - I) / (y' + I), ?_, ?_⟩
  · rw [norm_div, div_lt_one (norm_pos_iff.mpr hyI)]
    apply lt_of_pow_lt_pow_left₀ 2 (norm_nonneg _)
    rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply]
    simp
    nlinarith
  · rw [hMM']
    show Ki (A (K (v : ExtPlane))) = _
    rw [hKs v hv1, hAs, ← hy', hKis y' hyI]

/-- The pole `p_μ = w_μ⁻¹(∞)` of Model A is not in the open unit disk (TT:353, TT:355). -/
theorem wAS_pole_notin_disc {μ : LinfStar} (hμ : μ ∈ LinfStarBall) {z : ℂ} (hz : ‖z‖ < 1) :
    Function.invFun (wAS μ) extInf ≠ (z : ExtPlane) := by
  intro h
  obtain ⟨M, hM, W, hW, hwf, hwi, hm1, hmI, hm2⟩ := wA_spec hμ
  obtain ⟨u, hu, hMu⟩ := modelA_mobius_disc hW hM ((hwf (-1)).symm.trans hm1)
    ((hwf (-I)).symm.trans hmI) ((hwf 1).symm.trans hm2) (normalized_solution_disc hW hz)
  have h1 : wAS μ (z : ExtPlane) = (u : ExtPlane) := by rw [hwf z, hMu]
  have h2 : wAS μ (Function.invFun (wAS μ) extInf) = extInf :=
    Function.invFun_eq ((wAS_bijective μ).2 extInf)
  rw [h, h1] at h2
  exact OnePoint.coe_ne_infty _ h2

/-- The Möbius map of Model B sends the image of the pole of `w_μ` to `∞` and has no pole in `W(𝔻)`. -/
theorem modelB_pole_data {W : ℂ → ℂ} (hWi : Function.Injective W) (hW0 : W 0 = 0) {p : ExtPlane}
    (hp : ∀ z : ℂ, ‖z‖ < 1 → p ≠ (z : ExtPlane)) (a : ℂ) :
    mobiusExt a 0 (-(finPart (OnePoint.map W p))⁻¹) 1 (OnePoint.map W p) = extInf ∧
      ∀ z : ℂ, ‖z‖ < 1 → -(finPart (OnePoint.map W p))⁻¹ * W z + 1 ≠ 0 := by
  revert hp
  induction p using OnePoint.rec with
  | infty =>
    intro hp
    have hf : finPart (OnePoint.map W extInf) = 0 := rfl
    rw [hf]
    refine ⟨?_, fun z _ => by simp⟩
    simp only [inv_zero, neg_zero]
    exact mobiusExt_infty_of_eq rfl
  | coe x =>
    intro hp
    have hx0 : x ≠ 0 := by
      rintro rfl
      exact hp 0 (by simp) rfl
    have hWx : W x ≠ 0 := fun h => hx0 (hWi (h.trans hW0.symm))
    have hf : finPart (OnePoint.map W (x : ExtPlane)) = W x := rfl
    rw [hf]
    refine ⟨?_, fun z hz h => ?_⟩
    · show mobiusExt a 0 (-(W x)⁻¹) 1 ((W x : ℂ) : ExtPlane) = extInf
      apply mobiusExt_coe_of_eq_zero
      field_simp
      ring
    · apply hp z hz
      have : W x = W z := by
        field_simp at h
        linear_combination h
      rw [hWi this]

/-- Existence of Model B for `μ ∈ L∞(𝔻*)₁` with the welding normalization (TT:355). -/
theorem exists_isNormalizedB {μ : LinfStar} (hμ : μ ∈ LinfStarBall) : ∃ w, IsNormalizedB μ w := by
  obtain ⟨W, hW, -, -⟩ := extB_normalized_plane_exists hμ
  obtain ⟨K, hK⟩ := hW.1
  have hWi : Function.Injective W :=
    fun _ _ he => hK.2.2.1.2.1 (mem_univ _) (mem_univ _) he
  have hz0 : (0 : ℂ) ∈ unitDisc := by simp [unitDisc]
  have hW0 : W 0 = 0 := hW.2.2.1
  have hd : deriv W 0 ≠ 0 :=
    deriv_ne_zero_of_injOn isOpen_ball (extB_solution_holomorphic hW) hWi.injOn hz0
  have hWa : AnalyticAt ℂ W 0 :=
    (extB_solution_holomorphic hW).analyticAt (isOpen_ball.mem_nhds hz0)
  have hpD : ∀ z : ℂ, ‖z‖ < 1 → Function.invFun (wAS μ) extInf ≠ (z : ExtPlane) :=
    fun z hz => wAS_pole_notin_disc hμ hz
  obtain ⟨hpole, hden⟩ := modelB_pole_data hWi hW0 hpD (deriv W 0)⁻¹
  obtain ⟨γ, hγ⟩ : ∃ γ : ℂ, γ = -(finPart (OnePoint.map W (Function.invFun (wAS μ) extInf)))⁻¹ :=
    ⟨_, rfl⟩
  rw [← hγ] at hpole hden
  have hden0 : γ * W 0 + 1 ≠ 0 := hden 0 (by simp)
  have hcomp := (hasDerivAt_mobius (a := (deriv W 0)⁻¹) (b := 0) hden0).comp (0 : ℂ)
    hWa.differentiableAt.hasDerivAt
  refine ⟨mobiusExt (deriv W 0)⁻¹ 0 γ 1 ∘ OnePoint.map W, mobiusExt (deriv W 0)⁻¹ 0 γ 1,
    ⟨(deriv W 0)⁻¹, 0, γ, 1, by simpa using inv_ne_zero hd, rfl⟩, W, hW, fun z => rfl, rfl,
    mobiusFn (deriv W 0)⁻¹ 0 γ 1 ∘ W, ?_, ?_, ?_, ?_⟩
  · intro z hz
    show mobiusExt (deriv W 0)⁻¹ 0 γ 1 ((W z : ℂ) : ExtPlane) = _
    rw [mobiusExt_coe (by simpa using hden z (mem_ball_zero_iff.mp hz))]
    rfl
  · simp [mobiusFn, hW0]
  · have hd' := hcomp.deriv
    change deriv (mobiusFn (deriv W 0)⁻¹ 0 γ 1 ∘ W) 0 = _ at hd'
    rw [hd', hW0]
    simp
    field_simp
  · show mobiusExt (deriv W 0)⁻¹ 0 γ 1 (OnePoint.map W (Function.invFun (wAS μ) extInf)) = extInf
    exact hpole

theorem kappa_im_eq (v : ℂ) : (I * (1 + v) / (1 - v)).im =
    (1 - (v.re ^ 2 + v.im ^ 2)) / ((1 - v.re) * (1 - v.re) + v.im * v.im) := by
  rw [Complex.div_im]
  have hns : Complex.normSq (1 - v) = (1 - v.re) * (1 - v.re) + v.im * v.im := by
    rw [Complex.normSq_apply]
    simp
  rw [hns]
  simp only [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.add_re, Complex.add_im,
    Complex.one_re, Complex.one_im, Complex.sub_re, Complex.sub_im]
  rw [← sub_div]
  congr 1
  ring

theorem normSq_eq_of_norm {v : ℂ} {c : ℝ} (hv : ‖v‖ = c) : v.re ^ 2 + v.im ^ 2 = c ^ 2 := by
  have h := Complex.sq_norm v
  rw [Complex.normSq_apply, hv] at h
  nlinarith

theorem kappa_im_zero {v : ℂ} (hv : ‖v‖ = 1) : (I * (1 + v) / (1 - v)).im = 0 := by
  rw [kappa_im_eq, normSq_eq_of_norm hv]
  simp

theorem kappa_im_neg {v : ℂ} (hv : 1 < ‖v‖) : (I * (1 + v) / (1 - v)).im < 0 := by
  rw [kappa_im_eq]
  have hn : 1 < v.re ^ 2 + v.im ^ 2 := by
    have h := Complex.sq_norm v
    rw [Complex.normSq_apply] at h
    nlinarith
  have hd : 0 < (1 - v.re) * (1 - v.re) + v.im * v.im := by
    by_contra hle
    push_neg at hle
    have h1 : (1 - v.re) * (1 - v.re) = 0 := by nlinarith [mul_self_nonneg (1 - v.re), mul_self_nonneg v.im]
    have h2 : v.im * v.im = 0 := by nlinarith [mul_self_nonneg (1 - v.re), mul_self_nonneg v.im]
    have h3 : v.re = 1 := by nlinarith
    have h4 : v.im = 0 := by nlinarith
    rw [h3, h4] at hn
    norm_num at hn
  exact div_neg_of_neg_of_pos (by linarith) hd

theorem K_apply {s : ℂ} (hs : s ≠ 1) :
    mobiusExt I I (-1) 1 (s : ExtPlane) = ((I * (1 + s) / (1 - s) : ℂ) : ExtPlane) := by
  have h3 : (-1 : ℂ) * s + 1 ≠ 0 := by
    intro h
    exact hs (by linear_combination -h)
  rw [mobiusExt_coe h3, kappa_form hs]

theorem A_apply {x₁ r : ℂ} (hr : r ≠ 0) (y : ℂ) :
    mobiusExt 1 (-x₁) 0 r (y : ExtPlane) = (((y - x₁) / r : ℂ) : ExtPlane) := by
  rw [mobiusExt_coe (by simpa using hr)]
  congr 1
  simp [mobiusFn, sub_eq_add_neg]

theorem Ki_apply {y : ℂ} (hy : y + I ≠ 0) :
    mobiusExt 1 (-I) 1 I (y : ExtPlane) = (((y - I) / (y + I) : ℂ) : ExtPlane) := by
  rw [mobiusExt_coe (by simpa using hy)]
  congr 1
  simp [mobiusFn, sub_eq_add_neg]

theorem norm_sub_I_lt {y : ℂ} (hy : 0 < y.im) : ‖y - I‖ < ‖y + I‖ := by
  apply lt_of_pow_lt_pow_left₀ 2 (norm_nonneg _)
  rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply]
  simp
  nlinarith

theorem norm_sub_I_eq {y : ℂ} (hy : y.im = 0) : ‖y - I‖ = ‖y + I‖ := by
  rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _), Complex.sq_norm, Complex.sq_norm,
    Complex.normSq_apply, Complex.normSq_apply]
  simp [hy]

theorem norm_sub_I_gt {y : ℂ} (hy : y.im < 0) : ‖y + I‖ < ‖y - I‖ := by
  apply lt_of_pow_lt_pow_left₀ 2 (norm_nonneg _)
  rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply]
  simp
  nlinarith

/-- Cayley form of the Model A Möbius map (TT:346): `M = κ⁻¹ ∘ A ∘ κ` with `A` an increasing real affine map. -/
theorem modelA_mobius_cayley {μ : LinfStar} {W : ℂ → ℂ} (hW : IsNormalizedSolution W (extA μ))
    {M : ExtPlane → ExtPlane} (hM : IsMobius M)
    (hm1 : M ((W (-1) : ℂ) : ExtPlane) = ((-1 : ℂ) : ExtPlane))
    (hmI : M ((W (-I) : ℂ) : ExtPlane) = ((-I : ℂ) : ExtPlane))
    (hm2 : M ((W 1 : ℂ) : ExtPlane) = ((1 : ℂ) : ExtPlane)) :
    ∃ x₁ r : ℝ, 0 < r ∧ M = fun w => mobiusExt 1 (-I) 1 I
      (mobiusExt 1 (-(x₁ : ℂ)) 0 (r : ℂ) (mobiusExt I I (-1) 1 w)) := by
  have hinj := normalized_solution_injective hW
  have hW1 : W 1 = 1 := hW.2.2.2.1
  obtain ⟨t, ht, hκ⟩ := normalized_solution_orient hW
  have hs1 : ‖W (-1)‖ = 1 := normalized_solution_circle hW (by simp)
  have hne1 : W (-1) ≠ 1 := by
    intro h
    have := hinj (h.trans hW1.symm)
    norm_num at this
  have hne2 : W (-I) ≠ 1 := by
    intro h
    have := congrArg Complex.re (hinj (h.trans hW1.symm))
    norm_num at this
  have hn12 : W (-1) ≠ W (-I) := by
    intro h
    have := congrArg Complex.re (hinj h)
    norm_num at this
  rw [hW1] at hm2
  obtain ⟨x₁, hx₁⟩ : ∃ x₁ : ℂ, x₁ = I * (1 + W (-1)) / (1 - W (-1)) := ⟨_, rfl⟩
  obtain ⟨x₂, hx₂⟩ : ∃ x₂ : ℂ, x₂ = I * (1 + W (-I)) / (1 - W (-I)) := ⟨_, rfl⟩
  have hr0 : ((2 * t : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (by positivity : (2 * t : ℝ) ≠ 0)
  have hx₁im : x₁.im = 0 := by
    have hg := inv_sub_one_re hs1 hne1
    rw [hx₁, kappa_eq hne1]
    simp [Complex.sub_im, Complex.mul_im, hg] <;> norm_num
  have hx₁re : ((x₁.re : ℝ) : ℂ) = x₁ := Complex.ext (by simp) (by simp [hx₁im])
  have hx₂₁ : x₂ = x₁ + ((2 * t : ℝ) : ℂ) := by
    rw [hx₂, hx₁]
    linear_combination hκ
  refine ⟨x₁.re, 2 * t, by positivity, ?_⟩
  rw [hx₁re]
  set K : ExtPlane → ExtPlane := mobiusExt I I (-1) 1 with hK
  set A : ExtPlane → ExtPlane := mobiusExt 1 (-x₁) 0 ((2 * t : ℝ) : ℂ) with hA
  set Ki : ExtPlane → ExtPlane := mobiusExt 1 (-I) 1 I with hKi
  have hKM : IsMobius K := ⟨I, I, -1, 1, by
    intro h
    apply Complex.I_ne_zero
    linear_combination (1 / 2 : ℂ) * h, rfl⟩
  have hAM : IsMobius A := ⟨1, -x₁, 0, _, by simpa using hr0, rfl⟩
  have hKiM : IsMobius Ki := ⟨1, -I, 1, I, by
    intro h
    apply Complex.I_ne_zero
    linear_combination (1 / 2 : ℂ) * h, rfl⟩
  have hM' : IsMobius (fun w => Ki (A (K w))) :=
    isMobius_comp (isMobius_comp hKM hAM) hKiM
  have e₁ : M ((W (-1) : ℂ) : ExtPlane) = Ki (A (K ((W (-1) : ℂ) : ExtPlane))) := by
    rw [hm1, hK, K_apply hne1, ← hx₁, hA, A_apply hr0, sub_self, zero_div, hKi,
      Ki_apply (by simpa using Complex.I_ne_zero)]
    congr 1
    simp
  have e₂ : M ((W (-I) : ℂ) : ExtPlane) = Ki (A (K ((W (-I) : ℂ) : ExtPlane))) := by
    rw [hmI, hK, K_apply hne2, ← hx₂, hA, A_apply hr0, hx₂₁, add_sub_cancel_left, div_self hr0]
    have h1I : (1 : ℂ) + I ≠ 0 := by
      intro h
      have := congrArg Complex.re h
      simp at this
    rw [hKi, Ki_apply h1I]
    congr 1
    field_simp
    linear_combination (-1 : ℂ) * Complex.I_sq
  have e₃ : M (((1 : ℂ)) : ExtPlane) = Ki (A (K (((1 : ℂ)) : ExtPlane))) := by
    rw [hm2, hK, mobiusExt_coe_of_eq_zero (by norm_num), hA, mobiusExt_infty_of_eq rfl, hKi,
      mobiusExt_infty_of_ne one_ne_zero, one_div_one]
  exact mobius_eq_of_three_points hM hM' hn12 hne1 hne2 e₁ e₂ e₃

theorem A_im {x₁ r : ℝ} (hr : 0 < r) (y : ℂ) : ((y - (x₁ : ℂ)) / (r : ℂ)).im = y.im / r := by
  rw [Complex.div_ofReal_im, Complex.sub_im, Complex.ofReal_im, sub_zero]

theorem Ki_disc_of_im_pos {y : ℂ} (hy : 0 < y.im) :
    ∃ u : ℂ, ‖u‖ < 1 ∧ mobiusExt 1 (-I) 1 I (y : ExtPlane) = (u : ExtPlane) := by
  have hyI : y + I ≠ 0 := by
    intro h
    have := congrArg Complex.im h
    simp at this
    linarith
  refine ⟨(y - I) / (y + I), ?_, Ki_apply hyI⟩
  rw [norm_div, div_lt_one (norm_pos_iff.mpr hyI)]
  exact norm_sub_I_lt hy

theorem Ki_circle_of_im_zero {y : ℂ} (hy : y.im = 0) :
    ∃ u : ℂ, ‖u‖ = 1 ∧ mobiusExt 1 (-I) 1 I (y : ExtPlane) = (u : ExtPlane) := by
  have hyI : y + I ≠ 0 := by
    intro h
    have := congrArg Complex.im h
    simp [hy] at this
  refine ⟨(y - I) / (y + I), ?_, Ki_apply hyI⟩
  rw [norm_div, norm_sub_I_eq hy]
  exact div_self (norm_ne_zero_iff.mpr hyI)

theorem Ki_ext_of_im_neg {y : ℂ} (hy : y.im < 0) :
    mobiusExt 1 (-I) 1 I (y : ExtPlane) = extInf ∨
      ∃ u : ℂ, 1 < ‖u‖ ∧ mobiusExt 1 (-I) 1 I (y : ExtPlane) = (u : ExtPlane) := by
  by_cases hyI : y + I = 0
  · left
    exact mobiusExt_coe_of_eq_zero (by simpa using hyI)
  · right
    refine ⟨(y - I) / (y + I), ?_, Ki_apply hyI⟩
    rw [norm_div, one_lt_div (norm_pos_iff.mpr hyI)]
    exact norm_sub_I_gt hy

theorem cayley_disc {x₁ r : ℝ} (hr : 0 < r) {v : ℂ} (hv : ‖v‖ < 1) :
    ∃ u : ℂ, ‖u‖ < 1 ∧ mobiusExt 1 (-I) 1 I (mobiusExt 1 (-(x₁ : ℂ)) 0 (r : ℂ)
      (mobiusExt I I (-1) 1 (v : ExtPlane))) = (u : ExtPlane) := by
  have hv1 : v ≠ 1 := by
    rintro rfl
    simp at hv
  have hr0 : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  rw [K_apply hv1, A_apply hr0]
  apply Ki_disc_of_im_pos
  rw [A_im hr]
  exact div_pos (kappa_im_pos hv) hr

theorem cayley_circle {x₁ r : ℝ} (hr : 0 < r) {v : ℂ} (hv : ‖v‖ = 1) :
    ∃ u : ℂ, ‖u‖ = 1 ∧ mobiusExt 1 (-I) 1 I (mobiusExt 1 (-(x₁ : ℂ)) 0 (r : ℂ)
      (mobiusExt I I (-1) 1 (v : ExtPlane))) = (u : ExtPlane) := by
  have hr0 : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  by_cases hv1 : v = 1
  · subst hv1
    refine ⟨1, by simp, ?_⟩
    rw [mobiusExt_coe_of_eq_zero (by norm_num), mobiusExt_infty_of_eq rfl,
      mobiusExt_infty_of_ne one_ne_zero, one_div_one]
  · rw [K_apply hv1, A_apply hr0]
    apply Ki_circle_of_im_zero
    rw [A_im hr, kappa_im_zero hv, zero_div]

theorem cayley_ext {x₁ r : ℝ} (hr : 0 < r) {v : ℂ} (hv : 1 < ‖v‖) :
    mobiusExt 1 (-I) 1 I (mobiusExt 1 (-(x₁ : ℂ)) 0 (r : ℂ) (mobiusExt I I (-1) 1 (v : ExtPlane))) =
        extInf ∨
      ∃ u : ℂ, 1 < ‖u‖ ∧ mobiusExt 1 (-I) 1 I (mobiusExt 1 (-(x₁ : ℂ)) 0 (r : ℂ)
        (mobiusExt I I (-1) 1 (v : ExtPlane))) = (u : ExtPlane) := by
  have hv1 : v ≠ 1 := by
    rintro rfl
    simp at hv
  have hr0 : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  rw [K_apply hv1, A_apply hr0]
  apply Ki_ext_of_im_neg
  rw [A_im hr]
  exact div_neg_of_neg_of_pos (kappa_im_neg hv) hr

theorem cayley_infty {x₁ r : ℝ} (hr : 0 < r) :
    mobiusExt 1 (-I) 1 I (mobiusExt 1 (-(x₁ : ℂ)) 0 (r : ℂ) (mobiusExt I I (-1) 1 extInf)) = extInf ∨
      ∃ u : ℂ, 1 < ‖u‖ ∧ mobiusExt 1 (-I) 1 I (mobiusExt 1 (-(x₁ : ℂ)) 0 (r : ℂ)
        (mobiusExt I I (-1) 1 extInf)) = (u : ExtPlane) := by
  have hr0 : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  rw [mobiusExt_infty_of_ne (by norm_num : (-1 : ℂ) ≠ 0), A_apply hr0]
  apply Ki_ext_of_im_neg
  rw [A_im hr]
  apply div_neg_of_neg_of_pos _ hr
  rw [div_neg, div_one, Complex.neg_im, Complex.I_im]
  norm_num

theorem wAS_maps_disc {μ : LinfStar} (hμ : μ ∈ LinfStarBall) {z : ℂ} (hz : ‖z‖ < 1) :
    ∃ u : ℂ, ‖u‖ < 1 ∧ wAS μ (z : ExtPlane) = (u : ExtPlane) := by
  obtain ⟨M, hM, W, hW, hwf, hwi, hm1, hmI, hm2⟩ := wA_spec hμ
  obtain ⟨x₁, r, hr, hMeq⟩ := modelA_mobius_cayley hW hM ((hwf (-1)).symm.trans hm1)
    ((hwf (-I)).symm.trans hmI) ((hwf 1).symm.trans hm2)
  rw [hwf z, hMeq]
  exact cayley_disc hr (normalized_solution_disc hW hz)

theorem wAS_maps_circle {μ : LinfStar} (hμ : μ ∈ LinfStarBall) {z : ℂ} (hz : ‖z‖ = 1) :
    ∃ u : ℂ, ‖u‖ = 1 ∧ wAS μ (z : ExtPlane) = (u : ExtPlane) := by
  obtain ⟨M, hM, W, hW, hwf, hwi, hm1, hmI, hm2⟩ := wA_spec hμ
  obtain ⟨x₁, r, hr, hMeq⟩ := modelA_mobius_cayley hW hM ((hwf (-1)).symm.trans hm1)
    ((hwf (-I)).symm.trans hmI) ((hwf 1).symm.trans hm2)
  rw [hwf z, hMeq]
  exact cayley_circle hr (normalized_solution_circle hW hz)

theorem wAS_maps_ext {μ : LinfStar} (hμ : μ ∈ LinfStarBall) {z : ℂ} (hz : 1 < ‖z‖) :
    wAS μ (z : ExtPlane) = extInf ∨ ∃ u : ℂ, 1 < ‖u‖ ∧ wAS μ (z : ExtPlane) = (u : ExtPlane) := by
  obtain ⟨M, hM, W, hW, hwf, hwi, hm1, hmI, hm2⟩ := wA_spec hμ
  obtain ⟨x₁, r, hr, hMeq⟩ := modelA_mobius_cayley hW hM ((hwf (-1)).symm.trans hm1)
    ((hwf (-I)).symm.trans hmI) ((hwf 1).symm.trans hm2)
  rw [hwf z, hMeq]
  exact cayley_ext hr (normalized_solution_exterior hW hz)

theorem wAS_maps_infty {μ : LinfStar} (hμ : μ ∈ LinfStarBall) :
    wAS μ extInf = extInf ∨ ∃ u : ℂ, 1 < ‖u‖ ∧ wAS μ extInf = (u : ExtPlane) := by
  obtain ⟨M, hM, W, hW, hwf, hwi, hm1, hmI, hm2⟩ := wA_spec hμ
  obtain ⟨x₁, r, hr, hMeq⟩ := modelA_mobius_cayley hW hM ((hwf (-1)).symm.trans hm1)
    ((hwf (-I)).symm.trans hmI) ((hwf 1).symm.trans hm2)
  rw [hwi, hMeq]
  exact cayley_infty hr

/-- (TT:353) `w_μ` fixes the domains `𝔻`, `𝔻*` and the unit circle `S¹`.
- **[CORRECTION 2026-10-25]** Stated for the sphere map `wAS μ` (the finite-point map `wA μ` has a junk value at the
  pole of `w_μ`, a point of `𝔻*` when `w_μ(∞) ≠ ∞`); `𝔻*` is taken with `∞`. -/
theorem wA_mapsTo {μ : LinfStar} (hμ : μ ∈ LinfStarBall) :
    wAS μ '' toExt unitDisc = toExt unitDisc ∧
      wAS μ '' (toExt unitDiscExterior ∪ {extInf}) = toExt unitDiscExterior ∪ {extInf} ∧
      wAS μ '' toExt unitCircle = toExt unitCircle := by

  have hD : wAS μ '' toExt unitDisc ⊆ toExt unitDisc := by
    rintro _ ⟨a, ⟨z, hz, rfl⟩, rfl⟩
    obtain ⟨u, hu, he⟩ := wAS_maps_disc hμ (mem_ball_zero_iff.mp hz)
    exact ⟨u, mem_ball_zero_iff.mpr hu, he.symm⟩
  have hC : wAS μ '' toExt unitCircle ⊆ toExt unitCircle := by
    rintro _ ⟨a, ⟨z, hz, rfl⟩, rfl⟩
    obtain ⟨u, hu, he⟩ := wAS_maps_circle hμ (show ‖z‖ = 1 from hz)
    exact ⟨u, hu, he.symm⟩
  have hE : wAS μ '' (toExt unitDiscExterior ∪ {extInf}) ⊆ toExt unitDiscExterior ∪ {extInf} := by
    rintro _ ⟨a, ha, rfl⟩
    rcases ha with ⟨z, hz, rfl⟩ | ha
    · rcases wAS_maps_ext hμ (show 1 < ‖z‖ from hz) with h | ⟨u, hu, h⟩
      · exact Or.inr h
      · exact Or.inl ⟨u, hu, h.symm⟩
    · rw [mem_singleton_iff] at ha
      subst ha
      rcases wAS_maps_infty hμ with h | ⟨u, hu, h⟩
      · exact Or.inr h
      · exact Or.inl ⟨u, hu, h.symm⟩
  have hpart : ∀ a : ExtPlane, a ∈ toExt unitDisc ∨ a ∈ toExt unitCircle ∨
      a ∈ toExt unitDiscExterior ∪ {extInf} := by
    intro a
    induction a using OnePoint.rec with
    | infty => exact Or.inr (Or.inr (Or.inr rfl))
    | coe z =>
      rcases lt_trichotomy ‖z‖ 1 with h | h | h
      · exact Or.inl ⟨z, mem_ball_zero_iff.mpr h, rfl⟩
      · exact Or.inr (Or.inl ⟨z, h, rfl⟩)
      · exact Or.inr (Or.inr (Or.inl ⟨z, h, rfl⟩))
  have dDC : ∀ y : ExtPlane, y ∈ toExt unitDisc → y ∈ toExt unitCircle → False := by
    rintro y ⟨z, hz, rfl⟩ ⟨w, hw, hwz⟩
    have := OnePoint.coe_injective hwz
    subst this
    have h1 := mem_ball_zero_iff.mp hz
    have h2 : ‖w‖ = 1 := hw
    linarith
  have dDE : ∀ y : ExtPlane, y ∈ toExt unitDisc → y ∈ toExt unitDiscExterior ∪ {extInf} → False := by
    rintro y ⟨z, hz, rfl⟩ (⟨w, hw, hwz⟩ | h)
    · have := OnePoint.coe_injective hwz
      subst this
      have h1 := mem_ball_zero_iff.mp hz
      have h2 : 1 < ‖w‖ := hw
      linarith
    · exact OnePoint.coe_ne_infty _ h
  have dCE : ∀ y : ExtPlane, y ∈ toExt unitCircle → y ∈ toExt unitDiscExterior ∪ {extInf} → False := by
    rintro y ⟨z, hz, rfl⟩ (⟨w, hw, hwz⟩ | h)
    · have := OnePoint.coe_injective hwz
      subst this
      have h1 : ‖w‖ = 1 := hz
      have h2 : 1 < ‖w‖ := hw
      linarith
    · exact OnePoint.coe_ne_infty _ h
  refine ⟨?_, ?_, ?_⟩
  · refine Subset.antisymm hD fun y hy => ?_
    obtain ⟨a, ha⟩ := (wAS_bijective μ).2 y
    rcases hpart a with h | h | h
    · exact ⟨a, h, ha⟩
    · have := hC ⟨a, h, rfl⟩
      rw [ha] at this
      exact (dDC y hy this).elim
    · have := hE ⟨a, h, rfl⟩
      rw [ha] at this
      exact (dDE y hy this).elim
  · refine Subset.antisymm hE fun y hy => ?_
    obtain ⟨a, ha⟩ := (wAS_bijective μ).2 y
    rcases hpart a with h | h | h
    · have := hD ⟨a, h, rfl⟩
      rw [ha] at this
      exact (dDE y this hy).elim
    · have := hC ⟨a, h, rfl⟩
      rw [ha] at this
      exact (dCE y this hy).elim
    · exact ⟨a, h, ha⟩
  · refine Subset.antisymm hC fun y hy => ?_
    obtain ⟨a, ha⟩ := (wAS_bijective μ).2 y
    rcases hpart a with h | h | h
    · have := hD ⟨a, h, rfl⟩
      rw [ha] at this
      exact (dDC y this hy).elim
    · exact ⟨a, h, ha⟩
    · have := hE ⟨a, h, rfl⟩
      rw [ha] at this
      exact (dCE y hy this).elim

theorem mobiusExt_conj_conj (a b c d : ℂ) (p : ExtPlane) :
    OnePoint.map conj (mobiusExt a b c d (OnePoint.map conj p)) =
      mobiusExt (conj a) (conj b) (conj c) (conj d) p := by
  induction p using OnePoint.rec with
  | infty =>
    show OnePoint.map conj (mobiusExt a b c d extInf) = _
    by_cases hc : c = 0
    · have hc' : conj c = 0 := by rw [hc]; simp
      rw [mobiusExt_infty_of_eq hc, mobiusExt_infty_of_eq hc']
      rfl
    · have hc' : conj c ≠ 0 := (map_ne_zero conj).mpr hc
      rw [mobiusExt_infty_of_ne hc, mobiusExt_infty_of_ne hc']
      show ((conj (a / c) : ℂ) : ExtPlane) = _
      rw [map_div₀]
  | coe z =>
    show OnePoint.map conj (mobiusExt a b c d ((conj z : ℂ) : ExtPlane)) = _
    by_cases h : c * conj z + d = 0
    · have h' : conj c * z + conj d = 0 := by
        have := congrArg conj h
        simpa using this
      rw [mobiusExt_coe_of_eq_zero h, mobiusExt_coe_of_eq_zero h']
      rfl
    · have h' : conj c * z + conj d ≠ 0 := by
        intro h0
        apply h
        have := congrArg conj h0
        simpa using this
      rw [mobiusExt_coe h, mobiusExt_coe h']
      show ((conj (mobiusFn a b c d (conj z)) : ℂ) : ExtPlane) = _
      congr 1
      simp [mobiusFn]

theorem isMobius_conj {F : ExtPlane → ExtPlane} (hF : IsMobius F) :
    IsMobius (fun p => OnePoint.map conj (F (OnePoint.map conj p))) := by
  obtain ⟨a, b, c, d, hdet, rfl⟩ := hF
  refine ⟨conj a, conj b, conj c, conj d, ?_, ?_⟩
  · intro h
    apply hdet
    have := congrArg conj h
    simpa using this
  · funext p
    exact mobiusExt_conj_conj a b c d p

theorem rho_coe {v : ℂ} (hv : v ≠ 0) :
    mobiusExt 0 1 1 0 (OnePoint.map conj (v : ExtPlane)) = ((refl v : ℂ) : ExtPlane) := by
  have hcv : conj v ≠ 0 := (map_ne_zero conj).mpr hv
  show mobiusExt 0 1 1 0 ((conj v : ℂ) : ExtPlane) = _
  rw [mobiusExt_coe (by simpa using hcv)]
  congr 1
  simp [mobiusFn, refl]

theorem rho_zero : mobiusExt 0 1 1 0 (OnePoint.map conj ((0 : ℂ) : ExtPlane)) = extInf := by
  show mobiusExt 0 1 1 0 ((conj 0 : ℂ) : ExtPlane) = _
  exact mobiusExt_coe_of_eq_zero (by simp)

theorem rho_infty : mobiusExt 0 1 1 0 (OnePoint.map conj extInf) = ((0 : ℂ) : ExtPlane) := by
  show mobiusExt 0 1 1 0 extInf = _
  rw [mobiusExt_infty_of_ne one_ne_zero]
  simp

theorem rho_invol (p : ExtPlane) :
    mobiusExt 0 1 1 0 (OnePoint.map conj (mobiusExt 0 1 1 0 (OnePoint.map conj p))) = p := by
  induction p using OnePoint.rec with
  | infty => rw [rho_infty, rho_zero]
  | coe z =>
    by_cases hz : z = 0
    · subst hz
      rw [rho_zero, rho_infty]
    · rw [rho_coe hz, rho_coe (by simpa [refl] using hz)]
      congr 1
      exact refl_involutive z

theorem refl_neg_one : refl (-1 : ℂ) = -1 := by simp [refl]

theorem refl_neg_I : refl (-I : ℂ) = -I := by simp [refl]

theorem refl_one : refl (1 : ℂ) = 1 := by simp [refl]

/-- `w_μ` commutes with the reflection `ρ = ι ∘ conj` of the sphere (TT:350, (1.2)). -/
theorem wAS_refl_comm {μ : LinfStar} (hμ : μ ∈ LinfStarBall) (p : ExtPlane) :
    wAS μ (mobiusExt 0 1 1 0 (OnePoint.map conj p)) =
      mobiusExt 0 1 1 0 (OnePoint.map conj (wAS μ p)) := by
  obtain ⟨M, hM, W, hW, hwf, hwi, hm1, hmI, hm2⟩ := wA_spec hμ
  have hW0 : W 0 = 0 := hW.2.2.1
  obtain ⟨ρ, hρ⟩ : ∃ ρ : ExtPlane → ExtPlane,
      ρ = fun q => mobiusExt 0 1 1 0 (OnePoint.map conj q) := ⟨_, rfl⟩
  have hρc : ∀ v : ℂ, v ≠ 0 → ρ (v : ExtPlane) = ((refl v : ℂ) : ExtPlane) := by
    intro v hv
    rw [hρ]
    exact rho_coe hv
  have hρ0 : ρ ((0 : ℂ) : ExtPlane) = extInf := by rw [hρ]; exact rho_zero
  have hρi : ρ extInf = ((0 : ℂ) : ExtPlane) := by rw [hρ]; exact rho_infty
  have hρρ : ∀ q, ρ (ρ q) = q := by
    intro q
    rw [hρ]
    exact rho_invol q
  have hinvM : IsMobius (mobiusExt 0 1 1 0) := ⟨0, 1, 1, 0, by norm_num, rfl⟩
  have hM' : IsMobius (fun q => ρ (M (ρ q))) := by
    have h1 : IsMobius (fun w => M (mobiusExt 0 1 1 0 w)) := isMobius_comp hinvM hM
    have h2 := isMobius_conj h1
    have h3 := isMobius_comp h2 hinvM
    rw [hρ]
    exact h3
  have hnorm : IsNormalizedA μ (fun p => ρ (wAS μ (ρ p))) := by
    refine ⟨fun q => ρ (M (ρ q)), hM', W, hW, ?_, ?_, ?_, ?_, ?_⟩
    · intro z
      by_cases hz0 : z = 0
      · subst hz0
        show ρ (wAS μ (ρ ((0 : ℂ) : ExtPlane))) = ρ (M (ρ ((W 0 : ℂ) : ExtPlane)))
        rw [hρ0, hW0, hρ0, hwi]
      · have hWz : W z ≠ 0 := normalized_solution_ne_zero hW hz0
        show ρ (wAS μ (ρ (z : ExtPlane))) = ρ (M (ρ ((W z : ℂ) : ExtPlane)))
        rw [hρc z hz0, hρc (W z) hWz, hwf (refl z), normalized_solution_refl_comm hW z]
    · show ρ (wAS μ (ρ extInf)) = ρ (M (ρ extInf))
      rw [hρi, hwf 0, hW0]
    · show ρ (wAS μ (ρ ((-1 : ℂ) : ExtPlane))) = _
      rw [hρc (-1) (by norm_num), refl_neg_one, hm1, hρc (-1) (by norm_num), refl_neg_one]
    · show ρ (wAS μ (ρ ((-I : ℂ) : ExtPlane))) = _
      rw [hρc (-I) (neg_ne_zero.mpr Complex.I_ne_zero), refl_neg_I, hmI,
        hρc (-I) (neg_ne_zero.mpr Complex.I_ne_zero), refl_neg_I]
    · show ρ (wAS μ (ρ ((1 : ℂ) : ExtPlane))) = _
      rw [hρc 1 one_ne_zero, refl_one, hm2, hρc 1 one_ne_zero, refl_one]
  have hu := wA_unique hμ hnorm
  have h := congrFun hu (ρ p)
  have h' : ρ (wAS μ (ρ (ρ p))) = wAS μ (ρ p) := h
  rw [hρρ] at h'
  have h'' : wAS μ (ρ p) = ρ (wAS μ p) := h'.symm
  rw [hρ] at h''
  exact h''

/-- **(1.2)** (TT:350). The reflection symmetry `1/w_μ(z) = \overline{w_μ(1/z̄)}` (for `z ≠ 0` with
`w_μ(z) ≠ 0`, where both sides are finite). -/
theorem eq_1_2 {μ : LinfStar} (hμ : μ ∈ LinfStarBall) {z : ℂ} (hz : z ≠ 0) (hwz : wA μ z ≠ 0) :
    1 / wA μ z = conj (wA μ (refl z)) := by
  have hcomm := wAS_refl_comm hμ (z : ExtPlane)
  rw [show OnePoint.map conj (z : ExtPlane) = ((conj z : ℂ) : ExtPlane) from rfl] at hcomm
  have hρ : mobiusExt 0 1 1 0 ((conj z : ℂ) : ExtPlane) = ((refl z : ℂ) : ExtPlane) := rho_coe hz
  rw [hρ] at hcomm
  simp only [wA] at hwz ⊢
  generalize hq : wAS μ (z : ExtPlane) = q at hcomm hwz ⊢
  induction q using OnePoint.rec with
  | infty => exact (hwz rfl).elim
  | coe u =>
    have hu0 : u ≠ 0 := hwz
    rw [hcomm]
    show 1 / u = conj (finPart (mobiusExt 0 1 1 0 (OnePoint.map conj (u : ExtPlane))))
    rw [rho_coe hu0]
    show 1 / u = conj (refl u)
    simp [refl]

/-- Existence and uniqueness for Model B (TT:355): for `μ ∈ L∞(𝔻*)₁`, `w^μ` is the normalized solution, and it is
the only one. -/
theorem wB_spec {μ : LinfStar} (hμ : μ ∈ LinfStarBall) :
    IsNormalizedB μ (wB μ) ∧ ∀ w, IsNormalizedB μ w → w = wB μ := by
  have hex : ∃ w, IsNormalizedB μ w := exists_isNormalizedB hμ
  have hB : IsNormalizedB μ (wB μ) := by
    simpa only [wB, dif_pos hex] using hex.choose_spec
  exact ⟨hB, fun w hw => wB_unique hw⟩

/-- (TT:357) `f = w^μ|𝔻` is holomorphic and univalent on `𝔻`. -/
theorem fB_holomorphic_injective {μ : LinfStar} (hμ : μ ∈ LinfStarBall) :
    DifferentiableOn ℂ (fB μ) unitDisc ∧ InjOn (fB μ) unitDisc := by
  by_cases hex : ∃ w, IsNormalizedB μ w
  · have hB : IsNormalizedB μ (wB μ) := by
      simpa only [wB, dif_pos hex] using hex.choose_spec
    obtain ⟨M, hM, W, hW, hfinite, _, f, hf, _⟩ := hB
    obtain ⟨a, b, c, d, hdet, rfl⟩ := hM
    have hhol : DifferentiableOn ℂ W unitDisc := extB_solution_holomorphic hW
    have hden : ∀ z ∈ unitDisc, c * W z + d ≠ 0 := by
      intro z hz he
      have hfin := (hfinite z).symm.trans (hf z hz)
      rw [mobiusExt_coe_of_eq_zero he] at hfin
      exact OnePoint.infty_ne_coe _ hfin
    have hrep : EqOn (fB μ) (fun z => (a * W z + b) / (c * W z + d)) unitDisc := by
      intro z hz
      rw [fB, hfinite z, mobiusExt_coe (hden z hz)]
      rfl
    refine ⟨?_, ?_⟩
    · exact (((hhol.const_mul a).add_const b).div
        ((hhol.const_mul c).add_const d) hden).congr hrep
    · intro x hx y hy hxy
      have hlift : ∀ z ∈ unitDisc, wB μ z = (fB μ z : ExtPlane) := by
        intro z hz
        rw [fB, hf z hz]
        rfl
      apply OnePoint.coe_injective
      apply (wB_bijective μ).injective
      rw [hlift x hx, hlift y hy, hxy]
  · have he : fB μ = id := by
      funext z
      simp [fB, wB, hex, finPart]
    rw [he]
    exact ⟨differentiableOn_id, injOn_id _⟩

/-- The three normalizations at the origin of Model B (TT:357) hold for its
finite part; derivatives only depend on its values in the disk. -/
theorem fB_normalization (μ : LinfStar) :
    fB μ 0 = 0 ∧ deriv (fB μ) 0 = 1 ∧
      ((∃ w, IsNormalizedB μ w) → wB μ (Function.invFun (wAS μ) extInf) = extInf) := by
  by_cases hex : ∃ w, IsNormalizedB μ w
  · have hB : IsNormalizedB μ (wB μ) := by
      simpa only [wB, dif_pos hex] using hex.choose_spec
    obtain ⟨M, _, W, _, _, _, f, hf, hf0, hf1, hfp⟩ := hB
    have he : fB μ =ᶠ[𝓝 (0 : ℂ)] f := by
      filter_upwards [show unitDisc ∈ 𝓝 (0 : ℂ) from
        isOpen_ball.mem_nhds (by simp [unitDisc])] with z hz
      rw [fB, hf z hz]
      rfl
    exact ⟨he.eq_of_nhds.trans hf0, he.deriv_eq.trans hf1, fun _ => hfp⟩
  · have hw : wB μ = id := by simp only [wB, dif_neg hex]
    have he : fB μ = id := by
      funext z
      simp [fB, hw, finPart]
    exact ⟨by simp [he], by simp [he, deriv_id''], fun h => absurd h hex⟩

/-- A Möbius map composed with the sphere extension of a plane solution is continuous. -/
theorem continuous_mobius_comp_map {M : ExtPlane → ExtPlane} (hM : IsMobius M) {W m : ℂ → ℂ}
    (hW : IsNormalizedSolution W m) : Continuous (fun p => M (OnePoint.map W p)) := by
  obtain ⟨⟨K, hK⟩, hs, -⟩ := hW
  obtain ⟨e, he⟩ := t1_homeomorph hK hs
  have hmap : (fun p => OnePoint.map W p) = e.onePointCongr := by
    funext p
    induction p using OnePoint.rec with
    | infty => rfl
    | coe z => simp [Homeomorph.onePointCongr_apply, he]
  obtain ⟨a, b, c, d, hdet, rfl⟩ := hM
  have h1 : Continuous (mobiusExt a b c d) := continuous_mobiusExt hdet
  have h2 : Continuous (fun p => OnePoint.map W p) := by
    rw [hmap]
    exact e.onePointCongr.continuous
  exact h1.comp h2

theorem wAS_continuous {μ : LinfStar} (hμ : μ ∈ LinfStarBall) : Continuous (wAS μ) := by
  obtain ⟨M, hM, W, hW, hwf, hwi, -⟩ := wA_spec hμ
  have h := continuous_mobius_comp_map hM hW
  have heq : wAS μ = fun p => M (OnePoint.map W p) := by
    funext p
    induction p using OnePoint.rec with
    | infty => exact hwi
    | coe z => exact hwf z
  rw [heq]
  exact h

theorem wB_continuous {μ : LinfStar} (hμ : μ ∈ LinfStarBall) : Continuous (wB μ) := by
  obtain ⟨hB, -⟩ := wB_spec hμ
  obtain ⟨M, hM, W, hW, hwf, hwi, -⟩ := hB
  have h := continuous_mobius_comp_map hM hW
  have heq : wB μ = fun p => M (OnePoint.map W p) := by
    funext p
    induction p using OnePoint.rec with
    | infty => exact hwi
    | coe z => exact hwf z
  rw [heq]
  exact h

/-- `w_μ` as a homeomorphism of the sphere. -/
theorem wAS_isHomeo {μ : LinfStar} (hμ : μ ∈ LinfStarBall) :
    ∃ e : ExtPlane ≃ₜ ExtPlane, ⇑e = wAS μ := by
  refine ⟨Continuous.homeoOfEquivCompactToT2 (f := Equiv.ofBijective (wAS μ) (wAS_bijective μ))
    (wAS_continuous hμ), rfl⟩

theorem wB_isHomeo {μ : LinfStar} (hμ : μ ∈ LinfStarBall) :
    ∃ e : ExtPlane ≃ₜ ExtPlane, ⇑e = wB μ := by
  refine ⟨Continuous.homeoOfEquivCompactToT2 (f := Equiv.ofBijective (wB μ) (wB_bijective μ))
    (wB_continuous hμ), rfl⟩

theorem wAS_invFun_continuous {μ : LinfStar} (hμ : μ ∈ LinfStarBall) :
    Continuous (Function.invFun (wAS μ)) := by
  obtain ⟨e, he⟩ := wAS_isHomeo hμ
  have : Function.invFun (wAS μ) = e.symm := by
    funext y
    rw [← he]
    have h : e (Function.invFun e y) = y := Function.invFun_eq ⟨e.symm y, e.apply_symm_apply y⟩
    apply e.injective
    rw [h, e.apply_symm_apply]
  rw [this]
  exact e.symm.continuous

theorem coe_mem_toExt_iff {s : Set ℂ} {z : ℂ} : (z : ExtPlane) ∈ toExt s ↔ z ∈ s :=
  OnePoint.coe_injective.mem_set_image

theorem infty_notMem_toExt (s : Set ℂ) : extInf ∉ toExt s := by
  rintro ⟨z, -, hz⟩
  exact OnePoint.coe_ne_infty z hz

theorem toExt_closedBall_eq : toExt (closedBall (0 : ℂ) 1) = toExt unitDisc ∪ toExt unitCircle := by
  unfold toExt
  rw [← image_union]
  congr 1
  ext z
  simp only [mem_closedBall_zero_iff, unitDisc, mem_ball_zero_iff, unitCircle, mem_union, mem_setOf_eq]
  exact le_iff_lt_or_eq

theorem not_mem_closed_iff (p : ExtPlane) :
    p ∉ toExt (closedBall (0 : ℂ) 1) ↔ p ∈ toExt unitDiscExterior ∪ {extInf} := by
  induction p using OnePoint.rec with
  | infty => exact ⟨fun _ => Or.inr rfl, fun _ => infty_notMem_toExt _⟩
  | coe z =>
    rw [mem_union, coe_mem_toExt_iff, coe_mem_toExt_iff]
    constructor
    · intro h
      left
      show 1 < ‖z‖
      simpa [mem_closedBall_zero_iff] using h
    · rintro (h | h)
      · have h' : 1 < ‖z‖ := h
        simp [mem_closedBall_zero_iff, h']
      · exact absurd (mem_singleton_iff.mp h) (OnePoint.coe_ne_infty z)

theorem welding_glue_map {μ ν : LinfStar} (hμ : μ ∈ LinfStarBall) (hν : ν ∈ LinfStarBall)
    (hcirc : ∀ z : ℂ, ‖z‖ = 1 → wAS μ (z : ExtPlane) = wAS ν (z : ExtPlane)) :
    ∃ G : ExtPlane → ExtPlane, Continuous G ∧ Function.Bijective G ∧
      (∀ p ∈ toExt (closedBall (0 : ℂ) 1), G p = p) ∧
      (∀ p ∉ toExt (closedBall (0 : ℂ) 1), G p = Function.invFun (wAS ν) (wAS μ p)) ∧
      (∀ p ∉ toExt (closedBall (0 : ℂ) 1),
        Function.invFun (wAS ν) (wAS μ p) ∉ toExt (closedBall (0 : ℂ) 1)) := by
  set Cl : Set ExtPlane := toExt (closedBall (0 : ℂ) 1) with hCl
  have himgCl : ∀ {ρ : LinfStar}, ρ ∈ LinfStarBall → wAS ρ '' Cl = Cl := by
    intro ρ hρ
    obtain ⟨hD, -, hC⟩ := wA_mapsTo hρ
    rw [hCl, toExt_closedBall_eq, image_union, hD, hC]
  have hmemCl : ∀ {ρ : LinfStar}, ρ ∈ LinfStarBall → ∀ p, p ∈ Cl ↔ wAS ρ p ∈ Cl := by
    intro ρ hρ p
    constructor
    · intro h
      rw [← himgCl hρ]
      exact mem_image_of_mem _ h
    · intro h
      rw [← himgCl hρ] at h
      obtain ⟨r, hr, hrp⟩ := h
      rwa [← (wAS_bijective ρ).1 hrp]
  have hinvν : ∀ q, wAS ν (Function.invFun (wAS ν) q) = q := fun q =>
    Function.invFun_eq ((wAS_bijective ν).2 q)
  have hinvνl : ∀ p, Function.invFun (wAS ν) (wAS ν p) = p := fun p =>
    Function.leftInverse_invFun (wAS_bijective ν).1 p
  have hmemInv : ∀ q, Function.invFun (wAS ν) q ∈ Cl ↔ q ∈ Cl := by
    intro q
    rw [hmemCl hν (Function.invFun (wAS ν) q), hinvν]
  set H : ExtPlane → ExtPlane := fun p => Function.invFun (wAS ν) (wAS μ p) with hH
  have hHcirc : ∀ z : ℂ, ‖z‖ = 1 → H (z : ExtPlane) = (z : ExtPlane) := by
    intro z hz
    show Function.invFun (wAS ν) (wAS μ (z : ExtPlane)) = _
    rw [hcirc z hz, hinvνl]
  have hHcont : Continuous H := (wAS_invFun_continuous hν).comp (wAS_continuous hμ)
  have hHinj : Function.Injective H := by
    intro p q hpq
    have h1 : wAS μ p = wAS μ q := by
      have := congrArg (wAS ν) hpq
      simp only [hH, hinvν] at this
      exact this
    exact (wAS_bijective μ).1 h1
  have hHnot : ∀ p, p ∉ Cl → H p ∉ Cl := by
    intro p hp
    show Function.invFun (wAS ν) (wAS μ p) ∉ Cl
    rw [hmemInv, ← hmemCl hμ]
    exact hp
  refine ⟨fun p => if p ∈ Cl then p else H p, ?_, ?_, ?_, ?_, hHnot⟩
  · have hCle : IsClosed Cl := by
      rw [hCl]
      exact ((isCompact_closedBall (0 : ℂ) 1).image OnePoint.continuous_coe).isClosed
    have hopen : IsOpen (toExt unitDisc) :=
      OnePoint.isOpenEmbedding_coe.isOpenMap _ isOpen_ball
    have hsub : toExt unitDisc ⊆ interior {a | a ∈ Cl} := by
      refine interior_maximal ?_ hopen
      intro x hx
      show x ∈ Cl
      rw [hCl, toExt_closedBall_eq]
      exact Or.inl hx
    refine Continuous.if ?_ continuous_id hHcont
    intro a ha
    have h1 : a ∈ Cl := by
      have := ha.1
      rwa [show {a | a ∈ Cl} = Cl from setOf_mem_eq, hCle.closure_eq] at this
    have h2 : a ∉ toExt unitDisc := fun h => ha.2 (hsub h)
    rw [hCl, toExt_closedBall_eq] at h1
    rcases h1 with h1 | h1
    · exact absurd h1 h2
    · obtain ⟨z, hz, rfl⟩ := h1
      exact (hHcirc z hz).symm
  · constructor
    · intro p q hpq
      by_cases hp : p ∈ Cl <;> by_cases hq : q ∈ Cl
      · simpa [hp, hq] using hpq
      · simp only [hp, hq, if_true, if_false] at hpq
        exact absurd (hpq ▸ hp) (hHnot q hq)
      · simp only [hp, hq, if_true, if_false] at hpq
        exact absurd (hpq ▸ hq) (hHnot p hp)
      · simp only [hp, hq, if_false] at hpq
        exact hHinj hpq
    · intro y
      by_cases hy : y ∈ Cl
      · exact ⟨y, by simp [hy]⟩
      · obtain ⟨q, hq⟩ := (wAS_bijective μ).2 (wAS ν y)
        have hqn : q ∉ Cl := by
          rw [hmemCl hμ, hq, ← hmemCl hν]
          exact hy
        refine ⟨q, ?_⟩
        simp only [hqn, if_false]
        show Function.invFun (wAS ν) (wAS μ q) = y
        rw [hq, hinvνl]
  · intro p hp
    simp [hp]
  · intro p hp
    simp [hp, hH]

theorem complexDilatation_eq_zero_of_diffAt {f : ℂ → ℂ} {z : ℂ} (h : DifferentiableAt ℂ f z) :
    complexDilatation f z = 0 := by
  have h2 := (cauchyRiemann_iff.1 h).2
  simp [complexDilatation, h2]

theorem isMobius_inverse {F : ExtPlane → ExtPlane} (hF : IsMobius F) :
    ∃ G : ExtPlane → ExtPlane, IsMobius G ∧ (∀ p, G (F p) = p) ∧ ∀ p, F (G p) = p := by
  obtain ⟨a, b, c, d, hdet, rfl⟩ := hF
  have hdet' : d * a - (-b) * (-c) ≠ 0 := by
    intro h
    apply hdet
    linear_combination h
  refine ⟨mobiusExt d (-b) (-c) a, ⟨d, -b, -c, a, hdet', rfl⟩, mobiusExt_inv_apply hdet, fun p => ?_⟩
  have := mobiusExt_inv_apply hdet' p
  simpa only [neg_neg] using this

theorem isMobius_injective {F : ExtPlane → ExtPlane} (hF : IsMobius F) : Function.Injective F := by
  obtain ⟨G, -, hGF, -⟩ := isMobius_inverse hF
  intro p q h
  rw [← hGF p, ← hGF q, h]

theorem exists_mobius_to_infty (c : ExtPlane) : ∃ R : ExtPlane → ExtPlane, IsMobius R ∧ R c = extInf := by
  induction c using OnePoint.rec with
  | infty =>
    refine ⟨mobiusExt 1 0 0 1, ⟨1, 0, 0, 1, by norm_num, rfl⟩, ?_⟩
    exact mobiusExt_infty_of_eq rfl
  | coe u =>
    refine ⟨mobiusExt 0 1 1 (-u), ⟨0, 1, 1, -u, by norm_num, rfl⟩, ?_⟩
    exact mobiusExt_coe_of_eq_zero (by ring)

theorem coe_finPart_of_ne {p : ExtPlane} (h : p ≠ extInf) : ((finPart p : ℂ) : ExtPlane) = p := by
  induction p using OnePoint.rec with
  | infty => exact absurd rfl h
  | coe u => rfl

theorem finPart_coe (u : ℂ) : finPart (u : ExtPlane) = u := rfl

theorem mobius_finite_open {M : ExtPlane → ExtPlane} (hM : IsMobius M) :
    IsOpen {u : ℂ | M (u : ExtPlane) ≠ extInf} := by
  obtain ⟨a, b, c, d, hdet, rfl⟩ := hM
  have hc : Continuous (fun u : ℂ => mobiusExt a b c d (u : ExtPlane)) :=
    (continuous_mobiusExt hdet).comp OnePoint.continuous_coe
  exact isOpen_compl_singleton.preimage hc

theorem mobius_finite_conformal {M : ExtPlane → ExtPlane} (hM : IsMobius M) :
    IsConformalOnto (fun u : ℂ => finPart (M (u : ExtPlane))) {u : ℂ | M (u : ExtPlane) ≠ extInf}
      ((fun u : ℂ => finPart (M (u : ExtPlane))) '' {u : ℂ | M (u : ExtPlane) ≠ extInf}) := by
  have hMi := isMobius_injective hM
  obtain ⟨a, b, c, d, hdet, rfl⟩ := hM
  refine ⟨?_, ?_, rfl⟩
  · intro u hu
    have hz : c * u + d ≠ 0 := fun h => hu (mobiusExt_coe_of_eq_zero h)
    have hnear : ∀ᶠ v : ℂ in 𝓝 u, c * v + d ≠ 0 :=
      ((continuousAt_const.mul continuousAt_id).add continuousAt_const).eventually_ne hz
    have heq : (fun v : ℂ => finPart (mobiusExt a b c d (v : ExtPlane))) =ᶠ[𝓝 u]
        (fun v => (a * v + b) / (c * v + d)) := by
      filter_upwards [hnear] with v hv
      rw [mobiusExt_coe hv]
      rfl
    exact ((hasDerivAt_mobius hz).differentiableAt.congr_of_eventuallyEq heq).differentiableWithinAt
  · intro u hu v hv huv
    have h1 := coe_finPart_of_ne (show mobiusExt a b c d (u : ExtPlane) ≠ extInf from hu)
    have h2 := coe_finPart_of_ne (show mobiusExt a b c d (v : ExtPlane) ≠ extInf from hv)
    have h3 : mobiusExt a b c d (u : ExtPlane) = mobiusExt a b c d (v : ExtPlane) := by
      rw [← h1, ← h2]
      exact congrArg _ huv
    exact OnePoint.coe_injective (hMi h3)

theorem normalized_solution_exterior_image {ρ : LinfStar} {W : ℂ → ℂ}
    (hW : IsNormalizedSolution W (extA ρ)) : W '' {w : ℂ | 1 < ‖w‖} = {w : ℂ | 1 < ‖w‖} := by
  ext w
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact normalized_solution_exterior hW hz
  · intro hw
    have hs : W '' univ = univ := hW.2.1
    have hw' : w ∈ W '' univ := by rw [hs]; exact mem_univ w
    obtain ⟨z, -, rfl⟩ := hw'
    refine ⟨z, ?_, rfl⟩
    by_contra hz
    have hz' : ‖z‖ ≤ 1 := not_lt.1 hz
    rcases hz'.lt_or_eq with h | h
    · have := normalized_solution_disc hW h
      have hw1 : 1 < ‖W z‖ := hw
      linarith
    · have := normalized_solution_circle hW h
      have hw1 : 1 < ‖W z‖ := hw
      linarith

theorem ext_piece_qc {μ ν : LinfStar} {s Wν Vν Ψ : ℂ → ℂ} {T Q : ExtPlane → ExtPlane}
    (hs : IsNormalizedSolution s (extA μ)) (hW : IsNormalizedSolution Wν (extA ν))
    (hV : IsNormalizedSolution Vν (extB ν)) (hT : IsMobius T) (hQ : IsMobius Q)
    (hmaps : ∀ z : ℂ, 1 < ‖z‖ → T (s z : ExtPlane) ≠ extInf →
      1 < ‖finPart (T (s z : ExtPlane))‖)
    (hfin : ∀ z : ℂ, 1 < ‖z‖ → T (s z : ExtPlane) ≠ extInf →
      Q ((Vν (Function.invFunOn Wν {w : ℂ | 1 < ‖w‖} (finPart (T (s z : ExtPlane)))) : ℂ) : ExtPlane)
        ≠ extInf)
    (hΨ : ∀ z : ℂ, 1 < ‖z‖ → T (s z : ExtPlane) ≠ extInf →
      Ψ z = finPart (Q ((Vν (Function.invFunOn Wν {w : ℂ | 1 < ‖w‖}
        (finPart (T (s z : ExtPlane)))) : ℂ) : ExtPlane))) :
    ∃ K : ℝ, IsKQC Ψ {z : ℂ | 1 < ‖z‖ ∧ T (s z : ExtPlane) ≠ extInf} K ∧
      ∀ᵐ z ∂(volume.restrict {z : ℂ | 1 < ‖z‖ ∧ T (s z : ExtPlane) ≠ extInf}),
        complexDilatation Ψ z = μ z := by
  obtain ⟨Ks, hKs⟩ := hs.1
  obtain ⟨KW, hKW⟩ := hW.1
  obtain ⟨KV, hKV⟩ := hV.1
  have hDo : IsOpen {w : ℂ | 1 < ‖w‖} := isOpen_lt continuous_const continuous_norm
  have hsc : Continuous s := continuousOn_univ.1 hKs.2.2.1.1
  have hΩo : IsOpen {z : ℂ | 1 < ‖z‖ ∧ T (s z : ExtPlane) ≠ extInf} := by
    refine hDo.inter ?_
    exact (mobius_finite_open hT).preimage hsc
  have hKsΩ := ac_t_isKQC_restrict hKs hΩo (subset_univ _)
  obtain ⟨h1K, h1d⟩ := bg_comp_conformal hKsΩ (mobius_finite_open hT) (mobius_finite_conformal hT)
    (by
      rintro _ ⟨z, hz, rfl⟩
      exact hz.2)
  have hKWD := ac_t_isKQC_restrict hKW hDo (subset_univ _)
  have hKVD := ac_t_isKQC_restrict hKV hDo (subset_univ _)
  have hdil : ∀ᵐ z ∂(volume.restrict {w : ℂ | 1 < ‖w‖}),
      complexDilatation Vν z = complexDilatation Wν z := by
    filter_upwards [ae_restrict_of_ae hV.2.2.2.2, ae_restrict_of_ae hW.2.2.2.2,
      ae_restrict_mem hDo.measurableSet] with z h1 h2 hz
    rw [h1, h2, extA_eq_on_exterior ν hz]
    simp only [extB, indicator_of_mem (show z ∈ unitDiscExterior from hz)]
  have hφ := bg_conformal_of_dilatation_eq hKWD hKVD hdil
  rw [normalized_solution_exterior_image hW] at hφ
  obtain ⟨h2K, h2d⟩ := bg_comp_conformal h1K hDo hφ
    (by
      rintro _ ⟨z, hz, rfl⟩
      exact hmaps z hz.1 hz.2)
  obtain ⟨h3K, h3d⟩ := bg_comp_conformal h2K (mobius_finite_open hQ) (mobius_finite_conformal hQ)
    (by
      rintro _ ⟨z, hz, rfl⟩
      exact hfin z hz.1 hz.2)
  have heq : EqOn Ψ ((fun u : ℂ => finPart (Q (u : ExtPlane))) ∘
      ((Vν ∘ Function.invFunOn Wν {w : ℂ | 1 < ‖w‖}) ∘
        ((fun u : ℂ => finPart (T (u : ExtPlane))) ∘ s)))
      {z : ℂ | 1 < ‖z‖ ∧ T (s z : ExtPlane) ≠ extInf} := fun z hz => hΨ z hz.1 hz.2
  refine ⟨Ks, ad_isKQC_congr h3K heq, ?_⟩
  filter_upwards [h1d, h2d, h3d, ae_restrict_of_ae hs.2.2.2.2,
    ae_restrict_mem hΩo.measurableSet] with z a1 a2 a3 a4 hz
  rw [bg_dilatation_congr hΩo heq hz, a3, a2, a1, a4]
  exact extA_eq_on_exterior μ hz.1

theorem int_piece_qc {ν : LinfStar} (hν : ν ∈ LinfStarBall) {R : ExtPlane → ExtPlane}
    (hR : IsMobius R) {Ψ : ℂ → ℂ}
    (hfin : ∀ z ∈ unitDisc, R ((fB ν z : ℂ) : ExtPlane) ≠ extInf)
    (hΨ : ∀ z ∈ unitDisc, Ψ z = finPart (R ((fB ν z : ℂ) : ExtPlane))) :
    IsKQC Ψ unitDisc 1 ∧ ∀ᵐ z ∂(volume.restrict unitDisc), complexDilatation Ψ z = 0 := by
  obtain ⟨hd, hi⟩ := fB_holomorphic_injective hν
  have hUo : IsOpen unitDisc := isOpen_ball
  have h1 : IsKQC (fB ν) unitDisc 1 := isKQC_one_of_conformal hUo ⟨hd, hi, rfl⟩
  obtain ⟨h2K, h2d⟩ := bg_comp_conformal h1 (mobius_finite_open hR) (mobius_finite_conformal hR)
    (by
      rintro _ ⟨z, hz, rfl⟩
      exact hfin z hz)
  have heq : EqOn Ψ ((fun u : ℂ => finPart (R (u : ExtPlane))) ∘ fB ν) unitDisc := hΨ
  refine ⟨ad_isKQC_congr h2K heq, ?_⟩
  filter_upwards [h2d, ae_restrict_mem hUo.measurableSet] with z a1 hz
  rw [bg_dilatation_congr hUo heq hz, a1]
  exact complexDilatation_eq_zero_of_diffAt ((hd z hz).differentiableAt (hUo.mem_nhds hz))

theorem plane_map_of_sphere_homeo {F : ExtPlane → ExtPlane} (hF : Function.Bijective F)
    (hFc : Continuous F) :
    ∃ R : ExtPlane → ExtPlane, IsMobius R ∧ ∃ F₁ : ℂ → ℂ, Continuous F₁ ∧ Function.Bijective F₁ ∧
      (∀ u : ℂ, R (F (u : ExtPlane)) = ((F₁ u : ℂ) : ExtPlane)) ∧ R (F extInf) = extInf := by
  obtain ⟨R, hR, hRq⟩ := exists_mobius_to_infty (F extInf)
  have hRi := isMobius_injective hR
  have hfin : ∀ u : ℂ, R (F (u : ExtPlane)) ≠ extInf := by
    intro u h
    have : F (u : ExtPlane) = F extInf := hRi (h.trans hRq.symm)
    exact OnePoint.coe_ne_infty u (hF.1 this)
  refine ⟨R, hR, fun u => finPart (R (F (u : ExtPlane))), ?_, ?_, fun u => ?_, hRq⟩
  · obtain ⟨a, b, c, d, hdet, rfl⟩ := hR
    rw [OnePoint.isOpenEmbedding_coe.isEmbedding.continuous_iff]
    have : (((↑) : ℂ → ExtPlane) ∘ fun u : ℂ => finPart (mobiusExt a b c d (F (u : ExtPlane)))) =
        fun u : ℂ => mobiusExt a b c d (F (u : ExtPlane)) := by
      funext u
      exact coe_finPart_of_ne (hfin u)
    rw [this]
    exact (continuous_mobiusExt hdet).comp (hFc.comp OnePoint.continuous_coe)
  · constructor
    · intro u v huv
      have h1 := congrArg (fun x : ℂ => (x : ExtPlane)) huv
      simp only [coe_finPart_of_ne (hfin u), coe_finPart_of_ne (hfin v)] at h1
      exact OnePoint.coe_injective (hF.1 (hRi h1))
    · intro w
      obtain ⟨G, -, hGR, hRG⟩ := isMobius_inverse hR
      obtain ⟨p, hp⟩ := hF.2 (G (w : ExtPlane))
      induction p using OnePoint.rec with
      | infty =>
        have : R (F extInf) = (w : ExtPlane) := by rw [hp, hRG]
        rw [hRq] at this
        exact absurd this.symm (OnePoint.coe_ne_infty w)
      | coe u =>
        refine ⟨u, ?_⟩
        have h1 : R (F (u : ExtPlane)) = (w : ExtPlane) := by rw [hp, hRG]
        show finPart (R (F (u : ExtPlane))) = w
        rw [h1]
        rfl
  · exact (coe_finPart_of_ne (hfin u)).symm

theorem ext_sphere_data {μ ν : LinfStar}
    {Mμ Mν Mνinv N : ExtPlane → ExtPlane} {s Wν Vν : ℂ → ℂ}
    (hWν : IsNormalizedSolution Wν (extA ν))
    (hwfμ : ∀ z : ℂ, wAS μ (z : ExtPlane) = Mμ ((s z : ℂ) : ExtPlane))
    (hwfν : ∀ z : ℂ, wAS ν (z : ExtPlane) = Mν ((Wν z : ℂ) : ExtPlane))
    (hwiν : wAS ν extInf = Mν extInf)
    (hMνinv : ∀ p, Mνinv (Mν p) = p)
    (hvfν : ∀ z : ℂ, wB ν (z : ExtPlane) = N ((Vν z : ℂ) : ExtPlane))
    {G : ExtPlane → ExtPlane}
    (hG2 : ∀ p ∉ toExt (closedBall (0 : ℂ) 1), G p = Function.invFun (wAS ν) (wAS μ p))
    (hG3 : ∀ p ∉ toExt (closedBall (0 : ℂ) 1),
      Function.invFun (wAS ν) (wAS μ p) ∉ toExt (closedBall (0 : ℂ) 1))
    (hbij : Function.Bijective (wAS ν))
    {z : ℂ} (hz : 1 < ‖z‖) {y : ℂ}
    (hy : Mνinv (Mμ ((s z : ℂ) : ExtPlane)) = (y : ExtPlane)) :
    1 < ‖y‖ ∧
      wB ν (G (z : ExtPlane)) =
        N ((Vν (Function.invFunOn Wν {w : ℂ | 1 < ‖w‖} y) : ℂ) : ExtPlane) := by
  have hzCl : (z : ExtPlane) ∉ toExt (closedBall (0 : ℂ) 1) := by
    rw [coe_mem_toExt_iff, mem_closedBall_zero_iff, not_le]
    exact hz
  rw [hG2 _ hzCl]
  have hg1 : wAS ν (Function.invFun (wAS ν) (wAS μ (z : ExtPlane))) = wAS μ (z : ExtPlane) :=
    Function.invFun_eq (hbij.2 _)
  have hgCl := hG3 _ hzCl
  generalize Function.invFun (wAS ν) (wAS μ (z : ExtPlane)) = g at hg1 hgCl
  rw [hwfμ z] at hg1
  induction g using OnePoint.rec with
  | infty =>
    rw [hwiν] at hg1
    rw [← hg1, hMνinv] at hy
    exact absurd hy (OnePoint.coe_ne_infty y).symm
  | coe w =>
    rw [hwfν w] at hg1
    have hWy : Wν w = y := by
      have := hMνinv ((Wν w : ℂ) : ExtPlane)
      rw [hg1, hy] at this
      exact (OnePoint.coe_injective this).symm
    have hw : 1 < ‖w‖ := by
      rw [coe_mem_toExt_iff, mem_closedBall_zero_iff, not_le] at hgCl
      exact hgCl
    refine ⟨?_, ?_⟩
    · rw [← hWy]
      exact normalized_solution_exterior hWν hw
    · have hinv : Function.invFunOn Wν {w : ℂ | 1 < ‖w‖} y = w := by
        rw [← hWy]
        exact (normalized_solution_injective hWν).injOn.leftInvOn_invFunOn hw
      rw [hinv]
      exact hvfν w

theorem wAS_closed_image {ρ : LinfStar} (hρ : ρ ∈ LinfStarBall) :
    wAS ρ '' toExt (closedBall (0 : ℂ) 1) = toExt (closedBall (0 : ℂ) 1) := by
  obtain ⟨hD, -, hC⟩ := wA_mapsTo hρ
  rw [toExt_closedBall_eq, image_union, hD, hC]

theorem iskqc_of_subsingleton_exceptional {Ω : Set ℂ} {g : ℂ → ℂ} {K : ℝ} {P : ℂ → Prop}
    (hΩ : IsOpen Ω) (hg : IsHomeomorphOnto g Ω (g '' Ω)) (hK : 1 ≤ K)
    (hPΩ : {z | P z} ⊆ Ω) (hsub : {z | z ∈ Ω ∧ ¬ P z}.Subsingleton)
    (hloc : IsKQC g {z | P z} K) : IsKQC g Ω K := by
  have hfin : {z | z ∈ Ω ∧ ¬ P z}.Finite := hsub.finite
  refine s13x_removable (L := {z | z ∈ Ω ∧ ¬ P z}) hΩ hK hg (hfin.measure_zero volume) ?_ ?_ ?_
  · refine Filter.Eventually.of_forall fun x => ?_
    refine Set.Subsingleton.countable (fun y1 hy1 y2 hy2 => ?_)
    have := hsub hy1 hy2
    have h2 := congrArg Complex.im this
    simpa using h2
  · refine Filter.Eventually.of_forall fun y => ?_
    refine Set.Subsingleton.countable (fun x1 hx1 x2 hx2 => ?_)
    have := hsub hx1 hx2
    have h2 := congrArg Complex.re this
    simpa using h2
  · intro z hz
    have hzP : P z := by
      by_contra h
      exact hz.2 ⟨hz.1, h⟩
    exact ⟨{z | P z}, hloc.1, hzP, hPΩ, hloc⟩

theorem wB_eq_of_circle_eq {μ ν : LinfStar} (hμ : μ ∈ LinfStarBall) (hν : ν ∈ LinfStarBall)
    (hcirc : ∀ z : ℂ, ‖z‖ = 1 → wAS μ (z : ExtPlane) = wAS ν (z : ExtPlane)) :
    ∀ z ∈ unitDisc, wB μ (z : ExtPlane) = wB ν (z : ExtPlane) := by
  obtain ⟨G, hGc, hGb, hG1, hG2, hG3⟩ := welding_glue_map hμ hν hcirc
  obtain ⟨F, hFdef⟩ : ∃ F : ExtPlane → ExtPlane, F = fun p => wB ν (G p) := ⟨_, rfl⟩
  have hFz : ∀ p, F p = wB ν (G p) := fun p => by rw [hFdef]
  have hFb : Function.Bijective F := by
    rw [hFdef]
    exact (wB_bijective ν).comp hGb
  have hFc : Continuous F := by
    rw [hFdef]
    exact (wB_continuous hν).comp hGc
  obtain ⟨R, hR, F₁, hF₁c, hF₁b, hRF, hRq⟩ := plane_map_of_sphere_homeo hFb hFc
  obtain ⟨hBν, -⟩ := wB_spec hν
  obtain ⟨N, hN, Vν, hVν, hvfν, hvi, f, hf, hf0, hf1, hfp⟩ := hBν
  obtain ⟨Mν, hMν, Wν, hWν, hwfν, hwiν, -, -, -⟩ := wA_spec hν
  obtain ⟨Mμ, hMμ, s, hs, hwfμ, hwiμ, -, -, -⟩ := wA_spec hμ
  obtain ⟨Mνinv, hMνinv, hMνl, -⟩ := isMobius_inverse hMν
  have hRF' : ∀ u : ℂ, (F₁ u : ExtPlane) = R (F (u : ExtPlane)) := fun u => (hRF u).symm
  have hF₁fin : ∀ u : ℂ, R (F (u : ExtPlane)) ≠ extInf := by
    intro u h
    rw [hRF u] at h
    exact OnePoint.coe_ne_infty _ h
  -- the interior
  have hGin : ∀ z ∈ unitDisc, G (z : ExtPlane) = (z : ExtPlane) := by
    intro z hz
    apply hG1
    rw [coe_mem_toExt_iff, mem_closedBall_zero_iff]
    exact (mem_ball_zero_iff.1 hz).le
  have hFin : ∀ z ∈ unitDisc, F (z : ExtPlane) = ((fB ν z : ℂ) : ExtPlane) := by
    intro z hz
    rw [hFdef]
    show wB ν (G (z : ExtPlane)) = _
    rw [hGin z hz]
    have h1 : wB ν (z : ExtPlane) = ((f z : ℂ) : ExtPlane) := hf z hz
    have h2 : fB ν z = f z := by
      show finPart (wB ν (z : ExtPlane)) = _
      rw [h1]
      rfl
    rw [h1, h2]
  have hint := int_piece_qc hν hR (Ψ := F₁)
    (fun z hz => by
      rw [← hFin z hz]
      exact hF₁fin z)
    (fun z hz => by
      rw [← hFin z hz, hRF z]
      rfl)
  -- the exterior
  have hQ : IsMobius (fun w => R (N w)) := isMobius_comp hN hR
  have hT : IsMobius (fun w => Mνinv (Mμ w)) := isMobius_comp hMμ hMνinv
  have hbij := wAS_bijective ν
  have hdata : ∀ z : ℂ, 1 < ‖z‖ → Mνinv (Mμ ((s z : ℂ) : ExtPlane)) ≠ extInf →
      1 < ‖finPart (Mνinv (Mμ ((s z : ℂ) : ExtPlane)))‖ ∧
      wB ν (G (z : ExtPlane)) = N ((Vν (Function.invFunOn Wν {w : ℂ | 1 < ‖w‖}
        (finPart (Mνinv (Mμ ((s z : ℂ) : ExtPlane))))) : ℂ) : ExtPlane) := by
    intro z hz hne
    exact ext_sphere_data hWν hwfμ hwfν hwiν hMνl hvfν hG2 hG3 hbij hz
      (coe_finPart_of_ne hne).symm
  have hext := ext_piece_qc (μ := μ) (ν := ν) (s := s) (Wν := Wν) (Vν := Vν) (Ψ := F₁)
    (T := fun w => Mνinv (Mμ w)) (Q := fun w => R (N w)) hs hWν hVν hT hQ
    (fun z hz hne => (hdata z hz hne).1)
    (fun z hz hne => by
      have h := (hdata z hz hne).2
      show R (N _) ≠ extInf
      rw [← h, ← hFz]
      exact hF₁fin z)
    (fun z hz hne => by
      have h := (hdata z hz hne).2
      show F₁ z = finPart (R (N _))
      rw [← h, ← hFz, hRF z]
      rfl)
  obtain ⟨K₀, hΩK, hΩd⟩ := hext
  have hDo : IsOpen {z : ℂ | 1 < ‖z‖} := isOpen_lt continuous_const continuous_norm
  have hK1 : 1 ≤ K₀ := hΩK.2.1
  have hF₁hom : IsHomeomorphOnto F₁ {z : ℂ | 1 < ‖z‖} (F₁ '' {z : ℂ | 1 < ‖z‖}) :=
    qcl_f_isHomeomorphOnto_of_injOn hDo hF₁c.continuousOn hF₁b.1.injOn
  have hsc : Function.Injective s := normalized_solution_injective hs
  have hTinj := isMobius_injective hT
  have hEsub : {z : ℂ | z ∈ {z : ℂ | 1 < ‖z‖} ∧
      ¬ (1 < ‖z‖ ∧ Mνinv (Mμ ((s z : ℂ) : ExtPlane)) ≠ extInf)}.Subsingleton := by
    intro z1 hz1 z2 hz2
    have e1 : Mνinv (Mμ ((s z1 : ℂ) : ExtPlane)) = extInf := by
      by_contra h
      exact hz1.2 ⟨hz1.1, h⟩
    have e2 : Mνinv (Mμ ((s z2 : ℂ) : ExtPlane)) = extInf := by
      by_contra h
      exact hz2.2 ⟨hz2.1, h⟩
    have h3 : (fun w => Mνinv (Mμ w)) ((s z1 : ℂ) : ExtPlane) =
        (fun w => Mνinv (Mμ w)) ((s z2 : ℂ) : ExtPlane) := e1.trans e2.symm
    exact hsc (OnePoint.coe_injective (hTinj h3))
  have hout : IsKQC F₁ {z : ℂ | 1 < ‖z‖} K₀ :=
    iskqc_of_subsingleton_exceptional
      (P := fun z => 1 < ‖z‖ ∧ Mνinv (Mμ ((s z : ℂ) : ExtPlane)) ≠ extInf)
      hDo hF₁hom hK1 (fun z hz => hz.1) hEsub hΩK
  have hhom : IsHomeomorphOnto F₁ univ univ := by
    have := qcl_f_isHomeomorphOnto_of_injOn isOpen_univ hF₁c.continuousOn hF₁b.1.injOn
    rwa [image_univ_of_surjective hF₁b.2] at this
  have hKuniv : IsKQC F₁ univ K₀ := abR_removable hhom (hint.1.mono hK1) hout
  have hdil : ∀ᵐ z : ℂ, complexDilatation F₁ z = extB μ z := by
    have h1 : ∀ᵐ z : ℂ, z ∈ unitDisc → complexDilatation F₁ z = 0 :=
      (ae_restrict_iff' (show IsOpen unitDisc from isOpen_ball).measurableSet).1 hint.2
    have h2 : ∀ᵐ z : ℂ, (1 < ‖z‖ ∧ Mνinv (Mμ ((s z : ℂ) : ExtPlane)) ≠ extInf) →
        complexDilatation F₁ z = μ z :=
      (ae_restrict_iff' hΩK.1.measurableSet).1 hΩd
    have h3 := measure_eq_zero_iff_ae_notMem.1 (hEsub.finite.measure_zero volume)
    have h4 : ∀ᵐ z : ℂ, z ∉ Metric.sphere (0 : ℂ) 1 :=
      measure_eq_zero_iff_ae_notMem.1 (Measure.addHaar_sphere volume 0 1)
    filter_upwards [h1, h2, h3, h4] with z a b c d
    rcases lt_trichotomy ‖z‖ 1 with h | h | h
    · have hz : z ∉ unitDiscExterior := fun hh => absurd (show 1 < ‖z‖ from hh) (not_lt.2 h.le)
      rw [a (mem_ball_zero_iff.2 h), extB, indicator_of_notMem hz]
    · exact absurd (mem_sphere_zero_iff_norm.2 h) d
    · have hzE : 1 < ‖z‖ ∧ Mνinv (Mμ ((s z : ℂ) : ExtPlane)) ≠ extInf := by
        by_contra hn
        exact c ⟨h, hn⟩
      rw [b hzE, extB, indicator_of_mem (show z ∈ unitDiscExterior from h)]
  obtain ⟨Nμ, hNμ, V, hV, -, -, -⟩ := (wB_spec hμ).1
  have hF₁q : IsQuasiconformal F₁ univ := ⟨K₀, hKuniv⟩
  obtain ⟨φ, hφ, hVφ⟩ := uq_conformal_auto isOpen_univ hF₁q hV.1
    (image_univ_of_surjective hF₁b.2) hV.2.1
    (by
      rw [Measure.restrict_univ]
      filter_upwards [hdil, hV.2.2.2.2] with z a b
      rw [a, b])
  obtain ⟨a, b, ha, hab⟩ := nx_entire_affine hφ
  have hVu : ∀ u, V u = a * F₁ u + b := fun u => by rw [hVφ u (mem_univ u), hab]
  obtain ⟨Rinv, hRinv, hRinvR, -⟩ := isMobius_inverse hR
  have haff : IsMobius (mobiusExt a⁻¹ (-(b / a)) 0 1) :=
    ⟨a⁻¹, -(b / a), 0, 1, by simp [ha], rfl⟩
  have haffv : ∀ u : ℂ, mobiusExt a⁻¹ (-(b / a)) 0 1 ((V u : ℂ) : ExtPlane) =
      ((F₁ u : ℂ) : ExtPlane) := by
    intro u
    rw [mobiusExt_coe (by simp)]
    congr 1
    simp only [mobiusFn, zero_mul, zero_add, div_one, hVu]
    field_simp
    ring
  have haffinf : mobiusExt a⁻¹ (-(b / a)) 0 1 extInf = extInf := mobiusExt_infty_of_eq rfl
  have hM' : IsMobius (fun w => Rinv (mobiusExt a⁻¹ (-(b / a)) 0 1 w)) := isMobius_comp haff hRinv
  have hNB : IsNormalizedB μ F := by
    refine ⟨_, hM', V, hV, fun u => ?_, ?_, f, fun z hz => ?_, hf0, hf1, ?_⟩
    · show F (u : ExtPlane) = Rinv (mobiusExt _ _ _ _ _)
      rw [haffv u, ← hRF u, hRinvR]
    · show F extInf = Rinv (mobiusExt _ _ _ _ _)
      rw [haffinf]
      calc F extInf = Rinv (R (F extInf)) := (hRinvR _).symm
        _ = Rinv extInf := by rw [hRq]
    · rw [hFz, hGin z hz]
      exact hf z hz
    · have hp : wAS μ (Function.invFun (wAS μ) extInf) = extInf :=
        Function.invFun_eq ((wAS_bijective μ).2 _)
      have hpCl : Function.invFun (wAS μ) extInf ∉ toExt (closedBall (0 : ℂ) 1) := by
        intro h
        have := mem_image_of_mem (wAS μ) h
        rw [wAS_closed_image hμ, hp] at this
        exact infty_notMem_toExt _ this
      rw [hFz, hG2 _ hpCl, hp]
      exact hfp
  have hFeq : F = wB μ := IsNormalizedB.unique hNB (wB_spec hμ).1
  intro z hz
  rw [← hFeq, hFz, hGin z hz]

theorem modelA_to_modelB (μ ν : LinfStarBall)
    (h : ∀ z ∈ unitCircle, wA μ.1 z = wA ν.1 z) : ∀ z ∈ unitDisc, fB μ.1 z = fB ν.1 z := by
  have hcirc : ∀ z : ℂ, ‖z‖ = 1 → wAS μ.1 (z : ExtPlane) = wAS ν.1 (z : ExtPlane) := by
    intro z hz
    obtain ⟨u, -, hu⟩ := wAS_maps_circle μ.2 hz
    obtain ⟨u', -, hu'⟩ := wAS_maps_circle ν.2 hz
    have h1 := h z hz
    simp only [wA, hu, hu'] at h1
    rw [hu, hu']
    exact congrArg _ h1
  intro z hz
  have := wB_eq_of_circle_eq μ.2 ν.2 hcirc z hz
  show finPart (wB μ.1 (z : ExtPlane)) = finPart (wB ν.1 (z : ExtPlane))
  rw [this]

/-- The relation of Model A (TT:351): `μ ∼ ν` iff `w_μ|S¹ = w_ν|S¹`. -/
def teichSetoid : Setoid LinfStarBall where
  r μ ν := ∀ z ∈ unitCircle, wA μ z = wA ν z
  iseqv := ⟨fun _ _ _ => rfl, fun h z hz => (h z hz).symm, fun h₁ h₂ z hz => (h₁ z hz).trans (h₂ z hz)⟩

/-- **The universal Teichmüller space** `T(1) = L∞(𝔻*)₁/∼` (TT:351), with the quotient topology (TT:363). -/
def T1 : Type := Quotient teichSetoid

instance : TopologicalSpace T1 := inferInstanceAs (TopologicalSpace (Quotient teichSetoid))

/-- The canonical projection `Φ : L∞(𝔻*)₁ → T(1)`, `μ ↦ [μ]` (TT:366). -/
def Phi (μ : LinfStarBall) : T1 := Quotient.mk teichSetoid μ

instance : Nonempty T1 := ⟨Phi ⟨0, mem_ball_self one_pos⟩⟩

theorem wB_disc_eq_fB {ρ : LinfStar} (hρ : ρ ∈ LinfStarBall) {z : ℂ} (hz : z ∈ unitDisc) :
    wB ρ (z : ExtPlane) = ((fB ρ z : ℂ) : ExtPlane) := by
  obtain ⟨hB, -⟩ := wB_spec hρ
  obtain ⟨N, hN, V, hV, -, -, f, hf, -⟩ := hB
  have h1 : wB ρ (z : ExtPlane) = ((f z : ℂ) : ExtPlane) := hf z hz
  have h2 : fB ρ z = f z := by
    show finPart (wB ρ (z : ExtPlane)) = _
    rw [h1]
    rfl
  rw [h1, h2]

theorem wB_eq_closed {μ ν : LinfStar} (hμ : μ ∈ LinfStarBall) (hν : ν ∈ LinfStarBall)
    (h : ∀ z ∈ unitDisc, fB μ z = fB ν z) :
    ∀ p ∈ toExt (closedBall (0 : ℂ) 1), wB μ p = wB ν p := by
  have hD : ∀ p ∈ toExt unitDisc, wB μ p = wB ν p := by
    rintro _ ⟨z, hz, rfl⟩
    rw [wB_disc_eq_fB hμ hz, wB_disc_eq_fB hν hz, h z hz]
  have hcl : EqOn (wB μ) (wB ν) (closure (toExt unitDisc)) :=
    EqOn.closure hD (wB_continuous hμ) (wB_continuous hν)
  intro p hp
  apply hcl
  rcases hp with ⟨z, hz, rfl⟩
  have hz' : z ∈ closure unitDisc := by
    rw [unitDisc, closure_ball _ one_ne_zero]
    exact hz
  exact (image_closure_subset_closure_image OnePoint.continuous_coe) ⟨z, hz', rfl⟩

theorem wB_glue_props {μ ν : LinfStar} (hν : ν ∈ LinfStarBall)
    (hBeq : ∀ p ∈ toExt (closedBall (0 : ℂ) 1), wB μ p = wB ν p) :
    (∀ p ∈ toExt (closedBall (0 : ℂ) 1), Function.invFun (wB ν) (wB μ p) = p) ∧
    (∀ p ∉ toExt (closedBall (0 : ℂ) 1), Function.invFun (wB ν) (wB μ p) ∉
      toExt (closedBall (0 : ℂ) 1)) := by
  refine ⟨fun p hp => ?_, fun p hp hq => ?_⟩
  · rw [hBeq p hp]
    exact Function.leftInverse_invFun (wB_bijective ν).1 p
  · have e : wB ν (Function.invFun (wB ν) (wB μ p)) = wB μ p :=
      Function.invFun_eq ((wB_bijective ν).2 _)
    have e2 := hBeq _ hq
    have e3 := (wB_bijective μ).1 (e2.trans e)
    exact hp (e3 ▸ hq)

theorem sigma_coe {z : ℂ} (hz : z ≠ 0) :
    mobiusExt 0 1 1 0 (z : ExtPlane) = ((z⁻¹ : ℂ) : ExtPlane) := by
  rw [mobiusExt_coe (by simpa using hz)]
  congr 1
  simp [mobiusFn]

theorem sigma_zero : mobiusExt 0 1 1 0 ((0 : ℂ) : ExtPlane) = extInf :=
  mobiusExt_coe_of_eq_zero (by simp)

theorem sigma_infty : mobiusExt 0 1 1 0 extInf = ((0 : ℂ) : ExtPlane) := by
  rw [mobiusExt_infty_of_ne one_ne_zero]
  simp

theorem sigma_invol (p : ExtPlane) : mobiusExt 0 1 1 0 (mobiusExt 0 1 1 0 p) = p := by
  induction p using OnePoint.rec with
  | infty => rw [sigma_infty, sigma_zero]
  | coe z =>
    by_cases hz : z = 0
    · subst hz
      rw [sigma_zero, sigma_infty]
    · rw [sigma_coe hz, sigma_coe (inv_ne_zero hz), inv_inv]

theorem sigma_not_closed {w : ℂ} (hw : w ∈ unitDisc) :
    mobiusExt 0 1 1 0 (w : ExtPlane) ∉ toExt (closedBall (0 : ℂ) 1) := by
  by_cases h0 : w = 0
  · subst h0
    rw [sigma_zero]
    exact infty_notMem_toExt _
  · rw [sigma_coe h0, coe_mem_toExt_iff, mem_closedBall_zero_iff, not_le, norm_inv]
    have hw' : ‖w‖ < 1 := mem_ball_zero_iff.1 hw
    exact (one_lt_inv₀ (norm_pos_iff.2 h0)).2 hw'

theorem sigma_of_not_closed {p : ExtPlane} (hp : p ∉ toExt (closedBall (0 : ℂ) 1)) :
    ∃ y : ℂ, mobiusExt 0 1 1 0 p = (y : ExtPlane) ∧ y ∈ unitDisc := by
  induction p using OnePoint.rec with
  | infty => exact ⟨0, sigma_infty, by simp [unitDisc]⟩
  | coe z =>
    rw [coe_mem_toExt_iff, mem_closedBall_zero_iff, not_le] at hp
    have hz0 : z ≠ 0 := norm_ne_zero_iff.1 (by linarith)
    refine ⟨z⁻¹, sigma_coe hz0, ?_⟩
    rw [unitDisc, mem_ball_zero_iff, norm_inv]
    exact inv_lt_one_of_one_lt₀ hp

theorem finite_preimage_data {Φ M Minv : ExtPlane → ExtPlane} {W : ℂ → ℂ}
    (hfin : ∀ z : ℂ, Φ (z : ExtPlane) = M ((W z : ℂ) : ExtPlane)) (hinf : Φ extInf = M extInf)
    (hMinv : ∀ p, Minv (M p) = p) {q x : ExtPlane} (hq : Φ q = x)
    (hqCl : q ∉ toExt (closedBall (0 : ℂ) 1)) {v : ℂ} (hv : Minv x = (v : ExtPlane)) :
    ∃ u : ℂ, q = (u : ExtPlane) ∧ W u = v ∧ 1 < ‖u‖ := by
  induction q using OnePoint.rec with
  | infty =>
    rw [hinf] at hq
    rw [← hq, hMinv] at hv
    exact absurd hv (OnePoint.coe_ne_infty v).symm
  | coe u =>
    refine ⟨u, rfl, ?_, ?_⟩
    · rw [hfin u] at hq
      rw [← hq, hMinv] at hv
      exact OnePoint.coe_injective hv
    · rw [coe_mem_toExt_iff, mem_closedBall_zero_iff, not_le] at hqCl
      exact hqCl

theorem differentiableOn_of_finite_exceptional {f : ℂ → ℂ} {s E : Set ℂ} (hs : IsOpen s)
    (hE : E.Finite) (hc : ContinuousOn f s) (hd : DifferentiableOn ℂ f (s \ E)) :
    DifferentiableOn ℂ f s := by
  induction E, hE using Set.Finite.induction_on generalizing s with
  | empty => simpa using hd
  | @insert a E' ha hE' ih =>
    by_cases has : a ∈ s
    · have hs' : IsOpen (s \ E') := hs.sdiff hE'.isClosed
      have has' : a ∈ s \ E' := ⟨has, fun h => ha h⟩
      have h1 : DifferentiableOn ℂ f (s \ E') := by
        rw [← differentiableOn_compl_singleton_and_continuousAt_iff (hs'.mem_nhds has')]
        refine ⟨?_, (hc.continuousAt (hs.mem_nhds has))⟩
        refine hd.mono ?_
        intro x hx
        refine ⟨hx.1.1, ?_⟩
        rintro (h | h)
        · exact hx.2 h
        · exact hx.1.2 h
      exact ih hs hc h1
    · have : s \ insert a E' = s \ E' := by
        ext x
        simp only [mem_diff, mem_insert_iff, not_or]
        constructor
        · rintro ⟨h1, -, h3⟩
          exact ⟨h1, h3⟩
        · rintro ⟨h1, h3⟩
          exact ⟨h1, fun h => has (h ▸ h1), h3⟩
      rw [this] at hd
      exact ih hs hc hd

theorem wB_invFun_continuous {μ : LinfStar} (hμ : μ ∈ LinfStarBall) :
    Continuous (Function.invFun (wB μ)) := by
  obtain ⟨e, he⟩ := wB_isHomeo hμ
  have : Function.invFun (wB μ) = e.symm := by
    funext y
    rw [← he]
    have h : e (Function.invFun e y) = y := Function.invFun_eq ⟨e.symm y, e.apply_symm_apply y⟩
    apply e.injective
    rw [h, e.apply_symm_apply]
  rw [this]
  exact e.symm.continuous

theorem wAS_closed_iff {ρ : LinfStar} (hρ : ρ ∈ LinfStarBall) (p : ExtPlane) :
    p ∈ toExt (closedBall (0 : ℂ) 1) ↔ wAS ρ p ∈ toExt (closedBall (0 : ℂ) 1) := by
  constructor
  · intro h
    rw [← wAS_closed_image hρ]
    exact mem_image_of_mem _ h
  · intro h
    rw [← wAS_closed_image hρ] at h
    obtain ⟨r, hr, hrp⟩ := h
    rwa [← (wAS_bijective ρ).1 hrp]

theorem transition_conformal {ρ : LinfStar} {W V : ℂ → ℂ} (hW : IsNormalizedSolution W (extA ρ))
    (hV : IsNormalizedSolution V (extB ρ)) :
    IsConformalOnto (V ∘ Function.invFunOn W {w : ℂ | 1 < ‖w‖}) {w : ℂ | 1 < ‖w‖}
      (V '' {w : ℂ | 1 < ‖w‖}) ∧
    IsConformalOnto (W ∘ Function.invFunOn V {w : ℂ | 1 < ‖w‖}) (V '' {w : ℂ | 1 < ‖w‖})
      {w : ℂ | 1 < ‖w‖} := by
  obtain ⟨KW, hKW⟩ := hW.1
  obtain ⟨KV, hKV⟩ := hV.1
  have hDo : IsOpen {w : ℂ | 1 < ‖w‖} := isOpen_lt continuous_const continuous_norm
  have hKWD := ac_t_isKQC_restrict hKW hDo (subset_univ _)
  have hKVD := ac_t_isKQC_restrict hKV hDo (subset_univ _)
  have hdil : ∀ᵐ z ∂(volume.restrict {w : ℂ | 1 < ‖w‖}),
      complexDilatation V z = complexDilatation W z := by
    filter_upwards [ae_restrict_of_ae hV.2.2.2.2, ae_restrict_of_ae hW.2.2.2.2,
      ae_restrict_mem hDo.measurableSet] with z h1 h2 hz
    rw [h1, h2, extA_eq_on_exterior ρ hz]
    simp only [extB, indicator_of_mem (show z ∈ unitDiscExterior from hz)]
  have h1 := bg_conformal_of_dilatation_eq hKWD hKVD hdil
  have h2 := bg_conformal_of_dilatation_eq hKVD hKWD (hdil.mono fun z hz => hz.symm)
  rw [normalized_solution_exterior_image hW] at h1 h2
  exact ⟨h1, h2⟩

theorem wAS_c_diffOn {μ ν : LinfStar} (hμ : μ ∈ LinfStarBall) (hν : ν ∈ LinfStarBall)
    (hBeq : ∀ p ∈ toExt (closedBall (0 : ℂ) 1), wB μ p = wB ν p) :
    DifferentiableOn ℂ (fun w : ℂ => finPart (mobiusExt 0 1 1 0 (wAS ν (Function.invFun (wB ν)
      (wB μ (Function.invFun (wAS μ) (mobiusExt 0 1 1 0 (w : ExtPlane)))))))) unitDisc := by
  obtain ⟨c, hc⟩ : ∃ c : ℂ → ℂ, c = fun w : ℂ => finPart (mobiusExt 0 1 1 0 (wAS ν
      (Function.invFun (wB ν) (wB μ (Function.invFun (wAS μ) (mobiusExt 0 1 1 0 (w : ExtPlane))))))) :=
    ⟨_, rfl⟩
  suffices hmain : DifferentiableOn ℂ c unitDisc by
    rw [hc] at hmain
    exact hmain
  obtain ⟨hHid, hHnot⟩ := wB_glue_props (μ := μ) hν hBeq
  obtain ⟨Mμ, hMμ, Wμ, hWμ, hwfμ, hwiμ, -, -, -⟩ := wA_spec hμ
  obtain ⟨Mν, hMν, Wν, hWν, hwfν, hwiν, -, -, -⟩ := wA_spec hν
  obtain ⟨Nμ, hNμ, Vμ, hVμ, hvfμ, hviμ, -⟩ := (wB_spec hμ).1
  obtain ⟨Nν, hNν, Vν, hVν, hvfν, hviν, -⟩ := (wB_spec hν).1
  obtain ⟨Mμinv, hMμinv, hMμl, -⟩ := isMobius_inverse hMμ
  obtain ⟨Nνinv, hNνinv, hNνl, -⟩ := isMobius_inverse hNν
  have hσ : IsMobius (mobiusExt 0 1 1 0) := ⟨0, 1, 1, 0, by norm_num, rfl⟩
  have hσi : Function.Injective (mobiusExt 0 1 1 0) := fun a b h => by
    rw [← sigma_invol a, ← sigma_invol b, h]
  have hP : IsMobius (fun p => Mμinv (mobiusExt 0 1 1 0 p)) := isMobius_comp hσ hMμinv
  have hN' : IsMobius (fun p => Nνinv (Nμ p)) := isMobius_comp hNμ hNνinv
  have hQ : IsMobius (fun p => mobiusExt 0 1 1 0 (Mν p)) := isMobius_comp hMν hσ
  have hDo : IsOpen {u : ℂ | 1 < ‖u‖} := isOpen_lt continuous_const continuous_norm
  obtain ⟨ψ, hψdef⟩ : ∃ ψ : ℂ → ℂ, ψ = Vμ ∘ Function.invFunOn Wμ {w : ℂ | 1 < ‖w‖} := ⟨_, rfl⟩
  obtain ⟨χ, hχdef⟩ : ∃ χ : ℂ → ℂ, χ = Wν ∘ Function.invFunOn Vν {w : ℂ | 1 < ‖w‖} := ⟨_, rfl⟩
  have hψ := (transition_conformal hWμ hVμ).1
  have hχ := (transition_conformal hWν hVν).2
  rw [← hψdef] at hψ
  rw [← hχdef] at hχ
  obtain ⟨cP, hcP⟩ : ∃ cP : ℂ → ℂ,
      cP = fun u : ℂ => finPart (Mμinv (mobiusExt 0 1 1 0 (u : ExtPlane))) := ⟨_, rfl⟩
  obtain ⟨cN, hcN⟩ : ∃ cN : ℂ → ℂ, cN = fun u : ℂ => finPart (Nνinv (Nμ (u : ExtPlane))) := ⟨_, rfl⟩
  obtain ⟨cQ, hcQ⟩ : ∃ cQ : ℂ → ℂ,
      cQ = fun u : ℂ => finPart (mobiusExt 0 1 1 0 (Mν (u : ExtPlane))) := ⟨_, rfl⟩
  have hPc : IsConformalOnto cP {u : ℂ | Mμinv (mobiusExt 0 1 1 0 (u : ExtPlane)) ≠ extInf}
      (cP '' {u : ℂ | Mμinv (mobiusExt 0 1 1 0 (u : ExtPlane)) ≠ extInf}) := by
    rw [hcP]
    exact mobius_finite_conformal hP
  have hNc : IsConformalOnto cN {u : ℂ | Nνinv (Nμ (u : ExtPlane)) ≠ extInf}
      (cN '' {u : ℂ | Nνinv (Nμ (u : ExtPlane)) ≠ extInf}) := by
    rw [hcN]
    exact mobius_finite_conformal hN'
  have hQc : IsConformalOnto cQ {u : ℂ | mobiusExt 0 1 1 0 (Mν (u : ExtPlane)) ≠ extInf}
      (cQ '' {u : ℂ | mobiusExt 0 1 1 0 (Mν (u : ExtPlane)) ≠ extInf}) := by
    rw [hcQ]
    exact mobius_finite_conformal hQ
  have hinvA : ∀ q, wAS μ (Function.invFun (wAS μ) q) = q := fun q =>
    Function.invFun_eq ((wAS_bijective μ).2 q)
  have hinvB : ∀ q, wB ν (Function.invFun (wB ν) q) = q := fun q =>
    Function.invFun_eq ((wB_bijective ν).2 q)
  have hinjV : InjOn Vν {w : ℂ | 1 < ‖w‖} := by
    obtain ⟨K, hK⟩ := hVν.1
    exact hK.2.2.1.2.1.mono (subset_univ _)
  have hinjW : InjOn Wμ {w : ℂ | 1 < ‖w‖} := (normalized_solution_injective hWμ).injOn
  -- the first step
  have hA1 : ∀ w ∈ unitDisc, Mμinv (mobiusExt 0 1 1 0 (w : ExtPlane)) ≠ extInf →
      ∃ u₁ : ℂ, Function.invFun (wAS μ) (mobiusExt 0 1 1 0 (w : ExtPlane)) = (u₁ : ExtPlane) ∧
        Wμ u₁ = cP w ∧ 1 < ‖u₁‖ := by
    intro w hw hne
    have hpn := sigma_not_closed hw
    have hq1n : Function.invFun (wAS μ) (mobiusExt 0 1 1 0 (w : ExtPlane)) ∉
        toExt (closedBall (0 : ℂ) 1) := by
      intro h
      rw [wAS_closed_iff hμ, hinvA] at h
      exact hpn h
    exact finite_preimage_data hwfμ hwiμ hMμl (hinvA _) hq1n
      (by rw [hcP]; exact (coe_finPart_of_ne hne).symm)
  have hDmem : ∀ w ∈ unitDisc, Mμinv (mobiusExt 0 1 1 0 (w : ExtPlane)) ≠ extInf →
      cP w ∈ {u : ℂ | 1 < ‖u‖} := by
    intro w hw hne
    obtain ⟨u₁, -, h2, h3⟩ := hA1 w hw hne
    rw [← h2]
    exact normalized_solution_exterior hWμ h3
  -- the second step
  have hA2 : ∀ w ∈ unitDisc, ∀ (hne : Mμinv (mobiusExt 0 1 1 0 (w : ExtPlane)) ≠ extInf),
      Nνinv (Nμ ((ψ (cP w) : ℂ) : ExtPlane)) ≠ extInf →
      ∃ u₂ : ℂ, Function.invFun (wB ν) (wB μ (Function.invFun (wAS μ)
        (mobiusExt 0 1 1 0 (w : ExtPlane)))) = (u₂ : ExtPlane) ∧
        Vν u₂ = cN (ψ (cP w)) ∧ 1 < ‖u₂‖ := by
    intro w hw hne hne2
    obtain ⟨u₁, hq1, hWu, hu1⟩ := hA1 w hw hne
    have hq1n : Function.invFun (wAS μ) (mobiusExt 0 1 1 0 (w : ExtPlane)) ∉
        toExt (closedBall (0 : ℂ) 1) := by
      rw [hq1, coe_mem_toExt_iff, mem_closedBall_zero_iff, not_le]
      exact hu1
    have hψeq : ψ (cP w) = Vμ u₁ := by
      rw [hψdef, Function.comp_apply, ← hWu, hinjW.leftInvOn_invFunOn hu1]
    have hwB : wB μ (Function.invFun (wAS μ) (mobiusExt 0 1 1 0 (w : ExtPlane))) =
        Nμ ((ψ (cP w) : ℂ) : ExtPlane) := by
      rw [hq1, hvfμ u₁, hψeq]
    have hq2n := hHnot _ hq1n
    exact finite_preimage_data hvfν hviν hNνl (hinvB _) hq2n
      (by rw [hwB, hcN]; exact (coe_finPart_of_ne hne2).symm)
  -- the value of `c`
  have hcw : ∀ w ∈ unitDisc, ∀ (hne : Mμinv (mobiusExt 0 1 1 0 (w : ExtPlane)) ≠ extInf)
      (hne2 : Nνinv (Nμ ((ψ (cP w) : ℂ) : ExtPlane)) ≠ extInf),
      c w = cQ (χ (cN (ψ (cP w)))) ∧ cN (ψ (cP w)) ∈ Vν '' {u : ℂ | 1 < ‖u‖} ∧
        mobiusExt 0 1 1 0 (Mν ((χ (cN (ψ (cP w))) : ℂ) : ExtPlane)) ≠ extInf := by
    intro w hw hne hne2
    obtain ⟨u₂, hq2, hVu, hu2⟩ := hA2 w hw hne hne2
    have hχeq : χ (cN (ψ (cP w))) = Wν u₂ := by
      rw [hχdef, Function.comp_apply, ← hVu, hinjV.leftInvOn_invFunOn hu2]
    have hq2n : Function.invFun (wB ν) (wB μ (Function.invFun (wAS μ)
        (mobiusExt 0 1 1 0 (w : ExtPlane)))) ∉ toExt (closedBall (0 : ℂ) 1) := by
      rw [hq2, coe_mem_toExt_iff, mem_closedBall_zero_iff, not_le]
      exact hu2
    have hAn : wAS ν (Function.invFun (wB ν) (wB μ (Function.invFun (wAS μ)
        (mobiusExt 0 1 1 0 (w : ExtPlane))))) ∉ toExt (closedBall (0 : ℂ) 1) := by
      rw [← wAS_closed_iff hν]
      exact hq2n
    have hMq : Mν ((Wν u₂ : ℂ) : ExtPlane) = wAS ν (u₂ : ExtPlane) := (hwfν u₂).symm
    refine ⟨?_, ⟨u₂, hu2, hVu⟩, ?_⟩
    · rw [hc]
      show finPart (mobiusExt 0 1 1 0 (wAS ν (Function.invFun (wB ν) (wB μ
        (Function.invFun (wAS μ) (mobiusExt 0 1 1 0 (w : ExtPlane))))))) = _
      rw [hq2, hχeq, hcQ]
      show _ = finPart (mobiusExt 0 1 1 0 (Mν ((Wν u₂ : ℂ) : ExtPlane)))
      rw [hMq]
    · rw [hχeq, hMq]
      rw [hq2] at hAn
      obtain ⟨y, hy, -⟩ := sigma_of_not_closed hAn
      rw [hy]
      exact OnePoint.coe_ne_infty y
  -- the exceptional set
  obtain ⟨Ω, hΩ⟩ : ∃ Ω : Set ℂ, Ω = {w | w ∈ unitDisc ∧
      Mμinv (mobiusExt 0 1 1 0 (w : ExtPlane)) ≠ extInf ∧
      Nνinv (Nμ ((ψ (cP w) : ℂ) : ExtPlane)) ≠ extInf} := ⟨_, rfl⟩
  have hdiffΩ : DifferentiableOn ℂ c Ω := by
    have hPd : DifferentiableOn ℂ cP Ω := hPc.1.mono (fun w hw => by rw [hΩ] at hw; exact hw.2.1)
    have h1 : DifferentiableOn ℂ (ψ ∘ cP) Ω :=
      hψ.1.comp hPd (fun w hw => by rw [hΩ] at hw; exact hDmem w hw.1 hw.2.1)
    have h2 : DifferentiableOn ℂ (cN ∘ ψ ∘ cP) Ω :=
      hNc.1.comp h1 (fun w hw => by rw [hΩ] at hw; exact hw.2.2)
    have h3 : DifferentiableOn ℂ (χ ∘ cN ∘ ψ ∘ cP) Ω :=
      hχ.1.comp h2 (fun w hw => by
        rw [hΩ] at hw
        exact (hcw w hw.1 hw.2.1 hw.2.2).2.1)
    have h4 : DifferentiableOn ℂ (cQ ∘ χ ∘ cN ∘ ψ ∘ cP) Ω :=
      hQc.1.comp h3 (fun w hw => by
        rw [hΩ] at hw
        exact (hcw w hw.1 hw.2.1 hw.2.2).2.2)
    refine h4.congr (fun w hw => ?_)
    rw [hΩ] at hw
    exact (hcw w hw.1 hw.2.1 hw.2.2).1
  have hE1 : {w : ℂ | w ∈ unitDisc ∧ Mμinv (mobiusExt 0 1 1 0 (w : ExtPlane)) = extInf}.Subsingleton := by
    intro w1 h1 w2 h2
    have := isMobius_injective hMμinv (h1.2.trans h2.2.symm)
    exact OnePoint.coe_injective (hσi this)
  have hE2 : {w : ℂ | w ∈ unitDisc ∧ Mμinv (mobiusExt 0 1 1 0 (w : ExtPlane)) ≠ extInf ∧
      Nνinv (Nμ ((ψ (cP w) : ℂ) : ExtPlane)) = extInf}.Subsingleton := by
    intro w1 h1 w2 h2
    have h3 : (fun p => Nνinv (Nμ p)) ((ψ (cP w1) : ℂ) : ExtPlane) =
        (fun p => Nνinv (Nμ p)) ((ψ (cP w2) : ℂ) : ExtPlane) := h1.2.2.trans h2.2.2.symm
    have h4 := OnePoint.coe_injective (isMobius_injective hN' h3)
    have h5 := hψ.2.1 (hDmem w1 h1.1 h1.2.1) (hDmem w2 h2.1 h2.2.1) h4
    exact hPc.2.1 h1.2.1 h2.2.1 h5
  have hEfin : (unitDisc \ Ω).Finite := by
    refine (hE1.finite.union hE2.finite).subset ?_
    intro w hw
    by_cases ha : Mμinv (mobiusExt 0 1 1 0 (w : ExtPlane)) = extInf
    · exact Or.inl ⟨hw.1, ha⟩
    · refine Or.inr ⟨hw.1, ha, ?_⟩
      by_contra hb
      apply hw.2
      rw [hΩ]
      exact ⟨hw.1, ha, hb⟩
  have hcont : ContinuousOn c unitDisc := by
    have hσc : Continuous (mobiusExt 0 1 1 0) := continuous_mobiusExt (by norm_num)
    have hcoe : ∀ w ∈ unitDisc, ((c w : ℂ) : ExtPlane) = mobiusExt 0 1 1 0 (wAS ν
        (Function.invFun (wB ν) (wB μ (Function.invFun (wAS μ)
          (mobiusExt 0 1 1 0 (w : ExtPlane)))))) := by
      intro w hw
      have hn : wAS ν (Function.invFun (wB ν) (wB μ (Function.invFun (wAS μ)
          (mobiusExt 0 1 1 0 (w : ExtPlane))))) ∉ toExt (closedBall (0 : ℂ) 1) := by
        rw [← wAS_closed_iff hν]
        refine hHnot _ ?_
        rw [wAS_closed_iff hμ, hinvA]
        exact sigma_not_closed hw
      obtain ⟨y, hy, -⟩ := sigma_of_not_closed hn
      rw [hc]
      show ((finPart (mobiusExt 0 1 1 0 (wAS ν (Function.invFun (wB ν) (wB μ
        (Function.invFun (wAS μ) (mobiusExt 0 1 1 0 (w : ExtPlane))))))) : ℂ) : ExtPlane) = _
      rw [hy]
      rfl
    have hct : Continuous (fun p : ExtPlane => mobiusExt 0 1 1 0 (wAS ν (Function.invFun (wB ν)
        (wB μ (Function.invFun (wAS μ) (mobiusExt 0 1 1 0 p)))))) :=
      hσc.comp ((wAS_continuous hν).comp ((wB_invFun_continuous hν).comp
        ((wB_continuous hμ).comp ((wAS_invFun_continuous hμ).comp hσc))))
    rw [OnePoint.isOpenEmbedding_coe.isEmbedding.isInducing.continuousOn_iff]
    refine (hct.comp OnePoint.continuous_coe).continuousOn.congr ?_
    intro w hw
    exact hcoe w hw
  refine differentiableOn_of_finite_exceptional (show IsOpen unitDisc from isOpen_ball) hEfin hcont ?_
  refine hdiffΩ.mono ?_
  intro w hw
  by_contra h
  exact hw.2 ⟨hw.1, h⟩

theorem wAS_eq_of_wB_eq {μ ν : LinfStar} (hμ : μ ∈ LinfStarBall) (hν : ν ∈ LinfStarBall)
    (hBeq : ∀ p ∈ toExt (closedBall (0 : ℂ) 1), wB μ p = wB ν p) :
    ∀ z : ℂ, ‖z‖ = 1 → wAS μ (z : ExtPlane) = wAS ν (z : ExtPlane) := by
  obtain ⟨hHid, hHnot⟩ := wB_glue_props (μ := μ) hν hBeq
  have hdiff := wAS_c_diffOn hμ hν hBeq
  obtain ⟨Mμ, hMμ, Wμ, hWμ, hwfμ, hwiμ, hm1, hmI, hm2⟩ := wA_spec hμ
  obtain ⟨Csph, hCsph⟩ : ∃ Csph : ExtPlane → ExtPlane, Csph = fun p => wAS ν
      (Function.invFun (wB ν) (wB μ (Function.invFun (wAS μ) p))) := ⟨_, rfl⟩
  have hinvA : ∀ q, wAS μ (Function.invFun (wAS μ) q) = q := fun q =>
    Function.invFun_eq ((wAS_bijective μ).2 q)
  have hinvAl : ∀ q, Function.invFun (wAS μ) (wAS μ q) = q := fun q =>
    Function.leftInverse_invFun (wAS_bijective μ).1 q
  have hinvB : ∀ q, wB ν (Function.invFun (wB ν) q) = q := fun q =>
    Function.invFun_eq ((wB_bijective ν).2 q)
  have hCnot : ∀ p ∉ toExt (closedBall (0 : ℂ) 1), Csph p ∉ toExt (closedBall (0 : ℂ) 1) := by
    intro p hp
    rw [hCsph]
    show wAS ν _ ∉ _
    rw [← wAS_closed_iff hν]
    refine hHnot _ ?_
    rw [wAS_closed_iff hμ, hinvA]
    exact hp
  have hCinj : Function.Injective Csph := by
    intro p q hpq
    rw [hCsph] at hpq
    have h1 := (wAS_bijective ν).1 hpq
    have h2 : wB μ (Function.invFun (wAS μ) p) = wB μ (Function.invFun (wAS μ) q) := by
      have := congrArg (wB ν) h1
      simp only [hinvB] at this
      exact this
    have h3 := (wB_bijective μ).1 h2
    have := congrArg (wAS μ) h3
    simpa only [hinvA] using this
  have hCsurj : ∀ p' ∉ toExt (closedBall (0 : ℂ) 1), ∃ p ∉ toExt (closedBall (0 : ℂ) 1),
      Csph p = p' := by
    intro p' hp'
    obtain ⟨q2, hq2⟩ := (wAS_bijective ν).2 p'
    have hq2n : q2 ∉ toExt (closedBall (0 : ℂ) 1) := by
      rw [wAS_closed_iff hν, hq2]
      exact hp'
    obtain ⟨q1, hq1⟩ := (wB_bijective μ).2 (wB ν q2)
    have hq1n : q1 ∉ toExt (closedBall (0 : ℂ) 1) := by
      intro h
      have e := hBeq q1 h
      rw [hq1] at e
      exact hq2n (((wB_bijective ν).1 e) ▸ h)
    refine ⟨wAS μ q1, ?_, ?_⟩
    · rw [← wAS_closed_iff hμ]
      exact hq1n
    · rw [hCsph]
      show wAS ν (Function.invFun (wB ν) (wB μ (Function.invFun (wAS μ) (wAS μ q1)))) = p'
      rw [hinvAl, hq1, Function.leftInverse_invFun (wB_bijective ν).1 q2, hq2]
  have hCcont : Continuous Csph := by
    rw [hCsph]
    exact (wAS_continuous hν).comp ((wB_invFun_continuous hν).comp
      ((wB_continuous hμ).comp (wAS_invFun_continuous hμ)))
  have hCcl : ∀ ξ ∈ toExt (closedBall (0 : ℂ) 1), Csph (wAS μ ξ) = wAS ν ξ := by
    intro ξ hξ
    rw [hCsph]
    show wAS ν (Function.invFun (wB ν) (wB μ (Function.invFun (wAS μ) (wAS μ ξ)))) = _
    rw [hinvAl, hHid ξ hξ]
  obtain ⟨Mν, hMν, Wν, hWν, hwfν, hwiν, hn1, hnI, hn2⟩ := wA_spec hν
  have hσc : Continuous (mobiusExt 0 1 1 0) := continuous_mobiusExt (by norm_num)
  have hσi : Function.Injective (mobiusExt 0 1 1 0) := fun a b h => by
    rw [← sigma_invol a, ← sigma_invol b, h]
  obtain ⟨c, hcdef⟩ : ∃ c : ℂ → ℂ, c = fun w : ℂ =>
      finPart (mobiusExt 0 1 1 0 (Csph (mobiusExt 0 1 1 0 (w : ExtPlane)))) := ⟨_, rfl⟩
  have hdiff' : DifferentiableOn ℂ c unitDisc := by
    rw [hcdef, hCsph]
    exact hdiff
  have hc1 : ∀ w ∈ unitDisc, mobiusExt 0 1 1 0 (Csph (mobiusExt 0 1 1 0 (w : ExtPlane))) =
      ((c w : ℂ) : ExtPlane) ∧ c w ∈ unitDisc := by
    intro w hw
    obtain ⟨y, hy, hyD⟩ := sigma_of_not_closed (hCnot _ (sigma_not_closed hw))
    have hcy : c w = y := by
      rw [hcdef]
      show finPart (mobiusExt 0 1 1 0 (Csph _)) = y
      rw [hy]
      rfl
    exact ⟨by rw [hcy]; exact hy, hcy ▸ hyD⟩
  have hcinj : InjOn c unitDisc := by
    intro w1 hw1 w2 hw2 h
    have e1 := (hc1 w1 hw1).1
    have e2 := (hc1 w2 hw2).1
    rw [h] at e1
    have := hCinj (hσi (e1.trans e2.symm))
    exact OnePoint.coe_injective (hσi this)
  have hcsurj : c '' unitDisc = unitDisc := by
    apply Subset.antisymm
    · rintro _ ⟨w, hw, rfl⟩
      exact (hc1 w hw).2
    · intro y hy
      obtain ⟨p, hpn, hp⟩ := hCsurj _ (sigma_not_closed hy)
      obtain ⟨w, hwp, hwD⟩ := sigma_of_not_closed hpn
      refine ⟨w, hwD, ?_⟩
      have e := (hc1 w hwD).1
      rw [← hwp, sigma_invol, hp, sigma_invol] at e
      exact (OnePoint.coe_injective e).symm
  obtain ⟨A, B, C, D, hdet, heq⟩ :=
    exists_mobius_of_isConformalOnto_unitDisc ⟨hdiff', hcinj, hcsurj⟩
  have hmc : Continuous (mobiusExt A B C D) := continuous_mobiusExt hdet
  have hZ : {x : ℂ | C * x + D = 0}.Subsingleton := by
    intro x hx y hy
    have hx' : C * x + D = 0 := hx
    have hy' : C * y + D = 0 := hy
    by_cases hC : C = 0
    · exfalso
      rw [hC, zero_mul, zero_add] at hx'
      apply hdet
      rw [hC, hx']
      ring
    · have : C * (x - y) = 0 := by linear_combination hx' - hy'
      exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_left hC)
  have hZd : Dense ({x : ℂ | C * x + D = 0}ᶜ) := Set.Countable.dense_compl ℂ hZ.finite.countable
  have hagree : EqOn (fun p => mobiusExt 0 1 1 0 (Csph (mobiusExt 0 1 1 0 p))) (mobiusExt A B C D)
      (((↑) : ℂ → ExtPlane) '' (ball (0 : ℂ) 1 ∩ {x : ℂ | C * x + D = 0}ᶜ)) := by
    rintro _ ⟨w, ⟨hw, hwZ⟩, rfl⟩
    have hwD : w ∈ unitDisc := hw
    show mobiusExt 0 1 1 0 (Csph (mobiusExt 0 1 1 0 (w : ExtPlane))) = _
    rw [(hc1 w hwD).1, mobiusExt_coe hwZ, heq hwD]
  have hcl : EqOn (fun p => mobiusExt 0 1 1 0 (Csph (mobiusExt 0 1 1 0 p))) (mobiusExt A B C D)
      (closure (((↑) : ℂ → ExtPlane) '' (ball (0 : ℂ) 1 ∩ {x : ℂ | C * x + D = 0}ᶜ))) :=
    EqOn.closure hagree (hσc.comp (hCcont.comp hσc)) hmc
  have hcirc : ∀ ζ : ℂ, ‖ζ‖ = 1 → mobiusExt 0 1 1 0 (Csph (mobiusExt 0 1 1 0 (ζ : ExtPlane))) =
      mobiusExt A B C D (ζ : ExtPlane) := by
    intro ζ hζ
    apply hcl
    have h1 : ζ ∈ closure (ball (0 : ℂ) 1 ∩ {x : ℂ | C * x + D = 0}ᶜ) := by
      have hsub : ball (0 : ℂ) 1 ⊆ closure (ball (0 : ℂ) 1 ∩ {x : ℂ | C * x + D = 0}ᶜ) :=
        hZd.open_subset_closure_inter isOpen_ball
      have : closure (ball (0 : ℂ) 1) ⊆ closure (ball (0 : ℂ) 1 ∩ {x : ℂ | C * x + D = 0}ᶜ) :=
        closure_minimal hsub isClosed_closure
      apply this
      rw [closure_ball _ one_ne_zero]
      exact mem_closedBall_zero_iff.2 hζ.le
    exact (image_closure_subset_closure_image OnePoint.continuous_coe) ⟨ζ, h1, rfl⟩
  -- the three fixed points
  have hid : ∀ p, mobiusExt 1 0 0 1 p = p := by
    intro p
    induction p using OnePoint.rec with
    | infty => exact mobiusExt_infty_of_eq rfl
    | coe z =>
      rw [mobiusExt_coe (by simp)]
      congr 1
      simp [mobiusFn]
  have hfix1 : Csph ((-1 : ℂ) : ExtPlane) = ((-1 : ℂ) : ExtPlane) := by
    have := hCcl ((-1 : ℂ) : ExtPlane) (by
      rw [coe_mem_toExt_iff, mem_closedBall_zero_iff]; simp)
    rw [hm1, hn1] at this
    exact this
  have hfixI : Csph ((-I : ℂ) : ExtPlane) = ((-I : ℂ) : ExtPlane) := by
    have := hCcl ((-I : ℂ) : ExtPlane) (by
      rw [coe_mem_toExt_iff, mem_closedBall_zero_iff]; simp)
    rw [hmI, hnI] at this
    exact this
  have hfix2 : Csph ((1 : ℂ) : ExtPlane) = ((1 : ℂ) : ExtPlane) := by
    have := hCcl ((1 : ℂ) : ExtPlane) (by
      rw [coe_mem_toExt_iff, mem_closedBall_zero_iff]; simp)
    rw [hm2, hn2] at this
    exact this
  have hI0 : (-I : ℂ) ≠ 0 := neg_ne_zero.2 Complex.I_ne_zero
  have hMid : mobiusExt A B C D = mobiusExt 1 0 0 1 := by
    refine mobius_eq_of_three_points (p₁ := -1) (p₂ := I) (p₃ := 1) ⟨A, B, C, D, hdet, rfl⟩
      ⟨1, 0, 0, 1, by norm_num, rfl⟩ ?_ ?_ ?_ ?_ ?_ ?_
    · intro h
      have := congrArg Complex.re h
      norm_num at this
    · norm_num
    · intro h
      have := congrArg Complex.re h
      norm_num at this
    · rw [← hcirc (-1) (by simp), sigma_coe (by norm_num), hid]
      have : ((-1 : ℂ)⁻¹) = -1 := by norm_num
      rw [this, hfix1, sigma_coe (by norm_num), this]
    · rw [← hcirc I (by simp), sigma_coe Complex.I_ne_zero, hid]
      have : (I : ℂ)⁻¹ = -I := by simp
      rw [this, hfixI, sigma_coe hI0]
      simp
    · rw [← hcirc 1 (by simp), sigma_coe one_ne_zero, hid]
      rw [inv_one, hfix2, sigma_coe one_ne_zero, inv_one]
  have hCid : ∀ ζ : ℂ, ‖ζ‖ = 1 → Csph (ζ : ExtPlane) = (ζ : ExtPlane) := by
    intro ζ hζ
    have hζ0 : ζ ≠ 0 := norm_ne_zero_iff.1 (by rw [hζ]; exact one_ne_zero)
    have h1 := hcirc ζ⁻¹ (by rw [norm_inv, hζ]; simp)
    rw [hMid, hid, sigma_coe (inv_ne_zero hζ0), inv_inv] at h1
    have h2 := congrArg (mobiusExt 0 1 1 0) h1
    rw [sigma_invol, sigma_coe (inv_ne_zero hζ0), inv_inv] at h2
    exact h2
  intro z hz
  obtain ⟨u, hu, hu'⟩ := wAS_maps_circle hμ hz
  have hzCl : (z : ExtPlane) ∈ toExt (closedBall (0 : ℂ) 1) := by
    rw [coe_mem_toExt_iff, mem_closedBall_zero_iff]
    exact hz.le
  have h3 := hCcl _ hzCl
  rw [hu', hCid u hu] at h3
  rw [hu', h3]

theorem modelB_to_modelA (μ ν : LinfStarBall)
    (h : ∀ z ∈ unitDisc, fB μ z = fB ν z) :
    ∀ z ∈ unitCircle, wA μ z = wA ν z := by
  intro z hz
  exact congrArg finPart (wAS_eq_of_wB_eq μ.property ν.property
    (wB_eq_closed μ.property ν.property h) z hz)


/-- (TT:361) The two models agree: `w_μ|S¹ = w_ν|S¹` iff `w^μ|𝔻 = w^ν|𝔻`. -/
theorem modelA_iff_modelB (μ ν : LinfStarBall) :
    (∀ z ∈ unitCircle, wA μ z = wA ν z) ↔ ∀ z ∈ unitDisc, fB μ z = fB ν z := by
  exact ⟨modelA_to_modelB μ ν, modelB_to_modelA μ ν⟩

/-- The real-analytic Beltrami differentials `𝓛∞(𝔻*)` (TT:363): elements of `L∞(𝔻*)` with a representative that is
real-analytic on `𝔻* ∪ {∞}`, i.e. on `𝔻*` and, as a `(−1,1)`-form, at `∞`: its pullback by `ι(z) = 1/z`,
`g(1/z) z²/z̄²`, extends real-analytically across `0`.
- **[CORRECTION 2026-10-28, user-approved]** Analyticity at `∞` added: with analyticity on the finite points only, the
group law (which moves `∞` to `w_μ(∞) ∈ 𝔻*`) leaves the set (`realAnalyticBeltrami_subgroup` was false). -/
def realAnalyticBeltrami : Set LinfStar :=
  {μ | ∃ g : ℂ → ℂ, AnalyticOnNhd ℝ g unitDiscExterior ∧ μ =ᵐ[volume.restrict unitDiscExterior] g ∧
    ∃ h : ℂ → ℂ, AnalyticAt ℝ h 0 ∧ ∀ z : ℂ, z ≠ 0 → ‖z‖ < 1 → h z = g z⁻¹ * (z ^ 2 / conj z ^ 2)}

-- `exists_realAnalytic_rep` moved to `TakhtajanTeo.Ch1.BeltramiRealAnalytic` (2026-10-29, Program G).

/-! ## §1.1.3 The Bers embedding -/

/-- Disk quadratic differentials are determined by their values on the disk
(TT:477): the weight used in A-infinity never vanishes there. -/
theorem AInf.ext_toFun_disc {φ ψ : AInf unitDisc}
    (h : EqOn (AInf.toFun φ) (AInf.toFun ψ) unitDisc) : φ = ψ := by
  apply Subtype.ext
  apply BoundedContinuousFunction.ext
  intro z
  have hz : ‖(z : ℂ)‖ < 1 := mem_ball_zero_iff.mp z.2
  have hd : (1 - (‖(z : ℂ)‖ : ℂ) ^ 2) ^ 2 ≠ 0 := by
    apply pow_ne_zero
    intro he
    have heR : 1 - ‖(z : ℂ)‖ ^ 2 = 0 := by exact_mod_cast he
    have hn := norm_nonneg (z : ℂ)
    nlinarith
  have he := h z.2
  simp only [AInf.toFun, unweight, dif_pos z.2] at he
  exact (div_left_inj' hd).mp he

/-- Conversion to A-infinity depends only on disk values (TT:477), including
its fallback branch when no representative exists. -/
theorem toAInf_congr_disc {f g : ℂ → ℂ} (h : EqOn f g unitDisc) :
    toAInf unitDisc f = toAInf unitDisc g := by
  by_cases hf : ∃ φ : AInf unitDisc, ∀ z ∈ unitDisc, AInf.toFun φ z = f z
  · have hg : ∃ φ : AInf unitDisc, ∀ z ∈ unitDisc, AInf.toFun φ z = g z :=
      ⟨hf.choose, fun z hz => (hf.choose_spec z hz).trans (h hz)⟩
    unfold toAInf
    rw [dif_pos hf, dif_pos hg]
    apply AInf.ext_toFun_disc
    intro z hz
    exact (hf.choose_spec z hz).trans ((h hz).trans (hg.choose_spec z hz).symm)
  · have hg : ¬ ∃ φ : AInf unitDisc, ∀ z ∈ unitDisc, AInf.toFun φ z = g z := by
      rintro ⟨φ, hφ⟩
      exact hf ⟨φ, fun z hz => (hφ z hz).trans (h hz).symm⟩
    simp only [toAInf, dif_neg hf, dif_neg hg]

/-- `β ∘ Φ` on `L∞(𝔻*)` (TT:486–490): `μ ↦ 𝒮(w^μ|𝔻) ∈ A∞(𝔻)`, where `𝒮` is the Schwarzian derivative
`𝒮(f) = f_{zzz}/f_z - (3/2)(f_{zz}/f_z)²` (TT:483; `LiZhongQC.schwarzianHol` is the same expression). Meaningful for
`μ ∈ L∞(𝔻*)₁`. -/
def bersPhi (μ : LinfStar) : AInf unitDisc := toAInf unitDisc (schwarzianHol (fB μ))

/-- Equal Model B functions on the disk give equal Bers differentials
(TT:483–490), since all derivatives are local. -/
theorem bersPhi_congr_fB {μ ν : LinfStar} (h : EqOn (fB μ) (fB ν) unitDisc) :
    bersPhi μ = bersPhi ν := by
  apply toAInf_congr_disc
  intro z hz
  have he : fB μ =ᶠ[𝓝 z] fB ν := by
    filter_upwards [isOpen_ball.mem_nhds hz] with w hw
    exact h hw
  have hpre := (he.deriv.deriv.div he.deriv).deriv_eq
  simp only [schwarzianHol, he.deriv_eq, he.deriv.deriv_eq]
  exact congrArg (fun t : ℂ => t - (1 / 2 : ℂ) *
    (deriv (deriv (fB ν)) z / deriv (fB ν) z) ^ 2) hpre

/-- **The Bers embedding** `β : T(1) → A∞(𝔻)`, `β([μ]) = 𝒮(w^μ|𝔻)` (TT:489), computed on the representative
`Quotient.out`; `bers_Phi` shows that the representative does not matter. -/
def bers (p : T1) : AInf unitDisc := bersPhi (Quotient.out p : LinfStarBall)

/-- `β([μ]) = 𝒮(w^μ|𝔻)` for every representative `μ` (TT:489). -/
theorem bers_Phi (μ : LinfStarBall) : bers (Phi μ) = bersPhi μ := by
  have h : teichSetoid.r (Phi μ).out μ := Quotient.mk_out (s := teichSetoid) μ
  exact bersPhi_congr_fB (modelA_to_modelB _ _ h)

/-- A holomorphic function with the weighted sup bound has its intended
A-infinity representative (TT:363, TT:477). -/
theorem exists_AInf_disc_of_bound {F : ℂ → ℂ} {C : ℝ} (hC : 0 ≤ C)
    (hF : DifferentiableOn ℂ F unitDisc)
    (hb : ∀ z ∈ unitDisc, ‖F z‖ * (1 - ‖z‖ ^ 2) ^ 2 ≤ C) :
    ∃ φ : AInf unitDisc, (∀ z ∈ unitDisc, AInf.toFun φ z = F z) ∧ ‖φ‖ ≤ C := by
  have hb' : ∀ z ∈ unitDisc, ‖(1 - (‖z‖ : ℂ) ^ 2) ^ 2 * F z‖ ≤ C := by
    intro z hz
    simpa only [norm_mul, norm_pow, ← Complex.ofReal_pow, ← Complex.ofReal_one,
      ← Complex.ofReal_sub, norm_real, Real.norm_eq_abs, sq_abs, mul_comm] using hb z hz
  have hc : ContinuousOn (fun z : ℂ => (1 - (‖z‖ : ℂ) ^ 2) ^ 2 * F z) unitDisc := by
    have hw : Continuous (fun z : ℂ => (1 - (‖z‖ : ℂ) ^ 2) ^ 2) := by fun_prop
    exact hw.continuousOn.mul hF.continuousOn
  let Ψ : unitDisc →ᵇ ℂ :=
    { toFun := fun z => (1 - (‖(z : ℂ)‖ : ℂ) ^ 2) ^ 2 * F z
      continuous_toFun := continuousOn_iff_continuous_domRestrict.mp hc
      map_bounded' := ⟨2 * C, fun x y => by
        have hx := hb' x x.2
        have hy := hb' y y.2
        have hxy := norm_sub_le ((1 - (‖(x : ℂ)‖ : ℂ) ^ 2) ^ 2 * F x)
          ((1 - (‖(y : ℂ)‖ : ℂ) ^ 2) ^ 2 * F y)
        rw [← dist_eq_norm] at hxy
        linarith⟩ }
  have he : EqOn (unweight unitDisc Ψ) F unitDisc := by
    intro z hz
    have hn : ‖z‖ < 1 := mem_ball_zero_iff.mp hz
    have hd : (1 - (‖z‖ : ℂ) ^ 2) ^ 2 ≠ 0 := by
      apply pow_ne_zero
      intro he
      have hr : 1 - ‖z‖ ^ 2 = 0 := by exact_mod_cast he
      nlinarith [norm_nonneg z]
    rw [unweight, dif_pos hz]
    exact mul_div_cancel_left₀ _ hd
  refine ⟨⟨Ψ, hF.congr he⟩, (fun z hz => he hz), ?_⟩
  change ‖Ψ‖ ≤ C
  exact (BoundedContinuousFunction.norm_le hC).mpr (fun z => hb' z z.2)

/-- The conversion to disk A-infinity preserves a holomorphic function
and its weighted bound (TT:363, TT:477). -/
theorem toAInf_disc_spec_of_bound {F : ℂ → ℂ} {C : ℝ} (hC : 0 ≤ C)
    (hF : DifferentiableOn ℂ F unitDisc)
    (hb : ∀ z ∈ unitDisc, ‖F z‖ * (1 - ‖z‖ ^ 2) ^ 2 ≤ C) :
    (∀ z ∈ unitDisc, AInf.toFun (toAInf unitDisc F) z = F z) ∧
      ‖toAInf unitDisc F‖ ≤ C := by
  obtain ⟨φ, hφ, hφnorm⟩ := exists_AInf_disc_of_bound hC hF hb
  have hex : ∃ ψ : AInf unitDisc, ∀ z ∈ unitDisc, AInf.toFun ψ z = F z := ⟨φ, hφ⟩
  have he : toAInf unitDisc F = φ := by
    apply AInf.ext_toFun_disc
    intro z hz
    rw [toAInf, dif_pos hex]
    exact (hex.choose_spec z hz).trans (hφ z hz).symm
  rw [he]
  exact ⟨hφ, hφnorm⟩

/-- The Schwarzian of a univalent holomorphic disk function lies in
the A-infinity ball of radius six, by Kraus–Nehari (TT:486). -/
theorem schwarzianHol_AInf_spec {F : ℂ → ℂ}
    (hF : DifferentiableOn ℂ F unitDisc) (hinj : InjOn F unitDisc) :
    (∀ z ∈ unitDisc, AInf.toFun (toAInf unitDisc (schwarzianHol F)) z = schwarzianHol F z) ∧
      ‖toAInf unitDisc (schwarzianHol F)‖ ≤ 6 := by
  have han : ∀ z ∈ unitDisc, AnalyticAt ℂ F z := fun z hz =>
    hF.analyticAt (isOpen_ball.mem_nhds hz)
  apply toAInf_disc_spec_of_bound (by norm_num)
  · intro z hz
    exact (analyticAt_schwarzianHol (han z hz)
      (deriv_ne_zero_of_injOn isOpen_ball hF hinj hz)).differentiableAt.differentiableWithinAt
  · intro z hz
    have hb := knr_holomorphic_bound hF hinj hz
    rwa [schwarzian_of_analyticAt (han z hz)] at hb

/-- (TT:486) For `μ ∈ L∞(𝔻*)₁`, `𝒮(w^μ|𝔻)` lies in `A∞(𝔻)`, and by the Kraus–Nehari inequality in its ball of
radius `6`. -/
theorem bersPhi_spec {μ : LinfStar} (hμ : μ ∈ LinfStarBall) :
    (∀ z ∈ unitDisc, AInf.toFun (bersPhi μ) z = schwarzianHol (fB μ) z) ∧ ‖bersPhi μ‖ ≤ 6 := by
  obtain ⟨hd, hi⟩ := fB_holomorphic_injective hμ
  exact schwarzianHol_AInf_spec hd hi

/-- The three Model B jets remove the Mobius ambiguity in the Schwarzian
of univalent disk functions (TT:357, TT:489). -/
theorem normalized_disk_schwarzian_unique {F G : ℂ → ℂ}
    (hF : DifferentiableOn ℂ F unitDisc) (hG : DifferentiableOn ℂ G unitDisc)
    (hinj : InjOn G unitDisc)
    (hF0 : F 0 = 0) (hG0 : G 0 = 0)
    (hF1 : deriv F 0 = 1) (hG1 : deriv G 0 = 1)
    (hF2 : deriv (deriv F) 0 = 0) (hG2 : deriv (deriv G) 0 = 0)
    (hS : EqOn (schwarzianHol F) (schwarzianHol G) unitDisc) :
    EqOn F G unitDisc := by
  have hzero : (0 : ℂ) ∈ unitDisc := mem_ball_self (by norm_num)
  have hFan : AnalyticOnNhd ℂ F unitDisc := fun z hz => hF.analyticAt (isOpen_ball.mem_nhds hz)
  have hGan : AnalyticOnNhd ℂ G unitDisc := fun z hz => hG.analyticAt (isOpen_ball.mem_nhds hz)
  have hSe : schwarzianHol F =ᶠ[𝓝 (0 : ℂ)] schwarzianHol G := by
    filter_upwards [isOpen_ball.mem_nhds hzero] with z hz
    exact hS hz
  obtain ⟨a, b, c, d, hdet, he⟩ := exists_mobius_of_schwarzianHol_eventuallyEq
    (hFan 0 hzero) (by simp [hF1]) (hGan 0 hzero) (by simp [hG1]) hSe
  have hd : d ≠ 0 := by
    intro hd0
    have hc : c ≠ 0 := by
      intro hc0
      apply hdet
      simp [hd0, hc0]
    have he' : (fun z => F z * (c * G z + d)) =ᶠ[𝓝[≠] (0 : ℂ)]
        (fun z => a * G z + b) := by
      filter_upwards [he.filter_mono nhdsWithin_le_nhds,
        mem_nhdsWithin_of_mem_nhds (isOpen_ball.mem_nhds hzero), self_mem_nhdsWithin]
        with z hz hzD hz0
      have hGz : G z ≠ 0 := by
        intro h
        exact hz0 (hinj hzD hzero (h.trans hG0.symm))
      exact (eq_div_iff (by simpa only [hd0, add_zero] using mul_ne_zero hc hGz)).mp hz
    have hFc : ContinuousAt F 0 := (hFan 0 hzero).continuousAt
    have hGc : ContinuousAt G 0 := (hGan 0 hzero).continuousAt
    have hL : ContinuousAt (fun z => F z * (c * G z + d)) 0 := by fun_prop
    have hR : ContinuousAt (fun z => a * G z + b) 0 := by fun_prop
    have hlim := tendsto_nhds_unique
      (hL.tendsto.mono_left (nhdsWithin_le_nhds : 𝓝[≠] (0 : ℂ) ≤ 𝓝 (0 : ℂ)))
      ((hR.tendsto.mono_left (nhdsWithin_le_nhds : 𝓝[≠] (0 : ℂ) ≤ 𝓝 (0 : ℂ))).congr' he'.symm)
    have hb : b = 0 := by simpa [hF0, hG0] using hlim.symm
    exact hdet (by simp [hd0, hb])
  have heM : F =ᶠ[𝓝 (0 : ℂ)] (fun z => mobiusFn a b c d (G z)) := he
  obtain ⟨hb, ha, hc⟩ := normalized_mobius_comp_parameters (hGan 0 hzero) hG0 hd
    (heM.self_of_nhds.symm.trans hF0) (heM.deriv_eq.symm.trans hF1)
    (heM.deriv.deriv_eq.symm.trans hF2)
  have ha' : a = d := by simpa [hG1] using ha
  have hc' : c = 0 := by
    rw [hG1, hG2] at hc
    linear_combination (1 / 2 : ℂ) * hc
  have heFG : F =ᶠ[𝓝 (0 : ℂ)] G := by
    filter_upwards [heM] with z hz
    simpa [mobiusFn, hb, ha', hc', hd] using hz
  exact hFan.eqOn_of_preconnected_of_eventuallyEq hGan
    (convex_ball (0 : ℂ) (1 : ℝ)).isPreconnected hzero heFG

-- `bers_isOpenEmbedding` moved to `Ch1/BanachSubmersion.lean` (2026-10-27).

-- bersPhi_differentiableOn moved to Ch1/QCVariation.lean (2026-10-25, leader; proved there by 下属5).

-- `phi_submersion` moved to `Ch1/BanachSubmersion.lean` (2026-10-27).

-- `ker_D0Phi` moved to `Ch1/S1_1_Completed.lean` (2026-10-25).

-- `eq_1_3` moved to `Ch1/S1_1_Completed.lean` (2026-10-25).

-- `eq_1_4` (TT:495) and `D0bers_bijective_on_harmonic` (TT:498) moved to `Ch1/QCVariationBergman.lean` (2026-10-25).

/-- The map `Λ : A∞(𝔻) → Ω^{-1,1}(𝔻*)` (TT:501):
`Λ(φ)(z) = -½ (1 - |z|²)² φ(1/z̄) z̄⁻⁴` for `z ∈ 𝔻*`. -/
def Lambda (φ : AInf unitDisc) : LinfStar :=
  toLinf fun z => -(1 / 2) * (1 - ‖z‖ ^ 2) ^ 2 * AInf.toFun φ (refl z) / conj z ^ 4

/-- Reflection cancels the weights in the explicit formula for Lambda
(TT:501). -/
theorem Lambda_kernel_norm (φ : AInf unitDisc) {z : ℂ} (hz : z ∈ unitDiscExterior)
    (hzD : refl z ∈ unitDisc) :
    ‖-(1 / 2 : ℂ) * (1 - ‖z‖ ^ 2) ^ 2 * AInf.toFun φ (refl z) / conj z ^ 4‖ =
      (1 / 2 : ℝ) * ‖φ.1 ⟨refl z, hzD⟩‖ := by
  have hz0 : z ≠ 0 := by
    intro he
    norm_num [he, unitDiscExterior] at hz
  have hn : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz0
  have hsmall : ‖refl z‖ < 1 := mem_ball_zero_iff.mp hzD
  have hweight : (1 - ‖refl z‖ ^ 2) ^ 2 * ‖z‖ ^ 4 = (1 - ‖z‖ ^ 2) ^ 2 := by
    rw [norm_refl]
    field_simp
    <;> ring
  have hd : 1 - ‖refl z‖ ^ 2 ≠ 0 := by
    have hn0 := norm_nonneg (refl z)
    nlinarith
  simp only [AInf.toFun, unweight, dif_pos hzD, norm_div, norm_mul, norm_neg,
    norm_pow, norm_conj, norm_one, norm_ofNat, norm_real, Real.norm_eq_abs]
  norm_num only [one_div, inv_pow, norm_inv, norm_ofNat]
  simp only [← Complex.ofReal_pow, ← Complex.ofReal_one, ← Complex.ofReal_sub, norm_real,
    Real.norm_eq_abs, sq_abs]
  rw [← hweight]
  field_simp [hn, hd]
  <;> ring

/-- The formula for Lambda is continuous on the exterior (TT:501). -/
theorem Lambda_kernel_continuousOn (φ : AInf unitDisc) :
    ContinuousOn (fun z : ℂ => -(1 / 2 : ℂ) * (1 - ‖z‖ ^ 2) ^ 2 *
      AInf.toFun φ (refl z) / conj z ^ 4) unitDiscExterior := by
  have hn : ∀ z ∈ unitDiscExterior, z ≠ 0 := by
    intro z hz he
    norm_num [he, unitDiscExterior] at hz
  have hr : ContinuousOn refl unitDiscExterior := by
    exact continuous_conj.continuousOn.inv₀ fun z hz =>
      (map_ne_zero (starRingEnd ℂ)).mpr (hn z hz)
  have hm : MapsTo refl unitDiscExterior unitDisc :=
    fun z hz => (refl_mem_disc_iff (hn z hz)).mpr hz
  have hf : ContinuousOn (fun z => AInf.toFun φ (refl z)) unitDiscExterior :=
    φ.property.continuousOn.comp hr hm
  have hw : Continuous (fun z : ℂ => -(1 / 2 : ℂ) * (1 - ‖z‖ ^ 2) ^ 2) := by
    fun_prop
  exact (hw.continuousOn.mul hf).div (continuous_conj.pow 4).continuousOn
    fun z hz => pow_ne_zero 4 ((map_ne_zero (starRingEnd ℂ)).mpr (hn z hz))

/-- The explicit Lambda formula is essentially bounded and measurable
(TT:501), so its conversion to L-infinity uses the genuine formula. -/
theorem Lambda_kernel_memLp (φ : AInf unitDisc) :
    MemLp (fun z : ℂ => -(1 / 2 : ℂ) * (1 - ‖z‖ ^ 2) ^ 2 *
      AInf.toFun φ (refl z) / conj z ^ 4) ∞ (volume.restrict unitDiscExterior) := by
  have hmeas : MeasurableSet unitDiscExterior :=
    (isOpen_lt continuous_const continuous_norm).measurableSet
  apply memLp_top_of_bound ((Lambda_kernel_continuousOn φ).aestronglyMeasurable hmeas) (‖φ‖ / 2)
  filter_upwards [self_mem_ae_restrict hmeas] with z hz
  have hz0 : z ≠ 0 := by intro he; norm_num [he, unitDiscExterior] at hz
  have hzD : refl z ∈ unitDisc := (refl_mem_disc_iff hz0).mpr hz
  rw [Lambda_kernel_norm φ hz hzD]
  have hbound := φ.1.norm_coe_le_norm ⟨refl z, hzD⟩
  change ‖φ.1 _‖ ≤ ‖φ‖ at hbound
  linarith

/-- The L-infinity element Lambda has the displayed coefficient almost
everywhere on the exterior (TT:501). -/
theorem Lambda_coe_ae (φ : AInf unitDisc) :
    Lambda φ =ᵐ[volume.restrict unitDiscExterior]
      (fun z : ℂ => -(1 / 2 : ℂ) * (1 - ‖z‖ ^ 2) ^ 2 *
        AInf.toFun φ (refl z) / conj z ^ 4) := by
  unfold Lambda toLinf
  rw [dif_pos (Lambda_kernel_memLp φ)]
  exact (Lambda_kernel_memLp φ).coeFn_toLp

/-- The conversion to L-infinity preserves every nonnegative almost-everywhere
bound; this also holds in its zero fallback branch. -/
theorem norm_toLinf_le_of_ae_bound {f : ℂ → ℂ} {C : ℝ} (hC : 0 ≤ C)
    (hf : ∀ᵐ z ∂(volume.restrict unitDiscExterior), ‖f z‖ ≤ C) :
    ‖toLinf f‖ ≤ C := by
  unfold toLinf
  split_ifs with h
  · rw [Lp.norm_toLp, eLpNorm_exponent_top h.aestronglyMeasurable]
    exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top
      (eLpNormEssSup_le_of_ae_bound hf)).trans_eq (ENNReal.toReal_ofReal hC)
  · simpa using hC

/-- The explicit inverse differential has operator bound one half
(TT:501–504), independently of the inverse-embedding theorem. -/
theorem Lambda_norm_le (φ : AInf unitDisc) : ‖Lambda φ‖ ≤ ‖φ‖ / 2 := by
  unfold Lambda
  apply norm_toLinf_le_of_ae_bound (by positivity)
  have hmeas : MeasurableSet unitDiscExterior :=
    (isOpen_lt continuous_const continuous_norm).measurableSet
  filter_upwards [self_mem_ae_restrict hmeas] with z hz
  have hz0 : z ≠ 0 := by intro he; norm_num [he, unitDiscExterior] at hz
  have hzD : refl z ∈ unitDisc := (refl_mem_disc_iff hz0).mpr hz
  rw [Lambda_kernel_norm φ hz hzD]
  have hbound := φ.1.norm_coe_le_norm ⟨refl z, hzD⟩
  change ‖φ.1 _‖ ≤ ‖φ‖ at hbound
  linarith

/-- The unit-ball clause in Ahlfors–Weill (TT:504): the radius-two ball is
mapped into the open unit ball of Beltrami differentials. -/
theorem Lambda_mem_ball {φ : AInf unitDisc} (hφ : ‖φ‖ < 2) :
    Lambda φ ∈ LinfStarBall := by
  change Lambda φ ∈ ball 0 1
  rw [mem_ball_zero_iff]
  exact (Lambda_norm_le φ).trans_lt (by linarith)

/-- Linearity in the quadratic differential in the Lambda formula (TT:501). -/
theorem Lambda_add (φ ψ : AInf unitDisc) : Lambda (φ + ψ) = Lambda φ + Lambda ψ := by
  apply Lp.ext
  filter_upwards [Lambda_coe_ae (φ + ψ), Lambda_coe_ae φ, Lambda_coe_ae ψ,
    Lp.coeFn_add (Lambda φ) (Lambda ψ)] with z hsum hφ hψ hadd
  rw [hsum, hadd]
  simp only [Pi.add_apply, hφ, hψ, AInf.toFun, Submodule.coe_add, unweight_add, Pi.add_apply]
  ring

/-- Complex homogeneity of the Lambda formula (TT:501). -/
theorem Lambda_smul (a : ℂ) (φ : AInf unitDisc) : Lambda (a • φ) = a • Lambda φ := by
  apply Lp.ext
  filter_upwards [Lambda_coe_ae (a • φ), Lambda_coe_ae φ,
    Lp.coeFn_smul a (Lambda φ)] with z hsmul hφ hae
  rw [hsmul, hae]
  simp only [Pi.smul_apply, smul_eq_mul, hφ, AInf.toFun, Submodule.coe_smul,
    unweight_smul, Pi.smul_apply, smul_eq_mul]
  ring

/-- Lambda is a bounded complex-linear map, hence holomorphic (TT:498–501).
This uses its formula and norm estimate, not the inverse-embedding assertion. -/
theorem Lambda_differentiable : Differentiable ℂ Lambda := by
  let L : AInf unitDisc →ₗ[ℂ] LinfStar :=
    { toFun := Lambda, map_add' := Lambda_add, map_smul' := Lambda_smul }
  have hL : ∀ φ, ‖L φ‖ ≤ (1 / 2 : ℝ) * ‖φ‖ := by
    intro φ
    simpa only [L, LinearMap.coe_mk, AddHom.coe_mk, one_div, div_eq_mul_inv, mul_comm, one_mul]
      using Lambda_norm_le φ
  exact (L.mkContinuous (1 / 2) hL).differentiable

/-- Lambda takes values in the harmonic Beltrami subspace (TT:498–501),
with the exterior quadratic differential obtained by conjugate reflection. -/
theorem Lambda_mem_harmonic (φ : AInf unitDisc) : Lambda φ ∈ harmonicBeltrami := by
  let F : ℂ → ℂ := fun z => -(1 / 2 : ℂ) * (1 - ‖z‖ ^ 2) ^ 2 *
    AInf.toFun φ (refl z) / conj z ^ 4
  let Q : ℂ → ℂ := fun z => -(1 / 2 : ℂ) * conj (AInf.toFun φ (refl z)) / z ^ 4
  have hn : ∀ z ∈ unitDiscExterior, z ≠ 0 := by
    intro z hz he
    norm_num [he, unitDiscExterior] at hz
  have hd : ∀ z ∈ unitDiscExterior, (1 - (‖z‖ : ℂ) ^ 2) ≠ 0 := by
    intro z hz he
    have heR : 1 - ‖z‖ ^ 2 = 0 := by exact_mod_cast he
    have hzR : 1 < ‖z‖ := hz
    nlinarith
  have hbound : ∀ z ∈ unitDiscExterior, ‖F z‖ ≤ ‖φ‖ / 2 := by
    intro z hz
    have hzD : refl z ∈ unitDisc := (refl_mem_disc_iff (hn z hz)).mpr hz
    rw [show F z = _ from rfl, Lambda_kernel_norm φ hz hzD]
    have hb := φ.1.norm_coe_le_norm ⟨refl z, hzD⟩
    change ‖φ.1 _‖ ≤ ‖φ‖ at hb
    linarith
  let Ψ : unitDiscExterior →ᵇ ℂ :=
    { toFun := fun z => conj (F z)
      continuous_toFun := continuous_conj.comp
        (continuousOn_iff_continuous_restrict.mp (Lambda_kernel_continuousOn φ))
      map_bounded' := ⟨‖φ‖, fun x y => by
        have hx := hbound x x.2
        have hy := hbound y y.2
        have hxy := norm_sub_le (conj (F x)) (conj (F y))
        rw [← dist_eq_norm] at hxy
        simp only [norm_conj] at hxy
        linarith⟩ }
  have hQ : DifferentiableOn ℂ Q unitDiscExterior := by
    intro z hz
    have hzD : refl z ∈ unitDisc := (refl_mem_disc_iff (hn z hz)).mpr hz
    have hf : DifferentiableAt ℂ (AInf.toFun φ) (refl z) :=
      φ.property.differentiableAt (isOpen_ball.mem_nhds hzD)
    have hg : DifferentiableAt ℂ (conj ∘ AInf.toFun φ ∘ conj) z⁻¹ := by
      simpa [refl] using hf.conj_conj
    have hc : DifferentiableAt ℂ (fun z => conj (AInf.toFun φ (refl z))) z := by
      simpa only [Function.comp_def, refl, map_inv₀] using
        hg.comp z (hasDerivAt_inv (hn z hz)).differentiableAt
    exact ((hc.const_mul (-(1 / 2 : ℂ))).div (differentiableAt_id.pow 4)
      (pow_ne_zero 4 (hn z hz))).differentiableWithinAt
  have heq : EqOn (unweight unitDiscExterior Ψ) Q unitDiscExterior := by
    intro z hz
    rw [unweight, dif_pos hz]
    change conj (F z) / (1 - (‖z‖ : ℂ) ^ 2) ^ 2 = Q z
    simp only [F, Q, map_div₀, map_mul, map_neg,
      map_pow, map_sub, map_one, map_ofNat, conj_ofReal, starRingEnd_self_apply]
    field_simp [hd z hz, hn z hz]
    <;> ring
  have hΨ : Ψ ∈ AInf unitDiscExterior := hQ.congr heq
  apply Submodule.subset_span
  refine ⟨⟨Ψ, hΨ⟩, ?_⟩
  have hmeas : MeasurableSet unitDiscExterior :=
    (isOpen_lt continuous_const continuous_norm).measurableSet
  filter_upwards [Lambda_coe_ae φ, self_mem_ae_restrict hmeas] with z hz hzE
  rw [hz]
  change F z = (1 - (‖z‖ : ℂ) ^ 2) ^ 2 * conj (unweight unitDiscExterior Ψ z)
  rw [unweight, dif_pos hzE]
  change F z = (1 - (‖z‖ : ℂ) ^ 2) ^ 2 * conj (conj (F z) / (1 - (‖z‖ : ℂ) ^ 2) ^ 2)
  simp only [map_div₀, map_pow, map_sub, map_one,
    conj_ofReal, starRingEnd_self_apply]
  field_simp [hd z hzE]
/-- The reflected inverse differential loses no quadratic differential
(TT:498–501), independently of the still-open derivative formula for Bers. -/
theorem Lambda_injective : Function.Injective Lambda := by
  intro φ ψ h
  let F : AInf unitDisc → ℂ → ℂ := fun φ z => -(1 / 2 : ℂ) * (1 - ‖z‖ ^ 2) ^ 2 *
    AInf.toFun φ (refl z) / conj z ^ 4
  have hae : F φ =ᵐ[volume.restrict unitDiscExterior] F ψ := by
    filter_upwards [Lambda_coe_ae φ, Lambda_coe_ae ψ] with z hφ hψ
    change F φ z = F ψ z
    exact hφ.symm.trans ((congrArg (fun μ : LinfStar => μ z) h).trans hψ)
  have hext : EqOn (F φ) (F ψ) unitDiscExterior :=
    Measure.eqOn_open_of_ae_eq (μ := volume) hae (isOpen_lt continuous_const continuous_norm)
      (Lambda_kernel_continuousOn φ) (Lambda_kernel_continuousOn ψ)
  have hdisc : ∀ x ∈ unitDisc, x ≠ 0 → AInf.toFun φ x = AInf.toFun ψ x := by
    intro x hx hx0
    have hy : refl x ∈ unitDiscExterior := (refl_mem_exterior_iff hx0).mpr hx
    have hy0 : refl x ≠ 0 := by
      simp only [refl, ne_eq, inv_eq_zero, map_eq_zero]
      exact hx0
    have hweight : 1 - (‖refl x‖ : ℂ) ^ 2 ≠ 0 := by
      intro he
      have heR : 1 - ‖refl x‖ ^ 2 = 0 := by exact_mod_cast he
      have hyR : 1 < ‖refl x‖ := hy
      nlinarith
    have hf := hext hy
    dsimp [F] at hf
    have hden : conj (refl x) ^ 4 ≠ 0 :=
      pow_ne_zero 4 ((map_ne_zero (starRingEnd ℂ)).mpr hy0)
    have hf' := (div_left_inj' hden).mp hf
    have hc : -(1 / 2 : ℂ) * (1 - (‖refl x‖ : ℂ) ^ 2) ^ 2 ≠ 0 :=
      mul_ne_zero (by norm_num) (pow_ne_zero 2 hweight)
    have he := mul_left_cancel₀ hc hf'
    simpa only [refl_involutive x] using he
  have haed : AInf.toFun φ =ᵐ[volume.restrict unitDisc] AInf.toFun ψ := by
    filter_upwards [self_mem_ae_restrict (show MeasurableSet unitDisc from isOpen_ball.measurableSet),
      ae_restrict_of_ae (show ∀ᵐ x : ℂ ∂volume, x ≠ 0 from ae_ne _)] with x hx hx0
    exact hdisc x hx hx0
  have heq : EqOn (AInf.toFun φ) (AInf.toFun ψ) unitDisc :=
    Measure.eqOn_open_of_ae_eq (μ := volume) haed isOpen_ball
      φ.property.continuousOn ψ.property.continuousOn
  apply Subtype.ext
  apply BoundedContinuousFunction.ext
  intro x
  have hx : ‖(x : ℂ)‖ < 1 := mem_ball_zero_iff.mp x.2
  have hd : (1 - (‖(x : ℂ)‖ : ℂ) ^ 2) ^ 2 ≠ 0 := by
    apply pow_ne_zero
    intro he
    have heR : 1 - ‖(x : ℂ)‖ ^ 2 = 0 := by exact_mod_cast he
    have hn := norm_nonneg (x : ℂ)
    nlinarith
  have hf := heq x.2
  simp only [AInf.toFun, unweight, dif_pos x.2] at hf
  exact (div_left_inj' hd).mp hf

/-- The reverse reflection in the Lambda correspondence preserves the
weighted norm up to the factor two (TT:498–501). -/
theorem exterior_reflection_norm (ψ : AInf unitDiscExterior) {z : ℂ} (hz0 : z ≠ 0)
    (hzE : refl z ∈ unitDiscExterior) :
    ‖(1 - (‖z‖ : ℂ) ^ 2) ^ 2 * (-(2 : ℂ) * conj (AInf.toFun ψ (refl z)) / z ^ 4)‖ =
      2 * ‖ψ.1 ⟨refl z, hzE⟩‖ := by
  have hn : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz0
  have hr : 1 < ‖refl z‖ := hzE
  have hd : 1 - ‖refl z‖ ^ 2 ≠ 0 := by nlinarith
  have hw : (1 - ‖refl z‖ ^ 2) ^ 2 * ‖z‖ ^ 4 = (1 - ‖z‖ ^ 2) ^ 2 := by
    rw [norm_refl]
    field_simp
    <;> ring
  simp only [AInf.toFun, unweight, dif_pos hzE, norm_mul, norm_div, norm_neg,
    norm_pow, norm_conj]
  norm_num only [norm_ofNat]
  simp only [← Complex.ofReal_pow, ← Complex.ofReal_one, ← Complex.ofReal_sub,
    norm_real, Real.norm_eq_abs, sq_abs]
  rw [← hw]
  field_simp [hn, hd]

/-- The reverse-reflected quadratic differential is holomorphic away from
the origin (TT:498–501). -/
theorem exterior_reflection_holomorphic (ψ : AInf unitDiscExterior) :
    DifferentiableOn ℂ (fun z => -(2 : ℂ) * conj (AInf.toFun ψ (refl z)) / z ^ 4)
      (unitDisc \ {0}) := by
  intro z hz
  have hz0 : z ≠ 0 := hz.2
  have hzE : refl z ∈ unitDiscExterior := (refl_mem_exterior_iff hz0).mpr hz.1
  have hf : DifferentiableAt ℂ (AInf.toFun ψ) (refl z) := ψ.property.differentiableAt
    ((isOpen_lt continuous_const continuous_norm).mem_nhds hzE)
  have hg : DifferentiableAt ℂ (conj ∘ AInf.toFun ψ ∘ conj) z⁻¹ := by
    simpa [refl] using hf.conj_conj
  have hc : DifferentiableAt ℂ (fun z => conj (AInf.toFun ψ (refl z))) z := by
    simpa only [Function.comp_def, refl, map_inv₀] using
      hg.comp z (hasDerivAt_inv hz0).differentiableAt
  exact ((hc.const_mul (-(2 : ℂ))).div (differentiableAt_id.pow 4)
    (pow_ne_zero 4 hz0)).differentiableWithinAt

/-- The apparent singularity of the reverse-reflected differential at zero
is bounded on a punctured half-disk (TT:498–501). -/
theorem exterior_reflection_bound_near_zero (ψ : AInf unitDiscExterior) {z : ℂ}
    (hz : z ∈ ball (0 : ℂ) (1 / 2 : ℝ)) (hz0 : z ≠ 0) :
    ‖-(2 : ℂ) * conj (AInf.toFun ψ (refl z)) / z ^ 4‖ ≤ 4 * ‖ψ‖ := by
  have hzN : ‖z‖ < 1 / 2 := mem_ball_zero_iff.mp hz
  have hzD : z ∈ unitDisc := mem_ball_zero_iff.mpr (lt_trans hzN (by norm_num))
  have hzE : refl z ∈ unitDiscExterior := (refl_mem_exterior_iff hz0).mpr hzD
  have hw := exterior_reflection_norm ψ hz0 hzE
  simp only [norm_mul, norm_pow, ← Complex.ofReal_pow, ← Complex.ofReal_one,
    ← Complex.ofReal_sub, norm_real, Real.norm_eq_abs, sq_abs] at hw
  have hb := ψ.1.norm_coe_le_norm ⟨refl z, hzE⟩
  change ‖ψ.1 _‖ ≤ ‖ψ‖ at hb
  have hmul : (1 - ‖z‖ ^ 2) ^ 2 * ‖-(2 : ℂ) * conj (AInf.toFun ψ (refl z)) / z ^ 4‖ ≤
      2 * ‖ψ‖ := by linarith
  have hr : ‖z‖ ^ 2 < 1 / 4 := by nlinarith [norm_nonneg z]
  have hweight : (1 / 2 : ℝ) ≤ (1 - ‖z‖ ^ 2) ^ 2 := by nlinarith [sq_nonneg (‖z‖ ^ 2)]
  have hp := mul_nonneg (sub_nonneg.mpr hweight)
    (norm_nonneg (-(2 : ℂ) * conj (AInf.toFun ψ (refl z)) / z ^ 4))
  linarith

/-- An exterior bounded quadratic differential reflects to a disk quadratic
differential after removal of the apparent singularity at zero (TT:498–501). -/
theorem exists_reverse_reflected_differential (ψ : AInf unitDiscExterior) :
    ∃ φ : AInf unitDisc, ∀ z ∈ unitDisc, z ≠ 0 →
      AInf.toFun φ z = -(2 : ℂ) * conj (AInf.toFun ψ (refl z)) / z ^ 4 := by
  let Q : ℂ → ℂ := fun z => -(2 : ℂ) * conj (AInf.toFun ψ (refl z)) / z ^ 4
  let F : ℂ → ℂ := Function.update Q 0 (limUnder (𝓝[≠] (0 : ℂ)) Q)
  have hQ0 : Q 0 = 0 := by simp [Q]
  have hb : IsBoundedUnder (· ≤ ·) (𝓝[≠] (0 : ℂ)) (fun z => ‖Q z - Q 0‖) := by
    refine ⟨4 * ‖ψ‖, ?_⟩
    change ∀ᶠ z in 𝓝[≠] (0 : ℂ), ‖Q z - Q 0‖ ≤ 4 * ‖ψ‖
    filter_upwards [mem_nhdsWithin_of_mem_nhds (ball_mem_nhds (0 : ℂ) (by norm_num : (0 : ℝ) < 1 / 2)),
      self_mem_nhdsWithin] with z hz hz0
    rw [hQ0, sub_zero]
    exact exterior_reflection_bound_near_zero ψ hz hz0
  have hF : DifferentiableOn ℂ F unitDisc :=
    Complex.differentiableOn_update_limUnder_of_isLittleO
      (isOpen_ball.mem_nhds (by simp [unitDisc]))
      (exterior_reflection_holomorphic ψ) hb.isLittleO_sub_self_inv
  have hFQ : ∀ z, z ≠ 0 → F z = Q z := by
    intro z hz
    simp only [F, Function.update_of_ne hz]
  have hpunct : ∀ z ∈ unitDisc, z ≠ 0 →
      ‖(1 - (‖z‖ : ℂ) ^ 2) ^ 2 * F z‖ ≤ 2 * ‖ψ‖ := by
    intro z hz hz0
    have hzE : refl z ∈ unitDiscExterior := (refl_mem_exterior_iff hz0).mpr hz
    rw [hFQ z hz0, show Q z = _ from rfl, exterior_reflection_norm ψ hz0 hzE]
    exact mul_le_mul_of_nonneg_left (ψ.1.norm_coe_le_norm ⟨refl z, hzE⟩) (by norm_num)
  have hbound : ∀ z ∈ unitDisc, ‖(1 - (‖z‖ : ℂ) ^ 2) ^ 2 * F z‖ ≤ 2 * ‖ψ‖ := by
    intro z hz
    by_cases hz0 : z = 0
    · subst z
      have hFc : ContinuousAt F 0 := hF.continuousOn.continuousAt (isOpen_ball.mem_nhds hz)
      have hc : ContinuousAt (fun z : ℂ => ‖(1 - (‖z‖ : ℂ) ^ 2) ^ 2 * F z‖) 0 := by fun_prop
      apply le_of_tendsto (hc.tendsto.mono_left
        (nhdsWithin_le_nhds : 𝓝[≠] (0 : ℂ) ≤ 𝓝 (0 : ℂ)))
      filter_upwards [mem_nhdsWithin_of_mem_nhds (isOpen_ball.mem_nhds hz),
        self_mem_nhdsWithin] with z hzD hz0
      exact hpunct z hzD hz0
    · exact hpunct z hz hz0
  have hc : ContinuousOn (fun z : ℂ => (1 - (‖z‖ : ℂ) ^ 2) ^ 2 * F z) unitDisc := by
    have hw : Continuous (fun z : ℂ => (1 - (‖z‖ : ℂ) ^ 2) ^ 2) := by fun_prop
    exact hw.continuousOn.mul hF.continuousOn
  let Ψ : unitDisc →ᵇ ℂ :=
    { toFun := fun z => (1 - (‖(z : ℂ)‖ : ℂ) ^ 2) ^ 2 * F z
      continuous_toFun := continuousOn_iff_continuous_domRestrict.mp hc
      map_bounded' := ⟨4 * ‖ψ‖, fun x y => by
        have hx := hbound x x.2
        have hy := hbound y y.2
        have hxy := norm_sub_le ((1 - (‖(x : ℂ)‖ : ℂ) ^ 2) ^ 2 * F x)
          ((1 - (‖(y : ℂ)‖ : ℂ) ^ 2) ^ 2 * F y)
        rw [← dist_eq_norm] at hxy
        linarith⟩ }
  have he : EqOn (unweight unitDisc Ψ) F unitDisc := by
    intro z hz
    have hzN : ‖z‖ < 1 := mem_ball_zero_iff.mp hz
    have hd : (1 - (‖z‖ : ℂ) ^ 2) ^ 2 ≠ 0 := by
      apply pow_ne_zero
      intro h
      have hr : 1 - ‖z‖ ^ 2 = 0 := by exact_mod_cast h
      nlinarith [norm_nonneg z]
    rw [unweight, dif_pos hz]
    change ((1 - (‖z‖ : ℂ) ^ 2) ^ 2 * F z) / (1 - (‖z‖ : ℂ) ^ 2) ^ 2 = F z
    exact mul_div_cancel_left₀ _ hd
  refine ⟨⟨Ψ, hF.congr he⟩, ?_⟩
  intro z hz hz0
  exact (he hz).trans (hFQ z hz0)

/-- Every bounded harmonic Beltrami differential is in the image of Lambda
(TT:498–501). This is an explicit reflection construction and does not use
the still-open differential formula for the Bers map. -/
theorem Lambda_surjective_harmonic {μ : LinfStar} (hμ : μ ∈ harmonicBeltrami) :
    ∃ φ : AInf unitDisc, Lambda φ = μ := by
  obtain ⟨ψ, hψ⟩ := (mem_harmonicBeltrami_iff μ).mp hμ
  obtain ⟨φ, hφ⟩ := exists_reverse_reflected_differential ψ
  refine ⟨φ, Lp.ext ?_⟩
  have hmeas : MeasurableSet unitDiscExterior :=
    (isOpen_lt continuous_const continuous_norm).measurableSet
  filter_upwards [Lambda_coe_ae φ, hψ, self_mem_ae_restrict hmeas] with z hΛ hμz hz
  rw [hΛ, hμz]
  have hz0 : z ≠ 0 := by intro he; norm_num [he, unitDiscExterior] at hz
  have hzD : refl z ∈ unitDisc := (refl_mem_disc_iff hz0).mpr hz
  have hr0 : refl z ≠ 0 := inv_ne_zero ((map_ne_zero (starRingEnd ℂ)).mpr hz0)
  rw [hφ (refl z) hzD hr0, refl_involutive z]
  dsimp only [refl]
  have hc : conj z ≠ 0 := (map_ne_zero (starRingEnd ℂ)).mpr hz0
  field_simp
  <;> ring

/-- The image of the explicit reflection map is exactly the bounded
harmonic Beltrami subspace (TT:498–501). -/
theorem range_Lambda : range Lambda = (harmonicBeltrami : Set LinfStar) := by
  ext μ
  constructor
  · rintro ⟨φ, rfl⟩
    exact Lambda_mem_harmonic φ
  · exact Lambda_surjective_harmonic

/-- The explicit map Lambda is a bijection onto the harmonic subspace
(TT:498–501). Identification with the inverse Bers derivative remains separate. -/
theorem Lambda_harmonic_bijective : Function.Bijective
    (fun φ : AInf unitDisc => (⟨Lambda φ, Lambda_mem_harmonic φ⟩ : harmonicBeltrami)) := by
  constructor
  · intro φ ψ h
    exact Lambda_injective (congrArg Subtype.val h)
  · intro μ
    obtain ⟨φ, hφ⟩ := Lambda_surjective_harmonic μ.2
    exact ⟨φ, Subtype.ext hφ⟩

/-- A continuous function on an open plane set satisfies a pointwise norm
bound whenever it satisfies that bound almost everywhere. -/
theorem continuousOn_norm_le_of_ae_bound {U : Set ℂ} {f : ℂ → ℂ} {C : ℝ}
    (hU : IsOpen U) (hf : ContinuousOn f U)
    (h : ∀ᵐ z ∂(volume.restrict U), ‖f z‖ ≤ C) : ∀ z ∈ U, ‖f z‖ ≤ C := by
  have he : (fun z => max ‖f z‖ C) =ᵐ[volume.restrict U] (fun _ => C) :=
    h.mono fun z hz => max_eq_right hz
  have hh := Measure.eqOn_open_of_ae_eq (μ := volume) he hU
    (continuous_max.comp_continuousOn (hf.norm.prodMk continuousOn_const)) continuousOn_const
  intro z hz
  exact (le_max_left _ _).trans_eq (hh hz)

/-- Lambda scales the Banach norm exactly by one half (TT:498–501).
Continuity upgrades its essential bound to pointwise bounds before reflecting
back to the disk, including the origin. -/
theorem Lambda_norm_eq (φ : AInf unitDisc) : ‖Lambda φ‖ = ‖φ‖ / 2 := by
  let F : ℂ → ℂ := fun z => -(1 / 2 : ℂ) * (1 - ‖z‖ ^ 2) ^ 2 *
    AInf.toFun φ (refl z) / conj z ^ 4
  have hae : ∀ᵐ z ∂(volume.restrict unitDiscExterior), ‖F z‖ ≤ ‖Lambda φ‖ := by
    filter_upwards [Lambda_coe_ae φ, LinfStar_ae_norm_le (Lambda φ)] with z hz hb
    rw [hz] at hb
    exact hb
  have hbound : ∀ z ∈ unitDiscExterior, ‖F z‖ ≤ ‖Lambda φ‖ :=
    continuousOn_norm_le_of_ae_bound (isOpen_lt continuous_const continuous_norm)
      (Lambda_kernel_continuousOn φ) hae
  have hpunct : ∀ (z : ℂ) (hz : z ∈ unitDisc), z ≠ 0 →
      ‖φ.1 ⟨z, hz⟩‖ ≤ 2 * ‖Lambda φ‖ := by
    intro z hz hz0
    have hzE : refl z ∈ unitDiscExterior := (refl_mem_exterior_iff hz0).mpr hz
    have hzD : refl (refl z) ∈ unitDisc := by simpa only [refl_involutive z] using hz
    have hnorm := Lambda_kernel_norm φ hzE hzD
    have hb := hbound (refl z) hzE
    change ‖-(1 / 2 : ℂ) * (1 - ‖refl z‖ ^ 2) ^ 2 *
      AInf.toFun φ (refl (refl z)) / conj (refl z) ^ 4‖ ≤ ‖Lambda φ‖ at hb
    rw [hnorm] at hb
    simp only [refl_involutive z] at hb
    linarith
  let G : ℂ → ℂ := fun z => (1 - (‖z‖ : ℂ) ^ 2) ^ 2 * AInf.toFun φ z
  have hG : ∀ (z : ℂ) (hz : z ∈ unitDisc), G z = φ.1 ⟨z, hz⟩ := by
    intro z hz
    have hzN : ‖z‖ < 1 := mem_ball_zero_iff.mp hz
    have hd : (1 - (‖z‖ : ℂ) ^ 2) ^ 2 ≠ 0 := by
      apply pow_ne_zero
      intro he
      have heR : 1 - ‖z‖ ^ 2 = 0 := by exact_mod_cast he
      nlinarith [norm_nonneg z]
    dsimp only [G, AInf.toFun]
    rw [unweight, dif_pos hz]
    exact mul_div_cancel₀ _ hd
  have hGc : ContinuousOn G unitDisc := by
    have hw : Continuous (fun z : ℂ => (1 - (‖z‖ : ℂ) ^ 2) ^ 2) := by fun_prop
    exact hw.continuousOn.mul φ.property.continuousOn
  have hGa : ∀ᵐ z ∂(volume.restrict unitDisc), ‖G z‖ ≤ 2 * ‖Lambda φ‖ := by
    filter_upwards [self_mem_ae_restrict (show MeasurableSet unitDisc from isOpen_ball.measurableSet),
      ae_restrict_of_ae (show ∀ᵐ z : ℂ ∂volume, z ≠ 0 from ae_ne _)] with z hz hz0
    rw [hG z hz]
    exact hpunct z hz hz0
  have hb := continuousOn_norm_le_of_ae_bound isOpen_ball hGc hGa
  have hφ : ‖φ‖ ≤ 2 * ‖Lambda φ‖ := by
    change ‖φ.1‖ ≤ 2 * ‖Lambda φ‖
    apply (BoundedContinuousFunction.norm_le (by positivity)).mpr
    intro z
    rw [← hG z z.2]
    exact hb z z.2
  linarith [Lambda_norm_le φ]

/-- The explicit bounded complex-linear equivalence between disk quadratic
differentials and harmonic Beltrami coefficients (TT:498–501). Its relation
to the Bers derivative is a separate theorem. -/
def LambdaEquiv : AInf unitDisc ≃L[ℂ] harmonicBeltrami := by
  let L : AInf unitDisc →ₗ[ℂ] harmonicBeltrami :=
    { toFun := fun φ => ⟨Lambda φ, Lambda_mem_harmonic φ⟩
      map_add' := fun φ ψ => Subtype.ext (Lambda_add φ ψ)
      map_smul' := fun a φ => Subtype.ext (Lambda_smul a φ) }
  let E : AInf unitDisc ≃ₗ[ℂ] harmonicBeltrami :=
    LinearEquiv.ofBijective L (show Function.Bijective L from Lambda_harmonic_bijective)
  refine E.toContinuousLinearEquivOfBounds (1 / 2) 2 ?_ ?_
  · intro φ
    change ‖Lambda φ‖ ≤ (1 / 2 : ℝ) * ‖φ‖
    linarith [Lambda_norm_le φ]
  · intro μ
    have he : Lambda (E.symm μ) = (μ : LinfStar) :=
      congrArg Subtype.val (E.apply_symm_apply μ)
    have hn := Lambda_norm_eq (E.symm μ)
    rw [he] at hn
    change ‖E.symm μ‖ ≤ 2 * ‖(μ : LinfStar)‖
    linarith

/-- The equivalence uses the previously defined Lambda map (TT:501). -/
theorem LambdaEquiv_apply (φ : AInf unitDisc) :
    (LambdaEquiv φ : LinfStar) = Lambda φ := rfl

/-- The inverse equivalence multiplies the norm by two (TT:498–501). -/
theorem LambdaEquiv_symm_norm (μ : harmonicBeltrami) :
    ‖LambdaEquiv.symm μ‖ = 2 * ‖μ‖ := by
  have he : Lambda (LambdaEquiv.symm μ) = (μ : LinfStar) := by
    rw [← LambdaEquiv_apply, LambdaEquiv.apply_symm_apply]
  have hn := Lambda_norm_eq (LambdaEquiv.symm μ)
  rw [he] at hn
  change ‖LambdaEquiv.symm μ‖ = 2 * ‖(μ : LinfStar)‖
  linarith

/-- The weighted holomorphic subspace is closed when the domain is open and
the weight does not vanish there (TT:363, TT:477). -/
theorem isClosed_AInf {D : Set ℂ} (hD : IsOpen D) (hweight : ∀ z ∈ D, ‖z‖ ≠ 1) :
    IsClosed (AInf D : Set (D →ᵇ ℂ)) := by
  apply IsSeqClosed.isClosed
  intro F f hF hf
  let r : D → ℂ := fun z => ((1 - (‖(z : ℂ)‖ : ℂ) ^ 2) ^ 2)⁻¹
  have hr : Continuous r := by
    apply Continuous.inv₀
    · fun_prop
    · intro z
      apply pow_ne_zero
      intro he
      have heR : 1 - ‖(z : ℂ)‖ ^ 2 = 0 := by exact_mod_cast he
      apply hweight z z.2
      nlinarith [norm_nonneg (z : ℂ)]
  have hU : TendstoUniformly (fun n => F n) f atTop :=
    BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mp hf
  have hrU : TendstoUniformly (fun _ : ℕ => r) r atTop := by
    apply Metric.tendstoUniformly_iff.mpr
    intro ε hε
    exact Filter.Eventually.of_forall fun n z => by simpa using hε
  have hprod := hU.tendstoLocallyUniformly.mul₀ hrU.tendstoLocallyUniformly f.continuous hr
  have hlim : TendstoLocallyUniformlyOn (fun n => unweight D (F n)) (unweight D f) atTop D := by
    apply tendstoLocallyUniformlyOn_iff_tendstoLocallyUniformly_comp_coe.mpr
    convert hprod using 1
    · funext n z
      simp [unweight, r, div_eq_mul_inv]
    · funext z
      simp [unweight, r, div_eq_mul_inv, Function.comp_def]
  exact hlim.differentiableOn (Filter.Eventually.of_forall hF) hD

/-- Completeness of the disk A-infinity space (TT:363, TT:477), proved from
closedness in the bounded continuous functions. -/
theorem AInf_completeSpace_disc : CompleteSpace (AInf unitDisc) := by
  apply (isClosed_AInf isOpen_ball ?_).completeSpace_coe
  intro z hz
  exact ne_of_lt (mem_ball_zero_iff.mp hz)

/-- Completeness of the exterior A-infinity space (TT:363, TT:477). -/
theorem AInf_completeSpace_exterior : CompleteSpace (AInf unitDiscExterior) := by
  apply (isClosed_AInf (isOpen_lt continuous_const continuous_norm) ?_).completeSpace_coe
  intro z hz
  exact ne_of_gt hz

/-- The harmonic Beltrami space is complete by the explicit bounded linear
equivalence Lambda (TT:361, TT:498). This theorem does not add a global instance. -/
theorem harmonicBeltrami_completeSpace : CompleteSpace harmonicBeltrami := by
  letI : CompleteSpace (AInf unitDisc) := AInf_completeSpace_disc
  let E : AInf unitDisc ≃ᵤ harmonicBeltrami :=
    { toEquiv := LambdaEquiv.toLinearEquiv.toEquiv
      uniformContinuous_toFun := LambdaEquiv.toContinuousLinearMap.uniformContinuous
      uniformContinuous_invFun := LambdaEquiv.symm.toContinuousLinearMap.uniformContinuous }
  exact E.completeSpace_iff.mp inferInstance

/-- The harmonic Beltrami subspace is closed in L-infinity (TT:361). -/
theorem isClosed_harmonicBeltrami : IsClosed (harmonicBeltrami : Set LinfStar) := by
  have hc : IsComplete (harmonicBeltrami : Set LinfStar) :=
    completeSpace_coe_iff_isComplete.mp harmonicBeltrami_completeSpace
  exact hc.isClosed

/-- The L-infinity/L-one pairing defining infinitesimal triviality is
bounded by the product of the norms (TT:351–353). -/
theorem trivialPairing_norm_le (μ : LinfStar) {φ : ℂ → ℂ}
    (hφ : IntegrableOn φ unitDiscExterior) :
    ‖∫ z in unitDiscExterior, μ z * φ z‖ ≤ ‖μ‖ * ∫ z in unitDiscExterior, ‖φ z‖ := by
  have hi : IntegrableOn (fun z => μ z * φ z) unitDiscExterior :=
    hφ.mul_of_top_right (Lp.memLp μ)
  calc
    _ ≤ ∫ z in unitDiscExterior, ‖μ z * φ z‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ z in unitDiscExterior, ‖μ‖ * ‖φ z‖ := by
      apply integral_mono_ae hi.norm (hφ.norm.const_mul ‖μ‖)
      filter_upwards [LinfStar_ae_norm_le μ] with z hz
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right hz (norm_nonneg _)
    _ = _ := integral_const_mul _ _

/-- Each annihilator functional is continuous and complex linear
(TT:351–353); continuity follows from its explicit integral bound. -/
theorem trivialPairing_continuous {φ : ℂ → ℂ} (hφ : IntegrableOn φ unitDiscExterior) :
    Continuous (fun μ : LinfStar => ∫ z in unitDiscExterior, μ z * φ z) := by
  let L : LinfStar →ₗ[ℂ] ℂ :=
    { toFun := fun μ => ∫ z in unitDiscExterior, μ z * φ z
      map_add' := fun μ ν => by
        have he : (fun z => (μ + ν) z * φ z) =ᵐ[volume.restrict unitDiscExterior]
            (fun z => μ z * φ z + ν z * φ z) := by
          filter_upwards [Lp.coeFn_add μ ν] with z hz
          simp only [hz, Pi.add_apply, add_mul]
        exact (integral_congr_ae he).trans
          (integral_add (hφ.mul_of_top_right (Lp.memLp μ)) (hφ.mul_of_top_right (Lp.memLp ν)))
      map_smul' := fun a μ => by
        have he : (fun z => (a • μ) z * φ z) =ᵐ[volume.restrict unitDiscExterior]
            (fun z => a * (μ z * φ z)) := by
          filter_upwards [Lp.coeFn_smul a μ] with z hz
          simp only [hz, Pi.smul_apply, smul_eq_mul, mul_assoc]
        exact (integral_congr_ae he).trans (integral_const_mul a _) }
  have hb : ∀ μ, ‖L μ‖ ≤ (∫ z in unitDiscExterior, ‖φ z‖) * ‖μ‖ := by
    intro μ
    simpa only [L, LinearMap.coe_mk, AddHom.coe_mk, mul_comm] using trivialPairing_norm_le μ hφ
  exact (L.mkContinuous _ hb).continuous

/-- The infinitesimally trivial subspace is closed, as the intersection of
the kernels of its continuous annihilator functionals (TT:351–353). -/
theorem isClosed_trivialBeltrami : IsClosed (trivialBeltrami : Set LinfStar) := by
  have he : (trivialBeltrami : Set LinfStar) =
      ⋂ φ : {φ : ℂ → ℂ // φ ∈ AOneStar}, {μ : LinfStar | ∫ z in unitDiscExterior, μ z * φ.1 z = 0} := by
    ext μ
    change μ ∈ trivialBeltrami ↔ _
    simp only [mem_trivialBeltrami_iff, trivialBeltramiSet, mem_setOf_eq, mem_iInter, Subtype.forall]
  rw [he]
  apply isClosed_iInter
  intro φ
  exact isClosed_eq (trivialPairing_continuous φ.2.2.1) continuous_const

/-- Completeness of the infinitesimally trivial subspace (TT:351–353),
without installing a new global typeclass instance. -/
theorem trivialBeltrami_completeSpace : CompleteSpace trivialBeltrami :=
  isClosed_trivialBeltrami.completeSpace_coe

/-- Boundary-pole quadratic differentials belong to disk A-infinity
(TT:365). Their weighted norms are bounded by four. -/
theorem exists_boundaryKernel (ξ : ℂ) (hξ : ‖ξ‖ = 1) :
    ∃ φ : AInf unitDisc, ∀ z : unitDisc,
      φ.1 z = (1 - (‖(z : ℂ)‖ : ℂ) ^ 2) ^ 2 / (ξ - z) ^ 2 := by
  have hden : ∀ z ∈ unitDisc, ξ - z ≠ 0 := by
    intro z hz he
    have hn := mem_ball_zero_iff.mp hz
    have heq := sub_eq_zero.mp he
    rw [← heq, hξ] at hn
    exact lt_irrefl _ hn
  let F : ℂ → ℂ := fun z => 1 / (ξ - z) ^ 2
  have hF : DifferentiableOn ℂ F unitDisc := by
    intro z hz
    exact ((differentiableAt_const (1 : ℂ)).div (((differentiableAt_const ξ).sub differentiableAt_id).pow 2)
      (pow_ne_zero 2 (hden z hz))).differentiableWithinAt
  have hb : ∀ z ∈ unitDisc, ‖(1 - (‖z‖ : ℂ) ^ 2) ^ 2 * F z‖ ≤ 4 := by
    intro z hz
    have hn : ‖z‖ < 1 := mem_ball_zero_iff.mp hz
    have hlow : 1 - ‖z‖ ≤ ‖ξ - z‖ := by simpa only [hξ] using norm_sub_norm_le ξ z
    have hp : 0 < ‖ξ - z‖ := norm_pos_iff.mpr (hden z hz)
    have hw : 0 ≤ 1 - ‖z‖ ^ 2 := by nlinarith [norm_nonneg z]
    have hupper : 1 - ‖z‖ ^ 2 ≤ 2 * ‖ξ - z‖ := by nlinarith [sq_nonneg (1 - ‖z‖)]
    rw [show (1 - (‖z‖ : ℂ) ^ 2) ^ 2 * F z =
      (1 - (‖z‖ : ℂ) ^ 2) ^ 2 / (ξ - z) ^ 2 by dsimp [F]; ring]
    simp only [norm_div, norm_pow, ← Complex.ofReal_pow,
      ← Complex.ofReal_one, ← Complex.ofReal_sub, norm_real, Real.norm_eq_abs, sq_abs]
    apply (div_le_iff₀ (sq_pos_of_pos hp)).mpr
    nlinarith
  have hc : ContinuousOn (fun z : ℂ => (1 - (‖z‖ : ℂ) ^ 2) ^ 2 * F z) unitDisc := by
    have hw : Continuous (fun z : ℂ => (1 - (‖z‖ : ℂ) ^ 2) ^ 2) := by fun_prop
    exact hw.continuousOn.mul hF.continuousOn
  let Ψ : unitDisc →ᵇ ℂ :=
    { toFun := fun z => (1 - (‖(z : ℂ)‖ : ℂ) ^ 2) ^ 2 * F z
      continuous_toFun := continuousOn_iff_continuous_domRestrict.mp hc
      map_bounded' := ⟨8, fun x y => by
        have hx := hb x x.2
        have hy := hb y y.2
        have hxy := norm_sub_le ((1 - (‖(x : ℂ)‖ : ℂ) ^ 2) ^ 2 * F x)
          ((1 - (‖(y : ℂ)‖ : ℂ) ^ 2) ^ 2 * F y)
        rw [← dist_eq_norm] at hxy
        linarith⟩ }
  have he : EqOn (unweight unitDisc Ψ) F unitDisc := by
    intro z hz
    have hn : ‖z‖ < 1 := mem_ball_zero_iff.mp hz
    have hd : (1 - (‖z‖ : ℂ) ^ 2) ^ 2 ≠ 0 := by
      apply pow_ne_zero
      intro he
      have hr : 1 - ‖z‖ ^ 2 = 0 := by exact_mod_cast he
      nlinarith [norm_nonneg z]
    rw [unweight, dif_pos hz]
    exact mul_div_cancel_left₀ _ hd
  refine ⟨⟨Ψ, hF.congr he⟩, ?_⟩
  intro z
  change _ * (1 / (ξ - z) ^ 2) = _
  ring

/-- Distinct boundary poles give uniformly separated elements (TT:365).
The estimate follows by approaching one pole radially inside the disk. -/
theorem boundaryKernel_separated {ξ η : ℂ} (hξ : ‖ξ‖ = 1) (hne : ξ ≠ η)
    (φ ψ : AInf unitDisc)
    (hφ : ∀ z : unitDisc, φ.1 z = (1 - (‖(z : ℂ)‖ : ℂ) ^ 2) ^ 2 / (ξ - z) ^ 2)
    (hψ : ∀ z : unitDisc, ψ.1 z = (1 - (‖(z : ℂ)‖ : ℂ) ^ 2) ^ 2 / (η - z) ^ 2) :
    4 ≤ ‖φ - ψ‖ := by
  have hξ0 : ξ ≠ 0 := by intro h; simpa [h] using hξ
  have hηξ : η - ξ ≠ 0 := sub_ne_zero.mpr hne.symm
  let G : ℝ → ℂ := fun r => (1 + (r : ℂ)) ^ 2 / ξ ^ 2 -
    (1 - (r : ℂ) ^ 2) ^ 2 / (η - (r : ℂ) * ξ) ^ 2
  have hc : ContinuousAt G 1 := by
    apply ContinuousAt.sub
    · fun_prop
    · apply ContinuousAt.div
      · fun_prop
      · fun_prop
      · simpa using pow_ne_zero 2 hηξ
  have hG1 : ‖G 1‖ = 4 := by
    norm_num [G, norm_div, norm_pow, hξ]
  rw [← hG1]
  apply le_of_tendsto (hc.norm.tendsto.mono_left
    (nhdsWithin_le_nhds : 𝓝[<] (1 : ℝ) ≤ 𝓝 (1 : ℝ)))
  filter_upwards [mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds (by norm_num : (0 : ℝ) < 1)),
    self_mem_nhdsWithin] with r hr0 hr1
  change 0 < r at hr0
  change r < 1 at hr1
  have hn : ‖(r : ℂ) * ξ‖ = r := by
    rw [norm_mul, hξ, mul_one, norm_real, Real.norm_eq_abs, abs_of_pos hr0]
  have hz : (r : ℂ) * ξ ∈ unitDisc := mem_ball_zero_iff.mpr (by simpa only [hn] using hr1)
  have hd : (1 : ℂ) - r ≠ 0 := by
    exact_mod_cast (ne_of_gt (sub_pos.mpr hr1) : (1 : ℝ) - r ≠ 0)
  have he : G r = (φ - ψ).1 ⟨(r : ℂ) * ξ, hz⟩ := by
    change G r = φ.1 ⟨_, hz⟩ - ψ.1 ⟨_, hz⟩
    rw [hφ, hψ]
    simp only [hn, G]
    congr 1
    rw [show ξ - (r : ℂ) * ξ = (1 - r) * ξ by ring]
    field_simp [hd, hξ0]
    ring
  rw [he]
  exact (φ - ψ).1.norm_coe_le_norm _

/-- A Cayley parametrization supplies distinct unit-circle poles indexed
by all real numbers (TT:365). -/
theorem exists_boundaryPole_family : ∃ ξ : ℝ → ℂ,
    Function.Injective ξ ∧ ∀ t, ‖ξ t‖ = 1 := by
  let ξ : ℝ → ℂ := fun t => ((t : ℂ) - I) / ((t : ℂ) + I)
  have hd : ∀ t : ℝ, (t : ℂ) + I ≠ 0 := by
    intro t he
    have hi := congrArg Complex.im he
    simpa using hi
  refine ⟨ξ, ?_, ?_⟩
  · intro a b he
    have hp := (div_eq_div_iff (hd a) (hd b)).mp he
    have hi := congrArg Complex.im hp
    simp only [mul_im, sub_re, ofReal_re, I_re, sub_zero, add_im, ofReal_im,
      I_im, zero_add, sub_im, zero_sub, add_re, add_zero, mul_one, neg_mul, one_mul] at hi
    linarith
  · intro t
    change ‖((t : ℂ) - I) / ((t : ℂ) + I)‖ = 1
    rw [norm_div]
    have he : ‖(t : ℂ) - I‖ = ‖(t : ℂ) + I‖ := by
      simp [Complex.norm_def, Complex.normSq_apply]
    rw [he, div_self (norm_ne_zero_iff.mpr (hd t))]

/-- Disk A-infinity is not separable: its boundary-pole kernels give
uncountably many disjoint open balls (TT:365). -/
theorem AInf_disc_not_separable : ¬ TopologicalSpace.SeparableSpace (AInf unitDisc) := by
  intro hs
  letI := hs
  obtain ⟨ξ, hξinj, hξnorm⟩ := exists_boundaryPole_family
  choose φ hφ using fun t => exists_boundaryKernel (ξ t) (hξnorm t)
  have hdis : Pairwise (fun a b : ℝ => Disjoint (ball (φ a) 1) (ball (φ b) 1)) := by
    intro a b hab
    apply ball_disjoint_ball
    rw [dist_eq_norm]
    have hb := boundaryKernel_separated (hξnorm a) (fun he => hab (hξinj he))
      (φ a) (φ b) (hφ a) (hφ b)
    linarith
  haveI : Countable ℝ := hdis.countable_of_isOpen_disjoint
    (fun _ => isOpen_ball) (fun _ => ⟨_, mem_ball_self (by norm_num)⟩)
  exact Cardinal.not_countable_real (Set.to_countable _)

/-- (TT:365) The Banach space `Ω^{-1,1}(𝔻*)` is not separable.
Nonseparability transfers through the proved Lambda equivalence. -/
theorem harmonicBeltrami_not_separable :
    ¬ TopologicalSpace.SeparableSpace harmonicBeltrami := by
  intro hs
  letI := hs
  exact AInf_disc_not_separable
    (LambdaEquiv.symm.surjective.denseRange.separableSpace LambdaEquiv.symm.continuous)

-- `lambda_inverse_D0bers` (TT:498) moved to `Ch1/QCVariationBergman.lean` (2026-10-25).

-- `ahlfors_weill` moved to `Ch1/AhlforsWeillCompleted.lean` (2026-10-25).

/-! ## §1.1.2 The group structure -/

/-- The composition law on `L∞(𝔻*)₁` (TT:447–452): `ν * μ` is the Beltrami differential (on `𝔻*`) of
`w_ν ∘ w_μ`, so that `w_{ν * μ} = w_ν ∘ w_μ` (`wA_mul`). -/
def beltramiMul (ν μ : LinfStar) : LinfStar := toLinf (complexDilatation (wA ν ∘ wA μ))

/-- The inverse `μ⁻¹` (TT:447): the Beltrami differential (on `𝔻*`) of `w_μ⁻¹`, so that `μ * μ⁻¹ = 0`. -/
def beltramiInv (μ : LinfStar) : LinfStar := toLinf (complexDilatation (Function.invFun (wA μ)))

-- `wA_mul` moved to `Ch1/S1_1_Completed.lean` (2026-10-25).

-- `beltramiMul_inv_formula` moved to `Ch1/S1_1_Completed.lean` (2026-10-25).

-- `realAnalyticBeltrami_subgroup` moved to `TakhtajanTeo.Ch1.BeltramiRealAnalytic` (2026-10-29, Program G).

-- `beltramiMul_respects` moved to `Ch1/S1_1_Completed.lean` (2026-10-25).

/-- The right translation `R_[μ] : T(1) → T(1)`, `[λ] ↦ [λ * μ]` (TT:461), computed on representatives. -/
def rightTrans (μ : LinfStarBall) (p : T1) : T1 :=
  if h : beltramiMul (Quotient.out p : LinfStarBall) μ ∈ LinfStarBall then Phi ⟨_, h⟩ else p

/-- The left translation `L_[μ] : T(1) → T(1)`, `[λ] ↦ [μ * λ]` (TT:466), computed on representatives. -/
def leftTrans (μ : LinfStarBall) (p : T1) : T1 :=
  if h : beltramiMul μ (Quotient.out p : LinfStarBall) ∈ LinfStarBall then Phi ⟨_, h⟩ else p

-- `rightTrans_biholomorphic` moved to `Ch1/BanachSubmersion.lean` (2026-10-27).

-- `exists_leftTrans_not_continuous` moved to `Ch1/LeftTransDiscont.lean` (2026-10-28).

-- `ker_DmuPhi` moved to `Ch1/BanachSubmersion.lean` (2026-10-27).

/-! ## §1.1.4 The complex structure -/

/-- The inverse Bers chart `h_μ⁻¹ = Φ ∘ R_μ ∘ Λ` on the ball of radius `2` in `A∞(𝔻)` (TT:506), with values in
`T(1)` (junk value `Phi μ` when `R_μ(Λ(φ))` leaves `L∞(𝔻*)₁`, which does not happen for `‖φ‖ < 2`). -/
def bersChartInv (μ : LinfStarBall) (φ : AInf unitDisc) : T1 :=
  if h : beltramiMul (Lambda φ) μ ∈ LinfStarBall then Phi ⟨_, h⟩ else Phi μ

/-- The chart domain `U_μ = h_μ⁻¹(ball 0 2)` (TT:506). -/
def bersChartDomain (μ : LinfStarBall) : Set T1 := bersChartInv μ '' ball 0 2

/-- The Bers chart `h_μ : U_μ → A∞(𝔻)` (TT:506), the inverse of `h_μ⁻¹` on the ball of radius `2`. -/
def bersChart (μ : LinfStarBall) : T1 → AInf unitDisc := Function.invFunOn (bersChartInv μ) (ball 0 2)

-- `bers_atlas` moved to `Ch1/BersAtlas.lean` (2026-10-26).

-- `remark_1_2` moved to `TakhtajanTeo.Ch1.BeltramiRealAnalytic` (2026-10-29, Program G).

/-- **(1.6)** (TT:545). `R(ν, μ) = ((ν/(1 - |μ|²)) (w_μ)_z/\overline{(w_μ)_z}) ∘ w_μ⁻¹` on `𝔻*`. -/
def Rnm (ν μ : LinfStar) : LinfStar :=
  toLinf fun z =>
    (fun u => ν u / (1 - ‖μ u‖ ^ 2) * (dz (wA μ) u / conj (dz (wA μ) u))) (Function.invFun (wA μ) z)

/-- **(1.7)** (TT:551). The operator `P : L∞(𝔻*) → L∞(𝔻*)`,
`(Pμ)(z) = (3(1 - |z|²)²/π) ∬_{𝔻*} μ(ζ)/(1 - ζ z̄)⁴ d²ζ`. -/
def harmonicProj (μ : LinfStar) : LinfStar :=
  toLinf fun z => 3 * (1 - ‖z‖ ^ 2) ^ 2 / π * ∫ ζ in unitDiscExterior, μ ζ / (1 - ζ * conj z) ^ 4

-- `harmonicProj_isProjection` moved to `Ch1/HarmonicProjCompleted.lean` (2026-10-26).

-- `eq_1_5` moved to `Ch1/S1_1_Completed.lean` (2026-10-25).

-- `remark_1_3` moved to `Ch1/S1_1_Completed.lean` (2026-10-25).

/-! ## §1.1.5 The universal Teichmüller curve -/

/-- `𝔻*` as a subset of `ℂ̄` (including `∞`). -/
def extDiscExterior : Set ExtPlane := toExt unitDiscExterior ∪ {extInf}

/-- **(1.8)** (TT:565). The universal Teichmüller curve `𝒯(1) = {([μ], z) : [μ] ∈ T(1), z ∈ w^μ(𝔻*)}`. The fiber
`w^μ(𝔻*)` depends only on `[μ]` (`fiber_independent`), so it is computed on the representative `Quotient.out`. -/
def TCurve : Set (T1 × ExtPlane) :=
  {q | q.2 ∈ wB (Quotient.out q.1 : LinfStarBall) '' extDiscExterior}

theorem fi_extDiscExterior_eq_compl :
    extDiscExterior = (toExt (closedBall (0 : ℂ) 1))ᶜ := by
  ext p
  induction p using OnePoint.rec with
  | infty => simp [extDiscExterior, extInf, toExt]
  | coe z =>
    simp only [extDiscExterior, mem_union, mem_compl_iff, toExt, mem_image, mem_singleton_iff]
    constructor
    · rintro (⟨y, hy, hyz⟩ | h)
      · rintro ⟨x, hx, hxz⟩
        have := OnePoint.coe_injective (hxz.trans hyz.symm)
        subst this
        simp [unitDiscExterior] at hy
        simp at hx
        linarith
      · exact absurd h (OnePoint.coe_ne_infty z)
    · intro h
      left
      refine ⟨z, ?_, rfl⟩
      simp [unitDiscExterior]
      by_contra hc
      exact h ⟨z, by simpa using not_lt.mp hc, rfl⟩

/-- (TT:562) The fiber `w^μ(𝔻*)` depends only on the class `[μ]`. -/
theorem fiber_independent {μ ν : LinfStarBall} (h : teichSetoid μ ν) :
    wB μ '' extDiscExterior = wB ν '' extDiscExterior := by
  have hfB : ∀ z ∈ unitDisc, fB μ z = fB ν z := (modelA_iff_modelB μ ν).1 h
  have hcl := wB_eq_closed μ.property ν.property hfB
  rw [fi_extDiscExterior_eq_compl, Set.image_compl_eq (wB_bijective μ),
    Set.image_compl_eq (wB_bijective ν), Set.image_congr hcl]

/-- The zero section `[μ] ↦ ([μ], w^μ(∞))` of `π : 𝒯(1) → T(1)` (TT:568; see the module docstring for the reading
of the memoir's `([μ], ∞)`). -/
def zeroSection (p : T1) : T1 × ExtPlane := (p, wB (Quotient.out p : LinfStarBall) extInf)

/-- (TT:568) The zero section lands in `𝒯(1)`. -/
theorem zeroSection_mem (p : T1) : zeroSection p ∈ TCurve :=
  ⟨extInf, Or.inr rfl, rfl⟩

/-- (TT:571–574) The map `T(1) × 𝔻* → 𝒯(1)`, `([μ], z) ↦ ([μ], w^μ(z))`, is a bijection (the memoir: a real-analytic
isomorphism). -/
theorem TCurve_param_bijective :
    BijOn (fun q : T1 × ExtPlane => (q.1, wB (Quotient.out q.1 : LinfStarBall) q.2))
      (univ ×ˢ extDiscExterior) TCurve := by
  refine ⟨?_, ?_, ?_⟩
  · intro q hq
    exact ⟨q.2, hq.2, rfl⟩
  · intro q hq r hr he
    have hp := congrArg (fun q : T1 × ExtPlane => q.1) he
    change q.1 = r.1 at hp
    apply Prod.ext hp
    have hw := congrArg (fun q : T1 × ExtPlane => q.2) he
    dsimp at hw
    rw [hp] at hw
    exact (wB_bijective (Quotient.out r.1 : LinfStarBall)).injective hw
  · intro q hq
    obtain ⟨z, hz, he⟩ := hq
    exact ⟨(q.1, z), ⟨mem_univ _, hz⟩, Prod.ext rfl he⟩

end TakhtajanTeo
