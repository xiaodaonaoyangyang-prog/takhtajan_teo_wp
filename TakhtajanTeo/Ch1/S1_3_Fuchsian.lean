import TakhtajanTeo.Ch1.S1_2_Homogeneous
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure

/-!
# Chapter 1, §1.3 — Teichmüller spaces and Teichmüller curves of Fuchsian groups (TT:1006–1062)

* Fuchsian groups (discrete subgroups of `PSU(1,1)`), `L∞(𝔻*, Γ)`, `T(Γ)`, `Ω^{-1,1}(𝔻*, Γ)`
* the embedding `T(Γ) ↪ T(1)`, the Bers fiber space `𝓑𝓕(Γ)`, the quasi-Fuchsian groups `Γ^μ`
* fundamental domains, integrals over `Γ\𝔻*`, cofinite groups, the Weil–Petersson inner product at the origin
  of `T(Γ)`
* Lemma 1.9 (Patterson)

**Modelling.**
- A Fuchsian group is a discrete subgroup `Γ` of `SL(2, ℂ)` whose elements have the `SU(1,1)` form
  `[[a, b], [b̄, ā]]`. The group `PSU(1,1)` of the memoir is the image; `±1` act alike.
- Integrals over `Γ\𝔻*` are integrals over a measurable fundamental domain.

**Not stated here** (recorded):
- "The Weil–Petersson metric on `T(Γ)` is a Kähler metric" (TT:1052) is a classical result that the memoir quotes.
  It is used in §8, where the Weil–Petersson metric of `T(Γ)` is defined at every point. The statement is made
  there.
- The Teichmüller curve `𝒯(Γ)` (TT:1032), with fibers `Γ^μ\w^μ(𝔻*)`, is not used before §8.
-/

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal ComplexConjugate Classical Real Matrix

noncomputable section

namespace TakhtajanTeo

open LiZhongQC

/-- `SL(2, ℂ)`. -/
abbrev SL2C := Matrix.SpecialLinearGroup (Fin 2) ℂ

/-- The action of `g = [[a, b], [c, d]] ∈ SL(2, ℂ)` on `ℂ`: `z ↦ (a z + b)/(c z + d)` (junk `0` at the pole). -/
def mob (g : SL2C) (z : ℂ) : ℂ := (g 0 0 * z + g 0 1) / (g 1 0 * z + g 1 1)

/-- `g ∈ SU(1,1)`: `g = [[a, b], [b̄, ā]]` (with `|a|² - |b|² = det g = 1`). -/
def IsSU11 (g : SL2C) : Prop := g 1 0 = conj (g 0 1) ∧ g 1 1 = conj (g 0 0)

/-- A **Fuchsian group** (TT:1006): a discrete subgroup of `PSU(1,1)`, here a discrete subgroup of `SL(2, ℂ)`
contained in `SU(1,1)`. -/
def IsFuchsian (Γ : Subgroup SL2C) : Prop :=
  (∀ g ∈ Γ, IsSU11 g) ∧ DiscreteTopology Γ

/-- `L∞(𝔻*, Γ)` (TT:1009): bounded Beltrami differentials for `Γ`,
`μ ∘ γ · \overline{γ'}/γ' = μ` for all `γ ∈ Γ` (a.e. on `𝔻*`). -/
def LinfGamma (Γ : Subgroup SL2C) : Set LinfStar :=
  {μ | ∀ g ∈ Γ, ∀ᵐ z ∂(volume.restrict unitDiscExterior),
    μ (mob g z) * (conj (deriv (mob g) z) / deriv (mob g) z) = μ z}

/-- The relation of `T(1)` restricted to `L∞(𝔻*, Γ)₁ = L∞(𝔻*)₁ ∩ L∞(𝔻*, Γ)` (TT:1015–1021). -/
def teichSetoidGamma (Γ : Subgroup SL2C) : Setoid {μ : LinfStarBall // (μ : LinfStar) ∈ LinfGamma Γ} where
  r μ ν := teichSetoid μ.1 ν.1
  iseqv := ⟨fun μ => teichSetoid.iseqv.refl μ.1, fun h => teichSetoid.iseqv.symm h,
    fun h₁ h₂ => teichSetoid.iseqv.trans h₁ h₂⟩

/-- The **Teichmüller space of a Fuchsian group** `T(Γ) = L∞(𝔻*, Γ)₁/∼` (TT:1021). -/
def TGamma (Γ : Subgroup SL2C) : Type := Quotient (teichSetoidGamma Γ)

/-- The canonical embedding `T(Γ) ↪ T(1)` (TT:1030). -/
def TGamma.toT1 {Γ : Subgroup SL2C} : TGamma Γ → T1 :=
  Quotient.map' (fun μ => μ.1) (fun _ _ h => h)

/-- The injectivity part of the canonical embedding (TT:1030) follows directly
from restricting the same boundary equivalence relation. No discreteness is needed. -/
theorem TGamma.toT1_injective {Γ : Subgroup SL2C} :
    Function.Injective (TGamma.toT1 (Γ := Γ)) := by
  intro p q hpq
  induction p using Quotient.inductionOn with
  | h μ =>
    induction q using Quotient.inductionOn with
    | h ν =>
      apply Quotient.sound
      change teichSetoid μ.1 ν.1
      exact Quotient.exact hpq

/-- Before passing to Bers coordinates, the image of the canonical embedding
(TT:1030) consists exactly of classes with a group-invariant representative. -/
theorem TGamma.range_toT1 {Γ : Subgroup SL2C} :
    range (TGamma.toT1 (Γ := Γ)) =
      Phi '' {μ : LinfStarBall | (μ : LinfStar) ∈ LinfGamma Γ} := by
  ext p
  constructor
  · rintro ⟨q, rfl⟩
    induction q using Quotient.inductionOn with
    | h μ => exact ⟨μ.1, μ.2, rfl⟩
  · rintro ⟨μ, hμ, rfl⟩
    exact ⟨Quotient.mk (teichSetoidGamma Γ) ⟨μ, hμ⟩, rfl⟩

/-- (TT:1030) The canonical embedding `T(Γ) ↪ T(1)` is injective, and in Bers coordinates `β(T(Γ))` is the image of
`L∞(𝔻*, Γ)₁` under `β ∘ Φ`. (The memoir adds that the embedding is holomorphic and that `T(Γ)` is a complex
submanifold of `T(1)`; in Bers coordinates the latter is the content of this description of the image.) -/
theorem TGamma_embedding {Γ : Subgroup SL2C} (hΓ : IsFuchsian Γ) :
    Function.Injective (TGamma.toT1 (Γ := Γ)) ∧
      range (bers ∘ TGamma.toT1 (Γ := Γ)) = bersPhi '' (LinfStarBall ∩ LinfGamma Γ) := by
  refine ⟨TGamma.toT1_injective, ?_⟩
  ext φ
  constructor
  · rintro ⟨p, rfl⟩
    induction p using Quotient.inductionOn with
    | h μ =>
      exact ⟨(μ.1 : LinfStar), ⟨μ.1.property, μ.property⟩, (bers_Phi μ.1).symm⟩
  · rintro ⟨μ, ⟨hball, hμΓ⟩, rfl⟩
    exact ⟨Quotient.mk (teichSetoidGamma Γ) ⟨⟨μ, hball⟩, hμΓ⟩, bers_Phi ⟨μ, hball⟩⟩

/-- `Ω^{-1,1}(𝔻*, Γ) = Ω^{-1,1}(𝔻*) ∩ L∞(𝔻*, Γ)` (TT:1027), the tangent space at the origin of `T(Γ)`. -/
def harmonicGamma (Γ : Subgroup SL2C) : Set LinfStar := (harmonicBeltrami : Set LinfStar) ∩ LinfGamma Γ

/-- (TT:1030) `T(1)` is the Teichmüller space of the trivial group. -/
theorem TGamma_bot_toT1_bijective : Function.Bijective (TGamma.toT1 (Γ := ⊥)) := by
  constructor
  · exact TGamma.toT1_injective
  · intro p
    induction p using Quotient.inductionOn with
    | h μ =>
      have hμ : (μ : LinfStar) ∈ LinfGamma ⊥ := by
        intro g hg
        have hg' : g = 1 := Subgroup.mem_bot.mp hg
        subst g
        have hm : mob (1 : SL2C) = id := by
          funext z
          simp [mob]
        simp [hm]
      exact ⟨Quotient.mk (teichSetoidGamma ⊥) ⟨μ, hμ⟩, rfl⟩

/-- The Bers fiber space `𝓑𝓕(Γ)` (TT:1032): the inverse image of `T(Γ)` under `𝒯(1) → T(1)`. -/
def bersFiber (Γ : Subgroup SL2C) : Set (T1 × ExtPlane) :=
  TCurve ∩ {q | q.1 ∈ range (TGamma.toT1 (Γ := Γ))}

/-- `F` is a measurable fundamental domain of `Γ` in `𝔻*`.
- The translates `γ(F)`, `γ ∈ Γ`, cover `𝔻*` up to a null set.
- Two translates by elements with different actions meet in a null set. -/
def IsFundDomain (Γ : Subgroup SL2C) (F : Set ℂ) : Prop :=
  MeasurableSet F ∧ F ⊆ unitDiscExterior ∧
    (∀ᵐ z ∂(volume.restrict unitDiscExterior), ∃ g ∈ Γ, mob g z ∈ F) ∧
    ∀ g ∈ Γ, ∀ h ∈ Γ, mob g ≠ mob h → volume (mob g ⁻¹' F ∩ mob h ⁻¹' F ∩ unitDiscExterior) = 0

/-- A chosen fundamental domain (junk `∅` if none exists; every Fuchsian group has one). -/
def fundDomain (Γ : Subgroup SL2C) : Set ℂ := if h : ∃ F, IsFundDomain Γ F then h.choose else ∅

/-- The chosen fundamental domain is measurable in either branch of its
definition (TT:1032–1049). -/
theorem fundDomain_measurable (Γ : Subgroup SL2C) : MeasurableSet (fundDomain Γ) := by
  unfold fundDomain
  split_ifs with h
  · exact h.choose_spec.1
  · exact MeasurableSet.empty

/-- The chosen domain lies in the exterior (TT:1032–1049). -/
theorem fundDomain_subset (Γ : Subgroup SL2C) : fundDomain Γ ⊆ unitDiscExterior := by
  unfold fundDomain
  split_ifs with h
  · exact h.choose_spec.2.1
  · exact empty_subset _

/-- The integral `∬_{Γ\𝔻*} f d²z` over the orbifold `Γ\𝔻*`, computed on the chosen fundamental domain. -/
def quotientIntegral (Γ : Subgroup SL2C) (f : ℂ → ℂ) : ℂ := ∫ z in fundDomain Γ, f z

/-- For the trivial group the entire exterior is a fundamental domain
(TT:1030–1049). -/
theorem isFundDomain_bot : IsFundDomain (⊥ : Subgroup SL2C) unitDiscExterior := by
  have hmeas : MeasurableSet unitDiscExterior :=
    (isOpen_lt continuous_const continuous_norm).measurableSet
  refine ⟨hmeas, Subset.rfl, ?_, ?_⟩
  · filter_upwards [self_mem_ae_restrict hmeas] with z hz
    exact ⟨1, Subgroup.one_mem _, by simpa [mob] using hz⟩
  · intro g hg h hh hne
    have hg1 : g = 1 := Subgroup.mem_bot.mp hg
    have hh1 : h = 1 := Subgroup.mem_bot.mp hh
    exact (hne (by rw [hg1, hh1])).elim

/-- Any chosen fundamental domain of the trivial group agrees almost
everywhere with the full exterior (TT:1030–1049). -/
theorem fundDomain_bot_ae : fundDomain (⊥ : Subgroup SL2C) =ᵐ[volume] unitDiscExterior := by
  have hex : ∃ F, IsFundDomain (⊥ : Subgroup SL2C) F := ⟨_, isFundDomain_bot⟩
  have hF : IsFundDomain (⊥ : Subgroup SL2C) (fundDomain ⊥) := by
    simpa only [fundDomain, dif_pos hex] using hex.choose_spec
  have hae : ∀ᵐ z ∂(volume.restrict unitDiscExterior), z ∈ fundDomain (⊥ : Subgroup SL2C) := by
    filter_upwards [hF.2.2.1] with z hz
    obtain ⟨g, hg, hz⟩ := hz
    have hg1 : g = 1 := Subgroup.mem_bot.mp hg
    simpa [hg1, mob] using hz
  have hmeas : MeasurableSet unitDiscExterior :=
    (isOpen_lt continuous_const continuous_norm).measurableSet
  filter_upwards [(ae_restrict_iff' hmeas).mp hae] with z hz
  exact propext ⟨fun h => hF.2.1 h, hz⟩

/-- Quotient integration for the trivial group reduces to integration over
the exterior, independently of the chosen fundamental domain (TT:1030–1049). -/
theorem quotientIntegral_bot (f : ℂ → ℂ) :
    quotientIntegral (⊥ : Subgroup SL2C) f = ∫ z in unitDiscExterior, f z := by
  exact setIntegral_congr_set fundDomain_bot_ae

/-! ### Existence of a fundamental domain for a Fuchsian group acting on `𝔻*`

Instead of a Dirichlet domain (and its boundary geometry) we use a *strict* measurable fundamental set: the
points of `𝔻*` that are lexicographically minimal in their orbit for the key
`(1/(|z|²-1), Re z, Im z)`. Discreteness of `Γ` makes the minimum exist; the strict order makes each orbit
meet the set exactly once. -/

theorem fd_box_isCompact (C : ℝ) :
    IsCompact {g : SL2C | ∀ i j, ‖(g : Matrix (Fin 2) (Fin 2) ℂ) i j‖ ≤ C} := by
  have hemb : IsClosedEmbedding ((↑) : SL2C → Matrix (Fin 2) (Fin 2) ℂ) :=
    Matrix.SpecialLinearGroup.isClosedEmbedding_val
  refine (hemb.isEmbedding.isCompact_iff).mpr ?_
  have hbox : IsCompact {A : Matrix (Fin 2) (Fin 2) ℂ | ∀ i j, ‖A i j‖ ≤ C} := by
    have : {A : Matrix (Fin 2) (Fin 2) ℂ | ∀ i j, ‖A i j‖ ≤ C} =
        Set.pi univ fun i => Set.pi univ fun j => closedBall (0 : ℂ) C := by
      ext A
      constructor
      · intro h i _ j _
        simpa [mem_closedBall, dist_zero_right] using h i j
      · intro h i j
        simpa [mem_closedBall, dist_zero_right] using h i (mem_univ i) j (mem_univ j)
    rw [this]
    exact isCompact_univ_pi fun i => isCompact_univ_pi fun j => isCompact_closedBall _ _
  have himg : ((↑) : SL2C → Matrix (Fin 2) (Fin 2) ℂ) ''
      {g : SL2C | ∀ i j, ‖(g : Matrix (Fin 2) (Fin 2) ℂ) i j‖ ≤ C} =
      range ((↑) : SL2C → Matrix (Fin 2) (Fin 2) ℂ) ∩ {A | ∀ i j, ‖A i j‖ ≤ C} := by
    ext A
    constructor
    · rintro ⟨g, hg, rfl⟩
      exact ⟨⟨g, rfl⟩, hg⟩
    · rintro ⟨⟨g, rfl⟩, hA⟩
      exact ⟨g, hA, rfl⟩
  have hc : IsCompact (range ((↑) : SL2C → Matrix (Fin 2) (Fin 2) ℂ) ∩ {A : Matrix (Fin 2) (Fin 2) ℂ | ∀ i j, ‖A i j‖ ≤ C}) :=
    hbox.of_isClosed_subset (hemb.isClosed_range.inter hbox.isClosed) inter_subset_right
  exact himg ▸ hc

theorem fd_bounded_finite {Γ : Subgroup SL2C} [DiscreteTopology Γ] (C : ℝ) :
    {g : SL2C | g ∈ Γ ∧ ∀ i j, ‖(g : Matrix (Fin 2) (Fin 2) ℂ) i j‖ ≤ C}.Finite := by
  have hcl : IsClosed (Γ : Set SL2C) := Subgroup.isClosed_of_discreteTopology
  have hK := (fd_box_isCompact C).inter_left hcl
  have hd : IsDiscrete (Γ : Set SL2C) := isDiscrete_iff_discreteTopology.mpr (inferInstanceAs (DiscreteTopology Γ))
  exact hK.finite (hd.mono inter_subset_left)

theorem fd_countable {Γ : Subgroup SL2C} [DiscreteTopology Γ] : (Γ : Set SL2C).Countable := by
  have : (Γ : Set SL2C) ⊆ ⋃ n : ℕ, {g : SL2C | g ∈ Γ ∧ ∀ i j, ‖(g : Matrix (Fin 2) (Fin 2) ℂ) i j‖ ≤ n} := by
    intro g hg
    obtain ⟨n, hn⟩ := exists_nat_ge (∑ i, ∑ j, ‖(g : Matrix (Fin 2) (Fin 2) ℂ) i j‖)
    refine mem_iUnion.mpr ⟨n, hg, fun i j => ?_⟩
    refine le_trans ?_ hn
    calc ‖(g : Matrix (Fin 2) (Fin 2) ℂ) i j‖ ≤ ∑ j', ‖(g : Matrix (Fin 2) (Fin 2) ℂ) i j'‖ :=
          Finset.single_le_sum (f := fun j' => ‖(g : Matrix (Fin 2) (Fin 2) ℂ) i j'‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ j)
      _ ≤ ∑ i', ∑ j', ‖(g : Matrix (Fin 2) (Fin 2) ℂ) i' j'‖ :=
          Finset.single_le_sum (f := fun i' => ∑ j', ‖(g : Matrix (Fin 2) (Fin 2) ℂ) i' j'‖) (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ i)
  exact Set.Countable.mono this (Set.countable_iUnion fun n => (fd_bounded_finite (Γ := Γ) n).countable)

theorem fd_su11_det {g : SL2C} (hg : IsSU11 g) :
    ‖g 0 0‖ ^ 2 - ‖g 0 1‖ ^ 2 = 1 := by
  have hdet : g 0 0 * g 1 1 - g 0 1 * g 1 0 = 1 := by
    have := g.det_coe
    rwa [Matrix.det_fin_two] at this
  rw [hg.1, hg.2, Complex.mul_conj, Complex.mul_conj] at hdet
  have h := congrArg Complex.re hdet
  simp only [Complex.sub_re, Complex.ofReal_re, Complex.one_re, Complex.normSq_eq_norm_sq] at h
  simpa using h

/-- The `SU(1,1)` identity `|a z + b|² - |b̄ z + ā|² = |z|² - 1`. -/
theorem fd_su11_identity {g : SL2C} (hg : IsSU11 g) (z : ℂ) :
    ‖g 0 0 * z + g 0 1‖ ^ 2 = ‖g 1 0 * z + g 1 1‖ ^ 2 + (‖z‖ ^ 2 - 1) := by
  have h1 := fd_su11_det hg
  rw [hg.1, hg.2]
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.mul_re,
    Complex.mul_im, Complex.conj_re, Complex.conj_im] at h1 ⊢
  nlinarith [h1]

theorem fd_mob_norm {g : SL2C} (hg : IsSU11 g) {z : ℂ} (hz : 1 < ‖z‖)
    (hD : g 1 0 * z + g 1 1 ≠ 0) :
    ‖mob g z‖ ^ 2 - 1 = (‖z‖ ^ 2 - 1) / ‖g 1 0 * z + g 1 1‖ ^ 2 := by
  have hn : 0 < ‖g 1 0 * z + g 1 1‖ := norm_pos_iff.mpr hD
  unfold mob
  rw [norm_div, div_pow, fd_su11_identity hg z]
  field_simp
  ring

theorem fd_mob_exterior {g : SL2C} (hg : IsSU11 g) {z : ℂ} (hz : 1 < ‖z‖)
    (hD : g 1 0 * z + g 1 1 ≠ 0) : 1 < ‖mob g z‖ := by
  have h := fd_mob_norm hg hz hD
  have hn : 0 < ‖g 1 0 * z + g 1 1‖ := norm_pos_iff.mpr hD
  have hpos : 0 < (‖z‖ ^ 2 - 1) / ‖g 1 0 * z + g 1 1‖ ^ 2 := by
    apply div_pos _ (by positivity)
    nlinarith
  by_contra hcon
  have : ‖mob g z‖ ≤ 1 := not_lt.mp hcon
  nlinarith [norm_nonneg (mob g z)]

theorem fd_entries_bound {g : SL2C} (hg : IsSU11 g) {w : ℂ} (hw : 1 < ‖w‖) {δ : ℝ} (hδ : 0 < δ)
    (hD : g 1 0 * w + g 1 1 ≠ 0) (hs : δ ≤ ‖mob g w‖ ^ 2 - 1) :
    ∀ i j, ‖(g : Matrix (Fin 2) (Fin 2) ℂ) i j‖ ≤
      (√((‖w‖ ^ 2 - 1) / δ) + √((‖w‖ ^ 2 - 1) / δ + (‖w‖ ^ 2 - 1))) * (‖w‖ + 1) / (‖w‖ ^ 2 - 1) := by
  have hs0 : 0 < ‖w‖ ^ 2 - 1 := by nlinarith
  set s : ℝ := ‖w‖ ^ 2 - 1 with hsdef
  set B1 : ℝ := √(s / δ) with hB1
  set B2 : ℝ := √(s / δ + s) with hB2
  have hDn : 0 < ‖g 1 0 * w + g 1 1‖ := norm_pos_iff.mpr hD
  have hnorm := fd_mob_norm hg hw hD
  have hD2 : ‖g 1 0 * w + g 1 1‖ ^ 2 ≤ s / δ := by
    rw [hnorm] at hs
    rw [le_div_iff₀ hδ]
    have h2 : δ * ‖g 1 0 * w + g 1 1‖ ^ 2 ≤ s := by
      rw [le_div_iff₀ (by positivity)] at hs
      linarith
    linarith
  have hD1 : ‖g 1 0 * w + g 1 1‖ ≤ B1 := Real.le_sqrt_of_sq_le hD2
  have hN2 : ‖g 0 0 * w + g 0 1‖ ^ 2 ≤ s / δ + s := by
    rw [fd_su11_identity hg w]; linarith
  have hN1 : ‖g 0 0 * w + g 0 1‖ ≤ B2 := Real.le_sqrt_of_sq_le hN2
  have hB1n : 0 ≤ B1 := Real.sqrt_nonneg _
  have hB2n : 0 ≤ B2 := Real.sqrt_nonneg _
  have hww : w * conj w = ((‖w‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have hDc : g 1 0 * w + g 1 1 = conj (g 0 1) * w + conj (g 0 0) := by rw [hg.1, hg.2]
  have ha : g 0 0 * (s : ℂ) = (g 0 0 * w + g 0 1) * conj w - conj (g 1 0 * w + g 1 1) := by
    rw [hDc]; simp only [map_add, map_mul, Complex.conj_conj, hsdef]
    push_cast
    have := hww
    push_cast at this
    linear_combination (g 0 0) * (-this)
  have hb : g 0 1 * (s : ℂ) = conj (g 1 0 * w + g 1 1) * w - (g 0 0 * w + g 0 1) := by
    rw [hDc]; simp only [map_add, map_mul, Complex.conj_conj, hsdef]
    push_cast
    have := hww
    push_cast at this
    linear_combination (g 0 1) * (-this)
  have hw0 : 0 ≤ ‖w‖ := norm_nonneg _
  have hBa : ‖g 0 0‖ ≤ (B1 + B2) * (‖w‖ + 1) / s := by
    rw [le_div_iff₀ hs0]
    have := congrArg norm ha
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs0] at this
    have h2 : ‖(g 0 0 * w + g 0 1) * conj w - conj (g 1 0 * w + g 1 1)‖ ≤
        ‖g 0 0 * w + g 0 1‖ * ‖w‖ + ‖g 1 0 * w + g 1 1‖ := by
      refine (norm_sub_le _ _).trans ?_
      rw [norm_mul, Complex.norm_conj, Complex.norm_conj]
    nlinarith [mul_nonneg hB1n hw0, mul_nonneg hB2n hw0, mul_le_mul_of_nonneg_right hN1 hw0]
  have hBb : ‖g 0 1‖ ≤ (B1 + B2) * (‖w‖ + 1) / s := by
    rw [le_div_iff₀ hs0]
    have := congrArg norm hb
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs0] at this
    have h2 : ‖conj (g 1 0 * w + g 1 1) * w - (g 0 0 * w + g 0 1)‖ ≤
        ‖g 1 0 * w + g 1 1‖ * ‖w‖ + ‖g 0 0 * w + g 0 1‖ := by
      refine (norm_sub_le _ _).trans ?_
      rw [norm_mul, Complex.norm_conj]
    nlinarith [mul_nonneg hB1n hw0, mul_nonneg hB2n hw0, mul_le_mul_of_nonneg_right hD1 hw0]
  intro i j
  fin_cases i <;> fin_cases j
  · exact hBa
  · exact hBb
  · simpa [hg.1] using hBb
  · simpa [hg.2] using hBa

theorem fd_mul_entries (g h : SL2C) (i j : Fin 2) :
    ((g * h : SL2C) : Matrix (Fin 2) (Fin 2) ℂ) i j = g i 0 * h 0 j + g i 1 * h 1 j := by
  simp [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]

theorem fd_mob_mul {g h : SL2C} {z : ℂ} (hh : h 1 0 * z + h 1 1 ≠ 0)
    (hg : g 1 0 * mob h z + g 1 1 ≠ 0) :
    (g * h : SL2C) 1 0 * z + (g * h : SL2C) 1 1 = (g 1 0 * mob h z + g 1 1) * (h 1 0 * z + h 1 1) ∧
      mob (g * h) z = mob g (mob h z) := by
  have e : ∀ i j, ((g * h : SL2C) : Matrix (Fin 2) (Fin 2) ℂ) i j = g i 0 * h 0 j + g i 1 * h 1 j :=
    fd_mul_entries g h
  have hm : mob h z = (h 0 0 * z + h 0 1) / (h 1 0 * z + h 1 1) := rfl
  constructor
  · rw [e, e, hm]
    field_simp
    ring
  · unfold mob
    rw [e, e, e, e]
    rw [hm] at hg
    set P := h 0 0 * z + h 0 1 with hP
    set Q := h 1 0 * z + h 1 1 with hQ
    have h1 : g 0 0 * (P / Q) + g 0 1 = (g 0 0 * P + g 0 1 * Q) / Q := by field_simp
    have h2 : g 1 0 * (P / Q) + g 1 1 = (g 1 0 * P + g 1 1 * Q) / Q := by field_simp
    rw [h1, h2, div_div_div_cancel_right₀ hh]
    congr 1 <;> (rw [hP, hQ]; ring)

theorem fd_inv_entries (g : SL2C) :
    ((g⁻¹ : SL2C) : Matrix (Fin 2) (Fin 2) ℂ) 0 0 = g 1 1 ∧ ((g⁻¹ : SL2C) : Matrix (Fin 2) (Fin 2) ℂ) 0 1 = -g 0 1 ∧
      ((g⁻¹ : SL2C) : Matrix (Fin 2) (Fin 2) ℂ) 1 0 = -g 1 0 ∧ ((g⁻¹ : SL2C) : Matrix (Fin 2) (Fin 2) ℂ) 1 1 = g 0 0 := by
  simp [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]

theorem fd_not_both_zero (g : SL2C) (z : ℂ) :
    ¬ (g 0 0 * z + g 0 1 = 0 ∧ g 1 0 * z + g 1 1 = 0) := by
  rintro ⟨h1, h2⟩
  have hdet : g 0 0 * g 1 1 - g 0 1 * g 1 0 = 1 := by
    have := g.det_coe
    rwa [Matrix.det_fin_two] at this
  have hz : z = 0 := by
    have : z * (g 0 0 * g 1 1 - g 0 1 * g 1 0) = g 1 1 * (g 0 0 * z + g 0 1) - g 0 1 * (g 1 0 * z + g 1 1) := by
      ring
    rw [h1, h2, hdet] at this
    simpa using this
  subst hz
  have a1 : g 0 1 = 0 := by simpa using h1
  have a2 : g 1 1 = 0 := by simpa using h2
  rw [a1, a2] at hdet
  simp at hdet

/-- Two Möbius maps that agree at three points where both are finite coincide everywhere. -/
theorem fd_agree_finite {g h : SL2C} (hne : mob g ≠ mob h) :
    {z : ℂ | g 1 0 * z + g 1 1 ≠ 0 ∧ h 1 0 * z + h 1 1 ≠ 0 ∧ mob g z = mob h z}.Finite := by
  by_contra hinf
  obtain ⟨s, hs, hcard⟩ := (show Set.Infinite _ from hinf).exists_subset_card_eq 3
  obtain ⟨z1, z2, z3, h12, h13, h23, rfl⟩ := Finset.card_eq_three.mp hcard
  have key : ∀ z, z ∈ {z : ℂ | g 1 0 * z + g 1 1 ≠ 0 ∧ h 1 0 * z + h 1 1 ≠ 0 ∧ mob g z = mob h z} →
      (g 0 0 * z + g 0 1) * (h 1 0 * z + h 1 1) = (h 0 0 * z + h 0 1) * (g 1 0 * z + g 1 1) := by
    rintro z ⟨hg, hh, he⟩
    unfold mob at he
    rwa [div_eq_div_iff hg hh] at he
  have e1 := key z1 (hs (by simp))
  have e2 := key z2 (hs (by simp))
  have e3 := key z3 (hs (by simp))
  set A := g 0 0 * h 1 0 - h 0 0 * g 1 0
  set B := g 0 0 * h 1 1 + g 0 1 * h 1 0 - h 0 0 * g 1 1 - h 0 1 * g 1 0
  set C := g 0 1 * h 1 1 - h 0 1 * g 1 1
  have q : ∀ z, (g 0 0 * z + g 0 1) * (h 1 0 * z + h 1 1) - (h 0 0 * z + h 0 1) * (g 1 0 * z + g 1 1) =
      A * z ^ 2 + B * z + C := by intro z; simp only [A, B, C]; ring
  have q1 : A * z1 ^ 2 + B * z1 + C = 0 := by rw [← q]; linear_combination e1
  have q2 : A * z2 ^ 2 + B * z2 + C = 0 := by rw [← q]; linear_combination e2
  have q3 : A * z3 ^ 2 + B * z3 + C = 0 := by rw [← q]; linear_combination e3
  have d12 : z1 - z2 ≠ 0 := sub_ne_zero.mpr h12
  have d13 : z1 - z3 ≠ 0 := sub_ne_zero.mpr h13
  have d23 : z2 - z3 ≠ 0 := sub_ne_zero.mpr h23
  have l12 : A * (z1 + z2) + B = 0 := by
    have : (z1 - z2) * (A * (z1 + z2) + B) = 0 := by linear_combination q1 - q2
    exact (mul_eq_zero.mp this).resolve_left d12
  have l13 : A * (z1 + z3) + B = 0 := by
    have : (z1 - z3) * (A * (z1 + z3) + B) = 0 := by linear_combination q1 - q3
    exact (mul_eq_zero.mp this).resolve_left d13
  have hA : A = 0 := by
    have : A * (z2 - z3) = 0 := by linear_combination l12 - l13
    exact (mul_eq_zero.mp this).resolve_right d23
  have hB : B = 0 := by rw [hA] at l12; simpa using l12
  have hC : C = 0 := by rw [hA, hB] at q1; simpa using q1
  apply hne
  funext z
  have hq : (g 0 0 * z + g 0 1) * (h 1 0 * z + h 1 1) = (h 0 0 * z + h 0 1) * (g 1 0 * z + g 1 1) := by
    have := q z
    rw [hA, hB, hC] at this
    linear_combination this
  unfold mob
  by_cases hg : g 1 0 * z + g 1 1 = 0
  · have hnz : g 0 0 * z + g 0 1 ≠ 0 := fun h0 => fd_not_both_zero g z ⟨h0, hg⟩
    have hh : h 1 0 * z + h 1 1 = 0 := by
      rw [hg, mul_zero] at hq
      exact (mul_eq_zero.mp hq).resolve_left hnz
    rw [hg, hh]; simp
  · by_cases hh : h 1 0 * z + h 1 1 = 0
    · have hnz : h 0 0 * z + h 0 1 ≠ 0 := fun h0 => fd_not_both_zero h z ⟨h0, hh⟩
      rw [hh, mul_zero] at hq
      exact absurd ((mul_eq_zero.mp hq.symm).resolve_left hnz) hg
    · rw [div_eq_div_iff hg hh]; exact hq

/-- The lexicographic key `(1/(|z|²-1), Re z, Im z)` ordering the points of `𝔻*`. -/
def fdKey (z : ℂ) : ℝ ×ₗ ℝ ×ₗ ℝ := toLex ((‖z‖ ^ 2 - 1)⁻¹, toLex (z.re, z.im))

theorem fdKey_lt_iff (z w : ℂ) : fdKey z < fdKey w ↔
    ((‖z‖ ^ 2 - 1)⁻¹ < (‖w‖ ^ 2 - 1)⁻¹ ∨ ((‖z‖ ^ 2 - 1)⁻¹ = (‖w‖ ^ 2 - 1)⁻¹ ∧
      (z.re < w.re ∨ (z.re = w.re ∧ z.im < w.im)))) := by
  simp [fdKey, Prod.Lex.toLex_lt_toLex]

theorem fdKey_injective : Function.Injective fdKey := by
  intro z w h
  have h2 := congrArg (fun k => (ofLex (ofLex k).2)) h
  simp only [fdKey, ofLex_toLex] at h2
  exact Complex.ext (congrArg Prod.fst h2) (congrArg Prod.snd h2)

/-- A strict measurable fundamental set for `Γ` acting on `𝔻*`: the lexicographic minima of the orbits. -/
def fdSet (Γ : Subgroup SL2C) : Set ℂ :=
  {z | 1 < ‖z‖ ∧ ∀ g ∈ Γ, g 1 0 * z + g 1 1 ≠ 0 → mob g z = z ∨ fdKey z < fdKey (mob g z)}

theorem fd_measurable_mob (g : SL2C) : Measurable (mob g) := by
  unfold mob; fun_prop

theorem fd_measurableSet_key_lt (f f' : ℂ → ℂ) (hf : Measurable f) (hf' : Measurable f') :
    MeasurableSet {z | fdKey (f z) < fdKey (f' z)} := by
  simp only [fdKey_lt_iff]
  have m1 : Measurable fun z => ((‖f z‖ ^ 2 - 1)⁻¹ : ℝ) := by fun_prop
  have m2 : Measurable fun z => ((‖f' z‖ ^ 2 - 1)⁻¹ : ℝ) := by fun_prop
  have m3 : Measurable fun z => (f z).re := by fun_prop
  have m4 : Measurable fun z => (f' z).re := by fun_prop
  have m5 : Measurable fun z => (f z).im := by fun_prop
  have m6 : Measurable fun z => (f' z).im := by fun_prop
  refine (measurableSet_lt m1 m2).union ((measurableSet_eq_fun m1 m2).inter
    ((measurableSet_lt m3 m4).union ((measurableSet_eq_fun m3 m4).inter (measurableSet_lt m5 m6))))

theorem fdSet_measurable {Γ : Subgroup SL2C} (hc : (Γ : Set SL2C).Countable) : MeasurableSet (fdSet Γ) := by
  have : fdSet Γ = {z : ℂ | 1 < ‖z‖} ∩ ⋂ g ∈ (Γ : Set SL2C),
      ({z | g 1 0 * z + g 1 1 = 0} ∪ {z | mob g z = z} ∪ {z | fdKey z < fdKey (mob g z)}) := by
    ext z
    simp only [fdSet, mem_setOf_eq, mem_inter_iff, mem_iInter, mem_union, SetLike.mem_coe]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨h1, fun g hg => ?_⟩
      by_cases hD : g 1 0 * z + g 1 1 = 0
      · exact Or.inl (Or.inl hD)
      · rcases h2 g hg hD with h | h
        · exact Or.inl (Or.inr h)
        · exact Or.inr h
    · rintro ⟨h1, h2⟩
      refine ⟨h1, fun g hg hD => ?_⟩
      rcases h2 g hg with (h | h) | h
      · exact absurd h hD
      · exact Or.inl h
      · exact Or.inr h
  rw [this]
  refine (measurableSet_lt measurable_const (by fun_prop)).inter (MeasurableSet.biInter hc fun g _ => ?_)
  refine MeasurableSet.union (MeasurableSet.union ?_ ?_) ?_
  · exact measurableSet_eq_fun (by fun_prop) measurable_const
  · exact measurableSet_eq_fun (fd_measurable_mob g) measurable_id
  · exact fd_measurableSet_key_lt id (mob g) measurable_id (fd_measurable_mob g)

theorem fd_det (g : SL2C) : g 0 0 * g 1 1 - g 0 1 * g 1 0 = 1 := by
  have := g.det_coe
  rwa [Matrix.det_fin_two] at this

/-- The inverse of a genuine step is genuine and returns the point. -/
theorem fd_inv_step (g : SL2C) {z : ℂ} (hD : g 1 0 * z + g 1 1 ≠ 0) :
    (g⁻¹ : SL2C) 1 0 * mob g z + (g⁻¹ : SL2C) 1 1 ≠ 0 ∧ mob g⁻¹ (mob g z) = z := by
  obtain ⟨e00, e01, e10, e11⟩ := fd_inv_entries g
  have hdet := fd_det g
  have hm : mob g z = (g 0 0 * z + g 0 1) / (g 1 0 * z + g 1 1) := rfl
  have hden : (g⁻¹ : SL2C) 1 0 * mob g z + (g⁻¹ : SL2C) 1 1 = (g 1 0 * z + g 1 1)⁻¹ := by
    rw [e10, e11, hm]
    field_simp
    linear_combination hdet
  refine ⟨by rw [hden]; exact inv_ne_zero hD, ?_⟩
  show ((g⁻¹ : SL2C) 0 0 * mob g z + (g⁻¹ : SL2C) 0 1) /
    ((g⁻¹ : SL2C) 1 0 * mob g z + (g⁻¹ : SL2C) 1 1) = z
  rw [e00, e01, hden, hm]
  have hD2 : z * g 1 0 + g 1 1 ≠ 0 := by rwa [mul_comm]
  field_simp
  linear_combination z * hdet

theorem fd_unique {Γ : Subgroup SL2C} {z1 z2 : ℂ} (h1 : z1 ∈ fdSet Γ) (h2 : z2 ∈ fdSet Γ) {γ : SL2C}
    (hγ : γ ∈ Γ) (hD : γ 1 0 * z1 + γ 1 1 ≠ 0) (he : mob γ z1 = z2) : z1 = z2 := by
  by_contra hne
  have hlt : fdKey z1 < fdKey z2 := by
    rcases h1.2 γ hγ hD with h | h
    · exact absurd (h.symm.trans he) hne
    · rwa [he] at h
  obtain ⟨hD', hback⟩ := fd_inv_step γ hD
  rw [he] at hD' hback
  rcases h2.2 γ⁻¹ (Γ.inv_mem hγ) hD' with h | h
  · exact hne (hback.symm.trans h)
  · rw [hback] at h
    exact lt_asymm hlt h

theorem fd_orbit_min {Γ : Subgroup SL2C} (hΓ : IsFuchsian Γ) {z : ℂ} (hz : 1 < ‖z‖) :
    ∃ γ ∈ Γ, γ 1 0 * z + γ 1 1 ≠ 0 ∧ mob γ z ∈ fdSet Γ := by
  haveI : DiscreteTopology Γ := hΓ.2
  set δ : ℝ := ‖z‖ ^ 2 - 1 with hδdef
  have hδ : 0 < δ := by nlinarith
  set Q : Set SL2C := {g | g ∈ Γ ∧ g 1 0 * z + g 1 1 ≠ 0 ∧ δ ≤ ‖mob g z‖ ^ 2 - 1} with hQ
  have hfin : Q.Finite := by
    refine (fd_bounded_finite (Γ := Γ) ((√((‖z‖ ^ 2 - 1) / δ) + √((‖z‖ ^ 2 - 1) / δ + (‖z‖ ^ 2 - 1))) *
      (‖z‖ + 1) / (‖z‖ ^ 2 - 1))).subset (fun g hg => ?_)
    exact ⟨hg.1, fd_entries_bound (hΓ.1 g hg.1) hz hδ hg.2.1 hg.2.2⟩
  have hne : Q.Nonempty := by
    refine ⟨1, Γ.one_mem, ?_, ?_⟩
    · simp
    · simp [mob, hδdef]
  obtain ⟨γ, hγQ, hmin⟩ := Set.exists_min_image Q (fun g => fdKey (mob g z)) hfin hne
  refine ⟨γ, hγQ.1, hγQ.2.1, ?_, ?_⟩
  · exact fd_mob_exterior (hΓ.1 γ hγQ.1) hz hγQ.2.1
  · intro g' hg' hD'
    have hmul := fd_mob_mul hγQ.2.1 hD'
    set k : SL2C := g' * γ with hk
    have hkΓ : k ∈ Γ := Γ.mul_mem hg' hγQ.1
    have hkD : k 1 0 * z + k 1 1 ≠ 0 := by
      rw [hmul.1]; exact mul_ne_zero hD' hγQ.2.1
    by_cases hks : δ ≤ ‖mob k z‖ ^ 2 - 1
    · have hle := hmin k ⟨hkΓ, hkD, hks⟩
      rw [hmul.2] at hle
      rcases hle.eq_or_lt with h | h
      · exact Or.inl (fdKey_injective h).symm
      · exact Or.inr h
    · right
      rw [hmul.2] at hks
      have hw1 := fd_mob_exterior (hΓ.1 γ hγQ.1) hz hγQ.2.1
      have hw2 : 1 < ‖mob g' (mob γ z)‖ := fd_mob_exterior (hΓ.1 g' hg') hw1 hD'
      rw [fdKey_lt_iff]
      left
      have hpos : 0 < ‖mob g' (mob γ z)‖ ^ 2 - 1 := by nlinarith
      apply inv_strictAnti₀ hpos
      push_neg at hks
      linarith [hγQ.2.2]

/-- **Existence of a fundamental domain** for a Fuchsian group acting on `𝔻*`: the lexicographic orbit minima
form a measurable set meeting every orbit exactly once. -/
theorem fd_exists_isFundDomain {Γ : Subgroup SL2C} (hΓ : IsFuchsian Γ) : IsFundDomain Γ (fdSet Γ) := by
  haveI : DiscreteTopology Γ := hΓ.2
  have hext : (fdSet Γ) ⊆ unitDiscExterior := fun z hz => hz.1
  refine ⟨fdSet_measurable fd_countable, hext, ?_, ?_⟩
  · refine (ae_restrict_iff' (show MeasurableSet unitDiscExterior from
      (isOpen_lt continuous_const continuous_norm).measurableSet)).mpr (Eventually.of_forall fun z hz => ?_)
    obtain ⟨γ, hγ, _, hF⟩ := fd_orbit_min hΓ hz
    exact ⟨γ, hγ, hF⟩
  · intro g hg h hh hne
    refine measure_mono_null ?_ ((fd_agree_finite hne).measure_zero volume)
    rintro z ⟨⟨hz1, hz2⟩, hz3⟩
    have hz2' : mob h z ∈ fdSet Γ := hz2
    have hz1' : mob g z ∈ fdSet Γ := hz1
    have hDg : g 1 0 * z + g 1 1 ≠ 0 := by
      intro h0
      have : mob g z = 0 := by unfold mob; rw [h0]; simp
      have h1 := hz1'.1
      rw [this] at h1; norm_num at h1
    have hDh : h 1 0 * z + h 1 1 ≠ 0 := by
      intro h0
      have : mob h z = 0 := by unfold mob; rw [h0]; simp
      have h1 := hz2'.1
      rw [this] at h1; norm_num at h1
    refine ⟨hDg, hDh, ?_⟩
    obtain ⟨hDi, hback⟩ := fd_inv_step g hDg
    have hmul := fd_mob_mul (g := h) (h := g⁻¹) hDi (by rw [hback]; exact hDh)
    refine fd_unique hz1' hz2' (γ := h * g⁻¹) (Γ.mul_mem hh (Γ.inv_mem hg)) ?_ ?_
    · rw [hmul.1]; exact mul_ne_zero (by rw [hback]; exact hDh) hDi
    · rw [hmul.2, hback]

/-- The chosen fundamental domain of a Fuchsian group is a fundamental domain. -/
theorem isFundDomain_fundDomain {Γ : Subgroup SL2C} (hΓ : IsFuchsian Γ) :
    IsFundDomain Γ (fundDomain Γ) := by
  have hex : ∃ F, IsFundDomain Γ F := ⟨_, fd_exists_isFundDomain hΓ⟩
  simpa only [fundDomain, dif_pos hex] using hex.choose_spec

theorem fd_quad_zero {A B C z1 z2 z3 : ℂ} (h12 : z1 ≠ z2) (h13 : z1 ≠ z3) (h23 : z2 ≠ z3)
    (q1 : A * z1 ^ 2 + B * z1 + C = 0) (q2 : A * z2 ^ 2 + B * z2 + C = 0)
    (q3 : A * z3 ^ 2 + B * z3 + C = 0) : A = 0 ∧ B = 0 ∧ C = 0 := by
  have d12 : z1 - z2 ≠ 0 := sub_ne_zero.mpr h12
  have d13 : z1 - z3 ≠ 0 := sub_ne_zero.mpr h13
  have d23 : z2 - z3 ≠ 0 := sub_ne_zero.mpr h23
  have l12 : A * (z1 + z2) + B = 0 := by
    have : (z1 - z2) * (A * (z1 + z2) + B) = 0 := by linear_combination q1 - q2
    exact (mul_eq_zero.mp this).resolve_left d12
  have l13 : A * (z1 + z3) + B = 0 := by
    have : (z1 - z3) * (A * (z1 + z3) + B) = 0 := by linear_combination q1 - q3
    exact (mul_eq_zero.mp this).resolve_left d13
  have hA : A = 0 := by
    have : A * (z2 - z3) = 0 := by linear_combination l12 - l13
    exact (mul_eq_zero.mp this).resolve_right d23
  have hB : B = 0 := by rw [hA] at l12; simpa using l12
  exact ⟨hA, hB, by rw [hA, hB] at q1; simpa using q1⟩

theorem fd_denom_finite (g : SL2C) : {z : ℂ | g 1 0 * z + g 1 1 = 0}.Finite := by
  by_cases h : g 1 0 = 0
  · have : g 1 1 ≠ 0 := by
      intro h1
      have := fd_det g
      rw [h, h1] at this
      simp at this
    have : {z : ℂ | g 1 0 * z + g 1 1 = 0} = ∅ := by
      ext z; simp [h, this]
    rw [this]; exact Set.finite_empty
  · refine (Set.finite_singleton (-g 1 1 / g 1 0)).subset (fun z hz => ?_)
    have hz' : g 1 0 * z + g 1 1 = 0 := hz
    simp only [mem_singleton_iff]
    field_simp
    linear_combination hz'

/-- A Möbius map determines its matrix up to sign. -/
theorem fd_mob_eq {k l : SL2C} (h : mob k = mob l) : l = k ∨ l = -k := by
  set m : SL2C := l⁻¹ * k with hm
  have hS : {z : ℂ | k 1 0 * z + k 1 1 ≠ 0 ∧ l 1 0 * z + l 1 1 ≠ 0}.Infinite := by
    have hfin : {z : ℂ | k 1 0 * z + k 1 1 = 0 ∨ l 1 0 * z + l 1 1 = 0}.Finite :=
      (fd_denom_finite k).union (fd_denom_finite l)
    have : ({z : ℂ | k 1 0 * z + k 1 1 ≠ 0 ∧ l 1 0 * z + l 1 1 ≠ 0}) =
        Set.univ \ {z : ℂ | k 1 0 * z + k 1 1 = 0 ∨ l 1 0 * z + l 1 1 = 0} := by
      ext z; simp [not_or]
    rw [this]
    exact Set.infinite_univ.sdiff hfin
  have key : ∀ z, k 1 0 * z + k 1 1 ≠ 0 → l 1 0 * z + l 1 1 ≠ 0 →
      m 1 0 * z ^ 2 + (m 1 1 - m 0 0) * z + (-m 0 1) = 0 := by
    intro z hk hl
    have hkl : mob k z = mob l z := by rw [h]
    obtain ⟨hDi, hback⟩ := fd_inv_step l hl
    rw [← hkl] at hDi hback
    have hmul := fd_mob_mul (g := l⁻¹) (h := k) hk hDi
    have hmz : mob m z = z := by rw [hm, hmul.2, hback]
    have hDm : m 1 0 * z + m 1 1 ≠ 0 := by
      rw [hm, hmul.1]; exact mul_ne_zero hDi hk
    unfold mob at hmz
    rw [div_eq_iff hDm] at hmz
    linear_combination (-1 : ℂ) * hmz
  obtain ⟨s, hs, hcard⟩ := hS.exists_subset_card_eq 3
  obtain ⟨z1, z2, z3, h12, h13, h23, rfl⟩ := Finset.card_eq_three.mp hcard
  have p1 := key z1 (hs (by simp)).1 (hs (by simp)).2
  have p2 := key z2 (hs (by simp)).1 (hs (by simp)).2
  have p3 := key z3 (hs (by simp)).1 (hs (by simp)).2
  obtain ⟨c10, c11, c01⟩ := fd_quad_zero h12 h13 h23 p1 p2 p3
  have hm10 : m 1 0 = 0 := c10
  have hm01 : m 0 1 = 0 := by simpa using c01
  have hm11 : m 1 1 = m 0 0 := by linear_combination c11 + (0 : ℂ) * c10
  have hdet := fd_det m
  rw [hm10, hm01, hm11] at hdet
  have hsq : m 0 0 * m 0 0 = 1 := by linear_combination hdet
  have : m 0 0 = 1 ∨ m 0 0 = -1 := mul_self_eq_one_iff.mp hsq
  have hkm : k = l * m := by rw [hm]; group
  rcases this with h1 | h1
  · left
    have : m = 1 := by
      ext i j; fin_cases i <;> fin_cases j <;> simp [hm10, hm01, hm11, h1]
    rw [hkm, this, mul_one]
  · right
    have : m = -1 := by
      ext i j; fin_cases i <;> fin_cases j <;> simp [hm10, hm01, hm11, h1]
    rw [hkm, this]
    simp

theorem fd_mob_neg (g : SL2C) : mob (-g) = mob g := by
  funext z
  unfold mob
  simp only [Matrix.SpecialLinearGroup.coe_neg, Matrix.neg_apply, neg_mul]
  rw [← neg_add, ← neg_add, neg_div_neg_eq]

theorem fd_mob_differentiableAt (h : SL2C) {w : ℂ} (hD : h 1 0 * w + h 1 1 ≠ 0) :
    DifferentiableAt ℂ (mob h) w := by
  unfold mob
  exact ((differentiableAt_const _ |>.mul differentiableAt_id).add (differentiableAt_const _)).div
    ((differentiableAt_const _ |>.mul differentiableAt_id).add (differentiableAt_const _)) hD

theorem fd_lintegral_image (h : SL2C) {s : Set ℂ} (hs : MeasurableSet s)
    (hgen : ∀ w ∈ s, h 1 0 * w + h 1 1 ≠ 0) (hinj : InjOn (mob h) s) (φ : ℂ → ℝ≥0∞) :
    ∫⁻ z in mob h '' s, φ z =
      ∫⁻ w in s, ENNReal.ofReal (‖deriv (mob h) w‖ ^ 2) * φ (mob h w) := by
  rw [lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hs
    (f' := fun x => (ContinuousLinearMap.toSpanSingleton ℂ (deriv (mob h) x)).restrictScalars ℝ)
    (fun x hx => ((fd_mob_differentiableAt h (hgen x hx)).hasDerivAt.hasFDerivAt.restrictScalars ℝ).hasFDerivWithinAt)
    hinj φ]
  refine setLIntegral_congr_fun hs fun w _ => ?_
  simp only [det_restrictScalars_toSpanSingleton]
  rw [abs_of_nonneg (sq_nonneg _)]

theorem isSU11_inv {g : SL2C} (hg : IsSU11 g) : IsSU11 g⁻¹ := by
  obtain ⟨e00, e01, e10, e11⟩ := fd_inv_entries g
  refine ⟨?_, ?_⟩
  · rw [e10, e01, hg.1]; simp
  · rw [e11, e00, hg.2]; simp

theorem fd_measurableSet_gen (h : SL2C) : MeasurableSet {w : ℂ | h 1 0 * w + h 1 1 ≠ 0} :=
  (measurableSet_eq_fun (by fun_prop) measurable_const).compl

/-- Change of variables for the tile `{z ∈ 𝔻* | mob g z ∈ F}` of the action of `g`. -/
theorem fd_tile_lintegral {F : Set ℂ} (hFm : MeasurableSet F) (hFe : F ⊆ unitDiscExterior)
    (g : SL2C) (hg : IsSU11 g) (ψ : ℂ → ℝ≥0∞) :
    ∫⁻ z in {z : ℂ | 1 < ‖z‖ ∧ mob g z ∈ F}, ψ z =
      ∫⁻ w in F, ENNReal.ofReal (‖deriv (mob g⁻¹) w‖ ^ 2) * ψ (mob g⁻¹ w) := by
  set s : Set ℂ := F ∩ {w | (g⁻¹ : SL2C) 1 0 * w + (g⁻¹ : SL2C) 1 1 ≠ 0} with hs
  have hsm : MeasurableSet s := hFm.inter (fd_measurableSet_gen g⁻¹)
  have hgen : ∀ w ∈ s, (g⁻¹ : SL2C) 1 0 * w + (g⁻¹ : SL2C) 1 1 ≠ 0 := fun w hw => hw.2
  have hleft : ∀ w ∈ s, mob g (mob g⁻¹ w) = w ∧ (g : SL2C) 1 0 * mob g⁻¹ w + g 1 1 ≠ 0 := by
    intro w hw
    have := fd_inv_step g⁻¹ (hgen w hw)
    rw [inv_inv] at this
    exact ⟨this.2, this.1⟩
  have hinj : InjOn (mob g⁻¹) s := fun w1 h1 w2 h2 h => by
    rw [← (hleft w1 h1).1, ← (hleft w2 h2).1, h]
  have himg : mob g⁻¹ '' s = {z : ℂ | 1 < ‖z‖ ∧ mob g z ∈ F} := by
    ext z
    constructor
    · rintro ⟨w, hw, rfl⟩
      have hw1 : 1 < ‖w‖ := hFe hw.1
      refine ⟨?_, by rw [(hleft w hw).1]; exact hw.1⟩
      exact fd_mob_exterior (isSU11_inv hg) hw1 (hgen w hw)
    · rintro ⟨hz, hzF⟩
      have hDg : g 1 0 * z + g 1 1 ≠ 0 := by
        intro h0
        have : mob g z = 0 := by unfold mob; rw [h0]; simp
        have h1 := hFe hzF
        rw [this] at h1
        change 1 < ‖(0 : ℂ)‖ at h1
        norm_num at h1
      obtain ⟨hDi, hback⟩ := fd_inv_step g hDg
      exact ⟨mob g z, ⟨hzF, hDi⟩, hback⟩
  rw [← himg, fd_lintegral_image g⁻¹ hsm hgen hinj ψ]
  refine setLIntegral_congr ?_
  have hnull : volume {w : ℂ | (g⁻¹ : SL2C) 1 0 * w + (g⁻¹ : SL2C) 1 1 = 0} = 0 :=
    (fd_denom_finite g⁻¹).measure_zero volume
  have : ∀ᵐ w ∂volume, w ∉ {w : ℂ | (g⁻¹ : SL2C) 1 0 * w + (g⁻¹ : SL2C) 1 1 = 0} :=
    measure_eq_zero_iff_ae_notMem.mp hnull
  refine eventuallyEqSet_iff.mpr ?_
  filter_upwards [this] with w hw
  have hw' : (g⁻¹ : SL2C) 1 0 * w + (g⁻¹ : SL2C) 1 1 ≠ 0 := hw
  exact ⟨fun h => h.1, fun h => ⟨h, hw'⟩⟩

theorem fd_inv_neg (k : SL2C) : (-k)⁻¹ = -k⁻¹ := by
  refine inv_eq_of_mul_eq_one_right ?_
  ext i j
  simp [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_neg, Matrix.neg_mul,
    Matrix.mul_neg]

/-- **Unfolding over a fundamental domain** (lower integrals): the integral over `𝔻*` is the sum over the
distinct actions `a ∈ Γ/±1` of the integrals over `F` of the pulled-back density. -/
theorem fd_unfold {Γ : Subgroup SL2C} (hΓ : IsFuchsian Γ) {F : Set ℂ} (hF : IsFundDomain Γ F)
    (ψ : ℂ → ℝ≥0∞) :
    ∫⁻ w in unitDiscExterior, ψ w =
      ∑' a : (fun g : SL2C => mob g) '' (Γ : Set SL2C),
        ∫⁻ w in F, ENNReal.ofReal (‖deriv (a : ℂ → ℂ) w‖ ^ 2) * ψ ((a : ℂ → ℂ) w) := by
  classical
  haveI : DiscreteTopology Γ := hΓ.2
  set A := (fun g : SL2C => mob g) '' (Γ : Set SL2C) with hA
  haveI : Countable A := (fd_countable (Γ := Γ)).image _ |>.to_subtype
  have hext : MeasurableSet unitDiscExterior := (isOpen_lt continuous_const continuous_norm).measurableSet
  let S : A → Set ℂ := fun b => {z | 1 < ‖z‖ ∧ (b : ℂ → ℂ) z ∈ F}
  have hSm : ∀ b, MeasurableSet (S b) := by
    rintro ⟨_, g, hg, rfl⟩
    exact (measurableSet_lt measurable_const measurable_norm).inter ((fd_measurable_mob g) hF.1)
  have hcover : unitDiscExterior =ᵐ[volume] ⋃ b, S b := by
    refine eventuallyEqSet_iff.mpr ?_
    filter_upwards [(ae_restrict_iff' hext).mp hF.2.2.1] with z hz
    constructor
    · intro hz1
      obtain ⟨g, hg, hF'⟩ := hz hz1
      exact mem_iUnion.mpr ⟨⟨mob g, g, hg, rfl⟩, hz1, hF'⟩
    · intro h
      obtain ⟨b, hb⟩ := mem_iUnion.mp h
      exact hb.1
  have hdisj : Pairwise (Function.onFun (AEDisjoint volume) S) := by
    rintro ⟨_, g, hg, rfl⟩ ⟨_, h, hh, rfl⟩ hne
    have : mob g ≠ mob h := fun e => hne (Subtype.ext e)
    refine measure_mono_null (t := mob g ⁻¹' F ∩ mob h ⁻¹' F ∩ unitDiscExterior) ?_ (hF.2.2.2 g hg h hh this)
    intro z hz
    exact ⟨⟨hz.1.2, hz.2.2⟩, hz.1.1⟩
  let rep : A → SL2C := fun b => Classical.choose b.2
  have hrep : ∀ b : A, rep b ∈ Γ ∧ mob (rep b) = b.1 := fun b => Classical.choose_spec b.2
  let ι : A → A := fun b => ⟨mob (rep b)⁻¹, (rep b)⁻¹, Γ.inv_mem (hrep b).1, rfl⟩
  have hιι : Function.Involutive ι := by
    intro b
    apply Subtype.ext
    show mob (rep (ι b))⁻¹ = b.1
    have h1 : mob (rep b)⁻¹ = mob (rep (ι b)) := ((hrep (ι b)).2).symm
    rcases fd_mob_eq h1 with h | h
    · rw [h, inv_inv]; exact (hrep b).2
    · rw [h, fd_inv_neg, inv_inv, fd_mob_neg]; exact (hrep b).2
  let e : A ≃ A := hιι.toPerm
  calc ∫⁻ w in unitDiscExterior, ψ w = ∫⁻ w in ⋃ b, S b, ψ w := setLIntegral_congr hcover
    _ = ∑' b, ∫⁻ w in S b, ψ w :=
        lintegral_iUnion₀ (fun b => (hSm b).nullMeasurableSet) hdisj ψ
    _ = ∑' b : A, ∫⁻ w in F, ENNReal.ofReal (‖deriv ((ι b : A) : ℂ → ℂ) w‖ ^ 2) *
          ψ (((ι b : A) : ℂ → ℂ) w) := by
        refine tsum_congr fun b => ?_
        have hS : S b = {z : ℂ | 1 < ‖z‖ ∧ mob (rep b) z ∈ F} := by
          ext z; simp only [S, mem_setOf_eq, (hrep b).2]
        rw [hS]
        exact fd_tile_lintegral hF.1 hF.2.1 (rep b) (hΓ.1 _ (hrep b).1) ψ
    _ = ∑' a : A, ∫⁻ w in F, ENNReal.ofReal (‖deriv (a : ℂ → ℂ) w‖ ^ 2) * ψ ((a : ℂ → ℂ) w) :=
        e.tsum_eq (fun a : A => ∫⁻ w in F, ENNReal.ofReal (‖deriv (a : ℂ → ℂ) w‖ ^ 2) * ψ ((a : ℂ → ℂ) w))

private theorem fdq_integrable_sum_transfer {ι : Type*} [Countable ι]
    (μ ν : ι → Measure ℂ) (f : ℂ → ℂ)
    (hi : ∀ i, Integrable f (μ i) → Integrable f (ν i))
    (hn : ∀ i, (∫ x, ‖f x‖ ∂μ i) = ∫ x, ‖f x‖ ∂ν i)
    (h : Integrable f (Measure.sum μ)) : Integrable f (Measure.sum ν) := by
  obtain ⟨hparts, hsum⟩ := integrable_sum_measure_iff.mp h
  exact integrable_sum_measure (fun i => hi i (hparts i)) (hsum.congr hn)

/-- This comparison includes the nonintegrable case, where the Bochner
integrals are both totalized to zero. -/
theorem fdq_integral_sum_compare {ι : Type*} [Countable ι]
    (μ ν : ι → Measure ℂ) (f : ℂ → ℂ)
    (hi : ∀ i, Integrable f (μ i) ↔ Integrable f (ν i))
    (hn : ∀ i, (∫ x, ‖f x‖ ∂μ i) = ∫ x, ‖f x‖ ∂ν i)
    (hv : ∀ i, (∫ x, f x ∂μ i) = ∫ x, f x ∂ν i) :
    (∫ x, f x ∂Measure.sum μ) = ∫ x, f x ∂Measure.sum ν := by
  have hiff : Integrable f (Measure.sum μ) ↔ Integrable f (Measure.sum ν) :=
    ⟨fdq_integrable_sum_transfer μ ν f (fun i => (hi i).mp) hn,
      fdq_integrable_sum_transfer ν μ f (fun i => (hi i).mpr) (fun i => (hn i).symm)⟩
  by_cases h : Integrable f (Measure.sum μ)
  · rw [integral_sum_measure h, integral_sum_measure (hiff.mp h)]
    exact tsum_congr hv
  · rw [integral_undef h, integral_undef (mt hiff.mpr h)]

theorem fdq_mob_integral_image {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : SL2C) {s : Set ℂ} (hs : MeasurableSet s)
    (hD : ∀ w ∈ s, g 1 0 * w + g 1 1 ≠ 0) (f : ℂ → E) :
    (∫ u in mob g '' s, f u) = ∫ w in s, (‖deriv (mob g) w‖ ^ 2) • f (mob g w) := by
  have hinj : InjOn (mob g) s := by
    intro x hx y hy heq
    rw [← (fd_inv_step g (hD x hx)).2, ← (fd_inv_step g (hD y hy)).2, heq]
  rw [integral_image_eq_integral_abs_det_fderiv_smul volume hs
    (f' := fun w => (ContinuousLinearMap.toSpanSingleton ℂ (deriv (mob g) w)).restrictScalars ℝ)
    (fun w hw => ((fd_mob_differentiableAt g (hD w hw)).hasDerivAt.hasFDerivAt.restrictScalars
      ℝ).hasFDerivWithinAt) hinj f]
  apply setIntegral_congr_fun hs
  intro w hw
  simp only [det_restrictScalars_toSpanSingleton]
  rw [abs_of_nonneg (sq_nonneg ‖deriv (mob g) w‖)]

theorem fdq_mob_integrable_image {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : SL2C) {s : Set ℂ} (hs : MeasurableSet s)
    (hD : ∀ w ∈ s, g 1 0 * w + g 1 1 ≠ 0) (f : ℂ → E) :
    IntegrableOn f (mob g '' s) ↔
      IntegrableOn (fun w => (‖deriv (mob g) w‖ ^ 2) • f (mob g w)) s := by
  have hinj : InjOn (mob g) s := by
    intro x hx y hy heq
    rw [← (fd_inv_step g (hD x hx)).2, ← (fd_inv_step g (hD y hy)).2, heq]
  rw [integrableOn_image_iff_integrableOn_abs_det_fderiv_smul volume hs
    (f' := fun w => (ContinuousLinearMap.toSpanSingleton ℂ (deriv (mob g) w)).restrictScalars ℝ)
    (fun w hw => ((fd_mob_differentiableAt g (hD w hw)).hasDerivAt.hasFDerivAt.restrictScalars
      ℝ).hasFDerivWithinAt) hinj f]
  apply integrableOn_congr_fun _ hs
  intro w hw
  simp only [det_restrictScalars_toSpanSingleton]
  rw [abs_of_nonneg (sq_nonneg ‖deriv (mob g) w‖)]

theorem fdq_denom_ne_of_image_exterior (g : SL2C) {w : ℂ}
    (hw : mob g w ∈ unitDiscExterior) : g 1 0 * w + g 1 1 ≠ 0 := by
  intro hzero
  have heq : mob g w = 0 := by simp [mob, hzero]
  norm_num [heq, unitDiscExterior] at hw

theorem fdq_tile_image (g : SL2C) {F G : Set ℂ}
    (hF : F ⊆ unitDiscExterior) (hG : G ⊆ unitDiscExterior) :
    mob g '' (F ∩ mob g ⁻¹' G) = G ∩ mob g⁻¹ ⁻¹' F := by
  ext y
  constructor
  · rintro ⟨w, ⟨hwF, hwG⟩, rfl⟩
    have hback := (fd_inv_step g (fdq_denom_ne_of_image_exterior g (hG hwG))).2
    exact ⟨hwG, by simpa only [mem_preimage, hback] using hwF⟩
  · rintro ⟨hyG, hyF⟩
    have hback := (fd_inv_step g⁻¹ (fdq_denom_ne_of_image_exterior g⁻¹ (hF hyF))).2
    rw [inv_inv] at hback
    exact ⟨mob g⁻¹ y, ⟨hyF, by simpa only [mem_preimage, hback] using hyG⟩, hback⟩

theorem fdq_inv_action_congr {g h : SL2C} (heq : mob g = mob h) : mob g⁻¹ = mob h⁻¹ := by
  rcases fd_mob_eq heq with rfl | rfl
  · rfl
  · rw [fd_inv_neg, fd_mob_neg]

theorem fdq_partition_cover {ι : Type*} {Γ : Subgroup SL2C} {F G : Set ℂ}
    (hFe : F ⊆ unitDiscExterior) (hG : IsFundDomain Γ G) (r : ι → SL2C)
    (hsurj : ∀ g ∈ Γ, ∃ i, mob (r i) = mob g) :
    F =ᵐ[volume] ⋃ i, F ∩ mob (r i) ⁻¹' G := by
  have hext : MeasurableSet unitDiscExterior :=
    (isOpen_lt continuous_const continuous_norm).measurableSet
  apply eventuallyEqSet_iff.mpr
  filter_upwards [(ae_restrict_iff' hext).mp hG.2.2.1] with w hw
  constructor
  · intro hwF
    obtain ⟨g, hg, hgw⟩ := hw (hFe hwF)
    obtain ⟨i, hi⟩ := hsurj g hg
    exact mem_iUnion.mpr ⟨i, hwF, by simpa only [mem_preimage, hi] using hgw⟩
  · intro hwU
    obtain ⟨i, hi⟩ := mem_iUnion.mp hwU
    exact hi.1

theorem fdq_partition_disjoint {ι : Type*} {Γ : Subgroup SL2C} {F G : Set ℂ}
    (hFe : F ⊆ unitDiscExterior) (hG : IsFundDomain Γ G) (r : ι → SL2C)
    (hr : ∀ i, r i ∈ Γ) (hinj : Function.Injective (fun i => mob (r i))) :
    Pairwise (Function.onFun (AEDisjoint volume) (fun i => F ∩ mob (r i) ⁻¹' G)) := by
  intro i j hij
  have hne : mob (r i) ≠ mob (r j) := fun heq => hij (hinj heq)
  apply measure_mono_null (t := mob (r i) ⁻¹' G ∩ mob (r j) ⁻¹' G ∩ unitDiscExterior)
    _ (hG.2.2.2 (r i) (hr i) (r j) (hr j) hne)
  intro w hw
  exact ⟨⟨hw.1.2, hw.2.2⟩, hFe hw.1.1⟩

theorem fdq_partition_measure {ι : Type*} [Countable ι] {Γ : Subgroup SL2C} {F G : Set ℂ}
    (hFm : MeasurableSet F) (hFe : F ⊆ unitDiscExterior) (hG : IsFundDomain Γ G)
    (r : ι → SL2C) (hr : ∀ i, r i ∈ Γ)
    (hsurj : ∀ g ∈ Γ, ∃ i, mob (r i) = mob g)
    (hinj : Function.Injective (fun i => mob (r i))) :
    volume.restrict F = Measure.sum (fun i => volume.restrict (F ∩ mob (r i) ⁻¹' G)) := by
  exact (Measure.restrict_congr_set (fdq_partition_cover hFe hG r hsurj)).trans
    (Measure.restrict_iUnion_ae (fdq_partition_disjoint hFe hG r hr hinj)
      (fun i => (hFm.inter ((fd_measurable_mob (r i)) hG.1)).nullMeasurableSet))

theorem fdq_tile_compare {F G : Set ℂ}
    (hFm : MeasurableSet F) (hGm : MeasurableSet G)
    (hFe : F ⊆ unitDiscExterior) (hGe : G ⊆ unitDiscExterior)
    {g : SL2C} (f : ℂ → ℂ)
    (hinv : ∀ᵐ w ∂(volume.restrict unitDiscExterior),
      (‖deriv (mob g) w‖ ^ 2) • f (mob g w) = f w) :
    (IntegrableOn f (G ∩ mob g⁻¹ ⁻¹' F) ↔ IntegrableOn f (F ∩ mob g ⁻¹' G)) ∧
    (∫ w in G ∩ mob g⁻¹ ⁻¹' F, f w) = (∫ w in F ∩ mob g ⁻¹' G, f w) ∧
    (∫ w in G ∩ mob g⁻¹ ⁻¹' F, ‖f w‖) = (∫ w in F ∩ mob g ⁻¹' G, ‖f w‖) := by
  have hs : MeasurableSet (F ∩ mob g ⁻¹' G) := hFm.inter ((fd_measurable_mob g) hGm)
  have hD : ∀ w ∈ F ∩ mob g ⁻¹' G, g 1 0 * w + g 1 1 ≠ 0 :=
    fun w hw => fdq_denom_ne_of_image_exterior g (hGe hw.2)
  have heq : (fun w => (‖deriv (mob g) w‖ ^ 2) • f (mob g w)) =ᵐ[
      volume.restrict (F ∩ mob g ⁻¹' G)] f :=
    ae_restrict_of_ae_restrict_of_subset (fun w hw => hFe hw.1) hinv
  have hnorm : (fun w => (‖deriv (mob g) w‖ ^ 2) • ‖f (mob g w)‖) =ᵐ[
      volume.restrict (F ∩ mob g ⁻¹' G)] (fun w => ‖f w‖) := by
    filter_upwards [heq] with w hw
    have hn := congrArg norm hw
    simpa only [norm_smul, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg ‖deriv (mob g) w‖),
      smul_eq_mul] using hn
  rw [← fdq_tile_image g hFe hGe]
  exact ⟨(fdq_mob_integrable_image g hs hD f).trans (integrableOn_congr_fun_ae heq),
    (fdq_mob_integral_image g hs hD f).trans (integral_congr_ae heq),
    (fdq_mob_integral_image g hs hD (fun w => ‖f w‖)).trans (integral_congr_ae hnorm)⟩

theorem fdq_integral_independent {Γ : Subgroup SL2C} (hΓ : IsFuchsian Γ)
    {F G : Set ℂ} (hF : IsFundDomain Γ F) (hG : IsFundDomain Γ G)
    (f : ℂ → ℂ)
    (hinv : ∀ g ∈ Γ, ∀ᵐ w ∂(volume.restrict unitDiscExterior),
      (‖deriv (mob g) w‖ ^ 2) • f (mob g w) = f w) :
    (∫ w in F, f w) = ∫ w in G, f w := by
  classical
  haveI : DiscreteTopology Γ := hΓ.2
  let A := (fun g : SL2C => mob g) '' (Γ : Set SL2C)
  haveI : Countable A := (fd_countable (Γ := Γ)).image _ |>.to_subtype
  let r : A → SL2C := fun a => Classical.choose a.property
  have hr : ∀ a : A, r a ∈ Γ ∧ mob (r a) = a.val :=
    fun a => Classical.choose_spec a.property
  have hi : Function.Injective (fun a : A => mob (r a)) := by
    intro a b hab
    apply Subtype.ext
    exact (hr a).2.symm.trans (hab.trans (hr b).2)
  have ho : ∀ g ∈ Γ, ∃ a : A, mob (r a) = mob g := by
    intro g hg
    exact ⟨⟨mob g, g, hg, rfl⟩, (hr ⟨mob g, g, hg, rfl⟩).2⟩
  have hii : Function.Injective (fun a : A => mob (r a)⁻¹) := by
    intro a b hab
    apply hi
    simpa only [inv_inv] using fdq_inv_action_congr hab
  have hoi : ∀ g ∈ Γ, ∃ a : A, mob (r a)⁻¹ = mob g := by
    intro g hg
    obtain ⟨a, ha⟩ := ho g⁻¹ (Γ.inv_mem hg)
    exact ⟨a, by simpa only [inv_inv] using fdq_inv_action_congr ha⟩
  have hμ := fdq_partition_measure hF.1 hF.2.1 hG r (fun a => (hr a).1) ho hi
  have hν := fdq_partition_measure hG.1 hG.2.1 hF
    (fun a : A => (r a)⁻¹) (fun a => Γ.inv_mem (hr a).1) hoi hii
  change (∫ w, f w ∂volume.restrict F) = ∫ w, f w ∂volume.restrict G
  rw [hμ, hν]
  apply fdq_integral_sum_compare _ _ f
  · intro a
    exact (fdq_tile_compare hF.1 hG.1 hF.2.1 hG.2.1 f (hinv (r a) (hr a).1)).1.symm
  · intro a
    exact (fdq_tile_compare hF.1 hG.1 hF.2.1 hG.2.1 f (hinv (r a) (hr a).1)).2.2.symm
  · intro a
    exact (fdq_tile_compare hF.1 hG.1 hF.2.1 hG.2.1 f (hinv (r a) (hr a).1)).2.1.symm

/-- Every Fuchsian group has a fundamental domain, and for `Γ`-invariant integrands (`f ∘ γ · |γ'|² = f`) the integral
over `Γ\𝔻*` does not depend on the fundamental domain. -/
theorem quotientIntegral_spec {Γ : Subgroup SL2C} (hΓ : IsFuchsian Γ) :
    (∃ F, IsFundDomain Γ F) ∧
      ∀ (f : ℂ → ℂ) (F : Set ℂ), IsFundDomain Γ F →
        (∀ g ∈ Γ, ∀ᵐ z ∂(volume.restrict unitDiscExterior), f (mob g z) * ‖deriv (mob g) z‖ ^ 2 = f z) →
        ∫ z in F, f z = quotientIntegral Γ f := by
  refine ⟨⟨fundDomain Γ, isFundDomain_fundDomain hΓ⟩, ?_⟩
  intro f F hF hinv
  apply fdq_integral_independent hΓ hF (isFundDomain_fundDomain hΓ) f
  intro g hg
  filter_upwards [hinv g hg] with w hw
  simpa only [Complex.real_smul, Complex.ofReal_pow, mul_comm] using hw

/-- The hyperbolic area `A(Γ\𝔻*) = ∬_{Γ\𝔻*} ρ(z) d²z` (TT:1046). -/
def hypArea (Γ : Subgroup SL2C) : ℝ≥0∞ := ∫⁻ z in fundDomain Γ, ENNReal.ofReal (rho z)

/-- `Γ` is of finite type (cofinite) (TT:1046): `Γ\𝔻*` has finite hyperbolic area. -/
def IsCofinite (Γ : Subgroup SL2C) : Prop := IsFuchsian Γ ∧ hypArea Γ < ∞

/-- Cofiniteness makes the hyperbolic density integrable on the chosen
fundamental domain (TT:1046). -/
theorem rho_integrableOn_fundDomain {Γ : Subgroup SL2C} (hΓ : IsCofinite Γ) :
    IntegrableOn rho (fundDomain Γ) := by
  have hm : Measurable rho := by unfold rho; fun_prop
  have hn : ∀ z, 0 ≤ rho z := fun z => div_nonneg (by norm_num) (sq_nonneg _)
  refine ⟨hm.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_norm]
  simpa only [hypArea, Real.norm_eq_abs, abs_of_nonneg (hn _)] using hΓ.2

/-- The Weil–Petersson inner product at the origin of `T(Γ)` (TT:1049):
`⟨μ, ν⟩_WP = ∬_{Γ\𝔻*} μ ν̄ ρ(z) d²z` for `μ, ν ∈ Ω^{-1,1}(𝔻*, Γ)`. -/
def wpInnerGamma (Γ : Subgroup SL2C) (μ ν : LinfStar) : ℂ :=
  quotientIntegral Γ fun z => μ z * conj (ν z) * rho z

/-- The Weil–Petersson integrand is absolutely integrable for every pair of
bounded Beltrami differentials when the group is cofinite (TT:1046–1049). -/
theorem wpInnerGamma_integrable {Γ : Subgroup SL2C} (hΓ : IsCofinite Γ) (μ ν : LinfStar) :
    IntegrableOn (fun z => μ z * conj (ν z) * rho z) (fundDomain Γ) := by
  have hle : volume.restrict (fundDomain Γ) ≤ volume.restrict unitDiscExterior :=
    Measure.restrict_mono_set volume (fundDomain_subset Γ)
  have hμ : MemLp μ ∞ (volume.restrict (fundDomain Γ)) :=
    MemLp.mono_measure hle (Lp.memLp μ)
  have hν : MemLp (fun z => conj (ν z)) ∞ (volume.restrict (fundDomain Γ)) :=
    (MemLp.mono_measure hle (Lp.memLp ν)).star
  have hρ : IntegrableOn (fun z => (rho z : ℂ)) (fundDomain Γ) :=
    (rho_integrableOn_fundDomain hΓ).ofReal
  have hi := (hρ.mul_of_top_right hν).mul_of_top_right hμ
  exact hi.congr (Filter.Eventually.of_forall fun z => by simp only [Pi.mul_apply, mul_assoc])

/-- The conjugate-symmetry part of the Weil–Petersson pairing (TT:1049) follows
from the real density and commutation of conjugation with the integral. -/
theorem wpInnerGamma_conj_symm (Γ : Subgroup SL2C) (μ ν : LinfStar) :
    wpInnerGamma Γ ν μ = conj (wpInnerGamma Γ μ ν) := by
  unfold wpInnerGamma quotientIntegral
  rw [← integral_conj]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun z => by
    simp only [map_mul, starRingEnd_self_apply, conj_ofReal]
    ring

/-- Additivity in the first variable of the cofinite Weil–Petersson pairing
(TT:1049). Absolute integrability is supplied explicitly. -/
theorem wpInnerGamma_add_left {Γ : Subgroup SL2C} (hΓ : IsCofinite Γ)
    (μ ν κ : LinfStar) :
    wpInnerGamma Γ (μ + ν) κ = wpInnerGamma Γ μ κ + wpInnerGamma Γ ν κ := by
  have he : (fun z => (μ + ν) z * conj (κ z) * rho z) =ᵐ[volume.restrict (fundDomain Γ)]
      (fun z => μ z * conj (κ z) * rho z + ν z * conj (κ z) * rho z) := by
    filter_upwards [ae_restrict_of_ae_restrict_of_subset (fundDomain_subset Γ)
      (Lp.coeFn_add μ ν)] with z hz
    simp only [hz, Pi.add_apply, add_mul]
  unfold wpInnerGamma quotientIntegral
  exact (integral_congr_ae he).trans
    (integral_add (wpInnerGamma_integrable hΓ μ κ) (wpInnerGamma_integrable hΓ ν κ))

/-- Complex homogeneity in the first variable of the pairing (TT:1049). -/
theorem wpInnerGamma_smul_left (Γ : Subgroup SL2C) (a : ℂ) (μ ν : LinfStar) :
    wpInnerGamma Γ (a • μ) ν = a * wpInnerGamma Γ μ ν := by
  have he : (fun z => (a • μ) z * conj (ν z) * rho z) =ᵐ[volume.restrict (fundDomain Γ)]
      (fun z => a * (μ z * conj (ν z) * rho z)) := by
    filter_upwards [ae_restrict_of_ae_restrict_of_subset (fundDomain_subset Γ)
      (Lp.coeFn_smul a μ)] with z hz
    simp only [hz, Pi.smul_apply, smul_eq_mul, mul_assoc]
  unfold wpInnerGamma quotientIntegral
  exact (integral_congr_ae he).trans (integral_const_mul a _)

/-- Additivity in the second variable of the cofinite pairing (TT:1049). -/
theorem wpInnerGamma_add_right {Γ : Subgroup SL2C} (hΓ : IsCofinite Γ)
    (μ ν κ : LinfStar) :
    wpInnerGamma Γ μ (ν + κ) = wpInnerGamma Γ μ ν + wpInnerGamma Γ μ κ := by
  rw [wpInnerGamma_conj_symm Γ (ν + κ) μ, wpInnerGamma_add_left hΓ ν κ μ, map_add,
    ← wpInnerGamma_conj_symm Γ ν μ, ← wpInnerGamma_conj_symm Γ κ μ]

/-- Conjugate homogeneity in the second variable (TT:1049). -/
theorem wpInnerGamma_smul_right (Γ : Subgroup SL2C) (a : ℂ) (μ ν : LinfStar) :
    wpInnerGamma Γ μ (a • ν) = conj a * wpInnerGamma Γ μ ν := by
  rw [wpInnerGamma_conj_symm Γ (a • ν) μ, wpInnerGamma_smul_left Γ a ν μ,
    map_mul, ← wpInnerGamma_conj_symm Γ ν μ]

/-- The diagonal Weil–Petersson pairing is the integral of the real,
nonnegative density `|μ|² ρ` (TT:1049). -/
theorem wpInnerGamma_self_eq (Γ : Subgroup SL2C) (μ : LinfStar) :
    wpInnerGamma Γ μ μ = ((∫ z in fundDomain Γ, ‖μ z‖ ^ 2 * rho z : ℝ) : ℂ) := by
  unfold wpInnerGamma quotientIntegral
  rw [← integral_complex_ofReal]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun z => by
    simp only [Complex.mul_conj', Complex.ofReal_mul, Complex.ofReal_pow]

/-- Nonnegativity of the diagonal pairing (TT:1049). Strict positivity still
requires the fundamental-domain and harmonicity arguments. -/
theorem wpInnerGamma_self_nonneg (Γ : Subgroup SL2C) (μ : LinfStar) :
    0 ≤ (wpInnerGamma Γ μ μ).re := by
  rw [wpInnerGamma_self_eq, ofReal_re]
  apply integral_nonneg
  intro z
  exact mul_nonneg (sq_nonneg _) (div_nonneg (by norm_num) (sq_nonneg _))

/-- The diagonal pairing has zero imaginary part (TT:1049). -/
theorem wpInnerGamma_self_im (Γ : Subgroup SL2C) (μ : LinfStar) :
    (wpInnerGamma Γ μ μ).im = 0 := by
  rw [wpInnerGamma_self_eq, ofReal_im]

-- `harmonicGamma_finiteDimensional` moved to `TakhtajanTeo.Ch1.S13Cusp` (2026-10-29, Program G).

/-- The diagonal pairing vanishes exactly when the coefficient vanishes
almost everywhere on the fundamental domain (TT:1049). This separates the
integral argument from the remaining automorphic propagation argument. -/
theorem wpInnerGamma_self_eq_zero_iff {Γ : Subgroup SL2C} (hΓ : IsCofinite Γ) (μ : LinfStar) :
    wpInnerGamma Γ μ μ = 0 ↔ ∀ᵐ z ∂(volume.restrict (fundDomain Γ)), μ z = 0 := by
  have hn : ∀ z, 0 ≤ ‖μ z‖ ^ 2 * rho z := fun z =>
    mul_nonneg (sq_nonneg _) (div_nonneg (by norm_num) (sq_nonneg _))
  have hi : IntegrableOn (fun z => ‖μ z‖ ^ 2 * rho z) (fundDomain Γ) := by
    have h := (wpInnerGamma_integrable hΓ μ μ).re
    exact h.congr (Filter.Eventually.of_forall fun z => by
      change (μ z * conj (μ z) * (rho z : ℂ)).re = ‖μ z‖ ^ 2 * rho z
      simp only [Complex.mul_conj', ← Complex.ofReal_pow, ← Complex.ofReal_mul,
        Complex.ofReal_re])
  rw [wpInnerGamma_self_eq, Complex.ofReal_eq_zero,
    integral_eq_zero_iff_of_nonneg hn hi]
  constructor
  · intro h
    filter_upwards [h, self_mem_ae_restrict (fundDomain_measurable Γ)] with z hz hzF
    have hzE : 1 < ‖z‖ := fundDomain_subset Γ hzF
    have hp : 0 < rho z := by
      apply div_pos (by norm_num)
      apply sq_pos_of_ne_zero
      intro he
      nlinarith
    have hs : ‖μ z‖ ^ 2 = 0 := (mul_eq_zero.mp hz).resolve_right (ne_of_gt hp)
    apply norm_eq_zero.mp
    nlinarith [norm_nonneg (μ z)]
  · intro h
    filter_upwards [h] with z hz
    simp [hz]

/-- Strict positivity reduces to nonvanishing on the fundamental domain
(TT:1049); no unfinished harmonic or fundamental-domain theorem is used. -/
theorem wpInnerGamma_self_pos_iff {Γ : Subgroup SL2C} (hΓ : IsCofinite Γ) (μ : LinfStar) :
    0 < (wpInnerGamma Γ μ μ).re ↔
      ¬ (∀ᵐ z ∂(volume.restrict (fundDomain Γ)), μ z = 0) := by
  rw [← wpInnerGamma_self_eq_zero_iff hΓ μ]
  have hn := wpInnerGamma_self_nonneg Γ μ
  have hi := wpInnerGamma_self_im Γ μ
  constructor
  · intro hp he
    simpa [he] using hp
  · intro hne
    apply lt_of_le_of_ne hn
    intro he
    apply hne
    apply Complex.ext
    · exact he.symm
    · exact hi

theorem fdq_mob_deriv_ne_zero (g : SL2C) {w : ℂ}
    (hD : g 1 0 * w + g 1 1 ≠ 0) : deriv (mob g) w ≠ 0 := by
  have hd := hasDerivAt_mobius (a := g 0 0) (b := g 0 1) hD
  rw [fd_det g] at hd
  have hd' : deriv (mob g) w = 1 / (g 1 0 * w + g 1 1) ^ 2 := hd.deriv
  rw [hd']
  exact one_div_ne_zero (pow_ne_zero 2 hD)

theorem fdq_invariant_zero_on_tile {Γ : Subgroup SL2C} {μ : LinfStar}
    (hμ : μ ∈ LinfGamma Γ)
    (hzero : ∀ᵐ w ∂(volume.restrict (fundDomain Γ)), μ w = 0)
    {g : SL2C} (hg : g ∈ Γ) :
    ∀ᵐ w ∂(volume.restrict (fundDomain Γ)), μ (mob g w) = 0 := by
  have hD : ∀ᵐ w : ℂ ∂volume, g 1 0 * w + g 1 1 ≠ 0 :=
    measure_eq_zero_iff_ae_notMem.mp ((fd_denom_finite g).measure_zero volume)
  filter_upwards [hzero, ae_restrict_of_ae hD,
    ae_restrict_of_ae_restrict_of_subset (fundDomain_subset Γ) (hμ g hg)] with w hw hd hinv
  have hd' := fdq_mob_deriv_ne_zero g hd
  have hc : conj (deriv (mob g) w) ≠ 0 := by
    intro heq
    apply hd'
    simpa using congrArg conj heq
  exact (mul_eq_zero.mp (hinv.trans hw)).resolve_right (div_ne_zero hc hd')

/-- Invariance propagates a.e. vanishing from the fundamental domain to the
whole exterior. This holds for every invariant L∞ class, not only harmonic ones. -/
theorem fdq_invariant_eq_zero {Γ : Subgroup SL2C} (hΓ : IsFuchsian Γ)
    {μ : LinfStar} (hμ : μ ∈ LinfGamma Γ)
    (hzero : ∀ᵐ w ∂(volume.restrict (fundDomain Γ)), μ w = 0) : μ = 0 := by
  have hmass : (∫⁻ w in unitDiscExterior, ENNReal.ofReal ‖μ w‖) = 0 := by
    rw [fd_unfold hΓ (isFundDomain_fundDomain hΓ)]
    apply ENNReal.tsum_eq_zero.mpr
    rintro ⟨_, g, hg, rfl⟩
    calc _ = ∫⁻ w in fundDomain Γ, (0 : ℝ≥0∞) := by
          apply lintegral_congr_ae
          filter_upwards [fdq_invariant_zero_on_tile hμ hzero hg] with w hw
          simp only [hw, norm_zero, ENNReal.ofReal_zero, mul_zero]
      _ = 0 := by simp
  have hm : AEMeasurable (fun w => ENNReal.ofReal ‖μ w‖)
      (volume.restrict unitDiscExterior) :=
    (Lp.memLp μ).aestronglyMeasurable.norm.aemeasurable.ennreal_ofReal
  have hnorm := (lintegral_eq_zero_iff' hm).mp hmass
  apply Lp.ext
  filter_upwards [hnorm, Lp.coeFn_zero (E := ℂ) (p := ∞)
    (μ := volume.restrict unitDiscExterior)] with w hw hz
  apply Eq.trans _ hz.symm
  apply norm_eq_zero.mp
  exact le_antisymm (ENNReal.ofReal_eq_zero.mp hw) (norm_nonneg _)

/-- (TT:1046) For a cofinite group the Weil–Petersson product is a Hermitian inner product on
`Ω^{-1,1}(𝔻*, Γ)`: conjugate-symmetric and positive definite. -/
theorem wpInnerGamma_hermitian {Γ : Subgroup SL2C} (hΓ : IsCofinite Γ) :
    (∀ μ ∈ harmonicGamma Γ, ∀ ν ∈ harmonicGamma Γ, wpInnerGamma Γ ν μ = conj (wpInnerGamma Γ μ ν)) ∧
      ∀ μ ∈ harmonicGamma Γ, μ ≠ 0 → 0 < (wpInnerGamma Γ μ μ).re := by
  refine ⟨fun μ _ ν _ => wpInnerGamma_conj_symm Γ μ ν, ?_⟩
  intro μ hμ hne
  apply (wpInnerGamma_self_pos_iff hΓ μ).mpr
  intro hzero
  exact hne (fdq_invariant_eq_zero hΓ.1 hμ.2 hzero)

/-- `𝔻*_r = {z ∈ 𝔻* : |z| ≥ r}` (TT:1062). -/
def discExteriorR (r : ℝ) : Set ℂ := {z | z ∈ unitDiscExterior ∧ r ≤ ‖z‖}

-- `lemma_1_9` moved to `TakhtajanTeo.Ch1.S19Rep` (2026-10-29, Program G).

/-! ### Quasi-Fuchsian conjugation: coefficient transport and sphere action -/

theorem qf_mob_exterior_iff {g : SL2C} (hg : IsSU11 g) {z : ℂ}
    (hD : g 1 0 * z + g 1 1 ≠ 0) :
    mob g z ∈ unitDiscExterior ↔ z ∈ unitDiscExterior := by
  constructor
  · intro hz
    have hi := fd_inv_step g hD
    have hh := fd_mob_exterior (isSU11_inv hg) hz hi.1
    change 1 < ‖z‖
    simpa only [hi.2] using hh
  · intro hz
    exact fd_mob_exterior hg hz hD

/-- Zero extension preserves the automorphy equation on the entire plane,
with the coordinate pole excluded only as a null set. -/
theorem qf_extB_invariant {Γ : Subgroup SL2C} (hΓ : IsFuchsian Γ)
    {μ : LinfStar} (hμ : μ ∈ LinfGamma Γ) {g : SL2C} (hg : g ∈ Γ) :
    ∀ᵐ z ∂volume, extB μ (mob g z) *
      (conj (deriv (mob g) z) / deriv (mob g) z) = extB μ z := by
  have hext : MeasurableSet unitDiscExterior :=
    (isOpen_lt continuous_const continuous_norm).measurableSet
  filter_upwards [(ae_restrict_iff' hext).mp (hμ g hg),
    compl_mem_ae_iff.mpr ((fd_denom_finite g).measure_zero volume)] with z hz hD
  have hDz : g 1 0 * z + g 1 1 ≠ 0 := hD
  by_cases he : z ∈ unitDiscExterior
  · have hm := (qf_mob_exterior_iff (hΓ.1 g hg) hDz).mpr he
    simpa only [extB, indicator_of_mem he, indicator_of_mem hm] using hz he
  · have hm := mt (qf_mob_exterior_iff (hΓ.1 g hg) hDz).mp he
    simp only [extB, indicator_of_notMem he, indicator_of_notMem hm, zero_mul]

theorem qf_mobius_maps_exterior {g : SL2C} (hg : IsSU11 g) :
    MapsTo (mobiusExt (g 0 0) (g 0 1) (g 1 0) (g 1 1))
      extDiscExterior extDiscExterior := by
  intro p hp
  rcases hp with ⟨z, hz, rfl⟩ | hp
  · by_cases hd : g 1 0 * z + g 1 1 = 0
    · rw [mobiusExt_coe_of_eq_zero hd]
      exact Or.inr rfl
    · rw [mobiusExt_coe hd]
      exact Or.inl ⟨mob g z, fd_mob_exterior hg hz hd, rfl⟩
  · have hp' : p = extInf := hp
    subst p
    by_cases hc : g 1 0 = 0
    · rw [mobiusExt_infty_of_eq hc]
      exact Or.inr rfl
    · rw [mobiusExt_infty_of_ne hc]
      refine Or.inl ⟨g 0 0 / g 1 0, ?_, rfl⟩
      change 1 < ‖g 0 0 / g 1 0‖
      rw [norm_div, lt_div_iff₀ (norm_pos_iff.mpr hc), one_mul]
      have hh := fd_su11_det hg
      have he : ‖g 1 0‖ = ‖g 0 1‖ := by rw [hg.1, norm_conj]
      rw [he]
      nlinarith [norm_nonneg (g 0 0), norm_nonneg (g 0 1)]

theorem qf_mobius_inv (g : SL2C) (p : ExtPlane) :
    mobiusExt (g⁻¹ 0 0) (g⁻¹ 0 1) (g⁻¹ 1 0) (g⁻¹ 1 1)
      (mobiusExt (g 0 0) (g 0 1) (g 1 0) (g 1 1) p) = p := by
  obtain ⟨h00, h01, h10, h11⟩ := fd_inv_entries g
  rw [h00, h01, h10, h11]
  exact mobiusExt_inv_apply (by rw [fd_det]; exact one_ne_zero) p

theorem qf_mobius_image_exterior {g : SL2C} (hg : IsSU11 g) :
    mobiusExt (g 0 0) (g 0 1) (g 1 0) (g 1 1) '' extDiscExterior =
      extDiscExterior := by
  apply Subset.antisymm (qf_mobius_maps_exterior hg).image_subset
  intro p hp
  refine ⟨mobiusExt (g⁻¹ 0 0) (g⁻¹ 0 1) (g⁻¹ 1 0) (g⁻¹ 1 1) p,
    qf_mobius_maps_exterior (isSU11_inv hg) hp, ?_⟩
  simpa only [inv_inv] using qf_mobius_inv g⁻¹ p

theorem qf_mob_ae_pullback (g : SL2C) {P : ℂ → Prop}
    (hP : ∀ᵐ z ∂volume, P z) : ∀ᵐ z ∂volume, P (mob g z) := by
  let U : Set ℂ := {z | g 1 0 * z + g 1 1 ≠ 0}
  have hU : IsOpen U := isOpen_ne_fun (by fun_prop) continuous_const
  have hconf : IsConformalOnto (mob g) U (mob g '' U) := by
    refine ⟨fun z hz => (fd_mob_differentiableAt g hz).differentiableWithinAt, ?_, rfl⟩
    intro x hx y hy he
    rw [← (fd_inv_step g hx).2, ← (fd_inv_step g hy).2, he]
  have hP' : ∀ᵐ z ∂volume.restrict univ, P z := by simpa using hP
  have hh := s23_c2_ae_pullback (isKQC_one_of_conformal hU hconf) (subset_univ _) hP'
  filter_upwards [(ae_restrict_iff' hU.measurableSet).mp hh,
    compl_mem_ae_iff.mpr ((fd_denom_finite g).measure_zero volume)] with z hz hp
  exact hz hp

/-- The actual plane solution composed with a group element has the same
Beltrami coefficient; this is the analytic input to the conjugation argument. -/
theorem qf_solution_comp_dilatation {Γ : Subgroup SL2C} (hΓ : IsFuchsian Γ)
    {μ : LinfStar} (hμ : μ ∈ LinfGamma Γ) {g : SL2C} (hg : g ∈ Γ)
    {W : ℂ → ℂ} (hW : IsNormalizedSolution W (extB μ)) :
    ∀ᵐ z ∂volume, complexDilatation (W ∘ mob g) z = extB μ z := by
  filter_upwards [qf_mob_ae_pullback g hW.2.2.2.2, qf_extB_invariant hΓ hμ hg,
    compl_mem_ae_iff.mpr ((fd_denom_finite g).measure_zero volume)] with z hsol hinv hp
  have hD : g 1 0 * z + g 1 1 ≠ 0 := hp
  have hcomp := bg2_d_dil_mobius W (fd_det g) hD
  change complexDilatation (W ∘ mob g) z =
    complexDilatation W (mob g z) *
      ((g 1 0 * z + g 1 1) ^ 2 / conj ((g 1 0 * z + g 1 1) ^ 2)) at hcomp
  rw [hcomp, hsol]
  have hd := hasDerivAt_mobius (a := g 0 0) (b := g 0 1) hD
  rw [fd_det g] at hd
  have hd' : deriv (mob g) z = 1 / (g 1 0 * z + g 1 1) ^ 2 := hd.deriv
  rw [hd', map_div₀, map_one] at hinv
  simpa only [one_div, div_inv_eq_mul, div_eq_mul_inv, one_mul, inv_inv, mul_comm] using hinv

theorem qf_complex_pole_iff {γ : SL2C} (hc : γ 1 0 ≠ 0) (z : ℂ) :
    γ 1 0 * z + γ 1 1 = 0 ↔ z = -(γ 1 1 / γ 1 0) := by
  constructor
  · intro h
    field_simp
    linear_combination h
  · intro h
    rw [h]
    field_simp
    ring

theorem qf_complex_mobius_eq {γ : SL2C} (hc : γ 1 0 ≠ 0) {z : ℂ}
    (hz : z ≠ -(γ 1 1 / γ 1 0)) :
    mobiusFn (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1) z =
      γ 0 0 / γ 1 0 + -(γ 1 0 ^ 2)⁻¹ * (z + γ 1 1 / γ 1 0)⁻¹ := by
  have hdet := fd_det γ
  have hden : γ 1 0 * z + γ 1 1 ≠ 0 := fun h => hz ((qf_complex_pole_iff hc z).1 h)
  have hzr : z + γ 1 1 / γ 1 0 = (γ 1 0 * z + γ 1 1) / γ 1 0 := by
    field_simp
  have hden' : z * γ 1 0 + γ 1 1 ≠ 0 := by rwa [mul_comm]
  rw [mobiusFn, hzr, inv_div]
  field_simp
  linear_combination -hdet


/-- Complex-matrix version of LiZhongQC's `k24_mob_core`. The affine and pole
cases use plane-solution uniqueness. In the pole case the inversion conjugate
is a plane homeomorphism, and its punctured QC structure extends across the
puncture. The sphere relation is subsequently recovered by continuity. -/
theorem qf_complex_mob_core {f g τ : ℂ → ℂ} {K : ℝ} (hf : IsKQC f univ K) (hfs : f '' univ = univ) (hf0 : f 0 = 0)
    (γ : SL2C)
    (hd : ∀ᵐ z, complexDilatation (f ∘ mobiusFn (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1)) z = τ z)
    (hg : IsNormalizedSolution g τ) :
    ∃ A B C D : ℂ, A * D - B * C ≠ 0 ∧
      ∀ z : ℂ, f (mobiusFn (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1) z) = mobiusFn A B C D (g z) := by
  have hdetR : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
    have h := Matrix.SpecialLinearGroup.det_coe γ
    rwa [Matrix.det_fin_two] at h
  rcases eq_or_ne (γ 1 0) 0 with hc | hc
  · -- the affine case
    have hdet1 := hdetR
    rw [hc, mul_zero, sub_zero] at hdet1
    have h00 : (γ 0 0 : ℂ) ≠ 0 := by
      rintro h
      rw [h, zero_mul] at hdet1
      exact zero_ne_one hdet1
    have h11 : (γ 1 1 : ℂ) ≠ 0 := by
      rintro h
      rw [h, mul_zero] at hdet1
      exact zero_ne_one hdet1
    have hT : mobiusFn (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1) =
        fun u => (u - (-(γ 0 1 : ℂ) / γ 0 0)) / ((γ 1 1 : ℂ) / γ 0 0) := by
      funext u
      simp only [mobiusFn, hc, zero_mul, zero_add]
      field_simp
      ring
    have hTc : IsConformalOnto (mobiusFn (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1)) univ univ := by
      rw [hT]
      exact nxE_affine_isConformalOnto (div_ne_zero h11 h00)
    have hG := thm7_1_comp (isKQC_one_of_conformal isOpen_univ hTc) hf (subset_univ _)
    have hs : (f ∘ mobiusFn (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1)) '' univ = univ := by
      rw [image_comp, hTc.2.2, hfs]
    have hN := k24_normalize hg hG hs hd
    set G := f ∘ mobiusFn (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1) with hGdef
    have hΔ : G 1 - G 0 ≠ 0 := fun h =>
      one_ne_zero (hG.2.2.1.2.1 (mem_univ _) (mem_univ _) (sub_eq_zero.1 h))
    refine ⟨G 1 - G 0, G 0, 0, 1, by simpa using hΔ, fun z => ?_⟩
    show G z = ((G 1 - G 0) * g z + G 0) / (0 * g z + 1)
    rw [hN z, zero_mul, zero_add, div_one, mul_div_cancel₀ _ hΔ, sub_add_cancel]
  · -- the pole case, with the pole itself
    have hs := hfs
    have hc' : (γ 1 0 : ℂ) ≠ 0 := hc
    obtain ⟨p, hp⟩ : ∃ p : ℂ, p = (γ 0 0 : ℂ) / γ 1 0 := ⟨_, rfl⟩
    obtain ⟨q, hq'⟩ : ∃ q : ℂ, q = -((γ 1 0 : ℂ) ^ 2)⁻¹ := ⟨_, rfl⟩
    obtain ⟨r, hr⟩ : ∃ r : ℂ, r = (γ 1 1 : ℂ) / γ 1 0 := ⟨_, rfl⟩
    have hq : q ≠ 0 := by
      rw [hq']
      exact neg_ne_zero.mpr (inv_ne_zero (pow_ne_zero 2 hc'))
    have hM : ∀ z : ℂ, z ≠ -r → mobiusFn (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1) z = p + q * (z + r)⁻¹ := by
      intro z hz
      subst hp hq' hr
      exact qf_complex_mobius_eq hc hz
    have hpole : ∀ z : ℂ, (γ 1 0 : ℂ) * z + γ 1 1 ≠ 0 ↔ z ≠ -r := by
      intro z
      rw [hr]
      exact not_congr (qf_complex_pole_iff hc z)
    obtain ⟨G, hG⟩ : ∃ G : ℂ → ℂ, G = fun z => (f (p + q * (z + r)⁻¹) - f p)⁻¹ := ⟨_, rfl⟩
    have hGh : IsHomeomorphOnto G univ univ := hG ▸ k24_m1_isHomeomorphOnto hf hs p q r hq
    have hGK : IsKQC G univ K := b4_isKQC_univ_of_punctured hGh (hG ▸ k24_m1_isKQC hf p q r hq)
    have hfc : Continuous f := continuousOn_univ.1 hf.2.2.1.1
    have hfi : Function.Injective f := fun a b hab => hf.2.2.1.2.1 (mem_univ a) (mem_univ b) hab
    have hne : ∀ z : ℂ, z ≠ -r → f (mobiusFn (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1) z) - f p ≠ 0 := by
      intro z hz h
      have h1 := hfi (sub_eq_zero.1 h)
      rw [hM z hz, add_eq_left, mul_eq_zero, inv_eq_zero] at h1
      rcases h1 with h0 | h0
      · exact hq h0
      · exact hz (eq_neg_of_add_eq_zero_left h0)
    have hGd : ∀ᵐ z, complexDilatation G z = τ z := by
      filter_upwards [hd, compl_mem_ae_iff.mpr (measure_singleton (-r))] with z h1 h2
      have hz : z ≠ -r := h2
      rw [← h1]
      have heq : EqOn G ((fun w => (w - f p)⁻¹) ∘ (f ∘ mobiusFn (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1))) {-r}ᶜ := by
        intro w hw
        simp only [hG, Function.comp_apply, hM w hw]
      rw [abR_t_complexDilatation_congr isOpen_compl_singleton heq h2]
      have hden : (γ 1 0 : ℂ) * z + γ 1 1 ≠ 0 := (hpole z).2 hz
      have hMc : ContinuousAt (mobiusFn (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1)) z := by
        unfold mobiusFn
        exact ((continuousAt_const.mul continuousAt_id).add continuousAt_const).div
          ((continuousAt_const.mul continuousAt_id).add continuousAt_const) hden
      refine s23_dilatation_comp_left (k := fun u => f p + u⁻¹) (hfc.continuousAt.comp hMc) ?_ ?_ ?_
      · exact (differentiableAt_id.sub (differentiableAt_const _)).inv (hne z hz)
      · exact (differentiableAt_const _).add (differentiableAt_id.inv (inv_ne_zero (hne z hz)))
      · exact Eventually.of_forall fun w => by
          simp only [inv_inv]
          ring
    have hnorm : ∀ z, g z = (G z - G 0) / (G 1 - G 0) := k24_normalize hg hGK hGh.2.2.1 hGd
    have hΔ : G 1 - G 0 ≠ 0 := fun h =>
      one_ne_zero (hGh.2.1 (mem_univ _) (mem_univ _) (sub_eq_zero.1 h))
    have hGg : ∀ z, (G 1 - G 0) * g z + G 0 = G z := fun z => by
      rw [hnorm z]
      field_simp
      ring
    refine ⟨f p * (G 1 - G 0), f p * G 0 + 1, G 1 - G 0, G 0, ?_, fun z => ?_⟩
    · intro h
      apply hΔ
      linear_combination -h
    · by_cases hz' : z = -r
      · -- the pole: both sides are Lean's `0`
        have hden : (γ 1 0 : ℂ) * z + γ 1 1 = 0 := by
          by_contra h
          exact ((hpole z).1 h) hz'
        have hGr : G z = 0 := by
          rw [hG]
          show (f (p + q * (z + r)⁻¹) - f p)⁻¹ = 0
          rw [hz', neg_add_cancel, inv_zero, mul_zero, add_zero, sub_self, inv_zero]
        rw [mobiusFn, hden, div_zero, hf0, mobiusFn, hGg z, hGr, div_zero]
      · have hGz : G z = (f (mobiusFn (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1) z) - f p)⁻¹ := by
          simp only [hG, hM z hz']
        have hnum : f p * (G 1 - G 0) * g z + (f p * G 0 + 1) = f p * ((G 1 - G 0) * g z + G 0) + 1 := by
          ring
        show f (mobiusFn (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1) z) =
          (f p * (G 1 - G 0) * g z + (f p * G 0 + 1)) / ((G 1 - G 0) * g z + G 0)
        rw [hnum, hGg z, hGz]
        have := hne z hz'
        field_simp
        ring



theorem qf_solution_sphere_intertwine {Γ : Subgroup SL2C} (hΓ : IsFuchsian Γ)
    {μ : LinfStar} (hμ : μ ∈ LinfGamma Γ) {g : SL2C} (hg : g ∈ Γ)
    {W : ℂ → ℂ} (hW : IsNormalizedSolution W (extB μ)) :
    ∃ A : ExtPlane → ExtPlane, IsMobius A ∧ ∀ p : ExtPlane,
      OnePoint.map W (mobiusExt (g 0 0) (g 0 1) (g 1 0) (g 1 1) p) =
        A (OnePoint.map W p) := by
  obtain ⟨K, hK⟩ := hW.1
  obtain ⟨e, he⟩ := t1_homeomorph hK hW.2.1
  obtain ⟨a, b, c, d, hdet, hrel⟩ := qf_complex_mob_core hK hW.2.1 hW.2.2.1 g
    (qf_solution_comp_dilatation hΓ hμ hg hW) hW
  refine ⟨mobiusExt a b c d, ⟨a, b, c, d, hdet, rfl⟩, ?_⟩
  intro p
  exact k24_ext_relation e he (by rw [fd_det]; exact one_ne_zero) hdet (fun z _ => hrel z) p

theorem qf_wB_intertwine {Γ : Subgroup SL2C} (hΓ : IsFuchsian Γ)
    {μ : LinfStar} (hμ : μ ∈ LinfStarBall) (hμΓ : μ ∈ LinfGamma Γ)
    {g : SL2C} (hg : g ∈ Γ) :
    ∃ M : ExtPlane → ExtPlane, IsMobius M ∧ ∀ p : ExtPlane,
      M (wB μ p) = wB μ (mobiusExt (g 0 0) (g 0 1) (g 1 0) (g 1 1) p) := by
  obtain ⟨N, hN, W, hW, hfin, hinf, -⟩ := (wB_spec hμ).1
  have hrep : ∀ p : ExtPlane, wB μ p = N (OnePoint.map W p) := by
    intro p
    induction p using OnePoint.rec with
    | infty => exact hinf
    | coe z => exact hfin z
  obtain ⟨A, hA, hrel⟩ := qf_solution_sphere_intertwine hΓ hμΓ hg hW
  obtain ⟨Ni, hNi, hleft, -⟩ := isMobius_inverse hN
  refine ⟨fun p => N (A (Ni p)), isMobius_comp (isMobius_comp hNi hA) hN, ?_⟩
  intro p
  change N (A (Ni (wB μ p))) = _
  rw [hrep p, hleft, ← hrel p, hrep]

/-- (TT:1032) The quasi-Fuchsian group `Γ^μ = w^μ ∘ Γ ∘ (w^μ)⁻¹` acts on the fiber `w^μ(𝔻*)` over `[μ] ∈ T(Γ)`: for
`γ ∈ Γ`, the map `w^μ ∘ γ ∘ (w^μ)⁻¹` of `ℂ̄` is Möbius and preserves `w^μ(𝔻*)`. -/
theorem quasiFuchsian_acts {Γ : Subgroup SL2C} (hΓ : IsFuchsian Γ) {μ : LinfStar} (hμ : μ ∈ LinfStarBall)
    (hμΓ : μ ∈ LinfGamma Γ) {g : SL2C} (hg : g ∈ Γ) :
    ∃ M : ExtPlane → ExtPlane, IsMobius M ∧ (∀ z : ℂ, M (wB μ z) = wB μ (mobiusExt (g 0 0) (g 0 1) (g 1 0) (g 1 1) z)) ∧
      M '' (wB μ '' extDiscExterior) = wB μ '' extDiscExterior := by
  obtain ⟨M, hM, hrel⟩ := qf_wB_intertwine hΓ hμ hμΓ hg
  refine ⟨M, hM, fun z => hrel z, ?_⟩
  rw [← image_comp]
  have he : M ∘ wB μ = wB μ ∘ mobiusExt (g 0 0) (g 0 1) (g 1 0) (g 1 1) := funext hrel
  rw [he, image_comp, qf_mobius_image_exterior (hΓ.1 g hg)]


end TakhtajanTeo
