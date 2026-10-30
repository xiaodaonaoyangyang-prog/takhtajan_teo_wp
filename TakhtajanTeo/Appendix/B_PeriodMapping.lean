import TakhtajanTeo.Appendix.A_HilbertStructure
import TakhtajanTeo.Ch2.GrunskyOperator
import TakhtajanTeo.Appendix.BergmanKernelModel
import TakhtajanTeo.Appendix.BergmanCompactness
import TakhtajanTeo.Appendix.BergmanPeriodModel
import TakhtajanTeo.Appendix.B1Entries

/-!
# Appendix B — The period mapping `𝒫̂` (TT:5968–6441)

Theorem B.1, the Gardiner–Sullivan characterization of `S`, Lemma B.2, Remark B.3, Theorem B.4, Brazilevič's function
`F` and metric `d`, Lemma B.5, Remark B.6, Lemma B.7, Lemma B.8, Remark B.9, and the inclusion
`Ψ(A_∞^{1,0}(𝔻)) ⊂ A_∞⁰(𝔻)` of the final diagram.

**Modelling.**
- Operators on `ℓ²` are matrices (§2, §5).
  - The operator norm `matOpNorm` is valued in `ℝ≥0∞`, so an unbounded matrix has norm `∞`, not a junk `0`.
  - A matrix is compact (`IsCompactMat`) when it is bounded and its tails `(1 - P_N)Z` tend to `0` in norm
    (`P_N` the projection onto the first `N` coordinates). For bounded `Z` this is equivalent to compactness.
- The integral operators `K₁(f)ψ̄ = ∬_𝔻 K₁(f)(·, w) \overline{ψ(w)} d²w` act on `A₂¹(𝔻)`. Their norm `kerOpNorm` is the
  supremum over the unit ball of `A₂¹(𝔻)`, valued in `ℝ≥0∞`.
- `S = Möb(S¹)\Homeo_s(S¹)` is `symmetricT` (§1).
- The Banach manifold topology of `T(1)` is read through the Bers embedding into `A_∞(𝔻)`.
- `𝒰` is the class of univalent functions on `𝔻` (holomorphic and injective).

**Corrections.** Lemma B.7 (TT:6262): "`\varliminf`" is an OCR rendering of `lim`.

**Not stated.** The proof of Theorem B.4 cites Remark 1.7 (a sequence `ζ_m` with `|ζ_m| → 1` and
`(1 - |ζ_m|²)²|𝒮(f)(ζ_m)| ≥ ε` when `[μ] ∉ S`). This is the negation of `symmetricT_spec`.
-/

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal ComplexConjugate Classical Real

noncomputable section

namespace TakhtajanTeo

open LiZhongQC Ch2

namespace AppB

/-- The operator norm of a matrix on `ℓ²`: `sup_{‖x‖ ≤ 1} ‖Zx‖`, in `ℝ≥0∞`.
[CORRECTION] An unbounded matrix has norm `∞`; totalized real sums of
non-square-summable outputs must not be interpreted as zero norms. -/
def matOpNorm (Z : ℕ → ℕ → ℂ) : ℝ≥0∞ :=
  if IsBoundedMat Z then
    ⨆ (x : ℕ → ℂ) (_ : IsL2 x ∧ sqSum x ≤ 1), ENNReal.ofReal (Real.sqrt (sqSum (matApply Z x)))
  else ∞

/-- For a bounded matrix the operator norm retains the original unit-ball formula. -/
theorem matOpNorm_of_bounded {Z : ℕ → ℕ → ℂ} (hZ : IsBoundedMat Z) :
    matOpNorm Z = ⨆ (x : ℕ → ℂ) (_ : IsL2 x ∧ sqSum x ≤ 1),
      ENNReal.ofReal (Real.sqrt (sqSum (matApply Z x))) := by
  simp [matOpNorm, hZ]

/-- An unbounded matrix has infinite extended operator norm. -/
theorem matOpNorm_of_not_bounded {Z : ℕ → ℕ → ℂ} (hZ : ¬IsBoundedMat Z) :
    matOpNorm Z = ∞ := by
  simp [matOpNorm, hZ]

/-- Finiteness of the extended operator norm is equivalent to actual boundedness. -/
theorem matOpNorm_lt_top_iff (Z : ℕ → ℕ → ℂ) : matOpNorm Z < ∞ ↔ IsBoundedMat Z := by
  constructor
  · intro h
    by_contra hn
    rw [matOpNorm_of_not_bounded hn] at h
    exact lt_irrefl _ h
  · intro hZ
    obtain ⟨C, hC⟩ := hZ
    rw [matOpNorm_of_bounded ⟨C, hC⟩]
    apply lt_of_le_of_lt (b := ENNReal.ofReal (Real.sqrt (max C 0)))
    · apply iSup_le
      intro x
      apply iSup_le
      rintro ⟨hx, hx1⟩
      apply ENNReal.ofReal_le_ofReal
      apply Real.sqrt_le_sqrt
      have hx0 : 0 ≤ sqSum x := tsum_nonneg (fun n => sq_nonneg ‖x n‖)
      calc
        sqSum (matApply Z x) ≤ C * sqSum x := (hC x hx).2
        _ ≤ max C 0 * sqSum x := mul_le_mul_of_nonneg_right (le_max_left _ _) hx0
        _ ≤ max C 0 := mul_le_of_le_one_right (le_max_right _ _) hx1
    · exact ENNReal.ofReal_lt_top

/-- Each matrix entry is bounded by the extended operator norm. -/
theorem norm_entry_le_matOpNorm (Z : ℕ → ℕ → ℂ) (m n : ℕ) :
    ENNReal.ofReal ‖Z m n‖ ≤ matOpNorm Z := by
  by_cases hZ : IsBoundedMat Z
  · let e : ℕ → ℂ := Pi.single n 1
    have he : IsL2 e := by
      apply summable_of_ne_finset_zero (s := {n})
      intro k hk
      have hkn : k ≠ n := by simpa using hk
      simp [e, hkn]
    have hesq : sqSum e = 1 := by
      unfold sqSum
      rw [tsum_eq_single n (fun k hk => by simp [e, hk])]
      simp [e]
    have hme : matApply Z e m = Z m n := by
      unfold matApply
      rw [tsum_eq_single n (fun k hk => by simp [e, hk])]
      simp [e]
    obtain ⟨C, hC⟩ := hZ
    have hout : Summable (fun k => ‖matApply Z e k‖ ^ 2) := (hC e he).1
    have hcoord : ‖Z m n‖ ^ 2 ≤ sqSum (matApply Z e) := by
      simpa only [Finset.sum_singleton, sqSum, hme] using
        hout.sum_le_tsum {m} (fun k _ => sq_nonneg ‖matApply Z e k‖)
    rw [matOpNorm_of_bounded ⟨C, hC⟩]
    refine le_trans (b := ENNReal.ofReal (Real.sqrt (sqSum (matApply Z e)))) ?_ ?_
    · apply ENNReal.ofReal_le_ofReal
      simpa only [Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg (Z m n))] using
        Real.sqrt_le_sqrt hcoord
    · exact le_iSup_of_le e (le_iSup_of_le ⟨he, hesq.le⟩ le_rfl)
  · rw [matOpNorm_of_not_bounded hZ]
    exact le_top

/-- The zero matrix has zero extended operator norm. -/
theorem matOpNorm_zero : matOpNorm (0 : ℕ → ℕ → ℂ) = 0 := by
  have hz : IsBoundedMat (0 : ℕ → ℕ → ℂ) := by
    refine ⟨0, ?_⟩
    intro x hx
    constructor
    · simp [IsL2, matApply]
    · simp [sqSum, matApply]
  rw [matOpNorm_of_bounded hz]
  simp only [matApply, Pi.zero_apply, zero_mul, tsum_zero, sqSum, norm_zero,
    zero_pow (by decide : 2 ≠ 0), Real.sqrt_zero, ENNReal.ofReal_zero]
  exact le_antisymm (iSup_le fun x => iSup_le fun _ => le_rfl) bot_le

/-- The repaired norm is nondegenerate, including on unbounded matrices. -/
theorem matOpNorm_eq_zero_iff (Z : ℕ → ℕ → ℂ) : matOpNorm Z = 0 ↔ Z = 0 := by
  constructor
  · intro h
    funext m n
    have he := norm_entry_le_matOpNorm Z m n
    rw [h] at he
    have hn : ‖Z m n‖ ≤ 0 := ENNReal.ofReal_eq_zero.mp (le_antisymm he bot_le)
    exact norm_eq_zero.mp (le_antisymm hn (norm_nonneg _))
  · rintro rfl
    exact matOpNorm_zero

/-- Output truncation is a contraction for the repaired extended matrix norm. -/
theorem matOpNorm_tail_le (Z : ℕ → ℕ → ℂ) (N : ℕ) :
    matOpNorm (fun m n => if m < N then 0 else Z m n) ≤ matOpNorm Z := by
  by_cases hZ : IsBoundedMat Z
  · rw [matOpNorm_of_bounded (isBoundedMat_tail hZ N), matOpNorm_of_bounded hZ]
    apply iSup_le
    intro x
    apply iSup_le
    intro hx
    refine le_trans (b := ENNReal.ofReal (Real.sqrt (sqSum (matApply Z x)))) ?_ ?_
    · exact ENNReal.ofReal_le_ofReal (Real.sqrt_le_sqrt (matApply_tail_sqSum_le hZ hx.1 N).2)
    · exact le_iSup_of_le x (le_iSup_of_le hx le_rfl)
  · rw [matOpNorm_of_not_bounded hZ]
    exact le_top

/-- `Z` is a compact operator on `ℓ²`: bounded, with `‖(1 - P_N)Z‖ → 0`. -/
def IsCompactMat (Z : ℕ → ℕ → ℂ) : Prop :=
  IsBoundedMat Z ∧ Tendsto (fun N : ℕ => matOpNorm fun m n => if m < N then 0 else Z m n) atTop (𝓝 0)

theorem b1_finBil_bounded {Z : ℕ → ℕ → ℂ} {K : ℝ} (hK : 0 ≤ K) (h : FinBil Z K) :
    IsBoundedMat Z ∧ matOpNorm Z ≤ ENNReal.ofReal K := by
  have hB : IsBoundedMat Z := ⟨K ^ 2, fun x hx => b1_finBil_apply hK h hx⟩
  refine ⟨hB, ?_⟩
  rw [matOpNorm_of_bounded hB]
  apply iSup_le
  intro x
  apply iSup_le
  rintro ⟨hx, hx1⟩
  apply ENNReal.ofReal_le_ofReal
  have := (b1_finBil_apply hK h hx).2
  apply Real.sqrt_le_iff.mpr
  refine ⟨hK, ?_⟩
  have hx0 : 0 ≤ sqSum x := tsum_nonneg (fun _ => sq_nonneg _)
  calc sqSum (matApply Z x) ≤ K ^ 2 * sqSum x := this
    _ ≤ K ^ 2 * 1 := mul_le_mul_of_nonneg_left hx1 (sq_nonneg K)
    _ = K ^ 2 := mul_one _

/-- Operator-norm differentiability of a matrix family from entrywise holomorphy and a uniform bound
on finitely supported vectors (Cauchy / Schwarz-type estimate on the scalar pairings). -/
theorem b1_norm_diff {Bf : ℂ → ℕ → ℕ → ℂ} {t0 : ℂ} {r M : ℝ} (hr : 0 < r) (hM : 0 ≤ M)
    (hdiff : ∀ m n, DifferentiableOn ℂ (fun t => Bf t m n) (ball t0 (2 * r)))
    (hfin : ∀ s ∈ closedBall t0 r, FinBil (Bf s) M) :
    ∃ D : ℕ → ℕ → ℂ, IsBoundedMat D ∧
      Tendsto (fun t => matOpNorm fun m n => (Bf t m n - Bf t0 m n) / (t - t0) - D m n)
        (𝓝[≠] t0) (𝓝 0) := by
  have hnh : ball t0 (2 * r) ∈ 𝓝 t0 := ball_mem_nhds _ (by linarith)
  let D : ℕ → ℕ → ℂ := fun m n => deriv (fun t => Bf t m n) t0
  have hD : ∀ m n, HasDerivAt (fun t => Bf t m n) (D m n) t0 := fun m n =>
    ((hdiff m n).differentiableAt hnh).hasDerivAt
  -- the scalar pairing
  let φ : Finset ℕ → Finset ℕ → (ℕ → ℂ) → (ℕ → ℂ) → ℂ → ℂ := fun X Y x y s =>
    ∑ m ∈ Y, ∑ n ∈ X, y m * Bf s m n * x n
  have hφd : ∀ X Y x y, DifferentiableOn ℂ (φ X Y x y) (ball t0 (2 * r)) := by
    intro X Y x y
    apply DifferentiableOn.fun_sum
    intro m _
    apply DifferentiableOn.fun_sum
    intro n _
    exact ((hdiff m n).const_mul (y m)).mul_const (x n)
  have hφb : ∀ X Y x y, ∀ s ∈ closedBall t0 r, ‖φ X Y x y s‖ ≤
      M * Real.sqrt (∑ n ∈ X, ‖x n‖ ^ 2) * Real.sqrt (∑ m ∈ Y, ‖y m‖ ^ 2) :=
    fun X Y x y s hs => hfin s hs X Y x y
  have hφder : ∀ X Y x y, HasDerivAt (φ X Y x y) (∑ m ∈ Y, ∑ n ∈ X, y m * D m n * x n) t0 := by
    intro X Y x y
    apply HasDerivAt.fun_sum
    intro m _
    apply HasDerivAt.fun_sum
    intro n _
    exact ((hD m n).const_mul (y m)).mul_const (x n)
  have hDfin : FinBil D (M / r) := by
    intro X Y x y
    have hfc : DiffContOnCl ℂ (φ X Y x y) (ball t0 r) :=
      ((hφd X Y x y).mono ((closure_ball t0 hr.ne').symm ▸
        closedBall_subset_ball (by linarith))).diffContOnCl
    have hb := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hr hfc
      (fun z hz => hφb X Y x y z (sphere_subset_closedBall hz))
    rw [(hφder X Y x y).deriv] at hb
    calc _ ≤ _ := hb
      _ = _ := by ring
  refine ⟨D, (b1_finBil_bounded (div_nonneg hM hr.le) hDfin).1, ?_⟩
  have hbound : ∀ t ∈ closedBall t0 r, t ≠ t0 →
      matOpNorm (fun m n => (Bf t m n - Bf t0 m n) / (t - t0) - D m n) ≤
        ENNReal.ofReal (3 * M * ‖t - t0‖ / r ^ 2) := by
    intro t ht hne
    have hK : 0 ≤ 3 * M * ‖t - t0‖ / r ^ 2 := by positivity
    refine (b1_finBil_bounded hK ?_).2
    intro X Y x y
    have hdl := b1_dslope_bound hr (hφd X Y x y) (hφb X Y x y) ht
    have hsne : t - t0 ≠ 0 := sub_ne_zero.mpr hne
    have e : ∑ m ∈ Y, ∑ n ∈ X, y m * ((Bf t m n - Bf t0 m n) / (t - t0) - D m n) * x n =
        dslope (φ X Y x y) t0 t - deriv (φ X Y x y) t0 := by
      rw [dslope_of_ne _ hne, slope_def_field, (hφder X Y x y).deriv]
      simp only [φ, ← Finset.sum_sub_distrib, Finset.sum_div]
      apply Finset.sum_congr rfl
      intro m _
      apply Finset.sum_congr rfl
      intro n _
      field_simp
    rw [e]
    refine hdl.trans (le_of_eq ?_)
    ring
  have hlim : Tendsto (fun t : ℂ => ENNReal.ofReal (3 * M * ‖t - t0‖ / r ^ 2)) (𝓝[≠] t0) (𝓝 0) := by
    have h0 : Tendsto (fun t : ℂ => 3 * M * ‖t - t0‖ / r ^ 2) (𝓝 t0) (𝓝 0) := by
      have hc : Continuous (fun t : ℂ => 3 * M * ‖t - t0‖ / r ^ 2) := by fun_prop
      simpa using hc.tendsto t0
    have := (ENNReal.tendsto_ofReal h0).mono_left (nhdsWithin_le_nhds (s := {t0}ᶜ))
    simpa using this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    (Eventually.of_forall fun _ => bot_le) ?_
  have hcb : ∀ᶠ t in 𝓝[≠] t0, t ∈ closedBall t0 r :=
    nhdsWithin_le_nhds (closedBall_mem_nhds t0 hr)
  have hne : ∀ᶠ t in 𝓝[≠] t0, t ≠ t0 := self_mem_nhdsWithin
  exact (hcb.and hne).mono fun t h => hbound t h.1 h.2

/-- **Theorem B.1** (TT:5978–6016). `𝒫̂ : T(1) → ℬ(ℓ²)` is a holomorphic mapping of Banach manifolds. For `ν ∈ L∞(𝔻*)₁`
and `μ ∈ Ω^{-1,1}(𝔻*)`, the map `t ↦ B₁(𝖿^{ν + tμ})` is complex differentiable in the operator norm at every `t₀` with
`‖ν + t₀μ‖∞ < 1`. -/
theorem thm_B_1 {ν μ : LinfStar} {t₀ : ℂ} (h : ν + t₀ • μ ∈ LinfStarBall) :
    let B : ℂ → ℕ → ℕ → ℂ := fun t => B1 (grunsky (fsans (ν + t • μ)) (gsans (ν + t • μ)))
    ∃ D : ℕ → ℕ → ℂ, IsBoundedMat D ∧
      Tendsto (fun t => matOpNorm fun m n => (B t m n - B t₀ m n) / (t - t₀) - D m n) (𝓝[≠] t₀) (𝓝 0) := by
  obtain ⟨r, hr, hball, hdiff⟩ := b1_entries h
  refine b1_norm_diff (Bf := fun t => B1 (grunsky (fsans (ν + t • μ)) (gsans (ν + t • μ))))
    (M := 1) hr zero_le_one hdiff ?_
  intro s hs
  have hs' : s ∈ ball t₀ (2 * r) := closedBall_subset_ball (by linarith) hs
  exact b1_finBil_of_contractive
    (b8_pair_model (b8_welding_normalized_pair (hball s hs'))).2.2.1

/-- The classes of `Möb(S¹)\Diff₊(S¹)` in `T(1)`. -/
def diffT : Set T1 := {p | IsCircleDiffeo (wA (Quotient.out p : LinfStarBall))}

-- `lemma_B_2` moved to `TakhtajanTeo.Appendix.B2Closure` (2026-10-29, Program G).

-- `remark_B_3` moved to `TakhtajanTeo.Appendix.B3Closure` (2026-10-29, Program G).

-- `thm_B_4` moved to `Appendix/PeriodCompactCharacterization.lean` (2026-10-28).

/-- The class `𝒰` of univalent functions on `𝔻`. -/
def IsUnivalentDisc (f : ℂ → ℂ) : Prop := DifferentiableOn ℂ f unitDisc ∧ InjOn f unitDisc

/-- Brazilevič's function `F(f₁, f₂)(z) = √π (1 - |z|²) (∬_𝔻 |K₁(f₁)(z, w) - K₁(f₂)(z, w)|² d²w)^{1/2}` (TT:6064). -/
def brazF (f₁ f₂ : ℂ → ℂ) (z : ℂ) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.sqrt π * (1 - ‖z‖ ^ 2)) *
    (∫⁻ w in unitDisc, (‖kerK1 f₁ z w - kerK1 f₂ z w‖₊ : ℝ≥0∞) ^ 2) ^ (1 / 2 : ℝ)

/-- Brazilevič's metric `d(f₁, f₂) = sup_{z ∈ 𝔻} F(f₁, f₂)(z)` on `𝒰` (TT:6072). -/
def brazD (f₁ f₂ : ℂ → ℂ) : ℝ≥0∞ := ⨆ z ∈ unitDisc, brazF f₁ f₂ z

/-- The operator norm of `ψ ↦ ∬_𝔻 k(·, w) \overline{ψ(w)} d²w` on `A₂¹(𝔻)` (`ℝ≥0∞`-valued). -/
def kerOpNorm (k : ℂ → ℂ → ℂ) : ℝ≥0∞ :=
  ⨆ (ψ : ℂ → ℂ) (_ : ψ ∈ A21fun unitDisc ∧ normA21 unitDisc ψ ≤ 1),
    normA21 unitDisc fun z => ∫ w in unitDisc, k z w * conj (ψ w)

-- `remark_B_6` moved to `Appendix/B6Completed.lean` (2026-10-26).

/-- `f_n = r_n⁻¹ ∘ f ∘ r_n`, `r_n(z) = (n/(n + 1)) z` (TT:6224), analytic on `S¹`. -/
def dilateF (f : ℂ → ℂ) (n : ℕ) (z : ℂ) : ℂ := ((n + 1 : ℝ) / n : ℂ) * f (((n : ℝ) / (n + 1) : ℂ) * z)

/-- (TT:6224–6226) The dilated univalent function extends univalently to the
disk of radius `(n + 1) / n`, which strictly contains the closed unit disk. -/
theorem dilateF_extension {f : ℂ → ℂ} (hf : IsUnivalentDisc f) {n : ℕ} (hn : 1 ≤ n) :
    1 < (n + 1 : ℝ) / n ∧
      DifferentiableOn ℂ (dilateF f n) (ball 0 ((n + 1 : ℝ) / n)) ∧
      InjOn (dilateF f n) (ball 0 ((n + 1 : ℝ) / n)) := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hn1pos : (0 : ℝ) < n + 1 := by positivity
  have hrpos : 0 < (n : ℝ) / (n + 1) := div_pos hnpos hn1pos
  have hRpos : 0 < (n + 1 : ℝ) / n := div_pos hn1pos hnpos
  have hprod : (n : ℝ) / (n + 1) * ((n + 1) / n) = 1 := by field_simp
  have hmap : MapsTo (fun z : ℂ => (((n : ℝ) / (n + 1) : ℝ) : ℂ) * z)
      (ball 0 ((n + 1 : ℝ) / n)) unitDisc := by
    intro z hz
    apply mem_ball_zero_iff.mpr
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hrpos]
    have hz' := mul_lt_mul_of_pos_left (mem_ball_zero_iff.mp hz) hrpos
    rwa [hprod] at hz'
  refine ⟨(lt_div_iff₀ hnpos).mpr (by linarith), ?_, ?_⟩
  · have hd := (hf.1.fun_comp (differentiable_id.const_mul
        ((((n : ℝ) / (n + 1) : ℝ) : ℂ))).differentiableOn hmap).const_mul
        ((((n + 1 : ℝ) / n : ℝ) : ℂ))
    change DifferentiableOn ℂ
      (fun z => ((n + 1 : ℝ) / n : ℂ) * f (((n : ℝ) / (n + 1) : ℂ) * z)) _
    simpa only [Complex.ofReal_div, Complex.ofReal_add,
      Complex.ofReal_natCast, Complex.ofReal_one] using hd
  · intro z hz w hw hzw
    have hRne : (((n + 1 : ℝ) / n : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast ne_of_gt hRpos
    have hrne : (((n : ℝ) / (n + 1) : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast ne_of_gt hrpos
    apply mul_left_cancel₀ hrne
    apply hf.2 (hmap hz) (hmap hw)
    apply mul_left_cancel₀ hRne
    simpa only [dilateF, Complex.ofReal_div, Complex.ofReal_add,
      Complex.ofReal_natCast, Complex.ofReal_one] using hzw

/-- (TT:6224–6226) Dilation preserves univalence and the normalization
`f(0) = 0`, `f'(0) = 1`, independently of the boundary-limit assertions. -/
theorem dilateF_normalized {f : ℂ → ℂ} (hf : IsUnivalentDisc f)
    (h0 : f 0 = 0) (h1 : deriv f 0 = 1) {n : ℕ} (hn : 1 ≤ n) :
    IsUnivalentDisc (dilateF f n) ∧ dilateF f n 0 = 0 ∧ deriv (dilateF f n) 0 = 1 := by
  obtain ⟨hR, hdiff, hinj⟩ := dilateF_extension hf hn
  have hsub : unitDisc ⊆ ball (0 : ℂ) ((n + 1 : ℝ) / n) :=
    ball_subset_ball hR.le
  refine ⟨⟨hdiff.mono hsub, hinj.mono hsub⟩, ?_, ?_⟩
  · simp [dilateF, h0]
  · have hf0 : DifferentiableAt ℂ f 0 :=
      hf.1.differentiableAt (isOpen_ball.mem_nhds (by simp))
    have hf0' : HasDerivAt f (deriv f 0) ((n : ℂ) / (n + 1) * 0) := by
      simpa only [mul_zero] using hf0.hasDerivAt
    have hd := (hf0'.comp 0
      ((hasDerivAt_id (0 : ℂ)).const_mul ((n : ℂ) / (n + 1)))).const_mul
        (((n : ℂ) + 1) / n)
    have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
    have hn10 : (n : ℂ) + 1 ≠ 0 := by
      exact_mod_cast (by positivity : (n : ℝ) + 1 ≠ 0)
    change deriv (fun z => ((n + 1 : ℝ) / n : ℂ) *
      f (((n : ℝ) / (n + 1) : ℂ) * z)) 0 = 1
    have hm : ((n : ℂ) + 1) / n * (1 * ((n : ℂ) / (n + 1) * 1)) = 1 := by
      field_simp
    simpa only [h1, hm, Function.comp_apply, id_eq, Complex.ofReal_add,
      Complex.ofReal_natCast, Complex.ofReal_one] using hd.deriv

/-- (TT:6224) The argument of a radial dilation stays in the unit disk. -/
theorem dilateF_argument_mem (n : ℕ) {z : ℂ} (hz : z ∈ unitDisc) :
    (n : ℂ) / (n + 1) * z ∈ unitDisc := by
  have hr0 : (0 : ℝ) ≤ n / (n + 1) := by positivity
  have hr1 : (n : ℝ) / (n + 1) ≤ 1 := by
    apply (div_le_one (by positivity)).mpr
    linarith
  have hm : ((((n : ℝ) / (n + 1) : ℝ) : ℂ) * z) ∈ unitDisc := by
    apply mem_ball_zero_iff.mpr
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr0]
    exact (mul_le_of_le_one_left (norm_nonneg z) hr1).trans_lt (mem_ball_zero_iff.mp hz)
  simpa only [Complex.ofReal_div, Complex.ofReal_add, Complex.ofReal_natCast,
    Complex.ofReal_one] using hm

/-- (TT:6224) The input and output scaling factors cancel in the first derivative. -/
theorem dilateF_hasDerivAt {f : ℂ → ℂ} {n : ℕ} (hn : 1 ≤ n) {z : ℂ}
    (hf : DifferentiableAt ℂ f ((n : ℂ) / (n + 1) * z)) :
    HasDerivAt (dilateF f n) (deriv f ((n : ℂ) / (n + 1) * z)) z := by
  have hd := (hf.hasDerivAt.comp z
    ((hasDerivAt_id z).const_mul ((n : ℂ) / (n + 1)))).const_mul (((n : ℂ) + 1) / n)
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  have hn10 : (n : ℂ) + 1 ≠ 0 := by
    exact_mod_cast (by positivity : (n : ℝ) + 1 ≠ 0)
  have hm : ((n : ℂ) + 1) / n *
      (deriv f ((n : ℂ) / (n + 1) * z) * ((n : ℂ) / (n + 1) * 1)) =
        deriv f ((n : ℂ) / (n + 1) * z) := by field_simp
  change HasDerivAt (fun u => ((n + 1 : ℝ) / n : ℂ) *
    f (((n : ℝ) / (n + 1) : ℂ) * u)) _ z
  simpa only [hm, Function.comp_apply, id_eq, Complex.ofReal_add,
    Complex.ofReal_natCast, Complex.ofReal_one] using hd

/-- (TT:6224) The derivative formula on the unit disk. -/
theorem dilateF_deriv {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f unitDisc)
    {n : ℕ} (hn : 1 ≤ n) {z : ℂ} (hz : z ∈ unitDisc) :
    deriv (dilateF f n) z = deriv f ((n : ℂ) / (n + 1) * z) := by
  exact (dilateF_hasDerivAt hn
    (hf.differentiableAt (isOpen_ball.mem_nhds (dilateF_argument_mem n hz)))).deriv

/-- (TT:6224, 6238) Radial dilations converge pointwise to a holomorphic function
on the unit disk. This does not use the asserted strong operator convergence. -/
theorem dilateF_tendsto {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f unitDisc)
    {z : ℂ} (hz : z ∈ unitDisc) :
    Tendsto (fun n => dilateF f n z) atTop (𝓝 (f z)) := by
  have hr := tendsto_natCast_div_add_atTop (1 : ℂ)
  have hzlim : Tendsto (fun n : ℕ => (n : ℂ) / (n + 1) * z) atTop (𝓝 z) := by
    simpa only [one_mul] using hr.mul_const z
  have hflim := (hf.differentiableAt (isOpen_ball.mem_nhds hz)).continuousAt.tendsto.comp hzlim
  have hR := hr.inv₀ (by simp)
  change Tendsto (fun n : ℕ => ((n + 1 : ℝ) / n : ℂ) *
    f (((n : ℝ) / (n + 1) : ℂ) * z)) atTop (𝓝 (f z))
  simpa only [inv_div, inv_one, one_mul, Function.comp_apply, Complex.ofReal_add,
    Complex.ofReal_natCast, Complex.ofReal_one] using hR.mul hflim

/-- (TT:6224, 6238) The derivatives of radial dilations converge pointwise. -/
theorem dilateF_deriv_tendsto {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f unitDisc)
    {z : ℂ} (hz : z ∈ unitDisc) :
    Tendsto (fun n => deriv (dilateF f n) z) atTop (𝓝 (deriv f z)) := by
  have hzlim : Tendsto (fun n : ℕ => (n : ℂ) / (n + 1) * z) atTop (𝓝 z) := by
    simpa only [one_mul] using (tendsto_natCast_div_add_atTop (1 : ℂ)).mul_const z
  have hd := ((hf.deriv isOpen_ball).differentiableAt
    (isOpen_ball.mem_nhds hz)).continuousAt.tendsto.comp hzlim
  apply hd.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  exact (dilateF_deriv hf hn hz).symm

/-- (TT:6224–6226) The Schwarzian transforms quadratically under radial dilation. -/
theorem dilateF_schwarzian {f : ℂ → ℂ} (hf : IsUnivalentDisc f) {n : ℕ} (hn : 1 ≤ n)
    {z : ℂ} (hz : z ∈ unitDisc) :
    schwarzianHol (dilateF f n) z = ((n : ℂ) / (n + 1)) ^ 2 *
      schwarzianHol f ((n : ℂ) / (n + 1) * z) := by
  let r : ℂ := (n : ℂ) / (n + 1)
  let g : ℂ → ℂ := fun u => r * u
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  have hn10 : (n : ℂ) + 1 ≠ 0 := by
    exact_mod_cast (by positivity : (n : ℝ) + 1 ≠ 0)
  have hr : r ≠ 0 := div_ne_zero hn0 hn10
  have hgz : g z ∈ unitDisc := dilateF_argument_mem n hz
  have hga : AnalyticAt ℂ g z := by dsimp [g]; fun_prop
  have hgd : deriv g z = r := by
    simpa only [g, mul_one, id_eq] using ((hasDerivAt_id z).const_mul r).deriv
  have hg' : deriv g z ≠ 0 := hgd ▸ hr
  have hfa := hf.1.analyticAt (isOpen_ball.mem_nhds hgz)
  have hf' : deriv f (g z) ≠ 0 := LiZhongQC.deriv_ne_zero_of_injOn isOpen_ball hf.1 hf.2 hgz
  have hcomp : AnalyticAt ℂ (f ∘ g) z := hfa.comp hga
  have hcomp' : deriv (f ∘ g) z ≠ 0 := by
    rw [deriv_comp z hfa.differentiableAt hga.differentiableAt]
    exact mul_ne_zero hf' hg'
  have hfun : dilateF f n = fun u => r⁻¹ * (f ∘ g) u := by
    funext u
    simp only [dilateF, r, g, inv_div, Function.comp_apply, Complex.ofReal_add,
      Complex.ofReal_natCast, Complex.ofReal_one]
  have hdil : AnalyticAt ℂ (dilateF f n) z := by
    rw [hfun]
    exact analyticAt_const.mul hcomp
  have hp := schwarzian_mobius_comp_of_ne hcomp hcomp'
    (a := r⁻¹) (b := 0) (c := 0) (d := 1) (by simpa using inv_ne_zero hr) (by simp)
  simp only [zero_mul, add_zero, zero_add, div_one] at hp
  rw [← hfun, schwarzian_of_analyticAt hdil, schwarzian_of_analyticAt hcomp] at hp
  have hlin : schwarzianHol g z = 0 := by
    simpa only [g, zero_mul, add_zero, zero_add, div_one] using
      (schwarzianHol_mobius (a := r) (b := 0) (c := 0) (d := 1)
        (z := z) (by simpa using hr) (by simp))
  have hc := eq19_1_chain_rule hga hg' hfa hf'
  rw [schwarzian_of_analyticAt hcomp, schwarzian_of_analyticAt hfa,
    schwarzian_of_analyticAt hga] at hc
  rw [hp, hc, hlin, hgd]
  change schwarzianHol f (r * z) * r ^ 2 + 0 = r ^ 2 * schwarzianHol f (r * z)
  ring

/-- (TT:6224–6226) The Schwarzians of radial dilations converge pointwise. -/
theorem dilateF_schwarzian_tendsto {f : ℂ → ℂ} (hf : IsUnivalentDisc f)
    {z : ℂ} (hz : z ∈ unitDisc) :
    Tendsto (fun n => schwarzianHol (dilateF f n) z) atTop (𝓝 (schwarzianHol f z)) := by
  have hr := tendsto_natCast_div_add_atTop (1 : ℂ)
  have hzlim : Tendsto (fun n : ℕ => (n : ℂ) / (n + 1) * z) atTop (𝓝 z) := by
    simpa only [one_mul] using hr.mul_const z
  have hs := (analyticAt_schwarzianHol (hf.1.analyticAt (isOpen_ball.mem_nhds hz))
    (LiZhongQC.deriv_ne_zero_of_injOn isOpen_ball hf.1 hf.2 hz)).continuousAt.tendsto.comp hzlim
  have hlim : Tendsto (fun n : ℕ => ((n : ℂ) / (n + 1)) ^ 2 *
      schwarzianHol f ((n : ℂ) / (n + 1) * z)) atTop (𝓝 (schwarzianHol f z)) := by
    simpa only [one_pow, one_mul, Function.comp_apply] using (hr.pow 2).mul hs
  apply hlim.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  exact (dilateF_schwarzian hf hn hz).symm

/-- (TT:6224, 6238–6278) The Grunsky kernel transforms by the square of the
radial scaling factor. This identity also respects the present diagonal value. -/
theorem kerK1_dilateF {f : ℂ → ℂ} (hf : IsUnivalentDisc f) {n : ℕ} (hn : 1 ≤ n)
    {z w : ℂ} (hz : z ∈ unitDisc) (hw : w ∈ unitDisc) :
    kerK1 (dilateF f n) z w = ((n : ℂ) / (n + 1)) ^ 2 *
      kerK1 f ((n : ℂ) / (n + 1) * z) ((n : ℂ) / (n + 1) * w) := by
  by_cases hzw : z = w
  · subst w
    rw [kerK1_diag, kerK1_diag, dilateF_schwarzian hf hn hz]
    ring
  let r : ℂ := (n : ℂ) / (n + 1)
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  have hn10 : (n : ℂ) + 1 ≠ 0 := by
    exact_mod_cast (by positivity : (n : ℝ) + 1 ≠ 0)
  have hr : r ≠ 0 := div_ne_zero hn0 hn10
  have hfw : f (r * z) - f (r * w) ≠ 0 := by
    intro h
    apply hzw
    apply mul_left_cancel₀ hr
    exact hf.2 (dilateF_argument_mem n hz) (dilateF_argument_mem n hw) (sub_eq_zero.mp h)
  have hR : ((n + 1 : ℝ) / n : ℂ) = r⁻¹ := by
    simp only [r, inv_div, Complex.ofReal_add, Complex.ofReal_natCast, Complex.ofReal_one]
  have hscaled : (n : ℂ) / (n + 1) * z ≠ (n : ℂ) / (n + 1) * w := by
    intro h
    exact hzw (mul_left_cancel₀ hr h)
  rw [kerK1_of_ne _ hzw, kerK1_of_ne _ hscaled]
  rw [dilateF_deriv hf.1 hn hz, dilateF_deriv hf.1 hn hw]
  change 1 / (π : ℂ) * (1 / (z - w) ^ 2 -
    deriv f (r * z) * deriv f (r * w) /
      (((n + 1 : ℝ) / n : ℂ) * f (r * z) - ((n + 1 : ℝ) / n : ℂ) * f (r * w)) ^ 2) =
      r ^ 2 * (1 / (π : ℂ) * (1 / (r * z - r * w) ^ 2 -
        deriv f (r * z) * deriv f (r * w) / (f (r * z) - f (r * w)) ^ 2))
  rw [hR, ← mul_sub, ← mul_sub]
  field_simp [hr, sub_ne_zero.mpr hzw, hfw]

/-- (TT:6238–6278) The dilated kernels converge at every pair of points of
the disk. Passing this limit through the integral still requires bounds. -/
theorem kerK1_dilateF_tendsto {f : ℂ → ℂ} (hf : IsUnivalentDisc f)
    {z w : ℂ} (hz : z ∈ unitDisc) (hw : w ∈ unitDisc) :
    Tendsto (fun n => kerK1 (dilateF f n) z w) atTop (𝓝 (kerK1 f z w)) := by
  by_cases hzw : z = w
  · subst w
    simpa only [kerK1_diag] using
      (dilateF_schwarzian_tendsto hf hz).neg.div_const (6 * (π : ℂ))
  have hfw : (f z - f w) ^ 2 ≠ 0 :=
    pow_ne_zero 2 (sub_ne_zero.mpr (fun h => hzw (hf.2 hz hw h)))
  simp only [kerK1_of_ne _ hzw]
  exact tendsto_const_nhds.mul (tendsto_const_nhds.sub
    (((dilateF_deriv_tendsto hf.1 hz).mul (dilateF_deriv_tendsto hf.1 hw)).div
      (((dilateF_tendsto hf.1 hz).sub (dilateF_tendsto hf.1 hw)).pow 2) hfw))

/-- (TT:6226) Analytic extension across the unit circle implies the first
weighted Schwarzian boundary limit in `dilateF_spec`. -/
theorem dilateF_schwarzian_boundary {f : ℂ → ℂ} (hf : IsUnivalentDisc f)
    {n : ℕ} (hn : 1 ≤ n) :
    Tendsto (fun z => ((1 - ‖z‖ ^ 2) ^ 2 : ℂ) * schwarzianHol (dilateF f n) z)
      (comap (fun z : ℂ => ‖z‖) (𝓝[<] 1)) (𝓝 0) := by
  obtain ⟨hR, hd, hi⟩ := dilateF_extension hf hn
  have hcont : ContinuousOn (schwarzianHol (dilateF f n)) (closedBall (0 : ℂ) 1) := by
    intro z hz
    have hzR : z ∈ ball (0 : ℂ) ((n + 1 : ℝ) / n) :=
      mem_ball_zero_iff.mpr ((mem_closedBall_zero_iff.mp hz).trans_lt hR)
    exact (analyticAt_schwarzianHol (hd.analyticAt (isOpen_ball.mem_nhds hzR))
      (LiZhongQC.deriv_ne_zero_of_injOn isOpen_ball hd hi hzR)).continuousAt.continuousWithinAt
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : ℂ) 1).exists_bound_of_continuousOn hcont
  let l := comap (fun z : ℂ => ‖z‖) (𝓝[<] (1 : ℝ))
  have hnorm : Tendsto (fun z : ℂ => ‖z‖) l (𝓝 1) :=
    tendsto_comap.mono_right nhdsWithin_le_nhds
  have hlt : ∀ᶠ z : ℂ in l, ‖z‖ < 1 := tendsto_comap.eventually self_mem_nhdsWithin
  have hlim : Tendsto (fun z : ℂ => (1 - ‖z‖ ^ 2) ^ 2 * C) l (𝓝 0) := by
    simpa using (((tendsto_const_nhds (x := (1 : ℝ))).sub (hnorm.pow 2)).pow 2).mul_const C
  apply squeeze_zero_norm' _ hlim
  filter_upwards [hlt] with z hz
  rw [norm_mul]
  have hfac : ‖((1 - ‖z‖ ^ 2) ^ 2 : ℂ)‖ = (1 - ‖z‖ ^ 2) ^ 2 := by
    norm_cast
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  rw [hfac]
  exact mul_le_mul_of_nonneg_left (hC z (mem_closedBall_zero_iff.mpr hz.le)) (sq_nonneg _)

/-- Differentiating the exact divided-difference identity recovers the derivative. -/
theorem deriv_eq_dslope_add {g : ℂ → ℂ} {a z : ℂ}
    (hd : DifferentiableAt ℂ (dslope g a) z) :
    deriv g z = dslope g a z + (z - a) * deriv (dslope g a) z := by
  have he : (fun u : ℂ => (u - a) * dslope g a u + g a) = g := by
    funext u
    have h := sub_smul_dslope g a u
    change (u - a) * dslope g a u = g u - g a at h
    linear_combination h
  have h := (((hasDerivAt_id z).sub_const a).mul hd.hasDerivAt).add_const (g a)
  simp only [Pi.mul_apply, id_eq] at h
  rw [he] at h
  simpa only [one_mul] using h.deriv

/-- The off-diagonal Grunsky kernel has a holomorphic extension in its first
variable. The divided-difference formula avoids any unproved kernel estimate. -/
theorem kerK1_exists_holomorphic_extension {f : ℂ → ℂ} {U : Set ℂ}
    (hU : IsOpen U) (hf : DifferentiableOn ℂ f U) (hi : InjOn f U)
    {a : ℂ} (ha : a ∈ U) :
    ∃ H : ℂ → ℂ, DifferentiableOn ℂ H U ∧
      ∀ z ∈ U, z ≠ a → H z = kerK1 f z a := by
  let d : ℂ → ℂ := dslope f a
  let q : ℂ → ℂ := dslope d a
  have hd : DifferentiableOn ℂ d U := (Complex.differentiableOn_dslope (hU.mem_nhds ha)).mpr hf
  have hq : DifferentiableOn ℂ q U := (Complex.differentiableOn_dslope (hU.mem_nhds ha)).mpr hd
  have hdne (z : ℂ) (hz : z ∈ U) : d z ≠ 0 := by
    by_cases hza : z = a
    · subst z
      simpa only [d, dslope_same] using LiZhongQC.deriv_ne_zero_of_injOn hU hf hi ha
    · dsimp only [d]
      rw [dslope_of_ne f hza]
      change (z - a)⁻¹ * (f z - f a) ≠ 0
      exact mul_ne_zero (inv_ne_zero (sub_ne_zero.mpr hza))
        (sub_ne_zero.mpr (fun h => hza (hi hz ha h)))
  have hpi : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  let H : ℂ → ℂ := fun z => (q z ^ 2 - deriv f a * deriv q z) / (π * d z ^ 2)
  refine ⟨H, ?_, ?_⟩
  · exact ((hq.pow 2).sub ((hq.deriv hU).const_mul (deriv f a))).div
      ((hd.pow 2).const_mul (π : ℂ)) (fun z hz => mul_ne_zero hpi (pow_ne_zero 2 (hdne z hz)))
  · intro z hz hza
    have hdval : d z = deriv f a + (z - a) * q z := by
      have h := sub_smul_dslope d a z
      change (z - a) * q z = d z - d a at h
      have hda : d a = deriv f a := dslope_same f a
      rw [hda] at h
      linear_combination -h
    have hfval : f z - f a = (z - a) * d z := by
      simpa only [d, smul_eq_mul] using (sub_smul_dslope f a z).symm
    have hdf := deriv_eq_dslope_add (hd.differentiableAt (hU.mem_nhds hz))
    have hdd := deriv_eq_dslope_add (hq.differentiableAt (hU.mem_nhds hz))
    change deriv f z = d z + (z - a) * deriv d z at hdf
    change deriv d z = q z + (z - a) * deriv q z at hdd
    rw [kerK1_of_ne f hza, hfval, hdf, hdd]
    dsimp only [H]
    field_simp [hpi, hdne z hz, sub_ne_zero.mpr hza]
    rw [hdval]
    ring

/-- A map univalent on a disk larger than the unit disk has a uniformly
bounded off-diagonal Grunsky kernel on the closed unit disk. -/
theorem kerK1_uniform_bound_of_extension {f : ℂ → ℂ} {R : ℝ} (hR : 1 < R)
    (hf : DifferentiableOn ℂ f (ball 0 R)) (hi : InjOn f (ball 0 R)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a ∈ closedBall (0 : ℂ) 1, ∀ z ∈ closedBall (0 : ℂ) 1,
      z ≠ a → ‖kerK1 f z a‖ ≤ C := by
  let ρ : ℝ := (1 + R) / 2
  have hρ1 : 1 < ρ := by dsimp [ρ]; linarith
  have hρR : ρ < R := by dsimp [ρ]; linarith
  let T : Set (ℂ × ℂ) := sphere 0 ρ ×ˢ closedBall 0 1
  have hsmall : closedBall (0 : ℂ) 1 ⊆ ball 0 R := by
    intro z hz
    exact mem_ball_zero_iff.mpr ((mem_closedBall_zero_iff.mp hz).trans_lt hR)
  have houter : sphere (0 : ℂ) ρ ⊆ ball 0 R := by
    intro z hz
    have hzn : ‖z‖ = ρ := by simpa only [mem_sphere, dist_zero_right] using hz
    exact mem_ball_zero_iff.mpr (hzn ▸ hρR)
  have hne (p : ℂ × ℂ) (hp : p ∈ T) : p.1 ≠ p.2 := by
    intro he
    have h1 : ‖p.1‖ = ρ := by simpa only [mem_sphere, dist_zero_right] using hp.1
    have h2 : ‖p.2‖ ≤ 1 := mem_closedBall_zero_iff.mp hp.2
    rw [he] at h1
    linarith
  have hcont : ContinuousOn (fun p : ℂ × ℂ => kerK1 f p.1 p.2) T := by
    intro p hp
    have h1 := houter hp.1
    have h2 := hsmall hp.2
    have hf1 : ContinuousAt (fun q : ℂ × ℂ => f q.1) p :=
      (hf.continuousOn.continuousAt (isOpen_ball.mem_nhds h1)).comp continuousAt_fst
    have hf2 : ContinuousAt (fun q : ℂ × ℂ => f q.2) p :=
      (hf.continuousOn.continuousAt (isOpen_ball.mem_nhds h2)).comp continuousAt_snd
    have hd1 : ContinuousAt (fun q : ℂ × ℂ => deriv f q.1) p :=
      ((hf.deriv isOpen_ball).continuousOn.continuousAt (isOpen_ball.mem_nhds h1)).comp continuousAt_fst
    have hd2 : ContinuousAt (fun q : ℂ × ℂ => deriv f q.2) p :=
      ((hf.deriv isOpen_ball).continuousOn.continuousAt (isOpen_ball.mem_nhds h2)).comp continuousAt_snd
    have hpn : p.1 - p.2 ≠ 0 := sub_ne_zero.mpr (hne p hp)
    have hfn : f p.1 - f p.2 ≠ 0 := sub_ne_zero.mpr (fun he => hne p hp (hi h1 h2 he))
    have hraw : ContinuousAt (fun q : ℂ × ℂ => (1 / (π : ℂ)) *
        (1 / (q.1 - q.2) ^ 2 - deriv f q.1 * deriv f q.2 / (f q.1 - f q.2) ^ 2)) p :=
      ((continuousAt_const.div ((continuousAt_fst.sub continuousAt_snd).pow 2) (pow_ne_zero 2 hpn)).sub
        ((hd1.mul hd2).div ((hf1.sub hf2).pow 2) (pow_ne_zero 2 hfn))).const_mul _
    have hev : ∀ᶠ q : ℂ × ℂ in 𝓝 p, q.1 - q.2 ≠ 0 :=
      (continuousAt_fst.sub continuousAt_snd).eventually_ne hpn
    apply ContinuousAt.continuousWithinAt
    apply hraw.congr_of_eventuallyEq
    filter_upwards [hev] with q hq
    exact kerK1_of_ne f (sub_ne_zero.mp hq)
  have hT : IsCompact T := (isCompact_sphere (0 : ℂ) ρ).prod (isCompact_closedBall (0 : ℂ) 1)
  obtain ⟨C, hC⟩ := hT.exists_bound_of_continuousOn hcont
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro a ha z hz hza
  obtain ⟨H, hH, hHeq⟩ := kerK1_exists_holomorphic_extension isOpen_ball hf hi (hsmall ha)
  have hcl : closedBall (0 : ℂ) ρ ⊆ ball 0 R := by
    intro w hw
    exact mem_ball_zero_iff.mpr ((mem_closedBall_zero_iff.mp hw).trans_lt hρR)
  have hfront : ∀ w ∈ frontier (ball (0 : ℂ) ρ), ‖H w‖ ≤ max C 0 := by
    intro w hw
    have hws : w ∈ sphere (0 : ℂ) ρ := frontier_ball_subset_sphere hw
    rw [hHeq w (houter hws) (hne (w, a) ⟨hws, ha⟩)]
    exact (hC (w, a) ⟨hws, ha⟩).trans (le_max_left _ _)
  have hzc : z ∈ closure (ball (0 : ℂ) ρ) := by
    exact subset_closure (mem_ball_zero_iff.mpr ((mem_closedBall_zero_iff.mp hz).trans_lt hρ1))
  have hbound := Complex.norm_le_of_forall_mem_frontier_norm_le isBounded_ball
    (hH.diffContOnCl_ball hcl) hfront hzc
  rwa [hHeq z (hsmall hz) hza] at hbound

/-- The squared Grunsky-kernel row integrals of a function univalent across
the closed disk have a finite bound independent of the second variable. -/
theorem kerK1_row_integral_bound_of_extension {f : ℂ → ℂ} {R : ℝ} (hR : 1 < R)
    (hf : DifferentiableOn ℂ f (ball 0 R)) (hi : InjOn f (ball 0 R)) :
    ∃ M : ℝ≥0∞, M < ∞ ∧ ∀ a ∈ closedBall (0 : ℂ) 1,
      (∫⁻ w in unitDisc, (‖kerK1 f w a‖₊ : ℝ≥0∞) ^ 2) ≤ M := by
  obtain ⟨C, hC0, hC⟩ := kerK1_uniform_bound_of_extension hR hf hi
  refine ⟨ENNReal.ofReal C ^ 2 * (NNReal.pi : ℝ≥0∞), by finiteness, ?_⟩
  intro a ha
  have hpoint : ∀ᵐ w ∂(volume.restrict unitDisc),
      (‖kerK1 f w a‖₊ : ℝ≥0∞) ^ 2 ≤ ENNReal.ofReal C ^ 2 := by
    filter_upwards [ae_restrict_mem (isOpen_ball.measurableSet),
      (volume.restrict unitDisc).ae_ne a] with w hw hwa
    have hnorm : (‖kerK1 f w a‖₊ : ℝ≥0∞) ≤ ENNReal.ofReal C := by
      rw [← ENNReal.ofReal_coe_nnreal]
      exact ENNReal.ofReal_le_ofReal (hC a ha w (ball_subset_closedBall hw) hwa)
    exact pow_le_pow_left' hnorm 2
  calc
    (∫⁻ w in unitDisc, (‖kerK1 f w a‖₊ : ℝ≥0∞) ^ 2) ≤
        ∫⁻ _ in unitDisc, ENNReal.ofReal C ^ 2 := lintegral_mono_ae hpoint
    _ = ENNReal.ofReal C ^ 2 * (NNReal.pi : ℝ≥0∞) := by
      rw [setLIntegral_const]
      simp [unitDisc]

/-- The finite uniform row bound yields the weighted kernel boundary limit. -/
theorem kerK1_weighted_row_boundary_of_extension {f : ℂ → ℂ} {R : ℝ} (hR : 1 < R)
    (hf : DifferentiableOn ℂ f (ball 0 R)) (hi : InjOn f (ball 0 R)) :
    Tendsto (fun a => ENNReal.ofReal ((1 - ‖a‖ ^ 2) ^ 2) *
      ∫⁻ w in unitDisc, (‖kerK1 f w a‖₊ : ℝ≥0∞) ^ 2)
      (comap (fun z : ℂ => ‖z‖) (𝓝[<] 1)) (𝓝 0) := by
  obtain ⟨M, hM, hbound⟩ := kerK1_row_integral_bound_of_extension hR hf hi
  let l := comap (fun z : ℂ => ‖z‖) (𝓝[<] (1 : ℝ))
  have hnorm : Tendsto (fun z : ℂ => ‖z‖) l (𝓝 1) :=
    tendsto_comap.mono_right nhdsWithin_le_nhds
  have hreal : Tendsto (fun z : ℂ => (1 - ‖z‖ ^ 2) ^ 2) l (𝓝 0) := by
    simpa using ((tendsto_const_nhds (x := (1 : ℝ))).sub (hnorm.pow 2)).pow 2
  have hzero : Tendsto (fun z : ℂ => ENNReal.ofReal ((1 - ‖z‖ ^ 2) ^ 2)) l (𝓝 0) := by
    simpa only [ENNReal.ofReal_zero] using ENNReal.tendsto_ofReal hreal
  have hupper : Tendsto (fun z : ℂ => ENNReal.ofReal ((1 - ‖z‖ ^ 2) ^ 2) * M) l (𝓝 0) := by
    simpa only [zero_mul] using ENNReal.Tendsto.mul_const hzero (Or.inr hM.ne)
  have hlt : ∀ᶠ z : ℂ in l, ‖z‖ < 1 := tendsto_comap.eventually self_mem_nhdsWithin
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper
    (Eventually.of_forall fun _ => bot_le)
  filter_upwards [hlt] with z hz
  gcongr; exact hbound z (mem_closedBall_zero_iff.mpr hz.le)

/-- The corrected Grunsky kernel is symmetric, including its removable diagonal. -/
theorem kerK1_symm (f : ℂ → ℂ) (z w : ℂ) : kerK1 f z w = kerK1 f w z := by
  by_cases h : z = w
  · subst w
    rfl
  · rw [kerK1_of_ne f h, kerK1_of_ne f (Ne.symm h)]
    have hzw : (z - w) ^ 2 = (w - z) ^ 2 := by ring
    have hfw : (f z - f w) ^ 2 = (f w - f z) ^ 2 := by ring
    rw [hzw, hfw, mul_comm (deriv f z) (deriv f w)]

/-- Two divided differences give the corrected kernel, including the
Schwarzian value on the diagonal. -/
theorem kerK1_eq_divided_difference {f : ℂ → ℂ} {U : Set ℂ}
    (hU : IsOpen U) (hf : DifferentiableOn ℂ f U) (hi : InjOn f U)
    {a z : ℂ} (ha : a ∈ U) (hz : z ∈ U) :
    let d := dslope f a
    let q := dslope d a
    kerK1 f z a = (q z ^ 2 - deriv f a * deriv q z) / (π * d z ^ 2) := by
  let d := dslope f a
  let q := dslope d a
  change kerK1 f z a = (q z ^ 2 - deriv f a * deriv q z) / (π * d z ^ 2)
  have hpi : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hd : DifferentiableOn ℂ d U := (Complex.differentiableOn_dslope (hU.mem_nhds ha)).mpr hf
  have hq : DifferentiableOn ℂ q U := (Complex.differentiableOn_dslope (hU.mem_nhds ha)).mpr hd
  by_cases hza : z = a
  · subst z
    have hA := hf.analyticAt (hU.mem_nhds ha)
    have hfa : deriv f a ≠ 0 := LiZhongQC.deriv_ne_zero_of_injOn hU hf hi ha
    have hda : d a = deriv f a := dslope_same f a
    have hqa : q a = deriv (deriv f) a / 2 := by
      dsimp only [q]
      rw [dslope_same]
      exact kn_deriv_dslope_same hA
    have hqa' : deriv q a = deriv (deriv (deriv f)) a / 6 := by
      dsimp only [q, d]
      rw [kn_deriv_dslope_same (kn_analyticAt_dslope_same hA), kn_deriv2_dslope_same hA]
      ring
    have hlog : deriv (fun w => deriv (deriv f) w / deriv f w) a =
        (deriv (deriv (deriv f)) a * deriv f a - deriv (deriv f) a * deriv (deriv f) a) /
          deriv f a ^ 2 :=
      (hA.deriv.deriv.differentiableAt.hasDerivAt.div hA.deriv.differentiableAt.hasDerivAt hfa).deriv
    rw [kerK1_diag, hda, hqa, hqa']
    unfold schwarzianHol
    rw [hlog]
    field_simp [hpi, hfa]; ring
  · have hdn : d z ≠ 0 := by
      dsimp only [d]
      rw [dslope_of_ne f hza]
      change (z - a)⁻¹ * (f z - f a) ≠ 0
      exact mul_ne_zero (inv_ne_zero (sub_ne_zero.mpr hza))
        (sub_ne_zero.mpr (fun he => hza (hi hz ha he)))
    have hdval : d z = deriv f a + (z - a) * q z := by
      have h := sub_smul_dslope d a z
      change (z - a) * q z = d z - d a at h
      have hda : d a = deriv f a := dslope_same f a
      rw [hda] at h
      linear_combination -h
    have hfval : f z - f a = (z - a) * d z := by
      simpa only [d, smul_eq_mul] using (sub_smul_dslope f a z).symm
    have hdf := deriv_eq_dslope_add (hd.differentiableAt (hU.mem_nhds hz))
    have hdd := deriv_eq_dslope_add (hq.differentiableAt (hU.mem_nhds hz))
    change deriv f z = d z + (z - a) * deriv d z at hdf
    change deriv d z = q z + (z - a) * deriv q z at hdd
    rw [kerK1_of_ne f hza, hfval, hdf, hdd]
    field_simp [hpi, hdn, sub_ne_zero.mpr hza]
    rw [hdval]
    ring

/-- The corrected kernel, rather than only an almost-everywhere replacement,
is holomorphic in its first variable. -/
theorem differentiableOn_kerK1 {f : ℂ → ℂ} {U : Set ℂ}
    (hU : IsOpen U) (hf : DifferentiableOn ℂ f U) (hi : InjOn f U)
    {a : ℂ} (ha : a ∈ U) : DifferentiableOn ℂ (fun z => kerK1 f z a) U := by
  let d := dslope f a
  let q := dslope d a
  have hd : DifferentiableOn ℂ d U := (Complex.differentiableOn_dslope (hU.mem_nhds ha)).mpr hf
  have hq : DifferentiableOn ℂ q U := (Complex.differentiableOn_dslope (hU.mem_nhds ha)).mpr hd
  have hdne (z : ℂ) (hz : z ∈ U) : d z ≠ 0 := by
    by_cases hza : z = a
    · subst z
      simpa only [d, dslope_same] using LiZhongQC.deriv_ne_zero_of_injOn hU hf hi ha
    · dsimp only [d]
      rw [dslope_of_ne f hza]
      change (z - a)⁻¹ * (f z - f a) ≠ 0
      exact mul_ne_zero (inv_ne_zero (sub_ne_zero.mpr hza))
        (sub_ne_zero.mpr (fun he => hza (hi hz ha he)))
  have hpi : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hH : DifferentiableOn ℂ
      (fun z => (q z ^ 2 - deriv f a * deriv q z) / (π * d z ^ 2)) U :=
    ((hq.pow 2).sub ((hq.deriv hU).const_mul (deriv f a))).div
      ((hd.pow 2).const_mul (π : ℂ)) (fun z hz => mul_ne_zero hpi (pow_ne_zero 2 (hdne z hz)))
  exact (differentiableOn_congr (fun z hz => kerK1_eq_divided_difference hU hf hi ha hz)).mpr hH

/-- Kernels of functions univalent across the closed disk have genuine
holomorphic square-integrable rows, including at diagonal points. -/
theorem kerK1_row_mem_A21_of_extension {f : ℂ → ℂ} {R : ℝ} (hR : 1 < R)
    (hf : DifferentiableOn ℂ f (ball 0 R)) (hi : InjOn f (ball 0 R))
    {a : ℂ} (ha : a ∈ closedBall (0 : ℂ) 1) :
    (fun z => kerK1 f z a) ∈ A21fun unitDisc := by
  have haR : a ∈ ball (0 : ℂ) R :=
    mem_ball_zero_iff.mpr ((mem_closedBall_zero_iff.mp ha).trans_lt hR)
  refine ⟨(differentiableOn_kerK1 isOpen_ball hf hi haR).mono (ball_subset_ball hR.le), ?_⟩
  obtain ⟨M, hM, hbound⟩ := kerK1_row_integral_bound_of_extension hR hf hi
  have hI : (∫⁻ z in unitDisc, (‖kerK1 f z a‖₊ : ℝ≥0∞) ^ 2) < ∞ :=
    (hbound a ha).trans_lt hM
  change (∫⁻ z in unitDisc, (‖kerK1 f z a‖₊ : ℝ≥0∞) ^ 2) ^ (1 / 2 : ℝ) < ∞
  finiteness

/-- Each radial approximation has square-integrable holomorphic kernel rows. -/
theorem dilateF_kernel_row_mem_A21 {f : ℂ → ℂ} (hf : IsUnivalentDisc f)
    {n : ℕ} (hn : 1 ≤ n) {a : ℂ} (ha : a ∈ closedBall (0 : ℂ) 1) :
    (fun z => kerK1 (dilateF f n) z a) ∈ A21fun unitDisc := by
  obtain ⟨hR, hd, hi⟩ := dilateF_extension hf hn
  exact kerK1_row_mem_A21_of_extension hR hd hi ha

/-- The identity map has identically zero Grunsky kernel, also on the diagonal. -/
theorem kerK1_id (z w : ℂ) : kerK1 id z w = 0 := by
  by_cases h : z = w
  · subst w
    rw [kerK1_diag]
    simp [schwarzianHol]
  · rw [kerK1_of_ne id h]
    simp

/-- (TT:6076) Brazilevic's distance from the identity uses the kernel itself. -/
theorem brazF_id_formula (f : ℂ → ℂ) (z : ℂ) :
    brazF f id z = ENNReal.ofReal (Real.sqrt π * (1 - ‖z‖ ^ 2)) *
      (∫⁻ w in unitDisc, (‖kerK1 f z w‖₊ : ℝ≥0∞) ^ 2) ^ (1 / 2 : ℝ) := by
  simp only [brazF, kerK1_id, sub_zero]

/-- (TT:6226–6236) For normalized `f ∈ 𝒰` and `n ≥ 1`, `f_n` is a normalized univalent function, analytic on a
neighbourhood of `𝔻̄`, with:
- `(1 - |z|²)² 𝒮(f_n)(z) → 0` as `|z| → 1⁻`;
- `(1 - |ζ|²)² 𝖪₁(f_n)(ζ, ζ) → 0` as `|ζ| → 1⁻`. -/
theorem dilateF_spec {f : ℂ → ℂ} (hf : IsUnivalentDisc f) (h0 : f 0 = 0) (h1 : deriv f 0 = 1) {n : ℕ} (hn : 1 ≤ n) :
    IsUnivalentDisc (dilateF f n) ∧ dilateF f n 0 = 0 ∧ deriv (dilateF f n) 0 = 1 ∧
      Tendsto (fun z => ((1 - ‖z‖ ^ 2) ^ 2 : ℂ) * schwarzianHol (dilateF f n) z) (comap (fun z : ℂ => ‖z‖) (𝓝[<] 1))
        (𝓝 0) ∧
      Tendsto (fun ζ => ENNReal.ofReal ((1 - ‖ζ‖ ^ 2) ^ 2) * ∫⁻ w in unitDisc, (‖kerK1 (dilateF f n) w ζ‖₊ : ℝ≥0∞) ^ 2)
        (comap (fun z : ℂ => ‖z‖) (𝓝[<] 1)) (𝓝 0) := by
  obtain ⟨hu, hz, hd⟩ := dilateF_normalized hf h0 h1 hn
  obtain ⟨hR, hdiff, hinj⟩ := dilateF_extension hf hn
  exact ⟨hu, hz, hd, dilateF_schwarzian_boundary hf hn,
    kerK1_weighted_row_boundary_of_extension hR hdiff hinj⟩

/-- Radial dilation of the actual Grunsky kernel acts diagonally on both
Bergman indices, with exponent `m+1` and `n+1`. -/
theorem kerK1_dilateF_bergman_series {f : ℂ → ℂ} (hf : IsUnivalentDisc f)
    {B : ℕ → ℕ → ℂ}
    (hK : ∀ z ∈ unitDisc, ∀ w ∈ unitDisc, z ≠ w →
      HasSum (fun p : ℕ × ℕ => B p.1 p.2 * basisE p.1 z * basisE p.2 w) (kerK1 f z w))
    {n : ℕ} (hn : 1 ≤ n) {z w : ℂ} (hz : z ∈ unitDisc) (hw : w ∈ unitDisc)
    (hzw : z ≠ w) :
    HasSum (fun p : ℕ × ℕ => b7Matrix ((n : ℝ) / (n + 1)) B p.1 p.2 *
      basisE p.1 z * basisE p.2 w) (kerK1 (dilateF f n) z w) := by
  have hr0 : (n : ℂ) / (n + 1) ≠ 0 := div_ne_zero
    (by exact_mod_cast (show n ≠ 0 by omega))
    (by exact_mod_cast (show (n : ℝ) + 1 ≠ 0 by positivity))
  have hneq : (n : ℂ) / (n + 1) * z ≠ (n : ℂ) / (n + 1) * w :=
    fun he => hzw (mul_left_cancel₀ hr0 he)
  have hs := (hK _ (dilateF_argument_mem n hz) _ (dilateF_argument_mem n hw) hneq).mul_left
    (((n : ℂ) / (n + 1)) ^ 2)
  rw [← kerK1_dilateF hf hn hz hw] at hs
  apply hs.congr_fun
  intro p
  simp only [b7Matrix, Complex.ofReal_div, Complex.ofReal_add, Complex.ofReal_natCast,
    Complex.ofReal_one, basisE, mul_pow, pow_succ]
  ring

/-- **Lemma B.7** (TT:6238–6278). For normalized `f ∈ 𝒰`, `K₁(f_n) → K₁(f)` in the strong operator topology on
`A₂¹(𝔻)`. -/
theorem lemma_B_7 {f : ℂ → ℂ} (hf : IsUnivalentDisc f) (h0 : f 0 = 0) (h1 : deriv f 0 = 1) {ψ : ℂ → ℂ}
    (hψ : ψ ∈ A21fun unitDisc) :
    Tendsto (fun n => normA21 unitDisc fun z =>
      (∫ w in unitDisc, kerK1 (dilateF f n) z w * conj (ψ w)) - ∫ w in unitDisc, kerK1 f z w * conj (ψ w)) atTop (𝓝 0) := by
  clear h0
  obtain ⟨B, hsym, hrow, hB, hK⟩ := b7_grunsky_model hf.1 hf.2 h1
  let r : ℕ → ℝ := fun n => (n : ℝ) / (n + 1)
  have hr0 : ∀ n, 0 ≤ r n := by intro n; dsimp [r]; positivity
  have hr1 : ∀ n, r n ≤ 1 := by
    intro n
    dsimp [r]
    apply (div_le_one (by positivity)).mpr
    linarith
  have hr : Tendsto r atTop (𝓝 1) := tendsto_natCast_div_add_atTop (1 : ℝ)
  exact b7_kernel_strong hsym hrow hB hK hr0 hr1 hr
    (fun n hn z hz w hw hzw => kerK1_dilateF_bergman_series hf hK hn hz hw hzw) hψ

-- `remark_B_9` moved to `Appendix/PeriodCompactCharacterization.lean` (2026-10-28).

/-- (TT:6436–6441) A localized Cauchy estimate for the derivative near the
unit circle. Only values in the outer annulus enter the bound. -/
theorem weighted_deriv_annulus_bound {ψ : ℂ → ℂ} (hψ : DifferentiableOn ℂ ψ unitDisc)
    {a C : ℝ} (_hC : 0 ≤ C)
    (hb : ∀ w ∈ unitDisc, a < ‖w‖ → (1 - ‖w‖ ^ 2) * ‖ψ w‖ ≤ C)
    {z : ℂ} (hz : z ∈ unitDisc) (hza : (2 * a + 1) / 3 < ‖z‖) :
    (1 - ‖z‖ ^ 2) ^ 2 * ‖deriv ψ z‖ ≤ 16 * C := by
  let R : ℝ := (1 - ‖z‖) / 2
  have hzn : ‖z‖ < 1 := mem_ball_zero_iff.mp hz
  have hR : 0 < R := by dsimp [R]; linarith
  have hball (w : ℂ) (hw : w ∈ closedBall z R) :
      w ∈ unitDisc ∧ a < ‖w‖ ∧ R ≤ 1 - ‖w‖ ^ 2 := by
    have hdist : ‖w - z‖ ≤ R := by simpa only [mem_closedBall, dist_eq_norm] using hw
    have huw : ‖w‖ ≤ R + ‖z‖ := by
      have ht := norm_le_insert' w z
      linarith
    have hlw : ‖z‖ ≤ ‖w‖ + R := by
      have ht := norm_le_insert' z w
      rw [norm_sub_rev] at ht
      exact ht.trans (add_le_add_right hdist _)
    have hwn : ‖w‖ < 1 := by dsimp [R] at huw; linarith
    have hwr : R ≤ 1 - ‖w‖ := by dsimp [R] at huw ⊢; linarith
    refine ⟨mem_ball_zero_iff.mpr hwn, ?_, ?_⟩
    · dsimp [R] at hlw
      linarith
    · nlinarith [norm_nonneg w, mul_nonneg (norm_nonneg w) (sub_nonneg.mpr hwn.le)]
  have hd := hψ.diffContOnCl_ball (fun w hw => (hball w hw).1)
  have hbnd : ∀ w ∈ sphere z R, ‖ψ w‖ ≤ C / R := by
    intro w hw
    obtain ⟨hwd, hwa, hwr⟩ := hball w (sphere_subset_closedBall hw)
    apply (le_div_iff₀ hR).mpr
    simpa only [mul_comm R] using
      (mul_le_mul_of_nonneg_right hwr (norm_nonneg (ψ w))).trans (hb w hwd hwa)
  have hc := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hR hd hbnd
  have hc1 := (le_div_iff₀ hR).mp hc
  have hc2 := (le_div_iff₀ hR).mp hc1
  have hfac : (1 - ‖z‖ ^ 2) ^ 2 ≤ 16 * R ^ 2 := by
    have ht : (1 + ‖z‖) ^ 2 ≤ 4 := by nlinarith [norm_nonneg z]
    have hm := mul_le_mul_of_nonneg_left ht (sq_nonneg (1 - ‖z‖))
    dsimp [R]
    nlinarith [hm]
  have hm := mul_le_mul_of_nonneg_right hfac (norm_nonneg (deriv ψ z))
  nlinarith

/-- (TT:6436–6441) A holomorphic function with vanishing weighted boundary
values has a derivative with vanishing weight squared. -/
theorem weighted_deriv_boundary {ψ : ℂ → ℂ} (hψ : DifferentiableOn ℂ ψ unitDisc)
    (h0 : Tendsto (fun z => ((1 - ‖z‖ ^ 2 : ℝ) : ℂ) * ψ z)
      (comap (fun z : ℂ => ‖z‖) (𝓝[<] 1)) (𝓝 0)) :
    Tendsto (fun z => ((1 - ‖z‖ ^ 2) ^ 2 : ℂ) * deriv ψ z)
      (comap (fun z : ℂ => ‖z‖) (𝓝[<] 1)) (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hsmall : ∀ᶠ w : ℂ in comap (fun z : ℂ => ‖z‖) (𝓝[<] (1 : ℝ)),
      ‖(((1 - ‖w‖ ^ 2 : ℝ) : ℂ) * ψ w)‖ < ε / 32 := by
    simpa only [mem_ball, dist_zero_right] using
      h0.eventually (Metric.ball_mem_nhds (0 : ℂ) (by positivity : 0 < ε / 32))
  obtain ⟨s, hs, hsub⟩ := Filter.mem_comap.mp hsmall
  obtain ⟨a, ha, has⟩ := mem_nhdsLT_iff_exists_Ioo_subset.mp hs
  have hb : ∀ w ∈ unitDisc, a < ‖w‖ → (1 - ‖w‖ ^ 2) * ‖ψ w‖ ≤ ε / 32 := by
    intro w hw hwa
    have hwn : ‖w‖ < 1 := mem_ball_zero_iff.mp hw
    have hp : 0 ≤ 1 - ‖w‖ ^ 2 := by nlinarith [norm_nonneg w]
    have hh := hsub (has ⟨hwa, hwn⟩)
    change ‖(((1 - ‖w‖ ^ 2 : ℝ) : ℂ) * ψ w)‖ < ε / 32 at hh
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hp] at hh
    exact hh.le
  have hnorm : Tendsto (fun z : ℂ => ‖z‖)
      (comap (fun z : ℂ => ‖z‖) (𝓝[<] (1 : ℝ))) (𝓝 1) :=
    tendsto_comap.mono_right nhdsWithin_le_nhds
  have ha' : (2 * a + 1) / 3 < 1 := by change a < 1 at ha; linarith
  have hgt := hnorm.eventually (eventually_gt_nhds ha')
  have hlt : ∀ᶠ z : ℂ in comap (fun z : ℂ => ‖z‖) (𝓝[<] (1 : ℝ)), ‖z‖ < 1 :=
    tendsto_comap.eventually self_mem_nhdsWithin
  filter_upwards [hgt, hlt] with z hza hz
  have hbound := weighted_deriv_annulus_bound hψ (by positivity : 0 ≤ ε / 32)
    hb (mem_ball_zero_iff.mpr hz) hza
  rw [dist_zero_right, norm_mul]
  have hfac : ‖((1 - ‖z‖ ^ 2) ^ 2 : ℂ)‖ = (1 - ‖z‖ ^ 2) ^ 2 := by
    norm_cast
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  rw [hfac]
  linarith

/-- (TT:6436–6441) The remaining arrow of the final diagram: `Ψ(A_∞^{1,0}(𝔻)) ⊂ A_∞⁰(𝔻)`. If `ψ` is holomorphic on
`𝔻` with `(1 - |z|²) ψ(z)` bounded and tending to `0` as `|z| → 1⁻`, then `(1 - |z|²)² (ψ' - ½ψ²)(z) → 0`. -/
theorem psi_A1inf0 {ψ : ℂ → ℂ} (hψ : DifferentiableOn ℂ ψ unitDisc) (hb : ∃ C, ∀ z ∈ unitDisc, (1 - ‖z‖ ^ 2) * ‖ψ z‖ ≤ C)
    (h0 : Tendsto (fun z => ((1 - ‖z‖ ^ 2 : ℝ) : ℂ) * ψ z) (comap (fun z : ℂ => ‖z‖) (𝓝[<] 1)) (𝓝 0)) :
    Tendsto (fun z => ((1 - ‖z‖ ^ 2) ^ 2 : ℂ) * PsiOp ψ z) (comap (fun z : ℂ => ‖z‖) (𝓝[<] 1)) (𝓝 0) := by
  have _ := hb
  have hd := weighted_deriv_boundary hψ h0
  have hsq := (h0.pow 2).const_mul (1 / 2 : ℂ)
  convert hd.sub hsq using 1
  · funext z
    dsimp only [PsiOp]
    push_cast
    ring
  · norm_num

/-- The first inequality of Lemma B.5 follows from the sharp Bergman
point-evaluation bound and the corrected kernel diagonal. -/
theorem brazF_schwarzian_lower {f₁ f₂ : ℂ → ℂ}
    (h₁ : IsUnivalentDisc f₁) (h₂ : IsUnivalentDisc f₂)
    {z : ℂ} (hz : z ∈ unitDisc) :
    ENNReal.ofReal ((1 - ‖z‖ ^ 2) ^ 2 * ‖schwarzianHol f₁ z - schwarzianHol f₂ z‖) ≤
      6 * brazF f₁ f₂ z := by
  let κ : ℂ → ℂ := fun w => kerK1 f₁ w z - kerK1 f₂ w z
  let δ : ℝ := 1 - ‖z‖ ^ 2
  let s : ℝ := Real.sqrt π
  have hδ : 0 < δ := by
    have hzn : ‖z‖ < 1 := mem_ball_zero_iff.mp hz
    dsimp only [δ]
    nlinarith [norm_nonneg z]
  have hs : 0 < s := Real.sqrt_pos.mpr Real.pi_pos
  have hs2 : s ^ 2 = π := Real.sq_sqrt Real.pi_nonneg
  have hD : DifferentiableOn ℂ κ unitDisc :=
    (differentiableOn_kerK1 isOpen_ball h₁.1 h₁.2 hz).sub
      (differentiableOn_kerK1 isOpen_ball h₂.1 h₂.2 hz)
  have hF : brazF f₁ f₂ z = ENNReal.ofReal (s * δ) * normA21 unitDisc κ := by
    simp only [brazF, normA21, κ, δ, s, kerK1_symm f₁ z, kerK1_symm f₂ z]
  by_cases hN : normA21 unitDisc κ < ∞
  · let N : ℝ := (normA21 unitDisc κ).toReal
    have hN0 : 0 ≤ N := ENNReal.toReal_nonneg
    have hNc : ENNReal.ofReal N = normA21 unitDisc κ := ENNReal.ofReal_toReal hN.ne
    have hp := a21_disc_pointwise ⟨hD, hN⟩ hz
    have hdiag : κ z = -(schwarzianHol f₁ z - schwarzianHol f₂ z) / (6 * (π : ℂ)) := by
      dsimp only [κ]
      rw [kerK1_diag, kerK1_diag]
      ring
    have hfac : ‖(1 - ‖z‖ ^ 2 : ℂ)‖ = δ := by
      norm_cast
      exact abs_of_pos hδ
    have hval : ‖(1 - ‖z‖ ^ 2) * κ z‖ =
        δ * ‖schwarzianHol f₁ z - schwarzianHol f₂ z‖ / (6 * π) := by
      rw [hdiag, norm_mul, norm_div, norm_neg, hfac]
      norm_num [norm_mul, Complex.norm_real, Real.norm_eq_abs, Real.pi_pos.le]
      ring
    rw [hval, ← hNc, ← ENNReal.ofReal_mul (by positivity : 0 ≤ 1 / Real.sqrt π)] at hp
    have hreal : δ * ‖schwarzianHol f₁ z - schwarzianHol f₂ z‖ / (6 * π) ≤ (1 / s) * N :=
      (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hp
    have hlin : δ * ‖schwarzianHol f₁ z - schwarzianHol f₂ z‖ ≤ 6 * s * N := by
      have h := (div_le_iff₀ (by positivity : (0 : ℝ) < 6 * π)).mp hreal
      have he : (1 / s) * N * (6 * π) = 6 * s * N := by
        rw [← hs2]
        field_simp
      exact h.trans_eq he
    have hfinal : δ ^ 2 * ‖schwarzianHol f₁ z - schwarzianHol f₂ z‖ ≤ 6 * (s * δ) * N := by
      have h := mul_le_mul_of_nonneg_left hlin hδ.le
      nlinarith
    change ENNReal.ofReal (δ ^ 2 * ‖schwarzianHol f₁ z - schwarzianHol f₂ z‖) ≤ _
    rw [hF]
    calc
      ENNReal.ofReal (δ ^ 2 * ‖schwarzianHol f₁ z - schwarzianHol f₂ z‖) ≤
          ENNReal.ofReal (6 * (s * δ) * N) := ENNReal.ofReal_le_ofReal hfinal
      _ = 6 * (ENNReal.ofReal (s * δ) * normA21 unitDisc κ) := by
        rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity), hNc]
        norm_num [mul_assoc]
  · have ht : normA21 unitDisc κ = ∞ := top_le_iff.mp (not_lt.mp hN)
    have hfac : ENNReal.ofReal (s * δ) ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.mpr (mul_pos hs hδ))
    rw [hF, ht, ENNReal.mul_top hfac]
    simp

/-- The area norm is the genuine extended L2 norm on measurable functions. -/
theorem normA21_eq_eLpNorm {D : Set ℂ} {ψ : ℂ → ℂ}
    (hψ : AEStronglyMeasurable ψ (volume.restrict D)) :
    normA21 D ψ = eLpNorm ψ 2 (volume.restrict D) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) hψ]
  norm_num [normA21, enorm_eq_nnnorm]

/-- The extended area norm satisfies Minkowski's inequality. -/
theorem normA21_add_le {D : Set ℂ} {ψ φ : ℂ → ℂ}
    (hψ : AEStronglyMeasurable ψ (volume.restrict D))
    (hφ : AEStronglyMeasurable φ (volume.restrict D)) :
    normA21 D (ψ + φ) ≤ normA21 D ψ + normA21 D φ := by
  rw [normA21_eq_eLpNorm (hψ.add hφ), normA21_eq_eLpNorm hψ, normA21_eq_eLpNorm hφ]
  exact eLpNorm_add_le (by norm_num)

/-- Symmetry gives holomorphy of the corrected kernel in its second variable. -/
theorem differentiableOn_kerK1_right {f : ℂ → ℂ} {U : Set ℂ}
    (hU : IsOpen U) (hf : DifferentiableOn ℂ f U) (hi : InjOn f U)
    {a : ℂ} (ha : a ∈ U) : DifferentiableOn ℂ (fun z => kerK1 f a z) U := by
  have he : (fun z => kerK1 f a z) = (fun z => kerK1 f z a) := funext (kerK1_symm f a)
  rw [he]
  exact differentiableOn_kerK1 hU hf hi ha

/-- Brazilevic's pointwise distance is symmetric. -/
theorem brazF_symm (f g : ℂ → ℂ) (z : ℂ) : brazF f g z = brazF g f z := by
  unfold brazF
  congr 2
  apply lintegral_congr_ae
  filter_upwards [] with w
  have hn : ‖kerK1 f z w - kerK1 g z w‖₊ = ‖kerK1 g z w - kerK1 f z w‖₊ := by
    apply Subtype.ext
    exact norm_sub_rev _ _
  rw [hn]

/-- The pointwise distance of a function to itself is zero. -/
theorem brazF_self (f : ℂ → ℂ) (z : ℂ) : brazF f f z = 0 := by
  norm_num [brazF]

/-- (TT:6064–6072) Minkowski's inequality gives the pointwise triangle inequality. -/
theorem brazF_triangle {f₁ f₂ f₃ : ℂ → ℂ}
    (h₁ : IsUnivalentDisc f₁) (h₂ : IsUnivalentDisc f₂) (h₃ : IsUnivalentDisc f₃)
    {z : ℂ} (hz : z ∈ unitDisc) :
    brazF f₁ f₃ z ≤ brazF f₁ f₂ z + brazF f₂ f₃ z := by
  have hmeas : MeasurableSet unitDisc := isOpen_ball.measurableSet
  have hm₁ := (differentiableOn_kerK1_right isOpen_ball h₁.1 h₁.2 hz).continuousOn.aestronglyMeasurable (μ := volume) hmeas
  have hm₂ := (differentiableOn_kerK1_right isOpen_ball h₂.1 h₂.2 hz).continuousOn.aestronglyMeasurable (μ := volume) hmeas
  have hm₃ := (differentiableOn_kerK1_right isOpen_ball h₃.1 h₃.2 hz).continuousOn.aestronglyMeasurable (μ := volume) hmeas
  have hn := normA21_add_le (hm₁.sub hm₂) (hm₂.sub hm₃)
  let c : ℝ≥0∞ := ENNReal.ofReal (Real.sqrt π * (1 - ‖z‖ ^ 2))
  change c * normA21 unitDisc (fun w => kerK1 f₁ z w - kerK1 f₃ z w) ≤
    c * normA21 unitDisc (fun w => kerK1 f₁ z w - kerK1 f₂ z w) +
      c * normA21 unitDisc (fun w => kerK1 f₂ z w - kerK1 f₃ z w)
  have he : (fun w => kerK1 f₁ z w - kerK1 f₃ z w) =
      (fun w => kerK1 f₁ z w - kerK1 f₂ z w) + (fun w => kerK1 f₂ z w - kerK1 f₃ z w) := by
    funext w
    simp only [Pi.add_apply]
    ring
  rw [he, ← mul_add]
  gcongr; exact hn

/-- The supremum distance is symmetric. -/
theorem brazD_symm (f g : ℂ → ℂ) : brazD f g = brazD g f := by
  simp only [brazD, brazF_symm f g]

/-- The supremum distance of a function to itself is zero. -/
theorem brazD_self (f : ℂ → ℂ) : brazD f f = 0 := by
  simp only [brazD, brazF_self]
  exact le_antisymm (iSup_le fun z => iSup_le fun _ => le_rfl) bot_le

/-- (TT:6072) The extended supremum distance satisfies the triangle inequality. -/
theorem brazD_triangle {f₁ f₂ f₃ : ℂ → ℂ}
    (h₁ : IsUnivalentDisc f₁) (h₂ : IsUnivalentDisc f₂) (h₃ : IsUnivalentDisc f₃) :
    brazD f₁ f₃ ≤ brazD f₁ f₂ + brazD f₂ f₃ := by
  apply iSup_le
  intro z
  apply iSup_le
  intro hz
  apply (brazF_triangle h₁ h₂ h₃ hz).trans
  apply add_le_add
  · exact le_iSup_of_le z (le_iSup_of_le hz le_rfl)
  · exact le_iSup_of_le z (le_iSup_of_le hz le_rfl)

/-- The Schwarzian supremum inequality in Remark B.6 follows from the first
inequality of Lemma B.5 without assuming any operator norm bound. -/
theorem brazD_schwarzian_bound {f₁ f₂ : ℂ → ℂ} (h₁ : IsUnivalentDisc f₁) (h₂ : IsUnivalentDisc f₂) :
    (⨆ z ∈ unitDisc, ENNReal.ofReal ((1 - ‖z‖ ^ 2) ^ 2 *
      ‖schwarzianHol f₁ z - schwarzianHol f₂ z‖)) ≤ 6 * brazD f₁ f₂ := by
  apply iSup_le
  intro z
  apply iSup_le
  intro hz
  have hlocal : brazF f₁ f₂ z ≤ brazD f₁ f₂ := by
    unfold brazD
    exact le_iSup_of_le z (le_iSup_of_le hz le_rfl)
  apply (brazF_schwarzian_lower h₁ h₂ hz).trans
  gcongr

/-- Zero Brazilevic distance forces equality of the Schwarzians on the disk. -/
theorem brazD_zero_schwarzian_eq {f₁ f₂ : ℂ → ℂ}
    (h₁ : IsUnivalentDisc f₁) (h₂ : IsUnivalentDisc f₂) (hzero : brazD f₁ f₂ = 0) :
    EqOn (schwarzianHol f₁) (schwarzianHol f₂) unitDisc := by
  intro z hz
  have hs := brazD_schwarzian_bound h₁ h₂
  have hp : ENNReal.ofReal ((1 - ‖z‖ ^ 2) ^ 2 *
      ‖schwarzianHol f₁ z - schwarzianHol f₂ z‖) ≤ 0 := by
    calc
      _ ≤ ⨆ w ∈ unitDisc, ENNReal.ofReal ((1 - ‖w‖ ^ 2) ^ 2 *
          ‖schwarzianHol f₁ w - schwarzianHol f₂ w‖) :=
        le_iSup_of_le z (le_iSup_of_le hz le_rfl)
      _ ≤ 6 * brazD f₁ f₂ := hs
      _ = 0 := by rw [hzero]; simp
  have hr := ENNReal.ofReal_eq_zero.mp (le_antisymm hp bot_le)
  have hw : 0 < (1 - ‖z‖ ^ 2) ^ 2 := by
    have hz1 : ‖z‖ < 1 := mem_ball_zero_iff.mp hz
    have hpos : 0 < 1 - ‖z‖ ^ 2 := by nlinarith [norm_nonneg z]
    exact pow_pos hpos 2
  have hn : ‖schwarzianHol f₁ z - schwarzianHol f₂ z‖ ≤ 0 := by
    by_contra hn
    exact (not_lt_of_ge hr) (mul_pos hw (lt_of_not_ge hn))
  exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm hn (norm_nonneg _)))


/-! ### Integral-operator bounds and completion of Lemma B.5 -/

theorem kerOpNorm_kerK1_le_one {f : ℂ → ℂ} (hf : IsUnivalentDisc f) :
    kerOpNorm (kerK1 f) ≤ 1 := by
  apply iSup_le
  intro ψ
  apply iSup_le
  intro hψ
  exact (kerK1_opNorm_le hf.1 hf.2 hψ.1).trans hψ.2

theorem kerK1_row_mem_A21_normalized {f : ℂ → ℂ} (hf : IsUnivalentDisc f)
    (hf0 : deriv f 0 = 1) {z : ℂ} (hz : z ∈ unitDisc) :
    (fun w => kerK1 f z w) ∈ A21fun unitDisc := by
  obtain ⟨a, hsym, hexp, hker⟩ := g2c_normalized_kernel_series_exists hf.1 hf.2 hf0
  let B : ℕ → ℕ → ℂ := fun m n =>
    (Real.sqrt (((m : ℝ) + 1) * ((n : ℝ) + 1)) : ℂ) * a (m + 1) (n + 1)
  have hB := g2c_grunsky_matrix_contraction hf.1 hf.2 hsym hexp
  have hsB : ∀ m n, B m n = B n m := by
    intro m n
    simp only [B, hsym (m + 1) (n + 1), mul_comm ((m : ℝ) + 1)]
  have hK : ∀ x ∈ unitDisc, ∀ w ∈ unitDisc, x ≠ w →
      HasSum (fun p : ℕ × ℕ => B p.1 p.2 * basisE p.1 x * basisE p.2 w) (kerK1 f x w) := by
    intro x hx w hw hxw
    have hh := (hker x hx w hw hxw).div_const (π : ℂ)
    have hp : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    rw [show ((π : ℂ) * kerK1 f x w) / (π : ℂ) = kerK1 f x w by field_simp] at hh
    exact hh.congr_fun (fun p => g2c_basis_weight a p.1 p.2 x w)
  let d : ℕ → ℂ := fun n => ∑' m, B n m * basisE m z
  have hd := (hB.2 (fun m => basisE m z) (basisE_sq_summable hz)).2.1
  let H : ℂ → ℂ := fun w => ∑' n, d n * basisE n w
  have hH : H ∈ A21fun unitDisc := (bergman_ell2_series hd).1
  have hconv (n : ℕ) : Summable (fun m => B n m * basisE m z) :=
    (bergman_pair_summable (hB.1 n).1 (basisE_sq_summable hz)).of_norm
  have he : (fun w => kerK1 f z w) =ᵐ[volume.restrict unitDisc] H := by
    filter_upwards [ae_restrict_mem isOpen_ball.measurableSet,
      (volume.restrict unitDisc).ae_ne z] with w hw hwz
    exact (g2c_kernel_row_series hsB hK hz hw (Ne.symm hwz) hconv).tsum_eq.symm
  apply (mem_A21fun_iff_memLp isOpen_ball.measurableSet).mpr
  exact ⟨differentiableOn_kerK1_right isOpen_ball hf.1 hf.2 hz,
    (a21_memLp_two isOpen_ball.measurableSet hH).ae_eq he.symm⟩

theorem kerK1_row_mem_A21 {f : ℂ → ℂ} (hf : IsUnivalentDisc f)
    {z : ℂ} (hz : z ∈ unitDisc) : (fun w => kerK1 f z w) ∈ A21fun unitDisc := by
  obtain ⟨F, hFd, hFi, hF0, hK⟩ := g2c_univalent_normalization hf.1 hf.2
  have hF := kerK1_row_mem_A21_normalized ⟨hFd, hFi⟩ hF0 hz
  apply (mem_A21fun_iff_memLp isOpen_ball.measurableSet).mpr
  exact ⟨differentiableOn_kerK1_right isOpen_ball hf.1 hf.2 hz,
    (a21_memLp_two isOpen_ball.measurableSet hF).ae_eq (hK z hz)⟩

theorem normA21_const_mul {D : Set ℂ} {ψ : ℂ → ℂ}
    (hψ : AEStronglyMeasurable ψ (volume.restrict D)) (c : ℂ) :
    normA21 D (fun z => c * ψ z) = (‖c‖₊ : ℝ≥0∞) * normA21 D ψ := by
  rw [normA21_eq_eLpNorm (hψ.const_mul c), normA21_eq_eLpNorm hψ]
  change eLpNorm (c • ψ) 2 (volume.restrict D) = _
  simpa only [enorm_eq_nnnorm] using
    eLpNorm_const_smul c ψ 2 (volume.restrict D)

theorem normalized_constant_A21 :
    (fun _ : ℂ => (Real.sqrt π : ℂ)⁻¹) ∈ A21fun unitDisc ∧
      normA21 unitDisc (fun _ : ℂ => (Real.sqrt π : ℂ)⁻¹) = 1 := by
  have hD : MeasurableSet unitDisc := isOpen_ball.measurableSet
  have : IsFiniteMeasure (volume.restrict unitDisc) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact measure_ball_lt_top⟩
  have hm : (fun _ : ℂ => (Real.sqrt π : ℂ)⁻¹) ∈ A21fun unitDisc :=
    (mem_A21fun_iff_memLp hD).mpr ⟨differentiableOn_const _, memLp_const _⟩
  refine ⟨hm, ?_⟩
  have hi : (∫ z in unitDisc, ‖(Real.sqrt π : ℂ)⁻¹‖ ^ 2) = 1 := by
    simp only [norm_inv, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _),
      inv_pow, Real.sq_sqrt Real.pi_nonneg, integral_const, smul_eq_mul]
    have hv : (volume.restrict unitDisc).real univ = π := by
      simp [Measure.real, unitDisc, Complex.volume_ball]
    rw [hv]
    exact mul_inv_cancel₀ Real.pi_ne_zero
  have hh := a21_norm_sq_eq_integral hD hm
  rw [hi, ENNReal.ofReal_one] at hh
  have hr := congrArg (fun x : ℝ≥0∞ => x ^ (1 / 2 : ℝ)) hh
  rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul] at hr
  norm_num at hr
  exact hr

def normalizedBergmanTest (z w : ℂ) : ℂ := (Real.sqrt π : ℂ)⁻¹ * deriv (blaschke z) w

theorem normalizedBergmanTest_spec {z : ℂ} (hz : z ∈ unitDisc) :
    normalizedBergmanTest z ∈ A21fun unitDisc ∧ normA21 unitDisc (normalizedBergmanTest z) = 1 := by
  have hc := isConformalOnto_blaschke (mem_ball_zero_iff.mp hz)
  exact ⟨a21_pullback isOpen_ball hc normalized_constant_A21.1,
    (normA21_pullback isOpen_ball hc (fun _ => (Real.sqrt π : ℂ)⁻¹)).trans
      normalized_constant_A21.2⟩

theorem normalizedBergmanTest_pairing {ψ : ℂ → ℂ} (hψ : ψ ∈ A21fun unitDisc)
    {z : ℂ} (hz : z ∈ unitDisc) :
    (∫ w in unitDisc, ψ w * conj (normalizedBergmanTest z w)) =
      (Real.sqrt π * (1 - ‖z‖ ^ 2) : ℂ) * ψ z := by
  have he : (fun w => ψ w * conj (normalizedBergmanTest z w)) =
      (fun w => (Real.sqrt π : ℂ)⁻¹ * (ψ w * conj (deriv (blaschke z) w))) := by
    ext w
    simp only [normalizedBergmanTest, map_mul, map_inv₀, conj_ofReal]
    ring
  rw [he, integral_const_mul, a21_blaschke_deriv_pairing hψ hz]
  have hs : (Real.sqrt π : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have hs2 : (Real.sqrt π : ℂ) ^ 2 = (π : ℂ) := by
    exact_mod_cast Real.sq_sqrt Real.pi_nonneg
  rw [← hs2]
  field_simp

theorem kerK1_difference_row_mem_A21 {f g : ℂ → ℂ}
    (hf : IsUnivalentDisc f) (hg : IsUnivalentDisc g) {z : ℂ} (hz : z ∈ unitDisc) :
    (fun w => kerK1 f z w - kerK1 g z w) ∈ A21fun unitDisc := by
  have h1 := kerK1_row_mem_A21 hf hz
  have h2 := kerK1_row_mem_A21 hg hz
  apply (mem_A21fun_iff_memLp isOpen_ball.measurableSet).mpr
  exact ⟨h1.1.sub h2.1, (a21_memLp_two isOpen_ball.measurableSet h1).sub
    (a21_memLp_two isOpen_ball.measurableSet h2)⟩

theorem brazF_le_kerOpNorm {f g : ℂ → ℂ} (hf : IsUnivalentDisc f)
    (hg : IsUnivalentDisc g) {z : ℂ} (hz : z ∈ unitDisc) :
    brazF f g z ≤ kerOpNorm (fun u w => kerK1 f u w - kerK1 g u w) := by
  let κ : ℂ → ℂ := fun w => kerK1 f z w - kerK1 g z w
  let c : ℝ := Real.sqrt π * (1 - ‖z‖ ^ 2)
  have hcn : 0 ≤ c := by
    have hz1 := mem_ball_zero_iff.mp hz
    have hd : 0 ≤ 1 - ‖z‖ ^ 2 := by nlinarith [norm_nonneg z]
    exact mul_nonneg (Real.sqrt_nonneg _) hd
  have hκ := kerK1_difference_row_mem_A21 hf hg hz
  have hκm := hκ.1.continuousOn.aestronglyMeasurable (μ := volume) isOpen_ball.measurableSet
  have he : ∀ u ∈ unitDisc,
      (∫ w in unitDisc, (kerK1 f u w - kerK1 g u w) * conj (normalizedBergmanTest z w)) =
        (c : ℂ) * κ u := by
    intro u hu
    have hh := normalizedBergmanTest_pairing (kerK1_difference_row_mem_A21 hf hg hu) hz
    simpa only [c, κ, kerK1_symm f u z, kerK1_symm g u z, Complex.ofReal_mul,
      Complex.ofReal_sub, Complex.ofReal_one, Complex.ofReal_pow] using hh
  have hnorm : normA21 unitDisc (fun u =>
      ∫ w in unitDisc, (kerK1 f u w - kerK1 g u w) * conj (normalizedBergmanTest z w)) =
        brazF f g z := by
    calc _ = normA21 unitDisc (fun u => (c : ℂ) * κ u) := by
          unfold normA21
          congr 1
          apply lintegral_congr_ae
          filter_upwards [ae_restrict_mem isOpen_ball.measurableSet] with u hu
          rw [he u hu]
      _ = ENNReal.ofReal c * normA21 unitDisc κ := by
          rw [normA21_const_mul hκm]
          congr 1
          rw [← enorm_eq_nnnorm, ← ofReal_norm, Complex.norm_real, Real.norm_of_nonneg hcn]
      _ = brazF f g z := rfl
  rw [← hnorm]
  exact le_iSup_of_le (normalizedBergmanTest z)
    (le_iSup_of_le ⟨(normalizedBergmanTest_spec hz).1, (normalizedBergmanTest_spec hz).2.le⟩ le_rfl)

theorem brazD_le_kerOpNorm {f g : ℂ → ℂ} (hf : IsUnivalentDisc f) (hg : IsUnivalentDisc g) :
    brazD f g ≤ kerOpNorm (fun z w => kerK1 f z w - kerK1 g z w) :=
  iSup_le fun _z => iSup_le fun hz => brazF_le_kerOpNorm hf hg hz

theorem brazD_id_le_one {f : ℂ → ℂ} (hf : IsUnivalentDisc f) : brazD f id ≤ 1 := by
  have hi : IsUnivalentDisc (id : ℂ → ℂ) := ⟨differentiableOn_id, Function.injective_id.injOn⟩
  have hh := brazD_le_kerOpNorm hf hi
  simp only [kerK1_id, sub_zero] at hh
  exact hh.trans (kerOpNorm_kerK1_le_one hf)

theorem kerK1_row_sq_le {f : ℂ → ℂ} (hf : IsUnivalentDisc f) {z : ℂ} (hz : z ∈ unitDisc) :
    (∫⁻ w in unitDisc, (‖kerK1 f z w‖₊ : ℝ≥0∞) ^ 2) ≤
      ENNReal.ofReal (1 / (π * (1 - ‖z‖ ^ 2) ^ 2)) := by
  let δ : ℝ := 1 - ‖z‖ ^ 2
  have hδ : 0 < δ := by
    have hh := mem_ball_zero_iff.mp hz
    dsimp [δ]
    nlinarith [norm_nonneg z]
  have hc : 0 ≤ Real.sqrt π * δ := mul_nonneg (Real.sqrt_nonneg _) hδ.le
  have hi : IsUnivalentDisc (id : ℂ → ℂ) := ⟨differentiableOn_id, Function.injective_id.injOn⟩
  have hF := brazF_le_kerOpNorm hf hi hz
  simp only [kerK1_id, sub_zero] at hF
  have hF1 := hF.trans (kerOpNorm_kerK1_le_one hf)
  rw [brazF_id_formula] at hF1
  change ENNReal.ofReal (Real.sqrt π * δ) * normA21 unitDisc (kerK1 f z) ≤ 1 at hF1
  have hs : (ENNReal.ofReal (Real.sqrt π * δ) * normA21 unitDisc (kerK1 f z)) ^ 2 ≤ 1 := by
    calc _ ≤ (1 : ℝ≥0∞) ^ 2 := pow_le_pow_left' hF1 2
      _ = 1 := one_pow _
  have hn : normA21 unitDisc (kerK1 f z) ^ 2 =
      ∫⁻ w in unitDisc, (‖kerK1 f z w‖₊ : ℝ≥0∞) ^ 2 := by
    rw [normA21, ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
    norm_num
  rw [mul_pow, hn, ← ENNReal.ofReal_pow hc, mul_pow, Real.sq_sqrt Real.pi_nonneg] at hs
  have hden : 0 < π * δ ^ 2 := mul_pos Real.pi_pos (sq_pos_of_pos hδ)
  change (∫⁻ w in unitDisc, (‖kerK1 f z w‖₊ : ℝ≥0∞) ^ 2) ≤ ENNReal.ofReal (1 / (π * δ ^ 2))
  rw [ENNReal.ofReal_div_of_pos hden, ENNReal.ofReal_one]
  apply (ENNReal.le_div_iff_mul_le (Or.inr one_ne_zero) (Or.inr ENNReal.one_ne_top)).mpr
  simpa only [mul_comm] using hs

/-- (TT:6076–6090) `F(f, id)(z) = √π (1 - |z|²) 𝖪₁(z, z)^{1/2}`. By the Grunsky inequality,
`𝖪₁(f)(ζ, ζ) = ‖K₁(f)(·, ζ)‖₂² ≤ 1/(π(1 - |ζ|²)²)`, so `K₁(f)(·, ζ) ∈ A₂¹(𝔻)`. -/
theorem brazF_id {f : ℂ → ℂ} (hf : IsUnivalentDisc f) {ζ : ℂ} (hζ : ζ ∈ unitDisc) :
    brazF f id ζ = ENNReal.ofReal (Real.sqrt π * (1 - ‖ζ‖ ^ 2)) *
        (∫⁻ w in unitDisc, (‖kerK1 f ζ w‖₊ : ℝ≥0∞) ^ 2) ^ (1 / 2 : ℝ) ∧
      (fun z => kerK1 f z ζ) ∈ A21fun unitDisc ∧
      (∫⁻ w in unitDisc, (‖kerK1 f w ζ‖₊ : ℝ≥0∞) ^ 2) ≤ ENNReal.ofReal (1 / (π * (1 - ‖ζ‖ ^ 2) ^ 2)) := by
  refine ⟨brazF_id_formula f ζ, ?_, ?_⟩
  · simpa only [kerK1_symm f ζ] using kerK1_row_mem_A21 hf hζ
  · simpa only [kerK1_symm f ζ] using kerK1_row_sq_le hf hζ

/-- **Lemma B.5** (TT:6116–6204), generalizing [Bra65]. For `f₁, f₂ ∈ 𝒰` and `z ∈ 𝔻`:
`(1 - |z|²)² |𝒮(f₁)(z) - 𝒮(f₂)(z)| ≤ 6 F(f₁, f₂)(z) ≤ 6 ‖K₁(f₁) - K₁(f₂)‖`. -/
theorem lemma_B_5 {f₁ f₂ : ℂ → ℂ} (h₁ : IsUnivalentDisc f₁) (h₂ : IsUnivalentDisc f₂) {z : ℂ} (hz : z ∈ unitDisc) :
    ENNReal.ofReal ((1 - ‖z‖ ^ 2) ^ 2 * ‖schwarzianHol f₁ z - schwarzianHol f₂ z‖) ≤ 6 * brazF f₁ f₂ z ∧
      brazF f₁ f₂ z ≤ kerOpNorm fun z w => kerK1 f₁ z w - kerK1 f₂ z w := by
  exact ⟨brazF_schwarzian_lower h₁ h₂ hz, brazF_le_kerOpNorm h₁ h₂ hz⟩


/-! ### Compact kernel rows and Lemma B.8 -/

/-- The extended tail operator norm bounds the actual square mass of every
unit-ball output tail. -/
theorem b8_mat_tail_mass_le {Z : ℕ → ℕ → ℂ} (hZ : IsBoundedMat Z)
    {x : ℕ → ℂ} (hx : IsL2 x) (hx1 : sqSum x ≤ 1) (N : ℕ) :
    (∑' n, ‖matApply Z x (n + N)‖ ^ 2) ≤
      (matOpNorm (fun m n => if m < N then 0 else Z m n)).toReal ^ 2 := by
  let T : ℕ → ℕ → ℂ := fun m n => if m < N then 0 else Z m n
  have hT : IsBoundedMat T := isBoundedMat_tail hZ N
  have hnorm : ENNReal.ofReal (Real.sqrt (sqSum (matApply T x))) ≤ matOpNorm T := by
    rw [matOpNorm_of_bounded hT]
    exact le_iSup_of_le x (le_iSup_of_le ⟨hx, hx1⟩ le_rfl)
  have hreal := ENNReal.toReal_mono ((matOpNorm_lt_top_iff T).mpr hT).ne hnorm
  rw [ENNReal.toReal_ofReal (Real.sqrt_nonneg _)] at hreal
  have hmass : sqSum (matApply T x) = ∑' n, ‖matApply Z x (n + N)‖ ^ 2 := by
    have hs : Summable (fun n => ‖matApply T x n‖ ^ 2) := (matApply_tail_sqSum_le hZ hx N).1
    rw [sqSum, ← hs.sum_add_tsum_nat_add N]
    have hzero : (∑ m ∈ Finset.range N, ‖matApply T x m‖ ^ 2) = 0 := by
      apply Finset.sum_eq_zero
      intro m hm
      simp [T, matApply, Finset.mem_range.mp hm]
    rw [hzero, zero_add]
    apply tsum_congr
    intro n
    simp [T, matApply, show ¬n + N < N by omega]
  have hnonneg : 0 ≤ sqSum (matApply T x) := tsum_nonneg fun _ => sq_nonneg _
  have hsq := Real.sq_sqrt hnonneg
  rw [hmass] at hsq
  have hpos := Real.sqrt_nonneg (sqSum (matApply T x))
  rw [hmass] at hreal hpos
  have hnormpos := ENNReal.toReal_nonneg (a := matOpNorm T)
  change (∑' n, ‖matApply Z x (n + N)‖ ^ 2) ≤ (matOpNorm T).toReal ^ 2
  nlinarith

set_option maxHeartbeats 800000 in
/-- Exact sequential compactness bridge for the stated matrix tail criterion. -/
theorem b8_compact_matrix_subsequence {Z : ℕ → ℕ → ℂ} (hZ : IsCompactMat Z)
    {x : ℕ → ℕ → ℂ} (hx : ∀ k, IsL2 (x k)) (hx1 : ∀ k, sqSum (x k) ≤ 1) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ y : ℕ → ℂ, IsL2 y ∧
      Tendsto (fun k => ∑' n, ‖matApply Z (x (φ k)) n - y n‖ ^ 2) atTop (𝓝 0) := by
  obtain ⟨C, hC⟩ := hZ.1
  have hb : ∀ k, sqSum (matApply Z (x k)) ≤ max C 0 := by
    intro k
    calc _ ≤ C * sqSum (x k) := (hC (x k) (hx k)).2
      _ ≤ max C 0 * sqSum (x k) := mul_le_mul_of_nonneg_right
        (le_max_left _ _) (tsum_nonneg fun _ => sq_nonneg _)
      _ ≤ max C 0 := mul_le_of_le_one_right (le_max_right _ _) (hx1 k)
  have ht := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hZ.2
  have ht2 : Tendsto (fun N => (matOpNorm (fun m n => if m < N then 0 else Z m n)).toReal ^ 2)
      atTop (𝓝 0) := by simpa using ht.pow 2
  have hout := b8_subsequence_of_uniform_tails
    (v := fun k => matApply Z (x k)) (C := max C 0)
    (M := fun N => (matOpNorm (fun m n => if m < N then 0 else Z m n)).toReal ^ 2)
    (fun k => (hC (x k) (hx k)).1) hb ht2
    (fun N k => b8_mat_tail_mass_le (Z := Z) (x := x k) hZ.1 (hx k) (hx1 k) N)
  exact hout

/-- Compactness of the actual integral images of an A21 unit-ball sequence. -/
theorem b8_kernel_compact_sequence {B : ℕ → ℕ → ℂ} {K : ℂ → ℂ → ℂ}
    (hsym : ∀ m n, B m n = B n m)
    (hrow : ∀ m, Summable (fun n => ‖B m n‖ ^ 2) ∧ (∑' n, ‖B m n‖ ^ 2) ≤ 1)
    (hB : B7Contractive B) (hcompact : IsCompactMat B)
    (hK : ∀ z ∈ unitDisc, ∀ w ∈ unitDisc, z ≠ w →
      HasSum (fun p : ℕ × ℕ => B p.1 p.2 * basisE p.1 z * basisE p.2 w) (K z w))
    {ψ : ℕ → ℂ → ℂ} (hψ : ∀ k, ψ k ∈ A21fun unitDisc)
    (hψ1 : ∀ k, normA21 unitDisc (ψ k) ≤ 1) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ u ∈ A21fun unitDisc,
      Tendsto (fun k => normA21 unitDisc (fun z =>
        (∫ w in unitDisc, K z w * conj (ψ (φ k) w)) - u z)) atTop (𝓝 0) := by
  choose x hx hxe hmass using fun k => A21_exists_ell2_expansion (hψ k)
  have hxc : ∀ k, IsL2 (fun n => conj (x k n)) := by
    intro k
    simpa only [IsL2, Complex.norm_conj] using hx k
  have hx1 : ∀ k, sqSum (fun n => conj (x k n)) ≤ 1 := by
    intro k
    have hs := A21_ell2_norm_sq (hψ k) (hmass k)
    have he : ENNReal.ofReal (∑' n, ‖x k n‖ ^ 2) ≤ 1 := by
      rw [← hs]
      simpa only [one_pow] using pow_le_pow_left' (hψ1 k) 2
    have hr := ENNReal.toReal_mono ENNReal.one_ne_top he
    simpa only [sqSum, Complex.norm_conj, ENNReal.toReal_ofReal
      (tsum_nonneg fun _ => sq_nonneg _), ENNReal.toReal_one] using hr
  obtain ⟨φ, hφ, y, hy, ht⟩ := b8_compact_matrix_subsequence hcompact hxc hx1
  let u : ℂ → ℂ := fun z => ∑' n, y n * basisE n z
  have hu : u ∈ A21fun unitDisc := (bergman_ell2_series hy).1
  have hue : ∀ z ∈ unitDisc, HasSum (fun n => y n * basisE n z) (u z) :=
    fun z hz => (bergman_pair_summable hy (basisE_sq_summable hz)).of_norm.hasSum
  have hnorm : ∀ k, normA21 unitDisc (fun z =>
      (∫ w in unitDisc, K z w * conj (ψ (φ k) w)) - u z) =
      (ENNReal.ofReal (∑' n, ‖matApply B (fun n => conj (x (φ k) n)) n - y n‖ ^ 2)) ^ (1/2 : ℝ) := by
    intro k
    have hA := b7_kernel_action hsym hrow hB hK (hψ (φ k)) (hx (φ k)) (hxe (φ k))
    have hD : (fun z => (∫ w in unitDisc, K z w * conj (ψ (φ k) w)) - u z)
        ∈ A21fun unitDisc := by
      apply (mem_A21fun_iff_memLp isOpen_ball.measurableSet).mpr
      exact ⟨hA.1.1.sub hu.1, (a21_memLp_two isOpen_ball.measurableSet hA.1).sub
        (a21_memLp_two isOpen_ball.measurableSet hu)⟩
    have hs : ∀ z ∈ unitDisc, HasSum
        (fun n => (matApply B (fun n => conj (x (φ k) n)) n - y n) * basisE n z)
        ((∫ w in unitDisc, K z w * conj (ψ (φ k) w)) - u z) := by
      intro z hz
      exact ((hA.2 z hz).sub (hue z hz)).congr_fun (fun n => by
        dsimp only [matApply, b7Apply]; ring)
    have hh := congrArg (fun a : ℝ≥0∞ => a ^ (1/2 : ℝ))
      (A21_ell2_norm_sq hD (A21_basis_parseval hD hs))
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul] at hh
    norm_num at hh
    exact hh
  refine ⟨φ, hφ, u, hu, ?_⟩
  have he := ENNReal.continuous_ofReal.continuousAt.tendsto.comp ht
  have hh := (ENNReal.continuous_rpow_const (y := (1/2 : ℝ))).continuousAt.tendsto.comp he
  simp only [ENNReal.ofReal_zero,
    ENNReal.zero_rpow_of_pos (by norm_num : (0 : ℝ) < 1/2)] at hh
  exact hh.congr (fun k => (hnorm k).symm)

/-- **Lemma B.8** (TT:6280–6350). Let `[μ] ∈ T(1)` with `K₁(𝖿^μ)` (equivalently `B₁(𝖿^μ)`) compact. For every sequence
`ζ_m ∈ 𝔻`, the functions `u_m(z) = (1 - |ζ_m|²) K₁(𝖿^μ)(z, ζ_m)` have a subsequence converging in `A₂¹(𝔻)`. The proof
uses `𝖪₃(ζ, ζ) + 𝖪₄(ζ, ζ) = 1/(π(1 - |ζ|²)²)`, `𝖪₄(ζ, ζ) ≥ 0`, and that `B₃` is a topological isomorphism. -/
theorem lemma_B_8 {p : T1} (hK : IsCompactMat (periodP p)) {ζ : ℕ → ℂ} (hζ : ∀ m, ζ m ∈ unitDisc) :
    let f := fsans (Quotient.out p : LinfStarBall)
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ u ∈ A21fun unitDisc,
      Tendsto (fun k => normA21 unitDisc fun z => (1 - ‖ζ (φ k)‖ ^ 2) * kerK1 f z (ζ (φ k)) - u z) atTop (𝓝 0) := by
  let μ : LinfStarBall := Quotient.out p
  let f := fsans μ
  have hpair := b8_welding_normalized_pair μ.2
  have hf : IsUnivalentDisc f := ⟨hpair.1, hpair.2.1⟩
  obtain ⟨hsym,hrow,hB,hseries⟩ := b8_pair_model hpair
  let ψ : ℕ → ℂ → ℂ := fun k => normalizedBergmanTest (ζ k)
  have hψ : ∀ k, ψ k ∈ A21fun unitDisc := fun k => (normalizedBergmanTest_spec (hζ k)).1
  have hψ1 : ∀ k, normA21 unitDisc (ψ k) ≤ 1 :=
    fun k => (normalizedBergmanTest_spec (hζ k)).2.le
  obtain ⟨φ,hφ,U,hU,hlim⟩ := b8_kernel_compact_sequence hsym hrow hB hK hseries hψ hψ1
  let c : ℂ := (Real.sqrt π : ℂ)⁻¹
  let u : ℂ → ℂ := fun z => c * U z
  have hu : u ∈ A21fun unitDisc := a21_const_mul isOpen_ball.measurableSet hU c
  have hc : (Real.sqrt π : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have hnorm : ∀ k, normA21 unitDisc (fun z =>
      (1 - ‖ζ (φ k)‖ ^ 2) * kerK1 f z (ζ (φ k)) - u z) =
      (‖c‖₊ : ℝ≥0∞) * normA21 unitDisc (fun z =>
        (∫ w in unitDisc, kerK1 f z w * conj (ψ (φ k) w)) - U z) := by
    intro k
    have hT : (fun z => ∫ w in unitDisc, kerK1 f z w * conj (ψ (φ k) w))
        ∈ A21fun unitDisc := by
      obtain ⟨x,hx,hxe,_⟩ := A21_exists_ell2_expansion (hψ (φ k))
      exact (b7_kernel_action hsym hrow hB hseries (hψ (φ k)) hx hxe).1
    have hm := (hT.1.sub hU.1).continuousOn.aestronglyMeasurable
      (μ := volume) isOpen_ball.measurableSet
    change AEStronglyMeasurable (fun z =>
      (∫ w in unitDisc, kerK1 f z w * conj (ψ (φ k) w)) - U z) (volume.restrict unitDisc) at hm
    rw [← normA21_const_mul hm c]
    unfold normA21
    congr 1
    apply lintegral_congr_ae
    filter_upwards [ae_restrict_mem (show MeasurableSet unitDisc from measurableSet_ball)] with z hz
    have he := normalizedBergmanTest_pairing (kerK1_row_mem_A21 hf hz) (hζ (φ k))
    change (∫ w in unitDisc, kerK1 f z w * conj (ψ (φ k) w)) = _ at he
    have hval : (1 - ‖ζ (φ k)‖ ^ 2) * kerK1 f z (ζ (φ k)) - u z =
        c * ((∫ w in unitDisc, kerK1 f z w * conj (ψ (φ k) w)) - U z) := by
      rw [he]
      dsimp [u,c]
      field_simp [hc]
    exact congrArg (fun a : ℂ => (‖a‖₊ : ℝ≥0∞) ^ 2) hval
  refine ⟨φ,hφ,u,hu,?_⟩
  have hh := ENNReal.Tendsto.const_mul hlim
    (Or.inr (show (‖c‖₊ : ℝ≥0∞) ≠ ∞ from ENNReal.coe_ne_top))
  simp only [mul_zero] at hh
  exact hh.congr (fun k => (hnorm k).symm)

end AppB

end TakhtajanTeo
