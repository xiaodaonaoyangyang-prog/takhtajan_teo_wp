import TakhtajanTeo.Ch2.S5QCCompositionEnergy
import TakhtajanTeo.Ch2.PeriodMatrixBridge
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal NNReal ComplexConjugate Classical Real

noncomputable section
namespace TakhtajanTeo.Ch2
open LiZhongQC

def s5ca_coeff (F : ℂ → ℂ) (b : Bool) (n : ℕ) : ℂ :=
  (Real.sqrt ((n : ℝ) + 1) : ℂ) * circleCoeff F (if b then -(n + 1 : ℤ) else (n + 1 : ℤ))

theorem s5ca_coeff_norm (F : ℂ → ℂ) (b : Bool) (n : ℕ) :
    ‖s5ca_coeff F b n‖ ^ 2 = ((n : ℝ) + 1) *
      ‖circleCoeff F (if b then -(n + 1 : ℤ) else (n + 1 : ℤ))‖ ^ 2 := by
  simp only [s5ca_coeff, norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _),
    mul_pow, Real.sq_sqrt (by positivity : 0 ≤ (n : ℝ) + 1)]

theorem s5ca_coeff_l2 {F : ℂ → ℂ} (hF : F ∈ HC) (b : Bool) :
    Summable (fun n => ‖s5ca_coeff F b n‖ ^ 2) := by
  cases b
  · have hi : Function.Injective (fun n : ℕ => (n + 1 : ℤ)) := by intro n m h; dsimp only at h; omega
    apply (hF.2.comp_injective hi).congr
    intro n
    simp only [Function.comp_apply, s5ca_coeff_norm, Bool.false_eq_true, ite_false, Int.cast_add, Int.cast_natCast, Int.cast_one]
    rw [abs_of_nonneg (by positivity)]
  · have hi : Function.Injective (fun n : ℕ => -(n + 1 : ℤ)) := by intro n m h; dsimp only at h; omega
    apply (hF.2.comp_injective hi).congr
    intro n
    simp only [Function.comp_apply, s5ca_coeff_norm, ite_true, Int.cast_neg, abs_neg,
      Int.cast_add, Int.cast_natCast, Int.cast_one]
    rw [abs_of_nonneg (by positivity)]

def s5ca_coordinates (F : ℂ → ℂ) (hF : F ∈ HC) : ell2 × ell2 :=
  (⟨s5ca_coeff F false, gop_mem_of_summable (s5ca_coeff_l2 hF false)⟩,
   ⟨s5ca_coeff F true, gop_mem_of_summable (s5ca_coeff_l2 hF true)⟩)

theorem s5ca_coordinates_energy {F : ℂ → ℂ} (hF : F ∈ HC) :
    ‖(s5ca_coordinates F hF).1‖ ^ 2 + ‖(s5ca_coordinates F hF).2‖ ^ 2 =
      ∑' n : ℤ, |(n : ℝ)| * ‖circleCoeff F n‖ ^ 2 := by
  have hp : Function.Injective (fun n : ℕ => (n + 1 : ℤ)) := by intro n m h; dsimp only at h; omega
  have hm : Function.Injective (fun n : ℕ => -(n + 1 : ℤ)) := by intro n m h; dsimp only at h; omega
  have hS : Summable (fun n : ℤ => |(n : ℝ)| * ‖circleCoeff F n‖ ^ 2) := hF.2
  have hsplit : (∑' n, ‖s5ca_coeff F false n‖ ^ 2) + (∑' n, ‖s5ca_coeff F true n‖ ^ 2) =
      ∑' n : ℤ, |(n : ℝ)| * ‖circleCoeff F n‖ ^ 2 := by
    have hI : (∑' n : ℤ, |(n : ℝ)| * ‖circleCoeff F n‖ ^ 2) =
        (∑' n : ℕ, |((n + 1 : ℤ) : ℝ)| * ‖circleCoeff F (n + 1 : ℤ)‖ ^ 2) +
        (∑' n : ℕ, |((-(n + 1 : ℤ)) : ℝ)| * ‖circleCoeff F (-(n + 1 : ℤ))‖ ^ 2) := by
      simpa only [Int.cast_zero, abs_zero, zero_mul, add_zero, Int.cast_neg] using
        tsum_of_add_one_of_neg_add_one (f := fun n : ℤ => |(n : ℝ)| * ‖circleCoeff F n‖ ^ 2)
          (hS.comp_injective hp) (hS.comp_injective hm)
    apply Eq.trans _ hI.symm
    apply congrArg₂ (fun a b : ℝ => a + b)
    · apply tsum_congr
      intro n
      simp only [s5ca_coeff_norm, Bool.false_eq_true, ite_false, Int.cast_add, Int.cast_natCast, Int.cast_one]
      rw [abs_of_nonneg (by positivity)]
    · apply tsum_congr
      intro n
      simp only [s5ca_coeff_norm, ite_true, abs_neg,
        Int.cast_add, Int.cast_natCast, Int.cast_one]
      rw [abs_of_nonneg (by positivity)]
  exact (congrArg₂ (fun a b : ℝ => a + b)
    (gop_norm_sq (s5ca_coordinates F hF).1) (gop_norm_sq (s5ca_coordinates F hF).2)).trans hsplit

theorem s5ca_circle_continuous {γ : ℂ → ℂ} (hγ : IsQSCircleHomeo γ) :
    Continuous (fun θ : ℝ => γ (exp (θ * I))) := by
  obtain ⟨K, Γ, hΓ, _, he⟩ := s5qc_extension hγ
  have hfun : (fun θ : ℝ => γ (exp (θ * I))) = fun θ : ℝ => Γ (exp (θ * I)) := by
    funext θ
    exact (he (by change ‖exp ((θ : ℂ) * I)‖ = 1; simp [Complex.norm_exp])).symm
  rw [hfun]
  exact (continuousOn_univ.mp hΓ.2.2.1.1).comp (by fun_prop)

theorem s5ca_center_coeff {F : ℂ → ℂ}
    (hF : Continuous (fun θ : ℝ => F (exp (θ * I)))) (c : ℂ) {n : ℤ} (hn : n ≠ 0) :
    circleCoeff (fun z => F z - c) n = circleCoeff F n := by
  have hc : fourierCoeff (fun _ : ℝ => -c) n = 0 := by
    have h := fourierCoeff_const_mul (fun θ : ℝ => exp ((0 : ℤ) * θ * I)) (-c) n
    rw [fourierCoeff_exponential] at h
    simpa [hn] using h
  have h := fourierCoeff_add_continuous hF (continuous_const (y := -c)) n
  simpa only [circleCoeff, sub_eq_add_neg, hc, add_zero] using h

theorem s5ca_piHat_coeff {γ F : ℂ → ℂ} (hγ : IsQSCircleHomeo γ)
    (hF : Continuous F) {n : ℤ} (hn : n ≠ 0) :
    circleCoeff (piHat γ F) n = circleCoeff (F ∘ γ) n := by
  exact s5ca_center_coeff (F := F ∘ γ) (hF.comp (s5ca_circle_continuous hγ))
    (circleCoeff (F ∘ γ) 0) hn

def s5ca_basis (b : Bool) (n : ℕ) (z : ℂ) : ℂ :=
  (if b then conj z ^ (n + 1) else z ^ (n + 1)) / (Real.sqrt ((n : ℝ) + 1) : ℂ)

theorem s5ca_basis_contDiff (b : Bool) (n : ℕ) : ContDiff ℝ 1 (s5ca_basis b n) := by
  cases b
  · change ContDiff ℝ 1 (fun z : ℂ => z ^ (n + 1) / (Real.sqrt ((n : ℝ) + 1) : ℂ))
    fun_prop
  · change ContDiff ℝ 1 (fun z : ℂ => conj z ^ (n + 1) / (Real.sqrt ((n : ℝ) + 1) : ℂ))
    exact ((Complex.conjCLE : ℂ →L[ℝ] ℂ).contDiff.pow (n + 1)).div_const _

theorem s5ca_basis_HC {γ : ℂ → ℂ} (hγ : IsQSCircleHomeo γ) (b : Bool) (n : ℕ) :
    piHat γ (s5ca_basis b n) ∈ HC := by
  obtain ⟨K, _, hK⟩ := s5qc_piHat_smooth hγ
  exact (hK _ (s5ca_basis_contDiff b n)).1

def s5ca_column (γ : ℂ → ℂ) (hγ : IsQSCircleHomeo γ) (b : Bool) (n : ℕ) : ell2 × ell2 :=
  s5ca_coordinates (piHat γ (s5ca_basis b n)) (s5ca_basis_HC hγ b n)

def s5ca_embed : (ℕ →₀ ℂ) →ₗ[ℂ] ell2 :=
  Finsupp.linearCombination ℂ (fun n => (lp.single 2 n 1 : ell2))

theorem s5ca_embed_apply (x : ℕ →₀ ℂ) (n : ℕ) : s5ca_embed x n = x n := by
  change (∑ k ∈ x.support, x k • (lp.single 2 k 1 : ell2)) n = x n
  rw [lp.coeFn_sum, Finset.sum_apply]
  simp only [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, gop_single_apply, mul_ite, mul_one, mul_zero]
  by_cases hn : n ∈ x.support
  · simp [hn]
  · simp [hn, Finsupp.notMem_support_iff.mp hn]

theorem s5ca_embed_single (n : ℕ) (c : ℂ) : s5ca_embed (Finsupp.single n c) = lp.single 2 n c := by
  ext m
  simp [s5ca_embed_apply, lp.single_apply, Finsupp.single_apply, Pi.single_apply, eq_comm]

theorem s5ca_embed_dense : DenseRange s5ca_embed := by
  intro X
  apply mem_closure_of_tendsto (lp.hasSum_single (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) X)
  refine Eventually.of_forall fun s => ⟨∑ n ∈ s, Finsupp.single n (X n), ?_⟩
  rw [map_sum]
  simp_rw [s5ca_embed_single]

theorem s5ca_embed_energy (x : ℕ →₀ ℂ) (s : Finset ℕ) (hs : x.support ⊆ s) :
    ‖s5ca_embed x‖ ^ 2 = ∑ n ∈ s, ‖x n‖ ^ 2 := by
  rw [gop_norm_sq]
  simp only [s5ca_embed_apply]
  apply tsum_eq_sum
  intro n hn
  have hx : n ∉ x.support := fun h => hn (hs h)
  simp [Finsupp.notMem_support_iff.mp hx]

def s5ca_finite (γ : ℂ → ℂ) (hγ : IsQSCircleHomeo γ) :
    ((ℕ →₀ ℂ) × (ℕ →₀ ℂ)) →ₗ[ℂ] (ell2 × ell2) :=
  (Finsupp.linearCombination ℂ (s5ca_column γ hγ false)).coprod
    (Finsupp.linearCombination ℂ (s5ca_column γ hγ true))

theorem s5ca_coeff_mul (F : ℂ → ℂ) (c : ℂ) (n : ℤ) :
    circleCoeff (fun z => c * F z) n = c * circleCoeff F n := by
  exact fourierCoeff_const_mul (fun θ => F (exp (θ * I))) c n

theorem s5ca_coeff_add {F G : ℂ → ℂ}
    (hF : Continuous (fun θ : ℝ => F (exp (θ * I))))
    (hG : Continuous (fun θ : ℝ => G (exp (θ * I)))) (n : ℤ) :
    circleCoeff (fun z => F z + G z) n = circleCoeff F n + circleCoeff G n := by
  exact fourierCoeff_add_continuous hF hG n

theorem s5ca_coeff_sum {ι : Type*} (s : Finset ι) (F : ι → ℂ → ℂ)
    (hF : ∀ i ∈ s, Continuous (fun θ : ℝ => F i (exp (θ * I)))) (n : ℤ) :
    circleCoeff (fun z => ∑ i ∈ s, F i z) n = ∑ i ∈ s, circleCoeff (F i) n := by
  unfold circleCoeff fourierCoeff
  simp only [Finset.sum_mul]
  rw [intervalIntegral.integral_finsetSum, Finset.mul_sum]
  intro i hi
  exact ((hF i hi).mul (by fun_prop)).intervalIntegrable _ _

theorem s5ca_harmonic_basis (s : Finset ℕ) (x y : ℕ → ℂ) (z : ℂ) :
    s5qc_harmonic s x y z =
      (∑ n ∈ s, x n * s5ca_basis false n z) + (∑ n ∈ s, y n * s5ca_basis true n z) := by
  rw [s5qc_harmonic_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  simp only [s5ca_basis, Bool.false_eq_true, ite_false, ite_true]
  ring

theorem s5ca_harmonic_coeff {γ : ℂ → ℂ} (hγ : IsQSCircleHomeo γ)
    (s : Finset ℕ) (x y : ℕ → ℂ) {k : ℤ} (hk : k ≠ 0) :
    circleCoeff (piHat γ (s5qc_harmonic s x y)) k =
      (∑ n ∈ s, x n * circleCoeff (piHat γ (s5ca_basis false n)) k) +
      (∑ n ∈ s, y n * circleCoeff (piHat γ (s5ca_basis true n)) k) := by
  have hc (b : Bool) (n : ℕ) : Continuous (fun θ : ℝ => s5ca_basis b n (γ (exp (θ * I)))) :=
    (s5ca_basis_contDiff b n).continuous.comp (s5ca_circle_continuous hγ)
  have hs (b : Bool) (a : ℕ → ℂ) : Continuous
      (fun θ : ℝ => ∑ n ∈ s, a n * s5ca_basis b n (γ (exp (θ * I)))) :=
    continuous_finsetSum s (fun n _ => continuous_const.mul (hc b n))
  have hfun : s5qc_harmonic s x y ∘ γ = fun z =>
      (∑ n ∈ s, x n * s5ca_basis false n (γ z)) + (∑ n ∈ s, y n * s5ca_basis true n (γ z)) :=
    funext fun z => s5ca_harmonic_basis s x y (γ z)
  rw [s5ca_piHat_coeff hγ (s5qc_harmonic_contDiff s x y).continuous hk, hfun,
    s5ca_coeff_add (hs false x) (hs true y)]
  rw [s5ca_coeff_sum s (fun n z => x n * s5ca_basis false n (γ z))
      (fun n _ => continuous_const.mul (hc false n)),
    s5ca_coeff_sum s (fun n z => y n * s5ca_basis true n (γ z))
      (fun n _ => continuous_const.mul (hc true n))]
  simp only [s5ca_coeff_mul]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro n hn
  · rw [s5ca_piHat_coeff hγ (s5ca_basis_contDiff false n).continuous hk]
    rfl
  · rw [s5ca_piHat_coeff hγ (s5ca_basis_contDiff true n).continuous hk]
    rfl

theorem s5ca_linearCombination_sum (v : ℕ → ell2 × ell2) (x : ℕ →₀ ℂ)
    (s : Finset ℕ) (hs : x.support ⊆ s) :
    Finsupp.linearCombination ℂ v x = ∑ n ∈ s, x n • v n := by
  change (∑ n ∈ x.support, x n • v n) = _
  apply Finset.sum_subset hs
  intro n hn hnx
  rw [Finsupp.notMem_support_iff.mp hnx, zero_smul]

theorem s5ca_finite_apply {γ : ℂ → ℂ} (hγ : IsQSCircleHomeo γ)
    (x y : ℕ →₀ ℂ) (s : Finset ℕ) (hx : x.support ⊆ s) (hy : y.support ⊆ s)
    (hH : piHat γ (s5qc_harmonic s x y) ∈ HC) :
    s5ca_finite γ hγ (x, y) = s5ca_coordinates (piHat γ (s5qc_harmonic s x y)) hH := by
  have he : s5ca_finite γ hγ (x, y) =
      (∑ n ∈ s, x n • s5ca_column γ hγ false n) + (∑ n ∈ s, y n • s5ca_column γ hγ true n) := by
    rw [s5ca_finite, LinearMap.coprod_apply, s5ca_linearCombination_sum _ x s hx,
      s5ca_linearCombination_sum _ y s hy]
  rw [he]
  apply Prod.ext <;> ext m
  · simp only [Prod.fst_add, Prod.fst_sum, lp.coeFn_add, lp.coeFn_sum, Pi.add_apply, Finset.sum_apply]
    change (∑ n ∈ s, x n * s5ca_coeff (piHat γ (s5ca_basis false n)) false m) +
      (∑ n ∈ s, y n * s5ca_coeff (piHat γ (s5ca_basis true n)) false m) =
      s5ca_coeff (piHat γ (s5qc_harmonic s x y)) false m
    simp only [s5ca_coeff, Bool.false_eq_true, ite_false]
    rw [s5ca_harmonic_coeff hγ s x y (by omega)]
    simp only [mul_add, Finset.mul_sum]
    congr 1 <;> apply Finset.sum_congr rfl <;> intro n hn <;> ring
  · simp only [Prod.snd_add, Prod.snd_sum, lp.coeFn_add, lp.coeFn_sum, Pi.add_apply, Finset.sum_apply]
    change (∑ n ∈ s, x n * s5ca_coeff (piHat γ (s5ca_basis false n)) true m) +
      (∑ n ∈ s, y n * s5ca_coeff (piHat γ (s5ca_basis true n)) true m) =
      s5ca_coeff (piHat γ (s5qc_harmonic s x y)) true m
    simp only [s5ca_coeff, ite_true]
    rw [s5ca_harmonic_coeff hγ s x y (by omega)]
    simp only [mul_add, Finset.mul_sum]
    congr 1 <;> apply Finset.sum_congr rfl <;> intro n hn <;> ring

theorem s5ca_prod_energy (u : ell2 × ell2) :
    ‖u‖ ^ 2 ≤ ‖u.1‖ ^ 2 + ‖u.2‖ ^ 2 ∧ ‖u.1‖ ^ 2 + ‖u.2‖ ^ 2 ≤ 2 * ‖u‖ ^ 2 := by
  constructor
  · rw [Prod.norm_def]
    rcases le_total ‖u.1‖ ‖u.2‖ with h | h
    · rw [max_eq_right h]; nlinarith [sq_nonneg (‖u.1‖)]
    · rw [max_eq_left h]; nlinarith [sq_nonneg (‖u.2‖)]
  · have h1 := pow_le_pow_left₀ (norm_nonneg _) (norm_fst_le u) 2
    have h2 := pow_le_pow_left₀ (norm_nonneg _) (norm_snd_le u) 2
    linarith

theorem s5ca_finite_energy {γ : ℂ → ℂ} (hγ : IsQSCircleHomeo γ) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ u : (ℕ →₀ ℂ) × (ℕ →₀ ℂ),
      ‖(s5ca_finite γ hγ u).1‖ ^ 2 + ‖(s5ca_finite γ hγ u).2‖ ^ 2 ≤
        K * (‖s5ca_embed u.1‖ ^ 2 + ‖s5ca_embed u.2‖ ^ 2) := by
  obtain ⟨K, Γ, hΓ, _, _, hA⟩ := s5qc_finite_action hγ
  refine ⟨K, hΓ.2.1, ?_⟩
  intro u
  let s := u.1.support ∪ u.2.support
  have hx : u.1.support ⊆ s := Finset.subset_union_left
  have hy : u.2.support ⊆ s := Finset.subset_union_right
  obtain ⟨_, hH, hB⟩ := hA s u.1 u.2
  rw [s5ca_finite_apply hγ u.1 u.2 s hx hy hH, s5ca_coordinates_energy]
  simpa only [Finset.sum_add_distrib, ← s5ca_embed_energy u.1 s hx,
    ← s5ca_embed_energy u.2 s hy] using hB

theorem s5ca_finite_bound {γ : ℂ → ℂ} (hγ : IsQSCircleHomeo γ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : (ℕ →₀ ℂ) × (ℕ →₀ ℂ),
      ‖s5ca_finite γ hγ u‖ ≤ C * ‖(s5ca_embed u.1, s5ca_embed u.2)‖ := by
  obtain ⟨K, hK, hE⟩ := s5ca_finite_energy hγ
  refine ⟨Real.sqrt (2 * K), Real.sqrt_nonneg _, ?_⟩
  intro u
  have h0 : 0 ≤ K := zero_le_one.trans hK
  have hout := (s5ca_prod_energy (s5ca_finite γ hγ u)).1
  have hin := (s5ca_prod_energy (s5ca_embed u.1, s5ca_embed u.2)).2
  have hm := mul_le_mul_of_nonneg_left hin h0
  have hs : ‖s5ca_finite γ hγ u‖ ^ 2 ≤ (2 * K) * ‖(s5ca_embed u.1, s5ca_embed u.2)‖ ^ 2 := by
    have he := hE u
    dsimp only at hm
    nlinarith
  have h := Real.sqrt_le_sqrt hs
  rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_mul (by positivity : 0 ≤ 2 * K),
    Real.sqrt_sq (norm_nonneg _)] at h

def s5ca_completed (γ : ℂ → ℂ) (hγ : IsQSCircleHomeo γ) :
    (ell2 × ell2) →L[ℂ] (ell2 × ell2) :=
  (s5ca_finite γ hγ).extendOfNorm (s5ca_embed.prodMap s5ca_embed)

theorem s5ca_completed_apply {γ : ℂ → ℂ} (hγ : IsQSCircleHomeo γ)
    (u : (ℕ →₀ ℂ) × (ℕ →₀ ℂ)) :
    s5ca_completed γ hγ (s5ca_embed u.1, s5ca_embed u.2) = s5ca_finite γ hγ u := by
  obtain ⟨C, _, hC⟩ := s5ca_finite_bound hγ
  exact LinearMap.extendOfNorm_eq (s5ca_embed_dense.prodMap s5ca_embed_dense) ⟨C, hC⟩ u

theorem s5ca_completed_unique {γ : ℂ → ℂ} (hγ : IsQSCircleHomeo γ)
    (T : (ell2 × ell2) →L[ℂ] (ell2 × ell2))
    (hT : ∀ u : (ℕ →₀ ℂ) × (ℕ →₀ ℂ), T (s5ca_embed u.1, s5ca_embed u.2) = s5ca_finite γ hγ u) :
    s5ca_completed γ hγ = T := by
  obtain ⟨C, _, hC⟩ := s5ca_finite_bound hγ
  apply LinearMap.extendOfNorm_unique (f := s5ca_finite γ hγ)
    (e := s5ca_embed.prodMap s5ca_embed) (s5ca_embed_dense.prodMap s5ca_embed_dense) C hC T
  apply LinearMap.ext
  intro u
  exact hT u

theorem s5ca_completed_finite {γ : ℂ → ℂ} (hγ : IsQSCircleHomeo γ)
    (x y : ℕ →₀ ℂ) (s : Finset ℕ) (hx : x.support ⊆ s) (hy : y.support ⊆ s)
    (hH : piHat γ (s5qc_harmonic s x y) ∈ HC) :
    s5ca_completed γ hγ (s5ca_embed x, s5ca_embed y) =
      s5ca_coordinates (piHat γ (s5qc_harmonic s x y)) hH := by
  exact (s5ca_completed_apply hγ (x, y)).trans (s5ca_finite_apply hγ x y s hx hy hH)

theorem s5ca_completed_energy {γ : ℂ → ℂ} (hγ : IsQSCircleHomeo γ) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ u : ell2 × ell2,
      ‖(s5ca_completed γ hγ u).1‖ ^ 2 + ‖(s5ca_completed γ hγ u).2‖ ^ 2 ≤
        K * (‖u.1‖ ^ 2 + ‖u.2‖ ^ 2) := by
  obtain ⟨K, hK, hE⟩ := s5ca_finite_energy hγ
  let e := s5ca_embed.prodMap s5ca_embed
  have hd : DenseRange e := s5ca_embed_dense.prodMap s5ca_embed_dense
  have hs : range e ⊆ {u : ell2 × ell2 |
      ‖(s5ca_completed γ hγ u).1‖ ^ 2 + ‖(s5ca_completed γ hγ u).2‖ ^ 2 ≤
        K * (‖u.1‖ ^ 2 + ‖u.2‖ ^ 2)} := by
    rintro _ ⟨u, rfl⟩
    change ‖(s5ca_completed γ hγ (s5ca_embed u.1, s5ca_embed u.2)).1‖ ^ 2 +
      ‖(s5ca_completed γ hγ (s5ca_embed u.1, s5ca_embed u.2)).2‖ ^ 2 ≤ _
    rw [s5ca_completed_apply]
    exact hE u
  have hc : IsClosed {u : ell2 × ell2 |
      ‖(s5ca_completed γ hγ u).1‖ ^ 2 + ‖(s5ca_completed γ hγ u).2‖ ^ 2 ≤
        K * (‖u.1‖ ^ 2 + ‖u.2‖ ^ 2)} := isClosed_le (by fun_prop) (by fun_prop)
  exact ⟨K, hK, fun u => closure_minimal hs hc (hd u)⟩

theorem s5ca_column_A {γ : ℂ → ℂ} (hγ : IsQSCircleHomeo γ) (m n : ℕ) :
    (s5ca_column γ hγ false n).1 m = matA γ m n := by
  change (Real.sqrt ((m : ℝ) + 1) : ℂ) *
    circleCoeff (piHat γ (s5ca_basis false n)) (m + 1 : ℤ) = _
  rw [s5ca_piHat_coeff hγ (s5ca_basis_contDiff false n).continuous (by omega)]
  change (Real.sqrt ((m : ℝ) + 1) : ℂ) *
    circleCoeff (fun z => γ z ^ (n + 1) / (Real.sqrt ((n : ℝ) + 1) : ℂ)) (m + 1 : ℤ) = _
  rw [circleCoeff_div_const, matA, Real.sqrt_div (by positivity), Complex.ofReal_div]
  ring

theorem s5ca_column_B {γ : ℂ → ℂ} (hγ : IsQSCircleHomeo γ) (m n : ℕ) :
    (s5ca_column γ hγ true n).1 m = matB γ m n := by
  have he : EqOn (s5ca_basis true n ∘ γ)
      (fun z => γ z ^ (-(n + 1 : ℤ)) / (Real.sqrt ((n : ℝ) + 1) : ℂ)) unitCircle := by
    intro z hz
    have hzγ : γ z ∈ unitCircle := by
      rw [← sense_circle_image hγ.1]
      exact mem_image_of_mem γ hz
    change conj (γ z) ^ (n + 1) / (Real.sqrt ((n : ℝ) + 1) : ℂ) =
      γ z ^ (-(n + 1 : ℤ)) / (Real.sqrt ((n : ℝ) + 1) : ℂ)
    rw [← Complex.inv_eq_conj hzγ, show (n + 1 : ℤ) = ((n + 1 : ℕ) : ℤ) by omega,
      zpow_neg, zpow_natCast, inv_pow]
  change (Real.sqrt ((m : ℝ) + 1) : ℂ) *
    circleCoeff (piHat γ (s5ca_basis true n)) (m + 1 : ℤ) = _
  rw [s5ca_piHat_coeff hγ (s5ca_basis_contDiff true n).continuous (by omega),
    s5qc_coeff_congr he, circleCoeff_div_const, matB,
    Real.sqrt_div (by positivity), Complex.ofReal_div]
  ring

theorem s5ca_column_conj {γ : ℂ → ℂ} (hγ : IsQSCircleHomeo γ) (b : Bool) (m n : ℕ) :
    (s5ca_column γ hγ b n).2 m = conj ((s5ca_column γ hγ (!b) n).1 m) := by
  have hb : s5ca_basis (!b) n ∘ γ = fun z => conj ((s5ca_basis b n ∘ γ) z) := by
    funext z
    cases b <;> simp [s5ca_basis, map_div₀, map_pow]
  change (Real.sqrt ((m : ℝ) + 1) : ℂ) *
    circleCoeff (piHat γ (s5ca_basis b n)) (-(m + 1 : ℤ)) =
    conj ((Real.sqrt ((m : ℝ) + 1) : ℂ) * circleCoeff (piHat γ (s5ca_basis (!b) n)) (m + 1 : ℤ))
  rw [s5ca_piHat_coeff hγ (s5ca_basis_contDiff b n).continuous (by omega),
    s5ca_piHat_coeff hγ (s5ca_basis_contDiff (!b) n).continuous (by omega), hb]
  simp only [circleCoeff, ts2_fc_conj, map_mul, conj_ofReal, conj_conj]

theorem s5ca_completed_single {γ : ℂ → ℂ} (hγ : IsQSCircleHomeo γ) (b : Bool) (n : ℕ) :
    s5ca_completed γ hγ (if b then (0, lp.single 2 n 1) else (lp.single 2 n 1, 0)) =
      s5ca_column γ hγ b n := by
  cases b
  · have h := s5ca_completed_apply hγ (Finsupp.single n 1, 0)
    simpa [s5ca_finite, s5ca_embed_single] using h
  · have h := s5ca_completed_apply hγ (0, Finsupp.single n 1)
    simpa [s5ca_finite, s5ca_embed_single] using h

def s5ca_in (b : Bool) : ell2 →L[ℂ] (ell2 × ell2) :=
  if b then ContinuousLinearMap.inr ℂ ell2 ell2 else ContinuousLinearMap.inl ℂ ell2 ell2

def s5ca_out (b : Bool) : (ell2 × ell2) →L[ℂ] ell2 :=
  if b then ContinuousLinearMap.snd ℂ ell2 ell2 else ContinuousLinearMap.fst ℂ ell2 ell2

def s5ca_block (γ : ℂ → ℂ) (hγ : IsQSCircleHomeo γ) (b c : Bool) : ell2 →L[ℂ] ell2 :=
  (s5ca_out b).comp ((s5ca_completed γ hγ).comp (s5ca_in c))

def s5ca_matrix (γ : ℂ → ℂ) (b c : Bool) (m n : ℕ) : ℂ :=
  if b then (if c then conj (matA γ m n) else conj (matB γ m n))
  else (if c then matB γ m n else matA γ m n)

theorem s5ca_block_entry {γ : ℂ → ℂ} (hγ : IsQSCircleHomeo γ) (b c : Bool) (m n : ℕ) :
    s5ca_block γ hγ b c (lp.single 2 n 1) m = s5ca_matrix γ b c m n := by
  have hp : s5ca_completed γ hγ (lp.single 2 n 1, 0) = s5ca_column γ hγ false n :=
    s5ca_completed_single hγ false n
  have hm : s5ca_completed γ hγ (0, lp.single 2 n 1) = s5ca_column γ hγ true n :=
    s5ca_completed_single hγ true n
  cases b <;> cases c
  · change (s5ca_completed γ hγ (lp.single 2 n 1, 0)).1 m = matA γ m n
    rw [hp]
    exact s5ca_column_A hγ m n
  · change (s5ca_completed γ hγ (0, lp.single 2 n 1)).1 m = matB γ m n
    rw [hm]
    exact s5ca_column_B hγ m n
  · change (s5ca_completed γ hγ (lp.single 2 n 1, 0)).2 m = conj (matB γ m n)
    rw [hp, s5ca_column_conj]
    exact congrArg conj (s5ca_column_B hγ m n)
  · change (s5ca_completed γ hγ (0, lp.single 2 n 1)).2 m = conj (matA γ m n)
    rw [hm, s5ca_column_conj]
    exact congrArg conj (s5ca_column_A hγ m n)

theorem s5ca_matrix_bounded {γ : ℂ → ℂ} (hγ : IsQSCircleHomeo γ) (b c : Bool) :
    IsBoundedMat (s5ca_matrix γ b c) := by
  exact pmb_of_operator (s5ca_block γ hγ b c) (s5ca_block_entry hγ b c)

theorem s5ca_bounded_matrices {γ : ℂ → ℂ} (hγ : IsQSCircleHomeo γ) :
    IsBoundedMat (matA γ) ∧ IsBoundedMat (matB γ) ∧
      IsBoundedMat (fun m n => conj (matB γ m n)) ∧ IsBoundedMat (fun m n => conj (matA γ m n)) := by
  exact ⟨s5ca_matrix_bounded hγ false false, s5ca_matrix_bounded hγ false true,
    s5ca_matrix_bounded hγ true false, s5ca_matrix_bounded hγ true true⟩

theorem s5ca_block_eq_gop {γ : ℂ → ℂ} (hγ : IsQSCircleHomeo γ) (b c : Bool) :
    s5ca_block γ hγ b c = gopOp (s5ca_matrix γ b c) := by
  apply gop_ext
  intro m n
  exact (s5ca_block_entry hγ b c m n).trans (pmb_entry (s5ca_matrix_bounded hγ b c) m n).symm

/-- All four blocks are the original Fourier matrices, with boundedness
derived from the finite QC estimate and the actual completion construction. -/
theorem s5ca_completed_blocks {γ : ℂ → ℂ} (hγ : IsQSCircleHomeo γ) (x y : ell2) :
    s5ca_completed γ hγ (x, y) =
      (gopOp (matA γ) x + gopOp (matB γ) y,
       gopOp (fun m n => conj (matB γ m n)) x + gopOp (fun m n => conj (matA γ m n)) y) := by
  have h00 : (s5ca_completed γ hγ (x, 0)).1 = gopOp (matA γ) x :=
    congrArg (fun S : ell2 →L[ℂ] ell2 => S x) (s5ca_block_eq_gop hγ false false)
  have h01 : (s5ca_completed γ hγ (0, y)).1 = gopOp (matB γ) y :=
    congrArg (fun S : ell2 →L[ℂ] ell2 => S y) (s5ca_block_eq_gop hγ false true)
  have h10 : (s5ca_completed γ hγ (x, 0)).2 = gopOp (fun m n => conj (matB γ m n)) x :=
    congrArg (fun S : ell2 →L[ℂ] ell2 => S x) (s5ca_block_eq_gop hγ true false)
  have h11 : (s5ca_completed γ hγ (0, y)).2 = gopOp (fun m n => conj (matA γ m n)) y :=
    congrArg (fun S : ell2 →L[ℂ] ell2 => S y) (s5ca_block_eq_gop hγ true true)
  have hs : (x, y) = (x, 0) + (0, y) := by simp
  rw [hs, map_add]
  apply Prod.ext
  · change (s5ca_completed γ hγ (x, 0)).1 + (s5ca_completed γ hγ (0, y)).1 = _
    rw [h00, h01]
  · change (s5ca_completed γ hγ (x, 0)).2 + (s5ca_completed γ hγ (0, y)).2 = _
    rw [h10, h11]

end TakhtajanTeo.Ch2
