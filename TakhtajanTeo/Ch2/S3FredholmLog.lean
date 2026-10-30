import TakhtajanTeo.Ch2.S2_DetF
import TakhtajanTeo.Ch2.S2_Eq212
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-! # Convergent Fredholm logarithm for the actual Grunsky singular sequence

The existing determinant is identified with an absolutely convergent log sum
and a nonnegative double power series. This is the scalar foundation for §3;
no parameter derivative or Theorem 3.1 is asserted here.
-/
open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal NNReal ComplexConjugate Classical Real
noncomputable section
namespace TakhtajanTeo
open LiZhongQC
namespace Ch2

/-- A square-summable subunit singular sequence has a convergent real log determinant. -/
theorem s3fl_log_tprod {lam : ℕ → ℝ} (h0 : ∀ n, 0 ≤ lam n) (h1 : ∀ n, lam n < 1)
    (hs : Summable fun n => lam n^2) :
    Summable (fun n => Real.log (1-lam n^2)) ∧
      Real.log (∏' n, (1-lam n^2)) = ∑' n, Real.log (1-lam n^2) := by
  have hp : ∀ n, 0 < 1-lam n^2 := fun n => by nlinarith [h0 n,h1 n]
  have hl : Summable (fun n => Real.log (1-lam n^2)) := by
    simpa only [sub_eq_add_neg] using Real.summable_log_one_add_of_summable hs.neg
  exact ⟨hl,by rw [← Real.rexp_tsum_eq_tprod hp hl,Real.log_exp]⟩

/-- Scalar log expansion at a subunit singular value. -/
theorem s3fl_scalar_series {s : ℝ} (h0 : 0 ≤ s) (h1 : s < 1) :
    HasSum (fun k : ℕ => (s^2)^(k+1)/(k+1)) (-Real.log (1-s^2)) := by
  have h : |s^2| < 1 := by rw [abs_of_nonneg (sq_nonneg s)]; nlinarith
  exact Real.hasSum_pow_div_log_of_abs_lt_one h

/-- Joint summability of the nonnegative spectral power series. -/
theorem s3fl_joint_summable {lam : ℕ → ℝ} (h0 : ∀ n, 0 ≤ lam n) (h1 : ∀ n, lam n < 1)
    (hs : Summable fun n => lam n^2) :
    Summable (fun q : ℕ × ℕ => (lam q.1^2)^(q.2+1)/(q.2+1)) := by
  have hl := (s3fl_log_tprod h0 h1 hs).1
  have hn : (0 : ℕ × ℕ → ℝ) ≤ (fun q : ℕ × ℕ => (lam q.1^2)^(q.2+1)/(q.2+1)) := by
    intro q
    exact div_nonneg (pow_nonneg (sq_nonneg _) _) (by positivity)
  apply (summable_prod_of_nonneg hn).mpr
  exact ⟨fun n => (s3fl_scalar_series (h0 n) (h1 n)).summable,
    hl.neg.congr (fun n => (s3fl_scalar_series (h0 n) (h1 n)).tsum_eq.symm)⟩

/-- Reordering the convergent spectral power series. -/
theorem s3fl_series_reorder {lam : ℕ → ℝ} (h0 : ∀ n, 0 ≤ lam n) (h1 : ∀ n, lam n < 1)
    (hs : Summable fun n => lam n^2) :
    (∑' n, -Real.log (1-lam n^2)) = ∑' k : ℕ, (∑' n : ℕ, (lam n^2)^(k+1))/(k+1) := by
  have hj := s3fl_joint_summable h0 h1 hs
  calc
    (∑' n, -Real.log (1-lam n^2)) = ∑' n, ∑' k : ℕ, (lam n^2)^(k+1)/(k+1) :=
      tsum_congr (fun n => (s3fl_scalar_series (h0 n) (h1 n)).tsum_eq.symm)
    _ = ∑' k : ℕ, ∑' n : ℕ, (lam n^2)^(k+1)/(k+1) :=
      (Summable.tsum_comm (f := fun n k : ℕ => (lam n^2)^(k+1)/((k : ℝ)+1)) hj).symm
    _ = _ := by
      apply tsum_congr
      intro k
      exact tsum_div_const (f := fun n : ℕ => (lam n^2)^(k+1)) (a := (k : ℝ)+1)

/-- The Fredholm log power series is jointly summable and can be summed by powers. -/
theorem s3fl_power_series {lam : ℕ → ℝ} (h0 : ∀ n, 0 ≤ lam n) (h1 : ∀ n, lam n < 1)
    (hs : Summable fun n => lam n^2) :
    Summable (fun q : ℕ × ℕ => (lam q.1^2)^(q.2+1)/(q.2+1)) ∧
      -Real.log (∏' n, (1-lam n^2)) =
        ∑' k : ℕ, (∑' n : ℕ, (lam n^2)^(k+1))/(k+1) := by
  refine ⟨s3fl_joint_summable h0 h1 hs,?_⟩
  rw [(s3fl_log_tprod h0 h1 hs).2,← tsum_neg]
  exact s3fl_series_reorder h0 h1 hs

/-- The first spectral moment is bounded by minus the logarithmic determinant. -/
theorem s3fl_energy_le {lam : ℕ → ℝ} (h0 : ∀ n, 0 ≤ lam n) (h1 : ∀ n, lam n < 1)
    (hs : Summable fun n => lam n^2) :
    (∑' n, lam n^2) ≤ -Real.log (∏' n, (1-lam n^2)) := by
  obtain ⟨hl,he⟩ := s3fl_log_tprod h0 h1 hs
  rw [he,← tsum_neg]
  apply hs.tsum_le_tsum _ hl.neg
  intro n
  have hp : 0 < 1-lam n^2 := by nlinarith [h0 n,h1 n]
  have hb := Real.log_le_sub_one_of_pos hp
  linarith

/-- Uniform scalar Taylor remainder on a fixed subunit spectral interval. -/
theorem s3fl_scalar_remainder {x r : ℝ} (hx : 0 ≤ x) (hxr : x ≤ r) (hr : r < 1) (N : ℕ) :
    |(∑ k ∈ Finset.range N, x^(k+1)/(k+1)) + Real.log (1-x)| ≤ x*r^N/(1-r) := by
  have hxl : x < 1 := hxr.trans_lt hr
  have hr0 : 0 ≤ r := hx.trans hxr
  have he := Real.abs_log_sub_add_sum_range_le (by rw [abs_of_nonneg hx]; exact hxl) N
  rw [abs_of_nonneg hx,pow_succ] at he
  apply he.trans
  apply div_le_div₀ (by positivity) _ (by linarith) (by linarith)
  have hp := pow_le_pow_left₀ hx hxr N
  nlinarith

/-- A uniform spectral gap bounds the entire logarithm by the first spectral moment. -/
theorem s3fl_gap_bound {lam : ℕ → ℝ} (h0 : ∀ n, 0 ≤ lam n) (h1 : ∀ n, lam n < 1)
    (hs : Summable fun n => lam n^2) {r : ℝ} (hr : r < 1) (hg : ∀ n, lam n^2 ≤ r) :
    -Real.log (∏' n, (1-lam n^2)) ≤ (∑' n, lam n^2)/(1-r) := by
  obtain ⟨hl,he⟩ := s3fl_log_tprod h0 h1 hs
  rw [he,← tsum_neg,← tsum_div_const]
  apply hl.neg.tsum_le_tsum _ (hs.div_const (1-r))
  intro n
  have hb := s3fl_scalar_remainder (sq_nonneg (lam n)) (hg n) hr 0
  simp only [Finset.range_zero,Finset.sum_empty,zero_add,pow_zero,mul_one] at hb
  exact (neg_le_abs _).trans hb

/-- There is an actual singular sequence for every point of T₀(1), with
square summability and convergent logarithmic and double-series formulas for S₂. -/
theorem s3fl_liouvilleS2_series {p : T1} (hp : p ∈ T01) :
    let μ : LinfStar := (Quotient.out p : LinfStarBall)
    ∃ lam : ℕ → ℝ, IsSingularSeq (B1 (grunsky (fsans μ) (gsans μ))) lam ∧
      (∀ n, lam n < 1) ∧ Summable (fun n => lam n^2) ∧
      Summable (fun n => Real.log (1-lam n^2)) ∧
      liouvilleS2 p = ∑' n, Real.log (1-lam n^2) ∧
      Summable (fun q : ℕ × ℕ => (lam q.1^2)^(q.2+1)/(q.2+1)) ∧
      -liouvilleS2 p = ∑' k : ℕ, (∑' n : ℕ, (lam n^2)^(k+1))/(k+1) ∧
      (∑' n, lam n^2) ≤ -liouvilleS2 p := by
  intro μ
  have hμ : μ ∈ LinfStarBall := (Quotient.out p).2
  obtain ⟨lam,hl,hlt,-⟩ := eq_2_12 hp
  have hpair := AppB.b8_welding_normalized_pair hμ
  have hnull := r22_complement_null hμ
  obtain ⟨hr,hb⟩ := gop_grunsky_bounds hpair hnull (B1 (grunsky (fsans μ) (gsans μ))) (Set.mem_insert _ _)
  obtain ⟨u,hu⟩ := gop_singular_basis hr hb hl
  have hs := dF_sq_summable hr hb (((cor_2_9 p).1).mp hp) u hu
  have hprod := ((detF_spec hp).2.1 lam hl).2
  have he : liouvilleS2 p = Real.log (∏' n, (1-lam n^2)) := by
    rw [hprod]; rfl
  obtain ⟨hlog,hlogeq⟩ := s3fl_log_tprod hl.1 hlt hs
  obtain ⟨hj,hje⟩ := s3fl_power_series hl.1 hlt hs
  exact ⟨lam,hl,hlt,hs,hlog,he.trans hlogeq,hj,by rw [he]; exact hje,
    by rw [he]; exact s3fl_energy_le hl.1 hlt hs⟩

/-- The actual Liouville S₂ is nonpositive on T₀(1). -/
theorem s3fl_liouvilleS2_nonpos {p : T1} (hp : p ∈ T01) : liouvilleS2 p ≤ 0 := by
  obtain ⟨lam,-,-,-,-,-,-,-,he⟩ := s3fl_liouvilleS2_series hp
  have hn : 0 ≤ ∑' n, lam n^2 := tsum_nonneg (fun _ => sq_nonneg _)
  linarith

end Ch2
end TakhtajanTeo
