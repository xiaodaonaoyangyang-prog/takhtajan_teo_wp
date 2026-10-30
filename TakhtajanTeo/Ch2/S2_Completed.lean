import TakhtajanTeo.Ch2.FaberGramCorollary
import TakhtajanTeo.Ch2.BergmanSeries
import TakhtajanTeo.Appendix.B_PeriodMapping

/-!
# Ch2 §2 completed originals (`s2c_` copies)

`S2_Grunsky` is upstream of `GrunskyOperator`, `FaberGram*` and `BergmanSeries`, so proofs that need them live here as
`s2c_<name>` copies with the original statement byte-identical. The leader moves each proved statement back at an
integration window.

Contents: kernel series of `K₁`, `K₄` and their rows against the Bergman bases (`s2c_kernels_spec`); Hilbert–Schmidt
criterion, trace and `𝒮(f) ∈ A₂` (`s2c_lemma_2_5`).
-/

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal ComplexConjugate Classical Real
noncomputable section
namespace TakhtajanTeo.Ch2
open LiZhongQC

/-- Convergence at the off-diagonal points of the bidisk forces absolute convergence at every point of it. -/
theorem s2c_norm_summable_of_offdiag {a : ℕ → ℕ → ℂ}
    (hoff : ∀ z ∈ unitDisc, ∀ w ∈ unitDisc, z ≠ w →
      Summable (fun p : ℕ × ℕ => a p.1 p.2 * z ^ p.1 * w ^ p.2))
    {z w : ℂ} (hz : z ∈ unitDisc) (hw : w ∈ unitDisc) :
    Summable (fun p : ℕ × ℕ => ‖a p.1 p.2 * z ^ p.1 * w ^ p.2‖) := by
  obtain ⟨ρ, hρ1, hρ2⟩ := exists_between (max_lt (mem_ball_zero_iff.mp hz) (mem_ball_zero_iff.mp hw))
  have hzρ : ‖z‖ < ρ := lt_of_le_of_lt (le_max_left _ _) hρ1
  have hwρ : ‖w‖ < ρ := lt_of_le_of_lt (le_max_right _ _) hρ1
  have hρ0 : 0 < ρ := lt_of_le_of_lt (norm_nonneg z) hzρ
  have hρD : (ρ : ℂ) ∈ unitDisc := by simpa [unitDisc, abs_of_pos hρ0] using hρ2
  have hρD' : (-(ρ : ℂ)) ∈ unitDisc := by simpa [unitDisc, abs_of_pos hρ0] using hρ2
  have hne : (ρ : ℂ) ≠ -(ρ : ℂ) := by
    intro h
    have h2 : (ρ : ℂ) = 0 := by linear_combination h / 2
    exact hρ0.ne' (by exact_mod_cast h2)
  have hsum := hoff _ hρD _ hρD' hne
  obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.1
    (Metric.isBounded_range_of_tendsto_cofinite hsum.tendsto_cofinite_zero)
  have hbound : ∀ p : ℕ × ℕ, ‖a p.1 p.2‖ * ρ ^ p.1 * ρ ^ p.2 ≤ C := by
    intro p
    have := hC _ ⟨p, rfl⟩
    simpa [norm_mul, norm_pow, norm_neg, abs_of_pos hρ0, mul_assoc] using this
  have hgz : Summable (fun n : ℕ => (‖z‖ / ρ) ^ n) :=
    summable_geometric_of_lt_one (by positivity) ((div_lt_one hρ0).2 hzρ)
  have hgw : Summable (fun n : ℕ => (‖w‖ / ρ) ^ n) :=
    summable_geometric_of_lt_one (by positivity) ((div_lt_one hρ0).2 hwρ)
  have hg : Summable (fun p : ℕ × ℕ => C * ((‖z‖ / ρ) ^ p.1 * (‖w‖ / ρ) ^ p.2)) :=
    (Summable.mul_of_nonneg hgz hgw (fun _ => by positivity) (fun _ => by positivity)).mul_left C
  refine hg.of_nonneg_of_le (fun _ => norm_nonneg _) ?_
  intro p
  have hb := hbound p
  have hpow : ρ ^ p.1 * ρ ^ p.2 ≠ 0 := by positivity
  calc ‖a p.1 p.2 * z ^ p.1 * w ^ p.2‖
      = (‖a p.1 p.2‖ * ρ ^ p.1 * ρ ^ p.2) * ((‖z‖ / ρ) ^ p.1 * (‖w‖ / ρ) ^ p.2) := by
        simp only [norm_mul, norm_pow, div_pow]
        field_simp
    _ ≤ C * ((‖z‖ / ρ) ^ p.1 * (‖w‖ / ρ) ^ p.2) :=
        mul_le_mul_of_nonneg_right hb (by positivity)

/-- The sum of a double power series that converges off the diagonal is a genuine `HasSum` on the whole bidisk. -/
theorem s2c_bidisk_hasSum {a : ℕ → ℕ → ℂ}
    (hoff : ∀ z ∈ unitDisc, ∀ w ∈ unitDisc, z ≠ w →
      Summable (fun p : ℕ × ℕ => a p.1 p.2 * z ^ p.1 * w ^ p.2)) :
    ∀ z ∈ unitDisc, ∀ w ∈ unitDisc,
      HasSum (fun p : ℕ × ℕ => a p.1 p.2 * z ^ p.1 * w ^ p.2)
        (∑' p : ℕ × ℕ, a p.1 p.2 * z ^ p.1 * w ^ p.2) :=
  fun _ hz _ hw => (s2c_norm_summable_of_offdiag hoff hz hw).of_norm.hasSum

/-- The first partial function of a double power series is differentiable. -/
theorem s2c_series_differentiableAt {a : ℕ → ℕ → ℂ} {F : ℂ → ℂ → ℂ}
    (hs : ∀ z ∈ unitDisc, ∀ w ∈ unitDisc,
      HasSum (fun p : ℕ × ℕ => a p.1 p.2 * z ^ p.1 * w ^ p.2) (F z w))
    {z w : ℂ} (hz : z ∈ unitDisc) (hw : w ∈ unitDisc) :
    DifferentiableAt ℂ (fun u => F u w) z := by
  obtain ⟨R, hzR, hR1⟩ := exists_between (mem_ball_zero_iff.mp hz)
  have hR : 0 < R := (norm_nonneg z).trans_lt hzR
  have hRD : (R : ℂ) ∈ unitDisc := by simpa [unitDisc, abs_of_pos hR] using hR1
  have hsum : Summable (fun p : ℕ × ℕ => (a p.1 p.2 * w ^ p.2) * (R : ℂ) ^ p.1) := by
    convert (hs (R : ℂ) hRD w hw).summable using 1
    funext p; ring
  have hb : Summable (fun p : ℕ × ℕ => ‖a p.1 p.2 * w ^ p.2‖ * R ^ p.1) := by
    simpa only [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR] using hsum.norm
  have hd : ∀ p : ℕ × ℕ, DifferentiableOn ℂ (fun u : ℂ => (a p.1 p.2 * w ^ p.2) * u ^ p.1) (ball 0 R) :=
    fun p => ((differentiable_const _).mul (differentiable_id.pow _)).differentiableOn
  have hbd : ∀ (p : ℕ × ℕ) (u : ℂ), u ∈ ball (0 : ℂ) R →
      ‖(a p.1 p.2 * w ^ p.2) * u ^ p.1‖ ≤ ‖a p.1 p.2 * w ^ p.2‖ * R ^ p.1 := by
    intro p u hu
    rw [norm_mul, norm_pow]
    gcongr
    exact (mem_ball_zero_iff.mp hu).le
  have hD := Complex.differentiableOn_tsum_of_summable_norm hb hd isOpen_ball hbd
  have he : (fun u => ∑' p : ℕ × ℕ, (a p.1 p.2 * w ^ p.2) * u ^ p.1) =ᶠ[𝓝 z] (fun u => F u w) := by
    filter_upwards [(isOpen_ball : IsOpen unitDisc).mem_nhds hz] with u hu
    convert (hs u hu w hw).tsum_eq using 1
    congr 1; funext p; ring
  exact (((hD z (mem_ball_zero_iff.mpr hzR)).differentiableAt
    (isOpen_ball.mem_nhds (mem_ball_zero_iff.mpr hzR))).congr_of_eventuallyEq he.symm)

/-- Logarithmic derivative of the divided difference in the first variable. -/
theorem s2c_log_deriv {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f unitDisc) (hi : InjOn f unitDisc)
    {L : ℂ → ℂ} {v z : ℂ} (hz : z ∈ unitDisc) (hv : v ∈ unitDisc) (hzv : z ≠ v)
    (hL : DifferentiableAt ℂ L z) (hev : ∀ᶠ u in 𝓝 z, exp (L u) = (f u - f v) / (u - v)) :
    deriv L z = deriv f z / (f z - f v) - 1 / (z - v) := by
  have hzn : z - v ≠ 0 := sub_ne_zero.mpr hzv
  have hfn : f z - f v ≠ 0 := sub_ne_zero.mpr (fun h => hzv (hi hz hv h))
  have hExp := hL.hasDerivAt.cexp
  have hQ := ((hf.differentiableAt (isOpen_ball.mem_nhds hz)).hasDerivAt.sub_const (f v)).div
    ((hasDerivAt_id z).sub_const v) hzn
  have hder := hExp.unique (hQ.congr_of_eventuallyEq hev)
  have hez : exp (L z) = (f z - f v) / (z - v) := hev.self_of_nhds
  rw [hez] at hder
  calc
    deriv L z = ((deriv f z * (z - v) - (f z - f v) * 1) / (z - v) ^ 2) / ((f z - f v) / (z - v)) := by
      apply (eq_div_iff (div_ne_zero hfn hzn)).mpr
      simpa [mul_comm] using hder
    _ = deriv f z / (f z - f v) - 1 / (z - v) := by field_simp [hfn, hzn]

/-- A double power series whose exponential is the divided difference of a univalent `f` has the kernel
`π K₁(f)` as its twice differentiated series (off the diagonal). -/
theorem s2c_kernel_series_of_exp {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f unitDisc) (hi : InjOn f unitDisc)
    {a : ℕ → ℕ → ℂ} {b00 : ℂ}
    (hexp : ∀ z ∈ unitDisc, ∀ w ∈ unitDisc, z ≠ w → ∃ S : ℂ,
      HasSum (fun p : ℕ × ℕ => a p.1 p.2 * z ^ p.1 * w ^ p.2) S ∧
        (f z - f w) / (z - w) = exp (b00 - S))
    {z w : ℂ} (hz : z ∈ unitDisc) (hw : w ∈ unitDisc) (hzw : z ≠ w) :
    HasSum (fun p : ℕ × ℕ => a (p.1 + 1) (p.2 + 1) * ((p.1 + 1 : ℕ) : ℂ) * ((p.2 + 1 : ℕ) : ℂ) *
      z ^ p.1 * w ^ p.2) ((π : ℂ) * kerK1 f z w) := by
  have hoff : ∀ z ∈ unitDisc, ∀ w ∈ unitDisc, z ≠ w →
      Summable (fun p : ℕ × ℕ => a p.1 p.2 * z ^ p.1 * w ^ p.2) := by
    intro z hz w hw hzw
    obtain ⟨S, hS, -⟩ := hexp z hz w hw hzw
    exact hS.summable
  have hs0 := s2c_bidisk_hasSum hoff
  obtain ⟨F, hFdef⟩ : ∃ F : ℂ → ℂ → ℂ, F = fun u v => ∑' p : ℕ × ℕ, a p.1 p.2 * u ^ p.1 * v ^ p.2 :=
    ⟨_, rfl⟩
  have hs : ∀ z ∈ unitDisc, ∀ w ∈ unitDisc,
      HasSum (fun p : ℕ × ℕ => a p.1 p.2 * z ^ p.1 * w ^ p.2) (F z w) := by
    intro z hz w hw
    rw [hFdef]
    exact hs0 z hz w hw
  have hmix := g2c_double_series_deriv_mixed_succ hs hz hw
  convert hmix using 1
  -- first derivative in the first variable, for `v` near `w`
  have hDU : ∀ v ∈ unitDisc, v ≠ z → deriv (fun u => F u v) z =
      -(deriv f z / (f z - f v) - 1 / (z - v)) := by
    intro v hv hvz
    have hdiff := s2c_series_differentiableAt hs hz hv
    have hL : DifferentiableAt ℂ (fun u => b00 - F u v) z := hdiff.const_sub b00
    have hev : ∀ᶠ u in 𝓝 z, exp (b00 - F u v) = (f u - f v) / (u - v) := by
      filter_upwards [(isOpen_ball : IsOpen unitDisc).mem_nhds hz, eventually_ne_nhds (Ne.symm hvz)]
        with u hu huv
      obtain ⟨S, hS, he⟩ := hexp u hu v hv huv
      rw [he, show F u v = S from (hs u hu v hv).unique hS]
    have := s2c_log_deriv hf hi hz hv (Ne.symm hvz) hL hev
    rw [deriv_const_sub] at this
    linear_combination -this
  have hev2 : (fun v => deriv (fun u => F u v) z) =ᶠ[𝓝 w]
      (fun v => -(deriv f z / (f z - f v) - 1 / (z - v))) := by
    filter_upwards [(isOpen_ball : IsOpen unitDisc).mem_nhds hw, eventually_ne_nhds (Ne.symm hzw)]
      with v hv hvz
    exact hDU v hv hvz
  have hzn : z - w ≠ 0 := sub_ne_zero.mpr hzw
  have hfn : f z - f w ≠ 0 := sub_ne_zero.mpr (fun h => hzw (hi hz hw h))
  have hfd := (hf.differentiableAt (isOpen_ball.mem_nhds hw)).hasDerivAt
  have hd := (((hasDerivAt_const w (deriv f z)).div (hfd.const_sub (f z)) hfn).sub
    ((hasDerivAt_const w (1 : ℂ)).div ((hasDerivAt_id w).const_sub z) hzn)).neg
  rw [hev2.deriv_eq]
  have hd' : deriv (fun v => -(deriv f z / (f z - f v) - 1 / (z - v))) w = _ := hd.deriv
  simp only [id_eq] at hd'
  rw [hd', kerK1_of_ne f hzw]
  have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  field_simp
  ring

/-- Clause 1 of `kernels_spec`: the actual disk kernel series. -/
theorem s2c_kernels_K1 {f g : ℂ → ℂ} (h : IsNormalizedDisjointPair f g) :
    ∀ z ∈ unitDisc, ∀ w ∈ unitDisc, z ≠ w → HasSum (fun p : ℕ × ℕ =>
        1 / π * (((p.1 + 1) * (p.2 + 1) : ℕ) : ℂ) * grunsky f g (-(p.1 + 1 : ℤ)) (-(p.2 + 1 : ℤ)) *
          z ^ p.1 * w ^ p.2) (kerK1 f z w) := by
  intro z hz w hw hzw
  have hb := (grunsky_spec h).1.2.2.2.1
  have hser := s2c_kernel_series_of_exp (a := fun p q => grunsky f g (-(p : ℤ)) (-(q : ℤ)))
    (b00 := grunsky f g 0 0) h.1 h.2.1 hb hz hw hzw
  have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have h2 := hser.mul_left (1 / (π : ℂ))
  rw [← mul_assoc, one_div, inv_mul_cancel₀ hπ, one_mul] at h2
  refine h2.congr_fun (fun p => ?_)
  simp only [Nat.cast_add, Nat.cast_one, Nat.cast_mul, neg_add]
  ring

/-- A kernel row against a basis vector: the Bergman-basis expansion of `∫ K(z,·) conj e_k`. -/
theorem s2c_kernel_row {B : ℕ → ℕ → ℂ} {K : ℂ → ℂ → ℂ}
    (hsym : ∀ m n, B m n = B n m)
    (hrow : ∀ m, Summable (fun n => ‖B m n‖ ^ 2) ∧ (∑' n, ‖B m n‖ ^ 2) ≤ 1)
    (hout : ∀ x : ℕ → ℂ, Summable (fun n => ‖x n‖ ^ 2) →
      Summable (fun m => ‖∑' n, B m n * x n‖ ^ 2) ∧
        (∑' m, ‖∑' n, B m n * x n‖ ^ 2) ≤ ∑' n, ‖x n‖ ^ 2)
    (hK : ∀ z ∈ unitDisc, ∀ w ∈ unitDisc, z ≠ w →
      HasSum (fun p : ℕ × ℕ => B p.1 p.2 * basisE p.1 z * basisE p.2 w) (K z w))
    (k : ℕ) {z : ℂ} (hz : z ∈ unitDisc) :
    HasSum (fun n => B n k * basisE n z) (∫ w in unitDisc, K z w * conj (basisE k w)) := by
  let x : ℕ → ℂ := fun n => if n = k then 1 else 0
  have hxn : (fun n => ‖x n‖ ^ 2) = fun n => if n = k then (1 : ℝ) else 0 := by
    funext n; by_cases hn : n = k <;> simp [x, hn]
  have hx : Summable (fun n => ‖x n‖ ^ 2) := by
    rw [hxn]; exact (hasSum_ite_eq k (1 : ℝ)).summable
  have hxe : ∀ w ∈ unitDisc, HasSum (fun n => x n * basisE n w) (basisE k w) := by
    intro w _
    have := hasSum_single (f := fun n => x n * basisE n w) k (fun n hn => by simp [x, hn])
    simpa [x] using this
  let ψ : ℂ → ℂ := fun w => ∑' n, x n * basisE n w
  have hψ : ψ ∈ A21fun unitDisc := (bergman_ell2_series hx).1
  have hψe : ∀ w ∈ unitDisc, ψ w = basisE k w := fun w hw => (hxe w hw).tsum_eq
  have hψexp : ∀ w ∈ unitDisc, HasSum (fun n => x n * basisE n w) (ψ w) := by
    intro w hw; rw [hψe w hw]; exact hxe w hw
  let d : ℕ → ℂ := fun n => ∑' m, B n m * basisE m z
  have hd := hout (fun m => basisE m z) (basisE_sq_summable hz)
  let H : ℂ → ℂ := fun w => ∑' n, d n * basisE n w
  have hH : H ∈ A21fun unitDisc := (bergman_ell2_series hd.1).1
  have hHexp : ∀ w ∈ unitDisc, HasSum (fun n => d n * basisE n w) (H w) :=
    fun w hw => (bergman_pair_summable hd.1 (basisE_sq_summable hw)).of_norm.hasSum
  have hconv (n : ℕ) : Summable (fun m => B n m * basisE m z) :=
    (bergman_pair_summable (hrow n).1 (basisE_sq_summable hz)).of_norm
  have hAE : K z =ᵐ[volume.restrict unitDisc] H := by
    filter_upwards [ae_restrict_mem (show MeasurableSet unitDisc from measurableSet_ball),
      (volume.restrict unitDisc).ae_ne z] with w hw hwz
    exact (g2c_kernel_row_series hsym hK hz hw (Ne.symm hwz) hconv).tsum_eq.symm
  have hint : (∫ w in unitDisc, K z w * conj (basisE k w)) = ∫ w in unitDisc, H w * conj (ψ w) := by
    apply integral_congr_ae
    filter_upwards [hAE, ae_restrict_mem (show MeasurableSet unitDisc from measurableSet_ball)]
      with w hw hwD
    rw [hw, hψe w hwD]
  rw [hint, ← (A21_basis_pairing hH hψ hHexp hψexp).tsum_eq]
  have hdk : ∑' n, d n * conj (x n) = d k := by
    rw [tsum_eq_single k]
    · simp [x]
    · intro n hn; simp [x, hn]
  rw [hdk]
  exact (hconv k).hasSum.congr_fun (fun n => by rw [hsym n k])

/-- Kernel row against a basis vector, for any symmetric array with the defining exponential identity. -/
theorem s2c_row_of_exp {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f unitDisc) (hi : InjOn f unitDisc)
    {a : ℕ → ℕ → ℂ} {b00 : ℂ} (hsym0 : ∀ m n, a m n = a n m)
    (hexp : ∀ z ∈ unitDisc, ∀ w ∈ unitDisc, z ≠ w → ∃ S : ℂ,
      HasSum (fun p : ℕ × ℕ => a p.1 p.2 * z ^ p.1 * w ^ p.2) S ∧
        (f z - f w) / (z - w) = exp (b00 - S))
    (k : ℕ) {z : ℂ} (hz : z ∈ unitDisc) :
    HasSum (fun n : ℕ => (Real.sqrt (((n : ℝ) + 1) * ((k : ℝ) + 1)) : ℂ) * a (n + 1) (k + 1) * basisE n z)
      (∫ w in unitDisc, kerK1 f z w * conj (basisE k w)) := by
  have hB := g2c_grunsky_matrix_contraction hf hi (a := a) (b00 := b00) hsym0 hexp
  let B : ℕ → ℕ → ℂ := fun m n => (Real.sqrt (((m : ℝ) + 1) * ((n : ℝ) + 1)) : ℂ) * a (m + 1) (n + 1)
  have hsymB : ∀ m n, B m n = B n m := by
    intro m n
    simp only [B, hsym0 (m + 1) (n + 1), mul_comm ((m : ℝ) + 1)]
  have hK : ∀ z ∈ unitDisc, ∀ w ∈ unitDisc, z ≠ w →
      HasSum (fun p : ℕ × ℕ => B p.1 p.2 * basisE p.1 z * basisE p.2 w) (kerK1 f z w) := by
    intro z hz w hw hzw
    have hser := s2c_kernel_series_of_exp (a := a) (b00 := b00) hf hi hexp hz hw hzw
    have hsum := hser.div_const (π : ℂ)
    have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    have he : ((π : ℂ) * kerK1 f z w) / (π : ℂ) = kerK1 f z w := by field_simp
    rw [he] at hsum
    exact hsum.congr_fun (fun p => g2c_basis_weight a p.1 p.2 z w)
  exact s2c_kernel_row hsymB hB.1 (fun x hx => (hB.2 x hx).2) hK k hz

/-- Clause 3 of `kernels_spec`. -/
theorem s2c_kernels_row_K1 {f g : ℂ → ℂ} (h : IsNormalizedDisjointPair f g) :
    ∀ k, ∀ z ∈ unitDisc, HasSum (fun n => B1 (grunsky f g) n k * basisE n z)
      (∫ w in unitDisc, kerK1 f z w * conj (basisE k w)) := by
  intro k z hz
  have hb := (grunsky_spec h).1.2.2.2.1
  have hsym0 : ∀ m n : ℕ, grunsky f g (-(m : ℤ)) (-(n : ℤ)) = grunsky f g (-(n : ℤ)) (-(m : ℤ)) :=
    fun m n => ((grunsky_spec h).2 m n).2
  have := s2c_row_of_exp h.1 h.2.1 (a := fun p q => grunsky f g (-(p : ℤ)) (-(q : ℤ)))
    (b00 := grunsky f g 0 0) hsym0 hb k hz
  refine this.congr_fun (fun n => ?_)
  simp only [B1, Nat.cast_add, Nat.cast_one, neg_add]

/-- The exterior kernel in terms of the inverted univalent function `φ(s) = b / g(1/s)`. -/
theorem s2c_kerK4_eq {g φ : ℂ → ℂ} {b : ℂ}
    (hφd : DifferentiableOn ℂ φ unitDisc) (hφi : InjOn φ unitDisc) (hφ0 : φ 0 = 0) (hb : b ≠ 0)
    (hg : ∀ s ∈ unitDisc, s ≠ 0 → g (1 / s) = b / φ s)
    {z w : ℂ} (hz : z ∈ unitDiscExterior) (hw : w ∈ unitDiscExterior) (hzw : z ≠ w) :
    kerK4 g z w = (z⁻¹) ^ 2 * (w⁻¹) ^ 2 * kerK1 φ z⁻¹ w⁻¹ := by
  have hinvD : ∀ u ∈ unitDiscExterior, u⁻¹ ∈ unitDisc := by
    intro u hu
    have hu1 : 1 < ‖u‖ := hu
    have : ‖u⁻¹‖ < 1 := by
      rw [norm_inv]
      exact inv_lt_one_of_one_lt₀ hu1
    exact mem_ball_zero_iff.mpr this
  have hu0 : ∀ u ∈ unitDiscExterior, u ≠ 0 := by
    intro u hu h0
    have : 1 < ‖u‖ := hu
    rw [h0, norm_zero] at this
    exact absurd this (by norm_num)
  have hgeq : ∀ u ∈ unitDiscExterior, g u = b / φ u⁻¹ := by
    intro u hu
    have := hg u⁻¹ (hinvD u hu) (inv_ne_zero (hu0 u hu))
    rwa [one_div, inv_inv] at this
  have hφne : ∀ s ∈ unitDisc, s ≠ 0 → φ s ≠ 0 := by
    intro s hs hs0 he
    exact hs0 (hφi hs (mem_ball_self one_pos) (by rw [he, hφ0]))
  have hderiv : ∀ u ∈ unitDiscExterior,
      deriv g u = b * deriv φ u⁻¹ * (u⁻¹) ^ 2 / (φ u⁻¹) ^ 2 := by
    intro u hu
    have hu0' := hu0 u hu
    have hs := hinvD u hu
    have hφne' := hφne _ hs (inv_ne_zero hu0')
    have hφdiff : HasDerivAt φ (deriv φ u⁻¹) u⁻¹ :=
      (hφd.differentiableAt (isOpen_ball.mem_nhds hs)).hasDerivAt
    have hcomp : HasDerivAt (fun x => φ x⁻¹) (deriv φ u⁻¹ * (-(u ^ 2)⁻¹)) u :=
      hφdiff.comp u (hasDerivAt_inv hu0')
    have hdiv : HasDerivAt (fun x => b / φ x⁻¹)
        ((0 * φ u⁻¹ - b * (deriv φ u⁻¹ * -(u ^ 2)⁻¹)) / φ u⁻¹ ^ 2) u :=
      (hasDerivAt_const u b).div hcomp hφne'
    have hev : g =ᶠ[𝓝 u] (fun x => b / φ x⁻¹) := by
      filter_upwards [(isOpen_lt continuous_const continuous_norm : IsOpen {x : ℂ | 1 < ‖x‖}).mem_nhds hu]
        with x hx using hgeq x hx
    rw [hev.deriv_eq, hdiv.deriv]
    field_simp
    ring
  have hs : z⁻¹ ∈ unitDisc := hinvD z hz
  have ht : w⁻¹ ∈ unitDisc := hinvD w hw
  have hz0 := hu0 z hz
  have hw0 := hu0 w hw
  have hφs := hφne _ hs (inv_ne_zero hz0)
  have hφt := hφne _ ht (inv_ne_zero hw0)
  have hst : z⁻¹ ≠ w⁻¹ := inv_injective.ne hzw
  have hφst : φ z⁻¹ - φ w⁻¹ ≠ 0 := sub_ne_zero.mpr (fun he => hst (hφi hs ht he))
  have alg : ∀ s t φs φt dφs dφt : ℂ, s ≠ 0 → t ≠ 0 → s - t ≠ 0 → φs ≠ 0 → φt ≠ 0 → φs - φt ≠ 0 →
      1 / (π : ℂ) * (1 / (s⁻¹ - t⁻¹) ^ 2 -
        (b * dφs * s ^ 2 / φs ^ 2) * (b * dφt * t ^ 2 / φt ^ 2) / (b / φs - b / φt) ^ 2) =
      s ^ 2 * t ^ 2 * (1 / (π : ℂ) * (1 / (s - t) ^ 2 - dφs * dφt / (φs - φt) ^ 2)) := by
    intro s t φs φt dφs dφt hs0 ht0 hst0 hφs0 hφt0 hφst0
    have hbst : b / φs - b / φt = b * (φt - φs) / (φs * φt) := by field_simp
    have hts : φt - φs ≠ 0 := by
      intro h0; exact hφst0 (by linear_combination -h0)
    have hs1 : s⁻¹ - t⁻¹ = (t - s) / (s * t) := by field_simp
    have hts' : t - s ≠ 0 := by
      intro h0; exact hst0 (by linear_combination -h0)
    rw [hbst, hs1]
    field_simp
    ring
  rw [kerK4_of_ne g hzw, kerK1_of_ne φ hst, hderiv z hz, hderiv w hw, hgeq z hz, hgeq w hw]
  have hzwe : z - w = z⁻¹⁻¹ - w⁻¹⁻¹ := by simp
  rw [hzwe]
  exact alg z⁻¹ w⁻¹ (φ z⁻¹) (φ w⁻¹) (deriv φ z⁻¹) (deriv φ w⁻¹) (inv_ne_zero hz0) (inv_ne_zero hw0)
    (sub_ne_zero.mpr hst) hφs hφt hφst

/-- Clause 2 of `kernels_spec`: the actual exterior kernel series. -/
theorem s2c_kernels_K4 {f g : ℂ → ℂ} (h : IsNormalizedDisjointPair f g) :
    ∀ z ∈ unitDiscExterior, ∀ w ∈ unitDiscExterior, z ≠ w → HasSum (fun p : ℕ × ℕ =>
        1 / π * (((p.1 + 1) * (p.2 + 1) : ℕ) : ℂ) * grunsky f g (p.1 + 1) (p.2 + 1) *
          z ^ (-(p.1 : ℤ) - 2) * w ^ (-(p.2 : ℤ) - 2)) (kerK4 g z w) := by
  intro z hz w hw hzw
  obtain ⟨φ, b, hφd, hφi, hφ0, hφ1, hb, hbg, hg⟩ := g1_inverted_exterior h
  obtain ⟨d, hd0, hd'⟩ := disk_axis_coefficients_exist hφd hφi hφ1 0
  have hd : ∀ s ∈ unitDisc, ∃ S : ℂ, HasSum (fun j => d j * s ^ j) S ∧ exp (-S) = dslope φ 0 s := by
    intro s hs
    simpa only [zero_sub] using hd' s hs
  have hexp := faber_inverted_full_series h hφd hφi hφ0 hφ1 hb hbg hg hd
  have hinvD : ∀ u ∈ unitDiscExterior, u⁻¹ ∈ unitDisc := by
    intro u hu
    have hu1 : 1 < ‖u‖ := hu
    have : ‖u⁻¹‖ < 1 := by
      rw [norm_inv]
      exact inv_lt_one_of_one_lt₀ hu1
    exact mem_ball_zero_iff.mpr this
  have hz0 : z ≠ 0 := by
    intro h0
    have : 1 < ‖z‖ := hz
    rw [h0, norm_zero] at this
    exact absurd this (by norm_num)
  have hw0 : w ≠ 0 := by
    intro h0
    have : 1 < ‖w‖ := hw
    rw [h0, norm_zero] at this
    exact absurd this (by norm_num)
  have hser := s2c_kernel_series_of_exp (a := faberFillAxes (fun m n => grunsky f g (m + 1) (n + 1)) d)
    (b00 := 0) hφd hφi hexp (hinvD z hz) (hinvD w hw) (inv_injective.ne hzw)
  have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have h2 := hser.mul_left ((z⁻¹) ^ 2 * (w⁻¹) ^ 2 / (π : ℂ))
  have hK4 := s2c_kerK4_eq hφd hφi hφ0 hb hg hz hw hzw
  have he : (z⁻¹) ^ 2 * (w⁻¹) ^ 2 / (π : ℂ) * ((π : ℂ) * kerK1 φ z⁻¹ w⁻¹) = kerK4 g z w := by
    rw [hK4]; field_simp
  rw [he] at h2
  refine h2.congr_fun (fun p => ?_)
  have hz2 : z ^ (-(p.1 : ℤ) - 2) = (z⁻¹) ^ (p.1 + 2) := by
    rw [show (-(p.1 : ℤ) - 2) = -((p.1 + 2 : ℕ) : ℤ) by push_cast; ring, zpow_neg, zpow_natCast, inv_pow]
  have hw2 : w ^ (-(p.2 : ℤ) - 2) = (w⁻¹) ^ (p.2 + 2) := by
    rw [show (-(p.2 : ℤ) - 2) = -((p.2 + 2 : ℕ) : ℤ) by push_cast; ring, zpow_neg, zpow_natCast, inv_pow]
  rw [hz2, hw2, faberFillAxes_succ]
  simp only [Nat.cast_add, Nat.cast_one, Nat.cast_mul]
  ring

/-- Clause 4 of `kernels_spec`. -/
theorem s2c_kernels_row_K4 {f g : ℂ → ℂ} (h : IsNormalizedDisjointPair f g) :
    ∀ k, ∀ z ∈ unitDiscExterior, HasSum (fun n => B4 (grunsky f g) n k * basisF n z)
      (∫ w in unitDiscExterior, kerK4 g z w * conj (basisF k w)) := by
  intro k z hz
  obtain ⟨φ, b, hφd, hφi, hφ0, hφ1, hb, hbg, hg⟩ := g1_inverted_exterior h
  obtain ⟨d, hd0, hd'⟩ := disk_axis_coefficients_exist hφd hφi hφ1 0
  have hd : ∀ s ∈ unitDisc, ∃ S : ℂ, HasSum (fun j => d j * s ^ j) S ∧ exp (-S) = dslope φ 0 s := by
    intro s hs
    simpa only [zero_sub] using hd' s hs
  have hexp := faber_inverted_full_series h hφd hφi hφ0 hφ1 hb hbg hg hd
  have hCsym : ∀ m n : ℕ, grunsky f g ((m : ℤ) + 1) ((n : ℤ) + 1) = grunsky f g ((n : ℤ) + 1) ((m : ℤ) + 1) :=
    fun m n => ((grunsky_spec h).2 m n).1
  have hsymφ := faberFillAxes_symm (C := fun m n : ℕ => grunsky f g ((m : ℤ) + 1) ((n : ℤ) + 1)) d hCsym
  have hz0 : z ≠ 0 := by
    intro h0
    have : 1 < ‖z‖ := hz
    rw [h0, norm_zero] at this
    exact absurd this (by norm_num)
  have hzD : z⁻¹ ∈ unitDisc := (a21_inv_exterior hz).1
  have hrow := s2c_row_of_exp hφd hφi (a := faberFillAxes (fun m n => grunsky f g (m + 1) (n + 1)) d)
    (b00 := 0) hsymφ hexp k hzD
  -- change of variables `w = 1/s`
  have hUm : MeasurableSet (unitDisc \ {0}) :=
    (measurableSet_ball).diff (measurableSet_singleton 0)
  have hcv := faber_pairing_pullback_measurable (f := fun s : ℂ => s⁻¹) (U := unitDisc \ {0}) hUm
    (fun s hs => differentiableAt_inv hs.2) inv_injective.injOn (kerK4 g z) (basisF k)
  rw [a21_inversion_conformal.2.2] at hcv
  have hdel : volume.restrict (unitDisc \ {0}) = volume.restrict unitDisc := by
    apply Measure.restrict_congr_set
    filter_upwards [volume.ae_ne (0 : ℂ)] with w hw
    simp [hw]
  have hint : (∫ w in unitDiscExterior, kerK4 g z w * conj (basisF k w)) =
      (z⁻¹) ^ 2 * ∫ s in unitDisc, kerK1 φ z⁻¹ s * conj (basisE k s) := by
    rw [hcv, hdel, ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem (show MeasurableSet unitDisc from measurableSet_ball),
      (volume.restrict unitDisc).ae_ne 0, (volume.restrict unitDisc).ae_ne z⁻¹] with s hsD hs0 hsz
    have hsE : s⁻¹ ∈ unitDiscExterior := a21_inv_punctured ⟨hsD, hs0⟩
    have hne : z ≠ s⁻¹ := by
      intro he
      apply hsz
      rw [he, inv_inv]
    have hK4 := s2c_kerK4_eq hφd hφi hφ0 hb hg hz hsE hne
    rw [inv_inv] at hK4
    have hderiv : deriv (fun x : ℂ => x⁻¹) s = -(s ^ 2)⁻¹ := deriv_inv
    rw [hderiv, hK4]
    have hF : basisF k s⁻¹ = basisE k s * s ^ 2 := by
      simp only [basisF, basisE]
      rw [inv_zpow', show (-(-(k : ℤ) - 2)) = ((k + 2 : ℕ) : ℤ) by push_cast; ring, zpow_natCast]
      ring
    rw [hF]
    have h2 : s ^ 2 ≠ 0 := pow_ne_zero 2 hs0
    have e1 : basisE k s * s ^ 2 * -(s ^ 2)⁻¹ = -basisE k s := by field_simp
    have e2 : (z⁻¹) ^ 2 * (s) ^ 2 * kerK1 φ z⁻¹ s * -(s ^ 2)⁻¹ = -((z⁻¹) ^ 2 * kerK1 φ z⁻¹ s) := by
      field_simp
    rw [e1, show (z⁻¹) ^ 2 * (s) ^ 2 * kerK1 φ z⁻¹ s * -(s ^ 2)⁻¹ = _ from e2]
    simp only [map_neg, neg_mul, mul_neg, neg_neg]
    ring
  rw [hint]
  have h2 := hrow.mul_left ((z⁻¹) ^ 2)
  refine h2.congr_fun (fun n => ?_)
  have hFz : basisF n z = (z⁻¹) ^ 2 * basisE n z⁻¹ := by
    simp only [basisF, basisE]
    rw [show (-(n : ℤ) - 2) = -((n + 2 : ℕ) : ℤ) by push_cast; ring, zpow_neg, zpow_natCast, ← inv_pow]
    ring
  rw [hFz, faberFillAxes_succ]
  simp only [B4]
  ring

/-- (TT:3949–4000) For a normalized disjoint pair with null `F`:
- the kernels have the expansions `K₁ = (1/π) Σ nm b_{-n,-m} z^{n-1} w^{m-1}` (on `𝔻 × 𝔻`) and
  `K₄ = (1/π) Σ nm b_{nm} z^{-n-1} w^{-m-1}` (on `𝔻* × 𝔻*`);
- the operators `(K_l ψ)(z) = ∬ K_l(z, w) \overline{ψ(w)} d²w` correspond to `B_l` in the bases `e_n`, `f_n`:
  `K₁ e_k = Σ_n (B₁)_{nk} e_n` on `𝔻` and `K₄ f_k = Σ_n (B₄)_{nk} f_n` on `𝔻*`. 
Proved here as `s2c_kernels_spec`; statement identical to `kernels_spec`. -/
theorem s2c_kernels_spec {f g : ℂ → ℂ} (h : IsNormalizedDisjointPair f g)
    (hF : volume ((f '' unitDisc ∪ g '' unitDiscExterior)ᶜ) = 0) :
    let b := grunsky f g
    (∀ z ∈ unitDisc, ∀ w ∈ unitDisc, z ≠ w → HasSum (fun p : ℕ × ℕ =>
        1 / π * (((p.1 + 1) * (p.2 + 1) : ℕ) : ℂ) * b (-(p.1 + 1 : ℤ)) (-(p.2 + 1 : ℤ)) * z ^ p.1 * w ^ p.2) (kerK1 f z w)) ∧
      (∀ z ∈ unitDiscExterior, ∀ w ∈ unitDiscExterior, z ≠ w → HasSum (fun p : ℕ × ℕ =>
        1 / π * (((p.1 + 1) * (p.2 + 1) : ℕ) : ℂ) * b (p.1 + 1) (p.2 + 1) * z ^ (-(p.1 : ℤ) - 2) * w ^ (-(p.2 : ℤ) - 2))
        (kerK4 g z w)) ∧
      (∀ k, ∀ z ∈ unitDisc, HasSum (fun n => B1 b n k * basisE n z)
        (∫ w in unitDisc, kerK1 f z w * conj (basisE k w))) ∧
      ∀ k, ∀ z ∈ unitDiscExterior, HasSum (fun n => B4 b n k * basisF n z)
        (∫ w in unitDiscExterior, kerK4 g z w * conj (basisF k w)) := by
  intro b
  exact ⟨s2c_kernels_K1 h, s2c_kernels_K4 h, s2c_kernels_row_K1 h, s2c_kernels_row_K4 h⟩

/-- Area Parseval in `ℝ≥0∞` for an arbitrary convergent power series on the disc (both sides may be `⊤`). -/
theorem s2c_area_parseval_lintegral {F : ℂ → ℂ} {c : ℕ → ℂ}
    (hs : ∀ z ∈ unitDisc, HasSum (fun n => c n * z ^ n) (F z)) :
    (∫⁻ z in unitDisc, ENNReal.ofReal (‖F z‖ ^ 2)) =
      ∑' n, ENNReal.ofReal (π * ‖c n‖ ^ 2 / ((n : ℝ) + 1)) := by
  by_cases hc : Summable (fun n => π * ‖c n‖ ^ 2 / ((n : ℝ) + 1))
  · have hA : F ∈ A21fun unitDisc := bergman_mem_A21_of_coeff hs hc
    have hP := A21_area_parseval hA hs
    rw [← ofReal_integral_eq_lintegral_ofReal
      (a21_integrable_sq (show MeasurableSet unitDisc from measurableSet_ball) hA)
      (Eventually.of_forall fun z => sq_nonneg ‖F z‖), ← hP.tsum_eq,
      ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity) hc]
  · have hR : (∑' n, ENNReal.ofReal (π * ‖c n‖ ^ 2 / ((n : ℝ) + 1))) = ⊤ := by
      by_contra hne
      apply hc
      have := ENNReal.summable_toReal hne
      refine this.congr (fun n => ?_)
      rw [ENNReal.toReal_ofReal (by positivity)]
    rw [hR]
    by_contra hne
    apply hc
    have hd := differentiableOn_of_powerSeries hs
    have hconv : ∀ z : ℂ, ENNReal.ofReal (‖F z‖ ^ 2) = (‖F z‖₊ : ℝ≥0∞) ^ 2 := fun z => by
      rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm, enorm_eq_nnnorm]
    have hfin : normA21 unitDisc F < ∞ := by
      unfold normA21
      refine ENNReal.rpow_lt_top_of_nonneg (by norm_num) ?_
      intro h0
      apply hne
      rw [lintegral_congr hconv]
      exact h0
    exact bergman_coeff_summable ⟨hd, hfin⟩ hs

/-- A double power series that converges on the bidisk is continuous there. -/
theorem s2c_bidisk_continuousOn {c : ℕ → ℕ → ℂ} {F : ℂ → ℂ → ℂ}
    (hs : ∀ z ∈ unitDisc, ∀ w ∈ unitDisc,
      HasSum (fun p : ℕ × ℕ => c p.1 p.2 * z ^ p.1 * w ^ p.2) (F z w)) :
    ContinuousOn (fun x : ℂ × ℂ => F x.1 x.2) (unitDisc ×ˢ unitDisc) := by
  intro x hx
  obtain ⟨r, hr1, hr2⟩ := exists_between (max_lt (mem_ball_zero_iff.mp hx.1) (mem_ball_zero_iff.mp hx.2))
  have hx1 : ‖x.1‖ < r := lt_of_le_of_lt (le_max_left _ _) hr1
  have hx2 : ‖x.2‖ < r := lt_of_le_of_lt (le_max_right _ _) hr1
  have hr0 : 0 < r := lt_of_le_of_lt (norm_nonneg _) hx1
  have hrD : (r : ℂ) ∈ unitDisc := by simpa [unitDisc, abs_of_pos hr0] using hr2
  have hsum := s2c_norm_summable_of_offdiag
    (fun z hz w hw _ => (hs z hz w hw).summable) hrD hrD
  have hu : Summable (fun p : ℕ × ℕ => ‖c p.1 p.2‖ * r ^ p.1 * r ^ p.2) := by
    refine hsum.congr (fun p => ?_)
    simp only [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr0]
  let S : Set (ℂ × ℂ) := closedBall (0 : ℂ) r ×ˢ closedBall (0 : ℂ) r
  have hSD : S ⊆ unitDisc ×ˢ unitDisc := by
    intro y hy
    exact ⟨mem_ball_zero_iff.mpr (lt_of_le_of_lt (mem_closedBall_zero_iff.mp hy.1) hr2),
      mem_ball_zero_iff.mpr (lt_of_le_of_lt (mem_closedBall_zero_iff.mp hy.2) hr2)⟩
  have hSn : S ∈ 𝓝 x := by
    have : ball (0 : ℂ) r ×ˢ ball (0 : ℂ) r ∈ 𝓝 x :=
      (isOpen_ball.prod isOpen_ball).mem_nhds ⟨mem_ball_zero_iff.mpr hx1, mem_ball_zero_iff.mpr hx2⟩
    exact Filter.mem_of_superset this (prod_mono ball_subset_closedBall ball_subset_closedBall)
  have hcont : ContinuousOn (fun y : ℂ × ℂ => ∑' p : ℕ × ℕ, c p.1 p.2 * y.1 ^ p.1 * y.2 ^ p.2) S := by
    apply continuousOn_tsum (u := fun p : ℕ × ℕ => ‖c p.1 p.2‖ * r ^ p.1 * r ^ p.2)
    · intro p; fun_prop
    · exact hu
    · intro p y hy
      have h1 : ‖y.1‖ ≤ r := mem_closedBall_zero_iff.mp hy.1
      have h2 : ‖y.2‖ ≤ r := mem_closedBall_zero_iff.mp hy.2
      simp only [norm_mul, norm_pow]
      gcongr
  have hcongr : ContinuousOn (fun y : ℂ × ℂ => F y.1 y.2) S :=
    hcont.congr (fun y hy => ((hs y.1 (hSD hy).1 y.2 (hSD hy).2).tsum_eq).symm)
  exact (hcongr.continuousAt hSn).continuousWithinAt

/-- Parseval on the bidisk in `ℝ≥0∞` for a double power series. -/
theorem s2c_bidisk_parseval {c : ℕ → ℕ → ℂ} {F : ℂ → ℂ → ℂ}
    (hs : ∀ z ∈ unitDisc, ∀ w ∈ unitDisc,
      HasSum (fun p : ℕ × ℕ => c p.1 p.2 * z ^ p.1 * w ^ p.2) (F z w)) :
    (∫⁻ x in unitDisc ×ˢ unitDisc, ENNReal.ofReal (‖F x.1 x.2‖ ^ 2)) =
      ∑' r : ℕ × ℕ, ENNReal.ofReal (π ^ 2 * ‖c r.1 r.2‖ ^ 2 / (((r.1 : ℝ) + 1) * ((r.2 : ℝ) + 1))) := by
  have hD : MeasurableSet unitDisc := measurableSet_ball
  have hhalf : (1 / 2 : ℂ) ∈ unitDisc := by norm_num [unitDisc, mem_ball, dist_zero_right]
  -- columns converge
  have hcol : ∀ q : ℕ, ∀ z ∈ unitDisc, Summable (fun p : ℕ => c p q * z ^ p) := by
    intro q z hz
    have h1 := (Equiv.prodComm ℕ ℕ).summable_iff.mpr (hs z hz (1 / 2) hhalf).summable
    have h2 := h1.prod_factor q
    have h3 : Summable (fun p : ℕ => (c p q * z ^ p) * (1 / 2 : ℂ) ^ q) := by
      refine h2.congr (fun p => ?_)
      simp
    exact (summable_mul_right_iff (pow_ne_zero q (by norm_num : (1 / 2 : ℂ) ≠ 0))).mp h3
  let d : ℕ → ℂ → ℂ := fun q z => ∑' p : ℕ, c p q * z ^ p
  have hdw : ∀ z ∈ unitDisc, ∀ w ∈ unitDisc, HasSum (fun q : ℕ => d q z * w ^ q) (F z w) := by
    intro z hz w hw
    have h1 := (Equiv.prodComm ℕ ℕ).hasSum_iff.mpr (hs z hz w hw)
    refine h1.prod_fiberwise (fun q => ?_)
    have := (hcol q z hz).hasSum.mul_right (w ^ q)
    simpa [d] using this
  -- Parseval in `w` for fixed `z`
  have hP1 : ∀ z ∈ unitDisc, (∫⁻ w in unitDisc, ENNReal.ofReal (‖F z w‖ ^ 2)) =
      ∑' q : ℕ, ENNReal.ofReal (π * ‖d q z‖ ^ 2 / ((q : ℝ) + 1)) :=
    fun z hz => s2c_area_parseval_lintegral (hdw z hz)
  have hdiff : ∀ q : ℕ, DifferentiableOn ℂ (d q) unitDisc := fun q =>
    differentiableOn_of_powerSeries (fun z hz => (hcol q z hz).hasSum)
  have hP2 : ∀ q : ℕ, (∫⁻ z in unitDisc, ENNReal.ofReal (‖d q z‖ ^ 2)) =
      ∑' p : ℕ, ENNReal.ofReal (π * ‖c p q‖ ^ 2 / ((p : ℝ) + 1)) :=
    fun q => s2c_area_parseval_lintegral (fun z hz => (hcol q z hz).hasSum)
  have hcontF := s2c_bidisk_continuousOn hs
  have hFm : AEMeasurable (fun x : ℂ × ℂ => ENNReal.ofReal (‖F x.1 x.2‖ ^ 2))
      (volume.restrict (unitDisc ×ˢ unitDisc)) := by
    have hF1 : AEMeasurable (fun x : ℂ × ℂ => F x.1 x.2) (volume.restrict (unitDisc ×ˢ unitDisc)) :=
      hcontF.aemeasurable (μ := (volume : Measure (ℂ × ℂ))) (hD.prod hD)
    fun_prop
  have hmeas : (volume : Measure (ℂ × ℂ)).restrict (unitDisc ×ˢ unitDisc) =
      (volume.restrict unitDisc).prod (volume.restrict unitDisc) := by
    rw [Measure.volume_eq_prod, Measure.prod_restrict]
  have hprod : (∫⁻ x in unitDisc ×ˢ unitDisc, ENNReal.ofReal (‖F x.1 x.2‖ ^ 2)) =
      ∫⁻ z in unitDisc, ∫⁻ w in unitDisc, ENNReal.ofReal (‖F z w‖ ^ 2) := by
    rw [hmeas]
    rw [hmeas] at hFm
    exact lintegral_prod _ hFm
  rw [hprod]
  have hterm : ∀ q p : ℕ, ENNReal.ofReal (π / ((q : ℝ) + 1)) *
      ENNReal.ofReal (π * ‖c p q‖ ^ 2 / ((p : ℝ) + 1)) =
      ENNReal.ofReal (π ^ 2 * ‖c p q‖ ^ 2 / (((p : ℝ) + 1) * ((q : ℝ) + 1))) := by
    intro q p
    rw [← ENNReal.ofReal_mul (by positivity)]
    congr 1
    field_simp
  calc (∫⁻ z in unitDisc, ∫⁻ w in unitDisc, ENNReal.ofReal (‖F z w‖ ^ 2))
      = ∫⁻ z in unitDisc, ∑' q : ℕ, ENNReal.ofReal (π * ‖d q z‖ ^ 2 / ((q : ℝ) + 1)) :=
        setLIntegral_congr_fun hD (fun z hz => hP1 z hz)
    _ = ∑' q : ℕ, ∫⁻ z in unitDisc, ENNReal.ofReal (π * ‖d q z‖ ^ 2 / ((q : ℝ) + 1)) := by
        apply lintegral_tsum
        intro q
        have hm : AEMeasurable (d q) (volume.restrict unitDisc) :=
          (hdiff q).continuousOn.aemeasurable hD
        fun_prop
    _ = ∑' q : ℕ, ∑' p : ℕ,
          ENNReal.ofReal (π ^ 2 * ‖c p q‖ ^ 2 / (((p : ℝ) + 1) * ((q : ℝ) + 1))) := by
        refine tsum_congr (fun q => ?_)
        have : ∀ z, ENNReal.ofReal (π * ‖d q z‖ ^ 2 / ((q : ℝ) + 1)) =
            ENNReal.ofReal (π / ((q : ℝ) + 1)) * ENNReal.ofReal (‖d q z‖ ^ 2) := by
          intro z
          rw [← ENNReal.ofReal_mul (by positivity)]
          congr 1; ring
        simp_rw [this]
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, hP2 q, ← ENNReal.tsum_mul_left]
        exact tsum_congr (fun p => hterm q p)
    _ = ∑' p : ℕ, ∑' q : ℕ,
          ENNReal.ofReal (π ^ 2 * ‖c p q‖ ^ 2 / (((p : ℝ) + 1) * ((q : ℝ) + 1))) :=
        ENNReal.tsum_comm
    _ = ∑' r : ℕ × ℕ,
          ENNReal.ofReal (π ^ 2 * ‖c r.1 r.2‖ ^ 2 / (((r.1 : ℝ) + 1) * ((r.2 : ℝ) + 1))) :=
        (ENNReal.tsum_prod (f := fun a b => ENNReal.ofReal
          (π ^ 2 * ‖c a b‖ ^ 2 / (((a : ℝ) + 1) * ((b : ℝ) + 1))))).symm

/-- The diagonal is null in the product measure on the bidisk. -/
theorem s2c_diag_ae :
    ∀ᵐ x ∂((volume : Measure (ℂ × ℂ)).restrict (unitDisc ×ˢ unitDisc)), x.1 ≠ x.2 := by
  have hmeas : (volume : Measure (ℂ × ℂ)).restrict (unitDisc ×ˢ unitDisc) =
      (volume.restrict unitDisc).prod (volume.restrict unitDisc) := by
    rw [Measure.volume_eq_prod, Measure.prod_restrict]
  rw [hmeas, Measure.ae_prod_iff_ae_ae]
  · filter_upwards with z
    filter_upwards [(volume.restrict unitDisc).ae_ne z] with w hw using Ne.symm hw
  · exact (measurableSet_eq_fun measurable_fst measurable_snd).compl

/-- `ℝ≥0∞` sums of nonnegative reals are finite iff the real series is summable. -/
theorem s2c_tsum_ofReal_lt_top_iff {w : ℕ × ℕ → ℝ} (hw : ∀ r, 0 ≤ w r) :
    (∑' r, ENNReal.ofReal (w r)) < ∞ ↔ Summable w := by
  constructor
  · intro h
    have := ENNReal.summable_toReal h.ne
    exact this.congr (fun r => ENNReal.toReal_ofReal (hw r))
  · intro h
    rw [← ENNReal.ofReal_tsum_of_nonneg hw h]
    exact ENNReal.ofReal_lt_top

/-- The area integral of `|K₁|²` over the bidisk, as an `ℝ≥0∞` series of Grunsky coefficients. -/
theorem s2c_kerK1_lintegral {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f unitDisc) (hi : InjOn f unitDisc)
    {a : ℕ → ℕ → ℂ} {b00 : ℂ}
    (hexp : ∀ z ∈ unitDisc, ∀ w ∈ unitDisc, z ≠ w → ∃ S : ℂ,
      HasSum (fun p : ℕ × ℕ => a p.1 p.2 * z ^ p.1 * w ^ p.2) S ∧
        (f z - f w) / (z - w) = exp (b00 - S)) :
    (∫⁻ x in unitDisc ×ˢ unitDisc, (‖kerK1 f x.1 x.2‖₊ : ℝ≥0∞) ^ 2) =
      ∑' r : ℕ × ℕ, ENNReal.ofReal (((r.1 + 1) * (r.2 + 1) : ℝ) * ‖a (r.1 + 1) (r.2 + 1)‖ ^ 2) := by
  let c : ℕ → ℕ → ℂ := fun p q => a (p + 1) (q + 1) * ((p + 1 : ℕ) : ℂ) * ((q + 1 : ℕ) : ℂ)
  have hser : ∀ z ∈ unitDisc, ∀ w ∈ unitDisc, z ≠ w →
      HasSum (fun p : ℕ × ℕ => c p.1 p.2 * z ^ p.1 * w ^ p.2) ((π : ℂ) * kerK1 f z w) :=
    fun z hz w hw hzw => s2c_kernel_series_of_exp hf hi hexp hz hw hzw
  have hs0 := s2c_bidisk_hasSum (a := c) (fun z hz w hw hzw => (hser z hz w hw hzw).summable)
  obtain ⟨F, hFdef⟩ : ∃ F : ℂ → ℂ → ℂ,
      F = fun z w => ∑' p : ℕ × ℕ, c p.1 p.2 * z ^ p.1 * w ^ p.2 := ⟨_, rfl⟩
  have hs : ∀ z ∈ unitDisc, ∀ w ∈ unitDisc,
      HasSum (fun p : ℕ × ℕ => c p.1 p.2 * z ^ p.1 * w ^ p.2) (F z w) := by
    intro z hz w hw
    rw [hFdef]
    exact hs0 z hz w hw
  have hFK : ∀ z ∈ unitDisc, ∀ w ∈ unitDisc, z ≠ w → F z w = (π : ℂ) * kerK1 f z w :=
    fun z hz w hw hzw => (hs z hz w hw).unique (hser z hz w hw hzw)
  have hpar := s2c_bidisk_parseval hs
  have hπ : (0 : ℝ) < π := Real.pi_pos
  have hae : (fun x : ℂ × ℂ => (‖kerK1 f x.1 x.2‖₊ : ℝ≥0∞) ^ 2) =ᵐ[(volume : Measure (ℂ × ℂ)).restrict
      (unitDisc ×ˢ unitDisc)] (fun x => ENNReal.ofReal (1 / π ^ 2) * ENNReal.ofReal (‖F x.1 x.2‖ ^ 2)) := by
    filter_upwards [s2c_diag_ae, ae_restrict_mem (measurableSet_ball.prod measurableSet_ball)]
      with x hx hxm
    rw [hFK x.1 hxm.1 x.2 hxm.2 hx, ← ENNReal.ofReal_mul (by positivity)]
    have e1 : (‖kerK1 f x.1 x.2‖₊ : ℝ≥0∞) ^ 2 = ENNReal.ofReal (‖kerK1 f x.1 x.2‖ ^ 2) := by
      rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm, enorm_eq_nnnorm]
    rw [e1]
    congr 1
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hπ.le]
    field_simp
  calc (∫⁻ x in unitDisc ×ˢ unitDisc, (‖kerK1 f x.1 x.2‖₊ : ℝ≥0∞) ^ 2)
      = ∫⁻ x in unitDisc ×ˢ unitDisc, ENNReal.ofReal (1 / π ^ 2) * ENNReal.ofReal (‖F x.1 x.2‖ ^ 2) :=
        lintegral_congr_ae hae
    _ = ENNReal.ofReal (1 / π ^ 2) * ∑' r : ℕ × ℕ,
          ENNReal.ofReal (π ^ 2 * ‖c r.1 r.2‖ ^ 2 / (((r.1 : ℝ) + 1) * ((r.2 : ℝ) + 1))) := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, hpar]
    _ = _ := by
        rw [← ENNReal.tsum_mul_left]
        refine tsum_congr (fun r => ?_)
        rw [← ENNReal.ofReal_mul (by positivity)]
        congr 1
        simp only [c, norm_mul, Complex.norm_natCast]
        push_cast
        have h1 : (0 : ℝ) < (r.1 : ℝ) + 1 := by positivity
        have h2 : (0 : ℝ) < (r.2 : ℝ) + 1 := by positivity
        field_simp

/-- Clause 3 of `lemma_2_5`: `-6π K₁(z, w) → 𝒮(f)(z)` as `w → z`. -/
theorem s2c_schwarzian_limit {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f unitDisc) (hi : InjOn f unitDisc)
    {z : ℂ} (hz : z ∈ unitDisc) :
    Tendsto (fun w => -6 * (π : ℂ) * kerK1 f z w) (𝓝[≠] z) (𝓝 (schwarzianHol f z)) := by
  have hdiff := AppB.differentiableOn_kerK1 (show IsOpen unitDisc from isOpen_ball) hf hi hz
  have hc : ContinuousAt (fun w => kerK1 f z w) z := by
    have := (hdiff.differentiableAt (isOpen_ball.mem_nhds hz)).continuousAt
    have heq : (fun w => kerK1 f z w) = fun w => kerK1 f w z := funext (AppB.kerK1_symm f z)
    rw [heq]
    exact this
  have ht := (hc.tendsto.const_mul (-6 * (π : ℂ))).mono_left (nhdsWithin_le_nhds (s := {z}ᶜ))
  have hval : -6 * (π : ℂ) * kerK1 f z z = schwarzianHol f z := by
    rw [kerK1_diag]
    have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    field_simp
  rw [hval] at ht
  exact ht

/-- The diagonal of the kernel of `K₁ K₁*` is the squared row norm. -/
theorem s2c_kerKK1_diag (f : ℂ → ℂ) (z : ℂ) :
    kerKK1 f z z = ((∫ u in unitDisc, ‖kerK1 f z u‖ ^ 2 : ℝ) : ℂ) := by
  unfold kerKK1
  rw [← integral_complex_ofReal]
  refine integral_congr_ae (Eventually.of_forall fun u => ?_)
  show kerK1 f z u * conj (kerK1 f z u) = ((‖kerK1 f z u‖ ^ 2 : ℝ) : ℂ)
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]

/-- The series sum `F = π K₁` on the bidisk (including the diagonal). -/
theorem s2c_kerK1_series_F {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f unitDisc) (hi : InjOn f unitDisc)
    {a : ℕ → ℕ → ℂ} {b00 : ℂ}
    (hexp : ∀ z ∈ unitDisc, ∀ w ∈ unitDisc, z ≠ w → ∃ S : ℂ,
      HasSum (fun p : ℕ × ℕ => a p.1 p.2 * z ^ p.1 * w ^ p.2) S ∧
        (f z - f w) / (z - w) = exp (b00 - S)) :
    ∃ F : ℂ → ℂ → ℂ, (∃ c : ℕ → ℕ → ℂ, ∀ z ∈ unitDisc, ∀ w ∈ unitDisc,
      HasSum (fun p : ℕ × ℕ => c p.1 p.2 * z ^ p.1 * w ^ p.2) (F z w)) ∧
      ∀ z ∈ unitDisc, ∀ w ∈ unitDisc, z ≠ w → F z w = (π : ℂ) * kerK1 f z w := by
  let c : ℕ → ℕ → ℂ := fun p q => a (p + 1) (q + 1) * ((p + 1 : ℕ) : ℂ) * ((q + 1 : ℕ) : ℂ)
  have hser : ∀ z ∈ unitDisc, ∀ w ∈ unitDisc, z ≠ w →
      HasSum (fun p : ℕ × ℕ => c p.1 p.2 * z ^ p.1 * w ^ p.2) ((π : ℂ) * kerK1 f z w) :=
    fun z hz w hw hzw => s2c_kernel_series_of_exp hf hi hexp hz hw hzw
  have hs0 := s2c_bidisk_hasSum (a := c) (fun z hz w hw hzw => (hser z hz w hw hzw).summable)
  refine ⟨fun z w => ∑' p : ℕ × ℕ, c p.1 p.2 * z ^ p.1 * w ^ p.2, ⟨c, hs0⟩, ?_⟩
  intro z hz w hw hzw
  exact (hs0 z hz w hw).unique (hser z hz w hw hzw)

/-- Almost-everywhere measurability of `K₁` on the bidisk. -/
theorem s2c_kerK1_aemeasurable {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f unitDisc) (hi : InjOn f unitDisc)
    {a : ℕ → ℕ → ℂ} {b00 : ℂ}
    (hexp : ∀ z ∈ unitDisc, ∀ w ∈ unitDisc, z ≠ w → ∃ S : ℂ,
      HasSum (fun p : ℕ × ℕ => a p.1 p.2 * z ^ p.1 * w ^ p.2) S ∧
        (f z - f w) / (z - w) = exp (b00 - S)) :
    AEMeasurable (fun x : ℂ × ℂ => kerK1 f x.1 x.2)
      ((volume : Measure (ℂ × ℂ)).restrict (unitDisc ×ˢ unitDisc)) := by
  obtain ⟨F, ⟨c, hs⟩, hFK⟩ := s2c_kerK1_series_F hf hi hexp
  have hD : MeasurableSet unitDisc := measurableSet_ball
  have hFm : AEMeasurable (fun x : ℂ × ℂ => F x.1 x.2)
      ((volume : Measure (ℂ × ℂ)).restrict (unitDisc ×ˢ unitDisc)) :=
    (s2c_bidisk_continuousOn hs).aemeasurable (μ := (volume : Measure (ℂ × ℂ))) (hD.prod hD)
  have hae : (fun x : ℂ × ℂ => kerK1 f x.1 x.2) =ᵐ[(volume : Measure (ℂ × ℂ)).restrict
      (unitDisc ×ˢ unitDisc)] (fun x => (π : ℂ)⁻¹ * F x.1 x.2) := by
    filter_upwards [s2c_diag_ae, ae_restrict_mem (hD.prod hD)] with x hx hxm
    rw [hFK x.1 hxm.1 x.2 hxm.2 hx]
    have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    field_simp
  exact (hFm.const_mul _).congr hae.symm

/-- Iterated form of the `K₁` area integral (Tonelli). -/
theorem s2c_kerK1_iterated {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f unitDisc) (hi : InjOn f unitDisc)
    {a : ℕ → ℕ → ℂ} {b00 : ℂ}
    (hexp : ∀ z ∈ unitDisc, ∀ w ∈ unitDisc, z ≠ w → ∃ S : ℂ,
      HasSum (fun p : ℕ × ℕ => a p.1 p.2 * z ^ p.1 * w ^ p.2) S ∧
        (f z - f w) / (z - w) = exp (b00 - S)) :
    AEMeasurable (fun z => ∫⁻ u in unitDisc, (‖kerK1 f z u‖₊ : ℝ≥0∞) ^ 2) (volume.restrict unitDisc) ∧
      (∫⁻ z in unitDisc, ∫⁻ u in unitDisc, (‖kerK1 f z u‖₊ : ℝ≥0∞) ^ 2) =
        ∫⁻ x in unitDisc ×ˢ unitDisc, (‖kerK1 f x.1 x.2‖₊ : ℝ≥0∞) ^ 2 := by
  have hmeas : (volume : Measure (ℂ × ℂ)).restrict (unitDisc ×ˢ unitDisc) =
      (volume.restrict unitDisc).prod (volume.restrict unitDisc) := by
    rw [Measure.volume_eq_prod, Measure.prod_restrict]
  have hKm := s2c_kerK1_aemeasurable hf hi hexp
  rw [hmeas] at hKm
  have hGm : AEMeasurable (fun x : ℂ × ℂ => (‖kerK1 f x.1 x.2‖₊ : ℝ≥0∞) ^ 2)
      ((volume.restrict unitDisc).prod (volume.restrict unitDisc)) := by fun_prop
  refine ⟨hGm.lintegral_prod_right', ?_⟩
  rw [hmeas]
  exact (lintegral_prod _ hGm).symm

/-- `∫ 𝖪₁(z, z) = ∬∬ |K₁|²` (real value), when the double integral is finite. -/
theorem s2c_kerKK1_integral {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f unitDisc) (hi : InjOn f unitDisc)
    {a : ℕ → ℕ → ℂ} {b00 : ℂ}
    (hexp : ∀ z ∈ unitDisc, ∀ w ∈ unitDisc, z ≠ w → ∃ S : ℂ,
      HasSum (fun p : ℕ × ℕ => a p.1 p.2 * z ^ p.1 * w ^ p.2) S ∧
        (f z - f w) / (z - w) = exp (b00 - S))
    (hM : (∫⁻ x in unitDisc ×ˢ unitDisc, (‖kerK1 f x.1 x.2‖₊ : ℝ≥0∞) ^ 2) ≠ ∞) :
    (∫ z in unitDisc, kerKK1 f z z) =
      (((∫⁻ x in unitDisc ×ˢ unitDisc, (‖kerK1 f x.1 x.2‖₊ : ℝ≥0∞) ^ 2).toReal : ℝ) : ℂ) := by
  have hD : MeasurableSet unitDisc := measurableSet_ball
  obtain ⟨hgm, hint⟩ := s2c_kerK1_iterated hf hi hexp
  let g : ℂ → ℝ≥0∞ := fun z => ∫⁻ u in unitDisc, (‖kerK1 f z u‖₊ : ℝ≥0∞) ^ 2
  rw [← hint] at hM ⊢
  have hfin : ∀ᵐ z ∂(volume.restrict unitDisc), g z < ∞ := ae_lt_top' hgm hM
  have hkk : ∀ z ∈ unitDisc, kerKK1 f z z = (((g z).toReal : ℝ) : ℂ) := by
    intro z hz
    rw [s2c_kerKK1_diag]
    congr 1
    have hdiff := AppB.differentiableOn_kerK1 (show IsOpen unitDisc from isOpen_ball) hf hi hz
    have hc : ContinuousOn (fun u => kerK1 f z u) unitDisc := by
      have heq : (fun u => kerK1 f z u) = fun u => kerK1 f u z := funext (AppB.kerK1_symm f z)
      rw [heq]
      exact hdiff.continuousOn
    rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun u => sq_nonneg _)
      ((hc.norm.pow 2).aestronglyMeasurable hD)]
    refine congrArg ENNReal.toReal (lintegral_congr fun u => ?_)
    rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm, enorm_eq_nnnorm]
  rw [setIntegral_congr_fun hD hkk, integral_complex_ofReal, integral_toReal hgm hfin]

/-- `𝒮(f) ∈ A₂(𝔻)` when `K₁` is Hilbert–Schmidt (submean estimate on the row `K₁(z, ·)`). -/
theorem s2c_schwarzian_A2 {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f unitDisc) (hi : InjOn f unitDisc)
    {a : ℕ → ℕ → ℂ} {b00 : ℂ}
    (hexp : ∀ z ∈ unitDisc, ∀ w ∈ unitDisc, z ≠ w → ∃ S : ℂ,
      HasSum (fun p : ℕ × ℕ => a p.1 p.2 * z ^ p.1 * w ^ p.2) S ∧
        (f z - f w) / (z - w) = exp (b00 - S))
    (hM : (∫⁻ x in unitDisc ×ˢ unitDisc, (‖kerK1 f x.1 x.2‖₊ : ℝ≥0∞) ^ 2) ≠ ∞) :
    schwarzianHol f ∈ A2fun unitDisc := by
  have hD : MeasurableSet unitDisc := measurableSet_ball
  have hdiffS : DifferentiableOn ℂ (schwarzianHol f) unitDisc := by
    intro z hz
    have hA := hf.analyticAt (isOpen_ball.mem_nhds hz)
    have hd := deriv_ne_zero_of_injOn (show IsOpen unitDisc from isOpen_ball) hf hi hz
    exact (analyticAt_schwarzianHol hA hd).differentiableAt.differentiableWithinAt
  refine ⟨hdiffS, ?_⟩
  obtain ⟨hgm, hint⟩ := s2c_kerK1_iterated hf hi hexp
  let g : ℂ → ℝ≥0∞ := fun z => ∫⁻ u in unitDisc, (‖kerK1 f z u‖₊ : ℝ≥0∞) ^ 2
  have hM' : (∫⁻ z in unitDisc, g z) ≠ ∞ := by rw [hint]; exact hM
  have hbound : ∀ z ∈ unitDisc, (‖schwarzianHol f z‖₊ : ℝ≥0∞) ^ 2 * ENNReal.ofReal (rho z)⁻¹ ≤
      ENNReal.ofReal (144 * π) * g z := by
    intro z hz
    have ht : ‖z‖ < 1 := mem_ball_zero_iff.mp hz
    have ht0 : 0 ≤ ‖z‖ := norm_nonneg z
    set r : ℝ := (1 - ‖z‖) / 2 with hr
    have hr0 : 0 < r := by rw [hr]; linarith
    have hball : closedBall z r ⊆ unitDisc := by
      intro u hu
      have h1 : ‖u - z‖ ≤ r := by simpa [dist_eq_norm] using hu
      have h2 : ‖u‖ ≤ ‖u - z‖ + ‖z‖ := by
        calc ‖u‖ = ‖(u - z) + z‖ := by rw [sub_add_cancel]
          _ ≤ ‖u - z‖ + ‖z‖ := norm_add_le _ _
      exact mem_ball_zero_iff.mpr (by rw [hr] at h1; linarith)
    have hdiff := AppB.differentiableOn_kerK1 (show IsOpen unitDisc from isOpen_ball) hf hi hz
    have hψ : DifferentiableOn ℂ (fun u => kerK1 f z u) unitDisc := by
      have heq : (fun u => kerK1 f z u) = fun u => kerK1 f u z := funext (AppB.kerK1_symm f z)
      rw [heq]
      exact hdiff
    have hsub := a21_submean_sq hψ hr0 hball
    have hsub' : ENNReal.ofReal (π * r ^ 2 * ‖kerK1 f z z‖ ^ 2) ≤ g z :=
      hsub.trans (lintegral_mono_set (ball_subset_closedBall.trans hball))
    have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    have hS' : schwarzianHol f z = -(6 * (π : ℂ)) * kerK1 f z z := by
      rw [kerK1_diag]
      field_simp
    have hS : ‖schwarzianHol f z‖ = 6 * π * ‖kerK1 f z z‖ := by
      rw [hS', norm_mul, norm_neg, norm_mul, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le]
      norm_num
    have h1t : (1 - ‖z‖ ^ 2) ≠ 0 := by nlinarith
    have hrho : (rho z)⁻¹ = (1 - ‖z‖ ^ 2) ^ 2 / 4 := by
      unfold rho
      field_simp
    have hreal : ‖schwarzianHol f z‖ ^ 2 * (rho z)⁻¹ ≤ 144 * π * (π * r ^ 2 * ‖kerK1 f z z‖ ^ 2) := by
      rw [hS, hrho, hr]
      have hX : 0 ≤ π ^ 2 * ‖kerK1 f z z‖ ^ 2 := by positivity
      have h1 : (1 + ‖z‖) ^ 2 ≤ 4 := by nlinarith
      have h2 : (1 - ‖z‖ ^ 2) ^ 2 ≤ 4 * (1 - ‖z‖) ^ 2 := by
        have : (1 - ‖z‖ ^ 2) ^ 2 = (1 - ‖z‖) ^ 2 * (1 + ‖z‖) ^ 2 := by ring
        rw [this]
        nlinarith [sq_nonneg (1 - ‖z‖)]
      nlinarith [mul_le_mul_of_nonneg_left h2 hX]
    calc (‖schwarzianHol f z‖₊ : ℝ≥0∞) ^ 2 * ENNReal.ofReal (rho z)⁻¹
        = ENNReal.ofReal (‖schwarzianHol f z‖ ^ 2 * (rho z)⁻¹) := by
          rw [ENNReal.ofReal_mul (sq_nonneg _), ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm,
            enorm_eq_nnnorm]
      _ ≤ ENNReal.ofReal (144 * π * (π * r ^ 2 * ‖kerK1 f z z‖ ^ 2)) := ENNReal.ofReal_le_ofReal hreal
      _ = ENNReal.ofReal (144 * π) * ENNReal.ofReal (π * r ^ 2 * ‖kerK1 f z z‖ ^ 2) :=
          ENNReal.ofReal_mul (by positivity)
      _ ≤ ENNReal.ofReal (144 * π) * g z := by gcongr
  unfold normA2
  refine ENNReal.rpow_lt_top_of_nonneg (by norm_num) ?_
  refine ne_top_of_le_ne_top ?_ (setLIntegral_mono' hD hbound)
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hM'

/-- Inversion of the double integral over `𝔻* × 𝔻*`: the exterior kernel `K₄` becomes the disc kernel `K₁(φ)`. -/
theorem s2c_kerK4_lintegral {g φ : ℂ → ℂ} {b : ℂ}
    (hφd : DifferentiableOn ℂ φ unitDisc) (hφi : InjOn φ unitDisc) (hφ0 : φ 0 = 0) (hb : b ≠ 0)
    (hg : ∀ s ∈ unitDisc, s ≠ 0 → g (1 / s) = b / φ s) :
    (∫⁻ x in unitDiscExterior ×ˢ unitDiscExterior, (‖kerK4 g x.1 x.2‖₊ : ℝ≥0∞) ^ 2) =
      ∫⁻ x in unitDisc ×ˢ unitDisc, (‖kerK1 φ x.1 x.2‖₊ : ℝ≥0∞) ^ 2 := by
  let U : Set ℂ := unitDisc \ {0}
  have hUm : MeasurableSet U := (measurableSet_ball).diff (measurableSet_singleton 0)
  let T : ℂ × ℂ → ℂ × ℂ := fun x => (x.1⁻¹, x.2⁻¹)
  have himg : T '' (U ×ˢ U) = unitDiscExterior ×ˢ unitDiscExterior := by
    ext ⟨z, w⟩
    constructor
    · rintro ⟨⟨s, t⟩, ⟨hs, ht⟩, he⟩
      simp only [T, Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      exact ⟨a21_inv_punctured hs, a21_inv_punctured ht⟩
    · rintro ⟨hz, hw⟩
      exact ⟨(z⁻¹, w⁻¹), ⟨a21_inv_exterior hz, a21_inv_exterior hw⟩, by simp [T]⟩
  have hinj : InjOn T (U ×ˢ U) := by
    rintro ⟨s, t⟩ _ ⟨s', t'⟩ _ he
    simp only [T, Prod.mk.injEq, inv_inj] at he
    exact Prod.ext he.1 he.2
  let f' : ℂ × ℂ → (ℂ × ℂ) →L[ℝ] (ℂ × ℂ) := fun x =>
    ((ContinuousLinearMap.toSpanSingleton ℂ (-(x.1 ^ 2)⁻¹)).restrictScalars ℝ).prodMap
      ((ContinuousLinearMap.toSpanSingleton ℂ (-(x.2 ^ 2)⁻¹)).restrictScalars ℝ)
  have hder : ∀ x ∈ U ×ˢ U, HasFDerivWithinAt T (f' x) (U ×ˢ U) x := by
    rintro ⟨s, t⟩ ⟨hs, ht⟩
    have h1 := ((hasDerivAt_inv hs.2).hasFDerivAt.restrictScalars ℝ)
    have h2 := ((hasDerivAt_inv ht.2).hasFDerivAt.restrictScalars ℝ)
    exact (h1.prodMap (s, t) h2).hasFDerivWithinAt
  have : (volume : Measure (ℂ × ℂ)).IsAddHaarMeasure :=
    inferInstanceAs (Measure.prod (volume : Measure ℂ) volume).IsAddHaarMeasure
  have hcv := lintegral_image_eq_lintegral_abs_det_fderiv_mul (volume : Measure (ℂ × ℂ))
    (hUm.prod hUm) hder hinj (fun x => (‖kerK4 g x.1 x.2‖₊ : ℝ≥0∞) ^ 2)
  rw [himg] at hcv
  rw [hcv]
  have h1 : ∀ᵐ x : ℂ × ℂ ∂(volume : Measure (ℂ × ℂ)), x.1 ≠ 0 := by
    rw [Measure.volume_eq_prod]
    exact Measure.quasiMeasurePreserving_fst.ae (volume.ae_ne 0)
  have h2 : ∀ᵐ x : ℂ × ℂ ∂(volume : Measure (ℂ × ℂ)), x.2 ≠ 0 := by
    rw [Measure.volume_eq_prod]
    exact Measure.quasiMeasurePreserving_snd.ae (volume.ae_ne 0)
  have hdel : (volume : Measure (ℂ × ℂ)).restrict (U ×ˢ U) =
      (volume : Measure (ℂ × ℂ)).restrict (unitDisc ×ˢ unitDisc) := by
    apply Measure.restrict_congr_set
    refine Filter.eventuallyEqSet_iff.2 ?_
    filter_upwards [h1, h2] with x hx1 hx2
    simp [U, hx1, hx2]
  rw [hdel]
  apply lintegral_congr_ae
  filter_upwards [s2c_diag_ae, ae_restrict_mem (measurableSet_ball.prod measurableSet_ball),
    ae_restrict_of_ae h1, ae_restrict_of_ae h2] with x hx hxm hx1 hx2
  obtain ⟨s, t⟩ := x
  simp only at hx hxm hx1 hx2
  have hsE : s⁻¹ ∈ unitDiscExterior := a21_inv_punctured ⟨hxm.1, hx1⟩
  have htE : t⁻¹ ∈ unitDiscExterior := a21_inv_punctured ⟨hxm.2, hx2⟩
  have hK4 := s2c_kerK4_eq hφd hφi hφ0 hb hg hsE htE (inv_injective.ne hx)
  rw [inv_inv, inv_inv] at hK4
  have e1 : ∀ z : ℂ, (‖z‖₊ : ℝ≥0∞) ^ 2 = ENNReal.ofReal (‖z‖ ^ 2) := fun z => by
    rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm, enorm_eq_nnnorm]
  have hdet : (f' (s, t)).det = ‖-(s ^ 2)⁻¹‖ ^ 2 * ‖-(t ^ 2)⁻¹‖ ^ 2 := by
    have d1 := LiZhongQC.det_restrictScalars_toSpanSingleton (-(s ^ 2)⁻¹)
    have d2 := LiZhongQC.det_restrictScalars_toSpanSingleton (-(t ^ 2)⁻¹)
    have hco : ((f' (s, t) : (ℂ × ℂ) →L[ℝ] (ℂ × ℂ)) : (ℂ × ℂ) →ₗ[ℝ] (ℂ × ℂ)) =
        LinearMap.prodMap
          (((ContinuousLinearMap.toSpanSingleton ℂ (-(s ^ 2)⁻¹)).restrictScalars ℝ : ℂ →L[ℝ] ℂ) : ℂ →ₗ[ℝ] ℂ)
          (((ContinuousLinearMap.toSpanSingleton ℂ (-(t ^ 2)⁻¹)).restrictScalars ℝ : ℂ →L[ℝ] ℂ) : ℂ →ₗ[ℝ] ℂ) := rfl
    have h3 : (f' (s, t)).det = LinearMap.det
        (LinearMap.prodMap
          (((ContinuousLinearMap.toSpanSingleton ℂ (-(s ^ 2)⁻¹)).restrictScalars ℝ : ℂ →L[ℝ] ℂ) : ℂ →ₗ[ℝ] ℂ)
          (((ContinuousLinearMap.toSpanSingleton ℂ (-(t ^ 2)⁻¹)).restrictScalars ℝ : ℂ →L[ℝ] ℂ) : ℂ →ₗ[ℝ] ℂ)) := by
      rw [ContinuousLinearMap.det, hco]
    rw [h3, LinearMap.det_prodMap]
    exact congrArg₂ (· * ·) d1 d2
  show ENNReal.ofReal |(f' (s, t)).det| * (‖kerK4 g s⁻¹ t⁻¹‖₊ : ℝ≥0∞) ^ 2 = (‖kerK1 φ s t‖₊ : ℝ≥0∞) ^ 2
  rw [e1, e1, ← ENNReal.ofReal_mul (abs_nonneg _), hK4, hdet]
  congr 1
  rw [abs_of_nonneg (by positivity)]
  have hs0 : s ≠ 0 := hx1
  have ht0 : t ≠ 0 := hx2
  simp only [norm_neg, norm_inv, norm_pow, norm_mul]
  have hs' : 0 < ‖s‖ := norm_pos_iff.2 hs0
  have ht' : 0 < ‖t‖ := norm_pos_iff.2 ht0
  field_simp


/-- **Lemma 2.5** (TT:4016–4046), with **(2.5)**.
- `∬∬_{𝔻×𝔻} |K₁(z, w)|² < ∞` iff `K₁` is Hilbert–Schmidt, i.e. iff `Σ_{n,m} nm |b_{-n,-m}|² < ∞` (iff `𝖪₁` is of trace
  class).
- In that case `Tr 𝖪₁ = Σ nm|b_{-n,-m}|² = ∬∬ |K₁|² = ∬ 𝖪₁(z, z) d²z`.
- Then `𝒮(f) ∈ A₂(𝔻)`, where `𝒮(f)(z) = -6π lim_{w → z} K₁(z, w)`.

Similarly for `K₄` and `𝖪₄`. 
Proved here as `s2c_lemma_2_5`; statement identical to `lemma_2_5`. -/
theorem s2c_lemma_2_5 {f g : ℂ → ℂ} (h : IsNormalizedDisjointPair f g)
    (hF : volume ((f '' unitDisc ∪ g '' unitDiscExterior)ᶜ) = 0) :
    let b := grunsky f g
    ((∫⁻ p in unitDisc ×ˢ unitDisc, (‖kerK1 f p.1 p.2‖₊ : ℝ≥0∞) ^ 2) < ∞ ↔
        Summable fun p : ℕ × ℕ => ((p.1 + 1) * (p.2 + 1) : ℝ) * ‖b (-(p.1 + 1 : ℤ)) (-(p.2 + 1 : ℤ))‖ ^ 2) ∧
      ((∫⁻ p in unitDisc ×ˢ unitDisc, (‖kerK1 f p.1 p.2‖₊ : ℝ≥0∞) ^ 2) < ∞ →
        ENNReal.ofReal (∑' p : ℕ × ℕ, ((p.1 + 1) * (p.2 + 1) : ℝ) * ‖b (-(p.1 + 1 : ℤ)) (-(p.2 + 1 : ℤ))‖ ^ 2) =
            ∫⁻ p in unitDisc ×ˢ unitDisc, (‖kerK1 f p.1 p.2‖₊ : ℝ≥0∞) ^ 2 ∧
          (∫ z in unitDisc, kerKK1 f z z) =
            ∑' p : ℕ × ℕ, ((p.1 + 1) * (p.2 + 1) : ℝ) * ‖b (-(p.1 + 1 : ℤ)) (-(p.2 + 1 : ℤ))‖ ^ 2 ∧
          schwarzianHol f ∈ A2fun unitDisc) ∧
      (∀ z ∈ unitDisc, Tendsto (fun w => -6 * π * kerK1 f z w) (𝓝[≠] z) (𝓝 (schwarzianHol f z))) ∧
      ((∫⁻ p in unitDiscExterior ×ˢ unitDiscExterior, (‖kerK4 g p.1 p.2‖₊ : ℝ≥0∞) ^ 2) < ∞ ↔
        Summable fun p : ℕ × ℕ => ((p.1 + 1) * (p.2 + 1) : ℝ) * ‖b (p.1 + 1) (p.2 + 1)‖ ^ 2) := by
  intro b
  have hb := (grunsky_spec h).1.2.2.2.1
  have hwnn : ∀ r : ℕ × ℕ, 0 ≤ ((r.1 + 1) * (r.2 + 1) : ℝ) * ‖b (-(r.1 + 1 : ℤ)) (-(r.2 + 1 : ℤ))‖ ^ 2 :=
    fun r => by positivity
  have hM1 := s2c_kerK1_lintegral h.1 h.2.1 (a := fun p q => grunsky f g (-(p : ℤ)) (-(q : ℤ)))
    (b00 := grunsky f g 0 0) hb
  have hM1' : (∫⁻ x in unitDisc ×ˢ unitDisc, (‖kerK1 f x.1 x.2‖₊ : ℝ≥0∞) ^ 2) =
      ∑' r : ℕ × ℕ, ENNReal.ofReal (((r.1 + 1) * (r.2 + 1) : ℝ) *
        ‖b (-(r.1 + 1 : ℤ)) (-(r.2 + 1 : ℤ))‖ ^ 2) := by
    rw [hM1]
    refine tsum_congr (fun r => ?_)
    simp only [b, Nat.cast_add, Nat.cast_one, neg_add]
  refine ⟨?_, ?_, fun z hz => s2c_schwarzian_limit h.1 h.2.1 hz, ?_⟩
  · rw [hM1']
    exact s2c_tsum_ofReal_lt_top_iff hwnn
  · intro hlt
    have hsum : Summable fun r : ℕ × ℕ => ((r.1 + 1) * (r.2 + 1) : ℝ) *
        ‖b (-(r.1 + 1 : ℤ)) (-(r.2 + 1 : ℤ))‖ ^ 2 := (s2c_tsum_ofReal_lt_top_iff hwnn).1 (hM1' ▸ hlt)
    have hEq : ENNReal.ofReal (∑' r : ℕ × ℕ, ((r.1 + 1) * (r.2 + 1) : ℝ) *
        ‖b (-(r.1 + 1 : ℤ)) (-(r.2 + 1 : ℤ))‖ ^ 2) =
        ∫⁻ x in unitDisc ×ˢ unitDisc, (‖kerK1 f x.1 x.2‖₊ : ℝ≥0∞) ^ 2 := by
      rw [hM1', ENNReal.ofReal_tsum_of_nonneg hwnn hsum]
    refine ⟨hEq, ?_, s2c_schwarzian_A2 h.1 h.2.1 (a := fun p q => grunsky f g (-(p : ℤ)) (-(q : ℤ))) (b00 := grunsky f g 0 0) hb hlt.ne⟩
    rw [s2c_kerKK1_integral h.1 h.2.1 (a := fun p q => grunsky f g (-(p : ℤ)) (-(q : ℤ))) (b00 := grunsky f g 0 0) hb hlt.ne, ← hEq,
      ENNReal.toReal_ofReal (tsum_nonneg hwnn), Complex.ofReal_tsum]
  · obtain ⟨φ, b', hφd, hφi, hφ0, hφ1, hb', hbg, hg⟩ := g1_inverted_exterior h
    obtain ⟨d, hd0, hd'⟩ := disk_axis_coefficients_exist hφd hφi hφ1 0
    have hd : ∀ s ∈ unitDisc, ∃ S : ℂ, HasSum (fun j => d j * s ^ j) S ∧ exp (-S) = dslope φ 0 s := by
      intro s hs
      simpa only [zero_sub] using hd' s hs
    have hexp := faber_inverted_full_series h hφd hφi hφ0 hφ1 hb' hbg hg hd
    have hM4 := s2c_kerK4_lintegral hφd hφi hφ0 hb' hg
    have hM4' := s2c_kerK1_lintegral hφd hφi
      (a := faberFillAxes (fun m n => grunsky f g (m + 1) (n + 1)) d) (b00 := 0) hexp
    rw [hM4, hM4']
    have hw4 : ∀ r : ℕ × ℕ, ENNReal.ofReal (((r.1 + 1) * (r.2 + 1) : ℝ) *
        ‖faberFillAxes (fun m n => grunsky f g (m + 1) (n + 1)) d (r.1 + 1) (r.2 + 1)‖ ^ 2) =
        ENNReal.ofReal (((r.1 + 1) * (r.2 + 1) : ℝ) * ‖b (r.1 + 1) (r.2 + 1)‖ ^ 2) := by
      intro r
      rw [faberFillAxes_succ]
    simp_rw [hw4]
    exact s2c_tsum_ofReal_lt_top_iff (fun r => by positivity)

/-! ### Originals relocated from `S2_Grunsky` (2026-10-26) -/

/-- (TT:3949–4000) For a normalized disjoint pair with null `F`:
- the kernels have the expansions `K₁ = (1/π) Σ nm b_{-n,-m} z^{n-1} w^{m-1}` (on `𝔻 × 𝔻`) and
  `K₄ = (1/π) Σ nm b_{nm} z^{-n-1} w^{-m-1}` (on `𝔻* × 𝔻*`);
- the operators `(K_l ψ)(z) = ∬ K_l(z, w) \overline{ψ(w)} d²w` correspond to `B_l` in the bases `e_n`, `f_n`:
  `K₁ e_k = Σ_n (B₁)_{nk} e_n` on `𝔻` and `K₄ f_k = Σ_n (B₄)_{nk} f_n` on `𝔻*`. -/
theorem kernels_spec {f g : ℂ → ℂ} (h : IsNormalizedDisjointPair f g)
    (hF : volume ((f '' unitDisc ∪ g '' unitDiscExterior)ᶜ) = 0) :
    let b := grunsky f g
    (∀ z ∈ unitDisc, ∀ w ∈ unitDisc, z ≠ w → HasSum (fun p : ℕ × ℕ =>
        1 / π * (((p.1 + 1) * (p.2 + 1) : ℕ) : ℂ) * b (-(p.1 + 1 : ℤ)) (-(p.2 + 1 : ℤ)) * z ^ p.1 * w ^ p.2) (kerK1 f z w)) ∧
      (∀ z ∈ unitDiscExterior, ∀ w ∈ unitDiscExterior, z ≠ w → HasSum (fun p : ℕ × ℕ =>
        1 / π * (((p.1 + 1) * (p.2 + 1) : ℕ) : ℂ) * b (p.1 + 1) (p.2 + 1) * z ^ (-(p.1 : ℤ) - 2) * w ^ (-(p.2 : ℤ) - 2))
        (kerK4 g z w)) ∧
      (∀ k, ∀ z ∈ unitDisc, HasSum (fun n => B1 b n k * basisE n z)
        (∫ w in unitDisc, kerK1 f z w * conj (basisE k w))) ∧
      ∀ k, ∀ z ∈ unitDiscExterior, HasSum (fun n => B4 b n k * basisF n z)
        (∫ w in unitDiscExterior, kerK4 g z w * conj (basisF k w)) :=
  s2c_kernels_spec h hF

/-- **Lemma 2.5** (TT:4016–4046), with **(2.5)**.
- `∬∬_{𝔻×𝔻} |K₁(z, w)|² < ∞` iff `K₁` is Hilbert–Schmidt, i.e. iff `Σ_{n,m} nm |b_{-n,-m}|² < ∞` (iff `𝖪₁` is of trace
  class).
- In that case `Tr 𝖪₁ = Σ nm|b_{-n,-m}|² = ∬∬ |K₁|² = ∬ 𝖪₁(z, z) d²z`.
- Then `𝒮(f) ∈ A₂(𝔻)`, where `𝒮(f)(z) = -6π lim_{w → z} K₁(z, w)`.

Similarly for `K₄` and `𝖪₄`. -/
theorem lemma_2_5 {f g : ℂ → ℂ} (h : IsNormalizedDisjointPair f g)
    (hF : volume ((f '' unitDisc ∪ g '' unitDiscExterior)ᶜ) = 0) :
    let b := grunsky f g
    ((∫⁻ p in unitDisc ×ˢ unitDisc, (‖kerK1 f p.1 p.2‖₊ : ℝ≥0∞) ^ 2) < ∞ ↔
        Summable fun p : ℕ × ℕ => ((p.1 + 1) * (p.2 + 1) : ℝ) * ‖b (-(p.1 + 1 : ℤ)) (-(p.2 + 1 : ℤ))‖ ^ 2) ∧
      ((∫⁻ p in unitDisc ×ˢ unitDisc, (‖kerK1 f p.1 p.2‖₊ : ℝ≥0∞) ^ 2) < ∞ →
        ENNReal.ofReal (∑' p : ℕ × ℕ, ((p.1 + 1) * (p.2 + 1) : ℝ) * ‖b (-(p.1 + 1 : ℤ)) (-(p.2 + 1 : ℤ))‖ ^ 2) =
            ∫⁻ p in unitDisc ×ˢ unitDisc, (‖kerK1 f p.1 p.2‖₊ : ℝ≥0∞) ^ 2 ∧
          (∫ z in unitDisc, kerKK1 f z z) =
            ∑' p : ℕ × ℕ, ((p.1 + 1) * (p.2 + 1) : ℝ) * ‖b (-(p.1 + 1 : ℤ)) (-(p.2 + 1 : ℤ))‖ ^ 2 ∧
          schwarzianHol f ∈ A2fun unitDisc) ∧
      (∀ z ∈ unitDisc, Tendsto (fun w => -6 * π * kerK1 f z w) (𝓝[≠] z) (𝓝 (schwarzianHol f z))) ∧
      ((∫⁻ p in unitDiscExterior ×ˢ unitDiscExterior, (‖kerK4 g p.1 p.2‖₊ : ℝ≥0∞) ^ 2) < ∞ ↔
        Summable fun p : ℕ × ℕ => ((p.1 + 1) * (p.2 + 1) : ℝ) * ‖b (p.1 + 1) (p.2 + 1)‖ ^ 2) :=
  s2c_lemma_2_5 h hF

end TakhtajanTeo.Ch2
