import TakhtajanTeo.Appendix.BergmanDilation

/-! # Actual integral kernels in the contractive Bergman coefficient model -/

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal ComplexConjugate Classical Real
noncomputable section
namespace TakhtajanTeo
open LiZhongQC Ch2
namespace AppB

theorem b7_matrix_symm {B : ℕ → ℕ → ℂ} (hs : ∀ m n, B m n = B n m) (r : ℝ) :
    ∀ m n, b7Matrix r B m n = b7Matrix r B n m := by
  intro m n
  dsimp [b7Matrix]
  rw [hs m n]
  ring

theorem b7_matrix_row {B : ℕ → ℕ → ℂ}
    (hrow : ∀ m, Summable (fun n => ‖B m n‖ ^ 2) ∧ (∑' n, ‖B m n‖ ^ 2) ≤ 1)
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    ∀ m, Summable (fun n => ‖b7Matrix r B m n‖ ^ 2) ∧
      (∑' n, ‖b7Matrix r B m n‖ ^ 2) ≤ 1 := by
  have hb : ∀ m n, ‖b7Matrix r B m n‖ ≤ ‖B m n‖ := by
    intro m n
    simp only [b7Matrix, norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hr0]
    calc r ^ (m + 1) * ‖B m n‖ * r ^ (n + 1) ≤ 1 * ‖B m n‖ * 1 := by
          gcongr <;> exact pow_le_one₀ hr0 hr1
      _ = _ := by ring
  intro m
  have hp : ∀ n, ‖b7Matrix r B m n‖ ^ 2 ≤ ‖B m n‖ ^ 2 :=
    fun n => pow_le_pow_left₀ (norm_nonneg _) (hb m n) 2
  have hh := (hrow m).1.of_nonneg_of_le (fun _ => sq_nonneg _) hp
  exact ⟨hh, (Summable.tsum_le_tsum hp hh (hrow m).1).trans (hrow m).2⟩

/-- The integral action equals the actual convergent Bergman output series. -/
theorem b7_kernel_action {B : ℕ → ℕ → ℂ} {K : ℂ → ℂ → ℂ}
    (hsym : ∀ m n, B m n = B n m)
    (hrow : ∀ m, Summable (fun n => ‖B m n‖ ^ 2) ∧ (∑' n, ‖B m n‖ ^ 2) ≤ 1)
    (hB : B7Contractive B)
    (hK : ∀ z ∈ unitDisc, ∀ w ∈ unitDisc, z ≠ w →
      HasSum (fun p : ℕ × ℕ => B p.1 p.2 * basisE p.1 z * basisE p.2 w) (K z w))
    {ψ : ℂ → ℂ} (hψ : ψ ∈ A21fun unitDisc) {x : ℕ → ℂ}
    (hx : Summable (fun n => ‖x n‖ ^ 2))
    (hxe : ∀ z ∈ unitDisc, HasSum (fun n => x n * basisE n z) (ψ z)) :
    (fun z => ∫ w in unitDisc, K z w * conj (ψ w)) ∈ A21fun unitDisc ∧
      ∀ z ∈ unitDisc, HasSum
        (fun m => b7Apply B (fun n => conj (x n)) m * basisE m z)
        (∫ w in unitDisc, K z w * conj (ψ w)) := by
  have hxc : Summable (fun n => ‖conj (x n)‖ ^ 2) := by simpa only [Complex.norm_conj] using hx
  let y := b7Apply B (fun n => conj (x n))
  have hy := hB (fun n => conj (x n)) hxc
  let T : ℂ → ℂ := fun z => ∑' m, y m * basisE m z
  have hT : T ∈ A21fun unitDisc := (bergman_ell2_series hy.1).1
  have heq : ∀ z ∈ unitDisc, (∫ w in unitDisc, K z w * conj (ψ w)) = T z := by
    intro z hz
    let d : ℕ → ℂ := fun n => ∑' m, B n m * basisE m z
    have hd := hB (fun m => basisE m z) (basisE_sq_summable hz)
    let H : ℂ → ℂ := fun w => ∑' n, d n * basisE n w
    have hH : H ∈ A21fun unitDisc := (bergman_ell2_series hd.1).1
    have hHe : ∀ w ∈ unitDisc, HasSum (fun n => d n * basisE n w) (H w) :=
      fun w hw => (bergman_pair_summable hd.1 (basisE_sq_summable hw)).of_norm.hasSum
    have hconv (n : ℕ) : Summable (fun m => B n m * basisE m z) :=
      (bergman_pair_summable (hrow n).1 (basisE_sq_summable hz)).of_norm
    have hAE : K z =ᵐ[volume.restrict unitDisc] H := by
      filter_upwards [ae_restrict_mem (show MeasurableSet unitDisc from measurableSet_ball),
        (volume.restrict unitDisc).ae_ne z] with w hw hwz
      exact (g2c_kernel_row_series hsym hK hz hw (Ne.symm hwz) hconv).tsum_eq.symm
    calc _ = ∫ w in unitDisc, H w * conj (ψ w) := by
          apply integral_congr_ae
          filter_upwards [hAE] with w hw
          rw [hw]
      _ = ∑' n, d n * conj (x n) := (A21_basis_pairing hH hψ hHe hxe).tsum_eq.symm
      _ = T z := g2c_matrix_pair_comm hsym hrow hxc (basisE_norm_summable hz)
  have hnorm : normA21 unitDisc (fun z => ∫ w in unitDisc, K z w * conj (ψ w)) =
      normA21 unitDisc T := by
    unfold normA21
    congr 1
    apply lintegral_congr_ae
    filter_upwards [ae_restrict_mem (show MeasurableSet unitDisc from measurableSet_ball)] with z hz
    rw [heq z hz]
  refine ⟨⟨hT.1.congr heq, by rw [hnorm]; exact hT.2⟩, ?_⟩
  intro z hz
  rw [heq z hz]
  exact (bergman_pair_summable hy.1 (basisE_sq_summable hz)).of_norm.hasSum

/-- The proved Grunsky construction provides one fixed contractive coefficient
matrix for the original function, with its actual off-diagonal kernel series. -/
theorem b7_grunsky_model {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f unitDisc)
    (hi : InjOn f unitDisc) (hf0 : deriv f 0 = 1) :
    ∃ B : ℕ → ℕ → ℂ, (∀ m n, B m n = B n m) ∧
      (∀ m, Summable (fun n => ‖B m n‖ ^ 2) ∧ (∑' n, ‖B m n‖ ^ 2) ≤ 1) ∧
      B7Contractive B ∧
      ∀ z ∈ unitDisc, ∀ w ∈ unitDisc, z ≠ w →
        HasSum (fun p : ℕ × ℕ => B p.1 p.2 * basisE p.1 z * basisE p.2 w) (kerK1 f z w) := by
  obtain ⟨a, hsym, hexp, hker⟩ := g2c_normalized_kernel_series_exists hf hi hf0
  let B : ℕ → ℕ → ℂ := fun m n =>
    (Real.sqrt (((m : ℝ) + 1) * ((n : ℝ) + 1)) : ℂ) * a (m + 1) (n + 1)
  have hB := g2c_grunsky_matrix_contraction hf hi hsym hexp
  refine ⟨B, ?_, hB.1, ?_, ?_⟩
  · intro m n
    simp only [B, hsym (m + 1) (n + 1), mul_comm ((m : ℝ) + 1)]
  · intro x hx
    exact (hB.2 x hx).2
  · intro z hz w hw hzw
    have hh := (hker z hz w hw hzw).div_const (π : ℂ)
    have hp : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    rw [show ((π : ℂ) * kerK1 f z w) / (π : ℂ) = kerK1 f z w by field_simp] at hh
    exact hh.congr_fun (fun p => g2c_basis_weight a p.1 p.2 z w)

/-- Strong convergence of the genuine integral operators follows from the
fixed coefficient model and its diagonal dilations, not just kernel limits. -/
theorem b7_kernel_strong {B : ℕ → ℕ → ℂ} {K : ℂ → ℂ → ℂ}
    {Kn : ℕ → ℂ → ℂ → ℂ} (hsym : ∀ m n, B m n = B n m)
    (hrow : ∀ m, Summable (fun n => ‖B m n‖ ^ 2) ∧ (∑' n, ‖B m n‖ ^ 2) ≤ 1)
    (hB : B7Contractive B)
    (hK : ∀ z ∈ unitDisc, ∀ w ∈ unitDisc, z ≠ w →
      HasSum (fun p : ℕ × ℕ => B p.1 p.2 * basisE p.1 z * basisE p.2 w) (K z w))
    {r : ℕ → ℝ} (hr0 : ∀ k, 0 ≤ r k) (hr1 : ∀ k, r k ≤ 1)
    (hr : Tendsto r atTop (𝓝 1))
    (hKn : ∀ k, 1 ≤ k → ∀ z ∈ unitDisc, ∀ w ∈ unitDisc, z ≠ w →
      HasSum (fun p : ℕ × ℕ => b7Matrix (r k) B p.1 p.2 * basisE p.1 z * basisE p.2 w)
        (Kn k z w))
    {ψ : ℂ → ℂ} (hψ : ψ ∈ A21fun unitDisc) :
    Tendsto (fun k => normA21 unitDisc (fun z =>
      (∫ w in unitDisc, Kn k z w * conj (ψ w)) - ∫ w in unitDisc, K z w * conj (ψ w)))
      atTop (𝓝 0) := by
  obtain ⟨x, hx, hxe, _⟩ := A21_exists_ell2_expansion hψ
  have hxc : Summable (fun n => ‖conj (x n)‖ ^ 2) := by simpa only [Complex.norm_conj] using hx
  let y := b7Apply B (fun n => conj (x n))
  let yn := fun k => b7Apply (b7Matrix (r k) B) (fun n => conj (x n))
  have hA := b7_kernel_action hsym hrow hB hK hψ hx hxe
  have hnorm : ∀ k, 1 ≤ k →
      normA21 unitDisc (fun z => (∫ w in unitDisc, Kn k z w * conj (ψ w)) -
        ∫ w in unitDisc, K z w * conj (ψ w)) =
      (ENNReal.ofReal (∑' m, ‖yn k m - y m‖ ^ 2)) ^ (1 / 2 : ℝ) := by
    intro k hk
    have hAk := b7_kernel_action (b7_matrix_symm hsym (r k))
      (b7_matrix_row hrow (hr0 k) (hr1 k)) (b7_matrix_contractive hB (hr0 k) (hr1 k))
      (hKn k hk) hψ hx hxe
    have hD : (fun z => (∫ w in unitDisc, Kn k z w * conj (ψ w)) -
        ∫ w in unitDisc, K z w * conj (ψ w)) ∈ A21fun unitDisc := by
      apply (mem_A21fun_iff_memLp isOpen_ball.measurableSet).mpr
      exact ⟨hAk.1.1.sub hA.1.1,
        (a21_memLp_two isOpen_ball.measurableSet hAk.1).sub
          (a21_memLp_two isOpen_ball.measurableSet hA.1)⟩
    have hs : ∀ z ∈ unitDisc, HasSum (fun m => (yn k m - y m) * basisE m z)
        ((∫ w in unitDisc, Kn k z w * conj (ψ w)) -
          ∫ w in unitDisc, K z w * conj (ψ w)) := by
      intro z hz
      exact ((hAk.2 z hz).sub (hA.2 z hz)).congr_fun (fun m => by dsimp [yn, y]; ring)
    have hh := congrArg (fun a : ℝ≥0∞ => a ^ (1 / 2 : ℝ))
      (A21_ell2_norm_sq hD (A21_basis_parseval hD hs))
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul] at hh
    norm_num at hh
    exact hh
  have hm := b7_matrix_strong hB (fun m => (hrow m).1) hr0 hr1 hr hxc
  have he := ENNReal.continuous_ofReal.continuousAt.tendsto.comp hm
  have ht := (ENNReal.continuous_rpow_const (y := (1 / 2 : ℝ))).continuousAt.tendsto.comp he
  have ht' : Tendsto (fun k => (ENNReal.ofReal (∑' m, ‖yn k m - y m‖ ^ 2)) ^ (1 / 2 : ℝ))
      atTop (𝓝 0) := by
    simpa only [Function.comp_def, yn, y, ENNReal.ofReal_zero,
      ENNReal.zero_rpow_of_pos (by norm_num : (0 : ℝ) < 1 / 2)] using ht
  apply ht'.congr'
  filter_upwards [eventually_ge_atTop 1] with k hk
  exact (hnorm k hk).symm

end AppB
end TakhtajanTeo
