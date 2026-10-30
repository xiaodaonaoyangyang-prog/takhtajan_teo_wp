import TakhtajanTeo.Appendix.CompactBergmanDilation

/-! # Actual integral-operator norm convergence under compactness

The endpoints in this module assume compactness. They do not replace the
symmetric-class hypothesis of the original Remark B.9.
-/

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal ComplexConjugate Classical Real
noncomputable section
namespace TakhtajanTeo
open LiZhongQC Ch2
namespace AppB

theorem b9_A21_norm_of_coeff {f : ℂ → ℂ} {x : ℕ → ℂ} (hf : f ∈ A21fun unitDisc)
    (hs : ∀ z ∈ unitDisc, HasSum (fun n => x n * basisE n z) (f z)) :
    normA21 unitDisc f = ENNReal.ofReal (Real.sqrt (sqSum x)) := by
  have hh := congrArg (fun a : ℝ≥0∞ => a ^ (1/2 : ℝ))
    (A21_ell2_norm_sq hf (A21_basis_parseval hf hs))
  rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul] at hh
  norm_num at hh
  rw [ENNReal.ofReal_rpow_of_nonneg (tsum_nonneg fun _ => sq_nonneg _) (by norm_num),
    ← Real.sqrt_eq_rpow] at hh
  exact hh

/-- Norm comparison for the actual difference kernel, with integrability
justified by its A21 rows before subtracting the Bochner integrals. -/
theorem b9_kernel_norm_le_matrix {B : ℕ → ℕ → ℂ} {K Kr : ℂ → ℂ → ℂ}
    (hsym : ∀ m n, B m n = B n m)
    (hrow : ∀ m, Summable (fun n => ‖B m n‖ ^ 2) ∧ (∑' n, ‖B m n‖ ^ 2) ≤ 1)
    (hB : B7Contractive B) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    (hK : ∀ z ∈ unitDisc, ∀ w ∈ unitDisc, z ≠ w →
      HasSum (fun p : ℕ × ℕ => B p.1 p.2 * basisE p.1 z * basisE p.2 w) (K z w))
    (hKr : ∀ z ∈ unitDisc, ∀ w ∈ unitDisc, z ≠ w →
      HasSum (fun p : ℕ × ℕ => b7Matrix r B p.1 p.2 * basisE p.1 z * basisE p.2 w) (Kr z w))
    (hKA : ∀ z ∈ unitDisc, K z ∈ A21fun unitDisc)
    (hKrA : ∀ z ∈ unitDisc, Kr z ∈ A21fun unitDisc) :
    kerOpNorm (fun z w => Kr z w - K z w) ≤ matOpNorm (fun m n => b7Matrix r B m n - B m n) := by
  have hBb : IsBoundedMat B := ⟨1, fun x hx =>
    ⟨(hB x hx).1, by simpa only [one_mul, sqSum, matApply, b7Apply] using (hB x hx).2⟩⟩
  have hBr := b9_isBounded_dilate hBb hr0 hr1
  have hE := b9_isBounded_sub hBr hBb
  apply iSup_le
  intro ψ
  apply iSup_le
  rintro ⟨hψ,hψ1⟩
  obtain ⟨x,hx,hxe,hmass⟩ := A21_exists_ell2_expansion hψ
  have hxc : IsL2 (fun n => conj (x n)) := by simpa only [IsL2, Complex.norm_conj] using hx
  have hx1 : sqSum (fun n => conj (x n)) ≤ 1 := by
    have hs := A21_ell2_norm_sq hψ hmass
    have he : ENNReal.ofReal (sqSum x) ≤ 1 := by
      change ENNReal.ofReal (∑' n, ‖x n‖ ^ 2) ≤ 1
      rw [← hs]
      simpa only [one_pow] using pow_le_pow_left' hψ1 2
    have hh := ENNReal.toReal_mono ENNReal.one_ne_top he
    simpa only [sqSum, Complex.norm_conj, ENNReal.toReal_ofReal
      (tsum_nonneg fun _ => sq_nonneg _), ENNReal.toReal_one] using hh
  have hA := b7_kernel_action hsym hrow hB hK hψ hx hxe
  have hAr := b7_kernel_action (b7_matrix_symm hsym r) (b7_matrix_row hrow hr0 hr1)
    (b7_matrix_contractive hB hr0 hr1) hKr hψ hx hxe
  let D : ℂ → ℂ := fun z => (∫ w in unitDisc, Kr z w * conj (ψ w)) -
    ∫ w in unitDisc, K z w * conj (ψ w)
  have hD : D ∈ A21fun unitDisc := by
    apply (mem_A21fun_iff_memLp isOpen_ball.measurableSet).mpr
    exact ⟨hAr.1.1.sub hA.1.1, (a21_memLp_two isOpen_ball.measurableSet hAr.1).sub
      (a21_memLp_two isOpen_ball.measurableSet hA.1)⟩
  have hs : ∀ z ∈ unitDisc, HasSum
      (fun m => matApply (fun m n => b7Matrix r B m n - B m n) (fun n => conj (x n)) m * basisE m z)
      (D z) := by
    intro z hz
    rw [b9_mat_apply_sub hBr hBb hxc]
    exact ((hAr.2 z hz).sub (hA.2 z hz)).congr_fun (fun m => by
      dsimp only [matApply,b7Apply]; ring)
  have hi : ∀ z ∈ unitDisc, (∫ w in unitDisc, (Kr z w - K z w) * conj (ψ w)) = D z := by
    intro z hz
    have hk : Integrable (fun w => K z w * conj (ψ w)) (volume.restrict unitDisc) :=
      (a21_memLp_two isOpen_ball.measurableSet (hKA z hz)).integrable_mul
        (a21_memLp_two isOpen_ball.measurableSet hψ).star
    have hkr : Integrable (fun w => Kr z w * conj (ψ w)) (volume.restrict unitDisc) :=
      (a21_memLp_two isOpen_ball.measurableSet (hKrA z hz)).integrable_mul
        (a21_memLp_two isOpen_ball.measurableSet hψ).star
    simp only [sub_mul]
    exact integral_sub hkr hk
  have hn : normA21 unitDisc (fun z => ∫ w in unitDisc, (Kr z w - K z w) * conj (ψ w)) =
      normA21 unitDisc D := by
    unfold normA21
    congr 1
    apply lintegral_congr_ae
    filter_upwards [ae_restrict_mem (show MeasurableSet unitDisc from measurableSet_ball)] with z hz
    rw [hi z hz]
  rw [hn, b9_A21_norm_of_coeff hD hs, matOpNorm_of_bounded hE]
  exact le_iSup_of_le (fun n => conj (x n)) (le_iSup_of_le ⟨hxc,hx1⟩ le_rfl)

/-- Conditional operator-norm part of B.9, with the explicit compactness
hypothesis and the original integral-operator norm. -/
theorem b9_kernel_norm_tendsto_of_compact {p : T1} (hK : IsCompactMat (periodP p)) :
    let f := fsans (Quotient.out p : LinfStarBall)
    Tendsto (fun n => kerOpNorm (fun z w => kerK1 (dilateF f n) z w - kerK1 f z w)) atTop (𝓝 0) := by
  let μ : LinfStarBall := Quotient.out p
  let f := fsans μ
  have hpair := b8_welding_normalized_pair μ.2
  have hf : IsUnivalentDisc f := ⟨hpair.1,hpair.2.1⟩
  obtain ⟨hsym,hrow,hB,hseries⟩ := b8_pair_model hpair
  let r : ℕ → ℝ := fun n => (n : ℝ)/(n+1)
  have hr0 : ∀ n, 0 ≤ r n := by intro n; dsimp [r]; positivity
  have hr1 : ∀ n, r n ≤ 1 := by
    intro n
    dsimp [r]
    apply (div_le_one (by positivity)).mpr
    linarith
  have hr : Tendsto r atTop (𝓝 1) := tendsto_natCast_div_add_atTop (1 : ℝ)
  have hlim := b9_compact_matrix_norm_tendsto hK hr0 hr1 hr
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    (Eventually.of_forall fun _ => bot_le)
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hfn : IsUnivalentDisc (dilateF f n) :=
    (dilateF_normalized hf hpair.2.2.1 hpair.2.2.2.1 hn).1
  exact b9_kernel_norm_le_matrix hsym hrow hB (hr0 n) (hr1 n) hseries
    (fun z hz w hw hzw => kerK1_dilateF_bergman_series hf hseries hn hz hw hzw)
    (fun z hz => kerK1_row_mem_A21 hf hz) (fun z hz => kerK1_row_mem_A21 hfn hz)

/-- Both conclusions of B.9 under compactness. This is a conditional support
theorem; the original symmetricT statement is deliberately unchanged. -/
theorem remark_B_9_of_compact {p : T1} (hK : IsCompactMat (periodP p)) :
    let f := fsans (Quotient.out p : LinfStarBall)
    Tendsto (fun n => ⨆ z ∈ unitDisc,
      ENNReal.ofReal ((1 - ‖z‖ ^ 2) ^ 2 * ‖schwarzianHol (dilateF f n) z - schwarzianHol f z‖))
      atTop (𝓝 0) ∧
    Tendsto (fun n => kerOpNorm (fun z w => kerK1 (dilateF f n) z w - kerK1 f z w)) atTop (𝓝 0) := by
  let μ : LinfStarBall := Quotient.out p
  let f := fsans μ
  have hpair := b8_welding_normalized_pair μ.2
  have hf : IsUnivalentDisc f := ⟨hpair.1,hpair.2.1⟩
  have hk := b9_kernel_norm_tendsto_of_compact hK
  refine ⟨?_,hk⟩
  have hh := ENNReal.Tendsto.const_mul (a := 6) hk (Or.inr (by norm_num))
  simp only [mul_zero] at hh
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hh
    (Eventually.of_forall fun _ => bot_le)
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hfn : IsUnivalentDisc (dilateF f n) :=
    (dilateF_normalized hf hpair.2.2.1 hpair.2.2.2.1 hn).1
  apply iSup_le
  intro z
  apply iSup_le
  intro hz
  have hb := lemma_B_5 hfn hf hz
  exact hb.1.trans (mul_le_mul' le_rfl hb.2)

end AppB
end TakhtajanTeo
