import TakhtajanTeo.Appendix.PeriodCompactSymmetric
import TakhtajanTeo.Appendix.PeriodSymmetricRepresentative
import TakhtajanTeo.Appendix.PeriodCoefficientContinuity
import TakhtajanTeo.Appendix.PeriodCompactLimits
import TakhtajanTeo.Ch2.PeriodGrunskyBounds
import TakhtajanTeo.Ch2.S2_Cor29

/-! # Compactness characterization of the period mapping

The converse uses actual vanishing representatives, L∞ collar cutoffs,
Cui's proved L² estimate, Hilbert–Schmidt compactness, and norm continuity.
It does not assume B.9 or a compactness conclusion for symmetric classes.
-/
open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal ComplexConjugate Classical Real
noncomputable section
namespace TakhtajanTeo
open LiZhongQC Ch2
namespace AppB

-- B1
theorem pcb_period_rep {p : T1} {ν : LinfStarBall} (hν : Phi ν = p) :
    periodP p = B1 (grunsky (fsans ν) (gsans ν)) := by
  have hc : teichSetoid (Quotient.out p : LinfStarBall) ν :=
    Quotient.exact ((Quotient.out_eq p).trans hν.symm)
  exact congrArg B1 (FB.fb_grunsky_class (Quotient.out p).2 ν.2 hc)

-- B2
theorem pcb_cutoff_T01 {ν : LinfStarBall} {r : ℝ} (hr : 1 < r)
    (hz : ∀ᵐ z ∂(volume.restrict unitDiscExterior), ‖z‖ < r → (ν : LinfStar) z = 0) :
    Phi ν ∈ T01 := by
  have hlog : 0 < Real.log r := Real.log_pos hr
  have hb : ∀ᵐ z ∂(volume.restrict unitDiscExterior),
      ‖(ν : LinfStar) z‖ ≤ (‖(ν : LinfStar)‖ / Real.log r) * Real.log ‖z‖ := by
    filter_upwards [hz, LinfStar_ae_norm_le (ν : LinfStar),
      ae_restrict_mem resolvent_exterior_isOpen.measurableSet] with z hzero hnorm hzE
    have hz1 : 1 < ‖z‖ := hzE
    by_cases hzr : ‖z‖ < r
    · rw [hzero hzr, norm_zero]
      exact mul_nonneg (div_nonneg (norm_nonneg _) hlog.le) (Real.log_nonneg hz1.le)
    · calc ‖(ν : LinfStar) z‖ ≤ ‖(ν : LinfStar)‖ := hnorm
        _ = (‖(ν : LinfStar)‖ / Real.log r) * Real.log r := by field_simp
        _ ≤ (‖(ν : LinfStar)‖ / Real.log r) * Real.log ‖z‖ :=
          mul_le_mul_of_nonneg_left (Real.log_le_log (by linarith) (le_of_not_gt hzr))
            (div_nonneg (norm_nonneg _) hlog.le)
  have hL2 := r19_L2 ν.2 hb
  have hk1 : ‖(ν : LinfStar)‖ < 1 := mem_ball_zero_iff.mp ν.2
  obtain ⟨C, _, hA2⟩ := CUI.cui_A2_bound (norm_nonneg (ν : LinfStar)) hk1
  have hfin : normA2 unitDisc (AInf.toFun (bersPhi (ν : LinfStar))) < ⊤ :=
    lt_of_le_of_lt (hA2 (ν : LinfStar) le_rfl)
      (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hL2)
  rw [TakhtajanTeo.cor_3_2]
  change AInf.toFun (bers (Phi ν)) ∈ A2fun unitDisc
  rw [bers_Phi]
  exact ⟨(bersPhi (ν : LinfStar)).2, hfin⟩

-- B3
theorem pcb_symmetric_compact {p : T1} (hp : p ∈ symmetricT) :
    IsCompactMat (periodP p) := by
  obtain ⟨ν, hν, happ⟩ := psr_approximation hp
  choose η r hr hn he hz using fun n : ℕ =>
    happ (1 / ((n : ℝ) + 1)) (by positivity)
  have hd : Tendsto (fun n => ‖(η n : LinfStar) - (ν : LinfStar)‖) atTop (𝓝 0) :=
    squeeze_zero (fun n => norm_nonneg _) he tendsto_one_div_add_atTop_nhds_zero_nat
  have hη : Tendsto (fun n => (η n : LinfStar)) atTop (𝓝 (ν : LinfStar)) :=
    tendsto_iff_norm_sub_tendsto_zero.mpr hd
  have hB : ∀ n, IsCompactMat (B1 (grunsky (fsans (η n)) (gsans (η n)))) := by
    intro n
    have hclass := pcb_cutoff_T01 (hr n) (hz n)
    have hhs := (cor_2_9 (Phi (η n))).1.mp hclass
    change Summable (fun q : ℕ × ℕ => ‖periodP (Phi (η n)) q.1 q.2‖ ^ 2) at hhs
    rw [pcb_period_rep rfl] at hhs
    exact pcl_hilbert_schmidt (pgb_bounded (η n).2 (by simp)) hhs
  rw [pcb_period_rep hν]
  exact pcl_compact_of_limit (pgb_bounded ν.2 (by simp)) hB (pcc_tendsto ν.2 hη)

-- B4
theorem pcb_thm_B_4 (p : T1) : IsCompactMat (periodP p) ↔ p ∈ symmetricT := by
  exact ⟨pcs_compact_symmetric, pcb_symmetric_compact⟩

-- B5
theorem pcb_remark_B_9 {p : T1} (hp : p ∈ symmetricT) :
    let f := fsans (Quotient.out p : LinfStarBall)
    Tendsto (fun n => ⨆ z ∈ unitDisc,
        ENNReal.ofReal ((1 - ‖z‖ ^ 2) ^ 2 * ‖schwarzianHol (dilateF f n) z - schwarzianHol f z‖)) atTop (𝓝 0) ∧
      Tendsto (fun n => kerOpNorm fun z w => kerK1 (dilateF f n) z w - kerK1 f z w) atTop (𝓝 0) := by
  exact remark_B_9_of_compact (pcb_symmetric_compact hp)

/-! ## Original declarations (unchanged statements) -/

/-- **Theorem B.4** (TT:6054–6374). `𝒫̂(S) = 𝒮_∞ ∩ 𝒫̂(T(1))`: `B₁(𝖿^μ)` is compact iff `[μ] ∈ S`. -/
theorem thm_B_4 (p : T1) : IsCompactMat (periodP p) ↔ p ∈ symmetricT := by
  exact pcb_thm_B_4 p

/-- **Remark B.9** (TT:6376–6380). For `[μ] ∈ S`, with `f = 𝖿^μ`, `𝒮(f_n) → 𝒮(f)` in `A_∞(𝔻)` and `K₁(f_n) → K₁(f)` in
operator norm. -/
theorem remark_B_9 {p : T1} (hp : p ∈ symmetricT) :
    let f := fsans (Quotient.out p : LinfStarBall)
    Tendsto (fun n => ⨆ z ∈ unitDisc,
        ENNReal.ofReal ((1 - ‖z‖ ^ 2) ^ 2 * ‖schwarzianHol (dilateF f n) z - schwarzianHol f z‖)) atTop (𝓝 0) ∧
      Tendsto (fun n => kerOpNorm fun z w => kerK1 (dilateF f n) z w - kerK1 f z w) atTop (𝓝 0) := by
  exact pcb_remark_B_9 hp

end AppB
end TakhtajanTeo
