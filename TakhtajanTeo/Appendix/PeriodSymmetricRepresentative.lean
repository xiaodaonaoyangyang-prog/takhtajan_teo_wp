import TakhtajanTeo.Ch2.S1_SymmetricT
import TakhtajanTeo.Ch1.ComponentRelativeCollar

/-! # Actual vanishing representatives and collar cutoffs for symmetric classes -/
open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal ComplexConjugate Classical Real
noncomputable section
namespace TakhtajanTeo
open LiZhongQC Ch2
namespace AppB

-- R1
theorem psr_representative {p : T1} (hp : p ∈ symmetricT) :
    ∃ ν : LinfStarBall, Phi ν = p ∧ ∀ ε : ℝ, 0 < ε →
      ∃ r : ℝ, 1 < r ∧ ∀ᵐ z ∂(volume.restrict unitDiscExterior),
        ‖z‖ < r → ‖(ν : LinfStar) z‖ ≤ ε := by
  let μ : LinfStarBall := Quotient.out p
  have hq : IsQSCircleHomeo (wA μ) :=
    ⟨wA_circle_sensePreserving μ.2, wA_circle_quasisymmetric μ.2⟩
  obtain ⟨H, ⟨K, hHK⟩, hHs, hHc, hHb, hdec⟩ := symt_plane_extension hq hp
  obtain ⟨e, rfl⟩ := t1_homeomorph hHK hHs
  obtain ⟨M, _, W, _, _, _, hm1, hmI, hm2⟩ := wA_spec μ.2
  have hn1 : wA μ (-1) = -1 := by
    show finPart (wAS _ ((-1 : ℂ) : ExtPlane)) = -1
    rw [hm1]; rfl
  have hnI : wA μ (-I) = -I := by
    show finPart (wAS _ ((-I : ℂ) : ExtPlane)) = -I
    rw [hmI]; rfl
  have hn2 : wA μ 1 = 1 := by
    show finPart (wAS _ ((1 : ℂ) : ExtPlane)) = 1
    rw [hm2]; rfl
  obtain ⟨ν, hν, hae, hw⟩ := r19_exists_mu hHK hHc hHb hn1 hnI hn2
  refine ⟨⟨ν, hν⟩, ?_, fun ε hε => ?_⟩
  · rw [← Quotient.out_eq p]
    exact Quotient.sound (fun z hz => hw z hz)
  · have hev : ∀ᶠ z in crc_exteriorBoundary, ‖complexDilatation e z‖ < ε := by
      have hh := Metric.tendsto_nhds.mp hdec ε hε
      simpa only [dist_zero_right, crc_exteriorBoundary, nhdsWithin, Filter.comap_inf,
        Filter.comap_principal, unitDiscExterior, Set.Ioi, Set.preimage_setOf_eq] using hh
    obtain ⟨r, hr, hsmall⟩ := crc_eventually_collar hev
    refine ⟨r, hr, ?_⟩
    filter_upwards [hae, ae_restrict_mem resolvent_exterior_isOpen.measurableSet] with z hz hzE hzr
    rw [hz]
    exact (hsmall z hzE hzr).le

-- R2
theorem psr_cutoff {ν : LinfStarBall} {ε r : ℝ} (hε : 0 ≤ ε) (_hr : 1 < r)
    (hsmall : ∀ᵐ z ∂(volume.restrict unitDiscExterior), ‖z‖ < r → ‖(ν : LinfStar) z‖ ≤ ε) :
    ∃ η : LinfStarBall, ‖(η : LinfStar)‖ ≤ ‖(ν : LinfStar)‖ ∧
      ‖(η : LinfStar) - (ν : LinfStar)‖ ≤ ε ∧
      ∀ᵐ z ∂(volume.restrict unitDiscExterior), ‖z‖ < r → (η : LinfStar) z = 0 := by
  let F : ℂ → ℂ := {z : ℂ | r ≤ ‖z‖}.indicator (ν : LinfStar)
  have hF : MemLp F ∞ (volume.restrict unitDiscExterior) :=
    (Lp.memLp (ν : LinfStar)).indicator (isClosed_le continuous_const continuous_norm).measurableSet
  have hae := bc_toLinf_ae hF
  have hn : ‖toLinf F‖ ≤ ‖(ν : LinfStar)‖ := by
    apply norm_toLinf_le_of_ae_bound (norm_nonneg _)
    filter_upwards [LinfStar_ae_norm_le (ν : LinfStar)] with z hz
    by_cases hzr : r ≤ ‖z‖
    · simpa [F, hzr] using hz
    · simp [F, hzr]
  have hmem : toLinf F ∈ LinfStarBall :=
    mem_ball_zero_iff.mpr (hn.trans_lt (mem_ball_zero_iff.mp ν.2))
  refine ⟨⟨toLinf F, hmem⟩, hn, ?_, ?_⟩
  · have he : toLinf F - (ν : LinfStar) = toLinf (fun z => F z - (ν : LinfStar) z) := by
      apply Lp.ext
      filter_upwards [Lp.coeFn_sub (toLinf F) (ν : LinfStar), hae,
        bc_toLinf_ae (hF.sub (Lp.memLp (ν : LinfStar)))] with z h1 h2 h3
      simp only [Pi.sub_apply] at h1 h3
      exact h1.trans ((congrArg (fun w : ℂ => w - (ν : LinfStar) z) h2).trans h3.symm)
    change ‖toLinf F - (ν : LinfStar)‖ ≤ ε
    rw [he]
    apply norm_toLinf_le_of_ae_bound hε
    filter_upwards [hsmall] with z hz
    by_cases hzr : r ≤ ‖z‖
    · simpa [F, hzr] using hε
    · simpa [F, hzr] using hz (lt_of_not_ge hzr)
  · filter_upwards [hae] with z hz hzr
    change toLinf F z = 0
    rw [hz]
    simp [F, not_le.mpr hzr]

-- R3
theorem psr_approximation {p : T1} (hp : p ∈ symmetricT) :
    ∃ ν : LinfStarBall, Phi ν = p ∧ ∀ ε : ℝ, 0 < ε →
      ∃ η : LinfStarBall, ∃ r : ℝ, 1 < r ∧
        ‖(η : LinfStar)‖ ≤ ‖(ν : LinfStar)‖ ∧
        ‖(η : LinfStar) - (ν : LinfStar)‖ ≤ ε ∧
        ∀ᵐ z ∂(volume.restrict unitDiscExterior), ‖z‖ < r → (η : LinfStar) z = 0 := by
  obtain ⟨ν, hν, hsmall⟩ := psr_representative hp
  refine ⟨ν, hν, fun ε hε => ?_⟩
  obtain ⟨r, hr, hh⟩ := hsmall ε hε
  obtain ⟨η, hn, he, hz⟩ := psr_cutoff hε.le hr hh
  exact ⟨η, r, hr, hn, he, hz⟩

end AppB
end TakhtajanTeo
