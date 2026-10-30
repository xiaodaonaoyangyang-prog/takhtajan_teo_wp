import TakhtajanTeo.Ch1.GroupBaseLimit

/-! The actual harmonic sequence argument for the S3 origin estimate. -/
open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal NNReal ComplexConjugate Classical Real
noncomputable section
namespace TakhtajanTeo
open LiZhongQC

theorem grp25b_small_sequence {μ : ℕ → LinfStar}
    (hμ : ∀ n, μ n ∈ harmonicBeltrami) (hsmall : ∀ n, ‖μ n‖ < 1 / 4)
    (hlim : Tendsto (fun n => ‖μ n‖) atTop (𝓝 0)) :
    Tendsto (fun n => ‖dz (wA (μ n)) 0‖ ^ 2 / (1 - ‖wA (μ n) 0‖ ^ 2) ^ 2)
      atTop (𝓝 1) := by
  have hball : ∀ n, μ n ∈ LinfStarBall := fun n => by
    simpa [LinfStarBall] using (show ‖μ n‖ < 1 by linarith [hsmall n])
  choose φ hφ using (fun n => Lambda_surjective_harmonic (hμ n))
  have hnorm : ∀ n, ‖φ n‖ / 2 = ‖μ n‖ := by
    intro n
    rw [← Lambda_norm_eq, hφ n]
  let Kn : ℕ → ℝ := fun n => (1 + ‖μ n‖) / (1 - ‖μ n‖)
  have hKbound : ∀ n, Kn n ≤ 3 := by
    intro n
    dsimp only [Kn]
    rw [div_le_iff₀ (by linarith [hsmall n] : 0 < 1 - ‖μ n‖)]
    linarith [hsmall n]
  have hKlim : Tendsto Kn atTop (𝓝 1) := by
    have hc : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
    have he : Kn = ((fun n => 1 + ‖μ n‖) / (fun n => 1 - ‖μ n‖)) := by
      funext n
      rfl
    rw [he]
    simpa only [add_zero, sub_zero, div_one] using
      (hc.add hlim).div (hc.sub hlim) (by norm_num : (1 : ℝ) - 0 ≠ 0)
  have hex : ∀ n, ∃ e : ℂ ≃ₜ ℂ, IsKQC (e : ℂ → ℂ) univ (Kn n) ∧ e 0 = 0 ∧ e 1 = 1 ∧
      DifferentiableOn ℂ (e : ℂ → ℂ) lowerHalf ∧
      (∀ z ∈ upperHalf, complexDilatation (e : ℂ → ℂ) z = -2 * (z.im : ℂ) ^ 2 * awPhi (φ n) (conj z)) ∧
      (∀ z ∈ upperHalf, ContDiffAt ℝ 1 (e : ℂ → ℂ) z ∧ dz (e : ℂ → ℂ) z ≠ 0) ∧
      ∀ z ∈ upperHalf, dz (e : ℂ → ℂ) z = deriv (e : ℂ → ℂ) (conj z) /
        (1 - (z - conj z) * deriv (deriv (e : ℂ → ℂ)) (conj z) /
          (2 * deriv (e : ℂ → ℂ) (conj z))) ^ 2 := by
    intro n
    obtain ⟨H, hHK, hHs, hH0, hH1, hHd, hHμ, hHr, hHj⟩ :=
      grp25b_core (s := ‖φ n‖ / 4) (by positivity) (by linarith [hnorm n, hsmall n])
        (aw_phi_diff (φ n)) (fun z hz => aw_phi_bound (φ n) hz)
    have he : 4 * (‖φ n‖ / 4) / 2 = ‖μ n‖ := by linarith [hnorm n]
    have hHK' : IsKQC H univ (Kn n) := by simpa only [he] using hHK
    obtain ⟨e, rfl⟩ := t1_homeomorph hHK' hHs
    exact ⟨e, hHK', hH0, hH1, hHd, hHμ, hHr, hHj⟩
  choose H hHK hH0 hH1 hHhol hHμ hHreg hHjet using hex
  have hHlim : TendstoLocallyUniformly (fun n => (H n : ℂ → ℂ)) id atTop :=
    grp25b_normalized_tendsto hHK hKbound (fun n => ⟨by
      rw [image_univ]; exact Set.range_eq_univ.mpr (H n).surjective, hH0 n, hH1 n⟩) hKlim
  have hHdz : Tendsto (fun n => dz (H n : ℂ → ℂ) I) atTop (𝓝 1) :=
    grp25b_aw_dz_tendsto hHhol hHlim (fun n => hHjet n I (by simp [upperHalf]))
  choose F τ hFK hF0 hF1 hFdil hτcd hτ0 hτdz hτrel using
    (fun n => grp25b_chart (H n) (hHK n) (hHhol n) (hHμ n) (hHreg n))
  have hFlim : TendstoLocallyUniformly (fun n => (F n : ℂ → ℂ)) id atTop :=
    grp25b_normalized_tendsto hFK hKbound (fun n => ⟨by
      rw [image_univ]; exact Set.range_eq_univ.mpr (F n).surjective, hF0 n, hF1 n⟩) hKlim
  have hWex : ∀ n, ∃ W : ℂ ≃ₜ ℂ, IsNormalizedSolution (W : ℂ → ℂ) (extA (μ n)) ∧
      IsKQC (W : ℂ → ℂ) univ (Kn n) := by
    intro n
    obtain ⟨-, -, W, hW, -, -, -, -, -⟩ := wA_spec (hball n)
    obtain ⟨K, hWK⟩ := hW.1
    have hsol := nxS_genHomeoSolution_congr (thm10_2_genHomeoSolution_of_isKQC hWK).2
      (by simpa only [Measure.restrict_univ] using hW.2.2.2.2)
    have hWK' : IsKQC W univ (Kn n) := thm10_2_isKQC_of_genHomeoSolution isOpen_univ
      (norm_nonneg _) (by linarith [hsmall n]) (extA_isBeltramiCoeff (μ n)) hsol
    obtain ⟨e, rfl⟩ := t1_homeomorph hWK' hW.2.1
    exact ⟨e, hW, hWK'⟩
  choose W hW hWK using hWex
  have hWlim : TendstoLocallyUniformly (fun n => (W n : ℂ → ℂ)) id atTop :=
    grp25b_normalized_tendsto hWK hKbound (fun n => ⟨(hW n).2.1, (hW n).2.2.1, (hW n).2.2.2.1⟩) hKlim
  have hE : IsOpen unitDiscExterior := isOpen_lt continuous_const continuous_norm
  have hψex : ∀ n, ∃ ψ : ℂ → ℂ,
      IsConformalOnto ψ (F n '' unitDiscExterior) (W n '' unitDiscExterior) ∧
        ∀ z ∈ unitDiscExterior, W n z = ψ (F n z) := by
    intro n
    apply grp_stoilow hE ⟨Kn n, nx_isKQC_restrict (hFK n) hE (subset_univ _)⟩
      ⟨Kn n, nx_isKQC_restrict (hWK n) hE (subset_univ _)⟩
    filter_upwards [hFdil n, ae_restrict_of_ae (hW n).2.2.2.2,
      ae_restrict_mem hE.measurableSet] with z hz₁ hz₂ hzE
    rw [hz₁, hz₂, hφ n]
    exact (extA_eq_on_exterior _ hzE).symm
  choose ψ hψ hrel using hψex
  have hHI : Tendsto (fun n => H n I) atTop (𝓝 I) :=
    hHlim.tendstoLocallyUniformlyOn.tendsto_at (mem_univ I)
  have hHm : Tendsto (fun n => H n (-I)) atTop (𝓝 (-I)) :=
    hHlim.tendstoLocallyUniformlyOn.tendsto_at (mem_univ (-I))
  have hτlim : Tendsto (fun n => dz (τ n) 0) atTop (𝓝 1) := by
    have hc : Tendsto (fun _ : ℕ => 2 * I) atTop (𝓝 (2 * I)) := tendsto_const_nhds
    have hne : I - -I ≠ 0 := by intro hh; have := congrArg Complex.im hh; norm_num at this
    have hh := (hHdz.mul hc).div (hHI.sub hHm) hne
    have he : 1 * (2 * I) / (I - -I) = (1 : ℂ) := by
      rw [show I - -I = 2 * I by ring]
      norm_num
    rw [he] at hh
    exact hh.congr (fun n => (hτdz n).symm)
  exact grp25b_density_limit hball hF0 hW hψ hrel hτcd hτ0 hτrel hFlim hWlim hτlim

theorem grp25b_sequence {μ : ℕ → LinfStar}
    (hμ : ∀ n, μ n ∈ harmonicBeltrami) (hsmall : ∀ n, ‖μ n‖ < 1)
    (hlim : Tendsto (fun n => ‖μ n‖) atTop (𝓝 0)) :
    Tendsto (fun n => ‖dz (wA (μ n)) 0‖ ^ 2 / (1 - ‖wA (μ n) 0‖ ^ 2) ^ 2)
      atTop (𝓝 1) := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hlim.eventually_lt_const (by norm_num : (0 : ℝ) < 1 / 4))
  apply (tendsto_add_atTop_iff_nat N).mp
  exact grp25b_small_sequence (fun n => hμ (n + N))
    (fun n => hN (n + N) (Nat.le_add_left N n)) (hlim.comp (tendsto_add_atTop_nat N))

end TakhtajanTeo

#print axioms TakhtajanTeo.grp25b_small_sequence
#print axioms TakhtajanTeo.grp25b_sequence
