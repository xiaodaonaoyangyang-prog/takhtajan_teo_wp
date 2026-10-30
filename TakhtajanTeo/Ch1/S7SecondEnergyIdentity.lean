import TakhtajanTeo.Ch1.S7SecondEnergyLimit

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal NNReal ComplexConjugate Classical Real
noncomputable section
namespace TakhtajanTeo
open LiZhongQC

theorem s7ei_pair_disk {f g : ℂ → ℂ} (hs : tsupport f ⊆ unitDisc) :
    (∫ z, f z*conj (g z)*(rho z : ℂ)) =
      ∫ z in unitDisc, f z*conj (g z)*(rho z : ℂ) := by
  symm
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro z hz
  rw [image_eq_zero_of_notMem_tsupport (fun ht => hz (hs ht))]
  simp

private theorem split_pair {f g : ℂ → ℂ}
    (hI : Integrable (fun z => f z*conj (f z)*(rho z : ℂ)) (volume.restrict unitDisc))
    (hJ : Integrable (fun z => f z*conj (g z)*(rho z : ℂ)) (volume.restrict unitDisc)) :
    (∫ z in unitDisc, f z*conj (f z+(1/2:ℂ)*g z)*(rho z : ℂ)) =
      (∫ z in unitDisc, f z*conj (f z)*(rho z : ℂ))+
      (1/2:ℂ)*(∫ z in unitDisc, f z*conj (g z)*(rho z : ℂ)) := by
  calc
    _ = ∫ z in unitDisc, (f z*conj (f z)*(rho z : ℂ)+
        (1/2:ℂ)*(f z*conj (g z)*(rho z : ℂ))) := by
      apply integral_congr_ae
      filter_upwards with z
      simp only [map_add, map_mul, map_div₀, map_one, map_ofNat]
      ring
    _ = _ := by rw [integral_add hI (hJ.const_mul _), integral_const_mul]

/-- The actual second-energy identity on the full disk, obtained by passing
the explicit compact approximants through the proved weighted pairings. -/
theorem s7ei_second_energy {h : ℂ → ℂ}
    (hh : ContDiffOn ℝ (⊤ : ℕ∞) h unitDisc)
    (hL : normL2 unitDisc h < ∞) (hDL : normL2 unitDisc (laplace0 h) < ∞) :
    normL2 unitDisc (s7et_q h) < ∞ ∧
    (∫ z in unitDisc, s7et_q h z*conj (s7et_q h z)*(rho z : ℂ)) =
      (∫ z in unitDisc, laplace0 h z*conj (laplace0 h z)*(rho z : ℂ))+
      (1/2:ℂ)*(∫ z in unitDisc, laplace0 h z*conj (h z)*(rho z : ℂ)) := by
  obtain ⟨hk,hkh,hkl⟩ := s7ga_graph_approximation hh hL hDL
  obtain ⟨hQn,hqc⟩ := s7el_q_convergence hh hL hDL
  let k : ℕ → ℂ → ℂ := fun n z => (s7dc_cutoff n z : ℂ)*h z
  have hkm (n : ℕ) : AEStronglyMeasurable (k n) (volume.restrict unitDisc) :=
    (hk n).1.continuous.aestronglyMeasurable
  have hlm (n : ℕ) : AEStronglyMeasurable (laplace0 (k n)) (volume.restrict unitDisc) :=
    (s7el_laplace_measurable _).aestronglyMeasurable
  have hqm (n : ℕ) : AEStronglyMeasurable (s7et_q (k n)) (volume.restrict unitDisc) :=
    (s7el_q_measurable _).aestronglyMeasurable
  have hkn (n : ℕ) : normL2 unitDisc (k n) < ∞ :=
    s7gn_compact_normL2_finite (hk n).1 (hk n).2.1 (hk n).2.2
  have hln (n : ℕ) : normL2 unitDisc (laplace0 (k n)) < ∞ :=
    s7gn_compact_normL2_finite (s7gb_laplace_smooth (hk n).1)
      ((hk n).2.1.of_isClosed_subset (isClosed_tsupport _) (s7gb_laplace_support _))
      ((s7gb_laplace_support _).trans (hk n).2.2)
  have hqn (n : ℕ) : normL2 unitDisc (s7et_q (k n)) < ∞ :=
    (s7gn_graph_norm_bound (hk n).1 (hk n).2.1 (hk n).2.2).1
  have hm : AEStronglyMeasurable h (volume.restrict unitDisc) :=
    hh.continuousOn.aestronglyMeasurable measurableSet_ball
  have hDm : AEStronglyMeasurable (laplace0 h) (volume.restrict unitDisc) :=
    (s7el_laplace_measurable _).aestronglyMeasurable
  have hQm : AEStronglyMeasurable (s7et_q h) (volume.restrict unitDisc) :=
    (s7el_q_measurable _).aestronglyMeasurable
  have htQ := s7pc_pairing_tendsto hqm hqm hQm hQm hqn hqn hQn hQn hqc hqc
  have htD := s7pc_pairing_tendsto hlm hlm hDm hDm hln hln hDL hDL hkl hkl
  have htDH := s7pc_pairing_tendsto hlm hkm hDm hm hln hkn hDL hL hkl hkh
  have htR := htD.add (tendsto_const_nhds.mul htDH (a := (1/2:ℂ)))
  have he : (fun n => ∫ z in unitDisc, s7et_q (k n) z*conj (s7et_q (k n) z)*(rho z : ℂ)) =
      (fun n => (∫ z in unitDisc, laplace0 (k n) z*conj (laplace0 (k n) z)*(rho z : ℂ))+
        (1/2:ℂ)*(∫ z in unitDisc, laplace0 (k n) z*conj (k n z)*(rho z : ℂ))) := by
    funext n
    have hid := (s7gb_reduced_energy (hk n).1 (hk n).2.1 (hk n).2.2).2.2
    rw [s7ei_pair_disk ((s7gb_q_support _).trans (hk n).2.2),
      s7ei_pair_disk ((s7gb_laplace_support _).trans (hk n).2.2)] at hid
    exact hid.trans (split_pair
      (s7pc_pairing_integrable (hlm n) (hlm n) (hln n) (hln n))
      (s7pc_pairing_integrable (hlm n) (hkm n) (hln n) (hkn n)))
  rw [he] at htQ
  exact ⟨hQn,tendsto_nhds_unique htQ htR⟩

end TakhtajanTeo
