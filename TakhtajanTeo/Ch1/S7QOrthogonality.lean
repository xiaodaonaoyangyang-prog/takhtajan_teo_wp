import TakhtajanTeo.Ch1.S7SecondEnergyIdentity
import TakhtajanTeo.Ch1.S7ResolventEnergy

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal NNReal ComplexConjugate Classical Real
noncomputable section
namespace TakhtajanTeo
open LiZhongQC

/-- Actual compact Stokes against a holomorphic quadratic differential. -/
theorem s7qo_compact_holomorphic {h φ : ℂ → ℂ}
    (hh : ContDiff ℝ (⊤ : ℕ∞) h) (hc : HasCompactSupport h)
    (hs : tsupport h ⊆ unitDisc) (hφ : DifferentiableOn ℂ φ unitDisc) :
    (∫ z in unitDisc, s7et_q h z*φ z) = 0 := by
  let v : ℂ → ℂ := fun z => (rho z : ℂ)⁻¹*dzbar h z
  have hv : ContDiff ℝ (⊤ : ℕ∞) v :=
    (wp_rho_inv_contDiff.of_le le_top).mul (s7ca_dzbar_smooth hh)
  have hvs : tsupport v ⊆ tsupport h :=
    tsupport_mul_subset_right.trans (s7ca_dzbar_support h)
  have hvc : HasCompactSupport v := hc.of_isClosed_subset (isClosed_tsupport _) hvs
  have hφs : ContDiffOn ℝ 1 φ unitDisc :=
    (hφ.contDiffOn isOpen_ball).restrict_scalars ℝ
  obtain ⟨_,_,he⟩ := s7cg_stokes isOpen_ball hφs (hv.of_le (by simp)) hvc (hvs.trans hs)
  have hz : (fun z => v z*dzbar φ z) = (fun _ => (0:ℂ)) := by
    funext z
    by_cases hz : z ∈ unitDisc
    · rw [e124_dzbar_holo ((hφ z hz).differentiableAt (isOpen_ball.mem_nhds hz)),mul_zero]
    · rw [image_eq_zero_of_notMem_tsupport (fun ht => hz (hs (hvs ht))),zero_mul]
  rw [hz,integral_zero] at he
  have hzero : (∫ z, φ z*s7et_q h z) = 0 := neg_eq_zero.mp he.symm
  calc
    _ = ∫ z, s7et_q h z*φ z := by
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro z hz
      rw [image_eq_zero_of_notMem_tsupport (fun ht => hz (hs (s7gb_q_support h ht))),zero_mul]
    _ = 0 := by simpa only [mul_comm] using hzero

/-- Cancellation of the actual harmonic density, only at genuine disk points. -/
theorem s7qo_harmonic_pair {ψ φ : ℂ → ℂ}
    (hrep : ∀ z ∈ unitDisc, ψ z=(rho z:ℂ)⁻¹*conj (φ z))
    (f : ℂ → ℂ) {z : ℂ} (hz : z ∈ unitDisc) :
    f z*conj (ψ z)*(rho z:ℂ)=f z*φ z := by
  have hn : ‖z‖ ≠ 1 := ne_of_lt (mem_ball_zero_iff.mp hz)
  have hr : (rho z:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (rho_pos_of_norm_ne_one hn).ne'
  rw [hrep z hz]
  simp only [map_mul,map_inv₀,conj_conj,Complex.conj_ofReal]
  field_simp

theorem s7qo_compact_pair {h ψ : ℂ → ℂ}
    (hh : ContDiff ℝ (⊤ : ℕ∞) h) (hc : HasCompactSupport h)
    (hs : tsupport h ⊆ unitDisc) (hψ : ψ ∈ harmonicL2 unitDisc) :
    (∫ z in unitDisc, s7et_q h z*conj (ψ z)*(rho z:ℂ)) = 0 := by
  obtain ⟨φ,hφ,hrep,_⟩ := hψ
  rw [show (∫ z in unitDisc, s7et_q h z*conj (ψ z)*(rho z:ℂ)) =
    ∫ z in unitDisc, s7et_q h z*φ z from
      setIntegral_congr_fun measurableSet_ball (fun z hz => s7qo_harmonic_pair hrep _ hz)]
  exact s7qo_compact_holomorphic hh hc hs hφ

theorem s7qo_harmonic_measurable {ψ : ℂ → ℂ} (hψ : ψ ∈ harmonicL2 unitDisc) :
    AEStronglyMeasurable ψ (volume.restrict unitDisc) := by
  obtain ⟨φ,hφ,hrep,_⟩ := hψ
  have hφs : ContDiffOn ℝ (⊤ : ℕ∞) φ unitDisc :=
    (hφ.contDiffOn isOpen_ball).restrict_scalars ℝ
  have hs : ContDiffOn ℝ (⊤ : ℕ∞) (fun z => (rho z:ℂ)⁻¹*conj (φ z)) unitDisc :=
    (wp_rho_inv_contDiff.of_le le_top).contDiffOn.mul
      (Complex.conjCLE.contDiff.comp_contDiffOn hφs)
  apply (hs.continuousOn.aestronglyMeasurable measurableSet_ball).congr
  filter_upwards [ae_restrict_mem measurableSet_ball] with z hz
  exact (hrep z hz).symm

/-- Genuine orthogonality on the full disk, by the actual second-differential
L2 limit. No boundary integral is silently discarded. -/
theorem s7qo_disk {h ψ : ℂ → ℂ}
    (hh : ContDiffOn ℝ (⊤ : ℕ∞) h unitDisc)
    (hL : normL2 unitDisc h < ∞) (hDL : normL2 unitDisc (laplace0 h) < ∞)
    (hψ : ψ ∈ harmonicL2 unitDisc) :
    (∫ z in unitDisc, s7et_q h z*conj (ψ z)*(rho z:ℂ)) = 0 := by
  have hk := s7ap_compact_test hh
  obtain ⟨hQ,hqc⟩ := s7el_q_convergence hh hL hDL
  have hm := s7qo_harmonic_measurable hψ
  have hψn := hψ.choose_spec.2.2
  have hc : Tendsto (fun _ : ℕ => normL2 unitDisc (fun z => ψ z-ψ z)) atTop (𝓝 0) := by
    simpa [normL2] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0:ℝ≥0∞)) atTop (𝓝 0))
  have ht := s7pc_pairing_tendsto
    (fun n => (s7el_q_measurable (fun z => (s7dc_cutoff n z:ℂ)*h z)).aestronglyMeasurable)
    (fun _ => hm) (s7el_q_measurable h).aestronglyMeasurable hm
    (fun n => (s7gn_graph_norm_bound (hk n).1 (hk n).2.1 (hk n).2.2).1)
    (fun _ => hψn) hQ hψn hqc hc
  have he (n : ℕ) := s7qo_compact_pair (hk n).1 (hk n).2.1 (hk n).2.2 hψ
  simp only [he] at ht
  exact (tendsto_nhds_unique ht tendsto_const_nhds)

/-- The actual Lambda disk representative is harmonic, with a genuinely
holomorphic reflected quadratic differential, once its weighted norm is finite. -/
theorem s7qo_diskRep_harmonic (φ : AInf unitDisc)
    (hn : normL2 unitDisc (s7et_diskRep φ) < ∞) :
    s7et_diskRep φ ∈ harmonicL2 unitDisc := by
  refine ⟨fun z => -2*conj (AInf.toFun φ (conj z)), ?_, ?_, hn⟩
  · intro z hz
    have hc : conj z ∈ unitDisc := by simpa [unitDisc,mem_ball_zero_iff] using hz
    have hd := (φ.2.differentiableAt (isOpen_ball.mem_nhds hc)).conj_conj
    have hdd : DifferentiableAt ℂ (fun w => conj (AInf.toFun φ (conj w))) z := by
      simpa only [Function.comp_def,conj_conj,AInf.toFun] using hd
    exact (hdd.const_mul (-2)).differentiableWithinAt
  · intro z hz
    simp only [s7et_diskRep,map_mul,map_neg,map_ofNat,conj_conj]
    ring

/-- An arbitrary exterior harmonic L2 representative has a genuine disk
harmonic L2 pullback, with the actual unit phase and no regularity at zero assumed. -/
theorem s7qo_harmonic_transport {ν : ℂ → ℂ} (hν : ν ∈ harmonicL2 unitDiscExterior) :
    ∃ ψ : ℂ → ℂ, ψ ∈ harmonicL2 unitDisc ∧
      ν =ᵐ[volume.restrict unitDiscExterior] (fun z => (z/conj z)^2*ψ z⁻¹) := by
  obtain ⟨φ,hφ⟩ := Lambda_surjective_harmonic ((harmonicL2_subset_harmonic.choose_spec ν hν).1)
  have he : ν =ᵐ[volume.restrict unitDiscExterior]
      (fun z => (z/conj z)^2*s7et_diskRep φ z⁻¹) := by
    filter_upwards [s7et_lambda_phase φ,wp_harmonic_toLinf_ae hν] with z hz hv
    rw [hφ,hv] at hz
    simpa only [div_pow,mul_comm] using hz
  refine ⟨s7et_diskRep φ,s7qo_diskRep_harmonic φ ?_,he⟩
  rw [← s7et_normL2_phase_inv,← grp_normL2_congr_ae he]
  exact hν.choose_spec.2.2

/-- Orthogonality transported through the actual inversion phase. -/
theorem s7qo_exterior_phase {h ν : ℂ → ℂ}
    (hh : ContDiffOn ℝ (⊤ : ℕ∞) h unitDisc)
    (hL : normL2 unitDisc h < ∞) (hDL : normL2 unitDisc (laplace0 h) < ∞)
    (hν : ν ∈ harmonicL2 unitDiscExterior) :
    l2Inner (fun z => (z/conj z)^2*(-2*s7et_q h z⁻¹)) ν = 0 := by
  obtain ⟨ψ,hψ,he⟩ := s7qo_harmonic_transport hν
  have hi : l2Inner (fun z => (z/conj z)^2*(-2*s7et_q h z⁻¹)) ν =
      ∫ z in unitDisc, (-2*s7et_q h z)*conj (ψ z)*(rho z:ℂ) := by
    rw [← s7et_pairing_phase_inv]
    apply integral_congr_ae
    filter_upwards [he] with z hz
    rw [hz]
  rw [hi]
  calc
    _ = (-2:ℂ)*(∫ z in unitDisc, s7et_q h z*conj (ψ z)*(rho z:ℂ)) := by
      simp only [mul_assoc,integral_const_mul]
    _ = 0 := by rw [s7qo_disk hh hL hDL hψ,mul_zero]

/-- The actual exterior Qdot is orthogonal to every harmonic L2 differential.
This is the orthogonality clause of Theorem 7.4, not its differentiability clause. -/
theorem s7qo_Qdot {μ ν : ℂ → ℂ} (hμ : μ ∈ harmonicL2 unitDiscExterior)
    (hν : ν ∈ harmonicL2 unitDiscExterior) {κ : LinfStar} (hκ : κ ∈ harmonicBeltrami) :
    l2Inner (Qdot (toLinf μ) κ) ν = 0 := by
  obtain ⟨F,hF,hFn,_,hH,hHn,hpot⟩ := s7et_forcing_potential_bridge hμ hκ
  have hd := s7re_resolvent_laplace_finite hF hFn
  have he : Qdot (toLinf μ) κ =ᵐ[volume.restrict unitDiscExterior]
      (fun z => (z/conj z)^2*(-2*s7et_q (resolventOp unitDisc F) z⁻¹)) := by
    filter_upwards [ae_restrict_mem resolvent_exterior_isOpen.measurableSet] with z hz
    exact s7et_Qdot_of_potential hμ hκ hH.1 hpot hz
  calc
    _ = l2Inner (fun z => (z/conj z)^2*(-2*s7et_q (resolventOp unitDisc F) z⁻¹)) ν := by
      apply integral_congr_ae
      filter_upwards [he] with z hz
      rw [hz]
    _ = 0 := s7qo_exterior_phase hH.1 hHn hd hν

end TakhtajanTeo
