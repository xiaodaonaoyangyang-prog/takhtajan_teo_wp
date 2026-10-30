import TakhtajanTeo.Ch1.S7EnergyData
import TakhtajanTeo.Ch1.GroupChain1

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal NNReal ComplexConjugate Classical Real
noncomputable section
namespace TakhtajanTeo
open LiZhongQC

/-- A smooth harmonic representative retains the actual essential supremum bound. -/
theorem s7er_bounded_rep {ν : LinfStar} (hν : ν ∈ harmonicBeltrami) :
    ∃ g : ℂ → ℂ, g ∈ BCinf unitDiscExterior ∧
      (∀ᵐ z ∂(volume.restrict unitDiscExterior), ν z = g z) ∧
      ∀ z ∈ unitDiscExterior, ‖g z‖ ≤ ‖ν‖ := by
  obtain ⟨g, hgs, hae⟩ := wr_harm_rep hν
  have hb : ∀ᵐ z ∂(volume.restrict unitDiscExterior), ‖g z‖ ≤ ‖ν‖ := by
    filter_upwards [hae, LinfStar_ae_norm_le ν] with z hz hn
    rwa [← hz]
  have he : (fun z => max ‖g z‖ ‖ν‖) =ᵐ[volume.restrict unitDiscExterior]
      (fun _ => ‖ν‖) := hb.mono fun _ hz => max_eq_right hz
  have hpt := Measure.eqOn_open_of_ae_eq he resolvent_exterior_isOpen
    (continuous_max.comp_continuousOn
      (hgs.continuousOn.norm.prodMk continuousOn_const)) continuousOn_const
  have hbound : ∀ z ∈ unitDiscExterior, ‖g z‖ ≤ ‖ν‖ := by
    intro z hz
    exact max_eq_right_iff.mp (hpt hz)
  exact ⟨g, ⟨hgs, ‖ν‖, hbound⟩, hae, hbound⟩

/-- The genuine forcing term of Proposition 7.2 has a smooth bounded L2
representative. No regularity or energy assumption is added to the inputs. -/
theorem s7er_forcing_smooth {μ : ℂ → ℂ} (hμ : μ ∈ harmonicL2 unitDiscExterior)
    {ν : LinfStar} (hν : ν ∈ harmonicBeltrami) :
    ∃ f : ℂ → ℂ, f ∈ BCinf unitDiscExterior ∧
      normL2 unitDiscExterior f < ∞ ∧
      (fun z => μ z * conj (ν z)) =ᵐ[volume.restrict unitDiscExterior] f := by
  have hm : toLinf μ ∈ harmonicBeltrami :=
    (harmonicL2_subset_harmonic.choose_spec μ hμ).1
  obtain ⟨a, ha, hea, hba⟩ := s7er_bounded_rep hm
  obtain ⟨b, hb, heb, hbb⟩ := s7er_bounded_rep hν
  let f : ℂ → ℂ := fun z => a z * conj (b z)
  have hfs : ContDiffOn ℝ (⊤ : ℕ∞) f unitDiscExterior :=
    ha.1.mul (Complex.conjCLE.toContinuousLinearMap.contDiff.comp_contDiffOn hb.1)
  have hfb : ∀ z ∈ unitDiscExterior, ‖f z‖ ≤ ‖toLinf μ‖ * ‖ν‖ := by
    intro z hz
    simp only [f, norm_mul, Complex.norm_conj]
    exact mul_le_mul (hba z hz) (hbb z hz) (norm_nonneg _) (norm_nonneg _)
  have he : (fun z => μ z * conj (ν z)) =ᵐ[volume.restrict unitDiscExterior] f := by
    filter_upwards [hea, heb, wp_harmonic_toLinf_ae hμ] with z hz₁ hz₂ hz₃
    change μ z * conj (ν z) = a z * conj (b z)
    rw [← hz₁, ← hz₂, hz₃]
  refine ⟨f, ⟨hfs, _, hfb⟩, ?_, he⟩
  rw [← grp_normL2_congr_ae he]
  exact s7ed_forcing_finite hμ ν

/-- The actual resolvent potential is smooth, bounded and solves its elliptic
PDE; its second antiholomorphic differential is the actual Q variation.
The global integration-by-parts energy identity remains a separate step. -/
theorem s7er_resolvent_data {μ : ℂ → ℂ} (hμ : μ ∈ harmonicL2 unitDiscExterior)
    {ν : LinfStar} (hν : ν ∈ harmonicBeltrami) :
    ∃ f : ℂ → ℂ, f ∈ BCinf unitDiscExterior ∧ normL2 unitDiscExterior f < ∞ ∧
      (fun z => μ z * conj (ν z)) =ᵐ[volume.restrict unitDiscExterior] f ∧
      resolventStar f ∈ BCinf unitDiscExterior ∧
      (∀ z ∈ unitDiscExterior,
        2 * (laplace0 (resolventStar f) z + (1 / 2) * resolventStar f z) = f z) ∧
      (∀ z ∈ unitDiscExterior, Qdot (toLinf μ) ν z =
        -2 * dzbar (fun y => (rho y : ℂ)⁻¹ * dzbar (resolventStar f) y) z) := by
  obtain ⟨f, hf, hn, he⟩ := s7er_forcing_smooth hμ hν
  have hpot : resolventStar (fun z => μ z * conj (ν z)) = resolventStar f := by
    funext z
    apply integral_congr_ae
    filter_upwards [he] with w hw
    simp only [hw]
  obtain ⟨_, hsm, hpde⟩ := (RK3 (Or.inr rfl)).1 f hf
  refine ⟨f, hf, hn, he, hsm, hpde, ?_⟩
  intro z hz
  rw [s7ed_Qdot_raw hμ hν hz, hpot]

end TakhtajanTeo
