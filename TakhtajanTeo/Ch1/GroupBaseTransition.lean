import TakhtajanTeo.Ch1.GroupOrigin
import TakhtajanTeo.Ch1.GroupHolomorphicCenter

/-! A common analytic disk for normalized Stoilow transition charts. -/
open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal NNReal ComplexConjugate Classical Real
noncomputable section
namespace TakhtajanTeo
open LiZhongQC

theorem grp25b_transition_analytic (F W : ℂ ≃ₜ ℂ) (hF0 : F 0 = 0) (hW0 : W 0 = 0)
    {ψ : ℂ → ℂ}
    (hψ : IsConformalOnto ψ (F '' unitDiscExterior) (W '' unitDiscExterior))
    (hrel : ∀ z ∈ unitDiscExterior, W z = ψ (F z))
    (hbound : ∀ z : ℂ, ‖z‖ ≤ 1 → ‖F z‖ < 2) :
    DifferentiableOn ℂ (fun t : ℂ => (W (F.symm t⁻¹))⁻¹) (ball 0 (1 / 3)) := by
  have hFi0 : F.symm 0 = 0 := by
    apply F.injective
    rw [F.apply_symm_apply, hF0]
  obtain ⟨η, hηa, hη0, -, hηrel⟩ := grp25z_transition_chart F W hψ hrel
  have hηeq : (fun t : ℂ => (W (F.symm t⁻¹))⁻¹) = η := by
    funext t
    by_cases ht : t = 0
    · subst t
      simp [hFi0, hW0, hη0]
    · exact (hηrel t ht).symm
  have hE : IsOpen unitDiscExterior := isOpen_lt continuous_const continuous_norm
  have hU : IsOpen (F '' unitDiscExterior) := F.isOpenMap _ hE
  intro t ht
  by_cases ht0 : t = 0
  · subst t
    rw [hηeq]
    exact hηa.differentiableAt.differentiableWithinAt
  have hInv : 2 < ‖t⁻¹‖ := by
    have htN : ‖t‖ < 1 / 3 := mem_ball_zero_iff.mp ht
    rw [norm_inv, inv_eq_one_div, lt_div_iff₀ (norm_pos_iff.mpr ht0)]
    linarith
  have hx : F.symm t⁻¹ ∈ unitDiscExterior := by
    change 1 < ‖F.symm t⁻¹‖
    by_contra hh
    have hB := hbound (F.symm t⁻¹) (le_of_not_gt hh)
    rw [F.apply_symm_apply] at hB
    linarith
  have hψd := hψ.1.differentiableAt (hU.mem_nhds
    (show t⁻¹ ∈ F '' unitDiscExterior from ⟨F.symm t⁻¹, hx, F.apply_symm_apply _⟩))
  have hψne : ψ t⁻¹ ≠ 0 := by
    have hh := hrel (F.symm t⁻¹) hx
    rw [F.apply_symm_apply] at hh
    rw [← hh]
    intro h0
    have hx0 : F.symm t⁻¹ = 0 := W.injective (h0.trans hW0.symm)
    have hinv0 := congrArg F hx0
    rw [F.apply_symm_apply, hF0] at hinv0
    exact ht0 (inv_eq_zero.mp hinv0)
  have hEv : ∀ᶠ u in 𝓝 t, F.symm u⁻¹ ∈ unitDiscExterior :=
    ((F.symm.continuous.continuousAt).comp (continuousAt_inv₀ ht0)).preimage_mem_nhds (hE.mem_nhds hx)
  have he : (fun u : ℂ => (W (F.symm u⁻¹))⁻¹) =ᶠ[𝓝 t] fun u => (ψ u⁻¹)⁻¹ := by
    filter_upwards [hEv] with u hu
    rw [hrel _ hu, F.apply_symm_apply]
  exact (((hψd.comp t (differentiableAt_inv ht0)).inv hψne).congr_of_eventuallyEq he).differentiableWithinAt

theorem grp25b_eventually_disc_bound {F : ℕ → ℂ → ℂ}
    (hlim : TendstoLocallyUniformly F id atTop) :
    ∀ᶠ n in atTop, ∀ z : ℂ, ‖z‖ ≤ 1 → ‖F n z‖ < 2 := by
  have hu := tendstoLocallyUniformly_iff_forall_isCompact.mp hlim
    (closedBall (0 : ℂ) 1) (isCompact_closedBall _ _)
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp hu 1 zero_lt_one] with n hn
  intro z hz
  have hd := hn z (mem_closedBall_zero_iff.mpr hz)
  have ht := norm_le_norm_sub_add (F n z) z
  rw [dist_eq_norm] at hd
  dsimp only [id_eq] at hd
  rw [norm_sub_rev] at hd
  linarith

/-- The two reciprocal charts identify the normalized solution's origin jet
by reflection. No nonvanishing derivative premise is needed for this identity. -/
theorem grp25b_transition_dz {μ : LinfStar} (F W : ℂ ≃ₜ ℂ)
    (hF0 : F 0 = 0) (hW : IsNormalizedSolution (W : ℂ → ℂ) (extA μ))
    {τ : ℂ → ℂ} (hτcd : ContDiffAt ℝ 1 τ 0) (hτ0 : τ 0 = 0)
    (hτrel : ∀ᶠ t in 𝓝[≠] (0 : ℂ), τ t = (F t⁻¹)⁻¹)
    (hξa : AnalyticAt ℂ (fun t : ℂ => (W (F.symm t⁻¹))⁻¹) 0) :
    ContDiffAt ℝ 1 (W : ℂ → ℂ) 0 ∧ dz (W : ℂ → ℂ) 0 =
      conj (deriv (fun t : ℂ => (W (F.symm t⁻¹))⁻¹) 0 * dz τ 0) := by
  let ξ : ℂ → ℂ := fun t => (W (F.symm t⁻¹))⁻¹
  have hFi0 : F.symm 0 = 0 := by
    apply F.injective
    rw [F.apply_symm_apply, hF0]
  have hξ0 : ξ 0 = 0 := by simp [ξ, hFi0, hW.2.2.1]
  have hξat : DifferentiableAt ℂ ξ (τ 0) := by rw [hτ0]; exact hξa.differentiableAt
  have hξcd : ContDiffAt ℝ 1 ξ (τ 0) := by rw [hτ0]; exact hξa.contDiffAt.restrict_scalars ℝ
  have hcomp : ContDiffAt ℝ 1 (fun t => ξ (τ t)) 0 := hξcd.comp 0 hτcd
  have hcompdz : dz (fun t => ξ (τ t)) 0 = deriv ξ 0 * dz τ 0 := by
    rw [(grp_dz_comp_holo (hτcd.differentiableAt one_ne_zero) hξat).2, hτ0]
  let Q : ℂ → ℂ := fun z => conj (ξ (τ (conj z)))
  obtain ⟨hQcd, hQdz⟩ := grp25z_conj_chart hcomp
  have hQ0 : Q 0 = 0 := by simp [Q, hτ0, hξ0]
  have hconjT : Tendsto (conj : ℂ → ℂ) (𝓝[≠] 0) (𝓝[≠] 0) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · simpa only [map_zero] using (Complex.continuous_conj.tendsto (0 : ℂ)).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with z hz
      simpa using hz
  have hev : (W : ℂ → ℂ) =ᶠ[𝓝[≠] 0] Q := by
    filter_upwards [hconjT.eventually hτrel] with z hzτ
    change W z = conj (ξ (τ (conj z)))
    dsimp only [ξ]
    rw [hzτ, inv_inv, F.symm_apply_apply]
    have href := normalized_solution_refl_comm hW z
    change W (conj z)⁻¹ = (conj (W z))⁻¹ at href
    rw [href, inv_inv, Complex.conj_conj]
  have hev0 : (W : ℂ → ℂ) =ᶠ[𝓝 0] Q := by
    filter_upwards [eventually_nhdsWithin_iff.mp hev] with z hz
    by_cases hz0 : z = 0
    · subst z
      rw [hW.2.2.1, hQ0]
    · exact hz hz0
  refine ⟨hQcd.congr_of_eventuallyEq hev0, ?_⟩
  rw [(t203_c1_dz_congr hev0).1]
  exact hQdz.trans (congrArg conj hcompdz)

end TakhtajanTeo

#print axioms TakhtajanTeo.grp25b_transition_analytic
#print axioms TakhtajanTeo.grp25b_eventually_disc_bound
#print axioms TakhtajanTeo.grp25b_transition_dz
