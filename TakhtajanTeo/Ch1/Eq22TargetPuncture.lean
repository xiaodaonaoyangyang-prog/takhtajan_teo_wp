import TakhtajanTeo.Ch1.Eq22TargetTransfer
import TakhtajanTeo.Ch1.Eq22InfinityKernel

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal NNReal ComplexConjugate Classical Real
noncomputable section
namespace TakhtajanTeo
open LiZhongQC

/-- The actual reflection inverse escapes every finite compact set at its omitted point.
The inverse H and point a are the ones supplied by the target transfer formula. -/
theorem eq22p_inverse_escape {μ : LinfStar} (hμ : μ∈LinfStarBall) {h H : ℂ → ℂ} {a : ℂ}
    (hh : IsQCReflection (fsans μ '' unitDisc) (gsans μ '' unitDiscExterior) h)
    (ha : a∈fsans μ '' unitDisc) (hinf : Tendsto h (cocompact ℂ) (𝓝 a))
    (hmap : MapsTo H ((fsans μ '' unitDisc) \ {a}) (gsans μ '' unitDiscExterior))
    (hright : ∀ v∈(fsans μ '' unitDisc) \ {a}, h (H v)=v) :
    Tendsto H (𝓝[(fsans μ '' unitDisc) \ {a}] a) (cocompact ℂ) := by
  classical
  let E := gsans μ '' unitDiscExterior
  let Ω := fsans μ '' unitDisc
  have hE : IsOpen E := (Classical.choose_spec hh.1).1
  have hΩ : IsOpen Ω := (S2C.s2c_conf_f hμ).isOpen isOpen_ball
  have hhc : ContinuousOn h E := eq22w_antiQC_continuous hh.1
  obtain ⟨b,_,hb,hnot⟩ := eq22_reflection_infty_limit hμ hh
  have hba : b=a := tendsto_nhds_unique hb hinf
  subst b
  have hfr : frontier E = frontier Ω := by
    obtain ⟨e,heΩ,heE⟩ := eq22_welding_common_chart hμ
    have hDc : unitDiscExterior = (closedBall (0 : ℂ) 1)ᶜ := by
      ext u
      simp [unitDiscExterior,mem_closedBall,not_le]
    dsimp only [E,Ω]
    rw [heE,heΩ,←e.image_frontier,←e.image_frontier,hDc,frontier_compl,
      frontier_closedBall (0 : ℂ) one_ne_zero]
    simp only [unitDisc,frontier_ball (0 : ℂ) one_ne_zero]
  have hnoE (u : ℂ) (hu : u∈frontier Ω) : u∉E := by
    have huE : u∈frontier E := hfr.symm ▸ hu
    intro huin
    exact huE.2 (hE.interior_eq.symm ▸ huin)
  let k : ℂ → ℂ := fun u => if u∈E then h u else u
  have hkc : Continuous k := by
    apply continuous_if'
    · intro u hu
      have huf : u∈frontier Ω := hfr ▸ hu
      simpa [hnoE u huf] using hh.2.2 u huf
    · intro u hu
      have huf : u∈frontier Ω := hfr ▸ hu
      rw [ite_eq_right (hnoE u huf)]
      exact tendsto_id.mono_left nhdsWithin_le_nhds
    · exact hhc
    · exact continuous_id.continuousOn
  have hnak : a∉k '' closure E := by
    rintro ⟨u,hu,he⟩
    by_cases huE : u∈E
    · apply hnot
      exact ⟨u,huE,by simpa [k,huE] using he⟩
    · have huf : u∈frontier Ω := hfr ▸ ⟨hu,fun hi => huE (interior_subset hi)⟩
      have hua : u=a := by simpa [k,huE] using he
      apply huf.2
      rw [hΩ.interior_eq]
      exact hua.symm ▸ ha
  apply Filter.hasBasis_cocompact.tendsto_right_iff.mpr
  intro K hK
  have hC : IsCompact (k '' (K ∩ closure E)) := (hK.inter_right isClosed_closure).image hkc
  have haC : a∉k '' (K ∩ closure E) := fun hc => hnak ((image_mono inter_subset_right) hc)
  have hn : (k '' (K ∩ closure E))ᶜ ∈ 𝓝 a := hC.isClosed.isOpen_compl.mem_nhds haC
  filter_upwards [nhdsWithin_le_nhds hn,self_mem_nhdsWithin] with v hv hvW
  change H v∉K
  intro hvK
  apply hv
  refine ⟨H v,⟨hvK,subset_closure (hmap hvW)⟩,?_⟩
  have hvE : H v∈E := hmap hvW
  simp only [k,ite_eq_left hvE,hright v hvW]

/-- The actual target kernel tends to zero at the same omitted point, and setting its
value there to zero gives ordinary continuity at that point. -/
theorem eq22p_kernel_zero {μ : LinfStar} (hμ : μ∈LinfStarBall) {h H q : ℂ → ℂ} {a : ℂ}
    (hh : IsQCReflection (fsans μ '' unitDisc) (gsans μ '' unitDiscExterior) h)
    (hq : DifferentiableOn ℂ q (fsans μ '' unitDisc))
    (ha : a∈fsans μ '' unitDisc) (hinf : Tendsto h (cocompact ℂ) (𝓝 a))
    (hmap : MapsTo H ((fsans μ '' unitDisc) \ {a}) (gsans μ '' unitDiscExterior))
    (hright : ∀ v∈(fsans μ '' unitDisc) \ {a}, h (H v)=v) (z : ℂ) :
    Tendsto H (𝓝[(fsans μ '' unitDisc) \ {a}] a) (cocompact ℂ) ∧
    Tendsto (eq22v_targetKernel H q z) (𝓝[(fsans μ '' unitDisc) \ {a}] a) (𝓝 0) ∧
    ContinuousAt (Function.update (eq22v_targetKernel H q z) a 0) a := by
  have hescape := eq22p_inverse_escape hμ hh ha hinf hmap hright
  have ht : Tendsto (eq22v_targetKernel H q z) (𝓝[(fsans μ '' unitDisc) \ {a}] a) (𝓝 0) := by
    have hs := (eq22_reflection_transfer_tendsto_zero hμ hh hq z).comp hescape
    apply hs.congr'
    filter_upwards [self_mem_nhdsWithin] with v hv
    simp [eq22v_targetKernel,hright v hv]
  refine ⟨hescape,ht,?_⟩
  have hΩ : IsOpen (fsans μ '' unitDisc) := (S2C.s2c_conf_f hμ).isOpen isOpen_ball
  have hfilter : 𝓝[(fsans μ '' unitDisc) \ {a}] a = 𝓝[≠] a := by
    rw [sdiff_eq,nhdsWithin_inter_of_mem (nhdsWithin_le_nhds (hΩ.mem_nhds ha))]
  apply continuousAt_update_same.mpr
  rwa [hfilter] at ht

theorem eq22p_kernel_local_bound {Ω : Set ℂ} {H q : ℂ → ℂ} {z a : ℂ}
    (ht : Tendsto (eq22v_targetKernel H q z) (𝓝[Ω \ {a}] a) (𝓝 0)) :
    ∃ r>0, ∀ v∈Ω \ {a}, ‖v-a‖<r → ‖eq22v_targetKernel H q z v‖≤1 := by
  obtain ⟨r,hr,hbound⟩ := Metric.tendsto_nhdsWithin_nhds.mp ht 1 zero_lt_one
  refine ⟨r,hr,?_⟩
  intro v hv hvr
  have hvr' : dist v a<r := by simpa only [dist_eq_norm] using hvr
  simpa only [dist_zero_right] using (hbound hv hvr').le

/-- The target transfer formula and puncture regularity with exactly the same a and H. -/
theorem eq22p_reflection_transfer {μ : LinfStar} (hμ : μ∈LinfStarBall)
    {h q : ℂ → ℂ} {z : ℂ}
    (hh : IsQCReflection (fsans μ '' unitDisc) (gsans μ '' unitDiscExterior) h)
    (hq : DifferentiableOn ℂ q (fsans μ '' unitDisc)) (hz : z∈fsans μ '' unitDisc) :
    ∃ a∈fsans μ '' unitDisc, Tendsto h (cocompact ℂ) (𝓝 a) ∧
      ∃ H : ℂ → ℂ, ContinuousOn H ((fsans μ '' unitDisc) \ {a}) ∧
        MapsTo H ((fsans μ '' unitDisc) \ {a}) (gsans μ '' unitDiscExterior) ∧
        (∀ u∈gsans μ '' unitDiscExterior, H (h u)=u) ∧
        (∀ v∈(fsans μ '' unitDisc) \ {a}, h (H v)=v) ∧
        Tendsto H (𝓝[(fsans μ '' unitDisc) \ {a}] a) (cocompact ℂ) ∧
        Tendsto (eq22v_targetKernel H q z) (𝓝[(fsans μ '' unitDisc) \ {a}] a) (𝓝 0) ∧
        ContinuousAt (Function.update (eq22v_targetKernel H q z) a 0) a ∧
        (∃ r>0, ∀ v∈(fsans μ '' unitDisc) \ {a}, ‖v-a‖<r → ‖eq22v_targetKernel H q z v‖≤1) ∧
        ∀ t : ℂ → ℂ, ContDiff ℝ 1 t → HasCompactSupport t →
          tsupport t⊆(fsans μ '' unitDisc) \ {a} →
          Integrable (fun u => (gsans μ '' unitDiscExterior).indicator (t ∘ h) u *
            (q (h u)*(u-h u)^2*dzbar h u/(u-z)^4)) ∧
          IntegrableOn (fun v => eq22v_targetKernel H q z v*dzbar t v)
            ((fsans μ '' unitDisc) \ {a}) ∧
          (∫ u, (gsans μ '' unitDiscExterior).indicator (t ∘ h) u *
            (q (h u)*(u-h u)^2*dzbar h u/(u-z)^4)) =
            (1/3 : ℂ)*(∫ v in (fsans μ '' unitDisc) \ {a}, eq22v_targetKernel H q z v*dzbar t v) := by
  obtain ⟨a,ha,hinf,H,hH,hmap,hleft,hright,htransfer⟩ := eq22v_reflection_transfer hμ hh hq hz
  obtain ⟨hescape,hzero,hcont⟩ := eq22p_kernel_zero hμ hh hq ha hinf hmap hright z
  exact ⟨a,ha,hinf,H,hH,hmap,hleft,hright,hescape,hzero,hcont,
    eq22p_kernel_local_bound hzero,htransfer⟩

end TakhtajanTeo

