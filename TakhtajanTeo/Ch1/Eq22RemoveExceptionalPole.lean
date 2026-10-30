import TakhtajanTeo.Ch1.Eq22KernelContinuity

open Complex Set MeasureTheory Metric Filter Topology
namespace TakhtajanTeo

theorem eq22_remove_exceptional_pole {Ω E : Set ℂ} {F q : ℂ → ℂ} {a c : ℂ}
    (hΩ : IsOpen Ω) (hE : MeasurableSet E) (hdisj : Disjoint Ω E)
    (hq : ContinuousOn q Ω)
    (hI : ∀ z ∈ Ω, IntegrableOn (fun u => F u/(u-z)^4) E)
    (he : ∀ z ∈ Ω, z ≠ a → q z = c*(∫ u in E, F u/(u-z)^4)) :
    EqOn q (fun z => c*(∫ u in E, F u/(u-z)^4)) Ω := by
  intro z hz
  by_cases hza : z = a
  · subst z
    obtain ⟨r,hr,hball⟩ := Metric.isOpen_iff.mp hΩ a hz
    have hsep : ∀ u ∈ E, r ≤ ‖u-a‖ := by
      intro u hu
      by_contra hn
      have hub : u ∈ ball a r := by
        simpa only [mem_ball, dist_eq_norm] using lt_of_not_ge hn
      exact disjoint_left.mp hdisj (hball hub) hu
    have hInt := (eq22_kernel_integral_continuousAt hE hr hsep (hI a hz)).const_mul c
    have hQ : Tendsto q (𝓝[≠] a) (𝓝 (q a)) :=
      (hq.continuousAt (hΩ.mem_nhds hz)).tendsto.mono_left nhdsWithin_le_nhds
    have hJ : Tendsto (fun z => c*(∫ u in E, F u/(u-z)^4)) (𝓝[≠] a)
        (𝓝 (c*(∫ u in E, F u/(u-a)^4))) :=
      hInt.tendsto.mono_left nhdsWithin_le_nhds
    have hEq : q =ᶠ[𝓝[≠] a] (fun z => c*(∫ u in E, F u/(u-z)^4)) := by
      filter_upwards [nhdsWithin_le_nhds (hΩ.mem_nhds hz),self_mem_nhdsWithin] with z hzΩ hzne
      exact he z hzΩ hzne
    exact tendsto_nhds_unique (hQ.congr' hEq) hJ
  · exact he z hz hza

end TakhtajanTeo
