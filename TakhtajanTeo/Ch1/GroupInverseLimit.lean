import LiZhongQC.Ch10.S34_BersFiberSpace

/-!
# Locally uniform convergence of inverse plane homeomorphisms

The existing sequential inverse-convergence theorem is upgraded on compact
target sets. Both the maps and their limit are explicitly homeomorphisms.
This supplies only the inverse-convergence bridge in the group estimate.
-/

open Set Filter Topology Metric

namespace TakhtajanTeo

/-- Inversion preserves locally uniform convergence of plane homeomorphisms
when the limiting map is also a plane homeomorphism. -/
theorem kn6_inverse_locallyUniform
    {Fn : ℕ → (ℂ ≃ₜ ℂ)} {F : ℂ ≃ₜ ℂ}
    (hlim : TendstoLocallyUniformly (fun n => (Fn n : ℂ → ℂ))
      (F : ℂ → ℂ) atTop) :
    TendstoLocallyUniformly (fun n => ((Fn n).symm : ℂ → ℂ))
      (F.symm : ℂ → ℂ) atTop := by
  classical
  have hcompact := tendstoLocallyUniformly_iff_forall_isCompact.mp hlim
  rw [tendstoLocallyUniformly_iff_forall_isCompact]
  intro K hK
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  by_contra hbad
  rw [not_eventually] at hbad
  obtain ⟨σ, hσ, hσbad⟩ := extraction_of_frequently_atTop hbad
  have hwitness : ∀ n, ∃ y ∈ K, ε ≤ dist (F.symm y) ((Fn (σ n)).symm y) := by
    intro n
    have h := hσbad n
    push Not at h
    exact h
  choose y hy herr using hwitness
  obtain ⟨z, -, τ, hτ, hz⟩ := hK.tendsto_subseq hy
  have hmono : StrictMono (σ ∘ τ) := hσ.comp hτ
  have hsub : ∀ C : Set ℂ, IsCompact C →
      TendstoUniformlyOn (fun n => (Fn (σ (τ n)) : ℂ → ℂ))
        (F : ℂ → ℂ) atTop C := by
    intro C hC u hu
    exact hmono.tendsto_atTop.eventually (hcompact C hC u hu)
  have htarget : Tendsto (fun n => y (τ n)) atTop (𝓝 (F (F.symm z))) := by
    simpa [Function.comp_def] using hz
  have hinv := LiZhongQC.b34_b_inv_tendsto
    (F := fun n => (Fn (σ (τ n)) : ℂ → ℂ)) (f := (F : ℂ → ℂ))
    (fun n => (Fn (σ (τ n))).isOpenMap)
    (fun n => (Fn (σ (τ n))).continuous)
    (fun n => (Fn (σ (τ n))).injective) F.continuous F.injective hsub
    (w := fun n => (Fn (σ (τ n))).symm (y (τ n))) htarget
    (fun n => (Fn (σ (τ n))).apply_symm_apply (y (τ n)))
  have hdist : Tendsto
      (fun n => dist (F.symm (y (τ n))) ((Fn (σ (τ n))).symm (y (τ n))))
      atTop (𝓝 (0 : ℝ)) := by
    simpa [Function.comp_def] using ((F.symm.continuous.tendsto z).comp hz).dist hinv
  obtain ⟨n, hn⟩ := (hdist.eventually (gt_mem_nhds hε)).exists
  exact (not_lt_of_ge (herr (τ n))) hn

end TakhtajanTeo
