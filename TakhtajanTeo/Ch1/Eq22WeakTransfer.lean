import TakhtajanTeo.Ch1.Eq22SobolevStokes
import TakhtajanTeo.Ch1.Eq22PairedPrimitive
import TakhtajanTeo.Ch1.Eq22PullbackSupport
import TakhtajanTeo.Ch1.Eq22ReflectionCutoff
import TakhtajanTeo.Ch1.Eq22Primitives

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal NNReal ComplexConjugate Classical Real
noncomputable section
namespace TakhtajanTeo
open LiZhongQC

/-- Continuous ACL functions with actual a.e. derivatives locally in L2. -/
structure eq22t_WeakL2 (f : ℂ → ℂ) (D : Set ℂ) : Prop where
  acl : IsACL f D
  diff : ∀ᵐ u ∂(volume.restrict D), DifferentiableAt ℝ f u
  lp : ∀ C⊆D, IsCompact C →
    MemLp (fun u => fderiv ℝ f u 1) 2 (volume.restrict C) ∧
    MemLp (fun u => fderiv ℝ f u I) 2 (volume.restrict C)

theorem eq22t_of_gen {D : Set ℂ} (hD : IsOpen D) {f fx fy : ℂ → ℂ}
    (hf : HasGenPartials f fx fy D 2)
    (hd : ∀ᵐ u ∂(volume.restrict D), DifferentiableAt ℝ f u) : eq22t_WeakL2 f D := by
  refine ⟨(lemma9_2_isACL_of_genPartials hD (by norm_num) hf).1,hd,?_⟩
  have he := eq22s_partials hD hf hd
  intro C hCD hC
  have hx : (fun u => fderiv ℝ f u 1) =ᵐ[volume.restrict C] fx :=
    ae_restrict_of_ae_restrict_of_subset hCD he.1
  have hy : (fun u => fderiv ℝ f u I) =ᵐ[volume.restrict C] fy :=
    ae_restrict_of_ae_restrict_of_subset hCD he.2
  exact ⟨(hf.1 C hCD hC).1.ae_eq hx.symm,(hf.1 C hCD hC).2.ae_eq hy.symm⟩

theorem eq22t_gen {D : Set ℂ} (hD : IsOpen D) {f : ℂ → ℂ} (hf : eq22t_WeakL2 f D) :
    HasGenPartials f (partialX f) (partialY f) D 2 := by
  apply lemma9_2_genPartials_of_isACL hD (by norm_num) (by norm_num) hf.acl
  intro C hCD hC
  obtain ⟨hx,hy⟩ := hf.lp C hCD hC
  constructor
  · apply hx.ae_eq
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hCD hf.diff] with u hu
    exact (partialX_eq_of_differentiableAt hu).symm
  · apply hy.ae_eq
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hCD hf.diff] with u hu
    exact (partialY_eq_of_differentiableAt hu).symm

theorem eq22t_c1 {D : Set ℂ} (hD : IsOpen D) {f : ℂ → ℂ}
    (hf : ContDiffOn ℝ 1 f D) : eq22t_WeakL2 f D := by
  have hdf : ∀ u∈D, DifferentiableAt ℝ f u := fun u hu =>
    (hf.differentiableOn one_ne_zero u hu).differentiableAt (hD.mem_nhds hu)
  have hLp : ∀ C⊆D, IsCompact C →
      MemLp (fun u => fderiv ℝ f u 1) 2 (volume.restrict C) ∧
      MemLp (fun u => fderiv ℝ f u I) 2 (volume.restrict C) := by
    intro C hCD hC
    have he (e : ℂ) : MemLp (fun u => fderiv ℝ f u e) 2 (volume.restrict C) :=
      eq22w_cont_memLp ((hf.continuousOn_fderiv_of_isOpen hD le_rfl).clm_apply continuousOn_const) hCD hC
    exact ⟨he 1,he I⟩
  have hgen : HasGenPartials f (fun u => fderiv ℝ f u 1) (fun u => fderiv ℝ f u I) D 2 := by
    refine ⟨hLp,fun _ => f,fun _ => hf,?_,?_⟩
    · have hu : TendstoUniformlyOn (fun _ : ℕ => f) f atTop D := by
        intro U hU
        filter_upwards with n u _
        exact refl_mem_uniformity hU
      exact hu.tendstoLocallyUniformlyOn
    · intro C _ _
      constructor <;> simp
  exact eq22t_of_gen hD hgen ((ae_restrict_mem hD.measurableSet).mono hdf)

theorem eq22t_memLp_mul {C : Set ℂ} (hC : IsCompact C) {f g : ℂ → ℂ}
    (hf : ContinuousOn f C) (hg : MemLp g 2 (volume.restrict C)) :
    MemLp (fun u => f u*g u) 2 (volume.restrict C) := by
  obtain ⟨M,hM⟩ := hC.exists_bound_of_continuousOn hf
  apply MemLp.of_le_mul (c := M) hg
    ((hf.aestronglyMeasurable hC.measurableSet).mul hg.aestronglyMeasurable)
  filter_upwards [ae_restrict_mem hC.measurableSet] with u hu
  change ‖f u*g u‖ ≤ M*‖g u‖
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right (hM u hu) (norm_nonneg _)

theorem eq22t_add {D : Set ℂ} {f g : ℂ → ℂ}
    (hf : eq22t_WeakL2 f D) (hg : eq22t_WeakL2 g D) : eq22t_WeakL2 (fun u => f u+g u) D := by
  refine ⟨⟨hf.acl.1.add hg.acl.1,?_⟩,?_,?_⟩
  · intro a b c d hab hcd hR
    obtain ⟨hfx,hfy⟩ := hf.acl.2 a b c d hab hcd hR
    obtain ⟨hgx,hgy⟩ := hg.acl.2 a b c d hab hcd hR
    exact ⟨hfx.and hgx |>.mono (fun _ h => h.1.add h.2),
      hfy.and hgy |>.mono (fun _ h => h.1.add h.2)⟩
  · filter_upwards [hf.diff,hg.diff] with u hu hv
    exact hu.add hv
  · intro C hCD hC
    have hd := ae_restrict_of_ae_restrict_of_subset hCD (hf.diff.and hg.diff)
    have he (e : ℂ) (hfe : MemLp (fun u => fderiv ℝ f u e) 2 (volume.restrict C))
        (hge : MemLp (fun u => fderiv ℝ g u e) 2 (volume.restrict C)) :
        MemLp (fun u => fderiv ℝ (fun u => f u+g u) u e) 2 (volume.restrict C) := by
      apply (hfe.add hge).ae_eq
      filter_upwards [hd] with u hu
      simp [fderiv_fun_add hu.1 hu.2]
    exact ⟨he 1 (hf.lp C hCD hC).1 (hg.lp C hCD hC).1,
      he I (hf.lp C hCD hC).2 (hg.lp C hCD hC).2⟩

theorem eq22t_mul {D : Set ℂ} {f g : ℂ → ℂ}
    (hf : eq22t_WeakL2 f D) (hg : eq22t_WeakL2 g D) : eq22t_WeakL2 (fun u => f u*g u) D := by
  refine ⟨⟨hf.acl.1.mul hg.acl.1,?_⟩,?_,?_⟩
  · intro a b c d hab hcd hR
    obtain ⟨hfx,hfy⟩ := hf.acl.2 a b c d hab hcd hR
    obtain ⟨hgx,hgy⟩ := hg.acl.2 a b c d hab hcd hR
    constructor
    · filter_upwards [hfx,hgx] with x hx hy
      convert hx.smul hy using 1
    · filter_upwards [hfy,hgy] with y hx hy
      convert hx.smul hy using 1
  · filter_upwards [hf.diff,hg.diff] with u hu hv
    exact hu.mul hv
  · intro C hCD hC
    have hd := ae_restrict_of_ae_restrict_of_subset hCD (hf.diff.and hg.diff)
    have he (e : ℂ) (hfe : MemLp (fun u => fderiv ℝ f u e) 2 (volume.restrict C))
        (hge : MemLp (fun u => fderiv ℝ g u e) 2 (volume.restrict C)) :
        MemLp (fun u => fderiv ℝ (fun u => f u*g u) u e) 2 (volume.restrict C) := by
      apply ((eq22t_memLp_mul hC (hf.acl.1.mono hCD) hge).add
        (eq22t_memLp_mul hC (hg.acl.1.mono hCD) hfe)).ae_eq
      filter_upwards [hd] with u hu
      simp [fderiv_fun_mul hu.1 hu.2,smul_eq_mul]
    exact ⟨he 1 (hf.lp C hCD hC).1 (hg.lp C hCD hC).1,
      he I (hf.lp C hCD hC).2 (hg.lp C hCD hC).2⟩

/-- Local representatives on compact subsets suffice; no global target extension is assumed. -/
theorem eq22t_local {D : Set ℂ} {f : ℂ → ℂ} (hc : ContinuousOn f D)
    (hd : ∀ᵐ u ∂(volume.restrict D), DifferentiableAt ℝ f u)
    (hloc : ∀ C⊆D, IsCompact C → ∃ g : ℂ → ℂ, eq22t_WeakL2 g D ∧
      ∀ u∈C, g =ᶠ[𝓝 u] f) : eq22t_WeakL2 f D := by
  refine ⟨⟨hc,?_⟩,hd,?_⟩
  · intro a b c d hab hcd hR
    obtain ⟨g,hg,he⟩ := hloc _ hR (isCompact_closedRect a b c d)
    obtain ⟨hx,hy⟩ := hg.acl.2 a b c d hab hcd hR
    constructor
    · filter_upwards [hx,ae_restrict_mem measurableSet_Ioo] with x hx hxI
      apply hx.congr
      intro y hyI
      rw [uIcc_of_le hcd.le] at hyI
      exact (he _ (mem_closedRect_of_mem_Icc (Ioo_subset_Icc_self hxI) hyI)).self_of_nhds
    · filter_upwards [hy,ae_restrict_mem measurableSet_Ioo] with y hy hyI
      apply hy.congr
      intro x hxI
      rw [uIcc_of_le hab.le] at hxI
      exact (he _ (mem_closedRect_of_mem_Icc hxI (Ioo_subset_Icc_self hyI))).self_of_nhds
  · intro C hCD hC
    obtain ⟨g,hg,he⟩ := hloc C hCD hC
    have hEq (e : ℂ) : (fun u => fderiv ℝ g u e) =ᵐ[volume.restrict C]
        (fun u => fderiv ℝ f u e) := by
      filter_upwards [ae_restrict_mem hC.measurableSet] with u hu
      rw [(he u hu).fderiv_eq]
    exact ⟨(hg.lp C hCD hC).1.ae_eq (hEq 1),(hg.lp C hCD hC).2.ae_eq (hEq I)⟩

theorem eq22t_holo_comp {D Ω : Set ℂ} (hD : IsOpen D) (hΩ : IsOpen Ω)
    {h Q : ℂ → ℂ} (hh : IsQuasiconformal (fun u => conj (h u)) D)
    (hm : MapsTo h D Ω) (hQ : DifferentiableOn ℂ Q Ω) : eq22t_WeakL2 (fun u => Q (h u)) D := by
  have hhc := eq22w_antiQC_continuous hh
  apply eq22t_local (hQ.continuousOn.comp hhc hm)
  · filter_upwards [eq22w_antiQC_diff hh,ae_restrict_mem hD.measurableSet] with u hu huD
    exact (((hQ _ (hm huD)).differentiableAt (hΩ.mem_nhds (hm huD))).restrictScalars ℝ).comp u hu
  · intro C hCD hC
    have hK := hC.image_of_continuousOn (hhc.mono hCD)
    obtain ⟨ψ,hψ,hψc,hψQ⟩ := eq22w_target_extension hΩ hK
      (image_subset_iff.mpr (fun u hu => hm (hCD hu))) ((hQ.contDiffOn hΩ).restrict_scalars ℝ)
    obtain ⟨Fx,Fy,hgen,hdψ⟩ := eq22w_antiQC_comp hh hψ hψc
    refine ⟨fun u => ψ (h u),eq22t_of_gen hD hgen hdψ,?_⟩
    intro u hu
    exact (hψQ (h u) (mem_image_of_mem _ hu)).comp_tendsto
      ((hhc u (hCD hu)).continuousAt (hD.mem_nhds (hCD hu)))

/-- The concrete paired primitive has actual local L2 weak derivatives. -/
theorem eq22t_paired_regular {D Ω : Set ℂ} (hD : IsOpen D) (hΩ : IsOpen Ω)
    {h q Q1 Q2 Q3 : ℂ → ℂ} {z : ℂ}
    (hh : IsQuasiconformal (fun u => conj (h u)) D) (hm : MapsTo h D Ω)
    (h1 : ∀ v∈Ω, HasDerivAt Q1 (q v) v)
    (h2 : ∀ v∈Ω, HasDerivAt Q2 (Q1 v) v)
    (h3 : ∀ v∈Ω, HasDerivAt Q3 (Q2 v) v) (hz : z∉D) :
    eq22t_WeakL2 (fun u => eq22PairedPrimitive Q1 Q2 Q3 z u (h u)) D := by
  have hc (c : ℂ) : eq22t_WeakL2 (fun _ => c) D := eq22t_c1 hD contDiffOn_const
  have hid : eq22t_WeakL2 (fun u : ℂ => u) D := eq22t_c1 hD contDiffOn_id
  have hhr : eq22t_WeakL2 h D :=
    eq22t_holo_comp (h := h) (Q := fun v : ℂ => v) hD hΩ hh hm differentiableOn_id
  have hd : eq22t_WeakL2 (fun u => u-h u) D := by
    simpa only [neg_one_mul,sub_eq_add_neg] using eq22t_add hid (eq22t_mul (hc (-1)) hhr)
  have hd2 : eq22t_WeakL2 (fun u => (u-h u)^2) D := by
    simpa only [pow_two] using eq22t_mul hd hd
  have hQ1 := eq22t_holo_comp hD hΩ hh hm
    (fun v hv => (h1 v hv).differentiableAt.differentiableWithinAt)
  have hQ2 := eq22t_holo_comp hD hΩ hh hm
    (fun v hv => (h2 v hv).differentiableAt.differentiableWithinAt)
  have hQ3 := eq22t_holo_comp hD hΩ hh hm
    (fun v hv => (h3 v hv).differentiableAt.differentiableWithinAt)
  have hk (n : ℕ) : eq22t_WeakL2 (fun u => ((u-z)^n)⁻¹) D := by
    have hholo : DifferentiableOn ℂ (fun u => ((u-z)^n)⁻¹) D := by
      intro u hu
      exact (((differentiableAt_id.sub_const z).pow n).inv
        (pow_ne_zero n (sub_ne_zero.mpr (fun he => hz (he ▸ hu))))).differentiableWithinAt
    exact eq22t_c1 hD ((hholo.contDiffOn hD).restrict_scalars ℝ)
  have hN := eq22t_add (eq22t_add (eq22t_mul hQ1 hd2) (eq22t_mul (hc 2) (eq22t_mul hQ2 hd)))
    (eq22t_mul (hc 2) hQ3)
  have hL := eq22t_add (eq22t_mul hQ1 hd) hQ2
  have hT := eq22t_add (eq22t_add (eq22t_mul hN (hk 3)) (eq22t_mul hL (hk 2)))
    (eq22t_mul hQ1 (hk 1))
  convert hT using 1
  funext u
  simp only [eq22PairedPrimitive,div_eq_mul_inv,pow_one]
  ring

def eq22t_kernel (h q : ℂ → ℂ) (z u : ℂ) : ℂ :=
  q (h u)*(1/(u-z)+(u-h u)/(u-z)^2+(u-h u)^2/(u-z)^3)

/-- The real directional derivative is supplied by the verified paired-primitive algebra. -/
theorem eq22t_paired_fderiv {h q Q1 Q2 Q3 : ℂ → ℂ} {u z : ℂ}
    (hh : DifferentiableAt ℝ h u)
    (hT : DifferentiableAt ℝ (fun u => eq22PairedPrimitive Q1 Q2 Q3 z u (h u)) u)
    (h1 : HasDerivAt Q1 (q (h u)) (h u)) (h2 : HasDerivAt Q2 (Q1 (h u)) (h u))
    (h3 : HasDerivAt Q3 (Q2 (h u)) (h u)) (huz : u≠z) (e : ℂ) :
    fderiv ℝ (fun u => eq22PairedPrimitive Q1 Q2 Q3 z u (h u)) u e =
      -3*eq22Primitive h Q1 Q2 Q3 z u*e+eq22t_kernel h q z u*fderiv ℝ h u e := by
  have hline : HasDerivAt (fun s : ℝ => u+(s : ℂ)*e) e 0 := by
    simpa using (Complex.ofRealCLM.hasDerivAt.mul_const e).const_add u
  have hv : HasDerivAt (fun s : ℝ => h (u+(s : ℂ)*e)) (fderiv ℝ h u e) 0 := by
    simpa [Function.comp_def] using hh.hasFDerivAt.comp_hasDerivAt_of_eq 0 hline (by simp)
  have ht : HasDerivAt (fun s : ℝ => eq22PairedPrimitive Q1 Q2 Q3 z
      (u+(s : ℂ)*e) (h (u+(s : ℂ)*e)))
      (fderiv ℝ (fun u => eq22PairedPrimitive Q1 Q2 Q3 z u (h u)) u e) 0 := by
    simpa [Function.comp_def] using hT.hasFDerivAt.comp_hasDerivAt_of_eq 0 hline (by simp)
  have hp := eq22_paired_hasDerivAt hline hv (by simpa using h1)
    (by simpa using h2) (by simpa using h3) (by simpa using sub_ne_zero.mpr huz)
  simpa only [Complex.ofReal_zero,zero_mul,add_zero,eq22Primitive,eq22t_kernel,mul_assoc] using ht.unique hp

theorem eq22t_paired_wirtinger {h q Q1 Q2 Q3 : ℂ → ℂ} {u z : ℂ}
    (hh : DifferentiableAt ℝ h u)
    (hT : DifferentiableAt ℝ (fun u => eq22PairedPrimitive Q1 Q2 Q3 z u (h u)) u)
    (h1 : HasDerivAt Q1 (q (h u)) (h u)) (h2 : HasDerivAt Q2 (Q1 (h u)) (h u))
    (h3 : HasDerivAt Q3 (Q2 (h u)) (h u)) (huz : u≠z) :
    dz (fun u => eq22PairedPrimitive Q1 Q2 Q3 z u (h u)) u =
      -3*eq22Primitive h Q1 Q2 Q3 z u+eq22t_kernel h q z u*dz h u ∧
    dzbar (fun u => eq22PairedPrimitive Q1 Q2 Q3 z u (h u)) u =
      eq22t_kernel h q z u*dzbar h u := by
  have hx := eq22t_paired_fderiv hh hT h1 h2 h3 huz 1
  have hy := eq22t_paired_fderiv hh hT h1 h2 h3 huz I
  constructor
  · simp only [dz,hx,hy]
    linear_combination (3*eq22Primitive h Q1 Q2 Q3 z u/2)*Complex.I_sq
  · simp only [dzbar,hx,hy]
    linear_combination (-3*eq22Primitive h Q1 Q2 Q3 z u/2)*Complex.I_sq

theorem eq22t_gen_congr {D : Set ℂ} {f fx fy gx gy : ℂ → ℂ}
    (hf : HasGenPartials f fx fy D 2)
    (hx : fx =ᵐ[volume.restrict D] gx) (hy : fy =ᵐ[volume.restrict D] gy) :
    HasGenPartials f gx gy D 2 := by
  obtain ⟨hLp,fn,hfn,hconv,hlim⟩ := hf
  refine ⟨?_,fn,hfn,hconv,?_⟩
  · intro C hCD hC
    exact ⟨(hLp C hCD hC).1.ae_eq (ae_restrict_of_ae_restrict_of_subset hCD hx),
      (hLp C hCD hC).2.ae_eq (ae_restrict_of_ae_restrict_of_subset hCD hy)⟩
  · intro C hCD hC
    have he (a b : ℂ → ℂ) (e : ℂ) (hab : a =ᵐ[volume.restrict D] b) (n : ℕ) :
        eLpNorm (fun u => fderiv ℝ (fn n) u e-a u) 2 (volume.restrict C) =
        eLpNorm (fun u => fderiv ℝ (fn n) u e-b u) 2 (volume.restrict C) := by
      apply eLpNorm_congr_ae
      filter_upwards [ae_restrict_of_ae_restrict_of_subset hCD hab] with u hu
      rw [hu]
    exact ⟨(hlim C hCD hC).1.congr (he fx gx 1 hx), (hlim C hCD hC).2.congr (he fy gy I hy)⟩

/-- Explicit weak derivatives of the actual paired primitive, using the actual h-partials. -/
theorem eq22t_paired_hasGen {D Ω : Set ℂ} (hD : IsOpen D) (hΩ : IsOpen Ω)
    {h q Q1 Q2 Q3 : ℂ → ℂ} {z : ℂ}
    (hh : IsQuasiconformal (fun u => conj (h u)) D) (hm : MapsTo h D Ω)
    (h1 : ∀ v∈Ω, HasDerivAt Q1 (q v) v)
    (h2 : ∀ v∈Ω, HasDerivAt Q2 (Q1 v) v)
    (h3 : ∀ v∈Ω, HasDerivAt Q3 (Q2 v) v) (hz : z∉D) :
    HasGenPartials (fun u => eq22PairedPrimitive Q1 Q2 Q3 z u (h u))
      (fun u => -3*eq22Primitive h Q1 Q2 Q3 z u+eq22t_kernel h q z u*partialX h u)
      (fun u => -3*eq22Primitive h Q1 Q2 Q3 z u*I+eq22t_kernel h q z u*partialY h u) D 2 := by
  have hreg := eq22t_paired_regular hD hΩ hh hm h1 h2 h3 hz
  apply eq22t_gen_congr (eq22t_gen hD hreg)
  · filter_upwards [hreg.diff,eq22w_antiQC_diff hh,ae_restrict_mem hD.measurableSet] with u hu hhu huD
    rw [partialX_eq_of_differentiableAt hu,partialX_eq_of_differentiableAt hhu]
    simpa only [mul_one] using eq22t_paired_fderiv hhu hu (h1 _ (hm huD))
      (h2 _ (hm huD)) (h3 _ (hm huD)) (fun he => hz (he ▸ huD)) 1
  · filter_upwards [hreg.diff,eq22w_antiQC_diff hh,ae_restrict_mem hD.measurableSet] with u hu hhu huD
    rw [partialY_eq_of_differentiableAt hu,partialY_eq_of_differentiableAt hhu]
    exact eq22t_paired_fderiv hhu hu (h1 _ (hm huD)) (h2 _ (hm huD))
      (h3 _ (hm huD)) (fun he => hz (he ▸ huD)) I

/-- The zero-extended pullback has actual weak derivatives on the source open set. -/
theorem eq22t_pullback_regular {D : Set ℂ} (hD : IsOpen D) {h t : ℂ → ℂ}
    (hh : IsQuasiconformal (fun u => conj (h u)) D)
    (ht : ContDiff ℝ 1 t) (htc : HasCompactSupport t) :
    eq22t_WeakL2 (D.indicator (t ∘ h)) D := by
  obtain ⟨Fx,Fy,hgen,hd⟩ := eq22w_antiQC_comp hh ht htc
  have hreg := eq22t_of_gen hD hgen hd
  have he (u : ℂ) (hu : u∈D) : (fun u => t (h u)) =ᶠ[𝓝 u] D.indicator (t ∘ h) := by
    filter_upwards [hD.mem_nhds hu] with v hv
    exact (indicator_of_mem hv (t ∘ h)).symm
  apply eq22t_local ((ht.continuous.comp_continuousOn (eq22w_antiQC_continuous hh)).congr
    (fun u hu => indicator_of_mem hu _))
  · filter_upwards [hd,ae_restrict_mem hD.measurableSet] with u hu huD
    exact (he u huD).differentiableAt_iff.mp hu
  · intro C hCD _
    exact ⟨fun u => t (h u),hreg,fun u hu => he u (hCD hu)⟩

theorem eq22t_chain_jacobian {h t χ : ℂ → ℂ} {u : ℂ}
    (hh : DifferentiableAt ℝ h u) (ht : DifferentiableAt ℝ t (h u))
    (hχ : χ =ᶠ[𝓝 u] fun v => t (h v)) :
    dz h u*dzbar χ u-dzbar h u*dz χ u = (jacobian h u : ℂ)*dzbar t (h u) := by
  have hder : fderiv ℝ χ u = (fderiv ℝ t (h u)).comp (fderiv ℝ h u) :=
    hχ.fderiv_eq.trans (fderiv_fun_comp u ht hh)
  have hJ := sp_chain_algebra (ψ := t) (fx := fun v => fderiv ℝ h v 1)
    (fy := fun v => fderiv ℝ h v I) hh rfl rfl
  simp only [sp_beta,genDz,genDzbar,dz,dzbar,hder,ContinuousLinearMap.comp_apply] at hJ ⊢
  linear_combination -hJ

/-- Actual weak transfer on the source domain, prior to anti-QC area change of variables. -/
theorem eq22t_transfer {D Ω : Set ℂ} (hD : IsOpen D) (hΩ : IsOpen Ω)
    {h q Q1 Q2 Q3 t : ℂ → ℂ} {z : ℂ}
    (hh : IsQuasiconformal (fun u => conj (h u)) D) (hm : MapsTo h D Ω)
    (h1 : ∀ v∈Ω, HasDerivAt Q1 (q v) v)
    (h2 : ∀ v∈Ω, HasDerivAt Q2 (Q1 v) v)
    (h3 : ∀ v∈Ω, HasDerivAt Q3 (Q2 v) v) (hz : z∉D)
    (ht : ContDiff ℝ 1 t) (htc : HasCompactSupport t)
    (hc : HasCompactSupport (D.indicator (t ∘ h))) (hs : tsupport (D.indicator (t ∘ h))⊆D) :
    Integrable (fun u => D.indicator (t ∘ h) u *
      (q (h u)*(u-h u)^2*dzbar h u/(u-z)^4)) ∧
    IntegrableOn (fun u => eq22t_kernel h q z u*dzbar t (h u)*(jacobian h u : ℂ)) D ∧
      (∫ u, D.indicator (t ∘ h) u*(q (h u)*(u-h u)^2*dzbar h u/(u-z)^4)) =
        -(1/3 : ℂ)*(∫ u in D, eq22t_kernel h q z u*dzbar t (h u)*(jacobian h u : ℂ)) := by
  let χ := D.indicator (t ∘ h)
  let T := fun u => eq22PairedPrimitive Q1 Q2 Q3 z u (h u)
  let P := eq22Primitive h Q1 Q2 Q3 z
  let G := fun u => eq22t_kernel h q z u*dzbar t (h u)*(jacobian h u : ℂ)
  have hregT := eq22t_paired_regular hD hΩ hh hm h1 h2 h3 hz
  have hregχ := eq22t_pullback_regular hD hh ht htc
  have hS := eq22s_reflected_stokes hD hΩ hh hm h1 h2 h3 hz
    (eq22t_gen hD hregχ) hregχ.diff hc hs
  have hE := eq22s_exact_form_zero hD (eq22t_gen hD hregχ) (eq22t_gen hD hregT)
    hregχ.diff hregT.diff hc hs
  have hP : IntegrableOn (fun u => P u*dzbar χ u) D := hS.2.1.integrableOn
  have hEq : (fun u => (dz T u*dzbar χ u-dzbar T u*dz χ u)+3*(P u*dzbar χ u))
      =ᵐ[volume.restrict D] G := by
    filter_upwards [hregT.diff,eq22w_antiQC_diff hh,ae_restrict_mem hD.measurableSet] with u hu hhu huD
    have huz : u≠z := fun he => hz (he ▸ huD)
    obtain ⟨hdz,hdbar⟩ := eq22t_paired_wirtinger hhu hu (h1 _ (hm huD))
      (h2 _ (hm huD)) (h3 _ (hm huD)) huz
    have hχg : χ =ᶠ[𝓝 u] fun v => t (h v) := by
      filter_upwards [hD.mem_nhds huD] with v hv
      exact indicator_of_mem hv _
    have hJ := eq22t_chain_jacobian hhu (ht.differentiable one_ne_zero _) hχg
    change (dz (fun u => eq22PairedPrimitive Q1 Q2 Q3 z u (h u)) u*dzbar χ u-
      dzbar (fun u => eq22PairedPrimitive Q1 Q2 Q3 z u (h u)) u*dz χ u)+3*(P u*dzbar χ u)=G u
    rw [hdz,hdbar]
    change (-3*P u+eq22t_kernel h q z u*dz h u)*dzbar χ u-
      (eq22t_kernel h q z u*dzbar h u)*dz χ u+3*(P u*dzbar χ u)=G u
    calc _ = eq22t_kernel h q z u*(dz h u*dzbar χ u-dzbar h u*dz χ u) := by ring
      _ = G u := by rw [hJ]; dsimp only [G]; ring
  have hGi : IntegrableOn G D := (hE.1.add (hP.const_mul 3)).congr hEq
  have hInt : (∫ u in D, G u) = 3*(∫ u in D, P u*dzbar χ u) := by
    rw [← integral_congr_ae hEq,integral_add hE.1 (hP.const_mul 3),integral_const_mul,hE.2,zero_add]
  have hPD : (∫ u in D, P u*dzbar χ u) = ∫ u, P u*dzbar χ u := by
    apply sp_setIntegral_eq_integral hD.measurableSet hs
    intro u hu
    change u∉tsupport χ at hu
    simp [dzbar,sp_fderiv_eq_zero_of_notMem_tsupport hu]
  refine ⟨hS.1,hGi,?_⟩
  rw [hS.2.2]
  change -(∫ u, P u*dzbar χ u) = -(1/3 : ℂ)*(∫ u in D, G u)
  rw [hInt,hPD]
  ring

/-- The genuine reflection supplies all support conditions for the zero-extended pullback.
Only the final area change of variables and removal of the target cutoff remain downstream. -/
theorem eq22t_reflection_transfer_of_primitives {μ : LinfStar} (hμ : μ∈LinfStarBall)
    {h q Q1 Q2 Q3 : ℂ → ℂ} {z : ℂ}
    (hh : IsQCReflection (fsans μ '' unitDisc) (gsans μ '' unitDiscExterior) h)
    (h1 : ∀ v∈fsans μ '' unitDisc, HasDerivAt Q1 (q v) v)
    (h2 : ∀ v∈fsans μ '' unitDisc, HasDerivAt Q2 (Q1 v) v)
    (h3 : ∀ v∈fsans μ '' unitDisc, HasDerivAt Q3 (Q2 v) v)
    (hz : z∈fsans μ '' unitDisc) :
    ∃ a∈fsans μ '' unitDisc, Tendsto h (cocompact ℂ) (𝓝 a) ∧
      ∀ t : ℂ → ℂ, ContDiff ℝ 1 t → HasCompactSupport t →
        tsupport t⊆(fsans μ '' unitDisc) \ {a} →
        Integrable (fun u => (gsans μ '' unitDiscExterior).indicator (t ∘ h) u *
          (q (h u)*(u-h u)^2*dzbar h u/(u-z)^4)) ∧
        IntegrableOn (fun u => eq22t_kernel h q z u*dzbar t (h u)*(jacobian h u : ℂ))
          (gsans μ '' unitDiscExterior) ∧
        (∫ u, (gsans μ '' unitDiscExterior).indicator (t ∘ h) u *
          (q (h u)*(u-h u)^2*dzbar h u/(u-z)^4)) =
          -(1/3 : ℂ)*(∫ u in gsans μ '' unitDiscExterior,
            eq22t_kernel h q z u*dzbar t (h u)*(jacobian h u : ℂ)) := by
  have hD : IsOpen (gsans μ '' unitDiscExterior) := (Classical.choose_spec hh.1).1
  have hΩ : IsOpen (fsans μ '' unitDisc) := (S2C.s2c_conf_f hμ).isOpen isOpen_ball
  have hzD : z∉gsans μ '' unitDiscExterior := by
    intro hzE
    obtain ⟨e,heΩ,heE⟩ := eq22_welding_common_chart hμ
    rw [heΩ] at hz
    rw [heE] at hzE
    obtain ⟨x,hx,hxz⟩ := hz
    obtain ⟨y,hy,hyz⟩ := hzE
    have hxy : x=y := e.injective (hxz.trans hyz.symm)
    have hxnorm : ‖x‖<1 := mem_ball_zero_iff.mp hx
    have hynorm : 1<‖y‖ := hy
    rw [←hxy] at hynorm
    exact lt_asymm hxnorm hynorm
  obtain ⟨a,ha,hinf,hcut⟩ := eq22_reflection_cutoff hμ hh
  refine ⟨a,ha,hinf,?_⟩
  intro t ht htc hts
  obtain ⟨hc,hs,_⟩ := hcut t ht.continuous htc hts
  exact eq22t_transfer hD hΩ hh.1 hh.2.1 h1 h2 h3 hzD ht htc hc hs

/-- Compact weak transfer for the original reflection and any holomorphic q. The three
primitives, weak derivatives, and zero-extended pullback support are all constructed. -/
theorem eq22t_reflection_transfer {μ : LinfStar} (hμ : μ∈LinfStarBall)
    {h q : ℂ → ℂ} {z : ℂ}
    (hh : IsQCReflection (fsans μ '' unitDisc) (gsans μ '' unitDiscExterior) h)
    (hq : DifferentiableOn ℂ q (fsans μ '' unitDisc)) (hz : z∈fsans μ '' unitDisc) :
    ∃ a∈fsans μ '' unitDisc, Tendsto h (cocompact ℂ) (𝓝 a) ∧
      ∀ t : ℂ → ℂ, ContDiff ℝ 1 t → HasCompactSupport t →
        tsupport t⊆(fsans μ '' unitDisc) \ {a} →
        Integrable (fun u => (gsans μ '' unitDiscExterior).indicator (t ∘ h) u *
          (q (h u)*(u-h u)^2*dzbar h u/(u-z)^4)) ∧
        IntegrableOn (fun u => eq22t_kernel h q z u*dzbar t (h u)*(jacobian h u : ℂ))
          (gsans μ '' unitDiscExterior) ∧
        (∫ u, (gsans μ '' unitDiscExterior).indicator (t ∘ h) u *
          (q (h u)*(u-h u)^2*dzbar h u/(u-z)^4)) =
          -(1/3 : ℂ)*(∫ u in gsans μ '' unitDiscExterior,
            eq22t_kernel h q z u*dzbar t (h u)*(jacobian h u : ℂ)) := by
  obtain ⟨Q1,Q2,Q3,hQ1,hQ2,hQ3,hd1,hd2,hd3⟩ := eq22_triple_primitives hμ hq
  have hΩ : IsOpen (fsans μ '' unitDisc) := (S2C.s2c_conf_f hμ).isOpen isOpen_ball
  apply eq22t_reflection_transfer_of_primitives hμ hh (Q1 := Q1) (Q2 := Q2) (Q3 := Q3) ?_ ?_ ?_ hz
  · intro v hv
    rw [←hd1 hv]
    exact ((hQ1 v hv).differentiableAt (hΩ.mem_nhds hv)).hasDerivAt
  · intro v hv
    rw [←hd2 hv]
    exact ((hQ2 v hv).differentiableAt (hΩ.mem_nhds hv)).hasDerivAt
  · intro v hv
    rw [←hd3 hv]
    exact ((hQ3 v hv).differentiableAt (hΩ.mem_nhds hv)).hasDerivAt

end TakhtajanTeo

