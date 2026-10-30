import TakhtajanTeo.Ch1.Eq22WeakStokes

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal NNReal ComplexConjugate Classical Real
noncomputable section
namespace TakhtajanTeo
open LiZhongQC

/-- Actual directional derivatives of a weakly differentiable function, locally in L2. -/
theorem eq22s_partials {D : Set ℂ} (hD : IsOpen D) {f fx fy : ℂ → ℂ}
    (hf : HasGenPartials f fx fy D 2)
    (hd : ∀ᵐ u ∂(volume.restrict D), DifferentiableAt ℝ f u) :
    (fun u => fderiv ℝ f u 1) =ᵐ[volume.restrict D] fx ∧
      (fun u => fderiv ℝ f u I) =ᵐ[volume.restrict D] fy := by
  obtain ⟨_,hx,hy⟩ := lemma9_2_isACL_of_genPartials hD (by norm_num) hf
  constructor
  · filter_upwards [hx,hd] with u hu hdu
    rwa [partialX_eq_of_differentiableAt hdu] at hu
  · filter_upwards [hy,hd] with u hu hdu
    rwa [partialY_eq_of_differentiableAt hdu] at hu

theorem eq22s_mollifier {D : Set ℂ} (hD : IsOpen D) {f fx fy : ℂ → ℂ}
    (hf : HasGenPartials f fx fy D 2) {L : Set ℂ} (hL : IsCompact L) (hLD : L⊆D) :
    Tendsto (fun n => eLpNorm (fun u => fderiv ℝ (lemma92Approx D f n) u 1-fx u)
      2 (volume.restrict L)) atTop (𝓝 0) ∧
    Tendsto (fun n => eLpNorm (fun u => fderiv ℝ (lemma92Approx D f n) u I-fy u)
      2 (volume.restrict L)) atTop (𝓝 0) := by
  obtain ⟨hacl,hx,hy⟩ := lemma9_2_isACL_of_genPartials hD (by norm_num) hf
  have hloc : ∀ C⊆D, IsCompact C → MemLp (partialX f) 2 (volume.restrict C) ∧
      MemLp (partialY f) 2 (volume.restrict C) := by
    intro C hCD hC
    have hxC : partialX f =ᵐ[volume.restrict C] fx := ae_restrict_of_ae_restrict_of_subset hCD hx
    have hyC : partialY f =ᵐ[volume.restrict C] fy := ae_restrict_of_ae_restrict_of_subset hCD hy
    exact ⟨(hf.1 C hCD hC).1.ae_eq hxC.symm, (hf.1 C hCD hC).2.ae_eq hyC.symm⟩
  obtain ⟨hxlim,hylim⟩ := sp_m_tendsto hD hacl hloc hLD hL
  constructor
  · apply hxlim.congr
    intro n
    apply eLpNorm_congr_ae
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hLD hx] with u hu
    rw [hu]
  · apply hylim.congr
    intro n
    apply eLpNorm_congr_ae
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hLD hy] with u hu
    rw [hu]

theorem eq22s_cutoff {K D : Set ℂ} (hK : IsCompact K) (hD : IsOpen D) (hKD : K⊆D) :
    ∃ a : ℂ → ℂ, ContDiff ℝ 2 a ∧ HasCompactSupport a ∧ tsupport a⊆D ∧
      (∀ u∈K, a =ᶠ[𝓝 u] fun _ => 1) ∧ K⊆tsupport a := by
  obtain ⟨b,hb,hb1,hbs,hbc,_⟩ := sp_e_exists_cutoff hK hD hKD
  let a : ℂ → ℂ := fun u => (b u : ℂ)
  have he : tsupport a = tsupport b := by
    change closure (Function.support a) = closure (Function.support b)
    congr 1
    ext u
    simp [a,Function.mem_support]
  have hg : ∀ u∈K, a =ᶠ[𝓝 u] fun _ => 1 := by
    intro u hu
    filter_upwards [eventually_nhdsSet_iff_forall.mp hb1 u hu] with v hv
    simp [a,hv]
  refine ⟨a,Complex.ofRealCLM.contDiff.comp hb,?_,?_,hg,?_⟩
  · change IsCompact (tsupport a)
    rw [he]
    exact hbc.isCompact
  · exact he.symm ▸ hbs
  · intro u hu
    apply subset_closure
    simp only [Function.mem_support, (hg u hu).self_of_nhds, ne_eq, one_ne_zero, not_false_eq_true]

/-- Exact-form zero integral with a compact Sobolev first factor. This is the limit of
the C2 compact-test bracket, and includes actual integrability. -/
theorem eq22s_beta_zero {D : Set ℂ} (hD : IsOpen D) {χ χx χy T Tx Ty : ℂ → ℂ}
    (hχ : HasGenPartials χ χx χy D 2) (hT : HasGenPartials T Tx Ty D 2)
    (hdχ : ∀ᵐ u ∂(volume.restrict D), DifferentiableAt ℝ χ u)
    (hcχ : HasCompactSupport χ) (hsχ : tsupport χ⊆D) :
    IntegrableOn (sp_beta χx χy Tx Ty) D ∧ (∫ u in D, sp_beta χx χy Tx Ty u)=0 := by
  obtain ⟨a,ha,hac,has,hag,hKa⟩ := eq22s_cutoff hcχ.isCompact hD hsχ
  let L := tsupport a
  have hL : IsCompact L := hac.isCompact
  have hLD : L⊆D := has
  have hm : MeasurableSet L := hL.measurableSet
  have hcc : ContinuousOn χ D :=
    (lemma9_2_isACL_of_genPartials hD (by norm_num) hχ).1.1
  let fn := lemma92Approx D χ
  have hfn : ∀ n, ContDiff ℝ 2 (fn n) := fun n => sp_m_contDiff2 hcc n
  have hunif : TendstoUniformlyOn fn χ atTop L :=
    (tendstoLocallyUniformlyOn_iff_forall_isCompact hD).mp
      (tendstoLocallyUniformlyOn_lemma92Approx hD hcc) L hLD hL
  obtain ⟨hxlim,hylim⟩ := eq22s_mollifier hD hχ hL hLD
  obtain ⟨hχx,hχy⟩ := hχ.1 L hLD hL
  obtain ⟨hTx,hTy⟩ := hT.1 L hLD hL
  have hdn (n : ℕ) (e : ℂ) : MemLp (fun u => fderiv ℝ (fn n) u e) 2 (volume.restrict L) :=
    sp_f2_memLp_of_continuousOn hL (sp_f2_continuous_fderiv (hfn n) e).continuousOn
  have hda (e : ℂ) : MemLp (fun u => fderiv ℝ a u e) 2 (volume.restrict L) :=
    sp_f2_memLp_of_continuousOn hL (sp_f2_continuous_fderiv ha e).continuousOn
  let B := sp_beta (fun u => fderiv ℝ a u 1) (fun u => fderiv ℝ a u I) Tx Ty
  have hB : IntegrableOn B L := by
    simpa only [one_mul] using sp_f2_integrableOn_mul_beta hL
      (a := fun _ => (1 : ℂ)) continuousOn_const (hda 1) (hda I) hTx hTy
  have hBn (n : ℕ) : IntegrableOn (fun u => fn n u*B u) L :=
    sp_f2_integrableOn_mul_beta hL (hfn n).continuous.continuousOn (hda 1) (hda I) hTx hTy
  have hBχ : IntegrableOn (fun u => χ u*B u) L :=
    sp_f2_integrableOn_mul_beta hL (hcc.mono hLD) (hda 1) (hda I) hTx hTy
  have hAn (n : ℕ) : IntegrableOn (fun u => a u*sp_beta
      (fun u => fderiv ℝ (fn n) u 1) (fun u => fderiv ℝ (fn n) u I) Tx Ty u) L :=
    sp_f2_integrableOn_mul_beta hL ha.continuous.continuousOn (hdn n 1) (hdn n I) hTx hTy
  have hz (n : ℕ) : (∫ u in L, fn n u*B u) + (∫ u in L, a u*sp_beta
      (fun u => fderiv ℝ (fn n) u 1) (fun u => fderiv ℝ (fn n) u I) Tx Ty u)=0 := by
    have hc : HasCompactSupport (fun u => a u*fn n u) := hac.mul_right
    have hs : tsupport (fun u => a u*fn n u) ⊆ L := tsupport_mul_subset_left
    have hzero := sp_integral_beta_eq_zero hD hT (ha.mul (hfn n)) hc (hs.trans hLD)
    have hrestrict : (∫ u in D, sp_beta
        (fun w => fderiv ℝ (fun t => a t*fn n t) w 1)
        (fun w => fderiv ℝ (fun t => a t*fn n t) w I) Tx Ty u) =
        ∫ u in L, sp_beta (fun w => fderiv ℝ (fun t => a t*fn n t) w 1)
          (fun w => fderiv ℝ (fun t => a t*fn n t) w I) Tx Ty u := by
      apply sp_f2_setIntegral_subset hD.measurableSet hLD
      intro u _ hu
      apply sp_f2_beta_eq_zero_of_fst
      · exact sp_fderiv_eq_zero_of_notMem_tsupport (fun hh => hu (hs hh)) 1
      · exact sp_fderiv_eq_zero_of_notMem_tsupport (fun hh => hu (hs hh)) I
    rw [hrestrict] at hzero
    rw [← integral_add (hBn n) (hAn n)]
    convert hzero using 1
    apply setIntegral_congr_fun hm
    intro u _
    exact (sp_beta_mul (ha.differentiable (by norm_num) u)
      ((hfn n).differentiable (by norm_num) u)).symm
  have hlimB := sp_tendsto_integral_mul_of_uniform hB hBn hBχ hunif
  have hlimA := sp_e_beta_tendsto hTx hTy hχx hχy (fun n => hdn n 1) (fun n => hdn n I)
    (hac.exists_bound_of_continuous ha.continuous) ha.continuous.aestronglyMeasurable hxlim hylim
  have hsum : (∫ u in L, χ u*B u) + (∫ u in L, a u*sp_beta χx χy Tx Ty u)=0 :=
    tendsto_nhds_unique (hlimB.add hlimA) (by simpa only [hz] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℂ)) atTop (𝓝 0)))
  have hχB : ∀ u, χ u*B u=0 := by
    intro u
    by_cases hu : u∈tsupport χ
    · have hx : fderiv ℝ a u 1=0 := by rw [(hag u hu).fderiv_eq]; simp
      have hy : fderiv ℝ a u I=0 := by rw [(hag u hu).fderiv_eq]; simp
      simp [B,sp_beta_eq,hx,hy]
    · simp [image_eq_zero_of_notMem_tsupport hu]
  have hder := eq22s_partials hD hχ hdχ
  have hzero : ∀ᵐ u ∂(volume.restrict D), u∉tsupport χ → sp_beta χx χy Tx Ty u=0 := by
    filter_upwards [hder.1,hder.2] with u hu hv hnot
    apply sp_f2_beta_eq_zero_of_fst
    · rw [← hu]; exact sp_fderiv_eq_zero_of_notMem_tsupport hnot 1
    · rw [← hv]; exact sp_fderiv_eq_zero_of_notMem_tsupport hnot I
  have haB : (fun u => a u*sp_beta χx χy Tx Ty u) =ᵐ[volume.restrict D] sp_beta χx χy Tx Ty := by
    filter_upwards [hzero] with u hu
    by_cases hK : u∈tsupport χ
    · rw [(hag u hK).self_of_nhds,one_mul]
    · rw [hu hK,mul_zero]
  have hBI : IntegrableOn (sp_beta χx χy Tx Ty) L := by
    simpa only [one_mul] using sp_f2_integrableOn_mul_beta hL
      (a := fun _ => (1 : ℂ)) continuousOn_const hχx hχy hTx hTy
  have hB0 : ∀ᵐ u ∂(volume.restrict D), u∉L → sp_beta χx χy Tx Ty u=0 :=
    hzero.mono (fun u hu hnot => hu (fun hh => hnot (hKa hh)))
  have hBD : IntegrableOn (sp_beta χx χy Tx Ty) D := by
    have hglob : Integrable (L.indicator (sp_beta χx χy Tx Ty)) :=
      (integrable_indicator_iff hm).mpr hBI
    apply hglob.integrableOn.congr
    filter_upwards [hB0] with u hu
    by_cases huL : u∈L
    · rw [indicator_of_mem huL]
    · rw [indicator_of_notMem huL, hu huL]
  refine ⟨hBD,?_⟩
  have he : (∫ u in D, sp_beta χx χy Tx Ty u) = ∫ u in L, sp_beta χx χy Tx Ty u :=
    setIntegral_eq_of_subset_of_ae_sdiff_eq_zero hD.measurableSet.nullMeasurableSet hLD ?_
  · rw [he, ← integral_congr_ae (ae_restrict_of_ae_restrict_of_subset hLD haB)]
    simpa only [hχB, integral_zero,zero_add] using hsum
  · exact (ae_restrict_iff' hD.measurableSet).mp hB0 |>.mono (fun u hu hmem => hu hmem.1 hmem.2)

/-- The actual Wirtinger version of the weak exact-form identity. -/
theorem eq22s_exact_form_zero {D : Set ℂ} (hD : IsOpen D) {χ χx χy T Tx Ty : ℂ → ℂ}
    (hχ : HasGenPartials χ χx χy D 2) (hT : HasGenPartials T Tx Ty D 2)
    (hdχ : ∀ᵐ u ∂(volume.restrict D), DifferentiableAt ℝ χ u)
    (hdT : ∀ᵐ u ∂(volume.restrict D), DifferentiableAt ℝ T u)
    (hcχ : HasCompactSupport χ) (hsχ : tsupport χ⊆D) :
    IntegrableOn (fun u => dz T u*dzbar χ u-dzbar T u*dz χ u) D ∧
      (∫ u in D, dz T u*dzbar χ u-dzbar T u*dz χ u)=0 := by
  obtain ⟨hI,he⟩ := eq22s_beta_zero hD hχ hT hdχ hcχ hsχ
  have hdc := eq22s_partials hD hχ hdχ
  have hdt := eq22s_partials hD hT hdT
  have hEq : sp_beta χx χy Tx Ty =ᵐ[volume.restrict D]
      (fun u => dz T u*dzbar χ u-dzbar T u*dz χ u) := by
    filter_upwards [hdc.1,hdc.2,hdt.1,hdt.2] with u hcx hcy htx hty
    simp only [sp_beta,genDz,genDzbar,dz,dzbar,←hcx,←hcy,←htx,←hty]
    ring
  exact ⟨hI.congr hEq,(integral_congr_ae hEq).symm.trans he⟩

theorem eq22s_local_integrable {D : Set ℂ} (hD : IsOpen D) {F A : ℂ → ℂ}
    (hpair : ∀ a : ℂ → ℂ, ContDiff ℝ 1 a → HasCompactSupport a → tsupport a⊆D →
      eq22w_Pair F A a) {L : Set ℂ} (hL : IsCompact L) (hLD : L⊆D) : IntegrableOn A L := by
  obtain ⟨a,ha,hac,has,hag,_⟩ := eq22s_cutoff hL hD hLD
  have hI := (hpair a (ha.of_le (by norm_num)) hac has).1.integrableOn (s := L)
  apply hI.congr
  filter_upwards [ae_restrict_mem hL.measurableSet] with u hu
  rw [(hag u hu).self_of_nhds,one_mul]

theorem eq22s_dzbar_limit {L : Set ℂ} {fn : ℕ → ℂ → ℂ} {x y b : ℂ → ℂ}
    (hfn : ∀ n e, MemLp (fun u => fderiv ℝ (fn n) u e) 2 (volume.restrict L))
    (hx : MemLp x 2 (volume.restrict L)) (hy : MemLp y 2 (volume.restrict L))
    (hb : MemLp b 2 (volume.restrict L))
    (hxl : Tendsto (fun n => eLpNorm (fun u => fderiv ℝ (fn n) u 1-x u)
      2 (volume.restrict L)) atTop (𝓝 0))
    (hyl : Tendsto (fun n => eLpNorm (fun u => fderiv ℝ (fn n) u I-y u)
      2 (volume.restrict L)) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ u in L, b u*dzbar (fn n) u) atTop
      (𝓝 (∫ u in L, b u*genDzbar x y u)) := by
  have hlx := sp_tendsto_integral_mul_of_L2 (fun n => hfn n 1) hx hb hxl
  have hly := sp_tendsto_integral_mul_of_L2 (fun n => hfn n I) hy hb hyl
  have hAlg (p q : ℂ → ℂ) (hp : MemLp p 2 (volume.restrict L))
      (hq : MemLp q 2 (volume.restrict L)) :
      (∫ u in L, b u*((p u+I*q u)/2)) =
        ((∫ u in L, p u*b u)+I*(∫ u in L, q u*b u))/2 := by
    have he : (fun u => b u*((p u+I*q u)/2)) =
        (fun u => (p u*b u+I*(q u*b u))/2) := by funext u; ring
    have hpi : Integrable (fun u => p u*b u) (volume.restrict L) := hp.integrable_mul hb
    have hqi : Integrable (fun u => q u*b u) (volume.restrict L) := hq.integrable_mul hb
    rw [he,integral_div,integral_add hpi (hqi.const_mul I),
      integral_const_mul]
  have he (n : ℕ) := hAlg _ _ (hfn n 1) (hfn n I)
  simp only [dzbar,genDzbar,he,hAlg x y hx hy]
  exact (hlx.add (hly.const_mul I)).div_const 2

/-- A compact C1 Stokes functional extends to a compact local-W1,2 test. Local L1 of
the kernel is deduced from the original test identity, not added as an assumption. -/
theorem eq22s_extend_pair {D : Set ℂ} (hD : IsOpen D) {F A χ χx χy : ℂ → ℂ}
    (hF : ContinuousOn F D)
    (hpair : ∀ a : ℂ → ℂ, ContDiff ℝ 1 a → HasCompactSupport a → tsupport a⊆D →
      eq22w_Pair F A a)
    (hχ : HasGenPartials χ χx χy D 2)
    (hdχ : ∀ᵐ u ∂(volume.restrict D), DifferentiableAt ℝ χ u)
    (hcχ : HasCompactSupport χ) (hsχ : tsupport χ⊆D) : eq22w_Pair F A χ := by
  obtain ⟨a,ha,hac,has,hag,hKa⟩ := eq22s_cutoff hcχ.isCompact hD hsχ
  let L := tsupport a
  have hL : IsCompact L := hac.isCompact
  have hLD : L⊆D := has
  have hm : MeasurableSet L := hL.measurableSet
  have hcc : ContinuousOn χ D :=
    (lemma9_2_isACL_of_genPartials hD (by norm_num) hχ).1.1
  let fn := lemma92Approx D χ
  have hfn : ∀ n, ContDiff ℝ 2 (fn n) := fun n => sp_m_contDiff2 hcc n
  have hunif : TendstoUniformlyOn fn χ atTop L :=
    (tendstoLocallyUniformlyOn_iff_forall_isCompact hD).mp
      (tendstoLocallyUniformlyOn_lemma92Approx hD hcc) L hLD hL
  obtain ⟨hxlim,hylim⟩ := eq22s_mollifier hD hχ hL hLD
  obtain ⟨hχx,hχy⟩ := hχ.1 L hLD hL
  have hAi := eq22s_local_integrable hD hpair hL hLD
  have haAi : IntegrableOn (fun u => a u*A u) L :=
    IntegrableOn.continuousOn_mul ha.continuous.continuousOn hAi hL
  have hχAi : IntegrableOn (fun u => χ u*A u) L :=
    IntegrableOn.continuousOn_mul (hcc.mono hLD) hAi hL
  have hFc : ContinuousOn (fun u => F u*dzbar a u) L :=
    (hF.mono hLD).mul (continuous_dzbar (ha.of_le (by norm_num))).continuousOn
  have haFc : ContinuousOn (fun u => a u*F u) L :=
    ha.continuous.continuousOn.mul (hF.mono hLD)
  have haF : MemLp (fun u => a u*F u) 2 (volume.restrict L) :=
    sp_f2_memLp_of_continuousOn hL haFc
  have hdn (n : ℕ) (e : ℂ) : MemLp (fun u => fderiv ℝ (fn n) u e) 2 (volume.restrict L) :=
    sp_f2_memLp_of_continuousOn hL (sp_f2_continuous_fderiv (hfn n) e).continuousOn
  have hLlim := sp_tendsto_integral_mul_of_uniform haAi
    (fun n => IntegrableOn.continuousOn_mul (hfn n).continuous.continuousOn haAi hL)
    (IntegrableOn.continuousOn_mul (hcc.mono hLD) haAi hL) hunif
  have hRlim1 := sp_tendsto_integral_mul_of_uniform (hFc.integrableOn_compact hL)
    (fun n => ((hfn n).continuous.continuousOn.mul hFc).integrableOn_compact hL)
    (((hcc.mono hLD).mul hFc).integrableOn_compact hL) hunif
  have hRlim2 := eq22s_dzbar_limit hdn hχx hχy haF hxlim hylim
  have heL : (fun u => χ u*(a u*A u)) = (fun u => χ u*A u) := by
    funext u
    by_cases hu : u∈tsupport χ
    · rw [(hag u hu).self_of_nhds,one_mul]
    · simp [image_eq_zero_of_notMem_tsupport hu]
  have heR1 : (fun u => χ u*(F u*dzbar a u)) = (fun _ => 0) := by
    funext u
    by_cases hu : u∈tsupport χ
    · have hd : dzbar a u=0 := by simp [dzbar,(hag u hu).fderiv_eq]
      simp [hd]
    · simp [image_eq_zero_of_notMem_tsupport hu]
  have heR2 : (fun u => (a u*F u)*genDzbar χx χy u) =ᵐ[volume.restrict L]
      (fun u => F u*dzbar χ u) := by
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hLD
      (eq22w_genDzbar_eq hD hχ hdχ)] with u hu
    rw [hu]
    by_cases hK : u∈tsupport χ
    · rw [(hag u hK).self_of_nhds,one_mul]
    · simp [dzbar,sp_fderiv_eq_zero_of_notMem_tsupport hK]
  have hFRi : IntegrableOn (fun u => F u*dzbar χ u) L := by
    have he : (fun u => (a u*F u)*genDzbar χx χy u) =
        (fun u => ((a u*F u)*χx u+I*((a u*F u)*χy u))/2) := by
      funext u; simp only [genDzbar]; ring
    have hi : IntegrableOn (fun u => (a u*F u)*genDzbar χx χy u) L := by
      rw [he]
      exact ((haF.integrable_mul hχx).add ((haF.integrable_mul hχy).const_mul I)).div_const 2
    exact hi.congr heR2
  have hχ0 (u : ℂ) (hu : u∉L) : χ u=0 := image_eq_zero_of_notMem_tsupport
    (fun hh => hu (hKa hh))
  have hdχ0 (u : ℂ) (hu : u∉L) : dzbar χ u=0 := by
    have hK : u∉tsupport χ := fun hh => hu (hKa hh)
    simp [dzbar,sp_fderiv_eq_zero_of_notMem_tsupport hK]
  have hLeft0 (u : ℂ) (hu : u∉L) : χ u*A u=0 := by rw [hχ0 u hu,zero_mul]
  have hRight0 (u : ℂ) (hu : u∉L) : F u*dzbar χ u=0 := by rw [hdχ0 u hu,mul_zero]
  refine ⟨sp_ibp_integrable_of_support hm hχAi hLeft0,
    sp_ibp_integrable_of_support hm hFRi hRight0,?_⟩
  have he (n : ℕ) : (∫ u in L, fn n u*(a u*A u)) =
      -((∫ u in L, fn n u*(F u*dzbar a u)) + (∫ u in L, (a u*F u)*dzbar (fn n) u)) := by
    have hc : HasCompactSupport (fun u => a u*fn n u) := hac.mul_right
    have hs : tsupport (fun u => a u*fn n u) ⊆ L := tsupport_mul_subset_left
    have hp := (hpair _ ((ha.mul (hfn n)).of_le (by norm_num)) hc (hs.trans hLD)).2.2
    have hleft : (fun u => (a u*fn n u)*A u) = (fun u => fn n u*(a u*A u)) := by funext u; ring
    have hright : (fun u => F u*dzbar (fun u => a u*fn n u) u) =
        (fun u => fn n u*(F u*dzbar a u)+(a u*F u)*dzbar (fn n) u) := by
      funext u
      rw [dzbar_mul (ha.differentiable (by norm_num) u) ((hfn n).differentiable (by norm_num) u)]
      ring
    have hint1 : IntegrableOn (fun u => fn n u*(F u*dzbar a u)) L :=
      ((hfn n).continuous.continuousOn.mul hFc).integrableOn_compact hL
    have hint2 : IntegrableOn (fun u => (a u*F u)*dzbar (fn n) u) L :=
      (haFc.mul (continuous_dzbar ((hfn n).of_le (by norm_num))).continuousOn).integrableOn_compact hL
    have hLI := sp_setIntegral_eq_integral hm (subset_refl L)
      (h := fun u => (a u*fn n u)*A u) (fun u hu => by
        rw [image_eq_zero_of_notMem_tsupport hu,zero_mul,zero_mul])
    have hRI := sp_setIntegral_eq_integral hm (subset_refl L)
      (h := fun u => F u*dzbar (fun u => a u*fn n u) u) (fun u hu => by
        have hnot : u∉tsupport (fun u => a u*fn n u) := fun hh => hu (hs hh)
        simp [dzbar,sp_fderiv_eq_zero_of_notMem_tsupport hnot])
    rw [←hLI,←hRI,hleft,hright,integral_add hint1 hint2] at hp
    exact hp
  have hlim := (hRlim1.add hRlim2).neg
  have hEq := tendsto_nhds_unique hLlim (hlim.congr fun n => (he n).symm)
  rw [heL,heR1,integral_zero,zero_add,integral_congr_ae heR2] at hEq
  rwa [sp_setIntegral_eq_integral hm (subset_refl L) hLeft0,
    sp_setIntegral_eq_integral hm (subset_refl L) hRight0] at hEq

/-- The reflected-primitive Stokes formula for a genuinely weak, compact test function. -/
theorem eq22s_reflected_stokes {D Ω : Set ℂ} (hD : IsOpen D) (hΩ : IsOpen Ω)
    {h q Q1 Q2 Q3 χ χx χy : ℂ → ℂ} {z : ℂ}
    (hh : IsQuasiconformal (fun u => conj (h u)) D) (hm : MapsTo h D Ω)
    (h1 : ∀ v∈Ω, HasDerivAt Q1 (q v) v)
    (h2 : ∀ v∈Ω, HasDerivAt Q2 (Q1 v) v)
    (h3 : ∀ v∈Ω, HasDerivAt Q3 (Q2 v) v) (hz : z∉D)
    (hχ : HasGenPartials χ χx χy D 2)
    (hdχ : ∀ᵐ u ∂(volume.restrict D), DifferentiableAt ℝ χ u)
    (hcχ : HasCompactSupport χ) (hsχ : tsupport χ⊆D) :
    Integrable (fun u => χ u*(q (h u)*(u-h u)^2*dzbar h u/(u-z)^4)) ∧
    Integrable (fun u => eq22Primitive h Q1 Q2 Q3 z u*dzbar χ u) ∧
      (∫ u, χ u*(q (h u)*(u-h u)^2*dzbar h u/(u-z)^4)) =
        -(∫ u, eq22Primitive h Q1 Q2 Q3 z u*dzbar χ u) := by
  have hhc := eq22w_antiQC_continuous hh
  have hQ1c : ContinuousOn Q1 Ω := fun v hv => (h1 v hv).continuousAt.continuousWithinAt
  have hQ2c : ContinuousOn Q2 Ω := fun v hv => (h2 v hv).continuousAt.continuousWithinAt
  have hQ3c : ContinuousOn Q3 Ω := fun v hv => (h3 v hv).continuousAt.continuousWithinAt
  have hF : ContinuousOn (eq22Primitive h Q1 Q2 Q3 z) D := by
    have hdiff : ContinuousOn (fun u => u-h u) D := continuousOn_id.sub hhc
    exact ((((hQ1c.comp hhc hm).mul (hdiff.pow 2)).add
      (((hQ2c.comp hhc hm).mul hdiff).const_mul 2)).add
      ((hQ3c.comp hhc hm).const_mul 2)).div
      ((continuousOn_id.sub continuousOn_const).pow 4) (fun u hu =>
        pow_ne_zero 4 (sub_ne_zero.mpr (fun he => hz (he ▸ hu))))
  exact eq22s_extend_pair hD hF
    (fun a ha hac has => eq22w_reflected_stokes hD hΩ hh hm h1 h2 h3 hz ha hac has)
    hχ hdχ hcχ hsχ

end TakhtajanTeo

