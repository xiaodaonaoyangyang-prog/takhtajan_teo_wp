import TakhtajanTeo.Ch1.CuiBound
import TakhtajanTeo.Ch1.Eq22Primitive
import Mathlib.Geometry.Manifold.PartitionOfUnity

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal NNReal ComplexConjugate Classical Real
noncomputable section
namespace TakhtajanTeo
open LiZhongQC

theorem eq22w_cont_memLp {D C : Set ℂ} {f : ℂ → ℂ}
    (hf : ContinuousOn f D) (hCD : C⊆D) (hC : IsCompact C) : MemLp f 2 (volume.restrict C) := by
  haveI : IsFiniteMeasure (volume.restrict C) := isFiniteMeasure_restrict.mpr hC.measure_lt_top.ne
  obtain ⟨M,hM⟩ := hC.exists_bound_of_continuousOn (hf.mono hCD)
  exact MemLp.of_bound ((hf.mono hCD).aestronglyMeasurable hC.measurableSet) M
    ((ae_restrict_mem hC.measurableSet).mono hM)

/-- Compact testing converts local L2 weak derivatives into genuine whole-plane L1 products. -/
theorem eq22w_integrable_test {D : Set ℂ} {v a : ℂ → ℂ}
    (hv : ∀ C⊆D, IsCompact C → MemLp v 2 (volume.restrict C))
    (ha : Continuous a) (hac : HasCompactSupport a) (has : tsupport a⊆D) :
    Integrable (fun z => a z*v z) := by
  have hK := hac.isCompact
  have hA : MemLp a 2 (volume.restrict (tsupport a)) :=
    eq22w_cont_memLp ha.continuousOn (subset_refl _) hK
  have hI := hA.integrable_mul (hv _ has hK)
  exact sp_ibp_integrable_of_support hK.measurableSet hI
    (fun z hz => by rw [image_eq_zero_of_notMem_tsupport hz,zero_mul])

/-- Weak compact-support Stokes on an arbitrary open set; both integrals are actual L1 integrals. -/
theorem eq22w_stokes_test {D : Set ℂ} (hD : IsOpen D) {F Fx Fy χ : ℂ → ℂ}
    (hF : HasGenPartials F Fx Fy D 2) (hχ : ContDiff ℝ 1 χ)
    (hc : HasCompactSupport χ) (hs : tsupport χ⊆D) :
    Integrable (fun z => χ z*genDzbar Fx Fy z) ∧
    Integrable (fun z => F z*dzbar χ z) ∧
      (∫ z, χ z*genDzbar Fx Fy z)=-(∫ z, F z*dzbar χ z) := by
  have hFc : ContinuousOn F D := by
    obtain ⟨_,fn,hfn,hconv,_⟩ := hF
    exact hconv.continuousOn (Frequently.of_forall (fun n => (hfn n).continuousOn))
  have hxi := eq22w_integrable_test (fun C hCD hC => (hF.1 C hCD hC).1) hχ.continuous hc hs
  have hyi := eq22w_integrable_test (fun C hCD hC => (hF.1 C hCD hC).2) hχ.continuous hc hs
  have hd (e : ℂ) : Continuous (fun z => fderiv ℝ χ z e) :=
    (hχ.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hdi (e : ℂ) : Integrable (fun z => fderiv ℝ χ z e*F z) :=
    eq22w_integrable_test (fun C hCD hC => eq22w_cont_memLp hFc hCD hC)
      (hd e) (sp_hasCompactSupport_fderiv hc e) ((sp_tsupport_fderiv_subset e).trans hs)
  have hzero (z : ℂ) (hz : z∉tsupport χ) : χ z=0 := image_eq_zero_of_notMem_tsupport hz
  obtain ⟨hx,hy⟩ := sp_ibp hD hF hχ hc hs
  rw [sp_setIntegral_eq_integral hD.measurableSet hs
      (fun z hz => by rw [sp_fderiv_eq_zero_of_notMem_tsupport hz 1,zero_mul]),
    sp_setIntegral_eq_integral hD.measurableSet hs (fun z hz => by rw [hzero z hz,zero_mul])] at hx
  rw [sp_setIntegral_eq_integral hD.measurableSet hs
      (fun z hz => by rw [sp_fderiv_eq_zero_of_notMem_tsupport hz I,zero_mul]),
    sp_setIntegral_eq_integral hD.measurableSet hs (fun z hz => by rw [hzero z hz,zero_mul])] at hy
  have heL : (fun z => χ z*genDzbar Fx Fy z)=
      (fun z => (χ z*Fx z+I*(χ z*Fy z))/2) := by funext z; simp only [genDzbar]; ring
  have heR : (fun z => F z*dzbar χ z)=
      (fun z => (fderiv ℝ χ z 1*F z+I*(fderiv ℝ χ z I*F z))/2) := by
    funext z; simp only [dzbar]; ring
  refine ⟨?_,?_,?_⟩
  · rw [heL]
    exact (hxi.add (hyi.const_mul I)).div_const 2
  · rw [heR]
    exact ((hdi 1).add ((hdi I).const_mul I)).div_const 2
  · rw [heL,heR,integral_div,integral_div,integral_add hxi (hyi.const_mul I),
      integral_add (hdi 1) ((hdi I).const_mul I),integral_const_mul,integral_const_mul,hx,hy]
    ring

/-- At points of actual differentiability, the generalized Wirtinger derivative agrees a.e. -/
theorem eq22w_genDzbar_eq {D : Set ℂ} (hD : IsOpen D) {F Fx Fy : ℂ → ℂ}
    (hF : HasGenPartials F Fx Fy D 2)
    (hd : ∀ᵐ z ∂(volume.restrict D), DifferentiableAt ℝ F z) :
    genDzbar Fx Fy=ᵐ[volume.restrict D] dzbar F := by
  obtain ⟨_,hx,hy⟩ := lemma9_2_isACL_of_genPartials hD (by norm_num : (1 : ℝ≥0∞)≤2) hF
  filter_upwards [hx,hy,hd] with z hzx hzy hzd
  simp only [genDzbar,dzbar,← hzx,← hzy,partialX_eq_of_differentiableAt hzd,
    partialY_eq_of_differentiableAt hzd]

theorem eq22w_stokes_actual {D : Set ℂ} (hD : IsOpen D) {F Fx Fy χ : ℂ → ℂ}
    (hF : HasGenPartials F Fx Fy D 2)
    (hd : ∀ᵐ z ∂(volume.restrict D), DifferentiableAt ℝ F z)
    (hχ : ContDiff ℝ 1 χ) (hc : HasCompactSupport χ) (hs : tsupport χ⊆D) :
    Integrable (fun z => χ z*dzbar F z) ∧ Integrable (fun z => F z*dzbar χ z) ∧
      (∫ z, χ z*dzbar F z)=-(∫ z, F z*dzbar χ z) := by
  obtain ⟨hI,hJ,he⟩ := eq22w_stokes_test hD hF hχ hc hs
  have hgen := (ae_restrict_iff' hD.measurableSet).mp (eq22w_genDzbar_eq hD hF hd)
  have hae : (fun z => χ z*genDzbar Fx Fy z)=ᵐ[volume] (fun z => χ z*dzbar F z) := by
    filter_upwards [hgen] with z hz
    by_cases hzD : z∈D
    · rw [hz hzD]
    · have hzK : z∉tsupport χ := fun hh => hzD (hs hh)
      simp only [image_eq_zero_of_notMem_tsupport hzK, zero_mul]
  exact ⟨hI.congr hae,hJ,(integral_congr_ae hae).symm.trans he⟩

theorem eq22w_comp_sec {ψ : ℂ → ℂ} (hdψ : Continuous (fderiv ℝ ψ))
    {B : ℝ} (hB : ∀ u, ‖fderiv ℝ ψ u‖ ≤ B) {μ : Measure ℂ}
    {fn : ℕ → ℂ → ℂ} {f g : ℂ → ℂ}
    (hfn : ∀ᵐ z ∂μ, Tendsto (fun n => fn n z) atTop (𝓝 (f z)))
    (hfnc : ∀ n, AEStronglyMeasurable (fn n) μ) (hfc : AEStronglyMeasurable f μ)
    (hg : MemLp g 2 μ) :
    Tendsto (fun n => eLpNorm
      (fun z => (fderiv ℝ ψ (fn n z) - fderiv ℝ ψ (f z)) (g z)) 2 μ) atTop (𝓝 0) := by
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  have hmeas : ∀ n, AEStronglyMeasurable
      (fun z => (fderiv ℝ ψ (fn n z) - fderiv ℝ ψ (f z)) (g z)) μ :=
    fun n => (show Continuous (Function.uncurry fun (A : ℂ →L[ℝ] ℂ) (v : ℂ) => A v) from
      continuous_fst.clm_apply continuous_snd).comp_aestronglyMeasurable₂
        ((hdψ.comp_aestronglyMeasurable (hfnc n)).sub
          (hdψ.comp_aestronglyMeasurable hfc)) hg.aestronglyMeasurable
  have hrew : ∀ n, eLpNorm (fun z =>
      (fderiv ℝ ψ (fn n z) - fderiv ℝ ψ (f z)) (g z)) 2 μ =
      (∫⁻ z, ‖(fderiv ℝ ψ (fn n z) - fderiv ℝ ψ (f z)) (g z)‖ₑ ^ (2 : ℝ) ∂μ) ^
        (1 / (2 : ℝ)) := by
    intro n
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) (hmeas n)]
    simp
  simp only [hrew]
  have hint : ∫⁻ z, ‖g z‖ₑ ^ (2 : ℝ) ∂μ < ⊤ := by
    have := hg.eLpNorm_lt_top
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)
      hg.aestronglyMeasurable] at this
    simp only [ENNReal.toReal_ofNat] at this
    by_contra hcon
    rw [not_lt, top_le_iff] at hcon
    rw [hcon] at this
    simp at this
  have hlim : Tendsto (fun n => ∫⁻ z,
      ‖(fderiv ℝ ψ (fn n z) - fderiv ℝ ψ (f z)) (g z)‖ₑ ^ (2 : ℝ) ∂μ) atTop (𝓝 0) := by
    have := tendsto_lintegral_of_dominated_convergence'
      (μ := μ) (F := fun n z => ‖(fderiv ℝ ψ (fn n z) - fderiv ℝ ψ (f z)) (g z)‖ₑ ^ (2 : ℝ))
      (f := fun _ => 0) (bound := fun z => ENNReal.ofReal (2 * B) ^ (2 : ℝ) * ‖g z‖ₑ ^ (2 : ℝ))
      (fun n => (hmeas n).enorm.pow_const _) ?_ ?_ ?_
    · simpa using this
    · intro n
      refine Eventually.of_forall fun z => ?_
      have hz : ‖(fderiv ℝ ψ (fn n z) - fderiv ℝ ψ (f z)) (g z)‖ₑ ≤
          ENNReal.ofReal (2 * B) * ‖g z‖ₑ := by
        rw [← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_mul (by positivity)]
        refine ENNReal.ofReal_le_ofReal ?_
        calc ‖(fderiv ℝ ψ (fn n z) - fderiv ℝ ψ (f z)) (g z)‖
            ≤ ‖fderiv ℝ ψ (fn n z) - fderiv ℝ ψ (f z)‖ * ‖g z‖ := ContinuousLinearMap.le_opNorm _ _
          _ ≤ (2 * B) * ‖g z‖ := by
            gcongr
            exact (norm_sub_le _ _).trans (by linarith [hB (fn n z), hB (f z)])
      calc ‖(fderiv ℝ ψ (fn n z) - fderiv ℝ ψ (f z)) (g z)‖ₑ ^ (2 : ℝ)
          ≤ (ENNReal.ofReal (2 * B) * ‖g z‖ₑ) ^ (2 : ℝ) := by gcongr
        _ = _ := by rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
    · rw [lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg (by norm_num) ENNReal.ofReal_ne_top)]
      exact ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg (by norm_num) ENNReal.ofReal_ne_top) hint.ne
    · filter_upwards [hfn] with z hz
      have h1 : Tendsto (fun n => (fderiv ℝ ψ (fn n z) - fderiv ℝ ψ (f z)) (g z)) atTop (𝓝 0) := by
        have h2 : Tendsto (fun n => fderiv ℝ ψ (fn n z)) atTop (𝓝 (fderiv ℝ ψ (f z))) :=
          (hdψ.tendsto (f z)).comp hz
        have h3 : Tendsto (fun n => fderiv ℝ ψ (fn n z) (g z)) atTop
            (𝓝 (fderiv ℝ ψ (f z) (g z))) :=
          ((ContinuousLinearMap.apply ℝ ℂ (g z)).continuous.tendsto _).comp h2
        have h4 := h3.sub (tendsto_const_nhds (x := fderiv ℝ ψ (f z) (g z)))
        simpa only [sub_apply, sub_self] using h4
      have h4 := (continuous_enorm.tendsto 0).comp h1
      rw [enorm_zero] at h4
      have h5 := ((ENNReal.continuous_rpow_const (y := (2 : ℝ))).tendsto 0).comp h4
      simpa [Function.comp_def] using h5
  have := ((ENNReal.continuous_rpow_const (y := 1 / (2 : ℝ))).tendsto 0).comp hlim
  simpa [Function.comp_def] using this

/-- The bounded-outer weak chain rule on the actual open QC domain. -/
theorem eq22w_hasGen_comp {D : Set ℂ} (hD : IsOpen D) {f g h ψ : ℂ → ℂ}
    (hf : HasGenPartials f g h D 2) (hψ : ContDiff ℝ 1 ψ)
    {B : ℝ} (hB : ∀ u, ‖fderiv ℝ ψ u‖ ≤ B) :
    HasGenPartials (fun z => ψ (f z)) (fun z => fderiv ℝ ψ (f z) (g z))
      (fun z => fderiv ℝ ψ (f z) (h z)) D 2 := by
  obtain ⟨hloc, fn, hfn, hconv, hLp⟩ := hf
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  have hψd : Differentiable ℝ ψ := hψ.differentiable one_ne_zero
  have hdψc : Continuous (fderiv ℝ ψ) := hψ.continuous_fderiv one_ne_zero
  have hfc : ContinuousOn f D :=
    hconv.continuousOn (Frequently.of_forall fun n => (hfn n).continuousOn)
  have hfnd : ∀ n z, z∈D → DifferentiableAt ℝ (fn n) z := fun n z hz =>
    ((hfn n).differentiableOn one_ne_zero z hz).differentiableAt (hD.mem_nhds hz)
  have hlip : LipschitzWith ⟨B, hB0⟩ ψ :=
    lipschitzWith_of_nnnorm_fderiv_le hψd (fun x => by exact_mod_cast hB x)
  have happly : Continuous (Function.uncurry fun (A : ℂ →L[ℝ] ℂ) (w : ℂ) => A w) :=
    continuous_fst.clm_apply continuous_snd
  refine ⟨?_, fun n z => ψ (fn n z), fun n => hψ.comp_contDiffOn (hfn n), ?_, ?_⟩
  · intro C hCD hC
    obtain ⟨hMg, hMh⟩ := hloc C hCD hC
    have hM : ∀ v : ℂ → ℂ, MemLp v 2 (volume.restrict C) →
        MemLp (fun z => fderiv ℝ ψ (f z) (v z)) 2 (volume.restrict C) := by
      intro v hv
      refine MemLp.of_le_mul (c := B) hv ?_ ?_
      · exact happly.comp_aestronglyMeasurable₂
          (hdψc.comp_aestronglyMeasurable ((hfc.mono hCD).aestronglyMeasurable hC.measurableSet))
          hv.aestronglyMeasurable
      · exact Eventually.of_forall fun z =>
          (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul_of_nonneg_right (hB _) (norm_nonneg _))
    exact ⟨hM g hMg, hM h hMh⟩
  · exact hlip.uniformContinuous.comp_tendstoLocallyUniformlyOn hconv
  · intro C hCD hC
    obtain ⟨hL1, hL2⟩ := hLp C hCD hC
    obtain ⟨hMg, hMh⟩ := hloc C hCD hC
    have hfnc : ∀ n, AEStronglyMeasurable (fn n) (volume.restrict C) := fun n =>
      ((hfn n).continuousOn.mono hCD).aestronglyMeasurable hC.measurableSet
    have hfm : AEStronglyMeasurable f (volume.restrict C) :=
      (hfc.mono hCD).aestronglyMeasurable hC.measurableSet
    have hptw : ∀ᵐ z ∂(volume.restrict C), Tendsto (fun n => fn n z) atTop (𝓝 (f z)) :=
      (ae_restrict_mem hC.measurableSet).mono (fun z hz => hconv.tendsto_at (hCD hz))
    have key : ∀ (v : ℂ) (gv : ℂ → ℂ), MemLp gv 2 (volume.restrict C) →
        Tendsto (fun n => eLpNorm (fun z => fderiv ℝ (fn n) z v - gv z) 2 (volume.restrict C)) atTop
          (𝓝 0) →
        Tendsto (fun n => eLpNorm (fun z => fderiv ℝ (fun z => ψ (fn n z)) z v -
          fderiv ℝ ψ (f z) (gv z)) 2 (volume.restrict C)) atTop (𝓝 0) := by
      intro v gv hgv hl
      have hsplit (n : ℕ) : (fun z => fderiv ℝ (fun z => ψ (fn n z)) z v - fderiv ℝ ψ (f z) (gv z))
          =ᵐ[volume.restrict C] (fun z =>
            fderiv ℝ ψ (fn n z) (fderiv ℝ (fn n) z v - gv z) +
            (fderiv ℝ ψ (fn n z) - fderiv ℝ ψ (f z)) (gv z)) := by
        filter_upwards [ae_restrict_mem hC.measurableSet] with z hz
        have e : fderiv ℝ (fun z => ψ (fn n z)) z =
            (fderiv ℝ ψ (fn n z)).comp (fderiv ℝ (fn n) z) :=
          fderiv_comp z (hψd (fn n z)) (hfnd n z (hCD hz))
        rw [e, ContinuousLinearMap.comp_apply, map_sub, sub_apply]
        abel
      have hmeas1 : ∀ n, AEStronglyMeasurable (fun z => fderiv ℝ (fn n) z v - gv z)
          (volume.restrict C) := fun n =>
        (measurable_fderiv_apply_const ℝ (fn n) v).aestronglyMeasurable.sub hgv.aestronglyMeasurable
      have hb : ∀ n, eLpNorm (fun z => fderiv ℝ (fun z => ψ (fn n z)) z v - fderiv ℝ ψ (f z) (gv z)) 2
          (volume.restrict C) ≤
          ENNReal.ofReal B * eLpNorm (fun z => fderiv ℝ (fn n) z v - gv z) 2 (volume.restrict C) +
            eLpNorm (fun z => (fderiv ℝ ψ (fn n z) - fderiv ℝ ψ (f z)) (gv z)) 2
              (volume.restrict C) := by
        intro n
        rw [eLpNorm_congr_ae (hsplit n)]
        refine (eLpNorm_add_le (by norm_num)).trans ?_
        gcongr
        have hfirst : AEStronglyMeasurable (fun z => fderiv ℝ ψ (fn n z) (fderiv ℝ (fn n) z v - gv z))
            (volume.restrict C) :=
          happly.comp_aestronglyMeasurable₂ (hdψc.comp_aestronglyMeasurable (hfnc n)) (hmeas1 n)
        have := eLpNorm_le_nnreal_smul_eLpNorm_of_ae_le_mul (c := ⟨B, hB0⟩) hfirst
          (Eventually.of_forall fun z => by
            rw [← NNReal.coe_le_coe]
            simp only [coe_nnnorm, NNReal.coe_mul]
            exact (ContinuousLinearMap.le_opNorm _ _).trans
              (mul_le_mul_of_nonneg_right (hB _) (norm_nonneg _))) 2
        refine this.trans (le_of_eq ?_)
        rw [ENNReal.ofReal, Real.toNNReal_of_nonneg hB0]
        rfl
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ?_ (fun n => zero_le) hb
      have h0 := (ENNReal.Tendsto.const_mul (a := ENNReal.ofReal B) hl (Or.inr ENNReal.ofReal_ne_top)).add
        (eq22w_comp_sec hdψc hB hptw hfnc hfm hgv)
      simpa using h0
    exact ⟨key 1 g hMg hL1, key I h hMh hL2⟩

/-- A genuine compact-test identity, including both integrability obligations. -/
def eq22w_Pair (F A χ : ℂ → ℂ) : Prop :=
  Integrable (fun u => χ u * A u) ∧ Integrable (fun u => F u * dzbar χ u) ∧
    (∫ u, χ u * A u) = -(∫ u, F u * dzbar χ u)

theorem eq22w_pair_congr {D : Set ℂ} (hD : MeasurableSet D)
    {F G A B χ : ℂ → ℂ} (hs : tsupport χ ⊆ D)
    (hF : ∀ u ∈ tsupport χ, F u = G u)
    (hA : A =ᵐ[volume.restrict D] B) (hp : eq22w_Pair F A χ) : eq22w_Pair G B χ := by
  have hAB : (fun u => χ u*A u) =ᵐ[volume] (fun u => χ u*B u) := by
    filter_upwards [(ae_restrict_iff' hD).mp hA] with u hu
    by_cases huD : u ∈ D
    · rw [hu huD]
    · have huK : u ∉ tsupport χ := fun hk => huD (hs hk)
      simp only [image_eq_zero_of_notMem_tsupport huK, zero_mul]
  have hFG : (fun u => F u*dzbar χ u) = (fun u => G u*dzbar χ u) := by
    funext u
    by_cases huK : u ∈ tsupport χ
    · rw [hF u huK]
    · have he : dzbar χ u = 0 := by
        simp [dzbar, sp_fderiv_eq_zero_of_notMem_tsupport huK]
      simp [he]
  exact ⟨hp.1.congr hAB, hFG ▸ hp.2.1,
    (integral_congr_ae hAB).symm.trans (hp.2.2.trans (by rw [hFG]))⟩

theorem eq22w_pair_add {F G A B χ : ℂ → ℂ}
    (hf : eq22w_Pair F A χ) (hg : eq22w_Pair G B χ) :
    eq22w_Pair (fun u => F u+G u) (fun u => A u+B u) χ := by
  unfold eq22w_Pair at *
  simp only [mul_add, add_mul]
  refine ⟨hf.1.add hg.1, hf.2.1.add hg.2.1, ?_⟩
  rw [integral_add hf.1 hg.1, integral_add hf.2.1 hg.2.1, hf.2.2, hg.2.2]
  ring

/-- A local smooth target can be extended near a compact set without boundary assumptions. -/
theorem eq22w_target_extension {Ω K : Set ℂ} (hΩ : IsOpen Ω) (hK : IsCompact K)
    (hKΩ : K ⊆ Ω) {Q : ℂ → ℂ} (hQ : ContDiffOn ℝ 1 Q Ω) :
    ∃ ψ : ℂ → ℂ, ContDiff ℝ 1 ψ ∧ HasCompactSupport ψ ∧
      ∀ v ∈ K, ψ =ᶠ[𝓝 v] Q := by
  obtain ⟨δ, hδ, hδΩ⟩ := hK.exists_cthickening_subset_open hΩ hKΩ
  obtain ⟨b, hb, _, hbs, hb1⟩ := exists_contDiff_support_eq_eq_one_iff
    (n := (1 : ℕ∞)) (s := thickening δ K) (t := cthickening (δ/2) K)
    isOpen_thickening isClosed_cthickening
    (cthickening_subset_thickening' hδ (half_lt_self hδ) K)
  let a : ℂ → ℂ := fun v => (b v : ℂ)
  have ha : ContDiff ℝ 1 a := Complex.ofRealCLM.contDiff.comp hb
  have hs : tsupport a ⊆ cthickening δ K := by
    have he : Function.support a = Function.support b := by
      ext v
      simp [a, Function.mem_support]
    rw [tsupport, he, hbs]
    exact closure_thickening_subset_cthickening δ K
  have hac : HasCompactSupport a := hK.cthickening.of_isClosed_subset (isClosed_tsupport a) hs
  refine ⟨fun v => a v*Q v, sp_contDiff_mul hΩ hQ ha (hs.trans hδΩ), hac.mul_right, ?_⟩
  intro v hv
  have hn : thickening (δ/2) K ∈ 𝓝 v :=
    isOpen_thickening.mem_nhds (self_subset_thickening (half_pos hδ) K hv)
  filter_upwards [hn] with w hw
  have he := (hb1 w).mp ((thickening_subset_cthickening (δ/2) K) hw)
  simp [a, he]

/-- Compact smooth targets of an anti-QC map have genuine local weak partials. -/
theorem eq22w_antiQC_comp {D : Set ℂ} {h ψ : ℂ → ℂ}
    (hh : IsQuasiconformal (fun u => conj (h u)) D)
    (hψ : ContDiff ℝ 1 ψ) (hc : HasCompactSupport ψ) :
    ∃ Fx Fy, HasGenPartials (fun u => ψ (h u)) Fx Fy D 2 ∧
      (∀ᵐ u ∂(volume.restrict D), DifferentiableAt ℝ (fun u => ψ (h u)) u) := by
  obtain ⟨K, hK⟩ := hh
  let φ : ℂ → ℂ := fun v => ψ (conj v)
  have hφ : ContDiff ℝ 1 φ := hψ.comp Complex.conjCLE.contDiff
  have hcφ : HasCompactSupport φ := hc.comp_homeomorph Complex.conjCLE.toHomeomorph
  obtain ⟨B,hB⟩ := (hcφ.fderiv (𝕜 := ℝ)).exists_bound_of_continuous
    (hφ.continuous_fderiv one_ne_zero)
  have hgen := eq22w_hasGen_comp hK.1 (thm9_5_L2_derivatives hK).1 hφ hB
  have he : (fun u => φ (conj (h u))) = (fun u => ψ (h u)) := by
    funext u
    simp [φ]
  rw [he] at hgen
  refine ⟨_,_,hgen,?_⟩
  filter_upwards [thm9_3_differentiable_ae hK] with u hu
  have hd : DifferentiableAt ℝ (fun u => φ (conj (h u))) u :=
    (hφ.differentiable one_ne_zero _).comp u hu
  rw [he] at hd
  exact hd

theorem eq22w_antiQC_continuous {D : Set ℂ} {h : ℂ → ℂ}
    (hh : IsQuasiconformal (fun u => conj (h u)) D) : ContinuousOn h D := by
  obtain ⟨K,hK⟩ := hh
  have hw := hK.2.2.1.1
  simpa [Function.comp_def] using
    Complex.continuous_conj.comp_continuousOn hw

theorem eq22w_antiQC_diff {D : Set ℂ} {h : ℂ → ℂ}
    (hh : IsQuasiconformal (fun u => conj (h u)) D) :
    ∀ᵐ u ∂(volume.restrict D), DifferentiableAt ℝ h u := by
  obtain ⟨K,hK⟩ := hh
  filter_upwards [thm9_3_differentiable_ae hK] with u hu
  have hd : DifferentiableAt ℝ (fun u => conj (conj (h u))) u :=
    Complex.conjCLE.differentiableAt.comp u hu
  simpa using hd

/-- Holomorphic targets need only be defined on the image domain of the anti-QC map. -/
theorem eq22w_stokes_pullback {D Ω : Set ℂ} (hD : IsOpen D) (hΩ : IsOpen Ω)
    {h Q χ : ℂ → ℂ} (hh : IsQuasiconformal (fun u => conj (h u)) D)
    (hm : MapsTo h D Ω) (hQ : DifferentiableOn ℂ Q Ω)
    (hχ : ContDiff ℝ 1 χ) (hc : HasCompactSupport χ) (hs : tsupport χ⊆D) :
    eq22w_Pair (fun u => Q (h u)) (dzbar (fun u => Q (h u))) χ := by
  have hhc := eq22w_antiQC_continuous hh
  have hK := hc.isCompact.image_of_continuousOn (hhc.mono hs)
  obtain ⟨ψ,hψ,hψc,hψQ⟩ := eq22w_target_extension hΩ hK
    (image_subset_iff.mpr (fun u hu => hm (hs hu))) ((hQ.contDiffOn hΩ).restrict_scalars ℝ)
  obtain ⟨Fx,Fy,hgen,hd⟩ := eq22w_antiQC_comp hh hψ hψc
  have hp := eq22w_stokes_actual hD hgen hd hχ hc hs
  have hgerm (u : ℂ) (hu : u∈tsupport χ) :
      (fun u => ψ (h u)) =ᶠ[𝓝 u] (fun u => Q (h u)) :=
    (hψQ (h u) (mem_image_of_mem _ hu)).comp_tendsto
      ((hhc u (hs hu)).continuousAt (hD.mem_nhds (hs hu)))
  apply eq22w_pair_congr hc.isCompact.measurableSet (subset_refl (tsupport χ))
    (fun u hu => (hgerm u hu).eq_of_nhds) ?_ hp
  filter_upwards [ae_restrict_mem hc.isCompact.measurableSet] with u hu
  exact dzbar_congr_of_eventuallyEq (hgerm u hu)

/-- Absorb a holomorphic spatial coefficient into the compact test function. -/
theorem eq22w_stokes_holo_mul {D : Set ℂ} (hD : IsOpen D) {F c χ : ℂ → ℂ}
    (hF : ∀ a : ℂ → ℂ, ContDiff ℝ 1 a → HasCompactSupport a → tsupport a⊆D →
      eq22w_Pair F (dzbar F) a)
    (hdF : ∀ᵐ u ∂(volume.restrict D), DifferentiableAt ℝ F u)
    (hcd : DifferentiableOn ℂ c D)
    (hχ : ContDiff ℝ 1 χ) (hc : HasCompactSupport χ) (hs : tsupport χ⊆D) :
    eq22w_Pair (fun u => F u*c u) (dzbar (fun u => F u*c u)) χ := by
  have hcc : ContDiffOn ℝ 1 c D := (hcd.contDiffOn hD).restrict_scalars ℝ
  have hac : HasCompactSupport (fun u => χ u*c u) := hc.mul_right
  have has : tsupport (fun u => χ u*c u) ⊆ tsupport χ := tsupport_mul_subset_left
  have hp := hF _ (sp_contDiff_mul hD hcc hχ hs) hac (has.trans hs)
  have he : (fun u => F u*dzbar (fun u => χ u*c u) u) =
      (fun u => (F u*c u)*dzbar χ u) := by
    funext u
    by_cases hu : u∈tsupport χ
    · have hcu := (hcd u (hs hu)).differentiableAt (hD.mem_nhds (hs hu))
      rw [dzbar_mul (hχ.differentiable one_ne_zero u) (hcu.restrictScalars ℝ),
        (cauchyRiemann_iff.mp hcu).2]
      ring
    · have hau : u∉tsupport (fun u => χ u*c u) := fun hh => hu (has hh)
      simp [dzbar, sp_fderiv_eq_zero_of_notMem_tsupport hu,
        sp_fderiv_eq_zero_of_notMem_tsupport hau]
  have heL : (fun u => (χ u*c u)*dzbar F u) = (fun u => χ u*(c u*dzbar F u)) := by
    funext u; ring
  have hp' : eq22w_Pair (fun u => F u*c u) (fun u => c u*dzbar F u) χ := by
    unfold eq22w_Pair at hp ⊢
    simpa only [he, heL] using hp
  apply eq22w_pair_congr hD.measurableSet hs (fun _ _ => rfl) ?_ hp'
  filter_upwards [hdF, ae_restrict_mem hD.measurableSet] with u hu huD
  have hcu := (hcd u huD).differentiableAt (hD.mem_nhds huD)
  rw [dzbar_mul hu (hcu.restrictScalars ℝ), (cauchyRiemann_iff.mp hcu).2]
  ring

theorem eq22w_stokes_add {D : Set ℂ} (hD : MeasurableSet D) {F G χ : ℂ → ℂ}
    (hs : tsupport χ⊆D)
    (hdF : ∀ᵐ u ∂(volume.restrict D), DifferentiableAt ℝ F u)
    (hdG : ∀ᵐ u ∂(volume.restrict D), DifferentiableAt ℝ G u)
    (hf : eq22w_Pair F (dzbar F) χ) (hg : eq22w_Pair G (dzbar G) χ) :
    eq22w_Pair (fun u => F u+G u) (dzbar (fun u => F u+G u)) χ := by
  apply eq22w_pair_congr hD hs (fun _ _ => rfl) ?_ (eq22w_pair_add hf hg)
  filter_upwards [hdF,hdG] with u hu hv
  exact (wp_dzbar_add hu hv).symm

theorem eq22w_stokes_holo_term {D Ω : Set ℂ} (hD : IsOpen D) (hΩ : IsOpen Ω)
    {h Q c χ : ℂ → ℂ} (hh : IsQuasiconformal (fun u => conj (h u)) D)
    (hm : MapsTo h D Ω) (hQ : DifferentiableOn ℂ Q Ω) (hcd : DifferentiableOn ℂ c D)
    (hχ : ContDiff ℝ 1 χ) (hc : HasCompactSupport χ) (hs : tsupport χ⊆D) :
    eq22w_Pair (fun u => Q (h u)*c u) (dzbar (fun u => Q (h u)*c u)) χ ∧
      (∀ᵐ u ∂(volume.restrict D), DifferentiableAt ℝ (fun u => Q (h u)*c u) u) := by
  have hdQ : ∀ᵐ u ∂(volume.restrict D), DifferentiableAt ℝ (fun u => Q (h u)) u := by
    filter_upwards [eq22w_antiQC_diff hh, ae_restrict_mem hD.measurableSet] with u hu huD
    exact (((hQ _ (hm huD)).differentiableAt (hΩ.mem_nhds (hm huD))).restrictScalars ℝ).comp u hu
  refine ⟨eq22w_stokes_holo_mul hD
    (fun a ha hac has => eq22w_stokes_pullback hD hΩ hh hm hQ ha hac has)
    hdQ hcd hχ hc hs, ?_⟩
  filter_upwards [hdQ, ae_restrict_mem hD.measurableSet] with u hu huD
  exact hu.mul (((hcd u huD).differentiableAt (hD.mem_nhds huD)).restrictScalars ℝ)

/-- Compact interior Stokes for the actual reflected triple primitive. No reflection C1 or
boundary trace assumption is used. Both displayed whole-plane integrals are integrable. -/
theorem eq22w_reflected_stokes {D Ω : Set ℂ} (hD : IsOpen D) (hΩ : IsOpen Ω)
    {h q Q1 Q2 Q3 χ : ℂ → ℂ} {z : ℂ}
    (hh : IsQuasiconformal (fun u => conj (h u)) D) (hm : MapsTo h D Ω)
    (h1 : ∀ v∈Ω, HasDerivAt Q1 (q v) v)
    (h2 : ∀ v∈Ω, HasDerivAt Q2 (Q1 v) v)
    (h3 : ∀ v∈Ω, HasDerivAt Q3 (Q2 v) v) (hz : z∉D)
    (hχ : ContDiff ℝ 1 χ) (hc : HasCompactSupport χ) (hs : tsupport χ⊆D) :
    Integrable (fun u => χ u*(q (h u)*(u-h u)^2*dzbar h u/(u-z)^4)) ∧
    Integrable (fun u => eq22Primitive h Q1 Q2 Q3 z u*dzbar χ u) ∧
      (∫ u, χ u*(q (h u)*(u-h u)^2*dzbar h u/(u-z)^4)) =
        -(∫ u, eq22Primitive h Q1 Q2 Q3 z u*dzbar χ u) := by
  have hQ1 : DifferentiableOn ℂ Q1 Ω := fun v hv => (h1 v hv).differentiableAt.differentiableWithinAt
  have hQ2 : DifferentiableOn ℂ Q2 Ω := fun v hv => (h2 v hv).differentiableAt.differentiableWithinAt
  have hQ3 : DifferentiableOn ℂ Q3 Ω := fun v hv => (h3 v hv).differentiableAt.differentiableWithinAt
  let A : ℂ → ℂ := Q1
  let B : ℂ → ℂ := fun v => 2*Q2 v-2*(v*Q1 v)
  let C : ℂ → ℂ := fun v => v^2*Q1 v-2*(v*Q2 v)+2*Q3 v
  have hB : DifferentiableOn ℂ B Ω :=
    (hQ2.const_mul 2).sub ((differentiableOn_id.mul hQ1).const_mul 2)
  have hC : DifferentiableOn ℂ C Ω :=
    (((differentiableOn_id.pow 2).mul hQ1).sub
      ((differentiableOn_id.mul hQ2).const_mul 2)).add (hQ3.const_mul 2)
  let k : ℂ → ℂ := fun u => ((u-z)^4)⁻¹
  have hk : DifferentiableOn ℂ k D := by
    intro u hu
    have huz : u≠z := fun he => hz (he ▸ hu)
    exact (((differentiableAt_id.sub_const z).pow 4).inv
      (pow_ne_zero 4 (sub_ne_zero.mpr huz))).differentiableWithinAt
  obtain ⟨hp0,hd0⟩ := eq22w_stokes_holo_term hD hΩ hh hm hQ1
    ((differentiableOn_id.pow 2).mul hk) hχ hc hs
  obtain ⟨hp1,hd1⟩ := eq22w_stokes_holo_term hD hΩ hh hm hB
    (differentiableOn_id.mul hk) hχ hc hs
  obtain ⟨hp2,hd2⟩ := eq22w_stokes_holo_term hD hΩ hh hm hC hk hχ hc hs
  have hp01 := eq22w_stokes_add hD.measurableSet hs hd0 hd1 hp0 hp1
  have hd01 : ∀ᵐ u ∂(volume.restrict D), DifferentiableAt ℝ
      (fun u => Q1 (h u)*(u^2*k u)+B (h u)*(u*k u)) u := by
    filter_upwards [hd0,hd1] with u hu hv
    exact hu.add hv
  have hp := eq22w_stokes_add hD.measurableSet hs hd01 hd2 hp01 hp2
  have he : (fun u => (Q1 (h u)*(u^2*k u)+B (h u)*(u*k u))+C (h u)*k u) =
      eq22Primitive h Q1 Q2 Q3 z := by
    funext u
    simp only [B,C,k,eq22Primitive,div_eq_mul_inv]
    ring
  rw [he] at hp
  apply eq22w_pair_congr hD.measurableSet hs (fun _ _ => rfl) ?_ hp
  filter_upwards [eq22w_antiQC_diff hh, ae_restrict_mem hD.measurableSet] with u hu huD
  have huz : u≠z := fun he => hz (he ▸ huD)
  exact (eq22_primitive_dzbar hu (h1 _ (hm huD)) (h2 _ (hm huD))
    (h3 _ (hm huD)) huz).2

end TakhtajanTeo

