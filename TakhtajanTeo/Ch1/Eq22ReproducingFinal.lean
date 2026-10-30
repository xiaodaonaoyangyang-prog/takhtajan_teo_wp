import TakhtajanTeo.Ch1.Eq22KernelAbsolute
import TakhtajanTeo.Ch1.Eq22BoundaryTail
import TakhtajanTeo.Ch1.Eq22RemainderLocal
import TakhtajanTeo.Ch1.Eq22BoundaryDisplacement
import TakhtajanTeo.Ch1.Eq22TargetTransfer
import TakhtajanTeo.Ch1.Eq22CompactCauchy
import TakhtajanTeo.Ch1.Eq22KernelContinuity
import TakhtajanTeo.Ch1.Eq22RemoveExceptionalPole

/-! Final assembly of the original reflection reproducing formula (2.2). -/
open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal Classical Real ComplexConjugate
noncomputable section
namespace TakhtajanTeo
open LiZhongQC

-- F0
theorem eq22_shrinking_sequence {R : ℝ} (hR : 0 < R) :
    ∃ ε : ℕ → ℝ, (∀ n, 0 < ε n) ∧ (∀ n, 2*ε n ≤ R) ∧ Tendsto ε atTop (𝓝 0) := by
  let ε : ℕ → ℝ := fun n => (R/4)/((n : ℝ)+1)
  have hε : ∀ n, 0 < ε n := fun n => div_pos (by positivity) (by positivity)
  have hb : ∀ n, ε n ≤ R/4 := by
    intro n
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < n+1)).mpr
    nlinarith [mul_nonneg hR.le (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  refine ⟨ε,hε,fun n => by linarith [hb n],?_⟩
  simpa only [ε,div_eq_mul_inv,one_mul,mul_zero] using
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (R/4)

-- F1
theorem eq22_reproducing_away {μ : LinfStar} (hμ : μ ∈ LinfStarBall) {h : ℂ → ℂ}
    (hh : IsQCReflection (fsans μ '' unitDisc) (gsans μ '' unitDiscExterior) h)
    {q : ℂ → ℂ} (hq : DifferentiableOn ℂ q (fsans μ '' unitDisc))
    (hq2 : ∫⁻ v in fsans μ '' unitDisc, (‖q v‖₊ : ℝ≥0∞)^2 *
      ENNReal.ofReal (poincareDensity (fsans μ '' unitDisc) v^2)⁻¹ < ∞)
    {a z : ℂ} (hinf : Tendsto h (cocompact ℂ) (𝓝 a))
    (hz : z ∈ fsans μ '' unitDisc) (hza : z ≠ a) :
    q z = -(3/π)*(∫ u in gsans μ '' unitDiscExterior,
      q (h u)*(u-h u)^2*dzbar h u/(u-z)^4) := by
  let Ω := fsans μ '' unitDisc
  let E := gsans μ '' unitDiscExterior
  let f := fsans μ
  let K : ℂ → ℂ := fun u => q (h u)*(u-h u)^2*dzbar h u/(u-z)^4
  have hf : IsConformalOnto f unitDisc Ω := S2C.s2c_conf_f hμ
  have hΩ : IsOpen Ω := hf.isOpen isOpen_ball
  obtain ⟨k,hk⟩ := hh.1
  have hEm : MeasurableSet E := hk.1.measurableSet
  have hhc : ContinuousOn h E := by
    simpa only [Function.comp_def,conj_conj] using continuous_conj.comp_continuousOn hk.2.2.1.1
  obtain ⟨e,heΩ,heE⟩ := eq22_welding_common_chart hμ
  have hΩb : Bornology.IsBounded Ω := by
    change Bornology.IsBounded (fsans μ '' unitDisc)
    rw [heΩ]
    exact ((isCompact_closedBall (0 : ℂ) 1).image e.continuous).isBounded.subset
      (image_mono ball_subset_closedBall)
  have hdis : Disjoint Ω E := by
    change Disjoint (fsans μ '' unitDisc) (gsans μ '' unitDiscExterior)
    rw [heΩ,heE]
    apply Set.disjoint_left.mpr
    rintro _ ⟨u,hu,rfl⟩ ⟨v,hv,he⟩
    have hev : v = u := e.injective he
    subst v
    have hnu := mem_ball_zero_iff.mp hu
    change 1 < ‖u‖ at hv
    linarith
  obtain ⟨a',ha',hinf',H,hH,hHmap,hleft,hright,htransfer⟩ := eq22v_reflection_transfer hμ hh hq hz
  have haa : a' = a := tendsto_nhds_unique hinf' hinf
  subst a'
  have ha : a ∈ Ω := ha'
  obtain ⟨ηE,hηE,hsepE⟩ := eq22_open_separation hΩ hdis hz
  obtain ⟨ηz,hηz,rz,hrz0,hrz1,hsepz⟩ := eq22_conformal_collar_separation hf hz
  obtain ⟨ηa,hηa,ra,hra0,hra1,hsepa⟩ := eq22_conformal_collar_separation hf ha
  obtain ⟨rg,hrg0,hrg1,D,hD,hgap⟩ := eq22_inverse_collar_displacement hμ hh hf ha hinf hHmap hright
  let r := max rg (max rz ra)
  have hr1 : r < 1 := max_lt hrg1 (max_lt hrz1 hra1)
  have hrrg : rg ≤ r := le_max_left _ _
  have hrrz : rz ≤ r := (le_max_left _ _).trans (le_max_right _ _)
  have hrra : ra ≤ r := (le_max_right _ _).trans (le_max_right _ _)
  let η := min ηE ηz
  have hη : 0 < η := lt_min hηE hηz
  have hgeom : ∀ w ∈ unitDisc, r ≤ ‖w‖^2 → ‖H (f w)-f w‖*poincareDensity Ω (f w) ≤ D :=
    fun w hw hwr => (hgap w hw (hrrg.trans hwr)).1
  have hsep : ∀ w ∈ unitDisc, r ≤ ‖w‖^2 → η ≤ ‖H (f w)-z‖ ∧ η ≤ ‖f w-z‖ := by
    intro w hw hwr
    have hneq : f w ≠ a := by
      intro he
      have hs := hsepa w hw (hrra.trans hwr)
      rw [he,sub_self,norm_zero] at hs
      exact (not_le_of_gt hηa) hs
    exact ⟨(min_le_left _ _).trans (hsepE _ (hHmap ⟨hf.mapsTo hw,hneq⟩)),
      (min_le_right _ _).trans (hsepz w hw (hrrz.trans hwr))⟩
  obtain ⟨ε,hε,hwidth,hεlim⟩ := eq22_shrinking_sequence (sub_pos.mpr hr1)
  have hθex : ∀ n, ∃ θ : ℂ → ℂ,
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) θ ∧ HasCompactSupport θ ∧ tsupport θ ⊆ Ω ∧
      (∀ w ∈ unitDisc, θ (f w) = eq22RadialCutoff (ε n) w) ∧ (∀ v, ‖θ v‖ ≤ 1) ∧
      ∀ w ∈ unitDisc, ‖dzbar θ (f w)‖*‖deriv f w‖ = ‖dzbar (eq22RadialCutoff (ε n)) w‖ := by
    intro n
    exact eq22_transport_cutoff hf (eq22_radial_cutoff_smooth (ε n))
      (eq22_radial_cutoff_support (hε n)).1 (eq22_radial_cutoff_support (hε n)).2
      (eq22_radial_cutoff_values (hε n)).2.2.1
  choose θ hθ hθc hθs hθf hθb hθd using hθex
  let R : ℂ → ℂ := fun v => q v*(H v-v)^3/((H v-z)^3*(v-z))
  have hRm : AEStronglyMeasurable R (volume.restrict Ω) :=
    eq22_remainder_measurable hΩ.measurableSet hH hq.continuousOn
  obtain ⟨r₀,hr₀,hball,B,hB,hRb⟩ := eq22_remainder_locally_bounded hΩ ha hza.symm
    (hq.continuousOn.continuousAt (hΩ.mem_nhds ha)) hHmap hηE hsepE
  obtain ⟨s,hs,hssmall,hslim⟩ := eq22_shrinking_sequence hr₀
  obtain ⟨M,hM,hbfamily⟩ := eq22_puncture_cutoff_family
  choose b hb hbc hb1 hb0 hbb hbcompl hbd using (fun n => hbfamily a (s n) (hs n))
  let t : ℕ → ℂ → ℂ := fun n v => θ n v*(1-b n v)
  have ht : ∀ n, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (t n) ∧ HasCompactSupport (t n) ∧
      tsupport (t n) ⊆ Ω \ {a} ∧ ∀ v, ‖t n v‖ ≤ 1 := by
    intro n
    exact eq22_remove_point_cutoff (hθ n) (hθc n) (hθs n) (hθb n) (hb n) (hbcompl n)
      (half_pos (hs n)) (fun v hv => hb1 n v hv.le)
  have hθlim : ∀ v ∈ Ω, Tendsto (fun n => θ n v) atTop (𝓝 1) := by
    intro v hv
    obtain ⟨w,hw,rfl⟩ := hf.2.2 ▸ hv
    exact (eq22_radial_cutoff_tendsto hε hεlim hw).congr (fun n => (hθf n w hw).symm)
  have htlim : ∀ v ∈ Ω \ {a}, Tendsto (fun n => t n v) atTop (𝓝 1) := by
    intro v hv
    have hvp : 0 < ‖v-a‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hv.2)
    have he : (fun n => t n v) =ᶠ[atTop] fun n => θ n v := by
      filter_upwards [hslim.eventually (gt_mem_nhds hvp)] with n hn
      simp only [t,hb0 n v hn.le,sub_zero,mul_one]
    exact (hθlim v hv.1).congr' he.symm
  have hmass : (∫⁻ v in Ω, ENNReal.ofReal (‖q v‖^2/(poincareDensity Ω v)^2)) < ∞ := by
    convert hq2 using 1
    apply setLIntegral_congr_fun hΩ.measurableSet
    intro v hv
    dsimp only
    rw [div_eq_mul_inv,ENNReal.ofReal_mul (sq_nonneg ‖q v‖),
      ENNReal.ofReal_pow (norm_nonneg (q v)),ofReal_norm,enorm_eq_nnnorm]
  let U : ℕ → ℂ → ℂ := fun n v => R v*(1-b n v)*dzbar (θ n) v
  let V : ℕ → ℂ → ℂ := fun n v => R v*θ n v*dzbar (b n) v
  have hU := eq22_boundary_tail hf hΩb ha hH hq hmass hε hεlim hwidth hθ hθd
    (fun n => continuous_const.sub (hb n).continuous) hbcompl hD.le hη hgeom hsep
  change (∀ n, IntegrableOn (U n) Ω) ∧ Tendsto (fun n => ∫ v in Ω, U n v) atTop (𝓝 0) at hU
  have hV := eq22_small_hole_tail hΩ.measurableSet hΩb hRm hB hM hball hRb hs hslim hssmall
    (fun n => (hθ n).continuous) hθb (fun n => (hb n).of_le (by norm_num)) hb0 hbd
  change (∀ n, IntegrableOn (V n) Ω) ∧ Tendsto (fun n => ∫ v in Ω, V n v) atTop (𝓝 0) at hV
  have hdt : ∀ n v, dzbar (t n) v = (1-b n v)*dzbar (θ n) v-θ n v*dzbar (b n) v := by
    intro n v
    have hd : dzbar (fun x => 1-b n x) v = -dzbar (b n) v := by
      unfold dzbar
      rw [fderiv_const_sub]
      simp only [neg_apply]
      ring
    have hm := dzbar_mul (u := θ n) (v := fun x => 1-b n x)
      (((hθ n).differentiable (by simp)) v)
      ((differentiableAt_const (1 : ℂ)).sub (((hb n).differentiable (by simp)) v))
    calc
      dzbar (t n) v = θ n v*dzbar (fun x => 1-b n x) v+(1-b n v)*dzbar (θ n) v := hm
      _ = _ := by rw [hd]; ring
  have heach : ∀ n, (∫ u in E, t n (h u)*K u) = (1/3 : ℂ)*
      (-(π : ℂ)*t n z*q z-((∫ v in Ω, U n v)-(∫ v in Ω, V n v))) := by
    intro n
    let J : ℂ → ℂ := fun v => q v*dzbar (t n) v/(v-z)
    obtain ⟨hJi,hJe⟩ := eq22_compact_cauchy hΩ hq ((ht n).1.of_le (by norm_num))
      (ht n).2.1 ((ht n).2.2.1.trans sdiff_subset) z
    have hJ0 : ∀ v, v ∉ Ω → J v = 0 := by
      intro v hv
      have hn : v ∉ tsupport (t n) := fun hn => hv ((ht n).2.2.1 hn).1
      have he := notMem_tsupport_iff_eventuallyEq.mp hn
      have hd : dzbar (t n) v = 0 := by
        rw [dzbar_congr_of_eventuallyEq he]
        simp [dzbar]
      simp only [J,hd,mul_zero,zero_div]
    have hJval : (∫ v in Ω, J v) = -(π : ℂ)*t n z*q z :=
      (setIntegral_eq_integral_of_forall_compl_eq_zero hJ0).trans hJe
    have he : (fun v => eq22v_targetKernel H q z v*dzbar (t n) v) =ᵐ[volume.restrict Ω]
        (fun v => J v-(U n v-V n v)) := by
      filter_upwards [ae_restrict_mem hΩ.measurableSet,
        ae_restrict_of_ae (volume.ae_ne a),ae_restrict_of_ae (volume.ae_ne z)] with v hv hva hvz
      have hHu : 0 < ‖H v-z‖ := hηE.trans_le (hsepE _ (hHmap ⟨hv,hva⟩))
      have hHnz : H v-z ≠ 0 := norm_pos_iff.mp hHu
      dsimp only [eq22v_targetKernel,J,U,V,R]
      rw [eq22_paired_kernel_split hHnz (sub_ne_zero.mpr hvz)]
      simp only [hdt n v]
      ring
    have htarget : (∫ v in Ω, eq22v_targetKernel H q z v*dzbar (t n) v) =
        -(π : ℂ)*t n z*q z-((∫ v in Ω, U n v)-(∫ v in Ω, V n v)) := by
      rw [integral_congr_ae he]
      calc
        (∫ v in Ω, J v-(U n v-V n v)) =
            (∫ v in Ω, J v)-(∫ v in Ω, U n v-V n v) :=
          integral_sub (show Integrable J (volume.restrict Ω) from hJi.integrableOn) ((hU.1 n).sub (hV.1 n))
        _ = _ := by rw [integral_sub (hU.1 n) (hV.1 n),hJval]
    obtain ⟨_,_,htr⟩ := htransfer (t n) ((ht n).1.of_le (by norm_num)) (ht n).2.1 (ht n).2.2.1
    have hsrc : (∫ u, E.indicator (t n ∘ h) u*K u) = ∫ u in E, t n (h u)*K u := by
      have he : (fun u => E.indicator (t n ∘ h) u*K u) = E.indicator (fun u => t n (h u)*K u) := by
        funext u
        by_cases hu : u ∈ E <;> simp [hu]
      rw [he,integral_indicator hEm]
    have hm : volume.restrict (Ω \ {a}) = volume.restrict Ω :=
      Measure.restrict_congr_set (sdiff_null_ae_eq_self (measure_singleton a))
    calc
      (∫ u in E, t n (h u)*K u) = ∫ u, E.indicator (t n ∘ h) u*K u := hsrc.symm
      _ = (1/3 : ℂ)*(∫ v in Ω \ {a}, eq22v_targetKernel H q z v*dzbar (t n) v) := htr
      _ = _ := by rw [hm,htarget]
  obtain ⟨a',_,hinf',himg⟩ := eq22_reflection_image hμ hh
  have haa : a' = a := tendsto_nhds_unique hinf' hinf
  subst a'
  have hmap : MapsTo h E (Ω \ {a}) := fun u hu => himg ▸ mem_image_of_mem h hu
  have hKi : IntegrableOn K E := eq22_kernel_integrable hμ hh hq hq2 hz
  have hleftlim : Tendsto (fun n => ∫ u in E, t n (h u)*K u) atTop (𝓝 (∫ u in E, K u)) := by
    apply tendsto_integral_of_dominated_convergence (fun u => ‖K u‖)
    · intro n
      exact (((ht n).1.continuous.comp_continuousOn hhc).aestronglyMeasurable hEm).mul hKi.aestronglyMeasurable
    · exact hKi.norm
    · intro n
      filter_upwards [ae_restrict_mem hEm] with u hu
      rw [norm_mul]
      exact (mul_le_mul_of_nonneg_right ((ht n).2.2.2 (h u)) (norm_nonneg _)).trans_eq (one_mul _)
    · filter_upwards [ae_restrict_mem hEm] with u hu
      simpa only [one_mul] using (htlim (h u) (hmap hu)).mul_const (K u)
  have hrightlim : Tendsto (fun n => (1/3 : ℂ)*
      (-(π : ℂ)*t n z*q z-((∫ v in Ω, U n v)-(∫ v in Ω, V n v)))) atTop
      (𝓝 ((1/3 : ℂ)*(-(π : ℂ)*q z))) := by
    simpa only [mul_one,sub_self,sub_zero] using
      ((((htlim z ⟨hz,hza⟩).const_mul (-(π : ℂ))).mul_const (q z)).sub (hU.2.sub hV.2)).const_mul (1/3 : ℂ)
  have heq := tendsto_nhds_unique hleftlim (hrightlim.congr (fun n => (heach n).symm))
  change q z = -(3/π)*(∫ u in E, K u)
  rw [heq]
  have hpi : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  field_simp

-- F2: the original hypotheses and conclusion, with no extra geometric input.
theorem eq22_reproducing {μ : LinfStar} (hμ : μ ∈ LinfStarBall) {h : ℂ → ℂ}
    (hh : IsQCReflection (fsans μ '' unitDisc) (gsans μ '' unitDiscExterior) h)
    {q : ℂ → ℂ} (hq : DifferentiableOn ℂ q (fsans μ '' unitDisc))
    (hq2 : ∫⁻ v in fsans μ '' unitDisc, (‖q v‖₊ : ℝ≥0∞)^2 *
      ENNReal.ofReal (poincareDensity (fsans μ '' unitDisc) v^2)⁻¹ < ∞)
    {z : ℂ} (hz : z ∈ fsans μ '' unitDisc) :
    q z = -(3/π)*(∫ u in gsans μ '' unitDiscExterior,
      q (h u)*(u-h u)^2*dzbar h u/(u-z)^4) := by
  obtain ⟨a,_,hinf,_⟩ := eq22_reflection_image hμ hh
  have hΩ := (S2C.s2c_conf_f hμ).isOpen isOpen_ball
  obtain ⟨k,hk⟩ := hh.1
  obtain ⟨e,heΩ,heE⟩ := eq22_welding_common_chart hμ
  have hdis : Disjoint (fsans μ '' unitDisc) (gsans μ '' unitDiscExterior) := by
    rw [heΩ,heE]
    apply Set.disjoint_left.mpr
    rintro _ ⟨u,hu,rfl⟩ ⟨v,hv,he⟩
    have hev : v = u := e.injective he
    subst v
    have hnu := mem_ball_zero_iff.mp hu
    change 1 < ‖u‖ at hv
    linarith
  exact eq22_remove_exceptional_pole (a := a) (c := -(3/π : ℂ)) hΩ hk.1.measurableSet hdis
    hq.continuousOn (fun w hw => eq22_kernel_integrable hμ hh hq hq2 hw)
    (fun w hw hwa => eq22_reproducing_away hμ hh hq hq2 hinf hw hwa) hz

end TakhtajanTeo
