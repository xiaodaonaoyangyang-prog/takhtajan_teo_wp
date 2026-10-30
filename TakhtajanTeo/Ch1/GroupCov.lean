import TakhtajanTeo.Ch1.GroupB1
import TakhtajanTeo.Ch1.TV1Variation
import TakhtajanTeo.Ch1.WPChangeOfVariables

/-!
# Group chain: harmonic base-point covariance (lemma 2.5, S2)

The frozen `grp25_cov` interface is proved without an extra nonzero-derivative premise.
Conformal pullback preserves harmonicity and the L∞ norm bound. Reflection gives the
correct interior coefficient, disk Stoilow gives the conformal comparison, and the
Poincaré density identity transports C¹ regularity and the density ratio from zero.
All helpers use the `grp25c_` prefix. This module does not close `lemma_2_5` itself.
-/

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal NNReal ComplexConjugate Classical Real
noncomputable section
namespace TakhtajanTeo
open LiZhongQC
open WPCV

theorem grp25c_density {S : ℂ → ℂ} (hS : IsConformalOnto S unitDisc unitDisc)
    {z : ℂ} (hz : z∈unitDisc) :
    ‖deriv S z‖^2/(1-‖S z‖^2)^2=1/(1-‖z‖^2)^2 := by
  obtain ⟨c,a,hc,ha,he⟩ := exists_rotation_blaschke_of_isConformalOnto_unitDisc hS
  have hev : S=ᶠ[𝓝 z] (fun w => c*blaschke a w) := by
    filter_upwards [(show IsOpen unitDisc from isOpen_ball).mem_nhds hz] with w hw
    exact he hw
  have hd := poincareDensityDisc_rotBlaschke hc ha (mem_ball_zero_iff.mp hz)
  rw [← hev.eq_of_nhds,← hev.deriv_eq] at hd
  have hs := congrArg (fun x : ℝ => x^2) hd
  norm_num [poincareDensityDisc,mul_pow,div_pow] at hs
  linear_combination hs/4

/-- Analytic transport from the normalized map at zero, once its disk Stoilow comparison is known. -/
theorem grp25c_transport {F G S : ℂ → ℂ} {a : ℂ} (ha : a∈unitDisc)
    (hS : IsConformalOnto S unitDisc unitDisc) (hG0 : G 0∈unitDisc)
    (he : EqOn (fun z => F (blaschke (-a) z)) (fun z => S (G z)) unitDisc)
    (hG : ContDiffAt ℝ 1 G 0) :
    ContDiffAt ℝ 1 F a ∧
      ‖dz F a‖^2/(1-‖F a‖^2)^2*(1-‖a‖^2)^2=
        ‖dz G 0‖^2/(1-‖G 0‖^2)^2 := by
  have han : ‖a‖<1 := mem_ball_zero_iff.mp ha
  have hna : ‖-a‖<1 := by simpa using han
  have hD : IsOpen unitDisc := isOpen_ball
  have h0 : (0 : ℂ)∈unitDisc := mem_ball_self one_pos
  have hSg : ContDiffAt ℝ 1 S (G 0) :=
    ((hS.1.contDiffOn hD).contDiffAt (hD.mem_nhds hG0)).restrict_scalars ℝ
  have hSG := hSg.comp 0 hG
  have hBa : ContDiffAt ℝ 1 (blaschke a) a :=
    (((differentiableOn_blaschke han).contDiffOn hD).contDiffAt (hD.mem_nhds ha)).restrict_scalars ℝ
  have hBaa : blaschke a a=0 := by simp [blaschke]
  have hFa : ContDiffAt ℝ 1 F a := by
    have hcomp : ContDiffAt ℝ 1 (fun z => S (G (blaschke a z))) a := by
      have hSG' : ContDiffAt ℝ 1 (fun z => S (G z)) (blaschke a a) := by rwa [hBaa]
      exact hSG'.comp a hBa
    apply hcomp.congr_of_eventuallyEq
    filter_upwards [hD.mem_nhds ha] with z hz
    have hBz : blaschke a z∈unitDisc :=
      mem_ball_zero_iff.mpr (blaschke_mem_unitDisc han (mem_ball_zero_iff.mp hz))
    have hh := he hBz
    dsimp only at hh
    rwa [blaschke_neg_blaschke han (mem_ball_zero_iff.mp hz)] at hh
  have hT0 : blaschke (-a) 0=a := by simp [blaschke]
  have hFval : F a=S (G 0) := by simpa only [hT0] using he h0
  have hFdiff : DifferentiableAt ℝ F a := hFa.differentiableAt (by norm_num)
  have hGdiff : DifferentiableAt ℝ G 0 := hG.differentiableAt (by norm_num)
  have hTdiff : DifferentiableAt ℂ (blaschke (-a)) 0 :=
    (differentiableOn_blaschke hna).differentiableAt (hD.mem_nhds h0)
  have hdF := (eq6_4 hTdiff (by simpa only [hT0] using hFdiff)).1
  have hdG := (eq6_5 hGdiff (hS.1.differentiableAt (hD.mem_nhds hG0))).1
  have hev : (F ∘ blaschke (-a))=ᶠ[𝓝 0] (S ∘ G) := by
    filter_upwards [hD.mem_nhds h0] with z hz
    exact he hz
  have hd := (t203_c1_dz_congr hev).1
  rw [hdF,hdG,hT0] at hd
  have hder : deriv (blaschke (-a)) 0=((1-‖a‖^2 : ℝ) : ℂ) := by
    rw [(hasDerivAt_blaschke hna (by simp)).deriv]
    simp only [map_neg,neg_mul_neg,mul_zero,sub_zero,one_pow,div_one,Complex.mul_conj']
    push_cast
    rfl
  rw [hder] at hd
  have hn := congrArg (fun z : ℂ => ‖z‖^2) hd
  have hapos : 0≤1-‖a‖^2 := by nlinarith [norm_nonneg a]
  simp only [norm_mul,mul_pow,Complex.norm_real,Real.norm_of_nonneg hapos] at hn
  have hρ := grp25c_density hS hG0
  refine ⟨hFa,?_⟩
  rw [hFval]
  calc
    _ = (‖dz F a‖^2*(1-‖a‖^2)^2)/(1-‖S (G 0)‖^2)^2 := by ring
    _ = (‖deriv S (G 0)‖^2/(1-‖S (G 0)‖^2)^2)*‖dz G 0‖^2 := by rw [hn]; ring
    _ = _ := by rw [hρ]; ring

/-- The conformal pullback is a genuine L∞ representative, with its essential norm controlled. -/
theorem grp25c_pullback_memLp (μ : LinfStar) {T : ℂ → ℂ} {p q : ℂ}
    (hTm : Measurable T)
    (hT : IsConformalOnto T (unitDiscExterior\{p}) (unitDiscExterior\{q})) :
    MemLp (fun z => μ (T z)*(conj (deriv T z)/deriv T z)) ∞ (volume.restrict unitDiscExterior) ∧
      ‖toLinf (fun z => μ (T z)*(conj (deriv T z)/deriv T z))‖≤‖μ‖ := by
  have hU : IsOpen (unitDiscExterior\{p}) := bc_hEo.sdiff isClosed_singleton
  have hK := isKQC_one_of_conformal hU hT
  have hsub : T '' (unitDiscExterior\{p})⊆unitDiscExterior := by
    rw [hT.2.2]
    exact sdiff_subset
  have hrestr : volume.restrict (unitDiscExterior\{p})=volume.restrict unitDiscExterior :=
    Measure.restrict_congr_set (sdiff_null_ae_eq_self (measure_singleton p))
  have hqp : Measure.QuasiMeasurePreserving T (volume.restrict (unitDiscExterior\{p}))
      (volume.restrict unitDiscExterior) := by
    refine ⟨hTm,Measure.AbsolutelyContinuous.mk (fun s hs hs0 => ?_)⟩
    rw [Measure.map_apply hTm hs]
    exact measure_eq_zero_iff_ae_notMem.mpr
      (s23_c2_ae_pullback hK hsub (measure_eq_zero_iff_ae_notMem.mp hs0))
  have hμm := (Lp.aestronglyMeasurable μ).comp_quasiMeasurePreserving hqp
  have hdm : AEStronglyMeasurable (deriv T) (volume.restrict (unitDiscExterior\{p})) :=
    (hT.1.deriv hU).continuousOn.aestronglyMeasurable hU.measurableSet
  have hmeas : AEStronglyMeasurable (fun z => μ (T z)*(conj (deriv T z)/deriv T z))
      (volume.restrict (unitDiscExterior\{p})) :=
    (hμm.aemeasurable.mul
      ((Complex.continuous_conj.comp_aestronglyMeasurable hdm).aemeasurable.div hdm.aemeasurable)).aestronglyMeasurable
  rw [hrestr] at hmeas
  have hbound : ∀ᵐ z ∂(volume.restrict unitDiscExterior),
      ‖μ (T z)*(conj (deriv T z)/deriv T z)‖≤‖μ‖ := by
    have hb := s23_c2_ae_pullback hK hsub (LinfStar_ae_norm_le μ)
    rw [hrestr] at hb
    filter_upwards [hb] with z hz
    by_cases hd : deriv T z=0
    · simpa only [hd,map_zero,zero_div,mul_zero,norm_zero] using norm_nonneg μ
    · simpa only [norm_mul,norm_div,Complex.norm_conj,div_self (norm_ne_zero_iff.mpr hd),mul_one] using hz
  exact ⟨memLp_top_of_bound hmeas ‖μ‖ hbound,norm_toLinf_le_of_ae_bound (norm_nonneg μ) hbound⟩

theorem grp25c_den {a z : ℂ} (ha : a≠0) (hz : z≠(conj a)⁻¹) : 1-conj a*z≠0 := by
  intro he
  apply hz
  have hc : conj a≠0 := (map_ne_zero _).mpr ha
  apply (mul_left_cancel₀ hc)
  rw [mul_inv_cancel₀ hc]
  linear_combination -he

theorem grp25c_deriv {a z : ℂ} (hd : 1-conj a*z≠0) :
    HasDerivAt (blaschke a) ((1-a*conj a)/(1-conj a*z)^2) z := by
  have hh := ((hasDerivAt_id z).sub_const a).div
    (((hasDerivAt_id z).const_mul (conj a)).const_sub 1) hd
  convert hh using 1 <;> first | rfl | (dsimp; ring)

theorem grp25c_norm {a z : ℂ} (ha : ‖a‖<1) (hd : 1-conj a*z≠0) :
    ‖blaschke a z‖^2-1=‖deriv (blaschke a) z‖*(‖z‖^2-1) := by
  have hapos : 0≤1-‖a‖^2 := by nlinarith [norm_nonneg a]
  have hn : ‖1-a*conj a‖=1-‖a‖^2 := by
    rw [Complex.mul_conj']
    norm_cast
    exact Real.norm_of_nonneg hapos
  rw [(grp25c_deriv hd).deriv,norm_div,norm_pow,hn]
  have hk := normSq_blaschke_key a z
  simp only [Complex.normSq_eq_norm_sq] at hk
  rw [blaschke,norm_div,div_pow]
  have hdn : ‖1-conj a*z‖^2≠0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hd)
  have hr (A B C D : ℝ) (hD : D≠0) (h : D-A=(1-B)*(1-C)) :
      A/D-1=(1-C)/D*(B-1) := by
    field_simp
    nlinarith only [h]
  exact hr _ _ _ _ hdn hk

theorem grp25c_exterior {a : ℂ} (ha : ‖a‖<1) (ha0 : a≠0) :
    (conj a)⁻¹∈unitDiscExterior ∧
    IsConformalOnto (blaschke a) (unitDiscExterior\{(conj a)⁻¹})
      (unitDiscExterior\{-(conj a)⁻¹}) ∧
    ∀ z∈unitDiscExterior\{(conj a)⁻¹},
      ‖blaschke a z‖^2-1=‖deriv (blaschke a) z‖*(‖z‖^2-1) := by
  have hc : conj a≠0 := (map_ne_zero _).mpr ha0
  have hdet : 1-conj a*a≠0 := by simpa only [mul_comm] using one_sub_mul_conj_ne_zero ha
  have hbn : ‖-a‖<1 := by simpa using ha
  have hdata {b z : ℂ} (hb : ‖b‖<1) (hb0 : b≠0)
      (hz : z∈unitDiscExterior\{(conj b)⁻¹}) :
      blaschke b z∈unitDiscExterior\{-(conj b)⁻¹} := by
    have hd := grp25c_den hb0 hz.2
    have hder : 0<‖deriv (blaschke b) z‖ := by
      rw [(grp25c_deriv hd).deriv]
      exact norm_pos_iff.mpr (div_ne_zero (one_sub_mul_conj_ne_zero hb) (pow_ne_zero 2 hd))
    have he := grp25c_norm hb hd
    have hz1 : 1<‖z‖ := hz.1
    have hpos : 0<‖deriv (blaschke b) z‖*(‖z‖^2-1) := mul_pos hder (by nlinarith)
    refine ⟨by change 1<‖blaschke b z‖; nlinarith [norm_nonneg (blaschke b z)],?_⟩
    intro hh
    have hbconj : conj b≠0 := (map_ne_zero _).mpr hb0
    have hplus := wpT_one_add (y := b) (v := z) hd
    change 1+conj b*blaschke b z=(1-conj b*b)/(1-conj b*z) at hplus
    rw [hh,mul_neg,mul_inv_cancel₀ hbconj] at hplus
    have hn : (1-conj b*b)/(1-conj b*z)≠0 :=
      div_ne_zero (by simpa only [mul_comm] using one_sub_mul_conj_ne_zero hb) hd
    exact hn (by linear_combination -hplus)
  refine ⟨?_,⟨?_,?_,?_⟩,fun z hz => grp25c_norm ha (grp25c_den ha0 hz.2)⟩
  · change 1<‖(conj a)⁻¹‖
    rw [norm_inv,Complex.norm_conj]
    exact (one_lt_inv₀ (norm_pos_iff.mpr ha0)).mpr ha
  · intro z hz
    exact (grp25c_deriv (grp25c_den ha0 hz.2)).differentiableAt.differentiableWithinAt
  · intro z hz w hw he
    have hzI := wpV_wpT hdet (grp25c_den ha0 hz.2)
    have hwI := wpV_wpT hdet (grp25c_den ha0 hw.2)
    change wpV a (blaschke a z)=z at hzI
    change wpV a (blaschke a w)=w at hwI
    rw [← hzI,← hwI,he]
  · ext w
    constructor
    · rintro ⟨z,hz,rfl⟩
      exact hdata ha ha0 hz
    · intro hw
      have hw' : w∈unitDiscExterior\{(conj (-a))⁻¹} := by simpa only [map_neg,inv_neg] using hw
      have hv := hdata hbn (neg_ne_zero.mpr ha0) hw'
      refine ⟨blaschke (-a) w,by simpa only [map_neg,inv_neg,neg_neg] using hv,?_⟩
      have hd : 1+conj a*w≠0 := by simpa only [map_neg,neg_mul,sub_neg_eq_add] using grp25c_den (neg_ne_zero.mpr ha0) hw'.2
      simpa only [wpT,wpV,blaschke,map_neg,sub_neg_eq_add,neg_mul] using wpT_wpV hdet hd

/-- Reflection and its derivative factor commute with a disk Blaschke automorphism. -/
theorem grp25c_reflection {a z : ℂ} (ha : ‖a‖<1) (ha0 : a≠0)
    (hz : z∈unitDisc) (hz0 : z≠0) (hza : z≠a) :
    blaschke a (refl z)=refl (blaschke a z) ∧
    (deriv (blaschke a) (refl z)/conj (deriv (blaschke a) (refl z)))*z^2/(conj z)^2=
      (blaschke a z)^2/(conj (blaschke a z))^2*
        (conj (deriv (blaschke a) z)/deriv (blaschke a) z) := by
  have hd := blaschke_den_ne_zero ha (mem_ball_zero_iff.mp hz)
  have hrp : refl z≠(conj a)⁻¹ := fun he => hza (by
    simpa only [conj_conj] using congrArg conj (inv_injective he))
  have hdR := grp25c_den ha0 hrp
  have hcz : conj z≠0 := (map_ne_zero _).mpr hz0
  have hsub : z-a≠0 := sub_ne_zero.mpr hza
  have hcsub : conj z-conj a≠0 := sub_ne_zero.mpr (fun he => hza (by
    simpa only [conj_conj] using congrArg conj he))
  have hcd : 1-a*conj z≠0 := by
    simpa only [map_sub,map_one,map_mul,conj_conj] using (map_ne_zero (starRingEnd ℂ)).mpr hd
  have hdet := one_sub_mul_conj_ne_zero ha
  have hdet' : 1-conj a*a≠0 := by simpa only [mul_comm] using hdet
  constructor
  · simp only [blaschke,refl,map_div₀,map_sub,map_one,map_mul,conj_conj]
    field_simp
    <;> ring
  · rw [(grp25c_deriv hd).deriv,(grp25c_deriv hdR).deriv]
    simp only [blaschke,refl,map_div₀,map_sub,map_one,map_mul,map_pow,map_inv₀,conj_conj]
    field_simp
    <;> ring

/-- The exterior coefficient pullback also gives the correct reflected coefficient inside the disk. -/
theorem grp25c_ext_pullback (μ : LinfStar) {a : ℂ} (ha : ‖a‖<1) (ha0 : a≠0) :
    let μ' := toLinf (fun z => μ (blaschke a z)*(conj (deriv (blaschke a) z)/deriv (blaschke a) z))
    ∀ᵐ z ∂(volume.restrict unitDisc),
      extA μ' z=extA μ (blaschke a z)*(conj (deriv (blaschke a) z)/deriv (blaschke a) z) := by
  dsimp only
  have hdata := grp25c_exterior ha ha0
  have hmeas : Measurable (blaschke a) := by unfold blaschke; fun_prop
  have hp := (grp25c_pullback_memLp μ hmeas hdata.2.1).1
  have he := bc_toLinf_ae hp
  have he' := ae_refl ((ae_restrict_iff' bc_hEo.measurableSet).mp he)
  filter_upwards [ae_restrict_of_ae he',ae_restrict_of_ae (volume.ae_ne (0 : ℂ)),
    ae_restrict_of_ae (volume.ae_ne a),ae_restrict_mem (show MeasurableSet unitDisc from measurableSet_ball)]
    with z hzR hz0 hza hz
  have hzn : ‖z‖<1 := mem_ball_zero_iff.mp hz
  have hTn : ‖blaschke a z‖<1 := blaschke_mem_unitDisc ha hzn
  have hRe := hzR ((refl_mem_exterior_iff hz0).mpr hz)
  have hRF := grp25c_reflection ha ha0 hz hz0 hza
  simp only [extA,if_neg (not_lt.mpr hzn.le),if_pos hzn,
    if_neg (not_lt.mpr hTn.le),if_pos hTn,hRe,map_mul,map_div₀,conj_conj]
  rw [hRF.1]
  calc
    _ = conj (μ (refl (blaschke a z)))*
        ((deriv (blaschke a) (refl z)/conj (deriv (blaschke a) (refl z)))*z^2/(conj z)^2) := by ring
    _ = _ := by rw [hRF.2]; ring

/-- Disk Stoilow comparison, requiring only the actual reflected pullback identity. -/
theorem grp25c_comparison {μ ν : LinfStar} (hμ : μ∈LinfStarBall) (hν : ν∈LinfStarBall)
    {b : ℂ} (hb : ‖b‖<1)
    (hcov : ∀ᵐ z ∂(volume.restrict unitDisc),
      extA ν z=extA μ (blaschke b z)*(conj (deriv (blaschke b) z)/deriv (blaschke b) z)) :
    ∃ S : ℂ → ℂ, IsConformalOnto S unitDisc unitDisc ∧ wA ν 0∈unitDisc ∧
      EqOn (fun z => wA μ (blaschke b z)) (fun z => S (wA ν z)) unitDisc := by
  have hD : IsOpen unitDisc := isOpen_ball
  obtain ⟨K,hK,himg⟩ := wpcv_g_disc hμ
  obtain ⟨L,hL,hνimg⟩ := wpcv_g_disc hν
  have hT := isConformalOnto_blaschke hb
  have hTK := isKQC_one_of_conformal hD hT
  have hFT := thm7_1_comp hTK hK (by rw [hT.2.2])
  have hpull := s23_c2_ae_pullback hTK (by rw [hT.2.2]) (D := unitDisc)
    (ae_restrict_of_ae (bc_wA_ae hμ))
  have hae : ∀ᵐ z ∂(volume.restrict unitDisc),
      complexDilatation (wA ν) z=complexDilatation (wA μ ∘ blaschke b) z := by
    filter_upwards [ae_restrict_of_ae (bc_wA_ae hν),hpull,hcov,ae_restrict_mem hD.measurableSet]
      with z hzν hzμ hzCov hz
    rw [hzν.2.2.1,complexDilatation_comp_conformal_right
      (hT.1.differentiableAt (hD.mem_nhds hz))
      (deriv_ne_zero_of_injOn hD hT.1 hT.2.1 hz) hzμ.1,hzμ.2.2.1]
    exact hzCov
  obtain ⟨S,hS,he⟩ := grp_stoilow hD ⟨L,hL⟩ ⟨1*K,hFT⟩ hae
  rw [hνimg,image_comp,hT.2.2,himg] at hS
  refine ⟨S,hS,?_,fun z hz => he z hz⟩
  rw [← hνimg]
  exact ⟨0,mem_ball_self one_pos,rfl⟩

theorem grp25_cov {μ : LinfStar} (hμ : μ ∈ harmonicBeltrami) (hμ1 : ‖μ‖ < 1) {a : ℂ} (ha : a ∈ unitDisc) :
    ∃ μ' ∈ harmonicBeltrami, ‖μ'‖ ≤ ‖μ‖ ∧
      (ContDiffAt ℝ 1 (wA μ') 0 →
        ContDiffAt ℝ 1 (wA μ) a ∧
          ‖dz (wA μ) a‖ ^ 2 / (1 - ‖wA μ a‖ ^ 2) ^ 2 * (1 - ‖a‖ ^ 2) ^ 2 =
            ‖dz (wA μ') 0‖ ^ 2 / (1 - ‖wA μ' 0‖ ^ 2) ^ 2) := by
  by_cases ha0 : a=0
  · subst a
    exact ⟨μ,hμ,le_rfl,fun hh => ⟨hh,by simp⟩⟩
  have hna : ‖-a‖<1 := by simpa only [norm_neg] using mem_ball_zero_iff.mp ha
  have hna0 : -a≠0 := neg_ne_zero.mpr ha0
  let μ' := toLinf (fun z => μ (blaschke (-a) z)*
    (conj (deriv (blaschke (-a)) z)/deriv (blaschke (-a)) z))
  have hdata := grp25c_exterior hna hna0
  have hTm : Measurable (blaschke (-a)) := by unfold blaschke; fun_prop
  have hnorm : ‖μ'‖≤‖μ‖ := (grp25c_pullback_memLp μ hTm hdata.2.1).2
  have hμ'h : μ'∈harmonicBeltrami := tv_pullback_harmonic hμ hdata.1 hdata.2.1 hdata.2.2
  have hμB : μ∈LinfStarBall := by simpa only [LinfStarBall,mem_ball_zero_iff] using hμ1
  have hμ'B : μ'∈LinfStarBall := by simpa only [LinfStarBall,mem_ball_zero_iff] using hnorm.trans_lt hμ1
  obtain ⟨S,hS,hG0,he⟩ := grp25c_comparison hμB hμ'B hna (grp25c_ext_pullback μ hna hna0)
  exact ⟨μ',hμ'h,hnorm,fun hh => grp25c_transport ha hS hG0 he hh⟩

end TakhtajanTeo
