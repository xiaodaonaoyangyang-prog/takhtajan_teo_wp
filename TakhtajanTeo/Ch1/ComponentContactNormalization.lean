import TakhtajanTeo.Ch1.ComponentContactJet
import TakhtajanTeo.Ch1.ComponentBlowupNormalization

/-! Actual two-jet normalization of the relative conformal map and its
contact sphere value. Relative-jet names from the blowup module are not
redefined; all ratios are explicit. -/
open Complex Set Metric Filter Topology
open scoped ComplexConjugate Classical Real
noncomputable section
namespace TakhtajanTeo
open LiZhongQC

-- N1
theorem ccn_second_chain {F f : ℂ → ℂ} {a : ℂ}
    (hf : AnalyticAt ℂ f a) (hF : AnalyticAt ℂ F (f a)) :
    deriv (deriv (F ∘ f)) a = deriv (deriv F) (f a)*(deriv f a)^2+
      deriv F (f a)*deriv (deriv f) a := by
  have he : deriv (F ∘ f) =ᶠ[𝓝 a] fun w => deriv F (f w)*deriv f w := by
    filter_upwards [hf.eventually_analyticAt,hf.continuousAt.eventually hF.eventually_analyticAt] with w hfw hFw
    exact deriv_comp w hFw.differentiableAt hfw.differentiableAt
  have h1 : HasDerivAt (fun w => deriv F (f w))
      (deriv (deriv F) (f a)*deriv f a) a :=
    hF.deriv.differentiableAt.hasDerivAt.comp a hf.differentiableAt.hasDerivAt
  have h2 := hf.deriv.differentiableAt.hasDerivAt
  rw [he.deriv_eq]
  convert (h1.mul h2).deriv using 1
  ring

-- N2
theorem ccn_affine_jets (f : ℂ → ℂ) (a α b c : ℂ) :
    deriv (fun t => (f (a+α*t)-c)/b) 0 = α*deriv f a/b ∧
    deriv (deriv (fun t => (f (a+α*t)-c)/b)) 0 = α^2*deriv (deriv f) a/b := by
  have hpre : ∀ (φ : ℂ → ℂ) (z : ℂ),
      deriv (fun t => φ (a+α*t)) z = α*deriv φ (a+α*z) := by
    intro φ z
    simpa only [deriv_comp_const_add,smul_eq_mul] using
      deriv_comp_mul_left α (fun t => φ (a+t)) z
  have hd : ∀ z : ℂ, deriv (fun t => (f (a+α*t)-c)/b) z = α*deriv f (a+α*z)/b := by
    intro z
    rw [deriv_div_const,deriv_sub_const,hpre f z]
  refine ⟨by simpa only [mul_zero,add_zero] using hd 0,?_⟩
  rw [show deriv (fun t => (f (a+α*t)-c)/b) = (fun z => α*deriv f (a+α*z)/b) from funext hd,
    deriv_div_const,deriv_const_mul_field,hpre (deriv f) 0]
  simp only [mul_zero,add_zero]
  ring

-- N3
theorem ccn_normalized_jets {μ : LinfStar} (hμ : μ ∈ LinfStarBall)
    (e : ℂ ≃ₜ ℂ) (he : EqOn e (fsans μ) unitDisc) {a : ℂ}
    (ha0 : 0 < ‖a‖) (ha1 : ‖a‖ < 1) :
    let b := e (cbl_source a 1)-e a
    b ≠ 0 ∧ deriv (cbl_normalized e a) 0 ≠ 0 ∧
      deriv (cbl_normalized e a) 0 = cbl_scale a*deriv (fsans μ) a/b ∧
      deriv (deriv (cbl_normalized e a)) 0 = (cbl_scale a)^2*deriv (deriv (fsans μ)) a/b := by
  let b := e (cbl_source a 1)-e a
  have ha : a ∈ unitDisc := mem_ball_zero_iff.mpr ha1
  have hgerm : (e : ℂ → ℂ) =ᶠ[𝓝 a] fsans μ := by
    filter_upwards [isOpen_ball.mem_nhds ha] with z hz
    exact he hz
  have hj := ccn_affine_jets (e : ℂ → ℂ) a (cbl_scale a) b (e a)
  change deriv (cbl_normalized e a) 0 = cbl_scale a*deriv (e : ℂ → ℂ) a/b ∧
    deriv (deriv (cbl_normalized e a)) 0 = (cbl_scale a)^2*deriv (deriv (e : ℂ → ℂ)) a/b at hj
  rw [hgerm.deriv_eq,hgerm.deriv.deriv_eq] at hj
  have hb : b ≠ 0 := cbl_image_difference_ne_zero e ha0 ha1
  have hfd := deriv_ne_zero_of_injOn isOpen_ball (S2C.s2c_conf_f hμ).1 (S2C.s2c_conf_f hμ).2.1 ha
  have hn : deriv (cbl_normalized e a) 0 ≠ 0 := by
    rw [hj.1]
    exact div_ne_zero (mul_ne_zero (cbl_scale_ne_zero ha0 ha1) hfd) hb
  exact ⟨hb,hn,hj.1,hj.2⟩

-- N4
theorem ccn_transition_jets {μ ν : LinfStar} (hμ : μ ∈ LinfStarBall) (hν : ν ∈ LinfStarBall)
    (eμ eν : ℂ ≃ₜ ℂ) (heμ : EqOn eμ (fsans μ) unitDisc) (heν : EqOn eν (fsans ν) unitDisc)
    {a : ℂ} (ha0 : 0 < ‖a‖) (ha1 : ‖a‖ < 1) :
    let bμ := eμ (cbl_source a 1)-eμ a
    let bν := eν (cbl_source a 1)-eν a
    let f := cbl_normalized eμ a
    let g := cbl_normalized eν a
    let v := fsans μ a
    bμ ≠ 0 ∧ bν ≠ 0 ∧ deriv f 0 ≠ 0 ∧ deriv g 0 ≠ 0 ∧
      deriv (crs_transition μ ν) v = (bν/bμ)*(deriv g 0/deriv f 0) ∧
      deriv (deriv (crs_transition μ ν)) v = (bν/bμ^2)*
        ((deriv (deriv g) 0*deriv f 0-deriv g 0*deriv (deriv f) 0)/(deriv f 0)^3) := by
  let bμ := eμ (cbl_source a 1)-eμ a
  let bν := eν (cbl_source a 1)-eν a
  let F := crs_transition μ ν
  let v := fsans μ a
  obtain ⟨hbμ,hfn,hf1,hf2⟩ := ccn_normalized_jets hμ eμ heμ ha0 ha1
  obtain ⟨hbν,hgn,hg1,hg2⟩ := ccn_normalized_jets hν eν heν ha0 ha1
  have ha : a ∈ unitDisc := mem_ball_zero_iff.mpr ha1
  have hμc := S2C.s2c_conf_f hμ
  have hFa : AnalyticAt ℂ F v :=
    (crs_conformal hμ hν).1.analyticAt ((hμc.isOpen isOpen_ball).mem_nhds ⟨a,ha,rfl⟩)
  have hfa := hμc.1.analyticAt (isOpen_ball.mem_nhds ha)
  have he : (F ∘ fsans μ) =ᶠ[𝓝 a] fsans ν := by
    filter_upwards [isOpen_ball.mem_nhds ha] with w hw
    change fsans ν (Function.invFunOn (fsans μ) unitDisc (fsans μ w)) = fsans ν w
    rw [hμc.2.1.leftInvOn_invFunOn hw]
  have hc1 : deriv (fsans ν) a = deriv F v*deriv (fsans μ) a := by
    have ht := deriv_comp a hFa.differentiableAt hfa.differentiableAt
    rwa [he.deriv_eq] at ht
  have hc2 : deriv (deriv (fsans ν)) a =
      deriv (deriv F) v*(deriv (fsans μ) a)^2+deriv F v*deriv (deriv (fsans μ)) a := by
    have ht := ccn_second_chain hfa hFa
    rwa [he.deriv.deriv_eq] at ht
  have hdf := deriv_ne_zero_of_injOn isOpen_ball hμc.1 hμc.2.1 ha
  have hα := cbl_scale_ne_zero ha0 ha1
  have hfirst : deriv F v = deriv (fsans ν) a/deriv (fsans μ) a :=
    (eq_div_iff hdf).mpr hc1.symm
  have hsecond : deriv (deriv F) v =
      (deriv (deriv (fsans ν)) a*deriv (fsans μ) a-
        deriv (fsans ν) a*deriv (deriv (fsans μ)) a)/(deriv (fsans μ) a)^3 := by
    apply (eq_div_iff (pow_ne_zero 3 hdf)).mpr
    linear_combination -(deriv (fsans μ) a)*hc2+deriv (deriv (fsans μ)) a*hc1
  refine ⟨hbμ,hbν,hfn,hgn,?_,?_⟩
  · change deriv F v = _
    rw [hfirst,hf1,hg1]
    field_simp
  · change deriv (deriv F) v = _
    rw [hsecond,hf1,hf2,hg1,hg2]
    field_simp

-- N5: consumes any already chosen actual pair without selecting a new one.
theorem ccn_contact_normalized {μ ν : LinfStar} (hμ : μ ∈ LinfStarBall) (hν : ν ∈ LinfStarBall)
    (eμ eν : ℂ ≃ₜ ℂ) (heμ : EqOn eμ (fsans μ) unitDisc) (heν : EqOn eν (fsans ν) unitDisc)
    {a : ℂ} (ha0 : 0 < ‖a‖) (ha1 : ‖a‖ < 1) {A B h : ℂ → ℂ}
    (hA : DifferentiableOn ℂ A (fsans μ '' unitDisc))
    (hB : DifferentiableOn ℂ B (fsans μ '' unitDisc))
    (hW : ∀ v ∈ fsans μ '' unitDisc, A v*deriv B v-B v*deriv A v = 1)
    (he : ∀ v ∈ fsans μ '' unitDisc, (crs_transition μ ν v : ExtPlane) = t203_ratio (A v) (B v))
    {u : ℂ} (hu : h u = fsans μ a) :
    let bμ := eμ (cbl_source a 1)-eμ a
    let bν := eν (cbl_source a 1)-eν a
    let f := cbl_normalized eμ a
    let g := cbl_normalized eν a
    let v := fsans μ a
    let x := (u-v)/bμ
    let p := deriv g 0/deriv f 0
    let q := (deriv (deriv g) 0*deriv f 0-deriv g 0*deriv (deriv f) 0)/(deriv f 0)^3
    1-x*q/(2*p) ≠ 0 →
      B (h u)+(u-h u)*deriv B (h u) ≠ 0 ∧
      cnl_sphere A B h u = ((crs_transition μ ν v+bν*(p*x/(1-x*q/(2*p))) : ℂ) : ExtPlane) := by
  let bμ := eμ (cbl_source a 1)-eμ a
  let bν := eν (cbl_source a 1)-eν a
  let f := cbl_normalized eμ a
  let g := cbl_normalized eν a
  let v := fsans μ a
  let x := (u-v)/bμ
  let p := deriv g 0/deriv f 0
  let q := (deriv (deriv g) 0*deriv f 0-deriv g 0*deriv (deriv f) 0)/(deriv f 0)^3
  change 1-x*q/(2*p) ≠ 0 → _
  intro hjet
  obtain ⟨hbμ,hbν,hfn,hgn,hfirst,hsecond⟩ := ccn_transition_jets hμ hν eμ eν heμ heν ha0 ha1
  change bμ ≠ 0 at hbμ
  change bν ≠ 0 at hbν
  change deriv (crs_transition μ ν) v = (bν/bμ)*p at hfirst
  change deriv (deriv (crs_transition μ ν)) v = (bν/bμ^2)*q at hsecond
  have hp : p ≠ 0 := div_ne_zero hgn hfn
  have hfactor : 1-(u-v)*deriv (deriv (crs_transition μ ν)) v/(2*deriv (crs_transition μ ν) v) =
      1-x*q/(2*p) := by
    rw [hfirst,hsecond]
    dsimp only [x]
    field_simp [hbμ,hbν,hp]
    <;> ring
  have hactual : 1-(u-h u)*deriv (deriv (crs_transition μ ν)) (h u)/(2*deriv (crs_transition μ ν) (h u)) ≠ 0 := by
    rw [hu]
    change 1-(u-v)*deriv (deriv (crs_transition μ ν)) v/(2*deriv (crs_transition μ ν) v) ≠ 0
    rwa [hfactor]
  have hΩ := (S2C.s2c_conf_f hμ).isOpen isOpen_ball
  have hv : h u ∈ fsans μ '' unitDisc := by
    rw [hu]
    exact ⟨a,mem_ball_zero_iff.mpr ha1,rfl⟩
  obtain ⟨hmap,hcontact⟩ := ccj_contact hΩ hA hB hW he hv hactual
  have hval : crs_transition μ ν v+(u-v)*deriv (crs_transition μ ν) v/
      (1-(u-v)*deriv (deriv (crs_transition μ ν)) v/(2*deriv (crs_transition μ ν) v)) =
      crs_transition μ ν v+bν*(p*x/(1-x*q/(2*p))) := by
    rw [hfactor,hfirst]
    dsimp only [x]
    ring
  refine ⟨hmap,?_⟩
  calc
    cnl_sphere A B h u = ((crs_transition μ ν v+(u-v)*deriv (crs_transition μ ν) v/
        (1-(u-v)*deriv (deriv (crs_transition μ ν)) v/(2*deriv (crs_transition μ ν) v)) : ℂ) : ExtPlane) := by
      simpa only [hu] using hcontact
    _ = _ := congrArg (fun w : ℂ => (w : ExtPlane)) hval

end TakhtajanTeo
