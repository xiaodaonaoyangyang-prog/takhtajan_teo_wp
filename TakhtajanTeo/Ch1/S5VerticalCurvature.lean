import TakhtajanTeo.Ch1.S5FiberGeometry
import TakhtajanTeo.Ch1.ConformalLaplacian
import TakhtajanTeo.Ch1.S7_Curvature
import TakhtajanTeo.Ch1.TCurveLocalRepresentatives
import Mathlib.Analysis.InnerProductSpace.Harmonic.Constructions

/-! Mixed derivatives of the actual fiber hyperbolic metric. -/
open Complex Set MeasureTheory Metric Filter Topology InnerProductSpace
open scoped ENNReal ComplexConjugate Classical Real
noncomputable section
namespace TakhtajanTeo
open LiZhongQC

theorem s5vc_mixed_laplacian {f : ℂ → ℂ} {z : ℂ} (hf : ContDiffAt ℝ 2 f z) :
    dz (dzbar f) z = Laplacian.laplacian f z / 4 := by
  let D := fderiv ℝ (fderiv ℝ f) z
  let L1 : ℂ →L[ℝ] ℂ := (ContinuousLinearMap.apply ℝ ℂ 1).comp D
  let LI : ℂ →L[ℝ] ℂ := (ContinuousLinearMap.apply ℝ ℂ I).comp D
  have hD : HasFDerivAt (fderiv ℝ f) D z :=
    ((hf.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero).hasFDerivAt
  have h1 : HasFDerivAt (fun y => fderiv ℝ f y 1) L1 z := by
    convert! (ContinuousLinearMap.apply ℝ ℂ 1 : (ℂ →L[ℝ] ℂ) →L[ℝ] ℂ).hasFDerivAt.comp z hD using 1
  have hI : HasFDerivAt (fun y => fderiv ℝ f y I) LI z := by
    convert! (ContinuousLinearMap.apply ℝ ℂ I : (ℂ →L[ℝ] ℂ) →L[ℝ] ℂ).hasFDerivAt.comp z hD using 1
  have hb : HasFDerivAt (dzbar f) ((1 / 2 : ℂ) • (L1 + I • LI)) z := by
    convert! ((h1.add (hI.const_mul I)).const_mul (1 / 2 : ℂ)) using 1
    funext y
    dsimp [dzbar]
    ring
  have hs : D 1 I = D I 1 := (hf.isSymmSndFDerivAt (by norm_num)) 1 I
  rw [laplacian_eq_iteratedFDeriv_complexPlane]
  simp only [iteratedFDeriv_two_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
  unfold dz
  rw [hb.fderiv]
  change ((1 / 2 : ℂ) * (D 1 1 + I * D 1 I) - I * ((1 / 2 : ℂ) * (D I 1 + I * D I I))) / 2 =
    (D 1 1 + D I I) / 4
  rw [hs]
  linear_combination (-(D I I) / 4) * I_sq

theorem s5vc_mixed_log_norm {f : ℂ → ℂ} {z : ℂ} (hf : AnalyticAt ℂ f z) (hne : f z ≠ 0) :
    dz (dzbar (fun w => (Real.log ‖f w‖ : ℂ))) z = 0 := by
  have hh := (hf.harmonicAt_log_norm hne).comp_CLM Complex.ofRealCLM
  change HarmonicAt (fun w => (Real.log ‖f w‖ : ℂ)) z at hh
  rw [s5vc_mixed_laplacian hh.1, hh.2.self_of_nhds]
  simp

theorem s5vc_disk_log_mixed {z : ℂ} (hz : z ∈ unitDisc) :
    dz (dzbar (fun w => -Complex.log (1 - w * conj w))) z = 1 / (1 - z * conj z) ^ 2 := by
  have hq (w : ℂ) : DifferentiableAt ℝ (fun v : ℂ => 1 - v * conj v) w := by fun_prop
  have hslit (w : ℂ) (hw : w ∈ unitDisc) : 1 - w * conj w ∈ slitPlane := by
    have hp : 0 < 1 - ‖w‖ ^ 2 := by
      have hn := mem_ball_zero_iff.mp hw
      nlinarith [norm_nonneg w]
    have he : (1 : ℂ) - w * conj w = ((1 - ‖w‖ ^ 2 : ℝ) : ℂ) := by
      simp [Complex.mul_conj, Complex.normSq_eq_norm_sq]
    rw [he]
    exact Complex.ofReal_mem_slitPlane.mpr hp
  have hfirst (w : ℂ) (hw : w ∈ unitDisc) :
      dzbar (fun v => -Complex.log (1 - v * conj v)) w = w / (1 - w * conj w) := by
    have hlog := Complex.differentiableAt_log (hslit w hw)
    have hchain := (eq6_5 (hq w) hlog).2
    change dzbar (fun v => Complex.log (1 - v * conj v)) w = _ at hchain
    rw [Complex.deriv_log (hslit w hw), wp_dzbar_disk_factor] at hchain
    have hneg : dzbar (fun v => -Complex.log (1 - v * conj v)) w =
        -dzbar (fun v => Complex.log (1 - v * conj v)) w := by
      convert! wp_dzbar_const_mul ((hlog.restrictScalars ℝ).comp w (hq w)) (-1) using 1 <;> simp <;> rfl
    rw [hneg, hchain]
    ring
  have hev : dzbar (fun v => -Complex.log (1 - v * conj v)) =ᶠ[𝓝 z]
      (fun w => w / (1 - w * conj w)) := by
    filter_upwards [isOpen_ball.mem_nhds hz] with w hw
    exact hfirst w hw
  have he : dz (dzbar (fun v => -Complex.log (1 - v * conj v))) z =
      dz (fun w => w / (1 - w * conj w)) z := by
    unfold dz
    rw [hev.fderiv_eq]
  have hid : dz (fun w : ℂ => w) z = 1 := rhoVar_dz_id z
  rw [he, (t203_dz_div (N := fun w : ℂ => w) differentiableAt_id (hq z) (wp_disk_factor_ne_zero hz)).1,
    wp_dz_disk_factor, hid]
  ring

theorem s5vc_mixed_congr {f g : ℂ → ℂ} {z : ℂ} (h : f =ᶠ[𝓝 z] g) :
    dz (dzbar f) z = dz (dzbar g) z := by
  have hb : dzbar f =ᶠ[𝓝 z] dzbar g := by
    filter_upwards [h.fderiv (𝕜 := ℝ)] with w hw
    simp only [dzbar, hw]
  unfold dz
  rw [hb.fderiv_eq]

theorem s5vc_mixed_add {f g : ℂ → ℂ} {z : ℂ}
    (hf : ContDiffAt ℝ 2 f z) (hg : ContDiffAt ℝ 2 g z) :
    dz (dzbar (fun w => f w + g w)) z = dz (dzbar f) z + dz (dzbar g) z := by
  change dz (dzbar (f + g)) z = _
  have hs : ContDiffAt ℝ 2 (f + g) z := by convert! hf.add hg using 1
  rw [s5vc_mixed_laplacian hs, hf.laplacian_add hg,
    s5vc_mixed_laplacian hf, s5vc_mixed_laplacian hg]
  ring

theorem s5vc_mixed_const_mul {f : ℂ → ℂ} {z : ℂ} (hf : ContDiffAt ℝ 2 f z) (c : ℂ) :
    dz (dzbar (fun w => c * f w)) z = c * dz (dzbar f) z := by
  change dz (dzbar (c • f)) z = _
  have hs : ContDiffAt ℝ 2 (c • f) z := by convert! hf.const_smul c using 1
  rw [s5vc_mixed_laplacian hs, laplacian_smul c hf, s5vc_mixed_laplacian hf]
  simp only [smul_eq_mul]
  ring

theorem s5vc_disk_potential_analytic {z : ℂ} (hz : z ∈ unitDisc) :
    AnalyticAt ℝ (fun w : ℂ => (-Real.log (1 - ‖w‖ ^ 2) : ℂ)) z := by
  have hp : 0 < 1 - ‖z‖ ^ 2 := by
    have hn := mem_ball_zero_iff.mp hz
    nlinarith [norm_nonneg z]
  have hq : AnalyticAt ℝ (fun w : ℂ => 1 - ‖w‖ ^ 2) z :=
    analyticAt_const.sub (s5fg_norm_sq_analytic analyticAt_id)
  have hlog := (analyticAt_log hp).comp_of_eq hq rfl
  have hc := (Complex.ofRealCLM.analyticAt (Real.log (1 - ‖z‖ ^ 2))).comp_of_eq hlog rfl
  convert! hc.neg using 1

theorem s5vc_disk_potential_mixed {z : ℂ} (hz : z ∈ unitDisc) :
    dz (dzbar (fun w : ℂ => (-Real.log (1 - ‖w‖ ^ 2) : ℂ))) z =
      ((1 / (1 - ‖z‖ ^ 2) ^ 2 : ℝ) : ℂ) := by
  have he : (fun w : ℂ => (-Real.log (1 - ‖w‖ ^ 2) : ℂ)) =ᶠ[𝓝 z]
      (fun w => -Complex.log (1 - w * conj w)) := by
    filter_upwards [isOpen_ball.mem_nhds hz] with w hw
    have hp : 0 ≤ 1 - ‖w‖ ^ 2 := by
      have hn := mem_ball_zero_iff.mp hw
      nlinarith [norm_nonneg w]
    rw [Complex.ofReal_log hp]
    congr 2
    simp [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  rw [s5vc_mixed_congr he, s5vc_disk_log_mixed hz]
  simp [Complex.mul_conj, Complex.normSq_eq_norm_sq]

theorem s5vc_log_metric_mixed {G : ℂ → ℂ} {z : ℂ} (hG : AnalyticAt ℂ G z)
    (hv : ‖G z‖ < 1) (hd : deriv G z ≠ 0) :
    dz (dzbar (fun w => (Real.log (4 * ‖deriv G w‖ ^ 2 / (1 - ‖G w‖ ^ 2) ^ 2) : ℂ))) z =
      ((2 * ‖deriv G z‖ ^ 2 / (1 - ‖G z‖ ^ 2) ^ 2 : ℝ) : ℂ) := by
  let P : ℂ → ℂ := fun w => (-Real.log (1 - ‖w‖ ^ 2) : ℂ)
  let A : ℂ → ℂ := fun w => (Real.log ‖deriv G w‖ : ℂ)
  let B : ℂ → ℂ := P ∘ G
  have hA : ContDiffAt ℝ 2 A z := (hG.deriv.harmonicAt_log_norm hd).comp_CLM Complex.ofRealCLM |>.1
  have hB : ContDiffAt ℝ 2 B z :=
    ((s5vc_disk_potential_analytic (mem_ball_zero_iff.mpr hv)).comp hG.restrictScalars).contDiffAt
  have hnorm : ∀ᶠ w in 𝓝 z, ‖G w‖ < 1 := hG.continuousAt.norm (gt_mem_nhds hv)
  have hev : ∀ᶠ w in 𝓝 z, AnalyticAt ℂ G w ∧ ‖G w‖ < 1 ∧ deriv G w ≠ 0 :=
    hG.eventually_analyticAt.and (hnorm.and (hG.deriv.continuousAt.eventually_ne hd))
  have he : (fun w => (Real.log (4 * ‖deriv G w‖ ^ 2 / (1 - ‖G w‖ ^ 2) ^ 2) : ℂ)) =ᶠ[𝓝 z]
      (fun w => (Real.log 4 : ℂ) + 2 * A w + 2 * B w) := by
    filter_upwards [hev] with w hw
    have hq : 0 < 1 - ‖G w‖ ^ 2 := by nlinarith [norm_nonneg (G w), hw.2.1]
    have hdn : ‖deriv G w‖ ≠ 0 := norm_ne_zero_iff.mpr hw.2.2
    dsimp [A, B, P]
    rw [Real.log_div (mul_ne_zero (by norm_num) (pow_ne_zero 2 hdn)) (pow_ne_zero 2 hq.ne'),
      Real.log_mul (by norm_num) (pow_ne_zero 2 hdn), Real.log_pow, Real.log_pow]
    push_cast
    ring
  obtain ⟨r, hr, hb⟩ := Metric.eventually_nhds_iff_ball.mp hev
  have hGon : DifferentiableOn ℂ G (ball z r) := fun w hw => (hb w hw).1.differentiableAt.differentiableWithinAt
  have hm : MapsTo G (ball z r) unitDisc := fun w hw => mem_ball_zero_iff.mpr (hb w hw).2.1
  have hP : ContDiffOn ℝ 2 P unitDisc := fun w hw => (s5vc_disk_potential_analytic hw).contDiffAt.contDiffWithinAt
  have hcomp := dz_dzbar_comp_holomorphic (φ := G) (f := P) isOpen_ball isOpen_ball hGon hm hP (mem_ball_self hr)
  change dz (dzbar B) z = dz (dzbar P) (G z) * (‖deriv G z‖ ^ 2 : ℝ) at hcomp
  rw [s5vc_disk_potential_mixed (mem_ball_zero_iff.mpr hv)] at hcomp
  have hAz : dz (dzbar A) z = 0 := s5vc_mixed_log_norm hG.deriv hd
  have hc : dz (dzbar (fun _ : ℂ => (Real.log 4 : ℂ))) z = 0 := by
    rw [s5vc_mixed_laplacian contDiffAt_const]
    simp
  have h2A : ContDiffAt ℝ 2 (fun w => (2 : ℂ) * A w) z := contDiffAt_const.mul hA
  have h2B : ContDiffAt ℝ 2 (fun w => (2 : ℂ) * B w) z := contDiffAt_const.mul hB
  rw [s5vc_mixed_congr he,
    s5vc_mixed_add (contDiffAt_const.add h2A) h2B,
    s5vc_mixed_add contDiffAt_const h2A,
    s5vc_mixed_const_mul hA 2, s5vc_mixed_const_mul hB 2, hc, hAz, hcomp]
  push_cast
  ring

theorem s5vc_affine_mixed {F : ℂ → ℂ} {z : ℂ} (hF : ContDiffAt ℝ 2 F z) (c : ℂ) :
    dz (dzbar (fun t : ℂ => F (z + t * c))) 0 = dz (dzbar F) z * (‖c‖ ^ 2 : ℝ) := by
  have hev : ∀ᶠ y in 𝓝 z, ContDiffAt ℝ 2 F y := hF.eventually (by simp)
  obtain ⟨r, hr, hb⟩ := Metric.eventually_nhds_iff_ball.mp hev
  have hFc : ContDiffOn ℝ 2 F (ball z r) := fun y hy => (hb y hy).contDiffWithinAt
  have hc : ContinuousAt (fun t : ℂ => z + t * c) 0 := by fun_prop
  have he : ∀ᶠ t in 𝓝 (0 : ℂ), z + t * c ∈ ball z r := hc (by simpa using ball_mem_nhds z hr)
  obtain ⟨δ, hδ, hm⟩ := Metric.eventually_nhds_iff_ball.mp he
  have hφ : DifferentiableOn ℂ (fun t : ℂ => z + t * c) (ball 0 δ) := by fun_prop
  have hh := dz_dzbar_comp_holomorphic isOpen_ball isOpen_ball hφ (fun t ht => hm t ht) hFc (mem_ball_self hδ)
  have hd : deriv (fun t : ℂ => z + t * c) 0 = c := by
    simpa using (((hasDerivAt_id (0 : ℂ)).mul_const c).const_add z).deriv
  rw [hd, zero_mul, add_zero] at hh
  exact hh

theorem s5vc_levi_vertical {q : T1 × ExtPlane} (hq : q ∈ TCurve) (c : ℂ) :
    let ζ := finPart (inversion q.2)
    let G := fiberUniformizer (Quotient.out q.1 : LinfStarBall)
    leviTC logNormSq q (0, c) = 2 * ‖deriv G ζ‖ ^ 2 / (1 - ‖G ζ‖ ^ 2) ^ 2 * ‖c‖ ^ 2 := by
  intro ζ G
  have hμ := (Quotient.out q.1 : LinfStarBall).2
  have hζ := s5fg_actual_fiber_condition hq
  obtain ⟨hGa, hGv, hGd⟩ := s5fg_uniformizer_regular hμ hζ
  let F : ℂ → ℂ := fun t => (Real.log (4 * ‖deriv G t‖ ^ 2 / (1 - ‖G t‖ ^ 2) ^ 2) : ℂ)
  have hreal := s5fg_metric_realAnalytic hμ hζ
  have hFc : ContDiffAt ℝ 2 F ζ := by
    convert! ((Complex.ofRealCLM.analyticAt _).comp_of_eq hreal rfl).contDiffAt using 1
  have haff := s5vc_affine_mixed hFc c
  have hmetric : dz (dzbar F) ζ = ((2 * ‖deriv G ζ‖ ^ 2 / (1 - ‖G ζ‖ ^ 2) ^ 2 : ℝ) : ℂ) :=
    s5vc_log_metric_mixed hGa hGv hGd
  have hx : (bers q.1, ζ) ∈ tcCoord '' TCurve := ⟨q, hq, rfl⟩
  have hmap : ContinuousAt (fun t : ℂ => (bers q.1, t)) ζ := by fun_prop
  have he0 : (fun t : ℂ => (logNormSq (tcCoordInv (bers q.1, t)) : ℂ)) =ᶠ[𝓝 ζ] F := by
    filter_upwards [hmap (tcCoord_chart.2.mem_nhds hx)] with t ht
    rw [s5fg_coordInv_fiber ht]
    unfold logNormSq
    rw [tcc_inversion_invol]
    rfl
  have hl : Tendsto (fun t : ℂ => ζ + t * c) (𝓝 0) (𝓝 ζ) := by
    have hlin : Continuous (fun t : ℂ => ζ + t * c) := by fun_prop
    simpa only [zero_mul, add_zero] using hlin.tendsto 0
  have he : (fun t : ℂ => (logNormSq (tcCoordInv (bers q.1, ζ + t * c)) : ℂ)) =ᶠ[𝓝 0]
      (fun t => F (ζ + t * c)) := he0.comp_tendsto hl
  -- G1 fix B: the shift of `tcCoordH` depends only on the base point, so vertical lines of `tcCoordH` and of
  -- `tcCoord` through `q` pass through the same points of `𝒯(1)`.
  have hHinj : InjOn tcCoordH TCurve := by
    intro a ha b hb hab
    have h1 : a.1 = b.1 := bers_injective (congrArg Prod.fst hab)
    have h2 := congrArg Prod.snd hab
    simp only [tcCoordH] at h2
    rw [h1] at h2
    exact tcCoord_chart.1 ha hb (Prod.ext (congrArg bers h1) (add_right_cancel h2))
  have hline : (fun t : ℂ => (logNormSq (tcCoordHInv (tcCoordH q + t • (0, c))) : ℂ)) =ᶠ[𝓝 0]
      fun t => (logNormSq (tcCoordInv (bers q.1, ζ + t * c)) : ℂ) := by
    filter_upwards [(hmap.tendsto.comp hl) (tcCoord_chart.2.mem_nhds hx)] with t ht
    obtain ⟨q', hq', hq'e⟩ := ht
    replace hq'e : tcCoord q' = (bers q.1, ζ + t * c) := hq'e
    have h1 : q'.1 = q.1 := bers_injective (congrArg Prod.fst hq'e)
    have h2 : finPart (inversion q'.2) = ζ + t * c := congrArg Prod.snd hq'e
    have hH : tcCoordH q + t • ((0 : AInf unitDisc), c) = tcCoordH q' := by
      simp only [tcCoordH, h1, h2, Prod.smul_mk, smul_zero, smul_eq_mul, Prod.mk_add_mk, add_zero]
      congr 1
      dsimp only [ζ]
      ring
    have hHq : tcCoordHInv (tcCoordH q') = q' := hHinj.leftInvOn_invFunOn hq'
    have hq0 : tcCoordInv (bers q.1, ζ + t * c) = q' := by
      rw [← hq'e]
      exact tcCoord_chart.1.leftInvOn_invFunOn hq'
    simp only [hH, hHq, hq0]
  unfold leviTC
  rw [s5vc_mixed_congr hline, s5vc_mixed_congr he, haff, hmetric]
  simp only [← Complex.ofReal_mul, Complex.ofReal_re]

theorem s5vc_polarize_vertical {N : AInf unitDisc × ℂ → ℝ} {a : ℝ}
    (hN : ∀ c : ℂ, N (0, c) = a * ‖c‖ ^ 2) (c : ℂ) :
    polarize N (0, c) (0, c) = (a * ‖c‖ ^ 2 : ℝ) := by
  have h1 : ((0, c) : AInf unitDisc × ℂ) + (0, c) = (0, c + c) := by ext <;> simp
  have h2 : ((0, c) : AInf unitDisc × ℂ) - (0, c) = (0, 0) := by ext <;> simp
  have h3 : ((0, c) : AInf unitDisc × ℂ) + I • (0, c) = (0, c + I * c) := by ext <;> simp [smul_eq_mul]
  have h4 : ((0, c) : AInf unitDisc × ℂ) - I • (0, c) = (0, c - I * c) := by ext <;> simp [smul_eq_mul]
  have hn1 : ‖c + c‖ ^ 2 = 4 * ‖c‖ ^ 2 := by
    rw [show c + c = (2 : ℂ) * c by ring, norm_mul, mul_pow]
    norm_num
  have hn3 : ‖c + I * c‖ ^ 2 = 2 * ‖c‖ ^ 2 := by
    rw [show c + I * c = (1 + I) * c by ring, norm_mul, mul_pow]
    norm_num [Complex.sq_norm, Complex.normSq_apply]
  have hn4 : ‖c - I * c‖ ^ 2 = 2 * ‖c‖ ^ 2 := by
    rw [show c - I * c = (1 - I) * c by ring, norm_mul, mul_pow]
    norm_num [Complex.sq_norm, Complex.normSq_apply]
  rw [polarize, h1, h2, h3, h4, hN, hN, hN, hN, hn1, hn3, hn4]
  simp only [norm_zero, zero_pow (by norm_num : 2 ≠ 0), mul_zero]
  push_cast
  ring

theorem s5vc_theta_vertical {q : T1 × ExtPlane} (hq : q ∈ TCurve) (c : ℂ) :
    let ζ := finPart (inversion q.2)
    let G := fiberUniformizer (Quotient.out q.1 : LinfStarBall)
    thetaForm q (0, c) (0, c) = -((2 * ‖deriv G ζ‖ ^ 2 / (1 - ‖G ζ‖ ^ 2) ^ 2 * ‖c‖ ^ 2 : ℝ) : ℂ) := by
  intro ζ G
  have hN : ∀ d : ℂ, leviTC logNormSq q (0, d) =
      (2 * ‖deriv G ζ‖ ^ 2 / (1 - ‖G ζ‖ ^ 2) ^ 2) * ‖d‖ ^ 2 := fun d => s5vc_levi_vertical hq d
  exact congrArg Neg.neg (s5vc_polarize_vertical hN c)

theorem s5vc_theta_vertical_neg {q : T1 × ExtPlane} (hq : q ∈ TCurve) {c : ℂ} (hc : c ≠ 0) :
    (thetaForm q (0, c) (0, c)).re < 0 := by
  have hμ := (Quotient.out q.1 : LinfStarBall).2
  obtain ⟨_, hv, hd⟩ := s5fg_uniformizer_regular hμ (s5fg_actual_fiber_condition hq)
  have hqpos : 0 < 1 - ‖fiberUniformizer (Quotient.out q.1 : LinfStarBall) (finPart (inversion q.2))‖ ^ 2 := by
    nlinarith [norm_nonneg (fiberUniformizer (Quotient.out q.1 : LinfStarBall) (finPart (inversion q.2)))]
  rw [s5vc_theta_vertical hq c]
  simp only [Complex.neg_re, Complex.ofReal_re, neg_lt_zero]
  exact mul_pos (div_pos (mul_pos (by norm_num) (pow_pos (norm_pos_iff.mpr hd) _)) (pow_pos hqpos _))
    (pow_pos (norm_pos_iff.mpr hc) _)

theorem s5vc_wB_zero : wB (0 : LinfStar) = id := by
  have hid : mobiusExt 1 0 0 1 = id := by
    funext p
    induction p using OnePoint.rec with
    | infty => exact mobiusExt_infty_of_eq rfl
    | coe z => rw [mobiusExt_coe (by simp)]; simp [mobiusFn]
  have hW0 : normalizedSolution (extB (0 : LinfStar)) = id := by
    simpa only [zero_smul] using QCV.qcv_W_zero (0 : LinfStar)
  have hN : IsNormalizedSolution id (extB (0 : LinfStar)) := by
    simpa only [hW0] using (QCV.qcv_W_props (μ := 0) (by norm_num)).1
  have hnorm : IsNormalizedB 0 id := by
    refine ⟨id, ⟨1, 0, 0, 1, by norm_num, hid.symm⟩, id, hN, fun z => rfl, rfl,
      id, fun z _ => rfl, rfl, deriv_id _, ?_⟩
    rw [grp_wAS_zero]
    exact Function.leftInverse_invFun Function.injective_id extInf
  exact (wB_unique hnorm).symm

theorem s5vc_origin_gMu {z : ℂ} (hz : z ∈ unitDiscExterior) :
    gMu (Quotient.out originT : LinfStarBall) z = z := by
  have h0 : (0 : LinfStar) ∈ LinfStarBall := by simp [LinfStarBall]
  have hclass : teichSetoid (Quotient.out originT : LinfStarBall) ⟨0, h0⟩ :=
    Quotient.exact (Quotient.out_eq originT)
  have he := tcg_welding_congr hclass (Or.inl ⟨z, hz, rfl⟩)
  have hμ := (Quotient.out originT : LinfStarBall).2
  apply OnePoint.coe_injective
  calc
    (gMu (Quotient.out originT : LinfStarBall) z : ExtPlane) =
        normalizedWeldingSphere (Quotient.out originT : LinfStarBall) z := gMu_sphere_factorization hμ hz
    _ = normalizedWeldingSphere (0 : LinfStar) z := he
    _ = (z : ExtPlane) := by
      simpa [normalizedWeldingSphere, s5vc_wB_zero, grp_wAS_zero] using
        Function.leftInverse_invFun Function.injective_id (z : ExtPlane)

theorem s5vc_fiberPt_mem {z : ℂ} (hz : z ∈ unitDiscExterior) : fiberPt z ∈ TCurve := by
  have h0 : (0 : LinfStar) ∈ LinfStarBall := by simp [LinfStarBall]
  have hclass : teichSetoid (Quotient.out originT : LinfStarBall) ⟨0, h0⟩ :=
    Quotient.exact (Quotient.out_eq originT)
  change (z : ExtPlane) ∈ wB (Quotient.out originT : LinfStarBall) '' extDiscExterior
  rw [fiber_independent hclass, s5vc_wB_zero, image_id]
  exact Or.inl ⟨z, hz, rfl⟩

theorem s5vc_origin_uniformizer_jet {z : ℂ} (hz : z ∈ unitDiscExterior) :
    fiberUniformizer (Quotient.out originT : LinfStarBall) z⁻¹ = z⁻¹ ∧
      deriv (fiberUniformizer (Quotient.out originT : LinfStarBall)) z⁻¹ = 1 := by
  have hμ := (Quotient.out originT : LinfStarBall).2
  have he : gMu (Quotient.out originT : LinfStarBall) =ᶠ[𝓝 z] id := by
    filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds hz] with w hw
    exact s5vc_origin_gMu hw
  have hd : deriv (gMu (Quotient.out originT : LinfStarBall)) z = 1 := by simpa using he.deriv_eq
  obtain ⟨hv, hder⟩ := s5wr_uniformizer_jet hμ hz
  rw [s5vc_origin_gMu hz] at hv hder
  refine ⟨hv, ?_⟩
  rw [hder.deriv, hd, mul_one, div_self]
  exact pow_ne_zero _ (resolvent_exterior_ne_zero hz)

theorem s5vc_prop_5_7_vertical {z : ℂ} (hz : z ∈ unitDiscExterior) :
    thetaForm (fiberPt z) (vertVec z) (vertVec z) = -2 / (1 - ‖z‖ ^ 2) ^ 2 := by
  have hz0 := resolvent_exterior_ne_zero hz
  have hn0 : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz0
  have hq : 1 - ‖z‖ ^ 2 ≠ 0 := by
    have hn : 1 < ‖z‖ := hz
    nlinarith [norm_nonneg z]
  have hq' : ‖z‖ ^ 2 - 1 ≠ 0 := by intro h; apply hq; linarith
  have hζ : finPart (inversion (z : ExtPlane)) = z⁻¹ := by simp [inversion, mobiusExt, hz0, finPart]
  obtain ⟨hv, hd⟩ := s5vc_origin_uniformizer_jet hz
  have he := s5vc_theta_vertical (s5vc_fiberPt_mem hz) (-1 / z ^ 2)
  change thetaForm (fiberPt z) (vertVec z) (vertVec z) = _ at he
  dsimp only [fiberPt] at he
  rw [hζ, hv, hd] at he
  have halg : 2 * ‖(1 : ℂ)‖ ^ 2 / (1 - ‖z⁻¹‖ ^ 2) ^ 2 * ‖(-1 : ℂ) / z ^ 2‖ ^ 2 =
      2 / (1 - ‖z‖ ^ 2) ^ 2 := by
    simp only [norm_one, one_pow, norm_inv, norm_div, norm_neg, norm_pow]
    field_simp [hn0, hq, hq']
    <;> ring
  rw [halg] at he
  unfold fiberPt
  rw [he]
  push_cast
  ring

end TakhtajanTeo
