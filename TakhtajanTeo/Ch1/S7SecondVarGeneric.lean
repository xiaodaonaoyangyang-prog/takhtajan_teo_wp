import TakhtajanTeo.Ch1.S7FirstVariation

/-!
# Program G, F2: generic second-order tools (下属1)

Stubs A–D of `F2_SUBINTERFACE` (`thm_7_7`): the mixed derivative under the integral sign at the centre of a polydisc
(`s7g_f2_mixed`, double torus Cauchy + Fubini, for a general second-countable measure space), the mixed partial of
`e ↦ Φ(e, ē)` (`s7g_f2_ddpartial`), `s7g_f2_conjflip`, `s7g_f2_conjW`, `s7g_f2_germ`, and the Hermitian symmetry
`s7g_f2_herm` of `g`. Also general-measure copies `s7g_f2_Gint`, `s7g_f2_cauchy`, `s7g_f2_param` of the `s7g_h_*`
parameter-integral lemmas.
-/

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal NNReal ComplexConjugate Classical Real
noncomputable section
namespace TakhtajanTeo
open LiZhongQC

/-- `∂_z(f̄) = \overline{∂_z̄ f}`. -/
theorem s7g_f2_dz_conj (f : ℂ → ℂ) (w : ℂ) : dz (fun x => conj (f x)) w = conj (dzbar f w) := by
  have h := p71r_dzbar_conj (fun x => conj (f x)) w
  simp only [Complex.conj_conj] at h
  rw [h, Complex.conj_conj]

/-- STUB C2. Wirtinger calculus of a conjugate. -/
theorem s7g_f2_conjW (f : ℂ → ℂ) (z : ℂ) : dzbar (dz fun e => conj (f e)) z = conj (dz (dzbar f) z) := by
  have h : (dz fun e => conj (f e)) = fun y => conj (dzbar f y) := funext fun y => s7g_f2_dz_conj f y
  rw [h, p71r_dzbar_conj]

/-- `∂_z` depends only on the germ. -/
theorem s7g_f2_dz_congr {f h : ℂ → ℂ} {z : ℂ} (hfh : f =ᶠ[𝓝 z] h) : dz f z = dz h z := by
  simp only [dz, hfh.fderiv_eq]

/-- STUB C3. `∂_z̄∂_z` depends only on the germ. -/
theorem s7g_f2_germ {f h : ℂ → ℂ} {z : ℂ} (hfh : f =ᶠ[𝓝 z] h) : dzbar (dz f) z = dzbar (dz h) z := by
  have h1 : (dz f) =ᶠ[𝓝 z] (dz h) := by
    filter_upwards [hfh.fderiv (𝕜 := ℝ)] with y hy
    simp only [dz, hy]
  exact p71_dzbar_congr h1

/-- STUB D. Hermitian symmetry of `g`. -/
theorem s7g_f2_herm (μ ν : ℂ → ℂ) (η : LinfStar) : gWP ν μ η = conj (gWP μ ν η) := by
  unfold gWP
  rw [← integral_conj]
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  simp only [map_mul, Complex.conj_conj, Complex.conj_ofReal]
  ring

/-- Wirtinger derivatives of `e ↦ h(ē)`. -/
theorem s7g_f2_wconj {h : ℂ → ℂ} {y : ℂ} (hh : DifferentiableAt ℝ h (conj y)) :
    dz (fun e => h (conj e)) y = dzbar h (conj y) ∧ dzbar (fun e => h (conj e)) y = dz h (conj y) := by
  set D := fderiv ℝ h (conj y) with hDd
  have hd : HasFDerivAt (fun e => h (conj e)) (D.comp (Complex.conjCLE : ℂ ≃L[ℝ] ℂ).toContinuousLinearMap) y :=
    HasFDerivAt.comp (g := h) (f := fun e : ℂ => conj e) y hh.hasFDerivAt
      (Complex.conjCLE : ℂ ≃L[ℝ] ℂ).hasFDerivAt
  unfold dz dzbar
  rw [hd.fderiv]
  simp only [ContinuousLinearMap.coe_comp, Function.comp_apply, ContinuousLinearEquiv.coe_coe,
    Complex.conjCLE_apply, map_one, Complex.conj_I, map_neg]
  constructor <;> ring

/-- `dz L` is real-differentiable at an interior point where `L` is `C²`. -/
theorem s7g_f2_dz_diff {L : ℂ → ℂ} {r : ℝ} (hL : ContDiffOn ℝ 2 L (ball 0 r)) {y : ℂ} (hy : y ∈ ball (0 : ℂ) r) :
    DifferentiableAt ℝ (dz L) y ∧ DifferentiableAt ℝ (dzbar L) y := by
  have hF : ContDiffOn ℝ 1 (fderiv ℝ L) (ball 0 r) := hL.fderiv_of_isOpen isOpen_ball (by norm_num)
  have hFd : DifferentiableAt ℝ (fderiv ℝ L) y :=
    (hF.differentiableOn (by norm_num)).differentiableAt (isOpen_ball.mem_nhds hy)
  have h1 : DifferentiableAt ℝ (fun x => fderiv ℝ L x 1) y := hFd.clm_apply (differentiableAt_const _)
  have hI : DifferentiableAt ℝ (fun x => fderiv ℝ L x I) y := hFd.clm_apply (differentiableAt_const _)
  have e1 : dz L = fun x => (fderiv ℝ L x 1 - I * fderiv ℝ L x I) * (2 : ℂ)⁻¹ :=
    funext fun x => by simp only [dz, div_eq_mul_inv]
  have e2 : dzbar L = fun x => (fderiv ℝ L x 1 + I * fderiv ℝ L x I) * (2 : ℂ)⁻¹ :=
    funext fun x => by simp only [dzbar, div_eq_mul_inv]
  rw [e1, e2]
  exact ⟨(h1.sub (hI.const_mul I)).mul_const _, (h1.add (hI.const_mul I)).mul_const _⟩

/-- STUB C. `∂_ε∂_ε̄ (L ∘ conj)(0) = ∂_ē∂_e L(0)` for `L` of class `C²` near `0`. -/
theorem s7g_f2_conjflip {L : ℂ → ℂ} {r : ℝ} (hr : 0 < r) (hL : ContDiffOn ℝ 2 L (ball 0 r)) :
    dz (dzbar fun ε => L (conj ε)) 0 = dzbar (dz L) 0 := by
  have hev : (dzbar fun ε => L (conj ε)) =ᶠ[𝓝 (0 : ℂ)] fun ε => dz L (conj ε) := by
    filter_upwards [isOpen_ball.mem_nhds (mem_ball_self hr)] with ε hε
    have hc : conj ε ∈ ball (0 : ℂ) r := by
      rw [mem_ball_zero_iff, Complex.norm_conj]
      exact mem_ball_zero_iff.1 hε
    exact (s7g_f2_wconj ((hL.differentiableOn (by norm_num)).differentiableAt
      (isOpen_ball.mem_nhds hc))).2
  rw [s7g_f2_dz_congr hev]
  have h0 : conj (0 : ℂ) ∈ ball (0 : ℂ) r := by rw [map_zero]; exact mem_ball_self hr
  rw [(s7g_f2_wconj (s7g_f2_dz_diff hL h0).1).1, map_zero]

/-- `∂_z` of `y ↦ H(y, ȳ)` is the first partial derivative of a jointly holomorphic `H`. -/
theorem s7g_f2_dz_partial1 {H : ℂ × ℂ → ℂ} {y : ℂ} (hH : DifferentiableAt ℂ H (y, conj y)) :
    dz (fun y => H (y, conj y)) y = deriv (fun a => H (a, conj y)) y := by
  set D := fderiv ℂ H (y, conj y) with hDd
  have hd : HasFDerivAt (fun y : ℂ => H (y, conj y))
      ((D.restrictScalars ℝ).comp ((ContinuousLinearMap.id ℝ ℂ).prod
        (Complex.conjCLE : ℂ ≃L[ℝ] ℂ).toContinuousLinearMap)) y :=
    HasFDerivAt.comp (g := H) (f := fun y : ℂ => (y, conj y)) y (hH.hasFDerivAt.restrictScalars ℝ)
      ((hasFDerivAt_id y).prodMk (Complex.conjCLE : ℂ ≃L[ℝ] ℂ).hasFDerivAt)
  have hb : HasDerivAt (fun a => H (a, conj y)) (D (1, 0)) y :=
    (HasFDerivAt.comp (g := H) (f := fun a : ℂ => (a, conj y)) y hH.hasFDerivAt
      (hasFDerivAt_prodMk_left y (conj y))).hasDerivAt
  rw [hb.deriv]
  unfold dz
  rw [hd.fderiv]
  simp only [ContinuousLinearMap.coe_comp, Function.comp_apply, ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.coe_id', id, ContinuousLinearEquiv.coe_coe, Complex.conjCLE_apply,
    ContinuousLinearMap.coe_restrictScalars', map_one, Complex.conj_I]
  have e1 : ((1 : ℂ), (1 : ℂ)) = ((1 : ℂ), (0 : ℂ)) + ((0 : ℂ), (1 : ℂ)) := by ext <;> simp
  have e2 : (I, -I) = I • ((1 : ℂ), (0 : ℂ)) + (-I) • ((0 : ℂ), (1 : ℂ)) := by ext <;> simp
  rw [e1, e2, map_add, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
  ring_nf
  rw [Complex.I_sq]
  ring

/-- Iterated slice derivatives of a `C²` holomorphic `Φ` are entries of its second derivative. -/
theorem s7g_f2_mixfd {Φ : ℂ × ℂ → ℂ} {R : ℝ} (hR : 0 < R)
    (hΦ : ContDiffOn ℂ 2 Φ (ball (0 : ℂ) R ×ˢ ball (0 : ℂ) R)) :
    deriv (fun a => deriv (fun b => Φ (a, b)) 0) 0 = fderiv ℂ (fderiv ℂ Φ) ((0 : ℂ), (0 : ℂ)) (1, 0) (0, 1) ∧
      deriv (fun b => deriv (fun a => Φ (a, b)) 0) 0 = fderiv ℂ (fderiv ℂ Φ) ((0 : ℂ), (0 : ℂ)) (0, 1) (1, 0) := by
  have hU : IsOpen (ball (0 : ℂ) R ×ˢ ball (0 : ℂ) R) := isOpen_ball.prod isOpen_ball
  have h0 : ((0 : ℂ), (0 : ℂ)) ∈ ball (0 : ℂ) R ×ˢ ball (0 : ℂ) R := ⟨mem_ball_self hR, mem_ball_self hR⟩
  have hd : ∀ P ∈ ball (0 : ℂ) R ×ˢ ball (0 : ℂ) R, HasFDerivAt Φ (fderiv ℂ Φ P) P := fun P hP =>
    ((hΦ.differentiableOn (by norm_num)).differentiableAt (hU.mem_nhds hP)).hasFDerivAt
  have hF : HasFDerivAt (fderiv ℂ Φ) (fderiv ℂ (fderiv ℂ Φ) ((0 : ℂ), (0 : ℂ))) ((0 : ℂ), (0 : ℂ)) :=
    (((hΦ.fderiv_of_isOpen hU (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)).differentiableOn
      (by norm_num)).differentiableAt (hU.mem_nhds h0)).hasFDerivAt
  constructor
  · have hev : (fun a => deriv (fun b => Φ (a, b)) 0) =ᶠ[𝓝 (0 : ℂ)] fun a => fderiv ℂ Φ (a, 0) (0, 1) := by
      filter_upwards [isOpen_ball.mem_nhds (mem_ball_self hR)] with a ha
      have hda : HasDerivAt (fun b => Φ (a, b)) (fderiv ℂ Φ (a, 0) (0, 1)) 0 := by
        exact (hd (a, 0) ⟨ha, mem_ball_self hR⟩).comp_hasDerivAt (0 : ℂ)
          ((hasDerivAt_const (0 : ℂ) a).prodMk (hasDerivAt_id (0 : ℂ)))
      exact hda.deriv
    rw [hev.deriv_eq]
    have hc := (HasFDerivAt.comp_hasDerivAt (l := fderiv ℂ Φ) (f := fun a : ℂ => (a, (0 : ℂ))) (0 : ℂ) hF
      ((hasDerivAt_id (0 : ℂ)).prodMk (hasDerivAt_const (0 : ℂ) (0 : ℂ)))).clm_apply
      (hasDerivAt_const (0 : ℂ) ((0 : ℂ), (1 : ℂ)))
    exact hc.deriv.trans (by simp)
  · have hev : (fun b => deriv (fun a => Φ (a, b)) 0) =ᶠ[𝓝 (0 : ℂ)] fun b => fderiv ℂ Φ (0, b) (1, 0) := by
      filter_upwards [isOpen_ball.mem_nhds (mem_ball_self hR)] with b hb
      have hda : HasDerivAt (fun a => Φ (a, b)) (fderiv ℂ Φ (0, b) (1, 0)) 0 := by
        exact (hd (0, b) ⟨mem_ball_self hR, hb⟩).comp_hasDerivAt (0 : ℂ)
          ((hasDerivAt_id (0 : ℂ)).prodMk (hasDerivAt_const (0 : ℂ) b))
      exact hda.deriv
    rw [hev.deriv_eq]
    have hc := (hF.comp_hasDerivAt (0 : ℂ) ((hasDerivAt_const (0 : ℂ) (0 : ℂ)).prodMk (hasDerivAt_id (0 : ℂ)))).clm_apply
      (hasDerivAt_const (0 : ℂ) ((1 : ℂ), (0 : ℂ)))
    exact hc.deriv.trans (by simp)

/-- STUB B. `∂_ē ∂_e` of `e ↦ Φ(e, ē)` is the mixed partial of a `C²` holomorphic `Φ`. -/
theorem s7g_f2_ddpartial {Φ : ℂ × ℂ → ℂ} {R : ℝ} (hR : 0 < R)
    (hΦ : ContDiffOn ℂ 2 Φ (ball (0 : ℂ) R ×ˢ ball (0 : ℂ) R)) :
    dzbar (dz fun e => Φ (e, conj e)) 0 = deriv (fun b => deriv (fun a => Φ (a, b)) 0) 0 ∧
      dz (dzbar fun e => Φ (e, conj e)) 0 = deriv (fun b => deriv (fun a => Φ (a, b)) 0) 0 := by
  have hU : IsOpen (ball (0 : ℂ) R ×ˢ ball (0 : ℂ) R) := isOpen_ball.prod isOpen_ball
  have h0 : ((0 : ℂ), (0 : ℂ)) ∈ ball (0 : ℂ) R ×ˢ ball (0 : ℂ) R := ⟨mem_ball_self hR, mem_ball_self hR⟩
  have hdiff : ∀ P ∈ ball (0 : ℂ) R ×ˢ ball (0 : ℂ) R, DifferentiableAt ℂ Φ P := fun P hP =>
    (hΦ.differentiableOn (by norm_num)).differentiableAt (hU.mem_nhds hP)
  have hFd : DifferentiableAt ℂ (fderiv ℂ Φ) ((0 : ℂ), (0 : ℂ)) :=
    ((hΦ.fderiv_of_isOpen hU (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)).differentiableOn
      (by norm_num)).differentiableAt (hU.mem_nhds h0)
  -- the two partial derivatives, near the origin
  have hD1 : (fun P : ℂ × ℂ => deriv (fun a => Φ (a, P.2)) P.1) =ᶠ[𝓝 ((0 : ℂ), (0 : ℂ))]
      fun P => fderiv ℂ Φ P (1, 0) := by
    filter_upwards [hU.mem_nhds h0] with P hP
    have hda : HasDerivAt (fun a => Φ (a, P.2)) (fderiv ℂ Φ P (1, 0)) P.1 := by
      exact (hdiff P hP).hasFDerivAt.comp_hasDerivAt P.1 ((hasDerivAt_id P.1).prodMk (hasDerivAt_const P.1 P.2))
    exact hda.deriv
  have hD2 : (fun P : ℂ × ℂ => deriv (fun b => Φ (P.1, b)) P.2) =ᶠ[𝓝 ((0 : ℂ), (0 : ℂ))]
      fun P => fderiv ℂ Φ P (0, 1) := by
    filter_upwards [hU.mem_nhds h0] with P hP
    have hda : HasDerivAt (fun b => Φ (P.1, b)) (fderiv ℂ Φ P (0, 1)) P.2 := by
      exact (hdiff P hP).hasFDerivAt.comp_hasDerivAt P.2 ((hasDerivAt_const P.2 P.1).prodMk (hasDerivAt_id P.2))
    exact hda.deriv
  have hD1d : DifferentiableAt ℂ (fun P : ℂ × ℂ => deriv (fun a => Φ (a, P.2)) P.1) ((0 : ℂ), conj (0 : ℂ)) := by
    rw [map_zero]
    exact (hFd.clm_apply (differentiableAt_const _)).congr_of_eventuallyEq hD1
  have hD2d : DifferentiableAt ℂ (fun P : ℂ × ℂ => deriv (fun b => Φ (P.1, b)) P.2) ((0 : ℂ), conj (0 : ℂ)) := by
    rw [map_zero]
    exact (hFd.clm_apply (differentiableAt_const _)).congr_of_eventuallyEq hD2
  have hmap : ∀ᶠ e in 𝓝 (0 : ℂ), (e, conj e) ∈ ball (0 : ℂ) R ×ˢ ball (0 : ℂ) R := by
    filter_upwards [isOpen_ball.mem_nhds (mem_ball_self hR)] with e he
    refine ⟨he, ?_⟩
    rw [mem_ball_zero_iff, Complex.norm_conj]
    exact mem_ball_zero_iff.1 he
  constructor
  · have hev : (dz fun e => Φ (e, conj e)) =ᶠ[𝓝 (0 : ℂ)]
        fun e => (fun P : ℂ × ℂ => deriv (fun a => Φ (a, P.2)) P.1) (e, conj e) := by
      filter_upwards [hmap] with e he
      exact s7g_f2_dz_partial1 (hdiff _ he)
    rw [p71_dzbar_congr hev, p71_dzbar_partial hD1d, map_zero]
  · have hev : (dzbar fun e => Φ (e, conj e)) =ᶠ[𝓝 (0 : ℂ)]
        fun e => (fun P : ℂ × ℂ => deriv (fun b => Φ (P.1, b)) P.2) (e, conj e) := by
      filter_upwards [hmap] with e he
      exact p71_dzbar_partial (hdiff _ he)
    rw [s7g_f2_dz_congr hev, s7g_f2_dz_partial1 hD2d, map_zero]
    obtain ⟨m1, m2⟩ := s7g_f2_mixfd hR hΦ
    have hsym := (hΦ.contDiffAt (hU.mem_nhds h0)).isSymmSndFDerivAt (by simp)
    rw [m1, m2]
    exact hsym _ _

/-- The circle-parametrised family is integrable on `[0, 2π] × T` under a uniform `L¹(T)` bound. -/
theorem s7g_f2_Gint {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    [SecondCountableTopology X] {m : Measure X} [SFinite m] {F : ℂ → X → ℂ} {T : Set X} (hT : MeasurableSet T) {c : ℂ} {R r : ℝ}
    (hr : 0 < r) (hrR : r ≤ R)
    (hc : ContinuousOn (fun p : ℂ × X => F p.1 p.2) (closedBall c R ×ˢ T))
    {M : ℝ} (hM : ∀ a ∈ closedBall c R, ∫⁻ x in T, ‖F a x‖ₑ ∂m ≤ ENNReal.ofReal M) :
    MeasureTheory.Integrable (fun q : ℝ × X => F (circleMap c r q.1) q.2)
      ((MeasureTheory.volume.restrict (Ioc 0 (2 * Real.pi))).prod (m.restrict T)) := by
  have hcm : ∀ θ : ℝ, circleMap c r θ ∈ closedBall c R := fun θ =>
    closedBall_subset_closedBall hrR (circleMap_mem_closedBall c hr.le θ)
  have hcont : ContinuousOn (fun q : ℝ × X => F (circleMap c r q.1) q.2) (Ioc 0 (2 * Real.pi) ×ˢ T) :=
    hc.comp (((continuous_circleMap c r).comp continuous_fst).prodMk continuous_snd).continuousOn
      (fun q hq => ⟨hcm q.1, hq.2⟩)
  refine ⟨?_, ?_⟩
  · rw [MeasureTheory.Measure.prod_restrict]
    exact hcont.aestronglyMeasurable (measurableSet_Ioc.prod hT)
  · calc _ ≤ ∫⁻ θ in Ioc 0 (2 * Real.pi), ∫⁻ x in T, ‖F (circleMap c r θ) x‖ₑ ∂m :=
          MeasureTheory.lintegral_prod_le _
      _ ≤ ∫⁻ _θ in Ioc 0 (2 * Real.pi), ENNReal.ofReal M := MeasureTheory.lintegral_mono fun θ => hM _ (hcm θ)
      _ < ⊤ := by
          rw [MeasureTheory.setLIntegral_const]
          exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top measure_Ioc_lt_top

/-- Cauchy's formula under the integral sign (Fubini on `[0, 2π] × T`). -/
theorem s7g_f2_cauchy {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    [SecondCountableTopology X] {m : Measure X} [SFinite m] {F : ℂ → X → ℂ} {T : Set X} (hT : MeasurableSet T) {c : ℂ} {R r : ℝ}
    (hr : 0 < r) (hrR : r < R)
    (hc : ContinuousOn (fun p : ℂ × X => F p.1 p.2) (closedBall c R ×ˢ T))
    (hhol : ∀ x ∈ T, DifferentiableOn ℂ (fun a => F a x) (ball c R))
    {M : ℝ} (hM : ∀ a ∈ closedBall c R, ∫⁻ x in T, ‖F a x‖ₑ ∂m ≤ ENNReal.ofReal M) {a : ℂ} (ha : a ∈ ball c r) :
    (2 * Real.pi * I : ℂ) • ∫ x in T, F a x ∂m = ∮ z in C(c, r), (z - a)⁻¹ • ∫ x in T, F z x ∂m := by
  have hG := s7g_f2_Gint hT hr hrR.le hc hM
  have hda : dist a c < r := ha
  set k : ℝ → ℂ := fun θ => deriv (circleMap c r) θ * (circleMap c r θ - a)⁻¹ with hk
  have hdist : ∀ θ : ℝ, ‖circleMap c r θ - c‖ = r := fun θ => by
    rw [circleMap_sub_center, norm_circleMap_zero, abs_of_pos hr]
  have hge : ∀ θ : ℝ, r - dist a c ≤ ‖circleMap c r θ - a‖ := by
    intro θ
    have h := norm_sub_norm_le (circleMap c r θ - c) (a - c)
    rw [hdist θ, sub_sub_sub_cancel_right, ← dist_eq_norm] at h
    exact h
  have hne : ∀ θ : ℝ, circleMap c r θ - a ≠ 0 := fun θ h => by
    have := hge θ
    rw [h, norm_zero] at this
    linarith
  have hkc : Continuous k := by
    have e : k = fun θ => circleMap 0 r θ * I * (circleMap c r θ - a)⁻¹ := by
      rw [hk]
      funext θ
      rw [deriv_circleMap]
    rw [e]
    exact ((continuous_circleMap 0 r).mul continuous_const).mul
      (((continuous_circleMap c r).sub continuous_const).inv₀ hne)
  have hkb : ∀ θ : ℝ, ‖k θ‖ ≤ r * (r - dist a c)⁻¹ := by
    intro θ
    rw [hk]
    simp only []
    rw [deriv_circleMap, norm_mul, norm_mul, norm_I, mul_one, norm_circleMap_zero, abs_of_pos hr, norm_inv]
    exact mul_le_mul_of_nonneg_left (inv_anti₀ (sub_pos.2 hda) (hge θ)) hr.le
  have hH : MeasureTheory.Integrable (fun q : ℝ × X => k q.1 * F (circleMap c r q.1) q.2)
      ((MeasureTheory.volume.restrict (Ioc 0 (2 * Real.pi))).prod (m.restrict T)) :=
    hG.bdd_mul (hkc.comp continuous_fst).aestronglyMeasurable (Eventually.of_forall fun q => hkb q.1)
  have hswap := MeasureTheory.integral_integral_swap (f := fun θ x => k θ * F (circleMap c r θ) x) hH
  have e1 : (∮ z in C(c, r), (z - a)⁻¹ • ∫ x in T, F z x ∂m) =
      ∫ θ in Ioc 0 (2 * Real.pi), ∫ x in T, k θ * F (circleMap c r θ) x ∂m := by
    rw [circleIntegral, intervalIntegral.integral_of_le Real.two_pi_pos.le]
    refine MeasureTheory.integral_congr_ae (Eventually.of_forall fun θ => ?_)
    simp only [hk, smul_eq_mul]
    rw [MeasureTheory.integral_const_mul]
    ring
  have e2 : ∀ x ∈ T, ∫ θ in Ioc 0 (2 * Real.pi), k θ * F (circleMap c r θ) x = (2 * Real.pi * I : ℂ) * F a x := by
    intro x hx
    have hd : DifferentiableOn ℂ (fun z => F z x) (closedBall c r) := (hhol x hx).mono (closedBall_subset_ball hrR)
    have h := hd.circleIntegral_sub_inv_smul ha
    rw [circleIntegral, intervalIntegral.integral_of_le Real.two_pi_pos.le] at h
    refine Eq.trans ?_ (h.trans (smul_eq_mul _ _))
    refine MeasureTheory.integral_congr_ae (Eventually.of_forall fun θ => ?_)
    simp only [hk, smul_eq_mul]
    ring
  rw [e1, hswap, ← MeasureTheory.integral_smul]
  refine MeasureTheory.setIntegral_congr_fun hT fun x hx => ?_
  simp only [smul_eq_mul]
  rw [e2 x hx]

/-- **Holomorphy of a parameter integral** under joint continuity, pointwise holomorphy and a uniform `L¹`
bound. -/
theorem s7g_f2_param {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    [SecondCountableTopology X] {m : Measure X} [SFinite m] {F : ℂ → X → ℂ} {T : Set X} (hT : MeasurableSet T) {c : ℂ} {R : ℝ}
    (hc : ContinuousOn (fun p : ℂ × X => F p.1 p.2) (closedBall c R ×ˢ T))
    (hhol : ∀ x ∈ T, DifferentiableOn ℂ (fun a => F a x) (ball c R))
    {M : ℝ} (hM : ∀ a ∈ closedBall c R, ∫⁻ x in T, ‖F a x‖ₑ ∂m ≤ ENNReal.ofReal M) :
    DifferentiableOn ℂ (fun a => ∫ x in T, F a x ∂m) (ball c R) := by
  intro a ha
  have hda : dist a c < R := ha
  have hd0 := dist_nonneg (x := a) (y := c)
  set r : ℝ := (dist a c + R) / 2 with hrdef
  have hr0 : 0 < r := by rw [hrdef]; linarith
  have hrR : r < R := by rw [hrdef]; linarith
  have har : a ∈ ball c r := by rw [mem_ball, hrdef]; linarith
  have hG := s7g_f2_Gint hT hr0 hrR.le hc hM
  have hci : CircleIntegrable (fun z => ∫ x in T, F z x ∂m) c r :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le Real.two_pi_pos.le).2 hG.integral_prod_left
  set r' : NNReal := ⟨r, hr0.le⟩ with hr'
  have hps := hasFPowerSeriesOn_cauchy_integral (R := r') hci (by
    show (0 : ℝ) < r
    exact hr0)
  have hmem : a ∈ Metric.eball c (r' : ENNReal) := by
    rw [Metric.eball_coe]
    exact har
  have hdo := (hps.differentiableOn a hmem).differentiableAt (Metric.isOpen_eball.mem_nhds hmem)
  have hev : (fun a' => ∫ x in T, F a' x ∂m) =ᶠ[𝓝 a]
      fun w => (2 * Real.pi * I : ℂ)⁻¹ • ∮ z in C(c, (r' : ℝ)), (z - w)⁻¹ • ∫ x in T, F z x ∂m := by
    filter_upwards [isOpen_ball.mem_nhds har] with w hw
    rw [show ((r' : ℝ)) = r from rfl, ← s7g_f2_cauchy hT hr0 hrR hc hhol hM hw, smul_smul,
      inv_mul_cancel₀ Complex.two_pi_I_ne_zero, one_smul]
  exact (hdo.congr_of_eventuallyEq hev).differentiableWithinAt


/-- The double Cauchy formula for the mixed partial of a `C²` holomorphic function on a polydisc, as one integral
over the parameter torus `[0, 2π]²`. -/
theorem s7g_f2_dcauchy {Ψ : ℂ × ℂ → ℂ} {R r : ℝ} (hr : 0 < r) (hrR : r < R)
    (hΨ : ContDiffOn ℂ 2 Ψ (ball (0 : ℂ) R ×ˢ ball (0 : ℂ) R)) :
    (2 * Real.pi * I : ℂ) ^ 2 * deriv (fun b => deriv (fun a => Ψ (a, b)) 0) 0 =
      ∫ q, (deriv (circleMap 0 r) q.1 * (1 / circleMap 0 r q.1 ^ 2)) *
          (deriv (circleMap 0 r) q.2 * (1 / circleMap 0 r q.2 ^ 2)) *
          Ψ (circleMap 0 r q.2, circleMap 0 r q.1)
        ∂((volume.restrict (Ioc 0 (2 * Real.pi))).prod (volume.restrict (Ioc 0 (2 * Real.pi)))) := by
  have hU : IsOpen (ball (0 : ℂ) R ×ˢ ball (0 : ℂ) R) := isOpen_ball.prod isOpen_ball
  have hcl : ∀ a ∈ closedBall (0 : ℂ) r, ∀ b ∈ closedBall (0 : ℂ) r, (a, b) ∈ ball (0 : ℂ) R ×ˢ ball (0 : ℂ) R :=
    fun a ha b hb => ⟨closedBall_subset_ball hrR ha, closedBall_subset_ball hrR hb⟩
  have hdiff : ∀ P ∈ ball (0 : ℂ) R ×ˢ ball (0 : ℂ) R, DifferentiableAt ℂ Ψ P := fun P hP =>
    (hΨ.differentiableOn (by norm_num)).differentiableAt (hU.mem_nhds hP)
  have hFd : DifferentiableOn ℂ (fderiv ℂ Ψ) (ball (0 : ℂ) R ×ˢ ball (0 : ℂ) R) :=
    (hΨ.fderiv_of_isOpen hU (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)).differentiableOn (by norm_num)
  set k : ℝ → ℂ := fun θ => deriv (circleMap 0 r) θ * (1 / circleMap 0 r θ ^ 2) with hk
  have hcm : ∀ θ : ℝ, circleMap 0 r θ ∈ closedBall (0 : ℂ) r := fun θ => circleMap_mem_closedBall 0 hr.le θ
  -- the inner Cauchy formula
  have hin : ∀ b ∈ closedBall (0 : ℂ) r, (2 * Real.pi * I : ℂ) * deriv (fun a => Ψ (a, b)) 0 =
      ∫ θ in Ioc 0 (2 * Real.pi), k θ * Ψ (circleMap 0 r θ, b) := by
    intro b hb
    have hd : DifferentiableOn ℂ (fun a => Ψ (a, b)) (closedBall 0 r) := fun a ha =>
      (DifferentiableAt.comp (g := Ψ) (f := fun a : ℂ => (a, b)) a (hdiff _ (hcl a ha b hb))
        (differentiableAt_id.prodMk (differentiableAt_const b))).differentiableWithinAt
    have h := hd.deriv_eq_smul_circleIntegral hr
    rw [circleIntegral, intervalIntegral.integral_of_le Real.two_pi_pos.le] at h
    rw [← smul_eq_mul, ← h]
    refine integral_congr_ae (Eventually.of_forall fun θ => ?_)
    simp only [hk, smul_eq_mul, sub_zero]
    ring
  -- the slice derivative is holomorphic in `b`
  set g : ℂ → ℂ := fun b => deriv (fun a => Ψ (a, b)) 0 with hgd
  have hg : DifferentiableOn ℂ g (closedBall 0 r) := by
    intro b hb
    have hb' : b ∈ ball (0 : ℂ) R := closedBall_subset_ball hrR hb
    have hev : g =ᶠ[𝓝 b] fun b' => fderiv ℂ Ψ (0, b') (1, 0) := by
      filter_upwards [isOpen_ball.mem_nhds hb'] with b' hb''
      have h0 : ((0 : ℂ), b') ∈ ball (0 : ℂ) R ×ˢ ball (0 : ℂ) R := ⟨mem_ball_self (hr.trans hrR), hb''⟩
      exact (HasFDerivAt.comp_hasDerivAt (l := Ψ) (f := fun a : ℂ => (a, b')) (0 : ℂ) (hdiff _ h0).hasFDerivAt
        ((hasDerivAt_id (0 : ℂ)).prodMk (hasDerivAt_const (0 : ℂ) b'))).deriv
    have h0 : ((0 : ℂ), b) ∈ ball (0 : ℂ) R ×ˢ ball (0 : ℂ) R := ⟨mem_ball_self (hr.trans hrR), hb'⟩
    have hd1 : DifferentiableAt ℂ (fun b' : ℂ => fderiv ℂ Ψ (0, b')) b :=
      DifferentiableAt.comp (g := fderiv ℂ Ψ) (f := fun b' : ℂ => ((0 : ℂ), b')) b
        (hFd.differentiableAt (hU.mem_nhds h0)) ((differentiableAt_const _).prodMk differentiableAt_id)
    exact ((hd1.clm_apply (differentiableAt_const _)).congr_of_eventuallyEq hev).differentiableWithinAt
  have hout := hg.deriv_eq_smul_circleIntegral hr
  rw [circleIntegral, intervalIntegral.integral_of_le Real.two_pi_pos.le] at hout
  -- integrability on the torus
  have hkc : Continuous k := by
    have e : k = fun θ => circleMap 0 r θ * I * (1 / circleMap 0 r θ ^ 2) := by
      rw [hk]
      funext θ
      rw [deriv_circleMap]
    have hne : ∀ θ : ℝ, circleMap 0 r θ ^ 2 ≠ 0 := fun θ => pow_ne_zero _ (by
      intro h
      have := norm_circleMap_zero r θ
      rw [h, norm_zero, abs_of_pos hr] at this
      linarith)
    rw [e]
    exact ((continuous_circleMap 0 r).mul continuous_const).mul (continuous_const.div
      ((continuous_circleMap 0 r).pow 2) hne)
  have hcont : Continuous fun q : ℝ × ℝ => k q.1 * k q.2 * Ψ (circleMap 0 r q.2, circleMap 0 r q.1) :=
    ((hkc.comp continuous_fst).mul (hkc.comp continuous_snd)).mul
      (hΨ.continuousOn.comp_continuous (((continuous_circleMap 0 r).comp continuous_snd).prodMk
        ((continuous_circleMap 0 r).comp continuous_fst)) fun q => hcl _ (hcm _) _ (hcm _))
  obtain ⟨B, hB⟩ := ((isCompact_closedBall (0 : ℂ) r).prod (isCompact_closedBall (0 : ℂ) r)).exists_bound_of_continuousOn
    (hΨ.continuousOn.mono fun P hP => hcl _ hP.1 _ hP.2)
  have hkb : ∀ θ : ℝ, ‖k θ‖ ≤ 1 / r := by
    intro θ
    rw [hk]
    simp only []
    rw [deriv_circleMap, norm_mul, norm_mul, norm_I, mul_one, norm_div, norm_one, norm_pow, norm_circleMap_zero,
      abs_of_pos hr]
    apply le_of_eq
    field_simp
  have hint : Integrable (fun q : ℝ × ℝ => k q.1 * k q.2 * Ψ (circleMap 0 r q.2, circleMap 0 r q.1))
      ((volume.restrict (Ioc 0 (2 * Real.pi))).prod (volume.restrict (Ioc 0 (2 * Real.pi)))) := by
    refine Integrable.of_bound hcont.aestronglyMeasurable (1 / r * (1 / r) * B) (Eventually.of_forall fun q => ?_)
    rw [norm_mul, norm_mul]
    have h3 := hB (circleMap 0 r q.2, circleMap 0 r q.1) ⟨hcm _, hcm _⟩
    have : 0 ≤ 1 / r := by positivity
    have hB0 : 0 ≤ B := (norm_nonneg _).trans h3
    exact mul_le_mul (mul_le_mul (hkb _) (hkb _) (norm_nonneg _) this) h3 (norm_nonneg _) (by positivity)
  rw [integral_prod _ hint]
  have e3 : (2 * Real.pi * I : ℂ) * deriv g 0 = ∫ θ in Ioc 0 (2 * Real.pi), k θ * g (circleMap 0 r θ) := by
    rw [← smul_eq_mul, ← hout]
    refine integral_congr_ae (Eventually.of_forall fun θ => ?_)
    simp only [hk, smul_eq_mul, sub_zero]
    ring
  show (2 * Real.pi * I : ℂ) ^ 2 * deriv g 0 = _
  rw [sq, mul_assoc, e3, ← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun θ => ?_)
  have hθ := hin _ (hcm θ)
  calc (2 * Real.pi * I : ℂ) * (k θ * g (circleMap 0 r θ))
      = k θ * ((2 * Real.pi * I : ℂ) * deriv (fun a => Ψ (a, circleMap 0 r θ)) 0) := by
        rw [hgd]
        ring
    _ = k θ * ∫ θ' in Ioc 0 (2 * Real.pi), k θ' * Ψ (circleMap 0 r θ', circleMap 0 r θ) := by rw [hθ]
    _ = _ := by
        rw [← integral_const_mul]
        refine integral_congr_ae (Eventually.of_forall fun θ' => ?_)
        simp only [hk]
        ring



/-- Regularity for `s7g_f2_mixed`: the parameter integral and each member of the family are `C²` on the open
polydisc. -/
theorem s7g_f2_mixC2 {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    [SecondCountableTopology X] {m : Measure X} [SFinite m] {F : ℂ × ℂ → X → ℂ} {T : Set X}
    (hT : MeasurableSet T) {R : ℝ}
    (hc : ContinuousOn (fun p : (ℂ × ℂ) × X => F p.1 p.2) ((closedBall (0 : ℂ) R ×ˢ closedBall (0 : ℂ) R) ×ˢ T))
    (hhol : ∀ x ∈ T, (∀ b ∈ closedBall (0 : ℂ) R, DifferentiableOn ℂ (fun a => F (a, b) x) (ball (0 : ℂ) R)) ∧
      ∀ a ∈ closedBall (0 : ℂ) R, DifferentiableOn ℂ (fun b => F (a, b) x) (ball (0 : ℂ) R))
    {M : ℝ} (hM : ∀ P ∈ closedBall (0 : ℂ) R ×ˢ closedBall (0 : ℂ) R, ∫⁻ x in T, ‖F P x‖ₑ ∂m ≤ ENNReal.ofReal M) :
    ContDiffOn ℂ 2 (fun P => ∫ x in T, F P x ∂m) (ball (0 : ℂ) R ×ˢ ball (0 : ℂ) R) ∧
      ∀ x ∈ T, ContDiffOn ℂ 2 (fun P => F P x) (ball (0 : ℂ) R ×ˢ ball (0 : ℂ) R) := by
  have hU : IsOpen (ball (0 : ℂ) R ×ˢ ball (0 : ℂ) R) := isOpen_ball.prod isOpen_ball
  have hsub : ball (0 : ℂ) R ×ˢ ball (0 : ℂ) R ⊆ closedBall (0 : ℂ) R ×ˢ closedBall (0 : ℂ) R :=
    prod_mono ball_subset_closedBall ball_subset_closedBall
  have hp1 : ∀ b ∈ closedBall (0 : ℂ) R,
      DifferentiableOn ℂ (fun a => ∫ x in T, F (a, b) x ∂m) (ball (0 : ℂ) R) := fun b hb =>
    s7g_f2_param (F := fun a x => F (a, b) x) hT
      (hc.comp ((continuous_fst.prodMk continuous_const).prodMk continuous_snd).continuousOn
        fun p hp => ⟨⟨hp.1, hb⟩, hp.2⟩) (fun x hx => (hhol x hx).1 b hb) (fun a ha => hM (a, b) ⟨ha, hb⟩)
  have hp2 : ∀ a ∈ closedBall (0 : ℂ) R,
      DifferentiableOn ℂ (fun b => ∫ x in T, F (a, b) x ∂m) (ball (0 : ℂ) R) := fun a ha =>
    s7g_f2_param (F := fun b x => F (a, b) x) hT
      (hc.comp ((continuous_const.prodMk continuous_fst).prodMk continuous_snd).continuousOn
        fun p hp => ⟨⟨ha, hp.1⟩, hp.2⟩) (fun x hx => (hhol x hx).2 a ha) (fun b hb => hM (a, b) ⟨ha, hb⟩)
  have hbd : ∀ P ∈ closedBall (0 : ℂ) R ×ˢ closedBall (0 : ℂ) R, ‖∫ x in T, F P x ∂m‖ ≤ max M 0 := by
    intro P hP
    have h1 := (enorm_integral_le_lintegral_enorm (μ := m.restrict T) (F P)).trans (hM P hP)
    have h2 : ENNReal.ofReal ‖∫ x in T, F P x ∂m‖ ≤ ENNReal.ofReal (max M 0) := by
      rw [ofReal_norm]
      exact h1.trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))
    exact (ENNReal.ofReal_le_ofReal_iff (le_max_right _ _)).1 h2
  constructor
  · have h := s7g_h_contDiffOn hU 2 (fun P => ∫ x in T, F P x ∂m)
      (fun p hp => (hp1 p.2 (ball_subset_closedBall hp.2)).differentiableAt (isOpen_ball.mem_nhds hp.1))
      (fun p hp => (hp2 p.1 (ball_subset_closedBall hp.1)).differentiableAt (isOpen_ball.mem_nhds hp.2))
      (fun p hp => by
        obtain ⟨ρ, hρ, hs⟩ := Metric.isOpen_iff.1 hU p hp
        exact ⟨ρ, hρ, max M 0, fun q hq => hbd q (hsub (hs hq))⟩)
    simpa using h
  · intro x hx
    obtain ⟨Bx, hBx⟩ := ((isCompact_closedBall (0 : ℂ) R).prod (isCompact_closedBall (0 : ℂ) R)).exists_bound_of_continuousOn
      (hc.comp (continuous_id.prodMk continuous_const).continuousOn fun P hP =>
        (⟨hP, hx⟩ : (P, x) ∈ (closedBall (0 : ℂ) R ×ˢ closedBall (0 : ℂ) R) ×ˢ T))
    have h := s7g_h_contDiffOn hU 2 (fun P => F P x)
      (fun p hp => ((hhol x hx).1 p.2 (ball_subset_closedBall hp.2)).differentiableAt (isOpen_ball.mem_nhds hp.1))
      (fun p hp => ((hhol x hx).2 p.1 (ball_subset_closedBall hp.1)).differentiableAt (isOpen_ball.mem_nhds hp.2))
      (fun p hp => by
        obtain ⟨ρ, hρ, hs⟩ := Metric.isOpen_iff.1 hU p hp
        exact ⟨ρ, hρ, Bx, fun q hq => hBx q (hsub (hs hq))⟩)
    simpa using h

/-- The circle kernel `k(θ) = (d/dθ) c(θ) · c(θ)⁻²`, `c = circleMap 0 r`: continuity and the bound `1/r`. -/
theorem s7g_f2_kern {r : ℝ} (hr : 0 < r) :
    Continuous (fun θ : ℝ => deriv (circleMap 0 r) θ * (1 / circleMap 0 r θ ^ 2)) ∧
      ∀ θ : ℝ, ‖deriv (circleMap 0 r) θ * (1 / circleMap 0 r θ ^ 2)‖ ≤ 1 / r := by
  constructor
  · have e : (fun θ : ℝ => deriv (circleMap 0 r) θ * (1 / circleMap 0 r θ ^ 2)) =
        fun θ => circleMap 0 r θ * I * (1 / circleMap 0 r θ ^ 2) := by
      funext θ
      rw [deriv_circleMap]
    have hne : ∀ θ : ℝ, circleMap 0 r θ ^ 2 ≠ 0 := fun θ => pow_ne_zero _ (by
      intro h
      have := norm_circleMap_zero r θ
      rw [h, norm_zero, abs_of_pos hr] at this
      linarith)
    rw [e]
    exact ((continuous_circleMap 0 r).mul continuous_const).mul (continuous_const.div
      ((continuous_circleMap 0 r).pow 2) hne)
  · intro θ
    rw [deriv_circleMap, norm_mul, norm_mul, norm_I, mul_one, norm_div, norm_one, norm_pow, norm_circleMap_zero,
      abs_of_pos hr]
    apply le_of_eq
    field_simp

/-- Integrability on `[0, 2π]² × T` of the double-circle family. -/
theorem s7g_f2_mixint {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    [SecondCountableTopology X] {m : Measure X} [SFinite m] {F : ℂ × ℂ → X → ℂ} {T : Set X}
    (hT : MeasurableSet T) {R r : ℝ} (hr : 0 < r) (hrR : r < R)
    (hc : ContinuousOn (fun p : (ℂ × ℂ) × X => F p.1 p.2) ((closedBall (0 : ℂ) R ×ˢ closedBall (0 : ℂ) R) ×ˢ T))
    {M : ℝ} (hM : ∀ P ∈ closedBall (0 : ℂ) R ×ˢ closedBall (0 : ℂ) R, ∫⁻ x in T, ‖F P x‖ₑ ∂m ≤ ENNReal.ofReal M) :
    Integrable (fun p : (ℝ × ℝ) × X => (deriv (circleMap 0 r) p.1.1 * (1 / circleMap 0 r p.1.1 ^ 2)) *
        (deriv (circleMap 0 r) p.1.2 * (1 / circleMap 0 r p.1.2 ^ 2)) *
        F (circleMap 0 r p.1.2, circleMap 0 r p.1.1) p.2)
      (((volume.restrict (Ioc 0 (2 * Real.pi))).prod (volume.restrict (Ioc 0 (2 * Real.pi)))).prod
        (m.restrict T)) := by
  obtain ⟨hkc, hkb⟩ := s7g_f2_kern hr
  set k : ℝ → ℂ := fun θ => deriv (circleMap 0 r) θ * (1 / circleMap 0 r θ ^ 2) with hk
  have hcm : ∀ θ : ℝ, circleMap 0 r θ ∈ closedBall (0 : ℂ) R := fun θ =>
    closedBall_subset_closedBall hrR.le (circleMap_mem_closedBall 0 hr.le θ)
  have hmeas : ((volume.restrict (Ioc 0 (2 * Real.pi))).prod (volume.restrict (Ioc 0 (2 * Real.pi)))).prod
      (m.restrict T) =
      ((volume.prod volume).prod m).restrict ((Ioc 0 (2 * Real.pi) ×ˢ Ioc 0 (2 * Real.pi)) ×ˢ T) := by
    rw [Measure.prod_restrict, Measure.prod_restrict]
  have hkk : ∀ q : ℝ × ℝ, ‖k q.1 * k q.2‖ₑ ≤ ENNReal.ofReal (1 / r * (1 / r)) := by
    intro q
    rw [← ofReal_norm, norm_mul]
    exact ENNReal.ofReal_le_ofReal (mul_le_mul (hkb _) (hkb _) (norm_nonneg _) (by positivity))
  refine ⟨?_, ?_⟩
  · rw [hmeas]
    refine ContinuousOn.aestronglyMeasurable ?_ ((measurableSet_Ioc.prod measurableSet_Ioc).prod hT)
    refine (((hkc.comp (continuous_fst.comp continuous_fst)).mul
      (hkc.comp (continuous_snd.comp continuous_fst))).continuousOn).mul ?_
    exact hc.comp ((((continuous_circleMap 0 r).comp (continuous_snd.comp continuous_fst)).prodMk
      ((continuous_circleMap 0 r).comp (continuous_fst.comp continuous_fst))).prodMk continuous_snd).continuousOn
      fun p hp => ⟨⟨hcm _, hcm _⟩, hp.2⟩
  · calc _ ≤ ∫⁻ q, ∫⁻ x in T, ‖k q.1 * k q.2 * F (circleMap 0 r q.2, circleMap 0 r q.1) x‖ₑ ∂m
          ∂((volume.restrict (Ioc 0 (2 * Real.pi))).prod (volume.restrict (Ioc 0 (2 * Real.pi)))) :=
          lintegral_prod_le _
      _ ≤ ∫⁻ _q, ENNReal.ofReal (1 / r * (1 / r)) * ENNReal.ofReal M
          ∂((volume.restrict (Ioc 0 (2 * Real.pi))).prod (volume.restrict (Ioc 0 (2 * Real.pi)))) := by
          refine lintegral_mono fun q => ?_
          calc _ = ∫⁻ x in T, ‖k q.1 * k q.2‖ₑ * ‖F (circleMap 0 r q.2, circleMap 0 r q.1) x‖ₑ ∂m := by
                refine lintegral_congr fun x => ?_
                rw [enorm_mul]
            _ = ‖k q.1 * k q.2‖ₑ * ∫⁻ x in T, ‖F (circleMap 0 r q.2, circleMap 0 r q.1) x‖ₑ ∂m :=
                lintegral_const_mul' _ _ enorm_ne_top
            _ ≤ _ := mul_le_mul' (hkk q) (hM _ ⟨hcm _, hcm _⟩)
      _ < ⊤ := by
          rw [lintegral_const]
          exact ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top)
            (measure_lt_top _ _)

/-- The Fubini step of `s7g_f2_mixed`, abstracted. -/
theorem s7g_f2_abs {X : Type*} [MeasurableSpace X] {μ : Measure X} {ν : Measure (ℝ × ℝ)} [SFinite μ] [SFinite ν]
    {G : ℝ × ℝ → X → ℂ} (hG : Integrable (fun p : (ℝ × ℝ) × X => G p.1 p.2) (ν.prod μ)) {d : X → ℂ} {D c : ℂ}
    (hc : c ≠ 0) (hd : ∀ᵐ x ∂μ, c * d x = ∫ q, G q x ∂ν) (hD : c * D = ∫ q, ∫ x, G q x ∂μ ∂ν) :
    Integrable d μ ∧ D = ∫ x, d x ∂μ := by
  have hae : d =ᵐ[μ] fun x => c⁻¹ * ∫ q, G q x ∂ν := by
    filter_upwards [hd] with x hx
    rw [← hx, ← mul_assoc, inv_mul_cancel₀ hc, one_mul]
  refine ⟨(hG.integral_prod_right.const_mul _).congr hae.symm, ?_⟩
  apply mul_left_cancel₀ hc
  rw [hD, integral_congr_ae hae, integral_const_mul, ← mul_assoc, mul_inv_cancel₀ hc, one_mul]
  exact integral_integral_swap (f := G) hG

/-- STUB A. Mixed second derivative under the integral sign at the centre of a polydisc (double torus Cauchy +
Fubini), for a jointly continuous, separately holomorphic family with a uniform `L¹` bound. -/
theorem s7g_f2_mixed {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    [SecondCountableTopology X] {m : Measure X} [SFinite m] {F : ℂ × ℂ → X → ℂ} {T : Set X}
    (hT : MeasurableSet T) {R : ℝ} (hR : 0 < R)
    (hc : ContinuousOn (fun p : (ℂ × ℂ) × X => F p.1 p.2) ((closedBall (0 : ℂ) R ×ˢ closedBall (0 : ℂ) R) ×ˢ T))
    (hhol : ∀ x ∈ T, (∀ b ∈ closedBall (0 : ℂ) R, DifferentiableOn ℂ (fun a => F (a, b) x) (ball (0 : ℂ) R)) ∧
      ∀ a ∈ closedBall (0 : ℂ) R, DifferentiableOn ℂ (fun b => F (a, b) x) (ball (0 : ℂ) R))
    {M : ℝ} (hM : ∀ P ∈ closedBall (0 : ℂ) R ×ˢ closedBall (0 : ℂ) R, ∫⁻ x in T, ‖F P x‖ₑ ∂m ≤ ENNReal.ofReal M) :
    IntegrableOn (fun x => deriv (fun b => deriv (fun a => F (a, b) x) 0) 0) T m ∧
      deriv (fun b => deriv (fun a => ∫ x in T, F (a, b) x ∂m) 0) 0 =
        ∫ x in T, deriv (fun b => deriv (fun a => F (a, b) x) 0) 0 ∂m := by
  have hr : 0 < R / 2 := half_pos hR
  have hrR : R / 2 < R := half_lt_self hR
  obtain ⟨hΦ2, hF2⟩ := s7g_f2_mixC2 hT hc hhol hM
  obtain ⟨K, hK⟩ : ∃ K : ℝ × ℝ → ℂ, K = fun q => (deriv (circleMap 0 (R / 2)) q.1 * (1 / circleMap 0 (R / 2) q.1 ^ 2)) *
      (deriv (circleMap 0 (R / 2)) q.2 * (1 / circleMap 0 (R / 2) q.2 ^ 2)) := ⟨_, rfl⟩
  have hH : Integrable (fun p : (ℝ × ℝ) × X => K p.1 * F (circleMap 0 (R / 2) p.1.2, circleMap 0 (R / 2) p.1.1) p.2)
      (((volume.restrict (Ioc 0 (2 * Real.pi))).prod (volume.restrict (Ioc 0 (2 * Real.pi)))).prod
        (m.restrict T)) := by
    rw [hK]
    exact s7g_f2_mixint hT hr hrR hc hM
  refine s7g_f2_abs (G := fun q x => K q * F (circleMap 0 (R / 2) q.2, circleMap 0 (R / 2) q.1) x) hH
    (pow_ne_zero 2 Complex.two_pi_I_ne_zero) ?_ ?_
  · filter_upwards [ae_restrict_mem hT] with x hx
    rw [s7g_f2_dcauchy (Ψ := fun P => F P x) hr hrR (hF2 x hx), hK]
  · rw [s7g_f2_dcauchy (Ψ := fun P => ∫ x in T, F P x ∂m) hr hrR hΦ2, hK]
    refine integral_congr_ae (Eventually.of_forall fun q => ?_)
    simp only []
    rw [integral_const_mul]

end TakhtajanTeo
