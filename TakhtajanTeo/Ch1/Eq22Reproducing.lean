import TakhtajanTeo.Ch1.CuiBound
import TakhtajanTeo.Ch1.FundDomainReflect
import TakhtajanTeo.Ch1.Eq22Primitive
import TakhtajanTeo.Ch1.Eq22Primitives

/-! Analytic assembly for (2.2). The reflected weighted-area estimates below
are independent of boundary regularity; the full reproducing endpoint is not yet established. -/
open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal Classical Real ComplexConjugate
noncomputable section
namespace TakhtajanTeo
open LiZhongQC QCV

-- L1
theorem eq22_weighted_energy {f : ℂ → ℂ} {D : Set ℂ} {k : ℝ}
    (hf : IsKQC f D k) (G : ℂ → ℝ≥0∞) :
    (∫⁻ u in D, ENNReal.ofReal (‖dz f u‖^2)*G (f u)) ≤
      ENNReal.ofReal k*(∫⁻ v in f '' D, G v) := by
  rw [qcv_lintegral_image_eq hf,← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply lintegral_mono_ae
  filter_upwards [thm9_4_dilatation_ae hf] with u hu
  have hbound : ‖dz f u‖^2 ≤ k*jacobian f u := by
    have hh := mul_le_mul_of_nonneg_right hu
      (add_nonneg (norm_nonneg (dz f u)) (norm_nonneg (dzbar f u)))
    dsimp [jacobian]
    nlinarith [mul_nonneg (norm_nonneg (dz f u)) (norm_nonneg (dzbar f u))]
  calc ENNReal.ofReal (‖dz f u‖^2)*G (f u)
      ≤ ENNReal.ofReal (k*jacobian f u)*G (f u) :=
        mul_le_mul' (ENNReal.ofReal_le_ofReal hbound) le_rfl
    _ = _ := by rw [ENNReal.ofReal_mul (by linarith [hf.2.1]),mul_assoc]

-- L2
theorem eq22_antiholo_weighted_energy {h : ℂ → ℂ} {E : Set ℂ} {k : ℝ}
    (hh : IsKQC (fun u => conj (h u)) E k) (G : ℂ → ℝ≥0∞) :
    (∫⁻ u in E, ENNReal.ofReal (‖dzbar h u‖^2)*G (h u)) ≤
      ENNReal.ofReal k*(∫⁻ v in h '' E, G v) := by
  have he := eq22_weighted_energy hh (fun v => G (conj v))
  have heq : (∫⁻ u in E, ENNReal.ofReal (‖dzbar h u‖^2)*G (h u)) =
      ∫⁻ u in E, ENNReal.ofReal (‖dz (fun v => conj (h v)) u‖^2)*G (conj (conj (h u))) := by
    apply lintegral_congr_ae
    filter_upwards [thm9_3_differentiable_ae hh] with u hu
    have hdu : DifferentiableAt ℝ h u := by
      have hx := Complex.conjCLE.differentiableAt.comp u hu
      simpa only [Function.comp_def,Complex.conjCLE_apply,conj_conj] using hx
    rw [← (eq6_3 hdu).2,Complex.norm_conj,conj_conj]
  rw [heq]
  refine he.trans_eq ?_
  congr 1
  have himg : (fun u => conj (h u)) '' E = conj '' (h '' E) := (image_image _ _ _).symm
  rw [himg,fdr_lintegral_conj]
  simp only [conj_conj]

-- L3, with an arbitrary weight (in particular the original q/A2 weight).
theorem eq22_weighted_pullback {h : ℂ → ℂ} {E Ω : Set ℂ} {k : ℝ}
    (hh : IsKQC (fun u => conj (h u)) E k) (hmap : MapsTo h E Ω) (G : ℂ → ℝ≥0∞) :
    (∫⁻ u in E, ENNReal.ofReal (‖dzbar h u‖^2)*G (h u)) ≤
      ENNReal.ofReal k*(∫⁻ v in Ω, G v) := by
  exact (eq22_antiholo_weighted_energy hh G).trans
    (mul_le_mul' le_rfl (lintegral_mono_set (image_subset_iff.mpr hmap)))

/-- Finite target area gives globally finite antiholomorphic derivative energy,
even though the exterior source domain has infinite area. -/
theorem eq22_antiholo_energy_finite {h : ℂ → ℂ} {E Ω : Set ℂ} {k : ℝ}
    (hh : IsKQC (fun u => conj (h u)) E k) (hmap : MapsTo h E Ω)
    (hΩ : volume Ω < ∞) : (∫⁻ u in E, ENNReal.ofReal (‖dzbar h u‖^2)) < ∞ := by
  have he := eq22_weighted_pullback hh hmap (fun _ => (1 : ℝ≥0∞))
  simp only [mul_one,lintegral_const,Measure.restrict_apply_univ,one_mul] at he
  exact he.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hΩ)

/-- Convenient finite-square criterion, with the same real norm convention as (2.2). -/
theorem eq22_memLp_two {D : Set ℂ} {A : ℂ → ℂ}
    (hA : AEStronglyMeasurable A (volume.restrict D))
    (hfin : (∫⁻ u in D, ENNReal.ofReal (‖A u‖^2)) < ∞) : MemLp A 2 (volume.restrict D) := by
  rw [memLp_iff,eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top two_ne_zero ENNReal.ofNat_ne_top hA]
  simpa only [ENNReal.toReal_ofNat,ENNReal.rpow_two,← ofReal_norm,
    ← ENNReal.ofReal_pow (norm_nonneg _)] using hfin

-- L4: the geometric factor is an explicit remaining obligation, not an extra premise of eq_2_2.
theorem eq22_kernel_integrable_of_geometry {h q : ℂ → ℂ} {ρ : ℂ → ℝ}
    {E Ω : Set ℂ} {k : ℝ} (hh : IsKQC (fun u => conj (h u)) E k)
    (hmap : MapsTo h E Ω) (hq : ContinuousOn q Ω) (hρ : ContinuousOn ρ Ω)
    (hρpos : ∀ v ∈ Ω, 0 < ρ v) {z : ℂ}
    (hq2 : (∫⁻ v in Ω, ENNReal.ofReal (‖q v‖^2/(ρ v)^2)) < ∞)
    (hgeom : (∫⁻ u in E, ENNReal.ofReal (‖u-h u‖^4*(ρ (h u))^2/‖u-z‖^8)) < ∞) :
    IntegrableOn (fun u => q (h u)*(u-h u)^2*dzbar h u/(u-z)^4) E := by
  have hc : ContinuousOn h E := by
    have hc := Complex.continuous_conj.comp_continuousOn hh.2.2.1.1
    simpa only [Function.comp_def,conj_conj] using hc
  have hEm : MeasurableSet E := hh.1.measurableSet
  have hqm : AEStronglyMeasurable (fun u => q (h u)) (volume.restrict E) :=
    (hq.comp hc hmap).aestronglyMeasurable hEm
  have hρm : AEStronglyMeasurable (fun u => (ρ (h u) : ℂ)) (volume.restrict E) :=
    (Complex.continuous_ofReal.comp_continuousOn (hρ.comp hc hmap)).aestronglyMeasurable hEm
  let A : ℂ → ℂ := fun u => q (h u)*dzbar h u/(ρ (h u) : ℂ)
  let B : ℂ → ℂ := fun u => (u-h u)^2*(ρ (h u) : ℂ)/(u-z)^4
  have hAm : AEStronglyMeasurable A (volume.restrict E) :=
    ((hqm.aemeasurable.mul (measurable_dzbar h).aemeasurable).div hρm.aemeasurable).aestronglyMeasurable
  have hBm : AEStronglyMeasurable B (volume.restrict E) :=
    ((((continuousOn_id.sub hc).aestronglyMeasurable hEm).aemeasurable.pow_const 2 |>.mul hρm.aemeasurable).div
      ((measurable_id.sub_const z).pow_const 4).aemeasurable).aestronglyMeasurable
  have hAfin : (∫⁻ u in E, ENNReal.ofReal (‖A u‖^2)) < ∞ := by
    have he := eq22_weighted_pullback hh hmap (fun v => ENNReal.ofReal (‖q v‖^2/(ρ v)^2))
    have hid : (∫⁻ u in E, ENNReal.ofReal (‖A u‖^2)) =
        ∫⁻ u in E, ENNReal.ofReal (‖dzbar h u‖^2)*ENNReal.ofReal (‖q (h u)‖^2/(ρ (h u))^2) := by
      apply setLIntegral_congr_fun hEm
      intro u hu
      dsimp [A]
      rw [norm_div,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (hρpos _ (hmap hu)),
        ← ENNReal.ofReal_mul (sq_nonneg _)]
      congr 1
      simp only [div_pow,mul_pow,div_eq_mul_inv]
      ring
    rw [hid]
    exact he.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hq2)
  have hBfin : (∫⁻ u in E, ENNReal.ofReal (‖B u‖^2)) < ∞ := by
    convert hgeom using 1
    apply setLIntegral_congr_fun hEm
    intro u hu
    dsimp [B]
    rw [norm_div,norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (hρpos _ (hmap hu))]
    congr 1
    simp only [mul_pow,div_pow,← pow_mul,norm_pow]
  have hAB := (eq22_memLp_two hAm hAfin).integrable_mul (eq22_memLp_two hBm hBfin)
  apply hAB.congr
  filter_upwards [ae_restrict_mem hEm] with u hu
  have hr : (ρ (h u) : ℂ) ≠ 0 := by exact_mod_cast (hρpos _ (hmap hu)).ne'
  change A u*B u = _
  dsimp [A,B]
  simp only [div_eq_mul_inv]
  calc q (h u)*dzbar h u*(ρ (h u) : ℂ)⁻¹*((u-h u)^2*(ρ (h u) : ℂ)*((u-z)^4)⁻¹)
      = q (h u)*(u-h u)^2*dzbar h u*((ρ (h u) : ℂ)⁻¹*(ρ (h u) : ℂ))*((u-z)^4)⁻¹ := by ring
    _ = _ := by rw [inv_mul_cancel₀ hr,mul_one]

/-- On a large annulus the reflected primitive decays quadratically whenever
the reflected point and the three primitive values stay bounded. -/
theorem eq22_primitive_annulus_bound {h Q1 Q2 Q3 : ℂ → ℂ} {u z : ℂ} {B R : ℝ}
    (hB : 0 ≤ B) (hR : 1 ≤ R) (hz : 2*‖z‖ ≤ R) (hu : R ≤ ‖u‖) (hu' : ‖u‖ ≤ 2*R)
    (hh : ‖h u‖ ≤ R) (h1 : ‖Q1 (h u)‖ ≤ B) (h2 : ‖Q2 (h u)‖ ≤ B)
    (h3 : ‖Q3 (h u)‖ ≤ B) : ‖eq22Primitive h Q1 Q2 Q3 z u‖ ≤ 272*B/R^2 := by
  have hRp : 0 < R := by linarith
  have hd : ‖u-h u‖ ≤ 3*R := (norm_sub_le _ _).trans (by linarith)
  have hden : R/2 ≤ ‖u-z‖ := by linarith [norm_sub_norm_le u z]
  have hnum : ‖Q1 (h u)*(u-h u)^2+2*(Q2 (h u)*(u-h u))+2*Q3 (h u)‖ ≤ 17*B*R^2 := by
    calc ‖Q1 (h u)*(u-h u)^2+2*(Q2 (h u)*(u-h u))+2*Q3 (h u)‖
        ≤ ‖Q1 (h u)*(u-h u)^2‖+‖2*(Q2 (h u)*(u-h u))‖+‖2*Q3 (h u)‖ :=
          (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
      _ = ‖Q1 (h u)‖*‖u-h u‖^2+2*(‖Q2 (h u)‖*‖u-h u‖)+2*‖Q3 (h u)‖ := by
          norm_num [norm_mul,norm_pow]
      _ ≤ B*(3*R)^2+2*(B*(3*R))+2*B := by gcongr
      _ ≤ 17*B*R^2 := by
          have ha := mul_le_mul_of_nonneg_left (show R ≤ R^2 by nlinarith) hB
          have hb := mul_le_mul_of_nonneg_left (show 1 ≤ R^2 by nlinarith) hB
          nlinarith
  unfold eq22Primitive
  rw [norm_div,norm_pow]
  calc _ ≤ (17*B*R^2)/(R/2)^4 := div_le_div₀ (by positivity) hnum (by positivity)
          (pow_le_pow_left₀ (by positivity) hden 4)
    _ = 272*B/R^2 := by field_simp; ring

/-- The outer cutoff error is O(1/R), uniformly in an arbitrary bounded
inner cutoff supported in the exterior domain. This is independent of the unresolved boundary limit. -/
theorem eq22_outer_error_bound {h Q1 Q2 Q3 θ χ : ℂ → ℂ} {E : Set ℂ} {z : ℂ} {B M R : ℝ}
    (hB : 0 ≤ B) (hM : 0 ≤ M) (hR : 1 ≤ R) (hz : 2*‖z‖ ≤ R)
    (hθ : ∀ u, ‖θ u‖ ≤ 1) (hθ0 : ∀ u, u ∉ E → θ u = 0)
    (hχ1 : ∀ u, ‖u‖ ≤ R → χ u = 1) (hχd : ∀ u, ‖dzbar χ u‖ ≤ M/R)
    (hbound : ∀ u ∈ E, R ≤ ‖u‖ → ‖u‖ ≤ 2*R →
      ‖h u‖ ≤ R ∧ ‖Q1 (h u)‖ ≤ B ∧ ‖Q2 (h u)‖ ≤ B ∧ ‖Q3 (h u)‖ ≤ B) :
    ‖∫ u in ball (0 : ℂ) (2*R), θ u*eq22Primitive h Q1 Q2 Q3 z u*dzbar χ u‖ ≤
      1088*π*B*M/R := by
  have hRp : 0 < R := by linarith
  have hb : ∀ u ∈ ball (0 : ℂ) (2*R),
      ‖θ u*eq22Primitive h Q1 Q2 Q3 z u*dzbar χ u‖ ≤ 272*B*M/R^3 := by
    intro u hu
    by_cases huE : u ∈ E
    · by_cases huR : ‖u‖ < R
      · have hd : dzbar χ u = 0 := CUI.cui_dzbar_plateau (c := 0)
          (fun v hv => hχ1 v (by simpa using hv.le)) (by simpa using huR)
        rw [hd,mul_zero,norm_zero]
        positivity
      · obtain ⟨hh,h1,h2,h3⟩ := hbound u huE (not_lt.mp huR) (mem_ball_zero_iff.mp hu).le
        have hp := eq22_primitive_annulus_bound hB hR hz (not_lt.mp huR)
          (mem_ball_zero_iff.mp hu).le hh h1 h2 h3
        calc ‖θ u*eq22Primitive h Q1 Q2 Q3 z u*dzbar χ u‖
            = ‖θ u‖*‖eq22Primitive h Q1 Q2 Q3 z u‖*‖dzbar χ u‖ := by rw [norm_mul,norm_mul]
          _ ≤ 1*(272*B/R^2)*(M/R) := mul_le_mul
            (mul_le_mul (hθ u) hp (norm_nonneg _) (by positivity)) (hχd u) (norm_nonneg _) (by positivity)
          _ = 272*B*M/R^3 := by field_simp
    · rw [hθ0 u huE,zero_mul,zero_mul,norm_zero]
      positivity
  have hi := norm_setIntegral_le_of_norm_le_const_ae
    (measure_ball_lt_top : volume (ball (0 : ℂ) (2*R)) < ∞)
    ((ae_restrict_mem measurableSet_ball).mono (fun u hu => hb u hu))
  apply hi.trans_eq
  simp only [Measure.real,Complex.volume_ball,ENNReal.toReal_mul,ENNReal.toReal_pow,
    ENNReal.coe_toReal,NNReal.coe_real_pi,ENNReal.toReal_ofReal (show 0 ≤ 2*R by positivity)]
  field_simp
  <;> ring

/-- Final limit assembly. The boundary trace is deliberately explicit here;
it must be proved for the actual reflection before this can close (2.2). -/
theorem eq22_reproducing_of_cutoffs {E : Set ℂ} {K P : ℂ → ℂ} {χ : ℕ → ℂ → ℂ} {qz : ℂ}
    (hE : MeasurableSet E) (hK : IntegrableOn K E)
    (hχm : ∀ n, AEStronglyMeasurable (χ n) (volume.restrict E))
    (hχb : ∀ n u, u ∈ E → ‖χ n u‖ ≤ 1)
    (hχt : ∀ u ∈ E, Tendsto (fun n => χ n u) atTop (𝓝 1))
    (hS : ∀ n, (∫ u in E, χ n u*K u) = -(∫ u in E, P u*dzbar (χ n) u))
    (htrace : Tendsto (fun n => ∫ u in E, P u*dzbar (χ n) u) atTop (𝓝 ((π : ℂ)*qz/3))) :
    qz = -(3/π)*(∫ u in E, K u) := by
  have hmain : Tendsto (fun n => ∫ u in E, χ n u*K u) atTop (𝓝 (∫ u in E, K u)) := by
    apply tendsto_integral_of_dominated_convergence (fun u => ‖K u‖)
    · intro n
      exact (hχm n).mul hK.aestronglyMeasurable
    · exact hK.norm
    · intro n
      filter_upwards [ae_restrict_mem hE] with u hu
      simpa only [norm_mul,one_mul] using mul_le_mul_of_nonneg_right (hχb n u hu) (norm_nonneg (K u))
    · filter_upwards [ae_restrict_mem hE] with u hu
      simpa only [one_mul] using (hχt u hu).mul_const (K u)
  have hlim := htrace.neg.congr (fun n => (hS n).symm)
  have heq := tendsto_nhds_unique hmain hlim
  rw [heq]
  have hp : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  field_simp

/-- The physical-domain density in conformal disk coordinates. -/
theorem eq22_density_formula {f : ℂ → ℂ} {Ω : Set ℂ}
    (hf : IsConformalOnto f unitDisc Ω) {w : ℂ} (hw : w ∈ unitDisc) :
    poincareDensity Ω (f w) = 2/((1-‖w‖^2)*‖deriv f w‖) := by
  let g := Function.invFunOn f unitDisc
  have hg : IsConformalOnto g Ω unitDisc := hf.symm isOpen_ball
  have hΩ : IsOpen Ω := hf.isOpen isOpen_ball
  have he := (poincareDensity_well_defined hΩ hg hg (hf.mapsTo hw)).2
  have hin : g (f w) = w := hf.2.1.leftInvOn_invFunOn hw
  have hmul : deriv f w*deriv g (f w) = 1 := by
    simpa only [g,unitDisc,mul_comm] using t1_deriv_invFunOn_mul (U := unitDisc) isOpen_ball hf hw
  have hn : ‖deriv g (f w)‖ = ‖deriv f w‖⁻¹ :=
    eq_inv_of_mul_eq_one_left (by rw [← norm_mul,mul_comm (deriv g (f w)),hmul,norm_one])
  rw [he,hin,hn]
  simp only [div_eq_mul_inv,mul_inv]
  ring

/-- Weighted quadratic-differential mass is invariant under the conformal disk chart. -/
theorem eq22_pullback_mass {f q : ℂ → ℂ} {Ω : Set ℂ}
    (hf : IsConformalOnto f unitDisc Ω) :
    (∫⁻ v in Ω, ENNReal.ofReal (‖q v‖^2/(poincareDensity Ω v)^2)) =
      ∫⁻ w in unitDisc, (‖q (f w)*deriv f w^2‖₊ : ℝ≥0∞)^2*ENNReal.ofReal (rho w)⁻¹ := by
  rw [← hf.2.2,r24_conformal_lintegral (U := unitDisc) isOpen_ball hf.1 hf.2.1]
  apply setLIntegral_congr_fun (show MeasurableSet unitDisc from isOpen_ball.measurableSet)
  intro w hw
  dsimp only
  rw [hf.2.2,eq22_density_formula hf hw]
  simp only [← enorm_eq_nnnorm,← ofReal_norm,norm_mul,norm_pow]
  rw [← ENNReal.ofReal_pow (by positivity),← ENNReal.ofReal_mul (sq_nonneg _),
    ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  have hd : ‖deriv f w‖ ≠ 0 := norm_ne_zero_iff.mpr (deriv_ne_zero_of_injOn isOpen_ball hf.1 hf.2.1 hw)
  have hδ : 1-‖w‖^2 ≠ 0 := by
    have hw1 := mem_ball_zero_iff.mp hw
    nlinarith [norm_nonneg w]
  unfold rho
  field_simp
  <;> ring

/-- The original physical-domain A2 hypothesis gives a bounded hyperbolic
supremum. No extension of q across the quasidisk boundary is asserted. -/
theorem eq22_A2_weighted_sup {f q : ℂ → ℂ} {Ω : Set ℂ}
    (hf : IsConformalOnto f unitDisc Ω) (hq : DifferentiableOn ℂ q Ω)
    (hq2 : (∫⁻ v in Ω, ENNReal.ofReal (‖q v‖^2/(poincareDensity Ω v)^2)) < ∞) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ v ∈ Ω, ‖q v‖ ≤ C*(poincareDensity Ω v)^2 := by
  let P : ℂ → ℂ := fun w => q (f w)*deriv f w^2
  have hPa : P ∈ A2fun unitDisc := by
    refine ⟨(hq.comp hf.1 hf.mapsTo).mul ((hf.1.deriv isOpen_ball).pow 2),?_⟩
    have hmass : (∫⁻ w in unitDisc, (‖P w‖₊ : ℝ≥0∞)^2*ENNReal.ofReal (rho w)⁻¹) < ∞ := by
      rwa [← eq22_pullback_mass hf]
    exact ENNReal.rpow_lt_top_of_nonneg (by norm_num : (0 : ℝ) ≤ 1/2) hmass.ne
  let ψ := toA2 unitDisc P
  have hψ : ∀ w ∈ unitDisc, A2.toFun ψ w = P w := fun w hw =>
    toA2_spec isOpen_ball (fun v hv => (mem_ball_zero_iff.mp hv).ne) hPa hw
  let B := Real.sqrt (12/π)*‖ψ‖
  have hB : 0 ≤ B := by dsimp [B]; positivity
  refine ⟨B/4,by positivity,?_⟩
  intro v hv
  obtain ⟨w,hw,rfl⟩ := hf.2.2 ▸ hv
  have hb := A2.weighted_pointwise_bound (Or.inl rfl) ψ hw
  rw [hψ w hw] at hb
  change (1-‖w‖^2)^2*‖q (f w)*deriv f w^2‖ ≤ B at hb
  rw [norm_mul,norm_pow] at hb
  have hw1 : ‖w‖ < 1 := mem_ball_zero_iff.mp hw
  have hδ : 0 < 1-‖w‖^2 := by nlinarith [norm_nonneg w]
  have hd : 0 < ‖deriv f w‖ := norm_pos_iff.mpr (deriv_ne_zero_of_injOn isOpen_ball hf.1 hf.2.1 hw)
  have hp : (1-‖w‖^2)^2*‖deriv f w‖^2*(poincareDensity Ω (f w))^2 = 4 := by
    rw [eq22_density_formula hf hw]
    field_simp
    <;> ring
  have hfour : 4*‖q (f w)‖ ≤ B*(poincareDensity Ω (f w))^2 := by
    calc 4*‖q (f w)‖ = ‖q (f w)‖*((1-‖w‖^2)^2*‖deriv f w‖^2*(poincareDensity Ω (f w))^2) := by rw [hp]; ring
      _ = ((1-‖w‖^2)^2*(‖q (f w)‖*‖deriv f w‖^2))*(poincareDensity Ω (f w))^2 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hb (sq_nonneg _)
  nlinarith

/-- Finite image area is the integrability needed for the radial boundary error. -/
theorem eq22_conformal_energy {f : ℂ → ℂ} {Ω : Set ℂ}
    (hf : IsConformalOnto f unitDisc Ω) (hΩ : Bornology.IsBounded Ω) :
    IntegrableOn (fun w => ‖deriv f w‖^2) unitDisc := by
  have hc := r24_conformal_lintegral (U := unitDisc) isOpen_ball hf.1 hf.2.1 (fun _ => (1 : ℝ≥0∞))
  have he : (∫⁻ w in unitDisc, ENNReal.ofReal (‖deriv f w‖^2)) = volume Ω := by
    simpa only [hf.2.2,mul_one,setLIntegral_one] using hc.symm
  obtain ⟨R,hR⟩ := hΩ.subset_closedBall (0 : ℂ)
  have hv : volume Ω < ∞ := (measure_mono hR).trans_lt measure_closedBall_lt_top
  have hd : AEStronglyMeasurable (deriv f) (volume.restrict unitDisc) :=
    (measurable_deriv f).aestronglyMeasurable
  exact (memLp_two_iff_integrable_sq_norm hd).mp (eq22_memLp_two hd (he ▸ hv))

/-- Boundary errors supported in shrinking disk collars vanish if they are
dominated by conformal area density. This uses no pointwise boundary trace or
monotonicity of circle energies. -/
theorem eq22_radial_error_tendsto_zero {f : ℂ → ℂ} {Ω : Set ℂ}
    (hf : IsConformalOnto f unitDisc Ω) (hΩ : Bornology.IsBounded Ω)
    {E : ℕ → ℂ → ℂ} {r : ℕ → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hr : Tendsto r atTop (𝓝 1))
    (hEm : ∀ n, AEStronglyMeasurable (E n) (volume.restrict unitDisc))
    (hEb : ∀ n w, w ∈ unitDisc → ‖E n w‖ ≤ C*‖deriv f w‖^2)
    (hE0 : ∀ n w, w ∈ unitDisc → ‖w‖^2 < r n → E n w = 0) :
    Tendsto (fun n => ∫ w in unitDisc, E n w) atTop (𝓝 0) := by
  have hlim : Tendsto (fun n => ∫ w in unitDisc, E n w) atTop
      (𝓝 (∫ w in unitDisc, (0 : ℂ))) := by
    apply tendsto_integral_of_dominated_convergence (fun w => C*‖deriv f w‖^2) hEm
    · exact (eq22_conformal_energy hf hΩ).const_mul C
    · intro n
      exact (ae_restrict_mem (show MeasurableSet unitDisc from isOpen_ball.measurableSet)).mono (fun w hw => hEb n w hw)
    · filter_upwards [ae_restrict_mem (show MeasurableSet unitDisc from isOpen_ball.measurableSet)] with w hw
      have hn : ‖w‖^2 < 1 := by
        have hw1 := mem_ball_zero_iff.mp hw
        nlinarith [norm_nonneg w]
      exact tendsto_const_nhds.congr' ((hr.eventually (lt_mem_nhds hn)).mono
        (fun n hnr => (hE0 n w hw hnr).symm))
  simpa only [integral_zero] using hlim

/-- Transport a smooth disk cutoff to the physical conformal image and extend
it by zero. Compact support strictly inside the disk supplies global smoothness;
no extension of the conformal map through the boundary is used. -/
theorem eq22_transport_cutoff {f b : ℂ → ℂ} {Ω : Set ℂ}
    (hf : IsConformalOnto f unitDisc Ω)
    (hb : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) b) (hbc : HasCompactSupport b)
    (hbs : tsupport b ⊆ unitDisc) (hbn : ∀ w, ‖b w‖ ≤ 1) :
    ∃ t : ℂ → ℂ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) t ∧ HasCompactSupport t ∧
      tsupport t ⊆ Ω ∧ (∀ w ∈ unitDisc, t (f w) = b w) ∧ (∀ v, ‖t v‖ ≤ 1) ∧
      ∀ w ∈ unitDisc, ‖dzbar t (f w)‖*‖deriv f w‖ = ‖dzbar b w‖ := by
  let g := Function.invFunOn f unitDisc
  let t := Ω.indicator (fun v => b (g v))
  let S := f '' tsupport b
  have hΩ : IsOpen Ω := hf.isOpen isOpen_ball
  have hg : IsConformalOnto g Ω unitDisc := hf.symm isOpen_ball
  have hSc : IsCompact S := hbc.image_of_continuousOn (hf.1.continuousOn.mono hbs)
  have hSΩ : S ⊆ Ω := image_subset_iff.mpr (fun w hw => hf.mapsTo (hbs hw))
  have hsupp : Function.support t ⊆ S := by
    intro v hv
    by_cases hvΩ : v ∈ Ω
    · have hgv : g v ∈ tsupport b := subset_closure (by
        change b (g v) ≠ 0
        intro hb0
        apply hv
        simp [t,hvΩ,hb0])
      have hvimg : v ∈ f '' unitDisc := by rw [hf.2.2]; exact hvΩ
      exact ⟨g v,hgv,Function.invFunOn_eq hvimg⟩
    · exact (hv (by simp [t,hvΩ])).elim
  have hts : tsupport t ⊆ S := closure_minimal hsupp hSc.isClosed
  have htc : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) t := by
    rw [contDiff_iff_contDiffAt]
    intro v
    by_cases hv : v ∈ Ω
    · have he : t =ᶠ[𝓝 v] fun x => b (g x) := by
        filter_upwards [hΩ.mem_nhds hv] with x hx
        exact indicator_of_mem hx _
      exact (hb.contDiffAt.comp v ((hg.1.analyticAt (hΩ.mem_nhds hv)).contDiffAt.restrict_scalars ℝ)).congr_of_eventuallyEq he
    · have he : t =ᶠ[𝓝 v] fun _ => (0 : ℂ) := by
        have hvS : v ∈ Sᶜ := fun hvS => hv (hSΩ hvS)
        filter_upwards [hSc.isClosed.isOpen_compl.mem_nhds hvS] with x hx
        by_contra htx
        exact hx (hsupp htx)
      exact contDiffAt_const.congr_of_eventuallyEq he
  have htf : ∀ w ∈ unitDisc, t (f w) = b w := by
    intro w hw
    simp only [t,indicator_of_mem (hf.mapsTo hw),show g (f w) = w from hf.2.1.leftInvOn_invFunOn hw]
  refine ⟨t,htc,hSc.of_isClosed_subset (isClosed_tsupport _) hts,
    hts.trans hSΩ,htf,?_,?_⟩
  · intro v
    by_cases hv : v ∈ Ω
    · simpa only [t,indicator_of_mem hv] using hbn (g v)
    · simp [t,hv]
  · intro w hw
    have he : (t ∘ f) =ᶠ[𝓝 w] b := by
      filter_upwards [isOpen_ball.mem_nhds hw] with x hx
      exact htf x hx
    have hd := (eq6_4 (hf.1.differentiableAt (isOpen_ball.mem_nhds hw))
      ((htc.differentiable (by simp)) (f w))).2
    have hde : dzbar (t ∘ f) w = dzbar b w := by unfold dzbar; rw [he.fderiv_eq]
    rw [hde] at hd
    simpa only [norm_mul,Complex.norm_conj] using (congrArg norm hd).symm

end TakhtajanTeo
