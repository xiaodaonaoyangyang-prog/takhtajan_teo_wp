import TakhtajanTeo.Ch1.Eq22RadialCutoff
import TakhtajanTeo.Ch1.Eq22BoundaryEstimate

/-! The actual target-domain boundary remainder tends to zero under reflection
collar geometry. No boundary trace of the holomorphic function is required. -/
open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal Classical Real ComplexConjugate
noncomputable section
namespace TakhtajanTeo
open LiZhongQC

-- T1
theorem eq22_punctured_pullback_measurable {f H : ℂ → ℂ} {Ω : Set ℂ}
    (hf : IsConformalOnto f unitDisc Ω) {p : ℂ} (hp : p ∈ Ω)
    (hH : ContinuousOn H (Ω \ {p})) :
    AEStronglyMeasurable (fun w => H (f w)) (volume.restrict unitDisc) := by
  obtain ⟨w₀,hw₀,he₀⟩ := hf.2.2 ▸ hp
  have hc : ContinuousOn (fun w => H (f w)) (unitDisc \ {w₀}) := by
    apply hH.comp (hf.1.continuousOn.mono sdiff_subset)
    intro w hw
    refine ⟨hf.mapsTo hw.1,?_⟩
    intro hn
    have he : f w = f w₀ := (mem_singleton_iff.mp hn).trans he₀.symm
    exact hw.2 (mem_singleton_iff.mpr (hf.2.1 hw.1 hw₀ he))
  have hm : volume.restrict (unitDisc \ {w₀}) = volume.restrict unitDisc :=
    Measure.restrict_congr_set (sdiff_null_ae_eq_self (measure_singleton w₀))
  simpa only [hm] using hc.aestronglyMeasurable (μ := volume)
    (isOpen_ball.measurableSet.diff (measurableSet_singleton w₀))

-- T2
theorem eq22_boundary_tail {f q H : ℂ → ℂ} {Ω : Set ℂ}
    (hf : IsConformalOnto f unitDisc Ω) (hΩ : Bornology.IsBounded Ω)
    {p : ℂ} (hp : p ∈ Ω) (hH : ContinuousOn H (Ω \ {p}))
    (hq : DifferentiableOn ℂ q Ω)
    (hq2 : (∫⁻ v in Ω, ENNReal.ofReal (‖q v‖^2/(poincareDensity Ω v)^2)) < ∞)
    {θ β : ℕ → ℂ → ℂ} {ε : ℕ → ℝ} {r η D : ℝ} {z : ℂ}
    (hε : ∀ n, 0 < ε n) (hεlim : Tendsto ε atTop (𝓝 0))
    (hwidth : ∀ n, 2*ε n ≤ 1-r)
    (hθ : ∀ n, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (θ n))
    (hθd : ∀ n w, w ∈ unitDisc →
      ‖dzbar (θ n) (f w)‖*‖deriv f w‖ = ‖dzbar (eq22RadialCutoff (ε n)) w‖)
    (hβ : ∀ n, Continuous (β n)) (hβb : ∀ n v, ‖β n v‖ ≤ 1)
    (hD : 0 ≤ D) (hη : 0 < η)
    (hgeom : ∀ w ∈ unitDisc, r ≤ ‖w‖^2 →
      ‖H (f w)-f w‖*poincareDensity Ω (f w) ≤ D)
    (hsep : ∀ w ∈ unitDisc, r ≤ ‖w‖^2 →
      η ≤ ‖H (f w)-z‖ ∧ η ≤ ‖f w-z‖) :
    (∀ n, IntegrableOn (fun v =>
      q v*(H v-v)^3/((H v-z)^3*(v-z))*β n v*dzbar (θ n) v) Ω) ∧
    Tendsto (fun n => ∫ v in Ω,
      q v*(H v-v)^3/((H v-z)^3*(v-z))*β n v*dzbar (θ n) v)
      atTop (𝓝 0) := by
  obtain ⟨Q,hQ,hqQ⟩ := eq22_A2_weighted_sup hf hq hq2
  obtain ⟨M,hM,hMd⟩ := eq22_radial_cutoff_derivative
  let F : ℕ → ℂ → ℂ := fun n w => (‖deriv f w‖^2) •
    (q (f w)*(H (f w)-f w)^3/((H (f w)-z)^3*(f w-z))*β n (f w)*dzbar (θ n) (f w))
  have hDm : MeasurableSet unitDisc := isOpen_ball.measurableSet
  have hfm := hf.1.continuousOn.aestronglyMeasurable (μ := volume) hDm
  have hHm := eq22_punctured_pullback_measurable hf hp hH
  have hqm := (hq.continuousOn.comp hf.1.continuousOn hf.mapsTo).aestronglyMeasurable (μ := volume) hDm
  have hFm : ∀ n, AEStronglyMeasurable (F n) (volume.restrict unitDisc) := by
    intro n
    have hβm := ((hβ n).comp_continuousOn hf.1.continuousOn).aestronglyMeasurable (μ := volume) hDm
    have htm := ((continuous_dzbar ((hθ n).of_le (by norm_num))).comp_continuousOn
      hf.1.continuousOn).aestronglyMeasurable (μ := volume) hDm
    have hGm := (((hqm.aemeasurable.mul ((hHm.aemeasurable.sub hfm.aemeasurable).pow_const 3)).div
      (((hHm.aemeasurable.sub_const z).pow_const 3).mul (hfm.aemeasurable.sub_const z))).mul
      hβm.aemeasurable).mul htm.aemeasurable
    exact ((measurable_deriv f).norm.pow_const 2).aestronglyMeasurable.smul hGm.aestronglyMeasurable
  have hzero : ∀ n w, w ∈ unitDisc → ‖w‖^2 < 1-2*ε n → F n w = 0 := by
    intro n w hw hn
    have he := hθd n w hw
    rw [eq22_radial_cutoff_derivative_zero (hε n) hn,norm_zero] at he
    have hs : ‖deriv f w‖ ≠ 0 := norm_ne_zero_iff.mpr
      (deriv_ne_zero_of_injOn isOpen_ball hf.1 hf.2.1 hw)
    have ht : dzbar (θ n) (f w) = 0 := norm_eq_zero.mp ((mul_eq_zero.mp he).resolve_right hs)
    simp only [F,ht,mul_zero,smul_zero]
  have hbound : ∀ n w, w ∈ unitDisc → ‖F n w‖ ≤ (Q*D^3*M/η^4)*‖deriv f w‖^2 := by
    intro n w hw
    by_cases hn : ‖w‖^2 < 1-2*ε n
    · rw [hzero n w hw hn,norm_zero]
      positivity
    · have hcollar : 1-‖w‖^2 ≤ 2*ε n := by linarith [le_of_not_gt hn]
      have hwr : r ≤ ‖w‖^2 := by linarith [hwidth n]
      have hδ : 0 < 1-‖w‖^2 := by
        have hw1 := mem_ball_zero_iff.mp hw
        nlinarith [norm_nonneg w]
      have hs : 0 < ‖deriv f w‖ := norm_pos_iff.mpr
        (deriv_ne_zero_of_injOn isOpen_ball hf.1 hf.2.1 hw)
      have hρ : 0 < poincareDensity Ω (f w) := by
        rw [eq22_density_formula hf hw]
        positivity
      have hdensity : poincareDensity Ω (f w)*(1-‖w‖^2)*‖deriv f w‖ = 2 := by
        rw [eq22_density_formula hf hw]
        field_simp
      have hcut : ‖dzbar (θ n) (f w)‖*‖deriv f w‖ ≤ M/ε n := by
        rw [hθd n w hw]
        exact hMd (ε n) (hε n) w hw
      have hb := eq22_boundary_remainder_bound hρ hδ.le (hε n) hQ hD hM hη
        hdensity hcollar (hqQ (f w) (hf.mapsTo hw)) (hgeom w hw hwr) hcut
        (hsep w hw hwr).1 (hsep w hw hwr).2
      calc
        ‖F n w‖ = ‖β n (f w)‖*‖q (f w)*(H (f w)-f w)^3/
            ((H (f w)-z)^3*(f w-z))*dzbar (θ n) (f w)*deriv f w^2‖ := by
          simp only [F,norm_smul,norm_mul,norm_div,norm_pow,norm_norm]
          ring
        _ ≤ 1*((Q*D^3*M/η^4)*‖deriv f w‖^2) :=
          mul_le_mul (hβb n (f w)) hb (norm_nonneg _) zero_le_one
        _ = _ := one_mul _
  have hr : Tendsto (fun n => 1-2*ε n) atTop (𝓝 1) := by
    simpa using (tendsto_const_nhds.sub (hεlim.const_mul 2))
  have hlim := eq22_radial_error_tendsto_zero hf hΩ (by positivity : 0 ≤ Q*D^3*M/η^4)
    hr hFm hbound hzero
  constructor
  · intro n
    have hFi : IntegrableOn (F n) unitDisc :=
      ((eq22_conformal_energy hf hΩ).const_mul (Q*D^3*M/η^4)).mono' (hFm n)
        ((ae_restrict_mem hDm).mono (fun w hw => hbound n w hw))
    have hi := (ahP_integrableOn_image (U := unitDisc) isOpen_ball hf.1 hf.2.1
      (fun v => q v*(H v-v)^3/((H v-z)^3*(v-z))*β n v*dzbar (θ n) v)).mpr hFi
    rwa [hf.2.2] at hi
  · apply hlim.congr
    intro n
    have hi := ahP_integral_image (U := unitDisc) isOpen_ball hf.1 hf.2.1
      (fun v => q v*(H v-v)^3/((H v-z)^3*(v-z))*β n v*dzbar (θ n) v)
    rw [hf.2.2] at hi
    exact hi.symm

end TakhtajanTeo
