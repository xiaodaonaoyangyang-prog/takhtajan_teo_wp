import LiZhongQC.Ch02.S13_Representation
import TakhtajanTeo.Basic
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.RemovableSingularity

/-!
# Ch1/QCVariationPlane — plane-normalized quasiconformal variation (foundation)

Owner: 下属5. Imports only `Basic` and LiZhongQC (immune to the Model A/B refactor of S1_1/S1_2).

* A  Gateaux ⇒ Fréchet holomorphy for locally bounded maps between complex Banach spaces
  (`qcv_gateaux_to_frechet`), with one-variable Cauchy/Schwarz estimates (`qcv_taylor2`).
-/

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal ComplexConjugate Real BoundedContinuousFunction

noncomputable section

namespace TakhtajanTeo
namespace QCV

open LiZhongQC

/-- Uniform coefficient estimates for the perturbation `g₀ + h`, `‖h‖∞ ≤ ε ≤ r` (constants independent of `h`). -/
theorem qcv_coeff_uniform {g₀ f₀ : ℂ → ℂ} {k r : ℝ} (hk₀ : 0 ≤ k) (hr : 0 < r) (hkr : k + r < 1)
    (hg₀ : IsBeltramiCoeff g₀ univ k) (hq : IsQuasiconformal f₀ univ) (himg : f₀ '' univ = univ) :
    ∃ C₃ C₂ : ℝ, 0 < C₃ ∧ ∀ (h : ℂ → ℂ) (ε : ℝ), 0 < ε → ε ≤ r → IsBeltramiCoeff h univ ε →
      IsBeltramiCoeff (ahT_dot h g₀ f₀) univ (C₃ * ε) ∧
      IsBeltramiCoeff (ahQuot (fun u => g₀ u + h u) g₀ f₀) univ (C₃ * ε) ∧
      IsBeltramiCoeff (fun w => ahQuot (fun u => g₀ u + h u) g₀ f₀ w - ahT_dot h g₀ f₀ w) univ (C₂ * ε ^ 2) := by
  have hqmp := ahT_qmp_inv hq himg
  set k' : ℝ := k + r with hk'
  have hk'0 : 0 ≤ k' := by linarith
  have hk'1 : k' < 1 := hkr
  have hk2 : 0 < 1 - k' ^ 2 := by nlinarith
  obtain ⟨hg₀m, hg₀b⟩ := hg₀
  rw [Measure.restrict_univ] at hg₀m hg₀b
  have hdzm : AEStronglyMeasurable (dz f₀) volume := (measurable_dz f₀).aestronglyMeasurable
  have hρm : AEStronglyMeasurable (fun z => dz f₀ z / conj (dz f₀ z)) volume :=
    hdzm.div₀ (Complex.continuous_conj.comp_aestronglyMeasurable hdzm)
  refine ⟨1 / (1 - k' ^ 2), k' / (1 - k' ^ 2) ^ 2 + 1 / (1 - k' ^ 2), by positivity, ?_⟩
  intro h ε hε hεr hh
  obtain ⟨hhm, hhb⟩ := hh
  rw [Measure.restrict_univ] at hhm hhb
  have hae := hqmp.ae (hhb.and hg₀b)
  have hDm : AEStronglyMeasurable (ahT_dot h g₀ f₀) volume := by
    have hin : AEStronglyMeasurable (fun z => h z / (1 - conj (g₀ z) * g₀ z) *
        (dz f₀ z / conj (dz f₀ z))) volume :=
      (hhm.div₀ (aestronglyMeasurable_const.sub
        ((Complex.continuous_conj.comp_aestronglyMeasurable hg₀m).mul hg₀m))).mul hρm
    exact hin.comp_quasiMeasurePreserving hqmp
  have hQm : AEStronglyMeasurable (ahQuot (fun u => g₀ u + h u) g₀ f₀) volume := by
    have hin : AEStronglyMeasurable (fun z => ((g₀ z + h z) - g₀ z) /
        (1 - conj (g₀ z) * (g₀ z + h z)) * (dz f₀ z / conj (dz f₀ z))) volume :=
      ((((hg₀m.add hhm).sub hg₀m)).div₀ (aestronglyMeasurable_const.sub
        ((Complex.continuous_conj.comp_aestronglyMeasurable hg₀m).mul (hg₀m.add hhm)))).mul hρm
    exact hin.comp_quasiMeasurePreserving hqmp
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · rw [Measure.restrict_univ]; exact hDm
  · rw [Measure.restrict_univ]
    filter_upwards [hae] with w hw
    have := ahT_frac_le (x := h (Function.invFunOn f₀ univ w)) (a := g₀ (Function.invFunOn f₀ univ w))
      (b := g₀ (Function.invFunOn f₀ univ w)) (ρ := dz f₀ (Function.invFunOn f₀ univ w) / conj (dz f₀ (Function.invFunOn f₀ univ w))) (hk := hk'1) hk'0 (hw.2.trans (by linarith))
      (hw.2.trans (by linarith)) (ahT_norm_div_conj_le _) hw.1
    refine this.trans_eq ?_
    field_simp
  · rw [Measure.restrict_univ]; exact hQm
  · rw [Measure.restrict_univ]
    filter_upwards [hae] with w hw
    have := ahT_frac_le (x := (g₀ (Function.invFunOn f₀ univ w) + h (Function.invFunOn f₀ univ w)) -
        g₀ (Function.invFunOn f₀ univ w)) (a := g₀ (Function.invFunOn f₀ univ w) +
        h (Function.invFunOn f₀ univ w)) (b := g₀ (Function.invFunOn f₀ univ w)) (ρ := dz f₀ (Function.invFunOn f₀ univ w) / conj (dz f₀ (Function.invFunOn f₀ univ w))) (hk := hk'1) hk'0
      ((norm_add_le _ _).trans (by linarith [hw.1, hw.2])) (hw.2.trans (by linarith))
      (ahT_norm_div_conj_le _) (by simpa using hw.1)
    refine this.trans_eq ?_
    field_simp
  · rw [Measure.restrict_univ]
    exact hQm.sub hDm
  · rw [Measure.restrict_univ]
    filter_upwards [hae] with w hw
    have hεc : (ε : ℂ) ≠ 0 := by exact_mod_cast hε.ne'
    set z := Function.invFunOn f₀ univ w with hz
    have key := ahT_quot_second (a := g₀ z + h z) (b := g₀ z) (m := h z / (ε : ℂ)) (s := (ε : ℂ))
      (ρ := dz f₀ z / conj (dz f₀ z)) (k := k') (C := 1) hk'0 hk'1
      ((norm_add_le _ _).trans (by linarith [hw.1, hw.2])) (hw.2.trans (by linarith))
      (ahT_norm_div_conj_le _)
      (by simpa [Complex.norm_real, abs_of_pos hε] using hw.1)
      (by
        have : g₀ z + h z - g₀ z - (ε : ℂ) * (h z / (ε : ℂ)) = 0 := by field_simp; ring
        rw [this]; simp; positivity)
    have e : ahQuot (fun u => g₀ u + h u) g₀ f₀ w - ahT_dot h g₀ f₀ w =
        (g₀ z + h z - g₀ z) / (1 - conj (g₀ z) * (g₀ z + h z)) * (dz f₀ z / conj (dz f₀ z)) -
          (ε : ℂ) * (h z / (ε : ℂ) / (1 - conj (g₀ z) * g₀ z) * (dz f₀ z / conj (dz f₀ z))) := by
      simp only [ahQuot, ahT_dot, hz]
      field_simp
    rw [e]
    refine key.trans_eq ?_
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hε]
    ring

/-- `normalizedSolution` is a normalized solution when the coefficient is bounded by `k < 1`. -/
theorem qcv_ns_spec {m : ℂ → ℂ} {k : ℝ} (hk₀ : 0 ≤ k) (hk : k < 1) (hm : IsBeltramiCoeff m univ k) :
    IsNormalizedSolution (normalizedSolution m) m := by
  obtain ⟨f, hf, -, -⟩ := thm13_7_normalized_existence hk₀ hk hm
  have hex : ∃ f : ℂ → ℂ, IsNormalizedSolution f m := ⟨f, hf⟩
  unfold normalizedSolution
  rw [dif_pos hex]
  exact hex.choose_spec


/-- Uniform first variation of the plane-normalized solution at `g₀`, in the perturbation `h` (`‖h‖∞ ≤ ε`). -/
theorem qcv_plane_remainder {g₀ f₀ : ℂ → ℂ} {k : ℝ} (hk₀ : 0 ≤ k) (hk : k < 1)
    (hg₀ : IsBeltramiCoeff g₀ univ k) (hf₀ : IsNormalizedSolution f₀ g₀) (z : ℂ) :
    ∀ c > 0, ∃ δ > 0, ∀ (h : ℂ → ℂ) (ε : ℝ), 0 < ε → ε ≤ δ → IsBeltramiCoeff h univ ε →
      ‖normalizedSolution (fun u => g₀ u + h u) z - f₀ z - ahVar (ahT_dot h g₀ f₀) (f₀ z)‖ ≤ c * ε := by
  intro c hc
  set r : ℝ := (1 - k) / 2 with hrdef
  have hr : 0 < r := by have := sub_pos.2 hk; positivity
  have hkr : k + r < 1 := by rw [hrdef]; linarith
  obtain ⟨C₃, C₂, hC₃, hU⟩ := qcv_coeff_uniform hk₀ hr hkr hg₀ hf₀.1 hf₀.2.1
  obtain ⟨K, hK⟩ := hf₀.1
  have hinj : InjOn f₀ univ := hK.2.2.1.2.1
  have hleft : Function.invFunOn f₀ univ (f₀ z) = z := hinj.leftInvOn_invFunOn (mem_univ z)
  set w : ℂ := f₀ z with hwdef
  set Kw : ℝ := 1 / π * ∫ ζ, ‖ahKer w ζ‖ with hKw
  have hA : 0 < |Kw * C₂| + 1 := by positivity
  obtain ⟨δ₁, hδ₁, hFV⟩ := ah_first_variation w (c / (2 * C₃)) (div_pos hc (by linarith))
  refine ⟨min r (min (δ₁ / C₃) (c / (2 * (|Kw * C₂| + 1)))),
    lt_min hr (lt_min (div_pos hδ₁ hC₃) (div_pos hc (by linarith))), ?_⟩
  intro h ε hε hεδ hh
  have hεr : ε ≤ r := hεδ.trans (min_le_left _ _)
  have hεδ₁ : ε ≤ δ₁ / C₃ := hεδ.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hεc : ε ≤ c / (2 * (|Kw * C₂| + 1)) := hεδ.trans ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨hD, hQ, hS⟩ := hU h ε hε hεr hh
  have hk1 : k + ε < 1 := by linarith
  have hk10 : 0 ≤ k + ε := by linarith
  have hg₀' : IsBeltramiCoeff g₀ univ (k + ε) :=
    ⟨hg₀.1, by
      have := hg₀.2
      rw [Measure.restrict_univ] at this ⊢
      filter_upwards [this] with u hu using hu.trans (by linarith)⟩
  have hg₁ : IsBeltramiCoeff (fun u => g₀ u + h u) univ (k + ε) := by
    refine ⟨hg₀.1.add hh.1, ?_⟩
    have h1 := hg₀.2
    have h2 := hh.2
    rw [Measure.restrict_univ] at h1 h2 ⊢
    filter_upwards [h1, h2] with u hu1 hu2
    exact (norm_add_le _ _).trans (add_le_add hu1 hu2)
  have hf₁ := qcv_ns_spec hk10 hk1 hg₁
  have hG := (ah_quotient hk10 hk1 hg₁ hg₀' hf₁ hf₀).1
  have hε' : C₃ * ε ≤ δ₁ := by
    have := (le_div_iff₀ hC₃).1 hεδ₁
    linarith
  have h1 := hFV _ _ (C₃ * ε) (mul_pos hC₃ hε) hε' hQ hG
  have hcomp : (normalizedSolution (fun u => g₀ u + h u) ∘ Function.invFunOn f₀ univ) w =
      normalizedSolution (fun u => g₀ u + h u) z := by
    rw [Function.comp_apply, hleft]
  rw [hcomp] at h1
  set ν₂ : ℂ → ℂ := fun w' => ahQuot (fun u => g₀ u + h u) g₀ f₀ w' - ahT_dot h g₀ f₀ w' with hν₂
  have hlin : ahVar (ahQuot (fun u => g₀ u + h u) g₀ f₀) w = ahVar (ahT_dot h g₀ f₀) w + ahVar ν₂ w := by
    have e : ahQuot (fun u => g₀ u + h u) g₀ f₀ = fun ζ => (1 : ℂ) * ahT_dot h g₀ f₀ ζ + ν₂ ζ := by
      funext ζ; rw [hν₂]; ring
    rw [e]
    simpa using ah_var_linear hD hS 1 w
  rw [hlin] at h1
  have h2 := ah_var_bound w hS
  have hkey : Kw * (C₂ * ε ^ 2) ≤ c / 2 * ε := by
    have e1 : Kw * (C₂ * ε ^ 2) ≤ |Kw * C₂| * (ε * ε) := by
      have e : Kw * (C₂ * ε ^ 2) = Kw * C₂ * (ε * ε) := by ring
      rw [e]
      exact mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
    have e2 : (|Kw * C₂| + 1) * ε ≤ c / 2 := by
      have := (le_div_iff₀ (by positivity : (0 : ℝ) < 2 * (|Kw * C₂| + 1))).1 hεc
      linarith
    calc Kw * (C₂ * ε ^ 2) ≤ |Kw * C₂| * (ε * ε) := e1
      _ ≤ (|Kw * C₂| + 1) * ε * ε := by nlinarith [mul_self_nonneg ε]
      _ ≤ c / 2 * ε := mul_le_mul_of_nonneg_right e2 hε.le
  have h1' : c / (2 * C₃) * (C₃ * ε) = c / 2 * ε := by field_simp
  have htri : ‖normalizedSolution (fun u => g₀ u + h u) z - w - ahVar (ahT_dot h g₀ f₀) w‖ ≤
      ‖normalizedSolution (fun u => g₀ u + h u) z - w - (ahVar (ahT_dot h g₀ f₀) w + ahVar ν₂ w)‖ +
        ‖ahVar ν₂ w‖ := by
    have e : normalizedSolution (fun u => g₀ u + h u) z - w - ahVar (ahT_dot h g₀ f₀) w =
        (normalizedSolution (fun u => g₀ u + h u) z - w - (ahVar (ahT_dot h g₀ f₀) w + ahVar ν₂ w)) +
          ahVar ν₂ w := by ring
    rw [e]; exact norm_add_le _ _
  have h2' : ‖ahVar ν₂ w‖ ≤ Kw * (C₂ * ε ^ 2) := h2
  linarith


/-- `ahT_dot` of a bounded Beltrami coefficient is a bounded Beltrami coefficient. -/
theorem qcv_dot_beltrami {g₀ f₀ h : ℂ → ℂ} {k ε : ℝ} (hk₀ : 0 ≤ k) (hk : k < 1)
    (hg₀ : IsBeltramiCoeff g₀ univ k) (hq : IsQuasiconformal f₀ univ) (himg : f₀ '' univ = univ)
    (hh : IsBeltramiCoeff h univ ε) : IsBeltramiCoeff (ahT_dot h g₀ f₀) univ (ε / (1 - k ^ 2)) := by
  have hqmp := ahT_qmp_inv hq himg
  obtain ⟨hg₀m, hg₀b⟩ := hg₀
  obtain ⟨hhm, hhb⟩ := hh
  rw [Measure.restrict_univ] at hg₀m hg₀b hhm hhb
  have hdzm : AEStronglyMeasurable (dz f₀) volume := (measurable_dz f₀).aestronglyMeasurable
  have hρm : AEStronglyMeasurable (fun z => dz f₀ z / conj (dz f₀ z)) volume :=
    hdzm.div₀ (Complex.continuous_conj.comp_aestronglyMeasurable hdzm)
  refine ⟨?_, ?_⟩
  · rw [Measure.restrict_univ]
    have hin : AEStronglyMeasurable (fun z => h z / (1 - conj (g₀ z) * g₀ z) *
        (dz f₀ z / conj (dz f₀ z))) volume :=
      (hhm.div₀ (aestronglyMeasurable_const.sub
        ((Complex.continuous_conj.comp_aestronglyMeasurable hg₀m).mul hg₀m))).mul hρm
    exact hin.comp_quasiMeasurePreserving hqmp
  · rw [Measure.restrict_univ]
    filter_upwards [hqmp.ae (hhb.and hg₀b)] with w hw
    exact ahT_frac_le (ρ := dz f₀ (Function.invFunOn f₀ univ w) / conj (dz f₀ (Function.invFunOn f₀ univ w)))
      hk₀ hk hw.2 hw.2 (ahT_norm_div_conj_le _) hw.1

/-- `ahVar` only depends on the a.e.-class of the coefficient. -/
theorem qcv_ahVar_congr_ae {ν₁ ν₂ : ℂ → ℂ} (h : ν₁ =ᵐ[volume] ν₂) (w : ℂ) : ahVar ν₁ w = ahVar ν₂ w := by
  unfold ahVar
  congr 1
  refine integral_congr_ae ?_
  filter_upwards [h] with ζ hζ
  rw [hζ]

/-- `IsNormalizedSolution` only depends on the a.e.-class of the coefficient. -/
theorem qcv_isNS_congr {f m₁ m₂ : ℂ → ℂ} (h : m₁ =ᵐ[volume] m₂) (hf : IsNormalizedSolution f m₁) :
    IsNormalizedSolution f m₂ := by
  obtain ⟨a, b, c, d, e⟩ := hf
  refine ⟨a, b, c, d, ?_⟩
  filter_upwards [e, h] with z hz1 hz2
  rw [hz1, hz2]

/-- Uniqueness: `normalizedSolution m` is the normalized solution of `m` for `‖m‖∞ ≤ k < 1`. -/
theorem qcv_ns_eq {m f : ℂ → ℂ} {k : ℝ} (hk₀ : 0 ≤ k) (hk : k < 1) (hm : IsBeltramiCoeff m univ k)
    (hf : IsNormalizedSolution f m) : normalizedSolution m = f := by
  obtain ⟨F, -, -, huniq⟩ := thm13_7_normalized_existence hk₀ hk hm
  exact (huniq _ (qcv_ns_spec hk₀ hk hm)).trans (huniq _ hf).symm

/-- **Fréchet derivative of the plane-normalized solution** under a bounded a.e.-linear perturbation
`v ↦ T v` of the coefficient.  `L v = V[ν̇_v](f₀ z)`, `ν̇_v = ahT_dot (T v) g₀ f₀` (first variation). -/
theorem qcv_plane_hasFDerivAt {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {g₀ f₀ : ℂ → ℂ} {k : ℝ} (hk₀ : 0 ≤ k) (hk : k < 1)
    (hg₀ : IsBeltramiCoeff g₀ univ k) (hf₀ : IsNormalizedSolution f₀ g₀)
    (T : E → ℂ → ℂ) {M : ℝ} (hM : 0 ≤ M) (hT : ∀ v, IsBeltramiCoeff (T v) univ (M * ‖v‖))
    (hTlin : ∀ (a : ℂ) (v₁ v₂ : E), T (a • v₁ + v₂) =ᵐ[volume] fun u => a * T v₁ u + T v₂ u) (z : ℂ) :
    ∃ L : E →L[ℂ] ℂ, (∀ v, L v = ahVar (ahT_dot (T v) g₀ f₀) (f₀ z)) ∧
      HasFDerivAt (fun v : E => normalizedSolution (fun u => g₀ u + T v u) z) L 0 := by
  have hq := hf₀.1
  have himg := hf₀.2.1
  set w : ℂ := f₀ z with hw
  have hdot : ∀ v, IsBeltramiCoeff (ahT_dot (T v) g₀ f₀) univ (M * ‖v‖ / (1 - k ^ 2)) :=
    fun v => qcv_dot_beltrami hk₀ hk hg₀ hq himg (hT v)
  have hT0 : T 0 =ᵐ[volume] fun _ => (0 : ℂ) := by
    have := (hT 0).2
    rw [Measure.restrict_univ] at this
    filter_upwards [this] with u hu
    simpa using hu
  have hlinV : ∀ (a : ℂ) (v₁ v₂ : E), ahVar (ahT_dot (T (a • v₁ + v₂)) g₀ f₀) w =
      a * ahVar (ahT_dot (T v₁) g₀ f₀) w + ahVar (ahT_dot (T v₂) g₀ f₀) w := by
    intro a v₁ v₂
    have hqmp := ahT_qmp_inv hq himg
    have hae : ahT_dot (T (a • v₁ + v₂)) g₀ f₀ =ᵐ[volume]
        fun ζ => a * ahT_dot (T v₁) g₀ f₀ ζ + ahT_dot (T v₂) g₀ f₀ ζ := by
      filter_upwards [hqmp.ae (hTlin a v₁ v₂)] with ζ hζ
      simp only [ahT_dot]
      rw [hζ]; ring
    rw [qcv_ahVar_congr_ae hae w]
    exact ah_var_linear (hdot v₁) (hdot v₂) a w
  have hL0 : ahVar (ahT_dot (T 0) g₀ f₀) w = 0 := by
    have h := hlinV 1 0 0
    rw [smul_zero, zero_add, one_mul] at h
    linear_combination -h
  let Lm : E →ₗ[ℂ] ℂ :=
    { toFun := fun v => ahVar (ahT_dot (T v) g₀ f₀) w
      map_add' := fun v₁ v₂ => by
        have := hlinV 1 v₁ v₂
        simpa using this
      map_smul' := fun a v => by
        have := hlinV a v 0
        rw [add_zero, hL0, add_zero] at this
        simpa using this }
  set Kw : ℝ := 1 / π * ∫ ζ, ‖ahKer w ζ‖ with hKw
  have hbound : ∀ v, ‖Lm v‖ ≤ Kw * (M / (1 - k ^ 2)) * ‖v‖ := by
    intro v
    have h := ah_var_bound w (hdot v)
    calc ‖Lm v‖ ≤ Kw * (M * ‖v‖ / (1 - k ^ 2)) := h
      _ = Kw * (M / (1 - k ^ 2)) * ‖v‖ := by ring
  let L : E →L[ℂ] ℂ := LinearMap.mkContinuous Lm (Kw * (M / (1 - k ^ 2))) hbound
  refine ⟨L, fun v => rfl, ?_⟩
  have hm0 : IsBeltramiCoeff (fun u => g₀ u + T 0 u) univ k := by
    refine ⟨hg₀.1.add (hT 0).1, ?_⟩
    have h1 := hg₀.2
    rw [Measure.restrict_univ] at h1 ⊢
    filter_upwards [h1, hT0] with u hu1 hu2
    rw [hu2, add_zero]; exact hu1
  have hNS : IsNormalizedSolution f₀ (fun u => g₀ u + T 0 u) := by
    refine qcv_isNS_congr ?_ hf₀
    filter_upwards [hT0] with u hu
    rw [hu, add_zero]
  have F0 : normalizedSolution (fun u => g₀ u + T 0 u) z = f₀ z := by
    rw [qcv_ns_eq hk₀ hk hm0 hNS]
  rw [hasFDerivAt_iff_isLittleO_nhds_zero, Asymptotics.isLittleO_iff]
  intro c hc
  obtain ⟨δ, hδ, hrem⟩ := qcv_plane_remainder hk₀ hk hg₀ hf₀ z (c / (M + 1)) (by positivity)
  filter_upwards [Metric.ball_mem_nhds (0 : E) (show 0 < δ / (M + 1) by positivity)] with v hv
  rw [mem_ball_zero_iff] at hv
  by_cases hv0 : v = 0
  · subst hv0
    simp [F0]
  · have hvpos : 0 < ‖v‖ := norm_pos_iff.2 hv0
    have hε : 0 < (M + 1) * ‖v‖ := by positivity
    have hεδ : (M + 1) * ‖v‖ ≤ δ := by
      have := (lt_div_iff₀ (by positivity : (0 : ℝ) < M + 1)).1 hv
      nlinarith
    have hmono : IsBeltramiCoeff (T v) univ ((M + 1) * ‖v‖) := by
      refine ⟨(hT v).1, ?_⟩
      have := (hT v).2
      rw [Measure.restrict_univ] at this ⊢
      filter_upwards [this] with u hu
      exact hu.trans (by nlinarith)
    have h := hrem (T v) ((M + 1) * ‖v‖) hε hεδ hmono
    simp only [zero_add, F0]
    refine h.trans_eq ?_
    field_simp


/-- Change of variables through a quasiconformal map (lower integrals), as in LiZhongQC `fx_lintegral_image_eq`
(re-proved here to avoid importing the large `FluxRoute` module). -/
theorem qcv_lintegral_image_eq {g : ℂ → ℂ} {D : Set ℂ} {K : ℝ} (hg : IsKQC g D K) (G : ℂ → ℝ≥0∞) :
    ∫⁻ w in g '' D, G w = ∫⁻ z in D, ENNReal.ofReal (jacobian g z) * G (g z) := by
  have hD : MeasurableSet D := hg.1.measurableSet
  set A : Set ℂ := D ∩ {z | DifferentiableAt ℝ g z} with hAdef
  have hSm : MeasurableSet A := hD.inter (measurableSet_of_differentiableAt ℝ g)
  have hAD : A ⊆ D := inter_subset_left
  have hnull : volume (D \ A) = 0 := by
    have h := thm9_3_differentiable_ae hg
    rw [ae_restrict_iff' hD, ae_iff] at h
    exact measure_mono_null (fun z hz => fun h' => hz.2 ⟨hz.1, h' hz.1⟩) h
  have himg_null : volume (g '' (D \ A)) = 0 :=
    ac_n_volume_image_null_of_isKQC hg (fun z hz => hz.1) hnull
  have hcv := lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hSm
    (fun z hz => hz.2.hasFDerivAt.hasFDerivWithinAt) (hg.2.2.1.2.1.mono hAD) G
  have hset1 : (g '' D : Set ℂ) =ᵐ[volume] (g '' A : Set ℂ) := by
    refine ae_eq_set.2 ⟨measure_mono_null ?_ himg_null, by
      rw [sdiff_eq_empty.2 (image_mono hAD), measure_empty]⟩
    rintro _ ⟨⟨z, hz, rfl⟩, hzA⟩
    exact ⟨z, ⟨hz, fun h => hzA ⟨z, h, rfl⟩⟩, rfl⟩
  have hset2 : (A : Set ℂ) =ᵐ[volume] (D : Set ℂ) :=
    ae_eq_set.2 ⟨by rw [sdiff_eq_empty.2 hAD, measure_empty], hnull⟩
  calc ∫⁻ w in g '' D, G w = ∫⁻ w in g '' A, G w := setLIntegral_congr hset1
    _ = ∫⁻ z in A, ENNReal.ofReal |(fderiv ℝ g z).det| * G (g z) := hcv
    _ = ∫⁻ z in A, ENNReal.ofReal (jacobian g z) * G (g z) := by
        refine setLIntegral_congr_fun hSm ?_
        intro z hz
        dsimp only
        have e : (fderiv ℝ g z).det = jacobian g z := det_fderiv_eq_jacobian hz.2
        rw [e, abs_of_nonneg (ac_j_jacobian_nonneg hg hz.1 hz.2)]
    _ = ∫⁻ z in D, ENNReal.ofReal (jacobian g z) * G (g z) := setLIntegral_congr hset2

/-- The Jacobian pushes `volume` to `volume` under a quasiconformal self-map of the plane. -/
theorem qcv_map_jacobian {f : ℂ → ℂ} {K : ℝ} (hf : IsKQC f univ K) (himg : f '' univ = univ) :
    Measure.map f (volume.withDensity fun u => ENNReal.ofReal (jacobian f u)) = volume := by
  have hfc : Continuous f := continuousOn_univ.1 hf.2.2.1.1
  ext s hs
  rw [Measure.map_apply hfc.measurable hs, withDensity_apply _ (hfc.measurable hs)]
  have h := qcv_lintegral_image_eq hf (s.indicator fun _ => 1)
  rw [himg, Measure.restrict_univ, lintegral_indicator hs] at h
  simp only [lintegral_const, Measure.restrict_apply MeasurableSet.univ, univ_inter, one_mul] at h
  have h2 : ∫⁻ z, ENNReal.ofReal (jacobian f z) * (s.indicator (fun _ => (1 : ℝ≥0∞))) (f z) =
      ∫⁻ z in f ⁻¹' s, ENNReal.ofReal (jacobian f z) := by
    rw [← lintegral_indicator (hfc.measurable hs)]
    congr 1
    funext z
    by_cases hz : f z ∈ s <;> simp [Set.indicator, hz]
  rw [h2] at h
  exact h.symm

/-- Change of variables through a quasiconformal self-map of the plane (Bochner form). -/
theorem qcv_cov_integral {f : ℂ → ℂ} {K : ℝ} (hf : IsKQC f univ K) (himg : f '' univ = univ)
    (G : ℂ → ℂ) (hG : AEStronglyMeasurable G volume) :
    ∫ w, G w = ∫ u, (ENNReal.ofReal (jacobian f u)).toReal • G (f u) := by
  have hfc : Continuous f := continuousOn_univ.1 hf.2.2.1.1
  have hJm : Measurable fun u => ENNReal.ofReal (jacobian f u) :=
    ENNReal.measurable_ofReal.comp
      (((measurable_dz f).norm.pow_const 2).sub ((measurable_dzbar f).norm.pow_const 2))
  have hm := qcv_map_jacobian hf himg
  calc ∫ w, G w = ∫ w, G w ∂(Measure.map f (volume.withDensity fun u => ENNReal.ofReal (jacobian f u))) := by
        rw [hm]
    _ = ∫ u, G (f u) ∂(volume.withDensity fun u => ENNReal.ofReal (jacobian f u)) := by
        refine integral_map hfc.measurable.aemeasurable ?_
        rw [hm]; exact hG
    _ = ∫ u, (ENNReal.ofReal (jacobian f u)).toReal • G (f u) :=
        integral_withDensity_eq_integral_toReal_smul hJm (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top) _


/-- **First variation in source coordinates.** For `g₀` Beltrami with normalized solution `f₀`,
`V[ahT_dot h g₀ f₀](w) = -(1/π) ∬ h(u) K_w(f₀ u) (∂_z f₀ u)² d²u`. -/
theorem qcv_var_source {g₀ f₀ h : ℂ → ℂ} {k ε : ℝ} (hk₀ : 0 ≤ k) (hk : k < 1)
    (hg₀ : IsBeltramiCoeff g₀ univ k) (hf₀ : IsNormalizedSolution f₀ g₀)
    (hh : IsBeltramiCoeff h univ ε) (w : ℂ) :
    ahVar (ahT_dot h g₀ f₀) w = -(1 / π : ℂ) * ∫ u, h u * ahKer w (f₀ u) * dz f₀ u ^ 2 := by
  obtain ⟨⟨K, hK⟩, himg, -, -, hdil⟩ := hf₀
  have hq : IsQuasiconformal f₀ univ := ⟨K, hK⟩
  have hdot := qcv_dot_beltrami hk₀ hk hg₀ hq himg hh
  have hmeasG : AEStronglyMeasurable (fun ζ => ahT_dot h g₀ f₀ ζ * ahKer w ζ) volume := by
    have h1 : AEStronglyMeasurable (ahT_dot h g₀ f₀) volume := by
      simpa [Measure.restrict_univ] using hdot.1
    exact h1.mul (ahK_measurable w).aestronglyMeasurable
  unfold ahVar
  congr 1
  rw [qcv_cov_integral hK himg _ hmeasG]
  refine integral_congr_ae ?_
  have hJ := thm9_6_cor2_jacobian_pos hK
  rw [Measure.restrict_univ] at hJ
  have hg0b := hg₀.2
  rw [Measure.restrict_univ] at hg0b
  have hinj : InjOn f₀ univ := hK.2.2.1.2.1
  filter_upwards [hJ, hdil, hg0b] with u hJu hdu hgu
  have hφ : Function.invFunOn f₀ univ (f₀ u) = u := hinj.leftInvOn_invFunOn (mem_univ u)
  have hdzne : dz f₀ u ≠ 0 := by
    intro h0
    have : jacobian f₀ u ≤ 0 := by
      unfold jacobian
      rw [h0]
      simp
    linarith
  have hdzbar : dzbar f₀ u = g₀ u * dz f₀ u := by
    unfold complexDilatation at hdu
    rw [div_eq_iff hdzne] at hdu
    rw [hdu]
  have hA : (1 : ℂ) - conj (g₀ u) * g₀ u ≠ 0 := by
    have : ‖conj (g₀ u) * g₀ u‖ < 1 := by
      rw [norm_mul, Complex.norm_conj]; nlinarith [norm_nonneg (g₀ u)]
    intro h0
    have h1 : conj (g₀ u) * g₀ u = 1 := by linear_combination -h0
    rw [h1] at this; simp at this
  have hJc : (jacobian f₀ u : ℂ) = dz f₀ u * conj (dz f₀ u) * (1 - conj (g₀ u) * g₀ u) := by
    unfold jacobian
    rw [hdzbar, norm_mul]
    push_cast
    rw [Complex.mul_conj, mul_comm (conj (g₀ u)) (g₀ u), Complex.mul_conj]
    simp only [Complex.normSq_eq_norm_sq, Complex.ofReal_pow]
    push_cast
    ring
  have hcne : conj (dz f₀ u) ≠ 0 := (map_ne_zero _).2 hdzne
  simp only [ahT_dot, hφ]
  rw [ENNReal.toReal_ofReal hJu.le, Complex.real_smul, hJc]
  field_simp

/-! ### Two complex parameters -/

/-- General form: the two-parameter family with a bound `‖v.1 a + v.2 b‖∞ ≤ M‖v‖` and base bound `k < 1`. -/
theorem qcv_plane_two_param_general {a b : ℂ → ℂ} {M k : ℝ} (hM : 0 ≤ M) (hk₀ : 0 ≤ k) (hk : k < 1)
    {p₀ : ℂ × ℂ} (hg₀ : IsBeltramiCoeff (fun u => p₀.1 * a u + p₀.2 * b u) univ k)
    (hT : ∀ v : ℂ × ℂ, IsBeltramiCoeff (fun u => v.1 * a u + v.2 * b u) univ (M * ‖v‖)) (z : ℂ) :
    ∃ L : ℂ × ℂ →L[ℂ] ℂ, HasFDerivAt
      (fun p : ℂ × ℂ => normalizedSolution (fun u => p.1 * a u + p.2 * b u) z) L p₀ ∧
      ∀ v : ℂ × ℂ, L v = -(1 / π : ℂ) * ∫ u,
        (v.1 * a u + v.2 * b u) * ahKer (normalizedSolution (fun u => p₀.1 * a u + p₀.2 * b u) z)
          (normalizedSolution (fun u => p₀.1 * a u + p₀.2 * b u) u) *
          dz (normalizedSolution (fun u => p₀.1 * a u + p₀.2 * b u)) u ^ 2 := by
  obtain ⟨f₀, hf₀, -, -⟩ := thm13_7_normalized_existence hk₀ hk hg₀
  let T : ℂ × ℂ → ℂ → ℂ := fun v u => v.1 * a u + v.2 * b u
  have hT' : ∀ v, IsBeltramiCoeff (T v) univ (M * ‖v‖) := hT
  have hTlin : ∀ (c : ℂ) (v₁ v₂ : ℂ × ℂ), T (c • v₁ + v₂) =ᵐ[volume] fun u => c * T v₁ u + T v₂ u := by
    intro c v₁ v₂
    refine Eventually.of_forall fun u => ?_
    simp only [T, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    ring
  obtain ⟨L, hLv, hL⟩ := qcv_plane_hasFDerivAt hk₀ hk hg₀ hf₀ T hM hT' hTlin z
  have hfn : normalizedSolution (fun u => p₀.1 * a u + p₀.2 * b u) = f₀ :=
    qcv_ns_eq hk₀ hk hg₀ hf₀
  refine ⟨L, ?_, ?_⟩
  swap
  · intro v
    rw [hfn, hLv v]
    exact qcv_var_source hk₀ hk hg₀ hf₀ (hT v) (f₀ z)
  rw [hasFDerivAt_iff_isLittleO_nhds_zero]
  have h := hasFDerivAt_iff_isLittleO_nhds_zero.1 hL
  have e : ∀ v : ℂ × ℂ, (fun u => p₀.1 * a u + p₀.2 * b u + T v u) =
      fun u => (p₀ + v).1 * a u + (p₀ + v).2 * b u := by
    intro v; funext u; simp only [T, Prod.fst_add, Prod.snd_add]; ring
  have e0 : (fun u => p₀.1 * a u + p₀.2 * b u + T 0 u) = fun u => p₀.1 * a u + p₀.2 * b u := by
    funext u; simp [T]
  simpa [e, e0] using h

/-- Fréchet derivative in two complex parameters of `(e₁, e₂) ↦ normalizedSolution (e₁ a + e₂ b) z`
(the derivative is the first variation at the base point). -/
theorem qcv_plane_two_param_hasFDerivAt {a b : ℂ → ℂ} {ka kb : ℝ} (hka : 0 ≤ ka) (hkb : 0 ≤ kb)
    (ha : IsBeltramiCoeff a univ ka) (hb : IsBeltramiCoeff b univ kb) {p₀ : ℂ × ℂ}
    (hp : ‖p₀.1‖ * ka + ‖p₀.2‖ * kb < 1) (z : ℂ) :
    ∃ L : ℂ × ℂ →L[ℂ] ℂ, HasFDerivAt
      (fun p : ℂ × ℂ => normalizedSolution (fun u => p.1 * a u + p.2 * b u) z) L p₀ ∧
      ∀ v : ℂ × ℂ, L v = -(1 / π : ℂ) * ∫ u,
        (v.1 * a u + v.2 * b u) * ahKer (normalizedSolution (fun u => p₀.1 * a u + p₀.2 * b u) z)
          (normalizedSolution (fun u => p₀.1 * a u + p₀.2 * b u) u) *
          dz (normalizedSolution (fun u => p₀.1 * a u + p₀.2 * b u)) u ^ 2 := by
  set k : ℝ := ‖p₀.1‖ * ka + ‖p₀.2‖ * kb with hkdef
  have hk₀ : 0 ≤ k := by positivity
  have hg₀ : IsBeltramiCoeff (fun u => p₀.1 * a u + p₀.2 * b u) univ k := by
    refine ⟨?_, ?_⟩
    · rw [Measure.restrict_univ]
      have ha1 : AEStronglyMeasurable a volume := by simpa [Measure.restrict_univ] using ha.1
      have hb1 : AEStronglyMeasurable b volume := by simpa [Measure.restrict_univ] using hb.1
      exact (ha1.const_mul p₀.1).add (hb1.const_mul p₀.2)
    · have h1 := ha.2
      have h2 := hb.2
      rw [Measure.restrict_univ] at h1 h2 ⊢
      filter_upwards [h1, h2] with u hu1 hu2
      calc ‖p₀.1 * a u + p₀.2 * b u‖ ≤ ‖p₀.1 * a u‖ + ‖p₀.2 * b u‖ := norm_add_le _ _
        _ ≤ ‖p₀.1‖ * ka + ‖p₀.2‖ * kb := by
          rw [norm_mul, norm_mul]; gcongr
  have hT : ∀ v : ℂ × ℂ, IsBeltramiCoeff (fun u => v.1 * a u + v.2 * b u) univ ((ka + kb) * ‖v‖) := by
    intro v
    refine ⟨?_, ?_⟩
    · rw [Measure.restrict_univ]
      have ha1 : AEStronglyMeasurable a volume := by simpa [Measure.restrict_univ] using ha.1
      have hb1 : AEStronglyMeasurable b volume := by simpa [Measure.restrict_univ] using hb.1
      exact (ha1.const_mul v.1).add (hb1.const_mul v.2)
    · have h1 := ha.2
      have h2 := hb.2
      rw [Measure.restrict_univ] at h1 h2 ⊢
      filter_upwards [h1, h2] with u hu1 hu2
      calc ‖v.1 * a u + v.2 * b u‖ ≤ ‖v.1 * a u‖ + ‖v.2 * b u‖ := norm_add_le _ _
        _ ≤ ‖v‖ * ka + ‖v‖ * kb := by
          rw [norm_mul, norm_mul]
          gcongr
          · exact norm_fst_le v
          · exact norm_snd_le v
        _ = (ka + kb) * ‖v‖ := by ring
  exact qcv_plane_two_param_general (by positivity) hk₀ hp hg₀ hT z

/-- Holomorphy in two complex parameters. -/
theorem qcv_plane_two_param_holomorphic {a b : ℂ → ℂ} {ka kb : ℝ} (hka : 0 ≤ ka) (hkb : 0 ≤ kb)
    (ha : IsBeltramiCoeff a univ ka) (hb : IsBeltramiCoeff b univ kb) (z : ℂ) :
    DifferentiableOn ℂ (fun p : ℂ × ℂ => normalizedSolution (fun u => p.1 * a u + p.2 * b u) z)
      {p : ℂ × ℂ | ‖p.1‖ * ka + ‖p.2‖ * kb < 1} := by
  intro p hp
  obtain ⟨L, hL, -⟩ := qcv_plane_two_param_hasFDerivAt hka hkb ha hb hp z
  exact hL.differentiableAt.differentiableWithinAt


set_option linter.unusedSectionVars false

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

/-- Maximum modulus on a closed disk, from the circle bound. -/
theorem qcv_maxmod_closedBall {g : ℂ → F} {R C : ℝ} (hR : 0 < R)
    (hd : DifferentiableOn ℂ g (closedBall 0 R)) (hC : ∀ z ∈ sphere (0 : ℂ) R, ‖g z‖ ≤ C) :
    ∀ z ∈ closedBall (0 : ℂ) R, ‖g z‖ ≤ C := by
  intro z hz
  have hdc : DiffContOnCl ℂ g (ball (0 : ℂ) R) :=
    ⟨hd.mono ball_subset_closedBall, hd.continuousOn.mono (by rw [closure_ball _ hR.ne'])⟩
  refine Complex.norm_le_of_forall_mem_frontier_norm_le (Metric.isBounded_ball) hdc ?_ ?_
  · intro w hw
    rw [frontier_ball _ hR.ne'] at hw
    exact hC w hw
  · rwa [closure_ball _ hR.ne']

/-- Second-order Taylor bound with Cauchy constants for a bounded holomorphic vector function on a closed disk. -/
theorem qcv_taylor2 {φ : ℂ → F} {R M : ℝ} (hR : 0 < R) (hd : DifferentiableOn ℂ φ (closedBall 0 R))
    (hM : ∀ t ∈ closedBall (0 : ℂ) R, ‖φ t‖ ≤ M) :
    ‖deriv φ 0‖ ≤ 2 * M / R ∧
      (∀ t ∈ closedBall (0 : ℂ) R, ‖φ t - φ 0‖ ≤ 2 * M * ‖t‖ / R) ∧
      ∀ t ∈ closedBall (0 : ℂ) R, ‖φ t - φ 0 - t • deriv φ 0‖ ≤ 4 * M * ‖t‖ ^ 2 / R ^ 2 := by
  have h0 : closedBall (0 : ℂ) R ∈ 𝓝 (0 : ℂ) := closedBall_mem_nhds _ hR
  have hg : DifferentiableOn ℂ (dslope φ 0) (closedBall 0 R) :=
    (Complex.differentiableOn_dslope h0).2 hd
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0 (mem_closedBall_self hR.le))
  have hsph : ∀ z ∈ sphere (0 : ℂ) R, ‖dslope φ 0 z‖ ≤ 2 * M / R := by
    intro z hz
    have hz' : ‖z‖ = R := by simpa using hz
    have hzne : z ≠ 0 := by
      intro h; rw [h] at hz'; simp at hz'; linarith
    have e := sub_smul_dslope φ 0 z
    have h1 : ‖z‖ * ‖dslope φ 0 z‖ ≤ 2 * M := by
      have : ‖φ z - φ 0‖ ≤ 2 * M :=
        (norm_sub_le _ _).trans (by linarith [hM z (sphere_subset_closedBall hz), hM 0 (mem_closedBall_self hR.le)])
      calc ‖z‖ * ‖dslope φ 0 z‖ = ‖(z - 0) • dslope φ 0 z‖ := by simp [norm_smul]
        _ = ‖φ z - φ 0‖ := by rw [e]
        _ ≤ 2 * M := this
    rw [hz'] at h1
    rw [le_div_iff₀ hR]
    linarith
  have hgb := qcv_maxmod_closedBall hR hg hsph
  have hderiv : deriv φ 0 = dslope φ 0 0 := by
    rw [dslope_same]
  refine ⟨by rw [hderiv]; exact hgb 0 (mem_closedBall_self hR.le), ?_, ?_⟩
  · intro t ht
    have e1 := sub_smul_dslope φ 0 t
    have : ‖φ t - φ 0‖ = ‖t‖ * ‖dslope φ 0 t‖ := by
      rw [← e1]; simp [norm_smul]
    rw [this]
    calc ‖t‖ * ‖dslope φ 0 t‖ ≤ ‖t‖ * (2 * M / R) := by gcongr; exact hgb t ht
      _ = 2 * M * ‖t‖ / R := by ring
  have hh : DifferentiableOn ℂ (dslope (dslope φ 0) 0) (closedBall 0 R) :=
    (Complex.differentiableOn_dslope h0).2 hg
  have hsph2 : ∀ z ∈ sphere (0 : ℂ) R, ‖dslope (dslope φ 0) 0 z‖ ≤ 4 * M / R ^ 2 := by
    intro z hz
    have hz' : ‖z‖ = R := by simpa using hz
    have e := sub_smul_dslope (dslope φ 0) 0 z
    have h1 : ‖z‖ * ‖dslope (dslope φ 0) 0 z‖ ≤ 4 * M / R := by
      have : ‖dslope φ 0 z - dslope φ 0 0‖ ≤ 4 * M / R := by
        refine (norm_sub_le _ _).trans ?_
        have a := hgb z (sphere_subset_closedBall hz)
        have b := hgb 0 (mem_closedBall_self hR.le)
        have : 2 * M / R + 2 * M / R = 4 * M / R := by ring
        linarith
      calc ‖z‖ * ‖dslope (dslope φ 0) 0 z‖ = ‖(z - 0) • dslope (dslope φ 0) 0 z‖ := by simp [norm_smul]
        _ = ‖dslope φ 0 z - dslope φ 0 0‖ := by rw [e]
        _ ≤ 4 * M / R := this
    rw [hz'] at h1
    rw [le_div_iff₀ (pow_pos hR 2)]
    have h2 : R * (R * ‖dslope (dslope φ 0) 0 z‖) ≤ 4 * M := by
      calc R * (R * ‖dslope (dslope φ 0) 0 z‖) ≤ R * (4 * M / R) := by gcongr
        _ = 4 * M := by field_simp
    nlinarith
  have hhb := qcv_maxmod_closedBall hR hh hsph2
  intro t ht
  have e1 := sub_smul_dslope φ 0 t
  have e2 := sub_smul_dslope (dslope φ 0) 0 t
  have e1' : t • dslope φ 0 t = φ t - φ 0 := by simpa using e1
  have e2' : t • dslope (dslope φ 0) 0 t = dslope φ 0 t - dslope φ 0 0 := by simpa using e2
  have key : φ t - φ 0 - t • deriv φ 0 = t • t • dslope (dslope φ 0) 0 t := by
    rw [hderiv, e2', smul_sub, e1']
  rw [key, norm_smul, norm_smul]
  have := hhb t ht
  calc ‖t‖ * (‖t‖ * ‖dslope (dslope φ 0) 0 t‖) ≤ ‖t‖ * (‖t‖ * (4 * M / R ^ 2)) := by gcongr
    _ = 4 * M * ‖t‖ ^ 2 / R ^ 2 := by ring


variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- A line-differentiability hypothesis at one base point transfers to every point of the line. -/
theorem qcv_line_diff {U : Set E} {f : E → F}
    (hg : ∀ x ∈ U, ∀ v : E, DifferentiableAt ℂ (fun t : ℂ => f (x + t • v)) 0)
    {a v : E} {t₀ : ℂ} (h : a + t₀ • v ∈ U) :
    DifferentiableAt ℂ (fun t : ℂ => f (a + t • v)) t₀ := by
  have h1 : DifferentiableAt ℂ (fun s : ℂ => f (a + t₀ • v + s • v)) ((fun t : ℂ => t - t₀) t₀) := by
    simp only [sub_self]; exact hg _ h v
  have h2 : DifferentiableAt ℂ (fun t : ℂ => t - t₀) t₀ := by fun_prop
  have h3 := DifferentiableAt.comp (f := fun t : ℂ => t - t₀) t₀ h1 h2
  have : (fun t : ℂ => f (a + t • v)) = (fun s : ℂ => f (a + t₀ • v + s • v)) ∘ (fun t : ℂ => t - t₀) := by
    funext t
    simp only [Function.comp]
    congr 1
    rw [sub_smul]; abel
  rw [this]; exact h3

/-- **Gateaux ⇒ Fréchet.** Locally bounded, Gateaux-holomorphic maps between complex Banach spaces are holomorphic. -/
theorem qcv_gateaux_to_frechet [CompleteSpace E] {U : Set E} (hU : IsOpen U) {f : E → F}
    (hloc : ∀ x ∈ U, ∃ r > 0, ∃ C : ℝ, ∀ y ∈ ball x r, ‖f y‖ ≤ C)
    (hg : ∀ x ∈ U, ∀ v : E, DifferentiableAt ℂ (fun t : ℂ => f (x + t • v)) 0) :
    DifferentiableOn ℂ f U := by
  intro x hx
  refine DifferentiableAt.differentiableWithinAt ?_
  obtain ⟨r₁, hr₁, hball⟩ := Metric.isOpen_iff.1 hU x hx
  obtain ⟨r₀, hr₀, C, hC⟩ := hloc x hx
  set ρ : ℝ := min r₀ r₁ / 2 with hρdef
  have hρ : 0 < ρ := by positivity
  have hρ0 : ρ < r₀ := by have := min_le_left r₀ r₁; linarith [lt_min hr₀ hr₁]
  have hρ1 : ρ < r₁ := by have := min_le_right r₀ r₁; linarith [lt_min hr₀ hr₁]
  have hcb : ∀ y ∈ closedBall x ρ, ‖f y‖ ≤ C := fun y hy =>
    hC y (closedBall_subset_ball hρ0 hy)
  have hsubU : closedBall x ρ ⊆ U := fun y hy => hball (closedBall_subset_ball hρ1 hy)
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hcb x (mem_closedBall_self hρ.le))
  -- the derivative along a direction
  let D : E → F := fun v => deriv (fun t : ℂ => f (x + t • v)) 0
  -- one-variable data for a nonzero direction
  have hline : ∀ v : E, v ≠ 0 → DifferentiableOn ℂ (fun t : ℂ => f (x + t • v)) (closedBall 0 (ρ / ‖v‖)) ∧
      ∀ t ∈ closedBall (0 : ℂ) (ρ / ‖v‖), ‖f (x + t • v)‖ ≤ C := by
    intro v hv
    have hvpos : 0 < ‖v‖ := norm_pos_iff.2 hv
    have hmem : ∀ t ∈ closedBall (0 : ℂ) (ρ / ‖v‖), x + t • v ∈ closedBall x ρ := by
      intro t ht
      rw [mem_closedBall, dist_eq_norm] at *
      simp only [add_sub_cancel_left, norm_smul]
      have : ‖t‖ ≤ ρ / ‖v‖ := by simpa using ht
      calc ‖t‖ * ‖v‖ ≤ ρ / ‖v‖ * ‖v‖ := by gcongr
        _ = ρ := by field_simp
    refine ⟨fun t ht => ?_, fun t ht => hcb _ (hmem t ht)⟩
    exact (qcv_line_diff hg (hsubU (hmem t ht))).differentiableWithinAt
  have hF1 : ∀ v : E, ‖D v‖ ≤ 2 * C * ‖v‖ / ρ := by
    intro v
    by_cases hv : v = 0
    · simp [hv, D]
    · have hvpos : 0 < ‖v‖ := norm_pos_iff.2 hv
      obtain ⟨hd, hb⟩ := hline v hv
      have := (qcv_taylor2 (div_pos hρ hvpos) hd hb).1
      calc ‖D v‖ ≤ 2 * C / (ρ / ‖v‖) := this
        _ = 2 * C * ‖v‖ / ρ := by field_simp
  have hF2 : ∀ z : E, ‖z‖ ≤ ρ → ‖f (x + z) - f x - D z‖ ≤ 4 * C * ‖z‖ ^ 2 / ρ ^ 2 := by
    intro z hz
    by_cases hv : z = 0
    · simp [hv, D]
    · have hvpos : 0 < ‖z‖ := norm_pos_iff.2 hv
      obtain ⟨hd, hb⟩ := hline z hv
      have h1 : (1 : ℂ) ∈ closedBall (0 : ℂ) (ρ / ‖z‖) := by
        rw [mem_closedBall_zero_iff, norm_one, le_div_iff₀ hvpos]; linarith
      have := (qcv_taylor2 (div_pos hρ hvpos) hd hb).2.2 1 h1
      simp only [one_smul, zero_smul, add_zero, norm_one, one_pow, mul_one] at this
      calc ‖f (x + z) - f x - D z‖ ≤ 4 * C / (ρ / ‖z‖) ^ 2 := this
        _ = 4 * C * ‖z‖ ^ 2 / ρ ^ 2 := by field_simp
  have hhom : ∀ (c : ℂ) (v : E), D (c • v) = c • D v := by
    intro c v
    have hd : HasDerivAt (fun t : ℂ => f (x + t • v)) (D v) ((fun t : ℂ => c * t) 0) := by
      have := (hg x hx v).hasDerivAt
      simpa [D] using this
    have hh : HasDerivAt (fun t : ℂ => c * t) c 0 := by
      simpa using (hasDerivAt_id (0 : ℂ)).const_mul c
    have := (hd.scomp 0 hh).deriv
    have e : (fun t : ℂ => f (x + t • (c • v))) = (fun t : ℂ => f (x + t • v)) ∘ (fun t : ℂ => c * t) := by
      funext t; simp only [Function.comp, smul_smul]; rw [mul_comm]
    simp only [D, e]
    rw [this]
  have hadd : ∀ v w : E, D (v + w) = D v + D w := by
    intro v w
    set N : ℝ := ‖v‖ + ‖w‖ + 1 with hN
    have hNpos : 0 < N := by positivity
    set R : ℝ := ρ / N with hR
    have hRpos : 0 < R := div_pos hρ hNpos
    have hRN : R * N = ρ := by rw [hR]; field_simp
    have hmem : ∀ s u : ℂ, ‖s‖ ≤ R → ‖u‖ ≤ R → (x + u • w) + s • v ∈ closedBall x ρ := by
      intro s u hs hu
      rw [mem_closedBall, dist_eq_norm]
      have : x + u • w + s • v - x = s • v + u • w := by abel
      rw [this]
      calc ‖s • v + u • w‖ ≤ ‖s • v‖ + ‖u • w‖ := norm_add_le _ _
        _ = ‖s‖ * ‖v‖ + ‖u‖ * ‖w‖ := by simp [norm_smul]
        _ ≤ R * ‖v‖ + R * ‖w‖ := by gcongr
        _ ≤ R * N := by rw [hN]; nlinarith
        _ = ρ := hRN
    have hmem0 : ∀ u : ℂ, ‖u‖ ≤ R → x + u • w ∈ closedBall x ρ := by
      intro u hu
      have := hmem 0 u (by simpa using hRpos.le) hu
      simpa using this
    let H : ℂ → ℂ → F := fun s u => f ((x + u • w) + s • v) - f (x + u • w)
    have hHs : ∀ u : ℂ, ‖u‖ ≤ R → DifferentiableOn ℂ (fun s => H s u) (closedBall 0 R) := by
      intro u hu s hs
      have hs' : ‖s‖ ≤ R := by simpa using hs
      refine DifferentiableAt.differentiableWithinAt (DifferentiableAt.sub ?_ (differentiableAt_const _))
      exact qcv_line_diff hg (a := x + u • w) (v := v) (t₀ := s) (hsubU (hmem s u hs' hu))
    have hHu : ∀ s : ℂ, ‖s‖ ≤ R → DifferentiableOn ℂ (fun u => H s u) (closedBall 0 R) := by
      intro s hs u hu
      have hu' : ‖u‖ ≤ R := by simpa using hu
      refine DifferentiableAt.differentiableWithinAt (DifferentiableAt.sub ?_ ?_)
      · have e : (fun u : ℂ => f ((x + u • w) + s • v)) = fun u : ℂ => f ((x + s • v) + u • w) := by
          funext u; congr 1; abel
        rw [e]
        refine qcv_line_diff hg (a := x + s • v) (v := w) (t₀ := u) (hsubU ?_)
        have := hmem s u hs hu'
        rwa [show x + s • v + u • w = x + u • w + s • v by abel]
      · exact qcv_line_diff hg (a := x) (v := w) (t₀ := u) (hsubU (hmem0 u hu'))
    have hHb : ∀ s u : ℂ, ‖s‖ ≤ R → ‖u‖ ≤ R → ‖H s u‖ ≤ 2 * C := by
      intro s u hs hu
      exact (norm_sub_le _ _).trans (by linarith [hcb _ (hmem s u hs hu), hcb _ (hmem0 u hu)])
    have hH0 : ∀ u : ℂ, H 0 u = 0 := by intro u; simp [H]
    have hS : ∀ s u : ℂ, ‖s‖ ≤ R → ‖u‖ ≤ R → ‖H s u‖ ≤ 4 * C * ‖s‖ / R := by
      intro s u hs hu
      have := (qcv_taylor2 hRpos (hHs u hu) (fun s' hs' => hHb s' u (by simpa using hs') hu)).2.1 s
        (mem_closedBall_zero_iff.2 hs)
      rw [hH0, sub_zero] at this
      calc ‖H s u‖ ≤ 2 * (2 * C) * ‖s‖ / R := this
        _ = 4 * C * ‖s‖ / R := by ring
    have hΔ : ∀ t : ℂ, ‖t‖ ≤ R → ‖H t t - H t 0‖ ≤ 24 * C * ‖t‖ ^ 2 / R ^ 2 := by
      intro t ht
      have hb : ∀ u ∈ closedBall (0 : ℂ) R, ‖H t u‖ ≤ 4 * C * ‖t‖ / R :=
        fun u hu => hS t u ht (by simpa using hu)
      have tay := qcv_taylor2 hRpos (hHu t ht) hb
      have h1 := tay.2.2 t (mem_closedBall_zero_iff.2 ht)
      have h2 := tay.1
      have hq : ‖t‖ / R ≤ 1 := (div_le_one hRpos).2 ht
      have hC' : 0 ≤ 16 * C * ‖t‖ ^ 2 / R ^ 2 := by positivity
      have h3 : 4 * (4 * C * ‖t‖ / R) * ‖t‖ ^ 2 / R ^ 2 ≤ 16 * C * ‖t‖ ^ 2 / R ^ 2 := by
        have e : 4 * (4 * C * ‖t‖ / R) * ‖t‖ ^ 2 / R ^ 2 = (16 * C * ‖t‖ ^ 2 / R ^ 2) * (‖t‖ / R) := by ring
        rw [e]
        calc (16 * C * ‖t‖ ^ 2 / R ^ 2) * (‖t‖ / R) ≤ (16 * C * ‖t‖ ^ 2 / R ^ 2) * 1 := by gcongr
          _ = _ := mul_one _
      have h4 : ‖t • deriv (fun u => H t u) 0‖ ≤ 8 * C * ‖t‖ ^ 2 / R ^ 2 := by
        rw [norm_smul]
        calc ‖t‖ * ‖deriv (fun u => H t u) 0‖ ≤ ‖t‖ * (2 * (4 * C * ‖t‖ / R) / R) := by gcongr
          _ = 8 * C * ‖t‖ ^ 2 / R ^ 2 := by ring
      calc ‖H t t - H t 0‖ ≤ ‖H t t - H t 0 - t • deriv (fun u => H t u) 0‖ + ‖t • deriv (fun u => H t u) 0‖ := by
            have := norm_add_le (H t t - H t 0 - t • deriv (fun u => H t u) 0) (t • deriv (fun u => H t u) 0)
            simpa using this
        _ ≤ 16 * C * ‖t‖ ^ 2 / R ^ 2 + 8 * C * ‖t‖ ^ 2 / R ^ 2 := add_le_add (h1.trans h3) h4
        _ = 24 * C * ‖t‖ ^ 2 / R ^ 2 := by ring
    have hkey : ∀ t : ℂ, ‖t‖ ≤ R → ‖t‖ * ‖D (v + w) - D v - D w‖ ≤ 36 * C * ‖t‖ ^ 2 / R ^ 2 := by
      intro t ht
      have hz : ∀ z : E, ‖z‖ ≤ ‖t‖ * N → ‖z‖ ≤ ρ → ‖f (x + z) - f x - D z‖ ≤ 4 * C * ‖t‖ ^ 2 / R ^ 2 := by
        intro z hz1 hz2
        refine (hF2 z hz2).trans ?_
        have : 4 * C * ‖z‖ ^ 2 / ρ ^ 2 ≤ 4 * C * (‖t‖ * N) ^ 2 / ρ ^ 2 := by gcongr
        refine this.trans (le_of_eq ?_)
        rw [← hRN]; field_simp
      have hnv : ‖t • v‖ ≤ ‖t‖ * N := by
        rw [norm_smul, hN]; gcongr; linarith [norm_nonneg w]
      have hnw : ‖t • w‖ ≤ ‖t‖ * N := by
        rw [norm_smul, hN]; gcongr; linarith [norm_nonneg v]
      have hnvw : ‖t • (v + w)‖ ≤ ‖t‖ * N := by
        rw [norm_smul, hN]; gcongr; linarith [norm_add_le v w]
      have hρle : ∀ z : E, ‖z‖ ≤ ‖t‖ * N → ‖z‖ ≤ ρ := fun z hz =>
        hz.trans (by rw [← hRN]; gcongr)
      have r1 := hz _ hnv (hρle _ hnv)
      have r2 := hz _ hnw (hρle _ hnw)
      have r3 := hz _ hnvw (hρle _ hnvw)
      have e3 : x + t • (v + w) = (x + t • w) + t • v := by rw [smul_add]; abel
      have hid : D (t • (v + w)) - D (t • v) - D (t • w) =
          (H t t - H t 0) + (f (x + t • v) - f x - D (t • v)) + (f (x + t • w) - f x - D (t • w)) -
            (f (x + t • (v + w)) - f x - D (t • (v + w))) := by
        simp only [H, e3, zero_smul, add_zero]; abel
      have hlhs : D (t • (v + w)) - D (t • v) - D (t • w) = t • (D (v + w) - D v - D w) := by
        rw [hhom, hhom, hhom, smul_sub, smul_sub]
      have hΔt := hΔ t ht
      calc ‖t‖ * ‖D (v + w) - D v - D w‖ = ‖D (t • (v + w)) - D (t • v) - D (t • w)‖ := by
            rw [hlhs, norm_smul]
        _ ≤ ‖H t t - H t 0‖ + ‖f (x + t • v) - f x - D (t • v)‖ + ‖f (x + t • w) - f x - D (t • w)‖ +
              ‖f (x + t • (v + w)) - f x - D (t • (v + w))‖ := by
            rw [hid]
            refine (norm_sub_le _ _).trans ?_
            gcongr
            exact (norm_add_le _ _).trans (by gcongr; exact norm_add_le _ _)
        _ ≤ 36 * C * ‖t‖ ^ 2 / R ^ 2 := by
            have : 24 * C * ‖t‖ ^ 2 / R ^ 2 + 4 * C * ‖t‖ ^ 2 / R ^ 2 + 4 * C * ‖t‖ ^ 2 / R ^ 2 +
                4 * C * ‖t‖ ^ 2 / R ^ 2 = 36 * C * ‖t‖ ^ 2 / R ^ 2 := by ring
            linarith
    by_contra hne
    have hq : 0 < ‖D (v + w) - D v - D w‖ := norm_pos_iff.2 (by
      intro h; apply hne; rw [sub_sub, sub_eq_zero] at h; exact h)
    set q : ℝ := ‖D (v + w) - D v - D w‖ with hqdef
    have hC1 : 0 < 72 * C + 1 := by linarith
    set τ : ℝ := min R (q * R ^ 2 / (72 * C + 1)) with hτdef
    have hτ : 0 < τ := lt_min hRpos (by positivity)
    have hτR : τ ≤ R := min_le_left _ _
    have hτq : τ ≤ q * R ^ 2 / (72 * C + 1) := min_le_right _ _
    have hk := hkey (τ : ℂ) (by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hτ]; exact hτR)
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hτ] at hk
    have h0 : τ * q * R ^ 2 ≤ 36 * C * τ ^ 2 := (le_div_iff₀ (pow_pos hRpos 2)).1 hk
    have h1 : q * R ^ 2 ≤ 36 * C * τ := by
      refine le_of_mul_le_mul_left ?_ hτ
      nlinarith
    have h2 : τ * (72 * C + 1) ≤ q * R ^ 2 := (le_div_iff₀ hC1).1 hτq
    nlinarith [mul_nonneg hτ.le hC0]
  let Lm : E →ₗ[ℂ] F := { toFun := D, map_add' := hadd, map_smul' := hhom }
  let L : E →L[ℂ] F := LinearMap.mkContinuous Lm (2 * C / ρ) (fun v => by
    show ‖D v‖ ≤ 2 * C / ρ * ‖v‖
    calc ‖D v‖ ≤ 2 * C * ‖v‖ / ρ := hF1 v
      _ = 2 * C / ρ * ‖v‖ := by ring)
  have hL : ∀ h, L h = D h := fun h => rfl
  refine ((hasFDerivAt_iff_isLittleO_nhds_zero (f' := L)).2 ?_).differentiableAt
  rw [Asymptotics.isLittleO_iff]
  intro c hc
  have hδ : 0 < min ρ (c * ρ ^ 2 / (4 * C + 1)) := lt_min hρ (by positivity)
  filter_upwards [Metric.ball_mem_nhds (0 : E) hδ] with h hh
  rw [mem_ball_zero_iff] at hh
  have hh1 : ‖h‖ ≤ ρ := (hh.trans_le (min_le_left _ _)).le
  have hh2 : ‖h‖ < c * ρ ^ 2 / (4 * C + 1) := hh.trans_le (min_le_right _ _)
  have := hF2 h hh1
  rw [hL]
  refine this.trans ?_
  have hpos : 0 < 4 * C + 1 := by linarith
  have h3 : 4 * C * ‖h‖ ≤ c * ρ ^ 2 := by
    have := (lt_div_iff₀ hpos).1 hh2
    nlinarith [norm_nonneg h]
  calc 4 * C * ‖h‖ ^ 2 / ρ ^ 2 = ‖h‖ * (4 * C * ‖h‖ / ρ ^ 2) := by ring
    _ ≤ ‖h‖ * c := by
      gcongr
      rw [div_le_iff₀ (pow_pos hρ 2)]
      exact h3
    _ = c * ‖h‖ := mul_comm _ _


/-- **Partial derivatives (Ahlfors–Bers).** At `(e₁, e₂)` with `w = normalizedSolution (e₁ a + e₂ b)`:
`∂_{e₁} w(z) = -(1/π) ∬ R(w z, w u) a(u) (w_u u)² d²u`, and likewise for `b`,
`R(z,u) = z(z-1)/((u-z)u(u-1))`. -/
theorem qcv_plane_partials {a b : ℂ → ℂ} {ka kb : ℝ} (hka : 0 ≤ ka) (hkb : 0 ≤ kb)
    (ha : IsBeltramiCoeff a univ ka) (hb : IsBeltramiCoeff b univ kb) {e₁ e₂ : ℂ}
    (he : ‖e₁‖ * ka + ‖e₂‖ * kb < 1) (z : ℂ) :
    let w := normalizedSolution (fun u => e₁ * a u + e₂ * b u)
    HasDerivAt (fun t : ℂ => normalizedSolution (fun u => t * a u + e₂ * b u) z)
        (-(1 / π : ℂ) * ∫ u, (w z * (w z - 1) / ((w u - w z) * w u * (w u - 1))) * a u * dz w u ^ 2) e₁ ∧
      HasDerivAt (fun t : ℂ => normalizedSolution (fun u => e₁ * a u + t * b u) z)
        (-(1 / π : ℂ) * ∫ u, (w z * (w z - 1) / ((w u - w z) * w u * (w u - 1))) * b u * dz w u ^ 2) e₂ := by
  obtain ⟨L, hL, hLv⟩ := qcv_plane_two_param_hasFDerivAt hka hkb ha hb (p₀ := (e₁, e₂)) he z
  intro w
  have hι1 : HasDerivAt (fun t : ℂ => ((t, e₂) : ℂ × ℂ)) ((1 : ℂ), (0 : ℂ)) e₁ :=
    (hasDerivAt_id e₁).prodMk (hasDerivAt_const e₁ e₂)
  have hι2 : HasDerivAt (fun t : ℂ => ((e₁, t) : ℂ × ℂ)) ((0 : ℂ), (1 : ℂ)) e₂ :=
    (hasDerivAt_const e₂ e₁).prodMk (hasDerivAt_id e₂)
  refine ⟨?_, ?_⟩
  · have h := hL.comp_hasDerivAt e₁ hι1
    refine HasDerivAt.congr_deriv h ?_
    rw [hLv]
    congr 1
    refine integral_congr_ae (Eventually.of_forall fun u => ?_)
    simp only [ahKer, w]
    ring
  · have h := hL.comp_hasDerivAt e₂ hι2
    refine HasDerivAt.congr_deriv h ?_
    rw [hLv]
    congr 1
    refine integral_congr_ae (Eventually.of_forall fun u => ?_)
    simp only [ahKer, w]
    ring


/-! ### Reflection symmetry and the real-analytic reflection family -/

/-- Wirtinger dilatation of the reflected map (copy of LiZhongQC S27 `s27u_b_dilatation_conj`). -/
theorem qcv_dilatation_conj (f : ℂ → ℂ) (z : ℂ) :
    complexDilatation (fun w => conj (f (conj w))) z = conj (complexDilatation f (conj z)) := by
  by_cases hd : DifferentiableAt ℝ f (conj z)
  · obtain ⟨-, h1, h2⟩ := abR_x_dz_dzbar_conj hd
    rw [complexDilatation, complexDilatation, h1, h2, map_div₀]
  · have hd' : ¬ DifferentiableAt ℝ (fun w => conj (f (conj w))) z := by
      intro h
      apply hd
      have h' : DifferentiableAt ℝ (fun w => conj (f (conj w))) (conj (conj z)) := by
        rwa [Complex.conj_conj]
      simpa only [Complex.conj_conj] using (abR_x_dz_dzbar_conj h').1
    simp [complexDilatation, dz, dzbar, fderiv_zero_of_not_differentiableAt hd,
      fderiv_zero_of_not_differentiableAt hd']

/-- The unique normalized solution of a coefficient symmetric under `z ↦ z̄` commutes with the reflection
(copy of LiZhongQC S27 `s27u_b_s_conj_comm`, for an arbitrary symmetric coefficient). -/
theorem qcv_ns_conj_comm {σ f : ℂ → ℂ} (hsym : ∀ z : ℂ, z.im ≠ 0 → conj (σ (conj z)) = σ z)
    (hN : IsNormalizedSolution f σ) (huniq : ∀ g : ℂ → ℂ, IsNormalizedSolution g σ → g = f) (z : ℂ) :
    f (conj z) = conj (f z) := by
  obtain ⟨⟨K, hK⟩, hs, h0, h1, hd⟩ := hN
  have hgK : IsKQC (fun w => conj (f (conj w))) univ K := by
    have h := abR_x_isKQC_conj hK
    rwa [preimage_univ] at h
  have hgs : (fun w => conj (f (conj w))) '' univ = univ := by
    refine eq_univ_of_forall fun w => ?_
    have hw : conj w ∈ f '' univ := by
      rw [hs]
      exact mem_univ _
    obtain ⟨v, -, hv⟩ := hw
    exact ⟨conj v, mem_univ _, by simp only [Complex.conj_conj, hv]⟩
  have hnull : ∀ᵐ w : ℂ, w ∉ {v : ℂ | v.im = 0} :=
    measure_eq_zero_iff_ae_notMem.1 gzE_volume_im_eq_zero
  have hgd : ∀ᵐ w, complexDilatation (fun w => conj (f (conj w))) w = σ w := by
    filter_upwards [gzE_conj_measurePreserving.quasiMeasurePreserving.ae hd, hnull] with w hw1 hw2
    rw [qcv_dilatation_conj, hw1]
    exact hsym w hw2
  have hg : IsNormalizedSolution (fun w => conj (f (conj w))) σ :=
    ⟨⟨_, hgK⟩, hgs, by simp [h0], by simp [h1], hgd⟩
  have h := congrFun (huniq _ hg) z
  rw [← h, Complex.conj_conj]

/-- Wirtinger derivative of a reflection-symmetric map. -/
theorem qcv_dz_conj_sym {w : ℂ → ℂ} (hsym : ∀ x, w (conj x) = conj (w x)) (u : ℂ) :
    dz w (conj u) = conj (dz w u) := by
  have hfun : (fun x => conj (w (conj x))) = w := by
    funext x; rw [hsym x, Complex.conj_conj]
  by_cases hd : DifferentiableAt ℝ w u
  · have hd' : DifferentiableAt ℝ w (conj (conj u)) := by rwa [Complex.conj_conj]
    obtain ⟨-, h1, -⟩ := abR_x_dz_dzbar_conj hd'
    rw [hfun, Complex.conj_conj] at h1
    exact h1
  · have hd2 : ¬ DifferentiableAt ℝ w (conj u) := by
      intro h
      apply hd
      have := (abR_x_dz_dzbar_conj (h := w) (z := u) (by simpa using h)).1
      rwa [hfun] at this
    simp [dz, fderiv_zero_of_not_differentiableAt hd, fderiv_zero_of_not_differentiableAt hd2]


/-- **Reflection form of the Ahlfors–Bers variation** (the upper-half-plane model of §1.5): with
`ext e = e μ` on `𝕌`, `conj (e μ(z̄))` on the lower half-plane, `0` on `ℝ`, and `w = normalizedSolution (ext ε)`,
`∂_ε` and `∂_ε̄` of `e ↦ normalizedSolution (ext e) z` at `ε` (`|ε| k < 1`). -/
theorem qcv_plane_reflection_dz {μ : ℂ → ℂ} {k : ℝ} (hk0 : 0 ≤ k)
    (hμ : IsBeltramiCoeff μ {z : ℂ | 0 < z.im} k) {ε : ℂ} (hε : ‖ε‖ * k < 1) (z : ℂ) :
    let ext : ℂ → ℂ → ℂ := fun e u => if 0 < u.im then e * μ u else if u.im < 0 then conj (e * μ (conj u)) else 0
    let w := normalizedSolution (ext ε)
    dz (fun e => normalizedSolution (ext e) z) ε =
        -(1 / π : ℂ) * ∫ u in {u : ℂ | 0 < u.im}, (w z * (w z - 1) / ((w u - w z) * w u * (w u - 1))) * μ u *
          dz w u ^ 2 ∧
      dzbar (fun e => normalizedSolution (ext e) z) ε =
        -(1 / π : ℂ) * ∫ u in {u : ℂ | 0 < u.im},
          (w z * (w z - 1) / ((conj (w u) - w z) * conj (w u) * (conj (w u) - 1))) *
            conj (μ u * dz w u ^ 2) := by
  intro ext w
  have hmU : MeasurableSet {z : ℂ | 0 < z.im} := measurableSet_lt measurable_const Complex.measurable_im
  have hmL : MeasurableSet {z : ℂ | z.im < 0} := measurableSet_lt Complex.measurable_im measurable_const
  have hpre : conj ⁻¹' {z : ℂ | 0 < z.im} = {z : ℂ | z.im < 0} := by
    ext z; simp [Complex.conj_im]
  have hmp : MeasurePreserving conj (volume.restrict {z : ℂ | z.im < 0}) (volume.restrict {z : ℂ | 0 < z.im}) := by
    have := gzE_conj_measurePreserving.restrict_preimage hmU
    rwa [hpre] at this
  -- the two disjointly supported coefficients
  let a' : ℂ → ℂ := fun u => if 0 < u.im then μ u else 0
  let b' : ℂ → ℂ := fun u => if u.im < 0 then conj (μ (conj u)) else 0
  have hext : ∀ e u, ext e u = e * a' u + conj e * b' u := by
    intro e u
    by_cases h1 : 0 < u.im
    · have h2 : ¬ u.im < 0 := not_lt.2 h1.le
      simp [ext, a', b', h1, h2]
    · by_cases h2 : u.im < 0
      · simp [ext, a', b', h1, h2, map_mul]
      · simp [ext, a', b', h1, h2]
  have hz : ∀ u, a' u = 0 ∨ b' u = 0 := by
    intro u
    by_cases h1 : 0 < u.im
    · right; have h2 : ¬ u.im < 0 := not_lt.2 h1.le
      simp [b', h2]
    · left; simp [a', h1]
  have ha_meas : AEStronglyMeasurable a' volume := by
    have : a' = {z : ℂ | 0 < z.im}.indicator μ := by funext u; simp [a', Set.indicator]
    rw [this]; exact (aestronglyMeasurable_indicator_iff hmU).2 hμ.1
  have hb_meas : AEStronglyMeasurable b' volume := by
    have h1 : AEStronglyMeasurable (fun u => conj (μ (conj u))) (volume.restrict {z : ℂ | z.im < 0}) :=
      Complex.continuous_conj.comp_aestronglyMeasurable
        (hμ.1.comp_quasiMeasurePreserving hmp.quasiMeasurePreserving)
    have : b' = {z : ℂ | z.im < 0}.indicator (fun u => conj (μ (conj u))) := by
      funext u; simp [b', Set.indicator]
    rw [this]; exact (aestronglyMeasurable_indicator_iff hmL).2 h1
  have ha_bd : ∀ᵐ u, ‖a' u‖ ≤ k := by
    have h := (ae_restrict_iff' hmU).1 hμ.2
    filter_upwards [h] with u hu
    by_cases hp : 0 < u.im
    · have : a' u = μ u := if_pos hp
      rw [this]; exact hu hp
    · have : a' u = 0 := if_neg hp
      rw [this, norm_zero]; exact hk0
  have hb_bd : ∀ᵐ u, ‖b' u‖ ≤ k := by
    have h' : ∀ᵐ u ∂(volume.restrict {z : ℂ | 0 < z.im}), ‖μ u‖ ≤ k := hμ.2
    have h2 := (ae_restrict_iff' hmL).1 (hmp.quasiMeasurePreserving.ae h')
    filter_upwards [h2] with u hu
    by_cases hp : u.im < 0
    · have : b' u = conj (μ (conj u)) := if_pos hp
      rw [this, Complex.norm_conj]; exact hu hp
    · have : b' u = 0 := if_neg hp
      rw [this, norm_zero]; exact hk0
  have hT : ∀ v : ℂ × ℂ, IsBeltramiCoeff (fun u => v.1 * a' u + v.2 * b' u) univ (k * ‖v‖) := by
    intro v
    refine ⟨?_, ?_⟩
    · rw [Measure.restrict_univ]
      exact (ha_meas.const_mul v.1).add (hb_meas.const_mul v.2)
    · rw [Measure.restrict_univ]
      filter_upwards [ha_bd, hb_bd] with u h1 h2
      rcases hz u with h | h
      · rw [h, mul_zero, zero_add, norm_mul]
        calc ‖v.2‖ * ‖b' u‖ ≤ ‖v‖ * k := by
              exact mul_le_mul (norm_snd_le v) h2 (norm_nonneg _) (norm_nonneg _)
          _ = k * ‖v‖ := mul_comm _ _
      · rw [h, mul_zero, add_zero, norm_mul]
        calc ‖v.1‖ * ‖a' u‖ ≤ ‖v‖ * k := by
              exact mul_le_mul (norm_fst_le v) h1 (norm_nonneg _) (norm_nonneg _)
          _ = k * ‖v‖ := mul_comm _ _
  have hnv : ‖((ε, conj ε) : ℂ × ℂ)‖ = ‖ε‖ := by
    rw [Prod.norm_def, Complex.norm_conj, max_self]
  have hg₀ : IsBeltramiCoeff (fun u => ε * a' u + conj ε * b' u) univ (k * ‖ε‖) := by
    have := hT (ε, conj ε)
    rwa [hnv] at this
  have hkε : k * ‖ε‖ < 1 := by rw [mul_comm]; exact hε
  have hk₀ : 0 ≤ k * ‖ε‖ := by positivity
  obtain ⟨L, hL, hLv⟩ := qcv_plane_two_param_general (a := a') (b := b') (M := k) hk0 hk₀ hkε
    (p₀ := (ε, conj ε)) hg₀ hT z
  -- identification of `w` and symmetry
  have hextf : ∀ e, ext e = fun u => e * a' u + conj e * b' u := fun e => funext (hext e)
  have hwdef : w = normalizedSolution (fun u => ε * a' u + conj ε * b' u) := by
    simp only [w, hextf]
  obtain ⟨F0, hF0, -, huniq0⟩ := thm13_7_normalized_existence hk₀ hkε hg₀
  have hsymσ : ∀ x : ℂ, x.im ≠ 0 → conj (ext ε (conj x)) = ext ε x := by
    intro x hx
    rcases lt_or_gt_of_ne hx with h | h
    · have hc : 0 < (conj x).im := by rw [Complex.conj_im]; linarith
      have h2 : ¬ x.im > 0 := not_lt.2 h.le
      simp only [ext, hc, if_true, if_neg (not_lt.2 h.le), h, Complex.conj_conj, map_mul, if_true]
    · have hc : (conj x).im < 0 := by rw [Complex.conj_im]; linarith
      have h1 : 0 < x.im := h
      have h2 : ¬ (conj x).im > 0 := by rw [Complex.conj_im]; linarith
      simp only [ext, h1, if_true, if_neg h2, hc, Complex.conj_conj, map_mul]
  have hbext : IsBeltramiCoeff (ext ε) univ (k * ‖ε‖) := by
    rw [hextf]; exact hg₀
  have hNw : IsNormalizedSolution w (ext ε) := by
    simp only [w]; exact qcv_ns_spec hk₀ hkε hbext
  have hconj : ∀ x, w (conj x) = conj (w x) := fun x =>
    qcv_ns_conj_comm hsymσ hNw (fun g hg => by
      have hg' : IsNormalizedSolution g (fun u => ε * a' u + conj ε * b' u) := by rwa [hextf] at hg
      have hw' : IsNormalizedSolution w (fun u => ε * a' u + conj ε * b' u) := by rwa [hextf] at hNw
      exact (huniq0 g hg').trans (huniq0 w hw').symm) x
  have hdzc : ∀ x, dz w (conj x) = conj (dz w x) := qcv_dz_conj_sym hconj
  -- real derivative of `e ↦ normalizedSolution (ext e) z`
  let ι : ℂ →L[ℝ] ℂ × ℂ := (ContinuousLinearMap.id ℝ ℂ).prod (Complex.conjCLE : ℂ →L[ℝ] ℂ)
  have hιfun : (⇑ι) = fun e : ℂ => (e, conj e) := by funext e; simp [ι]
  have hι : HasFDerivAt (fun e : ℂ => (e, conj e)) ι ε := by
    rw [← hιfun]; exact ι.hasFDerivAt
  have hF : (fun e => normalizedSolution (ext e) z) =
      (fun p : ℂ × ℂ => normalizedSolution (fun u => p.1 * a' u + p.2 * b' u) z) ∘ (fun e : ℂ => (e, conj e)) := by
    funext e; simp only [Function.comp, hextf]
  have hcomp : HasFDerivAt (fun e => normalizedSolution (ext e) z) ((L.restrictScalars ℝ).comp ι) ε := by
    rw [hF]; exact (hL.restrictScalars ℝ).comp ε hι
  have hLx : ∀ x y : ℂ, L (x, y) = x * L (1, 0) + y * L (0, 1) := by
    intro x y
    have : ((x, y) : ℂ × ℂ) = x • ((1 : ℂ), (0 : ℂ)) + y • ((0 : ℂ), (1 : ℂ)) := by ext <;> simp
    rw [this, map_add, map_smul, map_smul]; simp [smul_eq_mul]
  have hfd : ∀ h : ℂ, fderiv ℝ (fun e => normalizedSolution (ext e) z) ε h =
      h * L (1, 0) + conj h * L (0, 1) := by
    intro h
    rw [hcomp.fderiv]
    show L (ι h) = _
    rw [congrFun hιfun h, hLx]
  have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
  have hdzF : dz (fun e => normalizedSolution (ext e) z) ε = L (1, 0) := by
    unfold dz
    rw [hfd, hfd]
    simp only [one_mul, map_one, Complex.conj_I]
    linear_combination ((L (0, 1) - L (1, 0)) / 2) * hI
  have hdzbarF : dzbar (fun e => normalizedSolution (ext e) z) ε = L (0, 1) := by
    unfold dzbar
    rw [hfd, hfd]
    simp only [one_mul, map_one, Complex.conj_I]
    linear_combination ((L (1, 0) - L (0, 1)) / 2) * hI
  rw [hdzF, hdzbarF]
  have key : ∀ v : ℂ × ℂ, L v = -(1 / π : ℂ) * ∫ u, (v.1 * a' u + v.2 * b' u) * ahKer (w z) (w u) * dz w u ^ 2 := by
    intro v
    rw [hLv v, hwdef]
  have hmeasEmb : MeasurableEmbedding (conj : ℂ → ℂ) := Complex.conjLIE.toHomeomorph.measurableEmbedding
  refine ⟨?_, ?_⟩
  · rw [key]
    congr 1
    have e1 : (fun u => ((1, 0) : ℂ × ℂ).1 * a' u + ((1, 0) : ℂ × ℂ).2 * b' u) = a' := by
      funext u; simp
    have e2 : (fun u => (((1 : ℂ), (0 : ℂ)).1 * a' u + ((1 : ℂ), (0 : ℂ)).2 * b' u) * ahKer (w z) (w u) * dz w u ^ 2) =
        {z : ℂ | 0 < z.im}.indicator (fun u => (w z * (w z - 1) / ((w u - w z) * w u * (w u - 1))) * μ u *
          dz w u ^ 2) := by
      funext u
      by_cases hp : 0 < u.im
      · have ha : a' u = μ u := if_pos hp
        rw [Set.indicator_of_mem (show u ∈ {z : ℂ | 0 < z.im} from hp), ha]
        dsimp only
        simp only [ahKer]
        ring
      · have ha : a' u = 0 := if_neg hp
        rw [Set.indicator_of_notMem (show u ∉ {z : ℂ | 0 < z.im} from hp), ha]
        dsimp only
        ring
    rw [e2, integral_indicator hmU]
  · rw [key]
    congr 1
    let G : ℂ → ℂ := {z : ℂ | 0 < z.im}.indicator
      (fun x => conj (μ x) * ahKer (w z) (w (conj x)) * dz w (conj x) ^ 2)
    have hpt : ∀ u, (((0 : ℂ), (1 : ℂ)).1 * a' u + ((0 : ℂ), (1 : ℂ)).2 * b' u) * ahKer (w z) (w u) * dz w u ^ 2 =
        G (conj u) := by
      intro u
      by_cases hl : u.im < 0
      · have hc : 0 < (conj u).im := by rw [Complex.conj_im]; linarith
        simp [G, b', hl, hc, Set.indicator, Complex.conj_conj]
      · have hc : ¬ 0 < (conj u).im := by rw [Complex.conj_im]; linarith [not_lt.1 hl]
        simp [G, b', hl, hc, Set.indicator]
    have h1 : ∫ u, (((0 : ℂ), (1 : ℂ)).1 * a' u + ((0 : ℂ), (1 : ℂ)).2 * b' u) * ahKer (w z) (w u) * dz w u ^ 2 =
        ∫ u, G (conj u) := integral_congr_ae (Eventually.of_forall hpt)
    rw [h1, gzE_conj_measurePreserving.integral_comp hmeasEmb G, integral_indicator hmU]
    refine setIntegral_congr_fun hmU (fun x _ => ?_)
    simp only [hconj x, hdzc x, ahKer, map_mul, map_pow]
    ring

/-- `normalizedSolution` only depends on the a.e.-class of a coefficient bounded by `k < 1`. -/
theorem qcv_ns_congr_ae {m₁ m₂ : ℂ → ℂ} {k : ℝ} (hk₀ : 0 ≤ k) (hk : k < 1)
    (h₁ : IsBeltramiCoeff m₁ univ k) (h : m₁ =ᵐ[volume] m₂) :
    normalizedSolution m₁ = normalizedSolution m₂ := by
  have hs := qcv_ns_spec hk₀ hk h₁
  have h₂ : IsBeltramiCoeff m₂ univ k := by
    have hm1 := h₁.1
    have hb1 := h₁.2
    refine ⟨?_, ?_⟩
    · rw [Measure.restrict_univ] at hm1 ⊢
      exact hm1.congr h
    · rw [Measure.restrict_univ] at hb1 ⊢
      filter_upwards [hb1, h] with u hu he
      rw [← he]; exact hu
  exact (qcv_ns_eq hk₀ hk h₂ (qcv_isNS_congr h hs)).symm

/-- **Parameter-holomorphy of the `ζ`-derivative.** If `F t` is holomorphic and bounded by `M` on `ball c R`
and `t ↦ F t ζ` is holomorphic on `ball 0 r` for each `ζ`, then `t ↦ deriv (F t) c` is holomorphic on `ball 0 r`
(uniform limit of holomorphic difference quotients, with the Cauchy estimate `qcv_taylor2`). -/
theorem qcv_param_deriv {F : ℂ → ℂ → ℂ} {c : ℂ} {r R M : ℝ} (hR : 0 < R) (hM0 : 0 ≤ M)
    (hζ : ∀ t ∈ ball (0 : ℂ) r, DifferentiableOn ℂ (F t) (ball c R))
    (ht : ∀ ζ ∈ ball c R, DifferentiableOn ℂ (fun t => F t ζ) (ball (0 : ℂ) r))
    (hM : ∀ t ∈ ball (0 : ℂ) r, ∀ ζ ∈ ball c R, ‖F t ζ‖ ≤ M) :
    DifferentiableOn ℂ (fun t => deriv (F t) c) (ball (0 : ℂ) r) := by
  have hcR : c ∈ ball c R := mem_ball_self hR
  -- difference quotients
  let Q : ℂ → ℂ → ℂ := fun h t => (F t (c + h) - F t c) / h
  have hQdiff : ∀ h : ℂ, h ∈ ball (0 : ℂ) R → DifferentiableOn ℂ (Q h) (ball (0 : ℂ) r) := by
    intro h hh
    have hmem : c + h ∈ ball c R := by simpa [mem_ball_iff_norm] using hh
    exact ((ht _ hmem).sub (ht c hcR)).div_const h
  -- uniform estimate
  have hunif : ∀ h : ℂ, h ∈ ball (0 : ℂ) (R / 2) → h ≠ 0 → ∀ t ∈ ball (0 : ℂ) r,
      ‖Q h t - deriv (F t) c‖ ≤ 16 * M * ‖h‖ / R ^ 2 := by
    intro h hh hh0 t htr
    have hR2 : 0 < R / 2 := by positivity
    have hφ : DifferentiableOn ℂ (fun s => F t (c + s)) (closedBall 0 (R / 2)) := by
      intro s hs
      have hs' : c + s ∈ ball c R := by
        simp only [mem_closedBall, dist_zero_right] at hs
        simp [mem_ball_iff_norm]; linarith
      have := (hζ t htr).differentiableAt (isOpen_ball.mem_nhds hs')
      exact (this.comp s (differentiableAt_const c |>.add differentiableAt_id)).differentiableWithinAt
    have hb : ∀ s ∈ closedBall (0 : ℂ) (R / 2), ‖F t (c + s)‖ ≤ M := by
      intro s hs
      simp only [mem_closedBall, dist_zero_right] at hs
      apply hM t htr
      simp [mem_ball_iff_norm]; linarith
    obtain ⟨-, -, h3⟩ := qcv_taylor2 hR2 hφ hb
    have hmem : h ∈ closedBall (0 : ℂ) (R / 2) := by
      simp only [mem_closedBall, dist_zero_right]; exact le_of_lt (by simpa using hh)
    have h3' := h3 h hmem
    have hder : deriv (fun s => F t (c + s)) 0 = deriv (F t) c := by
      have : HasDerivAt (F t) (deriv (F t) c) c :=
        ((hζ t htr).differentiableAt (isOpen_ball.mem_nhds hcR)).hasDerivAt
      have h0 : HasDerivAt (F t) (deriv (F t) c) (c + 0) := by simpa using this
      have h2 : HasDerivAt (fun s => F t (c + s)) (deriv (F t) c) 0 := h0.comp_const_add c 0
      exact h2.deriv
    simp only [add_zero, hder, smul_eq_mul] at h3'
    have hq : Q h t - deriv (F t) c = (F t (c + h) - F t c - h * deriv (F t) c) / h := by
      simp only [Q]; field_simp
    rw [hq, norm_div]
    rw [div_le_iff₀ (norm_pos_iff.2 hh0)]
    calc ‖F t (c + h) - F t c - h * deriv (F t) c‖ ≤ 4 * M * ‖h‖ ^ 2 / (R / 2) ^ 2 := h3'
      _ = 16 * M * ‖h‖ / R ^ 2 * ‖h‖ := by field_simp; ring
  -- the limit
  have hlim : TendstoUniformlyOn Q (fun t => deriv (F t) c) (𝓝[≠] (0 : ℂ)) (ball (0 : ℂ) r) := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    set δ : ℝ := min (R / 2) (ε * R ^ 2 / (32 * M + 1)) with hδdef
    have hδ : 0 < δ := lt_min (by positivity) (by positivity)
    have h1 : ∀ᶠ h in 𝓝[≠] (0 : ℂ), h ∈ ball (0 : ℂ) δ := nhdsWithin_le_nhds (Metric.ball_mem_nhds _ hδ)
    have h2 : ∀ᶠ h in 𝓝[≠] (0 : ℂ), h ≠ 0 := self_mem_nhdsWithin
    filter_upwards [h1, h2] with h hh hh0 t htr
    have hn : ‖h‖ < δ := by simpa using hh
    have hh2 : h ∈ ball (0 : ℂ) (R / 2) := by
      simp only [mem_ball, dist_zero_right]; exact hn.trans_le (min_le_left _ _)
    have hn2 : ‖h‖ < ε * R ^ 2 / (32 * M + 1) := hn.trans_le (min_le_right _ _)
    rw [dist_comm, dist_eq_norm]
    refine (hunif h hh2 hh0 t htr).trans_lt ?_
    have h32 : 0 < 32 * M + 1 := by positivity
    have := (lt_div_iff₀ h32).1 hn2
    rw [div_lt_iff₀ (by positivity)]
    nlinarith [norm_nonneg h]
  have hev : ∀ᶠ h in 𝓝[≠] (0 : ℂ), DifferentiableOn ℂ (Q h) (ball (0 : ℂ) r) := by
    filter_upwards [nhdsWithin_le_nhds (Metric.ball_mem_nhds (0 : ℂ) hR)] with h hh using hQdiff h hh
  exact hlim.tendstoLocallyUniformlyOn.differentiableOn hev isOpen_ball


/-- **Parameter-holomorphy of all iterated `ζ`-derivatives** (radii halve at each step). -/
theorem qcv_param_iteratedDeriv (j : ℕ) : ∀ {F : ℂ → ℂ → ℂ} {c : ℂ} {r R M : ℝ}, 0 < R → 0 ≤ M →
    (∀ t ∈ ball (0 : ℂ) r, DifferentiableOn ℂ (F t) (ball c R)) →
    (∀ ζ ∈ ball c R, DifferentiableOn ℂ (fun t => F t ζ) (ball (0 : ℂ) r)) →
    (∀ t ∈ ball (0 : ℂ) r, ∀ ζ ∈ ball c R, ‖F t ζ‖ ≤ M) →
    DifferentiableOn ℂ (fun t => iteratedDeriv j (F t) c) (ball (0 : ℂ) r) := by
  induction j with
  | zero =>
    intro F c r R M hR hM0 hζ ht hM
    simpa using ht c (mem_ball_self hR)
  | succ j ih =>
    intro F c r R M hR hM0 hζ ht hM
    have hR2 : 0 < R / 2 := by positivity
    have hsub : ∀ ζ ∈ ball c (R / 2), closedBall ζ (R / 2) ⊆ ball c R := by
      intro ζ hζc p hp
      simp only [mem_ball, mem_closedBall, dist_eq_norm] at hζc hp ⊢
      have := norm_sub_le_norm_sub_add_norm_sub p ζ c
      linarith
    have hbound : ∀ t ∈ ball (0 : ℂ) r, ∀ ζ ∈ ball c (R / 2), ‖deriv (F t) ζ‖ ≤ M / (R / 2) := by
      intro t htr ζ hζc
      refine Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hR2 ?_ ?_
      · have hd : DifferentiableOn ℂ (F t) (closure (ball ζ (R / 2))) := by
          rw [closure_ball _ hR2.ne']; exact (hζ t htr).mono (hsub ζ hζc)
        exact hd.diffContOnCl
      · intro p hp
        exact hM t htr p (hsub ζ hζc (sphere_subset_closedBall hp))
    have key := ih (F := fun t ζ => deriv (F t) ζ) (c := c) (r := r) (R := R / 2) (M := M / (R / 2)) hR2
      (by positivity)
      (fun t htr => ((hζ t htr).deriv isOpen_ball).mono (ball_subset_ball (by linarith)))
      (fun ζ hζc => by
        refine qcv_param_deriv (F := F) (c := ζ) (r := r) (R := R / 2) (M := M) hR2 hM0 ?_ ?_ ?_
        · intro t htr
          exact (hζ t htr).mono ((ball_subset_closedBall).trans (hsub ζ hζc))
        · intro p hp
          exact ht p (hsub ζ hζc (ball_subset_closedBall hp))
        · intro t htr p hp
          exact hM t htr p (hsub ζ hζc (ball_subset_closedBall hp)))
      hbound
    simpa [iteratedDeriv_succ'] using key


/-- **Cauchy criterion in `A∞(D)`**: if the weighted values `ψ_t(z)` are holomorphic in `t ∈ ball 0 r` and
bounded by `C`, then `t ↦ Ψ t` is complex differentiable at `0` as a map into the Banach space `A∞(D)`. -/
theorem qcv_ainf_diffAt {D : Set ℂ} [CompleteSpace (AInf D)] {Ψ : ℂ → AInf D} {r C : ℝ}
    (hr : 0 < r) (hC : 0 ≤ C)
    (hH : ∀ z : D, DifferentiableOn ℂ (fun t => (Ψ t).1 z) (ball (0 : ℂ) r))
    (hb : ∀ z : D, ∀ t ∈ ball (0 : ℂ) r, ‖(Ψ t).1 z‖ ≤ C) :
    DifferentiableAt ℂ Ψ 0 := by
  set R : ℝ := r / 2 with hR
  have hRpos : 0 < R := by positivity
  have hRr : closedBall (0 : ℂ) R ⊆ ball 0 r := by
    intro t ht
    simp only [mem_closedBall, dist_zero_right, mem_ball] at ht ⊢
    linarith
  let G : D → ℂ := fun z => deriv (fun t => (Ψ t).1 z) 0
  have hest : ∀ (z : D) (h : ℂ), ‖h‖ ≤ R →
      ‖(Ψ h).1 z - (Ψ 0).1 z - h * G z‖ ≤ 4 * C * ‖h‖ ^ 2 / R ^ 2 := by
    intro z h hh
    have := (qcv_taylor2 hRpos ((hH z).mono hRr) (fun t ht => hb z t (hRr ht))).2.2 h (by simpa using hh)
    simpa [G] using this
  let Q : ℂ → AInf D := fun h => h⁻¹ • (Ψ h - Ψ 0)
  have hQ : ∀ (h : ℂ) (z : D), (Q h).1 z = h⁻¹ * ((Ψ h).1 z - (Ψ 0).1 z) := by
    intro h z; simp [Q]
  have hQest : ∀ (h : ℂ), h ≠ 0 → ‖h‖ ≤ R → ∀ z : D, ‖(Q h).1 z - G z‖ ≤ 4 * C * ‖h‖ / R ^ 2 := by
    intro h hh0 hh z
    rw [hQ]
    have e : h⁻¹ * ((Ψ h).1 z - (Ψ 0).1 z) - G z = h⁻¹ * ((Ψ h).1 z - (Ψ 0).1 z - h * G z) := by
      field_simp
    rw [e, norm_mul, norm_inv]
    have := hest z h hh
    have hpos : 0 < ‖h‖ := norm_pos_iff.2 hh0
    calc ‖h‖⁻¹ * ‖(Ψ h).1 z - (Ψ 0).1 z - h * G z‖ ≤ ‖h‖⁻¹ * (4 * C * ‖h‖ ^ 2 / R ^ 2) := by gcongr
      _ = 4 * C * ‖h‖ / R ^ 2 := by field_simp
  have hcauchy : Cauchy (Filter.map Q (𝓝[≠] (0 : ℂ))) := by
    rw [Metric.cauchy_iff]
    refine ⟨inferInstance, fun ε hε => ?_⟩
    set δ : ℝ := min R (ε * R ^ 2 / (8 * C + 1)) with hδdef
    have hδ : 0 < δ := lt_min hRpos (by positivity)
    set S : Set ℂ := ball (0 : ℂ) δ ∩ {0}ᶜ with hS
    have hSmem : S ∈ 𝓝[≠] (0 : ℂ) :=
      inter_mem (nhdsWithin_le_nhds (Metric.ball_mem_nhds _ hδ)) self_mem_nhdsWithin
    refine ⟨Q '' S, Filter.image_mem_map hSmem, ?_⟩
    rintro _ ⟨h, ⟨hh, hh0⟩, rfl⟩ _ ⟨h', ⟨hh', hh0'⟩, rfl⟩
    have hh0 : h ≠ 0 := hh0
    have hh0' : h' ≠ 0 := hh0'
    have hn : ‖h‖ < δ := by simpa using hh
    have hn' : ‖h'‖ < δ := by simpa using hh'
    have hnR : ‖h‖ ≤ R := (hn.trans_le (min_le_left _ _)).le
    have hnR' : ‖h'‖ ≤ R := (hn'.trans_le (min_le_left _ _)).le
    have hε8 : δ ≤ ε * R ^ 2 / (8 * C + 1) := min_le_right _ _
    rw [dist_eq_norm]
    have hbound : ∀ z : D, ‖(Q h - Q h').1 z‖ ≤ 4 * C * (‖h‖ + ‖h'‖) / R ^ 2 := by
      intro z
      have e : (Q h - Q h').1 z = ((Q h).1 z - G z) - ((Q h').1 z - G z) := by
        simp only [Submodule.coe_sub, BoundedContinuousFunction.coe_sub, Pi.sub_apply]; ring
      rw [e]
      refine (norm_sub_le _ _).trans ?_
      have h1 := hQest h hh0 hnR z
      have h2 := hQest h' hh0' hnR' z
      calc _ ≤ 4 * C * ‖h‖ / R ^ 2 + 4 * C * ‖h'‖ / R ^ 2 := add_le_add h1 h2
        _ = _ := by ring
    have hnorm : ‖Q h - Q h'‖ ≤ 4 * C * (‖h‖ + ‖h'‖) / R ^ 2 := by
      have hB : 0 ≤ 4 * C * (‖h‖ + ‖h'‖) / R ^ 2 := by positivity
      change ‖((Q h - Q h' : AInf D) : D →ᵇ ℂ)‖ ≤ _
      exact (BoundedContinuousFunction.norm_le hB).2 hbound
    refine hnorm.trans_lt ?_
    rw [div_lt_iff₀ (by positivity)]
    have h8 := (le_div_iff₀ (by positivity : (0 : ℝ) < 8 * C + 1)).1 hε8
    nlinarith [norm_nonneg h, norm_nonneg h']
  obtain ⟨D', hD'⟩ := CompleteSpace.complete hcauchy
  have hT : Tendsto Q (𝓝[≠] (0 : ℂ)) (𝓝 D') := hD'
  have hd : HasDerivAt Ψ D' 0 := by
    rw [hasDerivAt_iff_tendsto_slope_zero]
    simpa [Q] using hT
  exact hd.differentiableAt



end QCV
end TakhtajanTeo
