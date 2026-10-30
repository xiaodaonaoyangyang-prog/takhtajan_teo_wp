import TakhtajanTeo.Ch1.GroupLemma25Completed
import TakhtajanTeo.Ch1.S3_TopologicalGroup
import TakhtajanTeo.Ch1.BeltramiDerivative
import TakhtajanTeo.Ch1.BeltramiGroup
import TakhtajanTeo.Ch1.AhlforsWeillCompleted
import TakhtajanTeo.Ch1.S1_1_Completed
import TakhtajanTeo.Ch1.ComponentTBasics
import TakhtajanTeo.Ch1.BeltramiTranslation
import TakhtajanTeo.Ch1.GroupAlgebra


/-!
# Group chain, part 1: `cor_2_6`, `lemma_2_7`, `remark_2_8`, `L2_inter_groupO_subgroup`, `lemma_3_4`

[下属2, T₀(1) program]  PREFIXED copies `grp_<name>` of the originals (statements byte-identical to the installed
originals; the originals themselves stay in `S2_HilbertManifold` / `S3_TopologicalGroup` for the leader to relocate):
`grp_cor_2_6`, `grp_lemma_2_7`, `grp_remark_2_8`, `grp_L2_inter_groupO_subgroup`, `grp_lemma_3_4`, plus the helper
`grp_gen_lip` (generator Lipschitz estimate) and the density/transfer helpers.  The only open original used is
`lemma_2_5` (through `delta0`); `grp_lemma_3_4` is axiom-clean.
-/

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal NNReal ComplexConjugate Classical Real
noncomputable section
namespace TakhtajanTeo
open LiZhongQC

theorem grp_exists_coe {x : ExtPlane} (h : x ≠ extInf) : ∃ v : ℂ, x = (v : ExtPlane) := by
  induction x using OnePoint.rec with
  | infty => exact absurd rfl h
  | coe v => exact ⟨v, rfl⟩

theorem grp_wAS_coe_injective (μ : LinfStar) : Function.Injective (fun z : ℂ => wAS μ (z : ExtPlane)) :=
  fun _ _ h => OnePoint.coe_injective ((wAS_bijective μ).1 h)

/-- The density inequality (general form).  Hypothesis `hD`: the hyperbolic-density distortion of
`h = wA (μ⁻¹)` is `≤ 2` at every finite point of `𝔻*`. -/
theorem grp_density_gen {μ : LinfStar} (hμ : μ ∈ LinfStarBall)
    (hD : ∀ u ∈ unitDiscExterior, wAS (beltramiInv μ) (u : ExtPlane) ≠ extInf →
      ‖dz (wA (beltramiInv μ)) u‖ ^ 2 / (1 - ‖wA (beltramiInv μ) u‖ ^ 2) ^ 2 ≤ 2 / (1 - ‖u‖ ^ 2) ^ 2)
    (F : ℂ → ℂ) :
    ∫⁻ z in unitDiscExterior, (‖F (wA μ z)‖₊ : ℝ≥0∞) ^ 2 * ENNReal.ofReal (rho z) ≤
      2 * ∫⁻ u in unitDiscExterior, (‖F u‖₊ : ℝ≥0∞) ^ 2 * ENNReal.ofReal (rho u) := by
  have hμ' : beltramiInv μ ∈ LinfStarBall := grp_inv_mem hμ
  obtain ⟨U, K, hUo, hUE, hsub, hKQC, himg⟩ := bc_wA_kqc hμ'
  have hDo : IsOpen unitDiscExterior := isOpen_lt continuous_const continuous_norm
  have hinvL : ∀ x, wAS μ (wAS (beltramiInv μ) x) = x := fun x => congrFun (grp_wAS_inv_left hμ) x
  have hinvR : ∀ x, wAS (beltramiInv μ) (wAS μ x) = x := fun x => congrFun (grp_wAS_inv_right hμ) x
  set G : ℂ → ℝ≥0∞ := fun z => (‖F (wA μ z)‖₊ : ℝ≥0∞) ^ 2 * ENNReal.ofReal (rho z) with hG
  -- the exceptional null set
  set T : Set ExtPlane := {extInf} ∪ (fun q : ℂ => (q : ExtPlane)) '' (unitDiscExterior \ U) with hT
  have hTfin : T.Finite := (Set.finite_singleton _).union (hsub.finite.image _)
  set N : Set ℂ := (fun z : ℂ => wAS μ (z : ExtPlane)) ⁻¹' T with hN
  have hN0 : volume N = 0 := (hTfin.preimage (grp_wAS_coe_injective μ).injOn).measure_zero _
  have hcover : unitDiscExterior ⊆ wA (beltramiInv μ) '' U ∪ N := by
    intro z hz
    by_cases hzN : z ∈ N
    · exact Or.inr hzN
    · left
      have hz1 : 1 < ‖z‖ := hz
      rcases wAS_maps_ext hμ hz1 with hinf | ⟨u, hu1, hu⟩
      · exact absurd (Or.inl hinf) hzN
      · have huU : u ∈ U := by
          by_contra hnU
          exact hzN (Or.inr ⟨u, ⟨hu1, hnU⟩, hu.symm⟩)
        refine ⟨u, huU, ?_⟩
        have : wAS (beltramiInv μ) (u : ExtPlane) = (z : ExtPlane) := by rw [← hu, hinvR]
        simp only [wA, this]
        rfl
  have hpole0 : volume {u : ℂ | wAS (beltramiInv μ) (u : ExtPlane) = extInf} = 0 :=
    ((Set.finite_singleton extInf).preimage (grp_wAS_coe_injective (beltramiInv μ)).injOn).measure_zero _
  have hae : ∀ᵐ u ∂(volume.restrict U), ENNReal.ofReal (jacobian (wA (beltramiInv μ)) u) *
      G (wA (beltramiInv μ) u) ≤ 2 * ((‖F u‖₊ : ℝ≥0∞) ^ 2 * ENNReal.ofReal (rho u)) := by
    have hne : ∀ᵐ u : ℂ, wAS (beltramiInv μ) (u : ExtPlane) ≠ extInf := by
      have := measure_eq_zero_iff_ae_notMem.1 hpole0
      exact this
    filter_upwards [ae_restrict_of_ae hne, ae_restrict_mem hUo.measurableSet] with u hu huU
    obtain ⟨v, hv⟩ := grp_exists_coe hu
    have hhu : wA (beltramiInv μ) u = v := by simp only [wA, hv]; rfl
    have hgh : wA μ v = u := by
      have : wAS μ (v : ExtPlane) = (u : ExtPlane) := by rw [← hv, hinvL]
      simp only [wA, this]
      rfl
    have hGh : G (wA (beltramiInv μ) u) = (‖F u‖₊ : ℝ≥0∞) ^ 2 * ENNReal.ofReal (rho v) := by
      simp only [hG, hhu, hgh]
    rw [hGh]
    have hu' : u ∈ unitDiscExterior := hUE huU
    have hbd := hD u hu' hu
    have hJ : jacobian (wA (beltramiInv μ)) u ≤ ‖dz (wA (beltramiInv μ)) u‖ ^ 2 := by
      unfold jacobian
      nlinarith [sq_nonneg ‖dzbar (wA (beltramiInv μ)) u‖]
    have hrho : ‖dz (wA (beltramiInv μ)) u‖ ^ 2 * rho v ≤ 2 * rho u := by
      have : rho v = 4 / (1 - ‖v‖ ^ 2) ^ 2 := rfl
      have h4 : rho u = 4 / (1 - ‖u‖ ^ 2) ^ 2 := rfl
      rw [this, h4]
      rw [hhu] at hbd
      calc ‖dz (wA (beltramiInv μ)) u‖ ^ 2 * (4 / (1 - ‖v‖ ^ 2) ^ 2)
          = 4 * (‖dz (wA (beltramiInv μ)) u‖ ^ 2 / (1 - ‖v‖ ^ 2) ^ 2) := by ring
        _ ≤ 4 * (2 / (1 - ‖u‖ ^ 2) ^ 2) := by gcongr
        _ = 2 * (4 / (1 - ‖u‖ ^ 2) ^ 2) := by ring
    have hrho0 : 0 ≤ rho v := by
      show 0 ≤ 4 / (1 - ‖v‖ ^ 2) ^ 2
      positivity
    calc ENNReal.ofReal (jacobian (wA (beltramiInv μ)) u) *
          ((‖F u‖₊ : ℝ≥0∞) ^ 2 * ENNReal.ofReal (rho v))
        ≤ ENNReal.ofReal (‖dz (wA (beltramiInv μ)) u‖ ^ 2) *
          ((‖F u‖₊ : ℝ≥0∞) ^ 2 * ENNReal.ofReal (rho v)) := by
          gcongr
      _ = (‖F u‖₊ : ℝ≥0∞) ^ 2 * ENNReal.ofReal (‖dz (wA (beltramiInv μ)) u‖ ^ 2 * rho v) := by
          rw [ENNReal.ofReal_mul (sq_nonneg _)]
          ring
      _ ≤ (‖F u‖₊ : ℝ≥0∞) ^ 2 * ENNReal.ofReal (2 * rho u) := by
          gcongr
      _ = 2 * ((‖F u‖₊ : ℝ≥0∞) ^ 2 * ENNReal.ofReal (rho u)) := by
          rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
          simp only [ENNReal.ofReal_ofNat]
          ring
  calc ∫⁻ z in unitDiscExterior, G z
      ≤ ∫⁻ z in wA (beltramiInv μ) '' U ∪ N, G z := lintegral_mono_set hcover
    _ ≤ (∫⁻ z in wA (beltramiInv μ) '' U, G z) + ∫⁻ z in N, G z := lintegral_union_le _ _ _
    _ = ∫⁻ z in wA (beltramiInv μ) '' U, G z := by
        rw [Measure.restrict_eq_zero.2 hN0, lintegral_zero_measure, add_zero]
    _ = ∫⁻ u in U, ENNReal.ofReal (jacobian (wA (beltramiInv μ)) u) * G (wA (beltramiInv μ) u) :=
        QCV.qcv_lintegral_image_eq hKQC G
    _ ≤ ∫⁻ u in U, 2 * ((‖F u‖₊ : ℝ≥0∞) ^ 2 * ENNReal.ofReal (rho u)) := lintegral_mono_ae hae
    _ = 2 * ∫⁻ u in U, (‖F u‖₊ : ℝ≥0∞) ^ 2 * ENNReal.ofReal (rho u) := by
        rw [lintegral_const_mul' _ _ (by norm_num)]
    _ ≤ 2 * ∫⁻ u in unitDiscExterior, (‖F u‖₊ : ℝ≥0∞) ^ 2 * ENNReal.ofReal (rho u) := by
        gcongr

theorem grp_delta0_spec : Lemma25Prop 1 delta0 := by
  have h := grp25_lemma_2_5 (ε := 1) one_pos
  unfold delta0
  rw [dif_pos h]
  exact h.choose_spec

theorem grp_lt_two_of_abs_lt {E a : ℝ} (h : |E - a| < a) : E < 2 * a := by
  have := (abs_lt.1 h).2
  linarith

theorem grp_mem_ball_of_lt_delta0 {μ : LinfStar} (h : ‖μ‖ < delta0) : μ ∈ LinfStarBall := by
  have := delta0_bounds.2
  simpa [LinfStarBall] using h.trans this

theorem grp_density_fwd {μ : LinfStar} (hμ : μ ∈ harmonicBeltrami) (hδ : ‖μ‖ < delta0) {F : ℂ → ℂ}
    (hF : AEStronglyMeasurable F (volume.restrict unitDiscExterior)) :
    ∫⁻ z in unitDiscExterior, (‖F (wA μ z)‖₊ : ℝ≥0∞) ^ 2 * ENNReal.ofReal (rho z) ≤
      2 * ∫⁻ u in unitDiscExterior, (‖F u‖₊ : ℝ≥0∞) ^ 2 * ENNReal.ofReal (rho u) := by
  have _ := hF
  refine grp_density_gen (grp_mem_ball_of_lt_delta0 hδ) (fun u hu hne => ?_) F
  have h := ((grp_delta0_spec.2.2 μ hμ hδ u (Or.inr hu)).2 hne)
  have h2 := grp_lt_two_of_abs_lt h
  have e : 2 * (1 / (1 - ‖u‖ ^ 2) ^ 2) = 2 / (1 - ‖u‖ ^ 2) ^ 2 := by ring
  linarith

theorem grp_density_inv {μ : LinfStar} (hμ : μ ∈ harmonicBeltrami) (hδ : ‖μ‖ < delta0) {F : ℂ → ℂ}
    (hF : AEStronglyMeasurable F (volume.restrict unitDiscExterior)) :
    ∫⁻ z in unitDiscExterior, (‖F (wA (beltramiInv μ) z)‖₊ : ℝ≥0∞) ^ 2 * ENNReal.ofReal (rho z) ≤
      2 * ∫⁻ u in unitDiscExterior, (‖F u‖₊ : ℝ≥0∞) ^ 2 * ENNReal.ofReal (rho u) := by
  have _ := hF
  have hb := grp_mem_ball_of_lt_delta0 hδ
  refine grp_density_gen (grp_inv_mem hb) (fun u hu hne => ?_) F
  rw [grp_inv_inv hb] at hne ⊢
  have h := ((grp_delta0_spec.2.2 μ hμ hδ u (Or.inr hu)).1 hne)
  have h2 := grp_lt_two_of_abs_lt h
  have e : 2 * (1 / (1 - ‖u‖ ^ 2) ^ 2) = 2 / (1 - ‖u‖ ^ 2) ^ 2 := by ring
  linarith

theorem grp_enorm_le {a b : ℂ} {c : ℝ} (hc : 0 ≤ c) (h : ‖a‖ ≤ c * ‖b‖) :
    (‖a‖₊ : ℝ≥0∞) ≤ ENNReal.ofReal c * (‖b‖₊ : ℝ≥0∞) := by
  have e : ∀ x : ℂ, (‖x‖₊ : ℝ≥0∞) = ENNReal.ofReal ‖x‖ := fun x => by
    rw [← coe_nnnorm, ENNReal.ofReal_coe_nnreal]
  rw [e, e, ← ENNReal.ofReal_mul hc]
  exact ENNReal.ofReal_le_ofReal h

theorem grp_rpow_half {c X Y : ℝ≥0∞} (h : X ≤ c ^ 2 * (2 * Y)) :
    X ^ (1 / 2 : ℝ) ≤ c * ENNReal.ofReal (Real.sqrt 2) * Y ^ (1 / 2 : ℝ) := by
  calc X ^ (1 / 2 : ℝ) ≤ (c ^ 2 * (2 * Y)) ^ (1 / 2 : ℝ) := ENNReal.rpow_le_rpow h (by norm_num)
    _ = c * ENNReal.ofReal (Real.sqrt 2) * Y ^ (1 / 2 : ℝ) := by
      rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
      have h1 : (c ^ 2) ^ (1 / 2 : ℝ) = c := by
        rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
        norm_num
      have h2 : (2 : ℝ≥0∞) ^ (1 / 2 : ℝ) = ENNReal.ofReal (Real.sqrt 2) := by
        rw [Real.sqrt_eq_rpow, ← ENNReal.ofReal_rpow_of_nonneg (by norm_num) (by norm_num)]
        simp
      rw [h1, h2]
      ring

/-- Transfer of the `L²` norm along the density inequality: a pointwise bound `|f(z)| ≤ c |g(w_μ z)|` a.e. gives
`‖f‖ ≤ c√2 ‖g‖`. -/
theorem grp_l2_transfer {μ : LinfStar} {c : ℝ} (hc0 : 0 ≤ c) (f g : LinfStar)
    (hpt : ∀ᵐ z ∂(volume.restrict unitDiscExterior), ‖f z‖ ≤ c * ‖g (wA μ z)‖)
    (hdens : ∫⁻ z in unitDiscExterior, (‖g (wA μ z)‖₊ : ℝ≥0∞) ^ 2 * ENNReal.ofReal (rho z) ≤
        2 * ∫⁻ u in unitDiscExterior, (‖g u‖₊ : ℝ≥0∞) ^ 2 * ENNReal.ofReal (rho u)) :
    normL2 unitDiscExterior f ≤ ENNReal.ofReal (c * Real.sqrt 2) * normL2 unitDiscExterior g := by
  have hint : ∫⁻ z in unitDiscExterior, (‖f z‖₊ : ℝ≥0∞) ^ 2 * ENNReal.ofReal (rho z) ≤
      ENNReal.ofReal c ^ 2 * (2 * ∫⁻ u in unitDiscExterior, (‖g u‖₊ : ℝ≥0∞) ^ 2 * ENNReal.ofReal (rho u)) := by
    calc ∫⁻ z in unitDiscExterior, (‖f z‖₊ : ℝ≥0∞) ^ 2 * ENNReal.ofReal (rho z)
        ≤ ∫⁻ z in unitDiscExterior, ENNReal.ofReal c ^ 2 * ((‖g (wA μ z)‖₊ : ℝ≥0∞) ^ 2 *
          ENNReal.ofReal (rho z)) := by
          refine lintegral_mono_ae ?_
          filter_upwards [hpt] with z hz
          have := grp_enorm_le hc0 hz
          calc (‖f z‖₊ : ℝ≥0∞) ^ 2 * ENNReal.ofReal (rho z)
              ≤ (ENNReal.ofReal c * (‖g (wA μ z)‖₊ : ℝ≥0∞)) ^ 2 * ENNReal.ofReal (rho z) := by gcongr
            _ = ENNReal.ofReal c ^ 2 * ((‖g (wA μ z)‖₊ : ℝ≥0∞) ^ 2 * ENNReal.ofReal (rho z)) := by ring
      _ = ENNReal.ofReal c ^ 2 * ∫⁻ z in unitDiscExterior, (‖g (wA μ z)‖₊ : ℝ≥0∞) ^ 2 *
          ENNReal.ofReal (rho z) := by
          rw [lintegral_const_mul' _ _ (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)]
      _ ≤ ENNReal.ofReal c ^ 2 * (2 * ∫⁻ u in unitDiscExterior, (‖g u‖₊ : ℝ≥0∞) ^ 2 *
          ENNReal.ofReal (rho u)) := by
          gcongr
  have key := grp_rpow_half hint
  rw [ENNReal.ofReal_mul hc0]
  unfold normL2
  exact key

theorem grp_cor26_gen {μ : LinfStar} (hμ : μ ∈ LinfStarBall) {r : ℝ} (hr : ‖μ‖ ≤ r) (hr1 : r < 1)
    (hdens : ∀ F : ℂ → ℂ, AEStronglyMeasurable F (volume.restrict unitDiscExterior) →
      ∫⁻ z in unitDiscExterior, (‖F (wA μ z)‖₊ : ℝ≥0∞) ^ 2 * ENNReal.ofReal (rho z) ≤
        2 * ∫⁻ u in unitDiscExterior, (‖F u‖₊ : ℝ≥0∞) ^ 2 * ENNReal.ofReal (rho u))
    {l : LinfStar} (hl : l ∈ LinfStarBall) (ν : LinfStar) :
    normL2 unitDiscExterior (fderiv ℂ (fun x => beltramiMul x μ) l ν) ≤
      ENNReal.ofReal (Real.sqrt 2 / (1 - r) ^ 2) * normL2 unitDiscExterior ν := by
  have hr0 : 0 ≤ r := (norm_nonneg μ).trans hr
  have h1r : 0 < 1 - r := by linarith
  set c : ℝ := 1 / (1 - r) ^ 2 with hc
  have hc0 : 0 < c := by positivity
  have hl1 : ‖l‖ < 1 := bc_norm_lt_one hl
  have hpt : ∀ᵐ z ∂(volume.restrict unitDiscExterior),
      ‖fderiv ℂ (fun x => beltramiMul x μ) l ν z‖ ≤ c * ‖ν (wA μ z)‖ := by
    filter_upwards [bd_fderiv_ae hμ hl ν, ae_restrict_of_ae (bc_wA_ae hμ), LinfStar_ae_norm_le μ,
      bc_pullback_ae hμ (LinfStar_ae_norm_le l)] with z hz hw hμz hlz
    rw [hz]
    have hdz : dz (wA μ) z ≠ 0 := hw.2.1
    have hc1 : ‖conj (dz (wA μ) z) / dz (wA μ) z‖ = 1 := by
      rw [norm_div, Complex.norm_conj, div_self (norm_ne_zero_iff.2 hdz)]
    set c0 : ℂ := conj (dz (wA μ) z) / dz (wA μ) z with hc0def
    set x : ℂ := conj (μ z) * (l (wA μ z) * c0) with hxdef
    have hx : ‖x‖ ≤ r := by
      rw [hxdef, norm_mul, Complex.norm_conj, norm_mul, hc1, mul_one]
      calc ‖μ z‖ * ‖l (wA μ z)‖ ≤ r * 1 := by
            apply mul_le_mul (hμz.trans hr) ((hlz).trans hl1.le) (norm_nonneg _) hr0
        _ = r := mul_one r
    have hd : 1 - r ≤ ‖1 + x‖ := by
      have h1 : ‖(1 : ℂ)‖ ≤ ‖1 + x‖ + ‖x‖ := by
        calc ‖(1 : ℂ)‖ = ‖(1 + x) - x‖ := by ring_nf
          _ ≤ ‖1 + x‖ + ‖x‖ := norm_sub_le _ _
      rw [norm_one] at h1
      linarith
    have hnum : ‖((1 - ‖μ z‖ ^ 2 : ℝ) : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_real, Real.norm_eq_abs]
      have h0 : 0 ≤ ‖μ z‖ := norm_nonneg _
      have h2 : ‖μ z‖ ≤ 1 := (hμz.trans hr).trans hr1.le
      rw [abs_le]
      constructor <;> nlinarith
    have hnum' : ‖(1 - (‖μ z‖ : ℂ) ^ 2)‖ ≤ 1 := by
      have : (1 - (‖μ z‖ : ℂ) ^ 2) = ((1 - ‖μ z‖ ^ 2 : ℝ) : ℂ) := by push_cast; ring
      rw [this]
      exact hnum
    rw [norm_div, norm_mul, norm_mul, norm_pow, hc1, mul_one]
    have hdpos : 0 < ‖1 + x‖ := lt_of_lt_of_le h1r hd
    rw [div_le_iff₀ (by positivity)]
    calc ‖(1 - (‖μ z‖ : ℂ) ^ 2)‖ * ‖ν (wA μ z)‖
        ≤ 1 * ‖ν (wA μ z)‖ := mul_le_mul_of_nonneg_right hnum' (norm_nonneg _)
      _ = ‖ν (wA μ z)‖ := one_mul _
      _ ≤ c * ‖ν (wA μ z)‖ * ‖1 + x‖ ^ 2 := by
          have h2 : 1 ≤ c * ‖1 + x‖ ^ 2 := by
            rw [hc, div_mul_eq_mul_div, one_mul, le_div_iff₀ (by positivity)]
            have : (1 - r) ^ 2 ≤ ‖1 + x‖ ^ 2 := pow_le_pow_left₀ h1r.le hd 2
            linarith
          nlinarith [norm_nonneg (ν (wA μ z))]
  have := grp_l2_transfer (μ := μ) hc0.le _ ν hpt (hdens ν (Lp.aestronglyMeasurable ν))
  have e : Real.sqrt 2 / (1 - r) ^ 2 = c * Real.sqrt 2 := by rw [hc]; ring
  rw [e]
  exact this

theorem grp_cor_2_6 {μ : LinfStar} (hμ : μ ∈ harmonicBeltrami) (hδ : ‖μ‖ < delta0) {l : LinfStar} (hl : l ∈ LinfStarBall)
    (ν : LinfStar) :
    normL2 unitDiscExterior (fderiv ℂ (fun x => beltramiMul x μ) l ν) ≤
        ENNReal.ofReal (Real.sqrt 2 / (1 - ‖μ‖) ^ 2) * normL2 unitDiscExterior ν ∧
      normL2 unitDiscExterior (fderiv ℂ (fun x => beltramiMul x (beltramiInv μ)) l ν) ≤
        ENNReal.ofReal (Real.sqrt 2 / (1 - ‖μ‖) ^ 2) * normL2 unitDiscExterior ν := by
  have hb := grp_mem_ball_of_lt_delta0 hδ
  have h1 : ‖μ‖ < 1 := bc_norm_lt_one hb
  refine ⟨grp_cor26_gen hb le_rfl h1 (fun F hF => grp_density_fwd hμ hδ hF) hl ν, ?_⟩
  exact grp_cor26_gen (grp_inv_mem hb) (bc_beltramiInv_norm_le hb) h1
    (fun F hF => grp_density_inv hμ hδ hF) hl ν

theorem grp_mobius_sub (m c b₁ b₂ : ℂ) (h1 : 1 + c * b₁ ≠ 0) (h2 : 1 + c * b₂ ≠ 0) :
    (m + b₁) / (1 + c * b₁) - (m + b₂) / (1 + c * b₂) =
      (1 - m * c) * (b₁ - b₂) / ((1 + c * b₁) * (1 + c * b₂)) := by
  rw [div_sub_div _ _ h1 h2]
  congr 1
  ring

theorem grp_den_ge {m b : ℂ} {r : ℝ} (hm : ‖m‖ ≤ r) (hr0 : 0 ≤ r) (hb : ‖b‖ ≤ 1) :
    1 - r ≤ ‖1 + conj m * b‖ := by
  have hq : ‖conj m * b‖ ≤ r := by
    rw [norm_mul, Complex.norm_conj]
    calc ‖m‖ * ‖b‖ ≤ r * 1 := mul_le_mul hm hb (norm_nonneg _) hr0
      _ = r := mul_one r
  have h1 : ‖(1 : ℂ)‖ ≤ ‖1 + conj m * b‖ + ‖conj m * b‖ := by
    calc ‖(1 : ℂ)‖ = ‖(1 + conj m * b) - conj m * b‖ := by ring_nf
      _ ≤ ‖1 + conj m * b‖ + ‖conj m * b‖ := norm_sub_le _ _
  rw [norm_one] at h1
  linarith

theorem grp_mobius_lip {m b₁ b₂ : ℂ} {r : ℝ} (hm : ‖m‖ ≤ r) (hr1 : r < 1) (hb1 : ‖b₁‖ ≤ 1)
    (hb2 : ‖b₂‖ ≤ 1) :
    ‖(m + b₁) / (1 + conj m * b₁) - (m + b₂) / (1 + conj m * b₂)‖ ≤ 1 / (1 - r) ^ 2 * ‖b₁ - b₂‖ := by
  have hr0 : 0 ≤ r := (norm_nonneg m).trans hm
  have h1r : 0 < 1 - r := by linarith
  have hd1 := grp_den_ge hm hr0 hb1
  have hd2 := grp_den_ge hm hr0 hb2
  have hn1 : 1 + conj m * b₁ ≠ 0 := norm_pos_iff.1 (lt_of_lt_of_le h1r hd1)
  have hn2 : 1 + conj m * b₂ ≠ 0 := norm_pos_iff.1 (lt_of_lt_of_le h1r hd2)
  have hmm : ‖(1 : ℂ) - m * conj m‖ ≤ 1 := by
    have e : (1 : ℂ) - m * conj m = ((1 - ‖m‖ ^ 2 : ℝ) : ℂ) := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
      push_cast
      ring
    rw [e, Complex.norm_real, Real.norm_eq_abs, abs_le]
    have h0 : 0 ≤ ‖m‖ := norm_nonneg _
    have h2 : ‖m‖ ≤ 1 := hm.trans hr1.le
    constructor <;> nlinarith
  rw [grp_mobius_sub m (conj m) b₁ b₂ hn1 hn2, norm_div, norm_mul, norm_mul]
  have hK : (1 - r) ^ 2 ≤ ‖1 + conj m * b₁‖ * ‖1 + conj m * b₂‖ := by
    rw [sq]
    exact mul_le_mul hd1 hd2 h1r.le (norm_nonneg _)
  have hKpos : 0 < ‖1 + conj m * b₁‖ * ‖1 + conj m * b₂‖ := lt_of_lt_of_le (by positivity) hK
  rw [div_le_iff₀ hKpos]
  have h3 : 1 ≤ 1 / (1 - r) ^ 2 * (‖1 + conj m * b₁‖ * ‖1 + conj m * b₂‖) := by
    have : 1 / (1 - r) ^ 2 * (‖1 + conj m * b₁‖ * ‖1 + conj m * b₂‖) =
        (‖1 + conj m * b₁‖ * ‖1 + conj m * b₂‖) / (1 - r) ^ 2 := by ring
    rw [this, le_div_iff₀ (by positivity)]
    linarith
  calc ‖(1 : ℂ) - m * conj m‖ * ‖b₁ - b₂‖ ≤ 1 * ‖b₁ - b₂‖ :=
        mul_le_mul_of_nonneg_right hmm (norm_nonneg _)
    _ ≤ (1 / (1 - r) ^ 2 * (‖1 + conj m * b₁‖ * ‖1 + conj m * b₂‖)) * ‖b₁ - b₂‖ :=
        mul_le_mul_of_nonneg_right h3 (norm_nonneg _)
    _ = 1 / (1 - r) ^ 2 * ‖b₁ - b₂‖ * (‖1 + conj m * b₁‖ * ‖1 + conj m * b₂‖) := by ring

theorem grp_lip_gen {μ : LinfStar} (hμ : μ ∈ LinfStarBall) {r : ℝ} (hr : ‖μ‖ ≤ r) (hr1 : r < 1)
    (hdens : ∀ F : ℂ → ℂ, AEStronglyMeasurable F (volume.restrict unitDiscExterior) →
      ∫⁻ z in unitDiscExterior, (‖F (wA μ z)‖₊ : ℝ≥0∞) ^ 2 * ENNReal.ofReal (rho z) ≤
        2 * ∫⁻ u in unitDiscExterior, (‖F u‖₊ : ℝ≥0∞) ^ 2 * ENNReal.ofReal (rho u))
    {l₁ l₂ : LinfStar} (h1 : l₁ ∈ LinfStarBall) (h2 : l₂ ∈ LinfStarBall) :
    normL2 unitDiscExterior (beltramiMul l₁ μ - beltramiMul l₂ μ : LinfStar) ≤
      ENNReal.ofReal (1 / (1 - r) ^ 2 * Real.sqrt 2) * normL2 unitDiscExterior (l₁ - l₂ : LinfStar) := by
  have hr0 : 0 ≤ r := (norm_nonneg μ).trans hr
  have h1r : 0 < 1 - r := by linarith
  have hl1 := bc_norm_lt_one h1
  have hl2 := bc_norm_lt_one h2
  refine grp_l2_transfer (μ := μ) (by positivity) _ _ ?_
    (hdens _ (Lp.aestronglyMeasurable (l₁ - l₂ : LinfStar)))
  filter_upwards [Lp.coeFn_sub (beltramiMul l₁ μ) (beltramiMul l₂ μ), bc_mul_ae hμ h1, bc_mul_ae hμ h2,
    ae_restrict_of_ae (bc_wA_ae hμ), LinfStar_ae_norm_le μ, bc_pullback_ae hμ (Lp.coeFn_sub l₁ l₂),
    bc_b_bound (l := l₁) hμ, bc_b_bound (l := l₂) hμ] with z hf hm1 hm2 hw hμz hgp hb1 hb2
  rw [hf, Pi.sub_apply, hm1, hm2, hgp, Pi.sub_apply]
  have hdz : dz (wA μ) z ≠ 0 := hw.2.1
  have hc1 : ‖conj (dz (wA μ) z) / dz (wA μ) z‖ = 1 := by
    rw [norm_div, Complex.norm_conj, div_self (norm_ne_zero_iff.2 hdz)]
  set c0 : ℂ := conj (dz (wA μ) z) / dz (wA μ) z with hc0def
  have e1 : conj (μ z) * l₁ (wA μ z) * c0 = conj (μ z) * (l₁ (wA μ z) * c0) := mul_assoc _ _ _
  have e2 : conj (μ z) * l₂ (wA μ z) * c0 = conj (μ z) * (l₂ (wA μ z) * c0) := mul_assoc _ _ _
  rw [e1, e2]
  have key := grp_mobius_lip (m := μ z) (b₁ := l₁ (wA μ z) * c0) (b₂ := l₂ (wA μ z) * c0)
    (hμz.trans hr) hr1 (hb1.trans hl1.le) (hb2.trans hl2.le)
  have e3 : l₁ (wA μ z) * c0 - l₂ (wA μ z) * c0 = (l₁ (wA μ z) - l₂ (wA μ z)) * c0 := by ring
  rw [e3, norm_mul, hc1, mul_one] at key
  exact key

theorem grp_gen_lip {μ : LinfStar} (hμ : μ ∈ harmonicBeltrami) (hδ : ‖μ‖ < delta0) :
    ∃ C > 0, ∀ l₁ ∈ LinfStarBall, ∀ l₂ ∈ LinfStarBall, normL2 unitDiscExterior (l₁ - l₂ : LinfStar) < ∞ →
      normL2 unitDiscExterior (beltramiMul l₁ μ - beltramiMul l₂ μ : LinfStar) ≤
        ENNReal.ofReal C * normL2 unitDiscExterior (l₁ - l₂ : LinfStar) ∧
      normL2 unitDiscExterior (beltramiMul l₁ (beltramiInv μ) - beltramiMul l₂ (beltramiInv μ) : LinfStar) ≤
        ENNReal.ofReal C * normL2 unitDiscExterior (l₁ - l₂ : LinfStar) := by
  have hb := grp_mem_ball_of_lt_delta0 hδ
  have h1 : ‖μ‖ < 1 := bc_norm_lt_one hb
  have h1r : 0 < 1 - ‖μ‖ := by linarith
  refine ⟨1 / (1 - ‖μ‖) ^ 2 * Real.sqrt 2, by positivity, fun l₁ hl₁ l₂ hl₂ _ => ⟨?_, ?_⟩⟩
  · exact grp_lip_gen hb le_rfl h1 (fun F hF => grp_density_fwd hμ hδ hF) hl₁ hl₂
  · exact grp_lip_gen (grp_inv_mem hb) (bc_beltramiInv_norm_le hb) h1
      (fun F hF => grp_density_inv hμ hδ hF) hl₁ hl₂

theorem grp_lip_mul {a b : LinfStar} (ha : a ∈ LinfStarBall) (hb : b ∈ LinfStarBall)
    (Pa : ∃ C > 0, ∀ l₁ ∈ LinfStarBall, ∀ l₂ ∈ LinfStarBall, normL2 unitDiscExterior (l₁ - l₂ : LinfStar) < ∞ →
      normL2 unitDiscExterior (beltramiMul l₁ a - beltramiMul l₂ a : LinfStar) ≤
        ENNReal.ofReal C * normL2 unitDiscExterior (l₁ - l₂ : LinfStar))
    (Pb : ∃ C > 0, ∀ l₁ ∈ LinfStarBall, ∀ l₂ ∈ LinfStarBall, normL2 unitDiscExterior (l₁ - l₂ : LinfStar) < ∞ →
      normL2 unitDiscExterior (beltramiMul l₁ b - beltramiMul l₂ b : LinfStar) ≤
        ENNReal.ofReal C * normL2 unitDiscExterior (l₁ - l₂ : LinfStar)) :
    ∃ C > 0, ∀ l₁ ∈ LinfStarBall, ∀ l₂ ∈ LinfStarBall, normL2 unitDiscExterior (l₁ - l₂ : LinfStar) < ∞ →
      normL2 unitDiscExterior (beltramiMul l₁ (beltramiMul a b) - beltramiMul l₂ (beltramiMul a b) : LinfStar) ≤
        ENNReal.ofReal C * normL2 unitDiscExterior (l₁ - l₂ : LinfStar) := by
  obtain ⟨Ca, hCa, hA⟩ := Pa
  obtain ⟨Cb, hCb, hB⟩ := Pb
  refine ⟨Cb * Ca, mul_pos hCb hCa, fun l₁ h1 l₂ h2 hfin => ?_⟩
  rw [← grp_mul_assoc h1 ha hb, ← grp_mul_assoc h2 ha hb]
  have hA' := hA l₁ h1 l₂ h2 hfin
  have hfin' : normL2 unitDiscExterior (beltramiMul l₁ a - beltramiMul l₂ a : LinfStar) < ∞ :=
    lt_of_le_of_lt hA' (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfin)
  have hB' := hB _ (grp_mul_mem h1 ha) _ (grp_mul_mem h2 ha) hfin'
  calc normL2 unitDiscExterior (beltramiMul (beltramiMul l₁ a) b - beltramiMul (beltramiMul l₂ a) b : LinfStar)
      ≤ ENNReal.ofReal Cb * normL2 unitDiscExterior (beltramiMul l₁ a - beltramiMul l₂ a : LinfStar) := hB'
    _ ≤ ENNReal.ofReal Cb * (ENNReal.ofReal Ca * normL2 unitDiscExterior (l₁ - l₂ : LinfStar)) := by
        gcongr
    _ = ENNReal.ofReal (Cb * Ca) * normL2 unitDiscExterior (l₁ - l₂ : LinfStar) := by
        rw [ENNReal.ofReal_mul hCb.le, mul_assoc]

theorem grp_lemma_2_7 {μ : LinfStar} (hμ : μ ∈ groupO) :
    ∃ C > 0, ∀ l₁ ∈ LinfStarBall, ∀ l₂ ∈ LinfStarBall, normL2 unitDiscExterior (l₁ - l₂ : LinfStar) < ∞ →
      normL2 unitDiscExterior (beltramiMul l₁ μ - beltramiMul l₂ μ : LinfStar) ≤
        ENNReal.ofReal C * normL2 unitDiscExterior (l₁ - l₂ : LinfStar) := by
  have key := grp_groupO_induction
    (P := fun ν => (∃ C > 0, ∀ l₁ ∈ LinfStarBall, ∀ l₂ ∈ LinfStarBall,
        normL2 unitDiscExterior (l₁ - l₂ : LinfStar) < ∞ →
        normL2 unitDiscExterior (beltramiMul l₁ ν - beltramiMul l₂ ν : LinfStar) ≤
          ENNReal.ofReal C * normL2 unitDiscExterior (l₁ - l₂ : LinfStar)) ∧
      (∃ C > 0, ∀ l₁ ∈ LinfStarBall, ∀ l₂ ∈ LinfStarBall,
        normL2 unitDiscExterior (l₁ - l₂ : LinfStar) < ∞ →
        normL2 unitDiscExterior (beltramiMul l₁ (beltramiInv ν) - beltramiMul l₂ (beltramiInv ν) : LinfStar) ≤
          ENNReal.ofReal C * normL2 unitDiscExterior (l₁ - l₂ : LinfStar)))
    (fun ν hν hδ => by
      obtain ⟨C, hC, h⟩ := grp_gen_lip hν hδ
      exact ⟨⟨C, hC, fun l₁ h1 l₂ h2 hf => (h l₁ h1 l₂ h2 hf).1⟩,
        ⟨C, hC, fun l₁ h1 l₂ h2 hf => (h l₁ h1 l₂ h2 hf).2⟩⟩)
    (fun a b ha hb Pa Pb => by
      obtain ⟨Pa1, Pa2⟩ := Pa
      obtain ⟨Pb1, Pb2⟩ := Pb
      refine ⟨grp_lip_mul ha hb Pa1 Pb1, ?_⟩
      rw [grp_inv_mul_rev ha hb]
      exact grp_lip_mul (grp_inv_mem hb) (grp_inv_mem ha) Pb2 Pa2)
    (fun a ha Pa => by
      obtain ⟨Pa1, Pa2⟩ := Pa
      refine ⟨Pa2, ?_⟩
      rw [grp_inv_inv ha]
      exact Pa1)
    μ hμ
  exact key.2.1

theorem grp_fd_mul {a b : LinfStar} (ha : a ∈ LinfStarBall) (hb : b ∈ LinfStarBall)
    (Pa : ∃ C > 0, ∀ l ∈ LinfStarBall, ∀ ν : LinfStar,
      normL2 unitDiscExterior (fderiv ℂ (fun x => beltramiMul x a) l ν) ≤
        ENNReal.ofReal C * normL2 unitDiscExterior ν)
    (Pb : ∃ C > 0, ∀ l ∈ LinfStarBall, ∀ ν : LinfStar,
      normL2 unitDiscExterior (fderiv ℂ (fun x => beltramiMul x b) l ν) ≤
        ENNReal.ofReal C * normL2 unitDiscExterior ν) :
    ∃ C > 0, ∀ l ∈ LinfStarBall, ∀ ν : LinfStar,
      normL2 unitDiscExterior (fderiv ℂ (fun x => beltramiMul x (beltramiMul a b)) l ν) ≤
        ENNReal.ofReal C * normL2 unitDiscExterior ν := by
  obtain ⟨Ca, hCa, hA⟩ := Pa
  obtain ⟨Cb, hCb, hB⟩ := Pb
  refine ⟨Cb * Ca, mul_pos hCb hCa, fun l hl ν => ?_⟩
  have hopen : IsOpen LinfStarBall := Metric.isOpen_ball
  have hda : DifferentiableAt ℂ (fun x => beltramiMul x a) l :=
    (bd_differentiableOn ha).differentiableAt (hopen.mem_nhds hl)
  have hla : beltramiMul l a ∈ LinfStarBall := grp_mul_mem hl ha
  have hdb : DifferentiableAt ℂ (fun x => beltramiMul x b) (beltramiMul l a) :=
    (bd_differentiableOn hb).differentiableAt (hopen.mem_nhds hla)
  have heq : (fun x => beltramiMul x (beltramiMul a b)) =ᶠ[nhds l]
      (fun x => beltramiMul x b) ∘ (fun x => beltramiMul x a) := by
    filter_upwards [hopen.mem_nhds hl] with x hx
    exact (grp_mul_assoc hx ha hb).symm
  rw [heq.fderiv_eq, fderiv_comp l hdb hda, ContinuousLinearMap.comp_apply]
  calc normL2 unitDiscExterior (fderiv ℂ (fun x => beltramiMul x b) (beltramiMul l a)
        (fderiv ℂ (fun x => beltramiMul x a) l ν))
      ≤ ENNReal.ofReal Cb * normL2 unitDiscExterior (fderiv ℂ (fun x => beltramiMul x a) l ν) :=
        hB _ hla _
    _ ≤ ENNReal.ofReal Cb * (ENNReal.ofReal Ca * normL2 unitDiscExterior ν) := by
        gcongr
        exact hA l hl ν
    _ = ENNReal.ofReal (Cb * Ca) * normL2 unitDiscExterior ν := by
        rw [ENNReal.ofReal_mul hCb.le, mul_assoc]

theorem grp_remark_2_8 {μ : LinfStar} (hμ : μ ∈ groupO) :
    ∃ C > 0, ∀ l ∈ LinfStarBall, ∀ ν : LinfStar,
      normL2 unitDiscExterior (fderiv ℂ (fun x => beltramiMul x μ) l ν) ≤ ENNReal.ofReal C * normL2 unitDiscExterior ν := by
  have key := grp_groupO_induction
    (P := fun ν => (∃ C > 0, ∀ l ∈ LinfStarBall, ∀ x : LinfStar,
        normL2 unitDiscExterior (fderiv ℂ (fun y => beltramiMul y ν) l x) ≤
          ENNReal.ofReal C * normL2 unitDiscExterior x) ∧
      (∃ C > 0, ∀ l ∈ LinfStarBall, ∀ x : LinfStar,
        normL2 unitDiscExterior (fderiv ℂ (fun y => beltramiMul y (beltramiInv ν)) l x) ≤
          ENNReal.ofReal C * normL2 unitDiscExterior x))
    (fun ν hν hδ => by
      have hb := grp_mem_ball_of_lt_delta0 hδ
      have h1 : ‖ν‖ < 1 := bc_norm_lt_one hb
      have h1r : 0 < 1 - ‖ν‖ := by linarith
      exact ⟨⟨Real.sqrt 2 / (1 - ‖ν‖) ^ 2, by positivity,
          fun l hl x => (grp_cor_2_6 hν hδ hl x).1⟩,
        ⟨Real.sqrt 2 / (1 - ‖ν‖) ^ 2, by positivity,
          fun l hl x => (grp_cor_2_6 hν hδ hl x).2⟩⟩)
    (fun a b ha hb Pa Pb => by
      obtain ⟨Pa1, Pa2⟩ := Pa
      obtain ⟨Pb1, Pb2⟩ := Pb
      refine ⟨grp_fd_mul ha hb Pa1 Pb1, ?_⟩
      rw [grp_inv_mul_rev ha hb]
      exact grp_fd_mul (grp_inv_mem hb) (grp_inv_mem ha) Pb2 Pa2)
    (fun a ha Pa => by
      obtain ⟨Pa1, Pa2⟩ := Pa
      refine ⟨Pa2, ?_⟩
      rw [grp_inv_inv ha]
      exact Pa1)
    μ hμ
  exact key.2.1

theorem grp_normL2_eq (D : Set ℂ) {f : ℂ → ℂ} (hf : AEStronglyMeasurable f (volume.restrict D)) :
    normL2 D f = eLpNorm f 2 ((volume.restrict D).withDensity (fun z => ENNReal.ofReal (rho z))) := by
  have hmeas : Measurable (fun z : ℂ => ENNReal.ofReal (rho z)) := by
    unfold rho
    fun_prop
  have hac := withDensity_absolutelyContinuous (volume.restrict D) (fun z => ENNReal.ofReal (rho z))
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by simp) (hf.mono_ac hac),
    lintegral_withDensity_eq_lintegral_mul_non_measurable _ hmeas
      (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  unfold normL2
  simp only [Pi.mul_apply, ENNReal.toReal_ofNat, ENNReal.rpow_two, one_div]
  congr 1
  refine lintegral_congr (fun z => ?_)
  rw [mul_comm]
  rfl

theorem grp_normL2_congr_ae {D : Set ℂ} {f g : ℂ → ℂ} (h : f =ᵐ[volume.restrict D] g) :
    normL2 D f = normL2 D g := by
  unfold normL2
  congr 1
  refine lintegral_congr_ae ?_
  filter_upwards [h] with z hz
  rw [hz]

theorem grp_normL2_sub_le {f g : ℂ → ℂ} (hf : AEStronglyMeasurable f (volume.restrict unitDiscExterior))
    (hg : AEStronglyMeasurable g (volume.restrict unitDiscExterior)) :
    normL2 unitDiscExterior (fun z => f z - g z) ≤
      normL2 unitDiscExterior f + normL2 unitDiscExterior g := by
  have h1 := grp_normL2_eq unitDiscExterior (f := fun z => f z - g z) (hf.sub hg)
  rw [h1, grp_normL2_eq _ hf, grp_normL2_eq _ hg]
  exact eLpNorm_sub_le (f := f) (g := g) (by norm_num)

theorem grp_L2_inter_groupO_subgroup {l ν : LinfStar} (hl : l ∈ groupO) (hν : ν ∈ groupO)
    (hl2 : normL2 unitDiscExterior l < ∞) (hν2 : normL2 unitDiscExterior ν < ∞) :
    beltramiMul l (beltramiInv ν) ∈ groupO ∧ normL2 unitDiscExterior (beltramiMul l (beltramiInv ν)) < ∞ := by
  refine ⟨groupO_mul_mem hl (groupO_inv_mem hν), ?_⟩
  have hlb : l ∈ LinfStarBall :=
    (grp_groupO_induction (P := fun _ => True) (fun _ _ _ => trivial)
      (fun _ _ _ _ _ _ => trivial) (fun _ _ _ => trivial) l hl).1
  have hνb : ν ∈ LinfStarBall :=
    (grp_groupO_induction (P := fun _ => True) (fun _ _ _ => trivial)
      (fun _ _ _ _ _ _ => trivial) (fun _ _ _ => trivial) ν hν).1
  obtain ⟨C, hC, h⟩ := grp_lemma_2_7 (groupO_inv_mem hν)
  have hfin : normL2 unitDiscExterior (l - ν : LinfStar) < ∞ := by
    have h1 := grp_normL2_sub_le (Lp.aestronglyMeasurable l) (Lp.aestronglyMeasurable ν)
    have h2 := grp_normL2_congr_ae (D := unitDiscExterior) (Lp.coeFn_sub l ν)
    rw [h2]
    exact lt_of_le_of_lt h1 (ENNReal.add_lt_top.2 ⟨hl2, hν2⟩)
  have h3 := h l hlb ν hνb hfin
  rw [grp_mul_inv hνb, sub_zero] at h3
  exact lt_of_le_of_lt h3 (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfin)

theorem grp_comp_eq {p q : T1} (h : q ∈ componentT p) : componentT q = componentT p :=
  (@connectedComponent_eq T1 hilbertTopology p q h).symm

theorem grp_mem_comp (p : T1) : p ∈ componentT p := @mem_connectedComponent T1 hilbertTopology p

theorem grp_rightTrans_origin (ν : LinfStarBall) : rightTrans ν originT = Phi ν := by
  have h0 : originT = Phi ⟨0, mem_ball_self one_pos⟩ := rfl
  rw [h0, bt_rightTrans_phi]
  congr 1
  exact Subtype.ext (grp_zero_mul ν.2)

theorem grp_image_T01 (ν : LinfStarBall) : rightTrans ν '' T01 = componentT (Phi ν) := by
  obtain ⟨h, hh⟩ := ctb_componentT_spec_two originT ν
  have e2 : Phi (⟨_, h⟩ : LinfStarBall) = rightTrans ν originT := by
    have : rightTrans ν originT = rightTrans ν (Phi (Quotient.out originT)) := by
      rw [show Phi (Quotient.out originT) = originT from Quotient.out_eq originT]
    rw [this, bt_rightTrans_phi]
  rw [← grp_rightTrans_origin ν, ← e2]
  exact hh

theorem grp_lemma_3_4 : originT ∈ T01 ∧ (∀ p ∈ T01, ∀ q ∈ T01, mulT p q ∈ T01) ∧ ∀ p ∈ T01, invT p ∈ T01 := by
  have hT : T01 = componentT originT := rfl
  refine ⟨grp_mem_comp _, ?_, ?_⟩
  · intro p hp q hq
    have hm : beltramiMul (Quotient.out p : LinfStarBall) (Quotient.out q : LinfStarBall) ∈ LinfStarBall :=
      bg_mul_mem_ball (Quotient.out q).2 (Quotient.out p).2
    have e : mulT p q = rightTrans (Quotient.out q) p := by
      unfold mulT rightTrans
      rw [dif_pos hm]
    rw [e]
    have himg := grp_image_T01 (Quotient.out q)
    have hq' : componentT (Phi (Quotient.out q)) = T01 := by
      rw [show Phi (Quotient.out q : LinfStarBall) = q from Quotient.out_eq q, hT]
      exact grp_comp_eq (p := originT) hq
    rw [hq'] at himg
    have hmem : rightTrans (Quotient.out q) p ∈ rightTrans (Quotient.out q) '' T01 := ⟨p, hp, rfl⟩
    rwa [himg] at hmem
  · intro p hp
    have hi : beltramiInv ((Quotient.out p : LinfStarBall) : LinfStar) ∈ LinfStarBall :=
      grp_inv_mem (Quotient.out p : LinfStarBall).2
    have e : invT p = Phi (⟨beltramiInv ((Quotient.out p : LinfStarBall) : LinfStar), hi⟩ : LinfStarBall) := by
      unfold invT
      exact dif_pos hi
    have h0 : rightTrans (⟨beltramiInv ((Quotient.out p : LinfStarBall) : LinfStar), hi⟩ : LinfStarBall) p
        = originT := by
      have h1 := bt_rightTrans_phi
        (⟨beltramiInv ((Quotient.out p : LinfStarBall) : LinfStar), hi⟩ : LinfStarBall) (Quotient.out p)
      rw [show Phi (Quotient.out p : LinfStarBall) = p from Quotient.out_eq p] at h1
      rw [h1]
      have h00 : originT = Phi ⟨0, mem_ball_self one_pos⟩ := rfl
      rw [h00]
      congr 1
      exact Subtype.ext (grp_mul_inv (Quotient.out p : LinfStarBall).2)
    have hmem : originT ∈ componentT (Phi (⟨beltramiInv ((Quotient.out p : LinfStarBall) : LinfStar), hi⟩ :
        LinfStarBall)) := by
      rw [← grp_image_T01]
      exact ⟨p, hp, h0⟩
    have hcc := grp_comp_eq hmem
    rw [e, hT, hcc]
    exact grp_mem_comp _

/-- **Lemma 3.4** (TT:1944). `T₀(1)` is a subgroup of `T(1)`. -/
theorem lemma_3_4 : originT ∈ T01 ∧ (∀ p ∈ T01, ∀ q ∈ T01, mulT p q ∈ T01) ∧ ∀ p ∈ T01, invT p ∈ T01 :=
  grp_lemma_3_4

end TakhtajanTeo
