import TakhtajanTeo.Ch1.ComponentRelativeCoefficient
import TakhtajanTeo.Ch1.ComponentRelativeAmbient
import TakhtajanTeo.Ch1.ComponentRelativeBoundary
import TakhtajanTeo.Ch1.ComponentRelativeCollar
import TakhtajanTeo.Ch1.ComponentRelativeLeaf
import TakhtajanTeo.Ch1.ComponentRelativeBlowup
import TakhtajanTeo.Ch1.ComponentNonlinearFormula
import TakhtajanTeo.Ch1.ComponentNonlinearLocal
import TakhtajanTeo.Ch1.ComponentNonlinearEnergy
import TakhtajanTeo.Ch1.ComponentCoreEnergy
import TakhtajanTeo.Ch1.ComponentContactNormalization
import TakhtajanTeo.Ch1.ComponentContactLimit
import TakhtajanTeo.Ch1.ComponentBlowupDisplacement
import TakhtajanTeo.Ch1.ComponentBlowupAmplitude
import TakhtajanTeo.Ch1.HilbertChosenReflection
import TakhtajanTeo.Ch1.ComponentTBasics
import LiZhongQC.Ch11.S35_DiscTeichmullerMaps

/-!
# `componentT_spec` for every base point (`qd_`, 下属3, Program G, wall W-QDISK)

The Bers image of the component `T_p(1)` is the whole affine slice `(β(p) + A₂(𝔻)) ∩ β(T(1))`, for every `p`
(the memoir asserts it at TT:1896; previously only `⊆` and the base point were installed).

Route.
- Write `p = [μ]` with `μ ∈ 𝒪` (`ctb_exists_groupO_rep`), so `T_p(1) = cst_L2leaf μ` (`csl_L2leaf_eq_component`).
- For `q = [ν]` in the slice, `F = f^ν ∘ (f^μ)⁻¹` is conformal on the quasidisc `Ω = f^μ(𝔻)` with `S_F ∈ A₂(Ω)`.
- Near `∂Ω`, Ahlfors' reflection formula `N = (A + (u - h u) A')/(B + (u - h u) B')` uses the chosen `C¹` reflection
  `h` (`hc6_chosen_reflection`) and an ODE pair `A, B` of `F` (`cnf_pair`).
- `qd_blowup` and `qd_contact` show that `N` is, at the hyperbolic scale near `∂Ω`, `C¹`-close to the osculating
  Möbius map and `C⁰`-close to `F ∘ h`. This makes `N` injective on a thin collar and maps it into `Ω_ν*`
  (`qd_collar`).
- Glued with `F` on `Ω̄` and filled on the core (`annulus_extension_extends`), this gives a global q.c. extension
  whose pulled-back dilatation is `L²` (`qd_extension`, via `crn_schwarzian_collar_finite` and
  `cce_finite_of_collar`).
- `crc_relative_coefficient_of_qc` and right translation by `μ` (`cst_coeff_right_finite`) then put `q` in
  `cst_L2leaf μ`.

All `L²` norms here are the installed `normL2` (lintegral form).
-/

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal Classical Real ComplexConjugate
noncomputable section
namespace TakhtajanTeo
open LiZhongQC

/-- Exact derivative of the Ahlfors quotient map: `dN = -(1/b²)(1 + t² s Dg)` (`s = S/2`, Wronskian `1`). -/
theorem qd_N_hasFDerivAt {A B g : ℂ → ℂ} {y s : ℂ} (hg : DifferentiableAt ℝ g y)
    (hA : HasDerivAt A (deriv A (g y)) (g y)) (hA' : HasDerivAt (deriv A) (-(s * A (g y))) (g y))
    (hB : HasDerivAt B (deriv B (g y)) (g y)) (hB' : HasDerivAt (deriv B) (-(s * B (g y))) (g y))
    (hW : A (g y) * deriv B (g y) - B (g y) * deriv A (g y) = 1)
    (hD : B (g y) + (y - g y) * deriv B (g y) ≠ 0) :
    HasFDerivAt (cnf_finite A B g)
      ((-(1 / (B (g y) + (y - g y) * deriv B (g y)) ^ 2)) •
        ((1 : ℂ →L[ℝ] ℂ) + ((y - g y) ^ 2 * s) • fderiv ℝ g y)) y := by
  have hGa := t203_hasFDerivAt_G hg hA hA'
  have hGb := t203_hasFDerivAt_G hg hB hB'
  have hI := (hasDerivAt_inv hD).comp_hasFDerivAt y hGb
  have hP := hGa.mul hI
  have he : cnf_finite A B g = (fun w => A (g w) + (w - g w) * deriv A (g w)) *
      ((fun z : ℂ => z⁻¹) ∘ fun w => B (g w) + (w - g w) * deriv B (g w)) := by
    funext w
    simp only [cnf_finite, Pi.mul_apply, Function.comp, div_eq_mul_inv]
  rw [he]
  convert hP using 1
  ext z
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.one_apply, ContinuousLinearMap.coe_id', id, smul_eq_mul, Function.comp]
  field_simp
  linear_combination ((z + (y - g y) ^ 2 * s * (fderiv ℝ g y) z)) * hW

/-- Along every sequence of blow-up centres tending to the circle, a subsequence has bounded normalized first
derivative at `0` (normal-family limit + Cauchy jets). -/
theorem qd_nderiv_subseq {μ : LinfStar} (hμ : μ ∈ LinfStarBall) (e : ℂ ≃ₜ ℂ) {K : ℝ}
    (he : IsKQC e univ K) (hef : EqOn e (fsans μ) unitDisc) {a : ℕ → ℂ}
    (ha : ∀ n, 0 < ‖a n‖ ∧ ‖a n‖ < 1) (hlim : Tendsto (fun n => ‖a n‖) atTop (𝓝 1)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ C : ℝ, ∀ᶠ n in atTop,
      ‖deriv (cbl_normalized e (a (φ n))) 0‖ ≤ C := by
  obtain ⟨σ, hσ, f, -, -, -, hFl, -⟩ :=
    crbl_common_subseq (fun n => cbl_normalized_plane e he (ha n).1 (ha n).2)
      (fun n => cbl_normalized_plane e he (ha n).1 (ha n).2)
  have haσ : ∀ n, 0 < ‖a (σ n)‖ ∧ ‖a (σ n)‖ < 1 := fun n => ha (σ n)
  have hlimσ : Tendsto (fun n => ‖a (σ n)‖) atTop (𝓝 1) := hlim.comp hσ.tendsto_atTop
  have hK : closedBall (0 : ℂ) 1 ⊆ {t : ℂ | -2 < t.re} := by
    intro t ht
    have h1 := (abs_re_le_norm t).trans (mem_closedBall_zero_iff.mp ht)
    change -2 < t.re
    linarith [neg_abs_le t.re]
  have hev := cbs_eventually_mapsTo haσ hlimσ (isCompact_closedBall 0 1) hK
  have hlocal : ∀ z ∈ ball (0 : ℂ) 1, ∃ r > 0, ball z r ⊆ ball (0 : ℂ) 1 ∧
      ∀ᶠ n in atTop, DifferentiableOn ℂ (cbl_normalized e (a (σ n))) (ball z r) := by
    intro z hz
    have hz1 : ‖z‖ < 1 := mem_ball_zero_iff.mp hz
    refine ⟨1 - ‖z‖, by linarith, ?_, ?_⟩
    · intro w hw
      rw [mem_ball_zero_iff]
      have := norm_le_norm_add_norm_sub' w z
      rw [mem_ball, dist_eq_norm] at hw
      linarith
    · filter_upwards [hev] with n hn
      refine (cbs_normalized_holomorphic hμ e hef (haσ n).1 (haσ n).2).mono ?_
      intro w hw
      apply hn
      rw [mem_closedBall_zero_iff]
      have := norm_le_norm_add_norm_sub' w z
      rw [mem_ball, dist_eq_norm] at hw
      linarith
  obtain ⟨-, hj⟩ := crbl_local_jets (hFl.tendstoLocallyUniformlyOn.mono (subset_univ _)) hlocal
  have h0 := (hj 0 (mem_ball_self one_pos)).1
  refine ⟨σ, hσ, ‖deriv f 0‖ + 1, ?_⟩
  filter_upwards [h0.norm.eventually (eventually_lt_nhds (lt_add_one _))] with n hn
  exact hn.le

/-- Along the reflection-boundary filter the reflected points stay bounded (`h → p ∈ Ω` at `∞`). -/
theorem qd_bdd_of_boundary {μ : LinfStar} (hμ : μ ∈ LinfStarBall) {h : ℂ → ℂ} {p : ℂ}
    (hp : p ∈ fsans μ '' unitDisc)
    (hinf : Tendsto h (cocompact ℂ ⊓ 𝓟 (gsans μ '' unitDiscExterior)) (𝓝 p))
    {u : ℕ → ℂ} (hu : Tendsto u atTop (crb_reflectionBoundary μ h)) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ᶠ n in atTop, ‖u n‖ ≤ R := by
  obtain ⟨c, hc, rfl⟩ := hp
  have hc1 : ‖c‖ < 1 := mem_ball_zero_iff.mp hc
  set ρ : ℝ := (1 + ‖c‖) / 2 with hρ
  have hf := S2C.s2c_conf_f hμ
  have hsub : ball (0 : ℂ) ρ ⊆ unitDisc := ball_subset_ball (by rw [hρ]; linarith)
  have hVo : IsOpen (fsans μ '' ball (0 : ℂ) ρ) :=
    (show IsConformalOnto (fsans μ) (ball (0 : ℂ) ρ) (fsans μ '' ball (0 : ℂ) ρ) from
      ⟨hf.1.mono hsub, hf.2.1.mono hsub, rfl⟩).isOpen isOpen_ball
  have hcV : fsans μ c ∈ fsans μ '' ball (0 : ℂ) ρ :=
    ⟨c, mem_ball_zero_iff.mpr (by rw [hρ]; linarith), rfl⟩
  have hev := hinf (hVo.mem_nhds hcV)
  rw [Filter.mem_map, mem_inf_principal] at hev
  obtain ⟨K, hK, hKs⟩ := (Filter.hasBasis_cocompact).mem_iff.mp hev
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall 0
  refine ⟨max R 0, le_max_right _ _, ?_⟩
  have h1 : Tendsto (fun n => ‖Function.invFunOn (fsans μ) unitDisc (h (u n))‖) atTop (𝓝 1) := by
    have h2 := tendsto_comap_iff.mp (hu.mono_right inf_le_left)
    exact tendsto_comap_iff.mp (h2.mono_right inf_le_left)
  have hE : ∀ᶠ n in atTop, u n ∈ gsans μ '' unitDiscExterior :=
    tendsto_principal.mp (hu.mono_right inf_le_right)
  filter_upwards [hE, h1.eventually (lt_mem_nhds (show ρ < 1 by rw [hρ]; linarith))] with n hn hn1
  by_contra hcon
  have hnK : u n ∉ K := fun hk => hcon ((mem_closedBall_zero_iff.mp (hR hk)).trans (le_max_left _ _))
  obtain ⟨w, hw, hwe⟩ := hKs hnK hn
  have hwD : w ∈ unitDisc := hsub hw
  have hinv : Function.invFunOn (fsans μ) unitDisc (h (u n)) = w := by
    rw [← hwe]
    exact hf.2.1 (Function.invFunOn_mem ⟨w, hwD, rfl⟩) hwD (Function.invFunOn_eq ⟨w, hwD, rfl⟩)
  rw [hinv] at hn1
  linarith [mem_ball_zero_iff.mp hw]

/-- **(L-pre)** The relative pre-Schwarzian at the reflection scale vanishes at the boundary:
`(u - h u) F''(h u)/F'(h u) → 0` along every sequence tending to the reflection-boundary filter
(`= x_n q_n/p_n` in the synchronized blow-up frames; `q_n → 0`, `p_n → 1`, `x_n` bounded on subsequences). -/
theorem qd_prerel_seq {μ ν : LinfStar} (hμ : μ ∈ LinfStarBall) (hν : ν ∈ LinfStarBall)
    (hP : AInf.toFun (bersPhi ν - bersPhi μ) ∈ A2fun unitDisc)
    {h : ℂ → ℂ} {p : ℂ} (hp : p ∈ fsans μ '' unitDisc)
    (hh : IsQCReflection (fsans μ '' unitDisc) (gsans μ '' unitDiscExterior) h)
    (hinf : Tendsto h (cocompact ℂ ⊓ 𝓟 (gsans μ '' unitDiscExterior)) (𝓝 p))
    {u : ℕ → ℂ} (hu : Tendsto u atTop (crb_reflectionBoundary μ h)) :
    Tendsto (fun n => (u n - h (u n)) * deriv (deriv (crs_transition μ ν)) (h (u n)) /
      deriv (crs_transition μ ν) (h (u n))) atTop (𝓝 0) := by
  obtain ⟨eμ, Kμ, hKμ, heμ⟩ := cra_welding_extension hμ
  obtain ⟨eν, Kν, hKν, heν⟩ := cra_welding_extension hν
  set a : ℕ → ℂ := fun n => Function.invFunOn (fsans μ) unitDisc (h (u n)) with ha_def
  have hE : ∀ᶠ n in atTop, u n ∈ gsans μ '' unitDiscExterior :=
    tendsto_principal.mp (hu.mono_right inf_le_right)
  have hA : Tendsto (fun n => ‖a n‖) atTop (𝓝 1) := by
    have h2 := tendsto_comap_iff.mp (hu.mono_right inf_le_left)
    exact tendsto_comap_iff.mp (h2.mono_right inf_le_left)
  have hmem : ∀ n, u n ∈ gsans μ '' unitDiscExterior → a n ∈ unitDisc ∧ fsans μ (a n) = h (u n) :=
    fun n hn => ⟨Function.invFunOn_mem (hh.2.1 hn), Function.invFunOn_eq (hh.2.1 hn)⟩
  set a' : ℕ → ℂ := fun n => if 0 < ‖a n‖ ∧ ‖a n‖ < 1 then a n else (1 / 2 : ℂ) with ha'_def
  have ha' : ∀ n, 0 < ‖a' n‖ ∧ ‖a' n‖ < 1 := by
    intro n
    simp only [ha'_def]
    split_ifs with hc
    · exact hc
    · norm_num
  have hpos : ∀ᶠ n in atTop, 0 < ‖a n‖ := hA.eventually (lt_mem_nhds one_pos)
  have heq : ∀ᶠ n in atTop, a' n = a n ∧ u n ∈ gsans μ '' unitDiscExterior := by
    filter_upwards [hE, hpos] with n hn hn0
    have h1 : ‖a n‖ < 1 := mem_ball_zero_iff.mp (hmem n hn).1
    exact ⟨by simp only [ha'_def, if_pos (And.intro hn0 h1)], hn⟩
  have hA' : Tendsto (fun n => ‖a' n‖) atTop (𝓝 1) :=
    hA.congr' (heq.mono fun n hn => by show ‖a n‖ = ‖a' n‖; rw [hn.1])
  obtain ⟨hp1, hq0⟩ := crbl_actual_relative_jets hμ hν hP eμ eν hKμ hKν heμ heν ha' hA'
  obtain ⟨R, hR0, hRu⟩ := qd_bdd_of_boundary hμ hp hinf hu
  obtain ⟨D, hD, hcbd⟩ := cbd_normalized_displacement hμ hh R hR0
  have hqp : Tendsto (fun n => crbl_relative_second (cbl_normalized eμ (a' n)) (cbl_normalized eν (a' n)) /
      crbl_relative_first (cbl_normalized eμ (a' n)) (cbl_normalized eν (a' n))) atTop (𝓝 0) := by
    have h3 := hq0.div hp1 one_ne_zero
    rw [zero_div] at h3
    exact h3
  apply Filter.tendsto_of_subseq_tendsto
  intro ns hns
  obtain ⟨φ, hφ, C, hC⟩ := qd_nderiv_subseq hμ eμ hKμ heμ (a := fun n => a' (ns n)) (fun n => ha' _)
    (hA'.comp hns)
  refine ⟨φ, ?_⟩
  have hι : Tendsto (fun n => ns (φ n)) atTop atTop := hns.comp hφ.tendsto_atTop
  have hqpι := hqp.comp hι
  apply squeeze_zero_norm' (a := fun n => 2 * D * C *
    ‖crbl_relative_second (cbl_normalized eμ (a' (ns (φ n)))) (cbl_normalized eν (a' (ns (φ n)))) /
      crbl_relative_first (cbl_normalized eμ (a' (ns (φ n)))) (cbl_normalized eν (a' (ns (φ n))))‖)
  · filter_upwards [hι.eventually heq, hι.eventually hRu, hC] with n hn hnR hnC
    set m := ns (φ n)
    obtain ⟨hmD, hmf⟩ := hmem m hn.2
    have hfa : fsans μ (a' m) = h (u m) := by rw [hn.1]; exact hmf
    obtain ⟨hbμ, hbν, hf0, hg0, hF1, hF2⟩ :=
      ccn_transition_jets hμ hν eμ eν heμ heν (ha' m).1 (ha' m).2
    obtain ⟨-, -, hfj, -⟩ := ccn_normalized_jets hμ eμ heμ (ha' m).1 (ha' m).2
    have hx := hcbd (u m) hn.2 hnR (a' m) (ha' m).1 (ha' m).2 hfa (eμ (cbl_source (a' m) 1) - eμ (a' m))
    rw [hfa] at hF1 hF2
    rw [hF1, hF2]
    rw [← hfj] at hx
    calc ‖(u m - h (u m)) * ((eν (cbl_source (a' m) 1) - eν (a' m)) /
            (eμ (cbl_source (a' m) 1) - eμ (a' m)) ^ 2 *
          ((deriv (deriv (cbl_normalized eν (a' m))) 0 * deriv (cbl_normalized eμ (a' m)) 0 -
            deriv (cbl_normalized eν (a' m)) 0 * deriv (deriv (cbl_normalized eμ (a' m))) 0) /
            deriv (cbl_normalized eμ (a' m)) 0 ^ 3)) /
          ((eν (cbl_source (a' m) 1) - eν (a' m)) / (eμ (cbl_source (a' m) 1) - eμ (a' m)) *
            (deriv (cbl_normalized eν (a' m)) 0 / deriv (cbl_normalized eμ (a' m)) 0))‖
        = ‖(u m - h (u m)) / (eμ (cbl_source (a' m) 1) - eμ (a' m))‖ *
          ‖crbl_relative_second (cbl_normalized eμ (a' m)) (cbl_normalized eν (a' m)) /
            crbl_relative_first (cbl_normalized eμ (a' m)) (cbl_normalized eν (a' m))‖ := by
          rw [← norm_mul]
          congr 1
          simp only [crbl_relative_first, crbl_relative_second]
          field_simp
      _ ≤ 2 * D * C * ‖crbl_relative_second (cbl_normalized eμ (a' m)) (cbl_normalized eν (a' m)) /
            crbl_relative_first (cbl_normalized eμ (a' m)) (cbl_normalized eν (a' m))‖ := by
          apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
          exact hx.trans (mul_le_mul_of_nonneg_left hnC (by positivity))
  · have h4 := hqpι.norm.const_mul (2 * D * C)
    rw [norm_zero, mul_zero] at h4
    exact h4

/-- `Ω` and `Ω* = 𝗀_μ(𝔻*)` are disjoint, and `(Ω*)ᶜ ⊆ closure Ω`. -/
theorem qd_sides {μ : LinfStar} (hμ : μ ∈ LinfStarBall) :
    Disjoint (fsans μ '' unitDisc) (gsans μ '' unitDiscExterior) ∧
      (gsans μ '' unitDiscExterior)ᶜ ⊆ closure (fsans μ '' unitDisc) := by
  have hd := (l29b_open_disjoint hμ).2.2
  have hi := l29b_interior_compl hμ
  rw [← S2C.s2c_fsans_eq hμ] at hd hi
  refine ⟨hd, fun z hz => ?_⟩
  by_contra hc
  have : z ∈ interior ((fsans μ '' unitDisc)ᶜ) := by
    rw [interior_compl]; exact hc
  exact hz (hi this)

/-- Scale-invariant control of the chosen reflection: `|u - h u| λ_Ω(h u) ≥ 1/2` and `‖Dh u‖ ≤ 4 C₀`. -/
theorem qd_dh_bound {μ : LinfStar} (hμ : μ ∈ LinfStarBall) {h : ℂ → ℂ} {C₀ : ℝ}
    (hh : IsQCReflection (fsans μ '' unitDisc) (gsans μ '' unitDiscExterior) h)
    (hb1 : ∀ u ∈ gsans μ '' unitDiscExterior, ‖u - h u‖ ^ 2 * ‖fderiv ℝ h u‖ *
      poincareDensity (fsans μ '' unitDisc) (h u) ^ 2 ≤ C₀)
    {u : ℂ} (hu : u ∈ gsans μ '' unitDiscExterior) :
    (1 / 2 : ℝ) ≤ ‖u - h u‖ * poincareDensity (fsans μ '' unitDisc) (h u) ∧
      ‖fderiv ℝ h u‖ ≤ 4 * C₀ := by
  have hf := S2C.s2c_conf_f hμ
  have hΩ : IsOpen (fsans μ '' unitDisc) := hf.isOpen isOpen_ball
  have hφ := hf.symm isOpen_ball
  have hv : h u ∈ fsans μ '' unitDisc := hh.2.1 hu
  have huΩ : u ∈ (fsans μ '' unitDisc)ᶜ := fun h' => (qd_sides hμ).1.le_bot ⟨h', hu⟩
  have hlow := eq22_density_distance_lower hΩ hφ ⟨u, huΩ⟩ hv
  have hdist : Metric.infDist (h u) (fsans μ '' unitDisc)ᶜ ≤ ‖u - h u‖ := by
    rw [norm_sub_rev, ← dist_eq_norm]
    exact Metric.infDist_le_dist_of_mem huΩ
  have hlam : 0 ≤ poincareDensity (fsans μ '' unitDisc) (h u) := by
    by_contra hneg
    push_neg at hneg
    nlinarith [Metric.infDist_nonneg (x := h u) (s := (fsans μ '' unitDisc)ᶜ)]
  have h1 : (1 / 2 : ℝ) ≤ ‖u - h u‖ * poincareDensity (fsans μ '' unitDisc) (h u) := by
    nlinarith [mul_le_mul_of_nonneg_left hdist hlam]
  refine ⟨h1, ?_⟩
  have hb := hb1 u hu
  have hsq : (1 / 4 : ℝ) ≤ ‖u - h u‖ ^ 2 * poincareDensity (fsans μ '' unitDisc) (h u) ^ 2 := by
    have := mul_le_mul h1 h1 (by norm_num) (le_trans (by norm_num) h1)
    nlinarith
  have hD := norm_nonneg (fderiv ℝ h u)
  nlinarith [mul_le_mul_of_nonneg_left hsq hD]

/-- Mean-value bound for the chosen reflection on a convex subset of `Ω*`. -/
theorem qd_h_lip {μ : LinfStar} (hμ : μ ∈ LinfStarBall) {h : ℂ → ℂ} {C₀ : ℝ}
    (hC1 : ContDiffOn ℝ 1 h (gsans μ '' unitDiscExterior))
    (hh : IsQCReflection (fsans μ '' unitDisc) (gsans μ '' unitDiscExterior) h)
    (hb1 : ∀ u ∈ gsans μ '' unitDiscExterior, ‖u - h u‖ ^ 2 * ‖fderiv ℝ h u‖ *
      poincareDensity (fsans μ '' unitDisc) (h u) ^ 2 ≤ C₀)
    {s : Set ℂ} (hs : Convex ℝ s) (hsE : s ⊆ gsans μ '' unitDiscExterior) {x y : ℂ} (hx : x ∈ s)
    (hy : y ∈ s) : ‖h y - h x‖ ≤ 4 * C₀ * ‖y - x‖ := by
  have hEo : IsOpen (gsans μ '' unitDiscExterior) := (l29b_open_disjoint hμ).2.1
  refine Convex.norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℝ) (fun z hz => ?_) (fun z hz => ?_) hs hx hy
  · exact (hC1.differentiableOn one_ne_zero z (hsE hz)).differentiableAt (hEo.mem_nhds (hsE hz))
  · exact (qd_dh_bound hμ hh hb1 (hsE hz)).2

/-- **(G1)** The ball `B̄(u, |u - h u|/(2(1 + 4C₀)))` lies in `Ω*`, and the reflection scale is comparable on it. -/
theorem qd_ball {μ : LinfStar} (hμ : μ ∈ LinfStarBall) {h : ℂ → ℂ} {C₀ : ℝ}
    (hC1 : ContDiffOn ℝ 1 h (gsans μ '' unitDiscExterior))
    (hh : IsQCReflection (fsans μ '' unitDisc) (gsans μ '' unitDiscExterior) h)
    (hb1 : ∀ u ∈ gsans μ '' unitDiscExterior, ‖u - h u‖ ^ 2 * ‖fderiv ℝ h u‖ *
      poincareDensity (fsans μ '' unitDisc) (h u) ^ 2 ≤ C₀) (hC₀ : 0 ≤ C₀)
    {u : ℂ} (hu : u ∈ gsans μ '' unitDiscExterior) :
    closedBall u (‖u - h u‖ / (2 * (1 + 4 * C₀))) ⊆ gsans μ '' unitDiscExterior ∧
      ∀ y ∈ closedBall u (‖u - h u‖ / (2 * (1 + 4 * C₀))),
        ‖u - h u‖ ≤ 2 * ‖y - h y‖ ∧ ‖y - h y‖ ≤ 2 * ‖u - h u‖ := by
  set E := gsans μ '' unitDiscExterior with hEdef
  set Ω := fsans μ '' unitDisc with hΩdef
  have hEo : IsOpen E := (l29b_open_disjoint hμ).2.1
  have hΩo : IsOpen Ω := (S2C.s2c_conf_f hμ).isOpen isOpen_ball
  obtain ⟨hdisj, hcl⟩ := qd_sides hμ
  have hk : 0 < 2 * (1 + 4 * C₀) := by positivity
  set ρ := ‖u - h u‖ / (2 * (1 + 4 * C₀)) with hρ
  have hut : ‖u - h u‖ ≠ 0 := by
    intro h0
    have he : u = h u := sub_eq_zero.mp (norm_eq_zero.mp h0)
    exact hdisj.le_bot ⟨he ▸ hh.2.1 hu, hu⟩
  have hρt : (1 + 4 * C₀) * ρ = ‖u - h u‖ / 2 := by rw [hρ]; field_simp
  have hsub : closedBall u ρ ⊆ E := by
    intro y hy
    by_contra hyE
    set S := segment ℝ u y ∩ Eᶜ with hS
    have hSc : IsCompact S := by
      have hseg : IsCompact (segment ℝ u y) := by
        rw [segment_eq_image']
        exact isCompact_Icc.image (by fun_prop)
      exact hseg.inter_right hEo.isClosed_compl
    have hSne : S.Nonempty := ⟨y, right_mem_segment ℝ u y, hyE⟩
    obtain ⟨w, ⟨hwseg, hwE⟩, hwmin⟩ := hSc.exists_isMinOn (f := fun z : ℂ => ‖z - u‖) hSne
      (Continuous.continuousOn (by fun_prop))
    have hwu : w ≠ u := fun h' => hwE (h' ▸ hu)
    have hwr : ‖w - u‖ ≤ ρ := by
      obtain ⟨a, b, ha, hb, hab, rfl⟩ := hwseg
      have hy' : ‖y - u‖ ≤ ρ := by rw [← dist_eq_norm]; exact hy
      have : a • u + b • y - u = b • (y - u) := by
        rw [show a = 1 - b by linarith]; simp only [sub_smul, one_smul, smul_sub]; abel
      rw [this, norm_smul, Real.norm_of_nonneg hb]
      nlinarith [norm_nonneg (y - u)]
    have hin : ∀ s : ℝ, 0 ≤ s → s < 1 → u + s • (w - u) ∈ E := by
      intro s hs0 hs1
      by_contra hc
      have hseg : u + s • (w - u) ∈ segment ℝ u y := by
        have h1 : u + s • (w - u) ∈ segment ℝ u w := by
          refine ⟨1 - s, s, by linarith, hs0, by ring, ?_⟩
          simp only [sub_smul, one_smul, smul_sub]; abel
        exact (convex_segment u y).segment_subset (left_mem_segment ℝ u y) hwseg h1
      have hm : ‖w - u‖ ≤ ‖u + s • (w - u) - u‖ := hwmin ⟨hseg, hc⟩
      rw [add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hs0] at hm
      have hpos : 0 < ‖w - u‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hwu)
      nlinarith
    have hlim : Tendsto (fun s : ℝ => u + s • (w - u)) (𝓝[<] 1) (𝓝[E] w) := by
      apply tendsto_nhdsWithin_iff.mpr
      constructor
      · have hc : Continuous (fun s : ℝ => u + s • (w - u)) := by fun_prop
        have := hc.tendsto 1
        simp only [one_smul, add_sub_cancel] at this
        exact this.mono_left nhdsWithin_le_nhds
      · filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with s hs
        exact hin s hs.1.le hs.2
    have hwcE : w ∈ closure E := mem_closure_of_tendsto (hlim.mono_right nhdsWithin_le_nhds)
      (by filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with s hs
          exact hin s hs.1.le hs.2)
    have hwΩ : w ∉ Ω := fun hw => by
      have := mem_closure_iff.mp hwcE Ω hΩo hw
      obtain ⟨z, hzΩ, hzE⟩ := this
      exact hdisj.le_bot ⟨hzΩ, hzE⟩
    have hwfr : w ∈ frontier Ω := ⟨hcl hwE, by rw [hΩo.interior_eq]; exact hwΩ⟩
    have hht := (hh.2.2 w hwfr).comp hlim
    have hbd : ∀ᶠ s in 𝓝[<] (1 : ℝ), ‖h (u + s • (w - u)) - h u‖ ≤ 4 * C₀ * ‖w - u‖ := by
      filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with s hs
      have hconv : segment ℝ u (u + s • (w - u)) ⊆ E := by
        rintro z ⟨a, b, ha, hb, hab, rfl⟩
        have : a • u + b • (u + s • (w - u)) = u + (b * s) • (w - u) := by
          rw [show a = 1 - b by linarith]; simp only [sub_smul, one_smul, smul_add, mul_smul]; abel
        rw [this]
        exact hin _ (mul_nonneg hb hs.1.le)
          (by nlinarith [hs.2, mul_le_mul_of_nonneg_right (show b ≤ 1 by linarith) hs.1.le])
      have := qd_h_lip hμ hC1 hh hb1 (convex_segment _ _) hconv (left_mem_segment ℝ _ _)
        (right_mem_segment ℝ _ _)
      rw [add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hs.1.le] at this
      refine this.trans ?_
      have : s * ‖w - u‖ ≤ ‖w - u‖ := mul_le_of_le_one_left (norm_nonneg _) hs.2.le
      exact mul_le_mul_of_nonneg_left this (by positivity)
    have hl2 : ‖w - h u‖ ≤ 4 * C₀ * ‖w - u‖ :=
      le_of_tendsto ((hht.sub_const (h u)).norm) hbd
    have htri : ‖u - h u‖ ≤ ‖u - w‖ + ‖w - h u‖ := by
      calc ‖u - h u‖ = ‖(u - w) + (w - h u)‖ := by ring_nf
        _ ≤ _ := norm_add_le _ _
    rw [norm_sub_rev u w] at htri
    have : ‖u - h u‖ ≤ ‖u - h u‖ / 2 := by nlinarith
    have hpos : 0 < ‖u - h u‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hut)
    linarith
  refine ⟨hsub, fun y hy => ?_⟩
  have hl := qd_h_lip hμ hC1 hh hb1 (convex_closedBall u ρ) hsub hy (mem_closedBall_self
    (by positivity))
  rw [norm_sub_rev (h u), norm_sub_rev u] at hl
  have hyu : ‖y - u‖ ≤ ρ := by rw [← dist_eq_norm]; exact hy
  have hdiff : ‖(y - h y) - (u - h u)‖ ≤ ‖u - h u‖ / 2 := by
    calc ‖(y - h y) - (u - h u)‖ = ‖(y - u) - (h y - h u)‖ := by ring_nf
      _ ≤ ‖y - u‖ + ‖h y - h u‖ := norm_sub_le _ _
      _ ≤ (1 + 4 * C₀) * ρ := by
        nlinarith [mul_le_mul_of_nonneg_left hyu (show 0 ≤ 4 * C₀ by positivity)]
      _ = _ := hρt
  have h1 := norm_sub_norm_le (u - h u) (y - h y)
  have h2 := norm_sub_norm_le (y - h y) (u - h u)
  rw [norm_sub_rev (u - h u)] at h1
  constructor <;> linarith

/-- `‖a - a/|a|‖ = 1 - |a|` for `0 < |a| ≤ 1`. -/
theorem qd_radial_dist {a : ℂ} (ha0 : 0 < ‖a‖) (ha1 : ‖a‖ ≤ 1) :
    ‖a - a / (‖a‖ : ℂ)‖ = 1 - ‖a‖ ∧ ‖a / (‖a‖ : ℂ)‖ = 1 := by
  have hne : (‖a‖ : ℂ) ≠ 0 := by exact_mod_cast ha0.ne'
  constructor
  · have e : a - a / (‖a‖ : ℂ) = ((1 - 1 / ‖a‖ : ℝ) : ℂ) * a := by
      push_cast; field_simp
    rw [e, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have hle : 1 - 1 / ‖a‖ ≤ 0 := by
      rw [sub_nonpos, le_div_iff₀ ha0]; linarith
    rw [abs_of_nonpos hle]
    field_simp
    ring
  · rw [norm_div, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _), div_self ha0.ne']

/-- Along the reflection-boundary filter the reflection displacement tends to `0`. -/
theorem qd_t_tendsto {μ : LinfStar} (hμ : μ ∈ LinfStarBall) {h : ℂ → ℂ} {p : ℂ}
    (hp : p ∈ fsans μ '' unitDisc)
    (hh : IsQCReflection (fsans μ '' unitDisc) (gsans μ '' unitDiscExterior) h)
    (hinf : Tendsto h (cocompact ℂ ⊓ 𝓟 (gsans μ '' unitDiscExterior)) (𝓝 p))
    {u : ℕ → ℂ} (hu : Tendsto u atTop (crb_reflectionBoundary μ h)) :
    Tendsto (fun n => ‖u n - h (u n)‖) atTop (𝓝 0) := by
  obtain ⟨R, hR0, hRu⟩ := qd_bdd_of_boundary hμ hp hinf hu
  obtain ⟨D, hD, hdisp⟩ := eq22_reflection_bounded_displacement hμ hh R hR0
  obtain ⟨e, K, -, he⟩ := cra_welding_extension hμ
  set a : ℕ → ℂ := fun n => Function.invFunOn (fsans μ) unitDisc (h (u n)) with ha_def
  have hE : ∀ᶠ n in atTop, u n ∈ gsans μ '' unitDiscExterior :=
    tendsto_principal.mp (hu.mono_right inf_le_right)
  have hA : Tendsto (fun n => ‖a n‖) atTop (𝓝 1) := by
    have h2 := tendsto_comap_iff.mp (hu.mono_right inf_le_left)
    exact tendsto_comap_iff.mp (h2.mono_right inf_le_left)
  have hUC := Metric.uniformContinuousOn_iff.mp
    ((isCompact_closedBall (0 : ℂ) 1).uniformContinuousOn_of_continuous e.continuous.continuousOn)
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨δ, hδ, hδε⟩ := hUC (ε / (2 * D + 1)) (by positivity)
  filter_upwards [hE, hRu, hA.eventually (lt_mem_nhds (show (0 : ℝ) < 1 by norm_num)),
    hA.eventually (Metric.ball_mem_nhds 1 hδ)] with n hn hnR hn0 hnδ
  have haD : a n ∈ unitDisc := Function.invFunOn_mem (hh.2.1 hn)
  have hfa : fsans μ (a n) = h (u n) := Function.invFunOn_eq (hh.2.1 hn)
  have ha1 : ‖a n‖ < 1 := mem_ball_zero_iff.mp haD
  obtain ⟨hrd, hr1⟩ := qd_radial_dist hn0 ha1.le
  have hζ : e (a n / (‖a n‖ : ℂ)) ∈ (fsans μ '' unitDisc)ᶜ := by
    rintro ⟨w, hw, hwe⟩
    rw [← he hw] at hwe
    have := e.injective hwe
    rw [this] at hw
    have := mem_ball_zero_iff.mp hw
    linarith
  have hdd : dist (a n) (a n / (‖a n‖ : ℂ)) < δ := by
    rw [dist_eq_norm, hrd]
    have := hnδ
    rw [Real.dist_eq, abs_sub_lt_iff] at this
    linarith [this.2]
  have hcl := hδε (a n) (mem_closedBall_zero_iff.mpr ha1.le) (a n / (‖a n‖ : ℂ))
    (mem_closedBall_zero_iff.mpr hr1.le) hdd
  rw [he haD, hfa] at hcl
  have hinfd : Metric.infDist (h (u n)) (fsans μ '' unitDisc)ᶜ < ε / (2 * D + 1) :=
    (Metric.infDist_le_dist_of_mem hζ).trans_lt hcl
  have hb := (hdisp (u n) hn hnR).2
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _)]
  have hk : 2 * D * (ε / (2 * D + 1)) < ε := by
    rw [mul_div_assoc', div_lt_iff₀ (by positivity)]; nlinarith
  nlinarith [Metric.infDist_nonneg (x := h (u n)) (s := (fsans μ '' unitDisc)ᶜ)]

/-- The relative map through its ODE pair: `F = A/B`, `F' = -1/B²`, `F'' = 2B'/B³` on `Ω`. -/
theorem qd_FB {μ ν : LinfStar} (hμ : μ ∈ LinfStarBall) {A B : ℂ → ℂ}
    (hA : DifferentiableOn ℂ A (fsans μ '' unitDisc)) (hB : DifferentiableOn ℂ B (fsans μ '' unitDisc))
    (hode : ∀ z ∈ fsans μ '' unitDisc,
      deriv (deriv A) z + schwarzianHol (crs_transition μ ν) z / 2 * A z = 0 ∧
      deriv (deriv B) z + schwarzianHol (crs_transition μ ν) z / 2 * B z = 0 ∧
      A z * deriv B z - B z * deriv A z = 1)
    (hrat : ∀ z ∈ fsans μ '' unitDisc, (crs_transition μ ν z : ExtPlane) = t203_ratio (A z) (B z))
    {v : ℂ} (hv : v ∈ fsans μ '' unitDisc) :
    B v ≠ 0 ∧ crs_transition μ ν v = A v / B v ∧ deriv (crs_transition μ ν) v = -1 / B v ^ 2 ∧
      deriv (deriv (crs_transition μ ν)) v = 2 * deriv B v / B v ^ 3 := by
  have hΩ : IsOpen (fsans μ '' unitDisc) := (S2C.s2c_conf_f hμ).isOpen isOpen_ball
  have hBne : ∀ z ∈ fsans μ '' unitDisc, B z ≠ 0 := by
    intro z hz h0
    have := hrat z hz
    rw [t203_ratio, if_pos h0] at this
    exact OnePoint.coe_ne_infty _ this
  have hFq : ∀ z ∈ fsans μ '' unitDisc, crs_transition μ ν z = A z / B z := by
    intro z hz
    have := hrat z hz
    rw [t203_ratio, if_neg (hBne z hz)] at this
    exact OnePoint.coe_injective this
  have hd1 : ∀ z ∈ fsans μ '' unitDisc, deriv (crs_transition μ ν) z = -1 / B z ^ 2 := by
    intro z hz
    have hAd := (hA.differentiableAt (hΩ.mem_nhds hz)).hasDerivAt
    have hBd := (hB.differentiableAt (hΩ.mem_nhds hz)).hasDerivAt
    have hq := hAd.div hBd (hBne z hz)
    have he : crs_transition μ ν =ᶠ[𝓝 z] fun w => A w / B w :=
      Filter.eventuallyEq_of_mem (hΩ.mem_nhds hz) hFq
    rw [he.deriv_eq, show (fun w => A w / B w) = A / B from rfl, hq.deriv]
    have hW := (hode z hz).2.2
    have hb := hBne z hz
    field_simp
    linear_combination (-1 : ℂ) * hW
  refine ⟨hBne v hv, hFq v hv, hd1 v hv, ?_⟩
  have he : deriv (crs_transition μ ν) =ᶠ[𝓝 v] fun w => -1 / B w ^ 2 :=
    Filter.eventuallyEq_of_mem (hΩ.mem_nhds hv) hd1
  have hBd := (hB.differentiableAt (hΩ.mem_nhds hv)).hasDerivAt
  have hb := hBne v hv
  have h2 := (hasDerivAt_const v (-1 : ℂ)).div (hBd.pow 2) (pow_ne_zero 2 hb)
  rw [he.deriv_eq, show (fun w => -1 / B w ^ 2) = (fun _ => (-1 : ℂ)) / B ^ 2 from rfl, h2.deriv]
  simp only [Pi.pow_apply]
  field_simp
  ring

/-- **(G2)** Points of the reflection-scale balls around a sequence tending to the reflection-boundary filter
also tend to it. -/
theorem qd_ball_seq {μ : LinfStar} (hμ : μ ∈ LinfStarBall) {h : ℂ → ℂ} {C₀ : ℝ} {p : ℂ}
    (hp : p ∈ fsans μ '' unitDisc) (hC1 : ContDiffOn ℝ 1 h (gsans μ '' unitDiscExterior))
    (hh : IsQCReflection (fsans μ '' unitDisc) (gsans μ '' unitDiscExterior) h)
    (hinf : Tendsto h (cocompact ℂ ⊓ 𝓟 (gsans μ '' unitDiscExterior)) (𝓝 p))
    (hb1 : ∀ u ∈ gsans μ '' unitDiscExterior, ‖u - h u‖ ^ 2 * ‖fderiv ℝ h u‖ *
      poincareDensity (fsans μ '' unitDisc) (h u) ^ 2 ≤ C₀) (hC₀ : 0 ≤ C₀)
    {u y : ℕ → ℂ} (hu : Tendsto u atTop (crb_reflectionBoundary μ h))
    (hy : ∀ᶠ n in atTop, y n ∈ closedBall (u n) (‖u n - h (u n)‖ / (2 * (1 + 4 * C₀)))) :
    Tendsto y atTop (crb_reflectionBoundary μ h) := by
  have hf := S2C.s2c_conf_f hμ
  have hE : ∀ᶠ n in atTop, u n ∈ gsans μ '' unitDiscExterior :=
    tendsto_principal.mp (hu.mono_right inf_le_right)
  have hyE : ∀ᶠ n in atTop, y n ∈ gsans μ '' unitDiscExterior ∧
      ‖y n - h (y n)‖ ≤ 2 * ‖u n - h (u n)‖ := by
    filter_upwards [hE, hy] with n hn hyn
    obtain ⟨h1, h2⟩ := qd_ball hμ hC1 hh hb1 hC₀ hn
    exact ⟨h1 hyn, (h2 _ hyn).2⟩
  have ht := qd_t_tendsto hμ hp hh hinf hu
  set a : ℕ → ℂ := fun n => Function.invFunOn (fsans μ) unitDisc (h (y n)) with ha_def
  have hmem : ∀ᶠ n in atTop, a n ∈ unitDisc ∧ fsans μ (a n) = h (y n) ∧
      y n ∈ gsans μ '' unitDiscExterior ∧ ‖y n - h (y n)‖ ≤ 2 * ‖u n - h (u n)‖ := by
    filter_upwards [hyE] with n hn
    exact ⟨Function.invFunOn_mem (hh.2.1 hn.1), Function.invFunOn_eq (hh.2.1 hn.1), hn⟩
  have hnorm : Tendsto (fun n => ‖a n‖) atTop (𝓝 1) := by
    rw [tendsto_order]
    refine ⟨fun b hb => ?_, fun b hb => ?_⟩
    · set ρ := max b 0 with hρ
      have hρ1 : ρ < 1 := max_lt hb one_pos
      have hρ0 : 0 ≤ ρ := le_max_right _ _
      have hKs : closedBall (0 : ℂ) ρ ⊆ unitDisc := closedBall_subset_ball hρ1
      have hdc : ContinuousOn (fun w => ‖deriv (fsans μ) w‖) (closedBall (0 : ℂ) ρ) :=
        ((hf.1.deriv isOpen_ball).continuousOn.mono hKs).norm
      obtain ⟨x0, hx0, hmin⟩ := (isCompact_closedBall (0 : ℂ) ρ).exists_isMinOn
        ⟨0, mem_closedBall_self hρ0⟩ hdc
      have hm : 0 < ‖deriv (fsans μ) x0‖ :=
        norm_pos_iff.mpr (deriv_ne_zero_of_injOn isOpen_ball hf.1 hf.2.1 (hKs hx0))
      set Λ := 2 / ((1 - ρ ^ 2) * ‖deriv (fsans μ) x0‖) with hΛ
      have hgap : 0 < 1 - ρ ^ 2 := by nlinarith
      have hΛ0 : 0 < Λ := by positivity
      have hev := ht.eventually (gt_mem_nhds (show (0 : ℝ) < 1 / (4 * Λ) by positivity))
      filter_upwards [hmem, hev] with n hn hnt
      obtain ⟨haD, hfa, hyn, hle⟩ := hn
      by_contra hcon
      push_neg at hcon
      have haρ : ‖a n‖ ≤ ρ := hcon.trans (le_max_left _ _)
      have hlow := (qd_dh_bound hμ hh hb1 hyn).1
      have hden := eq22_density_formula hf haD
      rw [hfa] at hden
      have hmn : ‖deriv (fsans μ) x0‖ ≤ ‖deriv (fsans μ) (a n)‖ :=
        hmin (mem_closedBall_zero_iff.mpr haρ)
      have hga : 1 - ρ ^ 2 ≤ 1 - ‖a n‖ ^ 2 := by nlinarith [norm_nonneg (a n)]
      have hle2 : poincareDensity (fsans μ '' unitDisc) (h (y n)) ≤ Λ := by
        rw [hden, hΛ]
        apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
        exact mul_le_mul hga hmn hm.le (by linarith)
      have hty : ‖y n - h (y n)‖ < 1 / (2 * Λ) := by
        have : 2 * ‖u n - h (u n)‖ < 2 * (1 / (4 * Λ)) := by linarith
        calc ‖y n - h (y n)‖ ≤ _ := hle
          _ < _ := this
          _ = 1 / (2 * Λ) := by field_simp; ring
      have : ‖y n - h (y n)‖ * poincareDensity (fsans μ '' unitDisc) (h (y n)) < 1 / 2 := by
        calc _ ≤ ‖y n - h (y n)‖ * Λ := mul_le_mul_of_nonneg_left hle2 (norm_nonneg _)
          _ < 1 / (2 * Λ) * Λ := mul_lt_mul_of_pos_right hty hΛ0
          _ = 1 / 2 := by field_simp
      linarith
    · filter_upwards [hmem] with n hn
      exact (mem_ball_zero_iff.mp hn.1).trans hb
  unfold crb_reflectionBoundary crb_diskBoundary
  refine tendsto_inf.mpr ⟨tendsto_comap_iff.mpr (tendsto_inf.mpr ⟨tendsto_comap_iff.mpr hnorm, ?_⟩),
    tendsto_principal.mpr (hyE.mono fun n hn => hn.1)⟩
  exact tendsto_principal.mpr (hmem.mono fun n hn => hn.1)

/-- **Uniformization over reflection-scale balls.** If `g → 0` along every sequence tending to the
reflection-boundary filter, then along such a sequence `|g| < ε` eventually on the whole ball. -/
theorem qd_unif_seq {μ : LinfStar} (hμ : μ ∈ LinfStarBall) {h : ℂ → ℂ} {C₀ : ℝ} {p : ℂ}
    (hp : p ∈ fsans μ '' unitDisc) (hC1 : ContDiffOn ℝ 1 h (gsans μ '' unitDiscExterior))
    (hh : IsQCReflection (fsans μ '' unitDisc) (gsans μ '' unitDiscExterior) h)
    (hinf : Tendsto h (cocompact ℂ ⊓ 𝓟 (gsans μ '' unitDiscExterior)) (𝓝 p))
    (hb1 : ∀ u ∈ gsans μ '' unitDiscExterior, ‖u - h u‖ ^ 2 * ‖fderiv ℝ h u‖ *
      poincareDensity (fsans μ '' unitDisc) (h u) ^ 2 ≤ C₀) (hC₀ : 0 ≤ C₀)
    {g : ℂ → ℝ} (hg : ∀ w : ℕ → ℂ, Tendsto w atTop (crb_reflectionBoundary μ h) →
      Tendsto (fun n => g (w n)) atTop (𝓝 0))
    {u : ℕ → ℂ} (hu : Tendsto u atTop (crb_reflectionBoundary μ h)) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ y ∈ closedBall (u n) (‖u n - h (u n)‖ / (2 * (1 + 4 * C₀))), |g y| < ε := by
  by_contra hc
  rw [Filter.not_eventually] at hc
  obtain ⟨φ, hφ, hP⟩ := Filter.extraction_of_frequently_atTop hc
  have hP' : ∀ n, ∃ y ∈ closedBall (u (φ n)) (‖u (φ n) - h (u (φ n))‖ / (2 * (1 + 4 * C₀))),
      ε ≤ |g y| := by
    intro n
    have := hP n
    push_neg at this
    exact this
  choose y hyb hyg using hP'
  have huφ : Tendsto (fun n => u (φ n)) atTop (crb_reflectionBoundary μ h) :=
    hu.comp hφ.tendsto_atTop
  have hyt := qd_ball_seq hμ hp hC1 hh hinf hb1 hC₀ huφ (Eventually.of_forall hyb)
  have h0 := hg y hyt
  obtain ⟨n, hn⟩ := (h0.eventually (Metric.ball_mem_nhds 0 hε)).exists
  rw [Real.dist_eq, sub_zero] at hn
  exact absurd (hyg n) (not_le.mpr hn)

/-- **(Gronwall)** On a reflection-scale ball where `|t F''/F'| ≤ η`, the derivative of the relative map at reflected
points varies by a factor `≤ exp((8C₀+1)η) - 1`. -/
theorem qd_Fratio {μ ν : LinfStar} (hμ : μ ∈ LinfStarBall) (hν : ν ∈ LinfStarBall) {h : ℂ → ℂ} {C₀ : ℝ}
    (hC1 : ContDiffOn ℝ 1 h (gsans μ '' unitDiscExterior))
    (hh : IsQCReflection (fsans μ '' unitDisc) (gsans μ '' unitDiscExterior) h)
    (hb1 : ∀ u ∈ gsans μ '' unitDiscExterior, ‖u - h u‖ ^ 2 * ‖fderiv ℝ h u‖ *
      poincareDensity (fsans μ '' unitDisc) (h u) ^ 2 ≤ C₀) (hC₀ : 0 ≤ C₀)
    {u : ℂ} (hu : u ∈ gsans μ '' unitDiscExterior) {η : ℝ} (hη : 0 < η)
    (hsm : ∀ w ∈ closedBall u (‖u - h u‖ / (2 * (1 + 4 * C₀))),
      ‖(w - h w) * deriv (deriv (crs_transition μ ν)) (h w) / deriv (crs_transition μ ν) (h w)‖ ≤ η)
    {y : ℂ} (hy : y ∈ closedBall u (‖u - h u‖ / (2 * (1 + 4 * C₀)))) :
    ‖deriv (crs_transition μ ν) (h y) / deriv (crs_transition μ ν) (h u) - 1‖ ≤
      Real.exp ((8 * C₀ + 1) * η) - 1 := by
  set F := crs_transition μ ν with hFdef
  set ρ := ‖u - h u‖ / (2 * (1 + 4 * C₀)) with hρ
  have hΩ : IsOpen (fsans μ '' unitDisc) := (S2C.s2c_conf_f hμ).isOpen isOpen_ball
  have hEo : IsOpen (gsans μ '' unitDiscExterior) := (l29b_open_disjoint hμ).2.1
  have hFc := crs_conformal hμ hν
  have hF1d : DifferentiableOn ℂ (deriv F) (fsans μ '' unitDisc) := hFc.1.deriv hΩ
  have hFne : ∀ v ∈ fsans μ '' unitDisc, deriv F v ≠ 0 := fun v hv =>
    deriv_ne_zero_of_injOn hΩ hFc.1 hFc.2.1 hv
  obtain ⟨hB, hcomp⟩ := qd_ball hμ hC1 hh hb1 hC₀ hu
  have hk : 0 < 2 * (1 + 4 * C₀) := by positivity
  have hut : 0 < ‖u - h u‖ := by
    rcases (norm_nonneg (u - h u)).lt_or_eq with h1 | h1
    · exact h1
    · exfalso
      have he : u = h u := sub_eq_zero.mp (norm_eq_zero.mp h1.symm)
      exact (qd_sides hμ).1.le_bot ⟨he ▸ hh.2.1 hu, hu⟩
  set γ : ℝ → ℂ := fun s => u + s • (y - u) with hγ
  have hγB : ∀ s ∈ Icc (0 : ℝ) 1, γ s ∈ closedBall u ρ := by
    intro s hs
    rw [mem_closedBall, dist_eq_norm, hγ]
    simp only [add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hs.1]
    have := mem_closedBall.mp hy
    rw [dist_eq_norm] at this
    nlinarith [norm_nonneg (y - u), hs.2]
  set ψ' : ℝ → ℂ := fun s => deriv (deriv F) (h (γ s)) * fderiv ℝ h (γ s) (y - u) with hψ'
  have hder : ∀ s ∈ Icc (0 : ℝ) 1, HasDerivAt (fun s => deriv F (h (γ s))) (ψ' s) s := by
    intro s hs
    have hγs := hB (hγB s hs)
    have hγ' : HasDerivAt γ (y - u) s := by
      have h0 := ((hasDerivAt_id s).smul_const (y - u)).const_add u
      rw [one_smul] at h0
      exact h0
    have hhd : HasFDerivAt h (fderiv ℝ h (γ s)) (γ s) :=
      ((hC1.differentiableOn one_ne_zero _ hγs).differentiableAt (hEo.mem_nhds hγs)).hasFDerivAt
    have hh' := hhd.comp_hasDerivAt s hγ'
    have hF2 : HasDerivAt (deriv F) (deriv (deriv F) (h (γ s))) (h (γ s)) :=
      (hF1d.differentiableAt (hΩ.mem_nhds (hh.2.1 hγs))).hasDerivAt
    exact hF2.comp s hh'
  set ψ0 := deriv F (h u) with hψ0
  have hψ0ne : ψ0 ≠ 0 := hFne _ (hh.2.1 hu)
  set K := (8 * C₀ + 1) * η with hK
  have hK0 : 0 < K := by positivity
  have hbound : ∀ s ∈ Icc (0 : ℝ) 1, ‖ψ' s‖ ≤ K * ‖deriv F (h (γ s))‖ := by
    intro s hs
    have hγs := hB (hγB s hs)
    have hsm' := hsm _ (hγB s hs)
    have hne := hFne _ (hh.2.1 hγs)
    have htγ := (hcomp _ (hγB s hs)).1
    have hdh := (qd_dh_bound hμ hh hb1 hγs).2
    rw [norm_div, norm_mul, div_le_iff₀ (norm_pos_iff.mpr hne)] at hsm'
    have hyu : ‖y - u‖ ≤ ρ := by have := mem_closedBall.mp hy; rwa [dist_eq_norm] at this
    have htpos : 0 < ‖γ s - h (γ s)‖ := by linarith
    have h1 : ‖ψ' s‖ ≤ ‖deriv (deriv F) (h (γ s))‖ * (4 * C₀ * ‖y - u‖) := by
      rw [hψ', norm_mul]
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      exact ((fderiv ℝ h (γ s)).le_opNorm (y - u)).trans
        (mul_le_mul_of_nonneg_right hdh (norm_nonneg _))
    have h2 : ‖deriv (deriv F) (h (γ s))‖ ≤ η * ‖deriv F (h (γ s))‖ / ‖γ s - h (γ s)‖ := by
      rw [le_div_iff₀ htpos]; linarith
    have h3 : 4 * C₀ * ‖y - u‖ ≤ 4 * C₀ * ‖γ s - h (γ s)‖ := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      have : ρ ≤ ‖u - h u‖ / 2 := by
        rw [hρ]; apply div_le_div_of_nonneg_left (norm_nonneg _) (by norm_num); nlinarith
      linarith
    calc ‖ψ' s‖ ≤ ‖deriv (deriv F) (h (γ s))‖ * (4 * C₀ * ‖y - u‖) := h1
      _ ≤ η * ‖deriv F (h (γ s))‖ / ‖γ s - h (γ s)‖ * (4 * C₀ * ‖γ s - h (γ s)‖) :=
          mul_le_mul h2 h3 (by positivity) (by positivity)
      _ = 4 * C₀ * η * ‖deriv F (h (γ s))‖ := by field_simp
      _ ≤ K * ‖deriv F (h (γ s))‖ := by
          rw [hK]; apply mul_le_mul_of_nonneg_right _ (norm_nonneg _); nlinarith
  have hg := norm_le_gronwallBound_of_norm_deriv_right_le (f := fun s => deriv F (h (γ s)) - ψ0)
    (f' := ψ') (δ := 0) (K := K) (ε := K * ‖ψ0‖) (a := 0) (b := 1)
    (fun s hs => ((hder s hs).sub_const ψ0).continuousAt.continuousWithinAt)
    (fun s hs => ((hder s (Ico_subset_Icc_self hs)).sub_const ψ0).hasDerivWithinAt)
    (by simp [hγ, hψ0]) (fun s hs => by
      have := hbound s (Ico_subset_Icc_self hs)
      have htri : ‖deriv F (h (γ s))‖ ≤ ‖deriv F (h (γ s)) - ψ0‖ + ‖ψ0‖ := by
        calc _ = ‖(deriv F (h (γ s)) - ψ0) + ψ0‖ := by ring_nf
          _ ≤ _ := norm_add_le _ _
      nlinarith) 1 ⟨zero_le_one, le_rfl⟩
  rw [gronwallBound_of_K_ne_0 hK0.ne'] at hg
  simp only [sub_zero, zero_mul, zero_add, mul_one] at hg
  rw [show K * ‖ψ0‖ / K = ‖ψ0‖ by field_simp] at hg
  have hγ1 : γ 1 = y := by simp [hγ]
  rw [hγ1] at hg
  rw [show deriv F (h y) / ψ0 - 1 = (deriv F (h y) - ψ0) / ψ0 by field_simp, norm_div,
    div_le_iff₀ (norm_pos_iff.mpr hψ0ne)]
  linarith

/-- The value denominator through the relative pre-Schwarzian: `B(v) + t B'(v) = B(v)(1 - κ/2)`,
`κ = t F''(v)/F'(v)`. -/
theorem qd_den_formula {μ ν : LinfStar} (hμ : μ ∈ LinfStarBall) {A B : ℂ → ℂ}
    (hA : DifferentiableOn ℂ A (fsans μ '' unitDisc)) (hB : DifferentiableOn ℂ B (fsans μ '' unitDisc))
    (hode : ∀ z ∈ fsans μ '' unitDisc,
      deriv (deriv A) z + schwarzianHol (crs_transition μ ν) z / 2 * A z = 0 ∧
      deriv (deriv B) z + schwarzianHol (crs_transition μ ν) z / 2 * B z = 0 ∧
      A z * deriv B z - B z * deriv A z = 1)
    (hrat : ∀ z ∈ fsans μ '' unitDisc, (crs_transition μ ν z : ExtPlane) = t203_ratio (A z) (B z))
    {v : ℂ} (hv : v ∈ fsans μ '' unitDisc) (t : ℂ) :
    B v + t * deriv B v = B v * (1 - t * deriv (deriv (crs_transition μ ν)) v /
      deriv (crs_transition μ ν) v / 2) ∧
    -(1 / (B v + t * deriv B v) ^ 2) = deriv (crs_transition μ ν) v /
      (1 - t * deriv (deriv (crs_transition μ ν)) v / deriv (crs_transition μ ν) v / 2) ^ 2 := by
  obtain ⟨hb, -, h1, h2⟩ := qd_FB hμ hA hB hode hrat hv
  have e1 : B v + t * deriv B v = B v * (1 - t * deriv (deriv (crs_transition μ ν)) v /
      deriv (crs_transition μ ν) v / 2) := by
    rw [h1, h2]; field_simp; ring
  refine ⟨e1, ?_⟩
  rw [e1, h1]
  by_cases hk : (1 - t * (2 * deriv B v / B v ^ 3) / (-1 / B v ^ 2) / 2) = 0
  · rw [h2, hk]; simp
  · rw [h2]; field_simp

/-- `|(1 - z/2)²/(1 - x/2)² - 1| ≤ 12 η` for `|x|, |z| ≤ η ≤ 1`. -/
theorem qd_quot_sq {x z : ℂ} {η : ℝ} (hη : η ≤ 1) (hx : ‖x‖ ≤ η) (hz : ‖z‖ ≤ η) :
    ‖(1 - z / 2) ^ 2 / (1 - x / 2) ^ 2 - 1‖ ≤ 12 * η := by
  have hη0 : 0 ≤ η := (norm_nonneg x).trans hx
  have hx2 : (1 / 2 : ℝ) ≤ ‖1 - x / 2‖ := by
    have := norm_sub_norm_le (1 : ℂ) (x / 2)
    rw [norm_one, norm_div, Complex.norm_ofNat] at this
    linarith
  have hne : (1 - x / 2) ≠ 0 := norm_pos_iff.mp (by linarith)
  rw [show (1 - z / 2) ^ 2 / (1 - x / 2) ^ 2 - 1 =
      ((x - z) / 2 * (2 - (x + z) / 2)) / (1 - x / 2) ^ 2 by
        rw [div_sub_one (pow_ne_zero 2 hne)]; congr 1; ring]
  rw [norm_div, norm_mul, norm_pow, div_le_iff₀ (by positivity)]
  have h1 : ‖(x - z) / 2‖ ≤ η := by
    rw [norm_div, Complex.norm_ofNat]
    linarith [norm_sub_le x z]
  have h2 : ‖2 - (x + z) / 2‖ ≤ 3 := by
    have := norm_sub_le (2 : ℂ) ((x + z) / 2)
    rw [Complex.norm_ofNat, norm_div, Complex.norm_ofNat] at this
    linarith [norm_add_le x z]
  have h3 : (1 / 4 : ℝ) ≤ ‖1 - x / 2‖ ^ 2 := by nlinarith
  calc ‖(x - z) / 2‖ * ‖2 - (x + z) / 2‖ ≤ η * 3 :=
        mul_le_mul h1 h2 (norm_nonneg _) hη0
    _ ≤ 12 * η * ‖1 - x / 2‖ ^ 2 := by nlinarith

/-- **(B0, one ball)** Deterministic estimate: if the relative pre-Schwarzian at reflection scale is `≤ η` on the ball
and the Schwarzian error is `≤ η` at `y`, then the derivative of `N` at `y` is within
`Φ(η)` (relative) of the osculating derivative at `u`. -/
theorem qd_B0_det {μ ν : LinfStar} (hμ : μ ∈ LinfStarBall) (hν : ν ∈ LinfStarBall)
    {h : ℂ → ℂ} {C₀ : ℝ}
    (hC1 : ContDiffOn ℝ 1 h (gsans μ '' unitDiscExterior))
    (hh : IsQCReflection (fsans μ '' unitDisc) (gsans μ '' unitDiscExterior) h)
    (hb1 : ∀ u ∈ gsans μ '' unitDiscExterior, ‖u - h u‖ ^ 2 * ‖fderiv ℝ h u‖ *
      poincareDensity (fsans μ '' unitDisc) (h u) ^ 2 ≤ C₀) (hC₀ : 0 ≤ C₀)
    {A B : ℂ → ℂ} (hA : DifferentiableOn ℂ A (fsans μ '' unitDisc))
    (hB : DifferentiableOn ℂ B (fsans μ '' unitDisc))
    (hode : ∀ z ∈ fsans μ '' unitDisc,
      deriv (deriv A) z + schwarzianHol (crs_transition μ ν) z / 2 * A z = 0 ∧
      deriv (deriv B) z + schwarzianHol (crs_transition μ ν) z / 2 * B z = 0 ∧
      A z * deriv B z - B z * deriv A z = 1)
    (hrat : ∀ z ∈ fsans μ '' unitDisc, (crs_transition μ ν z : ExtPlane) = t203_ratio (A z) (B z))
    {u : ℂ} (hu : u ∈ gsans μ '' unitDiscExterior) {η : ℝ} (hη0 : 0 < η) (hη1 : η ≤ 1)
    (hk : ∀ w ∈ closedBall u (‖u - h u‖ / (2 * (1 + 4 * C₀))),
      ‖(w - h w) * deriv (deriv (crs_transition μ ν)) (h w) / deriv (crs_transition μ ν) (h w)‖ ≤ η)
    {y : ℂ} (hy : y ∈ closedBall u (‖u - h u‖ / (2 * (1 + 4 * C₀))))
    (hS : ‖schwarzianHol (crs_transition μ ν) (h y)‖ * ‖y - h y‖ ^ 2 * ‖fderiv ℝ h y‖ ≤ η) :
    B (h u) + (u - h u) * deriv B (h u) ≠ 0 ∧ B (h y) + (y - h y) * deriv B (h y) ≠ 0 ∧
      ‖fderiv ℝ (cnf_finite A B h) y - (-(1 / (B (h u) + (u - h u) * deriv B (h u)) ^ 2)) •
          (1 : ℂ →L[ℝ] ℂ)‖ ≤
        ((Real.exp ((8 * C₀ + 1) * η) - 1) * (1 + 12 * η) + 12 * η +
          Real.exp ((8 * C₀ + 1) * η) * (1 + 12 * η) * η / 2) *
          ‖1 / (B (h u) + (u - h u) * deriv B (h u)) ^ 2‖ := by
  set F := crs_transition μ ν with hFdef
  set S := schwarzianHol F with hSdef
  have hΩ : IsOpen (fsans μ '' unitDisc) := (S2C.s2c_conf_f hμ).isOpen isOpen_ball
  have hEo : IsOpen (gsans μ '' unitDiscExterior) := (l29b_open_disjoint hμ).2.1
  obtain ⟨hBsub, -⟩ := qd_ball hμ hC1 hh hb1 hC₀ hu
  have huB : u ∈ closedBall u (‖u - h u‖ / (2 * (1 + 4 * C₀))) := mem_closedBall_self (by positivity)
  have hyE := hBsub hy
  have hvu := hh.2.1 hu
  have hvy := hh.2.1 hyE
  set κu := (u - h u) * deriv (deriv F) (h u) / deriv F (h u) with hκu
  set κy := (y - h y) * deriv (deriv F) (h y) / deriv F (h y) with hκy
  have hku := hk u huB
  have hky := hk y hy
  have hnz : ∀ κ : ℂ, ‖κ‖ ≤ η → (1 - κ / 2) ≠ 0 := by
    intro κ hκ h0
    have : (1 : ℂ) = κ / 2 := by linear_combination h0
    have := congrArg norm this
    rw [norm_one, norm_div, Complex.norm_ofNat] at this
    linarith
  obtain ⟨du1, du2⟩ := qd_den_formula hμ hA hB hode hrat hvu (u - h u)
  obtain ⟨dy1, dy2⟩ := qd_den_formula hμ hA hB hode hrat hvy (y - h y)
  obtain ⟨hBu, -, hF1u, -⟩ := qd_FB hμ hA hB hode hrat hvu
  obtain ⟨hBy, -, hF1y, -⟩ := qd_FB hμ hA hB hode hrat hvy
  have hdu : B (h u) + (u - h u) * deriv B (h u) ≠ 0 := by
    rw [du1]; exact mul_ne_zero hBu (by simpa only [← hκu] using hnz κu hku)
  have hdy : B (h y) + (y - h y) * deriv B (h y) ≠ 0 := by
    rw [dy1]; exact mul_ne_zero hBy (by simpa only [← hκy] using hnz κy hky)
  refine ⟨hdu, hdy, ?_⟩
  -- the exact derivative
  have hAd : ∀ v ∈ fsans μ '' unitDisc, HasDerivAt A (deriv A v) v := fun v hv =>
    (hA.differentiableAt (hΩ.mem_nhds hv)).hasDerivAt
  have hBd : ∀ v ∈ fsans μ '' unitDisc, HasDerivAt B (deriv B v) v := fun v hv =>
    (hB.differentiableAt (hΩ.mem_nhds hv)).hasDerivAt
  have hA2 : HasDerivAt (deriv A) (-(S (h y) / 2 * A (h y))) (h y) := by
    have := ((hA.deriv hΩ).differentiableAt (hΩ.mem_nhds hvy)).hasDerivAt
    rwa [show deriv (deriv A) (h y) = -(S (h y) / 2 * A (h y)) by
      linear_combination (hode _ hvy).1] at this
  have hB2 : HasDerivAt (deriv B) (-(S (h y) / 2 * B (h y))) (h y) := by
    have := ((hB.deriv hΩ).differentiableAt (hΩ.mem_nhds hvy)).hasDerivAt
    rwa [show deriv (deriv B) (h y) = -(S (h y) / 2 * B (h y)) by
      linear_combination (hode _ hvy).2.1] at this
  have hgd : DifferentiableAt ℝ h y :=
    (hC1.differentiableOn one_ne_zero _ hyE).differentiableAt (hEo.mem_nhds hyE)
  have hfd := (qd_N_hasFDerivAt hgd (hAd _ hvy) hA2 (hBd _ hvy) hB2 (hode _ hvy).2.2 hdy).fderiv
  obtain ⟨L, hL⟩ : ∃ L : ℂ, L = -(1 / (B (h u) + (u - h u) * deriv B (h u)) ^ 2) := ⟨_, rfl⟩
  have hLn : ‖1 / (B (h u) + (u - h u) * deriv B (h u)) ^ 2‖ = ‖L‖ := by rw [hL, norm_neg]
  rw [← hL, hLn]
  set X : ℂ →L[ℝ] ℂ := ((y - h y) ^ 2 * (S (h y) / 2)) • fderiv ℝ h y with hX
  set a : ℂ := deriv F (h y) / deriv F (h u) with ha
  set b : ℂ := (1 - κu / 2) ^ 2 / (1 - κy / 2) ^ 2 with hb
  have hM : -(1 / (B (h y) + (y - h y) * deriv B (h y)) ^ 2) = L * (a * b) := by
    rw [hL, du2, dy2, ha, hb]
    have h1 := hnz κu hku
    have h2 := hnz κy hky
    have h3 : deriv F (h u) ≠ 0 := by rw [hF1u]; simp [hBu]
    rw [← hκu, ← hκy]
    field_simp
    have h4 : (2 : ℂ) - κu ≠ 0 := fun h0 => h1 (by linear_combination h0 / 2)
    rw [← hFdef]
    field_simp
  have hfd' : fderiv ℝ (cnf_finite A B h) y - L • (1 : ℂ →L[ℝ] ℂ) =
      L • ((a * b - 1) • (1 : ℂ →L[ℝ] ℂ) + (a * b) • X) := by
    rw [hfd, hM, hX]
    module
  have hXn : ‖X‖ ≤ η / 2 := by
    rw [hX, norm_smul, norm_mul, norm_div, norm_pow, Complex.norm_ofNat]
    nlinarith [norm_nonneg (fderiv ℝ h y), norm_nonneg (S (h y)), norm_nonneg (y - h y)]
  set δ := Real.exp ((8 * C₀ + 1) * η) - 1 with hδ
  have hδ0 : 0 ≤ δ := by
    rw [hδ, sub_nonneg]; exact Real.one_le_exp (by positivity)
  have han : ‖a - 1‖ ≤ δ := qd_Fratio hμ hν hC1 hh hb1 hC₀ hu hη0 hk hy
  have hbn : ‖b - 1‖ ≤ 12 * η := qd_quot_sq hη1 hky hku
  have hab : ‖a * b - 1‖ ≤ δ * (1 + 12 * η) + 12 * η := by
    have hb' : ‖b‖ ≤ 1 + 12 * η := by
      have := norm_le_norm_add_norm_sub' b 1
      rw [norm_one] at this; linarith
    calc ‖a * b - 1‖ = ‖(a - 1) * b + (b - 1)‖ := by ring_nf
      _ ≤ ‖a - 1‖ * ‖b‖ + ‖b - 1‖ := by
          rw [← norm_mul]; exact norm_add_le _ _
      _ ≤ δ * (1 + 12 * η) + 12 * η := by
          gcongr
  have hab2 : ‖a * b‖ ≤ (δ + 1) * (1 + 12 * η) := by
    have := norm_le_norm_add_norm_sub' (a * b) 1
    rw [norm_one] at this
    nlinarith
  rw [hfd', norm_smul, mul_comm]
  refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg L)
  calc ‖(a * b - 1) • (1 : ℂ →L[ℝ] ℂ) + (a * b) • X‖
      ≤ ‖a * b - 1‖ * ‖(1 : ℂ →L[ℝ] ℂ)‖ + ‖a * b‖ * ‖X‖ := by
        refine (norm_add_le _ _).trans ?_
        rw [norm_smul, norm_smul]
    _ ≤ (δ * (1 + 12 * η) + 12 * η) * 1 + (δ + 1) * (1 + 12 * η) * (η / 2) := by
        gcongr
        exact ContinuousLinearMap.norm_id_le
    _ = _ := by rw [hδ]; ring

/-- Along sequences tending to the reflection-boundary filter, the target scale `|u - h u| |F'(h u)|` tends to `0`
(`= |x_n| |b_ν| |p_n|` with `b_ν → 0`). -/
theorem qd_tF_seq {μ ν : LinfStar} (hμ : μ ∈ LinfStarBall) (hν : ν ∈ LinfStarBall)
    (hP : AInf.toFun (bersPhi ν - bersPhi μ) ∈ A2fun unitDisc)
    {h : ℂ → ℂ} {p : ℂ} (hp : p ∈ fsans μ '' unitDisc)
    (hh : IsQCReflection (fsans μ '' unitDisc) (gsans μ '' unitDiscExterior) h)
    (hinf : Tendsto h (cocompact ℂ ⊓ 𝓟 (gsans μ '' unitDiscExterior)) (𝓝 p))
    {u : ℕ → ℂ} (hu : Tendsto u atTop (crb_reflectionBoundary μ h)) :
    Tendsto (fun n => ‖u n - h (u n)‖ * ‖deriv (crs_transition μ ν) (h (u n))‖) atTop (𝓝 0) := by
  obtain ⟨eμ, Kμ, hKμ, heμ⟩ := cra_welding_extension hμ
  obtain ⟨eν, Kν, hKν, heν⟩ := cra_welding_extension hν
  set a : ℕ → ℂ := fun n => Function.invFunOn (fsans μ) unitDisc (h (u n)) with ha_def
  have hE : ∀ᶠ n in atTop, u n ∈ gsans μ '' unitDiscExterior :=
    tendsto_principal.mp (hu.mono_right inf_le_right)
  have hA : Tendsto (fun n => ‖a n‖) atTop (𝓝 1) := by
    have h2 := tendsto_comap_iff.mp (hu.mono_right inf_le_left)
    exact tendsto_comap_iff.mp (h2.mono_right inf_le_left)
  have hmem : ∀ n, u n ∈ gsans μ '' unitDiscExterior → a n ∈ unitDisc ∧ fsans μ (a n) = h (u n) :=
    fun n hn => ⟨Function.invFunOn_mem (hh.2.1 hn), Function.invFunOn_eq (hh.2.1 hn)⟩
  set a' : ℕ → ℂ := fun n => if 0 < ‖a n‖ ∧ ‖a n‖ < 1 then a n else (1 / 2 : ℂ) with ha'_def
  have ha' : ∀ n, 0 < ‖a' n‖ ∧ ‖a' n‖ < 1 := by
    intro n
    simp only [ha'_def]
    split_ifs with hc
    · exact hc
    · norm_num
  have hpos : ∀ᶠ n in atTop, 0 < ‖a n‖ := hA.eventually (lt_mem_nhds one_pos)
  have heq : ∀ᶠ n in atTop, a' n = a n ∧ u n ∈ gsans μ '' unitDiscExterior := by
    filter_upwards [hE, hpos] with n hn hn0
    have h1 : ‖a n‖ < 1 := mem_ball_zero_iff.mp (hmem n hn).1
    exact ⟨by simp only [ha'_def, if_pos (And.intro hn0 h1)], hn⟩
  have hA' : Tendsto (fun n => ‖a' n‖) atTop (𝓝 1) :=
    hA.congr' (heq.mono fun n hn => by show ‖a n‖ = ‖a' n‖; rw [hn.1])
  obtain ⟨hp1, -⟩ := crbl_actual_relative_jets hμ hν hP eμ eν hKμ hKν heμ heν ha' hA'
  have hbν := cba_welding_difference hν (fun n => (ha' n).1) (fun n => (ha' n).2) hA'
  obtain ⟨R, hR0, hRu⟩ := qd_bdd_of_boundary hμ hp hinf hu
  obtain ⟨D, hD, hcbd⟩ := cbd_normalized_displacement hμ hh R hR0
  apply Filter.tendsto_of_subseq_tendsto
  intro ns hns
  obtain ⟨φ, hφ, C, hC⟩ := qd_nderiv_subseq hμ eμ hKμ heμ (a := fun n => a' (ns n)) (fun n => ha' _)
    (hA'.comp hns)
  refine ⟨φ, ?_⟩
  have hι : Tendsto (fun n => ns (φ n)) atTop atTop := hns.comp hφ.tendsto_atTop
  have hlim : Tendsto (fun n => 2 * D * C * (‖fsans ν (cbl_source (a' (ns (φ n))) 1) - fsans ν (a' (ns (φ n)))‖ *
      ‖crbl_relative_first (cbl_normalized eμ (a' (ns (φ n)))) (cbl_normalized eν (a' (ns (φ n))))‖))
      atTop (𝓝 0) := by
    have h1 := ((hbν.comp hι).norm.mul (hp1.comp hι).norm).const_mul (2 * D * C)
    simp only [norm_zero, zero_mul, mul_zero, norm_one] at h1
    exact h1
  apply squeeze_zero' (Eventually.of_forall fun n => by positivity) _ hlim
  filter_upwards [hι.eventually heq, hι.eventually hRu, hC] with n hn hnR hnC
  set m := ns (φ n)
  obtain ⟨hmD, hmf⟩ := hmem m hn.2
  have hfa : fsans μ (a' m) = h (u m) := by rw [hn.1]; exact hmf
  obtain ⟨hbμ, -, hf0, -, hF1, -⟩ := ccn_transition_jets hμ hν eμ eν heμ heν (ha' m).1 (ha' m).2
  obtain ⟨-, -, hfj, -⟩ := ccn_normalized_jets hμ eμ heμ (ha' m).1 (ha' m).2
  have hx := hcbd (u m) hn.2 hnR (a' m) (ha' m).1 (ha' m).2 hfa (eμ (cbl_source (a' m) 1) - eμ (a' m))
  rw [← hfj] at hx
  rw [hfa] at hF1
  rw [hF1]
  have hsrc : cbl_source (a' m) 1 ∈ unitDisc := cbl_source_one_mem (ha' m).1 (ha' m).2
  have haD' : a' m ∈ unitDisc := mem_ball_zero_iff.mpr (ha' m).2
  rw [heν hsrc, heν haD']
  have hxC : ‖(u m - h (u m)) / (eμ (cbl_source (a' m) 1) - eμ (a' m))‖ ≤ 2 * D * C :=
    hx.trans (mul_le_mul_of_nonneg_left hnC (by positivity))
  have hbpos : 0 < ‖eμ (cbl_source (a' m) 1) - eμ (a' m)‖ := norm_pos_iff.mpr hbμ
  have key : ‖u m - h (u m)‖ * ‖(fsans ν (cbl_source (a' m) 1) - fsans ν (a' m)) /
        (eμ (cbl_source (a' m) 1) - eμ (a' m)) *
        (deriv (cbl_normalized eν (a' m)) 0 / deriv (cbl_normalized eμ (a' m)) 0)‖ =
      ‖(u m - h (u m)) / (eμ (cbl_source (a' m) 1) - eμ (a' m))‖ *
        (‖fsans ν (cbl_source (a' m) 1) - fsans ν (a' m)‖ *
          ‖crbl_relative_first (cbl_normalized eμ (a' m)) (cbl_normalized eν (a' m))‖) := by
    simp only [crbl_relative_first, norm_mul, norm_div]
    field_simp
  rw [key]
  exact mul_le_mul_of_nonneg_right hxC (by positivity)

/-- **(B0) `C¹` blow-up of the Ahlfors map at the boundary.** For the chosen reflection `h` and an ODE pair `A, B`
of the relative map, eventually along the reflection-boundary filter, the derivative of
`N = cnf_finite A B h` on the ball `u + (u - h u)·B(0, r)` is uniformly close to the derivative
`-1/(B(h u) + (u - h u) B'(h u))²` of the osculating Möbius map at `u`. -/
theorem qd_blowup {μ ν : LinfStar} (hμ : μ ∈ LinfStarBall) (hν : ν ∈ LinfStarBall)
    (hP : AInf.toFun (bersPhi ν - bersPhi μ) ∈ A2fun unitDisc)
    {h : ℂ → ℂ} {K C₀ : ℝ} {p : ℂ} (hp : p ∈ fsans μ '' unitDisc)
    (hC1 : ContDiffOn ℝ 1 h (gsans μ '' unitDiscExterior))
    (hpl : IsPlanarQCReflection (gsans μ '' unitDiscExterior) ((fsans μ '' unitDisc) \ {p}) h K)
    (hh : IsQCReflection (fsans μ '' unitDisc) (gsans μ '' unitDiscExterior) h)
    (hinf : Tendsto h (cocompact ℂ ⊓ 𝓟 (gsans μ '' unitDiscExterior)) (𝓝 p))
    (hb1 : ∀ u ∈ gsans μ '' unitDiscExterior, ‖u - h u‖ ^ 2 * ‖fderiv ℝ h u‖ *
      poincareDensity (fsans μ '' unitDisc) (h u) ^ 2 ≤ C₀)
    (hb2 : ∀ u ∈ gsans μ '' unitDiscExterior, ‖u - h u‖ ^ 2 * ‖dzbar h u‖ *
      poincareDensity (fsans μ '' unitDisc) (h u) ^ 2 ≤ C₀)
    {A B : ℂ → ℂ} (hA : DifferentiableOn ℂ A (fsans μ '' unitDisc))
    (hB : DifferentiableOn ℂ B (fsans μ '' unitDisc))
    (hode : ∀ z ∈ fsans μ '' unitDisc,
      deriv (deriv A) z + schwarzianHol (crs_transition μ ν) z / 2 * A z = 0 ∧
      deriv (deriv B) z + schwarzianHol (crs_transition μ ν) z / 2 * B z = 0 ∧
      A z * deriv B z - B z * deriv A z = 1)
    (hrat : ∀ z ∈ fsans μ '' unitDisc, (crs_transition μ ν z : ExtPlane) = t203_ratio (A z) (B z)) :
    ∃ r : ℝ, 0 < r ∧ ∀ ε : ℝ, 0 < ε → ∀ᶠ u in crb_reflectionBoundary μ h,
      B (h u) + (u - h u) * deriv B (h u) ≠ 0 ∧
      ∀ Z ∈ closedBall (0 : ℂ) r,
        u + (u - h u) * Z ∈ gsans μ '' unitDiscExterior ∧
        B (h (u + (u - h u) * Z)) + (u + (u - h u) * Z - h (u + (u - h u) * Z)) *
          deriv B (h (u + (u - h u) * Z)) ≠ 0 ∧
        ‖fderiv ℝ (cnf_finite A B h) (u + (u - h u) * Z) -
            (-(1 / (B (h u) + (u - h u) * deriv B (h u)) ^ 2)) • (1 : ℂ →L[ℝ] ℂ)‖ ≤
          ε * ‖1 / (B (h u) + (u - h u) * deriv B (h u)) ^ 2‖ := by
  have hC₀ : 0 ≤ C₀ := by
    have h2 : gsans μ 2 ∈ gsans μ '' unitDiscExterior :=
      ⟨2, show (1 : ℝ) < ‖(2 : ℂ)‖ by norm_num, rfl⟩
    exact le_trans (by positivity) (hb1 _ h2)
  have hk0 : 0 < 2 * (1 + 4 * C₀) := by positivity
  have hsmall : Tendsto (fun u => ‖schwarzianHol (crs_transition μ ν) (h u)‖ * ‖u - h u‖ ^ 2 *
      ‖fderiv ℝ h u‖) (crb_reflectionBoundary μ h) (𝓝 0) :=
    crb_reflection_error_tendsto_zero hμ hP (fun _ hw => crs_schwarzian_pullback hμ hν hw) hh.2.1 hC₀ hb1
  refine ⟨1 / (2 * (1 + 4 * C₀)), by positivity, fun ε hε => ?_⟩
  -- choose η with Φ(η) ≤ ε
  set Φ : ℝ → ℝ := fun η => (Real.exp ((8 * C₀ + 1) * η) - 1) * (1 + 12 * η) + 12 * η +
    Real.exp ((8 * C₀ + 1) * η) * (1 + 12 * η) * η / 2 with hΦ
  have hΦc : Tendsto Φ (𝓝 0) (𝓝 0) := by
    have hc : Continuous Φ := by rw [hΦ]; fun_prop
    have := hc.tendsto 0
    simpa [hΦ] using this
  obtain ⟨δ, hδ, hδΦ⟩ := Metric.tendsto_nhds_nhds.mp hΦc ε hε
  set η := min (δ / 2) 1 with hη
  have hη0 : 0 < η := lt_min (by linarith) one_pos
  have hη1 : η ≤ 1 := min_le_right _ _
  have hΦη : Φ η ≤ ε := by
    have hd : dist η 0 < δ := by
      rw [Real.dist_eq, sub_zero, abs_of_pos hη0]
      exact lt_of_le_of_lt (min_le_left _ _) (by linarith)
    have := hδΦ hd
    rw [Real.dist_eq, sub_zero] at this
    exact (le_abs_self _).trans this.le
  haveI : (crb_reflectionBoundary μ h).IsCountablyGenerated := by
    unfold crb_reflectionBoundary crb_diskBoundary
    infer_instance
  rw [Filter.eventually_iff_seq_eventually]
  intro u hu
  have hE : ∀ᶠ n in atTop, u n ∈ gsans μ '' unitDiscExterior :=
    tendsto_principal.mp (hu.mono_right inf_le_right)
  have hk := qd_unif_seq hμ hp hC1 hh hinf hb1 hC₀
    (g := fun w => ‖(w - h w) * deriv (deriv (crs_transition μ ν)) (h w) /
      deriv (crs_transition μ ν) (h w)‖)
    (fun w hw => by simpa using (qd_prerel_seq hμ hν hP hp hh hinf hw).norm) hu hη0
  have hs := qd_unif_seq hμ hp hC1 hh hinf hb1 hC₀
    (g := fun w => ‖schwarzianHol (crs_transition μ ν) (h w)‖ * ‖w - h w‖ ^ 2 * ‖fderiv ℝ h w‖)
    (fun w hw => hsmall.comp hw) hu hη0
  filter_upwards [hE, hk, hs] with n hn hkn hsn
  have hk' : ∀ w ∈ closedBall (u n) (‖u n - h (u n)‖ / (2 * (1 + 4 * C₀))),
      ‖(w - h w) * deriv (deriv (crs_transition μ ν)) (h w) / deriv (crs_transition μ ν) (h w)‖ ≤ η :=
    fun w hw => (le_abs_self _).trans (hkn w hw).le
  have hs' : ∀ w ∈ closedBall (u n) (‖u n - h (u n)‖ / (2 * (1 + 4 * C₀))),
      ‖schwarzianHol (crs_transition μ ν) (h w)‖ * ‖w - h w‖ ^ 2 * ‖fderiv ℝ h w‖ ≤ η :=
    fun w hw => (le_abs_self _).trans (hsn w hw).le
  have huB : u n ∈ closedBall (u n) (‖u n - h (u n)‖ / (2 * (1 + 4 * C₀))) :=
    mem_closedBall_self (by positivity)
  obtain ⟨hBsub, -⟩ := qd_ball hμ hC1 hh hb1 hC₀ hn
  refine ⟨(qd_B0_det hμ hν hC1 hh hb1 hC₀ hA hB hode hrat hn hη0 hη1 hk' huB (hs' _ huB)).1,
    fun Z hZ => ?_⟩
  have hyB : u n + (u n - h (u n)) * Z ∈ closedBall (u n) (‖u n - h (u n)‖ / (2 * (1 + 4 * C₀))) := by
    rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_mul]
    have hZ' : ‖Z‖ ≤ 1 / (2 * (1 + 4 * C₀)) := mem_closedBall_zero_iff.mp hZ
    calc ‖u n - h (u n)‖ * ‖Z‖ ≤ ‖u n - h (u n)‖ * (1 / (2 * (1 + 4 * C₀))) :=
          mul_le_mul_of_nonneg_left hZ' (norm_nonneg _)
      _ = _ := by ring
  obtain ⟨-, hdy, hineq⟩ := qd_B0_det hμ hν hC1 hh hb1 hC₀ hA hB hode hrat hn hη0 hη1 hk' hyB
    (hs' _ hyB)
  refine ⟨hBsub hyB, hdy, hineq.trans ?_⟩
  exact mul_le_mul_of_nonneg_right hΦη (norm_nonneg _)

/-- **(B2 input) Contact bound.** Eventually along the reflection-boundary filter, `N(u)` is within a fixed multiple
of the target scale `|u - h u| / |B(h u) + (u - h u) B'(h u)|²` from `F(h u)`. -/
theorem qd_contact {μ ν : LinfStar} (hμ : μ ∈ LinfStarBall) (hν : ν ∈ LinfStarBall)
    (hP : AInf.toFun (bersPhi ν - bersPhi μ) ∈ A2fun unitDisc)
    {h : ℂ → ℂ} {K C₀ : ℝ} {p : ℂ} (hp : p ∈ fsans μ '' unitDisc)
    (hC1 : ContDiffOn ℝ 1 h (gsans μ '' unitDiscExterior))
    (hpl : IsPlanarQCReflection (gsans μ '' unitDiscExterior) ((fsans μ '' unitDisc) \ {p}) h K)
    (hh : IsQCReflection (fsans μ '' unitDisc) (gsans μ '' unitDiscExterior) h)
    (hinf : Tendsto h (cocompact ℂ ⊓ 𝓟 (gsans μ '' unitDiscExterior)) (𝓝 p))
    (hb1 : ∀ u ∈ gsans μ '' unitDiscExterior, ‖u - h u‖ ^ 2 * ‖fderiv ℝ h u‖ *
      poincareDensity (fsans μ '' unitDisc) (h u) ^ 2 ≤ C₀)
    (hb2 : ∀ u ∈ gsans μ '' unitDiscExterior, ‖u - h u‖ ^ 2 * ‖dzbar h u‖ *
      poincareDensity (fsans μ '' unitDisc) (h u) ^ 2 ≤ C₀)
    {A B : ℂ → ℂ} (hA : DifferentiableOn ℂ A (fsans μ '' unitDisc))
    (hB : DifferentiableOn ℂ B (fsans μ '' unitDisc))
    (hode : ∀ z ∈ fsans μ '' unitDisc,
      deriv (deriv A) z + schwarzianHol (crs_transition μ ν) z / 2 * A z = 0 ∧
      deriv (deriv B) z + schwarzianHol (crs_transition μ ν) z / 2 * B z = 0 ∧
      A z * deriv B z - B z * deriv A z = 1)
    (hrat : ∀ z ∈ fsans μ '' unitDisc, (crs_transition μ ν z : ExtPlane) = t203_ratio (A z) (B z)) :
    ∃ C : ℝ, ∀ᶠ u in crb_reflectionBoundary μ h,
      B (h u) + (u - h u) * deriv B (h u) ≠ 0 ∧
      ‖cnf_finite A B h u - crs_transition μ ν (h u)‖ ≤
        C * (‖u - h u‖ * ‖1 / (B (h u) + (u - h u) * deriv B (h u)) ^ 2‖) := by
  haveI : (crb_reflectionBoundary μ h).IsCountablyGenerated := by
    unfold crb_reflectionBoundary crb_diskBoundary
    infer_instance
  have hpre : Tendsto (fun u => (u - h u) * deriv (deriv (crs_transition μ ν)) (h u) /
      deriv (crs_transition μ ν) (h u)) (crb_reflectionBoundary μ h) (𝓝 0) :=
    tendsto_iff_seq_tendsto.mpr fun u hu => qd_prerel_seq hμ hν hP hp hh hinf hu
  have hE : ∀ᶠ u in crb_reflectionBoundary μ h, u ∈ gsans μ '' unitDiscExterior :=
    mem_inf_of_right (mem_principal_self _)
  refine ⟨2, ?_⟩
  filter_upwards [hE, hpre.eventually (Metric.ball_mem_nhds 0 one_pos)] with u hu hκ
  rw [dist_zero_right] at hκ
  have hv := hh.2.1 hu
  obtain ⟨hBv, hFv, -, -⟩ := qd_FB hμ hA hB hode hrat hv
  obtain ⟨d1, -⟩ := qd_den_formula hμ hA hB hode hrat hv (u - h u)
  set κ := (u - h u) * deriv (deriv (crs_transition μ ν)) (h u) / deriv (crs_transition μ ν) (h u)
    with hκdef
  have h1κ : (1 / 2 : ℝ) ≤ ‖1 - κ / 2‖ := by
    have := norm_sub_norm_le (1 : ℂ) (κ / 2)
    rw [norm_one, norm_div, Complex.norm_ofNat] at this
    linarith
  have hne : (1 - κ / 2) ≠ 0 := norm_pos_iff.mp (by linarith)
  have hden : B (h u) + (u - h u) * deriv B (h u) ≠ 0 := by
    rw [d1]; exact mul_ne_zero hBv hne
  refine ⟨hden, ?_⟩
  have hW := (hode _ hv).2.2
  have hid : cnf_finite A B h u - crs_transition μ ν (h u) =
      -(u - h u) / (B (h u) * (B (h u) + (u - h u) * deriv B (h u))) := by
    rw [hFv]
    unfold cnf_finite
    field_simp
    linear_combination (-(u - h u)) * hW
  have hBn : 0 < ‖B (h u)‖ := norm_pos_iff.mpr hBv
  have hnn : 0 < ‖1 - κ / 2‖ := by linarith
  have hk2 : ‖1 - κ / 2‖ ≤ 2 := by
    have := norm_sub_le (1 : ℂ) (κ / 2)
    rw [norm_one, norm_div, Complex.norm_ofNat] at this
    linarith
  have hdn : ‖B (h u) + (u - h u) * deriv B (h u)‖ = ‖B (h u)‖ * ‖1 - κ / 2‖ := by rw [d1, norm_mul]
  rw [hid, norm_div, norm_neg, norm_mul, hdn, one_div, norm_inv, norm_pow, hdn,
    div_le_iff₀ (by positivity)]
  have he : 2 * (‖u - h u‖ * ((‖B (h u)‖ * ‖1 - κ / 2‖) ^ 2)⁻¹) *
      (‖B (h u)‖ * (‖B (h u)‖ * ‖1 - κ / 2‖)) = ‖u - h u‖ * (2 / ‖1 - κ / 2‖) := by
    field_simp
  rw [he]
  have h2 : 1 ≤ 2 / ‖1 - κ / 2‖ := by rw [le_div_iff₀ hnn]; linarith
  nlinarith [norm_nonneg (u - h u)]

/-- Approaching a boundary point of `Ω` from `Ω*` refines the reflection-boundary filter. -/
theorem qd_nhds_le {μ : LinfStar} (hμ : μ ∈ LinfStarBall) {h : ℂ → ℂ}
    (hh : IsQCReflection (fsans μ '' unitDisc) (gsans μ '' unitDiscExterior) h)
    {z : ℂ} (hz : z ∈ frontier (fsans μ '' unitDisc)) :
    𝓝[gsans μ '' unitDiscExterior] z ≤ crb_reflectionBoundary μ h := by
  have hf := S2C.s2c_conf_f hμ
  have hΩo : IsOpen (fsans μ '' unitDisc) := hf.isOpen isOpen_ball
  have hzΩ : z ∉ fsans μ '' unitDisc := fun h' => by
    have := hz.2; rw [hΩo.interior_eq] at this; exact this h'
  have hht := hh.2.2 z hz
  have hEv : ∀ᶠ u in 𝓝[gsans μ '' unitDiscExterior] z, u ∈ gsans μ '' unitDiscExterior :=
    self_mem_nhdsWithin
  have hD : ∀ᶠ u in 𝓝[gsans μ '' unitDiscExterior] z,
      Function.invFunOn (fsans μ) unitDisc (h u) ∈ unitDisc ∧
        fsans μ (Function.invFunOn (fsans μ) unitDisc (h u)) = h u := by
    filter_upwards [hEv] with u hu
    exact ⟨Function.invFunOn_mem (hh.2.1 hu), Function.invFunOn_eq (hh.2.1 hu)⟩
  have hnorm : Tendsto (fun u => ‖Function.invFunOn (fsans μ) unitDisc (h u)‖)
      (𝓝[gsans μ '' unitDiscExterior] z) (𝓝 1) := by
    rw [tendsto_order]
    refine ⟨fun b hb => ?_, fun b hb => ?_⟩
    · set ρ := max b 0 with hρ
      have hρ1 : ρ < 1 := max_lt hb one_pos
      have hKs : closedBall (0 : ℂ) ρ ⊆ unitDisc := closedBall_subset_ball hρ1
      have hKc : IsCompact (fsans μ '' closedBall (0 : ℂ) ρ) :=
        (isCompact_closedBall 0 ρ).image_of_continuousOn (hf.1.continuousOn.mono hKs)
      have hzK : z ∉ fsans μ '' closedBall (0 : ℂ) ρ := fun hk => hzΩ (image_mono hKs hk)
      have hev := hht (hKc.isClosed.isOpen_compl.mem_nhds hzK)
      filter_upwards [hev, hD] with u hu hu2
      by_contra hcon
      push_neg at hcon
      apply hu
      refine ⟨_, mem_closedBall_zero_iff.mpr (hcon.trans (le_max_left _ _)), hu2.2⟩
    · filter_upwards [hD] with u hu
      exact (mem_ball_zero_iff.mp hu.1).trans hb
  have ht : Tendsto (fun u : ℂ => u) (𝓝[gsans μ '' unitDiscExterior] z) (crb_reflectionBoundary μ h) := by
    unfold crb_reflectionBoundary crb_diskBoundary
    refine tendsto_inf.mpr ⟨tendsto_comap_iff.mpr (tendsto_inf.mpr ⟨tendsto_comap_iff.mpr hnorm, ?_⟩),
      tendsto_principal.mpr hEv⟩
    exact tendsto_principal.mpr (hD.mono fun u hu => hu.1)
  exact tendsto_id'.mp ht

/-- **(R1) Exterior boundary trace** of the Ahlfors map: `N → H(z)` from `Ω*` at every `z ∈ ∂Ω`. -/
theorem qd_trace {μ ν : LinfStar} (hμ : μ ∈ LinfStarBall) (hν : ν ∈ LinfStarBall)
    (hP : AInf.toFun (bersPhi ν - bersPhi μ) ∈ A2fun unitDisc)
    {h : ℂ → ℂ} {K C₀ : ℝ} {p : ℂ} (hp : p ∈ fsans μ '' unitDisc)
    (hC1 : ContDiffOn ℝ 1 h (gsans μ '' unitDiscExterior))
    (hpl : IsPlanarQCReflection (gsans μ '' unitDiscExterior) ((fsans μ '' unitDisc) \ {p}) h K)
    (hh : IsQCReflection (fsans μ '' unitDisc) (gsans μ '' unitDiscExterior) h)
    (hinf : Tendsto h (cocompact ℂ ⊓ 𝓟 (gsans μ '' unitDiscExterior)) (𝓝 p))
    (hb1 : ∀ u ∈ gsans μ '' unitDiscExterior, ‖u - h u‖ ^ 2 * ‖fderiv ℝ h u‖ *
      poincareDensity (fsans μ '' unitDisc) (h u) ^ 2 ≤ C₀)
    (hb2 : ∀ u ∈ gsans μ '' unitDiscExterior, ‖u - h u‖ ^ 2 * ‖dzbar h u‖ *
      poincareDensity (fsans μ '' unitDisc) (h u) ^ 2 ≤ C₀)
    {A B : ℂ → ℂ} (hA : DifferentiableOn ℂ A (fsans μ '' unitDisc))
    (hB : DifferentiableOn ℂ B (fsans μ '' unitDisc))
    (hode : ∀ z ∈ fsans μ '' unitDisc,
      deriv (deriv A) z + schwarzianHol (crs_transition μ ν) z / 2 * A z = 0 ∧
      deriv (deriv B) z + schwarzianHol (crs_transition μ ν) z / 2 * B z = 0 ∧
      A z * deriv B z - B z * deriv A z = 1)
    (hrat : ∀ z ∈ fsans μ '' unitDisc, (crs_transition μ ν z : ExtPlane) = t203_ratio (A z) (B z))
    (H : ℂ ≃ₜ ℂ) (hH : ∀ w ∈ unitDisc, H (fsans μ w) = fsans ν w)
    {z : ℂ} (hz : z ∈ frontier (fsans μ '' unitDisc)) :
    Tendsto (cnf_finite A B h) (𝓝[gsans μ '' unitDiscExterior] z) (𝓝 (H z)) := by
  haveI : (crb_reflectionBoundary μ h).IsCountablyGenerated := by
    unfold crb_reflectionBoundary crb_diskBoundary
    infer_instance
  have hle := qd_nhds_le hμ hh hz
  obtain ⟨C, hC⟩ := qd_contact hμ hν hP hp hC1 hpl hh hinf hb1 hb2 hA hB hode hrat
  have hpre : Tendsto (fun u => (u - h u) * deriv (deriv (crs_transition μ ν)) (h u) /
      deriv (crs_transition μ ν) (h u)) (crb_reflectionBoundary μ h) (𝓝 0) :=
    tendsto_iff_seq_tendsto.mpr fun u hu => qd_prerel_seq hμ hν hP hp hh hinf hu
  have htF : Tendsto (fun u => ‖u - h u‖ * ‖deriv (crs_transition μ ν) (h u)‖)
      (crb_reflectionBoundary μ h) (𝓝 0) :=
    tendsto_iff_seq_tendsto.mpr fun u hu => qd_tF_seq hμ hν hP hp hh hinf hu
  have hE : ∀ᶠ u in crb_reflectionBoundary μ h, u ∈ gsans μ '' unitDiscExterior :=
    mem_inf_of_right (mem_principal_self _)
  -- `N - F ∘ h → 0` along the filter
  have herr : Tendsto (fun u => cnf_finite A B h u - crs_transition μ ν (h u))
      (crb_reflectionBoundary μ h) (𝓝 0) := by
    apply squeeze_zero_norm' _ ((htF.const_mul (4 * |C|)).trans (by rw [mul_zero]))
    filter_upwards [hC, hE, hpre.eventually (Metric.ball_mem_nhds 0 one_pos)] with u hu hu2 hκ
    rw [dist_zero_right] at hκ
    have hv := hh.2.1 hu2
    obtain ⟨-, d2⟩ := qd_den_formula hμ hA hB hode hrat hv (u - h u)
    set κ := (u - h u) * deriv (deriv (crs_transition μ ν)) (h u) / deriv (crs_transition μ ν) (h u)
    have h1κ : (1 / 2 : ℝ) ≤ ‖1 - κ / 2‖ := by
      have := norm_sub_norm_le (1 : ℂ) (κ / 2)
      rw [norm_one, norm_div, Complex.norm_ofNat] at this
      linarith
    have hinv : ‖1 / (B (h u) + (u - h u) * deriv B (h u)) ^ 2‖ ≤
        4 * ‖deriv (crs_transition μ ν) (h u)‖ := by
      have := congrArg norm d2
      rw [norm_neg] at this
      rw [this, norm_div, norm_pow, div_le_iff₀ (by positivity)]
      have hsq : (1 / 4 : ℝ) ≤ ‖1 - κ / 2‖ ^ 2 := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_left hsq (norm_nonneg (deriv (crs_transition μ ν) (h u)))]
    calc ‖cnf_finite A B h u - crs_transition μ ν (h u)‖
        ≤ C * (‖u - h u‖ * ‖1 / (B (h u) + (u - h u) * deriv B (h u)) ^ 2‖) := hu.2
      _ ≤ |C| * (‖u - h u‖ * (4 * ‖deriv (crs_transition μ ν) (h u)‖)) := by
          exact mul_le_mul (le_abs_self C) (mul_le_mul_of_nonneg_left hinv (norm_nonneg (u - h u)))
            (by positivity) (abs_nonneg C)
      _ = 4 * |C| * (‖u - h u‖ * ‖deriv (crs_transition μ ν) (h u)‖) := by ring
  -- `F ∘ h = H ∘ h → H z`
  have hFH : ∀ u ∈ gsans μ '' unitDiscExterior, crs_transition μ ν (h u) = H (h u) := by
    intro u hu
    obtain ⟨w, hw, hwe⟩ := hh.2.1 hu
    have hf := S2C.s2c_conf_f hμ
    rw [← hwe, hH w hw]
    change fsans ν (Function.invFunOn (fsans μ) unitDisc (fsans μ w)) = fsans ν w
    rw [hf.2.1 (Function.invFunOn_mem ⟨w, hw, rfl⟩) hw (Function.invFunOn_eq ⟨w, hw, rfl⟩)]
  have hHh : Tendsto (fun u => H (h u)) (𝓝[gsans μ '' unitDiscExterior] z) (𝓝 (H z)) :=
    (H.continuous.tendsto z).comp (hh.2.2 z hz)
  have hsum := (herr.mono_left hle).add hHh
  rw [zero_add] at hsum
  refine hsum.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with u hu
  rw [hFH u hu]
  ring

/-- **(NF1)** Subsequential blow-up limits of the two synchronized welding families exist, are normalized q.c. planes,
and coincide (holomorphically) on the half-plane `Π = {Re > -2}`. -/
theorem qd_nf_limits {μ ν : LinfStar} (hμ : μ ∈ LinfStarBall) (hν : ν ∈ LinfStarBall)
    (hP : AInf.toFun (bersPhi ν - bersPhi μ) ∈ A2fun unitDisc)
    (eμ eν : ℂ ≃ₜ ℂ) {K L : ℝ} (hK : IsKQC eμ univ K) (hL : IsKQC eν univ L)
    (heμ : EqOn eμ (fsans μ) unitDisc) (heν : EqOn eν (fsans ν) unitDisc)
    {a : ℕ → ℂ} (ha : ∀ n, 0 < ‖a n‖ ∧ ‖a n‖ < 1)
    (halim : Tendsto (fun n => ‖a n‖) atTop (𝓝 1)) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧ ∃ f g : ℂ → ℂ,
      IsKQCNormalizedPlane f K ∧ IsKQCNormalizedPlane g L ∧
      TendstoLocallyUniformly (fun n => cbl_normalized eμ (a (σ n))) f atTop ∧
      TendstoLocallyUniformly (fun n => cbl_normalized eν (a (σ n))) g atTop ∧
      EqOn f g {t : ℂ | -2 < t.re} ∧ DifferentiableOn ℂ f {t : ℂ | -2 < t.re} := by
  let U : Set ℂ := {t : ℂ | -2 < t.re}
  have hU : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have h0 : (0 : ℂ) ∈ U := by norm_num [U]
  have h1 : (1 : ℂ) ∈ U := by norm_num [U]
  have hUc : IsConnected U := (convex_halfSpace_re_gt (-2)).isConnected ⟨0, h0⟩
  have hUb : ¬ Bornology.IsBounded U := by
    intro hb
    obtain ⟨R, hR⟩ := isBounded_iff_forall_norm_le.mp hb
    have hx : ((|R| + 1 : ℝ) : ℂ) ∈ U := by
      change -2 < |R| + 1
      linarith [abs_nonneg R]
    have hh := hR _ hx
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity : 0 < |R| + 1)] at hh
    linarith [le_abs_self R]
  have hlocal : ∀ z ∈ U, ∃ r > 0, ball z r ⊆ U ∧ ∀ᶠ n in atTop,
      DifferentiableOn ℂ (cbl_normalized eμ (a n)) (ball z r) ∧
        DifferentiableOn ℂ (cbl_normalized eν (a n)) (ball z r) := by
    intro z hz
    obtain ⟨r, hr, hb⟩ := Metric.isOpen_iff.mp hU z hz
    have hC : closedBall z (r/2) ⊆ U := by
      intro w hw
      exact hb (mem_ball.mpr ((mem_closedBall.mp hw).trans_lt (half_lt_self hr)))
    refine ⟨r/2, half_pos hr, ball_subset_closedBall.trans hC, ?_⟩
    filter_upwards [cbs_eventually_mapsTo ha halim (isCompact_closedBall z (r/2)) hC] with n hn
    exact ⟨(cbs_normalized_holomorphic hμ eμ heμ (ha n).1 (ha n).2).mono
      (fun w hw => hn (ball_subset_closedBall hw)),
      (cbs_normalized_holomorphic hν eν heν (ha n).1 (ha n).2).mono
      (fun w hw => hn (ball_subset_closedBall hw))⟩
  have hS : ∀ z ∈ U, Tendsto (fun n => schwarzianHol (cbl_normalized eν (a n)) z -
      schwarzianHol (cbl_normalized eμ (a n)) z) atTop (𝓝 0) := by
    intro z hz
    have ht := (cbs_scaled_tendsto_locallyUniformlyOn ha halim hP).tendsto_at hz
    apply ht.congr'
    filter_upwards [cbs_eventually_mapsTo ha halim (isCompact_singleton (x := z))
      (singleton_subset_iff.mpr hz)] with n hn
    exact (cbs_schwarzian_difference hμ hν eμ eν heμ heν (ha n).1 (ha n).2
      (hn (mem_singleton z))).symm
  obtain ⟨ms, hms, f, g, hf, hg, hFl, hGl⟩ :=
    crbl_common_subseq (fun n => cbl_normalized_plane eμ hK (ha n).1 (ha n).2)
      (fun n => cbl_normalized_plane eν hL (ha n).1 (ha n).2)
  have hι : Tendsto ms atTop atTop := hms.tendsto_atTop
  have hlocalF : ∀ z ∈ U, ∃ r > 0, ball z r ⊆ U ∧
      ∀ᶠ n in atTop, DifferentiableOn ℂ (cbl_normalized eμ (a (ms n))) (ball z r) := by
    intro z hz
    obtain ⟨r, hr, hs, hh⟩ := hlocal z hz
    exact ⟨r, hr, hs, hι.eventually (hh.mono (fun n hn => hn.1))⟩
  have hlocalG : ∀ z ∈ U, ∃ r > 0, ball z r ⊆ U ∧
      ∀ᶠ n in atTop, DifferentiableOn ℂ (cbl_normalized eν (a (ms n))) (ball z r) := by
    intro z hz
    obtain ⟨r, hr, hs, hh⟩ := hlocal z hz
    exact ⟨r, hr, hs, hι.eventually (hh.mono (fun n hn => hn.2))⟩
  obtain ⟨hfd, hFj⟩ := crbl_local_jets
    (hFl.tendstoLocallyUniformlyOn.mono (subset_univ U)) hlocalF
  obtain ⟨hgd, hGj⟩ := crbl_local_jets
    (hGl.tendstoLocallyUniformlyOn.mono (subset_univ U)) hlocalG
  have hfi : InjOn f U := hf.1.2.2.1.2.1.mono (subset_univ U)
  have hgi : InjOn g U := hg.1.2.2.1.2.1.mono (subset_univ U)
  have hSeq : ∀ z ∈ U, schwarzianHol f z = schwarzianHol g z := by
    intro z hz
    obtain ⟨r, hr, hs, hh⟩ := hlocal z hz
    have hFa : ∀ᶠ n in atTop, AnalyticAt ℂ (cbl_normalized eμ (a (ms n))) z :=
      hι.eventually (hh.mono (fun n hn => hn.1.analyticOnNhd isOpen_ball z (mem_ball_self hr)))
    have hGa : ∀ᶠ n in atTop, AnalyticAt ℂ (cbl_normalized eν (a (ms n))) z :=
      hι.eventually (hh.mono (fun n hn => hn.2.analyticOnNhd isOpen_ball z (mem_ball_self hr)))
    have hSF := crbl_schwarzian_tendsto hFa (hfd.analyticOnNhd hU z hz)
      (hFj z hz).1 (hFj z hz).2.1 (hFj z hz).2.2 (deriv_ne_zero_of_injOn hU hfd hfi hz)
    have hSG := crbl_schwarzian_tendsto hGa (hgd.analyticOnNhd hU z hz)
      (hGj z hz).1 (hGj z hz).2.1 (hGj z hz).2.2 (deriv_ne_zero_of_injOn hU hgd hgi hz)
    exact (sub_eq_zero.mp (tendsto_nhds_unique (hSG.sub hSF) ((hS z hz).comp hι))).symm
  exact ⟨ms, hms, f, g, hf, hg, hFl, hGl, crbl_rigidity hU hUc hUb h0 h1 hf hg hfd hgd hSeq, hfd⟩

/-- **(B1, local)** Eventually along the reflection-boundary filter, the Ahlfors map is injective on the ball
`u + (u - h u)·B̄(0, r)` (mean value + `qd_blowup` with `ε = 1/2`). -/
theorem qd_ball_inj {μ ν : LinfStar} (hμ : μ ∈ LinfStarBall) (hν : ν ∈ LinfStarBall)
    (hP : AInf.toFun (bersPhi ν - bersPhi μ) ∈ A2fun unitDisc)
    {h : ℂ → ℂ} {K C₀ : ℝ} {p : ℂ} (hp : p ∈ fsans μ '' unitDisc)
    (hC1 : ContDiffOn ℝ 1 h (gsans μ '' unitDiscExterior))
    (hpl : IsPlanarQCReflection (gsans μ '' unitDiscExterior) ((fsans μ '' unitDisc) \ {p}) h K)
    (hh : IsQCReflection (fsans μ '' unitDisc) (gsans μ '' unitDiscExterior) h)
    (hinf : Tendsto h (cocompact ℂ ⊓ 𝓟 (gsans μ '' unitDiscExterior)) (𝓝 p))
    (hb1 : ∀ u ∈ gsans μ '' unitDiscExterior, ‖u - h u‖ ^ 2 * ‖fderiv ℝ h u‖ *
      poincareDensity (fsans μ '' unitDisc) (h u) ^ 2 ≤ C₀)
    (hb2 : ∀ u ∈ gsans μ '' unitDiscExterior, ‖u - h u‖ ^ 2 * ‖dzbar h u‖ *
      poincareDensity (fsans μ '' unitDisc) (h u) ^ 2 ≤ C₀)
    {A B : ℂ → ℂ} (hA : DifferentiableOn ℂ A (fsans μ '' unitDisc))
    (hB : DifferentiableOn ℂ B (fsans μ '' unitDisc))
    (hode : ∀ z ∈ fsans μ '' unitDisc,
      deriv (deriv A) z + schwarzianHol (crs_transition μ ν) z / 2 * A z = 0 ∧
      deriv (deriv B) z + schwarzianHol (crs_transition μ ν) z / 2 * B z = 0 ∧
      A z * deriv B z - B z * deriv A z = 1)
    (hrat : ∀ z ∈ fsans μ '' unitDisc, (crs_transition μ ν z : ExtPlane) = t203_ratio (A z) (B z)) :
    ∃ r : ℝ, 0 < r ∧ ∀ᶠ u in crb_reflectionBoundary μ h, ∀ y ∈ closedBall u (r * ‖u - h u‖),
      ∀ y' ∈ closedBall u (r * ‖u - h u‖), cnf_finite A B h y = cnf_finite A B h y' → y = y' := by
  obtain ⟨r, hr, hev⟩ := qd_blowup hμ hν hP hp hC1 hpl hh hinf hb1 hb2 hA hB hode hrat
  refine ⟨r, hr, ?_⟩
  filter_upwards [hev (1 / 2) (by norm_num)] with u hu y hy y' hy' hNe
  obtain ⟨hdu, hball⟩ := hu
  set lamu : ℂ := -(1 / (B (h u) + (u - h u) * deriv B (h u)) ^ 2) with hlam
  have hlam0 : lamu ≠ 0 := by
    rw [hlam]; simp [hdu]
  -- every point of the ball is `u + (u - h u) Z` with `|Z| ≤ r`
  have hZ : ∀ x ∈ closedBall u (r * ‖u - h u‖), ∃ Z ∈ closedBall (0 : ℂ) r, x = u + (u - h u) * Z := by
    intro x hx
    by_cases ht : u - h u = 0
    · refine ⟨0, mem_closedBall_self hr.le, ?_⟩
      have := mem_closedBall.mp hx
      rw [ht, norm_zero, mul_zero, dist_le_zero] at this
      rw [this, ht, zero_mul, add_zero]
    · refine ⟨(x - u) / (u - h u), ?_, by field_simp; ring⟩
      rw [mem_closedBall_zero_iff, norm_div, div_le_iff₀ (norm_pos_iff.mpr ht)]
      have := mem_closedBall.mp hx
      rwa [dist_eq_norm] at this
  -- `N - λ·id` is `‖λ‖/2`-Lipschitz on the ball
  have hdiff : ∀ x ∈ closedBall u (r * ‖u - h u‖), DifferentiableAt ℝ (cnf_finite A B h) x ∧
      ‖fderiv ℝ (cnf_finite A B h) x - lamu • (1 : ℂ →L[ℝ] ℂ)‖ ≤ 1 / 2 * ‖1 / (B (h u) +
        (u - h u) * deriv B (h u)) ^ 2‖ := by
    intro x hx
    obtain ⟨Z, hZr, rfl⟩ := hZ x hx
    obtain ⟨hxE, hxd, hxb⟩ := hball Z hZr
    refine ⟨?_, hxb⟩
    by_contra hnd
    rw [fderiv_zero_of_not_differentiableAt hnd, zero_sub, norm_neg, norm_smul, norm_one, mul_one,
      hlam, norm_neg] at hxb
    have : 0 < ‖1 / (B (h u) + (u - h u) * deriv B (h u)) ^ 2‖ := by simp [hdu]
    linarith
  set L : ℂ →L[ℝ] ℂ := lamu • (1 : ℂ →L[ℝ] ℂ) with hLdef
  have hLx : ∀ x : ℂ, L x = lamu * x := fun x => by simp [hLdef]
  have hL : ‖cnf_finite A B h y' - cnf_finite A B h y - lamu * (y' - y)‖ ≤
      1 / 2 * ‖1 / (B (h u) + (u - h u) * deriv B (h u)) ^ 2‖ * ‖y' - y‖ := by
    have hconv := convex_closedBall u (r * ‖u - h u‖)
    have := hconv.norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℝ)
      (f := fun x => cnf_finite A B h x - L x)
      (fun x hx => (hdiff x hx).1.sub L.differentiableAt)
      (fun x hx => by
        rw [((hdiff x hx).1.hasFDerivAt.fun_sub L.hasFDerivAt).fderiv]
        exact (hdiff x hx).2) hy hy'
    rw [hLx, hLx] at this
    calc ‖cnf_finite A B h y' - cnf_finite A B h y - lamu * (y' - y)‖
        = ‖cnf_finite A B h y' - lamu * y' - (cnf_finite A B h y - lamu * y)‖ := by ring_nf
      _ ≤ _ := this
  rw [hNe, sub_self, zero_sub, norm_neg, norm_mul] at hL
  have hlamn : ‖lamu‖ = ‖1 / (B (h u) + (u - h u) * deriv B (h u)) ^ 2‖ := by rw [hlam, norm_neg]
  rw [hlamn] at hL
  have hpos : 0 < ‖1 / (B (h u) + (u - h u) * deriv B (h u)) ^ 2‖ := by simp [hdu]
  have : ‖y' - y‖ ≤ 0 := by nlinarith [norm_nonneg (y' - y)]
  exact (sub_eq_zero.mp (norm_le_zero_iff.mp this)).symm

/-- Value and derivative of a normalized blow-up at an interior source point. -/
theorem qd_nderiv_at {μ : LinfStar} (hμ : μ ∈ LinfStarBall) (e : ℂ ≃ₜ ℂ) (he : EqOn e (fsans μ) unitDisc)
    {a : ℂ} (ha0 : 0 < ‖a‖) (ha1 : ‖a‖ < 1) {T : ℂ} (hT : cbl_source a T ∈ unitDisc) :
    cbl_normalized e a T = (fsans μ (cbl_source a T) - e a) / (e (cbl_source a 1) - e a) ∧
      HasDerivAt (cbl_normalized e a)
        (cbl_scale a * deriv (fsans μ) (cbl_source a T) / (e (cbl_source a 1) - e a)) T := by
  have hf := S2C.s2c_conf_f hμ
  set b := e (cbl_source a 1) - e a with hb
  have hsrc : Continuous (cbl_source a) := by unfold cbl_source; fun_prop
  have hopen : IsOpen (cbl_source a ⁻¹' unitDisc) := isOpen_ball.preimage hsrc
  have hev : cbl_normalized e a =ᶠ[𝓝 T] fun t => (fsans μ (cbl_source a t) - e a) / b := by
    filter_upwards [hopen.mem_nhds hT] with t ht
    simp only [cbl_normalized, he ht, hb]
  refine ⟨by simp only [cbl_normalized, he hT, hb], ?_⟩
  have hs : HasDerivAt (cbl_source a) (cbl_scale a) T := by
    have := ((hasDerivAt_id T).const_mul (cbl_scale a)).const_add a
    simp only [mul_one] at this
    exact this
  have hfd : HasDerivAt (fsans μ) (deriv (fsans μ) (cbl_source a T)) (cbl_source a T) :=
    (hf.1.differentiableAt (isOpen_ball.mem_nhds hT)).hasDerivAt
  have hc := ((hfd.comp T hs).sub_const (e a)).div_const b
  refine (hc.congr_of_eventuallyEq hev).congr_deriv ?_
  ring

/-- **Frame identity.** In the blow-up frame at `a`, the Ahlfors map is
`W_ν(N y) = g_ν(T) + (g_ν'(T)/g_μ'(T)) (Z_μ(y) - g_μ(T)) / (1 - κ_y/2)`, with `T` the frame coordinate of `h y`. -/
theorem qd_frame_id {μ ν : LinfStar} (hμ : μ ∈ LinfStarBall) (hν : ν ∈ LinfStarBall)
    {A B : ℂ → ℂ} (hA : DifferentiableOn ℂ A (fsans μ '' unitDisc))
    (hB : DifferentiableOn ℂ B (fsans μ '' unitDisc))
    (hode : ∀ z ∈ fsans μ '' unitDisc,
      deriv (deriv A) z + schwarzianHol (crs_transition μ ν) z / 2 * A z = 0 ∧
      deriv (deriv B) z + schwarzianHol (crs_transition μ ν) z / 2 * B z = 0 ∧
      A z * deriv B z - B z * deriv A z = 1)
    (hrat : ∀ z ∈ fsans μ '' unitDisc, (crs_transition μ ν z : ExtPlane) = t203_ratio (A z) (B z))
    {h : ℂ → ℂ} (hh : IsQCReflection (fsans μ '' unitDisc) (gsans μ '' unitDiscExterior) h)
    (eμ eν : ℂ ≃ₜ ℂ) (heμ : EqOn eμ (fsans μ) unitDisc) (heν : EqOn eν (fsans ν) unitDisc)
    {a : ℂ} (ha0 : 0 < ‖a‖) (ha1 : ‖a‖ < 1) {y : ℂ} (hy : y ∈ gsans μ '' unitDiscExterior)
    (hd : B (h y) + (y - h y) * deriv B (h y) ≠ 0) :
    (cnf_finite A B h y - eν a) / (eν (cbl_source a 1) - eν a) =
      cbl_normalized eν a ((Function.invFunOn (fsans μ) unitDisc (h y) - a) / cbl_scale a) +
        deriv (cbl_normalized eν a) ((Function.invFunOn (fsans μ) unitDisc (h y) - a) / cbl_scale a) /
          deriv (cbl_normalized eμ a) ((Function.invFunOn (fsans μ) unitDisc (h y) - a) / cbl_scale a) *
          ((y - eμ a) / (eμ (cbl_source a 1) - eμ a) -
            cbl_normalized eμ a ((Function.invFunOn (fsans μ) unitDisc (h y) - a) / cbl_scale a)) /
          (1 - (y - h y) * deriv (deriv (crs_transition μ ν)) (h y) /
            deriv (crs_transition μ ν) (h y) / 2) := by
  have hf := S2C.s2c_conf_f hμ
  have hfν := S2C.s2c_conf_f hν
  have hΩ : IsOpen (fsans μ '' unitDisc) := hf.isOpen isOpen_ball
  have hc0 := cbl_scale_ne_zero ha0 ha1
  have haD : a ∈ unitDisc := mem_ball_zero_iff.mpr ha1
  set s := Function.invFunOn (fsans μ) unitDisc (h y) with hs
  have hsD : s ∈ unitDisc := Function.invFunOn_mem (hh.2.1 hy)
  have hfs : fsans μ s = h y := Function.invFunOn_eq (hh.2.1 hy)
  set T := (s - a) / cbl_scale a with hT
  have hsrc : cbl_source a T = s := by
    simp only [cbl_source, hT]; field_simp; ring
  obtain ⟨hgμ, hgμ'⟩ := qd_nderiv_at hμ eμ heμ ha0 ha1 (hsrc ▸ hsD)
  obtain ⟨hgν, hgν'⟩ := qd_nderiv_at hν eν heν ha0 ha1 (hsrc ▸ hsD)
  rw [hsrc] at hgμ hgμ' hgν hgν'
  rw [hgμ'.deriv, hgν'.deriv, hgμ, hgν]
  have hbμ : eμ (cbl_source a 1) - eμ a ≠ 0 :=
    sub_ne_zero.mpr fun h' => cbl_source_one_ne ha0 ha1 (eμ.injective h')
  have hbν : eν (cbl_source a 1) - eν a ≠ 0 :=
    sub_ne_zero.mpr fun h' => cbl_source_one_ne ha0 ha1 (eν.injective h')
  -- the relative map and its derivative at `h y = fsans μ s`
  have hFs : crs_transition μ ν (h y) = fsans ν s := by
    rw [← hfs]
    change fsans ν (Function.invFunOn (fsans μ) unitDisc (fsans μ s)) = fsans ν s
    rw [hf.2.1 (Function.invFunOn_mem ⟨s, hsD, rfl⟩) hsD (Function.invFunOn_eq ⟨s, hsD, rfl⟩)]
  have hFc := crs_conformal hμ hν
  have hfμd : deriv (fsans μ) s ≠ 0 := deriv_ne_zero_of_injOn isOpen_ball hf.1 hf.2.1 hsD
  have hFd : deriv (crs_transition μ ν) (h y) * deriv (fsans μ) s = deriv (fsans ν) s := by
    have hFat : HasDerivAt (crs_transition μ ν) (deriv (crs_transition μ ν) (fsans μ s)) (fsans μ s) :=
      (hFc.1.differentiableAt (hΩ.mem_nhds ⟨s, hsD, rfl⟩)).hasDerivAt
    have hcomp := hFat.comp s (hf.1.differentiableAt (isOpen_ball.mem_nhds hsD)).hasDerivAt
    have heq : crs_transition μ ν ∘ fsans μ =ᶠ[𝓝 s] fsans ν := by
      filter_upwards [isOpen_ball.mem_nhds hsD] with w hw
      change fsans ν (Function.invFunOn (fsans μ) unitDisc (fsans μ w)) = fsans ν w
      rw [hf.2.1 (Function.invFunOn_mem ⟨w, hw, rfl⟩) hw (Function.invFunOn_eq ⟨w, hw, rfl⟩)]
    rw [← hfs, ← heq.deriv_eq, hcomp.deriv]
  -- the contact identity `N y - F(h y) = F'(h y) t / (1 - κ/2)`
  have hv := hh.2.1 hy
  obtain ⟨hBv, hFq, hF1, -⟩ := qd_FB hμ hA hB hode hrat hv
  obtain ⟨d1, -⟩ := qd_den_formula hμ hA hB hode hrat hv (y - h y)
  set κ := (y - h y) * deriv (deriv (crs_transition μ ν)) (h y) / deriv (crs_transition μ ν) (h y)
    with hκ
  have hne : 1 - κ / 2 ≠ 0 := by
    intro h0; apply hd; rw [d1, h0, mul_zero]
  have hW := (hode _ hv).2.2
  have hNb : cnf_finite A B h y - crs_transition μ ν (h y) =
      -(y - h y) / (B (h y) * (B (h y) + (y - h y) * deriv B (h y))) := by
    rw [hFq]; unfold cnf_finite; field_simp; linear_combination (-(y - h y)) * hW
  have hN : cnf_finite A B h y = crs_transition μ ν (h y) +
      deriv (crs_transition μ ν) (h y) * (y - h y) / (1 - κ / 2) := by
    have h2 : cnf_finite A B h y - crs_transition μ ν (h y) =
        deriv (crs_transition μ ν) (h y) * (y - h y) / (1 - κ / 2) := by
      rw [hNb, d1, hF1]; field_simp
    linear_combination h2
  rw [hN, hFs, heμ haD, heν haD, ← hfs]
  have hF' : deriv (crs_transition μ ν) (fsans μ s) = deriv (fsans ν) s / deriv (fsans μ) s := by
    rw [hfs, eq_div_iff hfμd]; exact hFd
  rw [hF']
  rw [heμ haD] at hbμ
  rw [heν haD] at hbν
  field_simp
  ring

/-- Locally uniform convergence of the normalized derivatives near a point of `Π`, with the limit derivative
equal for the two families. -/
theorem qd_nderiv_conv {μ : LinfStar} (hμ : μ ∈ LinfStarBall) (e : ℂ ≃ₜ ℂ) (he : EqOn e (fsans μ) unitDisc)
    {a : ℕ → ℂ} (ha : ∀ n, 0 < ‖a n‖ ∧ ‖a n‖ < 1) (halim : Tendsto (fun n => ‖a n‖) atTop (𝓝 1))
    {f : ℂ → ℂ} (hfl : TendstoLocallyUniformly (fun n => cbl_normalized e (a n)) f atTop)
    {T : ℂ} (hT : -2 < T.re) :
    ∃ ρ > 0, ball T ρ ⊆ {t : ℂ | -2 < t.re} ∧
      TendstoLocallyUniformlyOn (fun n => deriv (cbl_normalized e (a n))) (deriv f) atTop (ball T ρ) ∧
      DifferentiableOn ℂ f (ball T ρ) := by
  have hU : IsOpen {t : ℂ | -2 < t.re} := isOpen_lt continuous_const Complex.continuous_re
  obtain ⟨r, hr, hb⟩ := Metric.isOpen_iff.mp hU T hT
  have hC : closedBall T (r/2) ⊆ {t : ℂ | -2 < t.re} := fun w hw =>
    hb (mem_ball.mpr ((mem_closedBall.mp hw).trans_lt (half_lt_self hr)))
  have hev : ∀ᶠ n in atTop, DifferentiableOn ℂ (cbl_normalized e (a n)) (ball T (r/2)) := by
    filter_upwards [cbs_eventually_mapsTo ha halim (isCompact_closedBall T (r/2)) hC] with n hn
    exact (cbs_normalized_holomorphic hμ e he (ha n).1 (ha n).2).mono
      (fun w hw => hn (ball_subset_closedBall hw))
  have hloc := hfl.tendstoLocallyUniformlyOn (s := ball T (r/2))
  refine ⟨r/2, half_pos hr, ball_subset_closedBall.trans hC, hloc.deriv hev isOpen_ball, ?_⟩
  exact hloc.differentiableOn hev isOpen_ball

/-- **(S1) The normalized Ahlfors map tends to the identity.** Along a blow-up sequence with NF1 limits, if the frame
coordinate `T_n` of `h y_n` tends to a point of `Π`, `Z_μ(y_n)` is bounded and `κ_{y_n} → 0`, then
`W_ν(N y_n) - Z_μ(y_n) → 0`. -/
theorem qd_S1 {μ ν : LinfStar} (hμ : μ ∈ LinfStarBall) (hν : ν ∈ LinfStarBall)
    {A B : ℂ → ℂ} (hA : DifferentiableOn ℂ A (fsans μ '' unitDisc))
    (hB : DifferentiableOn ℂ B (fsans μ '' unitDisc))
    (hode : ∀ z ∈ fsans μ '' unitDisc,
      deriv (deriv A) z + schwarzianHol (crs_transition μ ν) z / 2 * A z = 0 ∧
      deriv (deriv B) z + schwarzianHol (crs_transition μ ν) z / 2 * B z = 0 ∧
      A z * deriv B z - B z * deriv A z = 1)
    (hrat : ∀ z ∈ fsans μ '' unitDisc, (crs_transition μ ν z : ExtPlane) = t203_ratio (A z) (B z))
    {h : ℂ → ℂ} (hh : IsQCReflection (fsans μ '' unitDisc) (gsans μ '' unitDiscExterior) h)
    (eμ eν : ℂ ≃ₜ ℂ) (heμ : EqOn eμ (fsans μ) unitDisc) (heν : EqOn eν (fsans ν) unitDisc)
    {a : ℕ → ℂ} (ha : ∀ n, 0 < ‖a n‖ ∧ ‖a n‖ < 1) (halim : Tendsto (fun n => ‖a n‖) atTop (𝓝 1))
    {f g : ℂ → ℂ} {K L : ℝ} (hf : IsKQCNormalizedPlane f K) (hg : IsKQCNormalizedPlane g L)
    (hfl : TendstoLocallyUniformly (fun n => cbl_normalized eμ (a n)) f atTop)
    (hgl : TendstoLocallyUniformly (fun n => cbl_normalized eν (a n)) g atTop)
    (hfg : EqOn f g {t : ℂ | -2 < t.re})
    {y : ℕ → ℂ} (hy : ∀ n, y n ∈ gsans μ '' unitDiscExterior)
    (hd : ∀ n, B (h (y n)) + (y n - h (y n)) * deriv B (h (y n)) ≠ 0)
    {Tlim : ℂ} (hTlim : -2 < Tlim.re)
    (hT : Tendsto (fun n => (Function.invFunOn (fsans μ) unitDisc (h (y n)) - a n) / cbl_scale (a n))
      atTop (𝓝 Tlim))
    {M : ℝ} (hZ : ∀ n, ‖(y n - eμ (a n)) / (eμ (cbl_source (a n) 1) - eμ (a n))‖ ≤ M)
    (hκ : Tendsto (fun n => (y n - h (y n)) * deriv (deriv (crs_transition μ ν)) (h (y n)) /
      deriv (crs_transition μ ν) (h (y n))) atTop (𝓝 0)) :
    Tendsto (fun n => (cnf_finite A B h (y n) - eν (a n)) / (eν (cbl_source (a n) 1) - eν (a n)) -
      (y n - eμ (a n)) / (eμ (cbl_source (a n) 1) - eμ (a n))) atTop (𝓝 0) := by
  set T : ℕ → ℂ := fun n => (Function.invFunOn (fsans μ) unitDisc (h (y n)) - a n) / cbl_scale (a n)
  set Z : ℕ → ℂ := fun n => (y n - eμ (a n)) / (eμ (cbl_source (a n) 1) - eμ (a n))
  set κ : ℕ → ℂ := fun n => (y n - h (y n)) * deriv (deriv (crs_transition μ ν)) (h (y n)) /
      deriv (crs_transition μ ν) (h (y n))
  have hfc : Continuous f := continuousOn_univ.mp hf.1.2.2.1.1
  have hgc : Continuous g := continuousOn_univ.mp hg.1.2.2.1.1
  have hfr : ∀ n, (cnf_finite A B h (y n) - eν (a n)) / (eν (cbl_source (a n) 1) - eν (a n)) - Z n =
      (cbl_normalized eν (a n) (T n) - cbl_normalized eμ (a n) (T n)) +
        (deriv (cbl_normalized eν (a n)) (T n) / deriv (cbl_normalized eμ (a n)) (T n) / (1 - κ n / 2) - 1) *
          (Z n - cbl_normalized eμ (a n) (T n)) := by
    intro n
    rw [qd_frame_id hμ hν hA hB hode hrat hh eμ eν heμ heν (ha n).1 (ha n).2 (hy n) (hd n)]
    ring
  have hgμT : Tendsto (fun n => cbl_normalized eμ (a n) (T n)) atTop (𝓝 (f Tlim)) :=
    hfl.tendsto_comp hfc.continuousAt hT
  have hgνT : Tendsto (fun n => cbl_normalized eν (a n) (T n)) atTop (𝓝 (g Tlim)) :=
    hgl.tendsto_comp hgc.continuousAt hT
  have hfgT : f Tlim = g Tlim := hfg hTlim
  obtain ⟨ρ, hρ, hsub, hdμ, hfdiff⟩ := qd_nderiv_conv hμ eμ heμ ha halim hfl hTlim
  obtain ⟨ρ', hρ', hsub', hdν, hgdiff⟩ := qd_nderiv_conv hν eν heν ha halim hgl hTlim
  have hTw : Tendsto T atTop (𝓝[ball Tlim ρ] Tlim) :=
    tendsto_nhdsWithin_iff.mpr ⟨hT, hT.eventually (isOpen_ball.mem_nhds (mem_ball_self hρ))⟩
  have hTw' : Tendsto T atTop (𝓝[ball Tlim ρ'] Tlim) :=
    tendsto_nhdsWithin_iff.mpr ⟨hT, hT.eventually (isOpen_ball.mem_nhds (mem_ball_self hρ'))⟩
  have hdfc : ContinuousWithinAt (deriv f) (ball Tlim ρ) Tlim :=
    ((hfdiff.deriv isOpen_ball).continuousOn) Tlim (mem_ball_self hρ)
  have hdgc : ContinuousWithinAt (deriv g) (ball Tlim ρ') Tlim :=
    ((hgdiff.deriv isOpen_ball).continuousOn) Tlim (mem_ball_self hρ')
  have hdμT := hdμ.tendsto_comp hdfc (mem_ball_self hρ) hTw
  have hdνT := hdν.tendsto_comp hdgc (mem_ball_self hρ') hTw'
  have hU : IsOpen {t : ℂ | -2 < t.re} := isOpen_lt continuous_const Complex.continuous_re
  have hdeq : deriv g Tlim = deriv f Tlim :=
    (Filter.eventuallyEq_of_mem (hU.mem_nhds hTlim) (fun t ht => (hfg ht).symm)).deriv_eq
  have hfi : InjOn f (ball Tlim ρ) := hf.1.2.2.1.2.1.mono (subset_univ _)
  have hd0 : deriv f Tlim ≠ 0 := deriv_ne_zero_of_injOn isOpen_ball hfdiff hfi (mem_ball_self hρ)
  have hratio : Tendsto (fun n => deriv (cbl_normalized eν (a n)) (T n) /
      deriv (cbl_normalized eμ (a n)) (T n) / (1 - κ n / 2) - 1) atTop (𝓝 0) := by
    have h1 := (hdνT.div hdμT hd0).div ((tendsto_const_nhds.sub (hκ.div_const 2)))
      (by norm_num : (1 : ℂ) - 0 / 2 ≠ 0)
    rw [hdeq, div_self hd0, zero_div, sub_zero, div_one] at h1
    have h2 := h1.sub_const 1
    rw [sub_self] at h2
    exact h2
  have hdiffT : Tendsto (fun n => cbl_normalized eν (a n) (T n) - cbl_normalized eμ (a n) (T n)) atTop
      (𝓝 0) := by
    have := hgνT.sub hgμT
    rwa [← hfgT, sub_self] at this
  -- boundedness of `Z - g_μ(T)`
  have hbdd : ∀ᶠ n in atTop, ‖Z n - cbl_normalized eμ (a n) (T n)‖ ≤ M + ‖f Tlim‖ + 1 := by
    filter_upwards [hgμT.norm.eventually (eventually_lt_nhds (lt_add_one ‖f Tlim‖))] with n hn
    calc ‖Z n - cbl_normalized eμ (a n) (T n)‖ ≤ ‖Z n‖ + ‖cbl_normalized eμ (a n) (T n)‖ :=
          norm_sub_le _ _
      _ ≤ M + (‖f Tlim‖ + 1) := add_le_add (hZ n) hn.le
      _ = _ := by ring
  have hprod : Tendsto (fun n => (deriv (cbl_normalized eν (a n)) (T n) /
      deriv (cbl_normalized eμ (a n)) (T n) / (1 - κ n / 2) - 1) * (Z n - cbl_normalized eμ (a n) (T n)))
      atTop (𝓝 0) := by
    apply squeeze_zero_norm' _ ((hratio.norm.mul_const (M + ‖f Tlim‖ + 1)).trans (by simp))
    filter_upwards [hbdd] with n hn
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left hn (norm_nonneg _)
  have hsum := hdiffT.add hprod
  rw [add_zero] at hsum
  exact hsum.congr (fun n => (hfr n).symm)

/-- Frames along a sequence tending to the reflection-boundary filter. -/
theorem qd_frame_seq {μ : LinfStar} {h : ℂ → ℂ}
    (hh : IsQCReflection (fsans μ '' unitDisc) (gsans μ '' unitDiscExterior) h)
    {u : ℕ → ℂ} (hu : Tendsto u atTop (crb_reflectionBoundary μ h)) :
    ∃ α : ℕ → ℂ, (∀ n, 0 < ‖α n‖ ∧ ‖α n‖ < 1) ∧ Tendsto (fun n => ‖α n‖) atTop (𝓝 1) ∧
      ∀ᶠ n in atTop, α n = Function.invFunOn (fsans μ) unitDisc (h (u n)) ∧
        u n ∈ gsans μ '' unitDiscExterior ∧ fsans μ (α n) = h (u n) := by
  set a : ℕ → ℂ := fun n => Function.invFunOn (fsans μ) unitDisc (h (u n)) with ha_def
  have hE : ∀ᶠ n in atTop, u n ∈ gsans μ '' unitDiscExterior :=
    tendsto_principal.mp (hu.mono_right inf_le_right)
  have hA : Tendsto (fun n => ‖a n‖) atTop (𝓝 1) := by
    have h2 := tendsto_comap_iff.mp (hu.mono_right inf_le_left)
    exact tendsto_comap_iff.mp (h2.mono_right inf_le_left)
  set α : ℕ → ℂ := fun n => if 0 < ‖a n‖ ∧ ‖a n‖ < 1 then a n else (1 / 2 : ℂ) with hα
  have hα' : ∀ n, 0 < ‖α n‖ ∧ ‖α n‖ < 1 := by
    intro n
    simp only [hα]
    split_ifs with hc
    · exact hc
    · norm_num
  have heq : ∀ᶠ n in atTop, α n = a n ∧ u n ∈ gsans μ '' unitDiscExterior ∧ fsans μ (α n) = h (u n) := by
    filter_upwards [hE, hA.eventually (lt_mem_nhds one_pos)] with n hn hn0
    have hD : a n ∈ unitDisc := Function.invFunOn_mem (hh.2.1 hn)
    have h1 : α n = a n := by
      simp only [hα, if_pos (And.intro hn0 (mem_ball_zero_iff.mp hD))]
    exact ⟨h1, hn, by rw [h1]; exact Function.invFunOn_eq (hh.2.1 hn)⟩
  refine ⟨α, hα', hA.congr' (heq.mono fun n hn => by show ‖a n‖ = ‖α n‖; rw [hn.1]), heq⟩

/-- Conformal invariance and the distance bound for the target scale:
`|u - h u| |F'(h u)| ≤ 2D dist(F(h u), ∂Ω_ν)` on bounded parts of `Ω*`. -/
theorem qd_tF_dist {μ ν : LinfStar} (hμ : μ ∈ LinfStarBall) (hν : ν ∈ LinfStarBall) {h : ℂ → ℂ}
    (hh : IsQCReflection (fsans μ '' unitDisc) (gsans μ '' unitDiscExterior) h) (R : ℝ) (hR : 0 ≤ R) :
    ∃ D : ℝ, 0 < D ∧ ∀ u ∈ gsans μ '' unitDiscExterior, ‖u‖ ≤ R →
      ‖u - h u‖ * ‖deriv (crs_transition μ ν) (h u)‖ ≤
        2 * D * Metric.infDist (crs_transition μ ν (h u)) (fsans ν '' unitDisc)ᶜ := by
  obtain ⟨D, hD, hdisp⟩ := eq22_reflection_bounded_displacement hμ hh R hR
  refine ⟨D, hD, fun u hu huR => ?_⟩
  have hf := S2C.s2c_conf_f hμ
  have hfν := S2C.s2c_conf_f hν
  have hΩν : IsOpen (fsans ν '' unitDisc) := hfν.isOpen isOpen_ball
  obtain ⟨s, hs, hse⟩ := hh.2.1 hu
  have hFs : crs_transition μ ν (h u) = fsans ν s := by
    rw [← hse]
    change fsans ν (Function.invFunOn (fsans μ) unitDisc (fsans μ s)) = fsans ν s
    rw [hf.2.1 (Function.invFunOn_mem ⟨s, hs, rfl⟩) hs (Function.invFunOn_eq ⟨s, hs, rfl⟩)]
  have hFc := crs_conformal hμ hν
  have hΩ : IsOpen (fsans μ '' unitDisc) := hf.isOpen isOpen_ball
  have hfμd : deriv (fsans μ) s ≠ 0 := deriv_ne_zero_of_injOn isOpen_ball hf.1 hf.2.1 hs
  have hfνd : deriv (fsans ν) s ≠ 0 := deriv_ne_zero_of_injOn isOpen_ball hfν.1 hfν.2.1 hs
  have hFd : deriv (crs_transition μ ν) (fsans μ s) * deriv (fsans μ) s = deriv (fsans ν) s := by
    have hFat : HasDerivAt (crs_transition μ ν) (deriv (crs_transition μ ν) (fsans μ s)) (fsans μ s) :=
      (hFc.1.differentiableAt (hΩ.mem_nhds ⟨s, hs, rfl⟩)).hasDerivAt
    have hcomp := hFat.comp s (hf.1.differentiableAt (isOpen_ball.mem_nhds hs)).hasDerivAt
    have heq : crs_transition μ ν ∘ fsans μ =ᶠ[𝓝 s] fsans ν := by
      filter_upwards [isOpen_ball.mem_nhds hs] with w hw
      change fsans ν (Function.invFunOn (fsans μ) unitDisc (fsans μ w)) = fsans ν w
      rw [hf.2.1 (Function.invFunOn_mem ⟨w, hw, rfl⟩) hw (Function.invFunOn_eq ⟨w, hw, rfl⟩)]
    rw [← heq.deriv_eq, hcomp.deriv]
  have hlamμ := eq22_density_formula hf hs
  have hlamν := eq22_density_formula hfν hs
  have hgap : 0 < 1 - ‖s‖ ^ 2 := by nlinarith [mem_ball_zero_iff.mp hs, norm_nonneg s]
  have hne : ((fsans ν '' unitDisc)ᶜ).Nonempty :=
    ⟨gsans ν 2, fun h' => (qd_sides hν).1.le_bot ⟨h', ⟨2, show (1 : ℝ) < ‖(2 : ℂ)‖ by norm_num, rfl⟩⟩⟩
  have hlow := eq22_density_distance_lower hΩν (hfν.symm isOpen_ball) hne ⟨s, hs, rfl⟩
  have hdl := (hdisp u hu huR).1
  rw [← hse, hlamμ] at hdl
  rw [hlamν] at hlow
  rw [← hse, show crs_transition μ ν (fsans μ s) = fsans ν s by rw [hse]; exact hFs]
  rw [show deriv (crs_transition μ ν) (fsans μ s) = deriv (fsans ν) s / deriv (fsans μ) s by
    rw [eq_div_iff hfμd]; exact hFd, norm_div]
  have hpμ : 0 < ‖deriv (fsans μ) s‖ := norm_pos_iff.mpr hfμd
  have hpν : 0 < ‖deriv (fsans ν) s‖ := norm_pos_iff.mpr hfνd
  have hP : 0 < 1 - ‖s‖ ^ 2 := hgap
  have hx : ‖u - fsans μ s‖ * 2 ≤ D * ((1 - ‖s‖ ^ 2) * ‖deriv (fsans μ) s‖) := by
    rw [mul_div_assoc', div_le_iff₀ (by positivity)] at hdl; linarith
  have hb : (1 - ‖s‖ ^ 2) * ‖deriv (fsans ν) s‖ ≤
      4 * Metric.infDist (fsans ν s) (fsans ν '' unitDisc)ᶜ := by
    rw [show 2 * (2 / ((1 - ‖s‖ ^ 2) * ‖deriv (fsans ν) s‖)) *
        Metric.infDist (fsans ν s) (fsans ν '' unitDisc)ᶜ =
        4 * Metric.infDist (fsans ν s) (fsans ν '' unitDisc)ᶜ /
          ((1 - ‖s‖ ^ 2) * ‖deriv (fsans ν) s‖) by field_simp; ring,
      le_div_iff₀ (by positivity)] at hlow
    linarith
  rw [mul_div_assoc', div_le_iff₀ hpμ]
  have h1 := mul_le_mul_of_nonneg_right hx (norm_nonneg (deriv (fsans ν) s))
  have h2 := mul_le_mul_of_nonneg_left hb (mul_nonneg hD.le (norm_nonneg (deriv (fsans μ) s)))
  nlinarith

/-- **Radial projection to the frame boundary.** The radial projection of `cbl_source a T` to the unit circle has
frame coordinate within `2|1 + |a| + |a| Re T - (1 - |a|)|T|²/4|` of `T`. -/
theorem qd_radial {a T : ℂ} (ha0 : 0 < ‖a‖) (ha1 : ‖a‖ < 1) (hs : cbl_source a T ≠ 0) :
    ‖cbl_source a ((cbl_source a T / (‖cbl_source a T‖ : ℂ) - a) / cbl_scale a)‖ = 1 ∧
      ‖(cbl_source a T / (‖cbl_source a T‖ : ℂ) - a) / cbl_scale a - T‖ ≤
        2 * |1 + ‖a‖ + ‖a‖ * T.re - (1 - ‖a‖) * ‖T‖ ^ 2 / 4| := by
  set s := cbl_source a T with hsdef
  have hc := cbl_scale_ne_zero ha0 ha1
  have hcn := cbl_scale_norm ha0 ha1
  have hs0 : 0 < ‖s‖ := norm_pos_iff.mpr hs
  have hsn : (‖s‖ : ℂ) ≠ 0 := by exact_mod_cast hs0.ne'
  have hsrc : cbl_source a ((s / (‖s‖ : ℂ) - a) / cbl_scale a) = s / (‖s‖ : ℂ) := by
    simp only [cbl_source]; field_simp; ring
  refine ⟨?_, ?_⟩
  · rw [hsrc, norm_div, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _), div_self hs0.ne']
  · have hT : (s / (‖s‖ : ℂ) - a) / cbl_scale a - T = (s / (‖s‖ : ℂ) - s) / cbl_scale a := by
      rw [hsdef]; simp only [cbl_source]; field_simp; ring
    rw [hT, norm_div, hcn]
    have hgap := cbs_source_gap ha0 T
    rw [← hsdef] at hgap
    have hd : ‖s / (‖s‖ : ℂ) - s‖ = |1 - ‖s‖| := by
      have e : s / (‖s‖ : ℂ) - s = ((1 / ‖s‖ - 1 : ℝ) : ℂ) * s := by push_cast; field_simp
      rw [e, norm_mul, Complex.norm_real, Real.norm_eq_abs, ← abs_norm s, ← abs_mul]
      congr 1
      field_simp
      rw [abs_norm]
      ring
    rw [hd, div_le_iff₀ (by linarith)]
    have h1 : |1 - ‖s‖| ≤ |1 - ‖s‖ ^ 2| := by
      rw [show 1 - ‖s‖ ^ 2 = (1 - ‖s‖) * (1 + ‖s‖) by ring, abs_mul]
      have : 1 ≤ |1 + ‖s‖| := by rw [abs_of_pos (by positivity)]; linarith [norm_nonneg s]
      nlinarith [abs_nonneg (1 - ‖s‖)]
    rw [hgap, abs_mul, abs_of_pos (by linarith : 0 < 1 - ‖a‖)] at h1
    nlinarith [abs_nonneg (1 + ‖a‖ + ‖a‖ * T.re - (1 - ‖a‖) * ‖T‖ ^ 2 / 4)]

/-- Locally uniform convergence passes to subsequences. -/
theorem qd_tlu_sub {F : ℕ → ℂ → ℂ} {f : ℂ → ℂ} (hF : TendstoLocallyUniformly F f atTop) {τ : ℕ → ℕ}
    (hτ : Tendsto τ atTop atTop) : TendstoLocallyUniformly (fun n => F (τ n)) f atTop := by
  intro U hU x
  obtain ⟨t, ht, hev⟩ := hF U hU x
  exact ⟨t, ht, hτ.eventually hev⟩

/-- **Inverse convergence.** If normalized q.c. planes `F_n → g` locally uniformly and `F_n(S_n) → w`, then
`S_n → g⁻¹(w)`. -/
theorem qd_inv_tendsto {Fn : ℕ → ℂ → ℂ} {g : ℂ → ℂ} {K L : ℝ}
    (hF : ∀ n, IsKQCNormalizedPlane (Fn n) K) (hg : IsKQCNormalizedPlane g L)
    (hl : TendstoLocallyUniformly Fn g atTop) {S : ℕ → ℂ} {w : ℂ}
    (hw : Tendsto (fun n => Fn n (S n)) atTop (𝓝 w)) :
    ∃ S0 : ℂ, g S0 = w ∧ Tendsto S atTop (𝓝 S0) := by
  choose e he using fun n => t203_pack_homeo (hF n).1 (hF n).2.1
  obtain ⟨eg, heg⟩ := t203_pack_homeo hg.1 hg.2.1
  have hl' : TendstoLocallyUniformly (fun n => (e n : ℂ → ℂ)) (eg : ℂ → ℂ) atTop := by
    rw [heg]; simp only [he]; exact hl
  have hinv := kn6_inverse_locallyUniform hl'
  have hw' : Tendsto (fun n => e n (S n)) atTop (𝓝 w) := by simp only [he]; exact hw
  have h1 := hinv.tendsto_comp eg.symm.continuous.continuousAt hw'
  simp only [Homeomorph.symm_apply_apply] at h1
  refine ⟨eg.symm w, ?_, h1⟩
  rw [← heg]
  exact eg.apply_symm_apply w

/-- **Frame package.** Along a subsequence of any sequence tending to the reflection-boundary filter: frames, NF1
limits, the common limit `Z` of `Z_μ(u)` and `W_ν(N u)`, and the separation `ε ≤ |g(S) - Z|` on `Re S ≥ -2`. -/
theorem qd_pack {μ ν : LinfStar} (hμ : μ ∈ LinfStarBall) (hν : ν ∈ LinfStarBall)
    (hP : AInf.toFun (bersPhi ν - bersPhi μ) ∈ A2fun unitDisc)
    {h : ℂ → ℂ} {K C₀ : ℝ} {p : ℂ} (hp : p ∈ fsans μ '' unitDisc)
    (hC1 : ContDiffOn ℝ 1 h (gsans μ '' unitDiscExterior))
    (hpl : IsPlanarQCReflection (gsans μ '' unitDiscExterior) ((fsans μ '' unitDisc) \ {p}) h K)
    (hh : IsQCReflection (fsans μ '' unitDisc) (gsans μ '' unitDiscExterior) h)
    (hinf : Tendsto h (cocompact ℂ ⊓ 𝓟 (gsans μ '' unitDiscExterior)) (𝓝 p))
    (hb1 : ∀ u ∈ gsans μ '' unitDiscExterior, ‖u - h u‖ ^ 2 * ‖fderiv ℝ h u‖ *
      poincareDensity (fsans μ '' unitDisc) (h u) ^ 2 ≤ C₀)
    (hb2 : ∀ u ∈ gsans μ '' unitDiscExterior, ‖u - h u‖ ^ 2 * ‖dzbar h u‖ *
      poincareDensity (fsans μ '' unitDisc) (h u) ^ 2 ≤ C₀)
    {A B : ℂ → ℂ} (hA : DifferentiableOn ℂ A (fsans μ '' unitDisc))
    (hB : DifferentiableOn ℂ B (fsans μ '' unitDisc))
    (hode : ∀ z ∈ fsans μ '' unitDisc,
      deriv (deriv A) z + schwarzianHol (crs_transition μ ν) z / 2 * A z = 0 ∧
      deriv (deriv B) z + schwarzianHol (crs_transition μ ν) z / 2 * B z = 0 ∧
      A z * deriv B z - B z * deriv A z = 1)
    (hrat : ∀ z ∈ fsans μ '' unitDisc, (crs_transition μ ν z : ExtPlane) = t203_ratio (A z) (B z))
    (eμ eν : ℂ ≃ₜ ℂ) {Kμ Kν : ℝ} (hKμ : IsKQC eμ univ Kμ) (hKν : IsKQC eν univ Kν)
    (heμ : EqOn eμ (fsans μ) unitDisc) (heν : EqOn eν (fsans ν) unitDisc)
    {u : ℕ → ℂ} (hu : Tendsto u atTop (crb_reflectionBoundary μ h)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ a : ℕ → ℂ, (∀ n, 0 < ‖a n‖ ∧ ‖a n‖ < 1) ∧
      Tendsto (fun n => ‖a n‖) atTop (𝓝 1) ∧
      (∀ n, a n = Function.invFunOn (fsans μ) unitDisc (h (u (φ n))) ∧
        u (φ n) ∈ gsans μ '' unitDiscExterior ∧ fsans μ (a n) = h (u (φ n)) ∧
        B (h (u (φ n))) + (u (φ n) - h (u (φ n))) * deriv B (h (u (φ n))) ≠ 0) ∧
      ∃ f g : ℂ → ℂ, IsKQCNormalizedPlane f Kμ ∧ IsKQCNormalizedPlane g Kν ∧
        TendstoLocallyUniformly (fun n => cbl_normalized eμ (a n)) f atTop ∧
        TendstoLocallyUniformly (fun n => cbl_normalized eν (a n)) g atTop ∧
        EqOn f g {t : ℂ | -2 < t.re} ∧
        ∃ Z : ℂ, Tendsto (fun n => (u (φ n) - eμ (a n)) / (eμ (cbl_source (a n) 1) - eμ (a n))) atTop (𝓝 Z) ∧
          Tendsto (fun n => (cnf_finite A B h (u (φ n)) - eν (a n)) / (eν (cbl_source (a n) 1) - eν (a n)))
            atTop (𝓝 Z) ∧
          ∃ ε > 0, ∀ S : ℂ, -2 ≤ S.re → ε ≤ ‖g S - Z‖ := by
  have hf := S2C.s2c_conf_f hμ
  have hC₀ : 0 ≤ C₀ := by
    have h2 : gsans μ 2 ∈ gsans μ '' unitDiscExterior :=
      ⟨2, show (1 : ℝ) < ‖(2 : ℂ)‖ by norm_num, rfl⟩
    exact le_trans (by positivity) (hb1 _ h2)
  obtain ⟨α, hα, hαl, hαe⟩ := qd_frame_seq hh hu
  obtain ⟨Cc, hCc⟩ := qd_contact hμ hν hP hp hC1 hpl hh hinf hb1 hb2 hA hB hode hrat
  obtain ⟨R, hR0, hRu⟩ := qd_bdd_of_boundary hμ hp hinf hu
  obtain ⟨D, hD, hcbd⟩ := cbd_normalized_displacement hμ hh R hR0
  have hall : ∀ᶠ n in atTop, (α n = Function.invFunOn (fsans μ) unitDisc (h (u n)) ∧
      u n ∈ gsans μ '' unitDiscExterior ∧ fsans μ (α n) = h (u n)) ∧
      B (h (u n)) + (u n - h (u n)) * deriv B (h (u n)) ≠ 0 ∧ ‖u n‖ ≤ R := by
    filter_upwards [hαe, hu.eventually hCc, hRu] with n h1 h2 h3
    exact ⟨h1, h2.1, h3⟩
  obtain ⟨N0, hN0⟩ := eventually_atTop.mp hall
  have hN : ∀ n, (α (n + N0) = Function.invFunOn (fsans μ) unitDisc (h (u (n + N0))) ∧
      u (n + N0) ∈ gsans μ '' unitDiscExterior ∧ fsans μ (α (n + N0)) = h (u (n + N0))) ∧
      B (h (u (n + N0))) + (u (n + N0) - h (u (n + N0))) * deriv B (h (u (n + N0))) ≠ 0 ∧
      ‖u (n + N0)‖ ≤ R := fun n => hN0 (n + N0) (Nat.le_add_left _ _)
  have ha0p : ∀ n, 0 < ‖α (n + N0)‖ ∧ ‖α (n + N0)‖ < 1 := fun n => hα _
  have ha0l : Tendsto (fun n => ‖α (n + N0)‖) atTop (𝓝 1) := hαl.comp (tendsto_add_atTop_nat N0)
  obtain ⟨σ, hσ, f, g, hfK, hgK, hfl, hgl, hfg, -⟩ :=
    qd_nf_limits hμ hν hP eμ eν hKμ hKν heμ heν ha0p ha0l
  have hsp : ∀ n, 0 < ‖α (σ n + N0)‖ ∧ ‖α (σ n + N0)‖ < 1 := fun n => hα _
  have hsl : Tendsto (fun n => ‖α (σ n + N0)‖) atTop (𝓝 1) := ha0l.comp hσ.tendsto_atTop
  obtain ⟨ρ, hρ, -, hdμ, hfd⟩ := qd_nderiv_conv hμ eμ heμ hsp hsl hfl (T := 0) (by norm_num)
  have hd0 : Tendsto (fun n => deriv (cbl_normalized eμ (α (σ n + N0))) 0) atTop (𝓝 (deriv f 0)) :=
    hdμ.tendsto_at (mem_ball_self hρ)
  have hfi : InjOn f (ball 0 ρ) := hfK.1.2.2.1.2.1.mono (subset_univ _)
  have hf0 : deriv f 0 ≠ 0 := deriv_ne_zero_of_injOn isOpen_ball hfd hfi (mem_ball_self hρ)
  -- two-sided control of `Z_μ(u)` by the normalized derivative at `0`
  have hZd : ∀ n, ‖(u (σ n + N0) - eμ (α (σ n + N0))) /
      (eμ (cbl_source (α (σ n + N0)) 1) - eμ (α (σ n + N0)))‖ ≤
        2 * D * ‖deriv (cbl_normalized eμ (α (σ n + N0))) 0‖ ∧
      ‖deriv (cbl_normalized eμ (α (σ n + N0))) 0‖ / 2 ≤ ‖(u (σ n + N0) - eμ (α (σ n + N0))) /
        (eμ (cbl_source (α (σ n + N0)) 1) - eμ (α (σ n + N0)))‖ := by
    intro n
    obtain ⟨⟨-, hyE, hfa⟩, -, hyR⟩ := hN (σ n)
    have hb := hsp n
    generalize α (σ n + N0) = b at hb hfa ⊢
    generalize u (σ n + N0) = y at hyE hfa hyR ⊢
    have hbD : b ∈ unitDisc := mem_ball_zero_iff.mpr hb.2
    have hs0 : cbl_source b 0 = b := by simp [cbl_source]
    obtain ⟨-, hder⟩ := qd_nderiv_at hμ eμ heμ hb.1 hb.2 (T := 0) (by rw [hs0]; exact hbD)
    rw [hs0] at hder
    have heb : eμ b = h y := by rw [heμ hbD]; exact hfa
    have hbμ : 0 < ‖eμ (cbl_source b 1) - h y‖ := by
      rw [← heb]
      exact norm_pos_iff.mpr (sub_ne_zero.mpr fun h' => cbl_source_one_ne hb.1 hb.2 (eμ.injective h'))
    rw [hder.deriv, heb]
    refine ⟨hcbd y hyE hyR b hb.1 hb.2 hfa _, ?_⟩
    have hlow := (qd_dh_bound hμ hh hb1 hyE).1
    have hden : poincareDensity (fsans μ '' unitDisc) (h y) =
        2 / ((1 - ‖b‖ ^ 2) * ‖deriv (fsans μ) b‖) := by
      rw [← hfa]; exact eq22_density_formula hf hbD
    rw [hden] at hlow
    have hfd' : 0 < ‖deriv (fsans μ) b‖ :=
      norm_pos_iff.mpr (deriv_ne_zero_of_injOn isOpen_ball hf.1 hf.2.1 hbD)
    have hgap : 0 < 1 - ‖b‖ ^ 2 := by nlinarith [hb.2, norm_nonneg b]
    rw [mul_div_assoc', le_div_iff₀ (by positivity)] at hlow
    have ht : (1 - ‖b‖) * ‖deriv (fsans μ) b‖ ≤ 4 * ‖y - h y‖ := by
      nlinarith [mul_nonneg (mul_nonneg (by linarith [hb.2] : (0 : ℝ) ≤ 1 - ‖b‖) (norm_nonneg b)) hfd'.le]
    rw [norm_div, norm_div, norm_mul, cbl_scale_norm hb.1 hb.2, div_div,
      div_le_div_iff₀ (by positivity) hbμ]
    nlinarith [mul_le_mul_of_nonneg_right ht hbμ.le]
  have hfreq : ∃ᶠ n in atTop, (fun n => (u (σ n + N0) - eμ (α (σ n + N0))) /
      (eμ (cbl_source (α (σ n + N0)) 1) - eμ (α (σ n + N0)))) n ∈
        closedBall (0 : ℂ) (2 * D * (‖deriv f 0‖ + 1)) := by
    refine Eventually.frequently ?_
    filter_upwards [hd0.norm.eventually (eventually_lt_nhds (lt_add_one _))] with n hn
    rw [mem_closedBall_zero_iff]
    exact (hZd n).1.trans (mul_le_mul_of_nonneg_left hn.le (by positivity))
  obtain ⟨Z, -, τ, hτ, hZτ⟩ := tendsto_subseq_of_frequently_bounded isBounded_closedBall hfreq
  have hZpos : 0 < ‖Z‖ := by
    have h1 : ‖deriv f 0‖ / 2 ≤ ‖Z‖ :=
      le_of_tendsto_of_tendsto' (((hd0.comp hτ.tendsto_atTop).norm).div_const 2) hZτ.norm
        (fun n => (hZd (τ n)).2)
    have : 0 < ‖deriv f 0‖ := norm_pos_iff.mpr hf0
    linarith
  have hι : StrictMono (fun n => σ (τ n) + N0) := fun i j hij => Nat.add_lt_add_right (hσ (hτ hij)) N0
  have hap : ∀ n, 0 < ‖α (σ (τ n) + N0)‖ ∧ ‖α (σ (τ n) + N0)‖ < 1 := fun n => hα _
  have hal : Tendsto (fun n => ‖α (σ (τ n) + N0)‖) atTop (𝓝 1) := hαl.comp hι.tendsto_atTop
  have hflτ := qd_tlu_sub hfl hτ.tendsto_atTop
  have hglτ := qd_tlu_sub hgl hτ.tendsto_atTop
  obtain ⟨M, hM⟩ := isBounded_iff_forall_norm_le.mp (Metric.isBounded_range_of_tendsto _ hZτ)
  have hS1 := qd_S1 hμ hν hA hB hode hrat hh eμ eν heμ heν hap hal hfK hgK hflτ hglτ hfg
    (y := fun n => u (σ (τ n) + N0)) (fun n => (hN (σ (τ n))).1.2.1) (fun n => (hN (σ (τ n))).2.1)
    (Tlim := 0) (by norm_num)
    ((tendsto_const_nhds (x := (0 : ℂ))).congr fun n => by
      rw [← (hN (σ (τ n))).1.1, sub_self, zero_div])
    (M := M) (fun n => hM _ ⟨n, rfl⟩)
    ((qd_prerel_seq hμ hν hP hp hh hinf hu).comp hι.tendsto_atTop)
  have hW : Tendsto (fun n => (cnf_finite A B h (u (σ (τ n) + N0)) - eν (α (σ (τ n) + N0))) /
      (eν (cbl_source (α (σ (τ n) + N0)) 1) - eν (α (σ (τ n) + N0)))) atTop (𝓝 Z) := by
    have h2 := hS1.add hZτ
    rw [zero_add] at h2
    exact h2.congr fun n => sub_add_cancel _ _
  -- separation from the interior frame
  set r : ℝ := 1 / (2 * (1 + 4 * C₀)) with hr
  have hr0 : 0 < r := by positivity
  have hsepT : ∀ T : ℂ, -2 < T.re → r * ‖Z‖ ≤ ‖f T - Z‖ := by
    intro T hT
    have hev := cbs_eventually_mapsTo hap hal (isCompact_singleton (x := T)) (singleton_subset_iff.mpr hT)
    have hlim1 : Tendsto (fun n => ‖(u (σ (τ n) + N0) - eμ (α (σ (τ n) + N0))) /
        (eμ (cbl_source (α (σ (τ n) + N0)) 1) - eμ (α (σ (τ n) + N0))) -
          cbl_normalized eμ (α (σ (τ n) + N0)) T‖) atTop (𝓝 ‖Z - f T‖) :=
      (hZτ.sub ((hflτ.tendstoLocallyUniformlyOn (s := univ)).tendsto_at (mem_univ T))).norm
    have hlim2 : Tendsto (fun n => r * ‖(u (σ (τ n) + N0) - eμ (α (σ (τ n) + N0))) /
        (eμ (cbl_source (α (σ (τ n) + N0)) 1) - eμ (α (σ (τ n) + N0)))‖) atTop (𝓝 (r * ‖Z‖)) :=
      hZτ.norm.const_mul r
    rw [norm_sub_rev]
    refine le_of_tendsto_of_tendsto hlim2 hlim1 ?_
    filter_upwards [hev] with n hn
    obtain ⟨⟨-, hyE, hfa⟩, -, -⟩ := hN (σ (τ n))
    have hb := hap n
    have hsrcD : cbl_source (α (σ (τ n) + N0)) T ∈ unitDisc := hn (mem_singleton T)
    generalize α (σ (τ n) + N0) = b at hb hfa hsrcD ⊢
    generalize u (σ (τ n) + N0) = y at hyE hfa ⊢
    have hbD : b ∈ unitDisc := mem_ball_zero_iff.mpr hb.2
    have heb : eμ b = h y := by rw [heμ hbD]; exact hfa
    have hin : eμ (cbl_source b T) ∈ fsans μ '' unitDisc := ⟨_, hsrcD, (heμ hsrcD).symm⟩
    have hball := (qd_ball hμ hC1 hh hb1 hC₀ hyE).1
    have hfar : r * ‖y - h y‖ < ‖y - eμ (cbl_source b T)‖ := by
      by_contra hle
      push_neg at hle
      have hmem : eμ (cbl_source b T) ∈ closedBall y (‖y - h y‖ / (2 * (1 + 4 * C₀))) := by
        rw [mem_closedBall, dist_comm, dist_eq_norm]
        calc ‖y - eμ (cbl_source b T)‖ ≤ r * ‖y - h y‖ := hle
          _ = ‖y - h y‖ / (2 * (1 + 4 * C₀)) := by rw [hr]; ring
      exact (qd_sides hμ).1.le_bot ⟨hin, hball hmem⟩
    have hbμ : eμ (cbl_source b 1) - eμ b ≠ 0 :=
      sub_ne_zero.mpr fun h' => cbl_source_one_ne hb.1 hb.2 (eμ.injective h')
    have heq1 : (y - eμ b) / (eμ (cbl_source b 1) - eμ b) - cbl_normalized eμ b T =
        (y - eμ (cbl_source b T)) / (eμ (cbl_source b 1) - eμ b) := by
      unfold cbl_normalized; field_simp; ring
    rw [heq1, norm_div, norm_div, heb, mul_div_assoc']
    exact div_le_div_of_nonneg_right hfar.le (norm_nonneg _)
  have hgc : Continuous g := continuousOn_univ.mp hgK.1.2.2.1.1
  refine ⟨fun n => σ (τ n) + N0, hι, fun n => α (σ (τ n) + N0), hap, hal,
    fun n => ⟨(hN _).1.1, (hN _).1.2.1, (hN _).1.2.2, (hN _).2.1⟩, f, g, hfK, hgK, hflτ, hglτ, hfg, Z, hZτ, hW,
    r * ‖Z‖, by positivity, fun S hS => ?_⟩
  have hcl : IsClosed {S : ℂ | r * ‖Z‖ ≤ ‖g S - Z‖} :=
    isClosed_le continuous_const ((hgc.sub continuous_const).norm)
  have h0 : Tendsto (fun k : ℕ => 1 / ((k : ℝ) + 1)) atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hseq : Tendsto (fun k : ℕ => S + ((1 / ((k : ℝ) + 1) : ℝ) : ℂ)) atTop (𝓝 S) := by
    have h1 := ((Complex.continuous_ofReal.tendsto 0).comp h0).const_add S
    simpa using h1
  refine hcl.mem_of_tendsto hseq (Eventually.of_forall fun k => ?_)
  have hk : -2 < (S + ((1 / ((k : ℝ) + 1) : ℝ) : ℂ)).re := by
    rw [Complex.add_re, Complex.ofReal_re]
    have : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
    linarith
  show r * ‖Z‖ ≤ ‖g _ - Z‖
  rw [← hfg hk]
  exact hsepT _ hk

/-- Limit of the frame gap expression of `cbs_source_gap`. -/
theorem qd_gap_tendsto {a S : ℕ → ℂ} {S0 : ℂ} (hal : Tendsto (fun n => ‖a n‖) atTop (𝓝 1))
    (hS : Tendsto S atTop (𝓝 S0)) :
    Tendsto (fun n => 1 + ‖a n‖ + ‖a n‖ * (S n).re - (1 - ‖a n‖) * ‖S n‖ ^ 2 / 4) atTop (𝓝 (2 + S0.re)) := by
  have h1 := ((tendsto_const_nhds (x := (1 : ℝ))).add hal).add
    (hal.mul ((Complex.continuous_re.tendsto S0).comp hS))
  have h2 := (((tendsto_const_nhds (x := (1 : ℝ))).sub hal).mul (hS.norm.pow 2)).div_const 4
  have e : (2 + S0.re) = 1 + 1 + 1 * S0.re - (1 - 1) * ‖S0‖ ^ 2 / 4 := by ring
  rw [e]
  exact h1.sub h2

/-- Frame points inside the closed unit disc have limits in `Re ≥ -2`. -/
theorem qd_re_limit {a S : ℕ → ℂ} {S0 : ℂ} (ha : ∀ n, 0 < ‖a n‖ ∧ ‖a n‖ < 1)
    (hal : Tendsto (fun n => ‖a n‖) atTop (𝓝 1)) (hS : Tendsto S atTop (𝓝 S0))
    (hin : ∀ᶠ n in atTop, ‖cbl_source (a n) (S n)‖ ≤ 1) : -2 ≤ S0.re := by
  have hge : 0 ≤ 2 + S0.re := by
    refine ge_of_tendsto (qd_gap_tendsto hal hS) ?_
    filter_upwards [hin] with n hn
    have hg := cbs_source_gap (ha n).1 (S n)
    have h1 : 0 ≤ 1 - ‖cbl_source (a n) (S n)‖ ^ 2 := by
      nlinarith [norm_nonneg (cbl_source (a n) (S n))]
    rw [hg] at h1
    exact (mul_nonneg_iff_of_pos_left (by linarith [(ha n).2])).mp h1
  linarith

/-- The frame coordinate `-2` is the radial boundary point. -/
theorem qd_src_m2 {a : ℂ} (ha0 : 0 < ‖a‖) : ‖cbl_source a (-2)‖ = 1 := by
  have h := cbs_source_gap ha0 (-2)
  rw [show ((-2 : ℂ)).re = -2 by norm_num, show ‖(-2 : ℂ)‖ = 2 by norm_num] at h
  have h2 : ‖cbl_source a (-2)‖ ^ 2 = 1 := by linear_combination -h
  nlinarith [norm_nonneg (cbl_source a (-2))]

/-- A welding extension takes only disc points into `Ω`. -/
theorem qd_e_mem {μ : LinfStar} (e : ℂ ≃ₜ ℂ) (he : EqOn e (fsans μ) unitDisc) {x : ℂ}
    (hx : e x ∈ fsans μ '' unitDisc) : x ∈ unitDisc := by
  obtain ⟨s, hs, hse⟩ := hx
  rw [← he hs] at hse
  rw [← e.injective hse]
  exact hs

/-- The contact identity `N y = F(h y) + F'(h y)(y - h y)/(1 - κ/2)`. -/
theorem qd_N_contact {μ ν : LinfStar} (hμ : μ ∈ LinfStarBall)
    {A B : ℂ → ℂ} (hA : DifferentiableOn ℂ A (fsans μ '' unitDisc))
    (hB : DifferentiableOn ℂ B (fsans μ '' unitDisc))
    (hode : ∀ z ∈ fsans μ '' unitDisc,
      deriv (deriv A) z + schwarzianHol (crs_transition μ ν) z / 2 * A z = 0 ∧
      deriv (deriv B) z + schwarzianHol (crs_transition μ ν) z / 2 * B z = 0 ∧
      A z * deriv B z - B z * deriv A z = 1)
    (hrat : ∀ z ∈ fsans μ '' unitDisc, (crs_transition μ ν z : ExtPlane) = t203_ratio (A z) (B z))
    {h : ℂ → ℂ} (hh : IsQCReflection (fsans μ '' unitDisc) (gsans μ '' unitDiscExterior) h)
    {y : ℂ} (hy : y ∈ gsans μ '' unitDiscExterior)
    (hd : B (h y) + (y - h y) * deriv B (h y) ≠ 0) :
    1 - (y - h y) * deriv (deriv (crs_transition μ ν)) (h y) / deriv (crs_transition μ ν) (h y) / 2 ≠ 0 ∧
      cnf_finite A B h y - crs_transition μ ν (h y) = deriv (crs_transition μ ν) (h y) * (y - h y) /
        (1 - (y - h y) * deriv (deriv (crs_transition μ ν)) (h y) / deriv (crs_transition μ ν) (h y) / 2) := by
  have hv := hh.2.1 hy
  obtain ⟨hBv, hFq, hF1, -⟩ := qd_FB hμ hA hB hode hrat hv
  obtain ⟨d1, -⟩ := qd_den_formula hμ hA hB hode hrat hv (y - h y)
  have hne : 1 - (y - h y) * deriv (deriv (crs_transition μ ν)) (h y) /
      deriv (crs_transition μ ν) (h y) / 2 ≠ 0 := by
    intro h0; apply hd; rw [d1, h0, mul_zero]
  have hW := (hode _ hv).2.2
  have hNb : cnf_finite A B h y - crs_transition μ ν (h y) =
      -(y - h y) / (B (h y) * (B (h y) + (y - h y) * deriv B (h y))) := by
    rw [hFq]; unfold cnf_finite; field_simp; linear_combination (-(y - h y)) * hW
  refine ⟨hne, ?_⟩
  rw [hNb, d1, hF1]
  field_simp

/-- `qd_S1` with eventual hypotheses. -/
theorem qd_S1_ev {μ ν : LinfStar} (hμ : μ ∈ LinfStarBall) (hν : ν ∈ LinfStarBall)
    {A B : ℂ → ℂ} (hA : DifferentiableOn ℂ A (fsans μ '' unitDisc))
    (hB : DifferentiableOn ℂ B (fsans μ '' unitDisc))
    (hode : ∀ z ∈ fsans μ '' unitDisc,
      deriv (deriv A) z + schwarzianHol (crs_transition μ ν) z / 2 * A z = 0 ∧
      deriv (deriv B) z + schwarzianHol (crs_transition μ ν) z / 2 * B z = 0 ∧
      A z * deriv B z - B z * deriv A z = 1)
    (hrat : ∀ z ∈ fsans μ '' unitDisc, (crs_transition μ ν z : ExtPlane) = t203_ratio (A z) (B z))
    {h : ℂ → ℂ} (hh : IsQCReflection (fsans μ '' unitDisc) (gsans μ '' unitDiscExterior) h)
    (eμ eν : ℂ ≃ₜ ℂ) (heμ : EqOn eμ (fsans μ) unitDisc) (heν : EqOn eν (fsans ν) unitDisc)
    {a : ℕ → ℂ} (ha : ∀ n, 0 < ‖a n‖ ∧ ‖a n‖ < 1) (halim : Tendsto (fun n => ‖a n‖) atTop (𝓝 1))
    {f g : ℂ → ℂ} {K L : ℝ} (hf : IsKQCNormalizedPlane f K) (hg : IsKQCNormalizedPlane g L)
    (hfl : TendstoLocallyUniformly (fun n => cbl_normalized eμ (a n)) f atTop)
    (hgl : TendstoLocallyUniformly (fun n => cbl_normalized eν (a n)) g atTop)
    (hfg : EqOn f g {t : ℂ | -2 < t.re})
    {y : ℕ → ℂ} (hy : ∀ᶠ n in atTop, y n ∈ gsans μ '' unitDiscExterior)
    (hd : ∀ᶠ n in atTop, B (h (y n)) + (y n - h (y n)) * deriv B (h (y n)) ≠ 0)
    {Tlim : ℂ} (hTlim : -2 < Tlim.re)
    (hT : Tendsto (fun n => (Function.invFunOn (fsans μ) unitDisc (h (y n)) - a n) / cbl_scale (a n))
      atTop (𝓝 Tlim))
    {M : ℝ} (hZ : ∀ᶠ n in atTop, ‖(y n - eμ (a n)) / (eμ (cbl_source (a n) 1) - eμ (a n))‖ ≤ M)
    (hκ : Tendsto (fun n => (y n - h (y n)) * deriv (deriv (crs_transition μ ν)) (h (y n)) /
      deriv (crs_transition μ ν) (h (y n))) atTop (𝓝 0)) :
    Tendsto (fun n => (cnf_finite A B h (y n) - eν (a n)) / (eν (cbl_source (a n) 1) - eν (a n)) -
      (y n - eμ (a n)) / (eμ (cbl_source (a n) 1) - eμ (a n))) atTop (𝓝 0) := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hy.and (hd.and hZ))
  have hs := tendsto_add_atTop_nat N
  refine (tendsto_add_atTop_iff_nat N).mp ?_
  exact qd_S1 hμ hν hA hB hode hrat hh eμ eν heμ heν (a := fun n => a (n + N)) (fun n => ha _)
    (halim.comp hs) hf hg (qd_tlu_sub hfl hs) (qd_tlu_sub hgl hs) hfg (y := fun n => y (n + N))
    (fun n => (hN _ (Nat.le_add_left _ _)).1) (fun n => (hN _ (Nat.le_add_left _ _)).2.1) hTlim
    (hT.comp hs) (fun n => (hN _ (Nat.le_add_left _ _)).2.2) (hκ.comp hs)

/-- **Target-frame bound.** `W_ν(N u)` in the frame at `h u` is eventually bounded along the reflection-boundary
filter. -/
theorem qd_W_bdd {μ ν : LinfStar} (hμ : μ ∈ LinfStarBall) (hν : ν ∈ LinfStarBall)
    (hP : AInf.toFun (bersPhi ν - bersPhi μ) ∈ A2fun unitDisc)
    {h : ℂ → ℂ} {K C₀ : ℝ} {p : ℂ} (hp : p ∈ fsans μ '' unitDisc)
    (hC1 : ContDiffOn ℝ 1 h (gsans μ '' unitDiscExterior))
    (hpl : IsPlanarQCReflection (gsans μ '' unitDiscExterior) ((fsans μ '' unitDisc) \ {p}) h K)
    (hh : IsQCReflection (fsans μ '' unitDisc) (gsans μ '' unitDiscExterior) h)
    (hinf : Tendsto h (cocompact ℂ ⊓ 𝓟 (gsans μ '' unitDiscExterior)) (𝓝 p))
    (hb1 : ∀ u ∈ gsans μ '' unitDiscExterior, ‖u - h u‖ ^ 2 * ‖fderiv ℝ h u‖ *
      poincareDensity (fsans μ '' unitDisc) (h u) ^ 2 ≤ C₀)
    (hb2 : ∀ u ∈ gsans μ '' unitDiscExterior, ‖u - h u‖ ^ 2 * ‖dzbar h u‖ *
      poincareDensity (fsans μ '' unitDisc) (h u) ^ 2 ≤ C₀)
    {A B : ℂ → ℂ} (hA : DifferentiableOn ℂ A (fsans μ '' unitDisc))
    (hB : DifferentiableOn ℂ B (fsans μ '' unitDisc))
    (hode : ∀ z ∈ fsans μ '' unitDisc,
      deriv (deriv A) z + schwarzianHol (crs_transition μ ν) z / 2 * A z = 0 ∧
      deriv (deriv B) z + schwarzianHol (crs_transition μ ν) z / 2 * B z = 0 ∧
      A z * deriv B z - B z * deriv A z = 1)
    (hrat : ∀ z ∈ fsans μ '' unitDisc, (crs_transition μ ν z : ExtPlane) = t203_ratio (A z) (B z))
    (eμ eν : ℂ ≃ₜ ℂ) {Kμ Kν : ℝ} (hKμ : IsKQC eμ univ Kμ) (hKν : IsKQC eν univ Kν)
    (heμ : EqOn eμ (fsans μ) unitDisc) (heν : EqOn eν (fsans ν) unitDisc) :
    ∃ C : ℝ, ∀ᶠ u in crb_reflectionBoundary μ h,
      ‖(cnf_finite A B h u - eν (Function.invFunOn (fsans μ) unitDisc (h u))) /
        (eν (cbl_source (Function.invFunOn (fsans μ) unitDisc (h u)) 1) -
          eν (Function.invFunOn (fsans μ) unitDisc (h u)))‖ ≤ C := by
  haveI : (crb_reflectionBoundary μ h).IsCountablyGenerated := by
    unfold crb_reflectionBoundary crb_diskBoundary; infer_instance
  by_contra hc
  push_neg at hc
  obtain ⟨s, hs⟩ := (crb_reflectionBoundary μ h).exists_antitone_basis
  have hpick : ∀ k : ℕ, ∃ v ∈ s k, (k : ℝ) <
      ‖(cnf_finite A B h v - eν (Function.invFunOn (fsans μ) unitDisc (h v))) /
        (eν (cbl_source (Function.invFunOn (fsans μ) unitDisc (h v)) 1) -
          eν (Function.invFunOn (fsans μ) unitDisc (h v)))‖ := by
    intro k
    obtain ⟨v, h1, h2⟩ := ((hc k).and_eventually (hs.mem k)).exists
    exact ⟨v, h2, h1⟩
  choose v hvs hvk using hpick
  have hv : Tendsto v atTop (crb_reflectionBoundary μ h) := hs.tendsto hvs
  obtain ⟨φ, hφ, a, -, -, hpr, -, -, -, -, -, -, -, Z, -, hW, -⟩ :=
    qd_pack hμ hν hP hp hC1 hpl hh hinf hb1 hb2 hA hB hode hrat eμ eν hKμ hKν heμ heν hv
  have hW' : Tendsto (fun n => ‖(cnf_finite A B h (v (φ n)) -
      eν (Function.invFunOn (fsans μ) unitDisc (h (v (φ n))))) /
        (eν (cbl_source (Function.invFunOn (fsans μ) unitDisc (h (v (φ n)))) 1) -
          eν (Function.invFunOn (fsans μ) unitDisc (h (v (φ n)))))‖) atTop (𝓝 ‖Z‖) := by
    refine (hW.congr fun n => ?_).norm
    rw [(hpr n).1]
  obtain ⟨n, hn1, hn2⟩ :=
    ((hW'.eventually (gt_mem_nhds (lt_add_one ‖Z‖))).and (eventually_ge_atTop ⌈‖Z‖ + 1⌉₊)).exists
  have h3 := hvk (φ n)
  have h4 : (n : ℝ) ≤ φ n := by exact_mod_cast hφ.id_le n
  have h5 : ‖Z‖ + 1 ≤ n := (Nat.le_ceil _).trans (by exact_mod_cast hn2)
  linarith

/-- **(Collision)** Two distinct sequences tending to the reflection-boundary filter, with equal Ahlfors images and
the second target scale not larger than the first, cannot exist. -/
theorem qd_coll {μ ν : LinfStar} (hμ : μ ∈ LinfStarBall) (hν : ν ∈ LinfStarBall)
    (hP : AInf.toFun (bersPhi ν - bersPhi μ) ∈ A2fun unitDisc)
    {h : ℂ → ℂ} {K C₀ : ℝ} {p : ℂ} (hp : p ∈ fsans μ '' unitDisc)
    (hC1 : ContDiffOn ℝ 1 h (gsans μ '' unitDiscExterior))
    (hpl : IsPlanarQCReflection (gsans μ '' unitDiscExterior) ((fsans μ '' unitDisc) \ {p}) h K)
    (hh : IsQCReflection (fsans μ '' unitDisc) (gsans μ '' unitDiscExterior) h)
    (hinf : Tendsto h (cocompact ℂ ⊓ 𝓟 (gsans μ '' unitDiscExterior)) (𝓝 p))
    (hb1 : ∀ u ∈ gsans μ '' unitDiscExterior, ‖u - h u‖ ^ 2 * ‖fderiv ℝ h u‖ *
      poincareDensity (fsans μ '' unitDisc) (h u) ^ 2 ≤ C₀)
    (hb2 : ∀ u ∈ gsans μ '' unitDiscExterior, ‖u - h u‖ ^ 2 * ‖dzbar h u‖ *
      poincareDensity (fsans μ '' unitDisc) (h u) ^ 2 ≤ C₀)
    {A B : ℂ → ℂ} (hA : DifferentiableOn ℂ A (fsans μ '' unitDisc))
    (hB : DifferentiableOn ℂ B (fsans μ '' unitDisc))
    (hode : ∀ z ∈ fsans μ '' unitDisc,
      deriv (deriv A) z + schwarzianHol (crs_transition μ ν) z / 2 * A z = 0 ∧
      deriv (deriv B) z + schwarzianHol (crs_transition μ ν) z / 2 * B z = 0 ∧
      A z * deriv B z - B z * deriv A z = 1)
    (hrat : ∀ z ∈ fsans μ '' unitDisc, (crs_transition μ ν z : ExtPlane) = t203_ratio (A z) (B z))
    (eμ eν : ℂ ≃ₜ ℂ) {Kμ Kν : ℝ} (hKμ : IsKQC eμ univ Kμ) (hKν : IsKQC eν univ Kν)
    (heμ : EqOn eμ (fsans μ) unitDisc) (heν : EqOn eν (fsans ν) unitDisc)
    {u v : ℕ → ℂ} (hu : Tendsto u atTop (crb_reflectionBoundary μ h))
    (hv : Tendsto v atTop (crb_reflectionBoundary μ h)) (hne : ∀ n, u n ≠ v n)
    (heq : ∀ n, cnf_finite A B h (u n) = cnf_finite A B h (v n))
    (hlab : ∀ n, ‖eν (cbl_source (Function.invFunOn (fsans μ) unitDisc (h (v n))) 1) -
        eν (Function.invFunOn (fsans μ) unitDisc (h (v n)))‖ ≤
      ‖eν (cbl_source (Function.invFunOn (fsans μ) unitDisc (h (u n))) 1) -
        eν (Function.invFunOn (fsans μ) unitDisc (h (u n)))‖) : False := by
  have hf := S2C.s2c_conf_f hμ
  obtain ⟨φ, hφ, a, ha, hal, hpr, f, g, hfK, hgK, hfl, hgl, hfg, Z, hZ, hW, ε, hε, hsep⟩ :=
    qd_pack hμ hν hP hp hC1 hpl hh hinf hb1 hb2 hA hB hode hrat eμ eν hKμ hKν heμ heν hu
  have hφt := hφ.tendsto_atTop
  have hvt : Tendsto (fun n => v (φ n)) atTop (crb_reflectionBoundary μ h) := hv.comp hφt
  obtain ⟨C, hC⟩ := qd_W_bdd hμ hν hP hp hC1 hpl hh hinf hb1 hb2 hA hB hode hrat eμ eν hKμ hKν heμ heν
  obtain ⟨Cc, hCc⟩ := qd_contact hμ hν hP hp hC1 hpl hh hinf hb1 hb2 hA hB hode hrat
  obtain ⟨R, hR0, hRu⟩ := qd_bdd_of_boundary hμ hp hinf hvt
  obtain ⟨D1, hD1, hdisp⟩ := eq22_reflection_bounded_displacement hμ hh R hR0
  obtain ⟨D2, hD2, htF⟩ := qd_tF_dist hμ hν hh R hR0
  have hκv := qd_prerel_seq hμ hν hP hp hh hinf hvt
  obtain ⟨A', hA'⟩ : ∃ A' : ℕ → ℂ, ∀ n, A' n = Function.invFunOn (fsans μ) unitDisc (h (v (φ n))) :=
    ⟨_, fun n => rfl⟩
  have hA1 : Tendsto (fun n => ‖A' n‖) atTop (𝓝 1) := by
    have h2 := tendsto_comap_iff.mp (hvt.mono_right inf_le_left)
    refine (tendsto_comap_iff.mp (h2.mono_right inf_le_left)).congr fun n => ?_
    simp only [Function.comp_apply, hA']
  have hall : ∀ᶠ n in atTop, v (φ n) ∈ gsans μ '' unitDiscExterior ∧
      B (h (v (φ n))) + (v (φ n) - h (v (φ n))) * deriv B (h (v (φ n))) ≠ 0 ∧ ‖v (φ n)‖ ≤ R ∧
      ‖(cnf_finite A B h (v (φ n)) - eν (A' n)) / (eν (cbl_source (A' n) 1) - eν (A' n))‖ ≤ C ∧
      ‖(v (φ n) - h (v (φ n))) * deriv (deriv (crs_transition μ ν)) (h (v (φ n))) /
        deriv (crs_transition μ ν) (h (v (φ n)))‖ ≤ 1 ∧ 0 < ‖A' n‖ := by
    filter_upwards [tendsto_principal.mp (hvt.mono_right inf_le_right), hvt.eventually hCc, hRu,
      hvt.eventually hC, hκv.norm.eventually (ge_mem_nhds (by simp : ‖(0 : ℂ)‖ < 1)),
      hA1.eventually (lt_mem_nhds one_pos)] with n h1 h2 h3 h4 h5 h6
    rw [← hA' n] at h4
    exact ⟨h1, h2.1, h3, h4, h5, h6⟩
  have hAD : ∀ n, v (φ n) ∈ gsans μ '' unitDiscExterior → A' n ∈ unitDisc ∧ fsans μ (A' n) = h (v (φ n)) := by
    intro n hn
    rw [hA']
    exact ⟨Function.invFunOn_mem (hh.2.1 hn), Function.invFunOn_eq (hh.2.1 hn)⟩
  obtain ⟨S, hSdef⟩ : ∃ S : ℕ → ℂ, ∀ n, S n = (A' n - a n) / cbl_scale (a n) := ⟨_, fun n => rfl⟩
  have hsrc : ∀ n, cbl_source (a n) (S n) = A' n := by
    intro n
    have hc := cbl_scale_ne_zero (ha n).1 (ha n).2
    rw [hSdef]; simp only [cbl_source]; field_simp; ring
  have hbν : ∀ n, eν (cbl_source (a n) 1) - eν (a n) ≠ 0 := fun n =>
    sub_ne_zero.mpr fun h' => cbl_source_one_ne (ha n).1 (ha n).2 (eν.injective h')
  have hbμ : ∀ n, eμ (cbl_source (a n) 1) - eμ (a n) ≠ 0 := fun n =>
    sub_ne_zero.mpr fun h' => cbl_source_one_ne (ha n).1 (ha n).2 (eμ.injective h')
  have hWdiff : ∀ n, (cnf_finite A B h (u (φ n)) - eν (a n)) / (eν (cbl_source (a n) 1) - eν (a n)) -
      cbl_normalized eν (a n) (S n) =
        (cnf_finite A B h (v (φ n)) - eν (A' n)) / (eν (cbl_source (a n) 1) - eν (a n)) := by
    intro n
    have hb := hbν n
    unfold cbl_normalized
    rw [hsrc, heq]
    field_simp
    ring
  -- the labelled bound in the `u`-frame
  have hbd : ∀ᶠ n in atTop, ‖(cnf_finite A B h (u (φ n)) - eν (a n)) / (eν (cbl_source (a n) 1) - eν (a n)) -
      cbl_normalized eν (a n) (S n)‖ ≤ C := by
    filter_upwards [hall] with n hn
    rw [hWdiff n]
    have hl := hlab (φ n)
    rw [← (hpr n).1, ← hA' n] at hl
    have hD := hAD n hn.1
    have hbv : 0 < ‖eν (cbl_source (A' n) 1) - eν (A' n)‖ :=
      norm_pos_iff.mpr (sub_ne_zero.mpr fun h' => cbl_source_one_ne hn.2.2.2.2.2
        (mem_ball_zero_iff.mp hD.1) (eν.injective h'))
    have hbP : 0 < ‖eν (cbl_source (a n) 1) - eν (a n)‖ := norm_pos_iff.mpr (hbν n)
    have hC0 : 0 ≤ C := (norm_nonneg _).trans hn.2.2.2.1
    have h4 := hn.2.2.2.1
    rw [norm_div, div_le_iff₀ hbv] at h4
    rw [norm_div, div_le_iff₀ hbP]
    nlinarith [mul_le_mul_of_nonneg_left hl hC0]
  have hfreq : ∃ᶠ n in atTop, (fun n => cbl_normalized eν (a n) (S n)) n ∈ closedBall (0 : ℂ) (‖Z‖ + 1 + C) := by
    refine Eventually.frequently ?_
    filter_upwards [hbd, hW.norm.eventually (eventually_lt_nhds (lt_add_one ‖Z‖))] with n h1 h2
    rw [mem_closedBall_zero_iff]
    have h3 := norm_sub_le ((cnf_finite A B h (u (φ n)) - eν (a n)) / (eν (cbl_source (a n) 1) - eν (a n)))
      ((cnf_finite A B h (u (φ n)) - eν (a n)) / (eν (cbl_source (a n) 1) - eν (a n)) -
        cbl_normalized eν (a n) (S n))
    rw [sub_sub_cancel] at h3
    linarith
  obtain ⟨w, -, χ, hχ, hgS⟩ := tendsto_subseq_of_frequently_bounded isBounded_closedBall hfreq
  have hχt := hχ.tendsto_atTop
  obtain ⟨S0, -, hSχ⟩ := qd_inv_tendsto (fun n => cbl_normalized_plane eν hKν (ha (χ n)).1 (ha (χ n)).2) hgK
    (qd_tlu_sub hgl hχt) (S := fun n => S (χ n)) hgS
  have haχ : ∀ n, 0 < ‖a (χ n)‖ ∧ ‖a (χ n)‖ < 1 := fun n => ha _
  have halχ : Tendsto (fun n => ‖a (χ n)‖) atTop (𝓝 1) := hal.comp hχt
  have hallχ := hχt.eventually hall
  have hin : ∀ᶠ n in atTop, ‖cbl_source (a (χ n)) (S (χ n))‖ ≤ 1 := by
    filter_upwards [hallχ] with n hn
    rw [hsrc]
    exact (mem_ball_zero_iff.mp (hAD _ hn.1).1).le
  have hre := qd_re_limit haχ halχ hSχ hin
  have hWχ : Tendsto (fun n => (cnf_finite A B h (u (φ (χ n))) - eν (a (χ n))) /
      (eν (cbl_source (a (χ n)) 1) - eν (a (χ n)))) atTop (𝓝 Z) := hW.comp hχt
  have hfc : Continuous f := continuousOn_univ.mp hfK.1.2.2.1.1
  have hgc : Continuous g := continuousOn_univ.mp hgK.1.2.2.1.1
  have hflχ := qd_tlu_sub hfl hχt
  have hglχ := qd_tlu_sub hgl hχt
  rcases hre.lt_or_eq with hgt | heq2
  · -- interior limit: `S1` at `v` in the `u`-frame
    have hZb : ∀ n, v (φ n) ∈ gsans μ '' unitDiscExterior → ‖v (φ n)‖ ≤ R →
        ‖(v (φ n) - eμ (a n)) / (eμ (cbl_source (a n) 1) - eμ (a n))‖ ≤
          2 * D1 * ‖cbl_normalized eμ (a n) (S n) - cbl_normalized eμ (a n) (-2)‖ +
            ‖cbl_normalized eμ (a n) (S n)‖ := by
      intro n hn hnR
      obtain ⟨hD, hAf⟩ := hAD n hn
      have heA : eμ (A' n) = h (v (φ n)) := by rw [heμ hD]; exact hAf
      have hb := hbμ n
      have hsplit : (v (φ n) - eμ (a n)) / (eμ (cbl_source (a n) 1) - eμ (a n)) =
          (v (φ n) - h (v (φ n))) / (eμ (cbl_source (a n) 1) - eμ (a n)) + cbl_normalized eμ (a n) (S n) := by
        unfold cbl_normalized; rw [hsrc, heA]; field_simp; ring
      have hd := (hdisp _ hn hnR).2
      have hm2 : eμ (cbl_source (a n) (-2)) ∉ (fsans μ '' unitDisc) := fun hm => by
        have h1 := mem_ball_zero_iff.mp (qd_e_mem eμ heμ hm)
        rw [qd_src_m2 (ha n).1] at h1
        exact lt_irrefl _ h1
      have hid : Metric.infDist (h (v (φ n))) (fsans μ '' unitDisc)ᶜ ≤
          ‖h (v (φ n)) - eμ (cbl_source (a n) (-2))‖ := by
        rw [← dist_eq_norm]; exact Metric.infDist_le_dist_of_mem hm2
      have hgdiff : cbl_normalized eμ (a n) (S n) - cbl_normalized eμ (a n) (-2) =
          (h (v (φ n)) - eμ (cbl_source (a n) (-2))) / (eμ (cbl_source (a n) 1) - eμ (a n)) := by
        unfold cbl_normalized; rw [hsrc, heA]; field_simp; ring
      rw [hsplit]
      refine (norm_add_le _ _).trans ?_
      refine add_le_add ?_ le_rfl
      rw [hgdiff, norm_div, norm_div, mul_div_assoc']
      exact div_le_div_of_nonneg_right (hd.trans (mul_le_mul_of_nonneg_left hid (by positivity)))
        (norm_nonneg _)
    have h1 : Tendsto (fun n => cbl_normalized eμ (a (χ n)) (S (χ n))) atTop (𝓝 (f S0)) :=
      hflχ.tendsto_comp hfc.continuousAt hSχ
    have h2 : Tendsto (fun n => cbl_normalized eμ (a (χ n)) (-2)) atTop (𝓝 (f (-2))) :=
      hflχ.tendsto_comp hfc.continuousAt tendsto_const_nhds
    have hMev : ∀ᶠ n in atTop, ‖(v (φ (χ n)) - eμ (a (χ n))) /
        (eμ (cbl_source (a (χ n)) 1) - eμ (a (χ n)))‖ ≤
          2 * D1 * (‖f S0 - f (-2)‖ + 1) + (‖f S0‖ + 1) := by
      filter_upwards [hallχ, h1.norm.eventually (eventually_lt_nhds (lt_add_one ‖f S0‖)),
        (h1.sub h2).norm.eventually (eventually_lt_nhds (lt_add_one ‖f S0 - f (-2)‖))] with n hn hn1 hn2
      refine (hZb _ hn.1 hn.2.2.1).trans ?_
      gcongr
    have hS1 := qd_S1_ev hμ hν hA hB hode hrat hh eμ eν heμ heν haχ halχ hfK hgK hflχ hglχ hfg
      (y := fun n => v (φ (χ n))) (hallχ.mono fun n hn => hn.1) (hallχ.mono fun n hn => hn.2.1) hgt
      (hSχ.congr fun n => by rw [hSdef, hA']) hMev (hκv.comp hχt)
    have hWv : Tendsto (fun n => (cnf_finite A B h (v (φ (χ n))) - eν (a (χ n))) /
        (eν (cbl_source (a (χ n)) 1) - eν (a (χ n)))) atTop (𝓝 Z) :=
      hWχ.congr fun n => by rw [heq]
    have hZv : Tendsto (fun n => (v (φ (χ n)) - eμ (a (χ n))) /
        (eμ (cbl_source (a (χ n)) 1) - eμ (a (χ n)))) atTop (𝓝 Z) := by
      have h3 := hWv.sub hS1
      rw [sub_zero] at h3
      exact h3.congr fun n => sub_sub_cancel _ _
    have hZu : Tendsto (fun n => (u (φ (χ n)) - eμ (a (χ n))) /
        (eμ (cbl_source (a (χ n)) 1) - eμ (a (χ n)))) atTop (𝓝 Z) := hZ.comp hχt
    have hdiff : Tendsto (fun n => ‖(v (φ (χ n)) - u (φ (χ n))) /
        (eμ (cbl_source (a (χ n)) 1) - eμ (a (χ n)))‖) atTop (𝓝 0) := by
      have h3 := (hZv.sub hZu).norm
      rw [sub_self, norm_zero] at h3
      exact h3.congr fun n => by rw [div_sub_div_same, sub_sub_sub_cancel_right]
    have hZε : ε ≤ ‖Z‖ := by
      have h3 := hsep 0 (by norm_num)
      rwa [hgK.2.2.1, zero_sub, norm_neg] at h3
    have hut : Tendsto (fun n => ‖(u (φ (χ n)) - h (u (φ (χ n)))) /
        (eμ (cbl_source (a (χ n)) 1) - eμ (a (χ n)))‖) atTop (𝓝 ‖Z‖) :=
      hZu.norm.congr fun n => by rw [heμ (mem_ball_zero_iff.mpr (ha _).2), (hpr _).2.2.1]
    obtain ⟨r, hr, hev⟩ := qd_ball_inj hμ hν hP hp hC1 hpl hh hinf hb1 hb2 hA hB hode hrat
    have hev' := (hu.comp (hφ.comp hχ).tendsto_atTop).eventually hev
    obtain ⟨n, h3, h4, h5⟩ := (hev'.and ((hdiff.eventually (gt_mem_nhds
      (show (0 : ℝ) < r * ε / 2 by positivity))).and (hut.eventually (lt_mem_nhds
        (show ε / 2 < ‖Z‖ by linarith))))).exists
    have hb : 0 < ‖eμ (cbl_source (a (χ n)) 1) - eμ (a (χ n))‖ := norm_pos_iff.mpr (hbμ _)
    rw [norm_div, div_lt_iff₀ hb] at h4
    rw [norm_div, lt_div_iff₀ hb] at h5
    have hclose : ‖v (φ (χ n)) - u (φ (χ n))‖ ≤ r * ‖u (φ (χ n)) - h (u (φ (χ n)))‖ := by
      nlinarith
    apply hne (φ (χ n))
    exact h3 _ (mem_closedBall_self (by positivity)) _
      (by rw [mem_closedBall, dist_eq_norm]; exact hclose) (heq _)
  · -- boundary limit: `W_ν(N u) - g_ν(S) → 0`, so `g(S0) = Z`
    obtain ⟨Tb, hTb⟩ : ∃ Tb : ℕ → ℂ, ∀ n, Tb n =
        (cbl_source (a n) (S n) / (‖cbl_source (a n) (S n)‖ : ℂ) - a n) / cbl_scale (a n) := ⟨_, fun n => rfl⟩
    have hpt : ∀ n, v (φ n) ∈ gsans μ '' unitDiscExterior →
        B (h (v (φ n))) + (v (φ n) - h (v (φ n))) * deriv B (h (v (φ n))) ≠ 0 → ‖v (φ n)‖ ≤ R →
        ‖(v (φ n) - h (v (φ n))) * deriv (deriv (crs_transition μ ν)) (h (v (φ n))) /
          deriv (crs_transition μ ν) (h (v (φ n)))‖ ≤ 1 → 0 < ‖A' n‖ →
        ‖(cnf_finite A B h (u (φ n)) - eν (a n)) / (eν (cbl_source (a n) 1) - eν (a n)) -
          cbl_normalized eν (a n) (S n)‖ ≤
            4 * D2 * ‖cbl_normalized eν (a n) (S n) - cbl_normalized eν (a n) (Tb n)‖ := by
      intro n hn hnd hnR hnk hn0
      obtain ⟨hD, hAf⟩ := hAD n hn
      have heA' : eν (A' n) = crs_transition μ ν (h (v (φ n))) := by
        rw [heν hD, ← hAf]
        change fsans ν (A' n) = fsans ν (Function.invFunOn (fsans μ) unitDisc (fsans μ (A' n)))
        rw [hf.2.1 (Function.invFunOn_mem ⟨A' n, hD, rfl⟩) hD (Function.invFunOn_eq ⟨A' n, hD, rfl⟩)]
      have hs0 : cbl_source (a n) (S n) ≠ 0 := by rw [hsrc]; exact norm_pos_iff.mp hn0
      have hrad1 := (qd_radial (ha n).1 (ha n).2 hs0).1
      rw [← hTb n] at hrad1
      have hnot : eν (cbl_source (a n) (Tb n)) ∉ fsans ν '' unitDisc := fun hm => by
        have h1 := mem_ball_zero_iff.mp (qd_e_mem eν heν hm)
        rw [hrad1] at h1
        exact lt_irrefl _ h1
      obtain ⟨-, hcont⟩ := qd_N_contact hμ hA hB hode hrat hh hn hnd
      have hk2 : (1 : ℝ) / 2 ≤ ‖1 - (v (φ n) - h (v (φ n))) * deriv (deriv (crs_transition μ ν)) (h (v (φ n))) /
          deriv (crs_transition μ ν) (h (v (φ n))) / 2‖ := by
        have h1 := norm_sub_norm_le (1 : ℂ) ((v (φ n) - h (v (φ n))) *
          deriv (deriv (crs_transition μ ν)) (h (v (φ n))) / deriv (crs_transition μ ν) (h (v (φ n))) / 2)
        rw [norm_one, norm_div, Complex.norm_ofNat] at h1
        linarith
      have hX : ‖cnf_finite A B h (v (φ n)) - eν (A' n)‖ ≤
          2 * (‖v (φ n) - h (v (φ n))‖ * ‖deriv (crs_transition μ ν) (h (v (φ n)))‖) := by
        rw [heA', hcont, norm_div, norm_mul, div_le_iff₀ (by linarith)]
        nlinarith [mul_le_mul_of_nonneg_left hk2 (mul_nonneg (norm_nonneg (v (φ n) - h (v (φ n))))
          (norm_nonneg (deriv (crs_transition μ ν) (h (v (φ n))))))]
      have hT2 := htF _ hn hnR
      have hid : Metric.infDist (crs_transition μ ν (h (v (φ n)))) (fsans ν '' unitDisc)ᶜ ≤
          ‖eν (A' n) - eν (cbl_source (a n) (Tb n))‖ := by
        rw [heA', ← dist_eq_norm]; exact Metric.infDist_le_dist_of_mem hnot
      have hb := hbν n
      have hgd : cbl_normalized eν (a n) (S n) - cbl_normalized eν (a n) (Tb n) =
          (eν (A' n) - eν (cbl_source (a n) (Tb n))) / (eν (cbl_source (a n) 1) - eν (a n)) := by
        unfold cbl_normalized; rw [hsrc]; field_simp; ring
      rw [hWdiff n, hgd, norm_div, norm_div, mul_div_assoc']
      exact div_le_div_of_nonneg_right (by nlinarith [mul_le_mul_of_nonneg_left hid hD2.le])
        (norm_nonneg _)
    have hlim0 : Tendsto (fun n => 2 * |1 + ‖a (χ n)‖ + ‖a (χ n)‖ * (S (χ n)).re -
        (1 - ‖a (χ n)‖) * ‖S (χ n)‖ ^ 2 / 4|) atTop (𝓝 0) := by
      have h1 := (qd_gap_tendsto halχ hSχ).abs.const_mul 2
      rwa [← heq2, show (2 : ℝ) + -2 = 0 by norm_num, abs_zero, mul_zero] at h1
    have hTbS : Tendsto (fun n => Tb (χ n) - S (χ n)) atTop (𝓝 0) := by
      refine squeeze_zero_norm' ?_ hlim0
      filter_upwards [hallχ] with n hn
      have hs0 : cbl_source (a (χ n)) (S (χ n)) ≠ 0 := by rw [hsrc]; exact norm_pos_iff.mp hn.2.2.2.2.2
      rw [hTb]
      exact (qd_radial (ha _).1 (ha _).2 hs0).2
    have hTbχ : Tendsto (fun n => Tb (χ n)) atTop (𝓝 S0) := by
      have h1 := hTbS.add hSχ
      rw [zero_add] at h1
      exact h1.congr fun n => sub_add_cancel _ _
    have hg1 : Tendsto (fun n => cbl_normalized eν (a (χ n)) (S (χ n))) atTop (𝓝 (g S0)) :=
      hglχ.tendsto_comp hgc.continuousAt hSχ
    have hg2 : Tendsto (fun n => cbl_normalized eν (a (χ n)) (Tb (χ n))) atTop (𝓝 (g S0)) :=
      hglχ.tendsto_comp hgc.continuousAt hTbχ
    have hsq : Tendsto (fun n => ‖(cnf_finite A B h (u (φ (χ n))) - eν (a (χ n))) /
        (eν (cbl_source (a (χ n)) 1) - eν (a (χ n))) - cbl_normalized eν (a (χ n)) (S (χ n))‖) atTop (𝓝 0) := by
      have h1 := (hg1.sub hg2).norm.const_mul (4 * D2)
      rw [sub_self, norm_zero, mul_zero] at h1
      refine squeeze_zero' (Eventually.of_forall fun n => norm_nonneg _) ?_ h1
      filter_upwards [hallχ] with n hn
      exact hpt _ hn.1 hn.2.1 hn.2.2.1 hn.2.2.2.2.1 hn.2.2.2.2.2
    have hgZ : Tendsto (fun n => cbl_normalized eν (a (χ n)) (S (χ n))) atTop (𝓝 Z) := by
      have h1 := hWχ.sub (tendsto_zero_iff_norm_tendsto_zero.mpr hsq)
      rw [sub_zero] at h1
      exact h1.congr fun n => sub_sub_cancel _ _
    have hgS0 : g S0 = Z := tendsto_nhds_unique hg1 hgZ
    have h1 := hsep S0 heq2.le
    rw [hgS0, sub_self, norm_zero] at h1
    linarith

/-- **(B1+B2, sequences)** Two distinct sequences tending to the reflection-boundary filter eventually have distinct
images under the Ahlfors map. -/
theorem qd_inj_seq {μ ν : LinfStar} (hμ : μ ∈ LinfStarBall) (hν : ν ∈ LinfStarBall)
    (hP : AInf.toFun (bersPhi ν - bersPhi μ) ∈ A2fun unitDisc)
    {h : ℂ → ℂ} {K C₀ : ℝ} {p : ℂ} (hp : p ∈ fsans μ '' unitDisc)
    (hC1 : ContDiffOn ℝ 1 h (gsans μ '' unitDiscExterior))
    (hpl : IsPlanarQCReflection (gsans μ '' unitDiscExterior) ((fsans μ '' unitDisc) \ {p}) h K)
    (hh : IsQCReflection (fsans μ '' unitDisc) (gsans μ '' unitDiscExterior) h)
    (hinf : Tendsto h (cocompact ℂ ⊓ 𝓟 (gsans μ '' unitDiscExterior)) (𝓝 p))
    (hb1 : ∀ u ∈ gsans μ '' unitDiscExterior, ‖u - h u‖ ^ 2 * ‖fderiv ℝ h u‖ *
      poincareDensity (fsans μ '' unitDisc) (h u) ^ 2 ≤ C₀)
    (hb2 : ∀ u ∈ gsans μ '' unitDiscExterior, ‖u - h u‖ ^ 2 * ‖dzbar h u‖ *
      poincareDensity (fsans μ '' unitDisc) (h u) ^ 2 ≤ C₀)
    {A B : ℂ → ℂ} (hA : DifferentiableOn ℂ A (fsans μ '' unitDisc))
    (hB : DifferentiableOn ℂ B (fsans μ '' unitDisc))
    (hode : ∀ z ∈ fsans μ '' unitDisc,
      deriv (deriv A) z + schwarzianHol (crs_transition μ ν) z / 2 * A z = 0 ∧
      deriv (deriv B) z + schwarzianHol (crs_transition μ ν) z / 2 * B z = 0 ∧
      A z * deriv B z - B z * deriv A z = 1)
    (hrat : ∀ z ∈ fsans μ '' unitDisc, (crs_transition μ ν z : ExtPlane) = t203_ratio (A z) (B z)) {u u' : ℕ → ℂ}
    (hu : Tendsto u atTop (crb_reflectionBoundary μ h)) (hu' : Tendsto u' atTop (crb_reflectionBoundary μ h))
    (hne : ∀ n, u n ≠ u' n) :
    ∀ᶠ n in atTop, cnf_finite A B h (u n) ≠ cnf_finite A B h (u' n) := by
  obtain ⟨eμ, Kμ, hKμ, heμ⟩ := cra_welding_extension hμ
  obtain ⟨eν, Kν, hKν, heν⟩ := cra_welding_extension hν
  by_contra hc
  rw [Filter.not_eventually] at hc
  simp only [ne_eq, not_not] at hc
  have hsplit : ∃ᶠ n in atTop,
      (cnf_finite A B h (u n) = cnf_finite A B h (u' n) ∧
        ‖eν (cbl_source (Function.invFunOn (fsans μ) unitDisc (h (u' n))) 1) -
          eν (Function.invFunOn (fsans μ) unitDisc (h (u' n)))‖ ≤
        ‖eν (cbl_source (Function.invFunOn (fsans μ) unitDisc (h (u n))) 1) -
          eν (Function.invFunOn (fsans μ) unitDisc (h (u n)))‖) ∨
      (cnf_finite A B h (u' n) = cnf_finite A B h (u n) ∧
        ‖eν (cbl_source (Function.invFunOn (fsans μ) unitDisc (h (u n))) 1) -
          eν (Function.invFunOn (fsans μ) unitDisc (h (u n)))‖ ≤
        ‖eν (cbl_source (Function.invFunOn (fsans μ) unitDisc (h (u' n))) 1) -
          eν (Function.invFunOn (fsans μ) unitDisc (h (u' n)))‖) :=
    hc.mono fun n hn => (le_total _ _).imp (fun h1 => ⟨hn, h1⟩) (fun h1 => ⟨hn.symm, h1⟩)
  rcases Filter.frequently_or_distrib.mp hsplit with h1 | h1
  · obtain ⟨σ, hσ, hσp⟩ := extraction_of_frequently_atTop h1
    exact qd_coll hμ hν hP hp hC1 hpl hh hinf hb1 hb2 hA hB hode hrat eμ eν hKμ hKν heμ heν
      (hu.comp hσ.tendsto_atTop) (hu'.comp hσ.tendsto_atTop) (fun n => hne _) (fun n => (hσp n).1)
      (fun n => (hσp n).2)
  · obtain ⟨σ, hσ, hσp⟩ := extraction_of_frequently_atTop h1
    exact qd_coll hμ hν hP hp hC1 hpl hh hinf hb1 hb2 hA hB hode hrat eμ eν hKμ hKν heμ heν
      (hu'.comp hσ.tendsto_atTop) (hu.comp hσ.tendsto_atTop) (fun n => (hne _).symm) (fun n => (hσp n).1)
      (fun n => (hσp n).2)

/-- **(Side)** Eventually along the reflection-boundary filter the Ahlfors map lands in `Ω_ν* = 𝗀_ν(𝔻*)`. -/
theorem qd_side_ev {μ ν : LinfStar} (hμ : μ ∈ LinfStarBall) (hν : ν ∈ LinfStarBall)
    (hP : AInf.toFun (bersPhi ν - bersPhi μ) ∈ A2fun unitDisc)
    {h : ℂ → ℂ} {K C₀ : ℝ} {p : ℂ} (hp : p ∈ fsans μ '' unitDisc)
    (hC1 : ContDiffOn ℝ 1 h (gsans μ '' unitDiscExterior))
    (hpl : IsPlanarQCReflection (gsans μ '' unitDiscExterior) ((fsans μ '' unitDisc) \ {p}) h K)
    (hh : IsQCReflection (fsans μ '' unitDisc) (gsans μ '' unitDiscExterior) h)
    (hinf : Tendsto h (cocompact ℂ ⊓ 𝓟 (gsans μ '' unitDiscExterior)) (𝓝 p))
    (hb1 : ∀ u ∈ gsans μ '' unitDiscExterior, ‖u - h u‖ ^ 2 * ‖fderiv ℝ h u‖ *
      poincareDensity (fsans μ '' unitDisc) (h u) ^ 2 ≤ C₀)
    (hb2 : ∀ u ∈ gsans μ '' unitDiscExterior, ‖u - h u‖ ^ 2 * ‖dzbar h u‖ *
      poincareDensity (fsans μ '' unitDisc) (h u) ^ 2 ≤ C₀)
    {A B : ℂ → ℂ} (hA : DifferentiableOn ℂ A (fsans μ '' unitDisc))
    (hB : DifferentiableOn ℂ B (fsans μ '' unitDisc))
    (hode : ∀ z ∈ fsans μ '' unitDisc,
      deriv (deriv A) z + schwarzianHol (crs_transition μ ν) z / 2 * A z = 0 ∧
      deriv (deriv B) z + schwarzianHol (crs_transition μ ν) z / 2 * B z = 0 ∧
      A z * deriv B z - B z * deriv A z = 1)
    (hrat : ∀ z ∈ fsans μ '' unitDisc, (crs_transition μ ν z : ExtPlane) = t203_ratio (A z) (B z)) :
    ∀ᶠ u in crb_reflectionBoundary μ h, cnf_finite A B h u ∈ gsans ν '' unitDiscExterior := by
  haveI : (crb_reflectionBoundary μ h).IsCountablyGenerated := by
    unfold crb_reflectionBoundary crb_diskBoundary; infer_instance
  by_contra hne
  rw [Filter.not_eventually] at hne
  obtain ⟨v, hv, hvn⟩ := Filter.frequently_iff_seq_forall.mp hne
  obtain ⟨eμ, Kμ, hKμ, heμ⟩ := cra_welding_extension hμ
  obtain ⟨eν, Kν, hKν, heν⟩ := cra_welding_extension hν
  obtain ⟨φ, -, a, ha, hal, -, f, g, -, hgK, -, hgl, -, Z, -, hW, ε, hε, hsep⟩ :=
    qd_pack hμ hν hP hp hC1 hpl hh hinf hb1 hb2 hA hB hode hrat eμ eν hKμ hKν heμ heν hv
  have hcb : closure unitDisc = closedBall (0 : ℂ) 1 := closure_ball 0 one_ne_zero
  have hcl : ∀ n, ‖eν.symm (cnf_finite A B h (v (φ n)))‖ ≤ 1 := by
    intro n
    have h1 := (qd_sides hν).2 (hvn (φ n))
    rw [← heν.image_eq, ← eν.image_closure, hcb] at h1
    obtain ⟨w, hw, hwe⟩ := h1
    rw [← hwe, eν.symm_apply_apply]
    exact mem_closedBall_zero_iff.mp hw
  have hsrc : ∀ n, cbl_source (a n) ((eν.symm (cnf_finite A B h (v (φ n))) - a n) / cbl_scale (a n)) =
      eν.symm (cnf_finite A B h (v (φ n))) := by
    intro n
    have hc := cbl_scale_ne_zero (ha n).1 (ha n).2
    simp only [cbl_source]; field_simp; ring
  have hWS : ∀ n, cbl_normalized eν (a n) ((eν.symm (cnf_finite A B h (v (φ n))) - a n) / cbl_scale (a n)) =
      (cnf_finite A B h (v (φ n)) - eν (a n)) / (eν (cbl_source (a n) 1) - eν (a n)) := by
    intro n
    unfold cbl_normalized
    rw [hsrc, eν.apply_symm_apply]
  obtain ⟨S0, hgS, hS⟩ := qd_inv_tendsto (fun n => cbl_normalized_plane eν hKν (ha n).1 (ha n).2) hgK hgl
    (S := fun n => (eν.symm (cnf_finite A B h (v (φ n))) - a n) / cbl_scale (a n))
    (hW.congr fun n => (hWS n).symm)
  have hre := qd_re_limit ha hal hS (Eventually.of_forall fun n => by rw [hsrc]; exact hcl n)
  have h1 := hsep S0 hre
  rw [hgS, sub_self, norm_zero] at h1
  linarith

/-- **(B1–B3) The injective collar.** There is `R > 1` such that on `C = 𝗀_μ(1 < |w| < R)` the Ahlfors map `N` is
finite, `3`-q.c., injective, maps into `Ω_ν* = 𝗀_ν(𝔻*)`, has dilatation `crn_coefficient` with Beltrami denominator
`≥ 1/2`, and has boundary values `H` on `∂Ω` for every q.c. homeomorphism `H` extending `f^ν ∘ (f^μ)⁻¹`. -/
theorem qd_collar {μ ν : LinfStar} (hμ : μ ∈ LinfStarBall) (hν : ν ∈ LinfStarBall)
    (hP : AInf.toFun (bersPhi ν - bersPhi μ) ∈ A2fun unitDisc)
    {h : ℂ → ℂ} {K C₀ : ℝ} {p : ℂ} (hp : p ∈ fsans μ '' unitDisc)
    (hC1 : ContDiffOn ℝ 1 h (gsans μ '' unitDiscExterior))
    (hpl : IsPlanarQCReflection (gsans μ '' unitDiscExterior) ((fsans μ '' unitDisc) \ {p}) h K)
    (hh : IsQCReflection (fsans μ '' unitDisc) (gsans μ '' unitDiscExterior) h)
    (hinf : Tendsto h (cocompact ℂ ⊓ 𝓟 (gsans μ '' unitDiscExterior)) (𝓝 p))
    (hb1 : ∀ u ∈ gsans μ '' unitDiscExterior, ‖u - h u‖ ^ 2 * ‖fderiv ℝ h u‖ *
      poincareDensity (fsans μ '' unitDisc) (h u) ^ 2 ≤ C₀)
    (hb2 : ∀ u ∈ gsans μ '' unitDiscExterior, ‖u - h u‖ ^ 2 * ‖dzbar h u‖ *
      poincareDensity (fsans μ '' unitDisc) (h u) ^ 2 ≤ C₀)
    {A B : ℂ → ℂ} (hA : DifferentiableOn ℂ A (fsans μ '' unitDisc))
    (hB : DifferentiableOn ℂ B (fsans μ '' unitDisc))
    (hode : ∀ z ∈ fsans μ '' unitDisc,
      deriv (deriv A) z + schwarzianHol (crs_transition μ ν) z / 2 * A z = 0 ∧
      deriv (deriv B) z + schwarzianHol (crs_transition μ ν) z / 2 * B z = 0 ∧
      A z * deriv B z - B z * deriv A z = 1)
    (hrat : ∀ z ∈ fsans μ '' unitDisc, (crs_transition μ ν z : ExtPlane) = t203_ratio (A z) (B z)) :
    ∃ R : ℝ, 1 < R ∧
      (∀ u ∈ gsans μ '' annulus 1 R, B (h u) + (u - h u) * deriv B (h u) ≠ 0) ∧
      (∀ u ∈ gsans μ '' annulus 1 R, (1 / 2 : ℝ) ≤
        ‖1 + (u - h u) ^ 2 * (schwarzianHol (crs_transition μ ν) (h u) / 2) * dz h u‖) ∧
      (∀ u ∈ gsans μ '' annulus 1 R, complexDilatation (cnf_finite A B h) u =
        crn_coefficient (schwarzianHol (crs_transition μ ν)) h u) ∧
      IsKQC (cnf_finite A B h) (gsans μ '' annulus 1 R) 3 ∧
      InjOn (cnf_finite A B h) (gsans μ '' annulus 1 R) ∧
      MapsTo (cnf_finite A B h) (gsans μ '' annulus 1 R) (gsans ν '' unitDiscExterior) ∧
      ∀ H : ℂ ≃ₜ ℂ, (∀ w ∈ unitDisc, H (fsans μ w) = fsans ν w) →
        ∀ z ∈ frontier (fsans μ '' unitDisc),
          Tendsto (cnf_finite A B h) (𝓝[gsans μ '' annulus 1 R] z) (𝓝 (H z)) := by
  have hC₀ : 0 ≤ C₀ := by
    have h2 : gsans μ 2 ∈ gsans μ '' unitDiscExterior :=
      ⟨2, show (1 : ℝ) < ‖(2 : ℂ)‖ by norm_num, rfl⟩
    exact le_trans (by positivity) (hb1 _ h2)
  have hf := S2C.s2c_conf_f hμ
  have hΩ : IsOpen (fsans μ '' unitDisc) := hf.isOpen isOpen_ball
  have hEo : IsOpen (gsans μ '' unitDiscExterior) := (l29b_open_disjoint hμ).2.1
  have hsmall : Tendsto (fun u => ‖schwarzianHol (crs_transition μ ν) (h u)‖ * ‖u - h u‖ ^ 2 *
      ‖fderiv ℝ h u‖) (crb_reflectionBoundary μ h) (𝓝 0) :=
    crb_reflection_error_tendsto_zero hμ hP (fun _ hw => crs_schwarzian_pullback hμ hν hw) hh.2.1 hC₀ hb1
  obtain ⟨Cc, hCc⟩ := qd_contact hμ hν hP hp hC1 hpl hh hinf hb1 hb2 hA hB hode hrat
  have hEv : ∀ᶠ u in crb_reflectionBoundary μ h,
      (B (h u) + (u - h u) * deriv B (h u) ≠ 0) ∧
      (‖schwarzianHol (crs_transition μ ν) (h u)‖ * ‖u - h u‖ ^ 2 * ‖fderiv ℝ h u‖ < 2 * (1 / 4) ∧
        ‖(u - h u) ^ 2 * (schwarzianHol (crs_transition μ ν) (h u) / 2) * dz h u‖ < 1 / 4 ∧
        1 - 1 / 4 ≤ ‖1 + (u - h u) ^ 2 * (schwarzianHol (crs_transition μ ν) (h u) / 2) * dz h u‖ ∧
        1 + (u - h u) ^ 2 * (schwarzianHol (crs_transition μ ν) (h u) / 2) * dz h u ≠ 0) ∧
      cnf_finite A B h u ∈ gsans ν '' unitDiscExterior := by
    filter_upwards [hCc, crb_denominator_eventually hsmall (k := 1 / 4) (by norm_num) (by norm_num),
      qd_side_ev hμ hν hP hp hC1 hpl hh hinf hb1 hb2 hA hB hode hrat] with u h1 h2 h3
    exact ⟨h1.1, h2, h3⟩
  obtain ⟨R1, hR1, hcol⟩ := crc_eventually_collar ((crc_reflection_tendsto hμ hh) hEv)
  -- an injectivity radius, by contradiction with `qd_inj_seq`
  have hinj : ∃ R2 : ℝ, 1 < R2 ∧ InjOn (cnf_finite A B h) (gsans μ '' annulus 1 R2) := by
    by_contra hno
    push_neg at hno
    have hP' : ∀ n : ℕ, ∃ x ∈ gsans μ '' annulus 1 (1 + 1 / ((n : ℝ) + 1)),
        ∃ y ∈ gsans μ '' annulus 1 (1 + 1 / ((n : ℝ) + 1)),
          cnf_finite A B h x = cnf_finite A B h y ∧ x ≠ y := by
      intro n
      have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
      have := hno (1 + 1 / ((n : ℝ) + 1)) (by linarith)
      simp only [InjOn, not_forall] at this
      obtain ⟨x, hx, y, hy, hxy, hne⟩ := this
      exact ⟨x, hx, y, hy, hxy, hne⟩
    choose x hx y hy hxy hne using hP'
    have hseq : ∀ z : ℕ → ℂ, (∀ n : ℕ, z n ∈ gsans μ '' annulus 1 (1 + 1 / ((n : ℝ) + 1))) →
        Tendsto z atTop (crb_reflectionBoundary μ h) := by
      intro z hz
      choose w hw hwz using hz
      have hwl : Tendsto w atTop crc_exteriorBoundary := by
        unfold crc_exteriorBoundary
        refine tendsto_inf.mpr ⟨tendsto_comap_iff.mpr ?_, tendsto_principal.mpr
          (Eventually.of_forall fun n => (hw n).1)⟩
        have hup : Tendsto (fun n : ℕ => 1 + 1 / ((n : ℝ) + 1)) atTop (𝓝 1) := by
          have : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
            tendsto_one_div_add_atTop_nhds_zero_nat
          simpa using this.const_add 1
        exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup
          (fun n => (hw n).1.le) (fun n => (hw n).2.le)
      exact ((crc_reflection_tendsto hμ hh).comp hwl).congr hwz
    have hev := qd_inj_seq hμ hν hP hp hC1 hpl hh hinf hb1 hb2 hA hB hode hrat (hseq x hx) (hseq y hy) hne
    obtain ⟨n, hn⟩ := hev.exists
    exact hn (hxy n)
  obtain ⟨R2, hR2, hinj2⟩ := hinj
  set R := min R1 R2 with hRdef
  have hR : 1 < R := lt_min hR1 hR2
  have hCsub : ∀ u ∈ gsans μ '' annulus 1 R, ∃ w, 1 < ‖w‖ ∧ ‖w‖ < R1 ∧ u = gsans μ w := by
    rintro u ⟨w, hw, rfl⟩
    exact ⟨w, hw.1, lt_of_lt_of_le hw.2 (min_le_left _ _), rfl⟩
  have hCE : gsans μ '' annulus 1 R ⊆ gsans μ '' unitDiscExterior :=
    image_mono (fun w hw => hw.1)
  have hprop : ∀ u ∈ gsans μ '' annulus 1 R, (B (h u) + (u - h u) * deriv B (h u) ≠ 0) ∧
      (‖schwarzianHol (crs_transition μ ν) (h u)‖ * ‖u - h u‖ ^ 2 * ‖fderiv ℝ h u‖ < 2 * (1 / 4) ∧
        ‖(u - h u) ^ 2 * (schwarzianHol (crs_transition μ ν) (h u) / 2) * dz h u‖ < 1 / 4 ∧
        1 - 1 / 4 ≤ ‖1 + (u - h u) ^ 2 * (schwarzianHol (crs_transition μ ν) (h u) / 2) * dz h u‖ ∧
        1 + (u - h u) ^ 2 * (schwarzianHol (crs_transition μ ν) (h u) / 2) * dz h u ≠ 0) ∧
      cnf_finite A B h u ∈ gsans ν '' unitDiscExterior := by
    intro u hu
    obtain ⟨w, hw1, hw2, rfl⟩ := hCsub u hu
    exact hcol w hw1 hw2
  have hinjC : InjOn (cnf_finite A B h) (gsans μ '' annulus 1 R) :=
    hinj2.mono (image_mono fun w (hw : w ∈ annulus 1 R) =>
      (show w ∈ annulus 1 R2 from ⟨hw.1, lt_of_lt_of_le hw.2 (min_le_right _ _)⟩))
  have hCo : IsOpen (gsans μ '' annulus 1 R) := by
    have hg := S2C.s2c_conf_g hμ
    have hsub : annulus 1 R ⊆ unitDiscExterior := fun w hw => hw.1
    exact (show IsConformalOnto (gsans μ) (annulus 1 R) (gsans μ '' annulus 1 R) from
      ⟨hg.1.mono hsub, hg.2.1.mono hsub, rfl⟩).isOpen
      ((isOpen_lt continuous_const continuous_norm).inter (isOpen_lt continuous_norm continuous_const))
  -- pointwise derivative data
  have hAd : ∀ v ∈ fsans μ '' unitDisc, HasDerivAt A (deriv A v) v := fun v hv =>
    (hA.differentiableAt (hΩ.mem_nhds hv)).hasDerivAt
  have hBd : ∀ v ∈ fsans μ '' unitDisc, HasDerivAt B (deriv B v) v := fun v hv =>
    (hB.differentiableAt (hΩ.mem_nhds hv)).hasDerivAt
  have hA2 : ∀ v ∈ fsans μ '' unitDisc, HasDerivAt (deriv A)
      (-(schwarzianHol (crs_transition μ ν) v / 2 * A v)) v := by
    intro v hv
    have := ((hA.deriv hΩ).differentiableAt (hΩ.mem_nhds hv)).hasDerivAt
    rwa [show deriv (deriv A) v = -(schwarzianHol (crs_transition μ ν) v / 2 * A v) by
      linear_combination (hode _ hv).1] at this
  have hB2 : ∀ v ∈ fsans μ '' unitDisc, HasDerivAt (deriv B)
      (-(schwarzianHol (crs_transition μ ν) v / 2 * B v)) v := by
    intro v hv
    have := ((hB.deriv hΩ).differentiableAt (hΩ.mem_nhds hv)).hasDerivAt
    rwa [show deriv (deriv B) v = -(schwarzianHol (crs_transition μ ν) v / 2 * B v) by
      linear_combination (hode _ hv).2.1] at this
  have hhd : ∀ u ∈ gsans μ '' unitDiscExterior, DifferentiableAt ℝ h u := fun u hu =>
    (hC1.differentiableOn one_ne_zero u hu).differentiableAt (hEo.mem_nhds hu)
  have hdz : ∀ u ∈ gsans μ '' annulus 1 R,
      dz (cnf_finite A B h) u = -(1 + (u - h u) ^ 2 * (schwarzianHol (crs_transition μ ν) (h u) / 2) *
        dz h u) / (B (h u) + (u - h u) * deriv B (h u)) ^ 2 ∧
      dzbar (cnf_finite A B h) u = -((u - h u) ^ 2 * (schwarzianHol (crs_transition μ ν) (h u) / 2) *
        dzbar h u) / (B (h u) + (u - h u) * deriv B (h u)) ^ 2 := by
    intro u hu
    have hv := hh.2.1 (hCE hu)
    exact t203_dz_dzbar_F (hhd u (hCE hu)) (hAd _ hv) (hA2 _ hv) (hBd _ hv) (hB2 _ hv)
      (hode _ hv).2.2 (hprop u hu).1
  -- the `C¹` regularity of `N` on the collar
  have hcont : ContDiffOn ℝ 1 (cnf_finite A B h) (gsans μ '' annulus 1 R) := by
    have hAc : ContDiffOn ℝ 1 A (fsans μ '' unitDisc) :=
      ((hA.contDiffOn hΩ).of_le le_top).restrict_scalars ℝ
    have hA'c : ContDiffOn ℝ 1 (deriv A) (fsans μ '' unitDisc) :=
      (((hA.deriv hΩ).contDiffOn hΩ).of_le le_top).restrict_scalars ℝ
    have hBc : ContDiffOn ℝ 1 B (fsans μ '' unitDisc) :=
      ((hB.contDiffOn hΩ).of_le le_top).restrict_scalars ℝ
    have hB'c : ContDiffOn ℝ 1 (deriv B) (fsans μ '' unitDisc) :=
      (((hB.deriv hΩ).contDiffOn hΩ).of_le le_top).restrict_scalars ℝ
    have hhC : ContDiffOn ℝ 1 h (gsans μ '' annulus 1 R) := hC1.mono hCE
    have hmap : MapsTo h (gsans μ '' annulus 1 R) (fsans μ '' unitDisc) := fun u hu => hh.2.1 (hCE hu)
    have hnum := (hAc.comp hhC hmap).add ((contDiffOn_id.sub hhC).mul (hA'c.comp hhC hmap))
    have hden := (hBc.comp hhC hmap).add ((contDiffOn_id.sub hhC).mul (hB'c.comp hhC hmap))
    refine (hnum.mul (hden.inv fun u hu => (hprop u hu).1)).congr fun u _ => ?_
    simp only [cnf_finite, div_eq_mul_inv, Function.comp_apply, id, Pi.inv_apply]
  refine ⟨R, hR, fun u hu => (hprop u hu).1, fun u hu => ?_, fun u hu => ?_, ?_, hinjC,
    fun u hu => (hprop u hu).2.2, ?_⟩
  · have := (hprop u hu).2.1.2.2.1
    linarith
  · exact cnf_coefficient hΩ hA hB hode (hh.2.1 (hCE hu)) (hhd u (hCE hu)) (hprop u hu).1
  · refine isKQC_of_isC1Quasiconformal ⟨hCo, by norm_num, hcont,
      qcl_f_isHomeomorphOnto_of_injOn hCo (hcont.continuousOn) hinjC, fun u hu => ?_⟩
    obtain ⟨hdz1, hdz2⟩ := hdz u hu
    obtain ⟨hd0, ⟨hs1, hs2, hs3, hs4⟩, -⟩ := hprop u hu
    have hden : 0 < ‖B (h u) + (u - h u) * deriv B (h u)‖ := norm_pos_iff.mpr hd0
    have hzb : ‖(u - h u) ^ 2 * (schwarzianHol (crs_transition μ ν) (h u) / 2) * dzbar h u‖ ≤ 1 / 4 := by
      rw [norm_mul, norm_mul, norm_div, norm_pow, Complex.norm_ofNat]
      have hdb := (t203_norm_dz_add_dzbar_le (g := h) (z := u))
      have : ‖dzbar h u‖ ≤ ‖fderiv ℝ h u‖ := by linarith [norm_nonneg (dz h u)]
      nlinarith [norm_nonneg (schwarzianHol (crs_transition μ ν) (h u)), norm_nonneg (u - h u),
        mul_le_mul_of_nonneg_left this (mul_nonneg (sq_nonneg ‖u - h u‖)
          (norm_nonneg (schwarzianHol (crs_transition μ ν) (h u))))]
    have hdzn : ‖dz (cnf_finite A B h) u‖ = ‖1 + (u - h u) ^ 2 *
        (schwarzianHol (crs_transition μ ν) (h u) / 2) * dz h u‖ /
          ‖B (h u) + (u - h u) * deriv B (h u)‖ ^ 2 := by
      rw [hdz1, norm_div, norm_neg, norm_pow]
    have hdzbn : ‖dzbar (cnf_finite A B h) u‖ = ‖(u - h u) ^ 2 *
        (schwarzianHol (crs_transition μ ν) (h u) / 2) * dzbar h u‖ /
          ‖B (h u) + (u - h u) * deriv B (h u)‖ ^ 2 := by
      rw [hdz2, norm_div, norm_neg, norm_pow]
    have hlt : ‖dzbar (cnf_finite A B h) u‖ < ‖dz (cnf_finite A B h) u‖ := by
      rw [hdzn, hdzbn]
      apply div_lt_div_of_pos_right _ (by positivity)
      linarith
    refine ⟨hlt, ?_⟩
    have hmu : ‖complexDilatation (cnf_finite A B h) u‖ ≤ 1 / 3 := by
      rw [complexDilatation, norm_div, hdzn, hdzbn, div_div_div_cancel_right₀ (by positivity),
        div_le_iff₀ (by linarith)]
      linarith
    unfold dilatationQuotient
    rw [div_le_iff₀ (by linarith)]
    linarith
  · intro H hH z hz
    exact (qd_trace hμ hν hP hp hC1 hpl hh hinf hb1 hb2 hA hB hode hrat H hH hz).mono_left
      (nhdsWithin_mono _ hCE)

/-- A `C¹` bump on `ℂ` equal to `1` at `0`, vanishing off the unit disc, with bounded derivative. -/
theorem qd_bump : ∃ ψ : ℂ → ℝ, ContDiff ℝ 1 ψ ∧ ψ 0 = 1 ∧ (∀ z : ℂ, 1 ≤ ‖z‖ → ψ z = 0) ∧
    ∃ M : ℝ, 0 < M ∧ ∀ z, ‖fderiv ℝ ψ z‖ ≤ M := by
  let b : ContDiffBump (0 : ℂ) := ⟨1 / 2, 1, by norm_num, by norm_num⟩
  have hc : ContDiff ℝ 1 b := b.contDiff
  obtain ⟨C, hC⟩ := (hc.continuous_fderiv one_ne_zero).bounded_above_of_compact_support
    (b.hasCompactSupport.fderiv (𝕜 := ℝ))
  refine ⟨b, hc, b.one_of_mem_closedBall (by
      rw [mem_closedBall, dist_self]; show (0 : ℝ) ≤ 1 / 2; norm_num),
    fun z hz => b.zero_of_le_dist (by rw [dist_zero_right]; exact hz), max C 1, by positivity,
    fun z => (hC z).trans (le_max_left _ _)⟩

/-- **A small push.** `z ↦ z - v ψ((z - c)/δ)` is a `3`-q.c. homeomorphism moving `c` to `c - v` and fixing every
point at distance `≥ δ` from `c`, once `‖v‖ M ≤ δ/4`. -/
theorem qd_push1 : ∃ M : ℝ, 0 < M ∧ ∀ (c v : ℂ) (δ : ℝ), 0 < δ → ‖v‖ * M ≤ δ / 4 →
    ∃ P : ℂ ≃ₜ ℂ, IsKQC P univ 3 ∧ P c = c - v ∧ ∀ z, δ ≤ ‖z - c‖ → P z = z := by
  obtain ⟨ψ, hψ, hψ0, hψ1, M, hM, hMb⟩ := qd_bump
  refine ⟨M, hM, fun c v δ hδ hv => ?_⟩
  have hψd : Differentiable ℝ ψ := hψ.differentiable one_ne_zero
  have hψL : ∀ x y : ℂ, ‖ψ x - ψ y‖ ≤ M * ‖x - y‖ := fun x y =>
    Convex.norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℝ) (fun w _ => hψd w) (fun w _ => hMb w) convex_univ
      (mem_univ y) (mem_univ x)
  obtain ⟨Q, hQ⟩ : ∃ Q : ℂ → ℂ, Q = fun z => v * ((ψ ((z - c) / (δ : ℂ)) : ℝ) : ℂ) := ⟨_, rfl⟩
  have hQL : ∀ x y, ‖Q x - Q y‖ ≤ (1 / 4) * ‖x - y‖ := by
    intro x y
    rw [hQ]
    simp only
    rw [← mul_sub, norm_mul, ← Complex.ofReal_sub, Complex.norm_real]
    have h1 := hψL ((x - c) / (δ : ℂ)) ((y - c) / (δ : ℂ))
    rw [show (x - c) / (δ : ℂ) - (y - c) / (δ : ℂ) = (x - y) / (δ : ℂ) by ring, norm_div,
      Complex.norm_real, Real.norm_of_nonneg hδ.le] at h1
    calc ‖v‖ * ‖ψ ((x - c) / (δ : ℂ)) - ψ ((y - c) / (δ : ℂ))‖ ≤ ‖v‖ * (M * (‖x - y‖ / δ)) :=
          mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
      _ = (‖v‖ * M) * ‖x - y‖ / δ := by ring
      _ ≤ (δ / 4) * ‖x - y‖ / δ := by gcongr
      _ = 1 / 4 * ‖x - y‖ := by field_simp
  obtain ⟨P, hP⟩ : ∃ P : ℂ → ℂ, P = fun z => z - Q z := ⟨_, rfl⟩
  have hA : ApproximatesLinearOn P ((ContinuousLinearEquiv.refl ℝ ℂ : ℂ ≃L[ℝ] ℂ) : ℂ →L[ℝ] ℂ) univ
      (1 / 4 : NNReal) := by
    intro x _ y _
    have e : P x - P y - ((ContinuousLinearEquiv.refl ℝ ℂ : ℂ ≃L[ℝ] ℂ) : ℂ →L[ℝ] ℂ) (x - y) =
        -(Q x - Q y) := by
      rw [hP]; simp only [ContinuousLinearEquiv.coe_refl, ContinuousLinearMap.id_apply]; ring
    rw [e, norm_neg]
    have := hQL x y
    simpa using this
  have hN : (1 / 4 : NNReal) <
      ‖(((ContinuousLinearEquiv.refl ℝ ℂ : ℂ ≃L[ℝ] ℂ).symm : ℂ ≃L[ℝ] ℂ) : ℂ →L[ℝ] ℂ)‖₊⁻¹ := by
    rw [ContinuousLinearEquiv.refl_symm, ContinuousLinearEquiv.coe_refl, ContinuousLinearMap.nnnorm_id,
      inv_one]
    norm_num
  have hinj : InjOn P univ := hA.injOn (Or.inr hN)
  have hsurj : Function.Surjective P := hA.surjective (Or.inr hN)
  have hQc : ContDiff ℝ 1 Q := by
    rw [hQ]
    exact contDiff_const.mul (Complex.ofRealCLM.contDiff.comp
      (hψ.comp ((contDiff_id.sub contDiff_const).div_const _)))
  have hPc : ContDiff ℝ 1 P := by rw [hP]; exact contDiff_id.sub hQc
  have hQlip : LipschitzWith (1 / 4 : NNReal) Q := LipschitzWith.of_dist_le_mul fun x y => by
    rw [dist_eq_norm, dist_eq_norm]; push_cast; exact hQL x y
  have hdil : ∀ z, ‖dzbar P z‖ < ‖dz P z‖ ∧ dilatationQuotient P z ≤ 3 := by
    intro z
    have hQd : DifferentiableAt ℝ Q z := (hQc.differentiable one_ne_zero) z
    have hD : fderiv ℝ P z = ContinuousLinearMap.id ℝ ℂ - fderiv ℝ Q z := by
      rw [hP, show (fun z => z - Q z) = (fun z => id z - Q z) from rfl,
        fderiv_fun_sub differentiableAt_id hQd, fderiv_id]
    have hT : ‖fderiv ℝ Q z‖ ≤ 1 / 4 := by
      have := norm_fderiv_le_of_lipschitz ℝ hQlip (x₀ := z)
      simpa using this
    set T := fderiv ℝ Q z
    have h1 : ‖T 1‖ ≤ 1 / 4 := (T.le_opNorm 1).trans (by rw [norm_one, mul_one]; exact hT)
    have hI : ‖T Complex.I‖ ≤ 1 / 4 := (T.le_opNorm _).trans (by rw [Complex.norm_I, mul_one]; exact hT)
    have hdz : dz P z = 1 - (T 1 - Complex.I * T Complex.I) / 2 := by
      unfold dz; rw [hD]
      simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply]
      linear_combination (-(1 : ℂ) / 2) * Complex.I_sq
    have hdzb : dzbar P z = -((T 1 + Complex.I * T Complex.I) / 2) := by
      unfold dzbar; rw [hD]
      simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply]
      linear_combination (1 / 2 : ℂ) * Complex.I_sq
    have hn1 : ‖(T 1 - Complex.I * T Complex.I) / 2‖ ≤ 1 / 4 := by
      rw [norm_div, Complex.norm_ofNat]
      have := norm_sub_le (T 1) (Complex.I * T Complex.I)
      rw [norm_mul, Complex.norm_I, one_mul] at this
      linarith
    have hn2 : ‖(T 1 + Complex.I * T Complex.I) / 2‖ ≤ 1 / 4 := by
      rw [norm_div, Complex.norm_ofNat]
      have := norm_add_le (T 1) (Complex.I * T Complex.I)
      rw [norm_mul, Complex.norm_I, one_mul] at this
      linarith
    have hdzl : 3 / 4 ≤ ‖dz P z‖ := by
      rw [hdz]
      have := norm_sub_norm_le (1 : ℂ) ((T 1 - Complex.I * T Complex.I) / 2)
      rw [norm_one] at this
      linarith
    have hdzbl : ‖dzbar P z‖ ≤ 1 / 4 := by rw [hdzb, norm_neg]; exact hn2
    refine ⟨by linarith, ?_⟩
    have hmu : ‖complexDilatation P z‖ ≤ 1 / 3 := by
      rw [complexDilatation, norm_div, div_le_iff₀ (by linarith)]
      linarith
    unfold dilatationQuotient
    rw [div_le_iff₀ (by linarith)]
    linarith
  have hK : IsKQC P univ 3 := isKQC_of_isC1Quasiconformal ⟨isOpen_univ, by norm_num, hPc.contDiffOn,
    qcl_f_isHomeomorphOnto_of_injOn isOpen_univ hPc.continuous.continuousOn hinj, fun z _ => hdil z⟩
  obtain ⟨e, he⟩ := t203_pack_homeo hK (image_univ_of_surjective hsurj)
  refine ⟨e, by rw [he]; exact hK, ?_, fun z hz => ?_⟩
  · rw [he, hP, hQ]
    simp only [sub_self, zero_div, hψ0, Complex.ofReal_one, mul_one]
  · rw [he, hP, hQ]
    have h0 : ψ ((z - c) / (δ : ℂ)) = 0 := by
      apply hψ1
      rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hδ.le, le_div_iff₀ hδ, one_mul]
      exact hz
    simp only [h0, Complex.ofReal_zero, mul_zero, sub_zero]

/-- **The push.** For `‖b‖ < 1` there is a q.c. homeomorphism of `ℂ` moving `0` to `b` and fixing `‖z‖ ≥ ρ`, some
`ρ < 1`. -/
theorem qd_push {b : ℂ} (hb : ‖b‖ < 1) : ∃ (W : ℂ ≃ₜ ℂ) (K ρ : ℝ), IsKQC W univ K ∧ W 0 = b ∧ ρ < 1 ∧
    ∀ z, ρ ≤ ‖z‖ → W z = z := by
  obtain ⟨M, hM, hpush⟩ := qd_push1
  set δ : ℝ := (1 - ‖b‖) / 2 with hδ
  have hδ0 : 0 < δ := by rw [hδ]; linarith
  set ρ : ℝ := (1 + ‖b‖) / 2 with hρ
  obtain ⟨n, hn⟩ : ∃ n : ℕ, 4 * ‖b‖ * M / δ < n := exists_nat_gt _
  have hn0 : (0 : ℝ) < n := lt_of_le_of_lt (by positivity) hn
  have hstep : ‖-(b / n)‖ * M ≤ δ / 4 := by
    rw [norm_neg, norm_div, Complex.norm_natCast]
    rw [div_lt_iff₀ hδ0] at hn
    rw [div_mul_eq_mul_div, div_le_iff₀ hn0]
    nlinarith
  have hclaim : ∀ k : ℕ, k ≤ n → ∃ (W : ℂ ≃ₜ ℂ) (K : ℝ), IsKQC W univ K ∧ W 0 = (k / n : ℂ) * b ∧
      ∀ z, ρ ≤ ‖z‖ → W z = z := by
    intro k
    induction k with
    | zero =>
      intro _
      obtain ⟨P, hP, hP0, hPz⟩ := hpush 0 0 δ hδ0 (by rw [norm_zero, zero_mul]; positivity)
      refine ⟨P, 3, hP, by rw [hP0]; simp, fun z hz => hPz z ?_⟩
      rw [sub_zero]; linarith [norm_nonneg b]
    | succ k ih =>
      intro hk
      obtain ⟨W, K, hW, hW0, hWz⟩ := ih (Nat.le_of_succ_le hk)
      obtain ⟨P, hP, hPc, hPz⟩ := hpush ((k / n : ℂ) * b) (-(b / n)) δ hδ0 hstep
      have hck : ‖(k / n : ℂ) * b‖ ≤ ‖b‖ := by
        rw [norm_mul]
        have : ‖(k / n : ℂ)‖ ≤ 1 := by
          rw [norm_div, Complex.norm_natCast, Complex.norm_natCast, div_le_one hn0]
          exact_mod_cast (Nat.le_of_succ_le hk)
        nlinarith [norm_nonneg b]
      refine ⟨W.trans P, K * 3, ?_, ?_, fun z hz => ?_⟩
      · change IsKQC (P ∘ W) univ _
        exact thm7_1_comp hW hP (subset_univ _)
      · rw [Homeomorph.trans_apply, hW0, hPc]
        push_cast
        field_simp
        ring
      · rw [Homeomorph.trans_apply, hWz z hz]
        apply hPz
        have := norm_sub_norm_le z ((k / n : ℂ) * b)
        linarith
  obtain ⟨W, K, hW, hW0, hWz⟩ := hclaim n le_rfl
  refine ⟨W, K, ρ, hW, ?_, by rw [hρ]; linarith, hWz⟩
  rw [hW0, div_self (by exact_mod_cast hn0.ne'), one_mul]

/-- A homeomorphism extending `f^ν ∘ (f^μ)⁻¹` maps `Ω_μ*` into `Ω_ν*`. -/
theorem qd_side_homeo {μ ν : LinfStar} (hμ : μ ∈ LinfStarBall) (hν : ν ∈ LinfStarBall) (X : ℂ ≃ₜ ℂ)
    (hX : ∀ w ∈ unitDisc, X (fsans μ w) = fsans ν w) :
    ∀ x ∈ gsans μ '' unitDiscExterior, X x ∈ gsans ν '' unitDiscExterior := by
  intro x hx
  have himg : X '' (fsans μ '' unitDisc) = fsans ν '' unitDisc := by
    rw [image_image]; exact image_congr hX
  have hcl : X '' closure (fsans μ '' unitDisc) = closure (fsans ν '' unitDisc) := by
    rw [X.image_closure, himg]
  have hxn : x ∉ closure (fsans μ '' unitDisc) := by
    intro hc
    have hEo : IsOpen (gsans μ '' unitDiscExterior) := (l29b_open_disjoint hμ).2.1
    obtain ⟨y, hy⟩ := mem_closure_iff.mp hc _ hEo hx
    exact (qd_sides hμ).1.le_bot ⟨hy.2, hy.1⟩
  by_contra hn
  have h1 := (qd_sides hν).2 hn
  rw [← hcl] at h1
  obtain ⟨y, hy, hyx⟩ := h1
  exact hxn (X.injective hyx ▸ hy)

/-- A plane homeomorphism preserving `𝔻*` both ways preserves the closed disc, the circle and the open disc. -/
theorem qd_disc_pres (X : ℂ ≃ₜ ℂ) (h1 : ∀ w : ℂ, 1 < ‖w‖ → 1 < ‖X w‖)
    (h2 : ∀ w : ℂ, 1 < ‖w‖ → 1 < ‖X.symm w‖) :
    (∀ w : ℂ, ‖w‖ ≤ 1 → ‖X w‖ ≤ 1) ∧ (∀ w : ℂ, ‖w‖ = 1 → ‖X w‖ = 1) ∧ (∀ w : ℂ, ‖w‖ < 1 → ‖X w‖ < 1) := by
  have hle : ∀ Y : ℂ ≃ₜ ℂ, (∀ w : ℂ, 1 < ‖w‖ → 1 < ‖Y.symm w‖) → ∀ w : ℂ, ‖w‖ ≤ 1 → ‖Y w‖ ≤ 1 := by
    intro Y hY w hw
    by_contra hc
    push_neg at hc
    have h3 := hY _ hc
    rw [Y.symm_apply_apply] at h3
    linarith
  have hge : ∀ Y : ℂ ≃ₜ ℂ, (∀ w : ℂ, 1 < ‖w‖ → 1 < ‖Y w‖) → ∀ w : ℂ, ‖w‖ = 1 → 1 ≤ ‖Y w‖ := by
    intro Y hY w hw
    have h0 : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
    have hseq : Tendsto (fun n : ℕ => ((1 + 1 / ((n : ℝ) + 1) : ℝ) : ℂ) * w) atTop (𝓝 w) := by
      have h3 := ((Complex.continuous_ofReal.tendsto (1 + 0)).comp (h0.const_add 1)).mul_const w
      simpa using h3
    refine ge_of_tendsto ((Y.continuous.tendsto w).comp hseq).norm (Eventually.of_forall fun n => (hY _ ?_).le)
    rw [norm_mul, Complex.norm_real, hw, mul_one, Real.norm_of_nonneg (by positivity)]
    have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    linarith
  refine ⟨hle X h2, fun w hw => le_antisymm (hle X h2 w hw.le) (hge X h1 w hw), fun w hw => ?_⟩
  refine lt_of_le_of_ne (hle X h2 w hw.le) (fun heq => ?_)
  have h3 := hge X.symm h2 (X w) heq
  rw [X.symm_apply_apply] at h3
  linarith

/-- The circle reflection `σ z = 1/z̄`. -/
theorem qd_sigma {z : ℂ} (hz : z ≠ 0) :
    (conj ((conj z)⁻¹))⁻¹ = z ∧ ‖(conj z)⁻¹‖ = ‖z‖⁻¹ ∧ (conj z)⁻¹ ≠ 0 := by
  refine ⟨by rw [map_inv₀, Complex.conj_conj, inv_inv], by rw [norm_inv, Complex.norm_conj], ?_⟩
  exact inv_ne_zero ((map_ne_zero _).mpr hz)

theorem qd_sigma_circle {ζ : ℂ} (hζ : ‖ζ‖ = 1) : (conj ζ)⁻¹ = ζ := by
  apply inv_eq_of_mul_eq_one_right
  rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, hζ]
  norm_num

/-- Quasiconformality of the `σ`-conjugate `z ↦ σ(X(σ z))`. -/
theorem qd_conjinv_qc {X : ℂ → ℂ} {U D : Set ℂ} {K : ℝ} (hX : IsKQC X U K) (hD : IsOpen D)
    (h0 : (0 : ℂ) ∉ D) (hDU : ∀ z ∈ D, (conj z)⁻¹ ∈ U) (hX0 : ∀ u ∈ U, X u ≠ 0) :
    IsKQC (fun z => (conj (X ((conj z)⁻¹)))⁻¹) D K := by
  have hinv : ∀ V : Set ℂ, IsOpen V → (0 : ℂ) ∉ V → IsKQC (fun w : ℂ => w⁻¹) V 1 := by
    intro V hV h0V
    refine ad_isKQC_congr (nx_isKQC_restrict (b4_qc_invShift_isKQC 0) hV fun w hw hw0 => h0V ?_)
      (fun w _ => by simp)
    rw [mem_singleton_iff] at hw0
    rwa [hw0] at hw
  have hD' : IsOpen (conj ⁻¹' D) := hD.preimage Complex.continuous_conj
  have h0' : (0 : ℂ) ∉ conj ⁻¹' D := by
    intro h
    rw [mem_preimage, map_zero] at h
    exact h0 h
  have hs1 : (fun w : ℂ => w⁻¹) '' (conj ⁻¹' D) ⊆ U := by
    rintro _ ⟨w, hw, rfl⟩
    have h3 := hDU (conj w) hw
    rwa [Complex.conj_conj] at h3
  have h2 := thm7_1_comp (hinv _ hD' h0') hX hs1
  have hs2 : (X ∘ fun w : ℂ => w⁻¹) '' (conj ⁻¹' D) ⊆ {0}ᶜ := by
    rintro _ ⟨w, hw, rfl⟩
    exact hX0 _ (hs1 ⟨w, hw, rfl⟩)
  have h3 := thm7_1_comp h2 (hinv {0}ᶜ isOpen_compl_singleton (by simp)) hs2
  have h4 := abR_x_isKQC_conj h3
  have hDD : conj ⁻¹' (conj ⁻¹' D) = D := by
    ext z; simp
  rw [hDD, one_mul, mul_one] at h4
  refine ad_isKQC_congr h4 (fun z _ => ?_)
  simp only [Function.comp_apply, map_inv₀]

/-- The `ExtPlane` extension of a collar map with prescribed circle values (input of S35
`annulus_extension_extends`). -/
theorem qd_Gext {g : ℂ → ℂ} {Ψ : ℂ ≃ₜ ℂ} {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1)
    (hgc : ContinuousOn g {z : ℂ | r ≤ ‖z‖ ∧ ‖z‖ < 1}) (hgi : InjOn g {z : ℂ | r ≤ ‖z‖ ∧ ‖z‖ < 1})
    (hgD : ∀ z : ℂ, r ≤ ‖z‖ → ‖z‖ < 1 → ‖g z‖ < 1) (hΨ : ∀ ζ : ℂ, ‖ζ‖ = 1 → ‖Ψ ζ‖ = 1)
    (hlim : ∀ ζ : ℂ, ‖ζ‖ = 1 → Tendsto g (𝓝[{z : ℂ | r ≤ ‖z‖ ∧ ‖z‖ < 1}] ζ) (𝓝 (Ψ ζ))) :
    ∃ G : ExtPlane → ExtPlane, IsHomeoExtension g (annulus r 1) (g '' annulus r 1) G ∧
      ∀ ζ : ℂ, ‖ζ‖ = 1 → G ζ = Ψ.onePointCongr ζ := by
  have _ := hr0
  obtain ⟨G0, hG0⟩ : ∃ G0 : ℂ → ℂ, G0 = fun z => if ‖z‖ < 1 then g z else Ψ z := ⟨_, rfl⟩
  set S : Set ℂ := {z : ℂ | r ≤ ‖z‖ ∧ ‖z‖ < 1} with hS
  set Kc : Set ℂ := {z : ℂ | r ≤ ‖z‖ ∧ ‖z‖ ≤ 1} with hKc
  have hKcc : IsCompact Kc := Metric.isCompact_of_isClosed_isBounded
    ((isClosed_le continuous_const continuous_norm).inter (isClosed_le continuous_norm continuous_const))
    (isBounded_closedBall.subset fun z hz => mem_closedBall_zero_iff.mpr hz.2)
  have hG0c : ContinuousOn G0 Kc := by
    intro z hz
    rcases hz.2.lt_or_eq with h1 | h1
    · have hev : G0 =ᶠ[𝓝 z] g := by
        filter_upwards [(isOpen_lt continuous_norm continuous_const).mem_nhds h1] with w hw
        rw [hG0]; simp only [if_pos (show ‖w‖ < 1 from hw)]
      have hmem : S ∈ 𝓝[Kc] z := mem_nhdsWithin.mpr ⟨{w : ℂ | ‖w‖ < 1},
        isOpen_lt continuous_norm continuous_const, h1, fun w hw => ⟨hw.2.1, hw.1⟩⟩
      have hgz : ContinuousWithinAt g Kc z := (hgc z ⟨hz.1, h1⟩).mono_of_mem_nhdsWithin hmem
      exact hgz.congr_of_eventuallyEq (eventually_nhdsWithin_of_eventually_nhds hev) hev.eq_of_nhds
    · have hz1 : G0 z = Ψ z := by rw [hG0]; simp only [h1, lt_irrefl, if_false]
      have hT : ContinuousWithinAt G0 {w : ℂ | ‖w‖ = 1} z :=
        Ψ.continuous.continuousAt.continuousWithinAt.congr (fun w hw => by
          rw [hG0]; simp only [show ‖w‖ = 1 from hw, lt_irrefl, if_false]) hz1
      have hSz : ContinuousWithinAt G0 S z := by
        show Tendsto G0 (𝓝[S] z) (𝓝 (G0 z))
        rw [hz1]
        refine (hlim z h1).congr' ?_
        filter_upwards [self_mem_nhdsWithin] with w hw
        rw [hG0]; simp only [if_pos hw.2]
      exact (continuousWithinAt_union.mpr ⟨hSz, hT⟩).mono
        (fun w hw => (hw.2.lt_or_eq).imp (fun h => ⟨hw.1, h⟩) id)
  have hG0i : InjOn G0 Kc := by
    intro x hx y hy hxy
    rw [hG0] at hxy
    simp only at hxy
    rcases hx.2.lt_or_eq with hx1 | hx1 <;> rcases hy.2.lt_or_eq with hy1 | hy1
    · rw [if_pos hx1, if_pos hy1] at hxy
      exact hgi ⟨hx.1, hx1⟩ ⟨hy.1, hy1⟩ hxy
    · rw [if_pos hx1, if_neg (by rw [hy1]; exact lt_irrefl _)] at hxy
      have h1 := hgD x hx.1 hx1
      rw [hxy, hΨ y hy1] at h1
      exact absurd h1 (lt_irrefl _)
    · rw [if_neg (by rw [hx1]; exact lt_irrefl _), if_pos hy1] at hxy
      have h1 := hgD y hy.1 hy1
      rw [← hxy, hΨ x hx1] at h1
      exact absurd h1 (lt_irrefl _)
    · rw [if_neg (by rw [hx1]; exact lt_irrefl _), if_neg (by rw [hy1]; exact lt_irrefl _)] at hxy
      exact Ψ.injective hxy
  let G : ExtPlane → ExtPlane := fun x => x.elim OnePoint.infty (fun z => ((G0 z : ℂ) : ExtPlane))
  have hGc : ∀ z : ℂ, G z = ((G0 z : ℂ) : ExtPlane) := fun z => rfl
  have hcont : ContinuousOn G (toExt Kc) := by
    refine (OnePoint.isOpenEmbedding_coe.isInducing.continuousOn_image_iff).mpr ?_
    exact OnePoint.continuous_coe.comp_continuousOn hG0c
  have hinj : InjOn G (toExt Kc) := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ hxy
    rw [hGc, hGc] at hxy
    exact congrArg _ (hG0i hx hy (OnePoint.coe_injective hxy))
  have hsubA : annulus r 1 ⊆ Kc := fun z hz => ⟨hz.1.le, hz.2.le⟩
  have hcl : closure (toExt (annulus r 1)) ⊆ toExt Kc :=
    closure_minimal (image_mono hsubA) (hKcc.image OnePoint.continuous_coe).isClosed
  have hcont' := hcont.mono hcl
  have hGA : G '' toExt (annulus r 1) = toExt (g '' annulus r 1) := by
    simp only [toExt, image_image]
    refine image_congr fun z hz => ?_
    rw [hGc, hG0]
    simp only [if_pos hz.2]
  refine ⟨G, ⟨fun z hz => ?_, hcont', hinj.mono hcl, ?_⟩, fun ζ hζ => ?_⟩
  · rw [hGc, hG0]; simp only [if_pos hz.2]
  · apply Subset.antisymm
    · rw [← hGA]; exact hcont'.image_closure
    · rw [← hGA]
      exact closure_minimal (image_mono subset_closure)
        ((isClosed_closure.isCompact.image_of_continuousOn hcont').isClosed)
  · rw [hGc, hG0]
    simp only [hζ, lt_irrefl, if_false]
    rfl

/-- **Gluing across the unit circle.** `Ψ` on the closed disc and `σ ∘ f ∘ σ` outside define a q.c. homeomorphism of
`ℂ`, when `f` is a q.c. self-map of `𝔻` fixing `0` with boundary values `Ψ`. -/
theorem qd_theta (Ψ : ℂ ≃ₜ ℂ) {KΨ : ℝ} (hΨK : IsKQC Ψ univ KΨ)
    (hΨ1 : ∀ w : ℂ, 1 < ‖w‖ → 1 < ‖Ψ w‖) (hΨ2 : ∀ w : ℂ, 1 < ‖w‖ → 1 < ‖Ψ.symm w‖)
    {f : ℂ → ℂ} {Kf : ℝ} (hfK : IsKQC f unitDisc Kf) (hfs : f '' unitDisc = unitDisc) (hf0 : f 0 = 0)
    (hfb : ∀ ζ : ℂ, ‖ζ‖ = 1 → Tendsto f (𝓝[unitDisc] ζ) (𝓝 (Ψ ζ))) :
    ∃ (Θ : ℂ ≃ₜ ℂ) (K : ℝ), IsKQC Θ univ K ∧ (∀ w : ℂ, ‖w‖ ≤ 1 → Θ w = Ψ w) ∧
      ∀ w : ℂ, 1 < ‖w‖ → Θ w = (conj (f ((conj w)⁻¹)))⁻¹ := by
  obtain ⟨hcl, hcirc, -⟩ := qd_disc_pres Ψ hΨ1 hΨ2
  obtain ⟨hcl', -, -⟩ := qd_disc_pres Ψ.symm hΨ2 (by simpa using hΨ1)
  have hfc : ContinuousOn f unitDisc := hfK.2.2.1.1
  have hfi : InjOn f unitDisc := hfK.2.2.1.2.1
  have hmapf : ∀ s ∈ unitDisc, f s ∈ unitDisc := fun s hs => hfs ▸ mem_image_of_mem f hs
  have hfne : ∀ s ∈ unitDisc, s ≠ 0 → f s ≠ 0 := fun s hs hs0 h0 =>
    hs0 (hfi hs (mem_ball_self one_pos) (h0.trans hf0.symm))
  -- the reflection
  have hσD : ∀ w : ℂ, 1 < ‖w‖ → (conj w)⁻¹ ∈ unitDisc ∧ (conj w)⁻¹ ≠ 0 := by
    intro w hw
    have hw0 : w ≠ 0 := norm_pos_iff.mp (by linarith)
    obtain ⟨-, hn, hne⟩ := qd_sigma hw0
    refine ⟨mem_ball_zero_iff.mpr ?_, hne⟩
    rw [hn]; exact inv_lt_one_of_one_lt₀ hw
  have hσout : ∀ s : ℂ, s ∈ unitDisc → s ≠ 0 → 1 < ‖(conj s)⁻¹‖ := by
    intro s hs hs0
    rw [(qd_sigma hs0).2.1]
    exact one_lt_inv_iff₀.mpr ⟨norm_pos_iff.mpr hs0, mem_ball_zero_iff.mp hs⟩
  have hσc : ∀ z : ℂ, z ≠ 0 → ContinuousAt (fun z : ℂ => (conj z)⁻¹) z := fun z hz =>
    (Complex.continuous_conj.continuousAt).inv₀ ((map_ne_zero _).mpr hz)
  obtain ⟨Θ0, hΘ0⟩ : ∃ Θ0 : ℂ → ℂ, Θ0 = fun w => if 1 < ‖w‖ then (conj (f ((conj w)⁻¹)))⁻¹ else Ψ w :=
    ⟨_, rfl⟩
  have hout : ∀ w : ℂ, 1 < ‖w‖ → Θ0 w = (conj (f ((conj w)⁻¹)))⁻¹ := fun w hw => by
    rw [hΘ0]; simp only [if_pos hw]
  have hin : ∀ w : ℂ, ‖w‖ ≤ 1 → Θ0 w = Ψ w := fun w hw => by
    rw [hΘ0]; simp only [if_neg (not_lt.mpr hw)]
  have houtv : ∀ w : ℂ, 1 < ‖w‖ → 1 < ‖Θ0 w‖ := fun w hw => by
    rw [hout w hw]
    exact hσout _ (hmapf _ (hσD w hw).1) (hfne _ (hσD w hw).1 (hσD w hw).2)
  -- injectivity
  have hinj : Function.Injective Θ0 := by
    intro x y hxy
    by_cases hx : 1 < ‖x‖ <;> by_cases hy : 1 < ‖y‖
    · rw [hout x hx, hout y hy] at hxy
      have h1 := congrArg (fun z : ℂ => (conj z)⁻¹) hxy
      try simp only at h1
      rw [(qd_sigma (hfne _ (hσD x hx).1 (hσD x hx).2)).1,
        (qd_sigma (hfne _ (hσD y hy).1 (hσD y hy).2)).1] at h1
      have h2 := hfi (hσD x hx).1 (hσD y hy).1 h1
      have h3 := congrArg (fun z : ℂ => (conj z)⁻¹) h2
      try simp only at h3
      rwa [(qd_sigma (norm_pos_iff.mp (by linarith))).1, (qd_sigma (norm_pos_iff.mp (by linarith))).1] at h3
    · have h1 := houtv x hx
      rw [hxy, hin y (not_lt.mp hy)] at h1
      linarith [hcl y (not_lt.mp hy)]
    · have h1 := houtv y hy
      rw [← hxy, hin x (not_lt.mp hx)] at h1
      linarith [hcl x (not_lt.mp hx)]
    · rw [hin x (not_lt.mp hx), hin y (not_lt.mp hy)] at hxy
      exact Ψ.injective hxy
  -- surjectivity
  have hsurj : Function.Surjective Θ0 := by
    intro y
    by_cases hy : 1 < ‖y‖
    · obtain ⟨hyD, hy0⟩ := hσD y hy
      rw [← hfs] at hyD
      obtain ⟨s, hs, hfs'⟩ := hyD
      have hs0 : s ≠ 0 := fun h0 => hy0 (by rw [← hfs', h0, hf0])
      refine ⟨(conj s)⁻¹, ?_⟩
      rw [hout _ (hσout s hs hs0), (qd_sigma hs0).1, hfs', (qd_sigma (norm_pos_iff.mp (by linarith))).1]
    · refine ⟨Ψ.symm y, ?_⟩
      rw [hin _ (hcl' y (not_lt.mp hy)), Ψ.apply_symm_apply]
  -- continuity
  have hcont : Continuous Θ0 := by
    rw [continuous_iff_continuousAt]
    intro w
    rcases lt_trichotomy ‖w‖ 1 with hw | hw | hw
    · have hev : Θ0 =ᶠ[𝓝 w] Ψ := by
        filter_upwards [(isOpen_lt continuous_norm continuous_const).mem_nhds hw] with z hz
        exact hin z (le_of_lt hz)
      exact (Ψ.continuous.continuousAt).congr hev.symm
    · have hw0 : w ≠ 0 := norm_ne_zero_iff.mp (by rw [hw]; norm_num)
      have hσw : (conj w)⁻¹ = w := qd_sigma_circle hw
      have hΨw : ‖Ψ w‖ = 1 := hcirc w hw
      have hT : ContinuousWithinAt Θ0 {z : ℂ | ‖z‖ ≤ 1} w :=
        Ψ.continuous.continuousAt.continuousWithinAt.congr (fun z hz => hin z hz) (hin w hw.le)
      have hS : ContinuousWithinAt Θ0 {z : ℂ | 1 < ‖z‖} w := by
        show Tendsto Θ0 (𝓝[{z : ℂ | 1 < ‖z‖}] w) (𝓝 (Θ0 w))
        rw [hin w hw.le]
        have h1 : Tendsto (fun z : ℂ => (conj z)⁻¹) (𝓝[{z : ℂ | 1 < ‖z‖}] w) (𝓝[unitDisc] w) := by
          refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
          · have := (hσc w hw0).tendsto
            rw [hσw] at this
            exact this.mono_left nhdsWithin_le_nhds
          · filter_upwards [self_mem_nhdsWithin] with z hz
            exact (hσD z hz).1
        have h2 := (hfb w hw).comp h1
        have h3 := ((hσc _ (norm_ne_zero_iff.mp (by rw [hΨw]; norm_num))).tendsto).comp h2
        rw [qd_sigma_circle hΨw] at h3
        refine h3.congr' ?_
        filter_upwards [self_mem_nhdsWithin] with z hz
        exact (hout z hz).symm
      have hU := continuousWithinAt_union.mpr ⟨hS, hT⟩
      rw [show {z : ℂ | 1 < ‖z‖} ∪ {z : ℂ | ‖z‖ ≤ 1} = univ by
        ext z; simp only [mem_union, mem_setOf_eq, mem_univ, iff_true]; exact (lt_or_ge 1 ‖z‖)] at hU
      exact continuousWithinAt_univ _ _ |>.mp hU
    · have hev : Θ0 =ᶠ[𝓝 w] fun z => (conj (f ((conj z)⁻¹)))⁻¹ := by
        filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds hw] with z hz
        exact hout z hz
      have hw0 : w ≠ 0 := norm_pos_iff.mp (by linarith)
      obtain ⟨hD, hne⟩ := hσD w hw
      have hfa : ContinuousAt f ((conj w)⁻¹) := hfc.continuousAt (isOpen_ball.mem_nhds hD)
      have h2 : ContinuousAt (fun z : ℂ => f ((conj z)⁻¹)) w :=
        ContinuousAt.comp (f := fun z : ℂ => (conj z)⁻¹) hfa (hσc w hw0)
      have hc : ContinuousAt (fun z : ℂ => (conj (f ((conj z)⁻¹)))⁻¹) w :=
        ContinuousAt.comp (f := fun z : ℂ => f ((conj z)⁻¹)) (g := fun z : ℂ => (conj z)⁻¹)
          (hσc _ (hfne _ hD hne)) h2
      exact hc.congr hev.symm
  -- quasiconformality on the two sides
  have hhom : IsHomeomorphOnto Θ0 univ univ := by
    have h1 := qcl_f_isHomeomorphOnto_of_injOn isOpen_univ hcont.continuousOn hinj.injOn
    rwa [image_univ_of_surjective hsurj] at h1
  have hKin : IsKQC Θ0 unitDisc KΨ :=
    ad_isKQC_congr (nx_isKQC_restrict hΨK isOpen_ball (subset_univ _))
      (fun w hw => hin w (mem_ball_zero_iff.mp hw).le)
  have hU : IsOpen (unitDisc \ {(0 : ℂ)}) := isOpen_ball.sdiff isClosed_singleton
  have hKout : IsKQC Θ0 {z : ℂ | 1 < ‖z‖} Kf := by
    refine ad_isKQC_congr (qd_conjinv_qc (nx_isKQC_restrict hfK hU diff_subset)
      (isOpen_lt continuous_const continuous_norm) (by simp) (fun z hz => ⟨(hσD z hz).1, (hσD z hz).2⟩)
      (fun u hu => hfne u hu.1 hu.2)) (fun w hw => hout w hw)
  have hΘK : IsKQC Θ0 univ (max KΨ Kf) :=
    abR_removable hhom (hKin.mono (le_max_left _ _)) (hKout.mono (le_max_right _ _))
  obtain ⟨Θ, hΘ⟩ := t203_pack_homeo hΘK (image_univ_of_surjective hsurj)
  refine ⟨Θ, max KΨ Kf, by rw [hΘ]; exact hΘK, fun w hw => by rw [hΘ]; exact hin w hw,
    fun w hw => by rw [hΘ]; exact hout w hw⟩

/-- **(R4 fill)** A global q.c. homeomorphism extending `f^ν ∘ (f^μ)⁻¹` that equals the Ahlfors map on a thin
collar, together with the collar facts used for the energy. -/
theorem qd_fill {μ ν : LinfStar} (hμ : μ ∈ LinfStarBall) (hν : ν ∈ LinfStarBall)
    (hP : AInf.toFun (bersPhi ν - bersPhi μ) ∈ A2fun unitDisc)
    {h : ℂ → ℂ} {K C₀ : ℝ} {p : ℂ} (hp : p ∈ fsans μ '' unitDisc)
    (hC1 : ContDiffOn ℝ 1 h (gsans μ '' unitDiscExterior))
    (hpl : IsPlanarQCReflection (gsans μ '' unitDiscExterior) ((fsans μ '' unitDisc) \ {p}) h K)
    (hh : IsQCReflection (fsans μ '' unitDisc) (gsans μ '' unitDiscExterior) h)
    (hinf : Tendsto h (cocompact ℂ ⊓ 𝓟 (gsans μ '' unitDiscExterior)) (𝓝 p))
    (hb1 : ∀ u ∈ gsans μ '' unitDiscExterior, ‖u - h u‖ ^ 2 * ‖fderiv ℝ h u‖ *
      poincareDensity (fsans μ '' unitDisc) (h u) ^ 2 ≤ C₀)
    (hb2 : ∀ u ∈ gsans μ '' unitDiscExterior, ‖u - h u‖ ^ 2 * ‖dzbar h u‖ *
      poincareDensity (fsans μ '' unitDisc) (h u) ^ 2 ≤ C₀)
    {A B : ℂ → ℂ} (hA : DifferentiableOn ℂ A (fsans μ '' unitDisc))
    (hB : DifferentiableOn ℂ B (fsans μ '' unitDisc))
    (hode : ∀ z ∈ fsans μ '' unitDisc,
      deriv (deriv A) z + schwarzianHol (crs_transition μ ν) z / 2 * A z = 0 ∧
      deriv (deriv B) z + schwarzianHol (crs_transition μ ν) z / 2 * B z = 0 ∧
      A z * deriv B z - B z * deriv A z = 1)
    (hrat : ∀ z ∈ fsans μ '' unitDisc, (crs_transition μ ν z : ExtPlane) = t203_ratio (A z) (B z)) :
    ∃ (F : ℂ ≃ₜ ℂ) (KF : ℝ), IsKQC F univ KF ∧ (∀ w ∈ unitDisc, F (fsans μ w) = fsans ν w) ∧
      ∃ R₁ : ℝ, 1 < R₁ ∧ (∀ u ∈ gsans μ '' annulus 1 R₁, F u = cnf_finite A B h u) ∧
        (∀ u ∈ gsans μ '' annulus 1 R₁, (1 / 2 : ℝ) ≤
          ‖1 + (u - h u) ^ 2 * (schwarzianHol (crs_transition μ ν) (h u) / 2) * dz h u‖) ∧
        ∀ u ∈ gsans μ '' annulus 1 R₁, complexDilatation (cnf_finite A B h) u =
          crn_coefficient (schwarzianHol (crs_transition μ ν)) h u := by
  obtain ⟨R, hR, -, hhalf, hdilC, hqcN, hinjN, hmapsN, htrace⟩ :=
    qd_collar hμ hν hP hp hC1 hpl hh hinf hb1 hb2 hA hB hode hrat
  have hf := S2C.s2c_conf_f hμ
  have hΩo : IsOpen (fsans μ '' unitDisc) := hf.isOpen isOpen_ball
  have hcb : closure unitDisc = closedBall (0 : ℂ) 1 := closure_ball 0 one_ne_zero
  have hσc : ∀ z : ℂ, z ≠ 0 → ContinuousAt (fun z : ℂ => (conj z)⁻¹) z := fun z hz =>
    (Complex.continuous_conj.continuousAt).inv₀ ((map_ne_zero _).mpr hz)
  -- the charts
  obtain ⟨eμ, Kμ, hKμ, heμ⟩ := cra_welding_extension hμ
  obtain ⟨eν, Kν, hKν, heν⟩ := cra_welding_extension hν
  obtain ⟨H, hHd⟩ : ∃ H : ℂ ≃ₜ ℂ, H = eμ.symm.trans eν := ⟨_, rfl⟩
  have hH : ∀ w ∈ unitDisc, H (fsans μ w) = fsans ν w := by
    intro w hw; rw [hHd, Homeomorph.trans_apply, ← heμ hw, eμ.symm_apply_apply, heν hw]
  have hHs : ∀ w ∈ unitDisc, H.symm (fsans ν w) = fsans μ w := by
    intro w hw; rw [← hH w hw, H.symm_apply_apply]
  have hHK : IsKQC H univ (Kμ * Kν) := by
    rw [hHd]; change IsKQC (⇑eν ∘ ⇑eμ.symm) univ _
    exact thm7_1_comp (homeomorph_inverse_isKQC eμ hKμ) hKν (subset_univ _)
  obtain ⟨Gμ, KGμ, hKGμ, hGμ, -⟩ := crc_exterior_chart hμ
  obtain ⟨Gν, KGν, hKGν, hGν, -⟩ := crc_exterior_chart hν
  obtain ⟨Ψ, hΨd⟩ : ∃ Ψ : ℂ ≃ₜ ℂ, Ψ = Gμ.trans (H.trans Gν.symm) := ⟨_, rfl⟩
  have hΨa : ∀ w, Ψ w = Gν.symm (H (Gμ w)) := fun w => by rw [hΨd]; rfl
  have hΨsa : ∀ w, Ψ.symm w = Gμ.symm (H.symm (Gν w)) := fun w => by
    apply Ψ.injective
    rw [Ψ.apply_symm_apply, hΨa, Gμ.apply_symm_apply, H.apply_symm_apply, Gν.symm_apply_apply]
  have hΨK : IsKQC Ψ univ (KGμ * (Kμ * Kν) * KGν) := by
    rw [hΨd]; change IsKQC (⇑Gν.symm ∘ (⇑H ∘ ⇑Gμ)) univ _
    exact thm7_1_comp (thm7_1_comp hKGμ hHK (subset_univ _)) (homeomorph_inverse_isKQC Gν hKGν)
      (subset_univ _)
  have hGμE : ∀ w : ℂ, 1 < ‖w‖ → Gμ w ∈ gsans μ '' unitDiscExterior := fun w hw => ⟨w, hw, (hGμ hw).symm⟩
  have hGνinv : ∀ y ∈ gsans ν '' unitDiscExterior, 1 < ‖Gν.symm y‖ := by
    rintro _ ⟨x, hx, rfl⟩
    rw [← hGν hx, Gν.symm_apply_apply]
    exact hx
  have hΨ1 : ∀ w : ℂ, 1 < ‖w‖ → 1 < ‖Ψ w‖ := fun w hw => by
    rw [hΨa]; exact hGνinv _ (qd_side_homeo hμ hν H hH _ (hGμE w hw))
  have hΨ2 : ∀ w : ℂ, 1 < ‖w‖ → 1 < ‖Ψ.symm w‖ := fun w hw => by
    rw [hΨsa]
    obtain ⟨x, hx, hxe⟩ := qd_side_homeo hν hμ H.symm hHs _ (⟨w, hw, (hGν hw).symm⟩ :
      Gν w ∈ gsans ν '' unitDiscExterior)
    rw [← hxe, ← hGμ hx, Gμ.symm_apply_apply]
    exact hx
  obtain ⟨-, hcirc, hdisc⟩ := qd_disc_pres Ψ hΨ1 hΨ2
  obtain ⟨-, -, hdisc'⟩ := qd_disc_pres Ψ.symm hΨ2 (by simpa using hΨ1)
  have hΨD : Ψ '' unitDisc = unitDisc := by
    apply Subset.antisymm
    · rintro _ ⟨w, hw, rfl⟩
      exact mem_ball_zero_iff.mpr (hdisc w (mem_ball_zero_iff.mp hw))
    · intro y hy
      exact ⟨Ψ.symm y, mem_ball_zero_iff.mpr (hdisc' y (mem_ball_zero_iff.mp hy)), Ψ.apply_symm_apply y⟩
  -- the collar in disc coordinates
  have hAo : IsOpen (annulus 1 R) :=
    (isOpen_lt continuous_const continuous_norm).inter (isOpen_lt continuous_norm continuous_const)
  have hCo : IsOpen (gsans μ '' annulus 1 R) := by
    have hg := S2C.s2c_conf_g hμ
    have hsub : annulus 1 R ⊆ unitDiscExterior := fun w hw => hw.1
    exact (show IsConformalOnto (gsans μ) (annulus 1 R) (gsans μ '' annulus 1 R) from
      ⟨hg.1.mono hsub, hg.2.1.mono hsub, rfl⟩).isOpen hAo
  have hNc : ContinuousOn (cnf_finite A B h) (gsans μ '' annulus 1 R) := hqcN.2.2.1.1
  have hCN : ∀ w ∈ annulus 1 R, Gμ w ∈ gsans μ '' annulus 1 R := fun w hw => ⟨w, hw, (hGμ hw.1).symm⟩
  have hNΩ : ∀ u ∈ gsans μ '' annulus 1 R, 1 < ‖Gν.symm (cnf_finite A B h u)‖ := fun u hu =>
    hGνinv _ (hmapsN hu)
  obtain ⟨R2, hR2d⟩ : ∃ R2 : ℝ, R2 = (1 + R) / 2 := ⟨_, rfl⟩
  have hR21 : 1 < R2 := by rw [hR2d]; linarith
  have hR2R : R2 < R := by rw [hR2d]; linarith
  obtain ⟨r, hrd⟩ : ∃ r : ℝ, r = R2⁻¹ := ⟨_, rfl⟩
  have hr0 : 0 < r := by rw [hrd]; exact inv_pos.mpr (by linarith)
  have hr1 : r < 1 := by rw [hrd]; exact inv_lt_one_of_one_lt₀ hR21
  have hσA : ∀ z : ℂ, r ≤ ‖z‖ → ‖z‖ < 1 → (conj z)⁻¹ ∈ annulus 1 R := by
    intro z hz1 hz2
    have hz0 : z ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le hr0 hz1)
    show 1 < ‖(conj z)⁻¹‖ ∧ ‖(conj z)⁻¹‖ < R
    rw [(qd_sigma hz0).2.1]
    refine ⟨one_lt_inv_iff₀.mpr ⟨norm_pos_iff.mpr hz0, hz2⟩, ?_⟩
    calc ‖z‖⁻¹ ≤ r⁻¹ := inv_anti₀ hr0 hz1
      _ = R2 := by rw [hrd, inv_inv]
      _ < R := hR2R
  obtain ⟨g, hgd⟩ : ∃ g : ℂ → ℂ,
      g = fun z => (conj (Gν.symm (cnf_finite A B h (Gμ ((conj z)⁻¹)))))⁻¹ := ⟨_, rfl⟩
  have hX0 : ∀ z : ℂ, r ≤ ‖z‖ → ‖z‖ < 1 → Gν.symm (cnf_finite A B h (Gμ ((conj z)⁻¹))) ≠ 0 := by
    intro z h1 h2
    exact norm_pos_iff.mp (by linarith [hNΩ _ (hCN _ (hσA z h1 h2))])
  have hgD : ∀ z : ℂ, r ≤ ‖z‖ → ‖z‖ < 1 → ‖g z‖ < 1 := by
    intro z h1 h2
    rw [hgd]
    simp only
    rw [(qd_sigma (hX0 z h1 h2)).2.1]
    exact inv_lt_one_of_one_lt₀ (hNΩ _ (hCN _ (hσA z h1 h2)))
  have hgc : ContinuousOn g {z : ℂ | r ≤ ‖z‖ ∧ ‖z‖ < 1} := by
    rintro z ⟨h1, h2⟩
    have hz0 : z ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le hr0 h1)
    have c1 : ContinuousAt (fun z : ℂ => Gμ ((conj z)⁻¹)) z :=
      ContinuousAt.comp (f := fun z : ℂ => (conj z)⁻¹) Gμ.continuous.continuousAt (hσc z hz0)
    have c2 : ContinuousAt (fun z : ℂ => cnf_finite A B h (Gμ ((conj z)⁻¹))) z :=
      ContinuousAt.comp (f := fun z : ℂ => Gμ ((conj z)⁻¹))
        (hNc.continuousAt (hCo.mem_nhds (hCN _ (hσA z h1 h2)))) c1
    have c3 : ContinuousAt (fun z : ℂ => Gν.symm (cnf_finite A B h (Gμ ((conj z)⁻¹)))) z :=
      ContinuousAt.comp (f := fun z : ℂ => cnf_finite A B h (Gμ ((conj z)⁻¹))) Gν.symm.continuous.continuousAt c2
    have c4 : ContinuousAt g z := by
      rw [hgd]
      exact ContinuousAt.comp (f := fun z : ℂ => Gν.symm (cnf_finite A B h (Gμ ((conj z)⁻¹))))
        (g := fun z : ℂ => (conj z)⁻¹) (hσc _ (hX0 z h1 h2)) c3
    exact c4.continuousWithinAt
  have hgi : InjOn g {z : ℂ | r ≤ ‖z‖ ∧ ‖z‖ < 1} := by
    rintro x ⟨hx1, hx2⟩ y ⟨hy1, hy2⟩ hxy
    rw [hgd] at hxy
    simp only at hxy
    have e1 := (starRingEnd ℂ).injective (inv_injective hxy)
    have e2 := hinjN (hCN _ (hσA x hx1 hx2)) (hCN _ (hσA y hy1 hy2)) (Gν.symm.injective e1)
    exact (starRingEnd ℂ).injective (inv_injective (Gμ.injective e2))
  have hlim : ∀ ζ : ℂ, ‖ζ‖ = 1 → Tendsto g (𝓝[{z : ℂ | r ≤ ‖z‖ ∧ ‖z‖ < 1}] ζ) (𝓝 (Ψ ζ)) := by
    intro ζ hζ
    have hζ0 : ζ ≠ 0 := norm_ne_zero_iff.mp (by rw [hζ]; norm_num)
    have hσζ : (conj ζ)⁻¹ = ζ := qd_sigma_circle hζ
    have t1 : Tendsto (fun z : ℂ => (conj z)⁻¹) (𝓝[{z : ℂ | r ≤ ‖z‖ ∧ ‖z‖ < 1}] ζ) (𝓝[annulus 1 R] ζ) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
      · have h1 := (hσc ζ hζ0).tendsto
        rw [hσζ] at h1
        exact h1.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with z hz
        exact hσA z hz.1 hz.2
    have t2 : Tendsto Gμ (𝓝[annulus 1 R] ζ) (𝓝[gsans μ '' annulus 1 R] (Gμ ζ)) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨(Gμ.continuous.tendsto ζ).mono_left nhdsWithin_le_nhds, ?_⟩
      filter_upwards [self_mem_nhdsWithin] with w hw
      exact hCN w hw
    have hfr : Gμ ζ ∈ frontier (fsans μ '' unitDisc) := by
      have hnot : Gμ ζ ∉ gsans μ '' unitDiscExterior := by
        rintro ⟨w, hw, hwe⟩
        rw [← hGμ hw] at hwe
        have h1 : (1 : ℝ) < ‖w‖ := hw
        rw [Gμ.injective hwe, hζ] at h1
        exact lt_irrefl _ h1
      have h0 : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
      have hseq : Tendsto (fun n : ℕ => ((1 + 1 / ((n : ℝ) + 1) : ℝ) : ℂ) * ζ) atTop (𝓝 ζ) := by
        have h3 := ((Complex.continuous_ofReal.tendsto (1 + 0)).comp (h0.const_add 1)).mul_const ζ
        simpa using h3
      have hclE : Gμ ζ ∈ closure (gsans μ '' unitDiscExterior) := by
        refine mem_closure_of_tendsto ((Gμ.continuous.tendsto ζ).comp hseq)
          (Eventually.of_forall fun n => hGμE _ ?_)
        rw [norm_mul, Complex.norm_real, hζ, mul_one, Real.norm_of_nonneg (by positivity)]
        have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
        linarith
      have hnotΩ : Gμ ζ ∉ fsans μ '' unitDisc := fun hm => by
        obtain ⟨y, hy⟩ := mem_closure_iff.mp hclE _ hΩo hm
        exact (qd_sides hμ).1.le_bot ⟨hy.1, hy.2⟩
      rw [hΩo.frontier_eq]
      exact ⟨(qd_sides hμ).2 hnot, hnotΩ⟩
    have t3 := htrace H hH (Gμ ζ) hfr
    have t4 := (Gν.symm.continuous.tendsto _).comp (t3.comp (t2.comp t1))
    have hΨζ : Gν.symm (H (Gμ ζ)) = Ψ ζ := (hΨa ζ).symm
    have hΨn : ‖Ψ ζ‖ = 1 := hcirc ζ hζ
    have t5 := ((hσc _ (norm_ne_zero_iff.mp (by rw [hΨζ, hΨn]; norm_num))).tendsto).comp t4
    rw [hΨζ, qd_sigma_circle hΨn] at t5
    rw [hgd]
    exact t5
  have hgK : IsQuasiconformal g (annulus r 1) := by
    have k1 := thm7_1_comp (nx_isKQC_restrict hKGμ hAo (subset_univ _)) hqcN
      (by rintro _ ⟨w, hw, rfl⟩; exact hCN w hw)
    have k2 := thm7_1_comp k1 (homeomorph_inverse_isKQC Gν hKGν) (subset_univ _)
    refine ⟨KGμ * 3 * KGν, ?_⟩
    rw [hgd]
    exact qd_conjinv_qc k2 ((isOpen_lt continuous_const continuous_norm).inter
        (isOpen_lt continuous_norm continuous_const))
      (fun h0 => by
        have h1 := h0.1
        rw [norm_zero] at h1
        linarith)
      (fun z hz => hσA z hz.1.le hz.2)
      (fun u hu => norm_pos_iff.mp (lt_trans one_pos (hNΩ _ (hCN u hu))))
  have hgs : g '' annulus r 1 ⊆ unitDisc := by
    rintro _ ⟨z, hz, rfl⟩
    exact mem_ball_zero_iff.mpr (hgD z hz.1.le hz.2)
  obtain ⟨G', hG', hGh⟩ := qd_Gext hr0 hr1 hgc hgi hgD hcirc hlim
  have hbv : ∃ f : ℂ → ℂ, HasBoundaryValues f Ψ.onePointCongr :=
    ⟨Ψ, ⟨_, nx_isKQC_restrict hΨK isOpen_ball (subset_univ _)⟩, hΨD, Ψ.onePointCongr,
      s27v_b_isHomeoExtension_of_homeomorph Ψ.onePointCongr (fun z _ => rfl) hΨD, fun ζ _ => rfl⟩
  obtain ⟨f, r₀, -, hr₀1, ⟨⟨Kf, hfK⟩, hfs, Ff, hFf, hFfb⟩, hfg⟩ :=
    annulus_extension_extends hbv hr0 hr1 hgK hgs hG' hGh
  -- boundary values of `f`
  have hfb : ∀ ζ : ℂ, ‖ζ‖ = 1 → Tendsto f (𝓝[unitDisc] ζ) (𝓝 (Ψ ζ)) := by
    intro ζ hζ
    have hζcl : (ζ : ExtPlane) ∈ closure (toExt unitDisc) := by
      have h1 : ζ ∈ closure unitDisc := by rw [hcb]; exact mem_closedBall_zero_iff.mpr hζ.le
      exact mem_closure_image OnePoint.continuous_coe.continuousAt h1
    have h1 : ContinuousWithinAt Ff (toExt unitDisc) (ζ : ExtPlane) := (hFf.2.1 _ hζcl).mono subset_closure
    have h2 : Tendsto (fun z : ℂ => Ff z) (𝓝[unitDisc] ζ) (𝓝 (Ff ζ)) := by
      unfold ContinuousWithinAt at h1
      rw [toExt, ← OnePoint.isOpenEmbedding_coe.isInducing.map_nhdsWithin_eq] at h1
      exact tendsto_map'_iff.mp h1
    have h3 : Tendsto (fun z : ℂ => ((f z : ℂ) : ExtPlane)) (𝓝[unitDisc] ζ) (𝓝 ((Ψ ζ : ℂ) : ExtPlane)) := by
      rw [← show Ψ.onePointCongr ζ = ((Ψ ζ : ℂ) : ExtPlane) from rfl, ← hFfb ζ hζ]
      refine h2.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with z hz
      exact hFf.1 z hz
    exact OnePoint.isOpenEmbedding_coe.isInducing.tendsto_nhds_iff.mpr h3
  -- the push normalizing `f(0) = 0`
  obtain ⟨a, ha, hfa⟩ : (0 : ℂ) ∈ f '' unitDisc := by rw [hfs]; exact mem_ball_self one_pos
  obtain ⟨W, KW, ρ, hWK, hW0, hρ1, hWz⟩ := qd_push (mem_ball_zero_iff.mp ha)
  have hWD : ∀ z : ℂ, ‖z‖ < 1 → ‖W z‖ < 1 := by
    intro z hz
    by_contra hc
    push_neg at hc
    have h2 := W.injective (hWz _ (le_trans hρ1.le hc))
    rw [h2] at hc
    linarith
  have hWs : W '' unitDisc = unitDisc := by
    apply Subset.antisymm
    · rintro _ ⟨z, hz, rfl⟩
      exact mem_ball_zero_iff.mpr (hWD z (mem_ball_zero_iff.mp hz))
    · intro y hy
      refine ⟨W.symm y, mem_ball_zero_iff.mpr ?_, W.apply_symm_apply y⟩
      by_contra hc
      push_neg at hc
      have h1 := hWz _ (le_trans hρ1.le hc)
      rw [W.apply_symm_apply] at h1
      rw [← h1] at hc
      exact absurd (mem_ball_zero_iff.mp hy) (not_lt.mpr hc)
  have hf2K : IsKQC (f ∘ W) unitDisc (KW * Kf) :=
    thm7_1_comp (nx_isKQC_restrict hWK isOpen_ball (subset_univ _)) hfK hWs.subset
  have hf2s : (f ∘ W) '' unitDisc = unitDisc := by rw [image_comp, hWs, hfs]
  have hf20 : (f ∘ W) 0 = 0 := by simp only [Function.comp_apply, hW0, hfa]
  have hf2b : ∀ ζ : ℂ, ‖ζ‖ = 1 → Tendsto (f ∘ W) (𝓝[unitDisc] ζ) (𝓝 (Ψ ζ)) := by
    intro ζ hζ
    refine (hfb ζ hζ).congr' ?_
    have hev : ∀ᶠ z in 𝓝 ζ, ρ ≤ ‖z‖ := by
      filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds
        (show ρ < ‖ζ‖ by rw [hζ]; exact hρ1)] with z hz
      exact le_of_lt hz
    filter_upwards [nhdsWithin_le_nhds hev] with z hz
    rw [Function.comp_apply, hWz z hz]
  obtain ⟨Θ, KΘ, hΘK, hΘin, hΘout⟩ := qd_theta Ψ hΨK hΨ1 hΨ2 hf2K hf2s hf20 hf2b
  -- the collar radius
  obtain ⟨m, hmd⟩ : ∃ m : ℝ, m = max (max r₀ ρ) (1 / 2) := ⟨_, rfl⟩
  have hm1 : m < 1 := by rw [hmd]; exact max_lt (max_lt hr₀1 hρ1) (by norm_num)
  have hm0 : 0 < m := by rw [hmd]; exact lt_of_lt_of_le (by norm_num) (le_max_right _ _)
  have hr₀m : r₀ ≤ m := by rw [hmd]; exact le_trans (le_max_left _ _) (le_max_left _ _)
  have hρm : ρ ≤ m := by rw [hmd]; exact le_trans (le_max_right _ _) (le_max_left _ _)
  have hR₁ : 1 < min R m⁻¹ := lt_min hR (one_lt_inv_iff₀.mpr ⟨hm0, hm1⟩)
  have hsubR : gsans μ '' annulus 1 (min R m⁻¹) ⊆ gsans μ '' annulus 1 R :=
    image_mono fun w hw => ⟨hw.1, lt_of_lt_of_le hw.2 (min_le_left _ _)⟩
  have hFK : IsKQC (Gμ.symm.trans (Θ.trans Gν)) univ (KGμ * KΘ * KGν) := by
    change IsKQC (⇑Gν ∘ (⇑Θ ∘ ⇑Gμ.symm)) univ _
    exact thm7_1_comp (thm7_1_comp (homeomorph_inverse_isKQC Gμ hKGμ) hΘK (subset_univ _)) hKGν
      (subset_univ _)
  refine ⟨Gμ.symm.trans (Θ.trans Gν), _, hFK, ?_, min R m⁻¹, hR₁, ?_, fun u hu => hhalf u (hsubR hu),
    fun u hu => hdilC u (hsubR hu)⟩
  · intro w hw
    show Gν (Θ (Gμ.symm (fsans μ w))) = fsans ν w
    have hle : ‖Gμ.symm (fsans μ w)‖ ≤ 1 := by
      by_contra hc
      push_neg at hc
      have h1 := hGμE _ hc
      rw [Gμ.apply_symm_apply] at h1
      exact (qd_sides hμ).1.le_bot ⟨⟨w, hw, rfl⟩, h1⟩
    rw [hΘin _ hle, hΨa, Gμ.apply_symm_apply, Gν.apply_symm_apply, hH w hw]
  · rintro _ ⟨w, hw, rfl⟩
    show Gν (Θ (Gμ.symm (gsans μ w))) = cnf_finite A B h (gsans μ w)
    rw [← hGμ hw.1, Gμ.symm_apply_apply, hΘout w hw.1]
    have hw0 : w ≠ 0 := norm_pos_iff.mp (by linarith [hw.1])
    have hσw := qd_sigma hw0
    have hσn : m < ‖(conj w)⁻¹‖ := by
      rw [hσw.2.1]
      exact (lt_inv_comm₀ hm0 (norm_pos_iff.mpr hw0)).mpr (lt_of_lt_of_le hw.2 (min_le_right _ _))
    have hr₀w : (conj w)⁻¹ ∈ annulus r₀ 1 := by
      refine ⟨lt_of_le_of_lt hr₀m hσn, ?_⟩
      rw [hσw.2.1]
      exact inv_lt_one_of_one_lt₀ hw.1
    have hwR : w ∈ annulus 1 R := ⟨hw.1, lt_of_lt_of_le hw.2 (min_le_left _ _)⟩
    have hXw : Gν.symm (cnf_finite A B h (Gμ w)) ≠ 0 :=
      norm_pos_iff.mp (by linarith [hNΩ _ (hCN w hwR)])
    rw [Function.comp_apply, hWz _ (le_trans hρm hσn.le), hfg hr₀w, hgd]
    simp only
    rw [hσw.1, (qd_sigma hXw).1, Gν.apply_symm_apply]

/-- **(R4) Global extension with `L²` dilatation (Cor 3.2 over the quasidisc `f^μ(𝔻)`).** If `β([ν]) - β([μ]) ∈ A₂(𝔻)`,
then `f^ν ∘ (f^μ)⁻¹` has a q.c. extension to `ℂ` whose dilatation, pulled back to `𝔻*` by `𝗀_μ`, is in `L²(𝔻*, ρ)`. -/
theorem qd_extension {μ ν : LinfStar} (hμ : μ ∈ LinfStarBall) (hν : ν ∈ LinfStarBall)
    (hP : AInf.toFun (bersPhi ν - bersPhi μ) ∈ A2fun unitDisc) :
    ∃ (F : ℂ → ℂ) (K : ℝ), IsKQC F univ K ∧ F '' univ = univ ∧
      (∀ w ∈ unitDisc, F (fsans μ w) = fsans ν w) ∧
      normL2 unitDiscExterior (hbPre_pullback (complexDilatation F) (gsans μ)) < ∞ := by
  obtain ⟨h, K, p, C₀, -, hp, hC1, hpl, hh, hinf, hb1, hb2⟩ := hc6_chosen_reflection hμ
  obtain ⟨A, B, hA, hB, hode, hrat⟩ := cnf_pair hμ hν
  obtain ⟨F, KF, hFK, hmatch, R₁, hR₁, hFN, hd, hdil⟩ :=
    qd_fill hμ hν hP hp hC1 hpl hh hinf hb1 hb2 hA hB hode hrat
  refine ⟨F, KF, hFK, image_univ_of_surjective F.surjective, hmatch, ?_⟩
  obtain ⟨T, KT, hT, -, -, -, -, -, hTae⟩ := crc_circle_map hμ hν F hFK hmatch
  have hAo : IsOpen (annulus 1 R₁) :=
    (isOpen_lt continuous_const continuous_norm).inter (isOpen_lt continuous_norm continuous_const)
  have hCo : IsOpen (gsans μ '' annulus 1 R₁) := by
    have hg := S2C.s2c_conf_g hμ
    have hsub : annulus 1 R₁ ⊆ unitDiscExterior := fun w hw => hw.1
    exact (show IsConformalOnto (gsans μ) (annulus 1 R₁) (gsans μ '' annulus 1 R₁) from
      ⟨hg.1.mono hsub, hg.2.1.mono hsub, rfl⟩).isOpen hAo
  have hsplit : unitDiscExterior \ discExteriorR R₁ = annulus 1 R₁ := by
    ext z
    simp only [discExteriorR, mem_diff, mem_setOf_eq, not_and, not_le]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1, h2 h1⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h1, fun _ => h2⟩
  refine cce_finite_of_collar hR₁ (M := 1) ?_ ?_
  · have h2 := thm9_4_dilatation_ae hT
    rw [Measure.restrict_univ] at h2
    have hsub : discExteriorR R₁ ⊆ unitDiscExterior := fun z hz => hz.1
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hsub hTae, ae_restrict_of_ae h2] with z hz1 hz2
    rw [← hz1]
    have hle : ‖dzbar T z‖ ≤ ‖dz T z‖ := by
      by_contra hc
      push_neg at hc
      nlinarith [hT.2.1, norm_nonneg (dz T z), norm_nonneg (dzbar T z)]
    unfold complexDilatation
    rw [norm_div]
    rcases (norm_nonneg (dz T z)).eq_or_lt with h0 | h0
    · rw [← h0, div_zero]; norm_num
    · exact div_le_one_of_le₀ hle h0.le
  · rw [hsplit]
    have hEq : ∀ w ∈ annulus 1 R₁, hbPre_pullback (complexDilatation F) (gsans μ) w =
        hbPre_pullback (crn_coefficient (schwarzianHol (crs_transition μ ν)) h) (gsans μ) w := by
      intro w hw
      have hu : gsans μ w ∈ gsans μ '' annulus 1 R₁ := ⟨w, hw, rfl⟩
      have hev : (F : ℂ → ℂ) =ᶠ[𝓝 (gsans μ w)] cnf_finite A B h :=
        Filter.eventuallyEq_of_mem (hCo.mem_nhds hu) hFN
      unfold hbPre_pullback
      rw [← hdil _ hu]
      congr 1
      unfold complexDilatation dz dzbar
      rw [hev.fderiv_eq]
    have hcong : normL2 (annulus 1 R₁) (hbPre_pullback (complexDilatation F) (gsans μ)) =
        normL2 (annulus 1 R₁) (hbPre_pullback (crn_coefficient (schwarzianHol (crs_transition μ ν)) h)
          (gsans μ)) := by
      unfold normL2
      congr 1
      exact setLIntegral_congr_fun hAo.measurableSet (fun w hw => by simp only [hEq w hw])
    rw [hcong]
    exact crn_schwarzian_collar_finite hμ hν hP hh hAo.measurableSet (fun w hw => hw.1)
      (fun w hw => hd _ ⟨w, hw, rfl⟩)

/-- **(R5) Slice membership.** If `β(q) - β([μ]) ∈ A₂(𝔻)` with `μ ∈ 𝒪(𝔻*)₁`, then `q ∈ T_[μ](1)`. -/
theorem qd_mem_component (μ : LinfStarBall) (hμ : (μ : LinfStar) ∈ groupO) (ν : LinfStarBall)
    (hP : AInf.toFun (bersPhi ν - bersPhi μ) ∈ A2fun unitDisc) :
    Phi ν ∈ componentT (Phi μ) := by
  obtain ⟨F, K, hF, hFs, hm, hL⟩ := qd_extension μ.2 ν.2 hP
  obtain ⟨ω, hω, he⟩ := crc_relative_coefficient_of_qc μ.2 ν.2 hF hFs hm hL
  have h0 : (0 : LinfStar) ∈ LinfStarBall := mem_ball_self one_pos
  have hc := cst_coeff_right_finite hμ h0 ω.2 (by rwa [sub_zero])
  rw [grp_zero_mul μ.2] at hc
  rw [← csl_L2leaf_eq_component μ hμ, ← he]
  exact ⟨_, rfl, hc⟩

/-- `componentT_spec`, conjunct 1, for every base point. -/
theorem qd_componentT_spec_one (p : T1) :
    bers '' componentT p = {φ | ∃ ψ : A2 unitDisc, φ = bers p + A2toAInf ψ} ∩ range bers := by
  apply Subset.antisymm (ctd_componentT_spec_one_subset p)
  rintro φ ⟨⟨ψ, hψ⟩, q, rfl⟩
  obtain ⟨μ, hμ, rfl⟩ := ctb_exists_groupO_rep p
  obtain ⟨ν, -, rfl⟩ := ctb_exists_groupO_rep q
  have hP : AInf.toFun (bersPhi ν - bersPhi μ) ∈ A2fun unitDisc := by
    rw [← bers_Phi, ← bers_Phi, hψ, add_sub_cancel_left]
    exact ctc_mem_range.mpr ⟨ψ, rfl⟩
  exact ⟨Phi ν, qd_mem_component μ hμ ν hP, rfl⟩

/-- **`componentT_spec`** (TT:1896), both conjuncts, for every base point (to replace the original). -/
theorem qd_componentT_spec :
    (∀ p : T1, bers '' componentT p = {φ | ∃ ψ : A2 unitDisc, φ = bers p + A2toAInf ψ} ∩ range bers) ∧
      ∀ (p : T1) (ν : LinfStarBall), ∃ h : beltramiMul (Quotient.out p : LinfStarBall) ν ∈ LinfStarBall,
        rightTrans ν '' componentT p = componentT (Phi ⟨_, h⟩) :=
  ⟨qd_componentT_spec_one, ctb_componentT_spec_two⟩

/-- (TT:1896) The distribution `𝔇_T` is integrable. Its integral manifold through `[μ]` is the component `T_[μ](1)`,
whose Bers image is `(β([μ]) + A₂(𝔻)) ∩ β(T(1))`. Right translations permute the components transitively:
`R_[ν](T_[μ](1)) = T_[μ * ν](1)`.

[NOTE 2026-10-26] For `p ∉ T₀(1)` the first conjunct is only asserted in the memoir (via right translation); a proof
appears to need Lemma 2.9 for non-harmonic `λ`, whose stated form is in doubt. The statement is kept unchanged (user
decision); the second conjunct is proved as `ctb_componentT_spec_two` (`Ch1/ComponentTBasics`). -/
theorem componentT_spec :
    (∀ p : T1, bers '' componentT p = {φ | ∃ ψ : A2 unitDisc, φ = bers p + A2toAInf ψ} ∩ range bers) ∧
      ∀ (p : T1) (ν : LinfStarBall), ∃ h : beltramiMul (Quotient.out p : LinfStarBall) ν ∈ LinfStarBall,
        rightTrans ν '' componentT p = componentT (Phi ⟨_, h⟩) := by
  exact qd_componentT_spec

end TakhtajanTeo
