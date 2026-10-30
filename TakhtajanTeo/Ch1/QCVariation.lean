import TakhtajanTeo.Ch1.QCVariationPlane
import TakhtajanTeo.Ch1.S1_1_TeichmullerTheory

/-!
# Ch1/QCVariation — variation of the normalized solutions in the Banach parameter `μ ∈ L∞(𝔻*)₁`

Owner: 下属5. Imports `QCVariationPlane` (plane-normalized solutions, Gateaux/Fréchet tools) and `S1_1`.
Model B maps `fB`, `fsans` are NOT holomorphic in `μ` under the welding normalization (the Möbius map depends on the
real-analytic pole `p_μ`); everything holomorphic is Möbius invariant: the plane solution `W_μ`, `𝒮(fB μ) = 𝒮(W_μ)`.
-/

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal ComplexConjugate Real BoundedContinuousFunction

noncomputable section

namespace TakhtajanTeo
namespace QCV

open LiZhongQC

/-- The zero extension `extB` is a.e. linear. -/
theorem qcv_extB_lin (a : ℂ) (v₁ v₂ : LinfStar) :
    extB (a • v₁ + v₂) =ᵐ[volume] fun u => a * extB v₁ u + extB v₂ u := by
  have hmeas : MeasurableSet unitDiscExterior := (isOpen_lt continuous_const continuous_norm).measurableSet
  have h := (Lp.coeFn_add (a • v₁) v₂).and (Lp.coeFn_smul a v₁)
  have h' := (ae_restrict_iff' hmeas).1 h
  filter_upwards [h'] with u hu
  by_cases hm : u ∈ unitDiscExterior
  · obtain ⟨e1, e2⟩ := hu hm
    simp only [extB, Set.indicator_of_mem hm]
    rw [e1, Pi.add_apply, e2]
    simp
  · simp [extB, Set.indicator_of_notMem hm]

/-- **Holomorphy of the plane solution in the Beltrami coefficient `μ ∈ L∞(𝔻*)₁`** (Fréchet, for each `z`). -/
theorem qcv_planeB_differentiableOn (z : ℂ) :
    DifferentiableOn ℂ (fun μ : LinfStar => normalizedSolution (extB μ) z) LinfStarBall := by
  intro μ₀ hμ₀
  have hk : ‖μ₀‖ < 1 := by simpa [LinfStarBall] using hμ₀
  have hg₀ := extB_isBeltramiCoeff μ₀
  obtain ⟨f₀, hf₀, -, -⟩ := thm13_7_normalized_existence (norm_nonneg μ₀) hk hg₀
  have hT : ∀ v : LinfStar, IsBeltramiCoeff (extB v) univ (1 * ‖v‖) := fun v => by
    simpa using extB_isBeltramiCoeff v
  have hg₀' : IsBeltramiCoeff (fun u => extB μ₀ u) univ ‖μ₀‖ := hg₀
  obtain ⟨L, -, hL⟩ := qcv_plane_hasFDerivAt (norm_nonneg μ₀) hk hg₀' hf₀ (fun v => extB v) zero_le_one hT
    qcv_extB_lin z
  refine DifferentiableAt.differentiableWithinAt ?_
  refine ⟨L, ?_⟩
  rw [hasFDerivAt_iff_isLittleO_nhds_zero]
  have h := hasFDerivAt_iff_isLittleO_nhds_zero.1 hL
  have key : ∀ v : LinfStar, ‖v‖ < (1 - ‖μ₀‖) / 2 →
      normalizedSolution (fun u => extB μ₀ u + extB v u) = normalizedSolution (extB (μ₀ + v)) := by
    intro v hv
    have hk' : ‖μ₀ + v‖ < 1 := by
      have := norm_add_le μ₀ v
      linarith
    have hae : extB (μ₀ + v) =ᵐ[volume] fun u => extB μ₀ u + extB v u := by
      have := qcv_extB_lin 1 μ₀ v
      simpa using this
    have := qcv_ns_congr_ae (norm_nonneg _) hk' (extB_isBeltramiCoeff (μ₀ + v)) hae
    exact this.symm
  refine h.congr' ?_ Filter.EventuallyEq.rfl
  filter_upwards [Metric.ball_mem_nhds (0 : LinfStar) (show 0 < (1 - ‖μ₀‖) / 2 by linarith)] with v hv
  rw [mem_ball_zero_iff] at hv
  have h0 : ‖(0 : LinfStar)‖ < (1 - ‖μ₀‖) / 2 := by simp; linarith
  simp only [zero_add, add_zero]
  rw [key v hv, key 0 h0, add_zero]

/-! ### Plane solution on the disk: holomorphy, injectivity, Koebe bound, Möbius invariance -/

theorem qcv_W_props {μ : LinfStar} (hμ : ‖μ‖ < 1) :
    IsNormalizedSolution (normalizedSolution (extB μ)) (extB μ) ∧
      DifferentiableOn ℂ (normalizedSolution (extB μ)) unitDisc ∧
      InjOn (normalizedSolution (extB μ)) univ ∧ normalizedSolution (extB μ) 0 = 0 := by
  have hN := qcv_ns_spec (norm_nonneg μ) hμ (extB_isBeltramiCoeff μ)
  have hN' := hN
  obtain ⟨⟨K, hK⟩, -, h0, -, -⟩ := hN'
  exact ⟨hN, extB_solution_holomorphic hN, hK.2.2.1.2.1, h0⟩

theorem qcv_W_koebe {μ : LinfStar} (hμ : ‖μ‖ < 1) {ζ : ℂ} (hζ : ‖ζ‖ < 1) :
    ‖normalizedSolution (extB μ) ζ‖ ≤
      4 * ‖normalizedSolution (extB μ) 2‖ * (‖ζ‖ / (1 - ‖ζ‖) ^ 2) := by
  obtain ⟨-, hd, hi, h0⟩ := qcv_W_props hμ
  have hi' : InjOn (normalizedSolution (extB μ)) (ball (0 : ℂ) 1) := hi.mono (subset_univ _)
  have hw : normalizedSolution (extB μ) 2 ∉ normalizedSolution (extB μ) '' ball (0 : ℂ) 1 := by
    rintro ⟨u, hu, hu2⟩
    have := hi (mem_univ u) (mem_univ 2) hu2
    have hn : ‖u‖ < 1 := by simpa using hu
    rw [this] at hn
    norm_num at hn
  have hq := koebe_quarter_of_not_mem hd hi' h0 hw
  have hg := koebe_growth_scaled hd hi' h0 hζ
  have hpos : 0 ≤ ‖ζ‖ / (1 - ‖ζ‖) ^ 2 := by positivity
  calc ‖normalizedSolution (extB μ) ζ‖ ≤ ‖deriv (normalizedSolution (extB μ)) 0‖ * ‖ζ‖ / (1 - ‖ζ‖) ^ 2 := hg
    _ = ‖deriv (normalizedSolution (extB μ)) 0‖ * (‖ζ‖ / (1 - ‖ζ‖) ^ 2) := by ring
    _ ≤ 4 * ‖normalizedSolution (extB μ) 2‖ * (‖ζ‖ / (1 - ‖ζ‖) ^ 2) :=
        mul_le_mul_of_nonneg_right hq hpos

/-- Möbius invariance: on `𝔻`, `𝒮(fB μ) = 𝒮(W_μ)` with `W_μ` the plane solution of `extB μ`. -/
theorem qcv_schwarzian_fB_eq {μ : LinfStar} (hμ : μ ∈ LinfStarBall) {z : ℂ} (hz : z ∈ unitDisc) :
    schwarzianHol (fB μ) z = schwarzianHol (normalizedSolution (extB μ)) z := by
  have hk : ‖μ‖ < 1 := by simpa [LinfStarBall] using hμ
  obtain ⟨-, hhol, hinj, -⟩ := qcv_W_props hk
  obtain ⟨M, hM, W, hW, hfinite, -, f, hf, -⟩ := (wB_spec hμ).1
  have hWeq : normalizedSolution (extB μ) = W := qcv_ns_eq (norm_nonneg μ) hk (extB_isBeltramiCoeff μ) hW
  obtain ⟨a, b, c, d, hdet, rfl⟩ := hM
  have hden : ∀ z ∈ unitDisc, c * W z + d ≠ 0 := by
    intro z hz he
    have hfin := (hfinite z).symm.trans (hf z hz)
    rw [mobiusExt_coe_of_eq_zero he] at hfin
    exact OnePoint.infty_ne_coe _ hfin
  have hrep : EqOn (fB μ) (fun z => (a * W z + b) / (c * W z + d)) unitDisc := by
    intro z hz
    rw [fB, hfinite z, mobiusExt_coe (hden z hz)]
    rfl
  obtain ⟨hfd, -⟩ := fB_holomorphic_injective hμ
  have hWa : AnalyticAt ℂ W z := by
    rw [← hWeq]; exact (hhol.analyticAt (isOpen_ball.mem_nhds hz))
  have hW' : deriv W z ≠ 0 := by
    rw [← hWeq]; exact deriv_ne_zero_of_injOn isOpen_ball hhol (hinj.mono (subset_univ _)) hz
  have hev : fB μ =ᶠ[𝓝[≠] z] fun w => (a * W w + b) / (c * W w + d) :=
    (eventually_of_mem (isOpen_ball.mem_nhds hz) hrep).filter_mono nhdsWithin_le_nhds
  rw [← schwarzian_of_analyticAt (hfd.analyticAt (isOpen_ball.mem_nhds hz)), schwarzian_congr hev,
    schwarzian_mobius_comp_of_ne hWa hW' hdet (hden z hz), schwarzian_of_analyticAt hWa, hWeq]

/-- The Schwarzian through iterated derivatives. -/
theorem qcv_schwarzianHol_iter {f : ℂ → ℂ} {z : ℂ} (hf : AnalyticAt ℂ f z) (hf' : deriv f z ≠ 0) :
    schwarzianHol f z = iteratedDeriv 3 f z / deriv f z - 3 / 2 * (iteratedDeriv 2 f z / deriv f z) ^ 2 := by
  have h1 : AnalyticAt ℂ (deriv f) z := hf.deriv
  have h2 : AnalyticAt ℂ (deriv (deriv f)) z := h1.deriv
  have hd1 : HasDerivAt (deriv f) (deriv (deriv f) z) z := h1.differentiableAt.hasDerivAt
  have hd2 : HasDerivAt (deriv (deriv f)) (deriv (deriv (deriv f)) z) z := h2.differentiableAt.hasDerivAt
  have hq : HasDerivAt (fun w => deriv (deriv f) w / deriv f w) _ z := hd2.div hd1 hf'
  unfold schwarzianHol
  rw [hq.deriv]
  have e2 : iteratedDeriv 2 f z = deriv (deriv f) z := by
    rw [iteratedDeriv_succ, iteratedDeriv_one]
  have e3 : iteratedDeriv 3 f z = deriv (deriv (deriv f)) z := by
    rw [iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_one]
  rw [e2, e3]
  field_simp
  ring

/-- `x ↦ x/(1-x)²` is monotone on `[0, 1)`. -/
theorem qcv_mono_koebe {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) (hy : y < 1) :
    x / (1 - x) ^ 2 ≤ y / (1 - y) ^ 2 := by
  have h1 : 0 < 1 - y := by linarith
  have h2 : 0 < 1 - x := by linarith
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [mul_nonneg (sub_nonneg.2 hxy) (show 0 ≤ 1 - x * y by nlinarith)]

/-- Gateaux differentiability of the Bers map into `A∞(𝔻)` (via the Schwarzian of the plane solution). -/
theorem qcv_bersPhi_gateaux {μ : LinfStar} (hμ : μ ∈ LinfStarBall) (ν : LinfStar) :
    DifferentiableAt ℂ (fun t : ℂ => bersPhi (μ + t • ν)) 0 := by
  have hk : ‖μ‖ < 1 := by simpa [LinfStarBall] using hμ
  haveI : CompleteSpace (AInf unitDisc) := AInf_completeSpace_disc
  set r₀ : ℝ := (1 - ‖μ‖) / (2 * (‖ν‖ + 1)) with hr₀
  have hr₀pos : 0 < r₀ := by have := sub_pos.2 hk; positivity
  set r : ℝ := r₀ / 2 with hr
  have hrpos : 0 < r := by positivity
  have hball : ∀ t ∈ ball (0 : ℂ) r₀, μ + t • ν ∈ LinfStarBall := by
    intro t ht
    have ht' : ‖t‖ < r₀ := by simpa using ht
    have h1 : ‖μ + t • ν‖ ≤ ‖μ‖ + ‖t‖ * ‖ν‖ := by
      refine (norm_add_le _ _).trans ?_
      rw [norm_smul]
    have h2 : ‖t‖ * ‖ν‖ ≤ r₀ * ‖ν‖ := by gcongr
    have h3 : r₀ * ‖ν‖ ≤ (1 - ‖μ‖) / 2 := by
      rw [hr₀, div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith [norm_nonneg ν, sub_pos.2 hk]
    have : ‖μ + t • ν‖ < 1 := by
      nlinarith [norm_nonneg ν, sub_pos.2 hk, norm_nonneg t]
    simpa [LinfStarBall] using this
  let W : ℂ → ℂ → ℂ := fun t ζ => normalizedSolution (extB (μ + t • ν)) ζ
  have hWt : ∀ ζ, DifferentiableOn ℂ (fun t => W t ζ) (ball (0 : ℂ) r₀) := by
    intro ζ
    have hc : DifferentiableOn ℂ (fun t : ℂ => μ + t • ν) (ball (0 : ℂ) r₀) :=
      (differentiableOn_const μ).add ((differentiableOn_id).smul_const ν)
    exact (qcv_planeB_differentiableOn ζ).comp hc hball
  have hrsub : closedBall (0 : ℂ) r ⊆ ball 0 r₀ := by
    intro t ht
    simp only [mem_closedBall, dist_zero_right, mem_ball] at ht ⊢
    linarith
  obtain ⟨B, hB⟩ : ∃ B : ℝ, ∀ t ∈ closedBall (0 : ℂ) r, ‖W t 2‖ ≤ B :=
    (isCompact_closedBall (0 : ℂ) r).exists_bound_of_continuousOn
      ((hWt 2).continuousOn.mono hrsub)
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0 (mem_closedBall_self hrpos.le))
  have hnormt : ∀ t ∈ ball (0 : ℂ) r₀, ‖μ + t • ν‖ < 1 := fun t ht => by
    simpa [LinfStarBall] using hball t ht
  have hbersbd : ∀ t ∈ ball (0 : ℂ) r₀, ‖bersPhi (μ + t • ν)‖ ≤ 6 := fun t ht =>
    (bersPhi_spec (hball t ht)).2
  -- iterated derivatives are holomorphic in `t`
  have hderiv : ∀ z ∈ unitDisc, ∀ j : ℕ,
      DifferentiableOn ℂ (fun t => iteratedDeriv j (W t) z) (ball (0 : ℂ) r) := by
    intro z hz j
    have hz1 : ‖z‖ < 1 := mem_ball_zero_iff.mp hz
    set R : ℝ := (1 - ‖z‖) / 2 with hRdef
    have hRpos : 0 < R := by have := sub_pos.2 hz1; positivity
    set ρ : ℝ := (1 + ‖z‖) / 2 with hρdef
    have hρ1 : ρ < 1 := by rw [hρdef]; linarith
    have hballsub : ball z R ⊆ unitDisc := by
      intro p hp
      simp only [mem_ball, dist_eq_norm] at hp
      refine mem_ball_zero_iff.mpr ?_
      have := norm_le_norm_add_norm_sub' p z
      linarith
    have hM : ∀ t ∈ ball (0 : ℂ) r, ∀ ζ ∈ ball z R, ‖W t ζ‖ ≤ 4 * B * (ρ / (1 - ρ) ^ 2) := by
      intro t ht ζ hζ
      have htr₀ : t ∈ ball (0 : ℂ) r₀ := hrsub (ball_subset_closedBall ht)
      have hζ1 : ‖ζ‖ < 1 := mem_ball_zero_iff.mp (hballsub hζ)
      have hζρ : ‖ζ‖ ≤ ρ := by
        simp only [mem_ball, dist_eq_norm] at hζ
        have := norm_le_norm_add_norm_sub' ζ z
        rw [hρdef]; linarith
      refine (qcv_W_koebe (hnormt t htr₀) hζ1).trans ?_
      have hm := qcv_mono_koebe (norm_nonneg ζ) hζρ hρ1
      have hBt := hB t (ball_subset_closedBall ht)
      calc 4 * ‖normalizedSolution (extB (μ + t • ν)) 2‖ * (‖ζ‖ / (1 - ‖ζ‖) ^ 2)
          ≤ 4 * B * (‖ζ‖ / (1 - ‖ζ‖) ^ 2) := by gcongr
        _ ≤ 4 * B * (ρ / (1 - ρ) ^ 2) := by gcongr
    have hMnn : 0 ≤ 4 * B * (ρ / (1 - ρ) ^ 2) := by
      have : 0 ≤ ρ := by rw [hρdef]; positivity
      positivity
    refine qcv_param_iteratedDeriv j (F := W) (c := z) (r := r) (R := R) (M := 4 * B * (ρ / (1 - ρ) ^ 2))
      hRpos hMnn ?_ ?_ hM
    · intro t ht
      exact (qcv_W_props (hnormt t (hrsub (ball_subset_closedBall ht)))).2.1.mono hballsub
    · intro ζ _
      exact (hWt ζ).mono (ball_subset_ball (by linarith))
  -- the scalar functions `t ↦ (bersPhi (μ + t ν)).1 z`
  have hH : ∀ z : unitDisc, DifferentiableOn ℂ (fun t => (bersPhi (μ + t • ν)).1 z) (ball (0 : ℂ) r) := by
    rintro ⟨z, hz⟩
    have hz1 : ‖z‖ < 1 := mem_ball_zero_iff.mp hz
    have hder1 : ∀ t ∈ ball (0 : ℂ) r, deriv (W t) z ≠ 0 := by
      intro t ht
      obtain ⟨-, hd, hi, -⟩ := qcv_W_props (hnormt t (hrsub (ball_subset_closedBall ht)))
      exact deriv_ne_zero_of_injOn isOpen_ball hd (hi.mono (subset_univ _)) hz
    have h1 : DifferentiableOn ℂ (fun t => deriv (W t) z) (ball (0 : ℂ) r) := by
      simpa using hderiv z hz 1
    have h2 := hderiv z hz 2
    have h3 := hderiv z hz 3
    have hsch : DifferentiableOn ℂ (fun t => ((1 - ‖z‖ ^ 2) ^ 2 : ℂ) *
        (iteratedDeriv 3 (W t) z / deriv (W t) z - 3 / 2 * (iteratedDeriv 2 (W t) z / deriv (W t) z) ^ 2))
        (ball (0 : ℂ) r) := by
      refine DifferentiableOn.const_mul ?_ _
      refine DifferentiableOn.sub (h3.div h1 hder1) ?_
      exact ((DifferentiableOn.div h2 h1 hder1).pow 2).const_mul _
    refine hsch.congr ?_
    intro t ht
    have htr₀ : t ∈ ball (0 : ℂ) r₀ := hrsub (ball_subset_closedBall ht)
    have hμt := hball t htr₀
    obtain ⟨-, hd, hi, -⟩ := qcv_W_props (hnormt t htr₀)
    have hspec := (bersPhi_spec hμt).1 z hz
    have hS := qcv_schwarzian_fB_eq hμt hz
    have hWa : AnalyticAt ℂ (W t) z := hd.analyticAt (isOpen_ball.mem_nhds hz)
    rw [qcv_schwarzianHol_iter hWa (hder1 t ht)] at hS
    have hun : (bersPhi (μ + t • ν)).1 ⟨z, hz⟩ = ((1 - ‖z‖ ^ 2) ^ 2 : ℂ) * AInf.toFun (bersPhi (μ + t • ν)) z := by
      have : AInf.toFun (bersPhi (μ + t • ν)) z = (bersPhi (μ + t • ν)).1 ⟨z, hz⟩ / (1 - ‖z‖ ^ 2) ^ 2 := by
        simp only [AInf.toFun, unweight, dif_pos hz]
      rw [this]
      have hne : ((1 - ‖z‖ ^ 2) ^ 2 : ℂ) ≠ 0 := by
        have : (1 - ‖z‖ ^ 2 : ℝ) ≠ 0 := by nlinarith [norm_nonneg z]
        exact_mod_cast pow_ne_zero 2 this
      rw [mul_comm]
      exact (div_mul_cancel₀ _ hne).symm
    rw [hun, hspec, hS]
  have hb : ∀ z : unitDisc, ∀ t ∈ ball (0 : ℂ) r, ‖(bersPhi (μ + t • ν)).1 z‖ ≤ 6 := by
    intro z t ht
    exact (BoundedContinuousFunction.norm_coe_le_norm _ z).trans
      (hbersbd t (hrsub (ball_subset_closedBall ht)))
  exact qcv_ainf_diffAt (Ψ := fun t : ℂ => bersPhi (μ + t • ν)) hrpos (by norm_num) hH hb

/-- **`bersPhi_differentiableOn`** (TT:366, 492): the Bers map `μ ↦ 𝒮(fB μ) ∈ A∞(𝔻)` is holomorphic on `L∞(𝔻*)₁`. -/
theorem qcv_bersPhi_differentiableOn : DifferentiableOn ℂ bersPhi LinfStarBall := by
  haveI : CompleteSpace (AInf unitDisc) := AInf_completeSpace_disc
  refine qcv_gateaux_to_frechet isOpen_ball (fun x hx => ?_) (fun x hx v => qcv_bersPhi_gateaux hx v)
  have hk : ‖x‖ < 1 := by simpa [LinfStarBall] using hx
  refine ⟨1 - ‖x‖, sub_pos.2 hk, 6, fun y hy => ?_⟩
  have hy' : y ∈ LinfStarBall := by
    simp only [mem_ball, dist_eq_norm, LinfStarBall, mem_ball_zero_iff, sub_zero] at hy ⊢
    have := norm_le_norm_add_norm_sub' y x
    linarith
  exact (bersPhi_spec hy').2


end QCV

/-- (TT:492, TT:366) `β ∘ Φ` is holomorphic on `L∞(𝔻*)₁`. Together with `bers_isOpenEmbedding`, this says that
`Φ : L∞(𝔻*)₁ → T(1)` is holomorphic. -/
theorem bersPhi_differentiableOn : DifferentiableOn ℂ bersPhi LinfStarBall :=
  QCV.qcv_bersPhi_differentiableOn

end TakhtajanTeo
