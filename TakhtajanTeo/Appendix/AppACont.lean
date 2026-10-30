import TakhtajanTeo.Ch1.GroupPhase
import TakhtajanTeo.Ch1.BeltramiDerivative
import TakhtajanTeo.Ch1.GroupAlgebra
import TakhtajanTeo.Ch1.S1_1_Completed
import TakhtajanTeo.Ch1.GroupUniformProper
import TakhtajanTeo.Ch1.QCVariation
import TakhtajanTeo.Ch1.ExtPlaneCont

/-!
# INTERFACE: continuous dependence of the normalized maps on `μ` (host `Appendix/AppACont.lean`, prefix `acc_`)

Shared by `ac2_fpp_cont` (下属5) and `ac2_g_open` (下属3). Continuity in `μ ∈ L∞(𝔻*)₁` (norm topology) is stated as
joint continuity on `LinfStarBall ×ˢ univ ⊆ LinfStar × ℂ̄`. Since `ℂ̄` is compact, this is local uniform convergence in
the spherical metric.

Route:
- `acc_wAS_cont` (下属5), by the group law: `wAS μₙ = wAS νₙ ∘ wAS μ₀` with `νₙ = μₙ * μ₀⁻¹ → 0`
  (`bd_differentiableOn`, `grp_mul_inv`). Near `ν = 0`, `gph_near_id_seq` applies, and at `∞` the reflection
  `wAS_refl_comm`.
- `acc_WB_cont` (下属5): the plane solution `W_B` of `extB μ` fixing `0, 1, ∞`. Pointwise holomorphy in `μ`
  (`qcv_planeB_differentiableOn`) plus a normal-family upgrade, and `kn6_uniform_proper` at `∞`.
- Generic pieces (下属1): `acc_mob_cont` (the Möbius action is jointly continuous in the coefficients) and
  `acc_inv_cont` (inverses of jointly continuous bijections of `ℂ̄`, by the closed graph theorem for the compact
  codomain).
- Assembly (下属5): `acc_wAS_inv_cont`, `acc_pole_cont` (the pole `p_μ = w_μ⁻¹(∞)`), and `acc_wB_cont`
  (`wB μ = M ∘ W_B` with `M(0) = 0`, `M'(0) = 1/W_B'(0)`, `M(W_B(p_μ)) = ∞`); `acc_fB_tendsto`.
[CHANGE 2026-10-27, leader-approved] `acc_WA_cont` and `acc_three_point` were dropped (no consumer under the group-law
route).
-/

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal ComplexConjugate Classical Real
noncomputable section
namespace TakhtajanTeo
open LiZhongQC
namespace AppA

/-! ### The Model B plane solution (下属5) -/

theorem acc_WB_qc {μ : LinfStar} (hμ : μ ∈ LinfStarBall) {K : ℝ} (hK : (1 + ‖μ‖) / (1 - ‖μ‖) ≤ K) :
    IsKQCNormalizedPlane (normalizedSolution (extB μ)) K := by
  have hk : ‖μ‖ < 1 := by simpa [LinfStarBall] using hμ
  obtain ⟨f, hf, hfK, -⟩ := thm13_7_normalized_existence (norm_nonneg μ) hk (extB_isBeltramiCoeff μ)
  rw [QCV.qcv_ns_eq (norm_nonneg μ) hk (extB_isBeltramiCoeff μ) hf]
  exact ⟨hfK.mono hK, hf.2.1, hf.2.2.1, hf.2.2.2.1⟩

theorem acc_WB_pt {μs : ℕ → LinfStar} {μ₀ : LinfStar} (hμ₀ : μ₀ ∈ LinfStarBall)
    (hlim : Tendsto μs atTop (𝓝 μ₀)) (z : ℂ) :
    Tendsto (fun n => normalizedSolution (extB (μs n)) z) atTop (𝓝 (normalizedSolution (extB μ₀) z)) :=
  ((((QCV.qcv_planeB_differentiableOn z) μ₀ hμ₀).continuousWithinAt).continuousAt
    (isOpen_ball.mem_nhds hμ₀)).tendsto.comp hlim

/-- Locally uniform convergence of the Model B plane solutions along `μₙ → μ₀`. -/
theorem acc_WB_luc {μs : ℕ → LinfStar} {μ₀ : LinfStar} (hμ₀ : μ₀ ∈ LinfStarBall)
    (hlim : Tendsto μs atTop (𝓝 μ₀)) :
    TendstoLocallyUniformly (fun n => normalizedSolution (extB (μs n))) (normalizedSolution (extB μ₀))
      atTop := by
  have hk : ‖μ₀‖ < 1 := by simpa [LinfStarBall] using hμ₀
  obtain ⟨k, hk0, hk1⟩ : ∃ k : ℝ, ‖μ₀‖ < k ∧ k < 1 := ⟨(1 + ‖μ₀‖) / 2, by linarith, by linarith⟩
  have hev : ∀ᶠ n in atTop, ‖μs n‖ < k := ((continuous_norm.tendsto μ₀).comp hlim).eventually (gt_mem_nhds hk0)
  have hqc : ∀ᶠ n in atTop, IsKQCNormalizedPlane (normalizedSolution (extB (μs n))) ((1 + k) / (1 - k)) := by
    filter_upwards [hev] with n hn
    have hb : μs n ∈ LinfStarBall := by simpa [LinfStarBall] using hn.trans hk1
    refine acc_WB_qc hb ?_
    have h1 : 0 < 1 - k := by linarith
    have h2 : 0 < 1 - ‖μs n‖ := by linarith
    rw [div_le_div_iff₀ h2 h1]
    nlinarith [norm_nonneg (μs n)]
  rw [tendstoLocallyUniformly_iff_forall_isCompact]
  intro S hS
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  by_contra hcon
  rw [not_eventually] at hcon
  obtain ⟨N, hN⟩ := eventually_atTop.1 hqc
  obtain ⟨φ, hφ, hbad⟩ := extraction_of_frequently_atTop (hcon.and_eventually (eventually_ge_atTop N))
  have hK' : ∀ n, IsKQCNormalizedPlane (normalizedSolution (extB (μs (φ n)))) ((1 + k) / (1 - k)) :=
    fun n => hN _ (hbad n).2
  obtain ⟨ψ, hψ, G, hG⟩ := UniversalTeichmuller.ut2_nf_extract hK'
  have hGeq : G = normalizedSolution (extB μ₀) := by
    funext w
    exact tendsto_nhds_unique
      ((tendstoLocallyUniformly_iff_forall_isCompact.1 hG {w} isCompact_singleton).tendsto_at (mem_singleton w))
      ((acc_WB_pt hμ₀ hlim w).comp (hφ.tendsto_atTop.comp hψ.tendsto_atTop))
  rw [hGeq] at hG
  have hU := Metric.tendstoUniformlyOn_iff.1 (tendstoLocallyUniformly_iff_forall_isCompact.1 hG S hS) ε hε
  obtain ⟨n, hn⟩ := hU.exists
  exact (hbad (ψ n)).1 hn

/-- The plane solution of `extB μ` fixing `0, 1, ∞` depends continuously on `μ`, uniformly on `ℂ̄`. -/
theorem acc_WB_cont :
    ContinuousOn (fun p : LinfStar × ExtPlane => OnePoint.map (normalizedSolution (extB p.1)) p.2)
      (LinfStarBall ×ˢ univ) := by
  haveI := k22_t_firstCountable
  rintro ⟨μ₀, w₀⟩ ⟨hμ₀, -⟩
  show Tendsto _ (𝓝[LinfStarBall ×ˢ univ] (μ₀, w₀)) _
  rw [Filter.tendsto_iff_seq_tendsto]
  intro x hx
  have hx' := tendsto_nhdsWithin_iff.mp hx
  have h1 : Tendsto (fun n => (x n).1) atTop (𝓝 μ₀) := (continuous_fst.tendsto _).comp hx'.1
  have h2 : Tendsto (fun n => (x n).2) atTop (𝓝 w₀) := (continuous_snd.tendsto _).comp hx'.1
  have hL := acc_WB_luc hμ₀ h1
  have hW0 := acc_WB_qc hμ₀ le_rfl
  have hW0c : Continuous (normalizedSolution (extB μ₀)) := continuousOn_univ.1 hW0.1.2.2.1.1
  induction w₀ using OnePoint.rec with
  | coe z₀ =>
    have hfin : ContinuousAt finPart (z₀ : ExtPlane) :=
      OnePoint.isOpenEmbedding_coe.continuousAt_iff.mp (continuousAt_id : ContinuousAt (fun x : ℂ => x) z₀)
    have hz : Tendsto (fun n => finPart (x n).2) atTop (𝓝 z₀) := hfin.tendsto.comp h2
    have hev : ∀ᶠ n in atTop, (x n).2 ≠ extInf := by
      filter_upwards [h2.eventually (OnePoint.isOpen_range_coe.mem_nhds ⟨z₀, rfl⟩)] with n hn
      obtain ⟨y, hy⟩ := hn
      rw [← hy]
      exact OnePoint.coe_ne_infty y
    have hval := (OnePoint.continuous_coe.tendsto _).comp (hL.tendsto_comp hW0c.continuousAt hz)
    refine hval.congr' ?_
    filter_upwards [hev] with n hn
    show ((normalizedSolution (extB (x n).1) (finPart (x n).2) : ℂ) : ExtPlane) =
      OnePoint.map (normalizedSolution (extB (x n).1)) (x n).2
    conv_rhs => rw [← coe_finPart_of_ne hn]
    rfl
  | infty =>
    show Tendsto _ atTop (𝓝 (OnePoint.map (normalizedSolution (extB μ₀)) extInf))
    rw [show OnePoint.map (normalizedSolution (extB μ₀)) extInf = extInf from rfl]
    refine OnePoint.hasBasis_nhds_infty.tendsto_right_iff.mpr fun s hs => ?_
    obtain ⟨R₀, hR₀⟩ := hs.2.isBounded.subset_closedBall 0
    set R : ℝ := max R₀ 1
    have hR : 0 < R := lt_of_lt_of_le one_pos (le_max_right _ _)
    have hsR : s ⊆ closedBall 0 R := hR₀.trans (closedBall_subset_closedBall (le_max_left _ _))
    -- homeomorphisms along the tail
    have hball : ∀ᶠ n in atTop, (x n).1 ∈ LinfStarBall := hx'.2.mono fun n hn => hn.1
    obtain ⟨N, hN⟩ := eventually_atTop.1 hball
    have he : ∀ n, ∃ e : ℂ ≃ₜ ℂ, ⇑e = normalizedSolution (extB (x (n + N)).1) := fun n =>
      have h := acc_WB_qc (hN (n + N) (by omega)) le_rfl
      t1_homeomorph h.1 h.2.1
    choose E hE using he
    obtain ⟨e₀, he₀⟩ := t1_homeomorph hW0.1 hW0.2.1
    have hLE : TendstoLocallyUniformly (fun n => ⇑(E n)) ⇑e₀ atTop := by
      rw [tendstoLocallyUniformly_iff_forall_isCompact] at hL ⊢
      intro K hK
      have h := hL K hK
      rw [Metric.tendstoUniformlyOn_iff] at h ⊢
      intro ε hε
      filter_upwards [(tendsto_add_atTop_nat N).eventually (h ε hε)] with n hn
      intro z hz
      rw [he₀, hE n]
      exact hn z hz
    obtain ⟨S, hS0, hSev⟩ := kn6_uniform_proper hLE R hR
    obtain ⟨M, hM⟩ := eventually_atTop.1 hSev
    have hfar : ∀ᶠ n in atTop, (x n).2 ∈ (↑) '' (closedBall (0 : ℂ) S)ᶜ ∪ {extInf} :=
      h2.eventually (OnePoint.hasBasis_nhds_infty.mem_of_mem ⟨isClosed_closedBall, isCompact_closedBall 0 S⟩)
    filter_upwards [hfar, eventually_ge_atTop (M + N)] with n hn hnMN
    rcases hn with ⟨z, hz, hzn⟩ | hinf
    · left
      refine ⟨normalizedSolution (extB (x n).1) z, fun hzs => ?_, ?_⟩
      · have hzS : S ≤ ‖z‖ := by
          have : ¬ ‖z‖ ≤ S := by simpa [mem_closedBall, dist_zero_right] using hz
          linarith [not_le.mp this]
        have hb := hM (n - N) (by omega) z hzS
        rw [hE (n - N), Nat.sub_add_cancel (by omega : N ≤ n)] at hb
        have := hsR hzs
        rw [mem_closedBall, dist_zero_right] at this
        linarith
      · show ((normalizedSolution (extB (x n).1) z : ℂ) : ExtPlane) =
          OnePoint.map (normalizedSolution (extB (x n).1)) (x n).2
        rw [← hzn]
        rfl
    · right
      rw [mem_singleton_iff] at hinf ⊢
      show OnePoint.map (normalizedSolution (extB (x n).1)) (x n).2 = extInf
      rw [hinf]
      rfl

/-! ### The normalized maps of Models A and B (下属5) -/

theorem acc_rho_cont : Continuous (fun p : ExtPlane => mobiusExt 0 1 1 0 (OnePoint.map conj p)) := by
  have h1 : Continuous (OnePoint.map conj : ExtPlane → ExtPlane) :=
    (Complex.conjLIE.toHomeomorph.onePointCongr).continuous
  exact (mobiusHomeomorph 0 1 1 0 (by norm_num)).continuous.comp h1

/-- Near `ν = 0`, `(ν, v) ↦ w_ν(v)` tends to `v₀` at finite points. -/
theorem acc_near_id_coe (z₀ : ℂ) :
    Tendsto (fun p : LinfStar × ExtPlane => wAS p.1 p.2) ((𝓝[LinfStarBall] 0) ×ˢ 𝓝 (z₀ : ExtPlane))
      (𝓝 (z₀ : ExtPlane)) := by
  rw [OnePoint.nhds_coe_eq]
  refine (Metric.nhds_basis_ball.map _).tendsto_right_iff.mpr fun ε hε => ?_
  obtain ⟨δ, hδ, hnear⟩ := gph_near_id_all (R := ‖z₀‖ + 1) (half_pos hε)
  have h1 : ∀ᶠ ν in 𝓝[LinfStarBall] (0 : LinfStar), ν ∈ LinfStarBall ∧ ‖ν‖ < δ := by
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Metric.ball_mem_nhds (0 : LinfStar) hδ)] with ν h1 h2
    exact ⟨h1, by simpa using h2⟩
  have h2 : ∀ᶠ v : ExtPlane in Filter.map (fun z : ℂ => (z : ExtPlane)) (𝓝 z₀), ∃ z : ℂ, v = (z : ExtPlane) ∧ ‖z - z₀‖ < min (ε / 2) 1 := by
    rw [Filter.eventually_map]
    filter_upwards [Metric.ball_mem_nhds z₀ (lt_min (half_pos hε) one_pos)] with z hz
    exact ⟨z, rfl, by simpa [dist_eq_norm] using hz⟩
  filter_upwards [h1.prod_mk h2] with p hp
  obtain ⟨⟨hb, hs⟩, z, hz, hzz⟩ := hp
  have hR : ‖z‖ ≤ ‖z₀‖ + 1 := by
    have h3 : ‖z - z₀‖ < 1 := lt_of_lt_of_le hzz (min_le_right _ _)
    linarith [norm_sub_norm_le z z₀]
  obtain ⟨hne, hlt⟩ := hnear p.1 hb hs z hR
  refine ⟨wA p.1 z, ?_, ?_⟩
  · show dist (wA p.1 z) z₀ < ε
    rw [dist_eq_norm]
    calc ‖wA p.1 z - z₀‖ ≤ ‖wA p.1 z - z‖ + ‖z - z₀‖ := by
          rw [show wA p.1 z - z₀ = (wA p.1 z - z) + (z - z₀) by ring]; exact norm_add_le _ _
      _ < ε / 2 + ε / 2 := add_lt_add hlt (lt_of_lt_of_le hzz (min_le_left _ _))
      _ = ε := by ring
  · show ((wA p.1 z : ℂ) : ExtPlane) = wAS p.1 p.2
    rw [hz]
    obtain ⟨y, hy⟩ := OnePoint.ne_infty_iff_exists.mp hne
    show ((finPart (wAS p.1 (z : ExtPlane)) : ℂ) : ExtPlane) = wAS p.1 (z : ExtPlane)
    rw [← hy]
    rfl

/-- Near `ν = 0`, `(ν, v) ↦ w_ν(v)` tends to `v₀` at every point of `ℂ̄`. -/
theorem acc_near_id (v₀ : ExtPlane) :
    Tendsto (fun p : LinfStar × ExtPlane => wAS p.1 p.2) ((𝓝[LinfStarBall] 0) ×ˢ 𝓝 v₀) (𝓝 v₀) := by
  induction v₀ using OnePoint.rec with
  | coe z₀ => exact acc_near_id_coe z₀
  | infty =>
    set ρ : ExtPlane → ExtPlane := fun p => mobiusExt 0 1 1 0 (OnePoint.map conj p) with hρdef
    have hρc : Continuous ρ := acc_rho_cont
    have hρi : ρ extInf = ((0 : ℂ) : ExtPlane) := rho_infty
    have hρ0 : ρ ((0 : ℂ) : ExtPlane) = extInf := rho_zero
    have hmap : Tendsto (fun p : LinfStar × ExtPlane => (p.1, ρ p.2)) ((𝓝[LinfStarBall] 0) ×ˢ 𝓝 extInf)
        ((𝓝[LinfStarBall] 0) ×ˢ 𝓝 ((0 : ℂ) : ExtPlane)) := by
      refine tendsto_id.prodMap ?_
      rw [← hρi]
      exact hρc.continuousAt
    have h := (hρc.tendsto _).comp ((acc_near_id_coe 0).comp hmap)
    rw [hρ0] at h
    refine h.congr' ?_
    have hb : ∀ᶠ p : LinfStar × ExtPlane in (𝓝[LinfStarBall] 0) ×ˢ 𝓝 extInf, p.1 ∈ LinfStarBall :=
      tendsto_fst.eventually self_mem_nhdsWithin
    filter_upwards [hb] with p hp
    show ρ (wAS p.1 (ρ p.2)) = wAS p.1 p.2
    rw [wAS_refl_comm hp]
    exact rho_invol _

/-- `μ ↦ w_μ` (Model A) is continuous, uniformly on `ℂ̄`. -/
theorem acc_wAS_cont : ContinuousOn (fun p : LinfStar × ExtPlane => wAS p.1 p.2) (LinfStarBall ×ˢ univ) := by
  rintro ⟨μ₀, w₀⟩ ⟨hμ₀, -⟩
  have hinv : beltramiInv μ₀ ∈ LinfStarBall := (wA_mul hμ₀ hμ₀).2.2.1
  -- `N μ = μ * μ₀⁻¹ → 0`
  have hNc : ContinuousWithinAt (fun l => beltramiMul l (beltramiInv μ₀)) LinfStarBall μ₀ :=
    ((bd_differentiableOn hinv) μ₀ hμ₀).continuousWithinAt
  have hN0 : beltramiMul μ₀ (beltramiInv μ₀) = 0 := grp_mul_inv hμ₀
  have hNmem : ∀ l ∈ LinfStarBall, beltramiMul l (beltramiInv μ₀) ∈ LinfStarBall := fun l hl =>
    (wA_mul hinv hl).1
  have hN : Tendsto (fun l => beltramiMul l (beltramiInv μ₀)) (𝓝[LinfStarBall] μ₀) (𝓝[LinfStarBall] 0) := by
    rw [← hN0]
    exact tendsto_nhdsWithin_iff.mpr ⟨hNc, eventually_mem_nhdsWithin.mono hNmem⟩
  obtain ⟨e, he⟩ := wAS_isHomeo hμ₀
  have hW : Tendsto (wAS μ₀) (𝓝 w₀) (𝓝 (wAS μ₀ w₀)) := by
    rw [← he]; exact e.continuous.tendsto w₀
  have hG := (acc_near_id (wAS μ₀ w₀)).comp (hN.prodMap hW)
  show Tendsto _ (𝓝[LinfStarBall ×ˢ univ] (μ₀, w₀)) _
  rw [nhdsWithin_prod_eq, nhdsWithin_univ]
  refine hG.congr' ?_
  filter_upwards [tendsto_fst.eventually (self_mem_nhdsWithin : LinfStarBall ∈ 𝓝[LinfStarBall] μ₀)] with p hp
  show wAS (beltramiMul p.1 (beltramiInv μ₀)) (wAS μ₀ p.2) = wAS p.1 p.2
  rw [(wA_mul hinv hp).2.1]
  show wAS p.1 (wAS (beltramiInv μ₀) (wAS μ₀ p.2)) = wAS p.1 p.2
  have hc := congrFun (grp_wAS_inv_right hμ₀) p.2
  simp only [Function.comp_apply, id] at hc
  rw [hc]

theorem acc_ns_spec {μ : LinfStar} (hμ : μ ∈ LinfStarBall) :
    IsNormalizedSolution (normalizedSolution (extB μ)) (extB μ) := by
  have hk : ‖μ‖ < 1 := by simpa [LinfStarBall] using hμ
  exact QCV.qcv_ns_spec (norm_nonneg μ) hk (extB_isBeltramiCoeff μ)

/-- Normalizing a Möbius map with `b = 0` by `d ≠ 0`. -/
theorem acc_mob_scale {a c d : ℂ} (hd : d ≠ 0) (u : ExtPlane) :
    mobiusExt a 0 c d u = mobiusExt (a / d) 0 (c / d) 1 u := by
  induction u using OnePoint.rec with
  | infty =>
    by_cases hc : c = 0
    · rw [mobiusExt_infty_of_eq hc, mobiusExt_infty_of_eq (by rw [hc, zero_div])]
    · rw [mobiusExt_infty_of_ne hc, mobiusExt_infty_of_ne (div_ne_zero hc hd)]
      congr 1
      field_simp
  | coe z =>
    by_cases hz : c * z + d = 0
    · rw [mobiusExt_coe_of_eq_zero hz, mobiusExt_coe_of_eq_zero]
      field_simp
      linear_combination hz
    · have hz' : c / d * z + 1 ≠ 0 := by
        intro h; apply hz
        field_simp at h
        linear_combination h
      rw [mobiusExt_coe hz, mobiusExt_coe hz']
      congr 1
      simp only [mobiusFn]
      field_simp
      ring

/-- `q ↦ 1/q` sends every `q ≠ 0` of `ℂ̄` to a finite point. -/
theorem acc_recip_ne_infty {q : ExtPlane} (hq : q ≠ ((0 : ℂ) : ExtPlane)) : mobiusExt 0 1 1 0 q ≠ extInf := by
  induction q using OnePoint.rec with
  | infty =>
    rw [mobiusExt_infty_of_ne one_ne_zero]
    exact OnePoint.coe_ne_infty _
  | coe z =>
    have hz : z ≠ 0 := fun h => hq (by rw [h])
    rw [mobiusExt_coe (by simpa using hz)]
    exact OnePoint.coe_ne_infty _

/-- Möbius form of `w^μ`: `w^μ = M ∘ W_B` with `M(z) = αz/(1 + γz)`, `α = 1/W_B'(0)`, `γ = -1/W_B(p_μ)`. -/
theorem acc_wB_rep {μ : LinfStar} (hμ : μ ∈ LinfStarBall) :
    deriv (normalizedSolution (extB μ)) 0 ≠ 0 ∧
      OnePoint.map (normalizedSolution (extB μ)) (Function.invFun (wAS μ) extInf) ≠ ((0 : ℂ) : ExtPlane) ∧
      ∀ v, wB μ v = mobiusExt (1 / deriv (normalizedSolution (extB μ)) 0) 0
        (-finPart (mobiusExt 0 1 1 0
          (OnePoint.map (normalizedSolution (extB μ)) (Function.invFun (wAS μ) extInf)))) 1
        (OnePoint.map (normalizedSolution (extB μ)) v) := by
  have hk : ‖μ‖ < 1 := by simpa [LinfStarBall] using hμ
  obtain ⟨M, hM, W, hW, hfinite, hinf, f, hf, hf0, hf1, hfp⟩ := (wB_spec hμ).1
  rw [QCV.qcv_ns_eq (norm_nonneg μ) hk (extB_isBeltramiCoeff μ) hW]
  set p := Function.invFun (wAS μ) extInf
  obtain ⟨a, b, c, d, hdet, rfl⟩ := hM
  have hrepM : ∀ v, wB μ v = mobiusExt a b c d (OnePoint.map W v) := by
    intro v
    induction v using OnePoint.rec with
    | infty => exact hinf
    | coe z => exact hfinite z
  have h0D : (0 : ℂ) ∈ unitDisc := by simp [unitDisc]
  have hW0 : W 0 = 0 := hW.2.2.1
  have hM0 : mobiusExt a b c d ((0 : ℂ) : ExtPlane) = ((0 : ℂ) : ExtPlane) := by
    have h := (hfinite 0).symm.trans (hf 0 h0D)
    rw [hW0, hf0] at h
    exact h
  have hd : d ≠ 0 := by
    intro hd0
    rw [mobiusExt_coe_of_eq_zero (by simp [hd0])] at hM0
    exact OnePoint.infty_ne_coe _ hM0
  have hb : b = 0 := by
    rw [mobiusExt_coe (by simpa using hd)] at hM0
    have h : b / d = 0 := by simpa [mobiusFn] using OnePoint.coe_injective hM0
    exact (div_eq_zero_iff.mp h).resolve_right hd
  subst hb
  -- the derivative at `0`
  have hhol : DifferentiableOn ℂ W unitDisc := extB_solution_holomorphic hW
  have hden : ∀ z ∈ unitDisc, c * W z + d ≠ 0 := by
    intro z hz he
    have hfin := (hfinite z).symm.trans (hf z hz)
    rw [mobiusExt_coe_of_eq_zero he] at hfin
    exact OnePoint.infty_ne_coe _ hfin
  have hfe : f =ᶠ[𝓝 0] fun z => mobiusFn a 0 c d (W z) := by
    filter_upwards [isOpen_ball.mem_nhds h0D] with z hz
    have h := (hf z hz).symm.trans (hfinite z)
    rw [mobiusExt_coe (hden z hz)] at h
    exact OnePoint.coe_injective h
  have hWa : AnalyticAt ℂ W 0 := hhol.analyticAt (isOpen_ball.mem_nhds h0D)
  have hd0 : c * W 0 + d ≠ 0 := by rw [hW0]; simpa using hd
  have hder := (mobius_comp_first_second (a := a) (b := 0) hWa hd0).1
  rw [← hfe.deriv_eq, hf1, hW0] at hder
  have hWd : deriv W 0 ≠ 0 := by
    intro h; rw [h, mul_zero] at hder; exact one_ne_zero hder
  have h2 : (a * d - 0 * c) / (c * 0 + d) ^ 2 = a / d := by
    rw [zero_mul, sub_zero, mul_zero, zero_add, pow_two, mul_div_mul_right _ _ hd]
  rw [h2] at hder
  have hα : a / d = 1 / deriv W 0 := by
    rw [eq_div_iff hWd]
    exact hder.symm
  -- the pole
  have hq : mobiusExt a 0 c d (OnePoint.map W p) = extInf := (hrepM p).symm.trans hfp
  have hq0 : OnePoint.map W p ≠ ((0 : ℂ) : ExtPlane) := by
    intro h; rw [h, hM0] at hq; exact OnePoint.coe_ne_infty _ hq
  have hγ : c / d = -finPart (mobiusExt 0 1 1 0 (OnePoint.map W p)) := by
    revert hq hq0
    generalize OnePoint.map W p = q
    intro hq hq0
    induction q using OnePoint.rec with
    | infty =>
      have hc : c = 0 := by
        by_contra hc
        rw [mobiusExt_infty_of_ne hc] at hq
        exact OnePoint.coe_ne_infty _ hq
      rw [mobiusExt_infty_of_ne one_ne_zero, hc]
      simp [finPart]
    | coe z =>
      have hz : z ≠ 0 := fun h => hq0 (by rw [h])
      have hcz : c * z + d = 0 := by
        by_contra h
        rw [mobiusExt_coe h] at hq
        exact OnePoint.coe_ne_infty _ hq
      rw [mobiusExt_coe (by simpa using hz)]
      show c / d = -((0 * z + 1) / (1 * z + 0))
      rw [div_eq_iff hd, show -((0 * z + 1) / (1 * z + 0)) * d = -d / z by ring, eq_div_iff hz]
      linear_combination hcz
  refine ⟨hWd, hq0, fun v => ?_⟩
  rw [hrepM v, acc_mob_scale hd, hα, hγ]

/-- `μ ↦ W_B'(0)` is continuous on the ball. -/
theorem acc_dW0_cont :
    ContinuousOn (fun μ : LinfStar => deriv (normalizedSolution (extB μ)) 0) LinfStarBall := by
  intro μ₀ hμ₀
  rw [ContinuousWithinAt, Filter.tendsto_iff_seq_tendsto]
  intro x hx
  have hx' := tendsto_nhdsWithin_iff.mp hx
  have hL := (acc_WB_luc hμ₀ hx'.1).tendstoLocallyUniformlyOn (s := unitDisc)
  have hD := hL.deriv (hx'.2.mono fun n hn => extB_solution_holomorphic (acc_ns_spec hn)) isOpen_ball
  exact hD.tendsto_at (by simp [unitDisc] : (0 : ℂ) ∈ unitDisc)

/-- `μ ↦ w_μ⁻¹` (Model A) is continuous, uniformly on `ℂ̄`. -/
theorem acc_wAS_inv_cont :
    ContinuousOn (fun p : LinfStar × ExtPlane => Function.invFun (wAS p.1) p.2) (LinfStarBall ×ˢ univ) :=
  acc_inv_cont acc_wAS_cont (fun μ _ => wAS_bijective μ)

/-- The pole `p_μ = w_μ⁻¹(∞)` of Model B depends continuously on `μ`. -/
theorem acc_pole_cont : ContinuousOn (fun μ : LinfStar => Function.invFun (wAS μ) extInf) LinfStarBall := by
  have h := ContinuousOn.comp (g := fun p : LinfStar × ExtPlane => Function.invFun (wAS p.1) p.2)
    (f := fun μ : LinfStar => (μ, extInf)) acc_wAS_inv_cont (continuousOn_id.prodMk continuousOn_const)
    (fun μ hμ => ⟨hμ, mem_univ _⟩)
  exact h

/-- `μ ↦ w^μ` (Model B) is continuous, uniformly on `ℂ̄`. -/
theorem acc_wB_cont : ContinuousOn (fun p : LinfStar × ExtPlane => wB p.1 p.2) (LinfStarBall ×ˢ univ) := by
  have hq : ContinuousOn (fun μ : LinfStar =>
      OnePoint.map (normalizedSolution (extB μ)) (Function.invFun (wAS μ) extInf)) LinfStarBall := by
    have h := ContinuousOn.comp
      (g := fun p : LinfStar × ExtPlane => OnePoint.map (normalizedSolution (extB p.1)) p.2)
      (f := fun μ : LinfStar => (μ, Function.invFun (wAS μ) extInf)) acc_WB_cont
      (continuousOn_id.prodMk acc_pole_cont) (fun μ hμ => ⟨hμ, mem_univ _⟩)
    exact h
  have hR := (mobiusHomeomorph 0 1 1 0 (by norm_num)).continuous.comp_continuousOn hq
  have hC : ContinuousOn (fun μ : LinfStar => -finPart (mobiusExt 0 1 1 0
      (OnePoint.map (normalizedSolution (extB μ)) (Function.invFun (wAS μ) extInf)))) LinfStarBall := by
    intro μ hμ
    obtain ⟨y, hy⟩ := OnePoint.ne_infty_iff_exists.mp (acc_recip_ne_infty (acc_wB_rep hμ).2.1)
    have hfin : ContinuousAt finPart (mobiusExt 0 1 1 0
        (OnePoint.map (normalizedSolution (extB μ)) (Function.invFun (wAS μ) extInf))) := by
      rw [← hy]
      exact OnePoint.isOpenEmbedding_coe.continuousAt_iff.mp (continuousAt_id : ContinuousAt (fun x : ℂ => x) y)
    exact (ContinuousAt.comp_continuousWithinAt (g := finPart) (f := fun μ : LinfStar => mobiusExt 0 1 1 0
      (OnePoint.map (normalizedSolution (extB μ)) (Function.invFun (wAS μ) extInf))) hfin (hR μ hμ)).neg
  have hα : ContinuousOn (fun μ : LinfStar => 1 / deriv (normalizedSolution (extB μ)) 0) LinfStarBall :=
    continuousOn_const.div acc_dW0_cont (fun μ hμ => (acc_wB_rep hμ).1)
  have hcoef : ContinuousOn (fun p : LinfStar × ExtPlane =>
      (((1 / deriv (normalizedSolution (extB p.1)) 0, (0 : ℂ),
        -finPart (mobiusExt 0 1 1 0
          (OnePoint.map (normalizedSolution (extB p.1)) (Function.invFun (wAS p.1) extInf))), (1 : ℂ)) :
          ℂ × ℂ × ℂ × ℂ), OnePoint.map (normalizedSolution (extB p.1)) p.2)) (LinfStarBall ×ˢ univ) := by
    have hfst : MapsTo Prod.fst (LinfStarBall ×ˢ (univ : Set ExtPlane)) LinfStarBall := fun p (hp : p ∈ LinfStarBall ×ˢ (univ : Set ExtPlane)) => hp.1
    refine ContinuousOn.prodMk ?_ acc_WB_cont
    exact (hα.comp continuousOn_fst hfst).prodMk (continuousOn_const.prodMk
      ((hC.comp continuousOn_fst hfst).prodMk continuousOn_const))
  refine (acc_mob_cont.comp hcoef ?_).congr ?_
  · intro p hp
    refine ⟨?_, mem_univ _⟩
    show 1 / deriv (normalizedSolution (extB p.1)) 0 * 1 - 0 * _ ≠ 0
    rw [mul_one, zero_mul, sub_zero]
    exact one_div_ne_zero (acc_wB_rep hp.1).1
  · intro p hp
    exact (acc_wB_rep hp.1).2.2 p.2

/-- Sequential form for consumers (`ac2_g_open`): if `‖νₙ - ν‖∞ → 0`, then `fB νₙ → fB ν` uniformly on every compact
`S ⊆ ℂ` avoiding the pole `p_ν` of `w^ν`. Near the pole the finite parts cannot converge uniformly. -/
theorem acc_fB_tendsto {ν : LinfStar} (hν : ν ∈ LinfStarBall) {νs : ℕ → LinfStar} (hνs : ∀ n, νs n ∈ LinfStarBall)
    (hlim : Tendsto (fun n => ‖νs n - ν‖) atTop (𝓝 0)) {S : Set ℂ} (hS : IsCompact S)
    (hfin : ∀ z ∈ S, wB ν (z : ExtPlane) ≠ extInf) :
    TendstoUniformlyOn (fun n => fB (νs n)) (fB ν) atTop S := by
  have hG : ContinuousOn (fun p : LinfStar × ℂ => wB p.1 (p.2 : ExtPlane)) (LinfStarBall ×ˢ univ) := by
    have h := ContinuousOn.comp (g := fun p : LinfStar × ExtPlane => wB p.1 p.2)
      (f := fun p : LinfStar × ℂ => (p.1, (p.2 : ExtPlane))) acc_wB_cont
      (continuousOn_fst.prodMk (OnePoint.continuous_coe.comp continuous_snd).continuousOn)
      (fun (p : LinfStar × ℂ) (hp : p ∈ LinfStarBall ×ˢ (univ : Set ℂ)) => ⟨hp.1, mem_univ _⟩)
    exact h
  set W : Set (LinfStar × ℂ) :=
    (LinfStarBall ×ˢ univ) ∩ (fun p : LinfStar × ℂ => wB p.1 (p.2 : ExtPlane)) ⁻¹' {extInf}ᶜ with hWdef
  have hWo : IsOpen W := hG.isOpen_inter_preimage (isOpen_ball.prod isOpen_univ) isClosed_singleton.isOpen_compl
  have hsub : ({ν} : Set LinfStar) ×ˢ S ⊆ W := by
    rintro ⟨μ, z⟩ ⟨hμ, hz⟩
    rw [mem_singleton_iff] at hμ
    subst hμ
    exact ⟨⟨hν, mem_univ _⟩, hfin z hz⟩
  obtain ⟨U, V, hU, -, hνU, hSV, hUV⟩ := generalized_tube_lemma isCompact_singleton hS hWo hsub
  have hνU' : ν ∈ U := hνU (mem_singleton ν)
  set s' := U ∩ LinfStarBall
  have hF : ContinuousOn (Function.uncurry fun (μ : LinfStar) (z : ℂ) => fB μ z) (s' ×ˢ S) := by
    rintro ⟨μ, z⟩ ⟨hμ, hz⟩
    have hW : (μ, z) ∈ W := hUV ⟨hμ.1, hSV hz⟩
    have hW2 : wB μ (z : ExtPlane) ≠ extInf := hW.2
    obtain ⟨y, hy⟩ := OnePoint.ne_infty_iff_exists.mp hW2
    have hfin' : ContinuousAt finPart (wB μ (z : ExtPlane)) := by
      rw [← hy]
      exact OnePoint.isOpenEmbedding_coe.continuousAt_iff.mp (continuousAt_id : ContinuousAt (fun x : ℂ => x) y)
    exact ContinuousAt.comp_continuousWithinAt (g := finPart)
      (f := fun p : LinfStar × ℂ => wB p.1 (p.2 : ExtPlane)) hfin'
      ((hG (μ, z) ⟨hμ.2, mem_univ _⟩).mono fun (p : LinfStar × ℂ) (hp : p ∈ s' ×ˢ S) => ⟨hp.1.2, mem_univ _⟩)
  have hconv : Tendsto νs atTop (𝓝[s'] ν) := by
    have h := tendsto_iff_norm_sub_tendsto_zero.mpr hlim
    exact tendsto_nhdsWithin_iff.mpr ⟨h, (h.eventually (hU.mem_nhds hνU')).mono fun n hn => ⟨hn, hνs n⟩⟩
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  obtain ⟨v, hv, hvp⟩ := hS.mem_uniformity_of_prod hF ⟨hνU', hν⟩ (Metric.dist_mem_uniformity hε)
  filter_upwards [hconv hv] with n hn x hx
  rw [dist_comm]
  exact hvp _ hn x hx

end AppA
end TakhtajanTeo
