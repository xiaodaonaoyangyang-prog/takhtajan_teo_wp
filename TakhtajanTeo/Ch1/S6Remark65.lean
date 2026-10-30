import TakhtajanTeo.Ch1.S6Eq64
import TakhtajanTeo.Ch1.WRegFoundation

/-!
# Remark 6.5 (polarization of Proposition 6.3): interface (下属5, 2026-10-28)

Host module `TakhtajanTeo/Ch1/S6Remark65.lean`, prefix `r65_`. Imports `TakhtajanTeo.Ch1.S6Eq64` (program A,
provides `e64_prop_6_3`) and `TakhtajanTeo.Ch1.WRegFoundation`.

Owners: `[W5]` = 下属5, `[W4]` = 下属4, `[W3]` = 下属3.

**Route.**
* **Four-parameter family** (Part F). `Q = ((a₁, a₂), (b₁, b₂))`, coefficient `a₁m₁ + a₂m₂ + b₁n₁ + b₂n₂`.
  Joint ℂ-differentiability in `Q` is `qcv_plane_hasFDerivAt` with `E = (ℂ × ℂ) × (ℂ × ℂ)` (F1). Joint continuity
  of the solution and its inverse (F2, F3) are the proofs of `wr_ns2_cont`/`wr_ns2_inv_cont` with `E` in place of
  `ℂ × ℂ`. For `z`-regularity (F4) the hypothesis `m₂ = n₂ = 0` on `Ω` makes the cutoff family of D1 the
  **two-parameter** family `χ·(a₁m₁ + b₁n₁)` at the parameter `(a₁, b₁)`, so the installed A3 (`wr_smooth_family`)
  is reused unchanged; only D1/D2b are re-run with `E`. F5 is the four-parameter D2a `[W4]`; F6 assembles.
* **Model `𝕌`** (Part U). `extU (e₁μ + e₂ν) = e₁m₁ + ē₁m₂ + e₂n₁ + ē₂n₂` (U1); on `𝕌`, `m₂ = n₂ = 0`. U2 is the
  E2 analogue in two directions; U3: `e ↦ ρ^{e₁μ+e₂ν}(z)` is `C²` at `0` (`w₀ = id`, so `w - w̄ ≠ 0` near `0`).
* **Polarization** (Part P, `[W3]`). P1: for `F` `C²` at `0`,
  `∂_{e₁}∂̄_{e₂}F(0) = ¼ Σ_{λ ∈ {1,-1,i,-i}} λ ∂∂̄[ε ↦ F(ε, λε)](0)`. P2: harmonicity is closed under `μ + λν`.
  P3: `G(μν̄) = ¼ Σ λ G(|μ + λν|²)` (pointwise `¼ Σ λ|μ + λν|² = μν̄`; integrability from
  `harmonicU_resolvent_product_integrable`).
* **Assembly** `[W5]`: P1 + U3, `F(ε, λε) = rhoVar (μ + λν) ε z`, `e64_prop_6_3` for each `λ`, then P3.

No new definitions. No `set_option`.
-/

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal ComplexConjugate Classical Real

noncomputable section

namespace TakhtajanTeo

open LiZhongQC

/-! ## Part F — four-parameter normalized family -/

/-- Four-parameter linear coefficient bound (as `wr_coeff_lin`). -/
theorem r65_coeff_lin4 {m₁ m₂ n₁ n₂ : ℂ → ℂ} {k₁ k₂ k₃ k₄ : ℝ} (hm₁ : IsBeltramiCoeff m₁ univ k₁)
    (hm₂ : IsBeltramiCoeff m₂ univ k₂) (hn₁ : IsBeltramiCoeff n₁ univ k₃) (hn₂ : IsBeltramiCoeff n₂ univ k₄)
    (v : (ℂ × ℂ) × (ℂ × ℂ)) :
    IsBeltramiCoeff (fun u => v.1.1 * m₁ u + v.1.2 * m₂ u + v.2.1 * n₁ u + v.2.2 * n₂ u) univ
      ((|k₁| + |k₂| + |k₃| + |k₄|) * ‖v‖) := by
  refine ⟨(((hm₁.1.const_mul v.1.1).add (hm₂.1.const_mul v.1.2)).add (hn₁.1.const_mul v.2.1)).add
    (hn₂.1.const_mul v.2.2), ?_⟩
  filter_upwards [hm₁.2, hm₂.2, hn₁.2, hn₂.2] with u h₁ h₂ h₃ h₄
  have hv1 : ‖v.1.1‖ ≤ ‖v‖ := (norm_fst_le v.1).trans (norm_fst_le v)
  have hv2 : ‖v.1.2‖ ≤ ‖v‖ := (norm_snd_le v.1).trans (norm_fst_le v)
  have hv3 : ‖v.2.1‖ ≤ ‖v‖ := (norm_fst_le v.2).trans (norm_snd_le v)
  have hv4 : ‖v.2.2‖ ≤ ‖v‖ := (norm_snd_le v.2).trans (norm_snd_le v)
  have t : ∀ (a : ℂ) (x : ℂ) (k : ℝ), ‖a‖ ≤ ‖v‖ → ‖x‖ ≤ k → ‖a * x‖ ≤ ‖v‖ * |k| := fun a x k ha hx => by
    rw [norm_mul]; exact mul_le_mul ha (hx.trans (le_abs_self _)) (norm_nonneg _) (norm_nonneg _)
  have e1 := norm_add_le (v.1.1 * m₁ u + v.1.2 * m₂ u + v.2.1 * n₁ u) (v.2.2 * n₂ u)
  have e2 := norm_add_le (v.1.1 * m₁ u + v.1.2 * m₂ u) (v.2.1 * n₁ u)
  have e3 := norm_add_le (v.1.1 * m₁ u) (v.1.2 * m₂ u)
  have t1 := t _ _ _ hv1 h₁
  have t2 := t _ _ _ hv2 h₂
  have t3 := t _ _ _ hv3 h₃
  have t4 := t _ _ _ hv4 h₄
  have e : (|k₁| + |k₂| + |k₃| + |k₄|) * ‖v‖ = ‖v‖ * |k₁| + ‖v‖ * |k₂| + ‖v‖ * |k₃| + ‖v‖ * |k₄| := by ring
  rw [e]
  linarith

/-- Locally uniform bound `k < 1` near a parameter with bound `k₀ < 1` (as `wr_loc_unif`). -/
theorem r65_loc_unif4 {m₁ m₂ n₁ n₂ : ℂ → ℂ} {k₁ k₂ k₃ k₄ : ℝ} (hm₁ : IsBeltramiCoeff m₁ univ k₁)
    (hm₂ : IsBeltramiCoeff m₂ univ k₂) (hn₁ : IsBeltramiCoeff n₁ univ k₃) (hn₂ : IsBeltramiCoeff n₂ univ k₄)
    {Q₀ : (ℂ × ℂ) × (ℂ × ℂ)} {k₀ : ℝ} (hk₀ : k₀ < 1)
    (h₀ : IsBeltramiCoeff (fun u => Q₀.1.1 * m₁ u + Q₀.1.2 * m₂ u + Q₀.2.1 * n₁ u + Q₀.2.2 * n₂ u) univ k₀) :
    ∃ δ > 0, ∃ k : ℝ, 0 ≤ k ∧ k < 1 ∧ ∀ Q : (ℂ × ℂ) × (ℂ × ℂ), dist Q Q₀ < δ →
      IsBeltramiCoeff (fun u => Q.1.1 * m₁ u + Q.1.2 * m₂ u + Q.2.1 * n₁ u + Q.2.2 * n₂ u) univ k := by
  obtain ⟨h0, hk0, hk1⟩ := wr_coeff_nonneg hk₀ h₀
  obtain ⟨S, hSd⟩ : ∃ S : ℝ, S = |k₁| + |k₂| + |k₃| + |k₄| := ⟨_, rfl⟩
  have hS : 0 ≤ S := by rw [hSd]; positivity
  have hM : 0 < S + 1 := by linarith
  obtain ⟨δ, hδdef⟩ : ∃ δ : ℝ, δ = (1 - max k₀ 0) / (2 * (S + 1)) := ⟨_, rfl⟩
  have hδ : 0 < δ := by rw [hδdef]; exact div_pos (by linarith) (by positivity)
  have hMδ : (S + 1) * δ = (1 - max k₀ 0) / 2 := by
    rw [hδdef]; field_simp
  refine ⟨δ, hδ, max k₀ 0 + S * δ, add_nonneg hk0 (mul_nonneg hS hδ.le), ?_, fun Q hQ => ?_⟩
  · have : S * δ ≤ (S + 1) * δ := mul_le_mul_of_nonneg_right (by linarith) hδ.le
    linarith
  · have hT := r65_coeff_lin4 hm₁ hm₂ hn₁ hn₂ (Q - Q₀)
    rw [← hSd] at hT
    refine ⟨(((hm₁.1.const_mul Q.1.1).add (hm₂.1.const_mul Q.1.2)).add (hn₁.1.const_mul Q.2.1)).add
      (hn₂.1.const_mul Q.2.2), ?_⟩
    filter_upwards [h0.2, hT.2] with u h1 h2
    have he : Q.1.1 * m₁ u + Q.1.2 * m₂ u + Q.2.1 * n₁ u + Q.2.2 * n₂ u =
        (Q₀.1.1 * m₁ u + Q₀.1.2 * m₂ u + Q₀.2.1 * n₁ u + Q₀.2.2 * n₂ u) +
          ((Q - Q₀).1.1 * m₁ u + (Q - Q₀).1.2 * m₂ u + (Q - Q₀).2.1 * n₁ u + (Q - Q₀).2.2 * n₂ u) := by
      simp only [Prod.fst_sub, Prod.snd_sub]; ring
    rw [he]
    have hn : ‖Q - Q₀‖ ≤ δ := by rw [← dist_eq_norm]; exact hQ.le
    calc _ ≤ _ := norm_add_le _ _
      _ ≤ max k₀ 0 + S * δ := add_le_add h1 (h2.trans (mul_le_mul_of_nonneg_left hn hS))

/-- (F1) `[W5]` Joint complex differentiability in `Q` (from `qcv_plane_hasFDerivAt`, `E = (ℂ × ℂ) × (ℂ × ℂ)`). -/
theorem r65_ns4_diffAt {m₁ m₂ n₁ n₂ : ℂ → ℂ} {k₁ k₂ k₃ k₄ : ℝ} (hm₁ : IsBeltramiCoeff m₁ univ k₁)
    (hm₂ : IsBeltramiCoeff m₂ univ k₂) (hn₁ : IsBeltramiCoeff n₁ univ k₃) (hn₂ : IsBeltramiCoeff n₂ univ k₄)
    {Q₀ : (ℂ × ℂ) × (ℂ × ℂ)} {k : ℝ} (hk : k < 1)
    (hQ₀ : IsBeltramiCoeff (fun u => Q₀.1.1 * m₁ u + Q₀.1.2 * m₂ u + Q₀.2.1 * n₁ u + Q₀.2.2 * n₂ u) univ k)
    (z : ℂ) :
    DifferentiableAt ℂ (fun Q : (ℂ × ℂ) × (ℂ × ℂ) =>
      normalizedSolution (fun u => Q.1.1 * m₁ u + Q.1.2 * m₂ u + Q.2.1 * n₁ u + Q.2.2 * n₂ u) z) Q₀ := by
  obtain ⟨h0, hk0, hk1⟩ := wr_coeff_nonneg hk hQ₀
  obtain ⟨f₀, hf₀, -, -⟩ := thm13_7_normalized_existence hk0 hk1 h0
  obtain ⟨T, hTd⟩ : ∃ T : (ℂ × ℂ) × (ℂ × ℂ) → ℂ → ℂ,
      T = fun v u => v.1.1 * m₁ u + v.1.2 * m₂ u + v.2.1 * n₁ u + v.2.2 * n₂ u := ⟨_, rfl⟩
  have hT : ∀ v, IsBeltramiCoeff (T v) univ ((|k₁| + |k₂| + |k₃| + |k₄|) * ‖v‖) := by
    intro v; rw [hTd]; exact r65_coeff_lin4 hm₁ hm₂ hn₁ hn₂ v
  have hTlin : ∀ (c : ℂ) (v₁ v₂ : (ℂ × ℂ) × (ℂ × ℂ)),
      T (c • v₁ + v₂) =ᵐ[volume] fun u => c * T v₁ u + T v₂ u := by
    intro c v₁ v₂
    refine Eventually.of_forall fun u => ?_
    rw [hTd]
    simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    ring
  obtain ⟨L, -, hL⟩ := QCV.qcv_plane_hasFDerivAt hk0 hk1 h0 hf₀ T (by positivity) hT hTlin z
  have hL' : HasFDerivAt (fun v => normalizedSolution (fun u => Q₀.1.1 * m₁ u + Q₀.1.2 * m₂ u +
      Q₀.2.1 * n₁ u + Q₀.2.2 * n₂ u + T v u) z) L (Q₀ - Q₀) := by
    rw [sub_self]; exact hL
  have hs : HasFDerivAt (fun Q : (ℂ × ℂ) × (ℂ × ℂ) => Q - Q₀) (ContinuousLinearMap.id ℂ _) Q₀ :=
    (hasFDerivAt_id Q₀).sub_const Q₀
  have heq : (fun Q : (ℂ × ℂ) × (ℂ × ℂ) =>
      normalizedSolution (fun u => Q.1.1 * m₁ u + Q.1.2 * m₂ u + Q.2.1 * n₁ u + Q.2.2 * n₂ u) z) =
      (fun v => normalizedSolution (fun u => Q₀.1.1 * m₁ u + Q₀.1.2 * m₂ u +
        Q₀.2.1 * n₁ u + Q₀.2.2 * n₂ u + T v u) z) ∘ fun Q => Q - Q₀ := by
    funext Q
    show normalizedSolution _ z = normalizedSolution _ z
    congr 1
    funext u
    rw [hTd]
    simp only [Prod.fst_sub, Prod.snd_sub]
    ring
  rw [heq]
  exact (HasFDerivAt.comp (f := fun Q : (ℂ × ℂ) × (ℂ × ℂ) => Q - Q₀) Q₀ hL' hs).differentiableAt

/-- Locally uniform convergence along `Qₙ → Q₀ ∈ W` (as `wr_ns2_luc`). -/
theorem r65_ns4_luc {m₁ m₂ n₁ n₂ : ℂ → ℂ} {k₁ k₂ k₃ k₄ : ℝ} (hm₁ : IsBeltramiCoeff m₁ univ k₁)
    (hm₂ : IsBeltramiCoeff m₂ univ k₂) (hn₁ : IsBeltramiCoeff n₁ univ k₃) (hn₂ : IsBeltramiCoeff n₂ univ k₄)
    {W : Set ((ℂ × ℂ) × (ℂ × ℂ))}
    (hWk : ∀ Q ∈ W, ∃ k < 1,
      IsBeltramiCoeff (fun u => Q.1.1 * m₁ u + Q.1.2 * m₂ u + Q.2.1 * n₁ u + Q.2.2 * n₂ u) univ k)
    {Q₀ : (ℂ × ℂ) × (ℂ × ℂ)} (hQ₀ : Q₀ ∈ W) {Qs : ℕ → (ℂ × ℂ) × (ℂ × ℂ)} (hlim : Tendsto Qs atTop (𝓝 Q₀)) :
    TendstoLocallyUniformly (fun n => normalizedSolution (fun u => (Qs n).1.1 * m₁ u + (Qs n).1.2 * m₂ u +
      (Qs n).2.1 * n₁ u + (Qs n).2.2 * n₂ u))
      (normalizedSolution (fun u => Q₀.1.1 * m₁ u + Q₀.1.2 * m₂ u + Q₀.2.1 * n₁ u + Q₀.2.2 * n₂ u)) atTop := by
  obtain ⟨k₀, hk₀, h₀⟩ := hWk _ hQ₀
  obtain ⟨δ, hδ, k, hk0, hk1, hQ⟩ := r65_loc_unif4 hm₁ hm₂ hn₁ hn₂ hk₀ h₀
  have hpt : ∀ z, Tendsto (fun n => normalizedSolution (fun u => (Qs n).1.1 * m₁ u + (Qs n).1.2 * m₂ u +
      (Qs n).2.1 * n₁ u + (Qs n).2.2 * n₂ u) z) atTop
      (𝓝 (normalizedSolution (fun u => Q₀.1.1 * m₁ u + Q₀.1.2 * m₂ u + Q₀.2.1 * n₁ u + Q₀.2.2 * n₂ u) z)) :=
    fun z => (r65_ns4_diffAt hm₁ hm₂ hn₁ hn₂ hk₀ h₀ z).continuousAt.tendsto.comp hlim
  have hqc : ∀ᶠ n in atTop, IsKQCNormalizedPlane
      (normalizedSolution (fun u => (Qs n).1.1 * m₁ u + (Qs n).1.2 * m₂ u + (Qs n).2.1 * n₁ u +
        (Qs n).2.2 * n₂ u)) ((1 + k) / (1 - k)) := by
    filter_upwards [hlim.eventually (ball_mem_nhds Q₀ hδ)] with n hn
    exact wr_ns_qc hk0 hk1 (hQ _ hn) le_rfl
  rw [tendstoLocallyUniformly_iff_forall_isCompact]
  intro S hS
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  by_contra hcon
  rw [not_eventually] at hcon
  obtain ⟨N, hN⟩ := eventually_atTop.1 hqc
  obtain ⟨φ, hφ, hbad⟩ := extraction_of_frequently_atTop (hcon.and_eventually (eventually_ge_atTop N))
  have hK' : ∀ n, IsKQCNormalizedPlane
      (normalizedSolution (fun u => (Qs (φ n)).1.1 * m₁ u + (Qs (φ n)).1.2 * m₂ u + (Qs (φ n)).2.1 * n₁ u +
        (Qs (φ n)).2.2 * n₂ u)) ((1 + k) / (1 - k)) :=
    fun n => hN _ (hbad n).2
  obtain ⟨ψ, hψ, G, hG⟩ := UniversalTeichmuller.ut2_nf_extract hK'
  have hGeq : G = normalizedSolution (fun u => Q₀.1.1 * m₁ u + Q₀.1.2 * m₂ u + Q₀.2.1 * n₁ u +
      Q₀.2.2 * n₂ u) := by
    funext w
    exact tendsto_nhds_unique
      ((tendstoLocallyUniformly_iff_forall_isCompact.1 hG {w} isCompact_singleton).tendsto_at (mem_singleton w))
      ((hpt w).comp (hφ.tendsto_atTop.comp hψ.tendsto_atTop))
  rw [hGeq] at hG
  have hU := Metric.tendstoUniformlyOn_iff.1 (tendstoLocallyUniformly_iff_forall_isCompact.1 hG S hS) ε hε
  obtain ⟨n, hn⟩ := hU.exists
  exact (hbad (ψ n)).1 hn

/-- (F2) `[W5]` Joint continuity in `(Q, z)` (as `wr_ns2_cont`). -/
theorem r65_ns4_cont {m₁ m₂ n₁ n₂ : ℂ → ℂ} {k₁ k₂ k₃ k₄ : ℝ} (hm₁ : IsBeltramiCoeff m₁ univ k₁)
    (hm₂ : IsBeltramiCoeff m₂ univ k₂) (hn₁ : IsBeltramiCoeff n₁ univ k₃) (hn₂ : IsBeltramiCoeff n₂ univ k₄)
    {W : Set ((ℂ × ℂ) × (ℂ × ℂ))}
    (hWk : ∀ Q ∈ W, ∃ k < 1,
      IsBeltramiCoeff (fun u => Q.1.1 * m₁ u + Q.1.2 * m₂ u + Q.2.1 * n₁ u + Q.2.2 * n₂ u) univ k) :
    ContinuousOn (fun q : ((ℂ × ℂ) × (ℂ × ℂ)) × ℂ =>
      normalizedSolution (fun u => q.1.1.1 * m₁ u + q.1.1.2 * m₂ u + q.1.2.1 * n₁ u + q.1.2.2 * n₂ u) q.2)
      (W ×ˢ univ) := by
  rintro ⟨Q₀, z₀⟩ ⟨hQ₀, -⟩
  show Tendsto _ (𝓝[W ×ˢ univ] (Q₀, z₀)) _
  rw [Filter.tendsto_iff_seq_tendsto]
  intro x hx
  have hx' := tendsto_nhdsWithin_iff.mp hx
  have h1 : Tendsto (fun n => (x n).1) atTop (𝓝 Q₀) := (continuous_fst.tendsto _).comp hx'.1
  have h2 : Tendsto (fun n => (x n).2) atTop (𝓝 z₀) := (continuous_snd.tendsto _).comp hx'.1
  have hL := r65_ns4_luc hm₁ hm₂ hn₁ hn₂ hWk hQ₀ h1
  obtain ⟨k₀, hk₀, h₀⟩ := hWk _ hQ₀
  obtain ⟨h0, hk0, hk1⟩ := wr_coeff_nonneg hk₀ h₀
  have hc : Continuous (normalizedSolution (fun u => Q₀.1.1 * m₁ u + Q₀.1.2 * m₂ u + Q₀.2.1 * n₁ u +
      Q₀.2.2 * n₂ u)) :=
    continuousOn_univ.1 (wr_ns_qc hk0 hk1 h0 le_rfl).1.2.2.1.1
  exact hL.tendsto_comp hc.continuousAt h2

/-- (F3) `[W5]` Joint continuity of the inverse maps (as `wr_ns2_inv_cont`). -/
theorem r65_ns4_inv_cont {m₁ m₂ n₁ n₂ : ℂ → ℂ} {k₁ k₂ k₃ k₄ : ℝ} (hm₁ : IsBeltramiCoeff m₁ univ k₁)
    (hm₂ : IsBeltramiCoeff m₂ univ k₂) (hn₁ : IsBeltramiCoeff n₁ univ k₃) (hn₂ : IsBeltramiCoeff n₂ univ k₄)
    {W : Set ((ℂ × ℂ) × (ℂ × ℂ))}
    (hWk : ∀ Q ∈ W, ∃ k < 1,
      IsBeltramiCoeff (fun u => Q.1.1 * m₁ u + Q.1.2 * m₂ u + Q.2.1 * n₁ u + Q.2.2 * n₂ u) univ k) :
    ContinuousOn (fun q : ((ℂ × ℂ) × (ℂ × ℂ)) × ℂ => Function.invFun
      (normalizedSolution fun u => q.1.1.1 * m₁ u + q.1.1.2 * m₂ u + q.1.2.1 * n₁ u + q.1.2.2 * n₂ u) q.2)
      (W ×ˢ univ) := by
  rintro ⟨Q₀, z₀⟩ ⟨hQ₀, -⟩
  show Tendsto _ (𝓝[W ×ˢ univ] (Q₀, z₀)) _
  rw [Filter.tendsto_iff_seq_tendsto]
  intro x hx
  have hx' := tendsto_nhdsWithin_iff.mp hx
  have h1 : Tendsto (fun n => (x n).1) atTop (𝓝 Q₀) := (continuous_fst.tendsto _).comp hx'.1
  have h2 : Tendsto (fun n => (x n).2) atTop (𝓝 z₀) := (continuous_snd.tendsto _).comp hx'.1
  have hL := r65_ns4_luc hm₁ hm₂ hn₁ hn₂ hWk hQ₀ h1
  obtain ⟨N, hN⟩ := eventually_atTop.1 hx'.2
  have he : ∀ n, ∃ e : ℂ ≃ₜ ℂ, ⇑e = normalizedSolution (fun u => (x (n + N)).1.1.1 * m₁ u +
      (x (n + N)).1.1.2 * m₂ u + (x (n + N)).1.2.1 * n₁ u + (x (n + N)).1.2.2 * n₂ u) := by
    intro n
    obtain ⟨k, hk, hQ⟩ := hWk _ (hN (n + N) (by omega)).1
    obtain ⟨h0, hk0, hk1⟩ := wr_coeff_nonneg hk hQ
    have h := wr_ns_qc hk0 hk1 h0 le_rfl
    exact t1_homeomorph h.1 h.2.1
  choose E hE using he
  obtain ⟨k₀, hk₀, h₀⟩ := hWk _ hQ₀
  obtain ⟨h0, hk0, hk1⟩ := wr_coeff_nonneg hk₀ h₀
  have hW0 := wr_ns_qc hk0 hk1 h0 le_rfl
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
  have hinv := kn6_inverse_locallyUniform hLE
  have h2' : Tendsto (fun n => (x (n + N)).2) atTop (𝓝 z₀) := (tendsto_add_atTop_iff_nat N).2 h2
  have hlim := hinv.tendsto_comp e₀.symm.continuous.continuousAt h2'
  have hval : Function.invFun (normalizedSolution fun u => Q₀.1.1 * m₁ u + Q₀.1.2 * m₂ u + Q₀.2.1 * n₁ u +
      Q₀.2.2 * n₂ u) z₀ = e₀.symm z₀ := wr_invFun_eq he₀ z₀
  show Tendsto (fun n => Function.invFun (normalizedSolution fun u => (x n).1.1.1 * m₁ u + (x n).1.1.2 * m₂ u +
    (x n).1.2.1 * n₁ u + (x n).1.2.2 * n₂ u) (x n).2) atTop (𝓝 (Function.invFun (normalizedSolution fun u =>
      Q₀.1.1 * m₁ u + Q₀.1.2 * m₂ u + Q₀.2.1 * n₁ u + Q₀.2.2 * n₂ u) z₀))
  rw [hval, ← tendsto_add_atTop_iff_nat N]
  refine hlim.congr fun n => ?_
  show (E n).symm (x (n + N)).2 = _
  rw [wr_invFun_eq (hE n)]

/-- (D1) in four parameters: local Cauchy representation through the comparison family `G_Q`, the installed
two-parameter A3 family of `(χm₁, χn₁)` at `(Q.1.1, Q.2.1)` (as `wr_local_cauchy`). -/
theorem r65_local_cauchy4 {m₁ m₂ n₁ n₂ : ℂ → ℂ} {k₁ k₂ k₃ k₄ : ℝ} (hm₁ : IsBeltramiCoeff m₁ univ k₁)
    (hm₂ : IsBeltramiCoeff m₂ univ k₂) (hn₁ : IsBeltramiCoeff n₁ univ k₃) (hn₂ : IsBeltramiCoeff n₂ univ k₄)
    {Ω : Set ℂ} (hΩ : IsOpen Ω)
    (hs₁ : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) m₁ Ω) (hs₂ : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) n₁ Ω)
    (h0 : ∀ u ∈ Ω, m₂ u = 0 ∧ n₂ u = 0)
    {W : Set ((ℂ × ℂ) × (ℂ × ℂ))} (hW : IsOpen W)
    (hWk : ∀ Q ∈ W, ∃ k < 1,
      IsBeltramiCoeff (fun u => Q.1.1 * m₁ u + Q.1.2 * m₂ u + Q.2.1 * n₁ u + Q.2.2 * n₂ u) univ k)
    {Q₀ : (ℂ × ℂ) × (ℂ × ℂ)} (hQ₀ : Q₀ ∈ W) {z₀ : ℂ} (hz₀ : z₀ ∈ Ω) :
    ∃ V ∈ 𝓝 Q₀, V ⊆ W ∧ ∃ ρ > 0, ∃ G : (ℂ × ℂ) × (ℂ × ℂ) → ℂ → ℂ, ∃ c : ℂ, ∃ R > 0,
      (∀ Q ∈ V, ContDiff ℝ 3 (G Q)) ∧
      (∀ j ≤ 3, ContinuousOn (fun q : ((ℂ × ℂ) × (ℂ × ℂ)) × ℂ => iteratedFDeriv ℝ j (G q.1) q.2) (V ×ˢ univ)) ∧
      ContinuousOn (fun q : ((ℂ × ℂ) × (ℂ × ℂ)) × ℂ =>
        normalizedSolution (fun u => q.1.1.1 * m₁ u + q.1.1.2 * m₂ u + q.1.2.1 * n₁ u + q.1.2.2 * n₂ u)
          (Function.invFun (G q.1) q.2)) (V ×ˢ sphere c R) ∧
      ∀ Q ∈ V, ∀ z ∈ ball z₀ ρ, G Q z ∈ ball c (R / 2) ∧
        normalizedSolution (fun u => Q.1.1 * m₁ u + Q.1.2 * m₂ u + Q.2.1 * n₁ u + Q.2.2 * n₂ u) z =
          (2 * π * I)⁻¹ * ∮ ξ in C(c, R),
            normalizedSolution (fun u => Q.1.1 * m₁ u + Q.1.2 * m₂ u + Q.2.1 * n₁ u + Q.2.2 * n₂ u)
              (Function.invFun (G Q) ξ) / (ξ - G Q z) := by
  -- the cutoff
  obtain ⟨r, hr, hrΩ⟩ : ∃ r > 0, closedBall z₀ (3 * r) ⊆ Ω := by
    obtain ⟨ε, hε, hsub⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hΩ.mem_nhds hz₀)
    refine ⟨ε / 3, by positivity, ?_⟩
    rwa [mul_div_cancel₀ _ (by norm_num : (3 : ℝ) ≠ 0)]
  let χ : ContDiffBump z₀ := ⟨2 * r, 3 * r, by positivity, by linarith⟩
  have hχs : tsupport χ ⊆ Ω := by
    rw [χ.tsupport_eq]
    exact hrΩ
  have hχ1 : ∀ z ∈ ball z₀ (2 * r), (χ z : ℂ) = 1 := by
    intro z hz
    have h : χ z = 1 := χ.one_of_mem_closedBall (ball_subset_closedBall hz)
    rw [h, Complex.ofReal_one]
  have hχn : ∀ z, ‖(χ z : ℂ)‖ ≤ 1 := by
    intro z
    rw [Complex.norm_real, Real.norm_of_nonneg χ.nonneg]
    exact χ.le_one
  have hχ0 : ∀ z, z ∉ Ω → (χ z : ℂ) = 0 := by
    intro z hz
    rw [image_eq_zero_of_notMem_tsupport fun h => hz (hχs h), Complex.ofReal_zero]
  obtain ⟨ν₁, hν₁d⟩ : ∃ ν₁ : ℂ → ℂ, ν₁ = fun z => (χ z : ℂ) * m₁ z := ⟨_, rfl⟩
  obtain ⟨ν₂, hν₂d⟩ : ∃ ν₂ : ℂ → ℂ, ν₂ = fun z => (χ z : ℂ) * n₁ z := ⟨_, rfl⟩
  have hν₁ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ν₁ := hν₁d ▸ wr_cutoff_mul_contDiff hΩ hs₁ χ.contDiff hχs
  have hν₂ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ν₂ := hν₂d ▸ wr_cutoff_mul_contDiff hΩ hs₂ χ.contDiff hχs
  have hcs : HasCompactSupport (fun z => (χ z : ℂ)) := χ.hasCompactSupport.comp_left Complex.ofReal_zero
  have hc₁ : HasCompactSupport ν₁ := hν₁d ▸ hcs.mul_right
  have hc₂ : HasCompactSupport ν₂ := hν₂d ▸ hcs.mul_right
  -- on `Ω` the coefficient has only the two terms `m₁, n₁`; off `Ω` the cutoff vanishes
  have hνQ : ∀ (Q : (ℂ × ℂ) × (ℂ × ℂ)) z, Q.1.1 * ν₁ z + Q.2.1 * ν₂ z =
      (χ z : ℂ) * (Q.1.1 * m₁ z + Q.1.2 * m₂ z + Q.2.1 * n₁ z + Q.2.2 * n₂ z) := by
    intro Q z
    rw [hν₁d, hν₂d]
    by_cases hz : z ∈ Ω
    · obtain ⟨e₁, e₂⟩ := h0 z hz
      simp only [e₁, e₂, mul_zero, add_zero]
      ring
    · simp only [hχ0 z hz, zero_mul, mul_zero, add_zero]
  -- the projection `π Q = (Q.1.1, Q.2.1)` and the open parameter set `W₂ = π '' W`
  obtain ⟨π₂, hπd⟩ : ∃ π₂ : (ℂ × ℂ) × (ℂ × ℂ) → ℂ × ℂ, π₂ = fun Q => (Q.1.1, Q.2.1) := ⟨_, rfl⟩
  have hπc : Continuous π₂ := by rw [hπd]; fun_prop
  have hπo : IsOpenMap π₂ := by
    rw [show π₂ = Prod.map Prod.fst Prod.fst from by rw [hπd]; rfl]
    exact isOpenMap_fst.prodMap isOpenMap_fst
  obtain ⟨W₂, hW₂d⟩ : ∃ W₂ : Set (ℂ × ℂ), W₂ = π₂ '' W := ⟨_, rfl⟩
  have hW₂ : IsOpen W₂ := by rw [hW₂d]; exact hπo _ hW
  have hπW : ∀ Q ∈ W, π₂ Q ∈ W₂ := fun Q hQ => by rw [hW₂d]; exact ⟨Q, hQ, rfl⟩
  have hπ1 : ∀ Q, (π₂ Q).1 = Q.1.1 := fun Q => by rw [hπd]
  have hπ2 : ∀ Q, (π₂ Q).2 = Q.2.1 := fun Q => by rw [hπd]
  -- the comparison coefficients are bounded everywhere
  have hνk : ∀ P ∈ W₂, ∃ k < 1, ∀ z, ‖P.1 * ν₁ z + P.2 * ν₂ z‖ ≤ k := by
    intro P hP
    rw [hW₂d] at hP
    obtain ⟨Q, hQ, rfl⟩ := hP
    obtain ⟨k, hk, hb⟩ := hWk Q hQ
    obtain ⟨hb', hk0, hk1⟩ := wr_coeff_nonneg hk hb
    refine ⟨max k 0, hk1, fun z => ?_⟩
    rw [hπ1, hπ2, hνQ, norm_mul]
    by_cases hz : z ∈ Ω
    · have hc2 : ContinuousOn (fun u => Q.1.1 * m₁ u + Q.2.1 * n₁ u) Ω :=
        (continuousOn_const.mul hs₁.continuousOn).add (continuousOn_const.mul hs₂.continuousOn)
      have hcont : ContinuousOn (fun u => Q.1.1 * m₁ u + Q.1.2 * m₂ u + Q.2.1 * n₁ u + Q.2.2 * n₂ u) Ω :=
        hc2.congr (fun u hu => by
          obtain ⟨e₁, e₂⟩ := h0 u hu
          simp only [e₁, e₂, mul_zero, add_zero])
      have hae : ∀ᵐ u, ‖Q.1.1 * m₁ u + Q.1.2 * m₂ u + Q.2.1 * n₁ u + Q.2.2 * n₂ u‖ ≤ max k 0 := by
        simpa only [Measure.restrict_univ] using hb'.2
      exact (mul_le_of_le_one_left (norm_nonneg _) (hχn z)).trans (wr_ae_bound_on hΩ hcont hae z hz)
    · rw [hχ0 z hz, norm_zero, zero_mul]
      exact hk0
  have hBν : ∀ P ∈ W₂, ∃ k < 1, IsBeltramiCoeff (fun u => P.1 * ν₁ u + P.2 * ν₂ u) univ k := by
    intro P hP
    obtain ⟨k, hk, hb⟩ := hνk P hP
    exact ⟨k, hk, ((continuous_const.mul hν₁.continuous).add
      (continuous_const.mul hν₂.continuous)).aestronglyMeasurable, ae_of_all _ hb⟩
  have hBν₁ : IsBeltramiCoeff ν₁ univ k₁ := by
    refine ⟨hν₁.continuous.aestronglyMeasurable, hm₁.2.mono fun z hz => ?_⟩
    rw [hν₁d]
    show ‖(χ z : ℂ) * m₁ z‖ ≤ k₁
    rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) (hχn z)).trans hz
  have hBν₂ : IsBeltramiCoeff ν₂ univ k₃ := by
    refine ⟨hν₂.continuous.aestronglyMeasurable, hn₁.2.mono fun z hz => ?_⟩
    rw [hν₂d]
    show ‖(χ z : ℂ) * n₁ z‖ ≤ k₃
    rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) (hχn z)).trans hz
  -- the two-parameter comparison family and its properties
  obtain ⟨hGsm, hGcont⟩ := wr_smooth_family hν₁ hc₁ hν₂ hc₂ hW₂ hνk
  have hGc := wr_ns2_cont hBν₁ hBν₂ hW₂ hBν
  have hGi := wr_ns2_inv_cont hBν₁ hBν₂ hW₂ hBν
  have hMc := r65_ns4_cont hm₁ hm₂ hn₁ hn₂ hWk
  have hhom : ∀ P ∈ W₂, ∃ e : ℂ ≃ₜ ℂ, ⇑e = normalizedSolution (fun u => P.1 * ν₁ u + P.2 * ν₂ u) := by
    intro P hP
    obtain ⟨k, hk, hP'⟩ := hBν P hP
    obtain ⟨h0', hk0, hk1⟩ := wr_coeff_nonneg hk hP'
    have h := wr_ns_qc hk0 hk1 h0' le_rfl
    exact t1_homeomorph h.1 h.2.1
  have hleft : ∀ P ∈ W₂, ∀ z, Function.invFun (normalizedSolution (fun u => P.1 * ν₁ u + P.2 * ν₂ u))
      (normalizedSolution (fun u => P.1 * ν₁ u + P.2 * ν₂ u) z) = z := by
    intro P hP z
    obtain ⟨e, he⟩ := hhom P hP
    rw [wr_invFun_eq he, ← he]
    exact e.symm_apply_apply z
  have hP₀ := hπW Q₀ hQ₀
  have hWn : W₂ ×ˢ (univ : Set ℂ) ∈ 𝓝 (π₂ Q₀, z₀) := prod_mem_nhds (hW₂.mem_nhds hP₀) Filter.univ_mem
  -- uniform geometry: the inverse maps a fixed closed disc around `c` into `B(z₀, 2r)`
  obtain ⟨c, hcd⟩ : ∃ c : ℂ, c = normalizedSolution (fun u => (π₂ Q₀).1 * ν₁ u + (π₂ Q₀).2 * ν₂ u) z₀ :=
    ⟨_, rfl⟩
  have hWc : W₂ ×ˢ (univ : Set ℂ) ∈ 𝓝 (π₂ Q₀, c) := prod_mem_nhds (hW₂.mem_nhds hP₀) Filter.univ_mem
  have hev1 : ∀ᶠ q in 𝓝 (π₂ Q₀, c), Function.invFun (normalizedSolution
      (fun u => q.1.1 * ν₁ u + q.1.2 * ν₂ u)) q.2 ∈ ball z₀ (2 * r) := by
    refine (hGi.continuousAt hWc).eventually (isOpen_ball.mem_nhds ?_)
    show Function.invFun (normalizedSolution (fun u => (π₂ Q₀).1 * ν₁ u + (π₂ Q₀).2 * ν₂ u)) c ∈ ball z₀ (2 * r)
    rw [hcd, hleft _ hP₀ z₀]
    exact mem_ball_self (by positivity)
  obtain ⟨u₁, hu₁, v₁, hv₁, huv₁⟩ := mem_nhds_prod_iff.mp hev1
  obtain ⟨R₀, hR₀, hR₀v⟩ := Metric.mem_nhds_iff.mp hv₁
  have hR : 0 < R₀ / 2 := by positivity
  have hRsub : closedBall c (R₀ / 2) ⊆ v₁ :=
    (closedBall_subset_ball (by linarith)).trans hR₀v
  have hev2 : ∀ᶠ q in 𝓝 (π₂ Q₀, z₀), normalizedSolution
      (fun u => q.1.1 * ν₁ u + q.1.2 * ν₂ u) q.2 ∈ ball c (R₀ / 2 / 2) := by
    refine (hGc.continuousAt hWn).eventually (isOpen_ball.mem_nhds ?_)
    show normalizedSolution (fun u => (π₂ Q₀).1 * ν₁ u + (π₂ Q₀).2 * ν₂ u) z₀ ∈ ball c (R₀ / 2 / 2)
    rw [← hcd]
    exact mem_ball_self (by positivity)
  obtain ⟨u₂, hu₂, v₂, hv₂, huv₂⟩ := mem_nhds_prod_iff.mp hev2
  obtain ⟨ρ₀, hρ₀, hρ₀v⟩ := Metric.mem_nhds_iff.mp hv₂
  have hpre : π₂ ⁻¹' u₁ ∩ π₂ ⁻¹' u₂ ∩ W ∈ 𝓝 Q₀ :=
    inter_mem (inter_mem (hπc.continuousAt.preimage_mem_nhds hu₁) (hπc.continuousAt.preimage_mem_nhds hu₂))
      (hW.mem_nhds hQ₀)
  have hf2 : Continuous fun q : ((ℂ × ℂ) × (ℂ × ℂ)) × ℂ => (π₂ q.1, q.2) :=
    (hπc.comp continuous_fst).prodMk continuous_snd
  have hmaps2 : ∀ q ∈ (π₂ ⁻¹' u₁ ∩ π₂ ⁻¹' u₂ ∩ W) ×ˢ (univ : Set ℂ), (π₂ q.1, q.2) ∈ W₂ ×ˢ (univ : Set ℂ) :=
    fun q hq => ⟨hπW _ hq.1.2, mem_univ _⟩
  refine ⟨π₂ ⁻¹' u₁ ∩ π₂ ⁻¹' u₂ ∩ W, hpre, inter_subset_right,
    min ρ₀ (2 * r), lt_min hρ₀ (by positivity),
    fun Q => normalizedSolution (fun u => (π₂ Q).1 * ν₁ u + (π₂ Q).2 * ν₂ u), c, R₀ / 2, hR, ?_, ?_, ?_, ?_⟩
  · intro Q hQ
    exact hGsm _ (hπW Q hQ.2)
  · intro j hj
    exact (hGcont j hj).comp (f := fun q : ((ℂ × ℂ) × (ℂ × ℂ)) × ℂ => (π₂ q.1, q.2)) hf2.continuousOn hmaps2
  · have hf : ContinuousOn (fun q : ((ℂ × ℂ) × (ℂ × ℂ)) × ℂ => (q.1, Function.invFun (normalizedSolution
        (fun u => (π₂ q.1).1 * ν₁ u + (π₂ q.1).2 * ν₂ u)) q.2))
        ((π₂ ⁻¹' u₁ ∩ π₂ ⁻¹' u₂ ∩ W) ×ˢ sphere c (R₀ / 2)) :=
      continuousOn_fst.prodMk ((hGi.comp (f := fun q : ((ℂ × ℂ) × (ℂ × ℂ)) × ℂ => (π₂ q.1, q.2)) hf2.continuousOn fun q hq => ⟨hπW _ hq.1.2, mem_univ _⟩))
    exact hMc.comp hf fun q hq => ⟨hq.1.2, mem_univ _⟩
  · intro Q hQ z hz
    have hQW : Q ∈ W := hQ.2
    have hzv₂ : z ∈ v₂ := hρ₀v (ball_subset_ball (min_le_left _ _) hz)
    have hGz := huv₂ (show (π₂ Q, z) ∈ u₂ ×ˢ v₂ from ⟨hQ.1.2, hzv₂⟩)
    simp only [mem_ofPred_eq] at hGz
    refine ⟨hGz, ?_⟩
    have hzD : z ∈ ball z₀ (2 * r) := ball_subset_ball (min_le_right _ _) hz
    obtain ⟨k, hk, hbQ⟩ := hWk Q hQW
    obtain ⟨kν, hkν, hbν⟩ := hBν _ (hπW Q hQW)
    have hEq : EqOn (fun u => (π₂ Q).1 * ν₁ u + (π₂ Q).2 * ν₂ u)
        (fun u => Q.1.1 * m₁ u + Q.1.2 * m₂ u + Q.2.1 * n₁ u + Q.2.2 * n₂ u) (ball z₀ (2 * r)) := by
      intro u hu
      show (π₂ Q).1 * ν₁ u + (π₂ Q).2 * ν₂ u = Q.1.1 * m₁ u + Q.1.2 * m₂ u + Q.2.1 * n₁ u + Q.2.2 * n₂ u
      rw [hπ1, hπ2, hνQ, hχ1 u hu, one_mul]
    have hmemD : ∀ ξ ∈ closedBall c (R₀ / 2),
        Function.invFun (normalizedSolution (fun u => (π₂ Q).1 * ν₁ u + (π₂ Q).2 * ν₂ u)) ξ ∈ ball z₀ (2 * r) :=
      fun ξ hξ => by
        have h := huv₁ (show (π₂ Q, ξ) ∈ u₁ ×ˢ v₁ from ⟨hQ.1.1, hRsub hξ⟩)
        simp only [mem_ofPred_eq] at h
        exact h
    exact wr_d1_cauchy isOpen_ball hk hbQ hkν hbν hEq hR hmemD hzD (ball_subset_ball (by linarith) hGz)

/-- (F4) `[W5]` **`z`-regularity** on an open set `Ω` where `m₁, n₁` are smooth and `m₂ = n₂ = 0`: `C³` in `z`, with
`z`-iterated derivatives jointly continuous in `(Q, z)`. Route: D1/D2b (`wr_local_cauchy`, `wr_ns2_z_regular`) with
the comparison family `G_Q` = the A3 family (`wr_smooth_family`) of `(χm₁, χn₁)` at `(Q.1.1, Q.2.1)`. -/
theorem r65_ns4_z_regular {m₁ m₂ n₁ n₂ : ℂ → ℂ} {k₁ k₂ k₃ k₄ : ℝ} (hm₁ : IsBeltramiCoeff m₁ univ k₁)
    (hm₂ : IsBeltramiCoeff m₂ univ k₂) (hn₁ : IsBeltramiCoeff n₁ univ k₃) (hn₂ : IsBeltramiCoeff n₂ univ k₄)
    {Ω : Set ℂ} (hΩ : IsOpen Ω)
    (hs₁ : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) m₁ Ω) (hs₂ : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) n₁ Ω)
    (h0 : ∀ u ∈ Ω, m₂ u = 0 ∧ n₂ u = 0)
    {W : Set ((ℂ × ℂ) × (ℂ × ℂ))} (hW : IsOpen W)
    (hWk : ∀ Q ∈ W, ∃ k < 1,
      IsBeltramiCoeff (fun u => Q.1.1 * m₁ u + Q.1.2 * m₂ u + Q.2.1 * n₁ u + Q.2.2 * n₂ u) univ k) :
    (∀ Q ∈ W, ContDiffOn ℝ 3
      (normalizedSolution fun u => Q.1.1 * m₁ u + Q.1.2 * m₂ u + Q.2.1 * n₁ u + Q.2.2 * n₂ u) Ω) ∧
      ∀ j ≤ 3, ContinuousOn (fun q : ((ℂ × ℂ) × (ℂ × ℂ)) × ℂ => iteratedFDeriv ℝ j
        (normalizedSolution fun u => q.1.1.1 * m₁ u + q.1.1.2 * m₂ u + q.1.2.1 * n₁ u + q.1.2.2 * n₂ u) q.2)
        (W ×ˢ Ω) := by
  obtain ⟨F, hF⟩ : ∃ F : (ℂ × ℂ) × (ℂ × ℂ) → ℂ → ℂ, F = fun Q => normalizedSolution fun u => Q.1.1 * m₁ u + Q.1.2 * m₂ u + Q.2.1 * n₁ u + Q.2.2 * n₂ u :=
    ⟨_, rfl⟩
  have loc : ∀ P₀ ∈ W, ∀ z₀ ∈ Ω, ∃ r > 0, ∃ ρ > 0, ball z₀ ρ ⊆ Ω ∧
      (∀ P ∈ ball P₀ r, ContDiffOn ℝ 3 (F P) (ball z₀ ρ)) ∧
      ∀ j ≤ 3, ContinuousOn (fun q : ((ℂ × ℂ) × (ℂ × ℂ)) × ℂ => iteratedFDeriv ℝ j (F q.1) q.2)
        (ball P₀ r ×ˢ ball z₀ ρ) := by
    intro P₀ hP₀ z₀ hz₀
    obtain ⟨V, hV, -, ρ, hρ, G, c, R, hR, hG3, hGc, hhc0, hrep0⟩ :=
      r65_local_cauchy4 hm₁ hm₂ hn₁ hn₂ hΩ hs₁ hs₂ h0 hW hWk hP₀ hz₀
    have hhc : ContinuousOn (fun q : ((ℂ × ℂ) × (ℂ × ℂ)) × ℂ => F q.1 (Function.invFun (G q.1) q.2)) (V ×ˢ sphere c R) := by
      rw [hF]; exact hhc0
    have hrep : ∀ P ∈ V, ∀ z ∈ ball z₀ ρ, G P z ∈ ball c (R / 2) ∧
        F P z = (2 * π * I)⁻¹ * ∮ ξ in C(c, R), F P (Function.invFun (G P) ξ) / (ξ - G P z) := by
      rw [hF]; exact hrep0
    obtain ⟨r, hr, hrV⟩ := Metric.mem_nhds_iff.1 hV
    obtain ⟨ρ', hρ', hρ'Ω⟩ := Metric.isOpen_iff.1 hΩ z₀ hz₀
    obtain ⟨ρ₁, hρ₁def⟩ : ∃ ρ₁ : ℝ, ρ₁ = min ρ ρ' := ⟨_, rfl⟩
    have hρ₁ : 0 < ρ₁ := by rw [hρ₁def]; exact lt_min hρ hρ'
    have hρ₁ρ : ball z₀ ρ₁ ⊆ ball z₀ ρ := ball_subset_ball (by rw [hρ₁def]; exact min_le_left _ _)
    have hρ₁Ω : ball z₀ ρ₁ ⊆ Ω := (ball_subset_ball (by rw [hρ₁def]; exact min_le_right _ _)).trans hρ'Ω
    have hballV : ball P₀ r ⊆ V := hrV
    obtain ⟨h, hh⟩ : ∃ h : (ℂ × ℂ) × (ℂ × ℂ) → ℂ → ℂ, h = fun P ξ => (2 * π * I)⁻¹ * F P (Function.invFun (G P) ξ) :=
      ⟨_, rfl⟩
    have hhcont : ContinuousOn (fun p : ((ℂ × ℂ) × (ℂ × ℂ)) × ℂ => h p.1 p.2) (ball P₀ r ×ˢ sphere c R) := by
      rw [hh]; exact (continuousOn_const.mul hhc).mono (prod_mono hballV subset_rfl)
    have hhx : ∀ P ∈ ball P₀ r, ContinuousOn (h P) (sphere c R) :=
      fun P hP => hhcont.comp (continuous_const.prodMk continuous_id).continuousOn (fun y hy => ⟨hP, hy⟩)
    have hHcont := wr_param_cauchy_iter_cont hR hhcont
    have hHsm : ∀ P ∈ ball P₀ r, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun ζ => ∮ ξ in C(c, R), (ξ - ζ) ^ (-1 : ℤ) • h P ξ) (ball c R) := fun P hP =>
      ((wr_cauchy_diffOn hR (hhx P hP)).contDiffOn isOpen_ball).restrict_scalars ℝ
    have hmaps : ∀ P ∈ ball P₀ r, ∀ z ∈ ball z₀ ρ₁, G P z ∈ ball c R := fun P hP z hz =>
      ball_subset_ball (by linarith) (hrep P (hballV hP) z (hρ₁ρ hz)).1
    have hrep' : ∀ P ∈ ball P₀ r, ∀ z ∈ ball z₀ ρ₁,
        F P z = (fun ζ => ∮ ξ in C(c, R), (ξ - ζ) ^ (-1 : ℤ) • h P ξ) (G P z) := by
      intro P hP z hz
      rw [(hrep P (hballV hP) z (hρ₁ρ hz)).2, wr_cauchy_form, hh]
    have hGv : ContinuousOn (fun p : ((ℂ × ℂ) × (ℂ × ℂ)) × ℂ => G p.1 p.2) (ball P₀ r ×ˢ ball z₀ ρ₁) := by
      refine (((continuousMultilinearCurryFin0 ℝ ℂ ℂ).continuous.comp_continuousOn
        (hGc 0 (by norm_num))).mono (prod_mono hballV (subset_univ _))).congr ?_
      intro q _
      simp [iteratedFDeriv_zero_eq_comp]
    refine ⟨r, hr, ρ₁, hρ₁, hρ₁Ω, fun P hP => ?_, fun j hj => ?_⟩
    · refine ((hHsm P hP).of_le (by norm_cast)).comp ((hG3 P (hballV hP)).contDiffOn)
        (fun z hz => hmaps P hP z hz) |>.congr ?_
      intro z hz
      exact hrep' P hP z hz
    · have hcomp := wr_comp_iter_cont (S := ball P₀ r) (U := ball z₀ ρ₁) (T := ball c R) (j := j)
        (H := fun P ζ => ∮ ξ in C(c, R), (ξ - ζ) ^ (-1 : ℤ) • h P ξ)
        (G := G) (fun k _ => hHcont k)
        (fun k hk => (hGc k (hk.trans hj)).mono (prod_mono hballV (subset_univ _))) hGv
        (fun p hp => hmaps p.1 hp.1 p.2 hp.2)
      refine hcomp.congr ?_
      intro q hq
      have hqP := hq.1
      have hqz := hq.2
      have hev : F q.1 =ᶠ[𝓝 q.2] (fun ζ => ∮ ξ in C(c, R), (ξ - ζ) ^ (-1 : ℤ) • h q.1 ξ) ∘ G q.1 := by
        filter_upwards [isOpen_ball.mem_nhds hqz] with z hz
        exact hrep' q.1 hqP z hz
      have hHa : ContDiffAt ℝ 3 (fun ζ => ∮ ξ in C(c, R), (ξ - ζ) ^ (-1 : ℤ) • h q.1 ξ) (G q.1 q.2) :=
        ((hHsm q.1 hqP).of_le (by norm_cast)).contDiffAt (isOpen_ball.mem_nhds (hmaps q.1 hqP q.2 hqz))
      have hGa : ContDiffAt ℝ 3 (G q.1) q.2 := (hG3 q.1 (hballV hqP)).contDiffAt
      show iteratedFDeriv ℝ j (F q.1) q.2 = _
      rw [(hev.iteratedFDeriv ℝ j).self_of_nhds, iteratedFDeriv_comp hHa hGa (by exact_mod_cast hj)]
      rfl
  refine ⟨fun P hP => ?_, fun j hj => ?_⟩
  · have key : ContDiffOn ℝ 3 (F P) Ω := by
      apply contDiffOn_of_locally_contDiffOn
      intro z hz
      obtain ⟨r, hr, ρ, hρ, -, hcd, -⟩ := loc P hP z hz
      exact ⟨ball z ρ, isOpen_ball, mem_ball_self hρ, (hcd P (mem_ball_self hr)).mono inter_subset_right⟩
    rw [hF] at key
    exact key
  · have key : ContinuousOn (fun q : ((ℂ × ℂ) × (ℂ × ℂ)) × ℂ => iteratedFDeriv ℝ j (F q.1) q.2) (W ×ˢ Ω) := by
      intro q hq
      obtain ⟨r, hr, ρ, hρ, -, -, hc⟩ := loc q.1 hq.1 q.2 hq.2
      have hn : ball q.1 r ×ˢ ball q.2 ρ ∈ 𝓝 q :=
        (isOpen_ball.prod isOpen_ball).mem_nhds ⟨mem_ball_self hr, mem_ball_self hρ⟩
      exact ((hc j hj).continuousAt hn).continuousWithinAt
    rw [hF] at key
    exact key

/-- Four nested interval integrals over `[0, 2π]` as one integral against the product of the restricted measures. -/
theorem r65_int4 {Φ : (ℝ × ℝ) × (ℝ × ℝ) → ℂ} (hΦ : Continuous Φ) {C : ℝ} (hC : ∀ x, ‖Φ x‖ ≤ C) :
    ∫ x, Φ x ∂(((volume.restrict (Ioc (0 : ℝ) (2 * π))).prod (volume.restrict (Ioc (0 : ℝ) (2 * π)))).prod
      ((volume.restrict (Ioc (0 : ℝ) (2 * π))).prod (volume.restrict (Ioc (0 : ℝ) (2 * π))))) =
    ∫ θ in (0 : ℝ)..2 * π, ∫ η in (0 : ℝ)..2 * π, ∫ θ' in (0 : ℝ)..2 * π, ∫ η' in (0 : ℝ)..2 * π,
      Φ ((θ, η), (θ', η')) := by
  have h2π : (0 : ℝ) ≤ 2 * π := by positivity
  simp only [intervalIntegral.integral_of_le h2π]
  obtain ⟨μI, hμI⟩ : ∃ μI : Measure ℝ, μI = volume.restrict (Ioc (0 : ℝ) (2 * π)) := ⟨_, rfl⟩
  rw [← hμI]
  have : IsFiniteMeasure μI := by
    rw [hμI]
    exact isFiniteMeasure_restrict.mpr measure_Ioc_lt_top.ne
  have hint : Integrable Φ ((μI.prod μI).prod (μI.prod μI)) :=
    Integrable.of_bound hΦ.aestronglyMeasurable C (Eventually.of_forall hC)
  rw [integral_prod _ hint, integral_prod _ hint.integral_prod_left]
  refine integral_congr_ae (Eventually.of_forall fun θ => ?_)
  refine integral_congr_ae (Eventually.of_forall fun η => ?_)
  have hc : Continuous fun x : ℝ × ℝ => Φ ((θ, η), x) := hΦ.comp (continuous_const.prodMk continuous_id)
  exact integral_prod _ (Integrable.of_bound hc.aestronglyMeasurable C (Eventually.of_forall fun x => hC _))

/-- **Cauchy formula on a 4-polydisc**, by the bidisc formula `wr_cauchy_bidisc` applied twice. -/
theorem r65_cauchy4 {f : (ℂ × ℂ) × (ℂ × ℂ) → ℂ} {c : (ℂ × ℂ) × (ℂ × ℂ)} {r : ℝ} (hr : 0 < r)
    (hcont : ContinuousOn f ((closedBall c.1.1 r ×ˢ closedBall c.1.2 r) ×ˢ (closedBall c.2.1 r ×ˢ closedBall c.2.2 r)))
    (hd : ∀ Q ∈ (closedBall c.1.1 r ×ˢ closedBall c.1.2 r) ×ˢ (closedBall c.2.1 r ×ˢ closedBall c.2.2 r),
      DifferentiableAt ℂ f Q)
    {P : (ℂ × ℂ) × (ℂ × ℂ)} (hP : P ∈ (ball c.1.1 r ×ˢ ball c.1.2 r) ×ˢ (ball c.2.1 r ×ˢ ball c.2.2 r)) :
    f P = ((2 * π * I)⁻¹) ^ 4 * ∮ a in C(c.1.1, r), ∮ b in C(c.1.2, r), ∮ a' in C(c.2.1, r), ∮ b' in C(c.2.2, r),
      f ((a, b), (a', b')) / ((a - P.1.1) * (b - P.1.2) * ((a' - P.2.1) * (b' - P.2.2))) := by
  obtain ⟨⟨hP11, hP12⟩, hP21, hP22⟩ := hP
  have hP2 : P.2 ∈ closedBall c.2.1 r ×ˢ closedBall c.2.2 r :=
    ⟨ball_subset_closedBall hP21, ball_subset_closedBall hP22⟩
  have hin : ∀ a ∈ closedBall c.1.1 r, ∀ b ∈ closedBall c.1.2 r, f ((a, b), P.2) = ((2 * π * I)⁻¹) ^ 2 *
      ∮ a' in C(c.2.1, r), ∮ b' in C(c.2.2, r), f ((a, b), (a', b')) / ((a' - P.2.1) * (b' - P.2.2)) := by
    intro a ha b hb
    refine wr_cauchy_bidisc (f := fun Q => f ((a, b), Q)) (c := c.2) hr hr
      (hcont.comp (Continuous.continuousOn (by fun_prop)) fun Q hQ => ⟨⟨ha, hb⟩, hQ⟩)
      (fun b' hb' a' ha' => ?_) (fun a' ha' b' hb' => ?_) ⟨hP21, hP22⟩
    · have h := hd ((a, b), (a', b')) ⟨⟨ha, hb⟩, ball_subset_closedBall ha', hb'⟩
      exact (h.comp a' ((differentiableAt_const (a, b)).prodMk
        (differentiableAt_id.prodMk (differentiableAt_const b')))).differentiableWithinAt
    · have h := hd ((a, b), (a', b')) ⟨⟨ha, hb⟩, ha', ball_subset_closedBall hb'⟩
      exact (h.comp b' ((differentiableAt_const (a, b)).prodMk
        ((differentiableAt_const a').prodMk differentiableAt_id))).differentiableWithinAt
  have hout := wr_cauchy_bidisc (f := fun Q => f (Q, P.2)) (c := c.1) hr hr
    (hcont.comp (Continuous.continuousOn (by fun_prop)) fun Q hQ => ⟨hQ, hP2⟩)
    (fun b hb a ha => ((hd ((a, b), P.2) ⟨⟨ball_subset_closedBall ha, hb⟩, hP2⟩).comp a
      ((differentiableAt_id.prodMk (differentiableAt_const b)).prodMk
        (differentiableAt_const P.2))).differentiableWithinAt)
    (fun a ha b hb => ((hd ((a, b), P.2) ⟨⟨ha, ball_subset_closedBall hb⟩, hP2⟩).comp b
      (((differentiableAt_const a).prodMk differentiableAt_id).prodMk
        (differentiableAt_const P.2))).differentiableWithinAt)
    ⟨hP11, hP12⟩
  have e1 : ∀ a ∈ sphere c.1.1 r, (∮ b in C(c.1.2, r), f ((a, b), P.2) / ((a - P.1.1) * (b - P.1.2))) =
      ((2 * π * I)⁻¹) ^ 2 • ∮ b in C(c.1.2, r), ∮ a' in C(c.2.1, r), ∮ b' in C(c.2.2, r),
        f ((a, b), (a', b')) / ((a - P.1.1) * (b - P.1.2) * ((a' - P.2.1) * (b' - P.2.2))) := by
    intro a ha
    rw [← circleIntegral.integral_smul]
    refine circleIntegral.integral_congr hr.le fun b hb => ?_
    show f ((a, b), P.2) / ((a - P.1.1) * (b - P.1.2)) = ((2 * π * I)⁻¹) ^ 2 • ∮ a' in C(c.2.1, r),
      ∮ b' in C(c.2.2, r), f ((a, b), (a', b')) / ((a - P.1.1) * (b - P.1.2) * ((a' - P.2.1) * (b' - P.2.2)))
    rw [hin a (sphere_subset_closedBall ha) b (sphere_subset_closedBall hb)]
    have e : (fun a' => ∮ b' in C(c.2.2, r),
        f ((a, b), (a', b')) / ((a - P.1.1) * (b - P.1.2) * ((a' - P.2.1) * (b' - P.2.2)))) =
        fun a' => ((a - P.1.1) * (b - P.1.2))⁻¹ • ∮ b' in C(c.2.2, r),
          f ((a, b), (a', b')) / ((a' - P.2.1) * (b' - P.2.2)) := by
      funext a'
      rw [← circleIntegral.integral_smul]
      congr 1
      funext b'
      simp only [smul_eq_mul, div_eq_mul_inv, mul_inv]
      ring
    rw [e, circleIntegral.integral_smul]
    simp only [smul_eq_mul, div_eq_mul_inv, mul_inv]
    ring
  calc f P = ((2 * π * I)⁻¹) ^ 2 * ∮ a in C(c.1.1, r), ∮ b in C(c.1.2, r),
        f ((a, b), P.2) / ((a - P.1.1) * (b - P.1.2)) := hout
    _ = ((2 * π * I)⁻¹) ^ 2 * ∮ a in C(c.1.1, r), ((2 * π * I)⁻¹) ^ 2 • ∮ b in C(c.1.2, r),
        ∮ a' in C(c.2.1, r), ∮ b' in C(c.2.2, r),
          f ((a, b), (a', b')) / ((a - P.1.1) * (b - P.1.2) * ((a' - P.2.1) * (b' - P.2.2))) := by
      rw [circleIntegral.integral_congr hr.le e1]
    _ = _ := by
      rw [circleIntegral.integral_smul, smul_eq_mul]
      ring

/-- A function continuous on a compact set, composed with a continuous map into it, is continuous and bounded. -/
theorem r65_bdd_comp {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {Ψ : X → ℂ} {T : Set X}
    (hT : IsCompact T) (hΨ : ContinuousOn Ψ T) {q : Y → X} (hq : Continuous q) (hqT : ∀ y, q y ∈ T) :
    Continuous (fun y => Ψ (q y)) ∧ ∃ C, ∀ y, ‖Ψ (q y)‖ ≤ C := by
  obtain ⟨C, hC⟩ := hT.exists_bound_of_continuousOn hΨ
  exact ⟨hΨ.comp_continuous hq hqT, C, fun y => hC _ (hqT y)⟩

/-- The four circle integrals of the polydisc Cauchy formula as one integral over `[0, 2π]⁴`. -/
theorem r65_circ4 {f : (ℂ × ℂ) × (ℂ × ℂ) → ℂ} {c : (ℂ × ℂ) × (ℂ × ℂ)} {r : ℝ} {P : (ℂ × ℂ) × (ℂ × ℂ)} {C : ℝ}
    (hΦc : Continuous fun x : (ℝ × ℝ) × (ℝ × ℝ) =>
      ((circleMap c.1.1 r x.1.1 - c.1.1) * I * ((circleMap c.1.2 r x.1.2 - c.1.2) * I) *
        ((circleMap c.2.1 r x.2.1 - c.2.1) * I * ((circleMap c.2.2 r x.2.2 - c.2.2) * I))) *
        ((P.1.1 - circleMap c.1.1 r x.1.1) * (P.1.2 - circleMap c.1.2 r x.1.2) *
          ((P.2.1 - circleMap c.2.1 r x.2.1) * (P.2.2 - circleMap c.2.2 r x.2.2)))⁻¹ *
        f ((circleMap c.1.1 r x.1.1, circleMap c.1.2 r x.1.2), (circleMap c.2.1 r x.2.1, circleMap c.2.2 r x.2.2)))
    (hΦC : ∀ x : (ℝ × ℝ) × (ℝ × ℝ), ‖((circleMap c.1.1 r x.1.1 - c.1.1) * I * ((circleMap c.1.2 r x.1.2 - c.1.2) * I) *
        ((circleMap c.2.1 r x.2.1 - c.2.1) * I * ((circleMap c.2.2 r x.2.2 - c.2.2) * I))) *
        ((P.1.1 - circleMap c.1.1 r x.1.1) * (P.1.2 - circleMap c.1.2 r x.1.2) *
          ((P.2.1 - circleMap c.2.1 r x.2.1) * (P.2.2 - circleMap c.2.2 r x.2.2)))⁻¹ *
        f ((circleMap c.1.1 r x.1.1, circleMap c.1.2 r x.1.2), (circleMap c.2.1 r x.2.1, circleMap c.2.2 r x.2.2))‖ ≤ C) :
    (∮ a in C(c.1.1, r), ∮ b in C(c.1.2, r), ∮ a' in C(c.2.1, r), ∮ b' in C(c.2.2, r),
      f ((a, b), (a', b')) / ((a - P.1.1) * (b - P.1.2) * ((a' - P.2.1) * (b' - P.2.2)))) =
    ∫ x,
      ((circleMap c.1.1 r x.1.1 - c.1.1) * I * ((circleMap c.1.2 r x.1.2 - c.1.2) * I) *
        ((circleMap c.2.1 r x.2.1 - c.2.1) * I * ((circleMap c.2.2 r x.2.2 - c.2.2) * I))) *
        ((P.1.1 - circleMap c.1.1 r x.1.1) * (P.1.2 - circleMap c.1.2 r x.1.2) *
          ((P.2.1 - circleMap c.2.1 r x.2.1) * (P.2.2 - circleMap c.2.2 r x.2.2)))⁻¹ *
        f ((circleMap c.1.1 r x.1.1, circleMap c.1.2 r x.1.2), (circleMap c.2.1 r x.2.1, circleMap c.2.2 r x.2.2))
      ∂(((volume.restrict (Ioc (0 : ℝ) (2 * π))).prod (volume.restrict (Ioc (0 : ℝ) (2 * π)))).prod
        ((volume.restrict (Ioc (0 : ℝ) (2 * π))).prod (volume.restrict (Ioc (0 : ℝ) (2 * π))))) := by
  rw [r65_int4 hΦc hΦC]
  simp only [circleIntegral, deriv_circleMap, smul_eq_mul, ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun θ _ => intervalIntegral.integral_congr fun η _ =>
    intervalIntegral.integral_congr fun θ' _ => intervalIntegral.integral_congr fun η' _ => ?_
  rw [circleMap_sub_center, circleMap_sub_center, circleMap_sub_center, circleMap_sub_center,
    show (P.1.1 - circleMap c.1.1 r θ) * (P.1.2 - circleMap c.1.2 r η) *
        ((P.2.1 - circleMap c.2.1 r θ') * (P.2.2 - circleMap c.2.2 r η')) =
      (circleMap c.1.1 r θ - P.1.1) * (circleMap c.1.2 r η - P.1.2) *
        ((circleMap c.2.1 r θ' - P.2.1) * (circleMap c.2.2 r η' - P.2.2)) by ring]
  ring

/-- The 4-polydisc Cauchy formula as one integral over `[0, 2π]⁴` (for `P` in the half polydisc). -/
theorem r65_cauchy4_int {f : (ℂ × ℂ) × (ℂ × ℂ) → ℂ} {c : (ℂ × ℂ) × (ℂ × ℂ)} {r : ℝ} (hr : 0 < r)
    (hcont : ContinuousOn f ((closedBall c.1.1 r ×ˢ closedBall c.1.2 r) ×ˢ (closedBall c.2.1 r ×ˢ closedBall c.2.2 r)))
    (hd : ∀ Q ∈ (closedBall c.1.1 r ×ˢ closedBall c.1.2 r) ×ˢ (closedBall c.2.1 r ×ˢ closedBall c.2.2 r),
      DifferentiableAt ℂ f Q)
    {P : (ℂ × ℂ) × (ℂ × ℂ)} (hP : P ∈ ball c (r / 2)) :
    f P = ((2 * π * I)⁻¹) ^ 4 * ∫ x, ((circleMap c.1.1 r x.1.1 - c.1.1) * I * ((circleMap c.1.2 r x.1.2 - c.1.2) * I) *
        ((circleMap c.2.1 r x.2.1 - c.2.1) * I * ((circleMap c.2.2 r x.2.2 - c.2.2) * I))) *
        ((P.1.1 - circleMap c.1.1 r x.1.1) * (P.1.2 - circleMap c.1.2 r x.1.2) *
          ((P.2.1 - circleMap c.2.1 r x.2.1) * (P.2.2 - circleMap c.2.2 r x.2.2)))⁻¹ *
        f ((circleMap c.1.1 r x.1.1, circleMap c.1.2 r x.1.2), (circleMap c.2.1 r x.2.1, circleMap c.2.2 r x.2.2))
      ∂(((volume.restrict (Ioc (0 : ℝ) (2 * π))).prod (volume.restrict (Ioc (0 : ℝ) (2 * π)))).prod
        ((volume.restrict (Ioc (0 : ℝ) (2 * π))).prod (volume.restrict (Ioc (0 : ℝ) (2 * π))))) := by
  have hP' := hP
  rw [mem_ball] at hP'
  simp only [Prod.dist_eq, max_lt_iff] at hP'
  obtain ⟨⟨h11, h12⟩, h21, h22⟩ := hP'
  have hPo : P ∈ (ball c.1.1 r ×ˢ ball c.1.2 r) ×ˢ (ball c.2.1 r ×ˢ ball c.2.2 r) :=
    ⟨⟨mem_ball.2 (by linarith), mem_ball.2 (by linarith)⟩, mem_ball.2 (by linarith), mem_ball.2 (by linarith)⟩
  rw [r65_cauchy4 hr hcont hd hPo]
  congr 1
  -- the integrand, as a function on the torus `T`
  have hne : ∀ (w c' q : ℂ), dist w c' < r / 2 → q ∈ sphere c' r → w - q ≠ 0 := by
    intro w c' q hw hq h
    rw [sub_eq_zero] at h
    rw [h, mem_sphere.1 hq] at hw
    linarith
  obtain ⟨T, hTdef⟩ : ∃ T : Set ((ℂ × ℂ) × (ℂ × ℂ)),
      T = (sphere c.1.1 r ×ˢ sphere c.1.2 r) ×ˢ (sphere c.2.1 r ×ˢ sphere c.2.2 r) := ⟨_, rfl⟩
  have hTc : IsCompact T := by
    rw [hTdef]
    exact ((isCompact_sphere _ _).prod (isCompact_sphere _ _)).prod ((isCompact_sphere _ _).prod (isCompact_sphere _ _))
  have hTB : T ⊆ (closedBall c.1.1 r ×ˢ closedBall c.1.2 r) ×ˢ (closedBall c.2.1 r ×ˢ closedBall c.2.2 r) := by
    rw [hTdef]
    exact prod_mono (prod_mono sphere_subset_closedBall sphere_subset_closedBall)
      (prod_mono sphere_subset_closedBall sphere_subset_closedBall)
  have hqT : ∀ x : (ℝ × ℝ) × (ℝ × ℝ), ((circleMap c.1.1 r x.1.1, circleMap c.1.2 r x.1.2),
      (circleMap c.2.1 r x.2.1, circleMap c.2.2 r x.2.2)) ∈ T := fun x => by
    rw [hTdef]
    exact ⟨⟨circleMap_mem_sphere _ hr.le _, circleMap_mem_sphere _ hr.le _⟩,
      circleMap_mem_sphere _ hr.le _, circleMap_mem_sphere _ hr.le _⟩
  have hqc : Continuous fun x : (ℝ × ℝ) × (ℝ × ℝ) => ((circleMap c.1.1 r x.1.1, circleMap c.1.2 r x.1.2),
      (circleMap c.2.1 r x.2.1, circleMap c.2.2 r x.2.2)) :=
    (((continuous_circleMap _ _).comp (continuous_fst.comp continuous_fst)).prodMk
      ((continuous_circleMap _ _).comp (continuous_snd.comp continuous_fst))).prodMk
      (((continuous_circleMap _ _).comp (continuous_fst.comp continuous_snd)).prodMk
        ((continuous_circleMap _ _).comp (continuous_snd.comp continuous_snd)))
  have hΨ : ContinuousOn (fun q : (ℂ × ℂ) × (ℂ × ℂ) =>
      ((q.1.1 - c.1.1) * I * ((q.1.2 - c.1.2) * I) * ((q.2.1 - c.2.1) * I * ((q.2.2 - c.2.2) * I))) *
        ((P.1.1 - q.1.1) * (P.1.2 - q.1.2) * ((P.2.1 - q.2.1) * (P.2.2 - q.2.2)))⁻¹ * f q) T := by
    refine ((Continuous.continuousOn (by fun_prop)).mul
      (ContinuousOn.inv₀ (Continuous.continuousOn (by fun_prop)) fun q hq => ?_)).mul (hcont.mono hTB)
    rw [hTdef] at hq
    exact mul_ne_zero (mul_ne_zero (hne _ _ _ h11 hq.1.1) (hne _ _ _ h12 hq.1.2))
      (mul_ne_zero (hne _ _ _ h21 hq.2.1) (hne _ _ _ h22 hq.2.2))
  obtain ⟨hΦc, C, hΦC⟩ := r65_bdd_comp hTc hΨ hqc hqT
  dsimp only at hΦc hΦC
  exact r65_circ4 hΦc hΦC

/-- The Cauchy-kernel factor `a(q, P) = A(q) · ∏ (P - q)ᵢ⁻¹`, for `q` on the 4-torus and `P` in the half polydisc:
smooth in `P`, with `P`-iterated derivatives jointly continuous (the 4-variable `wr_d2a_kernel`). -/
theorem r65_kernel4 {c : (ℂ × ℂ) × (ℂ × ℂ)} {r : ℝ} (hr : 0 < r) (A : (ℂ × ℂ) × (ℂ × ℂ) → ℂ) (hA : Continuous A)
    (j : ℕ) :
    (∀ q ∈ (sphere c.1.1 r ×ˢ sphere c.1.2 r) ×ˢ (sphere c.2.1 r ×ˢ sphere c.2.2 r), ContDiffOn ℝ j
      (fun P : (ℂ × ℂ) × (ℂ × ℂ) => A q * ((P - q).1.1 * (P - q).1.2 * ((P - q).2.1 * (P - q).2.2))⁻¹)
      (ball c (r / 2))) ∧
    ∀ i ≤ j, ContinuousOn (fun p : ((ℂ × ℂ) × (ℂ × ℂ)) × ((ℂ × ℂ) × (ℂ × ℂ)) =>
      iteratedFDeriv ℝ i (fun P : (ℂ × ℂ) × (ℂ × ℂ) =>
        A p.1 * ((P - p.1).1.1 * (P - p.1).1.2 * ((P - p.1).2.1 * (P - p.1).2.2))⁻¹) p.2)
      (((sphere c.1.1 r ×ˢ sphere c.1.2 r) ×ˢ (sphere c.2.1 r ×ˢ sphere c.2.2 r)) ×ˢ ball c (r / 2)) := by
  have _hr := hr
  have hm : Continuous (fun w : (ℂ × ℂ) × (ℂ × ℂ) => w.1.1 * w.1.2 * (w.2.1 * w.2.2)) := by fun_prop
  obtain ⟨O, hOdef⟩ : ∃ O : Set ((ℂ × ℂ) × (ℂ × ℂ)), O = {w | w.1.1 * w.1.2 * (w.2.1 * w.2.2) ≠ 0} :=
    ⟨_, rfl⟩
  have hO : IsOpen O := by
    rw [hOdef]
    exact isOpen_ne_fun hm continuous_const
  have hmd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun w : (ℂ × ℂ) × (ℂ × ℂ) => w.1.1 * w.1.2 * (w.2.1 * w.2.2)) :=
    (contDiff_fst.fst.mul contDiff_fst.snd).mul (contDiff_snd.fst.mul contDiff_snd.snd)
  have hk : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun w : (ℂ × ℂ) × (ℂ × ℂ) => (w.1.1 * w.1.2 * (w.2.1 * w.2.2))⁻¹) O := by
    intro w hw
    rw [hOdef] at hw
    exact (hmd.contDiffAt.inv hw).contDiffWithinAt
  have hkc : ∀ i : ℕ, ContinuousOn (iteratedFDeriv ℝ i
      (fun w : (ℂ × ℂ) × (ℂ × ℂ) => (w.1.1 * w.1.2 * (w.2.1 * w.2.2))⁻¹)) O := fun i =>
    (hk.continuousOn_iteratedFDerivWithin (by exact_mod_cast le_top) hO.uniqueDiffOn).congr
      fun w hw => (iteratedFDerivWithin_of_isOpen i hO hw).symm
  have hTO : ∀ q ∈ (sphere c.1.1 r ×ˢ sphere c.1.2 r) ×ˢ (sphere c.2.1 r ×ˢ sphere c.2.2 r),
      ∀ P ∈ ball c (r / 2), P - q ∈ O := by
    intro q hq P hP
    rw [mem_ball] at hP
    simp only [Prod.dist_eq, max_lt_iff] at hP
    have e : ∀ (w c' q' : ℂ), dist w c' < r / 2 → q' ∈ sphere c' r → w - q' ≠ 0 := by
      intro w c' q' hw hq' h
      rw [sub_eq_zero] at h
      rw [h, mem_sphere.1 hq'] at hw
      linarith
    rw [hOdef]
    show (P - q).1.1 * (P - q).1.2 * ((P - q).2.1 * (P - q).2.2) ≠ 0
    simp only [Prod.fst_sub, Prod.snd_sub]
    exact mul_ne_zero (mul_ne_zero (e _ _ _ hP.1.1 hq.1.1) (e _ _ _ hP.1.2 hq.1.2))
      (mul_ne_zero (e _ _ _ hP.2.1 hq.2.1) (e _ _ _ hP.2.2 hq.2.2))
  have hkd : ∀ q ∈ (sphere c.1.1 r ×ˢ sphere c.1.2 r) ×ˢ (sphere c.2.1 r ×ˢ sphere c.2.2 r),
      ∀ P ∈ ball c (r / 2), ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun P : (ℂ × ℂ) × (ℂ × ℂ) => ((P - q).1.1 * (P - q).1.2 * ((P - q).2.1 * (P - q).2.2))⁻¹) P := by
    intro q hq P hP
    exact ContDiffAt.comp (g := fun w : (ℂ × ℂ) × (ℂ × ℂ) => (w.1.1 * w.1.2 * (w.2.1 * w.2.2))⁻¹)
      (f := fun P : (ℂ × ℂ) × (ℂ × ℂ) => P - q) P (hk.contDiffAt (hO.mem_nhds (hTO q hq P hP)))
      (contDiffAt_id.sub contDiffAt_const)
  have hform : ∀ i : ℕ, ∀ q ∈ (sphere c.1.1 r ×ˢ sphere c.1.2 r) ×ˢ (sphere c.2.1 r ×ˢ sphere c.2.2 r),
      ∀ P ∈ ball c (r / 2),
      iteratedFDeriv ℝ i (fun P : (ℂ × ℂ) × (ℂ × ℂ) =>
        A q * ((P - q).1.1 * (P - q).1.2 * ((P - q).2.1 * (P - q).2.2))⁻¹) P =
        A q • iteratedFDeriv ℝ i (fun w : (ℂ × ℂ) × (ℂ × ℂ) => (w.1.1 * w.1.2 * (w.2.1 * w.2.2))⁻¹) (P - q) := by
    intro i q hq P hP
    show iteratedFDeriv ℝ i (fun P : (ℂ × ℂ) × (ℂ × ℂ) =>
      A q • (fun w : (ℂ × ℂ) × (ℂ × ℂ) => (w.1.1 * w.1.2 * (w.2.1 * w.2.2))⁻¹) (P - q)) P = _
    have hs := iteratedFDeriv_comp_sub (𝕜 := ℝ)
      (f := fun w : (ℂ × ℂ) × (ℂ × ℂ) => (w.1.1 * w.1.2 * (w.2.1 * w.2.2))⁻¹) i q P
    rw [iteratedFDeriv_const_smul_apply' ((hkd q hq P hP).of_le (by exact_mod_cast le_top)), hs]
  refine ⟨fun q hq P hP =>
    (contDiffAt_const.mul ((hkd q hq P hP).of_le (by exact_mod_cast le_top))).contDiffWithinAt, fun i _ => ?_⟩
  haveI : ContinuousSMul ℂ (ContinuousMultilinearMap ℝ (fun _ : Fin i => (ℂ × ℂ) × (ℂ × ℂ)) ℂ) :=
    IsBoundedSMul.continuousSMul
  have h1 : ContinuousOn (fun p : ((ℂ × ℂ) × (ℂ × ℂ)) × ((ℂ × ℂ) × (ℂ × ℂ)) =>
      A p.1 • iteratedFDeriv ℝ i (fun w : (ℂ × ℂ) × (ℂ × ℂ) => (w.1.1 * w.1.2 * (w.2.1 * w.2.2))⁻¹) (p.2 - p.1))
      (((sphere c.1.1 r ×ˢ sphere c.1.2 r) ×ˢ (sphere c.2.1 r ×ˢ sphere c.2.2 r)) ×ˢ ball c (r / 2)) :=
    (hA.comp continuous_fst).continuousOn.smul ((hkc i).comp (continuous_snd.sub continuous_fst).continuousOn
      fun p hp => hTO p.1 hp.1 p.2 hp.2)
  exact h1.congr fun p hp => hform i p.1 hp.1 p.2 hp.2

/-- (F5) `[W4]` **Four-parameter D2a.** A function `u(Q, z)` that is jointly holomorphic in `Q` on an open `W`,
jointly continuous on `W ×ˢ Ω`, and `C³` in `z` with jointly continuous `z`-iterated derivatives, is jointly `C³` on
`W ×ˢ Ω` (Cauchy on a 4-polydisc in `Q`, then differentiation under the integral, as in `wr_joint_of_holo_param`). -/
theorem r65_joint_of_holo_param4 {u : (ℂ × ℂ) × (ℂ × ℂ) → ℂ → ℂ} {W : Set ((ℂ × ℂ) × (ℂ × ℂ))} (hW : IsOpen W)
    {Ω : Set ℂ} (hΩ : IsOpen Ω)
    (hh : ∀ z ∈ Ω, DifferentiableOn ℂ (fun Q => u Q z) W)
    (hc : ContinuousOn (fun q : ((ℂ × ℂ) × (ℂ × ℂ)) × ℂ => u q.1 q.2) (W ×ˢ Ω))
    (hz : ∀ Q ∈ W, ContDiffOn ℝ 3 (u Q) Ω)
    (hzc : ∀ j ≤ 3, ContinuousOn (fun q : ((ℂ × ℂ) × (ℂ × ℂ)) × ℂ => iteratedFDeriv ℝ j (u q.1) q.2) (W ×ˢ Ω)) :
    ContDiffOn ℝ 3 (fun q : ((ℂ × ℂ) × (ℂ × ℂ)) × ℂ => u q.1 q.2) (W ×ˢ Ω) := by
  refine contDiffOn_of_locally_contDiffOn fun q₀ hq₀ => ?_
  obtain ⟨hP₀, hz₀⟩ := hq₀
  set c := q₀.1 with hcdef
  obtain ⟨R, hR, hRW⟩ := Metric.isOpen_iff.1 hW c hP₀
  set r := R / 2 with hrdef
  have hr : 0 < r := by positivity
  have hsub : (closedBall c.1.1 r ×ˢ closedBall c.1.2 r) ×ˢ (closedBall c.2.1 r ×ˢ closedBall c.2.2 r) ⊆ W := by
    rintro P ⟨⟨h1, h2⟩, h3, h4⟩
    apply hRW
    rw [mem_closedBall] at h1 h2 h3 h4
    rw [mem_ball]
    simp only [Prod.dist_eq, max_lt_iff]
    exact ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩
  set T := (sphere c.1.1 r ×ˢ sphere c.1.2 r) ×ˢ (sphere c.2.1 r ×ˢ sphere c.2.2 r) with hTdef
  have hTW : T ⊆ W := fun q hq => hsub ⟨⟨sphere_subset_closedBall hq.1.1, sphere_subset_closedBall hq.1.2⟩,
    sphere_subset_closedBall hq.2.1, sphere_subset_closedBall hq.2.2⟩
  have hTc : IsCompact T :=
    ((isCompact_sphere _ _).prod (isCompact_sphere _ _)).prod ((isCompact_sphere _ _).prod (isCompact_sphere _ _))
  set U₁ := ball c (r / 2) with hU₁
  set U := U₁ ×ˢ Ω with hUdef
  have hUo : IsOpen U := isOpen_ball.prod hΩ
  -- the integrand `Φ q (P, z) = (A q · k(P - q)) · u(q, z)`
  set A : (ℂ × ℂ) × (ℂ × ℂ) → ℂ := fun q =>
    (q.1.1 - c.1.1) * I * ((q.1.2 - c.1.2) * I) * ((q.2.1 - c.2.1) * I * ((q.2.2 - c.2.2) * I)) with hAdef
  have hA : Continuous A := by
    rw [hAdef]
    fun_prop
  set a : (ℂ × ℂ) × (ℂ × ℂ) → (ℂ × ℂ) × (ℂ × ℂ) → ℂ := fun q P =>
    A q * ((P - q).1.1 * (P - q).1.2 * ((P - q).2.1 * (P - q).2.2))⁻¹ with hadef
  have hK := fun j => r65_kernel4 (c := c) hr A hA j
  have hsep : ∀ j ≤ 3, ContinuousOn (fun p : ((ℂ × ℂ) × (ℂ × ℂ)) × (((ℂ × ℂ) × (ℂ × ℂ)) × ℂ) =>
      iteratedFDeriv ℝ j (fun y : ((ℂ × ℂ) × (ℂ × ℂ)) × ℂ => ContinuousLinearMap.mul ℝ ℂ (a p.1 y.1) (u p.1 y.2))
        p.2) (T ×ˢ U) := by
    intro j hj
    exact wr_d2a_sep (S := T) isOpen_ball hΩ j (ContinuousLinearMap.mul ℝ ℂ) (a := a) (b := u) (hK j).1
      (fun q hq => (hz q (hTW hq)).of_le (by exact_mod_cast hj)) (hK j).2
      (fun i hi => (hzc i (hi.trans hj)).mono (prod_mono hTW subset_rfl))
  -- the torus parametrization
  set qm : (ℝ × ℝ) × (ℝ × ℝ) → (ℂ × ℂ) × (ℂ × ℂ) := fun x =>
    ((circleMap c.1.1 r x.1.1, circleMap c.1.2 r x.1.2), (circleMap c.2.1 r x.2.1, circleMap c.2.2 r x.2.2))
    with hqm
  have hqc : Continuous qm :=
    (((continuous_circleMap _ _).comp (continuous_fst.comp continuous_fst)).prodMk
      ((continuous_circleMap _ _).comp (continuous_snd.comp continuous_fst))).prodMk
      (((continuous_circleMap _ _).comp (continuous_fst.comp continuous_snd)).prodMk
        ((continuous_circleMap _ _).comp (continuous_snd.comp continuous_snd)))
  have hqT : ∀ x, qm x ∈ T := fun x => ⟨⟨circleMap_mem_sphere _ hr.le _, circleMap_mem_sphere _ hr.le _⟩,
    circleMap_mem_sphere _ hr.le _, circleMap_mem_sphere _ hr.le _⟩
  set F : (ℝ × ℝ) × (ℝ × ℝ) → ((ℂ × ℂ) × (ℂ × ℂ)) × ℂ → ℂ := fun x y =>
    ContinuousLinearMap.mul ℝ ℂ (a (qm x) y.1) (u (qm x) y.2) with hFdef
  set μI : Measure ℝ := volume.restrict (Ioc 0 (2 * π)) with hμI
  have : IsFiniteMeasure μI := isFiniteMeasure_restrict.mpr measure_Ioc_lt_top.ne
  have hI : ContDiffOn ℝ ((3 : ℕ) : WithTop ℕ∞) (fun y => ∫ x, F x y ∂((μI.prod μI).prod (μI.prod μI))) U := by
    refine wr_contDiffOn_integral hUo (fun x => ?_) (fun j hj y hy => ?_) (fun j hj K hK' hKc => ?_)
    · have h1 : ContDiffOn ℝ 3 (fun y : ((ℂ × ℂ) × (ℂ × ℂ)) × ℂ => a (qm x) y.1) U :=
        ((hK 3).1 _ (hqT x)).comp contDiff_fst.contDiffOn fun y hy => hy.1
      have h2 : ContDiffOn ℝ 3 (fun y : ((ℂ × ℂ) × (ℂ × ℂ)) × ℂ => u (qm x) y.2) U :=
        (hz _ (hTW (hqT x))).comp contDiff_snd.contDiffOn fun y hy => hy.2
      exact h1.mul h2
    · have hj' : j ≤ 3 := hj
      exact ((hsep j hj').comp_continuous (hqc.prodMk continuous_const)
        fun x => ⟨hqT x, hy⟩).aestronglyMeasurable
    · have hj' : j ≤ 3 := hj
      obtain ⟨C, hC⟩ := (hTc.prod hKc).exists_bound_of_continuousOn
        ((hsep j hj').mono (prod_mono subset_rfl hK'))
      exact ⟨C, fun x y hy => hC (qm x, y) ⟨hqT x, hy⟩⟩
  -- the Cauchy representation
  have hrep : ∀ y ∈ U, u y.1 y.2 = ((2 * π * I)⁻¹) ^ 4 * ∫ x, F x y ∂((μI.prod μI).prod (μI.prod μI)) := by
    rintro y ⟨hy1, hy2⟩
    rw [r65_cauchy4_int (f := fun P => u P y.2) hr
      (hc.comp (continuous_id.prodMk continuous_const).continuousOn fun P hP => ⟨hsub hP, hy2⟩)
      (fun Q hQ => (hh y.2 hy2).differentiableAt (hW.mem_nhds (hsub hQ))) hy1]
    congr 1
  refine ⟨U, hUo, ⟨mem_ball_self (by positivity), hz₀⟩, ?_⟩
  exact ((contDiffOn_const.mul (by exact_mod_cast hI)).congr hrep).mono inter_subset_right

/-- (F6) `[W5]` **Joint `C³` of the four-parameter family** on `W ×ˢ Ω` (F1 + F2 + F4 + F5). -/
theorem r65_local_joint_contDiff4 {m₁ m₂ n₁ n₂ : ℂ → ℂ} {k₁ k₂ k₃ k₄ : ℝ} (hm₁ : IsBeltramiCoeff m₁ univ k₁)
    (hm₂ : IsBeltramiCoeff m₂ univ k₂) (hn₁ : IsBeltramiCoeff n₁ univ k₃) (hn₂ : IsBeltramiCoeff n₂ univ k₄)
    {Ω : Set ℂ} (hΩ : IsOpen Ω)
    (hs₁ : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) m₁ Ω) (hs₂ : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) n₁ Ω)
    (h0 : ∀ u ∈ Ω, m₂ u = 0 ∧ n₂ u = 0)
    {W : Set ((ℂ × ℂ) × (ℂ × ℂ))} (hW : IsOpen W)
    (hWk : ∀ Q ∈ W, ∃ k < 1,
      IsBeltramiCoeff (fun u => Q.1.1 * m₁ u + Q.1.2 * m₂ u + Q.2.1 * n₁ u + Q.2.2 * n₂ u) univ k) :
    ContDiffOn ℝ 3 (fun q : ((ℂ × ℂ) × (ℂ × ℂ)) × ℂ =>
      normalizedSolution (fun u => q.1.1.1 * m₁ u + q.1.1.2 * m₂ u + q.1.2.1 * n₁ u + q.1.2.2 * n₂ u) q.2)
      (W ×ˢ Ω) := by
  obtain ⟨hz, hzc⟩ := r65_ns4_z_regular hm₁ hm₂ hn₁ hn₂ hΩ hs₁ hs₂ h0 hW hWk
  exact r65_joint_of_holo_param4
    (u := fun Q => normalizedSolution fun u => Q.1.1 * m₁ u + Q.1.2 * m₂ u + Q.2.1 * n₁ u + Q.2.2 * n₂ u) hW hΩ
    (fun z _ Q hQ => by
      obtain ⟨k, hk, hb⟩ := hWk Q hQ
      exact (r65_ns4_diffAt hm₁ hm₂ hn₁ hn₂ hk hb z).differentiableWithinAt)
    ((r65_ns4_cont hm₁ hm₂ hn₁ hn₂ hWk).mono (prod_mono subset_rfl (subset_univ _))) hz hzc

/-! ## Part U — model `𝕌`, two directions -/

/-- (U1) `[W5]` `extU (e₁μ + e₂ν) = e₁·m₁ + ē₁·m₂ + e₂·n₁ + ē₂·n₂` (two-direction `wr_extU_smul`). -/
theorem r65_extU_add (μ ν : ℂ → ℂ) (e₁ e₂ : ℂ) :
    extU (fun u => e₁ * μ u + e₂ * ν u) = fun u => e₁ * (if 0 < u.im then μ u else 0) +
      conj e₁ * (if u.im < 0 then conj (μ (conj u)) else 0) + e₂ * (if 0 < u.im then ν u else 0) +
      conj e₂ * (if u.im < 0 then conj (ν (conj u)) else 0) := by
  funext u
  unfold extU
  by_cases h1 : 0 < u.im
  · have h2 : ¬ u.im < 0 := by linarith
    simp only [h1, h2, ↓reduceIte, mul_zero, add_zero]
  · by_cases h2 : u.im < 0
    · simp only [h1, h2, ↓reduceIte, mul_zero, zero_add, add_zero, map_add, map_mul]
    · simp only [h1, h2, ↓reduceIte, mul_zero, add_zero]

/-- (U2) `[W5]` **E2 in two directions.** For `μ, ν` smooth on `𝕌` with `|μ|, |ν| ≤ k` there,
`((e₁, e₂), z) ↦ w_{e₁μ+e₂ν}(z)` is jointly `C³` on `{(‖e₁‖ + ‖e₂‖) k < 1} × 𝕌`. -/
theorem r65_joint_contDiff_U2 {μ ν : ℂ → ℂ} {k : ℝ} (hk : 0 ≤ k) (hμk : IsBeltramiCoeff μ upperHalf k)
    (hνk : IsBeltramiCoeff ν upperHalf k) (hμs : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) μ upperHalf)
    (hνs : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ν upperHalf) :
    ContDiffOn ℝ 3 (fun p : (ℂ × ℂ) × ℂ => wU (fun u => p.1.1 * μ u + p.1.2 * ν u) p.2)
      ({e : ℂ × ℂ | (‖e.1‖ + ‖e.2‖) * k < 1} ×ˢ upperHalf) := by
  obtain ⟨hm₁, hm₂, hs₁, -, -⟩ := wr_U_coeffs hk hμk hμs
  obtain ⟨hn₁, hn₂, hs₂, -, -⟩ := wr_U_coeffs hk hνk hνs
  have hU : IsOpen upperHalf := isOpen_lt continuous_const Complex.continuous_im
  have h0 : ∀ u ∈ upperHalf, (if u.im < 0 then conj (μ (conj u)) else 0) = 0 ∧
      (if u.im < 0 then conj (ν (conj u)) else 0) = 0 := by
    intro u hu
    have : ¬ u.im < 0 := by have : (0 : ℝ) < u.im := hu; linarith
    simp only [this, ↓reduceIte, and_self]
  have hW : IsOpen {Q : (ℂ × ℂ) × (ℂ × ℂ) | (max ‖Q.1.1‖ ‖Q.1.2‖ + max ‖Q.2.1‖ ‖Q.2.2‖) * k < 1} :=
    isOpen_lt ((((continuous_norm.comp (continuous_fst.comp continuous_fst)).max
      (continuous_norm.comp (continuous_snd.comp continuous_fst))).add
      ((continuous_norm.comp (continuous_fst.comp continuous_snd)).max
      (continuous_norm.comp (continuous_snd.comp continuous_snd)))).mul continuous_const) continuous_const
  have hWk : ∀ Q ∈ {Q : (ℂ × ℂ) × (ℂ × ℂ) | (max ‖Q.1.1‖ ‖Q.1.2‖ + max ‖Q.2.1‖ ‖Q.2.2‖) * k < 1}, ∃ k' < 1,
      IsBeltramiCoeff (fun u => Q.1.1 * (if 0 < u.im then μ u else 0) +
        Q.1.2 * (if u.im < 0 then conj (μ (conj u)) else 0) + Q.2.1 * (if 0 < u.im then ν u else 0) +
        Q.2.2 * (if u.im < 0 then conj (ν (conj u)) else 0)) univ k' := by
    intro Q hQ
    refine ⟨_, hQ, (((hm₁.1.const_mul Q.1.1).add (hm₂.1.const_mul Q.1.2)).add (hn₁.1.const_mul Q.2.1)).add
      (hn₂.1.const_mul Q.2.2), ?_⟩
    filter_upwards [hm₁.2, hm₂.2, hn₁.2, hn₂.2] with u h₁ h₂ h₃ h₄
    have a1 := le_max_left ‖Q.1.1‖ ‖Q.1.2‖
    have a2 := le_max_right ‖Q.1.1‖ ‖Q.1.2‖
    have a3 := le_max_left ‖Q.2.1‖ ‖Q.2.2‖
    have a4 := le_max_right ‖Q.2.1‖ ‖Q.2.2‖
    have t : ∀ (a x : ℂ) (M : ℝ), ‖a‖ ≤ M → ‖x‖ ≤ k → ‖a * x‖ ≤ M * k := fun a x M ha hx => by
      rw [norm_mul]; exact mul_le_mul ha hx (norm_nonneg _) ((norm_nonneg _).trans ha)
    have e : (max ‖Q.1.1‖ ‖Q.1.2‖ + max ‖Q.2.1‖ ‖Q.2.2‖) * k =
        max ‖Q.1.1‖ ‖Q.1.2‖ * k + max ‖Q.2.1‖ ‖Q.2.2‖ * k := by ring
    rw [e]
    by_cases hu1 : 0 < u.im
    · have hu2 : ¬ u.im < 0 := by linarith
      simp only [hu1, hu2, ↓reduceIte] at h₁ h₃ ⊢
      simp only [mul_zero, add_zero]
      exact (norm_add_le _ _).trans (add_le_add (t _ _ _ a1 h₁) (t _ _ _ a3 h₃))
    · by_cases hu2 : u.im < 0
      · simp only [hu1, hu2, ↓reduceIte] at h₂ h₄ ⊢
        simp only [mul_zero, zero_add, add_zero]
        exact (norm_add_le _ _).trans (add_le_add (t _ _ _ a2 h₂) (t _ _ _ a4 h₄))
      · simp only [hu1, hu2, ↓reduceIte, mul_zero, add_zero, norm_zero]
        have hk0 : 0 ≤ max ‖Q.1.1‖ ‖Q.1.2‖ * k := mul_nonneg ((norm_nonneg _).trans a1) hk
        have hk1 : 0 ≤ max ‖Q.2.1‖ ‖Q.2.2‖ * k := mul_nonneg ((norm_nonneg _).trans a3) hk
        linarith
  have hD := r65_local_joint_contDiff4 hm₁ hm₂ hn₁ hn₂ hU hs₁ hs₂ h0 hW hWk
  have hφ : ContDiff ℝ 3 (fun p : (ℂ × ℂ) × ℂ => (((p.1.1, conj p.1.1), (p.1.2, conj p.1.2)), p.2)) :=
    ((contDiff_fst.comp contDiff_fst).prodMk (Complex.conjCLE.contDiff.comp (contDiff_fst.comp contDiff_fst))
      |>.prodMk ((contDiff_snd.comp contDiff_fst).prodMk
        (Complex.conjCLE.contDiff.comp (contDiff_snd.comp contDiff_fst)))).prodMk contDiff_snd
  refine (hD.comp hφ.contDiffOn (fun p hp => ⟨?_, hp.2⟩)).congr (fun p _ => ?_)
  · show (max ‖p.1.1‖ ‖conj p.1.1‖ + max ‖p.1.2‖ ‖conj p.1.2‖) * k < 1
    rw [RCLike.norm_conj, RCLike.norm_conj, max_self, max_self]
    exact hp.1
  · show normalizedSolution (extU fun u => p.1.1 * μ u + p.1.2 * ν u) p.2 = _
    rw [r65_extU_add]
    rfl

/-- (U3) `[W5]` The two-parameter density `e ↦ ρ^{e₁μ+e₂ν}(z)` is real `C²` at `0` for harmonic `μ, ν`. -/
theorem r65_rho2_contDiffAt {μ ν φ ψ : ℂ → ℂ} (hμ : IsHarmonicU μ φ) (hν : IsHarmonicU ν ψ) {z : ℂ}
    (hz : z ∈ upperHalf) :
    ContDiffAt ℝ 2 (fun e : ℂ × ℂ => -4 * (‖dz (wU fun u => e.1 * μ u + e.2 * ν u) z‖ ^ 2 : ℝ) /
      (wU (fun u => e.1 * μ u + e.2 * ν u) z - conj (wU (fun u => e.1 * μ u + e.2 * ν u) z)) ^ 2) 0 := by
  have hU : IsOpen upperHalf := isOpen_lt continuous_const Complex.continuous_im
  obtain ⟨Cμ, hCμ0, hCμ⟩ := harmonicU_bounded hμ
  obtain ⟨Cν, -, hCν⟩ := harmonicU_bounded hν
  have hk : 0 ≤ max Cμ Cν := hCμ0.trans (le_max_left _ _)
  have hμk : IsBeltramiCoeff μ upperHalf (max Cμ Cν) :=
    ⟨(harmonicU_continuousOn hμ).aestronglyMeasurable hU.measurableSet,
      (ae_restrict_mem hU.measurableSet).mono fun u hu => (hCμ u hu).trans (le_max_left _ _)⟩
  have hνk : IsBeltramiCoeff ν upperHalf (max Cμ Cν) :=
    ⟨(harmonicU_continuousOn hν).aestronglyMeasurable hU.measurableSet,
      (ae_restrict_mem hU.measurableSet).mono fun u hu => (hCν u hu).trans (le_max_right _ _)⟩
  have hJ := r65_joint_contDiff_U2 hk hμk hνk (wr_isHarmonicU_contDiffOn hμ) (wr_isHarmonicU_contDiffOn hν)
  obtain ⟨J, hJd⟩ : ∃ J : (ℂ × ℂ) × ℂ → ℂ, J = fun p => wU (fun u => p.1.1 * μ u + p.1.2 * ν u) p.2 :=
    ⟨_, rfl⟩
  rw [← hJd] at hJ
  obtain ⟨S, hSd⟩ : ∃ S : Set ((ℂ × ℂ) × ℂ),
      S = {e : ℂ × ℂ | (‖e.1‖ + ‖e.2‖) * max Cμ Cν < 1} ×ˢ upperHalf := ⟨_, rfl⟩
  rw [← hSd] at hJ
  have hSo : IsOpen S := by
    rw [hSd]
    exact (isOpen_lt (((continuous_norm.comp continuous_fst).add (continuous_norm.comp continuous_snd)).mul
      continuous_const) continuous_const).prod hU
  have hg : Continuous fun e : ℂ × ℂ => (e, z) := continuous_id.prodMk continuous_const
  have h0S : ((0 : ℂ × ℂ), z) ∈ S := by
    rw [hSd]; exact ⟨by simp, hz⟩
  have hN : ∀ᶠ e in 𝓝 (0 : ℂ × ℂ), (e, z) ∈ S := hg.continuousAt.preimage_mem_nhds (hSo.mem_nhds h0S)
  -- `D w_e(z) v = DJ(e, z)(0, v)` near `e = 0`
  have hpart : ∀ e : ℂ × ℂ, (e, z) ∈ S → ∀ v : ℂ,
      fderiv ℝ (wU fun u => e.1 * μ u + e.2 * ν u) z v = fderiv ℝ J (e, z) (0, v) := by
    intro e he v
    have hJa : DifferentiableAt ℝ J (e, z) :=
      ((hJ.contDiffAt (hSo.mem_nhds he)).differentiableAt (by norm_num))
    have hi : HasFDerivAt (fun z' : ℂ => (e, z')) ((0 : ℂ →L[ℝ] ℂ × ℂ).prod (ContinuousLinearMap.id ℝ ℂ)) z :=
      (hasFDerivAt_const e z).prodMk (hasFDerivAt_id z)
    have hc := HasFDerivAt.comp (f := fun z' : ℂ => (e, z')) z hJa.hasFDerivAt hi
    have heq : (wU fun u => e.1 * μ u + e.2 * ν u) = J ∘ fun z' : ℂ => (e, z') := by
      funext z'; rw [hJd]; rfl
    rw [heq, hc.fderiv]
    simp
  have hD2 : ContDiffOn ℝ 2 (fderiv ℝ J) S := hJ.fderiv_of_isOpen hSo (by norm_num)
  have hDa : ContDiffAt ℝ 2 (fun e : ℂ × ℂ => fderiv ℝ J (e, z)) 0 :=
    (hD2.contDiffAt (hSo.mem_nhds h0S)).comp (0 : ℂ × ℂ) (contDiffAt_id.prodMk contDiffAt_const)
  have hdz : ContDiffAt ℝ 2 (fun e : ℂ × ℂ =>
      (fderiv ℝ J (e, z) (0, 1) - I * fderiv ℝ J (e, z) (0, I)) / 2) 0 :=
    ((hDa.clm_apply contDiffAt_const).sub (contDiffAt_const.mul (hDa.clm_apply contDiffAt_const))).div_const _
  have hV : ContDiffAt ℝ 2 (fun e : ℂ × ℂ => J (e, z)) 0 :=
    ((hJ.contDiffAt (hSo.mem_nhds h0S)).of_le (by norm_num)).comp (0 : ℂ × ℂ)
      (contDiffAt_id.prodMk contDiffAt_const)
  -- `w₀ = id`, so the denominator does not vanish at `0`
  have hw0 : J (0, z) = z := by
    rw [hJd]
    show normalizedSolution (extU fun u => (0 : ℂ × ℂ).1 * μ u + (0 : ℂ × ℂ).2 * ν u) z = z
    have hext : extU (fun u => (0 : ℂ × ℂ).1 * μ u + (0 : ℂ × ℂ).2 * ν u) = 0 := by
      funext u
      simp only [extU, Prod.fst_zero, Prod.snd_zero, zero_mul, add_zero, map_zero, ite_self, Pi.zero_apply]
    rw [hext, bB_l_normalizedSolution_zero]
    rfl
  have hne : J (0, z) - conj (J (0, z)) ≠ 0 := by
    rw [hw0, Complex.sub_conj]
    have : (0 : ℝ) < z.im := hz
    exact mul_ne_zero (Complex.ofReal_ne_zero.mpr (by positivity)) I_ne_zero
  have hden : ContDiffAt ℝ 2 (fun e : ℂ × ℂ => ((J (e, z) - conj (J (e, z))) ^ 2)⁻¹) 0 :=
    ((hV.sub (Complex.conjCLE.contDiff.contDiffAt.comp (0 : ℂ × ℂ) hV)).pow 2).inv (pow_ne_zero 2 hne)
  have hnum : ContDiffAt ℝ 2 (fun e : ℂ × ℂ => (-4 : ℂ) * (((‖(fderiv ℝ J (e, z) (0, 1) -
      I * fderiv ℝ J (e, z) (0, I)) / 2‖ ^ 2 : ℝ)) : ℂ)) 0 :=
    contDiffAt_const.mul (Complex.ofRealCLM.contDiff.contDiffAt.comp (0 : ℂ × ℂ)
      ((contDiff_norm_sq ℝ).contDiffAt.comp (0 : ℂ × ℂ) hdz))
  refine (hnum.mul hden).congr_of_eventuallyEq ?_
  filter_upwards [hN] with e he
  have h1 := hpart e he 1
  have hI := hpart e he I
  have hdze : dz (wU fun u => e.1 * μ u + e.2 * ν u) z =
      (fderiv ℝ J (e, z) (0, 1) - I * fderiv ℝ J (e, z) (0, I)) / 2 := by
    show (fderiv ℝ (wU fun u => e.1 * μ u + e.2 * ν u) z 1 -
      I * fderiv ℝ (wU fun u => e.1 * μ u + e.2 * ν u) z I) / 2 = _
    rw [h1, hI]
  have hJe : wU (fun u => e.1 * μ u + e.2 * ν u) z = J (e, z) := by rw [hJd]
  show -4 * ((‖dz (wU fun u => e.1 * μ u + e.2 * ν u) z‖ ^ 2 : ℝ) : ℂ) /
      (wU (fun u => e.1 * μ u + e.2 * ν u) z - conj (wU (fun u => e.1 * μ u + e.2 * ν u) z)) ^ 2 = _
  rw [hdze, hJe, div_eq_mul_inv]

/-! ## Part P — polarization `[W3]` -/


/-- `∂̄g(s) = ∂̄[t ↦ g(s + t)](0)`. -/
theorem r65_dzbar_shift (g : ℂ → ℂ) (s : ℂ) : dzbar g s = dzbar (fun t => g (s + t)) 0 := by
  unfold dzbar
  rw [fderiv_comp_add_left, add_zero]

/-- Mixed Wirtinger derivative of `(s, t) ↦ F(P s + B t)` at `0` through the second derivative of `F`. -/
theorem r65_mixed {F : ℂ × ℂ → ℂ} (hF : ContDiffAt ℝ 2 F 0) (P B : ℂ →L[ℝ] ℂ × ℂ) :
    dz (fun s => dzbar (fun t => F (P s + B t)) 0) 0 =
      (fderiv ℝ (fderiv ℝ F) 0 (P 1) (B 1) + I * fderiv ℝ (fderiv ℝ F) 0 (P 1) (B I) -
        I * fderiv ℝ (fderiv ℝ F) 0 (P I) (B 1) + fderiv ℝ (fderiv ℝ F) 0 (P I) (B I)) / 4 := by
  have hev : ∀ᶠ y in 𝓝 (0 : ℂ × ℂ), DifferentiableAt ℝ F y := by
    filter_upwards [hF.eventually (by simp)] with y hy
    exact hy.differentiableAt (by simp)
  have ht : Tendsto P (𝓝 0) (𝓝 0) := by simpa using P.continuous.tendsto 0
  have hP : ∀ᶠ s in 𝓝 (0 : ℂ), DifferentiableAt ℝ F (P s) := ht.eventually hev
  have hloc : (fun s => dzbar (fun t => F (P s + B t)) 0) =ᶠ[𝓝 0]
      fun s => (1 / 2 : ℂ) * (fderiv ℝ F (P s) (B 1) + I * fderiv ℝ F (P s) (B I)) := by
    filter_upwards [hP] with s hs
    have h1 : HasFDerivAt (fun t => P s + B t) B 0 := B.hasFDerivAt.const_add (P s)
    have h2 : HasFDerivAt F (fderiv ℝ F (P s)) (P s + B 0) := by
      rw [map_zero, add_zero]
      exact hs.hasFDerivAt
    have hd : HasFDerivAt (fun t => F (P s + B t)) ((fderiv ℝ F (P s)).comp B) 0 := h2.comp 0 h1
    unfold dzbar
    rw [hd.fderiv]
    simp only [ContinuousLinearMap.comp_apply]
    ring
  have hD : HasFDerivAt (fderiv ℝ F) (fderiv ℝ (fderiv ℝ F) 0) (P 0) := by
    rw [map_zero]
    exact ((hF.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero).hasFDerivAt
  have hDP : HasFDerivAt (fun s => fderiv ℝ F (P s)) ((fderiv ℝ (fderiv ℝ F) 0).comp P) 0 :=
    hD.comp 0 P.hasFDerivAt
  have hg1 := hDP.clm_apply (hasFDerivAt_const (B 1) (0 : ℂ))
  have hg2 := hDP.clm_apply (hasFDerivAt_const (B I) (0 : ℂ))
  have hG : HasFDerivAt (fun s => (1 / 2 : ℂ) * (fderiv ℝ F (P s) (B 1) + I * fderiv ℝ F (P s) (B I))) _ 0 :=
    (hg1.add (hg2.const_mul I)).const_mul (1 / 2 : ℂ)
  unfold dz
  rw [hloc.fderiv_eq, hG.fderiv]
  simp only [add_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply, ContinuousLinearMap.zero_apply, map_zero, zero_add, smul_eq_mul]
  linear_combination (-(fderiv ℝ (fderiv ℝ F) 0 (P I) (B I)) / 4) * I_sq

/-- `∂∂̄[ε ↦ F(ε, λε)](0)` through the second derivative of `F`. -/
theorem r65_line {F : ℂ × ℂ → ℂ} (hF : ContDiffAt ℝ 2 F 0) (c : ℂ) :
    dz (dzbar fun ε => F (ε, c * ε)) 0 =
      (fderiv ℝ (fderiv ℝ F) 0 (ContinuousLinearMap.inl ℝ ℂ ℂ 1 + ContinuousLinearMap.inr ℝ ℂ ℂ (c * 1))
          (ContinuousLinearMap.inl ℝ ℂ ℂ 1 + ContinuousLinearMap.inr ℝ ℂ ℂ (c * 1)) +
        I * fderiv ℝ (fderiv ℝ F) 0 (ContinuousLinearMap.inl ℝ ℂ ℂ 1 + ContinuousLinearMap.inr ℝ ℂ ℂ (c * 1))
          (ContinuousLinearMap.inl ℝ ℂ ℂ I + ContinuousLinearMap.inr ℝ ℂ ℂ (c * I)) -
        I * fderiv ℝ (fderiv ℝ F) 0 (ContinuousLinearMap.inl ℝ ℂ ℂ I + ContinuousLinearMap.inr ℝ ℂ ℂ (c * I))
          (ContinuousLinearMap.inl ℝ ℂ ℂ 1 + ContinuousLinearMap.inr ℝ ℂ ℂ (c * 1)) +
        fderiv ℝ (fderiv ℝ F) 0 (ContinuousLinearMap.inl ℝ ℂ ℂ I + ContinuousLinearMap.inr ℝ ℂ ℂ (c * I))
          (ContinuousLinearMap.inl ℝ ℂ ℂ I + ContinuousLinearMap.inr ℝ ℂ ℂ (c * I))) / 4 := by
  have hfun : (dzbar fun ε => F (ε, c * ε)) = fun s =>
      dzbar (fun t => F ((ContinuousLinearMap.inl ℝ ℂ ℂ + ContinuousLinearMap.inr ℝ ℂ ℂ ∘L
        ContinuousLinearMap.mul ℝ ℂ c) s + (ContinuousLinearMap.inl ℝ ℂ ℂ + ContinuousLinearMap.inr ℝ ℂ ℂ ∘L
        ContinuousLinearMap.mul ℝ ℂ c) t)) 0 := by
    funext s
    rw [r65_dzbar_shift]
    congr 1
    funext t
    congr 1
    ext <;> simp [mul_add]
  rw [hfun, r65_mixed hF]
  simp only [add_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.mul_apply']

/-- (P1) `[W3]` **Second-order Wirtinger polarization.** For `F` real `C²` at `0`, the mixed derivative
`∂_{e₁}∂̄_{e₂}F(0)` is `¼ Σ_{λ ∈ {1, -1, i, -i}} λ · ∂∂̄[ε ↦ F(ε, λε)](0)`. -/
theorem r65_wirtinger_polar {F : ℂ × ℂ → ℂ} (hF : ContDiffAt ℝ 2 F 0) :
    dz (fun e₁ => dzbar (fun e₂ => F (e₁, e₂)) 0) 0 =
      (1 / 4 : ℂ) * (dz (dzbar fun ε => F (ε, 1 * ε)) 0 - dz (dzbar fun ε => F (ε, -1 * ε)) 0 +
        I * dz (dzbar fun ε => F (ε, I * ε)) 0 - I * dz (dzbar fun ε => F (ε, -I * ε)) 0) := by
  have hL : (fun e₁ => dzbar (fun e₂ => F (e₁, e₂)) 0) =
      fun s => dzbar (fun t => F (ContinuousLinearMap.inl ℝ ℂ ℂ s + ContinuousLinearMap.inr ℝ ℂ ℂ t)) 0 := by
    funext s
    simp only [ContinuousLinearMap.inl_apply, ContinuousLinearMap.inr_apply, Prod.mk_add_mk, add_zero, zero_add]
  have hS := hF.isSymmSndFDerivAt (by simp)
  rw [hL, r65_mixed hF, r65_line hF, r65_line hF, r65_line hF, r65_line hF]
  set D := fderiv ℝ (fderiv ℝ F) 0
  set e₁ := ContinuousLinearMap.inl ℝ ℂ ℂ 1
  set e₂ := ContinuousLinearMap.inl ℝ ℂ ℂ I
  set e₃ := ContinuousLinearMap.inr ℝ ℂ ℂ 1
  set e₄ := ContinuousLinearMap.inr ℝ ℂ ℂ I
  have m1 : ContinuousLinearMap.inr ℝ ℂ ℂ (-1 * 1) = -e₃ := by rw [← map_neg]; norm_num
  have m2 : ContinuousLinearMap.inr ℝ ℂ ℂ (-1 * I) = -e₄ := by rw [← map_neg]; norm_num
  have m3 : ContinuousLinearMap.inr ℝ ℂ ℂ (I * I) = -e₃ := by rw [← map_neg]; norm_num
  have m4 : ContinuousLinearMap.inr ℝ ℂ ℂ (-I * 1) = -e₄ := by rw [← map_neg]; norm_num
  have m5 : ContinuousLinearMap.inr ℝ ℂ ℂ (-I * I) = e₃ := by norm_num [e₃]
  have m6 : ContinuousLinearMap.inr ℝ ℂ ℂ (1 * 1) = e₃ := by norm_num [e₃]
  have m7 : ContinuousLinearMap.inr ℝ ℂ ℂ (1 * I) = e₄ := by norm_num [e₄]
  have m8 : ContinuousLinearMap.inr ℝ ℂ ℂ (I * 1) = e₄ := by norm_num [e₄]
  rw [m1, m2, m3, m4, m5, m6, m7, m8]
  simp only [map_add, map_neg, add_apply, neg_apply]
  rw [hS e₂ e₁, hS e₃ e₁, hS e₄ e₁, hS e₃ e₂, hS e₄ e₂, hS e₄ e₃]
  ring

/-- (P2) `[W3]` Harmonic Beltrami differentials are closed under `μ + λν`. -/
theorem r65_harm_comb {μ ν φ ψ : ℂ → ℂ} (hμ : IsHarmonicU μ φ) (hν : IsHarmonicU ν ψ) (c : ℂ) :
    IsHarmonicU (fun u => μ u + c * ν u) (fun u => φ u + conj c * ψ u) := by
  obtain ⟨h1, ⟨C₁, hC₁⟩, h3⟩ := hμ
  obtain ⟨g1, ⟨C₂, hC₂⟩, g3⟩ := hν
  refine ⟨h1.add ((differentiableOn_const _).mul g1), ⟨C₁ + ‖c‖ * C₂, fun z hz => ?_⟩, fun z hz => ?_⟩
  · rw [mul_add, mul_left_comm]
    refine (norm_add_le _ _).trans (add_le_add (hC₁ z hz) ?_)
    rw [norm_mul, Complex.norm_conj]
    exact mul_le_mul_of_nonneg_left (hC₂ z hz) (norm_nonneg _)
  · show μ z + c * ν z = (z - conj z) ^ 2 / 2 * conj (φ z + conj c * ψ z)
    rw [h3 z hz, g3 z hz, map_add, map_mul, Complex.conj_conj]
    ring

/-- Pointwise polarization: `a b̄ = ¼ Σ_λ λ |a + λb|²`. -/
theorem r65_polar_pt (a b : ℂ) :
    a * conj b = (1 / 4 : ℂ) * (((‖a + 1 * b‖ ^ 2 : ℝ) : ℂ) - ((‖a + -1 * b‖ ^ 2 : ℝ) : ℂ) +
      I * ((‖a + I * b‖ ^ 2 : ℝ) : ℂ) - I * ((‖a + -I * b‖ ^ 2 : ℝ) : ℂ)) := by
  have h : ∀ x : ℂ, ((‖x‖ ^ 2 : ℝ) : ℂ) = x * conj x := fun x => by
    rw [Complex.mul_conj, Complex.sq_norm]
  rw [h, h, h, h]
  simp only [map_add, map_mul, map_neg, map_one, Complex.conj_I]
  linear_combination ((a * conj b - b * conj a) / 2) * I_sq

/-- (P3) `[W3]` Polarization of the resolvent: `G(μν̄) = ¼ Σ_λ λ G(|μ + λν|²)`. -/
theorem r65_resolvent_polar {μ ν φ ψ : ℂ → ℂ} (hμ : IsHarmonicU μ φ) (hν : IsHarmonicU ν ψ) {z : ℂ}
    (hz : z ∈ upperHalf) :
    resolventOpU (fun u => μ u * conj (ν u)) z =
      (1 / 4 : ℂ) * (resolventOpU (fun u => (‖μ u + 1 * ν u‖ ^ 2 : ℝ)) z -
        resolventOpU (fun u => (‖μ u + -1 * ν u‖ ^ 2 : ℝ)) z +
        I * resolventOpU (fun u => (‖μ u + I * ν u‖ ^ 2 : ℝ)) z -
        I * resolventOpU (fun u => (‖μ u + -I * ν u‖ ^ 2 : ℝ)) z) := by
  have hi : ∀ c : ℂ, Integrable (fun w => (resolventKernelU z w : ℂ) *
      ((‖μ w + c * ν w‖ ^ 2 : ℝ) : ℂ) * rhoU w) (volume.restrict upperHalf) := fun c => by
    refine (harmonicU_resolvent_product_integrable (r65_harm_comb hμ hν c) (r65_harm_comb hμ hν c) hz).congr
      (ae_of_all _ fun w => ?_)
    simp only
    rw [Complex.mul_conj, Complex.sq_norm]
  have hpt : (fun w => (resolventKernelU z w : ℂ) * (μ w * conj (ν w)) * rhoU w) = fun w =>
      (1 / 4 : ℂ) * ((resolventKernelU z w : ℂ) * ((‖μ w + 1 * ν w‖ ^ 2 : ℝ) : ℂ) * rhoU w -
        (resolventKernelU z w : ℂ) * ((‖μ w + -1 * ν w‖ ^ 2 : ℝ) : ℂ) * rhoU w +
        I * ((resolventKernelU z w : ℂ) * ((‖μ w + I * ν w‖ ^ 2 : ℝ) : ℂ) * rhoU w) -
        I * ((resolventKernelU z w : ℂ) * ((‖μ w + -I * ν w‖ ^ 2 : ℝ) : ℂ) * rhoU w)) := by
    funext w
    rw [r65_polar_pt (μ w) (ν w)]
    ring
  unfold resolventOpU
  rw [hpt, integral_const_mul, integral_sub ?_ ?_, integral_add ?_ ?_, integral_sub ?_ ?_, integral_const_mul,
    integral_const_mul]
  all_goals first
    | rfl
    | exact ((hi 1).sub (hi (-1))).add ((hi I).const_mul I)
    | exact (hi (-I)).const_mul I
    | exact (hi 1).sub (hi (-1))
    | exact (hi I).const_mul I
    | exact hi 1
    | exact hi (-1)


/-! ## Assembly `[W5]`: `r65_remark_6_5` is `remark_6_5` (S6) with the prefixed name, statement byte-identical
(relocated at round end, as `e62_eq_6_2`) -/

/-- **Remark 6.5** (TT:2668–2672). By polarization,
`L_μ L_{ν̄} ρ = ∂²/∂ε₁∂ε̄₂|_{ε₁=ε₂=0} ρ^{ε₁μ + ε₂ν} = ρ G(μν̄)`. -/
theorem r65_remark_6_5 {μ ν φ ψ : ℂ → ℂ} (hμ : IsHarmonicU μ φ) (hν : IsHarmonicU ν ψ) {z : ℂ} (hz : z ∈ upperHalf) :
    dz (fun e₁ => dzbar (fun e₂ => -4 * (‖dz (wU fun u => e₁ * μ u + e₂ * ν u) z‖ ^ 2 : ℝ) /
        (wU (fun u => e₁ * μ u + e₂ * ν u) z - conj (wU (fun u => e₁ * μ u + e₂ * ν u) z)) ^ 2) 0) 0 =
      rhoU z * resolventOpU (fun u => μ u * conj (ν u)) z := by
  obtain ⟨F, hF⟩ : ∃ F : ℂ × ℂ → ℂ, F = fun e => -4 * (‖dz (wU fun u => e.1 * μ u + e.2 * ν u) z‖ ^ 2 : ℝ) /
      (wU (fun u => e.1 * μ u + e.2 * ν u) z - conj (wU (fun u => e.1 * μ u + e.2 * ν u) z)) ^ 2 := ⟨_, rfl⟩
  have hP := r65_wirtinger_polar (F := F) (by rw [hF]; exact r65_rho2_contDiffAt hμ hν hz)
  have hlam : ∀ c : ℂ, dz (dzbar fun ε => F (ε, c * ε)) 0 =
      rhoU z * resolventOpU (fun u => (‖μ u + c * ν u‖ ^ 2 : ℝ)) z := by
    intro c
    have he : (fun ε => F (ε, c * ε)) = fun ε => rhoVar (fun u => μ u + c * ν u) ε z := by
      funext ε
      have hw : (fun u => ε * μ u + c * ε * ν u) = fun u => ε * (μ u + c * ν u) := by
        funext u; ring
      rw [hF]
      show -4 * (‖dz (wU fun u => ε * μ u + c * ε * ν u) z‖ ^ 2 : ℝ) /
          (wU (fun u => ε * μ u + c * ε * ν u) z - conj (wU (fun u => ε * μ u + c * ε * ν u) z)) ^ 2 =
        -4 * (‖dz (wU fun u => ε * (μ u + c * ν u)) z‖ ^ 2 : ℝ) /
          (wU (fun u => ε * (μ u + c * ν u)) z - conj (wU (fun u => ε * (μ u + c * ν u)) z)) ^ 2
      rw [hw]
    rw [he]
    exact e64_prop_6_3 (r65_harm_comb hμ hν c) hz
  have hL : (fun e₁ => dzbar (fun e₂ => -4 * (‖dz (wU fun u => e₁ * μ u + e₂ * ν u) z‖ ^ 2 : ℝ) /
      (wU (fun u => e₁ * μ u + e₂ * ν u) z - conj (wU (fun u => e₁ * μ u + e₂ * ν u) z)) ^ 2) 0) =
      fun e₁ => dzbar (fun e₂ => F (e₁, e₂)) 0 := by
    subst hF; rfl
  rw [hL, hP, hlam 1, hlam (-1), hlam I, hlam (-I), r65_resolvent_polar hμ hν hz]
  ring

/-- **Remark 6.5** (TT:2668–2672). By polarization,
`L_μ L_{ν̄} ρ = ∂²/∂ε₁∂ε̄₂|_{ε₁=ε₂=0} ρ^{ε₁μ + ε₂ν} = ρ G(μν̄)`. -/
theorem remark_6_5 {μ ν φ ψ : ℂ → ℂ} (hμ : IsHarmonicU μ φ) (hν : IsHarmonicU ν ψ) {z : ℂ} (hz : z ∈ upperHalf) :
    dz (fun e₁ => dzbar (fun e₂ => -4 * (‖dz (wU fun u => e₁ * μ u + e₂ * ν u) z‖ ^ 2 : ℝ) /
        (wU (fun u => e₁ * μ u + e₂ * ν u) z - conj (wU (fun u => e₁ * μ u + e₂ * ν u) z)) ^ 2) 0) 0 =
      rhoU z * resolventOpU (fun u => μ u * conj (ν u)) z :=
  r65_remark_6_5 hμ hν hz

end TakhtajanTeo
