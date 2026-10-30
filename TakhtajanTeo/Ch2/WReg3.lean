import TakhtajanTeo.Ch1.WRegFoundation
import TakhtajanTeo.Ch2.S4ModelAVariation

/-!
# W-REG3: the W-REG chain for affine three-coefficient families (Program G, interface by 下属6)

Target lane for the joint `(t, z)` regularity of `w_{a + t m}` on `𝔻*`, which `s35_wgside` (G35O/SUBIFACE f21f2877)
consumes:
- obligation (a) and clauses 2–5: for `γ_t = w_{λ_t} = w_{a+tm} ∘ w_a⁻¹` (`grp_wAS_mul`, no normalizing factor),
  `∂_t ∂_z^k γ_t = ∂_z^k ∂_t γ_t` for `k ≤ 3` at `t = 0`, and `C³` of `ψ = ∂_t γ_t|₀`;
- obligation (b): the `C³` regularity of `V_t = 𝗀_t ∘ γ_t ∘ 𝗀⁻¹` on `𝗀(𝔻*)`, which uses the joint continuity of
  `γ_t⁻¹` (W3-4).

`extA (a + t m) = m₀ + t m₁ + t̄ m₂` has three independent coefficients. The installed chain
(`wr_ns2_z_regular`, `wr_ns2_holo`, `wr_ns2_cont`, `wr_ns2_inv_cont`, `wr_local_jacobian_pos`) covers only the linear
two-coefficient families `P.1 m₁ + P.2 m₂`. Statements W3-1…W3-5 below are those five with the fixed base
coefficient `m₀` added. W3-0 is the coefficient decomposition, the analogue of `s4ma_coefficients`.

The consumer (下属6) evaluates at `P = (t, t̄)` and gets the mixed derivatives from holomorphy in each coordinate of
`P` together with the joint continuity of the `z`-jets up to order 3, through a Cauchy integral in `P`, as
`s4hv_wA_holomorphic_variation` does. Joint `C⁴` is therefore not requested.

Prefix `wr3_`. No new definitions.
-/

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal ComplexConjugate Classical Real

noncomputable section

namespace TakhtajanTeo

open LiZhongQC

/-- Additivity of the Model A extension, a.e. -/
theorem wr3_extA_add (a b : LinfStar) : extA (a + b) =ᵐ[volume] fun z => extA a z + extA b z := by
  have hms : MeasurableSet unitDiscExterior := (isOpen_lt continuous_const continuous_norm).measurableSet
  have hs := Lp.coeFn_add a b
  have hP : ∀ᵐ z : ℂ, z ∈ unitDiscExterior → (a + b) z = a z + b z := by
    have := (ae_restrict_iff' hms).1 hs
    filter_upwards [this] with z hz hzm
    simpa using hz hzm
  have hP' := ae_refl hP
  have hne : ∀ᵐ z : ℂ, z ≠ 0 := compl_mem_ae_iff.2 (measure_singleton 0)
  filter_upwards [hP, hP', hne] with z h1 h2 hz0
  unfold extA
  by_cases hz1 : 1 < ‖z‖
  · rw [if_pos hz1, if_pos hz1, if_pos hz1, h1 hz1]
  · rw [if_neg hz1, if_neg hz1, if_neg hz1]
    by_cases hz2 : ‖z‖ < 1
    · rw [if_pos hz2, if_pos hz2, if_pos hz2]
      have hr : refl z ∈ unitDiscExterior := by
        show 1 < ‖refl z‖
        rw [refl, norm_inv, Complex.norm_conj]
        exact one_lt_inv_iff₀.mpr ⟨norm_pos_iff.mpr hz0, hz2⟩
      rw [h2 hr, map_add]
      ring
    · rw [if_neg hz2, if_neg hz2, if_neg hz2]
      ring

/-- **W3-0** (coefficients). For harmonic `a`, `μ`, the Model A coefficient of `a + e μ` splits as
`m₀ + e m₁ + ē m₂`: `m₀`, `m₁` are smooth on `𝔻*` with sup bounds `‖a‖`, `‖μ‖`, and `m₂ = 𝟙_𝔻 · extA μ` vanishes
on `𝔻*`. -/
theorem wr3_coeffs {a μ : LinfStar} (ha : a ∈ harmonicBeltrami) (hμ : μ ∈ harmonicBeltrami) :
    ∃ m₀ m₁ : ℂ → ℂ, IsBeltramiCoeff m₀ univ ‖a‖ ∧ IsBeltramiCoeff m₁ univ ‖μ‖ ∧
      ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) m₀ unitDiscExterior ∧
      ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) m₁ unitDiscExterior ∧
      ∀ e : ℂ, extA (a + e • μ) =ᵐ[volume]
        (fun u => m₀ u + e * m₁ u + conj e * unitDisc.indicator (extA μ) u) := by
  obtain ⟨g, hg, hga⟩ := wr_harm_rep ha
  obtain ⟨m₁, hm₁BC, hm₁s, -, hm₁e⟩ := Ch2.s4ma_coefficients hμ
  have hE : MeasurableSet unitDiscExterior := wp_exterior_isOpen.measurableSet
  obtain ⟨m₀, hm₀d⟩ : ∃ m₀ : ℂ → ℂ, m₀ = fun u => if 1 < ‖u‖ then g u else extA a u := ⟨_, rfl⟩
  have hm₀e : m₀ =ᵐ[volume] extA a := by
    filter_upwards [(ae_restrict_iff' hE).1 hga] with u hu
    rw [hm₀d]
    by_cases h : 1 < ‖u‖
    · simp only [if_pos h]
      rw [extA_eq_on_exterior a h, hu h]
    · simp only [if_neg h]
  refine ⟨m₀, m₁, wr_isBC_congr (extA_isBeltramiCoeff a) hm₀e.symm, hm₁BC, ?_, hm₁s, fun e => ?_⟩
  · refine hg.congr fun u hu => ?_
    rw [hm₀d]
    exact if_pos hu
  · filter_upwards [wr3_extA_add a (e • μ), hm₁e e, hm₀e] with u h1 h2 h3
    rw [h1, h2, h3]
    ring

/-! ### Affine three-coefficient families: holomorphy, continuity, inverse (下属3) -/

/-- Joint complex differentiability in `P` of the affine family `m₀ + P.1 m₁ + P.2 m₂` at a point where the
coefficient is bounded by `k < 1` (the general first variation `qcv_plane_hasFDerivAt` at the base `P₀`). -/
theorem wr3_diffAt {m₀ m₁ m₂ : ℂ → ℂ} {k₁ k₂ : ℝ} (hm₁ : IsBeltramiCoeff m₁ univ k₁)
    (hm₂ : IsBeltramiCoeff m₂ univ k₂) {P₀ : ℂ × ℂ} {k : ℝ} (hk : k < 1)
    (hP₀ : IsBeltramiCoeff (fun u => m₀ u + P₀.1 * m₁ u + P₀.2 * m₂ u) univ k) (z : ℂ) :
    DifferentiableAt ℂ (fun p : ℂ × ℂ => normalizedSolution (fun u => m₀ u + p.1 * m₁ u + p.2 * m₂ u) z) P₀ := by
  obtain ⟨h0, hk0, hk1⟩ := wr_coeff_nonneg hk hP₀
  obtain ⟨f₀, hf₀, -, -⟩ := thm13_7_normalized_existence hk0 hk1 h0
  obtain ⟨L, -, hL⟩ := QCV.qcv_plane_hasFDerivAt hk0 hk1 h0 hf₀
    (fun (v : ℂ × ℂ) u => v.1 * m₁ u + v.2 * m₂ u) (by positivity : (0 : ℝ) ≤ |k₁| + |k₂|)
    (wr_coeff_lin hm₁ hm₂)
    (fun c v₁ v₂ => Eventually.of_forall fun u => by
      simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
      ring) z
  have hT : HasFDerivAt (fun p : ℂ × ℂ => p - P₀) (ContinuousLinearMap.id ℂ (ℂ × ℂ)) P₀ :=
    (hasFDerivAt_id P₀).sub_const P₀
  have hL' : HasFDerivAt (fun v : ℂ × ℂ => normalizedSolution
      (fun u => (m₀ u + P₀.1 * m₁ u + P₀.2 * m₂ u) + (v.1 * m₁ u + v.2 * m₂ u)) z) L (P₀ - P₀) := by
    rw [sub_self]
    exact hL
  refine (HasFDerivAt.comp (f := fun p : ℂ × ℂ => p - P₀) P₀ hL' hT).differentiableAt.congr_of_eventuallyEq (Eventually.of_forall fun p => ?_)
  exact congrArg (fun f => normalizedSolution f z) (funext fun u => by
    simp only [Prod.fst_sub, Prod.snd_sub]
    ring)

/-- Locally uniform bound `k < 1` near a parameter where the affine coefficient is bounded by `k₀ < 1`. -/
theorem wr3_loc_unif {m₀ m₁ m₂ : ℂ → ℂ} {k₀' k₁ k₂ : ℝ} (hm₀ : IsBeltramiCoeff m₀ univ k₀')
    (hm₁ : IsBeltramiCoeff m₁ univ k₁) (hm₂ : IsBeltramiCoeff m₂ univ k₂) {P₀ : ℂ × ℂ} {k₀ : ℝ} (hk₀ : k₀ < 1)
    (h₀ : IsBeltramiCoeff (fun u => m₀ u + P₀.1 * m₁ u + P₀.2 * m₂ u) univ k₀) :
    ∃ δ > 0, ∃ k : ℝ, 0 ≤ k ∧ k < 1 ∧ ∀ P : ℂ × ℂ, dist P P₀ < δ →
      IsBeltramiCoeff (fun u => m₀ u + P.1 * m₁ u + P.2 * m₂ u) univ k := by
  obtain ⟨h0, hk0, hk1⟩ := wr_coeff_nonneg hk₀ h₀
  have hM : 0 < |k₁| + |k₂| + 1 := by positivity
  have hδ : 0 < (1 - max k₀ 0) / (2 * (|k₁| + |k₂| + 1)) := div_pos (by linarith) (by positivity)
  obtain ⟨δ, hδdef⟩ : ∃ δ : ℝ, δ = (1 - max k₀ 0) / (2 * (|k₁| + |k₂| + 1)) := ⟨_, rfl⟩
  rw [← hδdef] at hδ
  have hMδ : (|k₁| + |k₂| + 1) * δ = (1 - max k₀ 0) / 2 := by
    rw [hδdef, mul_div_assoc', mul_comm (2 : ℝ), mul_div_mul_left _ _ hM.ne']
  refine ⟨δ, hδ, max k₀ 0 + (|k₁| + |k₂|) * δ, add_nonneg hk0 (mul_nonneg (by positivity) hδ.le), ?_,
    fun P hP => ?_⟩
  · have : (|k₁| + |k₂|) * δ ≤ (|k₁| + |k₂| + 1) * δ := mul_le_mul_of_nonneg_right (by linarith) hδ.le
    linarith
  · have hT := wr_coeff_lin hm₁ hm₂ (P - P₀)
    refine ⟨(hm₀.1.add (hm₁.1.const_mul P.1)).add (hm₂.1.const_mul P.2), ?_⟩
    filter_upwards [h0.2, hT.2] with u h1 h2
    have he : m₀ u + P.1 * m₁ u + P.2 * m₂ u =
        (m₀ u + P₀.1 * m₁ u + P₀.2 * m₂ u) + ((P - P₀).1 * m₁ u + (P - P₀).2 * m₂ u) := by
      simp only [Prod.fst_sub, Prod.snd_sub]; ring
    rw [he]
    have hn : ‖P - P₀‖ ≤ δ := by rw [← dist_eq_norm]; exact hP.le
    calc _ ≤ _ := norm_add_le _ _
      _ ≤ max k₀ 0 + (|k₁| + |k₂|) * δ :=
          add_le_add h1 (h2.trans (mul_le_mul_of_nonneg_left hn (by positivity)))

/-- Locally uniform convergence of the normalized solutions of the affine family along `Pₙ → P₀ ∈ W`. -/
theorem wr3_luc {m₀ m₁ m₂ : ℂ → ℂ} {k₀' k₁ k₂ : ℝ} (hm₀ : IsBeltramiCoeff m₀ univ k₀')
    (hm₁ : IsBeltramiCoeff m₁ univ k₁) (hm₂ : IsBeltramiCoeff m₂ univ k₂) {W : Set (ℂ × ℂ)}
    (hWk : ∀ P ∈ W, ∃ k < 1, IsBeltramiCoeff (fun u => m₀ u + P.1 * m₁ u + P.2 * m₂ u) univ k)
    {P₀ : ℂ × ℂ} (hP₀ : P₀ ∈ W) {Ps : ℕ → ℂ × ℂ} (hlim : Tendsto Ps atTop (𝓝 P₀)) :
    TendstoLocallyUniformly
      (fun n => normalizedSolution (fun u => m₀ u + (Ps n).1 * m₁ u + (Ps n).2 * m₂ u))
      (normalizedSolution (fun u => m₀ u + P₀.1 * m₁ u + P₀.2 * m₂ u)) atTop := by
  obtain ⟨k₀, hk₀, h₀⟩ := hWk _ hP₀
  obtain ⟨δ, hδ, k, hk0, hk1, hP⟩ := wr3_loc_unif hm₀ hm₁ hm₂ hk₀ h₀
  have hpt : ∀ z, Tendsto (fun n => normalizedSolution (fun u => m₀ u + (Ps n).1 * m₁ u + (Ps n).2 * m₂ u) z)
      atTop (𝓝 (normalizedSolution (fun u => m₀ u + P₀.1 * m₁ u + P₀.2 * m₂ u) z)) := fun z =>
    (wr3_diffAt hm₁ hm₂ hk₀ h₀ z).continuousAt.tendsto.comp hlim
  have hqc : ∀ᶠ n in atTop, IsKQCNormalizedPlane
      (normalizedSolution (fun u => m₀ u + (Ps n).1 * m₁ u + (Ps n).2 * m₂ u)) ((1 + k) / (1 - k)) := by
    filter_upwards [hlim.eventually (ball_mem_nhds P₀ hδ)] with n hn
    exact wr_ns_qc hk0 hk1 (hP _ hn) le_rfl
  rw [tendstoLocallyUniformly_iff_forall_isCompact]
  intro S hS
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  by_contra hcon
  rw [not_eventually] at hcon
  obtain ⟨N, hN⟩ := eventually_atTop.1 hqc
  obtain ⟨φ, hφ, hbad⟩ := extraction_of_frequently_atTop (hcon.and_eventually (eventually_ge_atTop N))
  have hK' : ∀ n, IsKQCNormalizedPlane
      (normalizedSolution (fun u => m₀ u + (Ps (φ n)).1 * m₁ u + (Ps (φ n)).2 * m₂ u)) ((1 + k) / (1 - k)) :=
    fun n => hN _ (hbad n).2
  obtain ⟨ψ, hψ, G, hG⟩ := UniversalTeichmuller.ut2_nf_extract hK'
  have hGeq : G = normalizedSolution (fun u => m₀ u + P₀.1 * m₁ u + P₀.2 * m₂ u) := by
    funext w
    exact tendsto_nhds_unique
      ((tendstoLocallyUniformly_iff_forall_isCompact.1 hG {w} isCompact_singleton).tendsto_at (mem_singleton w))
      ((hpt w).comp (hφ.tendsto_atTop.comp hψ.tendsto_atTop))
  rw [hGeq] at hG
  have hU := Metric.tendstoUniformlyOn_iff.1 (tendstoLocallyUniformly_iff_forall_isCompact.1 hG S hS) ε hε
  obtain ⟨n, hn⟩ := hU.exists
  exact (hbad (ψ n)).1 hn

/-! ### Smooth compactly supported affine families (下属3) -/

/-- `ν₀ + P.1 ν₁ + P.2 ν₂` as a finite combination with continuous real coefficients in `P` and `C_c^∞` functions
(`ν₀` with coefficient `1`, the rest as in `wr_s2_nu`). -/
theorem wr3_nu (ν₀ ν₁ ν₂ : ℂ → ℂ) (P : ℂ × ℂ) (z : ℂ) :
    ν₀ z + P.1 * ν₁ z + P.2 * ν₂ z = ∑ b : Unit ⊕ (Bool × Bool),
      ((Sum.elim (fun _ => (1 : ℝ)) (fun b : Bool × Bool => cond b.2 (cond b.1 P.1 P.2).re (cond b.1 P.1 P.2).im) b :
        ℝ) : ℂ) * Sum.elim (fun _ => ν₀ z) (fun b : Bool × Bool => cond b.2 1 I * cond b.1 (ν₁ z) (ν₂ z)) b := by
  rw [Fintype.sum_sum_type, add_assoc, wr_s2_nu ν₁ ν₂ P z]
  simp only [Finset.univ_unique, Finset.sum_singleton, Sum.elim_inl, Sum.elim_inr, Complex.ofReal_one, one_mul]

/-- The Neumann term `s P n` of the affine family is a finite combination `Σ aᵢ(P) cᵢ` with continuous real `aᵢ`
and `C_c^∞` `cᵢ` (cf. `wr_s2_rep`). -/
theorem wr3_s_rep {ν₀ ν₁ ν₂ : ℂ → ℂ} (h₀ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ν₀) (hc₀ : HasCompactSupport ν₀)
    (h₁ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ν₁) (hc₁ : HasCompactSupport ν₁)
    (h₂ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ν₂) (hc₂ : HasCompactSupport ν₂) {s : ℂ × ℂ → ℕ → ℂ → ℂ}
    (hs0 : ∀ P, s P 0 = fun z => ν₀ z + P.1 * ν₁ z + P.2 * ν₂ z)
    (hs : ∀ P n, s P (n + 1) = fun z => (ν₀ z + P.1 * ν₁ z + P.2 * ν₂ z) * hilbertHSmooth (s P n) z) (n : ℕ) :
    ∃ (ι : Type) (_ : Fintype ι) (a : ι → ℂ × ℂ → ℝ) (c : ι → ℂ → ℂ), (∀ i, Continuous (a i)) ∧
      (∀ i, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (c i) ∧ HasCompactSupport (c i)) ∧
      ∀ P, s P n = fun z => ∑ i, (a i P : ℂ) * c i z := by
  obtain ⟨A, hA⟩ : ∃ A : Unit ⊕ (Bool × Bool) → ℂ × ℂ → ℝ, A = fun b P =>
      Sum.elim (fun _ => (1 : ℝ)) (fun b : Bool × Bool => cond b.2 (cond b.1 P.1 P.2).re (cond b.1 P.1 P.2).im) b :=
    ⟨_, rfl⟩
  obtain ⟨C, hC⟩ : ∃ C : Unit ⊕ (Bool × Bool) → ℂ → ℂ, C = fun b z =>
      Sum.elim (fun _ => ν₀ z) (fun b : Bool × Bool => cond b.2 1 I * cond b.1 (ν₁ z) (ν₂ z)) b := ⟨_, rfl⟩
  have hnu : ∀ P z, ν₀ z + P.1 * ν₁ z + P.2 * ν₂ z = ∑ b, (A b P : ℂ) * C b z := by
    intro P z
    rw [hA, hC]
    exact wr3_nu ν₀ ν₁ ν₂ P z
  have he : ∀ b, Continuous (A b) := by
    intro b
    rw [hA]
    rcases b with u | ⟨b1, b2⟩
    · exact continuous_const
    · cases b1 <;> cases b2
      · exact Complex.continuous_im.comp continuous_snd
      · exact Complex.continuous_re.comp continuous_snd
      · exact Complex.continuous_im.comp continuous_fst
      · exact Complex.continuous_re.comp continuous_fst
  have hd : ∀ b, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (C b) ∧ HasCompactSupport (C b) := by
    intro b
    rw [hC]
    rcases b with u | ⟨b1, b2⟩
    · exact ⟨h₀, hc₀⟩
    · cases b1
      · exact ⟨contDiff_const.mul h₂, hc₂.mul_left⟩
      · exact ⟨contDiff_const.mul h₁, hc₁.mul_left⟩
  induction n with
  | zero =>
    refine ⟨Unit ⊕ (Bool × Bool), inferInstance, A, C, he, hd, fun P => ?_⟩
    rw [hs0 P]
    funext z
    exact hnu P z
  | succ n ih =>
    obtain ⟨ι, hι, a, c, ha, hc, hrep⟩ := ih
    refine ⟨(Unit ⊕ (Bool × Bool)) × ι, inferInstance, fun bi P => A bi.1 P * a bi.2 P,
      fun bi z => C bi.1 z * hilbertHSmooth (c bi.2) z, ?_, ?_, ?_⟩
    · rintro ⟨b, i⟩
      exact (he b).mul (ha i)
    · rintro ⟨b, i⟩
      exact wr_mul_hS_smooth (hd b).1 (hd b).2 (hc i).1 (hc i).2
    · intro P
      rw [hs P n, hrep P, (wr_s2_hS_sum Finset.univ (fun i => (a i P : ℂ)) c hc).2.2]
      funext z
      rw [hnu P z, Finset.sum_mul_sum, ← Finset.sum_product', Finset.univ_product_univ]
      apply Finset.sum_congr rfl
      rintro ⟨b, i⟩ _
      push_cast
      ring

/-- Continuity of each Neumann term of the affine family in the parameter (cf. `wr_iter_term_cont`). -/
theorem wr3_iter_term_cont {ν₀ ν₁ ν₂ : ℂ → ℂ} (h₀ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ν₀) (hc₀ : HasCompactSupport ν₀)
    (h₁ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ν₁) (hc₁ : HasCompactSupport ν₁)
    (h₂ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ν₂) (hc₂ : HasCompactSupport ν₂) {s : ℂ × ℂ → ℕ → ℂ → ℂ}
    (hs0 : ∀ P, s P 0 = fun z => ν₀ z + P.1 * ν₁ z + P.2 * ν₂ z)
    (hs : ∀ P n, s P (n + 1) = fun z => (ν₀ z + P.1 * ν₁ z + P.2 * ν₂ z) * hilbertHSmooth (s P n) z) (n j : ℕ) :
    Continuous (fun q : (ℂ × ℂ) × ℂ => iteratedFDeriv ℝ j (cauchyT (s q.1 n)) q.2) := by
  obtain ⟨ι, hι, a, c, ha, hc, hrep⟩ := wr3_s_rep h₀ hc₀ h₁ hc₁ h₂ hc₂ hs0 hs n
  have hT : ∀ i, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (cauchyT (c i)) := fun i =>
    wr_cauchyT_contDiff_top (hc i).1 (hc i).2
  have hTj : ∀ i, ContDiff ℝ j (cauchyT (c i)) := fun i => (hT i).of_le (by exact_mod_cast le_top)
  have key : ∀ q : (ℂ × ℂ) × ℂ, iteratedFDeriv ℝ j (cauchyT (s q.1 n)) q.2 =
      ∑ i, a i q.1 • iteratedFDeriv ℝ j (cauchyT (c i)) q.2 := by
    intro q
    rw [hrep q.1, wr_s2_cauchyT_sum Finset.univ (fun i => (a i q.1 : ℂ)) c hc]
    have hfun : (fun z => ∑ i, (a i q.1 : ℂ) * cauchyT (c i) z) = ∑ i, fun z => a i q.1 • cauchyT (c i) z := by
      funext z
      rw [Finset.sum_apply]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Complex.real_smul]
    rw [hfun, iteratedFDeriv_sum_apply fun i _ => ((hTj i).const_smul (a i q.1)).contDiffAt]
    refine Finset.sum_congr rfl fun i _ => ?_
    exact iteratedFDeriv_const_smul_apply' (hTj i).contDiffAt
  rw [show (fun q : (ℂ × ℂ) × ℂ => iteratedFDeriv ℝ j (cauchyT (s q.1 n)) q.2) =
    fun q => ∑ i, a i q.1 • iteratedFDeriv ℝ j (cauchyT (c i)) q.2 from funext key]
  refine continuous_finsetSum _ fun i _ => ((ha i).comp continuous_fst).smul ?_
  exact ((hT i).continuous_iteratedFDeriv (by exact_mod_cast le_top)).comp continuous_snd

/-- Local `C³` bounds for the Neumann series of the affine family (cf. `wr_A3_local`). -/
theorem wr3_A3_local {ν₀ ν₁ ν₂ : ℂ → ℂ} (h₀ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ν₀) (hc₀ : HasCompactSupport ν₀)
    (h₁ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ν₁) (hc₁ : HasCompactSupport ν₁)
    (h₂ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ν₂) (hc₂ : HasCompactSupport ν₂) {W : Set (ℂ × ℂ)} (hW : IsOpen W)
    (hWk : ∀ P ∈ W, ∃ k < 1, ∀ z, ‖ν₀ z + P.1 * ν₁ z + P.2 * ν₂ z‖ ≤ k) {s : ℂ × ℂ → ℕ → ℂ → ℂ}
    (hs0 : ∀ P, s P 0 = fun z => ν₀ z + P.1 * ν₁ z + P.2 * ν₂ z)
    (hs : ∀ P n, s P (n + 1) = fun z => (ν₀ z + P.1 * ν₁ z + P.2 * ν₂ z) * hilbertHSmooth (s P n) z)
    {P₀ : ℂ × ℂ} (hP₀ : P₀ ∈ W) :
    ∃ δ > 0, ball P₀ δ ⊆ W ∧ (∀ P ∈ ball P₀ δ, ContDiff ℝ 3 (fun z => ∑' n, cauchyT (s P n) z)) ∧
      ∀ j ≤ 3, ContinuousOn (fun q : (ℂ × ℂ) × ℂ => iteratedFDeriv ℝ j (fun z => ∑' n, cauchyT (s q.1 n) z) q.2)
        (ball P₀ δ ×ˢ univ) := by
  have S1 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ν₁ ∧ HasCompactSupport ν₁ := ⟨h₁, hc₁⟩
  have S2 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ν₂ ∧ HasCompactSupport ν₂ := ⟨h₂, hc₂⟩
  have SP : ∀ P : ℂ × ℂ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z => ν₀ z + P.1 * ν₁ z + P.2 * ν₂ z) ∧
      HasCompactSupport (fun z => ν₀ z + P.1 * ν₁ z + P.2 * ν₂ z) := by
    intro P
    have e : (fun z => ν₀ z + P.1 * ν₁ z + P.2 * ν₂ z) = fun z => ν₀ z + (P.1 * ν₁ z + P.2 * ν₂ z) :=
      funext fun z => add_assoc _ _ _
    rw [e]
    exact ⟨h₀.add (wr_lin_sc h₁ hc₁ h₂ hc₂ P.1 P.2).1, hc₀.add (wr_lin_sc h₁ hc₁ h₂ hc₂ P.1 P.2).2⟩
  have hsc : ∀ P n, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (s P n) ∧ HasCompactSupport (s P n) := fun P n =>
    wr_iter_smooth (SP P).1 (SP P).2 (hs0 P) (hs P) n
  obtain ⟨k₀, hk₀1, hk₀⟩ := hWk P₀ hP₀
  have hk₀0 : 0 ≤ k₀ := (norm_nonneg _).trans (hk₀ 0)
  obtain ⟨M₁, hM₁0, hM₁⟩ := wr_sc_bound S1
  obtain ⟨M₂, hM₂0, hM₂⟩ := wr_sc_bound S2
  obtain ⟨δ₁, hδ₁, hball⟩ := Metric.isOpen_iff.1 hW P₀ hP₀
  obtain ⟨δ, hδ, hδ1, hδ2⟩ : ∃ δ : ℝ, 0 < δ ∧ δ ≤ δ₁ ∧ δ * (M₁ + M₂ + 1) ≤ (1 - k₀) / 2 := by
    refine ⟨min δ₁ ((1 - k₀) / (2 * (M₁ + M₂ + 1))), lt_min hδ₁ (div_pos (by linarith) (by positivity)),
      min_le_left _ _, ?_⟩
    have h := min_le_right δ₁ ((1 - k₀) / (2 * (M₁ + M₂ + 1)))
    rw [le_div_iff₀ (by positivity)] at h
    linarith
  obtain ⟨k', hk'def⟩ : ∃ k' : ℝ, k' = (k₀ + 1) / 2 := ⟨_, rfl⟩
  have hk'1 : k' < 1 := by rw [hk'def]; linarith
  have hk'0 : 0 ≤ k' := by rw [hk'def]; positivity
  have hcomp : ∀ P ∈ ball P₀ δ, ‖P.1 - P₀.1‖ < δ ∧ ‖P.2 - P₀.2‖ < δ := by
    intro P hP
    rw [mem_ball, Prod.dist_eq] at hP
    have h1 : dist P.1 P₀.1 < δ := (le_max_left _ _).trans_lt hP
    have h2 : dist P.2 P₀.2 < δ := (le_max_right _ _).trans_lt hP
    rw [dist_eq_norm] at h1 h2
    exact ⟨h1, h2⟩
  have hνP : ∀ P ∈ ball P₀ δ, ∀ z, ‖ν₀ z + P.1 * ν₁ z + P.2 * ν₂ z‖ ≤ k' := by
    intro P hP z
    obtain ⟨h1, h2⟩ := hcomp P hP
    have e : ν₀ z + P.1 * ν₁ z + P.2 * ν₂ z =
        (ν₀ z + P₀.1 * ν₁ z + P₀.2 * ν₂ z) + ((P.1 - P₀.1) * ν₁ z + (P.2 - P₀.2) * ν₂ z) := by ring
    rw [e]
    have t1 := norm_add_le (ν₀ z + P₀.1 * ν₁ z + P₀.2 * ν₂ z) ((P.1 - P₀.1) * ν₁ z + (P.2 - P₀.2) * ν₂ z)
    have t2 := norm_add_le ((P.1 - P₀.1) * ν₁ z) ((P.2 - P₀.2) * ν₂ z)
    rw [norm_mul, norm_mul] at t2
    have t3 : ‖P.1 - P₀.1‖ * ‖ν₁ z‖ ≤ δ * M₁ := mul_le_mul h1.le (hM₁ z) (norm_nonneg _) hδ.le
    have t4 : ‖P.2 - P₀.2‖ * ‖ν₂ z‖ ≤ δ * M₂ := mul_le_mul h2.le (hM₂ z) (norm_nonneg _) hδ.le
    have t5 := hk₀ z
    have t6 : δ * M₁ + δ * M₂ ≤ δ * (M₁ + M₂ + 1) := by nlinarith
    rw [hk'def]
    linarith
  obtain ⟨R, hRdef⟩ : ∃ R : ℝ, R = ‖P₀.1‖ + ‖P₀.2‖ + δ := ⟨_, rfl⟩
  have hR0 : 0 ≤ R := by rw [hRdef]; positivity
  have hR : ∀ P ∈ ball P₀ δ, ‖P.1‖ ≤ R ∧ ‖P.2‖ ≤ R := by
    intro P hP
    obtain ⟨h1, h2⟩ := hcomp P hP
    have e1 : P.1 = P₀.1 + (P.1 - P₀.1) := by ring
    have e2 : P.2 = P₀.2 + (P.2 - P₀.2) := by ring
    have n1 := norm_add_le P₀.1 (P.1 - P₀.1)
    have n2 := norm_add_le P₀.2 (P.2 - P₀.2)
    rw [← e1] at n1
    rw [← e2] at n2
    have := norm_nonneg P₀.1
    have := norm_nonneg P₀.2
    rw [hRdef]
    constructor <;> linarith
  obtain ⟨p, hp2, -, hkp⟩ := eq12_1_exists_exponent hk'1 (p₁ := 3) (by norm_num)
  have hp1 : 1 < p := by linarith
  have hΛ := hilbertNorm_nonneg p
  obtain ⟨ρ, hρdef⟩ : ∃ ρ : ℝ, ρ = (k' * hilbertNorm p + 1) / 2 := ⟨_, rfl⟩
  have hρ : k' * hilbertNorm p < ρ := by rw [hρdef]; linarith
  have hρ1 : ρ < 1 := by rw [hρdef]; linarith
  have hρ0 : 0 ≤ ρ := (mul_nonneg hk'0 hΛ).trans hρ.le
  obtain ⟨β₀, hβ₀0, hβ₀⟩ := wr_word_bounds h₀ hc₀ p
  obtain ⟨β₁, hβ₁0, hβ₁⟩ := wr_word_bounds h₁ hc₁ p
  obtain ⟨β₂, hβ₂0, hβ₂⟩ := wr_word_bounds h₂ hc₂ p
  obtain ⟨B, hBdef⟩ : ∃ B : ℝ, B = 1 * (β₀ + R * (β₁ + β₂)) := ⟨_, rfl⟩
  have hB0 : 0 ≤ B := by rw [hBdef]; positivity
  obtain ⟨Γ, hΓdef⟩ : ∃ Γ : ℝ, Γ = 7 * B * hilbertNorm p / (ρ - k' * hilbertNorm p) := ⟨_, rfl⟩
  have hΓ0 : 0 ≤ Γ := by rw [hΓdef]; exact div_nonneg (by positivity) (by linarith)
  obtain ⟨E, hEdef⟩ : ∃ E : ℝ, E = B * (1 + Γ) * (1 + Γ) * (1 + Γ) := ⟨_, rfl⟩
  have hE0 : 0 ≤ E := by rw [hEdef]; positivity
  have hwP : ∀ P ∈ ball P₀ δ, ∀ a b e : ℂ, ‖a‖ ≤ 1 → ‖b‖ ≤ 1 → ‖e‖ ≤ 1 →
      (∀ z, ‖fderiv ℝ (fun z => ν₀ z + P.1 * ν₁ z + P.2 * ν₂ z) z a‖ ≤ B ∧
        ‖fderiv ℝ (fun z => fderiv ℝ (fun z => ν₀ z + P.1 * ν₁ z + P.2 * ν₂ z) z b) z a‖ ≤ B ∧
        ‖fderiv ℝ (fun z => fderiv ℝ (fun z => fderiv ℝ (fun z => ν₀ z + P.1 * ν₁ z + P.2 * ν₂ z) z e) z b) z a‖ ≤ B) ∧
      (eLpNorm (fun z => ν₀ z + P.1 * ν₁ z + P.2 * ν₂ z) (ENNReal.ofReal p)).toReal ≤ B ∧
      (eLpNorm (fun z => fderiv ℝ (fun z => ν₀ z + P.1 * ν₁ z + P.2 * ν₂ z) z a) (ENNReal.ofReal p)).toReal ≤ B ∧
      (eLpNorm (fun z => fderiv ℝ (fun z => fderiv ℝ (fun z => ν₀ z + P.1 * ν₁ z + P.2 * ν₂ z) z b) z a)
        (ENNReal.ofReal p)).toReal ≤ B ∧
      (eLpNorm (fun z => fderiv ℝ (fun z => fderiv ℝ (fun z => fderiv ℝ (fun z => ν₀ z + P.1 * ν₁ z + P.2 * ν₂ z) z e) z b) z a)
        (ENNReal.ofReal p)).toReal ≤ B := by
    intro P hP
    have hX := wr_lin_bounds h₁ hc₁ h₂ hc₂ hp1.le hβ₁ hβ₂ (hR P hP).1 (hR P hP).2
    have SX := wr_lin_sc h₁ hc₁ h₂ hc₂ P.1 P.2
    have h := wr_lin_bounds h₀ hc₀ SX.1 SX.2 hp1.le hβ₀ hX (c := 1) (d := 1) (le_of_eq norm_one)
      (le_of_eq norm_one)
    have e : (fun z => 1 * ν₀ z + 1 * (P.1 * ν₁ z + P.2 * ν₂ z)) = fun z => ν₀ z + P.1 * ν₁ z + P.2 * ν₂ z := by
      funext z
      ring
    simp only [e] at h
    rw [hBdef]
    exact h
  have hΓ : 7 * B * hilbertNorm p / (ρ - k' * hilbertNorm p) ≤ Γ := hΓdef.ge
  have hlev : ∀ P ∈ ball P₀ δ, ∀ a b c : ℂ, ‖a‖ ≤ 1 → ‖b‖ ≤ 1 → ‖c‖ ≤ 1 → ∀ n,
      (eLpNorm (s P n) (ENNReal.ofReal p)).toReal ≤ E * ρ ^ n ∧
      (eLpNorm (fun z => fderiv ℝ (s P n) z a) (ENNReal.ofReal p)).toReal ≤ E * ρ ^ n ∧
      (eLpNorm (fun z => fderiv ℝ (fun z => fderiv ℝ (s P n) z b) z a) (ENNReal.ofReal p)).toReal ≤ E * ρ ^ n ∧
      (eLpNorm (fun z => fderiv ℝ (fun z => fderiv ℝ (fun z => fderiv ℝ (s P n) z c) z b) z a)
        (ENNReal.ofReal p)).toReal ≤ E * ρ ^ n := by
    intro P hP a b c ha hb hc n
    rw [hEdef]
    exact wr_all_levels hp1 (SP P).1 (SP P).2 hk'0 (hνP P hP) hρ hB0 hB0 hΓ hΓ0 (hwP P hP) (hs0 P) (hs P)
      ha hb hc n
  -- supports
  have hK : IsCompact (tsupport ν₀ ∪ tsupport ν₁ ∪ tsupport ν₂) := (hc₀.isCompact.union hc₁.isCompact).union hc₂.isCompact
  obtain ⟨r, hr⟩ := hK.isBounded.subset_closedBall (0 : ℂ)
  obtain ⟨R₀, hR₀def⟩ : ∃ R₀ : ℝ, R₀ = max r 1 := ⟨_, rfl⟩
  have hR₀ : 0 < R₀ := by rw [hR₀def]; exact lt_of_lt_of_le one_pos (le_max_right _ _)
  have hU : IsOpen (tsupport ν₀ ∪ tsupport ν₁ ∪ tsupport ν₂)ᶜ :=
    (((isClosed_tsupport _).union (isClosed_tsupport _)).union (isClosed_tsupport _)).isOpen_compl
  have hout : ∀ y : ℂ, R₀ < ‖y‖ → y ∈ (tsupport ν₀ ∪ tsupport ν₁ ∪ tsupport ν₂)ᶜ := by
    intro y hy hyK
    have h := hr hyK
    rw [mem_closedBall_zero_iff] at h
    have : r ≤ R₀ := by rw [hR₀def]; exact le_max_left _ _
    linarith
  have hνz : ∀ P : ℂ × ℂ, ∀ y ∈ (tsupport ν₀ ∪ tsupport ν₁ ∪ tsupport ν₂)ᶜ, ν₀ y + P.1 * ν₁ y + P.2 * ν₂ y = 0 := by
    intro P y hy
    have h0 : ν₀ y = 0 := image_eq_zero_of_notMem_tsupport (fun h => hy (Or.inl (Or.inl h)))
    have h1 : ν₁ y = 0 := image_eq_zero_of_notMem_tsupport (fun h => hy (Or.inl (Or.inr h)))
    have h2 : ν₂ y = 0 := image_eq_zero_of_notMem_tsupport (fun h => hy (Or.inr h))
    rw [h0, h1, h2]; ring
  have hz : ∀ P n, ∀ y ∈ (tsupport ν₀ ∪ tsupport ν₁ ∪ tsupport ν₂)ᶜ, s P n y = 0 := by
    intro P n
    induction n with
    | zero =>
      intro y hy
      have e := congrFun (hs0 P) y
      beta_reduce at e
      rw [e]; exact hνz P y hy
    | succ n ih =>
      intro y hy
      have e := congrFun (hs P n) y
      beta_reduce at e
      rw [e, hνz P y hy, zero_mul]
  have hz1 : ∀ P n a, ∀ y ∈ (tsupport ν₀ ∪ tsupport ν₁ ∪ tsupport ν₂)ᶜ, fderiv ℝ (s P n) y a = 0 :=
    fun P n a => wr_D_zero_on hU (hz P n) a
  have hz2 : ∀ P n a b, ∀ y ∈ (tsupport ν₀ ∪ tsupport ν₁ ∪ tsupport ν₂)ᶜ,
      fderiv ℝ (fun z => fderiv ℝ (s P n) z b) y a = 0 :=
    fun P n a b => wr_D_zero_on hU (hz1 P n b) a
  have hz3 : ∀ P n a b c, ∀ y ∈ (tsupport ν₀ ∪ tsupport ν₁ ∪ tsupport ν₂)ᶜ,
      fderiv ℝ (fun z => fderiv ℝ (fun z => fderiv ℝ (s P n) z c) z b) y a = 0 :=
    fun P n a b c => wr_D_zero_on hU (hz2 P n b c) a
  obtain ⟨M, hM⟩ := lemma11_1 hp2 hR₀
  have hM'0 : 0 ≤ max M 0 := le_max_right _ _
  have hTb : ∀ ω : ℂ → ℂ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ω → HasCompactSupport ω →
      (∀ y ∈ (tsupport ν₀ ∪ tsupport ν₁ ∪ tsupport ν₂)ᶜ, ω y = 0) → ∀ z,
      ‖cauchyT ω z‖ ≤ max M 0 * (eLpNorm ω (ENNReal.ofReal p)).toReal := by
    intro ω hω hωc hωU z
    have h := hM ω (wr_memLp hω hωc p) (fun y hy => hωU y (hout y hy)) z
    exact h.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) ENNReal.toReal_nonneg)
  have hfin : ∀ {N : ℝ} (n : ℕ), N ≤ E * ρ ^ n → max M 0 * N ≤ max M 0 * E * ρ ^ n := by
    intro N n hN
    have := mul_le_mul_of_nonneg_left hN hM'0
    linarith [this, show max M 0 * (E * ρ ^ n) = max M 0 * E * ρ ^ n by ring]
  have hT1 : ∀ P n a, (fun z => fderiv ℝ (cauchyT (s P n)) z a) = cauchyT (fun z => fderiv ℝ (s P n) z a) :=
    fun P n a => wr_D_cauchyT (hsc P n).1 (hsc P n).2 a
  have hT2 : ∀ P n a b, (fun z => fderiv ℝ (fun y => fderiv ℝ (cauchyT (s P n)) y b) z a) =
      cauchyT (fun z => fderiv ℝ (fun z => fderiv ℝ (s P n) z b) z a) := fun P n a b =>
    (congrArg (fun f : ℂ → ℂ => fun z => fderiv ℝ f z a) (hT1 P n b)).trans
      (wr_D_cauchyT (wr_D_sc (hsc P n) b).1 (wr_D_sc (hsc P n) b).2 a)
  have hT3 : ∀ P n a b c, (fun z => fderiv ℝ (fun y => fderiv ℝ (fun w => fderiv ℝ (cauchyT (s P n)) w c) y b) z a) =
      cauchyT (fun z => fderiv ℝ (fun z => fderiv ℝ (fun z => fderiv ℝ (s P n) z c) z b) z a) := fun P n a b c =>
    (congrArg (fun f : ℂ → ℂ => fun z => fderiv ℝ f z a) (hT2 P n b c)).trans
      (wr_D_cauchyT (wr_D_sc (wr_D_sc (hsc P n) c) b).1 (wr_D_sc (wr_D_sc (hsc P n) c) b).2 a)
  have hu : Summable (fun n : ℕ => max M 0 * E * ρ ^ n) :=
    (summable_geometric_of_lt_one hρ0 hρ1).mul_left (max M 0 * E)
  have one1 : ‖(1 : ℂ)‖ ≤ 1 := by simp
  obtain ⟨hcd, hcont⟩ := wr_tsum_contDiff (X := ℂ × ℂ) (S := ball P₀ δ) (g := fun P n => cauchyT (s P n))
    (fun P n => wr_cauchyT_contDiff_top (hsc P n).1 (hsc P n).2) hu
    (fun P hP n z => (hTb _ (hsc P n).1 (hsc P n).2 (hz P n) z).trans
      (hfin n (hlev P hP 1 1 1 one1 one1 one1 n).1))
    (fun P hP n z a ha => by
      rw [show fderiv ℝ (cauchyT (s P n)) z a = cauchyT (fun z => fderiv ℝ (s P n) z a) z from congrFun (hT1 P n a) z]
      exact (hTb _ (wr_D_sc (hsc P n) a).1 (wr_D_sc (hsc P n) a).2 (hz1 P n a) z).trans
        (hfin n (hlev P hP a 1 1 ha one1 one1 n).2.1))
    (fun P hP n z a b ha hb => by
      rw [show fderiv ℝ (fun y => fderiv ℝ (cauchyT (s P n)) y b) z a =
          cauchyT (fun z => fderiv ℝ (fun z => fderiv ℝ (s P n) z b) z a) z from congrFun (hT2 P n a b) z]
      exact (hTb _ (wr_D_sc (wr_D_sc (hsc P n) b) a).1 (wr_D_sc (wr_D_sc (hsc P n) b) a).2 (hz2 P n a b) z).trans
        (hfin n (hlev P hP a b 1 ha hb one1 n).2.2.1))
    (fun P hP n z a b c ha hb hc => by
      rw [show fderiv ℝ (fun y => fderiv ℝ (fun w => fderiv ℝ (cauchyT (s P n)) w c) y b) z a =
          cauchyT (fun z => fderiv ℝ (fun z => fderiv ℝ (fun z => fderiv ℝ (s P n) z c) z b) z a) z from
        congrFun (hT3 P n a b c) z]
      exact (hTb _ (wr_D_sc (wr_D_sc (wr_D_sc (hsc P n) c) b) a).1
        (wr_D_sc (wr_D_sc (wr_D_sc (hsc P n) c) b) a).2 (hz3 P n a b c) z).trans
        (hfin n (hlev P hP a b c ha hb hc n).2.2.2))
    (fun n j _ => (wr3_iter_term_cont h₀ hc₀ h₁ hc₁ h₂ hc₂ hs0 hs n j).continuousOn)
  exact ⟨δ, hδ, (ball_subset_ball hδ1).trans hball, hcd, hcont⟩

/-- **Smooth compactly supported affine family** (cf. `wr_smooth_family`): every normalized solution is `C³` in
`z`, with `z`-derivatives of order `≤ 3` jointly continuous in `(P, z)`. -/
theorem wr3_smooth_family {ν₀ ν₁ ν₂ : ℂ → ℂ} (h₀ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ν₀) (hc₀ : HasCompactSupport ν₀)
    (h₁ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ν₁) (hc₁ : HasCompactSupport ν₁)
    (h₂ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ν₂) (hc₂ : HasCompactSupport ν₂) {W : Set (ℂ × ℂ)} (hW : IsOpen W)
    (hWk : ∀ P ∈ W, ∃ k < 1, ∀ z, ‖ν₀ z + P.1 * ν₁ z + P.2 * ν₂ z‖ ≤ k) :
    (∀ P ∈ W, ContDiff ℝ 3 (normalizedSolution fun u => ν₀ u + P.1 * ν₁ u + P.2 * ν₂ u)) ∧
      ∀ j ≤ 3, ContinuousOn (fun q : (ℂ × ℂ) × ℂ =>
        iteratedFDeriv ℝ j (normalizedSolution fun u => ν₀ u + q.1.1 * ν₁ u + q.1.2 * ν₂ u) q.2) (W ×ˢ univ) := by
  obtain ⟨s, hs0, hs⟩ : ∃ s : ℂ × ℂ → ℕ → ℂ → ℂ, (∀ P, s P 0 = fun z => ν₀ z + P.1 * ν₁ z + P.2 * ν₂ z) ∧
      ∀ P n, s P (n + 1) = fun z => (ν₀ z + P.1 * ν₁ z + P.2 * ν₂ z) * hilbertHSmooth (s P n) z :=
    ⟨fun P n => Nat.rec (motive := fun _ => ℂ → ℂ) (fun z => ν₀ z + P.1 * ν₁ z + P.2 * ν₂ z)
      (fun _ g => fun z => (ν₀ z + P.1 * ν₁ z + P.2 * ν₂ z) * hilbertHSmooth g z) n, fun _ => rfl, fun _ _ => rfl⟩
  have SP : ∀ P : ℂ × ℂ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z => ν₀ z + P.1 * ν₁ z + P.2 * ν₂ z) ∧
      HasCompactSupport (fun z => ν₀ z + P.1 * ν₁ z + P.2 * ν₂ z) := by
    intro P
    have e : (fun z => ν₀ z + P.1 * ν₁ z + P.2 * ν₂ z) = fun z => ν₀ z + (P.1 * ν₁ z + P.2 * ν₂ z) :=
      funext fun z => add_assoc _ _ _
    rw [e]
    exact ⟨h₀.add (wr_lin_sc h₁ hc₁ h₂ hc₂ P.1 P.2).1, hc₀.add (wr_lin_sc h₁ hc₁ h₂ hc₂ P.1 P.2).2⟩
  have hrep : ∀ P ∈ W, (∀ z, Summable fun n => cauchyT (s P n) z) ∧
      (1 + ∑' n, cauchyT (s P n) 1) - ∑' n, cauchyT (s P n) 0 ≠ 0 ∧
      (normalizedSolution fun u => ν₀ u + P.1 * ν₁ u + P.2 * ν₂ u) = fun z =>
        ((z + ∑' n, cauchyT (s P n) z) - ∑' n, cauchyT (s P n) 0) /
          ((1 + ∑' n, cauchyT (s P n) 1) - ∑' n, cauchyT (s P n) 0) := by
    intro P hP
    obtain ⟨k, hk1, hk⟩ := hWk P hP
    exact wr_ns_series (SP P).1 (SP P).2 ((norm_nonneg _).trans (hk 0)) hk1 hk (hs0 P) (hs P)
  refine ⟨fun P hP => ?_, fun j hj => ?_⟩
  · obtain ⟨δ, hδ, -, hcd, -⟩ := wr3_A3_local h₀ hc₀ h₁ hc₁ h₂ hc₂ hW hWk hs0 hs hP
    rw [(hrep P hP).2.2]
    exact ((contDiff_id.add (hcd P (mem_ball_self hδ))).sub contDiff_const).div_const _
  · intro q hq
    obtain ⟨δ, hδ, hsub, hcd, hcont⟩ := wr3_A3_local h₀ hc₀ h₁ hc₁ h₂ hc₂ hW hWk hs0 hs hq.1
    have hFv : ContinuousOn (fun q : (ℂ × ℂ) × ℂ => ∑' n, cauchyT (s q.1 n) q.2) (ball q.1 δ ×ˢ univ) := by
      refine ((continuousMultilinearCurryFin0 ℝ ℂ ℂ).continuous.comp_continuousOn (hcont 0 (by norm_num))).congr ?_
      intro q' _
      simp [iteratedFDeriv_zero_eq_comp]
    have hpt : ∀ w : ℂ, ContinuousOn (fun P : ℂ × ℂ => ∑' n, cauchyT (s P n) w) (ball q.1 δ) := fun w =>
      hFv.comp (continuous_id.prodMk continuous_const).continuousOn (fun P hP => ⟨hP, mem_univ _⟩)
    have hDc : ContinuousOn (fun P : ℂ × ℂ => (1 + ∑' n, cauchyT (s P n) 1) - ∑' n, cauchyT (s P n) 0)
        (ball q.1 δ) := (continuousOn_const.add (hpt 1)).sub (hpt 0)
    have haff := wr_affine_iter_cont (S := ball q.1 δ) (F := fun P z => ∑' n, cauchyT (s P n) z)
      (c0 := fun P => ∑' n, cauchyT (s P n) 0) (D := fun P => (1 + ∑' n, cauchyT (s P n) 1) - ∑' n, cauchyT (s P n) 0)
      hcd hcont (hpt 0) hDc (fun P hP => (hrep P (hsub hP)).2.1) j hj
    have hnhds : ball q.1 δ ×ˢ (univ : Set ℂ) ∈ 𝓝 q :=
      (isOpen_ball.prod isOpen_univ).mem_nhds ⟨mem_ball_self hδ, mem_univ _⟩
    refine ((haff.congr ?_).continuousAt hnhds).continuousWithinAt
    intro q' hq'
    show iteratedFDeriv ℝ j (normalizedSolution fun u => ν₀ u + q'.1.1 * ν₁ u + q'.1.2 * ν₂ u) q'.2 = _
    rw [(hrep q'.1 (hsub hq'.1)).2.2]

/-- Separate holomorphy in each parameter (helper copy of W3-2, placed above W3-1). -/
theorem wr3_aholo {m₀ m₁ m₂ : ℂ → ℂ} {k₀ k₁ k₂ : ℝ} (hm₀ : IsBeltramiCoeff m₀ univ k₀)
    (hm₁ : IsBeltramiCoeff m₁ univ k₁) (hm₂ : IsBeltramiCoeff m₂ univ k₂) {W : Set (ℂ × ℂ)} (hW : IsOpen W)
    (hWk : ∀ P ∈ W, ∃ k < 1, IsBeltramiCoeff (fun u => m₀ u + P.1 * m₁ u + P.2 * m₂ u) univ k) (z : ℂ) :
    (∀ b : ℂ, DifferentiableOn ℂ
      (fun a => normalizedSolution (fun u => m₀ u + a * m₁ u + b * m₂ u) z) {a | (a, b) ∈ W}) ∧
      ∀ a : ℂ, DifferentiableOn ℂ
        (fun b => normalizedSolution (fun u => m₀ u + a * m₁ u + b * m₂ u) z) {b | (a, b) ∈ W} := by
  -- `hm₀`, `hW` are not needed: differentiability holds at every point of `W` (`wr3_diffAt`).
  have _h₀ := hm₀
  have _hW := hW
  refine ⟨fun b a ha => ?_, fun a b hb => ?_⟩
  · obtain ⟨k, hk, hP⟩ := hWk _ ha
    have hf : DifferentiableAt ℂ (fun t : ℂ => (t, b)) a := by fun_prop
    exact (DifferentiableAt.comp (g := fun p : ℂ × ℂ =>
      normalizedSolution (fun u => m₀ u + p.1 * m₁ u + p.2 * m₂ u) z) a (wr3_diffAt hm₁ hm₂ hk hP z)
      hf).differentiableWithinAt
  · obtain ⟨k, hk, hP⟩ := hWk _ hb
    have hf : DifferentiableAt ℂ (fun t : ℂ => (a, t)) b := by fun_prop
    exact (DifferentiableAt.comp (g := fun p : ℂ × ℂ =>
      normalizedSolution (fun u => m₀ u + p.1 * m₁ u + p.2 * m₂ u) z) b (wr3_diffAt hm₁ hm₂ hk hP z)
      hf).differentiableWithinAt

/-- Joint continuity (helper copy of W3-3). -/
theorem wr3_acont {m₀ m₁ m₂ : ℂ → ℂ} {k₀ k₁ k₂ : ℝ} (hm₀ : IsBeltramiCoeff m₀ univ k₀)
    (hm₁ : IsBeltramiCoeff m₁ univ k₁) (hm₂ : IsBeltramiCoeff m₂ univ k₂) {W : Set (ℂ × ℂ)} (hW : IsOpen W)
    (hWk : ∀ P ∈ W, ∃ k < 1, IsBeltramiCoeff (fun u => m₀ u + P.1 * m₁ u + P.2 * m₂ u) univ k) :
    ContinuousOn (fun q : (ℂ × ℂ) × ℂ =>
      normalizedSolution (fun u => m₀ u + q.1.1 * m₁ u + q.1.2 * m₂ u) q.2) (W ×ˢ univ) := by
  -- `hW` is not needed (continuity within `W ×ˢ univ` holds at every point of `W`).
  have _hW := hW
  rintro ⟨P₀, z₀⟩ ⟨hP₀, -⟩
  show Tendsto _ (𝓝[W ×ˢ univ] (P₀, z₀)) _
  rw [Filter.tendsto_iff_seq_tendsto]
  intro x hx
  have hx' := tendsto_nhdsWithin_iff.mp hx
  have h1 : Tendsto (fun n => (x n).1) atTop (𝓝 P₀) := (continuous_fst.tendsto _).comp hx'.1
  have h2 : Tendsto (fun n => (x n).2) atTop (𝓝 z₀) := (continuous_snd.tendsto _).comp hx'.1
  have hL := wr3_luc hm₀ hm₁ hm₂ hWk hP₀ h1
  obtain ⟨k₀, hk₀, h₀⟩ := hWk _ hP₀
  obtain ⟨h0, hk0, hk1⟩ := wr_coeff_nonneg hk₀ h₀
  have hc : Continuous (normalizedSolution (fun u => m₀ u + P₀.1 * m₁ u + P₀.2 * m₂ u)) :=
    continuousOn_univ.1 (wr_ns_qc hk0 hk1 h0 le_rfl).1.2.2.1.1
  exact hL.tendsto_comp hc.continuousAt h2

/-- Joint continuity of the inverse (helper copy of W3-4). -/
theorem wr3_ainv {m₀ m₁ m₂ : ℂ → ℂ} {k₀ k₁ k₂ : ℝ} (hm₀ : IsBeltramiCoeff m₀ univ k₀)
    (hm₁ : IsBeltramiCoeff m₁ univ k₁) (hm₂ : IsBeltramiCoeff m₂ univ k₂) {W : Set (ℂ × ℂ)} (hW : IsOpen W)
    (hWk : ∀ P ∈ W, ∃ k < 1, IsBeltramiCoeff (fun u => m₀ u + P.1 * m₁ u + P.2 * m₂ u) univ k) :
    ContinuousOn (fun q : (ℂ × ℂ) × ℂ =>
      Function.invFun (normalizedSolution fun u => m₀ u + q.1.1 * m₁ u + q.1.2 * m₂ u) q.2) (W ×ˢ univ) := by
  -- `hW` is not needed (continuity within `W ×ˢ univ` holds at every point of `W`).
  have _hW := hW
  rintro ⟨P₀, z₀⟩ ⟨hP₀, -⟩
  show Tendsto _ (𝓝[W ×ˢ univ] (P₀, z₀)) _
  rw [Filter.tendsto_iff_seq_tendsto]
  intro x hx
  have hx' := tendsto_nhdsWithin_iff.mp hx
  have h1 : Tendsto (fun n => (x n).1) atTop (𝓝 P₀) := (continuous_fst.tendsto _).comp hx'.1
  have h2 : Tendsto (fun n => (x n).2) atTop (𝓝 z₀) := (continuous_snd.tendsto _).comp hx'.1
  have hL := wr3_luc hm₀ hm₁ hm₂ hWk hP₀ h1
  obtain ⟨N, hN⟩ := eventually_atTop.1 hx'.2
  have he : ∀ n, ∃ e : ℂ ≃ₜ ℂ,
      ⇑e = normalizedSolution (fun u => m₀ u + (x (n + N)).1.1 * m₁ u + (x (n + N)).1.2 * m₂ u) := by
    intro n
    obtain ⟨k, hk, hP⟩ := hWk _ (hN (n + N) (by omega)).1
    obtain ⟨h0, hk0, hk1⟩ := wr_coeff_nonneg hk hP
    have h := wr_ns_qc hk0 hk1 h0 le_rfl
    exact t1_homeomorph h.1 h.2.1
  choose E hE using he
  obtain ⟨k₀, hk₀, h₀⟩ := hWk _ hP₀
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
  have hval : Function.invFun (normalizedSolution fun u => m₀ u + P₀.1 * m₁ u + P₀.2 * m₂ u) z₀ =
      e₀.symm z₀ := wr_invFun_eq he₀ z₀
  show Tendsto (fun n => Function.invFun
    (normalizedSolution fun u => m₀ u + (x n).1.1 * m₁ u + (x n).1.2 * m₂ u) (x n).2) atTop
    (𝓝 (Function.invFun (normalizedSolution fun u => m₀ u + P₀.1 * m₁ u + P₀.2 * m₂ u) z₀))
  rw [hval, ← tendsto_add_atTop_iff_nat N]
  refine hlim.congr fun n => ?_
  show (E n).symm (x (n + N)).2 = _
  rw [wr_invFun_eq (hE n)]

/-- `C³` in the parameter at a fixed point (cf. `wr_ns2_param_contDiffOn`). -/
theorem wr3_pcd {m₀ m₁ m₂ : ℂ → ℂ} {k₀ k₁ k₂ : ℝ} (hm₀ : IsBeltramiCoeff m₀ univ k₀) (hm₁ : IsBeltramiCoeff m₁ univ k₁)
    (hm₂ : IsBeltramiCoeff m₂ univ k₂) {W : Set (ℂ × ℂ)} (hW : IsOpen W)
    (hWk : ∀ P ∈ W, ∃ k < 1, IsBeltramiCoeff (fun u => m₀ u + P.1 * m₁ u + P.2 * m₂ u) univ k) (z : ℂ) :
    ContDiffOn ℝ 3 (fun P : ℂ × ℂ => normalizedSolution (fun u => m₀ u + P.1 * m₁ u + P.2 * m₂ u) z) W := by
  refine contDiffOn_of_locally_contDiffOn fun P₀ hP₀ => ?_
  obtain ⟨R, hR, hRW⟩ := Metric.isOpen_iff.1 hW P₀ hP₀
  have hsub : closedBall P₀.1 (R / 2) ×ˢ closedBall P₀.2 (R / 2) ⊆ W := by
    intro P hP
    apply hRW
    rw [mem_ball, Prod.dist_eq, max_lt_iff]
    exact ⟨lt_of_le_of_lt hP.1 (by linarith), lt_of_le_of_lt hP.2 (by linarith)⟩
  have hC2 := wr3_acont hm₀ hm₁ hm₂ hW hWk
  have hcont : ContinuousOn (fun P : ℂ × ℂ => normalizedSolution (fun u => m₀ u + P.1 * m₁ u + P.2 * m₂ u) z)
      (closedBall P₀.1 (R / 2) ×ˢ closedBall P₀.2 (R / 2)) := by
    have h := ContinuousOn.comp (g := fun q : (ℂ × ℂ) × ℂ =>
        normalizedSolution (fun u => m₀ u + q.1.1 * m₁ u + q.1.2 * m₂ u) q.2)
      (f := fun P : ℂ × ℂ => (P, z)) hC2 (continuous_id.prodMk continuous_const).continuousOn
      (fun P hP => ⟨hsub hP, mem_univ _⟩)
    exact h
  have hH := wr3_aholo hm₀ hm₁ hm₂ hW hWk z
  have h₁ : ∀ b ∈ closedBall P₀.2 (R / 2), DifferentiableOn ℂ
      (fun a => normalizedSolution (fun u => m₀ u + a * m₁ u + b * m₂ u) z) (ball P₀.1 (R / 2)) :=
    fun b hb => (hH.1 b).mono fun a ha => hsub ⟨ball_subset_closedBall ha, hb⟩
  have h₂ : ∀ a ∈ closedBall P₀.1 (R / 2), DifferentiableOn ℂ
      (fun b => normalizedSolution (fun u => m₀ u + a * m₁ u + b * m₂ u) z) (ball P₀.2 (R / 2)) :=
    fun a ha => (hH.2 a).mono fun b hb => hsub ⟨ha, ball_subset_closedBall hb⟩
  refine ⟨ball P₀ (R / 4), isOpen_ball, mem_ball_self (by positivity), ?_⟩
  exact (wr_bidisc_contDiffOn (c := P₀) (by positivity) hcont h₁ h₂).mono
    (inter_subset_right.trans (ball_subset_ball (le_of_eq (by ring))))

/-- Local Cauchy representation through a smooth comparison family (cf. `wr_local_cauchy`). -/
theorem wr3_local_cauchy {m₀ m₁ m₂ : ℂ → ℂ} {k₀ k₁ k₂ : ℝ} (hm₀ : IsBeltramiCoeff m₀ univ k₀) (hm₁ : IsBeltramiCoeff m₁ univ k₁)
    (hm₂ : IsBeltramiCoeff m₂ univ k₂) {Ω : Set ℂ} (hΩ : IsOpen Ω)
    (hs₀ : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) m₀ Ω)
    (hs₁ : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) m₁ Ω) (hs₂ : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) m₂ Ω)
    {W : Set (ℂ × ℂ)} (hW : IsOpen W)
    (hWk : ∀ P ∈ W, ∃ k < 1, IsBeltramiCoeff (fun u => m₀ u + P.1 * m₁ u + P.2 * m₂ u) univ k)
    {P₀ : ℂ × ℂ} (hP₀ : P₀ ∈ W) {z₀ : ℂ} (hz₀ : z₀ ∈ Ω) :
    ∃ V ∈ 𝓝 P₀, V ⊆ W ∧ ∃ ρ > 0, ∃ G : ℂ × ℂ → ℂ → ℂ, ∃ c : ℂ, ∃ R > 0,
      (∀ P ∈ V, ContDiff ℝ 3 (G P)) ∧
      (∀ j ≤ 3, ContinuousOn (fun q : (ℂ × ℂ) × ℂ => iteratedFDeriv ℝ j (G q.1) q.2) (V ×ˢ univ)) ∧
      ContinuousOn (fun q : (ℂ × ℂ) × ℂ =>
        normalizedSolution (fun u => m₀ u + q.1.1 * m₁ u + q.1.2 * m₂ u) (Function.invFun (G q.1) q.2))
        (V ×ˢ sphere c R) ∧
      ∀ P ∈ V, ∀ z ∈ ball z₀ ρ, G P z ∈ ball c (R / 2) ∧
        normalizedSolution (fun u => m₀ u + P.1 * m₁ u + P.2 * m₂ u) z =
          (2 * π * I)⁻¹ * ∮ ξ in C(c, R),
            normalizedSolution (fun u => m₀ u + P.1 * m₁ u + P.2 * m₂ u) (Function.invFun (G P) ξ) / (ξ - G P z) := by
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
  obtain ⟨ν₀, hν₀d⟩ : ∃ ν₀ : ℂ → ℂ, ν₀ = fun z => (χ z : ℂ) * m₀ z := ⟨_, rfl⟩
  obtain ⟨ν₁, hν₁d⟩ : ∃ ν₁ : ℂ → ℂ, ν₁ = fun z => (χ z : ℂ) * m₁ z := ⟨_, rfl⟩
  obtain ⟨ν₂, hν₂d⟩ : ∃ ν₂ : ℂ → ℂ, ν₂ = fun z => (χ z : ℂ) * m₂ z := ⟨_, rfl⟩
  have hν₀ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ν₀ := hν₀d ▸ wr_cutoff_mul_contDiff hΩ hs₀ χ.contDiff hχs
  have hν₁ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ν₁ := hν₁d ▸ wr_cutoff_mul_contDiff hΩ hs₁ χ.contDiff hχs
  have hν₂ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ν₂ := hν₂d ▸ wr_cutoff_mul_contDiff hΩ hs₂ χ.contDiff hχs
  have hcs : HasCompactSupport (fun z => (χ z : ℂ)) := χ.hasCompactSupport.comp_left Complex.ofReal_zero
  have hc₀ : HasCompactSupport ν₀ := hν₀d ▸ hcs.mul_right
  have hc₁ : HasCompactSupport ν₁ := hν₁d ▸ hcs.mul_right
  have hc₂ : HasCompactSupport ν₂ := hν₂d ▸ hcs.mul_right
  have hνP : ∀ (P : ℂ × ℂ) z, ν₀ z + P.1 * ν₁ z + P.2 * ν₂ z = (χ z : ℂ) * (m₀ z + P.1 * m₁ z + P.2 * m₂ z) := by
    intro P z
    rw [hν₀d, hν₁d, hν₂d]
    ring
  -- the comparison coefficients are bounded everywhere
  have hνk : ∀ P ∈ W, ∃ k < 1, ∀ z, ‖ν₀ z + P.1 * ν₁ z + P.2 * ν₂ z‖ ≤ k := by
    intro P hP
    obtain ⟨k, hk, hb⟩ := hWk P hP
    obtain ⟨hb', hk0, hk1⟩ := wr_coeff_nonneg hk hb
    refine ⟨max k 0, hk1, fun z => ?_⟩
    rw [hνP, norm_mul]
    by_cases hz : z ∈ Ω
    · have hcont : ContinuousOn (fun u => m₀ u + P.1 * m₁ u + P.2 * m₂ u) Ω :=
        (hs₀.continuousOn.add (continuousOn_const.mul hs₁.continuousOn)).add (continuousOn_const.mul hs₂.continuousOn)
      have hae : ∀ᵐ u, ‖m₀ u + P.1 * m₁ u + P.2 * m₂ u‖ ≤ max k 0 := by
        simpa only [Measure.restrict_univ] using hb'.2
      exact (mul_le_of_le_one_left (norm_nonneg _) (hχn z)).trans (wr_ae_bound_on hΩ hcont hae z hz)
    · rw [hχ0 z hz, norm_zero, zero_mul]
      exact hk0
  have hBν : ∀ P ∈ W, ∃ k < 1, IsBeltramiCoeff (fun u => ν₀ u + P.1 * ν₁ u + P.2 * ν₂ u) univ k := by
    intro P hP
    obtain ⟨k, hk, hb⟩ := hνk P hP
    exact ⟨k, hk, ((hν₀.continuous.add (continuous_const.mul hν₁.continuous)).add
      (continuous_const.mul hν₂.continuous)).aestronglyMeasurable, ae_of_all _ hb⟩
  have hBν₀ : IsBeltramiCoeff ν₀ univ k₀ := by
    refine ⟨hν₀.continuous.aestronglyMeasurable, hm₀.2.mono fun z hz => ?_⟩
    rw [hν₀d]
    show ‖(χ z : ℂ) * m₀ z‖ ≤ k₀
    rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) (hχn z)).trans hz
  have hBν₁ : IsBeltramiCoeff ν₁ univ k₁ := by
    refine ⟨hν₁.continuous.aestronglyMeasurable, hm₁.2.mono fun z hz => ?_⟩
    rw [hν₁d]
    show ‖(χ z : ℂ) * m₁ z‖ ≤ k₁
    rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) (hχn z)).trans hz
  have hBν₂ : IsBeltramiCoeff ν₂ univ k₂ := by
    refine ⟨hν₂.continuous.aestronglyMeasurable, hm₂.2.mono fun z hz => ?_⟩
    rw [hν₂d]
    show ‖(χ z : ℂ) * m₂ z‖ ≤ k₂
    rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) (hχn z)).trans hz
  -- the comparison family and its properties
  obtain ⟨hGsm, hGcont⟩ := wr3_smooth_family hν₀ hc₀ hν₁ hc₁ hν₂ hc₂ hW hνk
  have hGc := wr3_acont hBν₀ hBν₁ hBν₂ hW hBν
  have hGi := wr3_ainv hBν₀ hBν₁ hBν₂ hW hBν
  have hMc := wr3_acont hm₀ hm₁ hm₂ hW hWk
  have hhom : ∀ P ∈ W, ∃ e : ℂ ≃ₜ ℂ, ⇑e = normalizedSolution (fun u => ν₀ u + P.1 * ν₁ u + P.2 * ν₂ u) := by
    intro P hP
    obtain ⟨k, hk, hP'⟩ := hBν P hP
    obtain ⟨h0, hk0, hk1⟩ := wr_coeff_nonneg hk hP'
    have h := wr_ns_qc hk0 hk1 h0 le_rfl
    exact t1_homeomorph h.1 h.2.1
  have hleft : ∀ P ∈ W, ∀ z, Function.invFun (normalizedSolution (fun u => ν₀ u + P.1 * ν₁ u + P.2 * ν₂ u))
      (normalizedSolution (fun u => ν₀ u + P.1 * ν₁ u + P.2 * ν₂ u) z) = z := by
    intro P hP z
    obtain ⟨e, he⟩ := hhom P hP
    rw [wr_invFun_eq he, ← he]
    exact e.symm_apply_apply z
  have hright : ∀ P ∈ W, ∀ ξ, normalizedSolution (fun u => ν₀ u + P.1 * ν₁ u + P.2 * ν₂ u)
      (Function.invFun (normalizedSolution (fun u => ν₀ u + P.1 * ν₁ u + P.2 * ν₂ u)) ξ) = ξ := by
    intro P hP ξ
    obtain ⟨e, he⟩ := hhom P hP
    rw [wr_invFun_eq he, ← he]
    exact e.apply_symm_apply ξ
  have hWn : W ×ˢ (univ : Set ℂ) ∈ 𝓝 (P₀, z₀) := prod_mem_nhds (hW.mem_nhds hP₀) Filter.univ_mem
  -- uniform geometry: the inverse maps a fixed closed disc around `c` into `B(z₀, 2r)`
  obtain ⟨c, hcd⟩ : ∃ c : ℂ, c = normalizedSolution (fun u => ν₀ u + P₀.1 * ν₁ u + P₀.2 * ν₂ u) z₀ := ⟨_, rfl⟩
  have hWc : W ×ˢ (univ : Set ℂ) ∈ 𝓝 (P₀, c) := prod_mem_nhds (hW.mem_nhds hP₀) Filter.univ_mem
  have hev1 : ∀ᶠ q in 𝓝 (P₀, c), Function.invFun (normalizedSolution
      (fun u => ν₀ u + q.1.1 * ν₁ u + q.1.2 * ν₂ u)) q.2 ∈ ball z₀ (2 * r) := by
    refine (hGi.continuousAt hWc).eventually (isOpen_ball.mem_nhds ?_)
    show Function.invFun (normalizedSolution (fun u => ν₀ u + P₀.1 * ν₁ u + P₀.2 * ν₂ u)) c ∈ ball z₀ (2 * r)
    rw [hcd, hleft P₀ hP₀ z₀]
    exact mem_ball_self (by positivity)
  obtain ⟨u₁, hu₁, v₁, hv₁, huv₁⟩ := mem_nhds_prod_iff.mp hev1
  obtain ⟨R₀, hR₀, hR₀v⟩ := Metric.mem_nhds_iff.mp hv₁
  have hR : 0 < R₀ / 2 := by positivity
  have hRsub : closedBall c (R₀ / 2) ⊆ v₁ :=
    (closedBall_subset_ball (by linarith)).trans hR₀v
  -- `G_P` maps a small ball around `z₀` into `B(c, R/2)`
  have hev2 : ∀ᶠ q in 𝓝 (P₀, z₀), normalizedSolution
      (fun u => ν₀ u + q.1.1 * ν₁ u + q.1.2 * ν₂ u) q.2 ∈ ball c (R₀ / 2 / 2) := by
    refine (hGc.continuousAt hWn).eventually (isOpen_ball.mem_nhds ?_)
    show normalizedSolution (fun u => ν₀ u + P₀.1 * ν₁ u + P₀.2 * ν₂ u) z₀ ∈ ball c (R₀ / 2 / 2)
    rw [← hcd]
    exact mem_ball_self (by positivity)
  obtain ⟨u₂, hu₂, v₂, hv₂, huv₂⟩ := mem_nhds_prod_iff.mp hev2
  obtain ⟨ρ₀, hρ₀, hρ₀v⟩ := Metric.mem_nhds_iff.mp hv₂
  refine ⟨u₁ ∩ u₂ ∩ W, inter_mem (inter_mem hu₁ hu₂) (hW.mem_nhds hP₀), inter_subset_right,
    min ρ₀ (2 * r), lt_min hρ₀ (by positivity), fun P => normalizedSolution (fun u => ν₀ u + P.1 * ν₁ u + P.2 * ν₂ u),
    c, R₀ / 2, hR, ?_, ?_, ?_, ?_⟩
  · intro P hP
    exact hGsm P hP.2
  · intro j hj
    exact (hGcont j hj).mono (prod_mono inter_subset_right subset_rfl)
  · have hf : ContinuousOn (fun q : (ℂ × ℂ) × ℂ => (q.1, Function.invFun (normalizedSolution
        (fun u => ν₀ u + q.1.1 * ν₁ u + q.1.2 * ν₂ u)) q.2)) ((u₁ ∩ u₂ ∩ W) ×ˢ sphere c (R₀ / 2)) :=
      continuousOn_fst.prodMk (hGi.mono (prod_mono inter_subset_right (subset_univ _)))
    exact hMc.comp hf fun q hq => ⟨hq.1.2, mem_univ _⟩
  · intro P hP z hz
    have hPW : P ∈ W := hP.2
    have hzv₂ : z ∈ v₂ := hρ₀v (ball_subset_ball (min_le_left _ _) hz)
    have hGz := huv₂ (show (P, z) ∈ u₂ ×ˢ v₂ from ⟨hP.1.2, hzv₂⟩)
    simp only [mem_ofPred_eq] at hGz
    refine ⟨hGz, ?_⟩
    have hzD : z ∈ ball z₀ (2 * r) := ball_subset_ball (min_le_right _ _) hz
    obtain ⟨k, hk, hbP⟩ := hWk P hPW
    obtain ⟨kν, hkν, hbν⟩ := hBν P hPW
    have hEq : EqOn (fun u => ν₀ u + P.1 * ν₁ u + P.2 * ν₂ u) (fun u => m₀ u + P.1 * m₁ u + P.2 * m₂ u) (ball z₀ (2 * r)) := by
      intro u hu
      show ν₀ u + P.1 * ν₁ u + P.2 * ν₂ u = m₀ u + P.1 * m₁ u + P.2 * m₂ u
      rw [hνP, hχ1 u hu, one_mul]
    have hmemD : ∀ ξ ∈ closedBall c (R₀ / 2),
        Function.invFun (normalizedSolution (fun u => ν₀ u + P.1 * ν₁ u + P.2 * ν₂ u)) ξ ∈ ball z₀ (2 * r) :=
      fun ξ hξ => by
        have h := huv₁ (show (P, ξ) ∈ u₁ ×ˢ v₁ from ⟨hP.1.1, hRsub hξ⟩)
        simp only [mem_ofPred_eq] at h
        exact h
    exact wr_d1_cauchy isOpen_ball hk hbP hkν hbν hEq hR hmemD hzD (ball_subset_ball (by linarith) hGz)

/-- **W3-1** (`z`-regularity with jointly continuous jets; cf. `wr_ns2_z_regular`). -/
theorem wr3_z_regular {m₀ m₁ m₂ : ℂ → ℂ} {k₀ k₁ k₂ : ℝ} (hm₀ : IsBeltramiCoeff m₀ univ k₀)
    (hm₁ : IsBeltramiCoeff m₁ univ k₁) (hm₂ : IsBeltramiCoeff m₂ univ k₂) {Ω : Set ℂ} (hΩ : IsOpen Ω)
    (hs₀ : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) m₀ Ω) (hs₁ : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) m₁ Ω)
    (hs₂ : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) m₂ Ω) {W : Set (ℂ × ℂ)} (hW : IsOpen W)
    (hWk : ∀ P ∈ W, ∃ k < 1, IsBeltramiCoeff (fun u => m₀ u + P.1 * m₁ u + P.2 * m₂ u) univ k) :
    (∀ P ∈ W, ContDiffOn ℝ 3 (normalizedSolution fun u => m₀ u + P.1 * m₁ u + P.2 * m₂ u) Ω) ∧
      ∀ j ≤ 3, ContinuousOn (fun q : (ℂ × ℂ) × ℂ =>
        iteratedFDeriv ℝ j (normalizedSolution fun u => m₀ u + q.1.1 * m₁ u + q.1.2 * m₂ u) q.2) (W ×ˢ Ω) := by
  obtain ⟨F, hF⟩ : ∃ F : ℂ × ℂ → ℂ → ℂ, F = fun P => normalizedSolution fun u => m₀ u + P.1 * m₁ u + P.2 * m₂ u :=
    ⟨_, rfl⟩
  have loc : ∀ P₀ ∈ W, ∀ z₀ ∈ Ω, ∃ r > 0, ∃ ρ > 0, ball z₀ ρ ⊆ Ω ∧
      (∀ P ∈ ball P₀ r, ContDiffOn ℝ 3 (F P) (ball z₀ ρ)) ∧
      ∀ j ≤ 3, ContinuousOn (fun q : (ℂ × ℂ) × ℂ => iteratedFDeriv ℝ j (F q.1) q.2)
        (ball P₀ r ×ˢ ball z₀ ρ) := by
    intro P₀ hP₀ z₀ hz₀
    obtain ⟨V, hV, -, ρ, hρ, G, c, R, hR, hG3, hGc, hhc0, hrep0⟩ :=
      wr3_local_cauchy hm₀ hm₁ hm₂ hΩ hs₀ hs₁ hs₂ hW hWk hP₀ hz₀
    have hhc : ContinuousOn (fun q : (ℂ × ℂ) × ℂ => F q.1 (Function.invFun (G q.1) q.2)) (V ×ˢ sphere c R) := by
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
    obtain ⟨h, hh⟩ : ∃ h : ℂ × ℂ → ℂ → ℂ, h = fun P ξ => (2 * π * I)⁻¹ * F P (Function.invFun (G P) ξ) :=
      ⟨_, rfl⟩
    have hhcont : ContinuousOn (fun p : (ℂ × ℂ) × ℂ => h p.1 p.2) (ball P₀ r ×ˢ sphere c R) := by
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
    have hGv : ContinuousOn (fun p : (ℂ × ℂ) × ℂ => G p.1 p.2) (ball P₀ r ×ˢ ball z₀ ρ₁) := by
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
  · have key : ContinuousOn (fun q : (ℂ × ℂ) × ℂ => iteratedFDeriv ℝ j (F q.1) q.2) (W ×ˢ Ω) := by
      intro q hq
      obtain ⟨r, hr, ρ, hρ, -, -, hc⟩ := loc q.1 hq.1 q.2 hq.2
      have hn : ball q.1 r ×ˢ ball q.2 ρ ∈ 𝓝 q :=
        (isOpen_ball.prod isOpen_ball).mem_nhds ⟨mem_ball_self hr, mem_ball_self hρ⟩
      exact ((hc j hj).continuousAt hn).continuousWithinAt
    rw [hF] at key
    exact key

/-- **W3-2** (holomorphy in each parameter; cf. `wr_ns2_holo`). -/
theorem wr3_holo {m₀ m₁ m₂ : ℂ → ℂ} {k₀ k₁ k₂ : ℝ} (hm₀ : IsBeltramiCoeff m₀ univ k₀)
    (hm₁ : IsBeltramiCoeff m₁ univ k₁) (hm₂ : IsBeltramiCoeff m₂ univ k₂) {W : Set (ℂ × ℂ)} (hW : IsOpen W)
    (hWk : ∀ P ∈ W, ∃ k < 1, IsBeltramiCoeff (fun u => m₀ u + P.1 * m₁ u + P.2 * m₂ u) univ k) (z : ℂ) :
    (∀ b : ℂ, DifferentiableOn ℂ
      (fun a => normalizedSolution (fun u => m₀ u + a * m₁ u + b * m₂ u) z) {a | (a, b) ∈ W}) ∧
      ∀ a : ℂ, DifferentiableOn ℂ
        (fun b => normalizedSolution (fun u => m₀ u + a * m₁ u + b * m₂ u) z) {b | (a, b) ∈ W} := by
  exact wr3_aholo hm₀ hm₁ hm₂ hW hWk z

/-- **W3-3** (joint continuity; cf. `wr_ns2_cont`). -/
theorem wr3_cont {m₀ m₁ m₂ : ℂ → ℂ} {k₀ k₁ k₂ : ℝ} (hm₀ : IsBeltramiCoeff m₀ univ k₀)
    (hm₁ : IsBeltramiCoeff m₁ univ k₁) (hm₂ : IsBeltramiCoeff m₂ univ k₂) {W : Set (ℂ × ℂ)} (hW : IsOpen W)
    (hWk : ∀ P ∈ W, ∃ k < 1, IsBeltramiCoeff (fun u => m₀ u + P.1 * m₁ u + P.2 * m₂ u) univ k) :
    ContinuousOn (fun q : (ℂ × ℂ) × ℂ =>
      normalizedSolution (fun u => m₀ u + q.1.1 * m₁ u + q.1.2 * m₂ u) q.2) (W ×ˢ univ) := by
  exact wr3_acont hm₀ hm₁ hm₂ hW hWk

/-- **W3-4** (joint continuity of the inverse; cf. `wr_ns2_inv_cont`). -/
theorem wr3_inv_cont {m₀ m₁ m₂ : ℂ → ℂ} {k₀ k₁ k₂ : ℝ} (hm₀ : IsBeltramiCoeff m₀ univ k₀)
    (hm₁ : IsBeltramiCoeff m₁ univ k₁) (hm₂ : IsBeltramiCoeff m₂ univ k₂) {W : Set (ℂ × ℂ)} (hW : IsOpen W)
    (hWk : ∀ P ∈ W, ∃ k < 1, IsBeltramiCoeff (fun u => m₀ u + P.1 * m₁ u + P.2 * m₂ u) univ k) :
    ContinuousOn (fun q : (ℂ × ℂ) × ℂ =>
      Function.invFun (normalizedSolution fun u => m₀ u + q.1.1 * m₁ u + q.1.2 * m₂ u) q.2) (W ×ˢ univ) := by
  exact wr3_ainv hm₀ hm₁ hm₂ hW hWk

/-- **W3-5** (positive Jacobian on `Ω`; cf. `wr_local_jacobian_pos`). -/
theorem wr3_jacobian_pos {m₀ m₁ m₂ : ℂ → ℂ} {Ω : Set ℂ} (hΩ : IsOpen Ω)
    (hs₀ : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) m₀ Ω) (hs₁ : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) m₁ Ω)
    (hs₂ : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) m₂ Ω) {P : ℂ × ℂ}
    (hP : ∃ k < 1, IsBeltramiCoeff (fun u => m₀ u + P.1 * m₁ u + P.2 * m₂ u) univ k) {z : ℂ} (hz : z ∈ Ω) :
    0 < ‖dz (normalizedSolution fun u => m₀ u + P.1 * m₁ u + P.2 * m₂ u) z‖ ^ 2 -
      ‖dzbar (normalizedSolution fun u => m₀ u + P.1 * m₁ u + P.2 * m₂ u) z‖ ^ 2 := by
  -- the two-coefficient Jacobian bound with `m₁' = m₀ + P.1 m₁ + P.2 m₂`, `m₂' = 0` at the parameter `(1, 0)`
  obtain ⟨k, hk, hb⟩ := hP
  have hz0 : IsBeltramiCoeff (fun _ : ℂ => (0 : ℂ)) univ 0 :=
    ⟨aestronglyMeasurable_const, ae_of_all _ fun u => by simp⟩
  have hs : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun u => m₀ u + P.1 * m₁ u + P.2 * m₂ u) Ω :=
    (hs₀.add (contDiffOn_const.mul hs₁)).add (contDiffOn_const.mul hs₂)
  have hb' : IsBeltramiCoeff (fun u => ((1 : ℂ), (0 : ℂ)).1 * (m₀ u + P.1 * m₁ u + P.2 * m₂ u) +
      ((1 : ℂ), (0 : ℂ)).2 * (0 : ℂ)) univ k := wr_isBC_congr hb (Eventually.of_forall fun u => by simp)
  have h := wr_local_jacobian_pos (m₁ := fun u => m₀ u + P.1 * m₁ u + P.2 * m₂ u) (m₂ := fun _ => 0)
    hb hz0 hΩ hs contDiffOn_const (P := ((1 : ℂ), (0 : ℂ))) ⟨k, hk, hb'⟩ hz
  have hF : normalizedSolution (fun u => ((1 : ℂ), (0 : ℂ)).1 * (m₀ u + P.1 * m₁ u + P.2 * m₂ u) +
      ((1 : ℂ), (0 : ℂ)).2 * (0 : ℂ)) = normalizedSolution (fun u => m₀ u + P.1 * m₁ u + P.2 * m₂ u) :=
    congrArg normalizedSolution (funext fun u => by simp)
  rw [hF] at h
  exact h

end TakhtajanTeo
