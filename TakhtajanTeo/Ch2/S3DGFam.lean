import TakhtajanTeo.Ch2.S35Gamma

/-!
# Γ-FAM: the Model A family `w_{a+tμ}` on `𝔻*` and on `𝔻`, with joint `C³` regularity and positive Jacobian
(下属6, statement file for audit; consumer: `s3d_D2_gd1_C1`).

As `s35g_family` (S35Gamma G2), with two strengthened clauses: the family is jointly `C³` in `((t, t̄), z)` on `D`
(the proof of `s35g_family` has it as `hUj`), and the Jacobian `|∂U|² - |∂̄U|²` is positive (`= |Φ'|² Jac(N)`,
`wr3_jacobian_pos`). The `𝔻` version needs coefficient representatives smooth on `𝔻`: the reflection
`(1 - |u|²)² ψ(ū)`, `ψ(s) = φ(1/s)/s⁴` of the harmonic `φ`, has a removable singularity at `0`.
It is needed at the point `p_a = w_a(∞) ∈ 𝔻*` (via `wAS_refl_comm`). Prefix `d2g_`. No new definitions.
-/

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal ComplexConjugate Classical Real

noncomputable section

namespace TakhtajanTeo.Ch2

open LiZhongQC

/-- [GFAM helper] `s35g_family` (S35Gamma G2) over a general open `Ω` carrying coefficient representatives
`m₀, m₁, m₂` smooth on `Ω`, with joint `C³` regularity and positive Jacobian. -/
theorem d2g_family_gen {a μ : LinfStar} (ha1 : ‖a‖ < 1) {Ω : Set ℂ} (hΩ : IsOpen Ω) {m₀ m₁ m₂ : ℂ → ℂ}
    (hm₀ : IsBeltramiCoeff m₀ univ ‖a‖) (hm₁ : IsBeltramiCoeff m₁ univ ‖μ‖) (hm₂ : IsBeltramiCoeff m₂ univ ‖μ‖)
    (hs₀ : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) m₀ Ω) (hs₁ : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) m₁ Ω)
    (hs₂ : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) m₂ Ω)
    (hcoef : ∀ e : ℂ, extA (a + e • μ) =ᵐ[volume] (fun u => m₀ u + e * m₁ u + conj e * m₂ u)) :
    ∃ r > 0, ∃ D : Set ((ℂ × ℂ) × ℂ), ∃ U : ℂ × ℂ → ℂ → ℂ, IsOpen D ∧
      (∀ q ∈ D, q.2 ∈ Ω) ∧
      (∀ t : ℂ, ‖t‖ < r → ∀ z ∈ Ω, wAS (a + t • μ) (z : ExtPlane) ≠ extInf →
        ((t, conj t), z) ∈ D ∧ U (t, conj t) z = wA (a + t • μ) z) ∧
      (∀ q ∈ D, DifferentiableAt ℂ (fun b => U (b, q.1.2) q.2) q.1.1 ∧
        DifferentiableAt ℂ (fun b => U (q.1.1, b) q.2) q.1.2) ∧
      ContDiffOn ℝ 3 (fun q : (ℂ × ℂ) × ℂ => U q.1 q.2) D ∧
      ∀ q ∈ D, 0 < ‖dz (U q.1) q.2‖ ^ 2 - ‖dzbar (U q.1) q.2‖ ^ 2 := by
  set W : Set (ℂ × ℂ) := {P | ‖a‖ + 2 * ‖μ‖ * ‖P‖ < 1} with hWdef
  have hWo : IsOpen W := isOpen_lt (continuous_const.add (continuous_const.mul continuous_norm)) continuous_const
  have hbc : ∀ P : ℂ × ℂ,
      IsBeltramiCoeff (fun u => m₀ u + P.1 * m₁ u + P.2 * m₂ u) univ (‖a‖ + 2 * ‖μ‖ * ‖P‖) := by
    intro P
    have hl := wr_coeff_lin hm₁ hm₂ P
    refine ⟨(hm₀.1.add (hm₁.1.const_mul P.1)).add (hm₂.1.const_mul P.2), ?_⟩
    filter_upwards [hm₀.2, hl.2] with u h0 h1
    have h1' : ‖P.1 * m₁ u + P.2 * m₂ u‖ ≤ (|‖μ‖| + |‖μ‖|) * ‖P‖ := h1
    calc ‖m₀ u + P.1 * m₁ u + P.2 * m₂ u‖ = ‖m₀ u + (P.1 * m₁ u + P.2 * m₂ u)‖ := by rw [add_assoc]
      _ ≤ ‖m₀ u‖ + ‖P.1 * m₁ u + P.2 * m₂ u‖ := norm_add_le _ _
      _ ≤ ‖a‖ + (|‖μ‖| + |‖μ‖|) * ‖P‖ := add_le_add h0 h1'
      _ = ‖a‖ + 2 * ‖μ‖ * ‖P‖ := by rw [abs_of_nonneg (norm_nonneg μ)]; ring
  have hWk : ∀ P ∈ W, ∃ k < 1, IsBeltramiCoeff (fun u => m₀ u + P.1 * m₁ u + P.2 * m₂ u) univ k :=
    fun P hP => ⟨_, hP, hbc P⟩
  set N : ℂ × ℂ → ℂ → ℂ := fun P => normalizedSolution (fun u => m₀ u + P.1 * m₁ u + P.2 * m₂ u) with hNdef
  set Φ : ℂ × ℂ × ℂ → ℂ := fun x =>
    ((-(1 * (-I - -1)) * (x.2.1 - 1) + -(-((-1) * (-I - 1))) * (x.2.1 - x.1)) * x.2.2 +
      (-(1 * (-I - -1)) * (-(x.1 * (x.2.1 - 1))) + -(-((-1) * (-I - 1))) * (-(1 * (x.2.1 - x.1))))) /
    ((-(-I - -1) * (x.2.1 - 1) + (-I - 1) * (x.2.1 - x.1)) * x.2.2 +
      (-(-I - -1) * (-(x.1 * (x.2.1 - 1))) + (-I - 1) * (-(1 * (x.2.1 - x.1))))) with hΦdef
  set den : ℂ × ℂ × ℂ → ℂ := fun x =>
    (-(-I - -1) * (x.2.1 - 1) + (-I - 1) * (x.2.1 - x.1)) * x.2.2 +
      (-(-I - -1) * (-(x.1 * (x.2.1 - 1))) + (-I - 1) * (-(1 * (x.2.1 - x.1)))) with hdendef
  have hdenc : Continuous den := by rw [hdendef]; fun_prop
  have hΦd : ∀ x, den x ≠ 0 → ContDiffAt ℂ 3 Φ x := by
    intro x hx
    rw [hΦdef]
    exact ContDiffAt.div (by fun_prop) (by fun_prop) hx
  set U : ℂ × ℂ → ℂ → ℂ := fun P z => Φ (N P (-1), N P (-I), N P z) with hUdef
  set g : (ℂ × ℂ) × ℂ → ℂ × ℂ × ℂ × ℂ := fun q =>
    (N q.1 (-1) - N q.1 (-I), N q.1 (-1) - 1, N q.1 (-I) - 1, den (N q.1 (-1), N q.1 (-I), N q.1 q.2)) with hgdef
  set T : Set (ℂ × ℂ × ℂ × ℂ) := {x | x.1 ≠ 0 ∧ x.2.1 ≠ 0 ∧ x.2.2.1 ≠ 0 ∧ x.2.2.2 ≠ 0} with hTdef
  have hTo : IsOpen T :=
    (isOpen_ne_fun continuous_fst continuous_const).inter
      ((isOpen_ne_fun (continuous_fst.comp continuous_snd) continuous_const).inter
        ((isOpen_ne_fun (continuous_fst.comp (continuous_snd.comp continuous_snd)) continuous_const).inter
          (isOpen_ne_fun (continuous_snd.comp (continuous_snd.comp continuous_snd)) continuous_const)))
  have hNc : ContinuousOn (fun q : (ℂ × ℂ) × ℂ => N q.1 q.2) (W ×ˢ univ) := wr3_cont hm₀ hm₁ hm₂ hWo hWk
  have hNpt : ∀ z : ℂ, ContinuousOn (fun q : (ℂ × ℂ) × ℂ => N q.1 z) (W ×ˢ Ω) := by
    intro z
    have h := ContinuousOn.comp (g := fun q : (ℂ × ℂ) × ℂ => N q.1 q.2)
      (f := fun q : (ℂ × ℂ) × ℂ => (q.1, z)) hNc (continuous_fst.prodMk continuous_const).continuousOn
      (fun (q : (ℂ × ℂ) × ℂ) (hq : q ∈ W ×ˢ Ω) => show (q.1, z) ∈ W ×ˢ univ from ⟨hq.1, mem_univ _⟩)
    exact h
  have hNz : ContinuousOn (fun q : (ℂ × ℂ) × ℂ => N q.1 q.2) (W ×ˢ Ω) :=
    hNc.mono (prod_mono subset_rfl (subset_univ _))
  have hgc : ContinuousOn g (W ×ˢ Ω) :=
    ((hNpt _).sub (hNpt _)).prodMk (((hNpt _).sub continuousOn_const).prodMk (((hNpt _).sub continuousOn_const).prodMk
      (hdenc.comp_continuousOn ((hNpt _).prodMk ((hNpt _).prodMk hNz)))))
  set D : Set ((ℂ × ℂ) × ℂ) := (W ×ˢ Ω) ∩ g ⁻¹' T with hDdef
  have hDo : IsOpen D := hgc.isOpen_inter_preimage (hWo.prod hΩ) hTo
  obtain ⟨hz3, hzc⟩ := wr3_z_regular hm₀ hm₁ hm₂ hΩ hs₀ hs₁ hs₂ hWo hWk
  have hH := wr3_holo hm₀ hm₁ hm₂ hWo hWk
  have hJ : ContDiffOn ℝ 3 (fun q : (ℂ × ℂ) × ℂ => N q.1 q.2) (W ×ˢ Ω) :=
    wr_joint_of_holo_param (u := N) hWo hΩ (fun z _ => (hH z).1) (fun z _ => (hH z).2) hNz hz3 hzc
  have hPz : ∀ z : ℂ, ContDiffOn ℝ 3 (fun P => N P z) W := by
    intro z
    refine contDiffOn_of_locally_contDiffOn fun P₀ hP₀ => ?_
    obtain ⟨R, hR, hRW⟩ := Metric.isOpen_iff.1 hWo P₀ hP₀
    have hsub : closedBall P₀.1 (R / 2) ×ˢ closedBall P₀.2 (R / 2) ⊆ W := by
      intro P hP
      apply hRW
      rw [mem_ball, Prod.dist_eq, max_lt_iff]
      exact ⟨lt_of_le_of_lt hP.1 (by linarith), lt_of_le_of_lt hP.2 (by linarith)⟩
    have hcont : ContinuousOn (fun P : ℂ × ℂ => N P z) (closedBall P₀.1 (R / 2) ×ˢ closedBall P₀.2 (R / 2)) := by
      have h := ContinuousOn.comp (g := fun q : (ℂ × ℂ) × ℂ => N q.1 q.2)
        (f := fun P : ℂ × ℂ => (P, z)) hNc (continuous_id.prodMk continuous_const).continuousOn
        (fun (P : ℂ × ℂ) (hP : P ∈ closedBall P₀.1 (R / 2) ×ˢ closedBall P₀.2 (R / 2)) =>
          show (P, z) ∈ W ×ˢ univ from ⟨hsub hP, mem_univ _⟩)
      exact h
    have h₁ : ∀ b ∈ closedBall P₀.2 (R / 2), DifferentiableOn ℂ (fun a => N (a, b) z) (ball P₀.1 (R / 2)) :=
      fun b hb => ((hH z).1 b).mono fun a ha => hsub ⟨ball_subset_closedBall ha, hb⟩
    have h₂ : ∀ a ∈ closedBall P₀.1 (R / 2), DifferentiableOn ℂ (fun b => N (a, b) z) (ball P₀.2 (R / 2)) :=
      fun a ha => ((hH z).2 a).mono fun b hb => hsub ⟨ha, ball_subset_closedBall hb⟩
    refine ⟨ball P₀ (R / 4), isOpen_ball, mem_ball_self (by positivity), ?_⟩
    exact (wr_bidisc_contDiffOn (c := P₀) (by positivity) hcont h₁ h₂).mono
      (inter_subset_right.trans (ball_subset_ball (le_of_eq (by ring))))
  have hDW : ∀ q ∈ D, q.1 ∈ W := fun q hq => hq.1.1
  have hUj : ContDiffOn ℝ 3 (fun q : (ℂ × ℂ) × ℂ => U q.1 q.2) D := by
    intro q hq
    have hden : den (N q.1 (-1), N q.1 (-I), N q.1 q.2) ≠ 0 := hq.2.2.2.2
    have hin : ContDiffWithinAt ℝ 3 (fun q : (ℂ × ℂ) × ℂ => (N q.1 (-1), N q.1 (-I), N q.1 q.2)) D q :=
      (((hPz (-1)).comp contDiffOn_fst hDW).prodMk (((hPz (-I)).comp contDiffOn_fst hDW).prodMk
        (hJ.mono inter_subset_left))) q hq
    exact ((hΦd _ hden).restrict_scalars ℝ).comp_contDiffWithinAt q hin
  have hr : 0 < (1 - ‖a‖) / (2 * ‖μ‖ + 1) := div_pos (by linarith) (by positivity)
  refine ⟨(1 - ‖a‖) / (2 * ‖μ‖ + 1), hr, D, U, hDo, fun q hq => hq.1.2, ?_, ?_, hUj, ?_⟩
  · intro t ht z hz hpole
    have hnt : ‖((t, conj t) : ℂ × ℂ)‖ = ‖t‖ := by rw [Prod.norm_mk, Complex.norm_conj, max_self]
    have ht' : (2 * ‖μ‖ + 1) * ‖t‖ < 1 - ‖a‖ := by
      rw [lt_div_iff₀ (by positivity)] at ht
      linarith
    have hP : ((t, conj t) : ℂ × ℂ) ∈ W := by
      show ‖a‖ + 2 * ‖μ‖ * ‖((t, conj t) : ℂ × ℂ)‖ < 1
      rw [hnt]
      nlinarith [norm_nonneg t, norm_nonneg μ]
    have hk : ‖a + t • μ‖ < 1 := by
      refine (norm_add_le _ _).trans_lt ?_
      rw [norm_smul]
      nlinarith [norm_nonneg t, norm_nonneg μ]
    have hμt : a + t • μ ∈ LinfStarBall := by simpa [LinfStarBall] using hk
    obtain ⟨M, hM, W', hW', hfin, -, hm1, hmi, hp1⟩ := wA_spec hμt
    have hWeq : W' = N (t, conj t) :=
      (QCV.qcv_ns_eq (norm_nonneg _) hk (extA_isBeltramiCoeff _) hW').symm.trans
        (QCV.qcv_ns_congr_ae (norm_nonneg _) hk (extA_isBeltramiCoeff _) (hcoef t))
    subst hWeq
    obtain ⟨K, hK⟩ := hW'.1
    obtain ⟨e, he⟩ := t1_homeomorph hK hW'.2.1
    have hinj : Function.Injective (N (t, conj t)) := by rw [← he]; exact e.injective
    have hW1 : N (t, conj t) 1 = 1 := hW'.2.2.2.1
    have hm1I : (-1 : ℂ) ≠ -I := by
      intro h; have := congrArg Complex.im h; simp at this
    have hmI1 : (-I : ℂ) ≠ 1 := by
      intro h; have := congrArg Complex.re h; simp at this
    have h12 := hinj.ne hm1I
    have h13 : N (t, conj t) (-1) ≠ 1 := by
      have h := hinj.ne (show (-1 : ℂ) ≠ 1 by norm_num)
      rwa [hW1] at h
    have h23 : N (t, conj t) (-I) ≠ 1 := by
      have h := hinj.ne hmI1
      rwa [hW1] at h
    have e₁ := (hfin (-1)).symm.trans hm1
    have e₂ := (hfin (-I)).symm.trans hmi
    have e₃ : M ((1 : ℂ) : ExtPlane) = ((1 : ℂ) : ExtPlane) := by
      have h := (hfin 1).symm.trans hp1
      rwa [hW1] at h
    have hMN := wr_three_point hM h12 h13 h23 e₁ e₂ e₃
    have hz' := hfin z
    rw [hMN] at hz'
    have hden : (-(-I - -1) * (N (t, conj t) (-I) - 1) + (-I - 1) * (N (t, conj t) (-I) - N (t, conj t) (-1))) *
        N (t, conj t) z + (-(-I - -1) * (-(N (t, conj t) (-1) * (N (t, conj t) (-I) - 1))) +
          (-I - 1) * (-(1 * (N (t, conj t) (-I) - N (t, conj t) (-1))))) ≠ 0 := by
      intro h0
      rw [mobiusExt_coe_of_eq_zero h0] at hz'
      exact hpole hz'
    refine ⟨⟨⟨hP, hz⟩, ⟨sub_ne_zero.2 h12, sub_ne_zero.2 h13, sub_ne_zero.2 h23, hden⟩⟩, ?_⟩
    show _ = finPart (wAS (a + t • μ) (z : ExtPlane))
    rw [hz', mobiusExt_coe hden]
    rfl
  · intro q hq
    have hden : den (N q.1 (-1), N q.1 (-I), N q.1 q.2) ≠ 0 := hq.2.2.2.2
    have hW : q.1 ∈ W := hq.1.1
    have hd1 : ∀ z, DifferentiableAt ℂ (fun b => N (b, q.1.2) z) q.1.1 := fun z =>
      ((hH z).1 q.1.2).differentiableAt ((hWo.preimage (continuous_id.prodMk continuous_const)).mem_nhds hW)
    have hd2 : ∀ z, DifferentiableAt ℂ (fun b => N (q.1.1, b) z) q.1.2 := fun z =>
      ((hH z).2 q.1.1).differentiableAt ((hWo.preimage (continuous_const.prodMk continuous_id)).mem_nhds hW)
    have hΦq : DifferentiableAt ℂ Φ (N (q.1.1, q.1.2) (-1), N (q.1.1, q.1.2) (-I), N (q.1.1, q.1.2) q.2) :=
      (hΦd _ hden).differentiableAt (by norm_num)
    have e1 := hΦq.comp q.1.1 ((hd1 (-1)).prodMk ((hd1 (-I)).prodMk (hd1 q.2)))
    have e2 := hΦq.comp q.1.2 ((hd2 (-1)).prodMk ((hd2 (-I)).prodMk (hd2 q.2)))
    exact ⟨e1, e2⟩
  · intro q hq
    have hden : den (N q.1 (-1), N q.1 (-I), N q.1 q.2) ≠ 0 := hq.2.2.2.2
    have h12 : N q.1 (-1) ≠ N q.1 (-I) := sub_ne_zero.1 hq.2.1
    have h13 : N q.1 (-1) ≠ 1 := sub_ne_zero.1 hq.2.2.1
    have h23 : N q.1 (-I) ≠ 1 := sub_ne_zero.1 hq.2.2.2.1
    set φ : ℂ → ℂ := fun w => Φ (N q.1 (-1), N q.1 (-I), w) with hφdef
    have hΦq : DifferentiableAt ℂ Φ (N q.1 (-1), N q.1 (-I), N q.1 q.2) :=
      (hΦd _ hden).differentiableAt (by norm_num)
    have hin : DifferentiableAt ℂ (fun w : ℂ => (N q.1 (-1), N q.1 (-I), w)) (N q.1 q.2) := by fun_prop
    have hφ0 := hΦq.comp (N q.1 q.2) hin
    have hφ : DifferentiableAt ℂ φ (N q.1 q.2) := hφ0
    have hNd : DifferentiableAt ℝ (N q.1) q.2 :=
      ((hz3 q.1 hq.1.1).contDiffAt (hΩ.mem_nhds hq.1.2)).differentiableAt (by norm_num)
    have hc := ra_dz_comp_holo hφ hNd
    have hj := wr3_jacobian_pos hΩ hs₀ hs₁ hs₂ (hWk q.1 hq.1.1) hq.1.2
    change 0 < ‖dz (N q.1) q.2‖ ^ 2 - ‖dzbar (N q.1) q.2‖ ^ 2 at hj
    have hm := s35g_mob_deriv h12 h13 h23 hden
    rw [show U q.1 = φ ∘ N q.1 from rfl, hc.1, hc.2, norm_mul, norm_mul, mul_pow, mul_pow, ← mul_sub]
    exact mul_pos (pow_pos (norm_pos_iff.2 hm) 2) hj

/-- [GFAM helper] On `𝔻`, the Model A coefficient is conjugate-linear: `extA (a + e μ) = extA a + ē extA μ` a.e. -/
theorem d2g_extA_disc_lin (a μ : LinfStar) (e : ℂ) :
    ∀ᵐ z, z ∈ unitDisc → extA (a + e • μ) z = extA a z + conj e * extA μ z := by
  have hE : MeasurableSet unitDiscExterior := (isOpen_lt continuous_const continuous_norm).measurableSet
  have h1 : ∀ᵐ w ∂(volume.restrict unitDiscExterior), (a + e • μ) w = a w + e * μ w := by
    filter_upwards [Lp.coeFn_add a (e • μ), Lp.coeFn_smul e μ] with w h1 h2
    rw [h1, Pi.add_apply, h2, Pi.smul_apply, smul_eq_mul]
  have h2 : ∀ᵐ w, w ∈ unitDiscExterior → (a + e • μ) w = a w + e * μ w := (ae_restrict_iff' hE).1 h1
  filter_upwards [ae_refl h2] with z hz hzD
  have hz1 : ‖z‖ < 1 := mem_ball_zero_iff.1 hzD
  have hn : ¬ 1 < ‖z‖ := by linarith
  by_cases hz0 : z = 0
  · subst hz0
    simp [extA, show ¬ (1 : ℝ) < 0 by norm_num]
  have hr : refl z ∈ unitDiscExterior := by
    show 1 < ‖refl z‖
    have : ‖refl z‖ = ‖z‖⁻¹ := by
      show ‖(conj z)⁻¹‖ = ‖z‖⁻¹
      rw [norm_inv, Complex.norm_conj]
    rw [this]
    exact one_lt_inv₀ (norm_pos_iff.2 hz0) |>.2 hz1
  have e1 : ∀ ν : LinfStar, extA ν z = conj (ν (refl z)) * z ^ 2 / conj z ^ 2 := fun ν => by
    simp only [extA, if_neg hn, if_pos hz1]
  rw [e1, e1, e1, hz hr, map_add, map_mul]
  ring

/-- [GFAM helper] **Disc representative.** For harmonic `ν = (1 - |w|²)² φ̄`, `extA ν = (1 - |z|²)² ψ(z̄)` a.e. on `𝔻`,
with `ψ(s) = φ(1/s)/s⁴` holomorphic on `𝔻` (removable singularity at `0`, by the `A∞` weight). -/
theorem d2g_disc_rep {ν : LinfStar} (hν : ν ∈ harmonicBeltrami) :
    ∃ p : ℂ → ℂ, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) p unitDisc ∧ ∀ᵐ z, z ∈ unitDisc → extA ν z = p z := by
  obtain ⟨φ, hφ⟩ := (mem_harmonicBeltrami_iff ν).1 hν
  have hE : MeasurableSet unitDiscExterior := (isOpen_lt continuous_const continuous_norm).measurableSet
  have hEo : IsOpen unitDiscExterior := isOpen_lt continuous_const continuous_norm
  obtain ⟨f, hf⟩ : ∃ f : ℂ → ℂ, f = AInf.toFun φ := ⟨_, rfl⟩
  have hfd : DifferentiableOn ℂ f unitDiscExterior := by
    rw [hf]
    exact (φ.2 : DifferentiableOn ℂ (AInf.toFun φ) unitDiscExterior)
  have hfb : ∀ w ∈ unitDiscExterior, ‖f w‖ * (‖w‖ ^ 2 - 1) ^ 2 ≤ ‖φ.1‖ := by
    intro w hw
    have hw1 : 1 < ‖w‖ := hw
    have h0 : (1 - (‖w‖ : ℂ) ^ 2) ≠ 0 := by
      intro h
      have : ‖w‖ ^ 2 = 1 := by exact_mod_cast (sub_eq_zero.1 h).symm
      nlinarith
    have hfw : f w = φ.1 ⟨w, hw⟩ / (1 - (‖w‖ : ℂ) ^ 2) ^ 2 := by
      rw [hf]
      show unweight unitDiscExterior φ.1 w = _
      simp only [unweight, dif_pos hw]
    have hn : ‖(1 - (‖w‖ : ℂ) ^ 2) ^ 2‖ = (‖w‖ ^ 2 - 1) ^ 2 := by
      rw [norm_pow, show (1 - (‖w‖ : ℂ) ^ 2) = ((1 - ‖w‖ ^ 2 : ℝ) : ℂ) by push_cast; rfl, Complex.norm_real,
        Real.norm_eq_abs, sq_abs]
      ring
    have hpos : 0 < ‖w‖ ^ 2 - 1 := by nlinarith
    rw [hfw, norm_div, hn, div_mul_cancel₀ _ (pow_ne_zero 2 hpos.ne')]
    exact BoundedContinuousFunction.norm_coe_le_norm φ.1 _
  -- `ψ(s) = f(1/s)/s⁴`
  obtain ⟨ψ0, hψ0⟩ : ∃ ψ : ℂ → ℂ, ψ = fun s => f s⁻¹ / s ^ 4 := ⟨_, rfl⟩
  have hinvE : ∀ s : ℂ, s ≠ 0 → ‖s‖ < 1 → s⁻¹ ∈ unitDiscExterior := fun s hs0 hs1 => by
    show 1 < ‖s⁻¹‖
    rw [norm_inv]
    exact (one_lt_inv₀ (norm_pos_iff.2 hs0)).2 hs1
  have hψd : DifferentiableOn ℂ ψ0 (unitDisc \ {0}) := by
    intro s hs
    have hs0 : s ≠ 0 := hs.2
    have hs1 : ‖s‖ < 1 := mem_ball_zero_iff.1 hs.1
    have hd : DifferentiableAt ℂ f s⁻¹ := hfd.differentiableAt (hEo.mem_nhds (hinvE s hs0 hs1))
    rw [hψ0]
    exact ((hd.comp s (differentiableAt_inv hs0)).div (differentiableAt_pow 4) (pow_ne_zero 4 hs0)).differentiableWithinAt
  have hψb : ∀ s : ℂ, s ≠ 0 → ‖s‖ < 1 / 2 → ‖ψ0 s‖ ≤ 16 / 9 * ‖φ.1‖ := by
    intro s hs0 hs1
    have hsp : 0 < ‖s‖ := norm_pos_iff.2 hs0
    have hb := hfb _ (hinvE s hs0 (by linarith))
    rw [norm_inv] at hb
    rw [hψ0]
    show ‖f s⁻¹ / s ^ 4‖ ≤ _
    rw [norm_div, norm_pow, div_le_iff₀ (by positivity)]
    have e : (‖s‖⁻¹ ^ 2 - 1) ^ 2 = (1 - ‖s‖ ^ 2) ^ 2 / ‖s‖ ^ 4 := by field_simp
    rw [e, ← mul_div_assoc, div_le_iff₀ (by positivity)] at hb
    have h34 : (3 / 4 : ℝ) ^ 2 ≤ (1 - ‖s‖ ^ 2) ^ 2 := by
      apply pow_le_pow_left₀ (by norm_num)
      nlinarith
    have hφ0 : 0 ≤ ‖φ.1‖ := norm_nonneg _
    nlinarith [mul_le_mul_of_nonneg_left h34 (norm_nonneg (f s⁻¹)), pow_pos hsp 4]
  have hrem := Complex.differentiableOn_update_limUnder_of_bddAbove (f := ψ0) (s := ball (0 : ℂ) (1 / 2)) (c := 0)
    (ball_mem_nhds _ (by norm_num))
    (hψd.mono fun s hs => ⟨ball_subset_ball (by norm_num) hs.1, hs.2⟩)
    ⟨16 / 9 * ‖φ.1‖, by
      rintro _ ⟨s, hs, rfl⟩
      exact hψb s hs.2 (mem_ball_zero_iff.1 hs.1)⟩
  obtain ⟨ψ, hψ⟩ : ∃ ψ : ℂ → ℂ, ψ = Function.update ψ0 0 (limUnder (𝓝[≠] (0 : ℂ)) ψ0) := ⟨_, rfl⟩
  have hψD : DifferentiableOn ℂ ψ unitDisc := by
    intro s hs
    by_cases hs0 : s = 0
    · subst hs0
      rw [hψ]
      exact (hrem 0 (mem_ball_self (by norm_num))).differentiableAt (ball_mem_nhds _ (by norm_num))
        |>.differentiableWithinAt
    · have heq : ψ0 =ᶠ[𝓝 s] ψ := by
        filter_upwards [isOpen_ne.mem_nhds hs0] with w hw
        rw [hψ, Function.update_of_ne hw]
      exact ((hψd s ⟨hs, hs0⟩).differentiableAt
        ((isOpen_ball.sdiff isClosed_singleton).mem_nhds ⟨hs, hs0⟩)).congr_of_eventuallyEq heq.symm
        |>.differentiableWithinAt
  -- the representative
  refine ⟨fun z => (((1 - ‖z‖ ^ 2 : ℝ)) : ℂ) ^ 2 * ψ (conj z), ?_, ?_⟩
  · have h1 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : ℂ => (((1 - ‖z‖ ^ 2 : ℝ)) : ℂ) ^ 2) :=
      (Complex.ofRealCLM.contDiff.comp (contDiff_const.sub (contDiff_norm_sq ℝ))).pow 2
    have h2 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ unitDisc :=
      (hψD.contDiffOn isOpen_ball).restrict_scalars ℝ
    have h3 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z => ψ (conj z)) unitDisc :=
      h2.comp (conjCLE : ℂ ≃L[ℝ] ℂ).contDiff.contDiffOn fun z hz => by
        show conj z ∈ ball (0 : ℂ) 1
        rw [mem_ball_zero_iff, Complex.norm_conj]
        exact mem_ball_zero_iff.1 hz
    exact h1.contDiffOn.mul h3
  · have h2 : ∀ᵐ w, w ∈ unitDiscExterior → ν w = (1 - ‖w‖ ^ 2) ^ 2 * conj (AInf.toFun φ w) :=
      (ae_restrict_iff' hE).1 hφ
    filter_upwards [ae_refl h2, measure_eq_zero_iff_ae_notMem.1 (measure_singleton (0 : ℂ))] with z hz hz0' hzD
    have hz1 : ‖z‖ < 1 := mem_ball_zero_iff.1 hzD
    have hn : ¬ 1 < ‖z‖ := by linarith
    have hz0 : z ≠ 0 := hz0'
    have hc0 : conj z ≠ 0 := (map_ne_zero _).2 hz0
    have hr : refl z ∈ unitDiscExterior := by
      have h := hinvE (conj z) hc0 (by rw [Complex.norm_conj]; exact hz1)
      exact h
    have hrz : refl z = (conj z)⁻¹ := rfl
    have hnr : ‖refl z‖ = ‖z‖⁻¹ := by rw [hrz, norm_inv, Complex.norm_conj]
    have hψz : ψ (conj z) = f (conj z)⁻¹ / conj z ^ 4 := by
      rw [hψ, Function.update_of_ne hc0, hψ0]
    have hzc : z * conj z = ((‖z‖ : ℝ) : ℂ) ^ 2 := Complex.mul_conj' z
    have hnz : (‖z‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (norm_ne_zero_iff.2 hz0)
    show extA ν z = (((1 - ‖z‖ ^ 2 : ℝ)) : ℂ) ^ 2 * ψ (conj z)
    simp only [extA, if_neg hn, if_pos hz1]
    rw [hz hr, ← hf, hψz, hnr, ← hrz]
    simp only [map_mul, map_pow, map_sub, map_one, conj_conj, Complex.conj_ofReal]
    rw [hrz]
    have hz' : z = ((‖z‖ : ℝ) : ℂ) ^ 2 / conj z := by
      field_simp
      exact hzc
    generalize hF : f (conj z)⁻¹ = F
    generalize hn : ‖z‖ = n at hz' hnz ⊢
    generalize hc : conj z = c at hz' hc0 ⊢
    rw [hz']
    push_cast
    field_simp
    ring

/-- **(F1)** The Model A family on `𝔻*`: `s35g_family` plus joint `C³` and positive Jacobian. -/
theorem d2g_family_ext {a μ : LinfStar} (ha : a ∈ harmonicBeltrami) (ha1 : ‖a‖ < 1) (hμ : μ ∈ harmonicBeltrami) :
    ∃ r > 0, ∃ D : Set ((ℂ × ℂ) × ℂ), ∃ U : ℂ × ℂ → ℂ → ℂ, IsOpen D ∧
      (∀ q ∈ D, q.2 ∈ unitDiscExterior) ∧
      (∀ t : ℂ, ‖t‖ < r → ∀ z ∈ unitDiscExterior, wAS (a + t • μ) (z : ExtPlane) ≠ extInf →
        ((t, conj t), z) ∈ D ∧ U (t, conj t) z = wA (a + t • μ) z) ∧
      (∀ q ∈ D, DifferentiableAt ℂ (fun b => U (b, q.1.2) q.2) q.1.1 ∧
        DifferentiableAt ℂ (fun b => U (q.1.1, b) q.2) q.1.2) ∧
      ContDiffOn ℝ 3 (fun q : (ℂ × ℂ) × ℂ => U q.1 q.2) D ∧
      ∀ q ∈ D, 0 < ‖dz (U q.1) q.2‖ ^ 2 - ‖dzbar (U q.1) q.2‖ ^ 2 := by
  obtain ⟨m₀, m₁, hm₀, hm₁, hs₀, hs₁, hcoef⟩ := wr3_coeffs ha hμ
  have hm₂ : IsBeltramiCoeff (unitDisc.indicator (extA μ)) univ ‖μ‖ :=
    ⟨(extA_isBeltramiCoeff μ).1.indicator isOpen_ball.measurableSet,
      (extA_isBeltramiCoeff μ).2.mono fun u hu => (norm_indicator_le_norm_self _ _).trans hu⟩
  have hΩ : IsOpen unitDiscExterior := isOpen_lt continuous_const continuous_norm
  have hs₂ : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (unitDisc.indicator (extA μ)) unitDiscExterior :=
    contDiffOn_const.congr fun u hu =>
      indicator_of_notMem (fun h => (not_lt_of_ge (le_of_lt hu)) (mem_ball_zero_iff.mp h)) _
  exact d2g_family_gen ha1 hΩ hm₀ hm₁ hm₂ hs₀ hs₁ hs₂ hcoef

/-- **(F2)** The Model A family on `𝔻` (the same construction with `Ω = 𝔻`). -/
theorem d2g_family_disc {a μ : LinfStar} (ha : a ∈ harmonicBeltrami) (ha1 : ‖a‖ < 1) (hμ : μ ∈ harmonicBeltrami) :
    ∃ r > 0, ∃ D : Set ((ℂ × ℂ) × ℂ), ∃ U : ℂ × ℂ → ℂ → ℂ, IsOpen D ∧
      (∀ q ∈ D, q.2 ∈ unitDisc) ∧
      (∀ t : ℂ, ‖t‖ < r → ∀ z ∈ unitDisc, wAS (a + t • μ) (z : ExtPlane) ≠ extInf →
        ((t, conj t), z) ∈ D ∧ U (t, conj t) z = wA (a + t • μ) z) ∧
      (∀ q ∈ D, DifferentiableAt ℂ (fun b => U (b, q.1.2) q.2) q.1.1 ∧
        DifferentiableAt ℂ (fun b => U (q.1.1, b) q.2) q.1.2) ∧
      ContDiffOn ℝ 3 (fun q : (ℂ × ℂ) × ℂ => U q.1 q.2) D ∧
      ∀ q ∈ D, 0 < ‖dz (U q.1) q.2‖ ^ 2 - ‖dzbar (U q.1) q.2‖ ^ 2 := by
  obtain ⟨m₀, m₁, hm₀, hm₁, -, -, hcoef⟩ := wr3_coeffs ha hμ
  obtain ⟨p₀, hp₀s, hp₀e⟩ := d2g_disc_rep ha
  obtain ⟨p₂, hp₂s, hp₂e⟩ := d2g_disc_rep hμ
  have hD : IsOpen unitDisc := isOpen_ball
  have hDm : MeasurableSet unitDisc := measurableSet_ball
  obtain ⟨n₀, hn₀⟩ : ∃ n : ℂ → ℂ, n = fun u => unitDisc.indicator p₀ u + unitDiscᶜ.indicator m₀ u := ⟨_, rfl⟩
  obtain ⟨n₁, hn₁⟩ : ∃ n : ℂ → ℂ, n = unitDiscᶜ.indicator m₁ := ⟨_, rfl⟩
  obtain ⟨n₂, hn₂⟩ : ∃ n : ℂ → ℂ, n = unitDisc.indicator p₂ := ⟨_, rfl⟩
  have hin : ∀ u ∈ unitDisc, n₀ u = p₀ u ∧ n₁ u = 0 ∧ n₂ u = p₂ u := fun u hu => by
    rw [hn₀, hn₁, hn₂]
    simp [indicator_of_mem hu, indicator_of_notMem (show u ∉ unitDiscᶜ from fun h => h hu)]
  have hout : ∀ u ∉ unitDisc, n₀ u = m₀ u ∧ n₁ u = m₁ u ∧ n₂ u = 0 := fun u hu => by
    rw [hn₀, hn₁, hn₂]
    simp [indicator_of_notMem hu, indicator_of_mem (show u ∈ unitDiscᶜ from hu)]
  -- smoothness on `𝔻`
  have hs₀ : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) n₀ unitDisc := hp₀s.congr fun u hu => (hin u hu).1
  have hs₁ : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) n₁ unitDisc := contDiffOn_const.congr fun u hu => (hin u hu).2.1
  have hs₂ : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) n₂ unitDisc := hp₂s.congr fun u hu => (hin u hu).2.2
  -- measurability and bounds
  have hpm : ∀ {p : ℂ → ℂ}, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) p unitDisc →
      AEStronglyMeasurable (unitDisc.indicator p) volume := fun {p} hp =>
    (aestronglyMeasurable_indicator_iff hDm).2 (hp.continuousOn.aestronglyMeasurable hDm)
  have hA := extA_isBeltramiCoeff a
  have hM := extA_isBeltramiCoeff μ
  have hb₀ : IsBeltramiCoeff n₀ univ ‖a‖ := by
    refine ⟨?_, ?_⟩
    · rw [hn₀]
      exact (hpm hp₀s).restrict.add ((aestronglyMeasurable_indicator_iff hDm.compl).2 hm₀.1.restrict)
    · filter_upwards [hm₀.2, hA.2, ae_restrict_of_ae hp₀e] with u h1 h2 h3
      by_cases hu : u ∈ unitDisc
      · rw [(hin u hu).1, ← h3 hu]
        exact h2
      · rw [(hout u hu).1]
        exact h1
  have hb₁ : IsBeltramiCoeff n₁ univ ‖μ‖ := by
    refine ⟨?_, ?_⟩
    · rw [hn₁]
      exact (aestronglyMeasurable_indicator_iff hDm.compl).2 hm₁.1.restrict
    · filter_upwards [hm₁.2] with u h1
      by_cases hu : u ∈ unitDisc
      · rw [(hin u hu).2.1, norm_zero]
        exact norm_nonneg _
      · rw [(hout u hu).2.1]
        exact h1
  have hb₂ : IsBeltramiCoeff n₂ univ ‖μ‖ := by
    refine ⟨?_, ?_⟩
    · rw [hn₂]
      exact (hpm hp₂s).restrict
    · filter_upwards [hM.2, ae_restrict_of_ae hp₂e] with u h2 h3
      by_cases hu : u ∈ unitDisc
      · rw [(hin u hu).2.2, ← h3 hu]
        exact h2
      · rw [(hout u hu).2.2, norm_zero]
        exact norm_nonneg _
  -- the coefficient relation
  have hcoef' : ∀ e : ℂ, extA (a + e • μ) =ᵐ[volume] (fun u => n₀ u + e * n₁ u + conj e * n₂ u) := by
    intro e
    filter_upwards [hcoef e, d2g_extA_disc_lin a μ e, hp₀e, hp₂e] with u h1 h2 h3 h4
    by_cases hu : u ∈ unitDisc
    · obtain ⟨e0, e1, e2⟩ := hin u hu
      rw [e0, e1, e2, h2 hu, h3 hu, h4 hu]
      ring
    · obtain ⟨e0, e1, e2⟩ := hout u hu
      rw [e0, e1, e2, h1, indicator_of_notMem hu]
  exact d2g_family_gen ha1 hD hb₀ hb₁ hb₂ hs₀ hs₁ hs₂ hcoef'

end TakhtajanTeo.Ch2
