import TakhtajanTeo.Ch1.S5Thm53Grunsky
import TakhtajanTeo.Ch1.S5VerticalCurvature
import TakhtajanTeo.Ch1.S5RightTranslationHol
import TakhtajanTeo.Ch1.TCurveSchwarzianTransport
import TakhtajanTeo.Ch1.S5TCurveGroup

/-!
# `prop_5_7` (`s5p57_`, 下属5, Program G)

Host: `TakhtajanTeo/Ch1/S5Prop57.lean` (plan `collaboration/下属5/SCOUT_P57.md`).

Notation: `q_z = fiberPt z = (0, z)`, `L_z = d(R_{q_z⁻¹})` in the coordinates `tcCoordH`, so
`vkNormSq q_z = vkNormSqCoordOrigin ∘ L_z`.

* P0: by `thm_5_3` and `s5t53_levi_log_K`, `Θ(X, Y) = -2 h_VK(X, Y)` on `𝒯(1)`. Hence (ii) is `-2·`(i).
* P1: `h_VK` is positive definite. Its parts:
  - `vkNormSqCoordOrigin` is positive definite, using summability from `s5gr_`;
  - `L_q` is injective.
* P2: vertical norm, from `s5vc_prop_5_7_vertical`.
* P3: `(L_z X).1 = (σ_z⁻¹)^* X.1`, and `(L_z ∂_z).1 = 0`.
* P4: `(L_z τ_μ).2 = 0`.
* P5: `(0, a) ⊥ (ψ, 0)`, and `‖((σ_z⁻¹)^* D₀β(μ), 0)‖²_VK = ½ G(|μ|²)(z)` (via `lemma_5_8`).
-/

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal ComplexConjugate Classical Real

noncomputable section

namespace TakhtajanTeo

open LiZhongQC Ch2

/-- **Stub P0.** `Θ(X, Y) = -2 h_VK(X, Y)` on `𝒯(1)` (`thm_5_3`, `s5t53_levi_log_K`). -/
theorem s5p57_theta_vk {q : T1 × ExtPlane} (hq : q ∈ TCurve) (X Y : AInf unitDisc × ℂ) :
    thetaForm q X Y = -2 * polarize (vkNormSq q) X Y := by
  have h : leviTC logNormSq q = fun Y => 2 * vkNormSq q Y := by
    funext Y
    rw [s5t53_levi_log_K hq, thm_5_3.2 q hq Y]
  show -polarize (leviTC logNormSq q) X Y = _
  rw [h]
  simp only [polarize]
  push_cast
  ring

/-- The VK series at the origin is the `ℓ²` norm of `ċ` along the curve pair (`s5gr_`), so it converges: with
`a_0 = Y.2`, `a_j = i·c_{j+1}`, `Σ_j (j + 1)|a_j|² = ‖Y‖²_VK`. -/
theorem s5p57_vk_hasSum (Y : AInf unitDisc × ℂ) :
    HasSum (fun j : ℕ => ((j : ℝ) + 1) * ‖(if j = 0 then Y.2 else I * tangentCoeff Y.1 (j + 1))‖ ^ 2)
      (vkNormSqCoordOrigin Y) := by
  obtain ⟨ε, hε, F, G, hFG, han, h0, hjet⟩ := s5gr_curve_pair Y
  set k : ℂ → ℝ := fun τ => potentialK (tcCoordHInv (τ • Y)) with hkdef
  -- continuity of `K` along the line
  have hkc : ContinuousAt k 0 := by
    have hx0 : tcCoordH tOrigin = 0 := by
      rw [← Prod.mk_zero_zero]
      exact s5t53_tcCoordH_origin
    have hreg := s5l54_regular s5rh_tOrigin_mem
    rw [hx0] at hreg
    have ha : ContDiffAt ℝ 2 (fun t : ℂ => t • Y) 0 := (contDiff_id.smul contDiff_const).contDiffAt
    have hg' : ContDiffAt ℝ 2 (fun w : AInf unitDisc × ℂ => logNormSq (tcCoordHInv w))
        ((fun t : ℂ => t • Y) 0) := by
      simpa using hreg
    have hc : ContDiffAt ℝ 2 (fun t : ℂ => logNormSq (tcCoordHInv (t • Y))) 0 :=
      ContDiffAt.comp (g := fun w : AInf unitDisc × ℂ => logNormSq (tcCoordHInv w))
        (f := fun t : ℂ => t • Y) 0 hg' ha
    exact ((hc.div_const 2).sub contDiffAt_const).continuousAt
  obtain ⟨ε1, hε1, hk1⟩ := Metric.continuousAt_iff.mp hkc 1 one_pos
  set ε2 := min ε ε1 with hε2
  have hε2p : 0 < ε2 := lt_min hε hε1
  have hsub : ∀ τ ∈ ball (0 : ℂ) ε2, τ ∈ ball (0 : ℂ) ε ∧ dist τ 0 < ε1 := fun τ hτ =>
    ⟨ball_subset_ball (min_le_left _ _) hτ, lt_of_lt_of_le (mem_ball.mp hτ) (min_le_right _ _)⟩
  have hM : ∀ τ ∈ ball (0 : ℂ) ε2, Real.log (‖derivAtInfty (G τ)‖ ^ 2) ≤ 2 * (|k 0| + 1) := by
    intro τ hτ
    obtain ⟨h1, h2⟩ := hsub τ hτ
    rw [Real.log_pow, ← (hFG τ h1).2.2.1]
    have h3 := hk1 h2
    rw [Real.dist_eq] at h3
    push_cast
    have : k τ ≤ |k 0| + 1 := by
      have := abs_lt.mp h3
      linarith [le_abs_self (k 0)]
    show 2 * k τ ≤ _
    linarith
  have hpair2 : ∀ τ ∈ ball (0 : ℂ) ε2, IsNormalizedDisjointPair (F τ) (G τ) ∧
      volume ((F τ '' unitDisc ∪ G τ '' unitDiscExterior)ᶜ) = 0 :=
    fun τ hτ => ⟨(hFG τ (hsub τ hτ).1).1, (hFG τ (hsub τ hτ).1).2.1⟩
  have han2 : AnalyticOnNhd ℂ (fun p : ℂ × ℂ => F p.1 p.2) (ball 0 ε2 ×ˢ unitDisc) :=
    han.mono (prod_mono (ball_subset_ball (min_le_left _ _)) subset_rfl)
  obtain ⟨r, hr, C, hcs, hW⟩ := s5gr_family_bounds hε2p hpair2 han2 h0 hM
  -- the derivative vector and the VK norm
  set a : ℕ → ℂ := fun n => if n = 0 then Y.2 else I * tangentCoeff Y.1 (n + 1) with ha
  have hcd : ∀ j : ℕ, deriv (fun τ => (Real.sqrt ((j : ℝ) + 1) : ℂ) * grunsky (F τ) (G τ) (-((j : ℤ) + 1)) 0) 0 =
      -((Real.sqrt ((j : ℝ) + 1) : ℂ) * a j) :=
    s5gr_cdot hε2p (fun τ hτ => (hpair2 τ hτ).1) han2 h0 hjet
  set w : ell2 := ⟨_, gop_mem_of_summable hcs⟩ with hw
  have e1 : ∀ j : ℕ, ‖w j‖ ^ 2 = ((j : ℝ) + 1) * ‖a j‖ ^ 2 := by
    intro j
    show ‖deriv (fun τ => (Real.sqrt ((j : ℝ) + 1) : ℂ) * grunsky (F τ) (G τ) (-((j : ℤ) + 1)) 0) 0‖ ^ 2 = _
    rw [hcd j, norm_neg, s5gr_sqrt_norm_sq]
  have hs : Summable (fun j : ℕ => ((j : ℝ) + 1) * ‖a j‖ ^ 2) := (gop_l2_summable w).congr e1
  have ht : (∑' j : ℕ, ((j : ℝ) + 1) * ‖a j‖ ^ 2) = vkNormSqCoordOrigin Y := by
    rw [hs.tsum_eq_zero_add]
    unfold vkNormSqCoordOrigin
    simp only [ha, Nat.cast_zero, zero_add, one_mul, if_true, Nat.succ_ne_zero, if_false, norm_mul,
      Complex.norm_I, mul_pow, one_pow]
    rw [add_comm]
    congr 1
    refine tsum_congr fun n => ?_
    push_cast
    ring
  rw [← ht]
  exact hs.hasSum

/-- **Stub P1a.** `‖·‖²_VK` at the origin is positive definite: the series `Σ (n + 2)|c_{n+2}|²` is summable for every
`φ ∈ A_∞(𝔻)` (`s5gr_curve_pair`, `s5gr_family_bounds`, `s5gr_cdot`), and it vanishes only for `φ = 0`. -/
theorem s5p57_origin_pos {Y : AInf unitDisc × ℂ} (hY : Y ≠ 0) : 0 < vkNormSqCoordOrigin Y := by
  have hS := s5p57_vk_hasSum Y
  by_contra hle
  push_neg at hle
  have hnn : ∀ j : ℕ, 0 ≤ ((j : ℝ) + 1) * ‖(if j = 0 then Y.2 else I * tangentCoeff Y.1 (j + 1))‖ ^ 2 :=
    fun j => by positivity
  have h0 : vkNormSqCoordOrigin Y = 0 := le_antisymm hle (hS.nonneg hnn)
  rw [h0] at hS
  have hz := (hasSum_zero_iff_of_nonneg hnn).mp hS
  have hc : ∀ j : ℕ, (if j = 0 then Y.2 else I * tangentCoeff Y.1 (j + 1)) = 0 := by
    intro j
    have h1 := congrFun hz j
    simp only [Pi.zero_apply] at h1
    have hpos : (0 : ℝ) < (j : ℝ) + 1 := by positivity
    have h2 := (mul_eq_zero.mp h1).resolve_left hpos.ne'
    exact norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp h2)
  have hY2 : Y.2 = 0 := by simpa using hc 0
  have hT : ∀ k : ℕ, iteratedDeriv k (AInf.toFun Y.1) 0 = 0 := by
    intro k
    have h := hc (k + 1)
    simp only [Nat.add_one_ne_zero, if_false, mul_eq_zero, Complex.I_ne_zero, false_or] at h
    have hD : (((k + 1 + 1 : ℕ) : ℂ) ^ 3 - ((k + 1 + 1 : ℕ) : ℂ)) ≠ 0 := by
      have hn : ((k + 1) * (k + 2) * (k + 3) : ℕ) ≠ 0 := by positivity
      have e : (((k + 1 + 1 : ℕ) : ℂ) ^ 3 - ((k + 1 + 1 : ℕ) : ℂ)) = (((k + 1) * (k + 2) * (k + 3) : ℕ) : ℂ) := by
        push_cast; ring
      rw [e]; exact_mod_cast hn
    have hf : ((k.factorial : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
    have h' : iteratedDeriv (k + 1 + 1 - 2) (AInf.toFun Y.1) 0 / ((k + 1 + 1 - 2).factorial : ℂ) /
        (I * (((k + 1 + 1 : ℕ) : ℂ) ^ 3 - ((k + 1 + 1 : ℕ) : ℂ))) = 0 := h
    rw [show k + 1 + 1 - 2 = k by omega] at h'
    rcases div_eq_zero_iff.mp h' with h3 | h3
    · rcases div_eq_zero_iff.mp h3 with h4 | h4
      · exact h4
      · exact absurd h4 hf
    · exact absurd h3 (mul_ne_zero Complex.I_ne_zero hD)
  have hY1 : Y.1 = 0 := by
    apply AInf.ext_toFun_disc
    intro u hu
    have hTs : HasSum (fun n : ℕ => ((n.factorial : ℂ))⁻¹ • (u - 0) ^ n • iteratedDeriv n (AInf.toFun Y.1) 0)
        (AInf.toFun Y.1 u) := Complex.hasSum_taylorSeries_on_ball Y.1.property hu
    simp only [hT, smul_zero] at hTs
    rw [s5tg_toFun_zero]
    exact hTs.unique hasSum_zero
  exact hY (Prod.ext hY1 hY2)

/-- The pullback `(σ_z⁻¹)^* φ` lies in `A_∞(𝔻)`, with norm at most `‖φ‖`. -/
theorem s5p57_pull_spec {z : ℂ} (hz : z ∈ unitDiscExterior) (φ : AInf unitDisc) :
    (∀ u ∈ unitDisc, AInf.toFun (toAInf unitDisc (fun u => AInf.toFun φ (sigmaInv z u) * deriv (sigmaInv z) u ^ 2)) u =
      AInf.toFun φ (sigmaInv z u) * deriv (sigmaInv z) u ^ 2) ∧
    ‖toAInf unitDisc (fun u => AInf.toFun φ (sigmaInv z u) * deriv (sigmaInv z) u ^ 2)‖ ≤ ‖φ‖ := by
  have hσ := wp_sigmaInv_disk_conformal hz
  have hFd : DifferentiableOn ℂ (fun u => AInf.toFun φ (sigmaInv z u) * deriv (sigmaInv z) u ^ 2) unitDisc :=
    (φ.property.comp hσ.1 hσ.mapsTo).mul ((hσ.1.deriv isOpen_ball).pow 2)
  refine toAInf_disc_spec_of_bound (norm_nonneg _) hFd fun u hu => ?_
  have h1 := wp_sigmaInv_pullback_norm (AInf.toFun φ) hz hu
  have h2 := wp_AInf_disc_weighted_bound φ (hσ.mapsTo hu)
  have e : (rho u)⁻¹ = (1 - ‖u‖ ^ 2) ^ 2 / 4 := by rw [rho, inv_div]
  rw [← h1, e] at h2
  nlinarith [h2]

/-- The pullback as a continuous linear operator on `A_∞(𝔻)`. -/
theorem s5p57_pull_clm {z : ℂ} (hz : z ∈ unitDiscExterior) :
    ∃ P : AInf unitDisc →L[ℂ] AInf unitDisc, ∀ φ, P φ =
      toAInf unitDisc (fun u => AInf.toFun φ (sigmaInv z u) * deriv (sigmaInv z) u ^ 2) := by
  have hadd : ∀ (φ ψ : AInf unitDisc) (u : ℂ), AInf.toFun (φ + ψ) u = AInf.toFun φ u + AInf.toFun ψ u := by
    intro φ ψ u
    show unweight unitDisc (φ + ψ).1 u = _
    rw [Submodule.coe_add, unweight_add]
    rfl
  have hsmul : ∀ (c : ℂ) (φ : AInf unitDisc) (u : ℂ), AInf.toFun (c • φ) u = c * AInf.toFun φ u := by
    intro c φ u
    show unweight unitDisc (c • φ).1 u = _
    rw [Submodule.coe_smul, unweight_smul]
    rfl
  refine ⟨LinearMap.mkContinuous
    { toFun := fun φ => toAInf unitDisc (fun u => AInf.toFun φ (sigmaInv z u) * deriv (sigmaInv z) u ^ 2)
      map_add' := fun φ ψ => ?_
      map_smul' := fun c φ => ?_ } 1 fun φ => ?_, fun φ => rfl⟩
  · apply AInf.ext_toFun_disc
    intro u hu
    rw [hadd, (s5p57_pull_spec hz (φ + ψ)).1 u hu, (s5p57_pull_spec hz φ).1 u hu,
      (s5p57_pull_spec hz ψ).1 u hu, hadd]
    ring
  · apply AInf.ext_toFun_disc
    intro u hu
    simp only [RingHom.id_apply]
    rw [hsmul, (s5p57_pull_spec hz (c • φ)).1 u hu, (s5p57_pull_spec hz φ).1 u hu, hsmul]
    ring
  · simp only [LinearMap.coe_mk, AddHom.coe_mk, one_mul]
    exact (s5p57_pull_spec hz φ).2

/-- The disk automorphism `S` of `tcg_mul_bers_coordinate` acts on `A_∞(𝔻)` by an injective continuous linear
pullback (`S = id` for the fibre point `∞`, `S = σ_{1/ā}⁻¹` otherwise). -/
theorem s5p57_S_pull {u : ExtPlane} (hu : u ∈ extDiscExterior) :
    ∃ P : AInf unitDisc →L[ℂ] AInf unitDisc, Function.Injective P ∧ ∀ ψ : AInf unitDisc, ∀ w ∈ unitDisc,
      AInf.toFun (P ψ) w = AInf.toFun ψ (blaschke (-(conj (finPart (mobiusExt 0 1 1 0 u))))
        (conj ((1 - conj (conj (finPart (mobiusExt 0 1 1 0 u)))) / (1 - conj (finPart (mobiusExt 0 1 1 0 u)))) *
          w)) * deriv (fun w => blaschke (-(conj (finPart (mobiusExt 0 1 1 0 u))))
        (conj ((1 - conj (conj (finPart (mobiusExt 0 1 1 0 u)))) / (1 - conj (finPart (mobiusExt 0 1 1 0 u)))) *
          w)) w ^ 2 := by
  have ha1 : ‖conj (finPart (mobiusExt 0 1 1 0 u))‖ < 1 := tcg_sigma_coordinate_mem hu
  obtain ⟨a, ha⟩ : ∃ a, a = conj (finPart (mobiusExt 0 1 1 0 u)) := ⟨_, rfl⟩
  rw [← ha] at ha1 ⊢
  by_cases ha0 : a = 0
  · subst ha0
    have hS : (fun w => blaschke (-0) (conj ((1 - conj 0) / (1 - 0)) * w)) = id := by
      funext w; simp [blaschke]
    refine ⟨ContinuousLinearMap.id ℂ _, fun x y h => h, fun ψ w _ => ?_⟩
    rw [hS, deriv_id]
    simp [blaschke]
  · obtain ⟨z', hz'⟩ : ∃ z' : ℂ, z' = (conj a)⁻¹ := ⟨_, rfl⟩
    have hca : conj a ≠ 0 := by simpa using ha0
    have hz'E : z' ∈ unitDiscExterior := by
      show 1 < ‖z'‖
      rw [hz', norm_inv, Complex.norm_conj]
      exact one_lt_inv_iff₀.mpr ⟨norm_pos_iff.mpr ha0, ha1⟩
    have hza : (conj z')⁻¹ = a := by rw [hz', map_inv₀, Complex.conj_conj, inv_inv]
    have ha' : a ≠ 1 := by intro h; rw [h, norm_one] at ha1; exact lt_irrefl _ ha1
    have h1 : 1 - a ≠ 0 := sub_ne_zero.mpr (Ne.symm ha')
    have h2 : 1 - conj a ≠ 0 := by
      intro h; apply h1; have := congrArg conj h; simpa [map_sub] using this
    have hS : (fun w => blaschke (-a) (conj ((1 - conj a) / (1 - a)) * w)) = sigmaInv z' := by
      funext w
      rw [wp_sigmaInv_blaschke hz'E w, hza]
      congr 2
      unfold wp_sigmaRotation
      rw [hz']
      simp only [map_div₀, map_sub, map_one, map_inv₀, Complex.conj_conj]
      have h3 : 1 - a⁻¹ ≠ 0 := by
        intro h; apply ha'; have := sub_eq_zero.mp h; field_simp at this; exact this
      have h4 : 1 - (conj a)⁻¹ ≠ 0 := by
        intro h; apply h2; have := sub_eq_zero.mp h; field_simp at this; rw [← this]; ring
      have h5 : -1 + conj a ≠ 0 := fun h => h2 (by linear_combination -h)
      have h6 : -1 + a ≠ 0 := fun h => h1 (by linear_combination -h)
      generalize conj a = b at h2 h4 h5 hca ⊢
      field_simp
      linear_combination (a - 1) * (mul_inv_cancel₀ h5)
    obtain ⟨P, hP⟩ := s5p57_pull_clm hz'E
    have hσ := wp_sigmaInv_disk_conformal hz'E
    refine ⟨P, (injective_iff_map_eq_zero P).mpr fun ψ hψ => ?_, fun ψ w hw => ?_⟩
    · apply AInf.ext_toFun_disc
      intro v hv
      rw [s5tg_toFun_zero]
      obtain ⟨w, hw, rfl⟩ : v ∈ sigmaInv z' '' unitDisc := by rw [hσ.2.2]; exact hv
      have h0 := (s5p57_pull_spec hz'E ψ).1 w hw
      rw [← hP, hψ, s5tg_toFun_zero] at h0
      have hd := deriv_ne_zero_of_injOn isOpen_ball hσ.1 hσ.2.1 hw
      exact (mul_eq_zero.mp h0.symm).resolve_right (pow_ne_zero 2 hd)
    · rw [congrFun hS w, hS, hP, (s5p57_pull_spec hz'E ψ).1 w hw]

/-- **Stub P1b.** The differential of a right translation is injective (it has the differential of the inverse right
translation as a left inverse). -/
theorem s5p57_L_injective {q : T1 × ExtPlane} (hq : q ∈ TCurve) :
    Function.Injective (fderiv ℂ (tcCoordExpr fun x => tcurveMulInv x q) (tcCoordH q)) := by
  obtain ⟨R, hR⟩ : ∃ R : AInf unitDisc × ℂ → AInf unitDisc × ℂ,
      R = tcCoordExpr fun x => tcurveMulInv x q := ⟨_, rfl⟩
  rw [← hR]
  have hd : DifferentiableAt ℂ R (tcCoordH q) := by rw [hR]; exact s5rh_mulInv_holo hq hq
  have hu := tcg_parameter_mem (Quotient.out q.1 : LinfStarBall).2 hq
  obtain ⟨P, hPi, hP⟩ := s5p57_S_pull hu
  -- the base right translation in Bers coordinates
  obtain ⟨-, hEd, hinv, hE'd, hcomp⟩ := rightTrans_biholomorphic (Quotient.out (invT q.1))
  obtain ⟨E, hE⟩ : ∃ E : AInf unitDisc → AInf unitDisc,
      E = bers ∘ rightTrans (Quotient.out (invT q.1)) ∘ Function.invFunOn bers univ := ⟨_, rfl⟩
  obtain ⟨E', hE'⟩ : ∃ E' : AInf unitDisc → AInf unitDisc,
      E' = bers ∘ rightTrans ⟨_, hinv⟩ ∘ Function.invFunOn bers univ := ⟨_, rfl⟩
  rw [← hE] at hEd
  rw [← hE'] at hE'd
  have hcls : ∀ p : T1, Function.invFunOn bers univ (bers p) = p := fun p =>
    bers_injective.injOn.leftInvOn_invFunOn (mem_univ p)
  have hopen : IsOpen (range bers) := bers_isOpenEmbedding.isOpen_range
  have hy0 : (tcCoordH q).1 ∈ range bers := ⟨q.1, rfl⟩
  have hEy : E (tcCoordH q).1 ∈ range bers := by rw [hE]; exact ⟨_, rfl⟩
  have hEE : E' ∘ E =ᶠ[𝓝 (tcCoordH q).1] id := by
    filter_upwards [hopen.mem_nhds hy0] with φ hφ
    obtain ⟨p, rfl⟩ := hφ
    simp only [Function.comp_apply, hE, hE', hcls, id]
    rw [show rightTrans ⟨_, hinv⟩ (rightTrans (Quotient.out (invT q.1)) p) = p from congrFun hcomp p]
  have hDE : HasFDerivAt E (fderiv ℂ E (tcCoordH q).1) (tcCoordH q).1 :=
    (hEd.differentiableAt (hopen.mem_nhds hy0)).hasFDerivAt
  have hDE' : HasFDerivAt E' (fderiv ℂ E' (E (tcCoordH q).1)) (E (tcCoordH q).1) :=
    (hE'd.differentiableAt (hopen.mem_nhds hEy)).hasFDerivAt
  have hid := (hDE'.comp _ hDE).unique ((hasFDerivAt_id _).congr_of_eventuallyEq hEE)
  have hDEinj : Function.Injective (fderiv ℂ E (tcCoordH q).1) := by
    intro v w h
    have := congrArg (fun L : AInf unitDisc →L[ℂ] AInf unitDisc => L v) hid
    have h' := congrArg (fun L : AInf unitDisc →L[ℂ] AInf unitDisc => L w) hid
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] at this h'
    rw [← this, ← h', h]
  -- `(R y).1 = P (E y.1)` near `tcCoordH q`
  have hev : (⇑(ContinuousLinearMap.fst ℂ (AInf unitDisc) ℂ) ∘ R) =ᶠ[𝓝 (tcCoordH q)]
      (P ∘ E ∘ ⇑(ContinuousLinearMap.fst ℂ (AInf unitDisc) ℂ)) := by
    filter_upwards [s5l54_image_nhds hq] with y hy
    have hxm : tcCoordHInv y ∈ TCurve := Function.invFunOn_mem hy
    have hHy : tcCoordH (tcCoordHInv y) = y := Function.invFunOn_eq hy
    have h1 : bers (tcCoordHInv y).1 = y.1 := congrArg Prod.fst hHy
    show (R y).1 = P (E y.1)
    apply AInf.ext_toFun_disc
    intro w hw
    have hb := tcg_mul_bers_coordinate hxm hq hw
    dsimp only at hb
    rw [hR]
    show AInf.toFun (bers (tcurveMulInv (tcCoordHInv y) q).1) w = _
    rw [hb, hP _ w hw, hE]
    simp only [Function.comp_apply]
    rw [← h1, hcls, gtp_mulT_eq]
  have hf := ((ContinuousLinearMap.fst ℂ (AInf unitDisc) ℂ).hasFDerivAt).comp (tcCoordH q) hd.hasFDerivAt
  have hg : HasFDerivAt (P ∘ E ∘ ⇑(ContinuousLinearMap.fst ℂ (AInf unitDisc) ℂ))
      (P.comp ((fderiv ℂ E (tcCoordH q).1).comp (ContinuousLinearMap.fst ℂ (AInf unitDisc) ℂ))) (tcCoordH q) :=
    P.hasFDerivAt.comp _ (hDE.comp _ (ContinuousLinearMap.fst ℂ (AInf unitDisc) ℂ).hasFDerivAt)
  have huniq := hf.unique (hg.congr_of_eventuallyEq hev)
  -- the fibre direction
  obtain ⟨hv, -⟩ := s5t53_law_at hq hq
  rw [← hR] at hv
  refine (injective_iff_map_eq_zero _).mpr fun X hX => ?_
  have h1 : P (fderiv ℂ E (tcCoordH q).1 X.1) = 0 := by
    have := congrArg (fun L : AInf unitDisc × ℂ →L[ℂ] AInf unitDisc => L X) huniq
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_fst'] at this
    rw [← this, hX]
    rfl
  have hX1 : X.1 = 0 := hDEinj (by rw [hPi (h1.trans (map_zero P).symm), map_zero])
  have hXe : X = X.2 • ((0 : AInf unitDisc), (1 : ℂ)) := Prod.ext (by simp [hX1]) (by simp)
  rw [hXe, map_smul] at hX
  have h2 := congrArg Prod.snd hX
  simp only [Prod.smul_snd, Prod.snd_zero, smul_eq_mul, mul_eq_zero] at h2
  rcases h2 with h2 | h2
  · exact Prod.ext hX1 h2
  · exact absurd h2 hv

/-- **Stub P2.** `‖∂_z‖²_VK = 1/(1 - |z|²)²` on `π⁻¹(0)`. -/
theorem s5p57_vert {z : ℂ} (hz : z ∈ unitDiscExterior) :
    vkNormSq (fiberPt z) (vertVec z) = 1 / (1 - ‖z‖ ^ 2) ^ 2 := by
  have h := s5vc_prop_5_7_vertical hz
  rw [s5p57_theta_vk (s5vc_fiberPt_mem hz), s5t53_polarize_diag (fun a Y => s5t53_vk_smul _ a Y)] at h
  have h' : ((vkNormSq (fiberPt z) (vertVec z) : ℝ) : ℂ) = ((1 / (1 - ‖z‖ ^ 2) ^ 2 : ℝ) : ℂ) := by
    push_cast
    linear_combination -h / 2
  exact_mod_cast h'

/-- **Stub P3.** The horizontal part of `L_z` is the pullback by `σ_z⁻¹` (`tcg_lambda_bers`). -/
theorem s5p57_L_fst {z : ℂ} (hz : z ∈ unitDiscExterior) (X : AInf unitDisc × ℂ) :
    (fderiv ℂ (tcCoordExpr fun x => tcurveMulInv x (fiberPt z)) (tcCoordH (fiberPt z)) X).1 =
      toAInf unitDisc (fun u => AInf.toFun (X.1) (sigmaInv z u) * deriv (sigmaInv z) u ^ 2) := by
  have hq := s5vc_fiberPt_mem hz
  have hz0 : z ≠ 0 := resolvent_exterior_ne_zero hz
  obtain ⟨P, hP⟩ := s5p57_pull_clm hz
  rw [← hP]
  obtain ⟨R, hR⟩ : ∃ R : AInf unitDisc × ℂ → AInf unitDisc × ℂ,
      R = tcCoordExpr fun x => tcurveMulInv x (fiberPt z) := ⟨_, rfl⟩
  rw [← hR]
  have hd : DifferentiableAt ℂ R (tcCoordH (fiberPt z)) := by rw [hR]; exact s5rh_mulInv_holo hq hq
  -- the fibre parameter of `(0, z)` and the automorphism `S = σ_z⁻¹`
  have hzE : ((z : ℂ) : ExtPlane) ∈ extDiscExterior := Or.inl ⟨z, hz, rfl⟩
  have hu : Function.invFun (normalizedWeldingSphere ((Quotient.out originT : LinfStarBall) : LinfStar))
      ((z : ℂ) : ExtPlane) = (z : ExtPlane) := by
    conv_lhs => rw [← s5tg_origin_nWS hzE]
    exact Function.leftInverse_invFun (normalizedWeldingSphere_bijective _).1 _
  have ha : conj (finPart (mobiusExt 0 1 1 0 ((z : ℂ) : ExtPlane))) = (conj z)⁻¹ := by
    show conj (finPart (inversion ((z : ℂ) : ExtPlane))) = _
    rw [s5rh_inversion_coe hz0, finPart_coe, map_inv₀]
  have hS : (fun w => blaschke (-(conj z)⁻¹) (conj ((1 - conj (conj z)⁻¹) / (1 - (conj z)⁻¹)) * w)) =
      sigmaInv z := by
    funext w
    rw [wp_sigmaInv_blaschke hz w]
    congr 2
    have hzc : conj z ≠ 0 := by simpa using hz0
    have hz1 : z ≠ 1 := by
      rintro rfl
      norm_num [unitDiscExterior] at hz
    have h1 : 1 - z ≠ 0 := sub_ne_zero.mpr (Ne.symm hz1)
    have h3 : z - 1 ≠ 0 := sub_ne_zero.mpr hz1
    have h4 : -1 + z ≠ 0 := by rw [neg_add_eq_sub]; exact h3
    have h2 : 1 - conj z ≠ 0 := by
      intro h; apply h1; have := congrArg conj h; simpa [map_sub] using this
    have h5 : conj z - 1 ≠ 0 := by
      intro h; apply h2; linear_combination -h
    have h6 : -1 + conj z ≠ 0 := by rw [neg_add_eq_sub]; exact h5
    unfold wp_sigmaRotation
    simp only [map_div₀, map_sub, map_one, map_inv₀, Complex.conj_conj]
    field_simp
    ring
  have hev : (⇑(ContinuousLinearMap.fst ℂ (AInf unitDisc) ℂ) ∘ R) =ᶠ[𝓝 (tcCoordH (fiberPt z))]
      ⇑(P.comp (ContinuousLinearMap.fst ℂ (AInf unitDisc) ℂ)) := by
    filter_upwards [s5l54_image_nhds hq] with y hy
    show (R y).1 = P y.1
    have hxm : tcCoordHInv y ∈ TCurve := Function.invFunOn_mem hy
    have hHy : tcCoordH (tcCoordHInv y) = y := Function.invFunOn_eq hy
    rw [hP]
    apply AInf.ext_toFun_disc
    intro w hw
    have hb := tcg_mul_bers_coordinate hxm hq hw
    simp only [fiberPt] at hb hu
    have hSw := congrFun hS w
    rw [hu, ha, hS] at hb
    rw [hSw] at hb
    rw [(s5p57_pull_spec hz y.1).1 w hw, hR]
    show AInf.toFun (bers (tcurveMulInv (tcCoordHInv y) (fiberPt z)).1) w = _
    rw [show fiberPt z = (originT, ((z : ℂ) : ExtPlane)) from rfl, hb]
    have hinv : invT originT = originT := by
      have h := gtr_c_inv_mul_self originT
      rwa [gtr_c_mul_one] at h
    rw [hinv, gtr_c_mul_one]
    have h1 : bers (tcCoordHInv y).1 = y.1 := congrArg Prod.fst hHy
    rw [h1]
  have hf := ((ContinuousLinearMap.fst ℂ (AInf unitDisc) ℂ).hasFDerivAt).comp (tcCoordH (fiberPt z)) hd.hasFDerivAt
  have hg := (P.comp (ContinuousLinearMap.fst ℂ (AInf unitDisc) ℂ)).hasFDerivAt (x := tcCoordH (fiberPt z))
  have huniq := hf.unique (hg.congr_of_eventuallyEq hev)
  exact congrArg (fun L : AInf unitDisc × ℂ →L[ℂ] AInf unitDisc => L X) huniq

/-- **Stub P3'.** `L_z` keeps `∂_z` vertical. -/
theorem s5p57_L_vert {z : ℂ} (hz : z ∈ unitDiscExterior) :
    (fderiv ℂ (tcCoordExpr fun x => tcurveMulInv x (fiberPt z)) (tcCoordH (fiberPt z)) (vertVec z)).1 = 0 := by
  rw [s5p57_L_fst hz]
  apply AInf.ext_toFun_disc
  intro u hu
  rw [(s5p57_pull_spec hz _).1 u hu]
  show AInf.toFun (0 : AInf unitDisc) (sigmaInv z u) * _ = AInf.toFun (0 : AInf unitDisc) u
  rw [s5tg_toFun_zero]
  simp

open QCV in
/-- First variation of the 1- and 2-jets of `W_{tν}` at a point `p ∈ 𝔻` (the pattern of
`qcv_schwarzian_fB_variation_origin`, with the kernels `kerD1`, `kerD2`). -/
theorem s5p57_W_jet_var (ν : LinfStar) {p : ℂ} (hp : p ∈ unitDisc) :
    HasDerivAt (fun t : ℂ => deriv (normalizedSolution (extB (t • ν))) p)
      (-(1 / π : ℂ) * ∫ u in unitDiscExterior, ν u * kerD1 p u) 0 ∧
    HasDerivAt (fun t : ℂ => iteratedDeriv 2 (normalizedSolution (extB (t • ν))) p)
      (-(1 / π : ℂ) * ∫ u in unitDiscExterior, ν u * kerD2 p u) 0 := by
  have hz1 : ‖p‖ < 1 := mem_ball_zero_iff.mp hp
  set r₀ : ℝ := 1 / (‖ν‖ + 1) with hr₀
  have hr₀pos : 0 < r₀ := by positivity
  set r : ℝ := r₀ / 2 with hr
  have hrpos : 0 < r := by positivity
  have hnorm : ∀ t ∈ ball (0 : ℂ) r₀, ‖t • ν‖ < 1 := by
    intro t ht
    have htn : ‖t‖ < 1 / (‖ν‖ + 1) := by
      have : ‖t‖ < r₀ := by simpa using ht
      rwa [hr₀] at this
    rw [norm_smul]
    rw [lt_div_iff₀ (by positivity)] at htn
    nlinarith [norm_nonneg ν, norm_nonneg t]
  have hball : ∀ t ∈ ball (0 : ℂ) r₀, t • ν ∈ LinfStarBall := fun t ht => by
    simpa [LinfStarBall] using hnorm t ht
  let W : ℂ → ℂ → ℂ := fun t ζ => normalizedSolution (extB (t • ν)) ζ
  have hWt : ∀ ζ, DifferentiableOn ℂ (fun t => W t ζ) (ball (0 : ℂ) r₀) := by
    intro ζ
    have hc : DifferentiableOn ℂ (fun t : ℂ => t • ν) (ball (0 : ℂ) r₀) :=
      differentiableOn_id.smul_const ν
    exact (qcv_planeB_differentiableOn ζ).comp hc hball
  have hrsub : closedBall (0 : ℂ) r ⊆ ball 0 r₀ := by
    intro t ht
    simp only [mem_closedBall, dist_zero_right, mem_ball] at ht ⊢
    linarith
  obtain ⟨B, hB⟩ : ∃ B : ℝ, ∀ t ∈ closedBall (0 : ℂ) r, ‖W t 2‖ ≤ B :=
    (isCompact_closedBall (0 : ℂ) r).exists_bound_of_continuousOn
      ((hWt 2).continuousOn.mono hrsub)
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0 (mem_closedBall_self hrpos.le))
  set R : ℝ := (1 - ‖p‖) / 2 with hRdef
  have hRpos : 0 < R := by have := sub_pos.2 hz1; positivity
  set ρ : ℝ := (1 + ‖p‖) / 2 with hρdef
  have hρ1 : ρ < 1 := by rw [hρdef]; linarith
  have hballsub : ball p R ⊆ unitDisc := by
    intro x hx
    simp only [mem_ball, dist_eq_norm] at hx
    refine mem_ball_zero_iff.mpr ?_
    have := norm_le_norm_add_norm_sub' x p
    linarith
  have hM : ∀ t ∈ ball (0 : ℂ) r, ∀ ζ ∈ ball p R, ‖W t ζ‖ ≤ 4 * B * (ρ / (1 - ρ) ^ 2) := by
    intro t ht ζ hζ
    have htr₀ : t ∈ ball (0 : ℂ) r₀ := hrsub (ball_subset_closedBall ht)
    have hζ1 : ‖ζ‖ < 1 := mem_ball_zero_iff.mp (hballsub hζ)
    have hζρ : ‖ζ‖ ≤ ρ := by
      simp only [mem_ball, dist_eq_norm] at hζ
      have := norm_le_norm_add_norm_sub' ζ p
      rw [hρdef]; linarith
    refine (qcv_W_koebe (hnorm t htr₀) hζ1).trans ?_
    have hm := qcv_mono_koebe (norm_nonneg ζ) hζρ hρ1
    have hBt := hB t (ball_subset_closedBall ht)
    calc 4 * ‖normalizedSolution (extB (t • ν)) 2‖ * (‖ζ‖ / (1 - ‖ζ‖) ^ 2)
        ≤ 4 * B * (‖ζ‖ / (1 - ‖ζ‖) ^ 2) := by gcongr
      _ ≤ 4 * B * (ρ / (1 - ρ) ^ 2) := by gcongr
  have hζdiff : ∀ t ∈ ball (0 : ℂ) r, DifferentiableOn ℂ (W t) (ball p R) := fun t ht =>
    (qcv_W_props (hnorm t (hrsub (ball_subset_closedBall ht)))).2.1.mono hballsub
  have htdiff : ∀ ζ ∈ ball p R, DifferentiableOn ℂ (fun t => W t ζ) (ball (0 : ℂ) r) := fun ζ _ =>
    (hWt ζ).mono (ball_subset_ball (by linarith))
  set V : ℂ → ℂ := fun ζ => deriv (fun t => W t ζ) 0 with hV
  have hVeq : V = fun ζ => -(1 / π : ℂ) * ∫ u in unitDiscExterior, ν u * ahKer ζ u := by
    funext ζ
    exact (qcv_W_hasDerivAt ν ζ).deriv
  have hj := fun j => qcv_param_hasDerivAt_iter j (F := W) (c := p) (r := r) (R := R)
    (M := 4 * B * (ρ / (1 - ρ) ^ 2)) hrpos hRpos hζdiff htdiff hM
  have hnhds : ball (0 : ℂ) 1 ∈ 𝓝 p := isOpen_ball.mem_nhds hp
  have e1 : deriv V =ᶠ[𝓝 p] fun x => -(1 / π : ℂ) * ∫ u in unitDiscExterior, ν u * kerD1 x u := by
    filter_upwards [hnhds] with x hx
    rw [hVeq]
    exact ((qcv_extK_deriv ν (by simpa using hx)).1.const_mul _).deriv
  have v1 : deriv V p = -(1 / π : ℂ) * ∫ u in unitDiscExterior, ν u * kerD1 p u := e1.eq_of_nhds
  have v2 : deriv (deriv V) p = -(1 / π : ℂ) * ∫ u in unitDiscExterior, ν u * kerD2 p u := by
    rw [e1.deriv_eq]
    exact ((qcv_extK_deriv ν hz1).2.1.const_mul _).deriv
  refine ⟨?_, ?_⟩
  · have d1 := hj 1
    simp only [iteratedDeriv_one] at d1
    rw [← v1]
    exact d1
  · have d2 := hj 2
    rw [← v2]
    refine d2.congr_deriv ?_
    rw [iteratedDeriv_succ', iteratedDeriv_one]

/-- A bounded Beltrami differential times an integrable function is integrable on `𝔻*`. -/
theorem s5p57_nu_int (ν : LinfStar) {A : ℂ → ℂ} (hA : Integrable A (volume.restrict unitDiscExterior)) :
    Integrable (fun u => ν u * A u) (volume.restrict unitDiscExterior) := by
  refine (hA.norm.const_mul ‖ν‖).mono' ((Lp.aestronglyMeasurable ν).mul hA.1) ?_
  filter_upwards [LinfStar_ae_norm_le ν] with u hu
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right hu (norm_nonneg _)

open QCV in
/-- The kernels `kerD1 p`, `kerD2 p` (`p ∈ 𝔻`) are integrable on `𝔻*`. -/
theorem s5p57_kerD_int {p : ℂ} (hp : p ∈ unitDisc) :
    Integrable (kerD1 p) (volume.restrict unitDiscExterior) ∧
      Integrable (kerD2 p) (volume.restrict unitDiscExterior) := by
  have hmeas : MeasurableSet unitDiscExterior := (isOpen_lt continuous_const continuous_norm).measurableSet
  have hp1 : ‖p‖ < 1 := mem_ball_zero_iff.mp hp
  have hB : Integrable (fun u => 12 / (1 - ‖p‖) ^ 4 * ‖ahKer (-1) u‖) (volume.restrict unitDiscExterior) :=
    ((ah_ker_integrable (-1)).norm.const_mul _).integrableOn
  have m1 : Measurable (kerD1 p) := by unfold kerD1; fun_prop
  have m2 : Measurable (kerD2 p) := by unfold kerD2; fun_prop
  refine ⟨hB.mono' m1.aestronglyMeasurable ?_, hB.mono' m2.aestronglyMeasurable ?_⟩
  · filter_upwards [ae_restrict_mem hmeas] with u hu
    exact (qcv_ker_majorant (norm_nonneg p) hp1 le_rfl hu).2.1
  · filter_upwards [ae_restrict_mem hmeas] with u hu
    exact (qcv_ker_majorant (norm_nonneg p) hp1 le_rfl hu).2.2.1

open QCV in
/-- The kernel of the fibre variation: the 2-jet extrapolation from `p` to `z` of `ahKer · u`. -/
theorem s5p57_alg {z p u : ℂ} (hzp : z - p ≠ 0) (h0 : u ≠ 0) (h1 : u - 1 ≠ 0) (hz : u - z ≠ 0)
    (hp : u - p ≠ 0) :
    kerD1 p u / (z - p) - (ahKer z u - ahKer p u) / (z - p) ^ 2 + kerD2 p u / 2 =
      (p - z) / ((u - p) ^ 3 * (u - z)) := by
  unfold kerD1 kerD2 ahKer
  field_simp
  ring

open QCV in
/-- The `t`-derivative at `0` of `σ W'(p)/(W(z) - W(p)) + σ W''(p)/(2 W'(p))`, `W = W_{tν}`, `p ∈ 𝔻`, `z ∈ 𝔻*`. -/
theorem s5p57_Phi_deriv (ν : LinfStar) {p z : ℂ} (σ : ℂ) (hp : p ∈ unitDisc) (hz : z ∈ unitDiscExterior) :
    HasDerivAt (fun t : ℂ => σ * deriv (normalizedSolution (extB (t • ν))) p /
        (normalizedSolution (extB (t • ν)) z - normalizedSolution (extB (t • ν)) p) +
        σ * iteratedDeriv 2 (normalizedSolution (extB (t • ν))) p /
          (2 * deriv (normalizedSolution (extB (t • ν))) p))
      (-(σ / π) * (p - z) * ∫ u in unitDiscExterior, ν u / ((u - p) ^ 3 * (u - z))) 0 := by
  have hmeas : MeasurableSet unitDiscExterior := (isOpen_lt continuous_const continuous_norm).measurableSet
  obtain ⟨d1, d2⟩ := s5p57_W_jet_var ν hp
  have wz := qcv_W_hasDerivAt ν z
  have wp := qcv_W_hasDerivAt ν p
  have hW0 := qcv_W_zero ν
  have i0 : ∀ ζ, normalizedSolution (extB ((0 : ℂ) • ν)) ζ = ζ := fun ζ => by rw [hW0]; rfl
  have i1 : deriv (normalizedSolution (extB ((0 : ℂ) • ν))) p = 1 := by rw [hW0]; exact deriv_id p
  have i2 : iteratedDeriv 2 (normalizedSolution (extB ((0 : ℂ) • ν))) p = 0 := by
    rw [hW0]; simp [iteratedDeriv_succ']
  have hp1 : ‖p‖ < 1 := mem_ball_zero_iff.mp hp
  have hz1 : 1 < ‖z‖ := hz
  have hzp : z - p ≠ 0 := by
    intro h
    rw [sub_eq_zero.mp h] at hz1
    linarith
  have h1 := (d1.const_mul σ).div (wz.sub wp) (by simp only [Pi.sub_apply]; rw [i0, i0]; exact hzp)
  have h2 := (d2.const_mul σ).div (d1.const_mul 2) (by rw [i1]; norm_num)
  -- the integral identity
  obtain ⟨k1, k2⟩ := s5p57_kerD_int hp
  have iz := s5p57_nu_int ν (ah_ker_integrable z).integrableOn
  have ip := s5p57_nu_int ν (ah_ker_integrable p).integrableOn
  have i1' := s5p57_nu_int ν k1
  have i2' := s5p57_nu_int ν k2
  have hne : ∀ᵐ u ∂(volume.restrict unitDiscExterior), u ≠ z := by
    have h := measure_eq_zero_iff_ae_notMem.mp (measure_singleton (μ := (volume : Measure ℂ)) z)
    filter_upwards [ae_restrict_of_ae h] with u hu
    exact hu
  have e : (fun u => (p - z) * (ν u / ((u - p) ^ 3 * (u - z)))) =ᵐ[volume.restrict unitDiscExterior]
      fun u => (ν u * kerD1 p u / (z - p) - (ν u * ahKer z u - ν u * ahKer p u) / (z - p) ^ 2) +
        ν u * kerD2 p u / 2 := by
    filter_upwards [ae_restrict_mem hmeas, hne] with u hu hu'
    have hu1 : 1 < ‖u‖ := hu
    have h0 : u ≠ 0 := by rintro rfl; simp at hu1; linarith
    have h1' : u - 1 ≠ 0 := by
      intro h; rw [sub_eq_zero.mp h] at hu1; simp at hu1
    have hz' : u - z ≠ 0 := sub_ne_zero.mpr hu'
    have hp' : u - p ≠ 0 := by
      intro h; rw [sub_eq_zero.mp h] at hu1; linarith
    rw [show (p - z) * (ν u / ((u - p) ^ 3 * (u - z))) = ν u * ((p - z) / ((u - p) ^ 3 * (u - z))) by ring,
      ← s5p57_alg hzp h0 h1' hz' hp']
    ring
  have hI : (p - z) * ∫ u in unitDiscExterior, ν u / ((u - p) ^ 3 * (u - z)) =
      ((∫ u in unitDiscExterior, ν u * kerD1 p u) / (z - p) -
        ((∫ u in unitDiscExterior, ν u * ahKer z u) - ∫ u in unitDiscExterior, ν u * ahKer p u) / (z - p) ^ 2) +
        (∫ u in unitDiscExterior, ν u * kerD2 p u) / 2 := by
    have hA : Integrable (fun u => ν u * kerD1 p u / (z - p) -
        (ν u * ahKer z u - ν u * ahKer p u) / (z - p) ^ 2) (volume.restrict unitDiscExterior) :=
      (i1'.div_const _).sub ((iz.sub ip).div_const _)
    have hD : Integrable (fun u => ν u * kerD2 p u / 2) (volume.restrict unitDiscExterior) := i2'.div_const _
    have hA1 : Integrable (fun u => ν u * kerD1 p u / (z - p)) (volume.restrict unitDiscExterior) :=
      i1'.div_const _
    have hA2 : Integrable (fun u => (ν u * ahKer z u - ν u * ahKer p u) / (z - p) ^ 2)
        (volume.restrict unitDiscExterior) := (iz.sub ip).div_const _
    have hBC : Integrable (fun u => ν u * ahKer z u - ν u * ahKer p u) (volume.restrict unitDiscExterior) :=
      iz.sub ip
    rw [← integral_const_mul, integral_congr_ae e, integral_add hA hD, integral_sub hA1 hA2,
      integral_div, integral_div, integral_div, integral_sub iz ip]
  refine (h1.add h2).congr_deriv ?_
  simp only [Pi.sub_apply]
  rw [i0, i0, i1, i2, mul_assoc (-(σ / (π : ℂ))), hI]
  have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 Real.pi_ne_zero
  field_simp
  ring

/-- The memoir fibre coordinate of `w^{λ}(R z)`, `λ = tcurveLambda ν R`, for a plane q.c. `R` that is conformal on `𝔻`:
by uniqueness `W_λ = a (W_ν ∘ R⁻¹) + b` (`tcg_lambda_is_dilatation`, `uq_conformal_auto`), so the coordinate is the
2-jet expression of `F = W_ν ∘ R⁻¹` at `0` (the affine factor cancels). -/
theorem s5p57_fibre_formula {ν : LinfStar} (hν : ν ∈ LinfStarBall)
    (R : ℂ ≃ₜ ℂ) {K : ℝ} (hR : IsKQC (⇑R) univ K)
    (hRE : R '' unitDiscExterior = unitDiscExterior)
    (hRD : IsConformalOnto (⇑R.symm) unitDisc unitDisc) {z : ℂ} (hz : z ∈ unitDiscExterior) :
    tcurveLambda ν R ∈ LinfStarBall ∧
    finPart (inversion (wB (tcurveLambda ν R) ((R z : ℂ) : ExtPlane))) +
        deriv (deriv (fB (tcurveLambda ν R))) 0 / 2 =
      deriv (normalizedSolution (extB ν) ∘ R.symm) 0 /
          (normalizedSolution (extB ν) z - normalizedSolution (extB ν) (R.symm 0)) +
        deriv (deriv (normalizedSolution (extB ν) ∘ R.symm)) 0 /
          (2 * deriv (normalizedSolution (extB ν) ∘ R.symm) 0) := by
  have hRs : R '' univ = univ := image_univ.trans R.surjective.range_eq
  have hL := (tmi_lambda_props hν hR hRs hRE).1
  refine ⟨hL, ?_⟩
  set lam := tcurveLambda ν R with hlam
  set W := normalizedSolution (extB ν) with hW
  set F := W ∘ R.symm with hF
  have hN := AppA.acc_ns_spec hν
  obtain ⟨KN, hKN⟩ := hN.1
  obtain ⟨-, hNd, hNi, -⟩ := QCV.qcv_W_props (bc_norm_lt_one hν)
  have hNe : complexDilatation W =ᵐ[volume.restrict unitDiscExterior] (ν : ℂ → ℂ) := by
    filter_upwards [ae_restrict_of_ae hN.2.2.2.2, ae_restrict_mem bc_hEo.measurableSet] with w hw hwE
    rw [hw]
    simp [extB, indicator_of_mem hwE]
  have hFd : DifferentiableOn ℂ F unitDisc := hNd.comp hRD.1 hRD.mapsTo
  have hFK := thm7_1_comp (homeomorph_inverse_isKQC R hR) hKN (subset_univ _)
  have hFs : F '' univ = univ := by
    rw [hF, image_comp, image_univ.trans R.symm.surjective.range_eq, hN.2.1]
  have hFe := (tcg_lambda_is_dilatation hν hKN hNe R hR hRE).symm
  have hM := AppA.acc_ns_spec hL
  have hMae : complexDilatation (normalizedSolution (extB lam)) =ᵐ[volume] extB lam := hM.2.2.2.2
  obtain ⟨T, hT, he⟩ := uq_conformal_auto isOpen_univ ⟨_, hFK⟩ hM.1 hFs hM.2.1 (by
    rw [Measure.restrict_univ]
    exact (tcg_plane_extB hFd hFe).trans hMae.symm)
  obtain ⟨a, b, ha, hab⟩ := nx_entire_affine hT
  have heq : normalizedSolution (extB lam) = fun w => a * F w + b := by
    funext w
    rw [he w (mem_univ w), hab]
  have hW0 : normalizedSolution (extB lam) 0 = 0 := (QCV.qcv_W_props (bc_norm_lt_one hL)).2.2.2
  have hb : b = -(a * F 0) := by
    have h0 := congrFun heq 0
    rw [hW0] at h0
    linear_combination -h0
  have hd1 : deriv (normalizedSolution (extB lam)) = fun w => a * deriv F w := by
    rw [heq]
    funext w
    rw [deriv_add_const, deriv_const_mul_field']
  have hd2 : deriv (deriv (normalizedSolution (extB lam))) 0 = a * deriv (deriv F) 0 := by
    rw [hd1, deriv_const_mul_field']
  have hF0 : F 0 = W (R.symm 0) := rfl
  have hRz : F (R z) = W z := by simp [hF]
  have h0D : (0 : ℂ) ∈ unitDisc := mem_ball_self one_pos
  have hS0 : R.symm 0 ∈ unitDisc := hRD.mapsTo h0D
  have hzS : z ≠ R.symm 0 := by
    intro h
    have h1 : 1 < ‖z‖ := hz
    have h2 : ‖R.symm 0‖ < 1 := mem_ball_zero_iff.mp hS0
    rw [h] at h1
    linarith
  have hWne : W z - F 0 ≠ 0 := by
    rw [hF0]
    exact sub_ne_zero.mpr fun h => hzS (hNi (mem_univ _) (mem_univ _) h)
  have hFinj : InjOn F unitDisc := fun x _ y _ hxy => R.symm.injective (hNi (mem_univ _) (mem_univ _) hxy)
  have hF'0 : deriv F 0 ≠ 0 := deriv_ne_zero_of_injOn isOpen_ball hFd hFinj h0D
  have hval : normalizedSolution (extB lam) (R z) = a * (W z - F 0) := by
    rw [heq]
    simp only
    rw [hRz, hb]
    ring
  have hval0 : a * (W z - F 0) ≠ 0 := mul_ne_zero ha hWne
  have hv : OnePoint.map (normalizedSolution (extB lam)) ((R z : ℂ) : ExtPlane) ≠ ((0 : ℂ) : ExtPlane) := by
    rw [OnePoint.map_some, hval]
    exact fun h => hval0 (OnePoint.coe_injective h)
  rw [s5rh_memoir hL hv, OnePoint.map_some, hval, s5rh_inversion_coe hval0, finPart_coe, hd2, hd1]
  rw [← hF0]
  field_simp

/-- The 1- and 2-jets at `0` of a composition of analytic germs. -/
theorem s5p57_comp_jets {W S : ℂ → ℂ} (hS : AnalyticAt ℂ S 0) (hW : AnalyticAt ℂ W (S 0)) :
    deriv (W ∘ S) 0 = deriv W (S 0) * deriv S 0 ∧
      deriv (deriv (W ∘ S)) 0 = deriv (deriv W) (S 0) * deriv S 0 ^ 2 + deriv W (S 0) * deriv (deriv S) 0 := by
  have hev : ∀ᶠ w in 𝓝 (0 : ℂ), AnalyticAt ℂ W (S w) :=
    hS.continuousAt.tendsto.eventually hW.eventually_analyticAt
  have hevS : ∀ᶠ w in 𝓝 (0 : ℂ), AnalyticAt ℂ S w := hS.eventually_analyticAt
  have hd : deriv (W ∘ S) =ᶠ[𝓝 (0 : ℂ)] fun w => deriv W (S w) * deriv S w := by
    filter_upwards [hev, hevS] with w h1 h2
    exact deriv_comp w h1.differentiableAt h2.differentiableAt
  refine ⟨hd.eq_of_nhds, ?_⟩
  rw [hd.deriv_eq]
  have h1 : HasDerivAt (fun w => deriv W (S w)) (deriv (deriv W) (S 0) * deriv S 0) 0 :=
    hW.deriv.differentiableAt.hasDerivAt.comp 0 hS.differentiableAt.hasDerivAt
  have h2 : HasDerivAt (deriv S) (deriv (deriv S) 0) 0 := hS.deriv.differentiableAt.hasDerivAt
  have h3 : HasDerivAt (fun w => deriv W (S w) * deriv S w)
      (deriv (deriv W) (S 0) * deriv S 0 * deriv S 0 + deriv W (S 0) * deriv (deriv S) 0) 0 := h1.mul h2
  rw [h3.deriv]
  ring

/-- The jets at `0` of the disc automorphism `w ↦ c B_A(w)`. -/
theorem s5p57_blaschke_jets (c : ℂ) {A : ℂ} (hA : ‖A‖ < 1) :
    deriv (fun w => c * blaschke A w) 0 = c * (1 - conj A * A) ∧
      deriv (deriv (fun w => c * blaschke A w)) 0 = 2 * c * conj A * (1 - conj A * A) := by
  have hden : ∀ w : ℂ, ‖w‖ < 1 → 1 - conj A * w ≠ 0 := by
    intro w hw h
    have h1 : conj A * w = 1 := by linear_combination -h
    have h2 : ‖conj A * w‖ < 1 := by
      rw [norm_mul, Complex.norm_conj]
      nlinarith [norm_nonneg A, norm_nonneg w]
    rw [h1, norm_one] at h2
    exact lt_irrefl _ h2
  have hE : ∀ w : ℂ, ‖w‖ < 1 → HasDerivAt (fun w => c * blaschke A w)
      (c * (1 - conj A * A) / (1 - conj A * w) ^ 2) w := by
    intro w hw
    have h1 : HasDerivAt (fun w : ℂ => w - A) 1 w := (hasDerivAt_id' w).sub_const A
    have h2 : HasDerivAt (fun w : ℂ => 1 - conj A * w) (-conj A) w := by
      exact (((hasDerivAt_id' w).const_mul (conj A)).const_sub 1).congr_deriv (by ring)
    have h := (h1.div h2 (hden w hw)).const_mul c
    unfold blaschke
    refine h.congr_deriv ?_
    have := hden w hw
    field_simp
    ring
  have h0 : ‖(0 : ℂ)‖ < 1 := by simp
  refine ⟨?_, ?_⟩
  · rw [(hE 0 h0).deriv]
    simp
  · have hev : deriv (fun w => c * blaschke A w) =ᶠ[𝓝 (0 : ℂ)]
        fun w => c * (1 - conj A * A) / (1 - conj A * w) ^ 2 := by
      filter_upwards [ball_mem_nhds (0 : ℂ) one_pos] with w hw
      exact (hE w (mem_ball_zero_iff.mp hw)).deriv
    rw [hev.deriv_eq]
    have h2 : HasDerivAt (fun w : ℂ => 1 - conj A * w) (-conj A) 0 := by
      exact (((hasDerivAt_id' (0 : ℂ)).const_mul (conj A)).const_sub 1).congr_deriv (by ring)
    have hd : HasDerivAt (fun w => c * (1 - conj A * A) / (1 - conj A * w) ^ 2)
        ((0 * (1 - conj A * 0) ^ 2 - c * (1 - conj A * A) * (↑2 * (1 - conj A * 0) ^ (2 - 1) * -conj A)) /
          ((1 - conj A * 0) ^ 2) ^ 2) 0 :=
      (hasDerivAt_const (0 : ℂ) (c * (1 - conj A * A))).div (h2.pow 2) (pow_ne_zero 2 (hden 0 h0))
    rw [hd.deriv]
    simp
    ring

/-- If the 2-jet expression of `S = c B_A` vanishes at `z ∈ 𝔻*`, then `S(0)` is the reflection of `z`. -/
theorem s5p57_refl_of_jets {z c A : ℂ} (hz : z ∈ unitDiscExterior) (hc : ‖c‖ = 1) (hA : ‖A‖ < 1)
    (h : c * (1 - conj A * A) / (z - c * blaschke A 0) +
      2 * c * conj A * (1 - conj A * A) / (2 * (c * (1 - conj A * A))) = 0) :
    c * blaschke A 0 = (conj z)⁻¹ := by
  have hb0 : blaschke A 0 = -A := by simp [blaschke]
  rw [hb0] at h ⊢
  simp only [mul_neg, sub_neg_eq_add] at h ⊢
  have hc0 : c ≠ 0 := by rintro rfl; simp at hc
  have hk : (1 - conj A * A) ≠ 0 := by
    rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    intro h'
    have : ((‖A‖ ^ 2 : ℝ) : ℂ) = 1 := by linear_combination -h'
    have h2 : ‖A‖ ^ 2 = 1 := by exact_mod_cast this
    nlinarith [norm_nonneg A]
  have hz0 : z ≠ 0 := resolvent_exterior_ne_zero hz
  have h2 : 2 * c * conj A * (1 - conj A * A) / (2 * (c * (1 - conj A * A))) = conj A := by
    field_simp
  rw [h2] at h
  have hcc : c * conj c = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hc]
    norm_num
  by_cases hd : z + c * A = 0
  · rw [hd, div_zero, zero_add] at h
    have hA0 : A = 0 := by simpa using h
    rw [hA0, mul_zero, add_zero] at hd
    exact absurd hd hz0
  · rw [div_add' _ _ _ hd, div_eq_zero_iff] at h
    have h3 := h.resolve_right hd
    have h4 : c = -(conj A * z) := by linear_combination h3
    have h5 : conj c = -(A * conj z) := by rw [h4]; simp
    rw [h5] at hcc
    refine eq_inv_of_mul_eq_one_left ?_
    linear_combination hcc

/-- Integrals over `𝔻*` are invariant under rotations. -/
theorem s5p57_rot_int (g : ℂ → ℂ) {c : ℂ} (hc : ‖c‖ = 1) :
    ∫ v in unitDiscExterior, g (c * v) = ∫ v in unitDiscExterior, g v := by
  have hc0 : c ≠ 0 := by rintro rfl; simp at hc
  have hd : DifferentiableOn ℂ (fun v : ℂ => c * v) unitDiscExterior :=
    (differentiable_id.const_mul c).differentiableOn
  have hi : InjOn (fun v : ℂ => c * v) unitDiscExterior := fun x _ y _ h => mul_left_cancel₀ hc0 h
  have himg : (fun v : ℂ => c * v) '' unitDiscExterior = unitDiscExterior := by
    ext w
    constructor
    · rintro ⟨v, hv, rfl⟩
      show 1 < ‖c * v‖
      rw [norm_mul, hc, one_mul]
      exact hv
    · intro hw
      refine ⟨c⁻¹ * w, ?_, by field_simp⟩
      show 1 < ‖c⁻¹ * w‖
      rw [norm_mul, norm_inv, hc, inv_one, one_mul]
      exact hw
  have h := ahP_integral_image bc_hEo hd hi g
  rw [himg] at h
  rw [h]
  refine setIntegral_congr_fun bc_hEo.measurableSet fun v _ => ?_
  have : deriv (fun v : ℂ => c * v) v = c := by
    simpa using ((hasDerivAt_id v).const_mul c).deriv
  simp only [this, hc, one_pow, one_smul]

/-- The monomials `(1 - |v|²)² v̄^{-(n+4)} v^{-3}` have zero integral over `𝔻*` (rotation by `e^{iπ/(n+1)}`). -/
theorem s5p57_mono_zero (n : ℕ) :
    ∫ v in unitDiscExterior, (((1 - ‖v‖ ^ 2) ^ 2 : ℝ) : ℂ) * ((conj v ^ (n + 4))⁻¹ * (v ^ 3)⁻¹) = 0 := by
  set c : ℂ := Complex.exp (((π / (n + 1) : ℝ) : ℂ) * I) with hcdef
  have hc : ‖c‖ = 1 := Complex.norm_exp_ofReal_mul_I _
  have hc0 : c ≠ 0 := Complex.exp_ne_zero _
  have hcn : c ^ (n + 1) = -1 := by
    rw [hcdef, ← Complex.exp_nat_mul]
    have : ((n + 1 : ℕ) : ℂ) * (((π / (n + 1) : ℝ) : ℂ) * I) = π * I := by
      push_cast
      have : (n : ℂ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
      field_simp
    rw [this, Complex.exp_pi_mul_I]
  have hcc : conj c = c⁻¹ := by
    refine eq_inv_of_mul_eq_one_right ?_
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hc]
    norm_num
  have h := s5p57_rot_int (fun v => (((1 - ‖v‖ ^ 2) ^ 2 : ℝ) : ℂ) * ((conj v ^ (n + 4))⁻¹ * (v ^ 3)⁻¹)) hc
  have hpt : ∀ v : ℂ, (((1 - ‖c * v‖ ^ 2) ^ 2 : ℝ) : ℂ) * ((conj (c * v) ^ (n + 4))⁻¹ * ((c * v) ^ 3)⁻¹) =
      -((((1 - ‖v‖ ^ 2) ^ 2 : ℝ) : ℂ) * ((conj v ^ (n + 4))⁻¹ * (v ^ 3)⁻¹)) := by
    intro v
    rw [norm_mul, hc, one_mul, map_mul, hcc, mul_pow, mul_pow, mul_inv, mul_inv, inv_pow, inv_inv]
    have e : c ^ (n + 4) * (c ^ 3)⁻¹ = c ^ (n + 1) := by
      rw [show n + 4 = (n + 1) + 3 by ring, pow_add]
      field_simp
    calc (((1 - ‖v‖ ^ 2) ^ 2 : ℝ) : ℂ) * (c ^ (n + 4) * (conj v ^ (n + 4))⁻¹ * ((c ^ 3)⁻¹ * (v ^ 3)⁻¹))
        = (c ^ (n + 4) * (c ^ 3)⁻¹) * ((((1 - ‖v‖ ^ 2) ^ 2 : ℝ) : ℂ) * ((conj v ^ (n + 4))⁻¹ * (v ^ 3)⁻¹)) := by
          ring
      _ = _ := by rw [e, hcn]; ring
  simp only [hpt, integral_neg] at h
  linear_combination -h / 2

/-- `|v^{-3}| ≤ 8 (1 + |v|)^{-3}` on `𝔻*`. -/
theorem s5p57_inv3 {v : ℂ} (hv : 1 < ‖v‖) : ‖(v ^ 3)⁻¹‖ ≤ 8 * (1 + ‖v‖) ^ (-3 : ℝ) := by
  have ha0 : 0 < ‖v‖ := by linarith
  rw [norm_inv, norm_pow, Real.rpow_neg (by positivity), show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num,
    Real.rpow_natCast]
  have h : (1 + ‖v‖) ^ 3 ≤ 8 * ‖v‖ ^ 3 := by
    nlinarith [pow_pos ha0 2, pow_pos ha0 3, sq_nonneg (‖v‖ - 1)]
  calc (‖v‖ ^ 3)⁻¹ = 8 * (8 * ‖v‖ ^ 3)⁻¹ := by field_simp
    _ ≤ 8 * ((1 + ‖v‖) ^ 3)⁻¹ := mul_le_mul_of_nonneg_left (inv_anti₀ (by positivity) h) (by norm_num)

/-- `(1 + |v|)^{-3}` is integrable on `𝔻*`. -/
theorem s5p57_B3_int : Integrable (fun v : ℂ => 8 * (1 + ‖v‖) ^ (-3 : ℝ)) (volume.restrict unitDiscExterior) := by
  have := integrable_one_add_norm (E := ℂ) (μ := volume) (r := 3) (by simp [Complex.finrank_real_complex]; norm_num)
  exact (this.const_mul 8).integrableOn

/-- Series form: if `φ₀ = Σ cₙ uⁿ` on `𝔻` with `Σ |cₙ| < ∞`, then `∬_{𝔻*} Λφ₀(v) v^{-3} = 0`. -/
theorem s5p57_series_zero {c : ℕ → ℂ} (hc : Summable fun n => ‖c n‖) {φ0 : ℂ → ℂ}
    (hφ : ∀ u : ℂ, ‖u‖ < 1 → HasSum (fun n => c n * u ^ n) (φ0 u)) :
    ∫ v in unitDiscExterior,
      (-(1 / 2 : ℂ) * (((1 - ‖v‖ ^ 2) ^ 2 : ℝ) : ℂ) * φ0 ((conj v)⁻¹) / conj v ^ 4) * (v ^ 3)⁻¹ = 0 := by
  have hmeas : MeasurableSet unitDiscExterior := bc_hEo.measurableSet
  set G : ℕ → ℂ → ℂ := fun n v => (((1 - ‖v‖ ^ 2) ^ 2 : ℝ) : ℂ) * ((conj v ^ (n + 4))⁻¹ * (v ^ 3)⁻¹) with hG
  set F : ℕ → ℂ → ℂ := fun n v => (-(1 / 2 : ℂ) * c n) * G n v with hF
  have hne0 : ∀ v : ℂ, 1 < ‖v‖ → v ≠ 0 := fun v hv h => by rw [h, norm_zero] at hv; linarith
  have hGb : ∀ n v, 1 < ‖v‖ → ‖G n v‖ ≤ 8 * (1 + ‖v‖) ^ (-3 : ℝ) := by
    intro n v hv
    have ha0 : 0 < ‖v‖ := by linarith
    have h1 : ‖G n v‖ = (‖v‖ ^ 2 - 1) ^ 2 * ((‖v‖ ^ (n + 4))⁻¹ * ‖(v ^ 3)⁻¹‖) := by
      simp only [hG, norm_mul, norm_inv, norm_pow, Complex.norm_conj, Complex.norm_real, Real.norm_eq_abs, sq_abs]
      ring
    have h2 : (‖v‖ ^ 2 - 1) ^ 2 * (‖v‖ ^ (n + 4))⁻¹ ≤ 1 := by
      rw [← div_eq_mul_inv, div_le_one (by positivity)]
      have h3 : (‖v‖ ^ 2 - 1) ^ 2 ≤ ‖v‖ ^ 4 := by nlinarith [sq_nonneg ‖v‖]
      exact h3.trans (pow_le_pow_right₀ hv.le (by omega))
    rw [h1, ← mul_assoc]
    calc (‖v‖ ^ 2 - 1) ^ 2 * (‖v‖ ^ (n + 4))⁻¹ * ‖(v ^ 3)⁻¹‖ ≤ 1 * ‖(v ^ 3)⁻¹‖ := by gcongr
      _ ≤ 8 * (1 + ‖v‖) ^ (-3 : ℝ) := by rw [one_mul]; exact s5p57_inv3 hv
  have hGc : ∀ n, ContinuousOn (G n) unitDiscExterior := by
    intro n
    refine ContinuousOn.mul (by fun_prop) (ContinuousOn.mul ?_ ?_)
    · exact ((continuous_conj.pow _).continuousOn).inv₀ fun v hv => pow_ne_zero _ ((map_ne_zero _).mpr (hne0 v hv))
    · exact ((continuous_id.pow 3).continuousOn).inv₀ fun v hv => pow_ne_zero _ (hne0 v hv)
  have hGi : ∀ n, Integrable (G n) (volume.restrict unitDiscExterior) := by
    intro n
    refine s5p57_B3_int.mono' ((hGc n).aestronglyMeasurable hmeas) ?_
    filter_upwards [ae_restrict_mem hmeas] with v hv
    exact hGb n v hv
  have hFi : ∀ n, Integrable (F n) (volume.restrict unitDiscExterior) := fun n => (hGi n).const_mul _
  have hFs : Summable fun n => ∫ v in unitDiscExterior, ‖F n v‖ := by
    refine Summable.of_nonneg_of_le (fun n => integral_nonneg fun v => norm_nonneg _) (fun n => ?_)
      ((hc.mul_left (1 / 2 * ∫ v in unitDiscExterior, 8 * (1 + ‖v‖) ^ (-3 : ℝ))))
    have hle : ∫ v in unitDiscExterior, ‖F n v‖ ≤
        ∫ v in unitDiscExterior, (1 / 2 * ‖c n‖) * (8 * (1 + ‖v‖) ^ (-3 : ℝ)) := by
      refine integral_mono_ae (hFi n).norm (s5p57_B3_int.const_mul _) ?_
      filter_upwards [ae_restrict_mem hmeas] with v hv
      simp only [hF, norm_mul, norm_neg, norm_div, norm_one, Complex.norm_ofNat]
      have := hGb n v hv
      nlinarith [norm_nonneg (c n), norm_nonneg (G n v)]
    rw [integral_const_mul] at hle
    linarith
  have hsum := integral_tsum_of_summable_integral_norm hFi hFs
  have hz : ∀ n, ∫ v in unitDiscExterior, F n v = 0 := fun n => by
    rw [integral_const_mul, s5p57_mono_zero, mul_zero]
  simp only [hz, tsum_zero] at hsum
  rw [hsum]
  refine integral_congr_ae ?_
  filter_upwards [ae_restrict_mem hmeas] with v hv
  have hv0 := hne0 v hv
  have hw : ‖(conj v)⁻¹‖ < 1 := by
    rw [norm_inv, Complex.norm_conj]; exact inv_lt_one_of_one_lt₀ hv
  set K : ℂ := -(1 / 2 : ℂ) * (((1 - ‖v‖ ^ 2) ^ 2 : ℝ) : ℂ) / conj v ^ 4 * (v ^ 3)⁻¹ with hK
  have hs := (hφ _ hw).mul_left K
  rw [show (-(1 / 2 : ℂ) * (((1 - ‖v‖ ^ 2) ^ 2 : ℝ) : ℂ) * φ0 ((conj v)⁻¹) / conj v ^ 4) * (v ^ 3)⁻¹ =
    K * φ0 ((conj v)⁻¹) by rw [hK]; ring, ← hs.tsum_eq]
  refine tsum_congr fun n => ?_
  have hcv : conj v ≠ 0 := (map_ne_zero _).mpr hv0
  simp only [hF, hG, hK]
  rw [inv_pow]
  field_simp <;> ring

/-- A function holomorphic on a disc of radius `R > 1` is an absolutely summable power series on `𝔻` (as in
`qcv_reproduce_ball`). -/
theorem s5p57_series_of_ball {φ0 : ℂ → ℂ} {R : ℝ} (hR : 1 < R) (hd : DifferentiableOn ℂ φ0 (ball 0 R)) :
    ∃ c : ℕ → ℂ, Summable (fun n => ‖c n‖) ∧ ∀ u : ℂ, ‖u‖ < 1 → HasSum (fun n => c n * u ^ n) (φ0 u) := by
  set ρ : ℝ := (1 + R) / 2 with hρ
  have hρ1 : 1 < ρ := by rw [hρ]; linarith
  have hρR : ρ < R := by rw [hρ]; linarith
  set ρ' : NNReal := ⟨ρ, by linarith⟩ with hρ'
  have hρ'pos : 0 < ρ' := by
    show (0 : NNReal) < ⟨ρ, _⟩
    exact_mod_cast (by linarith : (0 : ℝ) < ρ)
  have hdc : DifferentiableOn ℂ φ0 (closedBall 0 (ρ' : ℝ)) :=
    hd.mono (closedBall_subset_ball hρR)
  have hps := hdc.hasFPowerSeriesOnBall hρ'pos
  set p := cauchyPowerSeries φ0 0 (ρ' : ℝ) with hp
  have hrad : ((1 : NNReal) : ENNReal) < p.radius := by
    refine lt_of_lt_of_le ?_ hps.r_le
    exact_mod_cast hρ1
  have hc : Summable fun n => ‖p.coeff n‖ := by
    have := p.summable_norm_mul_pow hrad
    simpa [FormalMultilinearSeries.norm_apply_eq_norm_coef] using this
  refine ⟨p.coeff, hc, fun u hu => ?_⟩
  have hmem : u ∈ Metric.eball (0 : ℂ) ρ' := by
    rw [Metric.mem_eball, edist_zero_right]
    have : (‖u‖₊ : ℝ) < ρ := by simp only [coe_nnnorm]; linarith
    exact_mod_cast this
  have := hps.hasSum hmem
  simp only [zero_add] at this
  have e : (fun n => p n (fun _ => u)) = fun n => p.coeff n * u ^ n := by
    funext n
    rw [p.apply_eq_pow_smul_coeff, smul_eq_mul, mul_comm]
  rw [e] at this
  exact this

/-- **`∬_{𝔻*} Λφ(v) v^{-3} = 0`** for `φ ∈ A∞(𝔻)` (dilations `φ(s·)`, `s → 1`, as in `qcv_reproduce_AInf`). -/
theorem s5p57_cubic_zero (φ : AInf unitDisc) :
    ∫ v in unitDiscExterior,
      (-(1 / 2 : ℂ) * (((1 - ‖v‖ ^ 2) ^ 2 : ℝ) : ℂ) * AInf.toFun φ ((conj v)⁻¹) / conj v ^ 4) * (v ^ 3)⁻¹ = 0 := by
  have hmeas : MeasurableSet unitDiscExterior := bc_hEo.measurableSet
  have hφd : DifferentiableOn ℂ (AInf.toFun φ) unitDisc := φ.property
  have hne0 : ∀ v : ℂ, 1 < ‖v‖ → v ≠ 0 := fun v hv h => by rw [h, norm_zero] at hv; linarith
  let sq : ℕ → ℝ := fun k => 1 - (1 / 2) * (1 / ((k : ℝ) + 1))
  have hs0 : ∀ k, 0 < sq k := fun k => by
    have : 1 / ((k : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]; have : (0 : ℝ) ≤ k := k.cast_nonneg; linarith
    simp only [sq]; linarith
  have hs1 : ∀ k, sq k < 1 := fun k => by
    have : 0 < 1 / ((k : ℝ) + 1) := by positivity
    simp only [sq]; linarith
  have hslim : Tendsto sq atTop (𝓝 1) := by
    have := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (1 / 2 : ℝ)
    have := (tendsto_const_nhds (x := (1 : ℝ))).sub this
    simpa [sq] using this
  have hFint : ∀ k, ∫ v in unitDiscExterior, (-(1 / 2 : ℂ) * (((1 - ‖v‖ ^ 2) ^ 2 : ℝ) : ℂ) *
      AInf.toFun φ ((sq k : ℂ) * (conj v)⁻¹) / conj v ^ 4) * (v ^ 3)⁻¹ = 0 := by
    intro k
    have hR : 1 < 1 / sq k := by rw [lt_div_iff₀ (hs0 k)]; linarith [hs1 k]
    have hd : DifferentiableOn ℂ (fun u => AInf.toFun φ ((sq k : ℂ) * u)) (ball 0 (1 / sq k)) := by
      refine hφd.comp (differentiableOn_const _ |>.mul differentiableOn_id) ?_
      intro u hu
      rw [mem_ball_zero_iff] at hu
      refine mem_ball_zero_iff.2 ?_
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hs0 k).le]
      calc sq k * ‖u‖ < sq k * (1 / sq k) := mul_lt_mul_of_pos_left hu (hs0 k)
        _ = 1 := mul_one_div_cancel (hs0 k).ne'
    obtain ⟨c, hc, hφ⟩ := s5p57_series_of_ball hR hd
    have h := s5p57_series_zero (φ0 := fun u => AInf.toFun φ ((sq k : ℂ) * u)) hc hφ
    exact h
  have hcont : ∀ k, ContinuousOn (fun v : ℂ => (-(1 / 2 : ℂ) * (((1 - ‖v‖ ^ 2) ^ 2 : ℝ) : ℂ) *
      AInf.toFun φ ((sq k : ℂ) * (conj v)⁻¹) / conj v ^ 4) * (v ^ 3)⁻¹) unitDiscExterior := by
    intro k
    have hr : ContinuousOn (fun v : ℂ => (conj v)⁻¹) unitDiscExterior :=
      continuous_conj.continuousOn.inv₀ fun v hv => (map_ne_zero (starRingEnd ℂ)).mpr (hne0 v hv)
    have hm : MapsTo (fun v : ℂ => (sq k : ℂ) * (conj v)⁻¹) unitDiscExterior unitDisc := by
      intro v hv
      have hv1 : 1 < ‖v‖ := hv
      refine mem_ball_zero_iff.2 ?_
      show ‖(sq k : ℂ) * (conj v)⁻¹‖ < 1
      rw [norm_mul, norm_inv, Complex.norm_conj, Complex.norm_real, Real.norm_of_nonneg (hs0 k).le]
      have hb := inv_lt_one_of_one_lt₀ hv1
      have hb0 : 0 < ‖v‖⁻¹ := by positivity
      nlinarith [hs1 k]
    have hf : ContinuousOn (fun v : ℂ => AInf.toFun φ ((sq k : ℂ) * (conj v)⁻¹)) unitDiscExterior :=
      hφd.continuousOn.comp (continuousOn_const.mul hr) hm
    have hw : Continuous (fun v : ℂ => -(1 / 2 : ℂ) * (((1 - ‖v‖ ^ 2) ^ 2 : ℝ) : ℂ)) := by fun_prop
    exact ((hw.continuousOn.mul hf).div (continuous_conj.pow 4).continuousOn
      fun v hv => pow_ne_zero 4 ((map_ne_zero (starRingEnd ℂ)).mpr (hne0 v hv))).mul
      (((continuous_id.pow 3).continuousOn).inv₀ fun v hv => pow_ne_zero _ (hne0 v hv))
  have hlim := tendsto_integral_of_dominated_convergence (μ := volume.restrict unitDiscExterior)
    (F := fun k v => (-(1 / 2 : ℂ) * (((1 - ‖v‖ ^ 2) ^ 2 : ℝ) : ℂ) *
      AInf.toFun φ ((sq k : ℂ) * (conj v)⁻¹) / conj v ^ 4) * (v ^ 3)⁻¹)
    (f := fun v => (-(1 / 2 : ℂ) * (((1 - ‖v‖ ^ 2) ^ 2 : ℝ) : ℂ) * AInf.toFun φ ((conj v)⁻¹) / conj v ^ 4) *
      (v ^ 3)⁻¹)
    (fun v => (‖φ‖ / 2) * (8 * (1 + ‖v‖) ^ (-3 : ℝ)))
    (fun k => (hcont k).aestronglyMeasurable hmeas)
    (s5p57_B3_int.const_mul (‖φ‖ / 2))
    (fun k => by
      filter_upwards [ae_restrict_mem hmeas] with v hv
      have h1 := QCV.qcv_dil_bound φ (hs0 k) (hs1 k).le hv
      rw [norm_mul]
      exact mul_le_mul h1 (s5p57_inv3 hv) (norm_nonneg _) (by positivity))
    (by
      filter_upwards [ae_restrict_mem hmeas] with v hv
      have hv1 : 1 < ‖v‖ := hv
      have hw : ‖(conj v)⁻¹‖ < 1 := by
        rw [norm_inv, Complex.norm_conj]; exact inv_lt_one_of_one_lt₀ hv1
      have hc : ContinuousAt (AInf.toFun φ) ((conj v)⁻¹) :=
        hφd.continuousOn.continuousAt (isOpen_ball.mem_nhds (mem_ball_zero_iff.2 hw))
      have h1 : Tendsto (fun k => (sq k : ℂ) * (conj v)⁻¹) atTop (𝓝 ((conj v)⁻¹)) := by
        have := ((Complex.continuous_ofReal.tendsto 1).comp hslim).mul_const ((conj v)⁻¹)
        simpa using this
      have hG : ContinuousAt (fun w : ℂ => (-(1 / 2 : ℂ) * (((1 - ‖v‖ ^ 2) ^ 2 : ℝ) : ℂ) *
          AInf.toFun φ w / conj v ^ 4) * (v ^ 3)⁻¹) ((conj v)⁻¹) :=
        (((hc.const_mul _).div_const _).mul_const _)
      exact hG.tendsto.comp h1)
  simp_rw [hFint] at hlim
  exact tendsto_nhds_unique hlim tendsto_const_nhds

/-- The pointwise identity behind the change of variables `u = σ_z⁻¹(w)` (all quantities as atoms). -/
theorem s5p57_cov_alg {w W z Z k x X Φ0 r : ℂ} (hk : k ≠ 0) (hw : w ≠ 0) (hW : W ≠ 0) (hZ : Z ≠ 0)
    (hzz : z * Z - 1 ≠ 0) (h1 : w + k * Z ≠ 0) (h2 : 1 + k * W * Z ≠ 0) (h3 : k * W + z ≠ 0)
    (hxz : x - z = k * (1 - z * Z) / (w + k * Z)) (hxp : x - Z⁻¹ = w * (z * Z - 1) / (Z * (w + k * Z)))
    (hX : X = (1 + k * W * Z) / (k * W + z)) :
    (k * (z * Z - 1) / (w + k * Z) ^ 2 * (k⁻¹ * (Z * z - 1) / (W + k⁻¹ * z) ^ 2)) *
        (-(1 / 2) * ((k * (z * Z - 1) / (w + k * Z) ^ 2 * (k⁻¹ * (Z * z - 1) / (W + k⁻¹ * z) ^ 2)) * r) * Φ0 /
          X ^ 4) / ((x - Z⁻¹) ^ 3 * (x - z)) =
      (-(k * Z) / (Z⁻¹ - z) ^ 2) *
        ((-(1 / 2) * r * (Φ0 * (k * (z * Z - 1) / (W⁻¹ + k * Z) ^ 2) ^ 2) / W ^ 4) * (w ^ 3)⁻¹) := by
  have hzz' : 1 - z * Z ≠ 0 := fun h => hzz (by linear_combination -h)
  have h4 : W + k⁻¹ * z ≠ 0 := by
    intro h; apply h3; field_simp at h; linear_combination h
  have h5 : W⁻¹ + k * Z ≠ 0 := by
    intro h; apply h2; field_simp at h; linear_combination h
  have h6 : Z⁻¹ - z ≠ 0 := by
    intro h; apply hzz'; field_simp at h; linear_combination h
  rw [hX, hxp, hxz]
  field_simp
  ring

/-- The derivative of `σ_z⁻¹(w) = (k + wz)/(w + k z̄)`, `k = (1 - z)/(1 - z̄)`. -/
theorem s5p57_sI_deriv (z : ℂ) {w : ℂ} (hw : w + (1 - z) / (1 - conj z) * conj z ≠ 0) :
    HasDerivAt (sigmaInv z)
      ((1 - z) / (1 - conj z) * (z * conj z - 1) / (w + (1 - z) / (1 - conj z) * conj z) ^ 2) w := by
  set k := (1 - z) / (1 - conj z) with hk
  have h := (((hasDerivAt_id' w).mul_const z).const_add k).div
    ((hasDerivAt_id' w).add_const (k * conj z)) hw
  have e : sigmaInv z = fun y => (k + y * z) / (y + k * conj z) := rfl
  rw [e]
  refine h.congr_deriv ?_
  field_simp
  ring

/-- **Ahlfors' orthogonality on `𝔻*`** (disc form of `cor_1_15`): `∬_{𝔻*} Λφ(u)/((u - 1/z̄)³(u - z)) = 0`
for `z ∈ 𝔻*`. Change of variables `u = σ_z⁻¹(w)` reduces it to `s5p57_cubic_zero` for the pullback of `φ`. -/
theorem s5p57_orth_K (φ : AInf unitDisc) {z : ℂ} (hz : z ∈ unitDiscExterior) :
    ∫ u in unitDiscExterior, Lambda φ u / ((u - (conj z)⁻¹) ^ 3 * (u - z)) = 0 := by
  have hmeas : MeasurableSet unitDiscExterior := bc_hEo.measurableSet
  set k : ℂ := (1 - z) / (1 - conj z) with hkdef
  have hk1 : ‖k‖ = 1 := wp_sigma_normalizing_norm hz
  have hk0 : k ≠ 0 := by rintro h; rw [h, norm_zero] at hk1; norm_num at hk1
  have hkk : k * conj k = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hk1]; norm_num
  have hkc : conj k = k⁻¹ := eq_inv_of_mul_eq_one_right hkk
  have hz1 : 1 < ‖z‖ := hz
  have hz0 : z ≠ 0 := resolvent_exterior_ne_zero hz
  have hZ0 : conj z ≠ 0 := (map_ne_zero _).mpr hz0
  have hzZ : z * conj z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have hzz : z * conj z - 1 ≠ 0 := by
    rw [hzZ]; intro h
    have : ((‖z‖ ^ 2 : ℝ) : ℂ) = 1 := by linear_combination h
    have h2 : ‖z‖ ^ 2 = 1 := by exact_mod_cast this
    nlinarith
  set a : ℂ := -(k * conj z) with ha
  have hden : ∀ w : ℂ, w ≠ a → w + k * conj z ≠ 0 := by
    intro w hw h; apply hw; rw [ha]; linear_combination h
  have hsI : ∀ w : ℂ, sigmaInv z w = (k + w * z) / (w + k * conj z) := fun w => rfl
  have hd' : ∀ w : ℂ, w ≠ a → HasDerivAt (sigmaInv z) (k * (z * conj z - 1) / (w + k * conj z) ^ 2) w :=
    fun w hw => s5p57_sI_deriv z (hden w hw)
  set U : Set ℂ := unitDiscExterior \ {a} with hU
  have hUo : IsOpen U := bc_hEo.sdiff isClosed_singleton
  have hdiff : DifferentiableOn ℂ (sigmaInv z) U := fun w hw =>
    (hd' w hw.2).differentiableAt.differentiableWithinAt
  have hinj : InjOn (sigmaInv z) U := by
    intro w1 hw1 w2 hw2 h
    rw [hsI, hsI, div_eq_div_iff (hden w1 hw1.2) (hden w2 hw2.2)] at h
    have h' : k * (1 - z * conj z) * (w2 - w1) = 0 := by linear_combination h
    have hk' : k * (1 - z * conj z) ≠ 0 := mul_ne_zero hk0 fun h0 => hzz (by linear_combination -h0)
    exact (sub_eq_zero.mp ((mul_eq_zero.mp h').resolve_left hk')).symm
  -- `σ_z⁻¹` maps `𝔻* \ {a}` onto `𝔻* \ {z}`
  have hnorm : ∀ w : ℂ, w ≠ a → ‖sigmaInv z w‖ ^ 2 - 1 =
      (‖z‖ ^ 2 - 1) * (‖w‖ ^ 2 - 1) / ‖w + k * conj z‖ ^ 2 := by
    intro w hw
    have hn := tv1_norm_identity k w z hk1
    have hpos : 0 < ‖w + k * conj z‖ := norm_pos_iff.mpr (hden w hw)
    rw [hsI, norm_div, div_pow, ← hn]
    field_simp
  have hmaps : ∀ w ∈ U, sigmaInv z w ∈ unitDiscExterior \ {z} := by
    intro w hw
    have hw1 : 1 < ‖w‖ := hw.1
    refine ⟨?_, ?_⟩
    · show 1 < ‖sigmaInv z w‖
      have h := hnorm w hw.2
      have hpos : 0 < (‖z‖ ^ 2 - 1) * (‖w‖ ^ 2 - 1) / ‖w + k * conj z‖ ^ 2 := by
        have : 0 < ‖w + k * conj z‖ := norm_pos_iff.mpr (hden w hw.2)
        apply div_pos _ (by positivity)
        apply mul_pos <;> nlinarith
      nlinarith [norm_nonneg (sigmaInv z w)]
    · intro h
      have h' : sigmaInv z w = z := h
      rw [hsI, div_eq_iff (hden w hw.2)] at h'
      apply hzz
      have : k * (1 - z * conj z) = 0 := by linear_combination h'
      have := (mul_eq_zero.mp this).resolve_left hk0
      linear_combination -this
  have himg : sigmaInv z '' U = unitDiscExterior \ {z} := by
    refine Subset.antisymm (fun _ ⟨w, hw, hwe⟩ => hwe ▸ hmaps w hw) ?_
    intro y hy
    have hy1 : 1 < ‖y‖ := hy.1
    have hyz : y - z ≠ 0 := sub_ne_zero.mpr hy.2
    refine ⟨k * ((1 - y * conj z) / (y - z)), ⟨?_, ?_⟩, ?_⟩
    · show 1 < ‖k * ((1 - y * conj z) / (y - z))‖
      rw [norm_mul, hk1, one_mul, norm_div]
      have hn := tv1_norm_identity' y z
      have hpos : 0 < ‖y - z‖ := norm_pos_iff.mpr hyz
      rw [one_lt_div hpos]
      have hp : 0 < (‖y‖ ^ 2 - 1) * (‖z‖ ^ 2 - 1) := mul_pos (by nlinarith) (by nlinarith)
      have : ‖y - z‖ ^ 2 < ‖1 - y * conj z‖ ^ 2 := by linarith
      exact lt_of_pow_lt_pow_left₀ 2 (norm_nonneg _) this
    · intro h
      have h' : k * ((1 - y * conj z) / (y - z)) = -(k * conj z) := h
      apply hzz
      field_simp at h'
      have : 1 - z * conj z = 0 := by linear_combination h'
      linear_combination -this
    · have hden2 : k * ((1 - y * conj z) / (y - z)) + k * conj z ≠ 0 := by
        rw [show k * ((1 - y * conj z) / (y - z)) + k * conj z = k * (1 - z * conj z) / (y - z) by
          field_simp; ring]
        exact div_ne_zero (mul_ne_zero hk0 fun h0 => hzz (by linear_combination -h0)) hyz
      rw [hsI, div_eq_iff hden2]
      field_simp
      ring
  -- the pullback `ψ = (σ_z⁻¹)^* φ` and the reduced integral
  set ψ : AInf unitDisc :=
    toAInf unitDisc (fun u => AInf.toFun φ (sigmaInv z u) * deriv (sigmaInv z) u ^ 2) with hψdef
  have hψ := (s5p57_pull_spec hz φ).1
  have h0 := s5p57_cubic_zero ψ
  set g : ℂ → ℂ := fun u => (-(1 / 2 : ℂ) * (1 - (‖u‖ : ℂ) ^ 2) ^ 2 * AInf.toFun φ (refl u) / conj u ^ 4) /
    ((u - (conj z)⁻¹) ^ 3 * (u - z)) with hg
  set H : ℂ → ℂ := fun v => (-(1 / 2 : ℂ) * (((1 - ‖v‖ ^ 2) ^ 2 : ℝ) : ℂ) * AInf.toFun ψ ((conj v)⁻¹) /
    conj v ^ 4) * (v ^ 3)⁻¹ with hH
  set C : ℂ := -(k * conj z) / ((conj z)⁻¹ - z) ^ 2 with hC
  have ha1 : 1 < ‖a‖ := by rw [ha, norm_neg, norm_mul, hk1, one_mul, Complex.norm_conj]; exact hz1
  have hpt : ∀ w ∈ U, ‖deriv (sigmaInv z) w‖ ^ 2 • g (sigmaInv z w) = C * H w := by
    intro w hw
    have hw1 : 1 < ‖w‖ := hw.1
    have hwa : w ≠ a := hw.2
    have hw0 : w ≠ 0 := by rintro rfl; simp at hw1; linarith
    have hW0 : conj w ≠ 0 := (map_ne_zero _).mpr hw0
    have hWD : (conj w)⁻¹ ∈ unitDisc :=
      mem_ball_zero_iff.2 (by rw [norm_inv, Complex.norm_conj]; exact inv_lt_one_of_one_lt₀ hw1)
    have hWa : (conj w)⁻¹ ≠ a := fun h => by
      have := mem_ball_zero_iff.mp hWD; rw [h] at this; linarith
    have hd := (hd' w hwa).deriv
    have hd2 := (hd' _ hWa).deriv
    have h1 := hden w hwa
    have h5 := hden _ hWa
    have hxm := hmaps w hw
    have hx := hsI w
    set x := sigmaInv z w with hxdef
    have hx0 : x ≠ 0 := by
      intro h; have := hxm.1; rw [h] at this; simp [unitDiscExterior] at this; linarith
    have hkw : k + w * z ≠ 0 := by intro h; apply hx0; rw [hx, h, zero_div]
    have h2 : 1 + k * conj w * conj z ≠ 0 := by
      have e : 1 + k * conj w * conj z = k * conj (k + w * z) := by
        rw [map_add, map_mul, hkc]; field_simp
      rw [e]; exact mul_ne_zero hk0 ((map_ne_zero _).mpr hkw)
    have h3 : k * conj w + z ≠ 0 := by
      have e : k * conj w + z = k * conj (w + k * conj z) := by
        rw [map_add, map_mul, hkc, Complex.conj_conj]; field_simp
      rw [e]; exact mul_ne_zero hk0 ((map_ne_zero _).mpr h1)
    have hxz : x - z = k * (1 - z * conj z) / (w + k * conj z) := by rw [hx]; field_simp; ring
    have hxp : x - (conj z)⁻¹ = w * (z * conj z - 1) / (conj z * (w + k * conj z)) := by
      rw [hx]; field_simp; ring
    have hX : conj x = (1 + k * conj w * conj z) / (k * conj w + z) := by
      rw [hx, map_div₀, map_add, map_add, map_mul, map_mul, Complex.conj_conj, hkc]
      field_simp
    have hrefl : refl x = sigmaInv z (conj w)⁻¹ := by
      unfold refl
      rw [hX, hsI]
      field_simp
    have hdc : conj (deriv (sigmaInv z) w) = k⁻¹ * (conj z * z - 1) / (conj w + k⁻¹ * z) ^ 2 := by
      rw [hd]
      simp only [map_div₀, map_mul, map_sub, map_pow, map_add, map_one, Complex.conj_conj, hkc]
    have hdn : ‖deriv (sigmaInv z) w‖ = (‖z‖ ^ 2 - 1) / ‖w + k * conj z‖ ^ 2 := by
      rw [hd, norm_div, norm_mul, hk1, one_mul, norm_pow, hzZ,
        show ((‖z‖ ^ 2 : ℝ) : ℂ) - 1 = ((‖z‖ ^ 2 - 1 : ℝ) : ℂ) by push_cast; ring,
        Complex.norm_real, Real.norm_of_nonneg (by nlinarith)]
    have hr : (1 - ‖x‖ ^ 2) ^ 2 = ‖deriv (sigmaInv z) w‖ ^ 2 * (1 - ‖w‖ ^ 2) ^ 2 := by
      have hpos : 0 < ‖w + k * conj z‖ := norm_pos_iff.mpr h1
      rw [show (1 - ‖x‖ ^ 2) ^ 2 = (‖x‖ ^ 2 - 1) ^ 2 by ring, hnorm w hwa, hdn]
      field_simp
      ring
    have hwt : (1 - (‖x‖ : ℂ) ^ 2) ^ 2 =
        deriv (sigmaInv z) w * conj (deriv (sigmaInv z) w) * (((1 - ‖w‖ ^ 2) ^ 2 : ℝ) : ℂ) := by
      rw [Complex.mul_conj']
      exact_mod_cast hr
    have hψw : AInf.toFun ψ (conj w)⁻¹ =
        AInf.toFun φ (sigmaInv z (conj w)⁻¹) * deriv (sigmaInv z) (conj w)⁻¹ ^ 2 := hψ _ hWD
    have key := s5p57_cov_alg (x := x) (X := conj x) (Φ0 := AInf.toFun φ (sigmaInv z (conj w)⁻¹))
      (r := (((1 - ‖w‖ ^ 2) ^ 2 : ℝ) : ℂ)) hk0 hw0 hW0 hZ0 hzz h1 h2 h3 hxz hxp hX
    simp only [hg, hH]
    rw [Complex.real_smul, Complex.ofReal_pow, ← Complex.mul_conj', hwt, hrefl, hψw, hdc, hd, hd2]
    linear_combination key
  have hstep1 : ∫ u in unitDiscExterior, Lambda φ u / ((u - (conj z)⁻¹) ^ 3 * (u - z)) =
      ∫ u in unitDiscExterior, g u := by
    refine integral_congr_ae ?_
    filter_upwards [Lambda_coe_ae φ] with u hu
    simp only [hg]
    rw [hu]
  rw [hstep1, ← setIntegral_congr_set (sdiff_null_ae_eq_self (measure_singleton z)), ← himg,
    ahP_integral_image hUo hdiff hinj g, setIntegral_congr_fun hUo.measurableSet hpt, integral_const_mul,
    setIntegral_congr_set (sdiff_null_ae_eq_self (measure_singleton a))]
  simp only [hH]
  rw [h0, mul_zero]

/-- The coordinate curve of `t ↦ ([tμ], w^{tμ}(z))` has velocity `horVec μ z` at `t = 0` (TV1 and
`s5l54_c_analytic`). -/
theorem s5p57_curve_deriv {μ : LinfStar} (hμ : μ ∈ harmonicBeltrami) {z : ℂ} (hz : z ∈ unitDiscExterior) :
    HasDerivAt (fun t : ℝ => ((bersPhi ((t : ℂ) • μ),
        finPart (inversion (wB ((t : ℂ) • μ) (z : ExtPlane))) + deriv (deriv (fB ((t : ℂ) • μ))) 0 / 2) :
        AInf unitDisc × ℂ)) (horVec μ z) 0 := by
  have h0 : (0 : LinfStar) ∈ LinfStarBall := mem_ball_self one_pos
  have hz0 : z ≠ 0 := resolvent_exterior_ne_zero hz
  have hlin : HasDerivAt (fun t : ℝ => (t : ℂ) • μ) μ 0 := by
    have := ((hasDerivAt_id (0 : ℝ)).ofReal_comp).smul_const μ
    simpa using this
  have hB : HasFDerivAt bersPhi (fderiv ℂ bersPhi 0) (0 : LinfStar) :=
    (bersPhi_differentiableOn.differentiableAt (isOpen_ball.mem_nhds h0)).hasFDerivAt
  have h1 : HasDerivAt (fun t : ℝ => bersPhi ((t : ℂ) • μ)) (fderiv ℂ bersPhi 0 μ) 0 :=
    (hB.restrictScalars ℝ).comp_hasDerivAt_of_eq (x := (0 : ℝ)) hlin (by simp)
  obtain ⟨hTV, -⟩ := TV1 hμ hz
  have hf0 : finPart (wB (((0 : ℝ) : ℂ) • μ) (z : ExtPlane)) = z := by
    simp only [Complex.ofReal_zero, zero_smul, s5vc_wB_zero, id, finPart_coe]
  have hev : ∀ᶠ (t : ℝ) in 𝓝 (0 : ℝ), finPart (inversion (wB ((t : ℂ) • μ) (z : ExtPlane))) =
      (finPart (wB ((t : ℂ) • μ) (z : ExtPlane)))⁻¹ := by
    have hne' : ∀ᶠ (t : ℝ) in 𝓝 (0 : ℝ), finPart (wB ((t : ℂ) • μ) (z : ExtPlane)) ≠ 0 :=
      hTV.continuousAt.eventually_ne (by rw [hf0]; exact hz0)
    filter_upwards [hne'] with t ht
    have hne : wB ((t : ℂ) • μ) (z : ExtPlane) ≠ extInf := by
      intro h; apply ht; rw [h]; rfl
    rw [← coe_finPart_of_ne hne, s5rh_inversion_coe ht, finPart_coe, finPart_coe]
  have h2 : HasDerivAt (fun t : ℝ => (finPart (wB ((t : ℂ) • μ) (z : ExtPlane)))⁻¹) (-wdot μ z / z ^ 2) 0 := by
    have := hTV.inv (by rw [hf0]; exact hz0)
    rwa [hf0] at this
  have hD : DifferentiableAt ℝ (fun t : ℝ => deriv (deriv (fB ((t : ℂ) • μ))) 0) 0 := by
    have hA : DifferentiableAt ℝ (fun ν : LinfStar => deriv (deriv (fB ν)) 0 / 2) (((0 : ℝ) : ℂ) • μ) := by
      simpa using (s5l54_c_analytic h0).differentiableAt
    have hcomp : DifferentiableAt ℝ (fun t : ℝ => deriv (deriv (fB ((t : ℂ) • μ))) 0 / 2) 0 :=
      DifferentiableAt.comp (g := fun ν : LinfStar => deriv (deriv (fB ν)) 0 / 2) (0 : ℝ) hA
        hlin.differentiableAt
    have e : (fun t : ℝ => deriv (deriv (fB ((t : ℂ) • μ))) 0) =
        fun t : ℝ => (2 : ℂ) * (deriv (deriv (fB ((t : ℂ) • μ))) 0 / 2) := funext fun t => by ring
    rw [e]
    exact hcomp.const_mul (2 : ℂ)
  have h3 : HasDerivAt (fun t : ℝ => finPart (inversion (wB ((t : ℂ) • μ) (z : ExtPlane))) +
      deriv (deriv (fB ((t : ℂ) • μ))) 0 / 2)
      (-wdot μ z / z ^ 2 + deriv (fun t : ℝ => deriv (deriv (fB ((t : ℂ) • μ))) 0) 0 / 2) 0 := by
    refine (h2.add (hD.hasDerivAt.div_const 2)).congr_of_eventuallyEq ?_
    filter_upwards [hev] with t ht
    rw [ht]
    rfl
  exact h1.prodMk h3

/-- Along `x = ([ν], w^ν(z))`, the fibre coordinate of `x · (0, z)⁻¹` is the 2-jet expression of `W_ν ∘ R⁻¹`, for the
`σ_z`-extension `R` (`s5rh_mulInv_rep` with `G = R`: `out originT ∼ 0`, so `𝗀 = id` on `S¹`). -/
theorem s5p57_fib_t {z : ℂ} (hz : z ∈ unitDiscExterior) (R : ℂ ≃ₜ ℂ) {KR : ℝ} (hR : IsKQC (⇑R) univ KR)
    (hRE : R '' unitDiscExterior = unitDiscExterior) (hRD : IsConformalOnto (⇑R.symm) unitDisc unitDisc)
    (hRb : EqOn (⇑R) (fun w : ℂ => finPart (sigmaSphere (z : ExtPlane) (w : ExtPlane))) unitCircle)
    {ν : LinfStar} (hν : ν ∈ LinfStarBall) :
    (Phi ⟨ν, hν⟩, wB ν (z : ExtPlane)) ∈ TCurve ∧
    (tcCoordH (tcurveMulInv (Phi ⟨ν, hν⟩, wB ν (z : ExtPlane)) (fiberPt z))).2 =
      deriv (normalizedSolution (extB ν) ∘ R.symm) 0 /
          (normalizedSolution (extB ν) z - normalizedSolution (extB ν) (R.symm 0)) +
        deriv (deriv (normalizedSolution (extB ν) ∘ R.symm)) 0 /
          (2 * deriv (normalizedSolution (extB ν) ∘ R.symm) 0) := by
  have hq := s5vc_fiberPt_mem hz
  have hzE : ((z : ℂ) : ExtPlane) ∈ extDiscExterior := Or.inl ⟨z, hz, rfl⟩
  have hrel : teichSetoid.r (Phi ⟨ν, hν⟩).out ⟨ν, hν⟩ := Quotient.mk_out (s := teichSetoid) ⟨ν, hν⟩
  have hx : (Phi ⟨ν, hν⟩, wB ν (z : ExtPlane)) ∈ TCurve := by
    show wB ν (z : ExtPlane) ∈ wB (Quotient.out (Phi ⟨ν, hν⟩) : LinfStarBall) '' extDiscExterior
    rw [fiber_independent hrel]
    exact ⟨_, hzE, rfl⟩
  have h0 : (0 : LinfStar) ∈ LinfStarBall := mem_ball_self one_pos
  have hμb := (Quotient.out originT : LinfStarBall).2
  have hu : Function.invFun (normalizedWeldingSphere ((Quotient.out originT : LinfStarBall) : LinfStar))
      ((z : ℂ) : ExtPlane) = (z : ExtPlane) := by
    conv_lhs => rw [← s5tg_origin_nWS hzE]
    exact Function.leftInverse_invFun (normalizedWeldingSphere_bijective _).1 _
  have hclass0 : teichSetoid (Quotient.out originT : LinfStarBall) ⟨0, h0⟩ :=
    Quotient.exact (Quotient.out_eq originT)
  have hgam : ∀ w ∈ unitCircle,
      gammaMu ((Quotient.out originT : LinfStarBall) : LinfStar) w = ((w : ℂ) : ExtPlane) := by
    intro w hw
    obtain ⟨hγ, -⟩ := tce_gamma_circle hμb hw
    rw [hγ]
    have h1 : wA ((Quotient.out originT : LinfStarBall) : LinfStar) w = wA 0 w := hclass0 w hw
    rw [h1, wp_wA_zero]
    rfl
  have hG : IsQuasiconformal (⇑R) univ ∧ R '' univ = univ ∧
      EqOn (⇑R) (fun w : ℂ => finPart
        (sigmaSphere (Function.invFun (normalizedWeldingSphere (Quotient.out (fiberPt z).1 : LinfStarBall))
          (fiberPt z).2) (gammaMu (Quotient.out (fiberPt z).1 : LinfStarBall) w))) unitCircle := by
    refine ⟨⟨KR, hR⟩, image_univ.trans R.surjective.range_eq, fun w hw => ?_⟩
    show R w = finPart (sigmaSphere (Function.invFun (normalizedWeldingSphere
      ((Quotient.out originT : LinfStarBall) : LinfStar)) ((z : ℂ) : ExtPlane))
        (gammaMu ((Quotient.out originT : LinfStarBall) : LinfStar) w))
    rw [hu, hgam w hw]
    exact hRb hw
  obtain ⟨hl, hmul⟩ := s5rh_mulInv_rep hx hq hν rfl hG
  refine ⟨hx, ?_⟩
  rw [hmul]
  show finPart (inversion (tcurveZ ν (⇑R) (tcurveLambda ν R) (wB ν (z : ExtPlane)))) +
      deriv (deriv (fB ((Quotient.out (Phi ⟨_, hl⟩) : LinfStarBall) : LinfStar))) 0 / 2 = _
  rw [s5rh_c_congr ⟨_, hl⟩]
  unfold tcurveZ
  rw [Function.leftInverse_invFun (wB_bijective ν).1 ((z : ℂ) : ExtPlane), OnePoint.map_some]
  exact (s5p57_fibre_formula hν R hR hRE hRD hz).2

/-- **Stub P4.** `L_z τ_μ` has no vertical part: the fibre coordinate of `R_{q_z⁻¹}([tμ], w^{tμ}(z))` is stationary
at `t = 0`, with the `ċ`-shift of `horVec` included. -/
theorem s5p57_L_hor_snd {μ : LinfStar} (hμ : μ ∈ harmonicBeltrami) {z : ℂ} (hz : z ∈ unitDiscExterior) :
    (fderiv ℂ (tcCoordExpr fun x => tcurveMulInv x (fiberPt z)) (tcCoordH (fiberPt z)) (horVec μ z)).2 = 0 := by
  have hq := s5vc_fiberPt_mem hz
  have hzE : ((z : ℂ) : ExtPlane) ∈ extDiscExterior := Or.inl ⟨z, hz, rfl⟩
  obtain ⟨R, KR, hR, hRE, hRD, hRb⟩ := tcg_sigma_extension hzE
  -- `R⁻¹ = c B_A` on `𝔻`, with jets `σ`, `τ` and `p = R⁻¹(0)`
  obtain ⟨c, A, hc, hA, hSe⟩ := exists_rotation_blaschke_of_isConformalOnto_unitDisc hRD
  have h0D : (0 : ℂ) ∈ unitDisc := mem_ball_self one_pos
  have hSev : (⇑R.symm) =ᶠ[𝓝 (0 : ℂ)] fun w => c * blaschke A w :=
    Filter.eventuallyEq_of_mem (isOpen_ball.mem_nhds h0D) fun w hw => hSe hw
  obtain ⟨hj1, hj2⟩ := s5p57_blaschke_jets c hA
  set σ : ℂ := c * (1 - conj A * A) with hσ
  set τ : ℂ := 2 * c * conj A * (1 - conj A * A) with hτ
  have hS1 : deriv (⇑R.symm) 0 = σ := by rw [hSev.deriv_eq]; exact hj1
  have hS2 : deriv (deriv (⇑R.symm)) 0 = τ := by rw [hSev.deriv.deriv_eq]; exact hj2
  have hS0 : R.symm 0 = c * blaschke A 0 := hSe h0D
  have hSa : AnalyticAt ℂ (⇑R.symm) 0 := hRD.1.analyticAt (isOpen_ball.mem_nhds h0D)
  set p : ℂ := R.symm 0 with hpdef
  have hpD : p ∈ unitDisc := hRD.mapsTo h0D
  have hc0 : c ≠ 0 := by rintro rfl; simp at hc
  have hk : (1 - conj A * A) ≠ 0 := by
    rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    intro h'
    have : ((‖A‖ ^ 2 : ℝ) : ℂ) = 1 := by linear_combination -h'
    have h2 : ‖A‖ ^ 2 = 1 := by exact_mod_cast this
    nlinarith [norm_nonneg A]
  have hσ0 : σ ≠ 0 := mul_ne_zero hc0 hk
  -- the fibre coordinate along `([ν], w^ν(z))`
  have hform : ∀ (ν : LinfStar) (hν : ν ∈ LinfStarBall),
      (tcCoordH (tcurveMulInv (Phi ⟨ν, hν⟩, wB ν (z : ExtPlane)) (fiberPt z))).2 =
        (σ * deriv (normalizedSolution (extB ν)) p /
            (normalizedSolution (extB ν) z - normalizedSolution (extB ν) p) +
          σ * iteratedDeriv 2 (normalizedSolution (extB ν)) p / (2 * deriv (normalizedSolution (extB ν)) p)) +
          τ / (2 * σ) := by
    intro ν hν
    rw [(s5p57_fib_t hz R hR hRE hRD hRb hν).2, ← hpdef]
    obtain ⟨-, hWd, hWi, -⟩ := QCV.qcv_W_props (bc_norm_lt_one hν)
    have hWa : AnalyticAt ℂ (normalizedSolution (extB ν)) p := hWd.analyticAt (isOpen_ball.mem_nhds hpD)
    obtain ⟨e1, e2⟩ := s5p57_comp_jets hSa hWa
    have hW' : deriv (normalizedSolution (extB ν)) p ≠ 0 :=
      deriv_ne_zero_of_injOn isOpen_ball hWd (hWi.mono (subset_univ _)) hpD
    rw [← hpdef] at e1 e2
    have hzp : z ≠ p := by
      intro h
      have h1 : 1 < ‖z‖ := hz
      have h2 : ‖p‖ < 1 := mem_ball_zero_iff.mp hpD
      rw [h] at h1
      linarith
    have hWzp : normalizedSolution (extB ν) z - normalizedSolution (extB ν) p ≠ 0 :=
      sub_ne_zero.mpr fun h => hzp (hWi (mem_univ _) (mem_univ _) h)
    rw [e1, e2, hS1, hS2, iteratedDeriv_succ', iteratedDeriv_one]
    field_simp
    ring
  -- `p` is the reflection of `z`, from `(0, z) · (0, z)⁻¹ = (0, ∞)`
  have hp : p = (conj z)⁻¹ := by
    have h0b : (0 : LinfStar) ∈ LinfStarBall := mem_ball_self one_pos
    have hf := hform 0 h0b
    have e1 : (Phi ⟨0, h0b⟩, wB 0 (z : ExtPlane)) = fiberPt z := by rw [s5vc_wB_zero]; rfl
    rw [e1, s5tg_mul_self hq] at hf
    have hW0 : normalizedSolution (extB (0 : LinfStar)) = id := by
      simpa only [zero_smul] using QCV.qcv_W_zero (0 : LinfStar)
    have hO : (tcCoordH tOrigin).2 = 0 := by
      show finPart (inversion extInf) + deriv (deriv (fB ((Quotient.out originT : LinfStarBall) : LinfStar))) 0 / 2 = 0
      have hinf0 : inversion extInf = ((0 : ℂ) : ExtPlane) := by
        rw [← (tcc_inversion_eq_inf_iff ((0 : ℂ) : ExtPlane)).mpr rfl, tcc_inversion_invol]
      have hfid : fB ((Quotient.out originT : LinfStarBall) : LinfStar) =ᶠ[𝓝 (0 : ℂ)] id :=
        Filter.eventuallyEq_of_mem (isOpen_ball.mem_nhds h0D) fun w hw => s5tg_origin_fB hw
      rw [hinf0, finPart_coe, hfid.deriv.deriv_eq]
      simp
    rw [hO, hW0] at hf
    have i1 : deriv (id : ℂ → ℂ) p = 1 := deriv_id p
    have i2 : iteratedDeriv 2 (id : ℂ → ℂ) p = 0 := by simp [iteratedDeriv_succ']
    rw [i1, i2] at hf
    simp only [id] at hf
    have hrefl := s5p57_refl_of_jets hz hc hA (by rw [← hS0]; linear_combination -hf)
    rw [hS0]
    exact hrefl
  -- orthogonality and the `t`-derivative of the fibre coordinate
  have hO : ∫ u in unitDiscExterior, μ u / ((u - p) ^ 3 * (u - z)) = 0 := by
    rw [hp]
    have h := s5p57_orth_K (fderiv ℂ bersPhi 0 μ) hz
    rwa [lambda_inverse_D0bers.2.2 μ hμ] at h
  have hΦ := s5p57_Phi_deriv μ σ hpD hz
  rw [hO, mul_zero] at hΦ
  have hΦr := HasDerivAt.comp_ofReal (z := (0 : ℝ)) (by rw [Complex.ofReal_zero]; exact hΦ)
  -- the coordinate curve
  set γ : ℝ → AInf unitDisc × ℂ := fun t => (bersPhi ((t : ℂ) • μ),
    finPart (inversion (wB ((t : ℂ) • μ) (z : ExtPlane))) + deriv (deriv (fB ((t : ℂ) • μ))) 0 / 2) with hγdef
  have hγd : HasDerivAt γ (horVec μ z) 0 := s5p57_curve_deriv hμ hz
  have h0 : (0 : LinfStar) ∈ LinfStarBall := mem_ball_self one_pos
  have hγ0 : tcCoordH (fiberPt z) = γ 0 := by
    simp only [hγdef, Complex.ofReal_zero, zero_smul]
    refine Prod.ext ?_ ?_
    · exact bers_Phi ⟨0, h0⟩
    · show finPart (inversion ((z : ℂ) : ExtPlane)) +
          deriv (deriv (fB ((Quotient.out originT : LinfStarBall) : LinfStar))) 0 / 2 = _
      have hc0 : deriv (deriv (fB ((Quotient.out originT : LinfStarBall) : LinfStar))) 0 =
          deriv (deriv (fB (0 : LinfStar))) 0 := s5rh_c_congr ⟨0, h0⟩
      rw [s5vc_wB_zero, hc0]
      rfl
  set ε : ℝ := 1 / (‖μ‖ + 1) with hε
  have hεpos : 0 < ε := by positivity
  have hball : ∀ t : ℝ, |t| < ε → (t : ℂ) • μ ∈ LinfStarBall := by
    intro t ht
    show (t : ℂ) • μ ∈ ball (0 : LinfStar) 1
    rw [mem_ball_zero_iff, norm_smul, Complex.norm_real, Real.norm_eq_abs]
    rw [hε, lt_div_iff₀ (by positivity)] at ht
    nlinarith [norm_nonneg μ, abs_nonneg t]
  have hFev : (fun t : ℝ => (tcCoordExpr (fun x => tcurveMulInv x (fiberPt z)) (γ t)).2) =ᶠ[𝓝 (0 : ℝ)]
      fun t : ℝ => (σ * deriv (normalizedSolution (extB ((t : ℂ) • μ))) p /
            (normalizedSolution (extB ((t : ℂ) • μ)) z - normalizedSolution (extB ((t : ℂ) • μ)) p) +
          σ * iteratedDeriv 2 (normalizedSolution (extB ((t : ℂ) • μ))) p /
            (2 * deriv (normalizedSolution (extB ((t : ℂ) • μ))) p)) + τ / (2 * σ) := by
    filter_upwards [Ioo_mem_nhds (neg_neg_of_pos hεpos) hεpos] with t ht
    have hν := hball t (abs_lt.mpr ht)
    obtain ⟨hx, -⟩ := s5p57_fib_t hz R hR hRE hRD hRb hν
    have hγt : γ t = tcCoordH (Phi ⟨_, hν⟩, wB ((t : ℂ) • μ) (z : ExtPlane)) := by
      refine Prod.ext ?_ ?_
      · exact (bers_Phi ⟨_, hν⟩).symm
      · show _ = finPart (inversion (wB ((t : ℂ) • μ) (z : ExtPlane))) +
          deriv (deriv (fB ((Quotient.out (Phi ⟨_, hν⟩) : LinfStarBall) : LinfStar))) 0 / 2
        rw [s5rh_c_congr ⟨_, hν⟩]
    show (tcCoordH (tcurveMulInv (tcCoordHInv (γ t)) (fiberPt z))).2 = _
    rw [hγt, show tcCoordHInv (tcCoordH (Phi ⟨_, hν⟩, wB ((t : ℂ) • μ) (z : ExtPlane))) =
      (Phi ⟨_, hν⟩, wB ((t : ℂ) • μ) (z : ExtPlane)) from s5rh_injOn.leftInvOn_invFunOn hx]
    exact hform _ hν
  have hF := (hΦr.add_const (τ / (2 * σ))).congr_of_eventuallyEq hFev
  -- chain rule through `R_{q⁻¹}`
  have hL : HasFDerivAt (tcCoordExpr fun x => tcurveMulInv x (fiberPt z))
      (fderiv ℂ (tcCoordExpr fun x => tcurveMulInv x (fiberPt z)) (tcCoordH (fiberPt z))) (tcCoordH (fiberPt z)) :=
    (s5rh_mulInv_holo hq hq).hasFDerivAt
  have hcomp := (hL.restrictScalars ℝ).comp_hasDerivAt_of_eq (x := (0 : ℝ)) hγd hγ0
  have hs := ((ContinuousLinearMap.snd ℝ (AInf unitDisc) ℂ).hasFDerivAt).comp_hasDerivAt (0 : ℝ) hcomp
  exact hs.unique hF

/-- `‖·‖²_VK` at the origin is unchanged by a unimodular factor on the horizontal part. -/
theorem s5p57_unit_inv (c : ℂ) (hc : ‖c‖ = 1) (ψ : AInf unitDisc) (a : ℂ) :
    vkNormSqCoordOrigin (c • ψ, a) = vkNormSqCoordOrigin (ψ, a) := by
  simp only [vkNormSqCoordOrigin, s5t53_tangentCoeff_smul, norm_mul, hc, one_mul]

/-- **Stub P5a.** A vertical and a horizontal vector are `h_VK`-orthogonal at the origin. -/
theorem s5p57_orth (a : ℂ) (ψ : AInf unitDisc) :
    polarize vkNormSqCoordOrigin ((0 : AInf unitDisc), a) (ψ, (0 : ℂ)) = 0 := by
  have e1 : ((0 : AInf unitDisc), a) + (ψ, (0 : ℂ)) = (ψ, a) := Prod.ext (by simp) (by simp)
  have e2 : ((0 : AInf unitDisc), a) - (ψ, (0 : ℂ)) = ((-1 : ℂ) • ψ, a) :=
    Prod.ext (show (0 : AInf unitDisc) - ψ = (-1 : ℂ) • ψ by rw [zero_sub]; exact (neg_one_smul ℂ ψ).symm) (by simp)
  have e3 : ((0 : AInf unitDisc), a) + I • (ψ, (0 : ℂ)) = (I • ψ, a) := Prod.ext (by simp) (by simp)
  have e4 : ((0 : AInf unitDisc), a) - I • (ψ, (0 : ℂ)) = ((-I) • ψ, a) :=
    Prod.ext (show (0 : AInf unitDisc) - I • ψ = (-I) • ψ by rw [zero_sub]; exact (neg_smul I ψ).symm) (by simp)
  simp only [polarize]
  rw [e1, e2, e3, e4, s5p57_unit_inv (-1) (by simp), s5p57_unit_inv I (by simp), s5p57_unit_inv (-I) (by simp)]
  ring

/-- **Stub P5b.** `‖((σ_z⁻¹)^* D₀β(μ), 0)‖²_VK = ½ ∬_{𝔻*} G(z, u)|μ(u)|² ρ(u) d²u` (`lemma_5_8`). -/
theorem s5p57_hor {μ : LinfStar} (hμ : μ ∈ harmonicBeltrami) {z : ℂ} (hz : z ∈ unitDiscExterior) :
    (vkNormSqCoordOrigin (toAInf unitDisc (fun u => AInf.toFun (fderiv ℂ bersPhi 0 μ) (sigmaInv z u) * deriv (sigmaInv z) u ^ 2), (0 : ℂ)) : ℂ) =
      (1 / 2) * resolventStar (fun u => (‖μ u‖ ^ 2 : ℝ)) z := by
  obtain ⟨φ, hφ⟩ : ∃ φ : AInf unitDisc, φ = fderiv ℂ bersPhi 0 μ := ⟨_, rfl⟩
  obtain ⟨F, hF⟩ : ∃ F : ℂ → ℂ, F = fun u => AInf.toFun φ (sigmaInv z u) * deriv (sigmaInv z) u ^ 2 := ⟨_, rfl⟩
  have hσ := wp_sigmaInv_disk_conformal hz
  have hFd : DifferentiableOn ℂ F unitDisc := by
    rw [hF]; exact (φ.property.comp hσ.1 hσ.mapsTo).mul ((hσ.1.deriv isOpen_ball).pow 2)
  have hb : ∀ u ∈ unitDisc, ‖F u‖ * (1 - ‖u‖ ^ 2) ^ 2 ≤ ‖φ‖ := by
    intro u hu
    have h1 := wp_sigmaInv_pullback_norm (AInf.toFun φ) hz hu
    have h2 := wp_AInf_disc_weighted_bound φ (hσ.mapsTo hu)
    have hu1 : ‖u‖ < 1 := mem_ball_zero_iff.mp hu
    have hq : 0 < 1 - ‖u‖ ^ 2 := by nlinarith [norm_nonneg u]
    have e : (rho u)⁻¹ = (1 - ‖u‖ ^ 2) ^ 2 / 4 := by rw [rho, inv_div]
    rw [← h1, e] at h2
    rw [hF]
    nlinarith [h2]
  obtain ⟨hspec, -⟩ := toAInf_disc_spec_of_bound (norm_nonneg _) hFd hb
  obtain ⟨ψ, hψ⟩ : ∃ ψ : AInf unitDisc, ψ = toAInf unitDisc F := ⟨_, rfl⟩
  rw [← hψ] at hspec
  have ha : ∀ u ∈ unitDisc, HasSum (fun n : ℕ => (((n + 2 : ℕ) : ℂ) ^ 3 - (n + 2 : ℕ)) *
      (I * tangentCoeff ψ (n + 2)) * u ^ n) (AInf.toFun (fderiv ℂ bersPhi 0 μ) (sigmaInv z u) *
        deriv (sigmaInv z) u ^ 2) := by
    intro u hu
    have hT : HasSum (fun n : ℕ => ((n.factorial : ℂ))⁻¹ • (u - 0) ^ n • iteratedDeriv n (AInf.toFun ψ) 0)
        (AInf.toFun ψ u) := Complex.hasSum_taylorSeries_on_ball ψ.property hu
    rw [hspec u hu, hF, hφ] at hT
    convert hT using 1
    funext n
    have hne : (((n + 2 : ℕ) : ℂ) ^ 3 - (n + 2 : ℕ)) ≠ 0 := by
      have h : ((n + 1) * (n + 2) * (n + 3) : ℕ) ≠ 0 := by positivity
      have e : (((n + 2 : ℕ) : ℂ) ^ 3 - (n + 2 : ℕ)) = (((n + 1) * (n + 2) * (n + 3) : ℕ) : ℂ) := by
        push_cast; ring
      rw [e]; exact_mod_cast h
    have hf : ((n.factorial : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
    obtain ⟨D, hD⟩ : ∃ D : ℂ, D = (((n + 2 : ℕ) : ℂ) ^ 3 - (n + 2 : ℕ)) := ⟨_, rfl⟩
    rw [← hD] at hne
    simp only [tangentCoeff, show n + 2 - 2 = n by omega, smul_eq_mul, sub_zero]
    rw [← hD]
    field_simp
  have h58 := lemma_5_8 hμ hz (a := fun n => I * tangentCoeff ψ n) ha
  rw [← hφ, ← hF, ← hψ, h58]
  simp only [vkNormSqCoordOrigin, norm_mul, Complex.norm_I, one_mul, norm_zero]
  push_cast
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, add_zero]
  ring

/-- `vkNormSq q` is `vkNormSqCoordOrigin ∘ L_q`, so its polarization is that of `vkNormSqCoordOrigin` at `L_q X, L_q Y`. -/
theorem s5p57_polarize_L (q : T1 × ExtPlane) (X Y : AInf unitDisc × ℂ) :
    polarize (vkNormSq q) X Y = polarize vkNormSqCoordOrigin
      (fderiv ℂ (tcCoordExpr fun x => tcurveMulInv x q) (tcCoordH q) X)
      (fderiv ℂ (tcCoordExpr fun x => tcurveMulInv x q) (tcCoordH q) Y) := by
  simp only [polarize, vkNormSq, map_add, map_sub, map_smul]

/-- **Proposition 5.7** (assembled). -/
theorem s5p57_prop_5_7 {μ : LinfStar} (hμ : μ ∈ harmonicBeltrami) {z : ℂ} (hz : z ∈ unitDiscExterior) :
    (vkNormSq (fiberPt z) (vertVec z) = 1 / (1 - ‖z‖ ^ 2) ^ 2 ∧
      polarize (vkNormSq (fiberPt z)) (vertVec z) (horVec μ z) = 0 ∧
      (vkNormSq (fiberPt z) (horVec μ z) : ℂ) = (1 / 2) * resolventStar (fun u => (‖μ u‖ ^ 2 : ℝ)) z) ∧
    (thetaForm (fiberPt z) (vertVec z) (vertVec z) = -2 / (1 - ‖z‖ ^ 2) ^ 2 ∧
      thetaForm (fiberPt z) (vertVec z) (horVec μ z) = 0 ∧
      thetaForm (fiberPt z) (horVec μ z) (horVec μ z) = -resolventStar (fun u => (‖μ u‖ ^ 2 : ℝ)) z) ∧
    ∀ q ∈ TCurve, ∀ X : AInf unitDisc × ℂ, X ≠ 0 → (thetaForm q X X).re < 0 := by
  have hq := s5vc_fiberPt_mem hz
  set L := fderiv ℂ (tcCoordExpr fun x => tcurveMulInv x (fiberPt z)) (tcCoordH (fiberPt z)) with hL
  have hv : L (vertVec z) = ((0 : AInf unitDisc), (L (vertVec z)).2) := Prod.ext (s5p57_L_vert hz) rfl
  have hh : L (horVec μ z) = (toAInf unitDisc (fun u => AInf.toFun (fderiv ℂ bersPhi 0 μ) (sigmaInv z u) * deriv (sigmaInv z) u ^ 2), (0 : ℂ)) :=
    Prod.ext (s5p57_L_fst hz _) (s5p57_L_hor_snd hμ hz)
  have hdiag : ∀ (q : T1 × ExtPlane) X, polarize (vkNormSq q) X X = vkNormSq q X :=
    fun q X => s5t53_polarize_diag (fun a Y => s5t53_vk_smul q a Y) X
  have h1 := s5p57_vert hz
  have h2 : polarize (vkNormSq (fiberPt z)) (vertVec z) (horVec μ z) = 0 := by
    rw [s5p57_polarize_L, ← hL, hv, hh]
    exact s5p57_orth _ _
  have h3 : (vkNormSq (fiberPt z) (horVec μ z) : ℂ) = (1 / 2) * resolventStar (fun u => (‖μ u‖ ^ 2 : ℝ)) z := by
    have : vkNormSq (fiberPt z) (horVec μ z) = vkNormSqCoordOrigin (L (horVec μ z)) := rfl
    rw [this, hh]
    exact s5p57_hor hμ hz
  refine ⟨⟨h1, h2, h3⟩, ⟨?_, ?_, ?_⟩, ?_⟩
  · rw [s5p57_theta_vk hq, hdiag, h1]
    push_cast
    ring
  · rw [s5p57_theta_vk hq, h2, mul_zero]
  · rw [s5p57_theta_vk hq, hdiag, h3]
    ring
  · intro q' hq' X hX
    rw [s5p57_theta_vk hq', hdiag]
    have hp : 0 < vkNormSq q' X := s5p57_origin_pos fun h0 => hX (s5p57_L_injective hq' (by rw [h0, map_zero]))
    simp only [mul_re, neg_re, ofReal_re, ofReal_im, mul_zero, sub_zero]
    norm_num
    linarith

-- The original `prop_5_7` (S5_ChernForms) is relocated onto `s5p57_prop_5_7` by the leader.

/-- **Proposition 5.7** (TT:2398–2434), for `μ ∈ Ω^{-1,1}(𝔻*)` and `z ∈ 𝔻*`.
- (i) On `π⁻¹(0)`:
  - `⟨∂_z, ∂_z⟩_VK = 1/(1 - |z|²)²`;
  - `⟨∂_z, τ_μ⟩_VK = 0`;
  - `⟨τ_μ, τ_μ⟩_VK = ½ ∬_{𝔻*} G(z, u)|μ(u)|² ρ(u) d²u`.
- (ii) On `π⁻¹(0)`:
  - `Θ(∂_z, ∂_{z̄}) = -2/(1 - |z|²)²`;
  - `Θ(∂_z, τ_{μ̄}) = 0`;
  - `Θ(τ_μ, τ_{μ̄}) = -∬_{𝔻*} G(z, u)|μ(u)|² ρ(u) d²u`.
- (iii) `V` is a negative line bundle: `Θ(X, X̄) < 0` for `X ≠ 0`, at every point of `𝒯(1)`. -/
theorem prop_5_7 {μ : LinfStar} (hμ : μ ∈ harmonicBeltrami) {z : ℂ} (hz : z ∈ unitDiscExterior) :
    (vkNormSq (fiberPt z) (vertVec z) = 1 / (1 - ‖z‖ ^ 2) ^ 2 ∧
      polarize (vkNormSq (fiberPt z)) (vertVec z) (horVec μ z) = 0 ∧
      (vkNormSq (fiberPt z) (horVec μ z) : ℂ) = (1 / 2) * resolventStar (fun u => (‖μ u‖ ^ 2 : ℝ)) z) ∧
    (thetaForm (fiberPt z) (vertVec z) (vertVec z) = -2 / (1 - ‖z‖ ^ 2) ^ 2 ∧
      thetaForm (fiberPt z) (vertVec z) (horVec μ z) = 0 ∧
      thetaForm (fiberPt z) (horVec μ z) (horVec μ z) = -resolventStar (fun u => (‖μ u‖ ^ 2 : ℝ)) z) ∧
    ∀ q ∈ TCurve, ∀ X : AInf unitDisc × ℂ, X ≠ 0 → (thetaForm q X X).re < 0 := by
  exact s5p57_prop_5_7 hμ hz

end TakhtajanTeo
