import TakhtajanTeo.Ch2.S4GFirstVariation
import TakhtajanTeo.Ch1.S5WeldingNormalization

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal ComplexConjugate Classical Real

noncomputable section

namespace TakhtajanTeo.Ch2

open LiZhongQC

/-- `star` on `L∞(𝔻*)` is conjugate-linear. -/
theorem s3d0_star_smul (c : ℂ) (f : LinfStar) : star (c • f) = conj c • star f := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_star (c • f), Lp.coeFn_smul c f, Lp.coeFn_smul (conj c) (star f),
    Lp.coeFn_star f] with z h1 h2 h3 h4
  rw [h1, h3, Pi.star_apply, h2, Pi.smul_apply, Pi.smul_apply, h4, Pi.star_apply, smul_eq_mul, smul_eq_mul,
    star_mul', star_def]

/-- `star` on `L∞(𝔻*)` is a real continuous linear map. -/
theorem s3d0_starL : ∃ J : LinfStar →L[ℝ] LinfStar, ∀ ν, J ν = star ν := by
  let J : LinfStar →L[ℝ] LinfStar :=
    Complex.conjCLE.toContinuousLinearMap.compLpL ∞ (volume.restrict unitDiscExterior)
  refine ⟨J, fun ν => ?_⟩
  apply Lp.ext
  filter_upwards [Complex.conjCLE.toContinuousLinearMap.coeFn_compLpL (p := ∞)
    (μ := volume.restrict unitDiscExterior) ν, Lp.coeFn_star ν] with z h1 h2
  exact h1.trans h2.symm

/-- The plane solution of the `(μ, μ̄)`-coefficient is complex differentiable at `0`, with the
Ahlfors–Bers derivative `v ↦ V[s5cf_coeff v](p)`. -/
theorem s3d0_ns_fderiv (p : ℂ) :
    ∃ L : LinfStar × LinfStar →L[ℂ] ℂ, (∀ v, L v = ahVar (s5cf_coeff v) p) ∧
      HasFDerivAt (fun v : LinfStar × LinfStar => normalizedSolution (s5cf_coeff v) p) L 0 := by
  have hg0 : IsBeltramiCoeff (0 : ℂ → ℂ) univ 0 :=
    ⟨aestronglyMeasurable_zero, Filter.Eventually.of_forall fun u => by simp⟩
  have hf0 : IsNormalizedSolution id (0 : ℂ → ℂ) := by
    have h := QCV.qcv_ns_spec le_rfl zero_lt_one hg0
    rwa [bB_l_normalizedSolution_zero] at h
  have hT : ∀ v : LinfStar × LinfStar, IsBeltramiCoeff (s5cf_coeff v) univ (1 * ‖v‖) :=
    fun v => by simpa only [one_mul] using s5cf_coeff_bound v
  obtain ⟨L, hL, hd⟩ := QCV.qcv_plane_hasFDerivAt (E := LinfStar × LinfStar) (g₀ := (0 : ℂ → ℂ))
    (f₀ := id) (k := 0) le_rfl zero_lt_one hg0 hf0 s5cf_coeff zero_le_one hT s5cf_coeff_linear p
  refine ⟨L, fun v => ?_, ?_⟩
  · rw [hL v, QCV.qcv_var_source le_rfl zero_lt_one hg0 hf0 (hT v)]
    have hdz : ∀ u, dz (id : ℂ → ℂ) u = 1 := by intro u; simp [dz]
    simp only [id_eq, hdz, one_pow, mul_one, ahVar]
  · simpa only [Pi.zero_apply, zero_add] using hd

/-- The off-centre factor curve `t ↦ (a + t m) * a⁻¹` is complex differentiable at `0`, with derivative `R(m, a)`. -/
theorem s3d0_curve {a : LinfStar} (ha : a ∈ LinfStarBall) (m : LinfStar) :
    HasDerivAt (fun t : ℂ => beltramiMul (a + t • m) (beltramiInv a)) (Rnm m a) 0 ∧
      beltramiMul (a + (0 : ℂ) • m) (beltramiInv a) = 0 := by
  obtain ⟨D, hD, -⟩ := bd_hasFDerivAt (bc_beltramiInv_mem_ball ha) ha
  have hfd : fderiv ℂ (fun l => beltramiMul l (beltramiInv a)) a m = Rnm m a := bc_eq_1_5 ha m
  rw [hD.fderiv] at hfd
  have hl : HasDerivAt (fun t : ℂ => a + t • m) m 0 := by
    simpa using ((hasDerivAt_id (0 : ℂ)).smul_const m).const_add a
  refine ⟨?_, by rw [zero_smul, add_zero]; exact grp_mul_inv ha⟩
  rw [← hfd]
  exact hD.comp_hasDerivAt_of_eq 0 hl (by simp)

/-- `∂` and `∂̄` at `0` of a function whose real derivative factors through a complex linear map. -/
theorem s3d0_dz_clm {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {F : ℂ → ℂ} {Λ : E →L[ℂ] ℂ}
    {c' : ℂ →L[ℝ] E} (h : HasFDerivAt F ((Λ.restrictScalars ℝ).comp c') 0) :
    dz F 0 = Λ ((1 / 2 : ℂ) • (c' 1 - I • c' I)) ∧ dzbar F 0 = Λ ((1 / 2 : ℂ) • (c' 1 + I • c' I)) := by
  constructor
  · show (fderiv ℝ F 0 1 - I * fderiv ℝ F 0 I) / 2 = _
    rw [h.fderiv]
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_restrictScalars', map_smul, map_sub,
      smul_eq_mul]
    ring
  · show (fderiv ℝ F 0 1 + I * fderiv ℝ F 0 I) / 2 = _
    rw [h.fderiv]
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_restrictScalars', map_smul, map_add,
      smul_eq_mul]
    ring

/-- First jets at `(-1, -i, w)` of the numerator and denominator of the three-point normalization
`s5cf_three_coeff`: values `4w`, `4`, and `Dn v - w Dd v = 4 (v₃ - ℓ₁(w) v₁ - ℓ₂(w) v₂)`, where `ℓ₁, ℓ₂` are
the Lagrange basis polynomials at `-1, -i` for the nodes `-1, -i, 1`. -/
theorem s3d0_mob_jet (w : ℂ) :
    ∃ Dn Dd : ℂ × ℂ × ℂ →L[ℂ] ℂ,
      HasFDerivAt (fun x : ℂ × ℂ × ℂ => (s5cf_three_coeff x.1 x.2.1).1 * x.2.2 + (s5cf_three_coeff x.1 x.2.1).2.1)
        Dn (-1, -I, w) ∧
      HasFDerivAt (fun x : ℂ × ℂ × ℂ =>
        (s5cf_three_coeff x.1 x.2.1).2.2.1 * x.2.2 + (s5cf_three_coeff x.1 x.2.1).2.2.2) Dd (-1, -I, w) ∧
      (s5cf_three_coeff (-1) (-I)).1 * w + (s5cf_three_coeff (-1) (-I)).2.1 = 4 * w ∧
      (s5cf_three_coeff (-1) (-I)).2.2.1 * w + (s5cf_three_coeff (-1) (-I)).2.2.2 = 4 ∧
      ∀ v : ℂ × ℂ × ℂ, Dn v - w * Dd v =
        4 * (v.2.2 + (-(1 + I) * (w + I) * (w - 1) / 4) * v.1 + ((w + 1) * (w - 1) / 2) * v.2.1) := by
  set x₀ : ℂ × ℂ × ℂ := (-1, -I, w) with hx₀
  have h1 : HasFDerivAt (fun x : ℂ × ℂ × ℂ => x.1) (ContinuousLinearMap.fst ℂ ℂ (ℂ × ℂ)) x₀ := hasFDerivAt_fst
  have h2 : HasFDerivAt (fun x : ℂ × ℂ × ℂ => x.2.1)
      ((ContinuousLinearMap.fst ℂ ℂ ℂ).comp (ContinuousLinearMap.snd ℂ ℂ (ℂ × ℂ))) x₀ := hasFDerivAt_snd.fst
  have h3 : HasFDerivAt (fun x : ℂ × ℂ × ℂ => x.2.2)
      ((ContinuousLinearMap.snd ℂ ℂ ℂ).comp (ContinuousLinearMap.snd ℂ ℂ (ℂ × ℂ))) x₀ := hasFDerivAt_snd.snd
  have hA := ((h2.sub_const 1).const_mul (I - 1)).add ((h2.sub h1).const_mul (I + 1))
  have hB := ((h1.const_mul (-(I - 1))).mul (h2.sub_const 1)).sub ((h2.sub h1).const_mul (I + 1))
  have hC := ((h2.sub_const 1).const_mul (I - 1)).sub ((h2.sub h1).const_mul (I + 1))
  have hD := ((h1.const_mul (-(I - 1))).mul (h2.sub_const 1)).add ((h2.sub h1).const_mul (I + 1))
  refine ⟨_, _, (hA.mul h3).add hB, (hC.mul h3).add hD, ?_, ?_, fun v => ?_⟩
  · simp only [s5cf_three_coeff]
    linear_combination (-2 * w) * I_sq
  · simp only [s5cf_three_coeff]
    linear_combination (-2 : ℂ) * I_sq
  · simp only [hx₀, ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', smul_eq_mul,
      Pi.add_apply, Pi.sub_apply]
    linear_combination (-2 : ℂ) * v.2.2 * I_sq

/-- The kernel identity behind the three-point normalization at `-1, -i, 1`:
`K(z, u) - ℓ₁(z) K(-1, u) - ℓ₂(z) K(-i, u) = N(u, z)` for the Ahlfors–Bers kernel `K = ahKer` (nodes `0, 1, ∞`). -/
theorem s3d0_kernel {z u : ℂ} (hu0 : u ≠ 0) (hu1 : u - 1 ≠ 0) (huz : u - z ≠ 0) (hum : u + 1 ≠ 0)
    (huI : u + I ≠ 0) :
    ahKer z u + (-(1 + I) * (z + I) * (z - 1) / 4) * ahKer (-1) u + ((z + 1) * (z - 1) / 2) * ahKer (-I) u =
      (z + 1) * (z + I) * (z - 1) / ((u + 1) * (u + I) * (u - 1) * (u - z)) := by
  have hum' : u - -1 ≠ 0 := by rwa [sub_neg_eq_add]
  have huI' : u - -I ≠ 0 := by rwa [sub_neg_eq_add]
  have hQ : u * (u - 1) * (u - z) * (u + 1) * (u + I) ≠ 0 := by
    have := mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero hu0 hu1) huz) hum) huI
    exact this
  apply mul_right_cancel₀ hQ
  have e1 : ahKer z u * (u * (u - 1) * (u - z) * (u + 1) * (u + I)) = z * (z - 1) * (u + 1) * (u + I) := by
    unfold ahKer; field_simp
  have e2 : ahKer (-1) u * (u * (u - 1) * (u - z) * (u + 1) * (u + I)) =
      (-1) * (-1 - 1) * (u - z) * (u + I) := by
    unfold ahKer
    rw [div_mul_eq_mul_div, div_eq_iff (mul_ne_zero (mul_ne_zero hu0 hu1) hum')]
    ring
  have e3 : ahKer (-I) u * (u * (u - 1) * (u - z) * (u + 1) * (u + I)) =
      (-I) * (-I - 1) * (u - z) * (u + 1) := by
    unfold ahKer
    rw [div_mul_eq_mul_div, div_eq_iff (mul_ne_zero (mul_ne_zero hu0 hu1) huI')]
    ring
  have e4 : (z + 1) * (z + I) * (z - 1) / ((u + 1) * (u + I) * (u - 1) * (u - z)) *
      (u * (u - 1) * (u - z) * (u + 1) * (u + I)) = (z + 1) * (z + I) * (z - 1) * u := by
    rw [div_mul_eq_mul_div, div_eq_iff (mul_ne_zero (mul_ne_zero (mul_ne_zero hum huI) hu1) huz)]
    ring
  rw [show (ahKer z u + (-(1 + I) * (z + I) * (z - 1) / 4) * ahKer (-1) u +
      ((z + 1) * (z - 1) / 2) * ahKer (-I) u) * (u * (u - 1) * (u - z) * (u + 1) * (u + I)) =
      ahKer z u * (u * (u - 1) * (u - z) * (u + 1) * (u + I)) +
        (-(1 + I) * (z + I) * (z - 1) / 4) * (ahKer (-1) u * (u * (u - 1) * (u - z) * (u + 1) * (u + I))) +
        ((z + 1) * (z - 1) / 2) * (ahKer (-I) u * (u * (u - 1) * (u - z) * (u + 1) * (u + I))) by ring,
    e1, e2, e3, e4]
  linear_combination ((1/2 : ℂ) * u * I + (-1/2 : ℂ) * z * I + (-1/2 : ℂ) * z * u * I + (-1/2 : ℂ) * z * u ^ 2 +
    (1/2 : ℂ) * z ^ 2 * I + (1/2 : ℂ) * z ^ 2 * u + (1/2 : ℂ) * z ^ 2 * u ^ 2 + (-1/2 : ℂ) * z ^ 3 * u) * I_sq

/-- The Ahlfors–Bers variations at `z, -1, -i` combine to the three-point kernel `N(u, z)`. -/
theorem s3d0_var_combo {ν : ℂ → ℂ} {C : ℝ} (hνm : AEStronglyMeasurable ν volume) (hνb : ∀ᵐ u, ‖ν u‖ ≤ C)
    (z : ℂ) :
    ahVar ν z + (-(1 + I) * (z + I) * (z - 1) / 4) * ahVar ν (-1) + ((z + 1) * (z - 1) / 2) * ahVar ν (-I) =
      -(1 / π : ℂ) * ∫ u, ν u * ((z + 1) * (z + I) * (z - 1) / ((u + 1) * (u + I) * (u - 1) * (u - z))) := by
  have i1 := (ah_ker_integrable z).bdd_mul hνm hνb
  have i2 := ((ah_ker_integrable (-1)).bdd_mul hνm hνb).const_mul (-(1 + I) * (z + I) * (z - 1) / 4)
  have i3 := ((ah_ker_integrable (-I)).bdd_mul hνm hνb).const_mul ((z + 1) * (z - 1) / 2)
  unfold ahVar
  rw [show -(1 / π : ℂ) * (∫ u, ν u * ahKer z u) +
      (-(1 + I) * (z + I) * (z - 1) / 4) * (-(1 / π : ℂ) * ∫ u, ν u * ahKer (-1) u) +
      ((z + 1) * (z - 1) / 2) * (-(1 / π : ℂ) * ∫ u, ν u * ahKer (-I) u) =
      -(1 / π : ℂ) * ((∫ u, ν u * ahKer z u) +
        (-(1 + I) * (z + I) * (z - 1) / 4) * (∫ u, ν u * ahKer (-1) u) +
        ((z + 1) * (z - 1) / 2) * (∫ u, ν u * ahKer (-I) u)) by ring,
    ← integral_const_mul, ← integral_const_mul, ← integral_add i1 i2]
  have i12 : Integrable (fun u => ν u * ahKer z u + (-(1 + I) * (z + I) * (z - 1) / 4) * (ν u * ahKer (-1) u)) :=
    i1.add i2
  rw [← integral_add i12 i3]
  congr 1
  apply integral_congr_ae
  have hS : ({0, 1, z, -1, -I} : Set ℂ).Countable := (Set.toFinite _).countable
  filter_upwards [hS.ae_notMem volume] with u hu
  simp only [mem_insert_iff, mem_singleton_iff, not_or] at hu
  obtain ⟨hu0, hu1, huz, hum, huI⟩ := hu
  rw [← s3d0_kernel hu0 (sub_ne_zero.mpr hu1) (sub_ne_zero.mpr huz)
    (by rwa [← sub_neg_eq_add, sub_ne_zero]) (by rwa [← sub_neg_eq_add, sub_ne_zero])]
  ring

/-- The `(R, 0)` coefficient is the zero extension of `R`. -/
theorem s3d0_coeff_fst (R : LinfStar) : s5cf_coeff (R, 0) =ᵐ[volume] unitDiscExterior.indicator R := by
  have hE : MeasurableSet unitDiscExterior := (isOpen_lt continuous_const continuous_norm).measurableSet
  have h0 : ∀ᵐ x, x ∈ unitDiscExterior → (0 : LinfStar) x = 0 :=
    (ae_restrict_iff' hE).mp (Lp.coeFn_zero ℂ ∞ (volume.restrict unitDiscExterior))
  filter_upwards [ae_refl h0] with u hu
  by_cases hD : u ∈ unitDisc
  · have hE' : u ∉ unitDiscExterior := fun h =>
      (not_lt_of_ge (le_of_lt (show 1 < ‖u‖ from h))) (mem_ball_zero_iff.mp hD)
    show (if u ∈ unitDisc then extB (0 : LinfStar) (refl u) * u ^ 2 / conj u ^ 2 else extB R u) = _
    rw [if_pos hD, indicator_of_notMem hE']
    by_cases hr : refl u ∈ unitDiscExterior
    · simp only [extB, indicator_of_mem hr, hu hr, zero_mul, zero_div]
    · simp only [extB, indicator_of_notMem hr, zero_mul, zero_div]
  · show (if u ∈ unitDisc then extB (0 : LinfStar) (refl u) * u ^ 2 / conj u ^ 2 else extB R u) = _
    rw [if_neg hD]
    rfl

/-- The `(0, S)` coefficient is the reflected part `S(1/ū) u²/ū²` on `𝔻`. -/
theorem s3d0_coeff_snd (S : LinfStar) :
    s5cf_coeff (0, S) =ᵐ[volume] unitDisc.indicator (fun u => S (refl u) * u ^ 2 / conj u ^ 2) := by
  have hE : MeasurableSet unitDiscExterior := (isOpen_lt continuous_const continuous_norm).measurableSet
  have h0 : ∀ᵐ x, x ∈ unitDiscExterior → (0 : LinfStar) x = 0 :=
    (ae_restrict_iff' hE).mp (Lp.coeFn_zero ℂ ∞ (volume.restrict unitDiscExterior))
  filter_upwards [h0] with u hu
  by_cases hD : u ∈ unitDisc
  · show (if u ∈ unitDisc then extB S (refl u) * u ^ 2 / conj u ^ 2 else extB (0 : LinfStar) u) = _
    rw [if_pos hD, indicator_of_mem hD]
    by_cases hu0 : u = 0
    · subst hu0
      simp
    · have hr : refl u ∈ unitDiscExterior := (refl_mem_exterior_iff hu0).mpr hD
      simp only [extB, indicator_of_mem hr]
  · show (if u ∈ unitDisc then extB S (refl u) * u ^ 2 / conj u ^ 2 else extB (0 : LinfStar) u) = _
    rw [if_neg hD, indicator_of_notMem hD]
    by_cases hE' : u ∈ unitDiscExterior
    · simp only [extB, indicator_of_mem hE', hu hE']
    · simp only [extB, indicator_of_notMem hE']

/-- **(D0)** First variation of the Model A welding factor `γ̂_t = w_{λ_t}` on `𝔻*` (Ahlfors–Bers for the
three-point normalization at `-1, -i, 1`; `extA` reflection for the `t̄`-part).
At `κ = 0, a = 0` (`λ_t = t m`, `R = m`): `∂_z³ N(ζ, z) = 6/(ζ - z)⁴`, so `∂_z³` of the `t̄`-part is
`-(6/π) ∫_{𝔻*} conj m(w)/(1 - w̄ z)⁴` (substitute `ζ = 1/w̄`) `= s4ma_wA_variation`, and `∂_z³` of the `t`-part is
`-(6/π) ∫_{𝔻*} m/(ζ - z)⁴ = ∂_z³ ahVar (extB m) = s4hv_wA_holomorphic_variation`. -/
theorem s3d_D0 {κ : LinfStarBall} (hκ : Phi κ ∈ T01)
    (hκD : ∃ L : List (A2 unitDisc), (∀ φ ∈ L, (∃ q : Polynomial ℂ, ∀ z ∈ unitDisc, A2.toFun φ z = q.eval z) ∧
      ‖φ‖ < min (Real.sqrt (π / 3)) (2 * delta0 / Real.sqrt (12 / π))) ∧
      (κ : LinfStar) = L.foldr (fun φ acc => beltramiMul (Lambda (A2toAInf φ)) acc) 0)
    {a : LinfStar} (ha : a ∈ harmonicBeltrami) (has : ‖a‖ < delta0) (haL : normL2 unitDiscExterior a < ∞)
    (haD : ∃ ψ : A2 unitDisc, (∃ q : Polynomial ℂ, ∀ z ∈ unitDisc, A2.toFun ψ z = q.eval z) ∧ a = Lambda (A2toAInf ψ))
    {m : ℂ → ℂ} (hm : m ∈ harmonicL2 unitDiscExterior)
    (hmD : ∃ ψ : A2 unitDisc, (∃ q : Polynomial ℂ, ∀ z ∈ unitDisc, A2.toFun ψ z = q.eval z) ∧
      toLinf m = Lambda (A2toAInf ψ)) :
    ∀ z ∈ unitDiscExterior,
      DifferentiableAt ℝ (fun t : ℂ => wA (beltramiMul (a + t • toLinf m) (beltramiInv a)) z) 0 ∧
      dz (fun t : ℂ => wA (beltramiMul (a + t • toLinf m) (beltramiInv a)) z) 0 =
        -(1 / π : ℂ) * ∫ ζ in unitDiscExterior, RnmFun (toLinf m) a ζ *
          ((z + 1) * (z + I) * (z - 1) / ((ζ + 1) * (ζ + I) * (ζ - 1) * (ζ - z))) ∧
      dzbar (fun t : ℂ => wA (beltramiMul (a + t • toLinf m) (beltramiInv a)) z) 0 =
        -(1 / π : ℂ) * ∫ ζ in unitDisc, conj (RnmFun (toLinf m) a (1 / conj ζ)) * ζ ^ 2 / conj ζ ^ 2 *
          ((z + 1) * (z + I) * (z - 1) / ((ζ + 1) * (ζ + I) * (ζ - 1) * (ζ - z))) := by
  -- the frozen hypotheses `hκ`, `hκD`, `ha`, `haL`, `haD`, `hm`, `hmD` are not needed: D0 is the first variation of
  -- `w_λ` at `λ = 0` along any curve `λ_t` that is complex differentiable in `L∞` (only `‖a‖ < 1` is used)
  have _h := And.intro hκ (And.intro hκD (And.intro ha (And.intro haL (And.intro haD (And.intro hm hmD)))))
  intro z _hz
  have ha1 : a ∈ LinfStarBall := mem_ball_zero_iff.mpr (has.trans delta0_bounds.2)
  have hE : MeasurableSet unitDiscExterior := (isOpen_lt continuous_const continuous_norm).measurableSet
  obtain ⟨hlc, hlc0⟩ := s3d0_curve ha1 (toLinf m)
  obtain ⟨J, hJ⟩ := s3d0_starL
  obtain ⟨R, hRdef⟩ : ∃ R : LinfStar, R = Rnm (toLinf m) a := ⟨_, rfl⟩
  rw [← hRdef] at hlc
  obtain ⟨lam, hlam⟩ : ∃ lam : ℂ → LinfStar, lam = fun t => beltramiMul (a + t • toLinf m) (beltramiInv a) :=
    ⟨_, rfl⟩
  rw [← hlam] at hlc
  have hlam0 : lam 0 = 0 := by rw [hlam]; exact hlc0
  obtain ⟨e1, he1⟩ : ∃ e1 : ℂ →L[ℝ] LinfStar,
      e1 = (ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) R).restrictScalars ℝ := ⟨_, rfl⟩
  have hlamR : HasFDerivAt lam e1 0 := by rw [he1]; exact hlc.hasFDerivAt.restrictScalars ℝ
  have he1v : ∀ t : ℂ, e1 t = t • R := fun t => by rw [he1]; simp
  obtain ⟨c, hcdef⟩ : ∃ c : ℂ → LinfStar × LinfStar, c = fun t => (lam t, J (lam t)) := ⟨_, rfl⟩
  have hc : HasFDerivAt c (e1.prod (J.comp e1)) 0 := by
    rw [hcdef]; exact hlamR.prodMk (J.hasFDerivAt.comp 0 hlamR)
  have hc0 : c 0 = 0 := by rw [hcdef]; simp only [hlam0, map_zero]; rfl
  -- the plane solutions at `0` are the identity
  have hN0 : ∀ p, normalizedSolution (s5cf_coeff 0) p = p := by
    intro p
    have hb := s5cf_coeff_bound (0 : LinfStar × LinfStar)
    rw [norm_zero] at hb
    have hz0 : s5cf_coeff 0 =ᵐ[volume] (0 : ℂ → ℂ) := by
      have h2 := hb.2
      rw [Measure.restrict_univ] at h2
      filter_upwards [h2] with u hu
      simpa using hu
    rw [QCV.qcv_ns_congr_ae le_rfl zero_lt_one hb hz0, bB_l_normalizedSolution_zero]
    rfl
  obtain ⟨L1, hL1, hd1⟩ := s3d0_ns_fderiv (-1)
  obtain ⟨L2, hL2, hd2⟩ := s3d0_ns_fderiv (-I)
  obtain ⟨L3, hL3, hd3⟩ := s3d0_ns_fderiv z
  have hΘ : HasFDerivAt (fun v : LinfStar × LinfStar => (normalizedSolution (s5cf_coeff v) (-1),
      normalizedSolution (s5cf_coeff v) (-I), normalizedSolution (s5cf_coeff v) z)) (L1.prod (L2.prod L3)) (c 0) := by
    rw [hc0]; exact hd1.prodMk (hd2.prodMk hd3)
  obtain ⟨G, hGdef⟩ : ∃ G : ℂ → ℂ × ℂ × ℂ, G = fun t => (normalizedSolution (s5cf_coeff (c t)) (-1),
      normalizedSolution (s5cf_coeff (c t)) (-I), normalizedSolution (s5cf_coeff (c t)) z) := ⟨_, rfl⟩
  have hG : HasFDerivAt G (((L1.prod (L2.prod L3)).restrictScalars ℝ).comp (e1.prod (J.comp e1))) 0 := by
    rw [hGdef]; exact (hΘ.restrictScalars ℝ).comp 0 hc
  have hG0 : G 0 = (-1, -I, z) := by rw [hGdef]; simp only [hc0, hN0]
  obtain ⟨Dn, Dd, hDn, hDd, hn0, hd0, hDv⟩ := s3d0_mob_jet z
  rw [← hG0] at hDn hDd
  obtain ⟨numG, hnumG⟩ : ∃ f : ℂ → ℂ, f = fun t =>
      (s5cf_three_coeff (G t).1 (G t).2.1).1 * (G t).2.2 + (s5cf_three_coeff (G t).1 (G t).2.1).2.1 := ⟨_, rfl⟩
  obtain ⟨denG, hdenG⟩ : ∃ f : ℂ → ℂ, f = fun t =>
      (s5cf_three_coeff (G t).1 (G t).2.1).2.2.1 * (G t).2.2 + (s5cf_three_coeff (G t).1 (G t).2.1).2.2.2 :=
    ⟨_, rfl⟩
  have hnum : HasFDerivAt numG (((Dn.comp (L1.prod (L2.prod L3))).restrictScalars ℝ).comp
      (e1.prod (J.comp e1))) 0 := by
    rw [hnumG]; exact ((hDn.restrictScalars ℝ).comp 0 hG).congr_fderiv (ContinuousLinearMap.ext fun v => rfl)
  have hden : HasFDerivAt denG (((Dd.comp (L1.prod (L2.prod L3))).restrictScalars ℝ).comp
      (e1.prod (J.comp e1))) 0 := by
    rw [hdenG]; exact ((hDd.restrictScalars ℝ).comp 0 hG).congr_fderiv (ContinuousLinearMap.ext fun v => rfl)
  have hn0' : numG 0 = 4 * z := by rw [hnumG]; simp only [hG0]; exact hn0
  have hd0' : denG 0 = 4 := by rw [hdenG]; simp only [hG0]; exact hd0
  -- `w_{λ_t}(z) = numG t / denG t` near `t = 0`
  have hball : ∀ᶠ t in 𝓝 (0 : ℂ), lam t ∈ LinfStarBall :=
    hlamR.continuousAt.eventually (isOpen_ball.mem_nhds (by rw [hlam0]; exact mem_ball_self one_pos))
  have hne : ∀ᶠ t in 𝓝 (0 : ℂ), denG t ≠ 0 :=
    hden.continuousAt.eventually_ne (by rw [hd0']; norm_num)
  have hFeq : (fun t : ℂ => wA (beltramiMul (a + t • toLinf m) (beltramiInv a)) z) =ᶠ[𝓝 0]
      fun t => numG t / denG t := by
    filter_upwards [hball, hne] with t hb ht
    have hct : c t = (lam t, star (lam t)) := by rw [hcdef]; show (lam t, J (lam t)) = _; rw [hJ]
    have hrep := s5cf_wAS_rep hb (z : ExtPlane)
    rw [← s5cf_plane_diagonal hb, OnePoint.map_some] at hrep
    have ht' : (s5cf_normCoeffs (lam t, star (lam t))).2.2.1 *
        normalizedSolution (s5cf_coeff (lam t, star (lam t))) z +
        (s5cf_normCoeffs (lam t, star (lam t))).2.2.2 ≠ 0 := by
      rw [← hct]; rw [hdenG, hGdef] at ht; exact ht
    have hw : wA (lam t) z = numG t / denG t := by
      show finPart (wAS (lam t) (z : ExtPlane)) = _
      rw [hrep, mobiusExt_coe ht', finPart_coe]
      simp only [hnumG, hdenG, hGdef, mobiusFn]
      rw [hct]
      rfl
    rw [hlam] at hw
    exact hw
  have hinv : DifferentiableAt ℝ (fun t => (denG t)⁻¹) 0 :=
    ((differentiableAt_inv (𝕜 := ℂ) (show denG 0 ≠ 0 by rw [hd0']; norm_num)).restrictScalars ℝ).comp 0
      hden.differentiableAt
  have hQd : DifferentiableAt ℝ (fun t => numG t / denG t) 0 := by
    simpa only [div_eq_mul_inv] using hnum.differentiableAt.fun_mul hinv
  have hQ0 : numG 0 / denG 0 = z := by rw [hn0', hd0']; field_simp
  have hprod : (fun t => numG t) =ᶠ[𝓝 0] fun t => numG t / denG t * denG t := by
    filter_upwards [hne] with t ht
    rw [div_mul_cancel₀ _ ht]
  -- the two tangent vectors
  have hv1 : (1 / 2 : ℂ) • ((e1.prod (J.comp e1)) 1 - I • (e1.prod (J.comp e1)) I) = (R, 0) := by
    simp only [ContinuousLinearMap.prod_apply, ContinuousLinearMap.comp_apply, he1v, hJ, s3d0_star_smul,
      Complex.conj_I, Prod.smul_mk, Prod.mk_sub_mk, one_smul, smul_smul]
    ext1
    · simp only [I_mul_I]; module
    · simp only [mul_neg, I_mul_I, neg_neg]; module
  have hv2 : (1 / 2 : ℂ) • ((e1.prod (J.comp e1)) 1 + I • (e1.prod (J.comp e1)) I) = (0, star R) := by
    simp only [ContinuousLinearMap.prod_apply, ContinuousLinearMap.comp_apply, he1v, hJ, s3d0_star_smul,
      Complex.conj_I, Prod.smul_mk, Prod.mk_add_mk, one_smul, smul_smul]
    ext1
    · simp only [I_mul_I]; module
    · simp only [mul_neg, I_mul_I, neg_neg]; module
  obtain ⟨hnz, hnzb⟩ := s3d0_dz_clm hnum
  obtain ⟨hdz, hdzb⟩ := s3d0_dz_clm hden
  have hnz' : dz numG 0 = (Dn.comp (L1.prod (L2.prod L3))) (R, 0) := hnz.trans (congrArg _ hv1)
  have hdz' : dz denG 0 = (Dd.comp (L1.prod (L2.prod L3))) (R, 0) := hdz.trans (congrArg _ hv1)
  have hnzb' : dzbar numG 0 = (Dn.comp (L1.prod (L2.prod L3))) (0, star R) := hnzb.trans (congrArg _ hv2)
  have hdzb' : dzbar denG 0 = (Dd.comp (L1.prod (L2.prod L3))) (0, star R) := hdzb.trans (congrArg _ hv2)
  have hdzF : dz (fun t : ℂ => wA (beltramiMul (a + t • toLinf m) (beltramiInv a)) z) 0 =
      dz (fun t => numG t / denG t) 0 := by
    show (fderiv ℝ _ 0 1 - I * fderiv ℝ _ 0 I) / 2 = (fderiv ℝ _ 0 1 - I * fderiv ℝ _ 0 I) / 2
    rw [hFeq.fderiv_eq]
  have hdzbF : dzbar (fun t : ℂ => wA (beltramiMul (a + t • toLinf m) (beltramiInv a)) z) 0 =
      dzbar (fun t => numG t / denG t) 0 := by
    show (fderiv ℝ _ 0 1 + I * fderiv ℝ _ 0 I) / 2 = (fderiv ℝ _ 0 1 + I * fderiv ℝ _ 0 I) / 2
    rw [hFeq.fderiv_eq]
  have hmul : dz numG 0 = z * dz denG 0 + 4 * dz (fun t => numG t / denG t) 0 := by
    have h := dz_mul hQd hden.differentiableAt
    rw [hQ0, hd0'] at h
    rw [← h]
    show (fderiv ℝ _ 0 1 - I * fderiv ℝ _ 0 I) / 2 = (fderiv ℝ _ 0 1 - I * fderiv ℝ _ 0 I) / 2
    rw [hprod.fderiv_eq]
  have hmulb : dzbar numG 0 = z * dzbar denG 0 + 4 * dzbar (fun t => numG t / denG t) 0 := by
    have h := dzbar_mul hQd hden.differentiableAt
    rw [hQ0, hd0'] at h
    rw [← h]
    show (fderiv ℝ _ 0 1 + I * fderiv ℝ _ 0 I) / 2 = (fderiv ℝ _ 0 1 + I * fderiv ℝ _ 0 I) / 2
    rw [hprod.fderiv_eq]
  have hval : ∀ v : LinfStar × LinfStar, (4 : ℂ) * ((ahVar (s5cf_coeff v) z) +
      (-(1 + I) * (z + I) * (z - 1) / 4) * ahVar (s5cf_coeff v) (-1) +
      ((z + 1) * (z - 1) / 2) * ahVar (s5cf_coeff v) (-I)) =
      Dn ((L1.prod (L2.prod L3)) v) - z * Dd ((L1.prod (L2.prod L3)) v) := by
    intro v
    rw [hDv]
    simp only [ContinuousLinearMap.prod_apply, hL1, hL2, hL3]
  refine ⟨hQd.congr_of_eventuallyEq hFeq, ?_, ?_⟩
  · rw [hdzF]
    have h4 : (4 : ℂ) * dz (fun t => numG t / denG t) 0 = 4 * ((ahVar (s5cf_coeff (R, 0)) z) +
        (-(1 + I) * (z + I) * (z - 1) / 4) * ahVar (s5cf_coeff (R, 0)) (-1) +
        ((z + 1) * (z - 1) / 2) * ahVar (s5cf_coeff (R, 0)) (-I)) := by
      rw [hval]
      simp only [ContinuousLinearMap.comp_apply] at hnz' hdz'
      rw [← hnz', ← hdz', hmul]; ring
    have h4' := mul_left_cancel₀ (by norm_num : (4 : ℂ) ≠ 0) h4
    have hb := s5cf_coeff_bound (R, 0)
    have hb2 := hb.2
    rw [Measure.restrict_univ] at hb2
    have hb1 : AEStronglyMeasurable (s5cf_coeff (R, 0)) volume := by
      simpa only [Measure.restrict_univ] using hb.1
    rw [h4', s3d0_var_combo hb1 hb2 z]
    congr 1
    have hI : ∫ u, s5cf_coeff (R, 0) u * ((z + 1) * (z + I) * (z - 1) / ((u + 1) * (u + I) * (u - 1) * (u - z))) =
        ∫ u, unitDiscExterior.indicator (fun u => R u * ((z + 1) * (z + I) * (z - 1) / ((u + 1) * (u + I) * (u - 1) * (u - z)))) u :=
      integral_congr_ae (by
        filter_upwards [s3d0_coeff_fst R] with u hu
        rw [hu, indicator_mul_left])
    rw [hI]
    rw [integral_indicator hE]
    refine setIntegral_congr_ae hE ?_
    filter_upwards [(ae_restrict_iff' hE).mp (bc_Rnm_ae ha1 (toLinf m))] with u hu huE
    rw [hRdef, hu huE]
    rfl
  · rw [hdzbF]
    have h4 : (4 : ℂ) * dzbar (fun t => numG t / denG t) 0 = 4 * ((ahVar (s5cf_coeff (0, star R)) z) +
        (-(1 + I) * (z + I) * (z - 1) / 4) * ahVar (s5cf_coeff (0, star R)) (-1) +
        ((z + 1) * (z - 1) / 2) * ahVar (s5cf_coeff (0, star R)) (-I)) := by
      rw [hval]
      simp only [ContinuousLinearMap.comp_apply] at hnzb' hdzb'
      rw [← hnzb', ← hdzb', hmulb]; ring
    have h4' := mul_left_cancel₀ (by norm_num : (4 : ℂ) ≠ 0) h4
    have hb := s5cf_coeff_bound (0, star R)
    have hb2 := hb.2
    rw [Measure.restrict_univ] at hb2
    have hb1 : AEStronglyMeasurable (s5cf_coeff (0, star R)) volume := by
      simpa only [Measure.restrict_univ] using hb.1
    rw [h4', s3d0_var_combo hb1 hb2 z]
    congr 1
    have hI : ∫ u, s5cf_coeff (0, star R) u * ((z + 1) * (z + I) * (z - 1) / ((u + 1) * (u + I) * (u - 1) * (u - z))) =
        ∫ u, unitDisc.indicator (fun u => star R (refl u) * u ^ 2 / conj u ^ 2 * ((z + 1) * (z + I) * (z - 1) / ((u + 1) * (u + I) * (u - 1) * (u - z)))) u :=
      integral_congr_ae (by
        filter_upwards [s3d0_coeff_snd (star R)] with u hu
        rw [hu, indicator_mul_left])
    rw [hI]
    have hD : MeasurableSet unitDisc := measurableSet_ball
    rw [integral_indicator hD]
    refine setIntegral_congr_ae hD ?_
    have hs := ae_refl ((ae_restrict_iff' hE).mp (Lp.coeFn_star R))
    have hr := ae_refl ((ae_restrict_iff' hE).mp (bc_Rnm_ae ha1 (toLinf m)))
    filter_upwards [hs, hr] with u hs hr huD
    by_cases hu0 : u = 0
    · subst hu0; simp
    · have hre : refl u ∈ unitDiscExterior := (refl_mem_exterior_iff hu0).mpr huD
      rw [hs hre, Pi.star_apply, hRdef, hr hre, Complex.star_def]
      have h1 : refl u = 1 / conj u := by rw [one_div]; rfl
      rw [h1]
      rfl

end TakhtajanTeo.Ch2
