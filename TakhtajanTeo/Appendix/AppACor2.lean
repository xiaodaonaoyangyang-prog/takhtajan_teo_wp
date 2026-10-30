import TakhtajanTeo.Appendix.AppA5Conj5
import TakhtajanTeo.Appendix.AppACompleted
import TakhtajanTeo.Appendix.AppACont

/-!
# Appendix A, Corollary A.2: `β̂(𝒯₀(1))` is open in `A₂¹(𝔻)` (`ac2_`, 下属2)

Host: new module `Appendix/AppACor2.lean`. `cor_A_2` is relocated here from `A_HilbertStructure` (no consumers);
`ac2_cor_A_2` is its byte-identical copy.

Route (no inverse function theorem): `β̂(p, w) = 𝒜(λ_c ∘ 𝖿^p)`, `c = -1/𝗀_p(w)`; `Ψ` is injective given the value at `0`
(`PsiOp_injective_with_value`).
1. `ac2_sub` (first conjunct): `betaHat_spec`.
2. continuity of `Ψ` on `A₂¹(𝔻)` (`ac2_ptwise_disc`, `ac2_deriv_disc`, `ac2_mul_disc`, `ac2_psi_cont_disc`; 下属4);
3. the Bers image near `𝒮(𝖿^p)`, with control of the class (`ac2_bers_nbhd`, from `bers_isOpenEmbedding`);
4. the pole parameter: `q ↦ 𝖿^q''(0)` is continuous on `T(1)` (`ac2_fpp_cont`) and `𝗀_q(𝔻*)` contains a fixed ball
   around `𝗀_p(w)` for `q` near `p` (`ac2_g_open`) (下属3 / 下属5);
5. `𝒜(λ_c ∘ f)(0) = f''(0) - 2c` and `Ψ(𝒜(λ_c ∘ f)) = 𝒮(f)` (`ac2_betaHat_zero`, `ac2_psi_betaHat`); for `φ` near `ψ`
   take `q` from step 3, `c = (𝖿^q''(0) - φ(0))/2`, `w'` with `𝗀_q(w') = -1/c` from step 4, and conclude
   `φ = β̂(q, w')` by injectivity (`ac2_core`).
-/

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal ComplexConjugate Classical Real
noncomputable section
namespace TakhtajanTeo
open LiZhongQC Ch2
namespace AppA

/-! ### Step 1 -/

/-- `β̂(𝒯₀(1)) ⊆ A₂¹(𝔻)`. -/
theorem ac2_sub : betaHatT0 ⊆ A21fun unitDisc := by
  rintro ψ ⟨p, hp, w, hw, heq⟩
  exact (ab112_A21fun_congr (U := unitDisc) isOpen_ball heq).2 (((betaHat_spec p hw).1).2 hp)

/-! ### Step 2: continuity of `Ψ` on `A₂¹(𝔻)` (下属4) -/

/-- The coefficient comparison behind `ac2_deriv_disc`. -/
theorem ac2_coef_le (n : ℕ) (a : ℝ) :
    (π / 2) * ((((n : ℝ) + 1) * a) ^ 2 / (((n : ℝ) + 1) * ((n : ℝ) + 2) * ((n : ℝ) + 3))) ≤
      1 / 2 * (π * a ^ 2 / ((n : ℝ) + 1 + 1)) := by
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have e1 : (π / 2) * ((((n : ℝ) + 1) * a) ^ 2 / (((n : ℝ) + 1) * ((n : ℝ) + 2) * ((n : ℝ) + 3))) =
      π * a ^ 2 * (((n : ℝ) + 1) / (2 * ((n : ℝ) + 2) * ((n : ℝ) + 3))) := by
    field_simp
  have e2 : 1 / 2 * (π * a ^ 2 / ((n : ℝ) + 1 + 1)) = π * a ^ 2 * (1 / (2 * ((n : ℝ) + 2))) := by
    field_simp; ring
  rw [e1, e2]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith

/-- Point evaluation on `A₂¹(𝔻)`: `(1 - |z|²)|φ(z)| ≤ ‖φ‖_{A₂¹}/√π`. -/
theorem ac2_ptwise_disc {φ : ℂ → ℂ} (hφ : φ ∈ A21fun unitDisc) {z : ℂ} (hz : z ∈ unitDisc) :
    (1 - ‖z‖ ^ 2) * ‖φ z‖ ≤ (normA21 unitDisc φ).toReal / Real.sqrt π := by
  have h := lemma_1_3 (Or.inl rfl) hφ z hz
  rw [← ENNReal.ofReal_toReal hφ.2.ne, ← ENNReal.ofReal_mul (by positivity : 0 ≤ 1 / Real.sqrt π)] at h
  have h2 := (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp h
  have hz1 : ‖z‖ < 1 := mem_ball_zero_iff.mp hz
  have he : ‖(1 - ‖z‖ ^ 2 : ℂ) * φ z‖ = (1 - ‖z‖ ^ 2) * ‖φ z‖ := by
    rw [norm_mul]
    congr 1
    have : ((1 - ‖z‖ ^ 2 : ℝ) : ℂ) = (1 - ‖z‖ ^ 2 : ℂ) := by push_cast; ring
    rw [← this, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by nlinarith [norm_nonneg z])]
  have he' : ‖((1 : ℂ) - (‖z‖ : ℂ) ^ 2) * φ z‖ = ‖(1 - ‖z‖ ^ 2 : ℂ) * φ z‖ := rfl
  rw [he', he] at h2
  calc (1 - ‖z‖ ^ 2) * ‖φ z‖ ≤ 1 / Real.sqrt π * (normA21 unitDisc φ).toReal := h2
    _ = _ := by ring

/-- `‖h'‖_{A₂(𝔻)} ≤ C ‖h‖_{A₂¹(𝔻)}` on all of `A₂¹(𝔻)`. -/
theorem ac2_deriv_disc : ∃ C : ℝ, ∀ h ∈ A21fun unitDisc,
    normA2 unitDisc (deriv h) ≤ ENNReal.ofReal C * normA21 unitDisc h := by
  refine ⟨Real.sqrt (1 / 2), fun h hh => ?_⟩
  let c : ℕ → ℂ := fun n => (n.factorial : ℂ)⁻¹ * iteratedDeriv n h 0
  have hqs : ∀ z ∈ unitDisc, HasSum (fun n => c n * z ^ n) (h z) := by
    intro z hz
    have h' := Complex.hasSum_taylorSeries_on_ball (c := 0) (r := 1) hh.1 hz
    refine h'.congr_fun fun n => ?_
    simp only [c, sub_zero, smul_eq_mul]
    ring
  have hdq : DifferentiableOn ℂ (deriv h) unitDisc := hh.1.deriv isOpen_ball
  have hq's : ∀ z ∈ unitDisc, HasSum (fun n : ℕ => ((n : ℂ) + 1) * c (n + 1) * z ^ n) (deriv h z) := by
    intro z hz
    have h' := Complex.hasSum_taylorSeries_on_ball (c := 0) (r := 1) hdq hz
    refine h'.congr_fun fun n => ?_
    simp only [c, sub_zero, smul_eq_mul, ← iteratedDeriv_succ', Nat.factorial_succ]
    push_cast
    field_simp
  have hW := a55_weighted_le (F := deriv h) (d := fun n : ℕ => ((n : ℂ) + 1) * c (n + 1))
    (fun z hz => hq's z hz.1)
  have hcoef : ∀ n : ℕ, ENNReal.ofReal ((π / 2) * (‖((n : ℂ) + 1) * c (n + 1)‖ ^ 2 /
      (((n : ℝ) + 1) * ((n : ℝ) + 2) * ((n : ℝ) + 3)))) ≤
      ENNReal.ofReal (1 / 2) * ENNReal.ofReal (π * ‖c (n + 1)‖ ^ 2 / (((n + 1 : ℕ) : ℝ) + 1)) := by
    intro n
    rw [← ENNReal.ofReal_mul (by norm_num)]
    apply ENNReal.ofReal_le_ofReal
    have hd : ‖((n : ℂ) + 1) * c (n + 1)‖ = ((n : ℝ) + 1) * ‖c (n + 1)‖ := by
      rw [norm_mul]
      congr 1
      have : ((n : ℂ) + 1) = (((n : ℝ) + 1 : ℝ) : ℂ) := by push_cast; ring
      rw [this, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    rw [hd, Nat.cast_add, Nat.cast_one]
    exact ac2_coef_le n _
  have hpars := s2c_area_parseval_lintegral hqs
  have hshift : (∑' n : ℕ, ENNReal.ofReal (π * ‖c (n + 1)‖ ^ 2 / (((n + 1 : ℕ) : ℝ) + 1))) ≤
      ∑' n, ENNReal.ofReal (π * ‖c n‖ ^ 2 / ((n : ℝ) + 1)) := by
    exact le_add_self.trans
      (tsum_eq_zero_add' (f := fun n : ℕ => ENNReal.ofReal (π * ‖c n‖ ^ 2 / ((n : ℝ) + 1))) ENNReal.summable).ge
  have hqsq : (∫⁻ z in unitDisc, ENNReal.ofReal (‖h z‖ ^ 2)) = normA21 unitDisc h ^ 2 := by
    rw [a55_normA21_sq]
    exact lintegral_congr fun z => a55_ofReal_sq _
  have hL : normA2 unitDisc (deriv h) ^ 2 =
      ∫⁻ z in unitDisc, ENNReal.ofReal (‖deriv h z‖ ^ 2 * (rho z)⁻¹) := by
    rw [a55_normA2_sq]
    refine setLIntegral_congr_fun measurableSet_ball fun z _ => ?_
    rw [ENNReal.ofReal_mul (sq_nonneg _), a55_ofReal_sq]
  apply a55_le_of_sq_le
  rw [hL, mul_pow, ← ENNReal.ofReal_pow (Real.sqrt_nonneg _), Real.sq_sqrt (by norm_num), ← hqsq, hpars]
  calc _ ≤ _ := hW
    _ ≤ _ := ENNReal.tsum_le_tsum hcoef
    _ = ENNReal.ofReal (1 / 2) *
        ∑' n : ℕ, ENNReal.ofReal (π * ‖c (n + 1)‖ ^ 2 / (((n + 1 : ℕ) : ℝ) + 1)) := ENNReal.tsum_mul_left
    _ ≤ _ := by gcongr

/-- `‖hk‖_{A₂(𝔻)} ≤ C ‖h‖_{A₂¹(𝔻)} ‖k‖_{A₂¹(𝔻)}`. -/
theorem ac2_mul_disc : ∃ C : ℝ, ∀ h ∈ A21fun unitDisc, ∀ k ∈ A21fun unitDisc,
    normA2 unitDisc (fun z => h z * k z) ≤ ENNReal.ofReal C * normA21 unitDisc h * normA21 unitDisc k := by
  refine ⟨1 / (2 * Real.sqrt π), fun h hh k hk => ?_⟩
  have hE : MeasurableSet unitDisc := measurableSet_ball
  set N := (normA21 unitDisc k).toReal with hN
  have hpt : ∀ z ∈ unitDisc, ‖k z‖ ^ 2 * (rho z)⁻¹ ≤ (1 / (2 * Real.sqrt π)) ^ 2 * N ^ 2 := by
    intro z hz
    have h1 := ac2_ptwise_disc hk hz
    have hz1 : ‖z‖ < 1 := mem_ball_zero_iff.mp hz
    have hw : (rho z)⁻¹ = (1 - ‖z‖ ^ 2) ^ 2 / 4 := by
      unfold rho
      rw [inv_div]
    have h0 : 0 ≤ (1 - ‖z‖ ^ 2) * ‖k z‖ := by
      have : 0 ≤ 1 - ‖z‖ ^ 2 := by nlinarith [norm_nonneg z]
      positivity
    have h2 := pow_le_pow_left₀ h0 h1 2
    rw [hw]
    have e : (1 / (2 * Real.sqrt π)) ^ 2 * N ^ 2 = (N / Real.sqrt π) ^ 2 / 4 := by
      field_simp; ring
    rw [e]
    calc ‖k z‖ ^ 2 * ((1 - ‖z‖ ^ 2) ^ 2 / 4) = ((1 - ‖z‖ ^ 2) * ‖k z‖) ^ 2 / 4 := by ring
      _ ≤ _ := by gcongr
  apply a55_le_of_sq_le
  rw [a55_normA2_sq, mul_pow, mul_pow, a55_normA21_sq, a55_normA21_sq]
  have hk2 : (∫⁻ z in unitDisc, (‖k z‖₊ : ℝ≥0∞) ^ 2) = ENNReal.ofReal (N ^ 2) := by
    rw [← a55_normA21_sq, hN, ENNReal.ofReal_pow ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hk.2.ne]
  have hR : ENNReal.ofReal (1 / (2 * Real.sqrt π)) ^ 2 * (∫⁻ z in unitDisc, (‖h z‖₊ : ℝ≥0∞) ^ 2) *
      ENNReal.ofReal (N ^ 2) =
      ∫⁻ z in unitDisc, ENNReal.ofReal ((1 / (2 * Real.sqrt π)) ^ 2 * N ^ 2) * (‖h z‖₊ : ℝ≥0∞) ^ 2 := by
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ← ENNReal.ofReal_pow (by positivity),
      ENNReal.ofReal_mul (sq_nonneg _)]
    ring
  rw [hk2, hR]
  refine setLIntegral_mono' hE fun z hz => ?_
  rw [nnnorm_mul, ENNReal.coe_mul, mul_pow, mul_assoc, mul_comm (ENNReal.ofReal _)]
  gcongr
  have hc : ((‖k z‖₊ : ℝ≥0∞)) ^ 2 * ENNReal.ofReal (rho z)⁻¹ = ENNReal.ofReal (‖k z‖ ^ 2 * (rho z)⁻¹) := by
    rw [ENNReal.ofReal_mul (sq_nonneg _), a55_ofReal_sq]
  rw [hc]
  exact ENNReal.ofReal_le_ofReal (hpt z hz)

/-- `Ψ` is continuous on `A₂¹(𝔻)` into `A₂(𝔻)`. -/
theorem ac2_psi_cont_disc {ψ : ℂ → ℂ} (hψ : ψ ∈ A21fun unitDisc) :
    ∀ ε > 0, ∃ δ > 0, ∀ φ ∈ A21fun unitDisc,
      normA21 unitDisc (fun z => φ z - ψ z) < ENNReal.ofReal δ →
        normA2 unitDisc (fun z => PsiOp φ z - PsiOp ψ z) < ENNReal.ofReal ε := by
  intro ε hε
  obtain ⟨C₁, hC₁⟩ := ac2_deriv_disc
  obtain ⟨C₂, hC₂⟩ := ac2_mul_disc
  have hE : IsOpen unitDisc := isOpen_ball
  have hEm : MeasurableSet unitDisc := hE.measurableSet
  set A := (normA21 unitDisc ψ).toReal with hA
  have hA0 : 0 ≤ A := ENNReal.toReal_nonneg
  set K := max C₁ 0 + max C₂ 0 * (1 + 2 * A) + 1 with hK
  have hK0 : 0 < K := by positivity
  refine ⟨min 1 (ε / K), lt_min one_pos (div_pos hε hK0), fun φ hφ hφψ => ?_⟩
  set h : ℂ → ℂ := fun z => φ z - ψ z with hhdef
  have haes : ∀ {u : ℂ → ℂ}, DifferentiableOn ℂ u unitDisc →
      AEStronglyMeasurable u (volume.restrict unitDisc) :=
    fun hu => hu.continuousOn.aestronglyMeasurable hEm
  have hδ : ENNReal.ofReal (min 1 (ε / K)) < ⊤ := ENNReal.ofReal_lt_top
  have hhfin : normA21 unitDisc h < ⊤ := hφψ.trans hδ
  have hh : h ∈ A21fun unitDisc := ⟨hφ.1.sub hψ.1, hhfin⟩
  -- the algebraic identity on `𝔻`
  have hid : EqOn (fun z => PsiOp φ z - PsiOp ψ z)
      (fun z => deriv h z + (-(1 / 2 : ℂ)) * (h z * (φ z + ψ z))) unitDisc := by
    intro z hz
    have hφz := hφ.1.differentiableAt (hE.mem_nhds hz)
    have hψz := hψ.1.differentiableAt (hE.mem_nhds hz)
    have hd : deriv h z = deriv φ z - deriv ψ z := deriv_sub hφz hψz
    simp only [PsiOp]
    rw [hd]
    simp only [h]
    ring
  rw [normA2_congr hEm hid]
  -- bounds
  have hD := hC₁ h hh
  have hsum : (fun z => φ z + ψ z) = fun z => h z + (ψ z + ψ z) := by
    funext z
    simp only [h]
    ring
  have hplus : normA21 unitDisc (fun z => φ z + ψ z) ≤
      normA21 unitDisc h + (normA21 unitDisc ψ + normA21 unitDisc ψ) := by
    rw [hsum]
    refine (a55_normA21_add_le (haes hh.1) ((haes hψ.1).add (haes hψ.1))).trans ?_
    gcongr
    exact a55_normA21_add_le (haes hψ.1) (haes hψ.1)
  have hplusA : (fun z => φ z + ψ z) ∈ A21fun unitDisc := by
    refine ⟨hφ.1.add hψ.1, lt_of_le_of_lt hplus ?_⟩
    exact ENNReal.add_lt_top.mpr ⟨hhfin, ENNReal.add_lt_top.mpr ⟨hψ.2, hψ.2⟩⟩
  have hM := hC₂ h hh (fun z => φ z + ψ z) hplusA
  have hderm : AEStronglyMeasurable (deriv h) (volume.restrict unitDisc) :=
    haes (hh.1.deriv hE)
  have hprodm : AEStronglyMeasurable (fun z => (-(1 / 2 : ℂ)) * (h z * (φ z + ψ z)))
      (volume.restrict unitDisc) :=
    (haes (((hh.1.mul (hφ.1.add hψ.1))).const_smul (-(1 / 2 : ℂ))))
  have htri := a55_normA2_add_le hderm hprodm
  rw [normA2_const_mul] at htri
  -- pass to reals
  set t := (normA21 unitDisc h).toReal with ht
  have ht0 : 0 ≤ t := ENNReal.toReal_nonneg
  have hhe : normA21 unitDisc h = ENNReal.ofReal t := (ENNReal.ofReal_toReal hhfin.ne).symm
  have hψe : normA21 unitDisc ψ = ENNReal.ofReal A := (ENNReal.ofReal_toReal hψ.2.ne).symm
  have htδ : t < min 1 (ε / K) := by
    rw [hhe] at hφψ
    exact (ENNReal.ofReal_lt_ofReal_iff (lt_min one_pos (div_pos hε hK0))).mp hφψ
  have ht1 : t < 1 := lt_of_lt_of_le htδ (min_le_left _ _)
  have htK : t * K < ε := by
    have := lt_of_lt_of_le htδ (min_le_right _ _)
    rwa [lt_div_iff₀ hK0] at this
  have hC1 : ENNReal.ofReal C₁ ≤ ENNReal.ofReal (max C₁ 0) := ENNReal.ofReal_le_ofReal (le_max_left _ _)
  have hC2 : ENNReal.ofReal C₂ ≤ ENNReal.ofReal (max C₂ 0) := ENNReal.ofReal_le_ofReal (le_max_left _ _)
  have hhalf : (‖(-(1 / 2 : ℂ))‖₊ : ℝ≥0∞) = ENNReal.ofReal (1 / 2) := by
    rw [← enorm_eq_nnnorm, ← ofReal_norm, norm_neg]
    norm_num
  have hbound : normA2 unitDisc (deriv h) +
      (‖(-(1 / 2 : ℂ))‖₊ : ℝ≥0∞) * normA2 unitDisc (fun z => h z * (φ z + ψ z)) ≤
      ENNReal.ofReal (max C₁ 0 * t + 1 / 2 * (max C₂ 0 * t * (t + (A + A)))) := by
    rw [hhalf]
    have e1 : normA2 unitDisc (deriv h) ≤ ENNReal.ofReal (max C₁ 0 * t) := by
      rw [ENNReal.ofReal_mul (le_max_right _ _), ← hhe]
      exact hD.trans (by gcongr)
    have e2 : normA2 unitDisc (fun z => h z * (φ z + ψ z)) ≤
        ENNReal.ofReal (max C₂ 0 * t * (t + (A + A))) := by
      rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (le_max_right _ _), ← hhe,
        ENNReal.ofReal_add ht0 (by positivity), ENNReal.ofReal_add hA0 hA0, ← hhe, ← hψe]
      exact hM.trans (by gcongr)
    have hb0 : 0 ≤ max C₂ 0 * t * (t + (A + A)) :=
      mul_nonneg (mul_nonneg (le_max_right _ _) ht0) (by linarith)
    calc _ ≤ ENNReal.ofReal (max C₁ 0 * t) +
          ENNReal.ofReal (1 / 2) * ENNReal.ofReal (max C₂ 0 * t * (t + (A + A))) := by gcongr
      _ = _ := by
        rw [ENNReal.ofReal_add (mul_nonneg (le_max_right _ _) ht0) (mul_nonneg (by norm_num) hb0),
          ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  refine lt_of_le_of_lt (htri.trans hbound) ((ENNReal.ofReal_lt_ofReal_iff hε).mpr ?_)
  have hC1n : 0 ≤ max C₁ 0 := le_max_right _ _
  have hC2n : 0 ≤ max C₂ 0 := le_max_right _ _
  calc max C₁ 0 * t + 1 / 2 * (max C₂ 0 * t * (t + (A + A)))
      ≤ t * K := by
        rw [hK]
        have : t + (A + A) ≤ 1 + 2 * A := by linarith
        nlinarith [mul_le_mul_of_nonneg_left this (mul_nonneg hC2n ht0)]
    _ < ε := htK

/-! ### Step 3: the Bers image, with control of the class -/

/-- For every neighbourhood `U ∋ q₀` in `T(1)`, an `A₂(𝔻)`-ball around `𝒮(𝖿^{q₀})` consists of Schwarzians `𝒮(𝖿^q)`,
`q ∈ U`. -/
theorem ac2_bers_nbhd (q₀ : T1) {U : Set T1} (hU : IsOpen U) (hq₀ : q₀ ∈ U) :
    ∃ ε > 0, ∀ S : ℂ → ℂ, DifferentiableOn ℂ S unitDisc →
      normA2 unitDisc (fun y => S y - schwarzianHol (fsans (Quotient.out q₀ : LinfStarBall)) y) <
          ENNReal.ofReal ε →
        ∃ q ∈ U, EqOn S (schwarzianHol (fsans (Quotient.out q : LinfStarBall))) unitDisc := by
  have hcircle : ∀ z ∈ unitDisc, ‖z‖ ≠ 1 := fun z hz => (mem_ball_zero_iff.mp hz).ne
  -- `𝒮(𝖿^μ) = toFun (β[μ])` on `𝔻`
  have hspec : ∀ q : T1, ∀ y ∈ unitDisc,
      AInf.toFun (bers q) y = schwarzianHol (fsans (Quotient.out q : LinfStarBall)) y := by
    intro q y hy
    have hμ := (Quotient.out q : LinfStarBall).2
    obtain ⟨hfd, hfi⟩ := fB_holomorphic_injective hμ
    rw [S2C.s2c_fsans_eq hμ]
    exact (schwarzianHol_AInf_spec hfd hfi).1 y hy
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp (bers_isOpenEmbedding.isOpenMap U hU) (bers q₀) ⟨q₀, hq₀, rfl⟩
  have hcpos : 0 < Real.sqrt (12 / π) := Real.sqrt_pos.2 (by positivity)
  refine ⟨r / Real.sqrt (12 / π), div_pos hr hcpos, fun S hS hn => ?_⟩
  have hS₀d : DifferentiableOn ℂ (schwarzianHol (fsans (Quotient.out q₀ : LinfStarBall))) unitDisc :=
    (toAInf unitDisc _).2.congr fun z hz => (hspec q₀ z hz).symm
  have hmem : (fun y => S y - schwarzianHol (fsans (Quotient.out q₀ : LinfStarBall)) y) ∈ A2fun unitDisc :=
    ⟨hS.sub hS₀d, hn.trans ENNReal.ofReal_lt_top⟩
  set φ := toA2 unitDisc (fun y => S y - schwarzianHol (fsans (Quotient.out q₀ : LinfStarBall)) y) with hφ
  have hφn : ‖φ‖ < r / Real.sqrt (12 / π) := by
    have h1 : ENNReal.ofReal ‖φ‖ < ENNReal.ofReal (r / Real.sqrt (12 / π)) := by
      rw [ofReal_norm_eq_enorm]
      exact (hbL2_toA2_norm hmem).trans_lt hn
    exact (ENNReal.ofReal_lt_ofReal_iff (div_pos hr hcpos)).1 h1
  obtain ⟨hAn, hAf⟩ := A2toAInf_bounded.2 φ
  have hlt : ‖A2toAInf φ‖ < r := by
    calc ‖A2toAInf φ‖ ≤ Real.sqrt (12 / π) * ‖φ‖ := hAn
      _ < Real.sqrt (12 / π) * (r / Real.sqrt (12 / π)) := mul_lt_mul_of_pos_left hφn hcpos
      _ = r := by field_simp
  have hmemb : bers q₀ + A2toAInf φ ∈ ball (bers q₀) r := by
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left]
    exact hlt
  obtain ⟨q, hqU, hq⟩ := hball hmemb
  refine ⟨q, hqU, fun y hy => ?_⟩
  have e2 : AInf.toFun (bers q₀ + A2toAInf φ) y = AInf.toFun (bers q₀) y + AInf.toFun (A2toAInf φ) y := by
    simp only [AInf.toFun, Submodule.coe_add, unweight_add, Pi.add_apply]
  have hφy : A2.toFun φ y = S y - schwarzianHol (fsans (Quotient.out q₀ : LinfStarBall)) y :=
    toA2_spec isOpen_ball hcircle hmem hy
  rw [← hq, hspec q y hy, hspec q₀ y hy, hAf y hy, hφy] at e2
  rw [e2]
  ring

/-! ### Step 4: the pole parameter (下属3 / 下属5) -/

/-- Along `μₙ → μ₀` in the ball, `fB μₙ → fB μ₀` locally uniformly on `𝔻` (`acc_fB_tendsto`). -/
theorem ac2_fpp_luc {μ₀ : LinfStar} (hμ₀ : μ₀ ∈ LinfStarBall) {μs : ℕ → LinfStar}
    (hμs : ∀ n, μs n ∈ LinfStarBall) (hlim : Tendsto μs atTop (𝓝 μ₀)) :
    TendstoLocallyUniformlyOn (fun n => fB (μs n)) (fB μ₀) atTop unitDisc := by
  refine (tendstoLocallyUniformlyOn_iff_forall_isCompact (s := unitDisc) isOpen_ball).2 fun K hK hKc => ?_
  exact acc_fB_tendsto hμ₀ hμs (tendsto_iff_norm_sub_tendsto_zero.mp hlim) hKc
    (fun z hz => by rw [wB_disc_eq_fB hμ₀ (hK hz)]; exact OnePoint.coe_ne_infty _)

/-- Along `μₙ → μ₀` in the ball, `fB μₙ''(0) → fB μ₀''(0)` (Weierstrass, twice). -/
theorem ac2_fpp_seq {μ₀ : LinfStar} (hμ₀ : μ₀ ∈ LinfStarBall) {μs : ℕ → LinfStar}
    (hμs : ∀ n, μs n ∈ LinfStarBall) (hlim : Tendsto μs atTop (𝓝 μ₀)) :
    Tendsto (fun n => deriv (deriv (fB (μs n))) 0) atTop (𝓝 (deriv (deriv (fB μ₀)) 0)) := by
  have h0 : (0 : ℂ) ∈ unitDisc := by simp [unitDisc]
  have hL := ac2_fpp_luc hμ₀ hμs hlim
  have hD := hL.deriv (Filter.Eventually.of_forall fun n => (fB_holomorphic_injective (hμs n)).1) isOpen_ball
  have hD2 := hD.deriv (Filter.Eventually.of_forall fun n =>
    ((fB_holomorphic_injective (hμs n)).1).deriv isOpen_ball) isOpen_ball
  exact hD2.tendsto_at h0

/-- `q ↦ 𝖿^q''(0) = 𝒜(𝖿^q)(0)` is continuous on `T(1)`. -/
theorem ac2_fpp_cont :
    Continuous fun q : T1 => preSchwarzian (fsans (Quotient.out q : LinfStarBall)) 0 := by
  have h0 : (0 : ℂ) ∈ unitDisc := by simp [unitDisc]
  set g : LinfStarBall → ℂ := fun μ => deriv (deriv (fB (μ : LinfStar))) 0 with hg
  have hval : ∀ μ : LinfStarBall, preSchwarzian (fsans (μ : LinfStar)) 0 = g μ := by
    intro μ
    rw [S2C.s2c_fsans_eq μ.2]
    show deriv (deriv (fB (μ : LinfStar))) 0 / deriv (fB (μ : LinfStar)) 0 = g μ
    rw [(fB_normalization _).2.1, div_one]
  have hcls : ∀ μ ν : LinfStarBall, teichSetoid μ ν → g μ = g ν := by
    intro μ ν h
    have he : fB (μ : LinfStar) =ᶠ[𝓝 0] fB (ν : LinfStar) := by
      filter_upwards [isOpen_ball.mem_nhds h0] with z hz
      have hz' := (s2c_class_pair h).1 hz
      rwa [S2C.s2c_fsans_eq μ.2, S2C.s2c_fsans_eq ν.2] at hz'
    exact he.deriv.deriv_eq
  have hgc : Continuous g := by
    rw [continuous_iff_seqContinuous]
    intro x μ₀ hx
    exact ac2_fpp_seq μ₀.2 (fun n => (x n).2) ((continuous_subtype_val.tendsto _).comp hx)
  have heq : (fun q : T1 => preSchwarzian (fsans (Quotient.out q : LinfStarBall)) 0) =
      Quotient.lift (s := teichSetoid) g hcls := by
    funext q
    refine Quotient.inductionOn (s := teichSetoid) q fun μ => ?_
    rw [hval, Quotient.lift_mk]
    exact hcls _ _ (Quotient.mk_out (s := teichSetoid) μ)
  rw [heq]
  exact hgc.quotient_lift hcls

/-- A local continuous section of `Φ` through `out p`, in Bers coordinates (`bsub_G_local_inverse`). -/
theorem ac2g_section (p : T1) :
    ∃ s : AInf unitDisc → LinfStar, ContinuousAt s (bers p) ∧ s (bers p) = ((Quotient.out p : LinfStarBall) : LinfStar) ∧
      ∀ᶠ χ in 𝓝 (bers p), ∃ h : s χ ∈ LinfStarBall, bers (Phi ⟨s χ, h⟩) = χ := by
  have hν : ((Quotient.out p : LinfStarBall) : LinfStar) ∈ LinfStarBall := (Quotient.out p : LinfStarBall).2
  have hbp : bers p = bersPhi ((Quotient.out p : LinfStarBall) : LinfStar) := rfl
  obtain ⟨L, hLd, hL0, hev⟩ := bsub_G_local_inverse hν
  rw [hbp]
  refine ⟨fun χ => beltramiMul (Lambda (L χ)) ((Quotient.out p : LinfStarBall) : LinfStar), ?_, ?_, ?_⟩
  · have hΛ : Continuous Lambda := by
      have h : Lambda = fun φ => (LambdaEquiv φ : LinfStar) := funext fun φ => (LambdaEquiv_apply φ).symm
      rw [h]
      exact continuous_subtype_val.comp LambdaEquiv.continuous
    have hM : ContinuousAt (fun l => beltramiMul l ((Quotient.out p : LinfStarBall) : LinfStar))
        (Lambda (L (bersPhi ((Quotient.out p : LinfStarBall) : LinfStar)))) := by
      rw [hL0, glr_lambda_zero]
      exact ((bd_differentiableOn hν).differentiableAt
        (isOpen_ball.mem_nhds (mem_ball_self one_pos))).continuousAt
    exact hM.comp (f := fun χ => Lambda (L χ)) (hΛ.continuousAt.comp hLd.continuousAt)
  · show beltramiMul (Lambda (L (bersPhi ((Quotient.out p : LinfStarBall) : LinfStar)))) ((Quotient.out p : LinfStarBall) : LinfStar) = _
    rw [hL0, glr_lambda_zero, hb_zero_mul hν]
  · filter_upwards [hev] with χ hχ
    have hΛ : Lambda (L χ) ∈ LinfStarBall := Lambda_mem_ball (mem_ball_zero_iff.mp hχ.1)
    refine ⟨bg_mul_mem_ball hν hΛ, ?_⟩
    rw [bers_Phi]
    exact hχ.2

/-- The exterior image `𝗀_q(𝔻*)` only depends on the class: it can be computed from any representative. -/
theorem ac2g_image_rep {q : T1} {μ : LinfStarBall} (h : bers (Phi μ) = bers q) :
    gsans (Quotient.out q : LinfStarBall) '' unitDiscExterior = gsans (μ : LinfStar) '' unitDiscExterior := by
  have hq : Phi μ = q := bers_isOpenEmbedding.injective h
  have hr : teichSetoid (Quotient.out q) μ := by
    have h1 : Phi (Quotient.out q : LinfStarBall) = q := Quotient.out_eq (s := teichSetoid) q
    exact Quotient.exact (h1.trans hq.symm)
  exact (s2c_class_pair hr).2.image_eq

/-- Joint continuity of `(μ, x) ↦ w_μ((w^μ)⁻¹(x))`, the inverse of the sphere welding map `w^μ ∘ w_μ⁻¹`
(`acc_wAS_cont`, `acc_inv_cont`, `acc_wB_cont`). -/
theorem ac2g_inv_cont :
    ContinuousOn (fun x : LinfStar × ExtPlane => wAS x.1 (Function.invFun (wB x.1) x.2)) (LinfStarBall ×ˢ univ) :=
  acc_wAS_cont.comp (f := fun x : LinfStar × ExtPlane => (x.1, Function.invFun (wB x.1) x.2))
    (continuousOn_fst.prodMk (acc_inv_cont acc_wB_cont (fun μ _ => wB_bijective μ)))
    (fun _ hx => ⟨hx.1, mem_univ _⟩)

/-- `w_μ ∘ (w^μ)⁻¹` is a right inverse of the sphere welding map. -/
theorem ac2g_right_inv (μ : LinfStar) (x : ExtPlane) :
    normalizedWeldingSphere μ (wAS μ (Function.invFun (wB μ) x)) = x := by
  show wB μ (Function.invFun (wAS μ) (wAS μ (Function.invFun (wB μ) x))) = x
  rw [Function.leftInverse_invFun (wAS_bijective μ).1, Function.rightInverse_invFun (wB_bijective μ).2]

/-- On `𝔻*`, `𝗀_μ` is the finite part of the sphere welding map. -/
theorem ac2g_gsans_coe {μ : LinfStar} (hμ : μ ∈ LinfStarBall) {z : ℂ} (hz : z ∈ unitDiscExterior) :
    (gsans μ z : ExtPlane) = normalizedWeldingSphere μ z := by
  rw [S2C.s2c_gsans_eq hμ, gMu_eq_normalizedWeldingExterior hμ hz, normalizedWeldingExterior_coe hμ]

/-- Uniformly for `μ` near `ν₀` in `L∞`, `𝗀_μ(𝔻*)` contains a fixed ball around `𝗀_{ν₀}(w)`: the inverse welding
maps converge (`ac2g_inv_cont`), and `w ∈ 𝔻*` is an interior point. -/
theorem ac2g_local {ν0 : LinfStar} (hν0 : ν0 ∈ LinfStarBall) {w : ℂ} (hw : w ∈ unitDiscExterior) :
    ∃ r > 0, ∀ μ ∈ ball ν0 r, μ ∈ LinfStarBall → ball (gsans ν0 w) r ⊆ gsans μ '' unitDiscExterior := by
  have hEo : IsOpen unitDiscExterior := isOpen_lt continuous_const continuous_norm
  have hH0 : wAS ν0 (Function.invFun (wB ν0) (gsans ν0 w : ExtPlane)) = (w : ExtPlane) := by
    apply (normalizedWeldingSphere_bijective ν0).1
    rw [ac2g_right_inv, ac2g_gsans_coe hν0 hw]
  have hK0 : ContinuousAt (fun x : LinfStar × ExtPlane => wAS x.1 (Function.invFun (wB x.1) x.2))
      (ν0, (gsans ν0 w : ExtPlane)) :=
    ac2g_inv_cont.continuousAt ((isOpen_ball.prod isOpen_univ).mem_nhds ⟨hν0, mem_univ _⟩)
  have hf : ContinuousAt (fun x : LinfStar × ℂ => (x.1, (x.2 : ExtPlane))) (ν0, gsans ν0 w) :=
    (continuous_fst.prodMk (OnePoint.continuous_coe.comp continuous_snd)).continuousAt
  have hK := ContinuousAt.comp (x := (ν0, gsans ν0 w)) hK0 hf
  have hO : IsOpen (((↑) : ℂ → ExtPlane) '' unitDiscExterior) := OnePoint.isOpenEmbedding_coe.isOpenMap _ hEo
  have hwO : wAS ν0 (Function.invFun (wB ν0) (gsans ν0 w : ExtPlane)) ∈
      ((↑) : ℂ → ExtPlane) '' unitDiscExterior := by
    rw [hH0]
    exact ⟨w, hw, rfl⟩
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.1 (hK (hO.mem_nhds hwO))
  refine ⟨r, hr, fun μ hμ hμb x hx => ?_⟩
  have hpt : dist (μ, x) (ν0, gsans ν0 w) < r := by
    rw [Prod.dist_eq]
    exact max_lt (mem_ball.1 hμ) (mem_ball.1 hx)
  have hm := hball (mem_ball.2 hpt)
  simp only [mem_preimage, Function.comp_apply] at hm
  obtain ⟨y, hy, hyH⟩ := hm
  refine ⟨y, hy, OnePoint.coe_injective ?_⟩
  show (gsans μ y : ExtPlane) = x
  rw [ac2g_gsans_coe hμb hy, hyH, ac2g_right_inv]

/-- For `q` near `p` the exterior image `𝗀_q(𝔻*)` contains a fixed ball around `𝗀_p(w)`. -/
theorem ac2g_g_open (p : T1) {w : ℂ} (hw : w ∈ unitDiscExterior) :
    ∃ U : Set T1, IsOpen U ∧ p ∈ U ∧ ∃ δ > 0, ∀ q ∈ U,
      ball (gsans (Quotient.out p : LinfStarBall) w) δ ⊆ gsans (Quotient.out q : LinfStarBall) '' unitDiscExterior := by
  obtain ⟨r, hr, hloc⟩ := ac2g_local (Quotient.out p : LinfStarBall).2 hw
  obtain ⟨s, hsc, hs0, hsev⟩ := ac2g_section p
  have hV : s ⁻¹' ball ((Quotient.out p : LinfStarBall) : LinfStar) r ∩
      {χ | ∃ h : s χ ∈ LinfStarBall, bers (Phi ⟨s χ, h⟩) = χ} ∈ 𝓝 (bers p) := by
    refine inter_mem (hsc ?_) hsev
    rw [hs0]
    exact ball_mem_nhds _ hr
  refine ⟨bers ⁻¹' interior _, isOpen_interior.preimage bers_isOpenEmbedding.continuous,
    mem_interior_iff_mem_nhds.2 hV, r, hr, fun q hq => ?_⟩
  obtain ⟨hsb, hs, hbq⟩ := interior_subset hq
  rw [ac2g_image_rep hbq]
  exact hloc _ hsb hs

/-- For `q` near `p` the exterior image `𝗀_q(𝔻*)` contains a fixed ball around `𝗀_p(w)`. -/
theorem ac2_g_open (p : T1) {w : ℂ} (hw : w ∈ unitDiscExterior) :
    ∃ U : Set T1, IsOpen U ∧ p ∈ U ∧ ∃ δ > 0, ∀ q ∈ U,
      ball (gsans (Quotient.out p : LinfStarBall) w) δ ⊆ gsans (Quotient.out q : LinfStarBall) '' unitDiscExterior := by
  exact ac2g_g_open p hw

/-! ### Step 5 and assembly -/

/-- `β̂(q, w)(0) = 𝖿^q''(0) + 2/𝗀_q(w)`, i.e. `𝒜(λ_c ∘ f)(0) = f''(0) - 2c`. -/
theorem ac2_betaHat_zero (q : T1) {w : ℂ} (hw : w ∈ unitDiscExterior) :
    betaHat q w 0 = preSchwarzian (fsans (Quotient.out q : LinfStarBall)) 0 +
      2 / gsans (Quotient.out q : LinfStarBall) w := by
  have hμ := (Quotient.out q : LinfStarBall).2
  have h := appa_betaHat_eq (μ := Quotient.out q) hw (mem_ball_self one_pos)
  obtain ⟨hf0, hf1, -⟩ := fB_normalization (Quotient.out q : LinfStarBall)
  dsimp only at h
  rw [hf0, hf1, mul_zero, zero_add, div_one, mul_one] at h
  show preSchwarzian (weldF ((Quotient.out q : LinfStarBall) : LinfStar) w) 0 = _
  rw [h, S2C.s2c_fsans_eq hμ, S2C.s2c_gsans_eq hμ]
  ring

/-- `Ψ(β̂(q, w)) = 𝒮(𝖿^q)` on `𝔻` (`𝒮` is Möbius invariant; the pole `𝗀_q(w)` is off `𝖿^q(𝔻)`). -/
theorem ac2_psi_betaHat (q : T1) {w : ℂ} (hw : w ∈ unitDiscExterior) :
    EqOn (PsiOp (betaHat q w)) (schwarzianHol (fsans (Quotient.out q : LinfStarBall))) unitDisc := by
  intro z hz
  set μ := (Quotient.out q : LinfStarBall) with hμdef
  have hμ := μ.2
  have hpair := AppB.b8_welding_normalized_pair hμ
  rw [S2C.s2c_fsans_eq hμ]
  -- the pole `𝗀_μ(w)` is off `𝖿^μ(𝔻)`
  have hpole : ∀ y ∈ unitDisc, (-1 / gMu (μ : LinfStar) w) * fB μ y + 1 ≠ 0 := by
    intro y hy he
    have hg : gsans (μ : LinfStar) w ≠ fsans (μ : LinfStar) y :=
      fun h => hpair.2.2.2.2.2.ne_of_mem ⟨y, hy, rfl⟩ ⟨w, hw, rfl⟩ h.symm
    rw [S2C.s2c_fsans_eq hμ, S2C.s2c_gsans_eq hμ] at hg
    by_cases h0 : gMu (μ : LinfStar) w = 0
    · rw [h0, div_zero, zero_mul, zero_add] at he
      exact one_ne_zero he
    · apply hg
      have he' : fB (μ : LinfStar) y = gMu (μ : LinfStar) w := by
        field_simp at he
        first | linear_combination he | linear_combination -he
      exact he'.symm
  obtain ⟨hFd, -, -⟩ := weldF_regular_of_avoids_pole hμ w hpole
  obtain ⟨hfd, hfi⟩ := fB_holomorphic_injective hμ
  have hfa : AnalyticAt ℂ (fB μ) z := hfd.analyticAt (isOpen_ball.mem_nhds hz)
  have hFa : AnalyticAt ℂ (weldF (μ : LinfStar) w) z := hFd.analyticAt (isOpen_ball.mem_nhds hz)
  have hf' : deriv (fB μ) z ≠ 0 := deriv_ne_zero_of_injOn isOpen_ball hfd hfi hz
  have hev : weldF (μ : LinfStar) w =ᶠ[𝓝[≠] z]
      fun y => (1 * fB μ y + 0) / ((-1 / gMu (μ : LinfStar) w) * fB μ y + 1) :=
    Filter.Eventually.of_forall fun y => by simp [weldF, lambdaW]
  show schwarzianHol (weldF (μ : LinfStar) w) z = schwarzianHol (fB μ) z
  rw [← schwarzian_of_analyticAt hFa, schwarzian_congr hev,
    schwarzian_mobius_comp_of_ne hfa hf' (by norm_num) (hpole z hz), schwarzian_of_analyticAt hfa]

/-- `Ψ` only sees a neighbourhood. -/
theorem ac2_psi_congr {ψ₁ ψ₂ : ℂ → ℂ} (h : EqOn ψ₁ ψ₂ unitDisc) : EqOn (PsiOp ψ₁) (PsiOp ψ₂) unitDisc := by
  intro z hz
  have hev : ψ₁ =ᶠ[𝓝 z] ψ₂ := Filter.eventually_of_mem (isOpen_ball.mem_nhds hz) h
  unfold PsiOp
  rw [hev.deriv_eq, h hz]

/-- `𝗀_μ` omits `0 = 𝖿^μ(0)`. -/
theorem ac2_g_ne_zero {μ : LinfStar} (hμ : μ ∈ LinfStarBall) {w : ℂ} (hw : w ∈ unitDiscExterior) :
    gsans μ w ≠ 0 := by
  intro h0
  have hpair := AppB.b8_welding_normalized_pair hμ
  have hf0 : fsans μ 0 = 0 := by rw [S2C.s2c_fsans_eq hμ]; exact (fB_normalization μ).1
  exact hpair.2.2.2.2.2.ne_of_mem ⟨0, mem_ball_self one_pos, rfl⟩ ⟨w, hw, rfl⟩ (by rw [hf0, h0])

/-- The second conjunct of `cor_A_2`. -/
theorem ac2_core : ∀ ψ ∈ betaHatT0, ∃ ε > 0, ∀ φ ∈ A21fun unitDisc,
    normA21 unitDisc (fun z => φ z - ψ z) < ENNReal.ofReal ε → φ ∈ betaHatT0 := by
  intro ψ hψT
  have hψA := ac2_sub hψT
  obtain ⟨p, hp, w, hw, heq⟩ := hψT
  have hμp := (Quotient.out p : LinfStarBall).2
  set a : T1 → ℂ := fun q => preSchwarzian (fsans (Quotient.out q : LinfStarBall)) 0 with ha
  set z₀ := gsans (Quotient.out p : LinfStarBall) w with hz₀
  have hz₀0 : z₀ ≠ 0 := ac2_g_ne_zero hμp hw
  set c₀ : ℂ := -1 / z₀ with hc₀
  have hc₀0 : c₀ ≠ 0 := by rw [hc₀]; exact div_ne_zero (neg_ne_zero.2 one_ne_zero) hz₀0
  have hψ0 : ψ 0 = a p + 2 / z₀ := (heq (mem_ball_self one_pos)).trans (ac2_betaHat_zero p hw)
  -- the pole parameter: `c ↦ -1/c` near `c₀`, and `𝗀_q(𝔻*) ⊇ ball(z₀, δ)` near `p`
  obtain ⟨U₁, hU₁, hpU₁, δ, hδ, hball⟩ := ac2_g_open p hw
  have hinv : ContinuousAt (fun c : ℂ => -1 / c) c₀ := (continuousAt_const.div continuousAt_id hc₀0)
  obtain ⟨η, hη, hηδ⟩ := Metric.continuousAt_iff.1 hinv δ hδ
  have hz₀' : -1 / c₀ = z₀ := by rw [hc₀]; field_simp
  set U₂ : Set T1 := a ⁻¹' ball (a p) η with hU₂
  have hU₂o : IsOpen U₂ := isOpen_ball.preimage ac2_fpp_cont
  obtain ⟨ε₁, hε₁, hnb⟩ := ac2_bers_nbhd p (hU₁.inter hU₂o) ⟨hpU₁, mem_ball_self hη⟩
  obtain ⟨δ₁, hδ₁, hcont⟩ := ac2_psi_cont_disc hψA ε₁ hε₁
  have hsq : 0 < Real.sqrt π := Real.sqrt_pos.2 Real.pi_pos
  refine ⟨min δ₁ (η * Real.sqrt π), lt_min hδ₁ (mul_pos hη hsq), fun φ hφ hn => ?_⟩
  -- `Ψφ` is `A₂`-close to `𝒮(𝖿^p)`
  have hA2 := hcont φ hφ (hn.trans_le (ENNReal.ofReal_le_ofReal (min_le_left _ _)))
  have hPψ : EqOn (PsiOp ψ) (schwarzianHol (fsans (Quotient.out p : LinfStarBall))) unitDisc :=
    fun z hz => (ac2_psi_congr heq hz).trans (ac2_psi_betaHat p hw hz)
  have hA2' : normA2 unitDisc (fun y => PsiOp φ y - schwarzianHol (fsans (Quotient.out p : LinfStarBall)) y) <
      ENNReal.ofReal ε₁ := by
    refine (normA2_congr (D := unitDisc) measurableSet_ball
      (φ := fun y => PsiOp φ y - schwarzianHol (fsans (Quotient.out p : LinfStarBall)) y)
      (ψ := fun y => PsiOp φ y - PsiOp ψ y) (fun y hy => ?_)).trans_lt hA2
    show PsiOp φ y - schwarzianHol (fsans (Quotient.out p : LinfStarBall)) y = PsiOp φ y - PsiOp ψ y
    rw [hPψ hy]
  have hφP := lemma_1_5_disc hφ
  obtain ⟨q, ⟨hqU₁, hqU₂⟩, hq⟩ := hnb (PsiOp φ) hφP.1 hA2'
  have hqT : q ∈ T01 := by
    refine ((thm_1_12 q).1).2 ⟨hφP.1.congr fun y hy => (hq hy).symm, ?_⟩
    exact (normA2_congr measurableSet_ball (fun y hy => (hq hy).symm)).trans_lt hφP.2
  -- the value at `0`
  have hd : φ - ψ ∈ A21fun unitDisc := by
    have h := a21_add measurableSet_ball hφ (a21_const_mul measurableSet_ball hψA (-1))
    refine (ab112_A21fun_congr (U := unitDisc) isOpen_ball fun z _ => ?_).1 h
    show φ z + -1 * ψ z = φ z - ψ z
    ring
  have h0 : ‖φ 0 - ψ 0‖ < η := by
    have hb := a21_origin_bound hd
    have hn' : normA21 unitDisc (φ - ψ) < ENNReal.ofReal (η * Real.sqrt π) :=
      hn.trans_le (ENNReal.ofReal_le_ofReal (min_le_right _ _))
    have h1 : ENNReal.ofReal ‖(φ - ψ) 0‖ < ENNReal.ofReal η := by
      refine hb.trans_lt ?_
      calc ENNReal.ofReal (1 / Real.sqrt π) * normA21 unitDisc (φ - ψ)
          < ENNReal.ofReal (1 / Real.sqrt π) * ENNReal.ofReal (η * Real.sqrt π) :=
            ENNReal.mul_lt_mul_right (ENNReal.ofReal_pos.2 (by positivity)).ne' ENNReal.ofReal_ne_top hn'
        _ = ENNReal.ofReal η := by
            rw [← ENNReal.ofReal_mul (by positivity)]
            congr 1
            field_simp
    exact (ENNReal.ofReal_lt_ofReal_iff hη).1 h1
  set c : ℂ := (a q - φ 0) / 2 with hc
  have hcc : dist c c₀ < η := by
    have hc₀' : c₀ = (a p - ψ 0) / 2 := by rw [hψ0, hc₀]; field_simp; ring
    have haq : ‖a q - a p‖ < η := by simpa [hU₂, dist_eq_norm] using hqU₂
    rw [dist_eq_norm, hc, hc₀']
    calc ‖(a q - φ 0) / 2 - (a p - ψ 0) / 2‖ = ‖(a q - a p) - (φ 0 - ψ 0)‖ / 2 := by
          rw [← sub_div, norm_div, show ‖(2 : ℂ)‖ = 2 by simp]
          congr 2
          ring
      _ ≤ (‖a q - a p‖ + ‖φ 0 - ψ 0‖) / 2 := by gcongr; exact norm_sub_le _ _
      _ < η := by linarith
  have hzball : -1 / c ∈ ball z₀ δ := by
    have := hηδ hcc
    rwa [hz₀'] at this
  obtain ⟨w', hw', hgw'⟩ := hball q hqU₁ hzball
  have hc0 : c ≠ 0 := by
    intro h
    rw [h, div_zero] at hgw'
    exact ac2_g_ne_zero (Quotient.out q : LinfStarBall).2 hw' hgw'
  -- `φ = β̂(q, w')`
  refine ⟨q, hqT, w', hw', ?_⟩
  have hbA := ((betaHat_spec q hw').1).2 hqT
  refine PsiOp_injective_with_value hφ.1 hbA.1 (fun z hz => ((hq hz).trans (ac2_psi_betaHat q hw' hz).symm)) ?_
  rw [ac2_betaHat_zero q hw', hgw']
  rw [hc]
  field_simp
  ring

/-- **Corollary A.2** (TT:5800). `β̂(𝒯₀(1))` is open in `A₂¹(𝔻)`. -/
theorem ac2_cor_A_2 :
    betaHatT0 ⊆ A21fun unitDisc ∧ ∀ ψ ∈ betaHatT0, ∃ ε > 0, ∀ φ ∈ A21fun unitDisc,
      normA21 unitDisc (fun z => φ z - ψ z) < ENNReal.ofReal ε → φ ∈ betaHatT0 :=
  ⟨ac2_sub, ac2_core⟩

/-- **Corollary A.2** (TT:5800). `β̂(𝒯₀(1))` is open in `A₂¹(𝔻)`. -/
theorem cor_A_2 :
    betaHatT0 ⊆ A21fun unitDisc ∧ ∀ ψ ∈ betaHatT0, ∃ ε > 0, ∀ φ ∈ A21fun unitDisc,
      normA21 unitDisc (fun z => φ z - ψ z) < ENNReal.ofReal ε → φ ∈ betaHatT0 :=
  ac2_cor_A_2

end AppA
end TakhtajanTeo
