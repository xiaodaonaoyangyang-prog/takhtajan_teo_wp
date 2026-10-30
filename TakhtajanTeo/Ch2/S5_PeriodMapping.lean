import TakhtajanTeo.Ch2.S4_WPPotential

/-!
# Chapter 2, §5 — The period mapping (TT:5410–5750)

* §5.1 the space `𝓗_ℂ`, the form `Θ`, `W_±`, the Siegel disk `𝔇_∞`, (5.1), the Nag–Sullivan action `Π̂`, the matrices
  `𝔄`, `𝔅`, the KYNS period mapping `Π`, Proposition 5.1, Corollary 5.2, the restricted disk `𝔇_∞⁰`, Corollary 5.4,
  Remark 5.5
* §5.2 the embedding `ℰ` into the Segal–Wilson Grassmannian, Remark 5.7, Remark 5.8

**Modelling.**
- `𝓗_ℂ = H^{1/2}(S¹, ℂ)/ℂ` is modelled by functions on `S¹`, read through their Fourier coefficients
  `c_n(f) = (1/2π) ∫₀^{2π} f(e^{iθ}) e^{-inθ} dθ`. The constant term is ignored.
- Operators `W_- → W_+` and `ℓ² → ℓ²` are matrices in the bases `e_n = e^{inθ}/√n` and `f_n = e^{-inθ}/√n`. Indices
  `n ≥ 1` are written `n + 1`, `n : ℕ`, as in §2.
  - Inverses are avoided: `Π([μ]) = 𝔅𝔄̄⁻¹` is the matrix `Z` with `Z𝔄̄ = 𝔅`.
  - Proposition 5.1 is stated through the two-sided inverse relations.
- `Möb(S¹)`, on `S¹`: the restriction of a Möbius map preserving `𝔻`.
- The welding of `[μ] ∈ T(1)` is `w_μ = 𝗀_μ⁻¹ ∘ 𝖿^μ`, with `(𝖿^μ, 𝗀_μ) = (fsans μ, gsans μ)`.
- §5.2: `W_μ` is the graph of `B₁` over `V₊ = W₋` (`pr₊w = I`, `pr₋w = B₁`). The statement records:
  - the expansion of its spanning vectors `w_n = Q_n(𝖿^μ)/√n` (TT:5666);
  - the Hilbert–Schmidt property.

  The Segal–Wilson Grassmannian is not formalized as a manifold. The holomorphy of `ℰ` is Theorem 2.10.

**Not stated.**
- Remark 5.3: the holomorphy of `𝒫̂` is Theorem B.1.
- The transitivity of `Sp(𝓗)` on `𝔇_∞` and `Sp(𝓗)/U ≃ 𝔇_∞`: the standard theory of [Sie64, Seg81]; only the
  matrix form of `Π` is used.
- Remark 5.6: distributional solutions of the Beltrami equation [STZ99].
-/

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal ComplexConjugate Classical Real

noncomputable section

namespace TakhtajanTeo

open LiZhongQC

namespace Ch2

/-! ## §5.1 KYNS period mapping -/

/-- The Fourier coefficients `c_n(f) = (1/2π) ∫₀^{2π} f(e^{iθ}) e^{-inθ} dθ` of `f` on `S¹`. -/
def circleCoeff (f : ℂ → ℂ) (n : ℤ) : ℂ := fourierCoeff (fun θ => f (exp (θ * I))) n

/-- `𝓗_ℂ = H^{1/2}(S¹, ℂ)/ℂ` (TT:5432): integrable on `S¹` with `Σ'_n |n| |c_n|² < ∞`. -/
def HC : Set (ℂ → ℂ) :=
  {f | IntervalIntegrable (fun θ : ℝ => f (exp (θ * I))) volume 0 (2 * π) ∧
    Summable fun n : ℤ => |(n : ℝ)| * ‖circleCoeff f n‖ ^ 2}

/-- The real subspace `𝓗 = H^{1/2}(S¹, ℝ)/ℝ` (TT:5424). -/
def HR : Set (ℂ → ℂ) := {f ∈ HC | ∀ z ∈ unitCircle, (f z).im = 0}

/-- `W₊` (TT:5440): `c_n = 0` for `n ≤ 0`. -/
def Wplus : Set (ℂ → ℂ) := {f ∈ HC | ∀ n : ℤ, n ≤ 0 → circleCoeff f n = 0}
/-- `W₋` (TT:5444): `c_n = 0` for `n ≥ 0`. -/
def Wminus : Set (ℂ → ℂ) := {f ∈ HC | ∀ n : ℤ, 0 ≤ n → circleCoeff f n = 0}

/-- The symplectic form `Θ(f, g) = (1/2π) ∮_{S¹} g df = i Σ_n n c_n(f) c_{-n}(g)` (TT:5428), extended complex
bilinearly to `𝓗_ℂ`. -/
def thetaSymp (f g : ℂ → ℂ) : ℂ := I * ∑' n : ℤ, (n : ℂ) * circleCoeff f n * circleCoeff g (-n)

/-- (TT:5428–5446) Reindexing the Fourier series by `n ↦ -n` makes `Θ`
antisymmetric. This also holds for the totalized series outside `HC`. -/
theorem thetaSymp_antisymm (f g : ℂ → ℂ) : thetaSymp f g = -thetaSymp g f := by
  unfold thetaSymp
  calc
    I * ∑' n : ℤ, (n : ℂ) * circleCoeff f n * circleCoeff g (-n) =
        I * ∑' n : ℤ, ((-n : ℤ) : ℂ) * circleCoeff f (-n) * circleCoeff g (-(-n)) := by
      congr 1
      exact ((Equiv.neg ℤ).tsum_eq _).symm
    _ = I * ∑' n : ℤ, -((n : ℂ) * circleCoeff g n * circleCoeff f (-n)) := by
      congr 1
      apply tsum_congr
      intro n
      simp only [Int.cast_neg, neg_neg]
      ring
    _ = -(I * ∑' n : ℤ, (n : ℂ) * circleCoeff g n * circleCoeff f (-n)) := by
      rw [tsum_neg, mul_neg]

/-- (TT:5440–5446) The positive-frequency subspace is isotropic for `Θ`. -/
theorem thetaSymp_Wplus {f g : ℂ → ℂ} (hf : f ∈ Wplus) (hg : g ∈ Wplus) :
    thetaSymp f g = 0 := by
  unfold thetaSymp
  have hzero : ∀ n : ℤ, (n : ℂ) * circleCoeff f n * circleCoeff g (-n) = 0 := by
    intro n
    by_cases hn : n ≤ 0
    · rw [hf.2 n hn, mul_zero, zero_mul]
    · rw [hg.2 (-n) (by omega), mul_zero]
  simp only [hzero, tsum_zero, mul_zero]

/-- (TT:5440–5446) The negative-frequency subspace is isotropic for `Θ`. -/
theorem thetaSymp_Wminus {f g : ℂ → ℂ} (hf : f ∈ Wminus) (hg : g ∈ Wminus) :
    thetaSymp f g = 0 := by
  unfold thetaSymp
  have hzero : ∀ n : ℤ, (n : ℂ) * circleCoeff f n * circleCoeff g (-n) = 0 := by
    intro n
    by_cases hn : 0 ≤ n
    · rw [hf.2 n hn, mul_zero, zero_mul]
    · rw [hg.2 (-n) (by omega), mul_zero]
  simp only [hzero, tsum_zero, mul_zero]

/-- (TT:5428–5446) Conjugate-symmetric Fourier coefficients make `Θ` real. -/
theorem thetaSymp_real_of_coeff {f g : ℂ → ℂ}
    (hf : ∀ n : ℤ, circleCoeff f (-n) = conj (circleCoeff f n))
    (hg : ∀ n : ℤ, circleCoeff g (-n) = conj (circleCoeff g n)) :
    (thetaSymp f g).im = 0 := by
  have hconj : conj (thetaSymp f g) = -thetaSymp g f := by
    unfold thetaSymp
    simp only [map_mul, conj_I, conj_tsum, map_intCast, ← hf, ← hg, neg_neg]
    have hs : (∑' n : ℤ, (n : ℂ) * circleCoeff f (-n) * circleCoeff g n) =
        ∑' n : ℤ, (n : ℂ) * circleCoeff g n * circleCoeff f (-n) := by
      apply tsum_congr
      intro n
      ring
    rw [hs, neg_mul]
  exact Complex.conj_eq_iff_im.mp (hconj.trans (thetaSymp_antisymm f g).symm)

/-- (TT:5424–5446) A real function on the circle has conjugate-symmetric
circle Fourier coefficients. -/
theorem circleCoeff_neg_of_real {f : ℂ → ℂ}
    (hf : ∀ z ∈ unitCircle, (f z).im = 0) (n : ℤ) :
    circleCoeff f (-n) = conj (circleCoeff f n) := by
  let u : ℝ → ℝ := fun θ => (f (exp (θ * I))).re
  have he : (fun θ : ℝ => (u θ : ℂ)) = (fun θ : ℝ => f (exp (θ * I))) := by
    funext θ
    have hc : exp ((θ : ℂ) * I) ∈ unitCircle := by
      change ‖exp ((θ : ℂ) * I)‖ = 1
      simp [Complex.norm_exp]
    apply Complex.ext
    · rfl
    · simpa only [Complex.ofReal_im] using (hf _ hc).symm
  change fourierCoeff (fun θ : ℝ => f (exp (θ * I))) (-n) =
    conj (fourierCoeff (fun θ : ℝ => f (exp (θ * I))) n)
  rw [← he]
  exact fourierCoeff_neg_real u n

/-- (TT:5428–5446) The form `Θ` is real on the real subspace `HR`. -/
theorem thetaSymp_real {f g : ℂ → ℂ} (hf : f ∈ HR) (hg : g ∈ HR) :
    (thetaSymp f g).im = 0 :=
  thetaSymp_real_of_coeff (circleCoeff_neg_of_real hf.2) (circleCoeff_neg_of_real hg.2)

/-- (TT:5440–5446) Fourier orthogonality of the integer monomials on the circle. -/
theorem circleCoeff_zpow (k n : ℤ) :
    circleCoeff (fun z : ℂ => z ^ k) n = if n = k then 1 else 0 := by
  unfold circleCoeff fourierCoeff
  have he : (fun θ : ℝ => exp (θ * I) ^ k * exp (-(n * θ * I))) =
      fun θ : ℝ => exp ((((k - n : ℤ) : ℂ) * I) * θ) := by
    funext θ
    rw [← exp_int_mul, ← exp_add]
    congr 1
    push_cast
    ring
  rw [he]
  by_cases hnk : n = k
  · subst n
    have hp : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    simp
    field_simp
  · have hk : ((k - n : ℤ) : ℂ) ≠ 0 := by
      exact_mod_cast (sub_ne_zero.mpr (fun h => hnk h.symm))
    rw [integral_exp_mul_complex (mul_ne_zero hk I_ne_zero)]
    have hp : exp ((((k - n : ℤ) : ℂ) * I) * ((2 * π : ℝ) : ℂ)) = 1 := by
      convert exp_int_mul_two_pi_mul_I (k - n) using 1
      congr 1
      push_cast
      ring
    rw [hp]
    simp [hnk]

/-- (TT:5440–5446) Constant division commutes with circle Fourier coefficients. -/
theorem circleCoeff_div_const (f : ℂ → ℂ) (c : ℂ) (n : ℤ) :
    circleCoeff (fun z => f z / c) n = circleCoeff f n / c := by
  unfold circleCoeff fourierCoeff
  simp only [div_mul_eq_mul_div]
  simp only [div_eq_mul_inv]
  rw [intervalIntegral.integral_mul_const]
  ring

/-- (TT:5440–5446) The symplectic pairing of two integer monomials. -/
theorem thetaSymp_zpow (k l : ℤ) :
    thetaSymp (fun z : ℂ => z ^ k) (fun z : ℂ => z ^ l) =
      if k = -l then I * k else 0 := by
  unfold thetaSymp
  simp only [circleCoeff_zpow]
  have ht (n : ℤ) : (n : ℂ) * (if n = k then 1 else 0) * (if -n = l then 1 else 0) =
      if n = k then (if -k = l then (k : ℂ) else 0) else 0 := by
    by_cases hn : n = k
    · subst n
      split_ifs <;> simp_all
    · simp [hn]
  simp_rw [ht]
  rw [tsum_ite_eq]
  by_cases hk : k = -l
  · simp [hk]
  · have hk' : -k ≠ l := by omega
    simp [hk, hk']

/-- (TT:5440–5446) Separate constant divisions factor out of the symplectic form. -/
theorem thetaSymp_div_const (f g : ℂ → ℂ) (c d : ℂ) :
    thetaSymp (fun z => f z / c) (fun z => g z / d) = thetaSymp f g / (c * d) := by
  unfold thetaSymp
  simp only [circleCoeff_div_const]
  have ht (n : ℤ) : (n : ℂ) * (circleCoeff f n / c) * (circleCoeff g (-n) / d) =
      ((n : ℂ) * circleCoeff f n * circleCoeff g (-n)) / (c * d) := by ring
  simp_rw [ht]
  rw [tsum_div_const]
  ring

/-- (TT:5440–5446) The normalized positive and negative Fourier bases have
symplectic pairing `i δ_mn`. -/
theorem thetaSymp_basis (m n : ℕ) :
    thetaSymp (fun z : ℂ => z ^ (m + 1) / Real.sqrt (m + 1))
      (fun z : ℂ => z ^ (-(n + 1 : ℤ)) / Real.sqrt (n + 1)) = I * kron m n := by
  have hpow : (fun z : ℂ => z ^ (m + 1)) = (fun z : ℂ => z ^ ((m : ℤ) + 1)) := by
    funext z
    norm_cast
  rw [thetaSymp_div_const, hpow, thetaSymp_zpow]
  simp only [neg_neg]
  by_cases hmn : m = n
  · subst n
    have hroot : (Real.sqrt (m + 1) : ℂ) * Real.sqrt (m + 1) = (m : ℂ) + 1 := by
      exact_mod_cast (Real.mul_self_sqrt (by positivity : (0 : ℝ) ≤ m + 1))
    have hm : (m : ℂ) + 1 ≠ 0 := by
      exact_mod_cast (by positivity : (m : ℝ) + 1 ≠ 0)
    simp [kron, hroot, hm]
  · have hmn' : (m : ℤ) + 1 ≠ (n : ℤ) + 1 := by omega
    simp [kron, hmn, hmn']

/-- (TT:5440–5446) Every circle monomial, with any constant normalization,
belongs to the Fourier model of the half-order Sobolev space. -/
theorem zpow_div_mem_HC (k : ℤ) (c : ℂ) : (fun z : ℂ => z ^ k / c) ∈ HC := by
  constructor
  · have he : (fun θ : ℝ => exp (θ * I) ^ k / c) =
        fun θ : ℝ => exp ((k : ℂ) * (θ * I)) / c := by
      funext θ
      rw [exp_int_mul]
    change IntervalIntegrable (fun θ : ℝ => exp (θ * I) ^ k / c) volume 0 (2 * π)
    rw [he]
    apply Continuous.intervalIntegrable
    fun_prop
  · apply summable_of_ne_finset_zero (s := {k})
    intro n hn
    have hnk : n ≠ k := by simpa using hn
    simp [circleCoeff_div_const, circleCoeff_zpow, hnk]

/-- (TT:5440) Positive circle monomials lie in `Wplus`. -/
theorem zpow_div_mem_Wplus {k : ℤ} (hk : 0 < k) (c : ℂ) :
    (fun z : ℂ => z ^ k / c) ∈ Wplus := by
  refine ⟨zpow_div_mem_HC k c, ?_⟩
  intro n hn
  have hnk : n ≠ k := by omega
  simp [circleCoeff_div_const, circleCoeff_zpow, hnk]

/-- (TT:5444) Negative circle monomials lie in `Wminus`. -/
theorem zpow_div_mem_Wminus {k : ℤ} (hk : k < 0) (c : ℂ) :
    (fun z : ℂ => z ^ k / c) ∈ Wminus := by
  refine ⟨zpow_div_mem_HC k c, ?_⟩
  intro n hn
  have hnk : n ≠ k := by omega
  simp [circleCoeff_div_const, circleCoeff_zpow, hnk]

/-- (TT:5440–5446) Square-summable coefficient data are realized by an
integrable circle function, using the genuine Hilbert Fourier basis. -/
theorem exists_circleFn_of_sq_summable (c : ℤ → ℂ)
    (hc : Summable (fun n => ‖c n‖ ^ 2)) :
    ∃ f : ℂ → ℂ, IntervalIntegrable (fun θ : ℝ => f (exp (θ * I))) volume 0 (2 * π) ∧
      ∀ n : ℤ, circleCoeff f n = c n := by
  let : Fact (0 < 2 * π) := ⟨by positivity⟩
  let v : lp (fun _ : ℤ => ℂ) 2 := ⟨c, memℓp_gen (by simpa using hc)⟩
  let F : Lp ℂ 2 (AddCircle.haarAddCircle (T := 2 * π)) :=
    (_root_.fourierBasis (T := 2 * π)).repr.symm v
  have hcoeff (n : ℤ) : _root_.fourierCoeff (F : AddCircle (2 * π) → ℂ) n = c n := by
    rw [← _root_.fourierBasis_repr]
    change ((_root_.fourierBasis (T := 2 * π)).repr
      ((_root_.fourierBasis (T := 2 * π)).repr.symm v)) n = c n
    rw [LinearIsometryEquiv.apply_symm_apply]
  let f : ℂ → ℂ := fun z => F (arg z : AddCircle (2 * π))
  have hang (θ : ℝ) : (arg (exp (θ * I)) : AddCircle (2 * π)) = (θ : AddCircle (2 * π)) := by
    change (arg (exp (θ * I)) : Real.Angle) = (θ : Real.Angle)
    simpa only [Real.Angle.toCircle_coe, Circle.coe_exp] using
      Real.Angle.arg_toCircle (θ : Real.Angle)
  have heval (θ : ℝ) : f (exp (θ * I)) = F (θ : AddCircle (2 * π)) := by
    dsimp only [f]
    rw [hang]
  refine ⟨f, ?_, ?_⟩
  · have hi : Integrable (F : AddCircle (2 * π) → ℂ) volume :=
      MemLp.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2) (Lp.memLp F).of_haarAddCircle
    have hp := (AddCircle.measurePreserving_mk (2 * π) 0).integrable_comp_of_integrable hi
    change Integrable (fun θ : ℝ => F (θ : AddCircle (2 * π)))
      (volume.restrict (Ioc 0 (0 + 2 * π))) at hp
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by positivity)]
    change Integrable (fun θ : ℝ => f (exp (θ * I))) (volume.restrict (Ioc 0 (2 * π)))
    simpa only [heval, Function.comp_apply, zero_add] using hp
  · intro n
    have hchar (θ : ℝ) : _root_.fourier (-n) (θ : AddCircle (2 * π)) = exp (-(n * θ * I)) := by
      rw [_root_.fourier_coe_apply]
      congr 1
      push_cast
      field_simp
    have ht := _root_.fourierCoeff_eq_intervalIntegral (F : AddCircle (2 * π) → ℂ) n 0
    rw [← hcoeff n]
    unfold circleCoeff TakhtajanTeo.fourierCoeff
    simp only [heval]
    rw [ht]
    simp only [zero_add, hchar, smul_eq_mul, real_smul, Complex.ofReal_div,
      Complex.ofReal_one, Complex.ofReal_mul, Complex.ofReal_ofNat]
    congr 1
    apply intervalIntegral.integral_congr
    intro θ hθ
    ring

/-- (TT:5440–5446) Weighted square-summable Fourier data are realized in `HC`.
The single zero-frequency coefficient does not require a weight. -/
theorem exists_HC_of_weighted_sq_summable (c : ℤ → ℂ)
    (hc : Summable (fun n : ℤ => |(n : ℝ)| * ‖c n‖ ^ 2)) :
    ∃ f ∈ HC, ∀ n : ℤ, circleCoeff f n = c n := by
  have hconst := (hasSum_ite_eq (0 : ℤ) (‖c 0‖ ^ 2)).summable
  have hsq : Summable (fun n : ℤ => ‖c n‖ ^ 2) := by
    apply Summable.of_nonneg_of_le (fun n => sq_nonneg _) _ (hc.add hconst)
    intro n
    by_cases hn : n = 0
    · subst n
      simp
    · have hw : (1 : ℝ) ≤ |(n : ℝ)| := by exact_mod_cast Int.one_le_abs hn
      simp only [ite_eq_right hn, add_zero]
      exact le_mul_of_one_le_left (sq_nonneg _) hw
  obtain ⟨f, hi, hcoeff⟩ := exists_circleFn_of_sq_summable c hsq
  refine ⟨f, ⟨hi, ?_⟩, hcoeff⟩
  simpa only [hcoeff] using hc

/-- (TT:5440–5446) Positive and negative Fourier projections split `HC`
at the coefficient level, with the constant coefficient separated. -/
theorem HC_fourier_decomposition {f : ℂ → ℂ} (hf : f ∈ HC) :
    ∃ fp ∈ Wplus, ∃ fm ∈ Wminus, ∃ c : ℂ, ∀ n : ℤ, circleCoeff f n =
      circleCoeff fp n + circleCoeff fm n + if n = 0 then c else 0 := by
  have hmask (p : ℤ → Prop) :
      Summable (fun n : ℤ => |(n : ℝ)| * ‖if p n then circleCoeff f n else 0‖ ^ 2) := by
    apply Summable.of_nonneg_of_le (fun n => mul_nonneg (abs_nonneg _) (sq_nonneg _)) _ hf.2
    intro n
    by_cases hn : p n
    · simp only [ite_eq_left hn, le_refl]
    · simp only [ite_eq_right hn, norm_zero, zero_pow (by decide : 2 ≠ 0), mul_zero]
      exact mul_nonneg (abs_nonneg _) (sq_nonneg _)
  let cp : ℤ → ℂ := fun n => if 0 < n then circleCoeff f n else 0
  let cm : ℤ → ℂ := fun n => if n < 0 then circleCoeff f n else 0
  obtain ⟨fp, hfp, hpc⟩ := exists_HC_of_weighted_sq_summable cp
    (by
      apply (hmask (fun n => 0 < n)).congr
      intro n
      by_cases hn : 0 < n <;> simp [cp, hn])
  obtain ⟨fm, hfm, hmc⟩ := exists_HC_of_weighted_sq_summable cm
    (by
      apply (hmask (fun n => n < 0)).congr
      intro n
      by_cases hn : n < 0 <;> simp [cm, hn])
  refine ⟨fp, ⟨hfp, ?_⟩, fm, ⟨hfm, ?_⟩, circleCoeff f 0, ?_⟩
  · intro n hn
    rw [hpc]
    simp [cp, not_lt.mpr hn]
  · intro n hn
    rw [hmc]
    simp [cm, not_lt.mpr hn]
  · intro n
    rw [hpc, hmc]
    by_cases hn0 : n = 0
    · subst n
      simp [cp, cm]
    · by_cases hn : 0 < n
      · have hn' : ¬n < 0 := by omega
        simp [cp, cm, hn, hn', hn0]
      · have hn' : n < 0 := by omega
        simp [cp, cm, hn, hn', hn0]

/-- (TT:5428–5446) `Θ` is a symplectic form on `𝓗`:
- it is real and antisymmetric there;
- `W₊`, `W₋` are isotropic;
- `𝓗_ℂ = W₊ ⊕ W₋` up to constants;
- `Θ` is nondegenerate on `W₊ × W₋`.

In the bases, `Θ(e_m, f_n) = i δ_{mn}`. -/
theorem thetaSymp_spec :
    (∀ f ∈ HR, ∀ g ∈ HR, (thetaSymp f g).im = 0 ∧ thetaSymp f g = -thetaSymp g f) ∧
      (∀ f ∈ Wplus, ∀ g ∈ Wplus, thetaSymp f g = 0) ∧ (∀ f ∈ Wminus, ∀ g ∈ Wminus, thetaSymp f g = 0) ∧
      (∀ f ∈ HC, ∃ fp ∈ Wplus, ∃ fm ∈ Wminus, ∃ c : ℂ, ∀ n : ℤ, circleCoeff f n =
        circleCoeff fp n + circleCoeff fm n + if n = 0 then c else 0) ∧
      ∀ m n : ℕ, thetaSymp (fun z => z ^ (m + 1) / Real.sqrt (m + 1)) (fun z => z ^ (-(n + 1 : ℤ)) / Real.sqrt (n + 1)) =
        I * kron m n := by
  exact ⟨fun f hf g hg => ⟨thetaSymp_real hf hg, thetaSymp_antisymm f g⟩,
    fun f hf g hg => thetaSymp_Wplus hf hg,
    fun f hf g hg => thetaSymp_Wminus hf hg,
    fun f hf => HC_fourier_decomposition hf, thetaSymp_basis⟩

/-- `(Zx)_m = Σ_n Z_{mn} x_n`. -/
def matApply (Z : ℕ → ℕ → ℂ) (x : ℕ → ℂ) (m : ℕ) : ℂ := ∑' n, Z m n * x n
/-- `x ∈ ℓ²`. -/
def IsL2 (x : ℕ → ℂ) : Prop := Summable fun n => ‖x n‖ ^ 2
/-- `‖x‖² = Σ |x_n|²`. -/
def sqSum (x : ℕ → ℂ) : ℝ := ∑' n, ‖x n‖ ^ 2
/-- The matrix `Z` is a bounded operator on `ℓ²`. -/
def IsBoundedMat (Z : ℕ → ℕ → ℂ) : Prop := ∃ C, ∀ x, IsL2 x → IsL2 (matApply Z x) ∧ sqSum (matApply Z x) ≤ C * sqSum x
/-- Boundedness tested on finitely supported conjugate rows forces each row
to be square summable; no totalized divergent row sum is used. -/
theorem isBoundedMat_row_isL2 {Z : ℕ → ℕ → ℂ} (hZ : IsBoundedMat Z) (m : ℕ) :
    IsL2 (Z m) := by
  obtain ⟨C, hC⟩ := hZ
  apply summable_of_sum_le (c := max C 0) (fun j => sq_nonneg ‖Z m j‖)
  intro s
  let x : ℕ → ℂ := fun j => if j ∈ s then conj (Z m j) else 0
  have hx : IsL2 x := by
    apply summable_of_ne_finset_zero (s := s)
    intro j hj
    simp [x, hj]
  have hxsum : sqSum x = ∑ j ∈ s, ‖Z m j‖ ^ 2 := by
    unfold sqSum
    rw [tsum_eq_sum (s := s) (fun j hj => by simp [x, hj])]
    apply Finset.sum_congr rfl
    intro j hj
    simp [x, hj]
  have hxm : matApply Z x m = ((∑ j ∈ s, ‖Z m j‖ ^ 2 : ℝ) : ℂ) := by
    unfold matApply
    rw [tsum_eq_sum (s := s) (fun j hj => by simp [x, hj]), Complex.ofReal_sum]
    apply Finset.sum_congr rfl
    intro j hj
    simp [x, hj, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have hout : Summable (fun j => ‖matApply Z x j‖ ^ 2) := (hC x hx).1
  have hcoord : ‖matApply Z x m‖ ^ 2 ≤ sqSum (matApply Z x) := by
    simpa only [Finset.sum_singleton, sqSum] using
      hout.sum_le_tsum {m} (fun j _ => sq_nonneg ‖matApply Z x j‖)
  have hS : 0 ≤ ∑ j ∈ s, ‖Z m j‖ ^ 2 := Finset.sum_nonneg (fun j _ => sq_nonneg _)
  have hbound := hcoord.trans (hC x hx).2
  rw [hxm, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hS, hxsum] at hbound
  have hmax0 : 0 ≤ max C 0 := le_max_right _ _
  have hmaxC : C ≤ max C 0 := le_max_left _ _
  have hprod := mul_le_mul_of_nonneg_right hmaxC hS
  nlinarith

/-- Every coordinate series of a bounded matrix acting on an `ℓ²` vector is
absolutely convergent. The elementary estimate `ab ≤ a²+b²` suffices. -/
theorem isBoundedMat_summable_norm {Z : ℕ → ℕ → ℂ} (hZ : IsBoundedMat Z)
    {x : ℕ → ℂ} (hx : IsL2 x) (m : ℕ) : Summable (fun n => ‖Z m n * x n‖) := by
  have hrow : Summable (fun n => ‖Z m n‖ ^ 2) := isBoundedMat_row_isL2 hZ m
  apply Summable.of_nonneg_of_le (fun n => norm_nonneg _) _ (hrow.add hx)
  intro n
  rw [norm_mul]
  nlinarith [sq_nonneg (‖Z m n‖ - ‖x n‖), mul_nonneg (norm_nonneg (Z m n)) (norm_nonneg (x n))]

/-- A bounded matrix has genuinely summable coordinate series. -/
theorem isBoundedMat_summable {Z : ℕ → ℕ → ℂ} (hZ : IsBoundedMat Z)
    {x : ℕ → ℂ} (hx : IsL2 x) (m : ℕ) : Summable (fun n => Z m n * x n) :=
  (isBoundedMat_summable_norm hZ hx m).of_norm

/-- Addition is respected because both coordinate series really converge. -/
theorem matApply_add_of_bounded {Z : ℕ → ℕ → ℂ} (hZ : IsBoundedMat Z)
    {x y : ℕ → ℂ} (hx : IsL2 x) (hy : IsL2 y) :
    matApply Z (x + y) = matApply Z x + matApply Z y := by
  funext m
  simp only [matApply, Pi.add_apply, mul_add]
  exact (isBoundedMat_summable hZ hx m).tsum_add (isBoundedMat_summable hZ hy m)

/-- Deleting finitely many output coordinates preserves square summability
and cannot increase the squared norm. -/
theorem matApply_tail_sqSum_le {Z : ℕ → ℕ → ℂ} (hZ : IsBoundedMat Z)
    {x : ℕ → ℂ} (hx : IsL2 x) (N : ℕ) :
    IsL2 (matApply (fun m n => if m < N then 0 else Z m n) x) ∧
      sqSum (matApply (fun m n => if m < N then 0 else Z m n) x) ≤ sqSum (matApply Z x) := by
  obtain ⟨C, hC⟩ := hZ
  have hout : Summable (fun m => ‖matApply Z x m‖ ^ 2) := (hC x hx).1
  have hpoint (m : ℕ) :
      ‖matApply (fun m n => if m < N then 0 else Z m n) x m‖ ^ 2 ≤ ‖matApply Z x m‖ ^ 2 := by
    by_cases hm : m < N
    · simp [matApply, hm]
    · simp [matApply, hm]
  have htail : Summable (fun m => ‖matApply (fun m n => if m < N then 0 else Z m n) x m‖ ^ 2) :=
    Summable.of_nonneg_of_le (fun m => sq_nonneg _) hpoint hout
  exact ⟨htail, htail.tsum_le_tsum hpoint hout⟩

/-- Every tail in the compact-matrix criterion remains a bounded matrix. -/
theorem isBoundedMat_tail {Z : ℕ → ℕ → ℂ} (hZ : IsBoundedMat Z) (N : ℕ) :
    IsBoundedMat (fun m n => if m < N then 0 else Z m n) := by
  obtain ⟨C, hC⟩ := hZ
  refine ⟨C, ?_⟩
  intro x hx
  have ht := matApply_tail_sqSum_le ⟨C, hC⟩ hx N
  exact ⟨ht.1, ht.2.trans (hC x hx).2⟩

/-- The matrix product `(AB)_{mn} = Σ_k A_{mk} B_{kn}`. -/
def mulMat (A B : ℕ → ℕ → ℂ) (m n : ℕ) : ℂ := ∑' k, A m k * B k n

/-- The Siegel disk `𝔇_∞` (TT:5448): bounded `Z : W₋ → W₊` with `Θ(Zf, g) = Θ(Zg, f)` (i.e. `Z = Zᵗ`) and
`I - ZZ̄ > 0`. For symmetric `Z`, `Z̄ = Z*`, so `I - ZZ̄ > 0` means `‖Zx‖ < ‖x‖` for `x ≠ 0`. -/
def siegelDisk : Set (ℕ → ℕ → ℂ) :=
  {Z | (∀ m n, Z m n = Z n m) ∧ IsBoundedMat Z ∧ ∀ x, IsL2 x → x ≠ 0 → sqSum (matApply Z x) < sqSum x}

/-- The restricted Siegel disk `𝔇_∞⁰ = 𝔇_∞ ∩ 𝒮₂(W₋, W₊)` (TT:5622). -/
def siegelDisk0 : Set (ℕ → ℕ → ℂ) := {Z ∈ siegelDisk | Summable fun q : ℕ × ℕ => ‖Z q.1 q.2‖ ^ 2}

/-- `γ ∈ Möb(S¹)`: `γ` agrees on `S¹` with a Möbius map preserving `𝔻`. -/
def IsCircleMobius (γ : ℂ → ℂ) : Prop :=
  ∃ α : ExtPlane → ExtPlane, IsDiscMobius α ∧ ∀ z ∈ unitCircle, ((γ z : ℂ) : ExtPlane) = α (z : ExtPlane)

/-- The Nag–Sullivan operator `Π̂(γ)(f) = f ∘ γ - (1/2π) ∮_{S¹} f ∘ γ dθ` (TT:5480). -/
def piHat (γ : ℂ → ℂ) (f : ℂ → ℂ) (z : ℂ) : ℂ := f (γ z) - circleCoeff (f ∘ γ) 0

-- `nag_sullivan` moved to `TakhtajanTeo.Ch2.S5NagSullivan` (2026-10-29, Program G).

/-- `𝔄_{mn}(γ) = (1/2π) √(m/n) ∮ γ(e^{iθ})ⁿ e^{-imθ} dθ` (TT:5502). -/
def matA (γ : ℂ → ℂ) (m n : ℕ) : ℂ :=
  Real.sqrt ((m + 1 : ℝ) / (n + 1)) * circleCoeff (fun z => γ z ^ (n + 1)) (m + 1)
/-- `𝔅_{mn}(γ) = (1/2π) √(m/n) ∮ γ(e^{iθ})^{-n} e^{-imθ} dθ` (TT:5506). -/
def matB (γ : ℂ → ℂ) (m n : ℕ) : ℂ :=
  Real.sqrt ((m + 1 : ℝ) / (n + 1)) * circleCoeff (fun z => γ z ^ (-(n + 1 : ℤ))) (m + 1)

-- `matAB_spec` moved to `TakhtajanTeo.Ch2.S5MatAB` (2026-10-29, Program G).

/-- The KYNS period mapping `Π([μ]) = 𝔅𝔄̄⁻¹`, `𝔄 = 𝔄(w_μ)`, `𝔅 = 𝔅(w_μ)` (TT:5512): the bounded matrix `Z` with `Z𝔄̄ = 𝔅`
(junk `0` if none).
[CORRECTION 2026-10-28, user-approved] `Z` is required to be bounded: among all matrices the totalized system `Z𝔄̄ = 𝔅`
need not have a unique solution, and only for bounded `Z` does `𝔄̄` invertible force `Z = 𝔅𝔄̄⁻¹`. -/
def kyns (p : T1) : ℕ → ℕ → ℂ :=
  let γ := wA (Quotient.out p : LinfStarBall)
  if h : ∃ Z : ℕ → ℕ → ℂ, IsBoundedMat Z ∧ ∀ m n, mulMat Z (fun k l => conj (matA γ k l)) m n = matB γ m n then
    h.choose else 0

-- `prop_5_1` moved to `TakhtajanTeo.Ch2.S5Prop51` (2026-10-29, Program G).

-- `cor_5_2` moved to `TakhtajanTeo.Ch2.S5Cor` (2026-10-29, Program G).

-- `cor_5_4` moved to `TakhtajanTeo.Ch2.S5Cor` (2026-10-29, Program G).

-- `remark_5_5` moved to `TakhtajanTeo.Ch2.S5Cor` (2026-10-29, Program G).

/-! ## §5.2 Embeddings into the Segal–Wilson universal Grassmannian -/

-- `embedding_spec` moved to `Ch2/S5_Embedding.lean` (2026-10-27).

-- `remark_5_7` moved to `Ch2/FaberBoundary.lean` (2026-10-26).

-- `remark_5_8` moved to `TakhtajanTeo.Ch2.S5Remark58` (2026-10-29, Program G).

end Ch2

end TakhtajanTeo
