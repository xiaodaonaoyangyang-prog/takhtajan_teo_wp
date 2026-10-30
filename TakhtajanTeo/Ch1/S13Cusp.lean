import TakhtajanTeo.Ch1.S8_FiniteDimensional
import LiZhongQC.Lemmas.FoundationFinal
import LiZhongQC.Lemmas.SelbergLemma

/-!
# `harmonicGamma_finiteDimensional` (`s13c_`, 下属3, Program G, wall W-CUSP)

For a cofinite Fuchsian group `Γ`, the span of `Ω^{-1,1}(𝔻*, Γ)` is finite dimensional (TT:1046).

Route B.
- **B1** (`s13c_transfer_group`, `s13c_transfer_cover`). The Cayley map `τ ↦ (τ + i)/(τ - i)` sends `ℍ` onto `𝔻*`.
  It conjugates `Γ` to a Li Zhong Fuchsian group `Γ' ≤ SL(2, ℝ)`. The pulled-back fundamental domain `F` covers `ℍ`
  modulo `Γ'` with the same hyperbolic integrals.
- **B2** (`s13c_siegel_fg`, the wall). Siegel: a Fuchsian group with a finite-area covering set is finitely generated.
- **B3** (`s13c_selberg`). Selberg gives a torsion-free subgroup `Γ₀` of finite index. Its covering set
  `F₀ = ⋃ r⁻¹ F` (coset representatives) satisfies `∫_{F₀} f ≤ k ∫_F f` for `Γ'`-invariant `f`. This is explicit, so
  no fundamental-domain independence is needed.
- **B4** (`s13c_no_funnel`). `ft1_decomposition` for `Γ₀`. Finite area excludes the elementary cases and the funnels.
  What remains is a compact core plus finitely many precisely invariant cusp horoballs.
- **B5** (`s13c_sup_H`). Pointwise bound `(y²|ψ(τ)|)² ≤ K ∫_{F₀} (y²|ψ|)² y⁻²` for every holomorphic, bounded,
  `Γ₀`-invariant quadratic differential `ψ` on `ℍ`.
  - Thick part: mean value plus proper discontinuity.
  - Cusps: the actual periodic function `ψ(A τ)(A'τ)²` and its `cuspFunction`, which vanishes at `0` by boundedness.
    The Schwarz lemma in `q` reduces to a compact horocycle segment.
- **B6** (`s13c_pullback`). Each `μ ∈ span (harmonicGamma Γ)` is represented a.e. by `y² ψ` for such a `ψ`.
- **B7** (`s13c_dim`). An a.e. sup bound by the `L²(F)` norm forces finite dimension (orthonormal families,
  `n ≤ K · area`).

Every bound is pointwise or a.e. on actual coefficients, with `lintegral` (no junk Bochner values or `tsum`s).
-/

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal Classical Real ComplexConjugate
noncomputable section
namespace TakhtajanTeo
open LiZhongQC

/-- The Möbius action of `SL(2, ℝ)` on `ℍ` through its entries. -/
theorem s13c_smul_coe (M : Matrix.SpecialLinearGroup (Fin 2) ℝ) (τ : UpperHalfPlane) :
    ((M • τ : UpperHalfPlane) : ℂ) = (((M 0 0 : ℝ) : ℂ) * τ + ((M 0 1 : ℝ) : ℂ)) /
      (((M 1 0 : ℝ) : ℂ) * τ + ((M 1 1 : ℝ) : ℂ)) := by
  rw [UpperHalfPlane.coe_specialLinearGroup_apply]
  rfl

/-- The denominator of the action never vanishes on `ℍ`. -/
theorem s13c_den_ne (M : Matrix.SpecialLinearGroup (Fin 2) ℝ) (τ : UpperHalfPlane) :
    ((M 1 0 : ℝ) : ℂ) * τ + ((M 1 1 : ℝ) : ℂ) ≠ 0 := by
  intro h0
  have him := congrArg Complex.im h0
  have hre := congrArg Complex.re h0
  simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero,
    Complex.zero_im, Complex.add_re, Complex.mul_re, Complex.zero_re, sub_zero] at him hre
  have hy : 0 < (τ : ℂ).im := τ.im_pos
  have hr : M 1 0 = 0 := by
    rcases mul_eq_zero.mp him with h | h
    · exact h
    · linarith
  rw [hr, zero_mul, zero_add] at hre
  have hdet := M.det_coe
  rw [Matrix.det_fin_two, hr, hre] at hdet
  simp at hdet

/-- Imaginary part of the action: `Im (M τ) = Im τ / |c τ + d|²`. -/
theorem s13c_im_smul (M : Matrix.SpecialLinearGroup (Fin 2) ℝ) (τ : UpperHalfPlane) :
    (M • τ).im * Complex.normSq (((M 1 0 : ℝ) : ℂ) * τ + ((M 1 1 : ℝ) : ℂ)) = τ.im := by
  have hd := s13c_den_ne M τ
  have hdet := M.det_coe
  rw [Matrix.det_fin_two] at hdet
  rw [← UpperHalfPlane.coe_im (M • τ), ← UpperHalfPlane.coe_im τ, s13c_smul_coe, Complex.div_im]
  have hn : Complex.normSq (((M 1 0 : ℝ) : ℂ) * τ + ((M 1 1 : ℝ) : ℂ)) ≠ 0 := by
    rwa [Ne, Complex.normSq_eq_zero]
  rw [sub_mul, div_mul_cancel₀ _ hn, div_mul_cancel₀ _ hn]
  simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero, add_zero]
  linear_combination (τ : ℂ).im * hdet

/-- **Cayley relation from the matrix intertwining** `K M = g K`, `K = [[1, i], [1, -i]]`. -/
theorem s13c_cay_rel {M : Matrix.SpecialLinearGroup (Fin 2) ℝ} {g : SL2C}
    (hK : (!![1, I; 1, -I] : Matrix (Fin 2) (Fin 2) ℂ) *
      ((Matrix.SpecialLinearGroup.map Complex.ofRealHom M : SL2C) : Matrix (Fin 2) (Fin 2) ℂ) =
        (g : Matrix (Fin 2) (Fin 2) ℂ) * !![1, I; 1, -I])
    (τ : UpperHalfPlane) (h2 : ((M • τ : UpperHalfPlane) : ℂ) ≠ I) (h1 : (τ : ℂ) ≠ I) :
    mob g (((τ : ℂ) + I) / ((τ : ℂ) - I)) =
      (((M • τ : UpperHalfPlane) : ℂ) + I) / (((M • τ : UpperHalfPlane) : ℂ) - I) := by
  have e := fun i j => congrFun (congrFun hK i) j
  have e00 := e 0 0
  have e01 := e 0 1
  have e10 := e 1 0
  have e11 := e 1 1
  simp [Matrix.mul_apply, Fin.sum_univ_two] at e00 e01 e10 e11
  rw [s13c_smul_coe] at h2 ⊢
  have hD := s13c_den_ne M τ
  set p : ℂ := ((M 0 0 : ℝ) : ℂ)
  set q : ℂ := ((M 0 1 : ℝ) : ℂ)
  set r : ℂ := ((M 1 0 : ℝ) : ℂ)
  set s : ℂ := ((M 1 1 : ℝ) : ℂ)
  set t : ℂ := (τ : ℂ)
  have ht : t - I ≠ 0 := sub_ne_zero.mpr h1
  have hN : (p * t + q) - I * (r * t + s) ≠ 0 := by
    intro h0
    apply h2
    rw [div_eq_iff hD]
    linear_combination h0
  unfold mob
  have key1 : g 0 0 * ((t + I) / (t - I)) + g 0 1 = ((p * t + q) + I * (r * t + s)) / (t - I) := by
    field_simp
    linear_combination (-t) * e00 - e01
  have key2 : g 1 0 * ((t + I) / (t - I)) + g 1 1 = ((p * t + q) - I * (r * t + s)) / (t - I) := by
    field_simp
    linear_combination (-t) * e10 - e11
  have h2' : (p * t + q) / (r * t + s) - I ≠ 0 := sub_ne_zero.mpr h2
  rw [key1, key2, div_div_div_cancel_right₀ ht,
    show p * t + q + I * (r * t + s) = ((p * t + q) / (r * t + s) + I) * (r * t + s) by
      rw [add_mul, div_mul_cancel₀ _ hD],
    show p * t + q - I * (r * t + s) = ((p * t + q) / (r * t + s) - I) * (r * t + s) by
      rw [sub_mul, div_mul_cancel₀ _ hD],
    mul_div_mul_right _ _ hD]

/-- Entries of `γ ∈ SL(2, ℝ)` moving a point of a compact `C ⊆ ℍ` into `C` are uniformly bounded. -/
theorem s13c_entry_bound {C : Set UpperHalfPlane} (hC : IsCompact C) :
    ∃ L : ℝ, ∀ γ : Matrix.SpecialLinearGroup (Fin 2) ℝ, ∀ τ ∈ C, γ • τ ∈ C → ∀ i j, |γ i j| ≤ L := by
  rcases C.eq_empty_or_nonempty with hCe | hne
  · exact ⟨0, fun γ τ hτ => by rw [hCe] at hτ; simp at hτ⟩
  obtain ⟨R, hR⟩ := (hC.image UpperHalfPlane.continuous_coe).isBounded.exists_norm_le
  obtain ⟨τ0, hτ0, hmin⟩ := hC.exists_isMinOn hne UpperHalfPlane.continuous_im.continuousOn
  set y0 := τ0.im with hy0
  have hy0p : 0 < y0 := τ0.im_pos
  have hRτ : ∀ τ ∈ C, ‖(τ : ℂ)‖ ≤ R := fun τ hτ => hR _ ⟨τ, hτ, rfl⟩
  have hR0 : 0 ≤ R := le_trans (norm_nonneg _) (hRτ τ0 hτ0)
  set Q : ℝ := max 1 (R / y0) with hQ
  have hQ1 : 1 ≤ Q := le_max_left _ _
  refine ⟨Q + Q / y0 * R + R * Q + R * Q / y0 * R + Q / y0 + R * Q / y0, ?_⟩
  intro γ τ hτ hγτ i j
  have hyτ : y0 ≤ (τ : ℂ).im := hmin hτ
  have hyγ : y0 ≤ (γ • τ).im := hmin hγτ
  have hτR := hRτ τ hτ
  have hγR := hRτ _ hγτ
  have hyτR : τ.im ≤ R := (Complex.abs_im_le_norm _).trans' (le_abs_self _) |>.trans hτR
  set D : ℂ := ((γ 1 0 : ℝ) : ℂ) * τ + ((γ 1 1 : ℝ) : ℂ) with hD
  have hDne := s13c_den_ne γ τ
  have him := s13c_im_smul γ τ
  have hnD : ‖D‖ ^ 2 ≤ R / y0 := by
    rw [← Complex.normSq_eq_norm_sq, le_div_iff₀ hy0p]
    have h1 : 0 ≤ Complex.normSq D := Complex.normSq_nonneg _
    nlinarith [him]
  have hDQ : ‖D‖ ≤ Q := by
    by_contra hc
    push_neg at hc
    have h1 : Q ^ 2 < ‖D‖ ^ 2 := by nlinarith
    have h2 : R / y0 ≤ Q := le_max_right _ _
    nlinarith
  have hpos := (div_pos (by linarith : (0:ℝ) < 1) hy0p)
  -- `c`
  have hDim : D.im = γ 1 0 * (τ : ℂ).im := by
    simp [hD, Complex.add_im, Complex.mul_im]
  have hc : |γ 1 0| ≤ Q / y0 := by
    rw [le_div_iff₀ hy0p]
    have h1 : |γ 1 0| * (τ : ℂ).im ≤ Q := by
      have h3 := (Complex.abs_im_le_norm D).trans hDQ
      rwa [hDim, abs_mul, abs_of_pos (show (0 : ℝ) < (τ : ℂ).im from τ.im_pos)] at h3
    have h2 : |γ 1 0| * y0 ≤ |γ 1 0| * (τ : ℂ).im := mul_le_mul_of_nonneg_left hyτ (abs_nonneg _)
    linarith
  -- `d`
  have hDre : D.re = γ 1 0 * (τ : ℂ).re + γ 1 1 := by
    simp [hD, Complex.add_re, Complex.mul_re]
  have hd : |γ 1 1| ≤ Q + Q / y0 * R := by
    have h1 : γ 1 1 = D.re - γ 1 0 * (τ : ℂ).re := by rw [hDre]; ring
    rw [h1]
    refine (abs_sub _ _).trans (add_le_add ((Complex.abs_re_le_norm D).trans hDQ) ?_)
    rw [abs_mul]
    exact mul_le_mul hc ((Complex.abs_re_le_norm _).trans hτR) (abs_nonneg _) (by positivity)
  -- `a`, `b`
  set N : ℂ := ((γ 0 0 : ℝ) : ℂ) * τ + ((γ 0 1 : ℝ) : ℂ) with hN
  have hNe : N = ((γ • τ : UpperHalfPlane) : ℂ) * D := by
    rw [s13c_smul_coe, div_mul_cancel₀ _ hDne]
  have hNQ : ‖N‖ ≤ R * Q := by
    rw [hNe, norm_mul]
    exact mul_le_mul hγR hDQ (norm_nonneg _) hR0
  have hNim : N.im = γ 0 0 * (τ : ℂ).im := by
    simp [hN, Complex.add_im, Complex.mul_im]
  have hNre : N.re = γ 0 0 * (τ : ℂ).re + γ 0 1 := by
    simp [hN, Complex.add_re, Complex.mul_re]
  have ha : |γ 0 0| ≤ R * Q / y0 := by
    rw [le_div_iff₀ hy0p]
    have h1 : |γ 0 0| * (τ : ℂ).im ≤ R * Q := by
      have h3 := (Complex.abs_im_le_norm N).trans hNQ
      rwa [hNim, abs_mul, abs_of_pos (show (0 : ℝ) < (τ : ℂ).im from τ.im_pos)] at h3
    have h2 : |γ 0 0| * y0 ≤ |γ 0 0| * (τ : ℂ).im := mul_le_mul_of_nonneg_left hyτ (abs_nonneg _)
    linarith
  have hb : |γ 0 1| ≤ R * Q + R * Q / y0 * R := by
    have h1 : γ 0 1 = N.re - γ 0 0 * (τ : ℂ).re := by rw [hNre]; ring
    rw [h1]
    refine (abs_sub _ _).trans (add_le_add ((Complex.abs_re_le_norm N).trans hNQ) ?_)
    rw [abs_mul]
    exact mul_le_mul ha ((Complex.abs_re_le_norm _).trans hτR) (abs_nonneg _) (by positivity)
  have hq0 : 0 ≤ Q := by linarith
  have t1 : 0 ≤ Q / y0 * R := by positivity
  have t2 : 0 ≤ R * Q := by positivity
  have t3 : 0 ≤ R * Q / y0 * R := by positivity
  have t4 : 0 ≤ Q / y0 := by positivity
  have t5 : 0 ≤ R * Q / y0 := by positivity
  fin_cases i <;> fin_cases j
  · simp only [Fin.zero_eta, Fin.isValue]; linarith
  · simp only [Fin.zero_eta, Fin.isValue, Fin.mk_one]; linarith
  · simp only [Fin.zero_eta, Fin.isValue, Fin.mk_one]; linarith
  · simp only [Fin.isValue, Fin.mk_one]; linarith

/-- Entrywise form of the Cayley intertwining `K M = g K`, `K = [[1, i], [1, -i]]`. -/
theorem s13c_cay_entries {M : Matrix.SpecialLinearGroup (Fin 2) ℝ} {g : SL2C}
    (hK : (!![1, I; 1, -I] : Matrix (Fin 2) (Fin 2) ℂ) *
      ((Matrix.SpecialLinearGroup.map Complex.ofRealHom M : SL2C) : Matrix (Fin 2) (Fin 2) ℂ) =
        (g : Matrix (Fin 2) (Fin 2) ℂ) * !![1, I; 1, -I]) :
    ((M 0 0 : ℝ) : ℂ) + I * ((M 1 0 : ℝ) : ℂ) = g 0 0 + g 0 1 ∧
    ((M 0 1 : ℝ) : ℂ) + I * ((M 1 1 : ℝ) : ℂ) = (g 0 0 - g 0 1) * I ∧
    ((M 0 0 : ℝ) : ℂ) - I * ((M 1 0 : ℝ) : ℂ) = g 1 0 + g 1 1 ∧
    ((M 0 1 : ℝ) : ℂ) - I * ((M 1 1 : ℝ) : ℂ) = (g 1 0 - g 1 1) * I := by
  have e := fun i j => congrFun (congrFun hK i) j
  have e00 := e 0 0
  have e01 := e 0 1
  have e10 := e 1 0
  have e11 := e 1 1
  simp [Matrix.mul_apply, Fin.sum_univ_two] at e00 e01 e10 e11
  refine ⟨?_, ?_, ?_, ?_⟩
  · linear_combination e00
  · linear_combination e01
  · linear_combination e10
  · linear_combination e11

/-- The real matrix of a Cayley intertwining is determined by `g`. -/
theorem s13c_cay_inj {M1 M2 : Matrix.SpecialLinearGroup (Fin 2) ℝ} {g : SL2C}
    (h1 : (!![1, I; 1, -I] : Matrix (Fin 2) (Fin 2) ℂ) *
      ((Matrix.SpecialLinearGroup.map Complex.ofRealHom M1 : SL2C) : Matrix (Fin 2) (Fin 2) ℂ) =
        (g : Matrix (Fin 2) (Fin 2) ℂ) * !![1, I; 1, -I])
    (h2 : (!![1, I; 1, -I] : Matrix (Fin 2) (Fin 2) ℂ) *
      ((Matrix.SpecialLinearGroup.map Complex.ofRealHom M2 : SL2C) : Matrix (Fin 2) (Fin 2) ℂ) =
        (g : Matrix (Fin 2) (Fin 2) ℂ) * !![1, I; 1, -I]) :
    M1 = M2 := by
  obtain ⟨a1, b1, -, -⟩ := s13c_cay_entries h1
  obtain ⟨a2, b2, -, -⟩ := s13c_cay_entries h2
  have p := a1.trans a2.symm
  have q := b1.trans b2.symm
  have p0 := congrArg Complex.re p
  have p1 := congrArg Complex.im p
  have q0 := congrArg Complex.re q
  have q1 := congrArg Complex.im q
  simp at p0 p1 q0 q1
  ext i j
  fin_cases i <;> fin_cases j
  · exact p0
  · exact q0
  · exact p1
  · exact q1

/-- Entry bounds transfer through the Cayley intertwining. -/
theorem s13c_cay_bound {M : Matrix.SpecialLinearGroup (Fin 2) ℝ} {g : SL2C}
    (hK : (!![1, I; 1, -I] : Matrix (Fin 2) (Fin 2) ℂ) *
      ((Matrix.SpecialLinearGroup.map Complex.ofRealHom M : SL2C) : Matrix (Fin 2) (Fin 2) ℂ) =
        (g : Matrix (Fin 2) (Fin 2) ℂ) * !![1, I; 1, -I])
    {L : ℝ} (hL : ∀ i j, |M i j| ≤ L) (i j : Fin 2) :
    ‖(g : Matrix (Fin 2) (Fin 2) ℂ) i j‖ ≤ 2 * L + 2 * L := by
  obtain ⟨e1, e2, e3, e4⟩ := s13c_cay_entries hK
  have hL0 : 0 ≤ L := (abs_nonneg _).trans (hL 0 0)
  have hab : ∀ a b : ℝ, |a| ≤ L → |b| ≤ L →
      ‖(a : ℂ) + I * b‖ ≤ 2 * L ∧ ‖(a : ℂ) - I * b‖ ≤ 2 * L := by
    intro a b ha hb
    have n1 := norm_add_le (a : ℂ) (I * b)
    have n2 := norm_sub_le (a : ℂ) (I * b)
    simp only [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs] at n1 n2
    constructor <;> linarith
  have hpair : ∀ x y : ℂ, ‖x + y‖ ≤ 2 * L → ‖(x - y) * I‖ ≤ 2 * L →
      ‖x‖ ≤ 2 * L + 2 * L ∧ ‖y‖ ≤ 2 * L + 2 * L := by
    intro x y h1 h2
    rw [norm_mul, Complex.norm_I, mul_one] at h2
    have n1 := norm_add_le (x + y) (x - y)
    have n2 := norm_sub_le (x + y) (x - y)
    rw [show x + y + (x - y) = 2 * x by ring, norm_mul] at n1
    rw [show x + y - (x - y) = 2 * y by ring, norm_mul] at n2
    have h22 : ‖(2 : ℂ)‖ = 2 := by simp
    rw [h22] at n1 n2
    constructor <;> linarith
  have r0 := hpair (g 0 0) (g 0 1) (by rw [← e1]; exact (hab _ _ (hL 0 0) (hL 1 0)).1)
    (by rw [← e2]; exact (hab _ _ (hL 0 1) (hL 1 1)).1)
  have r1 := hpair (g 1 0) (g 1 1) (by rw [← e3]; exact (hab _ _ (hL 0 0) (hL 1 0)).2)
    (by rw [← e4]; exact (hab _ _ (hL 0 1) (hL 1 1)).2)
  fin_cases i <;> fin_cases j
  · exact r0.1
  · exact r0.2
  · exact r1.1
  · exact r1.2

/-- The inverse Cayley map `w ↦ i (w + 1)/(w - 1)` sends `𝔻*` into `ℍ`. -/
theorem s13c_cayInv_im {w : ℂ} (hw : 1 < ‖w‖) : 0 < (I * (w + 1) / (w - 1)).im := by
  have hw1 : w - 1 ≠ 0 := by
    intro h
    rw [sub_eq_zero] at h
    rw [h, norm_one] at hw
    exact lt_irrefl _ hw
  have h2 : 1 < w.re * w.re + w.im * w.im := by
    rw [← Complex.normSq_apply, ← Complex.sq_norm]
    nlinarith [norm_nonneg w]
  have hn : 0 < Complex.normSq (w - 1) := Complex.normSq_pos.mpr hw1
  rw [mul_div_assoc]
  simp only [Complex.mul_im, Complex.I_re, Complex.I_im, zero_mul, zero_add, one_mul]
  rw [Complex.div_re, ← add_div]
  apply div_pos _ hn
  simp only [Complex.add_re, Complex.sub_re, Complex.one_re, Complex.add_im, Complex.sub_im,
    Complex.one_im, sub_zero, add_zero]
  nlinarith

/-- The Cayley map inverts the inverse Cayley map. -/
theorem s13c_cay_cayInv {w : ℂ} (hw1 : w - 1 ≠ 0) :
    (I * (w + 1) / (w - 1) + I) / (I * (w + 1) / (w - 1) - I) = w := by
  have h2 : I * (w + 1) / (w - 1) - I = 2 * I / (w - 1) := by
    rw [eq_div_iff hw1, sub_mul, div_mul_cancel₀ _ hw1]
    ring
  have h3 : I * (w + 1) / (w - 1) + I = 2 * I * w / (w - 1) := by
    rw [eq_div_iff hw1, add_mul, div_mul_cancel₀ _ hw1]
    ring
  have hI : (2 : ℂ) * I ≠ 0 := mul_ne_zero two_ne_zero I_ne_zero
  rw [h2, h3, div_div_div_cancel_right₀ hw1, mul_div_cancel_left₀ w hI]

/-- The inverse Cayley map inverts the Cayley map. -/
theorem s13c_cayInv_cay {z : ℂ} (hz : z - I ≠ 0) :
    I * ((z + I) / (z - I) + 1) / ((z + I) / (z - I) - 1) = z := by
  have h1 : (z + I) / (z - I) + 1 = 2 * z / (z - I) := by
    rw [eq_div_iff hz, add_mul, div_mul_cancel₀ _ hz]
    ring
  have h2 : (z + I) / (z - I) - 1 = 2 * I / (z - I) := by
    rw [eq_div_iff hz, sub_mul, div_mul_cancel₀ _ hz]
    ring
  have hI : (2 : ℂ) * I ≠ 0 := mul_ne_zero two_ne_zero I_ne_zero
  rw [h1, h2, mul_div_assoc', div_div_div_cancel_right₀ hz, show I * (2 * z) = 2 * I * z by ring,
    mul_div_cancel_left₀ z hI]

/-- Derivative of the Cayley map. -/
theorem s13c_cay_hasDerivAt {z : ℂ} (hz : z - I ≠ 0) :
    HasDerivAt (fun z : ℂ => (z + I) / (z - I)) (-(2 * I) / (z - I) ^ 2) z := by
  have h := ((hasDerivAt_id' z).add_const I).div ((hasDerivAt_id' z).sub_const I) hz
  convert h using 1
  ring

/-- The Cayley map sends `ℍ` into `𝔻*`. -/
theorem s13c_cay_ext {z : ℂ} (hz : 0 < z.im) (hzI : z - I ≠ 0) : 1 < ‖(z + I) / (z - I)‖ := by
  rw [norm_div, one_lt_div (norm_pos_iff.mpr hzI), ← sq_lt_sq₀ (norm_nonneg _) (norm_nonneg _),
    Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply]
  simp only [Complex.add_re, Complex.sub_re, Complex.I_re, Complex.add_im, Complex.sub_im, Complex.I_im,
    add_zero, sub_zero]
  nlinarith

/-- Jacobian identity: `|cay'(z)|² ρ(cay z) = (Im z)⁻²`. -/
theorem s13c_cay_jac {z : ℂ} (hz : 0 < z.im) (hzI : z - I ≠ 0) :
    ‖-(2 * I) / (z - I) ^ 2‖ ^ 2 * rho ((z + I) / (z - I)) = (z.im ^ 2)⁻¹ := by
  have hd : ‖-(2 * I) / (z - I) ^ 2‖ ^ 2 = 4 / (‖z - I‖ ^ 2) ^ 2 := by
    rw [norm_div, norm_neg, norm_mul, Complex.norm_I, norm_pow, div_pow]
    norm_num
  have hc : ‖(z + I) / (z - I)‖ ^ 2 = ‖z + I‖ ^ 2 / ‖z - I‖ ^ 2 := by rw [norm_div, div_pow]
  have hab : ‖z + I‖ ^ 2 = ‖z - I‖ ^ 2 + 4 * z.im := by
    rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply]
    simp only [Complex.add_re, Complex.sub_re, Complex.I_re, Complex.add_im, Complex.sub_im,
      Complex.I_im, add_zero, sub_zero]
    ring
  have ha : 0 < ‖z - I‖ ^ 2 := pow_pos (norm_pos_iff.mpr hzI) 2
  rw [show rho ((z + I) / (z - I)) = 4 / (1 - ‖(z + I) / (z - I)‖ ^ 2) ^ 2 from rfl, hd, hc, hab]
  generalize ‖z - I‖ ^ 2 = a at ha ⊢
  have ha0 : a ≠ 0 := ha.ne'
  have hy0 : z.im ≠ 0 := hz.ne'
  rw [one_sub_div ha0, show a - (a + 4 * z.im) = -(4 * z.im) by ring]
  field_simp

/-- A Cayley relation `mob g ∘ cay = cay ∘ M` (valid off `τ = i`, `M τ = i`) forces `M τ₀ ≠ i` at every
`τ₀ ≠ i` where `mob g` has no pole at `cay τ₀`. -/
theorem s13c_not_pole {M : Matrix.SpecialLinearGroup (Fin 2) ℝ} {g : SL2C} {τ0 : UpperHalfPlane}
    (h0 : (τ0 : ℂ) ≠ I) (hden : g 1 0 * (((τ0 : ℂ) + I) / ((τ0 : ℂ) - I)) + g 1 1 ≠ 0)
    (hrel : ∀ τ : UpperHalfPlane, (τ : ℂ) ≠ I → ((M • τ : UpperHalfPlane) : ℂ) ≠ I →
      mob g (((τ : ℂ) + I) / ((τ : ℂ) - I)) =
        (((M • τ : UpperHalfPlane) : ℂ) + I) / (((M • τ : UpperHalfPlane) : ℂ) - I)) :
    ((M • τ0 : UpperHalfPlane) : ℂ) ≠ I := by
  intro hM
  obtain ⟨H, hH⟩ : ∃ H : ℂ → ℂ, H = fun z => (((M 0 0 : ℝ) : ℂ) * z + ((M 0 1 : ℝ) : ℂ)) /
      (((M 1 0 : ℝ) : ℂ) * z + ((M 1 1 : ℝ) : ℂ)) := ⟨_, rfl⟩
  have hdet : ((M 0 0 : ℝ) : ℂ) * ((M 1 1 : ℝ) : ℂ) - ((M 0 1 : ℝ) : ℂ) * ((M 1 0 : ℝ) : ℂ) = 1 := by
    have := M.det_coe
    rw [Matrix.det_fin_two] at this
    exact_mod_cast this
  have hHcont : ContinuousAt H (τ0 : ℂ) := by
    rw [hH]
    exact ((continuousAt_const.mul continuousAt_id).add continuousAt_const).div
      ((continuousAt_const.mul continuousAt_id).add continuousAt_const) (s13c_den_ne M τ0)
  have hHz0 : H (τ0 : ℂ) = I := by
    rw [hH, ← hM, s13c_smul_coe]
  have hHM : ∀ (z : ℂ) (hz : 0 < z.im), ((M • (⟨z, hz⟩ : UpperHalfPlane) : UpperHalfPlane) : ℂ) = H z := by
    intro z hz
    rw [hH, s13c_smul_coe]
  have hinj : ∀ z : ℂ, 0 < z.im → H z = H (τ0 : ℂ) → z = (τ0 : ℂ) := by
    intro z hz e
    rw [hH] at e
    simp only at e
    rw [div_eq_div_iff (s13c_den_ne M ⟨z, hz⟩) (s13c_den_ne M τ0)] at e
    linear_combination e - (z - (τ0 : ℂ)) * hdet
  have hc : ContinuousAt (fun z : ℂ => (z + I) / (z - I)) (τ0 : ℂ) :=
    (continuousAt_id.add continuousAt_const).div (continuousAt_id.sub continuousAt_const)
      (sub_ne_zero.mpr h0)
  have hm : ContinuousAt (mob g) (((τ0 : ℂ) + I) / ((τ0 : ℂ) - I)) :=
    (fd_mob_differentiableAt g hden).continuousAt
  have hφ : ContinuousAt (fun z : ℂ => mob g ((z + I) / (z - I)) * (H z - I)) (τ0 : ℂ) :=
    (ContinuousAt.comp (f := fun z : ℂ => (z + I) / (z - I)) hm hc).mul (hHcont.sub continuousAt_const)
  have hT1 : Tendsto (fun z : ℂ => mob g ((z + I) / (z - I)) * (H z - I)) (𝓝[≠] (τ0 : ℂ))
      (𝓝 (mob g (((τ0 : ℂ) + I) / ((τ0 : ℂ) - I)) * (H (τ0 : ℂ) - I))) :=
    hφ.tendsto.mono_left nhdsWithin_le_nhds
  have e1 : ∀ᶠ z in 𝓝 (τ0 : ℂ), 0 < z.im :=
    (isOpen_lt continuous_const Complex.continuous_im).mem_nhds τ0.im_pos
  have e2 : ∀ᶠ z in 𝓝 (τ0 : ℂ), z ≠ I := continuousAt_id.eventually_ne h0
  have heq : (fun z : ℂ => mob g ((z + I) / (z - I)) * (H z - I)) =ᶠ[𝓝[≠] (τ0 : ℂ)]
      fun z => H z + I := by
    filter_upwards [nhdsWithin_le_nhds e1, nhdsWithin_le_nhds e2, self_mem_nhdsWithin] with z hz1 hz2 hz3
    have hne : H z ≠ I := by
      intro e
      exact hz3 (hinj z hz1 (e.trans hHz0.symm))
    have hne' : ((M • (⟨z, hz1⟩ : UpperHalfPlane) : UpperHalfPlane) : ℂ) ≠ I := by
      rw [hHM]
      exact hne
    have h := hrel ⟨z, hz1⟩ hz2 hne'
    rw [hHM] at h
    change mob g ((z + I) / (z - I)) = (H z + I) / (H z - I) at h
    rw [h, div_mul_cancel₀ _ (sub_ne_zero.mpr hne)]
  have hT2 : Tendsto (fun z : ℂ => H z + I) (𝓝[≠] (τ0 : ℂ)) (𝓝 (H (τ0 : ℂ) + I)) :=
    (hHcont.add continuousAt_const).tendsto.mono_left nhdsWithin_le_nhds
  have hlim := tendsto_nhds_unique hT1 (hT2.congr' heq.symm)
  rw [hHz0, sub_self, mul_zero] at hlim
  have := congrArg Complex.im hlim
  norm_num at this

/-- Jacobian identity in the form `4 y² |cay'(z)|² = (1 - |cay z|²)²`. -/
theorem s13c_cay_jac' {z : ℂ} (hz : 0 < z.im) (hzI : z - I ≠ 0) :
    z.im ^ 2 * (4 * ‖-(2 * I) / (z - I) ^ 2‖ ^ 2) = (1 - ‖(z + I) / (z - I)‖ ^ 2) ^ 2 := by
  have hd : ‖-(2 * I) / (z - I) ^ 2‖ ^ 2 = 4 / (‖z - I‖ ^ 2) ^ 2 := by
    rw [norm_div, norm_neg, norm_mul, Complex.norm_I, norm_pow, div_pow]
    norm_num
  have hc : ‖(z + I) / (z - I)‖ ^ 2 = ‖z + I‖ ^ 2 / ‖z - I‖ ^ 2 := by rw [norm_div, div_pow]
  have hab : ‖z + I‖ ^ 2 = ‖z - I‖ ^ 2 + 4 * z.im := by
    rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply]
    simp only [Complex.add_re, Complex.sub_re, Complex.I_re, Complex.add_im, Complex.sub_im,
      Complex.I_im, add_zero, sub_zero]
    ring
  have ha : 0 < ‖z - I‖ ^ 2 := pow_pos (norm_pos_iff.mpr hzI) 2
  rw [hd, hc, hab]
  generalize ‖z - I‖ ^ 2 = a at ha ⊢
  have ha0 : a ≠ 0 := ha.ne'
  rw [one_sub_div ha0, show a - (a + 4 * z.im) = -(4 * z.im) by ring]
  field_simp
  try ring

/-- The norm of the weight `(1 - |w|²)²`, as it appears in `harmonicBeltramiSet`. -/
theorem s13c_norm_weight (w : ℂ) : ‖((1 : ℂ) - (‖w‖ : ℂ) ^ 2) ^ 2‖ = (1 - ‖w‖ ^ 2) ^ 2 := by
  rw [show ((1 : ℂ) - (‖w‖ : ℂ) ^ 2) ^ 2 = (((1 - ‖w‖ ^ 2) ^ 2 : ℝ) : ℂ) by norm_cast,
    Complex.norm_real, Real.norm_of_nonneg (sq_nonneg _)]

/-- An a.e. property on `𝔻*` holds a.e. along `mob g`, `g ∈ SU(1,1)`. -/
theorem s13c_mob_ae {g : SL2C} (hg : IsSU11 g) {P : ℂ → Prop}
    (h : ∀ᵐ w ∂(volume.restrict unitDiscExterior), P w) :
    ∀ᵐ z ∂(volume.restrict unitDiscExterior), P (mob g z) := by
  have hE : MeasurableSet unitDiscExterior := (isOpen_lt continuous_const continuous_norm).measurableSet
  have h1 := (ae_restrict_iff' hE).mp h
  set N : Set ℂ := {w | ¬ (w ∈ unitDiscExterior → P w)} with hN
  have hN0 : volume N = 0 := ae_iff.mp h1
  set G : Set ℂ := {w | (g⁻¹ : SL2C) 1 0 * w + (g⁻¹ : SL2C) 1 1 ≠ 0} with hG
  have hd : DifferentiableOn ℂ (mob g⁻¹) (N ∩ G) := fun w hw =>
    (fd_mob_differentiableAt g⁻¹ hw.2).differentiableWithinAt
  have hnull : volume (mob g⁻¹ '' (N ∩ G)) = 0 :=
    addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume (hd.restrictScalars ℝ)
      (measure_mono_null inter_subset_left hN0)
  have hpole : volume {z : ℂ | g 1 0 * z + g 1 1 = 0} = 0 := (fd_denom_finite g).measure_zero volume
  filter_upwards [ae_restrict_mem hE, ae_restrict_of_ae (compl_mem_ae_iff.mpr hnull),
    ae_restrict_of_ae (compl_mem_ae_iff.mpr hpole)] with z hz h1 h2
  have hD : g 1 0 * z + g 1 1 ≠ 0 := h2
  by_contra hP
  obtain ⟨hD', hinv⟩ := fd_inv_step g hD
  exact h1 ⟨mob g z, ⟨fun h => hP (h (fd_mob_exterior hg hz hD)), hD'⟩, hinv⟩

/-- Elements of the span of `harmonicGamma Γ` are harmonic and `Γ`-invariant. -/
theorem s13c_span_mem {Γ : Subgroup SL2C} (hΓ : IsFuchsian Γ) {μ : LinfStar}
    (hμ : μ ∈ Submodule.span ℂ (harmonicGamma Γ)) : μ ∈ harmonicBeltramiSet ∧ μ ∈ LinfGamma Γ := by
  refine ⟨(mem_harmonicBeltrami_iff μ).mp (Submodule.span_le.mpr (fun x hx => hx.1) hμ), ?_⟩
  induction hμ using Submodule.span_induction with
  | mem x hx => exact hx.2
  | zero =>
    simp only [LinfGamma, Set.mem_ofPred_eq]
    intro g hg
    have h0 := Lp.coeFn_zero ℂ ∞ (volume.restrict unitDiscExterior)
    filter_upwards [s13c_mob_ae (hΓ.1 g hg) h0, h0] with z h1 h2
    rw [h1, h2]
    simp
  | add x y _ _ hx hy =>
    simp only [LinfGamma, Set.mem_ofPred_eq] at hx hy ⊢
    intro g hg
    have h0 := Lp.coeFn_add x y
    filter_upwards [hx g hg, hy g hg, s13c_mob_ae (hΓ.1 g hg) h0, h0] with z h1 h2 h3 h4
    simp only [Pi.add_apply] at h3 h4
    rw [h3, h4, add_mul, h1, h2]
  | smul a x _ hx =>
    simp only [LinfGamma, Set.mem_ofPred_eq] at hx ⊢
    intro g hg
    have h0 := Lp.coeFn_smul a x
    filter_upwards [hx g hg, s13c_mob_ae (hΓ.1 g hg) h0, h0] with z h1 h3 h4
    simp only [Pi.smul_apply, smul_eq_mul] at h3 h4
    rw [h3, h4, mul_assoc, h1]

/-- **Automorphy.** If `μ = (1 - |z|²)² φ̄` a.e. with `φ` holomorphic on `𝔻*` and `μ ∈ L∞(𝔻*, Γ)`, then
`φ (g w) g'(w)² = φ w` at every `w ∈ 𝔻*` off the pole of `g`. -/
theorem s13c_auto {Γ : Subgroup SL2C} (hΓ : IsFuchsian Γ) {μ : LinfStar} (hμ : μ ∈ LinfGamma Γ)
    {Φ : ℂ → ℂ} (hΦ : DifferentiableOn ℂ Φ unitDiscExterior)
    (hrep : ∀ᵐ z ∂(volume.restrict unitDiscExterior), μ z = (1 - ‖z‖ ^ 2) ^ 2 * conj (Φ z))
    {g : SL2C} (hg : g ∈ Γ) {w : ℂ} (hw : 1 < ‖w‖) (hD : g 1 0 * w + g 1 1 ≠ 0) :
    Φ (mob g w) * deriv (mob g) w ^ 2 = Φ w := by
  have hgS := hΓ.1 g hg
  have hE : IsOpen unitDiscExterior := isOpen_lt continuous_const continuous_norm
  set U : Set ℂ := unitDiscExterior ∩ {w | g 1 0 * w + g 1 1 ≠ 0} with hU
  have hUo : IsOpen U := hE.inter (isOpen_ne_fun (by fun_prop) continuous_const)
  have hae : ∀ᵐ z ∂(volume.restrict unitDiscExterior),
      Φ (mob g z) * (1 / (g 1 0 * z + g 1 1) ^ 2) ^ 2 = Φ z := by
    have h3 := s13c_mob_ae hgS hrep
    filter_upwards [hμ g hg, hrep, h3, wp_mob_denom_ae g, ae_restrict_mem hE.measurableSet]
      with z h1 h2 h3 hd hz
    have hz1 : 1 < ‖z‖ := hz
    have hder : deriv (mob g) z = 1 / (g 1 0 * z + g 1 1) ^ 2 := (wp_mob_hasDerivAt g hd).deriv
    rw [hder] at h1
    set d : ℂ := 1 / (g 1 0 * z + g 1 1) ^ 2 with hd_def
    have hd0 : d ≠ 0 := one_div_ne_zero (pow_ne_zero 2 hd)
    have hR : (1 - ‖mob g z‖ ^ 2) ^ 2 = (1 - ‖z‖ ^ 2) ^ 2 * ‖d‖ ^ 2 := by
      have hn := fd_mob_norm hgS hz1 hd
      have hpos : 0 < ‖g 1 0 * z + g 1 1‖ := norm_pos_iff.mpr hd
      rw [hd_def, norm_div, norm_one, norm_pow]
      have hn' : ‖mob g z‖ ^ 2 = (‖z‖ ^ 2 - 1) / ‖g 1 0 * z + g 1 1‖ ^ 2 + 1 := by linarith
      rw [hn']
      field_simp
      try ring
    have hA : ((1 : ℂ) - (‖mob g z‖ : ℂ) ^ 2) ^ 2 = ((1 : ℂ) - (‖z‖ : ℂ) ^ 2) ^ 2 * (d * conj d) := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
      exact_mod_cast hR
    have hA0 : ((1 : ℂ) - (‖z‖ : ℂ) ^ 2) ^ 2 ≠ 0 := by
      have hr : (1 - ‖z‖ ^ 2 : ℝ) ≠ 0 := (by nlinarith [norm_nonneg z] : (1 - ‖z‖ ^ 2 : ℝ) < 0).ne
      exact pow_ne_zero 2 (by exact_mod_cast hr)
    rw [h3, h2, hA] at h1
    have key : conj (Φ (mob g z) * d ^ 2) = conj (Φ z) := by
      rw [map_mul, map_pow]
      apply mul_left_cancel₀ hA0
      rw [← h1]
      field_simp
      try ring
    have := congrArg conj key
    simpa using this
  have hcont1 : ContinuousOn (fun z => Φ (mob g z) * (1 / (g 1 0 * z + g 1 1) ^ 2) ^ 2) U := by
    intro z hz
    have hz1 : 1 < ‖z‖ := hz.1
    have hzd : g 1 0 * z + g 1 1 ≠ 0 := hz.2
    have hm : ContinuousAt (mob g) z := (fd_mob_differentiableAt g hzd).continuousAt
    have hΦc : ContinuousAt Φ (mob g z) :=
      (hΦ.differentiableAt (hE.mem_nhds (fd_mob_exterior hgS hz1 hzd))).continuousAt
    have hq : ContinuousAt (fun z : ℂ => (1 / (g 1 0 * z + g 1 1) ^ 2) ^ 2) z := by
      fun_prop (disch := exact pow_ne_zero 2 hzd)
    exact ((ContinuousAt.comp (f := mob g) hΦc hm).mul hq).continuousWithinAt
  have hEq := Measure.eqOn_open_of_ae_eq (ae_restrict_of_ae_restrict_of_subset inter_subset_left hae) hUo
    hcont1 (hΦ.continuousOn.mono inter_subset_left)
  have := hEq ⟨hw, hD⟩
  rw [(wp_mob_hasDerivAt g hD).deriv]
  exact this

/-- An a.e. property on `𝔻*` holds a.e. on `ℍ` along the Cayley map. -/
theorem s13c_cay_ae {P : ℂ → Prop} (h : ∀ᵐ w ∂(volume.restrict unitDiscExterior), P w) :
    ∀ᵐ z ∂(volume.restrict upperHalf), 0 < z.im → z ≠ I ∧ P ((z + I) / (z - I)) := by
  have hE : MeasurableSet unitDiscExterior := (isOpen_lt continuous_const continuous_norm).measurableSet
  have h1 := (ae_restrict_iff' hE).mp h
  set N : Set ℂ := {w | ¬ (w ∈ unitDiscExterior → P w)} with hN
  have hN0 : volume N = 0 := ae_iff.mp h1
  have hNd : DifferentiableOn ℂ (fun w : ℂ => I * (w + 1) / (w - 1)) N := by
    intro w hw
    have hw1 : 1 < ‖w‖ := by
      by_contra hc
      exact hw (fun h => absurd h hc)
    have hw1' : w - 1 ≠ 0 := by
      intro h
      rw [sub_eq_zero] at h
      rw [h, norm_one] at hw1
      exact lt_irrefl _ hw1
    exact (by fun_prop (disch := exact hw1') :
      DifferentiableAt ℂ (fun w : ℂ => I * (w + 1) / (w - 1)) w).differentiableWithinAt
  have hNi : volume ((fun w : ℂ => I * (w + 1) / (w - 1)) '' N) = 0 :=
    addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume (hNd.restrictScalars ℝ) hN0
  have hbad : ∀ᵐ z ∂volume, z ∉ (fun w : ℂ => I * (w + 1) / (w - 1)) '' N ∧ z ≠ I := by
    filter_upwards [compl_mem_ae_iff.mpr hNi, compl_mem_ae_iff.mpr (measure_singleton I)] with z h1 h2
    exact ⟨h1, h2⟩
  filter_upwards [ae_restrict_of_ae hbad] with z hz0 hz
  obtain ⟨hzN, hzI⟩ := hz0
  have hzI' : z - I ≠ 0 := sub_ne_zero.mpr hzI
  refine ⟨hzI, ?_⟩
  by_contra hc
  exact hzN ⟨(z + I) / (z - I), fun h => hc (h (s13c_cay_ext hz hzI')), s13c_cayInv_cay hzI'⟩

/-- Every point is eventually avoided in a punctured neighbourhood. -/
theorem s13c_ev_ne (z0 a : ℂ) : ∀ᶠ z in 𝓝[≠] z0, z ≠ a := by
  by_cases h : z0 = a
  · rw [h]
    exact self_mem_nhdsWithin
  · exact nhdsWithin_le_nhds (continuousAt_id.eventually_ne h)

/-- Two functions continuous at `z₀` and equal on a punctured neighbourhood agree at `z₀`. -/
theorem s13c_eq_of_punctured {f g : ℂ → ℂ} {z0 : ℂ} (hf : ContinuousAt f z0) (hg : ContinuousAt g z0)
    (h : ∀ᶠ z in 𝓝[≠] z0, f z = g z) : f z0 = g z0 :=
  tendsto_nhds_unique (hf.tendsto.mono_left nhdsWithin_le_nhds)
    ((hg.tendsto.mono_left nhdsWithin_le_nhds).congr' (h.mono fun _ e => e.symm))

/-- Derivative of the real Möbius map on `ℂ` at a point of `ℍ`. -/
theorem s13c_real_mob_hasDerivAt (M : Matrix.SpecialLinearGroup (Fin 2) ℝ) (τ : UpperHalfPlane) :
    HasDerivAt (fun z : ℂ => (((M 0 0 : ℝ) : ℂ) * z + ((M 0 1 : ℝ) : ℂ)) /
      (((M 1 0 : ℝ) : ℂ) * z + ((M 1 1 : ℝ) : ℂ)))
      (1 / (((M 1 0 : ℝ) : ℂ) * (τ : ℂ) + ((M 1 1 : ℝ) : ℂ)) ^ 2) (τ : ℂ) := by
  have hD := s13c_den_ne M τ
  have hdet : ((M 0 0 : ℝ) : ℂ) * ((M 1 1 : ℝ) : ℂ) - ((M 0 1 : ℝ) : ℂ) * ((M 1 0 : ℝ) : ℂ) = 1 := by
    have := M.det_coe
    rw [Matrix.det_fin_two] at this
    exact_mod_cast this
  have h := (((hasDerivAt_id' (τ : ℂ)).const_mul ((M 0 0 : ℝ) : ℂ)).add_const ((M 0 1 : ℝ) : ℂ)).div
    (((hasDerivAt_id' (τ : ℂ)).const_mul ((M 1 0 : ℝ) : ℂ)).add_const ((M 1 1 : ℝ) : ℂ)) hD
  convert h using 1
  rw [eq_div_iff (pow_ne_zero 2 hD), one_div, inv_mul_cancel₀ (pow_ne_zero 2 hD)]
  linear_combination -hdet

/-- The real Möbius map is injective on `ℍ`. -/
theorem s13c_real_mob_inj (M : Matrix.SpecialLinearGroup (Fin 2) ℝ) {z w : ℂ} (hz : 0 < z.im)
    (hw : 0 < w.im)
    (e : (((M 0 0 : ℝ) : ℂ) * z + ((M 0 1 : ℝ) : ℂ)) / (((M 1 0 : ℝ) : ℂ) * z + ((M 1 1 : ℝ) : ℂ)) =
      (((M 0 0 : ℝ) : ℂ) * w + ((M 0 1 : ℝ) : ℂ)) / (((M 1 0 : ℝ) : ℂ) * w + ((M 1 1 : ℝ) : ℂ))) :
    z = w := by
  have hdet : ((M 0 0 : ℝ) : ℂ) * ((M 1 1 : ℝ) : ℂ) - ((M 0 1 : ℝ) : ℂ) * ((M 1 0 : ℝ) : ℂ) = 1 := by
    have := M.det_coe
    rw [Matrix.det_fin_two] at this
    exact_mod_cast this
  rw [div_eq_div_iff (s13c_den_ne M ⟨z, hz⟩) (s13c_den_ne M ⟨w, hw⟩)] at e
  linear_combination e - (z - w) * hdet

/-- `s13c_smul_coe` at a point given by its coordinate. -/
theorem s13c_smul_coe' (M : Matrix.SpecialLinearGroup (Fin 2) ℝ) {z : ℂ} (hz : 0 < z.im) :
    ((M • (⟨z, hz⟩ : UpperHalfPlane) : UpperHalfPlane) : ℂ) =
      (((M 0 0 : ℝ) : ℂ) * z + ((M 0 1 : ℝ) : ℂ)) / (((M 1 0 : ℝ) : ℂ) * z + ((M 1 1 : ℝ) : ℂ)) :=
  s13c_smul_coe M ⟨z, hz⟩

/-- The real Möbius map preserves `ℍ`. -/
theorem s13c_mobR_im_pos (M : Matrix.SpecialLinearGroup (Fin 2) ℝ) {z : ℂ} (hz : 0 < z.im) :
    0 < ((((M 0 0 : ℝ) : ℂ) * z + ((M 0 1 : ℝ) : ℂ)) / (((M 1 0 : ℝ) : ℂ) * z + ((M 1 1 : ℝ) : ℂ))).im := by
  rw [← s13c_smul_coe' M hz]
  exact (M • (⟨z, hz⟩ : UpperHalfPlane)).im_pos

/-- `M⁻¹ ∘ M = id` on `ℍ`, in coordinates. -/
theorem s13c_mobR_inv (M : Matrix.SpecialLinearGroup (Fin 2) ℝ) {z : ℂ} (hz : 0 < z.im) :
    ((((M⁻¹ : Matrix.SpecialLinearGroup (Fin 2) ℝ) 0 0 : ℝ) : ℂ) *
        ((((M 0 0 : ℝ) : ℂ) * z + ((M 0 1 : ℝ) : ℂ)) / (((M 1 0 : ℝ) : ℂ) * z + ((M 1 1 : ℝ) : ℂ))) +
        (((M⁻¹ : Matrix.SpecialLinearGroup (Fin 2) ℝ) 0 1 : ℝ) : ℂ)) /
      ((((M⁻¹ : Matrix.SpecialLinearGroup (Fin 2) ℝ) 1 0 : ℝ) : ℂ) *
        ((((M 0 0 : ℝ) : ℂ) * z + ((M 0 1 : ℝ) : ℂ)) / (((M 1 0 : ℝ) : ℂ) * z + ((M 1 1 : ℝ) : ℂ))) +
        (((M⁻¹ : Matrix.SpecialLinearGroup (Fin 2) ℝ) 1 1 : ℝ) : ℂ)) = z := by
  have h := congrArg (fun x : UpperHalfPlane => (x : ℂ)) (inv_smul_smul M (⟨z, hz⟩ : UpperHalfPlane))
  simp only at h
  rw [s13c_smul_coe, s13c_smul_coe] at h
  exact h

/-- Weight-4 transfer of the invariant norm `y² |ψ|`. -/
theorem s13c_norm_transfer (M : Matrix.SpecialLinearGroup (Fin 2) ℝ) (ψ : ℂ → ℂ) (τ : UpperHalfPlane) :
    (M • τ).im ^ 2 * ‖ψ ((M • τ : UpperHalfPlane) : ℂ)‖ =
      τ.im ^ 2 * ‖ψ ((M • τ : UpperHalfPlane) : ℂ) *
        (((M 1 0 : ℝ) : ℂ) * (τ : ℂ) + ((M 1 1 : ℝ) : ℂ))⁻¹ ^ 4‖ := by
  have hD := s13c_den_ne M τ
  have hn : ‖((M 1 0 : ℝ) : ℂ) * (τ : ℂ) + ((M 1 1 : ℝ) : ℂ)‖ ≠ 0 := norm_ne_zero_iff.mpr hD
  rw [norm_mul, norm_pow, norm_inv, ← s13c_im_smul M τ, Complex.normSq_eq_norm_sq]
  field_simp
  try ring

/-- A Fuchsian group is countable. -/
theorem s13c_countable {Γ₀ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} (hΓ₀ : LiZhongQC.IsFuchsian Γ₀) :
    Countable Γ₀ := by
  have hS : (Γ₀ : Set (Matrix.SpecialLinearGroup (Fin 2) ℝ)) ⊆ ⋃ n : ℕ,
      {γ ∈ Γ₀ | ((γ • ·) '' closedBall UpperHalfPlane.I n ∩ closedBall UpperHalfPlane.I n).Nonempty} := by
    intro γ hγ
    obtain ⟨n, hn⟩ := exists_nat_ge (dist (γ • UpperHalfPlane.I) UpperHalfPlane.I)
    exact mem_iUnion.mpr ⟨n, hγ, γ • UpperHalfPlane.I,
      ⟨UpperHalfPlane.I, mem_closedBall_self (by positivity), rfl⟩, mem_closedBall.mpr hn⟩
  exact Set.countable_coe_iff.mpr
    ((Set.countable_iUnion fun n => (hΓ₀ _ (isCompact_closedBall _ _)).countable).mono hS)

/-- Change of variables for the hyperbolic area `y⁻² d²z` under `M ∈ SL(2, ℝ)`. -/
theorem s13c_hyp_cov (M : Matrix.SpecialLinearGroup (Fin 2) ℝ) {S : Set ℂ} (hSm : MeasurableSet S)
    (hSH : S ⊆ upperHalf) (h : ℂ → ℝ≥0∞) :
    ∫⁻ z in (fun z : ℂ => (((M 0 0 : ℝ) : ℂ) * z + ((M 0 1 : ℝ) : ℂ)) /
        (((M 1 0 : ℝ) : ℂ) * z + ((M 1 1 : ℝ) : ℂ))) '' S, h z * ENNReal.ofReal ((z.im ^ 2)⁻¹) =
      ∫⁻ z in S, h ((((M 0 0 : ℝ) : ℂ) * z + ((M 0 1 : ℝ) : ℂ)) /
        (((M 1 0 : ℝ) : ℂ) * z + ((M 1 1 : ℝ) : ℂ))) * ENNReal.ofReal ((z.im ^ 2)⁻¹) := by
  have hinj : InjOn (fun z : ℂ => (((M 0 0 : ℝ) : ℂ) * z + ((M 0 1 : ℝ) : ℂ)) /
      (((M 1 0 : ℝ) : ℂ) * z + ((M 1 1 : ℝ) : ℂ))) S :=
    fun z1 h1 z2 h2 e => s13c_real_mob_inj M (hSH h1) (hSH h2) e
  rw [lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hSm
    (f' := fun x => (ContinuousLinearMap.toSpanSingleton ℂ
      (1 / (((M 1 0 : ℝ) : ℂ) * x + ((M 1 1 : ℝ) : ℂ)) ^ 2)).restrictScalars ℝ)
    (fun x hx => ((s13c_real_mob_hasDerivAt M ⟨x, hSH hx⟩).hasFDerivAt.restrictScalars ℝ).hasFDerivWithinAt)
    hinj]
  refine setLIntegral_congr_fun hSm fun z hz => ?_
  simp only [det_restrictScalars_toSpanSingleton]
  have hz' : 0 < z.im := hSH hz
  have hD := s13c_den_ne M ⟨z, hz'⟩
  have him : ((((M 0 0 : ℝ) : ℂ) * z + ((M 0 1 : ℝ) : ℂ)) / (((M 1 0 : ℝ) : ℂ) * z + ((M 1 1 : ℝ) : ℂ))).im *
      Complex.normSq (((M 1 0 : ℝ) : ℂ) * z + ((M 1 1 : ℝ) : ℂ)) = z.im := by
    have h1 := s13c_im_smul M ⟨z, hz'⟩
    rw [show (M • (⟨z, hz'⟩ : UpperHalfPlane)).im =
      ((M • (⟨z, hz'⟩ : UpperHalfPlane) : UpperHalfPlane) : ℂ).im from rfl, s13c_smul_coe' M hz'] at h1
    exact h1
  have hn : 0 < Complex.normSq (((M 1 0 : ℝ) : ℂ) * z + ((M 1 1 : ℝ) : ℂ)) := Complex.normSq_pos.mpr hD
  have hY : ((((M 0 0 : ℝ) : ℂ) * z + ((M 0 1 : ℝ) : ℂ)) / (((M 1 0 : ℝ) : ℂ) * z + ((M 1 1 : ℝ) : ℂ))).im =
      z.im / Complex.normSq (((M 1 0 : ℝ) : ℂ) * z + ((M 1 1 : ℝ) : ℂ)) := eq_div_of_mul_eq hn.ne' him
  rw [abs_of_nonneg (sq_nonneg _), mul_left_comm, ← ENNReal.ofReal_mul (sq_nonneg _)]
  congr 2
  rw [hY, norm_div, norm_one, norm_pow, Complex.sq_norm]
  have hz0 : z.im ≠ 0 := hz'.ne'
  field_simp
  try ring

/-- **Unfolding.** If `S ⊆ ℍ` is measurable and every `γ ∈ Γ₀` moving a point of `S` into `S` lies in a finite set
`D`, the integral of an invariant density over `S` is at most `#D` times its integral over the covering set `F₀`. -/
theorem s13c_unfold_gen {Γ₀ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} (hΓ₀ : LiZhongQC.IsFuchsian Γ₀)
    {F₀ : Set ℂ} (hF₀m : MeasurableSet F₀)
    (hcov₀ : ∀ᵐ z ∂(volume.restrict upperHalf), ∀ hz : 0 < z.im, ∃ M ∈ Γ₀,
      ((M • (⟨z, hz⟩ : UpperHalfPlane) : UpperHalfPlane) : ℂ) ∈ F₀)
    {S : Set ℂ} (hSm : MeasurableSet S) (hSH : S ⊆ upperHalf)
    {D : Set (Matrix.SpecialLinearGroup (Fin 2) ℝ)} (hDf : D.Finite)
    (hD : ∀ γ ∈ Γ₀, ∀ σ : UpperHalfPlane, (σ : ℂ) ∈ S → ((γ • σ : UpperHalfPlane) : ℂ) ∈ S → γ ∈ D)
    {g : ℂ → ℝ≥0∞} (hg : Measurable g)
    (hginv : ∀ γ ∈ Γ₀, ∀ τ : UpperHalfPlane, g ((γ • τ : UpperHalfPlane) : ℂ) = g τ) :
    ∫⁻ z in S, g z * ENNReal.ofReal ((z.im ^ 2)⁻¹) ≤
      hDf.toFinset.card * ∫⁻ z in F₀, g z * ENNReal.ofReal ((z.im ^ 2)⁻¹) := by
  haveI := s13c_countable hΓ₀
  have hUHm : MeasurableSet upperHalf := (isOpen_lt continuous_const Complex.continuous_im).measurableSet
  have hSH' : ∀ z ∈ S, 0 < z.im := fun z hz => hSH hz
  obtain ⟨w, hw⟩ : ∃ w : ℂ → ℝ≥0∞, w = fun z => g z * ENNReal.ofReal ((z.im ^ 2)⁻¹) := ⟨_, rfl⟩
  have hwm : Measurable w := by
    rw [hw]
    exact hg.mul (ENNReal.measurable_ofReal.comp (by fun_prop))
  have hmob : ∀ γ : Matrix.SpecialLinearGroup (Fin 2) ℝ, Measurable fun z : ℂ =>
      (((γ 0 0 : ℝ) : ℂ) * z + ((γ 0 1 : ℝ) : ℂ)) / (((γ 1 0 : ℝ) : ℂ) * z + ((γ 1 1 : ℝ) : ℂ)) :=
    fun γ => by fun_prop
  obtain ⟨T, hT⟩ : ∃ T : Γ₀ → Set ℂ, T = fun γ : Γ₀ => {z : ℂ | 0 < z.im ∧
      (((((γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) 0 0 : ℝ) : ℂ) * z +
        (((γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) 0 1 : ℝ) : ℂ)) /
        ((((γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) 1 0 : ℝ) : ℂ) * z +
        (((γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) 1 1 : ℝ) : ℂ))) ∈ F₀} := ⟨_, rfl⟩
  have hTmem : ∀ (γ : Γ₀) (z : ℂ), z ∈ T γ ↔ 0 < z.im ∧
      (((((γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) 0 0 : ℝ) : ℂ) * z +
        (((γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) 0 1 : ℝ) : ℂ)) /
        ((((γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) 1 0 : ℝ) : ℂ) * z +
        (((γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) 1 1 : ℝ) : ℂ))) ∈ F₀ := by
    intro γ z
    subst hT
    exact Iff.rfl
  have hTm : ∀ γ : Γ₀, MeasurableSet (T γ) := by
    intro γ
    subst hT
    exact (measurableSet_lt measurable_const Complex.measurable_im).inter (hmob _ hF₀m)
  obtain ⟨E, hE⟩ : ∃ E : Γ₀ → Set ℂ, E = fun γ : Γ₀ => {z : ℂ | 0 < z.im ∧
      (((((γ : Matrix.SpecialLinearGroup (Fin 2) ℝ)⁻¹ 0 0 : ℝ) : ℂ) * z +
        (((γ : Matrix.SpecialLinearGroup (Fin 2) ℝ)⁻¹ 0 1 : ℝ) : ℂ)) /
        ((((γ : Matrix.SpecialLinearGroup (Fin 2) ℝ)⁻¹ 1 0 : ℝ) : ℂ) * z +
        (((γ : Matrix.SpecialLinearGroup (Fin 2) ℝ)⁻¹ 1 1 : ℝ) : ℂ))) ∈ S} := ⟨_, rfl⟩
  have hEmem : ∀ (γ : Γ₀) (z : ℂ), z ∈ E γ ↔ 0 < z.im ∧
      (((((γ : Matrix.SpecialLinearGroup (Fin 2) ℝ)⁻¹ 0 0 : ℝ) : ℂ) * z +
        (((γ : Matrix.SpecialLinearGroup (Fin 2) ℝ)⁻¹ 0 1 : ℝ) : ℂ)) /
        ((((γ : Matrix.SpecialLinearGroup (Fin 2) ℝ)⁻¹ 1 0 : ℝ) : ℂ) * z +
        (((γ : Matrix.SpecialLinearGroup (Fin 2) ℝ)⁻¹ 1 1 : ℝ) : ℂ))) ∈ S := by
    intro γ z
    subst hE
    exact Iff.rfl
  have hEm : ∀ γ : Γ₀, MeasurableSet (E γ) := by
    intro γ
    subst hE
    exact (measurableSet_lt measurable_const Complex.measurable_im).inter (hmob _ hSm)
  -- step 1: cover `S` by the tiles
  have h1 : ∫⁻ z in S, w z ≤ ∑' γ : Γ₀, ∫⁻ z in S ∩ T γ, w z := by
    rw [← lintegral_indicator hSm]
    calc ∫⁻ z, S.indicator w z ≤ ∫⁻ z, ∑' γ : Γ₀, (S ∩ T γ).indicator w z := by
          apply lintegral_mono_ae
          filter_upwards [(ae_restrict_iff' hUHm).mp hcov₀] with z hz
          by_cases hzS : z ∈ S
          · have hz' := hSH' z hzS
            obtain ⟨M, hM, hMF⟩ := hz hz' hz'
            rw [s13c_smul_coe' M hz'] at hMF
            have hmem : z ∈ S ∩ T ⟨M, hM⟩ := ⟨hzS, (hTmem _ z).mpr ⟨hz', hMF⟩⟩
            rw [indicator_of_mem hzS, ← indicator_of_mem hmem w]
            exact ENNReal.le_tsum (f := fun γ : Γ₀ => (S ∩ T γ).indicator w z) ⟨M, hM⟩
          · rw [indicator_of_notMem hzS]
            exact zero_le
      _ = ∑' γ : Γ₀, ∫⁻ z, (S ∩ T γ).indicator w z :=
          lintegral_tsum fun γ => (hwm.indicator (hSm.inter (hTm γ))).aemeasurable
      _ = ∑' γ : Γ₀, ∫⁻ z in S ∩ T γ, w z := by
          congr 1
          funext γ
          exact lintegral_indicator (hSm.inter (hTm γ)) w
  -- step 2: move each tile into `F₀`
  have h2 : ∀ γ : Γ₀, ∫⁻ z in S ∩ T γ, w z ≤ ∫⁻ z in F₀, (E γ).indicator w z := by
    intro γ
    have hA : S ∩ T γ ⊆ upperHalf := fun z hz => hSH' z hz.1
    have hAm : MeasurableSet (S ∩ T γ) := hSm.inter (hTm γ)
    rw [lintegral_indicator (hEm γ), Measure.restrict_restrict (hEm γ)]
    calc ∫⁻ z in S ∩ T γ, w z
        = ∫⁻ z in S ∩ T γ, g ((((((γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) 0 0 : ℝ) : ℂ) * z +
            (((γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) 0 1 : ℝ) : ℂ)) /
            ((((γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) 1 0 : ℝ) : ℂ) * z +
            (((γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) 1 1 : ℝ) : ℂ)))) *
              ENNReal.ofReal ((z.im ^ 2)⁻¹) := by
          refine setLIntegral_congr_fun hAm fun z hz => ?_
          have hz' : 0 < z.im := hA hz
          have e := hginv γ γ.2 ⟨z, hz'⟩
          rw [s13c_smul_coe' _ hz'] at e
          rw [hw]
          exact congrArg (· * ENNReal.ofReal ((z.im ^ 2)⁻¹)) e.symm
      _ = ∫⁻ z in (fun z : ℂ => (((((γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) 0 0 : ℝ) : ℂ) * z +
            (((γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) 0 1 : ℝ) : ℂ)) /
            ((((γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) 1 0 : ℝ) : ℂ) * z +
            (((γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) 1 1 : ℝ) : ℂ)))) '' (S ∩ T γ),
            g z * ENNReal.ofReal ((z.im ^ 2)⁻¹) := (s13c_hyp_cov _ hAm hA g).symm
      _ ≤ ∫⁻ z in E γ ∩ F₀, g z * ENNReal.ofReal ((z.im ^ 2)⁻¹) := by
          apply lintegral_mono_set
          rintro _ ⟨z, hz, rfl⟩
          have hz' : 0 < z.im := hA hz
          refine ⟨(hEmem γ _).mpr ⟨s13c_mobR_im_pos _ hz', ?_⟩, ((hTmem γ z).mp hz.2).2⟩
          rw [s13c_mobR_inv _ hz']
          exact hz.1
      _ = ∫⁻ z in E γ ∩ F₀, w z := by rw [hw]
  -- step 3: count the overlaps
  have h3 : ∀ z, ∑' γ : Γ₀, (E γ).indicator w z ≤ hDf.toFinset.card * w z := by
    intro z
    by_cases hA : ∃ γ1 : Γ₀, z ∈ E γ1
    · obtain ⟨γ1, hz1⟩ := hA
      obtain ⟨hz1pos, hσ1S⟩ := (hEmem γ1 z).mp hz1
      have hle : ∀ γ : Γ₀, (E γ).indicator w z ≤
          D.indicator (fun _ => w z) ((γ : Matrix.SpecialLinearGroup (Fin 2) ℝ)⁻¹ * γ1) := by
        intro γ
        by_cases hz : z ∈ E γ
        · obtain ⟨_, hσS⟩ := (hEmem γ z).mp hz
          have hmemD : (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ)⁻¹ * γ1 ∈ D := by
            refine hD _ (Γ₀.mul_mem (Γ₀.inv_mem γ.2) γ1.2)
              ((γ1 : Matrix.SpecialLinearGroup (Fin 2) ℝ)⁻¹ • (⟨z, hz1pos⟩ : UpperHalfPlane)) ?_ ?_
            · rw [s13c_smul_coe' _ hz1pos]
              exact hσ1S
            · rw [mul_smul, smul_inv_smul, s13c_smul_coe' _ hz1pos]
              exact hσS
          exact le_of_eq (by rw [indicator_of_mem hz, indicator_of_mem hmemD])
        · rw [indicator_of_notMem hz]
          exact zero_le
      have hinj : Function.Injective fun γ : Γ₀ => (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ)⁻¹ * γ1 := by
        intro a b hab
        simp only [mul_left_inj, inv_inj] at hab
        exact Subtype.ext hab
      calc ∑' γ : Γ₀, (E γ).indicator w z
          ≤ ∑' γ : Γ₀, D.indicator (fun _ => w z) ((γ : Matrix.SpecialLinearGroup (Fin 2) ℝ)⁻¹ * γ1) :=
            ENNReal.tsum_le_tsum hle
        _ ≤ ∑' δ, D.indicator (fun _ => w z) δ := ENNReal.tsum_comp_le_tsum_of_injective hinj _
        _ = ∑ δ ∈ hDf.toFinset, D.indicator (fun _ => w z) δ :=
            tsum_eq_sum fun δ hδ => indicator_of_notMem (by simpa using hδ) _
        _ = ∑ δ ∈ hDf.toFinset, w z :=
            Finset.sum_congr rfl fun δ hδ => indicator_of_mem (by simpa using hδ) _
        _ = hDf.toFinset.card * w z := by rw [Finset.sum_const, nsmul_eq_mul]
    · push_neg at hA
      rw [ENNReal.tsum_eq_zero.mpr fun γ => indicator_of_notMem (hA γ) _]
      exact zero_le
  rw [← hw]
  calc ∫⁻ z in S, w z ≤ ∑' γ : Γ₀, ∫⁻ z in S ∩ T γ, w z := h1
    _ ≤ ∑' γ : Γ₀, ∫⁻ z in F₀, (E γ).indicator w z := ENNReal.tsum_le_tsum h2
    _ = ∫⁻ z in F₀, ∑' γ : Γ₀, (E γ).indicator w z :=
        (lintegral_tsum fun γ => (hwm.indicator (hEm γ)).aemeasurable).symm
    _ ≤ ∫⁻ z in F₀, hDf.toFinset.card * w z := lintegral_mono h3
    _ = hDf.toFinset.card * ∫⁻ z in F₀, w z := lintegral_const_mul _ hwm

/-- **Unfolding over a compact set.** For a compact `K ⊆ ℍ`, the integral of an invariant density over a measurable
`S` inside `K` is at most `N_K` times its integral over the covering set `F₀`; `N_K = #{γ ∈ Γ₀ | γ K ∩ K ≠ ∅}`. -/
theorem s13c_unfold {Γ₀ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} (hΓ₀ : LiZhongQC.IsFuchsian Γ₀)
    {F₀ : Set ℂ} (hF₀m : MeasurableSet F₀)
    (hcov₀ : ∀ᵐ z ∂(volume.restrict upperHalf), ∀ hz : 0 < z.im, ∃ M ∈ Γ₀,
      ((M • (⟨z, hz⟩ : UpperHalfPlane) : UpperHalfPlane) : ℂ) ∈ F₀)
    {K : Set UpperHalfPlane} (hK : IsCompact K) :
    ∃ N : ℕ, ∀ g : ℂ → ℝ≥0∞, Measurable g →
      (∀ γ ∈ Γ₀, ∀ τ : UpperHalfPlane, g ((γ • τ : UpperHalfPlane) : ℂ) = g τ) →
      ∀ S : Set ℂ, MeasurableSet S → S ⊆ ((↑) : UpperHalfPlane → ℂ) '' K →
        ∫⁻ z in S, g z * ENNReal.ofReal ((z.im ^ 2)⁻¹) ≤
          N * ∫⁻ z in F₀, g z * ENNReal.ofReal ((z.im ^ 2)⁻¹) := by
  obtain ⟨Δ, hΔ⟩ : ∃ Δ : Set (Matrix.SpecialLinearGroup (Fin 2) ℝ),
      Δ = {γ ∈ Γ₀ | ((γ • ·) '' K ∩ K).Nonempty} := ⟨_, rfl⟩
  have hΔf : Δ.Finite := by
    rw [hΔ]
    exact hΓ₀ K hK
  refine ⟨hΔf.toFinset.card, fun g hg hginv S hSm hSK => ?_⟩
  have hSH : S ⊆ upperHalf := by
    intro z hz
    obtain ⟨τ, _, rfl⟩ := hSK hz
    exact τ.im_pos
  refine s13c_unfold_gen hΓ₀ hF₀m hcov₀ hSm hSH hΔf ?_ hg hginv
  intro γ hγ σ hσ hγσ
  obtain ⟨σ', hσ'K, hσ'⟩ := hSK hσ
  obtain ⟨ρ, hρK, hρ⟩ := hSK hγσ
  have e1 : σ' = σ := UpperHalfPlane.ext hσ'
  have e2 : ρ = γ • σ := UpperHalfPlane.ext hρ
  rw [hΔ]
  exact ⟨hγ, γ • σ, ⟨σ, e1 ▸ hσ'K, rfl⟩, e2 ▸ hρK⟩

/-- **Thick part.** On a compact `K ⊆ ℍ`, `(y²|ψ|)²` is bounded by a constant times `∫_{F₀} (y²|ψ|)² y⁻²`, for every
holomorphic `ψ` with `Γ₀`-invariant `y² |ψ|` (area sub-mean value plus unfolding). -/
theorem s13c_thick {Γ₀ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} (hΓ₀ : LiZhongQC.IsFuchsian Γ₀)
    {F₀ : Set ℂ} (hF₀m : MeasurableSet F₀) (hF₀H : F₀ ⊆ upperHalf)
    (hcov₀ : ∀ᵐ z ∂(volume.restrict upperHalf), ∀ hz : 0 < z.im, ∃ M ∈ Γ₀,
      ((M • (⟨z, hz⟩ : UpperHalfPlane) : UpperHalfPlane) : ℂ) ∈ F₀)
    {K : Set UpperHalfPlane} (hK : IsCompact K) :
    ∃ c : ℝ≥0∞, c < ∞ ∧ ∀ ψ : ℂ → ℂ, DifferentiableOn ℂ ψ upperHalf →
      (∀ γ ∈ Γ₀, ∀ τ : UpperHalfPlane,
        (γ • τ).im ^ 2 * ‖ψ ((γ • τ : UpperHalfPlane) : ℂ)‖ = τ.im ^ 2 * ‖ψ τ‖) →
      ∀ τ ∈ K, ENNReal.ofReal ((τ.im ^ 2 * ‖ψ τ‖) ^ 2) ≤
        c * ∫⁻ z in F₀, ENNReal.ofReal ((z.im ^ 2 * ‖ψ z‖) ^ 2) * ENNReal.ofReal ((z.im ^ 2)⁻¹) := by
  rcases K.eq_empty_or_nonempty with hKe | hne
  · refine ⟨0, ENNReal.zero_lt_top, fun ψ _ _ τ hτ => ?_⟩
    rw [hKe] at hτ
    simp at hτ
  obtain ⟨τm, hτm, hmin⟩ := hK.exists_isMinOn hne UpperHalfPlane.continuous_im.continuousOn
  obtain ⟨τM, hτM, hmax⟩ := hK.exists_isMaxOn hne UpperHalfPlane.continuous_im.continuousOn
  set r : ℝ := τm.im / 2 with hr
  have hr0 : 0 < r := by
    have := τm.im_pos
    rw [hr]
    linarith
  set Y : ℝ := τM.im with hY
  have hKc : IsCompact (((↑) : UpperHalfPlane → ℂ) '' K) := hK.image UpperHalfPlane.continuous_coe
  set S : Set ℂ := cthickening r (((↑) : UpperHalfPlane → ℂ) '' K) with hS
  have hSc : IsCompact S := hKc.cthickening
  have hSim : ∀ z ∈ S, r ≤ z.im := by
    intro z hz
    rw [hS, hKc.cthickening_eq_biUnion_closedBall hr0.le] at hz
    obtain ⟨_, ⟨σ, hσ, rfl⟩, hzσ⟩ := mem_iUnion₂.mp hz
    have h1 : τm.im ≤ σ.im := hmin hσ
    have h2 : ‖z - (σ : ℂ)‖ ≤ r := by
      rw [← dist_eq_norm]
      exact mem_closedBall.mp hzσ
    have h3 := (Complex.abs_im_le_norm (z - σ)).trans h2
    rw [Complex.sub_im] at h3
    have h4 := (abs_le.mp h3).1
    have e : (σ : ℂ).im = σ.im := rfl
    linarith
  have hSH : ∀ z ∈ S, 0 < z.im := fun z hz => lt_of_lt_of_le hr0 (hSim z hz)
  have hK'c : IsCompact (((↑) : UpperHalfPlane → ℂ) ⁻¹' S) := by
    refine (UpperHalfPlane.isOpenEmbedding_coe.isInducing.isCompact_preimage_iff ?_).mpr hSc
    intro z hz
    exact ⟨⟨z, hSH z hz⟩, rfl⟩
  obtain ⟨N, hN⟩ := s13c_unfold hΓ₀ hF₀m hcov₀ hK'c
  refine ⟨ENNReal.ofReal (Y ^ 4 / (π * r ^ 2)) * (ENNReal.ofReal ((r ^ 2)⁻¹) * N), ?_, ?_⟩
  · exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (ENNReal.natCast_lt_top N))
  intro ψ hψd hψi τ hτ
  have hUH : IsOpen upperHalf := isOpen_lt continuous_const Complex.continuous_im
  obtain ⟨g, hg⟩ : ∃ g : ℂ → ℝ≥0∞,
      g = upperHalf.piecewise (fun z => ENNReal.ofReal ((z.im ^ 2 * ‖ψ z‖) ^ 2)) 0 := ⟨_, rfl⟩
  have hgH : ∀ z ∈ upperHalf, g z = ENNReal.ofReal ((z.im ^ 2 * ‖ψ z‖) ^ 2) := fun z hz => by
    rw [hg]
    exact Set.piecewise_eq_of_mem _ _ _ hz
  have hgm : Measurable g := by
    rw [hg]
    refine ContinuousOn.measurable_piecewise ?_ continuousOn_const hUH.measurableSet
    exact ENNReal.continuous_ofReal.comp_continuousOn
      (((Complex.continuous_im.continuousOn.pow 2).mul hψd.continuousOn.norm).pow 2)
  have hginv : ∀ γ ∈ Γ₀, ∀ σ : UpperHalfPlane, g ((γ • σ : UpperHalfPlane) : ℂ) = g σ := by
    intro γ hγ σ
    rw [hgH _ (γ • σ).im_pos, hgH _ σ.im_pos]
    exact congrArg (fun t => ENNReal.ofReal (t ^ 2)) (hψi γ hγ σ)
  have hτK : (τ : ℂ) ∈ ((↑) : UpperHalfPlane → ℂ) '' K := mem_image_of_mem _ hτ
  have hball : ball (τ : ℂ) r ⊆ S := ball_subset_closedBall.trans (closedBall_subset_cthickening hτK r)
  have hτm' : τm.im ≤ τ.im := hmin hτ
  have hτY : τ.im ≤ Y := hmax hτ
  have hcl : closedBall (τ : ℂ) r ⊆ upperHalf := by
    intro z hz
    have h2 : ‖z - (τ : ℂ)‖ ≤ r := by
      rw [← dist_eq_norm]
      exact mem_closedBall.mp hz
    have h3 := (Complex.abs_im_le_norm (z - τ)).trans h2
    rw [Complex.sub_im] at h3
    have h4 := (abs_le.mp h3).1
    have e : (τ : ℂ).im = τ.im := rfl
    show 0 < z.im
    linarith
  have hsm := LiZhongQC.s82dx_submean hr0 (f := fun z => ψ z ^ 2)
    ((hψd.pow 2).mono (closure_ball_subset_closedBall.trans hcl)).diffContOnCl
  simp only [norm_pow] at hsm
  have hint : ∫⁻ z in ball (τ : ℂ) r, ENNReal.ofReal (‖ψ z‖ ^ 2) ≤
      ENNReal.ofReal ((r ^ 2)⁻¹) * ∫⁻ z in ball (τ : ℂ) r, g z * ENNReal.ofReal ((z.im ^ 2)⁻¹) := by
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    apply lintegral_mono_ae
    filter_upwards [ae_restrict_mem measurableSet_ball] with z hz
    have hzH : 0 < z.im := hcl (ball_subset_closedBall hz)
    have hzr : r ≤ z.im := hSim z (hball hz)
    rw [hgH z hzH, ← ENNReal.ofReal_mul (sq_nonneg _), ← ENNReal.ofReal_mul (inv_nonneg.mpr (sq_nonneg r))]
    apply ENNReal.ofReal_le_ofReal
    have hy2 : r ^ 2 ≤ z.im ^ 2 := pow_le_pow_left₀ hr0.le hzr 2
    have hr2 : 0 < r ^ 2 := by positivity
    have hz2 : 0 < z.im ^ 2 := by positivity
    rw [show (r ^ 2)⁻¹ * ((z.im ^ 2 * ‖ψ z‖) ^ 2 * (z.im ^ 2)⁻¹) = (z.im ^ 2 / r ^ 2) * ‖ψ z‖ ^ 2 by
      field_simp
      try ring]
    exact le_mul_of_one_le_left (sq_nonneg _) ((one_le_div hr2).mpr hy2)
  have hS' : ∫⁻ z in ball (τ : ℂ) r, g z * ENNReal.ofReal ((z.im ^ 2)⁻¹) ≤
      N * ∫⁻ z in F₀, g z * ENNReal.ofReal ((z.im ^ 2)⁻¹) :=
    (lintegral_mono_set hball).trans (hN g hgm hginv S hSc.isClosed.measurableSet
      (fun z hz => ⟨⟨z, hSH z hz⟩, hz, rfl⟩))
  have hF : ∫⁻ z in F₀, g z * ENNReal.ofReal ((z.im ^ 2)⁻¹) =
      ∫⁻ z in F₀, ENNReal.ofReal ((z.im ^ 2 * ‖ψ z‖) ^ 2) * ENNReal.ofReal ((z.im ^ 2)⁻¹) :=
    setLIntegral_congr_fun hF₀m fun z hz => by rw [hgH z (hF₀H hz)]
  have hlhs : ENNReal.ofReal ((τ.im ^ 2 * ‖ψ τ‖) ^ 2) ≤
      ENNReal.ofReal (Y ^ 4 / (π * r ^ 2)) * ENNReal.ofReal (π * r ^ 2 * ‖ψ τ‖ ^ 2) := by
    rw [← ENNReal.ofReal_mul (show (0 : ℝ) ≤ Y ^ 4 / (π * r ^ 2) by positivity)]
    apply ENNReal.ofReal_le_ofReal
    have hπr : 0 < π * r ^ 2 := by positivity
    rw [show Y ^ 4 / (π * r ^ 2) * (π * r ^ 2 * ‖ψ τ‖ ^ 2) = Y ^ 4 * ‖ψ τ‖ ^ 2 by
      field_simp]
    have h0 : 0 ≤ τ.im := τ.im_pos.le
    have h4 : τ.im ^ 4 ≤ Y ^ 4 := pow_le_pow_left₀ h0 hτY 4
    nlinarith [sq_nonneg ‖ψ τ‖, mul_le_mul_of_nonneg_right h4 (sq_nonneg ‖ψ τ‖)]
  calc ENNReal.ofReal ((τ.im ^ 2 * ‖ψ τ‖) ^ 2)
      ≤ ENNReal.ofReal (Y ^ 4 / (π * r ^ 2)) * ENNReal.ofReal (π * r ^ 2 * ‖ψ τ‖ ^ 2) := hlhs
    _ ≤ ENNReal.ofReal (Y ^ 4 / (π * r ^ 2)) * (ENNReal.ofReal ((r ^ 2)⁻¹) *
          (N * ∫⁻ z in F₀, g z * ENNReal.ofReal ((z.im ^ 2)⁻¹))) := by
        gcongr
        exact hsm.trans (hint.trans (mul_le_mul_of_nonneg_left hS' zero_le))
    _ = _ := by
        rw [hF]
        ring

/-- **Cusp part.** In a cusp `A` with parabolic `π₁` (`π₁ A τ = A (τ + 1)`), the invariant norm `y² |ψ|` on the
horoball `Im ≥ 1` is bounded by its maximum on the horocycle segment `{Im = 1, |Re| ≤ 1/2}` (q-expansion and the
maximum principle for `F(q)/q`; `F(0) = 0` since `ψ` is bounded). -/
theorem s13c_cusp {A π₁ : Matrix.SpecialLinearGroup (Fin 2) ℝ}
    (hπ : ∀ τ : UpperHalfPlane, π₁ • (A • τ) = A • ((1 : ℝ) +ᵥ τ)) {ψ : ℂ → ℂ}
    (hψd : DifferentiableOn ℂ ψ upperHalf) {B : ℝ} (hB : ∀ z ∈ upperHalf, z.im ^ 2 * ‖ψ z‖ ≤ B)
    (hinv : ∀ τ : UpperHalfPlane,
      ψ ((π₁ • τ : UpperHalfPlane) : ℂ) * (((π₁ 1 0 : ℝ) : ℂ) * (τ : ℂ) + ((π₁ 1 1 : ℝ) : ℂ))⁻¹ ^ 4 = ψ τ)
    {M : ℝ} (hseg : ∀ u : UpperHalfPlane, u.im = 1 → |u.re| ≤ 1 / 2 →
      (A • u).im ^ 2 * ‖ψ ((A • u : UpperHalfPlane) : ℂ)‖ ≤ M)
    (u : UpperHalfPlane) (hu : 1 ≤ u.im) :
    (A • u).im ^ 2 * ‖ψ ((A • u : UpperHalfPlane) : ℂ)‖ ≤ M := by
  have hUH : IsOpen upperHalf := isOpen_lt continuous_const Complex.continuous_im
  obtain ⟨Ψ, hΨ⟩ : ∃ f : ℂ → ℂ, f = fun z => if 0 < z.im then
      ψ ((((A 0 0 : ℝ) : ℂ) * z + ((A 0 1 : ℝ) : ℂ)) / (((A 1 0 : ℝ) : ℂ) * z + ((A 1 1 : ℝ) : ℂ))) *
        (((A 1 0 : ℝ) : ℂ) * z + ((A 1 1 : ℝ) : ℂ))⁻¹ ^ 4 else 0 := ⟨_, rfl⟩
  have hΨH : ∀ (z : ℂ) (hz : 0 < z.im), Ψ z = ψ ((A • (⟨z, hz⟩ : UpperHalfPlane) : UpperHalfPlane) : ℂ) *
      (((A 1 0 : ℝ) : ℂ) * z + ((A 1 1 : ℝ) : ℂ))⁻¹ ^ 4 := by
    intro z hz
    rw [hΨ, s13c_smul_coe' A hz]
    exact if_pos hz
  have hnT : ∀ (z : ℂ) (hz : 0 < z.im), (A • (⟨z, hz⟩ : UpperHalfPlane)).im ^ 2 *
      ‖ψ ((A • (⟨z, hz⟩ : UpperHalfPlane) : UpperHalfPlane) : ℂ)‖ = z.im ^ 2 * ‖Ψ z‖ := by
    intro z hz
    rw [hΨH z hz]
    exact s13c_norm_transfer A ψ ⟨z, hz⟩
  -- periodicity
  have hper : Function.Periodic Ψ ((1 : ℝ) : ℂ) := by
    intro z
    rw [Complex.ofReal_one]
    by_cases hz : 0 < z.im
    · have hz1 : 0 < (z + 1).im := by simpa using hz
      rw [hΨH _ hz1, hΨH _ hz]
      have hvadd : (⟨z + 1, hz1⟩ : UpperHalfPlane) = (1 : ℝ) +ᵥ (⟨z, hz⟩ : UpperHalfPlane) := by
        apply UpperHalfPlane.ext
        rw [UpperHalfPlane.coe_vadd]
        push_cast
        ring
      rw [hvadd, ← hπ ⟨z, hz⟩]
      have hF1 : HasDerivAt (fun w : ℂ => (((A 0 0 : ℝ) : ℂ) * (w + 1) + ((A 0 1 : ℝ) : ℂ)) /
          (((A 1 0 : ℝ) : ℂ) * (w + 1) + ((A 1 1 : ℝ) : ℂ)))
          (1 / (((A 1 0 : ℝ) : ℂ) * (z + 1) + ((A 1 1 : ℝ) : ℂ)) ^ 2 * 1) z := by
        have h := (s13c_real_mob_hasDerivAt A ⟨z + 1, hz1⟩).comp z ((hasDerivAt_id' z).add_const 1)
        exact h
      have hπd := s13c_real_mob_hasDerivAt π₁ (A • (⟨z, hz⟩ : UpperHalfPlane))
      rw [s13c_smul_coe' A hz] at hπd
      have hF2 : HasDerivAt (fun w : ℂ => (((π₁ 0 0 : ℝ) : ℂ) *
          ((((A 0 0 : ℝ) : ℂ) * w + ((A 0 1 : ℝ) : ℂ)) / (((A 1 0 : ℝ) : ℂ) * w + ((A 1 1 : ℝ) : ℂ))) +
            ((π₁ 0 1 : ℝ) : ℂ)) / (((π₁ 1 0 : ℝ) : ℂ) *
          ((((A 0 0 : ℝ) : ℂ) * w + ((A 0 1 : ℝ) : ℂ)) / (((A 1 0 : ℝ) : ℂ) * w + ((A 1 1 : ℝ) : ℂ))) +
            ((π₁ 1 1 : ℝ) : ℂ)))
          (1 / (((π₁ 1 0 : ℝ) : ℂ) *
            ((((A 0 0 : ℝ) : ℂ) * z + ((A 0 1 : ℝ) : ℂ)) / (((A 1 0 : ℝ) : ℂ) * z + ((A 1 1 : ℝ) : ℂ))) +
              ((π₁ 1 1 : ℝ) : ℂ)) ^ 2 * (1 / (((A 1 0 : ℝ) : ℂ) * z + ((A 1 1 : ℝ) : ℂ)) ^ 2)) z := by
        have h := hπd.comp z (s13c_real_mob_hasDerivAt A ⟨z, hz⟩)
        exact h
      have heq : (fun w : ℂ => (((A 0 0 : ℝ) : ℂ) * (w + 1) + ((A 0 1 : ℝ) : ℂ)) /
          (((A 1 0 : ℝ) : ℂ) * (w + 1) + ((A 1 1 : ℝ) : ℂ))) =ᶠ[𝓝 z]
          (fun w : ℂ => (((π₁ 0 0 : ℝ) : ℂ) *
          ((((A 0 0 : ℝ) : ℂ) * w + ((A 0 1 : ℝ) : ℂ)) / (((A 1 0 : ℝ) : ℂ) * w + ((A 1 1 : ℝ) : ℂ))) +
            ((π₁ 0 1 : ℝ) : ℂ)) / (((π₁ 1 0 : ℝ) : ℂ) *
          ((((A 0 0 : ℝ) : ℂ) * w + ((A 0 1 : ℝ) : ℂ)) / (((A 1 0 : ℝ) : ℂ) * w + ((A 1 1 : ℝ) : ℂ))) +
            ((π₁ 1 1 : ℝ) : ℂ))) := by
        filter_upwards [hUH.mem_nhds hz] with w hw
        have h : (((π₁ 0 0 : ℝ) : ℂ) *
            ((((A 0 0 : ℝ) : ℂ) * w + ((A 0 1 : ℝ) : ℂ)) / (((A 1 0 : ℝ) : ℂ) * w + ((A 1 1 : ℝ) : ℂ))) +
              ((π₁ 0 1 : ℝ) : ℂ)) / (((π₁ 1 0 : ℝ) : ℂ) *
            ((((A 0 0 : ℝ) : ℂ) * w + ((A 0 1 : ℝ) : ℂ)) / (((A 1 0 : ℝ) : ℂ) * w + ((A 1 1 : ℝ) : ℂ))) +
              ((π₁ 1 1 : ℝ) : ℂ)) =
            (((A 0 0 : ℝ) : ℂ) * (((1 : ℝ) : ℂ) + w) + ((A 0 1 : ℝ) : ℂ)) /
              (((A 1 0 : ℝ) : ℂ) * (((1 : ℝ) : ℂ) + w) + ((A 1 1 : ℝ) : ℂ)) := by
          have h0 : ((π₁ • (A • (⟨w, hw⟩ : UpperHalfPlane)) : UpperHalfPlane) : ℂ) =
              ((A • ((1 : ℝ) +ᵥ (⟨w, hw⟩ : UpperHalfPlane)) : UpperHalfPlane) : ℂ) := by
            rw [hπ ⟨w, hw⟩]
          rw [s13c_smul_coe, s13c_smul_coe, s13c_smul_coe, UpperHalfPlane.coe_vadd] at h0
          exact h0
        rw [Complex.ofReal_one, add_comm (1 : ℂ) w] at h
        exact h.symm
      have hd := (hF1.congr_of_eventuallyEq heq.symm).unique hF2
      rw [← s13c_smul_coe' A hz] at hd
      have hi := hinv (A • (⟨z, hz⟩ : UpperHalfPlane))
      generalize ((A 1 0 : ℝ) : ℂ) * (z + 1) + ((A 1 1 : ℝ) : ℂ) = a at hd ⊢
      generalize ((A 1 0 : ℝ) : ℂ) * z + ((A 1 1 : ℝ) : ℂ) = b at hd ⊢
      generalize ((π₁ 1 0 : ℝ) : ℂ) * ((A • (⟨z, hz⟩ : UpperHalfPlane) : UpperHalfPlane) : ℂ) +
        ((π₁ 1 1 : ℝ) : ℂ) = p at hd hi
      linear_combination (ψ ((π₁ • A • (⟨z, hz⟩ : UpperHalfPlane) : UpperHalfPlane) : ℂ) *
        (1 / a ^ 2 + 1 / p ^ 2 * (1 / b ^ 2))) * hd + b⁻¹ ^ 4 * hi
    · have hz1 : ¬ 0 < (z + 1).im := by simpa using hz
      rw [hΨ]
      simp only [if_neg hz, if_neg hz1]
  -- holomorphy and decay
  have hΨd : ∀ z : ℂ, 0 < z.im → DifferentiableAt ℂ Ψ z := by
    intro z hz
    have hD := s13c_den_ne A ⟨z, hz⟩
    have hfA := (s13c_real_mob_hasDerivAt A ⟨z, hz⟩).differentiableAt
    have hψa : DifferentiableAt ℂ ψ ((((A 0 0 : ℝ) : ℂ) * z + ((A 0 1 : ℝ) : ℂ)) /
        (((A 1 0 : ℝ) : ℂ) * z + ((A 1 1 : ℝ) : ℂ))) :=
      hψd.differentiableAt (hUH.mem_nhds (s13c_mobR_im_pos A hz))
    have hq : DifferentiableAt ℂ (fun w : ℂ => (((A 1 0 : ℝ) : ℂ) * w + ((A 1 1 : ℝ) : ℂ))⁻¹ ^ 4) z := by
      fun_prop (disch := exact hD)
    have heq : Ψ =ᶠ[𝓝 z] fun w => ψ ((((A 0 0 : ℝ) : ℂ) * w + ((A 0 1 : ℝ) : ℂ)) /
        (((A 1 0 : ℝ) : ℂ) * w + ((A 1 1 : ℝ) : ℂ))) * (((A 1 0 : ℝ) : ℂ) * w + ((A 1 1 : ℝ) : ℂ))⁻¹ ^ 4 := by
      filter_upwards [hUH.mem_nhds hz] with w hw
      rw [hΨ]
      exact if_pos hw
    exact ((hψa.comp z hfA).mul hq).congr_of_eventuallyEq heq
  have hΨb : ∀ z : ℂ, 0 < z.im → z.im ^ 2 * ‖Ψ z‖ ≤ B := by
    intro z hz
    rw [← hnT z hz]
    exact hB _ (A • (⟨z, hz⟩ : UpperHalfPlane)).im_pos
  have hev : ∀ᶠ z in comap Complex.im atTop, 0 < z.im :=
    tendsto_comap.eventually (eventually_gt_atTop 0)
  have hzero : (comap Complex.im atTop).ZeroAtFilter Ψ := by
    have hT : Tendsto (fun z : ℂ => B / z.im ^ 2) (comap Complex.im atTop) (𝓝 0) :=
      tendsto_const_nhds.div_atTop ((tendsto_pow_atTop two_ne_zero).comp tendsto_comap)
    refine squeeze_zero_norm' ?_ hT
    filter_upwards [hev] with z hz
    rw [le_div_iff₀ (pow_pos hz 2), mul_comm]
    exact hΨb z hz
  -- the q-expansion `F` and `G = F/q`
  set F : ℂ → ℂ := Function.Periodic.cuspFunction 1 Ψ with hFdef
  have hF0 : F 0 = 0 := Function.Periodic.cuspFunction_zero_of_zero_at_inf one_pos hzero
  have hFd : DifferentiableOn ℂ F (ball 0 1) := by
    intro q hq
    by_cases hq0 : q = 0
    · rw [hq0]
      exact (Function.Periodic.differentiableAt_cuspFunction_zero one_pos hper
        (hev.mono fun z hz => hΨd z hz) hzero.boundedAtFilter).differentiableWithinAt
    · have hq1 : ‖q‖ < 1 := mem_ball_zero_iff.mp hq
      have hzim : 0 < (Function.Periodic.invQParam 1 q).im := by
        rw [Function.Periodic.im_invQParam]
        have hlog : Real.log ‖q‖ < 0 := Real.log_neg (norm_pos_iff.mpr hq0) hq1
        have h1 : -(1 : ℝ) / (2 * π) < 0 := by
          have := Real.pi_pos
          apply div_neg_of_neg_of_pos <;> linarith
        exact mul_pos_of_neg_of_neg h1 hlog
      have h := Function.Periodic.differentiableAt_cuspFunction one_ne_zero hper (hΨd _ hzim)
      rw [Function.Periodic.qParam_right_inv one_ne_zero hq0] at h
      exact h.differentiableWithinAt
  set G : ℂ → ℂ := dslope F 0 with hGdef
  have hGd : DifferentiableOn ℂ G (ball 0 1) :=
    (differentiableOn_dslope (ball_mem_nhds 0 one_pos)).mpr hFd
  have hFG : ∀ q, F q = q * G q := by
    intro q
    have h := sub_smul_dslope F 0 q
    rw [hF0, sub_zero, sub_zero, smul_eq_mul] at h
    exact h.symm
  set r0 : ℝ := Real.exp (-2 * π) with hr0def
  have hr0 : 0 < r0 := Real.exp_pos _
  have hr01 : r0 < 1 := by
    rw [hr0def, ← Real.exp_zero]
    exact Real.exp_lt_exp.mpr (by linarith [Real.pi_pos])
  -- maximum principle for `G` on `|q| ≤ r₀`
  have hGb : ∀ q ∈ closedBall (0 : ℂ) r0, ‖G q‖ ≤ M / r0 := by
    intro q hq
    have hsub : closedBall (0 : ℂ) r0 ⊆ ball 0 1 := closedBall_subset_ball hr01
    refine Complex.norm_le_of_forall_mem_frontier_norm_le isBounded_ball
      (hGd.mono (by rw [closure_ball (0 : ℂ) hr0.ne']; exact hsub)).diffContOnCl ?_
      (by rw [closure_ball (0 : ℂ) hr0.ne']; exact hq)
    intro q' hq'
    rw [frontier_ball (0 : ℂ) hr0.ne'] at hq'
    have hn : ‖q'‖ = r0 := mem_sphere_zero_iff_norm.mp hq'
    have hq0 : q' ≠ 0 := by
      intro h
      rw [h, norm_zero] at hn
      linarith
    set z := Function.Periodic.invQParam 1 q' with hz
    have hzim : z.im = 1 := by
      rw [hz, Function.Periodic.im_invQParam, hn, hr0def, Real.log_exp]
      field_simp
    have hzre : |z.re| ≤ 1 / 2 := by
      have hne : (2 * (π : ℂ) * I) ≠ 0 := by simp [Real.pi_ne_zero, I_ne_zero]
      have h2 : 2 * (π : ℂ) * I * z = Complex.log q' := by
        rw [hz, Function.Periodic.invQParam, Complex.ofReal_one, ← mul_assoc, mul_one_div_cancel hne, one_mul]
      have h3 := congrArg Complex.im h2
      simp only [Complex.mul_im, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re,
        Complex.ofReal_im, Complex.re_ofNat, Complex.im_ofNat, Complex.log_im] at h3
      have h4 := Complex.neg_pi_lt_arg q'
      have h5 := Complex.arg_le_pi q'
      have hπ0 := Real.pi_pos
      rw [abs_le]
      constructor <;> nlinarith
    have hzpos : 0 < z.im := by
      rw [hzim]
      norm_num
    have hFq : F q' = Ψ z := by
      calc F q' = F (Function.Periodic.qParam 1 z) := by
            rw [hz, Function.Periodic.qParam_right_inv one_ne_zero hq0]
        _ = Ψ z := Function.Periodic.eq_cuspFunction one_ne_zero hper z
    have hval : ‖F q'‖ ≤ M := by
      rw [hFq]
      have h := hseg ⟨z, hzpos⟩ hzim hzre
      rw [hnT z hzpos, hzim, one_pow, one_mul] at h
      exact h
    rw [hFG q', norm_mul, hn] at hval
    rw [le_div_iff₀ hr0, mul_comm]
    exact hval
  -- conclusion at `u`
  have hmain : (A • u).im ^ 2 * ‖ψ ((A • u : UpperHalfPlane) : ℂ)‖ = (u : ℂ).im ^ 2 * ‖Ψ u‖ :=
    hnT (u : ℂ) u.im_pos
  rw [hmain]
  have hqn := Function.Periodic.norm_qParam 1 (u : ℂ)
  set q := Function.Periodic.qParam 1 (u : ℂ) with hqdef
  have hy1 : 1 ≤ (u : ℂ).im := hu
  set y := (u : ℂ).im with hydef
  have hqr : ‖q‖ ≤ r0 := by
    rw [hqn, hr0def, div_one]
    apply Real.exp_le_exp.mpr
    nlinarith [Real.pi_pos]
  have hFu : F q = Ψ u := Function.Periodic.eq_cuspFunction one_ne_zero hper u
  have hΨu : ‖Ψ u‖ ≤ ‖q‖ * (M / r0) := by
    rw [← hFu, hFG q, norm_mul]
    exact mul_le_mul_of_nonneg_left (hGb q (mem_closedBall_zero_iff.mpr hqr)) (norm_nonneg _)
  have hM0 : 0 ≤ M := by
    have h := hseg UpperHalfPlane.I (by simp) (by simp)
    exact le_trans (by positivity) h
  have h1 : y ≤ Real.exp (π * (y - 1)) := by
    have h := Real.add_one_le_exp (π * (y - 1))
    nlinarith [Real.pi_gt_three]
  have h2 : y ^ 2 ≤ Real.exp (π * (y - 1)) ^ 2 := pow_le_pow_left₀ (by linarith) h1 2
  have h3 : Real.exp (π * (y - 1)) ^ 2 * Real.exp (-2 * π * y) = r0 := by
    rw [sq, ← Real.exp_add, ← Real.exp_add, hr0def]
    congr 1
    ring
  have h4 : y ^ 2 * Real.exp (-2 * π * y) ≤ r0 := by
    rw [← h3]
    exact mul_le_mul_of_nonneg_right h2 (Real.exp_pos _).le
  calc y ^ 2 * ‖Ψ u‖ ≤ y ^ 2 * (‖q‖ * (M / r0)) := mul_le_mul_of_nonneg_left hΨu (sq_nonneg _)
    _ = y ^ 2 * Real.exp (-2 * π * y) * M / r0 := by
        rw [hqn, div_one]
        ring
    _ ≤ r0 * M / r0 := by gcongr
    _ = M := by field_simp

/-- The image of `S ⊆ ℍ` under a real Möbius map, as a preimage. -/
theorem s13c_image_eq (M : Matrix.SpecialLinearGroup (Fin 2) ℝ) {S : Set ℂ} (hSH : S ⊆ upperHalf) :
    (fun z : ℂ => (((M 0 0 : ℝ) : ℂ) * z + ((M 0 1 : ℝ) : ℂ)) / (((M 1 0 : ℝ) : ℂ) * z + ((M 1 1 : ℝ) : ℂ))) '' S =
      {z : ℂ | 0 < z.im ∧
        ((((M⁻¹ : Matrix.SpecialLinearGroup (Fin 2) ℝ) 0 0 : ℝ) : ℂ) * z +
          (((M⁻¹ : Matrix.SpecialLinearGroup (Fin 2) ℝ) 0 1 : ℝ) : ℂ)) /
        ((((M⁻¹ : Matrix.SpecialLinearGroup (Fin 2) ℝ) 1 0 : ℝ) : ℂ) * z +
          (((M⁻¹ : Matrix.SpecialLinearGroup (Fin 2) ℝ) 1 1 : ℝ) : ℂ)) ∈ S} := by
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact ⟨s13c_mobR_im_pos M (hSH hw), by rw [s13c_mobR_inv M (hSH hw)]; exact hw⟩
  · rintro ⟨hz, hzS⟩
    refine ⟨_, hzS, ?_⟩
    have h := s13c_mobR_inv M⁻¹ hz
    rw [inv_inv] at h
    exact h

/-- Membership of a point of `ℍ` in the preimage form of `M(Q)`. -/
theorem s13c_conj_mem (M : Matrix.SpecialLinearGroup (Fin 2) ℝ) (Q : Set ℂ) (σ : UpperHalfPlane) :
    (σ : ℂ) ∈ {z : ℂ | 0 < z.im ∧
        ((((M⁻¹ : Matrix.SpecialLinearGroup (Fin 2) ℝ) 0 0 : ℝ) : ℂ) * z +
          (((M⁻¹ : Matrix.SpecialLinearGroup (Fin 2) ℝ) 0 1 : ℝ) : ℂ)) /
        ((((M⁻¹ : Matrix.SpecialLinearGroup (Fin 2) ℝ) 1 0 : ℝ) : ℂ) * z +
          (((M⁻¹ : Matrix.SpecialLinearGroup (Fin 2) ℝ) 1 1 : ℝ) : ℂ)) ∈ Q} ↔
      ((M⁻¹ • σ : UpperHalfPlane) : ℂ) ∈ Q := by
  rw [s13c_smul_coe]
  exact ⟨fun h => h.2, fun h => ⟨σ.im_pos, h⟩⟩

/-- The preimage form of `M(Q)` is measurable and lies in `ℍ`, and its area is the area of `Q`. -/
theorem s13c_conj_set {M : Matrix.SpecialLinearGroup (Fin 2) ℝ} {Q : Set ℂ} (hQm : MeasurableSet Q)
    (hQH : Q ⊆ upperHalf) :
    MeasurableSet {z : ℂ | 0 < z.im ∧
        ((((M⁻¹ : Matrix.SpecialLinearGroup (Fin 2) ℝ) 0 0 : ℝ) : ℂ) * z +
          (((M⁻¹ : Matrix.SpecialLinearGroup (Fin 2) ℝ) 0 1 : ℝ) : ℂ)) /
        ((((M⁻¹ : Matrix.SpecialLinearGroup (Fin 2) ℝ) 1 0 : ℝ) : ℂ) * z +
          (((M⁻¹ : Matrix.SpecialLinearGroup (Fin 2) ℝ) 1 1 : ℝ) : ℂ)) ∈ Q} ∧
      {z : ℂ | 0 < z.im ∧
        ((((M⁻¹ : Matrix.SpecialLinearGroup (Fin 2) ℝ) 0 0 : ℝ) : ℂ) * z +
          (((M⁻¹ : Matrix.SpecialLinearGroup (Fin 2) ℝ) 0 1 : ℝ) : ℂ)) /
        ((((M⁻¹ : Matrix.SpecialLinearGroup (Fin 2) ℝ) 1 0 : ℝ) : ℂ) * z +
          (((M⁻¹ : Matrix.SpecialLinearGroup (Fin 2) ℝ) 1 1 : ℝ) : ℂ)) ∈ Q} ⊆ upperHalf ∧
      ∫⁻ z in {z : ℂ | 0 < z.im ∧
        ((((M⁻¹ : Matrix.SpecialLinearGroup (Fin 2) ℝ) 0 0 : ℝ) : ℂ) * z +
          (((M⁻¹ : Matrix.SpecialLinearGroup (Fin 2) ℝ) 0 1 : ℝ) : ℂ)) /
        ((((M⁻¹ : Matrix.SpecialLinearGroup (Fin 2) ℝ) 1 0 : ℝ) : ℂ) * z +
          (((M⁻¹ : Matrix.SpecialLinearGroup (Fin 2) ℝ) 1 1 : ℝ) : ℂ)) ∈ Q},
          ENNReal.ofReal ((z.im ^ 2)⁻¹) = ∫⁻ z in Q, ENNReal.ofReal ((z.im ^ 2)⁻¹) := by
  refine ⟨(measurableSet_lt measurable_const Complex.measurable_im).inter (by
    exact (show Measurable fun z : ℂ =>
      ((((M⁻¹ : Matrix.SpecialLinearGroup (Fin 2) ℝ) 0 0 : ℝ) : ℂ) * z +
          (((M⁻¹ : Matrix.SpecialLinearGroup (Fin 2) ℝ) 0 1 : ℝ) : ℂ)) /
        ((((M⁻¹ : Matrix.SpecialLinearGroup (Fin 2) ℝ) 1 0 : ℝ) : ℂ) * z +
          (((M⁻¹ : Matrix.SpecialLinearGroup (Fin 2) ℝ) 1 1 : ℝ) : ℂ)) by fun_prop) hQm),
    fun z hz => hz.1, ?_⟩
  rw [← s13c_image_eq M hQH]
  have h := s13c_hyp_cov M hQm hQH (fun _ => 1)
  simp only [one_mul] at h
  exact h

/-- A Euclidean rectangle `[a, b) × (0, c)` has infinite hyperbolic area. -/
theorem s13c_rect_area {a b c : ℝ} (hab : a < b) (hc : 0 < c) :
    MeasurableSet {z : ℂ | a ≤ z.re ∧ z.re < b ∧ 0 < z.im ∧ z.im < c} ∧
      {z : ℂ | a ≤ z.re ∧ z.re < b ∧ 0 < z.im ∧ z.im < c} ⊆ upperHalf ∧
      ∫⁻ z in {z : ℂ | a ≤ z.re ∧ z.re < b ∧ 0 < z.im ∧ z.im < c}, ENNReal.ofReal ((z.im ^ 2)⁻¹) = ∞ := by
  refine ⟨(measurableSet_le measurable_const Complex.measurable_re).inter
    ((measurableSet_lt Complex.measurable_re measurable_const).inter
      ((measurableSet_lt measurable_const Complex.measurable_im).inter
        (measurableSet_lt Complex.measurable_im measurable_const))), fun z hz => hz.2.2.1, ?_⟩
  have hy : ∫⁻ y in Ioo (0 : ℝ) c, ENNReal.ofReal ((y ^ 2)⁻¹) = ∞ := by
    by_contra hne
    have hint : IntegrableOn (fun y : ℝ => y ^ (-2 : ℝ)) (Ioo 0 c) := by
      refine ⟨(measurable_id.pow_const _).aestronglyMeasurable, ?_⟩
      rw [hasFiniteIntegral_iff_ofReal ((ae_restrict_iff' measurableSet_Ioo).mpr
        (Eventually.of_forall fun y hy => Real.rpow_nonneg hy.1.le _))]
      have heq : ∫⁻ y in Ioo (0 : ℝ) c, ENNReal.ofReal (y ^ (-2 : ℝ)) =
          ∫⁻ y in Ioo (0 : ℝ) c, ENNReal.ofReal ((y ^ 2)⁻¹) :=
        setLIntegral_congr_fun measurableSet_Ioo fun y hy => by
          rw [Real.rpow_neg hy.1.le, Real.rpow_two]
      rw [heq]
      exact lt_top_iff_ne_top.mpr hne
    have := (intervalIntegral.integrableOn_Ioo_rpow_iff hc).mp hint
    norm_num at this
  have hemb := Complex.measurableEquivRealProd.measurableEmbedding
  have h := Complex.volume_preserving_equiv_real_prod.setLIntegral_comp_preimage_emb hemb
    (fun p : ℝ × ℝ => ENNReal.ofReal ((p.2 ^ 2)⁻¹)) (Ico a b ×ˢ Ioo 0 c)
  have hpre : Complex.measurableEquivRealProd ⁻¹' (Ico a b ×ˢ Ioo 0 c) =
      {z : ℂ | a ≤ z.re ∧ z.re < b ∧ 0 < z.im ∧ z.im < c} := by
    ext z
    simp [Complex.measurableEquivRealProd_apply, and_assoc]
  rw [hpre] at h
  simp only [Complex.measurableEquivRealProd_apply] at h
  rw [h, Measure.volume_eq_prod, ← Measure.prod_restrict,
    show (fun p : ℝ × ℝ => ENNReal.ofReal ((p.2 ^ 2)⁻¹)) =
      fun p => (fun _ : ℝ => (1 : ℝ≥0∞)) p.1 * (fun y : ℝ => ENNReal.ofReal ((y ^ 2)⁻¹)) p.2 by
      funext p
      simp,
    lintegral_prod_mul (f := fun _ : ℝ => (1 : ℝ≥0∞)) (g := fun y : ℝ => ENNReal.ofReal ((y ^ 2)⁻¹))
      aemeasurable_const ((ENNReal.measurable_ofReal.comp (by fun_prop)).aemeasurable), hy]
  simp only [lintegral_const, Measure.restrict_apply MeasurableSet.univ, univ_inter, Real.volume_Ico, one_mul]
  exact ENNReal.mul_top (by simp [hab])

/-- **No infinite-area precisely invariant set.** A measurable `S ⊆ ℍ` of infinite hyperbolic area cannot be
precisely invariant modulo `±1` under a group with a finite-area covering set. -/
theorem s13c_no_inf {Γ₀ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} (hΓ₀ : LiZhongQC.IsFuchsian Γ₀)
    {F₀ : Set ℂ} (hF₀m : MeasurableSet F₀)
    (hcov₀ : ∀ᵐ z ∂(volume.restrict upperHalf), ∀ hz : 0 < z.im, ∃ M ∈ Γ₀,
      ((M • (⟨z, hz⟩ : UpperHalfPlane) : UpperHalfPlane) : ℂ) ∈ F₀)
    (harea : ∫⁻ z in F₀, ENNReal.ofReal ((z.im ^ 2)⁻¹) < ∞)
    {S : Set ℂ} (hSm : MeasurableSet S) (hSH : S ⊆ upperHalf)
    (hS : ∫⁻ z in S, ENNReal.ofReal ((z.im ^ 2)⁻¹) = ∞)
    (hD : ∀ γ ∈ Γ₀, ∀ σ : UpperHalfPlane, (σ : ℂ) ∈ S → ((γ • σ : UpperHalfPlane) : ℂ) ∈ S →
      γ = 1 ∨ γ = -1) : False := by
  have hDf : ({1, -1} : Set (Matrix.SpecialLinearGroup (Fin 2) ℝ)).Finite :=
    (Set.finite_singleton _).insert _
  have h := s13c_unfold_gen hΓ₀ hF₀m hcov₀ hSm hSH hDf
    (fun γ hγ σ h1 h2 => by rcases hD γ hγ σ h1 h2 with h | h <;> simp [h])
    (g := fun _ => 1) measurable_const (fun _ _ _ => rfl)
  simp only [one_mul] at h
  rw [hS] at h
  exact absurd (lt_of_le_of_lt h (ENNReal.mul_lt_top (ENNReal.natCast_lt_top _) harea)) (lt_irrefl _)

/-- `-M` acts on `ℍ` as `M`. -/
theorem s13c_neg_smul (M : Matrix.SpecialLinearGroup (Fin 2) ℝ) (τ : UpperHalfPlane) : (-M) • τ = M • τ := by
  apply UpperHalfPlane.ext
  rw [s13c_smul_coe, s13c_smul_coe]
  simp only [Matrix.SpecialLinearGroup.coe_neg, Matrix.neg_apply, Complex.ofReal_neg, neg_mul]
  rw [← neg_add, ← neg_add, neg_div_neg_eq]

/-- Powers of a parabolic element conjugate to `τ ↦ τ + 1`. -/
theorem s13c_par_iter {A π₀ : Matrix.SpecialLinearGroup (Fin 2) ℝ}
    (hπ : ∀ τ : UpperHalfPlane, π₀ • (A • τ) = A • ((1 : ℝ) +ᵥ τ)) :
    ∀ (k : ℤ) (τ : UpperHalfPlane), π₀ ^ k • (A • τ) = A • ((k : ℝ) +ᵥ τ) := by
  intro k
  induction k using Int.induction_on with
  | zero =>
    intro τ
    simp
  | succ k ih =>
    intro τ
    rw [zpow_add_one, mul_smul, hπ, ih, vadd_vadd]
    congr 2
    push_cast
    ring
  | pred k ih =>
    intro τ
    have h1 : π₀⁻¹ • (A • τ) = A • ((-1 : ℝ) +ᵥ τ) := by
      rw [inv_smul_eq_iff, hπ, vadd_vadd]
      norm_num
    rw [zpow_sub_one, mul_smul, h1, ih, vadd_vadd]
    congr 2
    push_cast
    ring

/-- Powers of a hyperbolic element conjugate to `τ ↦ λ τ`. -/
theorem s13c_hyp_iter {B h : Matrix.SpecialLinearGroup (Fin 2) ℝ} {lam : ℝ} (hl : 0 < lam)
    (hf : ∀ τ : UpperHalfPlane, ((B⁻¹ • (h • (B • τ)) : UpperHalfPlane) : ℂ) = (lam : ℂ) * (τ : ℂ)) :
    ∀ (k : ℤ) (τ : UpperHalfPlane),
      ((B⁻¹ • (h ^ k • (B • τ)) : UpperHalfPlane) : ℂ) = ((lam ^ k : ℝ) : ℂ) * (τ : ℂ) := by
  intro k
  induction k using Int.induction_on with
  | zero =>
    intro τ
    simp
  | succ k ih =>
    intro τ
    have e : h • (B • τ) = B • (B⁻¹ • (h • (B • τ))) := (smul_inv_smul B _).symm
    rw [zpow_add_one, mul_smul, e, ih, hf, zpow_add_one₀ hl.ne', Complex.ofReal_mul]
    ring
  | pred k ih =>
    intro τ
    have e : h⁻¹ • (B • τ) = B • (B⁻¹ • (h⁻¹ • (B • τ))) := (smul_inv_smul B _).symm
    have hρ : ((B⁻¹ • (h⁻¹ • (B • τ)) : UpperHalfPlane) : ℂ) = ((lam⁻¹ : ℝ) : ℂ) * (τ : ℂ) := by
      have h0 := hf (B⁻¹ • (h⁻¹ • (B • τ)))
      rw [smul_inv_smul, smul_inv_smul, inv_smul_smul] at h0
      rw [h0, ← mul_assoc, ← Complex.ofReal_mul, inv_mul_cancel₀ hl.ne', Complex.ofReal_one, one_mul]
    rw [zpow_sub_one, mul_smul, e, ih, hρ, ← mul_assoc, ← Complex.ofReal_mul, ← zpow_sub_one₀ hl.ne']

/-- Points with `Re ≥ 1` and `0 < Im < tan (θ/2)` lie in the sector `arg < θ`. -/
theorem s13c_arg_lt {θ : ℝ} (hθ0 : 0 < θ) (hθπ : θ < π) {z : ℂ} (hre : 1 ≤ z.re) (him : 0 < z.im)
    (himt : z.im < Real.tan (θ / 2)) : z.arg < θ := by
  have hre0 : 0 < z.re := by linarith
  have harg := abs_lt.mp (Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hre0))
  have hθ2 : θ / 2 ∈ Ioo (-(π / 2)) (π / 2) := ⟨by linarith, by linarith⟩
  have htan : Real.tan z.arg < Real.tan (θ / 2) := by
    rw [Complex.tan_arg]
    calc z.im / z.re ≤ z.im := div_le_self him.le hre
      _ < Real.tan (θ / 2) := himt
  have := (Real.strictMonoOn_tan.lt_iff_lt ⟨harg.1, harg.2⟩ hθ2).mp htan
  linarith

/-- The pairing of a finite combination, first slot. -/
theorem s13c_sum_left {Γ : Subgroup SL2C} (hΓ : IsCofinite Γ) (s : Finset ℕ) (c : ℕ → ℂ)
    (e : ℕ → LinfStar) (ν : LinfStar) :
    wpInnerGamma Γ (∑ i ∈ s, c i • e i) ν = ∑ i ∈ s, c i * wpInnerGamma Γ (e i) ν := by
  induction s using Finset.induction_on with
  | empty =>
    have h0 := wpInnerGamma_smul_left Γ 0 0 ν
    simpa using h0
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, wpInnerGamma_add_left hΓ, wpInnerGamma_smul_left, ih, Finset.sum_insert ha]

/-- The pairing of a finite combination, second slot. -/
theorem s13c_sum_right {Γ : Subgroup SL2C} (hΓ : IsCofinite Γ) (s : Finset ℕ) (c : ℕ → ℂ)
    (e : ℕ → LinfStar) (ν : LinfStar) :
    wpInnerGamma Γ ν (∑ i ∈ s, c i • e i) = ∑ i ∈ s, conj (c i) * wpInnerGamma Γ ν (e i) := by
  rw [wpInnerGamma_conj_symm Γ _ ν, s13c_sum_left hΓ, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, ← wpInnerGamma_conj_symm]

/-- Pointwise values of a finite combination. -/
theorem s13c_coeFn_sum (s : Finset ℕ) (c : ℕ → ℂ) (e : ℕ → LinfStar) :
    ∀ᵐ w ∂(volume.restrict unitDiscExterior), (∑ i ∈ s, c i • e i : LinfStar) w = ∑ i ∈ s, c i * e i w := by
  induction s using Finset.induction_on with
  | empty =>
    filter_upwards [Lp.coeFn_zero ℂ ∞ (volume.restrict unitDiscExterior)] with w hw
    simpa using hw
  | insert a s ha ih =>
    filter_upwards [ih, Lp.coeFn_add (c a • e a) (∑ i ∈ s, c i • e i), Lp.coeFn_smul (c a) (e a)]
      with w h1 h2 h3
    rw [Finset.sum_insert ha, h2, Pi.add_apply, h1, h3, Finset.sum_insert ha, Pi.smul_apply, smul_eq_mul]

/-- The ENNReal sup bound in real form. -/
theorem s13c_sup_real {Γ : Subgroup SL2C} (hΓ : IsCofinite Γ) {K : ℝ≥0∞} (hK : K < ∞) {μ : LinfStar}
    (hμ : ∀ᵐ w ∂(volume.restrict unitDiscExterior), (‖μ w‖₊ : ℝ≥0∞) ^ 2 ≤
      K * ∫⁻ z in fundDomain Γ, (‖μ z‖₊ : ℝ≥0∞) ^ 2 * ENNReal.ofReal (rho z)) :
    ∀ᵐ w ∂(volume.restrict unitDiscExterior), ‖μ w‖ ^ 2 ≤ K.toReal * (wpInnerGamma Γ μ μ).re := by
  have hint : IntegrableOn (fun z => ‖μ z‖ ^ 2 * rho z) (fundDomain Γ) := by
    have h := (wpInnerGamma_integrable hΓ μ μ).re
    refine h.congr (Filter.Eventually.of_forall fun z => ?_)
    simp only [Complex.mul_conj', ← Complex.ofReal_pow, ← Complex.ofReal_mul, Complex.ofReal_re, RCLike.ofReal_re]
    exact Complex.ofReal_re _
  have hn : ∀ z, 0 ≤ ‖μ z‖ ^ 2 * rho z := fun z =>
    mul_nonneg (sq_nonneg _) (div_nonneg (by norm_num) (sq_nonneg _))
  have hL : ∫⁻ z in fundDomain Γ, (‖μ z‖₊ : ℝ≥0∞) ^ 2 * ENNReal.ofReal (rho z) =
      ENNReal.ofReal (wpInnerGamma Γ μ μ).re := by
    rw [wpInnerGamma_self_eq, Complex.ofReal_re,
      ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall hn)]
    refine lintegral_congr fun z => ?_
    rw [ENNReal.ofReal_mul (sq_nonneg _), ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm_eq_enorm]
    rfl
  filter_upwards [hμ] with w hw
  rw [hL] at hw
  have hK' : K ≠ ∞ := hK.ne
  have h1 := ENNReal.toReal_mono (ENNReal.mul_ne_top hK' ENNReal.ofReal_ne_top) hw
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (wpInnerGamma_self_nonneg Γ μ), ENNReal.toReal_pow,
    ENNReal.coe_toReal, coe_nnnorm] at h1
  exact h1

/-- Orthonormal families of every length in an infinite-dimensional span (Gram–Schmidt). -/
theorem s13c_orthonormal {Γ : Subgroup SL2C} (hΓ : IsCofinite Γ) {K : ℝ≥0∞} (hK : K < ∞)
    (hsup : ∀ μ ∈ Submodule.span ℂ (harmonicGamma Γ),
      ∀ᵐ w ∂(volume.restrict unitDiscExterior), (‖μ w‖₊ : ℝ≥0∞) ^ 2 ≤
        K * ∫⁻ z in fundDomain Γ, (‖μ z‖₊ : ℝ≥0∞) ^ 2 * ENNReal.ofReal (rho z))
    (hinf : ¬ FiniteDimensional ℂ (Submodule.span ℂ (harmonicGamma Γ))) (m : ℕ) :
    ∃ e : ℕ → LinfStar, (∀ i < m, e i ∈ Submodule.span ℂ (harmonicGamma Γ)) ∧
      ∀ i < m, ∀ j < m, wpInnerGamma Γ (e i) (e j) = if i = j then 1 else 0 := by
  set V := Submodule.span ℂ (harmonicGamma Γ) with hV
  -- definiteness on `V`
  have hdef : ∀ μ ∈ V, (wpInnerGamma Γ μ μ).re = 0 → μ = 0 := by
    intro μ hμ h0
    have h1 := s13c_sup_real hΓ hK (hsup μ hμ)
    rw [h0, mul_zero] at h1
    apply Lp.eq_zero_iff_ae_eq_zero.mpr
    filter_upwards [h1, Lp.coeFn_zero ℂ ∞ (volume.restrict unitDiscExterior)] with w hw hz
    rw [Pi.zero_apply]
    have : ‖μ w‖ = 0 := by nlinarith [norm_nonneg (μ w)]
    simpa using this
  induction m with
  | zero => exact ⟨fun _ => 0, fun i hi => absurd hi (Nat.not_lt_zero _), fun i hi => absurd hi (Nat.not_lt_zero _)⟩
  | succ m ih =>
    obtain ⟨e, heV, heo⟩ := ih
    set S : Submodule ℂ LinfStar := Submodule.span ℂ (e '' (Finset.range m : Set ℕ)) with hS
    have hSfin : FiniteDimensional ℂ S :=
      FiniteDimensional.span_of_finite ℂ ((Finset.range m).finite_toSet.image e)
    obtain ⟨v, hvV, hvS⟩ : ∃ v ∈ V, v ∉ S := by
      by_contra hc
      push_neg at hc
      exact hinf (Submodule.finiteDimensional_of_le (fun x hx => hc x hx))
    set w : LinfStar := v - ∑ i ∈ Finset.range m, wpInnerGamma Γ v (e i) • e i with hw
    have hwV : w ∈ V := V.sub_mem hvV (V.sum_mem fun i hi => V.smul_mem _ (heV i (Finset.mem_range.mp hi)))
    have hsumS : (∑ i ∈ Finset.range m, wpInnerGamma Γ v (e i) • e i) ∈ S :=
      S.sum_mem fun i hi => S.smul_mem _ (Submodule.subset_span ⟨i, hi, rfl⟩)
    have hw0 : w ≠ 0 := by
      intro h0
      apply hvS
      have : v = ∑ i ∈ Finset.range m, wpInnerGamma Γ v (e i) • e i := sub_eq_zero.mp h0
      rw [this]; exact hsumS
    have hwe : ∀ j < m, wpInnerGamma Γ w (e j) = 0 := by
      intro j hj
      rw [hw, sub_eq_add_neg, wpInnerGamma_add_left hΓ, ← neg_one_smul ℂ, wpInnerGamma_smul_left,
        s13c_sum_left hΓ]
      rw [Finset.sum_congr rfl (fun i hi => by rw [heo i (Finset.mem_range.mp hi) j hj])]
      simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_range.mpr hj, if_true]
      ring
    have hew : ∀ j < m, wpInnerGamma Γ (e j) w = 0 := fun j hj => by
      rw [wpInnerGamma_conj_symm, hwe j hj, map_zero]
    set r : ℝ := (wpInnerGamma Γ w w).re with hr
    have hr0 : 0 < r := lt_of_le_of_ne (wpInnerGamma_self_nonneg Γ w) (fun h => hw0 (hdef w hwV h.symm))
    have hww : wpInnerGamma Γ w w = (r : ℂ) := Complex.ext (by simp [hr]) (by simp [wpInnerGamma_self_im])
    set s : ℂ := (((Real.sqrt r)⁻¹ : ℝ) : ℂ) with hs
    have hss : s * conj s * r = 1 := by
      rw [hs, Complex.conj_ofReal, ← Complex.ofReal_mul, ← Complex.ofReal_mul]
      rw [show (Real.sqrt r)⁻¹ * (Real.sqrt r)⁻¹ * r = 1 by
        rw [← mul_inv, Real.mul_self_sqrt hr0.le, inv_mul_cancel₀ hr0.ne']]
      simp
    refine ⟨fun i => if i = m then s • w else e i, fun i hi => ?_, fun i hi j hj => ?_⟩
    · by_cases him : i = m
      · simp only [him, if_true]; exact V.smul_mem _ hwV
      · simp only [him, if_false]; exact heV i (by omega)
    · by_cases him : i = m <;> by_cases hjm : j = m
      · simp only [him, hjm, if_true, wpInnerGamma_smul_left, wpInnerGamma_smul_right, hww]
        rw [← hss]; ring
      · have hj' : j < m := by omega
        simp only [him, hjm, if_true, if_false, wpInnerGamma_smul_left, hwe j hj', mul_zero]
        rw [if_neg (Ne.symm hjm ∘ Eq.symm ∘ fun h => h.symm)]
      · have hi' : i < m := by omega
        simp only [him, hjm, if_true, if_false, wpInnerGamma_smul_right, hew i hi', mul_zero]
      · simp only [him, hjm, if_false]
        exact heo i (by omega) j (by omega)

/-- **Bessel at a point.** For an orthonormal family in the span, `Σ |e_i(w)|² ≤ K` a.e. -/
theorem s13c_bessel {Γ : Subgroup SL2C} (hΓ : IsCofinite Γ) {K : ℝ≥0∞} (hK : K < ∞)
    (hsup : ∀ μ ∈ Submodule.span ℂ (harmonicGamma Γ),
      ∀ᵐ w ∂(volume.restrict unitDiscExterior), (‖μ w‖₊ : ℝ≥0∞) ^ 2 ≤
        K * ∫⁻ z in fundDomain Γ, (‖μ z‖₊ : ℝ≥0∞) ^ 2 * ENNReal.ofReal (rho z))
    {m : ℕ} {e : ℕ → LinfStar} (heV : ∀ i < m, e i ∈ Submodule.span ℂ (harmonicGamma Γ))
    (heo : ∀ i < m, ∀ j < m, wpInnerGamma Γ (e i) (e j) = if i = j then 1 else 0) :
    ∀ᵐ w ∂(volume.restrict unitDiscExterior), ∑ i ∈ Finset.range m, ‖e i w‖ ^ 2 ≤ K.toReal := by
  set V := Submodule.span ℂ (harmonicGamma Γ)
  obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense (Fin m → ℂ)
  -- the bound for each coefficient vector
  have hc : ∀ c : Fin m → ℂ, ∀ᵐ w ∂(volume.restrict unitDiscExterior),
      ‖∑ i : Fin m, c i * e i w‖ ^ 2 ≤ K.toReal * ∑ i : Fin m, ‖c i‖ ^ 2 := by
    intro c
    set c' : ℕ → ℂ := fun i => if h : i < m then c ⟨i, h⟩ else 0 with hc'
    have hmem : (∑ i ∈ Finset.range m, c' i • e i) ∈ V :=
      V.sum_mem fun i hi => V.smul_mem _ (heV i (Finset.mem_range.mp hi))
    have hQ : (wpInnerGamma Γ (∑ i ∈ Finset.range m, c' i • e i) (∑ i ∈ Finset.range m, c' i • e i)).re =
        ∑ i : Fin m, ‖c i‖ ^ 2 := by
      rw [s13c_sum_left hΓ]
      simp_rw [s13c_sum_right hΓ]
      rw [Finset.sum_congr rfl (fun i hi => by
        rw [Finset.sum_congr rfl (fun j hj => by
          rw [heo i (Finset.mem_range.mp hi) j (Finset.mem_range.mp hj)])])]
      simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_range]
      rw [Finset.sum_congr rfl (fun i hi => by rw [if_pos (Finset.mem_range.mp hi)]),
        Complex.re_sum, ← Fin.sum_univ_eq_sum_range (fun i => (c' i * conj (c' i)).re)]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [hc', dif_pos i.isLt, Complex.mul_conj', ← Complex.ofReal_pow, Complex.ofReal_re]
    filter_upwards [s13c_sup_real hΓ hK (hsup _ hmem), s13c_coeFn_sum (Finset.range m) c' e] with w h1 h2
    rw [hQ, h2] at h1
    rw [← Fin.sum_univ_eq_sum_range (fun i => c' i * e i w)] at h1
    simpa [hc'] using h1
  have hall : ∀ᵐ w ∂(volume.restrict unitDiscExterior), ∀ c ∈ D,
      ‖∑ i : Fin m, c i * e i w‖ ^ 2 ≤ K.toReal * ∑ i : Fin m, ‖c i‖ ^ 2 :=
    (ae_ball_iff hDc).mpr fun c _ => hc c
  filter_upwards [hall] with w hw
  -- extend to every coefficient vector by density
  have hcl : IsClosed {c : Fin m → ℂ | ‖∑ i : Fin m, c i * e i w‖ ^ 2 ≤ K.toReal * ∑ i : Fin m, ‖c i‖ ^ 2} :=
    isClosed_le (by fun_prop) (by fun_prop)
  have hevery : ∀ c : Fin m → ℂ, ‖∑ i : Fin m, c i * e i w‖ ^ 2 ≤ K.toReal * ∑ i : Fin m, ‖c i‖ ^ 2 := by
    intro c
    have : c ∈ closure D := by rw [hDd.closure_eq]; trivial
    exact (hcl.closure_subset_iff.mpr hw) this
  have h1 := hevery (fun i => conj (e i w))
  have hsum : ∑ i : Fin m, conj (e i w) * e i w = ((∑ i : Fin m, ‖e i w‖ ^ 2 : ℝ) : ℂ) := by
    push_cast
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mul_comm, Complex.mul_conj']
  rw [hsum, Complex.norm_real, Real.norm_of_nonneg (Finset.sum_nonneg fun i _ => sq_nonneg _)] at h1
  simp only [Complex.norm_conj] at h1
  rw [← Fin.sum_univ_eq_sum_range (fun i => ‖e i w‖ ^ 2)]
  set t := ∑ i : Fin m, ‖e (↑i) w‖ ^ 2
  have ht : 0 ≤ t := Finset.sum_nonneg fun i _ => sq_nonneg _
  rcases ht.eq_or_lt with h0 | h0
  · rw [← h0]; exact ENNReal.toReal_nonneg
  · nlinarith

/-- The fixed-point equation of `γ ∈ SL(2, ℝ)` in coordinates. -/
theorem s13c_fix_eq (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) {τ : UpperHalfPlane} (h : γ • τ = τ) :
    ((γ 0 0 : ℝ) : ℂ) * τ + ((γ 0 1 : ℝ) : ℂ) = (τ : ℂ) * (((γ 1 0 : ℝ) : ℂ) * τ + ((γ 1 1 : ℝ) : ℂ)) := by
  have h' : ((γ • τ : UpperHalfPlane) : ℂ) = τ := by rw [h]
  rw [s13c_smul_coe, div_eq_iff (s13c_den_ne γ τ)] at h'
  exact h'

/-- An element of `SL(2, ℝ)` with two distinct fixed points in `ℍ` is `±1`. -/
theorem s13c_fix_unique (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) {τ1 τ2 : UpperHalfPlane}
    (h1 : γ • τ1 = τ1) (h2 : γ • τ2 = τ2) (hne : τ1 ≠ τ2) : γ = 1 ∨ γ = -1 := by
  have e1 := s13c_fix_eq γ h1
  have e2 := s13c_fix_eq γ h2
  have hfac : ((τ1 : ℂ) - τ2) * (((γ 1 0 : ℝ) : ℂ) * ((τ1 : ℂ) + τ2) + ((γ 1 1 : ℝ) : ℂ) - ((γ 0 0 : ℝ) : ℂ)) = 0 := by
    linear_combination e2 - e1
  have hne' : (τ1 : ℂ) - τ2 ≠ 0 := fun h => hne (UpperHalfPlane.ext (sub_eq_zero.mp h))
  have hs := (mul_eq_zero.mp hfac).resolve_left hne'
  have him : γ 1 0 * ((τ1 : ℂ).im + (τ2 : ℂ).im) = 0 := by
    have h := congrArg Complex.im hs
    simp only [Complex.sub_im, Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.zero_im, zero_mul, add_zero, mul_zero, sub_zero, zero_sub] at h
    linarith
  have hc : γ 1 0 = 0 :=
    (mul_eq_zero.mp him).resolve_right (add_pos τ1.im_pos τ2.im_pos).ne'
  have hi := congrArg Complex.im e1
  have hr := congrArg Complex.re e1
  simp only [Complex.add_im, Complex.add_re, Complex.mul_im, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, hc, zero_mul, mul_zero, add_zero, zero_add, sub_zero, Complex.ofReal_zero] at hi hr
  have had : γ 0 0 = γ 1 1 := by
    have h3 : (γ 0 0 - γ 1 1) * (τ1 : ℂ).im = 0 := by linarith
    exact sub_eq_zero.mp ((mul_eq_zero.mp h3).resolve_right τ1.im_pos.ne')
  have hb : γ 0 1 = 0 := by
    rw [had] at hr
    linarith
  have hsq : γ 1 1 * γ 1 1 = 1 := by
    have := γ.det_coe
    rw [Matrix.det_fin_two, hc, hb, had] at this
    linarith
  rcases mul_self_eq_one_iff.mp hsq with h | h
  · left
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hc, hb, had, h]
  · right
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hc, hb, had, h]

/-- **(B2.1) Base point.** A Fuchsian group has a point of `ℍ` fixed by no element other than `±1`. -/
theorem s13c_sg_base {Γ' : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} (hΓ' : LiZhongQC.IsFuchsian Γ') :
    ∃ p : UpperHalfPlane, ∀ γ ∈ Γ', γ • p = p → γ = 1 ∨ γ = -1 := by
  haveI := s13c_countable hΓ'
  obtain ⟨S, hS⟩ : ∃ S : Set UpperHalfPlane, S = ⋃ γ : Γ', {τ : UpperHalfPlane |
      (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) • τ = τ ∧ (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) ≠ 1 ∧
        (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) ≠ -1} := ⟨_, rfl⟩
  -- each element other than `±1` fixes at most one point, and `Γ'` is countable
  have hSc : S.Countable := by
    rw [hS]
    refine Set.countable_iUnion fun γ => Set.Subsingleton.countable ?_
    intro τ1 h1 τ2 h2
    by_contra hne
    rcases s13c_fix_unique _ h1.1 h2.1 hne with h | h
    · exact h1.2.1 h
    · exact h1.2.2 h
  have hinj : Function.Injective fun t : ℝ => (⟨(t : ℂ) + I, by simp⟩ : UpperHalfPlane) := by
    intro s t h
    have := congrArg (fun x : UpperHalfPlane => (x : ℂ).re) h
    simpa using this
  have hne : ∃ p, p ∉ S := by
    by_contra hall
    push_neg at hall
    exact Cardinal.not_countable_real ((hSc.preimage hinj).mono fun t _ => hall _)
  obtain ⟨p, hp⟩ := hne
  refine ⟨p, fun γ hγ hfix => ?_⟩
  by_contra hc
  push_neg at hc
  apply hp
  rw [hS]
  exact mem_iUnion.mpr ⟨⟨γ, hγ⟩, hfix, hc⟩

/-- **(B2.2) Generation by neighbours.** The elements carrying a point of the closed Dirichlet domain
`D(p) = {w | ∀ g ∈ Γ', d(w, p) ≤ d(w, g p)}` into `D(p)` generate `Γ'` (local finiteness and connectedness of `ℍ`). -/
theorem s13c_sg_gen {Γ' : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} (hΓ' : LiZhongQC.IsFuchsian Γ')
    (p : UpperHalfPlane) :
    Subgroup.closure {γ | γ ∈ Γ' ∧ ∃ w : UpperHalfPlane, (∀ g ∈ Γ', dist w p ≤ dist w (g • p)) ∧
      ∀ g ∈ Γ', dist (γ • w) p ≤ dist (γ • w) (g • p)} = Γ' := by
  set D : Set UpperHalfPlane := {w | ∀ g ∈ Γ', dist w p ≤ dist w (g • p)} with hD
  set H := Subgroup.closure {γ | γ ∈ Γ' ∧ ∃ w : UpperHalfPlane, (∀ g ∈ Γ', dist w p ≤ dist w (g • p)) ∧
      ∀ g ∈ Γ', dist (γ • w) p ≤ dist (γ • w) (g • p)} with hH
  have hHle : H ≤ Γ' := (Subgroup.closure_le _).mpr fun γ hγ => hγ.1
  have hpD : p ∈ D := fun g _ => by rw [dist_self]; exact dist_nonneg
  -- `D` is closed
  have hDcl : IsClosed D := by
    have heq : D = ⋂ g : Γ', {w : UpperHalfPlane |
        dist w p ≤ dist w ((g : Matrix.SpecialLinearGroup (Fin 2) ℝ) • p)} := by
      ext w
      simp only [hD, mem_setOf_eq, mem_iInter, Subtype.forall]
    rw [heq]
    exact isClosed_iInter fun g => isClosed_le (continuous_id.dist continuous_const)
      (continuous_id.dist continuous_const)
  -- every point lies in a translate of `D`
  have hcover : ∀ w : UpperHalfPlane, ∃ g ∈ Γ', g⁻¹ • w ∈ D := by
    intro w
    have hT := LiZhongQC.s82dx_finite_ball hΓ' p w (dist p w)
    obtain ⟨g, hgT, hgmin⟩ := hT.toFinset.exists_min_image (fun γ => dist (γ • p) w)
      ⟨1, by simp [Γ'.one_mem]⟩
    rw [Set.Finite.mem_toFinset] at hgT
    have hmin : ∀ g' ∈ Γ', dist (g • p) w ≤ dist (g' • p) w := by
      intro g' hg'
      by_cases h : dist (g' • p) w ≤ dist p w
      · exact hgmin g' (by rw [Set.Finite.mem_toFinset]; exact ⟨hg', h⟩)
      · push_neg at h
        exact le_trans hgT.2 h.le
    refine ⟨g, hgT.1, fun g'' hg'' => ?_⟩
    have e1 : dist (g⁻¹ • w) p = dist (g • p) w := by
      rw [dist_comm, ← dist_smul g, smul_inv_smul]
    have e2 : dist (g⁻¹ • w) (g'' • p) = dist ((g * g'') • p) w := by
      rw [dist_comm, ← dist_smul g, smul_inv_smul, mul_smul]
    rw [e1, e2]
    exact hmin _ (Γ'.mul_mem hgT.1 hg'')
  -- local finiteness of the translates
  obtain ⟨f, hf⟩ : ∃ f : Γ' → Set UpperHalfPlane,
      f = fun g : Γ' => (fun x => (g : Matrix.SpecialLinearGroup (Fin 2) ℝ) • x) '' D := ⟨_, rfl⟩
  have hfcl : ∀ g, IsClosed (f g) := by
    intro g
    rw [hf]
    exact (Homeomorph.smul (g : Matrix.SpecialLinearGroup (Fin 2) ℝ)).isClosed_image.mpr hDcl
  have hlf : LocallyFinite f := by
    intro w
    refine ⟨closedBall w 1, closedBall_mem_nhds w one_pos, ?_⟩
    have hfin := LiZhongQC.s82dx_finite_ball hΓ' p w (dist w p + 2)
    refine (hfin.preimage Subtype.val_injective.injOn).subset ?_
    rintro g ⟨x, hx, hxw⟩
    rw [hf] at hx
    obtain ⟨z, hz, rfl⟩ := hx
    refine ⟨g.2, ?_⟩
    have h1 : dist ((g : Matrix.SpecialLinearGroup (Fin 2) ℝ) • p)
        ((g : Matrix.SpecialLinearGroup (Fin 2) ℝ) • z) = dist z p := by
      rw [dist_smul, dist_comm]
    have h2 : dist z p ≤ dist ((g : Matrix.SpecialLinearGroup (Fin 2) ℝ) • z) p := by
      have h0 := hz _ (Γ'.inv_mem g.2)
      have e : dist z ((g : Matrix.SpecialLinearGroup (Fin 2) ℝ)⁻¹ • p) =
          dist ((g : Matrix.SpecialLinearGroup (Fin 2) ℝ) • z) p := by
        rw [← dist_smul (g : Matrix.SpecialLinearGroup (Fin 2) ℝ), smul_inv_smul]
      exact h0.trans e.le
    have h3 := mem_closedBall.mp hxw
    have h4 := dist_triangle ((g : Matrix.SpecialLinearGroup (Fin 2) ℝ) • p)
      ((g : Matrix.SpecialLinearGroup (Fin 2) ℝ) • z) w
    have h5 := dist_triangle ((g : Matrix.SpecialLinearGroup (Fin 2) ℝ) • z) w p
    have h6 : dist w p = dist p w := dist_comm _ _
    linarith
  -- the two closed pieces
  set A := ⋃ g : {g : Γ' // (g : Matrix.SpecialLinearGroup (Fin 2) ℝ) ∈ H}, f g.1 with hA
  set B := ⋃ g : {g : Γ' // (g : Matrix.SpecialLinearGroup (Fin 2) ℝ) ∉ H}, f g.1 with hB
  have hAcl : IsClosed A := (hlf.comp_injective Subtype.val_injective).isClosed_iUnion fun g => hfcl g.1
  have hBcl : IsClosed B := (hlf.comp_injective Subtype.val_injective).isClosed_iUnion fun g => hfcl g.1
  have hmemf : ∀ (g : Γ') (w : UpperHalfPlane), (g : Matrix.SpecialLinearGroup (Fin 2) ℝ)⁻¹ • w ∈ D → w ∈ f g := by
    intro g w hw
    rw [hf]
    exact ⟨_, hw, smul_inv_smul _ _⟩
  have hunion : ∀ w, w ∈ A ∨ w ∈ B := by
    intro w
    obtain ⟨g, hg, hgw⟩ := hcover w
    by_cases hgH : g ∈ H
    · exact Or.inl (mem_iUnion.mpr ⟨⟨⟨g, hg⟩, hgH⟩, hmemf ⟨g, hg⟩ w hgw⟩)
    · exact Or.inr (mem_iUnion.mpr ⟨⟨⟨g, hg⟩, hgH⟩, hmemf ⟨g, hg⟩ w hgw⟩)
  have hdisj : ∀ w, w ∈ A → w ∉ B := by
    intro w hwA hwB
    obtain ⟨⟨g1, hg1H⟩, hw1⟩ := mem_iUnion.mp hwA
    obtain ⟨⟨g2, hg2H⟩, hw2⟩ := mem_iUnion.mp hwB
    rw [hf] at hw1 hw2
    obtain ⟨z1, hz1, hzw1⟩ := hw1
    obtain ⟨z2, hz2, hzw2⟩ := hw2
    have hzw1' : (g1 : Matrix.SpecialLinearGroup (Fin 2) ℝ) • z1 = w := hzw1
    have hzw2' : (g2 : Matrix.SpecialLinearGroup (Fin 2) ℝ) • z2 = w := hzw2
    apply hg2H
    have hγ : (g1 : Matrix.SpecialLinearGroup (Fin 2) ℝ)⁻¹ * g2 ∈ H := by
      refine Subgroup.subset_closure ⟨Γ'.mul_mem (Γ'.inv_mem g1.2) g2.2, z2, hz2, ?_⟩
      have e : ((g1 : Matrix.SpecialLinearGroup (Fin 2) ℝ)⁻¹ * g2) • z2 = z1 := by
        rw [mul_smul, hzw2', ← hzw1', inv_smul_smul]
      rw [e]
      exact hz1
    have := H.mul_mem hg1H hγ
    rwa [mul_inv_cancel_left] at this
  -- connectedness of `ℍ`
  have hBopen : IsOpen B := by
    have : B = Aᶜ := by
      ext w
      exact ⟨fun hwB hwA => hdisj w hwA hwB, fun hwA => (hunion w).resolve_left hwA⟩
    rw [this]
    exact hAcl.isOpen_compl
  have hpA : p ∈ A := mem_iUnion.mpr ⟨⟨⟨1, Γ'.one_mem⟩, H.one_mem⟩, hmemf ⟨1, Γ'.one_mem⟩ p (by simpa using hpD)⟩
  have hBempty : B = ∅ := by
    rcases isClopen_iff.mp ⟨hBcl, hBopen⟩ with h | h
    · exact h
    · exact absurd (h ▸ mem_univ p) (hdisj p hpA)
  refine le_antisymm hHle fun g hg => ?_
  by_contra hgH
  have hgp : g • p ∈ B := mem_iUnion.mpr ⟨⟨⟨g, hg⟩, hgH⟩, hmemf ⟨g, hg⟩ _ (by simpa using hpD)⟩
  rw [hBempty] at hgp
  exact hgp

/-- **(B2.3) The Dirichlet domain has finite area** when `Γ'` has a finite-area covering set (its interior is
precisely invariant modulo `±1`, its boundary lies in countably many null bisectors). -/
theorem s13c_sg_area {Γ' : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} (hΓ' : LiZhongQC.IsFuchsian Γ')
    {p : UpperHalfPlane} (hp : ∀ γ ∈ Γ', γ • p = p → γ = 1 ∨ γ = -1)
    {F : Set ℂ} (hFm : MeasurableSet F) (hFH : F ⊆ upperHalf)
    (hcov : ∀ᵐ z ∂(volume.restrict upperHalf), ∀ hz : 0 < z.im, ∃ M ∈ Γ',
      ((M • (⟨z, hz⟩ : UpperHalfPlane) : UpperHalfPlane) : ℂ) ∈ F)
    (harea : ∫⁻ z in F, ENNReal.ofReal ((z.im ^ 2)⁻¹) < ∞) :
    ∫⁻ z in ((↑) : UpperHalfPlane → ℂ) '' {w : UpperHalfPlane | ∀ g ∈ Γ', dist w p ≤ dist w (g • p)},
      ENNReal.ofReal ((z.im ^ 2)⁻¹) < ∞ := by
  haveI := s13c_countable hΓ'
  -- the strict Dirichlet set and the bisectors, in coordinates
  obtain ⟨S, hS⟩ : ∃ S : Set ℂ, S = {z : ℂ | 0 < z.im} ∩ ⋂ g : {g : Γ' //
      (g : Matrix.SpecialLinearGroup (Fin 2) ℝ) • p ≠ p}, {z : ℂ |
      ‖z - p‖ ^ 2 * ((g.1 : Matrix.SpecialLinearGroup (Fin 2) ℝ) • p).im <
        ‖z - (((g.1 : Matrix.SpecialLinearGroup (Fin 2) ℝ) • p : UpperHalfPlane) : ℂ)‖ ^ 2 * p.im} := ⟨_, rfl⟩
  obtain ⟨Bis, hBis⟩ : ∃ Bis : Set ℂ, Bis = ⋃ g : {g : Γ' //
      (g : Matrix.SpecialLinearGroup (Fin 2) ℝ) • p ≠ p}, {z : ℂ |
      ‖z - p‖ ^ 2 * ((g.1 : Matrix.SpecialLinearGroup (Fin 2) ℝ) • p).im =
        ‖z - (((g.1 : Matrix.SpecialLinearGroup (Fin 2) ℝ) • p : UpperHalfPlane) : ℂ)‖ ^ 2 * p.im} := ⟨_, rfl⟩
  have hSm : MeasurableSet S := by
    rw [hS]
    exact (measurableSet_lt measurable_const Complex.measurable_im).inter
      (MeasurableSet.iInter fun g => measurableSet_lt (by fun_prop) (by fun_prop))
  have hSH : S ⊆ upperHalf := fun z hz => by
    rw [hS] at hz
    exact hz.1
  have hBis0 : volume Bis = 0 := by
    rw [hBis]
    exact measure_iUnion_null fun g => LiZhongQC.s82dx_poly_bisector_null (Ne.symm g.2)
  -- strict membership in distance form
  have hSdist : ∀ σ : UpperHalfPlane, (σ : ℂ) ∈ S → ∀ g ∈ Γ', g • p ≠ p → dist σ p < dist σ (g • p) := by
    intro σ hσ g hg hgp
    rw [hS] at hσ
    have h := mem_iInter.mp hσ.2 ⟨⟨g, hg⟩, hgp⟩
    simp only [mem_setOf_eq] at h
    rw [← not_le, LiZhongQC.s82dx_dist_le_iff]
    exact not_le.mpr h
  -- precise invariance modulo `±1`
  have hDf : ({1, -1} : Set (Matrix.SpecialLinearGroup (Fin 2) ℝ)).Finite :=
    (Set.finite_singleton _).insert _
  have hprec : ∀ γ ∈ Γ', ∀ σ : UpperHalfPlane, (σ : ℂ) ∈ S → ((γ • σ : UpperHalfPlane) : ℂ) ∈ S →
      γ ∈ ({1, -1} : Set (Matrix.SpecialLinearGroup (Fin 2) ℝ)) := by
    intro γ hγ σ hσ hγσ
    by_contra hc
    have hc' : ¬ (γ = 1 ∨ γ = -1) := by
      rintro (h | h) <;> simp [h] at hc
    have h1 : γ • p ≠ p := fun h => hc' (hp γ hγ h)
    have h2 : γ⁻¹ • p ≠ p := by
      intro h
      apply h1
      conv_lhs => rw [← h]
      rw [smul_inv_smul]
    have i1 := hSdist σ hσ _ (Γ'.inv_mem hγ) h2
    have i2 := hSdist _ hγσ γ hγ h1
    have e1 : dist (γ • σ) p = dist σ (γ⁻¹ • p) := by
      rw [← dist_smul γ⁻¹, inv_smul_smul]
    have e2 : dist (γ • σ) (γ • p) = dist σ p := dist_smul _ _ _
    rw [e1, e2] at i2
    exact absurd (i1.trans i2) (lt_irrefl _)
  -- the closed domain lies in the strict one plus the bisectors
  have hsub : ((↑) : UpperHalfPlane → ℂ) '' {w : UpperHalfPlane | ∀ g ∈ Γ', dist w p ≤ dist w (g • p)} ⊆
      S ∪ Bis := by
    rintro _ ⟨w, hw, rfl⟩
    by_cases hstrict : ∀ g : {g : Γ' // (g : Matrix.SpecialLinearGroup (Fin 2) ℝ) • p ≠ p},
        ‖(w : ℂ) - p‖ ^ 2 * ((g.1 : Matrix.SpecialLinearGroup (Fin 2) ℝ) • p).im <
          ‖(w : ℂ) - (((g.1 : Matrix.SpecialLinearGroup (Fin 2) ℝ) • p : UpperHalfPlane) : ℂ)‖ ^ 2 * p.im
    · left
      rw [hS]
      exact ⟨w.im_pos, mem_iInter.mpr hstrict⟩
    · right
      push_neg at hstrict
      obtain ⟨g, hg⟩ := hstrict
      rw [hBis]
      refine mem_iUnion.mpr ⟨g, ?_⟩
      have hle := (LiZhongQC.s82dx_dist_le_iff w p _).mp (hw _ g.1.2)
      exact le_antisymm hle hg
  have hunf := s13c_unfold_gen hΓ' hFm hcov hSm hSH hDf hprec (g := fun _ => 1) measurable_const
    (fun _ _ _ => rfl)
  simp only [one_mul] at hunf
  calc ∫⁻ z in ((↑) : UpperHalfPlane → ℂ) '' {w : UpperHalfPlane | ∀ g ∈ Γ', dist w p ≤ dist w (g • p)},
        ENNReal.ofReal ((z.im ^ 2)⁻¹)
      ≤ ∫⁻ z in S ∪ Bis, ENNReal.ofReal ((z.im ^ 2)⁻¹) := lintegral_mono_set hsub
    _ ≤ (∫⁻ z in S, ENNReal.ofReal ((z.im ^ 2)⁻¹)) + ∫⁻ z in Bis, ENNReal.ofReal ((z.im ^ 2)⁻¹) :=
        lintegral_union_le (μ := volume) (fun z : ℂ => ENNReal.ofReal ((z.im ^ 2)⁻¹)) S Bis
    _ = ∫⁻ z in S, ENNReal.ofReal ((z.im ^ 2)⁻¹) := by
        simp [setLIntegral_measure_zero _ _ hBis0]
    _ < ∞ := lt_of_le_of_lt hunf (ENNReal.mul_lt_top (ENNReal.natCast_lt_top _) harea)

/-- Equality in `dist (log z.im) (log w.im) ≤ dist z w` forces equal real parts. -/
theorem s13c_cv_re_eq {w z : UpperHalfPlane} (h : dist w z = dist (Real.log w.im) (Real.log z.im)) :
    w.re = z.re := by
  have hw := w.im_pos
  have hz := z.im_pos
  have h1 := UpperHalfPlane.cosh_dist w z
  rw [h, Real.dist_eq, Real.cosh_abs, ← Real.log_div hw.ne' hz.ne', Real.cosh_log (div_pos hw hz),
    Complex.dist_eq, Complex.sq_norm, Complex.normSq_apply] at h1
  simp only [Complex.sub_re, Complex.sub_im, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im] at h1
  have h2 : (w.re - z.re) ^ 2 = 0 := by
    field_simp at h1
    nlinarith [h1]
  exact sub_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp h2)

/-- The real part of a Möbius quotient vanishes when the numerator is orthogonal to the denominator. -/
theorem s13c_cv_re0 (α β γ δ : ℝ) (z : ℂ)
    (h : (α * z.re + β) * (γ * z.re + δ) + (α * z.im) * (γ * z.im) = 0) :
    (((α : ℂ) * z + (β : ℂ)) / ((γ : ℂ) * z + (δ : ℂ))).re = 0 := by
  have h1 : ((α : ℂ) * z + (β : ℂ)).re = α * z.re + β := by simp
  have h2 : ((α : ℂ) * z + (β : ℂ)).im = α * z.im := by simp
  have h3 : ((γ : ℂ) * z + (δ : ℂ)).re = γ * z.re + δ := by simp
  have h4 : ((γ : ℂ) * z + (δ : ℂ)).im = γ * z.im := by simp
  rw [Complex.div_re, h1, h2, h3, h4, ← add_div, h, zero_div]

/-- Any two points of `ℍ` are carried by `SL(2, ℝ)` onto the imaginary axis. -/
theorem s13c_cv_norm (a b : UpperHalfPlane) :
    ∃ M : Matrix.SpecialLinearGroup (Fin 2) ℝ, (M • a).re = 0 ∧ (M • b).re = 0 := by
  by_cases hab : a.re = b.re
  · set M : Matrix.SpecialLinearGroup (Fin 2) ℝ := ⟨!![1, -a.re; 0, 1], by simp [Matrix.det_fin_two]⟩ with hM
    have e00 : M 0 0 = 1 := rfl
    have e01 : M 0 1 = -a.re := rfl
    have e10 : M 1 0 = 0 := rfl
    have e11 : M 1 1 = 1 := rfl
    refine ⟨M, ?_, ?_⟩
    · rw [← UpperHalfPlane.coe_re, s13c_smul_coe, e00, e01, e10, e11]
      apply s13c_cv_re0
      simp only [UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]
      ring
    · rw [← UpperHalfPlane.coe_re, s13c_smul_coe, e00, e01, e10, e11]
      apply s13c_cv_re0
      simp only [UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]
      rw [hab]
      ring
  · have hd : b.re - a.re ≠ 0 := sub_ne_zero.mpr (Ne.symm hab)
    set c : ℝ := (b.re ^ 2 + b.im ^ 2 - a.re ^ 2 - a.im ^ 2) / (2 * (b.re - a.re)) with hcdef
    have hc : 2 * (b.re - a.re) * c = b.re ^ 2 + b.im ^ 2 - a.re ^ 2 - a.im ^ 2 := by
      rw [hcdef]
      field_simp
    have hpos : 0 < (a.re - c) ^ 2 + a.im ^ 2 := by
      have := a.im_pos
      positivity
    set r : ℝ := √((a.re - c) ^ 2 + a.im ^ 2) with hrdef
    have hr0 : 0 < r := Real.sqrt_pos.mpr hpos
    have hra : r ^ 2 = (a.re - c) ^ 2 + a.im ^ 2 := Real.sq_sqrt hpos.le
    have hrb : r ^ 2 = (b.re - c) ^ 2 + b.im ^ 2 := by
      rw [hra]
      linear_combination hc
    set t : ℝ := √(2 * r) with htdef
    have ht0 : 0 < t := Real.sqrt_pos.mpr (by positivity)
    have ht2 : t ^ 2 = 2 * r := Real.sq_sqrt (by positivity)
    have hdet : 1 / t * ((c + r) / t) - -(c - r) / t * (-1 / t) = 1 := by
      rw [show 1 / t * ((c + r) / t) - -(c - r) / t * (-1 / t) = (2 * r) / t ^ 2 by ring, ht2,
        div_self (by positivity)]
    set M : Matrix.SpecialLinearGroup (Fin 2) ℝ :=
      ⟨!![1 / t, -(c - r) / t; -1 / t, (c + r) / t], by rw [Matrix.det_fin_two_of]; exact hdet⟩ with hM
    have e00 : M 0 0 = 1 / t := rfl
    have e01 : M 0 1 = -(c - r) / t := rfl
    have e10 : M 1 0 = -1 / t := rfl
    have e11 : M 1 1 = (c + r) / t := rfl
    refine ⟨M, ?_, ?_⟩
    · rw [← UpperHalfPlane.coe_re, s13c_smul_coe, e00, e01, e10, e11]
      apply s13c_cv_re0
      simp only [UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]
      linear_combination (1 / t) ^ 2 * hra
    · rw [← UpperHalfPlane.coe_re, s13c_smul_coe, e00, e01, e10, e11]
      apply s13c_cv_re0
      simp only [UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]
      linear_combination (1 / t) ^ 2 * hrb

/-- (B2.4.i) on the imaginary axis. -/
theorem s13c_cv_axis {a b z p q : UpperHalfPlane} (hra : a.re = 0) (hrb : b.re = 0)
    (ha : dist a p ≤ dist a q) (hb : dist b p ≤ dist b q)
    (hz : dist a z + dist z b = dist a b) : dist z p ≤ dist z q := by
  have hab := UpperHalfPlane.dist_of_re_eq (hra.trans hrb.symm)
  have h1 := UpperHalfPlane.dist_log_im_le a z
  have h2 := UpperHalfPlane.dist_log_im_le z b
  have h3 := dist_triangle (Real.log a.im) (Real.log z.im) (Real.log b.im)
  have hz1 : dist a z = dist (Real.log a.im) (Real.log z.im) := by linarith
  have hsum : |Real.log a.im - Real.log z.im + (Real.log z.im - Real.log b.im)| =
      |Real.log a.im - Real.log z.im| + |Real.log z.im - Real.log b.im| := by
    rw [show Real.log a.im - Real.log z.im + (Real.log z.im - Real.log b.im) =
      Real.log a.im - Real.log b.im by ring]
    simp only [Real.dist_eq] at hab h1 h2 h3 hz1
    linarith
  have hzre : z.re = 0 := (s13c_cv_re_eq hz1).symm.trans hra
  have hpa := a.im_pos
  have hpb := b.im_pos
  have hpz := z.im_pos
  have hpp := p.im_pos
  have hpq := q.im_pos
  rw [LiZhongQC.s82dx_dist_le_iff] at ha hb ⊢
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im, UpperHalfPlane.coe_re,
    UpperHalfPlane.coe_im] at ha hb ⊢
  rw [hra] at ha
  rw [hrb] at hb
  rw [hzre]
  rcases abs_add_eq_add_abs_iff _ _ |>.mp hsum with ⟨hu, hv⟩ | ⟨hu, hv⟩
  · have hza : z.im ≤ a.im := (Real.log_le_log_iff hpz hpa).mp (by linarith)
    have hbz : b.im ≤ z.im := (Real.log_le_log_iff hpb hpz).mp (by linarith)
    rcases le_total 0 (p.im - q.im) with hK | hK
    · nlinarith [mul_nonneg hK (mul_nonneg (sub_nonneg.mpr hbz) (add_pos hpz hpb).le)]
    · nlinarith [mul_nonneg (neg_nonneg.mpr hK) (mul_nonneg (sub_nonneg.mpr hza) (add_pos hpz hpa).le)]
  · have hza : a.im ≤ z.im := (Real.log_le_log_iff hpa hpz).mp (by linarith)
    have hbz : z.im ≤ b.im := (Real.log_le_log_iff hpz hpb).mp (by linarith)
    rcases le_total 0 (p.im - q.im) with hK | hK
    · nlinarith [mul_nonneg hK (mul_nonneg (sub_nonneg.mpr hza) (add_pos hpz hpa).le)]
    · nlinarith [mul_nonneg (neg_nonneg.mpr hK) (mul_nonneg (sub_nonneg.mpr hbz) (add_pos hpz hpb).le)]

/-- A continuous geodesic path from `w` to `b`: every `σ t`, `t ∈ [0, 1]`, realises equality in the triangle
inequality. -/
theorem s13c_fc_path (w b : UpperHalfPlane) :
    ∃ σ : ℝ → UpperHalfPlane, Continuous σ ∧ σ 0 = w ∧ σ 1 = b ∧
      ∀ t ∈ Icc (0 : ℝ) 1, dist w (σ t) + dist (σ t) b = dist w b := by
  obtain ⟨M, hMw, hMb⟩ := s13c_cv_norm w b
  obtain ⟨f, hf⟩ : ∃ f : ℝ → UpperHalfPlane, f = fun y => UpperHalfPlane.mk ⟨0, Real.exp y⟩ (Real.exp_pos y) :=
    ⟨_, rfl⟩
  have hfi : Isometry f := by
    rw [hf]
    exact UpperHalfPlane.isometry_vertical_line 0
  have hfx : ∀ x : UpperHalfPlane, x.re = 0 → f (Real.log x.im) = x := by
    intro x hx
    rw [hf]
    apply UpperHalfPlane.ext
    apply Complex.ext
    · simp [hx]
    · simp [Real.exp_log x.im_pos]
  have e1 : ∀ y : UpperHalfPlane, dist w (M⁻¹ • y) = dist (M • w) y := by
    intro y
    rw [← dist_smul M w, smul_inv_smul]
  have e2 : ∀ y : UpperHalfPlane, dist (M⁻¹ • y) b = dist y (M • b) := by
    intro y
    rw [← dist_smul M _ b, smul_inv_smul]
  refine ⟨fun t => M⁻¹ • f ((1 - t) * Real.log (M • w).im + t * Real.log (M • b).im), ?_, ?_, ?_, ?_⟩
  · exact (continuous_const_smul M⁻¹).comp (hfi.continuous.comp (by fun_prop))
  · simp only [sub_zero, one_mul, zero_mul, add_zero]
    rw [hfx _ hMw, inv_smul_smul]
  · simp only [sub_self, zero_mul, zero_add, one_mul]
    rw [hfx _ hMb, inv_smul_smul]
  · intro t ht
    have d1 : ∀ y, dist (M • w) (f y) = |Real.log (M • w).im - y| := by
      intro y
      rw [← Real.dist_eq, ← hfi.dist_eq, hfx _ hMw]
    have d2 : ∀ y, dist (f y) (M • b) = |y - Real.log (M • b).im| := by
      intro y
      rw [← Real.dist_eq, ← hfi.dist_eq, hfx _ hMb]
    have d3 : dist (M • w) (M • b) = |Real.log (M • w).im - Real.log (M • b).im| := by
      rw [← Real.dist_eq, ← hfi.dist_eq, hfx _ hMw, hfx _ hMb]
    simp only
    rw [e1, e2, ← dist_smul M w b, d1, d2, d3]
    rw [show Real.log (M • w).im - ((1 - t) * Real.log (M • w).im + t * Real.log (M • b).im) =
        t * (Real.log (M • w).im - Real.log (M • b).im) by ring,
      show (1 - t) * Real.log (M • w).im + t * Real.log (M • b).im - Real.log (M • b).im =
        (1 - t) * (Real.log (M • w).im - Real.log (M • b).im) by ring,
      abs_mul, abs_mul, abs_of_nonneg ht.1, abs_of_nonneg (sub_nonneg.mpr ht.2)]
    ring

/-- The denominator of the disc chart does not vanish inside the unit disc. -/
theorem s13c_cy_den (θ s : ℝ) (hs0 : 0 ≤ s) (hs1 : s < 1) :
    (1 : ℂ) - (s : ℂ) * Complex.exp ((θ : ℂ) * I) ≠ 0 := by
  intro h
  have h1 : (s : ℂ) * Complex.exp ((θ : ℂ) * I) = 1 := (sub_eq_zero.mp h).symm
  have h2 := congrArg (‖·‖) h1
  simp only [norm_mul, Complex.norm_exp_ofReal_mul_I, Complex.norm_real, Real.norm_eq_abs, mul_one, norm_one,
    abs_of_nonneg hs0] at h2
  linarith

/-- The point at chart radius `s < 1` in direction `θ` from `u` lies in `ℍ`. -/
theorem s13c_cy_rim (u : UpperHalfPlane) (θ s : ℝ) (hs0 : 0 ≤ s) (hs1 : s < 1) :
    0 < (((u : ℂ) - conj (u : ℂ) * ((s : ℂ) * Complex.exp ((θ : ℂ) * I))) /
      (1 - (s : ℂ) * Complex.exp ((θ : ℂ) * I))).im := by
  have hd := s13c_cy_den θ s hs0 hs1
  have hc := Real.cos_sq_add_sin_sq θ
  have hu := u.im_pos
  rw [Complex.div_im, ← sub_div]
  apply div_pos _ (Complex.normSq_pos.mpr hd)
  simp only [Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im,
    Complex.one_re, Complex.one_im, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im, zero_mul, mul_zero,
    sub_zero, zero_sub, add_zero]
  have h1 : u.im * s ^ 2 * (Real.cos θ ^ 2 + Real.sin θ ^ 2) = u.im * s ^ 2 := by rw [hc, mul_one]
  have h2 : 0 < u.im - u.im * s ^ 2 := by
    have h := mul_pos hu (show (0 : ℝ) < 1 - s ^ 2 by nlinarith)
    linarith [h, show u.im * (1 - s ^ 2) = u.im - u.im * s ^ 2 by ring]
  nlinarith [h1, h2]

/-- A point of `ℍ` lies in `(↑) '' X` iff it lies in `X`. -/
theorem s13c_cy_coe_mem (z : UpperHalfPlane) (X : Set UpperHalfPlane) :
    (z : ℂ) ∈ ((↑) : UpperHalfPlane → ℂ) '' X ↔ z ∈ X := by
  constructor
  · rintro ⟨x, hx, hxe⟩
    rw [← UpperHalfPlane.ext hxe]
    exact hx
  · intro h
    exact ⟨z, h, rfl⟩

/-- The chart point lies in `(↑) '' X` iff the corresponding point of `ℍ` lies in `X`. -/
theorem s13c_cy_memiff (u : UpperHalfPlane) (θ s : ℝ) (hs0 : 0 ≤ s) (hs1 : s < 1) (X : Set UpperHalfPlane) :
    ((u : ℂ) - conj (u : ℂ) * ((s : ℂ) * Complex.exp ((θ : ℂ) * I))) /
        (1 - (s : ℂ) * Complex.exp ((θ : ℂ) * I)) ∈ ((↑) : UpperHalfPlane → ℂ) '' X ↔
      (⟨_, s13c_cy_rim u θ s hs0 hs1⟩ : UpperHalfPlane) ∈ X :=
  s13c_cy_coe_mem ⟨_, s13c_cy_rim u θ s hs0 hs1⟩ X

/-- An element of `SL(2, ℝ)` maps the chart at `u` to the chart at `g u` up to a rotation. -/
theorem s13c_cy_rot (g : Matrix.SpecialLinearGroup (Fin 2) ℝ) (u : UpperHalfPlane) :
    ∃ c : ℝ, ∀ (θ s : ℝ) (hs0 : 0 ≤ s) (hs1 : s < 1),
      ((g • (⟨_, s13c_cy_rim u θ s hs0 hs1⟩ : UpperHalfPlane) : UpperHalfPlane) : ℂ) =
        (((g • u : UpperHalfPlane) : ℂ) - conj ((g • u : UpperHalfPlane) : ℂ) *
          ((s : ℂ) * Complex.exp (((θ + c : ℝ) : ℂ) * I))) /
          (1 - (s : ℂ) * Complex.exp (((θ + c : ℝ) : ℂ) * I)) := by
  have hden : ((g 1 0 : ℝ) : ℂ) * (u : ℂ) + ((g 1 1 : ℝ) : ℂ) ≠ 0 := s13c_den_ne g u
  have hconj : ((g 1 0 : ℝ) : ℂ) * conj (u : ℂ) + ((g 1 1 : ℝ) : ℂ) =
      conj (((g 1 0 : ℝ) : ℂ) * (u : ℂ) + ((g 1 1 : ℝ) : ℂ)) := by
    simp [map_add, map_mul, Complex.conj_ofReal]
  have hdenc : ((g 1 0 : ℝ) : ℂ) * conj (u : ℂ) + ((g 1 1 : ℝ) : ℂ) ≠ 0 := by
    rw [hconj]
    exact (map_ne_zero (starRingEnd ℂ)).mpr hden
  obtain ⟨l, hl⟩ : ∃ l : ℂ, l = (((g 1 0 : ℝ) : ℂ) * conj (u : ℂ) + ((g 1 1 : ℝ) : ℂ)) /
      (((g 1 0 : ℝ) : ℂ) * (u : ℂ) + ((g 1 1 : ℝ) : ℂ)) := ⟨_, rfl⟩
  have hnorm : ‖l‖ = 1 := by
    rw [hl, norm_div, hconj, Complex.norm_conj, div_self (norm_ne_zero_iff.mpr hden)]
  refine ⟨Complex.arg l, fun θ s hs0 hs1 => ?_⟩
  have hexp : Complex.exp (((θ + Complex.arg l : ℝ) : ℂ) * I) = Complex.exp ((θ : ℂ) * I) * l := by
    rw [Complex.ofReal_add, add_mul, Complex.exp_add]
    congr 1
    have h := Complex.norm_mul_exp_arg_mul_I l
    rw [hnorm, Complex.ofReal_one, one_mul] at h
    exact h
  have h1 := s13c_cy_den θ s hs0 hs1
  have h3 := s13c_cy_den (θ + Complex.arg l) s hs0 hs1
  rw [hexp] at h3
  have hX : ((⟨_, s13c_cy_rim u θ s hs0 hs1⟩ : UpperHalfPlane) : ℂ) =
      ((u : ℂ) - conj (u : ℂ) * ((s : ℂ) * Complex.exp ((θ : ℂ) * I))) /
        (1 - (s : ℂ) * Complex.exp ((θ : ℂ) * I)) := rfl
  have h2 := s13c_den_ne g ⟨_, s13c_cy_rim u θ s hs0 hs1⟩
  rw [hX] at h2
  rw [hexp, s13c_smul_coe, s13c_smul_coe, hX]
  simp only [map_div₀, map_add, map_mul, Complex.conj_ofReal]
  have hden' : (u : ℂ) * ((g 1 0 : ℝ) : ℂ) + ((g 1 1 : ℝ) : ℂ) ≠ 0 := by
    rw [mul_comm]
    exact hden
  have hdenc' : conj (u : ℂ) * ((g 1 0 : ℝ) : ℂ) + ((g 1 1 : ℝ) : ℂ) ≠ 0 := by
    rw [mul_comm]
    exact hdenc
  rw [hl] at h3 ⊢
  rw [div_eq_div_iff h2 h3]
  field_simp
  ring

/-- Directions measured in a window are invariant under a shift, for a measurable `2π`-periodic set. -/
theorem s13c_cy_shift {S : Set ℝ} (hS : MeasurableSet S) (hper : ∀ θ, θ + 2 * π ∈ S ↔ θ ∈ S) (c : ℝ) :
    volume {θ : ℝ | θ ∈ Ioc (-π) π ∧ θ + c ∈ S} = volume {θ : ℝ | θ ∈ Ioc (-π) π ∧ θ ∈ S} := by
  have key : ∀ t : ℝ, volume (Ioc t (t + 2 * π) ∩ S) = volume (Ioc (-π) (-π + 2 * π) ∩ S) := by
    intro t
    have hf : Function.Periodic (S.indicator (fun _ => (1 : ℝ))) (2 * π) := by
      intro θ
      by_cases h : θ ∈ S
      · rw [Set.indicator_of_mem h, Set.indicator_of_mem ((hper θ).mpr h)]
      · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem fun h' => h ((hper θ).mp h')]
    have hI := hf.intervalIntegral_add_eq t (-π)
    have hval : ∀ a : ℝ, ∫ x in a..a + 2 * π, S.indicator (fun _ => (1 : ℝ)) x =
        (volume (Ioc a (a + 2 * π) ∩ S)).toReal := by
      intro a
      rw [intervalIntegral.integral_of_le (by linarith [Real.pi_pos]), MeasureTheory.integral_indicator hS,
        MeasureTheory.setIntegral_const, smul_eq_mul, mul_one, Measure.real_def, Measure.restrict_apply hS,
        Set.inter_comm]
    rw [hval, hval] at hI
    have hfin : ∀ a : ℝ, volume (Ioc a (a + 2 * π) ∩ S) ≠ ⊤ := fun a =>
      ne_top_of_le_ne_top (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)
        (measure_mono Set.inter_subset_left)
    exact (ENNReal.toReal_eq_toReal_iff' (hfin t) (hfin (-π))).mp hI
  have e1 : {θ : ℝ | θ ∈ Ioc (-π) π ∧ θ + c ∈ S} =
      (fun θ => θ + c) ⁻¹' (Ioc (-π + c) (-π + c + 2 * π) ∩ S) := by
    ext θ
    simp only [mem_setOf_eq, mem_preimage, mem_inter_iff, mem_Ioc]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      exact ⟨⟨by linarith, by linarith⟩, h3⟩
    · rintro ⟨⟨h1, h2⟩, h3⟩
      exact ⟨⟨by linarith, by linarith⟩, h3⟩
  have e2 : {θ : ℝ | θ ∈ Ioc (-π) π ∧ θ ∈ S} = Ioc (-π) (-π + 2 * π) ∩ S := by
    rw [show -π + 2 * π = π by ring]
    rfl
  rw [e1, e2, measure_preimage_add_right, key]

/-- Directions along which a chart ray from a point of a bisector enters a Dirichlet half-plane: an exact
half-circle `0 ≤ Re (B e^{iθ})`, `B ≠ 0`. -/
theorem s13c_cy_half (u p1 p2 : UpperHalfPlane) (hne : p1 ≠ p2) (heq : dist u p1 = dist u p2) :
    ∃ B : ℂ, B ≠ 0 ∧ ∀ (θ s : ℝ) (hs0 : 0 < s) (hs1 : s < 1),
      (dist (⟨_, s13c_cy_rim u θ s hs0.le hs1⟩ : UpperHalfPlane) p1 ≤
          dist (⟨_, s13c_cy_rim u θ s hs0.le hs1⟩ : UpperHalfPlane) p2 ↔
        0 ≤ (B * Complex.exp ((θ : ℂ) * I)).re) ∧
      (dist (⟨_, s13c_cy_rim u θ s hs0.le hs1⟩ : UpperHalfPlane) p2 ≤
          dist (⟨_, s13c_cy_rim u θ s hs0.le hs1⟩ : UpperHalfPlane) p1 ↔
        (B * Complex.exp ((θ : ℂ) * I)).re ≤ 0) := by
  have hu := u.im_pos
  have hp1 := p1.im_pos
  have hp2 := p2.im_pos
  -- `u` is on the bisector, in coordinates
  have hFv : ((u.re - p1.re) ^ 2 + (u.im - p1.im) ^ 2) * p2.im =
      ((u.re - p2.re) ^ 2 + (u.im - p2.im) ^ 2) * p1.im := by
    have h1 := (LiZhongQC.s82dx_dist_le_iff u p1 p2).mp heq.le
    have h2 := (LiZhongQC.s82dx_dist_le_iff u p2 p1).mp heq.ge
    have h3 := le_antisymm h1 h2
    simpa only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im, UpperHalfPlane.coe_re,
      UpperHalfPlane.coe_im, ← sq] using h3
  obtain ⟨B, hBre, hBim⟩ : ∃ B : ℂ,
      B.re = -((p1.im - p2.im) * (u.re ^ 2 - u.im ^ 2) + (-2 * (p2.re * p1.im - p1.re * p2.im)) * u.re +
        ((p2.re ^ 2 + p2.im ^ 2) * p1.im - (p1.re ^ 2 + p1.im ^ 2) * p2.im)) ∧
      B.im = 2 * (p1.im - p2.im) * u.re * u.im + (-2 * (p2.re * p1.im - p1.re * p2.im)) * u.im :=
    ⟨⟨_, _⟩, rfl, rfl⟩
  have hB : B ≠ 0 := by
    intro hB0
    rw [hB0, Complex.zero_re] at hBre
    rw [hB0, Complex.zero_im] at hBim
    have h1 : 2 * (p1.im - p2.im) * u.re + (-2 * (p2.re * p1.im - p1.re * p2.im)) = 0 := by
      have h : (2 * (p1.im - p2.im) * u.re + (-2 * (p2.re * p1.im - p1.re * p2.im))) * u.im = 0 := by
        linarith
      exact (mul_eq_zero.mp h).resolve_right hu.ne'
    have h2 : (p1.im - p2.im) * u.im ^ 2 = 0 := by nlinarith
    have h3 : p1.im - p2.im = 0 := (mul_eq_zero.mp h2).resolve_right (by positivity)
    have h4 : p1.re = p2.re := by
      have h5 : (p1.re - p2.re) * p1.im = 0 := by linear_combination h1 / 2 + (p1.re - u.re) * h3
      exact sub_eq_zero.mp ((mul_eq_zero.mp h5).resolve_right hp1.ne')
    exact hne (UpperHalfPlane.ext (Complex.ext (by simpa using h4) (by simpa using sub_eq_zero.mp h3)))
  refine ⟨B, hB, fun θ s hs0 hs1 => ?_⟩
  have hDn := s13c_cy_den θ s hs0.le hs1
  have hn : 0 < ‖(1 : ℂ) - (s : ℂ) * Complex.exp ((θ : ℂ) * I)‖ ^ 2 := pow_pos (norm_pos_iff.mpr hDn) 2
  have hsub : ∀ q : ℂ, ((u : ℂ) - conj (u : ℂ) * ((s : ℂ) * Complex.exp ((θ : ℂ) * I))) /
      (1 - (s : ℂ) * Complex.exp ((θ : ℂ) * I)) - q =
      ((u : ℂ) - conj (u : ℂ) * ((s : ℂ) * Complex.exp ((θ : ℂ) * I)) -
        q * (1 - (s : ℂ) * Complex.exp ((θ : ℂ) * I))) / (1 - (s : ℂ) * Complex.exp ((θ : ℂ) * I)) := by
    intro q
    field_simp
  have hiff : ∀ q1 q2 : UpperHalfPlane,
      dist (⟨_, s13c_cy_rim u θ s hs0.le hs1⟩ : UpperHalfPlane) q1 ≤
          dist (⟨_, s13c_cy_rim u θ s hs0.le hs1⟩ : UpperHalfPlane) q2 ↔
        ‖(u : ℂ) - conj (u : ℂ) * ((s : ℂ) * Complex.exp ((θ : ℂ) * I)) -
            (q1 : ℂ) * (1 - (s : ℂ) * Complex.exp ((θ : ℂ) * I))‖ ^ 2 * q2.im ≤
          ‖(u : ℂ) - conj (u : ℂ) * ((s : ℂ) * Complex.exp ((θ : ℂ) * I)) -
            (q2 : ℂ) * (1 - (s : ℂ) * Complex.exp ((θ : ℂ) * I))‖ ^ 2 * q1.im := by
    intro q1 q2
    rw [LiZhongQC.s82dx_dist_le_iff]
    show ‖((u : ℂ) - conj (u : ℂ) * ((s : ℂ) * Complex.exp ((θ : ℂ) * I))) /
        (1 - (s : ℂ) * Complex.exp ((θ : ℂ) * I)) - (q1 : ℂ)‖ ^ 2 * q2.im ≤
      ‖((u : ℂ) - conj (u : ℂ) * ((s : ℂ) * Complex.exp ((θ : ℂ) * I))) /
        (1 - (s : ℂ) * Complex.exp ((θ : ℂ) * I)) - (q2 : ℂ)‖ ^ 2 * q1.im ↔ _
    rw [hsub, hsub, norm_div, norm_div, div_pow, div_pow, div_mul_eq_mul_div, div_mul_eq_mul_div,
      div_le_div_iff_of_pos_right hn]
  have hR : (B * Complex.exp ((θ : ℂ) * I)).re = B.re * Real.cos θ - B.im * Real.sin θ := by
    simp [Complex.mul_re, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
  have hkey : ‖(u : ℂ) - conj (u : ℂ) * ((s : ℂ) * Complex.exp ((θ : ℂ) * I)) -
          (p2 : ℂ) * (1 - (s : ℂ) * Complex.exp ((θ : ℂ) * I))‖ ^ 2 * p1.im -
        ‖(u : ℂ) - conj (u : ℂ) * ((s : ℂ) * Complex.exp ((θ : ℂ) * I)) -
          (p1 : ℂ) * (1 - (s : ℂ) * Complex.exp ((θ : ℂ) * I))‖ ^ 2 * p2.im =
      2 * s * (B * Complex.exp ((θ : ℂ) * I)).re := by
    rw [hR, hBre, hBim, Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im,
      Complex.one_re, Complex.one_im, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]
    linear_combination (-(1 + (s * Real.cos θ) ^ 2 + (s * Real.sin θ) ^ 2)) * hFv
  have h2s : 0 < 2 * s := by linarith
  constructor
  · rw [hiff, ← sub_nonneg, hkey]
    exact mul_nonneg_iff_of_pos_left h2s
  · rw [hiff, ← sub_nonpos, hkey]
    constructor
    · intro h
      by_contra hc
      push_neg at hc
      nlinarith [mul_pos h2s hc]
    · intro h
      exact mul_nonpos_of_nonneg_of_nonpos h2s.le h

/-- The directions of an exact half-circle condition `Re (B e^{iθ}) = 0` form a null set. -/
theorem s13c_cy_zero (B : ℂ) (hB : B ≠ 0) : volume {θ : ℝ | (B * Complex.exp ((θ : ℂ) * I)).re = 0} = 0 := by
  apply Set.Countable.measure_zero
  have hBn : 0 < ‖B‖ := norm_pos_iff.mpr hB
  refine (Set.countable_range fun k : ℤ => (2 * (k : ℝ) + 1) * π / 2 - Complex.arg B).mono ?_
  intro θ hθ
  simp only [mem_setOf_eq] at hθ
  have h1 : (B * Complex.exp ((θ : ℂ) * I)).re = ‖B‖ * Real.cos (θ + Complex.arg B) := by
    rw [Real.cos_add]
    simp only [Complex.mul_re, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
    rw [← Complex.norm_mul_cos_arg B, ← Complex.norm_mul_sin_arg B]
    ring
  rw [h1] at hθ
  have h2 : Real.cos (θ + Complex.arg B) = 0 := (mul_eq_zero.mp hθ).resolve_left hBn.ne'
  obtain ⟨k, hk⟩ := Real.cos_eq_zero_iff.mp h2
  exact ⟨k, by show (2 * (k : ℝ) + 1) * π / 2 - Complex.arg B = θ; linarith⟩

/-- A half-circle of directions has measure at most `π` in the window `(-π, π]`. -/
theorem s13c_cy_halfvol (B : ℂ) (hB : B ≠ 0) :
    volume {θ : ℝ | θ ∈ Ioc (-π) π ∧ 0 ≤ (B * Complex.exp ((θ : ℂ) * I)).re} ≤ ENNReal.ofReal π := by
  have hcont : Continuous fun θ : ℝ => (B * Complex.exp ((θ : ℂ) * I)).re := by fun_prop
  have hS : MeasurableSet {θ : ℝ | 0 ≤ (B * Complex.exp ((θ : ℂ) * I)).re} :=
    (isClosed_le continuous_const hcont).measurableSet
  have hper : ∀ θ : ℝ, θ + 2 * π ∈ {θ : ℝ | 0 ≤ (B * Complex.exp ((θ : ℂ) * I)).re} ↔
      θ ∈ {θ : ℝ | 0 ≤ (B * Complex.exp ((θ : ℂ) * I)).re} := by
    intro θ
    simp only [mem_setOf_eq]
    rw [show ((θ + 2 * π : ℝ) : ℂ) * I = (θ : ℂ) * I + 2 * π * I by push_cast; ring, Complex.exp_add,
      Complex.exp_two_pi_mul_I, mul_one]
  have hflip : ∀ θ : ℝ, (B * Complex.exp (((θ + π : ℝ) : ℂ) * I)).re = -(B * Complex.exp ((θ : ℂ) * I)).re := by
    intro θ
    rw [show ((θ + π : ℝ) : ℂ) * I = (θ : ℂ) * I + π * I by push_cast; ring, Complex.exp_add,
      Complex.exp_pi_mul_I]
    simp
  have hsh := s13c_cy_shift hS hper π
  have e2 : {θ : ℝ | θ ∈ Ioc (-π) π ∧ θ + π ∈ {θ : ℝ | 0 ≤ (B * Complex.exp ((θ : ℂ) * I)).re}} =
      {θ : ℝ | θ ∈ Ioc (-π) π ∧ (B * Complex.exp ((θ : ℂ) * I)).re ≤ 0} := by
    ext θ
    simp only [mem_setOf_eq, hflip]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1, by linarith⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h1, by linarith⟩
  rw [e2] at hsh
  have hS2 : MeasurableSet {θ : ℝ | θ ∈ Ioc (-π) π ∧ (B * Complex.exp ((θ : ℂ) * I)).re ≤ 0} :=
    measurableSet_Ioc.inter (isClosed_le hcont continuous_const).measurableSet
  have hU : {θ : ℝ | θ ∈ Ioc (-π) π ∧ 0 ≤ (B * Complex.exp ((θ : ℂ) * I)).re} ∪
      {θ : ℝ | θ ∈ Ioc (-π) π ∧ (B * Complex.exp ((θ : ℂ) * I)).re ≤ 0} = Ioc (-π) π := by
    ext θ
    simp only [mem_union, mem_setOf_eq]
    constructor
    · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
    · intro h
      rcases le_total 0 (B * Complex.exp ((θ : ℂ) * I)).re with h' | h'
      · exact Or.inl ⟨h, h'⟩
      · exact Or.inr ⟨h, h'⟩
  have hI : volume ({θ : ℝ | θ ∈ Ioc (-π) π ∧ 0 ≤ (B * Complex.exp ((θ : ℂ) * I)).re} ∩
      {θ : ℝ | θ ∈ Ioc (-π) π ∧ (B * Complex.exp ((θ : ℂ) * I)).re ≤ 0}) = 0 :=
    measure_mono_null (fun θ hθ => le_antisymm hθ.2.2 hθ.1.2) (s13c_cy_zero B hB)
  have hsum := measure_union_add_inter (μ := volume)
    {θ : ℝ | θ ∈ Ioc (-π) π ∧ 0 ≤ (B * Complex.exp ((θ : ℂ) * I)).re} hS2
  rw [hU, hI, add_zero, hsh, Real.volume_Ioc] at hsum
  have hsum' : ENNReal.ofReal (π - -π) =
      volume {θ : ℝ | θ ∈ Ioc (-π) π ∧ 0 ≤ (B * Complex.exp ((θ : ℂ) * I)).re} +
        volume {θ : ℝ | θ ∈ Ioc (-π) π ∧ 0 ≤ (B * Complex.exp ((θ : ℂ) * I)).re} := hsum
  by_contra hlt
  push_neg at hlt
  have h := ENNReal.add_lt_add hlt hlt
  rw [← hsum', ← ENNReal.ofReal_add Real.pi_pos.le Real.pi_pos.le,
    show π - -π = π + π by ring] at h
  exact lt_irrefl _ h

/-- The set of directions whose chart ray eventually stays in a closed set is measurable (an `F_σ`). -/
theorem s13c_cy_meas (u : UpperHalfPlane) {X : Set UpperHalfPlane} (hX : IsClosed X) :
    MeasurableSet {θ : ℝ | ∀ᶠ s : ℝ in 𝓝[>] (0 : ℝ),
      ((u : ℂ) - conj (u : ℂ) * ((s : ℂ) * Complex.exp ((θ : ℂ) * I))) /
        (1 - (s : ℂ) * Complex.exp ((θ : ℂ) * I)) ∈ ((↑) : UpperHalfPlane → ℂ) '' X} := by
  have heq : {θ : ℝ | ∀ᶠ s : ℝ in 𝓝[>] (0 : ℝ),
      ((u : ℂ) - conj (u : ℂ) * ((s : ℂ) * Complex.exp ((θ : ℂ) * I))) /
        (1 - (s : ℂ) * Complex.exp ((θ : ℂ) * I)) ∈ ((↑) : UpperHalfPlane → ℂ) '' X} =
      ⋃ n : ℕ, ⋂ s ∈ Ioo (0 : ℝ) (1 / ((n : ℝ) + 2)), {θ : ℝ |
        ((u : ℂ) - conj (u : ℂ) * ((s : ℂ) * Complex.exp ((θ : ℂ) * I))) /
          (1 - (s : ℂ) * Complex.exp ((θ : ℂ) * I)) ∈ ((↑) : UpperHalfPlane → ℂ) '' X} := by
    ext θ
    simp only [mem_setOf_eq, mem_iUnion, mem_iInter]
    constructor
    · intro h
      obtain ⟨ε, hε, hεP⟩ := Metric.eventually_nhds_iff.mp (eventually_nhdsWithin_iff.mp h)
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε
      refine ⟨n, fun s hs => hεP ?_ hs.1⟩
      rw [Real.dist_eq, sub_zero, abs_of_pos hs.1]
      have : 1 / ((n : ℝ) + 2) < 1 / ((n : ℝ) + 1) :=
        one_div_lt_one_div_of_lt (by positivity) (by linarith)
      linarith [hs.2]
    · rintro ⟨n, hn⟩
      rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff]
      refine ⟨1 / ((n : ℝ) + 2), by positivity, fun s hs hs0 => hn s ⟨hs0, ?_⟩⟩
      rw [Real.dist_eq, sub_zero] at hs
      exact lt_of_abs_lt hs
  rw [heq]
  refine MeasurableSet.iUnion fun n => IsClosed.measurableSet (isClosed_biInter fun s hs => ?_)
  have hs1 : s < 1 := lt_of_lt_of_le hs.2 (by rw [div_le_one (by positivity)]; linarith)
  have hc1 : Continuous fun θ : ℝ => ((u : ℂ) - conj (u : ℂ) * ((s : ℂ) * Complex.exp ((θ : ℂ) * I))) /
      (1 - (s : ℂ) * Complex.exp ((θ : ℂ) * I)) :=
    Continuous.div (by fun_prop) (by fun_prop) fun θ => s13c_cy_den θ s hs.1.le hs1
  have hcont : Continuous fun θ : ℝ => (⟨_, s13c_cy_rim u θ s hs.1.le hs1⟩ : UpperHalfPlane) :=
    hc1.upperHalfPlaneMk _
  have hpre : {θ : ℝ | ((u : ℂ) - conj (u : ℂ) * ((s : ℂ) * Complex.exp ((θ : ℂ) * I))) /
      (1 - (s : ℂ) * Complex.exp ((θ : ℂ) * I)) ∈ ((↑) : UpperHalfPlane → ℂ) '' X} =
      (fun θ : ℝ => (⟨_, s13c_cy_rim u θ s hs.1.le hs1⟩ : UpperHalfPlane)) ⁻¹' X := by
    ext θ
    exact s13c_cy_memiff u θ s hs.1.le hs1 X
  rw [hpre]
  exact hX.preimage hcont

/-- The arithmetic of a vertex cycle: with fibre sizes `m u ≥ 1` summing to at least `3`, angles in `[0, π]` and
`Σ m u · a u ≤ 2π`, the cycle has angle defect at least `π/3`. -/
theorem s13c_cy_arith {ι : Type*} (C : Finset ι) (a : ι → ℝ) (m : ι → ℕ) (ha0 : ∀ u ∈ C, 0 ≤ a u)
    (haπ : ∀ u ∈ C, a u ≤ π) (hm1 : ∀ u ∈ C, 1 ≤ m u) (hm3 : 3 ≤ ∑ u ∈ C, m u)
    (hsum : ∑ u ∈ C, (m u : ℝ) * a u ≤ 2 * π) : π / 3 + ∑ u ∈ C, a u ≤ (C.card : ℝ) * π := by
  have hπ := Real.pi_pos
  have hle : ∑ u ∈ C, a u ≤ ∑ u ∈ C, (m u : ℝ) * a u := Finset.sum_le_sum fun u hu => by
    have h1 : (1 : ℝ) ≤ m u := by exact_mod_cast hm1 u hu
    nlinarith [ha0 u hu]
  rcases Nat.lt_or_ge C.card 3 with hc | hc
  · obtain h | h | h : C.card = 0 ∨ C.card = 1 ∨ C.card = 2 := by omega
    · rw [Finset.card_eq_zero] at h
      subst h
      simp at hm3
    · rw [h]
      obtain ⟨u, rfl⟩ := Finset.card_eq_one.mp h
      simp only [Finset.sum_singleton] at hm3 hsum ⊢
      have h3 : (3 : ℝ) ≤ m u := by exact_mod_cast hm3
      have hu0 := ha0 u (Finset.mem_singleton_self u)
      push_cast
      nlinarith [mul_le_mul_of_nonneg_right h3 hu0]
    · rw [h]
      obtain ⟨u1, u2, hne, rfl⟩ := Finset.card_eq_two.mp h
      rw [Finset.sum_pair hne] at hm3 hsum ⊢
      have h10 := ha0 u1 (by simp)
      have h20 := ha0 u2 (by simp)
      have h1π := haπ u1 (by simp)
      have h2π := haπ u2 (by simp)
      have hm1' : (1 : ℝ) ≤ m u1 := by exact_mod_cast hm1 u1 (by simp)
      have hm2' : (1 : ℝ) ≤ m u2 := by exact_mod_cast hm1 u2 (by simp)
      push_cast
      rcases le_or_gt 2 (m u1) with h1 | h1
      · have h2 : (2 : ℝ) ≤ m u1 := by exact_mod_cast h1
        nlinarith [mul_le_mul_of_nonneg_right h2 h10, mul_le_mul_of_nonneg_right hm2' h20]
      · have h2' : 2 ≤ m u2 := by omega
        have h2 : (2 : ℝ) ≤ m u2 := by exact_mod_cast h2'
        nlinarith [mul_le_mul_of_nonneg_right h2 h20, mul_le_mul_of_nonneg_right hm1' h10]
  · have h3 : (3 : ℝ) ≤ C.card := by exact_mod_cast hc
    nlinarith

/-- Imaginary part of the disc chart `ζ ↦ (p - p̄ ζ)/(1 - ζ)`. -/
theorem s13c_pc_im (p : UpperHalfPlane) (ζ : ℂ) :
    (((p : ℂ) - conj (p : ℂ) * ζ) / (1 - ζ)).im = p.im * (1 - Complex.normSq ζ) / Complex.normSq (1 - ζ) := by
  rw [Complex.div_im, ← sub_div]
  congr 1
  simp only [Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im,
    Complex.one_re, Complex.one_im, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im, Complex.normSq_apply]
  ring

/-- **(P1) Hyperbolic area in polar coordinates of the disc chart at `p`.** The chart is
`ζ ↦ (p - p̄ ζ)/(1 - ζ)`, in which the hyperbolic density is `4/(1 - |ζ|²)²`. -/
theorem s13c_pc_area (p : UpperHalfPlane) {E : Set UpperHalfPlane} (hE : MeasurableSet E) :
    ∫⁻ z in ((↑) : UpperHalfPlane → ℂ) '' E, ENNReal.ofReal ((z.im ^ 2)⁻¹) =
      ∫⁻ θ in Ioc (-π) π, ∫⁻ s in Ioo (0 : ℝ) 1,
        (((↑) : UpperHalfPlane → ℂ) '' E).indicator (fun _ => ENNReal.ofReal (4 * s / (1 - s ^ 2) ^ 2))
          (((p : ℂ) - conj (p : ℂ) * ((s : ℂ) * Complex.exp ((θ : ℂ) * I))) /
            (1 - (s : ℂ) * Complex.exp ((θ : ℂ) * I))) := by
  obtain ⟨f, hf⟩ : ∃ f : ℂ → ℂ, f = fun ζ => ((p : ℂ) - conj (p : ℂ) * ζ) / (1 - ζ) := ⟨_, rfl⟩
  have hp := p.im_pos
  have hEm : MeasurableSet (((↑) : UpperHalfPlane → ℂ) '' E) :=
    UpperHalfPlane.measurableEmbedding_coe.measurableSet_image.mpr hE
  have hden : ∀ ζ ∈ Metric.ball (0 : ℂ) 1, (1 : ℂ) - ζ ≠ 0 := by
    intro ζ hζ h
    have h1 : ζ = 1 := (sub_eq_zero.mp h).symm
    rw [Metric.mem_ball, dist_zero_right, h1, norm_one] at hζ
    exact lt_irrefl _ hζ
  have hpp : (p : ℂ) - conj (p : ℂ) ≠ 0 := by
    intro h
    have h1 := congrArg Complex.im h
    simp only [Complex.sub_im, Complex.conj_im, Complex.zero_im, UpperHalfPlane.coe_im] at h1
    linarith
  have hfm : Measurable f := by
    rw [hf]
    exact (measurable_const.sub (measurable_const.mul measurable_id)).div (measurable_const.sub measurable_id)
  obtain ⟨S, hS⟩ : ∃ S : Set ℂ, S = Metric.ball (0 : ℂ) 1 ∩ f ⁻¹' (((↑) : UpperHalfPlane → ℂ) '' E) :=
    ⟨_, rfl⟩
  have hSm : MeasurableSet S := by
    rw [hS]
    exact Metric.isOpen_ball.measurableSet.inter (hfm hEm)
  -- the chart is a bijection from the disc onto `ℍ`
  have hinv : ∀ z : UpperHalfPlane, ((z : ℂ) - p) / ((z : ℂ) - conj (p : ℂ)) ∈ Metric.ball (0 : ℂ) 1 ∧
      f (((z : ℂ) - p) / ((z : ℂ) - conj (p : ℂ))) = z := by
    intro z
    have hz := z.im_pos
    have hzp : (z : ℂ) - conj (p : ℂ) ≠ 0 := by
      intro h
      have h1 := congrArg Complex.im h
      simp only [Complex.sub_im, Complex.conj_im, Complex.zero_im, UpperHalfPlane.coe_im] at h1
      linarith
    constructor
    · rw [Metric.mem_ball, dist_zero_right, norm_div, div_lt_one (norm_pos_iff.mpr hzp), ← sq_lt_sq₀
        (norm_nonneg _) (norm_nonneg _), Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply,
        Complex.normSq_apply]
      simp only [Complex.sub_re, Complex.sub_im, Complex.conj_re, Complex.conj_im, UpperHalfPlane.coe_re,
        UpperHalfPlane.coe_im]
      nlinarith [mul_pos hz hp]
    · rw [hf]
      have h1 : (1 : ℂ) - ((z : ℂ) - p) / ((z : ℂ) - conj (p : ℂ)) ≠ 0 := by
        rw [one_sub_div hzp]
        have e : (z : ℂ) - conj (p : ℂ) - ((z : ℂ) - p) = (p : ℂ) - conj (p : ℂ) := by ring
        rw [e]
        exact div_ne_zero hpp hzp
      rw [div_eq_iff h1]
      field_simp
      ring
  have himage : f '' S = ((↑) : UpperHalfPlane → ℂ) '' E := by
    apply Set.Subset.antisymm
    · rintro _ ⟨ζ, hζ, rfl⟩
      rw [hS] at hζ
      exact hζ.2
    · rintro _ ⟨z, hz, rfl⟩
      refine ⟨_, ?_, (hinv z).2⟩
      rw [hS]
      exact ⟨(hinv z).1, by rw [mem_preimage, (hinv z).2]; exact ⟨z, hz, rfl⟩⟩
  have hinj : InjOn f S := by
    intro ζ1 h1 ζ2 h2 h
    rw [hS] at h1 h2
    rw [hf] at h
    simp only at h
    rw [div_eq_div_iff (hden ζ1 h1.1) (hden ζ2 h2.1)] at h
    have h3 : ((p : ℂ) - conj (p : ℂ)) * (ζ1 - ζ2) = 0 := by linear_combination h
    exact sub_eq_zero.mp ((mul_eq_zero.mp h3).resolve_left hpp)
  -- the derivative of the chart
  have hder : ∀ ζ ∈ Metric.ball (0 : ℂ) 1, HasDerivAt f (((p : ℂ) - conj (p : ℂ)) / (1 - ζ) ^ 2) ζ := by
    intro ζ hζ
    rw [hf]
    have h1 : HasDerivAt (fun ζ : ℂ => (p : ℂ) - conj (p : ℂ) * ζ) (-(conj (p : ℂ) * 1)) ζ :=
      ((hasDerivAt_id ζ).const_mul (conj (p : ℂ))).const_sub (p : ℂ)
    have h2 : HasDerivAt (fun ζ : ℂ => 1 - ζ) (-1) ζ := (hasDerivAt_id ζ).const_sub 1
    have h3 := h1.div h2 (hden ζ hζ)
    convert h3 using 1
    ring
  have hfd : ∀ ζ ∈ S, HasFDerivWithinAt f ((ContinuousLinearMap.toSpanSingleton ℂ
      (((p : ℂ) - conj (p : ℂ)) / (1 - ζ) ^ 2)).restrictScalars ℝ) S ζ := by
    intro ζ hζ
    rw [hS] at hζ
    exact ((hder ζ hζ.1).hasFDerivAt.restrictScalars ℝ).hasFDerivWithinAt
  have hdet : ∀ w : ℂ, ((ContinuousLinearMap.toSpanSingleton ℂ w).restrictScalars ℝ).det = ‖w‖ ^ 2 := by
    intro w
    simp [ContinuousLinearMap.det, LinearMap.det_restrictScalars, Algebra.norm_complex_eq,
      Complex.normSq_eq_norm_sq]
  conv_lhs => rw [← himage, lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hSm hfd hinj]
  -- the hyperbolic density in the chart
  have hJ : ∀ ζ ∈ S, ENNReal.ofReal |((ContinuousLinearMap.toSpanSingleton ℂ
      (((p : ℂ) - conj (p : ℂ)) / (1 - ζ) ^ 2)).restrictScalars ℝ).det| * ENNReal.ofReal (((f ζ).im ^ 2)⁻¹) =
      ENNReal.ofReal (4 / (1 - ‖ζ‖ ^ 2) ^ 2) := by
    intro ζ hζ
    rw [hS] at hζ
    have hζ1 := hζ.1
    rw [Metric.mem_ball, dist_zero_right] at hζ1
    have hd := hden ζ hζ.1
    have hn : 0 < Complex.normSq (1 - ζ) := Complex.normSq_pos.mpr hd
    have hm : Complex.normSq ζ < 1 := by
      rw [← Complex.sq_norm]
      nlinarith [norm_nonneg ζ]
    rw [hdet, abs_of_nonneg (sq_nonneg _), ← ENNReal.ofReal_mul (sq_nonneg _), hf]
    simp only
    rw [s13c_pc_im, Complex.sq_norm, Complex.sq_norm, map_div₀, map_pow]
    congr 1
    have hpn : Complex.normSq ((p : ℂ) - conj (p : ℂ)) = 4 * p.im ^ 2 := by
      simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.conj_re, Complex.conj_im,
        UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]
      ring
    rw [hpn]
    have h1m : 0 < 1 - Complex.normSq ζ := by linarith
    field_simp
  rw [setLIntegral_congr_fun hSm hJ, ← lintegral_indicator hSm, ← Complex.lintegral_comp_polarCoord_symm,
    polarCoord_target]
  -- Fubini in polar coordinates
  have hmeas : Measurable fun q : ℝ × ℝ => ENNReal.ofReal q.1 •
      S.indicator (fun ζ => ENNReal.ofReal (4 / (1 - ‖ζ‖ ^ 2) ^ 2)) (Complex.polarCoord.symm q) := by
    have hg : Measurable fun ζ : ℂ => ENNReal.ofReal (4 / (1 - ‖ζ‖ ^ 2) ^ 2) :=
      (measurable_const.div ((measurable_const.sub (measurable_norm.pow_const 2)).pow_const 2)).ennreal_ofReal
    have hpc : Measurable fun q : ℝ × ℝ => Complex.polarCoord.symm q := by
      simp only [Complex.polarCoord_symm_apply]
      fun_prop
    exact measurable_fst.ennreal_ofReal.smul ((hg.indicator hSm).comp hpc)
  rw [Measure.volume_eq_prod, ← Measure.prod_restrict, lintegral_prod _ hmeas.aemeasurable,
    lintegral_lintegral_swap hmeas.aemeasurable, setLIntegral_congr Ioo_ae_eq_Ioc]
  refine setLIntegral_congr_fun measurableSet_Ioc fun θ _ => ?_
  -- the radial integral lives on `(0, 1)`
  have hpt : ∀ r ∈ Ioi (0 : ℝ), ENNReal.ofReal r •
      S.indicator (fun ζ => ENNReal.ofReal (4 / (1 - ‖ζ‖ ^ 2) ^ 2)) (Complex.polarCoord.symm (r, θ)) =
      (Ioo (0 : ℝ) 1).indicator (fun s => (((↑) : UpperHalfPlane → ℂ) '' E).indicator
        (fun _ => ENNReal.ofReal (4 * s / (1 - s ^ 2) ^ 2))
          (((p : ℂ) - conj (p : ℂ) * ((s : ℂ) * Complex.exp ((θ : ℂ) * I))) /
            (1 - (s : ℂ) * Complex.exp ((θ : ℂ) * I)))) r := by
    intro r hr
    have hr0 : 0 < r := hr
    have hpol : Complex.polarCoord.symm (r, θ) = (r : ℂ) * Complex.exp ((θ : ℂ) * I) := by
      simp only [Complex.polarCoord_symm_apply]
      rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
    have hnorm : ‖(r : ℂ) * Complex.exp ((θ : ℂ) * I)‖ = r := by
      rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hr0]
    rw [hpol]
    by_cases hr1 : r < 1
    · have hball : (r : ℂ) * Complex.exp ((θ : ℂ) * I) ∈ Metric.ball (0 : ℂ) 1 := by
        rw [Metric.mem_ball, dist_zero_right, hnorm]
        exact hr1
      rw [Set.indicator_of_mem (show r ∈ Ioo (0 : ℝ) 1 from ⟨hr0, hr1⟩)]
      have hfv : f ((r : ℂ) * Complex.exp ((θ : ℂ) * I)) =
          ((p : ℂ) - conj (p : ℂ) * ((r : ℂ) * Complex.exp ((θ : ℂ) * I))) /
            (1 - (r : ℂ) * Complex.exp ((θ : ℂ) * I)) := by
        rw [hf]
      by_cases hmem : ((p : ℂ) - conj (p : ℂ) * ((r : ℂ) * Complex.exp ((θ : ℂ) * I))) /
          (1 - (r : ℂ) * Complex.exp ((θ : ℂ) * I)) ∈ ((↑) : UpperHalfPlane → ℂ) '' E
      · have hS' : (r : ℂ) * Complex.exp ((θ : ℂ) * I) ∈ S := by
          rw [hS]
          refine ⟨hball, ?_⟩
          rw [mem_preimage, hfv]
          exact hmem
        rw [Set.indicator_of_mem hS', Set.indicator_of_mem hmem, hnorm, smul_eq_mul,
          ← ENNReal.ofReal_mul hr0.le]
        congr 1
        ring
      · have hS' : (r : ℂ) * Complex.exp ((θ : ℂ) * I) ∉ S := by
          intro h
          rw [hS] at h
          apply hmem
          rw [← hfv]
          exact h.2
        rw [Set.indicator_of_notMem hS', Set.indicator_of_notMem hmem, smul_zero]
    · have hnot : (r : ℂ) * Complex.exp ((θ : ℂ) * I) ∉ S := by
        intro h
        rw [hS] at h
        have h1 := h.1
        rw [Metric.mem_ball, dist_zero_right, hnorm] at h1
        exact hr1 h1
      rw [Set.indicator_of_notMem hnot, smul_zero, Set.indicator_of_notMem fun h => hr1 h.2]
  rw [setLIntegral_congr_fun measurableSet_Ioi hpt, setLIntegral_indicator measurableSet_Ioo,
    Set.inter_eq_left.mpr Set.Ioo_subset_Ioi_self]
/-- **(P3) A Dirichlet half-plane in the disc chart at `p`.** With `a = |p - x|² Im p`, the half-plane
`{d(·, p) ≤ d(·, x)}` reads `0 ≤ a (1 + s²) + 2 s Re (B e^{iθ})` along the chart ray in direction `θ`; moreover
`|B|² - a² = 4 (Im p)³ Im x |p - x|²` and `B (x - p) = -a (x - p̄)` (the chart point of `x` is `-a/B`). -/
theorem s13c_pb_chart (p x : UpperHalfPlane) :
    ∃ B : ℂ, ‖B‖ ^ 2 - (‖(p : ℂ) - x‖ ^ 2 * p.im) ^ 2 = 4 * p.im ^ 3 * x.im * ‖(p : ℂ) - x‖ ^ 2 ∧
      B * ((x : ℂ) - p) = -((‖(p : ℂ) - x‖ ^ 2 * p.im : ℝ) : ℂ) * ((x : ℂ) - conj (p : ℂ)) ∧
      ∀ (θ s : ℝ) (hs0 : 0 ≤ s) (hs1 : s < 1),
        (dist (⟨_, s13c_cy_rim p θ s hs0 hs1⟩ : UpperHalfPlane) p ≤
            dist (⟨_, s13c_cy_rim p θ s hs0 hs1⟩ : UpperHalfPlane) x ↔
          0 ≤ ‖(p : ℂ) - x‖ ^ 2 * p.im * (1 + s ^ 2) + 2 * s * (B * Complex.exp ((θ : ℂ) * I)).re) ∧
        (dist (⟨_, s13c_cy_rim p θ s hs0 hs1⟩ : UpperHalfPlane) x ≤
            dist (⟨_, s13c_cy_rim p θ s hs0 hs1⟩ : UpperHalfPlane) p ↔
          ‖(p : ℂ) - x‖ ^ 2 * p.im * (1 + s ^ 2) + 2 * s * (B * Complex.exp ((θ : ℂ) * I)).re ≤ 0) := by
  have hnx : ‖(p : ℂ) - x‖ ^ 2 = (p.re - x.re) ^ 2 + (p.im - x.im) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.sub_im, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]
    ring
  obtain ⟨B, hBre, hBim⟩ : ∃ B : ℂ,
      B.re = -((p.im - x.im) * (p.re ^ 2 - p.im ^ 2) + (-2 * (x.re * p.im - p.re * x.im)) * p.re +
        ((x.re ^ 2 + x.im ^ 2) * p.im - (p.re ^ 2 + p.im ^ 2) * x.im)) ∧
      B.im = 2 * (p.im - x.im) * p.re * p.im + (-2 * (x.re * p.im - p.re * x.im)) * p.im :=
    ⟨⟨_, _⟩, rfl, rfl⟩
  refine ⟨B, ?_, ?_, fun θ s hs0 hs1 => ?_⟩
  · rw [Complex.sq_norm, Complex.normSq_apply, hBre, hBim, hnx]
    ring
  · apply Complex.ext
    · simp only [Complex.mul_re, Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
        Complex.ofReal_re, Complex.ofReal_im, Complex.conj_re, Complex.conj_im, UpperHalfPlane.coe_re,
        UpperHalfPlane.coe_im, hBre, hBim, hnx]
      ring
    · simp only [Complex.mul_im, Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
        Complex.ofReal_re, Complex.ofReal_im, Complex.conj_re, Complex.conj_im, UpperHalfPlane.coe_re,
        UpperHalfPlane.coe_im, hBre, hBim, hnx]
      ring
  have hDn := s13c_cy_den θ s hs0 hs1
  have hn : 0 < ‖(1 : ℂ) - (s : ℂ) * Complex.exp ((θ : ℂ) * I)‖ ^ 2 := pow_pos (norm_pos_iff.mpr hDn) 2
  have hsub : ∀ q : ℂ, ((p : ℂ) - conj (p : ℂ) * ((s : ℂ) * Complex.exp ((θ : ℂ) * I))) /
      (1 - (s : ℂ) * Complex.exp ((θ : ℂ) * I)) - q =
      ((p : ℂ) - conj (p : ℂ) * ((s : ℂ) * Complex.exp ((θ : ℂ) * I)) -
        q * (1 - (s : ℂ) * Complex.exp ((θ : ℂ) * I))) / (1 - (s : ℂ) * Complex.exp ((θ : ℂ) * I)) := by
    intro q
    field_simp
  have hiff : ∀ q1 q2 : UpperHalfPlane,
      dist (⟨_, s13c_cy_rim p θ s hs0 hs1⟩ : UpperHalfPlane) q1 ≤
          dist (⟨_, s13c_cy_rim p θ s hs0 hs1⟩ : UpperHalfPlane) q2 ↔
        ‖(p : ℂ) - conj (p : ℂ) * ((s : ℂ) * Complex.exp ((θ : ℂ) * I)) -
            (q1 : ℂ) * (1 - (s : ℂ) * Complex.exp ((θ : ℂ) * I))‖ ^ 2 * q2.im ≤
          ‖(p : ℂ) - conj (p : ℂ) * ((s : ℂ) * Complex.exp ((θ : ℂ) * I)) -
            (q2 : ℂ) * (1 - (s : ℂ) * Complex.exp ((θ : ℂ) * I))‖ ^ 2 * q1.im := by
    intro q1 q2
    rw [LiZhongQC.s82dx_dist_le_iff]
    show ‖((p : ℂ) - conj (p : ℂ) * ((s : ℂ) * Complex.exp ((θ : ℂ) * I))) /
        (1 - (s : ℂ) * Complex.exp ((θ : ℂ) * I)) - (q1 : ℂ)‖ ^ 2 * q2.im ≤
      ‖((p : ℂ) - conj (p : ℂ) * ((s : ℂ) * Complex.exp ((θ : ℂ) * I))) /
        (1 - (s : ℂ) * Complex.exp ((θ : ℂ) * I)) - (q2 : ℂ)‖ ^ 2 * q1.im ↔ _
    rw [hsub, hsub, norm_div, norm_div, div_pow, div_pow, div_mul_eq_mul_div, div_mul_eq_mul_div,
      div_le_div_iff_of_pos_right hn]
  have hc := Real.cos_sq_add_sin_sq θ
  have hkey : ‖(p : ℂ) - conj (p : ℂ) * ((s : ℂ) * Complex.exp ((θ : ℂ) * I)) -
          (x : ℂ) * (1 - (s : ℂ) * Complex.exp ((θ : ℂ) * I))‖ ^ 2 * p.im -
        ‖(p : ℂ) - conj (p : ℂ) * ((s : ℂ) * Complex.exp ((θ : ℂ) * I)) -
          (p : ℂ) * (1 - (s : ℂ) * Complex.exp ((θ : ℂ) * I))‖ ^ 2 * x.im =
      ‖(p : ℂ) - x‖ ^ 2 * p.im * (1 + s ^ 2) + 2 * s * (B * Complex.exp ((θ : ℂ) * I)).re := by
    have hR : (B * Complex.exp ((θ : ℂ) * I)).re = B.re * Real.cos θ - B.im * Real.sin θ := by
      simp [Complex.mul_re, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
    rw [hR, hBre, hBim, hnx, Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im,
      Complex.one_re, Complex.one_im, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]
    linear_combination (((p.re - x.re) ^ 2 + (p.im - x.im) ^ 2) * p.im * s ^ 2) * hc
  constructor
  · rw [hiff, ← sub_nonneg, hkey]
  · rw [hiff, ← sub_nonpos, hkey]

/-- Along a chart ray, a Dirichlet half-plane (with `p` strictly inside) is an initial segment. -/
theorem s13c_pb_seg {a b S s : ℝ} (ha : 0 < a) (hs : 0 < s) (hsS : s ≤ S) (hS1 : S ≤ 1)
    (h : 0 ≤ a * (1 + S ^ 2) + 2 * S * b) : 0 ≤ a * (1 + s ^ 2) + 2 * s * b := by
  have hS : 0 < S := lt_of_lt_of_le hs hsS
  have h1 : 0 ≤ a * (S - s) * (1 - s * S) :=
    mul_nonneg (mul_nonneg ha.le (by linarith)) (by nlinarith)
  have h2 : 0 ≤ S * (a * (1 + s ^ 2) + 2 * s * b) := by
    have key : S * (a * (1 + s ^ 2) + 2 * s * b) =
        s * (a * (1 + S ^ 2) + 2 * S * b) + a * (S - s) * (1 - s * S) := by ring
    rw [key]
    exact add_nonneg (mul_nonneg hs.le h) h1
  exact (mul_nonneg_iff_of_pos_left hS).mp h2

/-- The smaller root of `S² - 2ρS + 1` for `ρ > 1`, and the radial area up to it. -/
theorem s13c_pb_root {ρ : ℝ} (hρ : 1 < ρ) :
    0 < ρ - √(ρ ^ 2 - 1) ∧ ρ - √(ρ ^ 2 - 1) < 1 ∧
      (ρ - √(ρ ^ 2 - 1)) ^ 2 - 2 * ρ * (ρ - √(ρ ^ 2 - 1)) + 1 = 0 ∧
      2 * (ρ - √(ρ ^ 2 - 1)) ^ 2 / (1 - (ρ - √(ρ ^ 2 - 1)) ^ 2) = ρ / √(ρ ^ 2 - 1) - 1 := by
  have hpos : 0 < ρ ^ 2 - 1 := by nlinarith
  have hr0 : 0 < √(ρ ^ 2 - 1) := Real.sqrt_pos.mpr hpos
  have hr2 : √(ρ ^ 2 - 1) ^ 2 = ρ ^ 2 - 1 := Real.sq_sqrt hpos.le
  have hrρ : √(ρ ^ 2 - 1) < ρ := by nlinarith
  have hS0 : 0 < ρ - √(ρ ^ 2 - 1) := by linarith
  have hS1 : ρ - √(ρ ^ 2 - 1) < 1 := by nlinarith
  have h1 : 1 - (ρ - √(ρ ^ 2 - 1)) ^ 2 = 2 * √(ρ ^ 2 - 1) * (ρ - √(ρ ^ 2 - 1)) := by
    linear_combination hr2
  refine ⟨hS0, hS1, by linear_combination hr2, ?_⟩
  rw [h1]
  field_simp

/-- The radial hyperbolic area of a chart ray up to radius `S < 1`. -/
theorem s13c_pb_radial {S : ℝ} (hS0 : 0 ≤ S) (hS1 : S < 1) :
    ∫⁻ s in Ioo (0 : ℝ) S, ENNReal.ofReal (4 * s / (1 - s ^ 2) ^ 2) = ENNReal.ofReal (2 * S ^ 2 / (1 - S ^ 2)) := by
  have hne : ∀ s ∈ Icc (0 : ℝ) S, 1 - s ^ 2 ≠ 0 := by
    intro s hs
    have : s ^ 2 < 1 := by nlinarith [hs.1, hs.2]
    linarith
  have hcont : ContinuousOn (fun s : ℝ => 4 * s / (1 - s ^ 2) ^ 2) (Icc 0 S) :=
    ContinuousOn.div (by fun_prop) (by fun_prop) fun s hs => pow_ne_zero 2 (hne s hs)
  have hint : IntegrableOn (fun s : ℝ => 4 * s / (1 - s ^ 2) ^ 2) (Ioo 0 S) :=
    (hcont.integrableOn_Icc).mono_set Ioo_subset_Icc_self
  rw [← ofReal_integral_eq_lintegral_ofReal hint
    (ae_restrict_of_forall_mem measurableSet_Ioo fun s hs => div_nonneg (by linarith [hs.1]) (sq_nonneg _)),
    ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hS0]
  have hderiv : ∀ s ∈ uIcc (0 : ℝ) S, HasDerivAt (fun s : ℝ => 2 / (1 - s ^ 2)) (4 * s / (1 - s ^ 2) ^ 2) s := by
    intro s hs
    rw [uIcc_of_le hS0] at hs
    have h := (((hasDerivAt_id s).pow 2).const_sub 1).inv (hne s hs)
    have h2 := h.const_mul 2
    convert h2 using 1
    · ext s
      simp [div_eq_mul_inv]
    · simp only [Pi.pow_apply, id_eq, id]
      field_simp
      ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hcont.intervalIntegrable_of_Icc hS0)]
  congr 1
  have : 1 - S ^ 2 ≠ 0 := hne S ⟨hS0, le_rfl⟩
  field_simp
  ring

/-- The angular integral over the visible directions of a face: with `k > 1` there is `t₁ ∈ (0, π/2)` with
`k cos t₁ > 1` and `∫_{-t₁}^{t₁} (k cos t / √(k² cos² t - 1) - 1) dt = π - 1 - 2 t₁`. -/
theorem s13c_pb_ang {k : ℝ} (hk : 1 < k) :
    ∃ t1 : ℝ, 0 < t1 ∧ t1 < π / 2 ∧ 1 < k * Real.cos t1 ∧
      ∫⁻ t in Ioo (-t1) t1, ENNReal.ofReal (k * Real.cos t / √((k * Real.cos t) ^ 2 - 1) - 1) =
        ENNReal.ofReal (π - 1 - 2 * t1) := by
  have hk0 : 0 < k := by linarith
  have hkk : 0 < k ^ 2 - 1 := by nlinarith
  set c0 := Real.cos (1 / 2) with hc0
  have hc0pos : 0 < c0 := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith [Real.pi_gt_three]⟩
  have hc0lt : c0 < 1 := by
    rw [hc0]
    have h := Real.cos_lt_cos_of_nonneg_of_le_pi (le_refl 0) (by linarith [Real.pi_gt_three]) (by norm_num : (0 : ℝ) < 1 / 2)
    rwa [Real.cos_zero] at h
  set w := c0 * √(k ^ 2 - 1) / k with hw
  have hsq : √(k ^ 2 - 1) < k := by
    rw [Real.sqrt_lt' hk0]
    linarith
  have hw0 : 0 < w := by positivity
  have hw1 : w < c0 := by
    rw [hw, div_lt_iff₀ hk0]
    nlinarith [Real.sqrt_nonneg (k ^ 2 - 1)]
  set t1 := Real.arcsin w with ht1
  have hsin : Real.sin t1 = w := Real.sin_arcsin (by linarith) (by linarith)
  have ht10 : 0 < t1 := Real.arcsin_pos.mpr hw0
  have harc0 : Real.arcsin c0 = π / 2 - 1 / 2 := by
    rw [Real.arcsin_eq_pi_div_two_sub_arccos, hc0, Real.arccos_cos (by norm_num) (by linarith [Real.pi_gt_three])]
  have ht1lt : t1 < π / 2 - 1 / 2 := by
    rw [← harc0]
    exact Real.arcsin_lt_arcsin (by linarith) hw1 (by linarith)
  have ht1pi : t1 < π / 2 := by linarith
  have hcos1 : 0 < Real.cos t1 := Real.cos_pos_of_mem_Ioo ⟨by linarith, ht1pi⟩
  have hkc : (k * Real.cos t1) ^ 2 - 1 = (k ^ 2 - 1) * (1 - c0 ^ 2) := by
    have h1 : Real.cos t1 ^ 2 = 1 - w ^ 2 := by rw [← hsin]; linarith [Real.cos_sq_add_sin_sq t1]
    have h2 : √(k ^ 2 - 1) ^ 2 = k ^ 2 - 1 := Real.sq_sqrt hkk.le
    rw [mul_pow, h1, hw, div_pow, mul_pow, h2]
    field_simp
    ring
  have hkc1 : 1 < k * Real.cos t1 := by
    have h : 0 < (k * Real.cos t1) ^ 2 - 1 := by rw [hkc]; exact mul_pos hkk (by nlinarith)
    nlinarith [mul_pos hk0 hcos1]
  refine ⟨t1, ht10, ht1pi, hkc1, ?_⟩
  -- on `[-t₁, t₁]` the integrand is continuous and nonnegative
  have hcosge : ∀ t ∈ Icc (-t1) t1, Real.cos t1 ≤ Real.cos t := by
    intro t ht
    rw [← Real.cos_abs t]
    exact Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg t) (by linarith [Real.pi_gt_three])
      (abs_le.mpr ⟨ht.1, ht.2⟩)
  have hrad : ∀ t ∈ Icc (-t1) t1, 0 < (k * Real.cos t) ^ 2 - 1 := by
    intro t ht
    have h := hcosge t ht
    nlinarith [mul_le_mul_of_nonneg_left h hk0.le]
  have hcont : ContinuousOn (fun t : ℝ => k * Real.cos t / √((k * Real.cos t) ^ 2 - 1) - 1) (Icc (-t1) t1) := by
    refine ContinuousOn.sub (ContinuousOn.div (by fun_prop) (by fun_prop) fun t ht => ?_) continuousOn_const
    exact (Real.sqrt_pos.mpr (hrad t ht)).ne'
  have hnn : ∀ t ∈ Icc (-t1) t1, 0 ≤ k * Real.cos t / √((k * Real.cos t) ^ 2 - 1) - 1 := by
    intro t ht
    have h := hrad t ht
    have hkct : 0 < k * Real.cos t := by nlinarith [mul_le_mul_of_nonneg_left (hcosge t ht) hk0.le]
    have hs : √((k * Real.cos t) ^ 2 - 1) < k * Real.cos t := by
      rw [Real.sqrt_lt' hkct]
      linarith
    rw [sub_nonneg, le_div_iff₀ (Real.sqrt_pos.mpr h), one_mul]
    exact hs.le
  have hint : IntegrableOn (fun t : ℝ => k * Real.cos t / √((k * Real.cos t) ^ 2 - 1) - 1) (Ioo (-t1) t1) :=
    (hcont.integrableOn_Icc).mono_set Ioo_subset_Icc_self
  rw [← ofReal_integral_eq_lintegral_ofReal hint
    (ae_restrict_of_forall_mem measurableSet_Ioo fun t ht => hnn t (Ioo_subset_Icc_self ht)),
    ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le (by linarith)]
  -- antiderivative `arcsin (k sin t / √(k² - 1)) - t`
  have hsk : 0 < √(k ^ 2 - 1) := Real.sqrt_pos.mpr hkk
  have hval : k * Real.sin t1 / √(k ^ 2 - 1) = c0 := by
    rw [hsin, hw]
    field_simp
  have hu : ∀ t ∈ Icc (-t1) t1, |k * Real.sin t / √(k ^ 2 - 1)| ≤ c0 := by
    intro t ht
    have hta : |t| ≤ t1 := abs_le.mpr ⟨by linarith [ht.1], ht.2⟩
    have hsabs : |Real.sin t| = Real.sin |t| := by
      rcases le_or_gt 0 t with h | h
      · rw [abs_of_nonneg h, abs_of_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi h (by linarith [ht.2, Real.pi_pos]))]
      · have h2 : 0 ≤ Real.sin (-t) := Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith [ht.1, Real.pi_pos])
        rw [Real.sin_neg] at h2
        rw [abs_of_neg h, abs_of_nonpos (by linarith), Real.sin_neg]
    have hsint : |Real.sin t| ≤ Real.sin t1 := by
      rw [hsabs]
      exact Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith [abs_nonneg t]) ht1pi.le hta
    rw [abs_div, abs_mul, abs_of_pos hk0, abs_of_pos hsk, div_le_iff₀ hsk]
    rw [div_eq_iff hsk.ne'] at hval
    nlinarith [mul_le_mul_of_nonneg_left hsint hk0.le]
  have hderiv : ∀ t ∈ uIcc (-t1) t1, HasDerivAt (fun t : ℝ => Real.arcsin (k * Real.sin t / √(k ^ 2 - 1)) - t)
      (k * Real.cos t / √((k * Real.cos t) ^ 2 - 1) - 1) t := by
    intro t ht
    rw [uIcc_of_le (by linarith)] at ht
    have hut := hu t ht
    have hu1 : k * Real.sin t / √(k ^ 2 - 1) ≠ 1 := fun h => by rw [h, abs_one] at hut; linarith
    have hu2 : k * Real.sin t / √(k ^ 2 - 1) ≠ -1 := fun h => by rw [h, abs_neg, abs_one] at hut; linarith
    have h1 : HasDerivAt (fun t : ℝ => k * Real.sin t / √(k ^ 2 - 1)) (k * Real.cos t / √(k ^ 2 - 1)) t :=
      ((Real.hasDerivAt_sin t).const_mul k).div_const _
    have h2 := ((Real.hasDerivAt_arcsin hu2 hu1).comp t h1).sub (hasDerivAt_id t)
    convert h2 using 1
    · ext t
      simp [Function.comp]
    have hrt := hrad t ht
    have hid : 1 - (k * Real.sin t / √(k ^ 2 - 1)) ^ 2 = ((k * Real.cos t) ^ 2 - 1) / (k ^ 2 - 1) := by
      have h3 : √(k ^ 2 - 1) ^ 2 = k ^ 2 - 1 := Real.sq_sqrt hkk.le
      rw [div_pow, h3, eq_div_iff hkk.ne', sub_mul, one_mul, div_mul_cancel₀ _ hkk.ne']
      linear_combination (-k ^ 2) * Real.cos_sq_add_sin_sq t
    have hsq0 := (Real.sqrt_pos.mpr hrt).ne'
    rw [hid, Real.sqrt_div' _ hkk.le]
    field_simp
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hcont.intervalIntegrable_of_Icc (by linarith))]
  congr 1
  rw [Real.sin_neg, mul_neg, neg_div, Real.arcsin_neg, hval, harc0]
  ring

/-- Lebesgue integrals over the window `(-π, π]` of a `2π`-periodic function are invariant under shifts. -/
theorem s13c_pb_lshift (G : ℝ → ℝ≥0∞) (hper : ∀ θ, G (θ + 2 * π) = G θ) (c : ℝ) :
    ∫⁻ θ in Ioc (-π) π, G (θ + c) = ∫⁻ θ in Ioc (-π) π, G θ := by
  haveI : Fact (0 < 2 * π) := ⟨by positivity⟩
  have hP : Function.Periodic G (2 * π) := hper
  have e1 : ∀ t : ℝ, ∫⁻ θ in Ioc t (t + 2 * π), G θ = ∫⁻ b : AddCircle (2 * π), hP.lift b := by
    intro t
    rw [← AddCircle.lintegral_preimage (2 * π) t]
    rfl
  have e2 : ∫⁻ θ in Ioc (-π) π, G (θ + c) = ∫⁻ θ in Ioc (-π + c) (-π + c + 2 * π), G θ := by
    rw [← lintegral_indicator measurableSet_Ioc, ← lintegral_indicator measurableSet_Ioc,
      ← lintegral_add_right_eq_self (fun x => (Ioc (-π + c) (-π + c + 2 * π)).indicator G x) c]
    congr 1
    ext θ
    by_cases h : θ ∈ Ioc (-π) π
    · have h' : θ + c ∈ Ioc (-π + c) (-π + c + 2 * π) := ⟨by linarith [h.1], by linarith [h.2]⟩
      rw [Set.indicator_of_mem h, Set.indicator_of_mem h']
    · have h' : θ + c ∉ Ioc (-π + c) (-π + c + 2 * π) := fun h' => h ⟨by linarith [h'.1], by linarith [h'.2]⟩
      rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h']
  have e3 := e1 (-π)
  rw [show -π + 2 * π = π by ring] at e3
  rw [e2, e1, e3]

/-- The directions `t ∈ (-π, π]` with `cos t > cos t₁` (for `t₁ ∈ (0, π/2)`) are exactly `(-t₁, t₁)`. -/
theorem s13c_pb_cosset {t1 : ℝ} (h0 : 0 < t1) (h1 : t1 < π / 2) :
    {t : ℝ | t ∈ Ioc (-π) π ∧ Real.cos t1 < Real.cos t} = Ioo (-t1) t1 := by
  ext t
  simp only [mem_setOf_eq, mem_Ioo, mem_Ioc]
  constructor
  · rintro ⟨⟨ha, hb⟩, hc⟩
    by_contra hn
    have habs : t1 ≤ |t| := by
      rcases le_or_gt t 0 with ht | ht
      · rw [abs_of_nonpos ht]
        by_contra h'
        exact hn ⟨by linarith, by linarith⟩
      · rw [abs_of_pos ht]
        by_contra h'
        exact hn ⟨by linarith, by linarith⟩
    have hle := Real.cos_le_cos_of_nonneg_of_le_pi h0.le (abs_le.mpr ⟨by linarith, hb⟩) habs
    rw [Real.cos_abs] at hle
    linarith
  · rintro ⟨ha, hb⟩
    refine ⟨⟨by linarith [Real.pi_gt_three], by linarith [Real.pi_gt_three]⟩, ?_⟩
    rw [← Real.cos_abs t]
    exact Real.cos_lt_cos_of_nonneg_of_le_pi (abs_nonneg t) (by linarith [Real.pi_gt_three])
      (abs_lt.mpr ⟨ha, hb⟩)

/-- A Dirichlet half-plane `{d(·, p) ≤ d(·, x)}` in the disc chart at an arbitrary centre `w`: it reads
`0 ≤ F (1 + s²) + 2 s Re (B e^{iθ})`, where `F ≥ 0` exactly when `w` lies in the half-plane. -/
theorem s13c_ga_chart (w p x : UpperHalfPlane) :
    ∃ B : ℂ, (dist w p ≤ dist w x →
        0 ≤ ((w.re - x.re) ^ 2 + (w.im - x.im) ^ 2) * p.im - ((w.re - p.re) ^ 2 + (w.im - p.im) ^ 2) * x.im) ∧
      ∀ (θ s : ℝ) (hs0 : 0 ≤ s) (hs1 : s < 1),
        (dist (⟨_, s13c_cy_rim w θ s hs0 hs1⟩ : UpperHalfPlane) p ≤
            dist (⟨_, s13c_cy_rim w θ s hs0 hs1⟩ : UpperHalfPlane) x ↔
          0 ≤ (((w.re - x.re) ^ 2 + (w.im - x.im) ^ 2) * p.im - ((w.re - p.re) ^ 2 + (w.im - p.im) ^ 2) * x.im) *
            (1 + s ^ 2) + 2 * s * (B * Complex.exp ((θ : ℂ) * I)).re) := by
  obtain ⟨B, hBre, hBim⟩ : ∃ B : ℂ,
      B.re = -((p.im - x.im) * (w.re ^ 2 - w.im ^ 2) + (-2 * (x.re * p.im - p.re * x.im)) * w.re +
        ((x.re ^ 2 + x.im ^ 2) * p.im - (p.re ^ 2 + p.im ^ 2) * x.im)) ∧
      B.im = 2 * (p.im - x.im) * w.re * w.im + (-2 * (x.re * p.im - p.re * x.im)) * w.im :=
    ⟨⟨_, _⟩, rfl, rfl⟩
  refine ⟨B, fun h => ?_, fun θ s hs0 hs1 => ?_⟩
  · have h1 := (LiZhongQC.s82dx_dist_le_iff w p x).mp h
    simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im, UpperHalfPlane.coe_re,
      UpperHalfPlane.coe_im] at h1
    nlinarith [h1]
  have hDn := s13c_cy_den θ s hs0 hs1
  have hn : 0 < ‖(1 : ℂ) - (s : ℂ) * Complex.exp ((θ : ℂ) * I)‖ ^ 2 := pow_pos (norm_pos_iff.mpr hDn) 2
  have hsub : ∀ q : ℂ, ((w : ℂ) - conj (w : ℂ) * ((s : ℂ) * Complex.exp ((θ : ℂ) * I))) /
      (1 - (s : ℂ) * Complex.exp ((θ : ℂ) * I)) - q =
      ((w : ℂ) - conj (w : ℂ) * ((s : ℂ) * Complex.exp ((θ : ℂ) * I)) -
        q * (1 - (s : ℂ) * Complex.exp ((θ : ℂ) * I))) / (1 - (s : ℂ) * Complex.exp ((θ : ℂ) * I)) := by
    intro q
    field_simp
  rw [LiZhongQC.s82dx_dist_le_iff]
  show ‖((w : ℂ) - conj (w : ℂ) * ((s : ℂ) * Complex.exp ((θ : ℂ) * I))) /
      (1 - (s : ℂ) * Complex.exp ((θ : ℂ) * I)) - (p : ℂ)‖ ^ 2 * x.im ≤
    ‖((w : ℂ) - conj (w : ℂ) * ((s : ℂ) * Complex.exp ((θ : ℂ) * I))) /
      (1 - (s : ℂ) * Complex.exp ((θ : ℂ) * I)) - (x : ℂ)‖ ^ 2 * p.im ↔ _
  rw [hsub, hsub, norm_div, norm_div, div_pow, div_pow, div_mul_eq_mul_div, div_mul_eq_mul_div,
    div_le_div_iff_of_pos_right hn, ← sub_nonneg]
  have hc := Real.cos_sq_add_sin_sq θ
  have hR : (B * Complex.exp ((θ : ℂ) * I)).re = B.re * Real.cos θ - B.im * Real.sin θ := by
    simp [Complex.mul_re, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
  have hkey : ‖(w : ℂ) - conj (w : ℂ) * ((s : ℂ) * Complex.exp ((θ : ℂ) * I)) -
          (x : ℂ) * (1 - (s : ℂ) * Complex.exp ((θ : ℂ) * I))‖ ^ 2 * p.im -
        ‖(w : ℂ) - conj (w : ℂ) * ((s : ℂ) * Complex.exp ((θ : ℂ) * I)) -
          (p : ℂ) * (1 - (s : ℂ) * Complex.exp ((θ : ℂ) * I))‖ ^ 2 * x.im =
      (((w.re - x.re) ^ 2 + (w.im - x.im) ^ 2) * p.im - ((w.re - p.re) ^ 2 + (w.im - p.im) ^ 2) * x.im) *
        (1 + s ^ 2) + 2 * s * (B * Complex.exp ((θ : ℂ) * I)).re := by
    rw [hR, hBre, hBim, Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im,
      Complex.one_re, Complex.one_im, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]
    linear_combination ((((w.re - x.re) ^ 2 + (w.im - x.im) ^ 2) * p.im -
      ((w.re - p.re) ^ 2 + (w.im - p.im) ^ 2) * x.im) * s ^ 2) * hc
  rw [hkey]

/-- The initial-segment property with `a ≥ 0`. -/
theorem s13c_ga_seg {a b S s : ℝ} (ha : 0 ≤ a) (hs : 0 < s) (hsS : s ≤ S) (hS1 : S ≤ 1)
    (h : 0 ≤ a * (1 + S ^ 2) + 2 * S * b) : 0 ≤ a * (1 + s ^ 2) + 2 * s * b := by
  have hS : 0 < S := lt_of_lt_of_le hs hsS
  have h1 : 0 ≤ a * (S - s) * (1 - s * S) := mul_nonneg (mul_nonneg ha (by linarith)) (by nlinarith)
  have h2 : 0 ≤ S * (a * (1 + s ^ 2) + 2 * s * b) := by
    have key : S * (a * (1 + s ^ 2) + 2 * s * b) =
        s * (a * (1 + S ^ 2) + 2 * S * b) + a * (S - s) * (1 - s * S) := by ring
    rw [key]
    exact add_nonneg (mul_nonneg hs.le h) h1
  exact (mul_nonneg_iff_of_pos_left hS).mp h2

/-- Trigonometric interpolation: `sin (b - a) f(θ) = sin (b - θ) f(a) + sin (θ - a) f(b)` for
`f(θ) = Re (E e^{iθ})`. -/
theorem s13c_ga_interp_eq (E : ℂ) (a b θ : ℝ) :
    Real.sin (b - a) * (E * Complex.exp ((θ : ℂ) * I)).re =
      Real.sin (b - θ) * (E * Complex.exp ((a : ℂ) * I)).re + Real.sin (θ - a) * (E * Complex.exp ((b : ℂ) * I)).re := by
  simp only [Complex.mul_re, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im, Real.sin_sub]
  ring

/-- A half-circle condition holding at both ends of an arc shorter than `π` holds along the arc. -/
theorem s13c_ga_interp (E : ℂ) {a b θ : ℝ} (hab : a < b) (hπ : b - a < π) (h1 : a ≤ θ) (h2 : θ ≤ b)
    (ha : 0 ≤ (E * Complex.exp ((a : ℂ) * I)).re) (hb : 0 ≤ (E * Complex.exp ((b : ℂ) * I)).re) :
    0 ≤ (E * Complex.exp ((θ : ℂ) * I)).re := by
  have hs : 0 < Real.sin (b - a) := Real.sin_pos_of_pos_of_lt_pi (by linarith) hπ
  have hs1 : 0 ≤ Real.sin (b - θ) := Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith)
  have hs2 : 0 ≤ Real.sin (θ - a) := Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith)
  have h := s13c_ga_interp_eq E a b θ
  have h3 : 0 ≤ Real.sin (b - a) * (E * Complex.exp ((θ : ℂ) * I)).re := by
    rw [h]
    exact add_nonneg (mul_nonneg hs1 ha) (mul_nonneg hs2 hb)
  exact (mul_nonneg_iff_of_pos_left hs).mp h3

/-- The strict version for the chart circle: `1 < Re (c̄ e^{iθ})` along an arc shorter than `π`. -/
theorem s13c_ga_interp1 (c : ℂ) {a b θ : ℝ} (hab : a < b) (hπ : b - a < π) (h1 : a ≤ θ) (h2 : θ ≤ b)
    (ha : 1 < (conj c * Complex.exp ((a : ℂ) * I)).re) (hb : 1 < (conj c * Complex.exp ((b : ℂ) * I)).re) :
    1 < (conj c * Complex.exp ((θ : ℂ) * I)).re := by
  have hs : 0 < Real.sin (b - a) := Real.sin_pos_of_pos_of_lt_pi (by linarith) hπ
  have hs1 : 0 ≤ Real.sin (b - θ) := Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith)
  have hs2 : 0 ≤ Real.sin (θ - a) := Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith)
  have h := s13c_ga_interp_eq (conj c) a b θ
  -- `sin x + sin y ≥ sin (x + y)` on `[0, π]`
  have hsum : Real.sin (b - a) ≤ Real.sin (b - θ) + Real.sin (θ - a) := by
    have e : b - a = (b - θ) + (θ - a) := by ring
    rw [e, Real.sin_add]
    have c1 := Real.cos_le_one (θ - a)
    have c2 := Real.cos_le_one (b - θ)
    nlinarith [mul_le_mul_of_nonneg_left c1 hs1, mul_le_mul_of_nonneg_left c2 hs2]
  -- at least one weight is positive
  have hpos : 0 < Real.sin (b - θ) * ((conj c * Complex.exp ((a : ℂ) * I)).re - 1) +
      Real.sin (θ - a) * ((conj c * Complex.exp ((b : ℂ) * I)).re - 1) := by
    rcases lt_or_eq_of_le h2 with h2' | h2'
    · have hp : 0 < Real.sin (b - θ) := Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
      nlinarith [mul_pos hp (sub_pos.mpr ha), mul_nonneg hs2 (sub_pos.mpr hb).le]
    · rw [h2', sub_self, Real.sin_zero, zero_mul, zero_add]
      exact mul_pos hs (sub_pos.mpr hb)
  have h3 : Real.sin (b - a) * 1 < Real.sin (b - a) * (conj c * Complex.exp ((θ : ℂ) * I)).re := by
    rw [h]
    nlinarith
  exact lt_of_mul_lt_mul_left h3 hs.le

/-- **The fan.** Seen from a point `w ∈ D`, two points of `D` at chart directions `d_a < d_b < d_a + π`
span a fan inside `D`: there is a chart circle `|ζ|² + 1 = 2 Re (c̄ ζ)` through both, and every chart ray in a
direction `θ ∈ [d_a, d_b]` lies in `D` up to that circle. -/
theorem s13c_ga_fan {Γ' : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p w : UpperHalfPlane}
    (D : Set UpperHalfPlane) (hDdef : D = {w : UpperHalfPlane | ∀ g ∈ Γ', dist w p ≤ dist w (g • p)})
    (hwD : w ∈ D) {da db ra rb : ℝ} (hra0 : 0 < ra) (hra1 : ra < 1) (hrb0 : 0 < rb) (hrb1 : rb < 1)
    (hd : da < db) (hdπ : db - da < π)
    (hA : ((w : ℂ) - conj (w : ℂ) * ((ra : ℂ) * Complex.exp ((da : ℂ) * I))) /
      (1 - (ra : ℂ) * Complex.exp ((da : ℂ) * I)) ∈ ((↑) : UpperHalfPlane → ℂ) '' D)
    (hB : ((w : ℂ) - conj (w : ℂ) * ((rb : ℂ) * Complex.exp ((db : ℂ) * I))) /
      (1 - (rb : ℂ) * Complex.exp ((db : ℂ) * I)) ∈ ((↑) : UpperHalfPlane → ℂ) '' D) :
    ∃ c : ℂ, ra ^ 2 - 2 * (conj c * Complex.exp ((da : ℂ) * I)).re * ra + 1 = 0 ∧
      rb ^ 2 - 2 * (conj c * Complex.exp ((db : ℂ) * I)).re * rb + 1 = 0 ∧
      ∀ θ ∈ Icc da db, 1 < (conj c * Complex.exp ((θ : ℂ) * I)).re ∧
        ∀ s : ℝ, 0 < s → s ≤ (conj c * Complex.exp ((θ : ℂ) * I)).re -
            √((conj c * Complex.exp ((θ : ℂ) * I)).re ^ 2 - 1) →
          ((w : ℂ) - conj (w : ℂ) * ((s : ℂ) * Complex.exp ((θ : ℂ) * I))) /
            (1 - (s : ℂ) * Complex.exp ((θ : ℂ) * I)) ∈ ((↑) : UpperHalfPlane → ℂ) '' D := by
  have hDm : ∀ x : UpperHalfPlane, x ∈ D ↔ ∀ g ∈ Γ', dist x p ≤ dist x (g • p) := by
    intro x
    simp only [hDdef, mem_setOf_eq]
  have hsd : 0 < Real.sin (db - da) := Real.sin_pos_of_pos_of_lt_pi (by linarith) hdπ
  set ρa := (1 + ra ^ 2) / (2 * ra) with hρa
  set ρb := (1 + rb ^ 2) / (2 * rb) with hρb
  -- the circle through both points
  obtain ⟨c, hc⟩ : ∃ c : ℂ, c = ⟨(ρa * Real.sin db - ρb * Real.sin da) / Real.sin (db - da),
      -((ρa * Real.cos db - ρb * Real.cos da) / Real.sin (db - da))⟩ := ⟨_, rfl⟩
  have hcre : ∀ t : ℝ, (conj c * Complex.exp ((t : ℂ) * I)).re =
      ((ρa * Real.sin db - ρb * Real.sin da) * Real.cos t -
        (ρa * Real.cos db - ρb * Real.cos da) * Real.sin t) / Real.sin (db - da) := by
    intro t
    rw [hc]
    simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im, Complex.exp_ofReal_mul_I_re,
      Complex.exp_ofReal_mul_I_im]
    field_simp
  have hsd' : Real.sin db * Real.cos da - Real.cos db * Real.sin da ≠ 0 := by
    rw [← Real.sin_sub]
    exact hsd.ne'
  have hca : (conj c * Complex.exp ((da : ℂ) * I)).re = ρa := by
    rw [hcre, Real.sin_sub, div_eq_iff hsd']
    ring
  have hcb : (conj c * Complex.exp ((db : ℂ) * I)).re = ρb := by
    rw [hcre, Real.sin_sub, div_eq_iff hsd']
    ring
  have hρa1 : 1 < ρa := by
    rw [hρa, lt_div_iff₀ (by positivity)]
    nlinarith [mul_pos (sub_pos.mpr hra1) (sub_pos.mpr hra1)]
  have hρb1 : 1 < ρb := by
    rw [hρb, lt_div_iff₀ (by positivity)]
    nlinarith [mul_pos (sub_pos.mpr hrb1) (sub_pos.mpr hrb1)]
  have hρa2 : 2 * ρa * ra = 1 + ra ^ 2 := by
    rw [hρa]
    field_simp
  have hρb2 : 2 * ρb * rb = 1 + rb ^ 2 := by
    rw [hρb]
    field_simp
  have hcira : ra ^ 2 - 2 * ρa * ra + 1 = 0 := by linear_combination -hρa2
  have hcirb : rb ^ 2 - 2 * ρb * rb + 1 = 0 := by linear_combination -hρb2
  refine ⟨c, by rw [hca]; exact hcira, by rw [hcb]; exact hcirb, fun θ hθ => ?_⟩
  have hρ := s13c_ga_interp1 c hd hdπ hθ.1 hθ.2 (by rw [hca]; exact hρa1) (by rw [hcb]; exact hρb1)
  refine ⟨hρ, fun s hs0 hsS => ?_⟩
  obtain ⟨hS0, hS1, hSeq, -⟩ := s13c_pb_root hρ
  have hs1 : s < 1 := lt_of_le_of_lt hsS hS1
  rw [s13c_cy_memiff w θ s hs0.le hs1 D, hDm]
  intro g hg
  obtain ⟨B, hF, hBc⟩ := s13c_ga_chart w p (g • p)
  have hF0 := hF ((hDm w).mp hwD g hg)
  set F := ((w.re - (g • p).re) ^ 2 + (w.im - (g • p).im) ^ 2) * p.im -
    ((w.re - p.re) ^ 2 + (w.im - p.im) ^ 2) * (g • p).im with hFdef
  -- the condition at the two given points
  have hEa : 0 ≤ (((F : ℂ) * conj c + B) * Complex.exp ((da : ℂ) * I)).re := by
    have h := (hBc da ra hra0.le hra1).mp ((hDm _).mp ((s13c_cy_memiff w da ra hra0.le hra1 D).mp hA) g hg)
    have e : ((F : ℂ) * conj c + B) * Complex.exp ((da : ℂ) * I) =
        (F : ℂ) * (conj c * Complex.exp ((da : ℂ) * I)) + B * Complex.exp ((da : ℂ) * I) := by ring
    rw [e, Complex.add_re, Complex.re_ofReal_mul, hca]
    have e2 : F * (1 + ra ^ 2) = 2 * ra * (F * ρa) := by linear_combination -F * hρa2
    rw [e2] at h
    have h3 : 0 ≤ 2 * ra * (F * ρa + (B * Complex.exp ((da : ℂ) * I)).re) := by linarith
    exact (mul_nonneg_iff_of_pos_left (by positivity)).mp h3
  have hEb : 0 ≤ (((F : ℂ) * conj c + B) * Complex.exp ((db : ℂ) * I)).re := by
    have h := (hBc db rb hrb0.le hrb1).mp ((hDm _).mp ((s13c_cy_memiff w db rb hrb0.le hrb1 D).mp hB) g hg)
    have e : ((F : ℂ) * conj c + B) * Complex.exp ((db : ℂ) * I) =
        (F : ℂ) * (conj c * Complex.exp ((db : ℂ) * I)) + B * Complex.exp ((db : ℂ) * I) := by ring
    rw [e, Complex.add_re, Complex.re_ofReal_mul, hcb]
    have e2 : F * (1 + rb ^ 2) = 2 * rb * (F * ρb) := by linear_combination -F * hρb2
    rw [e2] at h
    have h3 : 0 ≤ 2 * rb * (F * ρb + (B * Complex.exp ((db : ℂ) * I)).re) := by linarith
    exact (mul_nonneg_iff_of_pos_left (by positivity)).mp h3
  have hEθ := s13c_ga_interp _ hd hdπ hθ.1 hθ.2 hEa hEb
  -- hence the condition at the circle point, and then along the ray
  set ρ := (conj c * Complex.exp ((θ : ℂ) * I)).re with hρdef
  set S := ρ - √(ρ ^ 2 - 1) with hSdef
  have hGS : 0 ≤ F * (1 + S ^ 2) + 2 * S * (B * Complex.exp ((θ : ℂ) * I)).re := by
    have e : ((F : ℂ) * conj c + B) * Complex.exp ((θ : ℂ) * I) =
        (F : ℂ) * (conj c * Complex.exp ((θ : ℂ) * I)) + B * Complex.exp ((θ : ℂ) * I) := by ring
    rw [e, Complex.add_re, Complex.re_ofReal_mul, ← hρdef] at hEθ
    have e2 : F * (1 + S ^ 2) = 2 * S * (F * ρ) := by linear_combination F * hSeq
    rw [e2]
    have h3 := mul_nonneg (by linarith : (0 : ℝ) ≤ 2 * S) hEθ
    linarith
  exact (hBc θ s hs0.le hs1).mpr (s13c_ga_seg hF0 hs0 hsS hS1.le hGS)

/-- `Re (c̄ e^{iθ}) = |c| cos (θ - arg c)`. -/
theorem s13c_ga_rho (c : ℂ) (θ : ℝ) :
    (conj c * Complex.exp ((θ : ℂ) * I)).re = ‖c‖ * Real.cos (θ - Complex.arg c) := by
  rw [Real.cos_sub]
  simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im, Complex.exp_ofReal_mul_I_re,
    Complex.exp_ofReal_mul_I_im]
  rw [← Complex.norm_mul_cos_arg c, ← Complex.norm_mul_sin_arg c]
  ring

/-- **The angular area under a chart circle** over `[a, b]`, where the circle is visible (`Re (c̄ e^{iθ}) > 1`):
with `ψ θ = arcsin (|c| sin (θ - arg c) / √(|c|² - 1))`, the integral of `ρ/√(ρ² - 1) - 1` is
`ψ b - ψ a - (b - a)`, a nonnegative number. -/
theorem s13c_ga_ang (c : ℂ) (hk : 1 < ‖c‖) {a b : ℝ} (hab : a ≤ b)
    (hρ : ∀ θ ∈ Icc a b, 1 < (conj c * Complex.exp ((θ : ℂ) * I)).re) :
    ∫⁻ θ in Ioo a b, ENNReal.ofReal ((conj c * Complex.exp ((θ : ℂ) * I)).re /
        √((conj c * Complex.exp ((θ : ℂ) * I)).re ^ 2 - 1) - 1) =
      ENNReal.ofReal (Real.arcsin (‖c‖ * Real.sin (b - Complex.arg c) / √(‖c‖ ^ 2 - 1)) -
        Real.arcsin (‖c‖ * Real.sin (a - Complex.arg c) / √(‖c‖ ^ 2 - 1)) - (b - a)) ∧
    0 ≤ Real.arcsin (‖c‖ * Real.sin (b - Complex.arg c) / √(‖c‖ ^ 2 - 1)) -
        Real.arcsin (‖c‖ * Real.sin (a - Complex.arg c) / √(‖c‖ ^ 2 - 1)) - (b - a) := by
  set k := ‖c‖ with hkdef
  have hk0 : 0 < k := by linarith
  have hkk : 0 < k ^ 2 - 1 := by nlinarith
  have hsk : 0 < √(k ^ 2 - 1) := Real.sqrt_pos.mpr hkk
  have hρ' : ∀ θ ∈ Icc a b, 1 < k * Real.cos (θ - Complex.arg c) := fun θ hθ => by
    rw [hkdef, ← s13c_ga_rho]
    exact hρ θ hθ
  simp_rw [s13c_ga_rho]
  have hrad : ∀ θ ∈ Icc a b, 0 < (k * Real.cos (θ - Complex.arg c)) ^ 2 - 1 := fun θ hθ => by
    nlinarith [hρ' θ hθ]
  have hcont : ContinuousOn (fun θ : ℝ => k * Real.cos (θ - Complex.arg c) /
      √((k * Real.cos (θ - Complex.arg c)) ^ 2 - 1) - 1) (Icc a b) := by
    refine ContinuousOn.sub (ContinuousOn.div (by fun_prop) (by fun_prop) fun θ hθ => ?_) continuousOn_const
    exact (Real.sqrt_pos.mpr (hrad θ hθ)).ne'
  have hnn : ∀ θ ∈ Icc a b, 0 ≤ k * Real.cos (θ - Complex.arg c) /
      √((k * Real.cos (θ - Complex.arg c)) ^ 2 - 1) - 1 := by
    intro θ hθ
    have h := hrad θ hθ
    have hkct := hρ' θ hθ
    have hs : √((k * Real.cos (θ - Complex.arg c)) ^ 2 - 1) < k * Real.cos (θ - Complex.arg c) := by
      rw [Real.sqrt_lt' (by linarith)]
      linarith
    rw [sub_nonneg, le_div_iff₀ (Real.sqrt_pos.mpr h), one_mul]
    exact hs.le
  have hu : ∀ θ ∈ Icc a b, |k * Real.sin (θ - Complex.arg c) / √(k ^ 2 - 1)| < 1 := by
    intro θ hθ
    have h := hrad θ hθ
    rw [abs_div, abs_of_pos hsk, div_lt_one hsk, ← sq_lt_sq₀ (abs_nonneg _) hsk.le, sq_abs,
      Real.sq_sqrt hkk.le]
    nlinarith [Real.sin_sq_add_cos_sq (θ - Complex.arg c)]
  have hderiv : ∀ θ ∈ uIcc a b, HasDerivAt
      (fun θ : ℝ => Real.arcsin (k * Real.sin (θ - Complex.arg c) / √(k ^ 2 - 1)) - θ)
      (k * Real.cos (θ - Complex.arg c) / √((k * Real.cos (θ - Complex.arg c)) ^ 2 - 1) - 1) θ := by
    intro θ hθ
    rw [uIcc_of_le hab] at hθ
    have hut := hu θ hθ
    have hu1 : k * Real.sin (θ - Complex.arg c) / √(k ^ 2 - 1) ≠ 1 := fun h => by
      rw [h, abs_one] at hut
      exact lt_irrefl _ hut
    have hu2 : k * Real.sin (θ - Complex.arg c) / √(k ^ 2 - 1) ≠ -1 := fun h => by
      rw [h, abs_neg, abs_one] at hut
      exact lt_irrefl _ hut
    have h0 : HasDerivAt (fun θ : ℝ => θ - Complex.arg c) 1 θ := (hasDerivAt_id θ).sub_const _
    have h1 : HasDerivAt (fun θ : ℝ => k * Real.sin (θ - Complex.arg c) / √(k ^ 2 - 1))
        (k * (Real.cos (θ - Complex.arg c) * 1) / √(k ^ 2 - 1)) θ :=
      (((Real.hasDerivAt_sin _).comp θ h0).const_mul k).div_const _
    have h2 := ((Real.hasDerivAt_arcsin hu2 hu1).comp θ h1).sub (hasDerivAt_id θ)
    convert h2 using 1
    · ext t
      simp [Function.comp]
    have hrt := hrad θ hθ
    have hid : 1 - (k * Real.sin (θ - Complex.arg c) / √(k ^ 2 - 1)) ^ 2 =
        ((k * Real.cos (θ - Complex.arg c)) ^ 2 - 1) / (k ^ 2 - 1) := by
      have h3 : √(k ^ 2 - 1) ^ 2 = k ^ 2 - 1 := Real.sq_sqrt hkk.le
      rw [div_pow, h3, eq_div_iff hkk.ne', sub_mul, one_mul, div_mul_cancel₀ _ hkk.ne']
      linear_combination (-k ^ 2) * Real.cos_sq_add_sin_sq (θ - Complex.arg c)
    have hsq0 := (Real.sqrt_pos.mpr hrt).ne'
    rw [hid, Real.sqrt_div' _ hkk.le]
    field_simp
  have hint : IntegrableOn (fun θ : ℝ => k * Real.cos (θ - Complex.arg c) /
      √((k * Real.cos (θ - Complex.arg c)) ^ 2 - 1) - 1) (Ioo a b) :=
    (hcont.integrableOn_Icc).mono_set Ioo_subset_Icc_self
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hcont.intervalIntegrable_of_Icc hab)
  have hval : ∫ θ in Ioo a b, (k * Real.cos (θ - Complex.arg c) /
      √((k * Real.cos (θ - Complex.arg c)) ^ 2 - 1) - 1) =
      Real.arcsin (k * Real.sin (b - Complex.arg c) / √(k ^ 2 - 1)) -
        Real.arcsin (k * Real.sin (a - Complex.arg c) / √(k ^ 2 - 1)) - (b - a) := by
    rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hab, hFTC]
    ring
  refine ⟨?_, ?_⟩
  · rw [← ofReal_integral_eq_lintegral_ofReal hint
      (ae_restrict_of_forall_mem measurableSet_Ioo fun t ht => hnn t (Ioo_subset_Icc_self ht)), hval]
  · rw [← hval]
    exact setIntegral_nonneg measurableSet_Ioo fun t ht => hnn t (Ioo_subset_Icc_self ht)

/-- The chart denominator `z - w̄` of two points of `ℍ` does not vanish. -/
theorem s13c_ga_ne (z w : UpperHalfPlane) : (z : ℂ) - conj (w : ℂ) ≠ 0 := by
  intro h
  have h1 := congrArg Complex.im h
  simp only [Complex.sub_im, Complex.conj_im, UpperHalfPlane.coe_im, Complex.zero_im] at h1
  linarith [z.im_pos, w.im_pos]

/-- The disc chart at `w` is inverted by the ray parametrization. -/
theorem s13c_ga_inv (w z : UpperHalfPlane) {s θ : ℝ}
    (h : ((z : ℂ) - w) / ((z : ℂ) - conj (w : ℂ)) = (s : ℂ) * Complex.exp ((θ : ℂ) * I)) :
    ((w : ℂ) - conj (w : ℂ) * ((s : ℂ) * Complex.exp ((θ : ℂ) * I))) /
      (1 - (s : ℂ) * Complex.exp ((θ : ℂ) * I)) = z := by
  have h1 := s13c_ga_ne z w
  have h2 := s13c_ga_ne w w
  have e1 : (1 : ℂ) - ((z : ℂ) - w) / ((z : ℂ) - conj (w : ℂ)) =
      ((w : ℂ) - conj (w : ℂ)) / ((z : ℂ) - conj (w : ℂ)) := by
    field_simp <;> ring
  have e2 : (w : ℂ) - conj (w : ℂ) * (((z : ℂ) - w) / ((z : ℂ) - conj (w : ℂ))) =
      (z : ℂ) * (((w : ℂ) - conj (w : ℂ)) / ((z : ℂ) - conj (w : ℂ))) := by
    field_simp <;> ring
  rw [← h, e2, e1, mul_div_cancel_right₀ _ (div_ne_zero h2 h1)]

/-- The disc chart takes values in the unit disc. -/
theorem s13c_ga_nlt (z w : UpperHalfPlane) : ‖((z : ℂ) - w) / ((z : ℂ) - conj (w : ℂ))‖ < 1 := by
  have h1 := s13c_ga_ne z w
  rw [norm_div, div_lt_one (norm_pos_iff.mpr h1), ← sq_lt_sq₀ (norm_nonneg _) (norm_nonneg _),
    Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.sub_im, Complex.conj_re, Complex.conj_im, UpperHalfPlane.coe_re,
    UpperHalfPlane.coe_im]
  nlinarith [mul_pos z.im_pos w.im_pos]

/-- Periodicity of the chart direction. -/
theorem s13c_ga_per (θ : ℝ) (k : ℤ) :
    Complex.exp (((θ + 2 * π * (k : ℝ) : ℝ) : ℂ) * I) = Complex.exp ((θ : ℂ) * I) := by
  have e : ((θ + 2 * π * (k : ℝ) : ℝ) : ℂ) * I = (θ : ℂ) * I + (k : ℂ) * (2 * π * I) := by
    push_cast
    ring
  rw [e, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

theorem s13c_ga_per2 (θ : ℝ) : Complex.exp (((θ + 2 * π : ℝ) : ℂ) * I) = Complex.exp ((θ : ℂ) * I) := by
  have h := s13c_ga_per θ 1
  rw [Int.cast_one, mul_one] at h
  exact h

/-- A union of translates of an arc by multiples of `2π` is `2π`-periodic. -/
theorem s13c_ga_Iper (a b θ : ℝ) :
    θ + 2 * π ∈ (⋃ k : ℤ, Ioo (a + 2 * π * k) (b + 2 * π * k)) ↔
      θ ∈ (⋃ k : ℤ, Ioo (a + 2 * π * k) (b + 2 * π * k)) := by
  simp only [mem_iUnion, mem_Ioo]
  constructor
  · rintro ⟨k, h1, h2⟩
    refine ⟨k - 1, ?_, ?_⟩
    · push_cast
      linarith
    · push_cast
      linarith
  · rintro ⟨k, h1, h2⟩
    refine ⟨k + 1, ?_, ?_⟩
    · push_cast
      linarith
    · push_cast
      linarith

/-- A periodic set containing an open arc of length `ℓ ≤ 2π` has at least measure `ℓ` in `(-π, π]`. -/
theorem s13c_ga_pmeas {G : Set ℝ} (hG : MeasurableSet G) (hper : ∀ θ, θ + 2 * π ∈ G ↔ θ ∈ G) {L ℓ : ℝ}
    (hℓ : ℓ ≤ 2 * π) (hsub : Ioo L (L + ℓ) ⊆ G) :
    ENNReal.ofReal ℓ ≤ volume {θ : ℝ | θ ∈ Ioc (-π) π ∧ θ ∈ G} := by
  rw [← s13c_cy_shift hG hper (L + π)]
  calc ENNReal.ofReal ℓ = volume (Ioo (-π) (-π + ℓ)) := by
        rw [Real.volume_Ioo]
        congr 1
        ring
    _ ≤ _ := measure_mono fun θ hθ => show θ ∈ Ioc (-π) π ∧ θ + (L + π) ∈ G from
        ⟨⟨hθ.1, by linarith [hθ.2]⟩, hsub ⟨by linarith [hθ.1], by linarith [hθ.2]⟩⟩

/-- Translation of an interval integral. -/
theorem s13c_ga_tint (f : ℝ → ℝ≥0∞) (a b c : ℝ) :
    ∫⁻ θ in Ioo a b, f (θ + c) = ∫⁻ θ in Ioo (a + c) (b + c), f θ := by
  rw [← lintegral_indicator measurableSet_Ioo, ← lintegral_indicator measurableSet_Ioo,
    ← lintegral_add_right_eq_self (fun x => (Ioo (a + c) (b + c)).indicator f x) c]
  congr 1
  ext θ
  by_cases h : θ ∈ Ioo a b
  · have h' : θ + c ∈ Ioo (a + c) (b + c) := ⟨by linarith [h.1], by linarith [h.2]⟩
    rw [Set.indicator_of_mem h, Set.indicator_of_mem h']
  · have h' : θ + c ∉ Ioo (a + c) (b + c) := fun h' => h ⟨by linarith [h'.1], by linarith [h'.2]⟩
    rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h']

/-- **One vertex per ray.** If `u` lies on the bisector of `p` and `x`, no point of the half-plane of `p` lies
farther out on the chart ray from `p` through `u`. -/
theorem s13c_ga_ray {p u v x : UpperHalfPlane} (hxp : x ≠ p) (hu : dist u p = dist u x)
    (hv : dist v p ≤ dist v x) {θ r1 r2 : ℝ} (h1 : 0 < r1) (h12 : r1 < r2) (h2 : r2 < 1)
    (hu' : ((u : ℂ) - p) / ((u : ℂ) - conj (p : ℂ)) = (r1 : ℂ) * Complex.exp ((θ : ℂ) * I))
    (hv' : ((v : ℂ) - p) / ((v : ℂ) - conj (p : ℂ)) = (r2 : ℂ) * Complex.exp ((θ : ℂ) * I)) : False := by
  obtain ⟨B, -, -, hB⟩ := s13c_pb_chart p x
  have hr1 : r1 < 1 := h12.trans h2
  have hU : (⟨_, s13c_cy_rim p θ r1 h1.le hr1⟩ : UpperHalfPlane) = u :=
    UpperHalfPlane.ext (s13c_ga_inv p u hu')
  have hV : (⟨_, s13c_cy_rim p θ r2 (h1.trans h12).le h2⟩ : UpperHalfPlane) = v :=
    UpperHalfPlane.ext (s13c_ga_inv p v hv')
  have f1 := (hB θ r1 h1.le hr1).1.mp (by rw [hU]; exact hu.le)
  have f1' := (hB θ r1 h1.le hr1).2.mp (by rw [hU]; exact hu.ge)
  have f2 := (hB θ r2 (h1.trans h12).le h2).1.mp (by rw [hV]; exact hv)
  have ha : 0 < ‖(p : ℂ) - x‖ ^ 2 * p.im :=
    mul_pos (pow_pos (norm_pos_iff.mpr fun h => hxp (UpperHalfPlane.ext (sub_eq_zero.mp h).symm)) 2) p.im_pos
  have e1 := le_antisymm f1' f1
  have e2 : r1 * (‖(p : ℂ) - x‖ ^ 2 * p.im * (1 + r2 ^ 2) + 2 * r2 * (B * Complex.exp ((θ : ℂ) * I)).re) =
      ‖(p : ℂ) - x‖ ^ 2 * p.im * (r1 - r2) * (1 - r1 * r2) := by
    linear_combination r2 * e1
  have h3 : 0 < 1 - r1 * r2 := by nlinarith
  nlinarith [mul_nonneg h1.le f2, mul_pos (mul_pos ha (sub_pos.mpr h12)) h3]

/-- The circle identity behind the vertex angles: for two points `ζ₁, ζ₂` of the chart circle
`|ζ|² + 1 = 2 Re (c̄ ζ)`, `(ζ₂ - ζ₁)(1 - ζ₁ ζ̄₂) = (ζ₁ ζ̄₂ - ζ̄₁ ζ₂)(ζ₁ - c)`. -/
theorem s13c_ga_Q (ζ1 ζ2 c : ℂ) (E1 : ζ1 * conj ζ1 = conj c * ζ1 + c * conj ζ1 - 1)
    (E2 : ζ2 * conj ζ2 = conj c * ζ2 + c * conj ζ2 - 1) :
    (ζ2 - ζ1) * (1 - ζ1 * conj ζ2) = (ζ1 * conj ζ2 - conj ζ1 * ζ2) * (ζ1 - c) := by
  linear_combination (-ζ1) * E2 + ζ2 * E1

/-- Algebraic core of the vertex angle formula. -/
theorem s13c_ga_comb {Φ Ψ ζ1 ζ2 c E : ℂ} {r1 r2 s t σ q N : ℝ}
    (hT : Ψ * ((1 - conj ζ1 * ζ2) * -ζ1) = Φ * (ζ2 - ζ1))
    (hQ : (ζ2 - ζ1) * (1 - ζ1 * conj ζ2) = (ζ1 * conj ζ2 - conj ζ1 * ζ2) * (ζ1 - c))
    (h2 : ζ1 * conj ζ2 - conj ζ1 * ζ2 = (r1 : ℂ) * r2 * s * I + (r1 : ℂ) * r2 * s * I)
    (h3 : I * r1 * (c - ζ1) = ((σ : ℂ) + q * I) * ζ1) (h4 : (σ : ℂ) + q * I = t * E)
    (hN : (1 - conj ζ1 * ζ2) * (1 - ζ1 * conj ζ2) = N) (hN0 : N ≠ 0) (hζ : ζ1 ≠ 0) :
    Ψ = Φ * ((2 * r2 * s * t / N : ℝ) : ℂ) * E := by
  have key : Ψ * ((N : ℂ) * -ζ1) = Φ * (-(2 * (r2 : ℂ) * s * t) * E * ζ1) := by
    rw [← hN]
    linear_combination (1 - ζ1 * conj ζ2) * hT + Φ * hQ + Φ * (ζ1 - c) * h2 - 2 * Φ * r2 * s * h3 -
      2 * Φ * r2 * s * ζ1 * h4
  have hNc : (N : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hN0
  have hA : ((2 * r2 * s * t / N : ℝ) : ℂ) * (N : ℂ) = 2 * (r2 : ℂ) * s * t := by
    push_cast
    rw [div_mul_cancel₀ _ hNc]
  apply mul_right_cancel₀ (mul_ne_zero hNc (neg_ne_zero.mpr hζ))
  rw [key]
  linear_combination (Φ * E * ζ1) * hA

/-- **The vertex angle formula.** Let `ζ₁ = r₁ e^{iθ₁}`, `ζ₂ = r₂ e^{iθ₂}` lie on the chart circle
`|ζ|² + 1 = 2 Re (c̄ ζ)`, `r₁ < 1`. If `Ψ (1 - ζ̄₁ ζ₂)(-ζ₁) = Φ (ζ₂ - ζ₁)` (the chart transition), then
`Ψ = Φ · R · e^{i(π/2 - ψ(θ₁))}` with an explicit real `R` of the sign of `sin (θ₁ - θ₂)`. -/
theorem s13c_ga_X (c : ℂ) (hk : 1 < ‖c‖) {r1 r2 θ1 θ2 : ℝ} (hr1 : 0 < r1) (hr1' : r1 < 1)
    (E1 : r1 ^ 2 - 2 * (conj c * Complex.exp ((θ1 : ℂ) * I)).re * r1 + 1 = 0)
    (E2 : r2 ^ 2 - 2 * (conj c * Complex.exp ((θ2 : ℂ) * I)).re * r2 + 1 = 0) {Φ Ψ : ℂ}
    (hT : Ψ * ((1 - conj ((r1 : ℂ) * Complex.exp ((θ1 : ℂ) * I)) * ((r2 : ℂ) * Complex.exp ((θ2 : ℂ) * I))) *
      -((r1 : ℂ) * Complex.exp ((θ1 : ℂ) * I))) =
      Φ * ((r2 : ℂ) * Complex.exp ((θ2 : ℂ) * I) - (r1 : ℂ) * Complex.exp ((θ1 : ℂ) * I)))
    (hD0 : 1 - conj ((r1 : ℂ) * Complex.exp ((θ1 : ℂ) * I)) * ((r2 : ℂ) * Complex.exp ((θ2 : ℂ) * I)) ≠ 0) :
    Ψ = Φ * ((2 * r2 * Real.sin (θ1 - θ2) * √(‖c‖ ^ 2 - 1) /
        Complex.normSq (1 - conj ((r1 : ℂ) * Complex.exp ((θ1 : ℂ) * I)) *
          ((r2 : ℂ) * Complex.exp ((θ2 : ℂ) * I))) : ℝ) : ℂ) *
      Complex.exp (((π / 2 - Real.arcsin (‖c‖ * Real.sin (θ1 - Complex.arg c) / √(‖c‖ ^ 2 - 1)) : ℝ) : ℂ) * I) := by
  have hre : ∀ θ : ℝ, (conj c * Complex.exp ((θ : ℂ) * I)).re = c.re * Real.cos θ + c.im * Real.sin θ := by
    intro θ
    simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im, Complex.exp_ofReal_mul_I_re,
      Complex.exp_ofReal_mul_I_im]
    ring
  rw [hre] at E1 E2
  have hC : ∀ r θ : ℝ, r ^ 2 - 2 * (c.re * Real.cos θ + c.im * Real.sin θ) * r + 1 = 0 →
      (r : ℂ) * Complex.exp ((θ : ℂ) * I) * conj ((r : ℂ) * Complex.exp ((θ : ℂ) * I)) =
        conj c * ((r : ℂ) * Complex.exp ((θ : ℂ) * I)) + c * conj ((r : ℂ) * Complex.exp ((θ : ℂ) * I)) - 1 := by
    intro r θ h
    apply Complex.ext
    · simp only [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.sub_re, Complex.conj_re,
        Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im, Complex.exp_ofReal_mul_I_re,
        Complex.exp_ofReal_mul_I_im, Complex.one_re]
      linear_combination h + r ^ 2 * Real.sin_sq_add_cos_sq θ
    · simp only [Complex.mul_re, Complex.mul_im, Complex.add_im, Complex.sub_im, Complex.conj_re,
        Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im, Complex.exp_ofReal_mul_I_re,
        Complex.exp_ofReal_mul_I_im, Complex.one_im]
      ring
  have hQ := s13c_ga_Q _ _ c (hC r1 θ1 E1) (hC r2 θ2 E2)
  have h2 : (r1 : ℂ) * Complex.exp ((θ1 : ℂ) * I) * conj ((r2 : ℂ) * Complex.exp ((θ2 : ℂ) * I)) -
      conj ((r1 : ℂ) * Complex.exp ((θ1 : ℂ) * I)) * ((r2 : ℂ) * Complex.exp ((θ2 : ℂ) * I)) =
      (r1 : ℂ) * r2 * (Real.sin (θ1 - θ2) : ℂ) * I + (r1 : ℂ) * r2 * (Real.sin (θ1 - θ2) : ℂ) * I := by
    apply Complex.ext
    · simp only [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.sub_re, Complex.conj_re,
        Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im, Complex.exp_ofReal_mul_I_re,
        Complex.exp_ofReal_mul_I_im, Complex.I_re, Complex.I_im]
      ring
    · simp only [Complex.mul_re, Complex.mul_im, Complex.add_im, Complex.sub_im, Complex.conj_re,
        Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im, Complex.exp_ofReal_mul_I_re,
        Complex.exp_ofReal_mul_I_im, Complex.I_re, Complex.I_im]
      rw [Real.sin_sub]
      ring
  have h3 : I * (r1 : ℂ) * (c - (r1 : ℂ) * Complex.exp ((θ1 : ℂ) * I)) =
      (((c.re * Real.sin θ1 - c.im * Real.cos θ1 : ℝ) : ℂ) +
        ((c.re * Real.cos θ1 + c.im * Real.sin θ1 - r1 : ℝ) : ℂ) * I) * ((r1 : ℂ) * Complex.exp ((θ1 : ℂ) * I)) := by
    apply Complex.ext
    · simp only [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.sub_re, Complex.add_im,
        Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
        Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
      linear_combination (r1 * c.im) * Real.sin_sq_add_cos_sq θ1
    · simp only [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.sub_re, Complex.add_im,
        Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
        Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
      linear_combination (-(r1 * c.re)) * Real.sin_sq_add_cos_sq θ1
  -- the exponential form of `σ + i q`
  have hkk : 0 < ‖c‖ ^ 2 - 1 := by nlinarith
  have ht : 0 < √(‖c‖ ^ 2 - 1) := Real.sqrt_pos.mpr hkk
  have ht0 : √(‖c‖ ^ 2 - 1) ≠ 0 := ht.ne'
  have ht2 : √(‖c‖ ^ 2 - 1) ^ 2 = ‖c‖ ^ 2 - 1 := Real.sq_sqrt hkk.le
  have hk2 : ‖c‖ ^ 2 = c.re ^ 2 + c.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    ring
  have hpy : (c.re * Real.sin θ1 - c.im * Real.cos θ1) ^ 2 + (c.re * Real.cos θ1 + c.im * Real.sin θ1) ^ 2 =
      ‖c‖ ^ 2 := by
    rw [hk2]
    linear_combination (c.re ^ 2 + c.im ^ 2) * Real.sin_sq_add_cos_sq θ1
  have hq1 : 2 * r1 * (c.re * Real.cos θ1 + c.im * Real.sin θ1 - r1) = 1 - r1 ^ 2 := by
    linear_combination -E1
  have hq0 : 0 < c.re * Real.cos θ1 + c.im * Real.sin θ1 - r1 := by
    nlinarith [mul_pos hr1 (sub_pos.mpr hr1')]
  have hq2 : (c.re * Real.cos θ1 + c.im * Real.sin θ1 - r1) ^ 2 =
      (c.re * Real.cos θ1 + c.im * Real.sin θ1) ^ 2 - 1 := by
    linear_combination E1
  have hσt : (c.re * Real.sin θ1 - c.im * Real.cos θ1) ^ 2 < √(‖c‖ ^ 2 - 1) ^ 2 := by
    nlinarith [pow_pos hq0 2]
  have hσa := abs_lt.mp (abs_lt_of_sq_lt_sq hσt ht.le)
  have hσ : ‖c‖ * Real.sin (θ1 - Complex.arg c) = c.re * Real.sin θ1 - c.im * Real.cos θ1 := by
    rw [Real.sin_sub]
    linear_combination (Real.sin θ1) * Complex.norm_mul_cos_arg c - (Real.cos θ1) * Complex.norm_mul_sin_arg c
  have hx1 : -1 ≤ (c.re * Real.sin θ1 - c.im * Real.cos θ1) / √(‖c‖ ^ 2 - 1) := by
    rw [le_div_iff₀ ht]
    linarith [hσa.1]
  have hx2 : (c.re * Real.sin θ1 - c.im * Real.cos θ1) / √(‖c‖ ^ 2 - 1) ≤ 1 := by
    rw [div_le_one ht]
    exact hσa.2.le
  have hsinψ : Real.sin (Real.arcsin (‖c‖ * Real.sin (θ1 - Complex.arg c) / √(‖c‖ ^ 2 - 1))) =
      (c.re * Real.sin θ1 - c.im * Real.cos θ1) / √(‖c‖ ^ 2 - 1) := by
    rw [hσ]
    exact Real.sin_arcsin hx1 hx2
  have hcosψ : Real.cos (Real.arcsin (‖c‖ * Real.sin (θ1 - Complex.arg c) / √(‖c‖ ^ 2 - 1))) =
      (c.re * Real.cos θ1 + c.im * Real.sin θ1 - r1) / √(‖c‖ ^ 2 - 1) := by
    rw [hσ, Real.cos_arcsin]
    have e : 1 - ((c.re * Real.sin θ1 - c.im * Real.cos θ1) / √(‖c‖ ^ 2 - 1)) ^ 2 =
        ((c.re * Real.cos θ1 + c.im * Real.sin θ1 - r1) / √(‖c‖ ^ 2 - 1)) ^ 2 := by
      rw [div_pow, div_pow, eq_div_iff (pow_pos ht 2).ne', sub_mul, one_mul, div_mul_cancel₀ _ (pow_pos ht 2).ne']
      linear_combination ht2 - hpy - hq2
    rw [e, Real.sqrt_sq (div_nonneg hq0.le ht.le)]
  have e1 : √(‖c‖ ^ 2 - 1) * ((c.re * Real.sin θ1 - c.im * Real.cos θ1) / √(‖c‖ ^ 2 - 1)) =
      c.re * Real.sin θ1 - c.im * Real.cos θ1 := by
    rw [mul_div_assoc']
    exact mul_div_cancel_left₀ _ ht0
  have e2 : √(‖c‖ ^ 2 - 1) * ((c.re * Real.cos θ1 + c.im * Real.sin θ1 - r1) / √(‖c‖ ^ 2 - 1)) =
      c.re * Real.cos θ1 + c.im * Real.sin θ1 - r1 := by
    rw [mul_div_assoc']
    exact mul_div_cancel_left₀ _ ht0
  have h4 : ((c.re * Real.sin θ1 - c.im * Real.cos θ1 : ℝ) : ℂ) +
      ((c.re * Real.cos θ1 + c.im * Real.sin θ1 - r1 : ℝ) : ℂ) * I =
      ((√(‖c‖ ^ 2 - 1) : ℝ) : ℂ) *
        Complex.exp (((π / 2 - Real.arcsin (‖c‖ * Real.sin (θ1 - Complex.arg c) / √(‖c‖ ^ 2 - 1)) : ℝ) : ℂ) * I) := by
    apply Complex.ext
    · simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
        Complex.I_im, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
      rw [Real.cos_pi_div_two_sub, Real.sin_pi_div_two_sub, hsinψ, hcosψ]
      linear_combination -e1
    · simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
        Complex.I_im, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
      rw [Real.cos_pi_div_two_sub, Real.sin_pi_div_two_sub, hsinψ, hcosψ]
      linear_combination -e2
  have hN : (1 - conj ((r1 : ℂ) * Complex.exp ((θ1 : ℂ) * I)) * ((r2 : ℂ) * Complex.exp ((θ2 : ℂ) * I))) *
      (1 - (r1 : ℂ) * Complex.exp ((θ1 : ℂ) * I) * conj ((r2 : ℂ) * Complex.exp ((θ2 : ℂ) * I))) =
      (Complex.normSq (1 - conj ((r1 : ℂ) * Complex.exp ((θ1 : ℂ) * I)) *
        ((r2 : ℂ) * Complex.exp ((θ2 : ℂ) * I))) : ℂ) := by
    have e : (1 : ℂ) - (r1 : ℂ) * Complex.exp ((θ1 : ℂ) * I) * conj ((r2 : ℂ) * Complex.exp ((θ2 : ℂ) * I)) =
        conj (1 - conj ((r1 : ℂ) * Complex.exp ((θ1 : ℂ) * I)) * ((r2 : ℂ) * Complex.exp ((θ2 : ℂ) * I))) := by
      conv_rhs => rw [map_sub, map_one, map_mul, Complex.conj_conj]
    rw [e]
    exact Complex.mul_conj _
  have hN0 := (Complex.normSq_pos.mpr hD0).ne'
  have hζ : (r1 : ℂ) * Complex.exp ((θ1 : ℂ) * I) ≠ 0 :=
    mul_ne_zero (Complex.ofReal_ne_zero.mpr hr1.ne') (Complex.exp_ne_zero _)
  exact s13c_ga_comb hT hQ h2 h3 h4 hN hN0 hζ

/-- The chart angle `ψ` stays in `(-π/2, π/2)` where the circle is visible. -/
theorem s13c_ga_psi (c : ℂ) (hk : 1 < ‖c‖) (θ : ℝ) (hρ : 1 < (conj c * Complex.exp ((θ : ℂ) * I)).re) :
    -(π / 2) < Real.arcsin (‖c‖ * Real.sin (θ - Complex.arg c) / √(‖c‖ ^ 2 - 1)) ∧
      Real.arcsin (‖c‖ * Real.sin (θ - Complex.arg c) / √(‖c‖ ^ 2 - 1)) < π / 2 := by
  rw [s13c_ga_rho] at hρ
  have hkk : 0 < ‖c‖ ^ 2 - 1 := by nlinarith
  have hsk : 0 < √(‖c‖ ^ 2 - 1) := Real.sqrt_pos.mpr hkk
  have hid : (‖c‖ * Real.sin (θ - Complex.arg c)) ^ 2 + (‖c‖ * Real.cos (θ - Complex.arg c)) ^ 2 = ‖c‖ ^ 2 := by
    linear_combination ‖c‖ ^ 2 * Real.sin_sq_add_cos_sq (θ - Complex.arg c)
  have hc2 : 1 < (‖c‖ * Real.cos (θ - Complex.arg c)) ^ 2 := by nlinarith
  have hu : |‖c‖ * Real.sin (θ - Complex.arg c) / √(‖c‖ ^ 2 - 1)| < 1 := by
    rw [abs_div, abs_of_pos hsk, div_lt_one hsk, ← sq_lt_sq₀ (abs_nonneg _) hsk.le, sq_abs,
      Real.sq_sqrt hkk.le]
    linarith
  obtain ⟨h1, h2⟩ := abs_lt.mp hu
  exact ⟨Real.neg_pi_div_two_lt_arcsin.mpr h1, Real.arcsin_lt_pi_div_two.mpr h2⟩

/-- The chart transition from `p` to `w`: `φ_w(b) (1 - ζ̄_w ζ_b)(-ζ_w) = φ_w(p) (ζ_b - ζ_w)`, where
`ζ_x = φ_p(x)` and `φ_w(z) = (z - w)/(z - w̄)`. -/
theorem s13c_ga_tr (p w b : UpperHalfPlane) :
    ((b : ℂ) - w) / ((b : ℂ) - conj (w : ℂ)) *
      ((1 - conj (((w : ℂ) - p) / ((w : ℂ) - conj (p : ℂ))) * (((b : ℂ) - p) / ((b : ℂ) - conj (p : ℂ)))) *
        -(((w : ℂ) - p) / ((w : ℂ) - conj (p : ℂ)))) =
      ((p : ℂ) - w) / ((p : ℂ) - conj (w : ℂ)) *
        (((b : ℂ) - p) / ((b : ℂ) - conj (p : ℂ)) - ((w : ℂ) - p) / ((w : ℂ) - conj (p : ℂ))) := by
  have h1 := s13c_ga_ne b w
  have h2 := s13c_ga_ne w p
  have h3 := s13c_ga_ne b p
  have h4 := s13c_ga_ne p w
  have h5 : conj (w : ℂ) - p ≠ 0 := by
    intro h
    apply h2
    have h6 := congrArg conj h
    rw [map_sub, Complex.conj_conj, map_zero] at h6
    exact h6
  rw [map_div₀, map_sub, map_sub, Complex.conj_conj]
  field_simp
  ring

/-- **The vertex arcs.** Let `w, b ∈ D` have chart coordinates `ζ₁ = r₁ e^{iθ₁}`, `ζ₂ = r₂ e^{iθ₂}` at `p` on
a common chart circle `c`. Seen from `w`, with `d` the direction of `p`, the directions between `d` and the
direction of `b` all lie in the angle of `D` at `w`: they form `[d - (π/2 + ψ(θ₁)), d]` if `sin (θ₁ - θ₂) < 0`
and `[d, d + (π/2 - ψ(θ₁))]` if `sin (θ₁ - θ₂) > 0`. -/
theorem s13c_ga_varc {Γ' : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p : UpperHalfPlane}
    (D : Set UpperHalfPlane) (hDdef : D = {w : UpperHalfPlane | ∀ g ∈ Γ', dist w p ≤ dist w (g • p)})
    {w b : UpperHalfPlane} (hwD : w ∈ D) (hbD : b ∈ D) (hpD : p ∈ D) (hwp : w ≠ p)
    (c : ℂ) {r1 r2 θ1 θ2 : ℝ} (hr1 : 0 < r1) (hr1' : r1 < 1) (hr2 : 0 < r2)
    (hw : ((w : ℂ) - p) / ((w : ℂ) - conj (p : ℂ)) = (r1 : ℂ) * Complex.exp ((θ1 : ℂ) * I))
    (hb : ((b : ℂ) - p) / ((b : ℂ) - conj (p : ℂ)) = (r2 : ℂ) * Complex.exp ((θ2 : ℂ) * I))
    (E1 : r1 ^ 2 - 2 * (conj c * Complex.exp ((θ1 : ℂ) * I)).re * r1 + 1 = 0)
    (E2 : r2 ^ 2 - 2 * (conj c * Complex.exp ((θ2 : ℂ) * I)).re * r2 + 1 = 0) (hk : 1 < ‖c‖) :
    (Real.sin (θ1 - θ2) < 0 → ∀ θ ∈ Icc (Complex.arg (((p : ℂ) - w) / ((p : ℂ) - conj (w : ℂ))) -
        (π / 2 + Real.arcsin (‖c‖ * Real.sin (θ1 - Complex.arg c) / √(‖c‖ ^ 2 - 1))))
        (Complex.arg (((p : ℂ) - w) / ((p : ℂ) - conj (w : ℂ)))),
      ∀ᶠ s : ℝ in 𝓝[>] (0 : ℝ), ((w : ℂ) - conj (w : ℂ) * ((s : ℂ) * Complex.exp ((θ : ℂ) * I))) /
        (1 - (s : ℂ) * Complex.exp ((θ : ℂ) * I)) ∈ ((↑) : UpperHalfPlane → ℂ) '' D) ∧
    (0 < Real.sin (θ1 - θ2) → ∀ θ ∈ Icc (Complex.arg (((p : ℂ) - w) / ((p : ℂ) - conj (w : ℂ))))
        (Complex.arg (((p : ℂ) - w) / ((p : ℂ) - conj (w : ℂ))) +
          (π / 2 - Real.arcsin (‖c‖ * Real.sin (θ1 - Complex.arg c) / √(‖c‖ ^ 2 - 1)))),
      ∀ᶠ s : ℝ in 𝓝[>] (0 : ℝ), ((w : ℂ) - conj (w : ℂ) * ((s : ℂ) * Complex.exp ((θ : ℂ) * I))) /
        (1 - (s : ℂ) * Complex.exp ((θ : ℂ) * I)) ∈ ((↑) : UpperHalfPlane → ℂ) '' D) := by
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : ℂ, Φ = ((p : ℂ) - w) / ((p : ℂ) - conj (w : ℂ)) := ⟨_, rfl⟩
  obtain ⟨Ψ, hΨ⟩ : ∃ Ψ : ℂ, Ψ = ((b : ℂ) - w) / ((b : ℂ) - conj (w : ℂ)) := ⟨_, rfl⟩
  rw [← hΦ]
  have hT := s13c_ga_tr p w b
  rw [hw, hb, ← hΦ, ← hΨ] at hT
  have n1 : ‖(r1 : ℂ) * Complex.exp ((θ1 : ℂ) * I)‖ < 1 := by
    rw [← hw]
    exact s13c_ga_nlt w p
  have n2 : ‖(r2 : ℂ) * Complex.exp ((θ2 : ℂ) * I)‖ < 1 := by
    rw [← hb]
    exact s13c_ga_nlt b p
  have hD0 : 1 - conj ((r1 : ℂ) * Complex.exp ((θ1 : ℂ) * I)) * ((r2 : ℂ) * Complex.exp ((θ2 : ℂ) * I)) ≠ 0 := by
    intro h
    have h1 : conj ((r1 : ℂ) * Complex.exp ((θ1 : ℂ) * I)) * ((r2 : ℂ) * Complex.exp ((θ2 : ℂ) * I)) = 1 :=
      (sub_eq_zero.mp h).symm
    have h2 := congrArg norm h1
    rw [norm_mul, Complex.norm_conj, norm_one] at h2
    nlinarith [norm_nonneg ((r1 : ℂ) * Complex.exp ((θ1 : ℂ) * I)),
      norm_nonneg ((r2 : ℂ) * Complex.exp ((θ2 : ℂ) * I))]
  have hX := s13c_ga_X c hk hr1 hr1' E1 E2 hT hD0
  have hρ1 : 1 < (conj c * Complex.exp ((θ1 : ℂ) * I)).re := by
    nlinarith [mul_pos (sub_pos.mpr hr1') (sub_pos.mpr hr1')]
  obtain ⟨hψ1, hψ2⟩ := s13c_ga_psi c hk θ1 hρ1
  obtain ⟨ψ, hψd⟩ : ∃ ψ : ℝ, ψ = Real.arcsin (‖c‖ * Real.sin (θ1 - Complex.arg c) / √(‖c‖ ^ 2 - 1)) :=
    ⟨_, rfl⟩
  rw [← hψd] at hX hψ1 hψ2 ⊢
  obtain ⟨R, hRd⟩ : ∃ R : ℝ, R = 2 * r2 * Real.sin (θ1 - θ2) * √(‖c‖ ^ 2 - 1) /
      Complex.normSq (1 - conj ((r1 : ℂ) * Complex.exp ((θ1 : ℂ) * I)) *
        ((r2 : ℂ) * Complex.exp ((θ2 : ℂ) * I))) := ⟨_, rfl⟩
  rw [← hRd] at hX
  have hN := Complex.normSq_pos.mpr hD0
  have hK : 0 < √(‖c‖ ^ 2 - 1) := Real.sqrt_pos.mpr (by nlinarith)
  have hΦ0 : Φ ≠ 0 := by
    rw [hΦ]
    exact div_ne_zero (sub_ne_zero.mpr fun h => hwp (UpperHalfPlane.ext h).symm) (s13c_ga_ne p w)
  have hΦn : ‖Φ‖ < 1 := by
    rw [hΦ]
    exact s13c_ga_nlt p w
  have hΦp : 0 < ‖Φ‖ := norm_pos_iff.mpr hΦ0
  have hΨn : ‖Ψ‖ < 1 := by
    rw [hΨ]
    exact s13c_ga_nlt b w
  have hpol : Φ = (‖Φ‖ : ℂ) * Complex.exp ((Complex.arg Φ : ℂ) * I) := (Complex.norm_mul_exp_arg_mul_I Φ).symm
  have hpray : ((w : ℂ) - conj (w : ℂ) * ((‖Φ‖ : ℂ) * Complex.exp ((Complex.arg Φ : ℂ) * I))) /
      (1 - (‖Φ‖ : ℂ) * Complex.exp ((Complex.arg Φ : ℂ) * I)) ∈ ((↑) : UpperHalfPlane → ℂ) '' D :=
    ⟨p, hpD, (s13c_ga_inv w p (by rw [← hΦ]; exact hpol)).symm⟩
  have hfw : ∀ da db ra rb : ℝ, 0 < ra → ra < 1 → 0 < rb → rb < 1 → da < db → db - da < π →
      ((w : ℂ) - conj (w : ℂ) * ((ra : ℂ) * Complex.exp ((da : ℂ) * I))) /
        (1 - (ra : ℂ) * Complex.exp ((da : ℂ) * I)) ∈ ((↑) : UpperHalfPlane → ℂ) '' D →
      ((w : ℂ) - conj (w : ℂ) * ((rb : ℂ) * Complex.exp ((db : ℂ) * I))) /
        (1 - (rb : ℂ) * Complex.exp ((db : ℂ) * I)) ∈ ((↑) : UpperHalfPlane → ℂ) '' D →
      ∀ θ ∈ Icc da db, ∀ᶠ s : ℝ in 𝓝[>] (0 : ℝ),
        ((w : ℂ) - conj (w : ℂ) * ((s : ℂ) * Complex.exp ((θ : ℂ) * I))) /
          (1 - (s : ℂ) * Complex.exp ((θ : ℂ) * I)) ∈ ((↑) : UpperHalfPlane → ℂ) '' D := by
    intro da db ra rb h1 h2 h3 h4 h5 h6 hA hB θ hθ
    obtain ⟨c', -, -, hf⟩ := s13c_ga_fan D hDdef hwD h1 h2 h3 h4 h5 h6 hA hB
    obtain ⟨hρ, hs⟩ := hf θ hθ
    obtain ⟨hS0, -, -, -⟩ := s13c_pb_root hρ
    filter_upwards [Ioo_mem_nhdsGT hS0] with s hs'
    exact hs s hs'.1 hs'.2.le
  refine ⟨fun hs => ?_, fun hs => ?_⟩
  · have hR0 : R < 0 := by
      rw [hRd]
      exact div_neg_of_neg_of_pos (mul_neg_of_neg_of_pos (mul_neg_of_pos_of_neg (by positivity) hs) hK) hN
    have e0 : ((Complex.arg Φ - (π / 2 + ψ) : ℝ) : ℂ) * I =
        ((Complex.arg Φ : ℂ) * I + ((π / 2 - ψ : ℝ) : ℂ) * I) - (π : ℂ) * I := by
      push_cast
      ring
    have e : Complex.exp (((Complex.arg Φ - (π / 2 + ψ) : ℝ) : ℂ) * I) =
        -(Complex.exp ((Complex.arg Φ : ℂ) * I) * Complex.exp (((π / 2 - ψ : ℝ) : ℂ) * I)) := by
      rw [e0, Complex.exp_sub, Complex.exp_add, Complex.exp_pi_mul_I, div_neg, div_one]
    have hΨp : Ψ = ((‖Φ‖ * -R : ℝ) : ℂ) * Complex.exp (((Complex.arg Φ - (π / 2 + ψ) : ℝ) : ℂ) * I) := by
      rw [hX, e]
      conv_lhs => rw [hpol]
      push_cast
      ring
    have hra : 0 < ‖Φ‖ * -R := mul_pos hΦp (neg_pos.mpr hR0)
    have hra1 : ‖Φ‖ * -R < 1 := by
      have h := congrArg norm hΨp
      rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_of_nonneg hra.le] at h
      linarith
    have hbray : ((w : ℂ) - conj (w : ℂ) * (((‖Φ‖ * -R : ℝ) : ℂ) *
        Complex.exp (((Complex.arg Φ - (π / 2 + ψ) : ℝ) : ℂ) * I))) /
        (1 - ((‖Φ‖ * -R : ℝ) : ℂ) * Complex.exp (((Complex.arg Φ - (π / 2 + ψ) : ℝ) : ℂ) * I)) ∈
          ((↑) : UpperHalfPlane → ℂ) '' D :=
      ⟨b, hbD, (s13c_ga_inv w b (by rw [← hΨ]; exact hΨp)).symm⟩
    exact hfw _ _ _ _ hra hra1 hΦp hΦn (by linarith) (by linarith) hbray hpray
  · have hR0 : 0 < R := by
      rw [hRd]
      exact div_pos (mul_pos (mul_pos (by positivity) hs) hK) hN
    have e : Complex.exp (((Complex.arg Φ + (π / 2 - ψ) : ℝ) : ℂ) * I) =
        Complex.exp ((Complex.arg Φ : ℂ) * I) * Complex.exp (((π / 2 - ψ : ℝ) : ℂ) * I) := by
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    have hΨp : Ψ = ((‖Φ‖ * R : ℝ) : ℂ) * Complex.exp (((Complex.arg Φ + (π / 2 - ψ) : ℝ) : ℂ) * I) := by
      rw [hX, e]
      conv_lhs => rw [hpol]
      push_cast
      ring
    have hrb : 0 < ‖Φ‖ * R := mul_pos hΦp hR0
    have hrb1 : ‖Φ‖ * R < 1 := by
      have h := congrArg norm hΨp
      rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_of_nonneg hrb.le] at h
      linarith
    have hbray : ((w : ℂ) - conj (w : ℂ) * (((‖Φ‖ * R : ℝ) : ℂ) *
        Complex.exp (((Complex.arg Φ + (π / 2 - ψ) : ℝ) : ℂ) * I))) /
        (1 - ((‖Φ‖ * R : ℝ) : ℂ) * Complex.exp (((Complex.arg Φ + (π / 2 - ψ) : ℝ) : ℂ) * I)) ∈
          ((↑) : UpperHalfPlane → ℂ) '' D :=
      ⟨b, hbD, (s13c_ga_inv w b (by rw [← hΨ]; exact hΨp)).symm⟩
    exact hfw _ _ _ _ hΦp hΦn hrb hrb1 (by linarith) (by linarith) hpray hbray

/-- **One gap of the fan at `p`.** Let `u, v ∈ D` have chart coordinates `r_u e^{iθ_u}`, `r_v e^{i(θ_u + α)}` at `p`.
If `α < π`, the triangle `p u v` gives: an arc of directions of length `bR` at `u` (ending at the direction of `p`)
and one of length `bL` at `v` (starting at the direction of `p`) inside the angles of `D`, and a function `Gu` on
directions, supported on the arc `(θ_u, θ_u + α)` mod `2π`, below the radial area density of `D` and of integral
at least `ar`, with `bR + bL + ar + α = π` (Gauss–Bonnet for the triangle). If `α ≥ π` everything is `0`. -/
theorem s13c_ga_gap {Γ' : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p : UpperHalfPlane}
    (D : Set UpperHalfPlane) (hDdef : D = {w : UpperHalfPlane | ∀ g ∈ Γ', dist w p ≤ dist w (g • p)})
    {u v : UpperHalfPlane} (huD : u ∈ D) (hvD : v ∈ D) (hup : u ≠ p) (hvp : v ≠ p)
    {ru rv θu α : ℝ} (hvu : α < π → v ≠ u) (hru : 0 < ru) (hru' : ru < 1) (hrv : 0 < rv) (hrv' : rv < 1)
    (hα : 0 < α) (hα' : α ≤ 2 * π)
    (hu : ((u : ℂ) - p) / ((u : ℂ) - conj (p : ℂ)) = (ru : ℂ) * Complex.exp ((θu : ℂ) * I))
    (hv : ((v : ℂ) - p) / ((v : ℂ) - conj (p : ℂ)) = (rv : ℂ) * Complex.exp (((θu + α : ℝ) : ℂ) * I)) :
    ∃ bR bL ar : ℝ, ∃ Gu : ℝ → ℝ≥0∞, 0 ≤ bR ∧ bR < π ∧ 0 ≤ bL ∧ bL < π ∧ 0 ≤ ar ∧ π ≤ bR + bL + ar + α ∧
      (∀ θ : ℝ, Complex.arg (((p : ℂ) - u) / ((p : ℂ) - conj (u : ℂ))) - bR < θ →
        θ ≤ Complex.arg (((p : ℂ) - u) / ((p : ℂ) - conj (u : ℂ))) →
        ∀ᶠ s : ℝ in 𝓝[>] (0 : ℝ), ((u : ℂ) - conj (u : ℂ) * ((s : ℂ) * Complex.exp ((θ : ℂ) * I))) /
          (1 - (s : ℂ) * Complex.exp ((θ : ℂ) * I)) ∈ ((↑) : UpperHalfPlane → ℂ) '' D) ∧
      (∀ θ : ℝ, Complex.arg (((p : ℂ) - v) / ((p : ℂ) - conj (v : ℂ))) ≤ θ →
        θ < Complex.arg (((p : ℂ) - v) / ((p : ℂ) - conj (v : ℂ))) + bL →
        ∀ᶠ s : ℝ in 𝓝[>] (0 : ℝ), ((v : ℂ) - conj (v : ℂ) * ((s : ℂ) * Complex.exp ((θ : ℂ) * I))) /
          (1 - (s : ℂ) * Complex.exp ((θ : ℂ) * I)) ∈ ((↑) : UpperHalfPlane → ℂ) '' D) ∧
      Measurable Gu ∧
      (∀ θ : ℝ, Gu θ ≤ ∫⁻ s in Ioo (0 : ℝ) 1,
        (((↑) : UpperHalfPlane → ℂ) '' D).indicator (fun _ => ENNReal.ofReal (4 * s / (1 - s ^ 2) ^ 2))
          (((p : ℂ) - conj (p : ℂ) * ((s : ℂ) * Complex.exp ((θ : ℂ) * I))) /
            (1 - (s : ℂ) * Complex.exp ((θ : ℂ) * I)))) ∧
      (∀ θ : ℝ, θ ∉ (⋃ k : ℤ, Ioo (θu + 2 * π * k) (θu + α + 2 * π * k)) → Gu θ = 0) ∧
      ENNReal.ofReal ar ≤ ∫⁻ θ in Ioc (-π) π, Gu θ := by
  rcases lt_or_ge α π with hsm | hbig
  swap
  · refine ⟨0, 0, 0, 0, le_rfl, Real.pi_pos, le_rfl, Real.pi_pos, le_rfl, by linarith,
      fun θ h1 h2 => by exfalso; linarith, fun θ h1 h2 => by exfalso; linarith, measurable_zero,
      fun θ => zero_le, fun θ _ => rfl, ?_⟩
    rw [ENNReal.ofReal_zero]
    exact zero_le
  have hDm : ∀ x : UpperHalfPlane, x ∈ D ↔ ∀ g ∈ Γ', dist x p ≤ dist x (g • p) := by
    intro x
    simp only [hDdef, mem_setOf_eq]
  have hpD : p ∈ D := (hDm p).mpr fun g _ => by
    rw [dist_self]
    exact dist_nonneg
  have hA : ((p : ℂ) - conj (p : ℂ) * ((ru : ℂ) * Complex.exp ((θu : ℂ) * I))) /
      (1 - (ru : ℂ) * Complex.exp ((θu : ℂ) * I)) ∈ ((↑) : UpperHalfPlane → ℂ) '' D :=
    ⟨u, huD, (s13c_ga_inv p u hu).symm⟩
  have hB : ((p : ℂ) - conj (p : ℂ) * ((rv : ℂ) * Complex.exp (((θu + α : ℝ) : ℂ) * I))) /
      (1 - (rv : ℂ) * Complex.exp (((θu + α : ℝ) : ℂ) * I)) ∈ ((↑) : UpperHalfPlane → ℂ) '' D :=
    ⟨v, hvD, (s13c_ga_inv p v hv).symm⟩
  obtain ⟨c, Ea, Eb, hfan⟩ := s13c_ga_fan D hDdef hpD hru hru' hrv hrv' (by linarith : θu < θu + α)
    (by linarith : θu + α - θu < π) hA hB
  have hρa := (hfan θu ⟨le_rfl, by linarith⟩).1
  have hρb := (hfan (θu + α) ⟨by linarith, le_rfl⟩).1
  have hk : 1 < ‖c‖ := by
    have h2 := Complex.re_le_norm (conj c * Complex.exp ((θu : ℂ) * I))
    rw [norm_mul, Complex.norm_conj, Complex.norm_exp_ofReal_mul_I, mul_one] at h2
    linarith
  obtain ⟨hint, hnn⟩ := s13c_ga_ang c hk (by linarith : θu ≤ θu + α) (fun θ hθ => (hfan θ hθ).1)
  have hsα : 0 < Real.sin α := Real.sin_pos_of_pos_of_lt_pi hα hsm
  have hs1 : Real.sin (θu - (θu + α)) < 0 := by
    have e : θu - (θu + α) = -α := by ring
    rw [e, Real.sin_neg]
    linarith
  have hs2 : 0 < Real.sin (θu + α - θu) := by
    have e : θu + α - θu = α := by ring
    rw [e]
    exact hsα
  have hR := (s13c_ga_varc D hDdef huD hvD hpD hup c hru hru' hrv hu hv Ea Eb hk).1 hs1
  have hL := (s13c_ga_varc D hDdef hvD huD hpD hvp c hrv hrv' hru hv hu Eb Ea hk).2 hs2
  obtain ⟨hψa1, hψa2⟩ := s13c_ga_psi c hk θu hρa
  obtain ⟨hψb1, hψb2⟩ := s13c_ga_psi c hk (θu + α) hρb
  obtain ⟨ψa, hψa⟩ : ∃ x : ℝ, x = Real.arcsin (‖c‖ * Real.sin (θu - Complex.arg c) / √(‖c‖ ^ 2 - 1)) :=
    ⟨_, rfl⟩
  obtain ⟨ψb, hψb⟩ : ∃ x : ℝ, x = Real.arcsin (‖c‖ * Real.sin (θu + α - Complex.arg c) / √(‖c‖ ^ 2 - 1)) :=
    ⟨_, rfl⟩
  rw [← hψa] at hR hψa1 hψa2 hint hnn
  rw [← hψb] at hL hψb1 hψb2 hint hnn
  obtain ⟨hf, hhf⟩ : ∃ hf : ℝ → ℝ≥0∞, hf = fun θ : ℝ => ENNReal.ofReal
      ((conj c * Complex.exp ((θ : ℂ) * I)).re / √((conj c * Complex.exp ((θ : ℂ) * I)).re ^ 2 - 1) - 1) :=
    ⟨_, rfl⟩
  obtain ⟨Iu, hIu⟩ : ∃ Iu : Set ℝ, Iu = ⋃ k : ℤ, Ioo (θu + 2 * π * k) (θu + α + 2 * π * k) := ⟨_, rfl⟩
  rw [← hIu]
  have hIm : MeasurableSet Iu := by
    rw [hIu]
    exact MeasurableSet.iUnion fun k => measurableSet_Ioo
  have hfeq : hf = fun θ : ℝ => ENNReal.ofReal (‖c‖ * Real.cos (θ - Complex.arg c) /
      √((‖c‖ * Real.cos (θ - Complex.arg c)) ^ 2 - 1) - 1) := by
    rw [hhf]
    funext θ
    rw [s13c_ga_rho]
  have hfm : Measurable hf := by
    rw [hfeq]
    exact (by fun_prop : Measurable fun θ : ℝ => ‖c‖ * Real.cos (θ - Complex.arg c) /
      √((‖c‖ * Real.cos (θ - Complex.arg c)) ^ 2 - 1) - 1).ennreal_ofReal
  refine ⟨π / 2 + ψa, π / 2 - ψb, ψb - ψa - (θu + α - θu), Iu.indicator hf, by linarith, by linarith,
    by linarith, by linarith, hnn, by linarith, fun θ h1 h2 => hR θ ⟨h1.le, h2⟩,
    fun θ h1 h2 => hL θ ⟨h1, h2.le⟩, hfm.indicator hIm, ?_, fun θ hθ => Set.indicator_of_notMem hθ hf, ?_⟩
  · -- below the radial density
    intro θ
    by_cases hθ : θ ∈ Iu
    · rw [Set.indicator_of_mem hθ, hhf]
      rw [hIu] at hθ
      obtain ⟨k, hk1, hk2⟩ := mem_iUnion.mp hθ
      obtain ⟨θ', hθ'⟩ : ∃ θ' : ℝ, θ' = θ - 2 * π * k := ⟨_, rfl⟩
      have hθe : Complex.exp ((θ : ℂ) * I) = Complex.exp ((θ' : ℂ) * I) := by
        rw [← s13c_ga_per θ' k, hθ', sub_add_cancel]
      have hmem : θ' ∈ Icc θu (θu + α) := ⟨by rw [hθ']; linarith, by rw [hθ']; linarith⟩
      obtain ⟨hρ, hseg⟩ := hfan θ' hmem
      obtain ⟨S, hS⟩ : ∃ S : ℝ, S = (conj c * Complex.exp ((θ' : ℂ) * I)).re -
          √((conj c * Complex.exp ((θ' : ℂ) * I)).re ^ 2 - 1) := ⟨_, rfl⟩
      obtain ⟨hS0, hS1, -, hSval⟩ := s13c_pb_root hρ
      rw [← hS] at hS0 hS1 hSval hseg
      beta_reduce
      rw [hθe, ← hSval, ← s13c_pb_radial hS0.le hS1]
      calc ∫⁻ s in Ioo (0 : ℝ) S, ENNReal.ofReal (4 * s / (1 - s ^ 2) ^ 2) =
          ∫⁻ s in Ioo (0 : ℝ) S, (((↑) : UpperHalfPlane → ℂ) '' D).indicator
            (fun _ => ENNReal.ofReal (4 * s / (1 - s ^ 2) ^ 2))
              (((p : ℂ) - conj (p : ℂ) * ((s : ℂ) * Complex.exp ((θ' : ℂ) * I))) /
                (1 - (s : ℂ) * Complex.exp ((θ' : ℂ) * I))) :=
            setLIntegral_congr_fun measurableSet_Ioo fun s hs =>
              (Set.indicator_of_mem (hseg s hs.1 hs.2.le) (fun _ => ENNReal.ofReal (4 * s / (1 - s ^ 2) ^ 2))).symm
        _ ≤ _ := lintegral_mono_set (Ioo_subset_Ioo_right hS1.le)
    · rw [Set.indicator_of_notMem hθ]
      exact zero_le
  · -- the integral over a period
    have hper : ∀ θ, Iu.indicator hf (θ + 2 * π) = Iu.indicator hf θ := by
      intro θ
      have hI := s13c_ga_Iper θu (θu + α) θ
      rw [← hIu] at hI
      by_cases hθ : θ ∈ Iu
      · rw [Set.indicator_of_mem (hI.mpr hθ), Set.indicator_of_mem hθ, hhf]
        simp only [s13c_ga_per2]
      · rw [Set.indicator_of_notMem (fun h => hθ (hI.mp h)), Set.indicator_of_notMem hθ]
    have hint' : ∫⁻ θ in Ioo θu (θu + α), hf θ = ENNReal.ofReal (ψb - ψa - (θu + α - θu)) := by
      rw [hhf]
      exact hint
    rw [← s13c_pb_lshift _ hper (θu + π)]
    have e1 : -π + (θu + π) = θu := by ring
    have e2 : -π + α + (θu + π) = θu + α := by ring
    calc ENNReal.ofReal (ψb - ψa - (θu + α - θu)) = ∫⁻ θ in Ioo θu (θu + α), hf θ := hint'.symm
      _ = ∫⁻ θ in Ioo (-π) (-π + α), hf (θ + (θu + π)) := by rw [s13c_ga_tint hf, e1, e2]
      _ = ∫⁻ θ in Ioo (-π) (-π + α), Iu.indicator hf (θ + (θu + π)) := by
          refine setLIntegral_congr_fun measurableSet_Ioo fun θ hθ => ?_
          have hm : θ + (θu + π) ∈ Iu := by
            rw [hIu]
            exact mem_iUnion.mpr ⟨0, by push_cast; linarith [hθ.1], by push_cast; linarith [hθ.2]⟩
          rw [Set.indicator_of_mem hm]
      _ ≤ ∫⁻ θ in Ioc (-π) π, Iu.indicator hf (θ + (θu + π)) :=
          lintegral_mono_set fun θ hθ => ⟨hθ.1, by linarith [hθ.2]⟩

/-- **(B2.4.i) Convexity of a Dirichlet half-plane.** The closed half-plane `{z | d(z, p) ≤ d(z, q)}` contains the
geodesic segment `{z | d(a, z) + d(z, b) = d(a, b)}` between any two of its points. -/
theorem s13c_sc_convex {a b z p q : UpperHalfPlane} (ha : dist a p ≤ dist a q) (hb : dist b p ≤ dist b q)
    (hz : dist a z + dist z b = dist a b) : dist z p ≤ dist z q := by
  obtain ⟨M, hMa, hMb⟩ := s13c_cv_norm a b
  have tr : ∀ x y : UpperHalfPlane, dist (M • x) (M • y) = dist x y := fun x y => dist_smul M x y
  have ha' : dist (M • a) (M • p) ≤ dist (M • a) (M • q) := by rw [tr, tr]; exact ha
  have hb' : dist (M • b) (M • p) ≤ dist (M • b) (M • q) := by rw [tr, tr]; exact hb
  have hz' : dist (M • a) (M • z) + dist (M • z) (M • b) = dist (M • a) (M • b) := by rw [tr, tr, tr]; exact hz
  have h := s13c_cv_axis hMa hMb ha' hb' hz'
  rwa [tr, tr] at h

/-- **(B2.4.ii) Faces.** Let `D` be the closed Dirichlet domain at `p` and `V` its set of vertices (points of `D`
equidistant from `p` and two further distinct orbit points). If `γ ∈ Γ'` moves `p` and carries a point of `D` into
`D`, then either a vertex lies on the bisector of `p` and `γ⁻¹ p` (the face of `γ` has a finite endpoint), or the whole
bisector lies in `D`. -/
theorem s13c_sc_face {Γ' : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} (hΓ' : LiZhongQC.IsFuchsian Γ')
    {p : UpperHalfPlane} (D V : Set UpperHalfPlane)
    (hDdef : D = {w : UpperHalfPlane | ∀ g ∈ Γ', dist w p ≤ dist w (g • p)})
    (hV : V = {v : UpperHalfPlane | v ∈ D ∧ ∃ g ∈ Γ', ∃ h ∈ Γ', g • p ≠ p ∧ h • p ≠ p ∧ g • p ≠ h • p ∧
      dist v p = dist v (g • p) ∧ dist v p = dist v (h • p)})
    {γ : Matrix.SpecialLinearGroup (Fin 2) ℝ} (hγ : γ ∈ Γ') (hγp : γ • p ≠ p)
    {w : UpperHalfPlane} (hw : w ∈ D) (hγw : γ • w ∈ D) :
    (∃ v ∈ V, dist v p = dist v (γ⁻¹ • p)) ∨ ∀ z : UpperHalfPlane, dist z p = dist z (γ⁻¹ • p) → z ∈ D := by
  have hγi : γ⁻¹ ∈ Γ' := Γ'.inv_mem hγ
  have hDm : ∀ x : UpperHalfPlane, x ∈ D ↔ ∀ g ∈ Γ', dist x p ≤ dist x (g • p) := by
    intro x
    simp only [hDdef, mem_setOf_eq]
  have hDcl : IsClosed D := by
    have heq : D = ⋂ g : Γ', {x : UpperHalfPlane |
        dist x p ≤ dist x ((g : Matrix.SpecialLinearGroup (Fin 2) ℝ) • p)} := by
      rw [hDdef]
      ext x
      simp only [mem_setOf_eq, mem_iInter, Subtype.forall]
    rw [heq]
    exact isClosed_iInter fun g => isClosed_le (continuous_id.dist continuous_const)
      (continuous_id.dist continuous_const)
  -- `w` lies on the bisector of `p` and `γ⁻¹ p`
  have hwB : dist w p = dist w (γ⁻¹ • p) := by
    apply le_antisymm ((hDm w).mp hw _ hγi)
    have h1 := (hDm _).mp hγw γ hγ
    rw [dist_smul] at h1
    have e : dist w (γ⁻¹ • p) = dist (γ • w) p := by
      rw [← dist_smul γ, smul_inv_smul]
    rw [e]
    exact h1
  by_cases hall : ∀ z : UpperHalfPlane, dist z p = dist z (γ⁻¹ • p) → z ∈ D
  · exact Or.inr hall
  left
  push_neg at hall
  obtain ⟨b, hbB, hbD⟩ := hall
  -- the geodesic segment from `w` to `b` stays on the bisector (two applications of (B2.4.i))
  obtain ⟨σ, hσc, hσ0, hσ1, hσseg⟩ := s13c_fc_path w b
  have hσB : ∀ t ∈ Icc (0 : ℝ) 1, dist (σ t) p = dist (σ t) (γ⁻¹ • p) := by
    intro t ht
    exact le_antisymm (s13c_sc_convex hwB.le hbB.le (hσseg t ht))
      (s13c_sc_convex hwB.ge hbB.ge (hσseg t ht))
  -- the first time the segment leaves `D`
  obtain ⟨U, hU⟩ : ∃ U : Set ℝ, U = {t | t ∈ Icc (0 : ℝ) 1 ∧ σ t ∉ D} := ⟨_, rfl⟩
  have h1U : (1 : ℝ) ∈ U := by
    rw [hU]
    exact ⟨⟨zero_le_one, le_rfl⟩, by rw [hσ1]; exact hbD⟩
  have hUb : BddBelow U := ⟨0, fun t ht => by rw [hU] at ht; exact ht.1.1⟩
  set ts := sInf U with hts
  have hts0 : 0 ≤ ts := le_csInf ⟨1, h1U⟩ fun t ht => by rw [hU] at ht; exact ht.1.1
  have hts1 : ts ≤ 1 := csInf_le hUb h1U
  have hbelow : ∀ t, 0 ≤ t → t < ts → σ t ∈ D := by
    intro t ht0 hlt
    by_contra hc
    have htU : t ∈ U := by
      rw [hU]
      exact ⟨⟨ht0, by linarith⟩, hc⟩
    exact absurd (csInf_le hUb htU) (not_le.mpr hlt)
  have heD : σ ts ∈ D := by
    rcases eq_or_lt_of_le hts0 with h0 | h0
    · rw [← h0, hσ0]
      exact hw
    · have hcl : IsClosed (σ ⁻¹' D) := hDcl.preimage hσc
      have hsub : Ico 0 ts ⊆ σ ⁻¹' D := fun t ht => hbelow t ht.1 ht.2
      have hmem := closure_mono hsub (by rw [closure_Ico h0.ne]; exact ⟨h0.le, le_rfl⟩)
      rwa [hcl.closure_eq] at hmem
  have heB := hσB ts ⟨hts0, hts1⟩
  by_cases hh : ∃ h ∈ Γ', h • p ≠ p ∧ h • p ≠ γ⁻¹ • p ∧ dist (σ ts) p = dist (σ ts) (h • p)
  · obtain ⟨h, hhΓ, hh1, hh2, hh3⟩ := hh
    refine ⟨σ ts, ?_, heB⟩
    rw [hV]
    refine ⟨heD, γ⁻¹, hγi, h, hhΓ, fun h' => hγp ?_, hh1, Ne.symm hh2, heB, hh3⟩
    have h2 := congrArg (fun x => γ • x) h'
    simp only [smul_inv_smul] at h2
    exact h2.symm
  -- otherwise every other bisector through a nearby orbit point is strictly beyond `σ ts`
  exfalso
  push_neg at hh
  have hstrict : ∀ g ∈ Γ', g • p ≠ p → g • p ≠ γ⁻¹ • p → dist (σ ts) p < dist (σ ts) (g • p) :=
    fun g hg h1 h2 => lt_of_le_of_ne ((hDm _).mp heD g hg) (hh g hg h1 h2)
  have hFin : {g | g ∈ Γ' ∧ g • p ≠ p ∧ g • p ≠ γ⁻¹ • p ∧ dist (g • p) (σ ts) ≤ dist (σ ts) p + 2}.Finite :=
    (LiZhongQC.s82dx_finite_ball hΓ' p (σ ts) (dist (σ ts) p + 2)).subset fun g hg => ⟨hg.1, hg.2.2.2⟩
  have hev1 : ∀ᶠ x in 𝓝 (σ ts), ∀ g ∈ {g | g ∈ Γ' ∧ g • p ≠ p ∧ g • p ≠ γ⁻¹ • p ∧
      dist (g • p) (σ ts) ≤ dist (σ ts) p + 2}, dist x p < dist x (g • p) := by
    refine (Filter.eventually_all_finite hFin).mpr fun g hg => ?_
    exact (continuous_id.dist continuous_const).continuousAt.eventually_lt
      (continuous_id.dist continuous_const).continuousAt (hstrict g hg.1 hg.2.1 hg.2.2.1)
  have hev2 : ∀ᶠ x in 𝓝 (σ ts), dist x (σ ts) < 1 := Metric.ball_mem_nhds _ one_pos
  have hevP : ∀ᶠ x in 𝓝 (σ ts), ∀ g ∈ Γ', g • p ≠ γ⁻¹ • p → dist x p ≤ dist x (g • p) := by
    filter_upwards [hev1, hev2] with x hx1 hx2
    intro g hg hgq
    by_cases hgp : g • p = p
    · simp [hgp]
    by_cases hnear : dist (g • p) (σ ts) ≤ dist (σ ts) p + 2
    · exact (hx1 g ⟨hg, hgp, hgq, hnear⟩).le
    · push_neg at hnear
      have t1 := dist_triangle (g • p) x (σ ts)
      have t2 := dist_triangle x (σ ts) p
      have t3 := dist_comm x (g • p)
      linarith
  have hevt := hσc.continuousAt.tendsto.eventually hevP
  obtain ⟨ε, hε, hεP⟩ := Metric.eventually_nhds_iff.mp hevt
  obtain ⟨u, huU, hu⟩ := exists_lt_of_csInf_lt ⟨1, h1U⟩ (show sInf U < ts + ε by rw [← hts]; linarith)
  have hu1 : ts ≤ u := csInf_le hUb huU
  rw [hU] at huU
  apply huU.2
  rw [hDm]
  intro g hg
  by_cases hgq : g • p = γ⁻¹ • p
  · rw [hgq]
    exact (hσB u huU.1).le
  · exact hεP (by rw [Real.dist_eq, abs_of_nonneg (by linarith)]; linarith) g hg hgq

/-- **(B2.4.iii) Vertex cycles.** `ang v` is the interior angle of `D` at `v`: the Lebesgue measure of the directions
`θ ∈ (-π, π]` whose geodesic ray from `v` (in the disc chart `ζ ↦ (v - v̄ ζ)/(1 - ζ)` centred at `v`) stays in `D` for
a short time; it is a genuine measure, at most `2π`. For a vertex `v`, its cycle `C = Γ' v ∩ V` is finite and
`π/3 + Σ_{u ∈ C} ang u ≤ |C| π`. (The copies `k D` through `v` have disjoint direction sets, so if `m` is the order of
the stabiliser of `v` modulo `±1`, then `m Σ_C ang ≤ 2π`; there are `|C| m ≥ 3` copies, since `p` has trivial
stabiliser modulo `±1` by `hp`, so torsion is counted honestly.) -/
theorem s13c_sc_cycle {Γ' : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} (hΓ' : LiZhongQC.IsFuchsian Γ')
    {p : UpperHalfPlane} (hp : ∀ γ ∈ Γ', γ • p = p → γ = 1 ∨ γ = -1) (D V : Set UpperHalfPlane)
    (hDdef : D = {w : UpperHalfPlane | ∀ g ∈ Γ', dist w p ≤ dist w (g • p)})
    (hV : V = {v : UpperHalfPlane | v ∈ D ∧ ∃ g ∈ Γ', ∃ h ∈ Γ', g • p ≠ p ∧ h • p ≠ p ∧ g • p ≠ h • p ∧
      dist v p = dist v (g • p) ∧ dist v p = dist v (h • p)})
    (ang : UpperHalfPlane → ℝ≥0∞)
    (hang : ∀ v : UpperHalfPlane, ang v = volume {θ : ℝ | θ ∈ Ioc (-π) π ∧ ∀ᶠ s : ℝ in 𝓝[>] (0 : ℝ),
      ((v : ℂ) - conj (v : ℂ) * ((s : ℂ) * Complex.exp ((θ : ℂ) * I))) / (1 - (s : ℂ) * Complex.exp ((θ : ℂ) * I)) ∈
        ((↑) : UpperHalfPlane → ℂ) '' D})
    {v : UpperHalfPlane} (hv : v ∈ V) :
    {u : UpperHalfPlane | u ∈ V ∧ ∃ g ∈ Γ', g • v = u}.Finite ∧
      ∀ C : Finset UpperHalfPlane, (C : Set UpperHalfPlane) = {u : UpperHalfPlane | u ∈ V ∧ ∃ g ∈ Γ', g • v = u} →
        ENNReal.ofReal (π / 3) + ∑ u ∈ C, ang u ≤ (C.card : ℝ≥0∞) * ENNReal.ofReal π := by
  have hDm : ∀ x : UpperHalfPlane, x ∈ D ↔ ∀ g ∈ Γ', dist x p ≤ dist x (g • p) := by
    intro x
    simp only [hDdef, mem_setOf_eq]
  have hDqcl : ∀ q : UpperHalfPlane, IsClosed {x : UpperHalfPlane | ∀ k ∈ Γ', dist x q ≤ dist x (k • p)} := by
    intro q
    simp only [setOf_forall]
    exact isClosed_iInter fun k => isClosed_iInter fun _ =>
      isClosed_le (continuous_id.dist continuous_const) (continuous_id.dist continuous_const)
  have hDcl : IsClosed D := by
    rw [hDdef]
    exact hDqcl p
  rw [hV] at hv
  obtain ⟨hvD, gA, hgA, gB, hgB, hgAp, hgBp, hgh, hvg, hvh⟩ := hv
  -- the elements carrying `v` into `D`
  have hGfin : {g | g ∈ Γ' ∧ g • v ∈ D}.Finite := by
    have hfin := LiZhongQC.s82dx_finite_ball hΓ' p v (dist v p)
    refine (hfin.preimage inv_injective.injOn).subset ?_
    rintro g ⟨hg, hgv⟩
    refine ⟨Γ'.inv_mem hg, ?_⟩
    have h1 := (hDm _).mp hgv g hg
    rw [dist_smul] at h1
    have e : dist (g⁻¹ • p) v = dist (g • v) p := by
      rw [dist_comm, ← dist_smul g v (g⁻¹ • p), smul_inv_smul]
    rw [e]
    exact h1
  have hCfin : {u | u ∈ V ∧ ∃ g ∈ Γ', g • v = u}.Finite := by
    refine (hGfin.image fun g => g • v).subset ?_
    rintro u ⟨huV, g, hg, rfl⟩
    have huD : g • v ∈ D := by
      rw [hV] at huV
      exact huV.1
    exact ⟨g, ⟨hg, huD⟩, rfl⟩
  refine ⟨hCfin, fun C hC => ?_⟩
  -- basic facts about copies of `D` through `v`
  have hqdist : ∀ g ∈ Γ', g • v ∈ D → dist v (g⁻¹ • p) = dist v p := by
    intro g hg hgv
    apply le_antisymm
    · have h1 := (hDm _).mp hgv g hg
      rw [dist_smul] at h1
      rw [← dist_smul g v (g⁻¹ • p), smul_inv_smul]
      exact h1
    · exact (hDm v).mp hvD _ (Γ'.inv_mem hg)
  have hDq : ∀ g ∈ Γ', ∀ x : UpperHalfPlane,
      (∀ k ∈ Γ', dist x (g⁻¹ • p) ≤ dist x (k • p)) ↔ g • x ∈ D := by
    intro g hg x
    rw [hDm]
    constructor
    · intro h k hk
      have h1 := h (g⁻¹ * k) (Γ'.mul_mem (Γ'.inv_mem hg) hk)
      rw [mul_smul, ← dist_smul g x (g⁻¹ • p), ← dist_smul g x (g⁻¹ • k • p), smul_inv_smul,
        smul_inv_smul] at h1
      exact h1
    · intro h k hk
      have h1 := h (g * k) (Γ'.mul_mem hg hk)
      rw [mul_smul, dist_smul] at h1
      rw [← dist_smul g x (g⁻¹ • p), smul_inv_smul]
      exact h1
  have hinvD : ∀ g ∈ Γ', dist v p = dist v (g • p) → g⁻¹ • v ∈ D := by
    intro g hg hvgp
    rw [hDm]
    intro k hk
    have h1 := (hDm v).mp hvD (g * k) (Γ'.mul_mem hg hk)
    rw [← dist_smul g⁻¹ v (g • p), inv_smul_smul] at hvgp
    rw [mul_smul, ← dist_smul g⁻¹ v (g • k • p), inv_smul_smul] at h1
    rw [← hvgp]
    exact h1
  have hneg : ∀ k : Matrix.SpecialLinearGroup (Fin 2) ℝ, (-k) • v = k • v := by
    intro k
    apply UpperHalfPlane.ext
    rw [s13c_smul_coe, s13c_smul_coe]
    simp only [Matrix.SpecialLinearGroup.coe_neg, Matrix.neg_apply, Complex.ofReal_neg]
    rw [show -((k 0 0 : ℝ) : ℂ) * (v : ℂ) + -((k 0 1 : ℝ) : ℂ) =
        -(((k 0 0 : ℝ) : ℂ) * (v : ℂ) + ((k 0 1 : ℝ) : ℂ)) by ring,
      show -((k 1 0 : ℝ) : ℂ) * (v : ℂ) + -((k 1 1 : ℝ) : ℂ) =
        -(((k 1 0 : ℝ) : ℂ) * (v : ℂ) + ((k 1 1 : ℝ) : ℂ)) by ring, neg_div_neg_eq]
  -- `q = g⁻¹ p` determines `g v` (this is where the trivial stabiliser of `p` enters)
  have hwd : ∀ g k : Matrix.SpecialLinearGroup (Fin 2) ℝ, g ∈ Γ' → k ∈ Γ' → g⁻¹ • p = k⁻¹ • p →
      g • v = k • v := by
    intro g k hg hk hgk
    have hfix : (g * k⁻¹) • p = p := by
      rw [mul_smul, ← hgk, smul_inv_smul]
    rcases hp _ (Γ'.mul_mem hg (Γ'.inv_mem hk)) hfix with h | h
    · rw [mul_inv_eq_one] at h
      rw [h]
    · rw [mul_inv_eq_iff_eq_mul, neg_one_mul] at h
      rw [h, hneg]
  -- vertices of the cycle
  have hVorb : ∀ g ∈ Γ', g • v ∈ D → g • v ∈ V := by
    intro g hg hgv
    have hd0 : dist (g • v) p = dist v p := by
      have h := hqdist g hg hgv
      rw [← h, ← dist_smul g v (g⁻¹ • p), smul_inv_smul]
    have hdk : ∀ k, dist v (k • p) = dist v p → dist (g • v) ((g * k) • p) = dist (g • v) p := by
      intro k hk
      rw [mul_smul, dist_smul, hk, hd0]
    have e1 := hdk 1 (by rw [one_smul])
    have e2 := hdk gA hvg.symm
    have e3 := hdk gB hvh.symm
    rw [mul_one] at e1
    have n12 : g • p ≠ (g * gA) • p := fun h => hgAp (by rw [mul_smul] at h; exact (smul_left_cancel g h).symm)
    have n13 : g • p ≠ (g * gB) • p := fun h => hgBp (by rw [mul_smul] at h; exact (smul_left_cancel g h).symm)
    have n23 : (g * gA) • p ≠ (g * gB) • p := fun h => hgh (by rw [mul_smul, mul_smul] at h; exact smul_left_cancel g h)
    rw [hV]
    refine ⟨hgv, ?_⟩
    by_cases ha : g • p = p
    · exact ⟨g * gA, Γ'.mul_mem hg hgA, g * gB, Γ'.mul_mem hg hgB, fun h => n12 (ha.trans h.symm),
        fun h => n13 (ha.trans h.symm), n23, e2.symm, e3.symm⟩
    · by_cases hb : (g * gA) • p = p
      · exact ⟨g, hg, g * gB, Γ'.mul_mem hg hgB, ha, fun h => n23 (hb.trans h.symm), n13, e1.symm, e3.symm⟩
      · exact ⟨g, hg, g * gA, Γ'.mul_mem hg hgA, ha, hb, n12, e1.symm, e2.symm⟩
  have hangpi : ∀ u ∈ V, ang u ≤ ENNReal.ofReal π := by
    intro u hu
    rw [hV] at hu
    obtain ⟨huD, g, hg, -, -, hgp, -, -, hug, -⟩ := hu
    obtain ⟨B, hB, hBiff⟩ := s13c_cy_half u p (g • p) (Ne.symm hgp) hug
    rw [hang u]
    refine le_trans (measure_mono ?_) (s13c_cy_halfvol B hB)
    rintro θ ⟨hθ, hev⟩
    refine ⟨hθ, ?_⟩
    obtain ⟨s, hsD, hs0, hs1⟩ := (hev.and (Ioo_mem_nhdsGT one_pos)).exists
    have hmem := (s13c_cy_memiff u θ s hs0.le hs1 D).mp hsD
    exact ((hBiff θ s hs0 hs1).1).mp ((hDm _).mp hmem g hg)
  -- the copies through `v`, indexed by the orbit points `q = g⁻¹ p`
  have hQfin : ((fun g : Matrix.SpecialLinearGroup (Fin 2) ℝ => g⁻¹ • p) '' {g | g ∈ Γ' ∧ g • v ∈ D}).Finite :=
    hGfin.image _
  set Q := hQfin.toFinset with hQ
  have hmemQ : ∀ q, q ∈ Q ↔ ∃ g, (g ∈ Γ' ∧ g • v ∈ D) ∧ g⁻¹ • p = q := by
    intro q
    rw [hQ, Set.Finite.mem_toFinset]
    rfl
  have hpQ : ∀ g ∈ Γ', g • v ∈ D → g⁻¹ • p ∈ Q := fun g hg hgv => (hmemQ _).mpr ⟨g, ⟨hg, hgv⟩, rfl⟩
  choose! φg hφg using fun q (hq : q ∈ Q) => (hmemQ q).mp hq
  obtain ⟨Θ, hΘ⟩ : ∃ Θ : UpperHalfPlane → Set ℝ, Θ = fun q => {θ : ℝ | θ ∈ Ioc (-π) π ∧
      ∀ᶠ s : ℝ in 𝓝[>] (0 : ℝ),
        ((v : ℂ) - conj (v : ℂ) * ((s : ℂ) * Complex.exp ((θ : ℂ) * I))) / (1 - (s : ℂ) * Complex.exp ((θ : ℂ) * I)) ∈
          ((↑) : UpperHalfPlane → ℂ) '' {x : UpperHalfPlane | ∀ k ∈ Γ', dist x q ≤ dist x (k • p)}} := ⟨_, rfl⟩
  -- each copy has the angle of the corresponding vertex of the cycle
  have hΘvol : ∀ q ∈ Q, volume (Θ q) = ang (φg q • v) := by
    intro q hq
    obtain ⟨⟨hgΓ, hgD⟩, hgq⟩ := hφg q hq
    obtain ⟨c, hc⟩ := s13c_cy_rot (φg q) v
    have hDq' : ∀ x : UpperHalfPlane, (∀ k ∈ Γ', dist x q ≤ dist x (k • p)) ↔ φg q • x ∈ D := fun x => by
      have h := hDq (φg q) hgΓ x
      rwa [hgq] at h
    have hSm := s13c_cy_meas (φg q • v) hDcl
    have hper : ∀ θ : ℝ, θ + 2 * π ∈ {θ : ℝ | ∀ᶠ s : ℝ in 𝓝[>] (0 : ℝ),
        (((φg q • v : UpperHalfPlane) : ℂ) - conj ((φg q • v : UpperHalfPlane) : ℂ) *
          ((s : ℂ) * Complex.exp ((θ : ℂ) * I))) / (1 - (s : ℂ) * Complex.exp ((θ : ℂ) * I)) ∈
          ((↑) : UpperHalfPlane → ℂ) '' D} ↔ θ ∈ {θ : ℝ | ∀ᶠ s : ℝ in 𝓝[>] (0 : ℝ),
        (((φg q • v : UpperHalfPlane) : ℂ) - conj ((φg q • v : UpperHalfPlane) : ℂ) *
          ((s : ℂ) * Complex.exp ((θ : ℂ) * I))) / (1 - (s : ℂ) * Complex.exp ((θ : ℂ) * I)) ∈
          ((↑) : UpperHalfPlane → ℂ) '' D} := by
      intro θ
      have he : Complex.exp (((θ + 2 * π : ℝ) : ℂ) * I) = Complex.exp ((θ : ℂ) * I) := by
        rw [show ((θ + 2 * π : ℝ) : ℂ) * I = (θ : ℂ) * I + 2 * π * I by push_cast; ring, Complex.exp_add,
          Complex.exp_two_pi_mul_I, mul_one]
      simp only [mem_setOf_eq, he]
    have hsh := s13c_cy_shift hSm hper c
    rw [hang (φg q • v)]
    refine Eq.trans ?_ hsh
    simp only [hΘ]
    congr 1
    ext θ
    simp only [mem_setOf_eq]
    refine and_congr_right fun _ => ?_
    apply Filter.eventually_congr
    filter_upwards [Ioo_mem_nhdsGT one_pos] with s hs
    rw [s13c_cy_memiff v θ s hs.1.le hs.2, mem_setOf_eq, hDq', ← hc θ s hs.1.le hs.2,
      s13c_cy_coe_mem]
  -- distinct copies meet in a null set of directions
  have hΘdisj : ∀ q ∈ Q, ∀ q' ∈ Q, q ≠ q' → volume (Θ q ∩ Θ q') = 0 := by
    intro q hq q' hq' hne
    obtain ⟨⟨hgΓ, hgD⟩, hgq⟩ := hφg q hq
    obtain ⟨⟨hg'Γ, hg'D⟩, hg'q⟩ := hφg q' hq'
    have hd1 := hqdist _ hgΓ hgD
    have hd2 := hqdist _ hg'Γ hg'D
    rw [hgq] at hd1
    rw [hg'q] at hd2
    obtain ⟨B, hB, hBiff⟩ := s13c_cy_half v q q' hne (hd1.trans hd2.symm)
    refine measure_mono_null ?_ (s13c_cy_zero B hB)
    rintro θ ⟨h1, h2⟩
    simp only [hΘ, mem_setOf_eq] at h1 h2
    obtain ⟨s, ⟨hs1, hs2⟩, hs0, hs1'⟩ := ((h1.2.and h2.2).and (Ioo_mem_nhdsGT one_pos)).exists
    rw [s13c_cy_memiff v θ s hs0.le hs1'] at hs1 hs2
    simp only [mem_setOf_eq] at hs1 hs2
    have a1 := hs1 _ (Γ'.inv_mem hg'Γ)
    have a2 := hs2 _ (Γ'.inv_mem hgΓ)
    rw [hg'q] at a1
    rw [hgq] at a2
    exact le_antisymm ((hBiff θ s hs0 hs1').2.mp a2) ((hBiff θ s hs0 hs1').1.mp a1)
  -- so the angles of the copies add up to at most `2π`
  have hsumΘ : ∑ q ∈ Q, volume (Θ q) ≤ ENNReal.ofReal (2 * π) := by
    have hd : Set.Pairwise (Q : Set UpperHalfPlane) (Function.onFun (AEDisjoint volume) Θ) :=
      fun q hq q' hq' hne => hΘdisj q hq q' hq' hne
    have hm : ∀ q ∈ Q, NullMeasurableSet (Θ q) volume := by
      intro q _
      rw [hΘ]
      exact (measurableSet_Ioc.inter (s13c_cy_meas v (hDqcl q))).nullMeasurableSet
    rw [← measure_biUnion_finset₀ hd hm]
    calc volume (⋃ q ∈ Q, Θ q) ≤ volume (Ioc (-π) π) :=
          measure_mono (iUnion₂_subset fun q _ θ hθ => by simp only [hΘ, mem_setOf_eq] at hθ; exact hθ.1)
      _ = ENNReal.ofReal (2 * π) := by
          rw [Real.volume_Ioc]
          congr 1
          ring
  -- there are at least three copies
  have hQ3 : 3 ≤ Q.card := by
    have h1 : p ∈ Q := by
      have h := hpQ 1 Γ'.one_mem (by rw [one_smul]; exact hvD)
      rwa [inv_one, one_smul] at h
    have h2 : gA • p ∈ Q := by
      have h := hpQ gA⁻¹ (Γ'.inv_mem hgA) (hinvD gA hgA hvg)
      rwa [inv_inv] at h
    have h3 : gB • p ∈ Q := by
      have h := hpQ gB⁻¹ (Γ'.inv_mem hgB) (hinvD gB hgB hvh)
      rwa [inv_inv] at h
    have hsub : ({p, gA • p, gB • p} : Finset UpperHalfPlane) ⊆ Q := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl
      · exact h1
      · exact h2
      · exact h3
    have hcard : ({p, gA • p, gB • p} : Finset UpperHalfPlane).card = 3 :=
      Finset.card_eq_three.mpr ⟨p, gA • p, gB • p, Ne.symm hgAp, Ne.symm hgBp, hgh, rfl⟩
    rw [← hcard]
    exact Finset.card_le_card hsub
  -- fibres of `q ↦ g v` over the cycle
  have hCV : ∀ u ∈ C, u ∈ V := fun u hu => by
    have h : u ∈ (C : Set UpperHalfPlane) := hu
    rw [hC] at h
    exact h.1
  have hφC : ∀ q ∈ Q, φg q • v ∈ C := by
    intro q hq
    obtain ⟨⟨hgΓ, hgD⟩, -⟩ := hφg q hq
    have h : φg q • v ∈ (C : Set UpperHalfPlane) := by
      rw [hC]
      exact ⟨hVorb _ hgΓ hgD, _, hgΓ, rfl⟩
    exact h
  have hφwd : ∀ q ∈ Q, ∀ g ∈ Γ', g⁻¹ • p = q → φg q • v = g • v := by
    intro q hq g hg hgq
    obtain ⟨⟨hkΓ, -⟩, hkq⟩ := hφg q hq
    exact (hwd g (φg q) hg hkΓ (hgq.trans hkq.symm)).symm
  have hfib : ∀ u ∈ C, 1 ≤ (Q.filter fun q => φg q • v = u).card := by
    intro u hu
    have hu' : u ∈ (C : Set UpperHalfPlane) := hu
    rw [hC] at hu'
    obtain ⟨huV, g, hg, rfl⟩ := hu'
    have hgD : g • v ∈ D := by
      rw [hV] at huV
      exact huV.1
    apply Finset.card_pos.mpr
    exact ⟨g⁻¹ • p, Finset.mem_filter.mpr ⟨hpQ g hg hgD, hφwd _ (hpQ g hg hgD) g hg rfl⟩⟩
  have hfibsum : ∑ u ∈ C, (Q.filter fun q => φg q • v = u).card = Q.card :=
    (Finset.card_eq_sum_card_fiberwise fun q hq => hφC q hq).symm
  have hsum1 : ∑ q ∈ Q, ang (φg q • v) ≤ ENNReal.ofReal (2 * π) := by
    calc ∑ q ∈ Q, ang (φg q • v) = ∑ q ∈ Q, volume (Θ q) :=
          Finset.sum_congr rfl fun q hq => (hΘvol q hq).symm
      _ ≤ _ := hsumΘ
  rw [← Finset.sum_fiberwise_of_maps_to hφC] at hsum1
  have hinner : ∀ u ∈ C, ∑ q ∈ Q with φg q • v = u, ang (φg q • v) =
      ((Q.filter fun q => φg q • v = u).card : ℝ≥0∞) * ang u := by
    intro u _
    rw [Finset.sum_congr rfl fun q hq => congrArg ang (Finset.mem_filter.mp hq).2, Finset.sum_const,
      nsmul_eq_mul]
  rw [Finset.sum_congr rfl hinner] at hsum1
  -- conclude in `ℝ`
  have hangfin : ∀ u ∈ C, ang u ≠ ∞ := fun u hu =>
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hangpi u (hCV u hu))
  have key := s13c_cy_arith C (fun u => (ang u).toReal) (fun u => (Q.filter fun q => φg q • v = u).card)
    (fun u _ => ENNReal.toReal_nonneg)
    (fun u hu => ENNReal.toReal_le_of_le_ofReal Real.pi_pos.le (hangpi u (hCV u hu)))
    hfib (by rw [hfibsum]; exact hQ3) (by
      have h := ENNReal.toReal_le_of_le_ofReal (by positivity) hsum1
      rw [ENNReal.toReal_sum fun u hu => ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) (hangfin u hu)] at h
      simpa only [ENNReal.toReal_mul, ENNReal.toReal_natCast] using h)
  have hsumC : ∑ u ∈ C, ang u = ENNReal.ofReal (∑ u ∈ C, (ang u).toReal) := by
    rw [ENNReal.ofReal_sum_of_nonneg fun u _ => ENNReal.toReal_nonneg]
    exact Finset.sum_congr rfl fun u hu => (ENNReal.ofReal_toReal (hangfin u hu)).symm
  rw [hsumC, ← ENNReal.ofReal_add (by positivity) (Finset.sum_nonneg fun u _ => ENNReal.toReal_nonneg),
    show (C.card : ℝ≥0∞) * ENNReal.ofReal π = ENNReal.ofReal ((C.card : ℝ) * π) by
      rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]]
  exact ENNReal.ofReal_le_ofReal key

/-- **(B2.4.iv-a) Gauss–Bonnet bound on the vertex angles** (Katok, Thm 4.1.1, (4.1.5)). For every finite set `S` of
vertices of `D`, `Σ_{u ∈ S} (π - ang u) ≤ area D + 3π`, stated without subtraction. Proof: the geodesic triangles
from `p` to consecutive vertices of `S` (ordered by direction at `p`) lie in `D` with disjoint interiors, their
angles at `p` sum to at most `2π`, the two triangles at `u` lie in the angle of `D` at `u`, and each triangle has
area `π − (sum of its angles)` (computed as an explicit `lintegral` of `y⁻²`; any `arcsin` only on `[-1, 1]`). -/
theorem s13c_sc_gb {Γ' : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} (hΓ' : LiZhongQC.IsFuchsian Γ')
    {p : UpperHalfPlane} (D V : Set UpperHalfPlane)
    (hDdef : D = {w : UpperHalfPlane | ∀ g ∈ Γ', dist w p ≤ dist w (g • p)})
    (hV : V = {v : UpperHalfPlane | v ∈ D ∧ ∃ g ∈ Γ', ∃ h ∈ Γ', g • p ≠ p ∧ h • p ≠ p ∧ g • p ≠ h • p ∧
      dist v p = dist v (g • p) ∧ dist v p = dist v (h • p)})
    (ang : UpperHalfPlane → ℝ≥0∞)
    (hang : ∀ v : UpperHalfPlane, ang v = volume {θ : ℝ | θ ∈ Ioc (-π) π ∧ ∀ᶠ s : ℝ in 𝓝[>] (0 : ℝ),
      ((v : ℂ) - conj (v : ℂ) * ((s : ℂ) * Complex.exp ((θ : ℂ) * I))) / (1 - (s : ℂ) * Complex.exp ((θ : ℂ) * I)) ∈
        ((↑) : UpperHalfPlane → ℂ) '' D})
    (S : Finset UpperHalfPlane) (hS : (S : Set UpperHalfPlane) ⊆ V) :
    (S.card : ℝ≥0∞) * ENNReal.ofReal π ≤
      ∑ u ∈ S, ang u + (∫⁻ z in ((↑) : UpperHalfPlane → ℂ) '' D, ENNReal.ofReal ((z.im ^ 2)⁻¹)) +
        ENNReal.ofReal (3 * π) := by
  have hDm : ∀ x : UpperHalfPlane, x ∈ D ↔ ∀ g ∈ Γ', dist x p ≤ dist x (g • p) := by
    intro x
    simp only [hDdef, mem_setOf_eq]
  have hDcl : IsClosed D := by
    rw [hDdef]
    simp only [setOf_forall]
    exact isClosed_iInter fun k => isClosed_iInter fun _ =>
      isClosed_le (continuous_id.dist continuous_const) (continuous_id.dist continuous_const)
  -- every vertex lies in `D`, differs from `p` and is equidistant from `p` and some `g p ≠ p`
  have hVS : ∀ u ∈ S, u ∈ D ∧ u ≠ p ∧ ∃ g ∈ Γ', g • p ≠ p ∧ dist u p = dist u (g • p) := by
    intro u hu
    have h := hS (Finset.mem_coe.mpr hu)
    rw [hV, mem_setOf_eq] at h
    obtain ⟨huD, g, hg, h', hh', hgp, -, -, hd1, -⟩ := h
    refine ⟨huD, fun hup => hgp ?_, g, hg, hgp, hd1⟩
    rw [hup, dist_self] at hd1
    exact (dist_eq_zero.mp hd1.symm).symm
  -- polar chart coordinates at `p`
  obtain ⟨rf, hrf⟩ : ∃ rf : UpperHalfPlane → ℝ, ∀ u, rf u = ‖((u : ℂ) - p) / ((u : ℂ) - conj (p : ℂ))‖ :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨tf, htf⟩ : ∃ tf : UpperHalfPlane → ℝ,
      ∀ u, tf u = Complex.arg (((u : ℂ) - p) / ((u : ℂ) - conj (p : ℂ))) := ⟨_, fun _ => rfl⟩
  have hpol : ∀ u : UpperHalfPlane,
      ((u : ℂ) - p) / ((u : ℂ) - conj (p : ℂ)) = (rf u : ℂ) * Complex.exp ((tf u : ℂ) * I) := by
    intro u
    rw [hrf, htf]
    exact (Complex.norm_mul_exp_arg_mul_I _).symm
  have hr1 : ∀ u, rf u < 1 := fun u => by
    rw [hrf]
    exact s13c_ga_nlt u p
  have hr0 : ∀ u, u ≠ p → 0 < rf u := by
    intro u hu
    rw [hrf]
    exact norm_pos_iff.mpr (div_ne_zero (sub_ne_zero.mpr fun h => hu (UpperHalfPlane.ext h)) (s13c_ga_ne u p))
  -- the angular gap from `u` to `v`, in `(0, 2π]`
  obtain ⟨gp, hgp⟩ : ∃ gp : UpperHalfPlane → UpperHalfPlane → ℝ,
      ∀ u v, gp u v = toIocMod Real.two_pi_pos 0 (tf v - tf u) := ⟨_, fun _ _ => rfl⟩
  have hgpm : ∀ u v, 0 < gp u v ∧ gp u v ≤ 2 * π := by
    intro u v
    have h := toIocMod_mem_Ioc Real.two_pi_pos 0 (tf v - tf u)
    rw [zero_add] at h
    rw [hgp]
    exact h
  have hgpd : ∀ u v, ∃ m : ℤ, gp u v = tf v - tf u - 2 * π * m := by
    intro u v
    refine ⟨toIocDiv Real.two_pi_pos 0 (tf v - tf u), ?_⟩
    rw [hgp, ← self_sub_toIocDiv_zsmul, zsmul_eq_mul]
    ring
  have hgpe : ∀ u v, Complex.exp (((tf u + gp u v : ℝ) : ℂ) * I) = Complex.exp ((tf v : ℂ) * I) := by
    intro u v
    obtain ⟨m, hm⟩ := hgpd u v
    have e : tf u + gp u v = tf v + 2 * π * ((-m : ℤ) : ℝ) := by
      rw [hm]
      push_cast
      ring
    rw [e, s13c_ga_per]
  have hgps : ∀ u, gp u u = 2 * π := by
    intro u
    rw [hgp, sub_self, toIocMod_apply_left, zero_add]
  -- distinct vertices have distinct directions at `p`
  have hdist : ∀ u ∈ S, ∀ v ∈ S, u ≠ v → gp u v < 2 * π := by
    intro u hu v hv huv
    rcases (hgpm u v).2.lt_or_eq with h | h
    · exact h
    exfalso
    have he : Complex.exp ((tf v : ℂ) * I) = Complex.exp ((tf u : ℂ) * I) := by
      rw [← hgpe u v, h, s13c_ga_per2]
    have hpv : ((v : ℂ) - p) / ((v : ℂ) - conj (p : ℂ)) = (rf v : ℂ) * Complex.exp ((tf u : ℂ) * I) := by
      rw [hpol v, he]
    obtain ⟨huD, hup, g, hg, hgp', hdu⟩ := hVS u hu
    obtain ⟨hvD, hvp, g', hg', hgp'', hdv⟩ := hVS v hv
    rcases lt_trichotomy (rf u) (rf v) with hlt | heq | hgt
    · exact s13c_ga_ray hgp' hdu ((hDm v).mp hvD g hg) (hr0 u hup) hlt (hr1 v) (hpol u) hpv
    · apply huv
      apply UpperHalfPlane.ext
      rw [← s13c_ga_inv p u (hpol u), ← s13c_ga_inv p v hpv, heq]
    · exact s13c_ga_ray hgp'' hdv ((hDm u).mp huD g' hg') (hr0 v hvp) hgt (hr1 u) hpv (hpol u)
  -- the successor of each vertex in the direction order at `p`
  have hnext : ∀ u, ∃ v, u ∈ S → v ∈ S ∧ ∀ v' ∈ S, gp u v ≤ gp u v' := by
    intro u
    by_cases hu : u ∈ S
    · obtain ⟨v, hv, hmin⟩ := S.exists_min_image (gp u) ⟨u, hu⟩
      exact ⟨v, fun _ => ⟨hv, hmin⟩⟩
    · exact ⟨u, fun h => absurd h hu⟩
  choose nx hnx using hnext
  -- the gap arcs `(θ_u, θ_u + α_u)` mod `2π` are pairwise disjoint
  have hcore : ∀ u ∈ S, ∀ u' ∈ S, u ≠ u' → ∀ (θ : ℝ) (k k' : ℤ), tf u + 2 * π * k < θ →
      θ < tf u + gp u (nx u) + 2 * π * k → tf u' + 2 * π * k' < θ → θ < tf u' + gp u' (nx u') + 2 * π * k' →
      θ - tf u' - 2 * π * k' ≤ θ - tf u - 2 * π * k → False := by
    intro u hu u' hu' hne θ k k' h1 h2 h3 h4 hle
    have hmin := (hnx u hu).2 u' hu'
    have e : tf u' - tf u = ((θ - tf u - 2 * π * k) - (θ - tf u' - 2 * π * k')) + (k - k') • (2 * π) := by
      rw [zsmul_eq_mul]
      push_cast
      ring
    have hg : gp u u' = toIocMod Real.two_pi_pos 0 ((θ - tf u - 2 * π * k) - (θ - tf u' - 2 * π * k')) := by
      rw [hgp, e, toIocMod_add_zsmul]
    have hα2 := (hgpm u (nx u)).2
    rcases (sub_nonneg.mpr hle).lt_or_eq with hpos | hzero
    · have h5 : toIocMod Real.two_pi_pos 0 ((θ - tf u - 2 * π * k) - (θ - tf u' - 2 * π * k')) =
          (θ - tf u - 2 * π * k) - (θ - tf u' - 2 * π * k') :=
        (toIocMod_eq_self _).mpr ⟨hpos, by linarith⟩
      rw [hg, h5] at hmin
      linarith
    · have h5 : gp u u' = 2 * π := by
        rw [hg, ← hzero, toIocMod_apply_left, zero_add]
      linarith [hdist u hu u' hu' hne]
  have hdisj : ∀ u ∈ S, ∀ u' ∈ S, u ≠ u' → ∀ θ : ℝ,
      θ ∈ (⋃ k : ℤ, Ioo (tf u + 2 * π * k) (tf u + gp u (nx u) + 2 * π * k)) →
      θ ∈ (⋃ k : ℤ, Ioo (tf u' + 2 * π * k) (tf u' + gp u' (nx u') + 2 * π * k)) → False := by
    intro u hu u' hu' hne θ h h'
    obtain ⟨k, hk1, hk2⟩ := mem_iUnion.mp h
    obtain ⟨k', hk1', hk2'⟩ := mem_iUnion.mp h'
    rcases le_total (θ - tf u' - 2 * π * k') (θ - tf u - 2 * π * k) with hle | hle
    · exact hcore u hu u' hu' hne θ k k' hk1 hk2 hk1' hk2' hle
    · exact hcore u' hu' u hu (Ne.symm hne) θ k' k hk1' hk2' hk1 hk2 hle
  -- hence the successor map is a permutation of `S`
  have hinj : Set.InjOn nx S := by
    intro u hu u' hu' heq
    by_contra hne
    obtain ⟨m, hm⟩ := hgpd u (nx u)
    obtain ⟨m', hm0⟩ := hgpd u' (nx u')
    have hm' : gp u' (nx u') = tf (nx u) - tf u' - 2 * π * m' := by
      rw [hm0, heq]
    have ha := (hgpm u (nx u)).1
    have ha' := (hgpm u' (nx u')).1
    obtain ⟨ε, hε⟩ : ∃ ε : ℝ, ε = min (gp u (nx u)) (gp u' (nx u')) / 2 := ⟨_, rfl⟩
    have hε0 : 0 < ε := by
      rw [hε]
      exact half_pos (lt_min ha ha')
    have hε1 : ε < gp u (nx u) := by
      rw [hε]
      linarith [min_le_left (gp u (nx u)) (gp u' (nx u'))]
    have hε2 : ε < gp u' (nx u') := by
      rw [hε]
      linarith [min_le_right (gp u (nx u)) (gp u' (nx u'))]
    refine hdisj u hu u' hu' hne (tf u + gp u (nx u) - ε) (mem_iUnion.mpr ⟨0, ?_, ?_⟩)
      (mem_iUnion.mpr ⟨m' - m, ?_, ?_⟩)
    · push_cast
      linarith
    · push_cast
      linarith
    · push_cast
      linarith
    · push_cast
      linarith
  have himg : S.image nx = S :=
    Finset.eq_of_subset_of_card_le (Finset.image_subset_iff.mpr fun u hu => (hnx u hu).1)
      (Finset.card_image_of_injOn hinj).ge
  have hre : ∀ f : UpperHalfPlane → ℝ≥0∞, ∑ u ∈ S, f (nx u) = ∑ w ∈ S, f w := by
    intro f
    calc ∑ u ∈ S, f (nx u) = ∑ w ∈ S.image nx, f w := (Finset.sum_image hinj).symm
      _ = ∑ w ∈ S, f w := by rw [himg]
  -- one triangle per gap
  have hgap := fun u (hu : u ∈ S) => s13c_ga_gap D hDdef (hVS u hu).1 (hVS (nx u) (hnx u hu).1).1
    (hVS u hu).2.1 (hVS (nx u) (hnx u hu).1).2.1
    (fun hα heq => by
      rw [heq, hgps] at hα
      linarith [Real.pi_pos])
    (hr0 u (hVS u hu).2.1) (hr1 u) (hr0 (nx u) (hVS (nx u) (hnx u hu).1).2.1) (hr1 (nx u))
    (hgpm u (nx u)).1 (hgpm u (nx u)).2 (hpol u) (by rw [hpol (nx u), hgpe u (nx u)])
  choose! bR bL ar Gu hG using hgap
  -- (c) the two arcs at each vertex lie in its angle
  have hvx : ∀ u ∈ S, ENNReal.ofReal (bR (nx u)) + ENNReal.ofReal (bL u) ≤ ang (nx u) := by
    intro u hu
    have hw := (hnx u hu).1
    obtain ⟨hbR0, hbRπ, -, -, -, -, hR, -, -, -, -, -⟩ := hG (nx u) hw
    obtain ⟨-, -, hbL0, hbLπ, -, -, -, hL, -, -, -, -⟩ := hG u hu
    rw [hang (nx u), ← ENNReal.ofReal_add hbR0 hbL0]
    refine s13c_ga_pmeas (s13c_cy_meas (nx u) hDcl) (fun θ => by simp only [mem_setOf_eq, s13c_ga_per2])
      (L := Complex.arg (((p : ℂ) - (nx u : UpperHalfPlane)) / ((p : ℂ) - conj ((nx u : UpperHalfPlane) : ℂ))) -
        bR (nx u)) (by linarith) ?_
    intro θ hθ
    by_cases hθd : θ ≤ Complex.arg (((p : ℂ) - (nx u : UpperHalfPlane)) /
        ((p : ℂ) - conj ((nx u : UpperHalfPlane) : ℂ)))
    · exact hR θ hθ.1 hθd
    · exact hL θ (le_of_not_ge hθd) (by linarith [hθ.2])
  -- (a) the triangles have disjoint interiors in `D`
  have harea : ∑ u ∈ S, ENNReal.ofReal (ar u) ≤
      ∫⁻ z in ((↑) : UpperHalfPlane → ℂ) '' D, ENNReal.ofReal ((z.im ^ 2)⁻¹) := by
    rw [s13c_pc_area p hDcl.measurableSet]
    calc ∑ u ∈ S, ENNReal.ofReal (ar u) ≤ ∑ u ∈ S, ∫⁻ θ in Ioc (-π) π, Gu u θ :=
          Finset.sum_le_sum fun u hu => (hG u hu).2.2.2.2.2.2.2.2.2.2.2
      _ = ∫⁻ θ in Ioc (-π) π, ∑ u ∈ S, Gu u θ :=
          (lintegral_finset_sum S fun u hu => (hG u hu).2.2.2.2.2.2.2.2.1).symm
      _ ≤ _ := by
          refine lintegral_mono fun θ => ?_
          by_cases hex : ∃ u ∈ S, θ ∈ (⋃ k : ℤ, Ioo (tf u + 2 * π * k) (tf u + gp u (nx u) + 2 * π * k))
          · obtain ⟨u0, hu0, hθ0⟩ := hex
            rw [Finset.sum_eq_single u0 (fun u hu hne => (hG u hu).2.2.2.2.2.2.2.2.2.2.1 θ
              (fun hθ => hdisj u hu u0 hu0 hne θ hθ hθ0)) (fun h => absurd hu0 h)]
            exact (hG u0 hu0).2.2.2.2.2.2.2.2.2.1 θ
          · push_neg at hex
            rw [Finset.sum_eq_zero fun u hu => (hG u hu).2.2.2.2.2.2.2.2.2.2.1 θ (hex u hu)]
            exact zero_le
  -- (d) the gaps at `p` sum to at most `2π`
  have hαsum : ∑ u ∈ S, ENNReal.ofReal (gp u (nx u)) ≤ ENNReal.ofReal (2 * π) := by
    have hI : ∀ u, MeasurableSet (⋃ k : ℤ, Ioo (tf u + 2 * π * k) (tf u + gp u (nx u) + 2 * π * k)) :=
      fun u => MeasurableSet.iUnion fun k => measurableSet_Ioo
    have hd : Set.PairwiseDisjoint (S : Set UpperHalfPlane)
        (fun u => Ioc (-π) π ∩ ⋃ k : ℤ, Ioo (tf u + 2 * π * k) (tf u + gp u (nx u) + 2 * π * k)) := by
      intro u hu u' hu' hne
      exact Set.disjoint_left.mpr fun θ h1 h2 => hdisj u hu u' hu' hne θ h1.2 h2.2
    calc ∑ u ∈ S, ENNReal.ofReal (gp u (nx u)) ≤
        ∑ u ∈ S, volume (Ioc (-π) π ∩ ⋃ k : ℤ, Ioo (tf u + 2 * π * k) (tf u + gp u (nx u) + 2 * π * k)) :=
          Finset.sum_le_sum fun u _ => s13c_ga_pmeas (hI u) (fun θ => s13c_ga_Iper _ _ θ) (L := tf u)
            (hgpm u (nx u)).2 fun θ hθ => mem_iUnion.mpr ⟨0, by push_cast; linarith [hθ.1],
              by push_cast; linarith [hθ.2]⟩
      _ = volume (⋃ u ∈ S, Ioc (-π) π ∩ ⋃ k : ℤ, Ioo (tf u + 2 * π * k) (tf u + gp u (nx u) + 2 * π * k)) :=
          (measure_biUnion_finset hd fun u _ => measurableSet_Ioc.inter (hI u)).symm
      _ ≤ volume (Ioc (-π) π) := measure_mono (iUnion₂_subset fun u _ => Set.inter_subset_left)
      _ = ENNReal.ofReal (2 * π) := by
          rw [Real.volume_Ioc]
          congr 1
          ring
  -- (b) Gauss–Bonnet for each triangle, summed
  have hterm : ∀ u ∈ S, ENNReal.ofReal π ≤ (ENNReal.ofReal (bR u) + ENNReal.ofReal (bL u)) +
      (ENNReal.ofReal (ar u) + ENNReal.ofReal (gp u (nx u))) := by
    intro u hu
    obtain ⟨hbR0, -, hbL0, -, har0, hsum, -⟩ := hG u hu
    have hα0 := (hgpm u (nx u)).1
    have e : bR u + bL u + ar u + gp u (nx u) = (bR u + bL u) + (ar u + gp u (nx u)) := by ring
    calc ENNReal.ofReal π ≤ ENNReal.ofReal (bR u + bL u + ar u + gp u (nx u)) := ENNReal.ofReal_le_ofReal hsum
      _ = _ := by
          rw [e, ENNReal.ofReal_add (by linarith) (by linarith), ENNReal.ofReal_add hbR0 hbL0,
            ENNReal.ofReal_add har0 hα0.le]
  have hsumR : ∑ u ∈ S, ENNReal.ofReal (bR (nx u)) = ∑ w ∈ S, ENNReal.ofReal (bR w) :=
    hre (fun w => ENNReal.ofReal (bR w))
  have hsumA : ∑ u ∈ S, ang (nx u) = ∑ w ∈ S, ang w := hre ang
  have hvsum : ∑ u ∈ S, ENNReal.ofReal (bR u) + ∑ u ∈ S, ENNReal.ofReal (bL u) ≤ ∑ u ∈ S, ang u := by
    rw [← hsumR, ← Finset.sum_add_distrib, ← hsumA]
    exact Finset.sum_le_sum hvx
  have h3π : ENNReal.ofReal (2 * π) ≤ ENNReal.ofReal (3 * π) :=
    ENNReal.ofReal_le_ofReal (by linarith [Real.pi_pos])
  calc (S.card : ℝ≥0∞) * ENNReal.ofReal π = ∑ u ∈ S, ENNReal.ofReal π := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ u ∈ S, ((ENNReal.ofReal (bR u) + ENNReal.ofReal (bL u)) +
        (ENNReal.ofReal (ar u) + ENNReal.ofReal (gp u (nx u)))) := Finset.sum_le_sum hterm
    _ = (∑ u ∈ S, ENNReal.ofReal (bR u) + ∑ u ∈ S, ENNReal.ofReal (bL u)) +
        (∑ u ∈ S, ENNReal.ofReal (ar u) + ∑ u ∈ S, ENNReal.ofReal (gp u (nx u))) := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib]
    _ ≤ ∑ u ∈ S, ang u + ((∫⁻ z in ((↑) : UpperHalfPlane → ℂ) '' D, ENNReal.ofReal ((z.im ^ 2)⁻¹)) +
        ENNReal.ofReal (3 * π)) := add_le_add hvsum (add_le_add harea (hαsum.trans h3π))
    _ = _ := (add_assoc _ _ _).symm

/-- **(B2.4.iv-b) Ideal faces.** Only finitely many `γ ∈ Γ'` have their whole bisector (the face of `γ` with both
ends at infinity) inside a Dirichlet domain of finite area. Proof: the triangles from `p` over these faces lie in `D`
with disjoint interiors and have area `π − α_γ` (two ideal vertices, `α_γ` the angle at `p`), and `Σ α_γ ≤ 2π`. -/
theorem s13c_sc_ideal {Γ' : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} (hΓ' : LiZhongQC.IsFuchsian Γ')
    {p : UpperHalfPlane} (D : Set UpperHalfPlane)
    (hDdef : D = {w : UpperHalfPlane | ∀ g ∈ Γ', dist w p ≤ dist w (g • p)})
    (hD : ∫⁻ z in ((↑) : UpperHalfPlane → ℂ) '' D, ENNReal.ofReal ((z.im ^ 2)⁻¹) < ∞) :
    {γ | γ ∈ Γ' ∧ γ • p ≠ p ∧ ∀ z : UpperHalfPlane, dist z p = dist z (γ⁻¹ • p) → z ∈ D}.Finite := by
  have hDm : ∀ x : UpperHalfPlane, x ∈ D ↔ ∀ g ∈ Γ', dist x p ≤ dist x (g • p) := by
    intro x
    simp only [hDdef, mem_setOf_eq]
  have hDcl : IsClosed D := by
    rw [hDdef]
    simp only [setOf_forall]
    exact isClosed_iInter fun k => isClosed_iInter fun _ =>
      isClosed_le (continuous_id.dist continuous_const) (continuous_id.dist continuous_const)
  have hp0 := p.im_pos
  -- the far points `q = γ⁻¹ p` of the full faces
  obtain ⟨Q, hQ⟩ : ∃ Q : Set UpperHalfPlane, Q = {q | q ≠ p ∧ (∃ γ ∈ Γ', γ⁻¹ • p = q) ∧
      ∀ z : UpperHalfPlane, dist z p = dist z q → z ∈ D} := ⟨_, rfl⟩
  have hfibq : ∀ q : UpperHalfPlane, {γ | γ ∈ Γ' ∧ γ⁻¹ • p = q}.Finite := by
    intro q
    refine ((LiZhongQC.s82dx_finite_ball hΓ' p q 0).preimage inv_injective.injOn).subset ?_
    rintro γ ⟨hγ, hγq⟩
    exact ⟨Γ'.inv_mem hγ, le_of_eq (by rw [hγq, dist_self])⟩
  suffices hQf : Q.Finite by
    refine (hQf.biUnion fun q _ => hfibq q).subset ?_
    rintro γ ⟨hγ, hγp, hall⟩
    refine mem_biUnion (x := γ⁻¹ • p) ?_ ⟨hγ, rfl⟩
    rw [hQ]
    refine ⟨fun h => hγp ?_, ⟨γ, hγ, rfl⟩, hall⟩
    have h2 := congrArg (fun x => γ • x) h
    simp only [smul_inv_smul] at h2
    exact h2.symm
  -- chart data of every half-plane
  choose Bf hBf using fun x : UpperHalfPlane => s13c_pb_chart p x
  have hxne : ∀ x : UpperHalfPlane, x ≠ p → (p : ℂ) - x ≠ 0 := fun x hx h =>
    hx (UpperHalfPlane.ext (sub_eq_zero.mp h).symm)
  have hapos : ∀ x : UpperHalfPlane, x ≠ p → 0 < ‖(p : ℂ) - x‖ ^ 2 * p.im := fun x hx =>
    mul_pos (pow_pos (norm_pos_iff.mpr (hxne x hx)) 2) hp0
  obtain ⟨kf, hkf⟩ : ∃ kf : UpperHalfPlane → ℝ, kf = fun x => ‖Bf x‖ / (‖(p : ℂ) - x‖ ^ 2 * p.im) := ⟨_, rfl⟩
  have hk1 : ∀ x : UpperHalfPlane, x ≠ p → 1 < kf x := by
    intro x hx
    have ha := hapos x hx
    have h1 := (hBf x).1
    have h3 : 0 < 4 * p.im ^ 3 * x.im * ‖(p : ℂ) - x‖ ^ 2 :=
      mul_pos (mul_pos (mul_pos four_pos (pow_pos hp0 3)) x.im_pos) (pow_pos (norm_pos_iff.mpr (hxne x hx)) 2)
    have h2 : (‖(p : ℂ) - x‖ ^ 2 * p.im) ^ 2 < ‖Bf x‖ ^ 2 := by linarith
    rw [hkf]
    simp only
    rw [lt_div_iff₀ ha, one_mul]
    exact lt_of_pow_lt_pow_left₀ 2 (norm_nonneg _) h2
  have hang : ∀ x : UpperHalfPlane, ∃ t1 : ℝ, x ≠ p → (0 < t1 ∧ t1 < π / 2 ∧ 1 < kf x * Real.cos t1 ∧
      ∫⁻ t in Ioo (-t1) t1, ENNReal.ofReal (kf x * Real.cos t / √((kf x * Real.cos t) ^ 2 - 1) - 1) =
        ENNReal.ofReal (π - 1 - 2 * t1)) := by
    intro x
    by_cases hx : x = p
    · exact ⟨0, fun h => absurd hx h⟩
    · obtain ⟨t1, h⟩ := s13c_pb_ang (hk1 x hx)
      exact ⟨t1, fun _ => h⟩
  choose t1f ht1f using hang
  obtain ⟨cf, hcf⟩ : ∃ cf : UpperHalfPlane → ℝ, cf = fun x => Complex.arg (Bf x) - π := ⟨_, rfl⟩
  obtain ⟨If, hIf⟩ : ∃ If : UpperHalfPlane → Set ℝ,
      If = fun x => {θ : ℝ | Real.cos (t1f x) < Real.cos (θ + cf x)} := ⟨_, rfl⟩
  obtain ⟨gf, hgf⟩ : ∃ gf : UpperHalfPlane → ℝ → ℝ≥0∞, gf = fun x θ => (If x).indicator
      (fun θ => ENNReal.ofReal (kf x * Real.cos (θ + cf x) / √((kf x * Real.cos (θ + cf x)) ^ 2 - 1) - 1)) θ :=
    ⟨_, rfl⟩
  obtain ⟨J, hJ⟩ : ∃ J : ℝ → ℝ≥0∞, J = fun θ : ℝ => ∫⁻ s in Ioo (0 : ℝ) 1,
      (((↑) : UpperHalfPlane → ℂ) '' D).indicator (fun _ => ENNReal.ofReal (4 * s / (1 - s ^ 2) ^ 2))
        (((p : ℂ) - conj (p : ℂ) * ((s : ℂ) * Complex.exp ((θ : ℂ) * I))) /
          (1 - (s : ℂ) * Complex.exp ((θ : ℂ) * I))) := ⟨_, rfl⟩
  -- the chart coefficient along direction `θ`
  have hK1 : ∀ x : UpperHalfPlane, x ≠ p → ∀ θ : ℝ, (Bf x * Complex.exp ((θ : ℂ) * I)).re =
      -(‖(p : ℂ) - x‖ ^ 2 * p.im) * (kf x * Real.cos (θ + cf x)) := by
    intro x hx θ
    have ha := hapos x hx
    have h1 : (Bf x * Complex.exp ((θ : ℂ) * I)).re = ‖Bf x‖ * Real.cos (θ + Complex.arg (Bf x)) := by
      rw [Real.cos_add]
      simp only [Complex.mul_re, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
      rw [← Complex.norm_mul_cos_arg (Bf x), ← Complex.norm_mul_sin_arg (Bf x)]
      ring
    have h2 : ‖Bf x‖ / (‖(p : ℂ) - x‖ ^ 2 * p.im) * (‖(p : ℂ) - x‖ ^ 2 * p.im) = ‖Bf x‖ :=
      div_mul_cancel₀ _ ha.ne'
    rw [h1, hkf, hcf]
    simp only
    rw [show θ + (Complex.arg (Bf x) - π) = θ + Complex.arg (Bf x) - π by ring, Real.cos_sub_pi]
    linear_combination (-Real.cos (θ + Complex.arg (Bf x))) * h2
  -- along a direction of `If x` the ray meets the full face at radius `S < 1`, and stays in `D` before it
  have hexit : ∀ x ∈ Q, ∀ θ ∈ If x, ∃ ρ S : ℝ, ρ = kf x * Real.cos (θ + cf x) ∧ 1 < ρ ∧ 0 < S ∧ S < 1 ∧
      S ^ 2 - 2 * ρ * S + 1 = 0 ∧ 2 * S ^ 2 / (1 - S ^ 2) = ρ / √(ρ ^ 2 - 1) - 1 ∧
      ((p : ℂ) - conj (p : ℂ) * ((S : ℂ) * Complex.exp ((θ : ℂ) * I))) /
          (1 - (S : ℂ) * Complex.exp ((θ : ℂ) * I)) ∈ ((↑) : UpperHalfPlane → ℂ) '' D ∧
      ∀ s ∈ Ioo (0 : ℝ) S, ((p : ℂ) - conj (p : ℂ) * ((s : ℂ) * Complex.exp ((θ : ℂ) * I))) /
          (1 - (s : ℂ) * Complex.exp ((θ : ℂ) * I)) ∈ ((↑) : UpperHalfPlane → ℂ) '' D := by
    intro x hx θ hθ
    rw [hQ] at hx
    obtain ⟨hxp, -, hfull⟩ := hx
    have ha := hapos x hxp
    obtain ⟨-, -, hkc, -⟩ := ht1f x hxp
    have hkpos : 0 < kf x := by linarith [hk1 x hxp]
    obtain ⟨ρ, hρ⟩ : ∃ ρ : ℝ, ρ = kf x * Real.cos (θ + cf x) := ⟨_, rfl⟩
    have hθ' : Real.cos (t1f x) < Real.cos (θ + cf x) := by
      simp only [hIf, mem_setOf_eq] at hθ
      exact hθ
    have hρ1 : 1 < ρ := by
      rw [hρ]
      calc 1 < kf x * Real.cos (t1f x) := hkc
        _ ≤ kf x * Real.cos (θ + cf x) := mul_le_mul_of_nonneg_left hθ'.le hkpos.le
    obtain ⟨S, hS⟩ : ∃ S : ℝ, S = ρ - √(ρ ^ 2 - 1) := ⟨_, rfl⟩
    obtain ⟨hS0, hS1, hSeq, hSval⟩ := s13c_pb_root hρ1
    rw [← hS] at hS0 hS1 hSeq hSval
    have hface : (⟨_, s13c_cy_rim p θ S hS0.le hS1⟩ : UpperHalfPlane) ∈ D := by
      apply hfull
      have hc := (hBf x).2.2 θ S hS0.le hS1
      have hval : ‖(p : ℂ) - x‖ ^ 2 * p.im * (1 + S ^ 2) + 2 * S * (Bf x * Complex.exp ((θ : ℂ) * I)).re = 0 := by
        rw [hK1 x hxp θ, ← hρ]
        linear_combination (‖(p : ℂ) - x‖ ^ 2 * p.im) * hSeq
      exact le_antisymm (hc.1.mpr hval.ge) (hc.2.mpr hval.le)
    refine ⟨ρ, S, hρ, hρ1, hS0, hS1, hSeq, hSval, (s13c_cy_memiff p θ S hS0.le hS1 D).mpr hface, ?_⟩
    intro s hs
    rw [s13c_cy_memiff p θ s hs.1.le (hs.2.trans hS1) D, hDm]
    intro g hg
    by_cases hgp : g • p = p
    · rw [hgp]
    · have hcS := (hBf (g • p)).2.2 θ S hS0.le hS1
      have hcs := (hBf (g • p)).2.2 θ s hs.1.le (hs.2.trans hS1)
      have h0 := hcS.1.mp ((hDm _).mp hface g hg)
      exact hcs.1.mpr (s13c_pb_seg (hapos _ hgp) hs.1 hs.2.le hS1.le h0)
  -- (K2) the inner radial integral dominates the face term
  have hK2 : ∀ x ∈ Q, ∀ θ ∈ If x, gf x θ ≤ J θ := by
    intro x hx θ hθ
    obtain ⟨ρ, S, hρ, hρ1, hS0, hS1, -, hSval, -, hseg⟩ := hexit x hx θ hθ
    have hval : gf x θ = ENNReal.ofReal (2 * S ^ 2 / (1 - S ^ 2)) := by
      rw [hgf]
      simp only
      rw [Set.indicator_of_mem hθ, hSval, hρ]
    rw [hval, ← s13c_pb_radial hS0.le hS1, hJ]
    simp only
    calc ∫⁻ s in Ioo (0 : ℝ) S, ENNReal.ofReal (4 * s / (1 - s ^ 2) ^ 2) =
        ∫⁻ s in Ioo (0 : ℝ) S, (((↑) : UpperHalfPlane → ℂ) '' D).indicator
          (fun _ => ENNReal.ofReal (4 * s / (1 - s ^ 2) ^ 2))
            (((p : ℂ) - conj (p : ℂ) * ((s : ℂ) * Complex.exp ((θ : ℂ) * I))) /
              (1 - (s : ℂ) * Complex.exp ((θ : ℂ) * I))) :=
          setLIntegral_congr_fun measurableSet_Ioo fun s hs =>
            (Set.indicator_of_mem (hseg s hs) (fun _ => ENNReal.ofReal (4 * s / (1 - s ^ 2) ^ 2))).symm
      _ ≤ _ := lintegral_mono_set (Ioo_subset_Ioo_right hS1.le)
  -- (K3) two distinct full faces share only a null set of directions
  have hK3 : ∀ x ∈ Q, ∀ x' ∈ Q, x ≠ x' → volume (If x ∩ If x') = 0 := by
    intro x hx x' hx' hne
    have hxQ := hx
    have hx'Q := hx'
    rw [hQ] at hx hx'
    obtain ⟨hxp, ⟨γ, hγ, hγx⟩, -⟩ := hx
    obtain ⟨hxp', ⟨γ', hγ', hγx'⟩, -⟩ := hx'
    have ha := hapos x hxp
    have ha' := hapos x' hxp'
    obtain ⟨C, hC⟩ : ∃ C : ℂ, C = Bf x / ((‖(p : ℂ) - x‖ ^ 2 * p.im : ℝ) : ℂ) -
        Bf x' / ((‖(p : ℂ) - x'‖ ^ 2 * p.im : ℝ) : ℂ) := ⟨_, rfl⟩
    have hC0 : C ≠ 0 := by
      intro hC0
      rw [hC, sub_eq_zero] at hC0
      have e1 := (hBf x).2.1
      have e2 := (hBf x').2.1
      have ha0 : ((‖(p : ℂ) - x‖ ^ 2 * p.im : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ha.ne'
      have ha0' : ((‖(p : ℂ) - x'‖ ^ 2 * p.im : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ha'.ne'
      have f1 : Bf x / ((‖(p : ℂ) - x‖ ^ 2 * p.im : ℝ) : ℂ) * ((x : ℂ) - p) = -((x : ℂ) - conj (p : ℂ)) := by
        rw [div_mul_eq_mul_div, e1, neg_mul, neg_div, mul_div_cancel_left₀ _ ha0]
      have f2 : Bf x' / ((‖(p : ℂ) - x'‖ ^ 2 * p.im : ℝ) : ℂ) * ((x' : ℂ) - p) = -((x' : ℂ) - conj (p : ℂ)) := by
        rw [div_mul_eq_mul_div, e2, neg_mul, neg_div, mul_div_cancel_left₀ _ ha0']
      rw [← hC0] at f2
      have f3 : (Bf x / ((‖(p : ℂ) - x‖ ^ 2 * p.im : ℝ) : ℂ) + 1) * ((x : ℂ) - x') = 0 := by
        linear_combination f1 - f2
      rcases mul_eq_zero.mp f3 with h | h
      · have f4 : (p : ℂ) - conj (p : ℂ) = 0 := by linear_combination f1 - (h * ((x : ℂ) - p))
        have f5 := congrArg Complex.im f4
        simp only [Complex.sub_im, Complex.conj_im, Complex.zero_im, UpperHalfPlane.coe_im] at f5
        linarith
      · exact hne (UpperHalfPlane.ext (sub_eq_zero.mp h))
    refine measure_mono_null ?_ (s13c_cy_zero C hC0)
    rintro θ ⟨hθ, hθ'⟩
    obtain ⟨ρ, S, hρ, hρ1, hS0, hS1, hSeq, -, hSD, -⟩ := hexit x hxQ θ hθ
    obtain ⟨ρ', S', hρ', hρ1', hS0', hS1', hSeq', -, hSD', -⟩ := hexit x' hx'Q θ hθ'
    -- the exit point of each face satisfies the other's half-plane
    have hbound : ∀ (y : UpperHalfPlane) (g : Matrix.SpecialLinearGroup (Fin 2) ℝ), g ∈ Γ' → g • p = y → y ≠ p →
        ∀ (T : ℝ) (hT0 : 0 < T) (hT1 : T < 1), ((p : ℂ) - conj (p : ℂ) * ((T : ℂ) * Complex.exp ((θ : ℂ) * I))) /
          (1 - (T : ℂ) * Complex.exp ((θ : ℂ) * I)) ∈ ((↑) : UpperHalfPlane → ℂ) '' D →
          0 ≤ 1 + T ^ 2 - 2 * T * (kf y * Real.cos (θ + cf y)) := by
      intro y g hg hgy hyp T hT0 hT1 hTD
      have hmem := (s13c_cy_memiff p θ T hT0.le hT1 D).mp hTD
      have h1 := ((hBf y).2.2 θ T hT0.le hT1).1.mp (by rw [← hgy]; exact (hDm _).mp hmem g hg)
      rw [hK1 y hyp θ] at h1
      have hay := hapos y hyp
      have h2 : 0 ≤ (‖(p : ℂ) - y‖ ^ 2 * p.im) * (1 + T ^ 2 - 2 * T * (kf y * Real.cos (θ + cf y))) := by
        linarith
      exact (mul_nonneg_iff_of_pos_left hay).mp h2
    have hb1 := hbound x' γ'⁻¹ (Γ'.inv_mem hγ') hγx' hxp' S hS0 hS1 hSD
    have hb2 := hbound x γ⁻¹ (Γ'.inv_mem hγ) hγx hxp S' hS0' hS1' hSD'
    rw [← hρ'] at hb1
    rw [← hρ] at hb2
    -- hence `S = S'`
    have hle : ∀ (A B r : ℝ), 0 < A → A < 1 → 0 < B → B < 1 → B ^ 2 - 2 * r * B + 1 = 0 →
        0 ≤ 1 + A ^ 2 - 2 * A * r → A ≤ B := by
      intro A B r hA0 hA1 hB0 hB1 hBeq hA
      by_contra hlt
      push_neg at hlt
      have h1 : B * (2 * r - B) = 1 := by linear_combination -hBeq
      have h2 : 1 < 2 * r - B := by
        by_contra h
        push_neg at h
        nlinarith [mul_le_mul_of_nonneg_left h hB0.le]
      nlinarith [mul_pos (sub_pos.mpr hlt) (sub_pos.mpr (show A < 2 * r - B by linarith))]
    have hSS : S = S' := le_antisymm (hle S S' ρ' hS0 hS1 hS0' hS1' hSeq' hb1)
      (hle S' S ρ hS0' hS1' hS0 hS1 hSeq hb2)
    have hρρ : ρ = ρ' := by
      have h1 : 2 * ρ * S = S ^ 2 + 1 := by linear_combination -hSeq
      have h2 : 2 * ρ' * S = S ^ 2 + 1 := by rw [hSS]; linear_combination -hSeq'
      have h3 : (ρ - ρ') * (2 * S) = 0 := by linear_combination h1 - h2
      exact sub_eq_zero.mp ((mul_eq_zero.mp h3).resolve_right (by linarith))
    show (C * Complex.exp ((θ : ℂ) * I)).re = 0
    have hre : ∀ (y : UpperHalfPlane), y ≠ p → (Bf y / ((‖(p : ℂ) - y‖ ^ 2 * p.im : ℝ) : ℂ) *
        Complex.exp ((θ : ℂ) * I)).re = -(kf y * Real.cos (θ + cf y)) := by
      intro y hyp
      rw [div_mul_eq_mul_div, Complex.div_ofReal_re, hK1 y hyp θ, neg_mul, neg_div,
        mul_div_cancel_left₀ _ (hapos y hyp).ne']
    rw [hC, sub_mul, Complex.sub_re, hre x hxp, hre x' hxp', ← hρ, ← hρ', hρρ, sub_self]
  -- (K4) the angular integrals, after centring each face's window
  have hcosmeas : ∀ t1 : ℝ, MeasurableSet {t : ℝ | Real.cos t1 < Real.cos t} := fun t1 =>
    (isOpen_lt continuous_const Real.continuous_cos).measurableSet
  have hK4 : ∀ x ∈ Q, ∫⁻ θ in Ioc (-π) π, gf x θ = ENNReal.ofReal (π - 1 - 2 * t1f x) := by
    intro x hx
    have hxp : x ≠ p := by
      rw [hQ] at hx
      exact hx.1
    obtain ⟨ht0, ht1, -, hint⟩ := ht1f x hxp
    obtain ⟨G, hG⟩ : ∃ G : ℝ → ℝ≥0∞, G = {t : ℝ | Real.cos (t1f x) < Real.cos t}.indicator
        (fun t => ENNReal.ofReal (kf x * Real.cos t / √((kf x * Real.cos t) ^ 2 - 1) - 1)) := ⟨_, rfl⟩
    have hshift : ∀ θ, gf x θ = G (θ + cf x) := by
      intro θ
      rw [hgf, hG, hIf]
      rfl
    have hper : ∀ θ, G (θ + 2 * π) = G θ := by
      intro θ
      rw [hG]
      simp only [Set.indicator, mem_setOf_eq, Real.cos_add_two_pi]
    simp_rw [hshift]
    rw [s13c_pb_lshift G hper (cf x), hG, setLIntegral_indicator (hcosmeas _), Set.inter_comm]
    rw [show Ioc (-π) π ∩ {t : ℝ | Real.cos (t1f x) < Real.cos t} =
        {t : ℝ | t ∈ Ioc (-π) π ∧ Real.cos (t1f x) < Real.cos t} from rfl, s13c_pb_cosset ht0 ht1, hint]
  have hK4' : ∀ x ∈ Q, volume (Ioc (-π) π ∩ If x) = ENNReal.ofReal (2 * t1f x) := by
    intro x hx
    have hxp : x ≠ p := by
      rw [hQ] at hx
      exact hx.1
    obtain ⟨ht0, ht1, -, -⟩ := ht1f x hxp
    have hIm : MeasurableSet (If x) := by
      rw [hIf]
      exact (isOpen_lt continuous_const (by fun_prop)).measurableSet
    obtain ⟨G, hG⟩ : ∃ G : ℝ → ℝ≥0∞, G = {t : ℝ | Real.cos (t1f x) < Real.cos t}.indicator 1 := ⟨_, rfl⟩
    have hper : ∀ θ, G (θ + 2 * π) = G θ := by
      intro θ
      rw [hG]
      simp only [Set.indicator, mem_setOf_eq, Real.cos_add_two_pi, Pi.one_apply]
    have h0 : ∫⁻ θ in Ioc (-π) π, (If x).indicator 1 θ = volume (Ioc (-π) π ∩ If x) := by
      rw [lintegral_indicator_one hIm, Measure.restrict_apply hIm, Set.inter_comm]
    have h1' : ∀ θ, (If x).indicator 1 θ = G (θ + cf x) := fun θ => by
      rw [hG, hIf]
      rfl
    rw [← h0]
    simp_rw [h1']
    rw [s13c_pb_lshift G hper (cf x), hG, setLIntegral_indicator (hcosmeas _), Set.inter_comm,
      show Ioc (-π) π ∩ {t : ℝ | Real.cos (t1f x) < Real.cos t} =
        {t : ℝ | t ∈ Ioc (-π) π ∧ Real.cos (t1f x) < Real.cos t} from rfl, s13c_pb_cosset ht0 ht1]
    simp only [Pi.one_apply, lintegral_const, Measure.restrict_apply MeasurableSet.univ, univ_inter,
      Real.volume_Ioo, one_mul]
    congr 1
    ring
  -- (K5)-(K8) every finite set of full faces has at most `(area + 2π)/(π - 1)` elements
  have hcount : ∀ T : Finset UpperHalfPlane, (T : Set UpperHalfPlane) ⊆ Q →
      (T.card : ℝ≥0∞) * ENNReal.ofReal (π - 1) ≤
        (∫⁻ z in ((↑) : UpperHalfPlane → ℂ) '' D, ENNReal.ofReal ((z.im ^ 2)⁻¹)) + ENNReal.ofReal (2 * π) := by
    intro T hTQ
    have hgm : ∀ x ∈ T, Measurable (gf x) := by
      intro x _
      rw [hgf]
      simp only
      refine Measurable.indicator ?_ ?_
      · exact (by fun_prop : Measurable fun θ : ℝ =>
          kf x * Real.cos (θ + cf x) / √((kf x * Real.cos (θ + cf x)) ^ 2 - 1) - 1).ennreal_ofReal
      · rw [hIf]
        exact (isOpen_lt continuous_const (by fun_prop)).measurableSet
    -- a.e. at most one face is visible
    obtain ⟨N, hN⟩ : ∃ N : Set ℝ, N = ⋃ x ∈ (T : Set UpperHalfPlane), ⋃ x' ∈ ((T.erase x : Finset _) : Set UpperHalfPlane),
        If x ∩ If x' := ⟨_, rfl⟩
    have hN0 : volume N = 0 := by
      rw [hN, measure_biUnion_null_iff T.countable_toSet]
      intro x hx
      rw [measure_biUnion_null_iff (T.erase x).countable_toSet]
      intro x' hx'
      exact hK3 x (hTQ hx) x' (hTQ (Finset.mem_of_mem_erase hx')) (Finset.ne_of_mem_erase hx').symm
    have hae : ∀ᵐ θ ∂(volume.restrict (Ioc (-π) π)), ∑ x ∈ T, gf x θ ≤ J θ := by
      refine ae_restrict_of_ae ?_
      filter_upwards [measure_eq_zero_iff_ae_notMem.mp hN0] with θ hθN
      by_cases hex : ∃ x ∈ T, θ ∈ If x
      · obtain ⟨x0, hx0T, hθx0⟩ := hex
        rw [Finset.sum_eq_single x0 (fun x hxT hxne => ?_) (fun h => absurd hx0T h)]
        · exact hK2 x0 (hTQ hx0T) θ hθx0
        · have hθx : θ ∉ If x := by
            intro hθx
            apply hθN
            rw [hN]
            exact mem_biUnion hx0T (mem_biUnion (Finset.mem_erase.mpr ⟨hxne, hxT⟩) ⟨hθx0, hθx⟩)
          rw [hgf]
          simp only
          exact Set.indicator_of_notMem hθx _
      · push_neg at hex
        rw [Finset.sum_eq_zero fun x hx => by rw [hgf]; simp only; exact Set.indicator_of_notMem (hex x hx) _]
        exact zero_le
    have hA : ∫⁻ z in ((↑) : UpperHalfPlane → ℂ) '' D, ENNReal.ofReal ((z.im ^ 2)⁻¹) =
        ∫⁻ θ in Ioc (-π) π, J θ := by
      rw [s13c_pc_area p hDcl.measurableSet, hJ]
    have hsumg : ∑ x ∈ T, ENNReal.ofReal (π - 1 - 2 * t1f x) ≤
        ∫⁻ z in ((↑) : UpperHalfPlane → ℂ) '' D, ENNReal.ofReal ((z.im ^ 2)⁻¹) := by
      rw [hA, ← Finset.sum_congr rfl fun x hx => hK4 x (hTQ hx), ← lintegral_finset_sum T hgm]
      exact lintegral_mono_ae hae
    have hsumI : ∑ x ∈ T, ENNReal.ofReal (2 * t1f x) ≤ ENNReal.ofReal (2 * π) := by
      rw [← Finset.sum_congr rfl fun x hx => hK4' x (hTQ hx)]
      have hd : Set.Pairwise (T : Set UpperHalfPlane)
          (Function.onFun (AEDisjoint volume) fun x => Ioc (-π) π ∩ If x) := by
        intro x hx x' hx' hne
        exact measure_mono_null (Set.inter_subset_inter Set.inter_subset_right Set.inter_subset_right)
          (hK3 x (hTQ hx) x' (hTQ hx') hne)
      have hm : ∀ x ∈ T, NullMeasurableSet (Ioc (-π) π ∩ If x) volume := by
        intro x _
        rw [hIf]
        exact (measurableSet_Ioc.inter (isOpen_lt continuous_const (by fun_prop)).measurableSet).nullMeasurableSet
      rw [← measure_biUnion_finset₀ hd hm]
      calc volume (⋃ x ∈ T, Ioc (-π) π ∩ If x) ≤ volume (Ioc (-π) π) :=
            measure_mono (iUnion₂_subset fun x _ => Set.inter_subset_left)
        _ = ENNReal.ofReal (2 * π) := by
            rw [Real.volume_Ioc]
            congr 1
            ring
    calc (T.card : ℝ≥0∞) * ENNReal.ofReal (π - 1) = ∑ x ∈ T, ENNReal.ofReal (π - 1) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ x ∈ T, (ENNReal.ofReal (π - 1 - 2 * t1f x) + ENNReal.ofReal (2 * t1f x)) := by
          refine Finset.sum_le_sum fun x _ => ?_
          have h : ENNReal.ofReal ((π - 1 - 2 * t1f x) + 2 * t1f x) ≤
              ENNReal.ofReal (π - 1 - 2 * t1f x) + ENNReal.ofReal (2 * t1f x) := ENNReal.ofReal_add_le
          rwa [sub_add_cancel] at h
      _ = ∑ x ∈ T, ENNReal.ofReal (π - 1 - 2 * t1f x) + ∑ x ∈ T, ENNReal.ofReal (2 * t1f x) :=
          Finset.sum_add_distrib
      _ ≤ _ := add_le_add hsumg hsumI
  -- conclusion
  by_contra hinf
  have hπ1 : ENNReal.ofReal (π - 1) ≠ 0 := by
    rw [Ne, ENNReal.ofReal_eq_zero, not_le]
    linarith [Real.pi_gt_three]
  have hnum : (∫⁻ z in ((↑) : UpperHalfPlane → ℂ) '' D, ENNReal.ofReal ((z.im ^ 2)⁻¹)) +
      ENNReal.ofReal (2 * π) ≠ ∞ := ENNReal.add_ne_top.mpr ⟨hD.ne, ENNReal.ofReal_ne_top⟩
  obtain ⟨n, hn⟩ := ENNReal.exists_nat_gt (ENNReal.div_ne_top hnum hπ1)
  have hn' := (ENNReal.div_lt_iff (Or.inl hπ1) (Or.inl ENNReal.ofReal_ne_top)).mp hn
  obtain ⟨T, hT, hTn⟩ := (Set.Infinite.exists_subset_card_eq hinf n)
  have h := hcount T hT
  rw [hTn] at h
  exact absurd h (not_le.mpr hn')

/-- **(B2.4.v) Counting.** A Dirichlet domain of finite area has finitely many vertices: every cycle contributes at
least `π/3` to `Σ (π - ang)` (B2.4.iii), which is bounded by `area + 3π` (B2.4.iv-a). -/
theorem s13c_sc_vfin {Γ' : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} (hΓ' : LiZhongQC.IsFuchsian Γ')
    {p : UpperHalfPlane} (hp : ∀ γ ∈ Γ', γ • p = p → γ = 1 ∨ γ = -1) (D V : Set UpperHalfPlane)
    (hDdef : D = {w : UpperHalfPlane | ∀ g ∈ Γ', dist w p ≤ dist w (g • p)})
    (hV : V = {v : UpperHalfPlane | v ∈ D ∧ ∃ g ∈ Γ', ∃ h ∈ Γ', g • p ≠ p ∧ h • p ≠ p ∧ g • p ≠ h • p ∧
      dist v p = dist v (g • p) ∧ dist v p = dist v (h • p)})
    (ang : UpperHalfPlane → ℝ≥0∞)
    (hang : ∀ v : UpperHalfPlane, ang v = volume {θ : ℝ | θ ∈ Ioc (-π) π ∧ ∀ᶠ s : ℝ in 𝓝[>] (0 : ℝ),
      ((v : ℂ) - conj (v : ℂ) * ((s : ℂ) * Complex.exp ((θ : ℂ) * I))) / (1 - (s : ℂ) * Complex.exp ((θ : ℂ) * I)) ∈
        ((↑) : UpperHalfPlane → ℂ) '' D})
    (hD : ∫⁻ z in ((↑) : UpperHalfPlane → ℂ) '' D, ENNReal.ofReal ((z.im ^ 2)⁻¹) < ∞) : V.Finite := by
  set A := ∫⁻ z in ((↑) : UpperHalfPlane → ℂ) '' D, ENNReal.ofReal ((z.im ^ 2)⁻¹) with hA
  have hcl := fun v (hv : v ∈ V) => s13c_sc_cycle hΓ' hp D V hDdef hV ang hang hv
  -- the cycles (orbit classes) of vertices
  obtain ⟨cls, hcls⟩ : ∃ cls : UpperHalfPlane → Set UpperHalfPlane,
      cls = fun v => {u : UpperHalfPlane | u ∈ V ∧ ∃ g ∈ Γ', g • v = u} := ⟨_, rfl⟩
  have hself : ∀ v ∈ V, v ∈ cls v := fun v hv => by
    rw [hcls]
    exact ⟨hv, 1, Γ'.one_mem, one_smul _ _⟩
  have hsubV : ∀ v, cls v ⊆ V := fun v u hu => by
    rw [hcls] at hu
    exact hu.1
  have hmeet : ∀ v w x, x ∈ cls v → x ∈ cls w → cls v = cls w := by
    intro v w x hxv hxw
    rw [hcls] at hxv hxw ⊢
    obtain ⟨_, g, hg, hgx⟩ := hxv
    obtain ⟨_, h, hh, hhx⟩ := hxw
    have hw : w = (h⁻¹ * g) • v := by
      rw [mul_smul, hgx, ← hhx, inv_smul_smul]
    have hv' : v = (g⁻¹ * h) • w := by
      rw [mul_smul, hhx, ← hgx, inv_smul_smul]
    ext y
    simp only [mem_setOf_eq]
    constructor
    · rintro ⟨hy, k, hk, hky⟩
      refine ⟨hy, k * (g⁻¹ * h), Γ'.mul_mem hk (Γ'.mul_mem (Γ'.inv_mem hg) hh), ?_⟩
      rw [mul_smul, ← hv', hky]
    · rintro ⟨hy, k, hk, hky⟩
      refine ⟨hy, k * (h⁻¹ * g), Γ'.mul_mem hk (Γ'.mul_mem (Γ'.inv_mem hh) hg), ?_⟩
      rw [mul_smul, ← hw, hky]
  have hCf : ∀ C ∈ cls '' V, C.Finite := by
    rintro C ⟨v, hv, rfl⟩
    have h := (hcl v hv).1
    rw [hcls]
    exact h
  have hangf : ∀ u, ang u ≠ ∞ := by
    intro u
    rw [hang u]
    exact ne_top_of_le_ne_top (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)
      (measure_mono fun θ hθ => hθ.1)
  by_contra hinf
  have hC : (cls '' V).Infinite := by
    intro hfin
    apply hinf
    exact (hfin.biUnion hCf).subset fun v hv => mem_biUnion ⟨v, hv, rfl⟩ (hself v hv)
  -- enough cycles to exceed `area + 3π`
  have hπ3 : ENNReal.ofReal (π / 3) ≠ 0 := by
    rw [Ne, ENNReal.ofReal_eq_zero, not_le]
    positivity
  have hnum : A + ENNReal.ofReal (3 * π) ≠ ∞ := ENNReal.add_ne_top.mpr ⟨hD.ne, ENNReal.ofReal_ne_top⟩
  obtain ⟨n, hn⟩ := ENNReal.exists_nat_gt (ENNReal.div_ne_top hnum hπ3)
  have hn' : A + ENNReal.ofReal (3 * π) < (n : ℝ≥0∞) * ENNReal.ofReal (π / 3) :=
    (ENNReal.div_lt_iff (Or.inl hπ3) (Or.inl ENNReal.ofReal_ne_top)).mp hn
  obtain ⟨T, hT, hTn⟩ := hC.exists_subset_card_eq n
  obtain ⟨F, hF⟩ : ∃ F : Set UpperHalfPlane → Finset UpperHalfPlane,
      F = fun C => if h : C.Finite then h.toFinset else ∅ := ⟨_, rfl⟩
  have hFC : ∀ C ∈ T, (F C : Set UpperHalfPlane) = C := by
    intro C hC
    rw [hF]
    simp only [dif_pos (hCf C (hT hC)), Set.Finite.coe_toFinset]
  have hTcls : ∀ C ∈ T, ∃ v ∈ V, C = cls v := by
    intro C hC
    obtain ⟨v, hv, hvC⟩ := hT hC
    exact ⟨v, hv, hvC.symm⟩
  have hdisj : (T : Set (Set UpperHalfPlane)).PairwiseDisjoint F := by
    intro C hC C' hC' hne
    show Disjoint (F C) (F C')
    rw [← Finset.disjoint_coe, hFC C hC, hFC C' hC', Set.disjoint_left]
    intro x hx hx'
    obtain ⟨v, hv, rfl⟩ := hTcls C hC
    obtain ⟨w, hw, rfl⟩ := hTcls C' hC'
    exact hne (hmeet v w x hx hx')
  have hSV : ((T.biUnion F : Finset UpperHalfPlane) : Set UpperHalfPlane) ⊆ V := by
    intro x hx
    obtain ⟨C, hC, hxC⟩ := Finset.mem_biUnion.mp hx
    have hxC' : x ∈ (F C : Set UpperHalfPlane) := hxC
    rw [hFC C hC] at hxC'
    obtain ⟨v, hv, rfl⟩ := hTcls C hC
    exact hsubV v hxC'
  -- sum the cycle bounds (B2.4.iii) and compare with Gauss–Bonnet (B2.4.iv-a)
  have hsumcyc : ∀ C ∈ T, ENNReal.ofReal (π / 3) + ∑ u ∈ F C, ang u ≤
      ((F C).card : ℝ≥0∞) * ENNReal.ofReal π := by
    intro C hC
    obtain ⟨v, hv, hCv⟩ := hTcls C hC
    apply (hcl v hv).2
    rw [hFC C hC, hCv, hcls]
  have h1 := Finset.sum_le_sum hsumcyc
  rw [Finset.sum_add_distrib, Finset.sum_const, hTn, nsmul_eq_mul, ← Finset.sum_mul, ← Nat.cast_sum,
    ← Finset.card_biUnion hdisj, ← Finset.sum_biUnion hdisj] at h1
  have h2 : ((T.biUnion F).card : ℝ≥0∞) * ENNReal.ofReal π ≤
      ∑ u ∈ T.biUnion F, ang u + A + ENNReal.ofReal (3 * π) :=
    s13c_sc_gb hΓ' D V hDdef hV ang hang (T.biUnion F) hSV
  have h3 : ∑ u ∈ T.biUnion F, ang u + (n : ℝ≥0∞) * ENNReal.ofReal (π / 3) ≤
      ∑ u ∈ T.biUnion F, ang u + (A + ENNReal.ofReal (3 * π)) := by
    rw [add_comm, ← add_assoc]
    exact h1.trans h2
  have h4 := (ENNReal.add_le_add_iff_left (ENNReal.sum_ne_top.mpr fun u _ => hangf u)).mp h3
  exact absurd h4 (not_le.mpr hn')

/-- **(B2.4) Siegel's core.** A Dirichlet domain of finite area (around a point with trivial stabilizer modulo `±1`)
has only finitely many neighbours (convex polygon, vertex cycles, Gauss–Bonnet). -/
theorem s13c_sg_core {Γ' : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} (hΓ' : LiZhongQC.IsFuchsian Γ')
    {p : UpperHalfPlane} (hp : ∀ γ ∈ Γ', γ • p = p → γ = 1 ∨ γ = -1)
    (hD : ∫⁻ z in ((↑) : UpperHalfPlane → ℂ) '' {w : UpperHalfPlane | ∀ g ∈ Γ', dist w p ≤ dist w (g • p)},
      ENNReal.ofReal ((z.im ^ 2)⁻¹) < ∞) :
    {γ | γ ∈ Γ' ∧ ∃ w : UpperHalfPlane, (∀ g ∈ Γ', dist w p ≤ dist w (g • p)) ∧
      ∀ g ∈ Γ', dist (γ • w) p ≤ dist (γ • w) (g • p)}.Finite := by
  obtain ⟨D, hDdef⟩ : ∃ D : Set UpperHalfPlane, D = {w : UpperHalfPlane | ∀ g ∈ Γ', dist w p ≤ dist w (g • p)} :=
    ⟨_, rfl⟩
  obtain ⟨V, hV⟩ : ∃ V : Set UpperHalfPlane, V = {v : UpperHalfPlane | v ∈ D ∧ ∃ g ∈ Γ', ∃ h ∈ Γ', g • p ≠ p ∧
      h • p ≠ p ∧ g • p ≠ h • p ∧ dist v p = dist v (g • p) ∧ dist v p = dist v (h • p)} := ⟨_, rfl⟩
  obtain ⟨ang, hang⟩ : ∃ ang : UpperHalfPlane → ℝ≥0∞, ∀ v : UpperHalfPlane, ang v = volume {θ : ℝ |
      θ ∈ Ioc (-π) π ∧ ∀ᶠ s : ℝ in 𝓝[>] (0 : ℝ),
        ((v : ℂ) - conj (v : ℂ) * ((s : ℂ) * Complex.exp ((θ : ℂ) * I))) / (1 - (s : ℂ) * Complex.exp ((θ : ℂ) * I)) ∈
          ((↑) : UpperHalfPlane → ℂ) '' D} := ⟨_, fun _ => rfl⟩
  have hD' : ∫⁻ z in ((↑) : UpperHalfPlane → ℂ) '' D, ENNReal.ofReal ((z.im ^ 2)⁻¹) < ∞ := by
    rw [hDdef]
    exact hD
  have hVf := s13c_sc_vfin hΓ' hp D V hDdef hV ang hang hD'
  have hIf := s13c_sc_ideal hΓ' D hDdef hD'
  -- the elements whose bisector passes through a given point are finitely many
  have hloc : ∀ v : UpperHalfPlane, {γ | γ ∈ Γ' ∧ dist v p = dist v (γ⁻¹ • p)}.Finite := by
    intro v
    have hfin := LiZhongQC.s82dx_finite_ball hΓ' p v (dist v p)
    refine (hfin.preimage inv_injective.injOn).subset ?_
    rintro γ ⟨hγ, hγv⟩
    exact ⟨Γ'.inv_mem hγ, le_of_eq ((dist_comm _ _).trans hγv.symm)⟩
  refine ((((hVf.biUnion fun v _ => hloc v).union hIf).union
    ((Set.finite_singleton (1 : Matrix.SpecialLinearGroup (Fin 2) ℝ)).insert (-1))).subset ?_)
  rintro γ ⟨hγ, w, hw, hγw⟩
  by_cases hγp : γ • p = p
  · right
    rcases hp γ hγ hγp with h | h
    · simp [h]
    · simp [h]
  · have hwD : w ∈ D := by
      rw [hDdef]
      exact hw
    have hγwD : γ • w ∈ D := by
      rw [hDdef]
      exact hγw
    rcases s13c_sc_face hΓ' D V hDdef hV hγ hγp hwD hγwD with ⟨v, hv, hvγ⟩ | hall
    · left
      left
      exact mem_biUnion hv ⟨hγ, hvγ⟩
    · left
      right
      exact ⟨hγ, hγp, hall⟩

/-- **(B1a)** The Cayley conjugate of a Fuchsian group is a Li Zhong Fuchsian group in `SL(2, ℝ)`. -/
theorem s13c_transfer_group {Γ : Subgroup SL2C} (hΓ : IsFuchsian Γ) :
    ∃ Γ' : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ), LiZhongQC.IsFuchsian Γ' ∧
      (∀ M ∈ Γ', ∃ g ∈ Γ, ∀ τ : UpperHalfPlane, (τ : ℂ) ≠ I → ((M • τ : UpperHalfPlane) : ℂ) ≠ I →
        mob g (((τ : ℂ) + I) / ((τ : ℂ) - I)) = (((M • τ : UpperHalfPlane) : ℂ) + I) / (((M • τ : UpperHalfPlane) : ℂ) - I)) ∧
      ∀ g ∈ Γ, ∃ M ∈ Γ', ∀ τ : UpperHalfPlane, (τ : ℂ) ≠ I → ((M • τ : UpperHalfPlane) : ℂ) ≠ I →
        mob g (((τ : ℂ) + I) / ((τ : ℂ) - I)) = (((M • τ : UpperHalfPlane) : ℂ) + I) / (((M • τ : UpperHalfPlane) : ℂ) - I) := by
  set Kc : Matrix (Fin 2) (Fin 2) ℂ := !![1, I; 1, -I] with hKc
  let H : Subgroup SL2C :=
    { carrier := {h | ∃ g ∈ Γ, Kc * (h : Matrix (Fin 2) (Fin 2) ℂ) = (g : Matrix (Fin 2) (Fin 2) ℂ) * Kc}
      mul_mem' := by
        rintro h1 h2 ⟨g1, hg1, e1⟩ ⟨g2, hg2, e2⟩
        refine ⟨g1 * g2, Γ.mul_mem hg1 hg2, ?_⟩
        rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, ← Matrix.mul_assoc, e1,
          Matrix.mul_assoc, e2, Matrix.mul_assoc]
      one_mem' := ⟨1, Γ.one_mem, by simp⟩
      inv_mem' := by
        rintro h ⟨g, hg, e⟩
        refine ⟨g⁻¹, Γ.inv_mem hg, ?_⟩
        calc Kc * ((h⁻¹ : SL2C) : Matrix (Fin 2) (Fin 2) ℂ)
            = ((g⁻¹ : SL2C) : Matrix (Fin 2) (Fin 2) ℂ) * ((g : Matrix (Fin 2) (Fin 2) ℂ) * Kc) *
                ((h⁻¹ : SL2C) : Matrix (Fin 2) (Fin 2) ℂ) := by
              rw [← Matrix.mul_assoc, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
                Matrix.SpecialLinearGroup.coe_one, Matrix.one_mul]
          _ = ((g⁻¹ : SL2C) : Matrix (Fin 2) (Fin 2) ℂ) * (Kc * (h : Matrix (Fin 2) (Fin 2) ℂ)) *
                ((h⁻¹ : SL2C) : Matrix (Fin 2) (Fin 2) ℂ) := by rw [e]
          _ = ((g⁻¹ : SL2C) : Matrix (Fin 2) (Fin 2) ℂ) * Kc := by
              rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
                Matrix.SpecialLinearGroup.coe_one, Matrix.mul_one] }
  have hmem : ∀ M : Matrix.SpecialLinearGroup (Fin 2) ℝ,
      M ∈ H.comap (Matrix.SpecialLinearGroup.map Complex.ofRealHom) ↔
        ∃ g ∈ Γ, Kc * ((Matrix.SpecialLinearGroup.map Complex.ofRealHom M : SL2C) : Matrix (Fin 2) (Fin 2) ℂ) =
          (g : Matrix (Fin 2) (Fin 2) ℂ) * Kc := fun M => Iff.rfl
  -- the reverse direction: the Cayley conjugate of `g ∈ SU(1,1)` is real
  have hrev : ∀ g ∈ Γ, ∃ M : Matrix.SpecialLinearGroup (Fin 2) ℝ,
      Kc * ((Matrix.SpecialLinearGroup.map Complex.ofRealHom M : SL2C) : Matrix (Fin 2) (Fin 2) ℂ) =
        (g : Matrix (Fin 2) (Fin 2) ℂ) * Kc := by
    intro g hg
    have hsu := hΓ.1 g hg
    have hdet := fd_su11_det hsu
    set a := g 0 0
    set b := g 0 1
    have hdet' : (a.re + b.re) * (a.re - b.re) - (b.im - a.im) * (a.im + b.im) = 1 := by
      rw [← hdet, ← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply,
        Complex.normSq_apply]
      ring
    set M0 : Matrix.SpecialLinearGroup (Fin 2) ℝ :=
      ⟨!![a.re + b.re, b.im - a.im; a.im + b.im, a.re - b.re], by
        rw [Matrix.det_fin_two_of]; exact hdet'⟩ with hM0
    refine ⟨M0, ?_⟩
    have h10 : g 1 0 = conj b := hsu.1
    have h11 : g 1 1 = conj a := hsu.2
    have hcoe : ((Matrix.SpecialLinearGroup.map Complex.ofRealHom M0 : SL2C) : Matrix (Fin 2) (Fin 2) ℂ) =
        !![((a.re + b.re : ℝ) : ℂ), ((b.im - a.im : ℝ) : ℂ); ((a.im + b.im : ℝ) : ℂ), ((a.re - b.re : ℝ) : ℂ)] := by
      ext i j
      fin_cases i <;> fin_cases j <;> rfl
    rw [hcoe]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [hKc, Matrix.mul_apply, Fin.sum_univ_two, h10, h11, Complex.ext_iff]
    all_goals (try constructor)
    all_goals ring
  refine ⟨H.comap (Matrix.SpecialLinearGroup.map Complex.ofRealHom), ?_,
    fun M hM => ?_, fun g hg => ?_⟩
  · -- proper discontinuity on compacta
    intro C hC
    haveI : DiscreteTopology Γ := hΓ.2
    obtain ⟨L, hL⟩ := s13c_entry_bound hC
    have hT := fd_bounded_finite (Γ := Γ) (2 * L + 2 * L)
    have hfib : ∀ g : SL2C, ({M : Matrix.SpecialLinearGroup (Fin 2) ℝ | Kc *
        ((Matrix.SpecialLinearGroup.map Complex.ofRealHom M : SL2C) : Matrix (Fin 2) (Fin 2) ℂ) =
          (g : Matrix (Fin 2) (Fin 2) ℂ) * Kc}).Finite := by
      intro g
      refine Set.Subsingleton.finite ?_
      intro M1 h1 M2 h2
      exact s13c_cay_inj h1 h2
    refine (hT.biUnion fun g _ => hfib g).subset ?_
    rintro M ⟨hM, hne⟩
    obtain ⟨g, hg, e⟩ := (hmem M).mp hM
    obtain ⟨_, ⟨τ, hτ, rfl⟩, hMτ⟩ := hne
    exact Set.mem_biUnion (x := g) ⟨hg, fun i j => s13c_cay_bound e (hL M τ hτ hMτ) i j⟩ e
  · obtain ⟨g, hg, e⟩ := (hmem M).mp hM
    exact ⟨g, hg, fun τ h1 h2 => s13c_cay_rel e τ h2 h1⟩
  · obtain ⟨M, e⟩ := hrev g hg
    exact ⟨M, (hmem M).mpr ⟨g, hg, e⟩, fun τ h1 h2 => s13c_cay_rel e τ h2 h1⟩

/-- **(B1b)** The Cayley pull-back of the fundamental domain covers `ℍ` modulo `Γ'` and carries the hyperbolic
integrals. -/
theorem s13c_transfer_cover {Γ : Subgroup SL2C} (hΓ : IsCofinite Γ)
    {Γ' : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    (hrel : ∀ M ∈ Γ', ∃ g ∈ Γ, ∀ τ : UpperHalfPlane, (τ : ℂ) ≠ I → ((M • τ : UpperHalfPlane) : ℂ) ≠ I →
      mob g (((τ : ℂ) + I) / ((τ : ℂ) - I)) = (((M • τ : UpperHalfPlane) : ℂ) + I) / (((M • τ : UpperHalfPlane) : ℂ) - I))
    (hrel' : ∀ g ∈ Γ, ∃ M ∈ Γ', ∀ τ : UpperHalfPlane, (τ : ℂ) ≠ I → ((M • τ : UpperHalfPlane) : ℂ) ≠ I →
      mob g (((τ : ℂ) + I) / ((τ : ℂ) - I)) = (((M • τ : UpperHalfPlane) : ℂ) + I) / (((M • τ : UpperHalfPlane) : ℂ) - I)) :
    MeasurableSet {z : ℂ | 0 < z.im ∧ (z + I) / (z - I) ∈ fundDomain Γ} ∧
      {z : ℂ | 0 < z.im ∧ (z + I) / (z - I) ∈ fundDomain Γ} ⊆ upperHalf ∧
      (∀ᵐ z ∂(volume.restrict upperHalf), ∀ hz : 0 < z.im, ∃ M ∈ Γ',
        ((M • (⟨z, hz⟩ : UpperHalfPlane) : UpperHalfPlane) : ℂ) ∈
          {z : ℂ | 0 < z.im ∧ (z + I) / (z - I) ∈ fundDomain Γ}) ∧
      ∀ f : ℂ → ℝ≥0∞, Measurable f →
        ∫⁻ z in {z : ℂ | 0 < z.im ∧ (z + I) / (z - I) ∈ fundDomain Γ},
            f ((z + I) / (z - I)) * ENNReal.ofReal ((z.im ^ 2)⁻¹) =
          ∫⁻ w in fundDomain Γ, f w * ENNReal.ofReal (rho w) := by
  -- `hrel` is not needed: the covering only uses `hrel'`, and the integral identity is a change of variables.
  have _h := hrel
  have hfd := isFundDomain_fundDomain hΓ.1
  set F' : Set ℂ := {z : ℂ | 0 < z.im ∧ (z + I) / (z - I) ∈ fundDomain Γ} with hF'
  have hcm : Measurable fun z : ℂ => (z + I) / (z - I) := by fun_prop
  have hF'm : MeasurableSet F' :=
    (measurableSet_lt measurable_const Complex.measurable_im).inter (hcm (fundDomain_measurable Γ))
  have hFI : ∀ z ∈ F', z - I ≠ 0 := by
    intro z hz h0
    have h := hfd.2.1 hz.2
    rw [h0, div_zero] at h
    exact absurd (show (1 : ℝ) < ‖(0 : ℂ)‖ from h) (by simp)
  have hinj : InjOn (fun z : ℂ => (z + I) / (z - I)) F' := by
    intro z1 h1 z2 h2 h
    simp only at h
    calc z1 = I * ((z1 + I) / (z1 - I) + 1) / ((z1 + I) / (z1 - I) - 1) :=
          (s13c_cayInv_cay (hFI z1 h1)).symm
      _ = I * ((z2 + I) / (z2 - I) + 1) / ((z2 + I) / (z2 - I) - 1) := by rw [h]
      _ = z2 := s13c_cayInv_cay (hFI z2 h2)
  have himg : (fun z : ℂ => (z + I) / (z - I)) '' F' = fundDomain Γ := by
    ext w
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact hz.2
    · intro hw
      have hw1 : 1 < ‖w‖ := hfd.2.1 hw
      have hw1' : w - 1 ≠ 0 := by
        intro h
        rw [sub_eq_zero] at h
        rw [h, norm_one] at hw1
        exact lt_irrefl _ hw1
      refine ⟨I * (w + 1) / (w - 1), ⟨s13c_cayInv_im hw1, ?_⟩, s13c_cay_cayInv hw1'⟩
      rw [s13c_cay_cayInv hw1']
      exact hw
  have hint : ∀ f : ℂ → ℝ≥0∞, Measurable f →
      ∫⁻ z in F', f ((z + I) / (z - I)) * ENNReal.ofReal ((z.im ^ 2)⁻¹) =
        ∫⁻ w in fundDomain Γ, f w * ENNReal.ofReal (rho w) := by
    intro f _
    rw [← himg, lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hF'm
      (f' := fun x => (ContinuousLinearMap.toSpanSingleton ℂ (-(2 * I) / (x - I) ^ 2)).restrictScalars ℝ)
      (fun x hx => ((s13c_cay_hasDerivAt (hFI x hx)).hasFDerivAt.restrictScalars ℝ).hasFDerivWithinAt)
      hinj]
    refine setLIntegral_congr_fun hF'm fun z hz => ?_
    simp only [det_restrictScalars_toSpanSingleton]
    rw [abs_of_nonneg (sq_nonneg _), mul_left_comm, ← ENNReal.ofReal_mul (sq_nonneg _),
      s13c_cay_jac hz.1 (hFI z hz)]
  have hcov : ∀ᵐ z ∂(volume.restrict upperHalf), ∀ hz : 0 < z.im, ∃ M ∈ Γ',
      ((M • (⟨z, hz⟩ : UpperHalfPlane) : UpperHalfPlane) : ℂ) ∈ F' := by
    have hE : MeasurableSet unitDiscExterior :=
      (isOpen_lt continuous_const continuous_norm).measurableSet
    have h1 := (ae_restrict_iff' hE).mp hfd.2.2.1
    set N : Set ℂ := {w | ¬ (w ∈ unitDiscExterior → ∃ g ∈ Γ, mob g w ∈ fundDomain Γ)} with hN
    have hN0 : volume N = 0 := ae_iff.mp h1
    have hNd : DifferentiableOn ℂ (fun w : ℂ => I * (w + 1) / (w - 1)) N := by
      intro w hw
      have hw1 : 1 < ‖w‖ := by
        by_contra hc
        exact hw (fun h => absurd h hc)
      have hw1' : w - 1 ≠ 0 := by
        intro h
        rw [sub_eq_zero] at h
        rw [h, norm_one] at hw1
        exact lt_irrefl _ hw1
      exact (by fun_prop (disch := exact hw1') :
        DifferentiableAt ℂ (fun w : ℂ => I * (w + 1) / (w - 1)) w).differentiableWithinAt
    have hNi : volume ((fun w : ℂ => I * (w + 1) / (w - 1)) '' N) = 0 :=
      addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume (hNd.restrictScalars ℝ) hN0
    have hbad : ∀ᵐ z ∂volume, z ∉ (fun w : ℂ => I * (w + 1) / (w - 1)) '' N ∧ z ≠ I := by
      filter_upwards [compl_mem_ae_iff.mpr hNi, compl_mem_ae_iff.mpr (measure_singleton I)] with z h1 h2
      exact ⟨h1, h2⟩
    filter_upwards [ae_restrict_of_ae hbad] with z hz0 hz
    obtain ⟨hzN, hzI⟩ := hz0
    have hzI' : z - I ≠ 0 := sub_ne_zero.mpr hzI
    have hcz : 1 < ‖(z + I) / (z - I)‖ := s13c_cay_ext hz hzI'
    obtain ⟨g, hg, hgF⟩ : ∃ g ∈ Γ, mob g ((z + I) / (z - I)) ∈ fundDomain Γ := by
      by_contra hc
      exact hzN ⟨(z + I) / (z - I), fun h => hc (h hcz), s13c_cayInv_cay hzI'⟩
    have hden : g 1 0 * ((z + I) / (z - I)) + g 1 1 ≠ 0 := by
      intro h0
      have h := hfd.2.1 hgF
      rw [show mob g ((z + I) / (z - I)) = (g 0 0 * ((z + I) / (z - I)) + g 0 1) /
        (g 1 0 * ((z + I) / (z - I)) + g 1 1) from rfl, h0, div_zero] at h
      exact absurd (show (1 : ℝ) < ‖(0 : ℂ)‖ from h) (by simp)
    obtain ⟨M, hM, hrelM⟩ := hrel' g hg
    have hMI := s13c_not_pole (τ0 := ⟨z, hz⟩) hzI hden hrelM
    refine ⟨M, hM, (M • (⟨z, hz⟩ : UpperHalfPlane)).im_pos, ?_⟩
    rw [← hrelM ⟨z, hz⟩ hzI hMI]
    exact hgF
  exact ⟨hF'm, fun z hz => hz.1, hcov, hint⟩

/-- **(B2) Siegel's theorem.** A Fuchsian group of `SL(2, ℝ)` with a measurable covering set of finite hyperbolic
area is finitely generated. -/
theorem s13c_siegel_fg {Γ' : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} (hΓ' : LiZhongQC.IsFuchsian Γ')
    {F : Set ℂ} (hFm : MeasurableSet F) (hFH : F ⊆ upperHalf)
    (hcov : ∀ᵐ z ∂(volume.restrict upperHalf), ∀ hz : 0 < z.im, ∃ M ∈ Γ',
      ((M • (⟨z, hz⟩ : UpperHalfPlane) : UpperHalfPlane) : ℂ) ∈ F)
    (harea : ∫⁻ z in F, ENNReal.ofReal ((z.im ^ 2)⁻¹) < ∞) : Γ'.FG := by
  obtain ⟨p, hp⟩ := s13c_sg_base hΓ'
  have hfin := s13c_sg_core hΓ' hp (s13c_sg_area hΓ' hp hFm hFH hcov harea)
  exact (Subgroup.fg_iff Γ').mpr ⟨_, s13c_sg_gen hΓ' p, hfin⟩

/-- **(B3) Selberg, with an explicit covering set.** A finitely generated Fuchsian group has a torsion-free,
finitely generated Fuchsian subgroup `Γ₀` and a covering set `F₀` for `Γ₀` with `∫_{F₀} f ≤ k ∫_F f` for all
`Γ'`-invariant `f`. -/
theorem s13c_selberg {Γ' : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} (hΓ' : LiZhongQC.IsFuchsian Γ')
    (hfg : Γ'.FG) {F : Set ℂ} (hFm : MeasurableSet F) (hFH : F ⊆ upperHalf)
    (hcov : ∀ᵐ z ∂(volume.restrict upperHalf), ∀ hz : 0 < z.im, ∃ M ∈ Γ',
      ((M • (⟨z, hz⟩ : UpperHalfPlane) : UpperHalfPlane) : ℂ) ∈ F) :
    ∃ Γ₀ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ), Γ₀ ≤ Γ' ∧ LiZhongQC.IsFuchsian Γ₀ ∧ ActsFreely Γ₀ ∧
      Γ₀.FG ∧ ∃ F₀ : Set ℂ, MeasurableSet F₀ ∧ F₀ ⊆ upperHalf ∧
        (∀ᵐ z ∂(volume.restrict upperHalf), ∀ hz : 0 < z.im, ∃ M ∈ Γ₀,
          ((M • (⟨z, hz⟩ : UpperHalfPlane) : UpperHalfPlane) : ℂ) ∈ F₀) ∧
        ∃ k : ℕ, ∀ f : ℂ → ℝ≥0∞, Measurable f →
          (∀ M ∈ Γ', ∀ τ : UpperHalfPlane, f ((M • τ : UpperHalfPlane) : ℂ) = f τ) →
          ∫⁻ z in F₀, f z * ENNReal.ofReal ((z.im ^ 2)⁻¹) ≤
            k * ∫⁻ z in F, f z * ENNReal.ofReal ((z.im ^ 2)⁻¹) := by
  obtain ⟨Γ₀, hle, hidx, hfg₀, htf⟩ := LiZhongQC.sel_selberg hfg
  have hΓ₀ : LiZhongQC.IsFuchsian Γ₀ := fun C hC => (hΓ' C hC).subset fun γ hγ => ⟨hle hγ.1, hγ.2⟩
  -- torsion-free and discrete: no element has a fixed point
  have hfree : ActsFreely Γ₀ := by
    intro γ hγ τ hfix
    left
    apply htf γ hγ
    have hfin := hΓ₀ {τ} isCompact_singleton
    rw [← finite_powers]
    refine hfin.subset ?_
    rintro _ ⟨k, rfl⟩
    have hk : γ ^ k • τ = τ := by
      induction k with
      | zero => simp
      | succ k ih => rw [pow_succ, mul_smul, hfix, ih]
    exact ⟨Γ₀.pow_mem hγ k, τ, ⟨τ, rfl, hk⟩, rfl⟩
  -- coset representatives of `Γ₀` in `Γ'`
  haveI : (Γ₀.subgroupOf Γ').FiniteIndex := ⟨hidx⟩
  haveI : Finite (Γ' ⧸ Γ₀.subgroupOf Γ') := Subgroup.finite_quotient_of_finiteIndex
  haveI := Fintype.ofFinite (Γ' ⧸ Γ₀.subgroupOf Γ')
  have hmob : ∀ γ : Matrix.SpecialLinearGroup (Fin 2) ℝ, Measurable fun z : ℂ =>
      (((γ 0 0 : ℝ) : ℂ) * z + ((γ 0 1 : ℝ) : ℂ)) / (((γ 1 0 : ℝ) : ℂ) * z + ((γ 1 1 : ℝ) : ℂ)) :=
    fun γ => by fun_prop
  obtain ⟨F₀, hF₀⟩ : ∃ F₀ : Set ℂ, F₀ = ⋃ q : Γ' ⧸ Γ₀.subgroupOf Γ',
      (fun z : ℂ => (((((q.out : Γ') : Matrix.SpecialLinearGroup (Fin 2) ℝ)⁻¹ 0 0 : ℝ) : ℂ) * z +
        ((((q.out : Γ') : Matrix.SpecialLinearGroup (Fin 2) ℝ)⁻¹ 0 1 : ℝ) : ℂ)) /
        (((((q.out : Γ') : Matrix.SpecialLinearGroup (Fin 2) ℝ)⁻¹ 1 0 : ℝ) : ℂ) * z +
        ((((q.out : Γ') : Matrix.SpecialLinearGroup (Fin 2) ℝ)⁻¹ 1 1 : ℝ) : ℂ))) '' F := ⟨_, rfl⟩
  refine ⟨Γ₀, hle, hΓ₀, hfree, hfg₀, F₀, ?_, ?_, ?_, Fintype.card (Γ' ⧸ Γ₀.subgroupOf Γ'), ?_⟩
  · rw [hF₀]
    refine MeasurableSet.iUnion fun q => ?_
    rw [s13c_image_eq _ hFH]
    exact (measurableSet_lt measurable_const Complex.measurable_im).inter (hmob _ hFm)
  · rw [hF₀]
    intro z hz
    obtain ⟨q, hq⟩ := mem_iUnion.mp hz
    obtain ⟨w, hw, rfl⟩ := hq
    exact s13c_mobR_im_pos _ (hFH hw)
  · filter_upwards [hcov] with z hz hz'
    obtain ⟨M, hM, hMF⟩ := hz hz'
    obtain ⟨q, hq⟩ : ∃ q : Γ' ⧸ Γ₀.subgroupOf Γ', q = QuotientGroup.mk ⟨M, hM⟩ := ⟨_, rfl⟩
    have h := QuotientGroup.eq.mp ((QuotientGroup.out_eq' q).trans hq)
    have hmem : ((q.out : Γ') : Matrix.SpecialLinearGroup (Fin 2) ℝ)⁻¹ * M ∈ Γ₀ :=
      Subgroup.mem_subgroupOf.mp h
    refine ⟨_, hmem, ?_⟩
    rw [hF₀]
    refine mem_iUnion.mpr ⟨q, _, hMF, ?_⟩
    rw [mul_smul, s13c_smul_coe (((q.out : Γ') : Matrix.SpecialLinearGroup (Fin 2) ℝ)⁻¹)]
  · intro f hf hfinv
    calc ∫⁻ z in F₀, f z * ENNReal.ofReal ((z.im ^ 2)⁻¹)
        ≤ ∑' q : Γ' ⧸ Γ₀.subgroupOf Γ', ∫⁻ z in
            (fun z : ℂ => (((((q.out : Γ') : Matrix.SpecialLinearGroup (Fin 2) ℝ)⁻¹ 0 0 : ℝ) : ℂ) * z +
              ((((q.out : Γ') : Matrix.SpecialLinearGroup (Fin 2) ℝ)⁻¹ 0 1 : ℝ) : ℂ)) /
              (((((q.out : Γ') : Matrix.SpecialLinearGroup (Fin 2) ℝ)⁻¹ 1 0 : ℝ) : ℂ) * z +
              ((((q.out : Γ') : Matrix.SpecialLinearGroup (Fin 2) ℝ)⁻¹ 1 1 : ℝ) : ℂ))) '' F,
            f z * ENNReal.ofReal ((z.im ^ 2)⁻¹) := by
          rw [hF₀]
          exact lintegral_iUnion_le _ _
      _ = ∑' _q : Γ' ⧸ Γ₀.subgroupOf Γ', ∫⁻ z in F, f z * ENNReal.ofReal ((z.im ^ 2)⁻¹) := by
          congr 1
          funext q
          rw [s13c_hyp_cov _ hFm hFH]
          refine setLIntegral_congr_fun hFm fun z hz => ?_
          have e := hfinv _ (Γ'.inv_mem q.out.2) ⟨z, hFH hz⟩
          rw [s13c_smul_coe' _ (hFH hz)] at e
          rw [e]
      _ = Fintype.card (Γ' ⧸ Γ₀.subgroupOf Γ') * ∫⁻ z in F, f z * ENNReal.ofReal ((z.im ^ 2)⁻¹) := by
          rw [tsum_fintype, Finset.sum_const, nsmul_eq_mul, Finset.card_univ]

/-- **(B4) No funnels.** For a torsion-free, finitely generated Fuchsian group with a finite-area covering set,
`ℍ` is covered modulo `Γ₀` by a compact set and finitely many precisely invariant cusp horoballs. -/
theorem s13c_no_funnel {Γ₀ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} (hΓ₀ : LiZhongQC.IsFuchsian Γ₀)
    (hfree : ActsFreely Γ₀) (hfg : Γ₀.FG) {F₀ : Set ℂ} (hF₀m : MeasurableSet F₀) (hF₀H : F₀ ⊆ upperHalf)
    (hcov₀ : ∀ᵐ z ∂(volume.restrict upperHalf), ∀ hz : 0 < z.im, ∃ M ∈ Γ₀,
      ((M • (⟨z, hz⟩ : UpperHalfPlane) : UpperHalfPlane) : ℂ) ∈ F₀)
    (harea : ∫⁻ z in F₀, ENNReal.ofReal ((z.im ^ 2)⁻¹) < ∞) :
    ∃ (n : ℕ) (C : Set UpperHalfPlane) (A π₀ : Fin n → Matrix.SpecialLinearGroup (Fin 2) ℝ),
      IsCompact C ∧
      (∀ i, π₀ i ∈ Γ₀ ∧ ∀ τ : UpperHalfPlane, π₀ i • (A i • τ) = A i • ((1 : ℝ) +ᵥ τ)) ∧
      (∀ i i' γ, γ ∈ Γ₀ → ∀ τ : UpperHalfPlane, 1 < τ.im → 1 < ((A i')⁻¹ • (γ • (A i • τ))).im →
        i = i' ∧ ∃ k : ℤ, γ = π₀ i ^ k ∨ γ = -π₀ i ^ k) ∧
      ∀ τ : UpperHalfPlane, ∃ γ ∈ Γ₀, γ • τ ∈ C ∨ ∃ i, 1 < ((A i)⁻¹ • (γ • τ)).im := by
  rcases LiZhongQC.ft1_decomposition hΓ₀ hfree hfg with htriv | ⟨A, π₀, hπmem, hπ, hall⟩ |
      ⟨n, m, C, A, π₀, B, h, lam, θ, hC, hcusp, hfun, hpc, hpf, hcross, hcover⟩
  · -- `Γ₀ ⊆ {±1}`: the rectangle `[0, 1) × (0, 1)` is precisely invariant and has infinite area
    exfalso
    obtain ⟨hQm, hQH, hQ⟩ := s13c_rect_area (zero_lt_one : (0 : ℝ) < 1) (zero_lt_one : (0 : ℝ) < 1)
    exact s13c_no_inf hΓ₀ hF₀m hcov₀ harea hQm hQH hQ fun γ hγ _ _ _ => htriv γ hγ
  · -- cyclic parabolic: `A([0, 1) × (0, 1))` is precisely invariant and has infinite area
    exfalso
    obtain ⟨hQm, hQH, hQ⟩ := s13c_rect_area (zero_lt_one : (0 : ℝ) < 1) (zero_lt_one : (0 : ℝ) < 1)
    obtain ⟨hSm, hSH, hSa⟩ := s13c_conj_set (M := A) hQm hQH
    refine s13c_no_inf hΓ₀ hF₀m hcov₀ harea hSm hSH (hSa.trans hQ) ?_
    intro γ hγ σ hσ hγσ
    rw [s13c_conj_mem] at hσ hγσ
    obtain ⟨k, hk⟩ := hall γ hγ
    have hact : γ • σ = π₀ ^ k • σ := by
      rcases hk with hk | hk
      · rw [hk]
      · rw [hk, s13c_neg_smul]
    have hw : A⁻¹ • (π₀ ^ k • σ) = (k : ℝ) +ᵥ (A⁻¹ • σ) := by
      conv_lhs => rw [← smul_inv_smul A σ]
      rw [s13c_par_iter hπ k, inv_smul_smul]
    rw [hact, hw, UpperHalfPlane.coe_vadd] at hγσ
    obtain ⟨h1, h2, -, -⟩ := hσ
    obtain ⟨h3, h4, -, -⟩ := hγσ
    simp only [Complex.add_re, Complex.ofReal_re] at h3 h4
    have hk0 : k = 0 := by
      have e1 : (k : ℝ) < 1 := by linarith
      have e2 : (-1 : ℝ) < k := by linarith
      have e3 : k < 1 := by exact_mod_cast e1
      have e4 : -1 < k := by exact_mod_cast e2
      omega
    rcases hk with hk | hk
    · left
      rw [hk, hk0, zpow_zero]
    · right
      rw [hk, hk0, zpow_zero]
  · rcases Nat.eq_zero_or_pos m with hm | hm
    · -- no funnels: this is the claimed decomposition
      subst hm
      refine ⟨n, C, A, π₀, hC, hcusp, hpc, fun τ => ?_⟩
      obtain ⟨γ, hγ, hτ⟩ := hcover τ
      rcases hτ with h1 | h2 | ⟨j, _⟩
      · exact ⟨γ, hγ, Or.inl h1⟩
      · exact ⟨γ, hγ, Or.inr h2⟩
      · exact j.elim0
    · -- a funnel: `B([1, λ) × (0, tan (θ/2)))` is precisely invariant and has infinite area
      exfalso
      set j : Fin m := ⟨0, hm⟩ with hj
      obtain ⟨-, hlam, hθ0, hθπ, hfj⟩ := hfun j
      have hs : 0 < Real.tan (θ j / 2) := Real.tan_pos_of_pos_of_lt_pi_div_two (by linarith) (by linarith)
      obtain ⟨hQm, hQH, hQ⟩ := s13c_rect_area hlam hs
      obtain ⟨hSm, hSH, hSa⟩ := s13c_conj_set (M := B j) hQm hQH
      refine s13c_no_inf hΓ₀ hF₀m hcov₀ harea hSm hSH (hSa.trans hQ) ?_
      intro γ hγ σ hσ hγσ
      rw [s13c_conj_mem] at hσ hγσ
      have hσw : σ = B j • ((B j)⁻¹ • σ) := (smul_inv_smul _ _).symm
      obtain ⟨h1, h2, h3, h4⟩ := hσ
      have hargw : (((B j)⁻¹ • σ : UpperHalfPlane) : ℂ).arg < θ j := s13c_arg_lt hθ0 hθπ h1 h3 h4
      rw [hσw] at hγσ
      obtain ⟨h5, h6, h7, h8⟩ := hγσ
      obtain ⟨-, k, hk⟩ := hpf j j γ hγ ((B j)⁻¹ • σ) hargw (s13c_arg_lt hθ0 hθπ h5 h7 h8)
      have hact : ((B j)⁻¹ • (γ • (B j • ((B j)⁻¹ • σ))) : UpperHalfPlane) =
          (B j)⁻¹ • (h j ^ k • (B j • ((B j)⁻¹ • σ))) := by
        rcases hk with hk | hk
        · rw [hk]
        · rw [hk, s13c_neg_smul]
      rw [hact, s13c_hyp_iter (by linarith) hfj k] at h5 h6
      simp only [Complex.re_ofReal_mul] at h5 h6
      have hw0 : 0 < (((B j)⁻¹ • σ : UpperHalfPlane) : ℂ).re := by linarith
      have hk0 : k = 0 := by
        by_contra hne
        rcases lt_or_gt_of_ne hne with hneg | hpos
        · have e : lam j ^ k ≤ lam j ^ (-1 : ℤ) := zpow_le_zpow_right₀ hlam.le (by omega)
          rw [zpow_neg_one] at e
          have : lam j ^ k * (((B j)⁻¹ • σ : UpperHalfPlane) : ℂ).re < 1 :=
            calc lam j ^ k * (((B j)⁻¹ • σ : UpperHalfPlane) : ℂ).re
                ≤ (lam j)⁻¹ * (((B j)⁻¹ • σ : UpperHalfPlane) : ℂ).re := mul_le_mul_of_nonneg_right e hw0.le
              _ < (lam j)⁻¹ * lam j := mul_lt_mul_of_pos_left h2 (inv_pos.mpr (by linarith))
              _ = 1 := inv_mul_cancel₀ (by linarith)
          linarith
        · have e : lam j ^ (1 : ℤ) ≤ lam j ^ k := zpow_le_zpow_right₀ hlam.le (by omega)
          rw [zpow_one] at e
          have : lam j ≤ lam j ^ k * (((B j)⁻¹ • σ : UpperHalfPlane) : ℂ).re := by
            calc lam j = lam j * 1 := (mul_one _).symm
              _ ≤ lam j ^ k * (((B j)⁻¹ • σ : UpperHalfPlane) : ℂ).re :=
                mul_le_mul e h1 zero_le_one (by linarith)
          linarith
      rcases hk with hk | hk
      · left
        rw [hk, hk0, zpow_zero]
      · right
        rw [hk, hk0, zpow_zero]

/-- **(B5) Sup bound in `ℍ`.** With a compact core and precisely invariant cusp horoballs, every holomorphic,
bounded, `Γ₀`-invariant quadratic differential `ψ` satisfies `(y²|ψ(τ)|)² ≤ K ∫_{F₀} (y²|ψ|)² y⁻²` at every point. -/
theorem s13c_sup_H {Γ₀ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} (hΓ₀ : LiZhongQC.IsFuchsian Γ₀)
    {F₀ : Set ℂ} (hF₀m : MeasurableSet F₀) (hF₀H : F₀ ⊆ upperHalf)
    (hcov₀ : ∀ᵐ z ∂(volume.restrict upperHalf), ∀ hz : 0 < z.im, ∃ M ∈ Γ₀,
      ((M • (⟨z, hz⟩ : UpperHalfPlane) : UpperHalfPlane) : ℂ) ∈ F₀)
    {n : ℕ} {C : Set UpperHalfPlane} {A π₀ : Fin n → Matrix.SpecialLinearGroup (Fin 2) ℝ}
    (hC : IsCompact C)
    (hcusp : ∀ i, π₀ i ∈ Γ₀ ∧ ∀ τ : UpperHalfPlane, π₀ i • (A i • τ) = A i • ((1 : ℝ) +ᵥ τ))
    (hpc : ∀ i i' γ, γ ∈ Γ₀ → ∀ τ : UpperHalfPlane, 1 < τ.im → 1 < ((A i')⁻¹ • (γ • (A i • τ))).im →
      i = i' ∧ ∃ k : ℤ, γ = π₀ i ^ k ∨ γ = -π₀ i ^ k)
    (hcover : ∀ τ : UpperHalfPlane, ∃ γ ∈ Γ₀, γ • τ ∈ C ∨ ∃ i, 1 < ((A i)⁻¹ • (γ • τ)).im) :
    ∃ K : ℝ≥0∞, K < ∞ ∧ ∀ ψ : ℂ → ℂ, DifferentiableOn ℂ ψ upperHalf →
      (∃ B : ℝ, ∀ z ∈ upperHalf, z.im ^ 2 * ‖ψ z‖ ≤ B) →
      (∀ γ ∈ Γ₀, ∀ τ : UpperHalfPlane,
        ψ ((γ • τ : UpperHalfPlane) : ℂ) * (((γ 1 0 : ℝ) : ℂ) * (τ : ℂ) + ((γ 1 1 : ℝ) : ℂ))⁻¹ ^ 4 = ψ τ) →
      ∀ τ : UpperHalfPlane, ENNReal.ofReal ((τ.im ^ 2 * ‖ψ τ‖) ^ 2) ≤
        K * ∫⁻ z in F₀, ENNReal.ofReal ((z.im ^ 2 * ‖ψ z‖) ^ 2) * ENNReal.ofReal ((z.im ^ 2)⁻¹) := by
  -- `hpc` (precise invariance of the horoballs) is not needed for the sup bound: the cusp estimate
  -- `s13c_cusp` only uses the parabolic relation `hcusp`, and the covering `hcover` does the rest.
  have _h := hpc
  obtain ⟨Kseg, hKseg⟩ : ∃ Kseg : Fin n → Set UpperHalfPlane, Kseg = fun i =>
      ((↑) : UpperHalfPlane → ℂ) ⁻¹' ((fun x : ℝ => ((((A i 0 0 : ℝ) : ℂ) * ((x : ℂ) + I) + ((A i 0 1 : ℝ) : ℂ)) /
        (((A i 1 0 : ℝ) : ℂ) * ((x : ℂ) + I) + ((A i 1 1 : ℝ) : ℂ)))) '' Icc (-(1 / 2) : ℝ) (1 / 2)) :=
    ⟨_, rfl⟩
  have hK : ∀ i, IsCompact (Kseg i) := by
    intro i
    rw [hKseg]
    refine (UpperHalfPlane.isOpenEmbedding_coe.isInducing.isCompact_preimage_iff ?_).mpr ?_
    · rintro _ ⟨x, _, rfl⟩
      exact ⟨⟨_, s13c_mobR_im_pos (A i) (by simp : (0 : ℝ) < ((x : ℂ) + I).im)⟩, rfl⟩
    · exact isCompact_Icc.image (Continuous.div (by fun_prop) (by fun_prop)
        fun x => s13c_den_ne (A i) ⟨(x : ℂ) + I, by simp⟩)
  obtain ⟨cC, hcC, hC'⟩ := s13c_thick hΓ₀ hF₀m hF₀H hcov₀ hC
  choose cs hcs hS' using fun i => s13c_thick hΓ₀ hF₀m hF₀H hcov₀ (hK i)
  refine ⟨cC + ∑ i, cs i, ENNReal.add_lt_top.mpr ⟨hcC, ENNReal.sum_lt_top.mpr fun i _ => hcs i⟩, ?_⟩
  intro ψ hψd hψb hψi τ
  obtain ⟨B, hB⟩ := hψb
  have hnI : ∀ γ ∈ Γ₀, ∀ σ : UpperHalfPlane,
      (γ • σ).im ^ 2 * ‖ψ ((γ • σ : UpperHalfPlane) : ℂ)‖ = σ.im ^ 2 * ‖ψ σ‖ :=
    fun γ hγ σ => by rw [s13c_norm_transfer, hψi γ hγ σ]
  obtain ⟨γ, hγ, hcase⟩ := hcover τ
  rw [← hnI γ hγ τ]
  rcases hcase with hC1 | ⟨i, hi⟩
  · exact (hC' ψ hψd hnI _ hC1).trans (mul_le_mul_of_nonneg_right le_self_add zero_le)
  · have hAu : A i • ((A i)⁻¹ • (γ • τ)) = γ • τ := smul_inv_smul _ _
    rw [← hAu]
    have hle : cs i ≤ cC + ∑ j, cs j :=
      (Finset.single_le_sum (fun j _ => zero_le) (Finset.mem_univ i)).trans le_add_self
    set Iψ := ∫⁻ z in F₀, ENNReal.ofReal ((z.im ^ 2 * ‖ψ z‖) ^ 2) * ENNReal.ofReal ((z.im ^ 2)⁻¹) with hIψ
    by_cases htop : cs i * Iψ = ∞
    · calc _ ≤ cs i * Iψ := by
            rw [htop]
            exact le_top
        _ ≤ (cC + ∑ j, cs j) * Iψ := mul_le_mul_of_nonneg_right hle zero_le
    have hT0 : 0 ≤ (cs i * Iψ).toReal := ENNReal.toReal_nonneg
    have hseg : ∀ v : UpperHalfPlane, v.im = 1 → |v.re| ≤ 1 / 2 →
        (A i • v).im ^ 2 * ‖ψ ((A i • v : UpperHalfPlane) : ℂ)‖ ≤ Real.sqrt (cs i * Iψ).toReal := by
      intro v hv hvr
      have hvK : A i • v ∈ Kseg i := by
        rw [hKseg]
        have hvc : (v : ℂ) = ((v.re : ℝ) : ℂ) + I := Complex.ext (by simp) (by simp [hv])
        refine ⟨v.re, ⟨(abs_le.mp hvr).1, (abs_le.mp hvr).2⟩, ?_⟩
        show _ = ((A i • v : UpperHalfPlane) : ℂ)
        rw [s13c_smul_coe, hvc]
      have h1 := hS' i ψ hψd hnI _ hvK
      rw [← ENNReal.ofReal_toReal htop] at h1
      have h2 := (ENNReal.ofReal_le_ofReal_iff hT0).mp h1
      exact (le_abs_self _).trans (Real.abs_le_sqrt h2)
    have hcu := s13c_cusp (hcusp i).2 hψd hB (fun σ => hψi _ (hcusp i).1 σ) hseg _ hi.le
    have hf0 : 0 ≤ (A i • ((A i)⁻¹ • (γ • τ))).im ^ 2 *
        ‖ψ ((A i • ((A i)⁻¹ • (γ • τ)) : UpperHalfPlane) : ℂ)‖ := by positivity
    calc ENNReal.ofReal (((A i • ((A i)⁻¹ • (γ • τ))).im ^ 2 *
          ‖ψ ((A i • ((A i)⁻¹ • (γ • τ)) : UpperHalfPlane) : ℂ)‖) ^ 2)
        ≤ ENNReal.ofReal (cs i * Iψ).toReal := by
          apply ENNReal.ofReal_le_ofReal
          calc _ ≤ Real.sqrt (cs i * Iψ).toReal ^ 2 := pow_le_pow_left₀ hf0 hcu 2
            _ = _ := Real.sq_sqrt hT0
      _ = cs i * Iψ := ENNReal.ofReal_toReal htop
      _ ≤ (cC + ∑ j, cs j) * Iψ := mul_le_mul_of_nonneg_right hle zero_le

/-- **(B6) Pull-back to `ℍ`.** Every `μ ∈ span (harmonicGamma Γ)` is represented a.e. through the Cayley map by
`y² ψ` with `ψ` holomorphic, bounded and `Γ'`-invariant on `ℍ`. -/
theorem s13c_pullback {Γ : Subgroup SL2C} (hΓ : IsFuchsian Γ)
    {Γ' : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    (hrel : ∀ M ∈ Γ', ∃ g ∈ Γ, ∀ τ : UpperHalfPlane, (τ : ℂ) ≠ I → ((M • τ : UpperHalfPlane) : ℂ) ≠ I →
      mob g (((τ : ℂ) + I) / ((τ : ℂ) - I)) = (((M • τ : UpperHalfPlane) : ℂ) + I) / (((M • τ : UpperHalfPlane) : ℂ) - I))
    (hrel' : ∀ g ∈ Γ, ∃ M ∈ Γ', ∀ τ : UpperHalfPlane, (τ : ℂ) ≠ I → ((M • τ : UpperHalfPlane) : ℂ) ≠ I →
      mob g (((τ : ℂ) + I) / ((τ : ℂ) - I)) = (((M • τ : UpperHalfPlane) : ℂ) + I) / (((M • τ : UpperHalfPlane) : ℂ) - I))
    {μ : LinfStar} (hμ : μ ∈ Submodule.span ℂ (harmonicGamma Γ)) :
    ∃ ψ : ℂ → ℂ, Measurable ψ ∧ DifferentiableOn ℂ ψ upperHalf ∧
      (∃ B : ℝ, ∀ z ∈ upperHalf, z.im ^ 2 * ‖ψ z‖ ≤ B) ∧
      (∀ γ ∈ Γ', ∀ τ : UpperHalfPlane,
        ψ ((γ • τ : UpperHalfPlane) : ℂ) * (((γ 1 0 : ℝ) : ℂ) * (τ : ℂ) + ((γ 1 1 : ℝ) : ℂ))⁻¹ ^ 4 = ψ τ) ∧
      (∀ γ ∈ Γ', ∀ τ : UpperHalfPlane,
        (γ • τ).im ^ 2 * ‖ψ ((γ • τ : UpperHalfPlane) : ℂ)‖ = τ.im ^ 2 * ‖ψ τ‖) ∧
      (∀ᵐ w ∂(volume.restrict unitDiscExterior), ∃ τ : UpperHalfPlane,
        ((τ : ℂ) + I) / ((τ : ℂ) - I) = w ∧ ‖μ w‖ = τ.im ^ 2 * ‖ψ τ‖) ∧
      ∀ᵐ z ∂(volume.restrict upperHalf), ∀ _ : 0 < z.im, ‖μ ((z + I) / (z - I))‖ = z.im ^ 2 * ‖ψ z‖ := by
  -- `hrel'` is not needed: invariance under `Γ'` only uses `hrel`.
  have _h := hrel'
  obtain ⟨hHB, hLG⟩ := s13c_span_mem hΓ hμ
  obtain ⟨φ, hrep⟩ := hHB
  set Φ : ℂ → ℂ := AInf.toFun φ with hΦdef
  have hΦd : DifferentiableOn ℂ Φ unitDiscExterior := φ.2
  have hE : IsOpen unitDiscExterior := isOpen_lt continuous_const continuous_norm
  have hUH : IsOpen upperHalf := isOpen_lt continuous_const Complex.continuous_im
  -- the weighted sup bound of `φ ∈ A∞(𝔻*)`
  have hQb : ∀ w : ℂ, 1 < ‖w‖ → (1 - ‖w‖ ^ 2) ^ 2 * ‖Φ w‖ ≤ ‖φ.1‖ := by
    intro w hw
    have hw' : w ∈ unitDiscExterior := hw
    have hv : Φ w = φ.1 ⟨w, hw'⟩ / ((1 : ℂ) - (‖w‖ : ℂ) ^ 2) ^ 2 := by
      simp only [hΦdef, AInf.toFun, unweight, dif_pos hw']
    have hr : 0 < (1 - ‖w‖ ^ 2) ^ 2 := by
      have h1 : (1 - ‖w‖ ^ 2 : ℝ) < 0 := by nlinarith [norm_nonneg w]
      rw [sq]
      exact mul_pos_of_neg_of_neg h1 h1
    rw [hv, norm_div, s13c_norm_weight, mul_div_assoc', mul_div_cancel_left₀ _ hr.ne']
    exact φ.1.norm_coe_le_norm _
  -- the pull-back `ψ₀ = 4 φ(cay z) cay'(z)²` (junk at `z = i`)
  obtain ⟨ψ0, hψ0⟩ : ∃ f : ℂ → ℂ, f = fun z => 4 * Φ ((z + I) / (z - I)) * (-(2 * I) / (z - I) ^ 2) ^ 2 :=
    ⟨_, rfl⟩
  have hn0 : ∀ z : ℂ, 0 < z.im → z ≠ I →
      z.im ^ 2 * ‖ψ0 z‖ = (1 - ‖(z + I) / (z - I)‖ ^ 2) ^ 2 * ‖Φ ((z + I) / (z - I))‖ := by
    intro z hz hzI
    rw [hψ0, ← s13c_cay_jac' hz (sub_ne_zero.mpr hzI), norm_mul, norm_mul, norm_pow,
      show ‖(4 : ℂ)‖ = 4 by norm_num]
    ring
  have hd0 : DifferentiableOn ℂ ψ0 (upperHalf \ {I}) := by
    intro z hz
    have hz1 : 0 < z.im := hz.1
    have hzI : z ≠ I := hz.2
    have hzI' : z - I ≠ 0 := sub_ne_zero.mpr hzI
    have hc := (s13c_cay_hasDerivAt hzI').differentiableAt
    have hΦa : DifferentiableAt ℂ Φ ((z + I) / (z - I)) :=
      hΦd.differentiableAt (hE.mem_nhds (s13c_cay_ext hz1 hzI'))
    have hq : DifferentiableAt ℂ (fun z : ℂ => (-(2 * I) / (z - I) ^ 2) ^ 2) z := by
      fun_prop (disch := exact pow_ne_zero 2 hzI')
    rw [hψ0]
    exact (((differentiableAt_const (4 : ℂ)).mul (hΦa.comp z hc)).mul hq).differentiableWithinAt
  -- removable singularity at `i`
  have hsub : ∀ z ∈ ball I (1 / 2), 1 / 2 < z.im := by
    intro z hz
    have h := mem_ball.mp hz
    rw [dist_eq_norm] at h
    have h2 := (Complex.abs_im_le_norm (z - I)).trans_lt h
    simp only [Complex.sub_im, Complex.I_im] at h2
    linarith [(abs_lt.mp h2).1]
  have hb : BddAbove (norm ∘ ψ0 '' (ball I (1 / 2) \ {I})) := by
    refine ⟨4 * ‖φ.1‖, ?_⟩
    rintro _ ⟨z, hz, rfl⟩
    have hy := hsub z hz.1
    have hz1 : 0 < z.im := by linarith
    have hzI : z ≠ I := hz.2
    have h1 := hn0 z hz1 hzI
    have h2 := hQb _ (s13c_cay_ext hz1 (sub_ne_zero.mpr hzI))
    have hy2 : 1 / 4 ≤ z.im ^ 2 := by nlinarith
    show ‖ψ0 z‖ ≤ 4 * ‖φ.1‖
    nlinarith [mul_nonneg (sub_nonneg.mpr hy2) (norm_nonneg (ψ0 z)), norm_nonneg (ψ0 z)]
  obtain ⟨ψ1, hψ1⟩ : ∃ f : ℂ → ℂ, f = Function.update ψ0 I (limUnder (𝓝[≠] I) ψ0) := ⟨_, rfl⟩
  have hd1s : DifferentiableOn ℂ ψ1 (ball I (1 / 2)) := by
    rw [hψ1]
    exact Complex.differentiableOn_update_limUnder_of_bddAbove (ball_mem_nhds I (by norm_num))
      (hd0.mono fun z hz => ⟨(show (0 : ℝ) < z.im from lt_trans (by norm_num) (hsub z hz.1)), hz.2⟩) hb
  have hψ1eq : ∀ z, z ≠ I → ψ1 z = ψ0 z := by
    intro z hz
    rw [hψ1]
    exact Function.update_of_ne hz _ _
  have hd1 : DifferentiableOn ℂ ψ1 upperHalf := by
    intro z hz
    by_cases hzI : z = I
    · rw [hzI]
      exact (hd1s.differentiableAt (ball_mem_nhds I (by norm_num))).differentiableWithinAt
    · have h0 : DifferentiableAt ℂ ψ0 z :=
        hd0.differentiableAt ((hUH.sdiff isClosed_singleton).mem_nhds ⟨hz, hzI⟩)
      have heq : ψ1 =ᶠ[𝓝 z] ψ0 := (continuousAt_id.eventually_ne hzI).mono fun w hw => hψ1eq w hw
      exact (h0.congr_of_eventuallyEq heq).differentiableWithinAt
  -- `ψ`: the filled-in pull-back on `ℍ`, zero off `ℍ`
  obtain ⟨ψ, hψ⟩ : ∃ f : ℂ → ℂ, f = upperHalf.piecewise ψ1 0 := ⟨_, rfl⟩
  have hψeq : ∀ z ∈ upperHalf, ψ z = ψ1 z := by
    intro z hz
    rw [hψ]
    exact Set.piecewise_eq_of_mem _ _ _ hz
  have hψd : DifferentiableOn ℂ ψ upperHalf := hd1.congr hψeq
  have hψm : Measurable ψ := by
    rw [hψ]
    exact ContinuousOn.measurable_piecewise hd1.continuousOn continuousOn_const hUH.measurableSet
  have hψc : ∀ z ∈ upperHalf, ContinuousAt ψ z := fun z hz =>
    (hψd.differentiableAt (hUH.mem_nhds hz)).continuousAt
  have hψ0' : ∀ z : ℂ, 0 < z.im → z ≠ I → ψ z = ψ0 z := fun z hz hzI =>
    (hψeq z hz).trans (hψ1eq z hzI)
  have hnorm : ∀ z : ℂ, 0 < z.im → z ≠ I →
      z.im ^ 2 * ‖ψ z‖ = (1 - ‖(z + I) / (z - I)‖ ^ 2) ^ 2 * ‖Φ ((z + I) / (z - I))‖ :=
    fun z hz hzI => by rw [hψ0' z hz hzI]; exact hn0 z hz hzI
  -- boundedness (at `i` by continuity)
  have hbound : ∀ z ∈ upperHalf, z.im ^ 2 * ‖ψ z‖ ≤ ‖φ.1‖ := by
    intro z hz
    by_cases hzI : z = I
    · have hI : I ∈ upperHalf := by
        show (0 : ℝ) < I.im
        simp
      rw [hzI]
      have hT : Tendsto (fun w : ℂ => w.im ^ 2 * ‖ψ w‖) (𝓝[≠] I) (𝓝 (I.im ^ 2 * ‖ψ I‖)) :=
        ((Complex.continuous_im.continuousAt.pow 2).mul (hψc I hI).norm).tendsto.mono_left
          nhdsWithin_le_nhds
      refine le_of_tendsto hT ?_
      filter_upwards [nhdsWithin_le_nhds (hUH.mem_nhds hI), self_mem_nhdsWithin] with w hw hw2
      rw [hnorm w hw hw2]
      exact hQb _ (s13c_cay_ext hw (sub_ne_zero.mpr hw2))
    · rw [hnorm z hz hzI]
      exact hQb _ (s13c_cay_ext hz (sub_ne_zero.mpr hzI))
  -- invariance off the exceptional points, by the chain rule
  have hinv0 : ∀ γ ∈ Γ', ∀ τ : UpperHalfPlane, (τ : ℂ) ≠ I → ((γ • τ : UpperHalfPlane) : ℂ) ≠ I →
      ψ ((γ • τ : UpperHalfPlane) : ℂ) * (((γ 1 0 : ℝ) : ℂ) * (τ : ℂ) + ((γ 1 1 : ℝ) : ℂ))⁻¹ ^ 4 =
        ψ τ := by
    intro γ hγ τ h1 h2
    obtain ⟨g, hg, hR⟩ := hrel γ hγ
    have hτI : (τ : ℂ) - I ≠ 0 := sub_ne_zero.mpr h1
    have hγI : ((γ • τ : UpperHalfPlane) : ℂ) - I ≠ 0 := sub_ne_zero.mpr h2
    have hR0 := hR τ h1 h2
    have hwE : 1 < ‖((τ : ℂ) + I) / ((τ : ℂ) - I)‖ := s13c_cay_ext τ.im_pos hτI
    have hden : g 1 0 * (((τ : ℂ) + I) / ((τ : ℂ) - I)) + g 1 1 ≠ 0 := by
      intro h0
      have h := s13c_cay_ext (γ • τ).im_pos hγI
      rw [← hR0, show mob g (((τ : ℂ) + I) / ((τ : ℂ) - I)) =
        (g 0 0 * (((τ : ℂ) + I) / ((τ : ℂ) - I)) + g 0 1) /
          (g 1 0 * (((τ : ℂ) + I) / ((τ : ℂ) - I)) + g 1 1) from rfl, h0, div_zero, norm_zero] at h
      exact absurd h (by norm_num)
    have hauto := s13c_auto hΓ hLG hΦd hrep hg hwE hden
    have hH := s13c_real_mob_hasDerivAt γ τ
    have hc2 := s13c_cay_hasDerivAt hγI
    rw [s13c_smul_coe] at hc2
    have hF1 := hc2.comp (τ : ℂ) hH
    have hF2 := ((fd_mob_differentiableAt g hden).hasDerivAt).comp (τ : ℂ) (s13c_cay_hasDerivAt hτI)
    have hHc := hH.continuousAt
    have h2' : (((γ 0 0 : ℝ) : ℂ) * (τ : ℂ) + ((γ 0 1 : ℝ) : ℂ)) /
        (((γ 1 0 : ℝ) : ℂ) * (τ : ℂ) + ((γ 1 1 : ℝ) : ℂ)) ≠ I := by
      rw [← s13c_smul_coe]
      exact h2
    have heq : (mob g ∘ fun z : ℂ => (z + I) / (z - I)) =ᶠ[𝓝 (τ : ℂ)]
        ((fun u : ℂ => (u + I) / (u - I)) ∘ fun z : ℂ => (((γ 0 0 : ℝ) : ℂ) * z + ((γ 0 1 : ℝ) : ℂ)) /
          (((γ 1 0 : ℝ) : ℂ) * z + ((γ 1 1 : ℝ) : ℂ))) := by
      filter_upwards [hUH.mem_nhds τ.im_pos, continuousAt_id.eventually_ne h1, hHc.eventually_ne h2']
        with z hz1 hz2 hz3
      have hz3' : ((γ • (⟨z, hz1⟩ : UpperHalfPlane) : UpperHalfPlane) : ℂ) ≠ I := by
        rw [s13c_smul_coe]
        exact hz3
      have h := hR ⟨z, hz1⟩ hz2 hz3'
      rw [s13c_smul_coe] at h
      exact h
    have hd := (hF1.congr_of_eventuallyEq heq).unique hF2
    rw [hψ0' _ (γ • τ).im_pos h2, hψ0' _ τ.im_pos h1, hψ0]
    beta_reduce
    rw [← hR0, s13c_smul_coe]
    generalize ((γ 1 0 : ℝ) : ℂ) * (τ : ℂ) + ((γ 1 1 : ℝ) : ℂ) = D at hd ⊢
    set c0 := -(2 * I) / ((τ : ℂ) - I) ^ 2 with hc0
    set g' := deriv (mob g) (((τ : ℂ) + I) / ((τ : ℂ) - I)) with hg'
    set Φ' := Φ (mob g (((τ : ℂ) + I) / ((τ : ℂ) - I))) with hΦ'
    set c1 := -(2 * I) / ((((γ 0 0 : ℝ) : ℂ) * (τ : ℂ) + ((γ 0 1 : ℝ) : ℂ)) / D - I) ^ 2 with hc1
    linear_combination (4 * Φ' * (c1 * (1 / D ^ 2) + g' * c0)) * hd + 4 * c0 ^ 2 * hauto
  -- invariance everywhere, by continuity
  have hinv : ∀ γ ∈ Γ', ∀ τ : UpperHalfPlane,
      ψ ((γ • τ : UpperHalfPlane) : ℂ) * (((γ 1 0 : ℝ) : ℂ) * (τ : ℂ) + ((γ 1 1 : ℝ) : ℂ))⁻¹ ^ 4 = ψ τ := by
    intro γ hγ τ
    have hH := s13c_real_mob_hasDerivAt γ τ
    have hHc := hH.continuousAt
    have hτH : (τ : ℂ) ∈ upperHalf := τ.im_pos
    have hψγ : ContinuousAt ψ ((((γ 0 0 : ℝ) : ℂ) * (τ : ℂ) + ((γ 0 1 : ℝ) : ℂ)) /
        (((γ 1 0 : ℝ) : ℂ) * (τ : ℂ) + ((γ 1 1 : ℝ) : ℂ))) := by
      rw [← s13c_smul_coe]
      exact hψc _ (γ • τ).im_pos
    have hf1 : ContinuousAt (fun z : ℂ => ψ ((((γ 0 0 : ℝ) : ℂ) * z + ((γ 0 1 : ℝ) : ℂ)) /
        (((γ 1 0 : ℝ) : ℂ) * z + ((γ 1 1 : ℝ) : ℂ))) * (((γ 1 0 : ℝ) : ℂ) * z + ((γ 1 1 : ℝ) : ℂ))⁻¹ ^ 4)
        (τ : ℂ) := by
      refine (ContinuousAt.comp (f := fun z : ℂ => (((γ 0 0 : ℝ) : ℂ) * z + ((γ 0 1 : ℝ) : ℂ)) /
        (((γ 1 0 : ℝ) : ℂ) * z + ((γ 1 1 : ℝ) : ℂ))) hψγ hHc).mul ?_
      exact (((continuousAt_const.mul continuousAt_id).add continuousAt_const).inv₀
        (s13c_den_ne γ τ)).pow 4
    have hH' : ∀ᶠ z in 𝓝[≠] (τ : ℂ), (((γ 0 0 : ℝ) : ℂ) * z + ((γ 0 1 : ℝ) : ℂ)) /
        (((γ 1 0 : ℝ) : ℂ) * z + ((γ 1 1 : ℝ) : ℂ)) ≠ I := by
      by_cases hHτ : (((γ 0 0 : ℝ) : ℂ) * (τ : ℂ) + ((γ 0 1 : ℝ) : ℂ)) /
          (((γ 1 0 : ℝ) : ℂ) * (τ : ℂ) + ((γ 1 1 : ℝ) : ℂ)) = I
      · filter_upwards [nhdsWithin_le_nhds (hUH.mem_nhds hτH), self_mem_nhdsWithin] with z hz hz'
        intro e
        exact hz' (s13c_real_mob_inj γ hz hτH (e.trans hHτ.symm))
      · exact nhdsWithin_le_nhds (hHc.eventually_ne hHτ)
    have hev : ∀ᶠ z in 𝓝[≠] (τ : ℂ), (fun z : ℂ => ψ ((((γ 0 0 : ℝ) : ℂ) * z + ((γ 0 1 : ℝ) : ℂ)) /
        (((γ 1 0 : ℝ) : ℂ) * z + ((γ 1 1 : ℝ) : ℂ))) * (((γ 1 0 : ℝ) : ℂ) * z + ((γ 1 1 : ℝ) : ℂ))⁻¹ ^ 4) z =
          ψ z := by
      filter_upwards [nhdsWithin_le_nhds (hUH.mem_nhds hτH), s13c_ev_ne (τ : ℂ) I, hH'] with z hz hz1 hz2
      have h := hinv0 γ hγ ⟨z, hz⟩ hz1 (by rw [s13c_smul_coe]; exact hz2)
      rw [s13c_smul_coe] at h
      exact h
    have := s13c_eq_of_punctured hf1 (hψc _ hτH) hev
    rw [s13c_smul_coe]
    exact this
  have hnormInv : ∀ γ ∈ Γ', ∀ τ : UpperHalfPlane,
      (γ • τ).im ^ 2 * ‖ψ ((γ • τ : UpperHalfPlane) : ℂ)‖ = τ.im ^ 2 * ‖ψ τ‖ := by
    intro γ hγ τ
    have hD := s13c_den_ne γ τ
    have hn : ‖((γ 1 0 : ℝ) : ℂ) * (τ : ℂ) + ((γ 1 1 : ℝ) : ℂ)‖ ≠ 0 := norm_ne_zero_iff.mpr hD
    rw [← hinv γ hγ τ, norm_mul, norm_pow, norm_inv, ← s13c_im_smul γ τ, Complex.normSq_eq_norm_sq]
    field_simp
    try ring
  -- the two a.e. representations
  have hae1 : ∀ᵐ w ∂(volume.restrict unitDiscExterior), ∃ τ : UpperHalfPlane,
      ((τ : ℂ) + I) / ((τ : ℂ) - I) = w ∧ ‖μ w‖ = τ.im ^ 2 * ‖ψ τ‖ := by
    filter_upwards [hrep, ae_restrict_mem hE.measurableSet] with w hw hwE
    have hw1 : 1 < ‖w‖ := hwE
    have hw1' : w - 1 ≠ 0 := by
      intro h
      rw [sub_eq_zero] at h
      rw [h, norm_one] at hw1
      exact lt_irrefl _ hw1
    obtain ⟨τ, hτc⟩ : ∃ τ : UpperHalfPlane, (τ : ℂ) = I * (w + 1) / (w - 1) :=
      ⟨⟨_, s13c_cayInv_im hw1⟩, rfl⟩
    have hτI : (τ : ℂ) ≠ I := by
      rw [hτc]
      intro h
      rw [div_eq_iff hw1'] at h
      exact mul_ne_zero two_ne_zero I_ne_zero (by linear_combination h)
    refine ⟨τ, by rw [hτc]; exact s13c_cay_cayInv hw1', ?_⟩
    show ‖μ w‖ = (τ : ℂ).im ^ 2 * ‖ψ τ‖
    rw [hnorm _ τ.im_pos hτI, hτc, s13c_cay_cayInv hw1', hw, norm_mul, Complex.norm_conj,
      s13c_norm_weight]
  have hae2 : ∀ᵐ z ∂(volume.restrict upperHalf), ∀ _ : 0 < z.im,
      ‖μ ((z + I) / (z - I))‖ = z.im ^ 2 * ‖ψ z‖ := by
    filter_upwards [s13c_cay_ae hrep] with z hz hz'
    obtain ⟨hzI, hP⟩ := hz hz'
    rw [hP, norm_mul, Complex.norm_conj, s13c_norm_weight, hnorm z hz' hzI]
  exact ⟨ψ, hψm, hψd, ⟨‖φ.1‖, hbound⟩, hinv, hnormInv, hae1, hae2⟩

/-- **(B7) Dimension bound.** An a.e. sup bound by the `L²(F)` norm makes the span finite dimensional. -/
theorem s13c_dim {Γ : Subgroup SL2C} (hΓ : IsCofinite Γ)
    (hsup : ∃ K : ℝ≥0∞, K < ∞ ∧ ∀ μ ∈ Submodule.span ℂ (harmonicGamma Γ),
      ∀ᵐ w ∂(volume.restrict unitDiscExterior), (‖μ w‖₊ : ℝ≥0∞) ^ 2 ≤
        K * ∫⁻ z in fundDomain Γ, (‖μ z‖₊ : ℝ≥0∞) ^ 2 * ENNReal.ofReal (rho z)) :
    FiniteDimensional ℂ (Submodule.span ℂ (harmonicGamma Γ)) := by
  obtain ⟨K, hK, hsupK⟩ := hsup
  by_contra hinf
  have hρ0 : ∀ z, 0 ≤ rho z := fun z => div_nonneg (by norm_num) (sq_nonneg _)
  have hA : ∫ z in fundDomain Γ, rho z = (hypArea Γ).toReal := by
    rw [hypArea, ← ofReal_integral_eq_lintegral_ofReal (rho_integrableOn_fundDomain hΓ)
      (Filter.Eventually.of_forall hρ0), ENNReal.toReal_ofReal (integral_nonneg hρ0)]
  obtain ⟨m, hm⟩ : ∃ m : ℕ, K.toReal * (hypArea Γ).toReal < m := exists_nat_gt _
  obtain ⟨e, heV, heo⟩ := s13c_orthonormal hΓ hK hsupK hinf m
  have hb := s13c_bessel hΓ hK hsupK heV heo
  have hint : ∀ i, IntegrableOn (fun z => ‖e i z‖ ^ 2 * rho z) (fundDomain Γ) := by
    intro i
    have h := (wpInnerGamma_integrable hΓ (e i) (e i)).re
    refine h.congr (Filter.Eventually.of_forall fun z => ?_)
    simp only [Complex.mul_conj', ← Complex.ofReal_pow, ← Complex.ofReal_mul, Complex.ofReal_re, RCLike.ofReal_re]
    exact Complex.ofReal_re _
  have hone : ∀ i < m, ∫ z in fundDomain Γ, ‖e i z‖ ^ 2 * rho z = 1 := by
    intro i hi
    have h := congrArg Complex.re (heo i hi i hi)
    rw [wpInnerGamma_self_eq, Complex.ofReal_re, if_pos rfl, Complex.one_re] at h
    exact h
  have hsum : ∫ z in fundDomain Γ, (∑ i ∈ Finset.range m, ‖e i z‖ ^ 2) * rho z = m := by
    simp_rw [Finset.sum_mul]
    rw [integral_finset_sum _ (fun i _ => hint i)]
    rw [Finset.sum_congr rfl (fun i hi => hone i (Finset.mem_range.mp hi))]
    simp
  have hle : ∫ z in fundDomain Γ, (∑ i ∈ Finset.range m, ‖e i z‖ ^ 2) * rho z ≤
      ∫ z in fundDomain Γ, K.toReal * rho z := by
    apply integral_mono_ae
    · simp_rw [Finset.sum_mul]; exact integrable_finset_sum _ (fun i _ => hint i)
    · exact (rho_integrableOn_fundDomain hΓ).const_mul _
    · filter_upwards [ae_restrict_of_ae_restrict_of_subset (fundDomain_subset Γ) hb] with z hz
      exact mul_le_mul_of_nonneg_right hz (div_nonneg (by norm_num) (sq_nonneg _))
  rw [hsum, integral_const_mul, hA] at hle
  linarith

/-- The sup bound on `𝔻*`, assembled from B1–B6. -/
theorem s13c_sup {Γ : Subgroup SL2C} (hΓ : IsCofinite Γ) :
    ∃ K : ℝ≥0∞, K < ∞ ∧ ∀ μ ∈ Submodule.span ℂ (harmonicGamma Γ),
      ∀ᵐ w ∂(volume.restrict unitDiscExterior), (‖μ w‖₊ : ℝ≥0∞) ^ 2 ≤
        K * ∫⁻ z in fundDomain Γ, (‖μ z‖₊ : ℝ≥0∞) ^ 2 * ENNReal.ofReal (rho z) := by
  obtain ⟨Γ', hΓ', hrel, hrel'⟩ := s13c_transfer_group hΓ.1
  obtain ⟨hFm, hFH, hcov, htr⟩ := s13c_transfer_cover hΓ hrel hrel'
  have harea : ∫⁻ z in {z : ℂ | 0 < z.im ∧ (z + I) / (z - I) ∈ fundDomain Γ},
      ENNReal.ofReal ((z.im ^ 2)⁻¹) < ∞ := by
    have h1 := htr (fun _ => 1) measurable_const
    simp only [one_mul] at h1
    rw [h1]
    exact hΓ.2
  have hfg := s13c_siegel_fg hΓ' hFm hFH hcov harea
  obtain ⟨Γ₀, hle, hΓ₀, hfree, hfg₀, F₀, hF₀m, hF₀H, hcov₀, k, hk⟩ := s13c_selberg hΓ' hfg hFm hFH hcov
  have harea₀ : ∫⁻ z in F₀, ENNReal.ofReal ((z.im ^ 2)⁻¹) < ∞ := by
    have h1 := hk (fun _ => 1) measurable_const (fun _ _ _ => rfl)
    simp only [one_mul] at h1
    exact lt_of_le_of_lt h1 (ENNReal.mul_lt_top (ENNReal.natCast_lt_top k) harea)
  obtain ⟨n, C, A, π₀, hC, hcusp, hpc, hcover⟩ := s13c_no_funnel hΓ₀ hfree hfg₀ hF₀m hF₀H hcov₀ harea₀
  obtain ⟨K, hK, hsupH⟩ := s13c_sup_H hΓ₀ hF₀m hF₀H hcov₀ hC hcusp hpc hcover
  refine ⟨K * k, ENNReal.mul_lt_top hK (ENNReal.natCast_lt_top k), fun μ hμ => ?_⟩
  obtain ⟨ψ, hψm, hψd, hψb, hψi, hψn, hψae, hψae'⟩ := s13c_pullback hΓ.1 hrel hrel' hμ
  have hfm : Measurable fun z : ℂ => ENNReal.ofReal ((z.im ^ 2 * ‖ψ z‖) ^ 2) :=
    ENNReal.measurable_ofReal.comp
      (((Complex.measurable_im.pow_const 2).mul hψm.norm).pow_const 2)
  have hfi : ∀ M ∈ Γ', ∀ τ : UpperHalfPlane,
      (fun z : ℂ => ENNReal.ofReal ((z.im ^ 2 * ‖ψ z‖) ^ 2)) ((M • τ : UpperHalfPlane) : ℂ) =
        (fun z : ℂ => ENNReal.ofReal ((z.im ^ 2 * ‖ψ z‖) ^ 2)) τ := by
    intro M hM τ
    simp only
    rw [UpperHalfPlane.coe_im, UpperHalfPlane.coe_im, hψn M hM τ]
  have h1 := hk _ hfm hfi
  have h2 : ∫⁻ z in {z : ℂ | 0 < z.im ∧ (z + I) / (z - I) ∈ fundDomain Γ},
      ENNReal.ofReal ((z.im ^ 2 * ‖ψ z‖) ^ 2) * ENNReal.ofReal ((z.im ^ 2)⁻¹) =
        ∫⁻ z in fundDomain Γ, (‖μ z‖₊ : ℝ≥0∞) ^ 2 * ENNReal.ofReal (rho z) := by
    rw [← htr (fun w => (‖μ w‖₊ : ℝ≥0∞) ^ 2) ((Lp.stronglyMeasurable μ).measurable.nnnorm.coe_nnreal_ennreal.pow_const 2)]
    refine setLIntegral_congr_fun_ae hFm ?_
    filter_upwards [(ae_restrict_iff' (isOpen_lt continuous_const Complex.continuous_im).measurableSet).mp hψae']
      with z hz hzF
    rw [← hz hzF.1 hzF.1, ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm_eq_enorm]
    rfl
  filter_upwards [hψae] with w hw
  obtain ⟨τ, -, hτ⟩ := hw
  calc (‖μ w‖₊ : ℝ≥0∞) ^ 2 = ENNReal.ofReal ((τ.im ^ 2 * ‖ψ τ‖) ^ 2) := by
        rw [← hτ, ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm_eq_enorm]
        rfl
    _ ≤ K * ∫⁻ z in F₀, ENNReal.ofReal ((z.im ^ 2 * ‖ψ z‖) ^ 2) * ENNReal.ofReal ((z.im ^ 2)⁻¹) :=
        hsupH ψ hψd hψb (fun γ hγ => hψi γ (hle hγ)) τ
    _ ≤ K * (k * ∫⁻ z in {z : ℂ | 0 < z.im ∧ (z + I) / (z - I) ∈ fundDomain Γ},
          ENNReal.ofReal ((z.im ^ 2 * ‖ψ z‖) ^ 2) * ENNReal.ofReal ((z.im ^ 2)⁻¹)) := by
        gcongr
    _ = K * k * ∫⁻ z in fundDomain Γ, (‖μ z‖₊ : ℝ≥0∞) ^ 2 * ENNReal.ofReal (rho z) := by
        rw [h2, mul_assoc]

/-- **`harmonicGamma_finiteDimensional`** (TT:1046), to replace the original in `S1_3_Fuchsian`. -/
theorem s13c_harmonicGamma_finiteDimensional {Γ : Subgroup SL2C} (hΓ : IsCofinite Γ) :
    FiniteDimensional ℂ (Submodule.span ℂ (harmonicGamma Γ)) :=
  s13c_dim hΓ (s13c_sup hΓ)

/-- (TT:1046) For a cofinite group, `T(Γ)` is finite dimensional: `Ω^{-1,1}(𝔻*, Γ)` spans a finite-dimensional
subspace. -/
theorem harmonicGamma_finiteDimensional {Γ : Subgroup SL2C} (hΓ : IsCofinite Γ) :
    FiniteDimensional ℂ (Submodule.span ℂ (harmonicGamma Γ)) :=
  by exact s13c_harmonicGamma_finiteDimensional hΓ

end TakhtajanTeo
