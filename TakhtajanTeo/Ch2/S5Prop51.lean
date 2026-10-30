import TakhtajanTeo.Ch2.S5MatAB
import TakhtajanTeo.Ch2.FaberBoundary
import TakhtajanTeo.Ch2.PeriodGrunskyBounds
import TakhtajanTeo.Ch1.ActualWelding

/-!
# Proposition 5.1 (Program G, 下属6)

Host of `prop_5_1` (TT:5564–5610). With `γ = w_μ` and the Faber polynomials `P_n` of `(𝖿, 𝗀)`, `h_N = P_{N+1} ∘ 𝗀`
on `S¹` satisfies `h_N ∘ γ = P_{N+1} ∘ 𝖿`; its coordinates are `e_N` plus the `N`-th row of `B₄`, those of `P_{N+1} ∘ 𝖿`
are the `N`-th row of `B₃`. The completed action (`s5mab_compat`) turns this into `𝔄 + 𝔅B₄ = B₃ᵗ`, `𝔅̄ + 𝔄̄B₄ = 0`,
and bounded-operator algebra gives the four clauses.

Convention check (non-trivial): `f = id`, `g(z) = e^{iθ}z` give `γ(z) = e^{-iθ}z`, `𝔄 = diag(e^{-i(n+1)θ}) ≠ I`,
`𝔅 = 0`, `b(k,-k) = e^{-ikθ}/k`, `B₂ = B₃ = diag(e^{-i(n+1)θ})`, `B₁ = B₄ = 0`; all clauses hold, and they would fail
for the reversed convention `γ = f⁻¹ ∘ g`.

* S1 `s5p51_faber_boundary`: `fb_clauses12` without the `T₀(1)` hypothesis.
* S2 `s5p51_faber_disc`: the Faber generating function on `𝔻`: `P_{n+1}(f ζ) = (n+1) Σ_q b(n+1, -q) ζ^q`.
* S3 `s5p51_weld_ext`: the continuous extension of `𝖿` to `𝔻̄` equals `𝗀 ∘ γ` on `S¹`.
* S4 `s5p51_composed`: `HC`, continuity, and the Fourier coefficients of `Π̂(γ) h_N`.
* S5 `s5p51_blocks`: the two block identities.
* S6 `s5p51_cols`: the column relations `𝔄*𝔄 - 𝔅ᵗ𝔅̄ = I`, `𝔄*𝔅 = 𝔅ᵗ𝔄̄`.
* S7 `s5p51_grunsky_facts`: boundedness, symmetry, unitarity entry, and the bounded inverse of `B₂`.
* S8 `s5p51_algebra`: the matrix algebra.
-/

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal NNReal ComplexConjugate Classical Real

noncomputable section

namespace TakhtajanTeo.Ch2

open LiZhongQC

/-- S1. Boundary Fourier coefficients of `P_{n+1} ∘ 𝗀`, for every `[μ]`. -/
theorem s5p51_faber_boundary {p : T1} {P Q : ℕ → Polynomial ℂ}
    (hPQ : IsFaber (fsans (Quotient.out p : LinfStarBall)) (gsans (Quotient.out p : LinfStarBall)) P Q) :
    let μ : LinfStar := (Quotient.out p : LinfStarBall)
    let b := grunsky (fsans μ) (gsans μ)
    let w : ℕ → ℂ → ℂ := fun n z =>
      (P (n + 1)).eval (normalizedWeldingExterior μ z) / Real.sqrt (n + 1)
    (∀ n m : ℕ, circleCoeff (w n) (m + 1) * Real.sqrt (m + 1) = kron m n) ∧
      (∀ n m : ℕ, circleCoeff (w n) (-(m + 1 : ℤ)) * Real.sqrt (m + 1) = B4 b n m) := by
  intro μ b w
  have hμ : μ ∈ LinfStarBall := (Quotient.out p : LinfStarBall).2
  have hcont := (normalizedWeldingExterior_continuous_proper hμ).1
  have hcoef : ∀ n : ℕ, ∀ k : ℤ, circleCoeff (fun z => (P (n + 1)).eval (normalizedWeldingExterior μ z)) k =
      (if k = ((n + 1 : ℕ) : ℤ) then 1 else 0) +
        (if k < 0 then ((n + 1 : ℕ) : ℂ) * grunsky (fsans μ) (gsans μ) (n + 1) ((k.natAbs - 1 : ℕ) + 1 : ℕ) else 0) := by
    intro n k
    have hF : ContinuousOn (fun z => (P (n + 1)).eval (normalizedWeldingExterior μ z)) {z | 1 ≤ ‖z‖} :=
      ((Polynomial.continuous _).comp hcont).continuousOn
    have hsum : ∀ z ∈ unitDiscExterior, HasSum
        (fun m : ℕ => (((n + 1 : ℕ) : ℂ) * grunsky (fsans μ) (gsans μ) (n + 1) (m + 1)) * z ^ (-(m + 1 : ℤ)))
        ((P (n + 1)).eval (normalizedWeldingExterior μ z) - z ^ (n + 1)) := by
      intro z hz
      have h := hPQ.2.1 n z hz
      have hg : gsans μ z = normalizedWeldingExterior μ z := by
        rw [e13_gsans_eq hμ]; exact gMu_eq_normalizedWeldingExterior hμ hz
      rw [hg] at h
      exact h
    exact FB.fb_coeff_boundary hF hsum k
  have hdiv : ∀ n : ℕ, ∀ k : ℤ, circleCoeff (w n) k =
      circleCoeff (fun z => (P (n + 1)).eval (normalizedWeldingExterior μ z)) k / (Real.sqrt (n + 1) : ℝ) :=
    fun n k => circleCoeff_div_const _ _ k
  have hsq : ∀ n : ℕ, (Real.sqrt ((n : ℝ) + 1) : ℂ) ≠ 0 := fun n => by
    exact_mod_cast (Real.sqrt_pos.2 (by positivity)).ne'
  refine ⟨fun n m => ?_, fun n m => ?_⟩
  · rw [hdiv, hcoef]
    have : ¬ ((m : ℤ) + 1 < 0) := by omega
    simp only [this, if_false, add_zero]
    unfold kron
    by_cases hmn : m = n
    · subst hmn
      have hk : ((m : ℤ) + 1 = ((m + 1 : ℕ) : ℤ)) := by push_cast; rfl
      rw [if_pos hk, if_pos rfl, div_mul_cancel₀ _ (hsq m)]
    · have : ¬ ((m : ℤ) + 1 = ((n + 1 : ℕ) : ℤ)) := by omega
      simp [this, hmn]
  · rw [hdiv, hcoef]
    have h1 : ¬ (-((m : ℤ) + 1) = ((n + 1 : ℕ) : ℤ)) := by omega
    have h2 : -((m : ℤ) + 1) < 0 := by omega
    have h3 : (-((m : ℤ) + 1)).natAbs - 1 = m := by omega
    simp only [h1, h2, if_false, if_true, zero_add, h3]
    unfold B4
    have hs1 := hsq n
    have hs2 : (Real.sqrt ((m : ℝ) + 1) : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.2 (by positivity)).ne'
    have hb : grunsky (fsans μ) (gsans μ) (n + 1) ((m : ℕ) + 1 : ℕ) = grunsky (fsans μ) (gsans μ) ((n : ℤ) + 1) ((m : ℤ) + 1) := by
      push_cast; rfl
    rw [hb]
    have hprod : (Real.sqrt (((n : ℝ) + 1) * ((m : ℝ) + 1)) : ℂ) =
        (Real.sqrt ((n : ℝ) + 1) : ℂ) * (Real.sqrt ((m : ℝ) + 1) : ℂ) := by
      rw [Real.sqrt_mul (by positivity)]; push_cast; ring
    rw [hprod]
    have hn2 : (((n + 1 : ℕ) : ℂ)) = (Real.sqrt ((n : ℝ) + 1) : ℂ) ^ 2 := by
      rw [← Complex.ofReal_pow, Real.sq_sqrt (by positivity)]; push_cast; ring
    rw [hn2]
    field_simp
    rfl

/-- S2. The Faber generating function on `𝔻`. -/
theorem s5p51_faber_disc {f g : ℂ → ℂ} (h : IsNormalizedDisjointPair f g) {P Q : ℕ → Polynomial ℂ}
    (hPQ : IsFaber f g P Q) :
    ∀ n : ℕ, ∀ ζ ∈ unitDisc,
      HasSum (fun q : ℕ => ((n + 1 : ℕ) : ℂ) * grunsky f g (n + 1) (-(q : ℤ)) * ζ ^ q) ((P (n + 1)).eval (f ζ)) := by
  intro n ζ hζ
  have h1 := faber_grunsky_positive h hPQ n hζ
  have h2 : HasSum (fun m : ℕ => (fun q : ℕ => ((n + 1 : ℕ) : ℂ) * grunsky f g (n + 1) (-(q : ℤ)) * ζ ^ q) (m + 1))
      ((P (n + 1)).eval (f ζ) -
        ∑ i ∈ Finset.range 1, (fun q : ℕ => ((n + 1 : ℕ) : ℂ) * grunsky f g (n + 1) (-(q : ℤ)) * ζ ^ q) i) := by
    simp only [Finset.sum_range_one, Nat.cast_zero, neg_zero, pow_zero, mul_one]
    push_cast
    push_cast at h1
    exact h1
  exact (hasSum_nat_add_iff' 1).mp h2

/-- S3. The continuous extension of `𝖿` to `𝔻̄` equals `𝗀 ∘ γ` on `S¹`. -/
theorem s5p51_weld_ext {μ : LinfStar} (hμ : μ ∈ LinfStarBall) :
    ∃ F : ℂ → ℂ, ContinuousOn F (closedBall 0 1) ∧ EqOn F (fsans μ) unitDisc ∧
      ∀ z ∈ unitCircle, F z = normalizedWeldingExterior μ (wA μ z) := by
  obtain ⟨⟨F, G, hFq, -, hFe, hGq, -, hGe, hFG⟩, -⟩ := normalizedWeldingPrime_actual hμ
  have hγ : IsQSCircleHomeo (wA μ) := ⟨wA_circle_sensePreserving hμ, wA_circle_quasisymmetric hμ⟩
  obtain ⟨KF, hKF⟩ := hFq
  obtain ⟨KG, hKG⟩ := hGq
  have hFc : Continuous F := continuousOn_univ.mp hKF.2.2.1.1
  have hGc : Continuous G := continuousOn_univ.mp hKG.2.2.1.1
  have hnc := (normalizedWeldingExterior_continuous_proper hμ).1
  have hsub : {z : ℂ | 1 ≤ ‖z‖} ⊆ closure unitDiscExterior := by
    have he : unitDiscExterior = (closedBall (0 : ℂ) 1)ᶜ := by
      ext z
      simp [unitDiscExterior]
    rw [he, closure_compl, interior_closedBall (0 : ℂ) one_ne_zero]
    intro z hz
    simp only [mem_compl_iff, mem_ball_zero_iff, not_lt]
    exact hz
  have hcl : EqOn G (normalizedWeldingExterior μ) {z : ℂ | 1 ≤ ‖z‖} :=
    hGe.of_subset_closure hGc.continuousOn hnc.continuousOn
      (fun z hz => show 1 ≤ ‖z‖ from le_of_lt (show 1 < ‖z‖ from hz)) hsub
  refine ⟨F, hFc.continuousOn, fun z hz => by rw [hFe hz, e13_fsans_eq hμ], fun z hz => ?_⟩
  have hw : ‖wA μ z‖ = 1 := (s5ns_circle hγ).1 hz
  rw [← hFG z hz]
  exact hcl (show 1 ≤ ‖wA μ z‖ from hw.ge)

/-- Fourier coefficients of a function continuous on `𝔻̄` with a power series in `𝔻`. -/
theorem s5p51_holo_coeff {H : ℂ → ℂ} {a : ℕ → ℂ} (hc : ContinuousOn H (closedBall 0 1))
    (ha : ∀ z ∈ unitDisc, HasSum (fun n => a n * z ^ n) (H z)) (k : ℤ) :
    circleCoeff H k = if 0 ≤ k then a k.toNat else 0 := by
  have hr := s5ct_radius_spec
  have hu := s5ct_radial_uniform hc (fun z _ => rfl) (fun j => ⟨(hr.1 j).1, (hr.1 j).2.le⟩) hr.2
  have hcont (j : ℕ) : ContinuousOn (fun z => H ((s5ct_radius j : ℂ) * z)) unitCircle := by
    apply hc.comp (by fun_prop : Continuous fun z : ℂ => (s5ct_radius j : ℂ) * z).continuousOn
    intro z hz
    show (s5ct_radius j : ℂ) * z ∈ closedBall (0 : ℂ) 1
    rw [mem_closedBall_zero_iff, norm_mul, Complex.norm_real, Real.norm_of_nonneg (hr.1 j).1,
      show ‖z‖ = 1 from hz, mul_one]
    exact (hr.1 j).2.le
  have hcf := s5ct_coeff_uniform hcont hu k
  have he (j : ℕ) : circleCoeff (fun z => H ((s5ct_radius j : ℂ) * z)) k =
      if 0 ≤ k then a k.toNat * (s5ct_radius j : ℂ) ^ k.toNat else 0 :=
    s5ct_disk_coeff ha (hr.1 j).1 (hr.1 j).2 k
  simp only [he] at hcf
  by_cases hk : 0 ≤ k
  · simp only [if_pos hk] at hcf ⊢
    have h1 : Tendsto (fun j => (s5ct_radius j : ℂ)) atTop (𝓝 ((1 : ℝ) : ℂ)) :=
      (Complex.continuous_ofReal.tendsto 1).comp hr.2
    rw [Complex.ofReal_one] at h1
    have h2 : Tendsto (fun j => a k.toNat * (s5ct_radius j : ℂ) ^ k.toNat) atTop (𝓝 (a k.toNat * 1 ^ k.toNat)) :=
      tendsto_const_nhds.mul (h1.pow k.toNat)
    rw [one_pow, mul_one] at h2
    exact tendsto_nhds_unique hcf h2
  · simp only [if_neg hk] at hcf ⊢
    exact tendsto_nhds_unique hcf tendsto_const_nhds

/-- S4. `h_N = P_{N+1} ∘ 𝗀 / √(N+1)` on `S¹`: membership, continuity, and the Fourier coefficients of `Π̂(γ) h_N`. -/
theorem s5p51_composed {p : T1} {P Q : ℕ → Polynomial ℂ}
    (hPQ : IsFaber (fsans (Quotient.out p : LinfStarBall)) (gsans (Quotient.out p : LinfStarBall)) P Q) :
    let μ : LinfStar := (Quotient.out p : LinfStarBall)
    let γ := wA μ
    let b := grunsky (fsans μ) (gsans μ)
    let w : ℕ → ℂ → ℂ := fun n z =>
      (P (n + 1)).eval (normalizedWeldingExterior μ z) / Real.sqrt (n + 1)
    (∀ n, w n ∈ HC ∧ ContinuousOn (w n) unitCircle) ∧
      ∀ n k : ℕ, circleCoeff (piHat γ (w n)) (k + 1) * Real.sqrt (k + 1) = B3 b n k ∧
        circleCoeff (piHat γ (w n)) (-(k + 1 : ℤ)) = 0 := by
  intro μ γ b w
  have hμ : μ ∈ LinfStarBall := (Quotient.out p : LinfStarBall).2
  have hγ : IsQSCircleHomeo γ := ⟨wA_circle_sensePreserving hμ, wA_circle_quasisymmetric hμ⟩
  have hpair := AppB.b8_welding_normalized_pair hμ
  have hnc := (normalizedWeldingExterior_continuous_proper hμ).1
  have hwc (n : ℕ) : Continuous (w n) := ((Polynomial.continuous _).comp hnc).div_const _
  obtain ⟨h1a, h1b⟩ := s5p51_faber_boundary hPQ
  have hsq (n : ℕ) : (Real.sqrt ((n : ℝ) + 1) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (by positivity : (0 : ℝ) < n + 1)).ne'
  have hsq2 (n : ℕ) : (Real.sqrt ((n : ℝ) + 1) : ℂ) ^ 2 = (n : ℂ) + 1 := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by positivity)]
    push_cast
    ring
  have hB4 : IsBoundedMat (B4 b) := pgb_bounded hμ (by simp [b])
  have hHC (n : ℕ) : w n ∈ HC := by
    refine ⟨((hwc n).comp (by fun_prop)).intervalIntegrable _ _, ?_⟩
    apply Summable.of_add_one_of_neg_add_one
    · apply summable_of_ne_finset_zero (s := {n})
      intro k hk
      have hkn : k ≠ n := by simpa using hk
      have h := h1a n k
      unfold kron at h
      rw [if_neg hkn, mul_eq_zero] at h
      rcases h with h | h
      · push_cast at h ⊢
        rw [h, norm_zero]
        ring
      · exact absurd h (hsq k)
    · apply (isBoundedMat_row_isL2 hB4 n).congr
      intro k
      have h := h1b n k
      have hc : circleCoeff (w n) (-((k : ℤ) + 1)) = B4 b n k / (Real.sqrt ((k : ℝ) + 1) : ℂ) := by
        rw [← h]
        field_simp [hsq k]
        rfl
      push_cast
      rw [hc, norm_div, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _), div_pow,
        Real.sq_sqrt (by positivity : (0 : ℝ) ≤ k + 1)]
      rw [abs_neg, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (k : ℝ) + 1)]
      field_simp
  refine ⟨fun n => ⟨hHC n, (hwc n).continuousOn⟩, fun N k => ?_⟩
  obtain ⟨F, hFc, hFf, hFw⟩ := s5p51_weld_ext hμ
  set H : ℂ → ℂ := fun z => (P (N + 1)).eval (F z) / (Real.sqrt ((N : ℝ) + 1) : ℂ) with hH
  have hHc : ContinuousOn H (closedBall 0 1) :=
    ((Polynomial.continuous _).comp_continuousOn hFc).div_const _
  have ha : ∀ ζ ∈ unitDisc, HasSum (fun q : ℕ => (((N + 1 : ℕ) : ℂ) * grunsky (fsans μ) (gsans μ) (N + 1) (-(q : ℤ)) /
      (Real.sqrt ((N : ℝ) + 1) : ℂ)) * ζ ^ q) (H ζ) := by
    intro ζ hζ
    have h := (s5p51_faber_disc hpair hPQ N ζ hζ).div_const (Real.sqrt ((N : ℝ) + 1) : ℂ)
    simp only [hH, hFf hζ]
    convert h using 1
    funext q
    ring
  have hcomp {j : ℤ} (hj : j ≠ 0) : circleCoeff (piHat γ (w N)) j = circleCoeff H j := by
    rw [s5ns_piHat_coeff hγ (hwc N).continuousOn hj]
    apply s5qc_coeff_congr
    intro z hz
    simp only [Function.comp_apply, hH, w]
    rw [hFw z hz]
  constructor
  · rw [hcomp (by omega), s5p51_holo_coeff hHc ha, if_pos (by omega)]
    have ht : ((k : ℤ) + 1).toNat = k + 1 := by omega
    rw [ht]
    unfold B3
    have hprod : (Real.sqrt (((N : ℝ) + 1) * ((k : ℝ) + 1)) : ℂ) =
        (Real.sqrt ((N : ℝ) + 1) : ℂ) * (Real.sqrt ((k : ℝ) + 1) : ℂ) := by
      rw [Real.sqrt_mul (by positivity)]
      push_cast
      ring
    push_cast
    rw [hprod]
    have hn2 := hsq2 N
    field_simp [hsq N]
    rw [← hn2]
  · rw [hcomp (by omega), s5p51_holo_coeff hHc ha, if_neg (by omega)]

/-- S5. The block identities `𝔄 + 𝔅B₄ = B₃ᵗ` and `𝔅̄ + 𝔄̄B₄ = 0`. -/
theorem s5p51_blocks (p : T1) :
    let μ : LinfStar := (Quotient.out p : LinfStarBall)
    let γ := wA μ
    let b := grunsky (fsans μ) (gsans μ)
    ∀ k n : ℕ, matA γ k n + (∑' j, matB γ k j * B4 b n j) = B3 b n k ∧
      conj (matB γ k n) + (∑' j, conj (matA γ k j) * B4 b n j) = 0 := by
  intro μ γ b k n
  have hμ : μ ∈ LinfStarBall := (Quotient.out p : LinfStarBall).2
  have hγ : IsQSCircleHomeo γ := ⟨wA_circle_sensePreserving hμ, wA_circle_quasisymmetric hμ⟩
  have hpair := AppB.b8_welding_normalized_pair hμ
  obtain ⟨P, Q, hPQ⟩ := faber_exists hpair
  obtain ⟨h1a, h1b⟩ := s5p51_faber_boundary hPQ
  obtain ⟨hw, hcoef⟩ := s5p51_composed hPQ
  obtain ⟨C, hC⟩ := s5ns_bound hγ
  set wn : ℂ → ℂ := fun z => (P (n + 1)).eval (normalizedWeldingExterior μ z) / Real.sqrt (n + 1) with hwn
  have hP := (hC wn (hw n).1 (hw n).2).1
  have hT := s5mab_compat hγ (hw n).1 (hw n).2 hP
  obtain ⟨hA, hB, hBc, hAc⟩ := s5ca_bounded_matrices hγ
  have hb := s5ca_completed_blocks hγ (s5ca_coordinates wn (hw n).1).1 (s5ca_coordinates wn (hw n).1).2
  rw [Prod.mk.eta, hT] at hb
  have hx (j : ℕ) : (s5ca_coordinates wn (hw n).1).1 j = kron j n := by
    change s5ca_coeff wn false j = kron j n
    simp only [s5ca_coeff, Bool.false_eq_true, ite_false]
    rw [mul_comm]
    exact h1a n j
  have hy (j : ℕ) : (s5ca_coordinates wn (hw n).1).2 j = B4 b n j := by
    change s5ca_coeff wn true j = B4 b n j
    simp only [s5ca_coeff, ite_true]
    rw [mul_comm]
    exact h1b n j
  have hsumk (Z : ℕ → ℕ → ℂ) : (∑' j, Z k j * kron j n) = Z k n := by
    rw [tsum_eq_single n (fun j hj => by simp [kron, hj])]
    simp [kron]
  constructor
  · have h := congrArg (fun u : ell2 × ell2 => u.1 k) hb
    simp only [lp.coeFn_add, Pi.add_apply, pmb_apply hA, pmb_apply hB, matApply, hx, hy] at h
    rw [hsumk] at h
    rw [← h]
    change s5ca_coeff (piHat γ wn) false k = B3 b n k
    simp only [s5ca_coeff, Bool.false_eq_true, ite_false]
    rw [mul_comm]
    exact (hcoef n k).1
  · have h := congrArg (fun u : ell2 × ell2 => u.2 k) hb
    simp only [lp.coeFn_add, Pi.add_apply, pmb_apply hBc, pmb_apply hAc, matApply, hx, hy] at h
    rw [hsumk (fun a c => conj (matB γ a c))] at h
    rw [← h]
    change s5ca_coeff (piHat γ wn) true k = 0
    simp only [s5ca_coeff, ite_true]
    rw [(hcoef n k).2, mul_zero]

/-- S6. The column relations of `Π̂(γ)`, from `Π̂(γ⁻¹)Π̂(γ) = 1`. -/
theorem s5p51_cols {γ : ℂ → ℂ} (hγ : IsQSCircleHomeo γ) :
    (∀ m n, (∑' k, conj (matA γ k m) * matA γ k n) - (∑' k, matB γ k m * conj (matB γ k n)) = kron m n) ∧
      ∀ m n, (∑' k, conj (matA γ k m) * matB γ k n) = ∑' k, matB γ k m * conj (matA γ k n) := by
  have hG := s5mab_inv_qs hγ
  have hinv := s5mab_inv_mat hγ
  obtain ⟨h1, h2⟩ := s5mab_rows hG
  constructor
  · intro m n
    have h := h1 m n
    unfold mulAdj at h
    simp only [(hinv _ _).1, (hinv _ _).2, Complex.conj_conj, map_neg, neg_mul_neg] at h
    exact h
  · intro m n
    have h := h2 m n
    simp only [(hinv _ _).1, (hinv _ _).2, mul_neg, neg_mul, tsum_neg, neg_inj] at h
    rw [h]

/-- S7. Boundedness, symmetry, the unitarity entry `B₁B₃* + B₂B₄* = 0`, and the bounded inverse of `B₂`. -/
theorem s5p51_grunsky_facts {μ : LinfStar} (hμ : μ ∈ LinfStarBall) :
    let b := grunsky (fsans μ) (gsans μ)
    IsBoundedMat (B1 b) ∧ IsBoundedMat (B2 b) ∧ IsBoundedMat (B3 b) ∧ IsBoundedMat (B4 b) ∧
      (∀ m n, B4 b m n = B4 b n m ∧ B3 b m n = B2 b n m) ∧
      (∀ m n, mulAdj (B1 b) (B3 b) m n + mulAdj (B2 b) (B4 b) m n = 0) ∧
      ∃ R : ℕ → ℕ → ℂ, IsBoundedMat R ∧ (∀ m n, mulMat (B2 b) R m n = kron m n) ∧
        ∀ m n, mulMat R (B2 b) m n = kron m n := by
  intro b
  have hpair := AppB.b8_welding_normalized_pair hμ
  have hnull := r22_complement_null hμ
  have hb1 : IsBoundedMat (B1 b) := pgb_bounded hμ (by simp [b])
  have hb2 : IsBoundedMat (B2 b) := pgb_bounded hμ (by simp [b])
  have hb3 : IsBoundedMat (B3 b) := pgb_bounded hμ (by simp [b])
  have hb4 : IsBoundedMat (B4 b) := pgb_bounded hμ (by simp [b])
  obtain ⟨hsym, -⟩ := grunsky_unitary hpair hnull
  obtain ⟨-, -, hu, -⟩ := gop_blocks hpair hnull
  refine ⟨hb1, hb2, hb3, hb4, fun m n => ⟨(hsym m n).2.1, (hsym m n).2.2⟩, fun m n => ?_,
    pgb_inverse_matrix hb2 (pgb_mixed_isUnit hμ).1⟩
  have h := congrArg (fun T : ell2 →L[ℂ] ell2 => T (lp.single 2 n 1 : ell2) m) hu
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.zero_apply, lp.coeFn_add, Pi.add_apply,
    lp.coeFn_zero, Pi.zero_apply] at h
  rw [gop_mul_adjoint_entry (isBoundedMat_row_isL2 hb1) (pmb_partial_bound hb1) (isBoundedMat_row_isL2 hb3)
      (pmb_partial_bound hb3),
    gop_mul_adjoint_entry (isBoundedMat_row_isL2 hb2) (pmb_partial_bound hb2) (isBoundedMat_row_isL2 hb4)
      (pmb_partial_bound hb4)] at h
  exact h

/-- The conjugate transpose of a bounded matrix is bounded (it is the matrix of the adjoint). -/
theorem s5p51_adj_bounded {X : ℕ → ℕ → ℂ} (hX : IsBoundedMat X) : IsBoundedMat (fun m n => conj (X n m)) := by
  apply pmb_of_operator (ContinuousLinearMap.adjoint (gopOp X))
  intro m n
  rw [gop_adjoint_apply (isBoundedMat_row_isL2 hX) (pmb_partial_bound hX)]
  rw [tsum_eq_single n (fun k hk => by rw [gop_single_apply, if_neg hk, mul_zero]), gop_single_apply, if_pos rfl,
    mul_one]

/-- A matrix identity `XY = Z` between bounded matrices, as an operator identity. -/
theorem s5p51_op_mul {X Y Z : ℕ → ℕ → ℂ} (hX : IsBoundedMat X) (hY : IsBoundedMat Y) (hZ : IsBoundedMat Z)
    (h : ∀ m n, mulMat X Y m n = Z m n) : gopOp X * gopOp Y = gopOp Z :=
  gop_ext fun m n => by rw [pmb_mul_entry hX hY, pmb_entry hZ, h]

/-- A matrix identity `XY = I` between bounded matrices, as an operator identity. -/
theorem s5p51_op_one {X Y : ℕ → ℕ → ℂ} (hX : IsBoundedMat X) (hY : IsBoundedMat Y)
    (h : ∀ m n, mulMat X Y m n = kron m n) : gopOp X * gopOp Y = 1 :=
  gop_ext fun m n => by rw [pmb_mul_entry hX hY, h, ContinuousLinearMap.one_apply, gop_single_apply]; rfl

/-- Back from an operator identity `XY = I` to the entries. -/
theorem s5p51_one_entry {X Y : ℕ → ℕ → ℂ} (hX : IsBoundedMat X) (hY : IsBoundedMat Y)
    (h : gopOp X * gopOp Y = 1) (m n : ℕ) : mulMat X Y m n = kron m n := by
  rw [← pmb_mul_entry hX hY, h, ContinuousLinearMap.one_apply, gop_single_apply]
  rfl

/-- S8. The matrix algebra of Proposition 5.1. -/
theorem s5p51_algebra {A B B1 B2 B3 B4 : ℕ → ℕ → ℂ} (hA : IsBoundedMat A) (hB : IsBoundedMat B)
    (hAc : IsBoundedMat fun m n => conj (A m n)) (hBc : IsBoundedMat fun m n => conj (B m n))
    (h1 : IsBoundedMat B1) (h2 : IsBoundedMat B2) (h3 : IsBoundedMat B3) (h4 : IsBoundedMat B4)
    (hsym : ∀ m n, B4 m n = B4 n m ∧ B3 m n = B2 n m)
    (hunit : ∀ m n, mulAdj B1 B3 m n + mulAdj B2 B4 m n = 0)
    (hrow : ∀ m n, (∑' k, A m k * B n k) = ∑' k, B m k * A n k)
    (hcol1 : ∀ m n, (∑' k, conj (A k m) * A k n) - (∑' k, B k m * conj (B k n)) = kron m n)
    (hcol2 : ∀ m n, (∑' k, conj (A k m) * B k n) = ∑' k, B k m * conj (A k n))
    (hinv : ∃ R : ℕ → ℕ → ℂ, IsBoundedMat R ∧ (∀ m n, mulMat B2 R m n = kron m n) ∧
      ∀ m n, mulMat R B2 m n = kron m n)
    (hblk : ∀ k n : ℕ, A k n + (∑' j, B k j * B4 n j) = B3 n k ∧
      conj (B k n) + (∑' j, conj (A k j) * B4 n j) = 0) :
    (∀ m n, (∑' k, conj (A k m) * B2 k n) = kron m n ∧ (∑' k, B2 m k * conj (A n k)) = kron m n) ∧
      (∀ m n, (∑' k, B3 m k * conj (A k n)) = kron m n ∧ (∑' k, conj (A m k) * B3 k n) = kron m n) ∧
      (∀ m n, (∑' k, conj (A k m) * B1 k n) = B n m) ∧
      ∀ m n, B4 m n = -∑' k, conj (B k m) * B2 k n := by
  obtain ⟨R, hR, hB2R, hRB2⟩ := hinv
  have hAt' : IsBoundedMat fun m n => A n m := by
    have h := s5p51_adj_bounded hAc
    simp only [Complex.conj_conj] at h
    exact h
  have hBt' : IsBoundedMat fun m n => B n m := by
    have h := s5p51_adj_bounded hBc
    simp only [Complex.conj_conj] at h
    exact h
  -- auxiliary bounded matrices
  set Aa : ℕ → ℕ → ℂ := fun m n => conj (A n m) with hAa
  set At : ℕ → ℕ → ℂ := fun m n => A n m with hAt
  set Bt : ℕ → ℕ → ℂ := fun m n => B n m with hBt
  set Ac : ℕ → ℕ → ℂ := fun m n => conj (A m n) with hAcd
  set Bc : ℕ → ℕ → ℂ := fun m n => conj (B m n) with hBcd
  set B2s : ℕ → ℕ → ℂ := fun m n => conj (B2 n m) with hB2s
  set B2c : ℕ → ℕ → ℂ := fun m n => conj (B2 m n) with hB2c
  set B4c : ℕ → ℕ → ℂ := fun m n => conj (B4 m n) with hB4c
  have hAa' : IsBoundedMat Aa := s5p51_adj_bounded hA
  have hB2s' : IsBoundedMat B2s := s5p51_adj_bounded h2
  have hB2c' : IsBoundedMat B2c := by
    have h := s5p51_adj_bounded h3
    have he : (fun m n => conj (B3 n m)) = B2c := by
      funext m n
      rw [(hsym n m).2]
    rw [he] at h
    exact h
  have hB4c' : IsBoundedMat B4c := by
    have h := s5p51_adj_bounded h4
    have he : (fun m n => conj (B4 n m)) = B4c := by
      funext m n
      rw [(hsym n m).1]
    rw [he] at h
    exact h
  -- operator relations
  have hsub {X Y X' Y' : ℕ → ℕ → ℂ} (hX : IsBoundedMat X) (hY : IsBoundedMat Y) (hX' : IsBoundedMat X')
      (hY' : IsBoundedMat Y') (m n : ℕ) :
      (gopOp X * gopOp Y - gopOp X' * gopOp Y') (lp.single 2 n 1 : ell2) m = mulMat X Y m n - mulMat X' Y' m n := by
    rw [ContinuousLinearMap.sub_apply, lp.coeFn_sub, Pi.sub_apply, pmb_mul_entry hX hY, pmb_mul_entry hX' hY']
  have hadd {X Y Z : ℕ → ℕ → ℂ} (hX : IsBoundedMat X) (hY : IsBoundedMat Y) (hZ : IsBoundedMat Z) (m n : ℕ) :
      (gopOp X + gopOp Y * gopOp Z) (lp.single 2 n 1 : ell2) m = X m n + mulMat Y Z m n := by
    rw [ContinuousLinearMap.add_apply, lp.coeFn_add, Pi.add_apply, pmb_entry hX, pmb_mul_entry hY hZ]
  have rcol1 : gopOp Aa * gopOp A - gopOp Bt * gopOp Bc = 1 := gop_ext fun m n => by
    rw [hsub hAa' hA hBt' hBc, ContinuousLinearMap.one_apply, gop_single_apply]
    exact hcol1 m n
  have rcol2 : gopOp Aa * gopOp B = gopOp Bt * gopOp Ac := gop_ext fun m n => by
    rw [pmb_mul_entry hAa' hB, pmb_mul_entry hBt' hAc]
    exact hcol2 m n
  have rrow : gopOp A * gopOp Bt = gopOp B * gopOp At := gop_ext fun m n => by
    rw [pmb_mul_entry hA hBt', pmb_mul_entry hB hAt']
    exact hrow m n
  have rblk1 : gopOp B2 = gopOp A + gopOp B * gopOp B4 := gop_ext fun m n => by
    rw [hadd hA hB h4, pmb_entry h2, ← (hsym n m).2, ← (hblk m n).1]
    congr 1
    apply tsum_congr
    intro j
    rw [(hsym n j).1]
  have rblk2 : gopOp Bc + gopOp Ac * gopOp B4 = 0 := gop_ext fun m n => by
    rw [hadd hBc hAc h4, ContinuousLinearMap.zero_apply, lp.coeFn_zero, Pi.zero_apply, ← (hblk m n).2]
    congr 1
    apply tsum_congr
    intro j
    rw [(hsym n j).1]
  have runit : gopOp B1 * gopOp B2c + gopOp B2 * gopOp B4c = 0 := gop_ext fun m n => by
    rw [ContinuousLinearMap.add_apply, lp.coeFn_add, Pi.add_apply, pmb_mul_entry h1 hB2c', pmb_mul_entry h2 hB4c',
      ContinuousLinearMap.zero_apply, lp.coeFn_zero, Pi.zero_apply, ← hunit m n]
    unfold mulMat mulAdj
    congr 1 <;> apply tsum_congr <;> intro k
    · rw [(hsym n k).2]
    · rw [(hsym n k).1]
  have rR1 : gopOp B2 * gopOp R = 1 := s5p51_op_one h2 hR hB2R
  have rR2 : gopOp R * gopOp B2 = 1 := s5p51_op_one hR h2 hRB2
  -- clause 1
  have g1a : gopOp Aa * gopOp B2 = 1 := by
    have hz : gopOp Bt * gopOp Bc + gopOp Bt * (gopOp Ac * gopOp B4) = 0 := by rw [← mul_add, rblk2, mul_zero]
    calc gopOp Aa * gopOp B2 = (gopOp Aa * gopOp A - gopOp Bt * gopOp Bc) +
          (gopOp Bt * gopOp Bc + gopOp Bt * (gopOp Ac * gopOp B4)) := by
          rw [rblk1, mul_add, ← mul_assoc, rcol2, mul_assoc]; abel
      _ = 1 := by rw [rcol1, hz, add_zero]
  have hAaR : gopOp Aa = gopOp R := by
    calc gopOp Aa = gopOp Aa * (gopOp B2 * gopOp R) := by rw [rR1, mul_one]
      _ = gopOp R := by rw [← mul_assoc, g1a, one_mul]
  have g1b : gopOp B2 * gopOp Aa = 1 := by rw [hAaR, rR1]
  have e1a := s5p51_one_entry hAa' h2 g1a
  have e1b := s5p51_one_entry h2 hAa' g1b
  have c1 : ∀ m n, (∑' k, conj (A k m) * B2 k n) = kron m n ∧ (∑' k, B2 m k * conj (A n k)) = kron m n :=
    fun m n => ⟨e1a m n, e1b m n⟩
  -- clause 2
  have c2 : ∀ m n, (∑' k, B3 m k * conj (A k n)) = kron m n ∧ (∑' k, conj (A m k) * B3 k n) = kron m n := by
    intro m n
    constructor
    · have h := e1a n m
      unfold kron at h ⊢
      unfold mulMat at h
      rw [show (if m = n then (1 : ℂ) else 0) = if n = m then 1 else 0 by simp [eq_comm], ← h]
      apply tsum_congr
      intro k
      rw [(hsym m k).2]
      ring
    · have h := e1b n m
      unfold kron at h ⊢
      unfold mulMat at h
      rw [show (if m = n then (1 : ℂ) else 0) = if n = m then 1 else 0 by simp [eq_comm], ← h]
      apply tsum_congr
      intro k
      rw [(hsym k n).2]
      ring
  -- clause 4
  have rB3Ac : gopOp B3 * gopOp Ac = 1 := s5p51_op_one h3 hAc fun m n => (c2 m n).1
  have rB4 : gopOp B4 + gopOp B3 * gopOp Bc = 0 := by
    calc gopOp B4 + gopOp B3 * gopOp Bc = gopOp B3 * (gopOp Bc + gopOp Ac * gopOp B4) := by
          rw [mul_add, ← mul_assoc, rB3Ac, one_mul, add_comm]
      _ = 0 := by rw [rblk2, mul_zero]
  have e4 (m n : ℕ) : B4 m n = -mulMat B3 Bc m n := by
    have h := congrArg (fun T : ell2 →L[ℂ] ell2 => T (lp.single 2 n 1 : ell2) m) rB4
    simp only at h
    rw [hadd h4 h3 hBc, ContinuousLinearMap.zero_apply, lp.coeFn_zero, Pi.zero_apply] at h
    exact eq_neg_of_add_eq_zero_left h
  have c4 : ∀ m n, B4 m n = -∑' k, conj (B k m) * B2 k n := by
    intro m n
    rw [(hsym m n).1, e4 n m]
    unfold mulMat
    congr 1
    apply tsum_congr
    intro k
    rw [(hsym n k).2]
    ring
  -- clause 3
  have rB2cAt : gopOp B2c * gopOp At = 1 := s5p51_op_one hB2c' hAt' fun m n => by
    have h := congrArg conj (e1b m n)
    simp only [mulMat, kron, hAa, Complex.conj_tsum, map_mul, Complex.conj_conj] at h
    simp only [mulMat, kron, hB2c, hAt]
    rw [h]
    split_ifs <;> simp
  have rB2sA : gopOp B2s * gopOp A = 1 := s5p51_op_one hB2s' hA fun m n => by
    have h := congrArg conj (e1a n m)
    simp only [mulMat, kron, hAa, Complex.conj_tsum, map_mul, Complex.conj_conj] at h
    simp only [mulMat, kron, hB2s]
    rw [show (∑' k, conj (B2 k m) * A k n) = ∑' k, A k n * conj (B2 k m) from tsum_congr fun k => mul_comm _ _, h]
    by_cases hmn : m = n
    · subst hmn
      simp
    · simp [hmn, Ne.symm hmn]
  have rB4c : gopOp B4c + gopOp B2s * gopOp B = 0 := gop_ext fun m n => by
    rw [hadd hB4c' hB2s' hB, ContinuousLinearMap.zero_apply, lp.coeFn_zero, Pi.zero_apply]
    show conj (B4 m n) + mulMat B2s B m n = 0
    rw [e4 m n, map_neg, neg_add_eq_zero]
    unfold mulMat
    rw [Complex.conj_tsum]
    apply tsum_congr
    intro k
    simp only [hBcd, hB2s, map_mul, Complex.conj_conj, (hsym m k).2]
  have rB1 : gopOp B1 = gopOp B2 * gopOp B2s * gopOp B * gopOp At := by
    have hz2 : gopOp B2 * gopOp B4c + gopOp B2 * (gopOp B2s * gopOp B) = 0 := by rw [← mul_add, rB4c, mul_zero]
    have hu : gopOp B1 * gopOp B2c = gopOp B2 * (gopOp B2s * gopOp B) :=
      (eq_neg_of_add_eq_zero_left runit).trans (eq_neg_of_add_eq_zero_right hz2).symm
    calc gopOp B1 = gopOp B1 * (gopOp B2c * gopOp At) := by rw [rB2cAt, mul_one]
      _ = gopOp B2 * gopOp B2s * gopOp B * gopOp At := by rw [← mul_assoc, hu]; simp only [mul_assoc]
  have g3 : gopOp Aa * gopOp B1 = gopOp Bt := by
    calc gopOp Aa * gopOp B1 = (gopOp Aa * gopOp B2) * gopOp B2s * (gopOp B * gopOp At) := by
          rw [rB1]; simp only [mul_assoc]
      _ = gopOp B2s * (gopOp A * gopOp Bt) := by rw [g1a, one_mul, rrow]
      _ = gopOp Bt := by rw [← mul_assoc, rB2sA, one_mul]
  have c3 : ∀ m n, (∑' k, conj (A k m) * B1 k n) = B n m := by
    intro m n
    have h := congrArg (fun T : ell2 →L[ℂ] ell2 => T (lp.single 2 n 1 : ell2) m) g3
    simp only at h
    rw [pmb_mul_entry hAa' h1, pmb_entry hBt'] at h
    exact h
  exact ⟨c1, c2, c3, c4⟩

/-- **Proposition 5.1** (TT:5564–5610). For `[μ] ∈ T(1)`, with `γ = w_μ` and the Grunsky matrices `B_l` of
`(𝖿^μ, 𝗀_μ)`:
- `B₂ = (𝔄*)⁻¹`;
- `B₃ = 𝔄̄⁻¹`;
- `𝔄*B₁ = 𝔅ᵗ`, i.e. `B₁ = 𝔅𝔄̄⁻¹`;
- `B₄ = -𝔅*(𝔄*)⁻¹ = -𝔅*B₂`. -/
theorem s5p51_prop_5_1 (p : T1) :
    let μ : LinfStar := (Quotient.out p : LinfStarBall)
    let γ := wA μ
    let b := grunsky (fsans μ) (gsans μ)
    (∀ m n, (∑' k, conj (matA γ k m) * B2 b k n) = kron m n ∧ (∑' k, B2 b m k * conj (matA γ n k)) = kron m n) ∧
      (∀ m n, (∑' k, B3 b m k * conj (matA γ k n)) = kron m n ∧ (∑' k, conj (matA γ m k) * B3 b k n) = kron m n) ∧
      (∀ m n, (∑' k, conj (matA γ k m) * B1 b k n) = matB γ n m) ∧
      ∀ m n, B4 b m n = -∑' k, conj (matB γ k m) * B2 b k n := by
  intro μ γ b
  have hμ : μ ∈ LinfStarBall := (Quotient.out p : LinfStarBall).2
  have hγ : IsQSCircleHomeo γ := ⟨wA_circle_sensePreserving hμ, wA_circle_quasisymmetric hμ⟩
  obtain ⟨hA, hB, hBc, hAc⟩ := s5ca_bounded_matrices hγ
  obtain ⟨h1, h2, h3, h4, hsym, hunit, hinv⟩ := s5p51_grunsky_facts hμ
  exact s5p51_algebra hA hB hAc hBc h1 h2 h3 h4 hsym hunit (s5mab_rows hγ).2 (s5p51_cols hγ).1
    (s5p51_cols hγ).2 hinv (s5p51_blocks p)

/-- **Proposition 5.1** (TT:5564–5610). For `[μ] ∈ T(1)`, with `γ = w_μ` and the Grunsky matrices `B_l` of
`(𝖿^μ, 𝗀_μ)`:
- `B₂ = (𝔄*)⁻¹`;
- `B₃ = 𝔄̄⁻¹`;
- `𝔄*B₁ = 𝔅ᵗ`, i.e. `B₁ = 𝔅𝔄̄⁻¹`;
- `B₄ = -𝔅*(𝔄*)⁻¹ = -𝔅*B₂`. -/
theorem prop_5_1 (p : T1) :
    let μ : LinfStar := (Quotient.out p : LinfStarBall)
    let γ := wA μ
    let b := grunsky (fsans μ) (gsans μ)
    (∀ m n, (∑' k, conj (matA γ k m) * B2 b k n) = kron m n ∧ (∑' k, B2 b m k * conj (matA γ n k)) = kron m n) ∧
      (∀ m n, (∑' k, B3 b m k * conj (matA γ k n)) = kron m n ∧ (∑' k, conj (matA γ m k) * B3 b k n) = kron m n) ∧
      (∀ m n, (∑' k, conj (matA γ k m) * B1 b k n) = matB γ n m) ∧
      ∀ m n, B4 b m n = -∑' k, conj (matB γ k m) * B2 b k n := by
  exact s5p51_prop_5_1 p

end TakhtajanTeo.Ch2
