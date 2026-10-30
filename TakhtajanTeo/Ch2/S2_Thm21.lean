import TakhtajanTeo.Ch2.S2_Remark22
import TakhtajanTeo.Ch2.S2_MixedB

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal ComplexConjugate Classical Real

noncomputable section

namespace TakhtajanTeo

open LiZhongQC

namespace Ch2

/-! ## `thm_2_1`: Laurent energy of a regular part plus a finite principal part -/

/-- Circle energy of `Hh + ∑_{k<m} β_k u^{-(k+1)}` with `Hh` a power series on `𝔻`. -/
theorem t21_energy {Hh : ℂ → ℂ} {cc β : ℕ → ℂ} {m : ℕ}
    (hs : ∀ z ∈ unitDisc, HasSum (fun n : ℕ => cc n * z ^ n) (Hh z)) {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) :
    Summable (fun j : ℕ => ((j + 1 : ℕ) : ℝ) * (‖cc (j + 1)‖ ^ 2 * ρ ^ (2 * (j + 1)))) ∧
      (∫ θ in (0 : ℝ)..2 * π,
          conj ((fun u : ℂ => Hh u + ∑ k ∈ Finset.range m, β k * u ^ (-((k : ℤ) + 1))) (circleMap 0 ρ θ)) *
            deriv (fun u : ℂ => Hh u + ∑ k ∈ Finset.range m, β k * u ^ (-((k : ℤ) + 1))) (circleMap 0 ρ θ) *
              circleMap 0 ρ θ) =
        2 * π * (((∑' j : ℕ, ((j + 1 : ℕ) : ℝ) * (‖cc (j + 1)‖ ^ 2 * ρ ^ (2 * (j + 1))) -
          ∑ k ∈ Finset.range m, ((k + 1 : ℕ) : ℝ) * (‖β k‖ ^ 2 * (ρ ^ (2 * (k + 1)))⁻¹) : ℝ) : ℂ)) := by
  set F : ℕ → ℂ := cc with hF
  set G : ℕ → ℂ := fun n => if 1 ≤ n ∧ n ≤ m then β (n - 1) else 0 with hG
  set d : ℤ → ℂ := fun n => if 0 ≤ n then F n.toNat else G (-n).toNat with hd
  obtain ⟨r1, hr1⟩ : ∃ r1 : ℝ, r1 = ρ / 2 := ⟨_, rfl⟩
  obtain ⟨r2, hr2⟩ : ∃ r2 : ℝ, r2 = (ρ + 1) / 2 := ⟨_, rfl⟩
  have hr1p : 0 < r1 := by rw [hr1]; positivity
  have hr1ρ : r1 < ρ := by rw [hr1]; linarith
  have hρr2 : ρ < r2 := by rw [hr2]; linarith
  have hr2one : r2 < 1 := by rw [hr2]; linarith
  have hdpos : ∀ n : ℕ, d (n : ℤ) = F n := fun n => by simp [hd]
  have hdneg : ∀ n : ℕ, d (-((n : ℤ) + 1)) = G (n + 1) := fun n => by
    have h1 : ¬ (0 : ℤ) ≤ -((n : ℤ) + 1) := by omega
    have h2 : (-(-((n : ℤ) + 1))).toNat = n + 1 := by omega
    simp only [hd, h1, if_false, h2]
  have hGβ : ∀ n : ℕ, G (n + 1) = if n < m then β n else 0 := fun n => by
    simp only [hG]
    by_cases hn : n < m
    · rw [if_pos ⟨by omega, by omega⟩, if_pos hn]; rfl
    · rw [if_neg (by omega), if_neg hn]
  have hLaurent : ∀ w : ℂ, r1 < ‖w‖ → ‖w‖ < r2 →
      (Hh w + ∑ k ∈ Finset.range m, β k * w ^ (-((k : ℤ) + 1))) = ∑' n : ℤ, d n * w ^ n := by
    intro w hw1 hw2
    have hwD : w ∈ unitDisc := mem_ball_zero_iff.mpr (hw2.trans hr2one)
    have hFsum : HasSum (fun n : ℕ => F n * w ^ n) (Hh w) := hs w hwD
    have hGsum : HasSum (fun n : ℕ => G (n + 1) * w ^ (-((n : ℤ) + 1)))
        (∑ k ∈ Finset.range m, β k * w ^ (-((k : ℤ) + 1))) := by
      have hh : HasSum (fun n : ℕ => G (n + 1) * w ^ (-((n : ℤ) + 1)))
          (∑ n ∈ Finset.range m, G (n + 1) * w ^ (-((n : ℤ) + 1))) :=
        hasSum_sum_of_ne_finset_zero (fun n hn => by
          rw [hGβ, if_neg (by simpa using hn), zero_mul])
      convert hh using 1
      refine Finset.sum_congr rfl (fun k hk => ?_)
      rw [hGβ, if_pos (by simpa using hk)]
    rw [(mg_hasSum_int F G hFsum hGsum).tsum_eq]
  have hpos : Summable (fun n : ℕ => ‖d n‖ * r2 ^ n) := by
    have hr2D : ((r2 : ℝ) : ℂ) ∈ unitDisc :=
      mem_ball_zero_iff.mpr (by rw [Complex.norm_real, Real.norm_of_nonneg (by linarith)]; exact hr2one)
    have hn := summable_norm_iff.mpr (hs _ hr2D).summable
    refine hn.congr (fun j => ?_)
    rw [hdpos, norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg (by linarith)]
  have hneg : Summable (fun n : ℕ => ‖d (-(n : ℤ))‖ * (r1 ^ n)⁻¹) := by
    refine summable_of_ne_finset_zero (s := Finset.range (m + 1)) (fun n hn => ?_)
    have hn' : m + 1 ≤ n := by simpa using hn
    have h1 : ¬ (0 : ℤ) ≤ -(n : ℤ) := by omega
    have h2 : (-(-(n : ℤ))).toNat = n := by omega
    have : d (-(n : ℤ)) = 0 := by
      simp only [hd, h1, if_false, h2]
      simp only [hG]
      rw [if_neg (by omega)]
    rw [this, norm_zero, zero_mul]
  have hE := mg_circle_energy (H := fun u => Hh u + ∑ k ∈ Finset.range m, β k * u ^ (-((k : ℤ) + 1))) d
    hr1p hr1ρ hρr2 hpos hneg hLaurent
  obtain ⟨hgs, hTc⟩ := mg_energy_real hr1p hr1ρ hρr2 hpos hneg
  obtain ⟨hsp, hsn, hsplit⟩ := mg_energy_split hr1p hr1ρ hρr2 hpos hneg
  have e1 : (fun j : ℕ => ((j + 1 : ℕ) : ℝ) * (‖d ((j + 1 : ℕ) : ℤ)‖ ^ 2 * ρ ^ (2 * (j + 1)))) =
      fun j : ℕ => ((j + 1 : ℕ) : ℝ) * (‖cc (j + 1)‖ ^ 2 * ρ ^ (2 * (j + 1))) := by
    funext j; rw [hdpos]
  have e2 : ∀ k : ℕ, d (-((k + 1 : ℕ) : ℤ)) = if k < m then β k else 0 := by
    intro k
    rw [show (-((k + 1 : ℕ) : ℤ)) = -((k : ℤ) + 1) by push_cast; ring, hdneg, hGβ]
  rw [e1] at hsp
  refine ⟨hsp, ?_⟩
  rw [hE, hTc, hsplit, e1]
  congr 3
  rw [tsum_eq_sum (s := Finset.range m) (fun k hk => by
    rw [e2, if_neg (by simpa using hk)]; simp)]
  refine Finset.sum_congr rfl (fun k hk => ?_)
  rw [e2, if_pos (by simpa using hk)]

/-- The circle integral of a negative power vanishes. -/
theorem t21_int_zpow {ρ : ℝ} (hρ0 : 0 < ρ) (k : ℕ) :
    ∫ θ in (0 : ℝ)..2 * π, (circleMap 0 ρ θ) ^ (-((k : ℤ) + 1)) = 0 := by
  have h := g2_circleAverage_zpow hρ0 (-((k : ℤ) + 1))
  rw [if_neg (by omega), Real.circleAverage_def] at h
  have h2 : (2 * π : ℝ) ≠ 0 := by positivity
  have h3 : ((2 * π)⁻¹ : ℝ) • ∫ θ in (0 : ℝ)..2 * π, (circleMap 0 ρ θ) ^ (-((k : ℤ) + 1)) = 0 := by
    simpa [smul_eq_mul] using h
  rcases smul_eq_zero.mp h3 with h4 | h4
  · exact absurd h4 (inv_ne_zero h2)
  · exact h4

/-- The circle integral of `φ(u) u^{-(k+1)}` for a power series `φ` is `2π` times the coefficient. -/
theorem t21_int_phi_zpow {φ : ℂ → ℂ} {c : ℕ → ℂ}
    (hs : ∀ z ∈ unitDisc, HasSum (fun n : ℕ => c n * z ^ n) (φ z)) {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (k : ℕ) :
    ∫ θ in (0 : ℝ)..2 * π, φ (circleMap 0 ρ θ) * (circleMap 0 ρ θ) ^ (-((k : ℤ) + 1)) =
      2 * π * c (k + 1) := by
  obtain ⟨r2, hr2⟩ : ∃ r2 : ℝ, r2 = (ρ + 1) / 2 := ⟨_, rfl⟩
  have hρr2 : ρ < r2 := by rw [hr2]; linarith
  have hr2one : r2 < 1 := by rw [hr2]; linarith
  have hr2D : ((r2 : ℝ) : ℂ) ∈ unitDisc :=
    mem_ball_zero_iff.mpr (by rw [Complex.norm_real, Real.norm_of_nonneg (by linarith)]; exact hr2one)
  have hB : Summable (fun q : ℕ => ‖c q‖ * ρ ^ q) := by
    have hn := summable_norm_iff.mpr (hs _ hr2D).summable
    have hn' : Summable (fun q : ℕ => ‖c q‖ * r2 ^ q) := by
      refine hn.congr (fun j => ?_)
      rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg (by linarith)]
    exact Summable.of_nonneg_of_le (fun q => by positivity)
      (fun q => by gcongr) hn'
  have hcoef := g2_circle_coeff (s := c) (F := φ) hρ0 (k + 1) (B := fun q => ‖c q‖ * ρ ^ q) hB
    (fun q u hu => by
      have hun : ‖u‖ = ρ := by simpa [abs_of_pos hρ0] using hu
      rw [norm_mul, norm_pow, hun])
    (fun u hu => by
      have hun : ‖u‖ = ρ := by simpa [abs_of_pos hρ0] using hu
      exact hs u (mem_ball_zero_iff.mpr (by rw [hun]; exact hρ1)))
  rw [Real.circleAverage_def] at hcoef
  have e : ∀ θ : ℝ, φ (circleMap 0 ρ θ) * (circleMap 0 ρ θ) ^ (-((k : ℤ) + 1)) =
      φ (circleMap 0 ρ θ) / (circleMap 0 ρ θ) ^ (k + 1) := fun θ => by
    rw [zpow_neg, div_eq_mul_inv]
    congr 2
  simp_rw [e]
  have h2 : (2 * π : ℝ) ≠ 0 := by positivity
  have h3 : ∫ θ in (0 : ℝ)..2 * π, φ (circleMap 0 ρ θ) / (circleMap 0 ρ θ) ^ (k + 1) =
      ((2 * π : ℝ)) • ((2 * π)⁻¹ • ∫ θ in (0 : ℝ)..2 * π, φ (circleMap 0 ρ θ) / (circleMap 0 ρ θ) ^ (k + 1)) := by
    rw [smul_smul, mul_inv_cancel₀ h2, one_smul]
  rw [h3, hcoef, Complex.real_smul]
  push_cast
  ring

/-- The boundary term of the log-Green identity for a regular part plus a finite principal part. -/
theorem t21_side {Hr φ : ℂ → ℂ} {cr cφ β : ℕ → ℂ} {m : ℕ}
    (hsr : ∀ z ∈ unitDisc, HasSum (fun n : ℕ => cr n * z ^ n) (Hr z))
    (hsφ : ∀ z ∈ unitDisc, HasSum (fun n : ℕ => cφ n * z ^ n) (φ z)) (hc0 : cφ 0 = 0)
    {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (κ L ε : ℂ) :
    (∫ θ in (0 : ℝ)..2 * π,
        (conj ((fun u : ℂ => Hr u + ∑ k ∈ Finset.range m, β k * u ^ (-((k : ℤ) + 1))) (circleMap 0 ρ θ)) +
            conj κ * (L + φ (circleMap 0 ρ θ))) *
          (ε * (circleMap 0 ρ θ * deriv (fun u : ℂ => Hr u + ∑ k ∈ Finset.range m, β k * u ^ (-((k : ℤ) + 1)))
              (circleMap 0 ρ θ)) + κ)) =
      2 * π * (ε * (((∑' j : ℕ, ((j + 1 : ℕ) : ℝ) * (‖cr (j + 1)‖ ^ 2 * ρ ^ (2 * (j + 1))) -
          ∑ k ∈ Finset.range m, ((k + 1 : ℕ) : ℝ) * (‖β k‖ ^ 2 * (ρ ^ (2 * (k + 1)))⁻¹) : ℝ) : ℂ)) +
        κ * conj (cr 0) -
        ε * conj κ * ∑ k ∈ Finset.range m, ((k + 1 : ℕ) : ℂ) * cφ (k + 1) * β k + conj κ * κ * L) := by
  obtain ⟨hsum, hen⟩ := t21_energy (Hh := Hr) (cc := cr) (β := β) (m := m) hsr hρ0 hρ1
  obtain ⟨Pr, hPr⟩ : ∃ Pr : ℂ → ℂ, ∀ u, Pr u = ∑ k ∈ Finset.range m, β k * u ^ (-((k : ℤ) + 1)) :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨Pd, hPd⟩ : ∃ Pd : ℂ → ℂ, ∀ u, Pd u =
      ∑ k ∈ Finset.range m, β k * (((-((k : ℤ) + 1) : ℤ) : ℂ) * u ^ (-((k : ℤ) + 1) - 1)) :=
    ⟨_, fun _ => rfl⟩
  have hfun : (fun u : ℂ => Hr u + ∑ k ∈ Finset.range m, β k * u ^ (-((k : ℤ) + 1))) =
      fun u => Hr u + Pr u := funext (fun u => by rw [hPr])
  rw [hfun] at hen ⊢
  beta_reduce at hen ⊢
  have hHr := differentiableOn_of_powerSeries hsr
  have hφ := differentiableOn_of_powerSeries hsφ
  have hHr' : DifferentiableOn ℂ (deriv Hr) unitDisc := hHr.deriv isOpen_ball
  have hval0 : ∀ {F : ℂ → ℂ} {c : ℕ → ℂ}, (∀ z ∈ unitDisc, HasSum (fun n : ℕ => c n * z ^ n) (F z)) →
      F 0 = c 0 := by
    intro F c hs
    have h1 := hs 0 (mem_ball_self one_pos)
    have h2 : HasSum (fun n : ℕ => c n * (0 : ℂ) ^ n) (c 0 * (0 : ℂ) ^ 0) :=
      hasSum_single 0 (fun n hn => by simp [hn])
    rw [h1.unique h2]; simp
  have hφ0 : φ 0 = 0 := by rw [hval0 hsφ, hc0]
  have hHr0 : Hr 0 = cr 0 := hval0 hsr
  have hcm : Continuous (fun θ : ℝ => circleMap 0 ρ θ) := continuous_circleMap 0 ρ
  have hcn : ∀ θ : ℝ, circleMap 0 ρ θ ≠ 0 := fun θ => circleMap_ne_center hρ0.ne'
  have hcD : ∀ θ : ℝ, circleMap 0 ρ θ ∈ unitDisc := fun θ =>
    mem_ball_zero_iff.mpr (by rw [norm_circleMap_zero, abs_of_pos hρ0]; exact hρ1)
  have hcont : ∀ F : ℂ → ℂ, ContinuousOn F unitDisc → Continuous (fun θ : ℝ => F (circleMap 0 ρ θ)) :=
    fun F hF => hF.comp_continuous hcm hcD
  have hzp : ∀ k : ℕ, Continuous (fun θ : ℝ => (circleMap 0 ρ θ) ^ (-((k : ℤ) + 1))) := fun k =>
    hcm.zpow₀ _ (fun θ => Or.inl (hcn θ))
  have hcPr : Continuous (fun θ : ℝ => Pr (circleMap 0 ρ θ)) := by
    simp_rw [hPr]
    exact continuous_finset_sum _ (fun k _ => continuous_const.mul (hzp k))
  have hPrd : ∀ u : ℂ, u ≠ 0 → HasDerivAt Pr (Pd u) u := by
    intro u hu
    have : Pr = fun u => ∑ k ∈ Finset.range m, β k * u ^ (-((k : ℤ) + 1)) := funext hPr
    rw [this, hPd]
    refine HasDerivAt.fun_sum (fun k _ => ?_)
    exact (hasDerivAt_zpow (-((k : ℤ) + 1)) u (Or.inl hu)).const_mul (β k)
  have hdĤ : ∀ θ : ℝ, deriv (fun u => Hr u + Pr u) (circleMap 0 ρ θ) =
      deriv Hr (circleMap 0 ρ θ) + Pd (circleMap 0 ρ θ) := by
    intro θ
    have h1 : HasDerivAt Hr (deriv Hr (circleMap 0 ρ θ)) (circleMap 0 ρ θ) :=
      (hHr.differentiableAt (isOpen_ball.mem_nhds (hcD θ))).hasDerivAt
    exact (h1.add (hPrd _ (hcn θ))).deriv
  have hcPd : Continuous (fun θ : ℝ => circleMap 0 ρ θ * Pd (circleMap 0 ρ θ)) := by
    have : (fun θ : ℝ => circleMap 0 ρ θ * Pd (circleMap 0 ρ θ)) =
        fun θ => ∑ k ∈ Finset.range m, β k * (((-((k : ℤ) + 1) : ℤ) : ℂ) * (circleMap 0 ρ θ) ^ (-((k : ℤ) + 1))) := by
      funext θ
      rw [hPd, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      have := hcn θ
      rw [zpow_sub_one₀ this]
      field_simp
    rw [this]
    exact continuous_finset_sum _ (fun k _ => continuous_const.mul (continuous_const.mul (hzp k)))
  have hcPd2 : Continuous (fun θ : ℝ => Pd (circleMap 0 ρ θ)) := by
    simp_rw [hPd]
    exact continuous_finset_sum _ (fun k _ => continuous_const.mul (continuous_const.mul
      (hcm.zpow₀ _ (fun θ => Or.inl (hcn θ)))))
  have hcHr : Continuous (fun θ : ℝ => Hr (circleMap 0 ρ θ)) := hcont _ hHr.continuousOn
  have hcdHr : Continuous (fun θ : ℝ => deriv Hr (circleMap 0 ρ θ)) := hcont _ hHr'.continuousOn
  have hcφ : Continuous (fun θ : ℝ => φ (circleMap 0 ρ θ)) := hcont _ hφ.continuousOn
  have hcĤ : Continuous (fun θ : ℝ => Hr (circleMap 0 ρ θ) + Pr (circleMap 0 ρ θ)) := hcHr.add hcPr
  have hcdĤ : Continuous (fun θ : ℝ => deriv Hr (circleMap 0 ρ θ) + Pd (circleMap 0 ρ θ)) :=
    hcdHr.add hcPd2
  simp_rw [hdĤ] at hen ⊢
  -- the four integrals
  have J1 := hen
  have J2 : ∫ θ in (0 : ℝ)..2 * π, (Hr (circleMap 0 ρ θ) + Pr (circleMap 0 ρ θ)) = 2 * π * cr 0 := by
    rw [intervalIntegral.integral_add (hcHr.intervalIntegrable _ _) (hcPr.intervalIntegrable _ _),
      r22_mean hHr hρ0 hρ1, hHr0]
    have : ∫ θ in (0 : ℝ)..2 * π, Pr (circleMap 0 ρ θ) = 0 := by
      simp_rw [hPr]
      rw [intervalIntegral.integral_finset_sum (fun k _ => (show IntervalIntegrable
        (fun θ : ℝ => β k * (circleMap 0 ρ θ) ^ (-((k : ℤ) + 1))) volume 0 (2 * π) from
          (continuous_const.mul (hzp k)).intervalIntegrable _ _))]
      refine Finset.sum_eq_zero (fun k _ => ?_)
      rw [intervalIntegral.integral_const_mul, t21_int_zpow hρ0, mul_zero]
    rw [this, add_zero]
  have hQ : ∀ θ : ℝ, circleMap 0 ρ θ * Pd (circleMap 0 ρ θ) =
      ∑ k ∈ Finset.range m, β k * (((-((k : ℤ) + 1) : ℤ) : ℂ) * (circleMap 0 ρ θ) ^ (-((k : ℤ) + 1))) := by
    intro θ
    rw [hPd, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    have := hcn θ
    rw [zpow_sub_one₀ this]
    field_simp
  have J3 : ∫ θ in (0 : ℝ)..2 * π, (L + φ (circleMap 0 ρ θ)) *
      (circleMap 0 ρ θ * (deriv Hr (circleMap 0 ρ θ) + Pd (circleMap 0 ρ θ))) =
      2 * π * (-∑ k ∈ Finset.range m, ((k + 1 : ℕ) : ℂ) * cφ (k + 1) * β k) := by
    have hsplit : ∀ θ : ℝ, (L + φ (circleMap 0 ρ θ)) *
        (circleMap 0 ρ θ * (deriv Hr (circleMap 0 ρ θ) + Pd (circleMap 0 ρ θ))) =
        (L + φ (circleMap 0 ρ θ)) * (circleMap 0 ρ θ * deriv Hr (circleMap 0 ρ θ)) +
          ∑ k ∈ Finset.range m, β k * (((-((k : ℤ) + 1) : ℤ) : ℂ)) *
            (L * (circleMap 0 ρ θ) ^ (-((k : ℤ) + 1)) +
              φ (circleMap 0 ρ θ) * (circleMap 0 ρ θ) ^ (-((k : ℤ) + 1))) := by
      intro θ
      have := hQ θ
      calc (L + φ (circleMap 0 ρ θ)) * (circleMap 0 ρ θ * (deriv Hr (circleMap 0 ρ θ) + Pd (circleMap 0 ρ θ)))
          = (L + φ (circleMap 0 ρ θ)) * (circleMap 0 ρ θ * deriv Hr (circleMap 0 ρ θ)) +
            (L + φ (circleMap 0 ρ θ)) * (circleMap 0 ρ θ * Pd (circleMap 0 ρ θ)) := by ring
        _ = _ := by
          rw [this, Finset.mul_sum]
          congr 1
          refine Finset.sum_congr rfl (fun k _ => ?_)
          ring
    simp_rw [hsplit]
    have hcF : Continuous (fun θ : ℝ => (L + φ (circleMap 0 ρ θ)) *
        (circleMap 0 ρ θ * deriv Hr (circleMap 0 ρ θ))) :=
      (continuous_const.add hcφ).mul (hcm.mul hcdHr)
    have hcS : ∀ k ∈ Finset.range m, Continuous (fun θ : ℝ => β k * (((-((k : ℤ) + 1) : ℤ) : ℂ)) *
        (L * (circleMap 0 ρ θ) ^ (-((k : ℤ) + 1)) + φ (circleMap 0 ρ θ) * (circleMap 0 ρ θ) ^ (-((k : ℤ) + 1)))) :=
      fun k _ => continuous_const.mul ((continuous_const.mul (hzp k)).add (hcφ.mul (hzp k)))
    rw [intervalIntegral.integral_add (hcF.intervalIntegrable _ _)
      ((continuous_finset_sum _ hcS).intervalIntegrable _ _),
      intervalIntegral.integral_finset_sum (fun k hk => (hcS k hk).intervalIntegrable _ _)]
    have hF0 : ∫ θ in (0 : ℝ)..2 * π, (L + φ (circleMap 0 ρ θ)) *
        (circleMap 0 ρ θ * deriv Hr (circleMap 0 ρ θ)) = 0 := by
      have hdiff : DifferentiableOn ℂ (fun u => (L + φ u) * (u * deriv Hr u)) unitDisc :=
        ((differentiableOn_const L).add hφ).mul (differentiableOn_id.mul hHr')
      rw [r22_mean hdiff hρ0 hρ1]
      simp
    rw [hF0, zero_add]
    have hk : ∀ k ∈ Finset.range m, ∫ θ in (0 : ℝ)..2 * π, β k * (((-((k : ℤ) + 1) : ℤ) : ℂ)) *
        (L * (circleMap 0 ρ θ) ^ (-((k : ℤ) + 1)) + φ (circleMap 0 ρ θ) * (circleMap 0 ρ θ) ^ (-((k : ℤ) + 1))) =
        2 * π * (-(((k + 1 : ℕ) : ℂ) * cφ (k + 1) * β k)) := by
      intro k _
      have ia : IntervalIntegrable (fun θ : ℝ => L * (circleMap 0 ρ θ) ^ (-((k : ℤ) + 1))) volume 0 (2 * π) :=
        (continuous_const.mul (hzp k)).intervalIntegrable _ _
      have ib : IntervalIntegrable (fun θ : ℝ => φ (circleMap 0 ρ θ) * (circleMap 0 ρ θ) ^ (-((k : ℤ) + 1)))
          volume 0 (2 * π) := (hcφ.mul (hzp k)).intervalIntegrable _ _
      rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add ia ib,
        intervalIntegral.integral_const_mul, t21_int_zpow hρ0, t21_int_phi_zpow hsφ hρ0 hρ1]
      push_cast
      ring
    rw [Finset.sum_congr rfl hk, ← Finset.mul_sum, Finset.sum_neg_distrib]
  have J4 : ∫ θ in (0 : ℝ)..2 * π, (L + φ (circleMap 0 ρ θ)) = 2 * π * L := by
    rw [intervalIntegral.integral_add intervalIntegrable_const (hcφ.intervalIntegrable _ _),
      r22_mean hφ hρ0 hρ1, hφ0]
    simp
  have hconjint : (∫ θ in (0 : ℝ)..2 * π, conj (Hr (circleMap 0 ρ θ) + Pr (circleMap 0 ρ θ))) =
      conj (∫ θ in (0 : ℝ)..2 * π, (Hr (circleMap 0 ρ θ) + Pr (circleMap 0 ρ θ))) := by
    rw [intervalIntegral.integral_of_le (by positivity), intervalIntegral.integral_of_le (by positivity)]
    exact integral_conj
  -- assemble
  obtain ⟨A, hA⟩ : ∃ A : ℝ → ℂ, ∀ θ, A θ = ε * (conj (Hr (circleMap 0 ρ θ) + Pr (circleMap 0 ρ θ)) *
      (deriv Hr (circleMap 0 ρ θ) + Pd (circleMap 0 ρ θ)) * circleMap 0 ρ θ) := ⟨_, fun _ => rfl⟩
  obtain ⟨B, hB⟩ : ∃ B : ℝ → ℂ, ∀ θ, B θ = κ * conj (Hr (circleMap 0 ρ θ) + Pr (circleMap 0 ρ θ)) :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨C, hC⟩ : ∃ C : ℝ → ℂ, ∀ θ, C θ = conj κ * ε * ((L + φ (circleMap 0 ρ θ)) *
      (circleMap 0 ρ θ * (deriv Hr (circleMap 0 ρ θ) + Pd (circleMap 0 ρ θ)))) := ⟨_, fun _ => rfl⟩
  obtain ⟨D, hD⟩ : ∃ D : ℝ → ℂ, ∀ θ, D θ = conj κ * κ * (L + φ (circleMap 0 ρ θ)) := ⟨_, fun _ => rfl⟩
  have hpt : ∀ θ : ℝ, (conj (Hr (circleMap 0 ρ θ) + Pr (circleMap 0 ρ θ)) + conj κ * (L + φ (circleMap 0 ρ θ))) *
      (ε * (circleMap 0 ρ θ * (deriv Hr (circleMap 0 ρ θ) + Pd (circleMap 0 ρ θ))) + κ) =
      A θ + B θ + C θ + D θ := fun θ => by rw [hA, hB, hC, hD]; ring
  simp_rw [hpt]
  have hcC : Continuous (fun θ : ℝ => conj (Hr (circleMap 0 ρ θ) + Pr (circleMap 0 ρ θ))) :=
    Complex.continuous_conj.comp hcĤ
  have cA : Continuous A := by
    have : A = fun θ => ε * (conj (Hr (circleMap 0 ρ θ) + Pr (circleMap 0 ρ θ)) *
      (deriv Hr (circleMap 0 ρ θ) + Pd (circleMap 0 ρ θ)) * circleMap 0 ρ θ) := funext hA
    rw [this]; exact continuous_const.mul ((hcC.mul hcdĤ).mul hcm)
  have cB : Continuous B := by
    have : B = fun θ => κ * conj (Hr (circleMap 0 ρ θ) + Pr (circleMap 0 ρ θ)) := funext hB
    rw [this]; exact continuous_const.mul hcC
  have cC : Continuous C := by
    have : C = fun θ => conj κ * ε * ((L + φ (circleMap 0 ρ θ)) *
      (circleMap 0 ρ θ * (deriv Hr (circleMap 0 ρ θ) + Pd (circleMap 0 ρ θ)))) := funext hC
    rw [this]; exact continuous_const.mul ((continuous_const.add hcφ).mul (hcm.mul hcdĤ))
  have cD : Continuous D := by
    have : D = fun θ => conj κ * κ * (L + φ (circleMap 0 ρ θ)) := funext hD
    rw [this]; exact continuous_const.mul (continuous_const.add hcφ)
  have iA : IntervalIntegrable A volume 0 (2 * π) := cA.intervalIntegrable _ _
  have iB : IntervalIntegrable B volume 0 (2 * π) := cB.intervalIntegrable _ _
  have iC : IntervalIntegrable C volume 0 (2 * π) := cC.intervalIntegrable _ _
  have iD : IntervalIntegrable D volume 0 (2 * π) := cD.intervalIntegrable _ _
  have eA : ∫ θ in (0 : ℝ)..2 * π, A θ = ε * (2 * π * (((∑' j : ℕ, ((j + 1 : ℕ) : ℝ) *
      (‖cr (j + 1)‖ ^ 2 * ρ ^ (2 * (j + 1))) - ∑ k ∈ Finset.range m, ((k + 1 : ℕ) : ℝ) *
        (‖β k‖ ^ 2 * (ρ ^ (2 * (k + 1)))⁻¹) : ℝ) : ℂ))) := by
    simp_rw [hA]
    rw [intervalIntegral.integral_const_mul, J1]
  have eB : ∫ θ in (0 : ℝ)..2 * π, B θ = κ * (2 * π * conj (cr 0)) := by
    simp_rw [hB]
    rw [intervalIntegral.integral_const_mul, hconjint, J2]
    simp only [map_mul, map_ofNat, Complex.conj_ofReal]
  have eC : ∫ θ in (0 : ℝ)..2 * π, C θ =
      conj κ * ε * (2 * π * (-∑ k ∈ Finset.range m, ((k + 1 : ℕ) : ℂ) * cφ (k + 1) * β k)) := by
    simp_rw [hC]
    rw [intervalIntegral.integral_const_mul, J3]
  have eD : ∫ θ in (0 : ℝ)..2 * π, D θ = conj κ * κ * (2 * π * L) := by
    simp_rw [hD]
    rw [intervalIntegral.integral_const_mul, J4]
  rw [intervalIntegral.integral_add ((iA.add iB).add iC) iD, intervalIntegral.integral_add (iA.add iB) iC,
    intervalIntegral.integral_add iA iB, eA, eB, eC, eD]
  ring

/-! ## `f`-side Faber expansion and boundary term -/

/-- The Laurent expansion of `U ∘ f` on `𝔻` for a combination of Faber polynomials. -/
theorem t21_f_exp {f g : ℂ → ℂ} (h : IsNormalizedDisjointPair f g) {P Q : ℕ → Polynomial ℂ}
    (hPQ : IsFaber f g P Q) (m : ℕ) (α β : ℕ → ℂ) (U : ℂ → ℂ)
    (hU : ∀ w : ℂ, U w = ∑ k ∈ Finset.range m, (α k * (P (k + 1)).eval w + β k * (Q (k + 1)).eval w⁻¹)) :
    ∀ z ∈ unitDisc, z ≠ 0 →
      HasSum (fun j : ℕ => (∑ k ∈ Finset.range m,
          (((k + 1 : ℕ) : ℂ) * α k * grunsky f g ((k : ℤ) + 1) (-((j : ℤ) + 1)) +
            ((k + 1 : ℕ) : ℂ) * β k * grunsky f g (-((k : ℤ) + 1)) (-((j : ℤ) + 1)))) * z ^ (j + 1))
        (U (f z) - (∑ k ∈ Finset.range m, ((k + 1 : ℕ) : ℂ) * α k * grunsky f g ((k : ℤ) + 1) 0) -
          ∑ k ∈ Finset.range m, β k * z ^ (-((k : ℤ) + 1))) := by
  intro z hz hz0
  set b := grunsky f g with hb
  have hk : ∀ k ∈ Finset.range m,
      HasSum (fun j : ℕ => α k * (((k + 1 : ℕ) : ℂ) * b ((k : ℤ) + 1) (-((j + 1 : ℕ) : ℤ)) * z ^ (j + 1)) +
          β k * (((k + 1 : ℕ) : ℂ) * b (-((k : ℤ) + 1)) (-((j + 1 : ℕ) : ℤ)) * z ^ (j + 1)))
        (α k * ((P (k + 1)).eval (f z) - ((k + 1 : ℕ) : ℂ) * b ((k : ℤ) + 1) 0) +
          β k * ((Q (k + 1)).eval (f z)⁻¹ - z ^ (-((k : ℤ) + 1)))) := by
    intro k _
    have hA := (faber_grunsky h hPQ k).1 z hz
    have hB := hPQ.2.2 k z hz hz0
    simp only [Nat.cast_add, Nat.cast_one, Int.cast_add, Int.cast_one] at hA hB ⊢
    exact (hA.mul_left (α k)).add (hB.mul_left (β k))
  have hS := hasSum_sum hk
  convert hS using 1
  · funext j
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    push_cast
    ring
  · rw [hU (f z)]
    simp only [mul_sub, mul_add, Finset.sum_add_distrib, Finset.sum_sub_distrib]
    have e1 : ∑ k ∈ Finset.range m, α k * (((k + 1 : ℕ) : ℂ) * b ((k : ℤ) + 1) 0) =
        ∑ k ∈ Finset.range m, ((k + 1 : ℕ) : ℂ) * α k * b ((k : ℤ) + 1) 0 :=
      Finset.sum_congr rfl (fun k _ => by ring)
    rw [e1]
    ring

/-- A combination of Faber polynomials is differentiable off `0`. -/
theorem t21_U_diff {P Q : ℕ → Polynomial ℂ} (m : ℕ) (α β : ℕ → ℂ) (U : ℂ → ℂ)
    (hU : ∀ w : ℂ, U w = ∑ k ∈ Finset.range m, (α k * (P (k + 1)).eval w + β k * (Q (k + 1)).eval w⁻¹))
    {w : ℂ} (hw : w ≠ 0) : DifferentiableAt ℂ U w := by
  have : U = fun w => ∑ k ∈ Finset.range m, (α k * (P (k + 1)).eval w + β k * (Q (k + 1)).eval w⁻¹) :=
    funext hU
  rw [this]
  refine DifferentiableAt.fun_sum (fun k _ => ?_)
  refine DifferentiableAt.add ?_ ?_
  · exact (Polynomial.differentiableAt _).const_mul _
  · exact ((Polynomial.differentiableAt (Q (k + 1))).comp w (differentiableAt_inv_iff.mpr hw)).const_mul _

/-- The `f`-side boundary term of the log-Green identity for `W = (Ū + κ̄ ℓ)(U' + κ/w)`. -/
theorem t21_f_side {f g : ℂ → ℂ} (h : IsNormalizedDisjointPair f g) {P Q : ℕ → Polynomial ℂ}
    (hPQ : IsFaber f g P Q) (m : ℕ) (α β : ℕ → ℂ) (U : ℂ → ℂ)
    (hU : ∀ w : ℂ, U w = ∑ k ∈ Finset.range m, (α k * (P (k + 1)).eval w + β k * (Q (k + 1)).eval w⁻¹))
    (κ : ℂ) {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) :
    ∃ (D : ℕ → ℂ) (c0 : ℂ),
      (∀ j : ℕ, D j = ∑ k ∈ Finset.range m,
          (((k + 1 : ℕ) : ℂ) * α k * grunsky f g ((k : ℤ) + 1) (-((j : ℤ) + 1)) +
            ((k + 1 : ℕ) : ℂ) * β k * grunsky f g (-((k : ℤ) + 1)) (-((j : ℤ) + 1)))) ∧
      c0 = ∑ k ∈ Finset.range m, ((k + 1 : ℕ) : ℂ) * α k * grunsky f g ((k : ℤ) + 1) 0 ∧
      Summable (fun j : ℕ => ((j + 1 : ℕ) : ℝ) *
        (‖D j + κ * (-grunsky f g (-((j : ℤ) + 1)) 0)‖ ^ 2 * ρ ^ (2 * (j + 1)))) ∧
      (∫ θ in (0 : ℝ)..2 * π,
          (conj (U (f (circleMap 0 ρ θ))) + conj κ * ((Real.log (‖f (circleMap 0 ρ θ)‖ ^ 2) : ℝ) : ℂ)) *
            (deriv U (f (circleMap 0 ρ θ)) + κ / f (circleMap 0 ρ θ)) *
              deriv f (circleMap 0 ρ θ) * circleMap 0 ρ θ) =
        2 * π * ((((∑' j : ℕ, ((j + 1 : ℕ) : ℝ) *
            (‖D j + κ * (-grunsky f g (-((j : ℤ) + 1)) 0)‖ ^ 2 * ρ ^ (2 * (j + 1))) -
          ∑ k ∈ Finset.range m, ((k + 1 : ℕ) : ℝ) * (‖β k‖ ^ 2 * (ρ ^ (2 * (k + 1)))⁻¹) : ℝ) : ℂ)) +
          κ * conj c0 -
          conj κ * ∑ k ∈ Finset.range m, ((k + 1 : ℕ) : ℂ) * (-grunsky f g (-((k : ℤ) + 1)) 0) * β k +
          conj κ * κ * ((Real.log (ρ ^ 2) : ℝ) : ℂ)) := by
  have hh := h
  obtain ⟨-, -, hf0, -, -, -⟩ := hh
  obtain ⟨φ, hsφ0, hf⟩ := r22_f_series h
  obtain ⟨D, hD⟩ : ∃ D : ℕ → ℂ, ∀ j : ℕ, D j = ∑ k ∈ Finset.range m,
      (((k + 1 : ℕ) : ℂ) * α k * grunsky f g ((k : ℤ) + 1) (-((j : ℤ) + 1)) +
        ((k + 1 : ℕ) : ℂ) * β k * grunsky f g (-((k : ℤ) + 1)) (-((j : ℤ) + 1))) := ⟨_, fun _ => rfl⟩
  obtain ⟨c0, hc0⟩ : ∃ c0 : ℂ, c0 = ∑ k ∈ Finset.range m,
      ((k + 1 : ℕ) : ℂ) * α k * grunsky f g ((k : ℤ) + 1) 0 := ⟨_, rfl⟩
  obtain ⟨cφ, hcφ⟩ : ∃ cφ : ℕ → ℂ, ∀ n, cφ n = if n = 0 then 0 else -grunsky f g (-(n : ℤ)) 0 :=
    ⟨_, fun _ => rfl⟩
  have hsφ : ∀ z ∈ unitDisc, HasSum (fun n : ℕ => cφ n * z ^ n) (φ z) := by
    intro z hz
    simpa only [hcφ] using hsφ0 z hz
  have hcφ0 : cφ 0 = 0 := by rw [hcφ]; simp
  have hcφs : ∀ j : ℕ, cφ (j + 1) = -grunsky f g (-((j : ℤ) + 1)) 0 := fun j => by
    rw [hcφ, if_neg (Nat.succ_ne_zero j)]
    push_cast
    rfl
  have hexp := t21_f_exp h hPQ m α β U hU
  simp only [← hD, ← hc0] at hexp
  obtain ⟨cc, hcc⟩ : ∃ cc : ℕ → ℂ, ∀ n, cc n = if n = 0 then c0 else D (n - 1) := ⟨_, fun _ => rfl⟩
  have hccs : ∀ j : ℕ, cc (j + 1) = D j := fun j => by rw [hcc]; simp
  have hcc0 : cc 0 = c0 := by rw [hcc]; simp
  obtain ⟨Hh, hHh⟩ : ∃ Hh : ℂ → ℂ, ∀ z, Hh z = ∑' n : ℕ, cc n * z ^ n := ⟨_, fun _ => rfl⟩
  have hsHh : ∀ z ∈ unitDisc, HasSum (fun n : ℕ => cc n * z ^ n) (Hh z) := by
    intro z hz
    rw [hHh]
    refine Summable.hasSum ?_
    by_cases hz0 : z = 0
    · subst hz0
      refine summable_of_ne_finset_zero (s := Finset.range 1) (fun n hn => ?_)
      have : n ≠ 0 := by simpa using hn
      simp [this]
    · have hS := hexp z hz hz0
      refine ((summable_nat_add_iff 1).mp ?_)
      refine hS.summable.congr (fun j => ?_)
      rw [hccs]
  have hHhv : ∀ z ∈ unitDisc, z ≠ 0 → Hh z + ∑ k ∈ Finset.range m, β k * z ^ (-((k : ℤ) + 1)) = U (f z) := by
    intro z hz hz0
    have hS := hexp z hz hz0
    have h1 : HasSum (fun n : ℕ => cc n * z ^ n)
        (c0 + (U (f z) - c0 - ∑ k ∈ Finset.range m, β k * z ^ (-((k : ℤ) + 1)))) := by
      refine (hasSum_nat_add_iff' 1).mp ?_
      have e : c0 + (U (f z) - c0 - ∑ k ∈ Finset.range m, β k * z ^ (-((k : ℤ) + 1))) -
          ∑ i ∈ Finset.range 1, cc i * z ^ i =
          U (f z) - c0 - ∑ k ∈ Finset.range m, β k * z ^ (-((k : ℤ) + 1)) := by
        simp [hcc0]
      rw [e]
      exact hS.congr_fun (fun j => by rw [hccs])
    rw [hHh, h1.tsum_eq]
    ring
  obtain ⟨Hr, hHr⟩ : ∃ Hr : ℂ → ℂ, ∀ z, Hr z = Hh z + κ * φ z := ⟨_, fun _ => rfl⟩
  obtain ⟨cr, hcr⟩ : ∃ cr : ℕ → ℂ, ∀ n, cr n = cc n + κ * cφ n := ⟨_, fun _ => rfl⟩
  have hsr : ∀ z ∈ unitDisc, HasSum (fun n : ℕ => cr n * z ^ n) (Hr z) := by
    intro z hz
    rw [hHr]
    refine ((hsHh z hz).add ((hsφ z hz).mul_left κ)).congr_fun (fun n => ?_)
    rw [hcr]; ring
  have hmain := t21_side (Hr := Hr) (φ := φ) (cr := cr) (cφ := cφ) (β := β) (m := m) hsr hsφ hcφ0
    hρ0 hρ1 κ ((Real.log (ρ ^ 2) : ℝ) : ℂ) 1
  beta_reduce at hmain
  have hcr1 : ∀ j : ℕ, cr (j + 1) = D j + κ * (-grunsky f g (-((j : ℤ) + 1)) 0) := fun j => by
    rw [hcr, hccs, hcφs]
  have hcr0 : cr 0 = c0 := by rw [hcr, hcc0, hcφ0]; ring
  have hen := (t21_energy (Hh := Hr) (cc := cr) (β := β) (m := m) hsr hρ0 hρ1).1
  simp_rw [hcr1] at hen
  refine ⟨D, c0, hD, hc0, hen, ?_⟩
  simp_rw [hcr1, hcφs] at hmain
  rw [hcr0] at hmain
  have hpt : ∀ θ : ℝ,
      (conj (U (f (circleMap 0 ρ θ))) + conj κ * ((Real.log (‖f (circleMap 0 ρ θ)‖ ^ 2) : ℝ) : ℂ)) *
          (deriv U (f (circleMap 0 ρ θ)) + κ / f (circleMap 0 ρ θ)) *
            deriv f (circleMap 0 ρ θ) * circleMap 0 ρ θ =
        (conj (Hr (circleMap 0 ρ θ) + ∑ k ∈ Finset.range m, β k * (circleMap 0 ρ θ) ^ (-((k : ℤ) + 1))) +
            conj κ * (((Real.log (ρ ^ 2) : ℝ) : ℂ) + φ (circleMap 0 ρ θ))) *
          (1 * (circleMap 0 ρ θ * deriv (fun u : ℂ => Hr u + ∑ k ∈ Finset.range m, β k * u ^ (-((k : ℤ) + 1)))
              (circleMap 0 ρ θ)) + κ) := by
    intro θ
    have hcn : circleMap 0 ρ θ ≠ 0 := circleMap_ne_center hρ0.ne'
    have hnorm : ‖circleMap 0 ρ θ‖ = ρ := by rw [norm_circleMap_zero, abs_of_pos hρ0]
    have hcD : circleMap 0 ρ θ ∈ unitDisc := mem_ball_zero_iff.mpr (by rw [hnorm]; exact hρ1)
    set c := circleMap 0 ρ θ with hcdef
    have hfc : f c = c * Complex.exp (φ c) := hf c hcD
    have hφd : DifferentiableAt ℂ φ c :=
      (differentiableOn_of_powerSeries hsφ).differentiableAt (isOpen_ball.mem_nhds hcD)
    have hev : f =ᶠ[𝓝 c] fun z => z * Complex.exp (φ z) :=
      Filter.eventuallyEq_of_mem (isOpen_ball.mem_nhds hcD) (fun z hz => hf z hz)
    have hfd : DifferentiableAt ℂ f c := by
      have : DifferentiableAt ℂ (fun z => z * Complex.exp (φ z)) c := differentiableAt_id.mul hφd.cexp
      exact this.congr_of_eventuallyEq hev
    have h2 : HasDerivAt (fun z => z * Complex.exp (φ z))
        (1 * Complex.exp (φ c) + c * (Complex.exp (φ c) * deriv φ c)) c :=
      (hasDerivAt_id' c).mul hφd.hasDerivAt.cexp
    have hdf : deriv f c = Complex.exp (φ c) * (1 + c * deriv φ c) := by
      rw [hev.deriv_eq, h2.deriv]; ring
    have hexpne : Complex.exp (φ c) ≠ 0 := Complex.exp_ne_zero _
    have hfne : f c ≠ 0 := by rw [hfc]; exact mul_ne_zero hcn hexpne
    have hUd : DifferentiableAt ℂ U (f c) := t21_U_diff m α β U hU hfne
    have hnb : IsOpen (unitDisc \ {0}) := isOpen_ball.sdiff isClosed_singleton
    have hĤ_eq : (fun u : ℂ => Hr u + ∑ k ∈ Finset.range m, β k * u ^ (-((k : ℤ) + 1))) =ᶠ[𝓝 c]
        fun u => U (f u) + κ * φ u := by
      refine Filter.eventuallyEq_of_mem (hnb.mem_nhds ⟨hcD, hcn⟩) (fun u hu => ?_)
      show Hr u + ∑ k ∈ Finset.range m, β k * u ^ (-((k : ℤ) + 1)) = U (f u) + κ * φ u
      rw [hHr]
      have := hHhv u hu.1 hu.2
      linear_combination this
    have hderĤ : deriv (fun u : ℂ => Hr u + ∑ k ∈ Finset.range m, β k * u ^ (-((k : ℤ) + 1))) c =
        deriv U (f c) * deriv f c + κ * deriv φ c := by
      rw [hĤ_eq.deriv_eq]
      have h1 : HasDerivAt (fun u => U (f u)) (deriv U (f c) * deriv f c) c :=
        hUd.hasDerivAt.comp c hfd.hasDerivAt
      exact (h1.add (hφd.hasDerivAt.const_mul κ)).deriv
    have hval : Hr c + ∑ k ∈ Finset.range m, β k * c ^ (-((k : ℤ) + 1)) = U (f c) + κ * φ c := by
      rw [hHr]
      have := hHhv c hcD hcn
      linear_combination this
    have hlogf : ((Real.log (‖f c‖ ^ 2) : ℝ) : ℂ) = ((Real.log (ρ ^ 2) : ℝ) : ℂ) + φ c + conj (φ c) := by
      rw [hfc, r22_log_norm hcn, hnorm]
    rw [hderĤ, hval, hlogf, map_add, map_mul, hdf, hfc]
    field_simp
    ring
  have hI := intervalIntegral.integral_congr (μ := volume) (a := (0 : ℝ)) (b := 2 * π) (fun θ _ => hpt θ)
  rw [hI, hmain]
  ring

/-! ## `g`-side Faber expansion and boundary term -/

/-- The Laurent expansion of `U ∘ g` on `𝔻*` for a combination of Faber polynomials. -/
theorem t21_g_exp {f g : ℂ → ℂ} (h : IsNormalizedDisjointPair f g) {P Q : ℕ → Polynomial ℂ}
    (hPQ : IsFaber f g P Q) (m : ℕ) (α β : ℕ → ℂ) (U : ℂ → ℂ)
    (hU : ∀ w : ℂ, U w = ∑ k ∈ Finset.range m, (α k * (P (k + 1)).eval w + β k * (Q (k + 1)).eval w⁻¹)) :
    ∀ z : ℂ, 1 < ‖z‖ →
      HasSum (fun k : ℕ => (∑ j ∈ Finset.range m,
          (((j + 1 : ℕ) : ℂ) * α j * grunsky f g ((j : ℤ) + 1) ((k : ℤ) + 1) +
            ((j + 1 : ℕ) : ℂ) * β j * grunsky f g ((k : ℤ) + 1) (-((j : ℤ) + 1)))) * z ^ (-((k : ℤ) + 1)))
        (U (g z) - ∑ j ∈ Finset.range m, α j * z ^ (j + 1) -
          (-∑ j ∈ Finset.range m, ((j + 1 : ℕ) : ℂ) * β j * grunsky f g (-((j : ℤ) + 1)) 0)) := by
  intro z hz
  set b := grunsky f g with hb
  have hk : ∀ j ∈ Finset.range m,
      HasSum (fun k : ℕ => α j * (((j + 1 : ℕ) : ℂ) * b ((j : ℤ) + 1) ((k : ℤ) + 1) * z ^ (-((k : ℤ) + 1))) +
          β j * (((j + 1 : ℕ) : ℂ) * b ((k : ℤ) + 1) (-((j : ℤ) + 1)) * z ^ (-((k : ℤ) + 1))))
        (α j * ((P (j + 1)).eval (g z) - z ^ (j + 1)) +
          β j * ((Q (j + 1)).eval (g z)⁻¹ + ((j + 1 : ℕ) : ℂ) * b (-((j : ℤ) + 1)) 0)) := by
    intro j _
    have hA := hPQ.2.1 j z hz
    have hB := (faber_grunsky h hPQ j).2 z hz
    simp only [Nat.cast_add, Nat.cast_one, Int.cast_add, Int.cast_one] at hA hB ⊢
    exact (hA.mul_left (α j)).add (hB.mul_left (β j))
  have hS := hasSum_sum hk
  convert hS using 1
  · funext k
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    push_cast
    ring
  · rw [hU (g z)]
    have e1 : ∑ j ∈ Finset.range m, β j * (((j + 1 : ℕ) : ℂ) * b (-((j : ℤ) + 1)) 0) =
        ∑ j ∈ Finset.range m, ((j + 1 : ℕ) : ℂ) * β j * b (-((j : ℤ) + 1)) 0 :=
      Finset.sum_congr rfl (fun j _ => by ring)
    simp only [mul_sub, mul_add, Finset.sum_add_distrib, Finset.sum_sub_distrib]
    rw [e1]
    ring

/-- The `g`-side boundary term of the log-Green identity for `W = (Ū + κ̄ ℓ)(U' + κ/w)`. -/
theorem t21_g_side {f g : ℂ → ℂ} (h : IsNormalizedDisjointPair f g) {P Q : ℕ → Polynomial ℂ}
    (hPQ : IsFaber f g P Q) (m : ℕ) (α β : ℕ → ℂ) (U : ℂ → ℂ)
    (hU : ∀ w : ℂ, U w = ∑ k ∈ Finset.range m, (α k * (P (k + 1)).eval w + β k * (Q (k + 1)).eval w⁻¹))
    (κ : ℂ) {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) :
    ∃ (E : ℕ → ℂ) (c0 : ℂ),
      (∀ k : ℕ, E k = ∑ j ∈ Finset.range m,
          (((j + 1 : ℕ) : ℂ) * α j * grunsky f g ((j : ℤ) + 1) ((k : ℤ) + 1) +
            ((j + 1 : ℕ) : ℂ) * β j * grunsky f g ((k : ℤ) + 1) (-((j : ℤ) + 1)))) ∧
      c0 = -∑ j ∈ Finset.range m, ((j + 1 : ℕ) : ℂ) * β j * grunsky f g (-((j : ℤ) + 1)) 0 ∧
      Summable (fun k : ℕ => ((k + 1 : ℕ) : ℝ) *
        (‖E k + κ * (-grunsky f g ((k : ℤ) + 1) 0)‖ ^ 2 * ρ ^ (2 * (k + 1)))) ∧
      (∫ θ in (0 : ℝ)..2 * π,
          (conj (U (g (circleMap 0 (1 / ρ) θ))) +
              conj κ * ((Real.log (‖g (circleMap 0 (1 / ρ) θ)‖ ^ 2) : ℝ) : ℂ)) *
            (deriv U (g (circleMap 0 (1 / ρ) θ)) + κ / g (circleMap 0 (1 / ρ) θ)) *
              deriv g (circleMap 0 (1 / ρ) θ) * circleMap 0 (1 / ρ) θ) =
        2 * π * (-(((∑' k : ℕ, ((k + 1 : ℕ) : ℝ) *
            (‖E k + κ * (-grunsky f g ((k : ℤ) + 1) 0)‖ ^ 2 * ρ ^ (2 * (k + 1))) -
          ∑ j ∈ Finset.range m, ((j + 1 : ℕ) : ℝ) * (‖α j‖ ^ 2 * (ρ ^ (2 * (j + 1)))⁻¹) : ℝ) : ℂ)) +
          κ * conj c0 +
          conj κ * ∑ j ∈ Finset.range m, ((j + 1 : ℕ) : ℂ) * (-grunsky f g ((j : ℤ) + 1) 0) * α j +
          conj κ * κ * ((Real.log (‖derivAtInfty g‖ ^ 2 * (ρ ^ 2)⁻¹) : ℝ) : ℂ)) := by
  have hh := h
  obtain ⟨-, -, hf0, -, hgu, -⟩ := hh
  obtain ⟨hexpb, -, -, -, -⟩ := (grunsky_spec h).1
  have hβ : derivAtInfty g ≠ 0 := by rw [← hexpb]; exact Complex.exp_ne_zero _
  obtain ⟨φ, hsφ0, hg⟩ := r22_g_series h
  obtain ⟨E, hE⟩ : ∃ E : ℕ → ℂ, ∀ k : ℕ, E k = ∑ j ∈ Finset.range m,
      (((j + 1 : ℕ) : ℂ) * α j * grunsky f g ((j : ℤ) + 1) ((k : ℤ) + 1) +
        ((j + 1 : ℕ) : ℂ) * β j * grunsky f g ((k : ℤ) + 1) (-((j : ℤ) + 1))) := ⟨_, fun _ => rfl⟩
  obtain ⟨c0, hc0⟩ : ∃ c0 : ℂ, c0 = -∑ j ∈ Finset.range m,
      ((j + 1 : ℕ) : ℂ) * β j * grunsky f g (-((j : ℤ) + 1)) 0 := ⟨_, rfl⟩
  obtain ⟨cφ, hcφ⟩ : ∃ cφ : ℕ → ℂ, ∀ n, cφ n = if n = 0 then 0 else -grunsky f g (n : ℤ) 0 :=
    ⟨_, fun _ => rfl⟩
  have hsφ : ∀ z ∈ unitDisc, HasSum (fun n : ℕ => cφ n * z ^ n) (φ z) := by
    intro z hz
    simpa only [hcφ] using hsφ0 z hz
  have hcφ0 : cφ 0 = 0 := by rw [hcφ]; simp
  have hcφs : ∀ j : ℕ, cφ (j + 1) = -grunsky f g ((j : ℤ) + 1) 0 := fun j => by
    rw [hcφ, if_neg (Nat.succ_ne_zero j)]
    push_cast
    rfl
  have hexp := t21_g_exp h hPQ m α β U hU
  simp only [← hE, ← hc0] at hexp
  have hzinv : ∀ u : ℂ, u ∈ unitDisc → u ≠ 0 → 1 < ‖u⁻¹‖ := by
    intro u hu hu0
    have hpos : 0 < ‖u‖ := norm_pos_iff.mpr hu0
    rw [norm_inv]
    exact (one_lt_inv₀ hpos).mpr (mem_ball_zero_iff.mp hu)
  have hpw : ∀ (u : ℂ) (n : ℕ), (u⁻¹) ^ (-((n : ℤ) + 1)) = u ^ (n + 1) := by
    intro u n
    rw [zpow_neg, inv_zpow, inv_inv]
    exact_mod_cast zpow_natCast u (n + 1)
  have hpw' : ∀ (u : ℂ) (n : ℕ), (u⁻¹) ^ (n + 1) = u ^ (-((n : ℤ) + 1)) := by
    intro u n
    have : ((n : ℤ) + 1) = ((n + 1 : ℕ) : ℤ) := by push_cast; ring
    rw [this, zpow_neg, zpow_natCast, inv_pow]
  obtain ⟨cc, hcc⟩ : ∃ cc : ℕ → ℂ, ∀ n, cc n = if n = 0 then c0 else E (n - 1) := ⟨_, fun _ => rfl⟩
  have hccs : ∀ j : ℕ, cc (j + 1) = E j := fun j => by rw [hcc]; simp
  have hcc0 : cc 0 = c0 := by rw [hcc]; simp
  obtain ⟨Hh, hHh⟩ : ∃ Hh : ℂ → ℂ, ∀ z, Hh z = ∑' n : ℕ, cc n * z ^ n := ⟨_, fun _ => rfl⟩
  have hSu : ∀ u ∈ unitDisc, u ≠ 0 → HasSum (fun j : ℕ => E j * u ^ (j + 1))
      (U (g u⁻¹) - ∑ k ∈ Finset.range m, α k * u ^ (-((k : ℤ) + 1)) - c0) := by
    intro u hu hu0
    have hS := hexp u⁻¹ (hzinv u hu hu0)
    simp only [hpw, hpw'] at hS
    exact hS
  have hsHh : ∀ z ∈ unitDisc, HasSum (fun n : ℕ => cc n * z ^ n) (Hh z) := by
    intro z hz
    rw [hHh]
    refine Summable.hasSum ?_
    by_cases hz0 : z = 0
    · subst hz0
      refine summable_of_ne_finset_zero (s := Finset.range 1) (fun n hn => ?_)
      have : n ≠ 0 := by simpa using hn
      simp [this]
    · refine ((summable_nat_add_iff 1).mp ?_)
      refine (hSu z hz hz0).summable.congr (fun j => ?_)
      rw [hccs]
  have hHhv : ∀ z ∈ unitDisc, z ≠ 0 →
      Hh z + ∑ k ∈ Finset.range m, α k * z ^ (-((k : ℤ) + 1)) = U (g z⁻¹) := by
    intro z hz hz0
    have hS := hSu z hz hz0
    have h1 : HasSum (fun n : ℕ => cc n * z ^ n)
        (c0 + (U (g z⁻¹) - ∑ k ∈ Finset.range m, α k * z ^ (-((k : ℤ) + 1)) - c0)) := by
      refine (hasSum_nat_add_iff' 1).mp ?_
      have e : c0 + (U (g z⁻¹) - ∑ k ∈ Finset.range m, α k * z ^ (-((k : ℤ) + 1)) - c0) -
          ∑ i ∈ Finset.range 1, cc i * z ^ i =
          U (g z⁻¹) - ∑ k ∈ Finset.range m, α k * z ^ (-((k : ℤ) + 1)) - c0 := by
        simp [hcc0]
      rw [e]
      exact hS.congr_fun (fun j => by rw [hccs])
    rw [hHh, h1.tsum_eq]
    ring
  obtain ⟨Hr, hHr⟩ : ∃ Hr : ℂ → ℂ, ∀ z, Hr z = Hh z + κ * φ z := ⟨_, fun _ => rfl⟩
  obtain ⟨cr, hcr⟩ : ∃ cr : ℕ → ℂ, ∀ n, cr n = cc n + κ * cφ n := ⟨_, fun _ => rfl⟩
  have hsr : ∀ z ∈ unitDisc, HasSum (fun n : ℕ => cr n * z ^ n) (Hr z) := by
    intro z hz
    rw [hHr]
    refine ((hsHh z hz).add ((hsφ z hz).mul_left κ)).congr_fun (fun n => ?_)
    rw [hcr]; ring
  have hmain := t21_side (Hr := Hr) (φ := φ) (cr := cr) (cφ := cφ) (β := α) (m := m) hsr hsφ hcφ0
    hρ0 hρ1 κ ((Real.log (‖derivAtInfty g‖ ^ 2 * (ρ ^ 2)⁻¹) : ℝ) : ℂ) (-1)
  beta_reduce at hmain
  have hcr1 : ∀ j : ℕ, cr (j + 1) = E j + κ * (-grunsky f g ((j : ℤ) + 1) 0) := fun j => by
    rw [hcr, hccs, hcφs]
  have hcr0 : cr 0 = c0 := by rw [hcr, hcc0, hcφ0]; ring
  have hen := (t21_energy (Hh := Hr) (cc := cr) (β := α) (m := m) hsr hρ0 hρ1).1
  simp_rw [hcr1] at hen
  refine ⟨E, c0, hE, hc0, hen, ?_⟩
  simp_rw [hcr1, hcφs] at hmain
  rw [hcr0] at hmain
  have hR : 0 < 1 / ρ := by positivity
  have hpt : ∀ θ : ℝ,
      (conj (U (g (circleMap 0 (1 / ρ) θ))) +
          conj κ * ((Real.log (‖g (circleMap 0 (1 / ρ) θ)‖ ^ 2) : ℝ) : ℂ)) *
        (deriv U (g (circleMap 0 (1 / ρ) θ)) + κ / g (circleMap 0 (1 / ρ) θ)) *
          deriv g (circleMap 0 (1 / ρ) θ) * circleMap 0 (1 / ρ) θ =
      (fun u : ℂ => (conj (Hr u + ∑ k ∈ Finset.range m, α k * u ^ (-((k : ℤ) + 1))) +
          conj κ * (((Real.log (‖derivAtInfty g‖ ^ 2 * (ρ ^ 2)⁻¹) : ℝ) : ℂ) + φ u)) *
        ((-1) * (u * deriv (fun v : ℂ => Hr v + ∑ k ∈ Finset.range m, α k * v ^ (-((k : ℤ) + 1))) u) + κ))
        (circleMap 0 ρ (-θ)) := by
    intro θ
    obtain ⟨u, hu⟩ : ∃ u, u = circleMap 0 ρ (-θ) := ⟨_, rfl⟩
    rw [← hu]
    have huz : circleMap 0 (1 / ρ) θ = u⁻¹ := by
      rw [hu, ← inv_inv (circleMap 0 (1 / ρ) θ), r22_circle_inv hR, one_div_one_div]
    have hun : ‖u‖ = ρ := by rw [hu, norm_circleMap_zero, abs_of_pos hρ0]
    have huD : u ∈ unitDisc := mem_ball_zero_iff.mpr (by rw [hun]; exact hρ1)
    have hu0 : u ≠ 0 := by rw [hu]; exact circleMap_ne_center hρ0.ne'
    rw [huz]
    have hzn : ‖u⁻¹‖ = 1 / ρ := by rw [norm_inv, hun, one_div]
    have hφ := differentiableOn_of_powerSeries hsφ
    have hφd : DifferentiableAt ℂ φ u := hφ.differentiableAt (isOpen_ball.mem_nhds huD)
    have hgz : g u⁻¹ = derivAtInfty g * u⁻¹ * Complex.exp (φ u) := hg u huD hu0
    have hder : deriv g u⁻¹ = derivAtInfty g * Complex.exp (φ u) * (1 - u * deriv φ u) :=
      r22_g_deriv hφ hg huD hu0
    have hz0 : u⁻¹ ≠ 0 := inv_ne_zero hu0
    have hgne : g u⁻¹ ≠ 0 := by
      rw [hgz]; exact mul_ne_zero (mul_ne_zero hβ hz0) (Complex.exp_ne_zero _)
    have hUd : DifferentiableAt ℂ U (g u⁻¹) := t21_U_diff m α β U hU hgne
    have hEo : IsOpen unitDiscExterior := isOpen_lt continuous_const continuous_norm
    have hgd : DifferentiableAt ℂ g u⁻¹ := hgu.1.differentiableAt (hEo.mem_nhds (hzinv u huD hu0))
    have hnb : IsOpen (unitDisc \ {0}) := isOpen_ball.sdiff isClosed_singleton
    have hĤ_eq : (fun v : ℂ => Hr v + ∑ k ∈ Finset.range m, α k * v ^ (-((k : ℤ) + 1))) =ᶠ[𝓝 u]
        fun v => U (g v⁻¹) + κ * φ v := by
      refine Filter.eventuallyEq_of_mem (hnb.mem_nhds ⟨huD, hu0⟩) (fun v hv => ?_)
      show Hr v + ∑ k ∈ Finset.range m, α k * v ^ (-((k : ℤ) + 1)) = U (g v⁻¹) + κ * φ v
      rw [hHr]
      have := hHhv v hv.1 hv.2
      linear_combination this
    have hderĤ : deriv (fun v : ℂ => Hr v + ∑ k ∈ Finset.range m, α k * v ^ (-((k : ℤ) + 1))) u =
        deriv U (g u⁻¹) * (deriv g u⁻¹ * (-(u ^ 2)⁻¹)) + κ * deriv φ u := by
      rw [hĤ_eq.deriv_eq]
      have h1 : HasDerivAt (fun v : ℂ => g v⁻¹) (deriv g u⁻¹ * (-(u ^ 2)⁻¹)) u :=
        hgd.hasDerivAt.comp u (hasDerivAt_inv hu0)
      have h2 : HasDerivAt (fun v : ℂ => U (g v⁻¹)) (deriv U (g u⁻¹) * (deriv g u⁻¹ * (-(u ^ 2)⁻¹))) u :=
        hUd.hasDerivAt.comp u h1
      exact (h2.add (hφd.hasDerivAt.const_mul κ)).deriv
    have hval : Hr u + ∑ k ∈ Finset.range m, α k * u ^ (-((k : ℤ) + 1)) = U (g u⁻¹) + κ * φ u := by
      rw [hHr]
      have := hHhv u huD hu0
      linear_combination this
    have hlogg : ((Real.log (‖g u⁻¹‖ ^ 2) : ℝ) : ℂ) =
        ((Real.log (‖derivAtInfty g‖ ^ 2 * (ρ ^ 2)⁻¹) : ℝ) : ℂ) + φ u + conj (φ u) := by
      rw [hgz, r22_log_norm (mul_ne_zero hβ hz0), norm_mul, hzn]
      have : (‖derivAtInfty g‖ * (1 / ρ)) ^ 2 = ‖derivAtInfty g‖ ^ 2 * (ρ ^ 2)⁻¹ := by
        rw [mul_pow, one_div, inv_pow]
      rw [this]
    beta_reduce
    rw [hderĤ, hval, hlogg, map_add, map_mul, hder, hgz]
    have hexpne : Complex.exp (φ u) ≠ 0 := Complex.exp_ne_zero _
    field_simp
    ring
  have hI := intervalIntegral.integral_congr (μ := volume) (a := (0 : ℝ)) (b := 2 * π) (fun θ _ => hpt θ)
  rw [hI, r22_reflect (fun u : ℂ => (conj (Hr u + ∑ k ∈ Finset.range m, α k * u ^ (-((k : ℤ) + 1))) +
          conj κ * (((Real.log (‖derivAtInfty g‖ ^ 2 * (ρ ^ 2)⁻¹) : ℝ) : ℂ) + φ u)) *
        ((-1) * (u * deriv (fun v : ℂ => Hr v + ∑ k ∈ Finset.range m, α k * v ^ (-((k : ℤ) + 1))) u) + κ)) ρ]
  beta_reduce
  rw [hmain]
  ring

/-! ## The Green function `W = (Ū + κ̄ ℓ)(U' + κ/w)` -/

/-- `ℓ(w) = log ‖w‖²` is `C¹` off `0`. -/
theorem t21_ell_contDiff : ContDiffOn ℝ 1 (fun w : ℂ => ((Real.log (‖w‖ ^ 2) : ℝ) : ℂ)) {0}ᶜ := by
  refine Complex.ofRealCLM.contDiff.comp_contDiffOn ?_
  intro w hw
  have hw0 : w ≠ 0 := hw
  have hn : ‖w‖ ^ 2 ≠ 0 := by positivity
  exact (((contDiff_norm_sq ℝ).contDiffAt).log hn).contDiffWithinAt

/-- `∂_{w̄} ℓ = w / |w|²` off `0`, and `ℓ` is real differentiable there. -/
theorem t21_ell_dzbar {w : ℂ} (hw : w ≠ 0) :
    DifferentiableAt ℝ (fun x : ℂ => ((Real.log (‖x‖ ^ 2) : ℝ) : ℂ)) w ∧
      dzbar (fun x : ℂ => ((Real.log (‖x‖ ^ 2) : ℝ) : ℂ)) w = w / ((‖w‖ ^ 2 : ℝ) : ℂ) := by
  have hn : ‖w‖ ^ 2 ≠ 0 := by positivity
  have h1 : HasFDerivAt (fun x : ℂ => ‖x‖ ^ 2) (2 • innerSL ℝ w) w :=
    (hasStrictFDerivAt_norm_sq w).hasFDerivAt
  have h2 := h1.log hn
  have h3 := Complex.ofRealCLM.hasFDerivAt.comp w h2
  refine ⟨h3.differentiableAt, ?_⟩
  have hd : fderiv ℝ (fun x : ℂ => ((Real.log (‖x‖ ^ 2) : ℝ) : ℂ)) w =
      Complex.ofRealCLM.comp (((‖w‖ ^ 2)⁻¹) • (2 • innerSL ℝ w)) := h3.fderiv
  simp only [dzbar, hd]
  simp [innerSL_apply_apply ℝ, Complex.inner]
  have e : ((‖w‖ : ℂ) ^ 2) = ((Complex.normSq w : ℝ) : ℂ) := by
    rw [← Complex.sq_norm]; push_cast; ring
  rw [e]
  apply Complex.ext
  · simp [Complex.div_ofReal_re]
    field_simp
  · simp [Complex.div_ofReal_im]
    field_simp

/-- `W` is `C¹` off `0`. -/
theorem t21_W_contDiff {U : ℂ → ℂ} (hU : DifferentiableOn ℂ U {0}ᶜ) (κ : ℂ) :
    ContDiffOn ℝ 1 (fun w : ℂ => (conj (U w) + conj κ * ((Real.log (‖w‖ ^ 2) : ℝ) : ℂ)) *
      (deriv U w + κ / w)) {0}ᶜ := by
  have hUs : ContDiffOn ℝ 1 U {0}ᶜ := (hU.contDiffOn isOpen_compl_singleton).restrict_scalars ℝ
  have hU' : DifferentiableOn ℂ (deriv U) {0}ᶜ := hU.deriv isOpen_compl_singleton
  have hUs' : ContDiffOn ℝ 1 (deriv U) {0}ᶜ := (hU'.contDiffOn isOpen_compl_singleton).restrict_scalars ℝ
  have hinv : ContDiffOn ℝ 1 (fun w : ℂ => w⁻¹) {0}ᶜ :=
    ((differentiableOn_inv.contDiffOn isOpen_compl_singleton).restrict_scalars ℝ)
  have hconj : ContDiffOn ℝ 1 (fun w : ℂ => conj (U w)) {0}ᶜ :=
    (Complex.conjCLE : ℂ →L[ℝ] ℂ).contDiff.comp_contDiffOn hUs
  have hV : ContDiffOn ℝ 1 (fun w : ℂ => deriv U w + κ / w) {0}ᶜ := by
    simpa only [div_eq_mul_inv] using hUs'.add (contDiffOn_const.mul hinv)
  exact (hconj.add (contDiffOn_const.mul t21_ell_contDiff)).mul hV

/-- `∂_{w̄} W = |U' + κ/w|²` off `0`. -/
theorem t21_W_dzbar {U : ℂ → ℂ} (hU : DifferentiableOn ℂ U {0}ᶜ) (κ : ℂ) {w : ℂ} (hw : w ≠ 0) :
    dzbar (fun w : ℂ => (conj (U w) + conj κ * ((Real.log (‖w‖ ^ 2) : ℝ) : ℂ)) *
      (deriv U w + κ / w)) w = ((‖deriv U w + κ / w‖ ^ 2 : ℝ) : ℂ) := by
  have hUd : DifferentiableAt ℂ U w := hU.differentiableAt (isOpen_compl_singleton.mem_nhds hw)
  have hU' : DifferentiableOn ℂ (deriv U) {0}ᶜ := hU.deriv isOpen_compl_singleton
  have hU'd : DifferentiableAt ℂ (deriv U) w := hU'.differentiableAt (isOpen_compl_singleton.mem_nhds hw)
  have hVd : DifferentiableAt ℂ (fun w : ℂ => deriv U w + κ / w) w := by
    exact hU'd.add (DifferentiableAt.div (differentiableAt_const κ) differentiableAt_id hw)
  have hVR : DifferentiableAt ℝ (fun w : ℂ => deriv U w + κ / w) w := hVd.restrictScalars ℝ
  have hcU : DifferentiableAt ℝ (fun x : ℂ => conj (U x)) w :=
    (Complex.conjCLE : ℂ →L[ℝ] ℂ).differentiableAt.comp w (hUd.restrictScalars ℝ)
  obtain ⟨hℓ, hℓz⟩ := t21_ell_dzbar hw
  have huR : DifferentiableAt ℝ (fun x : ℂ => conj (U x) + conj κ * ((Real.log (‖x‖ ^ 2) : ℝ) : ℂ)) w :=
    hcU.add (hℓ.const_mul _)
  have hdu : dzbar (fun x : ℂ => conj (U x) + conj κ * ((Real.log (‖x‖ ^ 2) : ℝ) : ℂ)) w =
      conj (deriv U w) + conj κ * (w / ((‖w‖ ^ 2 : ℝ) : ℂ)) := by
    have e1 : dzbar (fun x : ℂ => conj (U x)) w = conj (deriv U w) := by
      rw [dzbar_conj (hUd.restrictScalars ℝ), dz_eq_deriv hUd]
    have e2 : dzbar (fun x : ℂ => conj κ * ((Real.log (‖x‖ ^ 2) : ℝ) : ℂ)) w =
        conj κ * dzbar (fun x : ℂ => ((Real.log (‖x‖ ^ 2) : ℝ) : ℂ)) w := by
      simp only [dzbar, fderiv_const_mul hℓ, ContinuousLinearMap.coe_smul', Pi.smul_apply, smul_eq_mul]
      ring
    have e3 : dzbar (fun x : ℂ => conj (U x) + conj κ * ((Real.log (‖x‖ ^ 2) : ℝ) : ℂ)) w =
        dzbar (fun x : ℂ => conj (U x)) w + dzbar (fun x : ℂ => conj κ * ((Real.log (‖x‖ ^ 2) : ℝ) : ℂ)) w := by
      simp only [dzbar, fderiv_fun_add hcU (hℓ.const_mul _), ContinuousLinearMap.add_apply]
      ring
    rw [e3, e1, e2, hℓz]
  rw [dzbar_mul huR hVR, (cauchyRiemann_iff.1 hVd).2, hdu]
  have hwc : (conj w) ≠ 0 := by simpa using hw
  have hwn : ((‖w‖ ^ 2 : ℝ) : ℂ) = w * conj w := by
    rw [← Complex.normSq_eq_norm_sq, Complex.mul_conj]
  have hV2 : ((‖deriv U w + κ / w‖ ^ 2 : ℝ) : ℂ) =
      (deriv U w + κ / w) * conj (deriv U w + κ / w) := by
    rw [← Complex.normSq_eq_norm_sq, Complex.mul_conj]
  rw [hV2, hwn]
  simp only [map_add, map_div₀, mul_zero, zero_add]
  field_simp

/-! ## The gap identity -/

/-- The log-Green identity on the gap for `V = U' + κ/w`, in generic coefficients. -/
theorem t21_gap_generic {f g : ℂ → ℂ} (h : IsNormalizedDisjointPair f g) {P Q : ℕ → Polynomial ℂ}
    (hPQ : IsFaber f g P Q) (m : ℕ) (α β : ℕ → ℂ) (U : ℂ → ℂ)
    (hU : ∀ w : ℂ, U w = ∑ k ∈ Finset.range m, (α k * (P (k + 1)).eval w + β k * (Q (k + 1)).eval w⁻¹))
    (κ : ℂ) {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) :
    ∃ (D E : ℕ → ℂ) (c0f c0g : ℂ),
      (∀ j : ℕ, D j = ∑ k ∈ Finset.range m,
          (((k + 1 : ℕ) : ℂ) * α k * grunsky f g ((k : ℤ) + 1) (-((j : ℤ) + 1)) +
            ((k + 1 : ℕ) : ℂ) * β k * grunsky f g (-((k : ℤ) + 1)) (-((j : ℤ) + 1)))) ∧
      (∀ k : ℕ, E k = ∑ j ∈ Finset.range m,
          (((j + 1 : ℕ) : ℂ) * α j * grunsky f g ((j : ℤ) + 1) ((k : ℤ) + 1) +
            ((j + 1 : ℕ) : ℂ) * β j * grunsky f g ((k : ℤ) + 1) (-((j : ℤ) + 1)))) ∧
      c0f = ∑ k ∈ Finset.range m, ((k + 1 : ℕ) : ℂ) * α k * grunsky f g ((k : ℤ) + 1) 0 ∧
      c0g = -∑ j ∈ Finset.range m, ((j + 1 : ℕ) : ℂ) * β j * grunsky f g (-((j : ℤ) + 1)) 0 ∧
      Summable (fun j : ℕ => ((j + 1 : ℕ) : ℝ) *
        (‖D j + κ * (-grunsky f g (-((j : ℤ) + 1)) 0)‖ ^ 2 * ρ ^ (2 * (j + 1)))) ∧
      Summable (fun k : ℕ => ((k + 1 : ℕ) : ℝ) *
        (‖E k + κ * (-grunsky f g ((k : ℤ) + 1) 0)‖ ^ 2 * ρ ^ (2 * (k + 1)))) ∧
      ((∫ w in (f '' closedBall (0 : ℂ) ρ ∪ g '' {z : ℂ | 1 / ρ ≤ ‖z‖})ᶜ, ‖deriv U w + κ / w‖ ^ 2 : ℝ) : ℂ) =
        π * (
          (-(((∑' k : ℕ, ((k + 1 : ℕ) : ℝ) *
            (‖E k + κ * (-grunsky f g ((k : ℤ) + 1) 0)‖ ^ 2 * ρ ^ (2 * (k + 1))) -
          ∑ j ∈ Finset.range m, ((j + 1 : ℕ) : ℝ) * (‖α j‖ ^ 2 * (ρ ^ (2 * (j + 1)))⁻¹) : ℝ) : ℂ)) +
          κ * conj c0g +
          conj κ * ∑ j ∈ Finset.range m, ((j + 1 : ℕ) : ℂ) * (-grunsky f g ((j : ℤ) + 1) 0) * α j +
          conj κ * κ * ((Real.log (‖derivAtInfty g‖ ^ 2 * (ρ ^ 2)⁻¹) : ℝ) : ℂ)) -
          ((((∑' j : ℕ, ((j + 1 : ℕ) : ℝ) *
            (‖D j + κ * (-grunsky f g (-((j : ℤ) + 1)) 0)‖ ^ 2 * ρ ^ (2 * (j + 1))) -
          ∑ k ∈ Finset.range m, ((k + 1 : ℕ) : ℝ) * (‖β k‖ ^ 2 * (ρ ^ (2 * (k + 1)))⁻¹) : ℝ) : ℂ)) +
          κ * conj c0f -
          conj κ * ∑ k ∈ Finset.range m, ((k + 1 : ℕ) : ℂ) * (-grunsky f g (-((k : ℤ) + 1)) 0) * β k +
          conj κ * κ * ((Real.log (ρ ^ 2) : ℝ) : ℂ))) := by
  have hh := h
  obtain ⟨hfd, hfi, hf0, hf1, hgu, hdisj⟩ := hh
  obtain ⟨Df, c0f, hDf, hc0f, hsf, hAf⟩ := t21_f_side h hPQ m α β U hU κ hρ0 hρ1
  obtain ⟨Eg, c0g, hEg, hc0g, hsg, hAg⟩ := t21_g_side h hPQ m α β U hU κ hρ0 hρ1
  refine ⟨Df, Eg, c0f, c0g, hDf, hEg, hc0f, hc0g, hsf, hsg, ?_⟩
  have hUdiff : DifferentiableOn ℂ U {0}ᶜ := fun w hw =>
    (t21_U_diff m α β U hU hw).differentiableWithinAt
  have hG := mg_gap_green_gen h hρ0 hρ1 (t21_W_contDiff hUdiff κ)
  beta_reduce at hG
  rw [hAf, hAg] at hG
  have hgap : ∀ w ∈ (f '' closedBall (0 : ℂ) ρ ∪ g '' {z : ℂ | 1 / ρ ≤ ‖z‖})ᶜ, w ≠ 0 := by
    intro w hw hw0
    exact hw (Or.inl ⟨0, by simp [hρ0.le], by rw [hf0, hw0]⟩)
  have hKm : MeasurableSet (f '' closedBall (0 : ℂ) ρ ∪ g '' {z : ℂ | 1 / ρ ≤ ‖z‖})ᶜ := by
    have hR : 1 < 1 / ρ := one_lt_one_div hρ0 hρ1
    exact (((isCompact_closedBall (0 : ℂ) ρ).image_of_continuousOn (hfd.continuousOn.mono (fun z hz =>
      mem_ball_zero_iff.mpr (lt_of_le_of_lt (mem_closedBall_zero_iff.mp hz) hρ1)))).isClosed.union
        (mg_image_closed hgu hR)).measurableSet.compl
  have hint : (∫ w in (f '' closedBall (0 : ℂ) ρ ∪ g '' {z : ℂ | 1 / ρ ≤ ‖z‖})ᶜ, dzbar
      (fun w : ℂ => (conj (U w) + conj κ * ((Real.log (‖w‖ ^ 2) : ℝ) : ℂ)) * (deriv U w + κ / w)) w) =
      (((∫ w in (f '' closedBall (0 : ℂ) ρ ∪ g '' {z : ℂ | 1 / ρ ≤ ‖z‖})ᶜ, ‖deriv U w + κ / w‖ ^ 2 : ℝ)) : ℂ) := by
    rw [← integral_complex_ofReal]
    exact setIntegral_congr_fun hKm (fun w hw => t21_W_dzbar hUdiff κ (hgap w hw))
  rw [hint] at hG
  rw [hG]
  ring

/-! ## Specialization to the statement of `thm_2_1` -/

/-- Symmetry `b_{0l} = b_{l0}` for `l ≠ 0`. -/
theorem t21_b0sym {f g : ℂ → ℂ} (h : IsNormalizedDisjointPair f g) {l : ℤ} (hl : l ≠ 0) :
    grunsky f g 0 l = grunsky f g l 0 := by
  have hspec := grunsky_spec h
  have hc : ∃ j : ℕ, l = (j : ℤ) + 1 ∨ l = -((j : ℤ) + 1) := by
    rcases lt_or_gt_of_ne hl with hl' | hl'
    · exact ⟨(-l - 1).toNat, Or.inr (by omega)⟩
    · exact ⟨(l - 1).toNat, Or.inl (by omega)⟩
  obtain ⟨j, hj | hj⟩ := hc
  · subst hj
    have h1 := hspec.1.2.2.2.2 0 j
    simpa using h1
  · subst hj
    have h1 := (hspec.2 0 (j + 1)).2
    push_cast at h1
    simpa using h1

/-- Splitting a symmetric `Icc` sum. -/
theorem t21_Icc_split (F : ℤ → ℂ) (m : ℕ) :
    ∑ l ∈ Finset.Icc (-(m : ℤ)) m, F l =
      F 0 + ∑ i ∈ Finset.range m, (F ((i : ℤ) + 1) + F (-((i : ℤ) + 1))) := by
  rw [← mg_sum_erase F m, Finset.add_sum_erase _ _ (by simp)]

/-- Logarithm of `|g'(∞)|²`. -/
theorem t21_log_beta {f g : ℂ → ℂ} (h : IsNormalizedDisjointPair f g) :
    Real.log (‖derivAtInfty g‖ ^ 2) = 2 * (grunsky f g 0 0).re := by
  obtain ⟨hexp, -, -, -, -⟩ := (grunsky_spec h).1
  have : ‖derivAtInfty g‖ = Real.exp (grunsky f g 0 0).re := by
    rw [← hexp, Complex.norm_exp]
  rw [Real.log_pow, this, Real.log_exp]
  norm_num

/-- The finite-ρ identity of `thm_2_1` in the variables of the statement. -/
theorem t21_identity {f g : ℂ → ℂ} (h : IsNormalizedDisjointPair f g) (m : ℕ) (lam : ℤ → ℂ) :
    ∃ U : ℂ → ℂ, DifferentiableOn ℂ U {0}ᶜ ∧ ((∀ k : ℤ, k ≠ 0 → lam k = 0) → ∀ w, U w = 0) ∧
      ∀ ρ : ℝ, 0 < ρ → ρ < 1 →
      Summable (fun j : ℕ => ((j + 1 : ℕ) : ℝ) * (‖∑ l ∈ Finset.Icc (-(m : ℤ)) m,
          grunsky f g (-((j : ℤ) + 1)) l * lam l‖ ^ 2 * ρ ^ (2 * (j + 1)))) ∧
      Summable (fun k : ℕ => ((k + 1 : ℕ) : ℝ) * (‖∑ l ∈ Finset.Icc (-(m : ℤ)) m,
          grunsky f g ((k : ℤ) + 1) l * lam l‖ ^ 2 * ρ ^ (2 * (k + 1)))) ∧
      ((∑' j : ℕ, ((j + 1 : ℕ) : ℝ) * (‖∑ l ∈ Finset.Icc (-(m : ℤ)) m,
          grunsky f g (-((j : ℤ) + 1)) l * lam l‖ ^ 2 * ρ ^ (2 * (j + 1)))) +
        (∑' k : ℕ, ((k + 1 : ℕ) : ℝ) * (‖∑ l ∈ Finset.Icc (-(m : ℤ)) m,
          grunsky f g ((k : ℤ) + 1) l * lam l‖ ^ 2 * ρ ^ (2 * (k + 1)))) +
        (∫ w in (f '' closedBall (0 : ℂ) ρ ∪ g '' {z : ℂ | 1 / ρ ≤ ‖z‖})ᶜ,
          ‖deriv U w + (-lam 0) / w‖ ^ 2) / π =
        (∑ k ∈ Finset.range m, (‖lam ((k : ℤ) + 1)‖ ^ 2 + ‖lam (-((k : ℤ) + 1))‖ ^ 2) / ((k + 1 : ℕ) : ℝ) *
            (ρ ^ (2 * (k + 1)))⁻¹) +
          2 * (conj (lam 0) * ∑ l ∈ Finset.Icc (-(m : ℤ)) m, grunsky f g 0 l * lam l).re -
          2 * ‖lam 0‖ ^ 2 * Real.log (ρ ^ 2)) := by
  obtain ⟨P, Q, hPQ⟩ := faber_exists h
  obtain ⟨α, hα⟩ : ∃ α : ℕ → ℂ, ∀ k, α k = lam ((k : ℤ) + 1) / ((k + 1 : ℕ) : ℂ) := ⟨_, fun _ => rfl⟩
  obtain ⟨β, hβ⟩ : ∃ β : ℕ → ℂ, ∀ k, β k = lam (-((k : ℤ) + 1)) / ((k + 1 : ℕ) : ℂ) := ⟨_, fun _ => rfl⟩
  obtain ⟨U, hU⟩ : ∃ U : ℂ → ℂ, ∀ w : ℂ, U w = ∑ k ∈ Finset.range m,
      (α k * (P (k + 1)).eval w + β k * (Q (k + 1)).eval w⁻¹) := ⟨_, fun _ => rfl⟩
  have hUdiff : DifferentiableOn ℂ U {0}ᶜ := fun w hw =>
    (t21_U_diff m α β U hU hw).differentiableWithinAt
  have hU0 : (∀ k : ℤ, k ≠ 0 → lam k = 0) → ∀ w, U w = 0 := by
    intro hz w
    rw [hU w]
    refine Finset.sum_eq_zero (fun k _ => ?_)
    rw [hα, hβ, hz _ (by omega), hz _ (by omega)]
    simp
  refine ⟨U, hUdiff, hU0, fun ρ hρ0 hρ1 => ?_⟩
  obtain ⟨D, E, c0f, c0g, hD, hE, hc0f, hc0g, hsf, hsg, hI⟩ :=
    t21_gap_generic h hPQ m α β U hU (-lam 0) hρ0 hρ1
  have hk1 : ∀ k : ℕ, ((k + 1 : ℕ) : ℂ) ≠ 0 := fun k => by exact_mod_cast Nat.succ_ne_zero k
  have mulα : ∀ k : ℕ, ((k + 1 : ℕ) : ℂ) * α k = lam ((k : ℤ) + 1) := fun k => by
    rw [hα]; field_simp [hk1 k]
  have mulβ : ∀ k : ℕ, ((k + 1 : ℕ) : ℂ) * β k = lam (-((k : ℤ) + 1)) := fun k => by
    rw [hβ]; field_simp [hk1 k]
  have hne1 : ∀ k : ℕ, ((k : ℤ) + 1 ≠ 0) := fun k => by omega
  have hne2 : ∀ k : ℕ, (-((k : ℤ) + 1) ≠ 0) := fun k => by omega
  -- the coefficients are the sums `T`
  have hDT : ∀ j : ℕ, D j + (-lam 0) * (-grunsky f g (-((j : ℤ) + 1)) 0) =
      ∑ l ∈ Finset.Icc (-(m : ℤ)) m, grunsky f g (-((j : ℤ) + 1)) l * lam l := by
    intro j
    rw [t21_Icc_split (fun l => grunsky f g (-((j : ℤ) + 1)) l * lam l) m, hD j]
    have : ∀ i ∈ Finset.range m,
        (((i + 1 : ℕ) : ℂ) * α i * grunsky f g ((i : ℤ) + 1) (-((j : ℤ) + 1)) +
          ((i + 1 : ℕ) : ℂ) * β i * grunsky f g (-((i : ℤ) + 1)) (-((j : ℤ) + 1))) =
        (grunsky f g (-((j : ℤ) + 1)) ((i : ℤ) + 1) * lam ((i : ℤ) + 1) +
          grunsky f g (-((j : ℤ) + 1)) (-((i : ℤ) + 1)) * lam (-((i : ℤ) + 1))) := by
      intro i _
      rw [mulα i, mulβ i, mg_gsym h _ _ (hne1 i) (hne2 j), mg_gsym h _ _ (hne2 i) (hne2 j)]
      ring
    rw [Finset.sum_congr rfl this]
    ring
  have hET : ∀ k : ℕ, E k + (-lam 0) * (-grunsky f g ((k : ℤ) + 1) 0) =
      ∑ l ∈ Finset.Icc (-(m : ℤ)) m, grunsky f g ((k : ℤ) + 1) l * lam l := by
    intro k
    rw [t21_Icc_split (fun l => grunsky f g ((k : ℤ) + 1) l * lam l) m, hE k]
    have : ∀ i ∈ Finset.range m,
        (((i + 1 : ℕ) : ℂ) * α i * grunsky f g ((i : ℤ) + 1) ((k : ℤ) + 1) +
          ((i + 1 : ℕ) : ℂ) * β i * grunsky f g ((k : ℤ) + 1) (-((i : ℤ) + 1))) =
        (grunsky f g ((k : ℤ) + 1) ((i : ℤ) + 1) * lam ((i : ℤ) + 1) +
          grunsky f g ((k : ℤ) + 1) (-((i : ℤ) + 1)) * lam (-((i : ℤ) + 1))) := by
      intro i _
      rw [mulα i, mulβ i, mg_gsym h _ _ (hne1 i) (hne1 k)]
      ring
    rw [Finset.sum_congr rfl this]
    ring
  simp only [hDT] at hsf hI
  simp only [hET] at hsg hI
  refine ⟨hsf, hsg, ?_⟩
  obtain ⟨Bp, hBp⟩ : ∃ Bp : ℂ, Bp = ∑ i ∈ Finset.range m, lam ((i : ℤ) + 1) * grunsky f g ((i : ℤ) + 1) 0 :=
    ⟨_, rfl⟩
  obtain ⟨Bn, hBn⟩ : ∃ Bn : ℂ, Bn = ∑ i ∈ Finset.range m, lam (-((i : ℤ) + 1)) * grunsky f g (-((i : ℤ) + 1)) 0 :=
    ⟨_, rfl⟩
  have hc0f' : c0f = Bp := by
    rw [hc0f, hBp]
    exact Finset.sum_congr rfl (fun i _ => by rw [mulα i])
  have hc0g' : c0g = -Bn := by
    rw [hc0g, hBn]
    congr 1
    exact Finset.sum_congr rfl (fun i _ => by rw [mulβ i])
  have hS1 : ∑ j ∈ Finset.range m, ((j + 1 : ℕ) : ℂ) * (-grunsky f g ((j : ℤ) + 1) 0) * α j = -Bp := by
    rw [hBp, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    calc ((j + 1 : ℕ) : ℂ) * (-grunsky f g ((j : ℤ) + 1) 0) * α j
        = -(grunsky f g ((j : ℤ) + 1) 0 * (((j + 1 : ℕ) : ℂ) * α j)) := by ring
      _ = _ := by rw [mulα j]; ring
  have hS2 : ∑ k ∈ Finset.range m, ((k + 1 : ℕ) : ℂ) * (-grunsky f g (-((k : ℤ) + 1)) 0) * β k = -Bn := by
    rw [hBn, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    calc ((k + 1 : ℕ) : ℂ) * (-grunsky f g (-((k : ℤ) + 1)) 0) * β k
        = -(grunsky f g (-((k : ℤ) + 1)) 0 * (((k + 1 : ℕ) : ℂ) * β k)) := by ring
      _ = _ := by rw [mulβ k]; ring
  have hB0 : ∑ l ∈ Finset.Icc (-(m : ℤ)) m, grunsky f g 0 l * lam l = grunsky f g 0 0 * lam 0 + (Bp + Bn) := by
    rw [t21_Icc_split (fun l => grunsky f g 0 l * lam l) m, hBp, hBn, ← Finset.sum_add_distrib]
    congr 1
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [t21_b0sym h (hne1 i), t21_b0sym h (hne2 i)]
    ring
  have hAw : ∀ k : ℕ, ((k + 1 : ℕ) : ℝ) * (‖α k‖ ^ 2 * (ρ ^ (2 * (k + 1)))⁻¹) +
      ((k + 1 : ℕ) : ℝ) * (‖β k‖ ^ 2 * (ρ ^ (2 * (k + 1)))⁻¹) =
      (‖lam ((k : ℤ) + 1)‖ ^ 2 + ‖lam (-((k : ℤ) + 1))‖ ^ 2) / ((k + 1 : ℕ) : ℝ) *
        (ρ ^ (2 * (k + 1)))⁻¹ := by
    intro k
    have hkr : ((k + 1 : ℕ) : ℝ) ≠ 0 := by positivity
    rw [hα, hβ, norm_div, norm_div, Complex.norm_natCast]
    field_simp
  have hAsum : (∑ j ∈ Finset.range m, ((j + 1 : ℕ) : ℝ) * (‖α j‖ ^ 2 * (ρ ^ (2 * (j + 1)))⁻¹)) +
      (∑ j ∈ Finset.range m, ((j + 1 : ℕ) : ℝ) * (‖β j‖ ^ 2 * (ρ ^ (2 * (j + 1)))⁻¹)) =
      ∑ k ∈ Finset.range m, (‖lam ((k : ℤ) + 1)‖ ^ 2 + ‖lam (-((k : ℤ) + 1))‖ ^ 2) / ((k + 1 : ℕ) : ℝ) *
        (ρ ^ (2 * (k + 1)))⁻¹ := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun k _ => hAw k)
  have hβ0 : ‖derivAtInfty g‖ ^ 2 ≠ 0 := by
    obtain ⟨hexp, -, -, -, -⟩ := (grunsky_spec h).1
    have : derivAtInfty g ≠ 0 := by rw [← hexp]; exact Complex.exp_ne_zero _
    positivity
  have hLlog : Real.log (‖derivAtInfty g‖ ^ 2 * (ρ ^ 2)⁻¹) =
      2 * (grunsky f g 0 0).re - Real.log (ρ ^ 2) := by
    rw [Real.log_mul hβ0 (inv_ne_zero (by positivity)), Real.log_inv, t21_log_beta h]
    ring
  have hre : ∀ z : ℂ, ((2 * z.re : ℝ) : ℂ) = z + conj z := fun z => (Complex.add_conj z).symm
  have hnorm : ((‖lam 0‖ ^ 2 : ℝ) : ℂ) = lam 0 * conj (lam 0) := by
    rw [← Complex.normSq_eq_norm_sq, Complex.mul_conj]
  rw [hB0]
  generalize (∑' j : ℕ, ((j + 1 : ℕ) : ℝ) * (‖∑ l ∈ Finset.Icc (-(m : ℤ)) m,
      grunsky f g (-((j : ℤ) + 1)) l * lam l‖ ^ 2 * ρ ^ (2 * (j + 1)))) = Sf at hI ⊢
  generalize (∑' k : ℕ, ((k + 1 : ℕ) : ℝ) * (‖∑ l ∈ Finset.Icc (-(m : ℤ)) m,
      grunsky f g ((k : ℤ) + 1) l * lam l‖ ^ 2 * ρ ^ (2 * (k + 1)))) = Sg at hI ⊢
  generalize (∫ w in (f '' closedBall (0 : ℂ) ρ ∪ g '' {z : ℂ | 1 / ρ ≤ ‖z‖})ᶜ,
      ‖deriv U w + (-lam 0) / w‖ ^ 2) = I at hI ⊢
  rw [← hAsum]
  generalize (∑ j ∈ Finset.range m, ((j + 1 : ℕ) : ℝ) * (‖α j‖ ^ 2 * (ρ ^ (2 * (j + 1)))⁻¹)) = Aα at hI ⊢
  generalize (∑ j ∈ Finset.range m, ((j + 1 : ℕ) : ℝ) * (‖β j‖ ^ 2 * (ρ ^ (2 * (j + 1)))⁻¹)) = Aβ at hI ⊢
  apply Complex.ofReal_injective
  have hIπ : ((I / π : ℝ) : ℂ) = ((I : ℝ) : ℂ) / (π : ℂ) := by push_cast; ring
  rw [Complex.ofReal_add, Complex.ofReal_add, hIπ, hI]
  rw [hc0f', hc0g', hS1, hS2, hLlog] at *
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hnorm' : ((‖lam 0‖ : ℝ) : ℂ) ^ 2 = lam 0 * conj (lam 0) := by
    rw [← Complex.ofReal_pow]; exact hnorm
  push_cast
  simp only [Complex.re_eq_add_conj, hnorm', map_add, map_mul, map_neg, map_sub, map_div₀,
    Complex.conj_ofReal, Complex.conj_conj]
  field_simp
  ring

/-! ## The limit `ρ ↑ 1` -/

/-- Integrability of a function continuous off `0` on the gap. -/
theorem t21_gap_integrable {f g : ℂ → ℂ} (h : IsNormalizedDisjointPair f g) {ρ : ℝ} (hρ0 : 0 < ρ)
    (hρ1 : ρ < 1) {φ : ℂ → ℝ} (hφ : ContinuousOn φ {0}ᶜ) :
    IntegrableOn φ (f '' closedBall (0 : ℂ) ρ ∪ g '' {z : ℂ | 1 / ρ ≤ ‖z‖})ᶜ := by
  have h' := h
  obtain ⟨hfd, hfi, hf0, hf1, hgu, hdisj⟩ := h
  obtain ⟨R1, hR1⟩ := mg_far_exterior h' (T := 1 / ρ) (by positivity)
  set C : Set ℂ := closedBall (0 : ℂ) R1 ∩ (f '' ball (0 : ℂ) ρ)ᶜ with hC
  have hopen : IsOpen (f '' ball (0 : ℂ) ρ) :=
    (RMT.differentiableOn_invFunOn_of_injOn isOpen_ball (hfd.mono (ball_subset_ball hρ1.le))
      (hfi.mono (ball_subset_ball hρ1.le))).1
  have hCc : IsCompact C := (isCompact_closedBall (0 : ℂ) R1).inter_right hopen.isClosed_compl
  have hC0 : C ⊆ {0}ᶜ := by
    intro w hw h0
    exact hw.2 ⟨0, mem_ball_self hρ0, by rw [hf0, mem_singleton_iff.mp h0]⟩
  refine ((hφ.mono hC0).integrableOn_compact hCc).mono_set ?_
  intro w hw
  refine ⟨?_, fun hm => hw (Or.inl (image_mono ball_subset_closedBall hm))⟩
  by_contra hnot
  obtain ⟨z, hz, hzw⟩ := hR1 w (not_le.mp (by simpa [mem_closedBall_zero_iff] using hnot))
  exact hw (Or.inr ⟨z, hz, hzw⟩)

/-- The complement `F` lies in every gap. -/
theorem t21_F_subset_gap {f g : ℂ → ℂ} {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) :
    (f '' unitDisc ∪ g '' unitDiscExterior)ᶜ ⊆ (f '' closedBall (0 : ℂ) ρ ∪ g '' {z : ℂ | 1 / ρ ≤ ‖z‖})ᶜ := by
  intro w hw hw'
  apply hw
  rcases hw' with ⟨z, hz, rfl⟩ | ⟨z, hz, rfl⟩
  · exact Or.inl ⟨z, mem_ball_zero_iff.mpr (lt_of_le_of_lt (mem_closedBall_zero_iff.mp hz) hρ1), rfl⟩
  · exact Or.inr ⟨z, lt_of_lt_of_le (one_lt_one_div hρ0 hρ1) hz, rfl⟩

/-- Two-sided sums from the two halves. -/
theorem t21_int_sum (F : ℤ → ℝ) (h0 : F 0 = 0) (hp : Summable (fun j : ℕ => F ((j + 1 : ℕ) : ℤ)))
    (hn : Summable (fun j : ℕ => F (-((j : ℤ) + 1)))) :
    Summable F ∧ ∑' k : ℤ, F k = (∑' j : ℕ, F ((j + 1 : ℕ) : ℤ)) + ∑' j : ℕ, F (-((j : ℤ) + 1)) := by
  have hs : Summable F := Summable.of_nat_of_neg_add_one ((summable_nat_add_iff 1).mp hp) hn
  exact ⟨hs, mg_tsum_int_split hs h0⟩

/-- The limit `ρ ↑ 1` of the finite-`ρ` identity. -/
theorem t21_core {f g : ℂ → ℂ} (h : IsNormalizedDisjointPair f g) (m : ℕ) (lam : ℤ → ℂ) :
    ∃ (U : ℂ → ℂ) (r : ℕ → ℝ), DifferentiableOn ℂ U {0}ᶜ ∧ (∀ n, 0 < r n ∧ r n < 1) ∧ Monotone r ∧
      Tendsto r atTop (𝓝 1) ∧ ((∀ k : ℤ, k ≠ 0 → lam k = 0) → ∀ w, U w = 0) ∧
      Summable (fun j : ℕ => ((j + 1 : ℕ) : ℝ) *
        ‖∑ l ∈ Finset.Icc (-(m : ℤ)) m, grunsky f g ((j : ℤ) + 1) l * lam l‖ ^ 2) ∧
      Summable (fun j : ℕ => ((j + 1 : ℕ) : ℝ) *
        ‖∑ l ∈ Finset.Icc (-(m : ℤ)) m, grunsky f g (-((j : ℤ) + 1)) l * lam l‖ ^ 2) ∧
      ((∑' j : ℕ, ((j + 1 : ℕ) : ℝ) * ‖∑ l ∈ Finset.Icc (-(m : ℤ)) m, grunsky f g ((j : ℤ) + 1) l * lam l‖ ^ 2) +
        (∑' j : ℕ, ((j + 1 : ℕ) : ℝ) * ‖∑ l ∈ Finset.Icc (-(m : ℤ)) m, grunsky f g (-((j : ℤ) + 1)) l * lam l‖ ^ 2) ≤
          (∑ k ∈ (Finset.Icc (-(m : ℤ)) m).erase 0, ‖lam k‖ ^ 2 / |(k : ℝ)|) +
            2 * (conj (lam 0) * ∑ l ∈ Finset.Icc (-(m : ℤ)) m, grunsky f g 0 l * lam l).re) ∧
      ((Tendsto (fun n => ∫ w in (f '' closedBall (0 : ℂ) (r n) ∪ g '' {z : ℂ | 1 / r n ≤ ‖z‖})ᶜ,
          ‖deriv U w + (-lam 0) / w‖ ^ 2) atTop (𝓝 0)) →
        (∑ k ∈ (Finset.Icc (-(m : ℤ)) m).erase 0, ‖lam k‖ ^ 2 / |(k : ℝ)|) +
            2 * (conj (lam 0) * ∑ l ∈ Finset.Icc (-(m : ℤ)) m, grunsky f g 0 l * lam l).re ≤
          (∑' j : ℕ, ((j + 1 : ℕ) : ℝ) * ‖∑ l ∈ Finset.Icc (-(m : ℤ)) m, grunsky f g ((j : ℤ) + 1) l * lam l‖ ^ 2) +
        (∑' j : ℕ, ((j + 1 : ℕ) : ℝ) * ‖∑ l ∈ Finset.Icc (-(m : ℤ)) m, grunsky f g (-((j : ℤ) + 1)) l * lam l‖ ^ 2)) ∧
      ((∑' j : ℕ, ((j + 1 : ℕ) : ℝ) * ‖∑ l ∈ Finset.Icc (-(m : ℤ)) m, grunsky f g ((j : ℤ) + 1) l * lam l‖ ^ 2) +
        (∑' j : ℕ, ((j + 1 : ℕ) : ℝ) * ‖∑ l ∈ Finset.Icc (-(m : ℤ)) m, grunsky f g (-((j : ℤ) + 1)) l * lam l‖ ^ 2) =
          (∑ k ∈ (Finset.Icc (-(m : ℤ)) m).erase 0, ‖lam k‖ ^ 2 / |(k : ℝ)|) +
            2 * (conj (lam 0) * ∑ l ∈ Finset.Icc (-(m : ℤ)) m, grunsky f g 0 l * lam l).re →
        Tendsto (fun n => ∫ w in (f '' closedBall (0 : ℂ) (r n) ∪ g '' {z : ℂ | 1 / r n ≤ ‖z‖})ᶜ,
          ‖deriv U w + (-lam 0) / w‖ ^ 2) atTop (𝓝 0)) := by
  obtain ⟨U, hUd, hU0, hid⟩ := t21_identity h m lam
  obtain ⟨r, hr, hmono, hlim⟩ := mg_radius_seq
  obtain ⟨a, ha⟩ : ∃ a : ℕ → ℝ, ∀ j, a j = ((j + 1 : ℕ) : ℝ) *
      ‖∑ l ∈ Finset.Icc (-(m : ℤ)) m, grunsky f g ((j : ℤ) + 1) l * lam l‖ ^ 2 := ⟨_, fun _ => rfl⟩
  obtain ⟨c, hc⟩ : ∃ c : ℕ → ℝ, ∀ j, c j = ((j + 1 : ℕ) : ℝ) *
      ‖∑ l ∈ Finset.Icc (-(m : ℤ)) m, grunsky f g (-((j : ℤ) + 1)) l * lam l‖ ^ 2 := ⟨_, fun _ => rfl⟩
  obtain ⟨w, hw⟩ : ∃ w : ℕ → ℝ, ∀ k, w k = (‖lam ((k : ℤ) + 1)‖ ^ 2 + ‖lam (-((k : ℤ) + 1))‖ ^ 2) /
      ((k + 1 : ℕ) : ℝ) := ⟨_, fun _ => rfl⟩
  obtain ⟨X, hX⟩ : ∃ X : ℝ, X = 2 * (conj (lam 0) *
      ∑ l ∈ Finset.Icc (-(m : ℤ)) m, grunsky f g 0 l * lam l).re := ⟨_, rfl⟩
  obtain ⟨I, hI⟩ : ∃ I : ℕ → ℝ, ∀ n, I n = ∫ w in (f '' closedBall (0 : ℂ) (r n) ∪
      g '' {z : ℂ | 1 / r n ≤ ‖z‖})ᶜ, ‖deriv U w + (-lam 0) / w‖ ^ 2 := ⟨_, fun _ => rfl⟩
  have ha0 : ∀ j, 0 ≤ a j := fun j => by rw [ha]; positivity
  have hc0 : ∀ j, 0 ≤ c j := fun j => by rw [hc]; positivity
  have hpi : 0 < π := Real.pi_pos
  have hI0 : ∀ n, 0 ≤ I n := fun n => by rw [hI]; exact integral_nonneg (fun w => by positivity)
  have hR1 : (∑ k ∈ (Finset.Icc (-(m : ℤ)) m).erase 0, ‖lam k‖ ^ 2 / |(k : ℝ)|) =
      ∑ k ∈ Finset.range m, w k := by
    rw [mg_sum_erase (fun k : ℤ => ‖lam k‖ ^ 2 / |(k : ℝ)|) m]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [hw]
    have h1 : |(((k : ℤ) + 1 : ℤ) : ℝ)| = ((k + 1 : ℕ) : ℝ) := by
      push_cast; exact abs_of_nonneg (by positivity)
    have h2 : |((-((k : ℤ) + 1) : ℤ) : ℝ)| = ((k + 1 : ℕ) : ℝ) := by
      push_cast; rw [abs_neg]; exact abs_of_nonneg (by positivity)
    simp only [h1, h2, add_div]
  rw [← hX, hR1]
  -- the per-radius data
  have hSa : ∀ n, Summable (fun j : ℕ => a j * (r n) ^ (2 * (j + 1))) ∧
      Summable (fun j : ℕ => c j * (r n) ^ (2 * (j + 1))) ∧
      (∑' j : ℕ, c j * (r n) ^ (2 * (j + 1))) + (∑' j : ℕ, a j * (r n) ^ (2 * (j + 1))) + I n / π =
        (∑ k ∈ Finset.range m, w k * ((r n) ^ (2 * (k + 1)))⁻¹) + X -
          2 * ‖lam 0‖ ^ 2 * Real.log ((r n) ^ 2) := by
    intro n
    obtain ⟨h1, h2, h3⟩ := hid (r n) (hr n).1 (hr n).2
    refine ⟨h2.congr (fun j => by rw [ha, mul_assoc]), h1.congr (fun j => by rw [hc, mul_assoc]), ?_⟩
    rw [← hI n] at h3
    simp only [ha, hc, mul_assoc, hw, hX] at h3 ⊢
    exact h3
  have hwlim : ∀ j : ℕ, Tendsto (fun n => (r n) ^ (2 * (j + 1))) atTop (𝓝 1) := fun j => by
    simpa using hlim.pow (2 * (j + 1))
  have hwle : ∀ n j : ℕ, (r n) ^ (2 * (j + 1)) ≤ 1 := fun n j => pow_le_one₀ (hr n).1.le (hr n).2.le
  have hlog : Tendsto (fun n => Real.log ((r n) ^ 2)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun n => (r n) ^ 2) atTop (𝓝 1) := by simpa using hlim.pow 2
    simpa using h1.log (by norm_num)
  have hRlim : Tendsto (fun n => (∑ k ∈ Finset.range m, w k * ((r n) ^ (2 * (k + 1)))⁻¹) + X -
      2 * ‖lam 0‖ ^ 2 * Real.log ((r n) ^ 2)) atTop (𝓝 ((∑ k ∈ Finset.range m, w k) + X)) := by
    have h1 : Tendsto (fun n => ∑ k ∈ Finset.range m, w k * ((r n) ^ (2 * (k + 1)))⁻¹) atTop
        (𝓝 (∑ k ∈ Finset.range m, w k)) := by
      have := tendsto_finset_sum (Finset.range m) (fun k _ => ((hwlim k).inv₀ (by norm_num)).const_mul (w k))
      simpa using this
    have := (h1.add_const X).sub (hlog.const_mul (2 * ‖lam 0‖ ^ 2))
    simpa using this
  have hbound : ∀ N : ℕ, ∑ j ∈ Finset.range N, (a j + c j) ≤ (∑ k ∈ Finset.range m, w k) + X := by
    intro N
    have h1 : ∀ n, ∑ j ∈ Finset.range N, (a j + c j) * (r n) ^ (2 * (j + 1)) ≤
        (∑ k ∈ Finset.range m, w k * ((r n) ^ (2 * (k + 1)))⁻¹) + X -
          2 * ‖lam 0‖ ^ 2 * Real.log ((r n) ^ 2) := by
      intro n
      obtain ⟨hs1, hs2, he⟩ := hSa n
      have hw0 : 0 < r n := (hr n).1
      have h2 : ∑ j ∈ Finset.range N, (a j * (r n) ^ (2 * (j + 1)) + c j * (r n) ^ (2 * (j + 1))) ≤
          ∑' j : ℕ, (a j * (r n) ^ (2 * (j + 1)) + c j * (r n) ^ (2 * (j + 1))) :=
        Summable.sum_le_tsum (Finset.range N) (fun j _ => by
          have := ha0 j; have := hc0 j; positivity) (hs1.add hs2)
      have h3 := hs1.tsum_add hs2
      have h5 : 0 ≤ I n / π := div_nonneg (hI0 n) hpi.le
      calc ∑ j ∈ Finset.range N, (a j + c j) * (r n) ^ (2 * (j + 1))
          = ∑ j ∈ Finset.range N, (a j * (r n) ^ (2 * (j + 1)) + c j * (r n) ^ (2 * (j + 1))) :=
            Finset.sum_congr rfl (fun j _ => add_mul _ _ _)
        _ ≤ _ := h2
        _ = _ := h3
        _ ≤ _ := by linarith
    have h2 : Tendsto (fun n => ∑ j ∈ Finset.range N, (a j + c j) * (r n) ^ (2 * (j + 1))) atTop
        (𝓝 (∑ j ∈ Finset.range N, (a j + c j))) := by
      have := tendsto_finset_sum (Finset.range N) (fun j _ => (hwlim j).const_mul (a j + c j))
      simpa using this
    exact le_of_tendsto_of_tendsto h2 hRlim (Eventually.of_forall h1)
  have hsum : Summable (fun j => a j + c j) :=
    summable_of_sum_range_le (fun j => add_nonneg (ha0 j) (hc0 j)) hbound
  have hle : ∑' j, (a j + c j) ≤ (∑ k ∈ Finset.range m, w k) + X :=
    Real.tsum_le_of_sum_range_le (fun j => add_nonneg (ha0 j) (hc0 j)) hbound
  have hsa : Summable a := Summable.of_nonneg_of_le ha0 (fun j => le_add_of_nonneg_right (hc0 j)) hsum
  have hsc : Summable c := Summable.of_nonneg_of_le hc0 (fun j => le_add_of_nonneg_left (ha0 j)) hsum
  have hAC : (∑' j, a j) + (∑' j, c j) = ∑' j, (a j + c j) := (hsa.tsum_add hsc).symm
  have hA' : (fun j : ℕ => ((j + 1 : ℕ) : ℝ) *
      ‖∑ l ∈ Finset.Icc (-(m : ℤ)) m, grunsky f g ((j : ℤ) + 1) l * lam l‖ ^ 2) = a :=
    funext (fun j => (ha j).symm)
  have hC' : (fun j : ℕ => ((j + 1 : ℕ) : ℝ) *
      ‖∑ l ∈ Finset.Icc (-(m : ℤ)) m, grunsky f g (-((j : ℤ) + 1)) l * lam l‖ ^ 2) = c :=
    funext (fun j => (hc j).symm)
  rw [hA', hC']
  refine ⟨U, r, hUd, hr, hmono, hlim, hU0, hsa, hsc, hAC ▸ hle, ?_, ?_⟩
  · intro hI0lim
    rw [hAC]
    have h1 : ∀ n, (∑ k ∈ Finset.range m, w k * ((r n) ^ (2 * (k + 1)))⁻¹) + X -
        2 * ‖lam 0‖ ^ 2 * Real.log ((r n) ^ 2) - I n / π ≤ ∑' j, (a j + c j) := by
      intro n
      obtain ⟨hs1, hs2, he⟩ := hSa n
      have : (∑' j : ℕ, c j * (r n) ^ (2 * (j + 1))) + (∑' j : ℕ, a j * (r n) ^ (2 * (j + 1))) ≤
          ∑' j, (a j + c j) := by
        rw [add_comm, ← hs1.tsum_add hs2]
        refine Summable.tsum_le_tsum (fun j => add_le_add ?_ ?_) (hs1.add hs2) hsum
        · exact mul_le_of_le_one_right (ha0 j) (hwle n j)
        · exact mul_le_of_le_one_right (hc0 j) (hwle n j)
      linarith [he]
    have hIl : Tendsto (fun n => I n / π) atTop (𝓝 0) := by
      have := (hI0lim.congr (fun n => (hI n).symm)).div_const π
      simpa using this
    have := hRlim.sub hIl
    simp only [sub_zero] at this
    exact le_of_tendsto' this h1
  · intro heq
    rw [hAC] at heq
    have hdom : ∀ (x : ℕ → ℝ), (∀ j, 0 ≤ x j) → Summable x →
        Tendsto (fun n => ∑' j : ℕ, x j * (r n) ^ (2 * (j + 1))) atTop (𝓝 (∑' j, x j)) := by
      intro x hx0 hxs
      refine tendsto_tsum_of_dominated_convergence (𝓕 := atTop)
        (f := fun n j => x j * (r n) ^ (2 * (j + 1))) (g := x) (bound := x) hxs
        (fun j => by simpa using (hwlim j).const_mul (x j))
        (Eventually.of_forall (fun n j => ?_))
      rw [Real.norm_of_nonneg (mul_nonneg (hx0 j) (by have := (hr n).1; positivity))]
      exact mul_le_of_le_one_right (hx0 j) (hwle n j)
    have hSl : Tendsto (fun n => (∑' j : ℕ, c j * (r n) ^ (2 * (j + 1))) +
        (∑' j : ℕ, a j * (r n) ^ (2 * (j + 1)))) atTop (𝓝 ((∑' j, c j) + ∑' j, a j)) :=
      (hdom c hc0 hsc).add (hdom a ha0 hsa)
    have hIl : Tendsto (fun n => I n / π) atTop (𝓝 0) := by
      have h1 : ∀ n, I n / π = ((∑ k ∈ Finset.range m, w k * ((r n) ^ (2 * (k + 1)))⁻¹) + X -
          2 * ‖lam 0‖ ^ 2 * Real.log ((r n) ^ 2)) - ((∑' j : ℕ, c j * (r n) ^ (2 * (j + 1))) +
            (∑' j : ℕ, a j * (r n) ^ (2 * (j + 1)))) := by
        intro n
        have := (hSa n).2.2
        linarith
      have := hRlim.sub hSl
      rw [show (∑ k ∈ Finset.range m, w k) + X - ((∑' j, c j) + ∑' j, a j) = 0 by linarith] at this
      exact this.congr (fun n => (h1 n).symm)
    have := hIl.mul_const π
    simp only [zero_mul] at this
    refine this.congr (fun n => ?_)
    rw [hI]
    field_simp

/-- Two-sided Grunsky sum from the two halves. -/
theorem t21_lhs {f g : ℂ → ℂ} (m : ℕ) (lam : ℤ → ℂ)
    (hp : Summable (fun j : ℕ => ((j + 1 : ℕ) : ℝ) *
      ‖∑ l ∈ Finset.Icc (-(m : ℤ)) m, grunsky f g ((j : ℤ) + 1) l * lam l‖ ^ 2))
    (hn : Summable (fun j : ℕ => ((j + 1 : ℕ) : ℝ) *
      ‖∑ l ∈ Finset.Icc (-(m : ℤ)) m, grunsky f g (-((j : ℤ) + 1)) l * lam l‖ ^ 2)) :
    (∑' k : ℤ, |(k : ℝ)| * ‖∑ l ∈ Finset.Icc (-(m : ℤ)) m, grunsky f g k l * lam l‖ ^ 2) =
      (∑' j : ℕ, ((j + 1 : ℕ) : ℝ) *
        ‖∑ l ∈ Finset.Icc (-(m : ℤ)) m, grunsky f g ((j : ℤ) + 1) l * lam l‖ ^ 2) +
      ∑' j : ℕ, ((j + 1 : ℕ) : ℝ) *
        ‖∑ l ∈ Finset.Icc (-(m : ℤ)) m, grunsky f g (-((j : ℤ) + 1)) l * lam l‖ ^ 2 := by
  obtain ⟨F, hF⟩ : ∃ F : ℤ → ℝ, ∀ k, F k = |(k : ℝ)| *
      ‖∑ l ∈ Finset.Icc (-(m : ℤ)) m, grunsky f g k l * lam l‖ ^ 2 := ⟨_, fun _ => rfl⟩
  have hFp : ∀ j : ℕ, F ((j + 1 : ℕ) : ℤ) = ((j + 1 : ℕ) : ℝ) *
      ‖∑ l ∈ Finset.Icc (-(m : ℤ)) m, grunsky f g ((j : ℤ) + 1) l * lam l‖ ^ 2 := fun j => by
    rw [hF]
    have : (((j + 1 : ℕ) : ℤ) : ℝ) = ((j + 1 : ℕ) : ℝ) := by push_cast; ring
    rw [this, abs_of_nonneg (by positivity)]
    push_cast
    rfl
  have hFn : ∀ j : ℕ, F (-((j : ℤ) + 1)) = ((j + 1 : ℕ) : ℝ) *
      ‖∑ l ∈ Finset.Icc (-(m : ℤ)) m, grunsky f g (-((j : ℤ) + 1)) l * lam l‖ ^ 2 := fun j => by
    rw [hF]
    have : (((-((j : ℤ) + 1) : ℤ)) : ℝ) = -((j + 1 : ℕ) : ℝ) := by push_cast; ring
    rw [this, abs_neg, abs_of_nonneg (by positivity)]
  have hF0 : F 0 = 0 := by rw [hF]; simp
  have hp' : Summable (fun j : ℕ => F ((j + 1 : ℕ) : ℤ)) := by simp_rw [hFp]; exact hp
  have hn' : Summable (fun j : ℕ => F (-((j : ℤ) + 1))) := by simp_rw [hFn]; exact hn
  have := (t21_int_sum F hF0 hp' hn').2
  simp_rw [← hF]
  rw [this]
  simp_rw [hFp, hFn]

/-- **Theorem 2.1** (Hummel), the generalized Grunsky inequality and its equality case
(copy of `Ch2.thm_2_1`). -/
theorem mg_thm_2_1 {f g : ℂ → ℂ} (h : IsNormalizedDisjointPair f g) (m : ℕ) :
    (∀ lam : ℤ → ℂ,
      (∑' k : ℤ, |(k : ℝ)| * ‖∑ l ∈ Finset.Icc (-(m : ℤ)) m, grunsky f g k l * lam l‖ ^ 2) ≤
        (∑ k ∈ (Finset.Icc (-(m : ℤ)) m).erase 0, ‖lam k‖ ^ 2 / |(k : ℝ)|) +
          2 * (conj (lam 0) * ∑ l ∈ Finset.Icc (-(m : ℤ)) m, grunsky f g 0 l * lam l).re) ∧
      ((∀ lam : ℤ → ℂ,
        (∑' k : ℤ, |(k : ℝ)| * ‖∑ l ∈ Finset.Icc (-(m : ℤ)) m, grunsky f g k l * lam l‖ ^ 2) =
          (∑ k ∈ (Finset.Icc (-(m : ℤ)) m).erase 0, ‖lam k‖ ^ 2 / |(k : ℝ)|) +
            2 * (conj (lam 0) * ∑ l ∈ Finset.Icc (-(m : ℤ)) m, grunsky f g 0 l * lam l).re) ↔
        volume ((f '' unitDisc ∪ g '' unitDiscExterior)ᶜ) = 0) := by
  refine ⟨fun lam => ?_, ?_⟩
  · obtain ⟨U, r, hUd, hr, hmono, hlim, hU0, hs1, hs2, hle, -, -⟩ := t21_core h m lam
    rw [t21_lhs m lam hs1 hs2]
    exact hle
  · constructor
    · intro hall
      obtain ⟨lam0, hlam0⟩ : ∃ lam0 : ℤ → ℂ, ∀ l, lam0 l = if l = 0 then 1 else 0 := ⟨_, fun _ => rfl⟩
      obtain ⟨U, r, hUd, hr, hmono, hlim, hU0, hs1, hs2, hle, hge, heq⟩ := t21_core h m lam0
      have h1 := hall lam0
      rw [t21_lhs m lam0 hs1 hs2] at h1
      have hI := heq h1
      have hUz : U = fun _ => 0 := funext (hU0 (fun k hk => by rw [hlam0, if_neg hk]))
      have hl0 : lam0 0 = 1 := by rw [hlam0]; simp
      have hder : ∀ w, deriv U w = 0 := fun w => by rw [hUz]; exact deriv_const _ _
      have hφ : ∀ w : ℂ, ‖deriv U w + (-lam0 0) / w‖ ^ 2 = (‖w‖ ^ 2)⁻¹ := fun w => by
        rw [hder, hl0, zero_add, norm_div, norm_neg, norm_one, div_pow, one_pow, one_div]
      simp_rw [hφ] at hI
      have hcont : ContinuousOn (fun w : ℂ => (‖w‖ ^ 2)⁻¹) {0}ᶜ :=
        (continuous_norm.pow 2).continuousOn.inv₀ (fun w hw => by
          have : w ≠ 0 := hw
          exact pow_ne_zero 2 (norm_ne_zero_iff.mpr this))
      have hfo : IsOpen (f '' unitDisc) :=
        (RMT.differentiableOn_invFunOn_of_injOn isOpen_ball h.1 h.2.1).1
      have hEo : IsOpen unitDiscExterior := isOpen_lt continuous_const continuous_norm
      have hgo : IsOpen (g '' unitDiscExterior) :=
        (RMT.differentiableOn_invFunOn_of_injOn hEo h.2.2.2.2.1.1 h.2.2.2.2.1.2.1).1
      have hFm : MeasurableSet (f '' unitDisc ∪ g '' unitDiscExterior)ᶜ :=
        (hfo.union hgo).isClosed_compl.measurableSet
      have hF0 : ∀ w ∈ (f '' unitDisc ∪ g '' unitDiscExterior)ᶜ, w ≠ 0 := by
        intro w hw hw0
        exact hw (Or.inl ⟨0, mem_ball_self one_pos, by rw [h.2.2.1, hw0]⟩)
      have hR : ∀ R : ℕ, volume ((f '' unitDisc ∪ g '' unitDiscExterior)ᶜ ∩ ball (0 : ℂ) ((R : ℝ) + 1)) = 0 := by
        intro R
        set S : Set ℂ := (f '' unitDisc ∪ g '' unitDiscExterior)ᶜ ∩ ball (0 : ℂ) ((R : ℝ) + 1) with hS
        have hR0 : 0 < (R : ℝ) + 1 := by positivity
        have hSfin : volume S < ⊤ := lt_of_le_of_lt (measure_mono Set.inter_subset_right) measure_ball_lt_top
        have hbd : ∀ n, (((R : ℝ) + 1) ^ 2)⁻¹ * (volume S).toReal ≤
            ∫ w in (f '' closedBall (0 : ℂ) (r n) ∪ g '' {z : ℂ | 1 / r n ≤ ‖z‖})ᶜ, (‖w‖ ^ 2)⁻¹ := by
          intro n
          have hint := t21_gap_integrable h (hr n).1 (hr n).2 hcont
          have hsub : S ⊆ (f '' closedBall (0 : ℂ) (r n) ∪ g '' {z : ℂ | 1 / r n ≤ ‖z‖})ᶜ :=
            Set.inter_subset_left.trans (t21_F_subset_gap (hr n).1 (hr n).2)
          have h1 : ∫ w in S, (((R : ℝ) + 1) ^ 2)⁻¹ ≤ ∫ w in S, (‖w‖ ^ 2)⁻¹ := by
            refine setIntegral_mono_on (integrableOn_const hSfin.ne) ((hint.mono_set hsub))
              (hFm.inter measurableSet_ball) (fun w hw => ?_)
            have hw0 : w ≠ 0 := hF0 w hw.1
            have hwn : ‖w‖ ≤ (R : ℝ) + 1 := (mem_ball_zero_iff.mp hw.2).le
            have hpos : 0 < ‖w‖ := norm_pos_iff.mpr hw0
            exact inv_anti₀ (by positivity) (by nlinarith)
          have h2 : ∫ w in S, (‖w‖ ^ 2)⁻¹ ≤
              ∫ w in (f '' closedBall (0 : ℂ) (r n) ∪ g '' {z : ℂ | 1 / r n ≤ ‖z‖})ᶜ, (‖w‖ ^ 2)⁻¹ :=
            setIntegral_mono_set hint (Eventually.of_forall (fun w => by positivity))
              (Eventually.of_forall hsub)
          rw [setIntegral_const] at h1
          simp only [smul_eq_mul, MeasureTheory.measureReal_def] at h1
          linarith
        have hle0 := ge_of_tendsto' hI hbd
        have : (volume S).toReal = 0 := by
          have hpos : 0 < (((R : ℝ) + 1) ^ 2)⁻¹ := by positivity
          nlinarith [ENNReal.toReal_nonneg (a := volume S)]
        exact (ENNReal.toReal_eq_zero_iff _).mp this |>.resolve_right hSfin.ne
      have hU : (f '' unitDisc ∪ g '' unitDiscExterior)ᶜ = ⋃ R : ℕ,
          ((f '' unitDisc ∪ g '' unitDiscExterior)ᶜ ∩ ball (0 : ℂ) ((R : ℝ) + 1)) := by
        ext w
        simp only [mem_iUnion, mem_inter_iff, mem_ball_zero_iff]
        constructor
        · intro hw
          obtain ⟨R, hR⟩ := exists_nat_gt ‖w‖
          exact ⟨R, hw, by linarith⟩
        · rintro ⟨R, hw, -⟩
          exact hw
      rw [hU]
      exact measure_iUnion_null hR
    · intro hF lam
      obtain ⟨U, r, hUd, hr, hmono, hlim, hU0, hs1, hs2, hle, hge, -⟩ := t21_core h m lam
      have hcont : ContinuousOn (fun w : ℂ => ‖deriv U w + (-lam 0) / w‖ ^ 2) {0}ᶜ := by
        have h1 : ContinuousOn (deriv U) {0}ᶜ := (hUd.deriv isOpen_compl_singleton).continuousOn
        have h2 : ContinuousOn (fun w : ℂ => (-lam 0) / w) {0}ᶜ :=
          continuousOn_const.div continuousOn_id (fun w hw => hw)
        exact ((h1.add h2).norm).pow 2
      have hI := mg_gap_integral_tendsto_gen h hF hcont hr hmono hlim
      rw [t21_lhs m lam hs1 hs2]
      exact le_antisymm hle (hge hI)

/-- **Theorem 2.1** (Hummel [Hum72]) (TT:3820–3834), the generalized Grunsky inequality. For a normalized disjoint
pair and `λ_{-m}, …, λ_m ∈ ℂ`:
`Σ_{k ∈ ℤ} |k| |Σ_{l=-m}^{m} b_{kl} λ_l|² ≤ Σ'_{k=-m}^{m} |λ_k|²/|k| + 2 Re[λ̄₀ Σ_{l=-m}^{m} b_{0l} λ_l]`.
Equality holds for all `λ` iff `F = ℂ \ (f(𝔻) ∪ g(𝔻*))` is a null set. -/
theorem thm_2_1 {f g : ℂ → ℂ} (h : IsNormalizedDisjointPair f g) (m : ℕ) :
    (∀ lam : ℤ → ℂ,
      (∑' k : ℤ, |(k : ℝ)| * ‖∑ l ∈ Finset.Icc (-(m : ℤ)) m, grunsky f g k l * lam l‖ ^ 2) ≤
        (∑ k ∈ (Finset.Icc (-(m : ℤ)) m).erase 0, ‖lam k‖ ^ 2 / |(k : ℝ)|) +
          2 * (conj (lam 0) * ∑ l ∈ Finset.Icc (-(m : ℤ)) m, grunsky f g 0 l * lam l).re) ∧
      ((∀ lam : ℤ → ℂ,
        (∑' k : ℤ, |(k : ℝ)| * ‖∑ l ∈ Finset.Icc (-(m : ℤ)) m, grunsky f g k l * lam l‖ ^ 2) =
          (∑ k ∈ (Finset.Icc (-(m : ℤ)) m).erase 0, ‖lam k‖ ^ 2 / |(k : ℝ)|) +
            2 * (conj (lam 0) * ∑ l ∈ Finset.Icc (-(m : ℤ)) m, grunsky f g 0 l * lam l).re) ↔
        volume ((f '' unitDisc ∪ g '' unitDiscExterior)ᶜ) = 0) :=
  mg_thm_2_1 h m

end Ch2

end TakhtajanTeo
