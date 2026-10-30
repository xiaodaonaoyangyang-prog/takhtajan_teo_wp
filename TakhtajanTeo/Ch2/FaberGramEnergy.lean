import TakhtajanTeo.Ch2.FaberGram

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal ComplexConjugate Classical Real
noncomputable section
namespace TakhtajanTeo.Ch2
open LiZhongQC

set_option maxHeartbeats 2000000 in
/-- The exact Green energy identity underlying the existing finite Grunsky inequality.
The nonnegative exterior energy is retained instead of discarded. -/
theorem faber_grunsky_energy_at_radius {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f unitDisc) (hi : InjOn f unitDisc) (hf0 : f 0=0)
    {a φ : ℕ → ℕ → ℂ} {b00 : ℂ}
    (hexp : ∀ z∈unitDisc, ∀ w∈unitDisc, z≠w → ∃ S : ℂ,
      HasSum (fun p : ℕ × ℕ => a p.1 p.2*z^p.1*w^p.2) S ∧ (f z-f w)/(z-w)=exp (b00-S))
    (hφ : ∀ l k : ℕ, ∀ r : ℝ, 0<r → r<1 → Real.circleAverage (fun z => f z^l/z^k) 0 r=φ l k)
    (hφ0 : ∀ l k : ℕ, k<l → φ l k=0)
    {ρ : ℝ} (hρ0 : 0<ρ) (hρ1 : ρ<1) (N : ℕ) (μ : ℕ → ℂ) :
    let ν : ℕ → ℂ := fun l => ∑ k∈Finset.Icc 1 N, (k : ℂ)*μ k*φ l k/(l : ℂ)
    let H : ℂ → ℂ := fun w => ∑ l∈Finset.Icc 1 N, ν l*w^(-(l : ℤ))
    Summable (fun p : ℕ => ((p+1 : ℕ) : ℝ)*
      ‖∑ k∈Finset.Icc 1 N, (k : ℂ)*μ k*a (p+1) k‖^2*ρ^(2*(p+1))) ∧
    (∫ w in (f '' closedBall (0 : ℂ) ρ)ᶜ, ‖deriv H w‖^2) =
      π*((∑ k∈Finset.Icc 1 N, (k : ℝ)*‖μ k‖^2*(ρ^(2*k))⁻¹) -
        ∑' p : ℕ, ((p+1 : ℕ) : ℝ)*‖∑ k∈Finset.Icc 1 N, (k : ℂ)*μ k*a (p+1) k‖^2*ρ^(2*(p+1))) := by
  dsimp only
  set c : ℕ → ℂ := fun p => ∑ k ∈ Finset.Icc 1 N, (k : ℂ) * μ k * a p k with hc
  set ν : ℕ → ℂ := fun l => ∑ k ∈ Finset.Icc 1 N, (k : ℂ) * μ k * φ l k / (l : ℂ) with hν
  let h : ℂ → ℂ := fun w => ∑ l ∈ Finset.Icc 1 N, ν l * w ^ (-(l : ℤ))
  obtain ⟨r1, hr1⟩ : ∃ r1 : ℝ, r1 = ρ / 2 := ⟨_, rfl⟩
  obtain ⟨r2, hr2⟩ : ∃ r2 : ℝ, r2 = (ρ + 1) / 2 := ⟨_, rfl⟩
  have hr1pos : 0 < r1 := by rw [hr1]; positivity
  have hr1ρ : r1 < ρ := by rw [hr1]; linarith
  have hρr2 : ρ < r2 := by rw [hr2]; linarith
  have hr2pos : 0 < r2 := by linarith
  have hr2one : r2 < 1 := by rw [hr2]; linarith
  let d : ℤ → ℂ := fun n => if 0 ≤ n then c n.toNat else if (-n).toNat ≤ N then μ (-n).toNat else 0
  -- Laurent expansion
  have hdpos : ∀ n : ℕ, d (n : ℤ) = c n := fun n => by simp [d]
  have hdneg : ∀ m : ℕ, d (-((m : ℤ) + 1)) = if m + 1 ≤ N then μ (m + 1) else 0 := fun m => by
    have h1 : ¬ (0 : ℤ) ≤ -((m : ℤ) + 1) := by omega
    have h2 : (-(-((m : ℤ) + 1))).toNat = m + 1 := by omega
    show (if (0 : ℤ) ≤ -((m : ℤ) + 1) then c (-((m : ℤ) + 1)).toNat
      else if (-(-((m : ℤ) + 1))).toNat ≤ N then μ (-(-((m : ℤ) + 1))).toNat else 0) = _
    rw [if_neg h1, h2]
  have hlaurent : ∀ z : ℂ, r1 < ‖z‖ → ‖z‖ < r2 → h (f z) = ∑' n : ℤ, d n * z ^ n := by
    intro z hz1 hz2
    have hzD : z ∈ unitDisc := mem_ball_zero_iff.mpr (hz2.trans hr2one)
    have hz0 : z ≠ 0 := by
      intro h0; rw [h0, norm_zero] at hz1; linarith
    obtain ⟨hsc, hF⟩ := g2_laurent_of_faber hf hi hf0 hexp hφ hφ0 N μ hzD hz0
    have hpos : Summable (fun n : ℕ => d (n : ℤ) * z ^ (n : ℤ)) := by
      refine hsc.congr (fun n => ?_)
      rw [hdpos, zpow_natCast]
    have hneg : Summable (fun n : ℕ => d (-((n : ℤ) + 1)) * z ^ (-((n : ℤ) + 1))) := by
      refine summable_of_ne_finset_zero (s := Finset.range N) (fun m hm => ?_)
      have : ¬ m + 1 ≤ N := by simp at hm; omega
      rw [hdneg, if_neg this, zero_mul]
    rw [tsum_of_nat_of_neg_add_one hpos hneg]
    have e1 : ∑' n : ℕ, d (n : ℤ) * z ^ (n : ℤ) = ∑' p : ℕ, c p * z ^ p := by
      refine tsum_congr (fun n => ?_)
      rw [hdpos, zpow_natCast]
    have e2 : ∑' n : ℕ, d (-((n : ℤ) + 1)) * z ^ (-((n : ℤ) + 1)) =
        ∑ k ∈ Finset.Icc 1 N, μ k * z ^ (-(k : ℤ)) := by
      rw [tsum_eq_sum (s := Finset.range N) (fun m hm => by
        have : ¬ m + 1 ≤ N := by simp at hm; omega
        rw [hdneg, if_neg this, zero_mul])]
      refine Finset.sum_nbij' (fun m => m + 1) (fun k => k - 1) ?_ ?_ ?_ ?_ ?_
      · intro m hm; simp at hm ⊢; omega
      · intro k hk; simp at hk ⊢; omega
      · intro m _; simp
      · intro k hk; simp at hk; omega
      · intro m hm
        have : m + 1 ≤ N := by simp at hm; omega
        rw [hdneg, if_pos this]
        push_cast
        rfl
    rw [e1, e2, add_comm]
    exact hF
  have hcs : Summable (fun n : ℕ => ‖c n‖ * r2 ^ n) := by
    have hr2D : ((r2 : ℝ) : ℂ) ∈ unitDisc :=
      mem_ball_zero_iff.mpr (by rw [Complex.norm_real, Real.norm_of_nonneg (by linarith)]; exact hr2one)
    have hr20 : ((r2 : ℝ) : ℂ) ≠ 0 := by
      have : (0 : ℝ) < r2 := by linarith
      exact_mod_cast this.ne'
    have := (g2_laurent_of_faber hf hi hf0 hexp hφ hφ0 N μ hr2D hr20).1
    have h2 := (summable_norm_iff.mpr this)
    refine h2.congr (fun n => ?_)
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg (by linarith)]
  have hnegfin : ∀ (g : ℕ → ℝ), (∀ m : ℕ, N < m → g m = 0) → Summable g := fun g hg =>
    summable_of_ne_finset_zero (s := Finset.range (N + 1)) (fun m hm => hg m (by simpa using hm))
  have hdnegzero : ∀ m : ℕ, N < m → d (-(m : ℤ)) = 0 := fun m hm => by
    have h1 : ¬ (0 : ℤ) ≤ -(m : ℤ) := by omega
    have h2 : (-(-(m : ℤ))).toNat = m := by omega
    show (if (0 : ℤ) ≤ -(m : ℤ) then c (-(m : ℤ)).toNat
      else if (-(-(m : ℤ))).toNat ≤ N then μ (-(-(m : ℤ))).toNat else 0) = 0
    rw [if_neg h1, h2, if_neg (by omega)]
  have hs : Summable fun n : ℤ => ‖d n‖ * max (r1 ^ n) (r2 ^ n) := by
    rw [summable_int_iff_summable_nat_and_neg]
    refine ⟨?_, ?_⟩
    · refine hcs.congr (fun n => ?_)
      rw [hdpos]
      have : max (r1 ^ (n : ℤ)) (r2 ^ (n : ℤ)) = r2 ^ n := by
        rw [zpow_natCast, zpow_natCast]
        exact max_eq_right (pow_le_pow_left₀ hr1pos.le (by linarith) n)
      rw [this]
    · refine hnegfin _ (fun m hm => ?_)
      rw [hdnegzero m hm, norm_zero, zero_mul]
  have hs1 : Summable fun n : ℤ => |(n : ℝ)| * ‖d n‖ * ρ ^ n := by
    rw [summable_int_iff_summable_nat_and_neg]
    refine ⟨?_, ?_⟩
    · obtain ⟨C, hC⟩ := hcs.tendsto_atTop_zero.bddAbove_range
      have hgeo : Summable (fun n : ℕ => ((n : ℝ) ^ 1) * (ρ / r2) ^ n) :=
        summable_pow_mul_geometric_of_norm_lt_one 1 (by
          rw [Real.norm_of_nonneg (by positivity)]
          exact (div_lt_one (by linarith)).mpr hρr2)
      refine (hgeo.mul_left (|C|)).of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
      rw [hdpos]
      have h1 : ‖c n‖ * r2 ^ n ≤ |C| := (hC ⟨n, rfl⟩).trans (le_abs_self C)
      have h2 : (0 : ℝ) < r2 ^ n := pow_pos (by linarith) n
      simp only [Int.cast_natCast, Nat.abs_cast, zpow_natCast, pow_one]
      calc (n : ℝ) * ‖c n‖ * ρ ^ n = (n : ℝ) * ((‖c n‖ * r2 ^ n) * (ρ / r2) ^ n) := by
            rw [div_pow]; field_simp
        _ ≤ (n : ℝ) * (|C| * (ρ / r2) ^ n) := by gcongr
        _ = |C| * ((n : ℝ) * (ρ / r2) ^ n) := by ring
    · refine hnegfin _ (fun m hm => ?_)
      rw [hdnegzero m hm, norm_zero, mul_zero, zero_mul]
  -- decay of h'
  have hderiv : ∀ w : ℂ, w ≠ 0 → deriv h w =
      ∑ l ∈ Finset.Icc 1 N, ν l * (((-(l : ℤ) : ℤ) : ℂ) * w ^ (-(l : ℤ) - 1)) := by
    intro w hw
    have hd : HasDerivAt h (∑ l ∈ Finset.Icc 1 N, ν l * (((-(l : ℤ) : ℤ) : ℂ) * w ^ (-(l : ℤ) - 1))) w := by
      apply HasDerivAt.fun_sum
      intro l _
      exact (hasDerivAt_zpow (-(l : ℤ)) w (Or.inl hw)).const_mul (ν l)
    exact hd.deriv
  have hdecay : ∃ C R : ℝ, ∀ w : ℂ, R < ‖w‖ → ‖deriv h w‖ ≤ C / ‖w‖ ^ 2 := by
    refine ⟨∑ l ∈ Finset.Icc 1 N, (l : ℝ) * ‖ν l‖, 1, fun w hw => ?_⟩
    have hw0 : w ≠ 0 := by intro h0; rw [h0] at hw; simp at hw; linarith
    have hwpos : 0 < ‖w‖ := norm_pos_iff.mpr hw0
    rw [hderiv w hw0]
    refine (norm_sum_le _ _).trans ?_
    rw [Finset.sum_div]
    refine Finset.sum_le_sum (fun l hl => ?_)
    have hl1 : 1 ≤ l := (Finset.mem_Icc.mp hl).1
    rw [norm_mul, norm_mul, norm_zpow, Complex.norm_intCast]
    have hzp : ‖w‖ ^ (-(l : ℤ) - 1) ≤ ‖w‖ ^ (-(2 : ℤ)) :=
      zpow_le_zpow_right₀ hw.le (by omega)
    have : ‖w‖ ^ (-(2 : ℤ)) = 1 / ‖w‖ ^ 2 := by
      rw [zpow_neg, zpow_ofNat, one_div]
    rw [this] at hzp
    calc ‖ν l‖ * (|((-(l : ℤ) : ℤ) : ℝ)| * ‖w‖ ^ (-(l : ℤ) - 1))
        ≤ ‖ν l‖ * ((l : ℝ) * (1 / ‖w‖ ^ 2)) := by
          gcongr
          simp
        _ = (l : ℝ) * ‖ν l‖ / ‖w‖ ^ 2 := by ring
  have hh : DifferentiableOn ℂ h {0}ᶜ := by
    apply DifferentiableOn.fun_sum
    intro l _
    exact (differentiableOn_const _).mul (differentiableOn_zpow _ _ (Or.inl (by simp)))
  have hG := green_exterior_image hf hi hf0 hρ0 hρ1 hh hdecay
  have hP := g2_laurent_parseval hr1pos hr1ρ hρr2 hs hs1
  -- identify the two integrals
  have hcirc : ∀ θ : ℝ, r1 < ‖circleMap 0 ρ θ‖ ∧ ‖circleMap 0 ρ θ‖ < r2 := fun θ => by
    simp only [norm_circleMap_zero, abs_of_pos hρ0]
    exact ⟨hr1ρ, hρr2⟩
  have hint : ∫ θ in (0 : ℝ)..2 * π, conj (h (f (circleMap 0 ρ θ))) *
        deriv (fun z => h (f z)) (circleMap 0 ρ θ) * circleMap 0 ρ θ =
      ∫ θ in (0 : ℝ)..2 * π, conj (∑' n : ℤ, d n * (circleMap 0 ρ θ) ^ n) *
        deriv (fun w : ℂ => ∑' n : ℤ, d n * w ^ n) (circleMap 0 ρ θ) * circleMap 0 ρ θ := by
    refine intervalIntegral.integral_congr (fun θ _ => ?_)
    have hU : IsOpen {w : ℂ | r1 < ‖w‖ ∧ ‖w‖ < r2} :=
      (isOpen_lt continuous_const continuous_norm).inter (isOpen_lt continuous_norm continuous_const)
    have hev : (fun z => h (f z)) =ᶠ[𝓝 (circleMap 0 ρ θ)] fun w : ℂ => ∑' n : ℤ, d n * w ^ n := by
      filter_upwards [hU.mem_nhds (hcirc θ)] with w hw
      exact hlaurent w hw.1 hw.2
    rw [hev.deriv_eq, hlaurent _ (hcirc θ).1 (hcirc θ).2]
  rw [hint, hP] at hG
  -- real-valued weights
  have hs0 : Summable fun n : ℤ => ‖d n‖ * ρ ^ n :=
    Summable.of_nonneg_of_le (fun n => by positivity)
      (fun n => by gcongr; exact g2_zpow_le_max hr1pos hr1ρ.le hρr2.le n) hs
  have hB : ∀ n : ℤ, ‖d n‖ * ρ ^ n ≤ ∑' m : ℤ, ‖d m‖ * ρ ^ m := fun n =>
    hs0.le_tsum n (fun m _ => by positivity)
  have hgs : Summable fun n : ℤ => (n : ℝ) * (‖d n‖ ^ 2 * ρ ^ (2 * n)) := by
    refine ((hs1.mul_left (∑' m : ℤ, ‖d m‖ * ρ ^ m)).of_norm_bounded (fun n => ?_))
    have e : (n : ℝ) * (‖d n‖ ^ 2 * ρ ^ (2 * n)) =
        ((n : ℝ) * (‖d n‖ * ρ ^ n)) * (‖d n‖ * ρ ^ n) := by
      rw [show 2 * n = n + n by ring, zpow_add₀ hρ0.ne']; ring
    rw [e, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ ‖d n‖ * ρ ^ n),
      abs_mul, abs_of_nonneg (by positivity : 0 ≤ ‖d n‖ * ρ ^ n)]
    calc |(n : ℝ)| * (‖d n‖ * ρ ^ n) * (‖d n‖ * ρ ^ n)
        ≤ |(n : ℝ)| * (‖d n‖ * ρ ^ n) * (∑' m : ℤ, ‖d m‖ * ρ ^ m) := by
          gcongr; exact hB n
      _ = (∑' m : ℤ, ‖d m‖ * ρ ^ m) * (|(n : ℝ)| * ‖d n‖ * ρ ^ n) := by ring
  have hT : ((∑' n : ℤ, (n : ℝ) * (‖d n‖ ^ 2 * ρ ^ (2 * n)) : ℝ) : ℂ) =
      ∑' n : ℤ, (n : ℂ) * ((‖d n‖ ^ 2 * ρ ^ (2 * n) : ℝ) : ℂ) := by
    rw [Complex.ofReal_tsum]; push_cast; rfl
  rw [← hT] at hG
  have hEnergy := congrArg Complex.re hG
  simp at hEnergy
  -- split
  have hgn : Summable fun n : ℕ => ((n : ℤ) : ℝ) * (‖d (n : ℤ)‖ ^ 2 * ρ ^ (2 * (n : ℤ))) :=
    hgs.comp_injective Nat.cast_injective
  have hgm : Summable fun n : ℕ => ((-((n : ℤ) + 1) : ℤ) : ℝ) *
      (‖d (-((n : ℤ) + 1))‖ ^ 2 * ρ ^ (2 * (-((n : ℤ) + 1)))) :=
    hnegfin _ (fun m hm => by
      have := hdnegzero (m + 1) (by omega)
      rw [show (-(((m + 1 : ℕ) : ℤ))) = -((m : ℤ) + 1) by push_cast; ring] at this
      rw [this]; simp)
  rw [tsum_of_nat_of_neg_add_one hgn hgm] at hEnergy
  have hpos' : (fun p : ℕ => ((p + 1 : ℕ) : ℝ) *
        ‖∑ k ∈ Finset.Icc 1 N, (k : ℂ) * μ k * a (p + 1) k‖ ^ 2 * ρ ^ (2 * (p + 1))) =
      fun p : ℕ => ((((p + 1 : ℕ) : ℤ) : ℝ)) *
        (‖d (((p + 1 : ℕ) : ℤ))‖ ^ 2 * ρ ^ (2 * (((p + 1 : ℕ) : ℤ)))) := by
    funext p
    rw [hdpos, show (2 * (((p + 1 : ℕ) : ℤ))) = (((2 * (p + 1) : ℕ)) : ℤ) by push_cast; ring,
      zpow_natCast]
    push_cast; ring
  have hsum1 : Summable (fun p : ℕ => ((p + 1 : ℕ) : ℝ) *
        ‖∑ k ∈ Finset.Icc 1 N, (k : ℂ) * μ k * a (p + 1) k‖ ^ 2 * ρ ^ (2 * (p + 1))) := by
    rw [hpos']
    exact (summable_nat_add_iff 1).mpr hgn
  refine ⟨hsum1, ?_⟩
  have hnegval : ∑' n : ℕ, ((-((n : ℤ) + 1) : ℤ) : ℝ) *
      (‖d (-((n : ℤ) + 1))‖ ^ 2 * ρ ^ (2 * (-((n : ℤ) + 1)))) =
      -∑ k ∈ Finset.Icc 1 N, (k : ℝ) * ‖μ k‖ ^ 2 * (ρ ^ (2 * k))⁻¹ := by
    rw [tsum_eq_sum (s := Finset.range N) (fun m hm => by
      have : ¬ m + 1 ≤ N := by simp at hm; omega
      rw [hdneg, if_neg this]; simp)]
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_nbij' (fun m => m + 1) (fun k => k - 1) ?_ ?_ ?_ ?_ ?_
    · intro m hm; simp at hm ⊢; omega
    · intro k hk; simp at hk ⊢; omega
    · intro m _; simp
    · intro k hk; simp at hk; omega
    · intro m hm
      have : m + 1 ≤ N := by simp at hm; omega
      rw [hdneg, if_pos this]
      have e : ρ ^ (2 * (-((m : ℤ) + 1))) = (ρ ^ (2 * (m + 1)))⁻¹ := by
        rw [show 2 * (-((m : ℤ) + 1)) = -((2 * (m + 1) : ℕ) : ℤ) by push_cast; ring, zpow_neg,
          zpow_natCast]
      rw [e]; push_cast; ring
  rw [hnegval, hgn.tsum_eq_zero_add] at hEnergy
  have h0 : ((((0 : ℕ) : ℤ) : ℝ)) * (‖d (((0 : ℕ) : ℤ))‖ ^ 2 * ρ ^ (2 * (((0 : ℕ) : ℤ)))) = 0 := by simp
  rw [h0, zero_add] at hEnergy
  have : ∑' p : ℕ, ((((p + 1 : ℕ) : ℤ) : ℝ)) *
        (‖d (((p + 1 : ℕ) : ℤ))‖ ^ 2 * ρ ^ (2 * (((p + 1 : ℕ) : ℤ)))) =
      ∑' p : ℕ, ((p + 1 : ℕ) : ℝ) *
        ‖∑ k ∈ Finset.Icc 1 N, (k : ℂ) * μ k * a (p + 1) k‖ ^ 2 * ρ ^ (2 * (p + 1)) := by
    exact (congrArg tsum hpos').symm
  rw [this] at hEnergy
  nlinarith [hEnergy]

end TakhtajanTeo.Ch2
#print axioms TakhtajanTeo.Ch2.faber_grunsky_energy_at_radius


