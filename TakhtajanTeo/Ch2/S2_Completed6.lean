import TakhtajanTeo.Ch2.S2_MixedB
import TakhtajanTeo.Ch2.S2_Completed
import TakhtajanTeo.Ch2.S2_Completed4

/-!
# Ch2 §2 completed originals, part 6 (`s2c_` copies)

`eq_2_4` (`𝖪₂ = I - 𝖪₁`, `𝖪₃ = I - 𝖪₄`), proved as `s2c_eq_2_4` with the statement of `eq_2_4` byte-identical.
Route: the Bergman-basis series of `K₁, K₂, K₃, K₄` and the unitarity columns of `mg_unitary_core`
(`B₁*B₁ + B₃*B₃ = I`, `B₂*B₂ + B₄*B₄ = I`), with the polarized area Parseval `A21_basis_pairing` (inverted to `𝔻*`
through `s2c_inv_integral`). The `e24_` lemmas are helpers.
-/

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal ComplexConjugate Classical Real
noncomputable section
namespace TakhtajanTeo.Ch2
open LiZhongQC

theorem e24_sqrt3 (m n : ℕ) :
    (Real.sqrt (((m : ℝ) + 1) * ((n : ℝ) + 1)) : ℂ) * (Real.sqrt (((m : ℝ) + 1) / π) : ℂ) *
      (Real.sqrt (((n : ℝ) + 1) / π) : ℂ) = ((m + 1 : ℕ) : ℂ) * ((n + 1 : ℕ) : ℂ) / (π : ℂ) := by
  have hr : Real.sqrt (((m : ℝ) + 1) * ((n : ℝ) + 1)) * Real.sqrt (((m : ℝ) + 1) / π) *
      Real.sqrt (((n : ℝ) + 1) / π) = ((m : ℝ) + 1) * ((n : ℝ) + 1) / π := by
    rw [Real.sqrt_mul (by positivity), Real.sqrt_div (by positivity), Real.sqrt_div (by positivity)]
    calc
      _ = (Real.sqrt ((m : ℝ) + 1) ^ 2 * Real.sqrt ((n : ℝ) + 1) ^ 2) / Real.sqrt π ^ 2 := by ring
      _ = _ := by
        rw [Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity), Real.sq_sqrt Real.pi_pos.le]
  exact_mod_cast hr

theorem e24_K3_eq (f g : ℂ → ℂ) (z u : ℂ) : kerK3 f g z u = kerK2 f g u z := by
  unfold kerK3 kerK2
  rw [show (f u - g z) ^ 2 = (g z - f u) ^ 2 by ring, mul_comm (deriv g z)]

theorem e24_dinf_ne {f g : ℂ → ℂ} (h : IsNormalizedDisjointPair f g) : derivAtInfty g ≠ 0 := by
  rw [← (grunsky_spec h).1.1]
  exact Complex.exp_ne_zero _

/-- The mixed series of `K₂`, in the Bergman bases `e_p(z)`, `f_q(u)`. -/
theorem e24_K2_aux {f g : ℂ → ℂ} (h : IsNormalizedDisjointPair f g) {z s : ℂ} (hz : z ∈ unitDisc)
    (hs : s ∈ unitDisc) (hs0 : s ≠ 0) :
    HasSum (fun p : ℕ × ℕ => B2 (grunsky f g) p.1 p.2 * basisE p.1 z * basisF p.2 s⁻¹)
      (kerK2 f g z s⁻¹) := by
  have h' := h
  obtain ⟨hfd, hfi, hf0, hf1, hgu, hdisj⟩ := h
  have hb := (grunsky_spec h').1
  have hD : derivAtInfty g ≠ 0 := e24_dinf_ne h'
  have hinvE : ∀ t ∈ unitDisc, t ≠ 0 → t⁻¹ ∈ unitDiscExterior := by
    intro t ht ht0
    have hn : ‖t‖ < 1 := mem_ball_zero_iff.mp ht
    have hpos : 0 < ‖t‖ := norm_pos_iff.mpr ht0
    show 1 < ‖t⁻¹‖
    rw [norm_inv]
    exact (one_lt_inv₀ hpos).mpr hn
  let a' : ℕ → ℕ → ℂ := fun m n => if m = 0 then 0 else grunsky f g (m : ℤ) (-(n : ℤ))
  have hexp' : ∀ t ∈ unitDisc, ∀ v ∈ unitDisc, ∃ S : ℂ,
      HasSum (fun p : ℕ × ℕ => a' p.1 p.2 * t ^ p.1 * v ^ p.2) S ∧
        (t ≠ 0 → (g t⁻¹ - f v) * t / derivAtInfty g = exp (-S)) := by
    intro t ht v hv
    by_cases ht0 : t = 0
    · refine ⟨0, ?_, fun h0 => absurd ht0 h0⟩
      have : (fun p : ℕ × ℕ => a' p.1 p.2 * t ^ p.1 * v ^ p.2) = fun _ => 0 := by
        funext p
        by_cases hp : p.1 = 0
        · simp [a', hp]
        · simp [ht0, zero_pow hp]
      rw [this]
      exact hasSum_zero
    · obtain ⟨S, hS, he⟩ := hb.2.2.1 t⁻¹ (hinvE t ht ht0) v hv
      refine ⟨S, ?_, fun _ => ?_⟩
      · let gg : ℕ × ℕ → ℕ × ℕ := fun p => (p.1 + 1, p.2)
        have hg : Function.Injective gg := by
          intro p q hpq
          simp only [gg, Prod.mk.injEq, add_left_inj] at hpq
          exact Prod.ext hpq.1 hpq.2
        have hz : ∀ x ∉ Set.range gg, (fun p : ℕ × ℕ => a' p.1 p.2 * t ^ p.1 * v ^ p.2) x = 0 := by
          rintro ⟨a, b⟩ hx
          rcases a with _ | a
          · simp [a']
          · exact absurd ⟨(a, b), rfl⟩ hx
        refine (hg.hasSum_iff hz).mp ?_
        refine hS.congr_fun (fun p => ?_)
        simp only [Function.comp_apply, gg, a', Nat.add_eq_zero_iff, one_ne_zero, and_false, ite_false,
          Nat.cast_add, Nat.cast_one]
        rw [g1_zpow_neg_succ, inv_inv]
      · rw [← he]
        field_simp
  have hoff : ∀ t ∈ unitDisc, ∀ v ∈ unitDisc, t ≠ v →
      Summable (fun p : ℕ × ℕ => a' p.1 p.2 * t ^ p.1 * v ^ p.2) := by
    intro t ht v hv _
    obtain ⟨S, hS, -⟩ := hexp' t ht v hv
    exact hS.summable
  have hs0' := s2c_bidisk_hasSum hoff
  obtain ⟨F, hFdef⟩ : ∃ F : ℂ → ℂ → ℂ, F = fun t v => ∑' p : ℕ × ℕ, a' p.1 p.2 * t ^ p.1 * v ^ p.2 :=
    ⟨_, rfl⟩
  have hsF : ∀ t ∈ unitDisc, ∀ v ∈ unitDisc,
      HasSum (fun p : ℕ × ℕ => a' p.1 p.2 * t ^ p.1 * v ^ p.2) (F t v) := by
    intro t ht v hv
    rw [hFdef]
    exact hs0' t ht v hv
  have hmix := g2c_double_series_deriv_mixed_succ hsF hs hz
  -- the inverted function is differentiable
  have hgE : DifferentiableAt ℂ g s⁻¹ :=
    hgu.1.differentiableAt ((isOpen_lt continuous_const continuous_norm).mem_nhds (hinvE s hs hs0))
  have hĝ : HasDerivAt (fun t : ℂ => g t⁻¹) (deriv g s⁻¹ * (-(s ^ 2)⁻¹)) s :=
    HasDerivAt.comp s (h := fun t : ℂ => t⁻¹) hgE.hasDerivAt (hasDerivAt_inv hs0)
  have hne : ∀ v ∈ unitDisc, g s⁻¹ - f v ≠ 0 := by
    intro v hv h0
    have : g s⁻¹ = f v := sub_eq_zero.mp h0
    exact Set.disjoint_left.mp hdisj ⟨v, hv, this.symm⟩ ⟨s⁻¹, hinvE s hs hs0, rfl⟩ |>.elim
  have hDU : ∀ v ∈ unitDisc, deriv (fun t => F t v) s =
      -(1 / s) - (deriv g s⁻¹ * (-(s ^ 2)⁻¹)) / (g s⁻¹ - f v) := by
    intro v hv
    have hdiff := s2c_series_differentiableAt hsF hs hv
    have hev : (fun t => exp (-F t v)) =ᶠ[𝓝 s] (fun t => (g t⁻¹ - f v) * t / derivAtInfty g) := by
      filter_upwards [(isOpen_ball : IsOpen unitDisc).mem_nhds hs, eventually_ne_nhds hs0] with t ht ht0
      obtain ⟨S, hS, he⟩ := hexp' t ht v hv
      rw [show F t v = S from (hsF t ht v hv).unique hS]
      exact (he ht0).symm
    have hE := (hdiff.hasDerivAt.neg).cexp
    have hΦ : HasDerivAt (fun t => (g t⁻¹ - f v) * t / derivAtInfty g)
        (((deriv g s⁻¹ * (-(s ^ 2)⁻¹)) * s + (g s⁻¹ - f v) * 1) / derivAtInfty g) s :=
      (((hĝ.sub_const (f v)).mul (hasDerivAt_id s)).div_const (derivAtInfty g))
    have hu := hE.unique (hΦ.congr_of_eventuallyEq hev)
    have hz0 : exp (-F s v) = (g s⁻¹ - f v) * s / derivAtInfty g := hev.self_of_nhds
    simp only [Pi.neg_apply] at hu
    rw [hz0] at hu
    have hn := hne v hv
    set Fp := deriv (fun t => F t v) s
    have : Fp = -(((deriv g s⁻¹ * (-(s ^ 2)⁻¹)) * s + (g s⁻¹ - f v) * 1) / derivAtInfty g) /
        ((g s⁻¹ - f v) * s / derivAtInfty g) := by
      rw [eq_div_iff (div_ne_zero (mul_ne_zero hn hs0) hD)]
      linear_combination -hu
    rw [this]
    generalize g s⁻¹ - f v = A at hn ⊢
    field_simp
    ring
  have hev2 : (fun v => deriv (fun t => F t v) s) =ᶠ[𝓝 z]
      (fun v => -(1 / s) - (deriv g s⁻¹ * (-(s ^ 2)⁻¹)) / (g s⁻¹ - f v)) := by
    filter_upwards [(isOpen_ball : IsOpen unitDisc).mem_nhds hz] with v hv
    exact hDU v hv
  have hfz : HasDerivAt f (deriv f z) z := (hfd.differentiableAt (isOpen_ball.mem_nhds hz)).hasDerivAt
  have hd : HasDerivAt (fun v => -(1 / s) - (deriv g s⁻¹ * (-(s ^ 2)⁻¹)) / (g s⁻¹ - f v))
      (0 - (0 * (g s⁻¹ - f z) - (deriv g s⁻¹ * (-(s ^ 2)⁻¹)) * (-deriv f z)) / (g s⁻¹ - f z) ^ 2) z :=
    (hasDerivAt_const z (-(1 / s))).sub
      ((hasDerivAt_const z (deriv g s⁻¹ * (-(s ^ 2)⁻¹))).div (hfz.const_sub (g s⁻¹)) (hne z hz))
  have hV : deriv (fun v => deriv (fun u => F u v) s) z =
      -((deriv g s⁻¹ * (-(s ^ 2)⁻¹)) * deriv f z / (g s⁻¹ - f z) ^ 2) := by
    rw [hev2.deriv_eq, hd.deriv]
    have hn := hne z hz
    generalize g s⁻¹ - f z = A at hn ⊢
    field_simp
    ring
  rw [hV] at hmix
  have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hsw : HasSum (fun p : ℕ × ℕ => a' (p.2 + 1) (p.1 + 1) * ((p.2 + 1 : ℕ) : ℂ) * ((p.1 + 1 : ℕ) : ℂ) *
      s ^ p.2 * z ^ p.1) (-((deriv g s⁻¹ * (-(s ^ 2)⁻¹)) * deriv f z / (g s⁻¹ - f z) ^ 2)) :=
    (Equiv.prodComm ℕ ℕ).hasSum_iff.mpr hmix
  have h2 := (hsw.mul_left (s ^ 2 / (π : ℂ)))
  have hsym := hb.2.2.2.2
  convert h2 using 1
  · funext p
    obtain ⟨Q, P⟩ := p
    have hz2 : (s⁻¹) ^ (-(P : ℤ) - 2) = s ^ 2 * s ^ P := by
      rw [show (-(P : ℤ) - 2) = -((P + 2 : ℕ) : ℤ) by push_cast; ring, zpow_neg, zpow_natCast, inv_pow,
        inv_inv, pow_add, mul_comm]
    have hbq := hsym (Q + 1) P
    push_cast at hbq
    have h3 := e24_sqrt3 Q P
    simp only [B2, basisE, basisF, a', Nat.add_eq_zero_iff, one_ne_zero, and_false, ite_false, hz2]
    push_cast at h3 ⊢
    rw [hbq]
    linear_combination (grunsky f g ((P : ℤ) + 1) (-((Q : ℤ) + 1)) * z ^ Q * s ^ 2 * s ^ P) * h3
  · unfold kerK2
    have hn := hne z hz
    have hA : f z - g s⁻¹ = -(g s⁻¹ - f z) := by ring
    rw [hA]
    generalize g s⁻¹ - f z = A at hn ⊢
    field_simp


theorem e24_col {C D : ℕ → ℕ → ℂ}
    (hcol : ∀ m n : ℕ, (∑' k, (conj (C k m) * C k n + conj (D k m) * D k n)) = if m = n then 1 else 0)
    (m : ℕ) :
    (Summable (fun k => ‖C k m‖ ^ 2) ∧ (∑' k, ‖C k m‖ ^ 2) ≤ 1) ∧
      (Summable (fun k => ‖D k m‖ ^ 2) ∧ (∑' k, ‖D k m‖ ^ 2) ≤ 1) := by
  have e : ∀ z : ℂ, conj z * z = ((‖z‖ ^ 2 : ℝ) : ℂ) := fun z => by
    rw [mul_comm, Complex.mul_conj, Complex.sq_norm]
  have hfun : ∀ k, conj (C k m) * C k m + conj (D k m) * D k m =
      ((‖C k m‖ ^ 2 + ‖D k m‖ ^ 2 : ℝ) : ℂ) := fun k => by
    rw [e, e]; push_cast; ring
  have h := hcol m m
  simp only [ite_true] at h
  rw [tsum_congr hfun] at h
  have hsr : Summable (fun k => ‖C k m‖ ^ 2 + ‖D k m‖ ^ 2) := by
    by_contra hn
    have hn' : ¬ Summable (fun k => ((‖C k m‖ ^ 2 + ‖D k m‖ ^ 2 : ℝ) : ℂ)) :=
      fun hs => hn (Complex.summable_ofReal.mp hs)
    rw [tsum_eq_zero_of_not_summable hn'] at h
    exact zero_ne_one h
  have hsum : (∑' k, (‖C k m‖ ^ 2 + ‖D k m‖ ^ 2)) = 1 := by
    rw [← Complex.ofReal_tsum] at h
    exact_mod_cast h
  have hC : Summable (fun k => ‖C k m‖ ^ 2) :=
    hsr.of_nonneg_of_le (fun _ => by positivity) (fun k => by nlinarith [sq_nonneg ‖D k m‖])
  have hD : Summable (fun k => ‖D k m‖ ^ 2) :=
    hsr.of_nonneg_of_le (fun _ => by positivity) (fun k => by nlinarith [sq_nonneg ‖C k m‖])
  rw [hC.tsum_add hD] at hsum
  have h1 : 0 ≤ ∑' k, ‖C k m‖ ^ 2 := tsum_nonneg (fun _ => by positivity)
  have h2 : 0 ≤ ∑' k, ‖D k m‖ ^ 2 := tsum_nonneg (fun _ => by positivity)
  exact ⟨⟨hC, by linarith⟩, ⟨hD, by linarith⟩⟩

theorem e24_one {M : ℕ → ℕ → ℂ}
    (hM : ∀ m, Summable (fun k => ‖M k m‖ ^ 2) ∧ (∑' k, ‖M k m‖ ^ 2) ≤ 1)
    {v v' : ℕ → ℂ} (hv : Summable (fun p => ‖v p‖)) (hv' : Summable (fun p => ‖v' p‖)) :
    Summable (fun x : (ℕ × ℕ) × ℕ => ‖M x.2 x.1.1 * v x.1.1 * conj (M x.2 x.1.2 * v' x.1.2)‖) ∧
      ∀ k, HasSum (fun pp : ℕ × ℕ => M k pp.1 * v pp.1 * conj (M k pp.2 * v' pp.2))
        ((∑' p, M k p * v p) * conj (∑' p, M k p * v' p)) := by
  have hbd : ∀ k p, ‖M k p‖ ≤ 1 := by
    intro k p
    have h1 : ‖M k p‖ ^ 2 ≤ ∑' j, ‖M j p‖ ^ 2 :=
      (hM p).1.le_tsum k (fun j _ => by positivity)
    nlinarith [(hM p).2, norm_nonneg (M k p)]
  have hA : ∀ (w : ℕ → ℂ), Summable (fun p => ‖w p‖) → ∀ k, Summable (fun p => ‖M k p * w p‖) := by
    intro w hw k
    refine hw.of_nonneg_of_le (fun _ => norm_nonneg _) (fun p => ?_)
    rw [norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (hbd k p)
  refine ⟨?_, fun k => ?_⟩
  · have hnn : 0 ≤ fun x : (ℕ × ℕ) × ℕ => ‖M x.2 x.1.1 * v x.1.1 * conj (M x.2 x.1.2 * v' x.1.2)‖ :=
      fun _ => norm_nonneg _
    refine (summable_prod_of_nonneg hnn).mpr ⟨fun pp => ?_, ?_⟩
    · have hb : ∀ k, ‖M k pp.1 * v pp.1 * conj (M k pp.2 * v' pp.2)‖ ≤
          ‖v pp.1‖ * ‖v' pp.2‖ * ((‖M k pp.1‖ ^ 2 + ‖M k pp.2‖ ^ 2) / 2) := by
        intro k
        simp only [norm_mul, Complex.norm_conj]
        have := mul_nonneg (norm_nonneg (v pp.1)) (norm_nonneg (v' pp.2))
        nlinarith [sq_nonneg (‖M k pp.1‖ - ‖M k pp.2‖), mul_nonneg this (sq_nonneg (‖M k pp.1‖ - ‖M k pp.2‖))]
      exact (((hM pp.1).1.add (hM pp.2).1).div_const 2 |>.mul_left (‖v pp.1‖ * ‖v' pp.2‖)).of_nonneg_of_le
        (fun _ => norm_nonneg _) hb
    · have hb : ∀ pp : ℕ × ℕ, (∑' k, ‖M k pp.1 * v pp.1 * conj (M k pp.2 * v' pp.2)‖) ≤
          ‖v pp.1‖ * ‖v' pp.2‖ := by
        intro pp
        have hs : Summable (fun k => ‖v pp.1‖ * ‖v' pp.2‖ * ((‖M k pp.1‖ ^ 2 + ‖M k pp.2‖ ^ 2) / 2)) :=
          (((hM pp.1).1.add (hM pp.2).1).div_const 2).mul_left _
        have hle : ∀ k, ‖M k pp.1 * v pp.1 * conj (M k pp.2 * v' pp.2)‖ ≤
            ‖v pp.1‖ * ‖v' pp.2‖ * ((‖M k pp.1‖ ^ 2 + ‖M k pp.2‖ ^ 2) / 2) := by
          intro k
          simp only [norm_mul, Complex.norm_conj]
          have := mul_nonneg (norm_nonneg (v pp.1)) (norm_nonneg (v' pp.2))
          nlinarith [sq_nonneg (‖M k pp.1‖ - ‖M k pp.2‖),
            mul_nonneg this (sq_nonneg (‖M k pp.1‖ - ‖M k pp.2‖))]
        refine (Summable.tsum_le_tsum hle ?_ hs).trans ?_
        · exact (((hM pp.1).1.add (hM pp.2).1).div_const 2 |>.mul_left (‖v pp.1‖ * ‖v' pp.2‖)).of_nonneg_of_le
            (fun _ => norm_nonneg _) hle
        · rw [tsum_mul_left, tsum_div_const, ((hM pp.1).1.tsum_add (hM pp.2).1)]
          have := (hM pp.1).2
          have := (hM pp.2).2
          have h0 := mul_nonneg (norm_nonneg (v pp.1)) (norm_nonneg (v' pp.2))
          nlinarith
      have hsp : Summable (fun pp : ℕ × ℕ => ‖v pp.1‖ * ‖v' pp.2‖) :=
        hv.mul_of_nonneg hv' (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
      exact hsp.of_nonneg_of_le (fun _ => tsum_nonneg (fun _ => norm_nonneg _)) hb
  · have hB : Summable (fun p => ‖conj (M k p * v' p)‖) := by
      simpa only [Complex.norm_conj] using hA v' hv' k
    have hprod := tsum_mul_tsum_of_summable_norm (hA v hv k) hB
    have hsm := summable_mul_of_summable_norm (hA v hv k) hB
    rw [Complex.conj_tsum, hprod]
    exact hsm.hasSum

theorem e24_pair {C D : ℕ → ℕ → ℂ}
    (hcol : ∀ m n : ℕ, (∑' k, (conj (C k m) * C k n + conj (D k m) * D k n)) = if m = n then 1 else 0)
    {v v' : ℕ → ℂ} (hv : Summable (fun p => ‖v p‖)) (hv' : Summable (fun p => ‖v' p‖)) :
    HasSum (fun k => (∑' p, C k p * v p) * conj (∑' p, C k p * v' p) +
        (∑' p, D k p * v p) * conj (∑' p, D k p * v' p)) (∑' p, v p * conj (v' p)) := by
  obtain ⟨hC1, hC2⟩ := e24_one (fun m => (e24_col hcol m).1) hv hv'
  obtain ⟨hD1, hD2⟩ := e24_one (fun m => (e24_col hcol m).2) hv hv'
  have hT : Summable (fun x : (ℕ × ℕ) × ℕ =>
      C x.2 x.1.1 * v x.1.1 * conj (C x.2 x.1.2 * v' x.1.2) +
        D x.2 x.1.1 * v x.1.1 * conj (D x.2 x.1.2 * v' x.1.2)) := hC1.of_norm.add hD1.of_norm
  have hW := (Equiv.prodComm ℕ (ℕ × ℕ)).summable_iff.mpr hT
  have hfib := hW.hasSum.prod_fiberwise (fun k => (hC2 k).add (hD2 k))
  have hval : ∑' y : ℕ × (ℕ × ℕ), (fun x : (ℕ × ℕ) × ℕ =>
      C x.2 x.1.1 * v x.1.1 * conj (C x.2 x.1.2 * v' x.1.2) +
        D x.2 x.1.1 * v x.1.1 * conj (D x.2 x.1.2 * v' x.1.2)) ((Equiv.prodComm ℕ (ℕ × ℕ)) y) =
      ∑' p, v p * conj (v' p) := by
    rw [Equiv.tsum_eq (Equiv.prodComm ℕ (ℕ × ℕ)) (fun x : (ℕ × ℕ) × ℕ =>
      C x.2 x.1.1 * v x.1.1 * conj (C x.2 x.1.2 * v' x.1.2) +
        D x.2 x.1.1 * v x.1.1 * conj (D x.2 x.1.2 * v' x.1.2))]
    rw [hT.tsum_prod' (fun pp => hT.prod_factor pp)]
    have hin : ∀ pp : ℕ × ℕ, (∑' k, (C k pp.1 * v pp.1 * conj (C k pp.2 * v' pp.2) +
        D k pp.1 * v pp.1 * conj (D k pp.2 * v' pp.2))) =
        v pp.1 * conj (v' pp.2) * (if pp.2 = pp.1 then 1 else 0) := by
      intro pp
      have hf : ∀ k, C k pp.1 * v pp.1 * conj (C k pp.2 * v' pp.2) +
          D k pp.1 * v pp.1 * conj (D k pp.2 * v' pp.2) =
          (v pp.1 * conj (v' pp.2)) * (conj (C k pp.2) * C k pp.1 + conj (D k pp.2) * D k pp.1) := by
        intro k; rw [map_mul, map_mul]; ring
      rw [tsum_congr hf, tsum_mul_left, hcol pp.2 pp.1]
    simp only [hin]
    have hsp : Summable (fun pp : ℕ × ℕ => ‖v pp.1‖ * ‖v' pp.2‖) :=
      hv.mul_of_nonneg hv' (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
    let d : ℕ → ℕ × ℕ := fun p => (p, p)
    have hd : Function.Injective d := fun a b h => (Prod.mk.inj h).1
    have hdsum : Summable (fun p => v p * conj (v' p)) := by
      refine Summable.of_norm ?_
      have h1 := hsp.comp_injective hd
      refine h1.congr (fun p => ?_)
      simp [d, norm_mul]
    have hz : ∀ x ∉ Set.range d, (fun pp : ℕ × ℕ => v pp.1 * conj (v' pp.2) *
        (if pp.2 = pp.1 then (1 : ℂ) else 0)) x = 0 := by
      rintro ⟨a, b⟩ hx
      have hab : b ≠ a := fun h => hx ⟨a, by simp [d, h]⟩
      simp [hab]
    have hG : HasSum (fun pp : ℕ × ℕ => v pp.1 * conj (v' pp.2) *
        (if pp.2 = pp.1 then (1 : ℂ) else 0)) (∑' p, v p * conj (v' p)) := by
      refine (hd.hasSum_iff hz).mp ?_
      have hc : ((fun pp : ℕ × ℕ => v pp.1 * conj (v' pp.2) *
          (if pp.2 = pp.1 then (1 : ℂ) else 0)) ∘ d) = fun p => v p * conj (v' p) := by
        funext p; simp [d]
      rw [hc]
      exact hdsum.hasSum
    exact hG.tsum_eq
  rw [← hval]
  exact hfib

theorem e24_pair_sq {C D : ℕ → ℕ → ℂ}
    (hcol : ∀ m n : ℕ, (∑' k, (conj (C k m) * C k n + conj (D k m) * D k n)) = if m = n then 1 else 0)
    {v : ℕ → ℂ} (hv : Summable (fun p => ‖v p‖)) :
    Summable (fun k => ‖∑' p, C k p * v p‖ ^ 2) ∧ Summable (fun k => ‖∑' p, D k p * v p‖ ^ 2) := by
  have h := (e24_pair hcol hv hv).summable
  have e : ∀ z : ℂ, z * conj z = ((‖z‖ ^ 2 : ℝ) : ℂ) := fun z => by
    rw [Complex.mul_conj, Complex.sq_norm]
  have h' : Summable (fun k => ((‖∑' p, C k p * v p‖ ^ 2 + ‖∑' p, D k p * v p‖ ^ 2 : ℝ) : ℂ)) := by
    refine h.congr (fun k => ?_)
    rw [e, e]; push_cast; ring
  have hr := Complex.summable_ofReal.mp h'
  exact ⟨hr.of_nonneg_of_le (fun _ => by positivity) (fun k => by nlinarith [sq_nonneg ‖∑' p, D k p * v p‖]),
    hr.of_nonneg_of_le (fun _ => by positivity) (fun k => by nlinarith [sq_nonneg ‖∑' p, C k p * v p‖])⟩


theorem e24_int_pair {F G : ℂ → ℂ} {x y : ℕ → ℂ} (hx : Summable (fun n => ‖x n‖ ^ 2))
    (hy : Summable (fun n => ‖y n‖ ^ 2)) {E : Set ℂ} (hE : volume E = 0)
    (hF : ∀ u ∈ unitDisc, u ∉ E → HasSum (fun n => x n * basisE n u) (F u))
    (hG : ∀ u ∈ unitDisc, u ∉ E → HasSum (fun n => y n * basisE n u) (G u)) :
    HasSum (fun n => x n * conj (y n)) (∫ u in unitDisc, F u * conj (G u)) := by
  have hF' : (fun u => ∑' n, x n * basisE n u) ∈ A21fun unitDisc := (bergman_ell2_series hx).1
  have hG' : (fun u => ∑' n, y n * basisE n u) ∈ A21fun unitDisc := (bergman_ell2_series hy).1
  have hFe : ∀ u ∈ unitDisc, HasSum (fun n => x n * basisE n u) (∑' n, x n * basisE n u) :=
    fun u hu => (bergman_pair_summable hx (basisE_sq_summable hu)).of_norm.hasSum
  have hGe : ∀ u ∈ unitDisc, HasSum (fun n => y n * basisE n u) (∑' n, y n * basisE n u) :=
    fun u hu => (bergman_pair_summable hy (basisE_sq_summable hu)).of_norm.hasSum
  have hnull : ∀ᵐ u ∂(volume.restrict unitDisc), u ∉ E :=
    ae_restrict_of_ae (measure_eq_zero_iff_ae_notMem.mp hE)
  have hae : (fun u => F u * conj (G u)) =ᵐ[volume.restrict unitDisc]
      (fun u => (∑' n, x n * basisE n u) * conj (∑' n, y n * basisE n u)) := by
    filter_upwards [ae_restrict_mem (show MeasurableSet unitDisc from measurableSet_ball), hnull]
      with u hu hn
    rw [(hF u hu hn).unique (hFe u hu), (hG u hu hn).unique (hGe u hu)]
  rw [integral_congr_ae hae]
  exact A21_basis_pairing hF' hG' hFe hGe

theorem e24_basisF_inv (n : ℕ) {s : ℂ} (hs : s ≠ 0) : basisF n s⁻¹ = s ^ 2 * basisE n s := by
  have hz2 : (s⁻¹) ^ (-(n : ℤ) - 2) = s ^ 2 * s ^ n := by
    rw [show (-(n : ℤ) - 2) = -((n + 2 : ℕ) : ℤ) by push_cast; ring, zpow_neg, zpow_natCast, inv_pow,
      inv_inv, pow_add, mul_comm]
  simp only [basisF, basisE, hz2]
  ring

theorem e24_ext_pair {F G : ℂ → ℂ} {x y : ℕ → ℂ} (hx : Summable (fun n => ‖x n‖ ^ 2))
    (hy : Summable (fun n => ‖y n‖ ^ 2)) {E : Set ℂ} (hE : E.Finite)
    (hF : ∀ u ∈ unitDiscExterior, u ∉ E → HasSum (fun n => x n * basisF n u) (F u))
    (hG : ∀ u ∈ unitDiscExterior, u ∉ E → HasSum (fun n => y n * basisF n u) (G u)) :
    HasSum (fun n => x n * conj (y n)) (∫ u in unitDiscExterior, F u * conj (G u)) := by
  have hext0 : ∀ z ∈ unitDiscExterior, z ≠ 0 := fun z hz h => by
    subst h
    norm_num [unitDiscExterior] at hz
  have hinvD : ∀ u ∈ unitDiscExterior, u⁻¹ ∈ unitDisc := by
    intro u hu
    have hu1 : 1 < ‖u‖ := hu
    exact mem_ball_zero_iff.mpr (by rw [norm_inv]; exact inv_lt_one_of_one_lt₀ hu1)
  have hinvE : ∀ t ∈ unitDisc, t ≠ 0 → t⁻¹ ∈ unitDiscExterior := by
    intro t ht ht0
    have hn : ‖t‖ < 1 := mem_ball_zero_iff.mp ht
    have hpos : 0 < ‖t‖ := norm_pos_iff.mpr ht0
    show 1 < ‖t⁻¹‖
    rw [norm_inv]
    exact (one_lt_inv₀ hpos).mpr hn
  -- inversion of the integral
  have h1 := s2c_inv_integral (fun s => (‖s‖ ^ 4)⁻¹ • (F s⁻¹ * conj (G s⁻¹)))
  have hRHS : (∫ z in unitDiscExterior, (‖z‖ ^ 4)⁻¹ •
      ((fun s => (‖s‖ ^ 4)⁻¹ • (F s⁻¹ * conj (G s⁻¹))) z⁻¹)) = ∫ u in unitDiscExterior, F u * conj (G u) := by
    refine setIntegral_congr_fun (isOpen_lt continuous_const continuous_norm).measurableSet (fun z hz => ?_)
    have hz0 := hext0 z hz
    have hn : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz0
    simp only [inv_inv, norm_inv, smul_smul]
    rw [show (‖z‖ ^ 4)⁻¹ * ((‖z‖⁻¹) ^ 4)⁻¹ = (1 : ℝ) by field_simp, one_smul]
  rw [hRHS] at h1
  rw [← h1]
  -- the integrand on the disc
  let F1 : ℂ → ℂ := fun s => F s⁻¹ / s ^ 2
  let G1 : ℂ → ℂ := fun s => G s⁻¹ / s ^ 2
  have hcongr : ∫ s in unitDisc \ {0}, (‖s‖ ^ 4)⁻¹ • (F s⁻¹ * conj (G s⁻¹)) =
      ∫ s in unitDisc \ {0}, F1 s * conj (G1 s) := by
    refine setIntegral_congr_fun (measurableSet_ball.diff (measurableSet_singleton _)) (fun s hs => ?_)
    have hs0 : s ≠ 0 := fun h0 => hs.2 (by simp [h0])
    have hn : ‖s‖ ≠ 0 := norm_ne_zero_iff.mpr hs0
    have hq : ((‖s‖ : ℝ) : ℂ) ^ 2 = s * conj s := by
      have h0 := Complex.mul_conj s
      rw [Complex.normSq_eq_norm_sq] at h0
      push_cast at h0
      exact h0.symm
    have hc0 : conj s ≠ 0 := (map_ne_zero _).mpr hs0
    simp only [F1, G1]
    rw [Complex.real_smul]
    push_cast
    try simp only [map_div₀, map_pow]
    rw [show ((‖s‖ : ℂ)) ^ 4 = (((‖s‖ : ℂ)) ^ 2) ^ 2 by ring, hq]
    field_simp
  rw [hcongr]
  have hdiff : ∫ s in unitDisc \ {0}, F1 s * conj (G1 s) = ∫ s in unitDisc, F1 s * conj (G1 s) :=
    setIntegral_congr_set (sdiff_null_ae_eq_self (measure_singleton 0))
  rw [hdiff]
  have hE' : volume ((fun t : ℂ => t⁻¹) '' E ∪ {0}) = 0 :=
    ((hE.image _).union (Set.finite_singleton 0)).measure_zero volume
  have hmem : ∀ u ∈ unitDisc, u ∉ (fun t : ℂ => t⁻¹) '' E ∪ {0} → u ≠ 0 ∧ u⁻¹ ∉ E := by
    intro u hu hn
    refine ⟨fun h0 => hn (Or.inr (by simp [h0])), fun hE2 => hn (Or.inl ⟨u⁻¹, hE2, inv_inv u⟩)⟩
  refine e24_int_pair hx hy hE' ?_ ?_
  · intro u hu hn
    obtain ⟨hu0, hnE⟩ := hmem u hu hn
    have h2 := hF u⁻¹ (hinvE u hu hu0) hnE
    have hu2 : (u ^ 2 : ℂ) ≠ 0 := pow_ne_zero 2 hu0
    refine (hasSum_mul_left_iff hu2).mp ?_
    simp only [e24_basisF_inv _ hu0] at h2
    convert h2 using 1
    · funext n; ring
    · simp only [F1]; field_simp
  · intro u hu hn
    obtain ⟨hu0, hnE⟩ := hmem u hu hn
    have h2 := hG u⁻¹ (hinvE u hu hu0) hnE
    have hu2 : (u ^ 2 : ℂ) ≠ 0 := pow_ne_zero 2 hu0
    refine (hasSum_mul_left_iff hu2).mp ?_
    simp only [e24_basisF_inv _ hu0] at h2
    convert h2 using 1
    · funext n; ring
    · simp only [G1]; field_simp

theorem e24_geom {x : ℂ} (hx : ‖x‖ < 1) :
    HasSum (fun p : ℕ => (((p : ℂ) + 1)) * x ^ p) (1 / (1 - x) ^ 2) := by
  have h1 := hasSum_coe_mul_geometric_of_norm_lt_one hx
  have h2 := hasSum_geometric_of_norm_lt_one hx
  have h3 := h1.add h2
  have hx1 : (1 - x) ≠ 0 := by
    intro h0
    have : x = 1 := by linear_combination -h0
    rw [this] at hx; simp at hx
  convert h3 using 1
  · funext p; ring
  · field_simp
    ring

theorem e24_sumE {z w : ℂ} (hz : z ∈ unitDisc) (hw : w ∈ unitDisc) :
    HasSum (fun p : ℕ => basisE p z * conj (basisE p w)) (1 / (π * (1 - z * conj w) ^ 2)) := by
  have hx : ‖z * conj w‖ < 1 := by
    rw [norm_mul, Complex.norm_conj]
    have h1 : ‖z‖ < 1 := mem_ball_zero_iff.mp hz
    have h2 : ‖w‖ < 1 := mem_ball_zero_iff.mp hw
    nlinarith [norm_nonneg z, norm_nonneg w]
  have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have h := (e24_geom hx).div_const (π : ℂ)
  convert h using 1
  · funext p
    simp only [basisE, map_mul, Complex.conj_ofReal, map_pow]
    have hsq : (Real.sqrt (((p : ℝ) + 1) / π) : ℂ) * (Real.sqrt (((p : ℝ) + 1) / π) : ℂ) =
        (((p : ℂ) + 1)) / (π : ℂ) := by
      rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by positivity)]
      push_cast; ring
    calc _ = ((Real.sqrt (((p : ℝ) + 1) / π) : ℂ) * (Real.sqrt (((p : ℝ) + 1) / π) : ℂ)) *
          (z * conj w) ^ p := by rw [mul_pow]; ring
      _ = _ := by rw [hsq]; ring
  · field_simp

theorem e24_sumF {z w : ℂ} (hz : z ∈ unitDiscExterior) (hw : w ∈ unitDiscExterior) :
    HasSum (fun p : ℕ => basisF p z * conj (basisF p w)) (1 / (π * (1 - z * conj w) ^ 2)) := by
  have hz1 : 1 < ‖z‖ := hz
  have hw1 : 1 < ‖w‖ := hw
  have hz0 : z ≠ 0 := norm_pos_iff.mp (by linarith)
  have hw0 : w ≠ 0 := norm_pos_iff.mp (by linarith)
  have hwc : conj w ≠ 0 := (map_ne_zero _).mpr hw0
  set x : ℂ := (z * conj w)⁻¹ with hxdef
  have hxn : ‖x‖ < 1 := by
    rw [hxdef, norm_inv, norm_mul, Complex.norm_conj]
    exact inv_lt_one_of_one_lt₀ (by nlinarith)
  have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have h := ((e24_geom hxn).mul_left (x ^ 2)).div_const (π : ℂ)
  have hx0 : x ≠ 0 := inv_ne_zero (mul_ne_zero hz0 hwc)
  have hx1 : (1 - x) ≠ 0 := by
    intro h0
    have : x = 1 := by linear_combination -h0
    rw [this] at hxn; simp at hxn
  have hzw : (z * conj w) ≠ 0 := mul_ne_zero hz0 hwc
  convert h using 1
  · funext p
    have hzp : z ^ (-(p : ℤ) - 2) = (z⁻¹) ^ (p + 2) := by
      rw [show (-(p : ℤ) - 2) = -((p + 2 : ℕ) : ℤ) by push_cast; ring, zpow_neg, zpow_natCast, inv_pow]
    have hwp : w ^ (-(p : ℤ) - 2) = (w⁻¹) ^ (p + 2) := by
      rw [show (-(p : ℤ) - 2) = -((p + 2 : ℕ) : ℤ) by push_cast; ring, zpow_neg, zpow_natCast, inv_pow]
    have hsq : (Real.sqrt (((p : ℝ) + 1) / π) : ℂ) * (Real.sqrt (((p : ℝ) + 1) / π) : ℂ) =
        (((p : ℂ) + 1)) / (π : ℂ) := by
      rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by positivity)]
      push_cast; ring
    simp only [basisF, map_mul, Complex.conj_ofReal, hzp, hwp, map_pow, map_inv₀]
    have hxe : (z⁻¹) * (conj w)⁻¹ = x := by rw [hxdef, mul_inv]
    calc _ = ((Real.sqrt (((p : ℝ) + 1) / π) : ℂ) * (Real.sqrt (((p : ℝ) + 1) / π) : ℂ)) *
          (z⁻¹ * (conj w)⁻¹) ^ (p + 2) := by rw [mul_pow]; ring
      _ = _ := by rw [hsq, hxe]; ring
  · rw [hxdef]
    field_simp
    ring

theorem e24_sq_of_abs {a : ℕ → ℂ} (ha : Summable (fun n => ‖a n‖)) :
    Summable (fun n => ‖a n‖ ^ 2) := by
  refine Summable.of_norm_bounded_eventually_nat ha ?_
  have := ha.tendsto_atTop_zero
  filter_upwards [this.eventually (gt_mem_nhds (show (0 : ℝ) < 1 by norm_num))] with n hn
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  nlinarith [norm_nonneg (a n)]

theorem e24_absE {z : ℂ} (hz : z ∈ unitDisc) : Summable (fun p => ‖basisE p z‖) := by
  have hr : ‖‖z‖‖ < 1 := by rw [norm_norm]; exact mem_ball_zero_iff.mp hz
  have hs := (summable_pow_mul_geometric_of_norm_lt_one 1 hr).add (summable_geometric_of_norm_lt_one hr)
  refine hs.of_nonneg_of_le (fun _ => norm_nonneg _) (fun p => ?_)
  have hsq : Real.sqrt (((p : ℝ) + 1) / π) ≤ (p : ℝ) + 1 := by
    rw [Real.sqrt_le_iff]
    refine ⟨by positivity, ?_⟩
    have h1 : (1 : ℝ) ≤ π := by linarith [Real.pi_gt_three]
    rw [div_le_iff₀ Real.pi_pos]
    nlinarith [sq_nonneg ((p : ℝ) + 1), (by positivity : (0 : ℝ) ≤ (p : ℝ) + 1)]
  simp only [basisE, norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _), norm_pow]
  have : (p : ℝ) ^ 1 * ‖z‖ ^ p + ‖z‖ ^ p = ((p : ℝ) + 1) * ‖z‖ ^ p := by ring
  simp only [Real.norm_eq_abs, abs_norm, pow_one] at this ⊢
  nlinarith [mul_le_mul_of_nonneg_right hsq (pow_nonneg (norm_nonneg z) p)]

theorem e24_absF {z : ℂ} (hz : z ∈ unitDiscExterior) : Summable (fun p => ‖basisF p z‖) := by
  have hz1 : 1 < ‖z‖ := hz
  have hz0 : z ≠ 0 := norm_pos_iff.mp (by linarith)
  have hr : ‖‖z⁻¹‖‖ < 1 := by
    rw [norm_norm, norm_inv]; exact inv_lt_one_of_one_lt₀ hz1
  have hs := ((summable_pow_mul_geometric_of_norm_lt_one 1 hr).add
    (summable_geometric_of_norm_lt_one hr)).mul_left (‖z⁻¹‖ ^ 2)
  refine hs.of_nonneg_of_le (fun _ => norm_nonneg _) (fun p => ?_)
  have hsq : Real.sqrt (((p : ℝ) + 1) / π) ≤ (p : ℝ) + 1 := by
    rw [Real.sqrt_le_iff]
    refine ⟨by positivity, ?_⟩
    have h1 : (1 : ℝ) ≤ π := by linarith [Real.pi_gt_three]
    rw [div_le_iff₀ Real.pi_pos]
    nlinarith [sq_nonneg ((p : ℝ) + 1), (by positivity : (0 : ℝ) ≤ (p : ℝ) + 1)]
  have hzp : z ^ (-(p : ℤ) - 2) = (z⁻¹) ^ (p + 2) := by
    rw [show (-(p : ℤ) - 2) = -((p + 2 : ℕ) : ℤ) by push_cast; ring, zpow_neg, zpow_natCast, inv_pow]
  simp only [basisF, hzp, norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _), norm_pow,
    Real.norm_eq_abs, abs_norm, pow_one, pow_add]
  have h0 : 0 ≤ ‖z⁻¹‖ ^ p * ‖z⁻¹‖ ^ 2 := by positivity
  nlinarith [mul_le_mul_of_nonneg_right hsq h0]


theorem e24_K2_series {f g : ℂ → ℂ} (h : IsNormalizedDisjointPair f g) {z u : ℂ} (hz : z ∈ unitDisc)
    (hu : u ∈ unitDiscExterior) :
    HasSum (fun p : ℕ × ℕ => B2 (grunsky f g) p.1 p.2 * basisE p.1 z * basisF p.2 u)
      (kerK2 f g z u) := by
  have hu1 : 1 < ‖u‖ := hu
  have hu0 : u ≠ 0 := norm_pos_iff.mp (by linarith)
  have hs : u⁻¹ ∈ unitDisc :=
    mem_ball_zero_iff.mpr (by rw [norm_inv]; exact inv_lt_one_of_one_lt₀ hu1)
  have := e24_K2_aux h hz hs (inv_ne_zero hu0)
  rwa [inv_inv] at this

theorem e24_hK1 {f g : ℂ → ℂ} (h : IsNormalizedDisjointPair f g) :
    ∀ z ∈ unitDisc, ∀ w ∈ unitDisc, z ≠ w →
      HasSum (fun p : ℕ × ℕ => B1 (grunsky f g) p.1 p.2 * basisE p.1 z * basisE p.2 w) (kerK1 f z w) := by
  intro z hz w hw hzw
  have hb := (grunsky_spec h).1.2.2.2.1
  have hser := s2c_kernel_series_of_exp (a := fun p q => grunsky f g (-(p : ℤ)) (-(q : ℤ)))
    (b00 := grunsky f g 0 0) h.1 h.2.1 hb hz hw hzw
  have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hsum := hser.div_const (π : ℂ)
  have he : ((π : ℂ) * kerK1 f z w) / (π : ℂ) = kerK1 f z w := by field_simp
  rw [he] at hsum
  refine hsum.congr_fun (fun p => ?_)
  rw [← g2c_basis_weight (fun p q => grunsky f g (-(p : ℤ)) (-(q : ℤ))) p.1 p.2 z w]
  simp only [B1, Nat.cast_add, Nat.cast_one, neg_add]

theorem e24_hK4 {f g : ℂ → ℂ} (h : IsNormalizedDisjointPair f g)
    (hF : volume ((f '' unitDisc ∪ g '' unitDiscExterior)ᶜ) = 0) :
    ∀ z ∈ unitDiscExterior, ∀ w ∈ unitDiscExterior, z ≠ w →
      HasSum (fun p : ℕ × ℕ => B4 (grunsky f g) p.1 p.2 * basisF p.1 z * basisF p.2 w) (kerK4 g z w) := by
  intro z hz w hw hzw
  have hK := (s2c_kernels_spec h hF).2.1 z hz w hw hzw
  refine hK.congr_fun (fun p => ?_)
  have h3 := e24_sqrt3 p.1 p.2
  simp only [B4, basisF]
  push_cast at h3 ⊢
  linear_combination (grunsky f g ((p.1 : ℤ) + 1) ((p.2 : ℤ) + 1) * z ^ (-(p.1 : ℤ) - 2) *
    w ^ (-(p.2 : ℤ) - 2)) * h3

/-- **(2.4)** (TT:4000–4006). `𝖪₂ = I - 𝖪₁` and `𝖪₃ = I - 𝖪₄`. The identity kernels are `1/(π(1 - z w̄)²)` on `A₂¹(𝔻)`
and on `A₂¹(𝔻*)`. -/
theorem s2c_eq_2_4 {f g : ℂ → ℂ} (h : IsNormalizedDisjointPair f g)
    (hF : volume ((f '' unitDisc ∪ g '' unitDiscExterior)ᶜ) = 0) :
    (∀ z ∈ unitDisc, ∀ w ∈ unitDisc, kerKK2 f g z w = 1 / (π * (1 - z * conj w) ^ 2) - kerKK1 f z w) ∧
      ∀ z ∈ unitDiscExterior, ∀ w ∈ unitDiscExterior,
        kerKK3 f g z w = 1 / (π * (1 - z * conj w) ^ 2) - kerKK4 g z w := by
  obtain ⟨-, -, -, -, -, hA1, hA2, hA3, hA4⟩ := mg_eq_2_2_core h hF (B1 := B1 (grunsky f g))
    (B2 := B2 (grunsky f g)) (B3 := B3 (grunsky f g)) (B4 := B4 (grunsky f g))
    (fun m n => rfl) (fun m n => rfl) (fun m n => rfl) (fun m n => rfl)
  obtain ⟨hsy, hcol1, hcol2, -⟩ := mg_unitary_core h hF (B1 := B1 (grunsky f g))
    (B2 := B2 (grunsky f g)) (B3 := B3 (grunsky f g)) (B4 := B4 (grunsky f g))
    (fun m n => rfl) (fun m n => rfl) (fun m n => rfl) (fun m n => rfl)
  have hcolA : ∀ m n : ℕ, (∑' k, (conj (B1 (grunsky f g) k m) * B1 (grunsky f g) k n +
      conj (B3 (grunsky f g) k m) * B3 (grunsky f g) k n)) = if m = n then 1 else 0 := hcol1
  have hcolB : ∀ m n : ℕ, (∑' k, (conj (B2 (grunsky f g) k m) * B2 (grunsky f g) k n +
      conj (B4 (grunsky f g) k m) * B4 (grunsky f g) k n)) = if m = n then 1 else 0 := hcol2
  refine ⟨fun z hz w hw => ?_, fun z hz w hw => ?_⟩
  · have hv := e24_absE hz
    have hv' := e24_absE hw
    obtain ⟨hx1, hx3⟩ := e24_pair_sq (v := fun p => basisE p z) hcolA hv
    obtain ⟨hy1, hy3⟩ := e24_pair_sq (v := fun p => basisE p w) hcolA hv'
    have hconv1 : ∀ (u : ℂ), u ∈ unitDisc → ∀ n, Summable (fun m => B1 (grunsky f g) n m * basisE m u) :=
      fun u hu n => (bergman_pair_summable (hA1 n) (basisE_sq_summable hu)).of_norm
    have hconv3 : ∀ (u : ℂ), u ∈ unitDisc → ∀ n, Summable (fun m => B3 (grunsky f g) n m * basisE m u) :=
      fun u hu n => (bergman_pair_summable (hA3 n) (basisE_sq_summable hu)).of_norm
    have hK1exp : ∀ u0 ∈ unitDisc, ∀ u ∈ unitDisc, u0 ≠ u →
        HasSum (fun n => (∑' m, B1 (grunsky f g) n m * basisE m u0) * basisE n u) (kerK1 f u0 u) :=
      fun u0 hu0 u hu hne => g2c_kernel_row_series (fun m n => (hsy m n).1) (e24_hK1 h) hu0 hu hne
        (hconv1 u0 hu0)
    have hK2exp : ∀ u0 ∈ unitDisc, ∀ u ∈ unitDiscExterior,
        HasSum (fun q => (∑' p, B3 (grunsky f g) q p * basisE p u0) * basisF q u) (kerK2 f g u0 u) := by
      intro u0 hu0 u hu
      have hs := (Equiv.prodComm ℕ ℕ).hasSum_iff.mpr (e24_K2_series h hu0 hu)
      refine hs.prod_fiberwise (fun q => ?_)
      refine ((hconv3 u0 hu0 q).hasSum.mul_right (basisF q u)).congr_fun (fun p => ?_)
      simp only [Function.comp_apply, Equiv.prodComm_apply, Prod.fst_swap, Prod.snd_swap]
      rw [(hsy q p).2.2]
    have hKK1 : HasSum (fun n => (∑' p, B1 (grunsky f g) n p * basisE p z) *
        conj (∑' p, B1 (grunsky f g) n p * basisE p w)) (kerKK1 f z w) := by
      unfold kerKK1
      refine e24_int_pair hx1 hy1 (E := {z, w}) ((Set.toFinite _).measure_zero volume) ?_ ?_
      · intro u hu hn
        exact hK1exp z hz u hu (fun h0 => hn (by simp [h0]))
      · intro u hu hn
        exact hK1exp w hw u hu (fun h0 => hn (by simp [h0]))
    have hKK2 : HasSum (fun n => (∑' p, B3 (grunsky f g) n p * basisE p z) *
        conj (∑' p, B3 (grunsky f g) n p * basisE p w)) (kerKK2 f g z w) := by
      unfold kerKK2
      refine e24_ext_pair hx3 hy3 (E := ∅) Set.finite_empty ?_ ?_
      · intro u hu _
        exact hK2exp z hz u hu
      · intro u hu _
        exact hK2exp w hw u hu
    have htot := e24_pair hcolA hv hv'
    have hval := (e24_sumE hz hw).tsum_eq
    have hadd := hKK1.add hKK2
    have := hadd.unique htot
    rw [hval] at this
    linear_combination this
  · have hv := e24_absF hz
    have hv' := e24_absF hw
    obtain ⟨hx2, hx4⟩ := e24_pair_sq (v := fun p => basisF p z) hcolB hv
    obtain ⟨hy2, hy4⟩ := e24_pair_sq (v := fun p => basisF p w) hcolB hv'
    have hconv2 : ∀ (u : ℂ), u ∈ unitDiscExterior → ∀ n,
        Summable (fun m => B2 (grunsky f g) n m * basisF m u) :=
      fun u hu n => (bergman_pair_summable (hA2 n) (e24_sq_of_abs (e24_absF hu))).of_norm
    have hconv4 : ∀ (u : ℂ), u ∈ unitDiscExterior → ∀ n,
        Summable (fun m => B4 (grunsky f g) n m * basisF m u) :=
      fun u hu n => (bergman_pair_summable (hA4 n) (e24_sq_of_abs (e24_absF hu))).of_norm
    have hK3exp : ∀ u0 ∈ unitDiscExterior, ∀ u ∈ unitDisc,
        HasSum (fun n => (∑' q, B2 (grunsky f g) n q * basisF q u0) * basisE n u) (kerK3 f g u0 u) := by
      intro u0 hu0 u hu
      rw [e24_K3_eq]
      refine (e24_K2_series h hu hu0).prod_fiberwise (fun n => ?_)
      refine ((hconv2 u0 hu0 n).hasSum.mul_right (basisE n u)).congr_fun (fun q => ?_)
      ring
    have hK4exp : ∀ u0 ∈ unitDiscExterior, ∀ u ∈ unitDiscExterior, u0 ≠ u →
        HasSum (fun q => (∑' p, B4 (grunsky f g) q p * basisF p u0) * basisF q u) (kerK4 g u0 u) := by
      intro u0 hu0 u hu hne
      have hs := (Equiv.prodComm ℕ ℕ).hasSum_iff.mpr (e24_hK4 h hF u0 hu0 u hu hne)
      refine hs.prod_fiberwise (fun q => ?_)
      refine ((hconv4 u0 hu0 q).hasSum.mul_right (basisF q u)).congr_fun (fun p => ?_)
      simp only [Function.comp_apply, Equiv.prodComm_apply, Prod.fst_swap, Prod.snd_swap]
      rw [(hsy q p).2.1]
    have hKK3 : HasSum (fun n => (∑' p, B2 (grunsky f g) n p * basisF p z) *
        conj (∑' p, B2 (grunsky f g) n p * basisF p w)) (kerKK3 f g z w) := by
      unfold kerKK3
      refine e24_int_pair hx2 hy2 (E := ∅) (by simp) ?_ ?_
      · intro u hu _
        exact hK3exp z hz u hu
      · intro u hu _
        exact hK3exp w hw u hu
    have hKK4 : HasSum (fun n => (∑' p, B4 (grunsky f g) n p * basisF p z) *
        conj (∑' p, B4 (grunsky f g) n p * basisF p w)) (kerKK4 g z w) := by
      unfold kerKK4
      refine e24_ext_pair hx4 hy4 (E := {z, w}) (Set.toFinite _) ?_ ?_
      · intro u hu hn
        exact hK4exp z hz u hu (fun h0 => hn (by simp [h0]))
      · intro u hu hn
        exact hK4exp w hw u hu (fun h0 => hn (by simp [h0]))
    have htot := e24_pair hcolB hv hv'
    have hval := (e24_sumF hz hw).tsum_eq
    have hadd := hKK3.add hKK4
    have := hadd.unique htot
    rw [hval] at this
    linear_combination this

/-! ### Original relocated (2026-10-26) -/

/-- **(2.4)** (TT:4000–4006). `𝖪₂ = I - 𝖪₁` and `𝖪₃ = I - 𝖪₄`. The identity kernels are `1/(π(1 - z w̄)²)` on `A₂¹(𝔻)`
and on `A₂¹(𝔻*)`. -/
theorem eq_2_4 {f g : ℂ → ℂ} (h : IsNormalizedDisjointPair f g)
    (hF : volume ((f '' unitDisc ∪ g '' unitDiscExterior)ᶜ) = 0) :
    (∀ z ∈ unitDisc, ∀ w ∈ unitDisc, kerKK2 f g z w = 1 / (π * (1 - z * conj w) ^ 2) - kerKK1 f z w) ∧
      ∀ z ∈ unitDiscExterior, ∀ w ∈ unitDiscExterior,
        kerKK3 f g z w = 1 / (π * (1 - z * conj w) ^ 2) - kerKK4 g z w :=
  s2c_eq_2_4 h hF

end TakhtajanTeo.Ch2
