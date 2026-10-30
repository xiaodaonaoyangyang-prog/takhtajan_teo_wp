import TakhtajanTeo.Ch2.S2_Completed
import TakhtajanTeo.Ch1.BersInjective

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal ComplexConjugate Classical Real
noncomputable section
namespace TakhtajanTeo.Ch2
open LiZhongQC

/-- `𝒮(f)(z) = -6 Σ (p+1)(q+1) a_{p+1,q+1} z^{p+q}` on the diagonal, from the Grunsky array. -/
theorem s2c_schwarzian_series {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f unitDisc) (hi : InjOn f unitDisc)
    {a : ℕ → ℕ → ℂ} {b00 : ℂ}
    (hexp : ∀ z ∈ unitDisc, ∀ w ∈ unitDisc, z ≠ w → ∃ S : ℂ,
      HasSum (fun p : ℕ × ℕ => a p.1 p.2 * z ^ p.1 * w ^ p.2) S ∧
        (f z - f w) / (z - w) = exp (b00 - S))
    {z : ℂ} (hz : z ∈ unitDisc) :
    schwarzianHol f z = -6 * ∑' r : ℕ × ℕ,
      (a (r.1 + 1) (r.2 + 1) * ((r.1 + 1 : ℕ) : ℂ) * ((r.2 + 1 : ℕ) : ℂ)) * z ^ r.1 * z ^ r.2 := by
  let c : ℕ → ℕ → ℂ := fun p q => a (p + 1) (q + 1) * ((p + 1 : ℕ) : ℂ) * ((q + 1 : ℕ) : ℂ)
  have hser : ∀ z ∈ unitDisc, ∀ w ∈ unitDisc, z ≠ w →
      HasSum (fun p : ℕ × ℕ => c p.1 p.2 * z ^ p.1 * w ^ p.2) ((π : ℂ) * kerK1 f z w) :=
    fun z hz w hw hzw => s2c_kernel_series_of_exp hf hi hexp hz hw hzw
  have hs0 := s2c_bidisk_hasSum (a := c) (fun z hz w hw hzw => (hser z hz w hw hzw).summable)
  obtain ⟨F, hFdef⟩ : ∃ F : ℂ → ℂ → ℂ,
      F = fun z w => ∑' p : ℕ × ℕ, c p.1 p.2 * z ^ p.1 * w ^ p.2 := ⟨_, rfl⟩
  have hs : ∀ z ∈ unitDisc, ∀ w ∈ unitDisc,
      HasSum (fun p : ℕ × ℕ => c p.1 p.2 * z ^ p.1 * w ^ p.2) (F z w) := by
    intro z hz w hw
    rw [hFdef]
    exact hs0 z hz w hw
  have hFK : ∀ z ∈ unitDisc, ∀ w ∈ unitDisc, z ≠ w → F z w = (π : ℂ) * kerK1 f z w :=
    fun z hz w hw hzw => (hs z hz w hw).unique (hser z hz w hw hzw)
  have hcont := s2c_bidisk_continuousOn hs
  have hzz : (z, z) ∈ unitDisc ×ˢ unitDisc := ⟨hz, hz⟩
  have hat : ContinuousAt (fun x : ℂ × ℂ => F x.1 x.2) (z, z) :=
    hcont.continuousAt ((isOpen_ball.prod isOpen_ball).mem_nhds hzz)
  have hT2 : Tendsto (fun w => F z w) (𝓝[≠] z) (𝓝 (F z z)) := by
    have h1 : Tendsto (fun w : ℂ => (z, w)) (𝓝 z) (𝓝 (z, z)) :=
      (continuous_const.prodMk continuous_id).tendsto z
    exact (hat.tendsto.comp h1).mono_left nhdsWithin_le_nhds
  have hT1 := s2c_schwarzian_limit hf hi hz
  have hT1' : Tendsto (fun w => -6 * F z w) (𝓝[≠] z) (𝓝 (schwarzianHol f z)) := by
    refine hT1.congr' ?_
    have hD : ∀ᶠ w in 𝓝[≠] z, w ∈ unitDisc :=
      nhdsWithin_le_nhds ((isOpen_ball : IsOpen unitDisc).mem_nhds hz)
    filter_upwards [self_mem_nhdsWithin, hD] with w hw hwD
    have hw' : w ≠ z := hw
    rw [hFK z hz w hwD (Ne.symm hw')]
    ring
  have hT2' : Tendsto (fun w => -6 * F z w) (𝓝[≠] z) (𝓝 (-6 * F z z)) := hT2.const_mul (-6)
  have := tendsto_nhds_unique hT1' hT2'
  rw [this, hFdef]

/-- The Schwarzian of the disc function of a normalized pair, from its Grunsky coefficients. -/
theorem s2c_schwarzian_grunsky {f g : ℂ → ℂ} (h : IsNormalizedDisjointPair f g)
    {z : ℂ} (hz : z ∈ unitDisc) :
    schwarzianHol f z = -6 * ∑' r : ℕ × ℕ,
      (grunsky f g (-((r.1 : ℤ) + 1)) (-((r.2 : ℤ) + 1)) * ((r.1 + 1 : ℕ) : ℂ) * ((r.2 + 1 : ℕ) : ℂ)) *
        z ^ r.1 * z ^ r.2 := by
  have h1 := s2c_schwarzian_series h.1 h.2.1
    (a := fun m n => grunsky f g (-(m : ℤ)) (-(n : ℤ))) (b00 := grunsky f g 0 0)
    (grunsky_spec h).1.2.2.2.1 hz
  rw [h1]
  congr 2

/-- (TT:4204) `𝒫` is one to one on `T₀(1)`: Grunsky coefficients determine univalent functions up to Möbius maps. 
Proved here as `s2c_periodP_injective`; statement identical to `periodP_injective`. -/
theorem s2c_periodP_injective : InjOn periodP T01 := by
  intro p _ q _ he
  have hμ : (Quotient.out p : LinfStarBall).1 ∈ LinfStarBall := (Quotient.out p : LinfStarBall).2
  have hν : (Quotient.out q : LinfStarBall).1 ∈ LinfStarBall := (Quotient.out q : LinfStarBall).2
  have hpμ := AppB.b8_welding_normalized_pair hμ
  have hpν := AppB.b8_welding_normalized_pair hν
  have hcoef : ∀ m n : ℕ,
      grunsky (fsans (Quotient.out p : LinfStarBall)) (gsans (Quotient.out p : LinfStarBall))
        (-((m : ℤ) + 1)) (-((n : ℤ) + 1)) =
      grunsky (fsans (Quotient.out q : LinfStarBall)) (gsans (Quotient.out q : LinfStarBall))
        (-((m : ℤ) + 1)) (-((n : ℤ) + 1)) := by
    intro m n
    have h1 := congrFun (congrFun he m) n
    simp only [periodP, B1] at h1
    have hpos : (Real.sqrt (((m : ℝ) + 1) * ((n : ℝ) + 1)) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.2 (Real.sqrt_pos.2 (by positivity)).ne'
    exact mul_left_cancel₀ hpos (by simpa using h1)
  have hS : ∀ z ∈ unitDisc, schwarzianHol (fB (Quotient.out p : LinfStarBall)) z =
      schwarzianHol (fB (Quotient.out q : LinfStarBall)) z := by
    intro z hz
    rw [← AppB.b1_fsans_eq hμ, ← AppB.b1_fsans_eq hν, s2c_schwarzian_grunsky hpμ hz,
      s2c_schwarzian_grunsky hpν hz]
    exact congrArg (fun t => -6 * t) (tsum_congr fun r => by rw [hcoef r.1 r.2])
  have hb : bers p = bers q := by
    apply AInf.ext_toFun_disc
    intro z hz
    unfold bers
    rw [(bersPhi_spec hμ).1 z hz, (bersPhi_spec hν).1 z hz]
    exact hS z hz
  exact bers_injective hb

/-! ### Original relocated (2026-10-26) -/

/-- (TT:4204) `𝒫` is one to one on `T₀(1)`: Grunsky coefficients determine univalent functions up to Möbius maps. -/
theorem periodP_injective : InjOn periodP T01 :=
  s2c_periodP_injective

end TakhtajanTeo.Ch2
