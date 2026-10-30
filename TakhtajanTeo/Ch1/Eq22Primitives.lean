import TakhtajanTeo.Appendix.BergmanPeriodModel
import LiZhongQC.Ch02.S13_Representation
import Mathlib.Analysis.Complex.HasPrimitives

/-!
# Holomorphic primitives on the interior welding domain

Pull back the one-form `q(w) dw` to the disk, take its existing disk primitive,
and compose with the actual conformal inverse. Iterate the construction on
the image domain; no convexity or boundary regularity of that domain is used.
-/

open Complex Set Filter Topology Metric

namespace TakhtajanTeo
open LiZhongQC

/-- A holomorphic function on a conformal disk image has a primitive there,
with an ordinary complex derivative at every point of the image. -/
theorem eq22_primitive_on_conformal_disc {f q : ℂ → ℂ}
    (hf : IsConformalOnto f unitDisc (f '' unitDisc))
    (hq : DifferentiableOn ℂ q (f '' unitDisc)) :
    ∃ Q : ℂ → ℂ, DifferentiableOn ℂ Q (f '' unitDisc) ∧
      ∀ z ∈ f '' unitDisc, HasDerivAt Q (q z) z := by
  have hpull : DifferentiableOn ℂ
      (fun ζ => q (f ζ) * deriv f ζ) unitDisc :=
    (hq.comp hf.1 (fun ζ hζ => mem_image_of_mem f hζ)).mul
      (hf.1.deriv isOpen_ball)
  obtain ⟨P, hP⟩ := hpull.isExactOn_ball
  let g := Function.invFunOn f unitDisc
  have hpoint : ∀ z ∈ f '' unitDisc, HasDerivAt (P ∘ g) (q z) z := by
    rintro _ ⟨ζ, hζ, rfl⟩
    have hleft : g (f ζ) = ζ := hf.2.1.leftInvOn_invFunOn hζ
    have hgmem : g (f ζ) ∈ unitDisc := by rwa [hleft]
    have hgd : DifferentiableAt ℂ g (f ζ) :=
      hf.differentiableAt_invFunOn isOpen_ball hζ
    have hcancel : deriv f ζ * deriv g (f ζ) = 1 := by
      simpa only [g, unitDisc, mul_comm] using
        t1_deriv_invFunOn_mul (U := unitDisc) isOpen_ball hf hζ
    have hchain := (hP (g (f ζ)) hgmem).comp (f ζ) hgd.hasDerivAt
    simpa only [hleft, mul_assoc, hcancel, mul_one] using hchain
  exact ⟨P ∘ g, fun z hz => (hpoint z hz).differentiableAt.differentiableWithinAt,
    hpoint⟩

/-- Triple primitives on any conformal disk image, all normalized at the same
specified point. In particular the point may be any chosen `a ∈ Ω`. -/
theorem eq22_triple_primitives_on_conformal_disc {f q : ℂ → ℂ} {Ω : Set ℂ}
    (hf : IsConformalOnto f unitDisc Ω) (hq : DifferentiableOn ℂ q Ω) (a : ℂ) :
    ∃ Q1 Q2 Q3 : ℂ → ℂ,
      DifferentiableOn ℂ Q1 Ω ∧ DifferentiableOn ℂ Q2 Ω ∧ DifferentiableOn ℂ Q3 Ω ∧
      Q1 a = 0 ∧ Q2 a = 0 ∧ Q3 a = 0 ∧
      EqOn (deriv Q1) q Ω ∧ EqOn (deriv Q2) Q1 Ω ∧ EqOn (deriv Q3) Q2 Ω := by
  have hprim : ∀ r : ℂ → ℂ, DifferentiableOn ℂ r Ω →
      ∃ Q : ℂ → ℂ, DifferentiableOn ℂ Q Ω ∧ Q a = 0 ∧
        ∀ z ∈ Ω, HasDerivAt Q (r z) z := by
    intro r hr
    have hf' : IsConformalOnto f unitDisc (f '' unitDisc) := ⟨hf.1, hf.2.1, rfl⟩
    obtain ⟨P, hP, hdP⟩ := eq22_primitive_on_conformal_disc hf'
      (show DifferentiableOn ℂ r (f '' unitDisc) by rwa [hf.2.2])
    rw [hf.2.2] at hP hdP
    exact ⟨fun z => P z - P a, hP.sub (differentiableOn_const (P a)), sub_self _,
      fun z hz => (hdP z hz).sub_const (P a)⟩
  obtain ⟨Q1, hQ1, h01, hd1⟩ := hprim q hq
  obtain ⟨Q2, hQ2, h02, hd2⟩ := hprim Q1 hQ1
  obtain ⟨Q3, hQ3, h03, hd3⟩ := hprim Q2 hQ2
  exact ⟨Q1, Q2, Q3, hQ1, hQ2, hQ3, h01, h02, h03,
    fun z hz => (hd1 z hz).deriv, fun z hz => (hd2 z hz).deriv,
    fun z hz => (hd3 z hz).deriv⟩

/-- Three successive holomorphic primitives on the actual interior welding
domain, in the order used by the reflected primitive for equation (2.2). -/
theorem eq22_triple_primitives {μ : LinfStar} (hμ : μ ∈ LinfStarBall)
    {q : ℂ → ℂ} (hq : DifferentiableOn ℂ q (fsans μ '' unitDisc)) :
    ∃ Q1 Q2 Q3 : ℂ → ℂ,
      DifferentiableOn ℂ Q1 (fsans μ '' unitDisc) ∧
      DifferentiableOn ℂ Q2 (fsans μ '' unitDisc) ∧
      DifferentiableOn ℂ Q3 (fsans μ '' unitDisc) ∧
      EqOn (deriv Q1) q (fsans μ '' unitDisc) ∧
      EqOn (deriv Q2) Q1 (fsans μ '' unitDisc) ∧
      EqOn (deriv Q3) Q2 (fsans μ '' unitDisc) := by
  have hfeq : fsans μ = fB μ := by
    ext z
    simp [fsans, AppB.b8_weldConst_zero hμ, lambdaW]
  have hf : IsConformalOnto (fsans μ) unitDisc (fsans μ '' unitDisc) := by
    rw [hfeq]
    obtain ⟨hd, hi⟩ := fB_holomorphic_injective hμ
    exact ⟨hd, hi, rfl⟩
  obtain ⟨Q1, Q2, Q3, hQ1, hQ2, hQ3, -, -, -, hd1, hd2, hd3⟩ :=
    eq22_triple_primitives_on_conformal_disc hf hq 0
  exact ⟨Q1, Q2, Q3, hQ1, hQ2, hQ3, hd1, hd2, hd3⟩

end TakhtajanTeo
