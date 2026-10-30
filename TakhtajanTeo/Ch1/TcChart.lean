import TakhtajanTeo.Appendix.AppACor2

/-!
# `tcCoord_chart` (`tcc_`, 下属3): global holomorphic coordinates on `𝒯(1)`

Host: new module `TakhtajanTeo/Ch1/TcChart.lean`. It imports `Appendix.AppACor2`, whose closure contains:
- `Ch1.S5_ChernForms` (`tcCoord`);
- `Ch1.BersInjective` (`bers_injective`);
- `Appendix.AppACont` (`acc_wB_cont`);
- `AppA.ac2g_section`.

The target `tcc_tcCoord_chart` is `tcCoord_chart` (S5) with the prefixed name and a byte-identical statement (relocated
at round end).

**Route.**
* Injectivity:
  - `bers_injective` handles the first coordinate.
  - The second coordinate `finPart ∘ inversion` is injective off `0` (`tcc_inversion_invol`,
    `tcc_inversion_eq_inf_iff`).
  - `0 = w^μ(0)` is not in the fibre `w^μ(𝔻* ∪ ∞)` (`tcc_zero_not_mem`).
* Openness at `tcCoord (p, z)`:
  - `ac2g_section p` gives `s`, continuous at `bers p`, with `s (bers p) = out p` and `bers [s χ] = χ` near `bers p`.
  - The map `(χ, ζ) ↦ (s χ, inversion ζ)` is continuous at the point and sends it to `(out p, z)`.
  - `tcc_tube`: fibre membership is an open condition in `(μ, z)`. This is a tube lemma over the compact disc
    `toExt (closedBall 0 1)` (`IsCompact.eventually_forall_of_forall_eventually`), using `acc_wB_cont` and
    bijectivity of `wB μ`.
  - `tcc_mem_image` puts the nearby points in the image (`fiber_independent`, `bers_Phi`).
-/

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal ComplexConjugate Classical Real

noncomputable section

namespace TakhtajanTeo

open LiZhongQC

/-- `ι(z) = 1/z` is an involution of `ℂ̄`. -/
theorem tcc_inversion_invol (z : ExtPlane) : inversion (inversion z) = z := by
  induction z using OnePoint.rec with
  | infty => simp [inversion, mobiusExt, extInf]
  | coe z =>
    by_cases hz : z = 0
    · subst hz; simp [inversion, mobiusExt, extInf]
    · simp [inversion, mobiusExt, hz]

/-- `ι(z) = ∞` exactly at `z = 0`. -/
theorem tcc_inversion_eq_inf_iff (z : ExtPlane) : inversion z = extInf ↔ z = ((0 : ℂ) : ExtPlane) := by
  induction z using OnePoint.rec with
  | infty => simp [inversion, mobiusExt, extInf]
  | coe z =>
    by_cases hz : z = 0
    · subst hz; simp [inversion, mobiusExt, extInf]
    · simp [inversion, mobiusExt, extInf, hz]

/-- `ι` is continuous on `ℂ̄`. -/
theorem tcc_inversion_continuous : Continuous inversion := by
  rw [continuous_iff_continuousAt]
  intro w
  have hU : IsOpen {x : ℂ × ℂ × ℂ × ℂ | x.1 * x.2.2.2 - x.2.1 * x.2.2.1 ≠ 0} :=
    isOpen_ne_fun (by fun_prop) continuous_const
  have hmem : (((0 : ℂ), (1 : ℂ), (1 : ℂ), (0 : ℂ)), w) ∈
      {x : ℂ × ℂ × ℂ × ℂ | x.1 * x.2.2.2 - x.2.1 * x.2.2.1 ≠ 0} ×ˢ (univ : Set ExtPlane) :=
    ⟨by norm_num, mem_univ _⟩
  have hc := AppA.acc_mob_cont.continuousAt ((hU.prod isOpen_univ).mem_nhds hmem)
  exact hc.comp (f := fun w : ExtPlane => (((0 : ℂ), (1 : ℂ), (1 : ℂ), (0 : ℂ)), w))
    (continuous_const.prodMk continuous_id).continuousAt

/-- `0 = w^μ(0)` does not lie in the fibre `w^μ(𝔻* ∪ ∞)`. -/
theorem tcc_zero_not_mem {μ : LinfStar} (hμ : μ ∈ LinfStarBall) :
    ((0 : ℂ) : ExtPlane) ∉ wB μ '' extDiscExterior := by
  rintro ⟨y, hy, hy0⟩
  have hw0 : wB μ ((0 : ℂ) : ExtPlane) = ((0 : ℂ) : ExtPlane) := by
    rw [Ch2.e13_wB_disc hμ (u := 0) (by simp [unitDisc]), (fB_normalization μ).1]
  have hy' : y = ((0 : ℂ) : ExtPlane) := (wB_bijective μ).1 (hy0.trans hw0.symm)
  rw [fi_extDiscExterior_eq_compl, hy'] at hy
  exact hy ⟨0, by simp, rfl⟩

/-- Fibre membership `z ∈ w^μ(𝔻* ∪ ∞)` is an open condition in `(μ, z)` near points with `μ ∈ L∞(𝔻*)₁`. -/
theorem tcc_tube {ν : LinfStar} (hν : ν ∈ LinfStarBall) {z₀ : ExtPlane} (hz₀ : z₀ ∈ wB ν '' extDiscExterior) :
    ∀ᶠ x in 𝓝 (ν, z₀), x.2 ∈ wB x.1 '' extDiscExterior := by
  have hKc : IsCompact (toExt (closedBall (0 : ℂ) 1)) :=
    (isCompact_closedBall (0 : ℂ) 1).image OnePoint.continuous_coe
  obtain ⟨w₀, hw₀, rfl⟩ := hz₀
  have hP : ∀ k ∈ toExt (closedBall (0 : ℂ) 1), ∀ᶠ y : (LinfStar × ExtPlane) × ExtPlane in 𝓝 ((ν, wB ν w₀), k),
      wB y.1.1 y.2 ≠ y.1.2 := by
    intro k hk
    have hne : wB ν k ≠ wB ν w₀ := by
      intro he
      have hkw : k = w₀ := (wB_bijective ν).1 he
      rw [fi_extDiscExterior_eq_compl] at hw₀
      rw [hkw] at hk
      exact hw₀ hk
    have hcont : ContinuousAt (fun p : LinfStar × ExtPlane => wB p.1 p.2) (ν, k) :=
      AppA.acc_wB_cont.continuousAt ((isOpen_ball.prod isOpen_univ).mem_nhds ⟨hν, mem_univ _⟩)
    have hF : ContinuousAt (fun y : (LinfStar × ExtPlane) × ExtPlane => wB y.1.1 y.2) ((ν, wB ν w₀), k) :=
      ContinuousAt.comp (g := fun p : LinfStar × ExtPlane => wB p.1 p.2)
        (f := fun y : (LinfStar × ExtPlane) × ExtPlane => (y.1.1, y.2)) (x := ((ν, wB ν w₀), k)) hcont
        ((continuous_fst.comp continuous_fst).prodMk continuous_snd).continuousAt
    have hG : ContinuousAt (fun y : (LinfStar × ExtPlane) × ExtPlane => y.1.2) ((ν, wB ν w₀), k) :=
      (continuous_snd.comp continuous_fst).continuousAt
    have hopen : IsOpen {q : ExtPlane × ExtPlane | q.1 ≠ q.2} := isOpen_ne_fun continuous_fst continuous_snd
    exact (hF.prodMk hG).eventually (hopen.mem_nhds (show wB ν k ≠ wB ν w₀ from hne))
  have hall : ∀ᶠ x in 𝓝 (ν, wB ν w₀), ∀ k ∈ toExt (closedBall (0 : ℂ) 1), wB x.1 k ≠ x.2 :=
    hKc.eventually_forall_of_forall_eventually hP
  filter_upwards [hall] with x hx
  obtain ⟨k, hk⟩ := (wB_bijective x.1).2 x.2
  refine ⟨k, ?_, hk⟩
  rw [fi_extDiscExterior_eq_compl]
  exact fun hkK => hx k hkK hk

/-- A point of the fibre of `[μ]` gives a point of `tcCoord '' 𝒯(1)`. -/
theorem tcc_mem_image {μ : LinfStar} (hμ : μ ∈ LinfStarBall) {z : ExtPlane} (hz : z ∈ wB μ '' extDiscExterior) :
    (bers (Phi ⟨μ, hμ⟩), finPart (inversion z)) ∈ tcCoord '' TCurve := by
  refine ⟨(Phi ⟨μ, hμ⟩, z), ?_, rfl⟩
  have hs : teichSetoid (Quotient.out (Phi ⟨μ, hμ⟩) : LinfStarBall) ⟨μ, hμ⟩ :=
    Quotient.mk_out (s := teichSetoid) (⟨μ, hμ⟩ : LinfStarBall)
  show z ∈ wB (Quotient.out (Phi ⟨μ, hμ⟩) : LinfStarBall) '' extDiscExterior
  rw [fiber_independent hs]
  exact hz

/-- (TT:568) `𝒯(1)` is a complex Banach manifold modeled on `A∞(𝔻) ⊕ ℂ`, with global coordinates `tcCoord`: the map
is injective on `𝒯(1)` with open image, and `π : 𝒯(1) → T(1)` is holomorphic (in coordinates it is the first
projection). -/
theorem tcc_tcCoord_chart : InjOn tcCoord TCurve ∧ IsOpen (tcCoord '' TCurve) := by
  have hne : ∀ q ∈ TCurve, q.2 ≠ ((0 : ℂ) : ExtPlane) := fun q hq h0 =>
    tcc_zero_not_mem (Quotient.out q.1 : LinfStarBall).2 (h0 ▸ hq)
  have hback : ∀ z : ExtPlane, z ≠ ((0 : ℂ) : ExtPlane) →
      inversion ((finPart (inversion z) : ℂ) : ExtPlane) = z := by
    intro z hz
    rw [coe_finPart_of_ne (fun h => hz ((tcc_inversion_eq_inf_iff z).mp h)), tcc_inversion_invol]
  constructor
  · rintro ⟨p, z⟩ hq ⟨p', z'⟩ hq' he
    simp only [tcCoord, Prod.mk.injEq] at he
    have hp : p = p' := bers_injective he.1
    subst hp
    have h2 := congrArg (fun ζ : ℂ => inversion (ζ : ExtPlane)) he.2
    rw [hback z (hne _ hq), hback z' (hne _ hq')] at h2
    rw [h2]
  · rw [isOpen_iff_mem_nhds]
    rintro x ⟨⟨p, z⟩, hq, rfl⟩
    show tcCoord '' TCurve ∈ 𝓝 ((bers p, finPart (inversion z)) : AInf unitDisc × ℂ)
    obtain ⟨s, hsc, hs0, hev⟩ := AppA.ac2g_section p
    have hν := (Quotient.out p : LinfStarBall).2
    have hT := tcc_tube hν hq
    set m : AInf unitDisc × ℂ → LinfStar × ExtPlane := fun y => (s y.1, inversion (y.2 : ExtPlane)) with hm
    have hm0 : m (bers p, finPart (inversion z)) = (((Quotient.out p : LinfStarBall) : LinfStar), z) := by
      simp only [hm]
      rw [hs0, hback z (hne _ hq)]
    have hmc : ContinuousAt m (bers p, finPart (inversion z)) := by
      refine ContinuousAt.prodMk (hsc.comp (f := Prod.fst) continuousAt_fst) ?_
      exact (tcc_inversion_continuous.comp OnePoint.continuous_coe).continuousAt.comp continuousAt_snd
    have hT' : ∀ᶠ y in 𝓝 ((bers p, finPart (inversion z)) : AInf unitDisc × ℂ), (m y).2 ∈ wB (m y).1 '' extDiscExterior := by
      have := hmc.tendsto
      rw [hm0] at this
      exact this.eventually hT
    have hfst : Tendsto (Prod.fst : AInf unitDisc × ℂ → AInf unitDisc)
        (𝓝 ((bers p, finPart (inversion z)) : AInf unitDisc × ℂ)) (𝓝 (bers p)) := continuousAt_fst
    have hev' := hfst.eventually hev
    filter_upwards [hT', hev'] with y hy1 hy2
    obtain ⟨h, hb⟩ := hy2
    have hy := tcc_mem_image h hy1
    have hfin : finPart (inversion (inversion (y.2 : ExtPlane))) = y.2 := by
      rw [tcc_inversion_invol]; rfl
    simp only [hm] at hy
    rw [hb, hfin] at hy
    exact hy

/-- (TT:568) `𝒯(1)` is a complex Banach manifold modeled on `A∞(𝔻) ⊕ ℂ`, with global coordinates `tcCoord`: the map
is injective on `𝒯(1)` with open image, and `π : 𝒯(1) → T(1)` is holomorphic (in coordinates it is the first
projection). -/
theorem tcCoord_chart : InjOn tcCoord TCurve ∧ IsOpen (tcCoord '' TCurve) :=
  tcc_tcCoord_chart

end TakhtajanTeo
