import TakhtajanTeo.Ch1.HomogeneousCompleted
import TakhtajanTeo.Ch1.BeltramiCompose

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal NNReal ComplexConjugate Classical Real
noncomputable section
namespace TakhtajanTeo
open LiZhongQC

theorem wB_glue_props_mob {μ ν : LinfStar} (hν : ν ∈ LinfStarBall)
    {M Minv : ExtPlane → ExtPlane} (hM : IsMobius M) (hMinv : IsMobius Minv)
    (hMl : ∀ p, Minv (M p) = p) (hMr : ∀ p, M (Minv p) = p)
    (hBeq : ∀ p ∈ toExt (closedBall (0 : ℂ) 1), wB μ p = M (wB ν p)) :
    (∀ p ∈ toExt (closedBall (0 : ℂ) 1), Function.invFun (wB ν) (Minv (wB μ p)) = p) ∧
    (∀ p ∉ toExt (closedBall (0 : ℂ) 1), Function.invFun (wB ν) (Minv (wB μ p)) ∉
      toExt (closedBall (0 : ℂ) 1)) := by
  have hMinj : Function.Injective Minv := isMobius_injective hMinv
  refine ⟨fun p hp => ?_, fun p hp hq => ?_⟩
  · rw [hBeq p hp, hMl]
    exact Function.leftInverse_invFun (wB_bijective ν).1 p
  · have e : wB ν (Function.invFun (wB ν) (Minv (wB μ p))) = Minv (wB μ p) :=
      Function.invFun_eq ((wB_bijective ν).2 _)
    have e2 : Minv (wB μ (Function.invFun (wB ν) (Minv (wB μ p)))) =
        wB ν (Function.invFun (wB ν) (Minv (wB μ p))) := by
      rw [hBeq _ hq, hMl]
    have e3 := (wB_bijective μ).1 (hMinj (e2.trans e))
    exact hp (e3 ▸ hq)

theorem wAS_c_diffOn_mob {μ ν : LinfStar} (hμ : μ ∈ LinfStarBall) (hν : ν ∈ LinfStarBall)
    {M Minv : ExtPlane → ExtPlane} (hM : IsMobius M) (hMinv : IsMobius Minv)
    (hMl : ∀ p, Minv (M p) = p) (hMr : ∀ p, M (Minv p) = p)
    (hBeq : ∀ p ∈ toExt (closedBall (0 : ℂ) 1), wB μ p = M (wB ν p)) :
    DifferentiableOn ℂ (fun w : ℂ => finPart (mobiusExt 0 1 1 0 (wAS ν (Function.invFun (wB ν)
      (Minv (wB μ (Function.invFun (wAS μ) (mobiusExt 0 1 1 0 (w : ExtPlane))))))))) unitDisc := by
  obtain ⟨c, hc⟩ : ∃ c : ℂ → ℂ, c = fun w : ℂ => finPart (mobiusExt 0 1 1 0 (wAS ν
      (Function.invFun (wB ν) (Minv (wB μ (Function.invFun (wAS μ) (mobiusExt 0 1 1 0 (w : ExtPlane)))))))) :=
    ⟨_, rfl⟩
  suffices hmain : DifferentiableOn ℂ c unitDisc by
    rw [hc] at hmain
    exact hmain
  obtain ⟨hHid, hHnot⟩ := wB_glue_props_mob hν hM hMinv hMl hMr hBeq
  obtain ⟨Mμ, hMμ, Wμ, hWμ, hwfμ, hwiμ, -, -, -⟩ := wA_spec hμ
  obtain ⟨Mν, hMν, Wν, hWν, hwfν, hwiν, -, -, -⟩ := wA_spec hν
  obtain ⟨Nμ, hNμ, Vμ, hVμ, hvfμ, hviμ, -⟩ := (wB_spec hμ).1
  obtain ⟨Nν, hNν, Vν, hVν, hvfν, hviν, -⟩ := (wB_spec hν).1
  have hMc : Continuous Minv := by
    obtain ⟨a, b, c, d, hdet, rfl⟩ := hMinv
    exact continuous_mobiusExt hdet
  obtain ⟨Mμinv, hMμinv, hMμl, -⟩ := isMobius_inverse hMμ
  obtain ⟨Nνinv, hNνinv, hNνl, -⟩ := isMobius_inverse hNν
  have hσ : IsMobius (mobiusExt 0 1 1 0) := ⟨0, 1, 1, 0, by norm_num, rfl⟩
  have hσi : Function.Injective (mobiusExt 0 1 1 0) := fun a b h => by
    rw [← sigma_invol a, ← sigma_invol b, h]
  have hP : IsMobius (fun p => Mμinv (mobiusExt 0 1 1 0 p)) := isMobius_comp hσ hMμinv
  have hN' : IsMobius (fun p => Nνinv (Minv (Nμ p))) := isMobius_comp (isMobius_comp hNμ hMinv) hNνinv
  have hQ : IsMobius (fun p => mobiusExt 0 1 1 0 (Mν p)) := isMobius_comp hMν hσ
  have hDo : IsOpen {u : ℂ | 1 < ‖u‖} := isOpen_lt continuous_const continuous_norm
  obtain ⟨ψ, hψdef⟩ : ∃ ψ : ℂ → ℂ, ψ = Vμ ∘ Function.invFunOn Wμ {w : ℂ | 1 < ‖w‖} := ⟨_, rfl⟩
  obtain ⟨χ, hχdef⟩ : ∃ χ : ℂ → ℂ, χ = Wν ∘ Function.invFunOn Vν {w : ℂ | 1 < ‖w‖} := ⟨_, rfl⟩
  have hψ := (transition_conformal hWμ hVμ).1
  have hχ := (transition_conformal hWν hVν).2
  rw [← hψdef] at hψ
  rw [← hχdef] at hχ
  obtain ⟨cP, hcP⟩ : ∃ cP : ℂ → ℂ,
      cP = fun u : ℂ => finPart (Mμinv (mobiusExt 0 1 1 0 (u : ExtPlane))) := ⟨_, rfl⟩
  obtain ⟨cN, hcN⟩ : ∃ cN : ℂ → ℂ, cN = fun u : ℂ => finPart (Nνinv (Minv (Nμ (u : ExtPlane)))) := ⟨_, rfl⟩
  obtain ⟨cQ, hcQ⟩ : ∃ cQ : ℂ → ℂ,
      cQ = fun u : ℂ => finPart (mobiusExt 0 1 1 0 (Mν (u : ExtPlane))) := ⟨_, rfl⟩
  have hPc : IsConformalOnto cP {u : ℂ | Mμinv (mobiusExt 0 1 1 0 (u : ExtPlane)) ≠ extInf}
      (cP '' {u : ℂ | Mμinv (mobiusExt 0 1 1 0 (u : ExtPlane)) ≠ extInf}) := by
    rw [hcP]
    exact mobius_finite_conformal hP
  have hNc : IsConformalOnto cN {u : ℂ | Nνinv (Minv (Nμ (u : ExtPlane))) ≠ extInf}
      (cN '' {u : ℂ | Nνinv (Minv (Nμ (u : ExtPlane))) ≠ extInf}) := by
    rw [hcN]
    exact mobius_finite_conformal hN'
  have hQc : IsConformalOnto cQ {u : ℂ | mobiusExt 0 1 1 0 (Mν (u : ExtPlane)) ≠ extInf}
      (cQ '' {u : ℂ | mobiusExt 0 1 1 0 (Mν (u : ExtPlane)) ≠ extInf}) := by
    rw [hcQ]
    exact mobius_finite_conformal hQ
  have hinvA : ∀ q, wAS μ (Function.invFun (wAS μ) q) = q := fun q =>
    Function.invFun_eq ((wAS_bijective μ).2 q)
  have hinvB : ∀ q, wB ν (Function.invFun (wB ν) q) = q := fun q =>
    Function.invFun_eq ((wB_bijective ν).2 q)
  have hinjV : InjOn Vν {w : ℂ | 1 < ‖w‖} := by
    obtain ⟨K, hK⟩ := hVν.1
    exact hK.2.2.1.2.1.mono (subset_univ _)
  have hinjW : InjOn Wμ {w : ℂ | 1 < ‖w‖} := (normalized_solution_injective hWμ).injOn
  -- the first step
  have hA1 : ∀ w ∈ unitDisc, Mμinv (mobiusExt 0 1 1 0 (w : ExtPlane)) ≠ extInf →
      ∃ u₁ : ℂ, Function.invFun (wAS μ) (mobiusExt 0 1 1 0 (w : ExtPlane)) = (u₁ : ExtPlane) ∧
        Wμ u₁ = cP w ∧ 1 < ‖u₁‖ := by
    intro w hw hne
    have hpn := sigma_not_closed hw
    have hq1n : Function.invFun (wAS μ) (mobiusExt 0 1 1 0 (w : ExtPlane)) ∉
        toExt (closedBall (0 : ℂ) 1) := by
      intro h
      rw [wAS_closed_iff hμ, hinvA] at h
      exact hpn h
    exact finite_preimage_data hwfμ hwiμ hMμl (hinvA _) hq1n
      (by rw [hcP]; exact (coe_finPart_of_ne hne).symm)
  have hDmem : ∀ w ∈ unitDisc, Mμinv (mobiusExt 0 1 1 0 (w : ExtPlane)) ≠ extInf →
      cP w ∈ {u : ℂ | 1 < ‖u‖} := by
    intro w hw hne
    obtain ⟨u₁, -, h2, h3⟩ := hA1 w hw hne
    rw [← h2]
    exact normalized_solution_exterior hWμ h3
  -- the second step
  have hA2 : ∀ w ∈ unitDisc, ∀ (hne : Mμinv (mobiusExt 0 1 1 0 (w : ExtPlane)) ≠ extInf),
      Nνinv (Minv (Nμ ((ψ (cP w) : ℂ) : ExtPlane))) ≠ extInf →
      ∃ u₂ : ℂ, Function.invFun (wB ν) (Minv (wB μ (Function.invFun (wAS μ) (mobiusExt 0 1 1 0 (w : ExtPlane))))) = (u₂ : ExtPlane) ∧
        Vν u₂ = cN (ψ (cP w)) ∧ 1 < ‖u₂‖ := by
    intro w hw hne hne2
    obtain ⟨u₁, hq1, hWu, hu1⟩ := hA1 w hw hne
    have hq1n : Function.invFun (wAS μ) (mobiusExt 0 1 1 0 (w : ExtPlane)) ∉
        toExt (closedBall (0 : ℂ) 1) := by
      rw [hq1, coe_mem_toExt_iff, mem_closedBall_zero_iff, not_le]
      exact hu1
    have hψeq : ψ (cP w) = Vμ u₁ := by
      rw [hψdef, Function.comp_apply, ← hWu, hinjW.leftInvOn_invFunOn hu1]
    have hwB : wB μ (Function.invFun (wAS μ) (mobiusExt 0 1 1 0 (w : ExtPlane))) =
        Nμ ((ψ (cP w) : ℂ) : ExtPlane) := by
      rw [hq1, hvfμ u₁, hψeq]
    have hq2n := hHnot _ hq1n
    exact finite_preimage_data hvfν hviν hNνl (hinvB _) hq2n
      (by rw [hwB, hcN]; exact (coe_finPart_of_ne hne2).symm)
  -- the value of `c`
  have hcw : ∀ w ∈ unitDisc, ∀ (hne : Mμinv (mobiusExt 0 1 1 0 (w : ExtPlane)) ≠ extInf)
      (hne2 : Nνinv (Minv (Nμ ((ψ (cP w) : ℂ) : ExtPlane))) ≠ extInf),
      c w = cQ (χ (cN (ψ (cP w)))) ∧ cN (ψ (cP w)) ∈ Vν '' {u : ℂ | 1 < ‖u‖} ∧
        mobiusExt 0 1 1 0 (Mν ((χ (cN (ψ (cP w))) : ℂ) : ExtPlane)) ≠ extInf := by
    intro w hw hne hne2
    obtain ⟨u₂, hq2, hVu, hu2⟩ := hA2 w hw hne hne2
    have hχeq : χ (cN (ψ (cP w))) = Wν u₂ := by
      rw [hχdef, Function.comp_apply, ← hVu, hinjV.leftInvOn_invFunOn hu2]
    have hq2n : Function.invFun (wB ν) (Minv (wB μ (Function.invFun (wAS μ) (mobiusExt 0 1 1 0 (w : ExtPlane))))) ∉ toExt (closedBall (0 : ℂ) 1) := by
      rw [hq2, coe_mem_toExt_iff, mem_closedBall_zero_iff, not_le]
      exact hu2
    have hAn : wAS ν (Function.invFun (wB ν) (Minv (wB μ (Function.invFun (wAS μ) (mobiusExt 0 1 1 0 (w : ExtPlane)))))) ∉ toExt (closedBall (0 : ℂ) 1) := by
      rw [← wAS_closed_iff hν]
      exact hq2n
    have hMq : Mν ((Wν u₂ : ℂ) : ExtPlane) = wAS ν (u₂ : ExtPlane) := (hwfν u₂).symm
    refine ⟨?_, ⟨u₂, hu2, hVu⟩, ?_⟩
    · rw [hc]
      show finPart (mobiusExt 0 1 1 0 (wAS ν (Function.invFun (wB ν) (Minv (wB μ (Function.invFun (wAS μ) (mobiusExt 0 1 1 0 (w : ExtPlane)))))))) = _
      rw [hq2, hχeq, hcQ]
      show _ = finPart (mobiusExt 0 1 1 0 (Mν ((Wν u₂ : ℂ) : ExtPlane)))
      rw [hMq]
    · rw [hχeq, hMq]
      rw [hq2] at hAn
      obtain ⟨y, hy, -⟩ := sigma_of_not_closed hAn
      rw [hy]
      exact OnePoint.coe_ne_infty y
  -- the exceptional set
  obtain ⟨Ω, hΩ⟩ : ∃ Ω : Set ℂ, Ω = {w | w ∈ unitDisc ∧
      Mμinv (mobiusExt 0 1 1 0 (w : ExtPlane)) ≠ extInf ∧
      Nνinv (Minv (Nμ ((ψ (cP w) : ℂ) : ExtPlane))) ≠ extInf} := ⟨_, rfl⟩
  have hdiffΩ : DifferentiableOn ℂ c Ω := by
    have hPd : DifferentiableOn ℂ cP Ω := hPc.1.mono (fun w hw => by rw [hΩ] at hw; exact hw.2.1)
    have h1 : DifferentiableOn ℂ (ψ ∘ cP) Ω :=
      hψ.1.comp hPd (fun w hw => by rw [hΩ] at hw; exact hDmem w hw.1 hw.2.1)
    have h2 : DifferentiableOn ℂ (cN ∘ ψ ∘ cP) Ω :=
      hNc.1.comp h1 (fun w hw => by rw [hΩ] at hw; exact hw.2.2)
    have h3 : DifferentiableOn ℂ (χ ∘ cN ∘ ψ ∘ cP) Ω :=
      hχ.1.comp h2 (fun w hw => by
        rw [hΩ] at hw
        exact (hcw w hw.1 hw.2.1 hw.2.2).2.1)
    have h4 : DifferentiableOn ℂ (cQ ∘ χ ∘ cN ∘ ψ ∘ cP) Ω :=
      hQc.1.comp h3 (fun w hw => by
        rw [hΩ] at hw
        exact (hcw w hw.1 hw.2.1 hw.2.2).2.2)
    refine h4.congr (fun w hw => ?_)
    rw [hΩ] at hw
    exact (hcw w hw.1 hw.2.1 hw.2.2).1
  have hE1 : {w : ℂ | w ∈ unitDisc ∧ Mμinv (mobiusExt 0 1 1 0 (w : ExtPlane)) = extInf}.Subsingleton := by
    intro w1 h1 w2 h2
    have := isMobius_injective hMμinv (h1.2.trans h2.2.symm)
    exact OnePoint.coe_injective (hσi this)
  have hE2 : {w : ℂ | w ∈ unitDisc ∧ Mμinv (mobiusExt 0 1 1 0 (w : ExtPlane)) ≠ extInf ∧
      Nνinv (Minv (Nμ ((ψ (cP w) : ℂ) : ExtPlane))) = extInf}.Subsingleton := by
    intro w1 h1 w2 h2
    have h3 : (fun p => Nνinv (Minv (Nμ p))) ((ψ (cP w1) : ℂ) : ExtPlane) =
        (fun p => Nνinv (Minv (Nμ p))) ((ψ (cP w2) : ℂ) : ExtPlane) := h1.2.2.trans h2.2.2.symm
    have h4 := OnePoint.coe_injective (isMobius_injective hN' h3)
    have h5 := hψ.2.1 (hDmem w1 h1.1 h1.2.1) (hDmem w2 h2.1 h2.2.1) h4
    exact hPc.2.1 h1.2.1 h2.2.1 h5
  have hEfin : (unitDisc \ Ω).Finite := by
    refine (hE1.finite.union hE2.finite).subset ?_
    intro w hw
    by_cases ha : Mμinv (mobiusExt 0 1 1 0 (w : ExtPlane)) = extInf
    · exact Or.inl ⟨hw.1, ha⟩
    · refine Or.inr ⟨hw.1, ha, ?_⟩
      by_contra hb
      apply hw.2
      rw [hΩ]
      exact ⟨hw.1, ha, hb⟩
  have hcont : ContinuousOn c unitDisc := by
    have hσc : Continuous (mobiusExt 0 1 1 0) := continuous_mobiusExt (by norm_num)
    have hcoe : ∀ w ∈ unitDisc, ((c w : ℂ) : ExtPlane) = mobiusExt 0 1 1 0 (wAS ν
        (Function.invFun (wB ν) (Minv (wB μ (Function.invFun (wAS μ) (mobiusExt 0 1 1 0 (w : ExtPlane))))))) := by
      intro w hw
      have hn : wAS ν (Function.invFun (wB ν) (Minv (wB μ (Function.invFun (wAS μ) (mobiusExt 0 1 1 0 (w : ExtPlane)))))) ∉ toExt (closedBall (0 : ℂ) 1) := by
        rw [← wAS_closed_iff hν]
        refine hHnot _ ?_
        rw [wAS_closed_iff hμ, hinvA]
        exact sigma_not_closed hw
      obtain ⟨y, hy, -⟩ := sigma_of_not_closed hn
      rw [hc]
      show ((finPart (mobiusExt 0 1 1 0 (wAS ν (Function.invFun (wB ν) (Minv (wB μ (Function.invFun (wAS μ) (mobiusExt 0 1 1 0 (w : ExtPlane)))))))) : ℂ) : ExtPlane) = _
      rw [hy]
      rfl
    have hct : Continuous (fun p : ExtPlane => mobiusExt 0 1 1 0 (wAS ν (Function.invFun (wB ν)
        (Minv (wB μ (Function.invFun (wAS μ) (mobiusExt 0 1 1 0 p))))))) :=
      hσc.comp ((wAS_continuous hν).comp ((wB_invFun_continuous hν).comp
        (hMc.comp ((wB_continuous hμ).comp ((wAS_invFun_continuous hμ).comp hσc)))))
    rw [OnePoint.isOpenEmbedding_coe.isEmbedding.isInducing.continuousOn_iff]
    refine (hct.comp OnePoint.continuous_coe).continuousOn.congr ?_
    intro w hw
    exact hcoe w hw
  refine differentiableOn_of_finite_exceptional (show IsOpen unitDisc from isOpen_ball) hEfin hcont ?_
  refine hdiffΩ.mono ?_
  intro w hw
  by_contra h
  exact hw.2 ⟨hw.1, h⟩


theorem wAS_eq_of_wB_eq_mob {μ ν : LinfStar} (hμ : μ ∈ LinfStarBall) (hν : ν ∈ LinfStarBall)
    {M Minv : ExtPlane → ExtPlane} (hM : IsMobius M) (hMinv : IsMobius Minv)
    (hMl : ∀ p, Minv (M p) = p) (hMr : ∀ p, M (Minv p) = p)
    (hBeq : ∀ p ∈ toExt (closedBall (0 : ℂ) 1), wB μ p = M (wB ν p)) :
    ∀ z : ℂ, ‖z‖ = 1 → wAS μ (z : ExtPlane) = wAS ν (z : ExtPlane) := by
  obtain ⟨hHid, hHnot⟩ := wB_glue_props_mob hν hM hMinv hMl hMr hBeq
  have hdiff := wAS_c_diffOn_mob hμ hν hM hMinv hMl hMr hBeq
  obtain ⟨Mμ, hMμ, Wμ, hWμ, hwfμ, hwiμ, hm1, hmI, hm2⟩ := wA_spec hμ
  obtain ⟨Csph, hCsph⟩ : ∃ Csph : ExtPlane → ExtPlane, Csph = fun p => wAS ν
      (Function.invFun (wB ν) (Minv (wB μ (Function.invFun (wAS μ) p)))) := ⟨_, rfl⟩
  have hinvA : ∀ q, wAS μ (Function.invFun (wAS μ) q) = q := fun q =>
    Function.invFun_eq ((wAS_bijective μ).2 q)
  have hinvAl : ∀ q, Function.invFun (wAS μ) (wAS μ q) = q := fun q =>
    Function.leftInverse_invFun (wAS_bijective μ).1 q
  have hinvB : ∀ q, wB ν (Function.invFun (wB ν) q) = q := fun q =>
    Function.invFun_eq ((wB_bijective ν).2 q)
  have hMinj : Function.Injective Minv := isMobius_injective hMinv
  have hMc : Continuous Minv := by
    obtain ⟨a, b, c, d, hdet, rfl⟩ := hMinv
    exact continuous_mobiusExt hdet
  have hCnot : ∀ p ∉ toExt (closedBall (0 : ℂ) 1), Csph p ∉ toExt (closedBall (0 : ℂ) 1) := by
    intro p hp
    rw [hCsph]
    show wAS ν _ ∉ _
    rw [← wAS_closed_iff hν]
    refine hHnot _ ?_
    rw [wAS_closed_iff hμ, hinvA]
    exact hp
  have hCinj : Function.Injective Csph := by
    intro p q hpq
    rw [hCsph] at hpq
    have h1 := (wAS_bijective ν).1 hpq
    have h2 : Minv (wB μ (Function.invFun (wAS μ) p)) = Minv (wB μ (Function.invFun (wAS μ) q)) := by
      have := congrArg (wB ν) h1
      simp only [hinvB] at this
      exact this
    have h3 := (wB_bijective μ).1 (hMinj h2)
    have := congrArg (wAS μ) h3
    simpa only [hinvA] using this
  have hCsurj : ∀ p' ∉ toExt (closedBall (0 : ℂ) 1), ∃ p ∉ toExt (closedBall (0 : ℂ) 1),
      Csph p = p' := by
    intro p' hp'
    obtain ⟨q2, hq2⟩ := (wAS_bijective ν).2 p'
    have hq2n : q2 ∉ toExt (closedBall (0 : ℂ) 1) := by
      rw [wAS_closed_iff hν, hq2]
      exact hp'
    obtain ⟨q1, hq1⟩ := (wB_bijective μ).2 (M (wB ν q2))
    have hq1n : q1 ∉ toExt (closedBall (0 : ℂ) 1) := by
      intro h
      have e := hBeq q1 h
      rw [hq1] at e
      exact hq2n (((wB_bijective ν).1 (isMobius_injective hM e)) ▸ h)
    refine ⟨wAS μ q1, ?_, ?_⟩
    · rw [← wAS_closed_iff hμ]
      exact hq1n
    · rw [hCsph]
      show wAS ν (Function.invFun (wB ν) (Minv (wB μ (Function.invFun (wAS μ) (wAS μ q1))))) = p'
      rw [hinvAl, hq1, hMl, Function.leftInverse_invFun (wB_bijective ν).1 q2, hq2]
  have hCcont : Continuous Csph := by
    rw [hCsph]
    exact (wAS_continuous hν).comp ((wB_invFun_continuous hν).comp
      (hMc.comp ((wB_continuous hμ).comp (wAS_invFun_continuous hμ))))
  have hCcl : ∀ ξ ∈ toExt (closedBall (0 : ℂ) 1), Csph (wAS μ ξ) = wAS ν ξ := by
    intro ξ hξ
    rw [hCsph]
    show wAS ν (Function.invFun (wB ν) (Minv (wB μ (Function.invFun (wAS μ) (wAS μ ξ))))) = _
    rw [hinvAl, hBeq ξ hξ, hMl, Function.leftInverse_invFun (wB_bijective ν).1 ξ]
  obtain ⟨Mν, hMν, Wν, hWν, hwfν, hwiν, hn1, hnI, hn2⟩ := wA_spec hν
  have hσc : Continuous (mobiusExt 0 1 1 0) := continuous_mobiusExt (by norm_num)
  have hσi : Function.Injective (mobiusExt 0 1 1 0) := fun a b h => by
    rw [← sigma_invol a, ← sigma_invol b, h]
  obtain ⟨c, hcdef⟩ : ∃ c : ℂ → ℂ, c = fun w : ℂ =>
      finPart (mobiusExt 0 1 1 0 (Csph (mobiusExt 0 1 1 0 (w : ExtPlane)))) := ⟨_, rfl⟩
  have hdiff' : DifferentiableOn ℂ c unitDisc := by
    rw [hcdef, hCsph]
    exact hdiff
  have hc1 : ∀ w ∈ unitDisc, mobiusExt 0 1 1 0 (Csph (mobiusExt 0 1 1 0 (w : ExtPlane))) =
      ((c w : ℂ) : ExtPlane) ∧ c w ∈ unitDisc := by
    intro w hw
    obtain ⟨y, hy, hyD⟩ := sigma_of_not_closed (hCnot _ (sigma_not_closed hw))
    have hcy : c w = y := by
      rw [hcdef]
      show finPart (mobiusExt 0 1 1 0 (Csph _)) = y
      rw [hy]
      rfl
    exact ⟨by rw [hcy]; exact hy, hcy ▸ hyD⟩
  have hcinj : InjOn c unitDisc := by
    intro w1 hw1 w2 hw2 h
    have e1 := (hc1 w1 hw1).1
    have e2 := (hc1 w2 hw2).1
    rw [h] at e1
    have := hCinj (hσi (e1.trans e2.symm))
    exact OnePoint.coe_injective (hσi this)
  have hcsurj : c '' unitDisc = unitDisc := by
    apply Subset.antisymm
    · rintro _ ⟨w, hw, rfl⟩
      exact (hc1 w hw).2
    · intro y hy
      obtain ⟨p, hpn, hp⟩ := hCsurj _ (sigma_not_closed hy)
      obtain ⟨w, hwp, hwD⟩ := sigma_of_not_closed hpn
      refine ⟨w, hwD, ?_⟩
      have e := (hc1 w hwD).1
      rw [← hwp, sigma_invol, hp, sigma_invol] at e
      exact (OnePoint.coe_injective e).symm
  obtain ⟨A, B, C, D, hdet, heq⟩ :=
    exists_mobius_of_isConformalOnto_unitDisc ⟨hdiff', hcinj, hcsurj⟩
  have hmc : Continuous (mobiusExt A B C D) := continuous_mobiusExt hdet
  have hZ : {x : ℂ | C * x + D = 0}.Subsingleton := by
    intro x hx y hy
    have hx' : C * x + D = 0 := hx
    have hy' : C * y + D = 0 := hy
    by_cases hC : C = 0
    · exfalso
      rw [hC, zero_mul, zero_add] at hx'
      apply hdet
      rw [hC, hx']
      ring
    · have : C * (x - y) = 0 := by linear_combination hx' - hy'
      exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_left hC)
  have hZd : Dense ({x : ℂ | C * x + D = 0}ᶜ) := Set.Countable.dense_compl ℂ hZ.finite.countable
  have hagree : EqOn (fun p => mobiusExt 0 1 1 0 (Csph (mobiusExt 0 1 1 0 p))) (mobiusExt A B C D)
      (((↑) : ℂ → ExtPlane) '' (ball (0 : ℂ) 1 ∩ {x : ℂ | C * x + D = 0}ᶜ)) := by
    rintro _ ⟨w, ⟨hw, hwZ⟩, rfl⟩
    have hwD : w ∈ unitDisc := hw
    show mobiusExt 0 1 1 0 (Csph (mobiusExt 0 1 1 0 (w : ExtPlane))) = _
    rw [(hc1 w hwD).1, mobiusExt_coe hwZ, heq hwD]
  have hcl : EqOn (fun p => mobiusExt 0 1 1 0 (Csph (mobiusExt 0 1 1 0 p))) (mobiusExt A B C D)
      (closure (((↑) : ℂ → ExtPlane) '' (ball (0 : ℂ) 1 ∩ {x : ℂ | C * x + D = 0}ᶜ))) :=
    EqOn.closure hagree (hσc.comp (hCcont.comp hσc)) hmc
  have hcirc : ∀ ζ : ℂ, ‖ζ‖ = 1 → mobiusExt 0 1 1 0 (Csph (mobiusExt 0 1 1 0 (ζ : ExtPlane))) =
      mobiusExt A B C D (ζ : ExtPlane) := by
    intro ζ hζ
    apply hcl
    have h1 : ζ ∈ closure (ball (0 : ℂ) 1 ∩ {x : ℂ | C * x + D = 0}ᶜ) := by
      have hsub : ball (0 : ℂ) 1 ⊆ closure (ball (0 : ℂ) 1 ∩ {x : ℂ | C * x + D = 0}ᶜ) :=
        hZd.open_subset_closure_inter isOpen_ball
      have : closure (ball (0 : ℂ) 1) ⊆ closure (ball (0 : ℂ) 1 ∩ {x : ℂ | C * x + D = 0}ᶜ) :=
        closure_minimal hsub isClosed_closure
      apply this
      rw [closure_ball _ one_ne_zero]
      exact mem_closedBall_zero_iff.2 hζ.le
    exact (image_closure_subset_closure_image OnePoint.continuous_coe) ⟨ζ, h1, rfl⟩
  -- the three fixed points
  have hid : ∀ p, mobiusExt 1 0 0 1 p = p := by
    intro p
    induction p using OnePoint.rec with
    | infty => exact mobiusExt_infty_of_eq rfl
    | coe z =>
      rw [mobiusExt_coe (by simp)]
      congr 1
      simp [mobiusFn]
  have hfix1 : Csph ((-1 : ℂ) : ExtPlane) = ((-1 : ℂ) : ExtPlane) := by
    have := hCcl ((-1 : ℂ) : ExtPlane) (by
      rw [coe_mem_toExt_iff, mem_closedBall_zero_iff]; simp)
    rw [hm1, hn1] at this
    exact this
  have hfixI : Csph ((-I : ℂ) : ExtPlane) = ((-I : ℂ) : ExtPlane) := by
    have := hCcl ((-I : ℂ) : ExtPlane) (by
      rw [coe_mem_toExt_iff, mem_closedBall_zero_iff]; simp)
    rw [hmI, hnI] at this
    exact this
  have hfix2 : Csph ((1 : ℂ) : ExtPlane) = ((1 : ℂ) : ExtPlane) := by
    have := hCcl ((1 : ℂ) : ExtPlane) (by
      rw [coe_mem_toExt_iff, mem_closedBall_zero_iff]; simp)
    rw [hm2, hn2] at this
    exact this
  have hI0 : (-I : ℂ) ≠ 0 := neg_ne_zero.2 Complex.I_ne_zero
  have hMid : mobiusExt A B C D = mobiusExt 1 0 0 1 := by
    refine mobius_eq_of_three_points (p₁ := -1) (p₂ := I) (p₃ := 1) ⟨A, B, C, D, hdet, rfl⟩
      ⟨1, 0, 0, 1, by norm_num, rfl⟩ ?_ ?_ ?_ ?_ ?_ ?_
    · intro h
      have := congrArg Complex.re h
      norm_num at this
    · norm_num
    · intro h
      have := congrArg Complex.re h
      norm_num at this
    · rw [← hcirc (-1) (by simp), sigma_coe (by norm_num), hid]
      have : ((-1 : ℂ)⁻¹) = -1 := by norm_num
      rw [this, hfix1, sigma_coe (by norm_num), this]
    · rw [← hcirc I (by simp), sigma_coe Complex.I_ne_zero, hid]
      have : (I : ℂ)⁻¹ = -I := by simp
      rw [this, hfixI, sigma_coe hI0]
      simp
    · rw [← hcirc 1 (by simp), sigma_coe one_ne_zero, hid]
      rw [inv_one, hfix2, sigma_coe one_ne_zero, inv_one]
  have hCid : ∀ ζ : ℂ, ‖ζ‖ = 1 → Csph (ζ : ExtPlane) = (ζ : ExtPlane) := by
    intro ζ hζ
    have hζ0 : ζ ≠ 0 := norm_ne_zero_iff.1 (by rw [hζ]; exact one_ne_zero)
    have h1 := hcirc ζ⁻¹ (by rw [norm_inv, hζ]; simp)
    rw [hMid, hid, sigma_coe (inv_ne_zero hζ0), inv_inv] at h1
    have h2 := congrArg (mobiusExt 0 1 1 0) h1
    rw [sigma_invol, sigma_coe (inv_ne_zero hζ0), inv_inv] at h2
    exact h2
  intro z hz
  obtain ⟨u, hu, hu'⟩ := wAS_maps_circle hμ hz
  have hzCl : (z : ExtPlane) ∈ toExt (closedBall (0 : ℂ) 1) := by
    rw [coe_mem_toExt_iff, mem_closedBall_zero_iff]
    exact hz.le
  have h3 := hCcl _ hzCl
  rw [hu', hCid u hu] at h3
  rw [hu', h3]


theorem bm_locUniv {ρ : LinfStar} (hρ : ρ ∈ LinfStarBall) : IsLocUnivMero (fB ρ) unitDisc := by
  obtain ⟨hd, hi⟩ := fB_holomorphic_injective hρ
  have hUo : IsOpen unitDisc := isOpen_ball
  have han : ∀ z ∈ unitDisc, AnalyticAt ℂ (fB ρ) z := fun z hz => hd.analyticAt (hUo.mem_nhds hz)
  refine ⟨fun z hz => (han z hz).meromorphicAt, fun z hz => Or.inl ⟨han z hz, ?_⟩⟩
  exact deriv_ne_zero_of_injOn hUo hd hi hz

theorem bers_mobius_of_eq {μ ν : LinfStar} (hμ : μ ∈ LinfStarBall) (hν : ν ∈ LinfStarBall)
    (h : bersPhi μ = bersPhi ν) :
    ∃ M : ExtPlane → ExtPlane, IsMobius M ∧ ∀ p ∈ toExt (closedBall (0 : ℂ) 1), wB μ p = M (wB ν p) := by
  obtain ⟨hdμ, hiμ⟩ := fB_holomorphic_injective hμ
  obtain ⟨hdν, hiν⟩ := fB_holomorphic_injective hν
  have hUo : IsOpen unitDisc := isOpen_ball
  have hSch : ∀ z ∈ unitDisc, schwarzian (fB μ) z = schwarzian (fB ν) z := by
    intro z hz
    rw [schwarzian_of_analyticAt (hdμ.analyticAt (hUo.mem_nhds hz)),
      schwarzian_of_analyticAt (hdν.analyticAt (hUo.mem_nhds hz)),
      ← (bersPhi_spec hμ).1 z hz, ← (bersPhi_spec hν).1 z hz, h]
  obtain ⟨a, b, c, d, hdet, hfg⟩ := thm19_1_unique hUo
    ((convex_ball (0 : ℂ) 1).isConnected ⟨0, mem_ball_self one_pos⟩) (bm_locUniv hμ) (bm_locUniv hν) hSch
  refine ⟨mobiusExt a b c d, ⟨a, b, c, d, hdet, rfl⟩, ?_⟩
  have hmc : Continuous (mobiusExt a b c d) := continuous_mobiusExt hdet
  have hZ : {z : ℂ | z ∈ unitDisc ∧ c * fB ν z + d = 0}.Subsingleton := by
    intro x hx y hy
    have : fB ν x = fB ν y := by
      by_cases hc : c = 0
      · exfalso
        apply hdet
        have := hx.2
        rw [hc, zero_mul, zero_add] at this
        rw [hc, this]
        ring
      · have h1 : c * (fB ν x - fB ν y) = 0 := by linear_combination hx.2 - hy.2
        exact sub_eq_zero.1 ((mul_eq_zero.1 h1).resolve_left hc)
    exact hiν hx.1 hy.1 this
  have hZd : Dense ({z : ℂ | z ∈ unitDisc ∧ c * fB ν z + d = 0}ᶜ) :=
    Set.Countable.dense_compl ℂ hZ.finite.countable
  have hagree : EqOn (wB μ) (fun p => mobiusExt a b c d (wB ν p))
      (((↑) : ℂ → ExtPlane) '' (ball (0 : ℂ) 1 ∩ {z : ℂ | z ∈ unitDisc ∧ c * fB ν z + d = 0}ᶜ)) := by
    rintro _ ⟨z, ⟨hz, hzZ⟩, rfl⟩
    have hzD : z ∈ unitDisc := hz
    have hden : c * fB ν z + d ≠ 0 := fun hh => hzZ ⟨hzD, hh⟩
    have e1 : wB μ (z : ExtPlane) = ((fB μ z : ℂ) : ExtPlane) := wB_disc_eq_fB hμ hzD
    have e2 : wB ν (z : ExtPlane) = ((fB ν z : ℂ) : ExtPlane) := wB_disc_eq_fB hν hzD
    show wB μ (z : ExtPlane) = mobiusExt a b c d (wB ν (z : ExtPlane))
    rw [e1, e2, mobiusExt_coe hden]
    congr 1
    exact hfg z hzD (hdμ.analyticAt (hUo.mem_nhds hzD)) (hdν.analyticAt (hUo.mem_nhds hzD)) hden
  have hcl : EqOn (wB μ) (fun p => mobiusExt a b c d (wB ν p))
      (closure (((↑) : ℂ → ExtPlane) '' (ball (0 : ℂ) 1 ∩ {z : ℂ | z ∈ unitDisc ∧ c * fB ν z + d = 0}ᶜ))) :=
    EqOn.closure hagree (wB_continuous hμ) (hmc.comp (wB_continuous hν))
  intro p hp
  apply hcl
  rcases hp with ⟨z, hz, rfl⟩
  have h1 : z ∈ closure (ball (0 : ℂ) 1 ∩ {z : ℂ | z ∈ unitDisc ∧ c * fB ν z + d = 0}ᶜ) := by
    have hsub : ball (0 : ℂ) 1 ⊆ closure (ball (0 : ℂ) 1 ∩ {z : ℂ | z ∈ unitDisc ∧ c * fB ν z + d = 0}ᶜ) :=
      hZd.open_subset_closure_inter isOpen_ball
    have : closure (ball (0 : ℂ) 1) ⊆
        closure (ball (0 : ℂ) 1 ∩ {z : ℂ | z ∈ unitDisc ∧ c * fB ν z + d = 0}ᶜ) :=
      closure_minimal hsub isClosed_closure
    apply this
    rw [closure_ball _ one_ne_zero]
    exact hz
  exact (image_closure_subset_closure_image OnePoint.continuous_coe) ⟨z, h1, rfl⟩

theorem bers_injective : Function.Injective bers := by
  intro p q hpq
  have hμ := (Quotient.out p : LinfStarBall).property
  have hν := (Quotient.out q : LinfStarBall).property
  obtain ⟨M, hM, hBeq⟩ := bers_mobius_of_eq hμ hν hpq
  obtain ⟨Minv, hMinv, hMl, hMr⟩ := isMobius_inverse hM
  have hcirc := wAS_eq_of_wB_eq_mob hμ hν hM hMinv hMl hMr hBeq
  have h3 : teichSetoid.r (Quotient.out p : LinfStarBall) (Quotient.out q : LinfStarBall) := by
    intro z hz
    exact congrArg finPart (hcirc z hz)
  rw [← Quotient.out_eq p, ← Quotient.out_eq q]
  exact Quotient.sound h3

end TakhtajanTeo

