import TakhtajanTeo.Ch2.S1_BP78Completed
import TakhtajanTeo.Ch2.S1_BP16Forward
import TakhtajanTeo.Ch2.S1_BP78Loewner

/-!
# Theorem 1.6 (Becker–Pommerenke): TFAE assembly

Uses `Ch2/S1_BP16Forward` (`bpa_i_imp_ii`, (i) ⇒ (ii)), `Ch2/S1_BP78Completed` (`ab16_ii_imp_iii`,
`ab16_iii_imp_ii`) and `Ch2/S1_BP78Loewner` (`ab16_iii_imp_i`, (iii) ⇒ (i)). Relocation: `thm_1_6 := bpa_thm_1_6`.
-/

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal NNReal ComplexConjugate Classical Real

noncomputable section

namespace TakhtajanTeo

open LiZhongQC

namespace Ch2

/-- **Theorem 1.6** (Becker–Pommerenke [BP78]) (TT:3622–3638), byte-identical copy of `thm_1_6`. -/
theorem bpa_thm_1_6 {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f unitDisc) (hinj : InjOn f unitDisc)
    (hJ : IsJordanDomain (f '' unitDisc)) (hb : Bornology.IsBounded (f '' unitDisc)) :
    List.TFAE
      [∃ R > 1, ∃ F : ℂ → ℂ, IsQuasiconformal F (ball 0 R) ∧ EqOn F f unitDisc ∧
          Tendsto (complexDilatation F) (comap (fun z : ℂ => ‖z‖) (𝓝[>] 1)) (𝓝 0),
        Tendsto (fun z => ((1 - ‖z‖ ^ 2) ^ 2 : ℂ) * schwarzianHol f z) (comap (fun z : ℂ => ‖z‖) (𝓝[<] 1)) (𝓝 0),
        Tendsto (fun z => ((1 - ‖z‖ ^ 2) : ℂ) * preSchwarzian f z) (comap (fun z : ℂ => ‖z‖) (𝓝[<] 1)) (𝓝 0)] := by
  have hd : ∀ z ∈ unitDisc, deriv f z ≠ 0 := fun z hz => deriv_ne_zero_of_injOn isOpen_ball hf hinj hz
  obtain ⟨M, hM⟩ := hb.exists_norm_le
  have hM' : ∀ z ∈ unitDisc, ‖f z‖ ≤ M := fun z hz => hM _ (mem_image_of_mem f hz)
  tfae_have 1 → 2 := bpa_i_imp_ii hf hinj
  tfae_have 2 → 3 := ab16_ii_imp_iii hf hd hM'
  tfae_have 3 → 2 := ab16_iii_imp_ii hf hinj
  tfae_have 3 → 1 := ab16_iii_imp_i hf hinj hJ hb
  tfae_finish

/-- **Theorem 1.6** (Becker–Pommerenke [BP78]) (TT:3622–3638). Let `f` be univalent on `𝔻` with `f(𝔻)` a Jordan
domain. The following are equivalent.
- (i) `f` has a q.c. extension `F` to some disk `{|z| < R}`, `R > 1`, whose complex dilatation satisfies
  `μ(z) → 0` as `|z| → 1⁺`.
- (ii) `(1 - |z|²)² 𝒮(f)(z) → 0` as `|z| → 1⁻`.
- (iii) `(1 - |z|²) 𝒜(f)(z) → 0` as `|z| → 1⁻`. -/
theorem thm_1_6 {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f unitDisc) (hinj : InjOn f unitDisc)
    (hJ : IsJordanDomain (f '' unitDisc)) (hb : Bornology.IsBounded (f '' unitDisc)) :
    List.TFAE
      [∃ R > 1, ∃ F : ℂ → ℂ, IsQuasiconformal F (ball 0 R) ∧ EqOn F f unitDisc ∧
          Tendsto (complexDilatation F) (comap (fun z : ℂ => ‖z‖) (𝓝[>] 1)) (𝓝 0),
        Tendsto (fun z => ((1 - ‖z‖ ^ 2) ^ 2 : ℂ) * schwarzianHol f z) (comap (fun z : ℂ => ‖z‖) (𝓝[<] 1)) (𝓝 0),
        Tendsto (fun z => ((1 - ‖z‖ ^ 2) : ℂ) * preSchwarzian f z) (comap (fun z : ℂ => ‖z‖) (𝓝[<] 1)) (𝓝 0)] :=
  bpa_thm_1_6 hf hinj hJ hb

end Ch2

end TakhtajanTeo
