import TakhtajanTeo.Ch1.GroupL2Representatives
import TakhtajanTeo.Ch1.CuiBound
import TakhtajanTeo.Ch1.HilbertManifoldCompleted
import TakhtajanTeo.Ch1.GroupChainCompleted
import TakhtajanTeo.Ch1.GroupCov
import TakhtajanTeo.Ch1.GroupBaseCompleted
import TakhtajanTeo.Ch1.GroupTopology
import TakhtajanTeo.Ch1.S3_TopologicalGroup
import TakhtajanTeo.Ch1.GroupPhase

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal NNReal ComplexConjugate Classical Real
noncomputable section
namespace TakhtajanTeo
open LiZhongQC

/-! # Lemma 3.5 and Corollary 3.6 (prefix `gtr_`)

Left translations and the adjoint map in Hilbert charts. The core `L²` estimate `‖μ * ν - μ‖₂ → 0` uses density of
`C_c(𝔻*)` in `L²(𝔻*, ρ)`, the transfer bound of `grp_density_fwd`, and the phase lemmas of `Ch1/GroupPhase` (下属2). -/

/-- Truncation to a closed annulus `1 + 1/(n+1) ≤ |z| ≤ n + 2` is close in `L²(𝔻*, ρ)`. -/
theorem gtr_trunc {f : ℂ → ℂ} (hf2 : normL2 unitDiscExterior f < ⊤) {ε : ℝ} (hε : 0 < ε) :
    ∃ n : ℕ, normL2 unitDiscExterior (fun z => (({z : ℂ | 1 + 1 / ((n : ℝ) + 1) ≤ ‖z‖} ∩
      {z : ℂ | ‖z‖ ≤ (n : ℝ) + 2})ᶜ).indicator f z) < ENNReal.ofReal ε := by
  let F : ℂ → ℝ≥0∞ := fun z => (‖f z‖₊ : ℝ≥0∞) ^ 2 * ENNReal.ofReal (rho z)
  let m := (volume.restrict unitDiscExterior).withDensity F
  let S : ℕ → Set ℂ := fun n => ({z : ℂ | 1 + 1 / ((n : ℝ) + 1) ≤ ‖z‖} ∩ {z : ℂ | ‖z‖ ≤ (n : ℝ) + 2})ᶜ
  have hSm : ∀ n, MeasurableSet (S n) := fun n =>
    ((measurableSet_le measurable_const measurable_norm).inter
      (measurableSet_le measurable_norm measurable_const)).compl
  have hfin : ∫⁻ z in unitDiscExterior, F z < ⊤ :=
    (ENNReal.rpow_lt_top_iff_of_pos (by norm_num : (0 : ℝ) < 1 / 2)).mp hf2
  have hanti : Antitone S := by
    intro i j hij z hz hA
    apply hz
    have hij' : (i : ℝ) ≤ j := by exact_mod_cast hij
    obtain ⟨h1, h2⟩ := hA
    change 1 + 1 / ((i : ℝ) + 1) ≤ ‖z‖ at h1
    change ‖z‖ ≤ (i : ℝ) + 2 at h2
    refine ⟨le_trans ?_ h1, le_trans h2 (by linarith)⟩
    have : 1 / ((j : ℝ) + 1) ≤ 1 / ((i : ℝ) + 1) :=
      one_div_le_one_div_of_le (by positivity) (by linarith)
    linarith
  have hmS : ∀ n, m (S n) = ∫⁻ z in unitDiscExterior, (S n).indicator F z := by
    intro n
    rw [withDensity_apply _ (hSm n), lintegral_indicator (hSm n)]
  have hmuniv : m univ < ⊤ := by
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
    exact hfin
  have hlim := tendsto_measure_iInter_atTop (μ := m) (fun n => (hSm n).nullMeasurableSet) hanti
    ⟨0, ((measure_mono (subset_univ _)).trans_lt hmuniv).ne⟩
  have hI : m (⋂ n, S n) = 0 := by
    have hsub : (⋂ n, S n) ⊆ {z : ℂ | ‖z‖ ≤ 1} := by
      intro z hz
      by_contra h1
      have h1' : 1 < ‖z‖ := lt_of_not_ge h1
      obtain ⟨k, hk⟩ := exists_nat_gt (max (1 / (‖z‖ - 1)) ‖z‖)
      have hk1 : 1 / (‖z‖ - 1) < k := lt_of_le_of_lt (le_max_left _ _) hk
      have hk2 : ‖z‖ < k := lt_of_le_of_lt (le_max_right _ _) hk
      apply mem_iInter.mp hz k
      refine ⟨?_, ?_⟩
      · show 1 + 1 / ((k : ℝ) + 1) ≤ ‖z‖
        have hpos : 0 < ‖z‖ - 1 := by linarith
        have : 1 / ((k : ℝ) + 1) ≤ ‖z‖ - 1 := by
          rw [div_le_iff₀ (by positivity)]
          rw [div_lt_iff₀ hpos] at hk1
          nlinarith
        linarith
      · show ‖z‖ ≤ (k : ℝ) + 2
        linarith
    have hB : MeasurableSet {z : ℂ | ‖z‖ ≤ 1} := measurableSet_le measurable_norm measurable_const
    refine le_antisymm ((measure_mono hsub).trans (le_of_eq ?_)) bot_le
    rw [withDensity_apply _ hB, Measure.restrict_restrict hB]
    have he : {z : ℂ | ‖z‖ ≤ 1} ∩ unitDiscExterior = ∅ := by
      ext z
      simp only [mem_inter_iff, mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and, unitDiscExterior]
      intro h1 h2
      linarith
    rw [he, Measure.restrict_empty, lintegral_zero_measure]
  rw [hI] at hlim
  have hpos : (0 : ℝ≥0∞) < ENNReal.ofReal (ε ^ 2) := ENNReal.ofReal_pos.2 (by positivity)
  obtain ⟨n, hn⟩ := (hlim.eventually (gt_mem_nhds hpos)).exists
  refine ⟨n, ?_⟩
  have hint : ∫⁻ z in unitDiscExterior, (‖(S n).indicator f z‖₊ : ℝ≥0∞) ^ 2 * ENNReal.ofReal (rho z) =
      ∫⁻ z in unitDiscExterior, (S n).indicator F z := by
    congr 1
    funext z
    by_cases hz : z ∈ S n
    · simp only [indicator_of_mem hz, F]
    · simp only [indicator_of_notMem hz, nnnorm_zero, ENNReal.coe_zero, ne_eq, OfNat.ofNat_ne_zero,
        not_false_eq_true, zero_pow, zero_mul]
  show normL2 unitDiscExterior (fun z => (S n).indicator f z) < ENNReal.ofReal ε
  unfold normL2
  rw [hint, ← hmS n]
  calc m (S n) ^ (1 / 2 : ℝ) < ENNReal.ofReal (ε ^ 2) ^ (1 / 2 : ℝ) := ENNReal.rpow_lt_rpow hn (by norm_num)
    _ = ENNReal.ofReal ε := by
        rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num), ← Real.sqrt_eq_rpow,
          Real.sqrt_sq hε.le]

/-- Density of continuous functions with compact support in `𝔻*` in `L²(𝔻*, ρ d²z)`. -/
theorem gtr_dense_cc {f : ℂ → ℂ} (hf : AEStronglyMeasurable f (volume.restrict unitDiscExterior))
    (hf2 : normL2 unitDiscExterior f < ⊤) {ε : ℝ} (hε : 0 < ε) :
    ∃ g : ℂ → ℂ, Continuous g ∧ (∃ r R : ℝ, 1 < r ∧ ∀ z, g z ≠ 0 → r ≤ ‖z‖ ∧ ‖z‖ ≤ R) ∧
      normL2 unitDiscExterior (fun z => f z - g z) < ENNReal.ofReal ε := by
  obtain ⟨n, hn⟩ := gtr_trunc hf2 (half_pos hε)
  obtain ⟨a, ha⟩ : ∃ a : ℝ, a = 1 + 1 / ((n : ℝ) + 1) := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b : ℝ, b = (n : ℝ) + 2 := ⟨_, rfl⟩
  obtain ⟨a', ha'⟩ : ∃ a' : ℝ, a' = 1 + 1 / (2 * ((n : ℝ) + 1)) := ⟨_, rfl⟩
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have ha1 : 1 < a' := by
    have : 0 < 1 / (2 * ((n : ℝ) + 1)) := by positivity
    rw [ha']
    linarith
  have haa : a' < a := by
    rw [ha, ha']
    have h1 : 1 / (2 * ((n : ℝ) + 1)) < 1 / ((n : ℝ) + 1) :=
      one_div_lt_one_div_of_lt (by positivity) (by linarith)
    linarith
  let A : Set ℂ := {z : ℂ | a ≤ ‖z‖} ∩ {z : ℂ | ‖z‖ ≤ b}
  let U : Set ℂ := {z : ℂ | a' < ‖z‖} ∩ {z : ℂ | ‖z‖ < b + 1}
  have hAm : MeasurableSet A :=
    (measurableSet_le measurable_const measurable_norm).inter (measurableSet_le measurable_norm measurable_const)
  have hUo : IsOpen U :=
    (isOpen_lt continuous_const continuous_norm).inter (isOpen_lt continuous_norm continuous_const)
  have hUm : MeasurableSet U := hUo.measurableSet
  have hAU : A ⊆ U := fun z hz => ⟨lt_of_lt_of_le haa hz.1, lt_of_le_of_lt hz.2 (lt_add_one b)⟩
  have hUE : U ⊆ unitDiscExterior := fun z hz => by
    show 1 < ‖z‖
    exact lt_trans ha1 hz.1
  have hAc : IsCompact A :=
    (isCompact_closedBall (0 : ℂ) b).of_isClosed_subset
      ((isClosed_le continuous_const continuous_norm).inter (isClosed_le continuous_norm continuous_const))
      (fun z hz => mem_closedBall_zero_iff.2 hz.2)
  -- the finite measure on `U`
  let M := (volume.restrict U).withDensity (fun z => ENNReal.ofReal (rho z))
  have hρU : ∀ z ∈ U, rho z ≤ 4 / (a' ^ 2 - 1) ^ 2 := by
    intro z hz
    have h0 : a' < ‖z‖ := hz.1
    have h2 : 0 < a' ^ 2 - 1 := by nlinarith
    have h3 : a' ^ 2 - 1 ≤ ‖z‖ ^ 2 - 1 := by nlinarith
    unfold rho
    apply div_le_div_of_nonneg_left (by norm_num) (pow_pos h2 2)
    nlinarith [mul_le_mul h3 h3 h2.le (by linarith)]
  have hMfin : M univ < ⊤ := by
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
    calc ∫⁻ z in U, ENNReal.ofReal (rho z) ≤ ∫⁻ _ in U, ENNReal.ofReal (4 / (a' ^ 2 - 1) ^ 2) :=
          setLIntegral_mono' hUm (fun z hz => ENNReal.ofReal_le_ofReal (hρU z hz))
      _ = ENNReal.ofReal (4 / (a' ^ 2 - 1) ^ 2) * volume U := setLIntegral_const _ _
      _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top
          ((measure_mono (fun z hz => mem_ball_zero_iff.2 hz.2)).trans_lt measure_ball_lt_top)
  have : IsFiniteMeasure M := ⟨hMfin⟩
  -- `f` truncated to `A` lies in `L²(M)`
  have hUle : volume.restrict U ≪ volume.restrict unitDiscExterior :=
    Measure.absolutelyContinuous_of_le (Measure.restrict_mono hUE le_rfl)
  have hacU : M ≪ volume.restrict unitDiscExterior := (withDensity_absolutelyContinuous _ _).trans hUle
  have hfA : AEStronglyMeasurable (A.indicator f) (volume.restrict unitDiscExterior) := hf.indicator hAm
  have hfAU : AEStronglyMeasurable (A.indicator f) (volume.restrict U) := hfA.mono_ac hUle
  have hnormU : normL2 U (A.indicator f) ≤ normL2 unitDiscExterior f := by
    unfold normL2
    apply ENNReal.rpow_le_rpow _ (by norm_num)
    calc ∫⁻ z in U, (‖A.indicator f z‖₊ : ℝ≥0∞) ^ 2 * ENNReal.ofReal (rho z) ≤
          ∫⁻ z in U, (‖f z‖₊ : ℝ≥0∞) ^ 2 * ENNReal.ofReal (rho z) := by
          apply lintegral_mono
          intro z
          dsimp only
          gcongr
          rw [← NNReal.coe_le_coe, coe_nnnorm, coe_nnnorm]
          exact norm_indicator_le_norm_self (s := A) (f := f) (a := z)
      _ ≤ ∫⁻ z in unitDiscExterior, (‖f z‖₊ : ℝ≥0∞) ^ 2 * ENNReal.ofReal (rho z) := lintegral_mono_set hUE
  have hlt : eLpNorm (A.indicator f) 2 M < ⊤ := by
    rw [← grp_normL2_eq U hfAU]
    exact lt_of_le_of_lt hnormU hf2
  have hmem : MemLp (A.indicator f) 2 M := hlt
  have hε4 : ENNReal.ofReal (ε / 4) ≠ 0 := (ENNReal.ofReal_pos.2 (by positivity)).ne'
  obtain ⟨g0, hg0, -⟩ := hmem.exists_boundedContinuous_eLpNorm_sub_le (by norm_num) hε4
  -- the cutoff
  obtain ⟨χ, hχ0, hχ1, hχI⟩ := exists_continuous_zero_one_of_isCompact' hAc hUo.isClosed_compl
    (Set.disjoint_compl_right_iff_subset.mpr hAU)
  let g : ℂ → ℂ := fun z => (χ z : ℂ) * g0 z
  have hgc : Continuous g := (continuous_ofReal.comp χ.continuous).mul g0.continuous
  refine ⟨g, hgc, ⟨a', b + 1, ha1, fun z hz => ?_⟩, ?_⟩
  · have hzU : z ∈ U := by
      by_contra hzU
      apply hz
      show (χ z : ℂ) * g0 z = 0
      rw [hχ0 hzU, Pi.zero_apply, ofReal_zero, zero_mul]
    exact ⟨hzU.1.le, hzU.2.le⟩
  -- splitting `f - g`
  have hsplit : (fun z => f z - g z) = fun z => (A.indicator f z - g z) + Aᶜ.indicator f z := by
    funext z
    by_cases hz : z ∈ A
    · rw [indicator_of_mem hz, indicator_of_notMem (not_not.mpr hz)]
      ring
    · rw [indicator_of_notMem hz, indicator_of_mem hz]
      ring
  rw [hsplit]
  refine lt_of_le_of_lt (gtp_normL2_add_le (hfA.sub hgc.aestronglyMeasurable) (hf.indicator hAm.compl)) ?_
  have h1 : normL2 unitDiscExterior (fun z => A.indicator f z - g z) ≤ ENNReal.ofReal (ε / 4) := by
    refine le_trans ?_ hg0
    rw [← grp_normL2_eq U (hfAU.sub g0.continuous.aestronglyMeasurable)]
    unfold normL2
    apply ENNReal.rpow_le_rpow _ (by norm_num)
    calc ∫⁻ z in unitDiscExterior, (‖A.indicator f z - g z‖₊ : ℝ≥0∞) ^ 2 * ENNReal.ofReal (rho z) ≤
          ∫⁻ z in unitDiscExterior, U.indicator
            (fun z => (‖(A.indicator f - (g0 : ℂ → ℂ)) z‖₊ : ℝ≥0∞) ^ 2 * ENNReal.ofReal (rho z)) z := by
          apply lintegral_mono
          intro z
          by_cases hzU : z ∈ U
          · rw [indicator_of_mem hzU, Pi.sub_apply]
            dsimp only
            gcongr
            by_cases hzA : z ∈ A
            · show ‖A.indicator f z - (χ z : ℂ) * g0 z‖₊ ≤ _
              rw [hχ1 hzA, Pi.one_apply, ofReal_one, one_mul]
            · show ‖A.indicator f z - (χ z : ℂ) * g0 z‖₊ ≤ _
              rw [indicator_of_notMem hzA, zero_sub, zero_sub, nnnorm_neg, nnnorm_neg, nnnorm_mul]
              have hc : ‖(χ z : ℂ)‖₊ ≤ 1 := by
                rw [← NNReal.coe_le_coe, coe_nnnorm, Complex.norm_real, Real.norm_of_nonneg (hχI z).1]
                exact (hχI z).2
              calc ‖(χ z : ℂ)‖₊ * ‖g0 z‖₊ ≤ 1 * ‖g0 z‖₊ := by gcongr
                _ = ‖g0 z‖₊ := one_mul _
          · rw [indicator_of_notMem hzU]
            have hzA : z ∉ A := fun h => hzU (hAU h)
            show (‖A.indicator f z - (χ z : ℂ) * g0 z‖₊ : ℝ≥0∞) ^ 2 * ENNReal.ofReal (rho z) ≤ 0
            rw [indicator_of_notMem hzA, hχ0 hzU, Pi.zero_apply, ofReal_zero, zero_mul, sub_zero, nnnorm_zero]
            simp
      _ ≤ ∫⁻ z, U.indicator
            (fun z => (‖(A.indicator f - (g0 : ℂ → ℂ)) z‖₊ : ℝ≥0∞) ^ 2 * ENNReal.ofReal (rho z)) z :=
          setLIntegral_le_lintegral _ _
      _ = ∫⁻ z in U, (‖(A.indicator f - (g0 : ℂ → ℂ)) z‖₊ : ℝ≥0∞) ^ 2 * ENNReal.ofReal (rho z) :=
          lintegral_indicator hUm _
  have h2 : normL2 unitDiscExterior (fun z => Aᶜ.indicator f z) < ENNReal.ofReal (ε / 2) := by
    have hAe : Aᶜ = ({z : ℂ | 1 + 1 / ((n : ℝ) + 1) ≤ ‖z‖} ∩ {z : ℂ | ‖z‖ ≤ (n : ℝ) + 2})ᶜ := by
      rw [← ha, ← hb]
    rw [hAe]
    exact hn
  calc normL2 unitDiscExterior (fun z => A.indicator f z - g z) +
        normL2 unitDiscExterior (fun z => Aᶜ.indicator f z) < ENNReal.ofReal (ε / 4) + ENNReal.ofReal (ε / 2) :=
        ENNReal.add_lt_add_of_le_of_lt (h1.trans_lt ENNReal.ofReal_lt_top).ne h1 h2
    _ = ENNReal.ofReal (3 * ε / 4) := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
        ring_nf
    _ < ENNReal.ofReal ε := (ENNReal.ofReal_lt_ofReal_iff hε).2 (by linarith)

/-- The pointwise estimate behind Lemma 3.5: `|(a + T)/(1 + ā T) - m| ≤ 2(|T - m| + 2|a|)` for `|a| ≤ 1/2`,
`|m|, |T| ≤ 1`. -/
theorem gtr_mul_sub_le {a T m : ℂ} (ha : ‖a‖ ≤ 1 / 2) (hm : ‖m‖ ≤ 1) (hT : ‖T‖ ≤ 1) :
    ‖(a + T) / (1 + conj a * T) - m‖ ≤ 2 * (‖T - m‖ + 2 * ‖a‖) := by
  have h1 : ‖conj a * T‖ ≤ 1 / 2 := by
    rw [norm_mul, Complex.norm_conj]
    nlinarith [norm_nonneg a, norm_nonneg T]
  have hden : 1 / 2 ≤ ‖1 + conj a * T‖ := by
    have h2 : ‖(1 : ℂ)‖ ≤ ‖1 + conj a * T‖ + ‖conj a * T‖ := by
      calc ‖(1 : ℂ)‖ = ‖(1 + conj a * T) - conj a * T‖ := by ring_nf
        _ ≤ _ := norm_sub_le _ _
    rw [norm_one] at h2
    linarith
  have hd0 : (1 + conj a * T) ≠ 0 := by
    intro h
    rw [h, norm_zero] at hden
    linarith
  have he : (a + T) / (1 + conj a * T) - m = ((T - m) + a - m * conj a * T) / (1 + conj a * T) := by
    rw [eq_div_iff hd0, sub_mul, div_mul_cancel₀ _ hd0]
    ring
  rw [he, norm_div]
  have h3 : ‖m * conj a * T‖ ≤ ‖a‖ := by
    rw [mul_assoc, norm_mul, norm_mul, Complex.norm_conj]
    nlinarith [norm_nonneg a, norm_nonneg T, norm_nonneg m, mul_nonneg (norm_nonneg a) (norm_nonneg T)]
  have hnum : ‖(T - m) + a - m * conj a * T‖ ≤ ‖T - m‖ + 2 * ‖a‖ := by
    calc ‖(T - m) + a - m * conj a * T‖ ≤ ‖(T - m) + a‖ + ‖m * conj a * T‖ := norm_sub_le _ _
      _ ≤ ‖T - m‖ + ‖a‖ + ‖a‖ := by gcongr; exact norm_add_le _ _
      _ = ‖T - m‖ + 2 * ‖a‖ := by ring
  rw [div_le_iff₀ (by linarith)]
  nlinarith [norm_nonneg (T - m), norm_nonneg a]

/-- `L²(ρ)` norm of a function bounded by `c` and supported in a closed annulus `r ≤ |z| ≤ R` of `𝔻*`. -/
theorem gtr_annulus_bound {r R : ℝ} (hr : 1 < r) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ c : ℝ, 0 ≤ c → ∀ f : ℂ → ℂ, (∀ z, ‖f z‖ ≤ c) →
      (∀ z, f z ≠ 0 → r ≤ ‖z‖ ∧ ‖z‖ ≤ R) → normL2 unitDiscExterior f ≤ ENNReal.ofReal (c * K) := by
  have hr2 : 0 < r ^ 2 - 1 := by nlinarith
  obtain ⟨L, hL⟩ : ∃ L : ℝ, L = 4 / (r ^ 2 - 1) ^ 2 := ⟨_, rfl⟩
  have hL0 : 0 ≤ L := by rw [hL]; positivity
  obtain ⟨V, hV⟩ : ∃ V : ℝ, V = (volume (closedBall (0 : ℂ) R)).toReal := ⟨_, rfl⟩
  have hV0 : 0 ≤ V := by rw [hV]; exact ENNReal.toReal_nonneg
  have hVe : volume (closedBall (0 : ℂ) R) = ENNReal.ofReal V := by
    rw [hV, ENNReal.ofReal_toReal measure_closedBall_lt_top.ne]
  refine ⟨Real.sqrt (L * V), Real.sqrt_nonneg _, fun c hc f hf hs => ?_⟩
  have hpt : ∀ z, (‖f z‖₊ : ℝ≥0∞) ^ 2 * ENNReal.ofReal (rho z) ≤
      (closedBall (0 : ℂ) R).indicator (fun _ => ENNReal.ofReal (c ^ 2 * L)) z := by
    intro z
    by_cases h0 : f z = 0
    · simp [h0]
    · obtain ⟨h1, h2⟩ := hs z h0
      rw [indicator_of_mem (mem_closedBall_zero_iff.2 h2)]
      have hz2 : r ^ 2 ≤ ‖z‖ ^ 2 := pow_le_pow_left₀ (by linarith) h1 2
      have hρ : rho z ≤ L := by
        unfold rho
        rw [hL]
        apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
        nlinarith
      have hρ0 : 0 ≤ rho z := by unfold rho; positivity
      rw [show ((‖f z‖₊ : ℝ≥0∞)) ^ 2 = ENNReal.ofReal (‖f z‖ ^ 2) by
        rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm, enorm_eq_nnnorm],
        ← ENNReal.ofReal_mul (sq_nonneg _)]
      apply ENNReal.ofReal_le_ofReal
      exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) (hf z) 2) hρ hρ0 (sq_nonneg c)
  have hint : ∫⁻ z in unitDiscExterior, (‖f z‖₊ : ℝ≥0∞) ^ 2 * ENNReal.ofReal (rho z) ≤
      ENNReal.ofReal (c ^ 2 * L) * ENNReal.ofReal V := by
    calc ∫⁻ z in unitDiscExterior, (‖f z‖₊ : ℝ≥0∞) ^ 2 * ENNReal.ofReal (rho z) ≤
          ∫⁻ z in unitDiscExterior, (closedBall (0 : ℂ) R).indicator (fun _ => ENNReal.ofReal (c ^ 2 * L)) z :=
          lintegral_mono (fun z => hpt z)
      _ ≤ ∫⁻ z, (closedBall (0 : ℂ) R).indicator (fun _ => ENNReal.ofReal (c ^ 2 * L)) z :=
          setLIntegral_le_lintegral _ _
      _ = ENNReal.ofReal (c ^ 2 * L) * ENNReal.ofReal V := by
          rw [lintegral_indicator_const measurableSet_closedBall, hVe]
  unfold normL2
  calc (∫⁻ z in unitDiscExterior, (‖f z‖₊ : ℝ≥0∞) ^ 2 * ENNReal.ofReal (rho z)) ^ (1 / 2 : ℝ) ≤
        (ENNReal.ofReal (c ^ 2 * L) * ENNReal.ofReal V) ^ (1 / 2 : ℝ) :=
        ENNReal.rpow_le_rpow hint (by norm_num)
    _ = ENNReal.ofReal (c * Real.sqrt (L * V)) := by
        rw [← ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num),
          ← Real.sqrt_eq_rpow, mul_assoc, Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq hc]

/-- Transfer by a small harmonic `w_ν`: `‖F ∘ w_ν‖₂ ≤ √2 ‖F‖₂` (from `grp_density_fwd`). -/
theorem gtr_comp_L2 {ν : LinfStar} (hν : ν ∈ harmonicBeltrami) (hδ : ‖ν‖ < delta0) {F : ℂ → ℂ}
    (hF : AEStronglyMeasurable F (volume.restrict unitDiscExterior)) :
    normL2 unitDiscExterior (fun z => F (wA ν z)) ≤ ENNReal.ofReal (Real.sqrt 2) * normL2 unitDiscExterior F := by
  have h := grp_density_fwd hν hδ hF
  unfold normL2
  calc (∫⁻ z in unitDiscExterior, (‖F (wA ν z)‖₊ : ℝ≥0∞) ^ 2 * ENNReal.ofReal (rho z)) ^ (1 / 2 : ℝ) ≤
        (2 * ∫⁻ u in unitDiscExterior, (‖F u‖₊ : ℝ≥0∞) ^ 2 * ENNReal.ofReal (rho u)) ^ (1 / 2 : ℝ) :=
        ENNReal.rpow_le_rpow h (by norm_num)
    _ = (2 : ℝ≥0∞) ^ (1 / 2 : ℝ) *
        (∫⁻ u in unitDiscExterior, (‖F u‖₊ : ℝ≥0∞) ^ 2 * ENNReal.ofReal (rho u)) ^ (1 / 2 : ℝ) :=
        ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)
    _ = _ := by
        rw [Real.sqrt_eq_rpow, ← ENNReal.ofReal_rpow_of_nonneg (by norm_num) (by norm_num)]
        norm_num

/-- Minkowski for four terms in `L²(𝔻*, ρ)`, from a pointwise a.e. bound. -/
theorem gtr_normL2_le_four {f a b c d : ℂ → ℂ} (hf : AEStronglyMeasurable f (volume.restrict unitDiscExterior))
    (ha : AEStronglyMeasurable a (volume.restrict unitDiscExterior))
    (hb : AEStronglyMeasurable b (volume.restrict unitDiscExterior))
    (hc : AEStronglyMeasurable c (volume.restrict unitDiscExterior))
    (hd : AEStronglyMeasurable d (volume.restrict unitDiscExterior))
    (h : ∀ᵐ z ∂(volume.restrict unitDiscExterior), ‖f z‖ ≤ ‖a z‖ + ‖b z‖ + ‖c z‖ + ‖d z‖) :
    normL2 unitDiscExterior f ≤ normL2 unitDiscExterior a + normL2 unitDiscExterior b +
      normL2 unitDiscExterior c + normL2 unitDiscExterior d := by
  have hac := withDensity_absolutelyContinuous (volume.restrict unitDiscExterior) (fun z => ENNReal.ofReal (rho z))
  have ha' := ha.mono_ac hac
  have hb' := hb.mono_ac hac
  have hc' := hc.mono_ac hac
  have hd' := hd.mono_ac hac
  rw [grp_normL2_eq _ hf, grp_normL2_eq _ ha, grp_normL2_eq _ hb, grp_normL2_eq _ hc, grp_normL2_eq _ hd,
    ← eLpNorm_norm _ ha', ← eLpNorm_norm _ hb', ← eLpNorm_norm _ hc', ← eLpNorm_norm _ hd']
  refine (eLpNorm_mono_ae_real (hf.mono_ac hac) (hac.ae_le h)).trans ?_
  refine (eLpNorm_add_le (f := fun z => ‖a z‖ + ‖b z‖ + ‖c z‖) (g := fun z => ‖d z‖) (by norm_num)).trans ?_
  gcongr
  refine (eLpNorm_add_le (f := fun z => ‖a z‖ + ‖b z‖) (g := fun z => ‖c z‖) (by norm_num)).trans ?_
  gcongr
  exact eLpNorm_add_le (f := fun z => ‖a z‖) (g := fun z => ‖b z‖) (by norm_num)

theorem gtr_nnnorm_ofReal (x : ℂ) : (‖x‖₊ : ℝ≥0∞) = ENNReal.ofReal ‖x‖ := by
  rw [← coe_nnnorm, ENNReal.ofReal_coe_nnreal]

/-- The core `L²` estimate of Lemma 3.5 (TT:1998–2036): `‖μ * ν - μ‖₂ → 0` as `ν → 0` (harmonic, small in sup and in
`L²`), for fixed `μ ∈ L∞(𝔻*)₁ ∩ L²`. -/
theorem gtr_translate_core {μ : LinfStar} (hμ : μ ∈ LinfStarBall) (hμ2 : normL2 unitDiscExterior μ < ⊤)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ ν ∈ harmonicBeltrami, ‖ν‖ < δ → normL2 unitDiscExterior ν < ENNReal.ofReal δ →
      normL2 unitDiscExterior (beltramiMul μ ν - μ : LinfStar) < ENNReal.ofReal ε := by
  have hd := delta0_bounds
  have hEo : MeasurableSet unitDiscExterior := resolvent_exterior_isOpen.measurableSet
  have hμ1 : ‖μ‖ < 1 := mem_ball_zero_iff.mp hμ
  have hs2 : 0 < 8 * Real.sqrt 2 + 8 := by positivity
  obtain ⟨η, hη⟩ : ∃ η : ℝ, η = ε / (8 * Real.sqrt 2 + 8) := ⟨_, rfl⟩
  have hη0 : 0 < η := by rw [hη]; positivity
  obtain ⟨g, hgc, ⟨r, R, hr, hsupp⟩, hgF⟩ := gtr_dense_cc (Lp.aestronglyMeasurable μ) hμ2 hη0
  obtain ⟨r', R', δp, hr', hδp, hpre⟩ := gph_preimage (R := R) hr
  have hrs : 1 < min r r' := lt_min hr hr'
  obtain ⟨K, hK0, hK⟩ := gtr_annulus_bound (R := max R R') hrs
  obtain ⟨Mg, hMg0, hMg⟩ : ∃ Mg : ℝ, 0 ≤ Mg ∧ ∀ z, ‖g z‖ ≤ Mg := by
    obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : ℂ) R).exists_bound_of_continuousOn hgc.continuousOn
    refine ⟨max C 0, le_max_right _ _, fun z => ?_⟩
    by_cases h0 : g z = 0
    · rw [h0, norm_zero]
      exact le_max_right _ _
    · exact (hC z (mem_closedBall_zero_iff.2 (hsupp z h0).2)).trans (le_max_left _ _)
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = ε / (8 * (K + 1)) := ⟨_, rfl⟩
  have hc0 : 0 < c := by rw [hc]; positivity
  have huc := (isCompact_closedBall (0 : ℂ) (max R R' + 1)).uniformContinuousOn_of_continuous hgc.continuousOn
  obtain ⟨δu, hδu, hu⟩ := Metric.uniformContinuousOn_iff.mp huc (c / 2) (by positivity)
  obtain ⟨δ1, hδ1, hnear⟩ := gph_near_id (R := max R R') hrs (lt_min hδu one_pos)
  have hε2 : 0 < c / (2 * (Mg + 1)) := by positivity
  obtain ⟨δ2, hδ2, hphase⟩ := gph_phase (R := max R R') hrs hε2
  refine ⟨min (min (min (1 / 2) delta0) (min δp δ1)) (min δ2 (ε / 16)),
    lt_min (lt_min (lt_min (by norm_num) hd.1) (lt_min hδp hδ1)) (lt_min hδ2 (by positivity)),
    fun ν hν hνs hνL => ?_⟩
  have hν12 : ‖ν‖ < 1 / 2 :=
    lt_of_lt_of_le hνs ((min_le_left _ _).trans ((min_le_left _ _).trans (min_le_left _ _)))
  have hνd : ‖ν‖ < delta0 :=
    lt_of_lt_of_le hνs ((min_le_left _ _).trans ((min_le_left _ _).trans (min_le_right _ _)))
  have hνp : ‖ν‖ < δp :=
    lt_of_lt_of_le hνs ((min_le_left _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hν1 : ‖ν‖ < δ1 :=
    lt_of_lt_of_le hνs ((min_le_left _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hν2 : ‖ν‖ < δ2 := lt_of_lt_of_le hνs ((min_le_right _ _).trans (min_le_left _ _))
  have hνL' : normL2 unitDiscExterior ν < ENNReal.ofReal (ε / 16) :=
    lt_of_lt_of_le hνL (ENNReal.ofReal_le_ofReal ((min_le_right _ _).trans (min_le_right _ _)))
  have hνB : ν ∈ LinfStarBall := mem_ball_zero_iff.mpr (by linarith)
  -- the bounding function `E`: the constant `c` on the annulus `min r r' ≤ |z| ≤ max R R'`
  let E : ℂ → ℂ := fun z => if min r r' ≤ ‖z‖ ∧ ‖z‖ ≤ max R R' then (c : ℂ) else 0
  have hEn : ∀ z, min r r' ≤ ‖z‖ ∧ ‖z‖ ≤ max R R' → ‖E z‖ = c := by
    intro z hA
    simp only [E, hA, and_self, ↓reduceIte, Complex.norm_real, Real.norm_of_nonneg hc0.le]
  have hEb : ∀ z, ‖E z‖ ≤ c := by
    intro z
    by_cases hA : min r r' ≤ ‖z‖ ∧ ‖z‖ ≤ max R R'
    · rw [hEn z hA]
    · simp only [E, hA, ↓reduceIte, norm_zero]
      exact hc0.le
  have hEs : ∀ z, E z ≠ 0 → min r r' ≤ ‖z‖ ∧ ‖z‖ ≤ max R R' := by
    intro z h
    by_contra hA
    simp only [E, hA, ↓reduceIte, ne_eq, not_true_eq_false] at h
  -- the pointwise estimate
  have hpt : ∀ᵐ z ∂(volume.restrict unitDiscExterior), ‖(beltramiMul μ ν - μ : LinfStar) z‖ ≤
      ‖(2 : ℂ) * (μ (wA ν z) - g (wA ν z))‖ + ‖(2 : ℂ) * E z‖ + ‖(2 : ℂ) * (μ z - g z)‖ +
        ‖(4 : ℂ) * ν z‖ := by
    filter_upwards [Lp.coeFn_sub (beltramiMul μ ν) μ, bc_mul_ae hνB hμ, ae_restrict_of_ae (bc_wA_ae hνB),
      LinfStar_ae_norm_le ν, LinfStar_ae_norm_le μ, bc_b_bound (l := μ) hνB, ae_restrict_mem hEo]
      with z hsub hmul hw hνz hμz hb hz
    rw [hsub, Pi.sub_apply, hmul]
    obtain ⟨τ, hτd⟩ : ∃ τ : ℂ, τ = conj (dz (wA ν) z) / dz (wA ν) z := ⟨_, rfl⟩
    rw [← hτd] at hb ⊢
    have hdz : dz (wA ν) z ≠ 0 := hw.2.1
    have hτ : ‖τ‖ = 1 := by
      rw [hτd, norm_div, Complex.norm_conj, div_self (norm_ne_zero_iff.2 hdz)]
    rw [mul_assoc (conj (ν z))]
    have key := gtr_mul_sub_le (a := ν z) (T := μ (wA ν z) * τ) (m := μ z)
      (by linarith) (hμz.trans hμ1.le) (hb.trans hμ1.le)
    have hD : ‖g (wA ν z) * τ - g z‖ ≤ ‖E z‖ := by
      by_cases hA : min r r' ≤ ‖z‖ ∧ ‖z‖ ≤ max R R'
      · rw [hEn z hA]
        obtain ⟨-, hwz⟩ := hnear ν hνB hν1 z hA.1 hA.2
        obtain ⟨-, -, hph⟩ := hphase ν hν hν2 z hA.1 hA.2
        rw [← hτd] at hph
        have hz1 : z ∈ closedBall (0 : ℂ) (max R R' + 1) := mem_closedBall_zero_iff.2 (by linarith [hA.2])
        have hw1 : wA ν z ∈ closedBall (0 : ℂ) (max R R' + 1) := by
          rw [mem_closedBall_zero_iff]
          have h1 := norm_sub_norm_le (wA ν z) z
          have h2 : ‖wA ν z - z‖ < 1 := lt_of_lt_of_le hwz (min_le_right _ _)
          linarith [hA.2]
        have hg1 : ‖g (wA ν z) - g z‖ < c / 2 := by
          have h := hu _ hw1 _ hz1 (by rw [dist_eq_norm]; exact lt_of_lt_of_le hwz (min_le_left _ _))
          rwa [dist_eq_norm] at h
        have hsplit : g (wA ν z) * τ - g z = (g (wA ν z) - g z) * τ + g z * (τ - 1) := by ring
        rw [hsplit]
        have hm : Mg * (c / (2 * (Mg + 1))) ≤ c / 2 := by
          rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
          nlinarith
        calc ‖(g (wA ν z) - g z) * τ + g z * (τ - 1)‖ ≤ ‖(g (wA ν z) - g z) * τ‖ + ‖g z * (τ - 1)‖ :=
              norm_add_le _ _
          _ = ‖g (wA ν z) - g z‖ + ‖g z‖ * ‖τ - 1‖ := by rw [norm_mul, norm_mul, hτ, mul_one]
          _ ≤ c / 2 + Mg * (c / (2 * (Mg + 1))) := by
              gcongr
              · exact hMg z
          _ ≤ c := by linarith
      · have hgz : g z = 0 := by
          by_contra h0
          obtain ⟨h1, h2⟩ := hsupp z h0
          exact hA ⟨(min_le_left _ _).trans h1, h2.trans (le_max_left _ _)⟩
        have hgw : g (wA ν z) = 0 := by
          by_contra h0
          obtain ⟨h1, h2⟩ := hsupp _ h0
          have hinf : wAS ν (z : ExtPlane) ≠ extInf := by
            intro he
            have h0' : wA ν z = 0 := by
              unfold wA
              rw [he]
              rfl
            rw [h0', norm_zero] at h1
            linarith
          obtain ⟨h3, h4⟩ := hpre ν hνB hνp z hz hinf h1 h2
          exact hA ⟨(min_le_right _ _).trans h3, h4.trans (le_max_right _ _)⟩
        rw [hgz, hgw, zero_mul, sub_zero, norm_zero]
        exact norm_nonneg _
    have htri : ‖μ (wA ν z) * τ - μ z‖ ≤ ‖μ (wA ν z) - g (wA ν z)‖ + ‖E z‖ + ‖μ z - g z‖ := by
      have hsplit : μ (wA ν z) * τ - μ z =
          (μ (wA ν z) - g (wA ν z)) * τ + (g (wA ν z) * τ - g z) + (g z - μ z) := by ring
      rw [hsplit]
      calc ‖(μ (wA ν z) - g (wA ν z)) * τ + (g (wA ν z) * τ - g z) + (g z - μ z)‖ ≤
            ‖(μ (wA ν z) - g (wA ν z)) * τ‖ + ‖g (wA ν z) * τ - g z‖ + ‖g z - μ z‖ := norm_add₃_le
        _ ≤ ‖μ (wA ν z) - g (wA ν z)‖ + ‖E z‖ + ‖μ z - g z‖ := by
            rw [norm_mul, hτ, mul_one, norm_sub_rev (g z)]
            gcongr
    have hn2 : ‖(2 : ℂ)‖ = 2 := by norm_num
    have hn4 : ‖(4 : ℂ)‖ = 4 := by norm_num
    rw [norm_mul, norm_mul, norm_mul, norm_mul, hn2, hn4]
    linarith
  -- `L²` bounds
  have hFm : AEStronglyMeasurable (fun z => μ z - g z) (volume.restrict unitDiscExterior) :=
    (Lp.aestronglyMeasurable μ).sub hgc.aestronglyMeasurable
  have hFw : AEStronglyMeasurable (fun z => μ (wA ν z) - g (wA ν z)) (volume.restrict unitDiscExterior) :=
    hFm.comp_quasiMeasurePreserving (bc_wA_qmp hνB)
  have hEm : AEStronglyMeasurable E (volume.restrict unitDiscExterior) := by
    have hset : MeasurableSet {z : ℂ | min r r' ≤ ‖z‖ ∧ ‖z‖ ≤ max R R'} :=
      (measurableSet_le measurable_const measurable_norm).inter (measurableSet_le measurable_norm measurable_const)
    exact (Measurable.ite hset measurable_const measurable_const).aestronglyMeasurable
  have hmain := gtr_normL2_le_four (Lp.aestronglyMeasurable _) (hFw.const_mul 2) (hEm.const_mul 2)
    (hFm.const_mul 2) ((Lp.aestronglyMeasurable ν).const_mul 4) hpt
  rw [normL2_const_mul, normL2_const_mul, normL2_const_mul, normL2_const_mul, gtr_nnnorm_ofReal,
    gtr_nnnorm_ofReal] at hmain
  have hn2 : ‖(2 : ℂ)‖ = 2 := by norm_num
  have hn4 : ‖(4 : ℂ)‖ = 4 := by norm_num
  rw [hn2, hn4] at hmain
  have h1 : normL2 unitDiscExterior (fun z => μ (wA ν z) - g (wA ν z)) ≤ ENNReal.ofReal (Real.sqrt 2 * η) := by
    refine (gtr_comp_L2 hν hνd hFm).trans ?_
    rw [ENNReal.ofReal_mul (Real.sqrt_nonneg _)]
    exact mul_le_mul' le_rfl hgF.le
  have h2 : normL2 unitDiscExterior E ≤ ENNReal.ofReal (c * K) := hK c hc0.le E hEb hEs
  have h3 : normL2 unitDiscExterior (fun z => μ z - g z) ≤ ENNReal.ofReal η := hgF.le
  have p1 : 0 ≤ 2 * (Real.sqrt 2 * η) := by positivity
  have p2 : 0 ≤ 2 * (c * K) := by have := mul_nonneg hc0.le hK0; linarith
  have p3 : 0 ≤ 2 * η := by positivity
  have p4 : 0 ≤ 4 * (ε / 16) := by positivity
  have hsum : ENNReal.ofReal 2 * normL2 unitDiscExterior (fun z => μ (wA ν z) - g (wA ν z)) +
      ENNReal.ofReal 2 * normL2 unitDiscExterior E + ENNReal.ofReal 2 * normL2 unitDiscExterior (fun z => μ z - g z) +
      ENNReal.ofReal 4 * normL2 unitDiscExterior ν ≤
      ENNReal.ofReal (2 * (Real.sqrt 2 * η) + 2 * (c * K) + 2 * η + 4 * (ε / 16)) := by
    rw [ENNReal.ofReal_add (by linarith) p4, ENNReal.ofReal_add (by linarith) p3, ENNReal.ofReal_add p1 p2,
      ENNReal.ofReal_mul (p := 2) (q := Real.sqrt 2 * η) (by norm_num),
      ENNReal.ofReal_mul (p := 2) (q := c * K) (by norm_num),
      ENNReal.ofReal_mul (p := 2) (q := η) (by norm_num),
      ENNReal.ofReal_mul (p := 4) (q := ε / 16) (by norm_num)]
    exact add_le_add (add_le_add (add_le_add (mul_le_mul' le_rfl h1) (mul_le_mul' le_rfl h2))
      (mul_le_mul' le_rfl h3)) (mul_le_mul' le_rfl hνL'.le)
  refine lt_of_le_of_lt (hmain.trans hsum) ((ENNReal.ofReal_lt_ofReal_iff hε).2 ?_)
  have e1 : 2 * (Real.sqrt 2 * η) + 2 * η = ε / 4 := by
    rw [hη]
    field_simp
    ring
  have e2 : 2 * (c * K) < ε / 4 := by
    rw [hc, show 2 * (ε / (8 * (K + 1)) * K) = ε / 4 * (K / (K + 1)) by field_simp; ring]
    have : K / (K + 1) < 1 := by rw [div_lt_one (by positivity)]; linarith
    nlinarith
  linarith

/-- A uniform sup bound for products: `‖y * x‖ ≤ √(1 - (1 - s²)(1 - t²)/4)` when `‖x‖ ≤ s`, `‖y‖ ≤ t`. -/
theorem gtr_mul_norm_bound {x y : LinfStar} (hx : x ∈ LinfStarBall) (hy : y ∈ LinfStarBall) {s t : ℝ}
    (hs : ‖x‖ ≤ s) (ht : ‖y‖ ≤ t) (hs1 : s < 1) (ht1 : t < 1) :
    ‖beltramiMul y x‖ ≤ Real.sqrt (1 - (1 - s ^ 2) * (1 - t ^ 2) / 4) := by
  refine (gtp_mul_norm_le hx hy).trans (Real.sqrt_le_sqrt ?_)
  have h1 : ‖x‖ ^ 2 ≤ s ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hs 2
  have h2 : ‖y‖ ^ 2 ≤ t ^ 2 := pow_le_pow_left₀ (norm_nonneg _) ht 2
  have h3 : 0 ≤ 1 - s ^ 2 := by nlinarith [norm_nonneg x]
  have h4 : 0 ≤ 1 - t ^ 2 := by nlinarith [norm_nonneg y]
  have h5 : (1 - s ^ 2) * (1 - t ^ 2) ≤ (1 - ‖x‖ ^ 2) * (1 - ‖y‖ ^ 2) := by
    apply mul_le_mul <;> nlinarith
  linarith

theorem gtr_sqrt_lt_one {s t : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) (ht0 : 0 ≤ t) (ht1 : t < 1) :
    Real.sqrt (1 - (1 - s ^ 2) * (1 - t ^ 2) / 4) < 1 := by
  rw [Real.sqrt_lt' (by norm_num)]
  have h3 : 0 < 1 - s ^ 2 := by nlinarith
  have h4 : 0 < 1 - t ^ 2 := by nlinarith
  nlinarith [mul_pos h3 h4]

/-- The core of Corollary 3.6: for `μ ∈ 𝒪(𝔻*)₁ ∩ L²`, small chart coordinates `φ` at the origin give `(μ * Λφ) * μ⁻¹`
of small chart coordinate. -/
theorem gtr_adjoint_core {μ : LinfStarBall} (hμ : (μ : LinfStar) ∈ groupO)
    (hμ2 : normL2 unitDiscExterior μ < ⊤) :
    ∀ ε : ℝ, 0 < ε → ε ≤ Real.sqrt (π / 3) → ∃ δ : ℝ, 0 < δ ∧ δ ≤ Real.sqrt (π / 3) ∧
      ∀ φ : A2 unitDisc, ‖φ‖ < δ → ∃ φ' : A2 unitDisc, ‖φ'‖ < ε ∧
        ∀ h : beltramiMul (beltramiMul (μ : LinfStar) (Lambda (A2toAInf φ))) (beltramiInv (μ : LinfStar)) ∈
          LinfStarBall,
        Phi ⟨_, h⟩ = bersChartInv (⟨0, mem_ball_self one_pos⟩ : LinfStarBall) (A2toAInf φ') := by
  have hd := delta0_bounds
  have hμ1 : ‖(μ : LinfStar)‖ < 1 := mem_ball_zero_iff.mp μ.2
  have hμi := grp_inv_mem μ.2
  have hμi1 : ‖beltramiInv (μ : LinfStar)‖ < 1 := mem_ball_zero_iff.mp hμi
  obtain ⟨k1, hk1⟩ : ∃ k1 : ℝ, k1 = Real.sqrt (1 - (1 - delta0 ^ 2) * (1 - ‖(μ : LinfStar)‖ ^ 2) / 4) :=
    ⟨_, rfl⟩
  have hk10 : 0 ≤ k1 := hk1 ▸ Real.sqrt_nonneg _
  have hk11 : k1 < 1 := hk1 ▸ gtr_sqrt_lt_one hd.1.le hd.2 (norm_nonneg _) hμ1
  obtain ⟨k, hk⟩ : ∃ k : ℝ, k = Real.sqrt (1 - (1 - ‖beltramiInv (μ : LinfStar)‖ ^ 2) * (1 - k1 ^ 2) / 4) :=
    ⟨_, rfl⟩
  have hk0 : 0 ≤ k := hk ▸ Real.sqrt_nonneg _
  have hk1' : k < 1 := hk ▸ gtr_sqrt_lt_one (norm_nonneg _) hμi1 hk10 hk11
  obtain ⟨C, hC, hch⟩ := gtp_chart_of_small hk0 hk1'
  obtain ⟨C1, hC1, hlip⟩ := grp_lemma_2_7 (groupO_inv_mem hμ)
  intro ε hε hεr
  have hCC : 0 < C * C1 + 1 := by positivity
  obtain ⟨η, hη⟩ : ∃ η : ℝ, η = ε / (C * C1 + 1) := ⟨_, rfl⟩
  have hη0 : 0 < η := by rw [hη]; exact div_pos hε hCC
  obtain ⟨δ1, hδ1, hcore⟩ := gtr_translate_core μ.2 hμ2 hη0
  have hc0 : 0 < Real.sqrt (12 / π) := Real.sqrt_pos.2 (by positivity)
  refine ⟨min (min (Real.sqrt (π / 3)) (2 * delta0 / Real.sqrt (12 / π))) (min (δ1 / 2) (2 * δ1 / Real.sqrt (12 / π))),
    lt_min (lt_min (by positivity) (div_pos (by linarith [hd.1]) hc0)) (lt_min (by positivity) (by positivity)),
    (min_le_left _ _).trans (min_le_left _ _), fun φ hφ => ?_⟩
  have hφ1 : ‖φ‖ < min (Real.sqrt (π / 3)) (2 * delta0 / Real.sqrt (12 / π)) := lt_of_lt_of_le hφ (min_le_left _ _)
  have hφ2 : ‖φ‖ < δ1 / 2 := lt_of_lt_of_le hφ ((min_le_right _ _).trans (min_le_left _ _))
  have hφ3 : ‖φ‖ < 2 * δ1 / Real.sqrt (12 / π) := lt_of_lt_of_le hφ ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨hn, hharm, hsm, -⟩ := gtp_small_a hφ1
  have haB : Lambda (A2toAInf φ) ∈ LinfStarBall := Lambda_mem_ball hn
  -- smallness of `a` in sup and in `L²`
  have hasup : ‖Lambda (A2toAInf φ)‖ < δ1 := by
    have hb := (A2toAInf_bounded.2 φ).1
    have hl := Lambda_norm_le (A2toAInf φ)
    have h3 : Real.sqrt (12 / π) * ‖φ‖ < 2 * δ1 := by
      rwa [lt_div_iff₀ hc0, mul_comm] at hφ3
    linarith
  have haL2 : normL2 unitDiscExterior (Lambda (A2toAInf φ)) < ENNReal.ofReal δ1 := by
    rw [gtp_normL2_Lambda]
    exact (ENNReal.ofReal_lt_ofReal_iff hδ1).2 (by linarith)
  have htc := hcore _ hharm hasup haL2
  have hm : beltramiMul (μ : LinfStar) (Lambda (A2toAInf φ)) ∈ LinfStarBall := bg_mul_mem_ball haB μ.2
  have hlip' := hlip _ hm _ μ.2 (htc.trans ENNReal.ofReal_lt_top)
  rw [grp_mul_inv μ.2, sub_zero] at hlip'
  -- sup bound
  have hmsup : ‖beltramiMul (μ : LinfStar) (Lambda (A2toAInf φ))‖ ≤ k1 :=
    by rw [hk1]; exact gtr_mul_norm_bound haB μ.2 hsm.le le_rfl hd.2 hμ1
  have hlsup : ‖beltramiMul (beltramiMul (μ : LinfStar) (Lambda (A2toAInf φ))) (beltramiInv (μ : LinfStar))‖ ≤ k :=
    by rw [hk]; exact gtr_mul_norm_bound hμi hm le_rfl hmsup hμi1 hk11
  have hsmall : ENNReal.ofReal C *
      normL2 unitDiscExterior (beltramiMul (beltramiMul (μ : LinfStar) (Lambda (A2toAInf φ))) (beltramiInv (μ : LinfStar))) <
      ENNReal.ofReal ε := by
    calc ENNReal.ofReal C *
          normL2 unitDiscExterior (beltramiMul (beltramiMul (μ : LinfStar) (Lambda (A2toAInf φ))) (beltramiInv (μ : LinfStar))) ≤
        ENNReal.ofReal C * (ENNReal.ofReal C1 * ENNReal.ofReal η) :=
          mul_le_mul' le_rfl (hlip'.trans (mul_le_mul' le_rfl htc.le))
      _ = ENNReal.ofReal (C * C1 * η) := by
          rw [← ENNReal.ofReal_mul hC1.le, ← ENNReal.ofReal_mul hC.le, mul_assoc]
      _ < ENNReal.ofReal ε := by
          rw [ENNReal.ofReal_lt_ofReal_iff hε, hη, ← mul_div_assoc, div_lt_iff₀ hCC]
          nlinarith [mul_pos hC hC1]
  obtain ⟨φ', hφ', he⟩ := hch ⟨_, bg_mul_mem_ball hμi hm⟩ hlsup ε hε hεr hsmall
  exact ⟨φ', hφ', fun h => he⟩

/-- The adjoint map `[ν] ↦ [μ * ν * μ⁻¹]` sends small chart coordinates at the origin to small chart coordinates
(Corollary 3.6 in the chart at `0`). -/
theorem gtr_adjoint_SM {μ : LinfStarBall} (hμ : (μ : LinfStar) ∈ groupO)
    (hμ2 : normL2 unitDiscExterior μ < ⊤) :
    ∀ ε : ℝ, 0 < ε → ε ≤ Real.sqrt (π / 3) → ∃ δ : ℝ, 0 < δ ∧ δ ≤ Real.sqrt (π / 3) ∧
      ∀ φ : A2 unitDisc, ‖φ‖ < δ → ∃ φ' : A2 unitDisc, ‖φ'‖ < ε ∧
        mulT (mulT (Phi μ) (bersChartInv (⟨0, mem_ball_self one_pos⟩ : LinfStarBall) (A2toAInf φ)))
            (invT (Phi μ)) =
          bersChartInv (⟨0, mem_ball_self one_pos⟩ : LinfStarBall) (A2toAInf φ') := by
  intro ε hε hεr
  obtain ⟨δ, hδ, hδr, hδ'⟩ := gtr_adjoint_core hμ hμ2 ε hε hεr
  refine ⟨δ, hδ, hδr, fun φ hφ => ?_⟩
  obtain ⟨φ', hφ', he⟩ := hδ' φ hφ
  refine ⟨φ', hφ', ?_⟩
  have hn : ‖A2toAInf φ‖ < 2 := ct_A2toAInf_norm_lt (mem_ball_zero_iff.2 (lt_of_lt_of_le hφ hδr))
  rw [gtp_chart0 φ hn, gtp_mulT_phi, gtp_invT_phi, gtp_mulT_phi]
  exact he _

theorem gtr_chart_zero (κ : LinfStarBall) : bersChartInv κ (A2toAInf (0 : A2 unitDisc)) = Phi κ := by
  rw [A2toAInf_zero, ct_bersChartInv_eq (by simp), bt_rightTrans_phi]
  apply congrArg Phi
  apply Subtype.ext
  exact (congrArg (fun a => beltramiMul a (κ : LinfStar)) glr_lambda_zero).trans (grp_zero_mul κ.2)

theorem gtr_chart_continuous {κ : LinfStarBall} (hκ : (κ : LinfStar) ∈ groupO) :
    Continuous[(inferInstance : TopologicalSpace (ball (0 : A2 unitDisc) (Real.sqrt (π / 3)))),
        hilbertTopology]
      (fun φ : ball (0 : A2 unitDisc) (Real.sqrt (π / 3)) => bersChartInv κ (A2toAInf (φ : A2 unitDisc))) := by
  rw [continuous_iff_coinduced_le]
  unfold hilbertTopology
  exact le_iSup (fun μ : {μ : LinfStarBall // (μ : LinfStar) ∈ groupO} =>
    TopologicalSpace.coinduced (fun φ : ball (0 : A2 unitDisc) (Real.sqrt (π / 3)) =>
      bersChartInv μ.1 (A2toAInf (φ : A2 unitDisc))) inferInstance) ⟨κ, hκ⟩

theorem gtr_nhds_chart {κ : LinfStarBall} (hκ : (κ : LinfStar) ∈ groupO) {W : Set T1}
    (hW : W ∈ @nhds T1 hilbertTopology (Phi κ)) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ Real.sqrt (π / 3) ∧ ∀ φ : A2 unitDisc, ‖φ‖ < ε → bersChartInv κ (A2toAInf φ) ∈ W := by
  let _ : TopologicalSpace T1 := hilbertTopology
  have hr0 : 0 < Real.sqrt (π / 3) := by positivity
  obtain ⟨U, hUW, hUo, hU0⟩ := _root_.mem_nhds_iff.1 hW
  have hco : ContinuousOn (fun φ : A2 unitDisc => bersChartInv κ (A2toAInf φ))
      (ball (0 : A2 unitDisc) (Real.sqrt (π / 3))) :=
    continuousOn_iff_continuous_domRestrict.2 (gtr_chart_continuous hκ)
  have hpre := hco.isOpen_inter_preimage isOpen_ball hUo
  have h0mem : (0 : A2 unitDisc) ∈ ball (0 : A2 unitDisc) (Real.sqrt (π / 3)) ∩
      (fun φ : A2 unitDisc => bersChartInv κ (A2toAInf φ)) ⁻¹' U := by
    refine ⟨mem_ball_self hr0, ?_⟩
    show bersChartInv κ (A2toAInf (0 : A2 unitDisc)) ∈ U
    rw [gtr_chart_zero]
    exact hU0
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hpre 0 h0mem
  refine ⟨min ε (Real.sqrt (π / 3)), lt_min hε hr0, min_le_right _ _, fun φ hφ => ?_⟩
  have hφε : ‖φ‖ < ε := lt_of_lt_of_le hφ (min_le_left _ _)
  exact hUW (hball (mem_ball_zero_iff.2 hφε)).2

/-- Continuity at a chart centre from smallness of chart coordinates (general base points `κ, κ' ∈ 𝒪(𝔻*)₁`;
generalizes `gtp_continuousAt`). -/
theorem gtr_continuousAt_chart {κ κ' : LinfStarBall} (hκ : (κ : LinfStar) ∈ groupO)
    (hκ' : (κ' : LinfStar) ∈ groupO) {f : T1 → T1} (h0 : f (Phi κ) = Phi κ')
    (hs : ∀ ε : ℝ, 0 < ε → ε ≤ Real.sqrt (π / 3) → ∃ δ : ℝ, 0 < δ ∧ δ ≤ Real.sqrt (π / 3) ∧
      ∀ φ : A2 unitDisc, ‖φ‖ < δ → ∃ φ' : A2 unitDisc, ‖φ'‖ < ε ∧
        f (bersChartInv κ (A2toAInf φ)) = bersChartInv κ' (A2toAInf φ')) :
    @ContinuousAt T1 T1 hilbertTopology hilbertTopology f (Phi κ) := by
  let _ : TopologicalSpace T1 := hilbertTopology
  intro W hW
  rw [h0] at hW
  rw [Filter.mem_map]
  obtain ⟨ε, hε, hεr, hεW⟩ := gtr_nhds_chart hκ' hW
  obtain ⟨δ, hδ, hδr, hδ'⟩ := hs ε hε hεr
  have hopen := glr_chart_image_open hκ isOpen_ball (ball_subset_ball hδr)
  have hmem : Phi κ ∈ (fun φ : A2 unitDisc => bersChartInv κ (A2toAInf φ)) '' ball 0 δ :=
    ⟨0, mem_ball_self hδ, gtr_chart_zero κ⟩
  refine Filter.mem_of_superset (hopen.mem_nhds hmem) ?_
  rintro _ ⟨φ, hφ, rfl⟩
  obtain ⟨φ', hφ', he⟩ := hδ' φ (mem_ball_zero_iff.1 hφ)
  show f _ ∈ W
  rw [he]
  exact hεW φ' hφ'

theorem gtr_leftTrans_phi (μ x : LinfStarBall) :
    leftTrans μ (Phi x) = Phi ⟨beltramiMul (μ : LinfStar) (x : LinfStar), bg_mul_mem_ball x.2 μ.2⟩ := by
  unfold leftTrans
  simp only [bg_mul_mem_ball (Quotient.out (Phi x) : LinfStarBall).2 μ.2, ↓reduceDIte]
  exact Quotient.sound (bc_beltramiMul_respects (fun _ _ => rfl) (Quotient.mk_out (s := teichSetoid) x))

theorem gtr_leftTrans_congr {μ μ' : LinfStarBall} (h : Phi μ = Phi μ') : leftTrans μ = leftTrans μ' := by
  funext p
  obtain ⟨l, rfl⟩ := Quotient.exists_rep p
  change leftTrans μ (Phi l) = leftTrans μ' (Phi l)
  rw [gtr_leftTrans_phi, gtr_leftTrans_phi]
  exact Quotient.sound (bc_beltramiMul_respects (Quotient.exact h) (fun _ _ => rfl))

/-- Left translation in charts: `L_μ ∘ (chart at κ) = (chart at μ * κ) ∘ (coordinates of Ad_μ)`. -/
theorem gtr_leftTrans_SM {μ κ : LinfStarBall} (hμ : (μ : LinfStar) ∈ groupO)
    (hμ2 : normL2 unitDiscExterior μ < ⊤) (hκ : (κ : LinfStar) ∈ groupO) :
    ∀ ε : ℝ, 0 < ε → ε ≤ Real.sqrt (π / 3) → ∃ δ : ℝ, 0 < δ ∧ δ ≤ Real.sqrt (π / 3) ∧
      ∀ φ : A2 unitDisc, ‖φ‖ < δ → ∃ φ' : A2 unitDisc, ‖φ'‖ < ε ∧
        leftTrans μ (bersChartInv κ (A2toAInf φ)) =
          bersChartInv ⟨beltramiMul (μ : LinfStar) (κ : LinfStar), bg_mul_mem_ball κ.2 μ.2⟩ (A2toAInf φ') := by
  -- `hκ` is not needed: the chart formula holds at every base point.
  have _hκ := hκ
  intro ε hε hεr
  obtain ⟨δ, hδ, hδr, hδ'⟩ := gtr_adjoint_core hμ hμ2 ε hε hεr
  refine ⟨δ, hδ, hδr, fun φ hφ => ?_⟩
  obtain ⟨φ', hφ', he⟩ := hδ' φ hφ
  refine ⟨φ', hφ', ?_⟩
  have hn : ‖A2toAInf φ‖ < 2 := ct_A2toAInf_norm_lt (mem_ball_zero_iff.2 (lt_of_lt_of_le hφ hδr))
  have hn' : ‖A2toAInf φ'‖ < 2 := ct_A2toAInf_norm_lt (mem_ball_zero_iff.2 (lt_of_lt_of_le hφ' hεr))
  set a : LinfStar := Lambda (A2toAInf φ) with ha
  have haB : a ∈ LinfStarBall := Lambda_mem_ball hn
  have hμi := grp_inv_mem μ.2
  have hm : beltramiMul (μ : LinfStar) a ∈ LinfStarBall := bg_mul_mem_ball haB μ.2
  have hl : beltramiMul (beltramiMul (μ : LinfStar) a) (beltramiInv (μ : LinfStar)) ∈ LinfStarBall :=
    bg_mul_mem_ball hμi hm
  have hmk : beltramiMul (μ : LinfStar) (κ : LinfStar) ∈ LinfStarBall := bg_mul_mem_ball κ.2 μ.2
  have halg : beltramiMul (μ : LinfStar) (beltramiMul a (κ : LinfStar)) =
      beltramiMul (beltramiMul (beltramiMul (μ : LinfStar) a) (beltramiInv (μ : LinfStar)))
        (beltramiMul (μ : LinfStar) (κ : LinfStar)) := by
    rw [grp_mul_assoc hm hμi hmk, ← grp_mul_assoc hμi μ.2 κ.2, grp_inv_mul μ.2, grp_zero_mul κ.2,
      grp_mul_assoc μ.2 haB κ.2]
  rw [ct_bersChartInv_eq hn, bt_rightTrans_phi, gtr_leftTrans_phi, ct_bersChartInv_eq hn',
    ← gtp_chart0 φ' hn', ← he hl, bt_rightTrans_phi]
  apply congrArg Phi
  exact Subtype.ext halg

/-- **Lemma 3.5** (TT:1964), byte-identical copy of `lemma_3_5`. -/
theorem gtr_lemma_3_5 {μ : LinfStarBall} (hμ : Phi μ ∈ T01) :
    @ContinuousOn _ _ hilbertTopology hilbertTopology (leftTrans μ) T01 := by
  obtain ⟨μ0, hμ0L, hμ0O, hμ0⟩ := lemma_3_3 hμ
  rw [gtr_leftTrans_congr hμ0.symm]
  intro p hp
  obtain ⟨κ, -, hκO, rfl⟩ := lemma_3_3 hp
  exact @ContinuousAt.continuousWithinAt T1 T1 hilbertTopology hilbertTopology _ T01 _
    (gtr_continuousAt_chart hκO (groupO_mul_mem hμ0O hκO) (gtr_leftTrans_phi μ0 κ)
      (gtr_leftTrans_SM hμ0O hμ0L hκO))

/-- **Corollary 3.6** (TT:2040–2046), byte-identical copy of `cor_3_6`. -/
theorem gtr_cor_3_6 {p : T1} (hp : p ∈ T01) :
    @ContinuousWithinAt _ _ hilbertTopology hilbertTopology (fun q => mulT (mulT p q) (invT p)) T01 originT := by
  obtain ⟨μ0, hμ0L, hμ0O, rfl⟩ := lemma_3_3 hp
  have h0 : (fun q => mulT (mulT (Phi μ0) q) (invT (Phi μ0))) originT = originT := by
    show mulT (mulT (Phi μ0) originT) (invT (Phi μ0)) = originT
    unfold originT
    rw [gtp_mulT_phi, gtp_invT_phi, gtp_mulT_phi]
    apply congrArg Phi
    apply Subtype.ext
    show beltramiMul (beltramiMul (μ0 : LinfStar) 0) (beltramiInv (μ0 : LinfStar)) = 0
    rw [grp_mul_zero μ0.2, grp_mul_inv μ0.2]
  exact @ContinuousAt.continuousWithinAt T1 T1 hilbertTopology hilbertTopology _ T01 _
    (gtp_continuousAt h0 (gtr_adjoint_SM hμ0O hμ0L))

/-- **Lemma 3.5** (TT:1964). Left translations `L_[μ] : [ν] ↦ [μ * ν]` are continuous on `T₀(1)` (Hilbert manifold
topology), for `[μ] ∈ T₀(1)`. -/
theorem lemma_3_5 {μ : LinfStarBall} (hμ : Phi μ ∈ T01) :
    @ContinuousOn _ _ hilbertTopology hilbertTopology (leftTrans μ) T01 :=
  gtr_lemma_3_5 hμ

/-- **Corollary 3.6** (TT:2040–2046). For every `[μ] ∈ T₀(1)` the adjoint map `[ν] ↦ [μ * ν * μ⁻¹]` of `T₀(1)` is
continuous at the origin. -/
theorem cor_3_6 {p : T1} (hp : p ∈ T01) :
    @ContinuousWithinAt _ _ hilbertTopology hilbertTopology (fun q => mulT (mulT p q) (invT p)) T01 originT :=
  gtr_cor_3_6 hp

end TakhtajanTeo
