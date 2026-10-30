import TakhtajanTeo.Ch1.S19Mix
import TakhtajanTeo.Ch1.InvariantProjectionMixing

/-!
# W-MIX stage 2: the ball-average mixing statement `s19m_core` (`s19c_` prefix), top layer

`s19c_core` proves the frozen hypothesis `hcore` of `s19m_lemma_1_9_of_core` from a packaged unitary representation
(`hrep`, the representation-side layer R1–R4, see `CORE_PLAN.md`) through three reductions:
- **C0** `s19c_core_of_inv`: the complex `f`, `L¹(F)` weight `g` statement follows from the case of real, bounded,
  measurable, everywhere-`Γ`-invariant `f` and `g` (bilinearity; automorphic representative made everywhere invariant
  on the co-null `Γ`-invariant set where it is; truncation + periodization of `g` with `‖M_s f‖ ≤ C`);
- **C1** `s19c_radial`: hyperbolic polar coordinates about `z ∈ 𝔻*` through `T_z(w) = (z w + 1)/(w + z̄)` (`T_z ∞ = z`,
  `δ(T_z w, z) = 1/|w|`): `∬_{B(z,s)} f ρ = ∫_0^s 4u/(1 - u²)² ∫_0^{2π} f(T_z(e^{iθ}/u)) dθ du`;
- **C2** `s19c_core_of_rep`: the sphere pairing is the diagonal matrix coefficient at `a = √((1-u)/(1+u))`, which tends
  to the invariant projection (`diagonal_matrix_coeff_tendsto_projection`); the radial weights are probability
  densities on `(0, s)` whose mass escapes to `u → 1`.
-/

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal ComplexConjugate Classical Real Matrix MatrixGroups InnerProductSpace

noncomputable section

namespace TakhtajanTeo

open LiZhongQC

/-- The denominator of a product: `(g h)₁₀ z + (g h)₁₁ = (g₁₀ h(z) + g₁₁)(h₁₀ z + h₁₁)` off the pole of `h`. -/
theorem s19c_denom_mul (g h : SL2C) {z : ℂ} (hh : h 1 0 * z + h 1 1 ≠ 0) :
    (g * h : SL2C) 1 0 * z + (g * h : SL2C) 1 1 = (g 1 0 * mob h z + g 1 1) * (h 1 0 * z + h 1 1) := by
  have e := fd_mul_entries g h
  have hm : mob h z = (h 0 0 * z + h 0 1) / (h 1 0 * z + h 1 1) := rfl
  rw [e, e, hm]
  field_simp
  ring

/-- A measurable, a.e. bounded, a.e. `Γ`-automorphic function agrees a.e. with a measurable function that is bounded
and `Γ`-automorphic at every point of `𝔻*` (restriction to the co-null `Γ`-invariant set where it is). -/
theorem s19c_inv_modify {Γ : Subgroup SL2C} (hΓ : IsFuchsian Γ) {φ : ℂ → ℝ} (hφm : Measurable φ) {C : ℝ}
    (hC : ∀ᵐ z ∂(volume.restrict unitDiscExterior), |φ z| ≤ C)
    (hinv : ∀ γ ∈ Γ, ∀ᵐ z ∂(volume.restrict unitDiscExterior), φ (mob γ z) = φ z) :
    ∃ ψ : ℂ → ℝ, Measurable ψ ∧ ψ =ᵐ[volume.restrict unitDiscExterior] φ ∧
      (∀ z ∈ unitDiscExterior, |ψ z| ≤ max C 0) ∧ ∀ γ ∈ Γ, ∀ z ∈ unitDiscExterior, ψ (mob γ z) = ψ z := by
  haveI : DiscreteTopology Γ := hΓ.2
  haveI : Countable Γ := (fd_countable (Γ := Γ)).to_subtype
  have hext : MeasurableSet unitDiscExterior := (isOpen_lt continuous_const continuous_norm).measurableSet
  set E : Set ℂ := unitDiscExterior ∩ ⋂ γ : Γ, {z | (γ : SL2C) 1 0 * z + (γ : SL2C) 1 1 ≠ 0 ∧
    φ (mob γ z) = φ z ∧ |φ (mob γ z)| ≤ C} with hE
  have hEm : MeasurableSet E := by
    refine hext.inter (MeasurableSet.iInter fun γ => ?_)
    have hm1 : Measurable fun z => φ (mob (γ : SL2C) z) := hφm.comp (fd_measurable_mob _)
    exact (fd_measurableSet_gen _).inter ((measurableSet_eq_fun hm1 hφm).inter
      (measurableSet_le (continuous_abs.measurable.comp hm1) measurable_const))
  have hEae : ∀ᵐ z ∂(volume.restrict unitDiscExterior), z ∈ E := by
    have hall : ∀ γ : Γ, ∀ᵐ z ∂(volume.restrict unitDiscExterior), (γ : SL2C) 1 0 * z + (γ : SL2C) 1 1 ≠ 0 ∧
        φ (mob γ z) = φ z ∧ |φ (mob γ z)| ≤ C := by
      intro γ
      have hb : ∀ᵐ z ∂volume, z ∈ unitDiscExterior → |φ z| ≤ C := (ae_restrict_iff' hext).mp hC
      have hb' := qf_mob_ae_pullback (γ : SL2C) hb
      filter_upwards [ae_restrict_of_ae (s19m_pole_ae (γ : SL2C)), hinv γ γ.2, ae_restrict_of_ae hb',
        ae_restrict_mem hext] with z hD hi hbz hz
      exact ⟨hD, hi, hbz (fd_mob_exterior (hΓ.1 γ γ.2) hz hD)⟩
    filter_upwards [ae_all_iff.mpr hall, ae_restrict_mem hext] with z hz hz'
    exact ⟨hz', mem_iInter.mpr hz⟩
  have hfwd : ∀ z ∈ E, ∀ γ ∈ Γ, mob γ z ∈ E := by
    intro z hz γ hγ
    have hz1 : z ∈ unitDiscExterior := hz.1
    have hzI := mem_iInter.mp hz.2
    obtain ⟨hD, hi0, -⟩ := hzI ⟨γ, hγ⟩
    refine ⟨fd_mob_exterior (hΓ.1 γ hγ) hz1 hD, mem_iInter.mpr fun γ' => ?_⟩
    obtain ⟨hD', hi', hb'⟩ := hzI ⟨(γ' : SL2C) * γ, mul_mem γ'.2 hγ⟩
    have hden := s19c_denom_mul (γ' : SL2C) γ hD
    have hD'' : (γ' : SL2C) 1 0 * mob γ z + (γ' : SL2C) 1 1 ≠ 0 := by
      intro h0
      apply hD'
      show ((γ' : SL2C) * γ : SL2C) 1 0 * z + ((γ' : SL2C) * γ : SL2C) 1 1 = 0
      rw [hden, h0, zero_mul]
    have hmul := (fd_mob_mul hD hD'').2
    refine ⟨hD'', ?_, ?_⟩
    · show φ (mob (γ' : SL2C) (mob γ z)) = φ (mob γ z)
      rw [← hmul]
      exact hi'.trans hi0.symm
    · show |φ (mob (γ' : SL2C) (mob γ z))| ≤ C
      rw [← hmul]
      exact hb'
  have hiff : ∀ z ∈ unitDiscExterior, ∀ γ ∈ Γ, (mob γ z ∈ E ↔ z ∈ E) := by
    intro z hz γ hγ
    refine ⟨fun h => ?_, fun h => hfwd z h γ hγ⟩
    by_cases hD : γ 1 0 * z + γ 1 1 = 0
    · exfalso
      have h0 : mob γ z = 0 := by
        unfold mob
        rw [hD, div_zero]
      have h1 : 1 < ‖mob γ z‖ := h.1
      rw [h0, norm_zero] at h1
      linarith
    · have hst := fd_inv_step γ hD
      rw [← hst.2]
      exact hfwd _ h γ⁻¹ (inv_mem hγ)
  have hmob1 : ∀ z, mob (1 : SL2C) z = z := fun z => by
    unfold mob
    simp
  refine ⟨E.indicator φ, hφm.indicator hEm, ?_, ?_, ?_⟩
  · filter_upwards [hEae] with z hz
    exact indicator_of_mem hz φ
  · intro z _
    by_cases h : z ∈ E
    · rw [indicator_of_mem h]
      have hb := (mem_iInter.mp h.2 ⟨1, one_mem _⟩).2.2
      simp only [OneMemClass.coe_one, hmob1] at hb
      exact hb.trans (le_max_left _ _)
    · rw [indicator_of_notMem h, abs_zero]
      exact le_max_right _ _
  · intro γ hγ z hz
    by_cases h : z ∈ E
    · rw [indicator_of_mem h, indicator_of_mem ((hiff z hz γ hγ).mpr h)]
      exact (mem_iInter.mp h.2 ⟨γ, hγ⟩).2.1
    · rw [indicator_of_notMem h, indicator_of_notMem fun h' => h ((hiff z hz γ hγ).mp h')]

/-- For a.e. `z ∈ 𝔻*` exactly one action `a ∈ Γ/±1` maps `z` into the fundamental domain. -/
theorem s19c_unique_tile {Γ : Subgroup SL2C} (hΓ : IsFuchsian Γ) :
    ∀ᵐ z ∂(volume.restrict unitDiscExterior), ∃! a : (fun g : SL2C => mob g) '' (Γ : Set SL2C),
      (a : ℂ → ℂ) z ∈ fundDomain Γ := by
  haveI : DiscreteTopology Γ := hΓ.2
  set A := (fun g : SL2C => mob g) '' (Γ : Set SL2C) with hAdef
  haveI : Countable A := (fd_countable (Γ := Γ)).image _ |>.to_subtype
  have hFD := isFundDomain_fundDomain hΓ
  have hpair : ∀ᵐ z ∂(volume.restrict unitDiscExterior), ∀ p : A × A,
      p.1 ≠ p.2 → ¬ ((p.1 : ℂ → ℂ) z ∈ fundDomain Γ ∧ (p.2 : ℂ → ℂ) z ∈ fundDomain Γ) := by
    refine ae_all_iff.mpr fun p => ?_
    obtain ⟨g, hg, hga⟩ := p.1.2
    obtain ⟨h, hh, hha⟩ := p.2.2
    have hga : mob g = (p.1 : ℂ → ℂ) := hga
    have hha : mob h = (p.2 : ℂ → ℂ) := hha
    by_cases hp : p.1 = p.2
    · exact Eventually.of_forall fun z hne => absurd hp hne
    · have hne : mob g ≠ mob h := by
        intro e
        apply hp
        exact Subtype.ext (hga.symm.trans (e.trans hha))
      have hnull := hFD.2.2.2 g hg h hh hne
      have hae : ∀ᵐ z ∂volume, z ∉ mob g ⁻¹' fundDomain Γ ∩ mob h ⁻¹' fundDomain Γ ∩ unitDiscExterior :=
        measure_eq_zero_iff_ae_notMem.mp hnull
      filter_upwards [ae_restrict_of_ae hae, ae_restrict_mem (isOpen_lt continuous_const continuous_norm).measurableSet]
        with z hz hz1 _ hboth
      apply hz
      refine ⟨⟨?_, ?_⟩, hz1⟩
      · show mob g z ∈ fundDomain Γ
        rw [hga]
        exact hboth.1
      · show mob h z ∈ fundDomain Γ
        rw [hha]
        exact hboth.2
  filter_upwards [hFD.2.2.1, hpair] with z hex huniq
  obtain ⟨g, hg, hgz⟩ := hex
  refine ⟨⟨mob g, g, hg, rfl⟩, hgz, fun b hb => ?_⟩
  by_contra hne
  exact huniq (b, ⟨mob g, g, hg, rfl⟩) hne ⟨hb, hgz⟩

/-- Periodization of a bounded nonnegative function from the fundamental domain: a measurable, a.e. bounded, a.e.
automorphic function equal to `h` a.e. on `F`. -/
theorem s19c_periodize {Γ : Subgroup SL2C} (hΓ : IsFuchsian Γ) {h : ℂ → ℝ} (hhm : Measurable h)
    (hh0 : ∀ z, 0 ≤ h z) {n : ℝ} (hhn : ∀ z, h z ≤ n) :
    ∃ ψ : ℂ → ℝ, Measurable ψ ∧ (∀ᵐ z ∂(volume.restrict unitDiscExterior), |ψ z| ≤ n) ∧
      (∀ γ ∈ Γ, ∀ᵐ z ∂(volume.restrict unitDiscExterior), ψ (mob γ z) = ψ z) ∧
      ψ =ᵐ[volume.restrict (fundDomain Γ)] h := by
  haveI : DiscreteTopology Γ := hΓ.2
  set A := (fun g : SL2C => mob g) '' (Γ : Set SL2C) with hAdef
  haveI : Countable A := (fd_countable (Γ := Γ)).image _ |>.to_subtype
  have hext : MeasurableSet unitDiscExterior := (isOpen_lt continuous_const continuous_norm).measurableSet
  have hFm := fundDomain_measurable Γ
  have hFe := fundDomain_subset Γ
  have hAm : ∀ a : A, Measurable (a : ℂ → ℂ) := fun a => by
    obtain ⟨g, -, hg⟩ := a.2
    rw [← hg]
    exact fd_measurable_mob g
  set ψ : ℂ → ℝ := fun z => (∑' a : A, ENNReal.ofReal ((fundDomain Γ).indicator h ((a : ℂ → ℂ) z))).toReal
    with hψdef
  have hψm : Measurable ψ :=
    ENNReal.measurable_toReal.comp (Measurable.ennreal_tsum fun a =>
      ENNReal.measurable_ofReal.comp ((hhm.indicator hFm).comp (hAm a)))
  -- the value at a point with a unique tile
  have hval : ∀ z (a₀ : A), (a₀ : ℂ → ℂ) z ∈ fundDomain Γ →
      (∀ b : A, (b : ℂ → ℂ) z ∈ fundDomain Γ → b = a₀) → ψ z = h ((a₀ : ℂ → ℂ) z) := by
    intro z a₀ ha₀ huniq
    rw [hψdef]
    simp only
    rw [tsum_eq_single a₀ fun b hb => by
      rw [indicator_of_notMem fun hbF => hb (huniq b hbF), ENNReal.ofReal_zero],
      indicator_of_mem ha₀, ENNReal.toReal_ofReal (hh0 _)]
  have hU := s19c_unique_tile hΓ
  refine ⟨ψ, hψm, ?_, ?_, ?_⟩
  · filter_upwards [hU] with z hz
    obtain ⟨a₀, ha₀, huniq⟩ := hz
    rw [hval z a₀ ha₀ huniq, abs_of_nonneg (hh0 _)]
    exact hhn _
  · intro γ hγ
    have hU' : ∀ᵐ z ∂volume, z ∈ unitDiscExterior → ∃! a : A, (a : ℂ → ℂ) z ∈ fundDomain Γ :=
      (ae_restrict_iff' hext).mp hU
    filter_upwards [hU, ae_restrict_of_ae (qf_mob_ae_pullback γ hU'), ae_restrict_of_ae (s19m_pole_ae γ),
      ae_restrict_mem hext] with z hz hzγ hD hz1
    obtain ⟨a₀, ha₀, huniq⟩ := hz
    have hγz : mob γ z ∈ unitDiscExterior := fd_mob_exterior (hΓ.1 γ hγ) hz1 hD
    obtain ⟨a₁, ha₁, huniq₁⟩ := hzγ hγz
    obtain ⟨g₁, hg₁, hga₁⟩ := a₁.2
    have hga₁ : mob g₁ = (a₁ : ℂ → ℂ) := hga₁
    have hD₁ : g₁ 1 0 * mob γ z + g₁ 1 1 ≠ 0 := by
      intro h0
      have : mob g₁ (mob γ z) = 0 := by
        have e : mob g₁ (mob γ z) = (g₁ 0 0 * mob γ z + g₁ 0 1) / (g₁ 1 0 * mob γ z + g₁ 1 1) := rfl
        rw [e, h0, div_zero]
      have hin : mob g₁ (mob γ z) ∈ fundDomain Γ := by rw [hga₁]; exact ha₁
      rw [this] at hin
      have h1 : 1 < ‖(0 : ℂ)‖ := hFe hin
      rw [norm_zero] at h1
      linarith
    have hmul := (fd_mob_mul hD hD₁).2
    set b : A := ⟨mob (g₁ * γ), g₁ * γ, mul_mem hg₁ hγ, rfl⟩ with hbdef
    have hbz : (b : ℂ → ℂ) z = (a₁ : ℂ → ℂ) (mob γ z) := by
      show mob (g₁ * γ) z = _
      rw [hmul, hga₁]
    have hb : b = a₀ := huniq b (by show (b : ℂ → ℂ) z ∈ fundDomain Γ; rw [hbz]; exact ha₁)
    rw [hval z a₀ ha₀ huniq, hval (mob γ z) a₁ ha₁ huniq₁, ← hbz, hb]
  · have hUF : ∀ᵐ z ∂(volume.restrict (fundDomain Γ)), ∃! a : A, (a : ℂ → ℂ) z ∈ fundDomain Γ :=
      ae_restrict_of_ae_restrict_of_subset hFe hU
    filter_upwards [hUF, ae_restrict_mem hFm] with z hz hzF
    obtain ⟨a₀, ha₀, huniq⟩ := hz
    have hid : (⟨mob 1, 1, one_mem _, rfl⟩ : A) = a₀ := huniq _ (by
      show mob 1 z ∈ fundDomain Γ
      unfold mob
      simpa using hzF)
    rw [hval z a₀ ha₀ huniq, ← hid]
    show h (mob 1 z) = h z
    unfold mob
    simp

/-- Real ball integrals of a measurable function are measurable in the centre. -/
theorem s19c_ball_measurable_real {k : ℂ → ℝ} (hk : Measurable k) (s : ℝ) :
    Measurable fun z => ∫ w in {w | w ∈ unitDiscExterior ∧ ‖w - z‖ ≤ s * ‖w * conj z - 1‖}, k w * rho w := by
  have hext : MeasurableSet unitDiscExterior := (isOpen_lt continuous_const continuous_norm).measurableSet
  set E : Set (ℂ × ℂ) := {p | p.2 ∈ unitDiscExterior ∧ ‖p.2 - p.1‖ ≤ s * ‖p.2 * conj p.1 - 1‖} with hEdef
  have hE : MeasurableSet E :=
    (hext.preimage measurable_snd).inter (measurableSet_le
      (continuous_norm.comp (continuous_snd.sub continuous_fst)).measurable
      (continuous_const.mul (continuous_norm.comp ((continuous_snd.mul
        (Complex.continuous_conj.comp continuous_fst)).sub continuous_const))).measurable)
  have hg : Measurable fun p : ℂ × ℂ => k p.2 * rho p.2 :=
    (hk.comp measurable_snd).mul (s19m_rho_measurable.comp measurable_snd)
  have hsm := StronglyMeasurable.integral_prod_right (ν := volume)
    (f := fun z w => E.indicator (fun p : ℂ × ℂ => k p.2 * rho p.2) (z, w))
    (hg.indicator hE).stronglyMeasurable
  have heq : (fun z => ∫ w, E.indicator (fun p : ℂ × ℂ => k p.2 * rho p.2) (z, w)) =
      fun z => ∫ w in {w | w ∈ unitDiscExterior ∧ ‖w - z‖ ≤ s * ‖w * conj z - 1‖}, k w * rho w := by
    funext z
    rw [← integral_indicator (s19m_ball_measurable z s)]
    rfl
  rw [← heq]
  exact hsm.measurable

/-- `|∬_{B(z,s)} f ρ| ≤ C A_s` for `|f| ≤ C` on `𝔻*`. -/
theorem s19c_ball_bound_real {f : ℂ → ℝ} {C : ℝ} (hC : ∀ w ∈ unitDiscExterior, |f w| ≤ C)
    {z : ℂ} (hz : z ∈ unitDiscExterior) {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) :
    |∫ w in {w | w ∈ unitDiscExterior ∧ ‖w - z‖ ≤ s * ‖w * conj z - 1‖}, f w * rho w| ≤
      C * (4 * π * s ^ 2 / (1 - s ^ 2)) := by
  obtain ⟨hi, he⟩ := s19m_rho_ball hz hs0 hs1
  rw [← Real.norm_eq_abs]
  refine (norm_integral_le_of_norm_le (hi.const_mul C) ?_).trans_eq ?_
  · filter_upwards [ae_restrict_mem (s19m_ball_measurable z s)] with w hw
    have hρ0 : 0 ≤ rho w := div_nonneg (by norm_num) (sq_nonneg _)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hρ0]
    exact mul_le_mul_of_nonneg_right (hC w hw.1) hρ0
  · rw [integral_const_mul, he]

/-- An everywhere bounded, everywhere automorphic version of any bounded measurable function on `F`. -/
theorem s19c_lift_bounded {Γ : Subgroup SL2C} (hΓ : IsFuchsian Γ) {h : ℂ → ℝ} (hhm : Measurable h) {n : ℝ}
    (hn : 0 ≤ n) (hhn : ∀ z, |h z| ≤ n) :
    ∃ G : ℂ → ℝ, Measurable G ∧ (∀ z ∈ unitDiscExterior, |G z| ≤ 2 * n) ∧
      (∀ γ ∈ Γ, ∀ z ∈ unitDiscExterior, G (mob γ z) = G z) ∧ G =ᵐ[volume.restrict (fundDomain Γ)] h := by
  have hFe := fundDomain_subset Γ
  obtain ⟨ψp, hψpm, hψpb, hψpa, hψpF⟩ := s19c_periodize hΓ (h := fun z => max (h z) 0)
    (hhm.max measurable_const) (fun z => le_max_right _ _) (n := n)
    (fun z => max_le ((le_abs_self _).trans (hhn z)) hn)
  obtain ⟨ψq, hψqm, hψqb, hψqa, hψqF⟩ := s19c_periodize hΓ (h := fun z => max (-h z) 0)
    (hhm.neg.max measurable_const) (fun z => le_max_right _ _) (n := n)
    (fun z => max_le ((neg_le_abs _).trans (hhn z)) hn)
  obtain ⟨P, hPm, hPe, hPb, hPa⟩ := s19c_inv_modify hΓ hψpm hψpb hψpa
  obtain ⟨Q, hQm, hQe, hQb, hQa⟩ := s19c_inv_modify hΓ hψqm hψqb hψqa
  refine ⟨fun z => P z - Q z, hPm.sub hQm, fun z hz => ?_, fun γ hγ z hz => ?_, ?_⟩
  · have h1 := hPb z hz
    have h2 := hQb z hz
    rw [max_eq_left hn] at h1 h2
    calc |P z - Q z| ≤ |P z| + |Q z| := abs_sub _ _
      _ ≤ 2 * n := by linarith
  · show P (mob γ z) - Q (mob γ z) = P z - Q z
    rw [hPa γ hγ z hz, hQa γ hγ z hz]
  · have hPF := ae_restrict_of_ae_restrict_of_subset hFe hPe
    have hQF := ae_restrict_of_ae_restrict_of_subset hFe hQe
    filter_upwards [hPF, hQF, hψpF, hψqF] with z h1 h2 h3 h4
    show P z - Q z = h z
    rw [h1, h2, h3, h4]
    rcases le_total (h z) 0 with hle | hle
    · rw [max_eq_right hle, max_eq_left (by linarith)]
      ring
    · rw [max_eq_left hle, max_eq_right (by linarith)]
      ring

/-- **C0, real case.** CORE for bounded automorphic real `f` and any real `g` with `g ρ ∈ L¹(F)`. -/
theorem s19c_core_real {Γ : Subgroup SL2C} (hΓ : IsCofinite Γ)
    (hinv : ∀ f g : ℂ → ℝ, Measurable f → Measurable g →
      (∃ C, ∀ z ∈ unitDiscExterior, |f z| ≤ C) → (∃ C, ∀ z ∈ unitDiscExterior, |g z| ≤ C) →
      (∀ γ ∈ Γ, ∀ z ∈ unitDiscExterior, f (mob γ z) = f z) →
      (∀ γ ∈ Γ, ∀ z ∈ unitDiscExterior, g (mob γ z) = g z) →
      Tendsto (fun s : ℝ => ∫ z in fundDomain Γ,
          (∫ w in {w | w ∈ unitDiscExterior ∧ ‖w - z‖ ≤ s * ‖w * conj z - 1‖}, f w * rho w) /
            (4 * π * s ^ 2 / (1 - s ^ 2)) * g z * rho z)
        (𝓝[<] 1)
        (𝓝 ((∫ z in fundDomain Γ, f z * rho z) * (∫ z in fundDomain Γ, g z * rho z) / (hypArea Γ).toReal)))
    {f : ℂ → ℝ} (hfm : Measurable f) {Cf : ℝ} (hCf : ∀ z ∈ unitDiscExterior, |f z| ≤ Cf)
    (hfa : ∀ γ ∈ Γ, ∀ z ∈ unitDiscExterior, f (mob γ z) = f z) {g : ℂ → ℝ}
    (hgi : IntegrableOn (fun z => g z * rho z) (fundDomain Γ)) :
    Tendsto (fun s : ℝ => ∫ z in fundDomain Γ,
        (∫ w in {w | w ∈ unitDiscExterior ∧ ‖w - z‖ ≤ s * ‖w * conj z - 1‖}, f w * rho w) /
          (4 * π * s ^ 2 / (1 - s ^ 2)) * g z * rho z)
      (𝓝[<] 1)
      (𝓝 ((∫ z in fundDomain Γ, f z * rho z) * (∫ z in fundDomain Γ, g z * rho z) / (hypArea Γ).toReal)) := by
  have hFm := fundDomain_measurable Γ
  have hFe := fundDomain_subset Γ
  have hρF : IntegrableOn rho (fundDomain Γ) := rho_integrableOn_fundDomain hΓ
  have hA : 0 < (hypArea Γ).toReal := pat_hypArea_toReal_pos hΓ
  have hCf0 : 0 ≤ max Cf 0 := le_max_right _ _
  have hCf' : ∀ z ∈ unitDiscExterior, |f z| ≤ max Cf 0 := fun z hz => (hCf z hz).trans (le_max_left _ _)
  have hρpos : ∀ z ∈ unitDiscExterior, 0 < rho z := fun z hz => by
    have : (1 : ℝ) < ‖z‖ := hz
    unfold rho
    have hne : 1 - ‖z‖ ^ 2 ≠ 0 := by nlinarith
    exact div_pos (by norm_num) (by positivity)
  -- a measurable version of `g`
  set gm : ℂ → ℝ := fun z => hgi.1.mk _ z / rho z with hgmdef
  have hgmm : Measurable gm := hgi.1.stronglyMeasurable_mk.measurable.div s19m_rho_measurable
  have hgae : ∀ᵐ z ∂(volume.restrict (fundDomain Γ)), gm z = g z := by
    filter_upwards [hgi.1.ae_eq_mk, ae_restrict_mem hFm] with z hz hzF
    rw [hgmdef]
    simp only
    rw [← hz]
    field_simp [(hρpos z (hFe hzF)).ne']
  have hgmi : IntegrableOn (fun z => gm z * rho z) (fundDomain Γ) :=
    hgi.congr_fun_ae (by filter_upwards [hgae] with z hz; rw [hz])
  -- the pairing and the limit for an arbitrary integrable weight
  set M : ℝ → ℂ → ℝ := fun s z => (∫ w in {w | w ∈ unitDiscExterior ∧ ‖w - z‖ ≤ s * ‖w * conj z - 1‖},
    f w * rho w) / (4 * π * s ^ 2 / (1 - s ^ 2)) with hMdef
  have hMb : ∀ s ∈ Ioo (0 : ℝ) 1, ∀ z ∈ unitDiscExterior, |M s z| ≤ max Cf 0 := by
    intro s hs z hz
    have hAs : 0 < 4 * π * s ^ 2 / (1 - s ^ 2) := div_pos (by have := hs.1; positivity) (by nlinarith [hs.1, hs.2])
    rw [hMdef]
    simp only
    rw [abs_div, abs_of_pos hAs, div_le_iff₀ hAs]
    exact s19c_ball_bound_real hCf' hz hs.1 hs.2
  have hMm : ∀ s, Measurable (M s) := fun s => (s19c_ball_measurable_real hfm s).div_const _
  -- replace `g` by `gm`
  have hQg : ∀ s, (∫ z in fundDomain Γ, M s z * g z * rho z) = ∫ z in fundDomain Γ, M s z * gm z * rho z := by
    intro s
    refine setIntegral_congr_ae hFm ?_
    filter_upwards [(ae_restrict_iff' hFm).mp hgae] with z hz hzF
    rw [hz hzF]
  have hLg : (∫ z in fundDomain Γ, g z * rho z) = ∫ z in fundDomain Γ, gm z * rho z := by
    refine setIntegral_congr_ae hFm ?_
    filter_upwards [(ae_restrict_iff' hFm).mp hgae] with z hz hzF
    rw [hz hzF]
  show Tendsto (fun s => ∫ z in fundDomain Γ, M s z * g z * rho z) _ _
  simp only [hQg, hLg]
  -- truncations of `gm`
  set t : ℕ → ℂ → ℝ := fun n z => max (min (gm z) n) (-n) with htdef
  have htm : ∀ n, Measurable (t n) := fun n => (hgmm.min measurable_const).max measurable_const
  have htb : ∀ n : ℕ, ∀ z, |t n z| ≤ n := fun n z => by
    rw [htdef, abs_le]
    constructor
    · exact le_max_right _ _
    · exact max_le (min_le_right _ _) (by have : (0 : ℝ) ≤ n := Nat.cast_nonneg n; linarith)
  have htle : ∀ n z, |gm z - t n z| ≤ |gm z| := fun n z => by
    simp only [htdef]
    rcases le_total (gm z) n with h1 | h1 <;> rcases le_total (gm z) (-n) with h2 | h2
    · rw [min_eq_left h1, max_eq_right h2]
      have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      rw [abs_le]
      constructor <;> cases abs_cases (gm z) <;> linarith
    · rw [min_eq_left h1, max_eq_left h2, sub_self, abs_zero]
      exact abs_nonneg _
    · rw [min_eq_right h1, max_eq_right (by linarith)]
      have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      rw [abs_le]
      constructor <;> cases abs_cases (gm z) <;> linarith
    · rw [min_eq_right h1, max_eq_left (by have : (0 : ℝ) ≤ n := Nat.cast_nonneg n; linarith)]
      rw [abs_le]
      constructor <;> cases abs_cases (gm z) <;> linarith
  have htlim : ∀ z, Tendsto (fun n : ℕ => |gm z - t n z|) atTop (𝓝 0) := by
    intro z
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop ⌈|gm z|⌉₊] with n hn
    have hn' : |gm z| ≤ n := (Nat.le_ceil _).trans (Nat.cast_le.mpr hn)
    rw [htdef]
    simp only
    rw [min_eq_left ((le_abs_self _).trans hn'), max_eq_left (by linarith [neg_abs_le (gm z)]), sub_self,
      abs_zero]
  -- `δ_n = ∬_F |gm - t_n| ρ → 0`
  have hδ : Tendsto (fun n : ℕ => ∫ z in fundDomain Γ, |gm z - t n z| * rho z) atTop (𝓝 0) := by
    have := tendsto_integral_of_dominated_convergence (μ := volume.restrict (fundDomain Γ))
      (F := fun (n : ℕ) z => |gm z - t n z| * rho z) (f := fun _ => 0) (bound := fun z => |gm z * rho z|)
      (fun n => ((continuous_abs.measurable.comp (hgmm.sub (htm n))).mul s19m_rho_measurable).aestronglyMeasurable)
      hgmi.norm (fun n => ?_) ?_
    · simpa using this
    · filter_upwards [ae_restrict_mem hFm] with z hz
      have hρ0 := (hρpos z (hFe hz)).le
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hρ0, abs_mul, abs_of_nonneg hρ0, abs_abs]
      exact mul_le_mul_of_nonneg_right (htle n z) hρ0
    · exact Eventually.of_forall fun z => by simpa using (htlim z).mul_const (rho z)
  rw [Metric.tendsto_nhds]
  intro ε hε
  set K := max Cf 0 + |∫ z in fundDomain Γ, f z * rho z| / (hypArea Γ).toReal with hKdef
  have hK : 0 < K + 1 := by positivity
  obtain ⟨n, hn⟩ := ((Metric.tendsto_nhds.mp hδ) (ε / (3 * (K + 1))) (by positivity)).exists
  rw [Real.dist_eq, sub_zero] at hn
  set δ := ∫ z in fundDomain Γ, |gm z - t n z| * rho z with hδdef
  have hδ0 : 0 ≤ δ := setIntegral_nonneg hFm fun z hz => mul_nonneg (abs_nonneg _) (hρpos z (hFe hz)).le
  rw [abs_of_nonneg hδ0] at hn
  -- the lifted truncation
  obtain ⟨G, hGm, hGb, hGa, hGF⟩ := s19c_lift_bounded hΓ.1 (htm n) (Nat.cast_nonneg n) (htb n)
  have hlimG := hinv f G hfm hGm ⟨Cf, hCf⟩ ⟨2 * n, hGb⟩ hfa hGa
  have hGint : (∫ z in fundDomain Γ, G z * rho z) = ∫ z in fundDomain Γ, t n z * rho z := by
    refine setIntegral_congr_ae hFm ?_
    filter_upwards [(ae_restrict_iff' hFm).mp hGF] with z hz hzF
    rw [hz hzF]
  have hevG := (Metric.tendsto_nhds.mp hlimG) (ε / 3) (by positivity)
  filter_upwards [hevG, Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with s hsG hs
  rw [Real.dist_eq] at hsG ⊢
  have hint1 : IntegrableOn (fun z => M s z * gm z * rho z) (fundDomain Γ) := by
    refine Integrable.mono' (hgmi.norm.const_mul (max Cf 0)) ((hMm s).mul hgmm |>.mul s19m_rho_measurable).aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem hFm] with z hz
    have hρ0 := (hρpos z (hFe hz)).le
    rw [Real.norm_eq_abs, Real.norm_eq_abs, mul_assoc, abs_mul, abs_mul (gm z), abs_of_nonneg hρ0]
    exact mul_le_mul_of_nonneg_right (hMb s hs z (hFe hz)) (by positivity)
  have hint2 : IntegrableOn (fun z => M s z * G z * rho z) (fundDomain Γ) := by
    refine Integrable.mono' (hρF.const_mul (max Cf 0 * (2 * n))) ((hMm s).mul hGm |>.mul s19m_rho_measurable).aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem hFm] with z hz
    have hρ0 := (hρpos z (hFe hz)).le
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg hρ0]
    exact mul_le_mul_of_nonneg_right (mul_le_mul (hMb s hs z (hFe hz)) (hGb z (hFe hz)) (abs_nonneg _) hCf0) hρ0
  have hdom : IntegrableOn (fun z => |gm z - t n z| * rho z) (fundDomain Γ) := by
    refine Integrable.mono' hgmi.norm ((continuous_abs.measurable.comp (hgmm.sub (htm n))).mul
      s19m_rho_measurable).aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem hFm] with z hz
    have hρ0 := (hρpos z (hFe hz)).le
    calc ‖|gm z - t n z| * rho z‖ = |gm z - t n z| * rho z := by
          rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (abs_nonneg _) hρ0)]
      _ ≤ |gm z| * rho z := mul_le_mul_of_nonneg_right (htle n z) hρ0
      _ = ‖gm z * rho z‖ := by rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hρ0]
  have hti : IntegrableOn (fun z => t n z * rho z) (fundDomain Γ) := by
    refine Integrable.mono' (hρF.const_mul n) ((htm n).mul s19m_rho_measurable).aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem hFm] with z hz
    have hρ0 := (hρpos z (hFe hz)).le
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hρ0]
    exact mul_le_mul_of_nonneg_right (htb n z) hρ0
  -- `|Q(gm) - Q(G)| ≤ Cf δ`
  have hd1 : |(∫ z in fundDomain Γ, M s z * gm z * rho z) - ∫ z in fundDomain Γ, M s z * G z * rho z| ≤
      max Cf 0 * δ := by
    rw [← integral_sub hint1 hint2, ← Real.norm_eq_abs, hδdef, ← integral_const_mul]
    refine norm_integral_le_of_norm_le (hdom.const_mul _) ?_
    filter_upwards [hGF, ae_restrict_mem hFm] with z hzG hz
    have hρ0 := (hρpos z (hFe hz)).le
    calc ‖M s z * gm z * rho z - M s z * G z * rho z‖ = |M s z| * (|gm z - t n z| * rho z) := by
          rw [hzG, show M s z * gm z * rho z - M s z * t n z * rho z = M s z * ((gm z - t n z) * rho z) by ring,
            Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg hρ0]
      _ ≤ max Cf 0 * (|gm z - t n z| * rho z) :=
          mul_le_mul_of_nonneg_right (hMb s hs z (hFe hz)) (mul_nonneg (abs_nonneg _) hρ0)
  -- `|L(gm) - L(G)| ≤ |∬ f ρ|/A δ`
  have hd2 : |(∫ z in fundDomain Γ, f z * rho z) * (∫ z in fundDomain Γ, gm z * rho z) / (hypArea Γ).toReal -
      (∫ z in fundDomain Γ, f z * rho z) * (∫ z in fundDomain Γ, G z * rho z) / (hypArea Γ).toReal| ≤
      |∫ z in fundDomain Γ, f z * rho z| / (hypArea Γ).toReal * δ := by
    rw [hGint, show ∀ a b c A : ℝ, a * b / A - a * c / A = a * (b - c) / A from fun a b c A => by ring,
      abs_div, abs_mul, abs_of_pos hA, ← integral_sub hgmi hti]
    have hle : |∫ z in fundDomain Γ, gm z * rho z - t n z * rho z| ≤ δ := by
      rw [← Real.norm_eq_abs, hδdef]
      refine norm_integral_le_of_norm_le hdom ?_
      filter_upwards [ae_restrict_mem hFm] with z hz
      have hρ0 := (hρpos z (hFe hz)).le
      rw [← sub_mul, Real.norm_eq_abs, abs_mul, abs_of_nonneg hρ0]
    calc |∫ z in fundDomain Γ, f z * rho z| * |∫ z in fundDomain Γ, gm z * rho z - t n z * rho z| /
          (hypArea Γ).toReal ≤ |∫ z in fundDomain Γ, f z * rho z| * δ / (hypArea Γ).toReal := by
          gcongr
      _ = _ := by ring
  have hKδ : K * δ < ε / 3 := by
    have h1 : K * δ ≤ (K + 1) * δ := by nlinarith
    have h2 : (K + 1) * δ < (K + 1) * (ε / (3 * (K + 1))) := mul_lt_mul_of_pos_left hn hK
    have h3 : (K + 1) * (ε / (3 * (K + 1))) = ε / 3 := by field_simp
    linarith
  have hsplit : (∫ z in fundDomain Γ, M s z * gm z * rho z) -
      (∫ z in fundDomain Γ, f z * rho z) * (∫ z in fundDomain Γ, gm z * rho z) / (hypArea Γ).toReal =
      ((∫ z in fundDomain Γ, M s z * gm z * rho z) - ∫ z in fundDomain Γ, M s z * G z * rho z) +
      ((∫ z in fundDomain Γ, M s z * G z * rho z) -
        (∫ z in fundDomain Γ, f z * rho z) * (∫ z in fundDomain Γ, G z * rho z) / (hypArea Γ).toReal) +
      ((∫ z in fundDomain Γ, f z * rho z) * (∫ z in fundDomain Γ, G z * rho z) / (hypArea Γ).toReal -
        (∫ z in fundDomain Γ, f z * rho z) * (∫ z in fundDomain Γ, gm z * rho z) / (hypArea Γ).toReal) := by
    ring
  rw [hsplit]
  have hd2' := hd2
  rw [abs_sub_comm] at hd2'
  have hsG' : |(∫ z in fundDomain Γ, M s z * G z * rho z) -
      (∫ z in fundDomain Γ, f z * rho z) * (∫ z in fundDomain Γ, G z * rho z) / (hypArea Γ).toReal| < ε / 3 :=
    hsG
  refine lt_of_le_of_lt (abs_add_three _ _ _) ?_
  have hK' : max Cf 0 * δ + |∫ z in fundDomain Γ, f z * rho z| / (hypArea Γ).toReal * δ = K * δ := by
    rw [hKdef]
    ring
  linarith

/-- A bounded measurable real function times `ρ` is integrable on the fundamental domain. -/
theorem s19c_bdd_F {Γ : Subgroup SL2C} (hΓ : IsCofinite Γ) {φ : ℂ → ℝ} (hφm : Measurable φ) {C : ℝ}
    (hC : ∀ z ∈ unitDiscExterior, |φ z| ≤ C) : IntegrableOn (fun z => φ z * rho z) (fundDomain Γ) := by
  have hFe := fundDomain_subset Γ
  refine Integrable.mono' ((rho_integrableOn_fundDomain hΓ).const_mul C)
    (hφm.mul s19m_rho_measurable).aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem (fundDomain_measurable Γ)] with z hz
  have hρ0 : 0 ≤ rho z := div_nonneg (by norm_num) (sq_nonneg _)
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hρ0]
  exact mul_le_mul_of_nonneg_right (hC z (hFe hz)) hρ0

/-- `∫ (↑a + ↑b I) ↑ρ = ↑∫ a ρ + ↑∫ b ρ I` over a set where `a ρ`, `b ρ` are integrable. -/
theorem s19c_split {S : Set ℂ} {a b : ℂ → ℝ} (ha : IntegrableOn (fun z => a z * rho z) S)
    (hb : IntegrableOn (fun z => b z * rho z) S) :
    (∫ z in S, ((a z : ℂ) + (b z : ℂ) * I) * rho z) =
      ((∫ z in S, a z * rho z : ℝ) : ℂ) + ((∫ z in S, b z * rho z : ℝ) : ℂ) * I := by
  have e : (fun z => ((a z : ℂ) + (b z : ℂ) * I) * rho z) =
      fun z => ((a z * rho z : ℝ) : ℂ) + ((b z * rho z : ℝ) : ℂ) * I := by
    funext z
    push_cast
    ring
  have h1 : Integrable (fun z => ((a z * rho z : ℝ) : ℂ)) (volume.restrict S) := ha.ofReal
  have h2 : Integrable (fun z => ((b z * rho z : ℝ) : ℂ) * I) (volume.restrict S) := hb.ofReal.mul_const I
  rw [e, integral_add h1 h2, integral_mul_const,
    integral_complex_ofReal,
    integral_complex_ofReal]

/-- **C0.** The real, bounded, everywhere-automorphic case implies the frozen CORE statement. -/
theorem s19c_core_of_inv {Γ : Subgroup SL2C} (hΓ : IsCofinite Γ)
    (hinv : ∀ f g : ℂ → ℝ, Measurable f → Measurable g →
      (∃ C, ∀ z ∈ unitDiscExterior, |f z| ≤ C) → (∃ C, ∀ z ∈ unitDiscExterior, |g z| ≤ C) →
      (∀ γ ∈ Γ, ∀ z ∈ unitDiscExterior, f (mob γ z) = f z) →
      (∀ γ ∈ Γ, ∀ z ∈ unitDiscExterior, g (mob γ z) = g z) →
      Tendsto (fun s : ℝ => ∫ z in fundDomain Γ,
          (∫ w in {w | w ∈ unitDiscExterior ∧ ‖w - z‖ ≤ s * ‖w * conj z - 1‖}, f w * rho w) /
            (4 * π * s ^ 2 / (1 - s ^ 2)) * g z * rho z)
        (𝓝[<] 1)
        (𝓝 ((∫ z in fundDomain Γ, f z * rho z) * (∫ z in fundDomain Γ, g z * rho z) / (hypArea Γ).toReal))) :
    ∀ f g : ℂ → ℂ, AEStronglyMeasurable f (volume.restrict unitDiscExterior) →
      (∃ C, ∀ᵐ z ∂(volume.restrict unitDiscExterior), ‖f z‖ ≤ C) →
      (∀ γ ∈ Γ, ∀ᵐ z ∂(volume.restrict unitDiscExterior), f (mob γ z) = f z) →
      IntegrableOn (fun z => g z * rho z) (fundDomain Γ) →
      Tendsto (fun s : ℝ => ∫ z in fundDomain Γ,
          ((∫ w in {w | w ∈ unitDiscExterior ∧ ‖w - z‖ ≤ s * ‖w * conj z - 1‖}, f w * rho w) /
            ((4 * π * s ^ 2 / (1 - s ^ 2) : ℝ) : ℂ)) * g z * rho z)
        (𝓝[<] 1)
        (𝓝 ((∫ z in fundDomain Γ, f z * rho z) * (∫ z in fundDomain Γ, g z * rho z) /
          ((hypArea Γ).toReal : ℂ))) := by
  intro f g hfm hfb hfa hgi
  have hext : MeasurableSet unitDiscExterior := (isOpen_lt continuous_const continuous_norm).measurableSet
  have hFm := fundDomain_measurable Γ
  have hFe := fundDomain_subset Γ
  obtain ⟨k, hkm, hke, hka⟩ := pat_measurable_automorphic_representative hΓ.1 hfm hfa
  obtain ⟨C, hC⟩ := hfb
  have hkb : ∀ᵐ z ∂(volume.restrict unitDiscExterior), ‖k z‖ ≤ C := by
    filter_upwards [hke, hC] with z h1 h2
    rw [h1]
    exact h2
  -- real and imaginary parts, made everywhere automorphic
  obtain ⟨Fr, hFrm, hFre, hFrb, hFra⟩ := s19c_inv_modify hΓ.1 (Complex.measurable_re.comp hkm) (C := C)
    (by filter_upwards [hkb] with z hz; exact (Complex.abs_re_le_norm _).trans hz)
    (fun γ hγ => by filter_upwards [hka γ hγ] with z hz; simp only [Function.comp, hz])
  obtain ⟨Fi, hFim, hFie, hFib, hFia⟩ := s19c_inv_modify hΓ.1 (Complex.measurable_im.comp hkm) (C := C)
    (by filter_upwards [hkb] with z hz; exact (Complex.abs_im_le_norm _).trans hz)
    (fun γ hγ => by filter_upwards [hka γ hγ] with z hz; simp only [Function.comp, hz])
  have hfeq : ∀ᵐ z ∂(volume.restrict unitDiscExterior), f z = (Fr z : ℂ) + (Fi z : ℂ) * I := by
    filter_upwards [hke, hFre, hFie] with z h1 h2 h3
    rw [← h1, h2, h3]
    simp only [Function.comp]
    exact (Complex.re_add_im _).symm
  have hfeq' : ∀ᵐ z ∂volume, z ∈ unitDiscExterior → f z = (Fr z : ℂ) + (Fi z : ℂ) * I :=
    (ae_restrict_iff' hext).mp hfeq
  -- the parts of `g`
  set gr : ℂ → ℝ := fun z => (g z).re with hgrdef
  set gi : ℂ → ℝ := fun z => (g z).im with hgidef
  have hgri : IntegrableOn (fun z => gr z * rho z) (fundDomain Γ) := by
    refine hgi.re.congr_fun (fun z _ => ?_) hFm
    simp only [hgrdef, RCLike.re_to_complex, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero,
      sub_zero]
  have hgii : IntegrableOn (fun z => gi z * rho z) (fundDomain Γ) := by
    refine hgi.im.congr_fun (fun z _ => ?_) hFm
    simp only [hgidef, RCLike.im_to_complex, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero,
      add_zero, zero_add]
  have hgeq : ∀ z, g z = (gr z : ℂ) + (gi z : ℂ) * I := fun z => (Complex.re_add_im _).symm
  -- ball integrals
  have hball : ∀ s ∈ Ioo (0 : ℝ) 1, ∀ z ∈ unitDiscExterior,
      (∫ w in {w | w ∈ unitDiscExterior ∧ ‖w - z‖ ≤ s * ‖w * conj z - 1‖}, f w * rho w) =
        ((∫ w in {w | w ∈ unitDiscExterior ∧ ‖w - z‖ ≤ s * ‖w * conj z - 1‖}, Fr w * rho w : ℝ) : ℂ) +
          ((∫ w in {w | w ∈ unitDiscExterior ∧ ‖w - z‖ ≤ s * ‖w * conj z - 1‖}, Fi w * rho w : ℝ) : ℂ) * I := by
    intro s hs z hz
    have hBsub : {w | w ∈ unitDiscExterior ∧ ‖w - z‖ ≤ s * ‖w * conj z - 1‖} ⊆ unitDiscExterior :=
      fun w hw => hw.1
    have hρB := (s19m_rho_ball hz hs.1 hs.2).1
    have hbi : ∀ φ : ℂ → ℝ, Measurable φ → (∀ w ∈ unitDiscExterior, |φ w| ≤ max C 0) →
        IntegrableOn (fun w => φ w * rho w) {w | w ∈ unitDiscExterior ∧ ‖w - z‖ ≤ s * ‖w * conj z - 1‖} := by
      intro φ hφm hφb
      refine Integrable.mono' (hρB.const_mul (max C 0)) (hφm.mul s19m_rho_measurable).aestronglyMeasurable ?_
      filter_upwards [ae_restrict_mem (s19m_ball_measurable z s)] with w hw
      have hρ0 : 0 ≤ rho w := div_nonneg (by norm_num) (sq_nonneg _)
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hρ0]
      exact mul_le_mul_of_nonneg_right (hφb w hw.1) hρ0
    rw [← s19c_split (hbi Fr hFrm hFrb) (hbi Fi hFim hFib)]
    refine setIntegral_congr_ae (s19m_ball_measurable z s) ?_
    filter_upwards [hfeq'] with w hw hwB
    rw [hw hwB.1]
  -- quotient integrals
  have hFrF := s19c_bdd_F hΓ hFrm hFrb
  have hFiF := s19c_bdd_F hΓ hFim hFib
  have hfF : (∫ z in fundDomain Γ, f z * rho z) =
      ((∫ z in fundDomain Γ, Fr z * rho z : ℝ) : ℂ) + ((∫ z in fundDomain Γ, Fi z * rho z : ℝ) : ℂ) * I := by
    rw [← s19c_split hFrF hFiF]
    refine setIntegral_congr_ae hFm ?_
    filter_upwards [hfeq'] with z hz hzF
    rw [hz (hFe hzF)]
  have hgF : (∫ z in fundDomain Γ, g z * rho z) =
      ((∫ z in fundDomain Γ, gr z * rho z : ℝ) : ℂ) + ((∫ z in fundDomain Γ, gi z * rho z : ℝ) : ℂ) * I := by
    rw [← s19c_split hgri hgii]
    simp only [← hgeq]
  -- the four real limits
  have h1 := s19c_core_real hΓ hinv hFrm hFrb hFra hgri
  have h2 := s19c_core_real hΓ hinv hFim hFib hFia hgii
  have h3 := s19c_core_real hΓ hinv hFrm hFrb hFra hgii
  have h4 := s19c_core_real hΓ hinv hFim hFib hFia hgri
  have hlim := (((h1.sub h2).ofReal).add (((h3.add h4).ofReal).mul_const I))
  rw [hfF, hgF]
  have htarget : (((∫ z in fundDomain Γ, Fr z * rho z : ℝ) : ℂ) + ((∫ z in fundDomain Γ, Fi z * rho z : ℝ) : ℂ) * I) *
      (((∫ z in fundDomain Γ, gr z * rho z : ℝ) : ℂ) + ((∫ z in fundDomain Γ, gi z * rho z : ℝ) : ℂ) * I) /
        ((hypArea Γ).toReal : ℂ) =
      (((∫ z in fundDomain Γ, Fr z * rho z) * (∫ z in fundDomain Γ, gr z * rho z) / (hypArea Γ).toReal -
          (∫ z in fundDomain Γ, Fi z * rho z) * (∫ z in fundDomain Γ, gi z * rho z) / (hypArea Γ).toReal : ℝ) : ℂ) +
        (((∫ z in fundDomain Γ, Fr z * rho z) * (∫ z in fundDomain Γ, gi z * rho z) / (hypArea Γ).toReal +
          (∫ z in fundDomain Γ, Fi z * rho z) * (∫ z in fundDomain Γ, gr z * rho z) / (hypArea Γ).toReal : ℝ) : ℂ) *
          I := by
    push_cast
    linear_combination (((∫ z in fundDomain Γ, Fi z * rho z : ℝ) : ℂ) *
      ((∫ z in fundDomain Γ, gi z * rho z : ℝ) : ℂ) / ((hypArea Γ).toReal : ℂ)) * Complex.I_sq
  rw [htarget]
  refine hlim.congr' ?_
  filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with s hs
  -- split the complex pairing into the four real ones
  set As : ℝ := 4 * π * s ^ 2 / (1 - s ^ 2) with hAsdef
  have hAs : 0 < As := div_pos (by have := hs.1; positivity) (by nlinarith [hs.1, hs.2])
  set Br : ℂ → ℝ := fun z => ∫ w in {w | w ∈ unitDiscExterior ∧ ‖w - z‖ ≤ s * ‖w * conj z - 1‖}, Fr w * rho w
    with hBrdef
  set Bi : ℂ → ℝ := fun z => ∫ w in {w | w ∈ unitDiscExterior ∧ ‖w - z‖ ≤ s * ‖w * conj z - 1‖}, Fi w * rho w
    with hBidef
  have hBrm : Measurable Br := s19c_ball_measurable_real hFrm s
  have hBim : Measurable Bi := s19c_ball_measurable_real hFim s
  have hBrb : ∀ z ∈ unitDiscExterior, |Br z / As| ≤ max C 0 := fun z hz => by
    rw [abs_div, abs_of_pos hAs, div_le_iff₀ hAs]
    exact s19c_ball_bound_real hFrb hz hs.1 hs.2
  have hBib : ∀ z ∈ unitDiscExterior, |Bi z / As| ≤ max C 0 := fun z hz => by
    rw [abs_div, abs_of_pos hAs, div_le_iff₀ hAs]
    exact s19c_ball_bound_real hFib hz hs.1 hs.2
  have hpi : ∀ (b : ℂ → ℝ) (hbm : Measurable b) (hbb : ∀ z ∈ unitDiscExterior, |b z / As| ≤ max C 0)
      (c : ℂ → ℝ) (hc : IntegrableOn (fun z => c z * rho z) (fundDomain Γ)),
      IntegrableOn (fun z => b z / As * c z * rho z) (fundDomain Γ) := by
    intro b hbm hbb c hc
    refine IntegrableOn.congr_fun (Integrable.mono' (hc.norm.const_mul (max C 0))
      ((hbm.div_const As).aestronglyMeasurable.mul hc.1) ?_) (fun z _ => by simp only [Pi.mul_apply]; ring) hFm
    filter_upwards [ae_restrict_mem hFm] with z hz
    simp only [Pi.mul_apply]
    rw [Real.norm_eq_abs, abs_mul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (hbb z (hFe hz)) (abs_nonneg _)
  have e1 : (∫ z in fundDomain Γ,
      ((∫ w in {w | w ∈ unitDiscExterior ∧ ‖w - z‖ ≤ s * ‖w * conj z - 1‖}, f w * rho w) /
        ((As : ℝ) : ℂ)) * g z * rho z) =
      ∫ z in fundDomain Γ, (((Br z / As * gr z * rho z - Bi z / As * gi z * rho z : ℝ) : ℂ) +
        ((Br z / As * gi z * rho z + Bi z / As * gr z * rho z : ℝ) : ℂ) * I) := by
    refine setIntegral_congr_fun hFm fun z hz => ?_
    rw [hball s hs z (hFe hz), hgeq z]
    push_cast
    linear_combination (((Bi z : ℝ) : ℂ) / ((As : ℝ) : ℂ) * ((gi z : ℝ) : ℂ) * ((rho z : ℝ) : ℂ)) * Complex.I_sq
  symm
  have i1 : Integrable (fun z => ((Br z / As * gr z * rho z - Bi z / As * gi z * rho z : ℝ) : ℂ))
      (volume.restrict (fundDomain Γ)) := ((hpi Br hBrm hBrb gr hgri).sub (hpi Bi hBim hBib gi hgii)).ofReal
  have i2 : Integrable (fun z => ((Br z / As * gi z * rho z + Bi z / As * gr z * rho z : ℝ) : ℂ) * I)
      (volume.restrict (fundDomain Γ)) :=
    (((hpi Br hBrm hBrb gi hgii).add (hpi Bi hBim hBib gr hgri)).ofReal).mul_const I
  rw [e1, integral_add i1 i2,
    integral_mul_const, integral_complex_ofReal, integral_complex_ofReal,
    integral_sub (hpi Br hBrm hBrb gr hgri) (hpi Bi hBim hBib gi hgii),
    integral_add (hpi Br hBrm hBrb gi hgii) (hpi Bi hBim hBib gr hgri)]

/-- The ball `B(z, s)` is the image of `𝔻*_{1/s}` under `T_z(v) = (z v + 1)/(v + z̄)`: pulling back. -/
theorem s19c_ball_pull {z : ℂ} (hz : z ∈ unitDiscExterior) {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (f : ℂ → ℝ) :
    (∫ w in {w | w ∈ unitDiscExterior ∧ ‖w - z‖ ≤ s * ‖w * conj z - 1‖}, f w * rho w) =
      ∫ v in discExteriorR (1 / s), f ((z * v + 1) / (v + conj z)) * rho v := by
  have hz1 : 1 < ‖z‖ := hz
  set c : ℝ := √(‖z‖ ^ 2 - 1) with hcdef
  have hc : 0 < c := Real.sqrt_pos.mpr (by nlinarith)
  have hc2 : c ^ 2 = ‖z‖ ^ 2 - 1 := Real.sq_sqrt (by nlinarith)
  have hcC : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hc.ne'
  have hzz : z * conj z - 1 = ((‖z‖ ^ 2 - 1 : ℝ) : ℂ) := by
    rw [Complex.mul_conj']
    push_cast
    ring
  have hcc : (c : ℂ) ^ 2 = ((‖z‖ ^ 2 - 1 : ℝ) : ℂ) := by
    rw [← hc2]
    push_cast
    ring
  have hM : (!![z / (c : ℂ), 1 / (c : ℂ); 1 / (c : ℂ), conj z / (c : ℂ)] : Matrix (Fin 2) (Fin 2) ℂ).det = 1 := by
    rw [Matrix.det_fin_two_of]
    have e : z / (c : ℂ) * (conj z / c) - 1 / c * (1 / c) = (z * conj z - 1) / (c : ℂ) ^ 2 := by ring
    rw [e, hzz, hcc, div_self (Complex.ofReal_ne_zero.mpr (by nlinarith))]
  set g : SL2C := ⟨_, hM⟩ with hgdef
  have g00 : g 0 0 = z / (c : ℂ) := rfl
  have g01 : g 0 1 = 1 / (c : ℂ) := rfl
  have g10 : g 1 0 = 1 / (c : ℂ) := rfl
  have g11 : g 1 1 = conj z / (c : ℂ) := rfl
  have hg : IsSU11 g := by
    refine ⟨?_, ?_⟩
    · rw [g10, g01, map_div₀, map_one, Complex.conj_ofReal]
    · rw [g11, g00, map_div₀, Complex.conj_ofReal]
  have hden : ∀ v, g 1 0 * v + g 1 1 = (v + conj z) / c := by
    intro v
    rw [g10, g11]
    ring
  have hmob : ∀ v, mob g v = (z * v + 1) / (v + conj z) := by
    intro v
    unfold mob
    rw [g00, g01, hden, show z / (c : ℂ) * v + 1 / c = (z * v + 1) / c by ring, div_div_div_cancel_right₀ hcC]
  -- the pseudo-hyperbolic quantities of `T_z v` relative to `z`
  set m : ℝ := ‖z‖ ^ 2 - 1 with hmdef
  have hm : 0 < m := by rw [hmdef]; nlinarith
  have hmem : ∀ v, v ∈ unitDiscExterior → g 1 0 * v + g 1 1 ≠ 0 →
      (mob g v ∈ {w | w ∈ unitDiscExterior ∧ ‖w - z‖ ≤ s * ‖w * conj z - 1‖} ↔ 1 / s ≤ ‖v‖) := by
    intro v hv hD
    have hvz : v + conj z ≠ 0 := by
      intro h0
      apply hD
      rw [hden, h0, zero_div]
    have hdpos : 0 < ‖v + conj z‖ := norm_pos_iff.mpr hvz
    have e1 : mob g v - z = (1 - z * conj z) / (v + conj z) := by
      rw [hmob]
      field_simp
      ring
    have e2 : mob g v * conj z - 1 = v * (z * conj z - 1) / (v + conj z) := by
      rw [hmob]
      field_simp
      ring
    have n1 : ‖1 - z * conj z‖ = m := by
      rw [norm_sub_rev, hzz, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hm]
    have n2 : ‖z * conj z - 1‖ = m := by
      rw [hzz, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hm]
    have hext : mob g v ∈ unitDiscExterior := fd_mob_exterior hg hv hD
    constructor
    · rintro ⟨-, h2⟩
      rw [e1, e2, norm_div, norm_div, norm_mul, n1, n2, ← mul_div_assoc,
        div_le_div_iff_of_pos_right hdpos] at h2
      rw [div_le_iff₀ hs0]
      nlinarith
    · intro h2
      refine ⟨hext, ?_⟩
      rw [e1, e2, norm_div, norm_div, norm_mul, n1, n2, ← mul_div_assoc,
        div_le_div_iff_of_pos_right hdpos]
      rw [div_le_iff₀ hs0] at h2
      nlinarith
  set D := discExteriorR (1 / s) with hDdef
  set S := D ∩ {v | g 1 0 * v + g 1 1 ≠ 0} with hS
  have hSm : MeasurableSet S := (pat_discExteriorR_measurable _).inter (fd_measurableSet_gen g)
  have hgen : ∀ v ∈ S, g 1 0 * v + g 1 1 ≠ 0 := fun v hv => hv.2
  have hinj : InjOn (mob g) S := fun w1 h1 w2 h2 he => by
    rw [← (fd_inv_step g (hgen w1 h1)).2, ← (fd_inv_step g (hgen w2 h2)).2, he]
  have himg : mob g '' S =ᵐ[volume] {w | w ∈ unitDiscExterior ∧ ‖w - z‖ ≤ s * ‖w * conj z - 1‖} := by
    refine eventuallyEqSet_iff.mpr ?_
    filter_upwards [s19m_pole_ae g⁻¹] with u hu
    constructor
    · rintro ⟨v, hv, rfl⟩
      exact (hmem v hv.1.1 hv.2).mpr hv.1.2
    · intro huB
      have hstep := fd_inv_step g⁻¹ hu
      rw [inv_inv] at hstep
      have hvext : mob g⁻¹ u ∈ unitDiscExterior := fd_mob_exterior (isSU11_inv hg) huB.1 hu
      refine ⟨mob g⁻¹ u, ⟨⟨hvext, (hmem _ hvext hstep.1).mp (by rw [hstep.2]; exact huB)⟩, hstep.1⟩, hstep.2⟩
  have hcv := integral_image_eq_integral_abs_det_fderiv_smul volume hSm
    (f' := fun x => (ContinuousLinearMap.toSpanSingleton ℂ (deriv (mob g) x)).restrictScalars ℝ)
    (fun x hx => ((fd_mob_differentiableAt g (hgen x hx)).hasDerivAt.hasFDerivAt.restrictScalars ℝ).hasFDerivWithinAt)
    hinj (fun w => f w * rho w)
  rw [← setIntegral_congr_set himg, hcv]
  have hSD : S =ᵐ[volume] D := by
    refine eventuallyEqSet_iff.mpr ?_
    filter_upwards [s19m_pole_ae g] with w hw
    exact ⟨fun h => h.1, fun h => ⟨h, hw⟩⟩
  rw [setIntegral_congr_set hSD]
  refine setIntegral_congr_ae (pat_discExteriorR_measurable _) ?_
  filter_upwards [s19m_pole_ae g] with v hD hv
  have hv1 : v ∈ unitDiscExterior := hv.1
  rw [det_restrictScalars_toSpanSingleton, abs_of_nonneg (sq_nonneg _), smul_eq_mul, mul_left_comm,
    s19m_rho_pull hg hv1 hD, hmob v]

/-- `r (cos θ + i sin θ) = r e^{iθ}`. -/
theorem s19c_polar_pt (p : ℝ × ℝ) :
    Complex.polarCoord.symm p = (p.1 : ℂ) * exp ((p.2 : ℂ) * I) := by
  rw [Complex.polarCoord_symm_apply, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]

/-- Hyperbolic polar coordinates about `∞` on `𝔻*_{1/s}`, in the pseudo-radius `u = 1/|v|`. -/
theorem s19c_polar {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) {F0 : ℂ → ℝ} (hF0m : Measurable F0) {C : ℝ}
    (hF0b : ∀ᵐ v ∂(volume.restrict (discExteriorR (1 / s))), |F0 v| ≤ C) :
    (∫ v in discExteriorR (1 / s), F0 v * rho v) =
      ∫ u in Ioo 0 s, 4 * u / (1 - u ^ 2) ^ 2 * ∫ θ in (0 : ℝ)..2 * π, F0 (exp (θ * I) / u) := by
  have hr : 1 < 1 / s := by rw [one_lt_div hs0]; exact hs1
  set D := discExteriorR (1 / s) with hDdef
  have hDm : MeasurableSet D := pat_discExteriorR_measurable _
  set G : ℂ → ℝ := D.indicator (fun v => F0 v * rho v) with hGdef
  have hGm : Measurable G := (hF0m.mul s19m_rho_measurable).indicator hDm
  have hFi : IntegrableOn (fun v => F0 v * rho v) D := by
    refine Integrable.mono' ((pat_rho_integrable hr).const_mul C)
      (hF0m.mul s19m_rho_measurable).aestronglyMeasurable ?_
    filter_upwards [hF0b] with v hv
    have hρ0 : 0 ≤ rho v := div_nonneg (by norm_num) (sq_nonneg _)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hρ0]
    exact mul_le_mul_of_nonneg_right hv hρ0
  have hGi : Integrable G := (integrable_indicator_iff hDm).mpr hFi
  -- polar coordinates
  set H : ℝ × ℝ → ℝ := fun p => p.1 • G ((p.1 : ℂ) * exp ((p.2 : ℂ) * I)) with hHdef
  have hpolar : (∫ v in D, F0 v * rho v) = ∫ p in Ioi (0 : ℝ) ×ˢ Ioo (-π) π, H p := by
    rw [← integral_indicator hDm, ← Complex.integral_comp_polarCoord_symm]
    simp only [s19c_polar_pt]
    rfl
  have hHm : Measurable H := by
    rw [hHdef]
    exact measurable_fst.smul (hGm.comp (by fun_prop))
  have hHi : IntegrableOn H (Ioi (0 : ℝ) ×ˢ Ioo (-π) π) := by
    refine ⟨hHm.aestronglyMeasurable, ?_⟩
    have hl := Complex.lintegral_comp_polarCoord_symm (fun v => ‖G v‖ₑ)
    simp only [s19c_polar_pt] at hl
    show ∫⁻ p in Ioi (0 : ℝ) ×ˢ Ioo (-π) π, ‖H p‖ₑ < ⊤
    have he : ∫⁻ p in Ioi (0 : ℝ) ×ˢ Ioo (-π) π, ‖H p‖ₑ =
        ∫⁻ p in polarCoord.target, ENNReal.ofReal p.1 • ‖G ((p.1 : ℂ) * exp ((p.2 : ℂ) * I))‖ₑ := by
      refine setLIntegral_congr_fun (measurableSet_Ioi.prod measurableSet_Ioo) fun p hp => ?_
      rw [hHdef, enorm_smul, Real.enorm_eq_ofReal (le_of_lt hp.1), smul_eq_mul]
    rw [he, hl]
    exact hGi.2
  rw [hpolar, Measure.volume_eq_prod, setIntegral_prod H hHi]
  -- the inner (angular) integral
  set K : ℝ → ℝ := fun r => r * (4 / (1 - r ^ 2) ^ 2) * ∫ θ in (0 : ℝ)..2 * π, F0 ((r : ℂ) * exp ((θ : ℂ) * I))
    with hKdef
  have hinner : ∀ r ∈ Ioi (0 : ℝ), (∫ θ in Ioo (-π) π, H (r, θ)) = (Ici (1 / s)).indicator K r := by
    intro r hr0
    have hr0' : 0 < r := hr0
    have hnorm : ∀ θ : ℝ, ‖(r : ℂ) * exp ((θ : ℂ) * I)‖ = r := fun θ => by
      rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr0']
    have hper : Function.Periodic (fun θ : ℝ => F0 ((r : ℂ) * exp ((θ : ℂ) * I))) (2 * π) := by
      intro θ
      simp only
      rw [show ((θ + 2 * π : ℝ) : ℂ) * I = (θ : ℂ) * I + 2 * π * I by push_cast; ring, Complex.exp_add,
        Complex.exp_two_pi_mul_I, mul_one]
    have hshift : (∫ θ in Ioo (-π) π, F0 ((r : ℂ) * exp ((θ : ℂ) * I))) =
        ∫ θ in (0 : ℝ)..2 * π, F0 ((r : ℂ) * exp ((θ : ℂ) * I)) := by
      rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le (by linarith [Real.pi_pos])]
      have := hper.intervalIntegral_add_eq (-π) 0
      rw [show -π + 2 * π = π by ring, zero_add] at this
      exact this
    by_cases hrs : 1 / s ≤ r
    · rw [indicator_of_mem (show r ∈ Ici (1 / s) from hrs)]
      have hmemD : ∀ θ : ℝ, (r : ℂ) * exp ((θ : ℂ) * I) ∈ D := fun θ => by
        refine ⟨?_, ?_⟩
        · show 1 < ‖(r : ℂ) * exp ((θ : ℂ) * I)‖
          rw [hnorm]; linarith
        · rw [hnorm]; exact hrs
      have hρr : ∀ θ : ℝ, rho ((r : ℂ) * exp ((θ : ℂ) * I)) = 4 / (1 - r ^ 2) ^ 2 := fun θ => by
        unfold rho; rw [hnorm]
      have hpt : ∀ θ : ℝ, H (r, θ) = r * (4 / (1 - r ^ 2) ^ 2) * F0 ((r : ℂ) * exp ((θ : ℂ) * I)) := fun θ => by
        simp only [hHdef, hGdef, smul_eq_mul]
        rw [indicator_of_mem (hmemD θ), hρr]
        ring
      simp only [hpt]
      rw [integral_const_mul, hshift]
    · rw [indicator_of_notMem (show r ∉ Ici (1 / s) from hrs)]
      have hpt : ∀ θ : ℝ, H (r, θ) = 0 := fun θ => by
        simp only [hHdef, hGdef, smul_eq_mul]
        rw [indicator_of_notMem (fun h => hrs (by have := h.2; rwa [hnorm] at this)), mul_zero]
      simp only [hpt, integral_zero]
  rw [setIntegral_congr_fun measurableSet_Ioi hinner, setIntegral_indicator measurableSet_Ici,
    show Ioi (0 : ℝ) ∩ Ici (1 / s) = Ici (1 / s) from inter_eq_right.mpr fun r hr' => by
      have : (0 : ℝ) < 1 / s := by positivity
      exact lt_of_lt_of_le this hr', integral_Ici_eq_integral_Ioi]
  -- the substitution `r = 1/u`
  have himg : (fun u : ℝ => u⁻¹) '' Ioo 0 s = Ioi (1 / s) := by
    rw [Set.image_inv_eq_inv, Set.inv_Ioo_0_left hs0, one_div]
  have hsub := integral_image_eq_integral_abs_deriv_smul (f := fun u : ℝ => u⁻¹) (f' := fun u : ℝ => -(u ^ 2)⁻¹)
    (measurableSet_Ioo : MeasurableSet (Ioo (0 : ℝ) s))
    (fun u (hu : u ∈ Ioo (0 : ℝ) s) => (hasDerivAt_inv (ne_of_gt hu.1)).hasDerivWithinAt)
    (fun (a : ℝ) _ (b : ℝ) _ (h : a⁻¹ = b⁻¹) => inv_injective h) K
  rw [himg] at hsub
  rw [hsub]
  refine setIntegral_congr_fun measurableSet_Ioo fun u hu => ?_
  have hu0 : 0 < u := hu.1
  have hu1 : u < 1 := lt_trans hu.2 hs1
  simp only [hKdef, smul_eq_mul]
  have he : ∀ θ : ℝ, ((u⁻¹ : ℝ) : ℂ) * exp ((θ : ℂ) * I) = exp ((θ : ℂ) * I) / (u : ℂ) := fun θ => by
    push_cast
    ring
  simp only [he]
  have h1 : 1 - u ^ 2 ≠ 0 := by nlinarith
  have h2 : 1 - u⁻¹ ^ 2 ≠ 0 := by
    have : 1 < u⁻¹ := one_lt_inv₀ hu0 |>.mpr hu1
    nlinarith
  rw [abs_neg, abs_of_pos (by positivity)]
  generalize (∫ θ in (0 : ℝ)..2 * π, F0 (exp (θ * I) / u)) = Φ
  have hu2 : u ^ 2 ≠ 0 := by positivity
  have e : 1 - u⁻¹ ^ 2 = -(1 - u ^ 2) / u ^ 2 := by
    field_simp
    ring
  rw [e]
  field_simp

/-- **C1.** Hyperbolic polar coordinates about `z ∈ 𝔻*`: the circle of pseudo-hyperbolic radius `u` about `z` is
`θ ↦ T_z(e^{iθ}/u)`, `T_z(w) = (z w + 1)/(w + z̄)`, and `ρ d²w = 4u/(1 - u²)² du dθ`. -/
theorem s19c_radial {z : ℂ} (hz : z ∈ unitDiscExterior) {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) {f : ℂ → ℝ}
    (hfm : Measurable f) (hfb : ∃ C, ∀ w ∈ unitDiscExterior, |f w| ≤ C) :
    (∫ w in {w | w ∈ unitDiscExterior ∧ ‖w - z‖ ≤ s * ‖w * conj z - 1‖}, f w * rho w) =
      ∫ u in Ioo 0 s, 4 * u / (1 - u ^ 2) ^ 2 *
        ∫ θ in (0 : ℝ)..2 * π, f ((z * (exp (θ * I) / u) + 1) / (exp (θ * I) / u + conj z)) := by
  obtain ⟨C, hC⟩ := hfb
  rw [s19c_ball_pull hz hs0 hs1 f]
  have hTm : Measurable fun v : ℂ => (z * v + 1) / (v + conj z) := by fun_prop
  refine s19c_polar hs0 hs1 (hfm.comp hTm) (C := C) ?_
  have hpole : ∀ᵐ v ∂volume, v + conj z ≠ 0 := by
    have : ({-conj z} : Set ℂ)ᶜ ∈ ae volume := compl_mem_ae_iff.mpr (measure_singleton _)
    filter_upwards [this] with v hv
    intro h0
    exact hv (eq_neg_of_add_eq_zero_left h0)
  filter_upwards [ae_restrict_of_ae hpole, ae_restrict_mem (pat_discExteriorR_measurable (1 / s))] with v hv hvD
  apply hC
  -- `T_z` maps `𝔻*` minus its pole into `𝔻*`
  have hv1 : 1 < ‖v‖ := hvD.1
  have hz1 : 1 < ‖z‖ := hz
  have hdpos : 0 < ‖v + conj z‖ := norm_pos_iff.mpr hv
  show 1 < ‖(z * v + 1) / (v + conj z)‖
  have hid : ‖z * v + 1‖ ^ 2 - ‖v + conj z‖ ^ 2 = (‖z‖ ^ 2 - 1) * (‖v‖ ^ 2 - 1) := by
    simp only [Complex.sq_norm, Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.mul_re,
      Complex.mul_im, Complex.conj_re, Complex.conj_im, Complex.one_re, Complex.one_im]
    ring
  rw [norm_div, one_lt_div hdpos]
  have hpos : 0 < (‖z‖ ^ 2 - 1) * (‖v‖ ^ 2 - 1) := mul_pos (by nlinarith) (by nlinarith)
  nlinarith [norm_nonneg (z * v + 1)]

/-- `T_z(v) = (z v + 1)/(v + z̄)` maps `𝔻*` into `𝔻*`, except at its pole where it is the junk value `0`. -/
theorem s19c_T_mem {z : ℂ} (hz : z ∈ unitDiscExterior) {v : ℂ} (hv : v ∈ unitDiscExterior) :
    (z * v + 1) / (v + conj z) ∈ unitDiscExterior ∨ (z * v + 1) / (v + conj z) = 0 := by
  by_cases hp : v + conj z = 0
  · right
    rw [hp, div_zero]
  · left
    have hv1 : 1 < ‖v‖ := hv
    have hz1 : 1 < ‖z‖ := hz
    have hdpos : 0 < ‖v + conj z‖ := norm_pos_iff.mpr hp
    show 1 < ‖(z * v + 1) / (v + conj z)‖
    have hid : ‖z * v + 1‖ ^ 2 - ‖v + conj z‖ ^ 2 = (‖z‖ ^ 2 - 1) * (‖v‖ ^ 2 - 1) := by
      simp only [Complex.sq_norm, Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.mul_re,
        Complex.mul_im, Complex.conj_re, Complex.conj_im, Complex.one_re, Complex.one_im]
      ring
    rw [norm_div, one_lt_div hdpos]
    have hpos : 0 < (‖z‖ ^ 2 - 1) * (‖v‖ ^ 2 - 1) := mul_pos (by nlinarith) (by nlinarith)
    nlinarith [norm_nonneg (z * v + 1)]

/-- `∫_0^s 4u/(1 - u²)² du = 2s²/(1 - s²)`. -/
theorem s19c_W {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) :
    IntegrableOn (fun u : ℝ => 4 * u / (1 - u ^ 2) ^ 2) (Ioo 0 s) ∧
      (∫ u in Ioo 0 s, 4 * u / (1 - u ^ 2) ^ 2) = 2 * s ^ 2 / (1 - s ^ 2) := by
  have hcont : ContinuousOn (fun u : ℝ => 4 * u / (1 - u ^ 2) ^ 2) (Icc 0 s) := by
    refine (continuousOn_const.mul continuousOn_id).div (by fun_prop) fun u hu => ?_
    have : u < 1 := lt_of_le_of_lt hu.2 hs1
    have : 0 ≤ u := hu.1
    exact pow_ne_zero 2 (by nlinarith)
  have hii : IntervalIntegrable (fun u : ℝ => 4 * u / (1 - u ^ 2) ^ 2) volume 0 s :=
    (hcont.mono (by rw [uIcc_of_le hs0.le])).intervalIntegrable
  refine ⟨(hcont.integrableOn_Icc).mono_set Ioo_subset_Icc_self, ?_⟩
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hs0.le]
  have hd : ∀ u ∈ uIcc 0 s, HasDerivAt (fun u : ℝ => 2 / (1 - u ^ 2)) (4 * u / (1 - u ^ 2) ^ 2) u := by
    intro u hu
    rw [uIcc_of_le hs0.le] at hu
    have hne : 1 - u ^ 2 ≠ 0 := by nlinarith [hu.1, hu.2]
    have hp : HasDerivAt (fun x : ℝ => 1 - x ^ 2) (0 - 2 * u) u := by
      convert (hasDerivAt_pow 2 u).const_sub 1 using 1
      norm_num
    convert (hasDerivAt_const u (2 : ℝ)).div hp hne using 1
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hii]
  have hne : 1 - s ^ 2 ≠ 0 := by nlinarith
  field_simp
  ring

/-- Weighted averages with weights whose mass escapes to `u → 1` converge to the limit at `1`. -/
theorem s19c_avg_limit {w c : ℝ → ℝ} {P M : ℝ} (hw0 : ∀ u ∈ Ioo (0 : ℝ) 1, 0 ≤ w u)
    (hwi : ∀ s ∈ Ioo (0 : ℝ) 1, IntegrableOn w (Ioo 0 s))
    (hwci : ∀ s ∈ Ioo (0 : ℝ) 1, IntegrableOn (fun u => w u * c u) (Ioo 0 s))
    (hcb : ∀ u, |c u| ≤ M) (hc : Tendsto c (𝓝[<] 1) (𝓝 P))
    (hW : Tendsto (fun s => ∫ u in Ioo 0 s, w u) (𝓝[<] 1) atTop) :
    Tendsto (fun s => (∫ u in Ioo 0 s, w u * c u) / (∫ u in Ioo 0 s, w u)) (𝓝[<] 1) (𝓝 P) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hev := (Metric.tendsto_nhds.mp hc) (ε / 2) (half_pos hε)
  obtain ⟨u0, hu0, hsub⟩ := (mem_nhdsLT_iff_exists_Ioo_subset).mp hev
  set u1 := max u0 (1 / 2) with hu1def
  have hu1 : u1 < 1 := max_lt hu0 (by norm_num)
  have hu1pos : 0 < u1 := lt_of_lt_of_le (by norm_num) (le_max_right _ _)
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hcb 0)
  set B := ∫ u in Ioc 0 u1, w u with hBdef
  have hB0 : 0 ≤ B := setIntegral_nonneg measurableSet_Ioc fun u hu => hw0 u ⟨hu.1, lt_of_le_of_lt hu.2 hu1⟩
  set K := (M + |P|) * B with hKdef
  have hK0 : 0 ≤ K := mul_nonneg (by positivity) hB0
  filter_upwards [hW.eventually_gt_atTop (2 * K / ε), Ioo_mem_nhdsLT hu1] with s hWs hs
  have hs0 : 0 < s := lt_trans hu1pos hs.1
  have hsI : s ∈ Ioo (0 : ℝ) 1 := ⟨hs0, hs.2⟩
  set W := ∫ u in Ioo 0 s, w u with hWdef
  have hWpos : 0 < W := lt_of_le_of_lt (by positivity) hWs
  have hdiff : (∫ u in Ioo 0 s, w u * c u) / W - P = (∫ u in Ioo 0 s, w u * (c u - P)) / W := by
    have : (∫ u in Ioo 0 s, w u * (c u - P)) = (∫ u in Ioo 0 s, w u * c u) - W * P := by
      rw [← integral_mul_const, ← integral_sub (hwci s hsI) ((hwi s hsI).mul_const P)]
      congr 1
      funext u
      ring
    rw [this]
    field_simp
  rw [Real.dist_eq, hdiff, abs_div, abs_of_pos hWpos, div_lt_iff₀ hWpos]
  have hbi : IntegrableOn (fun u => w u * ((M + |P|) * (Ioc 0 u1).indicator 1 u + ε / 2)) (Ioo 0 s) := by
    have h1 : IntegrableOn (fun u => (Ioc 0 u1).indicator w u) (Ioo 0 s) :=
      ((hwi s hsI).indicator measurableSet_Ioc)
    refine IntegrableOn.congr_fun ((h1.const_mul (M + |P|)).add ((hwi s hsI).mul_const (ε / 2)))
      (fun u _ => ?_) measurableSet_Ioo
    by_cases hu : u ∈ Ioc 0 u1
    · simp only [Pi.add_apply, indicator_of_mem hu, Pi.one_apply]
      ring
    · simp only [Pi.add_apply, indicator_of_notMem hu]
      ring
  have hbound : |∫ u in Ioo 0 s, w u * (c u - P)| ≤
      ∫ u in Ioo 0 s, w u * ((M + |P|) * (Ioc 0 u1).indicator 1 u + ε / 2) := by
    rw [← Real.norm_eq_abs]
    refine norm_integral_le_of_norm_le hbi ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
    have hwu : 0 ≤ w u := hw0 u ⟨hu.1, lt_trans hu.2 hs.2⟩
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hwu]
    refine mul_le_mul_of_nonneg_left ?_ hwu
    by_cases hu1' : u ≤ u1
    · rw [indicator_of_mem (show u ∈ Ioc 0 u1 from ⟨hu.1, hu1'⟩)]
      have := hcb u
      have : |c u - P| ≤ M + |P| := (abs_sub _ _).trans (by linarith)
      simp only [Pi.one_apply, mul_one]
      linarith
    · rw [indicator_of_notMem (fun h => hu1' h.2)]
      have hlt : u ∈ Ioo u0 1 := ⟨lt_of_le_of_lt (le_max_left _ _) (not_le.mp hu1'), lt_trans hu.2 hs.2⟩
      have := hsub hlt
      simp only [mem_setOf_eq, Real.dist_eq] at this
      simp only [mul_zero, zero_add]
      linarith
  have hval : (∫ u in Ioo 0 s, w u * ((M + |P|) * (Ioc 0 u1).indicator 1 u + ε / 2)) = K + ε / 2 * W := by
    have e : (fun u => w u * ((M + |P|) * (Ioc 0 u1).indicator 1 u + ε / 2)) =
        fun u => (M + |P|) * (Ioc 0 u1).indicator w u + w u * (ε / 2) := by
      funext u
      by_cases hu : u ∈ Ioc 0 u1
      · simp only [indicator_of_mem hu, Pi.one_apply]
        ring
      · simp only [indicator_of_notMem hu]
        ring
    rw [e, integral_add ((((hwi s hsI).indicator measurableSet_Ioc)).const_mul _) ((hwi s hsI).mul_const _),
      integral_const_mul, integral_mul_const, setIntegral_indicator measurableSet_Ioc,
      show Ioo 0 s ∩ Ioc 0 u1 = Ioc 0 u1 from inter_eq_right.mpr fun u hu => ⟨hu.1, lt_of_le_of_lt hu.2 hs.1⟩]
    rw [hKdef]
    ring
  rw [hval] at hbound
  have : K < ε / 2 * W := by
    rw [div_lt_iff₀ hε] at hWs
    linarith
  linarith

/-- The sphere integral `Ψ(z, u) = ∫_0^{2π} f(T_z(e^{iθ}/u)) dθ` is jointly measurable and bounded. -/
theorem s19c_Psi {f : ℂ → ℝ} (hfm : Measurable f) {C : ℝ} (hC : ∀ w ∈ unitDiscExterior, |f w| ≤ C) :
    Measurable (fun p : ℂ × ℝ => ∫ θ in (0 : ℝ)..2 * π,
        f ((p.1 * (exp (θ * I) / p.2) + 1) / (exp (θ * I) / p.2 + conj p.1))) ∧
      ∀ z ∈ unitDiscExterior, ∀ u ∈ Ioo (0 : ℝ) 1,
        |∫ θ in (0 : ℝ)..2 * π, f ((z * (exp (θ * I) / u) + 1) / (exp (θ * I) / u + conj z))| ≤
          2 * π * max C |f 0| := by
  constructor
  · have hc : Measurable fun q : (ℂ × ℝ) × ℝ => conj q.1.1 :=
      Complex.continuous_conj.measurable.comp (measurable_fst.comp measurable_fst)
    have hφ : Measurable fun q : (ℂ × ℝ) × ℝ =>
        f ((q.1.1 * (exp (q.2 * I) / q.1.2) + 1) / (exp (q.2 * I) / q.1.2 + conj q.1.1)) := by
      refine hfm.comp ?_
      fun_prop
    have hsm := StronglyMeasurable.integral_prod_right (ν := volume.restrict (Ioc (0 : ℝ) (2 * π)))
      (f := fun p : ℂ × ℝ => fun θ : ℝ =>
        f ((p.1 * (exp (θ * I) / p.2) + 1) / (exp (θ * I) / p.2 + conj p.1))) hφ.stronglyMeasurable
    have heq : (fun p : ℂ × ℝ => ∫ θ in (0 : ℝ)..2 * π,
        f ((p.1 * (exp (θ * I) / p.2) + 1) / (exp (θ * I) / p.2 + conj p.1))) =
        fun p : ℂ × ℝ => ∫ θ in Ioc (0 : ℝ) (2 * π),
          f ((p.1 * (exp (θ * I) / p.2) + 1) / (exp (θ * I) / p.2 + conj p.1)) := by
      funext p
      exact intervalIntegral.integral_of_le (by positivity)
    rw [heq]
    exact hsm.measurable
  · intro z hz u hu
    have hb : ∀ θ : ℝ, ‖f ((z * (exp (θ * I) / u) + 1) / (exp (θ * I) / u + conj z))‖ ≤ max C |f 0| := by
      intro θ
      rw [Real.norm_eq_abs]
      have hv : exp (θ * I) / u ∈ unitDiscExterior := by
        show 1 < ‖exp (θ * I) / u‖
        rw [norm_div, Complex.norm_exp_ofReal_mul_I, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hu.1,
          one_lt_div hu.1]
        exact hu.2
      rcases s19c_T_mem hz hv with h | h
      · exact (hC _ h).trans (le_max_left _ _)
      · rw [h]
        exact le_max_right _ _
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := 2 * π)
      (fun θ _ => hb θ)
    rw [Real.norm_eq_abs, sub_zero, abs_of_pos (show (0 : ℝ) < 2 * π by positivity)] at this
    linarith

/-- **C2.** CORE from a packaged representation (`hrep`, built in R1–R4): a continuous isometric representation of
`SL(2, ℝ)` on a real `L²` space with a lift `L` of bounded automorphic functions such that (E) the invariant projection
pairs as the product of means, and (S) the sphere pairings are diagonal matrix coefficients. -/
theorem s19c_core_of_rep {Γ : Subgroup SL2C} (hΓ : IsCofinite Γ)
    (hrep : ∃ (X : Type) (_ : MeasurableSpace X) (μ : Measure X)
      (ρ : SL(2, ℝ) →* (Lp ℝ 2 μ ≃ₗᵢ[ℝ] Lp ℝ 2 μ)) (L : (ℂ → ℝ) → Lp ℝ 2 μ),
      Continuous (fun p : SL(2, ℝ) × Lp ℝ 2 μ => ρ p.1 p.2) ∧
      ∀ f g : ℂ → ℝ, Measurable f → Measurable g →
        (∃ C, ∀ z ∈ unitDiscExterior, |f z| ≤ C) → (∃ C, ∀ z ∈ unitDiscExterior, |g z| ≤ C) →
        (∀ γ ∈ Γ, ∀ z ∈ unitDiscExterior, f (mob γ z) = f z) →
        (∀ γ ∈ Γ, ∀ z ∈ unitDiscExterior, g (mob γ z) = g z) →
        inner ℝ (L g) (invariantProjection ρ (L f)) =
            (∫ z in fundDomain Γ, f z * rho z) * (∫ z in fundDomain Γ, g z * rho z) / (hypArea Γ).toReal ∧
          ∀ u ∈ Ioo (0 : ℝ) 1,
            (∫ z in fundDomain Γ, (∫ θ in (0 : ℝ)..2 * π,
                f ((z * (exp (θ * I) / u) + 1) / (exp (θ * I) / u + conj z))) / (2 * π) * g z * rho z) =
              inner ℝ (L g) (ρ (mautnerDiag (√((1 - u) / (1 + u))))⁻¹ (L f))) :
    ∀ f g : ℂ → ℝ, Measurable f → Measurable g →
      (∃ C, ∀ z ∈ unitDiscExterior, |f z| ≤ C) → (∃ C, ∀ z ∈ unitDiscExterior, |g z| ≤ C) →
      (∀ γ ∈ Γ, ∀ z ∈ unitDiscExterior, f (mob γ z) = f z) →
      (∀ γ ∈ Γ, ∀ z ∈ unitDiscExterior, g (mob γ z) = g z) →
      Tendsto (fun s : ℝ => ∫ z in fundDomain Γ,
          (∫ w in {w | w ∈ unitDiscExterior ∧ ‖w - z‖ ≤ s * ‖w * conj z - 1‖}, f w * rho w) /
            (4 * π * s ^ 2 / (1 - s ^ 2)) * g z * rho z)
        (𝓝[<] 1)
        (𝓝 ((∫ z in fundDomain Γ, f z * rho z) * (∫ z in fundDomain Γ, g z * rho z) / (hypArea Γ).toReal)) := by
  obtain ⟨X, _, μ, ρ, L, hcont, hP⟩ := hrep
  intro f g hfm hgm hfb hgb hfa hga
  obtain ⟨hE, hS⟩ := hP f g hfm hgm hfb hgb hfa hga
  obtain ⟨Cf, hCf⟩ := hfb
  obtain ⟨Cg, hCg⟩ := hgb
  have hFm := fundDomain_measurable Γ
  have hFsub := fundDomain_subset Γ
  have hρF : IntegrableOn rho (fundDomain Γ) := rho_integrableOn_fundDomain hΓ
  set w : ℝ → ℝ := fun u => 4 * u / (1 - u ^ 2) ^ 2 with hwdef
  set c : ℝ → ℝ := fun u => inner ℝ (L g) (ρ (mautnerDiag (√((1 - u) / (1 + u))))⁻¹ (L f)) with hcdef
  set Ψ : ℂ → ℝ → ℝ := fun z u => ∫ θ in (0 : ℝ)..2 * π,
    f ((z * (exp (θ * I) / u) + 1) / (exp (θ * I) / u + conj z)) with hΨdef
  obtain ⟨hΨm, hΨb⟩ := s19c_Psi hfm hCf
  set C' := 2 * π * max Cf |f 0| with hC'def
  have hCg0 : 0 ≤ max Cg 0 := le_max_right _ _
  -- the limit of the diagonal coefficients
  have ha : Tendsto (fun u : ℝ => √((1 - u) / (1 + u))) (𝓝[<] 1) (𝓝[≠] 0) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · have hca : ContinuousAt (fun u : ℝ => √((1 - u) / (1 + u))) 1 :=
        ((continuousAt_const.sub continuousAt_id).div (continuousAt_const.add continuousAt_id)
          (by norm_num)).sqrt
      simpa using hca.tendsto.mono_left nhdsWithin_le_nhds
    · filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with u hu
      exact (Real.sqrt_pos.mpr (div_pos (by linarith [hu.2]) (by linarith [hu.1]))).ne'
  have hclim : Tendsto c (𝓝[<] 1)
      (𝓝 ((∫ z in fundDomain Γ, f z * rho z) * (∫ z in fundDomain Γ, g z * rho z) / (hypArea Γ).toReal)) := by
    have h := (diagonal_matrix_coeff_tendsto_projection ρ hcont (L f) (L g)).comp ha
    rw [hE] at h
    exact h
  have hcb : ∀ u, |c u| ≤ ‖L g‖ * ‖L f‖ := fun u => by
    rw [hcdef]
    refine (abs_real_inner_le_norm _ _).trans_eq ?_
    rw [LinearIsometryEquiv.norm_map]
  -- Fubini on `F × (0, s)` and the radial formula
  have hQ : ∀ s ∈ Ioo (0 : ℝ) 1,
      IntegrableOn (fun u => w u * c u) (Ioo 0 s) ∧
      (∫ z in fundDomain Γ,
          (∫ w in {w | w ∈ unitDiscExterior ∧ ‖w - z‖ ≤ s * ‖w * conj z - 1‖}, f w * rho w) /
            (4 * π * s ^ 2 / (1 - s ^ 2)) * g z * rho z) =
        (∫ u in Ioo 0 s, w u * c u) / (∫ u in Ioo 0 s, w u) := by
    intro s hs
    obtain ⟨hwI, hWv⟩ := s19c_W hs.1 hs.2
    have hA : 4 * π * s ^ 2 / (1 - s ^ 2) = 2 * π * (∫ u in Ioo 0 s, w u) := by
      rw [hWv]
      ring
    set Φ : ℂ → ℝ → ℝ := fun z u => w u * Ψ z u * g z * rho z with hΦdef
    have hmeasΦ : Measurable (Function.uncurry Φ) := by
      have hw : Measurable w := by rw [hwdef]; fun_prop
      exact (((hw.comp measurable_snd).mul hΨm).mul (hgm.comp measurable_fst)).mul
        (s19m_rho_measurable.comp measurable_fst)
    have hint : Integrable (Function.uncurry Φ)
        ((volume.restrict (fundDomain Γ)).prod (volume.restrict (Ioo 0 s))) := by
      refine Integrable.mono' ((hρF.const_mul (C' * max Cg 0)).mul_prod hwI) hmeasΦ.aestronglyMeasurable ?_
      rw [Measure.prod_restrict]
      filter_upwards [ae_restrict_mem (hFm.prod measurableSet_Ioo)] with p hp
      obtain ⟨hz, hu⟩ := hp
      have hwu : 0 ≤ w p.2 := div_nonneg (by linarith [hu.1]) (sq_nonneg _)
      have hρ0 : 0 ≤ rho p.1 := div_nonneg (by norm_num) (sq_nonneg _)
      have h1 := hΨb p.1 (hFsub hz) p.2 ⟨hu.1, lt_trans hu.2 hs.2⟩
      have h2 : |g p.1| ≤ max Cg 0 := (hCg _ (hFsub hz)).trans (le_max_left _ _)
      simp only [Function.uncurry, hΦdef, Real.norm_eq_abs, abs_mul, abs_of_nonneg hwu, abs_of_nonneg hρ0]
      calc w p.2 * |Ψ p.1 p.2| * |g p.1| * rho p.1 ≤ w p.2 * C' * max Cg 0 * rho p.1 := by
            gcongr
        _ = C' * max Cg 0 * rho p.1 * w p.2 := by ring
    -- the inner `F`-integral for fixed `u` is `w u · 2π c u`
    have hinner : ∀ u ∈ Ioo (0 : ℝ) s, (∫ z in fundDomain Γ, Φ z u) = 2 * π * (w u * c u) := by
      intro u hu
      have hS' := hS u ⟨hu.1, lt_trans hu.2 hs.2⟩
      have e : (fun z => Φ z u) = fun z => (w u * (2 * π)) * (Ψ z u / (2 * π) * g z * rho z) := by
        funext z
        rw [hΦdef]
        field_simp
      rw [e, integral_const_mul, hS']
      ring
    have hswap := integral_integral_swap hint
    have hu_int : IntegrableOn (fun u => ∫ z in fundDomain Γ, Φ z u) (Ioo 0 s) := MeasureTheory.Integrable.integral_prod_right hint
    refine ⟨?_, ?_⟩
    · have := hu_int.const_mul (1 / (2 * π))
      refine IntegrableOn.congr_fun this (fun u hu => ?_) measurableSet_Ioo
      rw [hinner u hu]
      field_simp
    · calc (∫ z in fundDomain Γ,
            (∫ w in {w | w ∈ unitDiscExterior ∧ ‖w - z‖ ≤ s * ‖w * conj z - 1‖}, f w * rho w) /
              (4 * π * s ^ 2 / (1 - s ^ 2)) * g z * rho z)
          = ∫ z in fundDomain Γ, (1 / (4 * π * s ^ 2 / (1 - s ^ 2))) * ∫ u in Ioo 0 s, Φ z u := by
            refine setIntegral_congr_fun hFm fun z hz => ?_
            rw [s19c_radial (hFsub hz) hs.1 hs.2 hfm ⟨Cf, hCf⟩, hΦdef]
            rw [integral_mul_const, integral_mul_const]
            ring
        _ = (1 / (4 * π * s ^ 2 / (1 - s ^ 2))) * ∫ u in Ioo 0 s, ∫ z in fundDomain Γ, Φ z u := by
            rw [integral_const_mul, hswap]
        _ = (1 / (4 * π * s ^ 2 / (1 - s ^ 2))) * ∫ u in Ioo 0 s, 2 * π * (w u * c u) := by
            rw [setIntegral_congr_fun measurableSet_Ioo hinner]
        _ = (∫ u in Ioo 0 s, w u * c u) / (∫ u in Ioo 0 s, w u) := by
            rw [integral_const_mul, hA]
            have : (∫ u in Ioo 0 s, w u) ≠ 0 := by
              rw [hWv]
              have : 0 < 1 - s ^ 2 := by nlinarith [hs.1, hs.2]
              exact ne_of_gt (div_pos (by nlinarith [hs.1]) this)
            field_simp
  -- `∫_0^s w = 2s²/(1 - s²) → ∞`
  have hWtop : Tendsto (fun s => ∫ u in Ioo 0 s, w u) (𝓝[<] 1) atTop := by
    have hev : ∀ᶠ s in 𝓝[<] (1 : ℝ), 2 * s ^ 2 / (1 - s ^ 2) = ∫ u in Ioo 0 s, w u := by
      filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with s hs
      exact (s19c_W hs.1 hs.2).2.symm
    refine Tendsto.congr' hev ?_
    have h1 : Tendsto (fun s : ℝ => 2 * s ^ 2) (𝓝[<] 1) (𝓝 2) := by
      have : Continuous fun s : ℝ => 2 * s ^ 2 := by fun_prop
      simpa using (this.tendsto 1).mono_left nhdsWithin_le_nhds
    have h2 : Tendsto (fun s : ℝ => 1 - s ^ 2) (𝓝[<] 1) (𝓝[>] 0) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
      · have : Continuous fun s : ℝ => 1 - s ^ 2 := by fun_prop
        simpa using (this.tendsto 1).mono_left nhdsWithin_le_nhds
      · filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with s hs
        show 0 < 1 - s ^ 2
        nlinarith [hs.1, hs.2]
    have h3 := Filter.Tendsto.pos_mul_atTop (by norm_num) h1 (tendsto_inv_nhdsGT_zero.comp h2)
    refine h3.congr fun s => ?_
    simp only [Function.comp]
    rw [div_eq_mul_inv]
  -- the weighted average converges
  have hlim := s19c_avg_limit (w := w) (c := c) (M := ‖L g‖ * ‖L f‖)
    (fun u hu => div_nonneg (by linarith [hu.1]) (sq_nonneg _))
    (fun s hs => (s19c_W hs.1 hs.2).1) (fun s hs => (hQ s hs).1) hcb hclim hWtop
  refine hlim.congr' ?_
  filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with s hs
  exact ((hQ s hs).2).symm

end TakhtajanTeo
