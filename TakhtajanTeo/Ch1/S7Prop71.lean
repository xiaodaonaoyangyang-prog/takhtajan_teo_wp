import TakhtajanTeo.Ch1.S7Eq74
import TakhtajanTeo.Ch1.SphereWeldingTransport

/-!
# Chapter 1, §7.1 — Proposition 7.1 (`p71_`, 下属1 + 下属2)

`p71_prop_7_1` is a byte-identical copy of `prop_7_1` (S7; relocated by the leader). Owners: `[W1]` 下属1,
`[W2]` 下属2.

**Route.** Transfer along `Φ(u) = cayley(ū) : 𝕌 → 𝔻*` (W-MODEL, WM1–WM5), then Proposition 7.1 in the model `𝕌`
(U1–U3).
- `S = cayley`, `S(u) = (u - i)/(u + i)`, `S'(u) = 2i/(u + i)²`; `S : 𝕌 → 𝔻`, `𝕃 → 𝔻*`. For `z ∈ 𝔻*`:
  `x = cayleyInv z ∈ 𝕃`, `y = x̄ ∈ 𝕌`, phase `c(z) = S'(x)/\overline{S'(x)}`.
- `m[g](u) = \overline{g(S(ū))} · S(u)²/\overline{S(u)}² · \overline{S'(u)}/S'(u)`, the pullback by `S` of the
  `𝔻`-part of `extA`, for a continuous representative `g` (`wr_harm_rep`); antilinear, so `m[εν] = ε̄ m[ν]`.
- `w_A(εν) ∘ S = S ∘ w_U(ε̄ m[ν])` (WM2), hence `Q_A(μ, εν)(z) = c(z) \overline{Q_U(m[μ], ε̄ m[ν])(y)}` near `ε = 0`
  (WM3), and the same phase for `∂_z̄ ρ⁻¹ ∂_z̄ G` (WM4, WM4'). The `ε`-derivatives correspond without a swap (WM5).
- In `𝕌`: (i) is (7.2) with (7.4); (ii) is (7.5) with `cor_6_4` differentiated twice in `z̄` (U1, U2).
-/

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal ComplexConjugate Classical Real
noncomputable section
namespace TakhtajanTeo
open LiZhongQC

/-! ### W-MODEL: the transfer `𝕌 → 𝔻*` `[W2]` -/

/-- (WM0) `cayley` maps `𝕃 ∖ {-i}` into `𝔻*`. -/
theorem p71_cay_ext {x : ℂ} (hx : x.im < 0) (hxI : x + I ≠ 0) : cayley x ∈ unitDiscExterior := by
  show 1 < ‖(x - I) / (x + I)‖
  rw [norm_div, one_lt_div (norm_pos_iff.mpr hxI), ← sq_lt_sq₀ (norm_nonneg _) (norm_nonneg _),
    Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply]
  simp only [Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.I_re, Complex.I_im]
  nlinarith

/-- (WM0) `cayleyInv ∘ cayley = id` off the pole. -/
theorem p71_cinv_cay {x : ℂ} (hxI : x + I ≠ 0) : cayleyInv (cayley x) = x := by
  show I * (1 + (x - I) / (x + I)) / (1 - (x - I) / (x + I)) = x
  have h2 : (2 : ℂ) * I ≠ 0 := mul_ne_zero two_ne_zero I_ne_zero
  have e1 : 1 - (x - I) / (x + I) = 2 * I / (x + I) := by field_simp; ring
  rw [e1]
  field_simp
  ring_nf

/-- (WM0) `cayley ∘ cayleyInv = id` off `1`. -/
theorem p71_cay_cinv {w : ℂ} (hw : w ≠ 1) : cayley (cayleyInv w) = w := by
  show (I * (1 + w) / (1 - w) - I) / (I * (1 + w) / (1 - w) + I) = w
  have h1 : (1 : ℂ) - w ≠ 0 := sub_ne_zero.mpr (Ne.symm hw)
  have e : I * (1 + w) / (1 - w) + I = 2 * I / (1 - w) := by field_simp; ring
  rw [e]
  have h2 : (2 : ℂ) * I ≠ 0 := mul_ne_zero two_ne_zero I_ne_zero
  field_simp
  ring

/-- (WM0) `cayleyInv` maps `𝔻*` into `𝕃`. -/
theorem p71_cinv_im {w : ℂ} (hw : 1 < ‖w‖) : (cayleyInv w).im < 0 := by
  have h1 : (1 : ℂ) - w ≠ 0 := by
    intro h; rw [sub_eq_zero] at h; rw [← h, norm_one] at hw; exact lt_irrefl _ hw
  show (I * (1 + w) / (1 - w)).im < 0
  rw [Complex.div_im]
  have hn : 0 < Complex.normSq (1 - w) := Complex.normSq_pos.mpr h1
  have hw2 : 1 < w.re * w.re + w.im * w.im := by
    have := (one_lt_sq_iff₀ (norm_nonneg w)).mpr hw
    rwa [Complex.sq_norm, Complex.normSq_apply] at this
  simp only [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im]
  rw [div_sub_div_same]
  apply div_neg_of_neg_of_pos _ hn
  nlinarith

/-- (WM0) Null sets of `𝔻*` pull back to null sets of `𝕌` along `Φ(u) = cayley(ū)`. -/
theorem p71_phi_ae {P : ℂ → Prop} (h : ∀ᵐ w ∂(volume.restrict unitDiscExterior), P w) :
    ∀ᵐ u ∂(volume.restrict upperHalf), P (cayley (conj u)) := by
  have hmE : MeasurableSet unitDiscExterior := (isOpen_lt continuous_const continuous_norm).measurableSet
  rw [ae_restrict_iff' hmE, ae_iff] at h
  rw [ae_restrict_iff' measurableSet_upperHalf_aux, ae_iff]
  have hsub : {u : ℂ | ¬(u ∈ upperHalf → P (cayley (conj u)))} ⊆
      {I} ∪ (fun w => conj (cayleyInv w)) '' ({w : ℂ | ¬(w ∈ unitDiscExterior → P w)} ∩ unitDiscExterior) := by
    intro u hu
    simp only [mem_ofPred_eq, not_imp] at hu
    by_cases hui : u = I
    · exact Or.inl hui
    · right
      have hu0 : 0 < u.im := hu.1
      have hx : conj u + I ≠ 0 := by
        intro h0
        apply hui
        have : conj (conj u) = conj (-I) := by rw [eq_neg_of_add_eq_zero_left h0]
        rwa [Complex.conj_conj, map_neg, Complex.conj_I, neg_neg] at this
      have hext : cayley (conj u) ∈ unitDiscExterior :=
        p71_cay_ext (by rw [Complex.conj_im]; linarith) hx
      refine ⟨cayley (conj u), ⟨fun h' => hu.2 (h' hext), hext⟩, ?_⟩
      show conj (cayleyInv (cayley (conj u))) = u
      rw [p71_cinv_cay hx, Complex.conj_conj]
  refine measure_mono_null hsub (measure_union_null (measure_singleton I) ?_)
  refine addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume ?_
    (measure_mono_null inter_subset_left h)
  intro w hw
  have hw1 : 1 < ‖w‖ := hw.2
  have h1 : (1 : ℂ) - w ≠ 0 := by
    intro h; rw [sub_eq_zero] at h; rw [← h, norm_one] at hw1; exact lt_irrefl _ hw1
  have hd : DifferentiableAt ℂ (fun w : ℂ => I * (1 + w) / (1 - w)) w :=
    ((differentiableAt_const _).mul ((differentiableAt_const _).add differentiableAt_id)).div
      ((differentiableAt_const _).sub differentiableAt_id) h1
  exact ((Complex.conjCLE.differentiableAt).comp w (hd.restrictScalars ℝ)).differentiableWithinAt

/-- (WM1) `[W2]` **Harmonic transfer.** [REVISED 2026-10-28, leader: `m[g]` is junk `0/0` at `u = i`; the harmonic
`m` agrees with `m[g]` off `u = i`.] If `g` is a continuous representative on `𝔻*` of `μ ∈ Ω^{-1,1}(𝔻*)`, the
pulled-back reflected part `m[g]` is a harmonic Beltrami differential of the model `𝕌`. Route: `g = (1-|z|²)² φ̄`
on `𝔻*` everywhere (continuous + a.e. equal), then `ψ(u) = -2 φ(S ū)‾…` computed via `1 - |S u|² = 4 Im u/|u + i|²`. -/
theorem p71_wm_harm {μ : LinfStar} (hμ : μ ∈ harmonicBeltrami) {g : ℂ → ℂ} (hg : ContinuousOn g unitDiscExterior)
    (hgμ : ∀ᵐ z ∂(volume.restrict unitDiscExterior), μ z = g z) :
    ∃ m φ : ℂ → ℂ, IsHarmonicU m φ ∧ ∀ u ∈ upperHalf, u ≠ I →
      m u = conj (g (cayley (conj u))) * (cayley u ^ 2 / conj (cayley u) ^ 2) *
        (conj (2 * I / (u + I) ^ 2) / (2 * I / (u + I) ^ 2)) := by
  -- `φD` is the reflection of `φ0` to `𝔻` (apparent singularity at `0` removed); `ψ(u) = -4 φD(S u)/(u + i)⁴` has
  -- no pole at `u = i` (where `Φ(i) = ∞`), and agrees with the pullback of `g` off `i`.
  obtain ⟨φ0, hφ0⟩ := (mem_harmonicBeltrami_iff μ).1 hμ
  have hEo : IsOpen unitDiscExterior := isOpen_lt continuous_const continuous_norm
  have hφ0d : DifferentiableOn ℂ (AInf.toFun φ0) unitDiscExterior := φ0.2
  have hrc : ContinuousOn (fun z : ℂ => ((1 - ‖z‖ ^ 2) ^ 2 : ℂ) * conj (AInf.toFun φ0 z)) unitDiscExterior :=
    (by fun_prop : Continuous fun z : ℂ => ((1 - ‖z‖ ^ 2) ^ 2 : ℂ)).continuousOn.mul
      (Complex.continuous_conj.comp_continuousOn hφ0d.continuousOn)
  have hEq : EqOn g (fun z : ℂ => ((1 - ‖z‖ ^ 2) ^ 2 : ℂ) * conj (AInf.toFun φ0 z)) unitDiscExterior := by
    refine Measure.eqOn_open_of_ae_eq (μ := (volume : Measure ℂ)) ?_ hEo hg hrc
    filter_upwards [hgμ, hφ0] with z h1 h2
    rw [← h1, h2]
  obtain ⟨φD, hφD⟩ := exists_reverse_reflected_differential φ0
  refine ⟨fun u => (u - conj u) ^ 2 / 2 * conj (-4 * AInf.toFun φD (cayley u) / (u + I) ^ 4),
    fun u => -4 * AInf.toFun φD (cayley u) / (u + I) ^ 4, ⟨?_, ?_, fun z _ => rfl⟩, ?_⟩
  · intro u hu
    have hu0 : 0 < u.im := hu
    have hcd : DifferentiableAt ℂ cayley u := by
      show DifferentiableAt ℂ (fun z => (z - I) / (z + I)) u
      exact (differentiableAt_id.sub_const I).div (differentiableAt_id.add_const I) (cayley_den_ne_zero hu0)
    have hφd : DifferentiableAt ℂ (AInf.toFun φD) (cayley u) :=
      (φD.2 : DifferentiableOn ℂ (AInf.toFun φD) unitDisc).differentiableAt
        (isOpen_ball.mem_nhds (cayley_mem_unitDisc hu0))
    exact (((differentiableAt_const _).mul (hφd.comp u hcd)).div ((differentiableAt_id.add_const I).pow 4)
      (pow_ne_zero _ (cayley_den_ne_zero hu0))).differentiableWithinAt
  · refine ⟨‖φD.1‖, fun u hu => ?_⟩
    have hu0 : 0 < u.im := hu
    have hs : cayley u ∈ unitDisc := cayley_mem_unitDisc hu0
    have hs1 : ‖cayley u‖ < 1 := by simpa [unitDisc] using hs
    have h1 : u + I ≠ 0 := cayley_den_ne_zero hu0
    have hN : 0 < ‖u + I‖ := norm_pos_iff.mpr h1
    have hkey : (1 - ‖cayley u‖ ^ 2) * ‖u + I‖ ^ 2 = 4 * u.im := by
      show (1 - ‖(u - I) / (u + I)‖ ^ 2) * ‖u + I‖ ^ 2 = 4 * u.im
      rw [norm_div, div_pow, sub_mul, div_mul_cancel₀ _ (by positivity), Complex.sq_norm, Complex.sq_norm,
        Complex.normSq_apply, Complex.normSq_apply]
      simp only [Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.I_re, Complex.I_im]
      ring
    have hD : 0 < 1 - ‖cayley u‖ ^ 2 := by nlinarith [norm_nonneg (cayley u)]
    have h16 : (1 - ‖cayley u‖ ^ 2) ^ 2 * ‖u + I‖ ^ 4 = 16 * u.im ^ 2 := by
      rw [show (1 - ‖cayley u‖ ^ 2) ^ 2 * ‖u + I‖ ^ 4 = ((1 - ‖cayley u‖ ^ 2) * ‖u + I‖ ^ 2) ^ 2 by ring, hkey]
      ring
    have hval : AInf.toFun φD (cayley u) = φD.1 ⟨cayley u, hs⟩ / ((1 - ‖cayley u‖ ^ 2) ^ 2 : ℂ) := by
      show unweight unitDisc φD.1 (cayley u) = _
      simp only [unweight, dif_pos hs]
    have hnD : ‖((1 - ‖cayley u‖ ^ 2) ^ 2 : ℂ)‖ = (1 - ‖cayley u‖ ^ 2) ^ 2 := by
      rw [show ((1 - ‖cayley u‖ ^ 2) ^ 2 : ℂ) = (((1 - ‖cayley u‖ ^ 2) ^ 2 : ℝ) : ℂ) by push_cast; ring,
        Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    have hP : ‖φD.1 ⟨cayley u, hs⟩‖ ≤ ‖φD.1‖ := BoundedContinuousFunction.norm_coe_le_norm _ _
    have hn4 : ‖(-4 : ℂ)‖ = 4 := by rw [norm_neg]; norm_num
    have hnim : ‖((u.im : ℂ)) ^ 2‖ = u.im ^ 2 := by rw [norm_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
    rw [norm_mul, hnim, norm_div, norm_mul, hn4, hval, norm_div, hnD, norm_pow]
    calc u.im ^ 2 * (4 * (‖φD.1 ⟨cayley u, hs⟩‖ / (1 - ‖cayley u‖ ^ 2) ^ 2) / ‖u + I‖ ^ 4)
        = 4 * u.im ^ 2 * ‖φD.1 ⟨cayley u, hs⟩‖ / ((1 - ‖cayley u‖ ^ 2) ^ 2 * ‖u + I‖ ^ 4) := by
          field_simp
      _ = 4 * u.im ^ 2 * ‖φD.1 ⟨cayley u, hs⟩‖ / (16 * u.im ^ 2) := by rw [h16]
      _ = ‖φD.1 ⟨cayley u, hs⟩‖ / 4 := by field_simp; ring
      _ ≤ ‖φD.1‖ := by linarith [norm_nonneg (φD.1 ⟨cayley u, hs⟩)]
  · intro u hu hui
    have hu0 : 0 < u.im := hu
    have h1 : u + I ≠ 0 := cayley_den_ne_zero hu0
    have h2 : u - I ≠ 0 := sub_ne_zero.mpr hui
    have h3 : conj u + I ≠ 0 := by
      intro h0
      apply hui
      have : conj (conj u) = conj (-I) := by rw [eq_neg_of_add_eq_zero_left h0]
      rwa [Complex.conj_conj, map_neg, Complex.conj_I, neg_neg] at this
    have h4 : conj u - I ≠ 0 := by
      intro h0
      have := congrArg Complex.im h0
      simp only [Complex.sub_im, Complex.conj_im, Complex.I_im, Complex.zero_im] at this
      linarith
    have hs0 : cayley u ≠ 0 := by
      show (u - I) / (u + I) ≠ 0
      exact div_ne_zero h2 h1
    have h1' : u - -I ≠ 0 := by rwa [sub_neg_eq_add]
    have h2' : u + -I ≠ 0 := by rwa [← sub_eq_add_neg]
    have h3' : conj u - -I ≠ 0 := by rwa [sub_neg_eq_add]
    have h4' : conj u + -I ≠ 0 := by rwa [← sub_eq_add_neg]
    have hw : cayley (conj u) ∈ unitDiscExterior := p71_cay_ext (by rw [Complex.conj_im]; linarith) h3
    have hrefl : refl (cayley u) = cayley (conj u) := by
      show (conj ((u - I) / (u + I)))⁻¹ = (conj u - I) / (conj u + I)
      rw [map_div₀, map_sub, map_add, Complex.conj_I, inv_div]
      ring
    have hD := hφD (cayley u) (cayley_mem_unitDisc hu0) hs0
    rw [hrefl] at hD
    have hg' := hEq hw
    simp only at hg'
    show (u - conj u) ^ 2 / 2 * conj (-4 * AInf.toFun φD (cayley u) / (u + I) ^ 4) = _
    have hW : 1 - cayley (conj u) * conj (cayley (conj u)) = 2 * I * (u - conj u) / ((conj u + I) * (u - I)) := by
      show 1 - (conj u - I) / (conj u + I) * conj ((conj u - I) / (conj u + I)) = _
      rw [map_div₀, map_sub, map_add, Complex.conj_I, Complex.conj_conj]
      field_simp
      ring
    rw [hD, hg', ← Complex.mul_conj', hW]
    generalize AInf.toFun φ0 (cayley (conj u)) = a
    rw [div_pow, mul_pow, mul_pow, Complex.I_sq]
    simp only [cayley, map_div₀, map_mul, map_sub, map_add, map_neg, map_pow, map_ofNat, map_one,
      Complex.conj_I, Complex.conj_conj]
    field_simp
    ring

/-- (WM2) Plane null sets pull back to null sets along `cayley`. -/
theorem p71_cay_null {P : ℂ → Prop} (h : ∀ᵐ z, P z) : ∀ᵐ x, P (cayley x) := by
  rw [ae_iff] at h ⊢
  have hsub : {x : ℂ | ¬P (cayley x)} ⊆ {-I} ∪ cayleyInv '' ({z | ¬P z} ∩ {z | z ≠ 1}) := by
    intro x hx
    by_cases hxI : x + I = 0
    · left
      show x = -I
      linear_combination hxI
    · right
      have h1 : cayley x ≠ 1 := by
        show (x - I) / (x + I) ≠ 1
        intro h
        rw [div_eq_iff hxI] at h
        have h2 : (2 : ℂ) * I = 0 := by linear_combination -h
        simp at h2
      exact ⟨cayley x, ⟨hx, h1⟩, p71_cinv_cay hxI⟩
  refine measure_mono_null hsub (measure_union_null (measure_singleton _) ?_)
  refine addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume ?_
    (measure_mono_null inter_subset_left h)
  intro w hw
  have h1 : (1 : ℂ) - w ≠ 0 := sub_ne_zero.mpr (Ne.symm hw.2)
  have hd : DifferentiableAt ℂ (fun w : ℂ => I * (1 + w) / (1 - w)) w :=
    ((differentiableAt_const _).mul ((differentiableAt_const _).add differentiableAt_id)).div
      ((differentiableAt_const _).sub differentiableAt_id) h1
  exact (hd.restrictScalars ℝ).differentiableWithinAt

/-- (WM2) The Model A coefficient of `εν` in terms of a representative `g` of `ν`. -/
theorem p71_extA_g {ν : LinfStar} {g : ℂ → ℂ} (hgν : ∀ᵐ z ∂(volume.restrict unitDiscExterior), ν z = g z)
    (ε : ℂ) :
    ∀ᵐ z, extA (ε • ν) z = ε * (if 1 < ‖z‖ then g z else 0) +
      conj ε * (if ‖z‖ < 1 then conj (g (refl z)) * z ^ 2 / conj z ^ 2 else 0) := by
  have hmE : MeasurableSet unitDiscExterior := (isOpen_lt continuous_const continuous_norm).measurableSet
  have h1 : ∀ᵐ z, z ∈ unitDiscExterior → ν z = g z := (ae_restrict_iff' hmE).1 hgν
  have h2 := ae_refl h1
  have hne : ∀ᵐ z : ℂ, z ≠ 0 := compl_mem_ae_iff.2 (measure_singleton 0)
  filter_upwards [wr_extA_smul ε ν, h1, h2, hne] with z hz e1 e2 hz0
  rw [hz]
  by_cases ha : 1 < ‖z‖
  · have hb : ¬ ‖z‖ < 1 := not_lt.mpr ha.le
    rw [if_pos ha, if_pos ha, e1 ha, if_neg hb, if_neg hb]
  · rw [if_neg ha, if_neg ha]
    by_cases hb : ‖z‖ < 1
    · have hr : refl z ∈ unitDiscExterior := by
        show 1 < ‖refl z‖
        rw [norm_refl]
        exact (one_lt_inv₀ (norm_pos_iff.mpr hz0)).mpr hb
      rw [if_pos hb, if_pos hb, e2 hr]
    · rw [if_neg hb, if_neg hb]

/-- (WM2) **Coefficient identity.** `S^*(extA (εν)) = extU (ε̄ m[g])` a.e.: the pullback by the Cayley map `S` of the
Model A coefficient is the model `𝕌` coefficient of `ε̄ m[g]`. -/
theorem p71_coef {ν : LinfStar} {g : ℂ → ℂ} (hgν : ∀ᵐ z ∂(volume.restrict unitDiscExterior), ν z = g z)
    (ε : ℂ) :
    ∀ᵐ x, extA (ε • ν) (cayley x) * (conj (2 * I / (x + I) ^ 2) / (2 * I / (x + I) ^ 2)) =
      extU (fun u => conj ε * (conj (g (cayley (conj u))) * (cayley u ^ 2 / conj (cayley u) ^ 2) *
        (conj (2 * I / (u + I) ^ 2) / (2 * I / (u + I) ^ 2)))) x := by
  have hre : ∀ᵐ x : ℂ, x.im ≠ 0 := by
    rw [ae_iff]
    simpa only [ne_eq, not_not] using gzE_volume_im_eq_zero
  filter_upwards [p71_cay_null (p71_extA_g hgν ε), hre, Measure.ae_ne volume I, Measure.ae_ne volume (-I)]
    with x hx hxi hxI1 hxI2
  rw [hx]
  have h1 : x + I ≠ 0 := by
    intro h; apply hxI2; linear_combination h
  have h2 : x - I ≠ 0 := sub_ne_zero.mpr hxI1
  have h3 : conj x + I ≠ 0 := by
    intro h; apply hxI1
    have : conj (conj x) = conj (-I) := by rw [eq_neg_of_add_eq_zero_left h]
    rwa [Complex.conj_conj, map_neg, Complex.conj_I, neg_neg] at this
  have h4 : conj x - I ≠ 0 := by
    intro h; apply hxI2
    have : conj (conj x) = conj I := by rw [sub_eq_zero.mp h]
    rwa [Complex.conj_conj, Complex.conj_I] at this
  have h1' : x - -I ≠ 0 := by rwa [sub_neg_eq_add]
  have h2' : x + -I ≠ 0 := by rwa [← sub_eq_add_neg]
  have h3' : conj x - -I ≠ 0 := by rwa [sub_neg_eq_add]
  have h4' : conj x + -I ≠ 0 := by rwa [← sub_eq_add_neg]
  unfold extU
  rcases lt_or_gt_of_ne hxi with hneg | hpos
  · have hc : 1 < ‖cayley x‖ := p71_cay_ext hneg h1
    have hc' : ¬ ‖cayley x‖ < 1 := not_lt.mpr hc.le
    rw [if_pos hc, if_neg hc', if_neg (not_lt.mpr hneg.le), if_pos hneg]
    simp only [Complex.conj_conj]
    have hI : I ≠ 0 := I_ne_zero
    have key : conj (cayley (conj x) ^ 2 / conj (cayley (conj x)) ^ 2) *
        conj (conj (2 * I / (conj x + I) ^ 2) / (2 * I / (conj x + I) ^ 2)) =
        conj (2 * I / (x + I) ^ 2) / (2 * I / (x + I) ^ 2) := by
      simp only [cayley, map_mul, map_div₀, map_sub, map_add, map_neg, map_pow, map_ofNat, Complex.conj_I,
        Complex.conj_conj]
      field_simp
      ring
    simp only [map_mul, Complex.conj_conj, mul_zero, add_zero]
    rw [← key]
    ring
  · have hc : ‖cayley x‖ < 1 := mem_ball_zero_iff.mp (cayley_mem_unitDisc hpos)
    have hrefl : refl (cayley x) = cayley (conj x) := by
      show (conj ((x - I) / (x + I)))⁻¹ = (conj x - I) / (conj x + I)
      rw [map_div₀, map_sub, map_add, Complex.conj_I, inv_div]
      ring
    rw [if_neg (not_lt.mpr hc.le), if_pos hc, if_pos hpos, hrefl]
    ring

/-- (WM2) The sphere extension of `cayley` at finite points off its pole. -/
theorem p71_S_coe {x : ℂ} (h : x + I ≠ 0) : mobiusExt 1 (-I) 1 I (x : ExtPlane) = ((cayley x : ℂ) : ExtPlane) := by
  rw [mobiusExt_coe (by rwa [one_mul])]
  congr 1
  show (1 * x + -I) / (1 * x + I) = (x - I) / (x + I)
  ring_nf

/-- (WM2) `S ∘ S⁻¹ = id` on the sphere. -/
theorem p71_S_inv (q : ExtPlane) : mobiusExt 1 (-I) 1 I (mobiusExt I I (-1) 1 q) = q := by
  have := mobiusExt_inv_apply (a := I) (b := I) (c := -1) (d := 1) cayley_det q
  simpa only [neg_neg] using this

/-- (WM2) The derivative of `cayley`. -/
theorem p71_cay_hasDeriv {x : ℂ} (h : x + I ≠ 0) : HasDerivAt cayley (2 * I / (x + I) ^ 2) x := by
  have h1 : (1 : ℂ) * x + I ≠ 0 := by rwa [one_mul]
  have hd := bc_mobiusFn_hasDerivAt (a := 1) (b := -I) h1
  have e : mobiusFn 1 (-I) 1 I = cayley := by
    funext y
    show (1 * y + -I) / (1 * y + I) = (y - I) / (y + I)
    ring_nf
  rw [e] at hd
  convert hd using 1
  ring

/-- (WM2) `[W2]` **Conjugation of the normalized maps.** For `‖ε‖‖ν‖ < 1`, `w_A(εν) ∘ S = S ∘ w_U(ε̄ m[g])` on the
sphere (`S = mobiusExt 1 (-I) 1 I`, the extension of `cayley`). Route: `H = S⁻¹ ∘ wAS(εν) ∘ S` fixes `0, 1, ∞`; it is
q.c. off two points (`isKQC_one_of_conformal`, `thm7_1_comp`, `s13x_removable`) with dilatation
`extU (ε̄ m[g])` a.e. (`complexDilatation_comp_conformal_left/right`, WM1's coefficient identity); then
`thm13_5_uniqueness_plane`. -/
theorem p71_wm_conj {ν : LinfStar} (hν : ν ∈ harmonicBeltrami) {g : ℂ → ℂ} (hg : ContinuousOn g unitDiscExterior)
    (hgν : ∀ᵐ z ∂(volume.restrict unitDiscExterior), ν z = g z) {ε : ℂ} (hε : ‖ε‖ * ‖ν‖ < 1) (x : ℂ) :
    wAS (ε • ν) (mobiusExt 1 (-I) 1 I (x : ExtPlane)) =
      mobiusExt 1 (-I) 1 I ((wU (fun u => conj ε * (conj (g (cayley (conj u))) *
        (cayley u ^ 2 / conj (cayley u) ^ 2) * (conj (2 * I / (u + I) ^ 2) / (2 * I / (u + I) ^ 2)))) x : ℂ) :
          ExtPlane) := by
  -- `H = S⁻¹ ∘ wAS(εν) ∘ S` fixes `0, 1, ∞` (since `wAS(εν)` fixes `S 0 = -1`, `S 1 = -i`, `S ∞ = 1`); it is a
  -- normalized plane solution of `extU (ε̄ m[g])`, hence equals `wU (ε̄ m[g])` (`thm13_5_uniqueness_plane`).
  have hρ : ε • ν ∈ LinfStarBall := by
    show ε • ν ∈ ball (0 : LinfStar) 1
    rw [mem_ball_zero_iff, norm_smul]
    exact hε
  obtain ⟨M, hM, W, hW, hfin, -, hm1, hmI, hp1⟩ := wA_spec hρ
  obtain ⟨Mi, hMi, hMiM, hMMi⟩ := isMobius_inverse hM
  obtain ⟨K, hK⟩ := hW.1
  have hS : IsMobius (mobiusExt 1 (-I) 1 I) := ⟨1, -I, 1, I, cayley_inv_det, rfl⟩
  have hSi : IsMobius (mobiusExt I I (-1) 1) := ⟨I, I, -1, 1, cayley_det, rfl⟩
  have hN : IsMobius (fun p => mobiusExt I I (-1) 1 (M p)) := isMobius_comp hM hSi
  have hGb : Function.Bijective (fun p => Mi (wAS (ε • ν) p)) :=
    (mobius_sphere_continuous_bijective hMi).2.comp (wAS_bijective _)
  have hGc : Continuous (fun p => Mi (wAS (ε • ν) p)) :=
    (mobius_sphere_continuous_bijective hMi).1.comp (wAS_continuous hρ)
  have hg : ∀ z : ℂ, (fun p => Mi (wAS (ε • ν) p)) (z : ExtPlane) = ((W z : ℂ) : ExtPlane) := fun z => by
    show Mi (wAS (ε • ν) z) = _
    rw [hfin z, hMiM]
  have hS1 : mobiusExt 1 (-I) 1 I extInf = ((1 : ℂ) : ExtPlane) := by
    rw [mobiusExt_infty_of_ne one_ne_zero, div_one]
  have hSi1 : mobiusExt I I (-1) 1 ((1 : ℂ) : ExtPlane) = extInf := mobiusExt_coe_of_eq_zero (by ring)
  have hi : (fun p => mobiusExt I I (-1) 1 (M p)) ((fun p => Mi (wAS (ε • ν) p))
      (mobiusExt 1 (-I) 1 I extInf)) = extInf := by
    show mobiusExt I I (-1) 1 (M (Mi (wAS (ε • ν) (mobiusExt 1 (-I) 1 I extInf)))) = extInf
    rw [hMMi, hS1, hp1, hSi1]
  have hKH : IsKQC (fun z : ℂ => finPart (mobiusExt I I (-1) 1 (wAS (ε • ν) (mobiusExt 1 (-I) 1 I z)))) univ K := by
    have h0 := sphereTransport_isKQC hGb hGc hg hK hS hN hi
    have e : (fun z : ℂ => finPart ((fun p => mobiusExt I I (-1) 1 (M p))
        ((fun p => Mi (wAS (ε • ν) p)) (mobiusExt 1 (-I) 1 I (z : ExtPlane))))) =
        fun z : ℂ => finPart (mobiusExt I I (-1) 1 (wAS (ε • ν) (mobiusExt 1 (-I) 1 I z))) :=
      funext fun z => by
        show finPart (mobiusExt I I (-1) 1 (M (Mi _))) = _
        rw [hMMi]
    rwa [e] at h0
  have hFb : Function.Bijective (fun p => mobiusExt I I (-1) 1 (wAS (ε • ν) (mobiusExt 1 (-I) 1 I p))) :=
    (mobius_sphere_continuous_bijective hSi).2.comp
      ((wAS_bijective _).comp (mobius_sphere_continuous_bijective hS).2)
  have hFc : Continuous (fun p => mobiusExt I I (-1) 1 (wAS (ε • ν) (mobiusExt 1 (-I) 1 I p))) :=
    (mobius_sphere_continuous_bijective hSi).1.comp
      ((wAS_continuous hρ).comp (mobius_sphere_continuous_bijective hS).1)
  have hFi : (fun p => mobiusExt I I (-1) 1 (wAS (ε • ν) (mobiusExt 1 (-I) 1 I p))) extInf = extInf := by
    show mobiusExt I I (-1) 1 (wAS (ε • ν) (mobiusExt 1 (-I) 1 I extInf)) = extInf
    rw [hS1, hp1, hSi1]
  have hHom := sphereFinite_homeomorph hFb hFc hFi
  have hI1 : (1 : ℂ) + I ≠ 0 := by
    intro h; have := congrArg Complex.im h; simp at this
  have hH0 : finPart (mobiusExt I I (-1) 1 (wAS (ε • ν) (mobiusExt 1 (-I) 1 I ((0 : ℂ) : ExtPlane)))) = 0 := by
    have hc0 : cayley 0 = -1 := by
      show ((0 : ℂ) - I) / (0 + I) = -1
      rw [zero_sub, zero_add, neg_div, div_self I_ne_zero]
    rw [p71_S_coe (by simp), hc0, hm1, mobiusExt_coe (by norm_num)]
    show ((I * -1 + I) / (-1 * -1 + 1) : ℂ) = 0
    ring
  have hH1 : finPart (mobiusExt I I (-1) 1 (wAS (ε • ν) (mobiusExt 1 (-I) 1 I ((1 : ℂ) : ExtPlane)))) = 1 := by
    have hc1 : cayley 1 = -I := by
      show ((1 : ℂ) - I) / (1 + I) = -I
      rw [div_eq_iff hI1]
      linear_combination Complex.I_sq
    have hd : (-1 : ℂ) * -I + 1 ≠ 0 := by
      intro h; have := congrArg Complex.im h; simp at this
    rw [p71_S_coe hI1, hc1, hmI, mobiusExt_coe hd]
    show ((I * -I + I) / (-1 * -I + 1) : ℂ) = 1
    rw [div_eq_one_iff_eq hd]
    linear_combination -Complex.I_sq
  have hWd : ∀ᵐ z, DifferentiableAt ℝ W z := by
    have := thm9_3_differentiable_ae hK
    rwa [Measure.restrict_univ] at this
  have hWc : Continuous W := continuousOn_univ.mp hK.2.2.1.1
  obtain ⟨a', b', c', d', hdet', hNe⟩ := hN
  have hdil : ∀ᵐ x, complexDilatation
      (fun z : ℂ => finPart (mobiusExt I I (-1) 1 (wAS (ε • ν) (mobiusExt 1 (-I) 1 I z)))) x =
      extU (fun u => conj ε * (conj (g (cayley (conj u))) * (cayley u ^ 2 / conj (cayley u) ^ 2) *
        (conj (2 * I / (u + I) ^ 2) / (2 * I / (u + I) ^ 2)))) x := by
    filter_upwards [p71_cay_null hWd, p71_cay_null hW.2.2.2.2, p71_coef hgν ε, Measure.ae_ne volume (-I)]
      with x hxd hxμ hxc hxI
    have h1 : x + I ≠ 0 := by
      intro h; apply hxI; linear_combination h
    have hNx : ∀ w : ℂ, mobiusExt I I (-1) 1 (M (w : ExtPlane)) = mobiusExt a' b' c' d' (w : ExtPlane) :=
      fun w => congrFun hNe (w : ExtPlane)
    have hpole : c' * W (cayley x) + d' ≠ 0 := by
      intro h0
      have e1 := mobiusExt_coe_of_eq_zero (a := a') (b := b') h0
      rw [← hNx, ← hfin, ← p71_S_coe h1] at e1
      have e2 := congrArg (mobiusExt 1 (-I) 1 I) e1
      rw [p71_S_inv, hS1, ← hp1] at e2
      have e3 := congrArg (mobiusExt I I (-1) 1) ((wAS_bijective _).1 e2)
      rw [cayley_apply_inv, hSi1] at e3
      exact OnePoint.coe_ne_infty x e3
    have hcay : HasDerivAt cayley (2 * I / (x + I) ^ 2) x := p71_cay_hasDeriv h1
    have hloc : (fun z : ℂ => finPart (mobiusExt I I (-1) 1 (wAS (ε • ν) (mobiusExt 1 (-I) 1 I z)))) =ᶠ[𝓝 x]
        fun y => mobiusFn a' b' c' d' (W (cayley y)) := by
      have hc1 : ContinuousAt (fun y => c' * W (cayley y) + d') x :=
        (continuousAt_const.mul (hWc.continuousAt.comp hcay.continuousAt)).add continuousAt_const
      have hc2 : ContinuousAt (fun y : ℂ => y + I) x := continuousAt_id.add continuousAt_const
      filter_upwards [hc1.eventually_ne hpole, hc2.eventually_ne h1] with y hy1 hy2
      show finPart (mobiusExt I I (-1) 1 (wAS (ε • ν) (mobiusExt 1 (-I) 1 I (y : ExtPlane)))) = _
      rw [p71_S_coe hy2, hfin, hNx, mobiusExt_coe hy1]
      rfl
    have hcd : complexDilatation
        (fun z : ℂ => finPart (mobiusExt I I (-1) 1 (wAS (ε • ν) (mobiusExt 1 (-I) 1 I z)))) x =
        complexDilatation (fun y => mobiusFn a' b' c' d' (W (cayley y))) x := by
      simp only [complexDilatation, dz, dzbar, hloc.fderiv_eq]
    have hmd := bc_mobiusFn_hasDerivAt (a := a') (b := b') hpole
    have hl := complexDilatation_comp_conformal_left (f := fun y => W (cayley y)) (g := mobiusFn a' b' c' d')
      (z := x) (hxd.comp x (hcay.differentiableAt.restrictScalars ℝ)) hmd.differentiableAt
      (by rw [hmd.deriv]; exact div_ne_zero hdet' (pow_ne_zero _ hpole))
    have hr := complexDilatation_comp_conformal_right (f := cayley) (g := W) (z := x) hcay.differentiableAt
      (by rw [hcay.deriv]; exact div_ne_zero (mul_ne_zero two_ne_zero I_ne_zero) (pow_ne_zero _ h1)) hxd
    rw [hcd]
    rw [show (fun y => mobiusFn a' b' c' d' (W (cayley y))) = mobiusFn a' b' c' d' ∘ fun y => W (cayley y) from rfl,
      hl, show (fun y => W (cayley y)) = W ∘ cayley from rfl, hr, hcay.deriv, hxμ]
    exact hxc
  have hNS : IsNormalizedSolution
      (fun z : ℂ => finPart (mobiusExt I I (-1) 1 (wAS (ε • ν) (mobiusExt 1 (-I) 1 I z))))
      (extU (fun u => conj ε * (conj (g (cayley (conj u))) * (cayley u ^ 2 / conj (cayley u) ^ 2) *
        (conj (2 * I / (u + I) ^ 2) / (2 * I / (u + I) ^ 2))))) :=
    ⟨⟨K, hKH⟩, hHom.2.2.1, hH0, hH1, hdil⟩
  have hV : wU (fun u => conj ε * (conj (g (cayley (conj u))) * (cayley u ^ 2 / conj (cayley u) ^ 2) *
      (conj (2 * I / (u + I) ^ 2) / (2 * I / (u + I) ^ 2)))) =
      fun z : ℂ => finPart (mobiusExt I I (-1) 1 (wAS (ε • ν) (mobiusExt 1 (-I) 1 I z))) := by
    have hex : ∃ f, IsNormalizedSolution f (extU (fun u => conj ε * (conj (g (cayley (conj u))) *
        (cayley u ^ 2 / conj (cayley u) ^ 2) * (conj (2 * I / (u + I) ^ 2) / (2 * I / (u + I) ^ 2))))) :=
      ⟨_, hNS⟩
    show normalizedSolution _ = _
    rw [normalizedSolution, dif_pos hex]
    have hc := hex.choose_spec
    refine (thm13_5_uniqueness_plane hNS.1 hc.1 hNS.2.1 hc.2.1 ?_ hNS.2.2.1 hNS.2.2.2.1 hc.2.2.1
      hc.2.2.2.1).symm
    filter_upwards [hNS.2.2.2.2, hc.2.2.2.2] with z e1 e2
    rw [e1, e2]
  have hne : mobiusExt I I (-1) 1 (wAS (ε • ν) (mobiusExt 1 (-I) 1 I (x : ExtPlane))) ≠ extInf := by
    intro h
    have e2 := congrArg (mobiusExt 1 (-I) 1 I) h
    rw [p71_S_inv, hS1, ← hp1] at e2
    have e3 := congrArg (mobiusExt I I (-1) 1) ((wAS_bijective _).1 e2)
    rw [cayley_apply_inv, hSi1] at e3
    exact OnePoint.coe_ne_infty x e3
  rw [hV]
  show _ = mobiusExt 1 (-I) 1 I
    ((finPart (mobiusExt I I (-1) 1 (wAS (ε • ν) (mobiusExt 1 (-I) 1 I (x : ExtPlane)))) : ℂ) : ExtPlane)
  rw [coe_finPart_of_ne hne, p71_S_inv]

/-- (WM3) `normalizedSolution` sees its coefficient only a.e. (`IsNormalizedSolution` uses `∀ᵐ`; uniqueness is
`thm13_5_uniqueness_plane`). -/
theorem p71_ns_congr {μ₁ μ₂ : ℂ → ℂ} (h : μ₁ =ᵐ[volume] μ₂) : normalizedSolution μ₁ = normalizedSolution μ₂ := by
  have hiff : ∀ f, IsNormalizedSolution f μ₁ ↔ IsNormalizedSolution f μ₂ := fun f => by
    constructor
    · rintro ⟨h1, h2, h3, h4, h5⟩
      refine ⟨h1, h2, h3, h4, ?_⟩
      filter_upwards [h5, h] with z a b
      rw [a, b]
    · rintro ⟨h1, h2, h3, h4, h5⟩
      refine ⟨h1, h2, h3, h4, ?_⟩
      filter_upwards [h5, h] with z a b
      rw [a, ← b]
  by_cases hex : ∃ f, IsNormalizedSolution f μ₁
  · have hex2 : ∃ f, IsNormalizedSolution f μ₂ := by
      obtain ⟨f, hf⟩ := hex
      exact ⟨f, (hiff f).1 hf⟩
    rw [normalizedSolution, normalizedSolution, dif_pos hex, dif_pos hex2]
    have c1 := hex.choose_spec
    have c2 := (hiff _).2 hex2.choose_spec
    refine thm13_5_uniqueness_plane c1.1 c2.1 c1.2.1 c2.2.1 ?_ c1.2.2.1 c1.2.2.2.1 c2.2.2.1 c2.2.2.2.1
    filter_upwards [c1.2.2.2.2, c2.2.2.2.2] with z a b
    rw [a, b]
  · have hex2 : ¬ ∃ f, IsNormalizedSolution f μ₂ := by
      rintro ⟨f, hf⟩
      exact hex ⟨f, (hiff f).2 hf⟩
    rw [normalizedSolution, normalizedSolution, dif_neg hex, dif_neg hex2]

/-- (WM3) **Change of variables** `ζ = Φ(η) = cayley(η̄)`, `𝕌 → 𝔻*`, Jacobian `|S'(η̄)|²`. -/
theorem p71_cov (F : ℂ → ℂ) :
    ∫ ζ in unitDiscExterior, F ζ =
      ∫ η in upperHalf, ((‖2 * I / (conj η + I) ^ 2‖ ^ 2 : ℝ) : ℂ) * F (cayley (conj η)) := by
  have hU := measurableSet_upperHalf_aux
  have hd : ∀ w : ℂ, w ≠ -I → w + I ≠ 0 := fun w hw h => hw (by linear_combination h)
  have hLo : IsOpen ({w : ℂ | w.im < 0} \ {-I}) :=
    (isOpen_lt Complex.continuous_im continuous_const).sdiff isClosed_singleton
  have hdiff : DifferentiableOn ℂ cayley ({w : ℂ | w.im < 0} \ {-I}) := fun w hw =>
    (p71_cay_hasDeriv (hd w hw.2)).differentiableAt.differentiableWithinAt
  have hinj : InjOn cayley ({w : ℂ | w.im < 0} \ {-I}) := fun a ha b hb hab => by
    rw [← p71_cinv_cay (hd a ha.2), hab, p71_cinv_cay (hd b hb.2)]
  have himg : cayley '' ({w : ℂ | w.im < 0} \ {-I}) = unitDiscExterior := by
    ext ζ
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact p71_cay_ext hw.1 (hd w hw.2)
    · intro hζ
      have hζ' : (1 : ℝ) < ‖ζ‖ := hζ
      have hζ1 : ζ ≠ 1 := by
        intro h
        rw [h, norm_one] at hζ'
        exact lt_irrefl _ hζ'
      refine ⟨cayleyInv ζ, ⟨p71_cinv_im hζ', fun h => ?_⟩, p71_cay_cinv hζ1⟩
      have e := p71_cay_cinv hζ1
      rw [mem_singleton_iff.mp h] at e
      have h0 : cayley (-I) = 0 := by
        show (-I - I) / (-I + I) = 0
        simp
      rw [h0] at e
      rw [← e, norm_zero] at hζ'
      linarith
  have hpre : (fun w : ℂ => conj w) ⁻¹' ({w : ℂ | w.im < 0} \ {-I}) = upperHalf \ {I} := by
    ext w
    simp only [mem_preimage, Set.mem_sdiff, mem_ofPred_eq, mem_singleton_iff, Complex.conj_im]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨show 0 < w.im by linarith, fun h => h2 (by rw [h, Complex.conj_I])⟩
    · rintro ⟨h1, h2⟩
      refine ⟨by linarith [show 0 < w.im from h1], fun h => h2 ?_⟩
      have := congrArg conj h
      simpa using this
  have hnull : (upperHalf \ {I} : Set ℂ) =ᵐ[volume] upperHalf := diff_null_ae_eq_self (measure_singleton I)
  rw [← himg, ahP_integral_image hLo hdiff hinj,
    ← gzE_conj_measurePreserving.setIntegral_preimage_emb Complex.conjLIE.toHomeomorph.measurableEmbedding _ _,
    hpre, setIntegral_congr_set hnull.symm]
  refine setIntegral_congr_fun (hU.diff (measurableSet_singleton I)) fun v hv => ?_
  have hvd : conj v + I ≠ 0 := fun h => hv.2 (mem_singleton_iff.2 (by
    have := congrArg conj h
    simp only [map_add, Complex.conj_conj, Complex.conj_I, map_zero] at this
    linear_combination this))
  show ‖deriv cayley (conj v)‖ ^ 2 • F (cayley (conj v)) = _
  rw [(p71_cay_hasDeriv hvd).deriv, Complex.real_smul]

/-- (WM3) **Bergman kernel covariance.** For `η ∈ 𝕌 ∖ {i}` and `X ∈ 𝕃 ∖ {-i}` (`p = S X`, `q = X̄`):
`3(1-|p|²)²/π · S'(η̄)² (1 - Φ(η) p̄)⁻⁴ · \overline{S'(X)}/S'(X) = \overline{-3(q - q̄)²/π · (η - q̄)⁻⁴}`. -/
theorem p71_kernel {η X : ℂ} (hη : η ∈ upperHalf) (hηI : η ≠ I) (hX : X.im < 0) (hXI : X ≠ -I) :
    (3 * (1 - ‖cayley X‖ ^ 2) ^ 2 / π : ℂ) *
        ((2 * I / (conj η + I) ^ 2) ^ 2 / (1 - cayley (conj η) * conj (cayley X)) ^ 4) *
        (conj (2 * I / (X + I) ^ 2) / (2 * I / (X + I) ^ 2)) =
      conj (-(3 * (conj X - conj (conj X)) ^ 2 / π) / (η - conj (conj X)) ^ 4) := by
  have hη0 : 0 < η.im := hη
  have h1 : X + I ≠ 0 := fun h => hXI (by linear_combination h)
  have h2 : conj X - I ≠ 0 := by
    intro h; apply hXI
    have : conj (conj X) = conj I := by rw [sub_eq_zero.mp h]
    rwa [Complex.conj_conj, Complex.conj_I] at this
  have h3 : conj η + I ≠ 0 := by
    intro h; apply hηI
    have : conj (conj η) = conj (-I) := by rw [eq_neg_of_add_eq_zero_left h]
    rwa [Complex.conj_conj, map_neg, Complex.conj_I, neg_neg] at this
  have h4 : η - I ≠ 0 := sub_ne_zero.mpr hηI
  have h5 : conj X - conj η ≠ 0 := by
    intro h
    have := congrArg Complex.im h
    simp only [Complex.sub_im, Complex.conj_im, Complex.zero_im] at this
    linarith
  have h5' : conj η - conj X ≠ 0 := fun h => h5 (by linear_combination -h)
  have h6 : η - X ≠ 0 := by
    intro h
    have := congrArg Complex.im h
    simp only [Complex.sub_im, Complex.zero_im] at this
    linarith
  have h7 : X - I ≠ 0 := by
    intro h
    have := congrArg Complex.im h
    simp only [Complex.sub_im, Complex.I_im, Complex.zero_im] at this
    linarith
  have h1' : X - -I ≠ 0 := by rwa [sub_neg_eq_add]
  have h2' : conj X + -I ≠ 0 := by rwa [← sub_eq_add_neg]
  have h3' : conj η - -I ≠ 0 := by rwa [sub_neg_eq_add]
  have h4' : η + -I ≠ 0 := by rwa [← sub_eq_add_neg]
  have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hI4 : I ^ 4 = 1 := by
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, Complex.I_sq]
    norm_num
  have hW : 1 - cayley X * conj (cayley X) = 2 * I * (conj X - X) / ((X + I) * (conj X - I)) := by
    show 1 - (X - I) / (X + I) * conj ((X - I) / (X + I)) = _
    rw [map_div₀, map_sub, map_add, Complex.conj_I]
    field_simp
    ring
  have hD : 1 - cayley (conj η) * conj (cayley X) =
      2 * I * (conj X - conj η) / ((conj η + I) * (conj X - I)) := by
    show 1 - (conj η - I) / (conj η + I) * conj ((X - I) / (X + I)) = _
    rw [map_div₀, map_sub, map_add, Complex.conj_I]
    field_simp
    ring
  rw [← Complex.mul_conj', hW, hD]
  simp only [div_pow, mul_pow, Complex.I_sq, hI4]
  simp only [map_div₀, map_mul, map_neg, map_pow, map_sub, map_add, map_ofNat, Complex.conj_I,
    Complex.conj_conj, Complex.conj_ofReal]
  field_simp
  ring

/-- (WM3) Basic facts on `V = w_U(εm)`: continuous, bijective, real-symmetric, and `V⁻¹` maps `𝕌` to `𝕌`. -/
theorem p71_V_facts {m : ℂ → ℂ} {k : ℝ} (hk : 0 ≤ k) (hm : IsBeltramiCoeff m upperHalf k) {ε : ℂ}
    (hε : ‖ε‖ * k < 1) :
    Continuous (wU fun y => ε * m y) ∧ Function.Bijective (wU fun y => ε * m y) ∧
      (∀ x, wU (fun y => ε * m y) (conj x) = conj (wU (fun y => ε * m y) x)) ∧
      ∀ η ∈ upperHalf, Function.invFun (wU fun y => ε * m y) η ∈ upperHalf ∧
        wU (fun y => ε * m y) (Function.invFun (wU fun y => ε * m y) η) = η := by
  rw [e124_wU_eq_fMuSym hk hm hε]
  have hν : IsBeltramiCoeff (fun y => ε * m y) upperHalf (‖ε‖ * k) :=
    ⟨hm.1.const_mul ε, hm.2.mono fun z hz => by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left hz (norm_nonneg _)⟩
  obtain ⟨-, hN, hK, -⟩ := bg_sym_spec (by positivity) hε hν
  obtain ⟨himg, -, hsym, -, -⟩ := fMuSym_upperHalf (by positivity) hε hν
  have hc : Continuous (fMuSym fun y => ε * m y) := continuousOn_univ.mp hK.2.2.1.1
  have hinj : Function.Injective (fMuSym fun y => ε * m y) := fun a b h =>
    hK.2.2.1.2.1 (mem_univ a) (mem_univ b) h
  have hsurj : Function.Surjective (fMuSym fun y => ε * m y) := fun w => by
    have hw : w ∈ (fMuSym fun y => ε * m y) '' univ := by rw [hN.2.1]; exact mem_univ w
    obtain ⟨a, -, ha⟩ := hw
    exact ⟨a, ha⟩
  refine ⟨hc, ⟨hinj, hsurj⟩, hsym, fun η hη => ?_⟩
  rw [← himg] at hη
  obtain ⟨t, ht, rfl⟩ := hη
  rw [Function.leftInverse_invFun hinj t]
  exact ⟨ht, rfl⟩

/-- (WM3) A.e. statements on `𝕌` transfer along `V⁻¹` when `V` is differentiable on `𝕌`. -/
theorem p71_V_push {V : ℂ → ℂ} (hVd : DifferentiableOn ℝ V upperHalf)
    (hVi : ∀ η ∈ upperHalf, Function.invFun V η ∈ upperHalf ∧ V (Function.invFun V η) = η) {P : ℂ → Prop}
    (h : ∀ᵐ t ∂(volume.restrict upperHalf), P t) :
    ∀ᵐ η ∂(volume.restrict upperHalf), P (Function.invFun V η) := by
  rw [ae_restrict_iff' measurableSet_upperHalf_aux, ae_iff] at h ⊢
  have hsub : {η | ¬(η ∈ upperHalf → P (Function.invFun V η))} ⊆ V '' {t | ¬(t ∈ upperHalf → P t)} := by
    intro η hη
    have hη' := not_imp.mp hη
    obtain ⟨h1, h2⟩ := hVi η hη'.1
    exact ⟨Function.invFun V η, fun h' => hη'.2 (h' h1), h2⟩
  exact measure_mono_null hsub (addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume
    (hVd.mono fun t ht => (not_imp.mp ht).1) h)

/-- (WM3) The two phases in `m[g]` are unimodular off `u = i`. -/
theorem p71_AB_norm {t : ℂ} (ht : t ∈ upperHalf) (htI : t ≠ I) :
    ‖cayley t ^ 2 / conj (cayley t) ^ 2‖ = 1 ∧ ‖conj (2 * I / (t + I) ^ 2) / (2 * I / (t + I) ^ 2)‖ = 1 := by
  have ht0 : 0 < t.im := ht
  have hs : cayley t ≠ 0 := by
    show (t - I) / (t + I) ≠ 0
    exact div_ne_zero (sub_ne_zero.mpr htI) (cayley_den_ne_zero ht0)
  have hd : 2 * I / (t + I) ^ 2 ≠ 0 :=
    div_ne_zero (mul_ne_zero two_ne_zero I_ne_zero) (pow_ne_zero _ (cayley_den_ne_zero ht0))
  constructor
  · rw [norm_div, norm_pow, norm_pow, Complex.norm_conj, div_self (pow_ne_zero _ (norm_ne_zero_iff.mpr hs))]
  · rw [norm_div, Complex.norm_conj, div_self (norm_ne_zero_iff.mpr hd)]

/-- (WM3) The phase identity behind `R`: `\overline{A(t)} \overline{B(t)} = \overline{S'(t̄)}/S'(t̄)`. -/
theorem p71_key {t : ℂ} (ht : t ∈ upperHalf) (htI : t ≠ I) :
    conj (cayley t ^ 2 / conj (cayley t) ^ 2) * conj (conj (2 * I / (t + I) ^ 2) / (2 * I / (t + I) ^ 2)) =
      conj (2 * I / (conj t + I) ^ 2) / (2 * I / (conj t + I) ^ 2) := by
  have ht0 : 0 < t.im := ht
  have h1 : t + I ≠ 0 := cayley_den_ne_zero ht0
  have h2 : t - I ≠ 0 := sub_ne_zero.mpr htI
  have h3 : conj t + I ≠ 0 := by
    intro h; apply htI
    have : conj (conj t) = conj (-I) := by rw [eq_neg_of_add_eq_zero_left h]
    rwa [Complex.conj_conj, map_neg, Complex.conj_I, neg_neg] at this
  have h4 : conj t - I ≠ 0 := by
    intro h
    have := congrArg Complex.im h
    simp only [Complex.sub_im, Complex.conj_im, Complex.I_im, Complex.zero_im] at this
    linarith
  have h1' : t - -I ≠ 0 := by rwa [sub_neg_eq_add]
  have h2' : t + -I ≠ 0 := by rwa [← sub_eq_add_neg]
  have h3' : conj t - -I ≠ 0 := by rwa [sub_neg_eq_add]
  have h4' : conj t + -I ≠ 0 := by rwa [← sub_eq_add_neg]
  have hI : I ≠ 0 := I_ne_zero
  simp only [cayley, map_mul, map_div₀, map_sub, map_add, map_neg, map_pow, map_ofNat, Complex.conj_I,
    Complex.conj_conj]
  field_simp
  ring

/-- (WM3) `cayley` never takes the value `1`. -/
theorem p71_cay_ne_one {w : ℂ} (h : w + I ≠ 0) : cayley w ≠ 1 := by
  show (w - I) / (w + I) ≠ 1
  intro e
  rw [div_eq_iff h] at e
  have h2 : (2 : ℂ) * I = 0 := by linear_combination -e
  simp at h2

/-- (WM3) `cayleyInv w + i = 2i/(1 - w)`. -/
theorem p71_cinv_add {w : ℂ} (h : w ≠ 1) : cayleyInv w + I = 2 * I / (1 - w) := by
  have h1 : (1 : ℂ) - w ≠ 0 := sub_ne_zero.mpr (Ne.symm h)
  show I * (1 + w) / (1 - w) + I = _
  field_simp
  ring

/-- (WM3) The derivative of `cayleyInv`. -/
theorem p71_cinv_hasDeriv {w : ℂ} (h : w ≠ 1) : HasDerivAt cayleyInv (2 * I / (1 - w) ^ 2) w := by
  have h1 : (1 : ℂ) - w ≠ 0 := sub_ne_zero.mpr (Ne.symm h)
  have hd := (((hasDerivAt_id w).const_add 1).const_mul I).div ((hasDerivAt_id w).const_sub 1) h1
  convert hd using 1
  · funext y
    rfl
  · simp only [id_eq]
    field_simp
    ring

/-- (WM3) `(cayleyInv)'(w) = 1/cayley'(cayleyInv w)`. -/
theorem p71_DT {w : ℂ} (h : w ≠ 1) : 2 * I / (1 - w) ^ 2 = (2 * I / (cayleyInv w + I) ^ 2)⁻¹ := by
  have h1 : (1 : ℂ) - w ≠ 0 := sub_ne_zero.mpr (Ne.symm h)
  have hI : I ≠ 0 := I_ne_zero
  rw [p71_cinv_add h]
  field_simp

/-- (WM3) `|a|² · a/ā = a²`. -/
theorem p71_sq_phase {a : ℂ} (ha : a ≠ 0) : ((‖a‖ ^ 2 : ℝ) : ℂ) * (a / conj a) = a ^ 2 := by
  have ha' : conj a ≠ 0 := (map_ne_zero _).mpr ha
  push_cast
  rw [← Complex.mul_conj']
  field_simp

/-- (WM3) `[W2]` **Transformation law of `Q`.** For `z ∈ 𝔻*` and small `ε`,
`Q_A(μ, εν)(z) = c(z) · \overline{Q_U(m[gμ], ε̄ m[gν])(ȳ…)}` at `y = \overline{cayleyInv z}`. Route: WM2; `R` and `P`
transported along `S` on `𝕃` (change of variables on `𝔻* = S(𝕃)`, Bergman-kernel identity, `invFun` through the
conjugation, `wA`-null sets), then the reflection `𝕃 → 𝕌`; the pole of `wAS(εν)` stays away (`acc_pole_cont`). -/
theorem p71_wm_Q {μ ν : LinfStar} (hμ : μ ∈ harmonicBeltrami) (hν : ν ∈ harmonicBeltrami) {gμ gν : ℂ → ℂ}
    (hgμc : ContinuousOn gμ unitDiscExterior) (hgμ : ∀ᵐ z ∂(volume.restrict unitDiscExterior), μ z = gμ z)
    (hgνc : ContinuousOn gν unitDiscExterior) (hgν : ∀ᵐ z ∂(volume.restrict unitDiscExterior), ν z = gν z)
    {mμ mν : ℂ → ℂ}
    (hmμ : ∀ u ∈ upperHalf, u ≠ I → mμ u = conj (gμ (cayley (conj u))) * (cayley u ^ 2 / conj (cayley u) ^ 2) *
      (conj (2 * I / (u + I) ^ 2) / (2 * I / (u + I) ^ 2)))
    (hmν : ∀ u ∈ upperHalf, u ≠ I → mν u = conj (gν (cayley (conj u))) * (cayley u ^ 2 / conj (cayley u) ^ 2) *
      (conj (2 * I / (u + I) ^ 2) / (2 * I / (u + I) ^ 2)))
    {z : ℂ} (hz : z ∈ unitDiscExterior) :
    ∀ᶠ ε in 𝓝 (0 : ℂ), Qfun μ (ε • ν) z =
      (2 * I / (cayleyInv z + I) ^ 2) / conj (2 * I / (cayleyInv z + I) ^ 2) *
        conj (QfunU mμ (fun u => conj ε * mν u) (conj (cayleyInv z))) := by
  -- `V = w_U(ε̄ m')` with `m'` the harmonic representative of WM1'; `wU (ε̄ mν) = V = wU (ε̄ m[gν])` because the
  -- coefficients agree off `±i` (`p71_ns_congr`, i.e. `thm13_5_uniqueness_plane`). WM2 gives `w_A(εν) = S∘V∘S⁻¹`.
  -- `P` is transported by `p71_cov` + `p71_kernel`; `R` pointwise a.e. (`RnmFunU` differs from `R[m[g]]` only on
  -- the null set `{η = V(i)}`).
  obtain ⟨m', ψ', hharm', hm'⟩ := p71_wm_harm hν hgνc hgν
  obtain ⟨C, hC0, hCb⟩ := harmonicU_bounded hharm'
  have hU := measurableSet_upperHalf_aux
  have hUo : IsOpen upperHalf := isOpen_lt continuous_const Complex.continuous_im
  have hmB : IsBeltramiCoeff m' upperHalf C :=
    ⟨(harmonicU_continuousOn hharm').aestronglyMeasurable hU, by
      filter_upwards [ae_restrict_mem hU] with u hu
      exact hCb u hu⟩
  have hjoint := wr_joint_contDiff_U hC0 hmB (wr_isHarmonicU_contDiffOn hharm')
  have hz1 : (1 : ℝ) < ‖z‖ := hz
  have hzne : z ≠ 1 := by
    intro h
    rw [h, norm_one] at hz1
    exact lt_irrefl _ hz1
  have hx : (cayleyInv z).im < 0 := p71_cinv_im hz1
  have hTx : cayley (cayleyInv z) = z := p71_cay_cinv hzne
  have hxI : cayleyInv z + I ≠ 0 := by
    rw [p71_cinv_add hzne]
    exact div_ne_zero (mul_ne_zero two_ne_zero I_ne_zero) (sub_ne_zero.mpr (Ne.symm hzne))
  have hy : conj (cayleyInv z) ∈ upperHalf := by
    show 0 < (conj (cayleyInv z)).im
    rw [Complex.conj_im]
    linarith
  have hyI : conj (cayleyInv z) ≠ I := by
    intro h
    apply hxI
    have e : cayleyInv z = -I := by
      have := congrArg conj h
      rwa [Complex.conj_conj, Complex.conj_I] at this
    rw [e]
    ring
  have hev1 : ∀ᶠ ε in 𝓝 (0 : ℂ), ‖ε‖ * ‖ν‖ < 1 :=
    (continuous_norm.mul continuous_const).continuousAt.eventually
      (gt_mem_nhds (show ‖(0 : ℂ)‖ * ‖ν‖ < 1 by simp))
  have hev2 : ∀ᶠ ε in 𝓝 (0 : ℂ), ‖conj ε‖ * C < 1 :=
    ((continuous_norm.comp Complex.continuous_conj).mul continuous_const).continuousAt.eventually
      (gt_mem_nhds (show ‖conj (0 : ℂ)‖ * C < 1 by simp))
  have hev3 : ∀ᶠ ε in 𝓝 (0 : ℂ), wU (fun u => conj ε * m' u) (conj (cayleyInv z)) ≠ I := by
    have hopen : IsOpen ({ε : ℂ | ‖ε‖ * C < 1} ×ˢ upperHalf) :=
      (isOpen_lt (continuous_norm.mul continuous_const) continuous_const).prod hUo
    have h2 : ContinuousAt (fun p : ℂ × ℂ => wU (fun u => p.1 * m' u) p.2) (0, conj (cayleyInv z)) :=
      hjoint.continuousOn.continuousAt (hopen.mem_nhds ⟨by simp, hy⟩)
    have h3 : ContinuousAt (fun ε : ℂ => (conj ε, conj (cayleyInv z))) 0 :=
      (Complex.continuous_conj.prodMk continuous_const).continuousAt
    have hca := h2.comp_of_eq h3 (by simp)
    have hval : (fun ε : ℂ => wU (fun u => conj ε * m' u) (conj (cayleyInv z))) 0 = conj (cayleyInv z) := by
      show wU (fun u => conj 0 * m' u) (conj (cayleyInv z)) = _
      rw [map_zero, show (fun u : ℂ => (0 : ℂ) * m' u) = (0 : ℂ → ℂ) from funext fun u => zero_mul _,
        rhoVar_wU_zero]
      rfl
    exact hca.eventually_ne (by rw [← hval] at hyI; exact hyI)
  filter_upwards [hev1, hev2, hev3] with ε hε1 hε2 hVy
  have hρ : ε • ν ∈ LinfStarBall := by
    show ε • ν ∈ ball (0 : LinfStar) 1
    rw [mem_ball_zero_iff, norm_smul]
    exact hε1
  obtain ⟨hVc, -, hVs, hVi⟩ := p71_V_facts hC0 hmB hε2
  have hVd : DifferentiableOn ℝ (wU fun u => conj ε * m' u) upperHalf :=
    (hjoint.comp (contDiff_const.prodMk contDiff_id).contDiffOn
      (fun u hu => (⟨hε2, hu⟩ : (conj ε, u) ∈ {ε : ℂ | ‖ε‖ * C < 1} ×ˢ upperHalf))).differentiableOn
      (by norm_num)
  have hVup : ∀ u ∈ upperHalf, wU (fun y => conj ε * m' y) u ∈ upperHalf := fun u hu =>
    e124_wU_upper hC0 hmB hε2 hu
  have hmν' : ∀ u ∈ upperHalf, u ≠ I → mν u = m' u := fun u hu hI => by rw [hmν u hu hI, hm' u hu hI]
  have hconjU : ∀ u : ℂ, u.im < 0 → conj u ∈ upperHalf := fun u hu => by
    show 0 < (conj u).im
    rw [Complex.conj_im]
    linarith
  have hconjI : ∀ u : ℂ, u ≠ -I → conj u ≠ I := fun u h1 h => by
    apply h1
    have := congrArg conj h
    rwa [Complex.conj_conj, Complex.conj_I] at this
  have hVeq : wU (fun u => conj ε * mν u) = wU (fun u => conj ε * m' u) := by
    show normalizedSolution _ = normalizedSolution _
    refine p71_ns_congr ?_
    filter_upwards [Measure.ae_ne volume I, Measure.ae_ne volume (-I)] with u h1 h2
    unfold extU
    split_ifs with ha hb
    · simp only [hmν' u ha h1]
    · simp only [hmν' (conj u) (hconjU u hb) (hconjI u h2)]
    · rfl
  have hV2 : wU (fun u => conj ε * (conj (gν (cayley (conj u))) * (cayley u ^ 2 / conj (cayley u) ^ 2) *
      (conj (2 * I / (u + I) ^ 2) / (2 * I / (u + I) ^ 2)))) = wU (fun u => conj ε * m' u) := by
    show normalizedSolution _ = normalizedSolution _
    refine p71_ns_congr ?_
    filter_upwards [Measure.ae_ne volume I, Measure.ae_ne volume (-I)] with u h1 h2
    unfold extU
    split_ifs with ha hb
    · simp only [hm' u ha h1]
    · simp only [hm' (conj u) (hconjU u hb) (hconjI u h2)]
    · rfl
  set V := wU (fun u => conj ε * m' u) with hVdef
  have hF1 : ∀ x', x' + I ≠ 0 → V x' + I ≠ 0 → wA (ε • ν) (cayley x') = cayley (V x') := by
    intro x' h1 h2
    have h := p71_wm_conj hν hgνc hgν hε1 x'
    rw [hV2, p71_S_coe h1, p71_S_coe h2] at h
    show finPart (wAS (ε • ν) ((cayley x' : ℂ) : ExtPlane)) = _
    rw [h]
    rfl
  have hdzs : ∀ u ∈ upperHalf, dz V (conj u) = conj (dz V u) := by
    intro u hu
    have hd : DifferentiableAt ℝ V (conj (conj u)) := by
      rw [Complex.conj_conj]
      exact hVd.differentiableAt (hUo.mem_nhds hu)
    have h := (abR_x_dz_dzbar_conj hd).2.1
    have hfun : (fun w => conj (V (conj w))) = V := funext fun w => by rw [hVs, Complex.conj_conj]
    rwa [hfun, Complex.conj_conj] at h
  -- local representation `w_A(εν) = S ∘ V ∘ S⁻¹` and its `∂_z`
  have hcinvc : ∀ z0 : ℂ, z0 ≠ 1 → ContinuousAt cayleyInv z0 := fun z0 h => (p71_cinv_hasDeriv h).continuousAt
  have hloc : ∀ z0 : ℂ, z0 ≠ 1 → cayleyInv z0 + I ≠ 0 → V (cayleyInv z0) + I ≠ 0 →
      wA (ε • ν) =ᶠ[𝓝 z0] fun z' => cayley (V (cayleyInv z')) := by
    intro z0 h0 h1 h2
    have hc1 : ContinuousAt (fun z' => cayleyInv z' + I) z0 := (hcinvc z0 h0).add continuousAt_const
    have hc2 : ContinuousAt (fun z' => V (cayleyInv z') + I) z0 :=
      (hVc.continuousAt.comp (hcinvc z0 h0)).add continuousAt_const
    filter_upwards [hc1.eventually_ne h1, hc2.eventually_ne h2, continuousAt_id.eventually_ne h0]
      with z' e1 e2 e3
    have := hF1 (cayleyInv z') e1 e2
    rwa [p71_cay_cinv (show z' ≠ 1 from e3)] at this
  have hdzw : ∀ z0 : ℂ, z0 ≠ 1 → cayleyInv z0 + I ≠ 0 → V (cayleyInv z0) + I ≠ 0 →
      dz (wA (ε • ν)) z0 = 2 * I / (V (cayleyInv z0) + I) ^ 2 *
        (dz V (cayleyInv z0) * (2 * I / (1 - z0) ^ 2)) := by
    intro z0 h0 h1 h2
    have e0 : dz (wA (ε • ν)) z0 = dz (fun z' => cayley (V (cayleyInv z'))) z0 := by
      simp only [dz, (hloc z0 h0 h1 h2).fderiv_eq]
    have hL := s23_wirtinger_comp_left (g := fun z' => V (cayleyInv z')) (h := cayley) (k := cayleyInv) (z := z0)
      (hVc.continuousAt.comp (hcinvc z0 h0)) (p71_cay_hasDeriv h2).differentiableAt
      (p71_cinv_hasDeriv (p71_cay_ne_one h2)).differentiableAt
      (by
        filter_upwards [(continuousAt_id.add continuousAt_const).eventually_ne h2] with w hw
        exact p71_cinv_cay hw)
    have hR := s23_wirtinger_comp_right (g := V) (T := cayleyInv) (S := cayley) (z := z0)
      (p71_cinv_hasDeriv h0).differentiableAt (p71_cay_hasDeriv h1).differentiableAt
      (by
        filter_upwards [continuousAt_id.eventually_ne h0] with w hw
        exact p71_cay_cinv hw)
      (by
        filter_upwards [(continuousAt_id.add continuousAt_const).eventually_ne h1] with w hw
        exact p71_cinv_cay hw)
    rw [e0, show (fun z' => cayley (V (cayleyInv z'))) = cayley ∘ (fun z' => V (cayleyInv z')) from rfl, hL.1,
      show (fun z' => V (cayleyInv z')) = V ∘ cayleyInv from rfl, hR.1, (p71_cay_hasDeriv h2).deriv,
      (p71_cinv_hasDeriv h0).deriv]
  -- the point `z`
  have hVx : V (cayleyInv z) = conj (V (conj (cayleyInv z))) := by
    rw [← hVs, Complex.conj_conj]
  have hVxI : V (cayleyInv z) + I ≠ 0 := by
    rw [hVx]
    intro h
    apply hVy
    have := congrArg conj h
    simp only [map_add, Complex.conj_conj, Complex.conj_I, map_zero] at this
    linear_combination this
  have hXim : (V (cayleyInv z)).im < 0 := by
    rw [hVx, Complex.conj_im]
    have : 0 < (V (conj (cayleyInv z))).im := hVup _ hy
    linarith
  have hXI : V (cayleyInv z) ≠ -I := fun h => hVxI (by rw [h]; ring)
  have hwz : wA (ε • ν) z = cayley (V (cayleyInv z)) := by
    have := hF1 (cayleyInv z) hxI hVxI
    rwa [hTx] at this
  -- the `R` identity, a.e. on `𝕌`
  have hsm : ∀ᵐ w ∂(volume.restrict unitDiscExterior), (ε • ν) w = ε * gν w := by
    filter_upwards [Lp.coeFn_smul ε ν, hgν] with w h1 h2
    rw [h1, Pi.smul_apply, smul_eq_mul, h2]
  have hR : ∀ᵐ η ∂(volume.restrict upperHalf),
      RnmFun μ (ε • ν) (cayley (conj η)) = (2 * I / (conj η + I) ^ 2) / conj (2 * I / (conj η + I) ^ 2) *
        conj (RnmFunU mμ (fun u => conj ε * mν u) η) := by
    filter_upwards [ae_restrict_mem hU, ae_restrict_of_ae (Measure.ae_ne volume I),
      ae_restrict_of_ae (Measure.ae_ne volume (V I)), p71_V_push hVd hVi (p71_phi_ae hgμ),
      p71_V_push hVd hVi (p71_phi_ae hsm)] with η hη hηI hηV hμt hνt
    obtain ⟨ht, hVt⟩ := hVi η hη
    set t := Function.invFun V η with htdef
    have htI : t ≠ I := fun h => hηV (by rw [← hVt, h])
    have ht0 : 0 < t.im := ht
    have hη0 : 0 < η.im := hη
    have hctI : conj t + I ≠ 0 := by
      intro h; apply htI
      have : conj (conj t) = conj (-I) := by rw [eq_neg_of_add_eq_zero_left h]
      rwa [Complex.conj_conj, map_neg, Complex.conj_I, neg_neg] at this
    have hcηI : conj η + I ≠ 0 := by
      intro h; apply hηI
      have : conj (conj η) = conj (-I) := by rw [eq_neg_of_add_eq_zero_left h]
      rwa [Complex.conj_conj, map_neg, Complex.conj_I, neg_neg] at this
    have hVct : V (conj t) = conj η := by rw [hVs, hVt]
    have hVctI : V (conj t) + I ≠ 0 := by rw [hVct]; exact hcηI
    have hwt : wA (ε • ν) (cayley (conj t)) = cayley (conj η) := by rw [hF1 (conj t) hctI hVctI, hVct]
    have hext : cayley (conj η) ∈ unitDiscExterior :=
      p71_cay_ext (by rw [Complex.conj_im]; linarith) hcηI
    have hne0 : wA (ε • ν) (cayley (conj t)) ≠ 0 := by
      rw [hwt]
      intro h
      have : (1 : ℝ) < ‖cayley (conj η)‖ := hext
      rw [h, norm_zero] at this
      linarith
    have hinv : Function.invFun (wA (ε • ν)) (cayley (conj η)) = cayley (conj t) := by
      rw [← hwt]
      exact bc_invFun_wA hne0
    have hu1 : cayley (conj t) ≠ 1 := p71_cay_ne_one hctI
    have hci : cayleyInv (cayley (conj t)) = conj t := p71_cinv_cay hctI
    have hdzu := hdzw (cayley (conj t)) hu1 (by rw [hci]; exact hctI) (by rw [hci]; exact hVctI)
    rw [hci, hVct, hdzs t ht, p71_DT hu1, hci] at hdzu
    have hext' : cayley (conj t) ∈ unitDiscExterior :=
      p71_cay_ext (by rw [Complex.conj_im]; linarith) hctI
    obtain ⟨hA1, hB1⟩ := p71_AB_norm ht htI
    have hkey := p71_key ht htI
    show (fun u => μ u / (1 - ‖(ε • ν) u‖ ^ 2) * (dz (wA (ε • ν)) u / conj (dz (wA (ε • ν)) u)))
        (Function.invFun (wA (ε • ν)) (cayley (conj η))) = _ * conj ((fun u => mμ u / (1 - ‖conj ε * mν u‖ ^ 2) *
          (dz (wU fun u => conj ε * mν u) u / conj (dz (wU fun u => conj ε * mν u) u)))
            (Function.invFun (wU fun u => conj ε * mν u) η))
    rw [hVeq, hinv]
    simp only []
    rw [← htdef, hdzu, hmμ t ht htI, hmν t ht htI, hμt, hνt]
    have hnorm : ‖conj ε * (conj (gν (cayley (conj t))) * (cayley t ^ 2 / conj (cayley t) ^ 2) *
        (conj (2 * I / (t + I) ^ 2) / (2 * I / (t + I) ^ 2)))‖ = ‖ε * gν (cayley (conj t))‖ := by
      rw [norm_mul, norm_mul, norm_mul, hA1, hB1, Complex.norm_conj, Complex.norm_conj, norm_mul]
      ring
    rw [hnorm]
    have hT1 : 2 * I / (conj η + I) ^ 2 ≠ 0 :=
      div_ne_zero (mul_ne_zero two_ne_zero I_ne_zero) (pow_ne_zero _ hcηI)
    have hT2 : 2 * I / (conj t + I) ^ 2 ≠ 0 :=
      div_ne_zero (mul_ne_zero two_ne_zero I_ne_zero) (pow_ne_zero _ hctI)
    have hT1' : conj (2 * I / (conj η + I) ^ 2) ≠ 0 := (map_ne_zero _).mpr hT1
    have hT2' : conj (2 * I / (conj t + I) ^ 2) ≠ 0 := (map_ne_zero _).mpr hT2
    generalize cayley t ^ 2 / conj (cayley t) ^ 2 = A at hkey hA1 ⊢
    generalize conj (2 * I / (t + I) ^ 2) / (2 * I / (t + I) ^ 2) = B at hkey hB1 ⊢
    generalize 2 * I / (conj η + I) ^ 2 = T1 at hT1 hT1' ⊢
    generalize 2 * I / (conj t + I) ^ 2 = T2 at hkey hT2 hT2' ⊢
    generalize gμ (cayley (conj t)) = a
    generalize dz V t = d
    have hA0 : conj A ≠ 0 := (map_ne_zero _).mpr (norm_ne_zero_iff.mp (by rw [hA1]; norm_num))
    have hB' : conj B = conj T2 / T2 / conj A := by
      rw [← hkey]
      field_simp
    simp only [map_mul, map_div₀, map_sub, map_one, map_pow, map_inv₀, Complex.conj_ofReal, Complex.conj_conj]
    rw [hB']
    by_cases hd0 : d = 0
    · simp [hd0]
    · have hd0' : conj d ≠ 0 := (map_ne_zero _).mpr hd0
      field_simp
  -- assembly
  show harmonicProjFun (RnmFun μ (ε • ν)) (wA (ε • ν) z) * (conj (dz (wA (ε • ν)) z) / dz (wA (ε • ν)) z) =
    _ * conj (harmonicProjU (RnmFunU mμ (fun u => conj ε * mν u)) (wU (fun u => conj ε * mν u) (conj (cayleyInv z))) *
      (conj (dz (wU (fun u => conj ε * mν u)) (conj (cayleyInv z))) /
        dz (wU (fun u => conj ε * mν u)) (conj (cayleyInv z))))
  have hdz := hdzw z hzne hxI hVxI
  have hdzx : dz V (cayleyInv z) = conj (dz V (conj (cayleyInv z))) := by
    have := hdzs _ hy
    rwa [Complex.conj_conj] at this
  rw [hwz, hdz, hVeq, hdzx]
  have hP : harmonicProjFun (RnmFun μ (ε • ν)) (cayley (V (cayleyInv z))) =
      (2 * I / (V (cayleyInv z) + I) ^ 2) / conj (2 * I / (V (cayleyInv z) + I) ^ 2) *
        conj (harmonicProjU (RnmFunU mμ (fun u => conj ε * mν u)) (conj (V (cayleyInv z)))) := by
    show (3 * (1 - ‖cayley (V (cayleyInv z))‖ ^ 2) ^ 2 / π : ℂ) * ∫ ζ in unitDiscExterior,
        RnmFun μ (ε • ν) ζ / (1 - ζ * conj (cayley (V (cayleyInv z)))) ^ 4 =
      (2 * I / (V (cayleyInv z) + I) ^ 2) / conj (2 * I / (V (cayleyInv z) + I) ^ 2) *
      conj (-(3 * (conj (V (cayleyInv z)) - conj (conj (V (cayleyInv z)))) ^ 2 / (π : ℂ)) *
        ∫ u in upperHalf, RnmFunU mμ (fun u => conj ε * mν u) u / (u - conj (conj (V (cayleyInv z)))) ^ 4)
    rw [p71_cov, ← integral_const_mul, ← integral_const_mul, ← integral_conj, ← integral_const_mul]
    refine integral_congr_ae ?_
    filter_upwards [hR, ae_restrict_mem hU, ae_restrict_of_ae (Measure.ae_ne volume I)] with η hRη hη hηI
    have hη0 : 0 < η.im := hη
    have hcηI : conj η + I ≠ 0 := by
      intro h; apply hηI
      have : conj (conj η) = conj (-I) := by rw [eq_neg_of_add_eq_zero_left h]
      rwa [Complex.conj_conj, map_neg, Complex.conj_I, neg_neg] at this
    have hT1 : 2 * I / (conj η + I) ^ 2 ≠ 0 :=
      div_ne_zero (mul_ne_zero two_ne_zero I_ne_zero) (pow_ne_zero _ hcηI)
    have hT1' : conj (2 * I / (conj η + I) ^ 2) ≠ 0 := (map_ne_zero _).mpr hT1
    have hX1 : 2 * I / (V (cayleyInv z) + I) ^ 2 ≠ 0 :=
      div_ne_zero (mul_ne_zero two_ne_zero I_ne_zero) (pow_ne_zero _ hVxI)
    have hX1' : conj (2 * I / (V (cayleyInv z) + I) ^ 2) ≠ 0 := (map_ne_zero _).mpr hX1
    have hk := p71_kernel hη hηI hXim hXI
    have hsq := p71_sq_phase hT1
    rw [hRη]
    calc (3 * (1 - ‖cayley (V (cayleyInv z))‖ ^ 2) ^ 2 / π : ℂ) * (((‖2 * I / (conj η + I) ^ 2‖ ^ 2 : ℝ) : ℂ) *
          ((2 * I / (conj η + I) ^ 2) / conj (2 * I / (conj η + I) ^ 2) *
            conj (RnmFunU mμ (fun u => conj ε * mν u) η) / (1 - cayley (conj η) * conj (cayley (V (cayleyInv z)))) ^ 4))
        = ((3 * (1 - ‖cayley (V (cayleyInv z))‖ ^ 2) ^ 2 / π : ℂ) *
            ((2 * I / (conj η + I) ^ 2) ^ 2 / (1 - cayley (conj η) * conj (cayley (V (cayleyInv z)))) ^ 4) *
            (conj (2 * I / (V (cayleyInv z) + I) ^ 2) / (2 * I / (V (cayleyInv z) + I) ^ 2))) *
          ((2 * I / (V (cayleyInv z) + I) ^ 2) / conj (2 * I / (V (cayleyInv z) + I) ^ 2)) *
            conj (RnmFunU mμ (fun u => conj ε * mν u) η) := by
          rw [← hsq]
          field_simp
      _ = _ := by
          rw [hk]
          simp only [map_mul, map_div₀, map_neg, map_pow, map_sub, Complex.conj_conj, Complex.conj_ofReal,
            map_ofNat]
          ring
  rw [hVs (cayleyInv z), hP]
  have hX1 : 2 * I / (V (cayleyInv z) + I) ^ 2 ≠ 0 :=
    div_ne_zero (mul_ne_zero two_ne_zero I_ne_zero) (pow_ne_zero _ hVxI)
  have hX1' : conj (2 * I / (V (cayleyInv z) + I) ^ 2) ≠ 0 := (map_ne_zero _).mpr hX1
  have hx1 : 2 * I / (cayleyInv z + I) ^ 2 ≠ 0 :=
    div_ne_zero (mul_ne_zero two_ne_zero I_ne_zero) (pow_ne_zero _ hxI)
  have hx1' : conj (2 * I / (cayleyInv z + I) ^ 2) ≠ 0 := (map_ne_zero _).mpr hx1
  rw [p71_DT hzne]
  generalize 2 * I / (V (cayleyInv z) + I) ^ 2 = TX at hX1 hX1' ⊢
  generalize 2 * I / (cayleyInv z + I) ^ 2 = Tx at hx1 hx1' ⊢
  generalize harmonicProjU (RnmFunU mμ fun u => conj ε * mν u) (conj (V (cayleyInv z))) = Pu
  generalize dz V (conj (cayleyInv z)) = d
  by_cases hd0 : d = 0
  · simp [hd0]
  · have hd0' : conj d ≠ 0 := (map_ne_zero _).mpr hd0
    simp only [map_mul, map_div₀, map_inv₀, Complex.conj_conj]
    field_simp

/-! ### (WM4) helpers `[W6]` -/

/-- `S = cayley` off its pole: `S'(w) = 2i/(w + i)²`. -/
theorem p71r_hasDeriv_cayley {w : ℂ} (hw : w + I ≠ 0) : HasDerivAt cayley (2 * I / (w + I) ^ 2) w := by
  have h := ((hasDerivAt_id w).sub_const I).div ((hasDerivAt_id w).add_const I) hw
  convert h using 1
  · rfl
  · simp only [id_eq]
    ring

/-- `S⁻¹ = cayleyInv` off `1`: `(S⁻¹)'(ζ) = 2i/(1 - ζ)²`. -/
theorem p71r_hasDeriv_cayleyInv {ζ : ℂ} (hζ : 1 - ζ ≠ 0) :
    HasDerivAt cayleyInv (2 * I / (1 - ζ) ^ 2) ζ := by
  have h := (((hasDerivAt_id ζ).const_add 1).const_mul I).div ((hasDerivAt_id ζ).const_sub 1) hζ
  convert h using 1
  · funext w
    rfl
  · simp only [id_eq]
    field_simp
    ring

/-- `S⁻¹ ∘ S = id` off the pole `-i`. -/
theorem p71r_inv_cayley {a : ℂ} (ha : a + I ≠ 0) : cayleyInv (cayley a) = a := by
  have h1 : (1 : ℂ) + cayley a = 2 * a / (a + I) := by rw [cayley]; field_simp; ring
  have h2 : (1 : ℂ) - cayley a = 2 * I / (a + I) := by rw [cayley]; field_simp; ring
  rw [cayleyInv, mul_div_assoc, h1, h2]
  field_simp

/-- `S ∘ S⁻¹ = id` off `1`, and `S⁻¹(ζ) + i = 2i/(1 - ζ)`. -/
theorem p71r_cayley_inv {ζ : ℂ} (hζ : 1 - ζ ≠ 0) :
    cayleyInv ζ + I = 2 * I / (1 - ζ) ∧ cayley (cayleyInv ζ) = ζ := by
  have h1 : cayleyInv ζ - I = I * (2 * ζ) / (1 - ζ) := by rw [cayleyInv]; field_simp; ring
  have h2 : cayleyInv ζ + I = 2 * I / (1 - ζ) := by rw [cayleyInv]; field_simp; ring
  have h2ne : cayleyInv ζ + I ≠ 0 := by rw [h2]; exact div_ne_zero (by simp) hζ
  refine ⟨h2, ?_⟩
  rw [cayley, div_eq_iff h2ne, h1, h2]
  field_simp

/-- `Im S⁻¹(ζ) = (1 - |ζ|²)/|1 - ζ|²`. -/
theorem p71r_im_cayleyInv {ζ : ℂ} (hζ : 1 - ζ ≠ 0) :
    (cayleyInv ζ).im = (1 - ‖ζ‖ ^ 2) / Complex.normSq (1 - ζ) := by
  have hpos : 0 < Complex.normSq (1 - ζ) := Complex.normSq_pos.mpr hζ
  rw [cayleyInv, Complex.div_im, ← Complex.normSq_eq_norm_sq]
  simp only [Complex.mul_im, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.add_re, Complex.add_im,
    Complex.one_re, Complex.one_im, Complex.sub_re, Complex.sub_im, Complex.normSq_apply]
  field_simp
  ring

/-- `1 - |S z|² = 4 Im z/|z + i|²` off the pole. -/
theorem p71r_bf {z : ℂ} (hd : z + I ≠ 0) : 1 - ‖cayley z‖ ^ 2 = 4 * z.im / Complex.normSq (z + I) := by
  have hn := Complex.normSq_pos.mpr hd
  rw [← Complex.normSq_eq_norm_sq, cayley, Complex.normSq_div, eq_div_iff hn.ne', sub_mul, one_mul,
    div_mul_cancel₀ _ hn.ne']
  exact normSq_cayley_key z

/-- `Φ(u) = S(ū)` preserves the resolvent kernel (1.19) and the densities: `u, v ∈ 𝕌 ∖ {i}`. -/
theorem p71r_iso {u v : ℂ} (hu : u ∈ upperHalf) (hv : v ∈ upperHalf) (hu' : u ≠ I) (hv' : v ≠ I) :
    resolventKernel (cayley (conj u)) (cayley (conj v)) = resolventKernelU u v ∧
      rho (cayley (conj v)) * ‖2 * I / (conj v + I) ^ 2‖ ^ 2 = rhoU v := by
  have hd : ∀ w : ℂ, w ≠ I → conj w + I ≠ 0 := fun w hw h => hw (by
    have := congrArg conj h
    simp only [map_add, Complex.conj_conj, Complex.conj_I, map_zero] at this
    linear_combination this)
  have hui : (conj u).im ≠ 0 := by rw [Complex.conj_im]; exact neg_ne_zero.2 (ne_of_gt hu)
  have hvi : (conj v).im ≠ 0 := by rw [Complex.conj_im]; exact neg_ne_zero.2 (ne_of_gt hv)
  have hun := (Complex.normSq_pos.mpr (hd u hu')).ne'
  have hvn := (Complex.normSq_pos.mpr (hd v hv')).ne'
  constructor
  · have hsub : cayley (conj u) - cayley (conj v) =
        2 * I * (conj u - conj v) / ((conj u + I) * (conj v + I)) := by
      have := hd u hu'
      have := hd v hv'
      unfold cayley
      field_simp
      ring
    have hnorm : ‖cayley (conj u) - cayley (conj v)‖ ^ 2 =
        4 * ‖u - v‖ ^ 2 / (Complex.normSq (conj u + I) * Complex.normSq (conj v + I)) := by
      rw [hsub, ← map_sub]
      simp only [norm_div, norm_mul, Complex.norm_I, mul_pow, div_pow, Complex.normSq_eq_norm_sq,
        Complex.norm_conj]
      norm_num
    have hpp : pointPair (cayley (conj u)) (cayley (conj v)) = pointPairU u v := by
      unfold pointPair pointPairU
      rw [p71r_bf (hd u hu'), p71r_bf (hd v hv'), hnorm, Complex.conj_im, Complex.conj_im]
      have h1 : u.im ≠ 0 := ne_of_gt hu
      have h2 : v.im ≠ 0 := ne_of_gt hv
      field_simp
    simp only [resolventKernel, resolventKernelU, hpp]
  · have hn : ‖2 * I / (conj v + I) ^ 2‖ ^ 2 = 4 / (Complex.normSq (conj v + I)) ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_div]
      simp only [map_pow, Complex.normSq_mul, Complex.normSq_ofNat, Complex.normSq_I]
      norm_num
    rw [hn]
    unfold rho rhoU
    rw [p71r_bf (hd v hv'), Complex.conj_im]
    have h2 : v.im ≠ 0 := ne_of_gt hv
    field_simp

/-- **Change of variables** `ζ = Φ(w) = S(w̄)`, `𝕌 ∖ {i} → 𝔻*`: `G f ∘ Φ = G_U (f ∘ Φ)` on `𝕌 ∖ {i}` (unconditional). -/
theorem p71r_cov (f : ℂ → ℂ) {u : ℂ} (hu : u ∈ upperHalf) (hu' : u ≠ I) :
    resolventStar f (cayley (conj u)) = resolventOpU (fun w => f (cayley (conj w))) u := by
  have hU := measurableSet_upperHalf_aux
  have hd : ∀ w : ℂ, w ≠ -I → w + I ≠ 0 := fun w hw h => hw (by linear_combination h)
  have hLo : IsOpen ({w : ℂ | w.im < 0} \ {-I}) :=
    (isOpen_lt Complex.continuous_im continuous_const).sdiff isClosed_singleton
  have hdiff : DifferentiableOn ℂ cayley ({w : ℂ | w.im < 0} \ {-I}) := fun w hw =>
    (p71r_hasDeriv_cayley (hd w hw.2)).differentiableAt.differentiableWithinAt
  have hinj : InjOn cayley ({w : ℂ | w.im < 0} \ {-I}) := fun a ha b hb hab => by
    rw [← p71r_inv_cayley (hd a ha.2), hab, p71r_inv_cayley (hd b hb.2)]
  have himg : cayley '' ({w : ℂ | w.im < 0} \ {-I}) = unitDiscExterior := by
    ext ζ
    constructor
    · rintro ⟨w, hw, rfl⟩
      have h1 := p71r_bf (hd w hw.2)
      have hneg : 4 * w.im / Complex.normSq (w + I) < 0 :=
        div_neg_of_neg_of_pos (by linarith [show w.im < 0 from hw.1]) (Complex.normSq_pos.mpr (hd w hw.2))
      show 1 < ‖cayley w‖
      nlinarith [norm_nonneg (cayley w)]
    · intro hζ
      have h1 : (1 : ℂ) - ζ ≠ 0 := fun h => by
        have : ζ = 1 := by linear_combination -h
        have h2 : (1 : ℝ) < ‖ζ‖ := hζ
        rw [this, norm_one] at h2
        exact lt_irrefl _ h2
      obtain ⟨hplus, hcay⟩ := p71r_cayley_inv h1
      refine ⟨cayleyInv ζ, ⟨?_, fun h => ?_⟩, hcay⟩
      · show (cayleyInv ζ).im < 0
        rw [p71r_im_cayleyInv h1]
        have h2 : (1 : ℝ) < ‖ζ‖ := hζ
        exact div_neg_of_neg_of_pos (by nlinarith) (Complex.normSq_pos.mpr h1)
      · have h3 : cayleyInv ζ + I = 0 := by rw [show cayleyInv ζ = -I from h]; ring
        rw [hplus] at h3
        exact div_ne_zero (by simp) h1 h3
  have hpre : (fun w : ℂ => conj w) ⁻¹' ({w : ℂ | w.im < 0} \ {-I}) = upperHalf \ {I} := by
    ext w
    simp only [mem_preimage, Set.mem_sdiff, mem_setOf_eq, mem_singleton_iff, Complex.conj_im]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨show 0 < w.im by linarith, fun h => h2 (by rw [h, Complex.conj_I])⟩
    · rintro ⟨h1, h2⟩
      refine ⟨by linarith [show 0 < w.im from h1], fun h => h2 ?_⟩
      have := congrArg conj h
      simpa using this
  have hnull : (upperHalf \ {I} : Set ℂ) =ᵐ[volume] upperHalf := diff_null_ae_eq_self (measure_singleton I)
  unfold resolventStar resolventOp resolventOpU
  rw [← himg, ahP_integral_image hLo hdiff hinj,
    ← gzE_conj_measurePreserving.setIntegral_preimage_emb Complex.conjLIE.toHomeomorph.measurableEmbedding _ _,
    hpre, setIntegral_congr_set hnull.symm]
  refine setIntegral_congr_fun (hU.diff (measurableSet_singleton I)) fun v hv => ?_
  obtain ⟨hK, hρ⟩ := p71r_iso hu hv.1 hu' hv.2
  have hvd : conj v + I ≠ 0 := fun h => hv.2 (mem_singleton_iff.2 (by
    have := congrArg conj h
    simp only [map_add, Complex.conj_conj, Complex.conj_I, map_zero] at this
    linear_combination this))
  rw [(p71r_hasDeriv_cayley hvd).deriv, hK, ← hρ, Complex.real_smul]
  push_cast
  ring

/-- **Chain rule through `Φ⁻¹ = conj ∘ A`**, `A` holomorphic with a differentiable local inverse `B`:
`∂_ζ̄ (h ∘ conj ∘ A)(ζ) = (∂h)(\overline{A ζ}) \overline{A'(ζ)}`, for every `h` (both sides are `0` when `h` is not
differentiable). -/
theorem p71r_chain {h A B : ℂ → ℂ} {ζ a : ℂ} (hA : HasDerivAt A a ζ) (hB : DifferentiableAt ℝ B (conj (A ζ)))
    (hBζ : B (conj (A ζ)) = ζ) (hAB : ∀ᶠ w in 𝓝 (conj (A ζ)), conj (A (B w)) = w) :
    dzbar (fun ζ' => h (conj (A ζ'))) ζ = dz h (conj (A ζ)) * conj a := by
  by_cases hd : DifferentiableAt ℝ h (conj (A ζ))
  · have hc : HasFDerivAt (fun ζ' => h (conj (A ζ'))) ((fderiv ℝ h (conj (A ζ))).comp
        ((Complex.conjCLE : ℂ →L[ℝ] ℂ).comp
          ((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) a).restrictScalars ℝ))) ζ :=
      hd.hasFDerivAt.comp ζ ((Complex.conjCLE : ℂ →L[ℝ] ℂ).hasFDerivAt.comp ζ
        (hA.hasFDerivAt.restrictScalars ℝ))
    unfold dzbar dz
    rw [hc.fderiv]
    have hlin : ∀ x : ℂ, fderiv ℝ h (conj (A ζ)) x =
        x.re * fderiv ℝ h (conj (A ζ)) 1 + x.im * fderiv ℝ h (conj (A ζ)) I := by
      intro x
      conv_lhs => rw [← Complex.re_add_im x]
      rw [show (x.re : ℂ) + x.im * I = x.re • (1 : ℂ) + x.im • I by simp [Complex.real_smul], map_add,
        map_smul, map_smul, Complex.real_smul, Complex.real_smul]
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_restrictScalars',
      ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.one_apply, ContinuousLinearEquiv.coe_coe,
      Complex.conjCLE_apply, one_smul, smul_eq_mul, one_mul]
    rw [hlin (conj a), hlin (conj (I * a))]
    simp only [Complex.conj_re, Complex.conj_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
      zero_mul, one_mul, zero_sub, sub_zero, zero_add, neg_neg]
    rw [show conj a = (a.re : ℂ) - (a.im : ℂ) * I by apply Complex.ext <;> simp]
    push_cast
    linear_combination (-(a.im : ℂ) * fderiv ℝ h (conj (A ζ)) I / 2) * Complex.I_sq
  · have hnd : ¬ DifferentiableAt ℝ (fun ζ' => h (conj (A ζ'))) ζ := by
      intro hc
      apply hd
      have hc' : DifferentiableAt ℝ (fun ζ' => h (conj (A ζ'))) (B (conj (A ζ))) := by rw [hBζ]; exact hc
      refine (hc'.comp (conj (A ζ)) hB).congr_of_eventuallyEq ?_
      filter_upwards [hAB] with w hw
      simp only [Function.comp_apply, hw]
    unfold dzbar dz
    rw [fderiv_zero_of_not_differentiableAt hnd, fderiv_zero_of_not_differentiableAt hd]
    simp

/-- `∂_z̄ (F g) = (∂_z̄ F) g` for `g` holomorphic and nonvanishing at the point, for every `F`. -/
theorem p71r_mul_holo {F g : ℂ → ℂ} {z : ℂ} (hg : DifferentiableAt ℂ g z) (hg0 : g z ≠ 0) :
    dzbar (fun w => F w * g w) z = dzbar F z * g z := by
  by_cases hF : DifferentiableAt ℝ F z
  · have hgr : DifferentiableAt ℝ g z := hg.restrictScalars ℝ
    unfold dzbar
    rw [show (fun w => F w * g w) = F * g from rfl, fderiv_mul hF hgr]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
    have e : ∀ x, fderiv ℝ g z x = fderiv ℂ g z x := fun x => by rw [hg.fderiv_restrictScalars ℝ]; rfl
    have hI : fderiv ℂ g z I = I * fderiv ℂ g z 1 := by
      rw [← smul_eq_mul, ← map_smul, smul_eq_mul, mul_one]
    rw [e, e, hI]
    linear_combination (F z * fderiv ℂ g z 1 / 2) * Complex.I_sq
  · have hnd : ¬ DifferentiableAt ℝ (fun w => F w * g w) z := by
      intro hc
      apply hF
      refine (hc.mul ((hg.inv hg0).restrictScalars ℝ)).congr_of_eventuallyEq ?_
      filter_upwards [hg.continuousAt.eventually_ne hg0] with w hw
      simp only [Pi.mul_apply, Pi.inv_apply]
      field_simp
    unfold dzbar
    rw [fderiv_zero_of_not_differentiableAt hnd, fderiv_zero_of_not_differentiableAt hF]
    simp

/-- `∂_z̄ \overline{F} = \overline{∂_z F}`, for every `F`. -/
theorem p71r_dzbar_conj (F : ℂ → ℂ) (w : ℂ) : dzbar (fun x => conj (F x)) w = conj (dz F w) := by
  have h : fderiv ℝ (fun x => conj (F x)) w = (Complex.conjCLE : ℂ →L[ℝ] ℂ).comp (fderiv ℝ F w) :=
    Complex.conjCLE.comp_fderiv (f := F) (x := w)
  unfold dzbar dz
  rw [h]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe, Complex.conjCLE_apply, map_div₀,
    map_sub, map_mul, Complex.conj_I, map_ofNat]
  ring

/-- `∂_z̄` only sees germs. -/
theorem p71r_dzbar_congr {F G : ℂ → ℂ} {z : ℂ} (h : F =ᶠ[𝓝 z] G) : dzbar F z = dzbar G z := by
  unfold dzbar
  rw [h.fderiv_eq]

/-- (WM4) `[W2 or W?]` **Transformation law of `∂_z̄ ρ⁻¹ ∂_z̄ G`.** For any `f` and `z ∈ 𝔻*`, with the same phase `c(z)`
as WM3. Route: `Φ(u) = S(ū)` is an isometry `𝕌 → 𝔻*` (`ρ ∘ Φ |Φ_ū|² = ρ_U`, both resolvent kernels are
`sinh²(d/2)`), so `G f ∘ Φ = G_U (f ∘ Φ)`; `G_U` has a real kernel, so `conj (G f ∘ Φ) = G_U (conj (f ∘ Φ))`; then the
chain rule for the holomorphic `S` and for `conj` (both sides are junk `0` together, `Φ` being a diffeomorphism). -/
theorem p71_wm_rhs (f : ℂ → ℂ) {z : ℂ} (hz : z ∈ unitDiscExterior) :
    dzbar (fun w => (rho w : ℂ)⁻¹ * dzbar (resolventStar f) w) z =
      (2 * I / (cayleyInv z + I) ^ 2) / conj (2 * I / (cayleyInv z + I) ^ 2) *
        conj (dzbar (fun w => (rhoU w : ℂ)⁻¹ * dzbar (resolventOpU fun u => conj (f (cayley (conj u)))) w)
          (conj (cayleyInv z))) := by
  have hO : IsOpen unitDiscExterior := isOpen_lt continuous_const continuous_norm
  obtain ⟨h, hh⟩ : ∃ h : ℂ → ℂ, h = resolventOpU (fun u => f (cayley (conj u))) := ⟨_, rfl⟩
  obtain ⟨q, hq⟩ : ∃ q : ℂ → ℂ, q = fun w => (rhoU w : ℂ)⁻¹ * dz h w := ⟨_, rfl⟩
  -- the inverse chart `Φ⁻¹ = conj ∘ cayleyInv` on `𝔻*`
  have hpt : ∀ ζ ∈ unitDiscExterior, 1 - ζ ≠ 0 ∧ conj (cayleyInv ζ) ∈ upperHalf ∧ conj (cayleyInv ζ) ≠ I ∧
      cayley (conj (conj (cayleyInv ζ))) = ζ := by
    intro ζ hζ
    have h1 : (1 : ℂ) - ζ ≠ 0 := fun h => by
      have : ζ = 1 := by linear_combination -h
      have h2 : (1 : ℝ) < ‖ζ‖ := hζ
      rw [this, norm_one] at h2
      exact lt_irrefl _ h2
    obtain ⟨hplus, hcay⟩ := p71r_cayley_inv h1
    refine ⟨h1, ?_, fun h => ?_, by rw [Complex.conj_conj, hcay]⟩
    · show 0 < (conj (cayleyInv ζ)).im
      rw [Complex.conj_im, p71r_im_cayleyInv h1]
      have h2 : (1 : ℝ) < ‖ζ‖ := hζ
      have := div_neg_of_neg_of_pos (by nlinarith : 1 - ‖ζ‖ ^ 2 < 0) (Complex.normSq_pos.mpr h1)
      linarith
    · have h3 : cayleyInv ζ + I = 0 := by
        have := congrArg conj h
        rw [Complex.conj_conj, Complex.conj_I] at this
        rw [this]
        ring
      rw [hplus] at h3
      exact div_ne_zero (by simp) h1 h3
  have hH : ∀ ζ ∈ unitDiscExterior, resolventStar f ζ = h (conj (cayleyInv ζ)) := by
    intro ζ hζ
    obtain ⟨-, hy, hyI, hcay⟩ := hpt ζ hζ
    rw [hh, ← p71r_cov f hy hyI, hcay]
  -- first derivative
  have hL1 : ∀ ζ ∈ unitDiscExterior,
      dzbar (resolventStar f) ζ = dz h (conj (cayleyInv ζ)) * conj (2 * I / (1 - ζ) ^ 2) := by
    intro ζ hζ
    obtain ⟨h1, hy, hyI, hcay⟩ := hpt ζ hζ
    have hev : resolventStar f =ᶠ[𝓝 ζ] fun ζ' => h (conj (cayleyInv ζ')) :=
      Filter.eventually_of_mem (hO.mem_nhds hζ) hH
    have hyd : conj (conj (cayleyInv ζ)) + I ≠ 0 := by
      rw [Complex.conj_conj, (p71r_cayley_inv h1).1]
      exact div_ne_zero (by simp) h1
    have hB : DifferentiableAt ℝ (fun w => cayley (conj w)) (conj (cayleyInv ζ)) :=
      ((p71r_hasDeriv_cayley hyd).differentiableAt.restrictScalars ℝ).comp _
        (Complex.conjCLE : ℂ →L[ℝ] ℂ).differentiableAt
    have hAB : ∀ᶠ w in 𝓝 (conj (cayleyInv ζ)), conj (cayleyInv (cayley (conj w))) = w := by
      filter_upwards [isOpen_compl_singleton.mem_nhds hyI] with w hw
      have hwd : conj w + I ≠ 0 := fun h => hw (mem_singleton_iff.2 (by
        have := congrArg conj h
        simp only [map_add, Complex.conj_conj, Complex.conj_I, map_zero] at this
        linear_combination this))
      rw [p71r_inv_cayley hwd, Complex.conj_conj]
    rw [p71r_dzbar_congr hev]
    exact p71r_chain (p71r_hasDeriv_cayleyInv h1) hB hcay hAB
  -- the density: `ρ(ζ) = ρ_U(\overline{A ζ}) |A'(ζ)|²`
  have hρ : ∀ ζ ∈ unitDiscExterior,
      (rho ζ : ℂ) = (rhoU (conj (cayleyInv ζ)) : ℂ) * ((2 * I / (1 - ζ) ^ 2) * conj (2 * I / (1 - ζ) ^ 2)) := by
    intro ζ hζ
    obtain ⟨h1, -, -, -⟩ := hpt ζ hζ
    have h2 : (1 : ℝ) < ‖ζ‖ := hζ
    have hn : 0 < Complex.normSq (1 - ζ) := Complex.normSq_pos.mpr h1
    have hden : 1 - ‖ζ‖ ^ 2 ≠ 0 := by nlinarith
    rw [Complex.mul_conj, Complex.normSq_div, Complex.normSq_mul, Complex.normSq_I, Complex.normSq_ofNat,
      map_pow]
    unfold rho rhoU
    rw [Complex.conj_im, p71r_im_cayleyInv h1, ← Complex.normSq_eq_norm_sq]
    have hns : Complex.normSq ζ ≠ 1 := by
      rw [Complex.normSq_eq_norm_sq]
      intro h
      apply hden
      linarith
    have hA : (1 - (Complex.normSq ζ : ℂ)) ≠ 0 := by exact_mod_cast sub_ne_zero.2 (Ne.symm hns)
    have hB : (Complex.normSq (1 - ζ) : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
    push_cast
    field_simp
    ring
  -- second derivative
  have hL2 : ∀ ζ ∈ unitDiscExterior, (rho ζ : ℂ)⁻¹ * dzbar (resolventStar f) ζ =
      q (conj (cayleyInv ζ)) * (1 / (2 * I / (1 - ζ) ^ 2)) := by
    intro ζ hζ
    obtain ⟨h1, hy, -, -⟩ := hpt ζ hζ
    have ha : (2 * I / (1 - ζ) ^ 2) ≠ 0 := div_ne_zero (by simp) (pow_ne_zero _ h1)
    have hca : conj (2 * I / (1 - ζ) ^ 2) ≠ 0 := (map_ne_zero _).2 ha
    have hr : (rhoU (conj (cayleyInv ζ)) : ℂ) ≠ 0 := by
      unfold rhoU
      have : 0 < (conj (cayleyInv ζ)).im := hy
      exact_mod_cast (inv_pos.2 (pow_pos this 2)).ne'
    rw [hL1 ζ hζ, hρ ζ hζ, hq]
    field_simp
  have hgd : DifferentiableAt ℂ (fun ζ => 1 / (2 * I / (1 - ζ) ^ 2)) z := by
    obtain ⟨h1, -, -, -⟩ := hpt z hz
    exact (differentiableAt_const _).div ((differentiableAt_const _).div
      ((differentiableAt_const _).sub differentiableAt_id |>.pow 2) (pow_ne_zero _ h1))
      (div_ne_zero (by simp) (pow_ne_zero _ h1))
  -- the left side
  have hLHS : dzbar (fun w => (rho w : ℂ)⁻¹ * dzbar (resolventStar f) w) z =
      dz q (conj (cayleyInv z)) * conj (2 * I / (1 - z) ^ 2) * (1 / (2 * I / (1 - z) ^ 2)) := by
    obtain ⟨h1, hy, hyI, hcay⟩ := hpt z hz
    have hev : (fun w => (rho w : ℂ)⁻¹ * dzbar (resolventStar f) w) =ᶠ[𝓝 z]
        fun ζ => q (conj (cayleyInv ζ)) * (1 / (2 * I / (1 - ζ) ^ 2)) :=
      Filter.eventually_of_mem (hO.mem_nhds hz) hL2
    have hyd : conj (conj (cayleyInv z)) + I ≠ 0 := by
      rw [Complex.conj_conj, (p71r_cayley_inv h1).1]
      exact div_ne_zero (by simp) h1
    have hB : DifferentiableAt ℝ (fun w => cayley (conj w)) (conj (cayleyInv z)) :=
      ((p71r_hasDeriv_cayley hyd).differentiableAt.restrictScalars ℝ).comp _
        (Complex.conjCLE : ℂ →L[ℝ] ℂ).differentiableAt
    have hAB : ∀ᶠ w in 𝓝 (conj (cayleyInv z)), conj (cayleyInv (cayley (conj w))) = w := by
      filter_upwards [isOpen_compl_singleton.mem_nhds hyI] with w hw
      have hwd : conj w + I ≠ 0 := fun h => hw (mem_singleton_iff.2 (by
        have := congrArg conj h
        simp only [map_add, Complex.conj_conj, Complex.conj_I, map_zero] at this
        linear_combination this))
      rw [p71r_inv_cayley hwd, Complex.conj_conj]
    have e : dzbar (fun w => (rho w : ℂ)⁻¹ * dzbar (resolventStar f) w) z =
        dzbar (fun ζ => q (conj (cayleyInv ζ)) * (1 / (2 * I / (1 - ζ) ^ 2))) z := by
      exact p71r_dzbar_congr hev
    rw [e, p71r_mul_holo hgd (div_ne_zero one_ne_zero (div_ne_zero (by simp) (pow_ne_zero _ h1))),
      p71r_chain (p71r_hasDeriv_cayleyInv h1) hB hcay hAB]
  -- the right side: `G_U (conj (f ∘ Φ)) = conj h`, real kernel
  have hconj : resolventOpU (fun u => conj (f (cayley (conj u)))) = fun w => conj (h w) := by
    funext w
    rw [hh]
    unfold resolventOpU
    rw [← integral_conj]
    refine integral_congr_ae (Eventually.of_forall fun v => ?_)
    simp only [map_mul, Complex.conj_ofReal]
  have hin : (fun w => (rhoU w : ℂ)⁻¹ * dzbar (fun w => conj (h w)) w) = fun w => conj (q w) := by
    funext w
    rw [p71r_dzbar_conj, hq]
    simp only [map_mul, map_inv₀, Complex.conj_ofReal]
  rw [hLHS, hconj, hin, p71r_dzbar_conj, Complex.conj_conj]
  obtain ⟨h1, -, -, -⟩ := hpt z hz
  have hS : 2 * I / (cayleyInv z + I) ^ 2 = 1 / (2 * I / (1 - z) ^ 2) := by
    rw [(p71r_cayley_inv h1).1]
    field_simp
  have ha : (2 * I / (1 - z) ^ 2) ≠ 0 := div_ne_zero (by simp) (pow_ne_zero _ h1)
  have hca : conj (2 * I / (1 - z) ^ 2) ≠ 0 := (map_ne_zero _).2 ha
  have e : conj (1 / (2 * I / (1 - z) ^ 2)) = 1 / conj (2 * I / (1 - z) ^ 2) := by rw [map_div₀, map_one]
  rw [hS, e]
  field_simp

/-- (WM4') `[W2]` **Glue for the right side.** The product `m[gμ] \overline{m[gν]}` equals `\overline{(μν̄) ∘ Φ}` a.e. on
`𝕌` (unimodular phases; `u = i` is the only degenerate point), so the two resolvents agree. -/
theorem p71_wm_prod {μ ν : LinfStar} {gμ gν : ℂ → ℂ}
    (hgμ : ∀ᵐ z ∂(volume.restrict unitDiscExterior), μ z = gμ z)
    (hgν : ∀ᵐ z ∂(volume.restrict unitDiscExterior), ν z = gν z) {mμ mν : ℂ → ℂ}
    (hmμ : ∀ u ∈ upperHalf, u ≠ I → mμ u = conj (gμ (cayley (conj u))) * (cayley u ^ 2 / conj (cayley u) ^ 2) *
      (conj (2 * I / (u + I) ^ 2) / (2 * I / (u + I) ^ 2)))
    (hmν : ∀ u ∈ upperHalf, u ≠ I → mν u = conj (gν (cayley (conj u))) * (cayley u ^ 2 / conj (cayley u) ^ 2) *
      (conj (2 * I / (u + I) ^ 2) / (2 * I / (u + I) ^ 2))) :
    (resolventOpU fun u => mμ u * conj (mν u)) =
      resolventOpU fun u => conj ((fun w => μ w * conj (ν w)) (cayley (conj u))) := by
  funext y
  show ∫ w in upperHalf, (resolventKernelU y w : ℂ) * (mμ w * conj (mν w)) * rhoU w =
    ∫ w in upperHalf, (resolventKernelU y w : ℂ) * conj ((fun w => μ w * conj (ν w)) (cayley (conj w))) * rhoU w
  refine integral_congr_ae ?_
  filter_upwards [ae_restrict_mem measurableSet_upperHalf_aux, p71_phi_ae hgμ, p71_phi_ae hgν,
    ae_restrict_of_ae (Measure.ae_ne volume I)] with u hu e1 e2 hui
  have hu0 : 0 < u.im := hu
  have h1 : u + I ≠ 0 := cayley_den_ne_zero hu0
  have hs : cayley u ≠ 0 := by
    show (u - I) / (u + I) ≠ 0
    exact div_ne_zero (sub_ne_zero.mpr hui) h1
  have hs' : conj (cayley u) ≠ 0 := (map_ne_zero _).mpr hs
  have hd : 2 * I / (u + I) ^ 2 ≠ 0 := div_ne_zero (mul_ne_zero two_ne_zero I_ne_zero) (pow_ne_zero _ h1)
  have hd' : conj (2 * I / (u + I) ^ 2) ≠ 0 := (map_ne_zero _).mpr hd
  have hgen : ∀ y : ℂ, y ≠ 0 → y / conj y * conj (y / conj y) = 1 := fun y hy => by
    have hy' : conj y ≠ 0 := (map_ne_zero _).mpr hy
    rw [map_div₀, Complex.conj_conj]
    field_simp
  have hA : cayley u ^ 2 / conj (cayley u) ^ 2 * conj (cayley u ^ 2 / conj (cayley u) ^ 2) = 1 := by
    have := hgen (cayley u ^ 2) (pow_ne_zero _ hs)
    rwa [map_pow] at this
  have hB : conj (2 * I / (u + I) ^ 2) / (2 * I / (u + I) ^ 2) *
      conj (conj (2 * I / (u + I) ^ 2) / (2 * I / (u + I) ^ 2)) = 1 := by
    have := hgen (conj (2 * I / (u + I) ^ 2)) hd'
    rwa [Complex.conj_conj] at this
  have e : mμ u * conj (mν u) = conj ((fun w => μ w * conj (ν w)) (cayley (conj u))) := by
    rw [hmμ u hu hui, hmν u hu hui]
    simp only
    rw [e1, e2]
    calc conj (gμ (cayley (conj u))) * (cayley u ^ 2 / conj (cayley u) ^ 2) *
          (conj (2 * I / (u + I) ^ 2) / (2 * I / (u + I) ^ 2)) *
          conj (conj (gν (cayley (conj u))) * (cayley u ^ 2 / conj (cayley u) ^ 2) *
            (conj (2 * I / (u + I) ^ 2) / (2 * I / (u + I) ^ 2)))
        = conj (gμ (cayley (conj u))) * gν (cayley (conj u)) *
            (cayley u ^ 2 / conj (cayley u) ^ 2 * conj (cayley u ^ 2 / conj (cayley u) ^ 2)) *
            (conj (2 * I / (u + I) ^ 2) / (2 * I / (u + I) ^ 2) *
              conj (conj (2 * I / (u + I) ^ 2) / (2 * I / (u + I) ^ 2))) := by
          rw [map_mul, map_mul, Complex.conj_conj]; ring
      _ = conj (gμ (cayley (conj u)) * conj (gν (cayley (conj u)))) := by
          rw [hA, hB, map_mul, Complex.conj_conj]; ring
  rw [e]

/-- (WM5) `[W2]` **`ε`-bookkeeping.** If `F(ε) = c · \overline{G(ε̄)}` near `0` and `G` is real-differentiable at `0`,
then `∂_ε F(0) = c · \overline{∂_η G(0)}` and `∂_ε̄ F(0) = c · \overline{∂_η̄ G(0)}`. -/
theorem p71_wm_eps {F G : ℂ → ℂ} {c : ℂ} (hFG : ∀ᶠ ε in 𝓝 (0 : ℂ), F ε = c * conj (G (conj ε)))
    (hG : DifferentiableAt ℝ G 0) :
    dz F 0 = c * conj (dz G 0) ∧ dzbar F 0 = c * conj (dzbar G 0) := by
  have hh := abR_x_dz_dzbar_conj (h := G) (z := 0) (by rw [map_zero]; exact hG)
  have hfd : fderiv ℝ F 0 = fderiv ℝ (fun ε => c * conj (G (conj ε))) 0 :=
    Filter.EventuallyEq.fderiv_eq (show F =ᶠ[𝓝 0] fun ε => c * conj (G (conj ε)) from hFG)
  have hc : fderiv ℝ (fun ε => c * conj (G (conj ε))) 0 = c • fderiv ℝ (fun ε => conj (G (conj ε))) 0 :=
    fderiv_const_mul hh.1 c
  obtain ⟨-, h2, h3⟩ := hh
  rw [map_zero] at h2 h3
  refine ⟨?_, ?_⟩
  · rw [← h2]
    show (fderiv ℝ F 0 1 - I * fderiv ℝ F 0 I) / 2 =
      c * ((fderiv ℝ (fun w => conj (G (conj w))) 0 1 - I * fderiv ℝ (fun w => conj (G (conj w))) 0 I) / 2)
    rw [hfd, hc, ContinuousLinearMap.smul_apply, ContinuousLinearMap.smul_apply, smul_eq_mul, smul_eq_mul]
    ring
  · rw [← h3]
    show (fderiv ℝ F 0 1 + I * fderiv ℝ F 0 I) / 2 =
      c * ((fderiv ℝ (fun w => conj (G (conj w))) 0 1 + I * fderiv ℝ (fun w => conj (G (conj w))) 0 I) / 2)
    rw [hfd, hc, ContinuousLinearMap.smul_apply, ContinuousLinearMap.smul_apply, smul_eq_mul, smul_eq_mul]
    ring

/-- `Im C(x) · |1 - x|² = 1 - |x|²` for `C(x) = i(1 + x)/(1 - x)` (as `ltd_C_im`). -/
theorem p71_C_im {x : ℂ} (hx : x ≠ 1) : (cayleyInv x).im * normSq (1 - x) = 1 - normSq x := by
  have h : normSq (1 - x) ≠ 0 := by
    rw [Ne, normSq_eq_zero]
    exact sub_ne_zero.mpr (Ne.symm hx)
  show (I * (1 + x) / (1 - x)).im * normSq (1 - x) = 1 - normSq x
  rw [Complex.div_im]
  simp only [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im]
  rw [sub_mul, div_mul_cancel₀ _ h, div_mul_cancel₀ _ h, normSq_apply]
  ring

/-- **(A0)** `[W1]` `y = \overline{cayleyInv z} ∈ 𝕌` for `z ∈ 𝔻*` (`ltd_C_im`). -/
theorem p71_y_mem {z : ℂ} (hz : z ∈ unitDiscExterior) : conj (cayleyInv z) ∈ upperHalf := by
  have hz1 : z ≠ 1 := by
    intro h
    have : ‖z‖ = 1 := by rw [h, norm_one]
    have hz' : 1 < ‖z‖ := hz
    linarith
  have h := p71_C_im hz1
  have hn : 0 < normSq (1 - z) := normSq_pos.mpr (sub_ne_zero.mpr (Ne.symm hz1))
  have hzz : 1 < normSq z := by
    rw [Complex.normSq_eq_norm_sq]
    have hz' : 1 < ‖z‖ := hz
    nlinarith
  have him : (cayleyInv z).im < 0 := by
    by_contra hc
    push Not at hc
    nlinarith [mul_nonneg hc hn.le]
  show 0 < (conj (cayleyInv z)).im
  rw [Complex.conj_im]
  linarith

/-! ### The `𝕌`-model Proposition 7.1 `[W1]` -/

/-- Quotient rule for complex differentiability on `ℂ × ℂ`. -/
theorem p71_dA_div {f g : ℂ × ℂ → ℂ} {q : ℂ × ℂ} (hf : DifferentiableAt ℂ f q) (hg : DifferentiableAt ℂ g q)
    (hne : g q ≠ 0) : DifferentiableAt ℂ (fun x => f x / g x) q := by
  exact (hf.mul (hg.inv hne)).congr_of_eventuallyEq (Eventually.of_forall fun x => div_eq_mul_inv _ _)

/-- `∂_z̄` depends only on the germ. -/
theorem p71_dzbar_congr {f g : ℂ → ℂ} {z : ℂ} (h : f =ᶠ[𝓝 z] g) : dzbar f z = dzbar g z := by
  simp only [dzbar, h.fderiv_eq]

/-- `∂_z̄` of `y ↦ H(y, ȳ)` is the second partial derivative of a jointly holomorphic `H`. -/
theorem p71_dzbar_partial {H : ℂ × ℂ → ℂ} {y : ℂ} (hH : DifferentiableAt ℂ H (y, conj y)) :
    dzbar (fun y => H (y, conj y)) y = deriv (fun b => H (y, b)) (conj y) := by
  set D := fderiv ℂ H (y, conj y) with hDd
  have hd : HasFDerivAt (fun y : ℂ => H (y, conj y))
      ((D.restrictScalars ℝ).comp ((ContinuousLinearMap.id ℝ ℂ).prod
        (Complex.conjCLE : ℂ ≃L[ℝ] ℂ).toContinuousLinearMap)) y :=
    (hH.hasFDerivAt.restrictScalars ℝ).comp y ((hasFDerivAt_id y).prodMk
      (Complex.conjCLE : ℂ ≃L[ℝ] ℂ).hasFDerivAt)
  have hb : HasDerivAt (fun b => H (y, b)) (D (0, 1)) (conj y) :=
    (hH.hasFDerivAt.comp (conj y) (hasFDerivAt_prodMk_right y (conj y))).hasDerivAt
  rw [hb.deriv]
  unfold dzbar
  rw [hd.fderiv]
  simp only [ContinuousLinearMap.coe_comp, Function.comp_apply, ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.coe_id', id, ContinuousLinearEquiv.coe_coe, Complex.conjCLE_apply,
    ContinuousLinearMap.coe_restrictScalars', map_one, Complex.conj_I]
  have e1 : ((1 : ℂ), (1 : ℂ)) = ((1 : ℂ), (0 : ℂ)) + ((0 : ℂ), (1 : ℂ)) := by ext <;> simp
  have e2 : (I, -I) = I • ((1 : ℂ), (0 : ℂ)) + (-I) • ((0 : ℂ), (1 : ℂ)) := by ext <;> simp
  rw [e1, e2, map_add, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
  ring_nf
  rw [Complex.I_sq]
  ring

/-- **(U1)** `[W1]` **Pointwise second `z̄`-derivative of the Corollary 6.4 kernel.** For `u, v, z ∈ 𝕌`, with
`B_y(u, v) = (y - ȳ)²/((u - v̄)²(y - v̄)²(u - ȳ)²) + (y - ȳ)³/((u - ȳ)³(u - v̄)(y - v̄)³)` and `ρ_𝕌(y)⁻¹ = (Im y)²`:
`∂_z̄ (ρ_𝕌⁻¹ ∂_z̄ B)(z) = -(3/2)(z - z̄)² ((u - z)²/((u - z̄)⁴(v̄ - z)²(u - v̄)²) + 2(z - z̄)(z - u)²/((u - z̄)⁵(z - v̄)³(u - v̄)))`
(rational Wirtinger calculus; checked numerically). -/
theorem p71_kernel_dd {u v z : ℂ} (hu : u ∈ upperHalf) (hv : v ∈ upperHalf) (hz : z ∈ upperHalf) :
    dzbar (fun y => (rhoU y : ℂ)⁻¹ * dzbar (fun y' => (y' - conj y') ^ 2 / ((u - conj v) ^ 2 * (y' - conj v) ^ 2 *
        (u - conj y') ^ 2) + (y' - conj y') ^ 3 / ((u - conj y') ^ 3 * (u - conj v) * (y' - conj v) ^ 3)) y) z =
      -(3 / 2) * (z - conj z) ^ 2 * ((u - z) ^ 2 / ((u - conj z) ^ 4 * (conj v - z) ^ 2 * (u - conj v) ^ 2) +
        2 * (z - conj z) * (z - u) ^ 2 / ((u - conj z) ^ 5 * (z - conj v) ^ 3 * (u - conj v))) := by
  have hzim : 0 < z.im := hz
  have huim : 0 < u.im := hu
  have hvim : 0 < v.im := hv
  set V := conj v with hVd
  have hVim : V.im < 0 := by rw [hVd, Complex.conj_im]; linarith
  have hne1 : ∀ a : ℂ, 0 < a.im → a - V ≠ 0 := fun a ha h => by
    have := congrArg Complex.im h; rw [Complex.sub_im, Complex.zero_im] at this; linarith
  have hne2 : ∀ b : ℂ, b.im < 0 → u - b ≠ 0 := fun b hb h => by
    have := congrArg Complex.im h; rw [Complex.sub_im, Complex.zero_im] at this; linarith
  have huV : u - V ≠ 0 := hne1 u huim
  have hcim : ∀ y : ℂ, 0 < y.im → (conj y).im < 0 := fun y hy => by rw [Complex.conj_im]; linarith
  -- the first partial `∂_b B̂`
  set D1 : ℂ → ℂ → ℂ := fun a b => 2 * (a - b) * (a - u) / ((u - V) ^ 2 * (a - V) ^ 2 * (u - b) ^ 3) +
    3 * (a - b) ^ 2 * (a - u) / ((u - V) * (a - V) ^ 3 * (u - b) ^ 4) with hD1
  have hB1 : ∀ y : ℂ, 0 < y.im → dzbar (fun y' => (y' - conj y') ^ 2 / ((u - V) ^ 2 * (y' - V) ^ 2 *
      (u - conj y') ^ 2) + (y' - conj y') ^ 3 / ((u - conj y') ^ 3 * (u - V) * (y' - V) ^ 3)) y = D1 y (conj y) := by
    intro y hy
    have ha := hne1 y hy
    have hb := hne2 (conj y) (hcim y hy)
    have hH : DifferentiableAt ℂ (fun q : ℂ × ℂ => (q.1 - q.2) ^ 2 / ((u - V) ^ 2 * (q.1 - V) ^ 2 *
        (u - q.2) ^ 2) + (q.1 - q.2) ^ 3 / ((u - q.2) ^ 3 * (u - V) * (q.1 - V) ^ 3)) (y, conj y) := by
      have h1 : DifferentiableAt ℂ (fun q : ℂ × ℂ => q.1) (y, conj y) := differentiableAt_fst
      have h2 : DifferentiableAt ℂ (fun q : ℂ × ℂ => q.2) (y, conj y) := differentiableAt_snd
      refine (p71_dA_div ((h1.sub h2).pow 2) (((differentiableAt_const _).mul ((h1.sub_const V).pow 2)).mul
        (((differentiableAt_const u).sub h2).pow 2)) ?_).add (p71_dA_div ((h1.sub h2).pow 3)
        (((((differentiableAt_const u).sub h2).pow 3).mul (differentiableAt_const _)).mul
          ((h1.sub_const V).pow 3)) ?_)
      · exact mul_ne_zero (mul_ne_zero (pow_ne_zero 2 huV) (pow_ne_zero 2 ha)) (pow_ne_zero 2 hb)
      · exact mul_ne_zero (mul_ne_zero (pow_ne_zero 3 hb) huV) (pow_ne_zero 3 ha)
    have h := p71_dzbar_partial hH
    simp only at h
    rw [h]
    have hd : HasDerivAt (fun b => (y - b) ^ 2 / ((u - V) ^ 2 * (y - V) ^ 2 * (u - b) ^ 2) +
        (y - b) ^ 3 / ((u - b) ^ 3 * (u - V) * (y - V) ^ 3)) (D1 y (conj y)) (conj y) := by
      have hl : HasDerivAt (fun b : ℂ => y - b) (-1) (conj y) := by
        simpa using (hasDerivAt_id (conj y)).const_sub y
      have hr : HasDerivAt (fun b : ℂ => u - b) (-1) (conj y) := by
        simpa using (hasDerivAt_id (conj y)).const_sub u
      have k1 := (hl.pow 2).div ((hr.pow 2).const_mul ((u - V) ^ 2 * (y - V) ^ 2))
        (mul_ne_zero (mul_ne_zero (pow_ne_zero 2 huV) (pow_ne_zero 2 ha)) (pow_ne_zero 2 hb))
      have k2 := (hl.pow 3).div ((hr.pow 3).mul_const ((u - V) * (y - V) ^ 3))
        (mul_ne_zero (pow_ne_zero 3 hb) (mul_ne_zero huV (pow_ne_zero 3 ha)))
      have k := k1.add k2
      convert k using 1
      · funext b
        simp only [Pi.add_apply, Pi.div_apply, Pi.mul_apply, Pi.pow_apply]
        ring
      · simp only [hD1, Pi.pow_apply]
        field_simp
        ring
    exact hd.deriv
  -- `ρ_𝕌⁻¹ = -(y - ȳ)²/4`
  have hrho : ∀ y : ℂ, 0 < y.im → (rhoU y : ℂ)⁻¹ = -(y - conj y) ^ 2 / 4 := by
    intro y hy
    have hy0 : y - conj y ≠ 0 := by
      intro h; have := congrArg Complex.im h
      rw [Complex.sub_im, Complex.conj_im, Complex.zero_im] at this; linarith
    rw [rhoU_complex]
    field_simp
  have hU : IsOpen upperHalf := isOpen_lt continuous_const Complex.continuous_im
  have hev : (fun y => (rhoU y : ℂ)⁻¹ * dzbar (fun y' => (y' - conj y') ^ 2 / ((u - V) ^ 2 * (y' - V) ^ 2 *
      (u - conj y') ^ 2) + (y' - conj y') ^ 3 / ((u - conj y') ^ 3 * (u - V) * (y' - V) ^ 3)) y) =ᶠ[𝓝 z]
      fun y => (fun q : ℂ × ℂ => -(q.1 - q.2) ^ 2 / 4 * D1 q.1 q.2) (y, conj y) := by
    filter_upwards [hU.mem_nhds hz] with y hy
    rw [hrho y hy, hB1 y hy]
  have hstep : dzbar (fun y => (rhoU y : ℂ)⁻¹ * dzbar (fun y' => (y' - conj y') ^ 2 / ((u - V) ^ 2 *
      (y' - V) ^ 2 * (u - conj y') ^ 2) + (y' - conj y') ^ 3 / ((u - conj y') ^ 3 * (u - V) * (y' - V) ^ 3)) y) z =
      dzbar (fun y => (fun q : ℂ × ℂ => -(q.1 - q.2) ^ 2 / 4 * D1 q.1 q.2) (y, conj y)) z :=
    p71_dzbar_congr hev
  rw [hstep]
  have ha := hne1 z hzim
  have hb := hne2 (conj z) (hcim z hzim)
  have hH : DifferentiableAt ℂ (fun q : ℂ × ℂ => -(q.1 - q.2) ^ 2 / 4 * D1 q.1 q.2) (z, conj z) := by
    have h1 : DifferentiableAt ℂ (fun q : ℂ × ℂ => q.1) (z, conj z) := differentiableAt_fst
    have h2 : DifferentiableAt ℂ (fun q : ℂ × ℂ => q.2) (z, conj z) := differentiableAt_snd
    simp only [hD1]
    refine (p71_dA_div ((h1.sub h2).pow 2).neg (differentiableAt_const (4 : ℂ)) (by norm_num)).mul ((p71_dA_div (((differentiableAt_const (2 : ℂ)).mul
      (h1.sub h2)).mul (h1.sub_const u)) (((differentiableAt_const _).mul ((h1.sub_const V).pow 2)).mul
        (((differentiableAt_const u).sub h2).pow 3)) ?_).add (p71_dA_div (((differentiableAt_const (3 : ℂ)).mul
          ((h1.sub h2).pow 2)).mul (h1.sub_const u)) (((differentiableAt_const _).mul
            ((h1.sub_const V).pow 3)).mul (((differentiableAt_const u).sub h2).pow 4)) ?_))
    · exact mul_ne_zero (mul_ne_zero (pow_ne_zero 2 huV) (pow_ne_zero 2 ha)) (pow_ne_zero 3 hb)
    · exact mul_ne_zero (mul_ne_zero huV (pow_ne_zero 3 ha)) (pow_ne_zero 4 hb)
  rw [p71_dzbar_partial hH]
  simp only [hD1]
  have hl : HasDerivAt (fun b : ℂ => z - b) (-1) (conj z) := by
    simpa using (hasDerivAt_id (conj z)).const_sub z
  have hr : HasDerivAt (fun b : ℂ => u - b) (-1) (conj z) := by
    simpa using (hasDerivAt_id (conj z)).const_sub u
  have k1 := ((hl.pow 2).neg.div_const 4)
  have k2 := ((hl.const_mul (2 : ℂ)).mul_const (z - u)).div ((hr.pow 3).const_mul ((u - V) ^ 2 * (z - V) ^ 2))
    (mul_ne_zero (mul_ne_zero (pow_ne_zero 2 huV) (pow_ne_zero 2 ha)) (pow_ne_zero 3 hb))
  have k3 := (((hl.pow 2).const_mul (3 : ℂ)).mul_const (z - u)).div ((hr.pow 4).const_mul ((u - V) * (z - V) ^ 3))
    (mul_ne_zero (mul_ne_zero huV (pow_ne_zero 3 ha)) (pow_ne_zero 4 hb))
  have k := k1.mul (k2.add k3)
  have e : (fun b => -(z - b) ^ 2 / 4 * (2 * (z - b) * (z - u) / ((u - V) ^ 2 * (z - V) ^ 2 * (u - b) ^ 3) +
      3 * (z - b) ^ 2 * (z - u) / ((u - V) * (z - V) ^ 3 * (u - b) ^ 4))) =
      fun b => -(z - b) ^ 2 / 4 * (2 * (z - b) * (z - u) / ((u - V) ^ 2 * (z - V) ^ 2 * (u - b) ^ 3) +
      3 * (z - b) ^ 2 * (z - u) / ((u - V) * (z - V) ^ 3 * (u - b) ^ 4)) := rfl
  have kd : HasDerivAt (fun b => -(z - b) ^ 2 / 4 * (2 * (z - b) * (z - u) / ((u - V) ^ 2 * (z - V) ^ 2 *
      (u - b) ^ 3) + 3 * (z - b) ^ 2 * (z - u) / ((u - V) * (z - V) ^ 3 * (u - b) ^ 4))) _ (conj z) :=
    k.congr_of_eventuallyEq (Eventually.of_forall fun b => by
      simp only [Pi.add_apply, Pi.mul_apply, Pi.div_apply, Pi.pow_apply, Pi.neg_apply] <;> ring)
  rw [kd.deriv]
  simp only [Pi.add_apply, Pi.mul_apply, Pi.div_apply, Pi.pow_apply, Pi.neg_apply, Nat.reduceSub, pow_one,
    Nat.cast_ofNat]
  have hzv : z - conj v ≠ 0 := ha
  have hvz : conj v - z ≠ 0 := fun h => ha (by rw [← neg_sub, h, neg_zero])
  have hzz : z - conj z ≠ 0 := by
    intro h; have := congrArg Complex.im h
    rw [Complex.sub_im, Complex.conj_im, Complex.zero_im] at this; linarith
  rw [hVd] at huV ⊢
  field_simp
  ring

/-- Cauchy estimate for the derivative at a point at distance `< 3ρ/4` from the centre of a disc of holomorphy. -/
theorem p71_deriv_bound {h : ℂ → ℂ} {c a : ℂ} {ρ M : ℝ} (hρ : 0 < ρ) (hd : DifferentiableOn ℂ h (ball c ρ))
    (hM : ∀ x ∈ ball c ρ, ‖h x‖ ≤ M) (ha : dist a c < 3 * ρ / 4) : ‖deriv h a‖ ≤ 4 * M / ρ := by
  have hsub : closedBall a (ρ / 4) ⊆ ball c ρ := fun x hx => by
    rw [mem_closedBall] at hx
    rw [mem_ball]
    linarith [dist_triangle x a c]
  have hdc : DiffContOnCl ℂ h (ball a (ρ / 4)) := by
    apply DifferentiableOn.diffContOnCl
    rw [closure_ball a (by positivity)]
    exact hd.mono hsub
  have hle := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (by positivity) hdc
    (fun x hx => hM x (hsub (sphere_subset_closedBall hx)))
  calc ‖deriv h a‖ ≤ M / (ρ / 4) := hle
    _ = 4 * M / ρ := by field_simp

/-- A complex derivative of a family of strongly measurable functions is a.e. strongly measurable in the parameter
(limit of difference quotients). -/
theorem p71_deriv_meas {α : Type*} [MeasurableSpace α] {m : Measure α} {h : α → ℂ → ℂ} {c : ℂ} {ρ : ℝ}
    (hρ : 0 < ρ) (hmeas : ∀ t ∈ ball c ρ, StronglyMeasurable fun p => h p t)
    (hd : ∀ p, DifferentiableAt ℂ (h p) c) : AEStronglyMeasurable (fun p => deriv (h p) c) m := by
  obtain ⟨t, htd⟩ : ∃ t : ℕ → ℂ, t = fun n : ℕ => (((ρ / 2) / ((n : ℝ) + 1) : ℝ) : ℂ) := ⟨_, rfl⟩
  have hn1 : ∀ n : ℕ, (0 : ℝ) < (n : ℝ) + 1 := fun n => by positivity
  have htn : ∀ n, ‖t n‖ < ρ := fun n => by
    rw [htd]
    simp only [Complex.norm_real, Real.norm_eq_abs]
    rw [abs_of_pos (by have := hn1 n; positivity), div_lt_iff₀ (hn1 n)]
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    nlinarith
  have ht0 : Tendsto t atTop (𝓝[≠] 0) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, Eventually.of_forall fun n => ?_⟩
    · rw [htd]
      have h1 : Tendsto (fun n : ℕ => (ρ / 2) / ((n : ℝ) + 1)) atTop (𝓝 0) := by
        have := (tendsto_one_div_add_atTop_nhds_zero_nat).const_mul (ρ / 2)
        simpa [div_eq_mul_inv] using this
      have := (Complex.continuous_ofReal.tendsto 0).comp h1
      rw [Complex.ofReal_zero] at this
      exact this
    · rw [htd]
      show (((ρ / 2) / ((n : ℝ) + 1) : ℝ) : ℂ) ≠ 0
      exact Complex.ofReal_ne_zero.mpr (by have := hn1 n; positivity)
  refine aestronglyMeasurable_of_tendsto_ae atTop (f := fun n p => (t n)⁻¹ • (h p (c + t n) - h p c))
    (fun n => ?_) (Eventually.of_forall fun p => ((hd p).hasDerivAt.tendsto_slope_zero).comp ht0)
  have h1 : c + t n ∈ ball c ρ := by rw [mem_ball, dist_eq_norm, add_sub_cancel_left]; exact htn n
  have hsm := ((hmeas _ h1).sub (hmeas c (mem_ball_self hρ))).const_smul (t n)⁻¹
  exact hsm.aestronglyMeasurable

/-- **(U2a)** `[W5]` Differentiation under `∫ dm` of `y ↦ F(y, ȳ)(p)` for kernels jointly holomorphic on a polydisc and
dominated there by an integrable function. -/
theorem p71_torus_under {α : Type*} [MeasurableSpace α] {m : Measure α} [SFinite m]
    {F : ℂ × ℂ → α → ℂ} {z w : ℂ} {R : ℝ} (hR : 0 < R)
    (hhol : ∀ p, DifferentiableOn ℂ (fun q : ℂ × ℂ => F q p) (ball z R ×ˢ ball w R))
    (hmeas : ∀ q ∈ ball z R ×ˢ ball w R, StronglyMeasurable (F q))
    {g : α → ℝ} (hg : Integrable g m) (hb : ∀ q ∈ ball z R ×ˢ ball w R, ∀ p, ‖F q p‖ ≤ g p)
    {y : ℂ} (hy : (y, conj y) ∈ ball z (R / 2) ×ˢ ball w (R / 2)) :
    DifferentiableAt ℝ (fun y => ∫ p, F (y, conj y) p ∂m) y ∧
      dz (fun y => ∫ p, F (y, conj y) p ∂m) y = ∫ p, dz (fun y => F (y, conj y) p) y ∂m ∧
      dzbar (fun y => ∫ p, F (y, conj y) p ∂m) y = ∫ p, dzbar (fun y => F (y, conj y) p) y ∂m := by
  have hS : IsOpen (ball z R ×ˢ ball w R) := isOpen_ball.prod isOpen_ball
  have hhalf : ball z (R / 2) ×ˢ ball w (R / 2) ⊆ ball z R ×ˢ ball w R :=
    prod_mono (ball_subset_ball (by linarith)) (ball_subset_ball (by linarith))
  obtain ⟨T, hTd⟩ : ∃ T : Set ℂ, T = {y : ℂ | (y, conj y) ∈ ball z (R / 2) ×ˢ ball w (R / 2)} := ⟨_, rfl⟩
  have hT : IsOpen T := by
    rw [hTd]
    exact (isOpen_ball.prod isOpen_ball).preimage (continuous_id.prodMk Complex.continuous_conj)
  have hyT : y ∈ T := by rw [hTd]; exact hy
  have hTS : ∀ y' ∈ T, (y', conj y') ∈ ball z R ×ˢ ball w R := fun y' hy' => hhalf (by rw [hTd] at hy'; exact hy')
  -- the derivative of `y ↦ (y, ȳ)`
  obtain ⟨φ, hφ⟩ : ∃ φ : ℂ →L[ℝ] ℂ × ℂ, φ = (ContinuousLinearMap.id ℝ ℂ).prod Complex.conjCLE.toContinuousLinearMap :=
    ⟨_, rfl⟩
  have hφd : ∀ y' : ℂ, HasFDerivAt (fun y : ℂ => (y, conj y)) φ y' := fun y' => by
    rw [hφ]
    exact (hasFDerivAt_id y').prodMk Complex.conjCLE.toContinuousLinearMap.hasFDerivAt
  obtain ⟨F', hF'⟩ : ∃ F' : ℂ → α → ℂ →L[ℝ] ℂ,
      F' = fun y' p => ((fderiv ℂ (fun q : ℂ × ℂ => F q p) (y', conj y')).restrictScalars ℝ).comp φ := ⟨_, rfl⟩
  have hdiff : ∀ p, ∀ y' ∈ T, HasFDerivAt (fun y => F (y, conj y) p) (F' y' p) y' := by
    intro p y' hy'
    have hF := ((hhol p).differentiableAt (hS.mem_nhds (hTS y' hy'))).hasFDerivAt
    rw [hF']
    exact (hF.restrictScalars ℝ).comp y' (hφd y')
  -- partial derivatives
  have hpart : ∀ p, ∀ q ∈ ball z R ×ˢ ball w R, ∀ v : ℂ × ℂ,
      fderiv ℂ (fun q : ℂ × ℂ => F q p) q v = v.1 * deriv (fun a => F (a, q.2) p) q.1 +
        v.2 * deriv (fun b => F (q.1, b) p) q.2 := by
    intro p q hq v
    have hF : HasFDerivAt (fun q : ℂ × ℂ => F q p) (fderiv ℂ (fun q : ℂ × ℂ => F q p) q) (q.1, q.2) :=
      ((hhol p).differentiableAt (hS.mem_nhds hq)).hasFDerivAt
    have h1 : deriv (fun a => F (a, q.2) p) q.1 = fderiv ℂ (fun q : ℂ × ℂ => F q p) q (1, 0) := by
      calc deriv (fun a => F (a, q.2) p) q.1 =
          ((fderiv ℂ (fun q : ℂ × ℂ => F q p) q).comp (ContinuousLinearMap.inl ℂ ℂ ℂ)) 1 :=
            (HasFDerivAt.comp (g := fun q : ℂ × ℂ => F q p) (f := fun a : ℂ => (a, q.2)) q.1 hF
              (hasFDerivAt_prodMk_left q.1 q.2)).hasDerivAt.deriv
        _ = _ := by simp
    have h2 : deriv (fun b => F (q.1, b) p) q.2 = fderiv ℂ (fun q : ℂ × ℂ => F q p) q (0, 1) := by
      calc deriv (fun b => F (q.1, b) p) q.2 =
          ((fderiv ℂ (fun q : ℂ × ℂ => F q p) q).comp (ContinuousLinearMap.inr ℂ ℂ ℂ)) 1 :=
            (HasFDerivAt.comp (g := fun q : ℂ × ℂ => F q p) (f := fun b : ℂ => (q.1, b)) q.2 hF
              (hasFDerivAt_prodMk_right q.1 q.2)).hasDerivAt.deriv
        _ = _ := by simp
    rw [h1, h2]
    have hv : v = v.1 • ((1 : ℂ), (0 : ℂ)) + v.2 • ((0 : ℂ), (1 : ℂ)) := by
      ext <;> simp
    conv_lhs => rw [hv]
    rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
  have hD1 : ∀ p, ∀ q ∈ ball z (R / 2) ×ˢ ball w (R / 2), ‖deriv (fun a => F (a, q.2) p) q.1‖ ≤ 4 * g p / R := by
    intro p q hq
    refine p71_deriv_bound (h := fun a => F (a, q.2) p) (c := z) hR (fun a ha => ?_)
      (fun a ha => hb (a, q.2) ⟨ha, (hhalf hq).2⟩ p) ?_
    · have hq2 := (hhalf hq).2
      exact ((hhol p).comp (differentiableOn_id.prodMk (differentiableOn_const _))
        (fun a ha => ⟨ha, hq2⟩)) a ha
    · have := hq.1; rw [mem_ball] at this; linarith
  have hD2 : ∀ p, ∀ q ∈ ball z (R / 2) ×ˢ ball w (R / 2), ‖deriv (fun b => F (q.1, b) p) q.2‖ ≤ 4 * g p / R := by
    intro p q hq
    refine p71_deriv_bound (h := fun b => F (q.1, b) p) (c := w) hR (fun b hb' => ?_)
      (fun b hb' => hb (q.1, b) ⟨(hhalf hq).1, hb'⟩ p) ?_
    · have hq1 := (hhalf hq).1
      exact ((hhol p).comp ((differentiableOn_const _).prodMk differentiableOn_id)
        (fun b hb' => ⟨hq1, hb'⟩)) b hb'
    · have := hq.2; rw [mem_ball] at this; linarith
  have hF'v : ∀ p, ∀ y' ∈ T, ∀ v : ℂ, F' y' p v = v * deriv (fun a => F (a, conj y') p) y' +
      conj v * deriv (fun b => F (y', b) p) (conj y') := by
    intro p y' hy' v
    rw [hF']
    show fderiv ℂ (fun q : ℂ × ℂ => F q p) (y', conj y') (φ v) = _
    rw [hpart p _ (hTS y' hy')]
    rw [hφ]
    rfl
  have hbound : ∀ p, ∀ y' ∈ T, ‖F' y' p‖ ≤ 8 * g p / R := by
    intro p y' hy'
    have hq : (y', conj y') ∈ ball z (R / 2) ×ˢ ball w (R / 2) := by rw [hTd] at hy'; exact hy'
    have h1 := hD1 p _ hq
    have h2 := hD2 p _ hq
    have hg0 : 0 ≤ g p := (norm_nonneg _).trans (hb _ (hTS y' hy') p)
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v => ?_
    rw [hF'v p y' hy']
    calc ‖v * deriv (fun a => F (a, conj y') p) y' + conj v * deriv (fun b => F (y', b) p) (conj y')‖
        ≤ ‖v‖ * (4 * g p / R) + ‖v‖ * (4 * g p / R) := by
          refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
          · rw [norm_mul]; exact mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
          · rw [norm_mul, RCLike.norm_conj]; exact mul_le_mul_of_nonneg_left h2 (norm_nonneg _)
      _ = 8 * g p / R * ‖v‖ := by ring
  -- measurability of the derivative in `p`
  have hq0 := hTS y hyT
  have hy0 : (y, conj y) ∈ ball z (R / 2) ×ˢ ball w (R / 2) := hy
  have hball1 : ∀ t ∈ ball y (R / 2), t ∈ ball z R := fun t ht => by
    rw [mem_ball] at ht ⊢
    have := hy0.1; rw [mem_ball] at this
    linarith [dist_triangle t y z]
  have hball2 : ∀ t ∈ ball (conj y) (R / 2), t ∈ ball w R := fun t ht => by
    rw [mem_ball] at ht ⊢
    have := hy0.2; rw [mem_ball] at this
    linarith [dist_triangle t (conj y) w]
  have hm1 : AEStronglyMeasurable (fun p => deriv (fun a => F (a, conj y) p) y) m :=
    p71_deriv_meas (h := fun p a => F (a, conj y) p) (by linarith : (0 : ℝ) < R / 2)
      (fun t ht => hmeas _ ⟨hball1 t ht, hq0.2⟩)
      (fun p => DifferentiableAt.comp (g := fun q : ℂ × ℂ => F q p) (f := fun a : ℂ => (a, conj y)) y
        ((hhol p).differentiableAt (hS.mem_nhds hq0)) (differentiableAt_id.prodMk (differentiableAt_const _)))
  have hm2 : AEStronglyMeasurable (fun p => deriv (fun b => F (y, b) p) (conj y)) m :=
    p71_deriv_meas (h := fun p b => F (y, b) p) (by linarith : (0 : ℝ) < R / 2)
      (fun t ht => hmeas _ ⟨hq0.1, hball2 t ht⟩)
      (fun p => DifferentiableAt.comp (g := fun q : ℂ × ℂ => F q p) (f := fun b : ℂ => (y, b)) (conj y)
        ((hhol p).differentiableAt (hS.mem_nhds hq0)) ((differentiableAt_const _).prodMk differentiableAt_id))
  have hF'eq : F' y = fun p => deriv (fun a => F (a, conj y) p) y • ContinuousLinearMap.id ℝ ℂ +
      deriv (fun b => F (y, b) p) (conj y) • Complex.conjCLE.toContinuousLinearMap := by
    funext p
    ext v
    rw [hF'v p y hyT]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply,
      ContinuousLinearEquiv.coe_coe, Complex.conjCLE_apply, smul_eq_mul]
    ring
  have hF'meas : AEStronglyMeasurable (F' y) m := by
    rw [hF'eq]
    exact (hm1.smul_const _).add (hm2.smul_const _)
  -- differentiation under the integral sign
  have hbi : Integrable (fun p => 8 * g p / R) m := (hg.const_mul 8).div_const R
  have hFint : Integrable (F (y, conj y)) m :=
    hg.mono' (hmeas _ hq0).aestronglyMeasurable (Eventually.of_forall fun p => hb _ hq0 p)
  have hD := hasFDerivAt_integral_of_dominated_of_fderiv_le (𝕜 := ℝ) (μ := m)
    (F := fun y p => F (y, conj y) p) (F' := F') (bound := fun p => 8 * g p / R) (hT.mem_nhds hyT)
    (Eventually.mono (hT.mem_nhds hyT) fun y' hy' => (hmeas _ (hTS y' hy')).aestronglyMeasurable) hFint hF'meas
    (Eventually.of_forall fun p y' hy' => hbound p y' hy') hbi (Eventually.of_forall fun p y' hy' => hdiff p y' hy')
  have hF'i : Integrable (F' y) m :=
    hbi.mono' hF'meas (Eventually.of_forall fun p => hbound p y hyT)
  have hfd : ∀ p, fderiv ℝ (fun y => F (y, conj y) p) y = F' y p := fun p => (hdiff p y hyT).fderiv
  have i1 := hF'i.apply_continuousLinearMap 1
  have iI := hF'i.apply_continuousLinearMap I
  refine ⟨hD.differentiableAt, ?_, ?_⟩
  · show (fderiv ℝ (fun y => ∫ p, F (y, conj y) p ∂m) y 1 - I * fderiv ℝ (fun y => ∫ p, F (y, conj y) p ∂m) y I) / 2 =
      ∫ p, (fderiv ℝ (fun y => F (y, conj y) p) y 1 - I * fderiv ℝ (fun y => F (y, conj y) p) y I) / 2 ∂m
    simp only [hfd]
    rw [hD.fderiv, ContinuousLinearMap.integral_apply hF'i, ContinuousLinearMap.integral_apply hF'i,
      integral_div, integral_sub i1 (iI.const_mul I), integral_const_mul]
  · show (fderiv ℝ (fun y => ∫ p, F (y, conj y) p ∂m) y 1 + I * fderiv ℝ (fun y => ∫ p, F (y, conj y) p ∂m) y I) / 2 =
      ∫ p, (fderiv ℝ (fun y => F (y, conj y) p) y 1 + I * fderiv ℝ (fun y => F (y, conj y) p) y I) / 2 ∂m
    simp only [hfd]
    rw [hD.fderiv, ContinuousLinearMap.integral_apply hF'i, ContinuousLinearMap.integral_apply hF'i,
      integral_div, integral_add i1 (iI.const_mul I), integral_const_mul]

/-! ### U2 helpers (下属1) -/

/-- Uniform separation on the polydisc `B(z, Im z/2) × B(z̄, Im z/2)` from points of `𝕌`. -/
theorem p71_sepq {z a b u v : ℂ} (hz : 0 < z.im) (ha : a ∈ ball z (z.im / 2)) (hb : b ∈ ball (conj z) (z.im / 2))
    (hu : 0 ≤ u.im) (hv : 0 ≤ v.im) :
    z.im / 2 / (1 + (‖z‖ + z.im / 2) + z.im / 2) * (1 + ‖u‖) ≤ ‖u - b‖ ∧
      z.im / 2 / (1 + (‖z‖ + z.im / 2) + z.im / 2) * (1 + ‖v‖) ≤ ‖a - conj v‖ ∧
      ‖a - b‖ ≤ 2 * ‖z‖ + z.im ∧ ‖a‖ ≤ ‖z‖ + z.im := by
  have hs : 0 < z.im / 2 := half_pos hz
  have ha' : ‖a - z‖ < z.im / 2 := by rwa [mem_ball, dist_eq_norm] at ha
  have hb' : ‖b - conj z‖ < z.im / 2 := by rwa [mem_ball, dist_eq_norm] at hb
  have hbim : b.im ≤ -(z.im / 2) := by
    have h1 := Complex.abs_im_le_norm (b - conj z)
    rw [Complex.sub_im, Complex.conj_im] at h1
    have := le_abs_self (b.im - -z.im)
    linarith
  have haim : z.im / 2 ≤ a.im := by
    have h1 := Complex.abs_im_le_norm (a - z)
    rw [Complex.sub_im] at h1
    have := neg_abs_le (a.im - z.im)
    linarith
  have hbR : ‖b‖ ≤ ‖z‖ + z.im / 2 := by
    have := norm_le_insert' b (conj z)
    rw [Complex.norm_conj] at this
    linarith
  have haR : ‖a‖ ≤ ‖z‖ + z.im / 2 := by
    have := norm_le_insert' a z
    linarith
  have hR : 0 ≤ ‖z‖ + z.im / 2 := by positivity
  refine ⟨e64_sep hs hR hu hbim hbR, ?_, ?_, by linarith⟩
  · have h := e64_sep (w := conj a) hs hR hv (by rw [Complex.conj_im]; linarith)
      (by rw [Complex.norm_conj]; exact haR)
    have e : ‖v - conj a‖ = ‖a - conj v‖ := by
      rw [← Complex.norm_conj, map_sub, Complex.conj_conj, norm_sub_rev]
    rwa [e] at h
  · have h1 := norm_sub_le (a - z) (b - z)
    rw [sub_sub_sub_cancel_right] at h1
    have h2 : ‖b - z‖ ≤ ‖b - conj z‖ + ‖z - conj z‖ := by
      have := norm_sub_le (b - conj z) (z - conj z)
      rwa [sub_sub_sub_cancel_right] at this
    have h3 : ‖z - conj z‖ ≤ 2 * ‖z‖ := by
      have := norm_sub_le z (conj z)
      rw [Complex.norm_conj] at this
      linarith
    linarith

/-- `|u - v̄| ≤ (1 + |u|)(1 + |v|)`. -/
theorem p71_d_le (u v : ℂ) : ‖u - conj v‖ ≤ (1 + ‖u‖) * (1 + ‖v‖) := by
  have := norm_sub_le u (conj v)
  rw [Complex.norm_conj] at this
  nlinarith [norm_nonneg u, norm_nonneg v]

/-- The basic estimate `X/(d^k Y)` with `|u - v̄|⁻¹ ≤ (1 + |u|)(1 + |v|)|u - v̄|⁻²`. -/
theorem p71_inv_d {d tu tv : ℝ} (hd : 0 < d) (htu : 1 ≤ tu) (htv : 1 ≤ tv) (hle : d ≤ tu * tv) :
    d⁻¹ ≤ tu * tv * (d ^ 2)⁻¹ := by
  rw [show tu * tv * (d ^ 2)⁻¹ = tu * tv / d / d by field_simp]
  rw [le_div_iff₀ hd, inv_mul_cancel₀ hd.ne', le_div_iff₀ hd, one_mul]
  exact hle

/-- Polydisc bound of the Corollary 6.4 kernel `B̂(a, b)`. -/
theorem p71_Bh_bd {z a b u v : ℂ} (hz : 0 < z.im) (ha : a ∈ ball z (z.im / 2)) (hb : b ∈ ball (conj z) (z.im / 2))
    (hu : 0 < u.im) (hv : 0 < v.im) :
    ‖(a - b) ^ 2 / ((u - conj v) ^ 2 * (a - conj v) ^ 2 * (u - b) ^ 2) +
        (a - b) ^ 3 / ((u - b) ^ 3 * (u - conj v) * (a - conj v) ^ 3)‖ ≤
      ((2 * ‖z‖ + z.im) ^ 2 / (z.im / 2 / (1 + (‖z‖ + z.im / 2) + z.im / 2)) ^ 4 +
          (2 * ‖z‖ + z.im) ^ 3 / (z.im / 2 / (1 + (‖z‖ + z.im / 2) + z.im / 2)) ^ 6) *
        ((‖u - conj v‖ ^ 2)⁻¹ * ((1 + ‖u‖) ^ 2)⁻¹ * ((1 + ‖v‖) ^ 2)⁻¹) := by
  obtain ⟨h1, h2, h3, -⟩ := p71_sepq hz ha hb hu.le hv.le
  set c := z.im / 2 / (1 + (‖z‖ + z.im / 2) + z.im / 2) with hcd
  set K := 2 * ‖z‖ + z.im with hKd
  set tu := 1 + ‖u‖
  set tv := 1 + ‖v‖
  set d := ‖u - conj v‖ with hdd
  have hc : 0 < c := by positivity
  have htu : 1 ≤ tu := by simp only [tu]; linarith [norm_nonneg u]
  have htv : 1 ≤ tv := by simp only [tv]; linarith [norm_nonneg v]
  have hd : 0 < d := by
    rw [hdd, norm_pos_iff]
    intro h
    have := congrArg Complex.im h
    rw [Complex.sub_im, Complex.conj_im, Complex.zero_im] at this
    linarith
  have hdle : d ≤ tu * tv := p71_d_le u v
  have hK : 0 ≤ K := by positivity
  have hA : 0 < c * tu := by positivity
  have hB : 0 < c * tv := by positivity
  have hi := p71_inv_d hd htu htv hdle
  have t1 : ‖(a - b) ^ 2 / ((u - conj v) ^ 2 * (a - conj v) ^ 2 * (u - b) ^ 2)‖ ≤
      K ^ 2 / c ^ 4 * ((d ^ 2)⁻¹ * (tu ^ 2)⁻¹ * (tv ^ 2)⁻¹) := by
    rw [norm_div, norm_pow, norm_mul, norm_mul, norm_pow, norm_pow, norm_pow]
    calc ‖a - b‖ ^ 2 / (d ^ 2 * ‖a - conj v‖ ^ 2 * ‖u - b‖ ^ 2) ≤ K ^ 2 / (d ^ 2 * (c * tv) ^ 2 * (c * tu) ^ 2) := by
          gcongr
      _ = K ^ 2 / c ^ 4 * ((d ^ 2)⁻¹ * (tu ^ 2)⁻¹ * (tv ^ 2)⁻¹) := by field_simp
  have t2 : ‖(a - b) ^ 3 / ((u - b) ^ 3 * (u - conj v) * (a - conj v) ^ 3)‖ ≤
      K ^ 3 / c ^ 6 * ((d ^ 2)⁻¹ * (tu ^ 2)⁻¹ * (tv ^ 2)⁻¹) := by
    rw [norm_div, norm_pow, norm_mul, norm_mul, norm_pow, norm_pow]
    calc ‖a - b‖ ^ 3 / (‖u - b‖ ^ 3 * d * ‖a - conj v‖ ^ 3) ≤ K ^ 3 / ((c * tu) ^ 3 * d * (c * tv) ^ 3) := by
          gcongr
      _ = K ^ 3 / c ^ 6 * (tu ^ 3)⁻¹ * (tv ^ 3)⁻¹ * d⁻¹ := by field_simp
      _ ≤ K ^ 3 / c ^ 6 * (tu ^ 3)⁻¹ * (tv ^ 3)⁻¹ * (tu * tv * (d ^ 2)⁻¹) := by gcongr
      _ = K ^ 3 / c ^ 6 * ((d ^ 2)⁻¹ * (tu ^ 2)⁻¹ * (tv ^ 2)⁻¹) := by
          field_simp
  calc _ ≤ _ := norm_add_le _ _
    _ ≤ _ := add_le_add t1 t2
    _ = _ := by ring

/-- Polydisc bound of `-(a - b)²/4 · ∂_b B̂(a, b)`. -/
theorem p71_Dh_bd {z a b u v : ℂ} (hz : 0 < z.im) (ha : a ∈ ball z (z.im / 2)) (hb : b ∈ ball (conj z) (z.im / 2))
    (hu : 0 < u.im) (hv : 0 < v.im) :
    ‖-(a - b) ^ 2 / 4 * (2 * (a - b) * (a - u) / ((u - conj v) ^ 2 * (a - conj v) ^ 2 * (u - b) ^ 3) +
        3 * (a - b) ^ 2 * (a - u) / ((u - conj v) * (a - conj v) ^ 3 * (u - b) ^ 4))‖ ≤
      (2 * ‖z‖ + z.im) ^ 2 / 4 * (2 * (2 * ‖z‖ + z.im) * (1 + ‖z‖ + z.im) /
          (z.im / 2 / (1 + (‖z‖ + z.im / 2) + z.im / 2)) ^ 5 +
        3 * (2 * ‖z‖ + z.im) ^ 2 * (1 + ‖z‖ + z.im) / (z.im / 2 / (1 + (‖z‖ + z.im / 2) + z.im / 2)) ^ 7) *
        ((‖u - conj v‖ ^ 2)⁻¹ * ((1 + ‖u‖) ^ 2)⁻¹ * ((1 + ‖v‖) ^ 2)⁻¹) := by
  obtain ⟨h1, h2, h3, h4⟩ := p71_sepq hz ha hb hu.le hv.le
  set c := z.im / 2 / (1 + (‖z‖ + z.im / 2) + z.im / 2) with hcd
  set K := 2 * ‖z‖ + z.im with hKd
  set K1 := 1 + ‖z‖ + z.im with hK1d
  set tu := 1 + ‖u‖
  set tv := 1 + ‖v‖
  set d := ‖u - conj v‖ with hdd
  have hc : 0 < c := by positivity
  have htu : 1 ≤ tu := by simp only [tu]; linarith [norm_nonneg u]
  have htv : 1 ≤ tv := by simp only [tv]; linarith [norm_nonneg v]
  have hd : 0 < d := by
    rw [hdd, norm_pos_iff]
    intro h
    have := congrArg Complex.im h
    rw [Complex.sub_im, Complex.conj_im, Complex.zero_im] at this
    linarith
  have hdle : d ≤ tu * tv := p71_d_le u v
  have hK : 0 ≤ K := by positivity
  have hK1 : 0 ≤ K1 := by positivity
  have hau : ‖a - u‖ ≤ K1 * tu := by
    have := norm_sub_le a u
    have : ‖a‖ ≤ K1 := by linarith
    nlinarith [norm_nonneg u, norm_nonneg a]
  have hA : 0 < c * tu := by positivity
  have hB : 0 < c * tv := by positivity
  have hi := p71_inv_d hd htu htv hdle
  have t1 : ‖2 * (a - b) * (a - u) / ((u - conj v) ^ 2 * (a - conj v) ^ 2 * (u - b) ^ 3)‖ ≤
      2 * K * K1 / c ^ 5 * ((d ^ 2)⁻¹ * (tu ^ 2)⁻¹ * (tv ^ 2)⁻¹) := by
    rw [norm_div, norm_mul, norm_mul, norm_mul, norm_mul, norm_pow, norm_pow, norm_pow,
      show ‖(2 : ℂ)‖ = 2 by norm_num]
    calc 2 * ‖a - b‖ * ‖a - u‖ / (d ^ 2 * ‖a - conj v‖ ^ 2 * ‖u - b‖ ^ 3) ≤
          2 * K * (K1 * tu) / (d ^ 2 * (c * tv) ^ 2 * (c * tu) ^ 3) := by gcongr
      _ = 2 * K * K1 / c ^ 5 * ((d ^ 2)⁻¹ * (tu ^ 2)⁻¹ * (tv ^ 2)⁻¹) := by field_simp
  have t2 : ‖3 * (a - b) ^ 2 * (a - u) / ((u - conj v) * (a - conj v) ^ 3 * (u - b) ^ 4)‖ ≤
      3 * K ^ 2 * K1 / c ^ 7 * ((d ^ 2)⁻¹ * (tu ^ 2)⁻¹ * (tv ^ 2)⁻¹) := by
    rw [norm_div, norm_mul, norm_mul, norm_mul, norm_mul, norm_pow, norm_pow, norm_pow,
      show ‖(3 : ℂ)‖ = 3 by norm_num]
    calc 3 * ‖a - b‖ ^ 2 * ‖a - u‖ / (d * ‖a - conj v‖ ^ 3 * ‖u - b‖ ^ 4) ≤
          3 * K ^ 2 * (K1 * tu) / (d * (c * tv) ^ 3 * (c * tu) ^ 4) := by gcongr
      _ = 3 * K ^ 2 * K1 / c ^ 7 * (tu ^ 3)⁻¹ * (tv ^ 3)⁻¹ * d⁻¹ := by field_simp
      _ ≤ 3 * K ^ 2 * K1 / c ^ 7 * (tu ^ 3)⁻¹ * (tv ^ 3)⁻¹ * (tu * tv * (d ^ 2)⁻¹) := by gcongr
      _ = 3 * K ^ 2 * K1 / c ^ 7 * ((d ^ 2)⁻¹ * (tu ^ 2)⁻¹ * (tv ^ 2)⁻¹) := by field_simp
  have hab : ‖-(a - b) ^ 2 / 4‖ ≤ K ^ 2 / 4 := by
    rw [norm_div, norm_neg, norm_pow, show ‖(4 : ℂ)‖ = 4 by norm_num]
    gcongr
  rw [norm_mul]
  calc _ ≤ K ^ 2 / 4 * (2 * K * K1 / c ^ 5 * ((d ^ 2)⁻¹ * (tu ^ 2)⁻¹ * (tv ^ 2)⁻¹) +
        3 * K ^ 2 * K1 / c ^ 7 * ((d ^ 2)⁻¹ * (tu ^ 2)⁻¹ * (tv ^ 2)⁻¹)) :=
        mul_le_mul hab ((norm_add_le _ _).trans (add_le_add t1 t2)) (norm_nonneg _) (by positivity)
    _ = _ := by ring

/-- Bound of the (7.5) kernel `A(z, u, v)`. -/
theorem p71_A_bd {z u v : ℂ} (hz : 0 < z.im) (hu : 0 < u.im) (hv : 0 < v.im) :
    ‖(u - z) ^ 2 / ((u - conj z) ^ 4 * (conj v - z) ^ 2 * (u - conj v) ^ 2) +
        2 * (z - conj z) * (z - u) ^ 2 / ((u - conj z) ^ 5 * (z - conj v) ^ 3 * (u - conj v))‖ ≤
      ((1 + ‖z‖ + z.im) ^ 2 / (z.im / 2 / (1 + (‖z‖ + z.im / 2) + z.im / 2)) ^ 6 +
          2 * (2 * ‖z‖) * (1 + ‖z‖ + z.im) ^ 2 / (z.im / 2 / (1 + (‖z‖ + z.im / 2) + z.im / 2)) ^ 8) *
        ((‖u - conj v‖ ^ 2)⁻¹ * ((1 + ‖u‖) ^ 2)⁻¹ * ((1 + ‖v‖) ^ 2)⁻¹) := by
  have hzb : z ∈ ball z (z.im / 2) := mem_ball_self (half_pos hz)
  have hzb' : conj z ∈ ball (conj z) (z.im / 2) := mem_ball_self (half_pos hz)
  obtain ⟨h1, h2, -, h4⟩ := p71_sepq hz hzb hzb' hu.le hv.le
  set c := z.im / 2 / (1 + (‖z‖ + z.im / 2) + z.im / 2) with hcd
  set K1 := 1 + ‖z‖ + z.im with hK1d
  set tu := 1 + ‖u‖
  set tv := 1 + ‖v‖
  set d := ‖u - conj v‖ with hdd
  have hc : 0 < c := by positivity
  have htu : 1 ≤ tu := by simp only [tu]; linarith [norm_nonneg u]
  have htv : 1 ≤ tv := by simp only [tv]; linarith [norm_nonneg v]
  have hd : 0 < d := by
    rw [hdd, norm_pos_iff]
    intro h
    have := congrArg Complex.im h
    rw [Complex.sub_im, Complex.conj_im, Complex.zero_im] at this
    linarith
  have hdle : d ≤ tu * tv := p71_d_le u v
  have hK1 : 0 ≤ K1 := by positivity
  have huz : ‖u - z‖ ≤ K1 * tu := by
    have := norm_sub_le u z
    nlinarith [norm_nonneg u, norm_nonneg z]
  have hzu : ‖z - u‖ ≤ K1 * tu := by rw [norm_sub_rev]; exact huz
  have hzz : ‖z - conj z‖ ≤ 2 * ‖z‖ := by
    have := norm_sub_le z (conj z)
    rw [Complex.norm_conj] at this
    linarith
  have hvz : c * tv ≤ ‖conj v - z‖ := by rw [norm_sub_rev]; exact h2
  have hA : 0 < c * tu := by positivity
  have hB : 0 < c * tv := by positivity
  have hi := p71_inv_d hd htu htv hdle
  have t1 : ‖(u - z) ^ 2 / ((u - conj z) ^ 4 * (conj v - z) ^ 2 * (u - conj v) ^ 2)‖ ≤
      K1 ^ 2 / c ^ 6 * ((d ^ 2)⁻¹ * (tu ^ 2)⁻¹ * (tv ^ 2)⁻¹) := by
    rw [norm_div, norm_pow, norm_mul, norm_mul, norm_pow, norm_pow, norm_pow]
    calc ‖u - z‖ ^ 2 / (‖u - conj z‖ ^ 4 * ‖conj v - z‖ ^ 2 * d ^ 2) ≤
          (K1 * tu) ^ 2 / ((c * tu) ^ 4 * (c * tv) ^ 2 * d ^ 2) := by gcongr
      _ = K1 ^ 2 / c ^ 6 * ((d ^ 2)⁻¹ * (tu ^ 2)⁻¹ * (tv ^ 2)⁻¹) := by field_simp
  have t2 : ‖2 * (z - conj z) * (z - u) ^ 2 / ((u - conj z) ^ 5 * (z - conj v) ^ 3 * (u - conj v))‖ ≤
      2 * (2 * ‖z‖) * K1 ^ 2 / c ^ 8 * ((d ^ 2)⁻¹ * (tu ^ 2)⁻¹ * (tv ^ 2)⁻¹) := by
    rw [norm_div, norm_mul, norm_mul, norm_mul, norm_mul, norm_pow, norm_pow, norm_pow,
      show ‖(2 : ℂ)‖ = 2 by norm_num]
    calc 2 * ‖z - conj z‖ * ‖z - u‖ ^ 2 / (‖u - conj z‖ ^ 5 * ‖z - conj v‖ ^ 3 * d) ≤
          2 * (2 * ‖z‖) * (K1 * tu) ^ 2 / ((c * tu) ^ 5 * (c * tv) ^ 3 * d) := by gcongr
      _ = 2 * (2 * ‖z‖) * K1 ^ 2 / c ^ 8 * (tu ^ 3)⁻¹ * (tv ^ 3)⁻¹ * d⁻¹ := by field_simp
      _ ≤ 2 * (2 * ‖z‖) * K1 ^ 2 / c ^ 8 * (tu ^ 3)⁻¹ * (tv ^ 3)⁻¹ * (tu * tv * (d ^ 2)⁻¹) := by gcongr
      _ = 2 * (2 * ‖z‖) * K1 ^ 2 / c ^ 8 * ((d ^ 2)⁻¹ * (tu ^ 2)⁻¹ * (tv ^ 2)⁻¹) := by field_simp
  calc _ ≤ _ := norm_add_le _ _
    _ ≤ _ := add_le_add t1 t2
    _ = _ := by ring

/-- The majorant `|u - v̄|⁻² (1 + |u|)⁻² (1 + |v|)⁻²` is integrable on `𝕌 × 𝕌` (`s71_t_im`, `s71_t_conv`,
`s71_t_half`). -/
theorem p71_maj :
    Integrable (fun p : ℂ × ℂ => (‖p.1 - conj p.2‖ ^ 2)⁻¹ * ((1 + ‖p.1‖) ^ 2)⁻¹ * ((1 + ‖p.2‖) ^ 2)⁻¹)
      ((volume.restrict upperHalf).prod (volume.restrict upperHalf)) := by
  have hU := measurableSet_upperHalf_aux
  obtain ⟨C, hC0, hC⟩ := s71_t_conv
  have hcm : Measurable (conj : ℂ → ℂ) := Complex.continuous_conj.measurable
  set g' : ℂ × ℂ → ℝ := fun p => p.2.im ^ (-(1 / 2 : ℝ)) * ((1 + ‖p.2‖) ^ 2)⁻¹ *
    (((1 + ‖p.1‖) ^ 2)⁻¹ * ‖p.1 - conj p.2‖ ^ (-(3 / 2 : ℝ))) with hg'
  have hg'm : AEStronglyMeasurable g' ((volume.restrict upperHalf).prod (volume.restrict upperHalf)) :=
    Measurable.aestronglyMeasurable (by fun_prop)
  have hmaj : Integrable (fun v : ℂ => C * ((1 + ‖v‖) ^ (-(5 / 2 : ℝ)) * v.im ^ (-(1 / 2 : ℝ))))
      (volume.restrict upperHalf) := s71_t_half.const_mul C
  have hg'i : Integrable g' ((volume.restrict upperHalf).prod (volume.restrict upperHalf)) := by
    rw [integrable_prod_iff' hg'm]
    refine ⟨Eventually.of_forall fun v => by
      simp only [hg']
      exact (hC (conj v)).1.restrict.const_mul (v.im ^ (-(1 / 2 : ℝ)) * ((1 + ‖v‖) ^ 2)⁻¹), ?_⟩
    refine hmaj.mono' (MeasureTheory.AEStronglyMeasurable.integral_prod_right' (MeasureTheory.AEStronglyMeasurable.prod_swap (MeasureTheory.AEStronglyMeasurable.norm hg'm))) ?_
    filter_upwards [ae_restrict_mem hU] with v hv
    have hvim : 0 < v.im := hv
    have ht : 0 < 1 + ‖v‖ := by positivity
    have hp : ∀ u, 0 ≤ ((1 + ‖u‖) ^ 2)⁻¹ * ‖u - conj v‖ ^ (-(3 / 2 : ℝ)) := fun u => by positivity
    have e : (fun u => ‖g' (u, v)‖) = fun u => v.im ^ (-(1 / 2 : ℝ)) * ((1 + ‖v‖) ^ 2)⁻¹ *
        (((1 + ‖u‖) ^ 2)⁻¹ * ‖u - conj v‖ ^ (-(3 / 2 : ℝ))) := by
      funext u
      exact Real.norm_of_nonneg (by positivity)
    rw [e, integral_const_mul]
    have hI : ∫ u in upperHalf, ((1 + ‖u‖) ^ 2)⁻¹ * ‖u - conj v‖ ^ (-(3 / 2 : ℝ)) ≤
        C * (1 + ‖v‖) ^ (-(1 / 2 : ℝ)) := by
      refine (setIntegral_le_integral (hC (conj v)).1 (Eventually.of_forall hp)).trans ?_
      have := (hC (conj v)).2
      rwa [Complex.norm_conj] at this
    have hI0 : 0 ≤ ∫ u in upperHalf, ((1 + ‖u‖) ^ 2)⁻¹ * ‖u - conj v‖ ^ (-(3 / 2 : ℝ)) :=
      setIntegral_nonneg hU fun u _ => hp u
    rw [Real.norm_of_nonneg (mul_nonneg (by positivity) hI0)]
    have e2 : v.im ^ (-(1 / 2 : ℝ)) * ((1 + ‖v‖) ^ 2)⁻¹ * (C * (1 + ‖v‖) ^ (-(1 / 2 : ℝ))) =
        C * ((1 + ‖v‖) ^ (-(5 / 2 : ℝ)) * v.im ^ (-(1 / 2 : ℝ))) := by
      rw [show ((1 + ‖v‖) ^ 2)⁻¹ = (1 + ‖v‖) ^ (-((2 : ℕ) : ℝ)) by
        rw [Real.rpow_neg ht.le, Real.rpow_natCast]]
      have : (1 + ‖v‖) ^ (-((2 : ℕ) : ℝ)) * (1 + ‖v‖) ^ (-(1 / 2 : ℝ)) = (1 + ‖v‖) ^ (-(5 / 2 : ℝ)) := by
        rw [← Real.rpow_add ht]; norm_num
      calc _ = C * ((1 + ‖v‖) ^ (-((2 : ℕ) : ℝ)) * (1 + ‖v‖) ^ (-(1 / 2 : ℝ))) * v.im ^ (-(1 / 2 : ℝ)) := by ring
        _ = _ := by rw [this]; ring
    rw [← e2]
    exact mul_le_mul_of_nonneg_left hI (by positivity)
  refine hg'i.mono' (Measurable.aestronglyMeasurable (by fun_prop)) ?_
  rw [Measure.prod_restrict]
  filter_upwards [ae_restrict_mem (hU.prod hU)] with p hp
  have hu : 0 ≤ p.1.im := (show (0 : ℝ) < p.1.im from hp.1).le
  have hv : 0 < p.2.im := hp.2
  have h := s71_t_im hu hv
  rw [Real.norm_of_nonneg (by positivity)]
  show _ ≤ p.2.im ^ (-(1 / 2 : ℝ)) * ((1 + ‖p.2‖) ^ 2)⁻¹ *
    (((1 + ‖p.1‖) ^ 2)⁻¹ * ‖p.1 - conj p.2‖ ^ (-(3 / 2 : ℝ)))
  rw [← one_div]
  calc 1 / ‖p.1 - conj p.2‖ ^ 2 * ((1 + ‖p.1‖) ^ 2)⁻¹ * ((1 + ‖p.2‖) ^ 2)⁻¹ ≤
        p.2.im ^ (-(1 / 2 : ℝ)) * ‖p.1 - conj p.2‖ ^ (-(3 / 2 : ℝ)) * ((1 + ‖p.1‖) ^ 2)⁻¹ *
          ((1 + ‖p.2‖) ^ 2)⁻¹ := by gcongr
    _ = _ := by ring

/-- Joint holomorphy of the kernel `B̂(a, b)` and of `-(a - b)²/4 · ∂_b B̂(a, b)` on the polydisc. -/
theorem p71_hol {z u v : ℂ} (hz : 0 < z.im) (hu : 0 < u.im) (hv : 0 < v.im) {q : ℂ × ℂ}
    (hq : q ∈ ball z (z.im / 2) ×ˢ ball (conj z) (z.im / 2)) :
    DifferentiableAt ℂ (fun q : ℂ × ℂ => (q.1 - q.2) ^ 2 / ((u - conj v) ^ 2 * (q.1 - conj v) ^ 2 * (u - q.2) ^ 2) +
        (q.1 - q.2) ^ 3 / ((u - q.2) ^ 3 * (u - conj v) * (q.1 - conj v) ^ 3)) q ∧
      DifferentiableAt ℂ (fun q : ℂ × ℂ => -(q.1 - q.2) ^ 2 / 4 * (2 * (q.1 - q.2) * (q.1 - u) /
        ((u - conj v) ^ 2 * (q.1 - conj v) ^ 2 * (u - q.2) ^ 3) + 3 * (q.1 - q.2) ^ 2 * (q.1 - u) /
          ((u - conj v) * (q.1 - conj v) ^ 3 * (u - q.2) ^ 4))) q := by
  obtain ⟨h1, h2, -, -⟩ := p71_sepq hz hq.1 hq.2 hu.le hv.le
  have hc : 0 < z.im / 2 / (1 + (‖z‖ + z.im / 2) + z.im / 2) := by positivity
  have hb : u - q.2 ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le (by positivity) h1)
  have ha : q.1 - conj v ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le (by positivity) h2)
  have huV : u - conj v ≠ 0 := by
    intro h; have := congrArg Complex.im h
    rw [Complex.sub_im, Complex.conj_im, Complex.zero_im] at this; linarith
  have d1 : DifferentiableAt ℂ (fun q : ℂ × ℂ => q.1) q := differentiableAt_fst
  have d2 : DifferentiableAt ℂ (fun q : ℂ × ℂ => q.2) q := differentiableAt_snd
  refine ⟨(p71_dA_div ((d1.sub d2).pow 2) (((differentiableAt_const _).mul ((d1.sub_const _).pow 2)).mul
    (((differentiableAt_const u).sub d2).pow 2)) ?_).add (p71_dA_div ((d1.sub d2).pow 3)
      (((((differentiableAt_const u).sub d2).pow 3).mul (differentiableAt_const _)).mul ((d1.sub_const _).pow 3)) ?_),
    (p71_dA_div ((d1.sub d2).pow 2).neg (differentiableAt_const (4 : ℂ)) (by norm_num)).mul
      ((p71_dA_div (((differentiableAt_const (2 : ℂ)).mul (d1.sub d2)).mul (d1.sub_const u))
        (((differentiableAt_const _).mul ((d1.sub_const _).pow 2)).mul (((differentiableAt_const u).sub d2).pow 3))
          ?_).add (p71_dA_div (((differentiableAt_const (3 : ℂ)).mul ((d1.sub d2).pow 2)).mul (d1.sub_const u))
            (((differentiableAt_const _).mul ((d1.sub_const _).pow 3)).mul (((differentiableAt_const u).sub d2).pow 4))
              ?_))⟩
  · exact mul_ne_zero (mul_ne_zero (pow_ne_zero 2 huV) (pow_ne_zero 2 ha)) (pow_ne_zero 2 hb)
  · exact mul_ne_zero (mul_ne_zero (pow_ne_zero 3 hb) huV) (pow_ne_zero 3 ha)
  · exact mul_ne_zero (mul_ne_zero (pow_ne_zero 2 huV) (pow_ne_zero 2 ha)) (pow_ne_zero 3 hb)
  · exact mul_ne_zero (mul_ne_zero huV (pow_ne_zero 3 ha)) (pow_ne_zero 4 hb)

/-- `ρ_𝕌⁻¹ ∂_ȳ B = -(y - ȳ)²/4 · ∂_b B̂(y, ȳ)` on `𝕌` (as in `p71_kernel_dd`). -/
theorem p71_Dh_eq {u v y : ℂ} (hu : u ∈ upperHalf) (hv : v ∈ upperHalf) (hy : y ∈ upperHalf) :
    (rhoU y : ℂ)⁻¹ * dzbar (fun y' => (y' - conj y') ^ 2 / ((u - conj v) ^ 2 * (y' - conj v) ^ 2 *
        (u - conj y') ^ 2) + (y' - conj y') ^ 3 / ((u - conj y') ^ 3 * (u - conj v) * (y' - conj v) ^ 3)) y =
      -(y - conj y) ^ 2 / 4 * (2 * (y - conj y) * (y - u) / ((u - conj v) ^ 2 * (y - conj v) ^ 2 *
        (u - conj y) ^ 3) + 3 * (y - conj y) ^ 2 * (y - u) / ((u - conj v) * (y - conj v) ^ 3 * (u - conj y) ^ 4)) := by
  have hyim : 0 < y.im := hy
  have huim : 0 < u.im := hu
  have hvim : 0 < v.im := hv
  have hzb : y ∈ ball y (y.im / 2) := mem_ball_self (half_pos hyim)
  have hzb' : conj y ∈ ball (conj y) (y.im / 2) := mem_ball_self (half_pos hyim)
  have hH := (p71_hol (u := u) (v := v) hyim huim hvim (q := (y, conj y)) ⟨hzb, hzb'⟩).1
  have hy0 : y - conj y ≠ 0 := by
    intro h; have := congrArg Complex.im h
    rw [Complex.sub_im, Complex.conj_im, Complex.zero_im] at this; linarith
  have huV : u - conj v ≠ 0 := by
    intro h; have := congrArg Complex.im h
    rw [Complex.sub_im, Complex.conj_im, Complex.zero_im] at this; linarith
  have ha : y - conj v ≠ 0 := by
    intro h; have := congrArg Complex.im h
    rw [Complex.sub_im, Complex.conj_im, Complex.zero_im] at this; linarith
  have hb : u - conj y ≠ 0 := by
    intro h; have := congrArg Complex.im h
    rw [Complex.sub_im, Complex.conj_im, Complex.zero_im] at this; linarith
  have h := p71_dzbar_partial hH
  simp only at h
  rw [h, rhoU_complex]
  have hl : HasDerivAt (fun b : ℂ => y - b) (-1) (conj y) := by
    simpa using (hasDerivAt_id (conj y)).const_sub y
  have hr : HasDerivAt (fun b : ℂ => u - b) (-1) (conj y) := by
    simpa using (hasDerivAt_id (conj y)).const_sub u
  have k1 := (hl.pow 2).div ((hr.pow 2).const_mul ((u - conj v) ^ 2 * (y - conj v) ^ 2))
    (mul_ne_zero (mul_ne_zero (pow_ne_zero 2 huV) (pow_ne_zero 2 ha)) (pow_ne_zero 2 hb))
  have k2 := (hl.pow 3).div ((hr.pow 3).mul_const ((u - conj v) * (y - conj v) ^ 3))
    (mul_ne_zero (pow_ne_zero 3 hb) (mul_ne_zero huV (pow_ne_zero 3 ha)))
  have kd : HasDerivAt (fun b => (y - b) ^ 2 / ((u - conj v) ^ 2 * (y - conj v) ^ 2 * (u - b) ^ 2) +
      (y - b) ^ 3 / ((u - b) ^ 3 * (u - conj v) * (y - conj v) ^ 3)) _ (conj y) :=
    (k1.add k2).congr_of_eventuallyEq (Eventually.of_forall fun b => by
      simp only [Pi.add_apply, Pi.div_apply, Pi.mul_apply, Pi.pow_apply] <;> ring)
  rw [kd.deriv]
  simp only [Pi.add_apply, Pi.mul_apply, Pi.div_apply, Pi.pow_apply, Pi.neg_apply, Nat.reduceSub, pow_one,
    Nat.cast_ofNat]
  field_simp
  ring

/-- **(U2)** `[W1]` **Differentiation of `G(μν̄)` under the double integral.** Near `z ∈ 𝕌`, `G(μν̄) = (2/π²) ∬∬ μ ν̄ B`
(`cor_6_4`); `∂_ȳ` passes twice under `∬∬` (dominated: the `ȳ`-derivatives of `B` are rational with no singularity
for `y` near `z`, and the `u`, `v` majorants are those of `s71_t_*`, `s71_r75_*`). -/
theorem p71_diff_under {μ ν φ ψ : ℂ → ℂ} (hμ : IsHarmonicU μ φ) (hν : IsHarmonicU ν ψ) {z : ℂ} (hz : z ∈ upperHalf) :
    dzbar (fun y => (rhoU y : ℂ)⁻¹ * dzbar (resolventOpU fun u => μ u * conj (ν u)) y) z =
      2 / π ^ 2 * ∫ v in upperHalf, ∫ u in upperHalf, μ u * conj (ν v) *
        dzbar (fun y => (rhoU y : ℂ)⁻¹ * dzbar (fun y' => (y' - conj y') ^ 2 / ((u - conj v) ^ 2 *
          (y' - conj v) ^ 2 * (u - conj y') ^ 2) + (y' - conj y') ^ 3 / ((u - conj y') ^ 3 * (u - conj v) *
            (y' - conj v) ^ 3)) y) z := by
  obtain ⟨Mμ, hMμ0, hMμ⟩ := harmonicU_bounded hμ
  obtain ⟨Mν, hMν0, hMν⟩ := harmonicU_bounded hν
  have hU := measurableSet_upperHalf_aux
  have hUo : IsOpen upperHalf := isOpen_lt continuous_const Complex.continuous_im
  have hzim : 0 < z.im := hz
  have hcm : Measurable (conj : ℂ → ℂ) := Complex.continuous_conj.measurable
  have hR : 0 < z.im / 2 := half_pos hzim
  have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 Real.pi_ne_zero
  set m : Measure (ℂ × ℂ) := (volume.restrict upperHalf).prod (volume.restrict upperHalf) with hmd
  set S : Set (ℂ × ℂ) := upperHalf ×ˢ upperHalf with hSd
  have hSm : MeasurableSet S := hU.prod hU
  -- the coefficient `μ(u) ν̄(v)` on `𝕌 × 𝕌`
  set ind : ℂ × ℂ → ℂ := S.indicator fun p => μ p.1 * conj (ν p.2) with hind
  have hindm : StronglyMeasurable ind := by
    have hc : ContinuousOn (fun p : ℂ × ℂ => μ p.1 * conj (ν p.2)) S :=
      ((harmonicU_continuousOn hμ).comp continuousOn_fst (fun p hp => hp.1)).mul
        (Complex.continuous_conj.comp_continuousOn
          ((harmonicU_continuousOn hν).comp continuousOn_snd (fun p hp => hp.2)))
    have h := hc.measurable_piecewise (continuousOn_const (c := (0 : ℂ))) hSm
    have e : ind = S.piecewise (fun p : ℂ × ℂ => μ p.1 * conj (ν p.2)) (fun _ => 0) := by
      rw [hind]; exact Set.piecewise_eq_indicator.symm
    rw [e]; exact h.stronglyMeasurable
  have hindb : ∀ p, ‖ind p‖ ≤ Mμ * Mν := fun p => by
    by_cases hp : p ∈ S
    · rw [hind, indicator_of_mem hp, norm_mul, Complex.norm_conj]
      exact mul_le_mul (hMμ _ hp.1) (hMν _ hp.2) (norm_nonneg _) hMμ0
    · rw [hind, indicator_of_notMem hp, norm_zero]; positivity
  -- the kernels
  set Bq : ℂ × ℂ → ℂ × ℂ → ℂ := fun q p => (q.1 - q.2) ^ 2 / ((p.1 - conj p.2) ^ 2 * (q.1 - conj p.2) ^ 2 *
    (p.1 - q.2) ^ 2) + (q.1 - q.2) ^ 3 / ((p.1 - q.2) ^ 3 * (p.1 - conj p.2) * (q.1 - conj p.2) ^ 3) with hBq
  set Dq : ℂ × ℂ → ℂ × ℂ → ℂ := fun q p => -(q.1 - q.2) ^ 2 / 4 * (2 * (q.1 - q.2) * (q.1 - p.1) /
    ((p.1 - conj p.2) ^ 2 * (q.1 - conj p.2) ^ 2 * (p.1 - q.2) ^ 3) + 3 * (q.1 - q.2) ^ 2 * (q.1 - p.1) /
      ((p.1 - conj p.2) * (q.1 - conj p.2) ^ 3 * (p.1 - q.2) ^ 4)) with hDq
  set P : Set (ℂ × ℂ) := ball z (z.im / 2) ×ˢ ball (conj z) (z.im / 2) with hPd
  set maj : ℂ × ℂ → ℝ := fun p => (‖p.1 - conj p.2‖ ^ 2)⁻¹ * ((1 + ‖p.1‖) ^ 2)⁻¹ * ((1 + ‖p.2‖) ^ 2)⁻¹
    with hmaj
  have hmaj0 : ∀ p, 0 ≤ maj p := fun p => by simp only [hmaj]; positivity
  have hmajI : Integrable maj m := p71_maj
  set KB := (2 * ‖z‖ + z.im) ^ 2 / (z.im / 2 / (1 + (‖z‖ + z.im / 2) + z.im / 2)) ^ 4 +
    (2 * ‖z‖ + z.im) ^ 3 / (z.im / 2 / (1 + (‖z‖ + z.im / 2) + z.im / 2)) ^ 6 with hKB
  set KD := (2 * ‖z‖ + z.im) ^ 2 / 4 * (2 * (2 * ‖z‖ + z.im) * (1 + ‖z‖ + z.im) /
      (z.im / 2 / (1 + (‖z‖ + z.im / 2) + z.im / 2)) ^ 5 +
    3 * (2 * ‖z‖ + z.im) ^ 2 * (1 + ‖z‖ + z.im) / (z.im / 2 / (1 + (‖z‖ + z.im / 2) + z.im / 2)) ^ 7) with hKD
  have hKB0 : 0 ≤ KB := by positivity
  have hKD0 : 0 ≤ KD := by positivity
  -- holomorphy, measurability and domination of `F = ind · B̂` and `F₂ = ind · D̂`
  have hholB : ∀ p, DifferentiableOn ℂ (fun q => ind p * Bq q p) P := by
    intro p
    by_cases hp : p ∈ S
    · intro q hq
      exact ((differentiableAt_const _).mul (p71_hol hzim hp.1 hp.2 hq).1).differentiableWithinAt
    · have e : (fun q => ind p * Bq q p) = fun _ => 0 := by
        funext q; rw [hind, indicator_of_notMem hp, zero_mul]
      rw [e]; exact differentiableOn_const 0
  have hholD : ∀ p, DifferentiableOn ℂ (fun q => ind p * Dq q p) P := by
    intro p
    by_cases hp : p ∈ S
    · intro q hq
      exact ((differentiableAt_const _).mul (p71_hol hzim hp.1 hp.2 hq).2).differentiableWithinAt
    · have e : (fun q => ind p * Dq q p) = fun _ => 0 := by
        funext q; rw [hind, indicator_of_notMem hp, zero_mul]
      rw [e]; exact differentiableOn_const 0
  have hmB : ∀ q ∈ P, StronglyMeasurable fun p => ind p * Bq q p := fun q _ =>
    hindm.mul (Measurable.stronglyMeasurable (by simp only [hBq]; fun_prop))
  have hmD : ∀ q ∈ P, StronglyMeasurable fun p => ind p * Dq q p := fun q _ =>
    hindm.mul (Measurable.stronglyMeasurable (by simp only [hDq]; fun_prop))
  have hbB : ∀ q ∈ P, ∀ p, ‖ind p * Bq q p‖ ≤ Mμ * Mν * KB * maj p := by
    intro q hq p
    by_cases hp : p ∈ S
    · rw [norm_mul, mul_assoc (Mμ * Mν)]
      exact mul_le_mul (hindb p) (p71_Bh_bd hzim hq.1 hq.2 hp.1 hp.2) (norm_nonneg _) (by positivity)
    · rw [hind, indicator_of_notMem hp, zero_mul, norm_zero]
      exact mul_nonneg (by positivity) (hmaj0 p)
  have hbD : ∀ q ∈ P, ∀ p, ‖ind p * Dq q p‖ ≤ Mμ * Mν * KD * maj p := by
    intro q hq p
    by_cases hp : p ∈ S
    · rw [norm_mul, mul_assoc (Mμ * Mν)]
      exact mul_le_mul (hindb p) (p71_Dh_bd hzim hq.1 hq.2 hp.1 hp.2) (norm_nonneg _) (by positivity)
    · rw [hind, indicator_of_notMem hp, zero_mul, norm_zero]
      exact mul_nonneg (by positivity) (hmaj0 p)
  have hgB : Integrable (fun p => Mμ * Mν * KB * maj p) m := hmajI.const_mul _
  have hgD : Integrable (fun p => Mμ * Mν * KD * maj p) m := hmajI.const_mul _
  -- the small disc `B(z, Im z/4)`
  have hP : ∀ y ∈ ball z (z.im / 4), (y, conj y) ∈ ball z (z.im / 2 / 2) ×ˢ ball (conj z) (z.im / 2 / 2) := by
    intro y hy
    have h4 : z.im / 2 / 2 = z.im / 4 := by ring
    refine ⟨by rw [h4]; exact hy, ?_⟩
    rw [h4, mem_ball, dist_eq_norm, ← map_sub, Complex.norm_conj, ← dist_eq_norm]
    exact hy
  have hPP : ∀ y ∈ ball z (z.im / 4), (y, conj y) ∈ P := fun y hy =>
    ⟨ball_subset_ball (by linarith) (hP y hy).1, ball_subset_ball (by linarith) (hP y hy).2⟩
  have hB4 : ball z (z.im / 4) ⊆ upperHalf := fun y hy => by
    show 0 < y.im
    have h1 := Complex.abs_im_le_norm (y - z)
    rw [Complex.sub_im] at h1
    rw [mem_ball, dist_eq_norm] at hy
    have := neg_abs_le (y.im - z.im)
    linarith
  -- (5) `G(μν̄)(y) = (2/π²) ∫ F(y, ȳ) dm` near `z`
  have hG : ∀ y ∈ ball z (z.im / 4), resolventOpU (fun u => μ u * conj (ν u)) y =
      2 / π ^ 2 * ∫ p, ind p * Bq (y, conj y) p ∂m := by
    intro y hy
    have hyU := hB4 hy
    have hint : Integrable (fun p => ind p * Bq (y, conj y) p) m :=
      hgB.mono' (hmB _ (hPP y hy)).aestronglyMeasurable (Eventually.of_forall (hbB _ (hPP y hy)))
    rw [cor_6_4 hμ hν hyU, hmd, integral_prod_symm _ hint]
    congr 1
    refine setIntegral_congr_fun hU (fun v hv => ?_)
    refine setIntegral_congr_fun hU (fun u hu => ?_)
    show _ = ind (u, v) * Bq (y, conj y) (u, v)
    rw [hind, indicator_of_mem (show (u, v) ∈ S from ⟨hu, hv⟩)]
  -- (6) first derivative
  have hd1 : ∀ y ∈ ball z (z.im / 4), DifferentiableAt ℝ (resolventOpU fun u => μ u * conj (ν u)) y ∧
      dzbar (resolventOpU fun u => μ u * conj (ν u)) y =
        2 / π ^ 2 * ∫ p, dzbar (fun y' => ind p * Bq (y', conj y') p) y ∂m := by
    intro y hy
    obtain ⟨hdi, -, hdb⟩ := p71_torus_under (m := m) (F := fun q p => ind p * Bq q p) hR hholB hmB hgB hbB (hP y hy)
    have hev : (resolventOpU fun u => μ u * conj (ν u)) =ᶠ[𝓝 y]
        fun y' => 2 / π ^ 2 * ∫ p, ind p * Bq (y', conj y') p ∂m := by
      filter_upwards [isOpen_ball.mem_nhds hy] with y' hy' using hG y' hy'
    refine ⟨(hdi.const_mul _).congr_of_eventuallyEq hev, ?_⟩
    rw [p71_dzbar_congr hev, wp_dzbar_const_mul hdi, hdb]
  -- pointwise first derivative of `F`
  have hpt1 : ∀ y ∈ upperHalf, ∀ p, dzbar (fun y' => ind p * Bq (y', conj y') p) y * (rhoU y : ℂ)⁻¹ =
      ind p * Dq (y, conj y) p := by
    intro y hy p
    by_cases hp : p ∈ S
    · have hyim : 0 < y.im := hy
      have hq : (y, conj y) ∈ ball y (y.im / 2) ×ˢ ball (conj y) (y.im / 2) :=
        ⟨mem_ball_self (half_pos hyim), mem_ball_self (half_pos hyim)⟩
      have hh : DifferentiableAt ℂ (fun q => Bq q p) (y, conj y) := (p71_hol hyim hp.1 hp.2 hq).1
      have hBd : DifferentiableAt ℝ (fun y' => Bq (y', conj y') p) y :=
        (hh.restrictScalars ℝ).comp y (differentiableAt_id.prodMk Complex.conjCLE.differentiableAt)
      rw [wp_dzbar_const_mul hBd, mul_assoc, mul_comm _ (rhoU y : ℂ)⁻¹]
      have h := p71_Dh_eq hp.1 hp.2 hy
      simp only [hBq, hDq] at h ⊢
      rw [h]
    · have e : (fun y' => ind p * Bq (y', conj y') p) = fun _ => 0 := by
        funext y'; rw [hind, indicator_of_notMem hp, zero_mul]
      rw [e, (l613_dz_const 0 y).2, zero_mul, hind, indicator_of_notMem hp, zero_mul]
  -- (7) `ρ⁻¹ ∂_ȳ G = (2/π²) ∫ F₂(y, ȳ) dm` near `z`
  have hG2 : ∀ y ∈ ball z (z.im / 4), (rhoU y : ℂ)⁻¹ * dzbar (resolventOpU fun u => μ u * conj (ν u)) y =
      2 / π ^ 2 * ∫ p, ind p * Dq (y, conj y) p ∂m := by
    intro y hy
    rw [(hd1 y hy).2, mul_left_comm, ← integral_const_mul]
    congr 1
    exact integral_congr_ae (Eventually.of_forall fun p => by
      show (rhoU y : ℂ)⁻¹ * _ = ind p * _
      rw [mul_comm]; exact hpt1 y (hB4 hy) p)
  -- (8), (9) second derivative at `z`
  obtain ⟨hdi2, -, hdb2⟩ := p71_torus_under (m := m) (F := fun q p => ind p * Dq q p) hR hholD hmD hgD hbD
    (hP z (mem_ball_self (by linarith)))
  have hev2 : (fun y => (rhoU y : ℂ)⁻¹ * dzbar (resolventOpU fun u => μ u * conj (ν u)) y) =ᶠ[𝓝 z]
      fun y => 2 / π ^ 2 * ∫ p, ind p * Dq (y, conj y) p ∂m := by
    filter_upwards [isOpen_ball.mem_nhds (mem_ball_self (show 0 < z.im / 4 by linarith))] with y hy
    exact hG2 y hy
  rw [p71_dzbar_congr hev2, wp_dzbar_const_mul hdi2, hdb2]
  congr 1
  -- (10) pointwise second derivative
  have hpt2 : ∀ p, dzbar (fun y => ind p * Dq (y, conj y) p) z = ind p *
      dzbar (fun y => (rhoU y : ℂ)⁻¹ * dzbar (fun y' => (y' - conj y') ^ 2 / ((p.1 - conj p.2) ^ 2 *
        (y' - conj p.2) ^ 2 * (p.1 - conj y') ^ 2) + (y' - conj y') ^ 3 / ((p.1 - conj y') ^ 3 *
          (p.1 - conj p.2) * (y' - conj p.2) ^ 3)) y) z := by
    intro p
    by_cases hp : p ∈ S
    · have hq : (z, conj z) ∈ P := hPP z (mem_ball_self (by linarith))
      have hh : DifferentiableAt ℂ (fun q => Dq q p) (z, conj z) := (p71_hol hzim hp.1 hp.2 hq).2
      have hc : DifferentiableAt ℝ (fun y : ℂ => (y, conj y)) z :=
        differentiableAt_id.prodMk Complex.conjCLE.differentiableAt
      have hDd : DifferentiableAt ℝ (fun y => Dq (y, conj y) p) z :=
        DifferentiableAt.comp (g := fun q : ℂ × ℂ => Dq q p) (f := fun y : ℂ => (y, conj y)) z
          (hh.restrictScalars ℝ) hc
      rw [wp_dzbar_const_mul hDd]
      congr 1
      refine p71_dzbar_congr ?_
      filter_upwards [hUo.mem_nhds hz] with y hy
      rw [p71_Dh_eq hp.1 hp.2 hy]
    · have e : (fun y => ind p * Dq (y, conj y) p) = fun _ => 0 := by
        funext y; rw [hind, indicator_of_notMem hp, zero_mul]
      rw [e, (l613_dz_const 0 z).2, hind, indicator_of_notMem hp, zero_mul]
  simp only [hpt2]
  -- (11) back to the iterated integral
  have hHm : AEStronglyMeasurable (fun p => ind p * dzbar (fun y => (rhoU y : ℂ)⁻¹ * dzbar (fun y' =>
      (y' - conj y') ^ 2 / ((p.1 - conj p.2) ^ 2 * (y' - conj p.2) ^ 2 * (p.1 - conj y') ^ 2) +
        (y' - conj y') ^ 3 / ((p.1 - conj y') ^ 3 * (p.1 - conj p.2) * (y' - conj p.2) ^ 3)) y) z) m := by
    have hA : Measurable fun p : ℂ × ℂ => -(3 / 2 : ℂ) * (z - conj z) ^ 2 * ((p.1 - z) ^ 2 / ((p.1 - conj z) ^ 4 *
        (conj p.2 - z) ^ 2 * (p.1 - conj p.2) ^ 2) + 2 * (z - conj z) * (z - p.1) ^ 2 /
          ((p.1 - conj z) ^ 5 * (z - conj p.2) ^ 3 * (p.1 - conj p.2))) := by fun_prop
    refine (hindm.aestronglyMeasurable.mul hA.aestronglyMeasurable).congr ?_
    rw [hmd, Measure.prod_restrict]
    filter_upwards [ae_restrict_mem hSm] with p hp
    show ind p * _ = _
    rw [p71_kernel_dd hp.1 hp.2 hz]
  have hHi : Integrable (fun p => ind p * dzbar (fun y => (rhoU y : ℂ)⁻¹ * dzbar (fun y' =>
      (y' - conj y') ^ 2 / ((p.1 - conj p.2) ^ 2 * (y' - conj p.2) ^ 2 * (p.1 - conj y') ^ 2) +
        (y' - conj y') ^ 3 / ((p.1 - conj y') ^ 3 * (p.1 - conj p.2) * (y' - conj p.2) ^ 3)) y) z) m := by
    refine (hmajI.const_mul (Mμ * Mν * (3 / 2 * ‖z - conj z‖ ^ 2) *
      ((1 + ‖z‖ + z.im) ^ 2 / (z.im / 2 / (1 + (‖z‖ + z.im / 2) + z.im / 2)) ^ 6 +
        2 * (2 * ‖z‖) * (1 + ‖z‖ + z.im) ^ 2 / (z.im / 2 / (1 + (‖z‖ + z.im / 2) + z.im / 2)) ^ 8))).mono' hHm ?_
    rw [hmd, Measure.prod_restrict]
    filter_upwards [ae_restrict_mem hSm] with p hp
    rw [p71_kernel_dd hp.1 hp.2 hz, norm_mul, norm_mul, norm_mul, norm_neg, norm_pow,
      show ‖(3 / 2 : ℂ)‖ = 3 / 2 by norm_num]
    have hA := p71_A_bd hzim (show (0 : ℝ) < p.1.im from hp.1) (show (0 : ℝ) < p.2.im from hp.2)
    calc _ ≤ Mμ * Mν * (3 / 2 * ‖z - conj z‖ ^ 2 * (((1 + ‖z‖ + z.im) ^ 2 /
          (z.im / 2 / (1 + (‖z‖ + z.im / 2) + z.im / 2)) ^ 6 + 2 * (2 * ‖z‖) * (1 + ‖z‖ + z.im) ^ 2 /
            (z.im / 2 / (1 + (‖z‖ + z.im / 2) + z.im / 2)) ^ 8) * maj p)) := by
          refine mul_le_mul (hindb p) (mul_le_mul_of_nonneg_left hA (by positivity)) (by positivity)
            (by positivity)
      _ = _ := by simp only [hmaj]; ring
  rw [hmd, integral_prod_symm _ hHi]
  refine setIntegral_congr_fun hU (fun v hv => ?_)
  refine setIntegral_congr_fun hU (fun u hu => ?_)
  show ind (u, v) * _ = _
  rw [hind, indicator_of_mem (show (u, v) ∈ S from ⟨hu, hv⟩)]

/-- **(U3)** `[W1]` **Proposition 7.1 in the model `𝕌`.** For `μ, ν ∈ Ω^{-1,1}(𝕌)` and `z ∈ 𝕌`:
`ε ↦ Q(μ, εν)(z)` is differentiable at `0`, `∂_ε Q(μ, εν)(z)|₀ = 0` ((7.2) + (7.4)), and
`∂_ε̄ Q(μ, εν)(z)|₀ = -2 ∂_z̄ ρ⁻¹ ∂_z̄ G(μν̄)(z)` ((7.5), U1, U2). -/
theorem p71_prop_7_1U {μ ν φ ψ : ℂ → ℂ} (hμ : IsHarmonicU μ φ) (hν : IsHarmonicU ν ψ) {z : ℂ}
    (hz : z ∈ upperHalf) :
    DifferentiableAt ℝ (fun ε => QfunU μ (fun u => ε * ν u) z) 0 ∧
      dz (fun ε => QfunU μ (fun u => ε * ν u) z) 0 = 0 ∧
      dzbar (fun ε => QfunU μ (fun u => ε * ν u) z) 0 =
        -2 * dzbar (fun y => (rhoU y : ℂ)⁻¹ * dzbar (resolventOpU fun u => μ u * conj (ν u)) y) z := by
  obtain ⟨M, hM0, hνb, -⟩ := s71_harm_setup hν
  have hzim : 0 < z.im := hz
  have hz0 : z - conj z ≠ 0 := by
    intro h
    have := congrArg Complex.im h
    rw [Complex.sub_im, Complex.conj_im, Complex.zero_im] at this
    linarith
  have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 Real.pi_ne_zero
  -- differentiability: `Q = (12/π) J ρ⁻¹` near `0`
  obtain ⟨hJd, -, -⟩ := s71_J_deriv hμ hν hz
  set J : ℂ → ℂ := fun ε => ∫ u in upperHalf, μ u * kernelKbar (fun y => ε * ν y) u z ^ 2 with hJdef
  set R : ℂ → ℂ := fun ε => rhoVar ν ε z with hRdef
  have hRe : R = fun ε => -4 * kernelKbar (fun u => ε * ν u) z z := funext fun ε => eq_6_1 ν ε z
  have hRd : DifferentiableAt ℝ R 0 := by
    rw [hRe]; exact (s71_K_diffAt hν hz hz).const_mul (-4)
  have hR0 : R 0 ≠ 0 := by
    show rhoVar ν 0 z ≠ 0
    rw [s71_rho0]
    exact div_ne_zero (by norm_num) (pow_ne_zero 2 hz0)
  have hev : (fun ε => QfunU μ (fun u => ε * ν u) z) =ᶠ[𝓝 0] fun ε => 12 / π * J ε * (R ε)⁻¹ := by
    have h1 : {ε : ℂ | ‖ε‖ * M < 1} ∈ 𝓝 (0 : ℂ) :=
      (isOpen_lt (continuous_norm.mul continuous_const) continuous_const).mem_nhds (by simp)
    filter_upwards [h1, hRd.continuousAt.eventually_ne hR0] with ε hε hRε
    have h := s71_eq_7_1 hμ hν hM0 hνb hε hz
    show QfunU μ (fun u => ε * ν u) z = 12 / π * J ε * (R ε)⁻¹
    rw [hJdef, hRdef]
    beta_reduce
    have hRε' : rhoVar ν ε z ≠ 0 := hRε
    rw [← h]
    field_simp
  have hd : DifferentiableAt ℝ (fun ε => QfunU μ (fun u => ε * ν u) z) 0 :=
    ((hJd.const_mul (12 / π : ℂ)).mul (hRd.inv hR0)).congr_of_eventuallyEq hev
  refine ⟨hd, ?_, ?_⟩
  · rw [s71_eq_7_2 hμ hν hz, (eq_7_4 hμ hν hz).1.limUnder_eq, mul_zero]
  · rw [s71_eq_7_5 hμ hν hz, p71_diff_under hμ hν hz]
    have hU := measurableSet_upperHalf_aux
    have hin : ∀ v ∈ upperHalf, (∫ u in upperHalf, μ u * conj (ν v) *
        dzbar (fun y => (rhoU y : ℂ)⁻¹ * dzbar (fun y' => (y' - conj y') ^ 2 / ((u - conj v) ^ 2 *
          (y' - conj v) ^ 2 * (u - conj y') ^ 2) + (y' - conj y') ^ 3 / ((u - conj y') ^ 3 * (u - conj v) *
            (y' - conj v) ^ 3)) y) z) = -(3 / 2) * (z - conj z) ^ 2 * ∫ u in upperHalf, μ u * conj (ν v) *
          ((u - z) ^ 2 / ((u - conj z) ^ 4 * (conj v - z) ^ 2 * (u - conj v) ^ 2) +
            2 * (z - conj z) * (z - u) ^ 2 / ((u - conj z) ^ 5 * (z - conj v) ^ 3 * (u - conj v))) := by
      intro v hv
      rw [← integral_const_mul]
      refine setIntegral_congr_fun hU (fun u hu => ?_)
      rw [p71_kernel_dd hu hv hz]
      ring
    rw [setIntegral_congr_fun hU hin, integral_const_mul]
    ring

/-! ### The original statement (byte-identical copy) -/

/-- **Proposition 7.1** (TT:2686–2690). For `μ, ν ∈ Ω^{-1,1}(𝔻*)` and `z ∈ 𝔻*`:
- `∂/∂ε Q(μ, εν)|_{ε=0} = 0`;
- `∂/∂ε̄ Q(μ, εν)|_{ε=0} = -2 ∂_{z̄} ρ⁻¹ ∂_{z̄} G(μν̄)`. -/
theorem p71_prop_7_1 {μ ν : LinfStar} (hμ : μ ∈ harmonicBeltrami) (hν : ν ∈ harmonicBeltrami) {z : ℂ}
    (hz : z ∈ unitDiscExterior) :
    dz (fun ε => Qfun μ (ε • ν) z) 0 = 0 ∧
      Qdot μ ν z = -2 * dzbar (fun y => (rho y : ℂ)⁻¹ * dzbar (resolventStar fun u => μ u * conj (ν u)) y) z := by
  obtain ⟨gμ, hgμs, hgμ⟩ := wr_harm_rep hμ
  obtain ⟨gν, hgνs, hgν⟩ := wr_harm_rep hν
  have hgμc : ContinuousOn gμ unitDiscExterior := hgμs.continuousOn
  have hgνc : ContinuousOn gν unitDiscExterior := hgνs.continuousOn
  obtain ⟨mμ, φ', hm1, hmμ⟩ := p71_wm_harm hμ hgμc hgμ
  obtain ⟨mν, ψ', hm2, hmν⟩ := p71_wm_harm hν hgνc hgν
  have hy := p71_y_mem hz
  obtain ⟨hd, hi, hii⟩ := p71_prop_7_1U hm1 hm2 hy
  have hE := p71_wm_eps (G := fun η => QfunU mμ (fun u => η * mν u) (conj (cayleyInv z)))
    (p71_wm_Q hμ hν hgμc hgμ hgνc hgν hmμ hmν hz) hd
  have h4 := p71_wm_rhs (fun w => μ w * conj (ν w)) hz
  have h4' := p71_wm_prod hgμ hgν hmμ hmν
  refine ⟨?_, ?_⟩
  · rw [hE.1, hi, map_zero, mul_zero]
  · show dzbar (fun ε => Qfun μ (ε • ν) z) 0 = _
    rw [hE.2, hii, h4, ← h4']
    simp only [map_mul, map_neg, map_ofNat]
    ring

/-- **Proposition 7.1** (TT:2686–2690). For `μ, ν ∈ Ω^{-1,1}(𝔻*)` and `z ∈ 𝔻*`:
- `∂/∂ε Q(μ, εν)|_{ε=0} = 0`;
- `∂/∂ε̄ Q(μ, εν)|_{ε=0} = -2 ∂_{z̄} ρ⁻¹ ∂_{z̄} G(μν̄)`. -/
theorem prop_7_1 {μ ν : LinfStar} (hμ : μ ∈ harmonicBeltrami) (hν : ν ∈ harmonicBeltrami) {z : ℂ}
    (hz : z ∈ unitDiscExterior) :
    dz (fun ε => Qfun μ (ε • ν) z) 0 = 0 ∧
      Qdot μ ν z = -2 * dzbar (fun y => (rho y : ℂ)⁻¹ * dzbar (resolventStar fun u => μ u * conj (ν u)) y) z :=
  p71_prop_7_1 hμ hν hz

end TakhtajanTeo
