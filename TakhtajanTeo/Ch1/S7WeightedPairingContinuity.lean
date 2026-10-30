import TakhtajanTeo.Ch1.GroupChain1
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! Continuity and integrability of the actual rho-weighted complex pairing,
and Fatou lower semicontinuity of normL2. All domains are allowed. -/

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal NNReal ComplexConjugate Classical Real
noncomputable section
namespace TakhtajanTeo

private theorem s7pc_rho_nonneg (z : ℂ) : 0 ≤ rho z := by
  unfold rho
  positivity

private theorem s7pc_weight_measurable :
    Measurable (fun z : ℂ => ENNReal.ofReal (rho z)) := by
  unfold rho
  fun_prop

theorem s7pc_normL2_eq (D : Set ℂ) {f : ℂ → ℂ}
    (hf : AEStronglyMeasurable f (volume.restrict D)) :
    normL2 D f = eLpNorm f 2 (rhoMeasure D) := grp_normL2_eq D hf

/-- Finite actual weighted norm gives a genuine L2 function. -/
theorem s7pc_memLp {D : Set ℂ} {f : ℂ → ℂ}
    (hf : AEStronglyMeasurable f (volume.restrict D)) (hn : normL2 D f < ∞) :
    MemLp f 2 (rhoMeasure D) := by
  change eLpNorm f 2 (rhoMeasure D) < ∞
  rwa [← s7pc_normL2_eq D hf]

/-- The weighted measure integral is the actual density-weighted integral. -/
theorem s7pc_integral_rho (D : Set ℂ) (f : ℂ → ℂ) :
    (∫ z, f z ∂rhoMeasure D) = ∫ z in D, f z * rho z := by
  simpa only [rhoMeasure, ENNReal.toReal_ofReal (s7pc_rho_nonneg _), Complex.real_smul, mul_comm] using
    (integral_withDensity_eq_integral_toReal_smul (μ := volume.restrict D)
      s7pc_weight_measurable (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top) f)

theorem s7pc_integrable_rho_iff (D : Set ℂ) (f : ℂ → ℂ) :
    Integrable f (rhoMeasure D) ↔ Integrable (fun z => f z * rho z) (volume.restrict D) := by
  simpa only [rhoMeasure, ENNReal.toReal_ofReal (s7pc_rho_nonneg _), Complex.real_smul, mul_comm] using
    (integrable_withDensity_iff_integrable_smul' (μ := volume.restrict D) (g := f)
      s7pc_weight_measurable (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top))

/-- The order of the L2 arguments matches f * conj(g), not conj(f) * g. -/
theorem s7pc_pairing_eq_inner {D : Set ℂ} {f g : ℂ → ℂ}
    (hf : AEStronglyMeasurable f (volume.restrict D)) (hg : AEStronglyMeasurable g (volume.restrict D))
    (hfn : normL2 D f < ∞) (hgn : normL2 D g < ∞) :
    (∫ z in D, f z * conj (g z) * rho z) =
      inner ℂ ((s7pc_memLp hg hgn).toLp g) ((s7pc_memLp hf hfn).toLp f) := by
  rw [← s7pc_integral_rho D, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [(s7pc_memLp hf hfn).coeFn_toLp, (s7pc_memLp hg hgn).coeFn_toLp] with z hfz hgz
  simp only [RCLike.inner_apply, hfz, hgz]

/-- Actual product integrability follows from L2 membership, without an
integrability hypothesis on the pairing. -/
theorem s7pc_pairing_integrable {D : Set ℂ} {f g : ℂ → ℂ}
    (hf : AEStronglyMeasurable f (volume.restrict D)) (hg : AEStronglyMeasurable g (volume.restrict D))
    (hfn : normL2 D f < ∞) (hgn : normL2 D g < ∞) :
    Integrable (fun z => f z * conj (g z) * rho z) (volume.restrict D) := by
  apply (s7pc_integrable_rho_iff D _).mp
  apply (L2.integrable_inner (𝕜 := ℂ) ((s7pc_memLp hg hgn).toLp g)
    ((s7pc_memLp hf hfn).toLp f)).congr
  filter_upwards [(s7pc_memLp hf hfn).coeFn_toLp, (s7pc_memLp hg hgn).coeFn_toLp] with z hfz hgz
  simp only [RCLike.inner_apply, hfz, hgz]

/-- Cauchy--Schwarz for the original complex integral. -/
theorem s7pc_pairing_bound {D : Set ℂ} {f g : ℂ → ℂ}
    (hf : AEStronglyMeasurable f (volume.restrict D)) (hg : AEStronglyMeasurable g (volume.restrict D))
    (hfn : normL2 D f < ∞) (hgn : normL2 D g < ∞) :
    ‖∫ z in D, f z * conj (g z) * rho z‖ ≤ (normL2 D f).toReal * (normL2 D g).toReal := by
  rw [s7pc_pairing_eq_inner hf hg hfn hgn]
  have hb := norm_inner_le_norm (𝕜 := ℂ) ((s7pc_memLp hg hgn).toLp g)
    ((s7pc_memLp hf hfn).toLp f)
  simpa only [Lp.norm_toLp, ← s7pc_normL2_eq D hf, ← s7pc_normL2_eq D hg, mul_comm] using hb

/-- Actual normL2 convergence is convergence of the associated L2 elements. -/
theorem s7pc_toLp_tendsto {ι : Type*} {l : Filter ι} {D : Set ℂ}
    {f : ι → ℂ → ℂ} {F : ℂ → ℂ}
    (hf : ∀ i, AEStronglyMeasurable (f i) (volume.restrict D))
    (hF : AEStronglyMeasurable F (volume.restrict D))
    (hfn : ∀ i, normL2 D (f i) < ∞) (hFn : normL2 D F < ∞)
    (hc : Tendsto (fun i => normL2 D (fun z => f i z - F z)) l (𝓝 0)) :
    Tendsto (fun i => (s7pc_memLp (hf i) (hfn i)).toLp (f i)) l
      (𝓝 ((s7pc_memLp hF hFn).toLp F)) := by
  rw [tendsto_iff_edist_tendsto_0]
  have he (i : ι) : edist ((s7pc_memLp (hf i) (hfn i)).toLp (f i))
      ((s7pc_memLp hF hFn).toLp F) = normL2 D (fun z => f i z - F z) := by
    rw [Lp.edist_toLp_toLp]
    exact (grp_normL2_eq D ((hf i).sub hF)).symm
  simpa only [he] using hc

/-- Joint continuity of the actual rho-weighted complex pairing under
normL2 convergence. -/
theorem s7pc_pairing_tendsto {ι : Type*} {l : Filter ι} {D : Set ℂ}
    {f g : ι → ℂ → ℂ} {F G : ℂ → ℂ}
    (hf : ∀ i, AEStronglyMeasurable (f i) (volume.restrict D))
    (hg : ∀ i, AEStronglyMeasurable (g i) (volume.restrict D))
    (hF : AEStronglyMeasurable F (volume.restrict D))
    (hG : AEStronglyMeasurable G (volume.restrict D))
    (hfn : ∀ i, normL2 D (f i) < ∞) (hgn : ∀ i, normL2 D (g i) < ∞)
    (hFn : normL2 D F < ∞) (hGn : normL2 D G < ∞)
    (hfc : Tendsto (fun i => normL2 D (fun z => f i z - F z)) l (𝓝 0))
    (hgc : Tendsto (fun i => normL2 D (fun z => g i z - G z)) l (𝓝 0)) :
    Tendsto (fun i => ∫ z in D, f i z * conj (g i z) * rho z) l
      (𝓝 (∫ z in D, F z * conj (G z) * rho z)) := by
  have ht := (s7pc_toLp_tendsto hg hG hgn hGn hgc).inner
    (s7pc_toLp_tendsto hf hF hfn hFn hfc) (𝕜 := ℂ)
  simpa only [s7pc_pairing_eq_inner (hf _) (hg _) (hfn _) (hgn _),
    s7pc_pairing_eq_inner hF hG hFn hGn] using ht

/-- The L1 norm of the actual density-weighted product satisfies the sharp
Cauchy--Schwarz bound, so this controls absolute integrability as well. -/
theorem s7pc_product_L1_bound {D : Set ℂ} {f g : ℂ → ℂ}
    (hf : AEStronglyMeasurable f (volume.restrict D)) (hg : AEStronglyMeasurable g (volume.restrict D))
    (hfn : normL2 D f < ∞) (hgn : normL2 D g < ∞) :
    (∫ z in D, ‖f z * conj (g z) * rho z‖) ≤
      (normL2 D f).toReal * (normL2 D g).toReal := by
  let pf := s7pc_memLp hf hfn
  let pg := s7pc_memLp hg hgn
  have he : (∫ z in D, ‖f z * conj (g z) * rho z‖) =
      ∫ z, ‖f z‖ * ‖g z‖ ∂rhoMeasure D := by
    change _ = ∫ z, ‖f z‖ * ‖g z‖ ∂(volume.restrict D).withDensity
      (fun z => ENNReal.ofReal (rho z))
    rw [integral_withDensity_eq_integral_toReal_smul s7pc_weight_measurable
      (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
    apply integral_congr_ae
    exact Eventually.of_forall fun z => by
      simp only [norm_mul, norm_conj, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (s7pc_rho_nonneg z), ENNReal.toReal_ofReal (s7pc_rho_nonneg z), smul_eq_mul]
      ring
  have hi : (∫ z, ‖f z‖ * ‖g z‖ ∂rhoMeasure D) =
      inner ℝ (pg.norm.toLp (fun z => ‖g z‖)) (pf.norm.toLp (fun z => ‖f z‖)) := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [pf.norm.coeFn_toLp, pg.norm.coeFn_toLp] with z hfz hgz
    simp [RCLike.inner_apply, hfz, hgz]
  rw [he, hi]
  have hb := real_inner_le_norm (pg.norm.toLp (fun z => ‖g z‖)) (pf.norm.toLp (fun z => ‖f z‖))
  simpa only [Lp.norm_toLp, eLpNorm_norm f pf.aestronglyMeasurable,
    eLpNorm_norm g pg.aestronglyMeasurable, ← s7pc_normL2_eq D hf, ← s7pc_normL2_eq D hg,
    mul_comm] using hb

/-- Fatou lower semicontinuity for a.e. pointwise limits of the actual
weighted norm. Neither a uniform bound nor finite energy is assumed. -/
theorem s7pc_normL2_fatou {D : Set ℂ} {f : ℕ → ℂ → ℂ} {F : ℂ → ℂ}
    (hf : ∀ n, AEStronglyMeasurable (f n) (volume.restrict D))
    (hF : AEStronglyMeasurable F (volume.restrict D))
    (hc : ∀ᵐ z ∂(volume.restrict D), Tendsto (fun n => f n z) atTop (𝓝 (F z))) :
    normL2 D F ≤ atTop.liminf (fun n => normL2 D (f n)) := by
  have hac := withDensity_absolutelyContinuous (volume.restrict D)
    (fun z => ENNReal.ofReal (rho z))
  have ht := Lp.eLpNorm_lim_le_liminf_eLpNorm (p := (2 : ℝ≥0∞))
    (fun n => (hf n).mono_ac hac) F (hF.mono_ac hac) (hc.filter_mono hac.ae_le)
  simpa only [← grp_normL2_eq D hF, ← grp_normL2_eq D (hf _)] using ht

/-- A uniform weighted L2 bound passes to the actual a.e. pointwise limit. -/
theorem s7pc_normL2_limit_bound {D : Set ℂ} {f : ℕ → ℂ → ℂ} {F : ℂ → ℂ} {C : ℝ≥0∞}
    (hf : ∀ n, AEStronglyMeasurable (f n) (volume.restrict D))
    (hF : AEStronglyMeasurable F (volume.restrict D))
    (hc : ∀ᵐ z ∂(volume.restrict D), Tendsto (fun n => f n z) atTop (𝓝 (F z)))
    (hb : ∀ n, normL2 D (f n) ≤ C) : normL2 D F ≤ C := by
  exact (s7pc_normL2_fatou hf hF hc).trans
    (liminf_le_of_frequently_le' (Frequently.of_forall hb))

end TakhtajanTeo
