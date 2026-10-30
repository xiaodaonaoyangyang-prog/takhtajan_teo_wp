import TakhtajanTeo.Ch1.PoincareFour

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal Classical Real
noncomputable section
namespace TakhtajanTeo
open LiZhongQC

def mp_complexSquare : Set ℂ := Complex.measurableEquivRealProd.symm '' mp_unitSquare

theorem mp_complexSquare_compact : IsCompact mp_complexSquare :=
  (isCompact_Icc.prod isCompact_Icc).image Complex.equivRealProdCLM.symm.continuous

theorem mp_complexSquare_measurePreserving :
    MeasurePreserving Complex.measurableEquivRealProd.symm mp_squareMeasure
      (volume.restrict mp_complexSquare) := by
  have h := Complex.volume_preserving_equiv_real_prod.symm.restrict_image_emb
    Complex.measurableEquivRealProd.symm.measurableEmbedding mp_unitSquare
  simpa only [mp_squareMeasure, mp_unitMeasure, Measure.prod_restrict,
    ← Measure.volume_eq_prod, mp_unitSquare, mp_complexSquare] using h

theorem mp_complex_square_l4 {f : ℂ → ℂ} (hf : Continuous f) :
    eLpNorm (fun p => f (Complex.equivRealProdCLM.symm p)) 4 mp_squareMeasure =
      eLpNorm f 4 (volume.restrict mp_complexSquare) := by
  exact eLpNorm_comp_measurePreserving hf.aestronglyMeasurable
    mp_complexSquare_measurePreserving

theorem mp_complex_square_memLp {f : ℂ → ℂ} (hf : Continuous f) :
    MemLp f 4 (volume.restrict mp_complexSquare) := by
  haveI : IsFiniteMeasure (volume.restrict mp_complexSquare) :=
    isFiniteMeasure_restrict.mpr mp_complexSquare_compact.measure_ne_top
  obtain ⟨B, hB⟩ := mp_complexSquare_compact.image hf |>.isBounded.exists_norm_le
  apply MemLp.of_bound hf.aestronglyMeasurable B
  filter_upwards [self_mem_ae_restrict mp_complexSquare_compact.measurableSet] with z hz
  exact hB _ (mem_image_of_mem f hz)

/-- The actual area-measure L4 Poincare inequality on the complex unit square. -/
theorem mp_complex_square_poincare_l4 {f : ℂ → ℂ} (hf : ContDiff ℝ 1 f) :
    (eLpNorm (fun z => f z - ∫ w in mp_complexSquare, f w)
      4 (volume.restrict mp_complexSquare)).toReal ≤
      2 * ((eLpNorm (fun z => fderiv ℝ f z 1) 4 (volume.restrict mp_complexSquare)).toReal +
        (eLpNorm (fun z => fderiv ℝ f z I) 4 (volume.restrict mp_complexSquare)).toReal) := by
  let e := Complex.equivRealProdCLM.symm
  let g : ℝ × ℝ → ℂ := fun p => f (e p)
  have hg : ContDiff ℝ 1 g := hf.comp e.contDiff
  have hmean : (∫ p, g p ∂mp_squareMeasure) = ∫ z in mp_complexSquare, f z :=
    mp_complexSquare_measurePreserving.integral_comp' f
  have hderiv : ∀ p v, fderiv ℝ g p v = fderiv ℝ f (e p) (e v) := by
    intro p v
    have hh := (hf.differentiable one_ne_zero (e p)).hasFDerivAt.comp p e.hasFDerivAt
    change (fderiv ℝ (f ∘ e) p) v = _
    rw [hh.fderiv]
    rfl
  have hx : (fun p => fderiv ℝ g p (1, 0)) = fun p => fderiv ℝ f (e p) 1 := by
    funext p
    rw [hderiv]
    simp [e, Complex.equivRealProdCLM_symm_apply]
  have hy : (fun p => fderiv ℝ g p (0, 1)) = fun p => fderiv ℝ f (e p) I := by
    funext p
    rw [hderiv]
    simp [e, Complex.equivRealProdCLM_symm_apply]
  have h := mp_square_poincare_l4 hg
  rw [hmean, hx, hy] at h
  have hc : Continuous (fun z => f z - ∫ w in mp_complexSquare, f w) :=
    hf.continuous.sub continuous_const
  have hcx : Continuous (fun z => fderiv ℝ f z 1) :=
    (hf.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hcy : Continuous (fun z => fderiv ℝ f z I) :=
    (hf.continuous_fderiv one_ne_zero).clm_apply continuous_const
  change (eLpNorm (fun p => f (e p) - ∫ w in mp_complexSquare, f w)
    4 mp_squareMeasure).toReal ≤ _ at h
  rw [mp_complex_square_l4 hc, mp_complex_square_l4 hcx, mp_complex_square_l4 hcy] at h
  exact h

/-- Poincare after subtracting an arbitrary real-linear candidate derivative. -/
theorem mp_complex_square_affine_poincare {f : ℂ → ℂ} (hf : ContDiff ℝ 1 f)
    (A : ℂ →L[ℝ] ℂ) : ∃ c : ℂ,
      MemLp (fun z => f z - A z - c) 4 (volume.restrict mp_complexSquare) ∧
      (eLpNorm (fun z => f z - A z - c) 4 (volume.restrict mp_complexSquare)).toReal ≤
        2 * ((eLpNorm (fun z => fderiv ℝ f z 1 - A 1) 4 (volume.restrict mp_complexSquare)).toReal +
          (eLpNorm (fun z => fderiv ℝ f z I - A I) 4 (volume.restrict mp_complexSquare)).toReal) := by
  let c := ∫ z in mp_complexSquare, f z - A z
  refine ⟨c, mp_complex_square_memLp ((hf.continuous.sub A.continuous).sub continuous_const), ?_⟩
  have h := mp_complex_square_poincare_l4 (hf.sub A.contDiff)
  simpa only [fderiv_fun_sub (hf.differentiable one_ne_zero _) A.differentiableAt,
    A.fderiv, ContinuousLinearMap.sub_apply] using h

/-- A local Morrey--Poincare remainder estimate with no Poincare hypothesis.
Both points lie on the plateau of a cutoff supported in the unit square.
The right side contains only the two real-gradient errors. -/
theorem mp_complex_square_morrey_four :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ η f : ℂ → ℂ,
      ContDiff ℝ 1 η → HasCompactSupport η → ContDiff ℝ 1 f →
      ∀ A : ℂ →L[ℝ] ℂ, tsupport η ⊆ mp_complexSquare →
      (∀ z, ‖η z‖ ≤ 1) → ∀ K : ℝ, 0 ≤ K → (∀ z, ‖dzbar η z‖ ≤ K) →
      ∀ x y : ℂ, η x = 1 → η y = 1 →
      ‖f x - f y - A (x - y)‖ ≤ C * (1 + 2 * K) *
        ((eLpNorm (fun z => fderiv ℝ f z 1 - A 1) 4 (volume.restrict mp_complexSquare)).toReal +
          (eLpNorm (fun z => fderiv ℝ f z I - A I) 4 (volume.restrict mp_complexSquare)).toReal) *
        ‖x - y‖ ^ (1 / 2 : ℝ) := by
  obtain ⟨C, hC, hest⟩ := mp_local_affine_remainder_of_poincare
  refine ⟨C, hC, fun η f hη hc hf A hs hηbound K hK hderiv x y hx hy => ?_⟩
  obtain ⟨c, hR, hP⟩ := mp_complex_square_affine_poincare hf A
  have hfx : MemLp (fun z => fderiv ℝ f z 1 - A 1) 4 (volume.restrict mp_complexSquare) :=
    mp_complex_square_memLp (((hf.continuous_fderiv one_ne_zero).clm_apply
      continuous_const).sub continuous_const)
  have hfy : MemLp (fun z => fderiv ℝ f z I - A I) 4 (volume.restrict mp_complexSquare) :=
    mp_complex_square_memLp (((hf.continuous_fderiv one_ne_zero).clm_apply
      continuous_const).sub continuous_const)
  have h := hest η f hη hc hf A c mp_complexSquare mp_complexSquare_compact.measurableSet hs
    hfx hfy hR hηbound 1 K 2 one_pos hK (by simpa using hderiv) (by simpa using hP)
    x y hx hy
  simpa only [mul_comm K 2] using h

end TakhtajanTeo

