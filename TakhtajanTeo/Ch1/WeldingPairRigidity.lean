import TakhtajanTeo.Ch1.FiberCircleOrientation
import Mathlib.Analysis.Complex.AbsMax

/-! Infrastructure for uniqueness of arbitrary normalized welding pairs. -/
open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal NNReal ComplexConjugate Classical Real
noncomputable section
namespace TakhtajanTeo
open LiZhongQC

theorem circle_lift_surjective {u : ℝ → ℝ} (hu : Continuous u)
    (hp : ∀ t, u (t + 2 * π) = u t + 2 * π) : Function.Surjective u := by
  have hP : 0 < 2 * π := by positivity
  have hperiod : ∀ t, u (t + 2 * π) = u t + (1 : ℤ) * (2 * π) := by simpa using hp
  have hn : ∀ n : ℤ, u ((n : ℝ) * (2 * π)) = u 0 + (n : ℝ) * (2 * π) := by
    intro n
    simpa using CircleLift.lift_per_int hperiod 0 n
  intro y
  obtain ⟨n, hnlt⟩ := exists_int_lt ((y - u 0) / (2 * π))
  obtain ⟨m, hmlt⟩ := exists_int_gt ((y - u 0) / (2 * π))
  have hlow : u ((n : ℝ) * (2 * π)) < y := by
    rw [hn]
    have := (lt_div_iff₀ hP).mp hnlt
    linarith
  have hhigh : y < u ((m : ℝ) * (2 * π)) := by
    rw [hn]
    have := (div_lt_iff₀ hP).mp hmlt
    linarith
  obtain ⟨t, -, ht⟩ := intermediate_value_uIcc
    (hu.continuousOn (s := uIcc ((n : ℝ) * (2 * π)) ((m : ℝ) * (2 * π))))
    (mem_uIcc.mpr (Or.inl ⟨hlow.le, hhigh.le⟩))
  exact ⟨t, ht⟩

theorem sense_circle_image {h : ℂ → ℂ}
    (hh : Pommerenke1992.IsSensePreservingCircleHomeo h) :
    h '' unitCircle = unitCircle := by
  obtain ⟨u, hu, -, hp, he⟩ := hh
  have heζ : ∀ ζ : Circle, ∃ t : ℝ, (ζ : ℂ) = exp (t * I) := by
    intro ζ
    obtain ⟨t, rfl⟩ := Circle.exp_surjective ζ
    exact ⟨t, Circle.coe_exp t⟩
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨t, ht⟩ := heζ ⟨x, mem_sphere_zero_iff_norm.mpr hx⟩
    change x = exp (t * I) at ht
    rw [ht, he]
    exact Complex.norm_exp_ofReal_mul_I _
  · intro hz
    obtain ⟨s, hs⟩ := heζ ⟨z, mem_sphere_zero_iff_norm.mpr hz⟩
    obtain ⟨t, ht⟩ := circle_lift_surjective hu hp s
    exact ⟨exp (t * I), Complex.norm_exp_ofReal_mul_I _, by rw [he, ht, ← hs]⟩

theorem planeHomeomorph_circle_closed_subset (e : ℂ ≃ₜ ℂ)
    (he : MapsTo e (sphere (0 : ℂ) 1) (sphere (0 : ℂ) 1)) :
    e '' closedBall (0 : ℂ) 1 ⊆ closedBall (0 : ℂ) 1 := by
  have hb : Bornology.IsBounded (e '' ball (0 : ℂ) 1) :=
    ((isCompact_closedBall (0 : ℂ) 1).image e.continuous).isBounded.subset
      (image_mono ball_subset_closedBall)
  have hboundary : ∀ z ∈ frontier (e '' ball (0 : ℂ) 1), ‖(id : ℂ → ℂ) z‖ ≤ 1 := by
    intro z hz
    rw [← e.image_frontier, frontier_ball (0 : ℂ) one_ne_zero] at hz
    obtain ⟨x, hx, rfl⟩ := hz
    exact (mem_sphere_zero_iff_norm.mp (he hx)).le
  rintro z ⟨x, hx, rfl⟩
  apply mem_closedBall_zero_iff.mpr
  apply Complex.norm_le_of_forall_mem_frontier_norm_le hb
    (differentiable_id : Differentiable ℂ (id : ℂ → ℂ)).diffContOnCl hboundary
  rw [← e.image_closure, closure_ball (0 : ℂ) one_ne_zero]
  exact mem_image_of_mem e hx

theorem planeHomeomorph_circle_regions (e : ℂ ≃ₜ ℂ)
    (he : e '' sphere (0 : ℂ) 1 = sphere (0 : ℂ) 1) :
    e '' closedBall (0 : ℂ) 1 = closedBall (0 : ℂ) 1 ∧
      e '' unitDisc = unitDisc ∧ e '' unitDiscExterior = unitDiscExterior := by
  have hei : e.symm '' sphere (0 : ℂ) 1 = sphere (0 : ℂ) 1 := by
    calc
      e.symm '' sphere (0 : ℂ) 1 = e.symm '' (e '' sphere (0 : ℂ) 1) :=
        congrArg (fun s : Set ℂ => e.symm '' s) he.symm
      _ = sphere (0 : ℂ) 1 := e.toEquiv.symm_image_image _
  have hsub := planeHomeomorph_circle_closed_subset e (image_subset_iff.mp he.subset)
  have hisub := planeHomeomorph_circle_closed_subset e.symm (image_subset_iff.mp hei.subset)
  have hcl : e '' closedBall (0 : ℂ) 1 = closedBall (0 : ℂ) 1 := by
    apply Subset.antisymm hsub
    intro z hz
    exact ⟨e.symm z, hisub (mem_image_of_mem e.symm hz), e.apply_symm_apply z⟩
  refine ⟨hcl, ?_, ?_⟩
  · change e '' ball (0 : ℂ) 1 = ball (0 : ℂ) 1
    rw [← interior_closedBall (0 : ℂ) one_ne_zero, e.image_interior, hcl]
  · have hE : unitDiscExterior = (closedBall (0 : ℂ) 1)ᶜ := by
      ext z
      simp [unitDiscExterior, mem_closedBall_zero_iff, not_le]
    rw [hE]
    calc
      e '' (closedBall (0 : ℂ) 1)ᶜ = (e '' closedBall (0 : ℂ) 1)ᶜ := e.toEquiv.image_compl _
      _ = (closedBall (0 : ℂ) 1)ᶜ := congrArg (fun s : Set ℂ => sᶜ) hcl

theorem planeQC_unique_normalized_jet {f g : ℂ → ℂ}
    (hf : IsQuasiconformal f univ) (hg : IsQuasiconformal g univ)
    (hfs : f '' univ = univ) (hgs : g '' univ = univ)
    (hμ : ∀ᵐ z, complexDilatation f z = complexDilatation g z)
    (hfd : DifferentiableAt ℂ f 0) (hf0 : f 0 = 0) (hg0 : g 0 = 0)
    (hf1 : deriv f 0 = 1) (hg1 : deriv g 0 = 1) : f = g := by
  obtain ⟨φ, hφ, hrel⟩ := uq_conformal_auto isOpen_univ hf hg hfs hgs
    (by simpa only [Measure.restrict_univ] using hμ)
  obtain ⟨a, b, -, hab⟩ := nx_entire_affine hφ
  have hb : b = 0 := by simpa [hf0, hg0, hab] using (hrel 0 (mem_univ 0)).symm
  have he : g = fun z => a * f z := by
    funext z
    simpa [hab, hb] using hrel z (mem_univ z)
  have ha : a = 1 := by
    have hd := (hfd.hasDerivAt.const_mul a).deriv
    rw [← he, hg1, hf1, mul_one] at hd
    exact hd.symm
  funext z
  simp [he, ha]

def circleGlue (f g : ℂ → ℂ) (z : ℂ) : ℂ :=
  if ‖z‖ ≤ 1 then f z else g z

theorem circleGlue_inside (f g : ℂ → ℂ) {z : ℂ} (hz : z ∈ unitDisc) :
    circleGlue f g z = f z := by
  exact if_pos (mem_ball_zero_iff.mp hz).le

theorem circleGlue_outside (f g : ℂ → ℂ) {z : ℂ} (hz : z ∈ unitDiscExterior) :
    circleGlue f g z = g z := if_neg (not_le.mpr hz)

theorem circleGlue_homeomorph (A B : ℂ ≃ₜ ℂ)
    (hA : A '' sphere (0 : ℂ) 1 = sphere (0 : ℂ) 1)
    (hB : B '' sphere (0 : ℂ) 1 = sphere (0 : ℂ) 1)
    (he : ∀ z : ℂ, ‖z‖ = 1 → A z = B z) :
    IsHomeomorphOnto (circleGlue A B) univ univ := by
  have hmem : ∀ (e : ℂ ≃ₜ ℂ), e '' closedBall (0 : ℂ) 1 = closedBall (0 : ℂ) 1 →
      ∀ z : ℂ, ‖e z‖ ≤ 1 ↔ ‖z‖ ≤ 1 := by
    intro e he z
    constructor
    · intro hz
      have hh : e z ∈ e '' closedBall (0 : ℂ) 1 := by
        rw [he]
        exact mem_closedBall_zero_iff.mpr hz
      obtain ⟨x, hx, hh⟩ := hh
      rw [e.injective hh] at hx
      exact mem_closedBall_zero_iff.mp hx
    · intro hz
      have hh := mem_image_of_mem e (mem_closedBall_zero_iff.mpr hz)
      rw [he] at hh
      exact mem_closedBall_zero_iff.mp hh
  have hAm := hmem A (planeHomeomorph_circle_regions A hA).1
  have hBm := hmem B (planeHomeomorph_circle_regions B hB).1
  have hc : Continuous (circleGlue A B) :=
    continuous_if_le continuous_norm continuous_const A.continuous.continuousOn
      B.continuous.continuousOn he
  have hb : Function.Bijective (circleGlue A B) := by
    constructor
    · intro z w hzw
      by_cases hz : ‖z‖ ≤ 1 <;> by_cases hw : ‖w‖ ≤ 1
      · exact A.injective (by simpa [circleGlue, hz, hw] using hzw)
      · have hh : A z = B w := by simpa [circleGlue, hz, hw] using hzw
        exact (hw ((hBm w).mp (hh ▸ (hAm z).mpr hz))).elim
      · have hh : B z = A w := by simpa [circleGlue, hz, hw] using hzw
        exact (hz ((hBm z).mp (hh.symm ▸ (hAm w).mpr hw))).elim
      · exact B.injective (by simpa [circleGlue, hz, hw] using hzw)
    · intro y
      by_cases hy : ‖y‖ ≤ 1
      · have hx : ‖A.symm y‖ ≤ 1 := (hAm _).mp (by simpa using hy)
        exact ⟨A.symm y, by simp [circleGlue, hx]⟩
      · have hx : ¬‖B.symm y‖ ≤ 1 := by
          intro hh
          exact hy (by simpa using (hBm _).mpr hh)
        exact ⟨B.symm y, by simp [circleGlue, hx]⟩
  have hh := qcl_f_isHomeomorphOnto_of_injOn isOpen_univ hc.continuousOn hb.1.injOn
  rwa [image_univ_of_surjective hb.2] at hh

theorem circleGlue_quasiconformal {f g : ℂ → ℂ}
    (hf : IsQuasiconformal f univ) (hg : IsQuasiconformal g univ)
    (hfs : f '' univ = univ) (hgs : g '' univ = univ)
    (hfc : f '' sphere (0 : ℂ) 1 = sphere (0 : ℂ) 1)
    (hgc : g '' sphere (0 : ℂ) 1 = sphere (0 : ℂ) 1)
    (he : ∀ z : ℂ, ‖z‖ = 1 → f z = g z) :
    IsQuasiconformal (circleGlue f g) univ ∧ circleGlue f g '' univ = univ := by
  obtain ⟨Kf, hKf⟩ := hf
  obtain ⟨Kg, hKg⟩ := hg
  obtain ⟨A, rfl⟩ := t1_homeomorph hKf hfs
  obtain ⟨B, rfl⟩ := t1_homeomorph hKg hgs
  have hhome := circleGlue_homeomorph A B hfc hgc he
  refine ⟨⟨max Kf Kg, abR_removable hhome ?_ ?_⟩, hhome.2.2.1⟩
  · exact ad_isKQC_congr ((nx_isKQC_restrict hKf isOpen_ball (subset_univ _)).mono
      (le_max_left _ _)) (fun z hz => circleGlue_inside A B hz)
  · exact ad_isKQC_congr ((nx_isKQC_restrict hKg
      (isOpen_lt continuous_const continuous_norm) (subset_univ _)).mono
      (le_max_right _ _)) (fun z hz => circleGlue_outside A B hz)

end TakhtajanTeo

#print axioms TakhtajanTeo.sense_circle_image
#print axioms TakhtajanTeo.planeHomeomorph_circle_regions
#print axioms TakhtajanTeo.planeQC_unique_normalized_jet
#print axioms TakhtajanTeo.circleGlue_quasiconformal
