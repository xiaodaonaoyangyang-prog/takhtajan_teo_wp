import TakhtajanTeo.Ch2.S1_Remark19

/-! # Normalized symmetric lifts and their actual disk extensions -/
open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal NNReal ComplexConjugate Classical Real
noncomputable section
namespace TakhtajanTeo
open LiZhongQC
namespace Ch2

/-- Normalize a symmetric angular lift without changing its ratios. -/
theorem symt_normalized_lift {h : ℂ → ℂ} (hh : IsSymmetricHomeo h) :
    ∃ v : ℝ → ℝ, GardinerLakic2000.IsCircleLift h v ∧
      ∀ ε > 0, ∃ δ > 0, ∀ x t : ℝ, 0 < t → t < δ →
        |(v (x+t)-v x)/(v x-v (x-t))-1| < ε := by
  obtain ⟨u, hc, hm, hp, he, hr⟩ := hh
  have hπ : (0 : ℝ) < 2 * π := by positivity
  let k : ℤ := ⌊u 0 / (2 * π)⌋
  let v : ℝ → ℝ := fun x => u (2 * π * x) / (2 * π) - k
  have hvc : Continuous v := ((hc.comp (continuous_const.mul continuous_id)).div_const _).sub continuous_const
  have hvm : StrictMono v := by
    intro x y hxy
    exact sub_lt_sub_right ((div_lt_div_iff_of_pos_right hπ).mpr (hm (mul_lt_mul_of_pos_left hxy hπ))) _
  have hvp : ∀ x, v (x+1) = v x+1 := by
    intro x
    dsimp only [v]
    rw [show 2 * π * (x+1) = 2 * π * x + 2 * π by ring, hp]
    field_simp
    <;> ring
  have hv0 : v 0 = Int.fract (u 0 / (2 * π)) := by simp only [v, mul_zero, Int.fract, k]
  refine ⟨v, ⟨hvc, hvm, ?_, ?_, hvp, ?_⟩, ?_⟩
  · rw [hv0]; exact Int.fract_nonneg _
  · rw [hv0]; exact Int.fract_lt_one _
  · intro x
    have e1 : exp (2 * π * I * x) = exp (((2 * π * x : ℝ) : ℂ) * I) := by push_cast; ring_nf
    rw [e1, he]
    have e2 : 2 * (π : ℂ) * I * (v x : ℂ) = (u (2 * π * x) : ℂ) * I - (k : ℂ) * (2 * π * I) := by
      dsimp only [v]
      push_cast
      field_simp
    rw [e2, Complex.exp_sub, Complex.exp_int_mul_two_pi_mul_I, div_one]
  · intro ε hε
    obtain ⟨δ, hδ, hb⟩ := hr ε hε
    refine ⟨δ / (2 * π), div_pos hδ hπ, fun x t ht htδ => ?_⟩
    have ht' : 2 * π * t < δ := by rw [lt_div_iff₀ hπ] at htδ; nlinarith
    have h := hb (2 * π * x) (2 * π * t) (mul_pos hπ ht) ht'
    have eqr : (v (x+t)-v x)/(v x-v (x-t)) =
        (u (2 * π * x + 2 * π * t)-u (2 * π * x)) /
          (u (2 * π * x)-u (2 * π * x - 2 * π * t)) := by
      dsimp only [v]
      rw [mul_add, mul_sub]
      simp only [sub_sub_sub_cancel_right, ← sub_div, div_div_div_cancel_right₀ hπ.ne']
    rwa [eqr]

/-- The normalized BA extension is differentiable at every point of the upper half-plane. -/
theorem symt_ba_differentiable {v : ℝ → ℝ} (hc : Continuous v) {z : ℂ} (hz : 0 < z.im) :
    DifferentiableAt ℝ (beurlingAhlfors v 2) z := by
  have h1 : DifferentiableAt ℝ (beurlingAhlfors v 1) z :=
    ((ba_f1h_contDiffOn hc).contDiffAt (isOpen_upperHalf.mem_nhds hz)).differentiableAt one_ne_zero
  have he : beurlingAhlfors v 2 = s17p_stretch ∘ beurlingAhlfors v 1 := funext (s17p_ba2_apply v)
  rw [he]
  exact s17p_stretch.differentiableAt.comp z h1

/-- Uniform upper-half-plane BA decay descends to an actual pointwise radial limit. -/
theorem symt_disk_decay {v : ℝ → ℝ} (hc : Continuous v) (hp : ∀ x, v (x+1) = v x+1)
    (hv : ∀ ε > 0, ∃ η > 0, ∀ z : ℂ, 0 < z.im → z.im < η →
      ‖complexDilatation (beurlingAhlfors v 2) z‖ < ε) :
    Tendsto (complexDilatation (periodicDiskMap (beurlingAhlfors v 2)))
      (comap (fun z : ℂ => ‖z‖) (𝓝[<] 1)) (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨η, hη, hb⟩ := hv ε hε
  have hr : Real.exp (-2 * π * η) < 1 := Real.exp_lt_one_iff.mpr (by nlinarith [Real.pi_pos])
  have hev : ∀ᶠ w in comap (fun z : ℂ => ‖z‖) (𝓝[<] 1),
      ‖w‖ ∈ Ioo (Real.exp (-2 * π * η)) 1 := tendsto_comap.eventually (Ioo_mem_nhdsLT hr)
  filter_upwards [hev] with w hw
  have hw0 : w ≠ 0 := norm_pos_iff.mp (lt_trans (Real.exp_pos _) hw.1)
  have hwD : w ∈ diskCover '' upperHalf := by
    rw [diskCover_image]
    exact ⟨mem_ball_zero_iff.mpr hw.2, hw0⟩
  obtain ⟨z, hz, rfl⟩ := hwD
  have hzη : z.im < η := by
    have hr' := hw.1
    rw [diskCover_norm, Real.exp_lt_exp] at hr'
    nlinarith [Real.pi_pos]
  rw [dist_zero_right, r19_disk_dil_pt (beurlingAhlfors_add_int hc hp 2) (symt_ba_differentiable hc hz)]
  exact hb z hz hzη

/-- A symmetric QS circle map has an actual QC disk extension fixing zero,
with its given boundary values and pointwise vanishing complex dilatation. -/
theorem symt_disk_extension {h : ℂ → ℂ} (hq : IsQSCircleHomeo h) (hs : IsSymmetricHomeo h) :
    ∃ G : ℂ → ℂ, Continuous G ∧ InjOn G unitDisc ∧ G '' unitDisc = unitDisc ∧ G 0 = 0 ∧
      EqOn G h unitCircle ∧ IsQuasiconformal G unitDisc ∧
      (∀ z ∈ unitDisc, z ≠ 0 → DifferentiableAt ℝ G z) ∧
      Tendsto (complexDilatation G) (comap (fun z : ℂ => ‖z‖) (𝓝[<] 1)) (𝓝 0) := by
  obtain ⟨v, hl, hv⟩ := symt_normalized_lift hs
  obtain ⟨M, hM⟩ := GardinerLakic2000.gl16_cl_M_of_qsA (circle_quasisymmetric_ahlfors hq.2)
  obtain ⟨ρ, hρ⟩ := GardinerLakic2000.gl16_qs_of_M hl hM
  obtain ⟨hc, hi, himg, h0, hb, K, hK⟩ := r19_disk_ext hl hρ
  refine ⟨_, hc, hi, himg, h0, hb, ⟨K,hK⟩, ?_,
    symt_disk_decay hl.1 hl.2.2.2.2.1 (AppB.b9_lift_BA_vanishing hl.2.1 hl.1 hv)⟩
  intro w hw hw0
  have hwD : w ∈ diskCover '' upperHalf := by rw [diskCover_image]; exact ⟨hw,hw0⟩
  obtain ⟨z, hz, rfl⟩ := hwD
  have hd := symt_ba_differentiable hl.1 hz
  have hper := beurlingAhlfors_add_int hl.1 hl.2.2.2.2.1 2
  have he := periodicDiskMap_cover hper
  have hu := diskCover_injOn_ball z
  have hconf : IsConformalOnto diskCover (ball z (1/3)) (diskCover '' ball z (1/3)) :=
    ⟨diskCover_differentiable.differentiableOn, hu, rfl⟩
  have hzB : z ∈ ball z (1/3) := mem_ball_self (by norm_num)
  have hwin : diskCover z ∈ diskCover '' ball z (1/3) := mem_image_of_mem _ hzB
  have hinv := (hconf.symm isOpen_ball).1.differentiableAt (hconf.isOpen isOpen_ball |>.mem_nhds hwin)
  have hiz := hu.leftInvOn_invFunOn hzB
  have hd' : DifferentiableAt ℝ (diskCover ∘ beurlingAhlfors v 2 ∘ Function.invFunOn diskCover (ball z (1/3)))
      (diskCover z) := (diskCover_differentiable _ |>.restrictScalars ℝ).comp _
        ((hiz ▸ hd).comp _ (hinv.restrictScalars ℝ))
  apply hd'.congr_of_eventuallyEq
  filter_upwards [hconf.isOpen isOpen_ball |>.mem_nhds hwin] with y hy
  obtain ⟨x, hx, rfl⟩ := hy
  simp only [Function.comp_apply, hu.leftInvOn_invFunOn hx]
  exact he x

end Ch2
end TakhtajanTeo
