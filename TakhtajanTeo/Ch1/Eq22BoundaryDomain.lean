import TakhtajanTeo.Ch1.Eq22Reproducing

/-! Separation of interior poles from exterior points and conformal collars. -/
open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal Classical Real ComplexConjugate
noncomputable section
namespace TakhtajanTeo
open LiZhongQC

-- D1
theorem eq22_open_separation {Ω E : Set ℂ} (hΩ : IsOpen Ω) (hd : Disjoint Ω E)
    {z : ℂ} (hz : z ∈ Ω) : ∃ a : ℝ, 0 < a ∧ ∀ u ∈ E, a ≤ ‖u-z‖ := by
  obtain ⟨a,ha,hball⟩ := Metric.isOpen_iff.mp hΩ z hz
  refine ⟨a,ha,fun u hu => ?_⟩
  by_contra hn
  have hb : u ∈ ball z a := by simpa only [mem_ball,dist_eq_norm] using lt_of_not_ge hn
  exact Set.disjoint_left.mp hd (hball hb) hu

-- D2
theorem eq22_conformal_collar_separation {f : ℂ → ℂ} {Ω : Set ℂ}
    (hf : IsConformalOnto f unitDisc Ω) {z : ℂ} (hz : z ∈ Ω) :
    ∃ a : ℝ, 0 < a ∧ ∃ r : ℝ, 0 < r ∧ r < 1 ∧
      ∀ w ∈ unitDisc, r ≤ ‖w‖^2 → a ≤ ‖f w-z‖ := by
  let g := Function.invFunOn f unitDisc
  have hΩ : IsOpen Ω := hf.isOpen isOpen_ball
  have hg : IsConformalOnto g Ω unitDisc := hf.symm isOpen_ball
  have hn : ‖g z‖^2 < 1 := by
    have hg0 := mem_ball_zero_iff.mp (hg.mapsTo hz)
    nlinarith [norm_nonneg (g z)]
  let r := (1+‖g z‖^2)/2
  have hr : 0 < r := by dsimp [r]; positivity
  have hr1 : r < 1 := by dsimp [r]; linarith
  have hnr : ‖g z‖^2 < r := by dsimp [r]; linarith
  have hc : ContinuousAt (fun v => ‖g v‖^2) z :=
    (hg.1.continuousOn.continuousAt (hΩ.mem_nhds hz)).norm.pow 2
  obtain ⟨a,ha,hball⟩ := Metric.mem_nhds_iff.mp (hc.eventually (gt_mem_nhds hnr))
  refine ⟨a,ha,r,hr,hr1,fun w hw hwr => ?_⟩
  by_contra hn
  have hfw : f w ∈ ball z a := by simpa only [mem_ball,dist_eq_norm] using lt_of_not_ge hn
  have hsmall : ‖g (f w)‖^2 < r := hball hfw
  have hgf : g (f w) = w := hf.2.1.leftInvOn_invFunOn hw
  rw [hgf] at hsmall
  exact (not_lt_of_ge hwr) hsmall

end TakhtajanTeo
