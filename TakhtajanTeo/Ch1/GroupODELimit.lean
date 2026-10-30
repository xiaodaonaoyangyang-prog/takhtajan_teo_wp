import LiZhongQC.Ch10.S33_BersEmbedding

/-! The fixed-initial-data second-order ODE bridge for the zero-coefficient limit in S3. -/
open Complex Set Filter Topology Metric
open scoped Real
noncomputable section
namespace TakhtajanTeo
open LiZhongQC

theorem grp_ode_small_on_convex {w φ : ℂ → ℂ} {α β : ℂ} {S : Set ℂ} {δ R : ℝ}
    (hS : IsCompact S) (hconv : Convex ℝ S) (hSL : S ⊆ lowerHalf) (h0 : -I ∈ S)
    (hR : 0 < R) (hRS : ∀ z ∈ S, ‖z+I‖ ≤ R) (hδ : 0 ≤ δ) (hsmall : δ*R^2 ≤ 1)
    (hw : DifferentiableOn ℂ w lowerHalf)
    (hode : ∀ z ∈ lowerHalf, deriv (deriv w) z = -(φ z/2)*w z)
    (hα : w (-I) = α) (hβ : deriv w (-I) = β) (hφ : ∀ z ∈ S, ‖φ z‖ ≤ δ) :
    ∀ z ∈ S, ‖w z-(α+β*(z+I))‖ ≤ δ*(‖α‖+‖β‖*R)*R^2 := by
  obtain ⟨x,hx,hmax⟩ := hS.exists_isMaxOn ⟨-I,h0⟩ (hw.continuousOn.mono hSL).norm
  let B := ‖w x‖
  have hB : 0 ≤ B := norm_nonneg _
  have hb : ∀ z ∈ S, ‖w z‖ ≤ B := fun z hz => hmax hz
  have hd : ∀ z ∈ S, DifferentiableAt ℂ w z := fun z hz =>
    hw.differentiableAt (isOpen_lowerHalf.mem_nhds (hSL hz))
  have hdd : ∀ z ∈ S, DifferentiableAt ℂ (deriv w) z := fun z hz =>
    (hw.deriv isOpen_lowerHalf).differentiableAt (isOpen_lowerHalf.mem_nhds (hSL hz))
  have hddbound : ∀ z ∈ S, ‖deriv (deriv w) z‖ ≤ δ/2*B := by
    intro z hz
    rw [hode z (hSL hz),norm_mul,norm_neg,norm_div]
    norm_num only [Complex.norm_ofNat]
    exact mul_le_mul (div_le_div_of_nonneg_right (hφ z hz) (by norm_num)) (hb z hz)
      (norm_nonneg _) (by positivity)
  have hdbound : ∀ z ∈ S, ‖deriv w z-β‖ ≤ δ/2*B*R := by
    intro z hz
    have hh := hconv.norm_image_sub_le_of_norm_deriv_le hdd hddbound h0 hz
    rw [hβ,sub_neg_eq_add] at hh
    exact hh.trans (mul_le_mul_of_nonneg_left (hRS z hz) (by positivity))
  let e : ℂ → ℂ := fun z => w z-(α+β*(z+I))
  have heder : ∀ z ∈ S, HasDerivAt e (deriv w z-β) z := by
    intro z hz
    have hl : HasDerivAt (fun z : ℂ => α+β*(z+I)) β z := by
      simpa using ((((hasDerivAt_id z).add_const I).const_mul β).const_add α)
    exact (hd z hz).hasDerivAt.sub hl
  have he0 : e (-I) = 0 := by simp [e,hα]
  have heb : ∀ z ∈ S, ‖e z‖ ≤ δ/2*B*R^2 := by
    intro z hz
    have hh := hconv.norm_image_sub_le_of_norm_deriv_le
      (fun z hz => (heder z hz).differentiableAt)
      (fun z hz => by rw [(heder z hz).deriv]; exact hdbound z hz) h0 hz
    rw [he0,sub_zero,sub_neg_eq_add] at hh
    calc ‖e z‖ ≤ δ/2*B*R*‖z+I‖ := hh
      _ ≤ δ/2*B*R*R := mul_le_mul_of_nonneg_left (hRS z hz) (by positivity)
      _ = _ := by ring
  have hlin : ‖α+β*(x+I)‖ ≤ ‖α‖+‖β‖*R := by
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul]
    exact add_le_add le_rfl (mul_le_mul_of_nonneg_left (hRS x hx) (norm_nonneg β))
  have hBbound : B ≤ 2*(‖α‖+‖β‖*R) := by
    have hh := norm_le_insert' (w x) (α+β*(x+I))
    have he := heb x hx
    change ‖w x-(α+β*(x+I))‖ ≤ δ/2*B*R^2 at he
    change B ≤ ‖α+β*(x+I)‖+‖w x-(α+β*(x+I))‖ at hh
    nlinarith [mul_nonneg (sub_nonneg.mpr hsmall) hB]
  intro z hz
  calc ‖w z-(α+β*(z+I))‖ ≤ δ/2*B*R^2 := heb z hz
    _ ≤ δ/2*(2*(‖α‖+‖β‖*R))*R^2 := by gcongr
    _ = _ := by ring

theorem grp_ode_zero_limit {φ w : ℕ → ℂ → ℂ} {α β : ℂ}
    (hw : ∀ n, DifferentiableOn ℂ (w n) lowerHalf)
    (hode : ∀ n z, z ∈ lowerHalf → deriv (deriv (w n)) z = -(φ n z/2)*w n z)
    (hα : ∀ n, w n (-I) = α) (hβ : ∀ n, deriv (w n) (-I) = β)
    (hφ : TendstoLocallyUniformlyOn φ (fun _ => 0) atTop lowerHalf) :
    TendstoLocallyUniformlyOn w (fun z => α+β*(z+I)) atTop lowerHalf ∧
    TendstoLocallyUniformlyOn (fun n => deriv (w n)) (fun _ => β) atTop lowerHalf := by
  have hval : TendstoLocallyUniformlyOn w (fun z => α+β*(z+I)) atTop lowerHalf := by
    apply tendstoLocallyUniformlyOn_of_forall_exists_nhds
    intro z hz
    obtain ⟨hf,hm,hunion⟩ := l333_disc_facts
    obtain ⟨i,hi⟩ := mem_iUnion.mp (hunion.symm ▸ hz)
    have hbase : -I ∈ lowerHalf := by simp [lowerHalf]
    obtain ⟨j,hj⟩ := mem_iUnion.mp (hunion.symm ▸ hbase)
    let m := max i j
    let S := closure (l333_disc m)
    have hS : IsCompact S := (hf m).2.2.1
    have hSL : S ⊆ lowerHalf := (hf m).2.2.2.1
    have h0 : -I ∈ S := subset_closure (hm (le_max_right i j) hj)
    have hconv : Convex ℝ S := by
      dsimp [S,l333_disc]
      rw [closure_ball _ (hf m).1.ne']
      exact convex_closedBall _ _
    have hnb : S ∈ 𝓝[lowerHalf] z := mem_nhdsWithin_of_mem_nhds
      (mem_of_superset ((hf m).2.1.mem_nhds (hm (le_max_left i j) hi)) subset_closure)
    refine ⟨S,hnb,?_⟩
    obtain ⟨R₀,hR₀⟩ := hS.exists_bound_of_continuousOn
      (continuous_id.add (continuous_const : Continuous (fun _ : ℂ => I))).continuousOn
    let R := max R₀ 0+1
    have hR : 0 < R := by dsimp [R]; positivity
    have hRS : ∀ u ∈ S, ‖u+I‖ ≤ R := fun u hu => (hR₀ u hu).trans (by dsimp [R]; linarith [le_max_left R₀ 0])
    have hφS := (tendstoLocallyUniformlyOn_iff_forall_isCompact isOpen_lowerHalf).mp hφ S hSL hS
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    let A := (‖α‖+‖β‖*R)*R^2
    have hA : 0 ≤ A := by dsimp [A]; positivity
    let δ := min (1/R^2) (ε/(A+1))
    have hδ : 0 < δ := lt_min (by positivity) (by positivity)
    have hsmall : δ*R^2 ≤ 1 := by
      have hh : δ ≤ 1/R^2 := min_le_left _ _
      exact (le_div_iff₀ (sq_pos_of_pos hR)).mp hh
    have hεb : δ*A < ε := by
      have hh : δ*(A+1) ≤ ε := (le_div_iff₀ (by positivity)).mp (min_le_right _ _)
      nlinarith
    filter_upwards [Metric.tendstoUniformlyOn_iff.mp hφS δ hδ] with n hn
    intro u hu
    have hh := grp_ode_small_on_convex hS hconv hSL h0 hR hRS hδ.le hsmall
      (hw n) (hode n) (hα n) (hβ n) (fun v hv => by simpa using (hn v hv).le) u hu
    rw [dist_comm,dist_eq_norm]
    exact hh.trans_lt (by simpa [A,mul_assoc] using hεb)
  refine ⟨hval,?_⟩
  have hh := hval.deriv (Eventually.of_forall hw) isOpen_lowerHalf
  have hd : deriv (fun z : ℂ => α+β*(z+I)) = fun _ => β := by
    funext z
    have hh : HasDerivAt (fun z : ℂ => α+β*(z+I)) β z := by
      simpa using ((((hasDerivAt_id z).add_const I).const_mul β).const_add α)
    exact hh.deriv
  simpa only [hd,Function.comp_def] using hh

end TakhtajanTeo
