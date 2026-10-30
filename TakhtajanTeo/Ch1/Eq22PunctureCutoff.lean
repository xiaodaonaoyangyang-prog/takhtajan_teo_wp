import TakhtajanTeo.Ch1.Eq22RadialCutoff

/-! Real-valued small-hole cutoffs, including the bound for their complements. -/
open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal Classical Real ComplexConjugate
noncomputable section
namespace TakhtajanTeo
open LiZhongQC

-- H1
theorem eq22_puncture_cutoff_family :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ c : ℂ, ∀ r : ℝ, 0 < r → ∃ b : ℂ → ℂ,
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) b ∧ HasCompactSupport b ∧
      (∀ w, ‖w-c‖ ≤ r/2 → b w = 1) ∧
      (∀ w, r ≤ ‖w-c‖ → b w = 0) ∧
      (∀ w, ‖b w‖ ≤ 1) ∧ (∀ w, ‖1-b w‖ ≤ 1) ∧
      ∀ w, ‖dzbar b w‖ ≤ M/r := by
  obtain ⟨M,hM0,hM⟩ := eq22_radial_cutoff_global_derivative
  have hquarter : (0 : ℝ) < 1/4 := by norm_num
  obtain ⟨hb1,hb0,hbn,hbc⟩ := eq22_radial_cutoff_values hquarter
  refine ⟨4*M,by positivity,fun c r hr => ?_⟩
  let b : ℂ → ℂ := fun w => eq22RadialCutoff (1/4) ((w-c)/(r : ℂ))
  have hn : ∀ w : ℂ, ‖(w-c)/(r : ℂ)‖ = ‖w-c‖/r := by
    intro w
    rw [norm_div,Complex.norm_real,Real.norm_of_nonneg hr.le]
  have hb0' : ∀ w, r ≤ ‖w-c‖ → b w = 0 := by
    intro w hw
    apply hb0
    have he : 1 ≤ ‖(w-c)/(r : ℂ)‖ := by rw [hn,le_div_iff₀ hr]; simpa using hw
    nlinarith [norm_nonneg ((w-c)/(r : ℂ))]
  refine ⟨b,?_,?_,?_,hb0',fun w => hbn _,fun w => hbc _,?_⟩
  · exact (eq22_radial_cutoff_smooth (1/4)).comp
      ((contDiff_id.sub contDiff_const).div_const (r : ℂ))
  · apply HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall c r)
    intro w hw
    rw [mem_closedBall,dist_eq_norm]
    by_contra hn
    exact hw (hb0' w (le_of_lt (lt_of_not_ge hn)))
  · intro w hw
    apply hb1
    have he : ‖(w-c)/(r : ℂ)‖ ≤ 1/2 := by rw [hn,div_le_iff₀ hr]; linarith
    nlinarith [norm_nonneg ((w-c)/(r : ℂ))]
  · intro w
    have hf : HasDerivAt (fun v : ℂ => (v-c)/(r : ℂ)) ((r : ℂ)⁻¹) w := by
      simpa only [id_eq,one_div] using ((hasDerivAt_id w).sub_const c).div_const (r : ℂ)
    have hd := (eq6_4 hf.differentiableAt
      (((eq22_radial_cutoff_smooth (1/4)).differentiable (by simp)) ((w-c)/(r : ℂ)))).2
    change dzbar b w = _ at hd
    rw [hf.deriv] at hd
    rw [hd,norm_mul,Complex.norm_conj,norm_inv,Complex.norm_real,Real.norm_of_nonneg hr.le]
    calc
      ‖dzbar (eq22RadialCutoff (1/4)) ((w-c)/(r : ℂ))‖*r⁻¹ ≤ (M/(1/4))*r⁻¹ := by
        gcongr
        exact hM (1/4) hquarter _
      _ = 4*M/r := by ring

-- H2
theorem eq22_remove_point_cutoff {t b : ℂ → ℂ} {Ω : Set ℂ} {a : ℂ} {r : ℝ}
    (ht : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) t) (htc : HasCompactSupport t)
    (hts : tsupport t ⊆ Ω) (htn : ∀ w, ‖t w‖ ≤ 1)
    (hb : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) b)
    (hbn : ∀ w, ‖1-b w‖ ≤ 1) (hr : 0 < r)
    (hb1 : ∀ w, ‖w-a‖ < r → b w = 1) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun w => t w*(1-b w)) ∧
    HasCompactSupport (fun w => t w*(1-b w)) ∧
    tsupport (fun w => t w*(1-b w)) ⊆ Ω \ {a} ∧
    (∀ w, ‖t w*(1-b w)‖ ≤ 1) := by
  have hsub : tsupport (fun w => t w*(1-b w)) ⊆ tsupport t := tsupport_mul_subset_left
  have haway : tsupport (fun w => t w*(1-b w)) ⊆ (ball a r)ᶜ := by
    apply closure_minimal ?_ isOpen_ball.isClosed_compl
    intro w hw hwr
    apply hw
    change t w*(1-b w) = 0
    rw [hb1 w (by simpa only [mem_ball,dist_eq_norm] using hwr),sub_self,mul_zero]
  refine ⟨ht.mul (contDiff_const.sub hb),htc.of_isClosed_subset (isClosed_tsupport _) hsub,?_,?_⟩
  · intro w hw
    refine ⟨hts (hsub hw),?_⟩
    intro hwa
    have he : w = a := mem_singleton_iff.mp hwa
    exact haway hw (by rw [he]; exact mem_ball_self hr)
  · intro w
    rw [norm_mul]
    simpa only [one_mul] using mul_le_mul (htn w) (hbn w) (norm_nonneg _) zero_le_one

-- H3
theorem eq22_puncture_error_bound {F b : ℂ → ℂ} {a : ℂ} {r B M : ℝ}
    (hr : 0 < r) (hB : 0 ≤ B) (hM : 0 ≤ M)
    (hF : ∀ w ∈ ball a r, ‖F w‖ ≤ B)
    (hb : ∀ w ∈ ball a r, ‖dzbar b w‖ ≤ M/r) :
    ‖∫ w in ball a r, F w*dzbar b w‖ ≤ π*B*M*r := by
  have hbound : ∀ w ∈ ball a r, ‖F w*dzbar b w‖ ≤ B*M/r := by
    intro w hw
    rw [norm_mul]
    calc
      ‖F w‖*‖dzbar b w‖ ≤ B*(M/r) :=
        mul_le_mul (hF w hw) (hb w hw) (norm_nonneg _) hB
      _ = B*M/r := by ring
  have hi := norm_setIntegral_le_of_norm_le_const_ae
    (measure_ball_lt_top : volume (ball a r) < ∞)
    ((ae_restrict_mem measurableSet_ball).mono (fun w hw => hbound w hw))
  apply hi.trans_eq
  simp only [Measure.real,Complex.volume_ball,ENNReal.toReal_mul,ENNReal.toReal_pow,
    ENNReal.coe_toReal,NNReal.coe_real_pi,ENNReal.toReal_ofReal hr.le]
  field_simp
  <;> ring

end TakhtajanTeo
