import TakhtajanTeo.Ch2.S4VariationCompleted
import TakhtajanTeo.Ch2.S3SchwarzianTrace

/-! # Actual holomorphic variation and the diagonal kernel (`s4hv_`) -/
open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal ComplexConjugate Classical Real
noncomputable section
namespace TakhtajanTeo
open LiZhongQC QCV
namespace Ch2

def s4hv_kernel (g : ℂ → ℂ) (w z : ℂ) : ℂ :=
  deriv g w ^ 2 * deriv g z ^ 2 / (g w - g z) ^ 4 - 1 / (w - z) ^ 4

-- H1
theorem s4hv_lieTheta_split {κ : LinfStar} (hκ : κ ∈ LinfStarBall) {ν : ℂ → ℂ}
    (hν : ν ∈ harmonicL2 unitDiscExterior) {z : ℂ} (hz : z ∈ unitDiscExterior) :
    lieTheta κ ν z =
      deriv (fun e : ℂ => schwarzianDz
        (gsans (beltramiMul (e • toLinf ν) κ) ∘ wA (e • toLinf ν)) z) 0 -
      dz (fun e : ℂ => schwarzianDz (wA (e • toLinf ν)) z) 0 := by
  have hνh : toLinf ν ∈ harmonicBeltrami := (harmonicL2_subset_harmonic.choose_spec ν hν).1
  let H := fun e : ℂ => schwarzianDz (gsans (beltramiMul (e • toLinf ν) κ) ∘ wA (e • toLinf ν)) z
  let W := fun e : ℂ => schwarzianDz (wA (e • toLinf ν)) z
  have hH : DifferentiableAt ℂ H 0 := s4pv_welded_schwarzian_holomorphic hκ hνh hz
  have hW : DifferentiableAt ℝ W 0 := (s4ma_wA_variation hνh hz).1
  have hsmall : ∀ᶠ e : ℂ in 𝓝 0, ‖e‖ * ‖toLinf ν‖ < 1 :=
    (continuous_norm.mul continuous_const).continuousAt.eventually_lt continuousAt_const (by simp)
  have heq : (fun e : ℂ => schwarzianHol (gsans (beltramiMul (e • toLinf ν) κ))
      (wA (e • toLinf ν) z) * dz (wA (e • toLinf ν)) z ^ 2) =ᶠ[𝓝 0] (fun e => H e - W e) := by
    filter_upwards [hsmall, s4ma_pole_absent_eventually (toLinf ν) z] with e he hp
    have heB : e • toLinf ν ∈ LinfStarBall := by
      simpa [LinfStarBall, mem_ball_zero_iff, norm_smul] using he
    obtain ⟨hwc, hwz, hwE⟩ := e41_w_regular hνh he hz hp
    obtain ⟨hga, hgz⟩ := e41_g_holo (wA_mul hκ heB).1 hwE
    exact eq_sub_of_add_eq (e41_schw_left hga hgz hwc hwz).symm
  have hsub : dz (fun e => H e - W e) 0 = dz H 0 - dz W 0 := by
    unfold dz
    rw [fderiv_fun_sub (hH.restrictScalars ℝ) hW]
    simp only [sub_apply]
    ring
  rw [lieTheta, (t203_c1_dz_congr heq).1, hsub, dz_eq_deriv hH]

-- H2
theorem s4hv_kernel_factorization (g : ℂ → ℂ) {w z : ℂ} (hwz : w ≠ z) :
    s4hv_kernel g w z = (π : ℂ) ^ 2 * kerK4 g w z ^ 2 -
      2 * π * kerK4 g w z / (w - z) ^ 2 := by
  let A := deriv g w * deriv g z / (g w - g z) ^ 2
  let B : ℂ := 1 / (w - z) ^ 2
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hK : (π : ℂ) * kerK4 g w z = B - A := by
    rw [kerK4_of_ne g hwz]
    change (π : ℂ) * (1 / π * (B - A)) = B - A
    rw [← mul_assoc, mul_one_div, div_self hπ, one_mul]
  have hA : A = B - π * kerK4 g w z := by linear_combination hK
  calc s4hv_kernel g w z = A ^ 2 - B ^ 2 := by
        simp only [s4hv_kernel, A, B, div_pow, mul_pow, ← pow_mul, one_pow]
      _ = _ := by rw [hA]; dsimp only [B]; ring

-- H3
theorem s4hv_kernel_symm (g : ℂ → ℂ) (w z : ℂ) :
    s4hv_kernel g w z = s4hv_kernel g z w := by
  unfold s4hv_kernel
  rw [show (g z - g w) ^ 4 = (g w - g z) ^ 4 by ring,
    show (z - w) ^ 4 = (w - z) ^ 4 by ring]
  ring

-- H4
theorem s4hv_K4_analytic {κ : LinfStar} (hκ : κ ∈ LinfStarBall) {z : ℂ}
    (hz : z ∈ unitDiscExterior) :
    AnalyticOnNhd ℂ (fun w => kerK4 (gsans κ) w z) unitDiscExterior := by
  have hg := S2C.s2c_conf_g hκ
  exact (AppB.differentiableOn_kerK1 wp_exterior_isOpen hg.1 hg.2.1 hz).analyticOnNhd wp_exterior_isOpen

-- H5
theorem s4hv_K4_column_A21 {κ : LinfStar} (hκ : κ ∈ LinfStarBall) {z : ℂ}
    (hz : z ∈ unitDiscExterior) :
    (fun w => kerK4 (gsans κ) w z) ∈ A21fun unitDiscExterior := by
  let T := gopOp (B4 (grunsky (fsans κ) (gsans κ)))
  have hs := e212_ext_series (gop_l2_summable (T (s3st_vector z)))
  apply (ab112_A21fun_congr wp_exterior_isOpen (φ := fun w => ∑' n, (T (s3st_vector z)) n * basisF n w)
    (ψ := fun w => kerK4 (gsans κ) w z) ?_).1 hs
  intro w hw
  exact (s3st_kernel_series T hw z).symm.trans (s3st_B4_kernel hκ hw hz)

-- H6
theorem s4hv_harmonic_smooth {ν : ℂ → ℂ} (hν : ν ∈ harmonicL2 unitDiscExterior) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ν unitDiscExterior := by
  obtain ⟨φ, hφ, hrep, -⟩ := hν
  have hφs : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ unitDiscExterior :=
    (hφ.contDiffOn wp_exterior_isOpen).restrict_scalars ℝ
  have hconj : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z => conj (φ z)) unitDiscExterior :=
    Complex.conjCLE.toContinuousLinearMap.contDiff.comp_contDiffOn hφs
  have hw : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : ℂ => (rho z : ℂ)⁻¹) := by
    have hs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : ℂ => (1 - ‖z‖ ^ 2) ^ 2 / 4) :=
      ((contDiff_const.sub (contDiff_norm_sq ℝ)).pow 2).div_const 4
    convert Complex.ofRealCLM.contDiff.comp hs using 1
    funext z
    simp [rho, Complex.ofReal_div, inv_div]
  exact (hw.contDiffOn.mul hconj).congr hrep

end Ch2
end TakhtajanTeo
