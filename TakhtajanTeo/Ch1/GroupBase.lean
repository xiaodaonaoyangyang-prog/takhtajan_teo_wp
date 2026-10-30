import TakhtajanTeo.Ch1.GroupOrigin
import TakhtajanTeo.Ch1.GroupKnLimit

/-! S3 prerequisites: normalized plane maps prevent degeneration of the
K-to-one limit. The quantitative origin estimate is not yet proved here. -/
open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal NNReal ComplexConjugate Classical Real
noncomputable section
namespace TakhtajanTeo
open LiZhongQC

/-- Normalization at zero and one, together with plane surjectivity, identifies
every locally uniform limit as the identity when distortion tends to one. -/
theorem grp25b_normalized_limit {Fn : ℕ → ℂ → ℂ} {Kn : ℕ → ℝ}
    {G : ℂ → ℂ} {Kbar : ℝ}
    (hqc : ∀ n, IsKQC (Fn n) univ (Kn n)) (hbound : ∀ n, Kn n ≤ Kbar)
    (hnorm : ∀ n, Fn n '' univ = univ ∧ Fn n 0 = 0 ∧ Fn n 1 = 1)
    (hKn : Tendsto Kn atTop (𝓝 1))
    (hlim : TendstoLocallyUniformly Fn G atTop) : G = id := by
  have hN : ∀ n, IsKQCNormalizedPlane (Fn n) Kbar :=
    fun n => ⟨(hqc n).mono (hbound n), hnorm n⟩
  have hG := t203_lim_nf_limit hN hlim
  have hhol := ab_kn_one_limit hqc hbound hKn hlim
  obtain ⟨a, -, ha⟩ := nxU_entire_linear
    ⟨hhol.differentiableOn, hG.1.2.2.1.2.1, hG.2.1⟩ hG.2.2.1
  have ha1 : a = 1 := by simpa [hG.2.2.2] using (ha 1).symm
  funext z
  simpa [ha1] using ha z

/-- The normalized family has an identity-convergent subsequence; its limit
cannot be constant, so no injectivity premise is being omitted. -/
theorem grp25b_normalized_subseq {Fn : ℕ → ℂ → ℂ} {Kn : ℕ → ℝ} {Kbar : ℝ}
    (hqc : ∀ n, IsKQC (Fn n) univ (Kn n)) (hbound : ∀ n, Kn n ≤ Kbar)
    (hnorm : ∀ n, Fn n '' univ = univ ∧ Fn n 0 = 0 ∧ Fn n 1 = 1)
    (hKn : Tendsto Kn atTop (𝓝 1)) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧
      TendstoLocallyUniformly (fun n => Fn (ns n)) id atTop := by
  obtain ⟨ns, hns, G, hlim⟩ := t203_lim_nf_extract
    (fun n => show IsKQCNormalizedPlane (Fn n) Kbar from
      ⟨(hqc n).mono (hbound n), hnorm n⟩)
  have hG := grp25b_normalized_limit (fun n => hqc (ns n))
    (fun n => hbound (ns n)) (fun n => hnorm (ns n))
    (hKn.comp hns.tendsto_atTop) hlim
  exact ⟨ns, hns, hG ▸ hlim⟩

/-- The first two jets of a quotient with Wronskian one. -/
theorem grp25b_ratio_jets {A B H : ℂ → ℂ} {D : Set ℂ} (hD : IsOpen D)
    (hA : DifferentiableOn ℂ A D) (hB : DifferentiableOn ℂ B D)
    (hW : ∀ y ∈ D, A y * deriv B y - B y * deriv A y = 1)
    (hH : ∀ y ∈ D, H y = A y / B y) (hne : ∀ y ∈ D, B y ≠ 0)
    {y : ℂ} (hy : y ∈ D) :
    deriv H y = -1 / B y ^ 2 ∧ deriv (deriv H) y = 2 * deriv B y / B y ^ 3 := by
  have hd : ∀ x ∈ D, HasDerivAt H (-1 / B x ^ 2) x := by
    intro x hx
    have hh := (hA.differentiableAt (hD.mem_nhds hx)).hasDerivAt.div
      (hB.differentiableAt (hD.mem_nhds hx)).hasDerivAt (hne x hx)
    have he : (deriv A x * B x - A x * deriv B x) / B x ^ 2 = -1 / B x ^ 2 := by
      congr 1
      linear_combination -(hW x hx)
    rw [he] at hh
    exact hh.congr_of_eventuallyEq (Filter.eventuallyEq_of_mem (hD.mem_nhds hx) (fun t ht => hH t ht))
  refine ⟨(hd y hy).deriv, ?_⟩
  have he : deriv H =ᶠ[𝓝 y] fun x => -1 / B x ^ 2 :=
    Filter.eventuallyEq_of_mem (hD.mem_nhds hy) (fun x hx => (hd x hx).deriv)
  rw [he.deriv_eq]
  have hh := (hasDerivAt_const y (-1 : ℂ)).div
    ((hB.differentiableAt (hD.mem_nhds hy)).hasDerivAt.pow 2) (pow_ne_zero 2 (hne y hy))
  change deriv ((fun _ : ℂ => (-1 : ℂ)) / B ^ 2) y = _
  rw [hh.deriv]
  simp only [Pi.pow_apply, Nat.cast_ofNat, Nat.reduceSub, pow_one, zero_mul, neg_mul, one_mul,
    zero_sub, neg_neg]
  field_simp [hne y hy]
  <;> ring

/-- The upper-half-plane AW derivative is determined by the two holomorphic
jets at the reflected point. This identity permits Cauchy convergence below
the real axis to control the real derivative above it. -/
theorem grp25b_aw_jet {A B H φ : ℂ → ℂ}
    (hA : DifferentiableOn ℂ A lowerHalf) (hB : DifferentiableOn ℂ B lowerHalf)
    (hode : ∀ y ∈ lowerHalf, deriv (deriv A) y + φ y / 2 * A y = 0 ∧
      deriv (deriv B) y + φ y / 2 * B y = 0 ∧ A y * deriv B y - B y * deriv A y = 1)
    (hlo : ∀ y ∈ lowerHalf, H y = A y / B y) (hne : ∀ y ∈ lowerHalf, B y ≠ 0)
    (hhi : ∀ z ∈ upperHalf, H z =
      (A (conj z) + (z - conj z) * deriv A (conj z)) /
        (B (conj z) + (z - conj z) * deriv B (conj z)))
    {z : ℂ} (hz : z ∈ upperHalf)
    (hden : B (conj z) + (z - conj z) * deriv B (conj z) ≠ 0) :
    dz H z = deriv H (conj z) /
      (1 - (z - conj z) * deriv (deriv H) (conj z) / (2 * deriv H (conj z))) ^ 2 := by
  have hy : conj z ∈ lowerHalf := by simpa [upperHalf, lowerHalf] using hz
  have hn := isOpen_lowerHalf.mem_nhds hy
  obtain ⟨a1, b1⟩ := t203_ode_hasDerivAt (a := φ (conj z) / 2)
    (hA.differentiableAt hn) ((hA.deriv isOpen_lowerHalf).differentiableAt hn)
    (hode _ hy).1
  obtain ⟨a2, b2⟩ := t203_ode_hasDerivAt (a := φ (conj z) / 2)
    (hB.differentiableAt hn) ((hB.deriv isOpen_lowerHalf).differentiableAt hn)
    (hode _ hy).2.1
  obtain ⟨hc, hcz, -⟩ := l333_mux_dz_conj z
  have hd := (t203_dz_dzbar_F hc a1 b1 a2 b2 (hode _ hy).2.2 hden).1
  have he : H =ᶠ[𝓝 z] fun w =>
      (A (conj w) + (w - conj w) * deriv A (conj w)) /
        (B (conj w) + (w - conj w) * deriv B (conj w)) :=
    Filter.eventuallyEq_of_mem (isOpen_upperHalf.mem_nhds hz) (fun w hw => hhi w hw)
  rw [(t203_c1_dz_congr he).1, hd, hcz]
  obtain ⟨h1, h2⟩ := grp25b_ratio_jets isOpen_lowerHalf hA hB
    (fun y hy => (hode y hy).2.2) hlo hne hy
  rw [h1, h2]
  have hb := hne _ hy
  have heq : 1 - (z - conj z) * (2 * deriv B (conj z) / B (conj z) ^ 3) /
      (2 * (-1 / B (conj z) ^ 2)) =
      (B (conj z) + (z - conj z) * deriv B (conj z)) / B (conj z) := by
    field_simp [hb]
    <;> ring
  rw [heq, div_pow, div_div]
  field_simp [hb, hden]
  <;> ring

/-- The jet identity survives the Mobius normalization used by the AW existence
proof. The determinant is absorbed into a Wronskian-one pair. -/
theorem grp25b_mobius_aw_jet {w₁ w₂ H φ : ℂ → ℂ} {a b c d : ℂ}
    (hdet : a * d - b * c ≠ 0)
    (hw₁ : DifferentiableOn ℂ w₁ lowerHalf) (hw₂ : DifferentiableOn ℂ w₂ lowerHalf)
    (hode : ∀ y ∈ lowerHalf, deriv (deriv w₁) y + φ y / 2 * w₁ y = 0 ∧
      deriv (deriv w₂) y + φ y / 2 * w₂ y = 0 ∧
      w₁ y * deriv w₂ y - w₂ y * deriv w₁ y = 1)
    (hlo : ∀ y ∈ lowerHalf, mobiusExt a b c d (t203_ratio (w₁ y) (w₂ y)) = (H y : ExtPlane))
    (hhi : ∀ z ∈ upperHalf, mobiusExt a b c d (l333_E w₁ w₂ z) = (H z : ExtPlane))
    {z : ℂ} (hz : z ∈ upperHalf) :
    dz H z = deriv H (conj z) /
      (1 - (z - conj z) * deriv (deriv H) (conj z) / (2 * deriv H (conj z))) ^ 2 := by
  obtain ⟨σ, hσ⟩ := IsAlgClosed.exists_pow_nat_eq (a * d - b * c) two_pos
  have hσ0 : σ ≠ 0 := by
    rintro rfl
    apply hdet
    rw [← hσ]
    ring
  have hdet' : a / σ * (d / σ) - b / σ * (c / σ) = 1 := by
    rw [div_mul_div_comm, div_mul_div_comm, ← sub_div, ← hσ, pow_two]
    exact div_self (mul_ne_zero hσ0 hσ0)
  let A : ℂ → ℂ := fun y => a / σ * w₁ y + b / σ * w₂ y
  let B : ℂ → ℂ := fun y => c / σ * w₁ y + d / σ * w₂ y
  have hA : DifferentiableOn ℂ A lowerHalf := (hw₁.const_mul _).add (hw₂.const_mul _)
  have hB : DifferentiableOn ℂ B lowerHalf := (hw₁.const_mul _).add (hw₂.const_mul _)
  have hAB : ∀ y ∈ lowerHalf, deriv (deriv A) y + φ y / 2 * A y = 0 ∧
      deriv (deriv B) y + φ y / 2 * B y = 0 ∧ A y * deriv B y - B y * deriv A y = 1 := by
    intro y hy
    obtain ⟨e1, e1'⟩ := t203_ode_comb_deriv isOpen_lowerHalf hw₁ hw₂ (a / σ) (b / σ) hy
    obtain ⟨e2, e2'⟩ := t203_ode_comb_deriv isOpen_lowerHalf hw₁ hw₂ (c / σ) (d / σ) hy
    obtain ⟨o1, o2, hw⟩ := hode y hy
    refine ⟨?_, ?_, ?_⟩
    · rw [show deriv (deriv A) y = _ from e1']
      dsimp [A]
      linear_combination (a / σ) * o1 + (b / σ) * o2
    · rw [show deriv (deriv B) y = _ from e2']
      dsimp [B]
      linear_combination (c / σ) * o1 + (d / σ) * o2
    · rw [show deriv A y = _ from e1, show deriv B y = _ from e2]
      exact (neh_wronskian_comb (a := a / σ) (b := b / σ) (c := c / σ) (d := d / σ) hw).trans hdet'
  have hlo' : ∀ y ∈ lowerHalf, (H y : ExtPlane) = t203_ratio (A y) (B y) := by
    intro y hy
    rw [← hlo y hy]
    have hpair : w₁ y ≠ 0 ∨ w₂ y ≠ 0 := by
      by_contra hh
      push_neg at hh
      have hw := (hode y hy).2.2
      simp [hh.1, hh.2] at hw
    exact t203_c1_mobius_ratio hσ0 hpair
  have hhi' : ∀ y ∈ upperHalf, (H y : ExtPlane) =
      t203_ratio (A (conj y) + (y - conj y) * deriv A (conj y))
        (B (conj y) + (y - conj y) * deriv B (conj y)) := by
    intro y hy
    have hyL : conj y ∈ lowerHalf := by simpa [upperHalf, lowerHalf] using hy
    obtain ⟨e1, -⟩ := t203_ode_comb_deriv isOpen_lowerHalf hw₁ hw₂ (a / σ) (b / σ) hyL
    obtain ⟨e2, -⟩ := t203_ode_comb_deriv isOpen_lowerHalf hw₁ hw₂ (c / σ) (d / σ) hyL
    rw [← hhi y hy, l333_E, t203_c1_mobius_ratio hσ0 (l333_mux_pair_ne (hode _ hyL).2.2)]
    rw [show deriv A (conj y) = _ from e1, show deriv B (conj y) = _ from e2]
    dsimp [A, B]
    congr 1 <;> ring
  have hBne : ∀ y ∈ lowerHalf, B y ≠ 0 := fun y hy =>
    t203_c1_ratio_ne ((hlo' y hy) ▸ OnePoint.coe_ne_infty (H y))
  have hDne : ∀ y ∈ upperHalf, B (conj y) + (y - conj y) * deriv B (conj y) ≠ 0 :=
    fun y hy => t203_c1_ratio_ne ((hhi' y hy) ▸ OnePoint.coe_ne_infty (H y))
  apply grp25b_aw_jet hA hB hAB _ hBne _ hz (hDne z hz)
  · intro y hy
    have hh := congrArg extToC (hlo' y hy)
    rwa [t203_c1_extToC_ratio (hBne y hy)] at hh
  · intro y hy
    have hh := congrArg extToC (hhi' y hy)
    rwa [t203_c1_extToC_ratio (hDne y hy)] at hh

/-- Quantitative AW existence retaining the exact distortion and the upper
jet formula, so no arbitrary choices of ODE solutions enter convergence. -/
theorem grp25b_core {φ : ℂ → ℂ} {s : ℝ} (hs0 : 0 ≤ s) (hs : s < 1 / 2)
    (hφd : DifferentiableOn ℂ φ lowerHalf) (hφ : ∀ z ∈ lowerHalf, ‖φ z‖ * z.im ^ 2 ≤ s) :
    ∃ H : ℂ → ℂ, IsKQC H univ ((1 + 4 * s / 2) / (1 - 4 * s / 2)) ∧
      H '' univ = univ ∧ H 0 = 0 ∧ H 1 = 1 ∧ DifferentiableOn ℂ H lowerHalf ∧
      (∀ z ∈ upperHalf, complexDilatation H z = -2 * (z.im : ℂ) ^ 2 * φ (conj z)) ∧
      (∀ z ∈ upperHalf, ContDiffAt ℝ 1 H z ∧ dz H z ≠ 0) ∧
      ∀ z ∈ upperHalf, dz H z = deriv H (conj z) /
        (1 - (z - conj z) * deriv (deriv H) (conj z) / (2 * deriv H (conj z))) ^ 2 := by
  obtain ⟨w₁, w₂, hw₁, hw₂, hode, hloc, hSf, hmero⟩ := l333_ode hφd
  obtain ⟨hfam, hconv⟩ := l333_family hs0 hs hφ hw₁ hw₂ hode
  obtain ⟨hdisc, hmono, hU⟩ := l333_disc_facts
  have hk0 : 0 ≤ 4 * s / 2 := by positivity
  have hk1 : 4 * s / 2 < 1 := by linarith
  obtain ⟨G, A, T, h, hA, hT, hh, hhs, hG, hGD, hGlim⟩ :=
    l333_limit (D := lowerHalf) (f := fun z => w₁ z / w₂ z) (Dn := l333_disc) (F := l333_F w₁ w₂)
      hk0 hk1 le_rfl ⟨-I, by simp [lowerHalf]⟩ isOpen_lowerHalf hmono (fun n => (hdisc n).2.1) hU
      fun n => ⟨(hfam n).1, (hfam n).2.1, fun z hz => ((hfam n).2.2.1 z hz).trans
        (hmero z ((hdisc n).2.2.2.1 (subset_closure hz))).symm, (hfam n).2.2.2⟩
  obtain ⟨α, β, κ, δ, hdet, H, hH, hHs, hH0, hH1, hM⟩ := l333_normalize hA hT hh hhs hG
  have hGv : ∀ v ∈ lowerHalf, mobiusExt α β κ δ (meroToExt (fun z => w₁ z / w₂ z) v) = (H v : ExtPlane) := by
    intro v hv
    rw [← hGD v hv, hM]
    rfl
  have hHE : ∀ y ∈ upperHalf, mobiusExt α β κ δ (l333_E w₁ w₂ y) = (H y : ExtPlane) := by
    intro y hy
    rw [← hGlim y _ (hconv y hy), hM]
    rfl
  refine ⟨H, hH, hHs, hH0, hH1,
    (fun v hv => (aw_ext_analyticAt isOpen_lowerHalf hloc hGv hv).differentiableAt.differentiableWithinAt),
    (fun z hz => l333_mu_exact hdet hw₁ hw₂ hode hHE hz),
    (fun z hz => grp_l333_reg hdet hw₁ hw₂ hode hHE hz), ?_⟩
  intro z hz
  exact grp25b_mobius_aw_jet hdet hw₁ hw₂ hode
    (fun y hy => by rw [← hmero y hy]; exact hGv y hy) hHE hz

/-- Holomorphic convergence below the real axis controls the AW derivative
at I via the explicit reflected jet formula. -/
theorem grp25b_aw_dz_tendsto {H : ℕ → ℂ → ℂ}
    (hhol : ∀ n, DifferentiableOn ℂ (H n) lowerHalf)
    (hlim : TendstoLocallyUniformly H id atTop)
    (hjet : ∀ n, dz (H n) I = deriv (H n) (conj I) /
      (1 - (I - conj I) * deriv (deriv (H n)) (conj I) / (2 * deriv (H n) (conj I))) ^ 2) :
    Tendsto (fun n => dz (H n) I) atTop (𝓝 1) := by
  have h1 := hlim.tendstoLocallyUniformlyOn.deriv (Eventually.of_forall hhol) isOpen_lowerHalf
  have h2 := h1.deriv (Eventually.of_forall (fun n => (hhol n).deriv isOpen_lowerHalf)) isOpen_lowerHalf
  have hy : conj I ∈ lowerHalf := by simp [lowerHalf]
  have hd1 : Tendsto (fun n => deriv (H n) (conj I)) atTop (𝓝 (1 : ℂ)) := by
    simpa using h1.tendsto_at hy
  have hd2 : Tendsto (fun n => deriv (deriv (H n)) (conj I)) atTop (𝓝 (0 : ℂ)) := by
    simpa using h2.tendsto_at hy
  have hden : Tendsto (fun n =>
      (1 - (I - conj I) * deriv (deriv (H n)) (conj I) / (2 * deriv (H n) (conj I))) ^ 2)
      atTop (𝓝 (1 : ℂ)) := by
    have hc1 : Tendsto (fun _ : ℕ => (1 : ℂ)) atTop (𝓝 1) := tendsto_const_nhds
    have hcu : Tendsto (fun _ : ℕ => I - conj I) atTop (𝓝 (I - conj I)) := tendsto_const_nhds
    have hc2 : Tendsto (fun _ : ℕ => (2 : ℂ)) atTop (𝓝 2) := tendsto_const_nhds
    have hh := (hc1.sub ((hcu.mul hd2).div (hc2.mul hd1)
      (by norm_num : (2 : ℂ) * 1 ≠ 0))).pow 2
    simpa using hh
  simpa only [div_one] using (hd1.div hden one_ne_zero).congr (fun n => (hjet n).symm)

end TakhtajanTeo

#print axioms TakhtajanTeo.grp25b_normalized_limit
#print axioms TakhtajanTeo.grp25b_normalized_subseq
#print axioms TakhtajanTeo.grp25b_ratio_jets
#print axioms TakhtajanTeo.grp25b_aw_jet
#print axioms TakhtajanTeo.grp25b_mobius_aw_jet
#print axioms TakhtajanTeo.grp25b_core
#print axioms TakhtajanTeo.grp25b_aw_dz_tendsto
