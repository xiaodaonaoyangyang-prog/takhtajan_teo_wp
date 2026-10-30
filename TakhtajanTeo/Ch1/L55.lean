import TakhtajanTeo.Ch2.S2_Mixed

/-!
# Lemma 5.5 (`l55_`, 下属3): the area identity (5.2) for a welding pair

Host: new module `TakhtajanTeo/Ch1/L55.lean`, importing `Ch2.S2_Mixed` (which imports `Ch1.S5_ChernForms`). The
target `l55_lemma_5_5` is `lemma_5_5` (S5) with the prefixed name and a byte-identical statement (relocated at round
end).

**Route** (TT:2333–2346: the area of `Ω = f(𝔻)` computed from both sides).
* `l55_disjoint_pair`: the welding gives a normalized disjoint pair, and `ℂ \ (f(𝔻) ∪ g(𝔻*)) = F(S¹)` is null.
  - `F`, `G` are homeomorphisms of `ℂ` with `G ∘ h = F` on `S¹` and `h(S¹) = S¹`, so `G(S¹) = F(S¹) = Γ`.
  - The connected unbounded set `G(𝔻*)` lies in `ℂ \ Γ = F(𝔻) ⊔ F(𝔻*)` (two open sets), so it lies in `F(𝔻*)`.
    Symmetrically `F(𝔻*) ⊆ G(𝔻*)`.
  - `Γ` is null: `ac_n_volume_image_null_of_isKQC` on the null circle.
* `Ch2.mg_gap_green` with `U = id` gives
  `area(gap_ρ) = -½ ∫ \bar f f' z dθ (|z| = ρ) + ½ ∫ \bar g g' z dθ (|z| = 1/ρ)`.
* `l55_f_energy`, `l55_g_energy` (via `Ch2.mg_circle_energy`, `mg_energy_split`) evaluate the two circle integrals:
  `2π Σ (n+1)|a_n|² ρ^{2n+2}` and `2π (|b₀|² R² - Σ m |b_{m+1}|² R^{-2m})`.
* `l55_gap_tendsto`: `area(gap_ρ) → 0` as `ρ → 1⁻` (the gaps decrease to the null set of `l55_disjoint_pair`).
* `l55_abel`: monotone (Abel) limits of the two nonnegative series, with the bound coming from `area ≥ 0`.
-/

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal ComplexConjugate Classical Real

noncomputable section

namespace TakhtajanTeo

open LiZhongQC Ch2

/-- A welding pair (CW1, CW2′, CW3′, CW4) of `h ∈ S¹\Homeo_qs(S¹)` is a normalized disjoint pair, and the
complement of `f(𝔻) ∪ g(𝔻*)` (the quasicircle `F(S¹)`) is null. -/
theorem l55_disjoint_pair {h f g : ℂ → ℂ} (hh : IsOneFixedQS h) (hw : IsWeldingPrime h f g) :
    IsNormalizedDisjointPair f g ∧ volume (f '' unitDisc ∪ g '' unitDiscExterior)ᶜ = 0 := by
  obtain ⟨⟨F, G, ⟨KF, hKF⟩, hFs, hFf, ⟨KG, hKG⟩, hGs, hGg, hFG⟩, hfd, hfi, hf0, hf1, hgu⟩ := hw
  -- a q.c. self-map of `ℂ` onto `ℂ` is a homeomorphism
  have hhom : ∀ (H : ℂ → ℂ) (K : ℝ), IsKQC H univ K → H '' univ = univ →
      Continuous H ∧ Function.Injective H ∧ Function.Surjective H ∧ ∀ U, IsOpen U → IsOpen (H '' U) := by
    intro H K hK hHs
    obtain ⟨hc, hi, -, hinv⟩ := hK.2.2.1
    have hHc : Continuous H := continuousOn_univ.mp hc
    have hHi : Function.Injective H := fun x y hxy => hi trivial trivial hxy
    have hHsj : Function.Surjective H := fun w => by
      have hw : w ∈ H '' univ := by rw [hHs]; trivial
      obtain ⟨z, -, hz⟩ := hw
      exact ⟨z, hz⟩
    refine ⟨hHc, hHi, hHsj, fun U hU => ?_⟩
    rw [hHs] at hinv
    have hic : Continuous (Function.invFunOn H univ) := continuousOn_univ.mp hinv
    have he : H '' U = Function.invFunOn H univ ⁻¹' U := by
      ext w
      constructor
      · rintro ⟨z, hz, rfl⟩
        show Function.invFunOn H univ (H z) ∈ U
        rw [hi.leftInvOn_invFunOn (mem_univ z)]
        exact hz
      · intro hw
        refine ⟨_, hw, ?_⟩
        obtain ⟨z, hz⟩ := hHsj w
        exact Function.invFunOn_eq (f := H) ⟨z, mem_univ z, hz⟩
    rw [he]
    exact hU.preimage hic
  obtain ⟨hFc, hFi, hFsj, hFo⟩ := hhom F KF hKF hFs
  obtain ⟨hGc, hGi, hGsj, hGo⟩ := hhom G KG hKG hGs
  -- `h` maps `S¹` onto `S¹`
  obtain ⟨u, huc, -, hu2, hu⟩ := hh.1.1
  have hexp : ∀ z ∈ unitCircle, z = exp ((arg z : ℂ) * I) := by
    intro z hz
    have hz1 : ‖z‖ = 1 := hz
    have := Complex.norm_mul_exp_arg_mul_I z
    rw [hz1] at this
    simpa using this.symm
  have hmaps : ∀ z ∈ unitCircle, h z ∈ unitCircle := by
    intro z hz
    rw [hexp z hz, hu]
    show ‖exp ((u (arg z) : ℂ) * I)‖ = 1
    exact Complex.norm_exp_ofReal_mul_I _
  have hshift : ∀ n : ℕ, u (2 * π * n) = u 0 + 2 * π * n ∧ u (-(2 * π * n)) = u 0 - 2 * π * n := by
    intro n
    induction n with
    | zero => simp
    | succ k ih =>
      push_cast
      constructor
      · have := hu2 (2 * π * k)
        rw [ih.1] at this
        rw [show 2 * π * ((k : ℝ) + 1) = 2 * π * k + 2 * π by ring, this]; ring
      · have := hu2 (-(2 * π * ((k : ℝ) + 1)))
        rw [show -(2 * π * ((k : ℝ) + 1)) + 2 * π = -(2 * π * k) by ring, ih.2] at this
        linarith
  have honto : ∀ w ∈ unitCircle, ∃ z ∈ unitCircle, h z = w := by
    intro w hw
    obtain ⟨N, hN⟩ := exists_nat_gt ((|arg w| + |u 0|) / (2 * π))
    have hN' : |arg w| + |u 0| < 2 * π * N := by
      rw [div_lt_iff₀ (by positivity)] at hN; linarith
    have hle : -(2 * π * N) ≤ 2 * π * N := by
      have : (0 : ℝ) ≤ 2 * π * N := by positivity
      linarith
    obtain ⟨t, -, ht⟩ := intermediate_value_Icc hle huc.continuousOn
      (show arg w ∈ Icc (u (-(2 * π * N))) (u (2 * π * N)) by
        rw [(hshift N).1, (hshift N).2]
        constructor <;> linarith [le_abs_self (arg w), neg_abs_le (arg w), le_abs_self (u 0), neg_abs_le (u 0)])
    refine ⟨exp ((t : ℂ) * I), Complex.norm_exp_ofReal_mul_I t, ?_⟩
    rw [hu, ht, ← hexp w hw]
  have hΓ : F '' unitCircle = G '' unitCircle := by
    ext w
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact ⟨h z, hmaps z hz, hFG z hz⟩
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨z, hz, rfl⟩ := honto y hy
      exact ⟨z, hz, (hFG z hz).symm⟩
  -- the three pieces of `ℂ`
  have htri : ∀ z : ℂ, z ∈ unitDisc ∨ z ∈ unitCircle ∨ z ∈ unitDiscExterior := by
    intro z
    rcases lt_trichotomy ‖z‖ 1 with h1 | h1 | h1
    · exact Or.inl (mem_ball_zero_iff.mpr h1)
    · exact Or.inr (Or.inl h1)
    · exact Or.inr (Or.inr h1)
  have hcb : ∀ z : ℂ, z ∈ unitDisc ∨ z ∈ unitCircle → z ∈ closedBall (0 : ℂ) 1 := by
    rintro z (hz | hz)
    · exact mem_closedBall_zero_iff.mpr (mem_ball_zero_iff.mp hz).le
    · exact mem_closedBall_zero_iff.mpr (le_of_eq hz)
  have hEo : IsOpen unitDiscExterior := isOpen_lt continuous_const continuous_norm
  have hEc : IsPreconnected unitDiscExterior := isPreconnected_setOf_lt_norm zero_le_one
  -- for two homeomorphisms with the same image of `S¹`, the exterior images agree
  have side : ∀ A B : ℂ → ℂ, Continuous A → Function.Injective A → Function.Surjective A →
      (∀ U, IsOpen U → IsOpen (A '' U)) → Continuous B → Function.Injective B → Function.Surjective B →
      A '' unitCircle = B '' unitCircle → B '' unitDiscExterior ⊆ A '' unitDiscExterior := by
    intro A B hAc hAi hAs hAo hBc hBi hBs hAB
    have hsub : B '' unitDiscExterior ⊆ A '' unitDisc ∪ A '' unitDiscExterior := by
      rintro w ⟨z, hz, rfl⟩
      obtain ⟨y, hy'⟩ := hAs (B z)
      rw [← hy']
      rcases htri y with hy | hy | hy
      · exact Or.inl ⟨y, hy, rfl⟩
      · exfalso
        have : A y ∈ B '' unitCircle := hAB ▸ ⟨y, hy, rfl⟩
        obtain ⟨x, hx, hxy⟩ := this
        have hxz : x = z := hBi (hxy.trans hy')
        rw [hxz] at hx
        have h1 : ‖z‖ = 1 := hx
        have h2 : 1 < ‖z‖ := hz
        linarith
      · exact Or.inr ⟨y, hy, rfl⟩
    have hdisjA : Disjoint (A '' unitDisc) (A '' unitDiscExterior) := by
      rw [Set.disjoint_left]
      rintro w ⟨x, hx, rfl⟩ ⟨y, hy, hxy⟩
      have := hAi hxy
      rw [this] at hy
      have h1 : ‖x‖ < 1 := mem_ball_zero_iff.mp hx
      have h2 : 1 < ‖x‖ := hy
      linarith
    rcases (hEc.image B hBc.continuousOn).subset_or_subset (hAo _ isOpen_ball) (hAo _ hEo) hdisjA hsub
      with hcase | hcase
    · exfalso
      have hAb : Bornology.IsBounded (A '' unitDisc) :=
        ((isCompact_closedBall (0 : ℂ) 1).image hAc).isBounded.subset
          (image_mono (fun z hz => hcb z (Or.inl hz)))
      have hBb : Bornology.IsBounded (B '' closedBall (0 : ℂ) 1) :=
        ((isCompact_closedBall (0 : ℂ) 1).image hBc).isBounded
      have huniv : (univ : Set ℂ) ⊆ B '' closedBall (0 : ℂ) 1 ∪ A '' unitDisc := by
        intro w _
        obtain ⟨z, rfl⟩ := hBs w
        rcases htri z with hz | hz | hz
        · exact Or.inl ⟨z, hcb z (Or.inl hz), rfl⟩
        · exact Or.inl ⟨z, hcb z (Or.inr hz), rfl⟩
        · exact Or.inr (hcase ⟨z, hz, rfl⟩)
      exact NormedSpace.unbounded_univ ℝ ℂ ((hBb.union hAb).subset huniv)
    · exact hcase
  have hGF := side F G hFc hFi hFsj hFo hGc hGi hGsj hΓ
  have hFG' := side G F hGc hGi hGsj hGo hFc hFi hFsj hΓ.symm
  have hfimg : f '' unitDisc = F '' unitDisc := (image_congr hFf).symm
  have hgimg : g '' unitDiscExterior = F '' unitDiscExterior := by
    rw [← image_congr hGg]; exact hGF.antisymm hFG'
  refine ⟨⟨hfd, hfi, hf0, hf1, hgu, ?_⟩, ?_⟩
  · rw [hfimg, hgimg, Set.disjoint_left]
    rintro w ⟨x, hx, rfl⟩ ⟨y, hy, hxy⟩
    have := hFi hxy
    rw [this] at hy
    have h1 : ‖x‖ < 1 := mem_ball_zero_iff.mp hx
    have h2 : 1 < ‖x‖ := hy
    linarith
  · have hsub : (f '' unitDisc ∪ g '' unitDiscExterior)ᶜ ⊆ F '' unitCircle := by
      intro w hw
      obtain ⟨z, rfl⟩ := hFsj w
      rcases htri z with hz | hz | hz
      · exact absurd (Or.inl (hfimg ▸ ⟨z, hz, rfl⟩)) hw
      · exact ⟨z, hz, rfl⟩
      · exact absurd (Or.inr (hgimg ▸ ⟨z, hz, rfl⟩)) hw
    have hS : volume unitCircle = 0 := by
      have : unitCircle = sphere (0 : ℂ) 1 := by ext z; simp [unitCircle]
      rw [this]; exact Measure.addHaar_sphere volume 0 1
    exact measure_mono_null hsub (ac_n_volume_image_null_of_isKQC hKF (subset_univ _) hS)

/-- The `f`-side circle energy: `∫ \bar f f' z dθ = 2π Σ (n+1)|a_n|² ρ^{2n+2}` on `|z| = ρ < 1`. -/
theorem l55_f_energy {f : ℂ → ℂ} {a : ℕ → ℂ} (ha : ∀ z ∈ unitDisc, HasSum (fun n => a n * z ^ (n + 1)) (f z))
    {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) :
    Summable (fun n : ℕ => ((n + 1 : ℕ) : ℝ) * (‖a n‖ ^ 2 * ρ ^ (2 * (n + 1)))) ∧
      (∫ θ in (0 : ℝ)..2 * π, conj (f (circleMap 0 ρ θ)) * deriv f (circleMap 0 ρ θ) * circleMap 0 ρ θ) =
        2 * π * ((∑' n : ℕ, ((n + 1 : ℕ) : ℝ) * (‖a n‖ ^ 2 * ρ ^ (2 * (n + 1))) : ℝ) : ℂ) := by
  set d : ℤ → ℂ := fun n => if 1 ≤ n then a (n - 1).toNat else 0 with hd
  obtain ⟨r1, hr1⟩ : ∃ r1 : ℝ, r1 = ρ / 2 := ⟨_, rfl⟩
  obtain ⟨r2, hr2⟩ : ∃ r2 : ℝ, r2 = (ρ + 1) / 2 := ⟨_, rfl⟩
  have hr1p : 0 < r1 := by rw [hr1]; positivity
  have hr1ρ : r1 < ρ := by rw [hr1]; linarith
  have hρr2 : ρ < r2 := by rw [hr2]; linarith
  have hr2one : r2 < 1 := by rw [hr2]; linarith
  have hdpos : ∀ n : ℕ, d ((n + 1 : ℕ) : ℤ) = a n := fun n => by
    simp only [hd]; rw [ite_eq_left_of_eq_true _ _ (eq_true (by omega))]; congr 1; omega
  have hd0 : d 0 = 0 := by simp [hd]
  have hdneg : ∀ n : ℕ, d (-((n : ℤ) + 1)) = 0 := fun n => by
    simp only [hd]; rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega))]
  have hLaurent : ∀ w : ℂ, r1 < ‖w‖ → ‖w‖ < r2 → f w = ∑' n : ℤ, d n * w ^ n := by
    intro w _ hw2
    have hwD : w ∈ unitDisc := mem_ball_zero_iff.mpr (hw2.trans hr2one)
    have hpos : HasSum (fun n : ℕ => d (n : ℤ) * w ^ (n : ℤ)) (f w) := by
      rw [← hasSum_nat_add_iff' 1]
      simp only [Finset.sum_range_one, Nat.cast_zero, hd0, zero_mul, sub_zero]
      refine (ha w hwD).congr_fun (fun n => ?_)
      rw [hdpos n, zpow_natCast]
    have hneg : HasSum (fun n : ℕ => d (-((n : ℤ) + 1)) * w ^ (-((n : ℤ) + 1))) 0 := by
      simp only [hdneg, zero_mul]; exact hasSum_zero
    simpa only [add_zero] using (HasSum.of_nat_of_neg_add_one (f := fun n : ℤ => d n * w ^ n) hpos hneg).tsum_eq.symm
  have hpos : Summable (fun n : ℕ => ‖d n‖ * r2 ^ n) := by
    have hr2D : ((r2 : ℝ) : ℂ) ∈ unitDisc :=
      mem_ball_zero_iff.mpr (by rw [Complex.norm_real, Real.norm_of_nonneg (by linarith)]; exact hr2one)
    have hn := summable_norm_iff.mpr (ha _ hr2D).summable
    rw [← summable_nat_add_iff 1]
    refine hn.congr (fun j => ?_)
    simp only [Nat.cast_add, Nat.cast_one]
    rw [show ((j : ℤ) + 1) = (((j + 1 : ℕ)) : ℤ) by push_cast; ring, hdpos, norm_mul, norm_pow,
      Complex.norm_real, Real.norm_of_nonneg (by linarith)]
  have hneg : Summable (fun n : ℕ => ‖d (-(n : ℤ))‖ * (r1 ^ n)⁻¹) := by
    refine summable_of_ne_finset_zero (s := ∅) (fun n _ => ?_)
    have : d (-(n : ℤ)) = 0 := by simp only [hd]; rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega))]
    rw [this, norm_zero, zero_mul]
  have hE := mg_circle_energy (H := f) d hr1p hr1ρ hρr2 hpos hneg hLaurent
  obtain ⟨-, hTc⟩ := mg_energy_real hr1p hr1ρ hρr2 hpos hneg
  obtain ⟨hsp, -, hsplit⟩ := mg_energy_split hr1p hr1ρ hρr2 hpos hneg
  have e1 : (fun j : ℕ => ((j + 1 : ℕ) : ℝ) * (‖d ((j + 1 : ℕ) : ℤ)‖ ^ 2 * ρ ^ (2 * (j + 1)))) =
      fun j : ℕ => ((j + 1 : ℕ) : ℝ) * (‖a j‖ ^ 2 * ρ ^ (2 * (j + 1))) := by
    funext j; rw [hdpos]
  rw [e1] at hsp
  refine ⟨hsp, ?_⟩
  rw [hE, hTc, hsplit, e1]
  have hz : (∑' k : ℕ, ((k + 1 : ℕ) : ℝ) * (‖d (-((k + 1 : ℕ) : ℤ))‖ ^ 2 * (ρ ^ (2 * (k + 1)))⁻¹)) = 0 := by
    refine (tsum_congr (fun k => ?_)).trans tsum_zero
    rw [show (-((k + 1 : ℕ) : ℤ)) = -((k : ℤ) + 1) by push_cast; ring, hdneg]; simp
  rw [hz, sub_zero]

/-- The `g`-side circle energy: `∫ \bar g g' z dθ = 2π (|b₀|² R² - Σ m |b_{m+1}|² R^{-2m})` on `|z| = R > 1`. -/
theorem l55_g_energy {g : ℂ → ℂ} {b : ℕ → ℂ}
    (hb : ∀ z ∈ unitDiscExterior, HasSum (fun n : ℕ => b n * z ^ (1 - (n : ℤ))) (g z)) {R : ℝ} (hR : 1 < R) :
    Summable (fun m : ℕ => (m : ℝ) * (‖b (m + 1)‖ ^ 2 * (R ^ (2 * m))⁻¹)) ∧
      (∫ θ in (0 : ℝ)..2 * π, conj (g (circleMap 0 R θ)) * deriv g (circleMap 0 R θ) * circleMap 0 R θ) =
        2 * π * ((‖b 0‖ ^ 2 * R ^ 2 - ∑' m : ℕ, (m : ℝ) * (‖b (m + 1)‖ ^ 2 * (R ^ (2 * m))⁻¹) : ℝ) : ℂ) := by
  set d : ℤ → ℂ := fun n => if n ≤ 1 then b (1 - n).toNat else 0 with hd
  obtain ⟨r1, hr1⟩ : ∃ r1 : ℝ, r1 = (R + 1) / 2 := ⟨_, rfl⟩
  obtain ⟨r2, hr2⟩ : ∃ r2 : ℝ, r2 = R + 1 := ⟨_, rfl⟩
  have hr1p : 0 < r1 := by rw [hr1]; linarith
  have hr1one : 1 < r1 := by rw [hr1]; linarith
  have hr1R : r1 < R := by rw [hr1]; linarith
  have hRr2 : R < r2 := by rw [hr2]; linarith
  have hdk : ∀ k : ℕ, d (1 - (k : ℤ)) = b k := fun k => by
    simp only [hd]; rw [ite_eq_left_of_eq_true _ _ (eq_true (by omega))]; congr 1; omega
  have hdbig : ∀ n : ℤ, 2 ≤ n → d n = 0 := fun n hn => by
    simp only [hd]; rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega))]
  have hLaurent : ∀ w : ℂ, r1 < ‖w‖ → ‖w‖ < r2 → g w = ∑' n : ℤ, d n * w ^ n := by
    intro w hw1 _
    have hwE : w ∈ unitDiscExterior := show 1 < ‖w‖ by linarith
    have hinj : Function.Injective (fun k : ℕ => (1 - (k : ℤ))) := by
      intro x y hxy; simp only at hxy; omega
    have hsupp : ∀ n ∉ Set.range (fun k : ℕ => (1 - (k : ℤ))), d n * w ^ n = 0 := by
      intro n hn
      have h2 : 2 ≤ n := by
        by_contra hlt
        exact hn ⟨(1 - n).toNat, by simp only; omega⟩
      rw [hdbig n h2, zero_mul]
    have hS : HasSum (fun n : ℤ => d n * w ^ n) (g w) := by
      rw [← hinj.hasSum_iff hsupp]
      refine (hb w hwE).congr_fun (fun k => ?_)
      simp only [Function.comp, hdk]
    exact hS.tsum_eq.symm
  have hpos : Summable (fun n : ℕ => ‖d n‖ * r2 ^ n) := by
    refine summable_of_ne_finset_zero (s := Finset.range 2) (fun n hn => ?_)
    have hn' : 2 ≤ n := by simp at hn; omega
    rw [hdbig n (by exact_mod_cast hn'), norm_zero, zero_mul]
  have hneg : Summable (fun n : ℕ => ‖d (-(n : ℤ))‖ * (r1 ^ n)⁻¹) := by
    have hr1E : ((r1 : ℝ) : ℂ) ∈ unitDiscExterior := by
      show 1 < ‖((r1 : ℝ) : ℂ)‖
      rw [Complex.norm_real, Real.norm_of_nonneg (by linarith)]; exact hr1one
    have hn := summable_norm_iff.mpr (hb _ hr1E).summable
    rw [← summable_nat_add_iff 1] at hn
    refine hn.congr (fun n => ?_)
    rw [show (-(n : ℤ)) = 1 - ((n + 1 : ℕ) : ℤ) by push_cast; ring, hdk, norm_mul, norm_zpow,
      Complex.norm_real, Real.norm_of_nonneg (by linarith),
      show (1 - ((n + 1 : ℕ) : ℤ)) = -(n : ℤ) by push_cast; ring, zpow_neg, zpow_natCast]
  have hE := mg_circle_energy (H := g) d hr1p hr1R hRr2 hpos hneg hLaurent
  obtain ⟨-, hTc⟩ := mg_energy_real hr1p hr1R hRr2 hpos hneg
  obtain ⟨-, hsn, hsplit⟩ := mg_energy_split hr1p hr1R hRr2 hpos hneg
  have hP : (∑' j : ℕ, ((j + 1 : ℕ) : ℝ) * (‖d ((j + 1 : ℕ) : ℤ)‖ ^ 2 * R ^ (2 * (j + 1)))) = ‖b 0‖ ^ 2 * R ^ 2 := by
    rw [tsum_eq_single 0]
    · rw [show (((0 + 1 : ℕ)) : ℤ) = 1 - ((0 : ℕ) : ℤ) by norm_num, hdk]; simp
    · intro j hj
      rw [hdbig _ (by omega)]; simp
  have eN : ∀ k : ℕ, ((k + 1 : ℕ) : ℝ) * (‖d (-((k + 1 : ℕ) : ℤ))‖ ^ 2 * (R ^ (2 * (k + 1)))⁻¹) =
      (fun m : ℕ => (m : ℝ) * (‖b (m + 1)‖ ^ 2 * (R ^ (2 * m))⁻¹)) (k + 1) := by
    intro k
    rw [show (-((k + 1 : ℕ) : ℤ)) = 1 - ((k + 2 : ℕ) : ℤ) by push_cast; ring, hdk]
  have hsn' : Summable (fun m : ℕ => (m : ℝ) * (‖b (m + 1)‖ ^ 2 * (R ^ (2 * m))⁻¹)) := by
    rw [← summable_nat_add_iff 1]
    exact hsn.congr eN
  refine ⟨hsn', ?_⟩
  rw [hE, hTc, hsplit, hP, tsum_congr eN, hsn'.tsum_eq_zero_add]
  simp

/-- The gap areas tend to `0` as `ρ → 1⁻` when `ℂ \ (f(𝔻) ∪ g(𝔻*))` is null. -/
theorem l55_gap_tendsto {f g : ℂ → ℂ} (h : IsNormalizedDisjointPair f g)
    (hnull : volume (f '' unitDisc ∪ g '' unitDiscExterior)ᶜ = 0) :
    Tendsto (fun ρ : ℝ => ∫ w in (f '' closedBall (0 : ℂ) ρ ∪ g '' {z : ℂ | 1 / ρ ≤ ‖z‖})ᶜ,
      ‖deriv (fun w : ℂ => w) w‖ ^ 2) (𝓝[<] 1) (𝓝 0) := by
  obtain ⟨r, hr, hmono, hlim⟩ := mg_radius_seq
  have hseq := mg_gap_integral_tendsto h hnull (U := fun w : ℂ => w) differentiableOn_id hr hmono hlim
  set S : ℝ → Set ℂ := fun ρ => (f '' closedBall (0 : ℂ) ρ ∪ g '' {z : ℂ | 1 / ρ ≤ ‖z‖})ᶜ with hS
  have hderiv : ∀ w : ℂ, ‖deriv (fun w : ℂ => w) w‖ ^ 2 = 1 := by intro w; simp
  have hA : ∀ ρ : ℝ, (∫ w in S ρ, ‖deriv (fun w : ℂ => w) w‖ ^ 2) = volume.real (S ρ) := by
    intro ρ; simp only [hderiv, setIntegral_const, smul_eq_mul, mul_one]
  have hfin : ∀ ρ : ℝ, 0 < ρ → ρ < 1 → volume (S ρ) ≠ ∞ := by
    intro ρ hρ0 hρ1
    obtain ⟨R1, hR1⟩ := mg_far_exterior h (T := 1 / ρ) (by positivity)
    refine ((measure_mono (fun w hw => ?_)).trans_lt
      (measure_closedBall_lt_top (x := (0 : ℂ)) (r := |R1|))).ne
    rw [mem_closedBall_zero_iff]
    by_contra hnot
    obtain ⟨z, hz, hzw⟩ := hR1 w (lt_of_le_of_lt (le_abs_self R1) (not_le.mp hnot))
    exact hw (Or.inr ⟨z, hz, hzw⟩)
  have hanti : ∀ ρ ρ' : ℝ, 0 < ρ → ρ ≤ ρ' → S ρ' ⊆ S ρ := by
    intro ρ ρ' hρ0 hle w hw hwb
    apply hw
    rcases hwb with ⟨z, hz, rfl⟩ | ⟨z, hz, rfl⟩
    · exact Or.inl ⟨z, closedBall_subset_closedBall hle hz, rfl⟩
    · refine Or.inr ⟨z, ?_, rfl⟩
      exact le_trans (one_div_le_one_div_of_le hρ0 hle) hz
  rw [tendsto_order]
  constructor
  · intro a ha
    exact Eventually.of_forall (fun ρ => by
      show a < ∫ w in S ρ, ‖deriv (fun w : ℂ => w) w‖ ^ 2
      rw [hA]; exact lt_of_lt_of_le ha measureReal_nonneg)
  · intro a ha
    obtain ⟨n, hn⟩ := (hseq.eventually (gt_mem_nhds ha)).exists
    filter_upwards [Ioo_mem_nhdsLT (hr n).2] with ρ hρ
    show (∫ w in S ρ, ‖deriv (fun w : ℂ => w) w‖ ^ 2) < a
    have hn' : (∫ w in S (r n), ‖deriv (fun w : ℂ => w) w‖ ^ 2) < a := hn
    rw [hA] at hn' ⊢
    exact lt_of_le_of_lt (measureReal_mono (hanti _ _ (hr n).1 hρ.1.le) (hfin _ (hr n).1 (hr n).2)) hn'

/-- Abel limit of a nonnegative power series in `ρ²` bounded on `(1/2, 1)`. -/
theorem l55_abel {c : ℕ → ℝ} (hc : ∀ n, 0 ≤ c n) {M : ℝ}
    (hM : ∀ ρ ∈ Ioo (1 / 2 : ℝ) 1, Summable (fun n => c n * ρ ^ (2 * n)) ∧ ∑' n, c n * ρ ^ (2 * n) ≤ M) :
    Summable c ∧ Tendsto (fun ρ : ℝ => ∑' n, c n * ρ ^ (2 * n)) (𝓝[<] 1) (𝓝 (∑' n, c n)) := by
  have hpart : ∀ N : ℕ, ∑ i ∈ Finset.range N, c i ≤ M := by
    intro N
    have hlim : Tendsto (fun ρ : ℝ => ∑ i ∈ Finset.range N, c i * ρ ^ (2 * i)) (𝓝[<] 1)
        (𝓝 (∑ i ∈ Finset.range N, c i * 1 ^ (2 * i))) := by
      have : Continuous (fun ρ : ℝ => ∑ i ∈ Finset.range N, c i * ρ ^ (2 * i)) := by fun_prop
      exact (this.tendsto 1).mono_left nhdsWithin_le_nhds
    simp only [one_pow, mul_one] at hlim
    refine le_of_tendsto hlim ?_
    filter_upwards [Ioo_mem_nhdsLT (by norm_num : (1 / 2 : ℝ) < 1)] with ρ hρ
    obtain ⟨hs, hle⟩ := hM ρ hρ
    have hρ0 : 0 ≤ ρ := by linarith [hρ.1]
    exact (hs.sum_le_tsum _ (fun i _ => mul_nonneg (hc i) (pow_nonneg hρ0 _))).trans hle
  have hsum : Summable c := summable_of_sum_range_le hc hpart
  refine ⟨hsum, ?_⟩
  have hab := Real.tendsto_tsum_powerSeries_nhdsWithin_lt (f := c) hsum.hasSum.tendsto_sum_nat
  have hsq : Tendsto (fun ρ : ℝ => ρ ^ 2) (𝓝[<] (1 : ℝ)) (𝓝[<] 1) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have : Tendsto (fun ρ : ℝ => ρ ^ 2) (𝓝 (1 : ℝ)) (𝓝 (1 ^ 2)) := (continuous_pow 2).tendsto 1
      simpa using this.mono_left nhdsWithin_le_nhds
    · filter_upwards [Ioo_mem_nhdsLT (by norm_num : (0 : ℝ) < 1)] with ρ hρ
      simp only [mem_Iio]
      nlinarith [hρ.1, hρ.2]
  refine (hab.comp hsq).congr (fun ρ => ?_)
  simp only [Function.comp, pow_mul]

/-- **Lemma 5.5** (TT:2328–2331). Let `𝗀 = g⁻¹ ∘ f` with welding CW1, CW2′, CW3′, CW4.
- Expansions: `f(z) = Σ_{n ≥ 0} a_n z^{n+1}` on `𝔻` with `a₀ = 1`, and `g(z) = Σ_{n ≥ 0} b_n z^{1-n}` on `𝔻*`.
- **(5.2)** `|b₀|² = Σ_{n ≥ 0} (n + 1)|a_n|² + Σ_{n ≥ 1} (n - 1)|b_n|²`.
- **[CORRECTION 2026-10-26]** The second sum is written as `Σ_{m ≥ 0} m |b_{m+1}|²`; the former `Σ_{n ≥ 0} (n - 1)|b_n|²`
  added the spurious term `-|b₀|²` (found by 下属2). -/
theorem l55_lemma_5_5 {h f g : ℂ → ℂ} (hh : IsOneFixedQS h) (hw : IsWeldingPrime h f g) {a b : ℕ → ℂ}
    (ha : ∀ z ∈ unitDisc, HasSum (fun n => a n * z ^ (n + 1)) (f z))
    (hb : ∀ z ∈ unitDiscExterior, HasSum (fun n : ℕ => b n * z ^ (1 - (n : ℤ))) (g z)) :
    ‖b 0‖ ^ 2 = (∑' n : ℕ, ((n + 1 : ℕ) : ℝ) * ‖a n‖ ^ 2) + ∑' n : ℕ, (n : ℝ) * ‖b (n + 1)‖ ^ 2 := by
  obtain ⟨hpair, hnull⟩ := l55_disjoint_pair hh hw
  set c : ℕ → ℝ := fun n => ((n + 1 : ℕ) : ℝ) * ‖a n‖ ^ 2 with hc
  set d : ℕ → ℝ := fun m => (m : ℝ) * ‖b (m + 1)‖ ^ 2 with hd
  set S : ℝ → Set ℂ := fun ρ => (f '' closedBall (0 : ℂ) ρ ∪ g '' {z : ℂ | 1 / ρ ≤ ‖z‖})ᶜ with hS
  set A : ℝ → ℝ := fun ρ => ∫ w in S ρ, ‖deriv (fun w : ℂ => w) w‖ ^ 2 with hA
  have hc0 : ∀ n, 0 ≤ c n := fun n => by positivity
  have hd0 : ∀ n, 0 ≤ d n := fun n => by positivity
  -- the gap identity at every radius
  have key : ∀ ρ : ℝ, 0 < ρ → ρ < 1 →
      Summable (fun n => c n * ρ ^ (2 * n)) ∧ Summable (fun n => d n * ρ ^ (2 * n)) ∧
        A ρ = π * (‖b 0‖ ^ 2 * (ρ ^ 2)⁻¹ - ∑' n, d n * ρ ^ (2 * n)) - π * (ρ ^ 2 * ∑' n, c n * ρ ^ (2 * n)) := by
    intro ρ hρ0 hρ1
    have hR : 1 < 1 / ρ := one_lt_one_div hρ0 hρ1
    obtain ⟨hfs, hfe⟩ := l55_f_energy ha hρ0 hρ1
    obtain ⟨hgs, hge⟩ := l55_g_energy hb hR
    have hG := mg_gap_green hpair hρ0 hρ1 (U := fun w : ℂ => w) differentiableOn_id
    have ef : ∀ n : ℕ, ((n + 1 : ℕ) : ℝ) * (‖a n‖ ^ 2 * ρ ^ (2 * (n + 1))) = ρ ^ 2 * (c n * ρ ^ (2 * n)) := by
      intro n; simp only [hc]; ring
    have eg : ∀ m : ℕ, (m : ℝ) * (‖b (m + 1)‖ ^ 2 * ((1 / ρ) ^ (2 * m))⁻¹) = d m * ρ ^ (2 * m) := by
      intro m; simp only [hd, one_div, inv_pow, inv_inv]; ring
    have hcs : Summable (fun n => c n * ρ ^ (2 * n)) := by
      have := hfs.mul_left (ρ ^ 2)⁻¹
      refine this.congr (fun n => ?_)
      rw [ef n]; field_simp
    have hds : Summable (fun n => d n * ρ ^ (2 * n)) := hgs.congr eg
    refine ⟨hcs, hds, ?_⟩
    simp only [funext ef, funext eg, tsum_mul_left] at hfe hge
    simp only [hfe, hge] at hG
    have hR2 : (1 / ρ) ^ 2 = (ρ ^ 2)⁻¹ := by rw [one_div, inv_pow]
    rw [hR2] at hG
    have hG' : ((A ρ : ℝ) : ℂ) = ((π * (‖b 0‖ ^ 2 * (ρ ^ 2)⁻¹ - ∑' n, d n * ρ ^ (2 * n)) -
        π * (ρ ^ 2 * ∑' n, c n * ρ ^ (2 * n)) : ℝ) : ℂ) := by
      rw [show ((A ρ : ℝ) : ℂ) = _ from hG]
      push_cast
      ring
    exact_mod_cast hG'
  -- bounds from `A ≥ 0`
  have hA0 : ∀ ρ, 0 ≤ A ρ := fun ρ => setIntegral_nonneg_of_ae (ae_of_all _ (fun w => by positivity))
  have hbound : ∀ ρ ∈ Ioo (1 / 2 : ℝ) 1,
      ∑' n, d n * ρ ^ (2 * n) + ρ ^ 2 * ∑' n, c n * ρ ^ (2 * n) ≤ 4 * ‖b 0‖ ^ 2 := by
    rintro ρ ⟨hρ0, hρ1⟩
    obtain ⟨-, -, hk⟩ := key ρ (by linarith) hρ1
    have h1 := hA0 ρ
    rw [hk] at h1
    have hρ2 : (ρ ^ 2)⁻¹ ≤ 4 := by
      rw [inv_le_comm₀ (by positivity) (by norm_num)]; nlinarith
    have := mul_le_mul_of_nonneg_left hρ2 (sq_nonneg ‖b 0‖)
    nlinarith [Real.pi_pos]
  have hdM : ∀ ρ ∈ Ioo (1 / 2 : ℝ) 1, Summable (fun n => d n * ρ ^ (2 * n)) ∧
      ∑' n, d n * ρ ^ (2 * n) ≤ 4 * ‖b 0‖ ^ 2 := by
    intro ρ hρ
    obtain ⟨-, hds, -⟩ := key ρ (by linarith [hρ.1]) hρ.2
    refine ⟨hds, ?_⟩
    have := hbound ρ hρ
    have : 0 ≤ ρ ^ 2 * ∑' n, c n * ρ ^ (2 * n) :=
      mul_nonneg (by positivity) (tsum_nonneg (fun n => mul_nonneg (hc0 n) (pow_nonneg (by linarith [hρ.1]) _)))
    linarith
  have hcM : ∀ ρ ∈ Ioo (1 / 2 : ℝ) 1, Summable (fun n => c n * ρ ^ (2 * n)) ∧
      ∑' n, c n * ρ ^ (2 * n) ≤ 16 * ‖b 0‖ ^ 2 := by
    intro ρ hρ
    obtain ⟨hcs, -, -⟩ := key ρ (by linarith [hρ.1]) hρ.2
    refine ⟨hcs, ?_⟩
    have hb4 := hbound ρ hρ
    have hdn : 0 ≤ ∑' n, d n * ρ ^ (2 * n) := tsum_nonneg (fun n => mul_nonneg (hd0 n) (pow_nonneg (by linarith [hρ.1]) _))
    have hcn : 0 ≤ ∑' n, c n * ρ ^ (2 * n) := tsum_nonneg (fun n => mul_nonneg (hc0 n) (pow_nonneg (by linarith [hρ.1]) _))
    have hρ2 : 1 / 4 ≤ ρ ^ 2 := by nlinarith [hρ.1]
    nlinarith
  obtain ⟨-, hcl⟩ := l55_abel hc0 hcM
  obtain ⟨-, hdl⟩ := l55_abel hd0 hdM
  -- pass to the limit `ρ → 1⁻`
  have hev : ∀ᶠ ρ in 𝓝[<] (1 : ℝ), A ρ =
      π * (‖b 0‖ ^ 2 * (ρ ^ 2)⁻¹ - ∑' n, d n * ρ ^ (2 * n)) - π * (ρ ^ 2 * ∑' n, c n * ρ ^ (2 * n)) := by
    filter_upwards [Ioo_mem_nhdsLT (by norm_num : (0 : ℝ) < 1)] with ρ hρ
    exact (key ρ hρ.1 hρ.2).2.2
  have hρc : Tendsto (fun ρ : ℝ => ρ ^ 2) (𝓝[<] (1 : ℝ)) (𝓝 1) := by
    have : Tendsto (fun ρ : ℝ => ρ ^ 2) (𝓝 (1 : ℝ)) (𝓝 (1 ^ 2)) := (continuous_pow 2).tendsto 1
    simpa using this.mono_left nhdsWithin_le_nhds
  have hρi : Tendsto (fun ρ : ℝ => (ρ ^ 2)⁻¹) (𝓝[<] (1 : ℝ)) (𝓝 1) := by
    simpa using hρc.inv₀ one_ne_zero
  have hlim : Tendsto A (𝓝[<] (1 : ℝ))
      (𝓝 (π * (‖b 0‖ ^ 2 * 1 - ∑' n, d n) - π * (1 * ∑' n, c n))) := by
    refine Tendsto.congr' (EventuallyEq.symm hev) ?_
    exact ((tendsto_const_nhds.mul ((tendsto_const_nhds.mul hρi).sub hdl)).sub
      (tendsto_const_nhds.mul (hρc.mul hcl)))
  have h0 := tendsto_nhds_unique hlim (l55_gap_tendsto hpair hnull)
  have hπ : π ≠ 0 := Real.pi_ne_zero
  have : ‖b 0‖ ^ 2 - ∑' n, d n - ∑' n, c n = 0 := by
    have h1 : π * (‖b 0‖ ^ 2 - ∑' n, d n - ∑' n, c n) = 0 := by linear_combination h0
    exact (mul_eq_zero.mp h1).resolve_left hπ
  simp only [hc, hd] at this ⊢
  linarith

/-- **Lemma 5.5** (TT:2328–2331). Let `𝗀 = g⁻¹ ∘ f` with welding CW1, CW2′, CW3′, CW4.
- Expansions: `f(z) = Σ_{n ≥ 0} a_n z^{n+1}` on `𝔻` with `a₀ = 1`, and `g(z) = Σ_{n ≥ 0} b_n z^{1-n}` on `𝔻*`.
- **(5.2)** `|b₀|² = Σ_{n ≥ 0} (n + 1)|a_n|² + Σ_{n ≥ 1} (n - 1)|b_n|²`.
- **[CORRECTION 2026-10-26]** The second sum is written as `Σ_{m ≥ 0} m |b_{m+1}|²`; the former `Σ_{n ≥ 0} (n - 1)|b_n|²`
  added the spurious term `-|b₀|²` (found by 下属2). -/
theorem lemma_5_5 {h f g : ℂ → ℂ} (hh : IsOneFixedQS h) (hw : IsWeldingPrime h f g) {a b : ℕ → ℂ}
    (ha : ∀ z ∈ unitDisc, HasSum (fun n => a n * z ^ (n + 1)) (f z))
    (hb : ∀ z ∈ unitDiscExterior, HasSum (fun n : ℕ => b n * z ^ (1 - (n : ℤ))) (g z)) :
    ‖b 0‖ ^ 2 = (∑' n : ℕ, ((n + 1 : ℕ) : ℝ) * ‖a n‖ ^ 2) + ∑' n : ℕ, (n : ℝ) * ‖b (n + 1)‖ ^ 2 :=
  l55_lemma_5_5 hh hw ha hb

end TakhtajanTeo
