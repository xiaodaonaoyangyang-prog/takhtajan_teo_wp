import TakhtajanTeo.Ch1.HilbertManifoldCompleted
import TakhtajanTeo.Ch2.S1_UnivalentFunctions
import TakhtajanTeo.Ch2.S1_Part5
import TakhtajanTeo.Ch2.S2_Mixed
import TakhtajanTeo.Ch1.S3_TopologicalGroup
import TakhtajanTeo.Appendix.BergmanPeriodModel
import TakhtajanTeo.Ch2.S3_Completed
import TakhtajanTeo.Ch2.S2_Remark22
import TakhtajanTeo.Ch2.FaberGramIntegral
import TakhtajanTeo.Ch1.GroupAlgebra
import TakhtajanTeo.Ch1.GroupChain1
import TakhtajanTeo.Ch2.S1_BP78Completed
import LiZhongQC.Lemmas.JordanBridge
import LiZhongQC.Lemmas.Quadrilateral

/-!
# Ch2 §1 completed originals, `T₀(1)` lane (`ab112_` helpers)

Helpers towards `lemma_1_11` and `thm_1_12`. Open originals used: `cor_3_2`; (ii) ⇒ (iii) of `thm_1_6` is proved in `S1_BP78Completed`.
-/

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal ComplexConjugate Classical Real
noncomputable section
namespace TakhtajanTeo
open LiZhongQC
namespace Ch2

theorem ab112_filter_eq :
    comap (fun z : ℂ => ‖z‖) (𝓝[<] 1) = comap (fun z : ℂ => ‖z‖) (𝓝 1) ⊓ 𝓟 unitDisc := by
  rw [nhdsWithin, comap_inf, comap_principal]
  congr 2
  ext z
  simp [unitDisc, mem_ball_zero_iff]

/-- `S(f) ∈ A₂(𝔻)` gives condition (ii) of Theorem 1.6. -/
theorem ab112_ii_of_A2 {f : ℂ → ℂ} (hS : schwarzianHol f ∈ A2fun unitDisc) :
    Tendsto (fun z => ((1 - ‖z‖ ^ 2) ^ 2 : ℂ) * schwarzianHol f z)
      (comap (fun z : ℂ => ‖z‖) (𝓝[<] 1)) (𝓝 0) := by
  rw [ab112_filter_eq]
  have h := A2fun.disk_weighted_tendsto_zero hS
  rw [tendsto_zero_iff_norm_tendsto_zero] at h ⊢
  refine h.congr' ?_
  filter_upwards [eventually_inf_principal.mpr (Eventually.of_forall (fun z hz => hz))] with z hz
  have hz1 : ‖z‖ < 1 := mem_ball_zero_iff.mp hz
  have hnn : 0 ≤ 1 - ‖z‖ ^ 2 := by nlinarith [norm_nonneg z]
  have hc : ((1 - ‖z‖ ^ 2) ^ 2 : ℂ) = (((1 - ‖z‖ ^ 2) ^ 2 : ℝ) : ℂ) := by push_cast; ring
  rw [hc, norm_mul (((1 - ‖z‖ ^ 2) ^ 2 : ℝ) : ℂ), Complex.norm_real,
    Real.norm_of_nonneg (pow_nonneg hnn 2),
    Real.norm_of_nonneg (mul_nonneg (pow_nonneg hnn 2) (norm_nonneg _))]

/-- **Lemma 1.11, `f`-part**, from Theorem 1.6 ((ii) ⇒ (iii)) and the analytic half `lemma_1_11_disc_of_boundary_small`. -/
theorem ab112_lemma_1_11_f {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f unitDisc) (hinj : InjOn f unitDisc)
    (hJ : IsJordanDomain (f '' unitDisc)) (hb : Bornology.IsBounded (f '' unitDisc))
    (hS : schwarzianHol f ∈ A2fun unitDisc) : preSchwarzian f ∈ A21fun unitDisc := by
  -- The Jordan hypothesis `hJ` is not needed ((ii) ⇒ (iii) holds for every bounded locally univalent `f`);
  -- the statement stays true without it, and it is kept for the original statement.
  have _h := hJ
  obtain ⟨M, hM⟩ := isBounded_iff_forall_norm_le.1 hb
  have hiii := ab16_ii_imp_iii hf (fun z hz => deriv_ne_zero_of_injOn isOpen_ball hf hinj hz)
    (M := M) (fun z hz => hM _ ⟨z, hz, rfl⟩) (ab112_ii_of_A2 hS)
  rw [ab112_filter_eq] at hiii
  exact lemma_1_11_disc_of_boundary_small hf hinj hS (boundary_small_of_weighted_tendsto_zero hiii)

/-! ### The welding functions of `μ ∈ L∞(𝔻*)₁` -/

theorem ab112_fsans_eq_fB {μ : LinfStar} (hμ : μ ∈ LinfStarBall) : fsans μ = fB μ := by
  ext z
  simp [fsans, AppB.b8_weldConst_zero hμ, lambdaW]

/-- `𝖿^μ` is univalent on `𝔻` with bounded Jordan image. -/
theorem ab112_fsans_facts {μ : LinfStar} (hμ : μ ∈ LinfStarBall) :
    DifferentiableOn ℂ (fsans μ) unitDisc ∧ InjOn (fsans μ) unitDisc ∧
      IsJordanDomain (fsans μ '' unitDisc) ∧ Bornology.IsBounded (fsans μ '' unitDisc) := by
  have hpair := AppB.b8_welding_normalized_pair hμ
  have hf := ab112_fsans_eq_fB hμ
  obtain ⟨hd, hi⟩ := fB_holomorphic_injective hμ
  refine ⟨hf ▸ hd, hf ▸ hi, ?_, ?_⟩
  · obtain ⟨e, he⟩ := wB_isHomeo hμ
    obtain ⟨hB, -⟩ := wB_spec hμ
    obtain ⟨M, hM, W, hW, hfin, hinf, f, hfz, hf0, hf1, hinv⟩ := hB
    have hw : ∀ z ∈ unitDisc, wB μ z = ((fB μ z : ℂ) : ExtPlane) := by
      intro z hz
      rw [hfz z hz]
      simp [fB, finPart, hfz z hz]
    rw [hf]
    refine uq_isJordanDomain_image e (D := unitDisc) m35_isJordanDomain_unitDisc ?_
    ext p
    simp only [toExt, mem_image]
    constructor
    · rintro ⟨_, ⟨z, hz, rfl⟩, rfl⟩
      exact ⟨fB μ z, ⟨z, hz, rfl⟩, by rw [he, hw z hz]⟩
    · rintro ⟨_, ⟨z, hz, rfl⟩, rfl⟩
      exact ⟨(z : ExtPlane), ⟨z, hz, rfl⟩, by rw [he, hw z hz]⟩
  · obtain ⟨R1, hR1⟩ := mg_far_exterior hpair (T := 2) (by norm_num)
    rw [hf] at hpair ⊢
    refine (Metric.isBounded_closedBall (x := (0 : ℂ)) (r := |R1| + 1)).subset ?_
    rintro w ⟨u, hu, rfl⟩
    by_contra hw
    have hgt : R1 < ‖fB μ u‖ := by
      rw [mem_closedBall_zero_iff, not_le] at hw
      linarith [le_abs_self R1]
    obtain ⟨z, hz, hzw⟩ := hR1 _ hgt
    have hdisj := hpair.2.2.2.2.2
    exact Set.disjoint_left.mp hdisj ⟨u, hu, rfl⟩ ⟨z, show 1 < ‖z‖ by linarith, hzw⟩

/-- `β([μ]) = 𝒮(𝖿^μ)` on `𝔻`. -/
theorem ab112_bers_eq (p : T1) :
    ∀ z ∈ unitDisc, AInf.toFun (bers p) z = schwarzianHol (fsans (Quotient.out p : LinfStarBall)) z := by
  intro z hz
  have hμ := (Quotient.out p : LinfStarBall).2
  rw [ab112_fsans_eq_fB hμ]
  exact (bersPhi_spec hμ).1 z hz

/-! ### Congruence of the quadratic-differential spaces on an open set -/

theorem ab112_A2fun_congr {U : Set ℂ} (hU : IsOpen U) {φ ψ : ℂ → ℂ} (h : EqOn φ ψ U) :
    φ ∈ A2fun U ↔ ψ ∈ A2fun U := by
  have hn := normA2_congr hU.measurableSet h
  constructor
  · rintro ⟨hd, hf⟩
    exact ⟨hd.congr (fun z hz => (h hz).symm), by rw [← hn]; exact hf⟩
  · rintro ⟨hd, hf⟩
    exact ⟨hd.congr (fun z hz => h hz), by rw [hn]; exact hf⟩

theorem ab112_A21fun_congr {U : Set ℂ} (hU : IsOpen U) {φ ψ : ℂ → ℂ} (h : EqOn φ ψ U) :
    φ ∈ A21fun U ↔ ψ ∈ A21fun U := by
  have hn := normA21_congr_on hU.measurableSet h
  constructor
  · rintro ⟨hd, hf⟩
    exact ⟨hd.congr (fun z hz => (h hz).symm), by rw [← hn]; exact hf⟩
  · rintro ⟨hd, hf⟩
    exact ⟨hd.congr (fun z hz => h hz), by rw [hn]; exact hf⟩

/-- (i) of Theorem 1.12. -/
theorem ab112_i (p : T1) :
    p ∈ T01 ↔ schwarzianHol (fsans ((Quotient.out p : LinfStarBall) : LinfStar)) ∈ A2fun unitDisc :=
  (Set.ext_iff.mp _root_.TakhtajanTeo.cor_3_2 p).trans
    (ab112_A2fun_congr isOpen_ball (fun z hz => ab112_bers_eq p z hz))

/-- (ii) of Theorem 1.12. -/
theorem ab112_ii (p : T1) :
    p ∈ T01 ↔ preSchwarzian (fsans ((Quotient.out p : LinfStarBall) : LinfStar)) ∈ A21fun unitDisc := by
  have hμ := (Quotient.out p : LinfStarBall).2
  obtain ⟨hd, hi, hJ, hb⟩ := ab112_fsans_facts hμ
  refine ⟨fun hp => ab112_lemma_1_11_f hd hi hJ hb ((ab112_i p).1 hp), fun hA => (ab112_i p).2 ?_⟩
  have hne : unitDisc ≠ unitDiscExterior := by
    intro h
    have h0 : (0 : ℂ) ∈ unitDisc := mem_ball_self one_pos
    rw [h] at h0
    norm_num [unitDiscExterior] at h0
  exact lemma_1_5 (Or.inl rfl) hA (fun h => absurd h hne)

/-! ### Germs, differentiability and the Schwarzian under `z ↦ 1/z` and conjugation -/

theorem ab112_S_congr {f g : ℂ → ℂ} {z : ℂ} (h : f =ᶠ[𝓝 z] g) :
    schwarzianHol f z = schwarzianHol g z := by
  have e : ∀ k : ℂ → ℂ, schwarzianHol k z =
      deriv (preSchwarzian k) z - (1 / 2) * preSchwarzian k z ^ 2 := fun k => rfl
  have hP : preSchwarzian f =ᶠ[𝓝 z] preSchwarzian g := h.deriv.deriv.div h.deriv
  rw [e f, e g, hP.deriv_eq, hP.eq_of_nhds]

theorem ab112_S_eqOn {U : Set ℂ} (hU : IsOpen U) {f g : ℂ → ℂ} (h : EqOn f g U) :
    EqOn (schwarzianHol f) (schwarzianHol g) U := fun z hz =>
  ab112_S_congr (Filter.eventuallyEq_of_mem (hU.mem_nhds hz) h)

theorem ab112_P_eqOn {U : Set ℂ} (hU : IsOpen U) {f g : ℂ → ℂ} (h : EqOn f g U) :
    EqOn (preSchwarzian f) (preSchwarzian g) U := by
  intro z hz
  have h' : f =ᶠ[𝓝 z] g := Filter.eventuallyEq_of_mem (hU.mem_nhds hz) h
  unfold preSchwarzian
  rw [h'.deriv_eq, h'.deriv.deriv_eq]

theorem ab112_P_diff {f : ℂ → ℂ} {E : Set ℂ} (hE : IsOpen E) (hf : DifferentiableOn ℂ f E)
    (hf1 : ∀ w ∈ E, deriv f w ≠ 0) : DifferentiableOn ℂ (preSchwarzian f) E := by
  intro z hz
  have hfa : AnalyticAt ℂ f z := hf.analyticAt (hE.mem_nhds hz)
  have h : AnalyticAt ℂ (preSchwarzian f) z := hfa.deriv.deriv.div hfa.deriv (hf1 z hz)
  exact h.differentiableAt.differentiableWithinAt

theorem ab112_S_diff {f : ℂ → ℂ} {E : Set ℂ} (hE : IsOpen E) (hf : DifferentiableOn ℂ f E)
    (hf1 : ∀ w ∈ E, deriv f w ≠ 0) : DifferentiableOn ℂ (schwarzianHol f) E := by
  intro z hz
  have hfa : AnalyticAt ℂ f z := hf.analyticAt (hE.mem_nhds hz)
  exact (analyticAt_schwarzianHol hfa (hf1 z hz)).differentiableAt.differentiableWithinAt

theorem ab112_S_conj (h : ℂ → ℂ) (x : ℂ) :
    schwarzianHol (fun z => conj (h (conj z))) x = conj (schwarzianHol h (conj x)) := by
  have e : ∀ (k : ℂ → ℂ) (y : ℂ), schwarzianHol k y =
      deriv (preSchwarzian k) y - (1 / 2) * preSchwarzian k y ^ 2 := fun k y => rfl
  have h1 : preSchwarzian (fun z => conj (h (conj z))) = fun z => conj (preSchwarzian h (conj z)) :=
    funext (s2c_conj_pre h)
  rw [e, e, h1]
  beta_reduce
  rw [s2c_conj_deriv (preSchwarzian h) x]
  simp [map_sub, map_mul, map_pow, map_ofNat]

theorem ab112_S_const_mul {c : ℂ} (hc : c ≠ 0) (h : ℂ → ℂ) (z : ℂ) :
    schwarzianHol (fun x => c * h x) z = schwarzianHol h z := by
  have e : ∀ k : ℂ → ℂ, schwarzianHol k z =
      deriv (preSchwarzian k) z - (1 / 2) * preSchwarzian k z ^ 2 := fun k => rfl
  rw [e, e, show preSchwarzian (fun x => c * h x) = preSchwarzian h from
    funext (s2c_pre_const_mul hc h)]

/-- `𝒮(1/g(1/s)) = s⁻⁴ 𝒮(g)(1/s)`. -/
theorem ab112_S_inv_inv {g : ℂ → ℂ} {E : Set ℂ} (hE : IsOpen E) (hg : DifferentiableOn ℂ g E)
    (hg0 : ∀ w ∈ E, g w ≠ 0) (hg1 : ∀ w ∈ E, deriv g w ≠ 0) {s : ℂ} (hs : s ≠ 0) (hsE : s⁻¹ ∈ E) :
    schwarzianHol (fun x => (g x⁻¹)⁻¹) s = (s ^ 4)⁻¹ * schwarzianHol g s⁻¹ := by
  have hga : AnalyticAt ℂ g s⁻¹ := hg.analyticAt (hE.mem_nhds hsE)
  have hinvA : AnalyticAt ℂ (fun x : ℂ => x⁻¹) s := analyticAt_inv hs
  have hu : AnalyticAt ℂ (fun x : ℂ => g x⁻¹) s :=
    AnalyticAt.comp (f := fun x : ℂ => x⁻¹) (x := s) hga hinvA
  have hd : HasDerivAt (fun x : ℂ => g x⁻¹) (deriv g s⁻¹ * (-(s ^ 2)⁻¹)) s :=
    HasDerivAt.comp s hga.differentiableAt.hasDerivAt (hasDerivAt_inv hs)
  have hs2 : (s ^ 2)⁻¹ ≠ 0 := inv_ne_zero (pow_ne_zero 2 hs)
  have hd1 : deriv (fun x : ℂ => g x⁻¹) s ≠ 0 := by
    rw [hd.deriv]
    exact mul_ne_zero (hg1 _ hsE) (neg_ne_zero.2 hs2)
  have hinvA' : AnalyticAt ℂ (fun x : ℂ => (g x⁻¹)⁻¹) s := hu.inv (hg0 _ hsE)
  have hinv0 : schwarzianHol (fun x : ℂ => x⁻¹) s = 0 := by
    have h1 := schwarzian_inv (u := fun w : ℂ => w) (z := s) analyticAt_id (by simp)
    rw [schwarzian_of_analyticAt hinvA, schwarzian_of_analyticAt
      (by fun_prop : AnalyticAt ℂ (fun w : ℂ => w) s)] at h1
    rw [h1]
    simp [schwarzianHol]
  have hchain := eq19_1_chain_rule (f := g) (g := fun x : ℂ => x⁻¹) (z := s) hinvA
    (by rw [deriv_inv]; exact neg_ne_zero.2 hs2) hga (hg1 _ hsE)
  simp only [Function.comp_def] at hchain
  rw [schwarzian_of_analyticAt hu, schwarzian_of_analyticAt hga, schwarzian_of_analyticAt hinvA,
    deriv_inv, hinv0, add_zero] at hchain
  have hinvS := schwarzian_inv hu hd1
  rw [schwarzian_of_analyticAt hinvA', schwarzian_of_analyticAt hu] at hinvS
  rw [hinvS, hchain]
  have : (-(s ^ 2)⁻¹) ^ 2 = (s ^ 4)⁻¹ := by
    field_simp
  rw [this, mul_comm]

/-- On `𝔻*`, `|𝒮(𝗀_{μ⁻¹})(z)| = |z|⁻⁴ |𝒮(𝖿^μ)(1/z̄)|`. -/
theorem ab112_S_G {μ : LinfStar} (hμ : μ ∈ LinfStarBall) {z : ℂ} (hz : z ∈ unitDiscExterior) :
    ‖schwarzianHol (gsans (beltramiInv μ)) z‖ =
      (‖z‖ ^ 4)⁻¹ * ‖schwarzianHol (fsans μ) (refl z)‖ := by
  obtain ⟨hfd, hfi, hf0, -, -, -, -, -, hf0', hf1'⟩ := s2c_facts hμ
  obtain ⟨φ, b, -, -, -, -, hb, hbg, -⟩ := g1_inverted_exterior (AppB.b8_welding_normalized_pair hμ)
  have hopenE : IsOpen unitDiscExterior := isOpen_lt continuous_const continuous_norm
  have hE : IsOpen (unitDisc \ {0}) := isOpen_ball.sdiff isClosed_singleton
  have hbc : conj b ≠ 0 := by simpa using hb
  have hz1 : 1 < ‖z‖ := hz
  have hz0 : z ≠ 0 := fun h => by simp [h] at hz1; linarith
  have hconjE : ∀ y ∈ unitDisc \ {0}, conj y ∈ unitDisc \ {0} := fun y hy =>
    ⟨by simpa [unitDisc] using hy.1, by simpa using hy.2⟩
  set fs : ℂ → ℂ := fun y => conj (fsans μ (conj y)) with hfs
  have hfsd : DifferentiableOn ℂ fs (unitDisc \ {0}) := by
    intro y hy
    have h := (hfd.differentiableAt (isOpen_ball.mem_nhds (hconjE y hy).1)).conj_conj
    rw [Complex.conj_conj] at h
    exact h.differentiableWithinAt
  have hfs0 : ∀ y ∈ unitDisc \ {0}, fs y ≠ 0 := fun y hy h =>
    hf0' (conj y) (hconjE y hy).1 (hconjE y hy).2 (by simpa [hfs] using h)
  have hfs1 : ∀ y ∈ unitDisc \ {0}, deriv fs y ≠ 0 := by
    intro y hy h
    have h' : deriv fs y = conj (deriv (fsans μ) (conj y)) := s2c_conj_deriv _ _
    rw [h'] at h
    exact hf1' (conj y) (hconjE y hy).1 (by simpa using h)
  set Gm : ℂ → ℂ := fun x => conj b * (fs x⁻¹)⁻¹ with hGm
  have hev : gsans (beltramiInv μ) =ᶠ[𝓝 z] Gm := by
    filter_upwards [hopenE.mem_nhds hz] with x hx
    rw [(w3_eq_1_3 hμ).2 x hx, hbg]
    simp [hGm, hfs, refl, map_inv₀]
  have hsE : z⁻¹ ∈ unitDisc \ {0} :=
    ⟨mem_ball_zero_iff.2 (by rw [norm_inv]; exact inv_lt_one_of_one_lt₀ hz1), inv_ne_zero hz0⟩
  rw [ab112_S_congr hev, hGm, ab112_S_const_mul hbc,
    ab112_S_inv_inv hE hfsd hfs0 hfs1 hz0 hsE]
  have e1 : schwarzianHol fs z⁻¹ = conj (schwarzianHol (fsans μ) (conj z⁻¹)) := ab112_S_conj _ _
  have hrefl : conj z⁻¹ = refl z := by simp [refl]
  rw [e1, hrefl, norm_mul, norm_inv, norm_pow, RCLike.norm_conj]

/-! ### Change of variables `z ↦ 1/z̄` in `lintegral` form -/

theorem ab112_enorm_sq (x : ℂ) : ((‖x‖₊ : ℝ≥0∞)) ^ 2 = ENNReal.ofReal (‖x‖ ^ 2) := by
  have h : ((‖x‖₊ : ℝ≥0∞)) = ENNReal.ofReal ‖x‖ := by
    rw [← coe_nnnorm x, ENNReal.ofReal_coe_nnreal]
  rw [h, ENNReal.ofReal_pow (norm_nonneg x)]

theorem ab112_inv_lintegral (K : ℂ → ℝ≥0∞) :
    ∫⁻ z in unitDiscExterior, K z =
      ∫⁻ w in unitDisc \ {0}, ENNReal.ofReal ((‖w‖ ^ 4)⁻¹) * K w⁻¹ := by
  have hopen : IsOpen unitDiscExterior := isOpen_lt continuous_const continuous_norm
  have hext0 : ∀ z ∈ unitDiscExterior, z ≠ 0 := fun z hz h => by
    subst h
    norm_num [unitDiscExterior] at hz
  rw [← resolvent_inv_exterior_image,
    lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hopen.measurableSet
      (fun z hz => ((differentiableAt_inv (hext0 z hz)).hasDerivAt.hasFDerivAt.restrictScalars
        ℝ).hasFDerivWithinAt) (fun a _ b _ h => inv_injective h)]
  refine setLIntegral_congr_fun hopen.measurableSet (fun z hz => ?_)
  have hz0 := hext0 z hz
  have hn : ‖z‖ ≠ 0 := norm_ne_zero_iff.2 hz0
  simp only [det_restrictScalars_toSpanSingleton]
  rw [abs_of_nonneg (sq_nonneg _), deriv_inv', inv_inv, ← mul_assoc,
    ← ENNReal.ofReal_mul (sq_nonneg _)]
  have : ‖-(z ^ 2)⁻¹‖ ^ 2 * (‖z⁻¹‖ ^ 4)⁻¹ = 1 := by
    simp only [norm_neg, norm_inv, norm_pow]
    field_simp
  rw [this, ENNReal.ofReal_one, one_mul]

theorem ab112_refl_lintegral (K : ℂ → ℝ≥0∞) :
    ∫⁻ z in unitDiscExterior, K z =
      ∫⁻ w in unitDisc, ENNReal.ofReal ((‖w‖ ^ 4)⁻¹) * K (refl w) := by
  have hemb : MeasurableEmbedding (⇑Complex.conjLIE) :=
    Complex.conjLIE.toHomeomorph.measurableEmbedding
  have hpre : (⇑Complex.conjLIE) ⁻¹' (unitDisc \ {0}) = unitDisc \ {0} := by
    ext w
    simp [unitDisc]
  have h := (Complex.conjLIE.measurePreserving).setLIntegral_comp_preimage_emb hemb
    (fun w => ENNReal.ofReal ((‖w‖ ^ 4)⁻¹) * K w⁻¹) (unitDisc \ {0})
  rw [hpre] at h
  rw [ab112_inv_lintegral, ← h, setLIntegral_congr s2c_null_sdiff]
  refine lintegral_congr (fun w => ?_)
  simp [refl]

/-! ### `A₂(𝔻*)` versus `A₂(𝔻)` for the Schwarzian -/

theorem ab112_normA2_G {μ : LinfStar} (hμ : μ ∈ LinfStarBall) :
    normA2 unitDiscExterior (schwarzianHol (gsans (beltramiInv μ))) =
      normA2 unitDisc (schwarzianHol (fsans μ)) := by
  unfold normA2
  congr 1
  rw [ab112_refl_lintegral]
  refine lintegral_congr_ae ?_
  refine (ae_restrict_iff' (show MeasurableSet unitDisc from measurableSet_ball)).2 ?_
  filter_upwards [(Set.countable_singleton (0 : ℂ)).ae_notMem volume] with u hu0 hu
  have hu0' : u ≠ 0 := hu0
  have hn : ‖u‖ ≠ 0 := norm_ne_zero_iff.2 hu0'
  have hz : refl u ∈ unitDiscExterior := (refl_mem_exterior_iff hu0').2 hu
  have h := ab112_S_G hμ hz
  rw [refl_involutive u, norm_refl] at h
  have hrho : (rho (refl u))⁻¹ = (rho u)⁻¹ * (‖u‖ ^ 4)⁻¹ := by
    simp only [rho, norm_refl, inv_div]
    field_simp
    ring
  have hr0 : 0 ≤ (rho u)⁻¹ := by unfold rho; positivity
  rw [ab112_enorm_sq, ab112_enorm_sq, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity), h, hrho]
  congr 1
  field_simp

theorem ab112_S_G_iff {μ : LinfStar} (hμ : μ ∈ LinfStarBall) :
    schwarzianHol (gsans (beltramiInv μ)) ∈ A2fun unitDiscExterior ↔
      schwarzianHol (fsans μ) ∈ A2fun unitDisc := by
  obtain ⟨hfd, -, -, -, -, -, -, -, -, hf1'⟩ := s2c_facts hμ
  obtain ⟨-, -, -, -, hgd, -, -, hg1, -, -⟩ := s2c_facts (bc_beltramiInv_mem_ball hμ)
  have hopenE : IsOpen unitDiscExterior := isOpen_lt continuous_const continuous_norm
  have hSg := ab112_S_diff hopenE hgd hg1
  have hSf := ab112_S_diff isOpen_ball hfd hf1'
  constructor
  · exact fun h => ⟨hSf, by rw [← ab112_normA2_G hμ]; exact h.2⟩
  · exact fun h => ⟨hSg, by rw [ab112_normA2_G hμ]; exact h.2⟩

/-! ### `A₂¹(𝔻*)` versus `A₂¹(𝔻)` for the pre-Schwarzian -/

theorem ab112_mem_A21_iff {D : Set ℂ} {ψ : ℂ → ℂ} (hd : DifferentiableOn ℂ ψ D) :
    ψ ∈ A21fun D ↔ ∫⁻ z in D, (‖ψ z‖₊ : ℝ≥0∞) ^ 2 ≠ ∞ :=
  ⟨a21_sq_lintegral_ne_top, fun h => ⟨hd, ENNReal.rpow_lt_top_of_nonneg (by norm_num) h⟩⟩

theorem ab112_L2_add_ne_top {U : Set ℂ} {a b : ℂ → ℂ} (ha : AEMeasurable a (volume.restrict U))
    (hfa : ∫⁻ z in U, (‖a z‖₊ : ℝ≥0∞) ^ 2 ≠ ∞) (hfb : ∫⁻ z in U, (‖b z‖₊ : ℝ≥0∞) ^ 2 ≠ ∞) :
    ∫⁻ z in U, (‖a z + b z‖₊ : ℝ≥0∞) ^ 2 ≠ ∞ := by
  have hpt : ∀ z, (‖a z + b z‖₊ : ℝ≥0∞) ^ 2 ≤
      2 * (‖a z‖₊ : ℝ≥0∞) ^ 2 + 2 * (‖b z‖₊ : ℝ≥0∞) ^ 2 := by
    intro z
    have h0 : ‖a z + b z‖ ^ 2 ≤ (‖a z‖ + ‖b z‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) (norm_add_le _ _) 2
    have h1 : ‖a z + b z‖ ^ 2 ≤ 2 * ‖a z‖ ^ 2 + 2 * ‖b z‖ ^ 2 := by
      nlinarith [sq_nonneg (‖a z‖ - ‖b z‖)]
    rw [ab112_enorm_sq, ab112_enorm_sq, ab112_enorm_sq]
    calc ENNReal.ofReal (‖a z + b z‖ ^ 2) ≤ ENNReal.ofReal (2 * ‖a z‖ ^ 2 + 2 * ‖b z‖ ^ 2) :=
          ENNReal.ofReal_le_ofReal h1
      _ = 2 * ENNReal.ofReal (‖a z‖ ^ 2) + 2 * ENNReal.ofReal (‖b z‖ ^ 2) := by
          rw [ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_mul (by norm_num),
            ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]
  refine ne_top_of_le_ne_top ?_ (lintegral_mono hpt)
  have hm : AEMeasurable (fun z => 2 * (‖a z‖₊ : ℝ≥0∞) ^ 2) (volume.restrict U) :=
    ((ha.nnnorm.coe_nnreal_ennreal).pow_const 2).const_mul 2
  rw [lintegral_add_left' hm, lintegral_const_mul' 2 _ ENNReal.ofNat_ne_top,
    lintegral_const_mul' 2 _ ENNReal.ofNat_ne_top]
  exact ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top ENNReal.ofNat_ne_top hfa,
    ENNReal.mul_ne_top ENNReal.ofNat_ne_top hfb⟩

theorem ab112_L2_const_ne_top {U : Set ℂ} {ψ : ℂ → ℂ} (c : ℂ)
    (h : ∫⁻ z in U, (‖ψ z‖₊ : ℝ≥0∞) ^ 2 ≠ ∞) : ∫⁻ z in U, (‖c * ψ z‖₊ : ℝ≥0∞) ^ 2 ≠ ∞ := by
  have e : ∀ z, (‖c * ψ z‖₊ : ℝ≥0∞) ^ 2 = (‖c‖₊ : ℝ≥0∞) ^ 2 * (‖ψ z‖₊ : ℝ≥0∞) ^ 2 := fun z => by
    rw [nnnorm_mul, ENNReal.coe_mul, mul_pow]
  simp only [e]
  rw [lintegral_const_mul' _ _ (ENNReal.pow_ne_top ENNReal.coe_ne_top)]
  exact ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.coe_ne_top) h

theorem ab112_lint_G {μ : LinfStar} (hμ : μ ∈ LinfStarBall) :
    ∫⁻ z in unitDiscExterior, (‖preSchwarzian (gsans (beltramiInv μ)) z‖₊ : ℝ≥0∞) ^ 2 =
      ∫⁻ u in unitDisc, (‖preSchwarzian (fsans μ) u - 2 * deriv (fsans μ) u / fsans μ u + 2 / u‖₊ :
        ℝ≥0∞) ^ 2 := by
  rw [ab112_refl_lintegral]
  refine lintegral_congr_ae ?_
  refine (ae_restrict_iff' (show MeasurableSet unitDisc from measurableSet_ball)).2 ?_
  filter_upwards [(Set.countable_singleton (0 : ℂ)).ae_notMem volume] with u hu0 hu
  have hu0' : u ≠ 0 := hu0
  have hn : ‖u‖ ≠ 0 := norm_ne_zero_iff.2 hu0'
  have hz : refl u ∈ unitDiscExterior := (refl_mem_exterior_iff hu0').2 hu
  have h := s2c_pre_G hμ hz
  rw [refl_involutive u, norm_refl] at h
  rw [ab112_enorm_sq, ab112_enorm_sq, ← ENNReal.ofReal_mul (by positivity), h]
  congr 1
  field_simp

/-- `∫_𝔻 |𝖿'/𝖿 - 1/z|² < ∞` for the welding functions (from the area theorem of Remark 2.2). -/
theorem ab112_deriv_mem_A21 {φ : ℂ → ℂ} {c : ℕ → ℂ}
    (hs : ∀ z ∈ unitDisc, HasSum (fun n : ℕ => c n * z ^ n) (φ z))
    (hsum : Summable (fun j : ℕ => ((j + 1 : ℕ) : ℝ) * ‖c (j + 1)‖ ^ 2)) :
    deriv φ ∈ A21fun unitDisc := by
  have hs' : ∀ z ∈ unitDisc, HasSum (fun n : ℕ => (c (n + 1) * ((n + 1 : ℕ) : ℂ)) * z ^ n)
      (deriv φ z) := fun z hz => faber_powerSeries_deriv hs hz
  have hterm : ∀ n : ℕ, π * ‖c (n + 1) * ((n + 1 : ℕ) : ℂ)‖ ^ 2 / ((n : ℝ) + 1) =
      π * (((n + 1 : ℕ) : ℝ) * ‖c (n + 1)‖ ^ 2) := by
    intro n
    rw [norm_mul, mul_pow, Complex.norm_natCast]
    push_cast
    field_simp
  have hsumm : Summable (fun n : ℕ => π * ‖c (n + 1) * ((n + 1 : ℕ) : ℂ)‖ ^ 2 / ((n : ℝ) + 1)) := by
    simp_rw [hterm]; exact hsum.mul_left π
  exact bergman_mem_A21_of_coeff hs' hsumm

theorem ab112_logder_f {μ : LinfStar} (hμ : μ ∈ LinfStarBall) :
    ∫⁻ u in unitDisc, (‖deriv (fsans μ) u / fsans μ u - 1 / u‖₊ : ℝ≥0∞) ^ 2 ≠ ∞ := by
  obtain ⟨hpair, hnull, -, -⟩ := mg_remark_2_2 hμ
  have hsum := (r22_sum hpair hnull).1
  obtain ⟨φ, hs, hf⟩ := r22_f_series hpair
  have hφ := differentiableOn_of_powerSeries hs
  have hnorm : ∀ j : ℕ, ‖(if j + 1 = 0 then (0 : ℂ) else
      -grunsky (fsans μ) (gsans μ) (-((j + 1 : ℕ) : ℤ)) 0)‖ =
      ‖grunsky (fsans μ) (gsans μ) (-((j : ℤ) + 1)) 0‖ := fun j => by
    rw [if_neg (Nat.succ_ne_zero j), norm_neg]
    push_cast
    rfl
  have hsum' : Summable (fun j : ℕ => ((j + 1 : ℕ) : ℝ) * ‖(if j + 1 = 0 then (0 : ℂ) else
      -grunsky (fsans μ) (gsans μ) (-((j + 1 : ℕ) : ℤ)) 0)‖ ^ 2) := by
    simp_rw [hnorm]; exact hsum
  have hmem := ab112_deriv_mem_A21 hs hsum'
  refine ne_of_eq_of_ne ?_ (a21_sq_lintegral_ne_top hmem)
  refine lintegral_congr_ae ?_
  refine (ae_restrict_iff' (show MeasurableSet unitDisc from measurableSet_ball)).2 ?_
  filter_upwards [(Set.countable_singleton (0 : ℂ)).ae_notMem volume] with z hz0 hz
  have hz0' : z ≠ 0 := hz0
  have hφd : DifferentiableAt ℂ φ z := hφ.differentiableAt (isOpen_ball.mem_nhds hz)
  have hfz : fsans μ z = z * Complex.exp (φ z) := hf z hz
  have hev : fsans μ =ᶠ[𝓝 z] fun w => w * Complex.exp (φ w) :=
    Filter.eventuallyEq_of_mem (isOpen_ball.mem_nhds hz) (fun w hw => hf w hw)
  have h2 : HasDerivAt (fun w => w * Complex.exp (φ w))
      (1 * Complex.exp (φ z) + z * (Complex.exp (φ z) * deriv φ z)) z :=
    (hasDerivAt_id' z).mul hφd.hasDerivAt.cexp
  have hder : deriv (fsans μ) z = Complex.exp (φ z) * (1 + z * deriv φ z) := by
    rw [hev.deriv_eq, h2.deriv]; ring
  have hexp : Complex.exp (φ z) ≠ 0 := Complex.exp_ne_zero _
  have : deriv (fsans μ) z / fsans μ z - 1 / z = deriv φ z := by
    rw [hder, hfz]
    field_simp
    ring
  rw [this]

theorem ab112_A_G_iff {μ : LinfStar} (hμ : μ ∈ LinfStarBall) :
    preSchwarzian (gsans (beltramiInv μ)) ∈ A21fun unitDiscExterior ↔
      preSchwarzian (fsans μ) ∈ A21fun unitDisc := by
  obtain ⟨hfd, -, -, -, -, -, -, -, -, hf1'⟩ := s2c_facts hμ
  obtain ⟨-, -, -, -, hgd, -, -, hg1, -, -⟩ := s2c_facts (bc_beltramiInv_mem_ball hμ)
  have hopenE : IsOpen unitDiscExterior := isOpen_lt continuous_const continuous_norm
  have hAg := ab112_P_diff hopenE hgd hg1
  have hAf : DifferentiableOn ℂ (preSchwarzian (fsans μ)) unitDisc :=
    ab112_P_diff isOpen_ball hfd hf1'
  have hL := ab112_logder_f hμ
  have hLm : AEMeasurable (fun u => deriv (fsans μ) u / fsans μ u - 1 / u)
      (volume.restrict unitDisc) :=
    (((measurable_deriv (fsans μ)).aemeasurable).div
      (hfd.continuousOn.aemeasurable measurableSet_ball)).sub
        ((measurable_const.div measurable_id).aemeasurable)
  have hAm : AEMeasurable (preSchwarzian (fsans μ)) (volume.restrict unitDisc) :=
    hAf.continuousOn.aemeasurable measurableSet_ball
  rw [ab112_mem_A21_iff hAg, ab112_mem_A21_iff hAf, ab112_lint_G hμ]
  have hK : ∀ u, preSchwarzian (fsans μ) u - 2 * deriv (fsans μ) u / fsans μ u + 2 / u =
      preSchwarzian (fsans μ) u + (-2) * (deriv (fsans μ) u / fsans μ u - 1 / u) := fun u => by
    ring
  simp only [hK]
  constructor
  · intro h
    have := ab112_L2_add_ne_top (a := fun u => preSchwarzian (fsans μ) u +
        (-2) * (deriv (fsans μ) u / fsans μ u - 1 / u))
      (b := fun u => 2 * (deriv (fsans μ) u / fsans μ u - 1 / u))
      (hAm.add (hLm.const_mul (-2))) h (ab112_L2_const_ne_top 2 hL)
    have e : ∀ u, preSchwarzian (fsans μ) u + (-2) * (deriv (fsans μ) u / fsans μ u - 1 / u) +
        2 * (deriv (fsans μ) u / fsans μ u - 1 / u) = preSchwarzian (fsans μ) u := fun u => by ring
    simpa only [e] using this
  · intro h
    exact ab112_L2_add_ne_top (a := preSchwarzian (fsans μ))
      (b := fun u => (-2) * (deriv (fsans μ) u / fsans μ u - 1 / u)) hAm h
      (ab112_L2_const_ne_top (-2) hL)

/-! ### Inversion in `T(1)` -/

theorem ab112_invT_eq (q : T1) :
    invT q = Phi ⟨beltramiInv ((Quotient.out q : LinfStarBall) : LinfStar),
      bc_beltramiInv_mem_ball (Quotient.out q : LinfStarBall).2⟩ := by
  unfold invT
  rw [dif_pos (bc_beltramiInv_mem_ball (Quotient.out q : LinfStarBall).2)]

/-- **Theorem 1.12**, modulo the involutivity `invT (invT p) = p` of inversion on `T(1)`. -/
theorem ab112_thm_1_12_of_invT (hinv : ∀ q : T1, invT (invT q) = q) (p : T1) :
    let μ : LinfStar := (Quotient.out p : LinfStarBall)
    (p ∈ T01 ↔ schwarzianHol (fsans μ) ∈ A2fun unitDisc) ∧
      (p ∈ T01 ↔ preSchwarzian (fsans μ) ∈ A21fun unitDisc) ∧
      (p ∈ T01 ↔ schwarzianHol (gsans μ) ∈ A2fun unitDiscExterior) ∧
      (p ∈ T01 ↔ preSchwarzian (gsans μ) ∈ A21fun unitDiscExterior) := by
  intro μ
  have hopenE : IsOpen unitDiscExterior := isOpen_lt continuous_const continuous_norm
  have hν := (Quotient.out (invT p) : LinfStarBall).2
  -- `ν = out (invT p)` and `ν⁻¹ ~ out p`
  have hrel : teichSetoid
      ⟨beltramiInv ((Quotient.out (invT p) : LinfStarBall) : LinfStar),
        bc_beltramiInv_mem_ball hν⟩ (Quotient.out p : LinfStarBall) := by
    have h1 : Phi ⟨beltramiInv ((Quotient.out (invT p) : LinfStarBall) : LinfStar),
        bc_beltramiInv_mem_ball hν⟩ = Phi (Quotient.out p : LinfStarBall) := by
      rw [← ab112_invT_eq (invT p), hinv p]
      exact (Quotient.out_eq p).symm
    exact Quotient.exact h1
  have hg := (s2c_class_pair hrel).2
  have hT : p ∈ T01 ↔ invT p ∈ T01 := by
    refine ⟨fun hp => _root_.TakhtajanTeo.lemma_3_4.2.2 p hp, fun hp => ?_⟩
    have := _root_.TakhtajanTeo.lemma_3_4.2.2 _ hp
    rwa [hinv p] at this
  refine ⟨ab112_i p, ab112_ii p, ?_, ?_⟩
  · refine hT.trans ((ab112_i (invT p)).trans ((ab112_S_G_iff hν).symm.trans ?_))
    exact ab112_A2fun_congr hopenE (ab112_S_eqOn hopenE hg)
  · refine hT.trans ((ab112_ii (invT p)).trans ((ab112_A_G_iff hν).symm.trans ?_))
    exact ab112_A21fun_congr hopenE (ab112_P_eqOn hopenE hg)

/-- **Theorem 1.12** (TT:3738–3746). Let `w_μ = 𝗀_μ⁻¹ ∘ 𝖿^μ` be the conformal welding (1.15) of `[μ] ∈ T(1)`. Then
`[μ] ∈ T₀(1)` iff any one of the following holds:
- (i) `𝒮(𝖿^μ) ∈ A₂(𝔻)`;
- (ii) `𝒜(𝖿^μ) ∈ A₂¹(𝔻)`;
- (iii) `𝒮(𝗀_μ) ∈ A₂(𝔻*)`;
- (iv) `𝒜(𝗀_μ) ∈ A₂¹(𝔻*)`. -/
theorem ab112_thm_1_12 (p : T1) :
    let μ : LinfStar := (Quotient.out p : LinfStarBall)
    (p ∈ T01 ↔ schwarzianHol (fsans μ) ∈ A2fun unitDisc) ∧
      (p ∈ T01 ↔ preSchwarzian (fsans μ) ∈ A21fun unitDisc) ∧
      (p ∈ T01 ↔ schwarzianHol (gsans μ) ∈ A2fun unitDiscExterior) ∧
      (p ∈ T01 ↔ preSchwarzian (gsans μ) ∈ A21fun unitDiscExterior) :=
  ab112_thm_1_12_of_invT grp_invT_invT p

/-! ### P3: the `g`-part of Lemma 1.11 -/

/-- The complement of a Jordan curve's exterior domain: a point `c` of the bounded complementary component of
`∂Ω` is at positive distance from `Ω = g(𝔻*)` (via the Jordan curve theorem). -/
theorem ab112_exists_center {g : ℂ → ℂ} (hg : IsUnivalentAtInfty g)
    (hJg : IsJordanCurve (toExt (frontier (g '' unitDiscExterior)))) :
    ∃ (c : ℂ) (δ : ℝ), 0 < δ ∧ c ∉ frontier (g '' unitDiscExterior) ∧
      ∀ z ∈ unitDiscExterior, δ ≤ ‖g z - c‖ := by
  obtain ⟨hgd, hgi, hgt⟩ := hg
  have hopenE : IsOpen unitDiscExterior := isOpen_lt continuous_const continuous_norm
  set Ω : Set ℂ := g '' unitDiscExterior with hΩdef
  have h2 : (2 : ℂ) ∈ unitDiscExterior := by show 1 < ‖(2 : ℂ)‖; norm_num
  have h3 : (3 : ℂ) ∈ unitDiscExterior := by show 1 < ‖(3 : ℂ)‖; norm_num
  have hEc : IsConnected unitDiscExterior :=
    ⟨⟨2, h2⟩, isPreconnected_setOf_lt_norm zero_le_one⟩
  have hΩo : IsOpen Ω := by
    rcases (hgd.analyticOnNhd hopenE).is_constant_or_isOpen hEc.isPreconnected with ⟨w, hw⟩ | h
    · exact absurd (hgi h2 h3 ((hw 2 h2).trans (hw 3 h3).symm)) (by norm_num)
    · exact h _ subset_rfl hopenE
  have hΩc : IsConnected Ω := hEc.image g hgd.continuousOn
  have hΩunb : ¬ Bornology.IsBounded Ω := by
    intro hb
    obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_closedBall (0 : ℂ)).1 hb
    have hK : IsCompact (closedBall (0 : ℂ) R) := isCompact_closedBall _ _
    have h1 : ∀ᶠ z in cocompact ℂ, g z ∈ (closedBall (0 : ℂ) R)ᶜ := hgt hK.compl_mem_cocompact
    have h2' : ∀ᶠ z in cocompact ℂ, z ∈ unitDiscExterior := by
      filter_upwards [(isCompact_closedBall (0 : ℂ) 1).compl_mem_cocompact] with z hz
      show 1 < ‖z‖
      simpa [mem_closedBall_zero_iff] using hz
    obtain ⟨z, hz1, hz2⟩ := (h1.and h2').exists
    exact hz1 (hR ⟨z, hz2, rfl⟩)
  have hJΩ : Disjoint Ω (frontier Ω) := by
    rw [hΩo.frontier_eq]
    exact Set.disjoint_sdiff_right
  have hcl : closure Ω = Ω ∪ frontier Ω := by
    rw [closure_eq_interior_union_frontier, hΩo.interior_eq]
  obtain ⟨A, B, hA, hB, hAc, hBc, hAB, hAJ, hBJ, huniv, hAb, hBb⟩ :=
    jordan_curve_theorem_complex_bounded hJg
  have hΩAB : Ω ⊆ A ∪ B := fun z hz => by
    have : z ∈ A ∪ B ∪ frontier Ω := huniv ▸ mem_univ z
    rcases this with h | h
    · exact h
    · exact absurd h (Set.disjoint_left.1 hJΩ hz)
  have hΩB : Ω ⊆ B := by
    rcases IsPreconnected.subset_or_subset hA hB hAB hΩAB hΩc.isPreconnected with h | h
    · exact absurd (hAb.subset h) hΩunb
    · exact h
  have hBsub : B ⊆ Ω ∪ (closure Ω)ᶜ := fun z hz => by
    by_cases hzc : z ∈ closure Ω
    · rw [hcl] at hzc
      rcases hzc with h | h
      · exact Or.inl h
      · exact absurd h (Set.disjoint_left.1 hBJ hz)
    · exact Or.inr hzc
  have hdisj : Disjoint Ω (closure Ω)ᶜ :=
    Set.disjoint_left.2 fun z hz hz' => hz' (subset_closure hz)
  have hAcl : A ⊆ (closure Ω)ᶜ := fun z hz hzc => by
    rw [hcl] at hzc
    rcases hzc with h | h
    · exact Set.disjoint_left.1 hAB hz (hΩB h)
    · exact Set.disjoint_left.1 hAJ hz h
  obtain ⟨c, hc⟩ := hAc.nonempty
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1 hA c hc
  have hcJ : c ∉ frontier Ω := fun h => hAcl hc (frontier_subset_closure h)
  refine ⟨c, δ, hδ, hcJ, fun z hz => ?_⟩
  by_contra hlt
  push_neg at hlt
  have hmem : g z ∈ ball c δ := by
    rw [mem_ball_iff_norm]
    exact hlt
  exact hAcl (hball hmem) (subset_closure ⟨z, hz, rfl⟩)

/-- **(P3a)** A function univalent at `∞` whose image has Jordan boundary is `c + 1/F(1/s)` with `F` univalent on `𝔻`,
`F(0) = 0`, bounded Jordan image. -/
theorem ab112_g_to_f {g : ℂ → ℂ} (hg : IsUnivalentAtInfty g)
    (hJg : IsJordanCurve (toExt (frontier (g '' unitDiscExterior)))) :
    ∃ (c : ℂ) (F : ℂ → ℂ), DifferentiableOn ℂ F unitDisc ∧ InjOn F unitDisc ∧
      IsJordanDomain (F '' unitDisc) ∧ Bornology.IsBounded (F '' unitDisc) ∧ F 0 = 0 ∧
      ∀ s ∈ unitDisc, s ≠ 0 → g (1 / s) = c + (F s)⁻¹ := by
  obtain ⟨c, δ, hδ, hcJ, hδg⟩ := ab112_exists_center hg hJg
  obtain ⟨hgd, hgi, hgt⟩ := hg
  have hopenE : IsOpen unitDiscExterior := isOpen_lt continuous_const continuous_norm
  have hinvE : ∀ s ∈ unitDisc, s ≠ 0 → 1 / s ∈ unitDiscExterior := fun s hs hs0 => by
    show 1 < ‖1 / s‖
    rw [one_div, norm_inv]
    exact (one_lt_inv₀ (norm_pos_iff.2 hs0)).2 (mem_ball_zero_iff.1 hs)
  have hgc : ∀ z ∈ unitDiscExterior, g z - c ≠ 0 := fun z hz h => by
    have := hδg z hz
    rw [h, norm_zero] at this
    linarith
  set f0 : ℂ → ℂ := fun s => (g (1 / s) - c)⁻¹ with hf0
  set F : ℂ → ℂ := fun s => if s = 0 then 0 else f0 s with hF
  have hFupd : F = Function.update f0 0 0 := by
    funext s
    simp [hF, Function.update_apply]
  have hbd : ∀ s ∈ unitDisc, s ≠ 0 → ‖f0 s‖ ≤ δ⁻¹ := fun s hs hs0 => by
    simp only [hf0, norm_inv]
    exact inv_anti₀ hδ (hδg _ (hinvE s hs hs0))
  have hdiff0 : DifferentiableOn ℂ f0 (unitDisc \ {0}) := by
    intro s hs
    have hs0 : s ≠ 0 := hs.2
    have h1 : DifferentiableAt ℂ (fun x : ℂ => 1 / x) s :=
      (differentiableAt_const (1 : ℂ)).div differentiableAt_id hs0
    have h2 : DifferentiableAt ℂ g (1 / s) :=
      hgd.differentiableAt (hopenE.mem_nhds (hinvE s hs.1 hs0))
    have h3 : DifferentiableAt ℂ (fun x => g (1 / x) - c) s := (h2.comp s h1).sub_const c
    exact (h3.inv (hgc _ (hinvE s hs.1 hs0))).differentiableWithinAt
  have hbdd : BddAbove (norm ∘ f0 '' (unitDisc \ {0})) :=
    ⟨δ⁻¹, by
      rintro _ ⟨s, hs, rfl⟩
      exact hbd s hs.1 hs.2⟩
  have hlim : Tendsto f0 (𝓝[≠] 0) (𝓝 0) := by
    have h1 : Tendsto (fun s : ℂ => 1 / s) (𝓝[≠] 0) (cocompact ℂ) := by
      rw [← cobounded_eq_cocompact]
      simpa [one_div] using tendsto_inv₀_nhdsNE_zero (α := ℂ)
    have hsub : Tendsto (fun w : ℂ => w - c) (cocompact ℂ) (cocompact ℂ) :=
      (Homeomorph.subRight c).map_cocompact.le
    have h2 : Tendsto (fun s => g (1 / s) - c) (𝓝[≠] 0) (cocompact ℂ) :=
      hsub.comp (hgt.comp h1)
    have h3 : Tendsto (fun s => g (1 / s) - c) (𝓝[≠] 0) (Bornology.cobounded ℂ) := by
      rw [cobounded_eq_cocompact]; exact h2
    exact (tendsto_inv₀_cobounded (α := ℂ)).comp h3
  have hlimU : limUnder (𝓝[≠] (0 : ℂ)) f0 = 0 := hlim.limUnder_eq
  have hdiffF : DifferentiableOn ℂ F unitDisc := by
    have h := Complex.differentiableOn_update_limUnder_of_bddAbove (f := f0) (c := 0)
      (isOpen_ball.mem_nhds (mem_ball_self one_pos)) hdiff0 hbdd
    rw [hlimU] at h
    rw [hFupd]
    exact h
  have hF0 : F 0 = 0 := by simp [hF]
  have hFne : ∀ s ∈ unitDisc, s ≠ 0 → F s = f0 s := fun s _ hs0 => by simp [hF, hs0]
  have hrel : ∀ s ∈ unitDisc, s ≠ 0 → g (1 / s) = c + (F s)⁻¹ := by
    intro s hs hs0
    rw [hFne s hs hs0]
    simp [hf0]
  have hFinj : InjOn F unitDisc := by
    intro s hs t ht hst
    by_cases hs0 : s = 0
    · by_cases ht0 : t = 0
      · rw [hs0, ht0]
      · exfalso
        rw [hs0, hF0, hFne t ht ht0] at hst
        exact inv_ne_zero (hgc _ (hinvE t ht ht0)) hst.symm
    · by_cases ht0 : t = 0
      · exfalso
        rw [ht0, hF0, hFne s hs hs0] at hst
        exact inv_ne_zero (hgc _ (hinvE s hs hs0)) hst
      · rw [hFne s hs hs0, hFne t ht ht0] at hst
        have h1 : g (1 / s) - c = g (1 / t) - c := inv_injective hst
        have h2 : 1 / s = 1 / t := hgi (hinvE s hs hs0) (hinvE t ht ht0) (sub_left_inj.1 h1)
        simpa [one_div] using h2
  have hFopen : IsOpen (F '' unitDisc) := by
    rcases (hdiffF.analyticOnNhd isOpen_ball).is_constant_or_isOpen
      (convex_ball (0 : ℂ) 1).isPreconnected with ⟨w, hw⟩ | h
    · have h0 : (0 : ℂ) ∈ unitDisc := mem_ball_self one_pos
      have h1 : ((1 : ℂ) / 2) ∈ unitDisc := by
        rw [unitDisc, mem_ball_zero_iff]; norm_num
      have := hFinj h0 h1 ((hw 0 h0).trans (hw _ h1).symm)
      norm_num at this
    · exact h _ subset_rfl isOpen_ball
  have hFconn : IsConnected (F '' unitDisc) :=
    ((convex_ball (0 : ℂ) 1).isConnected ⟨0, mem_ball_self one_pos⟩).image F hdiffF.continuousOn
  have hFb : Bornology.IsBounded (F '' unitDisc) := by
    refine (Metric.isBounded_closedBall (x := (0 : ℂ)) (r := δ⁻¹)).subset ?_
    rintro _ ⟨s, hs, rfl⟩
    rw [mem_closedBall_zero_iff]
    by_cases hs0 : s = 0
    · rw [hs0, hF0, norm_zero]; positivity
    · rw [hFne s hs hs0]; exact hbd s hs hs0
  refine ⟨c, F, hdiffF, hFinj, ⟨hFopen, hFconn, ?_⟩, hFb, hF0, hrel⟩
  -- the frontier of `F(𝔻)` is the image of `∂Ω` under `w ↦ (w - c)⁻¹`
  set Ω : Set ℂ := g '' unitDiscExterior with hΩdef
  have hΩo : IsOpen Ω := by
    rcases (hgd.analyticOnNhd hopenE).is_constant_or_isOpen
      (isPreconnected_setOf_lt_norm (zero_le_one)) with ⟨w, hw⟩ | h
    · have h2 : (2 : ℂ) ∈ unitDiscExterior := by show 1 < ‖(2 : ℂ)‖; norm_num
      have h3 : (3 : ℂ) ∈ unitDiscExterior := by show 1 < ‖(3 : ℂ)‖; norm_num
      exact absurd (hgi h2 h3 ((hw 2 h2).trans (hw 3 h3).symm)) (by norm_num)
    · exact h _ subset_rfl hopenE
  set m : ℂ → ℂ := fun w => (w - c)⁻¹ with hm
  have hcΩ : c ∉ closure Ω := by
    intro hc
    have hgcl : ∀ w ∈ Ω, δ ≤ ‖w - c‖ := by
      rintro _ ⟨z, hz, rfl⟩
      exact hδg z hz
    have hcl : closure Ω ⊆ {w | δ ≤ ‖w - c‖} :=
      closure_minimal (fun w hw => hgcl w hw)
        (isClosed_le continuous_const ((continuous_id.sub continuous_const).norm))
    have : δ ≤ ‖c - c‖ := hcl hc
    rw [sub_self, norm_zero] at this
    linarith
  have hD' : F '' unitDisc = insert 0 (m '' Ω) := by
    ext w
    constructor
    · rintro ⟨s, hs, rfl⟩
      by_cases hs0 : s = 0
      · left; rw [hs0, hF0]
      · right
        exact ⟨g (1 / s), ⟨1 / s, hinvE s hs hs0, rfl⟩, by rw [hFne s hs hs0]⟩
    · rintro (rfl | ⟨_, ⟨z, hz, rfl⟩, rfl⟩)
      · exact ⟨0, mem_ball_self one_pos, hF0⟩
      · have hz1 : 1 < ‖z‖ := hz
        have hz0 : z ≠ 0 := fun h => by simp [h] at hz1; linarith
        have hzD : 1 / z ∈ unitDisc := by
          rw [unitDisc, mem_ball_zero_iff, one_div, norm_inv]
          exact inv_lt_one_of_one_lt₀ hz1
        refine ⟨1 / z, hzD, ?_⟩
        rw [hFne _ hzD (by simpa using hz0)]
        simp [hf0, hm]
  have hmΨ : ∀ w : ℂ, w ≠ 0 → m (c + w⁻¹) = w := fun w hw => by simp [hm]
  have himg : (fun u : ℂ => c + u⁻¹) '' (m '' Ω) = Ω := by
    ext x
    constructor
    · rintro ⟨_, ⟨ω, hω, rfl⟩, rfl⟩
      simpa [hm] using hω
    · intro hx
      exact ⟨m x, ⟨x, hx, rfl⟩, by simp [hm]⟩
  have hfr : frontier (F '' unitDisc) = m '' frontier Ω := by
    rw [hFopen.frontier_eq]
    ext w
    constructor
    · rintro ⟨hcl, hnot⟩
      have hw0 : w ≠ 0 := fun h => hnot (h ▸ ⟨0, mem_ball_self one_pos, hF0⟩)
      rw [hD', Set.insert_eq, closure_union, closure_singleton] at hcl
      have hcl' : w ∈ closure (m '' Ω) := by
        rcases hcl with h | h
        · exact absurd h hw0
        · exact h
      have hΨc : ContinuousAt (fun u : ℂ => c + u⁻¹) w :=
        (continuousAt_const).add (continuousAt_inv₀ hw0)
      have hv := ContinuousWithinAt.mem_closure_image (ContinuousAt.continuousWithinAt hΨc) hcl'
      rw [himg] at hv
      have hvΩ : c + w⁻¹ ∉ Ω := fun h => hnot (by rw [hD']; right; exact ⟨_, h, hmΨ w hw0⟩)
      refine ⟨c + w⁻¹, ?_, hmΨ w hw0⟩
      rw [hΩo.frontier_eq]
      exact ⟨hv, hvΩ⟩
    · rintro ⟨j, hj, rfl⟩
      rw [hΩo.frontier_eq] at hj
      obtain ⟨hjcl, hjΩ⟩ := hj
      have hjc : j ≠ c := fun h => hcΩ (h ▸ hjcl)
      have hmc : ContinuousAt m j :=
        (continuousAt_id.sub continuousAt_const).inv₀ (sub_ne_zero.2 hjc)
      refine ⟨?_, ?_⟩
      · rw [hD', Set.insert_eq, closure_union, closure_singleton]
        right
        exact ContinuousWithinAt.mem_closure_image (ContinuousAt.continuousWithinAt hmc) hjcl
      · rw [hD']
        rintro (h | ⟨ω, hω, hωj⟩)
        · exact hjc (sub_eq_zero.1 (inv_eq_zero.1 h))
        · have h1 : ω - c = j - c := inv_injective hωj
          exact hjΩ ((sub_left_inj.1 h1) ▸ hω)
  rw [frontier_toExt_of_isBounded hFb hFopen, hfr]
  obtain ⟨γ, hγc, hγi, hγr⟩ := exists_circle_param_of_isJordanCurve_toExt hJg
  have hγne : ∀ t, γ t - c ≠ 0 := fun t h => hcJ (by
    rw [← sub_eq_zero.1 h, ← hγr]
    exact mem_range_self t)
  refine ⟨fun t => ((m (γ t) : ℂ) : ExtPlane), ?_, ?_, ?_⟩
  · exact OnePoint.continuous_coe.comp ((hγc.sub continuous_const).inv₀ hγne)
  · intro a b hab
    have h1 : m (γ a) = m (γ b) := OnePoint.coe_injective hab
    exact hγi (sub_left_inj.1 (inv_injective h1))
  · rw [show (fun t => ((m (γ t) : ℂ) : ExtPlane)) = (((↑) : ℂ → ExtPlane) ∘ m ∘ γ) from rfl,
      range_comp, range_comp, hγr]
    rfl

/-! ### P3b: the Schwarzian and the pre-Schwarzian of `g = c + 1/F(1/z)` -/

theorem ab112_P_add_const (c : ℂ) (h : ℂ → ℂ) :
    preSchwarzian (fun x => c + h x) = preSchwarzian h := by
  funext y
  unfold preSchwarzian
  have h2 : deriv (fun x => c + h x) = deriv h := deriv_const_add' c
  rw [h2]

theorem ab112_S_add_const (c : ℂ) (h : ℂ → ℂ) (z : ℂ) :
    schwarzianHol (fun x => c + h x) z = schwarzianHol h z := by
  have e : ∀ k : ℂ → ℂ, schwarzianHol k z =
      deriv (preSchwarzian k) z - (1 / 2) * preSchwarzian k z ^ 2 := fun k => rfl
  rw [e, e, ab112_P_add_const]

theorem ab112_g_eq {g F : ℂ → ℂ} {c : ℂ}
    (hrel : ∀ s ∈ unitDisc, s ≠ 0 → g (1 / s) = c + (F s)⁻¹) :
    EqOn g (fun x => c + (F x⁻¹)⁻¹) unitDiscExterior := by
  intro z hz
  have hz1 : 1 < ‖z‖ := hz
  have hz0 : z ≠ 0 := fun h => by simp [h] at hz1; linarith
  have hD : z⁻¹ ∈ unitDisc := by
    rw [unitDisc, mem_ball_zero_iff, norm_inv]
    exact inv_lt_one_of_one_lt₀ hz1
  have := hrel z⁻¹ hD (inv_ne_zero hz0)
  simpa using this

theorem ab112_F_facts {F : ℂ → ℂ} (hFd : DifferentiableOn ℂ F unitDisc) (hFi : InjOn F unitDisc)
    (hF0 : F 0 = 0) :
    (∀ w ∈ unitDisc \ {0}, deriv F w ≠ 0) ∧ (∀ w ∈ unitDisc \ {0}, F w ≠ 0) := by
  refine ⟨fun w hw => deriv_ne_zero_of_injOn isOpen_ball hFd hFi hw.1, fun w hw h => hw.2 ?_⟩
  exact hFi hw.1 (mem_ball_self one_pos) (h.trans hF0.symm)

theorem ab112_S_ext {g F : ℂ → ℂ} {c : ℂ} (hFd : DifferentiableOn ℂ F unitDisc)
    (hFi : InjOn F unitDisc) (hF0 : F 0 = 0)
    (hrel : ∀ s ∈ unitDisc, s ≠ 0 → g (1 / s) = c + (F s)⁻¹) {z : ℂ} (hz : z ∈ unitDiscExterior) :
    schwarzianHol g z = (z ^ 4)⁻¹ * schwarzianHol F z⁻¹ := by
  have hopenE : IsOpen unitDiscExterior := isOpen_lt continuous_const continuous_norm
  have hE : IsOpen (unitDisc \ {0}) := isOpen_ball.sdiff isClosed_singleton
  obtain ⟨hF1, hF0'⟩ := ab112_F_facts hFd hFi hF0
  have hz1 : 1 < ‖z‖ := hz
  have hz0 : z ≠ 0 := fun h => by simp [h] at hz1; linarith
  have hsE : z⁻¹ ∈ unitDisc \ {0} :=
    ⟨mem_ball_zero_iff.2 (by rw [norm_inv]; exact inv_lt_one_of_one_lt₀ hz1), inv_ne_zero hz0⟩
  rw [ab112_S_eqOn hopenE (ab112_g_eq hrel) hz, ab112_S_add_const,
    ab112_S_inv_inv hE (hFd.mono Set.sdiff_subset) hF0' hF1 hz0 hsE]

theorem ab112_normA2_ext {g F : ℂ → ℂ} {c : ℂ} (hFd : DifferentiableOn ℂ F unitDisc)
    (hFi : InjOn F unitDisc) (hF0 : F 0 = 0)
    (hrel : ∀ s ∈ unitDisc, s ≠ 0 → g (1 / s) = c + (F s)⁻¹) :
    normA2 unitDiscExterior (schwarzianHol g) = normA2 unitDisc (schwarzianHol F) := by
  unfold normA2
  congr 1
  rw [ab112_inv_lintegral, setLIntegral_congr s2c_null_sdiff]
  refine lintegral_congr_ae ?_
  refine (ae_restrict_iff' (show MeasurableSet unitDisc from measurableSet_ball)).2 ?_
  filter_upwards [(Set.countable_singleton (0 : ℂ)).ae_notMem volume] with u hu0 hu
  have hu0' : u ≠ 0 := hu0
  have hn : ‖u‖ ≠ 0 := norm_ne_zero_iff.2 hu0'
  have hz : u⁻¹ ∈ unitDiscExterior := by
    show 1 < ‖u⁻¹‖
    rw [norm_inv]
    exact (one_lt_inv₀ (norm_pos_iff.2 hu0')).2 (mem_ball_zero_iff.1 hu)
  have h := congrArg norm (ab112_S_ext hFd hFi hF0 hrel hz)
  rw [norm_mul, inv_inv, norm_inv, norm_pow, norm_inv] at h
  have hrho : (rho u⁻¹)⁻¹ = (rho u)⁻¹ * (‖u‖ ^ 4)⁻¹ := by
    simp only [rho, norm_inv, inv_div]
    field_simp
    ring
  have hr0 : 0 ≤ (rho u)⁻¹ := by unfold rho; positivity
  rw [ab112_enorm_sq, ab112_enorm_sq, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity), h, hrho]
  congr 1
  field_simp

/-- **P3b.** `𝒮(g) ∈ A₂(𝔻*)` gives `𝒮(F) ∈ A₂(𝔻)`. -/
theorem ab112_schwarzian_transfer {g F : ℂ → ℂ} {c : ℂ} (hFd : DifferentiableOn ℂ F unitDisc)
    (hFi : InjOn F unitDisc) (hF0 : F 0 = 0)
    (hrel : ∀ s ∈ unitDisc, s ≠ 0 → g (1 / s) = c + (F s)⁻¹)
    (hS : schwarzianHol g ∈ A2fun unitDiscExterior) : schwarzianHol F ∈ A2fun unitDisc := by
  refine ⟨ab112_S_diff isOpen_ball hFd (fun w hw => deriv_ne_zero_of_injOn isOpen_ball hFd hFi hw), ?_⟩
  rw [← ab112_normA2_ext hFd hFi hF0 hrel]
  exact hS.2

/-! ### P3c: the function `Φ = 𝒜(F) - 2 (F'/F - 1/w)` -/

theorem ab112_Phi_data {F : ℂ → ℂ} (hFd : DifferentiableOn ℂ F unitDisc) (hFi : InjOn F unitDisc)
    (hF0 : F 0 = 0) :
    ∃ Φ : ℂ → ℂ, DifferentiableOn ℂ Φ unitDisc ∧ Φ 0 = 0 ∧
      (∀ w ∈ unitDisc, w ≠ 0 → Φ w = preSchwarzian F w - 2 * (deriv F w / F w - 1 / w)) ∧
      (∀ w ∈ unitDisc, w ≠ 0 → PsiOp Φ w = schwarzianHol F w - 2 * (Φ w / w)) := by
  obtain ⟨hF1, hF0'⟩ := ab112_F_facts hFd hFi hF0
  have h0mem : (0 : ℂ) ∈ unitDisc := mem_ball_self one_pos
  have hnhds : ∀ w ∈ unitDisc, unitDisc ∈ 𝓝 w := fun w hw => isOpen_ball.mem_nhds hw
  set h : ℂ → ℂ := dslope F 0 with hh
  have hhd : DifferentiableOn ℂ h unitDisc :=
    (Complex.differentiableOn_dslope (hnhds 0 h0mem)).2 hFd
  have hFh : ∀ w, F w = w * h w := fun w => by
    have := sub_smul_dslope F 0 w
    rw [smul_eq_mul, sub_zero, hF0, sub_zero] at this
    exact this.symm
  have hFeq : F = fun x => x * h x := funext hFh
  have hh0 : ∀ w ∈ unitDisc, h w ≠ 0 := by
    intro w hw
    by_cases hw0 : w = 0
    · subst hw0
      rw [hh, dslope_same]
      exact deriv_ne_zero_of_injOn isOpen_ball hFd hFi h0mem
    · intro hz
      exact hF0' w ⟨hw, hw0⟩ (by rw [hFh w, hz, mul_zero])
  have hhan : ∀ w ∈ unitDisc, AnalyticAt ℂ h w := fun w hw => hhd.analyticAt (hnhds w hw)
  have hderivF : ∀ w ∈ unitDisc, deriv F w = h w + w * deriv h w := by
    intro w hw
    have hH : HasDerivAt (fun x => x * h x) (1 * h w + w * deriv h w) w :=
      (hasDerivAt_id w).mul (hhan w hw).differentiableAt.hasDerivAt
    rw [hFeq, hH.deriv, one_mul]
  set ψ : ℂ → ℂ := fun w => deriv h w / h w with hψ
  have hψd : DifferentiableOn ℂ ψ unitDisc := fun w hw =>
    (((hhan w hw).deriv.div (hhan w hw) (hh0 w hw)).differentiableAt).differentiableWithinAt
  have hAd : DifferentiableOn ℂ (preSchwarzian F) unitDisc := ab112_P_diff isOpen_ball hFd
    (fun w hw => deriv_ne_zero_of_injOn isOpen_ball hFd hFi hw)
  set Φ : ℂ → ℂ := fun w => preSchwarzian F w - 2 * ψ w with hΦ
  have hΦd : DifferentiableOn ℂ Φ unitDisc := hAd.sub (hψd.const_mul 2)
  have hE1 : ∀ w ∈ unitDisc, w ≠ 0 → ψ w = deriv F w / F w - 1 / w := by
    intro w hw hw0
    have hhw := hh0 w hw
    simp only [hψ]
    rw [hderivF w hw, hFh w]
    field_simp
    ring
  have hΦe : ∀ w ∈ unitDisc, w ≠ 0 → Φ w = preSchwarzian F w - 2 * (deriv F w / F w - 1 / w) := by
    intro w hw hw0
    simp only [hΦ]
    rw [hE1 w hw hw0]
  refine ⟨Φ, hΦd, ?_, hΦe, ?_⟩
  · -- `Φ 0 = 0`
    have hd0 : deriv F 0 = h 0 := by rw [hderivF 0 h0mem]; simp
    have hdd0 : deriv (deriv F) 0 = 2 * deriv h 0 := by
      have hev : deriv F =ᶠ[𝓝 0] fun x => h x + x * deriv h x :=
        Filter.eventuallyEq_of_mem (hnhds 0 h0mem) (fun x hx => hderivF x hx)
      have hH : HasDerivAt (fun x => h x + x * deriv h x)
          (deriv h 0 + (1 * deriv h 0 + 0 * deriv (deriv h) 0)) 0 :=
        (hhan 0 h0mem).differentiableAt.hasDerivAt.add
          ((hasDerivAt_id 0).mul (hhan 0 h0mem).deriv.differentiableAt.hasDerivAt)
      rw [hev.deriv_eq, hH.deriv]
      ring
    simp only [hΦ, hψ, preSchwarzian]
    rw [hdd0, hd0]
    ring
  · -- `Ψ(Φ) = 𝒮(F) - 2 Φ/w`
    intro w hw hw0
    have hFw : F w ≠ 0 := hF0' w ⟨hw, hw0⟩
    have hFw' : deriv F w ≠ 0 := hF1 w ⟨hw, hw0⟩
    have hFan : AnalyticAt ℂ F w := hFd.analyticAt (hnhds w hw)
    have hN : unitDisc \ {0} ∈ 𝓝 w :=
      (isOpen_ball.sdiff isClosed_singleton).mem_nhds ⟨hw, hw0⟩
    have hev : Φ =ᶠ[𝓝 w] fun x => preSchwarzian F x - 2 * (deriv F x / F x - x⁻¹) := by
      filter_upwards [hN] with x hx
      rw [hΦe x hx.1 hx.2, one_div]
    have hA : HasDerivAt (preSchwarzian F) (deriv (preSchwarzian F) w) w :=
      (hAd.differentiableAt (hnhds w hw)).hasDerivAt
    have hF'' : HasDerivAt (deriv F) (deriv (deriv F) w) w := hFan.deriv.differentiableAt.hasDerivAt
    have hF' : HasDerivAt F (deriv F w) w := hFan.differentiableAt.hasDerivAt
    have hu : HasDerivAt (fun x => deriv F x / F x)
        ((deriv (deriv F) w * F w - deriv F w * deriv F w) / F w ^ 2) w := hF''.div hF' hFw
    have hi : HasDerivAt (fun x : ℂ => x⁻¹) (-(w ^ 2)⁻¹) w := hasDerivAt_inv hw0
    have hΦ' : HasDerivAt (fun x => preSchwarzian F x - 2 * (deriv F x / F x - x⁻¹))
        (deriv (preSchwarzian F) w -
          2 * ((deriv (deriv F) w * F w - deriv F w * deriv F w) / F w ^ 2 - -(w ^ 2)⁻¹)) w :=
      hA.sub ((hu.sub hi).const_mul 2)
    have hdΦ : deriv Φ w = deriv (preSchwarzian F) w -
        2 * ((deriv (deriv F) w * F w - deriv F w * deriv F w) / F w ^ 2 - -(w ^ 2)⁻¹) := by
      rw [hev.deriv_eq, hΦ'.deriv]
    have hΦw : Φ w = preSchwarzian F w - 2 * (deriv F w / F w - w⁻¹) := by
      rw [hΦe w hw hw0, one_div]
    have eS : schwarzianHol F w = deriv (preSchwarzian F) w - (1 / 2) * preSchwarzian F w ^ 2 := rfl
    have hpre : preSchwarzian F w = deriv (deriv F) w / deriv F w := rfl
    show deriv Φ w - 1 / 2 * Φ w ^ 2 = _
    rw [hdΦ, hΦw, eS, hpre]
    field_simp
    ring

/-! ### P3d: boundary smallness of `𝒜(F)` and `F'/F` -/

theorem ab112_open_image {F : ℂ → ℂ} (hFd : DifferentiableOn ℂ F unitDisc) (hFi : InjOn F unitDisc)
    {U : Set ℂ} (hU : U ⊆ unitDisc) (hUo : IsOpen U) : IsOpen (F '' U) := by
  rcases (hFd.analyticOnNhd isOpen_ball).is_constant_or_isOpen
    (convex_ball (0 : ℂ) 1).isPreconnected with ⟨w, hw⟩ | h
  · exfalso
    have h0 : (0 : ℂ) ∈ unitDisc := mem_ball_self one_pos
    have h1 : ((1 : ℂ) / 2) ∈ unitDisc := by
      rw [unitDisc, mem_ball_zero_iff]; norm_num
    have := hFi h0 h1 ((hw 0 h0).trans (hw _ h1).symm)
    norm_num at this
  · exact h U hU hUo

theorem ab112_F_far {F : ℂ → ℂ} (hFd : DifferentiableOn ℂ F unitDisc) (hFi : InjOn F unitDisc)
    (hF0 : F 0 = 0) : ∃ δ' : ℝ, 0 < δ' ∧ ∀ w ∈ unitDisc, 1 / 2 ≤ ‖w‖ → δ' ≤ ‖F w‖ := by
  have hsub : ball (0 : ℂ) (1 / 2) ⊆ unitDisc := ball_subset_ball (by norm_num)
  have hopen := ab112_open_image hFd hFi hsub isOpen_ball
  obtain ⟨δ', hδ', hb⟩ := Metric.isOpen_iff.1 hopen 0 ⟨0, mem_ball_self (by norm_num), hF0⟩
  refine ⟨δ', hδ', fun w hw hw2 => ?_⟩
  by_contra hlt
  push_neg at hlt
  have hmem : F w ∈ ball (0 : ℂ) δ' := by rwa [mem_ball_zero_iff]
  obtain ⟨v, hv, hvw⟩ := hb hmem
  have hvw' : v = w := hFi (hsub hv) hw hvw
  rw [hvw'] at hv
  have := mem_ball_zero_iff.1 hv
  linarith

theorem ab112_eventually_L :
    ∀ᶠ w in (comap (fun z : ℂ => ‖z‖) (𝓝 1) ⊓ 𝓟 unitDisc), w ∈ unitDisc ∧ 1 / 2 ≤ ‖w‖ := by
  have hn : Tendsto (fun z : ℂ => ‖z‖) (comap (fun z : ℂ => ‖z‖) (𝓝 1) ⊓ 𝓟 unitDisc) (𝓝 1) :=
    tendsto_comap.mono_left inf_le_left
  have hD : ∀ᶠ z in (comap (fun z : ℂ => ‖z‖) (𝓝 1) ⊓ 𝓟 unitDisc), z ∈ unitDisc :=
    (show ∀ᶠ z in 𝓟 unitDisc, z ∈ unitDisc from
      eventually_principal.mpr (fun _ hz => hz)).filter_mono inf_le_right
  exact hD.and (hn.eventually (Ici_mem_nhds (by norm_num : (1 / 2 : ℝ) < 1)))

theorem ab112_A_small {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f unitDisc) (hinj : InjOn f unitDisc)
    (hJ : IsJordanDomain (f '' unitDisc)) (hb : Bornology.IsBounded (f '' unitDisc))
    (hS : schwarzianHol f ∈ A2fun unitDisc) :
    Tendsto (fun z => ((1 - ‖z‖ ^ 2) : ℂ) * preSchwarzian f z)
      (comap (fun z : ℂ => ‖z‖) (𝓝 1) ⊓ 𝓟 unitDisc) (𝓝 0) := by
  -- The Jordan hypothesis `hJ` is not needed ((ii) ⇒ (iii) holds for every bounded locally univalent `f`);
  -- the statement stays true without it, and it is kept for the original statement.
  have _h := hJ
  obtain ⟨M, hM⟩ := isBounded_iff_forall_norm_le.1 hb
  have hiii := ab16_ii_imp_iii hf (fun z hz => deriv_ne_zero_of_injOn isOpen_ball hf hinj hz)
    (M := M) (fun z hz => hM _ ⟨z, hz, rfl⟩) (ab112_ii_of_A2 hS)
  rw [ab112_filter_eq] at hiii
  exact hiii

/-- `𝒜(1/(F - R)) = 𝒜(F) - 2F'/(F - R)`. -/
theorem ab112_P_inv_shift {F : ℂ → ℂ} {R : ℂ} (hFd : DifferentiableOn ℂ F unitDisc)
    (hne : ∀ w ∈ unitDisc, F w - R ≠ 0) {w : ℂ} (hw : w ∈ unitDisc) (hF1 : deriv F w ≠ 0) :
    preSchwarzian (fun x => (F x - R)⁻¹) w =
      preSchwarzian F w - 2 * (deriv F w / (F w - R)) := by
  have hn : F w - R ≠ 0 := hne w hw
  have hFan : ∀ x ∈ unitDisc, AnalyticAt ℂ F x := fun x hx =>
    hFd.analyticAt (isOpen_ball.mem_nhds hx)
  have hd1 : ∀ x ∈ unitDisc, deriv (fun y => (F y - R)⁻¹) x = -deriv F x / (F x - R) ^ 2 := by
    intro x hx
    have hh : HasDerivAt (fun y => (F y - R)⁻¹) (-(deriv F x) / (F x - R) ^ 2) x := by
      exact ((hFan x hx).differentiableAt.hasDerivAt.sub_const R).inv (hne x hx)
    exact hh.deriv
  have hev : deriv (fun y => (F y - R)⁻¹) =ᶠ[𝓝 w] fun x => -deriv F x / (F x - R) ^ 2 :=
    Filter.eventuallyEq_of_mem (isOpen_ball.mem_nhds hw) hd1
  have hF'' : HasDerivAt (deriv F) (deriv (deriv F) w) w :=
    (hFan w hw).deriv.differentiableAt.hasDerivAt
  have hF' : HasDerivAt F (deriv F w) w := (hFan w hw).differentiableAt.hasDerivAt
  have hden := (hF'.sub_const R).pow 2
  have hq := (hF''.neg).div hden (pow_ne_zero 2 hn)
  have hq2 : deriv (fun x => -deriv F x / (F x - R) ^ 2) w = _ := hq.deriv
  simp only [Pi.pow_apply, Pi.neg_apply] at hq2
  unfold preSchwarzian
  rw [hev.deriv_eq, hq2, hd1 w hw]
  simp only [Nat.cast_ofNat, Nat.reduceSub, pow_one]
  field_simp
  ring

theorem ab112_shift_facts {F : ℂ → ℂ} (hFd : DifferentiableOn ℂ F unitDisc) (hFi : InjOn F unitDisc)
    (hFJ : IsJordanDomain (F '' unitDisc)) {M : ℝ} (hM : ∀ w ∈ unitDisc, ‖F w‖ ≤ M) :
    DifferentiableOn ℂ (fun w => (F w - ((M + 1 : ℝ) : ℂ))⁻¹) unitDisc ∧
      InjOn (fun w => (F w - ((M + 1 : ℝ) : ℂ))⁻¹) unitDisc ∧
      IsJordanDomain ((fun w => (F w - ((M + 1 : ℝ) : ℂ))⁻¹) '' unitDisc) ∧
      Bornology.IsBounded ((fun w => (F w - ((M + 1 : ℝ) : ℂ))⁻¹) '' unitDisc) ∧
      (∀ w ∈ unitDisc, F w - ((M + 1 : ℝ) : ℂ) ≠ 0) := by
  have hMnn : 0 ≤ M := (norm_nonneg _).trans (hM 0 (mem_ball_self one_pos))
  set R : ℂ := ((M + 1 : ℝ) : ℂ) with hR
  have hRn : ‖R‖ = M + 1 := by
    rw [hR, Complex.norm_real, Real.norm_of_nonneg (by linarith)]
  have hge : ∀ w ∈ unitDisc, 1 ≤ ‖F w - R‖ := by
    intro w hw
    have h1 := hM w hw
    have h2 : ‖R‖ - ‖F w‖ ≤ ‖R - F w‖ := norm_sub_norm_le R (F w)
    rw [norm_sub_rev] at h2
    linarith
  have hne : ∀ w ∈ unitDisc, F w - R ≠ 0 := fun w hw h => by
    have := hge w hw
    rw [h, norm_zero] at this
    linarith
  refine ⟨(hFd.sub_const R).inv hne, ?_, ?_, ?_, hne⟩
  · intro s hs t ht hst
    exact hFi hs ht (sub_left_inj.1 (inv_injective hst))
  · have hdet : (0 : ℂ) * (-R) - 1 * 1 ≠ 0 := by norm_num
    have key : ∀ y : ℂ, y - R ≠ 0 →
        mobiusHomeomorph 0 1 1 (-R) hdet (y : ExtPlane) = (((y - R)⁻¹ : ℂ) : ExtPlane) := by
      intro y hy
      rw [mobiusHomeomorph_apply, mobiusExt_coe (by simpa [sub_eq_add_neg] using hy)]
      congr 1
      simp [mobiusFn, sub_eq_add_neg]
    refine uq_isJordanDomain_image (mobiusHomeomorph 0 1 1 (-R) hdet) hFJ ?_
    ext x
    constructor
    · rintro ⟨p, ⟨y, ⟨w, hw, rfl⟩, rfl⟩, rfl⟩
      exact ⟨_, ⟨w, hw, rfl⟩, (key (F w) (hne w hw)).symm⟩
    · rintro ⟨_, ⟨w, hw, rfl⟩, rfl⟩
      exact ⟨(F w : ExtPlane), ⟨F w, ⟨w, hw, rfl⟩, rfl⟩, key (F w) (hne w hw)⟩
  · refine (Metric.isBounded_closedBall (x := (0 : ℂ)) (r := 1)).subset ?_
    rintro _ ⟨w, hw, rfl⟩
    rw [mem_closedBall_zero_iff]
    show ‖(F w - R)⁻¹‖ ≤ 1
    rw [norm_inv]
    exact inv_le_one_of_one_le₀ (hge w hw)

theorem ab112_logder_small {F : ℂ → ℂ} (hFd : DifferentiableOn ℂ F unitDisc) (hFi : InjOn F unitDisc)
    (hF0 : F 0 = 0) (hFJ : IsJordanDomain (F '' unitDisc))
    (hFb : Bornology.IsBounded (F '' unitDisc)) (hS : schwarzianHol F ∈ A2fun unitDisc) :
    Tendsto (fun w => ((1 - ‖w‖ ^ 2) : ℂ) * (deriv F w / F w))
      (comap (fun z : ℂ => ‖z‖) (𝓝 1) ⊓ 𝓟 unitDisc) (𝓝 0) := by
  have hF1' : ∀ w ∈ unitDisc, deriv F w ≠ 0 := fun w hw =>
    deriv_ne_zero_of_injOn isOpen_ball hFd hFi hw
  obtain ⟨M, hM⟩ := hFb.exists_norm_le
  have hM' : ∀ w ∈ unitDisc, ‖F w‖ ≤ M := fun w hw => hM _ ⟨w, hw, rfl⟩
  have hMnn : 0 ≤ M := (norm_nonneg _).trans (hM' 0 (mem_ball_self one_pos))
  obtain ⟨hf₂d, hf₂i, hf₂J, hf₂b, hne⟩ := ab112_shift_facts hFd hFi hFJ hM'
  set R : ℂ := ((M + 1 : ℝ) : ℂ) with hR
  have hRn : ‖R‖ = M + 1 := by
    rw [hR, Complex.norm_real, Real.norm_of_nonneg (by linarith)]
  have hS₂ : schwarzianHol (fun w => (F w - R)⁻¹) ∈ A2fun unitDisc := by
    refine (ab112_A2fun_congr isOpen_ball (fun w hw => ?_)).2 hS
    have hFan : AnalyticAt ℂ F w := hFd.analyticAt (isOpen_ball.mem_nhds hw)
    have h1 : AnalyticAt ℂ (fun x => (F x - R)⁻¹) w := (hFan.sub analyticAt_const).inv (hne w hw)
    have hc := schwarzian_mobius_comp_of_ne hFan (hF1' w hw) (a := 0) (b := 1) (c := 1) (d := -R)
      (by norm_num) (by simpa [sub_eq_add_neg] using hne w hw)
    have hfun : (fun x => (0 * F x + 1) / (1 * F x + -R)) = fun x => (F x - R)⁻¹ := by
      funext x
      simp [sub_eq_add_neg]
    rw [hfun, schwarzian_of_analyticAt h1, schwarzian_of_analyticAt hFan] at hc
    exact hc
  have hsmall1 := ab112_A_small hFd hFi hFJ hFb hS
  have hsmall2 := ab112_A_small hf₂d hf₂i hf₂J hf₂b hS₂
  have hT : Tendsto (fun w => ((1 - ‖w‖ ^ 2) : ℂ) * (deriv F w / (F w - R)))
      (comap (fun z : ℂ => ‖z‖) (𝓝 1) ⊓ 𝓟 unitDisc) (𝓝 0) := by
    have h : Tendsto (fun w => (((1 - ‖w‖ ^ 2) : ℂ) * preSchwarzian F w -
        ((1 - ‖w‖ ^ 2) : ℂ) * preSchwarzian (fun x => (F x - R)⁻¹) w) / 2)
        (comap (fun z : ℂ => ‖z‖) (𝓝 1) ⊓ 𝓟 unitDisc) (𝓝 0) := by
      simpa using (hsmall1.sub hsmall2).div_const 2
    refine h.congr' ?_
    filter_upwards [ab112_eventually_L] with w hw
    rw [ab112_P_inv_shift hFd hne hw.1 (hF1' w hw.1)]
    ring
  obtain ⟨δ', hδ', hfar⟩ := ab112_F_far hFd hFi hF0
  set K : ℝ := (M + ‖R‖) / δ' with hK
  have hT' : Tendsto (fun w => K * ‖((1 - ‖w‖ ^ 2) : ℂ) * (deriv F w / (F w - R))‖)
      (comap (fun z : ℂ => ‖z‖) (𝓝 1) ⊓ 𝓟 unitDisc) (𝓝 0) := by
    simpa using (tendsto_zero_iff_norm_tendsto_zero.1 hT).const_mul K
  refine squeeze_zero_norm' ?_ hT'
  filter_upwards [ab112_eventually_L] with w hw
  have hFw : δ' ≤ ‖F w‖ := hfar w hw.1 hw.2
  have hFw0 : F w ≠ 0 := norm_pos_iff.1 (lt_of_lt_of_le hδ' hFw)
  have hFR : F w - R ≠ 0 := hne w hw.1
  have e : ((1 - ‖w‖ ^ 2) : ℂ) * (deriv F w / F w) =
      (((1 - ‖w‖ ^ 2) : ℂ) * (deriv F w / (F w - R))) * ((F w - R) / F w) := by
    field_simp
  have hq : ‖(F w - R) / F w‖ ≤ K := by
    rw [norm_div, hK]
    refine div_le_div₀ (by linarith [norm_nonneg R]) ?_ hδ' hFw
    calc ‖F w - R‖ ≤ ‖F w‖ + ‖R‖ := norm_sub_le _ _
      _ ≤ M + ‖R‖ := by linarith [hM' w hw.1]
  rw [e, norm_mul, mul_comm]
  exact mul_le_mul_of_nonneg_right hq (norm_nonneg _)

/-! ### P3f: `Φ ∈ A₂¹(𝔻)` and the exterior assembly -/

theorem ab112_sq_add_le (x y : ℂ) :
    (‖x + y‖₊ : ℝ≥0∞) ^ 2 ≤ 2 * (‖x‖₊ : ℝ≥0∞) ^ 2 + 2 * (‖y‖₊ : ℝ≥0∞) ^ 2 := by
  have h0 : ‖x + y‖ ^ 2 ≤ (‖x‖ + ‖y‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (norm_add_le _ _) 2
  have h1 : ‖x + y‖ ^ 2 ≤ 2 * ‖x‖ ^ 2 + 2 * ‖y‖ ^ 2 := by
    nlinarith [sq_nonneg (‖x‖ - ‖y‖)]
  rw [ab112_enorm_sq, ab112_enorm_sq, ab112_enorm_sq]
  calc ENNReal.ofReal (‖x + y‖ ^ 2) ≤ ENNReal.ofReal (2 * ‖x‖ ^ 2 + 2 * ‖y‖ ^ 2) :=
        ENNReal.ofReal_le_ofReal h1
    _ = 2 * ENNReal.ofReal (‖x‖ ^ 2) + 2 * ENNReal.ofReal (‖y‖ ^ 2) := by
        rw [ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_mul (by norm_num),
          ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]

theorem ab112_L2w_add_ne_top {U : Set ℂ} {a b : ℂ → ℂ} {ω : ℂ → ℝ≥0∞}
    (ha : AEMeasurable a (volume.restrict U)) (hω : Measurable ω)
    (hfa : ∫⁻ z in U, (‖a z‖₊ : ℝ≥0∞) ^ 2 * ω z ≠ ∞)
    (hfb : ∫⁻ z in U, (‖b z‖₊ : ℝ≥0∞) ^ 2 * ω z ≠ ∞) :
    ∫⁻ z in U, (‖a z + b z‖₊ : ℝ≥0∞) ^ 2 * ω z ≠ ∞ := by
  have hpt : ∀ z, (‖a z + b z‖₊ : ℝ≥0∞) ^ 2 * ω z ≤
      2 * ((‖a z‖₊ : ℝ≥0∞) ^ 2 * ω z) + 2 * ((‖b z‖₊ : ℝ≥0∞) ^ 2 * ω z) := by
    intro z
    calc (‖a z + b z‖₊ : ℝ≥0∞) ^ 2 * ω z
        ≤ (2 * (‖a z‖₊ : ℝ≥0∞) ^ 2 + 2 * (‖b z‖₊ : ℝ≥0∞) ^ 2) * ω z :=
          mul_le_mul' (ab112_sq_add_le (a z) (b z)) le_rfl
      _ = _ := by ring
  refine ne_top_of_le_ne_top ?_ (lintegral_mono hpt)
  have hm : AEMeasurable (fun z => 2 * ((‖a z‖₊ : ℝ≥0∞) ^ 2 * ω z)) (volume.restrict U) :=
    (((ha.nnnorm.coe_nnreal_ennreal).pow_const 2).mul hω.aemeasurable).const_mul 2
  rw [lintegral_add_left' hm, lintegral_const_mul' 2 _ ENNReal.ofNat_ne_top,
    lintegral_const_mul' 2 _ ENNReal.ofNat_ne_top]
  exact ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top ENNReal.ofNat_ne_top hfa,
    ENNReal.mul_ne_top ENNReal.ofNat_ne_top hfb⟩

theorem ab112_normA2_ne_top {D : Set ℂ} {ψ : ℂ → ℂ} (h : normA2 D ψ < ∞) :
    ∫⁻ z in D, (‖ψ z‖₊ : ℝ≥0∞) ^ 2 * ENNReal.ofReal (rho z)⁻¹ ≠ ∞ := by
  intro hh
  unfold normA2 at h
  rw [hh, ENNReal.top_rpow_of_pos (by norm_num)] at h
  exact lt_irrefl _ h

theorem ab112_rho_inv_cont : Continuous (fun z : ℂ => (rho z)⁻¹) := by
  simp only [rho, inv_div]
  fun_prop

theorem ab112_Phi_A21 {F : ℂ → ℂ} (hFd : DifferentiableOn ℂ F unitDisc) (hFi : InjOn F unitDisc)
    (hF0 : F 0 = 0) (hFJ : IsJordanDomain (F '' unitDisc))
    (hFb : Bornology.IsBounded (F '' unitDisc)) (hS : schwarzianHol F ∈ A2fun unitDisc) :
    ∃ Φ : ℂ → ℂ, Φ ∈ A21fun unitDisc ∧
      ∀ w ∈ unitDisc, w ≠ 0 → Φ w = preSchwarzian F w - 2 * (deriv F w / F w - 1 / w) := by
  obtain ⟨Φ, hΦd, hΦ0, hΦe, hΨ⟩ := ab112_Phi_data hFd hFi hF0
  refine ⟨Φ, ?_, hΦe⟩
  have hF1' : ∀ w ∈ unitDisc, deriv F w ≠ 0 := fun w hw =>
    deriv_ne_zero_of_injOn isOpen_ball hFd hFi hw
  have hsm1 := ab112_A_small hFd hFi hFJ hFb hS
  have hsm2 := ab112_logder_small hFd hFi hF0 hFJ hFb hS
  have hn : Tendsto (fun z : ℂ => ‖z‖) (comap (fun z : ℂ => ‖z‖) (𝓝 1) ⊓ 𝓟 unitDisc) (𝓝 1) :=
    tendsto_comap.mono_left inf_le_left
  have hz1 : Tendsto (fun z : ℂ => ((1 - ‖z‖ ^ 2) : ℂ))
      (comap (fun z : ℂ => ‖z‖) (𝓝 1) ⊓ 𝓟 unitDisc) (𝓝 0) := by
    have hc : Continuous (fun r : ℝ => ((1 : ℂ) - (r : ℂ) ^ 2)) := by fun_prop
    simpa [Function.comp_def] using (hc.tendsto 1).comp hn
  have hsm3 : Tendsto (fun w : ℂ => ((1 - ‖w‖ ^ 2) : ℂ) * (1 / w))
      (comap (fun z : ℂ => ‖z‖) (𝓝 1) ⊓ 𝓟 unitDisc) (𝓝 0) := by
    have h2 : Tendsto (fun w : ℂ => 2 * ‖((1 - ‖w‖ ^ 2) : ℂ)‖)
        (comap (fun z : ℂ => ‖z‖) (𝓝 1) ⊓ 𝓟 unitDisc) (𝓝 0) := by
      simpa using (tendsto_zero_iff_norm_tendsto_zero.1 hz1).const_mul 2
    refine squeeze_zero_norm' ?_ h2
    filter_upwards [ab112_eventually_L] with w hw
    have hwpos : 0 < ‖w‖ := lt_of_lt_of_le (by norm_num) hw.2
    have hinv : ‖w‖⁻¹ ≤ 2 := by
      rw [inv_le_comm₀ hwpos (by norm_num)]
      linarith [hw.2]
    rw [norm_mul, one_div, norm_inv, mul_comm]
    exact mul_le_mul_of_nonneg_right hinv (norm_nonneg _)
  have hΦlim : Tendsto (fun w => ((1 - ‖w‖ ^ 2) : ℂ) * Φ w)
      (comap (fun z : ℂ => ‖z‖) (𝓝 1) ⊓ 𝓟 unitDisc) (𝓝 0) := by
    have h : Tendsto (fun w => ((1 - ‖w‖ ^ 2) : ℂ) * preSchwarzian F w -
        2 * (((1 - ‖w‖ ^ 2) : ℂ) * (deriv F w / F w)) + 2 * (((1 - ‖w‖ ^ 2) : ℂ) * (1 / w)))
        (comap (fun z : ℂ => ‖z‖) (𝓝 1) ⊓ 𝓟 unitDisc) (𝓝 0) := by
      simpa using (hsm1.sub (hsm2.const_mul 2)).add (hsm3.const_mul 2)
    refine h.congr' ?_
    filter_upwards [ab112_eventually_L] with w hw
    have hw0 : w ≠ 0 := norm_pos_iff.1 (lt_of_lt_of_le (by norm_num) hw.2)
    rw [hΦe w hw.1 hw0]
    ring
  have hsmall := boundary_small_of_weighted_tendsto_zero hΦlim
  refine a21_of_Psi_A2_of_boundary_small hΦd ?_ hsmall
  -- `Ψ(Φ) ∈ A₂(𝔻)`
  have hSd : DifferentiableOn ℂ (schwarzianHol F) unitDisc := hS.1
  have hPd : DifferentiableOn ℂ (PsiOp Φ) unitDisc :=
    (hΦd.deriv isOpen_ball).sub ((hΦd.pow 2).const_mul (1 / 2))
  have h0mem : (0 : ℂ) ∈ unitDisc := mem_ball_self one_pos
  set Θ : ℂ → ℂ := dslope Φ 0 with hΘ
  have hΘd : DifferentiableOn ℂ Θ unitDisc :=
    (Complex.differentiableOn_dslope (isOpen_ball.mem_nhds h0mem)).2 hΦd
  have hΘe : ∀ w, w ≠ 0 → Θ w = Φ w / w := fun w hw => by
    rw [hΘ, dslope_of_ne _ hw, slope_def_field, hΦ0, sub_zero, sub_zero]
  obtain ⟨s, hs0, hs1, hsm⟩ := hsmall
  set s' : ℝ := max s (1 / 2) with hs'
  have hs'1 : s' < 1 := max_lt hs1 (by norm_num)
  have hs'0 : 0 ≤ s' := le_max_of_le_left hs0.le
  obtain ⟨M₁, hM₁⟩ := (isCompact_closedBall (0 : ℂ) s').exists_bound_of_continuousOn
    (hΘd.continuousOn.mono (fun w hw => by
      rw [unitDisc, mem_ball_zero_iff]
      exact lt_of_le_of_lt (mem_closedBall_zero_iff.1 hw) hs'1))
  -- the pointwise weighted bound for `Θ`
  have hbound : ∀ w ∈ unitDisc, (‖(-2 : ℂ) * Θ w‖₊ : ℝ≥0∞) ^ 2 * ENNReal.ofReal (rho w)⁻¹ ≤
      ENNReal.ofReal (4 * (M₁ ^ 2 + 1) / 4) := by
    intro w hw
    have hwn : ‖w‖ < 1 := mem_ball_zero_iff.1 hw
    have hr : (rho w)⁻¹ = (1 - ‖w‖ ^ 2) ^ 2 / 4 := by
      simp only [rho, inv_div]
    have hr0 : 0 ≤ 1 - ‖w‖ ^ 2 := by nlinarith [norm_nonneg w]
    have hr1 : 1 - ‖w‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg w]
    rw [ab112_enorm_sq, ← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [hr, norm_mul, mul_pow]
    simp only [norm_neg, RCLike.norm_ofNat]
    by_cases hin : ‖w‖ ≤ s'
    · have hΘb : ‖Θ w‖ ≤ M₁ := hM₁ w (mem_closedBall_zero_iff.2 hin)
      have hM0 : 0 ≤ M₁ := (norm_nonneg _).trans hΘb
      have h1 : ‖Θ w‖ ^ 2 ≤ M₁ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hΘb 2
      have h2 : (1 - ‖w‖ ^ 2) ^ 2 ≤ 1 := by nlinarith
      nlinarith [sq_nonneg ‖Θ w‖]
    · push_neg at hin
      have hwpos : 1 / 2 < ‖w‖ := lt_of_le_of_lt (le_max_right _ _) hin
      have hw0 : w ≠ 0 := norm_pos_iff.1 (by linarith)
      have hbΦ := hsm w hw (lt_of_le_of_lt (le_max_left _ _) hin)
      have hΘn : ‖Θ w‖ = ‖Φ w‖ / ‖w‖ := by rw [hΘe w hw0, norm_div]
      have h3 : (1 - ‖w‖ ^ 2) * ‖Θ w‖ ≤ 1 := by
        rw [hΘn, ← mul_div_assoc, div_le_one (by linarith)]
        linarith
      have h4 : ((1 - ‖w‖ ^ 2) * ‖Θ w‖) ^ 2 ≤ 1 := by
        have h5 : 0 ≤ (1 - ‖w‖ ^ 2) * ‖Θ w‖ := by positivity
        nlinarith
      have e : 2 ^ 2 * ‖Θ w‖ ^ 2 * ((1 - ‖w‖ ^ 2) ^ 2 / 4) = ((1 - ‖w‖ ^ 2) * ‖Θ w‖) ^ 2 := by ring
      rw [e]
      nlinarith [sq_nonneg M₁]
  have hfb : ∫⁻ z in unitDisc, (‖(-2 : ℂ) * Θ z‖₊ : ℝ≥0∞) ^ 2 * ENNReal.ofReal (rho z)⁻¹ ≠ ∞ := by
    refine ne_top_of_le_ne_top ?_ ((setLIntegral_mono' measurableSet_ball hbound))
    rw [setLIntegral_const]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ball_lt_top).ne
  have hfa := ab112_normA2_ne_top hS.2
  have hωm : Measurable (fun z : ℂ => ENNReal.ofReal (rho z)⁻¹) :=
    ENNReal.measurable_ofReal.comp ab112_rho_inv_cont.measurable
  have hadd := ab112_L2w_add_ne_top (U := unitDisc) (a := schwarzianHol F)
    (b := fun z => (-2 : ℂ) * Θ z) (ω := fun z => ENNReal.ofReal (rho z)⁻¹)
    (hSd.continuousOn.aemeasurable measurableSet_ball) hωm hfa hfb
  refine ⟨hPd, ?_⟩
  have hae : ∀ᵐ z ∂(volume.restrict unitDisc),
      (‖PsiOp Φ z‖₊ : ℝ≥0∞) ^ 2 * ENNReal.ofReal (rho z)⁻¹ =
        (‖schwarzianHol F z + (-2 : ℂ) * Θ z‖₊ : ℝ≥0∞) ^ 2 * ENNReal.ofReal (rho z)⁻¹ := by
    refine (ae_restrict_iff' (show MeasurableSet unitDisc from measurableSet_ball)).2 ?_
    filter_upwards [(Set.countable_singleton (0 : ℂ)).ae_notMem volume] with z hz0 hz
    have hz0' : z ≠ 0 := hz0
    have : PsiOp Φ z = schwarzianHol F z + (-2 : ℂ) * Θ z := by
      rw [hΨ z hz hz0', hΘe z hz0']
      ring
    rw [this]
  have hfin : ∫⁻ z in unitDisc, (‖PsiOp Φ z‖₊ : ℝ≥0∞) ^ 2 * ENNReal.ofReal (rho z)⁻¹ ≠ ∞ := by
    rw [lintegral_congr_ae hae]
    exact hadd
  exact ENNReal.rpow_lt_top_of_nonneg (by norm_num) hfin

/-- **P3c.** `𝒜(g) ∈ A₂¹(𝔻*)`, for `g = c + 1/F(1/z)`. -/
theorem ab112_g_part {g : ℂ → ℂ} (hg : IsUnivalentAtInfty g)
    (hJg : IsJordanCurve (toExt (frontier (g '' unitDiscExterior))))
    (hS : schwarzianHol g ∈ A2fun unitDiscExterior) :
    preSchwarzian g ∈ A21fun unitDiscExterior := by
  obtain ⟨c, F, hFd, hFi, hFJ, hFb, hF0, hrel⟩ := ab112_g_to_f hg hJg
  have hSF := ab112_schwarzian_transfer hFd hFi hF0 hrel hS
  obtain ⟨Φ, hΦ, hΦe⟩ := ab112_Phi_A21 hFd hFi hF0 hFJ hFb hSF
  obtain ⟨hgd, hgi, -⟩ := hg
  have hopenE : IsOpen unitDiscExterior := isOpen_lt continuous_const continuous_norm
  have hE : IsOpen (unitDisc \ {0}) := isOpen_ball.sdiff isClosed_singleton
  obtain ⟨hF1, hF0'⟩ := ab112_F_facts hFd hFi hF0
  have hgd1 : ∀ w ∈ unitDiscExterior, deriv g w ≠ 0 := fun w hw =>
    deriv_ne_zero_of_injOn hopenE hgd hgi hw
  have hAd := ab112_P_diff hopenE hgd hgd1
  have hrelA : ∀ z ∈ unitDiscExterior, preSchwarzian g z = -(z ^ 2)⁻¹ * Φ z⁻¹ := by
    intro z hz
    have hz1 : 1 < ‖z‖ := hz
    have hz0 : z ≠ 0 := fun h => by simp [h] at hz1; linarith
    have hsE : z⁻¹ ∈ unitDisc \ {0} :=
      ⟨mem_ball_zero_iff.2 (by rw [norm_inv]; exact inv_lt_one_of_one_lt₀ hz1), inv_ne_zero hz0⟩
    rw [ab112_P_eqOn hopenE (ab112_g_eq hrel) hz, ab112_P_add_const,
      s2c_A_inv hE (hFd.mono Set.sdiff_subset) hF0' hF1 hz0 hsE, hΦe z⁻¹ hsE.1 hsE.2]
    ring
  refine (ab112_mem_A21_iff hAd).2 ?_
  rw [ab112_inv_lintegral, setLIntegral_congr s2c_null_sdiff]
  refine ne_of_eq_of_ne ?_ (a21_sq_lintegral_ne_top hΦ)
  refine lintegral_congr_ae ?_
  refine (ae_restrict_iff' (show MeasurableSet unitDisc from measurableSet_ball)).2 ?_
  filter_upwards [(Set.countable_singleton (0 : ℂ)).ae_notMem volume] with u hu0 hu
  have hu0' : u ≠ 0 := hu0
  have hn : ‖u‖ ≠ 0 := norm_ne_zero_iff.2 hu0'
  have hz : u⁻¹ ∈ unitDiscExterior := by
    show 1 < ‖u⁻¹‖
    rw [norm_inv]
    exact (one_lt_inv₀ (norm_pos_iff.2 hu0')).2 (mem_ball_zero_iff.1 hu)
  rw [hrelA u⁻¹ hz, inv_inv, ab112_enorm_sq ((-((u⁻¹) ^ 2)⁻¹) * Φ u), ab112_enorm_sq (Φ u),
    ← ENNReal.ofReal_mul (by positivity), norm_mul, norm_neg, norm_inv, norm_pow, norm_inv]
  congr 1
  field_simp

/-- **Lemma 1.11** (TT:3666). Let `f`, `g` be univalent on `𝔻`, `𝔻*` with `𝒮(f) ∈ A₂(𝔻)` and `𝒮(g) ∈ A₂(𝔻*)`. Then
`𝒜(f) ∈ A₂¹(𝔻)` and `𝒜(g) ∈ A₂¹(𝔻*)`.

[CORRECTION 2026-10-25] The proof (TT:3666–3734) applies Theorem 1.6, so the images must be Jordan domains in `ℂ`:
- `f(𝔻)` is a bounded Jordan domain;
- `g(∞) = ∞` and the boundary of `g(𝔻*)` is a Jordan curve in `ℂ`.

Without them the disk clause fails for `f(z) = z/(1 - z)`: `𝒮(f) = 0`, but `𝒜(f) ∉ A₂¹(𝔻)` (lean4,
`collaboration/lean4/Lemma111DiskDiagnostic.lean`). These hypotheses hold for the welding pairs of Theorem 1.12.

[CORRECTION 2026-10-26] The Jordan hypothesis on `g` takes the frontier in `ℂ`. The earlier form, with the frontier
taken in `ℂ̄`, was unsatisfiable: `∞` is an isolated point of that frontier (found by 下属4). -/
theorem ab112_lemma_1_11 {f g : ℂ → ℂ} (hf : DifferentiableOn ℂ f unitDisc) (hfi : InjOn f unitDisc)
    (hJf : IsJordanDomain (f '' unitDisc)) (hbf : Bornology.IsBounded (f '' unitDisc))
    (hg : IsUnivalentAtInfty g) (hJg : IsJordanCurve (toExt (frontier (g '' unitDiscExterior))))
    (hSf : schwarzianHol f ∈ A2fun unitDisc) (hSg : schwarzianHol g ∈ A2fun unitDiscExterior) :
    preSchwarzian f ∈ A21fun unitDisc ∧ preSchwarzian g ∈ A21fun unitDiscExterior :=
  ⟨ab112_lemma_1_11_f hf hfi hJf hbf hSf, ab112_g_part hg hJg hSg⟩

/-- **Lemma 1.11** (TT:3666). Let `f`, `g` be univalent on `𝔻`, `𝔻*` with `𝒮(f) ∈ A₂(𝔻)` and `𝒮(g) ∈ A₂(𝔻*)`. Then
`𝒜(f) ∈ A₂¹(𝔻)` and `𝒜(g) ∈ A₂¹(𝔻*)`.

[CORRECTION 2026-10-25] The proof (TT:3666–3734) applies Theorem 1.6, so the images must be Jordan domains in `ℂ`:
- `f(𝔻)` is a bounded Jordan domain;
- `g(∞) = ∞` and the boundary of `g(𝔻*)` is a Jordan curve in `ℂ`.

Without them the disk clause fails for `f(z) = z/(1 - z)`: `𝒮(f) = 0`, but `𝒜(f) ∉ A₂¹(𝔻)` (lean4,
`collaboration/lean4/Lemma111DiskDiagnostic.lean`). These hypotheses hold for the welding pairs of Theorem 1.12.

[CORRECTION 2026-10-26] The Jordan hypothesis on `g` takes the frontier in `ℂ`. The earlier form, with the frontier
taken in `ℂ̄`, was unsatisfiable: `∞` is an isolated point of that frontier (found by 下属4). -/
theorem lemma_1_11 {f g : ℂ → ℂ} (hf : DifferentiableOn ℂ f unitDisc) (hfi : InjOn f unitDisc)
    (hJf : IsJordanDomain (f '' unitDisc)) (hbf : Bornology.IsBounded (f '' unitDisc))
    (hg : IsUnivalentAtInfty g) (hJg : IsJordanCurve (toExt (frontier (g '' unitDiscExterior))))
    (hSf : schwarzianHol f ∈ A2fun unitDisc) (hSg : schwarzianHol g ∈ A2fun unitDiscExterior) :
    preSchwarzian f ∈ A21fun unitDisc ∧ preSchwarzian g ∈ A21fun unitDiscExterior :=
  ab112_lemma_1_11 hf hfi hJf hbf hg hJg hSf hSg

end Ch2
end TakhtajanTeo
