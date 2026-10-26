import Muon.Volatility.Half
import Muon.Volatility.OddSpectral
import Muon.Volatility.Defs
import Muon.Setup.Residual
import Muon.Setup.Regime

/-!
# Appendix D, part 7: replacement of the residuals

Work package L-D.7 (interface draft). Snapshot `cr-2026-10-23`. Source of record:
`sections/04-volatility/section.tex`: `lem:app-vol-scalar-weak` (l.671–678),
`lem:app-vol-replacement` (l.697–708) and `cor:app-vol-filtered-replacement` (l.826–839).
Card: `sections/04-volatility/CARD.md` §2, §3, §5 (row L-D.7).

Reused, not redefined: `contraction`, `contractionRes`, `omegaF`, `iotaF` (`Muon.Volatility`, OddSpectral);
`def_app_vol_lag`, `def_app_vol_product`, `indepUpd`, `indepSpaceLaw` (Defs); `frozenBuf`, `frozenUpd`,
`FrozenParams`, `FrozenSamples`, `SetupRegime` (`Muon.Setup`); `resid`, `gaussPair` (Setup.Model,
Setup.Residual); `Muon.mean`, `Muon.fro`, `Muon.opNorm`.

Encoding decisions:
* The regime is `R : SetupRegime` with the sequence index `k : ℕ`, `Ω : ℕ → Type` and probability laws
  `P : ∀ k, Measure (Ω k)`, as in `Half.lean`. The state of the scalar comparison is `(R.F k).A`
  (`‖A‖_F = 1` and `‖A‖ → 0` come from `FrozenParams.hA` and `R.diffuse`).
* Every "sup → 0" conclusion is stated as the existence of a real sequence `ε : ℕ → ℝ` with
  `Tendsto ε atTop (𝓝 0)` and a uniform bound `≤ ε k` (or `≤ 2 * ε k`). This is equivalent to the
  paper's sup statement and avoids the `sSup` junk value.
* `lem:app-vol-scalar-weak` is stated as "for every `ε > 0`, eventually in `k`, uniformly in `θ`", the
  same content as `sup_θ |…| → 0`, with no `sSup` and no `BddAbove` side condition.
* `lem_app_vol_replacement` is uniform, as in `lem_app_de_replace`: `ε_B(𝒥)` depends only on `𝒥`, `C_Σ`,
  `γ⋆` and the state sequence `A` (`hA`, `hAn`). It is chosen before the frozen data `Fp`, the probability
  space, the samples, `t`, `ℓ`, `s`, `u`, `F`, `G`. `lem_app_vol_replacement_regime` is the regime form
  (specialization `A k := (R.F k).A`), used by the filtered replacement.
* Tested contractions are `contractionRes` (𝒦_{s,u} = 𝒦[ι_s, ι_u]) and `contraction` with `omegaF`
  (𝒦[ω_ϱ, ω_ϱ']). The frozen buffer is `frozenBuf (R.F k) (S k) t` (the `M_t` of
  `def:app-setup-frozen`); the independent buffer is `def_app_vol_product (R.F k) ω t` on
  `indepSpaceLaw`.
* `cor:app-vol-filtered-replacement` has two parts. `_i` is the first display (all `F, G` of norm at
  most one, all ridges in `I = [R.ϱlo, R.ϱhi]`). `_ii` is the second display: it carries the
  section-C input `ε_B` as an explicit sequence `εB` and the mean bound `hmean` (the bound
  `‖𝔼 S_t(ϱ)‖_F ≤ C_Σ ϱ₋^{-1/2} + ε_B` of `thm:app-drift-mean`, quantified over all times, as in
  `Half.lean`). It also requires `F`, `G` symmetric as the source does. The independent covariance
  `C^g_ℓ` is written literally as in the source, with the uncentred `indepUpd` (the updates have
  mean zero).
* The sup over `ϱ, ϱ' ∈ I` in `_ii` is written as a `∀` over `ϱ, ϱ' ∈ Icc R.ϱlo R.ϱhi`.
-/

set_option linter.style.longLine false

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped Matrix MatrixOrder ENNReal
open Matrix
open Muon Muon.Setup Muon.DetEquiv

noncomputable section

namespace Muon.Volatility

/-- Uniform approximation on a bounded window by a finite net of parameters. -/
private lemma net_window {Θ : Type*} [MetricSpace Θ] [CompactSpace Θ] (ψ : Θ → ℝ → ℂ)
    (hψ : Continuous fun p : Θ × ℝ => ψ p.1 p.2) (M ε : ℝ) (hε : 0 < ε) :
    ∃ S : Finset Θ, ∀ θ : Θ, ∃ θ' ∈ S, ∀ x : ℝ, |x| ≤ M → ‖ψ θ x - ψ θ' x‖ ≤ ε := by
  have hK : IsCompact (univ ×ˢ Icc (-M) M : Set (Θ × ℝ)) :=
    isCompact_univ.prod isCompact_Icc
  have hU := hK.uniformContinuousOn_of_continuous hψ.continuousOn
  rw [Metric.uniformContinuousOn_iff] at hU
  obtain ⟨δ, hδ, hδP⟩ := hU ε hε
  obtain ⟨S, hS⟩ := (isCompact_univ : IsCompact (univ : Set Θ)).elim_finite_subcover
    (fun θ : Θ => Metric.ball θ δ) (fun _ => Metric.isOpen_ball)
    (fun θ _ => mem_iUnion.2 ⟨θ, Metric.mem_ball_self hδ⟩)
  refine ⟨S, fun θ => ?_⟩
  have hθ : θ ∈ ⋃ i ∈ S, Metric.ball i δ := hS (mem_univ θ)
  obtain ⟨i, hiS, hi⟩ := mem_iUnion₂.1 hθ
  refine ⟨i, hiS, fun x hx => ?_⟩
  have hxI : x ∈ Icc (-M) M := abs_le.1 hx
  have := hδP (θ, x) ⟨mem_univ _, hxI⟩ (i, x) ⟨mem_univ _, hxI⟩ (by
    rw [Prod.dist_eq, dist_self]
    simpa [Metric.mem_ball, dist_comm] using hi)
  simpa [dist_eq_norm] using this.le

/-- Bounded continuous real test functions: convergence of expectations from `lem_app_setup_residual_iii`. -/
private lemma weak_bdd_real {m n : ℕ → ℕ} {Ω : ℕ → Type*} [∀ k, MeasurableSpace (Ω k)]
    (P : ∀ k, Measure (Ω k)) [∀ k, IsProbabilityMeasure (P k)]
    (A : ∀ k, Mat (m k) (n k)) (z : ∀ k, Ω k → Vec (m k)) (w : ∀ k, Ω k → Vec (n k))
    (hlaw : ∀ k, (P k).map (fun ω => (z k ω, w k ω)) = gaussPair (m k) (n k))
    (hA : ∀ k, fro (A k) = 1) (hAn : Tendsto (fun k => opNorm (A k)) atTop (𝓝 0))
    (φ : ℝ → ℝ) (hφ : Continuous φ) (C : ℝ) (hC : ∀ x, |φ x| ≤ C) :
    Tendsto (fun k => ∫ ω, φ (resid (A k) (z k ω, w k ω)) ∂(P k)) atTop
      (𝓝 (∫ x, φ x ∂(gaussianReal 0 1))) := by
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC 0)
  have hcpos : (0 : ℝ) < C + 1 := by linarith
  have hψ := (lem_app_setup_residual_iii P A z w hlaw hA hAn).2 (fun x => φ x / (C + 1))
    (by fun_prop) (by
      intro x
      rw [abs_div, abs_of_pos hcpos, div_le_iff₀ hcpos]
      nlinarith [hC x, sq_nonneg x])
  have e1 : ∀ k, ∫ ω, φ (resid (A k) (z k ω, w k ω)) ∂(P k)
      = (C + 1) * ∫ ω, φ (resid (A k) (z k ω, w k ω)) / (C + 1) ∂(P k) := fun k => by
    rw [integral_div, mul_div_cancel₀ _ hcpos.ne']
  have e2 : ∫ x, φ x ∂(gaussianReal 0 1) = (C + 1) * ∫ x, φ x / (C + 1) ∂(gaussianReal 0 1) := by
    rw [integral_div, mul_div_cancel₀ _ hcpos.ne']
  rw [e2]
  exact (hψ.const_mul (C + 1)).congr (fun k => (e1 k).symm)

private lemma vsw_one_add_pow6 (t : ℝ) (ht : 0 ≤ t) : (1 + t) ^ 6 ≤ 32 * (1 + t ^ 6) := by
  have h1 : (1 + t) ^ 2 ≤ 2 * (1 + t ^ 2) := by nlinarith [sq_nonneg (t - 1)]
  have h2 : (1 + t ^ 2) ^ 3 ≤ 4 * (1 + (t ^ 2) ^ 3) := by
    nlinarith [sq_nonneg (t ^ 2 - 1), sq_nonneg (t ^ 2), mul_nonneg (sq_nonneg t) (sq_nonneg (t ^ 2 - 1))]
  calc (1 + t) ^ 6 = ((1 + t) ^ 2) ^ 3 := by ring
    _ ≤ (2 * (1 + t ^ 2)) ^ 3 := pow_le_pow_left₀ (by positivity) h1 3
    _ = 8 * (1 + t ^ 2) ^ 3 := by ring
    _ ≤ 8 * (4 * (1 + (t ^ 2) ^ 3)) := by linarith
    _ = 32 * (1 + t ^ 6) := by ring

private lemma vsw_sqpow (n q : ℕ) :
    Integrable (fun z : Vec n => (∑ i, z i ^ 2) ^ q) (Muon.Foundations.stdGaussianPi n) := by
  rcases Nat.eq_zero_or_pos q with rfl | hq
  · simp
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [zero_pow hq.ne']
  refine Integrable.of_integral_ne_zero ?_
  rw [Muon.Foundations.stdGaussianPi_sq_norm_moment n q hq]
  refine (Finset.prod_pos fun j _ => ?_).ne'
  positivity

private lemma vsw_int6 {m n : ℕ} (A : Mat m n) (hA : fro A = 1) :
    Integrable (fun x => resid A x ^ 6) (gaussPair m n) := by
  have hF : ∑ i, ∑ j, ‖A i j‖ ^ 2 = 1 := by
    have := hA
    unfold fro at this
    rwa [Real.sqrt_eq_one] at this
  have hmeas : Measurable (fun x : Vec m × Vec n => resid A x ^ 6) := by
    unfold resid dotProduct Matrix.mulVec dotProduct; fun_prop
  have hint := (vsw_sqpow m 3).mul_prod (vsw_sqpow n 3)
  unfold gaussPair
  refine hint.mono' hmeas.aestronglyMeasurable (Filter.Eventually.of_forall fun x => ?_)
  obtain ⟨z, w⟩ := x
  simp only
  have hrow : ∀ i, (A *ᵥ w) i ^ 2 ≤ (∑ j, A i j ^ 2) * ∑ j, w j ^ 2 := by
    intro i
    simp only [Matrix.mulVec, dotProduct]
    exact Finset.sum_mul_sq_le_sq_mul_sq _ _ _
  have hAw : ∑ i, (A *ᵥ w) i ^ 2 ≤ ∑ j, w j ^ 2 := by
    calc ∑ i, (A *ᵥ w) i ^ 2 ≤ ∑ i, (∑ j, A i j ^ 2) * ∑ j, w j ^ 2 :=
          Finset.sum_le_sum fun i _ => hrow i
      _ = (∑ i, ∑ j, A i j ^ 2) * ∑ j, w j ^ 2 := by rw [Finset.sum_mul]
      _ = ∑ j, w j ^ 2 := by
          have : ∑ i, ∑ j, A i j ^ 2 = 1 := by simpa using hF
          rw [this, one_mul]
  have hr2 : resid A (z, w) ^ 2 ≤ (∑ i, z i ^ 2) * ∑ j, w j ^ 2 := by
    have h1 : resid A (z, w) ^ 2 ≤ (∑ i, z i ^ 2) * ∑ i, (A *ᵥ w) i ^ 2 := by
      unfold resid dotProduct
      exact Finset.sum_mul_sq_le_sq_mul_sq _ _ _
    have h0 : 0 ≤ ∑ i, z i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
    exact h1.trans (mul_le_mul_of_nonneg_left hAw h0)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  calc resid A (z, w) ^ 6 = (resid A (z, w) ^ 2) ^ 3 := by ring
    _ ≤ ((∑ i, z i ^ 2) * ∑ j, w j ^ 2) ^ 3 := pow_le_pow_left₀ (sq_nonneg _) hr2 3
    _ = _ := by ring


private lemma vsw_pair {m n : ℕ} {Ω : Type*} [MeasurableSpace Ω] (A : Mat m n) (hA : fro A = 1)
    (P : Measure Ω) [IsProbabilityMeasure P] (z : Ω → Vec m) (w : Ω → Vec n)
    (hlaw : P.map (fun ω => (z ω, w ω)) = gaussPair m n) :
    AEMeasurable (fun ω => (z ω, w ω)) P := by
  by_contra h
  have hne : Nonempty (Fin m) := by
    by_contra hc
    rw [not_nonempty_iff] at hc
    unfold fro at hA
    simp at hA
  obtain ⟨i0⟩ := hne
  have e := hlaw
  rw [Measure.map_of_not_aemeasurable_of_ne_zero h (IsProbabilityMeasure.ne_zero P)] at e
  have e2 := congrArg (Measure.map Prod.fst) e
  rw [Measure.map_dirac' measurable_fst _] at e2
  unfold gaussPair at e2
  rw [Measure.map_fst_prod] at e2
  simp only [measure_univ, one_smul] at e2
  have e3 := congrArg (Measure.map (Function.eval i0)) e2
  rw [Measure.map_dirac' (measurable_pi_apply i0) _] at e3
  unfold Muon.Foundations.stdGaussianPi at e3
  rw [Measure.pi_map_eval] at e3
  simp only [measure_univ, Finset.prod_const_one, one_smul] at e3
  have hsing : ∀ a : ℝ, gaussianReal 0 1 {a} = 0 := fun a =>
    gaussianReal_absolutelyContinuous 0 one_ne_zero Real.volume_singleton
  obtain ⟨a, ha⟩ : ∃ a : ℝ, Measure.dirac a = gaussianReal 0 1 := ⟨_, e3⟩
  have h7 := hsing a
  rw [← ha, Measure.dirac_apply_of_mem (Set.mem_singleton a)] at h7
  norm_num at h7

/-- Sample facts about the residual: measurability, integrability and the uniform sixth-moment bound. -/
private lemma vsw_sample {m n : ℕ} {Ω : Type*} [MeasurableSpace Ω] (A : Mat m n) (hA : fro A = 1)
    (P : Measure Ω) [IsProbabilityMeasure P] (z : Ω → Vec m) (w : Ω → Vec n)
    (hlaw : P.map (fun ω => (z ω, w ω)) = gaussPair m n) :
    AEMeasurable (fun ω => resid A (z ω, w ω)) P ∧
    Integrable (fun ω => (1 + |resid A (z ω, w ω)|) ^ 6) P ∧
    ∫ ω, (1 + |resid A (z ω, w ω)|) ^ 6 ∂P ≤ 7232 := by
  have hm : Measurable (fun x : Vec m × Vec n => resid A x) := by
    unfold resid dotProduct Matrix.mulVec dotProduct; fun_prop
  have hpair := vsw_pair A hA P z w hlaw
  have hD : AEMeasurable (fun ω => resid A (z ω, w ω)) P := hm.comp_aemeasurable hpair
  have hmap : P.map (fun ω => resid A (z ω, w ω)) = (gaussPair m n).map (resid A) := by
    rw [← hlaw]
    exact (AEMeasurable.map_map_of_aemeasurable hm.aemeasurable hpair).symm
  have hg : Measurable (fun x : ℝ => (1 + |x|) ^ 6) := by fun_prop
  have hI6 := vsw_int6 A hA
  have hpt : ∀ x, (1 + |resid A x|) ^ 6 ≤ 32 * (1 + resid A x ^ 6) := fun x => by
    have := vsw_one_add_pow6 |resid A x| (abs_nonneg _)
    rwa [show |resid A x| ^ 6 = resid A x ^ 6 from (Even.pow_abs ⟨3, rfl⟩ _)] at this
  have hIg : Integrable (fun x => (1 + |resid A x|) ^ 6) (gaussPair m n) := by
    refine (((integrable_const (1:ℝ)).add hI6).const_mul 32).mono' (by fun_prop : Measurable fun x : Vec m × Vec n => (1 + |resid A x|) ^ 6).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact hpt x
  refine ⟨hD, ?_, ?_⟩
  · have h1 : Integrable (fun x : ℝ => (1 + |x|) ^ 6) (P.map (fun ω => resid A (z ω, w ω))) := by
      rw [hmap, integrable_map_measure hg.aestronglyMeasurable hm.aemeasurable]
      exact hIg
    rwa [integrable_map_measure hg.aestronglyMeasurable hD] at h1
  · have e1 : ∫ ω, (1 + |resid A (z ω, w ω)|) ^ 6 ∂P
        = ∫ x, (1 + |resid A x|) ^ 6 ∂(gaussPair m n) := by
      rw [← integral_map hD hg.aestronglyMeasurable, hmap,
        integral_map hm.aemeasurable hg.aestronglyMeasurable]
    rw [e1]
    have h6 : ∫ x, resid A x ^ 6 ∂(gaussPair m n) ≤ 225 := by
      have := (lem_app_setup_residual_i A hA).2.2.2.2 3 (by norm_num)
      have e : ∀ x, |resid A x| ^ (2 * 3) = resid A x ^ 6 := fun x => Even.pow_abs ⟨3, rfl⟩ _
      simp only [e] at this
      have h15 : ((Nat.doubleFactorial (2 * 3 - 1) : ℕ) : ℝ) = 15 := by
        norm_num [Nat.doubleFactorial]
      rw [h15] at this
      linarith
    calc ∫ x, (1 + |resid A x|) ^ 6 ∂(gaussPair m n)
        ≤ ∫ x, 32 * (1 + resid A x ^ 6) ∂(gaussPair m n) :=
          integral_mono hIg (((integrable_const (1:ℝ)).add hI6).const_mul 32) hpt
      _ = 32 * (1 + ∫ x, resid A x ^ 6 ∂(gaussPair m n)) := by
          rw [integral_const_mul, integral_add (integrable_const 1) hI6]
          simp
      _ ≤ 7232 := by linarith


private lemma vsw_clamp_abs (M x : ℝ) (hM : 0 ≤ M) : |max (-M) (min M x)| ≤ M ∧
    |max (-M) (min M x)| ≤ |x| ∧ (|x| ≤ M → max (-M) (min M x) = x) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [abs_le]; constructor
    · exact le_max_left _ _
    · exact max_le (by linarith) (min_le_left _ _)
  · have h0 := abs_nonneg x
    have h1 := le_abs_self x
    have h2 := neg_abs_le x
    rw [abs_le]; constructor
    · rcases le_total M |x| with h | h
      · exact le_max_of_le_left (by linarith)
      · exact le_max_of_le_right (le_min (by linarith) h2)
    · exact max_le (by linarith) ((min_le_right _ _).trans h1)
  · intro h
    have h1 := abs_le.1 h
    rw [min_eq_right h1.2, max_eq_right h1.1]

private lemma vsw_tail_pt (g : ℝ → ℂ) (C : ℝ) (hC : 0 ≤ C) (hb : ∀ x, ‖g x‖ ≤ C * (1 + |x|) ^ 4)
    (M : ℝ) (hM : 0 ≤ M) (x : ℝ) :
    ‖g x - g (max (-M) (min M x))‖ ≤ 2 * C * (1 + |x|) ^ 6 / (1 + M) ^ 2 := by
  obtain ⟨-, h2, h3⟩ := vsw_clamp_abs M x hM
  have hp : 0 < (1 + M) ^ 2 := by positivity
  rw [le_div_iff₀ hp]
  by_cases hx : |x| ≤ M
  · rw [h3 hx, sub_self, norm_zero, zero_mul]
    positivity
  · rw [not_le] at hx
    have e1 : (1 + M) ^ 2 * (1 + |x|) ^ 4 ≤ (1 + |x|) ^ 6 := by
      have : (1 + M) ^ 2 ≤ (1 + |x|) ^ 2 := pow_le_pow_left₀ (by positivity) (by linarith) 2
      calc (1 + M) ^ 2 * (1 + |x|) ^ 4 ≤ (1 + |x|) ^ 2 * (1 + |x|) ^ 4 :=
            mul_le_mul_of_nonneg_right this (by positivity)
        _ = (1 + |x|) ^ 6 := by ring
    have e2 : (1 + |max (-M) (min M x)|) ^ 4 ≤ (1 + |x|) ^ 4 :=
      pow_le_pow_left₀ (by positivity) (by linarith) 4
    have e3 : ‖g x - g (max (-M) (min M x))‖ ≤ 2 * C * (1 + |x|) ^ 4 := by
      calc _ ≤ ‖g x‖ + ‖g (max (-M) (min M x))‖ := norm_sub_le _ _
        _ ≤ C * (1 + |x|) ^ 4 + C * (1 + |x|) ^ 4 :=
          add_le_add (hb x) ((hb _).trans (mul_le_mul_of_nonneg_left e2 hC))
        _ = _ := by ring
    calc ‖g x - g (max (-M) (min M x))‖ * (1 + M) ^ 2
        ≤ 2 * C * (1 + |x|) ^ 4 * (1 + M) ^ 2 := mul_le_mul_of_nonneg_right e3 hp.le
      _ = 2 * C * ((1 + M) ^ 2 * (1 + |x|) ^ 4) := by ring
      _ ≤ 2 * C * (1 + |x|) ^ 6 := mul_le_mul_of_nonneg_left e1 (by positivity)

private lemma vsw_integrable_comp {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (X : α → ℝ) (hX : AEMeasurable X μ) (hI : Integrable (fun a => (1 + |X a|) ^ 6) μ)
    (g : ℝ → ℂ) (hg : Continuous g) (B : ℝ) (hb : ∀ x, ‖g x‖ ≤ B * (1 + |x|) ^ 6) :
    Integrable (fun a => g (X a)) μ :=
  (hI.const_mul B).mono' (hg.aestronglyMeasurable.comp_aemeasurable hX)
    (Filter.Eventually.of_forall fun a => hb (X a))

private lemma vsw_tail_int {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
    (X : α → ℝ) (hX : AEMeasurable X μ) (hI : Integrable (fun a => (1 + |X a|) ^ 6) μ)
    (K : ℝ) (hK : ∫ a, (1 + |X a|) ^ 6 ∂μ ≤ K)
    (g : ℝ → ℂ) (hg : Continuous g) (C : ℝ) (hC : 0 ≤ C) (hb : ∀ x, ‖g x‖ ≤ C * (1 + |x|) ^ 4)
    (M : ℝ) (hM : 0 ≤ M) :
    ‖(∫ a, g (X a) ∂μ) - ∫ a, g (max (-M) (min M (X a))) ∂μ‖ ≤ 2 * C * K / (1 + M) ^ 2 := by
  have hp : 0 < (1 + M) ^ 2 := by positivity
  have h6 : ∀ x : ℝ, C * (1 + |x|) ^ 4 ≤ C * (1 + |x|) ^ 6 := fun x =>
    mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by linarith [abs_nonneg x]) (by norm_num)) hC
  have hcont : Continuous fun x : ℝ => g (max (-M) (min M x)) := by fun_prop
  have hi1 := vsw_integrable_comp μ X hX hI g hg C (fun x => (hb x).trans (h6 x))
  have hi2 := vsw_integrable_comp μ X hX hI _ hcont C (fun x => by
    have := vsw_clamp_abs M x hM
    calc _ ≤ C * (1 + |max (-M) (min M x)|) ^ 4 := hb _
      _ ≤ C * (1 + |x|) ^ 4 := mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (by positivity) (by linarith [this.2.1]) 4) hC
      _ ≤ _ := h6 x)
  rw [← integral_sub hi1 hi2]
  have hbd : Integrable (fun a => 2 * C / (1 + M) ^ 2 * (1 + |X a|) ^ 6) μ := hI.const_mul _
  calc _ ≤ ∫ a, 2 * C / (1 + M) ^ 2 * (1 + |X a|) ^ 6 ∂μ :=
        norm_integral_le_of_norm_le hbd (Filter.Eventually.of_forall fun a => by
          have := vsw_tail_pt g C hC hb M hM (X a)
          calc _ ≤ _ := this
            _ = _ := by ring)
    _ = 2 * C / (1 + M) ^ 2 * ∫ a, (1 + |X a|) ^ 6 ∂μ := integral_const_mul _ _
    _ ≤ 2 * C / (1 + M) ^ 2 * K := mul_le_mul_of_nonneg_left hK (by positivity)
    _ = _ := by ring

private lemma vsw_clamp_bd (g : ℝ → ℂ) (C : ℝ) (hC : 0 ≤ C) (hb : ∀ x, ‖g x‖ ≤ C * (1 + |x|) ^ 4)
    (M : ℝ) (hM : 0 ≤ M) (x : ℝ) : ‖g (max (-M) (min M x))‖ ≤ C * (1 + |x|) ^ 6 := by
  have := vsw_clamp_abs M x hM
  calc _ ≤ C * (1 + |max (-M) (min M x)|) ^ 4 := hb _
    _ ≤ C * (1 + |x|) ^ 4 := mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (by positivity) (by linarith [this.2.1]) 4) hC
    _ ≤ _ := mul_le_mul_of_nonneg_left
        (pow_le_pow_right₀ (by linarith [abs_nonneg x]) (by norm_num)) hC

private lemma vsw_net_int {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
    (X : α → ℝ) (hX : AEMeasurable X μ) (hI : Integrable (fun a => (1 + |X a|) ^ 6) μ)
    (g1 g2 : ℝ → ℂ) (h1 : Continuous g1) (h2 : Continuous g2) (B : ℝ)
    (hb1 : ∀ x, ‖g1 x‖ ≤ B * (1 + |x|) ^ 6) (hb2 : ∀ x, ‖g2 x‖ ≤ B * (1 + |x|) ^ 6)
    (η : ℝ) (hη : ∀ x, ‖g1 x - g2 x‖ ≤ η) :
    ‖(∫ a, g1 (X a) ∂μ) - ∫ a, g2 (X a) ∂μ‖ ≤ η := by
  rw [← integral_sub (vsw_integrable_comp μ X hX hI g1 h1 B hb1)
    (vsw_integrable_comp μ X hX hI g2 h2 B hb2)]
  calc _ ≤ ∫ a, η ∂μ := norm_integral_le_of_norm_le (integrable_const η)
        (Filter.Eventually.of_forall fun a => hη (X a))
    _ = η := by simp

private lemma vsw_conv {m n : ℕ → ℕ} {Ω : ℕ → Type*} [∀ k, MeasurableSpace (Ω k)]
    (P : ∀ k, Measure (Ω k)) [∀ k, IsProbabilityMeasure (P k)]
    (A : ∀ k, Mat (m k) (n k)) (z : ∀ k, Ω k → Vec (m k)) (w : ∀ k, Ω k → Vec (n k))
    (hlaw : ∀ k, (P k).map (fun ω => (z k ω, w k ω)) = gaussPair (m k) (n k))
    (hA : ∀ k, fro (A k) = 1) (hAn : Tendsto (fun k => opNorm (A k)) atTop (𝓝 0))
    (h : ℝ → ℂ) (hh : Continuous h) (Bd : ℝ) (hb : ∀ x, ‖h x‖ ≤ Bd) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ k in atTop, ‖(∫ ω, h (resid (A k) (z k ω, w k ω)) ∂(P k)) -
      ∫ x, h x ∂(gaussianReal 0 1)‖ ≤ ε := by
  have hre := weak_bdd_real P A z w hlaw hA hAn (fun x => (h x).re)
    (Complex.continuous_re.comp hh) Bd (fun x => (Complex.abs_re_le_norm _).trans (hb x))
  have him := weak_bdd_real P A z w hlaw hA hAn (fun x => (h x).im)
    (Complex.continuous_im.comp hh) Bd (fun x => (Complex.abs_im_le_norm _).trans (hb x))
  have e1 := Metric.tendsto_nhds.1 hre (ε / 2) (by positivity)
  have e2 := Metric.tendsto_nhds.1 him (ε / 2) (by positivity)
  filter_upwards [e1, e2] with k h1 h2
  have hi : Integrable (fun ω => h (resid (A k) (z k ω, w k ω))) (P k) :=
    (integrable_const Bd).mono'
      (hh.aestronglyMeasurable.comp_aemeasurable (vsw_sample (A k) (hA k) (P k) (z k) (w k) (hlaw k)).1)
      (Filter.Eventually.of_forall fun ω => hb _)
  have hg : Integrable h (gaussianReal 0 1) :=
    (integrable_const Bd).mono' hh.aestronglyMeasurable (Filter.Eventually.of_forall hb)
  have hr1 : ∫ ω, (h (resid (A k) (z k ω, w k ω))).re ∂(P k)
      = (∫ ω, h (resid (A k) (z k ω, w k ω)) ∂(P k)).re := integral_re hi
  have hr2 : ∫ x, (h x).re ∂(gaussianReal 0 1) = (∫ x, h x ∂(gaussianReal 0 1)).re := integral_re hg
  have hi1 : ∫ ω, (h (resid (A k) (z k ω, w k ω))).im ∂(P k)
      = (∫ ω, h (resid (A k) (z k ω, w k ω)) ∂(P k)).im := integral_im hi
  have hi2 : ∫ x, (h x).im ∂(gaussianReal 0 1) = (∫ x, h x ∂(gaussianReal 0 1)).im := integral_im hg
  rw [hr1, hr2, Real.dist_eq] at h1
  rw [hi1, hi2, Real.dist_eq] at h2
  refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
  rw [Complex.sub_re, Complex.sub_im]
  linarith

/-! ## Uniform scalar comparison -/

/-- `lem:app-vol-scalar-weak`, snapshot `cr-2026-10-23`. Declaration of record. The sup over the
compact parameter `Θ` is expressed as: for every `ε > 0`, eventually in `k`, every `θ` satisfies the
bound (equivalent to `sup_θ |…| → 0`). `ψ` is continuous and complex-valued. The state is the
regime's `(R.F k).A`, and the residual is `d = z^⊤ A w` (`resid`). LaTeX, verbatim from `section.tex`
(the whole environment):

```latex
\begin{lemma}[Uniform scalar comparison]\label{lem:app-vol-scalar-weak}
Let $\Theta$ be a compact metric space and $\psi:\Theta\times\R\to\mathbb C$
continuous with $\abs{\psi(\vartheta,x)}\le C_\psi(1+\abs x)^4$. Under
\cref{assum:app-setup-regime}, with $d=z^\T\Ahat w$ and $g\sim\mathcal N(0,1)$,
\[
\sup_{\vartheta\in\Theta}\abs{\EE\psi(\vartheta,d)-\EE\psi(\vartheta,g)}\longrightarrow0 .
\]
\end{lemma}
```
-/
theorem lem_app_vol_scalar_weak {Θ : Type*} [MetricSpace Θ] [CompactSpace Θ]
    {Ω : ℕ → Type} [∀ k, MeasurableSpace (Ω k)]
    (R : SetupRegime) (P : ∀ k, Measure (Ω k)) [∀ k, IsProbabilityMeasure (P k)]
    (z : ∀ k, Ω k → Vec (R.m k)) (w : ∀ k, Ω k → Vec (R.n k))
    (hlaw : ∀ k, (P k).map (fun ω => (z k ω, w k ω)) = gaussPair (R.m k) (R.n k))
    (ψ : Θ → ℝ → ℂ) (hψ : Continuous fun p : Θ × ℝ => ψ p.1 p.2)
    (Cψ : ℝ) (hψb : ∀ θ x, ‖ψ θ x‖ ≤ Cψ * (1 + |x|) ^ 4) :
    ∀ ε > 0, ∀ᶠ k in atTop, ∀ θ : Θ,
      ‖(∫ ω, ψ θ (resid (R.F k).A (z k ω, w k ω)) ∂(P k)) -
        ∫ x, ψ θ x ∂(gaussianReal 0 1)‖ ≤ ε := by
  intro ε hε
  have hA : ∀ k, fro (R.F k).A = 1 := fun k => (R.F k).hA
  have hAn := R.diffuse
  set C : ℝ := |Cψ| with hCdef
  have hC : 0 ≤ C := abs_nonneg _
  have hb : ∀ θ x, ‖ψ θ x‖ ≤ C * (1 + |x|) ^ 4 := fun θ x =>
    (hψb θ x).trans (mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity))
  have hcont : ∀ θ, Continuous (ψ θ) := fun θ => hψ.comp (continuous_const.prodMk continuous_id)
  have hIγ : Integrable (fun x : ℝ => (1 + |x|) ^ 6) (gaussianReal 0 1) := by
    refine ((integrable_const (1 : ℝ)).add (Muon.Foundations.gaussian_integrable_pow 6)).const_mul 32
      |>.mono' (by fun_prop : Measurable fun x : ℝ => (1 + |x|) ^ 6).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have := vsw_one_add_pow6 |x| (abs_nonneg _)
    rwa [show |x| ^ 6 = x ^ 6 from (Even.pow_abs ⟨3, rfl⟩ _)] at this
  set Kg : ℝ := ∫ x, (1 + |x|) ^ 6 ∂(gaussianReal 0 1) with hKg
  have hKg0 : 0 ≤ Kg := integral_nonneg fun x => by positivity
  set B : ℝ := 2 * C * (7232 + Kg) with hB
  have hB0 : 0 ≤ B := by positivity
  obtain ⟨M, hM0, hMB⟩ : ∃ M : ℝ, 0 ≤ M ∧ B / (1 + M) ^ 2 ≤ ε / 5 := by
    refine ⟨5 * B / ε, by positivity, ?_⟩
    set M : ℝ := 5 * B / ε
    have hM0 : 0 ≤ M := by positivity
    calc B / (1 + M) ^ 2 ≤ B / (1 + M) :=
          div_le_div_of_nonneg_left hB0 (by positivity) (by nlinarith)
      _ ≤ ε / 5 := by
          rw [div_le_iff₀ (by positivity)]
          have : ε / 5 * M = B := by simp only [M]; field_simp
          nlinarith
  have hp : 0 < (1 + M) ^ 2 := by positivity
  have hT1 : 2 * C * 7232 / (1 + M) ^ 2 ≤ ε / 5 :=
    (div_le_div_of_nonneg_right (by nlinarith) hp.le).trans hMB
  have hT2 : 2 * C * Kg / (1 + M) ^ 2 ≤ ε / 5 :=
    (div_le_div_of_nonneg_right (by nlinarith) hp.le).trans hMB
  obtain ⟨S, hS⟩ := net_window ψ hψ M (ε / 5) (by positivity)
  have hev : ∀ᶠ k in atTop, ∀ θ' ∈ S,
      ‖(∫ ω, ψ θ' (max (-M) (min M (resid (R.F k).A (z k ω, w k ω)))) ∂(P k)) -
        ∫ x, ψ θ' (max (-M) (min M x)) ∂(gaussianReal 0 1)‖ ≤ ε / 5 := by
    refine (Filter.eventually_all_finset S).2 fun θ' _ => ?_
    refine vsw_conv P (fun k => (R.F k).A) z w hlaw hA hAn
      (fun x => ψ θ' (max (-M) (min M x))) (by have := hcont θ'; fun_prop) (C * (1 + M) ^ 4)
      (fun x => ?_) (ε / 5) (by positivity)
    have := vsw_clamp_abs M x hM0
    exact (hb θ' _).trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by positivity) (by linarith [this.1]) 4) hC)
  filter_upwards [hev] with k hk θ
  obtain ⟨hD, hI, hK⟩ := vsw_sample (R.F k).A (hA k) (P k) (z k) (w k) (hlaw k)
  obtain ⟨θ', hθ'S, hθ'⟩ := hS θ
  have hclθ : ∀ x, ‖ψ θ (max (-M) (min M x)) - ψ θ' (max (-M) (min M x))‖ ≤ ε / 5 :=
    fun x => hθ' _ (vsw_clamp_abs M x hM0).1
  have t1 := vsw_tail_int (P k) _ hD hI 7232 hK (ψ θ) (hcont θ) C hC (hb θ) M hM0
  have t5 := vsw_tail_int (gaussianReal 0 1) (fun x => x) aemeasurable_id hIγ Kg le_rfl
    (ψ θ) (hcont θ) C hC (hb θ) M hM0
  have t2 := vsw_net_int (P k) _ hD hI (fun x => ψ θ (max (-M) (min M x)))
    (fun x => ψ θ' (max (-M) (min M x))) (by have := hcont θ; fun_prop)
    (by have := hcont θ'; fun_prop) C
    (vsw_clamp_bd (ψ θ) C hC (hb θ) M hM0) (vsw_clamp_bd (ψ θ') C hC (hb θ') M hM0) (ε / 5) hclθ
  have t4 := vsw_net_int (gaussianReal 0 1) (fun x => x) aemeasurable_id hIγ
    (fun x => ψ θ' (max (-M) (min M x))) (fun x => ψ θ (max (-M) (min M x)))
    (by have := hcont θ'; fun_prop) (by have := hcont θ; fun_prop) C
    (vsw_clamp_bd (ψ θ') C hC (hb θ') M hM0) (vsw_clamp_bd (ψ θ) C hC (hb θ) M hM0) (ε / 5)
    (fun x => by rw [norm_sub_rev]; exact hclθ x)
  have t3 := hk θ' hθ'S
  set a := ∫ ω, ψ θ (resid (R.F k).A (z k ω, w k ω)) ∂(P k)
  set a' := ∫ ω, ψ θ (max (-M) (min M (resid (R.F k).A (z k ω, w k ω)))) ∂(P k)
  set a'' := ∫ ω, ψ θ' (max (-M) (min M (resid (R.F k).A (z k ω, w k ω)))) ∂(P k)
  set b := ∫ x, ψ θ x ∂(gaussianReal 0 1)
  set b' := ∫ x, ψ θ (max (-M) (min M x)) ∂(gaussianReal 0 1)
  set b'' := ∫ x, ψ θ' (max (-M) (min M x)) ∂(gaussianReal 0 1)
  have e : a - b = (a - a') + (a' - a'') + (a'' - b'') + (b'' - b') + (b' - b) := by ring
  rw [e]
  have := norm_add_le ((a - a') + (a' - a'') + (a'' - b'') + (b'' - b')) (b' - b)
  have := norm_add_le ((a - a') + (a' - a'') + (a'' - b'')) (b'' - b')
  have := norm_add_le ((a - a') + (a' - a'')) (a'' - b'')
  have := norm_add_le (a - a') (a' - a'')
  rw [norm_sub_rev b' b] at *
  linarith

/-! ## Helpers for `lem_app_vol_replacement` (task P-D.7.P2) -/


/-- Fubini step for an independent family: separate the coordinate `p` from the finitely many others. -/
private lemma vrp_step {E ι Ω₀ : Type*} [MeasurableSpace E] [MeasurableSpace Ω₀]
    (P₀ : Measure Ω₀) [IsProbabilityMeasure P₀] (μ : Measure E) [IsProbabilityMeasure μ]
    (Y : ι → Ω₀ → E) (hY : ∀ i, Measurable (Y i)) (hind : iIndepFun Y P₀)
    (hlaw : ∀ i, P₀.map (Y i) = μ) (p : ι) (Λ' : Finset ι) (hp : p ∉ Λ')
    (Ψ : E → (Λ' → E) → ℝ) (hΨ : Measurable (fun r : E × (Λ' → E) => Ψ r.1 r.2)) (M : ℝ)
    (hb : ∀ x v, |Ψ x v| ≤ M) :
    ∫ ω, Ψ (Y p ω) (fun q => Y q ω) ∂P₀ = ∫ ω, (∫ x, Ψ x (fun q => Y q ω) ∂μ) ∂P₀ := by
  classical
  have hS : Disjoint ({p} : Finset ι) Λ' := by simpa using hp
  have h1 := hind.indepFun_finset {p} Λ' hS hY
  have hφ : Measurable (fun (v : ({p} : Finset ι) → E) => v ⟨p, Finset.mem_singleton_self p⟩) :=
    measurable_pi_apply _
  have h2 : IndepFun (Y p) (fun ω (q : Λ') => Y q ω) P₀ :=
    h1.comp hφ measurable_id
  have hV : Measurable (fun ω (q : Λ') => Y q ω) := measurable_pi_iff.2 fun q => hY q
  have h3 := (indepFun_iff_map_prod_eq_prod_map_map (hY p).aemeasurable hV.aemeasurable).1 h2
  rw [hlaw p] at h3
  set ν : Measure (Λ' → E) := P₀.map (fun ω (q : Λ') => Y q ω) with hν
  have hpair : Measurable (fun ω => (Y p ω, fun q : Λ' => Y q ω)) := (hY p).prodMk hV
  have hint : Integrable (fun r : E × (Λ' → E) => Ψ r.1 r.2) (P₀.map (fun ω => (Y p ω, fun q : Λ' => Y q ω))) := by
    refine Integrable.of_bound hΨ.aestronglyMeasurable M (Filter.Eventually.of_forall fun r => ?_)
    simpa using hb r.1 r.2
  have e1 : ∫ ω, Ψ (Y p ω) (fun q => Y q ω) ∂P₀ = ∫ r, Ψ r.1 r.2 ∂(μ.prod ν) := by
    rw [← h3, integral_map hpair.aemeasurable hΨ.aestronglyMeasurable]
  rw [e1]
  have hint2 : Integrable (fun r : E × (Λ' → E) => Ψ r.1 r.2) (μ.prod ν) := by
    rw [← h3]; exact hint
  rw [integral_prod_symm _ hint2]
  have hm : Measurable (fun v : Λ' → E => ∫ x, Ψ x v ∂μ) := by
    exact (hΨ.stronglyMeasurable.integral_prod_left).measurable
  rw [← integral_map hV.aemeasurable hm.aestronglyMeasurable]


/-- Lindeberg replacement of the scalar `e₁` by `e₂`, one slot at a time, over a finite window. -/
private lemma vrp_lindeberg {E ι Ω₀ : Type*} [MeasurableSpace E] [MeasurableSpace Ω₀] {m n : ℕ}
    (P₀ : Measure Ω₀) [IsProbabilityMeasure P₀] (μ : Measure E) [IsProbabilityMeasure μ]
    (Y : ι → Ω₀ → E) (hY : ∀ i, Measurable (Y i)) (hind : iIndepFun Y P₀)
    (hlaw : ∀ i, P₀.map (Y i) = μ)
    (X : E → Mat m n) (hX : Measurable X) (e₁ e₂ : E → ℝ) (he₁ : Measurable e₁) (he₂ : Measurable e₂)
    (f : Mat m n → Mat m n → ℝ) (hf : Measurable (fun r : Mat m n × Mat m n => f r.1 r.2))
    (M : ℝ) (hfb : ∀ K H, |f K H| ≤ M) (ε : ℝ)
    (hO : ∀ (K H : Mat m n) (α β : ℝ), 0 ≤ α → α ≤ 1 → 0 ≤ β → β ≤ 1 →
      |∫ x, f (K + (α * e₁ x) • X x) (H + (β * e₁ x) • X x) ∂μ -
        ∫ x, f (K + (α * e₂ x) • X x) (H + (β * e₂ x) • X x) ∂μ| ≤ (α + β) * ε)
    (Λ : Finset ι) (a b : ι → ℝ) (ha0 : ∀ p, 0 ≤ a p) (ha1 : ∀ p, a p ≤ 1)
    (hb0 : ∀ p, 0 ≤ b p) (hb1 : ∀ p, b p ≤ 1) :
    |(∫ ω, f (∑ p ∈ Λ, (a p * e₁ (Y p ω)) • X (Y p ω)) (∑ p ∈ Λ, (b p * e₁ (Y p ω)) • X (Y p ω)) ∂P₀) -
      ∫ ω, f (∑ p ∈ Λ, (a p * e₂ (Y p ω)) • X (Y p ω)) (∑ p ∈ Λ, (b p * e₂ (Y p ω)) • X (Y p ω)) ∂P₀|
      ≤ (∑ p ∈ Λ, (a p + b p)) * ε := by
  classical
  -- hybrid with the slots of `T` using `e₂`
  let sel : Finset ι → ι → E → ℝ := fun T q x => if q ∈ T then e₂ x else e₁ x
  have hsel : ∀ T q, Measurable (sel T q) := fun T q => by
    by_cases h : q ∈ T
    · simp only [sel, h, ite_true]; exact he₂
    · simp only [sel, h, ite_false]; exact he₁
  let V : Finset ι → ℝ := fun T =>
    ∫ ω, f (∑ p ∈ Λ, (a p * sel T p (Y p ω)) • X (Y p ω))
      (∑ p ∈ Λ, (b p * sel T p (Y p ω)) • X (Y p ω)) ∂P₀
  have hV0 : V ∅ = ∫ ω, f (∑ p ∈ Λ, (a p * e₁ (Y p ω)) • X (Y p ω))
      (∑ p ∈ Λ, (b p * e₁ (Y p ω)) • X (Y p ω)) ∂P₀ := by
    simp [V, sel]
  have hVT : V Λ = ∫ ω, f (∑ p ∈ Λ, (a p * e₂ (Y p ω)) • X (Y p ω))
      (∑ p ∈ Λ, (b p * e₂ (Y p ω)) • X (Y p ω)) ∂P₀ := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
    have : ∀ p ∈ Λ, sel Λ p (Y p ω) = e₂ (Y p ω) := fun p hp => by simp [sel, hp]
    have e1 : ∑ p ∈ Λ, (a p * sel Λ p (Y p ω)) • X (Y p ω) = ∑ p ∈ Λ, (a p * e₂ (Y p ω)) • X (Y p ω) :=
      Finset.sum_congr rfl fun p hp => by rw [this p hp]
    have e2 : ∑ p ∈ Λ, (b p * sel Λ p (Y p ω)) • X (Y p ω) = ∑ p ∈ Λ, (b p * e₂ (Y p ω)) • X (Y p ω) :=
      Finset.sum_congr rfl fun p hp => by rw [this p hp]
    simp only [e1, e2]
  have key : ∀ T : Finset ι, T ⊆ Λ → |V ∅ - V T| ≤ (∑ p ∈ T, (a p + b p)) * ε := by
    intro T
    induction T using Finset.induction_on with
    | empty => intro _; simp
    | insert p T hpT ih =>
      intro hsub
      have hpΛ : p ∈ Λ := hsub (Finset.mem_insert_self p T)
      have ihT := ih (fun x hx => hsub (Finset.mem_insert_of_mem hx))
      -- one step
      have step : |V T - V (insert p T)| ≤ (a p + b p) * ε := by
        set Λ' := Λ.erase p with hΛ'
        have hpΛ' : p ∉ Λ' := Finset.notMem_erase p Λ
        let Kf : (Λ' → E) → Mat m n := fun v => ∑ q : Λ', (a q * sel T q (v q)) • X (v q)
        let Hf : (Λ' → E) → Mat m n := fun v => ∑ q : Λ', (b q * sel T q (v q)) • X (v q)
        have hKf : Measurable Kf := by
          refine Finset.measurable_sum _ fun q _ => ?_
          exact (((measurable_const.mul ((hsel T q).comp (measurable_pi_apply q))).smul
            (hX.comp (measurable_pi_apply q))))
        have hHf : Measurable Hf := by
          refine Finset.measurable_sum _ fun q _ => ?_
          exact (((measurable_const.mul ((hsel T q).comp (measurable_pi_apply q))).smul
            (hX.comp (measurable_pi_apply q))))
        have hsplit : ∀ (c : ι → ℝ) (e : ι → E → ℝ) (ω : Ω₀),
            (∑ q ∈ Λ, (c q * e q (Y q ω)) • X (Y q ω)) =
              (c p * e p (Y p ω)) • X (Y p ω) +
                ∑ q ∈ Λ', (c q * e q (Y q ω)) • X (Y q ω) := fun c e ω =>
          (Finset.add_sum_erase Λ _ hpΛ).symm
        have hKω : ∀ ω, (∑ q ∈ Λ', (a q * sel T q (Y q ω)) • X (Y q ω)) = Kf (fun q : Λ' => Y q ω) := by
          intro ω
          simp only [Kf]
          exact (Finset.sum_coe_sort Λ' (fun q => (a q * sel T q (Y q ω)) • X (Y q ω))).symm
        have hHω : ∀ ω, (∑ q ∈ Λ', (b q * sel T q (Y q ω)) • X (Y q ω)) = Hf (fun q : Λ' => Y q ω) := by
          intro ω
          simp only [Hf]
          exact (Finset.sum_coe_sort Λ' (fun q => (b q * sel T q (Y q ω)) • X (Y q ω))).symm
        -- integrands
        have hselT : ∀ q ∈ Λ', sel (insert p T) q = sel T q := by
          intro q hq
          have hqp : q ≠ p := Finset.ne_of_mem_erase hq
          funext x
          simp [sel, hqp]
        have hVT1 : V T = ∫ ω, f (Kf (fun q : Λ' => Y q ω) + (a p * e₁ (Y p ω)) • X (Y p ω))
            (Hf (fun q : Λ' => Y q ω) + (b p * e₁ (Y p ω)) • X (Y p ω)) ∂P₀ := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
          simp only [V]
          rw [hsplit a (sel T) ω, hsplit b (sel T) ω, hKω ω, hHω ω, add_comm]
          have : sel T p = e₁ := by funext x; simp [sel, hpT]
          rw [this, add_comm (Kf _)]
          rw [add_comm (Hf _)]
        have hVT2 : V (insert p T) = ∫ ω, f (Kf (fun q : Λ' => Y q ω) + (a p * e₂ (Y p ω)) • X (Y p ω))
            (Hf (fun q : Λ' => Y q ω) + (b p * e₂ (Y p ω)) • X (Y p ω)) ∂P₀ := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
          simp only [V]
          rw [hsplit a (sel (insert p T)) ω, hsplit b (sel (insert p T)) ω]
          have h1 : (∑ q ∈ Λ', (a q * sel (insert p T) q (Y q ω)) • X (Y q ω)) = Kf (fun q : Λ' => Y q ω) := by
            rw [← hKω ω]
            exact Finset.sum_congr rfl fun q hq => by rw [hselT q hq]
          have h2 : (∑ q ∈ Λ', (b q * sel (insert p T) q (Y q ω)) • X (Y q ω)) = Hf (fun q : Λ' => Y q ω) := by
            rw [← hHω ω]
            exact Finset.sum_congr rfl fun q hq => by rw [hselT q hq]
          rw [h1, h2]
          have : sel (insert p T) p = e₂ := by funext x; simp [sel]
          rw [this, add_comm (Kf _), add_comm (Hf _)]
        let Ψ₁ : E → (Λ' → E) → ℝ := fun x v =>
          f (Kf v + (a p * e₁ x) • X x) (Hf v + (b p * e₁ x) • X x)
        let Ψ₂ : E → (Λ' → E) → ℝ := fun x v =>
          f (Kf v + (a p * e₂ x) • X x) (Hf v + (b p * e₂ x) • X x)
        have hΨ1 : Measurable (fun r : E × (Λ' → E) => Ψ₁ r.1 r.2) := by
          refine hf.comp (Measurable.prodMk ?_ ?_)
          · exact (hKf.comp measurable_snd).add ((measurable_const.mul (he₁.comp measurable_fst)).smul (hX.comp measurable_fst))
          · exact (hHf.comp measurable_snd).add ((measurable_const.mul (he₁.comp measurable_fst)).smul (hX.comp measurable_fst))
        have hΨ2 : Measurable (fun r : E × (Λ' → E) => Ψ₂ r.1 r.2) := by
          refine hf.comp (Measurable.prodMk ?_ ?_)
          · exact (hKf.comp measurable_snd).add ((measurable_const.mul (he₂.comp measurable_fst)).smul (hX.comp measurable_fst))
          · exact (hHf.comp measurable_snd).add ((measurable_const.mul (he₂.comp measurable_fst)).smul (hX.comp measurable_fst))
        have s1 := vrp_step P₀ μ Y hY hind hlaw p Λ' hpΛ' Ψ₁ hΨ1 M (fun x v => hfb _ _)
        have s2 := vrp_step P₀ μ Y hY hind hlaw p Λ' hpΛ' Ψ₂ hΨ2 M (fun x v => hfb _ _)
        have hV : Measurable (fun ω (q : Λ') => Y q ω) := measurable_pi_iff.2 fun q => hY q
        have hm1 : Measurable (fun v : Λ' → E => ∫ x, Ψ₁ x v ∂μ) :=
          (hΨ1.stronglyMeasurable.integral_prod_left).measurable
        have hm2 : Measurable (fun v : Λ' → E => ∫ x, Ψ₂ x v ∂μ) :=
          (hΨ2.stronglyMeasurable.integral_prod_left).measurable
        have hbd1 : ∀ v, |∫ x, Ψ₁ x v ∂μ| ≤ M := fun v => by
          have := norm_integral_le_of_norm_le_const (μ := μ) (f := fun x => Ψ₁ x v) (C := M)
            (Filter.Eventually.of_forall fun x => by simpa using hfb _ _)
          simpa using this
        have hbd2 : ∀ v, |∫ x, Ψ₂ x v ∂μ| ≤ M := fun v => by
          have := norm_integral_le_of_norm_le_const (μ := μ) (f := fun x => Ψ₂ x v) (C := M)
            (Filter.Eventually.of_forall fun x => by simpa using hfb _ _)
          simpa using this
        have hi1 : Integrable (fun ω => ∫ x, Ψ₁ x (fun q : Λ' => Y q ω) ∂μ) P₀ :=
          Integrable.of_bound ((hm1.comp hV).aestronglyMeasurable) M
            (Filter.Eventually.of_forall fun ω => by simpa using hbd1 _)
        have hi2 : Integrable (fun ω => ∫ x, Ψ₂ x (fun q : Λ' => Y q ω) ∂μ) P₀ :=
          Integrable.of_bound ((hm2.comp hV).aestronglyMeasurable) M
            (Filter.Eventually.of_forall fun ω => by simpa using hbd2 _)
        rw [hVT1, hVT2]
        change |(∫ ω, Ψ₁ (Y p ω) (fun q : Λ' => Y q ω) ∂P₀) - ∫ ω, Ψ₂ (Y p ω) (fun q : Λ' => Y q ω) ∂P₀| ≤ _
        rw [s1, s2, ← integral_sub hi1 hi2]
        have := norm_integral_le_of_norm_le_const (μ := P₀)
          (f := fun ω => (∫ x, Ψ₁ x (fun q : Λ' => Y q ω) ∂μ) - ∫ x, Ψ₂ x (fun q : Λ' => Y q ω) ∂μ)
          (C := (a p + b p) * ε) (Filter.Eventually.of_forall fun ω => ?_)
        · simpa using this
        · have := hO (Kf (fun q : Λ' => Y q ω)) (Hf (fun q : Λ' => Y q ω)) (a p) (b p)
            (ha0 p) (ha1 p) (hb0 p) (hb1 p)
          simpa [Ψ₁, Ψ₂] using this
      have hsumins : ∑ q ∈ insert p T, (a q + b q) = (a p + b p) + ∑ q ∈ T, (a q + b q) :=
        Finset.sum_insert hpT
      calc |V ∅ - V (insert p T)| = |(V ∅ - V T) + (V T - V (insert p T))| := by ring_nf
        _ ≤ |V ∅ - V T| + |V T - V (insert p T)| := abs_add_le _ _
        _ ≤ (∑ q ∈ T, (a q + b q)) * ε + (a p + b p) * ε := add_le_add ihT step
        _ = (∑ q ∈ insert p T, (a q + b q)) * ε := by rw [hsumins]; ring
  have := key Λ (Finset.Subset.refl Λ)
  rw [hV0, hVT] at this
  exact this


private lemma vrp_Rs_continuous {m n : ℕ} (s : ℝ) (hs : 0 < s) :
    Continuous (fun M : Mat m n => Rs M s) := by
  rw [continuous_iff_continuousAt]
  intro M
  have hA : ∀ M : Mat m n, IsUnit (M * Mᵀ + s • (1 : Mat m m)).det := by
    intro M
    have h6 := (lem_app_de_resolvent M s hs).2.2.2.2.2.1
    have : Rs M s * (M * Mᵀ + s • (1 : Mat m m)) = 1 := by
      rw [Matrix.mul_add, h6, Matrix.mul_smul, Matrix.mul_one]
      abel
    exact Matrix.isUnit_det_of_left_inverse this
  have hcont : ContinuousAt (fun M : Mat m n => M * Mᵀ + s • (1 : Mat m m)) M := by
    fun_prop
  have hdet : (M * Mᵀ + s • (1 : Mat m m)).det ≠ 0 := (hA M).ne_zero
  have hinv : ContinuousAt (Inv.inv : Mat m m → Mat m m) (M * Mᵀ + s • (1 : Mat m m)) := by
    refine continuousAt_matrix_inv _ ?_
    rw [Ring.inverse_eq_inv']
    exact continuousAt_inv₀ hdet
  show ContinuousAt (fun M : Mat m n => (M * Mᵀ + s • (1 : Mat m m))⁻¹) M
  exact ContinuousAt.comp (g := fun A : Mat m m => A⁻¹)
    (f := fun M : Mat m n => M * Mᵀ + s • (1 : Mat m m)) hinv hcont

private lemma vrp_Xs_continuous {m n : ℕ} (s : ℝ) (hs : 0 < s) :
    Continuous (fun M : Mat m n => Xs M s) := by
  unfold Xs
  exact (vrp_Rs_continuous s hs).matrix_mul continuous_id

private lemma vrp_f_cont {m n B : ℕ} (F : Mat m m) (G : Mat n n) {s u : ℝ} (hs : 0 < s) (hu : 0 < u) :
    Continuous (fun p : Mat m n × Mat m n => contractionRes B F G s u p.1 p.2) := by
  have e : ∀ p : Mat m n × Mat m n, contractionRes B F G s u p.1 p.2 =
      (B : ℝ)⁻¹ * Matrix.trace (F * Xs p.1 s * G * (Xs p.2 u)ᵀ) := by
    intro p
    unfold contractionRes contraction
    rw [eqn_app_vol_filters_sharp_i hs, eqn_app_vol_filters_sharp_i hu]
  simp_rw [e]
  have h1 : Continuous (fun p : Mat m n × Mat m n => Xs p.1 s) := (vrp_Xs_continuous s hs).comp continuous_fst
  have h2 : Continuous (fun p : Mat m n × Mat m n => Xs p.2 u) := (vrp_Xs_continuous u hu).comp continuous_snd
  exact continuous_const.mul (((continuous_const.matrix_mul h1).matrix_mul continuous_const).matrix_mul
    h2.matrix_transpose).matrix_trace

private lemma vrp_f_bdd {m n B : ℕ} (hB : 0 < B) (F : Mat m m) (G : Mat n n)
    (hF : opNorm F ≤ 1) (hG : opNorm G ≤ 1) {s u : ℝ} (hs : 0 < s) (hu : 0 < u) (K H : Mat m n) :
    |contractionRes B F G s u K H| ≤
      ((min m n : ℕ) : ℝ) / B * (1 / (2 * Real.sqrt s)) * (1 / (2 * Real.sqrt u)) := by
  have hBr : (0 : ℝ) < B := by exact_mod_cast hB
  have hdim : ((min m n : ℕ) : ℝ) ≤ (((min m n : ℕ) : ℝ) / B) * B := by
    rw [div_mul_cancel₀ _ hBr.ne']
  have h := lem_app_vol_finite_i hB (((min m n : ℕ) : ℝ) / B) hdim F G hF hG (iotaF s) (iotaF u)
    (lem_app_vol_sharp_ii hs hs).1 (lem_app_vol_sharp_ii hu hu).1 K H
  have hs' := (lem_app_vol_sharp_ii hs hs).2.2.1
  have hu' := (lem_app_vol_sharp_ii hu hu).2.2.1
  unfold contractionRes
  rw [hs', hu'] at h
  exact h


private lemma vrp_pair_meas {m n : ℕ} {X : Type*} [MeasurableSpace X] (f : Mat m n → Mat m n → ℝ)
    (hf : Continuous (fun p : Mat m n × Mat m n => f p.1 p.2)) (K H : X → Mat m n)
    (hK : Measurable K) (hH : Measurable H) : Measurable (fun x => f (K x) (H x)) :=
  hf.measurable.comp (hK.prodMk hH)


private lemma vrp_reindex {V : Type*} [AddCommGroup V] [Module ℝ V] (β : ℝ) (t : ℤ) (J : ℕ) (N : ℤ) (hN : t + 1 ≤ N)
    (H : ℤ → V) :
    ∑ j ∈ Finset.range (J + 1), emaW β j • H (t + 1 - (j : ℤ)) =
      ∑ s ∈ Finset.Icc (t + 1 - (J : ℤ)) N,
        (if s ≤ t + 1 then emaW β (t + 1 - s).toNat else 0) • H s := by
  classical
  have h1 : ∑ s ∈ Finset.Icc (t + 1 - (J : ℤ)) N,
        (if s ≤ t + 1 then emaW β (t + 1 - s).toNat else 0) • H s =
      ∑ s ∈ (Finset.Icc (t + 1 - (J : ℤ)) N).filter (fun s => s ≤ t + 1),
        emaW β (t + 1 - s).toNat • H s := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun s _ => ?_
    split_ifs <;> simp
  rw [h1]
  refine Finset.sum_nbij' (fun j : ℕ => t + 1 - (j : ℤ)) (fun s : ℤ => (t + 1 - s).toNat) ?_ ?_ ?_ ?_ ?_
  · intro j hj
    simp only [Finset.mem_range] at hj
    simp only [Finset.mem_filter, Finset.mem_Icc]
    omega
  · intro s hs
    simp only [Finset.mem_filter, Finset.mem_Icc] at hs
    simp only [Finset.mem_range]
    omega
  · intro j hj
    simp
  · intro s hs
    simp only [Finset.mem_filter, Finset.mem_Icc] at hs
    omega
  · intro j hj
    have : (t + 1 - (t + 1 - (j : ℤ))).toNat = j := by omega
    simp only [this]


private lemma vrp_transfer {m n B : ℕ} (Ω' : Type) [MeasurableSpace Ω'] (P : Measure Ω')
    [IsProbabilityMeasure P] (S : FrozenSamples P m n B)
    (Φ : ((ℤ × Fin B) → Vec m × Vec n) → ℝ) (hΦ : Measurable Φ) :
    ∫ ω, Φ (fun p => S.zw p.1 p.2 ω) ∂P =
      ∫ ω, Φ (fun p => (ω p).2) ∂(indepSpaceLaw m n B) := by
  classical
  set μ0 := (Muon.Foundations.stdGaussianPi m).prod (Muon.Foundations.stdGaussianPi n) with hμ0
  set ν0 := Measure.infinitePi (fun _ : ℤ × Fin B => μ0) with hν0
  let X : Ω' → (ℤ × Fin B → Vec m × Vec n) := fun ω p => S.zw p.1 p.2 ω
  have hX : Measurable X := measurable_pi_iff.2 fun p : ℤ × Fin B => S.meas p.1 p.2
  have hXlaw : P.map X = ν0 := by
    have := S.indep.map_fun_eq_infinitePi_map (fun p : ℤ × Fin B => S.meas p.1 p.2)
    rw [hν0]
    convert this using 2
    funext p
    exact (S.law p.1 p.2).symm
  have hsnd : Measurable (fun x : ℝ × (Vec m × Vec n) => x.2) := measurable_snd
  have hY : Measurable (fun (ω : (ℤ × Fin B) → ℝ × (Vec m × Vec n)) (p : ℤ × Fin B) => (ω p).2) :=
    measurable_pi_iff.2 fun p => hsnd.comp (measurable_pi_apply p)
  have hYlaw : (indepSpaceLaw m n B).map (fun (ω : (ℤ × Fin B) → ℝ × (Vec m × Vec n)) (p : ℤ × Fin B) => (ω p).2) = ν0 := by
    have hmap := Measure.infinitePi_map_pi (μ := fun _ : ℤ × Fin B => indepSlotLaw m n)
      (f := fun _ x => x.2) (fun _ => hsnd)
    have hsl : (indepSlotLaw m n).map (fun x : ℝ × (Vec m × Vec n) => x.2) = μ0 := by
      unfold indepSlotLaw
      rw [Measure.map_snd_prod]
      simp [hμ0]
    simp only [hsl] at hmap
    exact hmap
  calc ∫ ω, Φ (fun p => S.zw p.1 p.2 ω) ∂P = ∫ y, Φ y ∂(P.map X) := by
        rw [integral_map hX.aemeasurable hΦ.aestronglyMeasurable]
    _ = ∫ y, Φ y ∂ν0 := by rw [hXlaw]
    _ = ∫ y, Φ y ∂((indepSpaceLaw m n B).map _) := by rw [hYlaw]
    _ = _ := integral_map hY.aemeasurable hΦ.aestronglyMeasurable


/-- The rank-one structure of one slot of the batch: `X(z,w) = B⁻¹ Σ_out^{1/2} (z ⊗ w) Σ_in^{1/2}`. -/
private def vSlotX {m n : ℕ} (C : Covariances m n) (B : ℕ) (x : Vec m × Vec n) : Mat m n :=
  (B : ℝ)⁻¹ • (rOut C * outer x.1 x.2 * rIn C)

/-- Window sum `∑_{p∈Λ} (a_{p.1} d_p) X(zw_p)`. -/
private def vWinSum {m n B : ℕ} (C : Covariances m n) (Λ : Finset (ℤ × Fin B)) (a : ℤ → ℝ)
    (d : ℤ × Fin B → ℝ) (zw : ℤ × Fin B → Vec m × Vec n) : Mat m n :=
  ∑ p ∈ Λ, (a p.1 * d p) • vSlotX C B (zw p)

private lemma vrp_batch_eq {m n B : ℕ} (C : Covariances m n) (d : Fin B → ℝ)
    (zw : Fin B → Vec m × Vec n) :
    (B : ℝ)⁻¹ • ∑ a : Fin B, d a • (rOut C * outer (zw a).1 (zw a).2 * rIn C) =
      ∑ a : Fin B, d a • vSlotX C B (zw a) := by
  simp only [vSlotX, Finset.smul_sum]
  exact Finset.sum_congr rfl fun a _ => smul_comm _ _ _

private lemma vrp_win {m n B : ℕ} (C : Covariances m n) (β : ℝ) (t : ℤ) (J : ℕ) (N : ℤ)
    (hN : t + 1 ≤ N) (batch : ℤ → Mat m n) (d : ℤ × Fin B → ℝ) (zw : ℤ × Fin B → Vec m × Vec n)
    (hb : ∀ s, batch s = ∑ a : Fin B, d (s, a) • vSlotX C B (zw (s, a))) :
    ∑ j ∈ Finset.range (J + 1), emaW β j • batch (t + 1 - (j : ℤ)) =
      vWinSum C ((Finset.Icc (t + 1 - (J : ℤ)) N) ×ˢ (Finset.univ : Finset (Fin B)))
        (fun r => if r ≤ t + 1 then emaW β (t + 1 - r).toNat else 0) d zw := by
  unfold vWinSum
  rw [vrp_reindex β t J N hN batch, Finset.sum_product]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [hb s, Finset.smul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [smul_smul]


private lemma vrp_emaW_nonneg (β : ℝ) (hβ : 0 ≤ β ∧ β < 1) (j : ℕ) : 0 ≤ emaW β j := by
  unfold emaW
  exact mul_nonneg (by linarith [hβ.2]) (pow_nonneg hβ.1 j)

private lemma vrp_emaW_partial (β : ℝ) (hβ : 0 ≤ β ∧ β < 1) (J : ℕ) :
    ∑ j ∈ Finset.range J, emaW β j ≤ 1 := by
  have hs : Summable (fun j : ℕ => emaW β j) := by
    unfold emaW
    exact (summable_geometric_of_lt_one hβ.1 hβ.2).mul_left _
  have := hs.sum_le_tsum (Finset.range J) (fun j _ => vrp_emaW_nonneg β hβ j)
  rwa [tsum_emaW hβ.1 hβ.2] at this

open scoped Matrix.Norms.Frobenius in
private lemma vrp_partial_tendsto {m n : ℕ} (g : ℕ → Mat m n) (h : Summable fun j => fro (g j)) :
    Tendsto (fun J : ℕ => ∑ j ∈ Finset.range (J + 1), g j) atTop (𝓝 (∑' j, g j)) := by
  have hs : Summable g := by
    refine Summable.of_norm ?_
    simpa [fro_eq_norm] using h
  exact hs.hasSum.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)

open scoped Matrix.Norms.Frobenius in
private lemma vrp_partial_tendsto' {m n : ℕ} (g : ℕ → Mat m n) (h : Summable fun j => fro (g j)) (ℓ : ℕ) :
    Tendsto (fun J : ℕ => ∑ j ∈ Finset.range (J + ℓ + 1), g j) atTop (𝓝 (∑' j, g j)) := by
  have hs : Summable g := by
    refine Summable.of_norm ?_
    simpa [fro_eq_norm] using h
  exact hs.hasSum.tendsto_sum_nat.comp ((tendsto_add_atTop_nat (ℓ + 1)).congr fun J => by ring_nf)

/-- The mass of the paired weights in a window: `∑_p (a_p + b_p) ≤ 2B`. -/
private lemma vrp_mass {B : ℕ} (β : ℝ) (hβ : 0 ≤ β ∧ β < 1) (t : ℤ) (ℓ J : ℕ) :
    ∑ p ∈ (Finset.Icc (t + 1 - (J : ℤ)) (t + (ℓ : ℤ) + 1)) ×ˢ (Finset.univ : Finset (Fin B)),
      ((if p.1 ≤ t + 1 then emaW β (t + 1 - p.1).toNat else 0) +
        (if p.1 ≤ (t + (ℓ : ℤ)) + 1 then emaW β ((t + (ℓ : ℤ)) + 1 - p.1).toNat else 0)) ≤ 2 * B := by
  rw [Finset.sum_product]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [← Finset.mul_sum, Finset.sum_add_distrib]
  have h1 := vrp_reindex (V := ℝ) β t J (t + (ℓ : ℤ) + 1) (by omega) (fun _ => (1 : ℝ))
  have h2 := vrp_reindex (V := ℝ) β (t + (ℓ : ℤ)) (J + ℓ) (t + (ℓ : ℤ) + 1) le_rfl (fun _ => (1 : ℝ))
  have e : t + (ℓ : ℤ) + 1 - ((J + ℓ : ℕ) : ℤ) = t + 1 - (J : ℤ) := by push_cast; ring
  rw [e] at h2
  simp only [smul_eq_mul, mul_one] at h1 h2
  rw [← h1, ← h2]
  have := vrp_emaW_partial β hβ (J + 1)
  have := vrp_emaW_partial β hβ (J + ℓ + 1)
  have hB : (0 : ℝ) ≤ B := Nat.cast_nonneg B
  nlinarith


private lemma vrp_slot_cont {m n : ℕ} (C : Covariances m n) (B : ℕ) :
    Continuous (vSlotX C B : Vec m × Vec n → Mat m n) := by
  have hout : Continuous (fun x : Vec m × Vec n => outer x.1 x.2) := by
    unfold outer
    refine continuous_pi fun i => continuous_pi fun j => ?_
    simp only [Matrix.vecMulVec_apply]
    fun_prop
  unfold vSlotX
  have h2 : Continuous (fun x : Vec m × Vec n => rOut C * outer x.1 x.2 * rIn C) :=
    (continuous_const.matrix_mul hout).matrix_mul continuous_const
  exact h2.const_smul ((B : ℝ)⁻¹)

private lemma vrp_resid_cont {m n : ℕ} (A : Mat m n) :
    Continuous (fun x : Vec m × Vec n => resid A x) := by
  unfold resid dotProduct Matrix.mulVec dotProduct
  fun_prop

private lemma vrp_win_meas {m n B : ℕ} (C : Covariances m n) (Λ : Finset (ℤ × Fin B)) (a : ℤ → ℝ)
    {X : Type*} [MeasurableSpace X] (dd : X → ℤ × Fin B → ℝ) (zz : X → ℤ × Fin B → Vec m × Vec n)
    (hd : ∀ p, Measurable fun x => dd x p) (hz : ∀ p, Measurable fun x => zz x p) :
    Measurable (fun x => vWinSum C Λ a (dd x) (zz x)) := by
  unfold vWinSum
  refine Finset.measurable_sum _ fun p _ => ?_
  exact (measurable_const.mul (hd p)).smul ((vrp_slot_cont C B).measurable.comp (hz p))

private lemma vrp_win_meas_frozen {m n B : ℕ} (C : Covariances m n) (A : Mat m n)
    (Λ : Finset (ℤ × Fin B)) (a : ℤ → ℝ) :
    Measurable (fun y : (ℤ × Fin B) → Vec m × Vec n => vWinSum C Λ a (fun p => resid A (y p)) y) := by
  refine vrp_win_meas C Λ a (X := (ℤ × Fin B) → Vec m × Vec n) (fun y p => resid A (y p)) (fun y => y) ?_ ?_
  · intro p
    exact (vrp_resid_cont A).measurable.comp (measurable_pi_apply p)
  · intro p
    exact measurable_pi_apply p

private lemma vrp_win_meas_indep {m n B : ℕ} (C : Covariances m n)
    (Λ : Finset (ℤ × Fin B)) (a : ℤ → ℝ) :
    Measurable (fun ω : (ℤ × Fin B) → ℝ × (Vec m × Vec n) =>
      vWinSum C Λ a (fun p => (ω p).1) (fun p => (ω p).2)) := by
  refine vrp_win_meas C Λ a (X := (ℤ × Fin B) → ℝ × (Vec m × Vec n)) (fun ω p => (ω p).1)
    (fun ω p => (ω p).2) ?_ ?_
  · intro p
    exact measurable_fst.comp (measurable_pi_apply p)
  · intro p
    exact measurable_snd.comp (measurable_pi_apply p)


/-- Assembly of the all-samples argument: from the one-sample bound `hO` to the replacement
of the whole histories. -/
private lemma vrp_assemble {m n B : ℕ} (Fp : FrozenParams m n B) (F : Mat m m) (G : Mat n n)
    (hF : opNorm F ≤ 1) (hG : opNorm G ≤ 1) {s u : ℝ} (hs : 0 < s) (hu : 0 < u)
    (ε : ℝ) (hε : 0 ≤ ε)
    (hO : ∀ (K H : Mat m n) (α β : ℝ), 0 ≤ α → α ≤ 1 → 0 ≤ β → β ≤ 1 →
      |∫ x, contractionRes B F G s u (K + (α * resid Fp.A x.2) • vSlotX Fp.C B x.2)
            (H + (β * resid Fp.A x.2) • vSlotX Fp.C B x.2) ∂(indepSlotLaw m n) -
        ∫ x, contractionRes B F G s u (K + (α * x.1) • vSlotX Fp.C B x.2)
            (H + (β * x.1) • vSlotX Fp.C B x.2) ∂(indepSlotLaw m n)| ≤ (α + β) * (ε / B))
    (Ω' : Type) [MeasurableSpace Ω'] (P : Measure Ω') [IsProbabilityMeasure P]
    (S : FrozenSamples P m n B) (t : ℤ) (ℓ : ℕ) :
    |(∫ ω, contractionRes B F G s u (frozenBuf Fp S t ω) (frozenBuf Fp S (t + (ℓ : ℤ)) ω) ∂P) -
      ∫ ω, contractionRes B F G s u (def_app_vol_product Fp ω t)
        (def_app_vol_product Fp ω (t + (ℓ : ℤ))) ∂(indepSpaceLaw m n B)| ≤ 2 * ε := by
  classical
  have hβ := Fp.hβ
  have hBpos : (0 : ℝ) < B := by exact_mod_cast Fp.hB
  set f : Mat m n → Mat m n → ℝ := fun K H => contractionRes B F G s u K H with hfdef
  have hfc : Continuous (fun p : Mat m n × Mat m n => f p.1 p.2) := vrp_f_cont F G hs hu
  set Mb : ℝ := ((min m n : ℕ) : ℝ) / B * (1 / (2 * Real.sqrt s)) * (1 / (2 * Real.sqrt u)) with hMb
  have hfb : ∀ K H, |f K H| ≤ Mb := fun K H => vrp_f_bdd Fp.hB F G hF hG hs hu K H
  set aw : ℤ → ℝ := fun r => if r ≤ t + 1 then emaW Fp.β (t + 1 - r).toNat else 0 with haw
  set bw : ℤ → ℝ := fun r => if r ≤ (t + (ℓ : ℤ)) + 1 then emaW Fp.β ((t + (ℓ : ℤ)) + 1 - r).toNat else 0 with hbw
  have hawle : ∀ r, 0 ≤ aw r ∧ aw r ≤ 1 := by
    intro r
    simp only [haw]
    split_ifs
    · refine ⟨vrp_emaW_nonneg _ hβ _, ?_⟩
      unfold emaW
      have : Fp.β ^ (t + 1 - r).toNat ≤ 1 := pow_le_one₀ hβ.1 hβ.2.le
      nlinarith [hβ.1, hβ.2, pow_nonneg hβ.1 (t + 1 - r).toNat]
    · simp
  have hbwle : ∀ r, 0 ≤ bw r ∧ bw r ≤ 1 := by
    intro r
    simp only [hbw]
    split_ifs
    · refine ⟨vrp_emaW_nonneg _ hβ _, ?_⟩
      unfold emaW
      have : Fp.β ^ ((t + (ℓ : ℤ)) + 1 - r).toNat ≤ 1 := pow_le_one₀ hβ.1 hβ.2.le
      nlinarith [hβ.1, hβ.2, pow_nonneg hβ.1 ((t + (ℓ : ℤ)) + 1 - r).toNat]
    · simp
  let Λ : ℕ → Finset (ℤ × Fin B) := fun J =>
    (Finset.Icc (t + 1 - (J : ℤ)) (t + (ℓ : ℤ) + 1)) ×ˢ (Finset.univ : Finset (Fin B))
  -- (1) window representation of the truncated frozen buffers
  have hfroz : ∀ (ω : Ω') (J : ℕ),
      (truncBuf Fp S t J ω, truncBuf Fp S (t + (ℓ : ℤ)) (J + ℓ) ω) =
        (vWinSum Fp.C (Λ J) aw (fun p => resid Fp.A (S.zw p.1 p.2 ω)) (fun p => S.zw p.1 p.2 ω),
         vWinSum Fp.C (Λ J) bw (fun p => resid Fp.A (S.zw p.1 p.2 ω)) (fun p => S.zw p.1 p.2 ω)) := by
    intro ω J
    have hb : ∀ r, frozenBatchG Fp S r ω =
        ∑ a : Fin B, resid Fp.A (S.zw r a ω) • vSlotX Fp.C B (S.zw r a ω) := by
      intro r
      unfold frozenBatchG
      exact vrp_batch_eq Fp.C (fun a => resid Fp.A (S.zw r a ω)) (fun a => S.zw r a ω)
    refine Prod.ext ?_ ?_
    · exact vrp_win Fp.C Fp.β t J (t + (ℓ : ℤ) + 1) (by omega) (fun r => frozenBatchG Fp S r ω)
        (fun p => resid Fp.A (S.zw p.1 p.2 ω)) (fun p => S.zw p.1 p.2 ω) hb
    · have := vrp_win Fp.C Fp.β (t + (ℓ : ℤ)) (J + ℓ) (t + (ℓ : ℤ) + 1) le_rfl
        (fun r => frozenBatchG Fp S r ω) (fun p => resid Fp.A (S.zw p.1 p.2 ω))
        (fun p => S.zw p.1 p.2 ω) hb
      have e : t + (ℓ : ℤ) + 1 - ((J + ℓ : ℕ) : ℤ) = t + 1 - (J : ℤ) := by push_cast; ring
      rw [e] at this
      exact this
  have hindep : ∀ (ω : (ℤ × Fin B) → ℝ × (Vec m × Vec n)) (J : ℕ),
      (∑ j ∈ Finset.range (J + 1), emaW Fp.β j • indepBatchG Fp ω (t + 1 - (j : ℤ)),
        ∑ j ∈ Finset.range (J + ℓ + 1), emaW Fp.β j • indepBatchG Fp ω ((t + (ℓ : ℤ)) + 1 - (j : ℤ))) =
        (vWinSum Fp.C (Λ J) aw (fun p => (ω p).1) (fun p => (ω p).2),
         vWinSum Fp.C (Λ J) bw (fun p => (ω p).1) (fun p => (ω p).2)) := by
    intro ω J
    have hb : ∀ r, indepBatchG Fp ω r =
        ∑ a : Fin B, (ω (r, a)).1 • vSlotX Fp.C B (ω (r, a)).2 := by
      intro r
      unfold indepBatchG
      exact vrp_batch_eq Fp.C (fun a => (ω (r, a)).1) (fun a => (ω (r, a)).2)
    refine Prod.ext ?_ ?_
    · exact vrp_win Fp.C Fp.β t J (t + (ℓ : ℤ) + 1) (by omega) (fun r => indepBatchG Fp ω r)
        (fun p => (ω p).1) (fun p => (ω p).2) hb
    · have := vrp_win Fp.C Fp.β (t + (ℓ : ℤ)) (J + ℓ) (t + (ℓ : ℤ) + 1) le_rfl
        (fun r => indepBatchG Fp ω r) (fun p => (ω p).1) (fun p => (ω p).2) hb
      have e : t + (ℓ : ℤ) + 1 - ((J + ℓ : ℕ) : ℤ) = t + 1 - (J : ℤ) := by push_cast; ring
      rw [e] at this
      exact this
  haveI hprobν : IsProbabilityMeasure (indepSpaceLaw m n B) := by
    unfold indepSpaceLaw; infer_instance
  -- (2) measurability of the window functionals
  let Φ : ℕ → ((ℤ × Fin B) → Vec m × Vec n) → ℝ := fun J y =>
    f (vWinSum Fp.C (Λ J) aw (fun p => resid Fp.A (y p)) y)
      (vWinSum Fp.C (Λ J) bw (fun p => resid Fp.A (y p)) y)
  have hΦ : ∀ J, Measurable (Φ J) := by
    intro J
    exact vrp_pair_meas f hfc _ _ (vrp_win_meas_frozen Fp.C Fp.A (Λ J) aw)
      (vrp_win_meas_frozen Fp.C Fp.A (Λ J) bw)
  let Ψ : ℕ → ((ℤ × Fin B) → ℝ × (Vec m × Vec n)) → ℝ := fun J ω =>
    f (vWinSum Fp.C (Λ J) aw (fun p => (ω p).1) (fun p => (ω p).2))
      (vWinSum Fp.C (Λ J) bw (fun p => (ω p).1) (fun p => (ω p).2))
  have hΨ : ∀ J, Measurable (Ψ J) := by
    intro J
    exact vrp_pair_meas f hfc _ _ (vrp_win_meas_indep Fp.C (Λ J) aw)
      (vrp_win_meas_indep Fp.C (Λ J) bw)
  -- (3) the window estimate
  have hwin : ∀ J : ℕ, |(∫ ω, Φ J (fun p => S.zw p.1 p.2 ω) ∂P) -
      ∫ ω, Ψ J ω ∂(indepSpaceLaw m n B)| ≤ 2 * ε := by
    intro J
    rw [vrp_transfer Ω' P S (Φ J) (hΦ J)]
    have hI : iIndepFun (fun (p : ℤ × Fin B) (ω : (ℤ × Fin B) → ℝ × (Vec m × Vec n)) => ω p)
        (indepSpaceLaw m n B) :=
      iIndepFun_infinitePi (P := fun _ : ℤ × Fin B => indepSlotLaw m n)
        (X := fun _ x => x) (fun _ => measurable_id)
    have hlaw : ∀ p : ℤ × Fin B, (indepSpaceLaw m n B).map (fun ω : (ℤ × Fin B) → ℝ × (Vec m × Vec n) => ω p) =
        indepSlotLaw m n := fun p => by
      unfold indepSpaceLaw; exact Measure.infinitePi_map_eval _ p
    have hL := vrp_lindeberg (indepSpaceLaw m n B) (indepSlotLaw m n)
      (fun (p : ℤ × Fin B) (ω : (ℤ × Fin B) → ℝ × (Vec m × Vec n)) => ω p)
      (fun p => measurable_pi_apply p) hI hlaw
      (fun x : ℝ × (Vec m × Vec n) => vSlotX Fp.C B x.2)
      ((vrp_slot_cont Fp.C B).measurable.comp measurable_snd)
      (fun x => resid Fp.A x.2) (fun x => x.1)
      ((vrp_resid_cont _).measurable.comp measurable_snd) measurable_fst
      f hfc.measurable Mb hfb (ε / B) hO (Λ J) (fun p => aw p.1) (fun p => bw p.1)
      (fun p => (hawle p.1).1) (fun p => (hawle p.1).2) (fun p => (hbwle p.1).1)
      (fun p => (hbwle p.1).2)
    have hmass : (∑ p ∈ Λ J, (aw p.1 + bw p.1)) * (ε / B) ≤ 2 * ε := by
      have hm := vrp_mass (B := B) Fp.β hβ t ℓ J
      calc (∑ p ∈ Λ J, (aw p.1 + bw p.1)) * (ε / B) ≤ (2 * B) * (ε / B) :=
            mul_le_mul_of_nonneg_right hm (by positivity)
        _ = 2 * ε := by field_simp
    refine le_trans ?_ hmass
    exact hL
  have hX : Measurable (fun (ω : Ω') (p : ℤ × Fin B) => S.zw p.1 p.2 ω) :=
    measurable_pi_iff.2 fun p => S.meas p.1 p.2
  -- (4) the limits J → ∞
  have hFlim : Tendsto (fun J : ℕ => ∫ ω, Φ J (fun p => S.zw p.1 p.2 ω) ∂P) atTop
      (𝓝 (∫ ω, f (frozenBuf Fp S t ω) (frozenBuf Fp S (t + (ℓ : ℤ)) ω) ∂P)) := by
    refine tendsto_integral_of_dominated_convergence (fun _ => Mb) ?_ (integrable_const _) ?_ ?_
    · intro J
      exact ((hΦ J).comp hX).aestronglyMeasurable
    · intro J
      exact Filter.Eventually.of_forall fun ω => by simpa using hfb _ _
    · filter_upwards [(lem_app_setup_ema_law_i Fp S).1] with ω hω
      have h1 := vrp_partial_tendsto (fun j => emaW Fp.β j • frozenBatchG Fp S (t + 1 - (j : ℤ)) ω) (hω t)
      have h2 := vrp_partial_tendsto' (fun j => emaW Fp.β j • frozenBatchG Fp S ((t + (ℓ : ℤ)) + 1 - (j : ℤ)) ω)
        (hω (t + (ℓ : ℤ))) ℓ
      have h4 := (hfc.tendsto _).comp (h1.prodMk_nhds h2)
      refine h4.congr (fun J => ?_)
      have := hfroz ω J
      simp only [Prod.mk.injEq] at this
      simp only [Function.comp, Φ]
      rw [← this.1, ← this.2]
      rfl
  have hGlim : Tendsto (fun J : ℕ => ∫ ω, Ψ J ω ∂(indepSpaceLaw m n B)) atTop
      (𝓝 (∫ ω, f (def_app_vol_product Fp ω t) (def_app_vol_product Fp ω (t + (ℓ : ℤ))) ∂(indepSpaceLaw m n B))) := by
    refine tendsto_integral_of_dominated_convergence (fun _ => Mb) ?_ (integrable_const _) ?_ ?_
    · intro J
      exact (hΨ J).aestronglyMeasurable
    · intro J
      exact Filter.Eventually.of_forall fun ω => by simpa using hfb _ _
    · filter_upwards [def_app_vol_product_summable Fp] with ω hω
      have h1 := vrp_partial_tendsto (fun j => emaW Fp.β j • indepBatchG Fp ω (t + 1 - (j : ℤ))) (hω t)
      have h2 := vrp_partial_tendsto' (fun j => emaW Fp.β j • indepBatchG Fp ω ((t + (ℓ : ℤ)) + 1 - (j : ℤ)))
        (hω (t + (ℓ : ℤ))) ℓ
      have h4 := (hfc.tendsto _).comp (h1.prodMk_nhds h2)
      refine h4.congr (fun J => ?_)
      have := hindep ω J
      simp only [Prod.mk.injEq] at this
      simp only [Function.comp, Ψ]
      rw [← this.1, ← this.2]
  have hlim := (hFlim.sub hGlim).abs
  exact le_of_tendsto' hlim hwin


/-! ### Complex dilation resolvent -/

private abbrev IDx (m n : ℕ) := Fin m ⊕ Fin n
private abbrev CMat (m n : ℕ) := Matrix (IDx m n) (IDx m n) ℂ

private abbrev cOf {a b : ℕ} (K : Matrix (Fin a) (Fin b) ℝ) : Matrix (Fin a) (Fin b) ℂ :=
  K.map Complex.ofRealHom

/-- `i √s` -/
private def zI (s : ℝ) : ℂ := Complex.I * (Real.sqrt s : ℂ)

private lemma zI_sq {s : ℝ} (hs : 0 < s) : zI s * zI s = -(s : ℂ) := by
  unfold zI
  have : ((Real.sqrt s : ℝ) : ℂ) * ((Real.sqrt s : ℝ) : ℂ) = (s : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt hs.le]
  calc Complex.I * (Real.sqrt s : ℂ) * (Complex.I * (Real.sqrt s : ℂ))
      = Complex.I * Complex.I * ((Real.sqrt s : ℂ) * (Real.sqrt s : ℂ)) := by ring
    _ = -(s : ℂ) := by rw [this, Complex.I_mul_I]; ring

private def cDil {m n : ℕ} (K : Mat m n) : CMat m n :=
  Matrix.fromBlocks 0 (cOf K) (cOf Kᵀ) 0

private def cP {m n : ℕ} (K : Mat m n) (s : ℝ) : CMat m n :=
  Matrix.fromBlocks (zI s • cOf (Rs K s)) (cOf (Xs K s)) (cOf (Xs K s)ᵀ) (zI s • cOf (Rts K s))

private lemma Rs_symm {m n : ℕ} (K : Mat m n) (s : ℝ) : (Rs K s)ᵀ = Rs K s := by
  unfold Rs
  rw [Matrix.transpose_nonsing_inv]
  congr 1
  simp [Matrix.transpose_add, Matrix.transpose_mul]

private lemma Rts_symm {m n : ℕ} (K : Mat m n) (s : ℝ) : (Rts K s)ᵀ = Rts K s := by
  unfold Rts
  rw [Matrix.transpose_nonsing_inv]
  congr 1
  simp [Matrix.transpose_add, Matrix.transpose_mul]

private lemma Gm_unit {m n : ℕ} (K : Mat m n) {s : ℝ} (hs : 0 < s) :
    IsUnit (K * Kᵀ + s • (1 : Mat m m)).det := by
  have h1 : (K * Kᵀ).PosSemidef := by
    have h := Matrix.posSemidef_self_mul_conjTranspose K
    rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at h
  have h2 : (s • (1 : Mat m m)).PosDef := Matrix.PosDef.one.smul hs
  have h3 := Matrix.PosDef.add_posSemidef h2 h1
  rw [add_comm]
  exact isUnit_iff_ne_zero.mpr h3.det_pos.ne'

private lemma cres_real {m n : ℕ} (K : Mat m n) {s : ℝ} (hs : 0 < s) :
    s • Rs K s + K * (Xs K s)ᵀ = 1 ∧ K * Rts K s = Xs K s ∧
      Kᵀ * Xs K s + s • Rts K s = 1 ∧ Kᵀ * Rs K s = (Xs K s)ᵀ := by
  obtain ⟨-, -, -, h4, h5, h6, -⟩ := lem_app_de_resolvent K s hs
  have hX : (Xs K s)ᵀ = Kᵀ * Rs K s := by
    unfold Xs
    rw [Matrix.transpose_mul, Rs_symm]
  refine ⟨?_, ?_, ?_, hX.symm⟩
  · rw [hX]
    calc s • Rs K s + K * (Kᵀ * Rs K s) = (K * Kᵀ + s • (1 : Mat m m)) * Rs K s := by
          rw [Matrix.add_mul, ← Matrix.mul_assoc, Matrix.smul_mul, Matrix.one_mul, add_comm]
      _ = 1 := Matrix.mul_nonsing_inv _ (Gm_unit K hs)
  · exact h4.symm
  · have := h5
    rw [show Xs K s = Rs K s * K from rfl]
    calc Kᵀ * (Rs K s * K) + s • Rts K s = Kᵀ * Rs K s * K + s • Rts K s := by rw [Matrix.mul_assoc]
      _ = 1 := by rw [this]; abel


private lemma cOf_mul {a b c : ℕ} (A : Matrix (Fin a) (Fin b) ℝ) (B : Matrix (Fin b) (Fin c) ℝ) :
    cOf (A * B) = cOf A * cOf B := Matrix.map_mul

private lemma cOf_one {a : ℕ} : cOf (1 : Matrix (Fin a) (Fin a) ℝ) = 1 := by
  ext i j; simp [Matrix.one_apply]

private lemma cOf_add {a b : ℕ} (A B : Matrix (Fin a) (Fin b) ℝ) : cOf (A + B) = cOf A + cOf B := by
  ext i j; simp

private lemma cOf_smul {a b : ℕ} (c : ℝ) (A : Matrix (Fin a) (Fin b) ℝ) :
    cOf (c • A) = (c : ℂ) • cOf A := by
  ext i j; simp

private lemma cP_left {m n : ℕ} (K : Mat m n) {s : ℝ} (hs : 0 < s) :
    (cDil K - zI s • (1 : CMat m n)) * cP K s = 1 := by
  obtain ⟨r1, r2, r3, r4⟩ := cres_real K hs
  have hz := zI_sq hs
  have e1 : cDil K - zI s • (1 : CMat m n) =
      Matrix.fromBlocks (-(zI s • (1 : Matrix (Fin m) (Fin m) ℂ))) (cOf K) (cOf Kᵀ)
        (-(zI s • (1 : Matrix (Fin n) (Fin n) ℂ))) := by
    ext (i | i) (j | j) <;> simp [cDil, Matrix.one_apply] <;> split_ifs <;> simp_all
  rw [e1, cP, Matrix.fromBlocks_multiply, ← Matrix.fromBlocks_one]
  congr 1
  · -- top-left
    have := congrArg cOf r1
    rw [cOf_add, cOf_smul, cOf_mul, cOf_one] at this
    calc -(zI s • (1 : Matrix (Fin m) (Fin m) ℂ)) * (zI s • cOf (Rs K s)) + cOf K * cOf (Xs K s)ᵀ
        = (s : ℂ) • cOf (Rs K s) + cOf K * cOf (Xs K s)ᵀ := by
          rw [Matrix.neg_mul, Matrix.smul_mul, Matrix.one_mul, smul_smul, hz]; simp
      _ = 1 := this
  · -- top-right
    have := congrArg cOf r2
    rw [cOf_mul] at this
    rw [Matrix.neg_mul, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul, ← this]
    abel
  · -- bottom-left
    have := congrArg cOf r4
    rw [cOf_mul] at this
    rw [Matrix.neg_mul, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul, this]
    abel
  · have := congrArg cOf r3
    rw [cOf_add, cOf_smul, cOf_mul, cOf_one] at this
    calc cOf Kᵀ * cOf (Xs K s) + -(zI s • (1 : Matrix (Fin n) (Fin n) ℂ)) * (zI s • cOf (Rts K s))
        = cOf Kᵀ * cOf (Xs K s) + (s : ℂ) • cOf (Rts K s) := by
          rw [Matrix.neg_mul, Matrix.smul_mul, Matrix.one_mul, smul_smul, hz]; simp
      _ = 1 := this


/-- Abstract Woodbury-type algebra from the two resolvent identities. -/
private lemma woodbury_alg {ι : Type*} [Fintype ι] [DecidableEq ι]
    (D P P' : Matrix ι ι ℂ) (Z : Matrix ι (Fin 2) ℂ) (J : Matrix (Fin 2) (Fin 2) ℂ) (c z : ℂ)
    (hJ : J * J = 1)
    (hP : (D - z • 1) * P = 1)
    (hP' : (D + c • (Z * J * Zᵀ) - z • 1) * P' = 1) :
    P' = P - P * Z * (c • J - (c * c) • (J * (Zᵀ * (P' * Z)) * J)) * Zᵀ * P ∧
    Zᵀ * (P' * Z) = Zᵀ * (P * Z) - (Zᵀ * (P * Z)) * (c • J - (c * c) • (J * (Zᵀ * (P' * Z)) * J)) * (Zᵀ * (P * Z)) ∧
    (c • J - (c * c) • (J * (Zᵀ * (P' * Z)) * J)) * (1 + c • ((Zᵀ * (P * Z)) * J)) = c • J ∧
    (1 + c • (J * (Zᵀ * (P * Z)))) * (c • J - (c * c) • (J * (Zᵀ * (P' * Z)) * J)) = c • J := by
  set Δ : Matrix ι ι ℂ := Z * J * Zᵀ with hΔ
  have hPl : P * (D - z • 1) = 1 := mul_eq_one_comm.mp hP
  have hP'l : P' * (D + c • Δ - z • 1) = 1 := mul_eq_one_comm.mp hP'
  have R1 : P' = P - c • (P * Δ * P') := by
    calc P' = (P * (D - z • 1)) * P' := by rw [hPl, Matrix.one_mul]
      _ = P * ((D + c • Δ - z • 1) - c • Δ) * P' := by
          congr 2; abel
      _ = P * ((D + c • Δ - z • 1) * P') - c • (P * Δ * P') := by
          simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]
      _ = P - c • (P * Δ * P') := by rw [hP', Matrix.mul_one]
  have R2 : P' = P - c • (P' * Δ * P) := by
    calc P' = P' * ((D - z • 1) * P) := by rw [hP, Matrix.mul_one]
      _ = P' * (((D + c • Δ - z • 1) - c • Δ) * P) := by
          congr 2; abel
      _ = (P' * (D + c • Δ - z • 1)) * P - c • (P' * Δ * P) := by
          simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]
      _ = P - c • (P' * Δ * P) := by rw [hP'l, Matrix.one_mul]
  set W : Matrix (Fin 2) (Fin 2) ℂ := Zᵀ * (P * Z) with hW
  set W' : Matrix (Fin 2) (Fin 2) ℂ := Zᵀ * (P' * Z) with hW'
  -- sandwiched resolvent identities
  have S1 : W' = W - c • (W * (J * W')) := by
    have := congrArg (fun M => Zᵀ * (M * Z)) R1
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc, hΔ] at this
    simp only [hW, hW', Matrix.mul_assoc]
    exact this
  have S2 : W' = W - c • (W' * (J * W)) := by
    have := congrArg (fun M => Zᵀ * (M * Z)) R2
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc, hΔ] at this
    simp only [hW, hW', Matrix.mul_assoc]
    exact this
  have T2 : Zᵀ * P' = Zᵀ * P - c • (W' * (J * (Zᵀ * P))) := by
    have := congrArg (fun M => Zᵀ * M) R2
    simp only [Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_assoc, hΔ] at this
    simp only [hW', Matrix.mul_assoc]
    exact this
  set C : Matrix (Fin 2) (Fin 2) ℂ := c • J - (c * c) • (J * W' * J) with hC
  have ha : P' = P - P * Z * C * Zᵀ * P := by
    calc P' = P - c • (P * Δ * P') := R1
      _ = P - c • (P * Z * J * (Zᵀ * P')) := by simp only [hΔ, Matrix.mul_assoc]
      _ = P - P * Z * C * Zᵀ * P := by
          rw [T2, hC]
          simp only [Matrix.mul_sub, Matrix.mul_smul, Matrix.smul_mul, Matrix.sub_mul, Matrix.mul_assoc,
            smul_smul, smul_sub, hW']
  refine ⟨ha, ?_, ?_, ?_⟩
  · calc W' = Zᵀ * (P' * Z) := rfl
      _ = Zᵀ * ((P - P * Z * C * Zᵀ * P) * Z) := by rw [← ha]
      _ = W - W * C * W := by
          simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc, hW]
  · have hE : W - W' - c • (W' * (J * W)) = 0 := by
      have := S2
      calc W - W' - c • (W' * (J * W)) = W - (W - c • (W' * (J * W))) - c • (W' * (J * W)) := by
            rw [← S2]
        _ = 0 := by abel
    calc C * (1 + c • (W * J)) = c • J + (c * c) • (J * (W - W' - c • (W' * (J * W))) * J) := by
          simp only [hC, Matrix.mul_add, Matrix.mul_sub, Matrix.add_mul, Matrix.sub_mul, Matrix.smul_mul,
            Matrix.mul_smul, Matrix.mul_one, Matrix.one_mul, Matrix.mul_assoc, smul_smul, smul_add, smul_sub]
          module
      _ = c • J := by rw [hE]; simp
  · have hE : W - W' - c • (W * (J * W')) = 0 := by
      calc W - W' - c • (W * (J * W')) = W - (W - c • (W * (J * W'))) - c • (W * (J * W')) := by
            rw [← S1]
        _ = 0 := by abel
    calc (1 + c • (J * W)) * C = c • J + (c * c) • (J * (W - W' - c • (W * (J * W'))) * J) := by
          simp only [hC, Matrix.mul_add, Matrix.mul_sub, Matrix.add_mul, Matrix.sub_mul, Matrix.smul_mul,
            Matrix.mul_smul, Matrix.mul_one, Matrix.one_mul, Matrix.mul_assoc, smul_smul, smul_add, smul_sub]
          module
      _ = c • J := by rw [hE]; simp


private def J2 : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]

private lemma J2_mul : J2 * J2 = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [J2, Matrix.mul_apply, Fin.sum_univ_two]

private def Zc {m n : ℕ} (x : Vec m) (y : Vec n) : Matrix (IDx m n) (Fin 2) ℂ :=
  Matrix.of fun a k => Sum.elim (fun i => if k = 0 then (x i : ℂ) else 0)
    (fun j => if k = 1 then (y j : ℂ) else 0) a

private lemma cDil_rank {m n : ℕ} (K : Mat m n) (c : ℝ) (x : Vec m) (y : Vec n) :
    cDil (K + c • outer x y) = cDil K + (c : ℂ) • (Zc x y * J2 * (Zc x y)ᵀ) := by
  ext (i | i) (j | j)
  · simp [cDil, Zc, J2, Matrix.mul_apply, Fin.sum_univ_two]
  · simp [cDil, Zc, J2, Matrix.mul_apply, Fin.sum_univ_two, outer, Matrix.vecMulVec_apply]
  · simp [cDil, Zc, J2, Matrix.mul_apply, Fin.sum_univ_two, outer, Matrix.vecMulVec_apply]
  · simp [cDil, Zc, J2, Matrix.mul_apply, Fin.sum_univ_two]

private lemma cP_woodbury {m n : ℕ} (K : Mat m n) (c : ℝ) (x : Vec m) (y : Vec n) {s : ℝ} (hs : 0 < s) :
    let P := cP K s
    let P' := cP (K + c • outer x y) s
    let Z := Zc x y
    let W := Zᵀ * (P * Z)
    let W' := Zᵀ * (P' * Z)
    let C := (c : ℂ) • J2 - ((c : ℂ) * c) • (J2 * W' * J2)
    P' = P - P * Z * C * Zᵀ * P ∧ W' = W - W * C * W ∧
      C * (1 + (c : ℂ) • (W * J2)) = (c : ℂ) • J2 ∧ (1 + (c : ℂ) • (J2 * W)) * C = (c : ℂ) • J2 := by
  intro P P' Z W W' C
  have hP := cP_left K hs
  have hP' := cP_left (K + c • outer x y) hs
  rw [cDil_rank] at hP'
  exact woodbury_alg (cDil K) P P' Z J2 (c : ℂ) (zI s) J2_mul hP hP'

/-- Block matrices `D_F = diag(F, 0)` and `D_G = diag(0, G)`. -/
private def DFm {m n : ℕ} (F : Mat m m) : CMat m n := Matrix.fromBlocks (cOf F) 0 0 0
private def DGm {m n : ℕ} (G : Mat n n) : CMat m n := Matrix.fromBlocks 0 0 0 (cOf G)

private lemma trace_fb {a b : ℕ} (A : Matrix (Fin a) (Fin a) ℂ) (B : Matrix (Fin a) (Fin b) ℂ)
    (C : Matrix (Fin b) (Fin a) ℂ) (D : Matrix (Fin b) (Fin b) ℂ) :
    Matrix.trace (Matrix.fromBlocks A B C D) = Matrix.trace A + Matrix.trace D := by
  simp [Matrix.trace, Matrix.diag, Fintype.sum_sum_type]

private lemma trace_contraction {m n : ℕ} (F : Mat m m) (G : Mat n n) (K H : Mat m n) (s u : ℝ) :
    Matrix.trace (DFm F * cP K s * DGm G * cP H u) =
      ((Matrix.trace (F * Xs K s * G * (Xs H u)ᵀ) : ℝ) : ℂ) := by
  unfold DFm DGm cP
  rw [Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply,
    trace_fb]
  simp only [Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add, Matrix.trace_zero]
  have : cOf (F * Xs K s * G * (Xs H u)ᵀ) = cOf F * cOf (Xs K s) * cOf G * cOf (Xs H u)ᵀ := by
    simp only [cOf_mul]
  have h2 : ((Matrix.trace (F * Xs K s * G * (Xs H u)ᵀ) : ℝ) : ℂ) =
      Matrix.trace (cOf (F * Xs K s * G * (Xs H u)ᵀ)) := by
    unfold Matrix.trace Matrix.diag
    simp
  rw [h2, this]

private lemma trace_expand {ι : Type*} [Fintype ι] [DecidableEq ι]
    (DF DG P Q : Matrix ι ι ℂ) (Z : Matrix ι (Fin 2) ℂ) (C C' : Matrix (Fin 2) (Fin 2) ℂ) :
    Matrix.trace (DF * (P - P * Z * C * Zᵀ * P) * DG * (Q - Q * Z * C' * Zᵀ * Q)) =
      Matrix.trace (DF * P * DG * Q) - Matrix.trace (C * (Zᵀ * (P * DG * Q * DF * P * Z)))
        - Matrix.trace (C' * (Zᵀ * (Q * DF * P * DG * Q * Z)))
        + Matrix.trace (C * (Zᵀ * (P * DG * Q * Z)) * C' * (Zᵀ * (Q * DF * P * Z))) := by
  have h1 : Matrix.trace (DF * (P * Z * C * Zᵀ * P) * DG * Q) =
      Matrix.trace (C * (Zᵀ * (P * DG * Q * DF * P * Z))) := by
    have : DF * (P * Z * C * Zᵀ * P) * DG * Q = (DF * P * Z) * (C * (Zᵀ * P * DG * Q)) := by
      simp only [Matrix.mul_assoc]
    rw [this, Matrix.trace_mul_comm]
    simp only [Matrix.mul_assoc]
  have h2 : Matrix.trace (DF * P * DG * (Q * Z * C' * Zᵀ * Q)) =
      Matrix.trace (C' * (Zᵀ * (Q * DF * P * DG * Q * Z))) := by
    have : DF * P * DG * (Q * Z * C' * Zᵀ * Q) = (DF * P * DG * Q * Z) * (C' * (Zᵀ * Q)) := by
      simp only [Matrix.mul_assoc]
    rw [this, Matrix.trace_mul_comm]
    simp only [Matrix.mul_assoc]
  have h3 : Matrix.trace (DF * (P * Z * C * Zᵀ * P) * DG * (Q * Z * C' * Zᵀ * Q)) =
      Matrix.trace (C * (Zᵀ * (P * DG * Q * Z)) * C' * (Zᵀ * (Q * DF * P * Z))) := by
    have : DF * (P * Z * C * Zᵀ * P) * DG * (Q * Z * C' * Zᵀ * Q) =
        (DF * P * Z) * (C * (Zᵀ * (P * DG * Q * Z)) * C' * (Zᵀ * Q)) := by
      simp only [Matrix.mul_assoc]
    rw [this, Matrix.trace_mul_comm]
    simp only [Matrix.mul_assoc]
  have e : DF * (P - P * Z * C * Zᵀ * P) * DG * (Q - Q * Z * C' * Zᵀ * Q) =
      DF * P * DG * Q - DF * (P * Z * C * Zᵀ * P) * DG * Q - DF * P * DG * (Q * Z * C' * Zᵀ * Q)
        + DF * (P * Z * C * Zᵀ * P) * DG * (Q * Z * C' * Zᵀ * Q) := by
    simp only [Matrix.mul_sub, Matrix.sub_mul]
    abel
  rw [e, Matrix.trace_add, Matrix.trace_sub, Matrix.trace_sub, h1, h2, h3]

/-- The exact increment (`eqn:app-vol-increment`): `B (f(K', H') − f(K, H)) = Φ`. -/
private lemma increment_exact {m n : ℕ} (B : ℕ) (hB : 0 < B) (F : Mat m m) (G : Mat n n) {s u : ℝ}
    (hs : 0 < s) (hu : 0 < u) (K H : Mat m n) (c c' : ℝ) (x : Vec m) (y : Vec n) :
    let P := cP K s
    let Q := cP H u
    let Z := Zc x y
    let W := Zᵀ * (P * Z)
    let W' := Zᵀ * (cP (K + c • outer x y) s * Z)
    let V := Zᵀ * (Q * Z)
    let V' := Zᵀ * (cP (H + c' • outer x y) u * Z)
    let C := (c : ℂ) • J2 - ((c : ℂ) * c) • (J2 * W' * J2)
    let C' := (c' : ℂ) • J2 - ((c' : ℂ) * c') • (J2 * V' * J2)
    let A1 := Zᵀ * (P * DGm G * Q * DFm F * P * Z)
    let B1 := Zᵀ * (Q * DFm F * P * DGm G * Q * Z)
    let E1 := Zᵀ * (P * DGm G * Q * Z)
    let T1 := Zᵀ * (Q * DFm F * P * Z)
    (B : ℂ) * ((contractionRes B F G s u (K + c • outer x y) (H + c' • outer x y) -
        contractionRes B F G s u K H : ℝ) : ℂ) =
      -Matrix.trace (C * A1) - Matrix.trace (C' * B1) + Matrix.trace (C * E1 * C' * T1) := by
  intro P Q Z W W' V V' C C' A1 B1 E1 T1
  have hB0 : (B : ℂ) ≠ 0 := by exact_mod_cast hB.ne'
  obtain ⟨hPa, -, -, -⟩ := cP_woodbury K c x y hs
  obtain ⟨hQa, -, -, -⟩ := cP_woodbury H c' x y hu
  have e : ∀ K' H' : Mat m n, ((contractionRes B F G s u K' H' : ℝ) : ℂ) =
      (B : ℂ)⁻¹ * Matrix.trace (DFm F * cP K' s * DGm G * cP H' u) := by
    intro K' H'
    rw [trace_contraction]
    unfold contractionRes contraction
    rw [eqn_app_vol_filters_sharp_i hs, eqn_app_vol_filters_sharp_i hu]
    push_cast
    rfl
  rw [Complex.ofReal_sub, e, e]
  have key1 : cP (K + c • outer x y) s = P - P * Z * C * Zᵀ * P := hPa
  have key2 : cP (H + c' • outer x y) u = Q - Q * Z * C' * Zᵀ * Q := hQa
  rw [key1, key2, trace_expand]
  field_simp
  ring


/-! ### Euclidean norms of complex vectors and operator bounds -/

private def cn {ι : Type*} [Fintype ι] (v : ι → ℂ) : ℝ := Real.sqrt (∑ a, ‖v a‖ ^ 2)

private lemma cn_eq {ι : Type*} [Fintype ι] (v : ι → ℂ) :
    cn v = ‖(WithLp.toLp 2 v : EuclideanSpace ℂ ι)‖ := by
  rw [EuclideanSpace.norm_eq]; rfl

private lemma cn_nonneg {ι : Type*} [Fintype ι] (v : ι → ℂ) : 0 ≤ cn v := Real.sqrt_nonneg _

private lemma cn_sq {ι : Type*} [Fintype ι] (v : ι → ℂ) : cn v ^ 2 = ∑ a, ‖v a‖ ^ 2 := by
  unfold cn
  rw [Real.sq_sqrt (Finset.sum_nonneg fun a _ => sq_nonneg _)]

private lemma cn_add {ι : Type*} [Fintype ι] (v w : ι → ℂ) : cn (v + w) ≤ cn v + cn w := by
  rw [cn_eq, cn_eq, cn_eq]
  exact norm_add_le (WithLp.toLp 2 v : EuclideanSpace ℂ ι) (WithLp.toLp 2 w)

private lemma cn_smul {ι : Type*} [Fintype ι] (a : ℂ) (v : ι → ℂ) : cn (a • v) = ‖a‖ * cn v := by
  rw [cn_eq, cn_eq]
  exact norm_smul a (WithLp.toLp 2 v : EuclideanSpace ℂ ι)

private lemma cn_zero {ι : Type*} [Fintype ι] : cn (0 : ι → ℂ) = 0 := by
  simp [cn]

/-- Cauchy–Schwarz for the (non-conjugated) bilinear pairing. -/
private lemma cn_cs {ι : Type*} [Fintype ι] (a b : ι → ℂ) : ‖∑ i, a i * b i‖ ≤ cn a * cn b := by
  calc ‖∑ i, a i * b i‖ ≤ ∑ i, ‖a i‖ * ‖b i‖ := by
        refine (norm_sum_le _ _).trans (le_of_eq ?_)
        simp [norm_mul]
    _ ≤ cn a * cn b := by
        have := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ (fun i => ‖a i‖) (fun i => ‖b i‖)
        simpa [cn] using this

private def OB {κ ι : Type*} [Fintype κ] [Fintype ι] (M : Matrix κ ι ℂ) (c : ℝ) : Prop :=
  ∀ v : ι → ℂ, cn (M *ᵥ v) ≤ c * cn v

private lemma OB_mul {κ ι ρ : Type*} [Fintype κ] [Fintype ι] [Fintype ρ] {M : Matrix κ ι ℂ}
    {N : Matrix ι ρ ℂ} {c d : ℝ} (hc : 0 ≤ c) (hM : OB M c) (hN : OB N d) : OB (M * N) (c * d) := by
  intro v
  rw [← Matrix.mulVec_mulVec]
  calc cn (M *ᵥ (N *ᵥ v)) ≤ c * cn (N *ᵥ v) := hM _
    _ ≤ c * (d * cn v) := mul_le_mul_of_nonneg_left (hN v) hc
    _ = c * d * cn v := by ring

private lemma OB_add {κ ι : Type*} [Fintype κ] [Fintype ι] {M N : Matrix κ ι ℂ} {c d : ℝ}
    (hM : OB M c) (hN : OB N d) : OB (M + N) (c + d) := by
  intro v
  rw [Matrix.add_mulVec]
  calc cn (M *ᵥ v + N *ᵥ v) ≤ cn (M *ᵥ v) + cn (N *ᵥ v) := cn_add _ _
    _ ≤ c * cn v + d * cn v := add_le_add (hM v) (hN v)
    _ = (c + d) * cn v := by ring

private lemma OB_smul {κ ι : Type*} [Fintype κ] [Fintype ι] {M : Matrix κ ι ℂ} {c : ℝ} (a : ℂ)
    (hM : OB M c) : OB (a • M) (‖a‖ * c) := by
  intro v
  rw [Matrix.smul_mulVec, cn_smul]
  calc ‖a‖ * cn (M *ᵥ v) ≤ ‖a‖ * (c * cn v) := mul_le_mul_of_nonneg_left (hM v) (norm_nonneg _)
    _ = ‖a‖ * c * cn v := by ring

private lemma OB_mono {κ ι : Type*} [Fintype κ] [Fintype ι] {M : Matrix κ ι ℂ} {c d : ℝ}
    (hM : OB M c) (h : c ≤ d) : OB M d := fun v =>
  (hM v).trans (mul_le_mul_of_nonneg_right h (cn_nonneg v))

private lemma OB_one {ι : Type*} [Fintype ι] [DecidableEq ι] : OB (1 : Matrix ι ι ℂ) 1 := by
  intro v; simp

private lemma OB_zero {κ ι : Type*} [Fintype κ] [Fintype ι] : OB (0 : Matrix κ ι ℂ) 0 := by
  intro v; simp [cn_zero]

private lemma cn_mulVec_le {κ ι : Type*} [Fintype κ] [Fintype ι] {M : Matrix κ ι ℂ} {c : ℝ}
    (hM : OB M c) (a : κ → ℂ) (b : ι → ℂ) :
    ‖∑ i, a i * (M *ᵥ b) i‖ ≤ c * cn a * cn b := by
  calc ‖∑ i, a i * (M *ᵥ b) i‖ ≤ cn a * cn (M *ᵥ b) := cn_cs _ _
    _ ≤ cn a * (c * cn b) := mul_le_mul_of_nonneg_left (hM b) (cn_nonneg _)
    _ = c * cn a * cn b := by ring

/-- Real operator norm bound lifted to complex vectors. -/
private lemma OB_real {a b : ℕ} (L : Mat a b) {c : ℝ} (hc : opNorm L ≤ c) : OB (cOf L) c := by
  have hc0 : 0 ≤ c := (by unfold opNorm; exact norm_nonneg _ : (0:ℝ) ≤ opNorm L).trans hc
  have hreal : ∀ u : Fin b → ℝ, ∑ i, (L *ᵥ u) i ^ 2 ≤ c ^ 2 * ∑ j, u j ^ 2 := by
    intro u
    have h2 : ‖Matrix.toEuclideanLin L (WithLp.toLp 2 u)‖ ≤ opNorm L * ‖WithLp.toLp 2 u‖ := by
      have := (LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin L)).le_opNorm (WithLp.toLp 2 u)
      simpa [opNorm] using this
    have hn : ∀ v : Fin b → ℝ, ‖WithLp.toLp 2 v‖ ^ 2 = ∑ i, v i ^ 2 := by
      intro v
      rw [EuclideanSpace.norm_sq_eq]
      simp [Real.norm_eq_abs, sq_abs]
    have hm : ∀ v : Fin a → ℝ, ‖WithLp.toLp 2 v‖ ^ 2 = ∑ i, v i ^ 2 := by
      intro v
      rw [EuclideanSpace.norm_sq_eq]
      simp [Real.norm_eq_abs, sq_abs]
    have h3 : ‖Matrix.toEuclideanLin L (WithLp.toLp 2 u)‖ ≤ c * ‖WithLp.toLp 2 u‖ :=
      h2.trans (mul_le_mul_of_nonneg_right hc (norm_nonneg _))
    have h4 : Matrix.toEuclideanLin L (WithLp.toLp 2 u) = WithLp.toLp 2 (L *ᵥ u) := by
      simp [Matrix.toEuclideanLin, Matrix.toLpLin_toLp]
    rw [h4] at h3
    have := pow_le_pow_left₀ (norm_nonneg _) h3 2
    rw [hm, mul_pow, hn] at this
    exact this
  intro v
  -- split into real and imaginary parts
  have hsplit : ∀ i, ‖(cOf L *ᵥ v) i‖ ^ 2 =
      (L *ᵥ (fun j => (v j).re)) i ^ 2 + (L *ᵥ (fun j => (v j).im)) i ^ 2 := by
    intro i
    have h1 : (cOf L *ᵥ v) i = (((L *ᵥ (fun j => (v j).re)) i : ℝ) : ℂ) +
        (((L *ᵥ (fun j => (v j).im)) i : ℝ) : ℂ) * Complex.I := by
      simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, Complex.ofRealHom_eq_coe]
      push_cast
      rw [Finset.sum_mul, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      conv_lhs => rw [← Complex.re_add_im (v j)]
      ring
    rw [h1, Complex.sq_norm, Complex.normSq_apply]
    simp
    ring
  have hsq : cn (cOf L *ᵥ v) ^ 2 ≤ (c * cn v) ^ 2 := by
    rw [cn_sq, mul_pow, cn_sq]
    calc ∑ i, ‖(cOf L *ᵥ v) i‖ ^ 2
        = ∑ i, (L *ᵥ (fun j => (v j).re)) i ^ 2 + ∑ i, (L *ᵥ (fun j => (v j).im)) i ^ 2 := by
          simp only [hsplit, Finset.sum_add_distrib]
      _ ≤ c ^ 2 * ∑ j, (v j).re ^ 2 + c ^ 2 * ∑ j, (v j).im ^ 2 :=
          add_le_add (hreal _) (hreal _)
      _ = c ^ 2 * ∑ j, ‖v j‖ ^ 2 := by
          rw [← mul_add, ← Finset.sum_add_distrib]
          congr 1
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [Complex.sq_norm, Complex.normSq_apply]; ring
  exact abs_le_of_sq_le_sq' hsq (mul_nonneg hc0 (cn_nonneg v)) |>.2


private lemma cn_sum_sq {m n : ℕ} (v : IDx m n → ℂ) :
    cn v ^ 2 = cn (fun i : Fin m => v (Sum.inl i)) ^ 2 + cn (fun j : Fin n => v (Sum.inr j)) ^ 2 := by
  rw [cn_sq, cn_sq, cn_sq, Fintype.sum_sum_type]

private lemma OB_fromBlocks {m n m' n' : ℕ} {A : Matrix (Fin m') (Fin m) ℂ}
    {B : Matrix (Fin m') (Fin n) ℂ} {C : Matrix (Fin n') (Fin m) ℂ} {D : Matrix (Fin n') (Fin n) ℂ}
    {a b c d : ℝ} (ha : OB A a) (hb : OB B b) (hc : OB C c) (hd : OB D d)
    (ha0 : 0 ≤ a) (hb0 : 0 ≤ b) (hc0 : 0 ≤ c) (hd0 : 0 ≤ d) :
    OB (Matrix.fromBlocks A B C D) (a + b + c + d) := by
  intro v
  set va : Fin m → ℂ := fun i => v (Sum.inl i) with hva
  set vb : Fin n → ℂ := fun j => v (Sum.inr j) with hvb
  have hv : v = Sum.elim va vb := by
    funext x; cases x <;> rfl
  have e : Matrix.fromBlocks A B C D *ᵥ v = Sum.elim (A *ᵥ va + B *ᵥ vb) (C *ᵥ va + D *ᵥ vb) := by
    exact Matrix.fromBlocks_mulVec _ _ _ _ _
  have h1 : cn (A *ᵥ va + B *ᵥ vb) ≤ (a + b) * cn v := by
    have hva' : cn va ≤ cn v := by
      have := cn_sum_sq v
      exact abs_le_of_sq_le_sq' (by nlinarith [sq_nonneg (cn vb), cn_nonneg va, cn_nonneg v]) (cn_nonneg v) |>.2
    have hvb' : cn vb ≤ cn v := by
      have := cn_sum_sq v
      exact abs_le_of_sq_le_sq' (by nlinarith [sq_nonneg (cn va), cn_nonneg vb, cn_nonneg v]) (cn_nonneg v) |>.2
    calc cn (A *ᵥ va + B *ᵥ vb) ≤ cn (A *ᵥ va) + cn (B *ᵥ vb) := cn_add _ _
      _ ≤ a * cn va + b * cn vb := add_le_add (ha va) (hb vb)
      _ ≤ a * cn v + b * cn v := add_le_add (mul_le_mul_of_nonneg_left hva' ha0) (mul_le_mul_of_nonneg_left hvb' hb0)
      _ = (a + b) * cn v := by ring
  have h2 : cn (C *ᵥ va + D *ᵥ vb) ≤ (c + d) * cn v := by
    have hva' : cn va ≤ cn v := by
      have := cn_sum_sq v
      exact abs_le_of_sq_le_sq' (by nlinarith [sq_nonneg (cn vb), cn_nonneg va, cn_nonneg v]) (cn_nonneg v) |>.2
    have hvb' : cn vb ≤ cn v := by
      have := cn_sum_sq v
      exact abs_le_of_sq_le_sq' (by nlinarith [sq_nonneg (cn va), cn_nonneg vb, cn_nonneg v]) (cn_nonneg v) |>.2
    calc cn (C *ᵥ va + D *ᵥ vb) ≤ cn (C *ᵥ va) + cn (D *ᵥ vb) := cn_add _ _
      _ ≤ c * cn va + d * cn vb := add_le_add (hc va) (hd vb)
      _ ≤ c * cn v + d * cn v := add_le_add (mul_le_mul_of_nonneg_left hva' hc0) (mul_le_mul_of_nonneg_left hvb' hd0)
      _ = (c + d) * cn v := by ring
  rw [e]
  have hsq : cn (Sum.elim (A *ᵥ va + B *ᵥ vb) (C *ᵥ va + D *ᵥ vb)) ^ 2 =
      cn (A *ᵥ va + B *ᵥ vb) ^ 2 + cn (C *ᵥ va + D *ᵥ vb) ^ 2 := by
    rw [cn_sq, cn_sq, cn_sq, Fintype.sum_sum_type]; rfl
  have hcv := cn_nonneg v
  have hh : cn (Sum.elim (A *ᵥ va + B *ᵥ vb) (C *ᵥ va + D *ᵥ vb)) ^ 2 ≤ ((a + b + c + d) * cn v) ^ 2 := by
    rw [hsq]
    have p1 := pow_le_pow_left₀ (cn_nonneg _) h1 2
    have p2 := pow_le_pow_left₀ (cn_nonneg _) h2 2
    nlinarith [mul_nonneg (add_nonneg ha0 hb0) (add_nonneg hc0 hd0), sq_nonneg (cn v)]
  exact abs_le_of_sq_le_sq' hh (mul_nonneg (by linarith) hcv) |>.2

private lemma opNorm_transpose' {k l : ℕ} (A : Mat k l) : opNorm Aᵀ = opNorm A := by
  open scoped Matrix.Norms.L2Operator in
  rw [opNorm_eq_norm, opNorm_eq_norm, ← Matrix.conjTranspose_eq_transpose_of_trivial,
    Matrix.l2_opNorm_conjTranspose]

private lemma OB_DF {m n : ℕ} (F : Mat m m) (hF : opNorm F ≤ 1) : OB (DFm (n := n) F) 1 := by
  have := OB_fromBlocks (n := n) (n' := n) (OB_real F hF) (OB_zero (κ := Fin m) (ι := Fin n))
    (OB_zero (κ := Fin n) (ι := Fin m)) (OB_zero (κ := Fin n) (ι := Fin n)) zero_le_one le_rfl le_rfl le_rfl
  simpa [DFm] using this

private lemma OB_DG {m n : ℕ} (G : Mat n n) (hG : opNorm G ≤ 1) : OB (DGm (m := m) G) 1 := by
  have := OB_fromBlocks (m := m) (m' := m) (OB_zero (κ := Fin m) (ι := Fin m))
    (OB_zero (κ := Fin m) (ι := Fin n)) (OB_zero (κ := Fin n) (ι := Fin m)) (OB_real G hG)
    le_rfl le_rfl le_rfl zero_le_one
  simpa [DGm] using this

private lemma zI_norm (s : ℝ) : ‖zI s‖ = Real.sqrt s := by
  unfold zI
  rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]

private lemma OB_cP {m n : ℕ} (K : Mat m n) {s : ℝ} (hs : 0 < s) : OB (cP K s) (3 / Real.sqrt s) := by
  obtain ⟨h1, h2, h3, -⟩ := lem_app_de_resolvent K s hs
  have hs0 : 0 < Real.sqrt s := Real.sqrt_pos.mpr hs
  have hss : Real.sqrt s * Real.sqrt s = s := Real.mul_self_sqrt hs.le
  have hR : OB (zI s • cOf (Rs K s)) (1 / Real.sqrt s) := by
    have := OB_smul (zI s) (OB_real _ h1)
    rw [zI_norm] at this
    refine OB_mono this (le_of_eq ?_)
    field_simp
    nlinarith [hss]
  have hR' : OB (zI s • cOf (Rts K s)) (1 / Real.sqrt s) := by
    have := OB_smul (zI s) (OB_real _ h2)
    rw [zI_norm] at this
    refine OB_mono this (le_of_eq ?_)
    field_simp
    nlinarith [hss]
  have hX := OB_real (c := 1 / (2 * Real.sqrt s)) (Xs K s) h3
  have hXt := OB_real (c := 1 / (2 * Real.sqrt s)) (Xs K s)ᵀ (by rw [opNorm_transpose']; exact h3)
  have := OB_fromBlocks hR hX hXt hR' (by positivity) (by positivity) (by positivity) (by positivity)
  refine OB_mono this (le_of_eq ?_)
  field_simp
  ring


/-! ### The entrywise norm on `2 × 2` complex matrices -/

private def n2 (M : Matrix (Fin 2) (Fin 2) ℂ) : ℝ := ‖M 0 0‖ + ‖M 0 1‖ + ‖M 1 0‖ + ‖M 1 1‖

private lemma n2_nonneg (M : Matrix (Fin 2) (Fin 2) ℂ) : 0 ≤ n2 M := by
  unfold n2; positivity

private lemma n2_mul (M N : Matrix (Fin 2) (Fin 2) ℂ) : n2 (M * N) ≤ n2 M * n2 N := by
  unfold n2
  simp only [Matrix.mul_apply, Fin.sum_univ_two]
  have h : ∀ a b c d : ℂ, ‖a * b + c * d‖ ≤ ‖a‖ * ‖b‖ + ‖c‖ * ‖d‖ := fun a b c d =>
    (norm_add_le _ _).trans (by rw [norm_mul, norm_mul])
  have h00 := h (M 0 0) (N 0 0) (M 0 1) (N 1 0)
  have h01 := h (M 0 0) (N 0 1) (M 0 1) (N 1 1)
  have h10 := h (M 1 0) (N 0 0) (M 1 1) (N 1 0)
  have h11 := h (M 1 0) (N 0 1) (M 1 1) (N 1 1)
  nlinarith [norm_nonneg (M 0 0), norm_nonneg (M 0 1), norm_nonneg (M 1 0), norm_nonneg (M 1 1),
    norm_nonneg (N 0 0), norm_nonneg (N 0 1), norm_nonneg (N 1 0), norm_nonneg (N 1 1),
    mul_nonneg (norm_nonneg (M 0 0)) (norm_nonneg (N 0 0))]

private lemma n2_add (M N : Matrix (Fin 2) (Fin 2) ℂ) : n2 (M + N) ≤ n2 M + n2 N := by
  unfold n2
  simp only [Matrix.add_apply]
  have h : ∀ a b : ℂ, ‖a + b‖ ≤ ‖a‖ + ‖b‖ := fun a b => norm_add_le _ _
  linarith [h (M 0 0) (N 0 0), h (M 0 1) (N 0 1), h (M 1 0) (N 1 0), h (M 1 1) (N 1 1)]

private lemma n2_neg (M : Matrix (Fin 2) (Fin 2) ℂ) : n2 (-M) = n2 M := by
  unfold n2; simp [norm_neg]

private lemma n2_sub (M N : Matrix (Fin 2) (Fin 2) ℂ) : n2 (M - N) ≤ n2 M + n2 N := by
  rw [sub_eq_add_neg]
  exact (n2_add _ _).trans (by rw [n2_neg])

private lemma n2_smul (a : ℂ) (M : Matrix (Fin 2) (Fin 2) ℂ) : n2 (a • M) = ‖a‖ * n2 M := by
  unfold n2
  simp only [Matrix.smul_apply, smul_eq_mul, norm_mul]
  ring

private lemma n2_trace (M : Matrix (Fin 2) (Fin 2) ℂ) : ‖Matrix.trace M‖ ≤ n2 M := by
  unfold n2
  simp only [Matrix.trace, Matrix.diag, Fin.sum_univ_two]
  refine (norm_add_le _ _).trans ?_
  linarith [norm_nonneg (M 0 1), norm_nonneg (M 1 0)]

private lemma n2_J2 : n2 J2 = 2 := by
  simp [n2, J2]; norm_num

private lemma n2_one : n2 (1 : Matrix (Fin 2) (Fin 2) ℂ) = 2 := by
  simp [n2]; norm_num

private lemma n2_entry00 (M : Matrix (Fin 2) (Fin 2) ℂ) : ‖M 0 0‖ ≤ n2 M := by
  unfold n2; linarith [norm_nonneg (M 0 1), norm_nonneg (M 1 0), norm_nonneg (M 1 1)]
private lemma n2_entry01 (M : Matrix (Fin 2) (Fin 2) ℂ) : ‖M 0 1‖ ≤ n2 M := by
  unfold n2; linarith [norm_nonneg (M 0 0), norm_nonneg (M 1 0), norm_nonneg (M 1 1)]
private lemma n2_entry10 (M : Matrix (Fin 2) (Fin 2) ℂ) : ‖M 1 0‖ ≤ n2 M := by
  unfold n2; linarith [norm_nonneg (M 0 0), norm_nonneg (M 0 1), norm_nonneg (M 1 1)]
private lemma n2_entry11 (M : Matrix (Fin 2) (Fin 2) ℂ) : ‖M 1 1‖ ≤ n2 M := by
  unfold n2; linarith [norm_nonneg (M 0 0), norm_nonneg (M 0 1), norm_nonneg (M 1 0)]

/-- The telescoping identity `C - C̄ = -C (W - W̄) C̄`. -/
private lemma tele_C (c : ℂ) (W W' C C' : Matrix (Fin 2) (Fin 2) ℂ)
    (hC : C * (1 + c • (W * J2)) = c • J2) (hC' : (1 + c • (J2 * W')) * C' = c • J2) :
    C - C' = -(C * (W - W') * C') := by
  by_cases hc : c = 0
  · subst hc
    simp at hC hC'
    rw [hC, hC']; simp
  · have hJ := J2_mul
    have e1 : C * J2 + c • (C * W) = c • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
      have h := congrArg (fun M => M * J2) hC
      simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.mul_smul, Matrix.smul_mul,
        Matrix.mul_assoc, hJ] at h
      simpa using h
    have e2 : J2 * C' + c • (W' * C') = c • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
      have h := congrArg (fun M => J2 * M) hC'
      simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.mul_smul, Matrix.smul_mul,
        ← Matrix.mul_assoc, hJ, Matrix.one_mul] at h
      simpa using h
    have h1 : C * ((c⁻¹ : ℂ) • J2 + W) = 1 := by
      calc C * ((c⁻¹ : ℂ) • J2 + W) = (c⁻¹ : ℂ) • (C * J2 + c • (C * W)) := by
            simp only [Matrix.mul_add, Matrix.mul_smul, smul_add, smul_smul, inv_mul_cancel₀ hc, one_smul]
        _ = 1 := by rw [e1, smul_smul, inv_mul_cancel₀ hc, one_smul]
    have h2 : ((c⁻¹ : ℂ) • J2 + W') * C' = 1 := by
      calc ((c⁻¹ : ℂ) • J2 + W') * C' = (c⁻¹ : ℂ) • (J2 * C' + c • (W' * C')) := by
            simp only [Matrix.add_mul, Matrix.smul_mul, smul_add, smul_smul, inv_mul_cancel₀ hc, one_smul]
        _ = 1 := by rw [e2, smul_smul, inv_mul_cancel₀ hc, one_smul]
    calc C - C' = C * (((c⁻¹ : ℂ) • J2 + W') * C') - (C * ((c⁻¹ : ℂ) • J2 + W)) * C' := by
          rw [h1, h2, Matrix.mul_one, Matrix.one_mul]
      _ = -(C * (W - W') * C') := by
          simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc]
          abel


/-! ### The error estimate `Φ - Φ̄` in the `2 × 2` calculus -/

private lemma phi_err (c c' ℓ : ℝ) (C Cb C' Cb' W Wb V Vb A Ab B1 Bb E Eb T Tb : Matrix (Fin 2) (Fin 2) ℂ)
    (hCd : C - Cb = -(C * (W - Wb) * Cb)) (hCd' : C' - Cb' = -(C' * (V - Vb) * Cb'))
    (hℓ : 1 ≤ ℓ) (hc : |c| ≤ ℓ) (hc' : |c'| ≤ ℓ)
    (hC : n2 C ≤ |c| * ℓ) (hCb : n2 Cb ≤ |c| * ℓ) (hC' : n2 C' ≤ |c'| * ℓ) (hCb' : n2 Cb' ≤ |c'| * ℓ)
    (hA : n2 A ≤ ℓ) (hAb : n2 Ab ≤ ℓ) (hB : n2 B1 ≤ ℓ) (hBb : n2 Bb ≤ ℓ)
    (hE : n2 E ≤ ℓ) (hEb : n2 Eb ≤ ℓ) (hT : n2 T ≤ ℓ) (hTb : n2 Tb ≤ ℓ) :
    ‖(-Matrix.trace (C * A) - Matrix.trace (C' * B1) + Matrix.trace (C * E * C' * T)) -
      (-Matrix.trace (Cb * Ab) - Matrix.trace (Cb' * Bb) + Matrix.trace (Cb * Eb * Cb' * Tb))‖ ≤
      2 * (|c| + |c'|) * ℓ ^ 7 * (n2 (W - Wb) + n2 (V - Vb) + n2 (A - Ab) + n2 (B1 - Bb) +
        n2 (E - Eb) + n2 (T - Tb)) := by
  have hl0 : 0 ≤ ℓ := by linarith
  have ha0 := abs_nonneg c
  have hb0 := abs_nonneg c'
  set dW := n2 (W - Wb) with hdW
  set dV := n2 (V - Vb) with hdV
  set dA := n2 (A - Ab) with hdA
  set dB := n2 (B1 - Bb) with hdB
  set dE := n2 (E - Eb) with hdE
  set dT := n2 (T - Tb) with hdT
  have n0 : ∀ M : Matrix (Fin 2) (Fin 2) ℂ, 0 ≤ n2 M := n2_nonneg
  have d0 := n0 (W - Wb)
  have d1 := n0 (V - Vb)
  have d2 := n0 (A - Ab)
  have d3 := n0 (B1 - Bb)
  have d4 := n0 (E - Eb)
  have d5 := n0 (T - Tb)
  have hdCn := n0 (C - Cb)
  have hdCn' := n0 (C' - Cb')
  have hCb0 := n0 Cb
  have hCb0' := n0 Cb'
  have hC0 := n0 C
  have hC0' := n0 C'
  have hE0 := n0 E
  have hT0 := n0 T
  have hEb0 := n0 Eb
  have hTb0 := n0 Tb
  have hA0 := n0 A
  have hB0 := n0 B1
  have hAb0 := n0 Ab
  have hBb0 := n0 Bb
  have hp : ∀ k : ℕ, k ≤ 7 → ℓ ^ k ≤ ℓ ^ 7 := fun k hk => pow_le_pow_right₀ hℓ hk
  -- difference of the C's
  have hdC : n2 (C - Cb) ≤ |c| * |c| * ℓ ^ 2 * dW := by
    rw [hCd, n2_neg]
    calc n2 (C * (W - Wb) * Cb) ≤ n2 (C * (W - Wb)) * n2 Cb := n2_mul _ _
      _ ≤ (n2 C * n2 (W - Wb)) * n2 Cb := mul_le_mul_of_nonneg_right (n2_mul _ _) (n0 _)
      _ ≤ ((|c| * ℓ) * dW) * (|c| * ℓ) := by gcongr
      _ = |c| * |c| * ℓ ^ 2 * dW := by ring
  have hdC' : n2 (C' - Cb') ≤ |c'| * |c'| * ℓ ^ 2 * dV := by
    rw [hCd', n2_neg]
    calc n2 (C' * (V - Vb) * Cb') ≤ n2 (C' * (V - Vb)) * n2 Cb' := n2_mul _ _
      _ ≤ (n2 C' * n2 (V - Vb)) * n2 Cb' := mul_le_mul_of_nonneg_right (n2_mul _ _) (n0 _)
      _ ≤ ((|c'| * ℓ) * dV) * (|c'| * ℓ) := by gcongr
      _ = |c'| * |c'| * ℓ ^ 2 * dV := by ring
  -- first trace
  have t1 : ‖Matrix.trace (C * A) - Matrix.trace (Cb * Ab)‖ ≤ |c| * ℓ ^ 7 * dW + |c| * ℓ * dA := by
    rw [← Matrix.trace_sub]
    have e : C * A - Cb * Ab = (C - Cb) * A + Cb * (A - Ab) := by
      simp only [Matrix.sub_mul, Matrix.mul_sub]; abel
    rw [e]
    refine (n2_trace _).trans ((n2_add _ _).trans ?_)
    have h1 := n2_mul (C - Cb) A
    have h2 := n2_mul Cb (A - Ab)
    have k1 : n2 ((C - Cb) * A) ≤ |c| * ℓ ^ 7 * dW := by
      calc n2 ((C - Cb) * A) ≤ n2 (C - Cb) * n2 A := h1
        _ ≤ (|c| * |c| * ℓ ^ 2 * dW) * ℓ := by gcongr
        _ = (|c| * |c|) * ℓ ^ 3 * dW := by ring
        _ ≤ (|c| * ℓ) * ℓ ^ 3 * dW := by gcongr
        _ = |c| * ℓ ^ 4 * dW := by ring
        _ ≤ |c| * ℓ ^ 7 * dW := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hp 4 (by norm_num)) ha0) d0
    have k2 : n2 (Cb * (A - Ab)) ≤ |c| * ℓ * dA := by
      calc n2 (Cb * (A - Ab)) ≤ n2 Cb * n2 (A - Ab) := h2
        _ ≤ (|c| * ℓ) * dA := by gcongr
    linarith
  have t2 : ‖Matrix.trace (C' * B1) - Matrix.trace (Cb' * Bb)‖ ≤ |c'| * ℓ ^ 7 * dV + |c'| * ℓ * dB := by
    rw [← Matrix.trace_sub]
    have e : C' * B1 - Cb' * Bb = (C' - Cb') * B1 + Cb' * (B1 - Bb) := by
      simp only [Matrix.sub_mul, Matrix.mul_sub]; abel
    rw [e]
    refine (n2_trace _).trans ((n2_add _ _).trans ?_)
    have h1 := n2_mul (C' - Cb') B1
    have h2 := n2_mul Cb' (B1 - Bb)
    have k1 : n2 ((C' - Cb') * B1) ≤ |c'| * ℓ ^ 7 * dV := by
      calc n2 ((C' - Cb') * B1) ≤ n2 (C' - Cb') * n2 B1 := h1
        _ ≤ (|c'| * |c'| * ℓ ^ 2 * dV) * ℓ := by gcongr
        _ = (|c'| * |c'|) * ℓ ^ 3 * dV := by ring
        _ ≤ (|c'| * ℓ) * ℓ ^ 3 * dV := by gcongr
        _ = |c'| * ℓ ^ 4 * dV := by ring
        _ ≤ |c'| * ℓ ^ 7 * dV := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hp 4 (by norm_num)) hb0) d1
    have k2 : n2 (Cb' * (B1 - Bb)) ≤ |c'| * ℓ * dB := by
      calc n2 (Cb' * (B1 - Bb)) ≤ n2 Cb' * n2 (B1 - Bb) := h2
        _ ≤ (|c'| * ℓ) * dB := by gcongr
    linarith
  -- third trace
  have t3 : ‖Matrix.trace (C * E * C' * T) - Matrix.trace (Cb * Eb * Cb' * Tb)‖ ≤
      |c| * ℓ ^ 7 * dW + |c| * ℓ ^ 7 * dE + |c'| * ℓ ^ 7 * dV + |c| * ℓ ^ 7 * dT := by
    rw [← Matrix.trace_sub]
    have e : C * E * C' * T - Cb * Eb * Cb' * Tb =
        (C - Cb) * E * C' * T + Cb * (E - Eb) * C' * T + Cb * Eb * (C' - Cb') * T +
          Cb * Eb * Cb' * (T - Tb) := by
      simp only [Matrix.sub_mul, Matrix.mul_sub]; abel
    rw [e]
    refine (n2_trace _).trans ?_
    have hm4 : ∀ X Y Z U : Matrix (Fin 2) (Fin 2) ℂ, n2 (X * Y * Z * U) ≤ n2 X * n2 Y * n2 Z * n2 U := by
      intro X Y Z U
      have h3 : n2 (X * Y * Z) ≤ n2 X * n2 Y * n2 Z :=
        (n2_mul _ _).trans (mul_le_mul_of_nonneg_right (n2_mul _ _) (n0 _))
      exact (n2_mul _ _).trans (mul_le_mul_of_nonneg_right h3 (n0 _))
    refine (n2_add _ _).trans (add_le_add ((n2_add _ _).trans (add_le_add ((n2_add _ _).trans (add_le_add ?_ ?_)) ?_)) ?_)
    · calc n2 ((C - Cb) * E * C' * T) ≤ n2 (C - Cb) * n2 E * n2 C' * n2 T := hm4 _ _ _ _
        _ ≤ (|c| * |c| * ℓ ^ 2 * dW) * ℓ * (|c'| * ℓ) * ℓ := by gcongr
        _ = (|c| * |c| * |c'|) * ℓ ^ 5 * dW := by ring
        _ ≤ (|c| * ℓ * ℓ) * ℓ ^ 5 * dW := by
            have : |c| * |c| * |c'| ≤ |c| * ℓ * ℓ := by gcongr
            exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right this (pow_nonneg hl0 5)) d0
        _ = |c| * ℓ ^ 7 * dW := by ring
    · calc n2 (Cb * (E - Eb) * C' * T) ≤ n2 Cb * n2 (E - Eb) * n2 C' * n2 T := hm4 _ _ _ _
        _ ≤ (|c| * ℓ) * dE * (|c'| * ℓ) * ℓ := by gcongr
        _ = (|c| * |c'|) * ℓ ^ 3 * dE := by ring
        _ ≤ (|c| * ℓ) * ℓ ^ 3 * dE := by gcongr
        _ = |c| * ℓ ^ 4 * dE := by ring
        _ ≤ |c| * ℓ ^ 7 * dE := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hp 4 (by norm_num)) ha0) d4
    · calc n2 (Cb * Eb * (C' - Cb') * T) ≤ n2 Cb * n2 Eb * n2 (C' - Cb') * n2 T := hm4 _ _ _ _
        _ ≤ (|c| * ℓ) * ℓ * (|c'| * |c'| * ℓ ^ 2 * dV) * ℓ := by gcongr
        _ = (|c| * |c'| * |c'|) * ℓ ^ 5 * dV := by ring
        _ ≤ (ℓ * |c'| * ℓ) * ℓ ^ 5 * dV := by
            have : |c| * |c'| * |c'| ≤ ℓ * |c'| * |c'| := by gcongr
            have h2 : ℓ * |c'| * |c'| ≤ ℓ * |c'| * ℓ := by gcongr
            exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (this.trans h2) (pow_nonneg hl0 5)) d1
        _ = |c'| * ℓ ^ 7 * dV := by ring
    · calc n2 (Cb * Eb * Cb' * (T - Tb)) ≤ n2 Cb * n2 Eb * n2 Cb' * n2 (T - Tb) := hm4 _ _ _ _
        _ ≤ (|c| * ℓ) * ℓ * (|c'| * ℓ) * dT := by gcongr
        _ = (|c| * |c'|) * ℓ ^ 3 * dT := by ring
        _ ≤ (|c| * ℓ) * ℓ ^ 3 * dT := by gcongr
        _ = |c| * ℓ ^ 4 * dT := by ring
        _ ≤ |c| * ℓ ^ 7 * dT := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hp 4 (by norm_num)) ha0) d5
  -- assemble
  have hsplit : (-Matrix.trace (C * A) - Matrix.trace (C' * B1) + Matrix.trace (C * E * C' * T)) -
      (-Matrix.trace (Cb * Ab) - Matrix.trace (Cb' * Bb) + Matrix.trace (Cb * Eb * Cb' * Tb)) =
      -(Matrix.trace (C * A) - Matrix.trace (Cb * Ab)) - (Matrix.trace (C' * B1) - Matrix.trace (Cb' * Bb)) +
        (Matrix.trace (C * E * C' * T) - Matrix.trace (Cb * Eb * Cb' * Tb)) := by ring
  rw [hsplit]
  have n1 := norm_add_le (-(Matrix.trace (C * A) - Matrix.trace (Cb * Ab)) - (Matrix.trace (C' * B1) - Matrix.trace (Cb' * Bb)))
    (Matrix.trace (C * E * C' * T) - Matrix.trace (Cb * Eb * Cb' * Tb))
  have n2' := norm_sub_le (-(Matrix.trace (C * A) - Matrix.trace (Cb * Ab))) (Matrix.trace (C' * B1) - Matrix.trace (Cb' * Bb))
  rw [norm_neg] at n2'
  have hl1 : ℓ ≤ ℓ ^ 7 := by simpa using hp 1 (by norm_num)
  have e1 : |c| * ℓ * dA ≤ |c| * ℓ ^ 7 * dA :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hl1 ha0) d2
  have e2 : |c'| * ℓ * dB ≤ |c'| * ℓ ^ 7 * dB :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hl1 hb0) d3
  have p1 : 0 ≤ |c| * ℓ ^ 7 * dW := by positivity
  have p2 : 0 ≤ |c| * ℓ ^ 7 * dA := by positivity
  have p3 : 0 ≤ |c| * ℓ ^ 7 * dE := by positivity
  have p4 : 0 ≤ |c| * ℓ ^ 7 * dT := by positivity
  have p5 : 0 ≤ |c'| * ℓ ^ 7 * dV := by positivity
  have p6 : 0 ≤ |c'| * ℓ ^ 7 * dB := by positivity
  have p7 : 0 ≤ |c'| * ℓ ^ 7 * dW := by positivity
  have p8 : 0 ≤ |c'| * ℓ ^ 7 * dA := by positivity
  have p9 : 0 ≤ |c'| * ℓ ^ 7 * dE := by positivity
  have p10 : 0 ≤ |c'| * ℓ ^ 7 * dT := by positivity
  have p11 : 0 ≤ |c| * ℓ ^ 7 * dV := by positivity
  have p12 : 0 ≤ |c| * ℓ ^ 7 * dB := by positivity
  have expand : 2 * (|c| + |c'|) * ℓ ^ 7 * (dW + dV + dA + dB + dE + dT) =
      2 * (|c| * ℓ ^ 7 * dW) + 2 * (|c| * ℓ ^ 7 * dV) + 2 * (|c| * ℓ ^ 7 * dA) + 2 * (|c| * ℓ ^ 7 * dB) +
      2 * (|c| * ℓ ^ 7 * dE) + 2 * (|c| * ℓ ^ 7 * dT) + 2 * (|c'| * ℓ ^ 7 * dW) + 2 * (|c'| * ℓ ^ 7 * dV) +
      2 * (|c'| * ℓ ^ 7 * dA) + 2 * (|c'| * ℓ ^ 7 * dB) + 2 * (|c'| * ℓ ^ 7 * dE) + 2 * (|c'| * ℓ ^ 7 * dT) := by ring
  rw [expand]
  linarith


/-! ### Gaussian second moments of quadratic and bilinear forms -/

private lemma vrp_G1 (n : ℕ) (U : Matrix (Fin n) (Fin n) ℝ) :
    ∫ z : Fin n → ℝ, (∑ i, ∑ j, z i * U i j * z j - U.trace) ^ 2 ∂(Muon.Foundations.stdGaussianPi n) ≤
      2 * ∑ i, ∑ j, U i j ^ 2 := by
  set Us : Matrix (Fin n) (Fin n) ℝ := (1 / 2 : ℝ) • (U + Uᵀ) with hUs
  have hsym : Usᵀ = Us := by simp [hUs, Matrix.transpose_add, add_comm]
  have hform : ∀ z : Fin n → ℝ, ∑ i, ∑ j, z i * U i j * z j = ∑ i, ∑ j, z i * Us i j * z j := by
    intro z
    have h1 : ∑ i, ∑ j, z i * Us i j * z j =
        (1 / 2 : ℝ) * (∑ i, ∑ j, z i * U i j * z j + ∑ i, ∑ j, z i * U j i * z j) := by
      simp only [hUs, Matrix.smul_apply, Matrix.add_apply, Matrix.transpose_apply, smul_eq_mul]
      rw [← Finset.sum_add_distrib]
      simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
    have h2 : ∑ i, ∑ j, z i * U j i * z j = ∑ i, ∑ j, z i * U i j * z j := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
    rw [h1, h2]; ring
  have htr : Us.trace = U.trace := by
    have : ∀ i, Us i i = U i i := by intro i; simp [hUs]; ring
    simp only [Matrix.trace, Matrix.diag, this]
  simp_rw [hform, ← htr]
  rw [Muon.Foundations.stdGaussianPi_quadratic_variance n Us hsym]
  have : (Us * Us).trace = ∑ i, ∑ j, Us i j ^ 2 := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    have : Us j i = Us i j := by
      have := congrFun (congrFun hsym i) j
      simpa [Matrix.transpose_apply] using this
    rw [this]; ring
  rw [this]
  have : ∑ i, ∑ j, Us i j ^ 2 ≤ ∑ i, ∑ j, U i j ^ 2 := by
    have e : ∑ i, ∑ j, Us i j ^ 2 = (1 / 4 : ℝ) * ∑ i, ∑ j, (U i j + U j i) ^ 2 := by
      simp only [hUs, Matrix.smul_apply, Matrix.add_apply, Matrix.transpose_apply, smul_eq_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
    have h2 : ∑ i, ∑ j, (U i j + U j i) ^ 2 ≤ 2 * (∑ i, ∑ j, U i j ^ 2 + ∑ i, ∑ j, U j i ^ 2) := by
      calc ∑ i, ∑ j, (U i j + U j i) ^ 2 ≤ ∑ i, ∑ j, 2 * (U i j ^ 2 + U j i ^ 2) :=
            Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => by nlinarith [sq_nonneg (U i j - U j i)]
        _ = 2 * (∑ i, ∑ j, U i j ^ 2 + ∑ i, ∑ j, U j i ^ 2) := by
            simp only [← Finset.mul_sum, Finset.sum_add_distrib]
    have h3 : ∑ i, ∑ j, U j i ^ 2 = ∑ i, ∑ j, U i j ^ 2 := Finset.sum_comm
    rw [e]; linarith
  linarith

private lemma vrp_G2 (m n : ℕ) (U : Matrix (Fin m) (Fin n) ℝ) :
    ∫ p : Vec m × Vec n, (∑ i, ∑ j, p.1 i * U i j * p.2 j) ^ 2 ∂(gaussPair m n) =
      ∑ i, ∑ j, U i j ^ 2 := by
  have hresid : ∀ p : Vec m × Vec n, ∑ i, ∑ j, p.1 i * U i j * p.2 j = resid U p := by
    intro p
    simp only [resid, dotProduct, Matrix.mulVec, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  simp_rw [hresid]
  by_cases hU : ∑ i, ∑ j, U i j ^ 2 = 0
  · have h0 : ∀ i j, U i j = 0 := by
      intro i j
      have h1 : ∑ j, U i j ^ 2 = 0 := by
        have := Finset.sum_eq_zero_iff_of_nonneg (fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg (U i j)) |>.1 hU i (Finset.mem_univ i)
        exact this
      have h2 := Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg (U i j)) |>.1 h1 j (Finset.mem_univ j)
      exact pow_eq_zero_iff (two_ne_zero) |>.1 h2
    have : U = 0 := by ext i j; exact h0 i j
    subst this
    simp [resid, hU]
  · set f : ℝ := Real.sqrt (∑ i, ∑ j, U i j ^ 2) with hf
    have hfpos : 0 < f := Real.sqrt_pos.2 (lt_of_le_of_ne (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _) (Ne.symm hU))
    set A : Mat m n := f⁻¹ • U with hA
    have hAfro : fro A = 1 := by
      unfold fro
      rw [Real.sqrt_eq_one]
      have : ∑ i, ∑ j, ‖A i j‖ ^ 2 = f⁻¹ ^ 2 * ∑ i, ∑ j, U i j ^ 2 := by
        simp only [hA, Matrix.smul_apply, smul_eq_mul, norm_mul, Real.norm_eq_abs, mul_pow, sq_abs, Finset.mul_sum]
      have hs : f ^ 2 = ∑ i, ∑ j, U i j ^ 2 :=
        Real.sq_sqrt (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _)
      rw [this, inv_pow, hs]
      field_simp
    have h1 := (lem_app_setup_residual_i A hAfro).2.1
    have hres : ∀ p : Vec m × Vec n, resid U p = f * resid A p := by
      intro p
      simp only [hA, resid, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]
      field_simp
    simp_rw [hres, mul_pow]
    have hs : f ^ 2 = ∑ i, ∑ j, U i j ^ 2 :=
      Real.sq_sqrt (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _)
    rw [integral_const_mul, h1, mul_one, hs]


private lemma vrp_int_sqpoly (n : ℕ) (f : (Fin n → ℝ) → ℝ) (hf : Measurable f) (C : ℝ)
    (hb : ∀ z, |f z| ≤ C * (1 + ∑ i, z i ^ 2) ^ 2) :
    Integrable f (Muon.Foundations.stdGaussianPi n) := by
  have h1 : Integrable (fun z : Fin n → ℝ => (1 + ∑ i, z i ^ 2) ^ 2) (Muon.Foundations.stdGaussianPi n) := by
    have e : ∀ z : Fin n → ℝ, (1 + ∑ i, z i ^ 2) ^ 2 = 1 + 2 * (∑ i, z i ^ 2) ^ 1 + (∑ i, z i ^ 2) ^ 2 := by
      intro z; ring
    simp_rw [e]
    exact ((integrable_const (1 : ℝ)).add ((vsw_sqpow n 1).const_mul 2)).add (vsw_sqpow n 2)
  refine Integrable.mono' (h1.const_mul C) hf.aestronglyMeasurable (Filter.Eventually.of_forall fun z => ?_)
  rw [Real.norm_eq_abs]
  exact hb z

private lemma vrp_quad_bound (n : ℕ) (U : Matrix (Fin n) (Fin n) ℝ) (z : Fin n → ℝ) :
    |∑ i, ∑ j, z i * U i j * z j - U.trace| ≤
      (∑ i, ∑ j, |U i j| + ∑ i, |U i i|) * (1 + ∑ i, z i ^ 2) := by
  have hzz : ∀ i j, |z i * z j| ≤ ∑ k, z k ^ 2 := by
    intro i j
    have h1 : |z i * z j| ≤ (z i ^ 2 + z j ^ 2) / 2 := by
      rw [abs_mul]; nlinarith [sq_nonneg (|z i| - |z j|), sq_abs (z i), sq_abs (z j), abs_nonneg (z i), abs_nonneg (z j)]
    by_cases hij : i = j
    · subst hij
      have : z i ^ 2 ≤ ∑ k, z k ^ 2 :=
        Finset.single_le_sum (f := fun k => z k ^ 2) (fun k _ => sq_nonneg _) (Finset.mem_univ i)
      nlinarith
    · have : z i ^ 2 + z j ^ 2 ≤ ∑ k, z k ^ 2 := by
        have := Finset.sum_le_sum_of_subset_of_nonneg (f := fun k => z k ^ 2)
          (Finset.subset_univ ({i, j} : Finset (Fin n))) (fun k _ _ => sq_nonneg _)
        rwa [Finset.sum_pair hij] at this
      nlinarith
  have hS0 : 0 ≤ ∑ k, z k ^ 2 := Finset.sum_nonneg fun k _ => sq_nonneg _
  have h1 : |∑ i, ∑ j, z i * U i j * z j| ≤ (∑ i, ∑ j, |U i j|) * ∑ k, z k ^ 2 := by
    calc |∑ i, ∑ j, z i * U i j * z j| ≤ ∑ i, |∑ j, z i * U i j * z j| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, ∑ j, |z i * U i j * z j| :=
          Finset.sum_le_sum fun i _ => Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, ∑ j, |U i j| * ∑ k, z k ^ 2 := Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => by
          have : |z i * U i j * z j| = |U i j| * |z i * z j| := by
            rw [abs_mul, abs_mul, abs_mul]; ring
          rw [this]
          exact mul_le_mul_of_nonneg_left (hzz i j) (abs_nonneg _)
      _ = (∑ i, ∑ j, |U i j|) * ∑ k, z k ^ 2 := by simp only [← Finset.sum_mul]
  have h2 : |U.trace| ≤ ∑ i, |U i i| := by
    simp only [Matrix.trace, Matrix.diag]
    exact Finset.abs_sum_le_sum_abs _ _
  have hD0 : 0 ≤ ∑ i, ∑ j, |U i j| := Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => abs_nonneg _
  have hD1 : 0 ≤ ∑ i, |U i i| := Finset.sum_nonneg fun i _ => abs_nonneg _
  calc |∑ i, ∑ j, z i * U i j * z j - U.trace| ≤ |∑ i, ∑ j, z i * U i j * z j| + |U.trace| := abs_sub _ _
    _ ≤ (∑ i, ∑ j, |U i j|) * ∑ k, z k ^ 2 + ∑ i, |U i i| := add_le_add h1 h2
    _ ≤ (∑ i, ∑ j, |U i j| + ∑ i, |U i i|) * (1 + ∑ i, z i ^ 2) := by nlinarith [mul_nonneg hD1 hS0]

private lemma vrp_G1' (n : ℕ) (U : Matrix (Fin n) (Fin n) ℝ) :
    Integrable (fun z : Fin n → ℝ => (∑ i, ∑ j, z i * U i j * z j - U.trace) ^ 2)
      (Muon.Foundations.stdGaussianPi n) := by
  refine vrp_int_sqpoly n _ (by fun_prop) ((∑ i, ∑ j, |U i j| + ∑ i, |U i i|) ^ 2) fun z => ?_
  rw [abs_of_nonneg (sq_nonneg _)]
  have := vrp_quad_bound n U z
  have h0 := abs_nonneg (∑ i, ∑ j, z i * U i j * z j - U.trace)
  calc (∑ i, ∑ j, z i * U i j * z j - U.trace) ^ 2
      = |∑ i, ∑ j, z i * U i j * z j - U.trace| ^ 2 := (sq_abs _).symm
    _ ≤ ((∑ i, ∑ j, |U i j| + ∑ i, |U i i|) * (1 + ∑ i, z i ^ 2)) ^ 2 :=
        pow_le_pow_left₀ h0 this 2
    _ = (∑ i, ∑ j, |U i j| + ∑ i, |U i i|) ^ 2 * (1 + ∑ i, z i ^ 2) ^ 2 := by ring

/-- Complex quadratic forms: variance bound with integrability. -/
private lemma vrp_G3a (n : ℕ) (U : Matrix (Fin n) (Fin n) ℂ) :
    Integrable (fun z : Fin n → ℝ => ‖∑ i, ∑ j, (z i : ℂ) * U i j * (z j : ℂ) - U.trace‖ ^ 2)
      (Muon.Foundations.stdGaussianPi n) ∧
    ∫ z : Fin n → ℝ, ‖∑ i, ∑ j, (z i : ℂ) * U i j * (z j : ℂ) - U.trace‖ ^ 2
      ∂(Muon.Foundations.stdGaussianPi n) ≤ 2 * ∑ i, ∑ j, ‖U i j‖ ^ 2 := by
  set Ur : Matrix (Fin n) (Fin n) ℝ := Matrix.of fun i j => (U i j).re with hUr
  set Ui : Matrix (Fin n) (Fin n) ℝ := Matrix.of fun i j => (U i j).im with hUi
  have hsplit : ∀ z : Fin n → ℝ, ‖∑ i, ∑ j, (z i : ℂ) * U i j * (z j : ℂ) - U.trace‖ ^ 2 =
      (∑ i, ∑ j, z i * Ur i j * z j - Ur.trace) ^ 2 + (∑ i, ∑ j, z i * Ui i j * z j - Ui.trace) ^ 2 := by
    intro z
    rw [Complex.sq_norm, Complex.normSq_apply]
    have hre : (∑ i, ∑ j, (z i : ℂ) * U i j * (z j : ℂ) - U.trace).re =
        ∑ i, ∑ j, z i * Ur i j * z j - Ur.trace := by
      simp [Complex.re_sum, Complex.sub_re, Matrix.trace, Matrix.diag, hUr, mul_assoc, mul_comm, mul_left_comm]
    have him : (∑ i, ∑ j, (z i : ℂ) * U i j * (z j : ℂ) - U.trace).im =
        ∑ i, ∑ j, z i * Ui i j * z j - Ui.trace := by
      simp [Complex.im_sum, Complex.sub_im, Matrix.trace, Matrix.diag, hUi, mul_assoc, mul_comm, mul_left_comm]
    rw [hre, him]; ring
  simp_rw [hsplit]
  have h1 := vrp_G1' n Ur
  have h2 := vrp_G1' n Ui
  refine ⟨h1.add h2, ?_⟩
  rw [integral_add h1 h2]
  have g1 := vrp_G1 n Ur
  have g2 := vrp_G1 n Ui
  have : ∑ i, ∑ j, ‖U i j‖ ^ 2 = ∑ i, ∑ j, Ur i j ^ 2 + ∑ i, ∑ j, Ui i j ^ 2 := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Complex.sq_norm, Complex.normSq_apply]; simp [hUr, hUi]; ring
  rw [this]; linarith


private lemma vrp_G2_int (m n : ℕ) (U : Matrix (Fin m) (Fin n) ℝ) :
    Integrable (fun p : Vec m × Vec n => (∑ i, ∑ j, p.1 i * U i j * p.2 j) ^ 2) (gaussPair m n) := by
  have hint := (vsw_sqpow m 1).mul_prod (vsw_sqpow n 1)
  unfold gaussPair
  refine (hint.const_mul ((m : ℝ) * n * ∑ i, ∑ j, U i j ^ 2)).mono' (by fun_prop : Measurable fun p : Vec m × Vec n => (∑ i, ∑ j, p.1 i * U i j * p.2 j) ^ 2).aestronglyMeasurable (Filter.Eventually.of_forall fun p => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  obtain ⟨z, w⟩ := p
  simp only [pow_one]
  have h1 : (∑ i, ∑ j, z i * U i j * w j) ^ 2 ≤ ((m * n : ℕ) : ℝ) * ∑ i, ∑ j, (z i * U i j * w j) ^ 2 := by
    have a := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin m)))
      (f := fun i => ∑ j, z i * U i j * w j)
    have b : ∀ i, (∑ j, z i * U i j * w j) ^ 2 ≤ (n : ℝ) * ∑ j, (z i * U i j * w j) ^ 2 := fun i => by
      have := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin n)))
        (f := fun j => z i * U i j * w j)
      simpa using this
    simp only [Finset.card_univ, Fintype.card_fin] at a
    calc (∑ i, ∑ j, z i * U i j * w j) ^ 2 ≤ (m : ℝ) * ∑ i, (∑ j, z i * U i j * w j) ^ 2 := by simpa using a
      _ ≤ (m : ℝ) * ∑ i, (n : ℝ) * ∑ j, (z i * U i j * w j) ^ 2 := by
          gcongr with i _
          exact b i
      _ = ((m * n : ℕ) : ℝ) * ∑ i, ∑ j, (z i * U i j * w j) ^ 2 := by
          rw [← Finset.mul_sum]; push_cast; ring
  have h2 : ∀ i j, (z i * U i j * w j) ^ 2 ≤ U i j ^ 2 * ((∑ k, z k ^ 2) * ∑ k, w k ^ 2) := by
    intro i j
    have a1 : z i ^ 2 ≤ ∑ k, z k ^ 2 :=
      Finset.single_le_sum (f := fun k => z k ^ 2) (fun k _ => sq_nonneg _) (Finset.mem_univ i)
    have a2 : w j ^ 2 ≤ ∑ k, w k ^ 2 :=
      Finset.single_le_sum (f := fun k => w k ^ 2) (fun k _ => sq_nonneg _) (Finset.mem_univ j)
    have : (z i * U i j * w j) ^ 2 = U i j ^ 2 * (z i ^ 2 * w j ^ 2) := by ring
    rw [this]
    exact mul_le_mul_of_nonneg_left (mul_le_mul a1 a2 (sq_nonneg _) (Finset.sum_nonneg fun k _ => sq_nonneg _)) (sq_nonneg _)
  calc (∑ i, ∑ j, z i * U i j * w j) ^ 2 ≤ ((m * n : ℕ) : ℝ) * ∑ i, ∑ j, (z i * U i j * w j) ^ 2 := h1
    _ ≤ ((m * n : ℕ) : ℝ) * ∑ i, ∑ j, U i j ^ 2 * ((∑ k, z k ^ 2) * ∑ k, w k ^ 2) := by
        gcongr with i _ j _
        exact h2 i j
    _ = (m : ℝ) * n * (∑ i, ∑ j, U i j ^ 2) * ((∑ k, z k ^ 2) * ∑ k, w k ^ 2) := by
        simp only [← Finset.sum_mul]; push_cast; ring

private lemma vrp_G3b (m n : ℕ) (U : Matrix (Fin m) (Fin n) ℂ) :
    Integrable (fun p : Vec m × Vec n => ‖∑ i, ∑ j, (p.1 i : ℂ) * U i j * (p.2 j : ℂ)‖ ^ 2) (gaussPair m n) ∧
    ∫ p : Vec m × Vec n, ‖∑ i, ∑ j, (p.1 i : ℂ) * U i j * (p.2 j : ℂ)‖ ^ 2 ∂(gaussPair m n) =
      ∑ i, ∑ j, ‖U i j‖ ^ 2 := by
  set Ur : Matrix (Fin m) (Fin n) ℝ := Matrix.of fun i j => (U i j).re with hUr
  set Ui : Matrix (Fin m) (Fin n) ℝ := Matrix.of fun i j => (U i j).im with hUi
  have hsplit : ∀ p : Vec m × Vec n, ‖∑ i, ∑ j, (p.1 i : ℂ) * U i j * (p.2 j : ℂ)‖ ^ 2 =
      (∑ i, ∑ j, p.1 i * Ur i j * p.2 j) ^ 2 + (∑ i, ∑ j, p.1 i * Ui i j * p.2 j) ^ 2 := by
    intro p
    rw [Complex.sq_norm, Complex.normSq_apply]
    have hre : (∑ i, ∑ j, (p.1 i : ℂ) * U i j * (p.2 j : ℂ)).re = ∑ i, ∑ j, p.1 i * Ur i j * p.2 j := by
      simp [Complex.re_sum, hUr, mul_assoc, mul_comm, mul_left_comm]
    have him : (∑ i, ∑ j, (p.1 i : ℂ) * U i j * (p.2 j : ℂ)).im = ∑ i, ∑ j, p.1 i * Ui i j * p.2 j := by
      simp [Complex.im_sum, hUi, mul_assoc, mul_comm, mul_left_comm]
    rw [hre, him]; ring
  simp_rw [hsplit]
  have h1 := vrp_G2_int m n Ur
  have h2 := vrp_G2_int m n Ui
  refine ⟨h1.add h2, ?_⟩
  rw [integral_add h1 h2, vrp_G2, vrp_G2, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Complex.sq_norm, Complex.normSq_apply]; simp [hUr, hUi]; ring


private lemma vrp_bil_eq {k l : ℕ} (a : Fin k → ℂ) (L : Matrix (Fin k) (Fin l) ℂ) (b : Fin l → ℂ) :
    ∑ i, ∑ j, a i * L i j * b j = a ⬝ᵥ (L *ᵥ b) := by
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

/-- `Σ_{ij} (R z)_i L_ij (R' w)_j = Σ_{kl} z_k (Rᵀ L R')_kl w_l` -/
private lemma vrp_bil_conj {k l p q : ℕ} (R : Matrix (Fin k) (Fin p) ℝ) (R' : Matrix (Fin l) (Fin q) ℝ)
    (L : Matrix (Fin k) (Fin l) ℂ) (z : Fin p → ℝ) (w : Fin q → ℝ) :
    ∑ i, ∑ j, ((R *ᵥ z) i : ℂ) * L i j * ((R' *ᵥ w) j : ℂ) =
      ∑ i, ∑ j, (z i : ℂ) * (cOf Rᵀ * L * cOf R') i j * (w j : ℂ) := by
  rw [vrp_bil_eq, vrp_bil_eq]
  have e1 : (fun i => (((R *ᵥ z) i : ℝ) : ℂ)) = cOf R *ᵥ (fun i => ((z i : ℝ) : ℂ)) := by
    funext i
    simp [Matrix.mulVec, dotProduct]
  have e2 : (fun i => (((R' *ᵥ w) i : ℝ) : ℂ)) = cOf R' *ᵥ (fun i => ((w i : ℝ) : ℂ)) := by
    funext i
    simp [Matrix.mulVec, dotProduct]
  have e3 : ∀ (A : Matrix (Fin k) (Fin p) ℂ) (v : Fin p → ℂ) (u : Fin k → ℂ),
      (A *ᵥ v) ⬝ᵥ u = v ⬝ᵥ (Aᵀ *ᵥ u) := by
    intro A v u
    rw [dotProduct_comm, Matrix.dotProduct_mulVec, Matrix.mulVec_transpose, dotProduct_comm]
  have e4 : (cOf R)ᵀ = cOf Rᵀ := by ext i j; simp
  rw [e1, e2, e3, e4, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc]


private lemma cn_inl_le {m n : ℕ} (w : IDx m n → ℂ) : cn (fun i : Fin m => w (Sum.inl i)) ≤ cn w := by
  have h := cn_sum_sq w
  have h1 := sq_nonneg (cn (fun j : Fin n => w (Sum.inr j)))
  have h2 := cn_nonneg (fun i : Fin m => w (Sum.inl i))
  have h3 := cn_nonneg w
  exact abs_le_of_sq_le_sq' (by nlinarith) h3 |>.2

private lemma cn_inr_le {m n : ℕ} (w : IDx m n → ℂ) : cn (fun j : Fin n => w (Sum.inr j)) ≤ cn w := by
  have h := cn_sum_sq w
  have h1 := sq_nonneg (cn (fun i : Fin m => w (Sum.inl i)))
  have h2 := cn_nonneg (fun j : Fin n => w (Sum.inr j))
  have h3 := cn_nonneg w
  exact abs_le_of_sq_le_sq' (by nlinarith) h3 |>.2

private lemma cn_elim_left {m n : ℕ} (v : Fin m → ℂ) : cn (Sum.elim v (0 : Fin n → ℂ)) = cn v := by
  unfold cn; rw [Fintype.sum_sum_type]; simp

private lemma cn_elim_right {m n : ℕ} (v : Fin n → ℂ) : cn (Sum.elim (0 : Fin m → ℂ) v) = cn v := by
  unfold cn; rw [Fintype.sum_sum_type]; simp

private lemma OB_b11 {m n : ℕ} {M : CMat m n} {c : ℝ} (h : OB M c) : OB M.toBlocks₁₁ c := by
  intro v
  have e : M.toBlocks₁₁ *ᵥ v = fun i => (M *ᵥ Sum.elim v (0 : Fin n → ℂ)) (Sum.inl i) := by
    funext i; simp [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Matrix.toBlocks₁₁]
  rw [e]
  calc _ ≤ cn (M *ᵥ Sum.elim v (0 : Fin n → ℂ)) := cn_inl_le _
    _ ≤ c * cn (Sum.elim v (0 : Fin n → ℂ)) := h _
    _ = c * cn v := by rw [cn_elim_left]

private lemma OB_b12 {m n : ℕ} {M : CMat m n} {c : ℝ} (h : OB M c) : OB M.toBlocks₁₂ c := by
  intro v
  have e : M.toBlocks₁₂ *ᵥ v = fun i => (M *ᵥ Sum.elim (0 : Fin m → ℂ) v) (Sum.inl i) := by
    funext i; simp [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Matrix.toBlocks₁₂]
  rw [e]
  calc _ ≤ cn (M *ᵥ Sum.elim (0 : Fin m → ℂ) v) := cn_inl_le _
    _ ≤ c * cn (Sum.elim (0 : Fin m → ℂ) v) := h _
    _ = c * cn v := by rw [cn_elim_right]

private lemma OB_b21 {m n : ℕ} {M : CMat m n} {c : ℝ} (h : OB M c) : OB M.toBlocks₂₁ c := by
  intro v
  have e : M.toBlocks₂₁ *ᵥ v = fun i => (M *ᵥ Sum.elim v (0 : Fin n → ℂ)) (Sum.inr i) := by
    funext i; simp [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Matrix.toBlocks₂₁]
  rw [e]
  calc _ ≤ cn (M *ᵥ Sum.elim v (0 : Fin n → ℂ)) := cn_inr_le _
    _ ≤ c * cn (Sum.elim v (0 : Fin n → ℂ)) := h _
    _ = c * cn v := by rw [cn_elim_left]

private lemma OB_b22 {m n : ℕ} {M : CMat m n} {c : ℝ} (h : OB M c) : OB M.toBlocks₂₂ c := by
  intro v
  have e : M.toBlocks₂₂ *ᵥ v = fun i => (M *ᵥ Sum.elim (0 : Fin m → ℂ) v) (Sum.inr i) := by
    funext i; simp [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Matrix.toBlocks₂₂]
  rw [e]
  calc _ ≤ cn (M *ᵥ Sum.elim (0 : Fin m → ℂ) v) := cn_inr_le _
    _ ≤ c * cn (Sum.elim (0 : Fin m → ℂ) v) := h _
    _ = c * cn v := by rw [cn_elim_right]

/-- Frobenius norm from the operator bound, through the columns. -/
private lemma OB_fro {k l : ℕ} {L : Matrix (Fin k) (Fin l) ℂ} {c : ℝ} (hL : OB L c) :
    ∑ i, ∑ j, ‖L i j‖ ^ 2 ≤ (l : ℝ) * c ^ 2 := by
  rw [Finset.sum_comm]
  have hcol : ∀ j : Fin l, ∑ i, ‖L i j‖ ^ 2 ≤ c ^ 2 := by
    intro j
    have hv : cn (Pi.single j (1 : ℂ) : Fin l → ℂ) = 1 := by
      unfold cn
      have : ∀ x : Fin l, ‖(Pi.single j (1 : ℂ) : Fin l → ℂ) x‖ ^ 2 = if x = j then 1 else 0 := by
        intro x; by_cases h : x = j <;> simp [Pi.single_apply, h]
      simp only [this, Finset.sum_ite_eq', Finset.mem_univ, if_true, Real.sqrt_one]
    have h1 := hL (Pi.single j (1 : ℂ))
    rw [hv, mul_one] at h1
    have e : ∑ i, ‖L i j‖ ^ 2 = cn (L *ᵥ (Pi.single j (1 : ℂ) : Fin l → ℂ)) ^ 2 := by
      rw [cn_sq]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp [Matrix.mulVec, dotProduct, Pi.single_apply]
    rw [e]
    exact pow_le_pow_left₀ (cn_nonneg _) h1 2
  calc ∑ j, ∑ i, ‖L i j‖ ^ 2 ≤ ∑ _j : Fin l, c ^ 2 := Finset.sum_le_sum fun j _ => hcol j
    _ = (l : ℝ) * c ^ 2 := by simp


/-! ### The square roots of the covariances -/

private lemma vrp_rOut_symm {m n : ℕ} (C : Covariances m n) : (rOut C)ᵀ = rOut C := by
  have h : (CFC.sqrt C.Sout)ᴴ = CFC.sqrt C.Sout :=
    (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg C.Sout)).isHermitian
  rw [Matrix.conjTranspose_eq_transpose_of_trivial] at h
  exact h

private lemma vrp_rIn_symm {m n : ℕ} (C : Covariances m n) : (rIn C)ᵀ = rIn C := by
  have h : (CFC.sqrt C.Sin)ᴴ = CFC.sqrt C.Sin :=
    (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg C.Sin)).isHermitian
  rw [Matrix.conjTranspose_eq_transpose_of_trivial] at h
  exact h

private lemma vrp_rOut_mul {m n : ℕ} (C : Covariances m n) : rOut C * rOut C = C.Sout :=
  CFC.sqrt_mul_sqrt_self C.Sout (Matrix.nonneg_iff_posSemidef.mpr C.psdOut)

private lemma vrp_rIn_mul {m n : ℕ} (C : Covariances m n) : rIn C * rIn C = C.Sin :=
  CFC.sqrt_mul_sqrt_self C.Sin (Matrix.nonneg_iff_posSemidef.mpr C.psdIn)

private lemma vrp_opNorm_sq {k : ℕ} (A S : Mat k k) (hsym : Aᵀ = A) (hAA : A * A = S) :
    opNorm A ^ 2 = opNorm S := by
  open scoped Matrix.Norms.L2Operator in
  have h := Matrix.l2_opNorm_conjTranspose_mul_self A
  rw [Matrix.conjTranspose_eq_transpose_of_trivial, hsym, hAA] at h
  rw [opNorm_eq_norm, opNorm_eq_norm, h]; ring

private lemma vrp_rOut_opNorm {m n : ℕ} (C : Covariances m n) {CSig : ℝ} (h : opNorm C.Sout ≤ CSig) :
    opNorm (rOut C) ≤ Real.sqrt CSig := by
  have hsq := vrp_opNorm_sq (rOut C) C.Sout (vrp_rOut_symm C) (vrp_rOut_mul C)
  have h0 : 0 ≤ opNorm (rOut C) := by unfold opNorm; exact norm_nonneg _
  refine Real.le_sqrt_of_sq_le ?_
  rw [hsq]; exact h

private lemma vrp_rIn_opNorm {m n : ℕ} (C : Covariances m n) {CSig : ℝ} (h : opNorm C.Sin ≤ CSig) :
    opNorm (rIn C) ≤ Real.sqrt CSig := by
  have hsq := vrp_opNorm_sq (rIn C) C.Sin (vrp_rIn_symm C) (vrp_rIn_mul C)
  refine Real.le_sqrt_of_sq_le ?_
  rw [hsq]; exact h


private def compM {m n : ℕ} (M : CMat m n) (x : Vec m) (y : Vec n) : Matrix (Fin 2) (Fin 2) ℂ :=
  (Zc x y)ᵀ * (M * Zc x y)

private lemma compM_00 {m n : ℕ} (M : CMat m n) (x : Vec m) (y : Vec n) :
    compM M x y 0 0 = ∑ i, ∑ j, (x i : ℂ) * M.toBlocks₁₁ i j * (x j : ℂ) := by
  simp [compM, Matrix.mul_apply, Zc, Fintype.sum_sum_type, Matrix.toBlocks₁₁, Finset.mul_sum, Finset.sum_mul, mul_assoc]

private lemma compM_01 {m n : ℕ} (M : CMat m n) (x : Vec m) (y : Vec n) :
    compM M x y 0 1 = ∑ i, ∑ j, (x i : ℂ) * M.toBlocks₁₂ i j * (y j : ℂ) := by
  simp [compM, Matrix.mul_apply, Zc, Fintype.sum_sum_type, Matrix.toBlocks₁₂, Finset.mul_sum, Finset.sum_mul, mul_assoc]

private lemma compM_10 {m n : ℕ} (M : CMat m n) (x : Vec m) (y : Vec n) :
    compM M x y 1 0 = ∑ i, ∑ j, (y i : ℂ) * M.toBlocks₂₁ i j * (x j : ℂ) := by
  simp [compM, Matrix.mul_apply, Zc, Fintype.sum_sum_type, Matrix.toBlocks₂₁, Finset.mul_sum, Finset.sum_mul, mul_assoc]

private lemma compM_11 {m n : ℕ} (M : CMat m n) (x : Vec m) (y : Vec n) :
    compM M x y 1 1 = ∑ i, ∑ j, (y i : ℂ) * M.toBlocks₂₂ i j * (y j : ℂ) := by
  simp [compM, Matrix.mul_apply, Zc, Fintype.sum_sum_type, Matrix.toBlocks₂₂, Finset.mul_sum, Finset.sum_mul, mul_assoc]

/-- The mean compression `diag(B⁻¹ Tr Σ_out M_oo, B⁻¹ Tr Σ_in M_ii)`. -/
private def mmOf {m n : ℕ} (C : Covariances m n) (B : ℕ) (M : CMat m n) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(B : ℂ)⁻¹ * Matrix.trace (cOf C.Sout * M.toBlocks₁₁), 0;
     0, (B : ℂ)⁻¹ * Matrix.trace (cOf C.Sin * M.toBlocks₂₂)]


private lemma vrp_trace_conj {k : ℕ} (R S : Mat k k) (hsym : Rᵀ = R) (hRR : R * R = S)
    (L : Matrix (Fin k) (Fin k) ℂ) :
    Matrix.trace (cOf Rᵀ * L * cOf R) = Matrix.trace (cOf S * L) := by
  rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, ← cOf_mul, hsym, hRR]

private lemma vrp_quad_piece {k : ℕ} (R S : Mat k k) (hsym : Rᵀ = R) (hRR : R * R = S)
    (L : Matrix (Fin k) (Fin k) ℂ) (B : ℝ) (hB : 0 < B) :
    Integrable (fun z : Vec k => ‖∑ i, ∑ j, (((Real.sqrt B)⁻¹ • (R *ᵥ z)) i : ℂ) * L i j *
        (((Real.sqrt B)⁻¹ • (R *ᵥ z)) j : ℂ) - (B : ℂ)⁻¹ * Matrix.trace (cOf S * L)‖ ^ 2)
      (Muon.Foundations.stdGaussianPi k) ∧
    ∫ z : Vec k, ‖∑ i, ∑ j, (((Real.sqrt B)⁻¹ • (R *ᵥ z)) i : ℂ) * L i j *
        (((Real.sqrt B)⁻¹ • (R *ᵥ z)) j : ℂ) - (B : ℂ)⁻¹ * Matrix.trace (cOf S * L)‖ ^ 2
      ∂(Muon.Foundations.stdGaussianPi k) ≤
      (B ^ 2)⁻¹ * (2 * ∑ i, ∑ j, ‖(cOf Rᵀ * L * cOf R) i j‖ ^ 2) := by
  set Lt : Matrix (Fin k) (Fin k) ℂ := cOf Rᵀ * L * cOf R with hLt
  have hsq : ((Real.sqrt B)⁻¹ : ℝ) ^ 2 = B⁻¹ := by
    rw [inv_pow, Real.sq_sqrt hB.le]
  have hexp : ∀ z : Vec k, ∑ i, ∑ j, (((Real.sqrt B)⁻¹ • (R *ᵥ z)) i : ℂ) * L i j *
        (((Real.sqrt B)⁻¹ • (R *ᵥ z)) j : ℂ) - (B : ℂ)⁻¹ * Matrix.trace (cOf S * L) =
      (B : ℂ)⁻¹ * (∑ i, ∑ j, (z i : ℂ) * Lt i j * (z j : ℂ) - Matrix.trace Lt) := by
    intro z
    have h1 : ∀ i, (((Real.sqrt B)⁻¹ • (R *ᵥ z)) i : ℂ) = ((Real.sqrt B)⁻¹ : ℂ) * ((R *ᵥ z) i : ℂ) := by
      intro i; simp
    have h2 : ∑ i, ∑ j, (((Real.sqrt B)⁻¹ • (R *ᵥ z)) i : ℂ) * L i j * (((Real.sqrt B)⁻¹ • (R *ᵥ z)) j : ℂ) =
        (B : ℂ)⁻¹ * ∑ i, ∑ j, ((R *ᵥ z) i : ℂ) * L i j * ((R *ᵥ z) j : ℂ) := by
      simp only [h1, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      have : ((Real.sqrt B)⁻¹ : ℂ) * ((Real.sqrt B)⁻¹ : ℂ) = (B : ℂ)⁻¹ := by
        rw [← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt hB.le]
      calc ((Real.sqrt B)⁻¹ : ℂ) * ((R *ᵥ z) i : ℂ) * L i j * (((Real.sqrt B)⁻¹ : ℂ) * ((R *ᵥ z) j : ℂ))
          = (((Real.sqrt B)⁻¹ : ℂ) * ((Real.sqrt B)⁻¹ : ℂ)) * (((R *ᵥ z) i : ℂ) * L i j * ((R *ᵥ z) j : ℂ)) := by ring
        _ = _ := by rw [this]
    rw [h2, vrp_bil_conj R R L z z, hLt, vrp_trace_conj R S hsym hRR L]
    ring
  simp_rw [hexp]
  obtain ⟨hi, hv⟩ := vrp_G3a k Lt
  have hn : ∀ z : Vec k, ‖(B : ℂ)⁻¹ * (∑ i, ∑ j, (z i : ℂ) * Lt i j * (z j : ℂ) - Matrix.trace Lt)‖ ^ 2 =
      (B ^ 2)⁻¹ * ‖∑ i, ∑ j, (z i : ℂ) * Lt i j * (z j : ℂ) - Matrix.trace Lt‖ ^ 2 := by
    intro z
    have hnB : ‖((B : ℝ) : ℂ)⁻¹‖ = B⁻¹ := by
      rw [norm_inv, Complex.norm_real, Real.norm_of_nonneg hB.le]
    rw [norm_mul, mul_pow, hnB, inv_pow]
  simp_rw [hn]
  refine ⟨hi.const_mul _, ?_⟩
  rw [integral_const_mul]
  exact mul_le_mul_of_nonneg_left hv (by positivity)


private lemma vrp_bil_piece {k l : ℕ} (R : Mat k k) (R' : Mat l l) (N : Matrix (Fin k) (Fin l) ℂ)
    (B : ℝ) (hB : 0 < B) :
    Integrable (fun p : Vec k × Vec l => ‖∑ i, ∑ j, (((Real.sqrt B)⁻¹ • (R *ᵥ p.1)) i : ℂ) * N i j *
        (((Real.sqrt B)⁻¹ • (R' *ᵥ p.2)) j : ℂ)‖ ^ 2) (gaussPair k l) ∧
    ∫ p : Vec k × Vec l, ‖∑ i, ∑ j, (((Real.sqrt B)⁻¹ • (R *ᵥ p.1)) i : ℂ) * N i j *
        (((Real.sqrt B)⁻¹ • (R' *ᵥ p.2)) j : ℂ)‖ ^ 2 ∂(gaussPair k l) =
      (B ^ 2)⁻¹ * ∑ i, ∑ j, ‖(cOf Rᵀ * N * cOf R') i j‖ ^ 2 := by
  set Nt : Matrix (Fin k) (Fin l) ℂ := cOf Rᵀ * N * cOf R' with hNt
  have hexp : ∀ p : Vec k × Vec l, ∑ i, ∑ j, (((Real.sqrt B)⁻¹ • (R *ᵥ p.1)) i : ℂ) * N i j *
        (((Real.sqrt B)⁻¹ • (R' *ᵥ p.2)) j : ℂ) =
      (B : ℂ)⁻¹ * ∑ i, ∑ j, (p.1 i : ℂ) * Nt i j * (p.2 j : ℂ) := by
    intro p
    have h1 : ∀ i, (((Real.sqrt B)⁻¹ • (R *ᵥ p.1)) i : ℂ) = ((Real.sqrt B)⁻¹ : ℂ) * ((R *ᵥ p.1) i : ℂ) := by
      intro i; simp
    have h1' : ∀ i, (((Real.sqrt B)⁻¹ • (R' *ᵥ p.2)) i : ℂ) = ((Real.sqrt B)⁻¹ : ℂ) * ((R' *ᵥ p.2) i : ℂ) := by
      intro i; simp
    have h2 : ∑ i, ∑ j, (((Real.sqrt B)⁻¹ • (R *ᵥ p.1)) i : ℂ) * N i j * (((Real.sqrt B)⁻¹ • (R' *ᵥ p.2)) j : ℂ) =
        (B : ℂ)⁻¹ * ∑ i, ∑ j, ((R *ᵥ p.1) i : ℂ) * N i j * ((R' *ᵥ p.2) j : ℂ) := by
      simp only [h1, h1', Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      have : ((Real.sqrt B)⁻¹ : ℂ) * ((Real.sqrt B)⁻¹ : ℂ) = (B : ℂ)⁻¹ := by
        rw [← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt hB.le]
      calc ((Real.sqrt B)⁻¹ : ℂ) * ((R *ᵥ p.1) i : ℂ) * N i j * (((Real.sqrt B)⁻¹ : ℂ) * ((R' *ᵥ p.2) j : ℂ))
          = (((Real.sqrt B)⁻¹ : ℂ) * ((Real.sqrt B)⁻¹ : ℂ)) * (((R *ᵥ p.1) i : ℂ) * N i j * ((R' *ᵥ p.2) j : ℂ)) := by ring
        _ = _ := by rw [this]
    rw [h2, vrp_bil_conj R R' N p.1 p.2]
  simp_rw [hexp]
  obtain ⟨hi, hv⟩ := vrp_G3b k l Nt
  have hnB : ‖((B : ℝ) : ℂ)⁻¹‖ = B⁻¹ := by
    rw [norm_inv, Complex.norm_real, Real.norm_of_nonneg hB.le]
  have hn : ∀ p : Vec k × Vec l, ‖(B : ℂ)⁻¹ * ∑ i, ∑ j, (p.1 i : ℂ) * Nt i j * (p.2 j : ℂ)‖ ^ 2 =
      (B ^ 2)⁻¹ * ‖∑ i, ∑ j, (p.1 i : ℂ) * Nt i j * (p.2 j : ℂ)‖ ^ 2 := by
    intro p
    rw [norm_mul, mul_pow, hnB, inv_pow]
  simp_rw [hn]
  refine ⟨hi.const_mul _, ?_⟩
  rw [integral_const_mul, hv]

private lemma vrp_int_fst {m n : ℕ} (f : Vec m → ℝ) (hf : AEStronglyMeasurable f (Muon.Foundations.stdGaussianPi m)) :
    (Integrable (fun p : Vec m × Vec n => f p.1) (gaussPair m n) ↔
      Integrable f (Muon.Foundations.stdGaussianPi m)) ∧
    ∫ p : Vec m × Vec n, f p.1 ∂(gaussPair m n) = ∫ z, f z ∂(Muon.Foundations.stdGaussianPi m) := by
  have hmp : MeasurePreserving (Prod.fst : Vec m × Vec n → Vec m) (gaussPair m n)
      (Muon.Foundations.stdGaussianPi m) := measurePreserving_fst
  refine ⟨hmp.integrable_comp hf, ?_⟩
  rw [← hmp.map_eq, integral_map measurable_fst.aemeasurable (by rw [hmp.map_eq]; exact hf)]

private lemma vrp_int_snd {m n : ℕ} (f : Vec n → ℝ) (hf : AEStronglyMeasurable f (Muon.Foundations.stdGaussianPi n)) :
    (Integrable (fun p : Vec m × Vec n => f p.2) (gaussPair m n) ↔
      Integrable f (Muon.Foundations.stdGaussianPi n)) ∧
    ∫ p : Vec m × Vec n, f p.2 ∂(gaussPair m n) = ∫ z, f z ∂(Muon.Foundations.stdGaussianPi n) := by
  have hmp : MeasurePreserving (Prod.snd : Vec m × Vec n → Vec n) (gaussPair m n)
      (Muon.Foundations.stdGaussianPi n) := measurePreserving_snd
  refine ⟨hmp.integrable_comp hf, ?_⟩
  rw [← hmp.map_eq, integral_map measurable_snd.aemeasurable (by rw [hmp.map_eq]; exact hf)]


private lemma OB_conj {a b : ℕ} {R : Matrix (Fin a) (Fin a) ℝ} {R' : Matrix (Fin b) (Fin b) ℝ}
    {L : Matrix (Fin a) (Fin b) ℂ} {s c : ℝ} (hs : 0 ≤ s) (hc : 0 ≤ c)
    (hR : opNorm Rᵀ ≤ s) (hR' : opNorm R' ≤ s) (hL : OB L c) :
    OB (cOf Rᵀ * L * cOf R') (s * c * s) := by
  have h1 := OB_real _ hR
  have h2 := OB_real _ hR'
  have := OB_mul hs h1 (OB_mul hc hL h2 : OB (L * cOf R') (c * s))
  rw [← Matrix.mul_assoc] at this
  have e : s * (c * s) = s * c * s := by ring
  rwa [e] at this

private lemma vrp_integral_sum4 {α : Type*} [MeasurableSpace α] {μ : Measure α} (f1 f2 f3 f4 : α → ℝ)
    (h1 : Integrable f1 μ) (h2 : Integrable f2 μ) (h3 : Integrable f3 μ) (h4 : Integrable f4 μ) :
    ∫ x, (f1 x + f2 x + f3 x + f4 x) ∂μ = ∫ x, f1 x ∂μ + ∫ x, f2 x ∂μ + ∫ x, f3 x ∂μ + ∫ x, f4 x ∂μ := by
  have e1 : Integrable (fun x => f1 x + f2 x) μ := h1.add h2
  have e2 : Integrable (fun x => f1 x + f2 x + f3 x) μ := e1.add h3
  rw [integral_add e2 h4, integral_add e1 h3, integral_add h1 h2]

private def Dm {m n : ℕ} (C : Covariances m n) (B : ℕ) (M : CMat m n) (p : Vec m × Vec n) :
    Matrix (Fin 2) (Fin 2) ℂ := compM M (momU C B p) (momV C B p) - mmOf C B M

private lemma vrp_ent00 {m n : ℕ} (C : Covariances m n) (B : ℕ) (hB : 0 < B) (CSig c : ℝ)
    (hc : 0 ≤ c) (hCo : opNorm C.Sout ≤ CSig) (M : CMat m n) (hM : OB M c) :
    Integrable (fun p : Vec m × Vec n => ‖Dm C B M p 0 0‖ ^ 2) (gaussPair m n) ∧
    ∫ p : Vec m × Vec n, ‖Dm C B M p 0 0‖ ^ 2 ∂(gaussPair m n) ≤
      (B ^ 2 : ℝ)⁻¹ * (2 * ((m : ℝ) * (CSig * c) ^ 2)) := by
  have hBr : (0 : ℝ) < B := by exact_mod_cast hB
  have hC0 : 0 ≤ CSig := le_trans (by unfold opNorm; exact norm_nonneg _) hCo
  have hs0 : 0 ≤ Real.sqrt CSig := Real.sqrt_nonneg _
  have hRo : opNorm (rOut C)ᵀ ≤ Real.sqrt CSig := by rw [vrp_rOut_symm]; exact vrp_rOut_opNorm C hCo
  have hRo' : opNorm (rOut C) ≤ Real.sqrt CSig := vrp_rOut_opNorm C hCo
  have hss : Real.sqrt CSig * c * Real.sqrt CSig = CSig * c := by
    have := Real.mul_self_sqrt hC0; nlinarith
  have q00 := vrp_quad_piece (rOut C) C.Sout (vrp_rOut_symm C) (vrp_rOut_mul C) M.toBlocks₁₁ (B : ℝ) hBr
  have F00 : ∑ i, ∑ j, ‖(cOf (rOut C)ᵀ * M.toBlocks₁₁ * cOf (rOut C)) i j‖ ^ 2 ≤ (m : ℝ) * (CSig * c) ^ 2 := by
    have := OB_fro (OB_conj hs0 hc hRo hRo' (OB_b11 hM))
    rwa [hss] at this
  have eq00 : ∀ p : Vec m × Vec n, ‖Dm C B M p 0 0‖ ^ 2 = (fun z : Vec m => ‖∑ i, ∑ j, (((Real.sqrt (B : ℝ))⁻¹ • (rOut C *ᵥ z)) i : ℂ) * M.toBlocks₁₁ i j *
        (((Real.sqrt (B : ℝ))⁻¹ • (rOut C *ᵥ z)) j : ℂ) - ((B : ℝ) : ℂ)⁻¹ * Matrix.trace (cOf C.Sout * M.toBlocks₁₁)‖ ^ 2) p.1 := by
    intro p
    simp only [Dm, Matrix.sub_apply, compM_00, mmOf, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, Complex.ofReal_natCast, momU]
  have i00 := (vrp_int_fst (n := n) _ q00.1.aestronglyMeasurable)
  refine ⟨?_, ?_⟩
  · simp_rw [eq00]; exact i00.1.2 q00.1
  · simp_rw [eq00]; rw [i00.2]
    exact q00.2.trans (mul_le_mul_of_nonneg_left (by linarith) (by positivity))

private lemma vrp_ent11 {m n : ℕ} (C : Covariances m n) (B : ℕ) (hB : 0 < B) (CSig c : ℝ)
    (hc : 0 ≤ c) (hCi : opNorm C.Sin ≤ CSig) (M : CMat m n) (hM : OB M c) :
    Integrable (fun p : Vec m × Vec n => ‖Dm C B M p 1 1‖ ^ 2) (gaussPair m n) ∧
    ∫ p : Vec m × Vec n, ‖Dm C B M p 1 1‖ ^ 2 ∂(gaussPair m n) ≤
      (B ^ 2 : ℝ)⁻¹ * (2 * ((n : ℝ) * (CSig * c) ^ 2)) := by
  have hBr : (0 : ℝ) < B := by exact_mod_cast hB
  have hC0 : 0 ≤ CSig := le_trans (by unfold opNorm; exact norm_nonneg _) hCi
  have hs0 : 0 ≤ Real.sqrt CSig := Real.sqrt_nonneg _
  have hRi : opNorm (rIn C)ᵀ ≤ Real.sqrt CSig := by rw [vrp_rIn_symm]; exact vrp_rIn_opNorm C hCi
  have hRi' : opNorm (rIn C) ≤ Real.sqrt CSig := vrp_rIn_opNorm C hCi
  have hss : Real.sqrt CSig * c * Real.sqrt CSig = CSig * c := by
    have := Real.mul_self_sqrt hC0; nlinarith
  have q11 := vrp_quad_piece (rIn C) C.Sin (vrp_rIn_symm C) (vrp_rIn_mul C) M.toBlocks₂₂ (B : ℝ) hBr
  have F11 : ∑ i, ∑ j, ‖(cOf (rIn C)ᵀ * M.toBlocks₂₂ * cOf (rIn C)) i j‖ ^ 2 ≤ (n : ℝ) * (CSig * c) ^ 2 := by
    have := OB_fro (OB_conj hs0 hc hRi hRi' (OB_b22 hM))
    rwa [hss] at this
  have eq11 : ∀ p : Vec m × Vec n, ‖Dm C B M p 1 1‖ ^ 2 = (fun z : Vec n => ‖∑ i, ∑ j, (((Real.sqrt (B : ℝ))⁻¹ • (rIn C *ᵥ z)) i : ℂ) * M.toBlocks₂₂ i j *
        (((Real.sqrt (B : ℝ))⁻¹ • (rIn C *ᵥ z)) j : ℂ) - ((B : ℝ) : ℂ)⁻¹ * Matrix.trace (cOf C.Sin * M.toBlocks₂₂)‖ ^ 2) p.2 := by
    intro p
    simp only [Dm, Matrix.sub_apply, compM_11, mmOf, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, Complex.ofReal_natCast, momV]
  have i11 := (vrp_int_snd (m := m) _ q11.1.aestronglyMeasurable)
  refine ⟨?_, ?_⟩
  · simp_rw [eq11]; exact i11.1.2 q11.1
  · simp_rw [eq11]; rw [i11.2]
    exact q11.2.trans (mul_le_mul_of_nonneg_left (by linarith) (by positivity))

private lemma vrp_ent01 {m n : ℕ} (C : Covariances m n) (B : ℕ) (hB : 0 < B) (CSig c : ℝ)
    (hc : 0 ≤ c) (hCo : opNorm C.Sout ≤ CSig) (hCi : opNorm C.Sin ≤ CSig) (M : CMat m n) (hM : OB M c) :
    Integrable (fun p : Vec m × Vec n => ‖Dm C B M p 0 1‖ ^ 2) (gaussPair m n) ∧
    ∫ p : Vec m × Vec n, ‖Dm C B M p 0 1‖ ^ 2 ∂(gaussPair m n) ≤
      (B ^ 2 : ℝ)⁻¹ * ((n : ℝ) * (CSig * c) ^ 2) := by
  have hBr : (0 : ℝ) < B := by exact_mod_cast hB
  have hC0 : 0 ≤ CSig := le_trans (by unfold opNorm; exact norm_nonneg _) hCo
  have hs0 : 0 ≤ Real.sqrt CSig := Real.sqrt_nonneg _
  have hRo : opNorm (rOut C)ᵀ ≤ Real.sqrt CSig := by rw [vrp_rOut_symm]; exact vrp_rOut_opNorm C hCo
  have hRi' : opNorm (rIn C) ≤ Real.sqrt CSig := vrp_rIn_opNorm C hCi
  have hss : Real.sqrt CSig * c * Real.sqrt CSig = CSig * c := by
    have := Real.mul_self_sqrt hC0; nlinarith
  have b01 := vrp_bil_piece (rOut C) (rIn C) M.toBlocks₁₂ (B : ℝ) hBr
  have F01 : ∑ i, ∑ j, ‖(cOf (rOut C)ᵀ * M.toBlocks₁₂ * cOf (rIn C)) i j‖ ^ 2 ≤ (n : ℝ) * (CSig * c) ^ 2 := by
    have := OB_fro (OB_conj hs0 hc hRo hRi' (OB_b12 hM))
    rwa [hss] at this
  have eq01 : ∀ p : Vec m × Vec n, ‖Dm C B M p 0 1‖ ^ 2 = (fun q : Vec m × Vec n => ‖∑ i, ∑ j, (((Real.sqrt (B : ℝ))⁻¹ • (rOut C *ᵥ q.1)) i : ℂ) * M.toBlocks₁₂ i j *
        (((Real.sqrt (B : ℝ))⁻¹ • (rIn C *ᵥ q.2)) j : ℂ)‖ ^ 2) p := by
    intro p
    simp only [Dm, Matrix.sub_apply, compM_01, mmOf, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, sub_zero, momU, momV]
  refine ⟨?_, ?_⟩
  · simp_rw [eq01]; exact b01.1
  · simp_rw [eq01]; rw [b01.2]
    exact mul_le_mul_of_nonneg_left F01 (by positivity)

private lemma vrp_ent10 {m n : ℕ} (C : Covariances m n) (B : ℕ) (hB : 0 < B) (CSig c : ℝ)
    (hc : 0 ≤ c) (hCo : opNorm C.Sout ≤ CSig) (hCi : opNorm C.Sin ≤ CSig) (M : CMat m n) (hM : OB M c) :
    Integrable (fun p : Vec m × Vec n => ‖Dm C B M p 1 0‖ ^ 2) (gaussPair m n) ∧
    ∫ p : Vec m × Vec n, ‖Dm C B M p 1 0‖ ^ 2 ∂(gaussPair m n) ≤
      (B ^ 2 : ℝ)⁻¹ * ((m : ℝ) * (CSig * c) ^ 2) := by
  have hBr : (0 : ℝ) < B := by exact_mod_cast hB
  have hC0 : 0 ≤ CSig := le_trans (by unfold opNorm; exact norm_nonneg _) hCo
  have hs0 : 0 ≤ Real.sqrt CSig := Real.sqrt_nonneg _
  have hRi : opNorm (rIn C)ᵀ ≤ Real.sqrt CSig := by rw [vrp_rIn_symm]; exact vrp_rIn_opNorm C hCi
  have hRo' : opNorm (rOut C) ≤ Real.sqrt CSig := vrp_rOut_opNorm C hCo
  have hss : Real.sqrt CSig * c * Real.sqrt CSig = CSig * c := by
    have := Real.mul_self_sqrt hC0; nlinarith
  have b10 := vrp_bil_piece (rOut C) (rIn C) M.toBlocks₂₁ᵀ (B : ℝ) hBr
  have F10 : ∑ i, ∑ j, ‖(cOf (rOut C)ᵀ * M.toBlocks₂₁ᵀ * cOf (rIn C)) i j‖ ^ 2 ≤ (m : ℝ) * (CSig * c) ^ 2 := by
    have := OB_fro (OB_conj hs0 hc hRi hRo' (OB_b21 hM))
    rw [hss] at this
    have et : (cOf (rOut C)ᵀ * M.toBlocks₂₁ᵀ * cOf (rIn C))ᵀ = cOf (rIn C)ᵀ * M.toBlocks₂₁ * cOf (rOut C) := by
      rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose]
      have h1 : (cOf (rIn C))ᵀ = cOf (rIn C)ᵀ := by ext i j; simp
      have h2 : (cOf (rOut C)ᵀ)ᵀ = cOf (rOut C) := by ext i j; simp
      rw [h1, h2, Matrix.mul_assoc]
    have e : ∑ i, ∑ j, ‖(cOf (rOut C)ᵀ * M.toBlocks₂₁ᵀ * cOf (rIn C)) i j‖ ^ 2 =
        ∑ i, ∑ j, ‖(cOf (rIn C)ᵀ * M.toBlocks₂₁ * cOf (rOut C)) i j‖ ^ 2 := by
      rw [← et, Finset.sum_comm]
      simp [Matrix.transpose_apply]
    rw [e]; exact this
  have eq10 : ∀ p : Vec m × Vec n, ‖Dm C B M p 1 0‖ ^ 2 = (fun q : Vec m × Vec n => ‖∑ i, ∑ j, (((Real.sqrt (B : ℝ))⁻¹ • (rOut C *ᵥ q.1)) i : ℂ) * M.toBlocks₂₁ᵀ i j *
        (((Real.sqrt (B : ℝ))⁻¹ • (rIn C *ᵥ q.2)) j : ℂ)‖ ^ 2) p := by
    intro p
    simp only [Dm, Matrix.sub_apply, compM_10, mmOf, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, sub_zero, momU, momV]
    congr 2
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    simp only [Matrix.transpose_apply]
    ring
  refine ⟨?_, ?_⟩
  · simp_rw [eq10]; exact b10.1
  · simp_rw [eq10]; rw [b10.2]
    exact mul_le_mul_of_nonneg_left F10 (by positivity)

private lemma n2_cont {X : Type*} [TopologicalSpace X] {f : X → Matrix (Fin 2) (Fin 2) ℂ}
    (hf : Continuous f) : Continuous (fun x => n2 (f x)) := by
  unfold n2
  have e := fun (i j : Fin 2) => ((continuous_apply j).comp ((continuous_apply i).comp hf))
  exact ((((e 0 0).norm.add (e 0 1).norm).add (e 1 0).norm).add (e 1 1).norm)

private lemma Dm_cont {m n : ℕ} (C : Covariances m n) (B : ℕ) (M : CMat m n) :
    Continuous (Dm C B M) := by
  have hXc : Continuous (fun p : Vec m × Vec n => momU C B p) := by
    simp only [momU]; fun_prop
  have hYc : Continuous (fun p : Vec m × Vec n => momV C B p) := by
    simp only [momV]; fun_prop
  have hZ : Continuous (fun p : Vec m × Vec n => Zc (momU C B p) (momV C B p)) := by
    refine continuous_pi fun a => continuous_pi fun k => ?_
    rcases a with i | j
    · simp only [Zc, Matrix.of_apply, Sum.elim_inl]
      split_ifs
      · exact Complex.continuous_ofReal.comp ((continuous_apply i).comp hXc)
      · exact continuous_const
    · simp only [Zc, Matrix.of_apply, Sum.elim_inr]
      split_ifs
      · exact Complex.continuous_ofReal.comp ((continuous_apply j).comp hYc)
      · exact continuous_const
  unfold Dm compM
  exact ((hZ.matrix_transpose).matrix_mul (continuous_const.matrix_mul hZ)).sub continuous_const

private lemma vrp_compress {m n : ℕ} (C : Covariances m n) (B : ℕ) (hB : 0 < B) (γ CSig : ℝ)
    (hγ : 0 ≤ γ) (hm : (m : ℝ) ≤ γ * B) (hn : (n : ℝ) ≤ γ * B)
    (hCo : opNorm C.Sout ≤ CSig) (hCi : opNorm C.Sin ≤ CSig)
    (M : CMat m n) (c : ℝ) (hc : 0 ≤ c) (hM : OB M c) :
    Integrable (fun p : Vec m × Vec n => n2 (Dm C B M p) ^ 2) (gaussPair m n) ∧
    ∫ p : Vec m × Vec n, n2 (Dm C B M p) ^ 2 ∂(gaussPair m n) ≤ 24 * γ * CSig ^ 2 * c ^ 2 / B := by
  have hBr : (0 : ℝ) < B := by exact_mod_cast hB
  obtain ⟨I00, J00⟩ := vrp_ent00 C B hB CSig c hc hCo M hM
  obtain ⟨I11, J11⟩ := vrp_ent11 C B hB CSig c hc hCi M hM
  obtain ⟨I01, J01⟩ := vrp_ent01 C B hB CSig c hc hCo hCi M hM
  obtain ⟨I10, J10⟩ := vrp_ent10 C B hB CSig c hc hCo hCi M hM
  have hn2c : Continuous (fun p => n2 (Dm C B M p)) := n2_cont (Dm_cont C B M)
  have hpt : ∀ p, n2 (Dm C B M p) ^ 2 ≤ 4 * (‖Dm C B M p 0 0‖ ^ 2 + ‖Dm C B M p 0 1‖ ^ 2 +
      ‖Dm C B M p 1 0‖ ^ 2 + ‖Dm C B M p 1 1‖ ^ 2) := by
    intro p
    unfold n2
    nlinarith [sq_nonneg (‖Dm C B M p 0 0‖ - ‖Dm C B M p 0 1‖), sq_nonneg (‖Dm C B M p 0 0‖ - ‖Dm C B M p 1 0‖),
      sq_nonneg (‖Dm C B M p 0 0‖ - ‖Dm C B M p 1 1‖), sq_nonneg (‖Dm C B M p 0 1‖ - ‖Dm C B M p 1 0‖),
      sq_nonneg (‖Dm C B M p 0 1‖ - ‖Dm C B M p 1 1‖), sq_nonneg (‖Dm C B M p 1 0‖ - ‖Dm C B M p 1 1‖)]
  have hsum : Integrable (fun p : Vec m × Vec n => 4 * (‖Dm C B M p 0 0‖ ^ 2 + ‖Dm C B M p 0 1‖ ^ 2 +
      ‖Dm C B M p 1 0‖ ^ 2 + ‖Dm C B M p 1 1‖ ^ 2)) (gaussPair m n) :=
    (((I00.add I01).add I10).add I11).const_mul 4
  have hInt : Integrable (fun p : Vec m × Vec n => n2 (Dm C B M p) ^ 2) (gaussPair m n) := by
    refine hsum.mono' ((hn2c.pow 2).aestronglyMeasurable) (Filter.Eventually.of_forall fun p => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact hpt p
  refine ⟨hInt, ?_⟩
  have h1 : ∫ p : Vec m × Vec n, n2 (Dm C B M p) ^ 2 ∂(gaussPair m n) ≤
      ∫ p : Vec m × Vec n, 4 * (‖Dm C B M p 0 0‖ ^ 2 + ‖Dm C B M p 0 1‖ ^ 2 + ‖Dm C B M p 1 0‖ ^ 2 +
        ‖Dm C B M p 1 1‖ ^ 2) ∂(gaussPair m n) :=
    integral_mono hInt hsum hpt
  rw [integral_const_mul, vrp_integral_sum4 _ _ _ _ I00 I01 I10 I11] at h1
  have hB2 : (0 : ℝ) < B ^ 2 := by positivity
  have hmn : (m : ℝ) + n ≤ 2 * γ * B := by linarith
  calc ∫ p : Vec m × Vec n, n2 (Dm C B M p) ^ 2 ∂(gaussPair m n)
      ≤ 4 * (∫ p, ‖Dm C B M p 0 0‖ ^ 2 ∂(gaussPair m n) + ∫ p, ‖Dm C B M p 0 1‖ ^ 2 ∂(gaussPair m n) +
        ∫ p, ‖Dm C B M p 1 0‖ ^ 2 ∂(gaussPair m n) + ∫ p, ‖Dm C B M p 1 1‖ ^ 2 ∂(gaussPair m n)) := h1
    _ ≤ 4 * ((B ^ 2 : ℝ)⁻¹ * (2 * ((m : ℝ) * (CSig * c) ^ 2)) + (B ^ 2 : ℝ)⁻¹ * ((n : ℝ) * (CSig * c) ^ 2) +
        (B ^ 2 : ℝ)⁻¹ * ((m : ℝ) * (CSig * c) ^ 2) + (B ^ 2 : ℝ)⁻¹ * (2 * ((n : ℝ) * (CSig * c) ^ 2))) := by
        gcongr
    _ = 12 * ((m : ℝ) + n) * (CSig * c) ^ 2 / (B : ℝ) ^ 2 := by
        field_simp; ring
    _ ≤ 24 * γ * CSig ^ 2 * c ^ 2 / B := by
        rw [div_le_div_iff₀ (by positivity) hBr]
        nlinarith [sq_nonneg (CSig * c), mul_nonneg (sq_nonneg (CSig * c)) (Nat.cast_nonneg (α := ℝ) B)]

private lemma vrp_scalar_weak {Θ : Type*} [MetricSpace Θ] [CompactSpace Θ]
    {Ω : ℕ → Type} [∀ k, MeasurableSpace (Ω k)]
    {m n : ℕ → ℕ} (A : ∀ k, Mat (m k) (n k)) (hA : ∀ k, fro (A k) = 1)
    (hAn : Tendsto (fun k => opNorm (A k)) atTop (𝓝 0))
    (P : ∀ k, Measure (Ω k)) [∀ k, IsProbabilityMeasure (P k)]
    (z : ∀ k, Ω k → Vec (m k)) (w : ∀ k, Ω k → Vec (n k))
    (hlaw : ∀ k, (P k).map (fun ω => (z k ω, w k ω)) = gaussPair (m k) (n k))
    (ψ : Θ → ℝ → ℂ) (hψ : Continuous fun p : Θ × ℝ => ψ p.1 p.2)
    (Cψ : ℝ) (hψb : ∀ θ x, ‖ψ θ x‖ ≤ Cψ * (1 + |x|) ^ 4) :
    ∀ ε > 0, ∀ᶠ k in atTop, ∀ θ : Θ,
      ‖(∫ ω, ψ θ (resid (A k) (z k ω, w k ω)) ∂(P k)) -
        ∫ x, ψ θ x ∂(gaussianReal 0 1)‖ ≤ ε := by
  intro ε hε
  set C : ℝ := |Cψ| with hCdef
  have hC : 0 ≤ C := abs_nonneg _
  have hb : ∀ θ x, ‖ψ θ x‖ ≤ C * (1 + |x|) ^ 4 := fun θ x =>
    (hψb θ x).trans (mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity))
  have hcont : ∀ θ, Continuous (ψ θ) := fun θ => hψ.comp (continuous_const.prodMk continuous_id)
  have hIγ : Integrable (fun x : ℝ => (1 + |x|) ^ 6) (gaussianReal 0 1) := by
    refine ((integrable_const (1 : ℝ)).add (Muon.Foundations.gaussian_integrable_pow 6)).const_mul 32
      |>.mono' (by fun_prop : Measurable fun x : ℝ => (1 + |x|) ^ 6).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have := vsw_one_add_pow6 |x| (abs_nonneg _)
    rwa [show |x| ^ 6 = x ^ 6 from (Even.pow_abs ⟨3, rfl⟩ _)] at this
  set Kg : ℝ := ∫ x, (1 + |x|) ^ 6 ∂(gaussianReal 0 1) with hKg
  have hKg0 : 0 ≤ Kg := integral_nonneg fun x => by positivity
  set B : ℝ := 2 * C * (7232 + Kg) with hB
  have hB0 : 0 ≤ B := by positivity
  obtain ⟨M, hM0, hMB⟩ : ∃ M : ℝ, 0 ≤ M ∧ B / (1 + M) ^ 2 ≤ ε / 5 := by
    refine ⟨5 * B / ε, by positivity, ?_⟩
    set M : ℝ := 5 * B / ε
    have hM0 : 0 ≤ M := by positivity
    calc B / (1 + M) ^ 2 ≤ B / (1 + M) :=
          div_le_div_of_nonneg_left hB0 (by positivity) (by nlinarith)
      _ ≤ ε / 5 := by
          rw [div_le_iff₀ (by positivity)]
          have : ε / 5 * M = B := by simp only [M]; field_simp
          nlinarith
  have hp : 0 < (1 + M) ^ 2 := by positivity
  have hT1 : 2 * C * 7232 / (1 + M) ^ 2 ≤ ε / 5 :=
    (div_le_div_of_nonneg_right (by nlinarith) hp.le).trans hMB
  have hT2 : 2 * C * Kg / (1 + M) ^ 2 ≤ ε / 5 :=
    (div_le_div_of_nonneg_right (by nlinarith) hp.le).trans hMB
  obtain ⟨S, hS⟩ := net_window ψ hψ M (ε / 5) (by positivity)
  have hev : ∀ᶠ k in atTop, ∀ θ' ∈ S,
      ‖(∫ ω, ψ θ' (max (-M) (min M (resid (A k) (z k ω, w k ω)))) ∂(P k)) -
        ∫ x, ψ θ' (max (-M) (min M x)) ∂(gaussianReal 0 1)‖ ≤ ε / 5 := by
    refine (Filter.eventually_all_finset S).2 fun θ' _ => ?_
    refine vsw_conv P A z w hlaw hA hAn
      (fun x => ψ θ' (max (-M) (min M x))) (by have := hcont θ'; fun_prop) (C * (1 + M) ^ 4)
      (fun x => ?_) (ε / 5) (by positivity)
    have := vsw_clamp_abs M x hM0
    exact (hb θ' _).trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by positivity) (by linarith [this.1]) 4) hC)
  filter_upwards [hev] with k hk θ
  obtain ⟨hD, hI, hK⟩ := vsw_sample (A k) (hA k) (P k) (z k) (w k) (hlaw k)
  obtain ⟨θ', hθ'S, hθ'⟩ := hS θ
  have hclθ : ∀ x, ‖ψ θ (max (-M) (min M x)) - ψ θ' (max (-M) (min M x))‖ ≤ ε / 5 :=
    fun x => hθ' _ (vsw_clamp_abs M x hM0).1
  have t1 := vsw_tail_int (P k) _ hD hI 7232 hK (ψ θ) (hcont θ) C hC (hb θ) M hM0
  have t5 := vsw_tail_int (gaussianReal 0 1) (fun x => x) aemeasurable_id hIγ Kg le_rfl
    (ψ θ) (hcont θ) C hC (hb θ) M hM0
  have t2 := vsw_net_int (P k) _ hD hI (fun x => ψ θ (max (-M) (min M x)))
    (fun x => ψ θ' (max (-M) (min M x))) (by have := hcont θ; fun_prop)
    (by have := hcont θ'; fun_prop) C
    (vsw_clamp_bd (ψ θ) C hC (hb θ) M hM0) (vsw_clamp_bd (ψ θ') C hC (hb θ') M hM0) (ε / 5) hclθ
  have t4 := vsw_net_int (gaussianReal 0 1) (fun x => x) aemeasurable_id hIγ
    (fun x => ψ θ' (max (-M) (min M x))) (fun x => ψ θ (max (-M) (min M x)))
    (by have := hcont θ'; fun_prop) (by have := hcont θ; fun_prop) C
    (vsw_clamp_bd (ψ θ') C hC (hb θ') M hM0) (vsw_clamp_bd (ψ θ) C hC (hb θ) M hM0) (ε / 5)
    (fun x => by rw [norm_sub_rev]; exact hclθ x)
  have t3 := hk θ' hθ'S
  set a := ∫ ω, ψ θ (resid (A k) (z k ω, w k ω)) ∂(P k)
  set a' := ∫ ω, ψ θ (max (-M) (min M (resid (A k) (z k ω, w k ω)))) ∂(P k)
  set a'' := ∫ ω, ψ θ' (max (-M) (min M (resid (A k) (z k ω, w k ω)))) ∂(P k)
  set b := ∫ x, ψ θ x ∂(gaussianReal 0 1)
  set b' := ∫ x, ψ θ (max (-M) (min M x)) ∂(gaussianReal 0 1)
  set b'' := ∫ x, ψ θ' (max (-M) (min M x)) ∂(gaussianReal 0 1)
  have e : a - b = (a - a') + (a' - a'') + (a'' - b'') + (b'' - b') + (b' - b) := by ring
  rw [e]
  have := norm_add_le ((a - a') + (a' - a'') + (a'' - b'') + (b'' - b')) (b' - b)
  have := norm_add_le ((a - a') + (a' - a'') + (a'' - b'')) (b'' - b')
  have := norm_add_le ((a - a') + (a' - a'')) (a'' - b'')
  have := norm_add_le (a - a') (a' - a'')
  rw [norm_sub_rev b' b] at *
  linarith


/-! ### The parameter space and the scalar function `ψ` -/

-- The explicit normalized bar matrix entries.
private def csA (mm rho e chiO chiI : ℝ) : ℝ := rho * e / (1 + (mm * rho * e) * (mm * rho * e) * chiO * chiI)

-- `ψ(θ, e) = Φ̄ / m`, with the parameter vector
-- `θ = (m, ϱ, ϱ', χ_o, χ_i, χ_o', χ_i', A_o, A_i, B_o, B_i, E_o, E_i, T_o, T_i)`.
private def psiF (θ : Fin 15 → ℂ) (e : ℝ) : ℂ :=
  let mm := (θ 0).re
  let rho := (θ 1).re
  let rho' := (θ 2).re
  let co := (θ 3).re
  let ci := (θ 4).re
  let co' := (θ 5).re
  let ci' := (θ 6).re
  let c := mm * rho * e
  let c' := mm * rho' * e
  let a := csA mm rho e co ci
  let a' := csA mm rho' e co' ci'
  let S00 : ℂ := -Complex.I * ((a * c * ci : ℝ) : ℂ)
  let S01 : ℂ := (a : ℂ)
  let S11 : ℂ := -Complex.I * ((a * c * co : ℝ) : ℂ)
  let S'00 : ℂ := -Complex.I * ((a' * c' * ci' : ℝ) : ℂ)
  let S'01 : ℂ := (a' : ℂ)
  let S'11 : ℂ := -Complex.I * ((a' * c' * co' : ℝ) : ℂ)
  let t1 : ℂ := S00 * θ 7 + S11 * θ 8
  let t2 : ℂ := S'00 * θ 9 + S'11 * θ 10
  let t3 : ℂ := S00 * θ 11 * S'00 * θ 13 + S01 * θ 12 * S'01 * θ 13 +
      S01 * θ 11 * S'01 * θ 14 + S11 * θ 12 * S'11 * θ 14
  0 - t1 - t2 + (mm : ℂ) * t3

-- The compact parameter set: all coordinates bounded by `R`, and `χ` coordinates nonnegative.
private def ParSet (R : ℝ) : Set (Fin 15 → ℂ) :=
  Metric.closedBall 0 R ∩ {θ | 0 ≤ (θ 3).re ∧ 0 ≤ (θ 4).re ∧ 0 ≤ (θ 5).re ∧ 0 ≤ (θ 6).re}

private lemma ParSet_compact (R : ℝ) : IsCompact (ParSet R) := by
  refine (isCompact_closedBall (0 : Fin 15 → ℂ) R).inter_right ?_
  have hc : ∀ i : Fin 15, Continuous fun θ : Fin 15 → ℂ => (θ i).re :=
    fun i => Complex.continuous_re.comp (continuous_apply i)
  have : {θ : Fin 15 → ℂ | 0 ≤ (θ 3).re ∧ 0 ≤ (θ 4).re ∧ 0 ≤ (θ 5).re ∧ 0 ≤ (θ 6).re} =
      ({θ | 0 ≤ (θ 3).re} ∩ {θ | 0 ≤ (θ 4).re}) ∩ ({θ | 0 ≤ (θ 5).re} ∩ {θ | 0 ≤ (θ 6).re}) := by
    ext θ; simp [and_assoc]
  rw [this]
  exact ((isClosed_le continuous_const (hc 3)).inter (isClosed_le continuous_const (hc 4))).inter
    ((isClosed_le continuous_const (hc 5)).inter (isClosed_le continuous_const (hc 6)))

private lemma csA_den_pos {mm rho e chiO chiI : ℝ} (hO : 0 ≤ chiO) (hI : 0 ≤ chiI) :
    0 < 1 + (mm * rho * e) * (mm * rho * e) * chiO * chiI := by
  have : 0 ≤ (mm * rho * e) * (mm * rho * e) * chiO * chiI := by
    have := mul_self_nonneg (mm * rho * e)
    positivity
  linarith

private lemma psiF_cont (R : ℝ) :
    Continuous (fun p : ParSet R × ℝ => psiF p.1.1 p.2) := by
  have hco : ∀ i : Fin 15, Continuous fun p : ParSet R × ℝ => (p.1.1 i) :=
    fun i => (continuous_apply i).comp (continuous_subtype_val.comp continuous_fst)
  have hre : ∀ i : Fin 15, Continuous fun p : ParSet R × ℝ => (p.1.1 i).re :=
    fun i => Complex.continuous_re.comp (hco i)
  have he : Continuous fun p : ParSet R × ℝ => p.2 := continuous_snd
  have hpos : ∀ (p : ParSet R × ℝ), 0 ≤ (p.1.1 3).re ∧ 0 ≤ (p.1.1 4).re ∧ 0 ≤ (p.1.1 5).re ∧ 0 ≤ (p.1.1 6).re :=
    fun p => p.1.2.2
  have ha : Continuous fun p : ParSet R × ℝ => csA (p.1.1 0).re (p.1.1 1).re p.2 (p.1.1 3).re (p.1.1 4).re := by
    unfold csA
    refine Continuous.div (by fun_prop) (by fun_prop) fun p => (csA_den_pos (hpos p).1 (hpos p).2.1).ne'
  have ha' : Continuous fun p : ParSet R × ℝ => csA (p.1.1 0).re (p.1.1 2).re p.2 (p.1.1 5).re (p.1.1 6).re := by
    unfold csA
    refine Continuous.div (by fun_prop) (by fun_prop) fun p => (csA_den_pos (hpos p).2.2.1 (hpos p).2.2.2).ne'
  unfold psiF
  simp only
  fun_prop

private lemma psiF_bound_aux (S00 S01 S11 T00 T01 T11 A B C D E F G H : ℂ) (mm K R : ℝ) (hK : 0 ≤ K) (hR : 0 ≤ R)
    (hm : |mm| ≤ R) (h1 : ‖S00‖ ≤ K) (h2 : ‖S01‖ ≤ K) (h3 : ‖S11‖ ≤ K) (h4 : ‖T00‖ ≤ K) (h5 : ‖T01‖ ≤ K)
    (h6 : ‖T11‖ ≤ K) (hA : ‖A‖ ≤ R) (hB : ‖B‖ ≤ R) (hC : ‖C‖ ≤ R) (hD : ‖D‖ ≤ R) (hE : ‖E‖ ≤ R)
    (hF : ‖F‖ ≤ R) (hG : ‖G‖ ≤ R) (hH : ‖H‖ ≤ R) :
    ‖0 - (S00 * A + S11 * B) - (T00 * C + T11 * D) +
      (mm : ℂ) * (S00 * E * T00 * G + S01 * F * T01 * G + S01 * E * T01 * H + S11 * F * T11 * H)‖ ≤
      4 * K * R + R * (4 * K ^ 2 * R ^ 2) := by
  have n1 : ‖S00 * A + S11 * B‖ ≤ 2 * K * R := by
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul]
    nlinarith [mul_le_mul h1 hA (norm_nonneg _) hK, mul_le_mul h3 hB (norm_nonneg _) hK]
  have n2' : ‖T00 * C + T11 * D‖ ≤ 2 * K * R := by
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul]
    nlinarith [mul_le_mul h4 hC (norm_nonneg _) hK, mul_le_mul h6 hD (norm_nonneg _) hK]
  have q : ∀ (a b c d : ℂ), ‖a‖ ≤ K → ‖b‖ ≤ R → ‖c‖ ≤ K → ‖d‖ ≤ R → ‖a * b * c * d‖ ≤ K ^ 2 * R ^ 2 := by
    intro a b c d ha hb hc hd
    rw [norm_mul, norm_mul, norm_mul]
    have := mul_le_mul (mul_le_mul (mul_le_mul ha hb (norm_nonneg _) hK) hc (norm_nonneg _) (by positivity)) hd (norm_nonneg _) (by positivity)
    nlinarith [this]
  have n3 : ‖S00 * E * T00 * G + S01 * F * T01 * G + S01 * E * T01 * H + S11 * F * T11 * H‖ ≤ 4 * K ^ 2 * R ^ 2 := by
    have a1 := q S00 E T00 G h1 hE h4 hG
    have a2 := q S01 F T01 G h2 hF h5 hG
    have a3 := q S01 E T01 H h2 hE h5 hH
    have a4 := q S11 F T11 H h3 hF h6 hH
    calc _ ≤ ‖S00 * E * T00 * G + S01 * F * T01 * G + S01 * E * T01 * H‖ + ‖S11 * F * T11 * H‖ := norm_add_le _ _
      _ ≤ (‖S00 * E * T00 * G + S01 * F * T01 * G‖ + ‖S01 * E * T01 * H‖) + ‖S11 * F * T11 * H‖ :=
          add_le_add (norm_add_le _ _) le_rfl
      _ ≤ ((‖S00 * E * T00 * G‖ + ‖S01 * F * T01 * G‖) + ‖S01 * E * T01 * H‖) + ‖S11 * F * T11 * H‖ :=
          add_le_add (add_le_add (norm_add_le _ _) le_rfl) le_rfl
      _ ≤ 4 * K ^ 2 * R ^ 2 := by linarith
  have n4 : ‖(mm : ℂ) * (S00 * E * T00 * G + S01 * F * T01 * G + S01 * E * T01 * H + S11 * F * T11 * H)‖ ≤
      R * (4 * K ^ 2 * R ^ 2) := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul hm n3 (norm_nonneg _) hR
  calc _ ≤ ‖0 - (S00 * A + S11 * B) - (T00 * C + T11 * D)‖ + _ := norm_add_le _ _
    _ ≤ (‖0 - (S00 * A + S11 * B)‖ + ‖T00 * C + T11 * D‖) + _ := add_le_add (norm_sub_le _ _) le_rfl
    _ ≤ ((‖(0 : ℂ)‖ + ‖S00 * A + S11 * B‖) + ‖T00 * C + T11 * D‖) + _ :=
        add_le_add (add_le_add (norm_sub_le _ _) le_rfl) le_rfl
    _ ≤ 4 * K * R + R * (4 * K ^ 2 * R ^ 2) := by simp only [norm_zero]; linarith

private lemma psiF_bound (R : ℝ) (hR : 1 ≤ R) :
    ∃ Cψ : ℝ, ∀ (θ : ParSet R) (e : ℝ), ‖psiF θ.1 e‖ ≤ Cψ * (1 + |e|) ^ 4 := by
  refine ⟨4 * R ^ 5 + 4 * R ^ 11, fun θ e => ?_⟩
  have hR0 : 0 ≤ R := by linarith
  have hb : ∀ i : Fin 15, ‖θ.1 i‖ ≤ R := by
    intro i
    have := θ.2.1
    rw [mem_closedBall_zero_iff] at this
    exact (norm_le_pi_norm θ.1 i).trans this
  have hre : ∀ i : Fin 15, |(θ.1 i).re| ≤ R := fun i => (Complex.abs_re_le_norm _).trans (hb i)
  obtain ⟨h3, h4, h5, h6⟩ := θ.2.2
  have hu : 1 ≤ 1 + |e| := by linarith [abs_nonneg e]
  set u := 1 + |e| with hu_def
  have he1 : |e| ≤ u := by linarith
  have he2 : |e| * |e| ≤ u ^ 2 := by nlinarith [abs_nonneg e]
  -- generic bound for `a`
  have hcsA : ∀ (mm rho chiO chiI : ℝ), |rho| ≤ R → 0 ≤ chiO → 0 ≤ chiI → |csA mm rho e chiO chiI| ≤ R * u := by
    intro mm rho chiO chiI hrho hO hI
    unfold csA
    have hden := csA_den_pos (mm := mm) (rho := rho) (e := e) hO hI
    rw [abs_div, abs_of_pos hden, div_le_iff₀ hden]
    have : |rho * e| ≤ R * u := by
      rw [abs_mul]; exact mul_le_mul hrho he1 (abs_nonneg _) hR0
    have hge : 1 ≤ 1 + (mm * rho * e) * (mm * rho * e) * chiO * chiI := by
      have := hden; nlinarith [mul_nonneg (mul_nonneg (mul_self_nonneg (mm * rho * e)) hO) hI]
    calc |rho * e| ≤ R * u := this
      _ ≤ R * u * (1 + (mm * rho * e) * (mm * rho * e) * chiO * chiI) := by
          nlinarith [mul_nonneg hR0 (by linarith : (0:ℝ) ≤ u)]
  have ha := hcsA (θ.1 0).re (θ.1 1).re (θ.1 3).re (θ.1 4).re (hre 1) h3 h4
  have ha' := hcsA (θ.1 0).re (θ.1 2).re (θ.1 5).re (θ.1 6).re (hre 2) h5 h6
  set a := csA (θ.1 0).re (θ.1 1).re e (θ.1 3).re (θ.1 4).re with hadef
  set a' := csA (θ.1 0).re (θ.1 2).re e (θ.1 5).re (θ.1 6).re with ha'def
  set c := (θ.1 0).re * (θ.1 1).re * e with hcdef
  set c' := (θ.1 0).re * (θ.1 2).re * e with hc'def
  have hc : |c| ≤ R * R * u := by
    rw [hcdef, abs_mul, abs_mul]
    exact mul_le_mul (mul_le_mul (hre 0) (hre 1) (abs_nonneg _) hR0) he1 (abs_nonneg _) (by positivity)
  have hc' : |c'| ≤ R * R * u := by
    rw [hc'def, abs_mul, abs_mul]
    exact mul_le_mul (mul_le_mul (hre 0) (hre 2) (abs_nonneg _) hR0) he1 (abs_nonneg _) (by positivity)
  have hu2 : u ≤ u ^ 2 := by nlinarith
  have hK : ∀ (a c ch : ℝ), |a| ≤ R * u → |c| ≤ R * R * u → |ch| ≤ R → ‖(-Complex.I * ((a * c * ch : ℝ) : ℂ))‖ ≤ R ^ 4 * u ^ 2 := by
    intro a c ch h1 h2 h3
    rw [norm_mul, norm_neg, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_mul]
    have := mul_le_mul (mul_le_mul h1 h2 (abs_nonneg _) (by positivity)) h3 (abs_nonneg _) (by positivity)
    nlinarith [this]
  have hS00 := hK a c (θ.1 4).re ha hc (hre 4)
  have hS11 := hK a c (θ.1 3).re ha hc (hre 3)
  have hSp00 := hK a' c' (θ.1 6).re ha' hc' (hre 6)
  have hSp11 := hK a' c' (θ.1 5).re ha' hc' (hre 5)
  have h1R : R ≤ R ^ 4 := by nlinarith [pow_le_pow_right₀ hR (by norm_num : 1 ≤ 4)]
  have hRu : R * u ≤ R ^ 4 * u ^ 2 := mul_le_mul h1R hu2 (by positivity) (by positivity)
  have hS01 : ‖(a : ℂ)‖ ≤ R ^ 4 * u ^ 2 := by
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact ha.trans hRu
  have hSp01 : ‖(a' : ℂ)‖ ≤ R ^ 4 * u ^ 2 := by
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact ha'.trans hRu
  unfold psiF
  simp only
  have key := psiF_bound_aux (-Complex.I * ((a * c * (θ.1 4).re : ℝ) : ℂ)) (a : ℂ) (-Complex.I * ((a * c * (θ.1 3).re : ℝ) : ℂ))
    (-Complex.I * ((a' * c' * (θ.1 6).re : ℝ) : ℂ)) (a' : ℂ) (-Complex.I * ((a' * c' * (θ.1 5).re : ℝ) : ℂ))
    (θ.1 7) (θ.1 8) (θ.1 9) (θ.1 10) (θ.1 11) (θ.1 12) (θ.1 13) (θ.1 14) (θ.1 0).re (R ^ 4 * u ^ 2) R
    (by positivity) hR0 (hre 0) hS00 hS01 hS11 hSp00 hSp01 hSp11 (hb 7) (hb 8) (hb 9) (hb 10) (hb 11) (hb 12)
    (hb 13) (hb 14)
  refine key.trans ?_
  have hu4 : u ^ 2 ≤ u ^ 4 := pow_le_pow_right₀ hu (by norm_num)
  have e1 : 4 * (R ^ 4 * u ^ 2) * R = 4 * R ^ 5 * u ^ 2 := by ring
  have e2 : R * (4 * (R ^ 4 * u ^ 2) ^ 2 * R ^ 2) = 4 * R ^ 11 * u ^ 4 := by ring
  rw [e1, e2]
  have hR5 : 0 ≤ 4 * R ^ 5 := by positivity
  have hR11 : 0 ≤ 4 * R ^ 11 := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hu4 hR5]


/-! ### The bar parameters -/

private lemma vrp_abs_entry_opNorm {k l : ℕ} (K : Mat k l) (i : Fin k) (j : Fin l) : |K i j| ≤ opNorm K := by
  open scoped Matrix.Norms.L2Operator in
  have h1 := Matrix.l2_opNorm_mulVec K (EuclideanSpace.single j (1 : ℝ))
  have h2 := PiLp.norm_apply_le ((EuclideanSpace.equiv (Fin k) ℝ).symm
    (K *ᵥ ⇑(EuclideanSpace.single j (1 : ℝ)))) i
  have h3 : ((EuclideanSpace.equiv (Fin k) ℝ).symm
      (K *ᵥ ⇑(EuclideanSpace.single j (1 : ℝ)))) i = K i j := by
    simp [Matrix.mulVec, dotProduct, EuclideanSpace.single_apply]
  simp only [EuclideanSpace.norm_single, norm_one, mul_one] at h1
  rw [h3, Real.norm_eq_abs] at h2
  rw [opNorm_eq_norm]
  linarith

private lemma vrp_abs_trace_le {k : ℕ} (X : Mat k k) : |Matrix.trace X| ≤ (k : ℝ) * opNorm X := by
  unfold Matrix.trace
  calc |∑ i, X.diag i| ≤ ∑ i, |X.diag i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin k, opNorm X := Finset.sum_le_sum fun i _ => vrp_abs_entry_opNorm X i i
    _ = (k : ℝ) * opNorm X := by simp

private lemma vrp_opNorm_mul {a b c : ℕ} (A : Mat a b) (B : Mat b c) : opNorm (A * B) ≤ opNorm A * opNorm B := by
  open scoped Matrix.Norms.L2Operator in
  rw [opNorm_eq_norm, opNorm_eq_norm, opNorm_eq_norm]
  exact Matrix.l2_opNorm_mul A B

private lemma vrp_opNorm_nonneg {a b : ℕ} (A : Mat a b) : 0 ≤ opNorm A := by
  unfold opNorm; exact norm_nonneg _

/-- `Tr(S R) ≥ 0` for `S = r r` (`r` symmetric) and `R` positive semidefinite. -/
private lemma vrp_trace_nonneg {k : ℕ} (r S R : Mat k k) (hsym : rᵀ = r) (hrr : r * r = S)
    (hR : R.PosSemidef) : 0 ≤ Matrix.trace (S * R) := by
  have h := hR.conjTranspose_mul_mul_same r
  rw [Matrix.conjTranspose_eq_transpose_of_trivial, hsym] at h
  have := h.trace_nonneg
  have e : Matrix.trace (S * R) = Matrix.trace (r * R * r) := by
    rw [← hrr, Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc]
  rw [e]; exact this

private lemma Rs_psd {m n : ℕ} (K : Mat m n) {s : ℝ} (hs : 0 < s) : (Rs K s).PosSemidef := by
  have h1 : (K * Kᵀ).PosSemidef := by
    have h := Matrix.posSemidef_self_mul_conjTranspose K
    rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at h
  have h2 : (s • (1 : Mat m m)).PosDef := Matrix.PosDef.one.smul hs
  have h3 := (Matrix.PosDef.add_posSemidef h2 h1)
  rw [add_comm] at h3
  exact h3.posSemidef.inv

private lemma Rts_psd {m n : ℕ} (K : Mat m n) {s : ℝ} (hs : 0 < s) : (Rts K s).PosSemidef := by
  have := Rs_psd Kᵀ hs
  unfold Rs at this; unfold Rts
  simpa using this

/-- The real `χ` parameter of the compression of a resolvent. -/
private def chiO {m n : ℕ} (C : Covariances m n) (B : ℕ) (K : Mat m n) (s : ℝ) : ℝ :=
  Real.sqrt s * ((B : ℝ)⁻¹ * Matrix.trace (C.Sout * Rs K s))

private def chiI {m n : ℕ} (C : Covariances m n) (B : ℕ) (K : Mat m n) (s : ℝ) : ℝ :=
  Real.sqrt s * ((B : ℝ)⁻¹ * Matrix.trace (C.Sin * Rts K s))

private lemma chiO_nonneg {m n : ℕ} (C : Covariances m n) (B : ℕ) (K : Mat m n) {s : ℝ} (hs : 0 < s) :
    0 ≤ chiO C B K s := by
  unfold chiO
  have := vrp_trace_nonneg (rOut C) C.Sout (Rs K s) (vrp_rOut_symm C) (vrp_rOut_mul C) (Rs_psd K hs)
  positivity

private lemma chiI_nonneg {m n : ℕ} (C : Covariances m n) (B : ℕ) (K : Mat m n) {s : ℝ} (hs : 0 < s) :
    0 ≤ chiI C B K s := by
  unfold chiI
  have := vrp_trace_nonneg (rIn C) C.Sin (Rts K s) (vrp_rIn_symm C) (vrp_rIn_mul C) (Rts_psd K hs)
  positivity

private lemma chiO_le {m n : ℕ} (C : Covariances m n) (B : ℕ) (hB : 0 < B) (K : Mat m n) {s : ℝ} (hs : 0 < s)
    (γ CSig : ℝ) (hm : (m : ℝ) ≤ γ * B) (hCo : opNorm C.Sout ≤ CSig) (hγ : 0 ≤ γ) :
    chiO C B K s ≤ γ * CSig / Real.sqrt s := by
  unfold chiO
  have hBr : (0 : ℝ) < B := by exact_mod_cast hB
  have hs0 : 0 < Real.sqrt s := Real.sqrt_pos.mpr hs
  have hss : Real.sqrt s * Real.sqrt s = s := Real.mul_self_sqrt hs.le
  have hR : opNorm (Rs K s) ≤ 1 / s := (lem_app_de_resolvent K s hs).1
  have hC0 : 0 ≤ CSig := (vrp_opNorm_nonneg _).trans hCo
  have htr : Matrix.trace (C.Sout * Rs K s) ≤ (m : ℝ) * (CSig * (1 / s)) := by
    have h1 := vrp_abs_trace_le (C.Sout * Rs K s)
    have h2 := vrp_opNorm_mul C.Sout (Rs K s)
    have h3 : opNorm C.Sout * opNorm (Rs K s) ≤ CSig * (1 / s) :=
      mul_le_mul hCo hR (vrp_opNorm_nonneg _) hC0
    calc Matrix.trace (C.Sout * Rs K s) ≤ |Matrix.trace (C.Sout * Rs K s)| := le_abs_self _
      _ ≤ (m : ℝ) * opNorm (C.Sout * Rs K s) := h1
      _ ≤ (m : ℝ) * (CSig * (1 / s)) := mul_le_mul_of_nonneg_left (h2.trans h3) (Nat.cast_nonneg m)
  have h4 : Real.sqrt s * ((B : ℝ)⁻¹ * Matrix.trace (C.Sout * Rs K s)) ≤
      Real.sqrt s * ((B : ℝ)⁻¹ * ((m : ℝ) * (CSig * (1 / s)))) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left htr (by positivity)) hs0.le
  refine h4.trans ?_
  have : (m : ℝ) * (B : ℝ)⁻¹ ≤ γ := by
    rw [mul_inv_le_iff₀ hBr]; exact hm
  have hq : Real.sqrt s * (1 / s) = 1 / Real.sqrt s := by
    rw [mul_one_div, div_eq_div_iff hs.ne' hs0.ne']; nlinarith [hss]
  calc Real.sqrt s * ((B : ℝ)⁻¹ * ((m : ℝ) * (CSig * (1 / s))))
      = ((m : ℝ) * (B : ℝ)⁻¹) * CSig * (Real.sqrt s * (1 / s)) := by ring
    _ = ((m : ℝ) * (B : ℝ)⁻¹) * (CSig / Real.sqrt s) := by rw [hq]; ring
    _ ≤ γ * (CSig / Real.sqrt s) := mul_le_mul_of_nonneg_right this (by positivity)
    _ = γ * CSig / Real.sqrt s := by ring

private lemma chiI_le {m n : ℕ} (C : Covariances m n) (B : ℕ) (hB : 0 < B) (K : Mat m n) {s : ℝ} (hs : 0 < s)
    (γ CSig : ℝ) (hn : (n : ℝ) ≤ γ * B) (hCi : opNorm C.Sin ≤ CSig) (hγ : 0 ≤ γ) :
    chiI C B K s ≤ γ * CSig / Real.sqrt s := by
  unfold chiI
  have hBr : (0 : ℝ) < B := by exact_mod_cast hB
  have hs0 : 0 < Real.sqrt s := Real.sqrt_pos.mpr hs
  have hss : Real.sqrt s * Real.sqrt s = s := Real.mul_self_sqrt hs.le
  have hR : opNorm (Rts K s) ≤ 1 / s := (lem_app_de_resolvent K s hs).2.1
  have hC0 : 0 ≤ CSig := (vrp_opNorm_nonneg _).trans hCi
  have htr : Matrix.trace (C.Sin * Rts K s) ≤ (n : ℝ) * (CSig * (1 / s)) := by
    have h1 := vrp_abs_trace_le (C.Sin * Rts K s)
    have h2 := vrp_opNorm_mul C.Sin (Rts K s)
    have h3 : opNorm C.Sin * opNorm (Rts K s) ≤ CSig * (1 / s) :=
      mul_le_mul hCi hR (vrp_opNorm_nonneg _) hC0
    calc Matrix.trace (C.Sin * Rts K s) ≤ |Matrix.trace (C.Sin * Rts K s)| := le_abs_self _
      _ ≤ (n : ℝ) * opNorm (C.Sin * Rts K s) := h1
      _ ≤ (n : ℝ) * (CSig * (1 / s)) := mul_le_mul_of_nonneg_left (h2.trans h3) (Nat.cast_nonneg n)
  have h4 : Real.sqrt s * ((B : ℝ)⁻¹ * Matrix.trace (C.Sin * Rts K s)) ≤
      Real.sqrt s * ((B : ℝ)⁻¹ * ((n : ℝ) * (CSig * (1 / s)))) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left htr (by positivity)) hs0.le
  refine h4.trans ?_
  have : (n : ℝ) * (B : ℝ)⁻¹ ≤ γ := by
    rw [mul_inv_le_iff₀ hBr]; exact hn
  have hq : Real.sqrt s * (1 / s) = 1 / Real.sqrt s := by
    rw [mul_one_div, div_eq_div_iff hs.ne' hs0.ne']; nlinarith [hss]
  calc Real.sqrt s * ((B : ℝ)⁻¹ * ((n : ℝ) * (CSig * (1 / s))))
      = ((n : ℝ) * (B : ℝ)⁻¹) * CSig * (Real.sqrt s * (1 / s)) := by ring
    _ = ((n : ℝ) * (B : ℝ)⁻¹) * (CSig / Real.sqrt s) := by rw [hq]; ring
    _ ≤ γ * (CSig / Real.sqrt s) := mul_le_mul_of_nonneg_right this (by positivity)
    _ = γ * CSig / Real.sqrt s := by ring

private lemma mmOf_cP {m n : ℕ} (C : Covariances m n) (B : ℕ) (K : Mat m n) (s : ℝ) :
    mmOf C B (cP K s) = !![Complex.I * (chiO C B K s : ℂ), 0; 0, Complex.I * (chiI C B K s : ℂ)] := by
  have e1 : Matrix.trace (cOf C.Sout * (zI s • cOf (Rs K s))) =
      zI s * ((Matrix.trace (C.Sout * Rs K s) : ℝ) : ℂ) := by
    rw [Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul, ← cOf_mul]
    congr 1
    unfold Matrix.trace Matrix.diag
    simp
  have e2 : Matrix.trace (cOf C.Sin * (zI s • cOf (Rts K s))) =
      zI s * ((Matrix.trace (C.Sin * Rts K s) : ℝ) : ℂ) := by
    rw [Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul, ← cOf_mul]
    congr 1
    unfold Matrix.trace Matrix.diag
    simp
  unfold mmOf cP
  simp only [Matrix.toBlocks_fromBlocks₁₁, Matrix.toBlocks_fromBlocks₂₂, e1, e2]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [chiO, chiI, zI]
  · push_cast; ring
  · push_cast; ring


private lemma OB_entry {k l : ℕ} {X : Matrix (Fin k) (Fin l) ℂ} {d : ℝ} (hX : OB X d) (i : Fin k) (j : Fin l) :
    ‖X i j‖ ≤ d := by
  have hv : cn (Pi.single j (1 : ℂ) : Fin l → ℂ) = 1 := by
    unfold cn
    have : ∀ x : Fin l, ‖(Pi.single j (1 : ℂ) : Fin l → ℂ) x‖ ^ 2 = if x = j then 1 else 0 := by
      intro x; by_cases h : x = j <;> simp [Pi.single_apply, h]
    simp only [this, Finset.sum_ite_eq', Finset.mem_univ, if_true, Real.sqrt_one]
  have h1 := hX (Pi.single j (1 : ℂ))
  rw [hv, mul_one] at h1
  have h2 : ‖X i j‖ ≤ cn (X *ᵥ (Pi.single j (1 : ℂ) : Fin l → ℂ)) := by
    unfold cn
    refine Real.le_sqrt_of_sq_le ?_
    have : (X *ᵥ (Pi.single j (1 : ℂ) : Fin l → ℂ)) i = X i j := by
      simp [Matrix.mulVec, dotProduct, Pi.single_apply]
    calc ‖X i j‖ ^ 2 = ‖(X *ᵥ (Pi.single j (1 : ℂ) : Fin l → ℂ)) i‖ ^ 2 := by rw [this]
      _ ≤ ∑ a, ‖(X *ᵥ (Pi.single j (1 : ℂ) : Fin l → ℂ)) a‖ ^ 2 :=
          Finset.single_le_sum (f := fun a => ‖(X *ᵥ (Pi.single j (1 : ℂ) : Fin l → ℂ)) a‖ ^ 2)
            (fun a _ => sq_nonneg _) (Finset.mem_univ i)
  exact h2.trans h1

private lemma OB_trace {k : ℕ} {X : Matrix (Fin k) (Fin k) ℂ} {d : ℝ} (hX : OB X d) :
    ‖Matrix.trace X‖ ≤ (k : ℝ) * d := by
  unfold Matrix.trace
  calc ‖∑ i, X.diag i‖ ≤ ∑ i, ‖X.diag i‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin k, d := Finset.sum_le_sum fun i _ => OB_entry hX i i
    _ = (k : ℝ) * d := by simp

private lemma mmOf_entry00 {m n : ℕ} (C : Covariances m n) (B : ℕ) (hB : 0 < B) (γ CSig c : ℝ) (hγ : 0 ≤ γ)
    (hc : 0 ≤ c) (hm : (m : ℝ) ≤ γ * B) (hCo : opNorm C.Sout ≤ CSig) (M : CMat m n) (hM : OB M c) :
    ‖mmOf C B M 0 0‖ ≤ γ * CSig * c := by
  have hBr : (0 : ℝ) < B := by exact_mod_cast hB
  have hC0 : 0 ≤ CSig := (vrp_opNorm_nonneg _).trans hCo
  have hX : OB (cOf C.Sout * M.toBlocks₁₁) (CSig * c) :=
    OB_mul hC0 (OB_real _ hCo) (OB_b11 hM)
  have h1 := OB_trace hX
  unfold mmOf
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_fin_one]
  rw [norm_mul, norm_inv, Complex.norm_natCast]
  have : (m : ℝ) * (B : ℝ)⁻¹ ≤ γ := by rw [mul_inv_le_iff₀ hBr]; exact hm
  calc (B : ℝ)⁻¹ * ‖Matrix.trace (cOf C.Sout * M.toBlocks₁₁)‖ ≤ (B : ℝ)⁻¹ * ((m : ℝ) * (CSig * c)) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = ((m : ℝ) * (B : ℝ)⁻¹) * (CSig * c) := by ring
    _ ≤ γ * (CSig * c) := mul_le_mul_of_nonneg_right this (by positivity)
    _ = γ * CSig * c := by ring

private lemma mmOf_entry11 {m n : ℕ} (C : Covariances m n) (B : ℕ) (hB : 0 < B) (γ CSig c : ℝ) (hγ : 0 ≤ γ)
    (hc : 0 ≤ c) (hn : (n : ℝ) ≤ γ * B) (hCi : opNorm C.Sin ≤ CSig) (M : CMat m n) (hM : OB M c) :
    ‖mmOf C B M 1 1‖ ≤ γ * CSig * c := by
  have hBr : (0 : ℝ) < B := by exact_mod_cast hB
  have hC0 : 0 ≤ CSig := (vrp_opNorm_nonneg _).trans hCi
  have hX : OB (cOf C.Sin * M.toBlocks₂₂) (CSig * c) :=
    OB_mul hC0 (OB_real _ hCi) (OB_b22 hM)
  have h1 := OB_trace hX
  unfold mmOf
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_fin_one]
  rw [norm_mul, norm_inv, Complex.norm_natCast]
  have : (n : ℝ) * (B : ℝ)⁻¹ ≤ γ := by rw [mul_inv_le_iff₀ hBr]; exact hn
  calc (B : ℝ)⁻¹ * ‖Matrix.trace (cOf C.Sin * M.toBlocks₂₂)‖ ≤ (B : ℝ)⁻¹ * ((n : ℝ) * (CSig * c)) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = ((n : ℝ) * (B : ℝ)⁻¹) * (CSig * c) := by ring
    _ ≤ γ * (CSig * c) := mul_le_mul_of_nonneg_right this (by positivity)
    _ = γ * CSig * c := by ring


/-! ### The bar matrices `C̄` -/

private def Cbar (c chiO chiI : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  ((c / (1 + c * c * chiO * chiI) : ℝ) : ℂ) •
    !![-(Complex.I * ((c * chiI : ℝ) : ℂ)), 1; 1, -(Complex.I * ((c * chiO : ℝ) : ℂ))]

private def Wd (a b : ℂ) : Matrix (Fin 2) (Fin 2) ℂ := !![a, 0; 0, b]

private lemma Cbar_rel (c chiO chiI : ℝ) (hO : 0 ≤ chiO) (hI : 0 ≤ chiI) :
    (1 + (c : ℂ) • (J2 * Wd (Complex.I * (chiO : ℂ)) (Complex.I * (chiI : ℂ)))) * Cbar c chiO chiI =
      (c : ℂ) • J2 := by
  have hden : (1 + c * c * chiO * chiI : ℝ) ≠ 0 := by
    have : 0 ≤ c * c * chiO * chiI := by
      have := mul_self_nonneg c
      positivity
    linarith
  have hdenC : ((1 + c * c * chiO * chiI : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hden
  have hdenC' : (1 + (c : ℂ) ^ 2 * (chiO : ℂ) * (chiI : ℂ)) ≠ 0 := by
    intro h; apply hdenC; push_cast; linear_combination h
  unfold Cbar Wd J2
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> push_cast <;>
    field_simp <;> ring_nf <;> simp [Complex.I_sq] <;> ring

private lemma n2_Cbar (c chiO chiI : ℝ) (hO : 0 ≤ chiO) (hI : 0 ≤ chiI) :
    n2 (Cbar c chiO chiI) ≤ |c| * (2 + |c| * (chiO + chiI)) := by
  have hden : 1 ≤ 1 + c * c * chiO * chiI := by
    have : 0 ≤ c * c * chiO * chiI := by
      have := mul_self_nonneg c
      positivity
    linarith
  have hden0 : 0 < 1 + c * c * chiO * chiI := by linarith
  have ha : |c / (1 + c * c * chiO * chiI)| ≤ |c| := by
    rw [abs_div, abs_of_pos hden0, div_le_iff₀ hden0]
    nlinarith [abs_nonneg c]
  unfold n2 Cbar
  simp only [Matrix.smul_apply, smul_eq_mul, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_neg,
    Complex.norm_I, one_mul, mul_one, Matrix.cons_val_fin_one]
  set a := |c / (1 + c * c * chiO * chiI)| with ha_def
  have ha0 : 0 ≤ a := abs_nonneg _
  rw [abs_of_nonneg hI, abs_of_nonneg hO]
  have hc0 := abs_nonneg c
  nlinarith [mul_le_mul_of_nonneg_right ha (by positivity : 0 ≤ 2 + |c| * (chiO + chiI)),
    mul_nonneg ha0 hc0, mul_nonneg ha0 (mul_nonneg hc0 hO), mul_nonneg ha0 (mul_nonneg hc0 hI)]


private lemma cn_Zc_col0 {m n : ℕ} (x : Vec m) (y : Vec n) :
    cn (fun a : IDx m n => Zc x y a 0) = Real.sqrt (∑ i, x i ^ 2) := by
  unfold cn
  rw [Fintype.sum_sum_type]
  simp [Zc, Real.norm_eq_abs, sq_abs]

private lemma cn_Zc_col1 {m n : ℕ} (x : Vec m) (y : Vec n) :
    cn (fun a : IDx m n => Zc x y a 1) = Real.sqrt (∑ j, y j ^ 2) := by
  unfold cn
  rw [Fintype.sum_sum_type]
  simp [Zc, Real.norm_eq_abs, sq_abs]

private lemma compM_entry {m n : ℕ} (M : CMat m n) (x : Vec m) (y : Vec n) (i j : Fin 2) :
    compM M x y i j = ∑ a, Zc x y a i * (M *ᵥ (fun b : IDx m n => Zc x y b j)) a := by
  simp [compM, Matrix.mul_apply, Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc]

private lemma n2_compM {m n : ℕ} (M : CMat m n) (c : ℝ) (hc : 0 ≤ c) (hM : OB M c) (x : Vec m) (y : Vec n) :
    n2 (compM M x y) ≤ 2 * c * ((∑ i, x i ^ 2) + ∑ j, y j ^ 2) := by
  set nx := Real.sqrt (∑ i, x i ^ 2) with hnx
  set ny := Real.sqrt (∑ j, y j ^ 2) with hny
  have hx2 : nx ^ 2 = ∑ i, x i ^ 2 := Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)
  have hy2 : ny ^ 2 = ∑ j, y j ^ 2 := Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)
  have hnx0 : 0 ≤ nx := Real.sqrt_nonneg _
  have hny0 : 0 ≤ ny := Real.sqrt_nonneg _
  have key : ∀ i j : Fin 2, ‖compM M x y i j‖ ≤ c * cn (fun a : IDx m n => Zc x y a i) * cn (fun a : IDx m n => Zc x y a j) := by
    intro i j
    rw [compM_entry]
    exact cn_mulVec_le hM _ _
  have e00 : ‖compM M x y 0 0‖ ≤ c * nx * nx := by
    have := key 0 0; rwa [cn_Zc_col0] at this
  have e01 : ‖compM M x y 0 1‖ ≤ c * nx * ny := by
    have := key 0 1; rwa [cn_Zc_col0, cn_Zc_col1] at this
  have e10 : ‖compM M x y 1 0‖ ≤ c * ny * nx := by
    have := key 1 0; rwa [cn_Zc_col0, cn_Zc_col1] at this
  have e11 : ‖compM M x y 1 1‖ ≤ c * ny * ny := by
    have := key 1 1; rwa [cn_Zc_col1] at this
  unfold n2
  rw [← hx2, ← hy2]
  nlinarith [mul_nonneg hc (sq_nonneg (nx - ny)), mul_nonneg hc hnx0, mul_nonneg hc hny0]

private lemma n2_Cact (c : ℝ) (W' : Matrix (Fin 2) (Fin 2) ℂ) (w : ℝ) (hw : n2 W' ≤ w) :
    n2 ((c : ℂ) • J2 - ((c : ℂ) * c) • (J2 * W' * J2)) ≤ 2 * |c| + 4 * (c * c) * w := by
  refine (n2_sub _ _).trans ?_
  rw [n2_smul, n2_smul, Complex.norm_real, Real.norm_eq_abs, norm_mul, Complex.norm_real, Real.norm_eq_abs, n2_J2]
  have h1 : n2 (J2 * W' * J2) ≤ 2 * n2 W' * 2 := by
    calc n2 (J2 * W' * J2) ≤ n2 (J2 * W') * n2 J2 := n2_mul _ _
      _ ≤ (n2 J2 * n2 W') * n2 J2 := mul_le_mul_of_nonneg_right (n2_mul _ _) (n2_nonneg _)
      _ = 2 * n2 W' * 2 := by rw [n2_J2]
  have h2 : |c| * |c| = c * c := by rw [← abs_mul, abs_mul_self]
  have h0 := n2_nonneg W'
  have := mul_le_mul_of_nonneg_left h1 (mul_self_nonneg c)
  nlinarith [abs_nonneg c, mul_le_mul_of_nonneg_left hw (mul_self_nonneg c), h2]


/-! ### The pointwise comparison -/

private def kapOf (s₀ : ℝ) : ℝ := 3 / Real.sqrt s₀

private def LcOf (γ CSig s₀ : ℝ) : ℝ :=
  3 + 8 * kapOf s₀ + 2 * (γ * CSig / Real.sqrt s₀) + 2 * kapOf s₀ ^ 3 * (1 + γ * CSig) +
    2 * kapOf s₀ ^ 2 * (1 + γ * CSig)

private def parOf {m n : ℕ} (C : Covariances m n) (B : ℕ) (F : Mat m m) (G : Mat n n) (K H : Mat m n)
    (s u α β : ℝ) : Fin 15 → ℂ :=
  let mm := max α β
  ![(mm : ℂ), ((if mm = 0 then 0 else α / mm : ℝ) : ℂ), ((if mm = 0 then 0 else β / mm : ℝ) : ℂ),
    (chiO C B K s : ℂ), (chiI C B K s : ℂ), (chiO C B H u : ℂ), (chiI C B H u : ℂ),
    mmOf C B (cP K s * DGm G * cP H u * DFm F * cP K s) 0 0,
    mmOf C B (cP K s * DGm G * cP H u * DFm F * cP K s) 1 1,
    mmOf C B (cP H u * DFm F * cP K s * DGm G * cP H u) 0 0,
    mmOf C B (cP H u * DFm F * cP K s * DGm G * cP H u) 1 1,
    mmOf C B (cP K s * DGm G * cP H u) 0 0, mmOf C B (cP K s * DGm G * cP H u) 1 1,
    mmOf C B (cP H u * DFm F * cP K s) 0 0, mmOf C B (cP H u * DFm F * cP K s) 1 1]

private lemma mmOf_diag {m n : ℕ} (C : Covariances m n) (B : ℕ) (M : CMat m n) :
    mmOf C B M = Wd (mmOf C B M 0 0) (mmOf C B M 1 1) := by
  unfold mmOf Wd
  ext i j; fin_cases i <;> fin_cases j <;> simp

private lemma n2_mmOf {m n : ℕ} (C : Covariances m n) (B : ℕ) (M : CMat m n) :
    n2 (mmOf C B M) = ‖mmOf C B M 0 0‖ + ‖mmOf C B M 1 1‖ := by
  unfold n2 mmOf
  simp

private lemma psi_ident (mm rho rho' c c' chiO chiI chiO' chiI' e : ℝ) (Ao Ai Bo Bi Eo Ei To Ti : ℂ)
    (hc : c = mm * rho * e) (hc' : c' = mm * rho' * e) :
    (mm : ℂ) * psiF ![(mm : ℂ), (rho : ℂ), (rho' : ℂ), (chiO : ℂ), (chiI : ℂ), (chiO' : ℂ), (chiI' : ℂ),
        Ao, Ai, Bo, Bi, Eo, Ei, To, Ti] e =
      -Matrix.trace (Cbar c chiO chiI * Wd Ao Ai) - Matrix.trace (Cbar c' chiO' chiI' * Wd Bo Bi) +
        Matrix.trace (Cbar c chiO chiI * Wd Eo Ei * Cbar c' chiO' chiI' * Wd To Ti) := by
  subst hc hc'
  unfold psiF Cbar Wd csA
  simp [Matrix.trace, Matrix.diag, Matrix.mul_apply, Fin.sum_univ_two]
  ring_nf


private lemma OB_cP_mono {m n : ℕ} (K : Mat m n) {s s₀ : ℝ} (hs₀ : 0 < s₀) (hs : s₀ ≤ s) :
    OB (cP K s) (kapOf s₀) := by
  have hs0 : 0 < s := lt_of_lt_of_le hs₀ hs
  refine OB_mono (OB_cP K hs0) ?_
  unfold kapOf
  have h1 : Real.sqrt s₀ ≤ Real.sqrt s := Real.sqrt_le_sqrt hs
  have h2 : 0 < Real.sqrt s₀ := Real.sqrt_pos.mpr hs₀
  exact div_le_div_of_nonneg_left (by norm_num) h2 h1

private lemma kapOf_nonneg (s₀ : ℝ) : 0 ≤ kapOf s₀ := by unfold kapOf; positivity

private lemma LcOf_ge {γ CSig : ℝ} (hγ : 0 ≤ γ) (hC : 0 ≤ CSig) (s₀ : ℝ) :
    3 + 8 * kapOf s₀ ≤ LcOf γ CSig s₀ ∧ 2 * (γ * CSig / Real.sqrt s₀) ≤ LcOf γ CSig s₀ ∧
    2 * kapOf s₀ ^ 3 ≤ LcOf γ CSig s₀ ∧ 2 * γ * CSig * kapOf s₀ ^ 3 ≤ LcOf γ CSig s₀ ∧
    2 * kapOf s₀ ^ 2 ≤ LcOf γ CSig s₀ ∧ 2 * γ * CSig * kapOf s₀ ^ 2 ≤ LcOf γ CSig s₀ := by
  have hk := kapOf_nonneg s₀
  have h1 : 0 ≤ γ * CSig / Real.sqrt s₀ := by positivity
  have h2 : 0 ≤ kapOf s₀ ^ 3 := by positivity
  have h2' : 0 ≤ kapOf s₀ ^ 2 := by positivity
  have h3 : 0 ≤ γ * CSig := by positivity
  unfold LcOf
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> nlinarith [mul_nonneg h2 h3, mul_nonneg h2' h3]

private lemma LcOf_one_le {γ CSig : ℝ} (hγ : 0 ≤ γ) (hC : 0 ≤ CSig) (s₀ : ℝ) : 1 ≤ LcOf γ CSig s₀ := by
  have := (LcOf_ge hγ hC s₀).1
  have := kapOf_nonneg s₀
  linarith


private lemma ineq_C (c e N κ Lc q : ℝ) (hc : |c| ≤ |e|) (hq1 : 1 ≤ q) (hq2 : |e| * N ≤ q) (hκ : 0 ≤ κ)
    (hN : 0 ≤ N) (hL : 3 + 8 * κ ≤ Lc) :
    2 * |c| + 4 * (c * c) * (2 * κ * N) ≤ |c| * (Lc * q) := by
  have hcc : c * c = |c| * |c| := (abs_mul_abs_self c).symm
  have h0 := abs_nonneg c
  have h1 : |c| * N ≤ |e| * N := mul_le_mul_of_nonneg_right hc hN
  have h2 : 4 * (c * c) * (2 * κ * N) = 8 * κ * |c| * (|c| * N) := by rw [hcc]; ring
  rw [h2]
  have h3 : 8 * κ * |c| * (|c| * N) ≤ 8 * κ * |c| * q :=
    mul_le_mul_of_nonneg_left (h1.trans hq2) (by positivity)
  have h4 : |c| * ((3 + 8 * κ) * q) ≤ |c| * (Lc * q) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hL (by linarith)) h0
  nlinarith [mul_nonneg h0 (by linarith : (0:ℝ) ≤ q - 1)]

private lemma ineq_Cb (c e χo χi κ₁ Lc q : ℝ) (hc : |c| ≤ |e|) (hq3 : 1 + |e| ≤ q) (hχo : χo ≤ κ₁) (hχi : χi ≤ κ₁)
    (hχo0 : 0 ≤ χo) (hχi0 : 0 ≤ χi) (hL : 2 * κ₁ ≤ Lc) (hL3 : 3 ≤ Lc) :
    |c| * (2 + |c| * (χo + χi)) ≤ |c| * (Lc * q) := by
  have h0 := abs_nonneg c
  refine mul_le_mul_of_nonneg_left ?_ h0
  have h1 : |c| * (χo + χi) ≤ |e| * (2 * κ₁) := mul_le_mul hc (by linarith) (by positivity) (abs_nonneg _)
  have h2 : |e| * (2 * κ₁) ≤ |e| * Lc := mul_le_mul_of_nonneg_left hL (abs_nonneg _)
  nlinarith [mul_le_mul_of_nonneg_left hq3 (by linarith : (0:ℝ) ≤ Lc)]

private lemma ineq_sml (a Lc q N : ℝ) (hLc : 0 ≤ Lc) (hq : 1 ≤ q) (hN : N ≤ q) (hN0 : 0 ≤ N) (h : a ≤ Lc * N) :
    a ≤ Lc * q := h.trans (mul_le_mul_of_nonneg_left hN hLc)

private lemma ineq_sml' (a Lc q : ℝ) (hLc : 0 ≤ Lc) (hq : 1 ≤ q) (h : a ≤ Lc) : a ≤ Lc * q := by
  nlinarith


private lemma ineq_q (e N : ℝ) (hN : 0 ≤ N) :
    1 ≤ (1 + |e|) * (1 + N) ∧ |e| * N ≤ (1 + |e|) * (1 + N) ∧ 1 + |e| ≤ (1 + |e|) * (1 + N) ∧
      N ≤ (1 + |e|) * (1 + N) := by
  have he0 := abs_nonneg e
  have := mul_nonneg he0 hN
  refine ⟨?_, ?_, ?_, ?_⟩ <;> nlinarith

private lemma bnd_C {m n : ℕ} (K : Mat m n) (x : Vec m) (y : Vec n) {s s₀ : ℝ} (hs₀ : 0 < s₀)
    (hs : s₀ ≤ s) (c e Lc : ℝ) (hc : |c| ≤ |e|) (hL : 3 + 8 * kapOf s₀ ≤ Lc) :
    n2 ((c : ℂ) • J2 - ((c : ℂ) * c) • (J2 * ((Zc x y)ᵀ * (cP (K + c • outer x y) s * Zc x y)) * J2)) ≤
      |c| * (Lc * ((1 + |e|) * (1 + ((∑ i, x i ^ 2) + ∑ j, y j ^ 2)))) := by
  have hN0 : 0 ≤ (∑ i, x i ^ 2) + ∑ j, y j ^ 2 := by
    have : 0 ≤ ∑ i, x i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
    have : 0 ≤ ∑ j, y j ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
    linarith
  have hP' : OB (cP (K + c • outer x y) s) (kapOf s₀) := OB_cP_mono _ hs₀ hs
  have nW' := n2_compM _ _ (kapOf_nonneg s₀) hP' x y
  have h1 := n2_Cact c _ _ nW'
  obtain ⟨q1, q2, q3, q4⟩ := ineq_q e _ hN0
  exact h1.trans (ineq_C c e _ (kapOf s₀) Lc _ hc q1 q2 (kapOf_nonneg s₀) hN0 hL)

private lemma bnd_Cb {m n : ℕ} (C : Covariances m n) (B : ℕ) (hB : 0 < B) (K : Mat m n) {s s₀ : ℝ}
    (hs₀ : 0 < s₀) (hs : s₀ ≤ s) (γ CSig : ℝ) (hγ : 0 ≤ γ) (hm : (m : ℝ) ≤ γ * B) (hn : (n : ℝ) ≤ γ * B)
    (hCo : opNorm C.Sout ≤ CSig) (hCi : opNorm C.Sin ≤ CSig) (c e Lc N : ℝ) (hN : 0 ≤ N) (hc : |c| ≤ |e|)
    (hL : 2 * (γ * CSig / Real.sqrt s₀) ≤ Lc) (hL3 : 3 ≤ Lc) :
    n2 (Cbar c (chiO C B K s) (chiI C B K s)) ≤ |c| * (Lc * ((1 + |e|) * (1 + N))) := by
  have hs0 : 0 < s := lt_of_lt_of_le hs₀ hs
  have hκ1 : γ * CSig / Real.sqrt s ≤ γ * CSig / Real.sqrt s₀ := by
    have h1 : Real.sqrt s₀ ≤ Real.sqrt s := Real.sqrt_le_sqrt hs
    have h2 : 0 < Real.sqrt s₀ := Real.sqrt_pos.mpr hs₀
    have hC0 : 0 ≤ CSig := (vrp_opNorm_nonneg _).trans hCo
    exact div_le_div_of_nonneg_left (by positivity) h2 h1
  have xo := (chiO_le C B hB K hs0 γ CSig hm hCo hγ).trans hκ1
  have xi := (chiI_le C B hB K hs0 γ CSig hn hCi hγ).trans hκ1
  obtain ⟨q1, q2, q3, q4⟩ := ineq_q e _ hN
  exact (n2_Cbar c _ _ (chiO_nonneg C B K hs0) (chiI_nonneg C B K hs0)).trans
    (ineq_Cb c e _ _ _ Lc _ hc q3 xo xi (chiO_nonneg C B K hs0) (chiI_nonneg C B K hs0) hL hL3)


private lemma bnd_comp {m n : ℕ} (M : CMat m n) (c0 : ℝ) (hc0 : 0 ≤ c0) (hM : OB M c0) (x : Vec m) (y : Vec n)
    (Lc e : ℝ) (hLc : 0 ≤ Lc) (h : 2 * c0 ≤ Lc) :
    n2 (compM M x y) ≤ Lc * ((1 + |e|) * (1 + ((∑ i, x i ^ 2) + ∑ j, y j ^ 2))) := by
  have hN0 : 0 ≤ (∑ i, x i ^ 2) + ∑ j, y j ^ 2 := by
    have : 0 ≤ ∑ i, x i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
    have : 0 ≤ ∑ j, y j ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
    linarith
  obtain ⟨q1, q2, q3, q4⟩ := ineq_q e _ hN0
  refine (n2_compM M c0 hc0 hM x y).trans ?_
  refine ineq_sml _ Lc _ _ hLc q1 q4 hN0 ?_
  exact mul_le_mul_of_nonneg_right h hN0

private lemma bnd_mm {m n : ℕ} (C : Covariances m n) (B : ℕ) (hB : 0 < B) (γ CSig c0 : ℝ) (hγ : 0 ≤ γ)
    (hc0 : 0 ≤ c0) (hm : (m : ℝ) ≤ γ * B) (hn : (n : ℝ) ≤ γ * B) (hCo : opNorm C.Sout ≤ CSig)
    (hCi : opNorm C.Sin ≤ CSig) (M : CMat m n) (hM : OB M c0) (Lc N e : ℝ) (hLc : 0 ≤ Lc) (hN : 0 ≤ N)
    (h : 2 * γ * CSig * c0 ≤ Lc) :
    n2 (mmOf C B M) ≤ Lc * ((1 + |e|) * (1 + N)) := by
  obtain ⟨q1, q2, q3, q4⟩ := ineq_q e _ hN
  rw [n2_mmOf]
  have a := mmOf_entry00 C B hB γ CSig c0 hγ hc0 hm hCo M hM
  have b := mmOf_entry11 C B hB γ CSig c0 hγ hc0 hn hCi M hM
  exact ineq_sml' _ Lc _ hLc q1 (by linarith)


private lemma rho_ident (α β e : ℝ) (hα0 : 0 ≤ α) (hβ0 : 0 ≤ β) :
    α * e = max α β * (if max α β = 0 then 0 else α / max α β) * e := by
  by_cases h : max α β = 0
  · have : α = 0 := le_antisymm (h ▸ le_max_left α β) hα0
    simp [h, this]
  · simp only [h, if_false]
    field_simp

private lemma rho_ident' (α β e : ℝ) (hα0 : 0 ≤ α) (hβ0 : 0 ≤ β) :
    β * e = max α β * (if max α β = 0 then 0 else β / max α β) * e := by
  rw [max_comm α β] at *
  by_cases h : max β α = 0
  · have : β = 0 := le_antisymm (h ▸ le_max_left β α) hβ0
    simp [h, this]
  · simp only [h, if_false]
    field_simp

private lemma fin_eq (α β e ℓ S : ℝ) (hα0 : 0 ≤ α) (hβ0 : 0 ≤ β) :
    2 * (|α * e| + |β * e|) * ℓ ^ 7 * S = 2 * (α + β) * |e| * ℓ ^ 7 * S := by
  rw [abs_mul, abs_mul, abs_of_nonneg hα0, abs_of_nonneg hβ0]
  ring

private lemma vrp_point {m n : ℕ} (C : Covariances m n) (B : ℕ) (hB : 0 < B) (γ CSig s₀ : ℝ)
    (hγ : 0 ≤ γ) (hs₀ : 0 < s₀) (hm : (m : ℝ) ≤ γ * B) (hn : (n : ℝ) ≤ γ * B)
    (hCo : opNorm C.Sout ≤ CSig) (hCi : opNorm C.Sin ≤ CSig)
    (F : Mat m m) (G : Mat n n) (hF : opNorm F ≤ 1) (hG : opNorm G ≤ 1) {s u : ℝ}
    (hs : s₀ ≤ s) (hu : s₀ ≤ u) (K H : Mat m n) (α β e : ℝ) (hα0 : 0 ≤ α) (hα1 : α ≤ 1)
    (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) (p : Vec m × Vec n) :
    ‖(B : ℂ) * ((contractionRes B F G s u (K + (α * e) • outer (momU C B p) (momV C B p))
          (H + (β * e) • outer (momU C B p) (momV C B p)) - contractionRes B F G s u K H : ℝ) : ℂ) -
      ((max α β : ℝ) : ℂ) * psiF (parOf C B F G K H s u α β) e‖ ≤
      2 * (α + β) * |e| * (LcOf γ CSig s₀ * ((1 + |e|) *
          (1 + (∑ i, momU C B p i ^ 2 + ∑ j, momV C B p j ^ 2)))) ^ 7 *
        (n2 (Dm C B (cP K s) p) + n2 (Dm C B (cP H u) p) +
          n2 (Dm C B (cP K s * DGm G * cP H u * DFm F * cP K s) p) +
          n2 (Dm C B (cP H u * DFm F * cP K s * DGm G * cP H u) p) +
          n2 (Dm C B (cP K s * DGm G * cP H u) p) + n2 (Dm C B (cP H u * DFm F * cP K s) p)) := by
  have hs0 : 0 < s := lt_of_lt_of_le hs₀ hs
  have hu0 : 0 < u := lt_of_lt_of_le hs₀ hu
  have hC0 : 0 ≤ CSig := (vrp_opNorm_nonneg _).trans hCo
  obtain ⟨hL1, hL2, hL3, hL4, hL5, hL6⟩ := LcOf_ge hγ hC0 s₀
  have hLc1 : 1 ≤ LcOf γ CSig s₀ := LcOf_one_le hγ hC0 s₀
  have hκ0 := kapOf_nonneg s₀
  have hLc0 : 0 ≤ LcOf γ CSig s₀ := by linarith
  have hP : OB (cP K s) (kapOf s₀) := OB_cP_mono K hs₀ hs
  have hQ : OB (cP H u) (kapOf s₀) := OB_cP_mono H hs₀ hu
  have hDF : OB (DFm (n := n) F) 1 := OB_DF F hF
  have hDG : OB (DGm (m := m) G) 1 := OB_DG G hG
  have hMA : OB (cP K s * DGm G * cP H u * DFm F * cP K s) (kapOf s₀ * 1 * kapOf s₀ * 1 * kapOf s₀) :=
    OB_mul (by positivity) (OB_mul (by positivity) (OB_mul (by positivity)
      (OB_mul hκ0 hP hDG) hQ) hDF) hP
  have hMB : OB (cP H u * DFm F * cP K s * DGm G * cP H u) (kapOf s₀ * 1 * kapOf s₀ * 1 * kapOf s₀) :=
    OB_mul (by positivity) (OB_mul (by positivity) (OB_mul (by positivity)
      (OB_mul hκ0 hQ hDF) hP) hDG) hQ
  have hME : OB (cP K s * DGm G * cP H u) (kapOf s₀ * 1 * kapOf s₀) :=
    OB_mul (by positivity) (OB_mul hκ0 hP hDG) hQ
  have hMT : OB (cP H u * DFm F * cP K s) (kapOf s₀ * 1 * kapOf s₀) :=
    OB_mul (by positivity) (OB_mul hκ0 hQ hDF) hP
  set x : Vec m := momU C B p with hx
  set y : Vec n := momV C B p with hy
  set N : ℝ := (∑ i, x i ^ 2) + ∑ j, y j ^ 2 with hN
  have hN0 : 0 ≤ N := by
    have : 0 ≤ ∑ i, x i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
    have : 0 ≤ ∑ j, y j ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
    linarith
  set Lc := LcOf γ CSig s₀ with hLc
  set κ := kapOf s₀ with hκ
  have hcle : |α * e| ≤ |e| := by
    rw [abs_mul, abs_of_nonneg hα0]; exact mul_le_of_le_one_left (abs_nonneg _) hα1
  have hc'le : |β * e| ≤ |e| := by
    rw [abs_mul, abs_of_nonneg hβ0]; exact mul_le_of_le_one_left (abs_nonneg _) hβ1
  obtain ⟨q1, q2, q3, q4⟩ := ineq_q e N hN0
  have hℓ1 : 1 ≤ Lc * ((1 + |e|) * (1 + N)) := by nlinarith
  have hcℓ : |α * e| ≤ Lc * ((1 + |e|) * (1 + N)) := by nlinarith [abs_nonneg e]
  have hc'ℓ : |β * e| ≤ Lc * ((1 + |e|) * (1 + N)) := by nlinarith [abs_nonneg e]
  -- bounds
  have hC1 := bnd_C K x y hs₀ hs (α * e) e Lc hcle hL1
  have hC1' := bnd_C H x y hs₀ hu (β * e) e Lc hc'le hL1
  have hCb1 := bnd_Cb C B hB K hs₀ hs γ CSig hγ hm hn hCo hCi (α * e) e Lc N hN0 hcle hL2
    (by linarith)
  have hCb1' := bnd_Cb C B hB H hs₀ hu γ CSig hγ hm hn hCo hCi (β * e) e Lc N hN0 hc'le hL2
    (by linarith)
  have hk3 : 0 ≤ κ * 1 * κ * 1 * κ := by positivity
  have hk2 : 0 ≤ κ * 1 * κ := by positivity
  have e3 : κ * 1 * κ * 1 * κ = κ ^ 3 := by ring
  have e2 : κ * 1 * κ = κ ^ 2 := by ring
  have hA1 := bnd_comp _ _ hk3 hMA x y Lc e hLc0 (by rw [e3]; exact hL3)
  have hB1 := bnd_comp _ _ hk3 hMB x y Lc e hLc0 (by rw [e3]; exact hL3)
  have hE1 := bnd_comp _ _ hk2 hME x y Lc e hLc0 (by rw [e2]; exact hL5)
  have hT1 := bnd_comp _ _ hk2 hMT x y Lc e hLc0 (by rw [e2]; exact hL5)
  have hAb := bnd_mm C B hB γ CSig _ hγ hk3 hm hn hCo hCi _ hMA Lc N e hLc0 hN0 (by rw [e3]; exact hL4)
  have hBb := bnd_mm C B hB γ CSig _ hγ hk3 hm hn hCo hCi _ hMB Lc N e hLc0 hN0 (by rw [e3]; exact hL4)
  have hEb := bnd_mm C B hB γ CSig _ hγ hk2 hm hn hCo hCi _ hME Lc N e hLc0 hN0 (by rw [e2]; exact hL6)
  have hTb := bnd_mm C B hB γ CSig _ hγ hk2 hm hn hCo hCi _ hMT Lc N e hLc0 hN0 (by rw [e2]; exact hL6)
  -- exact increment and the Woodbury relations
  have inc := increment_exact B hB F G hs0 hu0 K H (α * e) (β * e) x y
  obtain ⟨-, -, hCrel, -⟩ := cP_woodbury K (α * e) x y hs0
  obtain ⟨-, -, hCrel', -⟩ := cP_woodbury H (β * e) x y hu0
  have hWb : mmOf C B (cP K s) = Wd (Complex.I * (chiO C B K s : ℂ)) (Complex.I * (chiI C B K s : ℂ)) := by
    rw [mmOf_cP]; rfl
  have hVb : mmOf C B (cP H u) = Wd (Complex.I * (chiO C B H u : ℂ)) (Complex.I * (chiI C B H u : ℂ)) := by
    rw [mmOf_cP]; rfl
  have hbr := Cbar_rel (α * e) (chiO C B K s) (chiI C B K s) (chiO_nonneg C B K hs0) (chiI_nonneg C B K hs0)
  have hbr' := Cbar_rel (β * e) (chiO C B H u) (chiI C B H u) (chiO_nonneg C B H hu0) (chiI_nonneg C B H hu0)
  rw [← hWb] at hbr
  rw [← hVb] at hbr'
  have hCd := tele_C ((α * e : ℝ) : ℂ) _ _ _ _ hCrel hbr
  have hCd' := tele_C ((β * e : ℝ) : ℂ) _ _ _ _ hCrel' hbr'
  have key := phi_err (α * e) (β * e) (Lc * ((1 + |e|) * (1 + N))) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    hCd hCd' hℓ1 hcℓ hc'ℓ hC1 hCb1 hC1' hCb1' hA1 hAb hB1 hBb hE1 hEb hT1 hTb
  have ident : ((max α β : ℝ) : ℂ) * psiF (parOf C B F G K H s u α β) e =
      -Matrix.trace (Cbar (α * e) (chiO C B K s) (chiI C B K s) * mmOf C B (cP K s * DGm G * cP H u * DFm F * cP K s)) -
        Matrix.trace (Cbar (β * e) (chiO C B H u) (chiI C B H u) * mmOf C B (cP H u * DFm F * cP K s * DGm G * cP H u)) +
        Matrix.trace (Cbar (α * e) (chiO C B K s) (chiI C B K s) * mmOf C B (cP K s * DGm G * cP H u) *
          Cbar (β * e) (chiO C B H u) (chiI C B H u) * mmOf C B (cP H u * DFm F * cP K s)) := by
    have h := psi_ident (max α β) (if max α β = 0 then 0 else α / max α β)
      (if max α β = 0 then 0 else β / max α β) (α * e) (β * e) (chiO C B K s) (chiI C B K s)
      (chiO C B H u) (chiI C B H u) e
      (mmOf C B (cP K s * DGm G * cP H u * DFm F * cP K s) 0 0)
      (mmOf C B (cP K s * DGm G * cP H u * DFm F * cP K s) 1 1)
      (mmOf C B (cP H u * DFm F * cP K s * DGm G * cP H u) 0 0)
      (mmOf C B (cP H u * DFm F * cP K s * DGm G * cP H u) 1 1)
      (mmOf C B (cP K s * DGm G * cP H u) 0 0) (mmOf C B (cP K s * DGm G * cP H u) 1 1)
      (mmOf C B (cP H u * DFm F * cP K s) 0 0) (mmOf C B (cP H u * DFm F * cP K s) 1 1)
      (rho_ident α β e hα0 hβ0) (rho_ident' α β e hα0 hβ0)
    rw [← mmOf_diag C B (cP K s * DGm G * cP H u * DFm F * cP K s),
      ← mmOf_diag C B (cP H u * DFm F * cP K s * DGm G * cP H u),
      ← mmOf_diag C B (cP K s * DGm G * cP H u), ← mmOf_diag C B (cP H u * DFm F * cP K s)] at h
    exact h
  rw [inc, ident]
  exact key.trans (le_of_eq (fin_eq α β e _ _ hα0 hβ0))


/-! ### Moments and a Cauchy–Schwarz inequality -/

private lemma vrp_cs_int {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (f g : Ω → ℝ) (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ)
    (hf0 : ∀ ω, 0 ≤ f ω) (hg0 : ∀ ω, 0 ≤ g ω)
    (hfi : Integrable (fun ω => f ω ^ 2) μ) (hgi : Integrable (fun ω => g ω ^ 2) μ)
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hfa : ∫ ω, f ω ^ 2 ∂μ ≤ a ^ 2) (hgb : ∫ ω, g ω ^ 2 ∂μ ≤ b ^ 2) :
    Integrable (fun ω => f ω * g ω) μ ∧ ∫ ω, f ω * g ω ∂μ ≤ a * b := by
  have hint : Integrable (fun ω => f ω * g ω) μ := by
    refine Integrable.mono' ((hfi.add hgi).const_mul (1 / 2)) (hf.mul hg) (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hf0 ω) (hg0 ω))]
    simp only [Pi.add_apply]
    nlinarith [sq_nonneg (f ω - g ω)]
  refine ⟨hint, ?_⟩
  -- for every t > 0:  ∫ f g ≤ (t a² + b²/t)/2
  have key : ∀ t : ℝ, 0 < t → ∫ ω, f ω * g ω ∂μ ≤ (t * a ^ 2 + b ^ 2 / t) / 2 := by
    intro t ht
    have hpt : ∀ ω, f ω * g ω ≤ (t * f ω ^ 2 + g ω ^ 2 / t) / 2 := by
      intro ω
      have : 0 ≤ (Real.sqrt t * f ω - g ω / Real.sqrt t) ^ 2 := sq_nonneg _
      have hs : Real.sqrt t ^ 2 = t := Real.sq_sqrt ht.le
      have hpos : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht
      have e : (Real.sqrt t * f ω - g ω / Real.sqrt t) ^ 2 = t * f ω ^ 2 + g ω ^ 2 / t - 2 * (f ω * g ω) := by
        field_simp; rw [hs]; ring
      linarith
    have hr : Integrable (fun ω => (t * f ω ^ 2 + g ω ^ 2 / t) / 2) μ :=
      ((hfi.const_mul t).add (hgi.div_const t)).div_const 2
    calc ∫ ω, f ω * g ω ∂μ ≤ ∫ ω, (t * f ω ^ 2 + g ω ^ 2 / t) / 2 ∂μ := integral_mono hint hr hpt
      _ = (t * ∫ ω, f ω ^ 2 ∂μ + (∫ ω, g ω ^ 2 ∂μ) / t) / 2 := by
          rw [integral_div, integral_add (hfi.const_mul t) (hgi.div_const t), integral_const_mul, integral_div]
      _ ≤ (t * a ^ 2 + b ^ 2 / t) / 2 := by
          gcongr
  -- optimize in t
  have hbound : ∀ η : ℝ, 0 < η → ∫ ω, f ω * g ω ∂μ ≤ (a + η) * (b + η) := by
    intro η hη
    have hab : 0 < (a + η) := by linarith
    have := key ((b + η) / (a + η)) (div_pos (by linarith) hab)
    have hbη : 0 < b + η := by linarith
    have e1 : ((b + η) / (a + η)) * a ^ 2 ≤ ((b + η) / (a + η)) * (a + η) ^ 2 :=
      mul_le_mul_of_nonneg_left (by nlinarith) (by positivity)
    have e2 : b ^ 2 / ((b + η) / (a + η)) ≤ (b + η) ^ 2 / ((b + η) / (a + η)) :=
      div_le_div_of_nonneg_right (by nlinarith) (by positivity)
    have e3 : ((b + η) / (a + η)) * (a + η) ^ 2 = (a + η) * (b + η) := by field_simp
    have e4 : (b + η) ^ 2 / ((b + η) / (a + η)) = (a + η) * (b + η) := by field_simp
    linarith
  have hlim : Tendsto (fun η : ℝ => (a + η) * (b + η)) (𝓝[>] 0) (𝓝 (a * b)) := by
    have : Continuous (fun η : ℝ => (a + η) * (b + η)) := by fun_prop
    have h0 := this.tendsto 0
    simp only [add_zero] at h0
    exact h0.mono_left nhdsWithin_le_nhds
  exact ge_of_tendsto hlim (eventually_nhdsWithin_of_forall fun η hη => hbound η hη)


private lemma vrp_mulVec_sq {a b : ℕ} (L : Mat a b) {c : ℝ} (hc : opNorm L ≤ c) (u : Vec b) :
    ∑ i, (L *ᵥ u) i ^ 2 ≤ c ^ 2 * ∑ j, u j ^ 2 := by
  have h2 : ‖Matrix.toEuclideanLin L (WithLp.toLp 2 u)‖ ≤ opNorm L * ‖WithLp.toLp 2 u‖ := by
    have := (LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin L)).le_opNorm (WithLp.toLp 2 u)
    simpa [opNorm] using this
  have hn : ∀ v : Fin b → ℝ, ‖WithLp.toLp 2 v‖ ^ 2 = ∑ i, v i ^ 2 := by
    intro v
    rw [EuclideanSpace.norm_sq_eq]
    simp [Real.norm_eq_abs, sq_abs]
  have hm : ∀ v : Fin a → ℝ, ‖WithLp.toLp 2 v‖ ^ 2 = ∑ i, v i ^ 2 := by
    intro v
    rw [EuclideanSpace.norm_sq_eq]
    simp [Real.norm_eq_abs, sq_abs]
  have h3 : ‖Matrix.toEuclideanLin L (WithLp.toLp 2 u)‖ ≤ c * ‖WithLp.toLp 2 u‖ :=
    h2.trans (mul_le_mul_of_nonneg_right hc (norm_nonneg _))
  have h4 : Matrix.toEuclideanLin L (WithLp.toLp 2 u) = WithLp.toLp 2 (L *ᵥ u) := by
    simp [Matrix.toEuclideanLin, Matrix.toLpLin_toLp]
  rw [h4] at h3
  have := pow_le_pow_left₀ (norm_nonneg _) h3 2
  rw [hm, mul_pow, hn] at this
  exact this

private def NN {m n : ℕ} (C : Covariances m n) (B : ℕ) (p : Vec m × Vec n) : ℝ :=
  ∑ i, momU C B p i ^ 2 + ∑ j, momV C B p j ^ 2

private lemma NN_nonneg {m n : ℕ} (C : Covariances m n) (B : ℕ) (p : Vec m × Vec n) : 0 ≤ NN C B p := by
  unfold NN
  have : 0 ≤ ∑ i, momU C B p i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  have : 0 ≤ ∑ j, momV C B p j ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  linarith

private lemma NN_le {m n : ℕ} (C : Covariances m n) (B : ℕ) (hB : 0 < B) {CSig : ℝ}
    (hCo : opNorm C.Sout ≤ CSig) (hCi : opNorm C.Sin ≤ CSig) (p : Vec m × Vec n) :
    NN C B p ≤ CSig / B * ((∑ i, p.1 i ^ 2) + ∑ j, p.2 j ^ 2) := by
  have hBr : (0 : ℝ) < B := by exact_mod_cast hB
  have hC0 : 0 ≤ CSig := (vrp_opNorm_nonneg _).trans hCo
  have hs : (Real.sqrt (B : ℝ))⁻¹ ^ 2 = (B : ℝ)⁻¹ := by rw [inv_pow, Real.sq_sqrt hBr.le]
  have h1 := vrp_mulVec_sq (rOut C) (vrp_rOut_opNorm C hCo) p.1
  have h2 := vrp_mulVec_sq (rIn C) (vrp_rIn_opNorm C hCi) p.2
  have hq : Real.sqrt CSig ^ 2 = CSig := Real.sq_sqrt hC0
  have e1 : ∑ i, momU C B p i ^ 2 = (B : ℝ)⁻¹ * ∑ i, ((rOut C) *ᵥ p.1) i ^ 2 := by
    simp only [momU, Pi.smul_apply, smul_eq_mul, mul_pow, hs, Finset.mul_sum]
  have e2 : ∑ j, momV C B p j ^ 2 = (B : ℝ)⁻¹ * ∑ j, ((rIn C) *ᵥ p.2) j ^ 2 := by
    simp only [momV, Pi.smul_apply, smul_eq_mul, mul_pow, hs, Finset.mul_sum]
  unfold NN
  rw [hq] at h1 h2
  rw [e1, e2]
  have hBi : 0 ≤ (B : ℝ)⁻¹ := by positivity
  calc (B : ℝ)⁻¹ * ∑ i, ((rOut C) *ᵥ p.1) i ^ 2 + (B : ℝ)⁻¹ * ∑ j, ((rIn C) *ᵥ p.2) j ^ 2
      ≤ (B : ℝ)⁻¹ * (CSig * ∑ i, p.1 i ^ 2) + (B : ℝ)⁻¹ * (CSig * ∑ j, p.2 j ^ 2) :=
        add_le_add (mul_le_mul_of_nonneg_left h1 hBi) (mul_le_mul_of_nonneg_left h2 hBi)
    _ = CSig / B * ((∑ i, p.1 i ^ 2) + ∑ j, p.2 j ^ 2) := by field_simp


private lemma NN_cont {m n : ℕ} (C : Covariances m n) (B : ℕ) : Continuous (NN C B) := by
  unfold NN momU momV
  fun_prop

private lemma vrp_sqnorm_moment_le (k q : ℕ) (hq : 1 ≤ q) (K : ℝ) (hK : (k : ℝ) + 2 * q ≤ K) :
    ∫ z : Vec k, (∑ i, z i ^ 2) ^ q ∂(Muon.Foundations.stdGaussianPi k) ≤ K ^ q := by
  rw [Muon.Foundations.stdGaussianPi_sq_norm_moment k q hq]
  calc ∏ j ∈ Finset.range q, ((k : ℝ) + 2 * j) ≤ ∏ _j ∈ Finset.range q, K := by
        gcongr with j hj
        have : (j : ℝ) ≤ q := by exact_mod_cast (Finset.mem_range.1 hj).le
        linarith
    _ = K ^ q := by simp

private lemma NN_moment {m n : ℕ} (C : Covariances m n) (B : ℕ) (hB : 0 < B) (γ CSig : ℝ)
    (hγ : 0 ≤ γ) (hm : (m : ℝ) ≤ γ * B) (hn : (n : ℝ) ≤ γ * B)
    (hCo : opNorm C.Sout ≤ CSig) (hCi : opNorm C.Sin ≤ CSig) (q : ℕ) (hq : 1 ≤ q) :
    Integrable (fun p : Vec m × Vec n => NN C B p ^ q) (gaussPair m n) ∧
    ∫ p : Vec m × Vec n, NN C B p ^ q ∂(gaussPair m n) ≤ 2 * (2 * CSig * (γ + 2 * q)) ^ q := by
  have hBr : (1 : ℝ) ≤ B := by exact_mod_cast hB
  have hC0 : 0 ≤ CSig := (vrp_opNorm_nonneg _).trans hCo
  set a : Vec m × Vec n → ℝ := fun p => ∑ i, p.1 i ^ 2 with ha
  set b : Vec m × Vec n → ℝ := fun p => ∑ j, p.2 j ^ 2 with hb
  have ha0 : ∀ p, 0 ≤ a p := fun p => Finset.sum_nonneg fun i _ => sq_nonneg _
  have hb0 : ∀ p, 0 ≤ b p := fun p => Finset.sum_nonneg fun i _ => sq_nonneg _
  have hia : Integrable (fun p => a p ^ q) (gaussPair m n) :=
    ((vrp_int_fst (n := n) (fun z : Vec m => (∑ i, z i ^ 2) ^ q) (vsw_sqpow m q).aestronglyMeasurable).1).2 (vsw_sqpow m q)
  have hib : Integrable (fun p => b p ^ q) (gaussPair m n) :=
    ((vrp_int_snd (m := m) (fun z : Vec n => (∑ i, z i ^ 2) ^ q) (vsw_sqpow n q).aestronglyMeasurable).1).2 (vsw_sqpow n q)
  have hea : ∫ p, a p ^ q ∂(gaussPair m n) ≤ (B * (γ + 2 * q)) ^ q := by
    have := (vrp_int_fst (n := n) (fun z : Vec m => (∑ i, z i ^ 2) ^ q) (vsw_sqpow m q).aestronglyMeasurable).2
    simp only [ha]
    rw [this]
    refine vrp_sqnorm_moment_le m q hq _ ?_
    nlinarith [(by exact_mod_cast hq : (1:ℝ) ≤ q)]
  have heb : ∫ p, b p ^ q ∂(gaussPair m n) ≤ (B * (γ + 2 * q)) ^ q := by
    have := (vrp_int_snd (m := m) (fun z : Vec n => (∑ i, z i ^ 2) ^ q) (vsw_sqpow n q).aestronglyMeasurable).2
    simp only [hb]
    rw [this]
    refine vrp_sqnorm_moment_le n q hq _ ?_
    nlinarith [(by exact_mod_cast hq : (1:ℝ) ≤ q)]
  -- pointwise
  have hpt : ∀ p, NN C B p ^ q ≤ (CSig / B) ^ q * 2 ^ q * (a p ^ q + b p ^ q) := by
    intro p
    have h1 := NN_le C B hB hCo hCi p
    have h2 : NN C B p ^ q ≤ (CSig / B * (a p + b p)) ^ q :=
      pow_le_pow_left₀ (NN_nonneg C B p) h1 q
    have h3 : (a p + b p) ^ q ≤ 2 ^ q * (a p ^ q + b p ^ q) := by
      have hm : a p + b p ≤ 2 * max (a p) (b p) := by
        have := le_max_left (a p) (b p); have := le_max_right (a p) (b p); linarith
      have hmax : max (a p) (b p) ^ q ≤ a p ^ q + b p ^ q := by
        rcases le_total (a p) (b p) with h | h
        · rw [max_eq_right h]; have := pow_nonneg (ha0 p) q; linarith
        · rw [max_eq_left h]; have := pow_nonneg (hb0 p) q; linarith
      calc (a p + b p) ^ q ≤ (2 * max (a p) (b p)) ^ q :=
            pow_le_pow_left₀ (add_nonneg (ha0 p) (hb0 p)) hm q
        _ = 2 ^ q * max (a p) (b p) ^ q := mul_pow _ _ _
        _ ≤ 2 ^ q * (a p ^ q + b p ^ q) := mul_le_mul_of_nonneg_left hmax (by positivity)
    calc NN C B p ^ q ≤ (CSig / B * (a p + b p)) ^ q := h2
      _ = (CSig / B) ^ q * (a p + b p) ^ q := mul_pow _ _ _
      _ ≤ (CSig / B) ^ q * (2 ^ q * (a p ^ q + b p ^ q)) :=
          mul_le_mul_of_nonneg_left h3 (by positivity)
      _ = (CSig / B) ^ q * 2 ^ q * (a p ^ q + b p ^ q) := by ring
  have hsum : Integrable (fun p => (CSig / B) ^ q * 2 ^ q * (a p ^ q + b p ^ q)) (gaussPair m n) :=
    (hia.add hib).const_mul _
  have hmeas : Continuous (fun p : Vec m × Vec n => NN C B p ^ q) := (NN_cont C B).pow q
  have hint : Integrable (fun p : Vec m × Vec n => NN C B p ^ q) (gaussPair m n) := by
    refine hsum.mono' hmeas.aestronglyMeasurable (Filter.Eventually.of_forall fun p => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (NN_nonneg C B p) q)]
    exact hpt p
  refine ⟨hint, ?_⟩
  calc ∫ p, NN C B p ^ q ∂(gaussPair m n) ≤ ∫ p, (CSig / B) ^ q * 2 ^ q * (a p ^ q + b p ^ q) ∂(gaussPair m n) :=
        integral_mono hint hsum hpt
    _ = (CSig / B) ^ q * 2 ^ q * (∫ p, a p ^ q ∂(gaussPair m n) + ∫ p, b p ^ q ∂(gaussPair m n)) := by
        rw [integral_const_mul, integral_add hia hib]
    _ ≤ (CSig / B) ^ q * 2 ^ q * ((B * (γ + 2 * q)) ^ q + (B * (γ + 2 * q)) ^ q) := by
        gcongr
    _ = 2 * (2 * CSig * (γ + 2 * q)) ^ q := by
        have hB0 : (B : ℝ) ≠ 0 := by positivity
        have e : (2 * CSig * (γ + 2 * q)) ^ q = (CSig / B) ^ q * 2 ^ q * ((B : ℝ) * (γ + 2 * q)) ^ q := by
          rw [show 2 * CSig * (γ + 2 * q) = (CSig / B) * 2 * ((B : ℝ) * (γ + 2 * q)) by field_simp,
            mul_pow, mul_pow]
        rw [e]
        ring


private lemma vrp_mu_fst {m n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] (f : ℝ → E) (hf : AEStronglyMeasurable f (gaussianReal 0 1)) :
    (Integrable (fun x : ℝ × (Vec m × Vec n) => f x.1) (indepSlotLaw m n) ↔ Integrable f (gaussianReal 0 1)) ∧
    ∫ x : ℝ × (Vec m × Vec n), f x.1 ∂(indepSlotLaw m n) = ∫ y, f y ∂(gaussianReal 0 1) := by
  have hmp : MeasurePreserving (Prod.fst : ℝ × (Vec m × Vec n) → ℝ) (indepSlotLaw m n) (gaussianReal 0 1) :=
    measurePreserving_fst
  refine ⟨hmp.integrable_comp hf, ?_⟩
  rw [← hmp.map_eq, integral_map measurable_fst.aemeasurable (by rw [hmp.map_eq]; exact hf)]

private lemma vrp_mu_snd {m n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] (f : Vec m × Vec n → E) (hf : AEStronglyMeasurable f (gaussPair m n)) :
    (Integrable (fun x : ℝ × (Vec m × Vec n) => f x.2) (indepSlotLaw m n) ↔ Integrable f (gaussPair m n)) ∧
    ∫ x : ℝ × (Vec m × Vec n), f x.2 ∂(indepSlotLaw m n) = ∫ y, f y ∂(gaussPair m n) := by
  have hmp : MeasurePreserving (Prod.snd : ℝ × (Vec m × Vec n) → Vec m × Vec n) (indepSlotLaw m n)
      (gaussPair m n) := measurePreserving_snd
  refine ⟨hmp.integrable_comp hf, ?_⟩
  rw [← hmp.map_eq, integral_map measurable_snd.aemeasurable (by rw [hmp.map_eq]; exact hf)]

private lemma vrp_pow32 (t : ℝ) (ht : 0 ≤ t) : (1 + t) ^ 32 ≤ 2 ^ 32 * (1 + t ^ 32) := by
  have hm : 1 + t ≤ 2 * max 1 t := by
    have := le_max_left 1 t; have := le_max_right 1 t; linarith
  have hmax : max 1 t ^ 32 ≤ 1 + t ^ 32 := by
    rcases le_total 1 t with h | h
    · rw [max_eq_right h]; linarith
    · rw [max_eq_left h]; have := pow_nonneg ht 32; simp; linarith
  calc (1 + t) ^ 32 ≤ (2 * max 1 t) ^ 32 := pow_le_pow_left₀ (by linarith) hm 32
    _ = 2 ^ 32 * max 1 t ^ 32 := mul_pow _ _ _
    _ ≤ 2 ^ 32 * (1 + t ^ 32) := mul_le_mul_of_nonneg_left hmax (by positivity)

private lemma vrp_resid_pow_int {m n : ℕ} (A : Mat m n) (hA : fro A = 1) (q : ℕ) :
    Integrable (fun p : Vec m × Vec n => |resid A p| ^ (2 * q)) (gaussPair m n) := by
  have hF : ∑ i, ∑ j, ‖A i j‖ ^ 2 = 1 := by
    have := hA
    unfold fro at this
    rwa [Real.sqrt_eq_one] at this
  have hint := (vsw_sqpow m q).mul_prod (vsw_sqpow n q)
  unfold gaussPair
  refine hint.mono' (by unfold resid dotProduct Matrix.mulVec dotProduct; fun_prop :
    Measurable fun p : Vec m × Vec n => |resid A p| ^ (2 * q)).aestronglyMeasurable
    (Filter.Eventually.of_forall fun p => ?_)
  obtain ⟨z, w⟩ := p
  have hr2 : resid A (z, w) ^ 2 ≤ (∑ i, z i ^ 2) * ∑ j, w j ^ 2 := by
    have hrow : ∀ i, (A *ᵥ w) i ^ 2 ≤ (∑ j, A i j ^ 2) * ∑ j, w j ^ 2 := by
      intro i
      simp only [Matrix.mulVec, dotProduct]
      exact Finset.sum_mul_sq_le_sq_mul_sq _ _ _
    have hAw : ∑ i, (A *ᵥ w) i ^ 2 ≤ ∑ j, w j ^ 2 := by
      calc ∑ i, (A *ᵥ w) i ^ 2 ≤ ∑ i, (∑ j, A i j ^ 2) * ∑ j, w j ^ 2 :=
            Finset.sum_le_sum fun i _ => hrow i
        _ = (∑ i, ∑ j, A i j ^ 2) * ∑ j, w j ^ 2 := by rw [Finset.sum_mul]
        _ = ∑ j, w j ^ 2 := by
            have : ∑ i, ∑ j, A i j ^ 2 = 1 := by simpa using hF
            rw [this, one_mul]
    have h1 : resid A (z, w) ^ 2 ≤ (∑ i, z i ^ 2) * ∑ i, (A *ᵥ w) i ^ 2 := by
      unfold resid dotProduct
      exact Finset.sum_mul_sq_le_sq_mul_sq _ _ _
    have h0 : 0 ≤ ∑ i, z i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
    exact h1.trans (mul_le_mul_of_nonneg_left hAw h0)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  simp only
  calc |resid A (z, w)| ^ (2 * q) = (resid A (z, w) ^ 2) ^ q := by rw [pow_mul, sq_abs]
    _ ≤ ((∑ i, z i ^ 2) * ∑ j, w j ^ 2) ^ q := pow_le_pow_left₀ (sq_nonneg _) hr2 q
    _ = _ := by rw [mul_pow]

private lemma resid_moment32 {m n : ℕ} (A : Mat m n) (hA : fro A = 1) :
    Integrable (fun p : Vec m × Vec n => (1 + |resid A p|) ^ 32) (gaussPair m n) ∧
    ∫ p : Vec m × Vec n, (1 + |resid A p|) ^ 32 ∂(gaussPair m n) ≤
      2 ^ 32 * (1 + ((Nat.doubleFactorial (2 * 16 - 1) : ℕ) : ℝ) ^ 2) := by
  have hi := vrp_resid_pow_int A hA 16
  have hmeas : Measurable fun p : Vec m × Vec n => (1 + |resid A p|) ^ 32 := by
    have := vrp_resid_cont A; fun_prop
  have hdom : Integrable (fun p : Vec m × Vec n => 2 ^ 32 * (1 + |resid A p| ^ (2 * 16))) (gaussPair m n) :=
    ((integrable_const (1 : ℝ)).add hi).const_mul _
  have hpt : ∀ p : Vec m × Vec n, (1 + |resid A p|) ^ 32 ≤ 2 ^ 32 * (1 + |resid A p| ^ (2 * 16)) :=
    fun p => by simpa using vrp_pow32 _ (abs_nonneg (resid A p))
  have hint : Integrable (fun p : Vec m × Vec n => (1 + |resid A p|) ^ 32) (gaussPair m n) := by
    refine hdom.mono' hmeas.aestronglyMeasurable (Filter.Eventually.of_forall fun p => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact hpt p
  refine ⟨hint, ?_⟩
  have hm := (lem_app_setup_residual_i A hA).2.2.2.2 16 (by norm_num)
  calc ∫ p, (1 + |resid A p|) ^ 32 ∂(gaussPair m n) ≤ ∫ p, 2 ^ 32 * (1 + |resid A p| ^ (2 * 16)) ∂(gaussPair m n) :=
        integral_mono hint hdom hpt
    _ = 2 ^ 32 * (1 + ∫ p, |resid A p| ^ (2 * 16) ∂(gaussPair m n)) := by
        rw [integral_const_mul, integral_add (integrable_const 1) hi]; simp
    _ ≤ 2 ^ 32 * (1 + ((Nat.doubleFactorial (2 * 16 - 1) : ℕ) : ℝ) ^ 2) := by gcongr

private lemma gauss_moment32 :
    Integrable (fun y : ℝ => (1 + |y|) ^ 32) (gaussianReal 0 1) := by
  have hi := Muon.Foundations.gaussian_integrable_pow 32
  have hdom : Integrable (fun y : ℝ => 2 ^ 32 * (1 + |y| ^ 32)) (gaussianReal 0 1) := by
    have : Integrable (fun y : ℝ => |y| ^ 32) (gaussianReal 0 1) := by
      simpa [Even.pow_abs ⟨16, rfl⟩] using hi
    exact ((integrable_const (1 : ℝ)).add this).const_mul _
  refine hdom.mono' (by fun_prop : Measurable fun y : ℝ => (1 + |y|) ^ 32).aestronglyMeasurable
    (Filter.Eventually.of_forall fun y => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact vrp_pow32 _ (abs_nonneg y)


/-! ### The one-sample estimate -/

private def Ysum {m n : ℕ} (C : Covariances m n) (B : ℕ) (F : Mat m m) (G : Mat n n) (K H : Mat m n)
    (s u : ℝ) (p : Vec m × Vec n) : ℝ :=
  n2 (Dm C B (cP K s) p) + n2 (Dm C B (cP H u) p) +
    n2 (Dm C B (cP K s * DGm G * cP H u * DFm F * cP K s) p) +
    n2 (Dm C B (cP H u * DFm F * cP K s * DGm G * cP H u) p) +
    n2 (Dm C B (cP K s * DGm G * cP H u) p) + n2 (Dm C B (cP H u * DFm F * cP K s) p)

private lemma Ysum_nonneg {m n : ℕ} (C : Covariances m n) (B : ℕ) (F : Mat m m) (G : Mat n n) (K H : Mat m n)
    (s u : ℝ) (p : Vec m × Vec n) : 0 ≤ Ysum C B F G K H s u p := by
  unfold Ysum
  have := fun M : CMat m n => n2_nonneg (Dm C B M p)
  have h1 := this (cP K s)
  have h2 := this (cP H u)
  have h3 := this (cP K s * DGm G * cP H u * DFm F * cP K s)
  have h4 := this (cP H u * DFm F * cP K s * DGm G * cP H u)
  have h5 := this (cP K s * DGm G * cP H u)
  have h6 := this (cP H u * DFm F * cP K s)
  linarith

private lemma Ysum_cont {m n : ℕ} (C : Covariances m n) (B : ℕ) (F : Mat m m) (G : Mat n n) (K H : Mat m n)
    (s u : ℝ) : Continuous (Ysum C B F G K H s u) := by
  unfold Ysum
  have := fun M : CMat m n => n2_cont (Dm_cont C B M)
  exact (((((this _).add (this _)).add (this _)).add (this _)).add (this _)).add (this _)

private lemma six_sq {α : Type*} [MeasurableSpace α] (μ : Measure α) (f1 f2 f3 f4 f5 f6 : α → ℝ)
    (m1 : Measurable f1) (m2 : Measurable f2) (m3 : Measurable f3) (m4 : Measurable f4)
    (m5 : Measurable f5) (m6 : Measurable f6) (b : ℝ)
    (i1 : Integrable (fun p => f1 p ^ 2) μ) (i2 : Integrable (fun p => f2 p ^ 2) μ)
    (i3 : Integrable (fun p => f3 p ^ 2) μ) (i4 : Integrable (fun p => f4 p ^ 2) μ)
    (i5 : Integrable (fun p => f5 p ^ 2) μ) (i6 : Integrable (fun p => f6 p ^ 2) μ)
    (j1 : ∫ p, f1 p ^ 2 ∂μ ≤ b) (j2 : ∫ p, f2 p ^ 2 ∂μ ≤ b) (j3 : ∫ p, f3 p ^ 2 ∂μ ≤ b)
    (j4 : ∫ p, f4 p ^ 2 ∂μ ≤ b) (j5 : ∫ p, f5 p ^ 2 ∂μ ≤ b) (j6 : ∫ p, f6 p ^ 2 ∂μ ≤ b) :
    Integrable (fun p => (f1 p + f2 p + f3 p + f4 p + f5 p + f6 p) ^ 2) μ ∧
    ∫ p, (f1 p + f2 p + f3 p + f4 p + f5 p + f6 p) ^ 2 ∂μ ≤ 36 * b := by
  have hpt : ∀ p, (f1 p + f2 p + f3 p + f4 p + f5 p + f6 p) ^ 2 ≤
      6 * (f1 p ^ 2 + f2 p ^ 2 + f3 p ^ 2 + f4 p ^ 2 + f5 p ^ 2 + f6 p ^ 2) := by
    intro p
    nlinarith [sq_nonneg (f1 p - f2 p), sq_nonneg (f1 p - f3 p), sq_nonneg (f1 p - f4 p),
      sq_nonneg (f1 p - f5 p), sq_nonneg (f1 p - f6 p), sq_nonneg (f2 p - f3 p), sq_nonneg (f2 p - f4 p),
      sq_nonneg (f2 p - f5 p), sq_nonneg (f2 p - f6 p), sq_nonneg (f3 p - f4 p), sq_nonneg (f3 p - f5 p),
      sq_nonneg (f3 p - f6 p), sq_nonneg (f4 p - f5 p), sq_nonneg (f4 p - f6 p), sq_nonneg (f5 p - f6 p)]
  have a12 : Integrable (fun p => f1 p ^ 2 + f2 p ^ 2) μ := i1.add i2
  have a123 : Integrable (fun p => f1 p ^ 2 + f2 p ^ 2 + f3 p ^ 2) μ := a12.add i3
  have a1234 : Integrable (fun p => f1 p ^ 2 + f2 p ^ 2 + f3 p ^ 2 + f4 p ^ 2) μ := a123.add i4
  have a12345 : Integrable (fun p => f1 p ^ 2 + f2 p ^ 2 + f3 p ^ 2 + f4 p ^ 2 + f5 p ^ 2) μ := a1234.add i5
  have a123456 : Integrable (fun p => f1 p ^ 2 + f2 p ^ 2 + f3 p ^ 2 + f4 p ^ 2 + f5 p ^ 2 + f6 p ^ 2) μ :=
    a12345.add i6
  have hsum := a123456.const_mul 6
  have hint : Integrable (fun p => (f1 p + f2 p + f3 p + f4 p + f5 p + f6 p) ^ 2) μ := by
    refine hsum.mono' ((((((m1.add m2).add m3).add m4).add m5).add m6).pow_const 2).aestronglyMeasurable
      (Filter.Eventually.of_forall fun p => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact hpt p
  refine ⟨hint, ?_⟩
  have h1 := integral_mono hint hsum hpt
  rw [integral_const_mul, integral_add a12345 i6, integral_add a1234 i5, integral_add a123 i4,
    integral_add a12 i3, integral_add i1 i2] at h1
  linarith

private lemma Ysum_sq {m n : ℕ} (C : Covariances m n) (B : ℕ) (hB : 0 < B) (γ CSig s₀ : ℝ)
    (hγ : 0 ≤ γ) (hs₀ : 0 < s₀) (hm : (m : ℝ) ≤ γ * B) (hn : (n : ℝ) ≤ γ * B)
    (hCo : opNorm C.Sout ≤ CSig) (hCi : opNorm C.Sin ≤ CSig)
    (F : Mat m m) (G : Mat n n) (hF : opNorm F ≤ 1) (hG : opNorm G ≤ 1) {s u : ℝ}
    (hs : s₀ ≤ s) (hu : s₀ ≤ u) (K H : Mat m n) :
    Integrable (fun p : Vec m × Vec n => Ysum C B F G K H s u p ^ 2) (gaussPair m n) ∧
    ∫ p : Vec m × Vec n, Ysum C B F G K H s u p ^ 2 ∂(gaussPair m n) ≤
      36 * (24 * γ * CSig ^ 2 * (kapOf s₀ + kapOf s₀ ^ 2 + kapOf s₀ ^ 3) ^ 2 / B) := by
  have hκ0 := kapOf_nonneg s₀
  set κ := kapOf s₀ with hκ
  have hP : OB (cP K s) κ := OB_cP_mono K hs₀ hs
  have hQ : OB (cP H u) κ := OB_cP_mono H hs₀ hu
  have hDF : OB (DFm (n := n) F) 1 := OB_DF F hF
  have hDG : OB (DGm (m := m) G) 1 := OB_DG G hG
  have hMA : OB (cP K s * DGm G * cP H u * DFm F * cP K s) (κ * 1 * κ * 1 * κ) :=
    OB_mul (by positivity) (OB_mul (by positivity) (OB_mul (by positivity)
      (OB_mul hκ0 hP hDG) hQ) hDF) hP
  have hMB : OB (cP H u * DFm F * cP K s * DGm G * cP H u) (κ * 1 * κ * 1 * κ) :=
    OB_mul (by positivity) (OB_mul (by positivity) (OB_mul (by positivity)
      (OB_mul hκ0 hQ hDF) hP) hDG) hQ
  have hME : OB (cP K s * DGm G * cP H u) (κ * 1 * κ) :=
    OB_mul (by positivity) (OB_mul hκ0 hP hDG) hQ
  have hMT : OB (cP H u * DFm F * cP K s) (κ * 1 * κ) :=
    OB_mul (by positivity) (OB_mul hκ0 hQ hDF) hP
  have comp := fun (M : CMat m n) (c : ℝ) (hc : 0 ≤ c) (hM : OB M c) =>
    vrp_compress C B hB γ CSig hγ hm hn hCo hCi M c hc hM
  obtain ⟨i1, j1⟩ := comp _ κ hκ0 hP
  obtain ⟨i2, j2⟩ := comp _ κ hκ0 hQ
  obtain ⟨i3, j3⟩ := comp _ _ (by positivity) hMA
  obtain ⟨i4, j4⟩ := comp _ _ (by positivity) hMB
  obtain ⟨i5, j5⟩ := comp _ _ (by positivity) hME
  obtain ⟨i6, j6⟩ := comp _ _ (by positivity) hMT
  have hBr : (0 : ℝ) < B := by exact_mod_cast hB
  have hC0 : 0 ≤ CSig := (vrp_opNorm_nonneg _).trans hCo
  have hcM0 : 0 ≤ κ + κ ^ 2 + κ ^ 3 := by positivity
  have bd : ∀ c : ℝ, 0 ≤ c → c ≤ κ + κ ^ 2 + κ ^ 3 →
      24 * γ * CSig ^ 2 * c ^ 2 / B ≤ 24 * γ * CSig ^ 2 * (κ + κ ^ 2 + κ ^ 3) ^ 2 / B := by
    intro c h0 h1
    have : c ^ 2 ≤ (κ + κ ^ 2 + κ ^ 3) ^ 2 := pow_le_pow_left₀ h0 h1 2
    gcongr
  have k1 : κ ≤ κ + κ ^ 2 + κ ^ 3 := by nlinarith [pow_nonneg hκ0 2, pow_nonneg hκ0 3]
  have k3 : κ * 1 * κ * 1 * κ ≤ κ + κ ^ 2 + κ ^ 3 := by
    have : κ * 1 * κ * 1 * κ = κ ^ 3 := by ring
    rw [this]; nlinarith [pow_nonneg hκ0 2, pow_nonneg hκ0 3]
  have k2 : κ * 1 * κ ≤ κ + κ ^ 2 + κ ^ 3 := by
    have : κ * 1 * κ = κ ^ 2 := by ring
    rw [this]; nlinarith [pow_nonneg hκ0 2, pow_nonneg hκ0 3]
  have := six_sq (gaussPair m n) (fun p => n2 (Dm C B (cP K s) p)) (fun p => n2 (Dm C B (cP H u) p))
    (fun p => n2 (Dm C B (cP K s * DGm G * cP H u * DFm F * cP K s) p))
    (fun p => n2 (Dm C B (cP H u * DFm F * cP K s * DGm G * cP H u) p))
    (fun p => n2 (Dm C B (cP K s * DGm G * cP H u) p)) (fun p => n2 (Dm C B (cP H u * DFm F * cP K s) p))
    (n2_cont (Dm_cont C B _)).measurable (n2_cont (Dm_cont C B _)).measurable (n2_cont (Dm_cont C B _)).measurable
    (n2_cont (Dm_cont C B _)).measurable (n2_cont (Dm_cont C B _)).measurable (n2_cont (Dm_cont C B _)).measurable
    (24 * γ * CSig ^ 2 * (κ + κ ^ 2 + κ ^ 3) ^ 2 / B) i1 i2 i3 i4 i5 i6
    (j1.trans (bd _ hκ0 k1)) (j2.trans (bd _ hκ0 k1)) (j3.trans (bd _ (by positivity) k3))
    (j4.trans (bd _ (by positivity) k3)) (j5.trans (bd _ (by positivity) k2)) (j6.trans (bd _ (by positivity) k2))
  exact this


private def KNof (γ CSig : ℝ) : ℝ := 2 ^ 32 * (1 + 2 * (2 * CSig * (γ + 2 * (32 : ℕ))) ^ 32)

private lemma NN_moment32 {m n : ℕ} (C : Covariances m n) (B : ℕ) (hB : 0 < B) (γ CSig : ℝ)
    (hγ : 0 ≤ γ) (hm : (m : ℝ) ≤ γ * B) (hn : (n : ℝ) ≤ γ * B)
    (hCo : opNorm C.Sout ≤ CSig) (hCi : opNorm C.Sin ≤ CSig) :
    Integrable (fun p : Vec m × Vec n => (1 + NN C B p) ^ 32) (gaussPair m n) ∧
    ∫ p : Vec m × Vec n, (1 + NN C B p) ^ 32 ∂(gaussPair m n) ≤ KNof γ CSig := by
  obtain ⟨hi, hv⟩ := NN_moment C B hB γ CSig hγ hm hn hCo hCi 32 (by norm_num)
  have hdom : Integrable (fun p : Vec m × Vec n => 2 ^ 32 * (1 + NN C B p ^ 32)) (gaussPair m n) :=
    ((integrable_const (1 : ℝ)).add hi).const_mul _
  have hpt : ∀ p : Vec m × Vec n, (1 + NN C B p) ^ 32 ≤ 2 ^ 32 * (1 + NN C B p ^ 32) :=
    fun p => vrp_pow32 _ (NN_nonneg C B p)
  have hint : Integrable (fun p : Vec m × Vec n => (1 + NN C B p) ^ 32) (gaussPair m n) := by
    refine hdom.mono' (((continuous_const.add (NN_cont C B)).pow 32).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun p => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (by have := NN_nonneg C B p; positivity)]
    exact hpt p
  refine ⟨hint, ?_⟩
  calc ∫ p, (1 + NN C B p) ^ 32 ∂(gaussPair m n) ≤ ∫ p, 2 ^ 32 * (1 + NN C B p ^ 32) ∂(gaussPair m n) :=
        integral_mono hint hdom hpt
    _ = 2 ^ 32 * (1 + ∫ p, NN C B p ^ 32 ∂(gaussPair m n)) := by
        rw [integral_const_mul, integral_add (integrable_const 1) hi]; simp
    _ ≤ KNof γ CSig := by
        unfold KNof
        have : ((32 : ℕ) : ℝ) = 32 := by norm_num
        gcongr


private lemma Bd_le (α β e N S Lc : ℝ) (hα : 0 ≤ α) (hβ : 0 ≤ β) (hLc : 0 ≤ Lc) (hN : 0 ≤ N) (hS : 0 ≤ S) :
    2 * (α + β) * |e| * (Lc * ((1 + |e|) * (1 + N))) ^ 7 * S ≤
      2 * (α + β) * Lc ^ 7 * (((1 + |e|) ^ 8 * (1 + N) ^ 8) * S) := by
  have he0 := abs_nonneg e
  have h1 : |e| * ((1 + |e|) ^ 7 * (1 + N) ^ 7) ≤ (1 + |e|) ^ 8 * (1 + N) ^ 8 := by
    have a : |e| ≤ 1 + |e| := by linarith
    have hX : 0 ≤ (1 + |e|) ^ 7 * (1 + N) ^ 7 := by positivity
    have b : 1 ≤ 1 + N := by linarith
    have c1 : |e| * ((1 + |e|) ^ 7 * (1 + N) ^ 7) ≤ (1 + |e|) * ((1 + |e|) ^ 7 * (1 + N) ^ 7) :=
      mul_le_mul_of_nonneg_right a hX
    have c2 : (1 + |e|) * ((1 + |e|) ^ 7 * (1 + N) ^ 7) ≤ (1 + |e|) * ((1 + |e|) ^ 7 * (1 + N) ^ 7) * (1 + N) := by
      have := mul_nonneg (by linarith : (0:ℝ) ≤ 1 + |e|) hX
      nlinarith
    have c3 : (1 + |e|) * ((1 + |e|) ^ 7 * (1 + N) ^ 7) * (1 + N) = (1 + |e|) ^ 8 * (1 + N) ^ 8 := by ring
    linarith
  have e1 : 2 * (α + β) * |e| * (Lc * ((1 + |e|) * (1 + N))) ^ 7 * S =
      2 * (α + β) * Lc ^ 7 * ((|e| * ((1 + |e|) ^ 7 * (1 + N) ^ 7)) * S) := by
    rw [mul_pow, mul_pow]; ring
  rw [e1]
  have hc : 0 ≤ 2 * (α + β) * Lc ^ 7 := by positivity
  exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h1 hS) hc

private lemma amgm2 (u v : ℝ) : u * v ≤ (1 / 2) * (u ^ 2 + v ^ 2) := by
  nlinarith [sq_nonneg (u - v)]

private lemma pi_sq_le (e N : ℝ) (he : 0 ≤ |e|) (hN : 0 ≤ N) :
    ((1 + |e|) ^ 8 * (1 + N) ^ 8) ^ 2 ≤ (1 / 2) * ((1 + |e|) ^ 32 + (1 + N) ^ 32) := by
  have a : ((1 + |e|) ^ 8 * (1 + N) ^ 8) ^ 2 = (1 + |e|) ^ 16 * (1 + N) ^ 16 := by
    rw [mul_pow, ← pow_mul, ← pow_mul]
  have b : (1 + |e|) ^ 32 = ((1 + |e|) ^ 16) ^ 2 := by rw [← pow_mul]
  have c : (1 + N) ^ 32 = ((1 + N) ^ 16) ^ 2 := by rw [← pow_mul]
  rw [a, b, c]
  exact amgm2 _ _


private lemma pi_moments {m n : ℕ} (C : Covariances m n) (B : ℕ) (hB : 0 < B) (γ CSig : ℝ)
    (hγ : 0 ≤ γ) (hm : (m : ℝ) ≤ γ * B) (hn : (n : ℝ) ≤ γ * B)
    (hCo : opNorm C.Sout ≤ CSig) (hCi : opNorm C.Sin ≤ CSig)
    (e : ℝ × (Vec m × Vec n) → ℝ) (he : Measurable e)
    (hEi : Integrable (fun x => (1 + |e x|) ^ 32) (indepSlotLaw m n)) (KE : ℝ)
    (hEv : ∫ x, (1 + |e x|) ^ 32 ∂(indepSlotLaw m n) ≤ KE) :
    Integrable (fun x : ℝ × (Vec m × Vec n) => ((1 + |e x|) ^ 8 * (1 + NN C B x.2) ^ 8) ^ 2) (indepSlotLaw m n) ∧
    ∫ x, ((1 + |e x|) ^ 8 * (1 + NN C B x.2) ^ 8) ^ 2 ∂(indepSlotLaw m n) ≤ (1 / 2) * (KE + KNof γ CSig) := by
  obtain ⟨hNi, hNv⟩ := NN_moment32 C B hB γ CSig hγ hm hn hCo hCi
  have hNi' : Integrable (fun x : ℝ × (Vec m × Vec n) => (1 + NN C B x.2) ^ 32) (indepSlotLaw m n) :=
    ((vrp_mu_snd (fun p => (1 + NN C B p) ^ 32) hNi.aestronglyMeasurable).1).2 hNi
  have hNv' : ∫ x : ℝ × (Vec m × Vec n), (1 + NN C B x.2) ^ 32 ∂(indepSlotLaw m n) ≤ KNof γ CSig := by
    rw [(vrp_mu_snd (fun p => (1 + NN C B p) ^ 32) hNi.aestronglyMeasurable).2]; exact hNv
  have hdom : Integrable (fun x : ℝ × (Vec m × Vec n) => (1 / 2) * ((1 + |e x| ) ^ 32 + (1 + NN C B x.2) ^ 32))
      (indepSlotLaw m n) := (hEi.add hNi').const_mul _
  have hmeas : Measurable (fun x : ℝ × (Vec m × Vec n) => ((1 + |e x|) ^ 8 * (1 + NN C B x.2) ^ 8) ^ 2) := by
    have h1 : Measurable (fun x : ℝ × (Vec m × Vec n) => NN C B x.2) := (NN_cont C B).measurable.comp measurable_snd
    have h2 : Measurable (fun x : ℝ × (Vec m × Vec n) => |e x|) := he.abs
    fun_prop
  have hpt : ∀ x : ℝ × (Vec m × Vec n), ((1 + |e x|) ^ 8 * (1 + NN C B x.2) ^ 8) ^ 2 ≤
      (1 / 2) * ((1 + |e x|) ^ 32 + (1 + NN C B x.2) ^ 32) := fun x =>
    pi_sq_le (e x) _ (abs_nonneg _) (NN_nonneg C B x.2)
  have hint : Integrable (fun x : ℝ × (Vec m × Vec n) => ((1 + |e x|) ^ 8 * (1 + NN C B x.2) ^ 8) ^ 2)
      (indepSlotLaw m n) := by
    refine hdom.mono' hmeas.aestronglyMeasurable (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact hpt x
  refine ⟨hint, ?_⟩
  calc _ ≤ ∫ x : ℝ × (Vec m × Vec n), (1 / 2) * ((1 + |e x|) ^ 32 + (1 + NN C B x.2) ^ 32) ∂(indepSlotLaw m n) :=
        integral_mono hint hdom hpt
    _ = (1 / 2) * (∫ x, (1 + |e x|) ^ 32 ∂(indepSlotLaw m n) +
          ∫ x : ℝ × (Vec m × Vec n), (1 + NN C B x.2) ^ 32 ∂(indepSlotLaw m n)) := by
        rw [integral_const_mul, integral_add hEi hNi']
    _ ≤ (1 / 2) * (KE + KNof γ CSig) := by gcongr


private def CbdOf (γ CSig s₀ KE : ℝ) : ℝ :=
  2 * LcOf γ CSig s₀ ^ 7 * Real.sqrt ((1 / 2) * (KE + KNof γ CSig)) *
    (6 * Real.sqrt (24 * γ) * CSig * (kapOf s₀ + kapOf s₀ ^ 2 + kapOf s₀ ^ 3))

private lemma bd_int {m n : ℕ} (C : Covariances m n) (B : ℕ) (hB : 0 < B) (γ CSig s₀ : ℝ)
    (hγ : 0 ≤ γ) (hs₀ : 0 < s₀) (hm : (m : ℝ) ≤ γ * B) (hn : (n : ℝ) ≤ γ * B)
    (hCo : opNorm C.Sout ≤ CSig) (hCi : opNorm C.Sin ≤ CSig)
    (F : Mat m m) (G : Mat n n) (hF : opNorm F ≤ 1) (hG : opNorm G ≤ 1) {s u : ℝ}
    (hs : s₀ ≤ s) (hu : s₀ ≤ u) (K H : Mat m n) (α β : ℝ) (hα0 : 0 ≤ α) (hβ0 : 0 ≤ β)
    (e : ℝ × (Vec m × Vec n) → ℝ) (he : Measurable e)
    (hEi : Integrable (fun x => (1 + |e x|) ^ 32) (indepSlotLaw m n)) (KE : ℝ)
    (hEv : ∫ x, (1 + |e x|) ^ 32 ∂(indepSlotLaw m n) ≤ KE) :
    Integrable (fun x : ℝ × (Vec m × Vec n) => 2 * (α + β) * |e x| *
        (LcOf γ CSig s₀ * ((1 + |e x|) * (1 + NN C B x.2))) ^ 7 * Ysum C B F G K H s u x.2)
      (indepSlotLaw m n) ∧
    ∫ x : ℝ × (Vec m × Vec n), 2 * (α + β) * |e x| *
        (LcOf γ CSig s₀ * ((1 + |e x|) * (1 + NN C B x.2))) ^ 7 * Ysum C B F G K H s u x.2
        ∂(indepSlotLaw m n) ≤ (α + β) * (CbdOf γ CSig s₀ KE / Real.sqrt B) := by
  have hBr : (0 : ℝ) < B := by exact_mod_cast hB
  have hsB : 0 < Real.sqrt (B : ℝ) := Real.sqrt_pos.mpr hBr
  have hC0 : 0 ≤ CSig := (vrp_opNorm_nonneg _).trans hCo
  have hκ0 := kapOf_nonneg s₀
  have hLc0 : 0 ≤ LcOf γ CSig s₀ := le_trans zero_le_one (LcOf_one_le hγ hC0 s₀)
  have hKE0 : 0 ≤ KE := le_trans (integral_nonneg fun x => by positivity) hEv
  have hKN0 : 0 ≤ KNof γ CSig := by unfold KNof; positivity
  obtain ⟨hpi, hpv⟩ := pi_moments C B hB γ CSig hγ hm hn hCo hCi e he hEi KE hEv
  obtain ⟨hgi0, hgv0⟩ := Ysum_sq C B hB γ CSig s₀ hγ hs₀ hm hn hCo hCi F G hF hG hs hu K H
  have hgi : Integrable (fun x : ℝ × (Vec m × Vec n) => Ysum C B F G K H s u x.2 ^ 2) (indepSlotLaw m n) :=
    ((vrp_mu_snd (fun p => Ysum C B F G K H s u p ^ 2) hgi0.aestronglyMeasurable).1).2 hgi0
  have hgv : ∫ x : ℝ × (Vec m × Vec n), Ysum C B F G K H s u x.2 ^ 2 ∂(indepSlotLaw m n) ≤
      36 * (24 * γ * CSig ^ 2 * (kapOf s₀ + kapOf s₀ ^ 2 + kapOf s₀ ^ 3) ^ 2 / B) := by
    rw [(vrp_mu_snd (fun p => Ysum C B F G K H s u p ^ 2) hgi0.aestronglyMeasurable).2]; exact hgv0
  set a := Real.sqrt ((1 / 2) * (KE + KNof γ CSig)) with ha
  set cM := kapOf s₀ + kapOf s₀ ^ 2 + kapOf s₀ ^ 3 with hcM
  have hcM0 : 0 ≤ cM := by positivity
  set b := 6 * Real.sqrt (24 * γ) * CSig * cM / Real.sqrt B with hb
  have ha0 : 0 ≤ a := Real.sqrt_nonneg _
  have hb0 : 0 ≤ b := by positivity
  have ha2 : a ^ 2 = (1 / 2) * (KE + KNof γ CSig) := Real.sq_sqrt (by positivity)
  have hb2 : b ^ 2 = 36 * (24 * γ * CSig ^ 2 * cM ^ 2 / B) := by
    rw [hb, div_pow, mul_pow, mul_pow, mul_pow, Real.sq_sqrt hBr.le, Real.sq_sqrt (by positivity)]
    ring
  have hπmeas : Measurable (fun x : ℝ × (Vec m × Vec n) => (1 + |e x|) ^ 8 * (1 + NN C B x.2) ^ 8) := by
    have h1 : Measurable (fun x : ℝ × (Vec m × Vec n) => NN C B x.2) := (NN_cont C B).measurable.comp measurable_snd
    have h2 : Measurable (fun x : ℝ × (Vec m × Vec n) => |e x|) := he.abs
    fun_prop
  have hgmeas : Measurable (fun x : ℝ × (Vec m × Vec n) => Ysum C B F G K H s u x.2) :=
    (Ysum_cont C B F G K H s u).measurable.comp measurable_snd
  obtain ⟨hpgi, hpgv⟩ := vrp_cs_int (indepSlotLaw m n) _ _ hπmeas.aestronglyMeasurable hgmeas.aestronglyMeasurable
    (fun x => by positivity) (fun x => Ysum_nonneg C B F G K H s u x.2) hpi hgi a b ha0 hb0
    (by rw [ha2]; exact hpv) (by rw [hb2]; exact hgv)
  have hBdmeas : Measurable (fun x : ℝ × (Vec m × Vec n) => 2 * (α + β) * |e x| *
        (LcOf γ CSig s₀ * ((1 + |e x|) * (1 + NN C B x.2))) ^ 7 * Ysum C B F G K H s u x.2) := by
    have h1 : Measurable (fun x : ℝ × (Vec m × Vec n) => NN C B x.2) := (NN_cont C B).measurable.comp measurable_snd
    have h2 : Measurable (fun x : ℝ × (Vec m × Vec n) => |e x|) := he.abs
    fun_prop
  have hdom : Integrable (fun x : ℝ × (Vec m × Vec n) => 2 * (α + β) * LcOf γ CSig s₀ ^ 7 *
      (((1 + |e x|) ^ 8 * (1 + NN C B x.2) ^ 8) * Ysum C B F G K H s u x.2)) (indepSlotLaw m n) :=
    hpgi.const_mul _
  have hpt : ∀ x : ℝ × (Vec m × Vec n), 2 * (α + β) * |e x| *
        (LcOf γ CSig s₀ * ((1 + |e x|) * (1 + NN C B x.2))) ^ 7 * Ysum C B F G K H s u x.2 ≤
      2 * (α + β) * LcOf γ CSig s₀ ^ 7 *
        (((1 + |e x|) ^ 8 * (1 + NN C B x.2) ^ 8) * Ysum C B F G K H s u x.2) := fun x =>
    Bd_le α β (e x) _ _ _ hα0 hβ0 hLc0 (NN_nonneg C B x.2) (Ysum_nonneg C B F G K H s u x.2)
  have hint : Integrable (fun x : ℝ × (Vec m × Vec n) => 2 * (α + β) * |e x| *
        (LcOf γ CSig s₀ * ((1 + |e x|) * (1 + NN C B x.2))) ^ 7 * Ysum C B F G K H s u x.2)
      (indepSlotLaw m n) := by
    refine hdom.mono' hBdmeas.aestronglyMeasurable (Filter.Eventually.of_forall fun x => ?_)
    have h0 : 0 ≤ 2 * (α + β) * |e x| * (LcOf γ CSig s₀ * ((1 + |e x|) * (1 + NN C B x.2))) ^ 7 *
        Ysum C B F G K H s u x.2 := by
      have := NN_nonneg C B x.2
      have := Ysum_nonneg C B F G K H s u x.2
      positivity
    rw [Real.norm_eq_abs, abs_of_nonneg h0]
    exact hpt x
  refine ⟨hint, ?_⟩
  calc _ ≤ ∫ x : ℝ × (Vec m × Vec n), 2 * (α + β) * LcOf γ CSig s₀ ^ 7 *
        (((1 + |e x|) ^ 8 * (1 + NN C B x.2) ^ 8) * Ysum C B F G K H s u x.2) ∂(indepSlotLaw m n) :=
        integral_mono hint hdom hpt
    _ = 2 * (α + β) * LcOf γ CSig s₀ ^ 7 *
        ∫ x : ℝ × (Vec m × Vec n), ((1 + |e x|) ^ 8 * (1 + NN C B x.2) ^ 8) * Ysum C B F G K H s u x.2
          ∂(indepSlotLaw m n) := integral_const_mul _ _
    _ ≤ 2 * (α + β) * LcOf γ CSig s₀ ^ 7 * (a * b) :=
        mul_le_mul_of_nonneg_left hpgv (by positivity)
    _ = (α + β) * (CbdOf γ CSig s₀ KE / Real.sqrt B) := by
        unfold CbdOf
        rw [ha, hb, hcM]
        ring


private def Rof (γ CSig s₀ : ℝ) : ℝ :=
  1 + γ * CSig / Real.sqrt s₀ + γ * CSig * (kapOf s₀ ^ 3 + kapOf s₀ ^ 2)

private lemma Rof_ge_one {γ CSig : ℝ} (hγ : 0 ≤ γ) (hC : 0 ≤ CSig) (s₀ : ℝ) : 1 ≤ Rof γ CSig s₀ := by
  unfold Rof
  have := kapOf_nonneg s₀
  have h1 : 0 ≤ γ * CSig / Real.sqrt s₀ := by positivity
  have h2 : 0 ≤ γ * CSig * (kapOf s₀ ^ 3 + kapOf s₀ ^ 2) := by positivity
  linarith

private lemma parOf_mem {m n : ℕ} (C : Covariances m n) (B : ℕ) (hB : 0 < B) (γ CSig s₀ : ℝ)
    (hγ : 0 ≤ γ) (hs₀ : 0 < s₀) (hm : (m : ℝ) ≤ γ * B) (hn : (n : ℝ) ≤ γ * B)
    (hCo : opNorm C.Sout ≤ CSig) (hCi : opNorm C.Sin ≤ CSig)
    (F : Mat m m) (G : Mat n n) (hF : opNorm F ≤ 1) (hG : opNorm G ≤ 1) {s u : ℝ}
    (hs : s₀ ≤ s) (hu : s₀ ≤ u) (K H : Mat m n) (α β : ℝ) (hα0 : 0 ≤ α) (hα1 : α ≤ 1)
    (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) : parOf C B F G K H s u α β ∈ ParSet (Rof γ CSig s₀) := by
  have hs0 : 0 < s := lt_of_lt_of_le hs₀ hs
  have hu0 : 0 < u := lt_of_lt_of_le hs₀ hu
  have hC0 : 0 ≤ CSig := (vrp_opNorm_nonneg _).trans hCo
  have hκ0 := kapOf_nonneg s₀
  set κ := kapOf s₀ with hκ
  have hR1 := Rof_ge_one hγ hC0 s₀
  have hRdef : Rof γ CSig s₀ = 1 + γ * CSig / Real.sqrt s₀ + γ * CSig * (κ ^ 3 + κ ^ 2) := rfl
  set R := Rof γ CSig s₀ with hR
  have hP : OB (cP K s) κ := OB_cP_mono K hs₀ hs
  have hQ : OB (cP H u) κ := OB_cP_mono H hs₀ hu
  have hDF : OB (DFm (n := n) F) 1 := OB_DF F hF
  have hDG : OB (DGm (m := m) G) 1 := OB_DG G hG
  have hMA : OB (cP K s * DGm G * cP H u * DFm F * cP K s) (κ * 1 * κ * 1 * κ) :=
    OB_mul (by positivity) (OB_mul (by positivity) (OB_mul (by positivity)
      (OB_mul hκ0 hP hDG) hQ) hDF) hP
  have hMB : OB (cP H u * DFm F * cP K s * DGm G * cP H u) (κ * 1 * κ * 1 * κ) :=
    OB_mul (by positivity) (OB_mul (by positivity) (OB_mul (by positivity)
      (OB_mul hκ0 hQ hDF) hP) hDG) hQ
  have hME : OB (cP K s * DGm G * cP H u) (κ * 1 * κ) :=
    OB_mul (by positivity) (OB_mul hκ0 hP hDG) hQ
  have hMT : OB (cP H u * DFm F * cP K s) (κ * 1 * κ) :=
    OB_mul (by positivity) (OB_mul hκ0 hQ hDF) hP
  have e3 : κ * 1 * κ * 1 * κ = κ ^ 3 := by ring
  have e2 : κ * 1 * κ = κ ^ 2 := by ring
  have hγC : 0 ≤ γ * CSig := by positivity
  -- entry bounds
  have bA0 := mmOf_entry00 C B hB γ CSig _ hγ (by positivity) hm hCo _ hMA
  have bA1 := mmOf_entry11 C B hB γ CSig _ hγ (by positivity) hn hCi _ hMA
  have bB0 := mmOf_entry00 C B hB γ CSig _ hγ (by positivity) hm hCo _ hMB
  have bB1 := mmOf_entry11 C B hB γ CSig _ hγ (by positivity) hn hCi _ hMB
  have bE0 := mmOf_entry00 C B hB γ CSig _ hγ (by positivity) hm hCo _ hME
  have bE1 := mmOf_entry11 C B hB γ CSig _ hγ (by positivity) hn hCi _ hME
  have bT0 := mmOf_entry00 C B hB γ CSig _ hγ (by positivity) hm hCo _ hMT
  have bT1 := mmOf_entry11 C B hB γ CSig _ hγ (by positivity) hn hCi _ hMT
  rw [e3] at bA0 bA1 bB0 bB1
  rw [e2] at bE0 bE1 bT0 bT1
  have k3 : γ * CSig * κ ^ 3 ≤ R := by
    have : 0 ≤ γ * CSig / Real.sqrt s₀ := by positivity
    have : 0 ≤ γ * CSig * κ ^ 2 := by positivity
    rw [hRdef]; nlinarith
  have k2 : γ * CSig * κ ^ 2 ≤ R := by
    have : 0 ≤ γ * CSig / Real.sqrt s₀ := by positivity
    have : 0 ≤ γ * CSig * κ ^ 3 := by positivity
    rw [hRdef]; nlinarith
  -- chi bounds
  have hs1 : γ * CSig / Real.sqrt s ≤ γ * CSig / Real.sqrt s₀ := by
    have h1 : Real.sqrt s₀ ≤ Real.sqrt s := Real.sqrt_le_sqrt hs
    have h2 : 0 < Real.sqrt s₀ := Real.sqrt_pos.mpr hs₀
    exact div_le_div_of_nonneg_left (by positivity) h2 h1
  have hu1 : γ * CSig / Real.sqrt u ≤ γ * CSig / Real.sqrt s₀ := by
    have h1 : Real.sqrt s₀ ≤ Real.sqrt u := Real.sqrt_le_sqrt hu
    have h2 : 0 < Real.sqrt s₀ := Real.sqrt_pos.mpr hs₀
    exact div_le_div_of_nonneg_left (by positivity) h2 h1
  have x1 := (chiO_le C B hB K hs0 γ CSig hm hCo hγ).trans hs1
  have x2 := (chiI_le C B hB K hs0 γ CSig hn hCi hγ).trans hs1
  have x3 := (chiO_le C B hB H hu0 γ CSig hm hCo hγ).trans hu1
  have x4 := (chiI_le C B hB H hu0 γ CSig hn hCi hγ).trans hu1
  have kχ : γ * CSig / Real.sqrt s₀ ≤ R := by
    have : 0 ≤ γ * CSig * (κ ^ 3 + κ ^ 2) := by positivity
    rw [hRdef]; linarith
  have n1 := chiO_nonneg C B K hs0
  have n2' := chiI_nonneg C B K hs0
  have n3 := chiO_nonneg C B H hu0
  have n4 := chiI_nonneg C B H hu0
  have mmle : max α β ≤ 1 := max_le hα1 hβ1
  have mm0 : 0 ≤ max α β := le_max_of_le_left hα0
  have rho1 : ∀ a b : ℝ, 0 ≤ a → a ≤ b → 0 ≤ (if b = 0 then 0 else a / b) ∧ (if b = 0 then 0 else a / b) ≤ 1 := by
    intro a b ha hab
    by_cases hb : b = 0
    · simp [hb]
    · have hb0 : 0 < b := lt_of_le_of_ne (ha.trans hab) (Ne.symm hb)
      simp only [hb, if_false]
      exact ⟨div_nonneg ha hb0.le, (div_le_one hb0).2 hab⟩
  have hr1 := rho1 α (max α β) hα0 (le_max_left α β)
  have hr2 := rho1 β (max α β) hβ0 (le_max_right α β)
  refine ⟨?_, ?_⟩
  · rw [mem_closedBall_zero_iff]
    refine (pi_norm_le_iff_of_nonneg (by linarith)).2 fun i => ?_
    fin_cases i
    · simp [parOf]; rw [abs_of_nonneg mm0]; linarith
    · simp [parOf]; rw [abs_of_nonneg hr1.1]; linarith [hr1.2]
    · simp [parOf]; rw [abs_of_nonneg hr2.1]; linarith [hr2.2]
    · simp [parOf]; rw [abs_of_nonneg n1]; linarith
    · simp [parOf]; rw [abs_of_nonneg n2']; linarith
    · simp [parOf]; rw [abs_of_nonneg n3]; linarith
    · simp [parOf]; rw [abs_of_nonneg n4]; linarith
    · simp [parOf]; linarith
    · simp [parOf]; linarith
    · simp [parOf]; linarith
    · simp [parOf]; linarith
    · simp [parOf]; linarith
    · simp [parOf]; linarith
    · simp [parOf]; linarith
    · simp [parOf]; linarith
  · simp [parOf]
    exact ⟨n1, n2', n3, n4⟩


private lemma vSlotX_eq {m n : ℕ} (C : Covariances m n) (B : ℕ) (hB : 0 < B) (p : Vec m × Vec n) :
    vSlotX C B p = outer (momU C B p) (momV C B p) := by
  have hBr : (0 : ℝ) < B := by exact_mod_cast hB
  have hsym : (rIn C)ᵀ = rIn C := vrp_rIn_symm C
  have h1 : rOut C * outer p.1 p.2 * rIn C = outer (Matrix.mulVec (rOut C) p.1) (Matrix.mulVec (rIn C) p.2) := by
    have hv : Matrix.vecMul p.2 (rIn C) = Matrix.mulVec (rIn C) p.2 := by
      rw [← Matrix.vecMul_transpose, hsym]
    rw [Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, hv]
  unfold vSlotX momU momV
  rw [h1]
  ext i j
  simp only [Matrix.smul_apply, Matrix.vecMulVec_apply, Pi.smul_apply, smul_eq_mul]
  have hs : Real.sqrt (B : ℝ) * Real.sqrt (B : ℝ) = B := Real.mul_self_sqrt hBr.le
  have hs0 : Real.sqrt (B : ℝ) ≠ 0 := (Real.sqrt_pos.mpr hBr).ne'
  field_simp
  rw [Real.sq_sqrt hBr.le]
  ring


private lemma fprime_meas {m n : ℕ} (C : Covariances m n) (B : ℕ) (F : Mat m m) (G : Mat n n) {s u : ℝ}
    (hs : 0 < s) (hu : 0 < u) (K H : Mat m n) (α β : ℝ)
    (e : ℝ × (Vec m × Vec n) → ℝ) (he : Measurable e) :
    Measurable (fun x : ℝ × (Vec m × Vec n) => contractionRes B F G s u
      (K + (α * e x) • vSlotX C B x.2) (H + (β * e x) • vSlotX C B x.2)) := by
  have hS : Measurable (fun x : ℝ × (Vec m × Vec n) => vSlotX C B x.2) :=
    (vrp_slot_cont C B).measurable.comp measurable_snd
  have h1 : Measurable (fun x : ℝ × (Vec m × Vec n) => K + (α * e x) • vSlotX C B x.2) :=
    measurable_const.add ((measurable_const.mul he).smul hS)
  have h2 : Measurable (fun x : ℝ × (Vec m × Vec n) => H + (β * e x) • vSlotX C B x.2) :=
    measurable_const.add ((measurable_const.mul he).smul hS)
  have e : (fun x : ℝ × (Vec m × Vec n) => contractionRes B F G s u
      (K + (α * e x) • vSlotX C B x.2) (H + (β * e x) • vSlotX C B x.2)) =
      (fun p : Mat m n × Mat m n => contractionRes B F G s u p.1 p.2) ∘
        (fun x : ℝ × (Vec m × Vec n) => (K + (α * e x) • vSlotX C B x.2, H + (β * e x) • vSlotX C B x.2)) := by
    funext x; rfl
  rw [e]
  exact (vrp_f_cont (B := B) F G hs hu).measurable.comp (h1.prodMk h2)

private lemma fprime_int {m n : ℕ} (C : Covariances m n) (B : ℕ) (hB : 0 < B) (F : Mat m m) (G : Mat n n)
    (hF : opNorm F ≤ 1) (hG : opNorm G ≤ 1) {s u : ℝ}
    (hs : 0 < s) (hu : 0 < u) (K H : Mat m n) (α β : ℝ)
    (e : ℝ × (Vec m × Vec n) → ℝ) (he : Measurable e) :
    Integrable (fun x : ℝ × (Vec m × Vec n) => contractionRes B F G s u
      (K + (α * e x) • vSlotX C B x.2) (H + (β * e x) • vSlotX C B x.2)) (indepSlotLaw m n) := by
  refine Integrable.of_bound (fprime_meas C B F G hs hu K H α β e he).aestronglyMeasurable
    (((min m n : ℕ) : ℝ) / B * (1 / (2 * Real.sqrt s)) * (1 / (2 * Real.sqrt u)))
    (Filter.Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs]
  exact vrp_f_bdd hB F G hF hG hs hu _ _

private lemma psiF_cont_e {R : ℝ} (θ : ParSet R) : Continuous (fun t : ℝ => psiF θ.1 t) := by
  have h : Continuous (fun t : ℝ => ((θ, t) : ParSet R × ℝ)) := continuous_const.prodMk continuous_id
  have e : (fun t : ℝ => psiF θ.1 t) = (fun p : ParSet R × ℝ => psiF p.1.1 p.2) ∘ (fun t : ℝ => ((θ, t) : ParSet R × ℝ)) := by
    funext t; rfl
  rw [e]
  exact (psiF_cont R).comp h

private lemma psiF_int {m n : ℕ} {R : ℝ} (hR : 1 ≤ R) (θ : ParSet R)
    (e : ℝ × (Vec m × Vec n) → ℝ) (he : Measurable e)
    (hEi : Integrable (fun x => (1 + |e x|) ^ 32) (indepSlotLaw m n)) :
    Integrable (fun x : ℝ × (Vec m × Vec n) => psiF θ.1 (e x)) (indepSlotLaw m n) := by
  obtain ⟨Cψ, hCψ⟩ := psiF_bound R hR
  have hdom : Integrable (fun x : ℝ × (Vec m × Vec n) => |Cψ| * (1 + (1 + |e x|) ^ 32)) (indepSlotLaw m n) :=
    ((integrable_const (1 : ℝ)).add hEi).const_mul _
  refine hdom.mono' ((psiF_cont_e θ).measurable.comp he).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => ?_)
  refine (hCψ θ (e x)).trans ?_
  have h1 : (1 + |e x|) ^ 4 ≤ 1 + (1 + |e x|) ^ 32 := by
    have : 1 ≤ 1 + |e x| := by linarith [abs_nonneg (e x)]
    have h2 : (1 + |e x|) ^ 4 ≤ (1 + |e x|) ^ 32 := pow_le_pow_right₀ this (by norm_num)
    linarith
  exact mul_le_mul (le_abs_self _) h1 (by positivity) (abs_nonneg _)


private lemma os_part {m n : ℕ} (C : Covariances m n) (B : ℕ) (hB : 0 < B) (γ CSig s₀ : ℝ)
    (hγ : 0 ≤ γ) (hs₀ : 0 < s₀) (hm : (m : ℝ) ≤ γ * B) (hn : (n : ℝ) ≤ γ * B)
    (hCo : opNorm C.Sout ≤ CSig) (hCi : opNorm C.Sin ≤ CSig)
    (F : Mat m m) (G : Mat n n) (hF : opNorm F ≤ 1) (hG : opNorm G ≤ 1) {s u : ℝ}
    (hs : s₀ ≤ s) (hu : s₀ ≤ u) (K H : Mat m n) (α β : ℝ) (hα0 : 0 ≤ α) (hα1 : α ≤ 1)
    (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1)
    (e : ℝ × (Vec m × Vec n) → ℝ) (he : Measurable e)
    (hEi : Integrable (fun x => (1 + |e x|) ^ 32) (indepSlotLaw m n)) (KE : ℝ)
    (hEv : ∫ x, (1 + |e x|) ^ 32 ∂(indepSlotLaw m n) ≤ KE) :
    ‖(B : ℂ) * ((((∫ x : ℝ × (Vec m × Vec n), contractionRes B F G s u
          (K + (α * e x) • vSlotX C B x.2) (H + (β * e x) • vSlotX C B x.2) ∂(indepSlotLaw m n)) -
          contractionRes B F G s u K H : ℝ)) : ℂ) -
      ((max α β : ℝ) : ℂ) * ∫ x : ℝ × (Vec m × Vec n), psiF (parOf C B F G K H s u α β) (e x)
        ∂(indepSlotLaw m n)‖ ≤ (α + β) * (CbdOf γ CSig s₀ KE / Real.sqrt B) := by
  have hs0 : 0 < s := lt_of_lt_of_le hs₀ hs
  have hu0 : 0 < u := lt_of_lt_of_le hs₀ hu
  have hC0 : 0 ≤ CSig := (vrp_opNorm_nonneg _).trans hCo
  have hθ := parOf_mem C B hB γ CSig s₀ hγ hs₀ hm hn hCo hCi F G hF hG hs hu K H α β hα0 hα1 hβ0 hβ1
  set θ : ParSet (Rof γ CSig s₀) := ⟨parOf C B F G K H s u α β, hθ⟩ with hθdef
  have hf' := fprime_int C B hB F G hF hG hs0 hu0 K H α β e he
  have hΨi := psiF_int (Rof_ge_one hγ hC0 s₀) θ e he hEi
  obtain ⟨hBdi, hBdv⟩ := bd_int C B hB γ CSig s₀ hγ hs₀ hm hn hCo hCi F G hF hG hs hu K H α β hα0 hβ0 e he hEi KE hEv
  -- the integrals
  set μ := indepSlotLaw m n with hμ
  have hΔi : Integrable (fun x : ℝ × (Vec m × Vec n) => (B : ℂ) * ((contractionRes B F G s u
      (K + (α * e x) • vSlotX C B x.2) (H + (β * e x) • vSlotX C B x.2) - contractionRes B F G s u K H : ℝ) : ℂ)) μ :=
    ((hf'.sub (integrable_const _)).ofReal).const_mul _
  have hΨi' : Integrable (fun x : ℝ × (Vec m × Vec n) => ((max α β : ℝ) : ℂ) * psiF (parOf C B F G K H s u α β) (e x)) μ :=
    hΨi.const_mul _
  have hint1 : ∫ x : ℝ × (Vec m × Vec n), (B : ℂ) * ((contractionRes B F G s u
      (K + (α * e x) • vSlotX C B x.2) (H + (β * e x) • vSlotX C B x.2) - contractionRes B F G s u K H : ℝ) : ℂ) ∂μ =
      (B : ℂ) * ((((∫ x : ℝ × (Vec m × Vec n), contractionRes B F G s u
          (K + (α * e x) • vSlotX C B x.2) (H + (β * e x) • vSlotX C B x.2) ∂μ) -
          contractionRes B F G s u K H : ℝ)) : ℂ) := by
    rw [integral_const_mul]
    congr 1
    rw [integral_complex_ofReal, integral_sub hf' (integrable_const _), integral_const]
    simp
  have hint2 : ∫ x : ℝ × (Vec m × Vec n), ((max α β : ℝ) : ℂ) * psiF (parOf C B F G K H s u α β) (e x) ∂μ =
      ((max α β : ℝ) : ℂ) * ∫ x : ℝ × (Vec m × Vec n), psiF (parOf C B F G K H s u α β) (e x) ∂μ :=
    integral_const_mul _ _
  rw [← hint1, ← hint2, ← integral_sub hΔi hΨi']
  refine (norm_integral_le_integral_norm _).trans ?_
  refine le_trans (integral_mono (hΔi.sub hΨi').norm hBdi fun x => ?_) hBdv
  have hx := vrp_point C B hB γ CSig s₀ hγ hs₀ hm hn hCo hCi F G hF hG hs hu K H α β (e x) hα0 hα1 hβ0 hβ1 x.2
  rw [← vSlotX_eq C B hB x.2] at hx
  exact hx


private def KEof : ℝ :=
  max (2 ^ 32 * (1 + ((Nat.doubleFactorial (2 * 16 - 1) : ℕ) : ℝ) ^ 2))
    (∫ y : ℝ, (1 + |y|) ^ 32 ∂(gaussianReal 0 1))

private lemma vrp_onesample {m n : ℕ} (C : Covariances m n) (B : ℕ) (hB : 0 < B) (γ CSig s₀ : ℝ)
    (hγ : 0 ≤ γ) (hs₀ : 0 < s₀) (hm : (m : ℝ) ≤ γ * B) (hn : (n : ℝ) ≤ γ * B)
    (hCo : opNorm C.Sout ≤ CSig) (hCi : opNorm C.Sin ≤ CSig) (A : Mat m n) (hA : fro A = 1)
    (F : Mat m m) (G : Mat n n) (hF : opNorm F ≤ 1) (hG : opNorm G ≤ 1) {s u : ℝ}
    (hs : s₀ ≤ s) (hu : s₀ ≤ u) (K H : Mat m n) (α β : ℝ) (hα0 : 0 ≤ α) (hα1 : α ≤ 1)
    (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) (r : ℝ)
    (hr : ∀ θ : ParSet (Rof γ CSig s₀),
      ‖(∫ p : Vec m × Vec n, psiF θ.1 (resid A p) ∂(gaussPair m n)) -
        ∫ y : ℝ, psiF θ.1 y ∂(gaussianReal 0 1)‖ ≤ r) :
    |(∫ x : ℝ × (Vec m × Vec n), contractionRes B F G s u (K + (α * resid A x.2) • vSlotX C B x.2)
        (H + (β * resid A x.2) • vSlotX C B x.2) ∂(indepSlotLaw m n)) -
      ∫ x : ℝ × (Vec m × Vec n), contractionRes B F G s u (K + (α * x.1) • vSlotX C B x.2)
        (H + (β * x.1) • vSlotX C B x.2) ∂(indepSlotLaw m n)| ≤
      (α + β) * (2 * (CbdOf γ CSig s₀ KEof / Real.sqrt B) + r) / B := by
  have hBr : (0 : ℝ) < B := by exact_mod_cast hB
  have hs0 : 0 < s := lt_of_lt_of_le hs₀ hs
  have hu0 : 0 < u := lt_of_lt_of_le hs₀ hu
  have hC0 : 0 ≤ CSig := (vrp_opNorm_nonneg _).trans hCo
  have hθ := parOf_mem C B hB γ CSig s₀ hγ hs₀ hm hn hCo hCi F G hF hG hs hu K H α β hα0 hα1 hβ0 hβ1
  set θ : ParSet (Rof γ CSig s₀) := ⟨parOf C B F G K H s u α β, hθ⟩ with hθdef
  -- the two scalars
  have hed : Measurable (fun x : ℝ × (Vec m × Vec n) => resid A x.2) :=
    (vrp_resid_cont A).measurable.comp measurable_snd
  have heg : Measurable (fun x : ℝ × (Vec m × Vec n) => x.1) := measurable_fst
  obtain ⟨hdi0, hdv0⟩ := resid_moment32 A hA
  have hdi : Integrable (fun x : ℝ × (Vec m × Vec n) => (1 + |resid A x.2|) ^ 32) (indepSlotLaw m n) :=
    ((vrp_mu_snd (fun p => (1 + |resid A p|) ^ 32) hdi0.aestronglyMeasurable).1).2 hdi0
  have hdv : ∫ x : ℝ × (Vec m × Vec n), (1 + |resid A x.2|) ^ 32 ∂(indepSlotLaw m n) ≤ KEof := by
    rw [(vrp_mu_snd (fun p => (1 + |resid A p|) ^ 32) hdi0.aestronglyMeasurable).2]
    exact hdv0.trans (le_max_left _ _)
  have hgi0 := gauss_moment32
  have hgi : Integrable (fun x : ℝ × (Vec m × Vec n) => (1 + |x.1|) ^ 32) (indepSlotLaw m n) :=
    ((vrp_mu_fst (fun y : ℝ => (1 + |y|) ^ 32) hgi0.aestronglyMeasurable).1).2 hgi0
  have hgv : ∫ x : ℝ × (Vec m × Vec n), (1 + |x.1|) ^ 32 ∂(indepSlotLaw m n) ≤ KEof := by
    rw [(vrp_mu_fst (fun y : ℝ => (1 + |y|) ^ 32) hgi0.aestronglyMeasurable).2]
    exact le_max_right _ _
  have Pd := os_part C B hB γ CSig s₀ hγ hs₀ hm hn hCo hCi F G hF hG hs hu K H α β hα0 hα1 hβ0 hβ1
    (fun x => resid A x.2) hed hdi KEof hdv
  have Pg := os_part C B hB γ CSig s₀ hγ hs₀ hm hn hCo hCi F G hF hG hs hu K H α β hα0 hα1 hβ0 hβ1
    (fun x => x.1) heg hgi KEof hgv
  -- the marginal integrals of ψ
  have hψd : ∫ x : ℝ × (Vec m × Vec n), psiF (parOf C B F G K H s u α β) (resid A x.2) ∂(indepSlotLaw m n) =
      ∫ p : Vec m × Vec n, psiF θ.1 (resid A p) ∂(gaussPair m n) := by
    have hc : Continuous (fun p : Vec m × Vec n => psiF θ.1 (resid A p)) := (psiF_cont_e θ).comp (vrp_resid_cont A)
    exact (vrp_mu_snd (fun p => psiF θ.1 (resid A p)) hc.aestronglyMeasurable).2
  have hψg : ∫ x : ℝ × (Vec m × Vec n), psiF (parOf C B F G K H s u α β) x.1 ∂(indepSlotLaw m n) =
      ∫ y : ℝ, psiF θ.1 y ∂(gaussianReal 0 1) :=
    (vrp_mu_fst (fun y => psiF θ.1 y) (psiF_cont_e θ).aestronglyMeasurable).2
  rw [hψd] at Pd
  rw [hψg] at Pg
  -- combine
  set Id := ∫ x : ℝ × (Vec m × Vec n), contractionRes B F G s u (K + (α * resid A x.2) • vSlotX C B x.2)
        (H + (β * resid A x.2) • vSlotX C B x.2) ∂(indepSlotLaw m n) with hId
  set Ig := ∫ x : ℝ × (Vec m × Vec n), contractionRes B F G s u (K + (α * x.1) • vSlotX C B x.2)
        (H + (β * x.1) • vSlotX C B x.2) ∂(indepSlotLaw m n) with hIg
  set f0 := contractionRes B F G s u K H with hf0
  set ψd := ∫ p : Vec m × Vec n, psiF θ.1 (resid A p) ∂(gaussPair m n) with hψd'
  set ψg := ∫ y : ℝ, psiF θ.1 y ∂(gaussianReal 0 1) with hψg'
  have hmm : max α β ≤ α + β := max_le (by linarith) (by linarith)
  have hmm0 : 0 ≤ max α β := le_max_of_le_left hα0
  have e1 : (B : ℂ) * (((Id - Ig : ℝ)) : ℂ) =
      ((B : ℂ) * (((Id - f0 : ℝ)) : ℂ) - ((max α β : ℝ) : ℂ) * ψd) -
        ((B : ℂ) * (((Ig - f0 : ℝ)) : ℂ) - ((max α β : ℝ) : ℂ) * ψg) + ((max α β : ℝ) : ℂ) * (ψd - ψg) := by
    push_cast; ring
  have n1 : (B : ℝ) * |Id - Ig| = ‖(B : ℂ) * (((Id - Ig : ℝ)) : ℂ)‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_natCast]
  have n2' : ‖((max α β : ℝ) : ℂ) * (ψd - ψg)‖ ≤ (α + β) * r := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hmm0]
    exact mul_le_mul hmm (hr θ) (norm_nonneg _) (by linarith)
  have key : (B : ℝ) * |Id - Ig| ≤ 2 * ((α + β) * (CbdOf γ CSig s₀ KEof / Real.sqrt B)) + (α + β) * r := by
    rw [n1, e1]
    refine (norm_add_le _ _).trans ?_
    refine add_le_add ((norm_sub_le _ _).trans ?_) n2'
    linarith [Pd, Pg]
  rw [le_div_iff₀ hBr, mul_comm]
  linarith [key]


/-! ### The final assembly -/

private lemma exists_s0 (J : Set ℝ) (hJ : IsCompact J) (hJpos : J ⊆ Ioi 0) :
    ∃ s₀ : ℝ, 0 < s₀ ∧ ∀ s ∈ J, s₀ ≤ s := by
  rcases J.eq_empty_or_nonempty with h | h
  · exact ⟨1, one_pos, by simp [h]⟩
  · obtain ⟨x, hx, hmin⟩ := hJ.exists_isMinOn h continuous_id.continuousOn
    exact ⟨x, hJpos hx, fun s hs => hmin hs⟩

private lemma fro_sq_le_card {m n : ℕ} (A : Mat m n) : fro A ^ 2 ≤ (n : ℝ) * opNorm A ^ 2 := by
  unfold fro
  rw [Real.sq_sqrt (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _)]
  have hcol : ∀ j : Fin n, ∑ i, ‖A i j‖ ^ 2 ≤ opNorm A ^ 2 := by
    intro j
    have h := vrp_mulVec_sq A (le_refl (opNorm A)) (Pi.single j (1 : ℝ))
    have e1 : ∑ k, (Pi.single j (1 : ℝ) : Vec n) k ^ 2 = 1 := by
      simp [Pi.single_apply]
    have e2 : ∑ i, (A *ᵥ (Pi.single j (1 : ℝ) : Vec n)) i ^ 2 = ∑ i, ‖A i j‖ ^ 2 := by
      refine Finset.sum_congr rfl fun i _ => ?_
      simp [Matrix.mulVec, dotProduct, Pi.single_apply, Real.norm_eq_abs, sq_abs]
    rw [e1, mul_one, e2] at h
    exact h
  rw [Finset.sum_comm]
  calc ∑ j, ∑ i, ‖A i j‖ ^ 2 ≤ ∑ _j : Fin n, opNorm A ^ 2 := Finset.sum_le_sum fun j _ => hcol j
    _ = (n : ℝ) * opNorm A ^ 2 := by simp

private lemma inv_sqrt_le {m n : ℕ} (A : Mat m n) (hA : fro A = 1) (B : ℕ) (hB : 0 < B) (γ : ℝ) (hγ : 0 ≤ γ)
    (hn : (n : ℝ) ≤ γ * B) : 1 / Real.sqrt B ≤ Real.sqrt γ * opNorm A := by
  have hBr : (0 : ℝ) < B := by exact_mod_cast hB
  have h1 := fro_sq_le_card A
  rw [hA] at h1
  have hop := vrp_opNorm_nonneg A
  have h2 : 1 ≤ γ * B * opNorm A ^ 2 := by
    calc (1 : ℝ) = 1 ^ 2 := by norm_num
      _ ≤ (n : ℝ) * opNorm A ^ 2 := h1
      _ ≤ γ * B * opNorm A ^ 2 := mul_le_mul_of_nonneg_right hn (sq_nonneg _)
  have hsB : 0 < Real.sqrt B := Real.sqrt_pos.mpr hBr
  rw [div_le_iff₀ hsB]
  have h3 : 1 ≤ (Real.sqrt γ * opNorm A * Real.sqrt B) ^ 2 := by
    rw [mul_pow, mul_pow, Real.sq_sqrt hγ, Real.sq_sqrt hBr.le]
    nlinarith [h2]
  have h4 : 0 ≤ Real.sqrt γ * opNorm A * Real.sqrt B := by positivity
  nlinarith [h3, h4]


private lemma psiF_norm_int {Ω₁ : Type*} [MeasurableSpace Ω₁] (ν : Measure Ω₁) [IsProbabilityMeasure ν]
    {R : ℝ} (θ : ParSet R) (Cψ : ℝ) (hCψ : ∀ t : ℝ, ‖psiF θ.1 t‖ ≤ Cψ * (1 + |t|) ^ 4)
    (e : Ω₁ → ℝ) (he : Measurable e) (hEi : Integrable (fun x => (1 + |e x|) ^ 32) ν) (KE : ℝ)
    (hEv : ∫ x, (1 + |e x|) ^ 32 ∂ν ≤ KE) :
    ‖∫ x, psiF θ.1 (e x) ∂ν‖ ≤ |Cψ| * (1 + KE) := by
  have hdom : Integrable (fun x => |Cψ| * (1 + (1 + |e x|) ^ 32)) ν :=
    ((integrable_const (1 : ℝ)).add hEi).const_mul _
  refine (norm_integral_le_integral_norm _).trans ?_
  have hpt : ∀ x, ‖psiF θ.1 (e x)‖ ≤ |Cψ| * (1 + (1 + |e x|) ^ 32) := by
    intro x
    refine (hCψ (e x)).trans ?_
    have h1 : (1 + |e x|) ^ 4 ≤ 1 + (1 + |e x|) ^ 32 := by
      have : 1 ≤ 1 + |e x| := by linarith [abs_nonneg (e x)]
      have h2 : (1 + |e x|) ^ 4 ≤ (1 + |e x|) ^ 32 := pow_le_pow_right₀ this (by norm_num)
      linarith
    exact mul_le_mul (le_abs_self _) h1 (by positivity) (abs_nonneg _)
  calc ∫ x, ‖psiF θ.1 (e x)‖ ∂ν ≤ ∫ x, |Cψ| * (1 + (1 + |e x|) ^ 32) ∂ν :=
        integral_mono_of_nonneg (Filter.Eventually.of_forall fun x => norm_nonneg _) hdom
          (Filter.Eventually.of_forall hpt)
    _ = |Cψ| * (1 + ∫ x, (1 + |e x|) ^ 32 ∂ν) := by
        rw [integral_const_mul, integral_add (integrable_const 1) hEi]; simp
    _ ≤ |Cψ| * (1 + KE) := by gcongr

private lemma psiF_moment_bound {R : ℝ} (hR : 1 ≤ R) : ∃ M : ℝ, ∀ {m n : ℕ} (A : Mat m n), fro A = 1 →
    ∀ θ : ParSet R, ‖(∫ p : Vec m × Vec n, psiF θ.1 (resid A p) ∂(gaussPair m n)) -
      ∫ y : ℝ, psiF θ.1 y ∂(gaussianReal 0 1)‖ ≤ M := by
  obtain ⟨Cψ, hCψ⟩ := psiF_bound R hR
  refine ⟨2 * (|Cψ| * (1 + KEof)), fun {m n} A hA θ => ?_⟩
  obtain ⟨hdi, hdv⟩ := resid_moment32 A hA
  have h1 := psiF_norm_int (gaussPair m n) θ Cψ (hCψ θ) (fun p => resid A p) (vrp_resid_cont A).measurable hdi KEof
    (hdv.trans (le_max_left _ _))
  have h2 := psiF_norm_int (gaussianReal 0 1) θ Cψ (hCψ θ) (fun y : ℝ => y) measurable_id gauss_moment32 KEof
    (le_max_right _ _)
  calc _ ≤ ‖∫ p : Vec m × Vec n, psiF θ.1 (resid A p) ∂(gaussPair m n)‖ + ‖∫ y : ℝ, psiF θ.1 y ∂(gaussianReal 0 1)‖ :=
        norm_sub_le _ _
    _ ≤ _ := by linarith

private lemma exists_rseq (γ CSig s₀ : ℝ) (hγ : 0 ≤ γ) (hC : 0 ≤ CSig) {m n : ℕ → ℕ}
    (A : ∀ k, Mat (m k) (n k)) (hA : ∀ k, fro (A k) = 1)
    (hAn : Tendsto (fun k => opNorm (A k)) atTop (𝓝 0)) :
    ∃ r : ℕ → ℝ, Tendsto r atTop (𝓝 0) ∧ (∀ k, 0 ≤ r k) ∧ ∀ k (θ : ParSet (Rof γ CSig s₀)),
      ‖(∫ p : Vec (m k) × Vec (n k), psiF θ.1 (resid (A k) p) ∂(gaussPair (m k) (n k))) -
        ∫ y : ℝ, psiF θ.1 y ∂(gaussianReal 0 1)‖ ≤ r k := by
  have hR1 := Rof_ge_one hγ hC s₀
  haveI : CompactSpace (ParSet (Rof γ CSig s₀)) := isCompact_iff_compactSpace.mp (ParSet_compact _)
  obtain ⟨Cψ, hCψ⟩ := psiF_bound (Rof γ CSig s₀) hR1
  obtain ⟨M, hM⟩ := psiF_moment_bound hR1
  set q : ∀ k, ParSet (Rof γ CSig s₀) → ℝ := fun k θ =>
    ‖(∫ p : Vec (m k) × Vec (n k), psiF θ.1 (resid (A k) p) ∂(gaussPair (m k) (n k))) -
      ∫ y : ℝ, psiF θ.1 y ∂(gaussianReal 0 1)‖ with hq
  have hbdd : ∀ k, BddAbove (Set.range (q k)) := fun k => ⟨M, by
    rintro _ ⟨θ, rfl⟩; exact hM (A k) (hA k) θ⟩
  refine ⟨fun k => ⨆ θ, q k θ, ?_, fun k => Real.iSup_nonneg fun θ => norm_nonneg _,
    fun k θ => le_ciSup (hbdd k) θ⟩
  -- convergence
  have hw := vrp_scalar_weak (Θ := ParSet (Rof γ CSig s₀)) (Ω := fun k => Vec (m k) × Vec (n k))
    A hA hAn (fun k => gaussPair (m k) (n k)) (fun k ω => ω.1) (fun k ω => ω.2)
    (fun k => by simp [Measure.map_id])
    (fun θ x => psiF θ.1 x) (psiF_cont _) Cψ (fun θ x => hCψ θ x)
  rw [Metric.tendsto_atTop]
  intro ε hε
  have := hw (ε / 2) (by linarith)
  rw [Filter.eventually_atTop] at this
  obtain ⟨N, hN⟩ := this
  refine ⟨N, fun k hk => ?_⟩
  have h1 : (⨆ θ, q k θ) ≤ ε / 2 := Real.iSup_le (fun θ => by simpa [hq] using hN k hk θ) (by linarith)
  have h2 : 0 ≤ ⨆ θ, q k θ := Real.iSup_nonneg fun θ => norm_nonneg _
  rw [Real.dist_eq, sub_zero, abs_of_nonneg h2]
  linarith


private lemma CbdOf_nonneg {γ CSig : ℝ} (hγ : 0 ≤ γ) (hC : 0 ≤ CSig) (s₀ KE : ℝ) :
    0 ≤ CbdOf γ CSig s₀ KE := by
  unfold CbdOf
  have hLc0 : 0 ≤ LcOf γ CSig s₀ := le_trans zero_le_one (LcOf_one_le hγ hC s₀)
  have := kapOf_nonneg s₀
  positivity

private theorem vrp_main (J : Set ℝ) (hJ : IsCompact J) (hJpos : J ⊆ Ioi 0)
    (CSig γstar : ℝ) (m n B : ℕ → ℕ) (A : ∀ k : ℕ, Mat (m k) (n k))
    (hA : ∀ k : ℕ, fro (A k) = 1) (hAn : Tendsto (fun k : ℕ => opNorm (A k)) atTop (𝓝 0)) :
    ∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧
      ∀ (k : ℕ) (Fp : FrozenParams (m k) (n k) (B k)), Fp.A = A k →
        opNorm Fp.C.Sout ≤ CSig → opNorm Fp.C.Sin ≤ CSig →
        ((max (m k) (n k) : ℕ) : ℝ) ≤ γstar * (B k : ℝ) →
        ∀ (Ω' : Type) [MeasurableSpace Ω'] (P : Measure Ω') [IsProbabilityMeasure P]
          (S : FrozenSamples P (m k) (n k) (B k)) (t : ℤ) (ℓ : ℕ) (s u : ℝ),
          s ∈ J → u ∈ J →
          ∀ F : Mat (m k) (m k), opNorm F ≤ 1 → ∀ G : Mat (n k) (n k), opNorm G ≤ 1 →
          |(∫ ω, contractionRes (B k) F G s u (frozenBuf Fp S t ω)
                (frozenBuf Fp S (t + (ℓ : ℤ)) ω) ∂P) -
            (∫ ω, contractionRes (B k) F G s u (def_app_vol_product Fp ω t)
                (def_app_vol_product Fp ω (t + (ℓ : ℤ)))
                ∂(indepSpaceLaw (m k) (n k) (B k)))| ≤ 2 * ε k := by
  obtain ⟨s₀, hs₀, hJs₀⟩ := exists_s0 J hJ hJpos
  set γ' : ℝ := max γstar 0 with hγ'
  set CS : ℝ := max CSig 0 with hCS
  have hγ0 : 0 ≤ γ' := le_max_right _ _
  have hCS0 : 0 ≤ CS := le_max_right _ _
  obtain ⟨r, hrt, hr0, hr⟩ := exists_rseq γ' CS s₀ hγ0 hCS0 A hA hAn
  have hCbd := CbdOf_nonneg hγ0 hCS0 s₀ KEof
  refine ⟨fun k => 2 * CbdOf γ' CS s₀ KEof * (Real.sqrt γ' * opNorm (A k)) + r k, ?_, ?_⟩
  · have h1 : Tendsto (fun k => 2 * CbdOf γ' CS s₀ KEof * (Real.sqrt γ' * opNorm (A k))) atTop (𝓝 0) := by
      have := (hAn.const_mul (Real.sqrt γ')).const_mul (2 * CbdOf γ' CS s₀ KEof)
      simpa using this
    simpa using h1.add hrt
  · intro k Fp hFpA hCo hCi hdim Ω' _ P _ S t ℓ s u hs hu F hF G hG
    have hB := Fp.hB
    have hBr : (0 : ℝ) < B k := by exact_mod_cast hB
    have hs₀s := hJs₀ s hs
    have hu₀u := hJs₀ u hu
    have hs0 : 0 < s := lt_of_lt_of_le hs₀ hs₀s
    have hu0 : 0 < u := lt_of_lt_of_le hs₀ hu₀u
    have hm : (m k : ℝ) ≤ γ' * B k := by
      have h1 : (m k : ℝ) ≤ ((max (m k) (n k) : ℕ) : ℝ) := by exact_mod_cast le_max_left _ _
      have h2 : γstar * (B k : ℝ) ≤ γ' * B k := mul_le_mul_of_nonneg_right (le_max_left _ _) hBr.le
      linarith
    have hn : (n k : ℝ) ≤ γ' * B k := by
      have h1 : (n k : ℝ) ≤ ((max (m k) (n k) : ℕ) : ℝ) := by exact_mod_cast le_max_right _ _
      have h2 : γstar * (B k : ℝ) ≤ γ' * B k := mul_le_mul_of_nonneg_right (le_max_left _ _) hBr.le
      linarith
    have hCo' : opNorm Fp.C.Sout ≤ CS := hCo.trans (le_max_left _ _)
    have hCi' : opNorm Fp.C.Sin ≤ CS := hCi.trans (le_max_left _ _)
    have hε0 : 0 ≤ 2 * CbdOf γ' CS s₀ KEof * (Real.sqrt γ' * opNorm (A k)) + r k := by
      have := hr0 k
      have := vrp_opNorm_nonneg (A k)
      positivity
    have hinv := inv_sqrt_le Fp.A Fp.hA (B k) hB γ' hγ0 hn
    refine vrp_assemble Fp F G hF hG hs0 hu0 _ hε0 ?_ Ω' P S t ℓ
    intro K H α β hα0 hα1 hβ0 hβ1
    have h1 := vrp_onesample Fp.C (B k) hB γ' CS s₀ hγ0 hs₀ hm hn hCo' hCi' Fp.A Fp.hA F G hF hG
      hs₀s hu₀u K H α β hα0 hα1 hβ0 hβ1 (r k) (by
        intro θ; have := hr k θ; rw [hFpA]; exact this)
    refine h1.trans ?_
    have hab : 0 ≤ α + β := by linarith
    have h2 : 2 * (CbdOf γ' CS s₀ KEof / Real.sqrt (B k)) + r k ≤
        2 * CbdOf γ' CS s₀ KEof * (Real.sqrt γ' * opNorm (A k)) + r k := by
      have : CbdOf γ' CS s₀ KEof / Real.sqrt (B k) = CbdOf γ' CS s₀ KEof * (1 / Real.sqrt (B k)) := by ring
      rw [this]
      have h3 : CbdOf γ' CS s₀ KEof * (1 / Real.sqrt (B k)) ≤ CbdOf γ' CS s₀ KEof * (Real.sqrt γ' * opNorm (A k)) := by
        refine mul_le_mul_of_nonneg_left ?_ hCbd
        rw [hFpA] at hinv; exact hinv
      linarith
    rw [mul_div_assoc]
    exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right h2 hBr.le) hab

/-! ## Replacement of the residuals -/

/-- `lem:app-vol-replacement`, snapshot `cr-2026-10-23`. Declaration of record, uniform form in the style
of `lem_app_de_replace`. The sequence `ε` (the paper's `ε_B(𝒥)`) is chosen after the compact `𝒥`, the
constants `C_Σ`, `γ⋆` and the normalized state sequence `A` (`hA`, `hAn`) only, as the source states
(l.699–700). It works for every frozen-state model `Fp` with state `A k`, the size and norm bounds, every
probability space, sample family, time `t`, lag `ℓ`, pair `s, u ∈ 𝒥` and test matrices `F, G` of
operator norm at most one. The two expectations are the frozen buffer (on `S`) and the independent
product buffer (`def_app_vol_product`, on `indepSpaceLaw`). LaTeX, verbatim from `section.tex` (the
whole environment):

```latex
\begin{lemma}[Replacement of the residuals]\label{lem:app-vol-replacement}
Under \cref{assum:app-setup-regime}, let $\mathcal J\subset(0,\infty)$ be
compact. There is a sequence $\varepsilon_B(\mathcal J)\to0$, depending only on
$\mathcal J$, $C_\Sigma$, $\gamma_\star$ and the sequence of states, such that for
every lag $\ell\ge0$
\begin{equation}\label{eqn:app-vol-replacement}
\sup_{s,u\in\mathcal J}\ \sup_{\norm F,\norm G\le1}
\abs{\EE\,\mathcal K^{F,G}_{s,u}(\Mt,M_{t+\ell})-\EE\,\mathcal K^{F,G}_{s,u}(M^{\mathrm g}_t,M^{\mathrm g}_{t+\ell})}\le2\varepsilon_B(\mathcal J),
\end{equation}
the supremum running over all deterministic $F\in\R^{\Nout\times\Nout}$ and
$G\in\R^{\Nin\times\Nin}$ of norm at most one.
\end{lemma}
```
-/
theorem lem_app_vol_replacement (J : Set ℝ) (hJ : IsCompact J) (hJpos : J ⊆ Ioi 0)
    (CSig γstar : ℝ) (m n B : ℕ → ℕ) (A : ∀ k : ℕ, Mat (m k) (n k))
    (hA : ∀ k : ℕ, fro (A k) = 1) (hAn : Tendsto (fun k : ℕ => opNorm (A k)) atTop (𝓝 0)) :
    ∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧
      ∀ (k : ℕ) (Fp : FrozenParams (m k) (n k) (B k)), Fp.A = A k →
        opNorm Fp.C.Sout ≤ CSig → opNorm Fp.C.Sin ≤ CSig →
        ((max (m k) (n k) : ℕ) : ℝ) ≤ γstar * (B k : ℝ) →
        ∀ (Ω' : Type) [MeasurableSpace Ω'] (P : Measure Ω') [IsProbabilityMeasure P]
          (S : FrozenSamples P (m k) (n k) (B k)) (t : ℤ) (ℓ : ℕ) (s u : ℝ),
          s ∈ J → u ∈ J →
          ∀ F : Mat (m k) (m k), opNorm F ≤ 1 → ∀ G : Mat (n k) (n k), opNorm G ≤ 1 →
          |(∫ ω, contractionRes (B k) F G s u (frozenBuf Fp S t ω)
                (frozenBuf Fp S (t + (ℓ : ℤ)) ω) ∂P) -
            (∫ ω, contractionRes (B k) F G s u (def_app_vol_product Fp ω t)
                (def_app_vol_product Fp ω (t + (ℓ : ℤ)))
                ∂(indepSpaceLaw (m k) (n k) (B k)))| ≤ 2 * ε k :=
  vrp_main J hJ hJpos CSig γstar m n B A hA hAn

/-- Regime form of `lem:app-vol-replacement` (`assum:app-setup-regime`), snapshot `cr-2026-10-23`.
Specialization of `lem_app_vol_replacement` to the regime's `A k := (R.F k).A`, `Fp := R.F k`,
with the regime's own samples `S k` on `P k`. The constant `ε` is chosen after the regime (it is
the form used by `cor_app_vol_filtered_replacement_i`). The LaTeX is the docstring of
`lem_app_vol_replacement`. -/
theorem lem_app_vol_replacement_regime {Ω : ℕ → Type} [∀ k, MeasurableSpace (Ω k)]
    (R : SetupRegime) (P : ∀ k, Measure (Ω k)) [∀ k, IsProbabilityMeasure (P k)]
    (S : ∀ k, FrozenSamples (P k) (R.m k) (R.n k) (R.B k))
    (J : Set ℝ) (hJ : IsCompact J) (hJpos : J ⊆ Ioi 0) :
    ∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧
      ∀ (t : ℤ) (ℓ : ℕ) (k : ℕ) (s u : ℝ), s ∈ J → u ∈ J →
        ∀ F : Mat (R.m k) (R.m k), opNorm F ≤ 1 → ∀ G : Mat (R.n k) (R.n k), opNorm G ≤ 1 →
          |(∫ ω, contractionRes (R.B k) F G s u (frozenBuf (R.F k) (S k) t ω)
                (frozenBuf (R.F k) (S k) (t + (ℓ : ℤ)) ω) ∂(P k)) -
            (∫ ω, contractionRes (R.B k) F G s u (def_app_vol_product (R.F k) ω t)
                (def_app_vol_product (R.F k) ω (t + (ℓ : ℤ)))
                ∂(indepSpaceLaw (R.m k) (R.n k) (R.B k)))| ≤ 2 * ε k := by
  obtain ⟨ε, hε, hbound⟩ := lem_app_vol_replacement J hJ hJpos R.CSig R.γstar
    R.m R.n R.B (fun k => (R.F k).A) (fun k => (R.F k).hA) R.diffuse
  refine ⟨ε, hε, ?_⟩
  intro t ℓ k s u hs hu F hF G hG
  exact hbound k (R.F k) rfl (R.normOut k) (R.normIn k) (R.dims k)
    (Ω k) (P k) (S k) t ℓ s u hs hu F hF G hG

/-! ## Replacement for the filtered updates -/

private lemma vfr_summable_mat_of_fro {m n : ℕ} {g : ℕ → Mat m n}
    (hg : Summable fun j => fro (g j)) : Summable g := by
  open scoped Matrix.Norms.Frobenius in
    refine Summable.of_norm ?_
  simpa [fro_eq_norm] using hg

private lemma vfr_frozen_summand_cont {m n B : ℕ} (Fp : FrozenParams m n B) :
    Continuous (fun p : Vec m × Vec n =>
      (dotProduct p.1 (Matrix.mulVec Fp.A p.2)) •
        (rOut Fp.C * outer p.1 p.2 * rIn Fp.C)) := by
  fun_prop

private lemma vfr_frozenBatch_sm {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {m n B : ℕ} (Fp : FrozenParams m n B) (S : FrozenSamples P m n B) (s : ℤ) :
    StronglyMeasurable (frozenBatchG Fp S s) := by
  unfold frozenBatchG
  refine StronglyMeasurable.const_smul ?_ ((B : ℝ))⁻¹
  exact Finset.stronglyMeasurable_fun_sum Finset.univ fun a _ =>
    (vfr_frozen_summand_cont Fp).comp_stronglyMeasurable (S.meas s a).stronglyMeasurable

private lemma vfr_frozenBuf_aesm {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {m n B : ℕ} (Fp : FrozenParams m n B)
    (S : FrozenSamples P m n B) (t : ℤ) : AEStronglyMeasurable (frozenBuf Fp S t) P := by
  letI : TopologicalSpace.PseudoMetrizableSpace (Mat m n) :=
    inferInstanceAs (TopologicalSpace.PseudoMetrizableSpace (Fin m → Fin n → ℝ))
  have hae := (lem_app_setup_ema_law_i Fp S).1
  refine aestronglyMeasurable_of_tendsto_ae atTop (f := fun N ω =>
    ∑ j ∈ Finset.range N, emaW Fp.β j • frozenBatchG Fp S (t + 1 - (j : ℤ)) ω) (fun N => ?_) ?_
  · exact (Finset.stronglyMeasurable_fun_sum (Finset.range N) fun j _ =>
      (vfr_frozenBatch_sm Fp S (t + 1 - (j : ℤ))).const_smul (emaW Fp.β j)).aestronglyMeasurable
  · filter_upwards [hae] with ω hω
    exact (vfr_summable_mat_of_fro (hω t)).hasSum.tendsto_sum_nat

private lemma vfr_indep_summand_cont {m n B : ℕ} (Fp : FrozenParams m n B) :
    Continuous (fun p : ℝ × (Vec m × Vec n) =>
      p.1 • (rOut Fp.C * outer p.2.1 p.2.2 * rIn Fp.C)) := by
  fun_prop

private lemma vfr_indepBatch_sm {m n B : ℕ} (Fp : FrozenParams m n B) (s : ℤ) :
    StronglyMeasurable (fun ω : (ℤ × Fin B) → ℝ × (Vec m × Vec n) => indepBatchG Fp ω s) := by
  apply Measurable.stronglyMeasurable
  unfold indepBatchG
  refine Measurable.const_smul ?_ ((B : ℝ))⁻¹
  exact Finset.measurable_fun_sum Finset.univ fun a _ =>
    (vfr_indep_summand_cont Fp).measurable.comp (measurable_pi_apply (s, a))

private lemma vfr_product_aesm {m n B : ℕ} (Fp : FrozenParams m n B) (t : ℤ) :
    AEStronglyMeasurable (fun ω => def_app_vol_product Fp ω t) (indepSpaceLaw m n B) := by
  letI : TopologicalSpace.PseudoMetrizableSpace (Mat m n) :=
    inferInstanceAs (TopologicalSpace.PseudoMetrizableSpace (Fin m → Fin n → ℝ))
  refine aestronglyMeasurable_of_tendsto_ae atTop (f := fun N ω =>
    ∑ j ∈ Finset.range N, emaW Fp.β j • indepBatchG Fp ω (t + 1 - (j : ℤ))) (fun N => ?_) ?_
  · exact (Finset.stronglyMeasurable_fun_sum (Finset.range N) fun j _ =>
      (vfr_indepBatch_sm Fp (t + 1 - (j : ℤ))).const_smul (emaW Fp.β j)).aestronglyMeasurable
  · filter_upwards [def_app_vol_product_summable Fp] with ω hω
    exact (vfr_summable_mat_of_fro (hω t)).hasSum.tendsto_sum_nat

private lemma vfr_indep_prob (m n B : ℕ) : IsProbabilityMeasure (indepSpaceLaw m n B) := by
  unfold indepSpaceLaw indepSlotLaw
  infer_instance

private lemma vfr_fro_zero {m n : ℕ} : fro (0 : Mat m n) = 0 := by
  unfold fro
  simp

private lemma vfr_product_fro_sq_integrable {m n B : ℕ} (Fp : FrozenParams m n B) (t : ℤ) :
    Integrable (fun ω => fro (def_app_vol_product Fp ω t) ^ 2) (indepSpaceLaw m n B) := by
  letI := vfr_indep_prob m n B
  have hout0 : 0 ≤ Matrix.trace Fp.C.Sout := Fp.C.psdOut.trace_nonneg
  have hin0 : 0 ≤ Matrix.trace Fp.C.Sin := Fp.C.psdIn.trace_nonneg
  by_cases hz : Matrix.trace Fp.C.Sout * Matrix.trace Fp.C.Sin = 0
  · rcases mul_eq_zero.mp hz with hout | hin
    · have hS : Fp.C.Sout = 0 := (Matrix.PosSemidef.trace_eq_zero_iff Fp.C.psdOut).mp hout
      have hr : rOut Fp.C = 0 := by simp [rOut, hS]
      have hp : (fun ω => def_app_vol_product Fp ω t) = fun _ => 0 := by
        funext ω
        simp [def_app_vol_product, indepBatchG, hr]
      have hp' : ∀ ω, def_app_vol_product Fp ω t = 0 := congrFun hp
      simpa only [hp', vfr_fro_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
        using (integrable_const (0 : ℝ) : Integrable (fun _ : (ℤ × Fin B) → ℝ × (Vec m × Vec n) => (0 : ℝ))
          (indepSpaceLaw m n B))
    · have hS : Fp.C.Sin = 0 := (Matrix.PosSemidef.trace_eq_zero_iff Fp.C.psdIn).mp hin
      have hr : rIn Fp.C = 0 := by simp [rIn, hS]
      have hp : (fun ω => def_app_vol_product Fp ω t) = fun _ => 0 := by
        funext ω
        simp [def_app_vol_product, indepBatchG, hr]
      have hp' : ∀ ω, def_app_vol_product Fp ω t = 0 := congrFun hp
      simpa only [hp', vfr_fro_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
        using (integrable_const (0 : ℝ) : Integrable (fun _ : (ℤ × Fin B) → ℝ × (Vec m × Vec n) => (0 : ℝ))
          (indepSpaceLaw m n B))
  · have htr : 0 < Matrix.trace Fp.C.Sout * Matrix.trace Fp.C.Sin :=
      lt_of_le_of_ne (mul_nonneg hout0 hin0) (Ne.symm hz)
    have hs : 0 < sPow Fp.β 2 := by
      rw [sPow_two Fp.hβ.1 Fp.hβ.2]
      exact div_pos (by linarith [Fp.hβ.2]) (by linarith [Fp.hβ.1])
    have houtp : 0 < Matrix.trace Fp.C.Sout := by
      by_contra h
      have : Matrix.trace Fp.C.Sout = 0 := le_antisymm (le_of_not_gt h) hout0
      exact hz (by rw [this, zero_mul])
    have hinp : 0 < Matrix.trace Fp.C.Sin := by
      by_contra h
      have : Matrix.trace Fp.C.Sin = 0 := le_antisymm (le_of_not_gt h) hin0
      exact hz (by rw [this, mul_zero])
    have hm := def_app_vol_product_moment Fp t
    have hpos : 0 < ∫ ω, fro (def_app_vol_product Fp ω t) ^ 2 ∂(indepSpaceLaw m n B) := by
      have hB : (0 : ℝ) < B := by exact_mod_cast Fp.hB
      have : 0 < ((B : ℝ))⁻¹ * ∫ ω, fro (def_app_vol_product Fp ω t) ^ 2
          ∂(indepSpaceLaw m n B) := by
        rw [hm]
        exact mul_pos (mul_pos (div_pos hs (sq_pos_of_pos hB)) houtp) hinp
      nlinarith [inv_pos.mpr hB]
    by_contra hnot
    rw [integral_undef hnot] at hpos
    linarith

private lemma vfr_product_moment_lintegral {m n B : ℕ} (Fp : FrozenParams m n B)
    (γstar CSig : ℝ) (hS : SizeFin Fp.C B γstar CSig) (t : ℤ) :
    ENNReal.ofReal ((B : ℝ)⁻¹) *
        ∫⁻ ω, ENNReal.ofReal (fro (def_app_vol_product Fp ω t) ^ 2)
          ∂(indepSpaceLaw m n B) ≤ ENNReal.ofReal (CSig ^ 2 * γstar ^ 2) := by
  rw [← ofReal_integral_eq_lintegral_ofReal (vfr_product_fro_sq_integrable Fp t)
    (Filter.Eventually.of_forall fun ω => sq_nonneg _),
    ← ENNReal.ofReal_mul (inv_nonneg.2 (Nat.cast_nonneg B))]
  exact ENNReal.ofReal_le_ofReal (def_app_vol_product_moment_le Fp γstar CSig hS t)

private lemma vfr_matrix_inv_meas {m : ℕ} : Measurable (Inv.inv : Mat m m → Mat m m) := by
  have hd : Measurable (fun A : Mat m m => A.det) := by fun_prop
  have ha : Measurable (fun A : Mat m m => A.adjugate) := by fun_prop
  rw [show (Inv.inv : Mat m m → Mat m m) = fun A => Ring.inverse A.det • A.adjugate by
    funext A; exact Matrix.inv_def A]
  rw [Ring.inverse_eq_inv']
  exact (measurable_inv.comp hd).smul ha

private lemma vfr_Rs_meas {D : Type*} [MeasurableSpace D] {m n : ℕ}
    (K : D → Mat m n) (hK : Measurable K) (s : D → ℝ) (hs : Measurable s) :
    Measurable (fun p => Rs (K p) (s p)) := by
  unfold Rs
  apply vfr_matrix_inv_meas.comp
  exact (by fun_prop : Continuous (fun q : Mat m n × ℝ =>
    q.1 * q.1ᵀ + q.2 • (1 : Mat m m))).measurable.comp (hK.prodMk hs)

private lemma vfr_Xs_meas {D : Type*} [MeasurableSpace D] {m n : ℕ}
    (K : D → Mat m n) (hK : Measurable K) (s : D → ℝ) (hs : Measurable s) :
    Measurable (fun p => Xs (K p) (s p)) := by
  unfold Xs
  exact (by fun_prop : Continuous (fun q : Mat m m × Mat m n => q.1 * q.2)).measurable.comp
    ((vfr_Rs_meas K hK s hs).prodMk hK)

private lemma vfr_contractionRes_eq_Xs {m n B : ℕ} (F : Mat m m) (G : Mat n n)
    (s u : ℝ) (hs : 0 < s) (hu : 0 < u) (K H : Mat m n) :
    contractionRes B F G s u K H =
      (B : ℝ)⁻¹ * Matrix.trace (F * Xs K s * G * (Xs H u)ᵀ) := by
  unfold contractionRes contraction
  rw [eqn_app_vol_filters_sharp_i hs, eqn_app_vol_filters_sharp_i hu]

private lemma vfr_borel (m n : ℕ) : BorelSpace (Mat m n) :=
  inferInstanceAs (BorelSpace (Fin m → Fin n → ℝ))

private lemma vfr_sc (m n : ℕ) : SecondCountableTopology (Mat m n) :=
  inferInstanceAs (SecondCountableTopology (Fin m → Fin n → ℝ))

private lemma vfr_trace_pair_cont {m n B : ℕ} (F : Mat m m) (G : Mat n n) :
    Continuous (fun p : Mat m n × Mat m n =>
      (B : ℝ)⁻¹ * Matrix.trace (F * p.1 * G * p.2ᵀ)) := by
  fun_prop

private lemma vfr_trace_pair_meas {D : Type*} [MeasurableSpace D] {m n B : ℕ}
    (F : Mat m m) (G : Mat n n) (X Y : D → Mat m n) (hX : Measurable X) (hY : Measurable Y) :
    Measurable (fun p => (B : ℝ)⁻¹ * Matrix.trace (F * X p * G * (Y p)ᵀ)) := by
  haveI := vfr_borel m n
  haveI := vfr_sc m n
  have hc : Measurable (fun q : Mat m n × Mat m n =>
      (B : ℝ)⁻¹ * Matrix.trace (F * q.1 * G * q.2ᵀ)) :=
    (vfr_trace_pair_cont (B := B) F G).measurable
  have hp : Measurable (fun p => (X p, Y p)) := hX.prodMk hY
  convert hc.comp hp using 1
  rfl

private lemma vfr_param_meas {Ω : Type*} [MeasurableSpace Ω] {m n B : ℕ}
    (F : Mat m m) (G : Mat n n) (K H : Ω → Mat m n) (hK : Measurable K) (hH : Measurable H)
    (ϱ ϱ' : ℝ) (hϱ : 0 < ϱ) (hϱ' : 0 < ϱ') :
    Measurable (fun p : (ℝ × ℝ) × Ω => contractionRes B F G (ϱ + p.1.1 ^ 2) (ϱ' + p.1.2 ^ 2)
      (K p.2) (H p.2)) := by
  rw [show (fun p : (ℝ × ℝ) × Ω => contractionRes B F G
      (ϱ + p.1.1 ^ 2) (ϱ' + p.1.2 ^ 2) (K p.2) (H p.2)) =
      fun p => (B : ℝ)⁻¹ * Matrix.trace
        (F * Xs (K p.2) (ϱ + p.1.1 ^ 2) * G * (Xs (H p.2) (ϱ' + p.1.2 ^ 2))ᵀ) by
    funext p; exact vfr_contractionRes_eq_Xs F G _ _ (by positivity) (by positivity) _ _]
  have hKm : Measurable (fun p : (ℝ × ℝ) × Ω => K p.2) := hK.comp measurable_snd
  have hHm : Measurable (fun p : (ℝ × ℝ) × Ω => H p.2) := hH.comp measurable_snd
  have hs : Measurable (fun p : (ℝ × ℝ) × Ω => ϱ + p.1.1 ^ 2) := by fun_prop
  have hu : Measurable (fun p : (ℝ × ℝ) × Ω => ϱ' + p.1.2 ^ 2) := by fun_prop
  have hX : Measurable (fun p : (ℝ × ℝ) × Ω => Xs (K p.2) (ϱ + p.1.1 ^ 2)) := by
    exact vfr_Xs_meas _ hKm _ hs
  have hY : Measurable (fun p : (ℝ × ℝ) × Ω => Xs (H p.2) (ϱ' + p.1.2 ^ 2)) := by
    exact vfr_Xs_meas _ hHm _ hu
  exact vfr_trace_pair_meas F G _ _ hX hY

private lemma vfr_param_expect_meas {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {m n B : ℕ} (F : Mat m m) (G : Mat n n)
    (K H : Ω → Mat m n) (hK : AEStronglyMeasurable K P) (hH : AEStronglyMeasurable H P)
    (ϱ ϱ' : ℝ) (hϱ : 0 < ϱ) (hϱ' : 0 < ϱ') :
    Measurable (fun p : ℝ × ℝ => ∫ ω, contractionRes B F G (ϱ + p.1 ^ 2) (ϱ' + p.2 ^ 2)
      (K ω) (H ω) ∂P) := by
  let K' := AEStronglyMeasurable.mk K hK
  let H' := AEStronglyMeasurable.mk H hH
  have hm : Measurable (fun p : (ℝ × ℝ) × Ω => contractionRes B F G
      (ϱ + p.1.1 ^ 2) (ϱ' + p.1.2 ^ 2) (K' p.2) (H' p.2)) :=
    vfr_param_meas F G K' H' hK.stronglyMeasurable_mk.measurable
      hH.stronglyMeasurable_mk.measurable ϱ ϱ' hϱ hϱ'
  have heq : ∀ p : ℝ × ℝ,
      (∫ ω, contractionRes B F G (ϱ + p.1 ^ 2) (ϱ' + p.2 ^ 2) (K' ω) (H' ω) ∂P) =
      ∫ ω, contractionRes B F G (ϱ + p.1 ^ 2) (ϱ' + p.2 ^ 2) (K ω) (H ω) ∂P := by
    intro p
    exact integral_congr_ae ((hK.ae_eq_mk.symm.and hH.ae_eq_mk.symm).mono fun ω hω => by
      dsimp [K', H']
      rw [hω.1, hω.2])
  rw [← funext heq]
  exact hm.stronglyMeasurable.integral_prod_right'.measurable

private lemma vfr_intervalIntegrable_of_measurable_bounded (f : ℝ → ℝ) (hf : Measurable f)
    (C a b : ℝ) (hb : ∀ x, |f x| ≤ C) : IntervalIntegrable f volume a b := by
  rw [intervalIntegrable_iff']
  change Integrable f (volume.restrict (Icc (min a b) (max a b)))
  refine Integrable.of_bound (hf.aestronglyMeasurable.restrict) C
    (Filter.Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs]
  exact hb x

private lemma vfr_double_diff (f g : ℝ → ℝ → ℝ) (hf : Measurable (Function.uncurry f))
    (hg : Measurable (Function.uncurry g)) (T C e : ℝ) (hT : 0 ≤ T)
    (hfb : ∀ x y, |f x y| ≤ C) (hgb : ∀ x y, |g x y| ≤ C)
    (hfg : ∀ x ∈ Icc (0 : ℝ) T, ∀ y ∈ Icc (0 : ℝ) T, |f x y - g x y| ≤ e) :
    |(∫ x in (0 : ℝ)..T, (∫ y in (0 : ℝ)..T, f x y)) -
        (∫ x in (0 : ℝ)..T, (∫ y in (0 : ℝ)..T, g x y))| ≤ T ^ 2 * e := by
  have hfm : ∀ x, Measurable (f x) := fun x => hf.comp (measurable_const.prodMk measurable_id)
  have hgm : ∀ x, Measurable (g x) := fun x => hg.comp (measurable_const.prodMk measurable_id)
  have hfi : ∀ x, IntervalIntegrable (f x) volume 0 T := fun x =>
    vfr_intervalIntegrable_of_measurable_bounded (f x) (hfm x) C 0 T (hfb x)
  have hgi : ∀ x, IntervalIntegrable (g x) volume 0 T := fun x =>
    vfr_intervalIntegrable_of_measurable_bounded (g x) (hgm x) C 0 T (hgb x)
  have hFmeas : Measurable (fun x => ∫ y in (0 : ℝ)..T, f x y) := by
    rw [show (fun x => ∫ y in (0 : ℝ)..T, f x y) =
        fun x => ∫ y in Ioc (0 : ℝ) T, f x y by funext x; exact intervalIntegral.integral_of_le hT]
    exact hf.stronglyMeasurable.integral_prod_right'.measurable
  have hGmeas : Measurable (fun x => ∫ y in (0 : ℝ)..T, g x y) := by
    rw [show (fun x => ∫ y in (0 : ℝ)..T, g x y) =
        fun x => ∫ y in Ioc (0 : ℝ) T, g x y by funext x; exact intervalIntegral.integral_of_le hT]
    exact hg.stronglyMeasurable.integral_prod_right'.measurable
  have hFb : ∀ x, |∫ y in (0 : ℝ)..T, f x y| ≤ T * C := fun x => by
    simpa [Real.norm_eq_abs, abs_of_nonneg hT, mul_comm] using
      (intervalIntegral.norm_integral_le_of_norm_le_const (f := f x) (C := C) (a := (0 : ℝ)) (b := T)
        (fun y _ => by simpa [Real.norm_eq_abs] using hfb x y))
  have hGb : ∀ x, |∫ y in (0 : ℝ)..T, g x y| ≤ T * C := fun x => by
    simpa [Real.norm_eq_abs, abs_of_nonneg hT, mul_comm] using
      (intervalIntegral.norm_integral_le_of_norm_le_const (f := g x) (C := C) (a := (0 : ℝ)) (b := T)
        (fun y _ => by simpa [Real.norm_eq_abs] using hgb x y))
  have hFi := vfr_intervalIntegrable_of_measurable_bounded _ hFmeas (T * C) 0 T hFb
  have hGi := vfr_intervalIntegrable_of_measurable_bounded _ hGmeas (T * C) 0 T hGb
  have hinner : ∀ x ∈ Icc (0 : ℝ) T,
      |∫ y in (0 : ℝ)..T, f x y - g x y| ≤ T * e := by
    intro x hx
    simpa [Real.norm_eq_abs, abs_of_nonneg hT, mul_comm] using
      (intervalIntegral.norm_integral_le_of_norm_le_const (f := fun y => f x y - g x y)
        (C := e) (a := (0 : ℝ)) (b := T)
        (fun y hy => by
          simpa [Real.norm_eq_abs] using hfg x hx y
            (Ioc_subset_Icc_self (by simpa [uIoc_of_le hT] using hy))))
  have hout := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := T)
    (f := fun x => (∫ y in (0 : ℝ)..T, f x y) - (∫ y in (0 : ℝ)..T, g x y))
    (C := T * e) (fun x hx => by
      rw [Real.norm_eq_abs, ← intervalIntegral.integral_sub (hfi x) (hgi x)]
      exact hinner x (Ioc_subset_Icc_self (by simpa [uIoc_of_le hT] using hx)))
  rw [Real.norm_eq_abs, sub_zero, abs_of_nonneg hT] at hout
  let A := ∫ x in (0 : ℝ)..T, ∫ y in (0 : ℝ)..T, f x y
  let B := ∫ x in (0 : ℝ)..T, ∫ y in (0 : ℝ)..T, g x y
  change |A - B| ≤ T ^ 2 * e
  have heq : A - B = ∫ x in (0 : ℝ)..T, ((∫ y in (0 : ℝ)..T, f x y) -
      (∫ y in (0 : ℝ)..T, g x y)) := by
    dsimp [A, B]
    rw [intervalIntegral.integral_sub hFi hGi]
  rw [heq]
  nlinarith

private lemma vfr_filtered_expect_bound {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {m n B : ℕ} (hB : 0 < B) (γstar : ℝ)
    (hdim : ((min m n : ℕ) : ℝ) ≤ γstar * B) (F : Mat m m) (G : Mat n n)
    (hF : opNorm F ≤ 1) (hG : opNorm G ≤ 1) (K H : Ω → Mat m n)
    (ϱ ϱ' : ℝ) (hϱ : 0 < ϱ) (hϱ' : 0 < ϱ') :
    |∫ ω, contraction B F G (omegaF ϱ) (omegaF ϱ') (K ω) (H ω) ∂P| ≤ |γstar| := by
  have hs := lem_app_vol_sharp_ii (s := ϱ) (by exact hϱ) hϱ
  have hs' := lem_app_vol_sharp_ii (s := ϱ') (by exact hϱ') hϱ'
  have hp : ∀ ω, |contraction B F G (omegaF ϱ) (omegaF ϱ') (K ω) (H ω)| ≤ |γstar| := by
    intro ω
    have h := lem_app_vol_finite_i hB γstar hdim F G hF hG _ _ hs.2.1 hs'.2.1 (K ω) (H ω)
    rw [hs.2.2.2.2.1, hs'.2.2.2.2.1, mul_one, mul_one] at h
    exact h.trans (le_abs_self γstar)
  simpa [Real.norm_eq_abs] using
    (norm_integral_le_of_norm_le_const (μ := P)
      (f := fun ω => contraction B F G (omegaF ϱ) (omegaF ϱ') (K ω) (H ω)) (C := |γstar|)
      (Filter.Eventually.of_forall fun ω => by simpa [Real.norm_eq_abs] using hp ω))

private lemma vfr_param_expect_bound {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {m n B : ℕ} (hB : 0 < B) (γstar : ℝ)
    (hdim : ((min m n : ℕ) : ℝ) ≤ γstar * B) (F : Mat m m) (G : Mat n n)
    (hF : opNorm F ≤ 1) (hG : opNorm G ≤ 1) (K H : Ω → Mat m n)
    (ϱ ϱ' x y : ℝ) (hϱ : 0 < ϱ) (hϱ' : 0 < ϱ') :
    |∫ ω, contractionRes B F G (ϱ + x ^ 2) (ϱ' + y ^ 2) (K ω) (H ω) ∂P| ≤
      |γstar| * (1 / (2 * Real.sqrt ϱ)) * (1 / (2 * Real.sqrt ϱ')) := by
  have hx : 0 < ϱ + x ^ 2 := by positivity
  have hy : 0 < ϱ' + y ^ 2 := by positivity
  have hs := lem_app_vol_sharp_ii (s := ϱ + x ^ 2) hx hϱ
  have hs' := lem_app_vol_sharp_ii (s := ϱ' + y ^ 2) hy hϱ'
  have hp : ∀ ω, |contractionRes B F G (ϱ + x ^ 2) (ϱ' + y ^ 2) (K ω) (H ω)| ≤
      |γstar| * (1 / (2 * Real.sqrt ϱ)) * (1 / (2 * Real.sqrt ϱ')) := by
    intro ω
    have h := lem_app_vol_finite_i hB γstar hdim F G hF hG _ _ hs.1 hs'.1 (K ω) (H ω)
    rw [hs.2.2.1, hs'.2.2.1] at h
    have h1 : 1 / (2 * Real.sqrt (ϱ + x ^ 2)) ≤ 1 / (2 * Real.sqrt ϱ) :=
      one_div_le_one_div_of_le (by positivity) (by gcongr; nlinarith [sq_nonneg x])
    have h2 : 1 / (2 * Real.sqrt (ϱ' + y ^ 2)) ≤ 1 / (2 * Real.sqrt ϱ') :=
      one_div_le_one_div_of_le (by positivity) (by gcongr; nlinarith [sq_nonneg y])
    calc
      _ ≤ γstar * (1 / (2 * Real.sqrt (ϱ + x ^ 2))) *
          (1 / (2 * Real.sqrt (ϱ' + y ^ 2))) := h
      _ ≤ |γstar| * (1 / (2 * Real.sqrt (ϱ + x ^ 2))) *
          (1 / (2 * Real.sqrt (ϱ' + y ^ 2))) := by gcongr; exact le_abs_self γstar
      _ ≤ _ := by gcongr
  simpa [Real.norm_eq_abs] using
    (norm_integral_le_of_norm_le_const (μ := P)
      (f := fun ω => contractionRes B F G (ϱ + x ^ 2) (ϱ' + y ^ 2) (K ω) (H ω))
      (Filter.Eventually.of_forall fun ω => by
        convert hp ω using 1 <;> ring))

private lemma vfr_exists_vanishing_majorant (E : ℕ → Set ℝ)
    (hne : ∀ k, (E k).Nonempty) (hnn : ∀ k x, x ∈ E k → 0 ≤ x)
    (hbdd : ∀ k, BddAbove (E k))
    (hvan : ∀ δ : ℝ, 0 < δ → Filter.Eventually (fun k => ∀ x ∈ E k, x < δ) atTop) :
    ∃ e : ℕ → ℝ, Tendsto e atTop (nhds 0) ∧ ∀ k x, x ∈ E k → x ≤ e k := by
  let e : ℕ → ℝ := fun k => sSup (E k)
  have heb : ∀ k x, x ∈ E k → x ≤ e k := fun k x hx => le_csSup (hbdd k) hx
  have he0 : ∀ k, 0 ≤ e k := by
    intro k
    obtain ⟨x, hx⟩ := hne k
    exact (hnn k x hx).trans (heb k x hx)
  refine ⟨e, ?_, heb⟩
  rw [Metric.tendsto_atTop]
  intro δ hδ
  obtain ⟨N, hN⟩ := (eventually_atTop.1 (hvan (δ / 2) (by positivity)))
  refine ⟨N, fun k hk => ?_⟩
  rw [dist_zero_right, Real.norm_eq_abs, abs_of_nonneg (he0 k)]
  exact (csSup_le (hne k) fun x hx => ((hN k hk) x hx).le).trans_lt (by linarith)

/-- The square-truncation estimate with the natural a.e.-measurability hypothesis. -/
private lemma vfr_square_ae {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {m n B : ℕ} (hB : 0 < B) (γstar CM : ℝ)
    (hdim : ((min m n : ℕ) : ℝ) ≤ γstar * B)
    (F : Mat m m) (G : Mat n n) (hF : opNorm F ≤ 1) (hG : opNorm G ≤ 1)
    (K H : Ω → Mat m n) (hK : AEStronglyMeasurable K P) (hH : AEStronglyMeasurable H P)
    (hKm : ENNReal.ofReal ((B : ℝ)⁻¹) * ∫⁻ ω, ENNReal.ofReal (fro (K ω) ^ 2) ∂P ≤
      ENNReal.ofReal CM)
    (hHm : ENNReal.ofReal ((B : ℝ)⁻¹) * ∫⁻ ω, ENNReal.ofReal (fro (H ω) ^ 2) ∂P ≤
      ENNReal.ofReal CM)
    (ϱ ϱ' T : ℝ) (hϱ : 0 < ϱ) (hϱ' : 0 < ϱ') (hT : 0 < T) :
    |(∫ ω, contraction B F G (omegaF ϱ) (omegaF ϱ') (K ω) (H ω) ∂P) -
        (4 / Real.pi ^ 2) * ∫ x in (0 : ℝ)..T, ∫ y in (0 : ℝ)..T,
          ∫ ω, contraction B F G (iotaF (ϱ + x ^ 2)) (iotaF (ϱ' + y ^ 2)) (K ω) (H ω) ∂P|
      ≤ 4 * Real.sqrt (γstar * CM) / (Real.pi * T) := by
  let K' := AEStronglyMeasurable.mk K hK
  let H' := AEStronglyMeasurable.mk H hH
  have hK' : Measurable K' := hK.stronglyMeasurable_mk.measurable
  have hH' : Measurable H' := hH.stronglyMeasurable_mk.measurable
  have hKae : K' =ᵐ[P] K := hK.ae_eq_mk.symm
  have hHae : H' =ᵐ[P] H := hH.ae_eq_mk.symm
  have hKm' : ENNReal.ofReal ((B : ℝ)⁻¹) * ∫⁻ ω, ENNReal.ofReal (fro (K' ω) ^ 2) ∂P ≤
      ENNReal.ofReal CM := by
    have he : (∫⁻ ω, ENNReal.ofReal (fro (K' ω) ^ 2) ∂P) =
        ∫⁻ ω, ENNReal.ofReal (fro (K ω) ^ 2) ∂P := by
      apply lintegral_congr_ae
      filter_upwards [hKae] with ω hω
      rw [hω]
    rw [he]
    exact hKm
  have hHm' : ENNReal.ofReal ((B : ℝ)⁻¹) * ∫⁻ ω, ENNReal.ofReal (fro (H' ω) ^ 2) ∂P ≤
      ENNReal.ofReal CM := by
    have he : (∫⁻ ω, ENNReal.ofReal (fro (H' ω) ^ 2) ∂P) =
        ∫⁻ ω, ENNReal.ofReal (fro (H ω) ^ 2) ∂P := by
      apply lintegral_congr_ae
      filter_upwards [hHae] with ω hω
      rw [hω]
    rw [he]
    exact hHm
  have hs := lem_app_vol_square_ii P hB γstar CM hdim F G hF hG K' H'
    (fun i j => (measurable_pi_apply j).comp ((measurable_pi_apply i).comp hK'))
    (fun i j => (measurable_pi_apply j).comp ((measurable_pi_apply i).comp hH'))
    hKm' hHm' ϱ ϱ' T hϱ hϱ' hT
  have hpair : ∀ᵐ ω ∂P, K' ω = K ω ∧ H' ω = H ω := hKae.and hHae
  have hbase : (∫ ω, contraction B F G (omegaF ϱ) (omegaF ϱ') (K' ω) (H' ω) ∂P) =
      ∫ ω, contraction B F G (omegaF ϱ) (omegaF ϱ') (K ω) (H ω) ∂P :=
    integral_congr_ae (hpair.mono fun ω hω => by
      change contraction B F G (omegaF ϱ) (omegaF ϱ') (K' ω) (H' ω) = _
      rw [hω.1, hω.2])
  have hinner : ∀ x y : ℝ,
      (∫ ω, contraction B F G (iotaF (ϱ + x ^ 2)) (iotaF (ϱ' + y ^ 2)) (K' ω) (H' ω) ∂P) =
      ∫ ω, contraction B F G (iotaF (ϱ + x ^ 2)) (iotaF (ϱ' + y ^ 2)) (K ω) (H ω) ∂P :=
    fun x y => integral_congr_ae (hpair.mono fun ω hω => by
      change contraction B F G (iotaF (ϱ + x ^ 2)) (iotaF (ϱ' + y ^ 2)) (K' ω) (H' ω) = _
      rw [hω.1, hω.2])
  rw [hbase] at hs
  simp_rw [hinner] at hs
  exact hs

/-- `cor:app-vol-filtered-replacement`, first display, snapshot `cr-2026-10-23`. Declaration of record
for the filtered replacement `sup_{ϱ,ϱ' ∈ I} sup_{‖F‖,‖G‖≤1} |𝔼 𝒦^{F,G}[ω_ϱ,ω_ϱ'](M_t,M_{t+ℓ}) −
𝔼 𝒦^{F,G}[ω_ϱ,ω_ϱ'](M^g_t,M^g_{t+ℓ})| → 0`, with a sequence `ε'` independent of the lag and of
the time. The regime interval is `I = Icc R.ϱlo R.ϱhi`. LaTeX, verbatim from `section.tex`:

```latex
\begin{corollary}[Replacement for the filtered updates]\label{cor:app-vol-filtered-replacement}
Under \cref{assum:app-setup-regime} there is a sequence $\varepsilon'_B\to0$,
independent of the lag, such that for every $\ell\ge0$
\begin{equation}\label{eqn:app-vol-filtered-replacement}
\sup_{\ridge,\ridge'\in I}\ \sup_{\norm F,\norm G\le1}
\abs{\EE\,\mathcal K^{F,G}[\omega_\ridge,\omega_{\ridge'}](\Mt,M_{t+\ell})-\EE\,\mathcal K^{F,G}[\omega_\ridge,\omega_{\ridge'}](M^{\mathrm g}_t,M^{\mathrm g}_{t+\ell})}\le\varepsilon'_B .
\end{equation}
Consequently, for symmetric $F,G$ with $\norm F,\norm G\le1$, the tested lag
covariances of \cref{def:app-vol-lag} and their independent counterparts
$C^{\mathrm g}_\ell[F,G](\ridge,\ridge')\defeq B^{-1}\EE\Tr[F\,{\mathsf S}^{\mathrm g}_t(\ridge)\,G\,{\mathsf S}^{\mathrm g}_{t+\ell}(\ridge')^\T]$ satisfy
\begin{equation}\label{eqn:app-vol-C-replacement}
\sup_{\ridge,\ridge'\in I}\abs{C_\ell[F,G](\ridge,\ridge')-C^{\mathrm g}_\ell[F,G](\ridge,\ridge')}\le\varepsilon'_B+\frac{(C_\Sigma\ridge_-^{-1/2}+\varepsilon_B)^2}{B}.
\end{equation}
\end{corollary}
```
-/
theorem cor_app_vol_filtered_replacement_i {Ω : ℕ → Type} [∀ k, MeasurableSpace (Ω k)]
    (R : SetupRegime) (P : ∀ k, Measure (Ω k)) [∀ k, IsProbabilityMeasure (P k)]
    (S : ∀ k, FrozenSamples (P k) (R.m k) (R.n k) (R.B k)) :
    ∃ ε' : ℕ → ℝ, Tendsto ε' atTop (𝓝 0) ∧
      ∀ (t : ℤ) (ℓ : ℕ) (k : ℕ) (ϱ ϱ' : ℝ), ϱ ∈ Icc R.ϱlo R.ϱhi → ϱ' ∈ Icc R.ϱlo R.ϱhi →
        ∀ F : Mat (R.m k) (R.m k), opNorm F ≤ 1 → ∀ G : Mat (R.n k) (R.n k), opNorm G ≤ 1 →
          |(∫ ω, contraction (R.B k) F G (omegaF ϱ) (omegaF ϱ')
                (frozenBuf (R.F k) (S k) t ω) (frozenBuf (R.F k) (S k) (t + (ℓ : ℤ)) ω) ∂(P k)) -
            (∫ ω, contraction (R.B k) F G (omegaF ϱ) (omegaF ϱ')
                (def_app_vol_product (R.F k) ω t) (def_app_vol_product (R.F k) ω (t + (ℓ : ℤ)))
                ∂(indepSpaceLaw (R.m k) (R.n k) (R.B k)))| ≤ ε' k := by
  letI vfr_prob_seq (k : ℕ) : IsProbabilityMeasure
      (indepSpaceLaw (R.m k) (R.n k) (R.B k)) := vfr_indep_prob _ _ _
  let err : ∀ k : ℕ, ℤ → ℕ → ℝ → ℝ → Mat (R.m k) (R.m k) →
      Mat (R.n k) (R.n k) → ℝ := fun k t ℓ ϱ ϱ' F G =>
    |(∫ ω, contraction (R.B k) F G (omegaF ϱ) (omegaF ϱ')
          (frozenBuf (R.F k) (S k) t ω) (frozenBuf (R.F k) (S k) (t + (ℓ : ℤ)) ω) ∂(P k)) -
      (∫ ω, contraction (R.B k) F G (omegaF ϱ) (omegaF ϱ')
          (def_app_vol_product (R.F k) ω t) (def_app_vol_product (R.F k) ω (t + (ℓ : ℤ)))
          ∂(indepSpaceLaw (R.m k) (R.n k) (R.B k)))|
  let E : ℕ → Set ℝ := fun k => {x | ∃ (t : ℤ) (ℓ : ℕ) (ϱ ϱ' : ℝ),
    ϱ ∈ Icc R.ϱlo R.ϱhi ∧ ϱ' ∈ Icc R.ϱlo R.ϱhi ∧
    ∃ (F : Mat (R.m k) (R.m k)), opNorm F ≤ 1 ∧
    ∃ (G : Mat (R.n k) (R.n k)), opNorm G ≤ 1 ∧ x = err k t ℓ ϱ ϱ' F G}
  have hdim : ∀ k, ((min (R.m k) (R.n k) : ℕ) : ℝ) ≤ R.γstar * R.B k := fun k =>
    (by exact_mod_cast min_le_max : ((min (R.m k) (R.n k) : ℕ) : ℝ) ≤ max (R.m k) (R.n k)) |>.trans (R.dims k)
  have hEne : ∀ k, (E k).Nonempty := by
    intro k
    refine ⟨err k 0 0 R.ϱlo R.ϱlo 0 0, 0, 0, R.ϱlo, R.ϱlo,
      ⟨le_rfl, R.hϱ.2⟩, ⟨le_rfl, R.hϱ.2⟩, 0, ?_, 0, ?_, rfl⟩
    · simp [opNorm]
    · simp [opNorm]
  have hEnn : ∀ k x, x ∈ E k → 0 ≤ x := by
    rintro k x ⟨t, ℓ, ϱ, ϱ', hϱ, hϱ', F, hF, G, hG, rfl⟩
    exact abs_nonneg _
  have hEbdd : ∀ k, BddAbove (E k) := by
    intro k
    refine ⟨2 * |R.γstar|, ?_⟩
    rintro x ⟨t, ℓ, ϱ, ϱ', hϱ, hϱ', F, hF, G, hG, rfl⟩
    have hf := vfr_filtered_expect_bound (P k) (R.F k).hB R.γstar (hdim k) F G hF hG
      (fun ω => frozenBuf (R.F k) (S k) t ω)
      (fun ω => frozenBuf (R.F k) (S k) (t + (ℓ : ℤ)) ω) ϱ ϱ' (R.hϱ.1.trans_le hϱ.1)
      (R.hϱ.1.trans_le hϱ'.1)
    have hg := vfr_filtered_expect_bound (indepSpaceLaw (R.m k) (R.n k) (R.B k))
      (R.F k).hB R.γstar (hdim k) F G hF hG
      (fun ω => def_app_vol_product (R.F k) ω t)
      (fun ω => def_app_vol_product (R.F k) ω (t + (ℓ : ℤ))) ϱ ϱ'
      (R.hϱ.1.trans_le hϱ.1) (R.hϱ.1.trans_le hϱ'.1)
    exact (abs_sub _ _).trans (by linarith)
  have hγ : 0 ≤ R.γstar := by
    have hB : (0 : ℝ) < R.B 0 := by exact_mod_cast (R.F 0).hB
    have hm : (0 : ℝ) ≤ ((max (R.m 0) (R.n 0) : ℕ) : ℝ) := Nat.cast_nonneg _
    nlinarith [R.dims 0]
  have hvan : ∀ δ : ℝ, 0 < δ → Filter.Eventually (fun k => ∀ x ∈ E k, x < δ) atTop := by
    intro δ hδ
    let CM : ℝ := max (R.CSig ^ 2 * (R.γstar + 2) ^ 2) (R.CSig ^ 2 * R.γstar ^ 2)
    have hCM : 0 ≤ CM := le_max_of_le_right (mul_nonneg (sq_nonneg _) (sq_nonneg _))
    let D : ℝ := 8 * Real.sqrt (R.γstar * CM) / Real.pi
    have hD : 0 ≤ D := by positivity
    let T : ℝ := max 1 (2 * D / δ + 1)
    have hT1 : 1 ≤ T := le_max_left _ _
    have hT : 0 < T := lt_of_lt_of_le zero_lt_one hT1
    have htail : 8 * Real.sqrt (R.γstar * CM) / (Real.pi * T) < δ / 2 := by
      have hbig : 2 * D / δ < T := lt_of_lt_of_le (lt_add_one _) (le_max_right _ _)
      have hpi : 0 < Real.pi := Real.pi_pos
      have heq : 8 * Real.sqrt (R.γstar * CM) / (Real.pi * T) = D / T := by
        dsimp [D]
        field_simp
      rw [heq, div_lt_iff₀ hT]
      rw [div_lt_iff₀ hδ] at hbig
      nlinarith
    let J : Set ℝ := Icc R.ϱlo (R.ϱhi + T ^ 2)
    have hJ : IsCompact J := isCompact_Icc
    have hJpos : J ⊆ Ioi 0 := fun s hs => R.hϱ.1.trans_le hs.1
    obtain ⟨ε, hε, hrep⟩ := lem_app_vol_replacement_regime R P S J hJ hJpos
    have hsmall : Filter.Eventually (fun k => |ε k| < δ * Real.pi ^ 2 / (16 * T ^ 2)) atTop := by
      have hpos : 0 < δ * Real.pi ^ 2 / (16 * T ^ 2) := by positivity
      simpa [Real.dist_eq] using (Metric.tendsto_atTop.1 hε _ hpos)
    filter_upwards [hsmall] with k hk
    intro z hz
    rcases hz with ⟨t, ℓ, ϱ, ϱ', hϱI, hϱ'I, F, hF, G, hG, rfl⟩
    have hϱ : 0 < ϱ := R.hϱ.1.trans_le hϱI.1
    have hϱ' : 0 < ϱ' := R.hϱ.1.trans_le hϱ'I.1
    have hm : (R.m k : ℝ) ≤ R.γstar * R.B k :=
      (show (R.m k : ℝ) ≤ (max (R.m k) (R.n k) : ℕ) by exact_mod_cast le_max_left _ _).trans (R.dims k)
    have hn : (R.n k : ℝ) ≤ R.γstar * R.B k :=
      (show (R.n k : ℝ) ≤ (max (R.m k) (R.n k) : ℕ) by exact_mod_cast le_max_right _ _).trans (R.dims k)
    have hsize : SizeFin (R.F k).C (R.B k) R.γstar R.CSig :=
      ⟨R.dims k, R.normOut k, R.normIn k⟩
    have hfrozen (s : ℤ) : ENNReal.ofReal (((R.B k : ℕ) : ℝ)⁻¹) *
        ∫⁻ ω, ENNReal.ofReal (fro (frozenBuf (R.F k) (S k) s ω) ^ 2) ∂(P k) ≤ ENNReal.ofReal CM := by
      exact (lem_app_vol_square_iii (R.F k) (S k) R.CSig R.γstar (R.normOut k)
        (R.normIn k) hm hn s).trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))
    have hprod (s : ℤ) : ENNReal.ofReal (((R.B k : ℕ) : ℝ)⁻¹) *
        ∫⁻ ω, ENNReal.ofReal (fro (def_app_vol_product (R.F k) ω s) ^ 2)
          ∂(indepSpaceLaw (R.m k) (R.n k) (R.B k)) ≤ ENNReal.ofReal CM := by
      exact (vfr_product_moment_lintegral (R.F k) R.γstar R.CSig hsize s).trans
        (ENNReal.ofReal_le_ofReal (le_max_right _ _))
    let af : ℝ := ∫ ω, contraction (R.B k) F G (omegaF ϱ) (omegaF ϱ')
      (frozenBuf (R.F k) (S k) t ω) (frozenBuf (R.F k) (S k) (t + (ℓ : ℤ)) ω) ∂(P k)
    let ag : ℝ := ∫ ω, contraction (R.B k) F G (omegaF ϱ) (omegaF ϱ')
      (def_app_vol_product (R.F k) ω t) (def_app_vol_product (R.F k) ω (t + (ℓ : ℤ)))
      ∂(indepSpaceLaw (R.m k) (R.n k) (R.B k))
    let qf : ℝ := (4 / Real.pi ^ 2) * ∫ x in (0 : ℝ)..T, ∫ y in (0 : ℝ)..T,
      ∫ ω, contractionRes (R.B k) F G (ϱ + x ^ 2) (ϱ' + y ^ 2)
        (frozenBuf (R.F k) (S k) t ω) (frozenBuf (R.F k) (S k) (t + (ℓ : ℤ)) ω) ∂(P k)
    let qg : ℝ := (4 / Real.pi ^ 2) * ∫ x in (0 : ℝ)..T, ∫ y in (0 : ℝ)..T,
      ∫ ω, contractionRes (R.B k) F G (ϱ + x ^ 2) (ϱ' + y ^ 2)
        (def_app_vol_product (R.F k) ω t) (def_app_vol_product (R.F k) ω (t + (ℓ : ℤ)))
        ∂(indepSpaceLaw (R.m k) (R.n k) (R.B k))
    have hsf : |af - qf| ≤ 4 * Real.sqrt (R.γstar * CM) / (Real.pi * T) := by
      exact vfr_square_ae (P k) (R.F k).hB R.γstar CM (hdim k) F G hF hG _ _
        (vfr_frozenBuf_aesm (R.F k) (S k) t)
        (vfr_frozenBuf_aesm (R.F k) (S k) (t + (ℓ : ℤ))) (hfrozen t) (hfrozen (t + (ℓ : ℤ)))
        ϱ ϱ' T hϱ hϱ' hT
    have hsg : |ag - qg| ≤ 4 * Real.sqrt (R.γstar * CM) / (Real.pi * T) := by
      exact vfr_square_ae (indepSpaceLaw (R.m k) (R.n k) (R.B k)) (R.F k).hB R.γstar CM
        (hdim k) F G hF hG _ _ (vfr_product_aesm (R.F k) t)
        (vfr_product_aesm (R.F k) (t + (ℓ : ℤ))) (hprod t) (hprod (t + (ℓ : ℤ)))
        ϱ ϱ' T hϱ hϱ' hT
    let ff : ℝ → ℝ → ℝ := fun x y => ∫ ω, contractionRes (R.B k) F G
      (ϱ + x ^ 2) (ϱ' + y ^ 2) (frozenBuf (R.F k) (S k) t ω)
      (frozenBuf (R.F k) (S k) (t + (ℓ : ℤ)) ω) ∂(P k)
    let fg : ℝ → ℝ → ℝ := fun x y => ∫ ω, contractionRes (R.B k) F G
      (ϱ + x ^ 2) (ϱ' + y ^ 2) (def_app_vol_product (R.F k) ω t)
      (def_app_vol_product (R.F k) ω (t + (ℓ : ℤ)))
      ∂(indepSpaceLaw (R.m k) (R.n k) (R.B k))
    have hffm : Measurable (Function.uncurry ff) := vfr_param_expect_meas (P k) F G _ _
      (vfr_frozenBuf_aesm (R.F k) (S k) t) (vfr_frozenBuf_aesm (R.F k) (S k) (t + (ℓ : ℤ))) ϱ ϱ' hϱ hϱ'
    have hfgm : Measurable (Function.uncurry fg) :=
      vfr_param_expect_meas (indepSpaceLaw (R.m k) (R.n k) (R.B k)) F G _ _
        (vfr_product_aesm (R.F k) t) (vfr_product_aesm (R.F k) (t + (ℓ : ℤ))) ϱ ϱ' hϱ hϱ'
    let C : ℝ := |R.γstar| * (1 / (2 * Real.sqrt ϱ)) * (1 / (2 * Real.sqrt ϱ'))
    have hffb : ∀ x y, |ff x y| ≤ C := fun x y => vfr_param_expect_bound (P k)
      (R.F k).hB R.γstar (hdim k) F G hF hG _ _ ϱ ϱ' x y hϱ hϱ'
    have hfgb : ∀ x y, |fg x y| ≤ C := fun x y => vfr_param_expect_bound
      (indepSpaceLaw (R.m k) (R.n k) (R.B k)) (R.F k).hB R.γstar (hdim k) F G hF hG _ _
      ϱ ϱ' x y hϱ hϱ'
    have hrepl : ∀ x ∈ Icc (0 : ℝ) T, ∀ y ∈ Icc (0 : ℝ) T, |ff x y - fg x y| ≤ 2 * ε k := by
      intro x hx y hy
      apply hrep t ℓ k (ϱ + x ^ 2) (ϱ' + y ^ 2)
      · constructor
        · change R.ϱlo ≤ ϱ + x ^ 2
          nlinarith [hϱI.1, sq_nonneg x]
        · change ϱ + x ^ 2 ≤ R.ϱhi + T ^ 2
          nlinarith [hϱI.2, mul_self_le_mul_self hx.1 hx.2]
      · constructor
        · change R.ϱlo ≤ ϱ' + y ^ 2
          nlinarith [hϱ'I.1, sq_nonneg y]
        · change ϱ' + y ^ 2 ≤ R.ϱhi + T ^ 2
          nlinarith [hϱ'I.2, mul_self_le_mul_self hy.1 hy.2]
      · exact hF
      · exact hG
    have hdbl := vfr_double_diff ff fg hffm hfgm T C (2 * ε k) hT.le hffb hfgb hrepl
    dsimp [ff, fg] at hdbl
    have hq : |qf - qg| ≤ (4 / Real.pi ^ 2) * (T ^ 2 * (2 * ε k)) := by
      dsimp [qf, qg]
      rw [← mul_sub]
      rw [abs_mul, abs_of_pos (by positivity : 0 < 4 / Real.pi ^ 2)]
      exact mul_le_mul_of_nonneg_left hdbl (by positivity)
    have hqsmall : |qf - qg| < δ / 2 := by
      refine hq.trans_lt ?_
      have heps : ε k ≤ |ε k| := le_abs_self _
      have hpi : 0 < Real.pi := Real.pi_pos
      have hT2 : 0 < T ^ 2 := sq_pos_of_pos hT
      calc
        (4 / Real.pi ^ 2) * (T ^ 2 * (2 * ε k))
            ≤ (4 / Real.pi ^ 2) * (T ^ 2 * (2 * |ε k|)) := by gcongr
        _ < δ / 2 := by
          rw [lt_div_iff₀ (by positivity : 0 < 16 * T ^ 2)] at hk
          field_simp
          nlinarith
    change |af - ag| < δ
    have htri : |af - ag| ≤ |af - qf| + |qf - qg| + |qg - ag| := by
      calc
        |af - ag| = |(af - qf) + (qf - qg) + (qg - ag)| := by ring_nf
        _ ≤ |af - qf| + |qf - qg| + |qg - ag| := by
          exact (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    have hsums : |af - qf| + |qg - ag| ≤ 8 * Real.sqrt (R.γstar * CM) / (Real.pi * T) := by
      have hsg' : |qg - ag| ≤ 4 * Real.sqrt (R.γstar * CM) / (Real.pi * T) := by
        rw [abs_sub_comm]
        exact hsg
      ring_nf at hsf hsg' ⊢
      linarith
    linarith
  obtain ⟨ε', hε', hmaj⟩ := vfr_exists_vanishing_majorant E hEne hEnn hEbdd hvan
  refine ⟨ε', hε', ?_⟩
  intro t ℓ k ϱ ϱ' hϱ hϱ' F hF G hG
  exact hmaj k _ ⟨t, ℓ, ϱ, ϱ', hϱ, hϱ', F, hF, G, hG, rfl⟩

/-- `cor:app-vol-filtered-replacement`, second display, snapshot `cr-2026-10-23`. Declaration of record
for the tested lag covariance bound `sup_{ϱ,ϱ' ∈ I} |C_ℓ[F,G](ϱ,ϱ') − C^g_ℓ[F,G](ϱ,ϱ')| ≤ ε'_B +
(C_Σ ϱ₋^{-1/2} + ε_B)² / B` for symmetric `F, G` of norm at most one. Section-C input: `εB` is the
sequence `ε_B` of `thm:app-drift-mean` and `hmean` its bound (`Half.lean` convention, quantified over
all times). `C_ℓ` is `def_app_vol_lag` (centred); `C^g_ℓ` is the uncentred independent covariance, as
written in the source. LaTeX, verbatim from `section.tex` (the whole environment):

```latex
\begin{corollary}[Replacement for the filtered updates]\label{cor:app-vol-filtered-replacement}
Under \cref{assum:app-setup-regime} there is a sequence $\varepsilon'_B\to0$,
independent of the lag, such that for every $\ell\ge0$
\begin{equation}\label{eqn:app-vol-filtered-replacement}
\sup_{\ridge,\ridge'\in I}\ \sup_{\norm F,\norm G\le1}
\abs{\EE\,\mathcal K^{F,G}[\omega_\ridge,\omega_{\ridge'}](\Mt,M_{t+\ell})-\EE\,\mathcal K^{F,G}[\omega_\ridge,\omega_{\ridge'}](M^{\mathrm g}_t,M^{\mathrm g}_{t+\ell})}\le\varepsilon'_B .
\end{equation}
Consequently, for symmetric $F,G$ with $\norm F,\norm G\le1$, the tested lag
covariances of \cref{def:app-vol-lag} and their independent counterparts
$C^{\mathrm g}_\ell[F,G](\ridge,\ridge')\defeq B^{-1}\EE\Tr[F\,{\mathsf S}^{\mathrm g}_t(\ridge)\,G\,{\mathsf S}^{\mathrm g}_{t+\ell}(\ridge')^\T]$ satisfy
\begin{equation}\label{eqn:app-vol-C-replacement}
\sup_{\ridge,\ridge'\in I}\abs{C_\ell[F,G](\ridge,\ridge')-C^{\mathrm g}_\ell[F,G](\ridge,\ridge')}\le\varepsilon'_B+\frac{(C_\Sigma\ridge_-^{-1/2}+\varepsilon_B)^2}{B}.
\end{equation}
\end{corollary}
```
-/
theorem cor_app_vol_filtered_replacement_ii {Ω : ℕ → Type} [∀ k, MeasurableSpace (Ω k)]
    (R : SetupRegime) (P : ∀ k, Measure (Ω k)) [∀ k, IsProbabilityMeasure (P k)]
    (S : ∀ k, FrozenSamples (P k) (R.m k) (R.n k) (R.B k)) (εB : ℕ → ℝ)
    (hmean : ∀ k, ∀ s : ℤ, ∀ ϱ ∈ Icc R.ϱlo R.ϱhi,
      fro (Muon.mean (P k) (frozenUpd (R.F k) (S k) ϱ s)) ≤ R.CSig / Real.sqrt R.ϱlo + εB k) :
    ∃ ε' : ℕ → ℝ, Tendsto ε' atTop (𝓝 0) ∧
      ∀ (t : ℤ) (ℓ : ℕ) (k : ℕ) (Fo : Mat (R.m k) (R.m k)) (Gi : Mat (R.n k) (R.n k)),
        Fo ᵀ = Fo → opNorm Fo ≤ 1 → Gi ᵀ = Gi → opNorm Gi ≤ 1 →
        ∀ ϱ ϱ' : ℝ, ϱ ∈ Icc R.ϱlo R.ϱhi → ϱ' ∈ Icc R.ϱlo R.ϱhi →
          |def_app_vol_lag (R.F k) (S k) ℓ t Fo Gi ϱ ϱ' -
              ((R.B k : ℝ))⁻¹ * (∫ ω, Matrix.trace (Fo * indepUpd (R.F k) ϱ ω t * Gi *
                (indepUpd (R.F k) ϱ' ω (t + (ℓ : ℤ)))ᵀ)
                ∂(indepSpaceLaw (R.m k) (R.n k) (R.B k)))| ≤
            ε' k + (R.CSig / Real.sqrt R.ϱlo + εB k) ^ 2 / (R.B k : ℝ) := by
  obtain ⟨ε', hε', hrep⟩ := cor_app_vol_filtered_replacement_i R P S
  refine ⟨ε', hε', ?_⟩
  intro t ℓ k Fo Gi _ hFo _ hGi ϱ ϱ' hϱI hϱ'I
  have hϱ0 : 0 < ϱ := R.hϱ.1.trans_le hϱI.1
  have hϱ'0 : 0 < ϱ' := R.hϱ.1.trans_le hϱ'I.1
  have hcenter := lem_app_vol_centering_i (R.F k) (S k) t R.ϱlo R.ϱhi R.CSig
    (εB k) R.hϱ.1 (hmean k) ℓ hϱI hϱ'I Fo Gi hFo hGi
  have hreplace := hrep t ℓ k ϱ ϱ' hϱI hϱ'I Fo hFo Gi hGi
  have hfrozen :
      (∫ ω, contraction (R.B k) Fo Gi (omegaF ϱ) (omegaF ϱ')
          (frozenBuf (R.F k) (S k) t ω)
          (frozenBuf (R.F k) (S k) (t + (ℓ : ℤ)) ω) ∂(P k)) =
        ((R.B k : ℝ))⁻¹ * (∫ ω, Matrix.trace (Fo * frozenUpd (R.F k) (S k) ϱ t ω * Gi *
          (frozenUpd (R.F k) (S k) ϱ' (t + (ℓ : ℤ)) ω)ᵀ) ∂(P k)) := by
    simp_rw [contraction, eqn_app_vol_filters_sharp_ii hϱ0,
      eqn_app_vol_filters_sharp_ii hϱ'0, frozenUpd, integral_const_mul]
  have hindep :
      (∫ ω, contraction (R.B k) Fo Gi (omegaF ϱ) (omegaF ϱ')
          (def_app_vol_product (R.F k) ω t)
          (def_app_vol_product (R.F k) ω (t + (ℓ : ℤ)))
          ∂(indepSpaceLaw (R.m k) (R.n k) (R.B k))) =
        ((R.B k : ℝ))⁻¹ * (∫ ω, Matrix.trace (Fo * indepUpd (R.F k) ϱ ω t * Gi *
          (indepUpd (R.F k) ϱ' ω (t + (ℓ : ℤ)))ᵀ)
          ∂(indepSpaceLaw (R.m k) (R.n k) (R.B k))) := by
    simp_rw [contraction, eqn_app_vol_filters_sharp_ii hϱ0,
      eqn_app_vol_filters_sharp_ii hϱ'0, indepUpd, integral_const_mul]
  rw [hfrozen, hindep] at hreplace
  calc
    |def_app_vol_lag (R.F k) (S k) ℓ t Fo Gi ϱ ϱ' -
        ((R.B k : ℝ))⁻¹ * (∫ ω, Matrix.trace (Fo * indepUpd (R.F k) ϱ ω t * Gi *
          (indepUpd (R.F k) ϱ' ω (t + (ℓ : ℤ)))ᵀ)
          ∂(indepSpaceLaw (R.m k) (R.n k) (R.B k)))| ≤
        |def_app_vol_lag (R.F k) (S k) ℓ t Fo Gi ϱ ϱ' -
          ((R.B k : ℝ))⁻¹ * (∫ ω, Matrix.trace (Fo * frozenUpd (R.F k) (S k) ϱ t ω * Gi *
            (frozenUpd (R.F k) (S k) ϱ' (t + (ℓ : ℤ)) ω)ᵀ) ∂(P k))| +
        |((R.B k : ℝ))⁻¹ * (∫ ω, Matrix.trace (Fo * frozenUpd (R.F k) (S k) ϱ t ω * Gi *
            (frozenUpd (R.F k) (S k) ϱ' (t + (ℓ : ℤ)) ω)ᵀ) ∂(P k)) -
          ((R.B k : ℝ))⁻¹ * (∫ ω, Matrix.trace (Fo * indepUpd (R.F k) ϱ ω t * Gi *
            (indepUpd (R.F k) ϱ' ω (t + (ℓ : ℤ)))ᵀ)
            ∂(indepSpaceLaw (R.m k) (R.n k) (R.B k)))| := by
          exact abs_sub_le _ _ _
    _ ≤ (R.CSig / Real.sqrt R.ϱlo + εB k) ^ 2 / (R.B k : ℝ) + ε' k :=
      add_le_add (by simpa [abs_sub_comm] using hcenter) hreplace
    _ = ε' k + (R.CSig / Real.sqrt R.ϱlo + εB k) ^ 2 / (R.B k : ℝ) := by ring

end Muon.Volatility
