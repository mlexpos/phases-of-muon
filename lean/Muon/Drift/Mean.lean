import Muon.Drift.Defs
import Muon.Drift.Coefficients
import Muon.Drift.Kernel
import Muon.Drift.Tail
import Muon.Drift.Response
import Muon.Setup.Regime
import Muon.Setup.Basic

/-!
# Muon.Drift: the regularized mean, history truncation, drift kernel (work package L-C.10)

Interface draft (statements only; every proof is `sorry` unless it is a term over other
declarations) for `thm:app-drift-mean`, `prop:app-drift-truncation`(i),(iii) with the assembled
record `prop:app-drift-truncation`, and `cor:app-drift-kernel`(i), of `sections/03-drift/CARD.md`
§3, snapshot `cr-2026-10-23`.

Not restated here (owned by other packages, card §5): `prop:app-drift-truncation`(ii) is
`Muon.Drift.prop_app_drift_truncation_ii` (L-C.4, `Kernel.lean`); `cor:app-drift-kernel`(ii) is
`Muon.Drift.cor_app_drift_kernel_ii` (L-C.4); `thm:app-drift-mixed` is in
`Response.lean` and `Tail.lean`.
The assembled record `prop_app_drift_truncation` below cites (ii) by its declaration.

Reused, not restated: `Hmix`, `Tcand`, `Gbar`, `kernel`, `EQ`, `Erho`, `epsB`, `truncW`,
`WeightedBuf`, `specOutFM`, `specInFM`, `EG`, `branchQ` (`Muon.Drift.Defs`); `WeightClass`
(`Muon.DetEquiv.Scalar`); `emaW`, `fro`, `Mat`, `Q`, `mean` (`Muon.Foundations.Conventions`);
`SpectralData`, `riskSigma`, `Ahat` (`Muon.Setup.Basic`); `SetupRegime` (`Muon.Setup.Regime`);
`DriftBound`, `prop_app_drift_truncation_ii` (`Muon.Drift.Kernel`); `emaW_weightClass`
(`Muon.Drift.Coefficients`).

Representation choices (see the docstrings):
* Each record is stated for a general weight sequence `w` with `WeightClass w` (card rule (a)),
  as a `_weights` declaration; the EMA record is a term-proved instance at `emaW R.β`.
* Sequences of models carry `Ω : ℕ → Type` (regime index `k`); `Tendsto` in `k` replaces the
  limit in dimension. Every `⨆` appears with a `BddAbove` conjunct (junk-value rule).
* `cor:app-drift-kernel`(i): the frozen-state state matrix `Δ_t` is not part of
  `FrozenParams`; it enters as data `Dt` with `F.A = Ahat F.C (Dt)` (the definition of the
  normalized state, `eqn:app-setup-normalized`) and `riskSigma F.C (Dt) = ℛ(t) > 0`
  (`eqn:app-setup-risk`, `assum:app-setup-regime` `cR(t)>0`).
* `prop:app-drift-truncation`(i) general helper takes only `WeightClass w` and `J`: if the
  truncation vanishes, `EQ` and `Gbar` are both `0`, so no extra hypothesis is needed.
  `truncW_emaW_weightClass` is kept as a helper for the EMA record.
* Ridge interval: `R.ϱlo`, `R.ϱhi` of the regime (`0 < ϱlo ≤ ϱhi`).
-/
set_option linter.style.longLine false
open MeasureTheory Filter Topology Set
open scoped Matrix ENNReal
open Matrix
open Muon Muon.Setup Muon.DetEquiv
namespace Muon.Drift
/-- The EMA weights of a regime form a weight class: `β = R.β ∈ [0,1)` by `R.hβ` and the frozen parameters of index `0`, then `emaW_weightClass` (Coefficients.lean). Helper for the EMA instances of this module. -/
theorem emaW_weightClass_regime (R : Muon.Setup.SetupRegime) : WeightClass (emaW R.β) := by
  have h0 := (R.F 0).hβ
  rw [R.hβ 0] at h0
  exact emaW_weightClass R.β h0
/-- Helper for the EMA case of `prop:app-drift-truncation`: the truncation at `J` of the EMA weights is a weight class (nonnegative, finite support, `w_0 = 1 - β > 0` so not all zero, total mass at most `∑ emaW ≤ 1`). Proof: finite-support summability and the geometric sum; no source label (proof-internal of the truncation proposition). -/
private lemma mp_truncW_weightClass {w : ℕ → ℝ} (hw : WeightClass w) (J : ℕ)
    (hz : ∃ j, truncW w J j ≠ 0) : WeightClass (truncW w J) := by
  obtain ⟨⟨hnn, hsum, -⟩, hle, htsum⟩ := hw
  have hnn' : ∀ j, 0 ≤ truncW w J j := fun j => by
    simp only [truncW]
    split_ifs
    · exact hnn j
    · exact le_rfl
  have hfin : ∀ b ∉ Finset.range (J + 1), truncW w J b = 0 := by
    intro b hb
    have hbJ : ¬ b ≤ J := fun h => hb (Finset.mem_range.2 (Nat.lt_succ_of_le h))
    simp [truncW, hbJ]
  have hsum' : Summable (truncW w J) := summable_of_ne_finset_zero hfin
  have htot : ∑' j, truncW w J j = ∑ j ∈ Finset.range (J + 1), w j := by
    rw [tsum_eq_sum hfin]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hjJ : j ≤ J := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
    simp [truncW, hjJ]
  refine ⟨⟨hnn', hsum', hz⟩, fun j => ?_, ?_⟩
  · simp only [truncW]
    split_ifs
    · exact hle j
    · norm_num
  · rw [htot]
    calc ∑ j ∈ Finset.range (J + 1), w j ≤ ∑' j, w j :=
          hsum.sum_le_tsum _ (fun j _ => hnn j)
      _ ≤ 1 := htsum

theorem truncW_emaW_weightClass (R : Muon.Setup.SetupRegime) (J : ℕ) :
    WeightClass (truncW (emaW R.β) J) := by
  have h0 := (R.F 0).hβ
  rw [R.hβ 0] at h0
  refine mp_truncW_weightClass (emaW_weightClass_regime R) J ⟨0, ?_⟩
  simp only [truncW, Nat.zero_le, ite_true]
  unfold emaW
  rw [pow_zero, mul_one]
  exact sub_ne_zero.2 h0.2.ne'

/-- Private helper (proof-internal, first conjunct of `thm_app_drift_mean_weights`): the entrywise
integrability of the candidate and the bound `‖Ḡ_ϱ‖_F ≤ C_Σ/√ϱ` for `ϱ > 0`. Uses
`gbar_integrable_bound` with `γ = max γ⋆ 1 > 0`, which dominates `max(N_out,N_in) ≤ γ⋆ B`. -/
private theorem drift_mean_part1 (R : Muon.Setup.SetupRegime) (w : ℕ → ℝ) (hw : WeightClass w)
    (k : ℕ) {ϱ : ℝ} (hϱ : 0 < ϱ) :
    (∀ i j, IntegrableOn (fun u : ℝ => Tcand w (R.F k) (specOutFM (R.F k)) (specInFM (R.F k)) (ϱ + u ^ 2) i j) (Ioi 0)) ∧
      fro (Gbar w (R.F k) (specOutFM (R.F k)) (specInFM (R.F k)) ϱ) ≤ R.CSig / Real.sqrt ϱ := by
  have hγ : 0 < max R.γstar 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hD : DriftBound (R.F k) R.CSig (max R.γstar 1) := by
    refine ⟨R.normOut k, R.normIn k, ?_⟩
    have hB : (0 : ℝ) ≤ (R.B k : ℝ) := Nat.cast_nonneg _
    exact (R.dims k).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hB)
  have hCpos : (0 : ℝ) < R.CSig := lt_of_lt_of_le one_pos R.hC
  exact gbar_integrable_bound hCpos hγ hw (R.F k) hD hϱ

private lemma mp_fro_nonneg {k l : ℕ} (A : Mat k l) : 0 ≤ fro A := Real.sqrt_nonneg _

private lemma mp_fro_sq {k l : ℕ} (A : Mat k l) : fro A ^ 2 = ∑ i, ∑ j, A i j ^ 2 := by
  unfold fro
  rw [Real.sq_sqrt (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => by positivity)]
  simp [Real.norm_eq_abs, sq_abs]

private lemma mp_inner_le {m n : ℕ} (a b : Mat m n) :
    ∑ i, ∑ k, a i k * b i k ≤ fro a * fro b := by
  have e : ∀ c : Mat m n, fro c = Real.sqrt (∑ x : Fin m × Fin n, c x.1 x.2 ^ 2) := by
    intro c; unfold fro; simp [Fintype.sum_prod_type, Real.norm_eq_abs, sq_abs]
  rw [e, e]
  have := Real.sum_mul_le_sqrt_mul_sqrt (Finset.univ : Finset (Fin m × Fin n))
    (fun x => a x.1 x.2) (fun x => b x.1 x.2)
  simpa [Fintype.sum_prod_type] using this

private lemma mp_fro_integral_le {α : Type*} [MeasurableSpace α] (μ : Measure α) {m n : ℕ}
    (F : α → Mat m n) (hF : ∀ i j, Integrable (fun x => F x i j) μ) (g : α → ℝ)
    (hg : Integrable g μ) (h : ∀ᵐ x ∂μ, fro (F x) ≤ g x) :
    fro (Matrix.of fun i j => ∫ x, F x i j ∂μ) ≤ ∫ x, g x ∂μ := by
  set E : Mat m n := Matrix.of fun i j => ∫ x, F x i j ∂μ with hE
  have hint : ∀ i k, Integrable (fun x => E i k * F x i k) μ := fun i k => (hF i k).const_mul _
  have h1 : fro E ^ 2 = ∫ x, ∑ i, ∑ k, E i k * F x i k ∂μ := by
    rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun k _ => hint i k))]
    rw [mp_fro_sq]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_finsetSum _ (fun k _ => hint i k)]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [integral_const_mul]
    simp only [hE, Matrix.of_apply]
    ring
  have h2 : ∫ x, ∑ i, ∑ k, E i k * F x i k ∂μ ≤ ∫ x, fro E * g x ∂μ := by
    refine integral_mono_ae (integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun k _ =>
      hint i k) (hg.const_mul _) ?_
    filter_upwards [h] with x hx
    exact (mp_inner_le E (F x)).trans (mul_le_mul_of_nonneg_left hx (mp_fro_nonneg _))
  rw [integral_const_mul] at h2
  have hG : 0 ≤ ∫ x, g x ∂μ :=
    integral_nonneg_of_ae (by filter_upwards [h] with x hx using (mp_fro_nonneg _).trans hx)
  have h3 : fro E ^ 2 ≤ fro E * ∫ x, g x ∂μ := h1 ▸ h2
  by_contra hc
  push Not at hc
  nlinarith [mp_fro_nonneg E]

private lemma mp_hQ {m n B : ℕ} (F : FrozenParams m n B) :
    Measurable (fun x : Vec m × Vec n =>
      (dotProduct x.1 (Matrix.mulVec F.A x.2)) • (rOut F.C * Muon.outer x.1 x.2 * rIn F.C)) := by
  have hdot : Measurable (fun x : Vec m × Vec n => dotProduct x.1 (Matrix.mulVec F.A x.2)) := by
    show Measurable (fun x : Vec m × Vec n => ∑ i, x.1 i * ∑ j, F.A i j * x.2 j)
    exact Finset.measurable_sum _ (fun i _ => ((measurable_pi_apply i).comp measurable_fst).mul
      (Finset.measurable_sum _ (fun j _ =>
        measurable_const.mul ((measurable_pi_apply j).comp measurable_snd))))
  have hout : Continuous (fun x : Vec m × Vec n => Muon.outer x.1 x.2) :=
    continuous_pi fun i => continuous_pi fun j =>
      ((continuous_apply i).comp continuous_fst).mul ((continuous_apply j).comp continuous_snd)
  have hM : Measurable (fun x : Vec m × Vec n => rOut F.C * Muon.outer x.1 x.2 * rIn F.C) :=
    Continuous.measurable ((continuous_const.matrix_mul hout).matrix_mul continuous_const)
  exact hdot.smul hM

private lemma mp_meas_WB {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {m n B : ℕ}
    (w : ℕ → ℝ) (F : FrozenParams m n B)
    (S : FrozenSamples P m n B) (t : ℤ) : Measurable (WeightedBuf w F S t) := by
  haveI : TopologicalSpace.IsCompletelyPseudoMetrizableSpace (Mat m n) :=
    inferInstanceAs (TopologicalSpace.IsCompletelyPseudoMetrizableSpace (Fin m → Fin n → ℝ))
  haveI : SecondCountableTopology (Mat m n) :=
    inferInstanceAs (SecondCountableTopology (Fin m → Fin n → ℝ))
  haveI : MeasurableAdd₂ (Mat m n) := inferInstanceAs (MeasurableAdd₂ (Fin m → Fin n → ℝ))
  have hQ := mp_hQ F
  unfold WeightedBuf
  refine Measurable.tsum fun j => ?_
  refine Measurable.const_smul ?_ (w j)
  show Measurable (fun ω => ((B : ℝ))⁻¹ • ∑ a : Fin B,
    (dotProduct (S.zw (t + 1 - (j : ℤ)) a ω).1 (Matrix.mulVec F.A (S.zw (t + 1 - (j : ℤ)) a ω).2)) •
      (rOut F.C * outer (S.zw (t + 1 - (j : ℤ)) a ω).1 (S.zw (t + 1 - (j : ℤ)) a ω).2 * rIn F.C))
  exact (Finset.measurable_sum _ fun a _ => hQ.comp (S.meas _ _)).const_smul ((B : ℝ)⁻¹)

private lemma mp_abs_entry_le_fro {k l : ℕ} (A : Mat k l) (i : Fin k) (j : Fin l) :
    |A i j| ≤ fro A := by
  have h1 : A i j ^ 2 ≤ fro A ^ 2 := by
    rw [mp_fro_sq]
    calc A i j ^ 2 ≤ ∑ j', A i j' ^ 2 :=
          Finset.single_le_sum (f := fun j' => A i j' ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ j)
      _ ≤ ∑ i', ∑ j', A i' j' ^ 2 :=
          Finset.single_le_sum (f := fun i' => ∑ j', A i' j' ^ 2)
            (fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _) (Finset.mem_univ i)
  exact abs_le_of_sq_le_sq' h1 (mp_fro_nonneg _) |>.2 |> fun h => by
    exact abs_le.2 ⟨(abs_le_of_sq_le_sq' h1 (mp_fro_nonneg _)).1, h⟩

private lemma mp_meas_Q {Ω : Type*} [MeasurableSpace Ω] {m n : ℕ} {ϱ : ℝ} (hϱ : 0 < ϱ)
    {f : Ω → Mat m n} (hf : Measurable f) : Measurable (fun ω => Q ϱ (f ω)) := by
  have hc : Continuous (fun M : Mat m n => Q ϱ M) := by
    have := (continuousOn_Q_pos (m := m) (n := n)).comp
      ((continuous_const.prodMk continuous_id).continuousOn : ContinuousOn (fun M : Mat m n => (ϱ, M)) univ)
      (fun M _ => ⟨hϱ, trivial⟩)
    exact continuousOn_univ.1 this
  exact hc.measurable.comp hf

private lemma mp_EQ_fro_le {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {m n B : ℕ} (w : ℕ → ℝ) (F : FrozenParams m n B) (S : FrozenSamples P m n B) (t : ℤ)
    {ϱ : ℝ} (hϱ : 0 < ϱ) : fro (EQ w F S t ϱ) ≤ Real.sqrt (min m n : ℕ) := by
  have hmeas := mp_meas_Q hϱ (mp_meas_WB w F S t)
  have hb : ∀ ω, fro (Q ϱ (WeightedBuf w F S t ω)) ≤ Real.sqrt (min m n : ℕ) := by
    intro ω
    obtain ⟨-, h2, h3, -⟩ := lem_app_setup_filter_i ϱ hϱ.le (WeightedBuf w F S t ω)
    refine Real.le_sqrt_of_sq_le ?_
    exact h2.trans (by exact_mod_cast h3)
  refine tl_mean_fro_le P _ (fun i k => ?_) _ (Filter.Eventually.of_forall hb)
  refine Integrable.of_bound (C := Real.sqrt (min m n : ℕ)) ?_ ?_
  · exact ((measurable_pi_apply k).comp ((measurable_pi_apply i).comp hmeas)).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun ω =>
      (by rw [Real.norm_eq_abs]; exact (mp_abs_entry_le_fro _ i k).trans (hb ω))

private lemma mp_posDef {m n : ℕ} (M : Mat m n) {c : ℝ} (hc : 0 < c) :
    (M * Mᵀ + c • (1 : Mat m m)).PosDef := by
  have h0 : (M * Mᵀ).PosSemidef := by
    simpa using Matrix.posSemidef_self_mul_conjTranspose M
  have hd : (c • (1 : Mat m m)).PosDef := by
    have : c • (1 : Mat m m) = Matrix.diagonal (fun _ : Fin m => c) := by
      ext i j
      by_cases h : i = j <;> simp [h]
    rw [this]
    exact Matrix.posDef_diagonal_iff.mpr (fun _ => hc)
  rw [add_comm]
  exact hd.add_posSemidef h0

open scoped Matrix.Norms.L2Operator in
private lemma mp_abs_entry_le_opNorm {p q : ℕ} (K : Mat p q) (i : Fin p) (j : Fin q) :
    |K i j| ≤ opNorm K := by
  have h1 := Matrix.l2_opNorm_mulVec K (EuclideanSpace.single j (1 : ℝ))
  have h2 := PiLp.norm_apply_le ((EuclideanSpace.equiv (Fin p) ℝ).symm
    (K *ᵥ ⇑(EuclideanSpace.single j (1 : ℝ)))) i
  have h3 : ((EuclideanSpace.equiv (Fin p) ℝ).symm
      (K *ᵥ ⇑(EuclideanSpace.single j (1 : ℝ)))) i = K i j := by
    simp [Matrix.mulVec, dotProduct, EuclideanSpace.single_apply]
  simp only [EuclideanSpace.norm_single, norm_one, mul_one] at h1
  rw [h3, Real.norm_eq_abs] at h2
  rw [opNorm_eq_norm]
  linarith

private lemma mp_Phi_cont {m n : ℕ} {ϱ : ℝ} (hϱ : 0 < ϱ) (i : Fin m) (j : Fin n) :
    Continuous (fun p : Mat m n × ℝ =>
      ((p.1 * p.1ᵀ + (ϱ + p.2 ^ 2) • (1 : Mat m m))⁻¹ * p.1) i j) := by
  have hA : Continuous (fun p : Mat m n × ℝ => p.1 * p.1ᵀ + (ϱ + p.2 ^ 2) • (1 : Mat m m)) := by
    refine Continuous.add (continuous_fst.matrix_mul continuous_fst.matrix_transpose) ?_
    exact (continuous_const.add (continuous_snd.pow 2)).smul continuous_const
  have hI : Continuous (fun p : Mat m n × ℝ => (p.1 * p.1ᵀ + (ϱ + p.2 ^ 2) • (1 : Mat m m))⁻¹) := by
    rw [continuous_iff_continuousAt]
    intro p
    have hdet : (p.1 * p.1ᵀ + (ϱ + p.2 ^ 2) • (1 : Mat m m)).det ≠ 0 :=
      (mp_posDef p.1 (by positivity : 0 < ϱ + p.2 ^ 2)).det_pos.ne'
    have h1 := continuousAt_matrix_inv (p.1 * p.1ᵀ + (ϱ + p.2 ^ 2) • (1 : Mat m m))
      (by rw [Ring.inverse_eq_inv']; exact continuousAt_inv₀ hdet)
    exact h1.comp_of_eq hA.continuousAt rfl
  exact (continuous_apply j).comp ((continuous_apply i).comp (hI.matrix_mul continuous_fst))

private lemma mp_meas_gen {Ω : Type*} [MeasurableSpace Ω] {m n : ℕ} {ϱ : ℝ} (hϱ : 0 < ϱ) (i : Fin m) (j : Fin n)
   (WB : Ω → Mat m n) (hWBm : Measurable WB) :
   Measurable (fun p : Ω × ℝ => ((WB p.1 * (WB p.1)ᵀ + (ϱ + p.2 ^ 2) • (1 : Mat m m))⁻¹ * WB p.1) i j) := by
  have hmp : Measurable (fun p : Ω × ℝ => (WB p.1, p.2)) := (hWBm.comp measurable_fst).prodMk measurable_snd
  have hΦ : Measurable (fun p : Mat m n × ℝ =>
      ((p.1 * p.1ᵀ + (ϱ + p.2 ^ 2) • (1 : Mat m m))⁻¹ * p.1) i j) := (mp_Phi_cont hϱ i j).measurable
  exact Measurable.comp (g := fun p : Mat m n × ℝ =>
      ((p.1 * p.1ᵀ + (ϱ + p.2 ^ 2) • (1 : Mat m m))⁻¹ * p.1) i j) (f := fun p : Ω × ℝ => (WB p.1, p.2)) hΦ hmp

private lemma mp_swap {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {m n B : ℕ} (w : ℕ → ℝ) (F : FrozenParams m n B) (S : FrozenSamples P m n B) (t : ℤ)
    {ϱ : ℝ} (hϱ : 0 < ϱ) (i : Fin m) (j : Fin n) :
    Integrable (fun u : ℝ => Hmix w F S t (ϱ + u ^ 2) i j) (volume.restrict (Ioi 0)) ∧
      EQ w F S t ϱ i j = (2 / Real.pi) * ∫ u in Ioi (0 : ℝ), Hmix w F S t (ϱ + u ^ 2) i j := by
  set WB := WeightedBuf w F S t with hWB
  have hWBm : Measurable WB := mp_meas_WB w F S t
  set g : Ω × ℝ → ℝ := fun p =>
    ((WB p.1 * (WB p.1)ᵀ + (ϱ + p.2 ^ 2) • (1 : Mat m m))⁻¹ * WB p.1) i j with hg
  have hgm : Measurable g := mp_meas_gen hϱ i j WB hWBm
  have hcont := fun ω => lem_app_setup_contour ϱ hϱ (WB ω)
  have hnorm : ∀ ω, ∀ u : ℝ, ‖g (ω, u)‖ ≤ nuc ((WB ω * (WB ω)ᵀ + (ϱ + u ^ 2) • (1 : Mat m m))⁻¹ * WB ω) := by
    intro ω u
    rw [Real.norm_eq_abs]
    exact (mp_abs_entry_le_opNorm ((WB ω * (WB ω)ᵀ + (ϱ + u ^ 2) • (1 : Mat m m))⁻¹ * WB ω) i j).trans
      (opNorm_le_nuc _)
  have hint : Integrable g (P.prod (volume.restrict (Ioi (0 : ℝ)))) := by
    rw [integrable_prod_iff hgm.aestronglyMeasurable]
    refine ⟨Filter.Eventually.of_forall fun ω => (hcont ω).2.1 i j, ?_⟩
    refine Integrable.of_bound (C := Real.pi / 2 * (min m n : ℝ)) ?_ ?_
    · exact hgm.norm.stronglyMeasurable.integral_prod_right'.aestronglyMeasurable
    · refine Filter.Eventually.of_forall fun ω => ?_
      have h0 : 0 ≤ ∫ u in Ioi (0 : ℝ), ‖g (ω, u)‖ := integral_nonneg fun u => norm_nonneg _
      rw [Real.norm_eq_abs, abs_of_nonneg h0]
      refine le_trans (integral_mono ((hcont ω).2.1 i j).norm (hcont ω).2.2.1 fun u => hnorm ω u)
        (hcont ω).2.2.2
  have hint' : Integrable (Function.uncurry fun ω u => g (ω, u))
      (P.prod (volume.restrict (Ioi (0 : ℝ)))) := hint
  have hswap := integral_integral_swap hint'
  have hH : ∀ u : ℝ, Hmix w F S t (ϱ + u ^ 2) i j = ∫ ω, g (ω, u) ∂P := fun u => by
    simp only [Hmix, Muon.mean, Matrix.of_apply, Xs, Rs, hg]
    rfl
  refine ⟨?_, ?_⟩
  · simp_rw [hH]
    exact hint.integral_prod_right
  · have hE : EQ w F S t ϱ i j = ∫ ω, ((2 / Real.pi) * ∫ u in Ioi (0 : ℝ), g (ω, u)) ∂P := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
      exact (hcont ω).1 i j
    rw [hE, integral_const_mul]
    simp_rw [hH]
    rw [← hswap]

open scoped Matrix.Norms.Frobenius in
private lemma mp_fro_add {k l : ℕ} (A B' : Mat k l) : fro (A + B') ≤ fro A + fro B' := by
  rw [fro_eq_norm, fro_eq_norm, fro_eq_norm]; exact norm_add_le _ _

open scoped Matrix.Norms.Frobenius in
private lemma mp_fro_smul {k l : ℕ} (c : ℝ) (A : Mat k l) : fro (c • A) = |c| * fro A := by
  rw [fro_eq_norm, fro_eq_norm, norm_smul, Real.norm_eq_abs]

private lemma mp_tail_int {R : ℝ} (hR : 0 < R) :
    IntegrableOn (fun u : ℝ => (u ^ 2)⁻¹) (Ioi R) ∧ ∫ u in Ioi R, (u ^ 2)⁻¹ = R⁻¹ := by
  have heq : EqOn (fun u : ℝ => u ^ (-2 : ℝ)) (fun u : ℝ => (u ^ 2)⁻¹) (Ioi R) := by
    intro u hu
    have hu0 : 0 < u := hR.trans hu
    simp only
    rw [Real.rpow_neg hu0.le, Real.rpow_two]
  refine ⟨(integrableOn_Ioi_rpow_of_lt (by norm_num) hR).congr_fun heq measurableSet_Ioi, ?_⟩
  rw [← setIntegral_congr_fun measurableSet_Ioi heq, integral_Ioi_rpow_of_lt (by norm_num) hR]
  rw [show (-2 : ℝ) + 1 = -1 by norm_num, Real.rpow_neg_one]
  field_simp

private lemma mp_diff_bound {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {m n B : ℕ} (w : ℕ → ℝ) (F : FrozenParams m n B) (S : FrozenSamples P m n B) (t : ℤ)
    {CS γ C : ℝ} (hCS : 0 < CS) (hγ : 0 < γ) (hw : WeightClass w) (hD : DriftBound F CS γ)
    (hHC : ∀ s : ℝ, 1 ≤ s → fro (Hmix w F S t s) ≤ C / s)
    {ϱ : ℝ} (hϱ : 0 < ϱ) {R δ : ℝ} (hR : 1 ≤ R)
    (hδ : ∀ u : ℝ, 0 < u → u ≤ R →
      fro (Hmix w F S t (ϱ + u ^ 2) - Tcand w F (specOutFM F) (specInFM F) (ϱ + u ^ 2)) ≤ δ) :
    fro (EQ w F S t ϱ - Gbar w F (specOutFM F) (specInFM F) ϱ) ≤
      2 / Real.pi * (R * δ + (C + CS) / R) := by
  have hR0 : 0 < R := lt_of_lt_of_le one_pos hR
  have hC0 : 0 ≤ C := by
    have h := (mp_fro_nonneg _).trans (hHC 1 le_rfl)
    simpa using h
  have hTint := (gbar_integrable_bound hCS hγ hw F hD hϱ).1
  set f : ℝ → Mat m n := fun u =>
    Hmix w F S t (ϱ + u ^ 2) - Tcand w F (specOutFM F) (specInFM F) (ϱ + u ^ 2) with hf
  have hfint : ∀ i j, IntegrableOn (fun u => f u i j) (Ioi 0) := fun i j =>
    ((mp_swap w F S t hϱ i j).1).sub (hTint i j)
  have hD' : EQ w F S t ϱ - Gbar w F (specOutFM F) (specInFM F) ϱ =
      (2 / Real.pi) • (Matrix.of fun i j => ∫ u in Ioi (0 : ℝ), f u i j) := by
    ext i j
    simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.of_apply, Gbar, smul_eq_mul, hf]
    rw [(mp_swap w F S t hϱ i j).2, integral_sub (mp_swap w F S t hϱ i j).1 (hTint i j)]
    ring
  rw [hD', mp_fro_smul, abs_of_nonneg (by positivity)]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  have hsplit : (Matrix.of fun i j => ∫ u in Ioi (0 : ℝ), f u i j) =
      (Matrix.of fun i j => ∫ u in Ioc (0 : ℝ) R, f u i j) +
        (Matrix.of fun i j => ∫ u in Ioi R, f u i j) := by
    ext i j
    simp only [Matrix.add_apply, Matrix.of_apply]
    rw [← Ioc_union_Ioi_eq_Ioi hR0.le]
    exact setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
      ((hfint i j).mono_set Ioc_subset_Ioi_self)
      ((hfint i j).mono_set (fun x hx => hR0.trans hx))
  rw [hsplit]
  refine (mp_fro_add _ _).trans (add_le_add ?_ ?_)
  · have := mp_fro_integral_le (volume.restrict (Ioc (0 : ℝ) R)) f
      (fun i j => (hfint i j).mono_set Ioc_subset_Ioi_self) (fun _ => δ) (integrable_const _)
      (ae_restrict_of_forall_mem measurableSet_Ioc fun u hu => hδ u hu.1 hu.2)
    simpa [mul_comm, max_eq_left hR0.le] using this
  · obtain ⟨hI2, hV2⟩ := mp_tail_int hR0
    have := mp_fro_integral_le (volume.restrict (Ioi R)) f
      (fun i j => (hfint i j).mono_set (fun x hx => hR0.trans hx))
      (fun u => (C + CS) * (u ^ 2)⁻¹) (hI2.const_mul _)
      (ae_restrict_of_forall_mem measurableSet_Ioi fun u hu => by
        have hu1 : 1 ≤ u := hR.trans hu.le
        have hu0 : 0 < u := lt_of_lt_of_le one_pos hu1
        have hs1 : 1 ≤ ϱ + u ^ 2 := by nlinarith
        have h1 := hHC _ hs1
        have h2 := thm_app_drift_mixed_ii_T hCS hγ hw F hD (s := ϱ + u ^ 2) (by positivity)
        have h3 : fro (f u) ≤ fro (Hmix w F S t (ϱ + u ^ 2)) +
            fro (Tcand w F (specOutFM F) (specInFM F) (ϱ + u ^ 2)) := by
          have := mp_fro_add (Hmix w F S t (ϱ + u ^ 2))
            (-(Tcand w F (specOutFM F) (specInFM F) (ϱ + u ^ 2)))
          have hneg : fro (-(Tcand w F (specOutFM F) (specInFM F) (ϱ + u ^ 2))) =
              fro (Tcand w F (specOutFM F) (specInFM F) (ϱ + u ^ 2)) := by
            have := mp_fro_smul (-1) (Tcand w F (specOutFM F) (specInFM F) (ϱ + u ^ 2))
            simpa using this
          simpa [hf, sub_eq_add_neg, hneg] using this
        have hu2 : (0 : ℝ) < u ^ 2 := by positivity
        have h4 : (C + CS) / (ϱ + u ^ 2) ≤ (C + CS) * (u ^ 2)⁻¹ := by
          rw [div_eq_mul_inv]
          exact mul_le_mul_of_nonneg_left (inv_anti₀ hu2 (by linarith)) (by linarith)
        calc fro (f u) ≤ C / (ϱ + u ^ 2) + CS / (ϱ + u ^ 2) := h3.trans (add_le_add h1 h2)
          _ = (C + CS) / (ϱ + u ^ 2) := by ring
          _ ≤ _ := h4)
    rw [integral_const_mul, hV2] at this
    simpa [div_eq_mul_inv] using this

private lemma mp_le_biSup {f : ℝ → ℝ} {I : Set ℝ} (hb : BddAbove (f '' I)) {s : ℝ} (hs : s ∈ I) :
    f s ≤ ⨆ s ∈ I, f s := by
  obtain ⟨b, hb'⟩ := hb
  have hbdd : BddAbove (Set.range fun s => ⨆ (_ : s ∈ I), f s) := by
    refine ⟨max b 0, ?_⟩
    rintro _ ⟨s', rfl⟩
    show (⨆ (_ : s' ∈ I), f s') ≤ max b 0
    by_cases hs' : s' ∈ I
    · rw [ciSup_pos hs']
      exact le_max_of_le_left (hb' ⟨s', hs', rfl⟩)
    · haveI : IsEmpty (s' ∈ I) := ⟨hs'⟩
      rw [Real.iSup_of_isEmpty]
      exact le_max_right _ _
  refine le_ciSup_of_le hbdd s ?_
  rw [ciSup_pos hs]

private lemma mp_biSup_nonneg {f : ℝ → ℝ} {I : Set ℝ} (hf : ∀ s, 0 ≤ f s) : 0 ≤ ⨆ s ∈ I, f s :=
  Real.iSup_nonneg fun s => Real.iSup_nonneg fun _ => hf s

private lemma mp_biSup_le {f : ℝ → ℝ} {I : Set ℝ} {a : ℝ} (ha : 0 ≤ a) (h : ∀ s ∈ I, f s ≤ a) :
    ⨆ s ∈ I, f s ≤ a :=
  Real.iSup_le (fun s => Real.iSup_le (fun hs => h s hs) ha) ha

private lemma mp_fro_sub_le {k l : ℕ} (A B' : Mat k l) : fro (A - B') ≤ fro A + fro B' := by
  have h := mp_fro_add A (-B')
  have hneg : fro (-B') = fro B' := by
    have := mp_fro_smul (-1) B'
    simpa using this
  simpa [sub_eq_add_neg, hneg] using h

open scoped Matrix.Norms.Frobenius in
private lemma mp_fro_comm {k l : ℕ} (A B' : Mat k l) : fro (A - B') = fro (B' - A) := by
  rw [fro_eq_norm, fro_eq_norm]
  exact norm_sub_rev _ _

private lemma mp_fro_tri4 {k l : ℕ} (A B' C D : Mat k l) :
    fro (A - B') ≤ fro (A - C) + fro (C - D) + fro (D - B') := by
  have h1 : A - B' = ((A - C) + (C - D)) + (D - B') := by abel
  rw [h1]
  have h2 := mp_fro_add ((A - C) + (C - D)) (D - B')
  have h3 := mp_fro_add (A - C) (C - D)
  linarith

private lemma mp_tendsto_aux (e : ℕ → ℝ) (δ : ℝ → ℕ → ℝ) (K : ℝ) (hK : 0 ≤ K)
    (he0 : ∀ k, 0 ≤ e k)
    (he : ∀ R : ℝ, 1 ≤ R → ∀ k, e k ≤ 2 / Real.pi * (R * δ R k + K / R))
    (hδ : ∀ R : ℝ, 1 ≤ R → Tendsto (δ R) atTop (𝓝 0)) : Tendsto e atTop (𝓝 0) := by
  refine tendsto_order.2 ⟨fun a ha => Filter.Eventually.of_forall fun k => lt_of_lt_of_le ha (he0 k), ?_⟩
  intro a ha
  have hπ := Real.pi_pos
  set R : ℝ := max 1 (4 * K / (Real.pi * a) + 1) with hRdef
  have hR1 : 1 ≤ R := le_max_left _ _
  have hR0 : 0 < R := lt_of_lt_of_le one_pos hR1
  have hRK : 4 * K / (Real.pi * a) < R := lt_of_lt_of_le (by linarith) (le_max_right _ _)
  have hKR : 2 / Real.pi * (K / R) < a / 2 := by
    have h1 : 4 * K < R * (Real.pi * a) := by
      have := (div_lt_iff₀ (mul_pos hπ ha)).1 hRK
      linarith
    rw [show 2 / Real.pi * (K / R) = 2 * K / (Real.pi * R) by field_simp]
    rw [div_lt_iff₀ (mul_pos hπ hR0)]
    nlinarith
  have hev := (tendsto_order.1 (hδ R hR1)).2 (Real.pi * a / (4 * R))
    (by positivity)
  filter_upwards [hev] with k hk
  have h2 : 2 / Real.pi * (R * δ R k) < a / 2 := by
    have : R * δ R k < R * (Real.pi * a / (4 * R)) := mul_lt_mul_of_pos_left hk hR0
    have h3 : R * (Real.pi * a / (4 * R)) = Real.pi * a / 4 := by field_simp
    rw [h3] at this
    calc 2 / Real.pi * (R * δ R k) < 2 / Real.pi * (Real.pi * a / 4) :=
          mul_lt_mul_of_pos_left this (by positivity)
      _ = a / 2 := by field_simp; ring
  calc e k ≤ 2 / Real.pi * (R * δ R k + K / R) := he R hR1 k
    _ = 2 / Real.pi * (R * δ R k) + 2 / Real.pi * (K / R) := by ring
    _ < a := by linarith

private lemma mp_trace_le {m n : ℕ} (V D : Mat m n) :
    |(V * Dᵀ).trace| ≤ fro V * fro D := by
  have htr : (V * Dᵀ).trace = ∑ i, ∑ j, V i j * D i j := by
    simp [Matrix.trace, Matrix.diag, Matrix.mul_apply]
  rw [htr]
  have h1 := mp_inner_le V D
  have h2 := mp_inner_le V (-D)
  have hneg : fro (-D) = fro D := by
    have := mp_fro_smul (-1) D
    simpa using this
  rw [hneg] at h2
  refine abs_le.2 ⟨?_, h1⟩
  have : ∑ i, ∑ j, V i j * (-D) i j = -∑ i, ∑ j, V i j * D i j := by
    simp [Finset.sum_neg_distrib]
  linarith


/-- `thm:app-drift-mean`, snapshot `cr-2026-10-23`. Regularized mean, general weight sequence (card rule (a)). For `WeightClass w` under `assum:app-setup-regime`: the entrywise integral defining `Ḡ_ϱ` converges absolutely with `‖Ḡ_ϱ‖_F ≤ C_Σ/√ϱ`; `ε_B → 0`; and the pairing bound. The EMA record is the instance at `emaW R.β`.
Source, verbatim (`sections/03-drift/section.tex`):
```latex
\begin{theorem}[Regularized mean]\label{thm:app-drift-mean}
Under \cref{assum:app-setup-regime}, the integral \cref{eqn:app-drift-Gbar}
converges absolutely in Frobenius norm, with
$\norm{\Gtildebar_\ridge}_\F\le C_\Sigma/\sqrt\ridge$, and
\begin{equation}\label{eqn:app-drift-mean}
\varepsilon_B\defeq\sup_{\ridge\in[\ridge_-,\ridge_+]}\norm{\EE\,\Qridge\ridge(\Mt)-\Gtildebar_\ridge}_\F\longrightarrow0 .
\end{equation}
Consequently, for every deterministic $V\in\R^{\Nout\times\Nin}$,
\begin{equation}\label{eqn:app-drift-pairing}
\sup_{\ridge\in[\ridge_-,\ridge_+]}\big|\big\langle V,\EE\,\Qridge\ridge(\Mt)-\Gtildebar_\ridge\big\rangle\big|\le\norm V_\F\,\varepsilon_B,
\qquad \langle V,W\rangle\defeq\Tr(VW^\T).
\end{equation}
\end{theorem}
```
-/
theorem thm_app_drift_mean_weights (R : Muon.Setup.SetupRegime) {Ω : ℕ → Type} [∀ k, MeasurableSpace (Ω k)]
    (P : ∀ k, Measure (Ω k)) [∀ k, IsProbabilityMeasure (P k)]
    (S : ∀ k, FrozenSamples (P k) (R.m k) (R.n k) (R.B k)) (t : ℤ)
    (w : ℕ → ℝ) (hw : WeightClass w) :
    (∀ k, ∀ ϱ ∈ Icc R.ϱlo R.ϱhi,
      (∀ i j, IntegrableOn (fun u : ℝ => Tcand w (R.F k) (specOutFM (R.F k)) (specInFM (R.F k)) (ϱ + u ^ 2) i j) (Ioi 0)) ∧
      fro (Gbar w (R.F k) (specOutFM (R.F k)) (specInFM (R.F k)) ϱ) ≤ R.CSig / Real.sqrt ϱ) ∧
    (∀ k, BddAbove ((fun ϱ => fro (EQ w (R.F k) (S k) t ϱ - Gbar w (R.F k) (specOutFM (R.F k)) (specInFM (R.F k)) ϱ)) '' Icc R.ϱlo R.ϱhi)) ∧
    Tendsto (fun k => epsB w (R.F k) (S k) t (specOutFM (R.F k)) (specInFM (R.F k)) R.ϱlo R.ϱhi) atTop (𝓝 0) ∧
    (∀ k, ∀ V : Mat (R.m k) (R.n k),
      BddAbove ((fun ϱ => |(V * (EQ w (R.F k) (S k) t ϱ - Gbar w (R.F k) (specOutFM (R.F k)) (specInFM (R.F k)) ϱ)ᵀ).trace|) '' Icc R.ϱlo R.ϱhi) ∧
      (⨆ ϱ ∈ Icc R.ϱlo R.ϱhi, |(V * (EQ w (R.F k) (S k) t ϱ - Gbar w (R.F k) (specOutFM (R.F k)) (specInFM (R.F k)) ϱ)ᵀ).trace|) ≤
        fro V * epsB w (R.F k) (S k) t (specOutFM (R.F k)) (specInFM (R.F k)) R.ϱlo R.ϱhi) := by
  have hCS : 0 < R.CSig := lt_of_lt_of_le one_pos R.hC
  have hγ : 0 < max R.γstar 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hD : ∀ k, DriftBound (R.F k) R.CSig (max R.γstar 1) := by
    intro k
    refine ⟨R.normOut k, R.normIn k, ?_⟩
    have hB : (0 : ℝ) ≤ (R.B k : ℝ) := Nat.cast_nonneg _
    exact (R.dims k).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hB)
  obtain ⟨C, hCall⟩ := thm_app_drift_mixed_ii R.CSig (max R.γstar 1) hCS hγ
  have hHC : ∀ k, ∀ s : ℝ, 1 ≤ s → fro (Hmix w (R.F k) (S k) t s) ≤ C / s := fun k =>
    (hCall (Ω k) (R.m k) (R.n k) (R.B k) (P k) w (R.F k) (S k) t hw (hD k)).1
  have hlo : 0 < R.ϱlo := R.hϱ.1
  have hC0 : 0 ≤ C := by
    have h := (mp_fro_nonneg _).trans (hHC 0 1 le_rfl)
    simpa using h
  have hbdd : ∀ k, BddAbove ((fun ϱ => fro (EQ w (R.F k) (S k) t ϱ - Gbar w (R.F k) (specOutFM (R.F k)) (specInFM (R.F k)) ϱ)) '' Icc R.ϱlo R.ϱhi) := by
    intro k
    refine ⟨Real.sqrt (min (R.m k) (R.n k) : ℕ) + R.CSig / Real.sqrt R.ϱlo, ?_⟩
    rintro _ ⟨ϱ, hϱ, rfl⟩
    have hp : 0 < ϱ := hlo.trans_le hϱ.1
    refine (mp_fro_sub_le _ _).trans (add_le_add (mp_EQ_fro_le w (R.F k) (S k) t hp) ?_)
    exact (drift_mean_part1 R w hw k hp).2.trans
      (div_le_div_of_nonneg_left hCS.le (Real.sqrt_pos.2 hlo) (Real.sqrt_le_sqrt hϱ.1))
  have hmi : ∀ R' : ℝ, 1 ≤ R' →
      (∀ k, BddAbove ((fun s => fro (Hmix w (R.F k) (S k) t s
        - Tcand w (R.F k) (specOutFM (R.F k)) (specInFM (R.F k)) s)) '' Icc R.ϱlo (R.ϱhi + R' ^ 2))) ∧
      Tendsto (fun k => ⨆ s ∈ Icc R.ϱlo (R.ϱhi + R' ^ 2), fro (Hmix w (R.F k) (S k) t s
        - Tcand w (R.F k) (specOutFM (R.F k)) (specInFM (R.F k)) s)) atTop (𝓝 0) := fun R' _ =>
    thm_app_drift_mixed_i_weights R P S t (Icc R.ϱlo (R.ϱhi + R' ^ 2)) isCompact_Icc
      (fun s hs => hlo.trans_le hs.1) w hw
  have hE0 : ∀ k, 0 ≤ epsB w (R.F k) (S k) t (specOutFM (R.F k)) (specInFM (R.F k)) R.ϱlo R.ϱhi :=
    fun k => mp_biSup_nonneg (fun ϱ => mp_fro_nonneg _)
  have heps : ∀ R' : ℝ, 1 ≤ R' → ∀ k,
      epsB w (R.F k) (S k) t (specOutFM (R.F k)) (specInFM (R.F k)) R.ϱlo R.ϱhi ≤
        2 / Real.pi * (R' * (⨆ s ∈ Icc R.ϱlo (R.ϱhi + R' ^ 2), fro (Hmix w (R.F k) (S k) t s
          - Tcand w (R.F k) (specOutFM (R.F k)) (specInFM (R.F k)) s)) + (C + R.CSig) / R') := by
    intro R' hR' k
    have hδ0 : 0 ≤ ⨆ s ∈ Icc R.ϱlo (R.ϱhi + R' ^ 2), fro (Hmix w (R.F k) (S k) t s
          - Tcand w (R.F k) (specOutFM (R.F k)) (specInFM (R.F k)) s) :=
      mp_biSup_nonneg (fun s => mp_fro_nonneg _)
    have hR0 : 0 < R' := lt_of_lt_of_le one_pos hR'
    refine mp_biSup_le (by positivity) (fun ϱ hϱ => ?_)
    have hp : 0 < ϱ := hlo.trans_le hϱ.1
    refine mp_diff_bound w (R.F k) (S k) t hCS hγ hw (hD k) (hHC k) hp hR' (fun u hu hu2 => ?_)
    refine mp_le_biSup (f := fun s => fro (Hmix w (R.F k) (S k) t s
          - Tcand w (R.F k) (specOutFM (R.F k)) (specInFM (R.F k)) s)) ((hmi R' hR').1 k)
      (s := ϱ + u ^ 2) ⟨by nlinarith [hϱ.1, sq_nonneg u], ?_⟩
    have : u ^ 2 ≤ R' ^ 2 := by nlinarith
    linarith [hϱ.2]
  have hT : Tendsto (fun k => epsB w (R.F k) (S k) t (specOutFM (R.F k)) (specInFM (R.F k)) R.ϱlo R.ϱhi) atTop (𝓝 0) :=
    mp_tendsto_aux _ (fun R' k => ⨆ s ∈ Icc R.ϱlo (R.ϱhi + R' ^ 2), fro (Hmix w (R.F k) (S k) t s
          - Tcand w (R.F k) (specOutFM (R.F k)) (specInFM (R.F k)) s)) (C + R.CSig)
      (by linarith) hE0 heps (fun R' hR' => (hmi R' hR').2)
  refine ⟨fun k ϱ hϱ => drift_mean_part1 R w hw k (hlo.trans_le hϱ.1), hbdd, hT, fun k V => ?_⟩
  have hle : ∀ ϱ ∈ Icc R.ϱlo R.ϱhi,
      fro (EQ w (R.F k) (S k) t ϱ - Gbar w (R.F k) (specOutFM (R.F k)) (specInFM (R.F k)) ϱ) ≤
        epsB w (R.F k) (S k) t (specOutFM (R.F k)) (specInFM (R.F k)) R.ϱlo R.ϱhi := fun ϱ hϱ =>
    mp_le_biSup (f := fun ϱ => fro (EQ w (R.F k) (S k) t ϱ - Gbar w (R.F k) (specOutFM (R.F k)) (specInFM (R.F k)) ϱ))
      (hbdd k) hϱ
  have hpt : ∀ ϱ ∈ Icc R.ϱlo R.ϱhi,
      |(V * (EQ w (R.F k) (S k) t ϱ - Gbar w (R.F k) (specOutFM (R.F k)) (specInFM (R.F k)) ϱ)ᵀ).trace| ≤
        fro V * epsB w (R.F k) (S k) t (specOutFM (R.F k)) (specInFM (R.F k)) R.ϱlo R.ϱhi := fun ϱ hϱ =>
    (mp_trace_le V _).trans (mul_le_mul_of_nonneg_left (hle ϱ hϱ) (mp_fro_nonneg V))
  refine ⟨⟨fro V * epsB w (R.F k) (S k) t (specOutFM (R.F k)) (specInFM (R.F k)) R.ϱlo R.ϱhi, ?_⟩,
    mp_biSup_le (mul_nonneg (mp_fro_nonneg V) (hE0 k)) hpt⟩
  rintro _ ⟨ϱ, hϱ, rfl⟩
  exact hpt ϱ hϱ
/-- `thm:app-drift-mean`, snapshot `cr-2026-10-23`. Regularized mean, EMA record (`emaW R.β`, `β` fixed by `R.hβ`). Term-proved instance of `thm_app_drift_mean_weights`.
Source, verbatim (`sections/03-drift/section.tex`):
```latex
\begin{theorem}[Regularized mean]\label{thm:app-drift-mean}
Under \cref{assum:app-setup-regime}, the integral \cref{eqn:app-drift-Gbar}
converges absolutely in Frobenius norm, with
$\norm{\Gtildebar_\ridge}_\F\le C_\Sigma/\sqrt\ridge$, and
\begin{equation}\label{eqn:app-drift-mean}
\varepsilon_B\defeq\sup_{\ridge\in[\ridge_-,\ridge_+]}\norm{\EE\,\Qridge\ridge(\Mt)-\Gtildebar_\ridge}_\F\longrightarrow0 .
\end{equation}
Consequently, for every deterministic $V\in\R^{\Nout\times\Nin}$,
\begin{equation}\label{eqn:app-drift-pairing}
\sup_{\ridge\in[\ridge_-,\ridge_+]}\big|\big\langle V,\EE\,\Qridge\ridge(\Mt)-\Gtildebar_\ridge\big\rangle\big|\le\norm V_\F\,\varepsilon_B,
\qquad \langle V,W\rangle\defeq\Tr(VW^\T).
\end{equation}
\end{theorem}
```
-/
theorem thm_app_drift_mean (R : Muon.Setup.SetupRegime) {Ω : ℕ → Type} [∀ k, MeasurableSpace (Ω k)]
    (P : ∀ k, Measure (Ω k)) [∀ k, IsProbabilityMeasure (P k)]
    (S : ∀ k, FrozenSamples (P k) (R.m k) (R.n k) (R.B k)) (t : ℤ) :
    (∀ k, ∀ ϱ ∈ Icc R.ϱlo R.ϱhi,
      (∀ i j, IntegrableOn (fun u : ℝ => Tcand (emaW R.β) (R.F k) (specOutFM (R.F k)) (specInFM (R.F k)) (ϱ + u ^ 2) i j) (Ioi 0)) ∧
      fro (Gbar (emaW R.β) (R.F k) (specOutFM (R.F k)) (specInFM (R.F k)) ϱ) ≤ R.CSig / Real.sqrt ϱ) ∧
    (∀ k, BddAbove ((fun ϱ => fro (EQ (emaW R.β) (R.F k) (S k) t ϱ - Gbar (emaW R.β) (R.F k) (specOutFM (R.F k)) (specInFM (R.F k)) ϱ)) '' Icc R.ϱlo R.ϱhi)) ∧
    Tendsto (fun k => epsB (emaW R.β) (R.F k) (S k) t (specOutFM (R.F k)) (specInFM (R.F k)) R.ϱlo R.ϱhi) atTop (𝓝 0) ∧
    (∀ k, ∀ V : Mat (R.m k) (R.n k),
      BddAbove ((fun ϱ => |(V * (EQ (emaW R.β) (R.F k) (S k) t ϱ - Gbar (emaW R.β) (R.F k) (specOutFM (R.F k)) (specInFM (R.F k)) ϱ)ᵀ).trace|) '' Icc R.ϱlo R.ϱhi) ∧
      (⨆ ϱ ∈ Icc R.ϱlo R.ϱhi, |(V * (EQ (emaW R.β) (R.F k) (S k) t ϱ - Gbar (emaW R.β) (R.F k) (specOutFM (R.F k)) (specInFM (R.F k)) ϱ)ᵀ).trace|) ≤
        fro V * epsB (emaW R.β) (R.F k) (S k) t (specOutFM (R.F k)) (specInFM (R.F k)) R.ϱlo R.ϱhi) :=
  thm_app_drift_mean_weights R P S t (emaW R.β) (emaW_weightClass_regime R)
/-- `prop:app-drift-truncation`, snapshot `cr-2026-10-23`. History truncation, part (i), general weight sequence: for `WeightClass w` and every `J`, the regularized update of the truncated buffer `w^{(J)} = w 𝟙_{j≤J}` truncated buffer converges to its candidate `Ḡ^{(J)}` uniformly in `ϱ`, as the dimension grows (sequence index `k`). The EMA record is the instance at `emaW R.β`.
Source, verbatim (`sections/03-drift/section.tex`):
```latex
\begin{proposition}[History truncation]\label{prop:app-drift-truncation}
Under \cref{assum:app-setup-regime}, for $J\ge0$ let $\emaw j^{(J)}\defeq\emaw j\mathbf 1_{j\le J}$,
let $M^{(J)}=\sum_{j\le J}\emaw jG_{t+1-j}$ be the truncated buffer of
\cref{lem:app-setup-truncation}, and let $T^{(J)}$ and $\Gtildebar^{(J)}_\ridge$
be the candidates \cref{eqn:app-drift-H,eqn:app-drift-Gbar} built from the
solution of the system \cref{eqn:app-de-system} for the weights $\emaw{}^{(J)}$.
\begin{enumerate}[label=(\roman*)]
\item For every fixed $J$,
$\sup_{\ridge\in[\ridge_-,\ridge_+]}\norm{\EE\,\Qridge\ridge(M^{(J)})-\Gtildebar^{(J)}_\ridge}_\F\to0$
as the dimension grows.
\item $\lim_{J\to\infty}\sup_B\sup_{\ridge\in[\ridge_-,\ridge_+]}\norm{\Gtildebar_\ridge-\Gtildebar^{(J)}_\ridge}_\F=0$,
where $\sup_B$ runs over the whole sequence of dimensions.
\item Consequently
\begin{equation}\label{eqn:app-drift-truncation}
\lim_{J\to\infty}\limsup_{B\to\infty}\sup_{\ridge\in[\ridge_-,\ridge_+]}
\norm{\EE\,\Qridge\ridge(\Mt)-\EE\,\Qridge\ridge(M^{(J)})}_\F=0 .
\end{equation}
\end{enumerate}
\end{proposition}
```
-/
theorem prop_app_drift_truncation_i_weights (R : Muon.Setup.SetupRegime) {Ω : ℕ → Type} [∀ k, MeasurableSpace (Ω k)]
    (P : ∀ k, Measure (Ω k)) [∀ k, IsProbabilityMeasure (P k)]
    (S : ∀ k, FrozenSamples (P k) (R.m k) (R.n k) (R.B k)) (t : ℤ)
    (w : ℕ → ℝ) (hw : WeightClass w) (J : ℕ) :
    (∀ k, BddAbove ((fun ϱ => fro (EQ (truncW w J) (R.F k) (S k) t ϱ - Gbar (truncW w J) (R.F k) (specOutFM (R.F k)) (specInFM (R.F k)) ϱ)) '' Icc R.ϱlo R.ϱhi)) ∧
    Tendsto (fun k => ⨆ ϱ ∈ Icc R.ϱlo R.ϱhi, fro (EQ (truncW w J) (R.F k) (S k) t ϱ - Gbar (truncW w J) (R.F k) (specOutFM (R.F k)) (specInFM (R.F k)) ϱ))
      atTop (𝓝 0) := by
  by_cases hz : ∃ j, truncW w J j ≠ 0
  · obtain ⟨-, hB, hT, -⟩ := thm_app_drift_mean_weights R P S t (truncW w J)
      (mp_truncW_weightClass hw J hz)
    exact ⟨hB, hT⟩
  · push_neg at hz
    have key : ∀ k ϱ, fro (EQ (truncW w J) (R.F k) (S k) t ϱ - Gbar (truncW w J) (R.F k) (specOutFM (R.F k)) (specInFM (R.F k)) ϱ) = 0 := by
      intro k ϱ
      have h1 : EQ (truncW w J) (R.F k) (S k) t ϱ = 0 := by
        simp [EQ, Muon.mean, WeightedBuf, hz, Q]
        ext i j; simp
      have h2 : Gbar (truncW w J) (R.F k) (specOutFM (R.F k)) (specInFM (R.F k)) ϱ = 0 := by
        have hL : ∀ q, Lw (truncW w J) q = 0 := fun q => by
          simp [Lw, hz]
        simp [Gbar, Tcand, hL]
        ext i j; simp
      rw [h1, h2, sub_zero]
      simp [fro]
    refine ⟨fun k => ⟨0, ?_⟩, ?_⟩
    · rintro _ ⟨ϱ, _, rfl⟩
      exact le_of_eq (key k ϱ)
    · have hg : ∀ k, (⨆ ϱ ∈ Icc R.ϱlo R.ϱhi, fro (EQ (truncW w J) (R.F k) (S k) t ϱ - Gbar (truncW w J) (R.F k) (specOutFM (R.F k)) (specInFM (R.F k)) ϱ)) = 0 :=
        fun k => le_antisymm (mp_biSup_le le_rfl (fun ϱ _ => le_of_eq (key k ϱ)))
          (mp_biSup_nonneg (fun ϱ => mp_fro_nonneg _))
      exact (tendsto_congr hg).2 tendsto_const_nhds
/-- `prop:app-drift-truncation`, snapshot `cr-2026-10-23`. History truncation, part (i), EMA record at `emaW R.β`. Term-proved instance of `prop_app_drift_truncation_i_weights`.
Source, verbatim (`sections/03-drift/section.tex`):
```latex
\begin{proposition}[History truncation]\label{prop:app-drift-truncation}
Under \cref{assum:app-setup-regime}, for $J\ge0$ let $\emaw j^{(J)}\defeq\emaw j\mathbf 1_{j\le J}$,
let $M^{(J)}=\sum_{j\le J}\emaw jG_{t+1-j}$ be the truncated buffer of
\cref{lem:app-setup-truncation}, and let $T^{(J)}$ and $\Gtildebar^{(J)}_\ridge$
be the candidates \cref{eqn:app-drift-H,eqn:app-drift-Gbar} built from the
solution of the system \cref{eqn:app-de-system} for the weights $\emaw{}^{(J)}$.
\begin{enumerate}[label=(\roman*)]
\item For every fixed $J$,
$\sup_{\ridge\in[\ridge_-,\ridge_+]}\norm{\EE\,\Qridge\ridge(M^{(J)})-\Gtildebar^{(J)}_\ridge}_\F\to0$
as the dimension grows.
\item $\lim_{J\to\infty}\sup_B\sup_{\ridge\in[\ridge_-,\ridge_+]}\norm{\Gtildebar_\ridge-\Gtildebar^{(J)}_\ridge}_\F=0$,
where $\sup_B$ runs over the whole sequence of dimensions.
\item Consequently
\begin{equation}\label{eqn:app-drift-truncation}
\lim_{J\to\infty}\limsup_{B\to\infty}\sup_{\ridge\in[\ridge_-,\ridge_+]}
\norm{\EE\,\Qridge\ridge(\Mt)-\EE\,\Qridge\ridge(M^{(J)})}_\F=0 .
\end{equation}
\end{enumerate}
\end{proposition}
```
-/
theorem prop_app_drift_truncation_i (R : Muon.Setup.SetupRegime) {Ω : ℕ → Type} [∀ k, MeasurableSpace (Ω k)]
    (P : ∀ k, Measure (Ω k)) [∀ k, IsProbabilityMeasure (P k)]
    (S : ∀ k, FrozenSamples (P k) (R.m k) (R.n k) (R.B k)) (t : ℤ) (J : ℕ) :
    (∀ k, BddAbove ((fun ϱ => fro (EQ (truncW (emaW R.β) J) (R.F k) (S k) t ϱ - Gbar (truncW (emaW R.β) J) (R.F k) (specOutFM (R.F k)) (specInFM (R.F k)) ϱ)) '' Icc R.ϱlo R.ϱhi)) ∧
    Tendsto (fun k => ⨆ ϱ ∈ Icc R.ϱlo R.ϱhi, fro (EQ (truncW (emaW R.β) J) (R.F k) (S k) t ϱ - Gbar (truncW (emaW R.β) J) (R.F k) (specOutFM (R.F k)) (specInFM (R.F k)) ϱ))
      atTop (𝓝 0) :=
  prop_app_drift_truncation_i_weights R P S t (emaW R.β) (emaW_weightClass_regime R) J
/-- `prop:app-drift-truncation`, snapshot `cr-2026-10-23`. History truncation, part (iii): the limit `lim_J limsup_B` of the difference of the expected updates of `M_t` and `M^{(J)}` is zero, written in ε–N form (the order of the limits is fixed by the quantifiers: `J` first, then the dimension index `k`). Uses (i), (ii) and `thm:app-drift-mean` in the proof; the bound is a `BddAbove` plus the `⨆` bound.
Source, verbatim (`sections/03-drift/section.tex`):
```latex
\begin{proposition}[History truncation]\label{prop:app-drift-truncation}
Under \cref{assum:app-setup-regime}, for $J\ge0$ let $\emaw j^{(J)}\defeq\emaw j\mathbf 1_{j\le J}$,
let $M^{(J)}=\sum_{j\le J}\emaw jG_{t+1-j}$ be the truncated buffer of
\cref{lem:app-setup-truncation}, and let $T^{(J)}$ and $\Gtildebar^{(J)}_\ridge$
be the candidates \cref{eqn:app-drift-H,eqn:app-drift-Gbar} built from the
solution of the system \cref{eqn:app-de-system} for the weights $\emaw{}^{(J)}$.
\begin{enumerate}[label=(\roman*)]
\item For every fixed $J$,
$\sup_{\ridge\in[\ridge_-,\ridge_+]}\norm{\EE\,\Qridge\ridge(M^{(J)})-\Gtildebar^{(J)}_\ridge}_\F\to0$
as the dimension grows.
\item $\lim_{J\to\infty}\sup_B\sup_{\ridge\in[\ridge_-,\ridge_+]}\norm{\Gtildebar_\ridge-\Gtildebar^{(J)}_\ridge}_\F=0$,
where $\sup_B$ runs over the whole sequence of dimensions.
\item Consequently
\begin{equation}\label{eqn:app-drift-truncation}
\lim_{J\to\infty}\limsup_{B\to\infty}\sup_{\ridge\in[\ridge_-,\ridge_+]}
\norm{\EE\,\Qridge\ridge(\Mt)-\EE\,\Qridge\ridge(M^{(J)})}_\F=0 .
\end{equation}
\end{enumerate}
\end{proposition}
```
-/
theorem prop_app_drift_truncation_iii (R : Muon.Setup.SetupRegime) {Ω : ℕ → Type} [∀ k, MeasurableSpace (Ω k)]
    (P : ∀ k, Measure (Ω k)) [∀ k, IsProbabilityMeasure (P k)]
    (S : ∀ k, FrozenSamples (P k) (R.m k) (R.n k) (R.B k)) (t : ℤ) :
    ∀ ε > 0, ∃ J₀ : ℕ, ∀ J : ℕ, J₀ ≤ J → ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k →
      BddAbove ((fun ϱ => fro (EQ (emaW R.β) (R.F k) (S k) t ϱ
          - EQ (truncW (emaW R.β) J) (R.F k) (S k) t ϱ)) '' Icc R.ϱlo R.ϱhi) ∧
      (⨆ ϱ ∈ Icc R.ϱlo R.ϱhi, fro (EQ (emaW R.β) (R.F k) (S k) t ϱ
          - EQ (truncW (emaW R.β) J) (R.F k) (S k) t ϱ)) ≤ ε := by
  intro ε hε
  obtain ⟨δ, hδdef⟩ : ∃ δ : ℝ, δ = ε / 3 := ⟨_, rfl⟩
  have hδ0 : 0 < δ := by rw [hδdef]; exact div_pos hε (by norm_num)
  obtain ⟨-, hBdd, hTend, -⟩ := thm_app_drift_mean R P S t
  have hCS : 0 < R.CSig := lt_of_lt_of_le one_pos R.hC
  have hγ : 0 < max R.γstar 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  obtain ⟨J₁, hJ₁⟩ := prop_app_drift_truncation_ii (ϱlo := R.ϱlo) (ϱhi := R.ϱhi) hCS hγ
    R.hϱ.1 R.hϱ.2 (emaW_weightClass_regime R) δ hδ0
  have hgbar : ∀ J, J₁ ≤ J → ∀ k : ℕ, ∀ ϱ ∈ Icc R.ϱlo R.ϱhi,
      fro (Gbar (emaW R.β) (R.F k) (specOutFM (R.F k)) (specInFM (R.F k)) ϱ
        - Gbar (truncW (emaW R.β) J) (R.F k) (specOutFM (R.F k)) (specInFM (R.F k)) ϱ) ≤ δ := by
    intro J hJ k ϱ hϱ
    refine hJ₁ J hJ (R.m k) (R.n k) (R.B k) (R.F k) ?_ ϱ hϱ
    unfold DriftBound
    refine ⟨R.normOut k, R.normIn k, ?_⟩
    calc ((max (R.m k) (R.n k) : ℕ) : ℝ) ≤ R.γstar * (R.B k : ℝ) := R.dims k
      _ ≤ max R.γstar 1 * (R.B k : ℝ) :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (Nat.cast_nonneg _)
  obtain ⟨kA, hkA⟩ := Filter.eventually_atTop.1 (hTend.eventually (gt_mem_nhds hδ0))
  refine ⟨J₁, fun J hJ => ?_⟩
  obtain ⟨hBddJ, hTJ⟩ := prop_app_drift_truncation_i R P S t J
  obtain ⟨kB, hkB⟩ := Filter.eventually_atTop.1 (hTJ.eventually (gt_mem_nhds hδ0))
  refine ⟨max kA kB, fun k hk => ?_⟩
  have hkA' : kA ≤ k := le_trans (le_max_left _ _) hk
  have hkB' : kB ≤ k := le_trans (le_max_right _ _) hk
  have pw : ∀ ϱ ∈ Icc R.ϱlo R.ϱhi,
      fro (EQ (emaW R.β) (R.F k) (S k) t ϱ - EQ (truncW (emaW R.β) J) (R.F k) (S k) t ϱ) ≤ ε := by
    intro ϱ hϱ
    have hf : fro (EQ (emaW R.β) (R.F k) (S k) t ϱ
        - Gbar (emaW R.β) (R.F k) (specOutFM (R.F k)) (specInFM (R.F k)) ϱ) ≤ δ :=
      le_trans (mp_le_biSup (hBdd k) hϱ) (le_of_lt (hkA k hkA'))
    have hg := hgbar J hJ k ϱ hϱ
    have hh : fro (EQ (truncW (emaW R.β) J) (R.F k) (S k) t ϱ
        - Gbar (truncW (emaW R.β) J) (R.F k) (specOutFM (R.F k)) (specInFM (R.F k)) ϱ) ≤ δ :=
      le_trans (mp_le_biSup (hBddJ k) hϱ) (le_of_lt (hkB k hkB'))
    have hsplit := mp_fro_tri4 (EQ (emaW R.β) (R.F k) (S k) t ϱ)
      (EQ (truncW (emaW R.β) J) (R.F k) (S k) t ϱ)
      (Gbar (emaW R.β) (R.F k) (specOutFM (R.F k)) (specInFM (R.F k)) ϱ)
      (Gbar (truncW (emaW R.β) J) (R.F k) (specOutFM (R.F k)) (specInFM (R.F k)) ϱ)
    rw [mp_fro_comm (Gbar (truncW (emaW R.β) J) (R.F k) (specOutFM (R.F k)) (specInFM (R.F k)) ϱ)
      (EQ (truncW (emaW R.β) J) (R.F k) (S k) t ϱ)] at hsplit
    linarith
  refine ⟨?_, ?_⟩
  · refine ⟨ε, ?_⟩
    rintro _ ⟨ϱ, hϱ, rfl⟩
    exact pw ϱ hϱ
  · exact mp_biSup_le hε.le pw
/-- `prop:app-drift-truncation`, snapshot `cr-2026-10-23`. Assembled record of `prop:app-drift-truncation`: part (i) for every fixed `J`, part (ii) (Kernel.lean, L-C.4: `prop_app_drift_truncation_ii`, cited by declaration, class-uniform form), and part (iii). Term-proved conjunction.
Source, verbatim (`sections/03-drift/section.tex`):
```latex
\begin{proposition}[History truncation]\label{prop:app-drift-truncation}
Under \cref{assum:app-setup-regime}, for $J\ge0$ let $\emaw j^{(J)}\defeq\emaw j\mathbf 1_{j\le J}$,
let $M^{(J)}=\sum_{j\le J}\emaw jG_{t+1-j}$ be the truncated buffer of
\cref{lem:app-setup-truncation}, and let $T^{(J)}$ and $\Gtildebar^{(J)}_\ridge$
be the candidates \cref{eqn:app-drift-H,eqn:app-drift-Gbar} built from the
solution of the system \cref{eqn:app-de-system} for the weights $\emaw{}^{(J)}$.
\begin{enumerate}[label=(\roman*)]
\item For every fixed $J$,
$\sup_{\ridge\in[\ridge_-,\ridge_+]}\norm{\EE\,\Qridge\ridge(M^{(J)})-\Gtildebar^{(J)}_\ridge}_\F\to0$
as the dimension grows.
\item $\lim_{J\to\infty}\sup_B\sup_{\ridge\in[\ridge_-,\ridge_+]}\norm{\Gtildebar_\ridge-\Gtildebar^{(J)}_\ridge}_\F=0$,
where $\sup_B$ runs over the whole sequence of dimensions.
\item Consequently
\begin{equation}\label{eqn:app-drift-truncation}
\lim_{J\to\infty}\limsup_{B\to\infty}\sup_{\ridge\in[\ridge_-,\ridge_+]}
\norm{\EE\,\Qridge\ridge(\Mt)-\EE\,\Qridge\ridge(M^{(J)})}_\F=0 .
\end{equation}
\end{enumerate}
\end{proposition}
```
-/
theorem prop_app_drift_truncation (R : Muon.Setup.SetupRegime) {Ω : ℕ → Type} [∀ k, MeasurableSpace (Ω k)]
    (P : ∀ k, Measure (Ω k)) [∀ k, IsProbabilityMeasure (P k)]
    (S : ∀ k, FrozenSamples (P k) (R.m k) (R.n k) (R.B k)) (t : ℤ) :
    (∀ J : ℕ, (∀ k, BddAbove ((fun ϱ => fro (EQ (truncW (emaW R.β) J) (R.F k) (S k) t ϱ - Gbar (truncW (emaW R.β) J) (R.F k) (specOutFM (R.F k)) (specInFM (R.F k)) ϱ)) '' Icc R.ϱlo R.ϱhi)) ∧
      Tendsto (fun k => ⨆ ϱ ∈ Icc R.ϱlo R.ϱhi, fro (EQ (truncW (emaW R.β) J) (R.F k) (S k) t ϱ - Gbar (truncW (emaW R.β) J) (R.F k) (specOutFM (R.F k)) (specInFM (R.F k)) ϱ)) atTop (𝓝 0)) ∧
    (∀ CS γ : ℝ, 0 < CS → 0 < γ → ∀ ε > 0, ∃ J₀ : ℕ, ∀ J : ℕ, J₀ ≤ J →
      ∀ (m' n' B' : ℕ) (F : FrozenParams m' n' B'), DriftBound F CS γ →
        ∀ ϱ ∈ Icc R.ϱlo R.ϱhi,
          fro (Gbar (emaW R.β) F (specOutFM F) (specInFM F) ϱ -
            Gbar (truncW (emaW R.β) J) F (specOutFM F) (specInFM F) ϱ) ≤ ε) ∧
    (∀ ε > 0, ∃ J₀ : ℕ, ∀ J : ℕ, J₀ ≤ J → ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k →
      BddAbove ((fun ϱ => fro (EQ (emaW R.β) (R.F k) (S k) t ϱ
          - EQ (truncW (emaW R.β) J) (R.F k) (S k) t ϱ)) '' Icc R.ϱlo R.ϱhi) ∧
      (⨆ ϱ ∈ Icc R.ϱlo R.ϱhi, fro (EQ (emaW R.β) (R.F k) (S k) t ϱ
          - EQ (truncW (emaW R.β) J) (R.F k) (S k) t ϱ)) ≤ ε) :=
  ⟨fun J => prop_app_drift_truncation_i R P S t J,
   fun _ _ hC hγ => prop_app_drift_truncation_ii hC hγ R.hϱ.1 R.hϱ.2 (emaW_weightClass_regime R),
   prop_app_drift_truncation_iii R P S t⟩
private lemma mp4_isBranch_nonneg {F : ℝ → ℝ} {ν ν' : FiniteMeasure ℝ} {s : ℝ}
    {x : ℝ × ℝ × ℝ × ℝ} (h : IsBranchSol F ν ν' s x) :
    0 ≤ x.1 ∧ 0 ≤ x.2.1 ∧ 0 ≤ x.2.2.1 ∧ 0 ≤ x.2.2.2 := by
  obtain ⟨σ, σ', a, c⟩ := x
  obtain ⟨a1, a2, a3, a4, -⟩ := h
  exact ⟨a1, a2, a3, a4⟩

private lemma mp4_isUnit_det {k : ℕ} (S : Mat k k) (hS : S.PosSemidef) {a s : ℝ}
    (ha : 0 ≤ a) (hs : 0 < s) : (s • (1 : Mat k k) + a • S).det ≠ 0 := by
  set M : Mat k k := s • (1 : Mat k k) + a • S with hM
  have hinj : Function.Injective (M *ᵥ ·) := by
    intro y y' h
    have h' : M *ᵥ y = M *ᵥ y' := h
    have h0 : M *ᵥ (y - y') = 0 := by rw [Matrix.mulVec_sub, h', sub_self]
    set z := y - y' with hz
    have hSz : 0 ≤ ∑ i, z i * (S *ᵥ z) i := by
      have := hS.dotProduct_mulVec_nonneg z
      simpa [dotProduct, star_trivial] using this
    have hMz : M *ᵥ z = s • z + a • (S *ᵥ z) := by
      simp [hM, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec]
    have h1 : 0 = ∑ i, z i * (M *ᵥ z) i := by rw [h0]; simp
    have h2 : ∑ i, z i * (M *ᵥ z) i = s * ∑ i, z i ^ 2 + a * ∑ i, z i * (S *ᵥ z) i := by
      rw [hMz, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp; ring
    have hnn : 0 ≤ ∑ i, z i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
    have hsum : ∑ i, z i ^ 2 = 0 := by
      refine le_antisymm ?_ hnn
      nlinarith [mul_nonneg ha hSz]
    have hz0 : ∀ i, z i = 0 := fun i => by
      have := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg (z i))).mp hsum i
        (Finset.mem_univ _)
      exact (pow_eq_zero_iff two_ne_zero).mp this
    exact sub_eq_zero.mp (funext hz0)
  have hu : IsUnit M := Matrix.mulVec_injective_iff_isUnit.mp hinj
  exact ((Matrix.isUnit_iff_isUnit_det M).mp hu).ne_zero

private lemma mp4_int_pair {p q : ℕ} (g : Fin p → Fin q → ℝ) (T : ℝ → Fin p → Fin q → ℝ)
    (hint : ∀ i j, IntegrableOn (fun u : ℝ => T u i j) (Ioi 0)) :
    IntegrableOn (fun u : ℝ => ∑ i, ∑ j, g i j * T u i j) (Ioi 0) ∧
    ∫ u in Ioi (0 : ℝ), ∑ i, ∑ j, g i j * T u i j = ∑ i, ∑ j, g i j * ∫ u in Ioi (0 : ℝ), T u i j := by
  refine ⟨integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
    (hint i j).const_mul _, ?_⟩
  rw [integral_finset_sum _ (fun i _ => integrable_finsetSum _ fun j _ =>
    (hint i j).const_mul _)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_finset_sum _ (fun j _ => (hint i j).const_mul _)]
  exact Finset.sum_congr rfl fun j _ => integral_const_mul _ _

private lemma mp4_dot_symm {k : ℕ} (M : Mat k k) (hM : Mᵀ = M) (x y : Vec k) :
    dotProduct x (M *ᵥ y) = dotProduct (M *ᵥ x) y := by
  rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hM]

private lemma mp4_symm_of_psd {k : ℕ} (S : Mat k k) (hS : S.PosSemidef) : Sᵀ = S := by
  simpa using hS.isHermitian.eq

private lemma mp4_inv_eig {k : ℕ} (S : Mat k k) (hS : S.PosSemidef) {a s μ : ℝ}
    (ha : 0 ≤ a) (hs : 0 < s) (hμ : 0 ≤ μ) {u : Vec k} (hu : S *ᵥ u = μ • u) :
    (s • (1 : Mat k k) + a • S)⁻¹ *ᵥ u = (s + a * μ)⁻¹ • u := by
  set M : Mat k k := s • (1 : Mat k k) + a • S with hM
  have hdet := mp4_isUnit_det S hS ha hs
  have hMu : M *ᵥ u = (s + a * μ) • u := by
    rw [hM, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, hu,
      smul_smul, add_smul]
  have hpos : 0 < s + a * μ := by positivity
  have h1 : M⁻¹ * M = 1 := Matrix.nonsing_inv_mul M (isUnit_iff_ne_zero.mpr hdet)
  have h2 : u = (s + a * μ) • (M⁻¹ *ᵥ u) := by
    calc u = (M⁻¹ * M) *ᵥ u := by rw [h1, Matrix.one_mulVec]
      _ = M⁻¹ *ᵥ (M *ᵥ u) := by rw [Matrix.mulVec_mulVec]
      _ = _ := by rw [hMu, Matrix.mulVec_smul]
  calc M⁻¹ *ᵥ u = (s + a * μ)⁻¹ • ((s + a * μ) • (M⁻¹ *ᵥ u)) := by
        rw [smul_smul, inv_mul_cancel₀ hpos.ne', one_smul]
    _ = (s + a * μ)⁻¹ • u := by rw [← h2]

private lemma mp4_dot_mulVec {p q : ℕ} (X : Mat p q) (U : Vec p) (V : Vec q) :
    dotProduct U (X *ᵥ V) = ∑ i, ∑ j, (U i * V j) * X i j := by
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

private lemma mp4_dot_integral {α : Type*} [MeasurableSpace α] (μ : Measure α)
    {m n : ℕ} (X : α → Mat m n) (hX : ∀ i j, Integrable (fun a => X a i j) μ)
    (u : Vec m) (v : Vec n) :
    (∫ a, dotProduct u (X a *ᵥ v) ∂μ) =
      dotProduct u ((Matrix.of fun i j => ∫ a, X a i j ∂μ) *ᵥ v) := by
  simp_rw [mp4_dot_mulVec]
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => (hX i j).const_mul _))]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_finsetSum _ (fun j _ => (hX i j).const_mul _)]
  simp only [integral_const_mul, Matrix.of_apply]

private lemma mp4_parseval {m n : ℕ} {C : Covariances m n} (SD : SpectralData C)
    (X : Mat m n) :
    Real.sqrt (∑ i, ∑ j, dotProduct (SD.u i) (X *ᵥ SD.v j) ^ 2) = fro X := by
  have ht : ∀ {p q : ℕ} (Y : Mat p q), (Y * Yᵀ).trace = fro Y ^ 2 := by
    intro p q Y
    rw [mp_fro_sq]
    simp [Matrix.trace, Matrix.diag, Matrix.mul_apply, pow_two]
  have he : fro (SD.uOutᵀ * X * SD.vIn) ^ 2 = fro X ^ 2 := by
    rw [← ht, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc SD.vIn SD.vInᵀ, mul_eq_one_comm.mp SD.hvIn, Matrix.one_mul]
    rw [Matrix.trace_mul_comm]
    simp only [Matrix.mul_assoc]
    rw [mul_eq_one_comm.mp SD.huOut, Matrix.mul_one, ht]
  have hs : (∑ i, ∑ j, dotProduct (SD.u i) (X *ᵥ SD.v j) ^ 2) = fro X ^ 2 := by
    rw [← he, mp_fro_sq]
    simp_rw [P_apply]
  rw [hs, Real.sqrt_sq (mp_fro_nonneg X)]

open scoped MatrixOrder in
private lemma mp4_EG_state {m n B : ℕ} (F : FrozenParams m n B) (D : Mat m n)
    (hD : F.A = Ahat F.C D) :
    EG F = (Real.sqrt (2 * riskSigma F.C D))⁻¹ • (F.C.Sout * D * F.C.Sin) := by
  have ho : rOut F.C * rOut F.C = F.C.Sout :=
    CFC.sqrt_mul_sqrt_self _ (Matrix.nonneg_iff_posSemidef.mpr F.C.psdOut)
  have hi : rIn F.C * rIn F.C = F.C.Sin :=
    CFC.sqrt_mul_sqrt_self _ (Matrix.nonneg_iff_posSemidef.mpr F.C.psdIn)
  unfold EG
  rw [hD]
  simp only [Ahat, Arot, Matrix.mul_smul, Matrix.smul_mul]
  congr 1
  calc rOut F.C * (rOut F.C * D * rIn F.C) * rIn F.C =
      (rOut F.C * rOut F.C) * D * (rIn F.C * rIn F.C) := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [ho, hi]

private lemma mp4_gbar_state {m n B : ℕ} {CS γ : ℝ} (hC : 0 < CS) (hγ : 0 < γ)
    {w : ℕ → ℝ} (hw : WeightClass w) (F : FrozenParams m n B) (h : DriftBound F CS γ)
    (SD : SpectralData F.C) (D : Mat m n) (hD : F.A = Ahat F.C D)
    {ϱ : ℝ} (hϱ : 0 < ϱ) (i : Fin m) (j : Fin n) :
    dotProduct (SD.u i) (Gbar w F (specOutFM F) (specInFM F) ϱ *ᵥ SD.v j) =
      (Real.sqrt 2 * kernel w (specOutFM F) (specInFM F) ϱ (SD.μ i) (SD.lam j)) /
        Real.sqrt (2 * riskSigma F.C D) * dotProduct (SD.u i) (D *ᵥ SD.v j) := by
  have hp := spectral_mem_classK F h
  have hF := Fw_admissible hw.1
  have hμ := μ_nonneg SD i
  have hl := lam_nonneg SD j
  obtain ⟨hint, -⟩ := gbar_integrable_bound hC hγ hw F h hϱ
  let c := (Real.sqrt (2 * riskSigma F.C D))⁻¹ * dotProduct (SD.u i) (D *ᵥ SD.v j)
  let f := fun t : ℝ => (ϱ + t ^ 2) * Lw w (branchQ w (specOutFM F) (specInFM F) (ϱ + t ^ 2)) * SD.μ i * SD.lam j /
    ((ϱ + t ^ 2 + (branchSol (Fw w) (specOutFM F) (specInFM F) (ϱ + t ^ 2)).2.2.1 * SD.μ i) *
     (ϱ + t ^ 2 + (branchSol (Fw w) (specOutFM F) (specInFM F) (ϱ + t ^ 2)).2.2.2 * SD.lam j))
  have hpt : ∀ t : ℝ, dotProduct (SD.u i)
      (Tcand w F (specOutFM F) (specInFM F) (ϱ + t ^ 2) *ᵥ SD.v j) = c * f t := by
    intro t
    have hz : 0 < ϱ + t ^ 2 := by positivity
    obtain ⟨-, -, h3, h4⟩ := mp4_isBranch_nonneg (branchSol_spec hF hC hγ hp hz)
    have hR : Rtbar (Fw w) (specOutFM F) (specInFM F) F.C (ϱ + t ^ 2) *ᵥ SD.v j =
        (ϱ + t ^ 2 + (branchSol (Fw w) (specOutFM F) (specInFM F) (ϱ + t ^ 2)).2.2.2 * SD.lam j)⁻¹ • SD.v j :=
      mp4_inv_eig F.C.Sin F.C.psdIn h4 hz hl (eig_v SD j)
    have hL : Rbar (Fw w) (specOutFM F) (specInFM F) F.C (ϱ + t ^ 2) *ᵥ SD.u i =
        (ϱ + t ^ 2 + (branchSol (Fw w) (specOutFM F) (specInFM F) (ϱ + t ^ 2)).2.2.1 * SD.μ i)⁻¹ • SD.u i :=
      mp4_inv_eig F.C.Sout F.C.psdOut h3 hz hμ (eig_u SD i)
    have hsym : (Rbar (Fw w) (specOutFM F) (specInFM F) F.C (ϱ + t ^ 2))ᵀ =
        Rbar (Fw w) (specOutFM F) (specInFM F) F.C (ϱ + t ^ 2) := by
      unfold Rbar
      rw [Matrix.transpose_nonsing_inv]
      congr 1
      rw [Matrix.transpose_add, Matrix.transpose_smul, Matrix.transpose_smul,
        Matrix.transpose_one, mp4_symm_of_psd _ F.C.psdOut]
    unfold Tcand
    rw [mp4_EG_state F D hD]
    simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_mulVec, dotProduct_smul,
      smul_eq_mul, ← Matrix.mulVec_mulVec]
    rw [hR]
    simp only [Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]
    rw [mp4_dot_symm _ hsym, hL]
    simp only [smul_dotProduct, smul_eq_mul]
    rw [mp4_dot_symm _ (mp4_symm_of_psd _ F.C.psdOut), eig_u SD i, eig_v SD j]
    simp only [smul_dotProduct, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]
    dsimp [c, f]
    simp only [div_eq_mul_inv, _root_.mul_inv_rev]
    ring
  have hG : dotProduct (SD.u i) (Gbar w F (specOutFM F) (specInFM F) ϱ *ᵥ SD.v j) =
      (2 / Real.pi) * (c * ∫ t in Ioi (0 : ℝ), f t) := by
    have he := mp4_dot_integral (volume.restrict (Ioi (0 : ℝ)))
      (fun t => Tcand w F (specOutFM F) (specInFM F) (ϱ + t ^ 2)) hint (SD.u i) (SD.v j)
    have hg : Gbar w F (specOutFM F) (specInFM F) ϱ =
        (2 / Real.pi) • (Matrix.of fun a b => ∫ t in Ioi (0 : ℝ), Tcand w F (specOutFM F) (specInFM F) (ϱ + t ^ 2) a b) := rfl
    rw [hg, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, ← he]
    simp_rw [hpt]
    rw [integral_const_mul]
  rw [hG]
  change _ = (Real.sqrt 2 * ((Real.sqrt 2 / Real.pi) * ∫ t in Ioi (0 : ℝ), f t)) / _ * _
  dsimp [c]
  have hs : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  simp only [div_eq_mul_inv]
  calc _ = (2 * Real.pi⁻¹) * ((Real.sqrt (2 * riskSigma F.C D))⁻¹ * dotProduct (SD.u i) (D *ᵥ SD.v j) * ∫ t in Ioi (0 : ℝ), f t) := by ring
    _ = (Real.sqrt 2 * Real.sqrt 2) * Real.pi⁻¹ * ((Real.sqrt (2 * riskSigma F.C D))⁻¹ * dotProduct (SD.u i) (D *ᵥ SD.v j) * ∫ t in Ioi (0 : ℝ), f t) := by rw [hs]
    _ = _ := by ring

private lemma mp4_fro_proj {m n : ℕ} {C : Covariances m n} (SD : SpectralData C)
    (X : Mat m n) : fro (Matrix.of fun i j => dotProduct (SD.u i) (X *ᵥ SD.v j)) = fro X := by
  simpa only [fro, Matrix.of_apply, Real.norm_eq_abs, sq_abs] using mp4_parseval SD X

private lemma mp4_Q_integrable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {m n B : ℕ} (w : ℕ → ℝ) (F : FrozenParams m n B)
    (S : FrozenSamples P m n B) (t : ℤ) {ϱ : ℝ} (hϱ : 0 < ϱ) :
    ∀ i j, Integrable (fun ω => Q ϱ (WeightedBuf w F S t ω) i j) P := by
  have hm := mp_meas_Q hϱ (mp_meas_WB w F S t)
  intro i j
  refine Integrable.of_bound (C := Real.sqrt (min m n : ℕ)) ?_ ?_
  · exact ((measurable_pi_apply j).comp ((measurable_pi_apply i).comp hm)).aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun ω => ?_
    rw [Real.norm_eq_abs]
    refine (mp_abs_entry_le_fro _ i j).trans ?_
    obtain ⟨-, h2, h3, -⟩ := lem_app_setup_filter_i ϱ hϱ.le (WeightedBuf w F S t ω)
    exact Real.le_sqrt_of_sq_le (h2.trans (by exact_mod_cast h3))

private lemma mp4_weighted_bound {m n : ℕ} (a e b : Mat m n) {C : ℝ}
    (hC : 0 ≤ C) (hb : ∀ i j, |b i j| ≤ C) :
    |∑ i, ∑ j, b i j * a i j * e i j| ≤ C * fro a * fro e := by
  have hfa : fro (Matrix.of fun i j => |a i j|) = fro a := by
    unfold fro
    simp only [Matrix.of_apply, Real.norm_eq_abs, abs_abs, sq_abs]
  have hfe : fro (Matrix.of fun i j => |e i j|) = fro e := by
    unfold fro
    simp only [Matrix.of_apply, Real.norm_eq_abs, abs_abs, sq_abs]
  calc
    |∑ i, ∑ j, b i j * a i j * e i j| ≤ ∑ i, |∑ j, b i j * a i j * e i j| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, ∑ j, |b i j * a i j * e i j| :=
      Finset.sum_le_sum (fun i _ => Finset.abs_sum_le_sum_abs _ _)
    _ ≤ ∑ i, ∑ j, C * (|a i j| * |e i j|) := by
      refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
      simp only [abs_mul]
      nlinarith [mul_le_mul_of_nonneg_right (hb i j) (mul_nonneg (abs_nonneg (a i j)) (abs_nonneg (e i j)))]
    _ = C * (∑ i, ∑ j, |a i j| * |e i j|) := by simp only [Finset.mul_sum]
    _ ≤ C * (fro a * fro e) := by
      apply mul_le_mul_of_nonneg_left _ hC
      simpa only [hfa, hfe, Matrix.of_apply] using
        mp_inner_le (Matrix.of fun i j => |a i j|) (Matrix.of fun i j => |e i j|)
    _ = _ := by ring

/-- `cor:app-drift-kernel`, snapshot `cr-2026-10-23`. The drift kernel, part (i), general weight sequence. Four claims: the identity for every `(i,j)` and `ϱ` (both forms of `eqn:app-drift-projected`); the `ℓ²`-supremum of `E_ϱ` equals `ε_B` and tends to `0`; `eqn:app-drift-Dij`; and the tested bound for every bounded `φ`. The frozen state `Δ_t` enters as `Dt` with `F.A = Ahat F.C Dt`, `ℛ(t) = riskSigma F.C Dt > 0`. Part (ii) is `cor_app_drift_kernel_ii` (L-C.4).
Source, verbatim (`sections/03-drift/section.tex`):
```latex
\begin{corollary}[The drift kernel]\label{cor:app-drift-kernel}
Under \cref{assum:app-setup-regime}, let $\Gtilde=\Qridge\ridge(\Mt)$ be the
frozen-state update and put $(E_\ridge)_{ij}\defeq u_i^\T\big(\EE\Gtilde-\Gtildebar_\ridge\big)v_j$.
\begin{enumerate}[label=(\roman*)]
\item For every pair $(i,j)$ and every $\ridge\in[\ridge_-,\ridge_+]$,
\begin{equation}\label{eqn:app-drift-projected}
\EE\big[u_i^\T\Gtilde v_j\big]=\frac{\sqrt2\,\mathfrak d(\mu_i,\lambda_j)}{\sqrt{2\cR(t)}}\,(u_i^\T\Dt v_j)+(E_\ridge)_{ij}
=\frac{\mathfrak d(\mu_i,\lambda_j)}{\sqrt{\cR(t)}}\,(u_i^\T\Dt v_j)+(E_\ridge)_{ij},
\end{equation}
and $\sup_{\ridge\in[\ridge_-,\ridge_+]}\big(\sum_{i,j}(E_\ridge)_{ij}^2\big)^{1/2}=\varepsilon_B\to0$.
Consequently the frozen-state drift \cref{eqn:app-setup-DV} of the update
$\Gtilde$ is
\begin{equation}\label{eqn:app-drift-Dij}
\cD_{ij}(t)=\frac{\mathfrak d_{ij}}{\sqrt{\cR(t)}}\,\CMscr Q_{ij}(t)+(u_i^\T\Dt v_j)(E_\ridge)_{ij},
\qquad \mathfrak d_{ij}\defeq\mathfrak d(\mu_i,\lambda_j),
\end{equation}
and for every bounded function $\phi$ on $[0,\infty)^2$,
\begin{equation}\label{eqn:app-drift-tested}
\Big|\sum_{i,j}\phi(\mu_i,\lambda_j)\,(u_i^\T\Dt v_j)\,(E_\ridge)_{ij}\Big|\le\norm\phi_\infty\,\norm{\Dt}_\F\,\varepsilon_B .
\end{equation}
\item For every $\ridge\in[\ridge_-,\ridge_+]$ the function $\mathfrak d$ is
continuous on $[0,\infty)^2$, vanishes when $\mu=0$ or $\lambda=0$, and satisfies
\begin{equation}\label{eqn:app-drift-kernel-bounds}
0\le\mathfrak d(\mu,\lambda)\le\frac{\mu\lambda}{\sqrt{2\ridge}},\qquad
\abs{\partial_\mu\mathfrak d(\mu,\lambda)}\le\frac{\lambda}{\sqrt{2\ridge}},\qquad
\abs{\partial_\lambda\mathfrak d(\mu,\lambda)}\le\frac{\mu}{\sqrt{2\ridge}},
\end{equation}
with one-sided derivatives at $0$; in particular $\mathfrak d$ is Lipschitz on
$[0,C_\Sigma]^2$ with constant $C_\Sigma/\sqrt{2\ridge_-}$ in each variable.
\end{enumerate}
\end{corollary}
```
-/
theorem cor_app_drift_kernel_i_weights (R : Muon.Setup.SetupRegime) {Ω : ℕ → Type} [∀ k, MeasurableSpace (Ω k)]
    (P : ∀ k, Measure (Ω k)) [∀ k, IsProbabilityMeasure (P k)]
    (S : ∀ k, FrozenSamples (P k) (R.m k) (R.n k) (R.B k)) (t : ℤ)
    (w : ℕ → ℝ) (hw : WeightClass w)
    (SD : ∀ k, SpectralData (R.F k).C) (Dt : ∀ k, Mat (R.m k) (R.n k))
    (hDt : ∀ k, (R.F k).A = Ahat (R.F k).C (Dt k)) (hRt : ∀ k, 0 < riskSigma (R.F k).C (Dt k)) :
    (∀ k, ∀ (i : Fin (R.m k)) (j : Fin (R.n k)), ∀ ϱ ∈ Icc R.ϱlo R.ϱhi,
      ∫ ω, dotProduct ((SD k).u i) (Q ϱ (WeightedBuf w (R.F k) (S k) t ω) *ᵥ (SD k).v j) ∂(P k) =
        (Real.sqrt 2 * kernel w (specOutFM (R.F k)) (specInFM (R.F k)) ϱ ((SD k).μ i) ((SD k).lam j)) / Real.sqrt (2 * riskSigma (R.F k).C (Dt k)) * dotProduct ((SD k).u i) ((Dt k) *ᵥ (SD k).v j) + Erho w (R.F k) (SD k) (S k) t (specOutFM (R.F k)) (specInFM (R.F k)) ϱ i j ∧
      ∫ ω, dotProduct ((SD k).u i) (Q ϱ (WeightedBuf w (R.F k) (S k) t ω) *ᵥ (SD k).v j) ∂(P k) =
        kernel w (specOutFM (R.F k)) (specInFM (R.F k)) ϱ ((SD k).μ i) ((SD k).lam j) / Real.sqrt (riskSigma (R.F k).C (Dt k)) * dotProduct ((SD k).u i) ((Dt k) *ᵥ (SD k).v j) + Erho w (R.F k) (SD k) (S k) t (specOutFM (R.F k)) (specInFM (R.F k)) ϱ i j) ∧
    (∀ k, BddAbove ((fun ϱ => Real.sqrt (∑ i : Fin (R.m k), ∑ j : Fin (R.n k),
        Erho w (R.F k) (SD k) (S k) t (specOutFM (R.F k)) (specInFM (R.F k)) ϱ i j ^ 2)) '' Icc R.ϱlo R.ϱhi) ∧
      (⨆ ϱ ∈ Icc R.ϱlo R.ϱhi, Real.sqrt (∑ i : Fin (R.m k), ∑ j : Fin (R.n k),
        Erho w (R.F k) (SD k) (S k) t (specOutFM (R.F k)) (specInFM (R.F k)) ϱ i j ^ 2)) =
        epsB w (R.F k) (S k) t (specOutFM (R.F k)) (specInFM (R.F k)) R.ϱlo R.ϱhi) ∧
    Tendsto (fun k => epsB w (R.F k) (S k) t (specOutFM (R.F k)) (specInFM (R.F k)) R.ϱlo R.ϱhi) atTop (𝓝 0) ∧
    (∀ k, ∀ (i : Fin (R.m k)) (j : Fin (R.n k)), ∀ ϱ ∈ Icc R.ϱlo R.ϱhi,
      dotProduct ((SD k).u i) ((Dt k) *ᵥ (SD k).v j) * ∫ ω, dotProduct ((SD k).u i) (Q ϱ (WeightedBuf w (R.F k) (S k) t ω) *ᵥ (SD k).v j) ∂(P k) =
        kernel w (specOutFM (R.F k)) (specInFM (R.F k)) ϱ ((SD k).μ i) ((SD k).lam j) / Real.sqrt (riskSigma (R.F k).C (Dt k)) * modeQ (SD k) (Dt k) i j +
          dotProduct ((SD k).u i) ((Dt k) *ᵥ (SD k).v j) * Erho w (R.F k) (SD k) (S k) t (specOutFM (R.F k)) (specInFM (R.F k)) ϱ i j) ∧
    (∀ k, ∀ ϱ ∈ Icc R.ϱlo R.ϱhi, ∀ (φ : ℝ → ℝ → ℝ) (C : ℝ),
      (∀ x y : ℝ, 0 ≤ x → 0 ≤ y → |φ x y| ≤ C) →
      |∑ i : Fin (R.m k), ∑ j : Fin (R.n k), φ ((SD k).μ i) ((SD k).lam j) *
          dotProduct ((SD k).u i) ((Dt k) *ᵥ (SD k).v j) * Erho w (R.F k) (SD k) (S k) t (specOutFM (R.F k)) (specInFM (R.F k)) ϱ i j| ≤
        C * fro (Dt k) * epsB w (R.F k) (S k) t (specOutFM (R.F k)) (specInFM (R.F k)) R.ϱlo R.ϱhi) := by
  have hCS : 0 < R.CSig := lt_of_lt_of_le one_pos R.hC
  have hγ : 0 < max R.γstar 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hD : ∀ k, DriftBound (R.F k) R.CSig (max R.γstar 1) := by
    intro k
    refine ⟨R.normOut k, R.normIn k, ?_⟩
    exact (R.dims k).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Nat.cast_nonneg _))
  obtain ⟨-, hBdd, hTend, -⟩ := thm_app_drift_mean_weights R P S t w hw
  have hParse : ∀ k ϱ, Real.sqrt (∑ i : Fin (R.m k), ∑ j : Fin (R.n k),
      Erho w (R.F k) (SD k) (S k) t (specOutFM (R.F k)) (specInFM (R.F k)) ϱ i j ^ 2) =
      fro (EQ w (R.F k) (S k) t ϱ - Gbar w (R.F k) (specOutFM (R.F k)) (specInFM (R.F k)) ϱ) := by
    intro k ϱ
    exact mp4_parseval (SD k) _
  have hProj : ∀ k, ∀ (i : Fin (R.m k)) (j : Fin (R.n k)), ∀ ϱ ∈ Icc R.ϱlo R.ϱhi,
      (∫ ω, dotProduct ((SD k).u i) (Q ϱ (WeightedBuf w (R.F k) (S k) t ω) *ᵥ (SD k).v j) ∂(P k)) =
        (Real.sqrt 2 * kernel w (specOutFM (R.F k)) (specInFM (R.F k)) ϱ ((SD k).μ i) ((SD k).lam j)) /
        Real.sqrt (2 * riskSigma (R.F k).C (Dt k)) * dotProduct ((SD k).u i) ((Dt k) *ᵥ (SD k).v j) +
        Erho w (R.F k) (SD k) (S k) t (specOutFM (R.F k)) (specInFM (R.F k)) ϱ i j := by
    intro k i j ϱ hϱ
    have hp : 0 < ϱ := R.hϱ.1.trans_le hϱ.1
    have he := mp4_dot_integral (P k) (fun ω => Q ϱ (WeightedBuf w (R.F k) (S k) t ω))
      (mp4_Q_integrable w (R.F k) (S k) t hp) ((SD k).u i) ((SD k).v j)
    change (∫ ω, dotProduct ((SD k).u i) (Q ϱ (WeightedBuf w (R.F k) (S k) t ω) *ᵥ (SD k).v j) ∂(P k)) =
      dotProduct ((SD k).u i) (EQ w (R.F k) (S k) t ϱ *ᵥ (SD k).v j) at he
    rw [he]
    have hg := mp4_gbar_state hCS hγ hw (R.F k) (hD k) (SD k) (Dt k) (hDt k) hp i j
    simp only [Erho, Matrix.of_apply, Matrix.sub_mulVec, dotProduct_sub]
    linarith
  have hScale : ∀ k d, Real.sqrt 2 * d / Real.sqrt (2 * riskSigma (R.F k).C (Dt k)) =
      d / Real.sqrt (riskSigma (R.F k).C (Dt k)) := by
    intro k d
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
    exact mul_div_mul_left d _ (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)).ne'
  have hProj' : ∀ k, ∀ (i : Fin (R.m k)) (j : Fin (R.n k)), ∀ ϱ ∈ Icc R.ϱlo R.ϱhi,
      (∫ ω, dotProduct ((SD k).u i) (Q ϱ (WeightedBuf w (R.F k) (S k) t ω) *ᵥ (SD k).v j) ∂(P k)) =
        kernel w (specOutFM (R.F k)) (specInFM (R.F k)) ϱ ((SD k).μ i) ((SD k).lam j) /
        Real.sqrt (riskSigma (R.F k).C (Dt k)) * dotProduct ((SD k).u i) ((Dt k) *ᵥ (SD k).v j) +
        Erho w (R.F k) (SD k) (S k) t (specOutFM (R.F k)) (specInFM (R.F k)) ϱ i j := by
    intro k i j ϱ hϱ
    simpa only [hScale] using hProj k i j ϱ hϱ
  refine ⟨fun k i j ϱ hϱ => ⟨hProj k i j ϱ hϱ, hProj' k i j ϱ hϱ⟩, ?_, hTend, ?_, ?_⟩
  · intro k
    simp_rw [hParse]
    exact ⟨hBdd k, rfl⟩
  · intro k i j ϱ hϱ
    rw [hProj' k i j ϱ hϱ]
    unfold modeQ
    ring
  · intro k ϱ hϱ φ C hφ
    have hC : 0 ≤ C := (abs_nonneg (φ 0 0)).trans (hφ 0 0 le_rfl le_rfl)
    have he : fro (Erho w (R.F k) (SD k) (S k) t (specOutFM (R.F k)) (specInFM (R.F k)) ϱ) ≤
        epsB w (R.F k) (S k) t (specOutFM (R.F k)) (specInFM (R.F k)) R.ϱlo R.ϱhi := by
      unfold Erho
      rw [mp4_fro_proj]
      exact mp_le_biSup (hBdd k) hϱ
    have ha : fro (Matrix.of fun i j => dotProduct ((SD k).u i) ((Dt k) *ᵥ (SD k).v j)) = fro (Dt k) :=
      mp4_fro_proj (SD k) (Dt k)
    have hb := mp4_weighted_bound
      (Matrix.of fun i j => dotProduct ((SD k).u i) ((Dt k) *ᵥ (SD k).v j))
      (Erho w (R.F k) (SD k) (S k) t (specOutFM (R.F k)) (specInFM (R.F k)) ϱ)
      (Matrix.of fun i j => φ ((SD k).μ i) ((SD k).lam j)) hC
      (fun i j => hφ _ _ (μ_nonneg (SD k) i) (lam_nonneg (SD k) j))
    simp only [Matrix.of_apply, ha] at hb
    exact hb.trans (mul_le_mul_of_nonneg_left he (mul_nonneg hC (mp_fro_nonneg _)))
/-- `cor:app-drift-kernel`, snapshot `cr-2026-10-23`. The drift kernel, part (i), EMA record at `emaW R.β`. Term-proved instance of `cor_app_drift_kernel_i_weights`.
Source, verbatim (`sections/03-drift/section.tex`):
```latex
\begin{corollary}[The drift kernel]\label{cor:app-drift-kernel}
Under \cref{assum:app-setup-regime}, let $\Gtilde=\Qridge\ridge(\Mt)$ be the
frozen-state update and put $(E_\ridge)_{ij}\defeq u_i^\T\big(\EE\Gtilde-\Gtildebar_\ridge\big)v_j$.
\begin{enumerate}[label=(\roman*)]
\item For every pair $(i,j)$ and every $\ridge\in[\ridge_-,\ridge_+]$,
\begin{equation}\label{eqn:app-drift-projected}
\EE\big[u_i^\T\Gtilde v_j\big]=\frac{\sqrt2\,\mathfrak d(\mu_i,\lambda_j)}{\sqrt{2\cR(t)}}\,(u_i^\T\Dt v_j)+(E_\ridge)_{ij}
=\frac{\mathfrak d(\mu_i,\lambda_j)}{\sqrt{\cR(t)}}\,(u_i^\T\Dt v_j)+(E_\ridge)_{ij},
\end{equation}
and $\sup_{\ridge\in[\ridge_-,\ridge_+]}\big(\sum_{i,j}(E_\ridge)_{ij}^2\big)^{1/2}=\varepsilon_B\to0$.
Consequently the frozen-state drift \cref{eqn:app-setup-DV} of the update
$\Gtilde$ is
\begin{equation}\label{eqn:app-drift-Dij}
\cD_{ij}(t)=\frac{\mathfrak d_{ij}}{\sqrt{\cR(t)}}\,\CMscr Q_{ij}(t)+(u_i^\T\Dt v_j)(E_\ridge)_{ij},
\qquad \mathfrak d_{ij}\defeq\mathfrak d(\mu_i,\lambda_j),
\end{equation}
and for every bounded function $\phi$ on $[0,\infty)^2$,
\begin{equation}\label{eqn:app-drift-tested}
\Big|\sum_{i,j}\phi(\mu_i,\lambda_j)\,(u_i^\T\Dt v_j)\,(E_\ridge)_{ij}\Big|\le\norm\phi_\infty\,\norm{\Dt}_\F\,\varepsilon_B .
\end{equation}
\item For every $\ridge\in[\ridge_-,\ridge_+]$ the function $\mathfrak d$ is
continuous on $[0,\infty)^2$, vanishes when $\mu=0$ or $\lambda=0$, and satisfies
\begin{equation}\label{eqn:app-drift-kernel-bounds}
0\le\mathfrak d(\mu,\lambda)\le\frac{\mu\lambda}{\sqrt{2\ridge}},\qquad
\abs{\partial_\mu\mathfrak d(\mu,\lambda)}\le\frac{\lambda}{\sqrt{2\ridge}},\qquad
\abs{\partial_\lambda\mathfrak d(\mu,\lambda)}\le\frac{\mu}{\sqrt{2\ridge}},
\end{equation}
with one-sided derivatives at $0$; in particular $\mathfrak d$ is Lipschitz on
$[0,C_\Sigma]^2$ with constant $C_\Sigma/\sqrt{2\ridge_-}$ in each variable.
\end{enumerate}
\end{corollary}
```
-/
theorem cor_app_drift_kernel_i (R : Muon.Setup.SetupRegime) {Ω : ℕ → Type} [∀ k, MeasurableSpace (Ω k)]
    (P : ∀ k, Measure (Ω k)) [∀ k, IsProbabilityMeasure (P k)]
    (S : ∀ k, FrozenSamples (P k) (R.m k) (R.n k) (R.B k)) (t : ℤ)
    (SD : ∀ k, SpectralData (R.F k).C) (Dt : ∀ k, Mat (R.m k) (R.n k))
    (hDt : ∀ k, (R.F k).A = Ahat (R.F k).C (Dt k)) (hRt : ∀ k, 0 < riskSigma (R.F k).C (Dt k)) :
    (∀ k, ∀ (i : Fin (R.m k)) (j : Fin (R.n k)), ∀ ϱ ∈ Icc R.ϱlo R.ϱhi,
      ∫ ω, dotProduct ((SD k).u i) (Q ϱ (WeightedBuf (emaW R.β) (R.F k) (S k) t ω) *ᵥ (SD k).v j) ∂(P k) =
        (Real.sqrt 2 * kernel (emaW R.β) (specOutFM (R.F k)) (specInFM (R.F k)) ϱ ((SD k).μ i) ((SD k).lam j)) / Real.sqrt (2 * riskSigma (R.F k).C (Dt k)) * dotProduct ((SD k).u i) ((Dt k) *ᵥ (SD k).v j) + Erho (emaW R.β) (R.F k) (SD k) (S k) t (specOutFM (R.F k)) (specInFM (R.F k)) ϱ i j ∧
      ∫ ω, dotProduct ((SD k).u i) (Q ϱ (WeightedBuf (emaW R.β) (R.F k) (S k) t ω) *ᵥ (SD k).v j) ∂(P k) =
        kernel (emaW R.β) (specOutFM (R.F k)) (specInFM (R.F k)) ϱ ((SD k).μ i) ((SD k).lam j) / Real.sqrt (riskSigma (R.F k).C (Dt k)) * dotProduct ((SD k).u i) ((Dt k) *ᵥ (SD k).v j) + Erho (emaW R.β) (R.F k) (SD k) (S k) t (specOutFM (R.F k)) (specInFM (R.F k)) ϱ i j) ∧
    (∀ k, BddAbove ((fun ϱ => Real.sqrt (∑ i : Fin (R.m k), ∑ j : Fin (R.n k),
        Erho (emaW R.β) (R.F k) (SD k) (S k) t (specOutFM (R.F k)) (specInFM (R.F k)) ϱ i j ^ 2)) '' Icc R.ϱlo R.ϱhi) ∧
      (⨆ ϱ ∈ Icc R.ϱlo R.ϱhi, Real.sqrt (∑ i : Fin (R.m k), ∑ j : Fin (R.n k),
        Erho (emaW R.β) (R.F k) (SD k) (S k) t (specOutFM (R.F k)) (specInFM (R.F k)) ϱ i j ^ 2)) =
        epsB (emaW R.β) (R.F k) (S k) t (specOutFM (R.F k)) (specInFM (R.F k)) R.ϱlo R.ϱhi) ∧
    Tendsto (fun k => epsB (emaW R.β) (R.F k) (S k) t (specOutFM (R.F k)) (specInFM (R.F k)) R.ϱlo R.ϱhi) atTop (𝓝 0) ∧
    (∀ k, ∀ (i : Fin (R.m k)) (j : Fin (R.n k)), ∀ ϱ ∈ Icc R.ϱlo R.ϱhi,
      dotProduct ((SD k).u i) ((Dt k) *ᵥ (SD k).v j) * ∫ ω, dotProduct ((SD k).u i) (Q ϱ (WeightedBuf (emaW R.β) (R.F k) (S k) t ω) *ᵥ (SD k).v j) ∂(P k) =
        kernel (emaW R.β) (specOutFM (R.F k)) (specInFM (R.F k)) ϱ ((SD k).μ i) ((SD k).lam j) / Real.sqrt (riskSigma (R.F k).C (Dt k)) * modeQ (SD k) (Dt k) i j +
          dotProduct ((SD k).u i) ((Dt k) *ᵥ (SD k).v j) * Erho (emaW R.β) (R.F k) (SD k) (S k) t (specOutFM (R.F k)) (specInFM (R.F k)) ϱ i j) ∧
    (∀ k, ∀ ϱ ∈ Icc R.ϱlo R.ϱhi, ∀ (φ : ℝ → ℝ → ℝ) (C : ℝ),
      (∀ x y : ℝ, 0 ≤ x → 0 ≤ y → |φ x y| ≤ C) →
      |∑ i : Fin (R.m k), ∑ j : Fin (R.n k), φ ((SD k).μ i) ((SD k).lam j) *
          dotProduct ((SD k).u i) ((Dt k) *ᵥ (SD k).v j) * Erho (emaW R.β) (R.F k) (SD k) (S k) t (specOutFM (R.F k)) (specInFM (R.F k)) ϱ i j| ≤
        C * fro (Dt k) * epsB (emaW R.β) (R.F k) (S k) t (specOutFM (R.F k)) (specInFM (R.F k)) R.ϱlo R.ϱhi) :=
  cor_app_drift_kernel_i_weights R P S t (emaW R.β) (emaW_weightClass_regime R) SD Dt hDt hRt
end Muon.Drift
