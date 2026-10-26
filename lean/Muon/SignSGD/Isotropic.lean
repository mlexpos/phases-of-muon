import Muon.Setup.Model
import Muon.SignSGD.Defs
import Muon.SignSGD.OneStep
import Muon.SignSGD.BatchConstant
import Muon.SignSGD.CoordinateMoments
import Muon.SignSGD.SignComparison
import Muon.SignSGD.ShiftArcsine

/-!
# Appendix I (SignSGD): isotropic volatility, coordinate drift, isotropic drift and recursion

Interface for work package L-I.7 (card `sections/08-signsgd/CARD.md` §3 rows 6, 10, 12, 13).
Source of record: snapshot `cr-2026-10-23`, `sections/08-signsgd/section.tex`, labels
`prop:app-sgd-iso-volatility` (l. 216–227), `prop:app-sgd-coordinate` (l. 473–482),
`thm:app-sgd-iso-drift` (l. 516–530), `prop:app-sgd-iso` = `prop:signsgd-recursion-B` (l. 566–577).

None of these labels involves the Haar measure on `O(n)`, so no `IsOrthHaar` hypothesis is
stated here (coordinator ruling Q1 applies to the half-anisotropic rows only).

Standing hypotheses of §I.3 (`Σin = Σout = Id`, `Δ` deterministic and nonzero, fixed entry `(i,j)`):
the isotropic-data statements (`prop_app_sgd_coordinate`, `thm_app_sgd_iso_drift`) take the batch law
`gaussBatch` of `CoordinateMoments`, which encodes `Σ = Id` by construction. The volatility and
recursion statements take a general `Covariances` value `C` with `C.Sout = 1`, `C.Sin = 1` and a batch
law `IIDBatch P ν` with `ν = dataTarget C` (`assum:data-target`), which is `gaussBatch` under `Σ = Id`.

Quantifier order. Universal constants `C₂` (from `lem:app-sgd-comparison`) are existentially quantified
before all dimensions, states and parameters. `C_r` depends on `(K, f₋, C_Δ)` only: it is chosen after
those three and before the state and `f₊`.

Declarations of record: `prop_app_sgd_iso_volatility_i`, `prop_app_sgd_iso_volatility_ii`,
`prop_app_sgd_coordinate`, `thm_app_sgd_iso_drift`, `prop_app_sgd_iso_frozen` (frozen-state helper),
and `prop_app_sgd_iso_filtered` (the label `prop:app-sgd-iso`, conditional on the past).

Batch bridge: `Muon.Setup.Batch` (`Fin B → Vec × Vec`, `(out, in)` order) is converted to
`SignSGD.Batch` (fields `xin`, `xout`) by `toSignBatch`.
-/

open MeasureTheory ProbabilityTheory
open scoped Matrix MatrixOrder

namespace Muon.SignSGD

/-- The isotropic step-size threshold `k₀ = max{4, 8 K C_Δ² / f₋²}` of `thm:app-sgd-iso-drift`
(`k ≥ k₀`), as a function of the parameters `P` of `def:app-sgd-iso-regime`. -/
noncomputable def isoK0 (P : IsoParams) : ℝ :=
  max 4 (8 * P.K * P.Cdelta ^ 2 / P.fMin ^ 2)

/-- Bridge from the `Setup` batch `Fin B → Vec m × Vec n` (pairs `(out, in)`) to the
`SignSGD.Batch` structure (fields `xin`, `xout`). -/
def toSignBatch {Nout Nin B : ℕ} (x : Muon.Setup.Batch Nout Nin B) : Batch Nout Nin B :=
  ⟨fun a => (x a).2, fun a => (x a).1⟩

/-- The expected sign `𝔼 sign(G°_{ij})` of one entry of the physical gradient over a batch of `B`
i.i.d. standard Gaussian samples `(z_a, w_a)`, with `G°_{ij} = (1/B) ∑_a X_a` and
`X_a = sgdCoord Δ i j (p a)` (`eqn:app-sgd-coordinate`, `CoordinateMoments`). This is the
expectation the isotropic statements integrate; it is not a new physical object. -/
noncomputable def expSignEntry (Nout Nin B : ℕ) (Δ : Matrix (Fin Nout) (Fin Nin) ℝ)
    (i : Fin Nout) (j : Fin Nin) : ℝ :=
  ∫ p : Fin B → (Fin Nout → ℝ) × (Fin Nin → ℝ),
    Real.sign ((1 / (B : ℝ)) * ∑ a, sgdCoord Δ i j (p a))
      ∂(Measure.pi fun _ : Fin B => gaussBatch Nout Nin)

/-- Under `Σout = Σin = 1` the Σ-pairing is the entrywise (Frobenius) inner product. -/
private lemma iso_pairSigma_eq_sum {Nout Nin : ℕ} (C : Covariances Nout Nin)
    (hSout : C.Sout = 1) (hSin : C.Sin = 1) (V W : Matrix (Fin Nout) (Fin Nin) ℝ) :
    Muon.Setup.pairSigma C V W = ∑ i, ∑ j, V i j * W i j := by
  unfold Muon.Setup.pairSigma
  rw [hSout, hSin, Matrix.one_mul, Matrix.mul_one]
  simp [Matrix.trace, Matrix.mul_apply]

/-- The squared Frobenius norm as an entrywise sum of squares. -/
private lemma iso_frobNorm_sq {Nout Nin : ℕ} (A : Matrix (Fin Nout) (Fin Nin) ℝ) :
    frobNorm A ^ 2 = ∑ i, ∑ j, A i j * A i j := by
  unfold frobNorm
  have h : 0 ≤ ∑ i, ∑ j, A i j ^ 2 :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _
  rw [Real.sq_sqrt h]
  simp only [sq]

/-- The sign direction of the zero state vanishes identically (`sign 0 = 0`). -/
private lemma iso_signGrad_zero {Nout Nin B : ℕ} (β : Batch Nout Nin B) :
    signGrad (0 : Matrix (Fin Nout) (Fin Nin) ℝ) β = 0 := by
  ext i j
  simp [signGrad, physGrad, residual]

/-- A nonzero row vector is nonzero at some point with prescribed coordinate `j` nonvanishing. -/
private lemma iso_row_witness {Nin : ℕ} (r : Fin Nin → ℝ) (hr : r ≠ 0) (j : Fin Nin) :
    ∃ x : Fin Nin → ℝ, x j ≠ 0 ∧ dotProduct r x ≠ 0 := by
  by_cases hrj : r j = 0
  · obtain ⟨l, hl⟩ : ∃ l, r l ≠ 0 := by
      by_contra h
      push_neg at h
      exact hr (funext h)
    have hlj : l ≠ j := fun h => hl (h ▸ hrj)
    refine ⟨Pi.single j 1 + Pi.single l 1, ?_, ?_⟩
    · simp [Pi.single_apply, Ne.symm hlj]
    · rw [dotProduct_add, dotProduct_single, dotProduct_single]
      simp [hrj, hl]
  · refine ⟨Pi.single j 1, by simp, ?_⟩
    rw [dotProduct_single]
    simp [hrj]

/-- Pointwise witness for the a.s. nonvanishing of one physical-gradient entry: for `Δ ≠ 0`
there is a sample `(y, x)` at which `y_i x_j (yᵀ Δ x) ≠ 0`. -/
private lemma iso_exists_point {Nout Nin : ℕ} (Δ : Matrix (Fin Nout) (Fin Nin) ℝ) (hΔ : Δ ≠ 0)
    (i : Fin Nout) (j : Fin Nin) :
    ∃ y : Fin Nout → ℝ, ∃ x : Fin Nin → ℝ,
      y i * x j * dotProduct y (Δ.mulVec x) ≠ 0 := by
  obtain ⟨k, l, hkl⟩ : ∃ k l, Δ k l ≠ 0 := by
    by_contra h
    push_neg at h
    exact hΔ (Matrix.ext fun k l => h k l)
  by_cases hi : ∀ l, Δ i l = 0
  · have hk : (fun l => Δ k l) ≠ 0 := fun h => hkl (congrFun h l)
    have hki : k ≠ i := fun h => by
      subst h
      exact hk (funext hi)
    obtain ⟨x, hxj, hx⟩ := iso_row_witness (fun l => Δ k l) hk j
    refine ⟨Pi.single i 1 + Pi.single k 1, x, ?_⟩
    have hyi : (Pi.single i 1 + Pi.single k 1 : Fin Nout → ℝ) i = 1 := by
      simp [Pi.single_apply, Ne.symm hki]
    have hdot : dotProduct (Pi.single i 1 + Pi.single k 1 : Fin Nout → ℝ) (Δ.mulVec x)
        = dotProduct (fun l => Δ k l) x := by
      rw [add_dotProduct, single_dotProduct, single_dotProduct]
      simp [Matrix.mulVec, dotProduct, hi]
    rw [hyi, hdot]
    exact mul_ne_zero (mul_ne_zero one_ne_zero hxj) hx
  · push_neg at hi
    obtain ⟨l0, hl0⟩ := hi
    have hr : (fun l => Δ i l) ≠ 0 := fun h => hl0 (congrFun h l0)
    obtain ⟨x, hxj, hx⟩ := iso_row_witness (fun l => Δ i l) hr j
    refine ⟨Pi.single i 1, x, ?_⟩
    have hdot : dotProduct (Pi.single i 1 : Fin Nout → ℝ) (Δ.mulVec x)
        = dotProduct (fun l => Δ i l) x := by
      rw [single_dotProduct]
      simp [Matrix.mulVec, dotProduct]
    rw [hdot, Pi.single_eq_same]
    exact mul_ne_zero (mul_ne_zero one_ne_zero hxj) hx

private noncomputable def isoGlue (Nout Nin : ℕ) :
    ((Fin Nout → ℝ) × (Fin Nin → ℝ)) ≃ᵐ (Fin (Nout + Nin) → ℝ) :=
  (MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin Nout ⊕ Fin Nin => ℝ)).symm.trans
    (MeasurableEquiv.piCongrLeft (fun _ : Fin (Nout + Nin) => ℝ) finSumFinEquiv)

private lemma isoGlue_left {Nout Nin : ℕ} (p : (Fin Nout → ℝ) × (Fin Nin → ℝ)) (k : Fin Nout) :
    isoGlue Nout Nin p (finSumFinEquiv (Sum.inl k)) = p.1 k := by
  show (Equiv.piCongrLeft (fun _ : Fin (Nout + Nin) => ℝ) finSumFinEquiv)
    ((MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin Nout ⊕ Fin Nin => ℝ)).symm p)
    (finSumFinEquiv (Sum.inl k)) = p.1 k
  rw [Equiv.piCongrLeft_apply_apply]
  rfl

private lemma isoGlue_right {Nout Nin : ℕ} (p : (Fin Nout → ℝ) × (Fin Nin → ℝ)) (l : Fin Nin) :
    isoGlue Nout Nin p (finSumFinEquiv (Sum.inr l)) = p.2 l := by
  show (Equiv.piCongrLeft (fun _ : Fin (Nout + Nin) => ℝ) finSumFinEquiv)
    ((MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin Nout ⊕ Fin Nin => ℝ)).symm p)
    (finSumFinEquiv (Sum.inr l)) = p.2 l
  rw [Equiv.piCongrLeft_apply_apply]
  rfl

private lemma isoGlue_mp (Nout Nin : ℕ) :
    MeasurePreserving (isoGlue Nout Nin) (gaussBatch Nout Nin)
      (Muon.Foundations.stdGaussianPi (Nout + Nin)) := by
  have h1 := measurePreserving_sumPiEquivProdPi_symm
    (fun _ : Fin Nout ⊕ Fin Nin => gaussianReal 0 1)
  have h2 := measurePreserving_piCongrLeft (α := fun _ : Fin (Nout + Nin) => ℝ)
    (fun _ => gaussianReal 0 1) finSumFinEquiv
  exact h1.trans h2

private noncomputable def isoPoly {Nout Nin : ℕ} (Δ : Matrix (Fin Nout) (Fin Nin) ℝ)
    (i : Fin Nout) (j : Fin Nin) (c : ℝ) : MvPolynomial (Fin (Nout + Nin)) ℝ :=
  (∑ k, ∑ l, MvPolynomial.C (Δ k l) * MvPolynomial.X (finSumFinEquiv (Sum.inl k))
      * MvPolynomial.X (finSumFinEquiv (Sum.inr l)))
    * MvPolynomial.X (finSumFinEquiv (Sum.inl i)) * MvPolynomial.X (finSumFinEquiv (Sum.inr j))
    - MvPolynomial.C c

private lemma isoPoly_eval {Nout Nin : ℕ} (Δ : Matrix (Fin Nout) (Fin Nin) ℝ)
    (i : Fin Nout) (j : Fin Nin) (c : ℝ) (p : (Fin Nout → ℝ) × (Fin Nin → ℝ)) :
    MvPolynomial.eval (isoGlue Nout Nin p) (isoPoly Δ i j c) = sgdCoord Δ i j p - c := by
  simp only [isoPoly, sgdCoord, map_sub, map_mul, map_sum, MvPolynomial.eval_C,
    MvPolynomial.eval_X, isoGlue_left, isoGlue_right, dotProduct, Matrix.mulVec]
  congr 1
  congr 2
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  ring

private lemma isoPoly_ne_zero {Nout Nin : ℕ} (Δ : Matrix (Fin Nout) (Fin Nin) ℝ) (hΔ : Δ ≠ 0)
    (i : Fin Nout) (j : Fin Nin) (c : ℝ) : isoPoly Δ i j c ≠ 0 := by
  intro h
  have h0 := isoPoly_eval Δ i j c (0, 0)
  rw [h] at h0
  simp [sgdCoord] at h0
  subst h0
  obtain ⟨y, x, hyx⟩ := iso_exists_point Δ hΔ i j
  have h1 := isoPoly_eval Δ i j 0 (y, x)
  rw [h] at h1
  apply hyx
  simpa [sgdCoord, mul_comm, mul_left_comm, mul_assoc] using h1.symm

private lemma iso_gauss_atomless {Nout Nin : ℕ} (Δ : Matrix (Fin Nout) (Fin Nin) ℝ) (hΔ : Δ ≠ 0)
    (i : Fin Nout) (j : Fin Nin) (c : ℝ) :
    gaussBatch Nout Nin {p | sgdCoord Δ i j p = c} = 0 := by
  have hnull := (Muon.Foundations.poly_zero_set_null (Nout + Nin) (isoPoly Δ i j c)
    (isoPoly_ne_zero Δ hΔ i j c)).2.2
  have hsub : {p : (Fin Nout → ℝ) × (Fin Nin → ℝ) | sgdCoord Δ i j p = c}
      = isoGlue Nout Nin ⁻¹' {x | MvPolynomial.eval x (isoPoly Δ i j c) = 0} := by
    ext p
    simp only [Set.mem_setOf_eq, Set.mem_preimage, isoPoly_eval, sub_eq_zero]
  have hms : MeasurableSet {x : Fin (Nout + Nin) → ℝ | MvPolynomial.eval x (isoPoly Δ i j c) = 0} :=
    (isClosed_eq (MvPolynomial.continuous_eval _) continuous_const).measurableSet
  rw [hsub, (isoGlue_mp Nout Nin).measure_preimage hms.nullMeasurableSet]
  exact hnull

private lemma iso_pi_sum_null {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [IsProbabilityMeasure μ] (f : α → ℝ) (hf : Measurable f) (hat : ∀ c, μ {x | f x = c} = 0)
    {B : ℕ} (hB : 1 ≤ B) :
    Measure.pi (fun _ : Fin B => μ) {v | ∑ a, f (v a) = 0} = 0 := by
  set a0 : Fin B := ⟨0, hB⟩
  set W : Fin B → (Fin B → α) → ℝ := fun a v => f (v a) with hW
  have hind : iIndepFun W (Measure.pi (fun _ : Fin B => μ)) :=
    iIndepFun_pi (μ := fun _ : Fin B => μ) (X := fun _ => f) (fun _ => hf.aemeasurable)
  have hWm : ∀ a, Measurable (W a) := fun a => hf.comp (measurable_pi_apply a)
  have hnot : a0 ∉ (Finset.univ.erase a0) := by simp
  have hi := hind.indepFun_finsetSum_of_notMem₀ (fun a => (hWm a).aemeasurable) hnot
  set Pm := Measure.pi (fun _ : Fin B => μ)
  have hXm : Measurable (∑ j ∈ Finset.univ.erase a0, W j) := by
    have := Finset.measurable_sum (Finset.univ.erase a0) (fun a _ => hWm a)
    convert this using 1
    ext v; simp [Finset.sum_apply]
  have hmap := (indepFun_iff_map_prod_eq_prod_map_map hXm.aemeasurable (hWm a0).aemeasurable).1 hi
  have hT : MeasurableSet {q : ℝ × ℝ | q.1 + q.2 = 0} :=
    (isClosed_eq (continuous_fst.add continuous_snd) continuous_const).measurableSet
  have hset : {v : Fin B → α | ∑ a, f (v a) = 0}
      = (fun v => ((∑ j ∈ Finset.univ.erase a0, W j) v, W a0 v)) ⁻¹' {q : ℝ × ℝ | q.1 + q.2 = 0} := by
    ext v
    simp only [Set.mem_setOf_eq, Set.mem_preimage, Finset.sum_apply, hW]
    rw [Finset.sum_erase_add _ _ (Finset.mem_univ a0)]
  rw [hset, ← Measure.map_apply (hXm.prodMk (hWm a0)) hT, hmap, Measure.prod_apply hT]
  have hz : ∀ x : ℝ, (Pm.map (W a0)) (Prod.mk x ⁻¹' {q : ℝ × ℝ | q.1 + q.2 = 0}) = 0 := by
    intro x
    have hset2 : Prod.mk x ⁻¹' {q : ℝ × ℝ | q.1 + q.2 = 0} = {-x} := by
      ext y; simp only [Set.mem_preimage, Set.mem_setOf_eq, Set.mem_singleton_iff]; constructor <;> intro h <;> linarith
    rw [hset2, Measure.map_apply (hWm a0) (measurableSet_singleton _)]
    have : W a0 ⁻¹' {-x} = (fun v : Fin B → α => v a0) ⁻¹' {p | f p = -x} := by
      ext v; simp [hW]
    rw [this, ← Measure.map_apply (measurable_pi_apply a0) (hf (measurableSet_singleton _)),
      (measurePreserving_eval (fun _ : Fin B => μ) a0).map_eq]
    exact hat _
  rw [lintegral_congr hz]; simp

private lemma iso_nu_eq {Nout Nin : ℕ} (C : Covariances Nout Nin)
    (hSout : C.Sout = 1) (hSin : C.Sin = 1)
    (ν : Measure (Vec Nout × Vec Nin)) (hν : Muon.Setup.assum_data_target C ν) :
    ν = gaussBatch Nout Nin := by
  have hphys : Muon.Setup.phys C = id := by
    funext zw
    simp [Muon.Setup.phys, Muon.Setup.rOut, Muon.Setup.rIn, hSout, hSin, CFC.sqrt_one]
  rw [hν]
  unfold Muon.Setup.dataTarget gaussBatch
  rw [hphys, Measure.map_id]

private lemma iso_gauss_prob (Nout Nin : ℕ) : IsProbabilityMeasure (gaussBatch Nout Nin) := by
  unfold gaussBatch; infer_instance

private lemma iso_physGrad_ne_zero_ae {Nout Nin B : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (hB : 1 ≤ B)
    (ν : Measure (Vec Nout × Vec Nin)) (hν : ν = gaussBatch Nout Nin)
    (β : Ω → Batch Nout Nin B)
    (hβ : Muon.Setup.IIDBatch P ν (fun a ω => ((β ω).xout a, (β ω).xin a)))
    (Δ : Matrix (Fin Nout) (Fin Nin) ℝ) (hΔ : Δ ≠ 0) (i : Fin Nout) (j : Fin Nin) :
    ∀ᵐ ω ∂P, physGrad Δ (β ω) i j ≠ 0 := by
  subst hν
  have := iso_gauss_prob Nout Nin
  set Y : Fin B → Ω → Vec Nout × Vec Nin := fun a ω => ((β ω).xout a, (β ω).xin a) with hY
  have hVm : AEMeasurable (fun ω (a : Fin B) => Y a ω) P := aemeasurable_pi_iff.2 hβ.meas
  have hlaw : P.map (fun ω (a : Fin B) => Y a ω)
      = Measure.pi (fun _ : Fin B => gaussBatch Nout Nin) := by
    rw [(iIndepFun_iff_map_fun_eq_pi_map hβ.meas).1 hβ.indep]
    simp only [hβ.law]
  have hf : Measurable (sgdCoord Δ i j) := by
    unfold sgdCoord; fun_prop
  have hnull := iso_pi_sum_null (gaussBatch Nout Nin) (sgdCoord Δ i j) hf
    (iso_gauss_atomless Δ hΔ i j) hB
  have hN : MeasurableSet {v : Fin B → Vec Nout × Vec Nin | ∑ a, sgdCoord Δ i j (v a) = 0} :=
    (isClosed_eq (by unfold sgdCoord; fun_prop) continuous_const).measurableSet
  have h0 : P {ω | ∑ a, sgdCoord Δ i j (Y a ω) = 0} = 0 := by
    have := Measure.map_apply_of_aemeasurable hVm hN
    rw [hlaw] at this
    rw [← hnull, this]
    rfl
  have hB0 : (B : ℝ) ≠ 0 := by
    have : 0 < B := hB
    positivity
  rw [ae_iff]
  refine measure_mono_null (fun ω hω => ?_) h0
  simp only [Set.mem_setOf_eq, not_not] at hω ⊢
  have : physGrad Δ (β ω) i j = (1 / (B : ℝ)) * ∑ a, sgdCoord Δ i j (Y a ω) := by
    unfold physGrad residual sgdCoord
    congr 1
    refine Finset.sum_congr rfl fun a _ => ?_
    simp [hY, mul_assoc]
  rw [this] at hω
  rcases mul_eq_zero.1 hω with h | h
  · exact absurd h (by positivity)
  · exact h

private lemma iso_sign_sq_sum_ae {Nout Nin B : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (hB : 1 ≤ B)
    (ν : Measure (Vec Nout × Vec Nin)) (hν : ν = gaussBatch Nout Nin)
    (β : Ω → Batch Nout Nin B)
    (hβ : Muon.Setup.IIDBatch P ν (fun a ω => ((β ω).xout a, (β ω).xin a)))
    (Δ : Matrix (Fin Nout) (Fin Nin) ℝ) (hΔ : Δ ≠ 0) :
    ∀ᵐ ω ∂P, ∑ i, ∑ j, signGrad Δ (β ω) i j * signGrad Δ (β ω) i j
      = (Nin : ℝ) * (Nout : ℝ) := by
  have hall : ∀ᵐ ω ∂P, ∀ i j, physGrad Δ (β ω) i j ≠ 0 := by
    rw [ae_all_iff]; intro i
    rw [ae_all_iff]; intro j
    exact iso_physGrad_ne_zero_ae P hB ν hν β hβ Δ hΔ i j
  filter_upwards [hall] with ω hω
  have h1 : ∀ i j, signGrad Δ (β ω) i j * signGrad Δ (β ω) i j = 1 := by
    intro i j
    have hne := hω i j
    show Real.sign (physGrad Δ (β ω) i j) * Real.sign (physGrad Δ (β ω) i j) = 1
    rcases lt_or_gt_of_ne hne with h | h
    · rw [Real.sign_of_neg h]; norm_num
    · rw [Real.sign_of_pos h]; norm_num
  simp only [h1]
  simp [mul_comm]

/-- **prop:app-sgd-iso-volatility**, first part: the isotropic volatility equals the Frobenius
volatility, and its value is `Nin Nout` for a nonzero state and `0` for the zero state.

`prop_app_sgd_iso_volatility_i` cr-2026-10-23. LaTeX statement (verbatim):
\begin{proposition}[Isotropic volatility]\label{prop:app-sgd-iso-volatility}
Let $\Sigmain=\Idin$ and $\Sigmaout=\Idout$ in \cref{assum:data-target}, let
$\Delta\in\R^{\Nout\times\Nin}$ be deterministic, and let $S=\sign(G^\circ)$
for a batch of size $B\ge1$. Then
\begin{equation}\label{eqn:signsgd-vol-exact}
\EE\norm S_\Sigma^2=\EE\norm S_\F^2=\begin{cases}\Nin\Nout,&\Delta\ne0,\\ 0,&\Delta=0.\end{cases}
\end{equation}
In particular the step \cref{eqn:app-sgd-update} satisfies
\begin{equation}\label{eqn:app-sgd-iso-risk}
\EE\,\cR(\Delta^+)=\cR(\Delta)-\lr\,\langle\Delta,\EE S\rangle_\F+\frac{\lr^2}2\,\Nin\Nout\,\mathbf 1_{\{\Delta\ne0\}} .
\end{equation}
\end{proposition}
Part (i) is `eqn:signsgd-vol-exact`. -/
theorem prop_app_sgd_iso_volatility_i {Nout Nin B : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (hB : 1 ≤ B)
    (C : Covariances Nout Nin) (hSout : C.Sout = 1) (hSin : C.Sin = 1)
    (ν : Measure (Vec Nout × Vec Nin)) (hν : Muon.Setup.assum_data_target C ν)
    (β : Ω → Batch Nout Nin B)
    (hβ : Muon.Setup.IIDBatch P ν (fun a ω => ((β ω).xout a, (β ω).xin a)))
    (Δ : Matrix (Fin Nout) (Fin Nin) ℝ) :
    ∫ ω, Muon.Setup.pairSigma C (signGrad Δ (β ω)) (signGrad Δ (β ω)) ∂P
        = ∫ ω, frobNorm (signGrad Δ (β ω)) ^ 2 ∂P ∧
      (Δ = 0 → ∫ ω, Muon.Setup.pairSigma C (signGrad Δ (β ω)) (signGrad Δ (β ω)) ∂P = 0) ∧
      (Δ ≠ 0 → ∫ ω, Muon.Setup.pairSigma C (signGrad Δ (β ω)) (signGrad Δ (β ω)) ∂P
        = (Nin : ℝ) * (Nout : ℝ)) := by
  have hν' := iso_nu_eq C hSout hSin ν hν
  have hpt : ∀ ω, Muon.Setup.pairSigma C (signGrad Δ (β ω)) (signGrad Δ (β ω))
      = frobNorm (signGrad Δ (β ω)) ^ 2 := by
    intro ω
    rw [iso_pairSigma_eq_sum C hSout hSin, iso_frobNorm_sq]
  refine ⟨integral_congr_ae (Filter.Eventually.of_forall hpt), ?_, ?_⟩
  · rintro rfl
    simp [iso_signGrad_zero, iso_pairSigma_eq_sum C hSout hSin]
  · intro hΔ
    have hae := iso_sign_sq_sum_ae P hB ν hν' β hβ Δ hΔ
    have hae2 : ∀ᵐ ω ∂P, Muon.Setup.pairSigma C (signGrad Δ (β ω)) (signGrad Δ (β ω))
        = (Nin : ℝ) * (Nout : ℝ) :=
      hae.mono fun ω hω => by rw [iso_pairSigma_eq_sum C hSout hSin]; exact hω
    rw [integral_congr_ae hae2]
    simp

/-- **prop:app-sgd-iso-volatility**, second part: the one-step risk identity
`eqn:app-sgd-iso-risk` at a deterministic state, with the indicator `𝟙{Δ ≠ 0}`.

`prop_app_sgd_iso_volatility_ii` cr-2026-10-23. LaTeX statement (verbatim):
\begin{proposition}[Isotropic volatility]\label{prop:app-sgd-iso-volatility}
Let $\Sigmain=\Idin$ and $\Sigmaout=\Idout$ in \cref{assum:data-target}, let
$\Delta\in\R^{\Nout\times\Nin}$ be deterministic, and let $S=\sign(G^\circ)$
for a batch of size $B\ge1$. Then
\begin{equation}\label{eqn:signsgd-vol-exact}
\EE\norm S_\Sigma^2=\EE\norm S_\F^2=\begin{cases}\Nin\Nout,&\Delta\ne0,\\ 0,&\Delta=0.\end{cases}
\end{equation}
In particular the step \cref{eqn:app-sgd-update} satisfies
\begin{equation}\label{eqn:app-sgd-iso-risk}
\EE\,\cR(\Delta^+)=\cR(\Delta)-\lr\,\langle\Delta,\EE S\rangle_\F+\frac{\lr^2}2\,\Nin\Nout\,\mathbf 1_{\{\Delta\ne0\}} .
\end{equation}
\end{proposition}
Part (ii) is `eqn:app-sgd-iso-risk`. -/
theorem prop_app_sgd_iso_volatility_ii {Nout Nin B : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (hB : 1 ≤ B)
    (C : Covariances Nout Nin) (hSout : C.Sout = 1) (hSin : C.Sin = 1)
    (ν : Measure (Vec Nout × Vec Nin)) (hν : Muon.Setup.assum_data_target C ν)
    (β : Ω → Batch Nout Nin B)
    (hβ : Muon.Setup.IIDBatch P ν (fun a ω => ((β ω).xout a, (β ω).xin a)))
    (Δ : Matrix (Fin Nout) (Fin Nin) ℝ) (η : ℝ) (hη : 0 ≤ η) :
    ∫ ω, Muon.Setup.riskSigma C (def_app_sgd_update η Δ (β ω)) ∂P
      = Muon.Setup.riskSigma C Δ
        - η * ∑ i, ∑ j, Δ i j * batchMean P (fun ω => signGrad Δ (β ω)) i j
        + η ^ 2 / 2 * (if Δ = 0 then 0 else (Nin : ℝ) * (Nout : ℝ)) := by
  obtain ⟨_, h0, h1⟩ := prop_app_sgd_iso_volatility_i P hB C hSout hSin ν hν β hβ Δ
  set Y : Fin B → Ω → Vec Nout × Vec Nin := fun a ω => ((β ω).xout a, (β ω).xin a) with hY
  set Y' : Fin B → Ω → Vec Nout × Vec Nin := fun a => (hβ.meas a).mk (Y a) with hY'
  set β' : Ω → Batch Nout Nin B := fun ω => ⟨fun a => (Y' a ω).2, fun a => (Y' a ω).1⟩ with hβ'
  have hYm : ∀ a, Measurable (Y' a) := fun a => (hβ.meas a).measurable_mk
  have hx : ∀ a k, Measurable fun ω => (β' ω).xin a k := fun a k =>
    (measurable_pi_apply k).comp (measurable_snd.comp (hYm a))
  have hy : ∀ a k, Measurable fun ω => (β' ω).xout a k := fun a k =>
    (measurable_pi_apply k).comp (measurable_fst.comp (hYm a))
  have hae : ∀ᵐ ω ∂P, β' ω = β ω := by
    have h : ∀ᵐ ω ∂P, ∀ a, Y a ω = Y' a ω :=
      ae_all_iff.2 fun a => (hβ.meas a).ae_eq_mk
    filter_upwards [h] with ω hω
    have e : β ω = ⟨(β ω).xin, (β ω).xout⟩ := rfl
    rw [e]
    simp only [hβ']
    congr 1
    · funext a; exact (congrArg Prod.snd (hω a)).symm
    · funext a; exact (congrArg Prod.fst (hω a)).symm
  have hrisk := eqn_app_sgd_risk P C Δ η hη β' hx hy
  have hL : ∫ ω, Muon.Setup.riskSigma C (def_app_sgd_update η Δ (β ω)) ∂P
      = ∫ ω, Muon.Setup.riskSigma C (def_app_sgd_update η Δ (β' ω)) ∂P :=
    integral_congr_ae (hae.mono fun ω hω => by simp only [hω])
  have hS : ∀ i j, ∫ ω, signGrad Δ (β' ω) i j ∂P = ∫ ω, signGrad Δ (β ω) i j ∂P :=
    fun i j => integral_congr_ae (hae.mono fun ω hω => by simp only [hω])
  have hQ : ∫ ω, Muon.Setup.pairSigma C (signGrad Δ (β' ω)) (signGrad Δ (β' ω)) ∂P
      = ∫ ω, Muon.Setup.pairSigma C (signGrad Δ (β ω)) (signGrad Δ (β ω)) ∂P :=
    integral_congr_ae (hae.mono fun ω hω => by simp only [hω])
  rw [hL, hrisk, hQ, iso_pairSigma_eq_sum C hSout hSin]
  have hbm : batchMean P (fun ω => signGrad Δ (β' ω)) = batchMean P (fun ω => signGrad Δ (β ω)) := by
    ext i j
    exact hS i j
  rw [hbm]
  by_cases hΔ : Δ = 0
  · rw [if_pos hΔ, h0 hΔ]
  · rw [if_neg hΔ, h1 hΔ]

/-! ### Helpers for `prop_app_sgd_coordinate` (P-I.7.P2) -/

private lemma cp_mono_int {n k : ℕ} (c : Fin k → Fin n) :
    Integrable (fun z : Fin n → ℝ => ∏ r : Fin k, z (c r))
      (Muon.Foundations.stdGaussianPi n) := by
  have hprod : (fun z : Fin n → ℝ => ∏ r : Fin k, z (c r))
      = fun z : Fin n → ℝ => ∏ i : Fin n,
          (fun (x : ℝ) => x ^ Fintype.card {r // c r = i}) (z i) := by
    funext z
    rw [← Fintype.prod_fiberwise c (fun r => z (c r))]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [Finset.prod_congr rfl (fun (r : {r // c r = i}) _ => by rw [r.2]), Finset.prod_const,
      Finset.card_univ]
  rw [hprod]
  unfold Muon.Foundations.stdGaussianPi
  exact Integrable.fintype_prod (fun i => Muon.Foundations.gaussian_integrable_pow _)

private lemma cp_four_sq_int (n : ℕ) (a b c d : Fin n) :
    Integrable (fun z : Fin n → ℝ => z a ^ 2 * z b ^ 2 * (z c ^ 2 * z d ^ 2))
      (Muon.Foundations.stdGaussianPi n) := by
  have h := cp_mono_int (n := n) ![a, a, b, b, c, c, d, d]
  refine Integrable.congr h (Filter.Eventually.of_forall fun z => ?_)
  simp [Fin.prod_univ_succ]
  ring

private lemma cp_sq_pow4_int (n : ℕ) :
    Integrable (fun z : Fin n → ℝ => (∑ i, z i ^ 2) ^ 4) (Muon.Foundations.stdGaussianPi n) := by
  have hS2 : ∀ z : Fin n → ℝ, (∑ i, z i ^ 2) ^ 2 = ∑ p : Fin n × Fin n, z p.1 ^ 2 * z p.2 ^ 2 := by
    intro z
    simp only [Fintype.sum_prod_type]
    rw [sq, Finset.sum_mul_sum]
  have e : (fun z : Fin n → ℝ => (∑ i, z i ^ 2) ^ 4)
      = fun z => ∑ p : Fin n × Fin n, ∑ q : Fin n × Fin n,
          z p.1 ^ 2 * z p.2 ^ 2 * (z q.1 ^ 2 * z q.2 ^ 2) := by
    funext z
    have h4 : (∑ i, z i ^ 2) ^ 4 = ((∑ i, z i ^ 2) ^ 2) ^ 2 := by ring
    rw [h4, hS2 z, sq, Finset.sum_mul_sum]
  rw [e]
  refine integrable_finsetSum _ fun p _ => integrable_finsetSum _ fun q _ => ?_
  exact cp_four_sq_int n p.1 p.2 q.1 q.2

private lemma cp_coord_pow4_int {Nout Nin : ℕ} (Δ : Matrix (Fin Nout) (Fin Nin) ℝ)
    (i : Fin Nout) (j : Fin Nin) :
    Integrable (fun p : (Fin Nout → ℝ) × (Fin Nin → ℝ) => sgdCoord Δ i j p ^ 4)
      (gaussBatch Nout Nin) := by
  have hint : Integrable (fun p : (Fin Nout → ℝ) × (Fin Nin → ℝ) =>
      (∑ k, p.1 k ^ 2) ^ 4 * (∑ l, p.2 l ^ 2) ^ 4) (gaussBatch Nout Nin) := by
    unfold gaussBatch
    exact Integrable.mul_prod (cp_sq_pow4_int Nout) (cp_sq_pow4_int Nin)
  have hcont : Continuous fun q : (Fin Nout → ℝ) × (Fin Nin → ℝ) => sgdCoord Δ i j q := by
    simp only [sgdCoord, Matrix.mulVec, dotProduct]
    fun_prop
  refine Integrable.mono' (hint.const_mul (frobNorm Δ ^ 4)) (hcont.pow 4).aestronglyMeasurable
    (Filter.Eventually.of_forall fun p => ?_)
  set S := ∑ k, p.1 k ^ 2 with hSdef
  set T := ∑ l, p.2 l ^ 2 with hTdef
  have ha : dotProduct p.1 (Matrix.mulVec Δ p.2)
      = ∑ x : Fin Nout × Fin Nin, Δ x.1 x.2 * (p.1 x.1 * p.2 x.2) := by
    simp only [dotProduct, Matrix.mulVec, Fintype.sum_prod_type, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring
  have hCS := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin Nout × Fin Nin))
    (fun x : Fin Nout × Fin Nin => Δ x.1 x.2) (fun x : Fin Nout × Fin Nin => p.1 x.1 * p.2 x.2)
  have hF2 : frobNorm Δ ^ 2 = ∑ x : Fin Nout × Fin Nin, Δ x.1 x.2 ^ 2 := by
    have h0 : 0 ≤ ∑ k, ∑ l, Δ k l ^ 2 := by positivity
    unfold frobNorm
    rw [Real.sq_sqrt h0, Fintype.sum_prod_type]
  have hST : ∑ x : Fin Nout × Fin Nin, (p.1 x.1 * p.2 x.2) ^ 2 = S * T := by
    rw [Fintype.sum_prod_type, hSdef, hTdef, Finset.sum_mul_sum]
    simp only [mul_pow]
  have hA : (dotProduct p.1 (Matrix.mulVec Δ p.2)) ^ 2 ≤ frobNorm Δ ^ 2 * (S * T) := by
    rw [ha, hF2, ← hST]
    exact hCS
  have hzi : p.1 i ^ 2 ≤ S :=
    Finset.single_le_sum (fun k _ => sq_nonneg (p.1 k)) (Finset.mem_univ i)
  have hwj : p.2 j ^ 2 ≤ T :=
    Finset.single_le_sum (fun l _ => sq_nonneg (p.2 l)) (Finset.mem_univ j)
  have h1 : (dotProduct p.1 (Matrix.mulVec Δ p.2) ^ 2) ^ 2 ≤ (frobNorm Δ ^ 2 * (S * T)) ^ 2 :=
    pow_le_pow_left₀ (sq_nonneg _) hA 2
  have h2 : (p.1 i ^ 2) ^ 2 ≤ S ^ 2 := pow_le_pow_left₀ (sq_nonneg _) hzi 2
  have h3 : (p.2 j ^ 2) ^ 2 ≤ T ^ 2 := pow_le_pow_left₀ (sq_nonneg _) hwj 2
  have hX : sgdCoord Δ i j p ^ 4
      = (dotProduct p.1 (Matrix.mulVec Δ p.2) ^ 2) ^ 2 * (p.1 i ^ 2) ^ 2 * (p.2 j ^ 2) ^ 2 := by
    unfold sgdCoord; ring
  rw [Real.norm_of_nonneg (by rw [hX]; positivity), hX]
  calc (dotProduct p.1 (Matrix.mulVec Δ p.2) ^ 2) ^ 2 * (p.1 i ^ 2) ^ 2 * (p.2 j ^ 2) ^ 2
      ≤ (frobNorm Δ ^ 2 * (S * T)) ^ 2 * S ^ 2 * T ^ 2 := by gcongr
    _ = frobNorm Δ ^ 4 * (S ^ 4 * T ^ 4) := by ring

private lemma cp_sign_meas : Measurable Real.sign := by
  unfold Real.sign
  exact Measurable.ite (measurableSet_lt measurable_id measurable_const) measurable_const
    (Measurable.ite (measurableSet_lt measurable_const measurable_id) measurable_const
      measurable_const)

private lemma cp_frob_pos {n m : ℕ} {Δ : Matrix (Fin n) (Fin m) ℝ} (hΔ : Δ ≠ 0) :
    0 < frobNorm Δ := by
  obtain ⟨a, b, hab⟩ : ∃ a b, Δ a b ≠ 0 := by
    by_contra h
    push_neg at h
    exact hΔ (Matrix.ext fun a b => by simpa using h a b)
  have hpos : 0 < ∑ a', ∑ b', Δ a' b' ^ 2 := by
    have h1 : 0 < Δ a b ^ 2 := lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hab))
    calc (0 : ℝ) < Δ a b ^ 2 := h1
      _ ≤ ∑ b', Δ a b' ^ 2 :=
          Finset.single_le_sum (f := fun b' => Δ a b' ^ 2) (fun _ _ => sq_nonneg _)
            (Finset.mem_univ b)
      _ ≤ ∑ a', ∑ b', Δ a' b' ^ 2 :=
          Finset.single_le_sum (f := fun a' => ∑ b', Δ a' b' ^ 2)
            (fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _) (Finset.mem_univ a)
  unfold frobNorm
  exact Real.sqrt_pos.2 hpos

private lemma cp_sub4_le (x d : ℝ) : (x - d) ^ 4 ≤ 8 * (x ^ 4 + d ^ 4) := by
  have h1 : (x - d) ^ 2 ≤ 2 * (x ^ 2 + d ^ 2) := by nlinarith [sq_nonneg (x + d)]
  have h2 : ((x - d) ^ 2) ^ 2 ≤ (2 * (x ^ 2 + d ^ 2)) ^ 2 := pow_le_pow_left₀ (sq_nonneg _) h1 2
  nlinarith [sq_nonneg (x ^ 2 - d ^ 2)]

private lemma cp_abs_le_quartic (x : ℝ) : |x| ≤ 1 + x ^ 4 := by
  have ht : 0 ≤ |x| := abs_nonneg x
  have hx4 : x ^ 4 = |x| ^ 4 := (Even.pow_abs ⟨2, rfl⟩ x).symm
  rw [hx4]
  nlinarith [sq_nonneg (|x| ^ 2 - 1 / 2), sq_nonneg (|x| - 1 / 2)]

private lemma cp_coord_int {Nout Nin : ℕ} (Δ : Matrix (Fin Nout) (Fin Nin) ℝ)
    (i : Fin Nout) (j : Fin Nin) :
    Integrable (fun p : (Fin Nout → ℝ) × (Fin Nin → ℝ) => sgdCoord Δ i j p)
      (gaussBatch Nout Nin) := by
  haveI : IsProbabilityMeasure (gaussBatch Nout Nin) := by
    unfold gaussBatch
    infer_instance
  have hcont : Continuous fun q : (Fin Nout → ℝ) × (Fin Nin → ℝ) => sgdCoord Δ i j q := by
    simp only [sgdCoord, Matrix.mulVec, dotProduct]
    fun_prop
  refine Integrable.mono' ((integrable_const (1 : ℝ)).add (cp_coord_pow4_int Δ i j))
    hcont.aestronglyMeasurable (Filter.Eventually.of_forall fun p => ?_)
  rw [Real.norm_eq_abs]
  exact cp_abs_le_quartic _

private lemma cp_coord_cont {Nout Nin : ℕ} (Δ : Matrix (Fin Nout) (Fin Nin) ℝ)
    (i : Fin Nout) (j : Fin Nin) : Continuous fun q : (Fin Nout → ℝ) × (Fin Nin → ℝ) => sgdCoord Δ i j q := by
  simp only [sgdCoord, Matrix.mulVec, dotProduct]
  fun_prop

private lemma cp_Y_facts {Nout Nin : ℕ} (Δ : Matrix (Fin Nout) (Fin Nin) ℝ) (hΔ : Δ ≠ 0)
    (i : Fin Nout) (j : Fin Nin) (hbar : frobNorm Δ / 2 ≤ frobNorm (sgdDeletedBlock Δ i j)) :
    IsProbabilityMeasure ((gaussBatch Nout Nin).map (sgdStdCoord Δ i j)) ∧
    ∫ y, y ∂((gaussBatch Nout Nin).map (sgdStdCoord Δ i j)) = 0 ∧
    variance (fun y : ℝ => y) ((gaussBatch Nout Nin).map (sgdStdCoord Δ i j)) = 1 ∧
    ∫⁻ y, ENNReal.ofReal (y ^ 4) ∂((gaussBatch Nout Nin).map (sgdStdCoord Δ i j))
      ≤ ENNReal.ofReal 88208 ∧
    (∀ t : ℝ, t ≠ 0 →
      ‖∫ y, Complex.exp ((t : ℂ) * Complex.I * (y : ℂ))
          ∂((gaussBatch Nout Nin).map (sgdStdCoord Δ i j))‖ ≤ sgdPsi (|t| / 8) ∧
        sgdPsi (|t| / 8) ≤ min 1 (sgdCch * |t| ^ (-(1 / 2 : ℝ)))) := by
  haveI : IsProbabilityMeasure (gaussBatch Nout Nin) := by
    unfold gaussBatch
    infer_instance
  have hvar := lem_app_sgd_moments_iii Δ hΔ i j
  have hF := cp_frob_pos hΔ
  have hs2 : sgdSd Δ i j ^ 2 = variance (sgdCoord Δ i j) (gaussBatch Nout Nin) :=
    Real.sq_sqrt (variance_nonneg _ _)
  have hs0 : 0 < sgdSd Δ i j := by
    unfold sgdSd
    exact Real.sqrt_pos.2 (lt_of_lt_of_le (pow_pos hF 2) (by nlinarith [hvar.1]))
  have hcont := cp_coord_cont Δ i j
  have hYc : Continuous (sgdStdCoord Δ i j) := by
    unfold sgdStdCoord
    exact (hcont.sub continuous_const).div_const _
  have hYm : AEMeasurable (sgdStdCoord Δ i j) (gaussBatch Nout Nin) :=
    hYc.measurable.aemeasurable
  have hXi := cp_coord_int Δ i j
  have hYi : Integrable (fun p => sgdStdCoord Δ i j p ^ 4) (gaussBatch Nout Nin) := by
    refine Integrable.mono' (((cp_coord_pow4_int Δ i j).add (integrable_const (Δ i j ^ 4))).const_mul
      (8 / sgdSd Δ i j ^ 4)) (hYc.pow 4).aestronglyMeasurable
      (Filter.Eventually.of_forall fun p => ?_)
    show ‖sgdStdCoord Δ i j p ^ 4‖ ≤ 8 / sgdSd Δ i j ^ 4 * (sgdCoord Δ i j p ^ 4 + Δ i j ^ 4)
    rw [Real.norm_of_nonneg (by positivity)]
    unfold sgdStdCoord
    calc ((sgdCoord Δ i j p - Δ i j) / sgdSd Δ i j) ^ 4
        = (sgdCoord Δ i j p - Δ i j) ^ 4 / sgdSd Δ i j ^ 4 := div_pow _ _ _
      _ ≤ 8 * (sgdCoord Δ i j p ^ 4 + Δ i j ^ 4) / sgdSd Δ i j ^ 4 :=
          div_le_div_of_nonneg_right (cp_sub4_le _ _) (by positivity)
      _ = 8 / sgdSd Δ i j ^ 4 * (sgdCoord Δ i j p ^ 4 + Δ i j ^ 4) := by ring
  refine ⟨(Measure.isProbabilityMeasure_map_iff hYm).2 inferInstance, ?_, ?_, ?_, ?_⟩
  · rw [integral_map hYm measurable_id'.aestronglyMeasurable]
    simp only [sgdStdCoord]
    rw [integral_div, integral_sub hXi (integrable_const _), integral_const,
      lem_app_sgd_moments_i Δ hΔ i j]
    simp
  · rw [variance_map (X := fun y : ℝ => y) measurable_id'.aemeasurable hYm]
    have e : ((fun y : ℝ => y) ∘ sgdStdCoord Δ i j)
        = fun p => (1 / sgdSd Δ i j) * sgdCoord Δ i j p + (-Δ i j / sgdSd Δ i j) := by
      funext p
      simp only [Function.comp, sgdStdCoord]
      ring
    rw [e, variance_add_const (X := fun p => 1 / sgdSd Δ i j * sgdCoord Δ i j p)
      (hcont.const_mul _).aestronglyMeasurable, variance_const_mul, ← hs2]
    field_simp
  · rw [lintegral_map (by fun_prop) hYc.measurable]
    rw [← ofReal_integral_eq_lintegral_ofReal hYi (Filter.Eventually.of_forall fun p => by positivity)]
    exact ENNReal.ofReal_le_ofReal (lem_app_sgd_moments_vii Δ hΔ i j)
  · intro t ht
    have e : ∫ y, Complex.exp ((t : ℂ) * Complex.I * (y : ℂ))
        ∂((gaussBatch Nout Nin).map (sgdStdCoord Δ i j)) = sgdCharFunY Δ i j t := by
      rw [integral_map hYm (by fun_prop : Continuous fun y : ℝ =>
        Complex.exp ((t : ℂ) * Complex.I * (y : ℂ))).aestronglyMeasurable]
      rfl
    rw [e]
    exact lem_app_sgd_decay Δ hΔ i j hbar t ht

private lemma cp_sign_pos_mul (c w : ℝ) (hc : 0 < c) : Real.sign (c * w) = Real.sign w := by
  rcases lt_trichotomy w 0 with h | h | h
  · rw [Real.sign_of_neg h, Real.sign_of_neg (mul_neg_of_pos_of_neg hc h)]
  · simp [h]
  · rw [Real.sign_of_pos h, Real.sign_of_pos (mul_pos hc h)]

private lemma cp_ratio_bound (r s F N : ℝ) (hr : 0 < r) (hF : 0 < F) (hFs : F ≤ s)
    (hN1 : 0 ≤ r - N) (hN2 : r - N ≤ 4 / r) :
    |r / s - N / F| ≤ r * (s ^ 2 - F ^ 2) / (s * F * (s + F)) + 4 / (F * r) := by
  have hs : 0 < s := lt_of_lt_of_le hF hFs
  have hsF : 0 < s + F := by linarith
  have key : r / s - N / F = -(r * (s - F) / (s * F)) + (r - N) / F := by
    field_simp
    ring
  have ha : r * (s - F) / (s * F) = r * (s ^ 2 - F ^ 2) / (s * F * (s + F)) := by
    field_simp
    ring
  have ha0 : 0 ≤ r * (s - F) / (s * F) := by
    apply div_nonneg (mul_nonneg hr.le (by linarith)) (by positivity)
  have hb1 : 0 ≤ (r - N) / F := div_nonneg hN1 hF.le
  have hrN : (r - N) * r ≤ 4 := by
    have h := hN2
    rw [le_div_iff₀ hr] at h
    linarith
  have hb2 : (r - N) / F ≤ 4 / (F * r) := by
    rw [div_le_div_iff₀ hF (by positivity)]
    nlinarith
  rw [key]
  calc |-(r * (s - F) / (s * F)) + (r - N) / F|
      ≤ |-(r * (s - F) / (s * F))| + |(r - N) / F| := abs_add_le _ _
    _ = r * (s - F) / (s * F) + (r - N) / F := by
        rw [abs_neg, abs_of_nonneg ha0, abs_of_nonneg hb1]
    _ ≤ r * (s ^ 2 - F ^ 2) / (s * F * (s + F)) + 4 / (F * r) := by
        rw [← ha]; linarith

private lemma cp_cube_root_pow (B : ℕ) : (B : ℝ) ^ (3 / 2 : ℝ) = Real.sqrt (B : ℝ) ^ 3 := by
  rw [show (3 / 2 : ℝ) = (1 / 2 : ℝ) * ((3 : ℕ) : ℝ) by norm_num,
    Real.rpow_mul (by positivity), Real.rpow_natCast, ← Real.sqrt_eq_rpow]

private lemma cp_batch_pointwise {Nout Nin : ℕ} (B : ℕ) (hB : 1 ≤ B)
    (Δ : Matrix (Fin Nout) (Fin Nin) ℝ) (i : Fin Nout) (j : Fin Nin) (hs0 : 0 < sgdSd Δ i j)
    (p : Fin B → (Fin Nout → ℝ) × (Fin Nin → ℝ)) :
    Real.sign ((1 / (B : ℝ)) * ∑ a, sgdCoord Δ i j (p a))
      = Real.sign ((∑ a, sgdStdCoord Δ i j (p a)) / Real.sqrt (B : ℝ)
          + Real.sqrt (B : ℝ) * Δ i j / sgdSd Δ i j) := by
  have hBpos : (0 : ℝ) < B := by exact_mod_cast hB
  have hr : 0 < Real.sqrt (B : ℝ) := Real.sqrt_pos.2 hBpos
  have hr2 : Real.sqrt (B : ℝ) * Real.sqrt (B : ℝ) = B := Real.mul_self_sqrt hBpos.le
  have hX : ∀ a, sgdCoord Δ i j (p a) = sgdSd Δ i j * sgdStdCoord Δ i j (p a) + Δ i j := by
    intro a
    unfold sgdStdCoord
    field_simp
    ring
  have hid : (1 / (B : ℝ)) * ∑ a, sgdCoord Δ i j (p a)
      = (sgdSd Δ i j / Real.sqrt (B : ℝ)) * ((∑ a, sgdStdCoord Δ i j (p a)) / Real.sqrt (B : ℝ)
          + Real.sqrt (B : ℝ) * Δ i j / sgdSd Δ i j) := by
    simp only [hX, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, ← Finset.mul_sum]
    generalize Real.sqrt (B : ℝ) = r at hr hr2 ⊢
    rw [← hr2]
    field_simp
  rw [hid, cp_sign_pos_mul _ _ (div_pos hs0 hr)]

private lemma cp_expect_eq {Nout Nin : ℕ} (B : ℕ) (hB : 1 ≤ B)
    (Δ : Matrix (Fin Nout) (Fin Nin) ℝ) (hΔ : Δ ≠ 0) (i : Fin Nout) (j : Fin Nin)
    (hbar : frobNorm Δ / 2 ≤ frobNorm (sgdDeletedBlock Δ i j)) :
    expSignEntry Nout Nin B Δ i j
      = ∫ v : Fin B → ℝ, Real.sign ((∑ a, v a) / Real.sqrt (B : ℝ)
          + Real.sqrt (B : ℝ) * Δ i j / sgdSd Δ i j)
        ∂(Measure.pi fun _ : Fin B => (gaussBatch Nout Nin).map (sgdStdCoord Δ i j)) := by
  have hs0 : 0 < sgdSd Δ i j := by
    have hF := cp_frob_pos hΔ
    have hvar := lem_app_sgd_moments_iii Δ hΔ i j
    have hs2 : sgdSd Δ i j ^ 2 = variance (sgdCoord Δ i j) (gaussBatch Nout Nin) :=
      Real.sq_sqrt (variance_nonneg _ _)
    unfold sgdSd
    exact Real.sqrt_pos.2 (lt_of_lt_of_le (pow_pos hF 2) (by nlinarith [hvar.1]))
  have hYc : Continuous (sgdStdCoord Δ i j) := by
    have hcont := cp_coord_cont Δ i j
    unfold sgdStdCoord
    exact (hcont.sub continuous_const).div_const _
  have hYm : AEMeasurable (sgdStdCoord Δ i j) (gaussBatch Nout Nin) :=
    hYc.measurable.aemeasurable
  have hφ : Measurable (fun (x : Fin B → (Fin Nout → ℝ) × (Fin Nin → ℝ)) (a : Fin B) =>
      sgdStdCoord Δ i j (x a)) := by
    apply measurable_pi_lambda
    intro a
    exact hYc.measurable.comp (measurable_pi_apply a)
  haveI : IsProbabilityMeasure (gaussBatch Nout Nin) := by
    unfold gaussBatch
    infer_instance
  haveI : IsProbabilityMeasure ((gaussBatch Nout Nin).map (sgdStdCoord Δ i j)) :=
    (Measure.isProbabilityMeasure_map_iff hYm).2 inferInstance
  have hmap := Measure.pi_map_pi (μ := fun _ : Fin B => gaussBatch Nout Nin)
    (f := fun _ : Fin B => sgdStdCoord Δ i j) (fun _ => hYm)
  have hG : Measurable (fun v : Fin B → ℝ => Real.sign ((∑ a, v a) / Real.sqrt (B : ℝ)
      + Real.sqrt (B : ℝ) * Δ i j / sgdSd Δ i j)) :=
    cp_sign_meas.comp (by fun_prop)
  unfold expSignEntry
  rw [← hmap, integral_map hφ.aemeasurable hG.aestronglyMeasurable]
  refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
  exact cp_batch_pointwise B hB Δ i j hs0 p

private lemma cp_N_bounds (r B N : ℝ) (hr : 0 < r) (hBr : B = r * r) (h1 : 0 ≤ 1 - N / r)
    (h2 : 1 - N / r ≤ 4 / B) : 0 ≤ r - N ∧ r - N ≤ 4 / r := by
  rw [hBr] at h2
  have e : r - N = r * (1 - N / r) := by field_simp
  constructor
  · rw [e]; exact mul_nonneg hr.le h1
  · rw [e]
    calc r * (1 - N / r) ≤ r * (4 / (r * r)) := mul_le_mul_of_nonneg_left h2 hr.le
      _ = 4 / r := by field_simp

private lemma cp_Y3 {Nout Nin : ℕ} (Δ : Matrix (Fin Nout) (Fin Nin) ℝ) (hΔ : Δ ≠ 0)
    (i : Fin Nout) (j : Fin Nin) :
    ∫ y, y ^ 3 ∂((gaussBatch Nout Nin).map (sgdStdCoord Δ i j))
      = (∫ p, (sgdCoord Δ i j p - Δ i j) ^ 3 ∂(gaussBatch Nout Nin)) / sgdSd Δ i j ^ 3 := by
  have hYc : Continuous (sgdStdCoord Δ i j) := by
    have hcont := cp_coord_cont Δ i j
    unfold sgdStdCoord
    exact (hcont.sub continuous_const).div_const _
  rw [integral_map hYc.measurable.aemeasurable
    (by fun_prop : Measurable fun y : ℝ => y ^ 3).aestronglyMeasurable]
  simp only [sgdStdCoord, div_pow]
  rw [integral_div]

/-- **prop:app-sgd-coordinate** `Muon.SignSGD.prop_app_sgd_coordinate`.

cr-2026-10-23. LaTeX statement (verbatim):
\begin{proposition}[Drift of one coordinate]\label{prop:app-sgd-coordinate}
Let $B\ge4$ and suppose $\norm{\bar\Delta}_\F\ge F/2$ for the entry $(i,j)$.
With $s,m_3$ from \cref{lem:app-sgd-moments} and $C_1,C_2$ from \cref{lem:app-sgd-comparison},
\begin{equation}\label{eqn:app-sgd-coordinate-bound}
\begin{aligned}
\Big|\EE\sign(G^\circ_{ij})-\sqrt{\frac2\pi}\,\mathcal N_B\frac{\Delta_{ij}}F\Big|\le{}&\frac{C_1\abs{m_3}}{s^3\sqrt B}+\frac{C_2}B+\frac{B^{3/2}\abs{\Delta_{ij}}^3}{3\sqrt{2\pi}\,s^3}\\
&+\sqrt{\frac2\pi}\,\frac{\sqrt B\,\abs{\Delta_{ij}}\,(s^2-F^2)}{sF(s+F)}+\sqrt{\frac2\pi}\,\frac{4\abs{\Delta_{ij}}}{F\sqrt B}.
\end{aligned}
\end{equation}
\end{proposition}
Here `s = sgdSd Δ i j`, `F = frobNorm Δ`, `m₃ = 𝔼(X − Δ_ij)³` is the integral of
`(sgdCoord Δ i j − Δ i j)³` against `gaussBatch`, `C₁ = sgdC1`, and `C₂` is the universal constant
of `lem:app-sgd-comparison`. The quantifier `∃ C₂` is outside all dimensions, the batch size, the
state and the entry. -/
theorem prop_app_sgd_coordinate :
    ∃ C₂ : ℝ, ∀ (Nout Nin B : ℕ) (Δ : Matrix (Fin Nout) (Fin Nin) ℝ) (i : Fin Nout) (j : Fin Nin),
      4 ≤ B → Δ ≠ 0 → frobNorm Δ / 2 ≤ frobNorm (sgdDeletedBlock Δ i j) →
      |expSignEntry Nout Nin B Δ i j
          - Real.sqrt (2 / Real.pi) * batchConst B * Δ i j / frobNorm Δ|
        ≤ sgdC1 * |∫ p, (sgdCoord Δ i j p - Δ i j) ^ 3 ∂(gaussBatch Nout Nin)|
              / (sgdSd Δ i j ^ 3 * Real.sqrt (B : ℝ))
          + C₂ / (B : ℝ)
          + (B : ℝ) ^ (3 / 2 : ℝ) * |Δ i j| ^ 3 / (3 * Real.sqrt (2 * Real.pi) * sgdSd Δ i j ^ 3)
          + Real.sqrt (2 / Real.pi) * (Real.sqrt (B : ℝ) * |Δ i j|
              * (sgdSd Δ i j ^ 2 - frobNorm Δ ^ 2))
              / (sgdSd Δ i j * frobNorm Δ * (sgdSd Δ i j + frobNorm Δ))
          + Real.sqrt (2 / Real.pi) * (4 * |Δ i j|) / (frobNorm Δ * Real.sqrt (B : ℝ)) := by
  obtain ⟨C₂, hC⟩ := lem_app_sgd_comparison
  refine ⟨C₂, fun Nout Nin B Δ i j hB hΔ hbar => ?_⟩
  have hB1 : 1 ≤ B := by omega
  have hBpos : (0 : ℝ) < B := by exact_mod_cast (show 0 < B by omega)
  have hr : 0 < Real.sqrt (B : ℝ) := Real.sqrt_pos.2 hBpos
  have hF := cp_frob_pos hΔ
  have hvar := lem_app_sgd_moments_iii Δ hΔ i j
  have hs2 : sgdSd Δ i j ^ 2 = variance (sgdCoord Δ i j) (gaussBatch Nout Nin) :=
    Real.sq_sqrt (variance_nonneg _ _)
  have hs0 : 0 < sgdSd Δ i j := by
    unfold sgdSd
    exact Real.sqrt_pos.2 (lt_of_lt_of_le (pow_pos hF 2) (by nlinarith [hvar.1]))
  have hFs : frobNorm Δ ≤ sgdSd Δ i j := by
    nlinarith [hvar.1]
  obtain ⟨hP, hmean, hvar1, hlint, hdec⟩ := cp_Y_facts Δ hΔ i j hbar
  have hcomp := hC B (by omega) _ hP hmean hvar1 hlint hdec
    (Real.sqrt (B : ℝ) * Δ i j / sgdSd Δ i j)
  rw [cp_Y3 Δ hΔ i j] at hcomp
  rw [cp_expect_eq B hB1 Δ hΔ i j hbar]
  -- Gaussian shift
  have hXm : (gaussianReal 0 1).map id = gaussianReal 0 ((1 : ℝ) ^ 2).toNNReal := by simp
  have hshift := lem_app_sgd_shift_iv (gaussianReal 0 1) id 1 one_pos hXm
    (Real.sqrt (B : ℝ) * Δ i j / sgdSd Δ i j)
  simp only [signShiftMean, id, div_one, one_pow, mul_one] at hshift
  -- ratio and batch-constant bounds
  have hN := prop_app_sgd_batch_coefficient_iii B hB1
  have hNb := cp_N_bounds (Real.sqrt (B : ℝ)) (B : ℝ) (batchConst B) hr
    (Real.mul_self_sqrt hBpos.le).symm (by linarith [hN.1]) hN.2
  have hratio := cp_ratio_bound (Real.sqrt (B : ℝ)) (sgdSd Δ i j) (frobNorm Δ) (batchConst B)
    hr hF hFs hNb.1 hNb.2
  have hx_abs : |Real.sqrt (B : ℝ) * Δ i j / sgdSd Δ i j|
      = Real.sqrt (B : ℝ) * |Δ i j| / sgdSd Δ i j := by
    rw [abs_div, abs_mul, abs_of_nonneg hr.le, abs_of_pos hs0]
  have hx3 : |Real.sqrt (B : ℝ) * Δ i j / sgdSd Δ i j| ^ 3
      = (B : ℝ) ^ (3 / 2 : ℝ) * |Δ i j| ^ 3 / sgdSd Δ i j ^ 3 := by
    rw [hx_abs, cp_cube_root_pow]
    ring
  -- the three error pieces
  set E := ∫ v : Fin B → ℝ, Real.sign ((∑ a, v a) / Real.sqrt (B : ℝ)
      + Real.sqrt (B : ℝ) * Δ i j / sgdSd Δ i j)
      ∂(Measure.pi fun _ : Fin B => (gaussBatch Nout Nin).map (sgdStdCoord Δ i j)) with hEdef
  set G0 := ∫ g, Real.sign (g + Real.sqrt (B : ℝ) * Δ i j / sgdSd Δ i j) ∂(gaussianReal 0 1)
    with hG0
  set x := Real.sqrt (B : ℝ) * Δ i j / sgdSd Δ i j with hxdef
  set s := sgdSd Δ i j with hsdef
  set F := frobNorm Δ with hFdef
  set N := batchConst B with hNdef
  set m := ∫ p, (sgdCoord Δ i j p - Δ i j) ^ 3 ∂(gaussBatch Nout Nin) with hmdef
  have hA : |E - G0| ≤ sgdC1 * |m / s ^ 3| / Real.sqrt (B : ℝ) + C₂ / (B : ℝ) := hcomp
  have hBd : |G0 - Real.sqrt (2 / Real.pi) * x|
      ≤ |x| ^ 3 / (3 * Real.sqrt (2 * Real.pi)) := hshift
  have hr' : |Real.sqrt (2 / Real.pi) * x - Real.sqrt (2 / Real.pi) * N * Δ i j / F|
      ≤ Real.sqrt (2 / Real.pi) * |Δ i j|
          * (Real.sqrt (B : ℝ) * (s ^ 2 - F ^ 2) / (s * F * (s + F)) + 4 / (F * Real.sqrt (B : ℝ))) := by
    have e : Real.sqrt (2 / Real.pi) * x - Real.sqrt (2 / Real.pi) * N * Δ i j / F
        = Real.sqrt (2 / Real.pi) * Δ i j * (Real.sqrt (B : ℝ) / s - N / F) := by
      rw [hxdef, hsdef, hFdef, hNdef]
      ring
    rw [e, abs_mul, abs_mul, abs_of_nonneg (Real.sqrt_nonneg (2 / Real.pi))]
    exact mul_le_mul_of_nonneg_left hratio (by positivity)
  have htri : |E - Real.sqrt (2 / Real.pi) * N * Δ i j / F|
      ≤ |E - G0| + |G0 - Real.sqrt (2 / Real.pi) * x|
          + |Real.sqrt (2 / Real.pi) * x - Real.sqrt (2 / Real.pi) * N * Δ i j / F| := by
    have h1 := abs_sub_le E G0 (Real.sqrt (2 / Real.pi) * N * Δ i j / F)
    have h2 := abs_sub_le G0 (Real.sqrt (2 / Real.pi) * x) (Real.sqrt (2 / Real.pi) * N * Δ i j / F)
    linarith
  have e1 : sgdC1 * |m / s ^ 3| / Real.sqrt (B : ℝ) = sgdC1 * |m| / (s ^ 3 * Real.sqrt (B : ℝ)) := by
    rw [abs_div, abs_of_pos (pow_pos hs0 3)]
    ring
  have e2 : |x| ^ 3 / (3 * Real.sqrt (2 * Real.pi))
      = (B : ℝ) ^ (3 / 2 : ℝ) * |Δ i j| ^ 3 / (3 * Real.sqrt (2 * Real.pi) * s ^ 3) := by
    rw [hx3]
    field_simp
  have e3 : Real.sqrt (2 / Real.pi) * |Δ i j|
          * (Real.sqrt (B : ℝ) * (s ^ 2 - F ^ 2) / (s * F * (s + F)) + 4 / (F * Real.sqrt (B : ℝ)))
      = Real.sqrt (2 / Real.pi) * (Real.sqrt (B : ℝ) * |Δ i j| * (s ^ 2 - F ^ 2))
              / (s * F * (s + F))
          + Real.sqrt (2 / Real.pi) * (4 * |Δ i j|) / (F * Real.sqrt (B : ℝ)) := by
    field_simp
  have hsum := add_le_add (add_le_add hA hBd) hr'
  rw [e1, e2, e3] at hsum
  calc |E - Real.sqrt (2 / Real.pi) * N * Δ i j / F|
      ≤ _ := htri
    _ ≤ _ := by linarith [hsum]

private lemma id_frob_sq {n m : ℕ} (D : Matrix (Fin n) (Fin m) ℝ) :
    frobNorm D ^ 2 = ∑ i, ∑ j, D i j ^ 2 := by
  simpa only [sq] using iso_frobNorm_sq D

private lemma id_sq_bound (x a : ℝ) (h : |x| ≤ a) : x ^ 2 ≤ a ^ 2 := by
  nlinarith [sq_abs x, abs_nonneg x]

private lemma id_row_col {n m : ℕ} (D : Matrix (Fin n) (Fin m) ℝ)
    (K C k : ℝ) (hk : 0 < k) (hC : 0 ≤ C)
    (hn : (n : ℝ) ≤ K * k) (hm : (m : ℝ) ≤ K * k)
    (he : ∀ i j, |D i j| ≤ C / k) :
    (∀ i, ∑ j, D i j ^ 2 ≤ K * C ^ 2 / k) ∧
    (∀ j, ∑ i, D i j ^ 2 ≤ K * C ^ 2 / k) := by
  have hb (a : ℕ) (ha : (a : ℝ) ≤ K * k) (v : Fin a → ℝ)
      (hv : ∀ i, |v i| ≤ C / k) : ∑ i, v i ^ 2 ≤ K * C ^ 2 / k := by
    calc ∑ i, v i ^ 2 ≤ ∑ _ : Fin a, (C / k) ^ 2 :=
          Finset.sum_le_sum fun i _ => id_sq_bound _ _ (hv i)
      _ = (a : ℝ) * (C / k) ^ 2 := by simp
      _ ≤ (K * k) * (C / k) ^ 2 := mul_le_mul_of_nonneg_right ha (sq_nonneg _)
      _ = K * C ^ 2 / k := by field_simp <;> ring
  exact ⟨fun i => hb m hm (D i) (he i), fun j => hb n hn (fun i => D i j) (fun i => he i j)⟩

private lemma id_deleted {n m : ℕ} (D : Matrix (Fin n) (Fin m) ℝ)
    (i : Fin n) (j : Fin m) :
    frobNorm D ^ 2 ≤ frobNorm (sgdDeletedBlock D i j) ^ 2
      + (∑ l, D i l ^ 2) + (∑ a, D a j ^ 2) := by
  rw [id_frob_sq, id_frob_sq]
  have hp (a : Fin n) (b : Fin m) : D a b ^ 2 ≤
      sgdDeletedBlock D i j a b ^ 2 + (if a = i then D a b ^ 2 else 0)
        + (if b = j then D a b ^ 2 else 0) := by
    by_cases ha : a = i <;> by_cases hb : b = j <;>
      simp [sgdDeletedBlock, ha, hb] <;> positivity
  have h := Finset.sum_le_sum fun a (_ : a ∈ Finset.univ) =>
    Finset.sum_le_sum fun b (_ : b ∈ Finset.univ) => hp a b
  simpa [Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.sum_ite_eq'] using h

private lemma id_coord_data {n m : ℕ} (D : Matrix (Fin n) (Fin m) ℝ)
    (hD : D ≠ 0) (K C f k : ℝ) (hk : 1 ≤ k) (hK : 1 ≤ K) (hC : 0 < C)
    (hf : 0 < f) (hF : f ≤ frobNorm D) (hsize : 8 * K * C ^ 2 / f ^ 2 ≤ k)
    (he : ∀ i j, |D i j| ≤ C / k)
    (hr : ∀ i, ∑ j, D i j ^ 2 ≤ K * C ^ 2 / k)
    (hc : ∀ j, ∑ i, D i j ^ 2 ≤ K * C ^ 2 / k)
    (i : Fin n) (j : Fin m) :
    frobNorm D / 2 ≤ frobNorm (sgdDeletedBlock D i j) ∧
    frobNorm D ≤ sgdSd D i j ∧
    sgdSd D i j ^ 2 - frobNorm D ^ 2 ≤ ((4 * K + 3) * C ^ 2) / k ∧
    |∫ p, (sgdCoord D i j p - D i j) ^ 3 ∂(gaussBatch n m)| / sgdSd D i j ^ 3
      ≤ (200 * C / f + 54 * K * C ^ 2 / f ^ 2) / k := by
  have hk0 : 0 < k := by linarith
  have hF0 : 0 < frobNorm D := lt_of_lt_of_le hf hF
  have hs0 : 0 ≤ sgdSd D i j := Real.sqrt_nonneg _
  have hs2 : sgdSd D i j ^ 2 = variance (sgdCoord D i j) (gaussBatch n m) :=
    Real.sq_sqrt (variance_nonneg _ _)
  have hvar := lem_app_sgd_moments_iii D hD i j
  have hFs : frobNorm D ≤ sgdSd D i j := by nlinarith [hvar.1]
  have hspos : 0 < sgdSd D i j := hF0.trans_le hFs
  have hsmall : K * C ^ 2 / k ≤ f ^ 2 / 8 := by
    apply (div_le_iff₀ hk0).2
    have h := (div_le_iff₀ (sq_pos_of_pos hf)).1 hsize
    nlinarith
  have hdel := id_deleted D i j
  have hb0 : 0 ≤ frobNorm (sgdDeletedBlock D i j) := Real.sqrt_nonneg _
  have hb : frobNorm D / 2 ≤ frobNorm (sgdDeletedBlock D i j) := by
    nlinarith [hr i, hc j]
  have he2 := id_sq_bound _ _ (he i j)
  have hk2 : (C / k) ^ 2 ≤ C ^ 2 / k := by
    rw [div_pow]
    exact div_le_div_of_nonneg_left (sq_nonneg C) hk0 (by nlinarith : k ≤ k ^ 2)
  have hv : sgdSd D i j ^ 2 - frobNorm D ^ 2 ≤ ((4 * K + 3) * C ^ 2) / k := by
    rw [hs2, lem_app_sgd_moments_ii D hD i j]
    calc _ ≤ 4 * (K * C ^ 2 / k) + 3 * (C ^ 2 / k) := by nlinarith [hr i, hc j]
      _ = _ := by ring
  have hR : ∑ l, sgdRow D i j l ^ 2 ≤ K * C ^ 2 / k := by
    refine le_trans (Finset.sum_le_sum fun l _ => ?_) (hr i)
    by_cases hl : l = j <;> simp [sgdRow, hl, sq_nonneg]
  have hQ : ∑ a, sgdCol D i j a ^ 2 ≤ K * C ^ 2 / k := by
    refine le_trans (Finset.sum_le_sum fun a _ => ?_) (hc j)
    by_cases ha : a = i <;> simp [sgdCol, ha, sq_nonneg]
  have hRQ : Real.sqrt (∑ l, sgdRow D i j l ^ 2) * Real.sqrt (∑ a, sgdCol D i j a ^ 2)
      ≤ K * C ^ 2 / k := by
    have hM : 0 ≤ K * C ^ 2 / k := by positivity
    have h1 := Real.sq_sqrt (Finset.sum_nonneg fun l (_ : l ∈ Finset.univ) => sq_nonneg (sgdRow D i j l))
    have h2 := Real.sq_sqrt (Finset.sum_nonneg fun a (_ : a ∈ Finset.univ) => sq_nonneg (sgdCol D i j a))
    nlinarith [Real.sqrt_nonneg (∑ l, sgdRow D i j l ^ 2),
      Real.sqrt_nonneg (∑ a, sgdCol D i j a ^ 2),
      mul_nonneg (sub_nonneg.2 hR) (sub_nonneg.2 hQ),
      sq_nonneg (Real.sqrt (∑ l, sgdRow D i j l ^ 2) - Real.sqrt (∑ a, sgdCol D i j a ^ 2))]
  have hm := lem_app_sgd_moments_v D hD i j
  have hm' : |∫ p, (sgdCoord D i j p - D i j) ^ 3 ∂(gaussBatch n m)|
      ≤ 200 * (C / k) * frobNorm D ^ 2 + 54 * frobNorm D * (K * C ^ 2 / k) := by
    calc _ ≤ _ := hm
      _ ≤ _ := by
        have h1 := mul_le_mul_of_nonneg_right (he i j) (show 0 ≤ 200 * frobNorm D ^ 2 by positivity)
        have h2 := mul_le_mul_of_nonneg_left hRQ (show 0 ≤ 54 * frobNorm D by positivity)
        nlinarith
  refine ⟨hb, hFs, hv, ?_⟩
  calc _ ≤ (200 * (C / k) * frobNorm D ^ 2 + 54 * frobNorm D * (K * C ^ 2 / k)) / frobNorm D ^ 3 := by
          exact div_le_div₀ (by positivity) hm' (pow_pos hF0 3) (pow_le_pow_left₀ hF0.le hFs 3)
    _ = (200 * C / frobNorm D + 54 * K * C ^ 2 / frobNorm D ^ 2) / k := by field_simp <;> ring
    _ ≤ _ := by gcongr

private lemma id_error (c A V R C f k t r s F d m : ℝ)
    (hc : 0 ≤ c) (hA : 0 ≤ A) (hV : 0 ≤ V) (hR : 0 ≤ R) (hC : 0 ≤ C)
    (hf : 0 < f) (ht : 0 < t) (hk : k = t ^ 2) (htr : t ≤ r) (hr : r ≤ R * t)
    (hF : f ≤ F) (hs : F ≤ s) (hd : |d| ≤ C / k)
    (hm : |m| / s ^ 3 ≤ A / k) (hv0 : 0 ≤ s ^ 2 - F ^ 2)
    (hv : s ^ 2 - F ^ 2 ≤ V / k) :
    c * |m| / (s ^ 3 * r)
      + r ^ 3 * |d| ^ 3 / (3 * Real.sqrt (2 * Real.pi) * s ^ 3)
      + Real.sqrt (2 / Real.pi) * (r * |d| * (s ^ 2 - F ^ 2)) / (s * F * (s + F))
      + Real.sqrt (2 / Real.pi) * (4 * |d|) / (F * r)
    ≤ (c * A + R ^ 3 * C ^ 3 / (3 * Real.sqrt (2 * Real.pi) * f ^ 3)
      + Real.sqrt (2 / Real.pi) * (R * C * V) / f ^ 3
      + Real.sqrt (2 / Real.pi) * (4 * C) / f) / t ^ 3 := by
  have hk0 : 0 < k := by rw [hk]; positivity
  have hr0 : 0 < r := ht.trans_le htr
  have hF0 : 0 < F := hf.trans_le hF
  have hs0 : 0 < s := hF0.trans_le hs
  have hsf : f ≤ s := hF.trans hs
  have hden : f ^ 3 ≤ s * F * (s + F) := by
    calc f ^ 3 = f * f * f := by ring
      _ ≤ s * F * (s + F) := by gcongr; linarith
  have h1 : c * |m| / (s ^ 3 * r) ≤ c * A / t ^ 3 := by
    calc _ = c * (|m| / s ^ 3) / r := by ring
      _ ≤ c * (A / k) / t := by gcongr
      _ = _ := by rw [hk]; field_simp <;> ring
  have h2 : r ^ 3 * |d| ^ 3 / (3 * Real.sqrt (2 * Real.pi) * s ^ 3)
      ≤ (R ^ 3 * C ^ 3 / (3 * Real.sqrt (2 * Real.pi) * f ^ 3)) / t ^ 3 := by
    calc _ ≤ (R * t) ^ 3 * (C / k) ^ 3 / (3 * Real.sqrt (2 * Real.pi) * f ^ 3) := by
          gcongr
      _ = _ := by rw [hk]; field_simp <;> ring
  have h3 : Real.sqrt (2 / Real.pi) * (r * |d| * (s ^ 2 - F ^ 2)) / (s * F * (s + F))
      ≤ (Real.sqrt (2 / Real.pi) * (R * C * V) / f ^ 3) / t ^ 3 := by
    calc _ ≤ Real.sqrt (2 / Real.pi) * ((R * t) * (C / k) * (V / k)) / f ^ 3 := by
          gcongr
      _ = _ := by rw [hk]; field_simp <;> ring
  have h4 : Real.sqrt (2 / Real.pi) * (4 * |d|) / (F * r)
      ≤ (Real.sqrt (2 / Real.pi) * (4 * C) / f) / t ^ 3 := by
    calc _ ≤ Real.sqrt (2 / Real.pi) * (4 * (C / k)) / (f * t) := by gcongr
      _ = _ := by rw [hk]; field_simp <;> ring
  calc _ ≤ c * A / t ^ 3
      + (R ^ 3 * C ^ 3 / (3 * Real.sqrt (2 * Real.pi) * f ^ 3)) / t ^ 3
      + (Real.sqrt (2 / Real.pi) * (R * C * V) / f ^ 3) / t ^ 3
      + (Real.sqrt (2 / Real.pi) * (4 * C) / f) / t ^ 3 := by linarith
    _ = _ := by ring

private lemma id_l1 {n m : ℕ} (D : Matrix (Fin n) (Fin m) ℝ) (K k : ℝ)
    (hK : 0 ≤ K) (hk : 0 ≤ k) (hn : (n : ℝ) ≤ K * k) (hm : (m : ℝ) ≤ K * k) :
    ∑ i, ∑ j, |D i j| ≤ K * k * frobNorm D := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin n × Fin m))
    (fun _ => (1 : ℝ)) (fun p => |D p.1 p.2|)
  simp only [one_mul, one_pow, Finset.sum_const, Finset.card_univ,
    Fintype.card_prod, Fintype.card_fin, nsmul_eq_mul, mul_one, sq_abs,
    Fintype.sum_prod_type] at h
  rw [← id_frob_sq] at h
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg _
  have hnm : (n : ℝ) * m ≤ (K * k) ^ 2 := by nlinarith [mul_le_mul hn hm hm0 (mul_nonneg hK hk)]
  have hF : 0 ≤ frobNorm D := Real.sqrt_nonneg _
  have hS : 0 ≤ ∑ i, ∑ j, |D i j| := by positivity
  push_cast at h
  apply (sq_le_sq₀ hS (by positivity : 0 ≤ K * k * frobNorm D)).1
  calc _ ≤ _ := h
    _ ≤ (K * k) ^ 2 * frobNorm D ^ 2 := mul_le_mul_of_nonneg_right hnm (sq_nonneg _)
    _ = _ := by ring

private lemma id_ratio (K a b t : ℝ) :
    K * (a + b) / (Real.sqrt (2 / Real.pi) * ((2 / Real.pi) * t))
      = Real.pi * K * (a + b) / (2 * Real.sqrt (2 / Real.pi) * t) := by
  field_simp
  <;> ring

/-- **thm:app-sgd-iso-drift** `Muon.SignSGD.thm_app_sgd_iso_drift`.

cr-2026-10-23. LaTeX statement (verbatim):
\begin{theorem}[Isotropic drift]\label{thm:app-sgd-iso-drift}
There is a constant $C_r$ depending only on $K,f_-,C_\Delta$ such that, for
every state in the isotropic regime with
$k\ge k_0\defeq\max\{4,8KC_\Delta^2/f_-^2\}$,
\begin{equation}\label{eqn:app-sgd-iso-entry}
\Big|\EE\sign(G^\circ_{ij})-\sqrt{\frac2\pi}\,\mathcal N_B\frac{\Delta_{ij}}F\Big|\le e_k\defeq\frac{C_2}B+\frac{C_r}{k^{3/2}}\qquad\text{for all }(i,j).
\end{equation}
With $\mathsf D\defeq\langle\Delta,\EE S\rangle_\F$ and
$\mathsf D_0\defeq\sqrt{2/\pi}\,\mathcal N_BF=\mathcal N_B\sqrt{4\cR(\Delta)/\pi}$,
\begin{equation}\label{eqn:app-sgd-iso-sum}
\abs{\mathsf D-\mathsf D_0}\le KF\Big(C_2+\frac{C_r}{\sqrt k}\Big),\qquad
\Big|\frac{\mathsf D}{\mathsf D_0}-1\Big|\le\frac{K(C_2+C_r/\sqrt k)}{\sqrt{2/\pi}\,\mathcal N_B}\le\frac{\pi K(C_2+C_r)}{2\sqrt{2/\pi}\,\sqrt k}.
\end{equation}
No hypothesis is made on the operator norm or the rank of $\Delta$.
\end{theorem}
Quantifier order: `C₂` universal; then `(K, f₋, C_Δ)` with `1 ≤ K`, `0 < f₋`, `0 < C_Δ`; then
`C_r` (which may depend on those three only, not on `f₊`); then the regime parameters `P` with the
same `K, f₋, C_Δ` and any `f₊ ≥ f₋`; then dimensions, batch size and state. The four conjuncts are
the entry bound `e_k`, the absolute sum bound, and the relative bound `a ≤ b ≤ c` of its display, with
`a` the relative error, `b = K(C₂+C_r/√k)/(√(2/π)𝒩_B)` and `c = πK(C₂+C_r)/(2√(2/π)√k)`.
The witnesses are taken nonnegative, which is what makes `b ≤ c` hold. -/
theorem thm_app_sgd_iso_drift :
    ∃ C₂ : ℝ, 0 ≤ C₂ ∧ ∀ K fMin Cdelta : ℝ, 1 ≤ K → 0 < fMin → 0 < Cdelta →
      ∃ Cr : ℝ, 0 ≤ Cr ∧ ∀ P : IsoParams, P.K = K → P.fMin = fMin → P.Cdelta = Cdelta →
        ∀ (Nout Nin B : ℕ) (Δ : Matrix (Fin Nout) (Fin Nin) ℝ),
          def_app_sgd_iso_regime P Nout Nin B Δ →
          isoK0 P ≤ (kOf Nout Nin B : ℝ) →
          (∀ i j, |expSignEntry Nout Nin B Δ i j
              - Real.sqrt (2 / Real.pi) * batchConst B * Δ i j / frobNorm Δ|
              ≤ C₂ / (B : ℝ) + Cr / (kOf Nout Nin B : ℝ) ^ (3 / 2 : ℝ))
          ∧ |∑ i, ∑ j, Δ i j * expSignEntry Nout Nin B Δ i j
              - Real.sqrt (2 / Real.pi) * batchConst B * frobNorm Δ|
              ≤ P.K * frobNorm Δ * (C₂ + Cr / Real.sqrt (kOf Nout Nin B : ℝ))
          ∧ |(∑ i, ∑ j, Δ i j * expSignEntry Nout Nin B Δ i j)
                / (Real.sqrt (2 / Real.pi) * batchConst B * frobNorm Δ) - 1|
              ≤ P.K * (C₂ + Cr / Real.sqrt (kOf Nout Nin B : ℝ))
                  / (Real.sqrt (2 / Real.pi) * batchConst B)
          ∧ P.K * (C₂ + Cr / Real.sqrt (kOf Nout Nin B : ℝ))
                  / (Real.sqrt (2 / Real.pi) * batchConst B)
              ≤ Real.pi * P.K * (C₂ + Cr)
                  / (2 * Real.sqrt (2 / Real.pi) * Real.sqrt (kOf Nout Nin B : ℝ)) := by
  obtain ⟨C₂, hcoord⟩ := prop_app_sgd_coordinate
  let C2 := max C₂ 0
  have hC2 : 0 ≤ C2 := le_max_right _ _
  have hC2' : C₂ ≤ C2 := le_max_left _ _
  refine ⟨C2, hC2, ?_⟩
  intro K f C hK hf hC
  let A := 200 * C / f + 54 * K * C ^ 2 / f ^ 2
  let V := (4 * K + 3) * C ^ 2
  let Cr := sgdC1 * A + K ^ 3 * C ^ 3 / (3 * Real.sqrt (2 * Real.pi) * f ^ 3)
    + Real.sqrt (2 / Real.pi) * (K * C * V) / f ^ 3
    + Real.sqrt (2 / Real.pi) * (4 * C) / f
  have hC1 : 0 ≤ sgdC1 := by unfold sgdC1; positivity
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hV : 0 ≤ V := by dsimp [V]; positivity
  have hCr : 0 ≤ Cr := by dsimp [Cr]; positivity
  refine ⟨Cr, hCr, ?_⟩
  intro P hPK hPf hPC n m B D hreg hthreshold
  let k : ℝ := kOf n m B
  let t := Real.sqrt k
  let r := Real.sqrt (B : ℝ)
  obtain ⟨hn, hm, hB, hF, _, he⟩ := hreg
  rw [hPK] at hn hm hB
  rw [hPf] at hF
  rw [hPC] at he
  have hk4 : 4 ≤ k := (le_max_left _ _).trans hthreshold
  have hk1 : 1 ≤ k := by linarith
  have hk0 : 0 < k := by linarith
  have ht : 0 < t := Real.sqrt_pos.2 hk0
  have ht1 : 1 ≤ t := by dsimp [t]; exact (Real.le_sqrt (by norm_num) hk0.le).2 (by simpa using hk1)
  have hkt : k = t ^ 2 := (Real.sq_sqrt hk0.le).symm
  have hkB : k ≤ (B : ℝ) := by
    change (kOf n m B : ℝ) ≤ (B : ℝ)
    exact_mod_cast (show kOf n m B ≤ B by unfold kOf; omega)
  have hB4 : 4 ≤ B := by exact_mod_cast (hk4.trans hkB)
  have hB0 : (0 : ℝ) < B := hk0.trans_le hkB
  have hr0 : 0 < r := Real.sqrt_pos.2 hB0
  have hr2 : r ^ 2 = (B : ℝ) := Real.sq_sqrt hB0.le
  have htr : t ≤ r := Real.sqrt_le_sqrt hkB
  have hrK : r ≤ K * t := by
    have hKk : K * k ≤ K ^ 2 * k := by nlinarith [mul_nonneg (sub_nonneg.2 hK) hk0.le]
    have hKt : 0 ≤ K * t := by positivity
    nlinarith
  have hF0 : 0 < frobNorm D := hf.trans_le hF
  have hD : D ≠ 0 := by
    intro hz
    simp [hz, frobNorm] at hF0
  have hsize : 8 * K * C ^ 2 / f ^ 2 ≤ k := by
    have hh := (le_max_right 4 (8 * P.K * P.Cdelta ^ 2 / P.fMin ^ 2)).trans hthreshold
    simpa only [hPK, hPC, hPf] using hh
  obtain ⟨hrow, hcol⟩ := id_row_col D K C k hk0 hC.le hn hm he
  have hdata := id_coord_data D hD K C f k hk1 hK hC hf hF hsize he hrow hcol
  have hp : k ^ (3 / 2 : ℝ) = t ^ 3 := cp_cube_root_pow (kOf n m B)
  have hentry : ∀ i j, |expSignEntry n m B D i j
      - Real.sqrt (2 / Real.pi) * batchConst B * D i j / frobNorm D|
      ≤ C2 / (B : ℝ) + Cr / t ^ 3 := by
    intro i j
    obtain ⟨hbar, hFs, hv, hm3⟩ := hdata i j
    have hv0 : 0 ≤ sgdSd D i j ^ 2 - frobNorm D ^ 2 := by
      nlinarith [Real.sqrt_nonneg (variance (sgdCoord D i j) (gaussBatch n m))]
    have herr := id_error sgdC1 A V K C f k t r (sgdSd D i j) (frobNorm D) (D i j)
      (∫ p, (sgdCoord D i j p - D i j) ^ 3 ∂(gaussBatch n m))
      hC1 hA hV (by linarith) hC.le hf ht hkt htr hrK hF hFs (he i j) hm3 hv0 hv
    have hh := hcoord n m B D i j hB4 hD hbar
    rw [cp_cube_root_pow] at hh
    have hCdiv : C₂ / (B : ℝ) ≤ C2 / (B : ℝ) := div_le_div_of_nonneg_right hC2' hB0.le
    change _ ≤ Cr / t ^ 3 at herr
    linarith
  have hL := id_l1 D K k (by linarith) hk0.le hn hm
  let E := C2 / (B : ℝ) + Cr / t ^ 3
  have hE : 0 ≤ E := by dsimp [E]; positivity
  let L := Real.sqrt (2 / Real.pi) * batchConst B
  let S := ∑ i, ∑ j, D i j * expSignEntry n m B D i j
  have hsum : |S - L * frobNorm D| ≤ K * frobNorm D * (C2 + Cr / t) := by
    have hid : S - L * frobNorm D = ∑ i, ∑ j,
        D i j * (expSignEntry n m B D i j - L * D i j / frobNorm D) := by
      dsimp [S]
      simp only [mul_sub, Finset.sum_sub_distrib]
      congr 1
      calc L * frobNorm D = L / frobNorm D * frobNorm D ^ 2 := by field_simp <;> ring
        _ = ∑ i, ∑ j, D i j * (L * D i j / frobNorm D) := by
          rw [id_frob_sq, Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun j _ => by ring
    calc |S - L * frobNorm D| = |∑ i, ∑ j,
        D i j * (expSignEntry n m B D i j - L * D i j / frobNorm D)| := by rw [hid]
      _ ≤ ∑ i, ∑ j, |D i j * (expSignEntry n m B D i j - L * D i j / frobNorm D)| :=
        (Finset.abs_sum_le_sum_abs _ _).trans
          (Finset.sum_le_sum fun i _ => Finset.abs_sum_le_sum_abs _ _)
      _ ≤ ∑ i, ∑ j, |D i j| * E := by
        apply Finset.sum_le_sum; intro i _
        apply Finset.sum_le_sum; intro j _
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (hentry i j) (abs_nonneg _)
      _ = (∑ i, ∑ j, |D i j|) * E := by simp only [Finset.sum_mul]
      _ ≤ (K * k * frobNorm D) * E := mul_le_mul_of_nonneg_right hL hE
      _ ≤ K * k * frobNorm D * (C2 / k + Cr / t ^ 3) := by
        dsimp [E]
        gcongr
      _ = K * frobNorm D * (C2 + Cr / t) := by rw [hkt]; field_simp <;> ring
  have hN := (le_max_left _ _).trans (prop_app_sgd_batch_coefficient_ii B (by omega)).1
  have hNlow : (2 / Real.pi) * t ≤ batchConst B :=
    (mul_le_mul_of_nonneg_left htr (by positivity)).trans hN
  have hNpos : 0 < batchConst B := lt_of_lt_of_le (by positivity) hNlow
  have hLpos : 0 < L := by dsimp [L]; positivity
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i j
    change _ ≤ C2 / (B : ℝ) + Cr / k ^ (3 / 2 : ℝ)
    rw [hp]
    exact hentry i j
  · simpa only [hPK] using hsum
  · change |S / (L * frobNorm D) - 1| ≤ P.K * (C2 + Cr / t) / L
    rw [hPK]
    have hid : S / (L * frobNorm D) - 1 = (S - L * frobNorm D) / (L * frobNorm D) := by
      field_simp
    rw [hid, abs_div, abs_of_pos (mul_pos hLpos hF0)]
    calc _ ≤ (K * frobNorm D * (C2 + Cr / t)) / (L * frobNorm D) :=
          div_le_div_of_nonneg_right hsum (by positivity)
      _ = _ := by field_simp <;> ring
  · change P.K * (C2 + Cr / t) / L ≤ Real.pi * P.K * (C2 + Cr) /
        (2 * Real.sqrt (2 / Real.pi) * t)
    rw [hPK]
    calc _ ≤ K * (C2 + Cr) / (Real.sqrt (2 / Real.pi) * ((2 / Real.pi) * t)) := by
          dsimp [L]
          gcongr
          exact div_le_self hCr ht1
      _ = _ := id_ratio K C2 Cr t

private lemma iso_batchMean_eq_expSignEntry {Nout Nin B : ℕ} {Ω : Type*}
    [MeasurableSpace Ω] (Pr : Measure Ω) [IsProbabilityMeasure Pr]
    (C : Covariances Nout Nin) (hSout : C.Sout = 1) (hSin : C.Sin = 1)
    (ν : Measure (Vec Nout × Vec Nin)) (hν : Muon.Setup.assum_data_target C ν)
    (β : Ω → Batch Nout Nin B)
    (hβ : Muon.Setup.IIDBatch Pr ν (fun a ω => ((β ω).xout a, (β ω).xin a)))
    (Δ : Matrix (Fin Nout) (Fin Nin) ℝ) (i : Fin Nout) (j : Fin Nin) :
    batchMean Pr (fun ω => signGrad Δ (β ω)) i j = expSignEntry Nout Nin B Δ i j := by
  let Y : Ω → Fin B → Vec Nout × Vec Nin :=
    fun ω a => ((β ω).xout a, (β ω).xin a)
  have hYm : AEMeasurable Y Pr := aemeasurable_pi_iff.2 hβ.meas
  have hlaw : Pr.map Y = Measure.pi (fun _ : Fin B => gaussBatch Nout Nin) := by
    rw [(iIndepFun_iff_map_fun_eq_pi_map hβ.meas).1 hβ.indep]
    simp only [hβ.law, iso_nu_eq C hSout hSin ν hν]
  have hf : Measurable (fun p : Fin B → Vec Nout × Vec Nin =>
      Real.sign ((1 / (B : ℝ)) * ∑ a, sgdCoord Δ i j (p a))) := by
    have hsign : Measurable Real.sign := by
      unfold Real.sign
      exact Measurable.ite (measurableSet_lt measurable_id measurable_const)
        measurable_const (Measurable.ite (measurableSet_lt measurable_const measurable_id)
          measurable_const measurable_const)
    apply hsign.comp
    unfold sgdCoord
    fun_prop
  unfold expSignEntry
  rw [← hlaw, integral_map hYm hf.aestronglyMeasurable]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun ω => by
    simp [signGrad, physGrad, residual, sgdCoord, Y, mul_assoc]

private lemma iso_risk_sqrt {Nout Nin : ℕ} (C : Covariances Nout Nin)
    (hSout : C.Sout = 1) (hSin : C.Sin = 1)
    (Δ : Matrix (Fin Nout) (Fin Nin) ℝ) :
    Real.sqrt (2 * Muon.Setup.riskSigma C Δ) = frobNorm Δ ∧
      Real.sqrt (4 * Muon.Setup.riskSigma C Δ / Real.pi)
        = Real.sqrt (2 / Real.pi) * frobNorm Δ := by
  have hrisk : Muon.Setup.riskSigma C Δ = frobNorm Δ ^ 2 / 2 := by
    rw [Muon.Setup.riskSigma, iso_pairSigma_eq_sum C hSout hSin, iso_frobNorm_sq]
  have hF : 0 ≤ frobNorm Δ := Real.sqrt_nonneg _
  constructor
  · rw [hrisk, show 2 * (frobNorm Δ ^ 2 / 2) = frobNorm Δ ^ 2 by ring,
      Real.sqrt_sq hF]
  · rw [hrisk, show 4 * (frobNorm Δ ^ 2 / 2) / Real.pi
        = (2 / Real.pi) * frobNorm Δ ^ 2 by ring,
      Real.sqrt_mul (by positivity : 0 ≤ 2 / Real.pi), Real.sqrt_sq hF]

/-- **prop:app-sgd-iso** (`prop:signsgd-recursion-B`), frozen-state helper.

`prop_app_sgd_iso_frozen` cr-2026-10-23. LaTeX statement (verbatim):
\begin{proposition}[Isotropic \SignSGD recursion]\label{prop:app-sgd-iso}\label{prop:signsgd-recursion-B}
Let $\Sigmain=\Idin$ and $\Sigmaout=\Idout$, and let $\Dt$ be the state at
step $t$. Suppose that, almost surely, $\Dt$ with the batch size $B$ is in
the isotropic regime of \cref{def:app-sgd-iso-regime} and $k\ge k_0$. Then the
\SignSGD step satisfies
\begin{equation}\label{eqn:signsgd-risk-recursion-B}
\EE_t\big[\cR(t+1)\big]=\cR(t)-\lr\,\mathcal N_B\sqrt{\frac{4\cR(t)}\pi}+\frac{\lr^2}2\,\Nin\Nout+E_t,\qquad
\abs{E_t}\le\lr\,K\sqrt{2\cR(t)}\,\Big(C_2+\frac{C_r}{\sqrt k}\Big),
\end{equation}
with $C_2$ universal and $C_r$ from \cref{thm:app-sgd-iso-drift}. The error
is at most $\pi K(C_2+C_r)/(2\sqrt{2/\pi}\sqrt k)$ times the drift term.
\end{proposition}
Deterministic-state form: the one-step risk identity at a state `Δ` with the fresh batch integrated
under `Pr`, with `Δ` in the isotropic regime and `k ≥ k₀`. It is the trivial-past special case of
`prop_app_sgd_iso_filtered`, which is the label's conditional statement. The second conjunct is the
sentence "the error is at most `πK(C₂+C_r)/(2√(2/π)√k)` times the drift term", where the drift
term is `η 𝒩_B √(4𝓡(Δ)/π)`. Here `riskSigma C Δ = 𝓡(Δ)`. -/
theorem prop_app_sgd_iso_frozen :
    ∃ C₂ : ℝ, 0 ≤ C₂ ∧ ∀ K fMin Cdelta : ℝ, 1 ≤ K → 0 < fMin → 0 < Cdelta →
      ∃ Cr : ℝ, 0 ≤ Cr ∧ ∀ P : IsoParams, P.K = K → P.fMin = fMin → P.Cdelta = Cdelta →
        ∀ (Nout Nin B : ℕ) (η : ℝ), 0 ≤ η → ∀ (Δ : Matrix (Fin Nout) (Fin Nin) ℝ),
          def_app_sgd_iso_regime P Nout Nin B Δ →
          isoK0 P ≤ (kOf Nout Nin B : ℝ) →
          ∀ (Ω : Type) [MeasurableSpace Ω] (Pr : Measure Ω) [IsProbabilityMeasure Pr]
            (C : Covariances Nout Nin) (hSout : C.Sout = 1) (hSin : C.Sin = 1)
            (ν : Measure (Vec Nout × Vec Nin)) (hν : Muon.Setup.assum_data_target C ν)
            (β : Ω → Batch Nout Nin B)
            (hβ : Muon.Setup.IIDBatch Pr ν (fun a ω => ((β ω).xout a, (β ω).xin a))),
            |∫ ω, Muon.Setup.riskSigma C (def_app_sgd_update η Δ (β ω)) ∂Pr
                - (Muon.Setup.riskSigma C Δ
                    - η * batchConst B * Real.sqrt (4 * Muon.Setup.riskSigma C Δ / Real.pi)
                    + η ^ 2 / 2 * ((Nin : ℝ) * (Nout : ℝ)))|
              ≤ η * P.K * Real.sqrt (2 * Muon.Setup.riskSigma C Δ)
                  * (C₂ + Cr / Real.sqrt (kOf Nout Nin B : ℝ))
            ∧ |∫ ω, Muon.Setup.riskSigma C (def_app_sgd_update η Δ (β ω)) ∂Pr
                - (Muon.Setup.riskSigma C Δ
                    - η * batchConst B * Real.sqrt (4 * Muon.Setup.riskSigma C Δ / Real.pi)
                    + η ^ 2 / 2 * ((Nin : ℝ) * (Nout : ℝ)))|
              ≤ Real.pi * P.K * (C₂ + Cr)
                  / (2 * Real.sqrt (2 / Real.pi) * Real.sqrt (kOf Nout Nin B : ℝ))
                  * (η * batchConst B * Real.sqrt (4 * Muon.Setup.riskSigma C Δ / Real.pi)) := by
  obtain ⟨C₂, hC₂, hdrift⟩ := thm_app_sgd_iso_drift
  refine ⟨C₂, hC₂, ?_⟩
  intro K fMin Cdelta hK hfMin hCdelta
  obtain ⟨Cr, hCr, hdrift⟩ := hdrift K fMin Cdelta hK hfMin hCdelta
  refine ⟨Cr, hCr, ?_⟩
  intro P hPK hPf hPC Nout Nin B η hη Δ hreg hthreshold Ω _ Pr _ C hSout hSin ν hν β hβ
  obtain ⟨_, hsum, hrel, hratio⟩ :=
    hdrift P hPK hPf hPC Nout Nin B Δ hreg hthreshold
  have hFpos : 0 < frobNorm Δ := P.fMin_pos.trans_le hreg.2.2.2.1
  have hΔ : Δ ≠ 0 := by
    intro hz
    simp [hz, frobNorm] at hFpos
  have hk4 : 4 ≤ (kOf Nout Nin B : ℝ) :=
    (le_max_left _ _).trans hthreshold
  have hkB : kOf Nout Nin B ≤ B := by unfold kOf; omega
  have hB : 1 ≤ B := by
    have hk4' : 4 ≤ kOf Nout Nin B := by exact_mod_cast hk4
    omega
  have hBpos : (0 : ℝ) < B := by exact_mod_cast hB
  have hNlow := (le_max_left _ _).trans (prop_app_sgd_batch_coefficient_ii B hB).1
  have hNpos : 0 < batchConst B := lt_of_lt_of_le (by positivity) hNlow
  have hDpos : 0 < Real.sqrt (2 / Real.pi) * batchConst B * frobNorm Δ := by
    positivity
  obtain ⟨hF, hroot⟩ := iso_risk_sqrt C hSout hSin Δ
  have hrisk := prop_app_sgd_iso_volatility_ii Pr hB C hSout hSin ν hν β hβ Δ η hη
  simp only [if_neg hΔ, iso_batchMean_eq_expSignEntry Pr C hSout hSin ν hν β hβ Δ]
    at hrisk
  rw [hrisk, hF, hroot]
  let S := ∑ i, ∑ j, Δ i j * expSignEntry Nout Nin B Δ i j
  let D₀ := Real.sqrt (2 / Real.pi) * batchConst B * frobNorm Δ
  have herr : Muon.Setup.riskSigma C Δ - η * S
      + η ^ 2 / 2 * ((Nin : ℝ) * (Nout : ℝ))
      - (Muon.Setup.riskSigma C Δ
        - η * batchConst B * (Real.sqrt (2 / Real.pi) * frobNorm Δ)
        + η ^ 2 / 2 * ((Nin : ℝ) * (Nout : ℝ))) = -η * (S - D₀) := by
    dsimp [D₀]
    ring
  change |Muon.Setup.riskSigma C Δ - η * S
      + η ^ 2 / 2 * ((Nin : ℝ) * (Nout : ℝ))
      - (Muon.Setup.riskSigma C Δ
        - η * batchConst B * (Real.sqrt (2 / Real.pi) * frobNorm Δ)
        + η ^ 2 / 2 * ((Nin : ℝ) * (Nout : ℝ)))| ≤ _ ∧ _
  rw [herr, abs_mul, abs_neg, abs_of_nonneg hη]
  constructor
  · calc η * |S - D₀| ≤ η * (P.K * frobNorm Δ
          * (C₂ + Cr / Real.sqrt (kOf Nout Nin B : ℝ))) :=
        mul_le_mul_of_nonneg_left hsum hη
      _ = _ := by ring
  · have hrel' := hrel.trans hratio
    have hid : S - D₀ = (S / D₀ - 1) * D₀ := by
      dsimp [D₀]
      field_simp
    have hbound : |S - D₀| ≤
        (Real.pi * P.K * (C₂ + Cr)
          / (2 * Real.sqrt (2 / Real.pi) * Real.sqrt (kOf Nout Nin B : ℝ))) * D₀ := by
      rw [hid, abs_mul, abs_of_pos hDpos]
      exact mul_le_mul_of_nonneg_right hrel' hDpos.le
    calc η * |S - D₀| ≤ η * ((Real.pi * P.K * (C₂ + Cr)
          / (2 * Real.sqrt (2 / Real.pi) * Real.sqrt (kOf Nout Nin B : ℝ))) * D₀) :=
        mul_le_mul_of_nonneg_left hbound hη
      _ = _ := by dsimp [D₀]; ring

private lemma iso_sign_sq_le (x : ℝ) : Real.sign x ^ 2 ≤ 1 := by
  rcases lt_trichotomy x 0 with h | h | h
  · rw [Real.sign_of_neg h]; norm_num
  · rw [h, Real.sign_zero]; norm_num
  · rw [Real.sign_of_pos h]; norm_num

private lemma iso_risk_eq_sum {Nout Nin : ℕ} (C : Covariances Nout Nin)
    (hSout : C.Sout = 1) (hSin : C.Sin = 1) (U : Matrix (Fin Nout) (Fin Nin) ℝ) :
    Muon.Setup.riskSigma C U = (∑ i, ∑ j, U i j * U i j) / 2 := by
  unfold Muon.Setup.riskSigma
  rw [iso_pairSigma_eq_sum C hSout hSin]

private lemma iso_update_entry {Nout Nin B : ℕ} (η : ℝ) (Δ : Matrix (Fin Nout) (Fin Nin) ℝ)
    (β : Batch Nout Nin B) (i : Fin Nout) (j : Fin Nin) :
    def_app_sgd_update η Δ β i j = Δ i j - η * Real.sign (physGrad Δ β i j) := by
  simp [def_app_sgd_update]

/-! Private copy of the freezing lemma (`Muon.Foundations.freezing_condExp`, `Foundations/Freezing.lean`,
which is not in this file's import closure). Same proof, renamed `iso_freezing_*`. -/

private theorem iso_freezing_joint_restrict {Ω α β : Type*} (𝒢 : MeasurableSpace Ω)
    {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ] [mα : MeasurableSpace α]
    [mβ : MeasurableSpace β] (h𝒢 : 𝒢 ≤ mΩ) {X : Ω → α} {Y : Ω → β} (hX : Measurable[𝒢] X)
    (hY : Measurable Y) (hind : Indep 𝒢 (MeasurableSpace.comap Y mβ) μ) {s : Set Ω}
    (hs : MeasurableSet[𝒢] s) :
    (μ.restrict s).map (fun ω => (X ω, Y ω)) = ((μ.restrict s).map X).prod (μ.map Y) := by
  have hXm : Measurable X := hX.mono h𝒢 le_rfl
  have hs' : MeasurableSet s := h𝒢 _ hs
  symm
  apply Measure.prod_eq
  intro A B hA hB
  have hYB : MeasurableSet (Y ⁻¹' B) := hY hB
  have hYB' : MeasurableSet[MeasurableSpace.comap Y mβ] (Y ⁻¹' B) :=
    MeasurableSpace.measurableSet_comap.2 ⟨B, hB, rfl⟩
  have hXA : MeasurableSet[𝒢] (X ⁻¹' A) := hX hA
  have hI := (Indep_iff _ _ μ).1 hind
  rw [Measure.map_apply hXm hA, Measure.map_apply hY hB,
    Measure.map_apply (hXm.prodMk hY) (hA.prod hB), Set.mk_preimage_prod,
    Measure.restrict_apply ((hXm hA).inter (hY hB)), Measure.restrict_apply (hXm hA),
    Set.inter_right_comm]
  exact hI _ _ (hXA.inter hs) hYB'

private theorem iso_freezing_setIntegral {Ω α β : Type*} (𝒢 : MeasurableSpace Ω)
    {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ] [mα : MeasurableSpace α]
    [mβ : MeasurableSpace β] (h𝒢 : 𝒢 ≤ mΩ) {X : Ω → α} {Y : Ω → β} (hX : Measurable[𝒢] X)
    (hY : Measurable Y) (hind : Indep 𝒢 (MeasurableSpace.comap Y mβ) μ)
    {f : α → β → ℝ} (hf : Measurable (Function.uncurry f))
    (hfint : Integrable (fun ω => f (X ω) (Y ω)) μ) {s : Set Ω} (hs : MeasurableSet[𝒢] s) :
    ∫ ω in s, f (X ω) (Y ω) ∂μ = ∫ ω in s, ∫ y, f (X ω) y ∂(μ.map Y) ∂μ := by
  have hXm : Measurable X := hX.mono h𝒢 le_rfl
  have hpair : Measurable (fun ω => (X ω, Y ω)) := hXm.prodMk hY
  have hgm : Measurable (fun x => ∫ y, f x y ∂(μ.map Y)) :=
    (hf.stronglyMeasurable.integral_prod_right' (ν := μ.map Y)).measurable
  have hkey := iso_freezing_joint_restrict 𝒢 h𝒢 hX hY hind hs
  have hFs : Integrable (fun ω => f (X ω) (Y ω)) (μ.restrict s) := hfint.restrict
  have hint : Integrable (Function.uncurry f) (((μ.restrict s).map X).prod (μ.map Y)) := by
    rw [← hkey]
    exact (integrable_map_measure hf.aestronglyMeasurable hpair.aemeasurable).2 hFs
  calc ∫ ω in s, f (X ω) (Y ω) ∂μ
      = ∫ p, Function.uncurry f p ∂((μ.restrict s).map (fun ω => (X ω, Y ω))) := by
        rw [integral_map hpair.aemeasurable hf.aestronglyMeasurable]
        rfl
    _ = ∫ p, Function.uncurry f p ∂(((μ.restrict s).map X).prod (μ.map Y)) := by rw [hkey]
    _ = ∫ x, ∫ y, f x y ∂(μ.map Y) ∂((μ.restrict s).map X) := integral_prod _ hint
    _ = ∫ ω in s, ∫ y, f (X ω) y ∂(μ.map Y) ∂μ := by
        rw [integral_map hXm.aemeasurable hgm.aestronglyMeasurable]

private theorem iso_freezing_condExp {Ω α β : Type*} (𝒢 : MeasurableSpace Ω)
    {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ] [mα : MeasurableSpace α]
    [mβ : MeasurableSpace β] (h𝒢 : 𝒢 ≤ mΩ) {X : Ω → α} {Y : Ω → β} (hX : Measurable[𝒢] X)
    (hY : Measurable Y) (hind : Indep 𝒢 (MeasurableSpace.comap Y mβ) μ)
    {f : α → β → ℝ} (hf : Measurable (Function.uncurry f))
    (hfint : Integrable (fun ω => f (X ω) (Y ω)) μ) :
    condExp 𝒢 μ (fun ω => f (X ω) (Y ω)) =ᵐ[μ] fun ω => ∫ y, f (X ω) y ∂(μ.map Y) := by
  have hXm : Measurable X := hX.mono h𝒢 le_rfl
  have hpair : Measurable (fun ω => (X ω, Y ω)) := hXm.prodMk hY
  have hgm : Measurable (fun x => ∫ y, f x y ∂(μ.map Y)) :=
    (hf.stronglyMeasurable.integral_prod_right' (ν := μ.map Y)).measurable
  have hGm : Measurable[𝒢] (fun ω => ∫ y, f (X ω) y ∂(μ.map Y)) := hgm.comp hX
  have huniv := iso_freezing_joint_restrict 𝒢 h𝒢 hX hY hind MeasurableSet.univ
  rw [Measure.restrict_univ] at huniv
  have hint : Integrable (Function.uncurry f) ((μ.map X).prod (μ.map Y)) := by
    rw [← huniv]
    exact (integrable_map_measure hf.aestronglyMeasurable hpair.aemeasurable).2 hfint
  have hGint : Integrable (fun ω => ∫ y, f (X ω) y ∂(μ.map Y)) μ := by
    have h1 := hint.integral_prod_left
    exact (integrable_map_measure hgm.aestronglyMeasurable hXm.aemeasurable).1 h1
  refine (ae_eq_condExp_of_forall_setIntegral_eq h𝒢 hfint
    (fun s _ _ => hGint.integrableOn) (fun s hs _ => ?_)
      hGm.stronglyMeasurable.aestronglyMeasurable).symm
  exact (iso_freezing_setIntegral 𝒢 h𝒢 hX hY hind hf hfint hs).symm

private lemma iso_comp_measurable {Ω α β γ : Type*} {mΩ : MeasurableSpace Ω}
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ] (F : α → β → γ)
    (hF : Measurable (Function.uncurry F)) {X : Ω → α} {Y : Ω → β}
    (hX : Measurable X) (hY : Measurable Y) : Measurable (fun ω => F (X ω) (Y ω)) :=
  hF.comp (hX.prodMk hY)

private lemma iso_update_measurable {Nout Nin B : ℕ} (C : Covariances Nout Nin)
    (hSout : C.Sout = 1) (hSin : C.Sin = 1) (η : ℝ) :
    Measurable (Function.uncurry fun (Δ : Matrix (Fin Nout) (Fin Nin) ℝ)
      (b : Muon.Setup.Batch Nout Nin B) =>
        Muon.Setup.riskSigma C (def_app_sgd_update η Δ (toSignBatch b))) := by
  have hent : ∀ i j, Measurable (fun p : Matrix (Fin Nout) (Fin Nin) ℝ × Muon.Setup.Batch Nout Nin B =>
      def_app_sgd_update η p.1 (toSignBatch p.2) i j) := by
    intro i j
    have hphys : Measurable (fun p : Matrix (Fin Nout) (Fin Nin) ℝ × Muon.Setup.Batch Nout Nin B =>
        physGrad p.1 (toSignBatch p.2) i j) := by
      simp only [physGrad, residual, toSignBatch, dotProduct, Matrix.mulVec]
      fun_prop
    simp only [iso_update_entry]
    have h1 : Measurable (fun p : Matrix (Fin Nout) (Fin Nin) ℝ × Muon.Setup.Batch Nout Nin B =>
        p.1 i j) :=
      (measurable_pi_apply j).comp ((measurable_pi_apply i).comp measurable_fst)
    have h2 : Measurable (fun p : Matrix (Fin Nout) (Fin Nin) ℝ × Muon.Setup.Batch Nout Nin B =>
        η * Real.sign (physGrad p.1 (toSignBatch p.2) i j)) :=
      (cp_sign_meas.comp hphys).const_mul η
    exact h1.sub h2
  have hfun : (Function.uncurry fun (Δ : Matrix (Fin Nout) (Fin Nin) ℝ)
      (b : Muon.Setup.Batch Nout Nin B) =>
        Muon.Setup.riskSigma C (def_app_sgd_update η Δ (toSignBatch b)))
      = fun p => (∑ i, ∑ j, def_app_sgd_update η p.1 (toSignBatch p.2) i j
          * def_app_sgd_update η p.1 (toSignBatch p.2) i j) / 2 := by
    funext p
    simp only [Function.uncurry]
    rw [iso_risk_eq_sum C hSout hSin]
  rw [hfun]
  exact (Finset.measurable_sum Finset.univ fun i _ =>
    Finset.measurable_sum Finset.univ fun j _ => (hent i j).mul (hent i j)).div_const 2

private lemma iso_update_risk_bound {Nout Nin B : ℕ} (C : Covariances Nout Nin)
    (hSout : C.Sout = 1) (hSin : C.Sin = 1) (η : ℝ) (Δ : Matrix (Fin Nout) (Fin Nin) ℝ)
    (b : Muon.Setup.Batch Nout Nin B) :
    Muon.Setup.riskSigma C (def_app_sgd_update η Δ (toSignBatch b))
      ≤ frobNorm Δ ^ 2 + η ^ 2 * ((Nin : ℝ) * (Nout : ℝ)) := by
  rw [iso_risk_eq_sum C hSout hSin, iso_frobNorm_sq]
  have hpt : ∀ i j, def_app_sgd_update η Δ (toSignBatch b) i j
      * def_app_sgd_update η Δ (toSignBatch b) i j ≤ 2 * (Δ i j * Δ i j) + 2 * η ^ 2 := by
    intro i j
    rw [iso_update_entry]
    have hs := iso_sign_sq_le (physGrad Δ (toSignBatch b) i j)
    nlinarith [sq_nonneg (Δ i j + η * Real.sign (physGrad Δ (toSignBatch b) i j)),
      mul_le_mul_of_nonneg_left hs (sq_nonneg η)]
  have hsum := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) =>
    Finset.sum_le_sum fun j (_ : j ∈ Finset.univ) => hpt i j
  have hrhs : ∑ i, ∑ j, (2 * (Δ i j * Δ i j) + 2 * η ^ 2)
      = 2 * (∑ i, ∑ j, Δ i j * Δ i j) + 2 * η ^ 2 * ((Nout : ℝ) * (Nin : ℝ)) := by
    simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, ← Finset.mul_sum]
    ring
  nlinarith [hsum, hrhs]

/-- **prop:app-sgd-iso** (`prop:signsgd-recursion-B`), filtered (conditional on the past) form.

`prop_app_sgd_iso_filtered` cr-2026-10-23. LaTeX statement (verbatim):
\begin{proposition}[Isotropic \SignSGD recursion]\label{prop:app-sgd-iso}\label{prop:signsgd-recursion-B}
Let $\Sigmain=\Idin$ and $\Sigmaout=\Idout$, and let $\Dt$ be the state at
step $t$. Suppose that, almost surely, $\Dt$ with the batch size $B$ is in
the isotropic regime of \cref{def:app-sgd-iso-regime} and $k\ge k_0$. Then the
\SignSGD step satisfies
\begin{equation}\label{eqn:signsgd-risk-recursion-B}
\EE_t\big[\cR(t+1)\big]=\cR(t)-\lr\,\mathcal N_B\sqrt{\frac{4\cR(t)}\pi}+\frac{\lr^2}2\,\Nin\Nout+E_t,\qquad
\abs{E_t}\le\lr\,K\sqrt{2\cR(t)}\,\Big(C_2+\frac{C_r}{\sqrt k}\Big),
\end{equation}
with $C_2$ universal and $C_r$ from \cref{thm:app-sgd-iso-drift}. The error
is at most $\pi K(C_2+C_r)/(2\sqrt{2/\pi}\sqrt k)$ times the drift term.
\end{proposition}
`G` is the σ-algebra of the past, `Dt` the state at step `t` (`G`-measurable entrywise), and `x` the
fresh batch, i.i.d. with law `ν = dataTarget C` (`C = Id`) and independent of `G`. The regime holds
almost surely. `k ≥ k₀` is deterministic. The conclusion is the conditional expectation given `G`
of the next-step risk, with both conjuncts of the frozen helper transported almost surely. -/
theorem prop_app_sgd_iso_filtered :
    ∃ C₂ : ℝ, 0 ≤ C₂ ∧ ∀ K fMin Cdelta : ℝ, 1 ≤ K → 0 < fMin → 0 < Cdelta →
      ∃ Cr : ℝ, 0 ≤ Cr ∧ ∀ P : IsoParams, P.K = K → P.fMin = fMin → P.Cdelta = Cdelta →
        ∀ (Nout Nin B : ℕ) (η : ℝ), 0 ≤ η → isoK0 P ≤ (kOf Nout Nin B : ℝ) →
          ∀ (Ω : Type) [mΩ : MeasurableSpace Ω] (Pr : Measure Ω) [IsProbabilityMeasure Pr]
            (C : Covariances Nout Nin) (hSout : C.Sout = 1) (hSin : C.Sin = 1)
            (ν : Measure (Vec Nout × Vec Nin)) (hν : Muon.Setup.assum_data_target C ν)
            (x : Ω → Muon.Setup.Batch Nout Nin B) (hxm : Measurable x)
            (hid : Muon.Setup.IIDBatch Pr ν (fun a ω => x ω a))
            (G : MeasurableSpace Ω) (hG : G ≤ mΩ)
            (Dt : Ω → Matrix (Fin Nout) (Fin Nin) ℝ)
            (hDt : ∀ i j, Measurable[G] fun ω => Dt ω i j)
            (hind : ProbabilityTheory.Indep G (MeasurableSpace.comap x inferInstance) Pr)
            (hreg : ∀ᵐ ω ∂Pr, def_app_sgd_iso_regime P Nout Nin B (Dt ω)),
            (∀ᵐ ω ∂Pr,
              |condExp G Pr (fun w => Muon.Setup.riskSigma C
                  (def_app_sgd_update η (Dt w) (toSignBatch (x w)))) ω
                - (Muon.Setup.riskSigma C (Dt ω)
                    - η * batchConst B * Real.sqrt (4 * Muon.Setup.riskSigma C (Dt ω) / Real.pi)
                    + η ^ 2 / 2 * ((Nin : ℝ) * (Nout : ℝ)))|
              ≤ η * P.K * Real.sqrt (2 * Muon.Setup.riskSigma C (Dt ω))
                  * (C₂ + Cr / Real.sqrt (kOf Nout Nin B : ℝ)))
            ∧ (∀ᵐ ω ∂Pr,
              |condExp G Pr (fun w => Muon.Setup.riskSigma C
                  (def_app_sgd_update η (Dt w) (toSignBatch (x w)))) ω
                - (Muon.Setup.riskSigma C (Dt ω)
                    - η * batchConst B * Real.sqrt (4 * Muon.Setup.riskSigma C (Dt ω) / Real.pi)
                    + η ^ 2 / 2 * ((Nin : ℝ) * (Nout : ℝ)))|
              ≤ Real.pi * P.K * (C₂ + Cr)
                  / (2 * Real.sqrt (2 / Real.pi) * Real.sqrt (kOf Nout Nin B : ℝ))
                  * (η * batchConst B * Real.sqrt (4 * Muon.Setup.riskSigma C (Dt ω) / Real.pi))) := by
  obtain ⟨C₂, hC₂, hfro⟩ := prop_app_sgd_iso_frozen
  refine ⟨C₂, hC₂, ?_⟩
  intro K fMin Cdelta hK hfMin hCdelta
  obtain ⟨Cr, hCr, hfro⟩ := hfro K fMin Cdelta hK hfMin hCdelta
  refine ⟨Cr, hCr, ?_⟩
  intro P hPK hPf hPC Nout Nin B η hη hthreshold Ω mΩ Pr _ C hSout hSin ν hν x hxm hid
    G hG Dt hDt hind hreg
  have hDtG : Measurable[G] Dt := measurable_pi_iff.2 fun i => measurable_pi_iff.2 fun j => hDt i j
  -- `G` is a class-typed local and would otherwise be picked up as the ambient σ-algebra.
  letI : MeasurableSpace Ω := mΩ
  have hDtm : Measurable[mΩ] Dt := Measurable.mono hDtG hG le_rfl
  have hFm := iso_update_measurable (Nout := Nout) (B := B) C hSout hSin η
  have hbm : ∀ Δ : Matrix (Fin Nout) (Fin Nin) ℝ, Measurable (fun b : Muon.Setup.Batch Nout Nin B =>
      Muon.Setup.riskSigma C (def_app_sgd_update η Δ (toSignBatch b))) :=
    fun Δ => Measurable.of_uncurry_left (x := Δ) hFm
  have hfint : Integrable (fun ω => Muon.Setup.riskSigma C
      (def_app_sgd_update η (Dt ω) (toSignBatch (x ω)))) Pr := by
    have hmeas : Measurable[mΩ] (fun ω => Muon.Setup.riskSigma C
        (def_app_sgd_update η (Dt ω) (toSignBatch (x ω)))) :=
      iso_comp_measurable _ hFm hDtm hxm
    refine (integrable_const (P.fMax ^ 2 + η ^ 2 * ((Nin : ℝ) * (Nout : ℝ)))).mono'
      hmeas.aestronglyMeasurable ?_
    filter_upwards [hreg] with ω hω
    have h0 : 0 ≤ frobNorm (Dt ω) := Real.sqrt_nonneg _
    have hfr : frobNorm (Dt ω) ^ 2 ≤ P.fMax ^ 2 := by
      nlinarith [hω.2.2.2.2.1]
    have hb := iso_update_risk_bound C hSout hSin η (Dt ω) (x ω)
    have hnn : 0 ≤ Muon.Setup.riskSigma C (def_app_sgd_update η (Dt ω) (toSignBatch (x ω))) := by
      rw [iso_risk_eq_sum C hSout hSin]
      apply div_nonneg _ (by norm_num)
      exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => mul_self_nonneg _
    rw [Real.norm_eq_abs, abs_of_nonneg hnn]
    linarith [hb, hfr]
  have hcond := iso_freezing_condExp G hG hDtG hxm hind hFm hfint
  have hmapint : ∀ Δ : Matrix (Fin Nout) (Fin Nin) ℝ,
      ∫ y, Muon.Setup.riskSigma C (def_app_sgd_update η Δ (toSignBatch y)) ∂(Pr.map x)
        = ∫ ω', Muon.Setup.riskSigma C (def_app_sgd_update η Δ (toSignBatch (x ω'))) ∂Pr :=
    fun Δ => integral_map hxm.aemeasurable (hbm Δ).aestronglyMeasurable
  have key : ∀ᵐ ω ∂Pr, condExp G Pr (fun w => Muon.Setup.riskSigma C
      (def_app_sgd_update η (Dt w) (toSignBatch (x w)))) ω
        = ∫ ω', Muon.Setup.riskSigma C (def_app_sgd_update η (Dt ω) (toSignBatch (x ω'))) ∂Pr := by
    filter_upwards [hcond] with ω hω
    exact hω.trans (hmapint (Dt ω))
  refine ⟨?_, ?_⟩
  · filter_upwards [key, hreg] with ω hω hr
    obtain ⟨h1, _⟩ := hfro P hPK hPf hPC Nout Nin B η hη (Dt ω) hr hthreshold Ω Pr C hSout hSin
      ν hν (fun ω' => toSignBatch (x ω')) hid
    rw [hω]
    exact h1
  · filter_upwards [key, hreg] with ω hω hr
    obtain ⟨_, h2⟩ := hfro P hPK hPf hPC Nout Nin B η hη (Dt ω) hr hthreshold Ω Pr C hSout hSin
      ν hν (fun ω' => toSignBatch (x ω')) hid
    rw [hω]
    exact h2

end Muon.SignSGD
