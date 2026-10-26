import Muon.Setup.Basic
import Muon.SignSGD.Defs

/-!
# Appendix I (SignSGD): one-step risk and row identities

Interface for the unlabeled one-step facts of `sections/08-signsgd/section.tex` l. 56–68,
promoted to helper declarations (CARD §3b, WP L-I.2). Labels: `eqn:app-sgd-risk` and
`eqn:app-sgd-row`, each at a deterministic state with one fresh batch, and their Haar
versions ("given U, then average"). Source of record: snapshot `cr-2026-10-23`.

Reused, not redefined: the Σ-pairing `⟨·,·⟩_Σ` and risk `ℛ` (`Muon.Setup.pairSigma`,
`Muon.Setup.riskSigma`, `eqn:app-setup-pairing`), the row energy `𝒬_i` (`Muon.Setup.rowQ`), the
batch `Muon.SignSGD.Batch`, the gradient `Muon.SignSGD.physGrad` and the update
`Muon.SignSGD.def_app_sgd_update`. Here `Σ_in` is the general `Covariances` field; in §I.3–I.4 it
is `I` (the identities do not use this).

Conventions. `E_t` is the expectation over the fresh batch, `batchMean` is the entrywise mean of
`S` (`Matrix` carries no Bochner integral). The Haar measure is `Muon.Foundations.haarO`
(`O(n)`); the Haar statements are stated for an arbitrary probability measure `ν` on the
parameter space so they apply to it. In the Haar model only the whitened batch is independent of
`U`, while `X_out = UΛ^{1/2} z` (l. 626–628), so the Haar batch is a function `β u ω` of the
parameter and the sample point, with joint measurability. The state `Δ(u)`, covariance `C(u)`
and row vector are functions of `u`. Integrability and measurability hypotheses (bounded entries
and joint measurability) are formalization-side side conditions.
-/

open MeasureTheory ProbabilityTheory
open scoped Matrix MatrixOrder
open Matrix

namespace Muon.SignSGD

variable {m n : ℕ}

/-- The signed direction `S = sign(G°)` of `def:app-sgd-update` at the state `Δ` with batch `β`
(`Real.sign` entrywise, `Real.sign 0 = 0`). -/
noncomputable def signGrad {B : ℕ} (Δ : Mat m n) (β : Batch m n B) : Mat m n :=
  (physGrad Δ β).map Real.sign

/-- The update `def_app_sgd_update` is `Δ - η • S` with `S = signGrad Δ β`. -/
lemma def_app_sgd_update_eq_signGrad {B : ℕ} (η : ℝ) (Δ : Mat m n) (β : Batch m n B) :
    def_app_sgd_update η Δ β = Δ - η • signGrad Δ β := rfl

/-- Entrywise expectation `E_t S` of a random matrix (the `E_t S` of `eqn:app-sgd-risk`). -/
noncomputable def batchMean {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (S : Ω → Mat m n) : Mat m n :=
  Matrix.of fun i j => ∫ ω, S ω i j ∂P

/-- The Σ-pairing is symmetric (both covariances are symmetric). -/
lemma pairSigma_comm (C : Covariances m n) (V W : Mat m n) :
    Muon.Setup.pairSigma C V W = Muon.Setup.pairSigma C W V := by
  have hO : C.Soutᵀ = C.Sout := by
    have h := C.psdOut.isHermitian.eq
    rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at h
  have hI : C.Sinᵀ = C.Sin := by
    have h := C.psdIn.isHermitian.eq
    rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at h
  unfold Muon.Setup.pairSigma
  rw [← Matrix.trace_transpose (C.Sout * V * C.Sin * Wᵀ)]
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose, hO, hI]
  rw [show W * (C.Sin * (Vᵀ * C.Sout)) = (W * C.Sin * Vᵀ) * C.Sout by
        simp only [Matrix.mul_assoc]]
  rw [show C.Sout * W * C.Sin * Vᵀ = C.Sout * (W * C.Sin * Vᵀ) by
        simp only [Matrix.mul_assoc]]
  exact Matrix.trace_mul_comm _ _

/-- Bilinearity of the Σ-pairing in its first slot (private helper). -/
private lemma pairSigma_sub_left' (C : Covariances m n) (A B W : Mat m n) :
    Muon.Setup.pairSigma C (A - B) W = Muon.Setup.pairSigma C A W - Muon.Setup.pairSigma C B W := by
  unfold Muon.Setup.pairSigma
  simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.trace_sub]

/-- Bilinearity of the Σ-pairing in its second slot (private helper). -/
private lemma pairSigma_sub_right' (C : Covariances m n) (V A B : Mat m n) :
    Muon.Setup.pairSigma C V (A - B) = Muon.Setup.pairSigma C V A - Muon.Setup.pairSigma C V B := by
  unfold Muon.Setup.pairSigma
  simp only [Matrix.mul_sub, Matrix.trace_sub, Matrix.transpose_sub]

/-- Scalar pulls out of the Σ-pairing in its first slot (private helper). -/
private lemma pairSigma_smul_left' (C : Covariances m n) (c : ℝ) (V W : Mat m n) :
    Muon.Setup.pairSigma C (c • V) W = c * Muon.Setup.pairSigma C V W := by
  unfold Muon.Setup.pairSigma
  simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul]

/-- Scalar pulls out of the Σ-pairing in its second slot (private helper). -/
private lemma pairSigma_smul_right' (C : Covariances m n) (c : ℝ) (V W : Mat m n) :
    Muon.Setup.pairSigma C V (c • W) = c * Muon.Setup.pairSigma C V W := by
  unfold Muon.Setup.pairSigma
  simp only [Matrix.mul_smul, Matrix.transpose_smul, Matrix.trace_smul, smul_eq_mul]

/-- Pointwise risk expansion at a fixed pair `(Δ, S)`: the algebraic core of
`eqn:app-sgd-risk` before averaging over the batch. -/
lemma riskSigma_step (C : Covariances m n) (Δ S : Mat m n) (η : ℝ) :
    Muon.Setup.riskSigma C (Δ - η • S)
      = Muon.Setup.riskSigma C Δ - η * Muon.Setup.pairSigma C Δ S
        + η ^ 2 / 2 * Muon.Setup.pairSigma C S S := by
  unfold Muon.Setup.riskSigma
  have hc := pairSigma_comm C S Δ
  simp only [pairSigma_sub_left', pairSigma_sub_right', pairSigma_smul_left',
    pairSigma_smul_right', hc]
  ring

/-- Pointwise row expansion at a fixed pair `(Δ, S)` and a vector `u`: the algebraic core of
`eqn:app-sgd-row` before averaging over the batch. -/
lemma rowEnergy_step (Δ S : Mat m n) (u : Vec m) (η : ℝ) :
    ∑ k, ((Δ - η • S)ᵀ *ᵥ u) k ^ 2
      = ∑ k, (Δᵀ *ᵥ u) k ^ 2 - 2 * η * ((Δᵀ *ᵥ u) ⬝ᵥ (Sᵀ *ᵥ u))
        + η ^ 2 * ∑ k, (Sᵀ *ᵥ u) k ^ 2 := by
  have hv : (Δ - η • S)ᵀ *ᵥ u = Δᵀ *ᵥ u - η • (Sᵀ *ᵥ u) := by
    rw [Matrix.transpose_sub, Matrix.transpose_smul, Matrix.sub_mulVec, Matrix.smul_mulVec]
  rw [hv]
  have hk : ∀ k, (Δᵀ *ᵥ u - η • (Sᵀ *ᵥ u)) k ^ 2
      = (Δᵀ *ᵥ u) k ^ 2 - 2 * η * ((Δᵀ *ᵥ u) k * (Sᵀ *ᵥ u) k) + η ^ 2 * (Sᵀ *ᵥ u) k ^ 2 := by
    intro k
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  simp only [hk, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  unfold dotProduct
  ring

/-- `𝒬_i` of `eqn:app-setup-pairing` at the updated state, in terms of the Setup eigenvector
`u_i = S.u i`. Reuses `Muon.Setup.rowQ`. -/
lemma rowQ_step {C : Covariances m n} (S : Muon.Setup.SpectralData C) (Δ U : Mat m n)
    (i : Fin m) (η : ℝ) :
    Muon.Setup.rowQ S (Δ - η • U) i
      = Muon.Setup.rowQ S Δ i - 2 * η * ((Δᵀ *ᵥ S.u i) ⬝ᵥ (Uᵀ *ᵥ S.u i))
        + η ^ 2 * ∑ k, (Uᵀ *ᵥ S.u i) k ^ 2 := by
  unfold Muon.Setup.rowQ
  exact rowEnergy_step Δ U (S.u i) η

/-! ### Private helpers for the fixed-state identities (P-I.2.P2) -/

private lemma sgdRealSign_measurable : Measurable Real.sign := by
  unfold Real.sign
  exact Measurable.ite (measurableSet_lt measurable_id measurable_const) measurable_const
    (Measurable.ite (measurableSet_lt measurable_const measurable_id) measurable_const
      measurable_const)

private lemma sgdRealSign_abs_le (x : ℝ) : |Real.sign x| ≤ 1 := by
  rcases Real.sign_apply_eq x with h | h | h <;> simp [h]

private lemma pairSigma_add_left' (C : Covariances m n) (A B W : Mat m n) :
    Muon.Setup.pairSigma C (A + B) W = Muon.Setup.pairSigma C A W + Muon.Setup.pairSigma C B W := by
  unfold Muon.Setup.pairSigma
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.trace_add]

private lemma pairSigma_add_right' (C : Covariances m n) (V A B : Mat m n) :
    Muon.Setup.pairSigma C V (A + B) = Muon.Setup.pairSigma C V A + Muon.Setup.pairSigma C V B := by
  unfold Muon.Setup.pairSigma
  simp only [Matrix.transpose_add, Matrix.mul_add, Matrix.trace_add]

/-- A linear functional on matrices is a finite sum over the matrix units. -/
private lemma sgdLinDecomp {L : Mat m n → ℝ}
    (hadd : ∀ V W, L (V + W) = L V + L W) (hsmul : ∀ (c : ℝ) (V : Mat m n), L (c • V) = c * L V)
    (V : Mat m n) :
    L V = ∑ i, ∑ j, V i j * L (Matrix.single i j 1) := by
  have hzero : L 0 = 0 := by
    have h := hsmul 0 0
    simpa using h
  let F : Mat m n →+ ℝ := { toFun := L, map_zero' := hzero, map_add' := hadd }
  have hV : V = ∑ i, ∑ j, V i j • (Matrix.single i j (1 : ℝ) : Mat m n) := by
    conv_lhs => rw [Matrix.matrix_eq_sum_single V]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [Matrix.smul_single, smul_eq_mul, mul_one]
  have key : F (∑ i, ∑ j, V i j • (Matrix.single i j (1 : ℝ) : Mat m n))
      = ∑ i, ∑ j, V i j * L (Matrix.single i j 1) := by
    simp only [map_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => hsmul _ _
  calc L V = F V := rfl
    _ = F (∑ i, ∑ j, V i j • (Matrix.single i j (1 : ℝ) : Mat m n)) := by rw [← hV]
    _ = ∑ i, ∑ j, V i j * L (Matrix.single i j 1) := key

/-- Integrability of a linear functional of a random matrix, and the entrywise mean rule. -/
private lemma sgdIntLinear {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {L : Mat m n → ℝ} (hadd : ∀ V W, L (V + W) = L V + L W)
    (hsmul : ∀ (c : ℝ) (V : Mat m n), L (c • V) = c * L V)
    (S : Ω → Mat m n) (hS : ∀ i j, Integrable (fun ω => S ω i j) P) :
    Integrable (fun ω => L (S ω)) P ∧ ∫ ω, L (S ω) ∂P = L (batchMean P S) := by
  have h1 : ∀ ω, L (S ω) = ∑ i, ∑ j, S ω i j * L (Matrix.single i j 1) :=
    fun ω => sgdLinDecomp hadd hsmul (S ω)
  have hi : ∀ i, Integrable (fun ω => ∑ j, S ω i j * L (Matrix.single i j 1)) P :=
    fun i => integrable_finsetSum _ fun j _ => (hS i j).mul_const _
  have hL : L (batchMean P S) = ∑ i, ∑ j, (∫ ω, S ω i j ∂P) * L (Matrix.single i j 1) :=
    sgdLinDecomp hadd hsmul (batchMean P S)
  have hfun : (fun ω => L (S ω)) = fun ω => ∑ i, ∑ j, S ω i j * L (Matrix.single i j 1) :=
    funext h1
  refine ⟨by rw [hfun]; exact integrable_finsetSum _ fun i _ => hi i, ?_⟩
  rw [hfun, hL, integral_finsetSum _ fun i _ => hi i]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_finsetSum _ fun j _ => (hS i j).mul_const _]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [integral_mul_const]

/-- The Σ-pairing is bilinear: a finite sum over matrix units in both slots. -/
private lemma sgdPairBilin (C : Covariances m n) (V W : Mat m n) :
    Muon.Setup.pairSigma C V W = ∑ k, ∑ l, W k l * ∑ i, ∑ j, V i j *
      Muon.Setup.pairSigma C (Matrix.single i j 1) (Matrix.single k l 1) := by
  refine (sgdLinDecomp (L := Muon.Setup.pairSigma C V) (fun A B => pairSigma_add_right' C V A B)
    (fun c A => pairSigma_smul_right' C c V A) W).trans ?_
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  have hV := sgdLinDecomp (L := fun V' => Muon.Setup.pairSigma C V' (Matrix.single k l 1))
    (fun A B => pairSigma_add_left' C A B _) (fun c A => pairSigma_smul_left' C c A _) V
  rw [hV]

/-- Entrywise products of bounded random entries are integrable. -/
private lemma sgdEntryProd_integrable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (S : Ω → Mat m n)
    (hm : ∀ i j, Measurable fun ω => S ω i j) (hb : ∀ ω i j, |S ω i j| ≤ 1) (i : Fin m)
    (j : Fin n) (k : Fin m) (l : Fin n) :
    Integrable (fun ω => S ω i j * S ω k l) P := by
  refine Integrable.of_bound ((hm i j).mul (hm k l)).aestronglyMeasurable 1
    (Filter.Eventually.of_forall fun ω => ?_)
  rw [Real.norm_eq_abs, abs_mul]
  calc |S ω i j| * |S ω k l| ≤ 1 * 1 := mul_le_mul (hb ω i j) (hb ω k l) (abs_nonneg _) zero_le_one
    _ = 1 := one_mul 1

/-- Integrability of the Σ-pairing of a random matrix with itself. -/
private lemma sgdPairQuad_integrable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (C : Covariances m n) (S : Ω → Mat m n)
    (hm : ∀ i j, Measurable fun ω => S ω i j) (hb : ∀ ω i j, |S ω i j| ≤ 1) :
    Integrable (fun ω => Muon.Setup.pairSigma C (S ω) (S ω)) P := by
  have hq : ∀ ω, Muon.Setup.pairSigma C (S ω) (S ω) = ∑ k, ∑ l, ∑ i, ∑ j,
      (S ω k l * S ω i j) * Muon.Setup.pairSigma C (Matrix.single i j 1) (Matrix.single k l 1) := by
    intro ω
    rw [sgdPairBilin C (S ω) (S ω)]
    simp only [Finset.mul_sum, mul_assoc]
  have hfun : (fun ω => Muon.Setup.pairSigma C (S ω) (S ω)) = fun ω => ∑ k, ∑ l, ∑ i, ∑ j,
      (S ω k l * S ω i j) * Muon.Setup.pairSigma C (Matrix.single i j 1) (Matrix.single k l 1) :=
    funext hq
  rw [hfun]
  exact integrable_finsetSum _ fun k _ => integrable_finsetSum _ fun l _ =>
    integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
      (sgdEntryProd_integrable P S hm hb k l i j).mul_const _

/-- Integrability of `‖Sᵀ u‖²` for a random matrix with bounded entries. -/
private lemma sgdRowQuad_integrable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (S : Ω → Mat m n) (u : Vec m)
    (hm : ∀ i j, Measurable fun ω => S ω i j) (hb : ∀ ω i j, |S ω i j| ≤ 1) :
    Integrable (fun ω => ∑ k, ((S ω)ᵀ *ᵥ u) k ^ 2) P := by
  have hr : ∀ ω, ∑ k, ((S ω)ᵀ *ᵥ u) k ^ 2
      = ∑ k, ∑ i, ∑ j, (S ω i k * S ω j k) * (u i * u j) := by
    intro ω
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply]
    rw [sq, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  have hfun : (fun ω => ∑ k, ((S ω)ᵀ *ᵥ u) k ^ 2)
      = fun ω => ∑ k, ∑ i, ∑ j, (S ω i k * S ω j k) * (u i * u j) := funext hr
  rw [hfun]
  exact integrable_finsetSum _ fun k _ => integrable_finsetSum _ fun i _ =>
    integrable_finsetSum _ fun j _ =>
      (sgdEntryProd_integrable P S hm hb i k j k).mul_const _

private lemma sgdPhysGrad_measurable {Ω : Type*} [MeasurableSpace Ω] {B : ℕ} (Δ : Mat m n)
    (β : Ω → Batch m n B) (hx : ∀ a k, Measurable fun ω => (β ω).xin a k)
    (hy : ∀ a k, Measurable fun ω => (β ω).xout a k) (i : Fin m) (j : Fin n) :
    Measurable fun ω => physGrad Δ (β ω) i j := by
  simp only [physGrad, residual, Matrix.mulVec, dotProduct]
  refine Measurable.const_mul ?_ _
  refine Finset.measurable_sum _ fun a _ => ?_
  refine Measurable.mul ?_ ((hy a i).mul (hx a j))
  refine Finset.measurable_sum _ fun l _ => ?_
  refine (hy a l).mul ?_
  refine Finset.measurable_sum _ fun k _ => ?_
  exact measurable_const.mul (hx a k)

private lemma sgdSignEntry_measurable {Ω : Type*} [MeasurableSpace Ω] {B : ℕ} (Δ : Mat m n)
    (β : Ω → Batch m n B) (hx : ∀ a k, Measurable fun ω => (β ω).xin a k)
    (hy : ∀ a k, Measurable fun ω => (β ω).xout a k) (i : Fin m) (j : Fin n) :
    Measurable fun ω => signGrad Δ (β ω) i j :=
  sgdRealSign_measurable.comp (sgdPhysGrad_measurable Δ β hx hy i j)

private lemma sgdSignEntry_bound {B : ℕ} (Δ : Mat m n) (b : Batch m n B) (i : Fin m) (j : Fin n) :
    |signGrad Δ b i j| ≤ 1 :=
  sgdRealSign_abs_le _

private lemma sgdSignEntry_integrable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {B : ℕ} (Δ : Mat m n) (β : Ω → Batch m n B)
    (hx : ∀ a k, Measurable fun ω => (β ω).xin a k)
    (hy : ∀ a k, Measurable fun ω => (β ω).xout a k) (i : Fin m) (j : Fin n) :
    Integrable (fun ω => signGrad Δ (β ω) i j) P :=
  Integrable.of_bound (sgdSignEntry_measurable Δ β hx hy i j).aestronglyMeasurable 1
    (Filter.Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs]; exact sgdSignEntry_bound Δ (β ω) i j)

/-- **eqn:app-sgd-risk** at a deterministic state, one fresh batch.
Declaration of record for the risk line of `eqn:app-sgd-risk`
(the fixed-state identity; the Haar version is `oneStep_risk_haar`).

cr-2026-10-23. LaTeX statement (verbatim):
\EE_t\big[\cR(t+1)\big]&=\cR(t)-\lr\big\langle\Dt,\EE_tS\big\rangle_\Sigma+\frac{\lr^2}2\,\EE_t\norm S_\Sigma^2,\label{eqn:app-sgd-risk}\\ -/
theorem eqn_app_sgd_risk {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (C : Covariances m n) {B : ℕ} (Δ : Mat m n) (η : ℝ)
    (hη : 0 ≤ η) (β : Ω → Batch m n B)
    (hx : ∀ a k, Measurable fun ω => (β ω).xin a k)
    (hy : ∀ a k, Measurable fun ω => (β ω).xout a k) :
    ∫ ω, Muon.Setup.riskSigma C (def_app_sgd_update η Δ (β ω)) ∂P
      = Muon.Setup.riskSigma C Δ
        - η * Muon.Setup.pairSigma C Δ (batchMean P fun ω => signGrad Δ (β ω))
        + η ^ 2 / 2 * ∫ ω, Muon.Setup.pairSigma C (signGrad Δ (β ω)) (signGrad Δ (β ω)) ∂P := by
  have hm : ∀ i j, Measurable fun ω => signGrad Δ (β ω) i j :=
    fun i j => sgdSignEntry_measurable Δ β hx hy i j
  have hb : ∀ ω i j, |signGrad Δ (β ω) i j| ≤ 1 :=
    fun ω i j => sgdSignEntry_bound Δ (β ω) i j
  have hS : ∀ i j, Integrable (fun ω => signGrad Δ (β ω) i j) P :=
    fun i j => sgdSignEntry_integrable P Δ β hx hy i j
  have hpt : ∀ ω, Muon.Setup.riskSigma C (def_app_sgd_update η Δ (β ω))
      = Muon.Setup.riskSigma C Δ - η * Muon.Setup.pairSigma C Δ (signGrad Δ (β ω))
        + η ^ 2 / 2 * Muon.Setup.pairSigma C (signGrad Δ (β ω)) (signGrad Δ (β ω)) :=
    fun ω => riskSigma_step C Δ (signGrad Δ (β ω)) η
  have hL := sgdIntLinear P (L := Muon.Setup.pairSigma C Δ)
    (fun A B => pairSigma_add_right' C Δ A B) (fun c A => pairSigma_smul_right' C c Δ A)
    (fun ω => signGrad Δ (β ω)) hS
  have hQ := sgdPairQuad_integrable P C (fun ω => signGrad Δ (β ω)) hm hb
  have hA : Integrable (fun ω => Muon.Setup.riskSigma C Δ
      - η * Muon.Setup.pairSigma C Δ (signGrad Δ (β ω))) P :=
    (integrable_const _).sub (hL.1.const_mul η)
  have hB : Integrable (fun ω => η ^ 2 / 2 *
      Muon.Setup.pairSigma C (signGrad Δ (β ω)) (signGrad Δ (β ω))) P :=
    hQ.const_mul _
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt), integral_add hA hB,
    integral_sub (integrable_const _) (hL.1.const_mul η), integral_const, integral_const_mul,
    integral_const_mul, hL.2]
  simp

/-- **eqn:app-sgd-row** at a deterministic state, one fresh batch, for a row vector `u`
(`u = u_i`; the Setup form is `rowQ_step`).

cr-2026-10-23. LaTeX statement (verbatim):
\EE_t\big[\CMscr Q_i(\Delta_{t+1})\big]&=\CMscr Q_i(\Dt)-2\lr\,\EE_t\big\langle\Dt^\T u_i,S^\T u_i\big\rangle+\lr^2\,\EE_t\norm{S^\T u_i}^2.\label{eqn:app-sgd-row} -/
theorem eqn_app_sgd_row {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {B : ℕ} (Δ : Mat m n) (u : Vec m) (η : ℝ)
    (hη : 0 ≤ η) (β : Ω → Batch m n B)
    (hx : ∀ a k, Measurable fun ω => (β ω).xin a k)
    (hy : ∀ a k, Measurable fun ω => (β ω).xout a k) :
    ∫ ω, ∑ k, ((def_app_sgd_update η Δ (β ω))ᵀ *ᵥ u) k ^ 2 ∂P
      = ∑ k, (Δᵀ *ᵥ u) k ^ 2
        - 2 * η * ∫ ω, ((Δᵀ *ᵥ u) ⬝ᵥ ((signGrad Δ (β ω))ᵀ *ᵥ u)) ∂P
        + η ^ 2 * ∫ ω, ∑ k, ((signGrad Δ (β ω))ᵀ *ᵥ u) k ^ 2 ∂P := by
  have hm : ∀ i j, Measurable fun ω => signGrad Δ (β ω) i j :=
    fun i j => sgdSignEntry_measurable Δ β hx hy i j
  have hb : ∀ ω i j, |signGrad Δ (β ω) i j| ≤ 1 :=
    fun ω i j => sgdSignEntry_bound Δ (β ω) i j
  have hS : ∀ i j, Integrable (fun ω => signGrad Δ (β ω) i j) P :=
    fun i j => sgdSignEntry_integrable P Δ β hx hy i j
  have hG := sgdIntLinear P (L := fun V => (Δᵀ *ᵥ u) ⬝ᵥ (Vᵀ *ᵥ u))
    (by intro A B; simp only [Matrix.transpose_add, Matrix.add_mulVec, dotProduct_add])
    (by intro c A; simp only [Matrix.transpose_smul, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul])
    (fun ω => signGrad Δ (β ω)) hS
  have hH := sgdRowQuad_integrable P (fun ω => signGrad Δ (β ω)) u hm hb
  have hpt : ∀ ω, ∑ k, ((def_app_sgd_update η Δ (β ω))ᵀ *ᵥ u) k ^ 2
      = (∑ k, (Δᵀ *ᵥ u) k ^ 2) - 2 * η * ((Δᵀ *ᵥ u) ⬝ᵥ ((signGrad Δ (β ω))ᵀ *ᵥ u))
        + η ^ 2 * ∑ k, ((signGrad Δ (β ω))ᵀ *ᵥ u) k ^ 2 :=
    fun ω => rowEnergy_step Δ (signGrad Δ (β ω)) u η
  have hA : Integrable (fun ω => (∑ k, (Δᵀ *ᵥ u) k ^ 2)
      - 2 * η * ((Δᵀ *ᵥ u) ⬝ᵥ ((signGrad Δ (β ω))ᵀ *ᵥ u))) P :=
    (integrable_const _).sub (hG.1.const_mul (2 * η))
  have hB : Integrable (fun ω => η ^ 2 * ∑ k, ((signGrad Δ (β ω))ᵀ *ᵥ u) k ^ 2) P :=
    hH.const_mul _
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt), integral_add hA hB,
    integral_sub (integrable_const _) (hG.1.const_mul (2 * η)), integral_const,
    integral_const_mul, integral_const_mul]
  simp

/-! ### Helpers for the Haar identities (P-I.2.P3) -/

private lemma sgd_abs_sum_le {ι : Type*} [Fintype ι] (f : ι → ℝ) (M : ℝ)
    (h : ∀ i, |f i| ≤ M) : |∑ i, f i| ≤ (Fintype.card ι : ℝ) * M := by
  calc |∑ i, f i| ≤ ∑ i, |f i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : ι, M := Finset.sum_le_sum fun i _ => h i
    _ = (Fintype.card ι : ℝ) * M := by simp

private lemma sgd_mul_entry_bound {I J K : Type*} [Fintype J] (A : Matrix I J ℝ)
    (B : Matrix J K ℝ) (KA KB : ℝ) (hA : ∀ i j, |A i j| ≤ KA) (hB : ∀ j k, |B j k| ≤ KB)
    (hKA : 0 ≤ KA) (i : I) (k : K) : |(A * B) i k| ≤ (Fintype.card J : ℝ) * (KA * KB) := by
  rw [Matrix.mul_apply]
  refine sgd_abs_sum_le _ _ fun j => ?_
  rw [abs_mul]
  exact mul_le_mul (hA i j) (hB j k) (abs_nonneg _) hKA

private lemma sgd_pairSigma_abs_le (C : Covariances m n) (V W : Mat m n)
    (Ko Ki Kv Kw : ℝ) (hKo : 0 ≤ Ko) (hKi : 0 ≤ Ki) (hKv : 0 ≤ Kv)
    (hCo : ∀ i j, |C.Sout i j| ≤ Ko) (hCi : ∀ i j, |C.Sin i j| ≤ Ki)
    (hV : ∀ i j, |V i j| ≤ Kv) (hW : ∀ i j, |W i j| ≤ Kw) :
    |Muon.Setup.pairSigma C V W| ≤ (Fintype.card (Fin m) : ℝ) *
      ((Fintype.card (Fin n) : ℝ) * (((Fintype.card (Fin n) : ℝ) *
        ((Fintype.card (Fin m) : ℝ) * (Ko * Kv) * Ki)) * Kw)) := by
  have hZ : ∀ p s, |(C.Sout * V * C.Sin) p s| ≤ (Fintype.card (Fin n) : ℝ) *
      ((Fintype.card (Fin m) : ℝ) * (Ko * Kv) * Ki) := by
    intro p s
    have h1 : ∀ i k, |(C.Sout * V) i k| ≤ (Fintype.card (Fin m) : ℝ) * (Ko * Kv) :=
      fun i k => sgd_mul_entry_bound C.Sout V Ko Kv hCo hV hKo i k
    exact sgd_mul_entry_bound (C.Sout * V) C.Sin ((Fintype.card (Fin m) : ℝ) * (Ko * Kv)) Ki
      h1 hCi (mul_nonneg (Nat.cast_nonneg _) (mul_nonneg hKo hKv)) p s
  have hzn : 0 ≤ (Fintype.card (Fin n) : ℝ) * ((Fintype.card (Fin m) : ℝ) * (Ko * Kv) * Ki) :=
    mul_nonneg (Nat.cast_nonneg _)
      (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (mul_nonneg hKo hKv)) hKi)
  have key : ∀ Z : Mat m n, (Z * Wᵀ).trace = ∑ p, ∑ s, Z p s * W p s := by
    intro Z
    simp [Matrix.trace, Matrix.diag, Matrix.mul_apply]
  have htr : Muon.Setup.pairSigma C V W = ∑ p, ∑ s, (C.Sout * V * C.Sin) p s * W p s :=
    key _
  have hrow : ∀ p, |∑ s, (C.Sout * V * C.Sin) p s * W p s| ≤ (Fintype.card (Fin n) : ℝ) *
      ((Fintype.card (Fin n) : ℝ) * ((Fintype.card (Fin m) : ℝ) * (Ko * Kv) * Ki) * Kw) :=
    fun p => sgd_abs_sum_le _ _ fun s => by
      rw [abs_mul]; exact mul_le_mul (hZ p s) (hW p s) (abs_nonneg _) hzn
  rw [htr]
  exact sgd_abs_sum_le _ _ hrow

private lemma sgd_risk_bound (C : Covariances m n) (X : Mat m n) (Ko Ki KX : ℝ)
    (hKo : 0 ≤ Ko) (hKi : 0 ≤ Ki) (hKX : 0 ≤ KX) (hCo : ∀ i j, |C.Sout i j| ≤ Ko)
    (hCi : ∀ i j, |C.Sin i j| ≤ Ki) (hX : ∀ i j, |X i j| ≤ KX) :
    |Muon.Setup.riskSigma C X| ≤ (Fintype.card (Fin m) : ℝ) * ((Fintype.card (Fin n) : ℝ) *
      (((Fintype.card (Fin n) : ℝ) * ((Fintype.card (Fin m) : ℝ) * (Ko * KX) * Ki)) * KX)) / 2 := by
  unfold Muon.Setup.riskSigma
  rw [abs_div, abs_two]
  have h := sgd_pairSigma_abs_le C X X Ko Ki KX KX hKo hKi hKX hCo hCi hX hX
  linarith

private lemma sgd_pairSigma_measurable {Ω : Type*} [MeasurableSpace Ω] (Cp : Ω → Covariances m n)
    (V W : Ω → Mat m n)
    (hA : ∀ i j, Measurable fun ω => (Cp ω).Sout i j)
    (hB : ∀ i j, Measurable fun ω => (Cp ω).Sin i j)
    (hV : ∀ i j, Measurable fun ω => V ω i j) (hW : ∀ i j, Measurable fun ω => W ω i j) :
    Measurable fun ω => Muon.Setup.pairSigma (Cp ω) (V ω) (W ω) := by
  have hZm : ∀ p s, Measurable fun ω => ((Cp ω).Sout * V ω * (Cp ω).Sin) p s := by
    intro p s
    simp only [Matrix.mul_apply]
    refine Finset.measurable_sum _ fun r _ => ?_
    refine Measurable.mul (Finset.measurable_sum _ fun q _ => ?_) (hB r s)
    exact Measurable.mul (hA p q) (hV q r)
  have htr : ∀ ω, Muon.Setup.pairSigma (Cp ω) (V ω) (W ω)
      = ∑ p, ∑ s, ((Cp ω).Sout * V ω * (Cp ω).Sin) p s * W ω p s := by
    intro ω
    have key : ∀ Z : Mat m n, (Z * (W ω)ᵀ).trace = ∑ p, ∑ s, Z p s * W ω p s := by
      intro Z
      simp [Matrix.trace, Matrix.diag, Matrix.mul_apply]
    exact key _
  simp only [htr]
  exact Finset.measurable_sum _ fun p _ => Finset.measurable_sum _ fun s _ =>
    (hZm p s).mul (hW p s)

private lemma sgdPhysGrad_measurable' {α Ω : Type*} [MeasurableSpace α] [MeasurableSpace Ω]
    {B : ℕ} (Δ : α → Mat m n) (β : α → Ω → Batch m n B)
    (hΔ : ∀ i j, Measurable fun p : α × Ω => Δ p.1 i j)
    (hx : ∀ a k, Measurable fun p : α × Ω => (β p.1 p.2).xin a k)
    (hy : ∀ a k, Measurable fun p : α × Ω => (β p.1 p.2).xout a k) (i : Fin m) (j : Fin n) :
    Measurable fun p : α × Ω => physGrad (Δ p.1) (β p.1 p.2) i j := by
  simp only [physGrad, residual, Matrix.mulVec, dotProduct]
  refine Measurable.const_mul ?_ _
  refine Finset.measurable_sum _ fun a _ => ?_
  refine Measurable.mul ?_ ((hy a i).mul (hx a j))
  refine Finset.measurable_sum _ fun l _ => ?_
  refine (hy a l).mul ?_
  refine Finset.measurable_sum _ fun k _ => ?_
  exact (hΔ l k).mul (hx a k)

private lemma sgdUpd_measurable {α Ω : Type*} [MeasurableSpace α] [MeasurableSpace Ω] {B : ℕ}
    (η : ℝ) (Δ : α → Mat m n) (β : α → Ω → Batch m n B)
    (hΔ : ∀ i j, Measurable fun p : α × Ω => Δ p.1 i j)
    (hx : ∀ a k, Measurable fun p : α × Ω => (β p.1 p.2).xin a k)
    (hy : ∀ a k, Measurable fun p : α × Ω => (β p.1 p.2).xout a k) (i : Fin m) (j : Fin n) :
    Measurable fun p : α × Ω => def_app_sgd_update η (Δ p.1) (β p.1 p.2) i j := by
  simp only [def_app_sgd_update, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
    Matrix.map_apply]
  exact (hΔ i j).sub (measurable_const.mul
    (sgdRealSign_measurable.comp (sgdPhysGrad_measurable' Δ β hΔ hx hy i j)))

private lemma sgdUpd_abs_le {B : ℕ} (η : ℝ) (hη : 0 ≤ η) (Δ : Mat m n) (b : Batch m n B)
    (K : ℝ) (hΔ : ∀ i j, |Δ i j| ≤ K) (i : Fin m) (j : Fin n) :
    |def_app_sgd_update η Δ b i j| ≤ K + η := by
  simp only [def_app_sgd_update, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
    Matrix.map_apply]
  have h1 : |Δ i j - η * Real.sign (physGrad Δ b i j)|
      ≤ |Δ i j| + |η * Real.sign (physGrad Δ b i j)| := by
    have := abs_add_le (Δ i j) (-(η * Real.sign (physGrad Δ b i j)))
    rwa [abs_neg, ← sub_eq_add_neg] at this
  have h2 : |η * Real.sign (physGrad Δ b i j)| ≤ η := by
    rw [abs_mul, abs_of_nonneg hη]
    exact mul_le_of_le_one_right hη (sgdRealSign_abs_le _)
  linarith [hΔ i j]

private lemma sgd_mulVec_abs_le {M : Mat m n} {v : Vec m} {KM Kv : ℝ} (hKM : 0 ≤ KM)
    (hM : ∀ i j, |M i j| ≤ KM) (hv : ∀ i, |v i| ≤ Kv) (k : Fin n) :
    |(Mᵀ *ᵥ v) k| ≤ (Fintype.card (Fin m) : ℝ) * (KM * Kv) := by
  simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply]
  refine sgd_abs_sum_le _ _ fun i => ?_
  rw [abs_mul]
  exact mul_le_mul (hM i k) (hv i) (abs_nonneg _) hKM

private lemma sgd_row_quad_abs_le {M : Mat m n} {v : Vec m} {KM Kv : ℝ} (hKM : 0 ≤ KM)
    (hM : ∀ i j, |M i j| ≤ KM) (hv : ∀ i, |v i| ≤ Kv) :
    |∑ k, (Mᵀ *ᵥ v) k ^ 2| ≤ (Fintype.card (Fin n) : ℝ) *
      ((Fintype.card (Fin m) : ℝ) * (KM * Kv)) ^ 2 := by
  refine sgd_abs_sum_le _ _ fun k => ?_
  rw [abs_of_nonneg (sq_nonneg _)]
  have h := abs_le.mp (sgd_mulVec_abs_le hKM hM hv k)
  exact sq_le_sq' h.1 h.2

private lemma sgd_integrable_of_bound {X : Type*} [MeasurableSpace X] (μ : Measure X)
    [IsFiniteMeasure μ] (f : X → ℝ) (hf : Measurable f) (hb : ∃ M : ℝ, ∀ x, |f x| ≤ M) :
    Integrable f μ := by
  obtain ⟨M, hM⟩ := hb
  exact Integrable.of_bound hf.aestronglyMeasurable M
    (Filter.Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hM x)

private lemma sgd_risk_integrable {α Ω : Type*} [MeasurableSpace α] [MeasurableSpace Ω]
    (ν : Measure α) [IsProbabilityMeasure ν] (P : Measure Ω) [IsProbabilityMeasure P]
    (C : α → Covariances m n) (Δ : α → Mat m n) (η : ℝ) (hη : 0 ≤ η)
    {B : ℕ} (β : α → Ω → Batch m n B)
    (hx : ∀ a k, Measurable fun p : α × Ω => (β p.1 p.2).xin a k)
    (hy : ∀ a k, Measurable fun p : α × Ω => (β p.1 p.2).xout a k)
    (hΔm : ∀ i j, Measurable fun u => Δ u i j)
    (hCo : ∀ i j, Measurable fun u => (C u).Sout i j)
    (hCi : ∀ i j : Fin n, Measurable fun u => (C u).Sin i j)
    (hΔb : ∃ K : ℝ, ∀ u i j, |Δ u i j| ≤ K)
    (hCb : ∃ K : ℝ, ∀ u : α, ∀ i j : Fin m, |(C u).Sout i j| ≤ K)
    (hCib : ∃ K : ℝ, ∀ u : α, ∀ i j : Fin n, |(C u).Sin i j| ≤ K) :
    Integrable (fun p : α × Ω =>
      Muon.Setup.riskSigma (C p.1) (def_app_sgd_update η (Δ p.1) (β p.1 p.2))) (ν.prod P) := by
  obtain ⟨KΔ, hKΔ⟩ := hΔb
  obtain ⟨Ko, hKo⟩ := hCb
  obtain ⟨Ki, hKi⟩ := hCib
  have hΔ' : ∀ u i j, |Δ u i j| ≤ max KΔ 0 := fun u i j => (hKΔ u i j).trans (le_max_left _ _)
  have hKo' : ∀ u i j, |(C u).Sout i j| ≤ max Ko 0 :=
    fun u i j => (hKo u i j).trans (le_max_left _ _)
  have hKi' : ∀ u i j, |(C u).Sin i j| ≤ max Ki 0 :=
    fun u i j => (hKi u i j).trans (le_max_left _ _)
  have hYb : ∀ p : α × Ω, ∀ i j,
      |def_app_sgd_update η (Δ p.1) (β p.1 p.2) i j| ≤ max KΔ 0 + η :=
    fun p i j => sgdUpd_abs_le η hη (Δ p.1) (β p.1 p.2) (max KΔ 0) (hΔ' p.1) i j
  have hYm : ∀ i j, Measurable fun p : α × Ω => def_app_sgd_update η (Δ p.1) (β p.1 p.2) i j :=
    sgdUpd_measurable η Δ β (fun i j => (hΔm i j).comp measurable_fst) hx hy
  have hmeas : Measurable fun p : α × Ω =>
      Muon.Setup.riskSigma (C p.1) (def_app_sgd_update η (Δ p.1) (β p.1 p.2)) := by
    have h1 : Measurable fun p : α × Ω =>
        Muon.Setup.pairSigma (C p.1) (def_app_sgd_update η (Δ p.1) (β p.1 p.2))
          (def_app_sgd_update η (Δ p.1) (β p.1 p.2)) :=
      sgd_pairSigma_measurable (Ω := α × Ω) (fun p => C p.1)
        (fun p => def_app_sgd_update η (Δ p.1) (β p.1 p.2))
        (fun p => def_app_sgd_update η (Δ p.1) (β p.1 p.2))
        (fun i j => (hCo i j).comp measurable_fst) (fun i j => (hCi i j).comp measurable_fst)
        hYm hYm
    exact h1.div_const 2
  have hbd : ∀ p : α × Ω, |Muon.Setup.riskSigma (C p.1)
      (def_app_sgd_update η (Δ p.1) (β p.1 p.2))| ≤ (Fintype.card (Fin m) : ℝ) *
      ((Fintype.card (Fin n) : ℝ) * (((Fintype.card (Fin n) : ℝ) *
        ((Fintype.card (Fin m) : ℝ) * (max Ko 0 * (max KΔ 0 + η)) * max Ki 0)) *
          (max KΔ 0 + η))) / 2 :=
    fun p => sgd_risk_bound (C p.1) _ (max Ko 0) (max Ki 0) (max KΔ 0 + η) (le_max_right _ _)
      (le_max_right _ _) (add_nonneg (le_max_right _ _) hη) (hKo' p.1) (hKi' p.1) (hYb p)
  exact sgd_integrable_of_bound _ _ hmeas ⟨_, hbd⟩

private lemma sgd_row_integrable {α Ω : Type*} [MeasurableSpace α] [MeasurableSpace Ω]
    (ν : Measure α) [IsProbabilityMeasure ν] (P : Measure Ω) [IsProbabilityMeasure P]
    (Δ : α → Mat m n) (vec : α → Vec m) (η : ℝ) (hη : 0 ≤ η)
    {B : ℕ} (β : α → Ω → Batch m n B)
    (hx : ∀ a k, Measurable fun p : α × Ω => (β p.1 p.2).xin a k)
    (hy : ∀ a k, Measurable fun p : α × Ω => (β p.1 p.2).xout a k)
    (hΔm : ∀ i j, Measurable fun u => Δ u i j)
    (hvm : ∀ k, Measurable fun u => vec u k)
    (hΔb : ∃ K : ℝ, ∀ u i j, |Δ u i j| ≤ K)
    (hvb : ∃ K : ℝ, ∀ u k, |vec u k| ≤ K) :
    Integrable (fun p : α × Ω =>
      ∑ k, ((def_app_sgd_update η (Δ p.1) (β p.1 p.2))ᵀ *ᵥ vec p.1) k ^ 2) (ν.prod P) := by
  obtain ⟨KΔ, hKΔ⟩ := hΔb
  obtain ⟨Kv, hKv⟩ := hvb
  have hΔ' : ∀ u i j, |Δ u i j| ≤ max KΔ 0 := fun u i j => (hKΔ u i j).trans (le_max_left _ _)
  have hv' : ∀ u k, |vec u k| ≤ max Kv 0 := fun u k => (hKv u k).trans (le_max_left _ _)
  have hYb : ∀ p : α × Ω, ∀ i j,
      |def_app_sgd_update η (Δ p.1) (β p.1 p.2) i j| ≤ max KΔ 0 + η :=
    fun p i j => sgdUpd_abs_le η hη (Δ p.1) (β p.1 p.2) (max KΔ 0) (hΔ' p.1) i j
  have hYm : ∀ i j, Measurable fun p : α × Ω => def_app_sgd_update η (Δ p.1) (β p.1 p.2) i j :=
    sgdUpd_measurable η Δ β (fun i j => (hΔm i j).comp measurable_fst) hx hy
  have hvm' : ∀ k, Measurable fun p : α × Ω => vec p.1 k :=
    fun k => (hvm k).comp measurable_fst
  have hmv : ∀ k, Measurable fun p : α × Ω =>
      ((def_app_sgd_update η (Δ p.1) (β p.1 p.2))ᵀ *ᵥ vec p.1) k := by
    intro k
    simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply]
    exact Finset.measurable_sum _ fun i _ => (hYm i k).mul (hvm' i)
  refine sgd_integrable_of_bound _ _
    (Finset.measurable_sum _ fun k _ => (hmv k).pow_const 2) ⟨_, fun p =>
      sgd_row_quad_abs_le (add_nonneg (le_max_right _ _) hη) (hYb p)
        (fun i => hv' p.1 i)⟩

/-- **Haar risk identity** (`eqn:app-sgd-risk` at the state `Δ(u)`, given `u`, then averaged
over `u`). The parameter `u` (for `U ∈ O(Nout)`, Haar law `ν`, e.g. `Muon.Foundations.haarO`)
and the batch `β u ω` are jointly random: the whitened batch is independent of `u`, while
`X_out = U Λ^{1/2} z` depends on `u` (l. 626–628), so the batch is a function of `(u, ω)`
with `P` the law of the whitening noise. The annealed expectation is over `ν.prod P`. -/
theorem oneStep_risk_haar {α Ω : Type*} [MeasurableSpace α] [MeasurableSpace Ω]
    (ν : Measure α) [IsProbabilityMeasure ν] (P : Measure Ω) [IsProbabilityMeasure P]
    (C : α → Covariances m n) (Δ : α → Mat m n) (η : ℝ) (hη : 0 ≤ η)
    {B : ℕ} (β : α → Ω → Batch m n B)
    (hx : ∀ a k, Measurable fun p : α × Ω => (β p.1 p.2).xin a k)
    (hy : ∀ a k, Measurable fun p : α × Ω => (β p.1 p.2).xout a k)
    (hΔm : ∀ i j, Measurable fun u => Δ u i j)
    (hCo : ∀ i j, Measurable fun u => (C u).Sout i j)
    (hCi : ∀ i j : Fin n, Measurable fun u => (C u).Sin i j)
    (hΔb : ∃ K : ℝ, ∀ u i j, |Δ u i j| ≤ K)
    (hCb : ∃ K : ℝ, ∀ u : α, ∀ i j : Fin m, |(C u).Sout i j| ≤ K)
    (hCib : ∃ K : ℝ, ∀ u : α, ∀ i j : Fin n, |(C u).Sin i j| ≤ K) :
    ∫ p, Muon.Setup.riskSigma (C p.1) (def_app_sgd_update η (Δ p.1) (β p.1 p.2))
      ∂(ν.prod P)
      = ∫ u, (Muon.Setup.riskSigma (C u) (Δ u)
          - η * Muon.Setup.pairSigma (C u) (Δ u) (batchMean P fun ω => signGrad (Δ u) (β u ω))
          + η ^ 2 / 2 * ∫ ω, Muon.Setup.pairSigma (C u) (signGrad (Δ u) (β u ω))
              (signGrad (Δ u) (β u ω)) ∂P) ∂ν := by
  have hint := sgd_risk_integrable ν P C Δ η hη β hx hy hΔm hCo hCi hΔb hCb hCib
  rw [integral_prod _ hint]
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  exact eqn_app_sgd_risk P (C u) (Δ u) η hη (β u)
    (fun a k => (hx a k).comp measurable_prodMk_left)
    (fun a k => (hy a k).comp measurable_prodMk_left)

/-- **Haar row identity** (`eqn:app-sgd-row` given `U`, averaged over `U`). The row vector
`vec u` is `U e_i` for `U` the Haar parameter; it is a measurable function of the parameter
with bounded entries. The batch `β u ω` is jointly random as in `oneStep_risk_haar`. -/
theorem oneStep_row_haar {α Ω : Type*} [MeasurableSpace α] [MeasurableSpace Ω]
    (ν : Measure α) [IsProbabilityMeasure ν] (P : Measure Ω) [IsProbabilityMeasure P]
    (Δ : α → Mat m n) (vec : α → Vec m) (η : ℝ) (hη : 0 ≤ η)
    {B : ℕ} (β : α → Ω → Batch m n B)
    (hx : ∀ a k, Measurable fun p : α × Ω => (β p.1 p.2).xin a k)
    (hy : ∀ a k, Measurable fun p : α × Ω => (β p.1 p.2).xout a k)
    (hΔm : ∀ i j, Measurable fun u => Δ u i j)
    (hvm : ∀ k, Measurable fun u => vec u k)
    (hΔb : ∃ K : ℝ, ∀ u i j, |Δ u i j| ≤ K)
    (hvb : ∃ K : ℝ, ∀ u k, |vec u k| ≤ K) :
    ∫ p, ∑ k, ((def_app_sgd_update η (Δ p.1) (β p.1 p.2))ᵀ *ᵥ vec p.1) k ^ 2 ∂(ν.prod P)
      = ∫ u, (∑ k, ((Δ u)ᵀ *ᵥ vec u) k ^ 2
        - 2 * η * ∫ ω, (((Δ u)ᵀ *ᵥ vec u) ⬝ᵥ ((signGrad (Δ u) (β u ω))ᵀ *ᵥ vec u)) ∂P
        + η ^ 2 * ∫ ω, ∑ k, ((signGrad (Δ u) (β u ω))ᵀ *ᵥ vec u) k ^ 2 ∂P) ∂ν := by
  have hint := sgd_row_integrable ν P Δ vec η hη β hx hy hΔm hvm hΔb hvb
  rw [integral_prod _ hint]
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  exact eqn_app_sgd_row P (Δ u) (vec u) η hη (β u)
    (fun a k => (hx a k).comp measurable_prodMk_left)
    (fun a k => (hy a k).comp measurable_prodMk_left)

end Muon.SignSGD
