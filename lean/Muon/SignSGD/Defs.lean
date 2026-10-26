import Mathlib

/-!
# Appendix I (SignSGD): definitions

Interface for the labels `def:app-sgd-update`, `def:app-sgd-iso-regime`,
`def:app-sgd-state-law` (the part that does not need the Haar measure on `O(n)`),
and the batch constant `eqn:signsgd-Nb` (exported as `Muon.SignSGD.batchConst`, used
early by Appendix H). Source of record: snapshot `cr-2026-10-22`, `sections/08-signsgd/section.tex`.

Conventions: `Real.sign 0 = 0` (the paper's `sign`, applied entrywise to matrices).
Vectors are `Fin n → ℝ`; matrices are `Matrix (Fin m) (Fin n) ℝ`.
The Haar probability on `O(Nout)` and the independence of `U` from the batch are NOT
formalized here (see the `TODO` in `def_app_sgd_state_law`).
-/

open MeasureTheory ProbabilityTheory

namespace Muon.SignSGD

/-! ## Batches and the physical gradient -/

/-- A batch of `B` pairs `(Xin^(a), Xout^(a))` with `Xin^(a) ∈ ℝ^{Nin}`, `Xout^(a) ∈ ℝ^{Nout}`. -/
structure Batch (Nout Nin B : ℕ) where
  xin : Fin B → (Fin Nin → ℝ)
  xout : Fin B → (Fin Nout → ℝ)

/-- The residual `d_a° = (Xout^(a))ᵀ Δ Xin^(a)` of `prop:app-setup-moments`(ii). -/
def residual {Nout Nin B : ℕ} (Δ : Matrix (Fin Nout) (Fin Nin) ℝ)
    (β : Batch Nout Nin B) (a : Fin B) : ℝ :=
  dotProduct (β.xout a) (Δ.mulVec (β.xin a))

/-- The physical gradient `G° = (1/B) Σ_a d_a° Xout^(a) ⊗ Xin^(a)` (the display before
`def:app-sgd-update`, i.e. `def:app-setup-model` with `Σin = I`). -/
noncomputable def physGrad {Nout Nin B : ℕ} (Δ : Matrix (Fin Nout) (Fin Nin) ℝ)
    (β : Batch Nout Nin B) : Matrix (Fin Nout) (Fin Nin) ℝ :=
  fun i j => (1 / (B : ℝ)) * ∑ a : Fin B, residual Δ β a * (β.xout a i * β.xin a j)

/-- **def:app-sgd-update** `Muon.SignSGD.def_app_sgd_update`.

cr-2026-10-22. LaTeX statement (verbatim):
The \SignSGD step from the state $\Delta$ with step $\lr\ge0$ is
\begin{equation}\label{eqn:app-sgd-update}
\Delta^+\defeq\Delta-\lr S,\qquad S\defeq\sign(G^\circ).
\end{equation}

The step is a function of the state `Δ`, the step size `η` (the paper takes `η ≥ 0`;
the definition is stated for all real `η`, and the nonnegativity is a hypothesis of
every consumer), and the batch. `Real.sign` is applied entrywise, with `Real.sign 0 = 0`.
-/
noncomputable def def_app_sgd_update {Nout Nin B : ℕ} (η : ℝ)
    (Δ : Matrix (Fin Nout) (Fin Nin) ℝ) (β : Batch Nout Nin B) :
    Matrix (Fin Nout) (Fin Nin) ℝ :=
  Δ - η • (physGrad Δ β).map Real.sign

/-- **eqn:signsgd-Nb** `Muon.SignSGD.batchConst`, the batch constant of the main text.

cr-2026-10-22. LaTeX statement (verbatim):
\begin{equation}\label{eqn:signsgd-Nb}
\mathcal N_B\defeq\EE\Big[\Big(\sum_{b=1}^Bx_b^2y_b^2\Big)^{1/2}\Big],\qquad x_b,y_b\ \text{independent standard Gaussian}.
\end{equation}

Here `x` and `y` are independent vectors in `ℝ^B` with i.i.d. `N(0,1)` coordinates:
the law of `(x, y)` is the product of two copies of `Measure.pi (fun _ => gaussianReal 0 1)`.
-/
noncomputable def batchConst (B : ℕ) : ℝ :=
  let stdGauss : Measure (Fin B → ℝ) := Measure.pi fun _ : Fin B => gaussianReal 0 1
  ∫ p, Real.sqrt (∑ b : Fin B, p.1 b ^ 2 * p.2 b ^ 2) ∂(stdGauss.prod stdGauss)

/-! ## Isotropic regime -/

/-- Frobenius norm `‖A‖_F = (Σ_{ij} A_ij²)^{1/2}` (explicit form; agrees with
`Matrix.frobenius_norm_def`). -/
noncomputable def frobNorm {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) : ℝ :=
  Real.sqrt (∑ i, ∑ j, A i j ^ 2)

/-- `k = min{Nout, Nin, B}`. -/
def kOf (Nout Nin B : ℕ) : ℕ := min Nout (min Nin B)

/-- The fixed parameters `K ≥ 1`, `0 < f₋ ≤ f₊`, `C_Δ > 0` of `def:app-sgd-iso-regime`
(the paper's "Fix ..."). -/
structure IsoParams where
  K : ℝ
  fMin : ℝ
  fMax : ℝ
  Cdelta : ℝ
  one_le_K : 1 ≤ K
  fMin_pos : 0 < fMin
  fMin_le_fMax : fMin ≤ fMax
  Cdelta_pos : 0 < Cdelta

/-- **def:app-sgd-iso-regime** `Muon.SignSGD.def_app_sgd_iso_regime`.

cr-2026-10-22. LaTeX statement (verbatim):
Fix $K\ge1$, $0<f_-\le f_+$ and $C_\Delta>0$. A deterministic state $\Delta$
with batch size $B$ is in the isotropic regime if, with
$k\defeq\min\{\Nout,\Nin,B\}$,
\begin{equation}\label{eqn:app-sgd-iso-regime}
\max\{\Nout,\Nin,B\}\le Kk,\qquad f_-\le\norm\Delta_\F\le f_+,\qquad \max_{i,j}\abs{\Delta_{ij}}\le\frac{C_\Delta}k .
\end{equation}
-/
def def_app_sgd_iso_regime (P : IsoParams) (Nout Nin B : ℕ)
    (Δ : Matrix (Fin Nout) (Fin Nin) ℝ) : Prop :=
  let k : ℝ := (kOf Nout Nin B : ℝ)
  (Nout : ℝ) ≤ P.K * k ∧ (Nin : ℝ) ≤ P.K * k ∧ (B : ℝ) ≤ P.K * k ∧
    P.fMin ≤ frobNorm Δ ∧ frobNorm Δ ≤ P.fMax ∧
    ∀ i j, |Δ i j| ≤ P.Cdelta / k

/-! ## Haar state law (deterministic part) -/

/-- The fixed parameters `K ≥ 1`, `0 < c ≤ L`, `0 < f₋ ≤ f₊`, `C_col > 0` of
`def:app-sgd-state-law`. -/
structure HaarParams where
  K : ℝ
  c : ℝ
  L : ℝ
  fMin : ℝ
  fMax : ℝ
  Ccol : ℝ
  one_le_K : 1 ≤ K
  c_pos : 0 < c
  c_le_L : c ≤ L
  fMin_pos : 0 < fMin
  fMin_le_fMax : fMin ≤ fMax
  Ccol_pos : 0 < Ccol

/-- **def:app-sgd-state-law** `Muon.SignSGD.def_app_sgd_state_law` (deterministic part).

cr-2026-10-22. LaTeX statement (verbatim):
Fix $K\ge1$, $0<c\le L$, $0<f_-\le f_+$ and $C_{\rm col}>0$. Let
$\Nout,\Nin,B$ be positive integers with $k\defeq\min\{\Nout,\Nin,B\}\ge2$ and
$\max\{\Nout,\Nin,B\}\le Kk$. Let $\Lambda=\diag(\mu_1,\dots,\mu_{\Nout})$
and $D\in\R^{\Nout\times\Nin}$ be deterministic with
\begin{equation}\label{eqn:app-sgd-state-bounds}
c\,\Idout\preceq\Lambda\preceq L\,\Idout,\qquad f_-\le\norm D_\F\le f_+,\qquad \max_j\norm{D_{\cdot j}}^2\le\frac{C_{\rm col}}k .
\end{equation}
Let $U$ be Haar distributed on the orthogonal group $O(\Nout)$ and
independent of the batch. The half-anisotropic Haar model is
\[
\Sigmaout=U\Lambda U^\T,\qquad \Sigmain=\Idin,\qquad \Delta=UD .
\]

The bounds on `μ` are coordinatewise, which is the Loewner order for diagonal matrices.
The Haar part is a TODO, not formalized here: the probability measure `U ~ Haar(O(Nout))`
and its independence from the whitened batch, the sample space `O(Nout) × batch`, and the
conditional mean `M(U) = E[S | U]` all need `orthHaar` (Q1 in `CARD.md`, §4 and §6.1).
The deterministic maps `U ↦ Δ = UD` and `U ↦ Σout = UΛUᵀ` are given below
(`haarDelta`, `haarSigmaOut`).
-/
def def_app_sgd_state_law (P : HaarParams) (Nout Nin B : ℕ) (μ : Fin Nout → ℝ)
    (D : Matrix (Fin Nout) (Fin Nin) ℝ) : Prop :=
  let k : ℝ := (kOf Nout Nin B : ℝ)
  (0 < Nout ∧ 0 < Nin ∧ 0 < B) ∧
  2 ≤ kOf Nout Nin B ∧
  (Nout : ℝ) ≤ P.K * k ∧ (Nin : ℝ) ≤ P.K * k ∧ (B : ℝ) ≤ P.K * k ∧
  (∀ i, P.c ≤ μ i ∧ μ i ≤ P.L) ∧
  P.fMin ≤ frobNorm D ∧ frobNorm D ≤ P.fMax ∧
  ∀ j, ∑ i, D i j ^ 2 ≤ P.Ccol / k

/-- Haar-model update `Δ = U D` for `U ∈ O(n)` (deterministic given `U`). -/
def haarDelta {n m : ℕ} (U : Matrix.orthogonalGroup (Fin n) ℝ)
    (D : Matrix (Fin n) (Fin m) ℝ) : Matrix (Fin n) (Fin m) ℝ :=
  (U : Matrix (Fin n) (Fin n) ℝ) * D

/-- Haar-model covariance `Σout = U Λ Uᵀ` with `Λ = diag(μ)` (deterministic given `U`). -/
def haarSigmaOut {n : ℕ} (U : Matrix.orthogonalGroup (Fin n) ℝ) (μ : Fin n → ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  (U : Matrix (Fin n) (Fin n) ℝ) * Matrix.diagonal μ * (U : Matrix (Fin n) (Fin n) ℝ).transpose

/-- `2ℛ := ‖Δ‖²_Σ = Tr(Λ D Dᵀ)` in the Haar model. -/
def twoR {n m : ℕ} (μ : Fin n → ℝ) (D : Matrix (Fin n) (Fin m) ℝ) : ℝ :=
  (Matrix.diagonal μ * (D * D.transpose)).trace

/-- `μ̄ = Tr Λ / Nout`. -/
noncomputable def muBar {n : ℕ} (μ : Fin n → ℝ) : ℝ :=
  (∑ i, μ i) / (n : ℝ)

/-- `T_D = Λ D Dᵀ Λ`. -/
noncomputable def TD {n m : ℕ} (μ : Fin n → ℝ) (D : Matrix (Fin n) (Fin m) ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  Matrix.diagonal μ * (D * D.transpose) * Matrix.diagonal μ

/-- `L_B = √(2/π) 𝒩_B / √(2ℛ μ̄)`. -/
noncomputable def LB (B : ℕ) {n m : ℕ} (μ : Fin n → ℝ) (D : Matrix (Fin n) (Fin m) ℝ) :
    ℝ :=
  Real.sqrt (2 / Real.pi) * batchConst B / Real.sqrt (twoR μ D * muBar μ)

/-- The fixed constants `P₋ = c f₋²`. -/
noncomputable def haarPminus (P : HaarParams) : ℝ := P.c * P.fMin ^ 2
/-- The fixed constants `P₊ = L f₊²`. -/
noncomputable def haarPplus (P : HaarParams) : ℝ := P.L * P.fMax ^ 2
/-- The fixed constants `H₀ = L² f₊²`. -/
noncomputable def haarH0 (P : HaarParams) : ℝ := P.L ^ 2 * P.fMax ^ 2
/-- The fixed constants `A₀ = H₀ / c`. -/
noncomputable def haarA0 (P : HaarParams) : ℝ := haarH0 P / P.c
/-- The fixed constants `A₁ = L² C_col / c`. -/
noncomputable def haarA1 (P : HaarParams) : ℝ := P.L ^ 2 * P.Ccol / P.c
/-- The fixed constants `A₂ = L C_col`. -/
noncomputable def haarA2 (P : HaarParams) : ℝ := P.L * P.Ccol

private lemma trace_diag_mul_DDt {n m : ℕ} (μ : Fin n → ℝ) (D : Matrix (Fin n) (Fin m) ℝ) :
    (Matrix.diagonal μ * (D * D.transpose)).trace = ∑ i, μ i * ∑ j, D i j ^ 2 := by
  simp only [Matrix.trace, Matrix.diag, Matrix.diagonal_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [Matrix.mul_apply, pow_two]

private lemma trace_TD_eq {n m : ℕ} (μ : Fin n → ℝ) (D : Matrix (Fin n) (Fin m) ℝ) :
    (Matrix.diagonal μ * (D * D.transpose) * Matrix.diagonal μ).trace
      = ∑ i, μ i * (μ i * ∑ j, D i j ^ 2) := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_diagonal, Matrix.diagonal_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [Matrix.mul_apply, pow_two]
  ring

/-- Bounds stated after `def:app-sgd-state-law` (l. 637): `P₋ ≤ 2ℛ ≤ P₊`,
`Tr T_D ≤ H₀`, `c ≤ μ̄ ≤ L`. Helper statement, proof pending. -/
theorem haar_bounds (P : HaarParams) (Nout Nin B : ℕ) (μ : Fin Nout → ℝ)
    (D : Matrix (Fin Nout) (Fin Nin) ℝ) (h : def_app_sgd_state_law P Nout Nin B μ D) :
    haarPminus P ≤ twoR μ D ∧ twoR μ D ≤ haarPplus P ∧
    (TD μ D).trace ≤ haarH0 P ∧ P.c ≤ muBar μ ∧ muBar μ ≤ P.L := by
  unfold def_app_sgd_state_law at h
  obtain ⟨⟨hNout, -, -⟩, -, -, -, -, hmu, hf1, hf2, -⟩ := h
  have hn : (0 : ℝ) < (Nout : ℝ) := by exact_mod_cast hNout
  have hS0 : 0 ≤ ∑ i, ∑ j, D i j ^ 2 :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _
  have hsq : Real.sqrt (∑ i, ∑ j, D i j ^ 2) ^ 2 = ∑ i, ∑ j, D i j ^ 2 := Real.sq_sqrt hS0
  have hF1 : P.fMin ^ 2 ≤ ∑ i, ∑ j, D i j ^ 2 := by
    have h1 : P.fMin ≤ Real.sqrt (∑ i, ∑ j, D i j ^ 2) := hf1
    nlinarith [Real.sqrt_nonneg (∑ i, ∑ j, D i j ^ 2), P.fMin_pos]
  have hF2 : ∑ i, ∑ j, D i j ^ 2 ≤ P.fMax ^ 2 := by
    have h2 : Real.sqrt (∑ i, ∑ j, D i j ^ 2) ≤ P.fMax := hf2
    nlinarith [Real.sqrt_nonneg (∑ i, ∑ j, D i j ^ 2), P.fMin_pos, P.fMin_le_fMax]
  have hr : ∀ i, 0 ≤ ∑ j, D i j ^ 2 := fun i => Finset.sum_nonneg fun j _ => sq_nonneg _
  have hLpos : 0 < P.L := lt_of_lt_of_le P.c_pos P.c_le_L
  have hlow : P.c * ∑ i, ∑ j, D i j ^ 2 ≤ ∑ i, μ i * ∑ j, D i j ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hmu i).1 (hr i)
  have hup : ∑ i, μ i * ∑ j, D i j ^ 2 ≤ P.L * ∑ i, ∑ j, D i j ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hmu i).2 (hr i)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · unfold haarPminus twoR
    rw [trace_diag_mul_DDt]
    exact le_trans (mul_le_mul_of_nonneg_left hF1 P.c_pos.le) hlow
  · unfold haarPplus twoR
    rw [trace_diag_mul_DDt]
    exact le_trans hup (mul_le_mul_of_nonneg_left hF2 hLpos.le)
  · unfold haarH0 TD
    rw [trace_TD_eq]
    have key : ∀ i, μ i * (μ i * ∑ j, D i j ^ 2) ≤ P.L * P.L * ∑ j, D i j ^ 2 := by
      intro i
      have hμ := hmu i
      have hμμ : μ i * μ i ≤ P.L * P.L :=
        mul_le_mul hμ.2 hμ.2 (P.c_pos.trans_le hμ.1).le hLpos.le
      calc μ i * (μ i * ∑ j, D i j ^ 2) = (μ i * μ i) * ∑ j, D i j ^ 2 := by ring
        _ ≤ (P.L * P.L) * ∑ j, D i j ^ 2 := mul_le_mul_of_nonneg_right hμμ (hr i)
    have hsum := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => key i
    rw [← Finset.mul_sum] at hsum
    have h3 := mul_le_mul_of_nonneg_left hF2 (mul_nonneg hLpos.le hLpos.le)
    calc _ ≤ _ := hsum
      _ ≤ P.L * P.L * P.fMax ^ 2 := h3
      _ = haarH0 P := by unfold haarH0; ring
  · unfold muBar
    rw [le_div_iff₀ hn]
    have := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => (hmu i).1)
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at this
    linarith
  · unfold muBar
    rw [div_le_iff₀ hn]
    have := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => (hmu i).2)
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at this
    linarith

end Muon.SignSGD
