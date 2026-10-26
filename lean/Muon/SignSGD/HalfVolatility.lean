import Mathlib
import Muon.SignSGD.HalfDrift
import Muon.External.Certificates

/-!
# Appendix I (SignSGD): column moments, quadratic forms, Haar reduction and the half-anisotropic
volatility (task L-I.10)

Interface for work package L-I.10 (card `sections/08-signsgd/CARD.md` §3 rows 23–27, §3b rows
990–994 and 1101–1108, §5 row L-I.10). Source of record: snapshot `cr-2026-10-23`,
`sections/08-signsgd/section.tex`. Labels: `lem:app-sgd-column` (l. 999–1014),
`prop:app-sgd-quadratic` (l. 1056–1063), `lem:app-sgd-reduction` (l. 1110–1118),
`thm:app-sgd-half-volatility` (l. 1135–1143), `cor:app-sgd-half-risk` (l. 1171–1177).
Docstrings carry the LaTeX statements verbatim (copied by script from `section.tex`).

Choices:
* Haar measure: a probability `ν` on `O(n)` with `Muon.Foundations.IsOrthHaar ν` (coordinator Q1).
  Joint expectations over `(U, batch)` use `ν.prod (batchLaw n m B)`; expectations over the batch
  alone use `batchLaw n m B`.
* Whitened batch (coordinator Q2): `Xout = U Λ^{1/2} z`, `Xin = w`, with `(z, w)` i.i.d. `gaussBatch`.
  `H` and the columns `h_j` are functions of the batch alone, so `H ⊥ U` holds by construction;
  `G° = U H` is `gPhys_eq_mul_hMatrix`.
* Admissible constants: `∀ P : HaarParams, ∃ C, 0 ≤ C, ∀ n m B μ D …`, with the constant chosen
  after `P` and before the dimensions, the state and the Haar measure. The explicit values of the
  source proofs are recorded as helper `def`s (`colV0`, `colA4`, `colA8`, `quadVstar`, `quadDstar`,
  `volConst`); the declarations of record are existential, as in the source.
* Moments of nonnegative quantities are `∫⁻` of `ENNReal.ofReal`, so no Bochner junk value can
  satisfy a bound. Expectations of the a.s.-defined ratio `R_j` are Bochner integrals over the batch,
  and the claims about `R_j` are `∀ᵐ` statements.
* `‖Π‖` is `Muon.External.matOpNorm`; `‖a‖²` is `∑ a_i²`; `‖·‖_F` is `Muon.SignSGD.frobNorm`.
-/

open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace Muon.SignSGD

/-! ## Objects of the half-anisotropic column (`eqn:app-sgd-H`, `eqn:app-sgd-cov`) -/

/-- `Λ^{1/2} = diag(√μ_k)`, the matrix used by `haarBatch` (`Xout = U Λ^{1/2} z`). -/
noncomputable def lamHalf {n : ℕ} (μ : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.diagonal fun k => Real.sqrt (μ k)

/-- The residual `zᵀ A w` with `A = Λ^{1/2} D`, for a whitened sample `p = (z, w)` (`eqn:app-sgd-H`). -/
noncomputable def resA {n m : ℕ} (μ : Fin n → ℝ) (D : Matrix (Fin n) (Fin m) ℝ)
    (p : (Fin n → ℝ) × (Fin m → ℝ)) : ℝ :=
  p.1 ⬝ᵥ ((lamHalf μ * D) *ᵥ p.2)

/-- The single-sample column `X = (zᵀ A w) w_j Λ^{1/2} z` (l. 995–998). -/
noncomputable def colSample {n m : ℕ} (μ : Fin n → ℝ) (D : Matrix (Fin n) (Fin m) ℝ) (j : Fin m)
    (p : (Fin n → ℝ) × (Fin m → ℝ)) : Fin n → ℝ :=
  fun i => resA μ D p * ((lamHalf μ *ᵥ p.1) i * p.2 j)

/-- `m_j = Λ D_{·j}` (l. 996). -/
noncomputable def colMeanVec {n m : ℕ} (μ : Fin n → ℝ) (D : Matrix (Fin n) (Fin m) ℝ) (j : Fin m) :
    Fin n → ℝ :=
  fun i => μ i * D i j

/-- `Z = X - m_j` (l. 996). -/
noncomputable def colZ {n m : ℕ} (μ : Fin n → ℝ) (D : Matrix (Fin n) (Fin m) ℝ) (j : Fin m)
    (p : (Fin n → ℝ) × (Fin m → ℝ)) : Fin n → ℝ :=
  colSample μ D j p - colMeanVec μ D j

/-- `V_j = E[Z ⊗ Z]` under the single-sample law `gaussBatch n m` (l. 1001). -/
noncomputable def colCov {n m : ℕ} (μ : Fin n → ℝ) (D : Matrix (Fin n) (Fin m) ℝ) (j : Fin m) :
    Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i k => ∫ p, colZ μ D j p i * colZ μ D j p k ∂(gaussBatch n m)

/-- `C_j = D_{·j}ᵀ Λ D_{·j}` (l. 996). -/
noncomputable def colC {n m : ℕ} (μ : Fin n → ℝ) (D : Matrix (Fin n) (Fin m) ℝ) (j : Fin m) : ℝ :=
  ∑ k, μ k * D k j ^ 2

/-- The `j`th column `h_j = (1/B) Σ_b X_b` of `H` (l. 991–994). -/
noncomputable def hCol {n m B : ℕ} (μ : Fin n → ℝ) (D : Matrix (Fin n) (Fin m) ℝ)
    (β : Fin B → (Fin n → ℝ) × (Fin m → ℝ)) (j : Fin m) : Fin n → ℝ :=
  fun i => (1 / (B : ℝ)) * ∑ a, colSample μ D j (β a) i

/-- The matrix `H = (1/B) Σ_b (z_bᵀ A w_b) Λ^{1/2} z_b ⊗ w_b` of `eqn:app-sgd-H`. It is a function
of the batch alone, which is the independence of `H` from `U`. -/
noncomputable def hMatrix {n m B : ℕ} (μ : Fin n → ℝ) (D : Matrix (Fin n) (Fin m) ℝ)
    (β : Fin B → (Fin n → ℝ) × (Fin m → ℝ)) : Matrix (Fin n) (Fin m) ℝ :=
  Matrix.of fun i j => hCol μ D β j i

/-- The ratio `R_j = h_jᵀ Λ h_j / ‖h_j‖²` of `lem:app-sgd-reduction`, with Lean division. The
claims about it are a.s. claims, on which `h_j ≠ 0`. -/
noncomputable def redR {n m B : ℕ} (μ : Fin n → ℝ) (D : Matrix (Fin n) (Fin m) ℝ)
    (β : Fin B → (Fin n → ℝ) × (Fin m → ℝ)) (j : Fin m) : ℝ :=
  (hCol μ D β j ⬝ᵥ (Matrix.diagonal μ *ᵥ hCol μ D β j)) / (hCol μ D β j ⬝ᵥ hCol μ D β j)

/-! ## Volatility objects (`eqn:app-sgd-Q`, l. 1101–1108) -/

/-- `𝔳_i^{s-SGD} = m [1 + (2/π)(μ_i/μ̄ - 1)]`, the main text's row volatility for general `n, m`
(`eqn:app-sgd-Q`, l. 1106–1107). -/
noncomputable def vSgd (n m : ℕ) (μ : Fin n → ℝ) (i : Fin n) : ℝ :=
  (m : ℝ) * (1 + 2 / Real.pi * (μ i / muBar μ - 1))

/-- `𝒬_print = m [(1 - 2/π) Tr Λ + (2/π) n Tr Λ² / Tr Λ]` (`eqn:app-sgd-Q`, l. 1103–1104). -/
noncomputable def haarQPrint (n m : ℕ) (μ : Fin n → ℝ) : ℝ :=
  (m : ℝ) * ((1 - 2 / Real.pi) * (∑ i, μ i)
    + (2 / Real.pi * (n : ℝ) * (∑ i, μ i ^ 2)) / (∑ i, μ i))

/-- `𝒬 = E‖S‖²_Σ` in the Haar model, annealed over `(U, batch)` with `Σ = U Λ Uᵀ` (`eqn:app-sgd-Q`,
l. 1102). The batch has `B` samples. -/
noncomputable def haarQ {n m : ℕ} (B : ℕ) (ν : Measure (Matrix.orthogonalGroup (Fin n) ℝ))
    (μ : Fin n → ℝ) (D : Matrix (Fin n) (Fin m) ℝ) : ℝ :=
  ∫ p, riskTwo (haarSigmaOut p.1 μ) (haarSign μ D p.1 p.2) ∂(ν.prod (batchLaw n m B))

/-! ## Explicit admissible constants of the source proofs (helpers; the declarations of record are
existential) -/

/-- `V₀ = L P₊ + 2 H₀ + 5 L² C_col` (proof of `lem:app-sgd-column`, l. 1013). -/
noncomputable def colV0 (P : HaarParams) : ℝ :=
  P.L * haarPplus P + 2 * haarH0 P + 5 * P.L ^ 2 * P.Ccol

/-- `A₄ = 16 (11!!)² P₊² L²` (proof of `lem:app-sgd-column`, l. 1031–1033). -/
noncomputable def colA4 (P : HaarParams) : ℝ :=
  16 * ((Nat.doubleFactorial 11 : ℕ) : ℝ) ^ 2 * haarPplus P ^ 2 * P.L ^ 2

/-- `A₈ = 256 (23!!)² P₊⁴ L⁴` (proof of `lem:app-sgd-column`, l. 1031–1033). -/
noncomputable def colA8 (P : HaarParams) : ℝ :=
  256 * ((Nat.doubleFactorial 23 : ℕ) : ℝ) ^ 2 * haarPplus P ^ 4 * P.L ^ 4

/-- `V_* = 2 A₄ K² + 4 K V₀² + 8 V₀ L² C_col` (proof of `prop:app-sgd-quadratic`, l. 1077). -/
noncomputable def quadVstar (P : HaarParams) : ℝ :=
  2 * colA4 P * P.K ^ 2 + 4 * P.K * colV0 P ^ 2 + 8 * colV0 P * P.L ^ 2 * P.Ccol

/-- `D_* = 2 L² C_col K + 2 H₀ + 4 L² C_col` (proof of `prop:app-sgd-quadratic`, l. 1090–1092). -/
noncomputable def quadDstar (P : HaarParams) : ℝ :=
  2 * P.L ^ 2 * P.Ccol * P.K + 2 * haarH0 P + 4 * P.L ^ 2 * P.Ccol

/-- `C_vol = (4L/(π x₋))(√V_* + D_*)`, `x₋ = c² f₋² / K` (proof of `thm:app-sgd-half-volatility`,
l. 1163). -/
noncomputable def volConst (P : HaarParams) : ℝ :=
  4 * P.L / (Real.pi * (P.c ^ 2 * P.fMin ^ 2 / P.K)) * (Real.sqrt (quadVstar P) + quadDstar P)

/-! ## Unlabeled helper facts (§3b rows 990–994 and 1101–1108) -/

private theorem orth_dot_P {n : ℕ} (U : Matrix.orthogonalGroup (Fin n) ℝ) (a b : Fin n → ℝ) :
    ((U : Matrix (Fin n) (Fin n) ℝ) *ᵥ a) ⬝ᵥ ((U : Matrix (Fin n) (Fin n) ℝ) *ᵥ b) = a ⬝ᵥ b := by
  have hU : (U : Matrix (Fin n) (Fin n) ℝ)ᵀ * (U : Matrix (Fin n) (Fin n) ℝ) = 1 :=
    (Matrix.mem_orthogonalGroup_iff' (Fin n) ℝ).mp U.2
  rw [← Matrix.vecMul_transpose, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, hU,
    Matrix.vecMul_one]

private theorem diag_dot_P {n : ℕ} (d : Fin n → ℝ) (z b : Fin n → ℝ) :
    (Matrix.diagonal d *ᵥ z) ⬝ᵥ b = z ⬝ᵥ (Matrix.diagonal d *ᵥ b) := by
  simp only [dotProduct, Matrix.mulVec_diagonal]
  exact Finset.sum_congr rfl fun i _ => by ring

private theorem resid_eq_P {n m B : ℕ} (μ : Fin n → ℝ) (D : Matrix (Fin n) (Fin m) ℝ)
    (U : Matrix.orthogonalGroup (Fin n) ℝ) (β : Fin B → (Fin n → ℝ) × (Fin m → ℝ)) (a : Fin B) :
    residual (haarDelta U D) (haarBatch μ U β) a = resA μ D (β a) := by
  simp only [residual, haarDelta, haarBatch, linBatch, resA, lamHalf]
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, orth_dot_P, diag_dot_P, ← Matrix.mulVec_mulVec]

/-- Unlabeled identity `G° = U H` of the Haar model (l. 990–994, `eqn:app-sgd-H`), with `H` the
function of the batch alone. Source (verbatim):
The update factors through the eigenbasis. With $A\defeq\Lambda^{1/2}D$,
which is $U^\T\At$ for the rotated error of \cref{eqn:app-setup-whitened},
\begin{equation}\label{eqn:app-sgd-H}
G^\circ=UH,\qquad H\defeq\frac1B\sum_{b=1}^B\big(z_b^\T Aw_b\big)\,\Lambda^{1/2}z_b\tensor w_b ,
\end{equation}
and $H$ is independent of $U$. Its $j$th column is the mean
$h_j=\frac1B\sum_bX_b$ of independent copies of
\[
X\defeq\big(z^\T Aw\big)\,w_j\,\Lambda^{1/2}z\in\R^{\Nout},\qquad
m_j\defeq\Lambda D_{\cdot j},\qquad Z\defeq X-m_j .
\]
-/
theorem gPhys_eq_mul_hMatrix {n m B : ℕ} (μ : Fin n → ℝ) (D : Matrix (Fin n) (Fin m) ℝ)
    (U : Matrix.orthogonalGroup (Fin n) ℝ) (β : Fin B → (Fin n → ℝ) × (Fin m → ℝ)) :
    physGrad (haarDelta U D) (haarBatch μ U β) = (U : Matrix (Fin n) (Fin n) ℝ) * hMatrix μ D β := by
  ext i j
  have hL : ∀ a, (haarBatch μ U β).xout a =
      (U : Matrix (Fin n) (Fin n) ℝ) *ᵥ (lamHalf μ *ᵥ (β a).1) := by
    intro a
    simp only [haarBatch, linBatch, lamHalf]
    rw [← Matrix.mulVec_mulVec]
  simp only [physGrad, hMatrix, hCol, Matrix.of_apply, Matrix.mul_apply, colSample, resid_eq_P,
    hL]
  simp only [haarBatch, linBatch]
  simp only [Matrix.mulVec, dotProduct, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun k _ => ?_
  exact Finset.sum_congr rfl fun x _ => by ring

/-- Unlabeled identity `𝒬_print = Σ_i μ_i 𝔳_i^{s-SGD}` (l. 1101–1108, `eqn:app-sgd-Q`). Source
(verbatim):
corresponding sum for the main text's array:
\begin{equation}\label{eqn:app-sgd-Q}
\begin{aligned}
\mathcal Q&\defeq\EE\norm S_\Sigma^2=\EE\Tr\big(\Sigmaout SS^\T\big),\\
\mathcal Q_{\rm print}&\defeq\Nin\Big[\Big(1-\frac2\pi\Big)\Tr\Lambda+\frac2\pi\,\Nout\,\frac{\Tr\Lambda^2}{\Tr\Lambda}\Big]=\sum_i\mu_i\,\mathfrak v_i^{\text{s-SGD}},
\end{aligned}
\end{equation}
where $\mathfrak v_i^{\text{s-SGD}}\defeq\Nin\big[1+\frac2\pi\big(\frac{\mu_i}{\bar\mu}-1\big)\big]$
is the main text's \SignSGD row volatility, written for general $\Nout,\Nin$.
-/
theorem qPrint_eq_sum (n m : ℕ) (μ : Fin n → ℝ) :
    haarQPrint n m μ = ∑ i, μ i * vSgd n m μ i := by
  unfold haarQPrint vSgd muBar
  have key : ∀ i, μ i * ((m : ℝ) * (1 + 2 / Real.pi * (μ i / ((∑ j, μ j) / (n : ℝ)) - 1)))
      = (m : ℝ) * (μ i + 2 / Real.pi * (n : ℝ) * μ i ^ 2 / (∑ j, μ j) - 2 / Real.pi * μ i) := by
    intro i
    rw [div_div_eq_mul_div]
    ring
  rw [Finset.sum_congr rfl (fun i _ => key i), ← Finset.mul_sum, Finset.sum_sub_distrib,
    Finset.sum_add_distrib, ← Finset.sum_div]
  simp only [← Finset.mul_sum]
  ring

/-! ## Column moments (`lem:app-sgd-column`) -/

/-! ### Proof helpers for `lem:app-sgd-column` (private; Gaussian facts re-proved locally) -/

private lemma hv_mono_int {n k : ℕ} (c : Fin k → Fin n) :
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

private lemma hv_pair_int {n : ℕ} (a b : Fin n) :
    Integrable (fun z : Fin n → ℝ => z a * z b) (Muon.Foundations.stdGaussianPi n) := by
  have h := hv_mono_int (n := n) (k := 2) ![a, b]
  simpa [Fin.prod_univ_two] using h

private lemma hv_quad_int {n : ℕ} (a b c d : Fin n) :
    Integrable (fun z : Fin n → ℝ => z a * z b * z c * z d)
      (Muon.Foundations.stdGaussianPi n) := by
  have h := hv_mono_int (n := n) (k := 4) ![a, b, c, d]
  simpa [Fin.prod_univ_four] using h

private lemma hv_double_int {n m : ℕ} {ι κ : Type*} [Fintype ι] [Fintype κ]
    (f : ι → κ → (Fin n → ℝ) → ℝ) (g : ι → κ → (Fin m → ℝ) → ℝ)
    (hf : ∀ a b, Integrable (f a b) (Muon.Foundations.stdGaussianPi n))
    (hg : ∀ a b, Integrable (g a b) (Muon.Foundations.stdGaussianPi m)) :
    Integrable (fun p : (Fin n → ℝ) × (Fin m → ℝ) => ∑ a, ∑ b, f a b p.1 * g a b p.2)
      (Muon.SignSGD.gaussBatch n m) := by
  unfold Muon.SignSGD.gaussBatch
  exact integrable_finsetSum _ fun a _ => integrable_finsetSum _ fun b _ =>
    (hf a b).mul_prod (hg a b)

private lemma hv_single_int {n m : ℕ} {ι : Type*} [Fintype ι]
    (f : ι → (Fin n → ℝ) → ℝ) (g : ι → (Fin m → ℝ) → ℝ)
    (hf : ∀ a, Integrable (f a) (Muon.Foundations.stdGaussianPi n))
    (hg : ∀ a, Integrable (g a) (Muon.Foundations.stdGaussianPi m)) :
    Integrable (fun p : (Fin n → ℝ) × (Fin m → ℝ) => ∑ a, f a p.1 * g a p.2)
      (Muon.SignSGD.gaussBatch n m) := by
  unfold Muon.SignSGD.gaussBatch
  exact integrable_finsetSum _ fun a _ => (hf a).mul_prod (hg a)

private lemma hv_Lw_int {m : ℕ} (α β : Fin m → ℝ) (j : Fin m) :
    Integrable (fun w : Fin m → ℝ => (∑ c, α c * (w c * w j)) * (∑ c, β c * (w c * w j)))
      (Muon.Foundations.stdGaussianPi m) := by
  have e : (fun w : Fin m → ℝ => (∑ c, α c * (w c * w j)) * (∑ c, β c * (w c * w j)))
      = fun w => ∑ c, ∑ c', (α c * β c') * (w c * w c' * w j * w j) := by
    funext w
    rw [Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun c' _ => ?_
    ring
  rw [e]
  exact integrable_finsetSum _ fun c _ => integrable_finsetSum _ fun c' _ =>
    (hv_quad_int c c' j j).const_mul _

private lemma hv_lam_sq {n : ℕ} (μ : Fin n → ℝ) (hμ : ∀ k, 0 ≤ μ k) :
    lamHalf μ * (lamHalf μ)ᵀ = Matrix.diagonal μ := by
  unfold lamHalf
  rw [Matrix.diagonal_transpose, Matrix.diagonal_mul_diagonal]
  congr 1
  funext k
  exact Real.mul_self_sqrt (hμ k)

private lemma hv_col_form {n m : ℕ} (μ : Fin n → ℝ) (D : Matrix (Fin n) (Fin m) ℝ) (j : Fin m)
    (z : Fin n → ℝ) (w : Fin m → ℝ) (i : Fin n) :
    colSample μ D j (z, w) i = (lamHalf μ *ᵥ z) i * ((z ᵥ* (lamHalf μ * D)) ⬝ᵥ w * w j) := by
  simp only [colSample, resA]
  rw [Matrix.dotProduct_mulVec]
  ring

private lemma hv_col_sum {n m : ℕ} (μ : Fin n → ℝ) (D : Matrix (Fin n) (Fin m) ℝ) (j : Fin m)
    (z : Fin n → ℝ) (w : Fin m → ℝ) (i : Fin n) :
    colSample μ D j (z, w) i = ∑ a, ((lamHalf μ *ᵥ z) i * z a) *
      ∑ c, (lamHalf μ * D) a c * (w c * w j) := by
  simp only [colSample, resA]
  generalize (lamHalf μ *ᵥ z) i = yi
  simp only [dotProduct, Matrix.mulVec, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => ?_
  ring

private lemma hv_vecMul_col {n m : ℕ} (μ : Fin n → ℝ) (D : Matrix (Fin n) (Fin m) ℝ)
    (z : Fin n → ℝ) (a : Fin m) :
    (z ᵥ* (lamHalf μ * D)) a = (lamHalf μ *ᵥ z) ⬝ᵥ (fun k => D k a) := by
  simp only [Matrix.vecMul, dotProduct, lamHalf, Matrix.diagonal_mul, Matrix.mulVec_diagonal]
  exact Finset.sum_congr rfl fun k _ => by ring

private lemma hv_quad_expand {n m : ℕ} (D : Matrix (Fin n) (Fin m) ℝ) (j : Fin m)
    (M : Matrix (Fin n) (Fin n) ℝ) (hM : M = D * Dᵀ + (2 : ℝ) • Matrix.vecMulVec (fun k => D k j)
      (fun k => D k j)) (y : Fin n → ℝ) :
    ∑ a, (y ⬝ᵥ (fun k => D k a)) ^ 2 + 2 * (y ⬝ᵥ (fun k => D k j)) ^ 2
      = y ⬝ᵥ (M *ᵥ y) := by
  subst hM
  have hv : ∀ a, (Dᵀ *ᵥ y) a = y ⬝ᵥ (fun k => D k a) := fun a => by
    simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply]
    exact Finset.sum_congr rfl fun k _ => mul_comm _ _
  have h1 : y ⬝ᵥ ((D * Dᵀ) *ᵥ y) = ∑ a, (y ⬝ᵥ (fun k => D k a)) ^ 2 := by
    rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose]
    rw [dotProduct]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [hv a, sq]
  have h2 : y ⬝ᵥ (Matrix.vecMulVec (fun k => D k j) (fun k => D k j) *ᵥ y)
      = (y ⬝ᵥ (fun k => D k j)) ^ 2 := by
    simp only [dotProduct, Matrix.mulVec, Matrix.vecMulVec_apply, sq, Finset.sum_mul,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    ring
  rw [Matrix.add_mulVec, Matrix.smul_mulVec, dotProduct_add, dotProduct_smul, smul_eq_mul,
    h1, h2]

private lemma hv_fubini {n m : ℕ} (F : (Fin n → ℝ) × (Fin m → ℝ) → ℝ)
    (hF : Integrable F (Muon.SignSGD.gaussBatch n m)) :
    ∫ p, F p ∂(Muon.SignSGD.gaussBatch n m)
      = ∫ z, ∫ w, F (z, w) ∂(Muon.Foundations.stdGaussianPi m)
          ∂(Muon.Foundations.stdGaussianPi n) := by
  unfold Muon.SignSGD.gaussBatch at hF ⊢
  exact integral_prod F hF

private lemma hv_int_single {n m : ℕ} (μ : Fin n → ℝ) (D : Matrix (Fin n) (Fin m) ℝ) (j : Fin m)
    (i : Fin n) :
    Integrable (fun p : (Fin n → ℝ) × (Fin m → ℝ) => colSample μ D j p i)
      (Muon.SignSGD.gaussBatch n m) := by
  have e : (fun p : (Fin n → ℝ) × (Fin m → ℝ) => colSample μ D j p i)
      = fun p => ∑ a, ((lamHalf μ *ᵥ p.1) i * p.1 a) *
          ∑ c, (lamHalf μ * D) a c * (p.2 c * p.2 j) := by
    funext p
    exact hv_col_sum μ D j p.1 p.2 i
  rw [e]
  refine hv_single_int (fun a (z : Fin n → ℝ) => (lamHalf μ *ᵥ z) i * z a)
    (fun a (w : Fin m → ℝ) => ∑ c, (lamHalf μ * D) a c * (w c * w j)) ?_ ?_
  · intro a
    have e2 : (fun z : Fin n → ℝ => (lamHalf μ *ᵥ z) i * z a)
        = fun z => Real.sqrt (μ i) * (z i * z a) := by
      funext z
      simp only [lamHalf, Matrix.mulVec_diagonal]
      ring
    rw [e2]
    exact (hv_pair_int i a).const_mul _
  · intro a
    exact integrable_finsetSum _ fun c _ => (hv_pair_int c j).const_mul _

private lemma hv_int_pair {n m : ℕ} (μ : Fin n → ℝ) (D : Matrix (Fin n) (Fin m) ℝ) (j : Fin m)
    (i k : Fin n) :
    Integrable (fun p : (Fin n → ℝ) × (Fin m → ℝ) => colSample μ D j p i * colSample μ D j p k)
      (Muon.SignSGD.gaussBatch n m) := by
  have e : (fun p : (Fin n → ℝ) × (Fin m → ℝ) => colSample μ D j p i * colSample μ D j p k)
      = fun p => ∑ a, ∑ b, ((lamHalf μ *ᵥ p.1) i * p.1 a * ((lamHalf μ *ᵥ p.1) k * p.1 b)) *
          ((∑ c, (lamHalf μ * D) a c * (p.2 c * p.2 j)) * (∑ c, (lamHalf μ * D) b c * (p.2 c * p.2 j))) := by
    funext p
    rw [hv_col_sum μ D j p.1 p.2 i, hv_col_sum μ D j p.1 p.2 k, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    ring
  rw [e]
  refine hv_double_int
    (fun a b (z : Fin n → ℝ) => ((lamHalf μ *ᵥ z) i * z a) * ((lamHalf μ *ᵥ z) k * z b))
    (fun a b (w : Fin m → ℝ) => (∑ c, (lamHalf μ * D) a c * (w c * w j)) *
      (∑ c, (lamHalf μ * D) b c * (w c * w j))) ?_ ?_
  · intro a b
    have e2 : (fun z : Fin n → ℝ => ((lamHalf μ *ᵥ z) i * z a) * ((lamHalf μ *ᵥ z) k * z b))
        = fun z => (Real.sqrt (μ i) * Real.sqrt (μ k)) * (z i * z a * z k * z b) := by
      funext z
      simp only [lamHalf, Matrix.mulVec_diagonal]
      ring
    rw [e2]
    exact (hv_quad_int i a k b).const_mul _
  · intro a b
    exact hv_Lw_int (fun c => (lamHalf μ * D) a c) (fun c => (lamHalf μ * D) b c) j

private lemma hv_mean_single {n m : ℕ} (μ : Fin n → ℝ) (hμ : ∀ k, 0 ≤ μ k)
    (D : Matrix (Fin n) (Fin m) ℝ) (j : Fin m) (i : Fin n) :
    ∫ p, colSample μ D j p i ∂(Muon.SignSGD.gaussBatch n m) = colMeanVec μ D j i := by
  rw [hv_fubini _ (hv_int_single μ D j i)]
  have inner : ∀ z : Fin n → ℝ,
      ∫ w, colSample μ D j (z, w) i ∂(Muon.Foundations.stdGaussianPi m)
        = (lamHalf μ *ᵥ z) i * (z ᵥ* (lamHalf μ * D)) j := by
    intro z
    have e : (fun w => colSample μ D j (z, w) i)
        = fun w => (lamHalf μ *ᵥ z) i * (((z ᵥ* (lamHalf μ * D)) ⬝ᵥ w) * w j) := by
      funext w
      exact hv_col_form μ D j z w i
    rw [e, integral_const_mul, Muon.Foundations.gaussian_weighted_linear_moment]
  simp only [inner]
  have outer : ∀ z : Fin n → ℝ, (lamHalf μ *ᵥ z) i * (z ᵥ* (lamHalf μ * D)) j
      = Real.sqrt (μ i) * (((fun k => Real.sqrt (μ k) * D k j) ⬝ᵥ z) * z i) := by
    intro z
    rw [hv_vecMul_col]
    simp only [lamHalf, Matrix.mulVec_diagonal, dotProduct, Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun k _ => by ring
  simp only [outer]
  rw [integral_const_mul]
  simp only [Muon.Foundations.gaussian_weighted_linear_moment]
  rw [← mul_assoc, Real.mul_self_sqrt (hμ i)]
  rfl

private lemma hv_trace {n m : ℕ} (μ : Fin n → ℝ) (D : Matrix (Fin n) (Fin m) ℝ) (j : Fin m)
    (M : Matrix (Fin n) (Fin n) ℝ)
    (hM : M = D * Dᵀ + (2 : ℝ) • Matrix.vecMulVec (fun k => D k j) (fun k => D k j)) :
    (Matrix.diagonal μ * M).trace = twoR μ D + 2 * colC μ D j := by
  subst hM
  unfold twoR colC Matrix.trace
  simp only [Matrix.diag, Matrix.diagonal_mul, Matrix.add_apply, Matrix.smul_apply,
    Matrix.mul_apply, Matrix.transpose_apply, Matrix.vecMulVec_apply, smul_eq_mul,
    Finset.mul_sum, Finset.sum_add_distrib, mul_add, sq, Finset.mul_sum, Matrix.diagonal_apply,
    ite_mul, zero_mul, Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  congr 1
  exact Finset.sum_congr rfl fun x _ => by ring

private lemma hv_sand {n m : ℕ} (μ : Fin n → ℝ) (D : Matrix (Fin n) (Fin m) ℝ) (j : Fin m)
    (M : Matrix (Fin n) (Fin n) ℝ)
    (hM : M = D * Dᵀ + (2 : ℝ) • Matrix.vecMulVec (fun k => D k j) (fun k => D k j))
    (i k : Fin n) :
    (Matrix.diagonal μ * M * Matrix.diagonal μ) i k
      = TD μ D i k + 2 * (colMeanVec μ D j i * colMeanVec μ D j k) := by
  subst hM
  simp only [TD, colMeanVec, Matrix.mul_add, Matrix.add_mul, Matrix.mul_diagonal,
    Matrix.diagonal_mul, Matrix.add_apply, Matrix.smul_apply, Matrix.vecMulVec_apply,
    smul_eq_mul]
  ring

private lemma hv_second_single {n m : ℕ} (μ : Fin n → ℝ) (hμ : ∀ k, 0 ≤ μ k)
    (D : Matrix (Fin n) (Fin m) ℝ) (j : Fin m) (i k : Fin n) :
    ∫ p, colSample μ D j p i * colSample μ D j p k ∂(Muon.SignSGD.gaussBatch n m) =
      (twoR μ D + 2 * colC μ D j) * Matrix.diagonal μ i k + 2 * TD μ D i k
        + 4 * (colMeanVec μ D j i * colMeanVec μ D j k) := by
  rw [hv_fubini _ (hv_int_pair μ D j i k)]
  obtain ⟨Mq, hMq⟩ : ∃ M : Matrix (Fin n) (Fin n) ℝ,
      M = D * Dᵀ + (2 : ℝ) • Matrix.vecMulVec (fun k => D k j) (fun k => D k j) := ⟨_, rfl⟩
  have inner : ∀ z : Fin n → ℝ,
      ∫ w, colSample μ D j (z, w) i * colSample μ D j (z, w) k
          ∂(Muon.Foundations.stdGaussianPi m)
        = ((lamHalf μ *ᵥ z) i * (lamHalf μ *ᵥ z) k) *
          ((∑ a, (z ᵥ* (lamHalf μ * D)) a ^ 2) + 2 * (z ᵥ* (lamHalf μ * D)) j ^ 2) := by
    intro z
    have e : (fun w => colSample μ D j (z, w) i * colSample μ D j (z, w) k)
        = fun w => ((lamHalf μ *ᵥ z) i * (lamHalf μ *ᵥ z) k) *
            (((z ᵥ* (lamHalf μ * D)) ⬝ᵥ w) ^ 2 * w j ^ 2) := by
      funext w
      rw [hv_col_form, hv_col_form]
      ring
    rw [e, integral_const_mul, Muon.Foundations.gaussian_weighted_square_moment]
  simp only [inner]
  have outer : ∀ z : Fin n → ℝ,
      ((lamHalf μ *ᵥ z) i * (lamHalf μ *ᵥ z) k) *
          ((∑ a, (z ᵥ* (lamHalf μ * D)) a ^ 2) + 2 * (z ᵥ* (lamHalf μ * D)) j ^ 2)
        = (lamHalf μ *ᵥ z) i * (lamHalf μ *ᵥ z) k *
          ((lamHalf μ *ᵥ z) ⬝ᵥ (Mq *ᵥ (lamHalf μ *ᵥ z))) := by
    intro z
    rw [← hv_quad_expand D j Mq hMq (lamHalf μ *ᵥ z)]
    simp only [hv_vecMul_col]
  simp only [outer]
  have hΛ : Matrix.diagonal μ = lamHalf μ * (lamHalf μ)ᵀ := (hv_lam_sq μ hμ).symm
  have hMsymm : Mqᵀ = Mq := by
    rw [hMq]
    ext a b
    simp only [Matrix.transpose_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.mul_apply,
      Matrix.vecMulVec_apply, smul_eq_mul]
    congr 1
    · exact Finset.sum_congr rfl fun k _ => mul_comm _ _
    · ring
  have hq := Muon.Foundations.gaussian_quartic_covariance n (lamHalf μ) Mq (Matrix.diagonal μ)
    hΛ hMsymm (Muon.Foundations.stdGaussianPi n) (fun z => lamHalf μ *ᵥ z) rfl
    (by fun_prop : Measurable (fun z : Fin n → ℝ => lamHalf μ *ᵥ z)).aemeasurable i k
  beta_reduce at hq
  rw [hq, hv_trace μ D j Mq hMq, hv_sand μ D j Mq hMq i k]
  ring

/-- **lem:app-sgd-column**, part (i): the mean and the covariance of one column sample
`X`, namely `E X = m_j` and `V_j = E[Z ⊗ Z]`.

cr-2026-10-23. LaTeX statement (verbatim):
\begin{lemma}[Column moments]
There are admissible constants $V_0$, $A_4$, $A_8$ such that, for every column $j$,
\begin{align}
\EE X&=m_j,\qquad V_j\defeq\EE[Z\tensor Z]=(2\cR+2C_j)\Lambda+2T_D+3\,m_j\tensor m_j,\\
\EE[h_j\tensor h_j]&=\frac{2\cR+2C_j}B\,\Lambda+\frac2B\,T_D+\Big(1+\frac3B\Big)m_j\tensor m_j,\\
\EE[HH^\T]&=\frac{2\cR\,(\Nin+2)}B\,\Lambda+\Big(1+\frac{2\Nin+3}B\Big)T_D,
\end{align}
with $C_j=D_{\cdot j}^\T\Lambda D_{\cdot j}$, and
\begin{gather}
V_j\succeq2\cR\,\Lambda,\qquad \norm{V_j}\le V_0,\qquad \norm{m_j}^2\le\frac{L^2C_{\rm col}}k,\\
\EE\abs{a^\T Z}^4\le A_4\norm a^4,\quad \EE\abs{a^\T Z}^8\le A_8\norm a^8\quad(a\in\R^{\Nout}),\\
\EE\norm Z^4\le A_4\Nout^2,\quad \EE\norm Z^8\le A_8\Nout^4 .
\end{gather}
Every column $h_j$ is nonzero almost surely.
\end{lemma}
-/
theorem lem_app_sgd_column_i (P : HaarParams) {n m B : ℕ} (μ : Fin n → ℝ)
    (D : Matrix (Fin n) (Fin m) ℝ) (hP : def_app_sgd_state_law P n m B μ D) (j : Fin m) :
    (∀ i, ∫ p, colSample μ D j p i ∂(gaussBatch n m) = colMeanVec μ D j i) ∧
    ∀ i k, colCov μ D j i k = (twoR μ D + 2 * colC μ D j) * Matrix.diagonal μ i k
      + 2 * TD μ D i k + 3 * (colMeanVec μ D j i * colMeanVec μ D j k) := by
  have hμ : ∀ k, 0 ≤ μ k := fun k => le_trans P.c_pos.le (hP.2.2.2.2.2.1 k).1
  refine ⟨fun i => hv_mean_single μ hμ D j i, fun i k => ?_⟩
  have : IsProbabilityMeasure (gaussBatch n m) := by unfold gaussBatch; infer_instance
  have hcov : colCov μ D j i k = ∫ p, (colSample μ D j p i * colSample μ D j p k
      - colMeanVec μ D j k * colSample μ D j p i - colMeanVec μ D j i * colSample μ D j p k
      + colMeanVec μ D j i * colMeanVec μ D j k) ∂(gaussBatch n m) := by
    unfold colCov
    rw [Matrix.of_apply]
    congr 1
    funext p
    simp only [colZ, Pi.sub_apply]
    ring
  have I1 := hv_int_pair μ D j i k
  have I2 := (hv_int_single μ D j i).const_mul (colMeanVec μ D j k)
  have I3 := (hv_int_single μ D j k).const_mul (colMeanVec μ D j i)
  have I4 : Integrable (fun _ : (Fin n → ℝ) × (Fin m → ℝ) =>
      colMeanVec μ D j i * colMeanVec μ D j k) (gaussBatch n m) := integrable_const _
  rw [hcov, integral_add, integral_sub, integral_sub, integral_const_mul, integral_const_mul,
    hv_mean_single μ hμ D j i, hv_mean_single μ hμ D j k, hv_second_single μ hμ D j i k]
  · simp only [integral_const, probReal_univ, one_smul]
    ring
  all_goals first
    | exact I1 | exact I2 | exact I3 | exact I4 | exact I1.sub I2 | exact (I1.sub I2).sub I3
    | exact integrable_const _ | exact (hv_int_single μ D j i) | exact (hv_int_single μ D j k)

/-- **lem:app-sgd-column**, part (ii): the covariance of the column mean `h_j`,
`E[h_j ⊗ h_j]` (`eqn:app-sgd-hh`).

cr-2026-10-23. LaTeX statement (verbatim):
\begin{lemma}[Column moments]
There are admissible constants $V_0$, $A_4$, $A_8$ such that, for every column $j$,
\begin{align}
\EE X&=m_j,\qquad V_j\defeq\EE[Z\tensor Z]=(2\cR+2C_j)\Lambda+2T_D+3\,m_j\tensor m_j,\\
\EE[h_j\tensor h_j]&=\frac{2\cR+2C_j}B\,\Lambda+\frac2B\,T_D+\Big(1+\frac3B\Big)m_j\tensor m_j,\\
\EE[HH^\T]&=\frac{2\cR\,(\Nin+2)}B\,\Lambda+\Big(1+\frac{2\Nin+3}B\Big)T_D,
\end{align}
with $C_j=D_{\cdot j}^\T\Lambda D_{\cdot j}$, and
\begin{gather}
V_j\succeq2\cR\,\Lambda,\qquad \norm{V_j}\le V_0,\qquad \norm{m_j}^2\le\frac{L^2C_{\rm col}}k,\\
\EE\abs{a^\T Z}^4\le A_4\norm a^4,\quad \EE\abs{a^\T Z}^8\le A_8\norm a^8\quad(a\in\R^{\Nout}),\\
\EE\norm Z^4\le A_4\Nout^2,\quad \EE\norm Z^8\le A_8\Nout^4 .
\end{gather}
Every column $h_j$ is nonzero almost surely.
\end{lemma}
-/
theorem lem_app_sgd_column_ii (P : HaarParams) {n m B : ℕ} (μ : Fin n → ℝ)
    (D : Matrix (Fin n) (Fin m) ℝ) (hP : def_app_sgd_state_law P n m B μ D) (j : Fin m) :
    ∀ i k, ∫ β, hCol μ D β j i * hCol μ D β j k ∂(batchLaw n m B) =
      (twoR μ D + 2 * colC μ D j) / (B : ℝ) * Matrix.diagonal μ i k
        + 2 / (B : ℝ) * TD μ D i k
        + (1 + 3 / (B : ℝ)) * (colMeanVec μ D j i * colMeanVec μ D j k) := by
  have hμ : ∀ k, 0 ≤ μ k := fun k => le_trans P.c_pos.le (hP.2.2.2.2.2.1 k).1
  have hBpos : 0 < B := hP.1.2.2
  have hB : (B : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hBpos.ne'
  have : IsProbabilityMeasure (gaussBatch n m) := by unfold gaussBatch; infer_instance
  intro i k
  have hexp : (fun β : Fin B → (Fin n → ℝ) × (Fin m → ℝ) => hCol μ D β j i * hCol μ D β j k)
      = fun β => (1 / (B : ℝ)) ^ 2 *
          ∑ a, ∑ b, colSample μ D j (β a) i * colSample μ D j (β b) k := by
    funext β
    simp only [hCol]
    rw [mul_mul_mul_comm, Finset.sum_mul_sum]
    ring
  have hmeas : ∀ l : Fin n, Measurable (fun p : (Fin n → ℝ) × (Fin m → ℝ) => colSample μ D j p l) := by
    intro l
    unfold colSample resA
    fun_prop
  have hTint : ∀ a b : Fin B, Integrable (fun β : Fin B → (Fin n → ℝ) × (Fin m → ℝ) =>
      colSample μ D j (β a) i * colSample μ D j (β b) k) (batchLaw n m B) := by
    intro a b
    unfold batchLaw
    by_cases hab : a = b
    · subst hab
      exact integrable_comp_eval (μ := fun _ : Fin B => gaussBatch n m) (i := a)
        (hv_int_pair μ D j i k)
    · have hind0 : IndepFun (fun β : Fin B → (Fin n → ℝ) × (Fin m → ℝ) => β a)
          (fun β => β b) (Measure.pi fun _ : Fin B => gaussBatch n m) :=
        (iIndepFun_pi (μ := fun _ : Fin B => gaussBatch n m)
          (X := fun _ => (id : (Fin n → ℝ) × (Fin m → ℝ) → (Fin n → ℝ) × (Fin m → ℝ)))
          (fun _ => measurable_id.aemeasurable)).indepFun hab
      have hind := hind0.comp (hmeas i) (hmeas k)
      have hX := integrable_comp_eval (μ := fun _ : Fin B => gaussBatch n m) (i := a)
        (hv_int_single μ D j i)
      have hY := integrable_comp_eval (μ := fun _ : Fin B => gaussBatch n m) (i := b)
        (hv_int_single μ D j k)
      exact hind.integrable_mul hX hY
  have hTval : ∀ a b : Fin B,
      ∫ β, colSample μ D j (β a) i * colSample μ D j (β b) k ∂(batchLaw n m B)
        = if a = b then (twoR μ D + 2 * colC μ D j) * Matrix.diagonal μ i k + 2 * TD μ D i k
            + 4 * (colMeanVec μ D j i * colMeanVec μ D j k)
          else colMeanVec μ D j i * colMeanVec μ D j k := by
    intro a b
    unfold batchLaw
    by_cases hab : a = b
    · subst hab
      have h1 : ∫ β, colSample μ D j (β a) i * colSample μ D j (β a) k
          ∂(Measure.pi fun _ : Fin B => gaussBatch n m)
          = ∫ p, colSample μ D j p i * colSample μ D j p k ∂(gaussBatch n m) :=
        integral_comp_eval (μ := fun _ : Fin B => gaussBatch n m) (i := a)
          (hv_int_pair μ D j i k).aestronglyMeasurable
      rw [if_pos rfl, h1]
      exact hv_second_single μ hμ D j i k
    · rw [if_neg hab]
      have hfi : ∫ β, colSample μ D j (β a) i ∂(Measure.pi fun _ : Fin B => gaussBatch n m)
          = colMeanVec μ D j i :=
        (integral_comp_eval (μ := fun _ : Fin B => gaussBatch n m) (i := a)
          (hmeas i).aestronglyMeasurable).trans (hv_mean_single μ hμ D j i)
      have hfk : ∫ β, colSample μ D j (β b) k ∂(Measure.pi fun _ : Fin B => gaussBatch n m)
          = colMeanVec μ D j k :=
        (integral_comp_eval (μ := fun _ : Fin B => gaussBatch n m) (i := b)
          (hmeas k).aestronglyMeasurable).trans (hv_mean_single μ hμ D j k)
      have hind0 : IndepFun (fun β : Fin B → (Fin n → ℝ) × (Fin m → ℝ) => β a)
          (fun β => β b) (Measure.pi fun _ : Fin B => gaussBatch n m) :=
        (iIndepFun_pi (μ := fun _ : Fin B => gaussBatch n m)
          (X := fun _ => (id : (Fin n → ℝ) × (Fin m → ℝ) → (Fin n → ℝ) × (Fin m → ℝ)))
          (fun _ => measurable_id.aemeasurable)).indepFun hab
      have hind := hind0.comp (hmeas i) (hmeas k)
      have hX := integrable_comp_eval (μ := fun _ : Fin B => gaussBatch n m) (i := a)
        (hv_int_single μ D j i)
      have hY := integrable_comp_eval (μ := fun _ : Fin B => gaussBatch n m) (i := b)
        (hv_int_single μ D j k)
      have hprod : ∫ β, colSample μ D j (β a) i * colSample μ D j (β b) k
          ∂(Measure.pi fun _ : Fin B => gaussBatch n m)
          = (∫ β, colSample μ D j (β a) i ∂(Measure.pi fun _ : Fin B => gaussBatch n m))
            * (∫ β, colSample μ D j (β b) k ∂(Measure.pi fun _ : Fin B => gaussBatch n m)) :=
        hind.integral_mul_eq_mul_integral hX.aestronglyMeasurable hY.aestronglyMeasurable
      rw [hprod, hfi, hfk]
  have hsumE : ∀ a : Fin B, ∑ b : Fin B,
      (if a = b then (twoR μ D + 2 * colC μ D j) * Matrix.diagonal μ i k + 2 * TD μ D i k
            + 4 * (colMeanVec μ D j i * colMeanVec μ D j k)
          else colMeanVec μ D j i * colMeanVec μ D j k)
        = ((twoR μ D + 2 * colC μ D j) * Matrix.diagonal μ i k + 2 * TD μ D i k
            + 4 * (colMeanVec μ D j i * colMeanVec μ D j k) - colMeanVec μ D j i * colMeanVec μ D j k)
          + (B : ℝ) * (colMeanVec μ D j i * colMeanVec μ D j k) := by
    intro a
    have hw : ∀ b : Fin B, (if a = b then (twoR μ D + 2 * colC μ D j) * Matrix.diagonal μ i k
            + 2 * TD μ D i k + 4 * (colMeanVec μ D j i * colMeanVec μ D j k)
          else colMeanVec μ D j i * colMeanVec μ D j k)
        = (if a = b then (twoR μ D + 2 * colC μ D j) * Matrix.diagonal μ i k
            + 2 * TD μ D i k + 4 * (colMeanVec μ D j i * colMeanVec μ D j k)
            - colMeanVec μ D j i * colMeanVec μ D j k else 0)
          + colMeanVec μ D j i * colMeanVec μ D j k := by
      intro b
      split_ifs <;> ring
    simp only [hw, Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, ite_true,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hsumint : ∫ β, ∑ a, ∑ b, colSample μ D j (β a) i * colSample μ D j (β b) k
      ∂(batchLaw n m B)
      = ∑ a, ∑ b, ∫ β, colSample μ D j (β a) i * colSample μ D j (β b) k ∂(batchLaw n m B) := by
    rw [integral_finsetSum _ (fun a _ => integrable_finsetSum _ fun b _ => hTint a b)]
    exact Finset.sum_congr rfl fun a _ => integral_finsetSum _ fun b _ => hTint a b
  rw [hexp, integral_const_mul, hsumint]
  simp only [hTval, hsumE, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp
  ring

private lemma hv_hcol_pair_int {n m B : ℕ} (μ : Fin n → ℝ)
    (D : Matrix (Fin n) (Fin m) ℝ) (j : Fin m) (i k : Fin n) :
    Integrable (fun β => hCol μ D β j i * hCol μ D β j k) (batchLaw n m B) := by
  have : IsProbabilityMeasure (gaussBatch n m) := by unfold gaussBatch; infer_instance
  have hmeas : ∀ l : Fin n, Measurable (fun p : (Fin n → ℝ) × (Fin m → ℝ) => colSample μ D j p l) := by
    intro l
    unfold colSample resA
    fun_prop
  have hTint : ∀ a b : Fin B, Integrable (fun β : Fin B → (Fin n → ℝ) × (Fin m → ℝ) =>
      colSample μ D j (β a) i * colSample μ D j (β b) k) (batchLaw n m B) := by
    intro a b
    unfold batchLaw
    by_cases hab : a = b
    · subst hab
      exact integrable_comp_eval (μ := fun _ : Fin B => gaussBatch n m) (i := a)
        (hv_int_pair μ D j i k)
    · have hind0 : IndepFun (fun β : Fin B → (Fin n → ℝ) × (Fin m → ℝ) => β a)
          (fun β => β b) (Measure.pi fun _ : Fin B => gaussBatch n m) :=
        (iIndepFun_pi (μ := fun _ : Fin B => gaussBatch n m)
          (X := fun _ => (id : (Fin n → ℝ) × (Fin m → ℝ) → (Fin n → ℝ) × (Fin m → ℝ)))
          (fun _ => measurable_id.aemeasurable)).indepFun hab
      have hind := hind0.comp (hmeas i) (hmeas k)
      have hX := integrable_comp_eval (μ := fun _ : Fin B => gaussBatch n m) (i := a)
        (hv_int_single μ D j i)
      have hY := integrable_comp_eval (μ := fun _ : Fin B => gaussBatch n m) (i := b)
        (hv_int_single μ D j k)
      exact hind.integrable_mul hX hY
  have hexp : (fun β : Fin B → (Fin n → ℝ) × (Fin m → ℝ) => hCol μ D β j i * hCol μ D β j k)
      = fun β => (1 / (B : ℝ)) ^ 2 *
          ∑ a, ∑ b, colSample μ D j (β a) i * colSample μ D j (β b) k := by
    funext β
    simp only [hCol]
    rw [mul_mul_mul_comm, Finset.sum_mul_sum]
    ring
  rw [hexp]
  exact (integrable_finsetSum _ fun a _ => integrable_finsetSum _ fun b _ => hTint a b).const_mul _

/-- **lem:app-sgd-column**, part (iii): `E[H Hᵀ]` (`eqn:app-sgd-HH`).

cr-2026-10-23. LaTeX statement (verbatim):
\begin{lemma}[Column moments]
There are admissible constants $V_0$, $A_4$, $A_8$ such that, for every column $j$,
\begin{align}
\EE X&=m_j,\qquad V_j\defeq\EE[Z\tensor Z]=(2\cR+2C_j)\Lambda+2T_D+3\,m_j\tensor m_j,\\
\EE[h_j\tensor h_j]&=\frac{2\cR+2C_j}B\,\Lambda+\frac2B\,T_D+\Big(1+\frac3B\Big)m_j\tensor m_j,\\
\EE[HH^\T]&=\frac{2\cR\,(\Nin+2)}B\,\Lambda+\Big(1+\frac{2\Nin+3}B\Big)T_D,
\end{align}
with $C_j=D_{\cdot j}^\T\Lambda D_{\cdot j}$, and
\begin{gather}
V_j\succeq2\cR\,\Lambda,\qquad \norm{V_j}\le V_0,\qquad \norm{m_j}^2\le\frac{L^2C_{\rm col}}k,\\
\EE\abs{a^\T Z}^4\le A_4\norm a^4,\quad \EE\abs{a^\T Z}^8\le A_8\norm a^8\quad(a\in\R^{\Nout}),\\
\EE\norm Z^4\le A_4\Nout^2,\quad \EE\norm Z^8\le A_8\Nout^4 .
\end{gather}
Every column $h_j$ is nonzero almost surely.
\end{lemma}
-/
theorem lem_app_sgd_column_iii (P : HaarParams) {n m B : ℕ} (μ : Fin n → ℝ)
    (D : Matrix (Fin n) (Fin m) ℝ) (hP : def_app_sgd_state_law P n m B μ D) :
    ∀ i k, ∫ β, (hMatrix μ D β * (hMatrix μ D β)ᵀ) i k ∂(batchLaw n m B) =
      twoR μ D * ((m : ℝ) + 2) / (B : ℝ) * Matrix.diagonal μ i k
        + (1 + (2 * (m : ℝ) + 3) / (B : ℝ)) * TD μ D i k := by
  intro i k
  have hC : ∑ j, colC μ D j = twoR μ D := by
    unfold colC twoR
    simp only [Matrix.diagonal_mul, Matrix.trace, Matrix.diag]
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Finset.mul_sum, sq]
    rw [Finset.sum_comm]
  have hM : ∑ j, colMeanVec μ D j i * colMeanVec μ D j k = TD μ D i k := by
    unfold colMeanVec TD
    simp only [Matrix.mul_diagonal, Matrix.diagonal_mul]
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun j _ => by ring
  change (∫ β, ∑ j, hCol μ D β j i * hCol μ D β j k ∂(batchLaw n m B)) = _
  rw [integral_finsetSum _ (fun j _ => hv_hcol_pair_int μ D j i k)]
  simp_rw [lem_app_sgd_column_ii P μ D hP]
  simp only [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum,
    ← Finset.sum_div, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [hC, hM]
  ring

private lemma hv_row_witness {Nin : ℕ} (r : Fin Nin → ℝ) (hr : r ≠ 0) (j : Fin Nin) :
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
private lemma hv_exists_point {Nout Nin : ℕ} (Δ : Matrix (Fin Nout) (Fin Nin) ℝ) (hΔ : Δ ≠ 0)
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
    obtain ⟨x, hxj, hx⟩ := hv_row_witness (fun l => Δ k l) hk j
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
    obtain ⟨x, hxj, hx⟩ := hv_row_witness (fun l => Δ i l) hr j
    refine ⟨Pi.single i 1, x, ?_⟩
    have hdot : dotProduct (Pi.single i 1 : Fin Nout → ℝ) (Δ.mulVec x)
        = dotProduct (fun l => Δ i l) x := by
      rw [single_dotProduct]
      simp [Matrix.mulVec, dotProduct]
    rw [hdot, Pi.single_eq_same]
    exact mul_ne_zero (mul_ne_zero one_ne_zero hxj) hx

private lemma hv_gauss_atomless {n m : ℕ} (A : Matrix (Fin n) (Fin m) ℝ) (hA : A ≠ 0)
    (i : Fin n) (j : Fin m) (c : ℝ) :
    gaussBatch n m {p | sgdCoord A i j p = c} = 0 := by
  classical
  let glue : ((Fin n → ℝ) × (Fin m → ℝ)) ≃ᵐ (Fin (n + m) → ℝ) :=
    (MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin n ⊕ Fin m => ℝ)).symm.trans
      (MeasurableEquiv.piCongrLeft (fun _ : Fin (n + m) => ℝ) finSumFinEquiv)
  have hleft (p : (Fin n → ℝ) × (Fin m → ℝ)) (k : Fin n) :
      glue p (finSumFinEquiv (Sum.inl k)) = p.1 k := by
    change (Equiv.piCongrLeft (fun _ : Fin (n + m) => ℝ) finSumFinEquiv)
      ((MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin n ⊕ Fin m => ℝ)).symm p)
      (finSumFinEquiv (Sum.inl k)) = p.1 k
    rw [Equiv.piCongrLeft_apply_apply]
    rfl
  have hright (p : (Fin n → ℝ) × (Fin m → ℝ)) (l : Fin m) :
      glue p (finSumFinEquiv (Sum.inr l)) = p.2 l := by
    change (Equiv.piCongrLeft (fun _ : Fin (n + m) => ℝ) finSumFinEquiv)
      ((MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin n ⊕ Fin m => ℝ)).symm p)
      (finSumFinEquiv (Sum.inr l)) = p.2 l
    rw [Equiv.piCongrLeft_apply_apply]
    rfl
  have hmp : MeasurePreserving glue (gaussBatch n m)
      (Muon.Foundations.stdGaussianPi (n + m)) :=
    (measurePreserving_sumPiEquivProdPi_symm
      (fun _ : Fin n ⊕ Fin m => gaussianReal 0 1)).trans
      (measurePreserving_piCongrLeft (α := fun _ : Fin (n + m) => ℝ)
        (fun _ => gaussianReal 0 1) finSumFinEquiv)
  let poly : MvPolynomial (Fin (n + m)) ℝ :=
    (∑ k, ∑ l, MvPolynomial.C (A k l) * MvPolynomial.X (finSumFinEquiv (Sum.inl k))
      * MvPolynomial.X (finSumFinEquiv (Sum.inr l)))
    * MvPolynomial.X (finSumFinEquiv (Sum.inl i))
    * MvPolynomial.X (finSumFinEquiv (Sum.inr j)) - MvPolynomial.C c
  have heval (p : (Fin n → ℝ) × (Fin m → ℝ)) :
      MvPolynomial.eval (glue p) poly = sgdCoord A i j p - c := by
    simp only [poly, sgdCoord, map_sub, map_mul, map_sum, MvPolynomial.eval_C,
      MvPolynomial.eval_X, hleft, hright, dotProduct, Matrix.mulVec]
    congr 1
    congr 2
    simp only [Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring
  have hp : poly ≠ 0 := by
    intro hz
    have h0 := heval (0, 0)
    rw [hz] at h0
    have hc : c = 0 := by simpa [sgdCoord] using h0
    obtain ⟨y, x, hyx⟩ := hv_exists_point A hA i j
    have h1 := heval (y, x)
    rw [hz, hc] at h1
    apply hyx
    simpa [sgdCoord, mul_comm, mul_left_comm, mul_assoc] using h1.symm
  have hnull := (Muon.Foundations.poly_zero_set_null (n + m) poly hp).2.2
  have hset : {p | sgdCoord A i j p = c} = glue ⁻¹' {x | MvPolynomial.eval x poly = 0} := by
    ext p
    simp only [Set.mem_setOf_eq, Set.mem_preimage, heval, sub_eq_zero]
  have hms : MeasurableSet {x : Fin (n + m) → ℝ | MvPolynomial.eval x poly = 0} :=
    (isClosed_eq (MvPolynomial.continuous_eval _) continuous_const).measurableSet
  rw [hset, hmp.measure_preimage hms.nullMeasurableSet]
  exact hnull

private lemma hv_pi_sum_null {α : Type*} [MeasurableSpace α] (μ : Measure α)
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

/-- **lem:app-sgd-column**, part (iv): every column `h_j` is nonzero almost surely.

cr-2026-10-23. LaTeX statement (verbatim):
\begin{lemma}[Column moments]
There are admissible constants $V_0$, $A_4$, $A_8$ such that, for every column $j$,
\begin{align}
\EE X&=m_j,\qquad V_j\defeq\EE[Z\tensor Z]=(2\cR+2C_j)\Lambda+2T_D+3\,m_j\tensor m_j,\\
\EE[h_j\tensor h_j]&=\frac{2\cR+2C_j}B\,\Lambda+\frac2B\,T_D+\Big(1+\frac3B\Big)m_j\tensor m_j,\\
\EE[HH^\T]&=\frac{2\cR\,(\Nin+2)}B\,\Lambda+\Big(1+\frac{2\Nin+3}B\Big)T_D,
\end{align}
with $C_j=D_{\cdot j}^\T\Lambda D_{\cdot j}$, and
\begin{gather}
V_j\succeq2\cR\,\Lambda,\qquad \norm{V_j}\le V_0,\qquad \norm{m_j}^2\le\frac{L^2C_{\rm col}}k,\\
\EE\abs{a^\T Z}^4\le A_4\norm a^4,\quad \EE\abs{a^\T Z}^8\le A_8\norm a^8\quad(a\in\R^{\Nout}),\\
\EE\norm Z^4\le A_4\Nout^2,\quad \EE\norm Z^8\le A_8\Nout^4 .
\end{gather}
Every column $h_j$ is nonzero almost surely.
\end{lemma}
-/
theorem lem_app_sgd_column_iv (P : HaarParams) {n m B : ℕ} (μ : Fin n → ℝ)
    (D : Matrix (Fin n) (Fin m) ℝ) (hP : def_app_sgd_state_law P n m B μ D) (j : Fin m) :
    ∀ᵐ β ∂(batchLaw n m B), hCol μ D β j ≠ 0 := by
  classical
  have hμ : ∀ k, 0 < μ k := fun k => P.c_pos.trans_le (hP.2.2.2.2.2.1 k).1
  have hD : D ≠ 0 := by
    intro hz
    have hF : 0 < frobNorm D := P.fMin_pos.trans_le hP.2.2.2.2.2.2.1
    simpa [hz, frobNorm] using hF
  have hA : lamHalf μ * D ≠ 0 := by
    intro hz
    apply hD
    ext k l
    have he := congrArg (fun M : Matrix (Fin n) (Fin m) ℝ => M k l) hz
    simp only [lamHalf, Matrix.diagonal_mul, Matrix.zero_apply] at he
    exact (mul_eq_zero.mp he).resolve_left (Real.sqrt_pos.mpr (hμ k)).ne'
  let i : Fin n := ⟨0, hP.1.1⟩
  have hprob : IsProbabilityMeasure (gaussBatch n m) := by unfold gaussBatch; infer_instance
  have hf : Measurable (sgdCoord (lamHalf μ * D) i j) := by
    unfold sgdCoord
    fun_prop
  have hnull := hv_pi_sum_null (gaussBatch n m) (sgdCoord (lamHalf μ * D) i j) hf
    (hv_gauss_atomless (lamHalf μ * D) hA i j) hP.1.2.2
  have heq (β : Fin B → (Fin n → ℝ) × (Fin m → ℝ)) :
      hCol μ D β j i = ((1 / (B : ℝ)) * Real.sqrt (μ i)) *
        ∑ a, sgdCoord (lamHalf μ * D) i j (β a) := by
    simp only [hCol, colSample, resA, lamHalf, Matrix.mulVec_diagonal, sgdCoord,
      Finset.mul_sum]
    exact Finset.sum_congr rfl fun a _ => by ring
  rw [ae_iff]
  refine measure_mono_null (fun β hβ => ?_) hnull
  simp only [Set.mem_setOf_eq, not_not] at hβ ⊢
  have hz := congrFun hβ i
  rw [heq] at hz
  exact (mul_eq_zero.mp hz).resolve_left (mul_ne_zero
    (one_div_ne_zero (Nat.cast_ne_zero.mpr hP.1.2.2.ne')) (Real.sqrt_pos.mpr (hμ i)).ne')

private lemma hv_TD_psd {n m : ℕ} (μ : Fin n → ℝ)
    (D : Matrix (Fin n) (Fin m) ℝ) : (TD μ D).PosSemidef := by
  have h := Matrix.posSemidef_self_mul_conjTranspose (Matrix.diagonal μ * D)
  have e : TD μ D = (Matrix.diagonal μ * D) * (Matrix.diagonal μ * D)ᴴ := by
    unfold TD
    rw [Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.transpose_mul,
      Matrix.diagonal_transpose]
    simp only [Matrix.mul_assoc]
  rw [e]
  exact h

private lemma hv_colC_bounds (P : HaarParams) {n m B : ℕ} (μ : Fin n → ℝ)
    (D : Matrix (Fin n) (Fin m) ℝ) (hP : def_app_sgd_state_law P n m B μ D)
    (j : Fin m) :
    0 ≤ colC μ D j ∧ colC μ D j ≤ P.L * P.Ccol / (kOf n m B : ℝ) := by
  have hL : 0 ≤ P.L := P.c_pos.le.trans P.c_le_L
  have hμ := hP.2.2.2.2.2.1
  refine ⟨Finset.sum_nonneg fun i _ =>
    mul_nonneg (P.c_pos.le.trans (hμ i).1) (sq_nonneg _), ?_⟩
  calc
    colC μ D j ≤ ∑ i, P.L * D i j ^ 2 :=
      Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hμ i).2 (sq_nonneg _)
    _ = P.L * ∑ i, D i j ^ 2 := (Finset.mul_sum _ _ _).symm
    _ ≤ P.L * (P.Ccol / (kOf n m B : ℝ)) :=
      mul_le_mul_of_nonneg_left (hP.2.2.2.2.2.2.2.2 j) hL
    _ = P.L * P.Ccol / (kOf n m B : ℝ) := by ring

private lemma hv_mean_sq_bound (P : HaarParams) {n m B : ℕ} (μ : Fin n → ℝ)
    (D : Matrix (Fin n) (Fin m) ℝ) (hP : def_app_sgd_state_law P n m B μ D)
    (j : Fin m) :
    ∑ i, colMeanVec μ D j i ^ 2 ≤ P.L ^ 2 * P.Ccol / (kOf n m B : ℝ) := by
  have hμ := hP.2.2.2.2.2.1
  calc
    ∑ i, colMeanVec μ D j i ^ 2 ≤ ∑ i, P.L ^ 2 * D i j ^ 2 := by
      refine Finset.sum_le_sum fun i _ => ?_
      rw [colMeanVec, mul_pow]
      exact mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (P.c_pos.le.trans (hμ i).1) (hμ i).2 2) (sq_nonneg _)
    _ = P.L ^ 2 * ∑ i, D i j ^ 2 := (Finset.mul_sum _ _ _).symm
    _ ≤ P.L ^ 2 * (P.Ccol / (kOf n m B : ℝ)) :=
      mul_le_mul_of_nonneg_left (hP.2.2.2.2.2.2.2.2 j) (sq_nonneg _)
    _ = P.L ^ 2 * P.Ccol / (kOf n m B : ℝ) := by ring

private lemma hv_cov_decomposition (P : HaarParams) {n m B : ℕ} (μ : Fin n → ℝ)
    (D : Matrix (Fin n) (Fin m) ℝ) (hP : def_app_sgd_state_law P n m B μ D)
    (j : Fin m) :
    colCov μ D j = (twoR μ D + 2 * colC μ D j) • Matrix.diagonal μ
      + (2 : ℝ) • TD μ D
      + (3 : ℝ) • Matrix.vecMulVec (colMeanVec μ D j) (colMeanVec μ D j) := by
  ext i k
  exact (lem_app_sgd_column_i P μ D hP j).2 i k

private lemma hv_cov_lower (P : HaarParams) {n m B : ℕ} (μ : Fin n → ℝ)
    (D : Matrix (Fin n) (Fin m) ℝ) (hP : def_app_sgd_state_law P n m B μ D)
    (j : Fin m) :
    (colCov μ D j - twoR μ D • Matrix.diagonal μ).PosSemidef := by
  have hdiag : (Matrix.diagonal μ).PosSemidef :=
    Matrix.PosSemidef.diagonal fun i => P.c_pos.le.trans (hP.2.2.2.2.2.1 i).1
  have hmm : (Matrix.vecMulVec (colMeanVec μ D j) (colMeanVec μ D j)).PosSemidef := by
    simpa using Matrix.posSemidef_vecMulVec_self_star (colMeanVec μ D j)
  have heq : colCov μ D j - twoR μ D • Matrix.diagonal μ =
      (2 * colC μ D j) • Matrix.diagonal μ + (2 : ℝ) • TD μ D
        + (3 : ℝ) • Matrix.vecMulVec (colMeanVec μ D j) (colMeanVec μ D j) := by
    rw [hv_cov_decomposition P μ D hP j]
    module
  rw [heq]
  exact ((hdiag.smul (mul_nonneg (by norm_num) (hv_colC_bounds P μ D hP j).1)).add
    ((hv_TD_psd μ D).smul (by norm_num : (0 : ℝ) ≤ 2))).add
      (hmm.smul (by norm_num : (0 : ℝ) ≤ 3))

private lemma hv_op_le_frob {n m : ℕ} (A : Matrix (Fin n) (Fin m) ℝ) :
    Muon.External.matOpNorm A ≤ Real.sqrt (∑ i, ∑ j, A i j ^ 2) := by
  unfold Muon.External.matOpNorm
  refine ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _) fun x => ?_
  have hsq : ‖(LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin A)) x‖ ^ 2
      ≤ (∑ i, ∑ j, A i j ^ 2) * ‖x‖ ^ 2 := by
    simp only [EuclideanSpace.real_norm_sq_eq]
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun i _ => ?_
    change (∑ j, A i j * x j) ^ 2 ≤ _
    exact Finset.sum_mul_sq_le_sq_mul_sq _ _ _
  have hS : 0 ≤ ∑ i, ∑ j, A i j ^ 2 :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
  nlinarith [Real.sq_sqrt hS, norm_nonneg
    ((LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin A)) x), norm_nonneg x,
    mul_nonneg (Real.sqrt_nonneg (∑ i, ∑ j, A i j ^ 2)) (norm_nonneg x)]

open scoped Matrix.Norms.L2Operator in
private lemma hv_gram_op_bound {n m : ℕ} (A : Matrix (Fin n) (Fin m) ℝ) :
    Muon.External.matOpNorm (A * Aᵀ) ≤ ∑ i, ∑ j, A i j ^ 2 := by
  have h := hv_op_le_frob A
  change ‖A‖ ≤ Real.sqrt (∑ i, ∑ j, A i j ^ 2) at h
  change ‖A * Aᵀ‖ ≤ _
  have hnorm : ‖Aᵀ‖ = ‖A‖ := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      Matrix.l2_opNorm_conjTranspose A
  calc
    ‖A * Aᵀ‖ ≤ ‖A‖ * ‖Aᵀ‖ := Matrix.l2_opNorm_mul A Aᵀ
    _ = ‖A‖ ^ 2 := by rw [hnorm, sq]
    _ ≤ Real.sqrt (∑ i, ∑ j, A i j ^ 2) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) h 2
    _ = ∑ i, ∑ j, A i j ^ 2 := Real.sq_sqrt
      (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _)

private lemma hv_TD_op_bound (P : HaarParams) {n m B : ℕ} (μ : Fin n → ℝ)
    (D : Matrix (Fin n) (Fin m) ℝ) (hP : def_app_sgd_state_law P n m B μ D) :
    Muon.External.matOpNorm (TD μ D) ≤ haarH0 P := by
  have heq : TD μ D = (Matrix.diagonal μ * D) * (Matrix.diagonal μ * D)ᵀ := by
    simp [TD, Matrix.transpose_mul, Matrix.mul_assoc]
  have htrace : (TD μ D).trace = ∑ i, ∑ j, (Matrix.diagonal μ * D) i j ^ 2 := by
    rw [heq]
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply, sq]
  calc
    Muon.External.matOpNorm (TD μ D) ≤ (TD μ D).trace := by
      rw [htrace, heq]
      exact hv_gram_op_bound _
    _ ≤ haarH0 P := (haar_bounds P n m B μ D hP).2.2.1

private lemma hv_outer_op_bound {n : ℕ} (a : Fin n → ℝ) :
    Muon.External.matOpNorm (Matrix.vecMulVec a a) ≤ ∑ i, a i ^ 2 := by
  let A : Matrix (Fin n) (Fin 1) ℝ := fun i _ => a i
  have heq : Matrix.vecMulVec a a = A * Aᵀ := by
    ext i k
    change a i * a k = ∑ _l : Fin 1, a i * a k
    simp
  rw [heq]
  simpa [A] using hv_gram_op_bound A

open scoped Matrix.Norms.L2Operator in
private lemma hv_cov_op_bound (P : HaarParams) {n m B : ℕ} (μ : Fin n → ℝ)
    (D : Matrix (Fin n) (Fin m) ℝ) (hP : def_app_sgd_state_law P n m B μ D)
    (j : Fin m) : Muon.External.matOpNorm (colCov μ D j) ≤ colV0 P := by
  have hL : 0 ≤ P.L := P.c_pos.le.trans P.c_le_L
  have hμ := hP.2.2.2.2.2.1
  have hk : (1 : ℝ) ≤ (kOf n m B : ℝ) := by
    have h := hP.2.1
    exact_mod_cast (by omega : 1 ≤ kOf n m B)
  have hC := hv_colC_bounds P μ D hP j
  have hC' : colC μ D j ≤ P.L * P.Ccol := hC.2.trans
    (div_le_self (mul_nonneg hL P.Ccol_pos.le) hk)
  have hm : ∑ i, colMeanVec μ D j i ^ 2 ≤ P.L ^ 2 * P.Ccol :=
    (hv_mean_sq_bound P μ D hP j).trans
      (div_le_self (mul_nonneg (sq_nonneg _) P.Ccol_pos.le) hk)
  have hR := haar_bounds P n m B μ D hP
  have hR0 : 0 ≤ twoR μ D := by
    refine le_trans ?_ hR.1
    exact mul_nonneg P.c_pos.le (sq_nonneg _)
  have hcoef : 0 ≤ twoR μ D + 2 * colC μ D j := by linarith [hC.1]
  have hcoef' : 0 ≤ haarPplus P + 2 * (P.L * P.Ccol) := by
    have : 0 ≤ haarPplus P := hR0.trans hR.2.1
    exact add_nonneg this (mul_nonneg (by norm_num) (mul_nonneg hL P.Ccol_pos.le))
  have hdiag : ‖Matrix.diagonal μ‖ ≤ P.L := by
    rw [Matrix.l2_opNorm_diagonal]
    exact (pi_norm_le_iff_of_nonneg hL).mpr fun i => by
      rw [Real.norm_eq_abs, abs_of_nonneg (P.c_pos.le.trans (hμ i).1)]
      exact (hμ i).2
  have hTD := hv_TD_op_bound P μ D hP
  have houter := (hv_outer_op_bound (colMeanVec μ D j)).trans hm
  change ‖TD μ D‖ ≤ _ at hTD
  change ‖Matrix.vecMulVec (colMeanVec μ D j) (colMeanVec μ D j)‖ ≤ _ at houter
  change ‖colCov μ D j‖ ≤ _
  rw [hv_cov_decomposition P μ D hP j]
  calc
    ‖(twoR μ D + 2 * colC μ D j) • Matrix.diagonal μ + (2 : ℝ) • TD μ D
        + (3 : ℝ) • Matrix.vecMulVec (colMeanVec μ D j) (colMeanVec μ D j)‖
      ≤ ‖(twoR μ D + 2 * colC μ D j) • Matrix.diagonal μ‖
        + ‖(2 : ℝ) • TD μ D‖
        + ‖(3 : ℝ) • Matrix.vecMulVec (colMeanVec μ D j) (colMeanVec μ D j)‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ = (twoR μ D + 2 * colC μ D j) * ‖Matrix.diagonal μ‖
        + 2 * ‖TD μ D‖
        + 3 * ‖Matrix.vecMulVec (colMeanVec μ D j) (colMeanVec μ D j)‖ := by
      simp [norm_smul, Real.norm_eq_abs, abs_of_nonneg hcoef]
    _ ≤ (haarPplus P + 2 * (P.L * P.Ccol)) * P.L + 2 * haarH0 P
        + 3 * (P.L ^ 2 * P.Ccol) := by
      exact add_le_add
        (add_le_add (mul_le_mul (by linarith [hR.2.1]) hdiag (norm_nonneg _) hcoef')
          (mul_le_mul_of_nonneg_left hTD (by norm_num)))
        (mul_le_mul_of_nonneg_left houter (by norm_num))
    _ = colV0 P := by unfold colV0; ring

private lemma hv_moment_coord_int (n : ℕ) (i : Fin n) (k : ℕ) :
    Integrable (fun z : Fin n → ℝ => z i ^ k) (Muon.Foundations.stdGaussianPi n) := by
  have hm : MeasurePreserving (fun z : Fin n → ℝ => z i) (Muon.Foundations.stdGaussianPi n)
      (gaussianReal 0 1) := measurePreserving_eval _ i
  exact (hm.integrable_comp (g := fun x : ℝ => x ^ k) (by fun_prop)).2
    (Muon.Foundations.gaussian_integrable_pow k)


private lemma hv_moment_coord_moment (n : ℕ) (i : Fin n) (p : ℕ) :
    ∫ z, z i ^ (2 * p) ∂(Muon.Foundations.stdGaussianPi n)
      = (((2 * p - 1).doubleFactorial : ℕ) : ℝ) := by
  have hm : Measurable (fun z : Fin n → ℝ => z i) := by fun_prop
  have e := integral_map (μ := Muon.Foundations.stdGaussianPi n) (φ := fun z : Fin n → ℝ => z i)
    hm.aemeasurable (f := fun x : ℝ => x ^ (2 * p))
    (by fun_prop : Measurable fun x : ℝ => x ^ (2 * p)).aestronglyMeasurable
  rw [Muon.Foundations.stdGaussianPi_map_coord, Muon.Foundations.gaussian_moment_even] at e
  exact e.symm


private lemma hv_moment_lin_int {n : ℕ} (p : ℕ) (hp : 1 ≤ p) (u : Fin n → ℝ) :
    Integrable (fun z : Fin n → ℝ => dotProduct z u ^ (2 * p))
      (Muon.Foundations.stdGaussianPi n) := by
  by_contra h
  have h0 : ∫ z, dotProduct z u ^ (2 * p) ∂(Muon.Foundations.stdGaussianPi n)
      = (((2 * p - 1).doubleFactorial : ℕ) : ℝ) * (∑ k, u k ^ 2) ^ p :=
    sgd_gauss_linear_even_moment p u
  rw [integral_undef h] at h0
  have hd : (((2 * p - 1).doubleFactorial : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.doubleFactorial_pos _).ne'
  have hS : ∑ k, u k ^ 2 = 0 := by
    rcases mul_eq_zero.1 h0.symm with h1 | h1
    · exact absurd h1 hd
    · exact (pow_eq_zero_iff (by omega : p ≠ 0)).1 h1
  have hu : ∀ k, u k = 0 := by
    intro k
    have h2 : u k ^ 2 ≤ ∑ k, u k ^ 2 :=
      Finset.single_le_sum (f := fun k => u k ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ k)
    have h3 : u k ^ 2 = 0 := by linarith [sq_nonneg (u k)]
    exact (pow_eq_zero_iff two_ne_zero).1 h3
  apply h
  have e : (fun z : Fin n → ℝ => dotProduct z u ^ (2 * p)) = fun _ => 0 := by
    funext z
    simp [dotProduct, hu, zero_pow (by omega : 2 * p ≠ 0)]
  rw [e]
  exact integrable_zero _ _ _


private lemma hv_moment_inner (n m : ℕ) (p : ℕ) (Δ : Matrix (Fin n) (Fin m) ℝ) (w : Fin m → ℝ) :
    ∫ z, dotProduct z (Matrix.mulVec Δ w) ^ (2 * p) ∂(Muon.Foundations.stdGaussianPi n)
      = (((2 * p - 1).doubleFactorial : ℕ) : ℝ) * (∑ k, Matrix.mulVec Δ w k ^ 2) ^ p :=
  sgd_gauss_linear_even_moment p (Matrix.mulVec Δ w)


private lemma hv_moment_sq_pow_int (m p : ℕ) (hp : 1 ≤ p) :
    Integrable (fun w : Fin m → ℝ => (∑ k, w k ^ 2) ^ p) (Muon.Foundations.stdGaussianPi m) := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp [zero_pow (by omega : p ≠ 0)]
  · by_contra h
    have h0 := Muon.Foundations.stdGaussianPi_sq_norm_moment m p hp
    rw [integral_undef h] at h0
    have hpos : ∏ j ∈ Finset.range p, ((m : ℝ) + 2 * (j : ℝ)) ≠ 0 := by
      rw [Finset.prod_ne_zero_iff]
      intro j _
      have h1 : (0 : ℝ) < m := by exact_mod_cast hm
      have h2 : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
      have h3 : (0 : ℝ) < (m : ℝ) + 2 * (j : ℝ) := by linarith
      exact h3.ne'
    exact hpos h0.symm


private lemma hv_moment_quad_int {n m : ℕ} (p : ℕ) (hp : 1 ≤ p) (Δ : Matrix (Fin n) (Fin m) ℝ) :
    Integrable (fun w : Fin m → ℝ => (∑ k, Matrix.mulVec Δ w k ^ 2) ^ p)
      (Muon.Foundations.stdGaussianPi m) := by
  have hS := (hv_moment_sq_pow_int m p hp).const_mul ((frobNorm Δ ^ 2) ^ p)
  have hcont : Continuous fun w : Fin m → ℝ => (∑ k, Matrix.mulVec Δ w k ^ 2) ^ p := by
    simp only [Matrix.mulVec, dotProduct]
    fun_prop
  refine Integrable.mono' hS hcont.aestronglyMeasurable (Filter.Eventually.of_forall fun w => ?_)
  have hnn : 0 ≤ ∑ k, Matrix.mulVec Δ w k ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  rw [Real.norm_of_nonneg (pow_nonneg hnn p)]
  have hCS : ∑ k, Matrix.mulVec Δ w k ^ 2 ≤ frobNorm Δ ^ 2 * ∑ l, w l ^ 2 := by
    rw [show frobNorm Δ ^ 2 = ∑ i, ∑ j, Δ i j ^ 2 from Real.sq_sqrt (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _), Finset.sum_mul]
    refine Finset.sum_le_sum fun k _ => ?_
    have e : Matrix.mulVec Δ w k = ∑ b, Δ k b * w b := rfl
    rw [e]
    exact Finset.sum_mul_sq_le_sq_mul_sq _ _ _
  calc (∑ k, Matrix.mulVec Δ w k ^ 2) ^ p ≤ (frobNorm Δ ^ 2 * ∑ l, w l ^ 2) ^ p :=
        pow_le_pow_left₀ hnn hCS p
    _ = (frobNorm Δ ^ 2) ^ p * (∑ l, w l ^ 2) ^ p := mul_pow _ _ _


private lemma hv_moment_hf_int {Nout Nin : ℕ} (Δ : Matrix (Fin Nout) (Fin Nin) ℝ) (p : ℕ)
    (hp : 1 ≤ p) :
    Integrable (fun q : (Fin Nout → ℝ) × (Fin Nin → ℝ) =>
      dotProduct q.1 (Matrix.mulVec Δ q.2) ^ (2 * p))
      ((Muon.Foundations.stdGaussianPi Nout).prod (Muon.Foundations.stdGaussianPi Nin)) := by
  have hcont : Continuous fun q : (Fin Nout → ℝ) × (Fin Nin → ℝ) =>
      dotProduct q.1 (Matrix.mulVec Δ q.2) ^ (2 * p) := by
    simp only [Matrix.mulVec, dotProduct]
    fun_prop
  rw [integrable_prod_iff' hcont.aestronglyMeasurable]
  refine ⟨Filter.Eventually.of_forall fun w => hv_moment_lin_int p hp (Matrix.mulVec Δ w), ?_⟩
  have hn : ∀ x : ℝ, ‖x ^ (2 * p)‖ = x ^ (2 * p) := fun x => by
    rw [pow_mul]
    exact Real.norm_of_nonneg (by positivity)
  have e : (fun w : Fin Nin → ℝ => ∫ z, ‖dotProduct z (Matrix.mulVec Δ w) ^ (2 * p)‖
      ∂(Muon.Foundations.stdGaussianPi Nout))
      = fun w => (((2 * p - 1).doubleFactorial : ℕ) : ℝ) *
          (∑ k, Matrix.mulVec Δ w k ^ 2) ^ p := by
    funext w
    simp only [hn]
    exact hv_moment_inner _ _ p Δ w
  rw [e]
  exact (hv_moment_quad_int p hp Δ).const_mul _


private lemma hv_moment_hd_val {Nout Nin : ℕ} (Δ : Matrix (Fin Nout) (Fin Nin) ℝ) (p : ℕ)
    (hp : 1 ≤ p) :
    ∫ q : (Fin Nout → ℝ) × (Fin Nin → ℝ), dotProduct q.1 (Matrix.mulVec Δ q.2) ^ (2 * p)
      ∂((Muon.Foundations.stdGaussianPi Nout).prod (Muon.Foundations.stdGaussianPi Nin))
      ≤ (((2 * p - 1).doubleFactorial : ℕ) : ℝ) *
          ((((2 * p - 1).doubleFactorial : ℕ) : ℝ) * frobNorm Δ ^ (2 * p)) := by
  rw [integral_prod_symm _ (hv_moment_hf_int Δ p hp)]
  simp only [hv_moment_inner]
  rw [integral_const_mul]
  have hq := sgd_quadform_moment_le p hp Δ
  exact mul_le_mul_of_nonneg_left hq (Nat.cast_nonneg _)


private lemma hv_weighted_product {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) (f g : Ω → ℝ) (hf : AEStronglyMeasurable f ν)
    (hg : AEStronglyMeasurable g ν) (hf2 : Integrable (fun x => f x ^ 2) ν)
    (hg2 : Integrable (fun x => g x ^ 2) ν) (C A B : ℝ)
    (hA : 0 < A) (hB : 0 < B)
    (hfa : ∫ x, f x ^ 2 ∂ν ≤ C * A ^ 2)
    (hgb : ∫ x, g x ^ 2 ∂ν ≤ C * B ^ 2) :
    Integrable (fun x => f x * g x) ν ∧
      (∫ x, f x * g x ∂ν) ≤ C * A * B := by
  have hint : Integrable (fun x => f x * g x) ν := by
    refine ((hf2.add hg2).div_const 2).mono' (hf.mul hg) ?_
    filter_upwards [] with x
    rw [Real.norm_eq_abs, abs_mul]
    dsimp
    nlinarith [sq_nonneg (|f x| - |g x|), sq_abs (f x), sq_abs (g x)]
  refine ⟨hint, ?_⟩
  have hpt : ∀ x, f x * g x ≤ ((B / A) * f x ^ 2 + (A / B) * g x ^ 2) / 2 := by
    intro x
    have h := sq_nonneg (B * f x - A * g x)
    apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 2)).2
    apply (mul_le_mul_iff_left₀ (mul_pos hA hB)).mp
    field_simp
    nlinarith
  have hbound := integral_mono hint
    (((hf2.const_mul (B / A)).add (hg2.const_mul (A / B))).div_const 2)
    hpt
  simp only [Pi.add_apply] at hbound
  rw [integral_div] at hbound
  rw [integral_add (hf2.const_mul _) (hg2.const_mul _),
    integral_const_mul, integral_const_mul] at hbound
  have h1 := mul_le_mul_of_nonneg_left hfa (div_nonneg hB.le hA.le)
  have h2 := mul_le_mul_of_nonneg_left hgb (div_nonneg hA.le hB.le)
  have heq : ((B / A) * (C * A ^ 2) + (A / B) * (C * B ^ 2)) / 2 = C * A * B := by
    field_simp
    <;> ring
  linarith

private lemma hv_directional_raw {n m : ℕ} (M : Matrix (Fin n) (Fin m) ℝ)
    (u : Fin n → ℝ) (j : Fin m) (q : ℕ) (hq : 1 ≤ q)
    (hF : 0 < frobNorm M) (hu : 0 < ∑ i, u i ^ 2) :
    Integrable (fun p => (p.1 ⬝ᵥ (M *ᵥ p.2) * (p.1 ⬝ᵥ u * p.2 j)) ^ (2 * q))
      (gaussBatch n m) ∧
    (∫ p, (p.1 ⬝ᵥ (M *ᵥ p.2) * (p.1 ⬝ᵥ u * p.2 j)) ^ (2 * q)
      ∂(gaussBatch n m)) ≤
      (((4 * q - 1).doubleFactorial : ℕ) : ℝ) ^ 2 * frobNorm M ^ (2 * q) *
        (∑ i, u i ^ 2) ^ q := by
  let f : ((Fin n → ℝ) × (Fin m → ℝ)) → ℝ :=
    fun p => (p.1 ⬝ᵥ (M *ᵥ p.2)) ^ (2 * q)
  let g : ((Fin n → ℝ) × (Fin m → ℝ)) → ℝ :=
    fun p => (p.1 ⬝ᵥ u * p.2 j) ^ (2 * q)
  have he : 2 * (2 * q) = 4 * q := by omega
  have hf2 : Integrable (fun p => f p ^ 2) (gaussBatch n m) := by
    simpa only [gaussBatch, f, ← pow_mul, he, show 2 * q * 2 = 4 * q by omega]
      using hv_moment_hf_int M (2 * q) (by omega)
  have hg2 : Integrable (fun p => g p ^ 2) (gaussBatch n m) := by
    have h := (hv_moment_lin_int (2 * q) (by omega) u).mul_prod
      (hv_moment_coord_int m j (2 * (2 * q)))
    simpa only [gaussBatch, g, ← pow_mul, mul_pow, he, show 2 * q * 2 = 4 * q by omega] using h
  have hfa : ∫ p, f p ^ 2 ∂(gaussBatch n m) ≤
      (((4 * q - 1).doubleFactorial : ℕ) : ℝ) ^ 2 * (frobNorm M ^ (2 * q)) ^ 2 := by
    have h := hv_moment_hd_val M (2 * q) (by omega)
    simp only [f, ← pow_mul, he, show 2 * q * 2 = 4 * q by omega, gaussBatch]
    convert h using 1 <;> ring
  have hgb : ∫ p, g p ^ 2 ∂(gaussBatch n m) =
      (((4 * q - 1).doubleFactorial : ℕ) : ℝ) ^ 2 * ((∑ i, u i ^ 2) ^ q) ^ 2 := by
    simp only [gaussBatch, g, ← pow_mul, show 2 * q * 2 = 4 * q by omega, mul_pow]
    rw [show 4 * q = 2 * (2 * q) by omega]
    rw [integral_prod_mul (μ := Muon.Foundations.stdGaussianPi n)
      (ν := Muon.Foundations.stdGaussianPi m)
      (fun z => (z ⬝ᵥ u) ^ (2 * (2 * q))) (fun w => w j ^ (2 * (2 * q)))]
    change (∫ z, (∑ i, z i * u i) ^ (2 * (2 * q)) ∂(Muon.Foundations.stdGaussianPi n)) * _ = _
    rw [sgd_gauss_linear_even_moment, hv_moment_coord_moment]
    rw [he]
    ring
  have h := hv_weighted_product (gaussBatch n m) f g
    (by dsimp [f]; simp only [dotProduct, Matrix.mulVec]; fun_prop)
    (by dsimp [g]; simp only [dotProduct]; fun_prop) hf2 hg2
    ((((4 * q - 1).doubleFactorial : ℕ) : ℝ) ^ 2)
    (frobNorm M ^ (2 * q)) ((∑ i, u i ^ 2) ^ q)
    (pow_pos hF _) (pow_pos hu _) hfa hgb.le
  simpa only [f, g, mul_pow] using h

private lemma hv_centered_even {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) [IsProbabilityMeasure ν] (f : Ω → ℝ) (m C R : ℝ)
    (q : ℕ) (hf : AEStronglyMeasurable f ν)
    (hi : Integrable (fun x => f x ^ (2 * q)) ν)
    (hr : (∫ x, f x ^ (2 * q) ∂ν) ≤ C * R) (hm : m ^ (2 * q) ≤ R) :
    Integrable (fun x => (f x - m) ^ (2 * q)) ν ∧
      (∫ x, (f x - m) ^ (2 * q) ∂ν) ≤ 2 ^ (2 * q - 1) * (C + 1) * R := by
  have hpt : ∀ x, (f x - m) ^ (2 * q) ≤
      2 ^ (2 * q - 1) * (f x ^ (2 * q) + m ^ (2 * q)) := by
    intro x
    have h := (even_two_mul q).add_pow_le (a := f x) (b := -m)
    simpa only [← sub_eq_add_neg, pow_mul, neg_sq] using h
  have hib : Integrable (fun x => 2 ^ (2 * q - 1) * (f x ^ (2 * q) + m ^ (2 * q))) ν :=
    (hi.add (integrable_const _)).const_mul _
  have hic : Integrable (fun x => (f x - m) ^ (2 * q)) ν := by
    refine hib.mono' ((hf.sub aestronglyMeasurable_const).pow _) ?_
    filter_upwards [] with x
    rw [Real.norm_of_nonneg (by rw [pow_mul]; positivity)]
    exact hpt x
  refine ⟨hic, ?_⟩
  have hb := integral_mono hic hib hpt
  rw [integral_const_mul, integral_add hi (integrable_const _), integral_const] at hb
  simp only [probReal_univ, smul_eq_mul, one_mul] at hb
  have hm' := add_le_add hr hm
  have h := mul_le_mul_of_nonneg_left hm' (by positivity : (0 : ℝ) ≤ 2 ^ (2 * q - 1))
  nlinarith

private lemma hv_lam_frob_sq {n m : ℕ} (μ : Fin n → ℝ)
    (D : Matrix (Fin n) (Fin m) ℝ) (hμ : ∀ i, 0 ≤ μ i) :
    frobNorm (lamHalf μ * D) ^ 2 = twoR μ D := by
  have hs : 0 ≤ ∑ i, ∑ k, (lamHalf μ * D) i k ^ 2 := by positivity
  unfold frobNorm
  rw [Real.sq_sqrt hs]
  simp only [lamHalf, Matrix.diagonal_mul, mul_pow, Real.sq_sqrt (hμ _)]
  simp only [twoR, Matrix.trace, Matrix.diag, Matrix.diagonal_mul]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Finset.mul_sum, sq]

private lemma hv_directional_id {n m : ℕ} (μ : Fin n → ℝ)
    (D : Matrix (Fin n) (Fin m) ℝ) (a : Fin n → ℝ) (j : Fin m)
    (p : (Fin n → ℝ) × (Fin m → ℝ)) :
    a ⬝ᵥ colSample μ D j p = resA μ D p *
      (p.1 ⬝ᵥ (fun i => a i * Real.sqrt (μ i)) * p.2 j) := by
  simp only [dotProduct, colSample, lamHalf, Matrix.mulVec_diagonal,
    Finset.mul_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl fun i _ => by ring

private lemma hv_directional_mean_sq {n m : ℕ} (μ : Fin n → ℝ)
    (D : Matrix (Fin n) (Fin m) ℝ) (a : Fin n → ℝ) (j : Fin m)
    (hμ : ∀ i, 0 ≤ μ i) :
    (a ⬝ᵥ colMeanVec μ D j) ^ 2 ≤
      frobNorm (lamHalf μ * D) ^ 2 * ∑ i, (a i * Real.sqrt (μ i)) ^ 2 := by
  have heq : a ⬝ᵥ colMeanVec μ D j =
      ∑ i, (a i * Real.sqrt (μ i)) * (lamHalf μ * D) i j := by
    simp only [dotProduct, colMeanVec, lamHalf, Matrix.diagonal_mul]
    exact Finset.sum_congr rfl fun i _ => by
      rw [show (a i * Real.sqrt (μ i)) * (Real.sqrt (μ i) * D i j) =
        a i * (Real.sqrt (μ i) ^ 2 * D i j) by ring, Real.sq_sqrt (hμ i)]
  rw [heq]
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun i => a i * Real.sqrt (μ i)) (fun i => (lamHalf μ * D) i j)
  have hcol : ∑ i, (lamHalf μ * D) i j ^ 2 ≤ frobNorm (lamHalf μ * D) ^ 2 := by
    have hs : 0 ≤ ∑ i, ∑ k, (lamHalf μ * D) i k ^ 2 := by positivity
    unfold frobNorm
    rw [Real.sq_sqrt hs]
    exact Finset.sum_le_sum fun i _ =>
      Finset.single_le_sum (fun k _ => sq_nonneg _) (Finset.mem_univ j)
  refine hcs.trans ?_
  rw [mul_comm (frobNorm (lamHalf μ * D) ^ 2)]
  exact mul_le_mul_of_nonneg_left hcol (Finset.sum_nonneg fun i _ => sq_nonneg _)

private lemma hv_directional_even_bound (P : HaarParams) {n m B : ℕ}
    (μ : Fin n → ℝ) (D : Matrix (Fin n) (Fin m) ℝ)
    (hP : def_app_sgd_state_law P n m B μ D) (j : Fin m) (a : Fin n → ℝ)
    (q : ℕ) (hq : 1 ≤ q) :
    (∫⁻ p, ENNReal.ofReal ((a ⬝ᵥ colZ μ D j p) ^ (2 * q)) ∂(gaussBatch n m)) ≤
      ENNReal.ofReal (2 ^ (2 * q - 1) *
        ((((4 * q - 1).doubleFactorial : ℕ) : ℝ) ^ 2 + 1) *
          haarPplus P ^ q * P.L ^ q * (∑ i, a i ^ 2) ^ q) := by
  have hL : 0 ≤ P.L := P.c_pos.le.trans P.c_le_L
  have hμ : ∀ i, 0 ≤ μ i := fun i => P.c_pos.le.trans (hP.2.2.2.2.2.1 i).1
  let u : Fin n → ℝ := fun i => a i * Real.sqrt (μ i)
  have hu2 : ∑ i, u i ^ 2 = ∑ i, a i ^ 2 * μ i := by
    simp only [u, mul_pow, Real.sq_sqrt (hμ _)]
  have hsum0 : 0 ≤ ∑ i, a i ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  by_cases ha : ∑ i, a i ^ 2 = 0
  · have ha0 : a = 0 := by
      funext i
      have hi := Finset.single_le_sum (f := fun i => a i ^ 2)
        (fun _ _ => sq_nonneg _) (Finset.mem_univ i)
      simp only [ha] at hi
      have : a i ^ 2 = 0 := le_antisymm hi (sq_nonneg _)
      simpa using (sq_eq_zero_iff.mp this)
    simp [ha0, zero_pow (by omega : 2 * q ≠ 0), zero_pow (by omega : q ≠ 0)]
  have hu : 0 < ∑ i, u i ^ 2 := by
    rw [hu2]
    have hh : P.c * ∑ i, a i ^ 2 ≤ ∑ i, a i ^ 2 * μ i := by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum fun i _ => by
        nlinarith [mul_le_mul_of_nonneg_left (hP.2.2.2.2.2.1 i).1 (sq_nonneg (a i))]
    exact lt_of_lt_of_le (mul_pos P.c_pos (lt_of_le_of_ne hsum0 (Ne.symm ha))) hh
  have huL : ∑ i, u i ^ 2 ≤ P.L * ∑ i, a i ^ 2 := by
    rw [hu2, Finset.mul_sum]
    exact Finset.sum_le_sum fun i _ => by
      nlinarith [mul_le_mul_of_nonneg_left (hP.2.2.2.2.2.1 i).2 (sq_nonneg (a i))]
  have hF2 := hv_lam_frob_sq μ D hμ
  have hR := haar_bounds P n m B μ D hP
  have hF : 0 < frobNorm (lamHalf μ * D) := by
    have hp : 0 < twoR μ D :=
      lt_of_lt_of_le (mul_pos P.c_pos (pow_pos P.fMin_pos 2)) hR.1
    have hn : 0 ≤ frobNorm (lamHalf μ * D) := Real.sqrt_nonneg _
    nlinarith
  have hraw := hv_directional_raw (lamHalf μ * D) u j q hq hF hu
  have hrawEq : (fun p => (p.1 ⬝ᵥ ((lamHalf μ * D) *ᵥ p.2) *
      (p.1 ⬝ᵥ u * p.2 j)) ^ (2 * q)) =
      (fun p => (a ⬝ᵥ colSample μ D j p) ^ (2 * q)) := by
    funext p
    rw [hv_directional_id]
    rfl
  rw [hrawEq] at hraw
  have hm : (a ⬝ᵥ colMeanVec μ D j) ^ (2 * q) ≤
      frobNorm (lamHalf μ * D) ^ (2 * q) * (∑ i, u i ^ 2) ^ q := by
    rw [pow_mul, pow_mul]
    simpa only [u, mul_pow] using pow_le_pow_left₀ (sq_nonneg _)
      (hv_directional_mean_sq μ D a j hμ) q
  letI : IsProbabilityMeasure (gaussBatch n m) := by unfold gaussBatch; infer_instance
  have hc := hv_centered_even (gaussBatch n m) (fun p => a ⬝ᵥ colSample μ D j p)
    (a ⬝ᵥ colMeanVec μ D j) ((((4 * q - 1).doubleFactorial : ℕ) : ℝ) ^ 2)
    (frobNorm (lamHalf μ * D) ^ (2 * q) * (∑ i, u i ^ 2) ^ q) q
    (by simp only [dotProduct, colSample, resA, lamHalf, Matrix.mulVec_diagonal,
        Matrix.mulVec, Matrix.mul_apply]; fun_prop)
    hraw.1 (by simpa only [mul_assoc] using hraw.2) hm
  have hzeq : (fun p => (a ⬝ᵥ colSample μ D j p - a ⬝ᵥ colMeanVec μ D j) ^ (2 * q)) =
      (fun p => (a ⬝ᵥ colZ μ D j p) ^ (2 * q)) := by
    funext p
    simp only [colZ, dotProduct_sub]
  rw [hzeq] at hc
  rw [← ofReal_integral_eq_lintegral_ofReal hc.1
    (Filter.Eventually.of_forall fun p => by dsimp; rw [pow_mul]; positivity)]
  apply ENNReal.ofReal_le_ofReal
  refine hc.2.trans ?_
  have hb : frobNorm (lamHalf μ * D) ^ (2 * q) * (∑ i, u i ^ 2) ^ q ≤
      haarPplus P ^ q * P.L ^ q * (∑ i, a i ^ 2) ^ q := by
    rw [pow_mul, hF2]
    calc
      _ ≤ haarPplus P ^ q * (P.L * ∑ i, a i ^ 2) ^ q := by
        have hr0 : 0 ≤ twoR μ D := by rw [← hF2]; positivity
        exact mul_le_mul (pow_le_pow_left₀ hr0 hR.2.1 q)
          (pow_le_pow_left₀ hu.le huL q) (pow_nonneg hu.le q)
          (pow_nonneg (hr0.trans hR.2.1) q)
      _ = _ := by rw [mul_pow]; ring
  have hh := mul_le_mul_of_nonneg_left hb
    (by positivity : (0 : ℝ) ≤ 2 ^ (2 * q - 1) *
      ((((4 * q - 1).doubleFactorial : ℕ) : ℝ) ^ 2 + 1))
  simpa only [mul_assoc] using hh

private lemma hv_vector_from_directional {n m : ℕ} (μ : Fin n → ℝ)
    (D : Matrix (Fin n) (Fin m) ℝ) (j : Fin m) (A : ℝ) (r : ℕ)
    (hdir : ∀ a : Fin n → ℝ,
      (∫⁻ p, ENNReal.ofReal ((a ⬝ᵥ colZ μ D j p) ^ (2 * (r + 1))) ∂(gaussBatch n m)) ≤
        ENNReal.ofReal (A * (∑ i, a i ^ 2) ^ (r + 1))) :
    (∫⁻ p, ENNReal.ofReal ((∑ i, colZ μ D j p i ^ 2) ^ (r + 1)) ∂(gaussBatch n m)) ≤
      ENNReal.ofReal (A * (n : ℝ) ^ (r + 1)) := by
  have hcoord (i : Fin n) :
      (∫⁻ p, ENNReal.ofReal (colZ μ D j p i ^ (2 * (r + 1))) ∂(gaussBatch n m)) ≤
        ENNReal.ofReal A := by
    have h := hdir (Pi.single i 1)
    simpa [single_dotProduct, Pi.single_apply, ite_pow] using h
  have hmeas (i : Fin n) : Measurable fun p =>
      ENNReal.ofReal (colZ μ D j p i ^ (2 * (r + 1))) := by
    simp only [colZ, Pi.sub_apply, colSample, resA, lamHalf, Matrix.mulVec_diagonal,
      Matrix.mulVec, dotProduct, Matrix.mul_apply]
    fun_prop
  calc
    _ ≤ ∫⁻ p, ENNReal.ofReal ((n : ℝ) ^ r) *
        ∑ i, ENNReal.ofReal (colZ μ D j p i ^ (2 * (r + 1))) ∂(gaussBatch n m) := by
      apply lintegral_mono
      intro p
      dsimp only
      rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => by rw [pow_mul]; positivity),
        ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ (n : ℝ) ^ r)]
      apply ENNReal.ofReal_le_ofReal
      have h := pow_sum_le_card_mul_sum_pow (s := Finset.univ)
        (f := fun i : Fin n => colZ μ D j p i ^ 2) (fun i _ => sq_nonneg _) r
      simpa only [Finset.card_univ, Fintype.card_fin, ← pow_mul] using h
    _ = ENNReal.ofReal ((n : ℝ) ^ r) *
        ∑ i, ∫⁻ p, ENNReal.ofReal (colZ μ D j p i ^ (2 * (r + 1))) ∂(gaussBatch n m) := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
        lintegral_finsetSum _ (fun i _ => hmeas i)]
    _ ≤ ENNReal.ofReal ((n : ℝ) ^ r) * ∑ _i : Fin n, ENNReal.ofReal A := by
      gcongr with i
      exact hcoord i
    _ = ENNReal.ofReal (A * (n : ℝ) ^ (r + 1)) := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      rw [← ENNReal.ofReal_natCast n, ← ENNReal.ofReal_mul (Nat.cast_nonneg n),
        ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ (n : ℝ) ^ r)]
      congr 1
      ring

/-- **lem:app-sgd-column**, part (v): the admissible constants `V₀, A₄, A₈` and the bounds
`V_j ⪰ 2ℛ Λ`, `‖V_j‖ ≤ V₀`, `‖m_j‖² ≤ L² C_col / k`, the directional moments
`E|aᵀZ|⁴ ≤ A₄‖a‖⁴`, `E|aᵀZ|⁸ ≤ A₈‖a‖⁸` and the vector moments `E‖Z‖⁴ ≤ A₄ N_out²`,
`E‖Z‖⁸ ≤ A₈ N_out⁴`. The constants depend on `P` only.

cr-2026-10-23. LaTeX statement (verbatim):
\begin{lemma}[Column moments]
There are admissible constants $V_0$, $A_4$, $A_8$ such that, for every column $j$,
\begin{align}
\EE X&=m_j,\qquad V_j\defeq\EE[Z\tensor Z]=(2\cR+2C_j)\Lambda+2T_D+3\,m_j\tensor m_j,\\
\EE[h_j\tensor h_j]&=\frac{2\cR+2C_j}B\,\Lambda+\frac2B\,T_D+\Big(1+\frac3B\Big)m_j\tensor m_j,\\
\EE[HH^\T]&=\frac{2\cR\,(\Nin+2)}B\,\Lambda+\Big(1+\frac{2\Nin+3}B\Big)T_D,
\end{align}
with $C_j=D_{\cdot j}^\T\Lambda D_{\cdot j}$, and
\begin{gather}
V_j\succeq2\cR\,\Lambda,\qquad \norm{V_j}\le V_0,\qquad \norm{m_j}^2\le\frac{L^2C_{\rm col}}k,\\
\EE\abs{a^\T Z}^4\le A_4\norm a^4,\quad \EE\abs{a^\T Z}^8\le A_8\norm a^8\quad(a\in\R^{\Nout}),\\
\EE\norm Z^4\le A_4\Nout^2,\quad \EE\norm Z^8\le A_8\Nout^4 .
\end{gather}
Every column $h_j$ is nonzero almost surely.
\end{lemma}
-/
theorem lem_app_sgd_column_v (P : HaarParams) :
    ∃ V0 A4 A8 : ℝ, 0 ≤ V0 ∧ 0 ≤ A4 ∧ 0 ≤ A8 ∧
      ∀ (n m B : ℕ) (μ : Fin n → ℝ) (D : Matrix (Fin n) (Fin m) ℝ),
        def_app_sgd_state_law P n m B μ D → ∀ j : Fin m,
          (colCov μ D j - twoR μ D • Matrix.diagonal μ).PosSemidef ∧
          Muon.External.matOpNorm (colCov μ D j) ≤ V0 ∧
          ∑ i, colMeanVec μ D j i ^ 2 ≤ P.L ^ 2 * P.Ccol / (kOf n m B : ℝ) ∧
          (∀ a : Fin n → ℝ,
            ∫⁻ p, ENNReal.ofReal ((a ⬝ᵥ colZ μ D j p) ^ 4) ∂(gaussBatch n m)
              ≤ ENNReal.ofReal (A4 * (∑ i, a i ^ 2) ^ 2) ∧
            ∫⁻ p, ENNReal.ofReal ((a ⬝ᵥ colZ μ D j p) ^ 8) ∂(gaussBatch n m)
              ≤ ENNReal.ofReal (A8 * (∑ i, a i ^ 2) ^ 4)) ∧
          ∫⁻ p, ENNReal.ofReal ((∑ i, colZ μ D j p i ^ 2) ^ 2) ∂(gaussBatch n m)
            ≤ ENNReal.ofReal (A4 * (n : ℝ) ^ 2) ∧
          ∫⁻ p, ENNReal.ofReal ((∑ i, colZ μ D j p i ^ 2) ^ 4) ∂(gaussBatch n m)
            ≤ ENNReal.ofReal (A8 * (n : ℝ) ^ 4) := by
  have hL : 0 ≤ P.L := P.c_pos.le.trans P.c_le_L
  have hK : 0 ≤ P.K := (by norm_num : (0 : ℝ) ≤ 1).trans P.one_le_K
  have hC : 0 ≤ P.Ccol := P.Ccol_pos.le
  refine ⟨colV0 P, colA4 P, colA8 P, ?_, ?_, ?_, ?_⟩
  · unfold colV0 haarPplus haarH0
    positivity
  · unfold colA4 haarPplus
    positivity
  · unfold colA8 haarPplus
    positivity
  · intro n m B μ D hP j
    have hcov := hv_cov_lower P μ D hP j
    have hop := hv_cov_op_bound P μ D hP j
    have hmean := hv_mean_sq_bound P μ D hP j
    have h4 : ∀ a : Fin n → ℝ,
        (∫⁻ p, ENNReal.ofReal ((a ⬝ᵥ colZ μ D j p) ^ 4) ∂(gaussBatch n m)) ≤
          ENNReal.ofReal (colA4 P * (∑ i, a i ^ 2) ^ 2) := by
      intro a
      refine (hv_directional_even_bound P μ D hP j a 2 (by norm_num)).trans ?_
      apply ENNReal.ofReal_le_ofReal
      unfold colA4
      norm_num [Nat.doubleFactorial]
      gcongr <;> norm_num
    have h8 : ∀ a : Fin n → ℝ,
        (∫⁻ p, ENNReal.ofReal ((a ⬝ᵥ colZ μ D j p) ^ 8) ∂(gaussBatch n m)) ≤
          ENNReal.ofReal (colA8 P * (∑ i, a i ^ 2) ^ 4) := by
      intro a
      refine (hv_directional_even_bound P μ D hP j a 4 (by norm_num)).trans ?_
      apply ENNReal.ofReal_le_ofReal
      unfold colA8
      norm_num [Nat.doubleFactorial]
      gcongr <;> norm_num
    exact ⟨hcov, hop, hmean, fun a => ⟨h4 a, h8 a⟩,
      hv_vector_from_directional μ D j (colA4 P) 1 h4,
      hv_vector_from_directional μ D j (colA8 P) 3 h8⟩

/-! ## Quadratic forms of a column (`prop:app-sgd-quadratic`) -/

private lemma hv_quadratic_trace {n : ℕ} (Pm : Matrix (Fin n) (Fin n) ℝ)
    (x : Fin n → ℝ) :
    x ⬝ᵥ (Pm *ᵥ x) = (Pm * Matrix.vecMulVec x x).trace := by
  simp only [dotProduct, Matrix.mulVec, Matrix.trace, Matrix.diag,
    Matrix.mul_apply, Matrix.vecMulVec_apply, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => by ring

private lemma hv_hcol_quadratic_integrable {n m B : ℕ} (μ : Fin n → ℝ)
    (D : Matrix (Fin n) (Fin m) ℝ) (j : Fin m) (Pm : Matrix (Fin n) (Fin n) ℝ) :
    Integrable (fun β => hCol μ D β j ⬝ᵥ (Pm *ᵥ hCol μ D β j))
      (batchLaw n m B) := by
  simp only [hv_quadratic_trace, Matrix.trace, Matrix.diag, Matrix.mul_apply,
    Matrix.vecMulVec_apply]
  exact integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun k _ =>
    (hv_hcol_pair_int μ D j k i).const_mul (Pm i k)

private lemma hv_hcol_quadratic_mean (P : HaarParams) {n m B : ℕ} (μ : Fin n → ℝ)
    (D : Matrix (Fin n) (Fin m) ℝ) (hP : def_app_sgd_state_law P n m B μ D)
    (j : Fin m) (Pm : Matrix (Fin n) (Fin n) ℝ) :
    ∫ β, hCol μ D β j ⬝ᵥ (Pm *ᵥ hCol μ D β j) ∂(batchLaw n m B) =
      (twoR μ D + 2 * colC μ D j) / (B : ℝ) * (Pm * Matrix.diagonal μ).trace
        + 2 / (B : ℝ) * (Pm * TD μ D).trace
        + (1 + 3 / (B : ℝ)) *
          (colMeanVec μ D j ⬝ᵥ (Pm *ᵥ colMeanVec μ D j)) := by
  let M : Matrix (Fin n) (Fin n) ℝ :=
    ((twoR μ D + 2 * colC μ D j) / (B : ℝ)) • Matrix.diagonal μ
      + (2 / (B : ℝ)) • TD μ D
      + (1 + 3 / (B : ℝ)) • Matrix.vecMulVec (colMeanVec μ D j) (colMeanVec μ D j)
  have hM : ∀ i k, ∫ β, hCol μ D β j i * hCol μ D β j k ∂(batchLaw n m B)
      = M i k := lem_app_sgd_column_ii P μ D hP j
  have heq : (∫ β, hCol μ D β j ⬝ᵥ (Pm *ᵥ hCol μ D β j) ∂(batchLaw n m B))
      = (Pm * M).trace := by
    simp only [hv_quadratic_trace, Matrix.trace, Matrix.diag, Matrix.mul_apply,
      Matrix.vecMulVec_apply]
    rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ fun k _ =>
      (hv_hcol_pair_int μ D j k i).const_mul (Pm i k))]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_finsetSum _ (fun k _ => (hv_hcol_pair_int μ D j k i).const_mul (Pm i k))]
    simp only [integral_const_mul, hM]
  rw [heq]
  simp only [M, Matrix.mul_add, Matrix.mul_smul, Matrix.trace_add, Matrix.trace_smul,
    smul_eq_mul, hv_quadratic_trace]

private lemma hv_quadratic_op_bound {n : ℕ} (Pm : Matrix (Fin n) (Fin n) ℝ)
    (x : Fin n → ℝ) :
    |x ⬝ᵥ (Pm *ᵥ x)| ≤ Muon.External.matOpNorm Pm * ∑ i, x i ^ 2 := by
  let v : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 x
  let T := LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin Pm)
  have hinner : inner ℝ v (T v) = x ⬝ᵥ (Pm *ᵥ x) := by
    simp only [EuclideanSpace.inner_eq_star_dotProduct, v, T]
    change (Pm *ᵥ x) ⬝ᵥ star x = x ⬝ᵥ (Pm *ᵥ x)
    simp only [star_trivial]
    exact dotProduct_comm _ _
  calc
    |x ⬝ᵥ (Pm *ᵥ x)| = |inner ℝ v (T v)| := congrArg abs hinner.symm
    _ ≤ ‖v‖ * ‖T v‖ := abs_real_inner_le_norm _ _
    _ ≤ ‖v‖ * (‖T‖ * ‖v‖) := mul_le_mul_of_nonneg_left (T.le_opNorm v) (norm_nonneg _)
    _ = Muon.External.matOpNorm Pm * ∑ i, x i ^ 2 := by
      rw [mul_left_comm, ← sq, EuclideanSpace.real_norm_sq_eq]
      rfl

private lemma hv_gram_trace_bound {n m : ℕ} (Pm : Matrix (Fin n) (Fin n) ℝ)
    (A : Matrix (Fin n) (Fin m) ℝ) :
    |(Pm * (A * Aᵀ)).trace| ≤ Muon.External.matOpNorm Pm * (A * Aᵀ).trace := by
  have htr : (Pm * (A * Aᵀ)).trace =
      ∑ j, (fun i => A i j) ⬝ᵥ (Pm *ᵥ (fun i => A i j)) := by
    have heq : A * Aᵀ = ∑ j, Matrix.vecMulVec (fun i => A i j) (fun i => A i j) := by
      ext i k
      simp [Matrix.mul_apply, Matrix.vecMulVec_apply, Matrix.sum_apply]
    rw [heq, Matrix.mul_sum, Matrix.trace_sum]
    exact Finset.sum_congr rfl fun j _ => (hv_quadratic_trace Pm (fun i => A i j)).symm
  have htrA : (A * Aᵀ).trace = ∑ j, ∑ i, A i j ^ 2 := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply, sq]
    rw [Finset.sum_comm]
  rw [htr, htrA, Finset.mul_sum]
  exact (Finset.abs_sum_le_sum_abs _ _).trans
    (Finset.sum_le_sum fun j _ => hv_quadratic_op_bound Pm (fun i => A i j))

private lemma hv_diag_trace_bound {n : ℕ} (Pm : Matrix (Fin n) (Fin n) ℝ)
    (μ : Fin n → ℝ) (hμ : ∀ i, 0 ≤ μ i) :
    |(Pm * Matrix.diagonal μ).trace| ≤ Muon.External.matOpNorm Pm * ∑ i, μ i := by
  have h := hv_gram_trace_bound Pm (lamHalf μ)
  rw [hv_lam_sq μ hμ] at h
  simpa only [Matrix.trace_diagonal] using h

private lemma hv_bias_scalar_bound (P : HaarParams) {n m B : ℕ} (μ : Fin n → ℝ)
    (D : Matrix (Fin n) (Fin m) ℝ) (hP : def_app_sgd_state_law P n m B μ D)
    (j : Fin m) :
    (∑ i, colMeanVec μ D j i ^ 2) +
        (2 * colC μ D j * (∑ i, μ i) + 2 * (TD μ D).trace
          + 3 * ∑ i, colMeanVec μ D j i ^ 2) / (B : ℝ)
      ≤ quadDstar P / (kOf n m B : ℝ) := by
  have hk2 : (2 : ℝ) ≤ (kOf n m B : ℝ) := by exact_mod_cast hP.2.1
  have hk : (0 : ℝ) < (kOf n m B : ℝ) := by linarith
  have hkB : (kOf n m B : ℝ) ≤ (B : ℝ) := by
    exact_mod_cast (le_trans (min_le_right _ _) (min_le_right _ _) : kOf n m B ≤ B)
  have hL : 0 ≤ P.L := P.c_pos.le.trans P.c_le_L
  have hK : 0 ≤ P.K := le_trans (by norm_num) P.one_le_K
  have hμ := hP.2.2.2.2.2.1
  have hμ0 : ∀ i, 0 ≤ μ i := fun i => P.c_pos.le.trans (hμ i).1
  have ht0 : 0 ≤ ∑ i, μ i := Finset.sum_nonneg fun i _ => hμ0 i
  have ht : ∑ i, μ i ≤ P.K * (kOf n m B : ℝ) * P.L := by
    calc
      ∑ i, μ i ≤ ∑ _i : Fin n, P.L := Finset.sum_le_sum fun i _ => (hμ i).2
      _ = (n : ℝ) * P.L := by simp
      _ ≤ P.K * (kOf n m B : ℝ) * P.L :=
        mul_le_mul_of_nonneg_right hP.2.2.1 hL
  have hC := hv_colC_bounds P μ D hP j
  have hCL : colC μ D j * (∑ i, μ i) ≤ P.L ^ 2 * P.Ccol * P.K := by
    calc
      colC μ D j * (∑ i, μ i) ≤ (P.L * P.Ccol / (kOf n m B : ℝ)) *
          (P.K * (kOf n m B : ℝ) * P.L) :=
        mul_le_mul hC.2 ht ht0 (div_nonneg (mul_nonneg hL P.Ccol_pos.le) hk.le)
      _ = _ := by field_simp <;> ring
  have hm := hv_mean_sq_bound P μ D hP j
  have hm0 : 0 ≤ ∑ i, colMeanVec μ D j i ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hm' : ∑ i, colMeanVec μ D j i ^ 2 ≤ P.L ^ 2 * P.Ccol :=
    hm.trans (div_le_self (mul_nonneg (sq_nonneg _) P.Ccol_pos.le) (by linarith))
  have hT0 := (hv_TD_psd μ D).trace_nonneg
  have hT := (haar_bounds P n m B μ D hP).2.2.1
  have hnum0 : 0 ≤ 2 * colC μ D j * (∑ i, μ i) + 2 * (TD μ D).trace
      + 3 * ∑ i, colMeanVec μ D j i ^ 2 := by
    exact add_nonneg (add_nonneg (mul_nonneg (mul_nonneg (by norm_num) hC.1) ht0)
      (mul_nonneg (by norm_num) hT0)) (mul_nonneg (by norm_num) hm0)
  have hnum : 2 * colC μ D j * (∑ i, μ i) + 2 * (TD μ D).trace
      + 3 * ∑ i, colMeanVec μ D j i ^ 2
      ≤ 2 * P.L ^ 2 * P.Ccol * P.K + 2 * haarH0 P + 3 * (P.L ^ 2 * P.Ccol) := by
    nlinarith
  calc
    _ ≤ P.L ^ 2 * P.Ccol / (kOf n m B : ℝ) +
        (2 * P.L ^ 2 * P.Ccol * P.K + 2 * haarH0 P + 3 * (P.L ^ 2 * P.Ccol)) /
          (kOf n m B : ℝ) :=
      add_le_add hm ((div_le_div_of_nonneg_left hnum0 hk hkB).trans
        (div_le_div_of_nonneg_right hnum hk.le))
    _ = _ := by unfold quadDstar; ring

private lemma hv_hcol_quadratic_bias (P : HaarParams) {n m B : ℕ} (μ : Fin n → ℝ)
    (D : Matrix (Fin n) (Fin m) ℝ) (hP : def_app_sgd_state_law P n m B μ D)
    (j : Fin m) (Pm : Matrix (Fin n) (Fin n) ℝ) :
    |(∫ β, hCol μ D β j ⬝ᵥ (Pm *ᵥ hCol μ D β j) ∂(batchLaw n m B))
        - twoR μ D / (B : ℝ) * (Pm * Matrix.diagonal μ).trace|
      ≤ Muon.External.matOpNorm Pm * (quadDstar P / (kOf n m B : ℝ)) := by
  have hB : (0 : ℝ) < B := by exact_mod_cast hP.1.2.2
  have hC := (hv_colC_bounds P μ D hP j).1
  have hμ : ∀ i, 0 ≤ μ i := fun i => P.c_pos.le.trans (hP.2.2.2.2.2.1 i).1
  have hd := hv_diag_trace_bound Pm μ hμ
  have ht : |(Pm * TD μ D).trace| ≤ Muon.External.matOpNorm Pm * (TD μ D).trace := by
    have heq : TD μ D = (Matrix.diagonal μ * D) * (Matrix.diagonal μ * D)ᵀ := by
      simp [TD, Matrix.transpose_mul, Matrix.mul_assoc]
    rw [heq]
    exact hv_gram_trace_bound _ _
  have hm := hv_quadratic_op_bound Pm (colMeanVec μ D j)
  have hc0 : 0 ≤ 2 * colC μ D j / (B : ℝ) := div_nonneg (by linarith) hB.le
  have hb0 : 0 ≤ 2 / (B : ℝ) := div_nonneg (by norm_num) hB.le
  have hb1 : 0 ≤ 1 + 3 / (B : ℝ) := by positivity
  rw [hv_hcol_quadratic_mean P μ D hP j Pm]
  have heq : (twoR μ D + 2 * colC μ D j) / (B : ℝ) * (Pm * Matrix.diagonal μ).trace
      + 2 / (B : ℝ) * (Pm * TD μ D).trace
      + (1 + 3 / (B : ℝ)) * (colMeanVec μ D j ⬝ᵥ (Pm *ᵥ colMeanVec μ D j))
      - twoR μ D / (B : ℝ) * (Pm * Matrix.diagonal μ).trace =
      (2 * colC μ D j / (B : ℝ)) * (Pm * Matrix.diagonal μ).trace
        + (2 / (B : ℝ)) * (Pm * TD μ D).trace
        + (1 + 3 / (B : ℝ)) * (colMeanVec μ D j ⬝ᵥ (Pm *ᵥ colMeanVec μ D j)) := by ring
  rw [heq]
  calc
    _ ≤ |(2 * colC μ D j / (B : ℝ)) * (Pm * Matrix.diagonal μ).trace|
        + |(2 / (B : ℝ)) * (Pm * TD μ D).trace|
        + |(1 + 3 / (B : ℝ)) * (colMeanVec μ D j ⬝ᵥ (Pm *ᵥ colMeanVec μ D j))| :=
      (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ = (2 * colC μ D j / (B : ℝ)) * |(Pm * Matrix.diagonal μ).trace|
        + (2 / (B : ℝ)) * |(Pm * TD μ D).trace|
        + (1 + 3 / (B : ℝ)) * |colMeanVec μ D j ⬝ᵥ (Pm *ᵥ colMeanVec μ D j)| := by
      rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg hc0, abs_of_nonneg hb0,
        abs_of_nonneg hb1]
    _ ≤ (2 * colC μ D j / (B : ℝ)) * (Muon.External.matOpNorm Pm * ∑ i, μ i)
        + (2 / (B : ℝ)) * (Muon.External.matOpNorm Pm * (TD μ D).trace)
        + (1 + 3 / (B : ℝ)) *
          (Muon.External.matOpNorm Pm * ∑ i, colMeanVec μ D j i ^ 2) :=
      add_le_add (add_le_add (mul_le_mul_of_nonneg_left hd hc0)
        (mul_le_mul_of_nonneg_left ht hb0)) (mul_le_mul_of_nonneg_left hm hb1)
    _ = Muon.External.matOpNorm Pm * ((∑ i, colMeanVec μ D j i ^ 2) +
        (2 * colC μ D j * (∑ i, μ i) + 2 * (TD μ D).trace
          + 3 * ∑ i, colMeanVec μ D j i ^ 2) / (B : ℝ)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (hv_bias_scalar_bound P μ D hP j) (norm_nonneg _)

private lemma hv_memLp_four_of_lint {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) (f : Ω → ℝ) (hf : AEStronglyMeasurable f ν)
    (C : ℝ) (hC : (∫⁻ x, ENNReal.ofReal (f x ^ 4) ∂ν) ≤ ENNReal.ofReal C) :
    MemLp f 4 ν := by
  have hi : Integrable (fun x => f x ^ 4) ν := by
    refine ⟨hf.pow 4, ?_⟩
    exact (hasFiniteIntegral_iff_ofReal
      (Filter.Eventually.of_forall fun x => by positivity)).2
      (lt_of_le_of_lt hC ENNReal.ofReal_lt_top)
  apply (integrable_norm_rpow_iff hf (by norm_num : (4 : ENNReal) ≠ 0)
    (by norm_num : (4 : ENNReal) ≠ ⊤)).1
  convert hi using 1
  funext x
  norm_num only [ENNReal.toReal_ofNat, Real.rpow_ofNat]
  rw [Real.norm_eq_abs, show (4 : ℕ) = 2 * 2 by decide, pow_mul, sq_abs]
  ring

private lemma hv_hcol_memLp_four (P : HaarParams) {n m B : ℕ} (μ : Fin n → ℝ)
    (D : Matrix (Fin n) (Fin m) ℝ) (hP : def_app_sgd_state_law P n m B μ D)
    (j : Fin m) (i : Fin n) :
    MemLp (fun β => hCol μ D β j i) 4 (batchLaw n m B) := by
  have : IsProbabilityMeasure (gaussBatch n m) := by unfold gaussBatch; infer_instance
  obtain ⟨V0, A4, A8, _, _, _, hbounds⟩ := lem_app_sgd_column_v P
  have h4 := (hbounds n m B μ D hP j).2.2.2.1 (Pi.single i 1)
  have hi4 : (∫⁻ p, ENNReal.ofReal (colZ μ D j p i ^ 4) ∂(gaussBatch n m)) ≤
      ENNReal.ofReal A4 := by
    simpa [single_dotProduct, Pi.single_apply, ite_pow] using h4.1
  have hZ : MemLp (fun p => colZ μ D j p i) 4 (gaussBatch n m) :=
    hv_memLp_four_of_lint _ _
      (by simp only [colZ, Pi.sub_apply, colSample, resA, lamHalf, Matrix.mulVec_diagonal,
        Matrix.mulVec, dotProduct, Matrix.mul_apply]; fun_prop) A4 hi4
  have hX : MemLp (fun p => colSample μ D j p i) 4 (gaussBatch n m) := by
    convert hZ.add (memLp_const (colMeanVec μ D j i)) using 1
    funext p
    simp [colZ]
  have hsum : MemLp (fun β : Fin B → (Fin n → ℝ) × (Fin m → ℝ) =>
      ∑ a, colSample μ D j (β a) i) 4 (batchLaw n m B) := by
    exact memLp_finsetSum _ fun a _ =>
      hX.comp_measurePreserving (measurePreserving_eval (fun _ : Fin B => gaussBatch n m) a)
  exact hsum.const_mul (1 / (B : ℝ))

private lemma hv_hcol_quadratic_memLp (P : HaarParams) {n m B : ℕ} (μ : Fin n → ℝ)
    (D : Matrix (Fin n) (Fin m) ℝ) (hP : def_app_sgd_state_law P n m B μ D)
    (j : Fin m) (Pm : Matrix (Fin n) (Fin n) ℝ) :
    MemLp (fun β => hCol μ D β j ⬝ᵥ (Pm *ᵥ hCol μ D β j)) 2
      (batchLaw n m B) := by
  simp only [hv_quadratic_trace, Matrix.trace, Matrix.diag, Matrix.mul_apply,
    Matrix.vecMulVec_apply]
  refine memLp_finsetSum _ fun i _ => memLp_finsetSum _ fun k _ => ?_
  have : ENNReal.HolderTriple 4 4 2 := ⟨by
    rw [show (4 : ENNReal) = 2 * 2 by norm_num, ENNReal.mul_inv (by norm_num) (by norm_num),
      ← add_mul, ENNReal.inv_two_add_inv_two, one_mul]⟩
  have hprod : MemLp (fun β => hCol μ D β j k * hCol μ D β j i) 2
      (batchLaw n m B) :=
    (hv_hcol_memLp_four P μ D hP j k).fun_mul (hv_hcol_memLp_four P μ D hP j i)
  exact hprod.const_mul (Pm i k)

private lemma hv_variance_le_second {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) [IsProbabilityMeasure ν] (X : Ω → ℝ) (hX : MemLp X 2 ν) :
    variance X ν ≤ ∫ x, X x ^ 2 ∂ν := by
  rw [variance_eq_sub hX]
  exact sub_le_self _ (sq_nonneg _)

private lemma hv_variance_add_le {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) [IsProbabilityMeasure ν] (X Y : Ω → ℝ)
    (hX : MemLp X 2 ν) (hY : MemLp Y 2 ν) :
    variance (X + Y) ν ≤ 2 * variance X ν + 2 * variance Y ν := by
  rw [variance_eq_integral (hX.add hY).aestronglyMeasurable.aemeasurable,
    variance_eq_integral hX.aestronglyMeasurable.aemeasurable,
    variance_eq_integral hY.aestronglyMeasurable.aemeasurable]
  have hXi := hX.integrable one_le_two
  have hYi := hY.integrable one_le_two
  change (∫ x, ((X x + Y x) - ∫ y, (X y + Y y) ∂ν) ^ 2 ∂ν) ≤ _
  rw [integral_add hXi hYi]
  calc
    _ ≤ ∫ x, (2 * (X x - ∫ y, X y ∂ν) ^ 2 +
        2 * (Y x - ∫ y, Y y ∂ν) ^ 2) ∂ν := by
      apply integral_mono ((hX.add hY).sub (memLp_const _)).integrable_sq
        (((hX.sub (memLp_const _)).integrable_sq.const_mul 2).add
          ((hY.sub (memLp_const _)).integrable_sq.const_mul 2))
      intro x
      simp only [Pi.add_apply, Pi.sub_apply]
      nlinarith [sq_nonneg ((X x - ∫ y, X y ∂ν) - (Y x - ∫ y, Y y ∂ν))]
    _ = _ := by
      rw [← integral_const_mul, ← integral_const_mul]
      exact integral_add
        ((hX.sub (memLp_const _)).integrable_sq.const_mul 2)
        ((hY.sub (memLp_const _)).integrable_sq.const_mul 2)

private lemma hv_vec_norm_mul_bound {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ)
    (x : Fin n → ℝ) :
    ∑ i, (M *ᵥ x) i ^ 2 ≤ Muon.External.matOpNorm M ^ 2 * ∑ i, x i ^ 2 := by
  let v : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 x
  let T := LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin M)
  have h := T.le_opNorm v
  have h0 : 0 ≤ ‖v‖ := norm_nonneg _
  have hT0 : 0 ≤ ‖T‖ := norm_nonneg _
  have hs := pow_le_pow_left₀ (norm_nonneg (T v)) h 2
  calc
    ∑ i, (M *ᵥ x) i ^ 2 = ‖T v‖ ^ 2 := by rw [EuclideanSpace.real_norm_sq_eq]; rfl
    _ ≤ (‖T‖ * ‖v‖) ^ 2 := hs
    _ = Muon.External.matOpNorm M ^ 2 * ∑ i, x i ^ 2 := by
      rw [mul_pow, EuclideanSpace.real_norm_sq_eq]
      rfl

private lemma hv_colZ_meas {n m : ℕ} (μ : Fin n → ℝ)
    (D : Matrix (Fin n) (Fin m) ℝ) (j : Fin m) : Measurable (colZ μ D j) := by
  refine measurable_pi_iff.mpr fun i => ?_
  unfold colZ colSample resA colMeanVec
  simp only [Pi.sub_apply]
  fun_prop

private lemma hv_colZ_memLp_four (P : HaarParams) {n m B : ℕ} (μ : Fin n → ℝ)
    (D : Matrix (Fin n) (Fin m) ℝ) (hP : def_app_sgd_state_law P n m B μ D)
    (j : Fin m) (a : Fin n → ℝ) :
    MemLp (fun p => a ⬝ᵥ colZ μ D j p) 4 (gaussBatch n m) := by
  obtain ⟨V0, A4, A8, _, _, _, hbounds⟩ := lem_app_sgd_column_v P
  have h4 := (hbounds n m B μ D hP j).2.2.2.1 a |>.1
  exact hv_memLp_four_of_lint _ _
    ((Finset.measurable_sum _ fun i _ =>
      (measurable_const.mul ((measurable_pi_apply i).comp (hv_colZ_meas μ D j)))).aestronglyMeasurable)
    (A4 * (∑ i, a i ^ 2) ^ 2) h4

private lemma hv_colZ_center (P : HaarParams) {n m B : ℕ} (μ : Fin n → ℝ)
    (D : Matrix (Fin n) (Fin m) ℝ) (hP : def_app_sgd_state_law P n m B μ D)
    (j : Fin m) (i : Fin n) :
    ∫ p, colZ μ D j p i ∂(gaussBatch n m) = 0 := by
  letI : IsProbabilityMeasure (gaussBatch n m) := by unfold gaussBatch; infer_instance
  have hμ : ∀ k, 0 ≤ μ k := fun k => P.c_pos.le.trans (hP.2.2.2.2.2.1 k).1
  have hi : Integrable (fun p => colZ μ D j p i) (gaussBatch n m) := by
    have h := hv_colZ_memLp_four P μ D hP j (Pi.single i 1)
    have h1 := h.integrable (by norm_num : (1 : ENNReal) ≤ 4)
    simpa [single_dotProduct] using h1
  have hX := hv_int_single μ D j i
  unfold colZ
  simp only [Pi.sub_apply]
  rw [integral_sub hX (integrable_const _), hv_mean_single μ hμ D j i]
  simp

private lemma hv_colZ_pair_mean (P : HaarParams) {n m B : ℕ} (μ : Fin n → ℝ)
    (D : Matrix (Fin n) (Fin m) ℝ) (hP : def_app_sgd_state_law P n m B μ D)
    (j : Fin m) (a : Fin n → ℝ) :
    ∫ p, (a ⬝ᵥ colZ μ D j p) ^ 2 ∂(gaussBatch n m) =
      a ⬝ᵥ (colCov μ D j *ᵥ a) := by
  letI : IsProbabilityMeasure (gaussBatch n m) := by unfold gaussBatch; infer_instance
  have hz i : MemLp (fun p => colZ μ D j p i) 4 (gaussBatch n m) := by
    have h := hv_colZ_memLp_four P μ D hP j (Pi.single i 1)
    simpa [single_dotProduct] using h
  have hp i k : Integrable (fun p => colZ μ D j p i * colZ μ D j p k)
      (gaussBatch n m) := by
    have : ENNReal.HolderTriple 4 4 2 := ⟨by
      rw [show (4 : ENNReal) = 2 * 2 by norm_num, ENNReal.mul_inv (by norm_num) (by norm_num),
        ← add_mul, ENNReal.inv_two_add_inv_two, one_mul]⟩
    exact ((hz i).fun_mul (hz k)).integrable one_le_two
  have he : (fun p => (a ⬝ᵥ colZ μ D j p) ^ 2) =
      fun p => ∑ i, ∑ k, (a i * a k) * (colZ μ D j p i * colZ μ D j p k) := by
    funext p
    simp only [dotProduct, sq, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => by ring
  rw [he]
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ fun k _ =>
    (hp i k).const_mul (a i * a k))]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_finsetSum _ (fun k _ => (hp i k).const_mul (a i * a k))]
  simp only [integral_const_mul, colCov, Matrix.of_apply, dotProduct, Matrix.mulVec]
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ => by ring

private lemma hv_directional_second_bound (P : HaarParams) {n m B : ℕ}
    (μ : Fin n → ℝ) (D : Matrix (Fin n) (Fin m) ℝ)
    (hP : def_app_sgd_state_law P n m B μ D) (j : Fin m) (a : Fin n → ℝ) :
    ∫ p, (a ⬝ᵥ colZ μ D j p) ^ 2 ∂(gaussBatch n m) ≤
      colV0 P * ∑ i, a i ^ 2 := by
  rw [hv_colZ_pair_mean P μ D hP j a]
  have hV := hv_cov_op_bound P μ D hP j
  exact (le_abs_self _).trans ((hv_quadratic_op_bound (colCov μ D j) a).trans
    (mul_le_mul_of_nonneg_right hV (Finset.sum_nonneg fun _ _ => sq_nonneg _)))

private lemma hv_hcol_decomp {n m B : ℕ} (μ : Fin n → ℝ)
    (D : Matrix (Fin n) (Fin m) ℝ) (j : Fin m) (hB : 0 < B)
    (β : Fin B → (Fin n → ℝ) × (Fin m → ℝ)) :
    hCol μ D β j = colMeanVec μ D j +
      (1 / (B : ℝ)) • ∑ b, colZ μ D j (β b) := by
  ext i
  have hB0 : (B : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hB.ne'
  simp only [hCol, Pi.add_apply, Pi.smul_apply, Finset.sum_apply, colZ, Pi.sub_apply,
    smul_eq_mul]
  change (1 / (B : ℝ)) * ∑ a, colSample μ D j (β a) i =
    colMeanVec μ D j i + (1 / (B : ℝ)) *
      ∑ a, (colSample μ D j (β a) i - colMeanVec μ D j i)
  rw [Finset.sum_sub_distrib, Finset.sum_const]
  simp only [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp
  ring

private lemma hv_linear_variance_bound (P : HaarParams) {n m B : ℕ}
    (μ : Fin n → ℝ) (D : Matrix (Fin n) (Fin m) ℝ)
    (hP : def_app_sgd_state_law P n m B μ D) (j : Fin m)
    (Pm : Matrix (Fin n) (Fin n) ℝ) (hPm : Pmᵀ = Pm) :
    variance (fun β => 2 * (colMeanVec μ D j ⬝ᵥ
      (Pm *ᵥ ((1 / (B : ℝ)) • ∑ b, colZ μ D j (β b))))) (batchLaw n m B) ≤
      4 * Muon.External.matOpNorm Pm ^ 2 * colV0 P *
        (P.L ^ 2 * P.Ccol / (kOf n m B : ℝ)) / (B : ℝ) := by
  letI : IsProbabilityMeasure (gaussBatch n m) := by unfold gaussBatch; infer_instance
  letI : IsProbabilityMeasure (batchLaw n m B) := by unfold batchLaw; infer_instance
  let a : Fin n → ℝ := Pm *ᵥ colMeanVec μ D j
  let Y : Fin B → (Fin B → (Fin n → ℝ) × (Fin m → ℝ)) → ℝ :=
    fun b β => a ⬝ᵥ colZ μ D j (β b)
  have hrewrite : (fun β => 2 * (colMeanVec μ D j ⬝ᵥ
      (Pm *ᵥ ((1 / (B : ℝ)) • ∑ b, colZ μ D j (β b))))) =
      fun β => (2 / (B : ℝ)) * ∑ b, Y b β := by
    funext β
    simp only [Y, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul, Finset.mul_sum]
    have hs : ∀ z : Fin n → ℝ,
        colMeanVec μ D j ⬝ᵥ (Pm *ᵥ z) = a ⬝ᵥ z := by
      intro z
      rw [Matrix.dotProduct_mulVec]
      congr 1
      funext i
      simp only [a, Matrix.vecMul, Matrix.mulVec]
      refine Finset.sum_congr rfl fun k _ => ?_
      have hp := congrFun (congrFun hPm k) i
      simp only [Matrix.transpose_apply] at hp
      change colMeanVec μ D j k * Pm k i = Pm i k * colMeanVec μ D j k
      rw [← hp]
      ring
    simp_rw [hs]
    rw [dotProduct_sum]
    rw [← mul_assoc, Finset.mul_sum]
    exact Finset.sum_congr rfl fun b _ => by ring
  rw [hrewrite, variance_const_mul]
  have hsumfun : (fun β => ∑ b, Y b β) = ∑ b, Y b := by
    funext β
    simp
  rw [hsumfun]
  rw [IndepFun.variance_sum]
  · have hB : (0 : ℝ) < B := by exact_mod_cast hP.1.2.2
    have hvar : ∀ b : Fin B, variance (Y b) (batchLaw n m B) ≤
        colV0 P * ∑ i, a i ^ 2 := by
      intro b
      have hmem : MemLp (Y b) 2 (batchLaw n m B) :=
        ((hv_colZ_memLp_four P μ D hP j a).comp_measurePreserving
          (measurePreserving_eval (fun _ : Fin B => gaussBatch n m) b)).mono_exponent
          (by norm_num)
      refine (hv_variance_le_second _ _ hmem).trans ?_
      have he := integral_comp_eval (μ := fun _ : Fin B => gaussBatch n m) (i := b)
        (f := fun p => (a ⬝ᵥ colZ μ D j p) ^ 2)
        (((hv_colZ_memLp_four P μ D hP j a).mono_exponent
          (by norm_num : (2 : ENNReal) ≤ 4)).integrable_sq.aestronglyMeasurable)
      rw [batchLaw, he]
      exact hv_directional_second_bound P μ D hP j a
    have ha := hv_vec_norm_mul_bound Pm (colMeanVec μ D j)
    have hm := hv_mean_sq_bound P μ D hP j
    have hV0 : 0 ≤ colV0 P := by
      have hL : 0 ≤ P.L := P.c_pos.le.trans P.c_le_L
      have hC : 0 ≤ P.Ccol := P.Ccol_pos.le
      unfold colV0 haarPplus haarH0
      positivity
    have hop0 : 0 ≤ Muon.External.matOpNorm Pm ^ 2 := sq_nonneg _
    calc
      (2 / (B : ℝ)) ^ 2 * ∑ b : Fin B, variance (Y b) (batchLaw n m B)
          ≤ (2 / (B : ℝ)) ^ 2 * ∑ _b : Fin B, (colV0 P * ∑ i, a i ^ 2) := by
            gcongr with b
            exact hvar b
      _ ≤ (2 / (B : ℝ)) ^ 2 *
          ((B : ℝ) * (colV0 P * (Muon.External.matOpNorm Pm ^ 2 *
            ∑ i, colMeanVec μ D j i ^ 2))) := by
            simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
            gcongr
      _ ≤ (2 / (B : ℝ)) ^ 2 *
          ((B : ℝ) * (colV0 P * (Muon.External.matOpNorm Pm ^ 2 *
            (P.L ^ 2 * P.Ccol / (kOf n m B : ℝ))))) := by
            gcongr
      _ = _ := by field_simp; ring
  · intro b _
    exact ((hv_colZ_memLp_four P μ D hP j a).comp_measurePreserving
      (measurePreserving_eval (fun _ : Fin B => gaussBatch n m) b)).mono_exponent
      (by norm_num)
  · intro b _ b' _ hne
    have hind := (iIndepFun_pi (μ := fun _ : Fin B => gaussBatch n m)
      (X := fun _ => (id : (Fin n → ℝ) × (Fin m → ℝ) →
        (Fin n → ℝ) × (Fin m → ℝ))) (fun _ => measurable_id.aemeasurable)).indepFun hne
    exact hind.comp
      ((Finset.measurable_sum _ fun i _ => measurable_const.mul
        ((measurable_pi_apply i).comp (hv_colZ_meas μ D j))).comp measurable_id)
      ((Finset.measurable_sum _ fun i _ => measurable_const.mul
        ((measurable_pi_apply i).comp (hv_colZ_meas μ D j))).comp measurable_id)

private lemma hv_mean_abs_centered_le {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) [IsProbabilityMeasure ν] (X : Ω → ℝ) (hX : MemLp X 2 ν) :
    (∫ x, |X x - ∫ y, X y ∂ν| ∂ν) ≤ Real.sqrt (variance X ν) := by
  have hcenter : MemLp (fun x => X x - ∫ y, X y ∂ν) 2 ν := hX.sub (memLp_const _)
  have habs : MemLp (fun x => |X x - ∫ y, X y ∂ν|) 2 ν := hcenter.abs
  have hvar := variance_nonneg (fun x => |X x - ∫ y, X y ∂ν|) ν
  rw [variance_eq_sub habs] at hvar
  simp only [Pi.pow_apply, sq_abs] at hvar
  have hv : variance X ν = ∫ x, (X x - ∫ y, X y ∂ν) ^ 2 ∂ν :=
    variance_eq_integral hX.aestronglyMeasurable.aemeasurable
  rw [← hv] at hvar
  have hsq := Real.sq_sqrt (variance_nonneg X ν)
  have hn := Real.sqrt_nonneg (variance X ν)
  have hi : 0 ≤ ∫ x, |X x - ∫ y, X y ∂ν| ∂ν := integral_nonneg fun _ => abs_nonneg _
  nlinarith

private lemma hv_quadratic_bound_of_variance (P : HaarParams) {n m B : ℕ}
    (μ : Fin n → ℝ) (D : Matrix (Fin n) (Fin m) ℝ)
    (hP : def_app_sgd_state_law P n m B μ D) (j : Fin m)
    (Pm : Matrix (Fin n) (Fin n) ℝ)
    (hvar : variance (fun β => hCol μ D β j ⬝ᵥ (Pm *ᵥ hCol μ D β j))
      (batchLaw n m B) ≤ Muon.External.matOpNorm Pm ^ 2 *
        (quadVstar P / (kOf n m B : ℝ))) :
    (∫⁻ β, ENNReal.ofReal |hCol μ D β j ⬝ᵥ (Pm *ᵥ hCol μ D β j)
      - twoR μ D / (B : ℝ) * (Pm * Matrix.diagonal μ).trace| ∂(batchLaw n m B)) ≤
      ENNReal.ofReal (Muon.External.matOpNorm Pm *
        (Real.sqrt (quadVstar P / (kOf n m B : ℝ)) + quadDstar P / (kOf n m B : ℝ))) := by
  have : IsProbabilityMeasure (gaussBatch n m) := by unfold gaussBatch; infer_instance
  have : IsProbabilityMeasure (batchLaw n m B) := by unfold batchLaw; infer_instance
  let X : (Fin B → (Fin n → ℝ) × (Fin m → ℝ)) → ℝ :=
    fun β => hCol μ D β j ⬝ᵥ (Pm *ᵥ hCol μ D β j)
  let c := twoR μ D / (B : ℝ) * (Pm * Matrix.diagonal μ).trace
  have hX : MemLp X 2 (batchLaw n m B) := hv_hcol_quadratic_memLp P μ D hP j Pm
  have hi : Integrable (fun β => |X β - c|) (batchLaw n m B) :=
    ((hX.integrable (by norm_num)).sub (integrable_const _)).abs
  rw [← ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall fun _ => abs_nonneg _)]
  apply ENNReal.ofReal_le_ofReal
  have htri : (∫ β, |X β - c| ∂(batchLaw n m B)) ≤
      (∫ β, |X β - ∫ γ, X γ ∂(batchLaw n m B)| ∂(batchLaw n m B)) +
        |(∫ γ, X γ ∂(batchLaw n m B)) - c| := by
    have hcent : Integrable (fun β => |X β - ∫ γ, X γ ∂(batchLaw n m B)|)
        (batchLaw n m B) := ((hX.integrable (by norm_num)).sub (integrable_const _)).abs
    calc
      _ ≤ ∫ β, |X β - ∫ γ, X γ ∂(batchLaw n m B)| +
          |(∫ γ, X γ ∂(batchLaw n m B)) - c| ∂(batchLaw n m B) := by
        apply integral_mono hi (hcent.add (integrable_const _))
        intro β
        dsimp
        simpa only [sub_add_sub_cancel] using
          abs_add_le (X β - ∫ γ, X γ ∂(batchLaw n m B))
            ((∫ γ, X γ ∂(batchLaw n m B)) - c)
      _ = _ := by
        rw [integral_add hcent (integrable_const _)]
        simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
  have hbias := hv_hcol_quadratic_bias P μ D hP j Pm
  have hfl := (hv_mean_abs_centered_le (batchLaw n m B) X hX).trans (Real.sqrt_le_sqrt hvar)
  rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs,
    abs_of_nonneg (show 0 ≤ Muon.External.matOpNorm Pm from norm_nonneg _)] at hfl
  calc
    _ ≤ _ := htri
    _ ≤ Muon.External.matOpNorm Pm * Real.sqrt (quadVstar P / (kOf n m B : ℝ)) +
        Muon.External.matOpNorm Pm * (quadDstar P / (kOf n m B : ℝ)) := add_le_add hfl hbias
    _ = _ := by ring

private lemma hv_quad_constants_nonneg (P : HaarParams) :
    0 ≤ quadVstar P ∧ 0 ≤ quadDstar P := by
  have hL : 0 ≤ P.L := P.c_pos.le.trans P.c_le_L
  have hK : 0 ≤ P.K := (by norm_num : (0 : ℝ) ≤ 1).trans P.one_le_K
  have hC : 0 ≤ P.Ccol := P.Ccol_pos.le
  constructor
  · unfold quadVstar colA4 colV0 haarPplus haarH0
    positivity
  · unfold quadDstar haarH0
    positivity

private lemma hv_integrable_triple {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) [IsFiniteMeasure ν] (f g h : Ω → ℝ)
    (hf : MemLp f 4 ν) (hg : MemLp g 4 ν) (hh : MemLp h 4 ν) :
    Integrable (fun ω => f ω * g ω * h ω) ν := by
  have h44 : ENNReal.HolderTriple 4 4 2 := ⟨by
    rw [show (4 : ENNReal) = 2 * 2 by norm_num, ENNReal.mul_inv (by norm_num) (by norm_num),
      ← add_mul, ENNReal.inv_two_add_inv_two, one_mul]⟩
  have h22 : ENNReal.HolderTriple 2 2 1 := ⟨by
    simpa using ENNReal.inv_two_add_inv_two⟩
  have hfg : MemLp (fun ω => f ω * g ω) 2 ν := hf.fun_mul hg
  have hh2 : MemLp h 2 ν := hh.mono_exponent (by norm_num)
  exact (hfg.fun_mul hh2).integrable le_rfl

private lemma hv_integral_four_zero_of_unique {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) [IsProbabilityMeasure ν] {B n : ℕ}
    (Zs : Fin B → Ω → (Fin n → ℝ)) (hZs : ∀ b, Measurable (Zs b))
    (hind : iIndepFun Zs ν) (hcent : ∀ b i, ∫ ω, Zs b ω i ∂ν = 0)
    (hmem : ∀ b i, MemLp (fun ω => Zs b ω i) 4 ν)
    (b c d e : Fin B) (i k p q : Fin n)
    (hbc : b ≠ c) (hbd : b ≠ d) (hbe : b ≠ e) :
    ∫ ω, Zs b ω i * Zs c ω k * (Zs d ω p * Zs e ω q) ∂ν = 0 := by
  let S : Finset (Fin B) := {b}
  let T : Finset (Fin B) := {c, d, e}
  have hdisj : Disjoint S T := by
    simp only [S, T, Finset.disjoint_left, Finset.mem_singleton, Finset.mem_insert,
      Finset.mem_singleton]
    aesop
  have hpair := hind.indepFun_finset S T hdisj hZs
  let ib : S := ⟨b, by simp [S]⟩
  let ic : T := ⟨c, by simp [T]⟩
  let id : T := ⟨d, by simp [T]⟩
  let ie : T := ⟨e, by simp [T]⟩
  have hi : IndepFun (fun ω => Zs b ω i)
      (fun ω => Zs c ω k * (Zs d ω p * Zs e ω q)) ν := by
    have hc := hpair.comp
      (φ := fun x : S → (Fin n → ℝ) => x ib i)
      (ψ := fun x : T → (Fin n → ℝ) => x ic k * (x id p * x ie q))
      (by fun_prop) (by fun_prop)
    refine hc.congr ?_ ?_
    · filter_upwards with ω
      rfl
    · filter_upwards with ω
      rfl
  have hbint : Integrable (fun ω => Zs b ω i) ν :=
    (hmem b i).integrable (by norm_num)
  have hrest : Integrable (fun ω => Zs c ω k * (Zs d ω p * Zs e ω q)) ν := by
    have := hv_integrable_triple ν (fun ω => Zs c ω k) (fun ω => Zs d ω p)
      (fun ω => Zs e ω q) (hmem c k) (hmem d p) (hmem e q)
    convert this using 1 <;> ring
  calc
    _ = ∫ ω, Zs b ω i * (Zs c ω k * (Zs d ω p * Zs e ω q)) ∂ν := by
      congr 1
      funext ω
      ring
    _ = (∫ ω, Zs b ω i ∂ν) *
        ∫ ω, Zs c ω k * (Zs d ω p * Zs e ω q) ∂ν :=
      hi.integral_fun_mul_eq_mul_integral hbint.aestronglyMeasurable
        hrest.aestronglyMeasurable
    _ = 0 := by rw [hcent b i, zero_mul]

private lemma hv_integrable_four {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) [IsFiniteMeasure ν] (f g h k : Ω → ℝ)
    (hf : MemLp f 4 ν) (hg : MemLp g 4 ν) (hh : MemLp h 4 ν) (hk : MemLp k 4 ν) :
    Integrable (fun ω => f ω * g ω * (h ω * k ω)) ν := by
  have h44 : ENNReal.HolderTriple 4 4 2 := ⟨by
    rw [show (4 : ENNReal) = 2 * 2 by norm_num, ENNReal.mul_inv (by norm_num) (by norm_num),
      ← add_mul, ENNReal.inv_two_add_inv_two, one_mul]⟩
  have h22 : ENNReal.HolderTriple 2 2 1 := ⟨by
    simpa using ENNReal.inv_two_add_inv_two⟩
  have hfg : MemLp (fun ω => f ω * g ω) 2 ν := hf.fun_mul hg
  have hhk : MemLp (fun ω => h ω * k ω) 2 ν := hh.fun_mul hk
  exact (hfg.fun_mul hhk).integrable le_rfl

private lemma hv_bilinear_cross_integral_zero {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) [IsProbabilityMeasure ν] {B n : ℕ}
    (Zs : Fin B → Ω → (Fin n → ℝ)) (hZs : ∀ b, Measurable (Zs b))
    (hind : iIndepFun Zs ν) (hcent : ∀ b i, ∫ ω, Zs b ω i ∂ν = 0)
    (hmem : ∀ b i, MemLp (fun ω => Zs b ω i) 4 ν)
    (M : Matrix (Fin n) (Fin n) ℝ) (b c d e : Fin B)
    (hbc : b ≠ c) (hde : d ≠ e)
    (hpairs : ¬ ((b = d ∧ c = e) ∨ (b = e ∧ c = d))) :
    ∫ ω, (Zs b ω ⬝ᵥ (M *ᵥ Zs c ω)) *
      (Zs d ω ⬝ᵥ (M *ᵥ Zs e ω)) ∂ν = 0 := by
  have huniq :
      (b ≠ c ∧ b ≠ d ∧ b ≠ e) ∨ (c ≠ b ∧ c ≠ d ∧ c ≠ e) ∨
      (d ≠ b ∧ d ≠ c ∧ d ≠ e) ∨ (e ≠ b ∧ e ≠ c ∧ e ≠ d) := by
    by_cases hbd : b = d
    · have hce : c ≠ e := fun hce => hpairs (Or.inl ⟨hbd, hce⟩)
      right
      left
      exact ⟨hbc.symm, fun hcd => hbc (hcd.trans hbd.symm).symm, hce⟩
    by_cases hbe : b = e
    · have hcd : c ≠ d := fun hcd => hpairs (Or.inr ⟨hbe, hcd⟩)
      right
      left
      exact ⟨hbc.symm, hcd, fun hce => hbc (hce.trans hbe.symm).symm⟩
    exact Or.inl ⟨hbc, hbd, hbe⟩
  have hfour (i k p q : Fin n) :
      ∫ ω, Zs b ω i * Zs c ω k * (Zs d ω p * Zs e ω q) ∂ν = 0 := by
    rcases huniq with hb | hc | hd | he
    · exact hv_integral_four_zero_of_unique ν Zs hZs hind hcent hmem
        b c d e i k p q hb.1 hb.2.1 hb.2.2
    · have hz := hv_integral_four_zero_of_unique ν Zs hZs hind hcent hmem
        c b d e k i p q hc.1 hc.2.1 hc.2.2
      rw [← hz]
      apply integral_congr_ae
      filter_upwards with ω
      ring
    · have hz := hv_integral_four_zero_of_unique ν Zs hZs hind hcent hmem
        d b c e p i k q hd.1 hd.2.1 hd.2.2
      rw [← hz]
      apply integral_congr_ae
      filter_upwards with ω
      ring
    · have hz := hv_integral_four_zero_of_unique ν Zs hZs hind hcent hmem
        e b c d q i k p he.1 he.2.1 he.2.2
      rw [← hz]
      apply integral_congr_ae
      filter_upwards with ω
      ring
  have hint (i k p q : Fin n) : Integrable
      (fun ω => (M i k * M p q) *
        (Zs b ω i * Zs c ω k * (Zs d ω p * Zs e ω q))) ν :=
    (hv_integrable_four ν (fun ω => Zs b ω i) (fun ω => Zs c ω k)
      (fun ω => Zs d ω p) (fun ω => Zs e ω q)
      (hmem b i) (hmem c k) (hmem d p) (hmem e q)).const_mul _
  have hexpand : (fun ω => (Zs b ω ⬝ᵥ (M *ᵥ Zs c ω)) *
      (Zs d ω ⬝ᵥ (M *ᵥ Zs e ω))) =
      fun ω => ∑ i, ∑ k, ∑ p, ∑ q, (M p q * M i k) *
        (Zs b ω p * Zs c ω q * (Zs d ω i * Zs e ω k)) := by
    funext ω
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ =>
      Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => by ring
  rw [hexpand]
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ fun k _ =>
    integrable_finsetSum _ fun p _ => integrable_finsetSum _ fun q _ => hint p q i k)]
  apply Finset.sum_eq_zero
  intro i _
  rw [integral_finsetSum _ (fun k _ => integrable_finsetSum _ fun p _ =>
    integrable_finsetSum _ fun q _ => hint p q i k)]
  apply Finset.sum_eq_zero
  intro k _
  rw [integral_finsetSum _ (fun p _ => integrable_finsetSum _ fun q _ => hint p q i k)]
  apply Finset.sum_eq_zero
  intro p _
  rw [integral_finsetSum _ (fun q _ => hint p q i k)]
  apply Finset.sum_eq_zero
  intro q _
  rw [integral_const_mul, hfour p q i k, mul_zero]

private lemma hv_directional_second_lintegral_bound (P : HaarParams) {n m B : ℕ}
    (μ : Fin n → ℝ) (D : Matrix (Fin n) (Fin m) ℝ)
    (hP : def_app_sgd_state_law P n m B μ D) (j : Fin m) (a : Fin n → ℝ) :
    ∫⁻ p, ENNReal.ofReal ((a ⬝ᵥ colZ μ D j p) ^ 2) ∂(gaussBatch n m) ≤
      ENNReal.ofReal (colV0 P * ∑ i, a i ^ 2) := by
  letI : IsProbabilityMeasure (gaussBatch n m) := by unfold gaussBatch; infer_instance
  have hmem := (hv_colZ_memLp_four P μ D hP j a).mono_exponent
    (by norm_num : (2 : ENNReal) ≤ 4)
  rw [← ofReal_integral_eq_lintegral_ofReal hmem.integrable_sq
    (Filter.Eventually.of_forall fun _ => sq_nonneg _)]
  exact ENNReal.ofReal_le_ofReal (hv_directional_second_bound P μ D hP j a)

private lemma hv_colZ_norm_second_lintegral_bound (P : HaarParams) {n m B : ℕ}
    (μ : Fin n → ℝ) (D : Matrix (Fin n) (Fin m) ℝ)
    (hP : def_app_sgd_state_law P n m B μ D) (j : Fin m) :
    ∫⁻ p, ENNReal.ofReal (∑ i, colZ μ D j p i ^ 2) ∂(gaussBatch n m) ≤
      ENNReal.ofReal ((n : ℝ) * colV0 P) := by
  have hmeas : ∀ i, Measurable (fun p => ENNReal.ofReal (colZ μ D j p i ^ 2)) :=
    fun i => ENNReal.measurable_ofReal.comp
      (((measurable_pi_apply i).comp (hv_colZ_meas μ D j)).pow_const 2)
  have heq : (fun p => ENNReal.ofReal (∑ i, colZ μ D j p i ^ 2)) =
      fun p => ∑ i, ENNReal.ofReal (colZ μ D j p i ^ 2) := by
    funext p
    exact ENNReal.ofReal_sum_of_nonneg (fun i _ => sq_nonneg _)
  rw [heq, lintegral_finsetSum _ (fun i _ => hmeas i)]
  calc
    ∑ i, ∫⁻ p, ENNReal.ofReal (colZ μ D j p i ^ 2) ∂(gaussBatch n m)
        ≤ ∑ _i : Fin n, ENNReal.ofReal (colV0 P) := by
          gcongr with i
          have h := hv_directional_second_lintegral_bound P μ D hP j (Pi.single i 1)
          simpa [single_dotProduct, Pi.single_apply, ite_pow] using h
    _ = ENNReal.ofReal ((n : ℝ) * colV0 P) := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
        ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg n)]

private lemma hv_lintegral_indep_bound {Ω E F : Type*} [MeasurableSpace Ω]
    [MeasurableSpace E] [MeasurableSpace F] (ν : Measure Ω) [IsProbabilityMeasure ν]
    {X : Ω → E} {Y : Ω → F} (hX : Measurable X) (hY : Measurable Y)
    (hind : IndepFun X Y ν) (Φ : E → F → ENNReal)
    (hΦ : Measurable (fun p : E × F => Φ p.1 p.2))
    (ψ : F → ENNReal) (hψ : Measurable ψ)
    (h : ∀ y, ∫⁻ ω, Φ (X ω) y ∂ν ≤ ψ y) :
    ∫⁻ ω, Φ (X ω) (Y ω) ∂ν ≤ ∫⁻ ω, ψ (Y ω) ∂ν := by
  have hmap := (indepFun_iff_map_prod_eq_prod_map_map
    hX.aemeasurable hY.aemeasurable).1 hind
  have hXY : Measurable (fun ω => (X ω, Y ω)) := hX.prodMk hY
  have heq : ∫⁻ ω, Φ (X ω) (Y ω) ∂ν =
      ∫⁻ p, Φ p.1 p.2 ∂((ν.map X).prod (ν.map Y)) := by
    rw [← hmap, lintegral_map hΦ hXY]
  rw [heq, lintegral_prod_symm _ hΦ.aemeasurable, ← lintegral_map hψ hY]
  exact lintegral_mono fun y => by
    calc
      ∫⁻ x, Φ x y ∂(ν.map X) = ∫⁻ ω, Φ (X ω) y ∂ν :=
        lintegral_map (hΦ.comp (measurable_id.prodMk measurable_const)) hX
      _ ≤ ψ y := h y

private lemma hv_bilinear_second_lintegral_bound (P : HaarParams) {n m B : ℕ}
    (μ : Fin n → ℝ) (D : Matrix (Fin n) (Fin m) ℝ)
    (hP : def_app_sgd_state_law P n m B μ D) (j : Fin m)
    (Pm : Matrix (Fin n) (Fin n) ℝ) (b c : Fin B) (hbc : b ≠ c) :
    ∫⁻ β, ENNReal.ofReal ((colZ μ D j (β b) ⬝ᵥ
      (Pm *ᵥ colZ μ D j (β c))) ^ 2) ∂(batchLaw n m B) ≤
      ENNReal.ofReal (Muon.External.matOpNorm Pm ^ 2 * (n : ℝ) * colV0 P ^ 2) := by
  letI : IsProbabilityMeasure (gaussBatch n m) := by unfold gaussBatch; infer_instance
  letI : IsProbabilityMeasure (batchLaw n m B) := by unfold batchLaw; infer_instance
  let Zs : Fin B → (Fin B → (Fin n → ℝ) × (Fin m → ℝ)) → (Fin n → ℝ) :=
    fun r β => colZ μ D j (β r)
  have hZm : ∀ r, Measurable (Zs r) := fun r =>
    (hv_colZ_meas μ D j).comp (measurable_pi_apply r)
  have hind : iIndepFun Zs (batchLaw n m B) :=
    iIndepFun_pi (μ := fun _ : Fin B => gaussBatch n m)
      (X := fun _ => colZ μ D j) (fun _ => (hv_colZ_meas μ D j).aemeasurable)
  have hV0 : 0 ≤ colV0 P := by
    have hL : 0 ≤ P.L := P.c_pos.le.trans P.c_le_L
    have hC : 0 ≤ P.Ccol := P.Ccol_pos.le
    unfold colV0 haarPplus haarH0
    positivity
  have hA4 : 0 ≤ colA4 P := by
    have hL : 0 ≤ P.L := P.c_pos.le.trans P.c_le_L
    unfold colA4 haarPplus
    positivity
  have hop : 0 ≤ Muon.External.matOpNorm Pm ^ 2 := sq_nonneg _
  let Φ : (Fin n → ℝ) → (Fin n → ℝ) → ENNReal :=
    fun x y => ENNReal.ofReal ((x ⬝ᵥ (Pm *ᵥ y)) ^ 2)
  let ψ : (Fin n → ℝ) → ENNReal := fun y =>
    ENNReal.ofReal (colV0 P * (Muon.External.matOpNorm Pm ^ 2 * ∑ i, y i ^ 2))
  have hΦ : Measurable (fun p : (Fin n → ℝ) × (Fin n → ℝ) => Φ p.1 p.2) := by
    simp only [Φ, dotProduct, Matrix.mulVec]
    fun_prop
  have hψ : Measurable ψ := by
    simp only [ψ]
    fun_prop
  have hinner : ∀ y, ∫⁻ β, Φ (Zs b β) y ∂(batchLaw n m B) ≤ ψ y := by
    intro y
    have hfun : Measurable (fun p =>
        ENNReal.ofReal (((Pm *ᵥ y) ⬝ᵥ colZ μ D j p) ^ 2)) := by
      exact ENNReal.measurable_ofReal.comp
        ((Finset.measurable_sum _ fun i _ => measurable_const.mul
          ((measurable_pi_apply i).comp (hv_colZ_meas μ D j))).pow_const 2)
    have heval := (measurePreserving_eval (fun _ : Fin B => gaussBatch n m) b).lintegral_comp
      hfun
    have hdir := hv_directional_second_lintegral_bound P μ D hP j (Pm *ᵥ y)
    have hopv := hv_vec_norm_mul_bound Pm y
    calc
      ∫⁻ β, Φ (Zs b β) y ∂(batchLaw n m B) =
          ∫⁻ β, ENNReal.ofReal (((Pm *ᵥ y) ⬝ᵥ colZ μ D j (β b)) ^ 2)
            ∂(batchLaw n m B) := by
              apply lintegral_congr
              intro β
              simp only [Φ, Zs]
              rw [dotProduct_comm]
      _ =
          ∫⁻ p, ENNReal.ofReal (((Pm *ᵥ y) ⬝ᵥ colZ μ D j p) ^ 2)
            ∂(gaussBatch n m) := by
              rw [show batchLaw n m B = Measure.pi (fun _ : Fin B => gaussBatch n m) by rfl]
              rw [heval]
      _ ≤ ENNReal.ofReal (colV0 P * ∑ i, (Pm *ᵥ y) i ^ 2) := hdir
      _ ≤ ψ y := ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hopv hV0)
  have hmain := hv_lintegral_indep_bound (batchLaw n m B) (hZm b) (hZm c)
    (hind.indepFun hbc) Φ hΦ ψ hψ hinner
  have hC : 0 ≤ colV0 P * Muon.External.matOpNorm Pm ^ 2 := mul_nonneg hV0 hop
  have houter : ∫⁻ β, ψ (Zs c β) ∂(batchLaw n m B) ≤
      ENNReal.ofReal (Muon.External.matOpNorm Pm ^ 2 * (n : ℝ) * colV0 P ^ 2) := by
    have heval := (measurePreserving_eval (fun _ : Fin B => gaussBatch n m) c).lintegral_comp
      (hψ.comp (hv_colZ_meas μ D j))
    rw [show batchLaw n m B = Measure.pi (fun _ : Fin B => gaussBatch n m) by rfl,
      show (∫⁻ β, ψ (colZ μ D j (β c)) ∂Measure.pi
        fun _ : Fin B => gaussBatch n m) =
        ∫⁻ p, ψ (colZ μ D j p) ∂(gaussBatch n m) from heval]
    simp only [ψ, Zs]
    have hnorm := hv_colZ_norm_second_lintegral_bound P μ D hP j
    simp_rw [show colV0 P * (Muon.External.matOpNorm Pm ^ 2 *
      ∑ i, colZ μ D j _ i ^ 2) =
      (colV0 P * Muon.External.matOpNorm Pm ^ 2) *
        (∑ i, colZ μ D j _ i ^ 2) by ring,
      ENNReal.ofReal_mul hC]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    calc
      ENNReal.ofReal (colV0 P * Muon.External.matOpNorm Pm ^ 2) *
          ∫⁻ p, ENNReal.ofReal (∑ i, colZ μ D j p i ^ 2) ∂(gaussBatch n m)
          ≤ ENNReal.ofReal (colV0 P * Muon.External.matOpNorm Pm ^ 2) *
            ENNReal.ofReal ((n : ℝ) * colV0 P) := by gcongr
      _ = _ := by
        rw [← ENNReal.ofReal_mul hC]
        congr 1
        ring
  exact hmain.trans houter

private lemma hv_colZ_bilinear_memLp (P : HaarParams) {n m B : ℕ}
    (μ : Fin n → ℝ) (D : Matrix (Fin n) (Fin m) ℝ)
    (hP : def_app_sgd_state_law P n m B μ D) (j : Fin m)
    (Pm : Matrix (Fin n) (Fin n) ℝ) (b c : Fin B) :
    MemLp (fun β => colZ μ D j (β b) ⬝ᵥ (Pm *ᵥ colZ μ D j (β c))) 2
      (batchLaw n m B) := by
  letI : IsProbabilityMeasure (gaussBatch n m) := by unfold gaussBatch; infer_instance
  letI : IsProbabilityMeasure (batchLaw n m B) := by unfold batchLaw; infer_instance
  have h4 (r : Fin B) (i : Fin n) :
      MemLp (fun β => colZ μ D j (β r) i) 4 (batchLaw n m B) := by
    have hz : MemLp (fun p => colZ μ D j p i) 4 (gaussBatch n m) := by
      have h := hv_colZ_memLp_four P μ D hP j (Pi.single i 1)
      simpa [single_dotProduct] using h
    exact hz.comp_measurePreserving
      (measurePreserving_eval (fun _ : Fin B => gaussBatch n m) r)
  letI : ENNReal.HolderTriple 4 4 2 := ⟨by
    rw [show (4 : ENNReal) = 2 * 2 by norm_num, ENNReal.mul_inv (by norm_num) (by norm_num),
      ← add_mul, ENNReal.inv_two_add_inv_two, one_mul]⟩
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
  refine memLp_finsetSum _ fun i _ => memLp_finsetSum _ fun k _ => ?_
  have hp : MemLp (fun β => colZ μ D j (β b) i * colZ μ D j (β c) k) 2
      (batchLaw n m B) := (h4 b i).fun_mul (h4 c k)
  convert hp.const_mul (Pm i k) using 1
  funext β
  ring

private lemma hv_colZ_bilinear_second_bound (P : HaarParams) {n m B : ℕ}
    (μ : Fin n → ℝ) (D : Matrix (Fin n) (Fin m) ℝ)
    (hP : def_app_sgd_state_law P n m B μ D) (j : Fin m)
    (Pm : Matrix (Fin n) (Fin n) ℝ) (b c : Fin B) (hbc : b ≠ c) :
    ∫ β, (colZ μ D j (β b) ⬝ᵥ (Pm *ᵥ colZ μ D j (β c))) ^ 2
        ∂(batchLaw n m B) ≤
      Muon.External.matOpNorm Pm ^ 2 * (n : ℝ) * colV0 P ^ 2 := by
  have hmem := hv_colZ_bilinear_memLp P μ D hP j Pm b c
  have hC : 0 ≤ Muon.External.matOpNorm Pm ^ 2 * (n : ℝ) * colV0 P ^ 2 := by
    positivity
  apply (ENNReal.ofReal_le_ofReal_iff hC).mp
  rw [ofReal_integral_eq_lintegral_ofReal hmem.integrable_sq
    (Filter.Eventually.of_forall fun _ => sq_nonneg _)]
  exact hv_bilinear_second_lintegral_bound P μ D hP j Pm b c hbc

private lemma hv_colZ_diagonal_second_bound (P : HaarParams) {n m B : ℕ}
    (μ : Fin n → ℝ) (D : Matrix (Fin n) (Fin m) ℝ)
    (hP : def_app_sgd_state_law P n m B μ D) (j : Fin m)
    (Pm : Matrix (Fin n) (Fin n) ℝ) (b : Fin B) :
    ∫ β, (colZ μ D j (β b) ⬝ᵥ (Pm *ᵥ colZ μ D j (β b))) ^ 2
        ∂(batchLaw n m B) ≤
      Muon.External.matOpNorm Pm ^ 2 * colA4 P * (n : ℝ) ^ 2 := by
  letI : IsProbabilityMeasure (gaussBatch n m) := by unfold gaussBatch; infer_instance
  letI : IsProbabilityMeasure (batchLaw n m B) := by unfold batchLaw; infer_instance
  have hmem := hv_colZ_bilinear_memLp P μ D hP j Pm b b
  have hop : 0 ≤ Muon.External.matOpNorm Pm ^ 2 := sq_nonneg _
  have hA4 : 0 ≤ colA4 P := by
    have hL : 0 ≤ P.L := P.c_pos.le.trans P.c_le_L
    unfold colA4 haarPplus
    positivity
  have hC : 0 ≤ Muon.External.matOpNorm Pm ^ 2 * colA4 P * (n : ℝ) ^ 2 := by
    positivity
  apply (ENNReal.ofReal_le_ofReal_iff hC).mp
  rw [ofReal_integral_eq_lintegral_ofReal hmem.integrable_sq
    (Filter.Eventually.of_forall fun _ => sq_nonneg _)]
  calc
    ∫⁻ β, ENNReal.ofReal
        ((colZ μ D j (β b) ⬝ᵥ (Pm *ᵥ colZ μ D j (β b))) ^ 2)
          ∂(batchLaw n m B)
        ≤ ∫⁻ β, ENNReal.ofReal (Muon.External.matOpNorm Pm ^ 2) *
            ENNReal.ofReal ((∑ i, colZ μ D j (β b) i ^ 2) ^ 2)
          ∂(batchLaw n m B) := by
            apply lintegral_mono
            intro β
            change ENNReal.ofReal
              ((colZ μ D j (β b) ⬝ᵥ (Pm *ᵥ colZ μ D j (β b))) ^ 2) ≤
              ENNReal.ofReal (Muon.External.matOpNorm Pm ^ 2) *
                ENNReal.ofReal ((∑ i, colZ μ D j (β b) i ^ 2) ^ 2)
            rw [← ENNReal.ofReal_mul hop]
            apply ENNReal.ofReal_le_ofReal
            have hq := hv_quadratic_op_bound Pm (colZ μ D j (β b))
            calc
              (colZ μ D j (β b) ⬝ᵥ (Pm *ᵥ colZ μ D j (β b))) ^ 2 =
                  |colZ μ D j (β b) ⬝ᵥ (Pm *ᵥ colZ μ D j (β b))| ^ 2 :=
                (sq_abs _).symm
              _ ≤ (Muon.External.matOpNorm Pm *
                  ∑ i, colZ μ D j (β b) i ^ 2) ^ 2 :=
                pow_le_pow_left₀ (abs_nonneg _) hq 2
              _ = _ := by ring
    _ = ENNReal.ofReal (Muon.External.matOpNorm Pm ^ 2) *
        ∫⁻ β, ENNReal.ofReal ((∑ i, colZ μ D j (β b) i ^ 2) ^ 2)
          ∂(batchLaw n m B) :=
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ = ENNReal.ofReal (Muon.External.matOpNorm Pm ^ 2) *
        ∫⁻ p, ENNReal.ofReal ((∑ i, colZ μ D j p i ^ 2) ^ 2)
          ∂(gaussBatch n m) := by
      congr 1
      exact (measurePreserving_eval (fun _ : Fin B => gaussBatch n m) b).lintegral_comp
        (ENNReal.measurable_ofReal.comp
          ((Finset.measurable_sum _ fun i _ =>
            (((measurable_pi_apply i).comp (hv_colZ_meas μ D j)).pow_const 2)).pow_const 2))
    _ ≤ ENNReal.ofReal (Muon.External.matOpNorm Pm ^ 2) *
        ENNReal.ofReal (colA4 P * (n : ℝ) ^ 2) := by
      gcongr
      have h4 : ∀ a : Fin n → ℝ,
          (∫⁻ p, ENNReal.ofReal ((a ⬝ᵥ colZ μ D j p) ^ 4) ∂(gaussBatch n m)) ≤
            ENNReal.ofReal (colA4 P * (∑ i, a i ^ 2) ^ 2) := by
        intro a
        refine (hv_directional_even_bound P μ D hP j a 2 (by norm_num)).trans ?_
        apply ENNReal.ofReal_le_ofReal
        unfold colA4
        norm_num [Nat.doubleFactorial]
        gcongr <;> norm_num
      exact hv_vector_from_directional μ D j (colA4 P) 1 h4
    _ = ENNReal.ofReal
        (Muon.External.matOpNorm Pm ^ 2 * colA4 P * (n : ℝ) ^ 2) := by
      rw [← ENNReal.ofReal_mul hop]
      congr 1
      ring

private lemma hv_colZ_bilinear_mean_zero (P : HaarParams) {n m B : ℕ}
    (μ : Fin n → ℝ) (D : Matrix (Fin n) (Fin m) ℝ)
    (hP : def_app_sgd_state_law P n m B μ D) (j : Fin m)
    (Pm : Matrix (Fin n) (Fin n) ℝ) (b c : Fin B) (hbc : b ≠ c) :
    ∫ β, colZ μ D j (β b) ⬝ᵥ (Pm *ᵥ colZ μ D j (β c))
      ∂(batchLaw n m B) = 0 := by
  letI : IsProbabilityMeasure (gaussBatch n m) := by unfold gaussBatch; infer_instance
  letI : IsProbabilityMeasure (batchLaw n m B) := by unfold batchLaw; infer_instance
  let Zs : Fin B → (Fin B → (Fin n → ℝ) × (Fin m → ℝ)) → (Fin n → ℝ) :=
    fun r β => colZ μ D j (β r)
  have hZm : ∀ r, Measurable (Zs r) := fun r =>
    (hv_colZ_meas μ D j).comp (measurable_pi_apply r)
  have hind : iIndepFun Zs (batchLaw n m B) :=
    iIndepFun_pi (μ := fun _ : Fin B => gaussBatch n m)
      (X := fun _ => colZ μ D j) (fun _ => (hv_colZ_meas μ D j).aemeasurable)
  have h4 (r : Fin B) (i : Fin n) : MemLp (fun β => Zs r β i) 4
      (batchLaw n m B) := by
    have hz : MemLp (fun p => colZ μ D j p i) 4 (gaussBatch n m) := by
      have h := hv_colZ_memLp_four P μ D hP j (Pi.single i 1)
      simpa [single_dotProduct] using h
    exact hz.comp_measurePreserving
      (measurePreserving_eval (fun _ : Fin B => gaussBatch n m) r)
  have hprod (i k : Fin n) :
      ∫ β, Zs b β i * Zs c β k ∂(batchLaw n m B) = 0 := by
    have hi : IndepFun (fun β => Zs b β i) (fun β => Zs c β k)
        (batchLaw n m B) :=
      (hind.indepFun hbc).comp ((measurable_pi_apply i)) ((measurable_pi_apply k))
    rw [hi.integral_fun_mul_eq_mul_integral
      ((h4 b i).integrable (by norm_num)).aestronglyMeasurable
      ((h4 c k).integrable (by norm_num)).aestronglyMeasurable]
    have hb : ∫ β, Zs b β i ∂(batchLaw n m B) = 0 := by
      rw [show batchLaw n m B = Measure.pi (fun _ : Fin B => gaussBatch n m) by rfl]
      exact (integral_comp_eval (μ := fun _ : Fin B => gaussBatch n m) (i := b)
        (f := fun p => colZ μ D j p i)
        (((measurable_pi_apply i).comp (hv_colZ_meas μ D j)).aestronglyMeasurable)).trans
          (hv_colZ_center P μ D hP j i)
    have hc : ∫ β, Zs c β k ∂(batchLaw n m B) = 0 := by
      rw [show batchLaw n m B = Measure.pi (fun _ : Fin B => gaussBatch n m) by rfl]
      exact (integral_comp_eval (μ := fun _ : Fin B => gaussBatch n m) (i := c)
        (f := fun p => colZ μ D j p k)
        (((measurable_pi_apply k).comp (hv_colZ_meas μ D j)).aestronglyMeasurable)).trans
          (hv_colZ_center P μ D hP j k)
    rw [hb, hc, zero_mul]
  have hprodLp (i k : Fin n) : MemLp (fun β => Zs b β i * Zs c β k) 2
      (batchLaw n m B) := by
    have h44 : ENNReal.HolderTriple 4 4 2 := ⟨by
      rw [show (4 : ENNReal) = 2 * 2 by norm_num,
        ENNReal.mul_inv (by norm_num) (by norm_num), ← add_mul,
        ENNReal.inv_two_add_inv_two, one_mul]⟩
    exact (h4 b i).fun_mul (h4 c k)
  have hint (i k : Fin n) : Integrable
      (fun β => Pm i k * (Zs b β i * Zs c β k)) (batchLaw n m B) :=
    ((hprodLp i k).integrable one_le_two).const_mul _
  have hexpand : (fun β => Zs b β ⬝ᵥ (Pm *ᵥ Zs c β)) =
      fun β => ∑ i, ∑ k, Pm i k * (Zs b β i * Zs c β k) := by
    funext β
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => by ring
  rw [hexpand]
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ fun k _ => hint i k)]
  apply Finset.sum_eq_zero
  intro i _
  rw [integral_finsetSum _ (fun k _ => hint i k)]
  exact Finset.sum_eq_zero fun k _ => by rw [integral_const_mul, hprod i k, mul_zero]

private lemma hv_diagonal_offdiag_integral_zero {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) [IsProbabilityMeasure ν] {B n : ℕ}
    (Zs : Fin B → Ω → (Fin n → ℝ)) (hZs : ∀ b, Measurable (Zs b))
    (hind : iIndepFun Zs ν) (hcent : ∀ b i, ∫ ω, Zs b ω i ∂ν = 0)
    (hmem : ∀ b i, MemLp (fun ω => Zs b ω i) 4 ν)
    (M : Matrix (Fin n) (Fin n) ℝ) (b d e : Fin B) (hde : d ≠ e) :
    ∫ ω, (Zs b ω ⬝ᵥ (M *ᵥ Zs b ω)) *
      (Zs d ω ⬝ᵥ (M *ᵥ Zs e ω)) ∂ν = 0 := by
  have hfour (i k p q : Fin n) :
      ∫ ω, Zs b ω i * Zs b ω k * (Zs d ω p * Zs e ω q) ∂ν = 0 := by
    by_cases hbd : b = d
    · have heb : e ≠ b := fun heb => hde (hbd.symm.trans heb.symm)
      have hz := hv_integral_four_zero_of_unique ν Zs hZs hind hcent hmem
        e b b d q i k p heb heb (fun hed => hde hed.symm)
      rw [← hz]
      apply integral_congr_ae
      filter_upwards with ω
      ring
    by_cases hbe : b = e
    · have hdb : d ≠ b := fun hdb => hde (hdb.trans hbe)
      have hz := hv_integral_four_zero_of_unique ν Zs hZs hind hcent hmem
        d b b e p i k q hdb hdb hde
      rw [← hz]
      apply integral_congr_ae
      filter_upwards with ω
      ring
    · have hz := hv_integral_four_zero_of_unique ν Zs hZs hind hcent hmem
        d b b e p i k q (Ne.symm hbd) (Ne.symm hbd) hde
      rw [← hz]
      apply integral_congr_ae
      filter_upwards with ω
      ring
  have hint (i k p q : Fin n) : Integrable
      (fun ω => (M i k * M p q) *
        (Zs b ω i * Zs b ω k * (Zs d ω p * Zs e ω q))) ν :=
    (hv_integrable_four ν (fun ω => Zs b ω i) (fun ω => Zs b ω k)
      (fun ω => Zs d ω p) (fun ω => Zs e ω q)
      (hmem b i) (hmem b k) (hmem d p) (hmem e q)).const_mul _
  have hexpand : (fun ω => (Zs b ω ⬝ᵥ (M *ᵥ Zs b ω)) *
      (Zs d ω ⬝ᵥ (M *ᵥ Zs e ω))) =
      fun ω => ∑ i, ∑ k, ∑ p, ∑ q, (M p q * M i k) *
        (Zs b ω p * Zs b ω q * (Zs d ω i * Zs e ω k)) := by
    funext ω
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ =>
      Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => by ring
  rw [hexpand]
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ fun k _ =>
    integrable_finsetSum _ fun p _ => integrable_finsetSum _ fun q _ => hint p q i k)]
  apply Finset.sum_eq_zero
  intro i _
  rw [integral_finsetSum _ (fun k _ => integrable_finsetSum _ fun p _ =>
    integrable_finsetSum _ fun q _ => hint p q i k)]
  apply Finset.sum_eq_zero
  intro k _
  rw [integral_finsetSum _ (fun p _ => integrable_finsetSum _ fun q _ => hint p q i k)]
  apply Finset.sum_eq_zero
  intro p _
  rw [integral_finsetSum _ (fun q _ => hint p q i k)]
  exact Finset.sum_eq_zero fun q _ => by
    rw [integral_const_mul, hfour p q i k, mul_zero]

private lemma hv_bilinear_swap {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ)
    (hM : Mᵀ = M) (x y : Fin n → ℝ) :
    x ⬝ᵥ (M *ᵥ y) = y ⬝ᵥ (M *ᵥ x) := by
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
  have hm := congrFun (congrFun hM k) i
  simp only [Matrix.transpose_apply] at hm
  rw [← hm]
  ring

private lemma hv_centered_quadratic_variance_bound (P : HaarParams) {n m B : ℕ}
    (μ : Fin n → ℝ) (D : Matrix (Fin n) (Fin m) ℝ)
    (hP : def_app_sgd_state_law P n m B μ D) (j : Fin m)
    (Pm : Matrix (Fin n) (Fin n) ℝ) (hPm : Pmᵀ = Pm) :
    variance (fun β =>
      ((1 / (B : ℝ)) • ∑ b, colZ μ D j (β b)) ⬝ᵥ
        (Pm *ᵥ ((1 / (B : ℝ)) • ∑ b, colZ μ D j (β b))))
      (batchLaw n m B) ≤ Muon.External.matOpNorm Pm ^ 2 *
        (colA4 P * (n : ℝ) ^ 2 / (B : ℝ) ^ 3 +
          2 * (n : ℝ) * colV0 P ^ 2 / (B : ℝ) ^ 2) := by
  letI : IsProbabilityMeasure (gaussBatch n m) := by unfold gaussBatch; infer_instance
  letI : IsProbabilityMeasure (batchLaw n m B) := by unfold batchLaw; infer_instance
  have hB : (0 : ℝ) < B := by exact_mod_cast hP.1.2.2
  let Zs : Fin B → (Fin B → (Fin n → ℝ) × (Fin m → ℝ)) → (Fin n → ℝ) :=
    fun r β => colZ μ D j (β r)
  let U : (Fin B × Fin B) →
      (Fin B → (Fin n → ℝ) × (Fin m → ℝ)) → ℝ :=
    fun p β => Zs p.1 β ⬝ᵥ (Pm *ᵥ Zs p.2 β)
  have hZm : ∀ r, Measurable (Zs r) := fun r =>
    (hv_colZ_meas μ D j).comp (measurable_pi_apply r)
  have hind : iIndepFun Zs (batchLaw n m B) :=
    iIndepFun_pi (μ := fun _ : Fin B => gaussBatch n m)
      (X := fun _ => colZ μ D j) (fun _ => (hv_colZ_meas μ D j).aemeasurable)
  have h4 (r : Fin B) (i : Fin n) : MemLp (fun β => Zs r β i) 4
      (batchLaw n m B) := by
    have hz : MemLp (fun p => colZ μ D j p i) 4 (gaussBatch n m) := by
      have h := hv_colZ_memLp_four P μ D hP j (Pi.single i 1)
      simpa [single_dotProduct] using h
    exact hz.comp_measurePreserving
      (measurePreserving_eval (fun _ : Fin B => gaussBatch n m) r)
  have hcent (r : Fin B) (i : Fin n) :
      ∫ β, Zs r β i ∂(batchLaw n m B) = 0 := by
    rw [show batchLaw n m B = Measure.pi (fun _ : Fin B => gaussBatch n m) by rfl]
    exact (integral_comp_eval (μ := fun _ : Fin B => gaussBatch n m) (i := r)
      (f := fun p => colZ μ D j p i)
      (((measurable_pi_apply i).comp (hv_colZ_meas μ D j)).aestronglyMeasurable)).trans
        (hv_colZ_center P μ D hP j i)
  have hU (p : Fin B × Fin B) : MemLp (U p) 2 (batchLaw n m B) := by
    exact hv_colZ_bilinear_memLp P μ D hP j Pm p.1 p.2
  have hmean (b c : Fin B) (hbc : b ≠ c) :
      ∫ β, U (b, c) β ∂(batchLaw n m B) = 0 :=
    hv_colZ_bilinear_mean_zero P μ D hP j Pm b c hbc
  let Cd : ℝ := Muon.External.matOpNorm Pm ^ 2 * colA4 P * (n : ℝ) ^ 2
  let Co : ℝ := Muon.External.matOpNorm Pm ^ 2 * (n : ℝ) * colV0 P ^ 2
  have hV0 : 0 ≤ colV0 P := by
    have hL : 0 ≤ P.L := P.c_pos.le.trans P.c_le_L
    have hC : 0 ≤ P.Ccol := P.Ccol_pos.le
    unfold colV0 haarPplus haarH0
    positivity
  have hA4 : 0 ≤ colA4 P := by
    have hL : 0 ≤ P.L := P.c_pos.le.trans P.c_le_L
    unfold colA4 haarPplus
    positivity
  have hCd : 0 ≤ Cd := by
    simp only [Cd]
    exact mul_nonneg (mul_nonneg (sq_nonneg _) hA4) (sq_nonneg _)
  have hCo : 0 ≤ Co := by simp only [Co]; positivity
  have hdiag (b : Fin B) : cov[U (b, b), U (b, b); batchLaw n m B] ≤ Cd := by
    rw [covariance_self (hU (b, b)).aestronglyMeasurable.aemeasurable]
    exact (hv_variance_le_second _ _ (hU (b, b))).trans
      (hv_colZ_diagonal_second_bound P μ D hP j Pm b)
  have hoff (b c : Fin B) (hbc : b ≠ c) :
      cov[U (b, c), U (b, c); batchLaw n m B] ≤ Co := by
    rw [covariance_self (hU (b, c)).aestronglyMeasurable.aemeasurable]
    exact (hv_variance_le_second _ _ (hU (b, c))).trans
      (hv_colZ_bilinear_second_bound P μ D hP j Pm b c hbc)
  have hcov (p q : Fin B × Fin B) : cov[U p, U q; batchLaw n m B] ≤
      if p.1 = p.2 then (if q = p then Cd else 0)
      else (if q = p ∨ q = (p.2, p.1) then Co else 0) := by
    obtain ⟨pb, pc⟩ := p
    obtain ⟨qb, qc⟩ := q
    simp only [Prod.fst, Prod.snd]
    by_cases hp : pb = pc
    · subst pc
      simp only [↓reduceIte]
      by_cases hqp : (qb, qc) = (pb, pb)
      · injection hqp with hqb hqc
        subst qb
        subst qc
        simp only [Prod.fst, Prod.snd, ↓reduceIte]
        exact hdiag pb
      · simp only [hqp, ↓reduceIte]
        by_cases hq : qb = qc
        · subst qc
          have hne : pb ≠ qb := by
            intro heq
            apply hqp
            apply Prod.ext <;> simp [heq]
          have hi := (hind.indepFun hne).comp
            (φ := fun x => x ⬝ᵥ (Pm *ᵥ x))
            (ψ := fun x => x ⬝ᵥ (Pm *ᵥ x)) (by fun_prop) (by fun_prop)
          have hz := hi.covariance_eq_zero (hU (pb, pb)) (hU (qb, qb))
          change cov[((fun x => x ⬝ᵥ (Pm *ᵥ x)) ∘ Zs pb),
            ((fun x => x ⬝ᵥ (Pm *ᵥ x)) ∘ Zs qb); batchLaw n m B] ≤ 0
          exact hz.le
        · rw [covariance_eq_sub (hU (pb, pb)) (hU (qb, qc))]
          simp only [U, Pi.mul_apply]
          have hz := hv_diagonal_offdiag_integral_zero (batchLaw n m B) Zs hZm hind
            hcent h4 Pm pb qb qc hq
          rw [hz, hmean qb qc hq, mul_zero, sub_zero]
    · simp only [hp, ↓reduceIte]
      by_cases hqp : (qb, qc) = (pb, pc) ∨ (qb, qc) = (pc, pb)
      · simp only [hqp, ↓reduceIte]
        rcases hqp with heq | hswap
        · injection heq with hqb hqc
          subst qb
          subst qc
          exact hoff pb pc hp
        · have heq : U (qb, qc) = U (pb, pc) := by
            funext β
            simp only [U, hswap]
            exact hv_bilinear_swap Pm hPm _ _
          rw [heq]
          exact hoff pb pc hp
      · simp only [hqp, ↓reduceIte]
        by_cases hq : qb = qc
        · subst qc
          rw [covariance_comm, covariance_eq_sub (hU (qb, qb)) (hU (pb, pc))]
          simp only [U, Pi.mul_apply]
          have hz := hv_diagonal_offdiag_integral_zero (batchLaw n m B) Zs hZm hind
            hcent h4 Pm qb pb pc hp
          rw [hz, hmean pb pc hp, mul_zero, sub_zero]
        · rw [covariance_eq_sub (hU (pb, pc)) (hU (qb, qc))]
          simp only [U, Pi.mul_apply]
          have hpairs : ¬ ((pb = qb ∧ pc = qc) ∨ (pb = qc ∧ pc = qb)) := by
            intro hh
            apply hqp
            rcases hh with hh | hh
            · exact Or.inl (Prod.ext hh.1.symm hh.2.symm)
            · exact Or.inr (Prod.ext hh.2.symm hh.1.symm)
          have hz := hv_bilinear_cross_integral_zero (batchLaw n m B) Zs hZm hind
            hcent h4 Pm pb pc qb qc hp hq hpairs
          rw [hz, hmean pb pc hp, hmean qb qc hq, zero_mul, sub_zero]
  let Q : (Fin B → (Fin n → ℝ) × (Fin m → ℝ)) → ℝ := fun β => ∑ p, U p β
  have hvarQ : variance Q (batchLaw n m B) ≤ (B : ℝ) * Cd +
      2 * (B : ℝ) ^ 2 * Co := by
    rw [variance_fun_sum hU]
    calc
      ∑ p : Fin B × Fin B, ∑ q : Fin B × Fin B,
          cov[U p, U q; batchLaw n m B]
          ≤ ∑ p : Fin B × Fin B, ∑ q : Fin B × Fin B,
            (if p.1 = p.2 then (if q = p then Cd else 0)
            else (if q = p ∨ q = (p.2, p.1) then Co else 0)) := by
              gcongr with p q
              exact hcov p q
      _ ≤ ∑ p : Fin B × Fin B, (if p.1 = p.2 then Cd else 2 * Co) := by
        gcongr with p
        by_cases hp : p.1 = p.2
        · simp [hp]
        · simp only [hp, ↓reduceIte]
          have hswapne : (p.2, p.1) ≠ p := by
            intro heq
            have hfirst := congrArg Prod.fst heq
            simp only [Prod.fst] at hfirst
            exact hp hfirst.symm
          calc
            (∑ q : Fin B × Fin B,
                if q = p ∨ q = (p.2, p.1) then Co else 0)
                ≤ ∑ q : Fin B × Fin B,
                  ((if q = p then Co else 0) +
                    (if q = (p.2, p.1) then Co else 0)) := by
                      gcongr with q
                      by_cases h1 : q = p <;> by_cases h2 : q = (p.2, p.1) <;>
                        simp [h1, h2, hswapne, Ne.symm hswapne, hCo]
            _ = 2 * Co := by
              rw [Finset.sum_add_distrib]
              simp
              ring
      _ ≤ ∑ p : Fin B × Fin B,
          ((if p.1 = p.2 then Cd else 0) + 2 * Co) := by
        gcongr with p
        by_cases hp : p.1 = p.2 <;> simp [hp, hCo]
      _ = (B : ℝ) * Cd + 2 * (B : ℝ) ^ 2 * Co := by
        rw [Finset.sum_add_distrib]
        have hd : (∑ p : Fin B × Fin B, if p.1 = p.2 then Cd else 0) =
            (B : ℝ) * Cd := by
          rw [Fintype.sum_prod_type]
          simp
        rw [hd]
        simp [pow_two]
        ring
  have hre : (fun β =>
      ((1 / (B : ℝ)) • ∑ b, Zs b β) ⬝ᵥ
        (Pm *ᵥ ((1 / (B : ℝ)) • ∑ b, Zs b β))) =
      fun β => (1 / (B : ℝ) ^ 2) * Q β := by
    funext β
    simp only [Q, U, Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul,
      sum_dotProduct, Matrix.mulVec_sum, dotProduct_sum, Finset.sum_product]
    rw [Fintype.sum_prod_type, Finset.sum_comm]
    simp_rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hre, variance_const_mul]
  calc
    (1 / (B : ℝ) ^ 2) ^ 2 * variance Q (batchLaw n m B)
        ≤ (1 / (B : ℝ) ^ 2) ^ 2 *
          ((B : ℝ) * Cd + 2 * (B : ℝ) ^ 2 * Co) := by gcongr
    _ = Muon.External.matOpNorm Pm ^ 2 *
        (colA4 P * (n : ℝ) ^ 2 / (B : ℝ) ^ 3 +
          2 * (n : ℝ) * colV0 P ^ 2 / (B : ℝ) ^ 2) := by
      simp only [Cd, Co]
      field_simp

private lemma hv_centered_quadratic_memLp (P : HaarParams) {n m B : ℕ}
    (μ : Fin n → ℝ) (D : Matrix (Fin n) (Fin m) ℝ)
    (hP : def_app_sgd_state_law P n m B μ D) (j : Fin m)
    (Pm : Matrix (Fin n) (Fin n) ℝ) :
    MemLp (fun β =>
      ((1 / (B : ℝ)) • ∑ b, colZ μ D j (β b)) ⬝ᵥ
        (Pm *ᵥ ((1 / (B : ℝ)) • ∑ b, colZ μ D j (β b)))) 2
      (batchLaw n m B) := by
  letI : IsProbabilityMeasure (gaussBatch n m) := by unfold gaussBatch; infer_instance
  letI : IsProbabilityMeasure (batchLaw n m B) := by unfold batchLaw; infer_instance
  have hz (b : Fin B) (i : Fin n) :
      MemLp (fun β => colZ μ D j (β b) i) 4 (batchLaw n m B) := by
    have hi : MemLp (fun p => colZ μ D j p i) 4 (gaussBatch n m) := by
      have h := hv_colZ_memLp_four P μ D hP j (Pi.single i 1)
      simpa [single_dotProduct] using h
    exact hi.comp_measurePreserving
      (measurePreserving_eval (fun _ : Fin B => gaussBatch n m) b)
  have hw (i : Fin n) : MemLp
      (fun β => ((1 / (B : ℝ)) • ∑ b, colZ μ D j (β b)) i) 4
      (batchLaw n m B) := by
    simp only [Pi.smul_apply, Finset.sum_apply, smul_eq_mul]
    exact (memLp_finsetSum _ fun b _ => hz b i).const_mul _
  letI : ENNReal.HolderTriple 4 4 2 := ⟨by
    rw [show (4 : ENNReal) = 2 * 2 by norm_num, ENNReal.mul_inv (by norm_num) (by norm_num),
      ← add_mul, ENNReal.inv_two_add_inv_two, one_mul]⟩
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
  refine memLp_finsetSum _ fun i _ => memLp_finsetSum _ fun k _ => ?_
  have hp : MemLp (fun β =>
      ((1 / (B : ℝ)) • ∑ b, colZ μ D j (β b)) i *
        ((1 / (B : ℝ)) • ∑ b, colZ μ D j (β b)) k) 2
      (batchLaw n m B) := (hw i).fun_mul (hw k)
  convert hp.const_mul (Pm i k) using 1
  funext β
  ring

private lemma hv_linear_memLp (P : HaarParams) {n m B : ℕ}
    (μ : Fin n → ℝ) (D : Matrix (Fin n) (Fin m) ℝ)
    (hP : def_app_sgd_state_law P n m B μ D) (j : Fin m)
    (Pm : Matrix (Fin n) (Fin n) ℝ) :
    MemLp (fun β => 2 * (colMeanVec μ D j ⬝ᵥ
      (Pm *ᵥ ((1 / (B : ℝ)) • ∑ b, colZ μ D j (β b))))) 2
      (batchLaw n m B) := by
  letI : IsProbabilityMeasure (gaussBatch n m) := by unfold gaussBatch; infer_instance
  letI : IsProbabilityMeasure (batchLaw n m B) := by unfold batchLaw; infer_instance
  let a : Fin n → ℝ := Matrix.vecMul (colMeanVec μ D j) Pm
  have hb (b : Fin B) : MemLp
      (fun β : Fin B → (Fin n → ℝ) × (Fin m → ℝ) =>
        colMeanVec μ D j ⬝ᵥ (Pm *ᵥ colZ μ D j (β b))) 2
      (batchLaw n m B) := by
    have h := (hv_colZ_memLp_four P μ D hP j a).comp_measurePreserving
      (measurePreserving_eval (fun _ : Fin B => gaussBatch n m) b)
    have heq : (fun β : Fin B → (Fin n → ℝ) × (Fin m → ℝ) =>
        colMeanVec μ D j ⬝ᵥ (Pm *ᵥ colZ μ D j (β b))) =
        (fun β : Fin B → (Fin n → ℝ) × (Fin m → ℝ) =>
          a ⬝ᵥ colZ μ D j (β b)) := by
      funext β
      exact Matrix.dotProduct_mulVec _ _ _
    rw [heq]
    exact h.mono_exponent (by norm_num)
  have hsum : MemLp (fun β : Fin B → (Fin n → ℝ) × (Fin m → ℝ) => ∑ b,
      colMeanVec μ D j ⬝ᵥ (Pm *ᵥ colZ μ D j (β b))) 2
      (batchLaw n m B) := memLp_finsetSum _ fun b _ => hb b
  have heq : (fun β : Fin B → (Fin n → ℝ) × (Fin m → ℝ) =>
      2 * (colMeanVec μ D j ⬝ᵥ
      (Pm *ᵥ ((1 / (B : ℝ)) • ∑ b, colZ μ D j (β b))))) =
      fun β : Fin B → (Fin n → ℝ) × (Fin m → ℝ) => (2 / (B : ℝ)) * ∑ b,
        colMeanVec μ D j ⬝ᵥ (Pm *ᵥ colZ μ D j (β b)) := by
    funext β
    simp only [Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul, Finset.mul_sum]
    rw [Matrix.mulVec_sum, dotProduct_sum]
    simp_rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b _
    ring
  rw [heq]
  exact hsum.const_mul _

/-- **prop:app-sgd-quadratic**: for every symmetric `Π` and every column `j`,
`E|h_jᵀ Π h_j - (2ℛ/B) Tr(Π Λ)| ≤ ‖Π‖ (√(V_*/k) + D_*/k)`, with admissible `V_*, D_*`.

cr-2026-10-23. LaTeX statement (verbatim):
\begin{proposition}[Quadratic forms of a column]
There are admissible constants $V_*$ and $D_*$ such that, for every
symmetric $\Pi\in\R^{\Nout\times\Nout}$ and every column $j$,
\begin{equation}
\EE\Big|h_j^\T\Pi h_j-\frac{2\cR}B\Tr(\Pi\Lambda)\Big|\le\norm\Pi\Big(\sqrt{\frac{V_*}k}+\frac{D_*}k\Big).
\end{equation}
\end{proposition}
-/
theorem prop_app_sgd_quadratic (P : HaarParams) :
    ∃ Vs Ds : ℝ, 0 ≤ Vs ∧ 0 ≤ Ds ∧
      ∀ (n m B : ℕ) (μ : Fin n → ℝ) (D : Matrix (Fin n) (Fin m) ℝ),
        def_app_sgd_state_law P n m B μ D →
        ∀ Pm : Matrix (Fin n) (Fin n) ℝ, Pmᵀ = Pm → ∀ j : Fin m,
          ∫⁻ β, ENNReal.ofReal
              |hCol μ D β j ⬝ᵥ (Pm *ᵥ hCol μ D β j)
                - twoR μ D / (B : ℝ) * (Pm * Matrix.diagonal μ).trace|
            ∂(batchLaw n m B)
            ≤ ENNReal.ofReal (Muon.External.matOpNorm Pm *
                (Real.sqrt (Vs / (kOf n m B : ℝ)) + Ds / (kOf n m B : ℝ))) := by
  refine ⟨quadVstar P, quadDstar P, (hv_quad_constants_nonneg P).1,
    (hv_quad_constants_nonneg P).2, ?_⟩
  intro n m B μ D hP Pm hPm j
  letI : IsProbabilityMeasure (gaussBatch n m) := by unfold gaussBatch; infer_instance
  letI : IsProbabilityMeasure (batchLaw n m B) := by unfold batchLaw; infer_instance
  apply hv_quadratic_bound_of_variance P μ D hP j Pm
  let W : (Fin B → (Fin n → ℝ) × (Fin m → ℝ)) → (Fin n → ℝ) :=
    fun β => (1 / (B : ℝ)) • ∑ b, colZ μ D j (β b)
  let Lf : (Fin B → (Fin n → ℝ) × (Fin m → ℝ)) → ℝ :=
    fun β => 2 * (colMeanVec μ D j ⬝ᵥ (Pm *ᵥ W β))
  let Qf : (Fin B → (Fin n → ℝ) × (Fin m → ℝ)) → ℝ :=
    fun β => W β ⬝ᵥ (Pm *ᵥ W β)
  let c0 : ℝ := colMeanVec μ D j ⬝ᵥ (Pm *ᵥ colMeanVec μ D j)
  have hB : 0 < B := hP.1.2.2
  have hexpand : (fun β => hCol μ D β j ⬝ᵥ (Pm *ᵥ hCol μ D β j)) =
      fun β => c0 + (Lf β + Qf β) := by
    funext β
    rw [hv_hcol_decomp μ D j hB]
    have hs := hv_bilinear_swap Pm hPm (colMeanVec μ D j) (W β)
    simp only [W, Lf, Qf, c0, Matrix.mulVec_add, add_dotProduct, dotProduct_add]
    rw [hs]
    ring
  have hLm : MemLp Lf 2 (batchLaw n m B) :=
    hv_linear_memLp P μ D hP j Pm
  have hQm : MemLp Qf 2 (batchLaw n m B) :=
    hv_centered_quadratic_memLp P μ D hP j Pm
  have hlin := hv_linear_variance_bound P μ D hP j Pm hPm
  have hquad := hv_centered_quadratic_variance_bound P μ D hP j Pm hPm
  have hraw : variance (fun β => hCol μ D β j ⬝ᵥ (Pm *ᵥ hCol μ D β j))
      (batchLaw n m B) ≤ Muon.External.matOpNorm Pm ^ 2 *
        (2 * colA4 P * (n : ℝ) ^ 2 / (B : ℝ) ^ 3 +
          4 * (n : ℝ) * colV0 P ^ 2 / (B : ℝ) ^ 2 +
          8 * colV0 P * P.L ^ 2 * P.Ccol /
            ((kOf n m B : ℝ) * (B : ℝ))) := by
    rw [hexpand]
    have hc : (fun β => c0 + (Lf β + Qf β)) =
        fun β => (Lf + Qf) β + c0 := by
      funext β
      simp only [Pi.add_apply]
      ring
    rw [hc, variance_add_const (hLm.add hQm).aestronglyMeasurable]
    calc
      variance (Lf + Qf) (batchLaw n m B)
          ≤ 2 * variance Lf (batchLaw n m B) +
            2 * variance Qf (batchLaw n m B) :=
        hv_variance_add_le _ _ _ hLm hQm
      _ ≤ 2 * (4 * Muon.External.matOpNorm Pm ^ 2 * colV0 P *
            (P.L ^ 2 * P.Ccol / (kOf n m B : ℝ)) / (B : ℝ)) +
          2 * (Muon.External.matOpNorm Pm ^ 2 *
            (colA4 P * (n : ℝ) ^ 2 / (B : ℝ) ^ 3 +
              2 * (n : ℝ) * colV0 P ^ 2 / (B : ℝ) ^ 2)) := by
        exact add_le_add (mul_le_mul_of_nonneg_left hlin (by norm_num))
          (mul_le_mul_of_nonneg_left hquad (by norm_num))
      _ = _ := by ring
  have hk2 : (2 : ℝ) ≤ (kOf n m B : ℝ) := by exact_mod_cast hP.2.1
  have hk : (0 : ℝ) < (kOf n m B : ℝ) := by linarith
  have hBreal : (0 : ℝ) < B := by exact_mod_cast hB
  have hkB : (kOf n m B : ℝ) ≤ (B : ℝ) := by
    exact_mod_cast (le_trans (min_le_right _ _) (min_le_right _ _) : kOf n m B ≤ B)
  have hnK : (n : ℝ) ≤ P.K * (kOf n m B : ℝ) := hP.2.2.1
  have hK : 0 ≤ P.K := le_trans (by norm_num) P.one_le_K
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  have hA4 : 0 ≤ colA4 P := by
    have hL : 0 ≤ P.L := P.c_pos.le.trans P.c_le_L
    unfold colA4 haarPplus
    positivity
  have hV0 : 0 ≤ colV0 P := by
    have hL : 0 ≤ P.L := P.c_pos.le.trans P.c_le_L
    have hC : 0 ≤ P.Ccol := P.Ccol_pos.le
    unfold colV0 haarPplus haarH0
    positivity
  have hL : 0 ≤ P.L := P.c_pos.le.trans P.c_le_L
  have hC : 0 ≤ P.Ccol := P.Ccol_pos.le
  have hn2 : (n : ℝ) ^ 2 ≤ P.K ^ 2 * (kOf n m B : ℝ) ^ 2 := by
    nlinarith [sq_nonneg (P.K * (kOf n m B : ℝ) - (n : ℝ))]
  have hkB2 : (kOf n m B : ℝ) ^ 2 ≤ (B : ℝ) ^ 2 :=
    pow_le_pow_left₀ hk.le hkB 2
  have hkB3 : (kOf n m B : ℝ) ^ 3 ≤ (B : ℝ) ^ 3 :=
    pow_le_pow_left₀ hk.le hkB 3
  have hterm1 : 2 * colA4 P * (n : ℝ) ^ 2 / (B : ℝ) ^ 3 ≤
      2 * colA4 P * P.K ^ 2 / (kOf n m B : ℝ) := by
    calc
      _ ≤ (2 * colA4 P * (P.K ^ 2 * (kOf n m B : ℝ) ^ 2)) /
          (B : ℝ) ^ 3 := div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_left hn2 (mul_nonneg (by norm_num) hA4))
            (by positivity)
      _ ≤ (2 * colA4 P * (P.K ^ 2 * (kOf n m B : ℝ) ^ 2)) /
          (kOf n m B : ℝ) ^ 3 := div_le_div_of_nonneg_left
            (by positivity) (by positivity) hkB3
      _ = _ := by field_simp
  have hterm2 : 4 * (n : ℝ) * colV0 P ^ 2 / (B : ℝ) ^ 2 ≤
      4 * P.K * colV0 P ^ 2 / (kOf n m B : ℝ) := by
    calc
      _ ≤ (4 * (P.K * (kOf n m B : ℝ)) * colV0 P ^ 2) /
          (B : ℝ) ^ 2 := div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hnK (by norm_num)) (sq_nonneg _))
            (by positivity)
      _ ≤ (4 * (P.K * (kOf n m B : ℝ)) * colV0 P ^ 2) /
          (kOf n m B : ℝ) ^ 2 := div_le_div_of_nonneg_left
            (by positivity) (by positivity) hkB2
      _ = _ := by field_simp
  have hterm3 : 8 * colV0 P * P.L ^ 2 * P.Ccol /
      ((kOf n m B : ℝ) * (B : ℝ)) ≤
      8 * colV0 P * P.L ^ 2 * P.Ccol / (kOf n m B : ℝ) := by
    have hnum : 0 ≤ 8 * colV0 P * P.L ^ 2 * P.Ccol := by positivity
    have hden : (kOf n m B : ℝ) ≤ (kOf n m B : ℝ) * (B : ℝ) := by
      have hB1 : (1 : ℝ) ≤ B := by exact_mod_cast hB
      nlinarith
    exact div_le_div_of_nonneg_left hnum hk hden
  calc
    _ ≤ Muon.External.matOpNorm Pm ^ 2 *
        (2 * colA4 P * (n : ℝ) ^ 2 / (B : ℝ) ^ 3 +
          4 * (n : ℝ) * colV0 P ^ 2 / (B : ℝ) ^ 2 +
          8 * colV0 P * P.L ^ 2 * P.Ccol /
            ((kOf n m B : ℝ) * (B : ℝ))) := hraw
    _ ≤ Muon.External.matOpNorm Pm ^ 2 *
        ((2 * colA4 P * P.K ^ 2 + 4 * P.K * colV0 P ^ 2 +
          8 * colV0 P * P.L ^ 2 * P.Ccol) / (kOf n m B : ℝ)) := by
      gcongr
      have hsplit :
          (2 * colA4 P * P.K ^ 2 + 4 * P.K * colV0 P ^ 2 +
            8 * colV0 P * P.L ^ 2 * P.Ccol) / (kOf n m B : ℝ) =
          2 * colA4 P * P.K ^ 2 / (kOf n m B : ℝ) +
            4 * P.K * colV0 P ^ 2 / (kOf n m B : ℝ) +
            8 * colV0 P * P.L ^ 2 * P.Ccol / (kOf n m B : ℝ) := by ring
      rw [hsplit]
      exact add_le_add (add_le_add hterm1 hterm2) hterm3
    _ = Muon.External.matOpNorm Pm ^ 2 *
        (quadVstar P / (kOf n m B : ℝ)) := by
      unfold quadVstar
      ring

/-! ## Haar reduction (`lem:app-sgd-reduction`) -/

private lemma diagonal_rayleigh_bounds {n : ℕ} (c L : ℝ) (μ v : Fin n → ℝ)
    (hμ : ∀ i, c ≤ μ i ∧ μ i ≤ L) (hv : v ≠ 0) :
    c ≤ (v ⬝ᵥ (Matrix.diagonal μ *ᵥ v)) / (v ⬝ᵥ v) ∧
      (v ⬝ᵥ (Matrix.diagonal μ *ᵥ v)) / (v ⬝ᵥ v) ≤ L := by
  have hden : 0 < v ⬝ᵥ v := by
    simpa using (Matrix.dotProduct_self_star_pos_iff.mpr hv)
  have hlo : c * (v ⬝ᵥ v) ≤ v ⬝ᵥ (Matrix.diagonal μ *ᵥ v) := by
    simp only [dotProduct, Matrix.mulVec_diagonal, Finset.mul_sum]
    exact Finset.sum_le_sum fun i _ => by
      have hi := (hμ i).1
      nlinarith [sq_nonneg (v i)]
  have hup : v ⬝ᵥ (Matrix.diagonal μ *ᵥ v) ≤ L * (v ⬝ᵥ v) := by
    simp only [dotProduct, Matrix.mulVec_diagonal, Finset.mul_sum]
    exact Finset.sum_le_sum fun i _ => by
      have hi := (hμ i).2
      nlinarith [sq_nonneg (v i)]
  exact ⟨(le_div_iff₀ hden).2 hlo, (div_le_iff₀ hden).2 hup⟩

private lemma euclidNorm_pos_of_ne_zero (n : ℕ) (v : Fin n → ℝ) (hv : v ≠ 0) :
    0 < Muon.Foundations.euclidNorm n v := by
  unfold Muon.Foundations.euclidNorm
  refine Real.sqrt_pos.2 ?_
  by_contra h
  apply hv
  have hsum : ∑ i, v i ^ 2 = 0 :=
    le_antisymm (not_lt.1 h) (Finset.sum_nonneg fun i _ => sq_nonneg _)
  funext i
  have hi := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg (v i))).1 hsum i
    (Finset.mem_univ i)
  exact (pow_eq_zero_iff two_ne_zero).1 hi

private lemma normalize_euclidNorm (n : ℕ) (v : Fin n → ℝ) (hv : v ≠ 0) :
    Muon.Foundations.euclidNorm n
        ((Muon.Foundations.euclidNorm n v)⁻¹ • v) = 1 := by
  have hpos := euclidNorm_pos_of_ne_zero n v hv
  have hsq (z : Fin n → ℝ) : Muon.Foundations.euclidNorm n z ^ 2 = ∑ i, z i ^ 2 :=
    Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)
  have hnormalized :
      Muon.Foundations.euclidNorm n
          ((Muon.Foundations.euclidNorm n v)⁻¹ • v) ^ 2 = 1 := by
    rw [hsq]
    simp only [Pi.smul_apply, smul_eq_mul, mul_pow, ← Finset.mul_sum, ← hsq v, inv_pow]
    exact inv_mul_cancel₀ (pow_ne_zero 2 hpos.ne')
  exact (pow_eq_one_iff_of_nonneg (Real.sqrt_nonneg _) two_ne_zero).1 hnormalized

private lemma orthHaar_mulVec_coord_ne_zero_of_ne_zero {n : ℕ}
    {ν : Measure (Matrix.orthogonalGroup (Fin n) ℝ)}
    (hν : Muon.Foundations.IsOrthHaar ν) (v : Fin n → ℝ) (hv : v ≠ 0) :
    ∀ᵐ U : Matrix.orthogonalGroup (Fin n) ℝ ∂ν,
      ∀ i, ((U : Matrix (Fin n) (Fin n) ℝ) *ᵥ v) i ≠ 0 := by
  have h := Muon.Foundations.orthHaar_mulVec_coord_ne_zero n hν
    ((Muon.Foundations.euclidNorm n v)⁻¹ • v) (normalize_euclidNorm n v hv)
  filter_upwards [h] with U hU
  intro i hi
  exact hU i (by simp [Matrix.mulVec_smul, hi])

private lemma hCol_measurable {n m B : ℕ} (μ : Fin n → ℝ)
    (D : Matrix (Fin n) (Fin m) ℝ) (j : Fin m) :
    Measurable (fun β : Fin B → (Fin n → ℝ) × (Fin m → ℝ) => hCol μ D β j) := by
  refine measurable_pi_iff.mpr fun i => ?_
  unfold hCol colSample resA lamHalf
  fun_prop

/-- **lem:app-sgd-reduction**, part (i): `c ≤ R_j ≤ L` almost surely, for every column `j`.

cr-2026-10-23. LaTeX statement (verbatim):
\begin{lemma}[Haar reduction]
In the Haar model, put $R_j\defeq h_j^\T\Lambda h_j/\norm{h_j}^2$. Then
$c\le R_j\le L$ almost surely, every entry of $G^\circ$ is nonzero almost
surely, $\norm S_\F^2=\Nout\Nin$, and
\begin{equation}
\mathcal Q=\Nin\Big(1-\frac2\pi\Big)\Tr\Lambda+\frac2\pi\,\Nout\sum_{j=1}^{\Nin}\EE R_j,\qquad
\EE\norm{S^\T u_i}^2=\Nin\Big(1-\frac2\pi\Big)+\frac2\pi\,\Nout\sum_{j=1}^{\Nin}\EE\frac{(h_j)_i^2}{\norm{h_j}^2}.
\end{equation}
\end{lemma}
-/
theorem lem_app_sgd_reduction_i (P : HaarParams) {n m B : ℕ} (μ : Fin n → ℝ)
    (D : Matrix (Fin n) (Fin m) ℝ) (hP : def_app_sgd_state_law P n m B μ D) (j : Fin m) :
    ∀ᵐ β ∂(batchLaw n m B), P.c ≤ redR μ D β j ∧ redR μ D β j ≤ P.L := by
  filter_upwards [lem_app_sgd_column_iv P μ D hP j] with β hβ
  exact diagonal_rayleigh_bounds P.c P.L μ (hCol μ D β j) hP.2.2.2.2.2.1 hβ

/-- **lem:app-sgd-reduction**, part (ii): every entry of `G° = physGrad (U D) (U Λ^{1/2} z)` is
nonzero almost surely, in the Haar model.

cr-2026-10-23. LaTeX statement (verbatim):
\begin{lemma}[Haar reduction]
In the Haar model, put $R_j\defeq h_j^\T\Lambda h_j/\norm{h_j}^2$. Then
$c\le R_j\le L$ almost surely, every entry of $G^\circ$ is nonzero almost
surely, $\norm S_\F^2=\Nout\Nin$, and
\begin{equation}
\mathcal Q=\Nin\Big(1-\frac2\pi\Big)\Tr\Lambda+\frac2\pi\,\Nout\sum_{j=1}^{\Nin}\EE R_j,\qquad
\EE\norm{S^\T u_i}^2=\Nin\Big(1-\frac2\pi\Big)+\frac2\pi\,\Nout\sum_{j=1}^{\Nin}\EE\frac{(h_j)_i^2}{\norm{h_j}^2}.
\end{equation}
\end{lemma}
-/
theorem lem_app_sgd_reduction_ii (P : HaarParams) {n m B : ℕ} (μ : Fin n → ℝ)
    (D : Matrix (Fin n) (Fin m) ℝ) (ν : Measure (Matrix.orthogonalGroup (Fin n) ℝ))
    (hν : Muon.Foundations.IsOrthHaar ν) (hP : def_app_sgd_state_law P n m B μ D) :
    ∀ᵐ p ∂(ν.prod (batchLaw n m B)),
      ∀ i j, physGrad (haarDelta p.1 D) (haarBatch μ p.1 p.2) i j ≠ 0 := by
  letI : IsProbabilityMeasure ν := hν.1
  letI : IsProbabilityMeasure (gaussBatch n m) := by unfold gaussBatch; infer_instance
  letI : IsProbabilityMeasure (batchLaw n m B) := by unfold batchLaw; infer_instance
  have hmset : MeasurableSet {p : Matrix.orthogonalGroup (Fin n) ℝ ×
      (Fin B → (Fin n → ℝ) × (Fin m → ℝ)) |
      ∀ i j, physGrad (haarDelta p.1 D) (haarBatch μ p.1 p.2) i j ≠ 0} := by
    rw [show {p : Matrix.orthogonalGroup (Fin n) ℝ ×
        (Fin B → (Fin n → ℝ) × (Fin m → ℝ)) |
        ∀ i j, physGrad (haarDelta p.1 D) (haarBatch μ p.1 p.2) i j ≠ 0} =
        ⋂ i, ⋂ j, {p | physGrad (haarDelta p.1 D) (haarBatch μ p.1 p.2) i j ≠ 0} by
      ext p
      simp]
    apply MeasurableSet.iInter
    intro i
    apply MeasurableSet.iInter
    intro j
    have hf : Measurable (fun p : Matrix.orthogonalGroup (Fin n) ℝ ×
        (Fin B → (Fin n → ℝ) × (Fin m → ℝ)) =>
        (((p.1 : Matrix (Fin n) (Fin n) ℝ) * hMatrix μ D p.2) i j)) := by
      simp only [Matrix.mul_apply, hMatrix, Matrix.of_apply]
      exact Finset.measurable_sum _ fun k _ =>
        ((measurable_pi_apply k).comp ((measurable_pi_apply i).comp
          (measurable_subtype_coe.comp measurable_fst))).mul
        ((measurable_pi_apply k).comp ((hCol_measurable μ D j).comp measurable_snd))
    have hs : {p : Matrix.orthogonalGroup (Fin n) ℝ ×
        (Fin B → (Fin n → ℝ) × (Fin m → ℝ)) |
        physGrad (haarDelta p.1 D) (haarBatch μ p.1 p.2) i j ≠ 0} =
        {p | ((p.1 : Matrix (Fin n) (Fin n) ℝ) * hMatrix μ D p.2) i j ≠ 0} := by
      ext p
      simp only [Set.mem_setOf_eq]
      have he := congrArg (fun M : Matrix (Fin n) (Fin m) ℝ => M i j)
        (gPhys_eq_mul_hMatrix μ D p.1 p.2)
      constructor
      · intro hn hz
        exact hn (he.trans hz)
      · intro hn hz
        exact hn (he.symm.trans hz)
    rw [hs]
    exact (measurableSet_singleton 0).compl.preimage hf
  rw [Measure.ae_prod_iff_ae_ae hmset, Measure.ae_ae_comm hmset]
  filter_upwards [ae_all_iff.2 fun j => lem_app_sgd_column_iv P μ D hP j] with β hβ
  have hU : ∀ᵐ U : Matrix.orthogonalGroup (Fin n) ℝ ∂ν,
      ∀ j i, ((U : Matrix (Fin n) (Fin n) ℝ) *ᵥ hCol μ D β j) i ≠ 0 :=
    ae_all_iff.2 fun j => orthHaar_mulVec_coord_ne_zero_of_ne_zero hν (hCol μ D β j) (hβ j)
  filter_upwards [hU] with U hU'
  intro i j
  rw [gPhys_eq_mul_hMatrix]
  simpa only [Matrix.mul_apply, Matrix.mulVec, dotProduct, hMatrix, Matrix.of_apply] using hU' j i

private lemma hv_haarSign_entry {n m B : ℕ} (μ : Fin n → ℝ)
    (D : Matrix (Fin n) (Fin m) ℝ) (U : Matrix.orthogonalGroup (Fin n) ℝ)
    (β : Fin B → (Fin n → ℝ) × (Fin m → ℝ)) (i : Fin n) (j : Fin m) :
    haarSign μ D U β i j =
      Real.sign (((U : Matrix (Fin n) (Fin n) ℝ) *ᵥ hCol μ D β j) i) := by
  unfold haarSign
  rw [gPhys_eq_mul_hMatrix]
  simp only [Matrix.map_apply, Matrix.mul_apply, Matrix.mulVec, dotProduct, hMatrix,
    Matrix.of_apply]

private lemma hv_haarSignY_entry {n m B : ℕ} (μ : Fin n → ℝ)
    (D : Matrix (Fin n) (Fin m) ℝ) (U : Matrix.orthogonalGroup (Fin n) ℝ)
    (β : Fin B → (Fin n → ℝ) × (Fin m → ℝ)) (i : Fin n) (j : Fin m) :
    ∑ k, (U : Matrix (Fin n) (Fin n) ℝ) k i * haarSign μ D U β k j =
      haarSignY (hCol μ D β j) U i := by
  unfold haarSignY
  simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply]
  apply Finset.sum_congr rfl
  intro k _
  rw [hv_haarSign_entry]
  rfl

private lemma hv_risk_eq_weighted_sign {n m B : ℕ} (μ : Fin n → ℝ)
    (D : Matrix (Fin n) (Fin m) ℝ) (U : Matrix.orthogonalGroup (Fin n) ℝ)
    (β : Fin B → (Fin n → ℝ) × (Fin m → ℝ)) :
    riskTwo (haarSigmaOut U μ) (haarSign μ D U β) =
      ∑ i, μ i * ∑ j, (∑ k, haarSign μ D U β k j *
        (U : Matrix (Fin n) (Fin n) ℝ) k i) ^ 2 := by
  unfold riskTwo pairIdIn haarSigmaOut
  rw [show (U : Matrix (Fin n) (Fin n) ℝ) * Matrix.diagonal μ *
      (U : Matrix (Fin n) (Fin n) ℝ)ᵀ * haarSign μ D U β *
          (haarSign μ D U β)ᵀ =
      (U : Matrix (Fin n) (Fin n) ℝ) *
        (Matrix.diagonal μ * (U : Matrix (Fin n) (Fin n) ℝ)ᵀ *
          haarSign μ D U β * (haarSign μ D U β)ᵀ) by
        simp only [Matrix.mul_assoc]]
  rw [Matrix.trace_mul_comm (U : Matrix (Fin n) (Fin n) ℝ)]
  simp only [Matrix.mul_assoc, Matrix.trace, Matrix.diag, Matrix.mul_apply,
    Matrix.transpose_apply]
  simp [Matrix.diagonal_apply]
  apply Finset.sum_congr rfl
  intro i _
  simp only [mul_assoc]
  rw [← Finset.mul_sum]
  congr 1
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  simp_rw [Finset.sum_mul]
  let f : Fin n → Fin n → Fin m → ℝ := fun y x j =>
    (U : Matrix (Fin n) (Fin n) ℝ) y i *
      (haarSign μ D U β y j * haarSign μ D U β x j) *
      (U : Matrix (Fin n) (Fin n) ℝ) x i
  change (∑ x, ∑ y, ∑ j, f y x j) = _
  calc
    _ = ∑ x, ∑ j, ∑ y, f y x j := by
      apply Finset.sum_congr rfl
      intro x _
      rw [Finset.sum_comm]
    _ = ∑ j, ∑ x, ∑ y, f y x j := by rw [Finset.sum_comm]
    _ = ∑ j, ∑ y, ∑ x, f y x j := by
      apply Finset.sum_congr rfl
      intro j _
      rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j _
      rw [pow_two, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro y _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      dsimp only [f]
      ring

private lemma hv_risk_eq_haarSignY {n m B : ℕ} (μ : Fin n → ℝ)
    (D : Matrix (Fin n) (Fin m) ℝ) (U : Matrix.orthogonalGroup (Fin n) ℝ)
    (β : Fin B → (Fin n → ℝ) × (Fin m → ℝ)) :
    riskTwo (haarSigmaOut U μ) (haarSign μ D U β) =
      ∑ j, ∑ i, μ i * haarSignY (hCol μ D β j) U i ^ 2 := by
  rw [hv_risk_eq_weighted_sign]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  rw [← hv_haarSignY_entry μ D U β i j]
  congr 2
  apply Finset.sum_congr rfl
  intro k _
  ring

private lemma hv_sign_measurable : Measurable Real.sign := by
  unfold Real.sign
  exact measurable_const.ite (measurableSet_lt measurable_id measurable_const)
    (measurable_const.ite (measurableSet_lt measurable_const measurable_id) measurable_const)

private lemma hv_haarSignY_measurable {n m B : ℕ} (μ : Fin n → ℝ)
    (D : Matrix (Fin n) (Fin m) ℝ) (j : Fin m) (i : Fin n) :
    Measurable (fun p : Matrix.orthogonalGroup (Fin n) ℝ ×
      (Fin B → (Fin n → ℝ) × (Fin m → ℝ)) => haarSignY (hCol μ D p.2 j) p.1 i) := by
  unfold haarSignY
  change Measurable (fun p : Matrix.orthogonalGroup (Fin n) ℝ ×
      (Fin B → (Fin n → ℝ) × (Fin m → ℝ)) =>
    ∑ k, (p.1 : Matrix (Fin n) (Fin n) ℝ) k i *
    Real.sign (∑ l, (p.1 : Matrix (Fin n) (Fin n) ℝ) k l * hCol μ D p.2 j l))
  apply Finset.measurable_sum
  intro k _
  have hU (r s : Fin n) : Measurable (fun p : Matrix.orthogonalGroup (Fin n) ℝ ×
      (Fin B → (Fin n → ℝ) × (Fin m → ℝ)) =>
      (p.1 : Matrix (Fin n) (Fin n) ℝ) r s) :=
    (measurable_pi_apply s).comp ((measurable_pi_apply r).comp
      (measurable_subtype_coe.comp measurable_fst))
  have hh (l : Fin n) : Measurable (fun p : Matrix.orthogonalGroup (Fin n) ℝ ×
      (Fin B → (Fin n → ℝ) × (Fin m → ℝ)) => hCol μ D p.2 j l) :=
    (measurable_pi_apply l).comp ((hCol_measurable μ D j).comp measurable_snd)
  exact (hU k i).mul (hv_sign_measurable.comp
    (Finset.measurable_sum _ fun l _ => (hU k l).mul (hh l)))

private lemma hv_orth_entry_abs_le_one {n : ℕ}
    (U : Matrix.orthogonalGroup (Fin n) ℝ) (k i : Fin n) :
    |(U : Matrix (Fin n) (Fin n) ℝ) k i| ≤ 1 := by
  have hU : (U : Matrix (Fin n) (Fin n) ℝ).transpose *
      (U : Matrix (Fin n) (Fin n) ℝ) = 1 :=
    (Matrix.mem_orthogonalGroup_iff' (Fin n) ℝ).1 U.2
  have hdiag := congrFun (congrFun hU i) i
  have hsum : ∑ l, (U : Matrix (Fin n) (Fin n) ℝ) l i ^ 2 = 1 := by
    simpa [Matrix.mul_apply, Matrix.transpose_apply, sq] using hdiag
  have hle := Finset.single_le_sum (f := fun l =>
    (U : Matrix (Fin n) (Fin n) ℝ) l i ^ 2) (fun l _ => sq_nonneg _)
      (Finset.mem_univ k)
  rw [hsum] at hle
  nlinarith [sq_abs ((U : Matrix (Fin n) (Fin n) ℝ) k i),
    abs_nonneg ((U : Matrix (Fin n) (Fin n) ℝ) k i)]

private lemma hv_haarSignY_abs_le {n : ℕ} (a : Fin n → ℝ)
    (U : Matrix.orthogonalGroup (Fin n) ℝ) (i : Fin n) :
    |haarSignY a U i| ≤ n := by
  have hs : ∀ x : ℝ, |Real.sign x| ≤ 1 := by
    intro x
    rcases Real.sign_apply_eq x with h | h | h <;> simp [h]
  unfold haarSignY Matrix.mulVec dotProduct
  calc
    |∑ k, (U : Matrix (Fin n) (Fin n) ℝ).transpose i k *
        Real.sign (Matrix.mulVec (U : Matrix (Fin n) (Fin n) ℝ) a k)|
        ≤ ∑ k, |(U : Matrix (Fin n) (Fin n) ℝ).transpose i k *
          Real.sign (Matrix.mulVec (U : Matrix (Fin n) (Fin n) ℝ) a k)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k : Fin n, (1 : ℝ) := Finset.sum_le_sum fun k _ => by
      rw [abs_mul, Matrix.transpose_apply]
      exact (mul_le_mul (hv_orth_entry_abs_le_one U k i) (hs _) (abs_nonneg _)
        zero_le_one).trans_eq (one_mul 1)
    _ = n := by simp

private lemma hv_risk_integrable {n m B : ℕ} (μ : Fin n → ℝ)
    (D : Matrix (Fin n) (Fin m) ℝ) (ν : Measure (Matrix.orthogonalGroup (Fin n) ℝ))
    [IsFiniteMeasure ν] [IsFiniteMeasure (batchLaw n m B)] :
    Integrable (fun p => riskTwo (haarSigmaOut p.1 μ) (haarSign μ D p.1 p.2))
      (ν.prod (batchLaw n m B)) := by
  have hterm (j : Fin m) (i : Fin n) : Integrable (fun p =>
      μ i * haarSignY (hCol μ D p.2 j) p.1 i ^ 2) (ν.prod (batchLaw n m B)) := by
    have hm : Measurable (fun p : Matrix.orthogonalGroup (Fin n) ℝ ×
        (Fin B → (Fin n → ℝ) × (Fin m → ℝ)) =>
        μ i * haarSignY (hCol μ D p.2 j) p.1 i ^ 2) :=
      measurable_const.mul ((hv_haarSignY_measurable μ D j i).pow_const 2)
    refine Integrable.mono' (integrable_const (|μ i| * (n : ℝ) ^ 2))
      hm.aestronglyMeasurable ?_
    filter_upwards [] with p
    rw [Real.norm_eq_abs, abs_mul, abs_pow]
    have h := hv_haarSignY_abs_le (hCol μ D p.2 j) p.1 i
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg _) h 2) (abs_nonneg _)
  have hsum : Integrable (fun p => ∑ j : Fin m, ∑ i : Fin n,
      μ i * haarSignY (hCol μ D p.2 j) p.1 i ^ 2) (ν.prod (batchLaw n m B)) := by
    apply integrable_finset_sum
    intro j _
    apply integrable_finset_sum
    intro i _
    exact hterm j i
  refine hsum.congr ?_
  filter_upwards [] with p
  exact (hv_risk_eq_haarSignY μ D p.1 p.2).symm

private lemma hv_euclidNorm_sq (n : ℕ) (v : Fin n → ℝ) :
    Muon.Foundations.euclidNorm n v ^ 2 = v ⬝ᵥ v := by
  unfold Muon.Foundations.euclidNorm dotProduct
  rw [Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg (v i))]
  exact Finset.sum_congr rfl fun i _ => by ring

private lemma hv_redR_integrable (P : HaarParams) {n m B : ℕ} (μ : Fin n → ℝ)
    (D : Matrix (Fin n) (Fin m) ℝ) (hP : def_app_sgd_state_law P n m B μ D)
    (j : Fin m) : Integrable (fun β => redR μ D β j) (batchLaw n m B) := by
  letI : IsProbabilityMeasure (gaussBatch n m) := by unfold gaussBatch; infer_instance
  letI : IsProbabilityMeasure (batchLaw n m B) := by unfold batchLaw; infer_instance
  refine Integrable.mono' (integrable_const P.L) ?_ ?_
  · have hh := hCol_measurable (B := B) μ D j
    have hnum : Measurable (fun β : Fin B → (Fin n → ℝ) × (Fin m → ℝ) =>
        hCol μ D β j ⬝ᵥ (Matrix.diagonal μ *ᵥ hCol μ D β j)) := by
      simp only [dotProduct, Matrix.mulVec_diagonal]
      exact Finset.measurable_sum _ fun i _ =>
        ((measurable_pi_apply i).comp hh).mul
          (measurable_const.mul ((measurable_pi_apply i).comp hh))
    have hden : Measurable (fun β : Fin B → (Fin n → ℝ) × (Fin m → ℝ) =>
        hCol μ D β j ⬝ᵥ hCol μ D β j) := by
      simp only [dotProduct]
      exact Finset.measurable_sum _ fun i _ =>
        ((measurable_pi_apply i).comp hh).mul ((measurable_pi_apply i).comp hh)
    change AEStronglyMeasurable (fun β : Fin B → (Fin n → ℝ) × (Fin m → ℝ) =>
      (hCol μ D β j ⬝ᵥ (Matrix.diagonal μ *ᵥ hCol μ D β j)) /
        (hCol μ D β j ⬝ᵥ hCol μ D β j)) (batchLaw n m B)
    exact (hnum.div hden).aestronglyMeasurable
  · filter_upwards [lem_app_sgd_reduction_i P μ D hP j] with β hβ
    rw [Real.norm_eq_abs, abs_of_nonneg (P.c_pos.le.trans hβ.1)]
    exact hβ.2

private lemma hv_risk_haar_average (P : HaarParams) {n m B : ℕ} (μ : Fin n → ℝ)
    (D : Matrix (Fin n) (Fin m) ℝ) (ν : Measure (Matrix.orthogonalGroup (Fin n) ℝ))
    (hν : Muon.Foundations.IsOrthHaar ν) (hP : def_app_sgd_state_law P n m B μ D)
    (β : Fin B → (Fin n → ℝ) × (Fin m → ℝ)) (hβ : ∀ j, hCol μ D β j ≠ 0) :
    ∫ U, riskTwo (haarSigmaOut U μ) (haarSign μ D U β) ∂ν =
      (m : ℝ) * (1 - 2 / Real.pi) * (∑ i, μ i) +
        2 / Real.pi * (n : ℝ) * ∑ j, redR μ D β j := by
  letI : IsProbabilityMeasure ν := hν.1
  have hk := hP.2.1
  have hn : 2 ≤ n := by
    unfold kOf at hk
    omega
  have hterm (j : Fin m) (i : Fin n) : Integrable (fun U =>
      μ i * haarSignY (hCol μ D β j) U i ^ 2) ν := by
    have hm : Measurable (fun U : Matrix.orthogonalGroup (Fin n) ℝ =>
        μ i * haarSignY (hCol μ D β j) U i ^ 2) :=
      measurable_const.mul (((hv_haarSignY_measurable (B := B) μ D j i).comp
        (measurable_id.prodMk measurable_const)).pow_const 2)
    refine Integrable.mono' (integrable_const (|μ i| * (n : ℝ) ^ 2))
      hm.aestronglyMeasurable ?_
    filter_upwards [] with U
    rw [Real.norm_eq_abs, abs_mul, abs_pow]
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (abs_nonneg _) (hv_haarSignY_abs_le (hCol μ D β j) U i) 2)
      (abs_nonneg _)
  have hmoment (j : Fin m) (i : Fin n) :
      ∫ U, μ i * haarSignY (hCol μ D β j) U i ^ 2 ∂ν =
        μ i * ((1 - 2 / Real.pi) + 2 * (n : ℝ) / Real.pi *
          (hCol μ D β j i ^ 2 / (hCol μ D β j ⬝ᵥ hCol μ D β j))) := by
    rw [integral_const_mul]
    have h := lem_app_sgd_haar_sign_i n hn ν hν (hCol μ D β j) (hβ j) i i
    rw [if_pos rfl, hv_euclidNorm_sq] at h
    simpa only [pow_two] using congrArg (fun x => μ i * x) h
  have hsum (j : Fin m) :
      ∑ i, μ i * ((1 - 2 / Real.pi) + 2 * (n : ℝ) / Real.pi *
          (hCol μ D β j i ^ 2 / (hCol μ D β j ⬝ᵥ hCol μ D β j))) =
        (1 - 2 / Real.pi) * (∑ i, μ i) +
          2 / Real.pi * (n : ℝ) * redR μ D β j := by
    let den : ℝ := hCol μ D β j ⬝ᵥ hCol μ D β j
    have hfirst : ∑ i, μ i * (1 - 2 / Real.pi) =
        (1 - 2 / Real.pi) * ∑ i, μ i := by
      rw [← Finset.sum_mul]
      ring
    have hsecond : ∑ i, μ i * (2 * (n : ℝ) / Real.pi *
        (hCol μ D β j i ^ 2 / den)) =
        2 * (n : ℝ) / Real.pi * ((∑ i, μ i * hCol μ D β j i ^ 2) / den) := by
      simp_rw [div_eq_mul_inv, show ∀ i, μ i * (2 * (n : ℝ) * Real.pi⁻¹ *
          (hCol μ D β j i ^ 2 * den⁻¹)) =
          (2 * (n : ℝ) * Real.pi⁻¹ * den⁻¹) *
            (μ i * hCol μ D β j i ^ 2) by intro i; ring]
      rw [← Finset.mul_sum]
      ring
    have hnum : hCol μ D β j ⬝ᵥ (Matrix.diagonal μ *ᵥ hCol μ D β j) =
        ∑ i, μ i * hCol μ D β j i ^ 2 := by
      simp only [dotProduct, Matrix.mulVec_diagonal]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [show (∑ i, μ i * ((1 - 2 / Real.pi) + 2 * (n : ℝ) / Real.pi *
        (hCol μ D β j i ^ 2 / (hCol μ D β j ⬝ᵥ hCol μ D β j)))) =
        (∑ i, μ i * (1 - 2 / Real.pi)) +
          ∑ i, μ i * (2 * (n : ℝ) / Real.pi *
            (hCol μ D β j i ^ 2 / den)) by
      simp only [mul_add, Finset.sum_add_distrib, den]]
    rw [hfirst, hsecond]
    unfold redR
    rw [hnum]
    change _ = _ + 2 / Real.pi * (n : ℝ) *
      ((∑ i, μ i * hCol μ D β j i ^ 2) / den)
    ring
  calc
    ∫ U, riskTwo (haarSigmaOut U μ) (haarSign μ D U β) ∂ν =
        ∫ U, ∑ j, ∑ i, μ i * haarSignY (hCol μ D β j) U i ^ 2 ∂ν :=
      integral_congr_ae (Filter.Eventually.of_forall fun U => hv_risk_eq_haarSignY μ D U β)
    _ = ∑ j, ∑ i, ∫ U, μ i * haarSignY (hCol μ D β j) U i ^ 2 ∂ν := by
      rw [integral_finsetSum _ (fun j _ => integrable_finsetSum _ fun i _ => hterm j i)]
      apply Finset.sum_congr rfl
      intro j _
      rw [integral_finsetSum _ fun i _ => hterm j i]
    _ = ∑ j, ((1 - 2 / Real.pi) * (∑ i, μ i) +
        2 / Real.pi * (n : ℝ) * redR μ D β j) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [Finset.sum_congr rfl (fun i _ => hmoment j i), hsum]
    _ = (m : ℝ) * (1 - 2 / Real.pi) * (∑ i, μ i) +
        2 / Real.pi * (n : ℝ) * ∑ j, redR μ D β j := by
      rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, Finset.card_univ,
        Fintype.card_fin, ← Finset.mul_sum]
      ring

/-- **lem:app-sgd-reduction**, part (iii): `‖S‖²_F = N_out N_in` almost surely.

cr-2026-10-23. LaTeX statement (verbatim):
\begin{lemma}[Haar reduction]
In the Haar model, put $R_j\defeq h_j^\T\Lambda h_j/\norm{h_j}^2$. Then
$c\le R_j\le L$ almost surely, every entry of $G^\circ$ is nonzero almost
surely, $\norm S_\F^2=\Nout\Nin$, and
\begin{equation}
\mathcal Q=\Nin\Big(1-\frac2\pi\Big)\Tr\Lambda+\frac2\pi\,\Nout\sum_{j=1}^{\Nin}\EE R_j,\qquad
\EE\norm{S^\T u_i}^2=\Nin\Big(1-\frac2\pi\Big)+\frac2\pi\,\Nout\sum_{j=1}^{\Nin}\EE\frac{(h_j)_i^2}{\norm{h_j}^2}.
\end{equation}
\end{lemma}
-/
theorem lem_app_sgd_reduction_iii (P : HaarParams) {n m B : ℕ} (μ : Fin n → ℝ)
    (D : Matrix (Fin n) (Fin m) ℝ) (ν : Measure (Matrix.orthogonalGroup (Fin n) ℝ))
    (hν : Muon.Foundations.IsOrthHaar ν) (hP : def_app_sgd_state_law P n m B μ D) :
    ∀ᵐ p ∂(ν.prod (batchLaw n m B)),
      ∑ i, ∑ j, haarSign μ D p.1 p.2 i j ^ 2 = (n : ℝ) * m := by
  filter_upwards [lem_app_sgd_reduction_ii P μ D ν hν hP] with p hp
  calc
    ∑ i, ∑ j, haarSign μ D p.1 p.2 i j ^ 2 = ∑ _i : Fin n, ∑ _j : Fin m, (1 : ℝ) := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      unfold haarSign
      simp only [Matrix.map_apply]
      rcases Real.sign_apply_eq_of_ne_zero _ (hp i j) with hs | hs <;> simp [hs]
    _ = (n : ℝ) * m := by simp

/-- **lem:app-sgd-reduction**, part (iv): the identity for `𝒬` (`eqn:app-sgd-reduction`, first
display).

cr-2026-10-23. LaTeX statement (verbatim):
\begin{lemma}[Haar reduction]
In the Haar model, put $R_j\defeq h_j^\T\Lambda h_j/\norm{h_j}^2$. Then
$c\le R_j\le L$ almost surely, every entry of $G^\circ$ is nonzero almost
surely, $\norm S_\F^2=\Nout\Nin$, and
\begin{equation}
\mathcal Q=\Nin\Big(1-\frac2\pi\Big)\Tr\Lambda+\frac2\pi\,\Nout\sum_{j=1}^{\Nin}\EE R_j,\qquad
\EE\norm{S^\T u_i}^2=\Nin\Big(1-\frac2\pi\Big)+\frac2\pi\,\Nout\sum_{j=1}^{\Nin}\EE\frac{(h_j)_i^2}{\norm{h_j}^2}.
\end{equation}
\end{lemma}
-/
theorem lem_app_sgd_reduction_iv (P : HaarParams) {n m B : ℕ} (μ : Fin n → ℝ)
    (D : Matrix (Fin n) (Fin m) ℝ) (ν : Measure (Matrix.orthogonalGroup (Fin n) ℝ))
    (hν : Muon.Foundations.IsOrthHaar ν) (hP : def_app_sgd_state_law P n m B μ D) :
    haarQ B ν μ D = (m : ℝ) * (1 - 2 / Real.pi) * (∑ i, μ i)
      + 2 / Real.pi * (n : ℝ) * ∑ j, ∫ β, redR μ D β j ∂(batchLaw n m B) := by
  letI : IsProbabilityMeasure ν := hν.1
  letI : IsProbabilityMeasure (gaussBatch n m) := by unfold gaussBatch; infer_instance
  letI : IsProbabilityMeasure (batchLaw n m B) := by unfold batchLaw; infer_instance
  have hint : Integrable (fun p =>
      riskTwo (haarSigmaOut p.1 μ) (haarSign μ D p.1 p.2))
      (ν.prod (batchLaw n m B)) := hv_risk_integrable (B := B) μ D ν
  have hint' : Integrable (Function.uncurry (fun U
      (β : Fin B → (Fin n → ℝ) × (Fin m → ℝ)) =>
        riskTwo (haarSigmaOut U μ) (haarSign μ D U β)))
      (ν.prod (batchLaw n m B)) := hint
  have hswap := integral_integral_swap hint'
  have hβ : ∀ᵐ β ∂(batchLaw n m B), ∀ j, hCol μ D β j ≠ 0 :=
    ae_all_iff.2 fun j => lem_app_sgd_column_iv P μ D hP j
  have havg : ∀ᵐ β ∂(batchLaw n m B),
      (∫ U, riskTwo (haarSigmaOut U μ) (haarSign μ D U β) ∂ν) =
        (m : ℝ) * (1 - 2 / Real.pi) * (∑ i, μ i) +
          2 / Real.pi * (n : ℝ) * ∑ j, redR μ D β j := by
    filter_upwards [hβ] with β hβ'
    exact hv_risk_haar_average P μ D ν hν hP β hβ'
  have hRint : Integrable (fun β => ∑ j, redR μ D β j) (batchLaw n m B) := by
    apply integrable_finset_sum
    intro j _
    exact hv_redR_integrable P μ D hP j
  unfold haarQ
  rw [integral_prod _ hint, hswap, integral_congr_ae havg]
  rw [integral_add (integrable_const _) (hRint.const_mul _)]
  have hconst : ∫ _β : Fin B → (Fin n → ℝ) × (Fin m → ℝ),
      (m : ℝ) * (1 - 2 / Real.pi) * (∑ i, μ i) ∂(batchLaw n m B) =
      (m : ℝ) * (1 - 2 / Real.pi) * (∑ i, μ i) := by simp
  rw [hconst]
  have hmul : ∫ β, 2 / Real.pi * (n : ℝ) * ∑ j, redR μ D β j
        ∂(batchLaw n m B) =
      (2 / Real.pi * (n : ℝ)) * ∫ β, ∑ j, redR μ D β j
        ∂(batchLaw n m B) := by
    rw [integral_const_mul]
  rw [hmul, integral_finsetSum _ fun j _ => hv_redR_integrable P μ D hP j]

private lemma hv_row_eq_haarSignY {n m B : ℕ} (μ : Fin n → ℝ)
    (D : Matrix (Fin n) (Fin m) ℝ) (U : Matrix.orthogonalGroup (Fin n) ℝ)
    (β : Fin B → (Fin n → ℝ) × (Fin m → ℝ)) (i : Fin n) :
    ((haarSign μ D U β)ᵀ *ᵥ haarCol U i) ⬝ᵥ ((haarSign μ D U β)ᵀ *ᵥ haarCol U i)
      = ∑ j, haarSignY (hCol μ D β j) U i ^ 2 := by
  have he (j : Fin m) : ((haarSign μ D U β)ᵀ *ᵥ haarCol U i) j =
      haarSignY (hCol μ D β j) U i := by
    rw [← hv_haarSignY_entry μ D U β i j]
    simp only [Matrix.mulVec, Matrix.transpose_apply]
    exact Finset.sum_congr rfl fun k _ => by
      rw [show haarCol U i k = (U : Matrix (Fin n) (Fin n) ℝ) k i from rfl]
      ring
  simp only [dotProduct, he, pow_two]

private lemma hv_row_integrable {n m B : ℕ} (μ : Fin n → ℝ)
    (D : Matrix (Fin n) (Fin m) ℝ) (ν : Measure (Matrix.orthogonalGroup (Fin n) ℝ))
    [IsFiniteMeasure ν] [IsFiniteMeasure (batchLaw n m B)] (i : Fin n) :
    Integrable (fun p =>
      ((haarSign μ D p.1 p.2)ᵀ *ᵥ haarCol p.1 i) ⬝ᵥ
        ((haarSign μ D p.1 p.2)ᵀ *ᵥ haarCol p.1 i))
      (ν.prod (batchLaw n m B)) := by
  have hm : Measurable (fun p : Matrix.orthogonalGroup (Fin n) ℝ ×
      (Fin B → (Fin n → ℝ) × (Fin m → ℝ)) =>
      ∑ j, haarSignY (hCol μ D p.2 j) p.1 i ^ 2) :=
    Finset.measurable_sum _ fun j _ => (hv_haarSignY_measurable μ D j i).pow_const 2
  have hi : Integrable (fun p : Matrix.orthogonalGroup (Fin n) ℝ ×
      (Fin B → (Fin n → ℝ) × (Fin m → ℝ)) =>
      ∑ j, haarSignY (hCol μ D p.2 j) p.1 i ^ 2)
      (ν.prod (batchLaw n m B)) := by
    refine Integrable.mono' (integrable_const ((m : ℝ) * (n : ℝ) ^ 2))
      hm.aestronglyMeasurable ?_
    filter_upwards [] with p
    rw [Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg fun j _ => sq_nonneg _)]
    calc
      ∑ j, haarSignY (hCol μ D p.2 j) p.1 i ^ 2
          ≤ ∑ _j : Fin m, (n : ℝ) ^ 2 := Finset.sum_le_sum fun j _ => by
            have hj := pow_le_pow_left₀
              (abs_nonneg (haarSignY (hCol μ D p.2 j) p.1 i))
              (hv_haarSignY_abs_le (hCol μ D p.2 j) p.1 i) 2
            rw [sq_abs] at hj
            exact hj
      _ = (m : ℝ) * (n : ℝ) ^ 2 := by simp only [Finset.sum_const, nsmul_eq_mul,
        Finset.card_univ, Fintype.card_fin]
  exact hi.congr (Filter.Eventually.of_forall fun p => (hv_row_eq_haarSignY μ D p.1 p.2 i).symm)

private lemma hv_ratio_integrable {n m B : ℕ} (μ : Fin n → ℝ)
    (D : Matrix (Fin n) (Fin m) ℝ) (j : Fin m) (i : Fin n) :
    Integrable (fun β => hCol μ D β j i ^ 2 /
      (hCol μ D β j ⬝ᵥ hCol μ D β j)) (batchLaw n m B) := by
  letI : IsProbabilityMeasure (gaussBatch n m) := by unfold gaussBatch; infer_instance
  letI : IsProbabilityMeasure (batchLaw n m B) := by unfold batchLaw; infer_instance
  have hh := hCol_measurable (B := B) μ D j
  have hm : Measurable (fun β : Fin B → (Fin n → ℝ) × (Fin m → ℝ) =>
      hCol μ D β j ⬝ᵥ hCol μ D β j) := by
    simp only [dotProduct]
    exact Finset.measurable_sum _ fun l _ =>
      ((measurable_pi_apply l).comp hh).mul ((measurable_pi_apply l).comp hh)
  refine Integrable.mono' (integrable_const (1 : ℝ))
    ((((measurable_pi_apply i).comp hh).pow_const 2).div hm).aestronglyMeasurable ?_
  filter_upwards [] with β
  have hden : 0 ≤ hCol μ D β j ⬝ᵥ hCol μ D β j := by
    exact Finset.sum_nonneg fun l _ => mul_self_nonneg _
  rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (sq_nonneg _) hden)]
  apply div_le_one_of_le₀
  · simpa only [dotProduct, pow_two] using
      (Finset.single_le_sum (f := fun l => hCol μ D β j l ^ 2)
        (fun l _ => sq_nonneg _) (Finset.mem_univ i))
  · exact hden

/-- **lem:app-sgd-reduction**, part (v): the identity for the row sums `E‖Sᵀ u_i‖²`
(`eqn:app-sgd-reduction`, second display), for each row `i`, with `u_i = U e_i`.

cr-2026-10-23. LaTeX statement (verbatim):
\begin{lemma}[Haar reduction]
In the Haar model, put $R_j\defeq h_j^\T\Lambda h_j/\norm{h_j}^2$. Then
$c\le R_j\le L$ almost surely, every entry of $G^\circ$ is nonzero almost
surely, $\norm S_\F^2=\Nout\Nin$, and
\begin{equation}
\mathcal Q=\Nin\Big(1-\frac2\pi\Big)\Tr\Lambda+\frac2\pi\,\Nout\sum_{j=1}^{\Nin}\EE R_j,\qquad
\EE\norm{S^\T u_i}^2=\Nin\Big(1-\frac2\pi\Big)+\frac2\pi\,\Nout\sum_{j=1}^{\Nin}\EE\frac{(h_j)_i^2}{\norm{h_j}^2}.
\end{equation}
\end{lemma}
-/
theorem lem_app_sgd_reduction_v (P : HaarParams) {n m B : ℕ} (μ : Fin n → ℝ)
    (D : Matrix (Fin n) (Fin m) ℝ) (ν : Measure (Matrix.orthogonalGroup (Fin n) ℝ))
    (hν : Muon.Foundations.IsOrthHaar ν) (hP : def_app_sgd_state_law P n m B μ D) (i : Fin n) :
    ∫ p, ((haarSign μ D p.1 p.2)ᵀ *ᵥ haarCol p.1 i) ⬝ᵥ ((haarSign μ D p.1 p.2)ᵀ *ᵥ haarCol p.1 i)
        ∂(ν.prod (batchLaw n m B))
      = (m : ℝ) * (1 - 2 / Real.pi)
        + 2 / Real.pi * (n : ℝ) * ∑ j, ∫ β, hCol μ D β j i ^ 2 / (hCol μ D β j ⬝ᵥ hCol μ D β j)
            ∂(batchLaw n m B) := by
  letI : IsProbabilityMeasure ν := hν.1
  letI : IsProbabilityMeasure (gaussBatch n m) := by unfold gaussBatch; infer_instance
  letI : IsProbabilityMeasure (batchLaw n m B) := by unfold batchLaw; infer_instance
  have hn : 2 ≤ n := by
    have hk := hP.2.1
    unfold kOf at hk
    omega
  have hint := hv_row_integrable (B := B) μ D ν i
  have hint' : Integrable (Function.uncurry (fun U
      (β : Fin B → (Fin n → ℝ) × (Fin m → ℝ)) =>
        ((haarSign μ D U β)ᵀ *ᵥ haarCol U i) ⬝ᵥ ((haarSign μ D U β)ᵀ *ᵥ haarCol U i)))
      (ν.prod (batchLaw n m B)) := hint
  have hswap := integral_integral_swap hint'
  have hβ : ∀ᵐ β ∂(batchLaw n m B), ∀ j, hCol μ D β j ≠ 0 :=
    ae_all_iff.2 fun j => lem_app_sgd_column_iv P μ D hP j
  have havg : ∀ᵐ β ∂(batchLaw n m B),
      (∫ U, ((haarSign μ D U β)ᵀ *ᵥ haarCol U i) ⬝ᵥ
          ((haarSign μ D U β)ᵀ *ᵥ haarCol U i) ∂ν) =
        (m : ℝ) * (1 - 2 / Real.pi) + 2 / Real.pi * (n : ℝ) *
          ∑ j, hCol μ D β j i ^ 2 / (hCol μ D β j ⬝ᵥ hCol μ D β j) := by
    filter_upwards [hβ] with β hβ'
    have hterm (j : Fin m) : Integrable (fun U =>
        haarSignY (hCol μ D β j) U i ^ 2) ν := by
      have hm : Measurable (fun U : Matrix.orthogonalGroup (Fin n) ℝ =>
          haarSignY (hCol μ D β j) U i ^ 2) :=
        (((hv_haarSignY_measurable (B := B) μ D j i).comp
          (measurable_id.prodMk measurable_const)).pow_const 2)
      refine Integrable.mono' (integrable_const ((n : ℝ) ^ 2)) hm.aestronglyMeasurable ?_
      filter_upwards [] with U
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      have hj := pow_le_pow_left₀ (abs_nonneg (haarSignY (hCol μ D β j) U i))
        (hv_haarSignY_abs_le (hCol μ D β j) U i) 2
      rw [sq_abs] at hj
      exact hj
    have hmoment (j : Fin m) :
        ∫ U, haarSignY (hCol μ D β j) U i ^ 2 ∂ν =
          (1 - 2 / Real.pi) + 2 * (n : ℝ) / Real.pi *
            (hCol μ D β j i ^ 2 / (hCol μ D β j ⬝ᵥ hCol μ D β j)) := by
      have h := lem_app_sgd_haar_sign_i n hn ν hν (hCol μ D β j) (hβ' j) i i
      rw [if_pos rfl, hv_euclidNorm_sq] at h
      simpa only [pow_two] using h
    calc
      _ = ∫ U, ∑ j, haarSignY (hCol μ D β j) U i ^ 2 ∂ν :=
        integral_congr_ae (Filter.Eventually.of_forall fun U => hv_row_eq_haarSignY μ D U β i)
      _ = ∑ j, ∫ U, haarSignY (hCol μ D β j) U i ^ 2 ∂ν := by
        rw [integral_finsetSum _ fun j _ => hterm j]
      _ = ∑ j, ((1 - 2 / Real.pi) + 2 * (n : ℝ) / Real.pi *
          (hCol μ D β j i ^ 2 / (hCol μ D β j ⬝ᵥ hCol μ D β j))) := by
        exact Finset.sum_congr rfl fun j _ => hmoment j
      _ = _ := by
        rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, Finset.card_univ,
          Fintype.card_fin, ← Finset.mul_sum]
        ring
  have hratio : Integrable (fun β => ∑ j, hCol μ D β j i ^ 2 /
      (hCol μ D β j ⬝ᵥ hCol μ D β j)) (batchLaw n m B) :=
    integrable_finsetSum _ fun j _ => hv_ratio_integrable μ D j i
  rw [integral_prod _ hint, hswap, integral_congr_ae havg,
    integral_add (integrable_const _) (hratio.const_mul _)]
  simp only [integral_const, probReal_univ, one_smul, integral_const_mul]
  rw [integral_finsetSum _ fun j _ => hv_ratio_integrable μ D j i]

/-! ## Half-anisotropic weighted volatility (`thm:app-sgd-half-volatility`) -/

private lemma hv_integral_abs_le_of_lintegral {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) (f : Ω → ℝ) (hf : AEStronglyMeasurable f ν) (C : ℝ) (hC : 0 ≤ C)
    (h : ∫⁻ ω, ENNReal.ofReal |f ω| ∂ν ≤ ENNReal.ofReal C) :
    Integrable (fun ω => |f ω|) ν ∧ ∫ ω, |f ω| ∂ν ≤ C := by
  have hfin : ∫⁻ ω, ENNReal.ofReal |f ω| ∂ν < ⊤ :=
    lt_of_le_of_lt h ENNReal.ofReal_lt_top
  have hi : Integrable (fun ω => |f ω|) ν :=
    ⟨hf.norm, (hasFiniteIntegral_iff_ofReal
      (Filter.Eventually.of_forall fun ω => abs_nonneg (f ω))).2 hfin⟩
  refine ⟨hi, ?_⟩
  have he := ofReal_integral_eq_lintegral_ofReal hi
    (Filter.Eventually.of_forall fun ω => abs_nonneg (f ω))
  exact (ENNReal.ofReal_le_ofReal_iff hC).1 (he.symm ▸ h)

private lemma hv_diag_op_bound {n : ℕ} (μ : Fin n → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (hμ : ∀ i, |μ i| ≤ L) :
    Muon.External.matOpNorm (Matrix.diagonal μ) ≤ L := by
  unfold Muon.External.matOpNorm
  refine ContinuousLinearMap.opNorm_le_bound _ hL fun x => ?_
  let T := LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin (Matrix.diagonal μ))
  have hsq : ‖T x‖ ^ 2 ≤ L ^ 2 * ‖x‖ ^ 2 := by
    simp only [EuclideanSpace.real_norm_sq_eq]
    dsimp [T]
    simp only [Matrix.mulVec_diagonal]
    change ∑ i, (μ i * x i) ^ 2 ≤ L ^ 2 * ∑ i, x i ^ 2
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun i _ => by
      have hi := pow_le_pow_left₀ (abs_nonneg (μ i)) (hμ i) 2
      rw [sq_abs] at hi
      nlinarith [sq_nonneg (x i)]
  change ‖T x‖ ≤ L * ‖x‖
  nlinarith [norm_nonneg (T x), norm_nonneg x, mul_nonneg hL (norm_nonneg x)]

private lemma hv_one_op_bound {n : ℕ} :
    Muon.External.matOpNorm (1 : Matrix (Fin n) (Fin n) ℝ) ≤ 1 := by
  have h := hv_diag_op_bound (fun _ : Fin n => (1 : ℝ)) 1 (by norm_num) (fun _ => by simp)
  simpa only [Matrix.diagonal_one] using h

private lemma hv_trace_diag_sq {n : ℕ} (μ : Fin n → ℝ) :
    (Matrix.diagonal μ * Matrix.diagonal μ).trace = ∑ i, μ i ^ 2 := by
  simp only [Matrix.trace, Matrix.diag, Matrix.diagonal_mul, Matrix.diagonal_apply_eq, pow_two]

private lemma hv_trace_one_diag {n : ℕ} (μ : Fin n → ℝ) :
    ((1 : Matrix (Fin n) (Fin n) ℝ) * Matrix.diagonal μ).trace = ∑ i, μ i := by
  simp

/-- **thm:app-sgd-half-volatility**: there is an admissible `C_vol` such that
`|𝒬 - 𝒬_print| ≤ C_vol N_out N_in / √k`, both `𝒬` and `𝒬_print` lie in `[c N_out N_in, L N_out N_in]`,
and `|𝒬/𝒬_print - 1| ≤ C_vol/(c √k)`.

cr-2026-10-23. LaTeX statement (verbatim):
\begin{theorem}[Half-anisotropic weighted volatility]
In the Haar model of \cref{def:app-sgd-state-law} there is an admissible
constant $C_{\rm vol}$ such that
\begin{equation}
\abs{\mathcal Q-\mathcal Q_{\rm print}}\le C_{\rm vol}\,\frac{\Nout\Nin}{\sqrt k},
\end{equation}
and both $\mathcal Q$ and $\mathcal Q_{\rm print}$ lie in $[c\Nout\Nin,L\Nout\Nin]$.
In particular $\abs{\mathcal Q/\mathcal Q_{\rm print}-1}\le C_{\rm vol}/(c\sqrt k)$.
\end{theorem}
-/
theorem thm_app_sgd_half_volatility (P : HaarParams) :
    ∃ Cvol : ℝ, 0 ≤ Cvol ∧
      ∀ (n m B : ℕ) (μ : Fin n → ℝ) (D : Matrix (Fin n) (Fin m) ℝ)
        (ν : Measure (Matrix.orthogonalGroup (Fin n) ℝ)),
        Muon.Foundations.IsOrthHaar ν → def_app_sgd_state_law P n m B μ D →
        |haarQ B ν μ D - haarQPrint n m μ| ≤ Cvol * ((n : ℝ) * m) / Real.sqrt (kOf n m B : ℝ) ∧
        P.c * ((n : ℝ) * m) ≤ haarQ B ν μ D ∧ haarQ B ν μ D ≤ P.L * ((n : ℝ) * m) ∧
        P.c * ((n : ℝ) * m) ≤ haarQPrint n m μ ∧ haarQPrint n m μ ≤ P.L * ((n : ℝ) * m) ∧
        |haarQ B ν μ D / haarQPrint n m μ - 1| ≤ Cvol / (P.c * Real.sqrt (kOf n m B : ℝ)) := by
  obtain ⟨Vs, Ds, hVs, hDs, hquad⟩ := prop_app_sgd_quadratic P
  let xmin : ℝ := P.c ^ 2 * P.fMin ^ 2 / P.K
  let Cvol : ℝ := 4 * P.L / (Real.pi * xmin) * (Real.sqrt Vs + Ds)
  have hL : 0 < P.L := P.c_pos.trans_le P.c_le_L
  have hK : 0 < P.K := zero_lt_one.trans_le P.one_le_K
  have hxmin : 0 < xmin := by
    dsimp [xmin]
    exact div_pos (mul_pos (sq_pos_of_pos P.c_pos) (sq_pos_of_pos P.fMin_pos)) hK
  have hCvol : 0 ≤ Cvol := by
    dsimp [Cvol]
    positivity
  refine ⟨Cvol, hCvol, ?_⟩
  intro n m B μ D ν hν hP
  letI : IsProbabilityMeasure ν := hν.1
  letI : IsProbabilityMeasure (gaussBatch n m) := by unfold gaussBatch; infer_instance
  letI : IsProbabilityMeasure (batchLaw n m B) := by unfold batchLaw; infer_instance
  obtain ⟨⟨hn, hm, hB⟩, hk2, hnK, hmK, hBK, hμ, hflo, hfhi, hcol⟩ := hP
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hBR : (0 : ℝ) < B := by exact_mod_cast hB
  have hkR : (0 : ℝ) < (kOf n m B : ℝ) := by exact_mod_cast (by omega : 0 < kOf n m B)
  have hk1 : (1 : ℝ) ≤ (kOf n m B : ℝ) := by exact_mod_cast (by omega : 1 ≤ kOf n m B)
  have hsqrtk : 0 < Real.sqrt (kOf n m B : ℝ) := Real.sqrt_pos.2 hkR
  have hpi : 0 < Real.pi := Real.pi_pos
  have ha : 0 < 2 / Real.pi := by positivity
  have hb : 0 < 1 - 2 / Real.pi := by
    rw [sub_pos, div_lt_one₀ Real.pi_pos]
    linarith [Real.pi_gt_three]
  let trμ : ℝ := ∑ i, μ i
  let trμ2 : ℝ := ∑ i, μ i ^ 2
  let a0 : ℝ := trμ2 / trμ
  let y0 : ℝ := twoR μ D / (B : ℝ) * trμ
  let x0 : ℝ := twoR μ D / (B : ℝ) * trμ2
  have htrlo : P.c * (n : ℝ) ≤ trμ := by
    dsimp [trμ]
    simpa [Finset.mul_sum, mul_comm] using
      (Finset.sum_le_sum (s := Finset.univ) fun i _ => (hμ i).1)
  have htrhi : trμ ≤ P.L * (n : ℝ) := by
    dsimp [trμ]
    simpa [Finset.mul_sum, mul_comm] using
      (Finset.sum_le_sum (s := Finset.univ) fun i _ => (hμ i).2)
  have htrpos : 0 < trμ := (mul_pos P.c_pos hnR).trans_le htrlo
  have hRlo : haarPminus P ≤ twoR μ D := (haar_bounds P n m B μ D
    ⟨⟨hn, hm, hB⟩, hk2, hnK, hmK, hBK, hμ, hflo, hfhi, hcol⟩).1
  have hRpos : 0 < twoR μ D := by
    have hp : 0 < haarPminus P := by
      unfold haarPminus
      exact mul_pos P.c_pos (sq_pos_of_pos P.fMin_pos)
    exact hp.trans_le hRlo
  have hy0 : 0 < y0 := by dsimp [y0]; positivity
  have hymin : xmin ≤ y0 := by
    have hnB : 1 / P.K ≤ (n : ℝ) / (B : ℝ) := by
      apply (div_le_div_iff₀ hK hBR).2
      have hkn : (kOf n m B : ℝ) ≤ (n : ℝ) := by
        exact_mod_cast (show kOf n m B ≤ n by unfold kOf; omega)
      have hKkn : P.K * (kOf n m B : ℝ) ≤ P.K * (n : ℝ) :=
        mul_le_mul_of_nonneg_left hkn hK.le
      nlinarith
    have hbase : P.c ^ 2 * P.fMin ^ 2 ≤ twoR μ D * (trμ / (n : ℝ)) := by
      have hbar : P.c ≤ trμ / (n : ℝ) := (le_div_iff₀ hnR).2 (by nlinarith)
      calc
        P.c ^ 2 * P.fMin ^ 2 = haarPminus P * P.c := by
          unfold haarPminus
          ring
        _ ≤ twoR μ D * (trμ / (n : ℝ)) :=
          mul_le_mul hRlo hbar P.c_pos.le hRpos.le
    dsimp [xmin, y0]
    calc
      P.c ^ 2 * P.fMin ^ 2 / P.K
          ≤ (twoR μ D * (trμ / (n : ℝ))) * ((n : ℝ) / (B : ℝ)) := by
            exact mul_le_mul hbase (by simpa only [one_div] using hnB)
              (by positivity) (by positivity)
      _ = twoR μ D / (B : ℝ) * trμ := by field_simp <;> ring
  have hdiagop : Muon.External.matOpNorm (Matrix.diagonal μ) ≤ P.L :=
    hv_diag_op_bound μ P.L hL.le (fun i => by
      rw [abs_of_nonneg (P.c_pos.le.trans (hμ i).1)]
      exact (hμ i).2)
  let E : ℝ := Real.sqrt (Vs / (kOf n m B : ℝ)) + Ds / (kOf n m B : ℝ)
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hcolerr (j : Fin m) :
      |(∫ β, redR μ D β j ∂(batchLaw n m B)) - a0| ≤ 2 * P.L * E / xmin := by
    let X : (Fin B → (Fin n → ℝ) × (Fin m → ℝ)) → ℝ := fun β =>
      hCol μ D β j ⬝ᵥ (Matrix.diagonal μ *ᵥ hCol μ D β j)
    let Y : (Fin B → (Fin n → ℝ) × (Fin m → ℝ)) → ℝ := fun β =>
      hCol μ D β j ⬝ᵥ hCol μ D β j
    have hXint : Integrable X (batchLaw n m B) :=
      hv_hcol_quadratic_integrable μ D j (Matrix.diagonal μ)
    have hYint : Integrable Y (batchLaw n m B) := by
      simpa [Y] using hv_hcol_quadratic_integrable μ D j (1 : Matrix (Fin n) (Fin n) ℝ)
    have hXL := hquad n m B μ D
      ⟨⟨hn, hm, hB⟩, hk2, hnK, hmK, hBK, hμ, hflo, hfhi, hcol⟩
      (Matrix.diagonal μ) (by simp) j
    have hYL := hquad n m B μ D
      ⟨⟨hn, hm, hB⟩, hk2, hnK, hmK, hBK, hμ, hflo, hfhi, hcol⟩
      (1 : Matrix (Fin n) (Fin n) ℝ) (by simp) j
    have hopdiag : 0 ≤ Muon.External.matOpNorm (Matrix.diagonal μ) := by
      unfold Muon.External.matOpNorm
      exact norm_nonneg _
    have hopone : 0 ≤ Muon.External.matOpNorm (1 : Matrix (Fin n) (Fin n) ℝ) := by
      unfold Muon.External.matOpNorm
      exact norm_nonneg _
    have hCX : 0 ≤ Muon.External.matOpNorm (Matrix.diagonal μ) * E := mul_nonneg hopdiag hE
    have hCY : 0 ≤ Muon.External.matOpNorm (1 : Matrix (Fin n) (Fin n) ℝ) * E :=
      mul_nonneg hopone hE
    have hXL' : ∫⁻ β, ENNReal.ofReal |X β - x0| ∂(batchLaw n m B) ≤
        ENNReal.ofReal (Muon.External.matOpNorm (Matrix.diagonal μ) * E) := by
      simpa only [X, x0, E, hv_trace_diag_sq] using hXL
    have hYL' : ∫⁻ β, ENNReal.ofReal |Y β - y0| ∂(batchLaw n m B) ≤
        ENNReal.ofReal (Muon.External.matOpNorm (1 : Matrix (Fin n) (Fin n) ℝ) * E) := by
      simpa only [Y, y0, E, Matrix.one_mulVec, hv_trace_one_diag] using hYL
    obtain ⟨hXabsint, hXabs⟩ := hv_integral_abs_le_of_lintegral
      (batchLaw n m B) (fun β => X β - x0)
      (hXint.sub (integrable_const _)).aestronglyMeasurable _ hCX hXL'
    obtain ⟨hYabsint, hYabs⟩ := hv_integral_abs_le_of_lintegral
      (batchLaw n m B) (fun β => Y β - y0)
      (hYint.sub (integrable_const _)).aestronglyMeasurable _ hCY hYL'
    have hpoint : ∀ᵐ β ∂(batchLaw n m B),
        |redR μ D β j - a0| ≤ (|X β - x0| + P.L * |Y β - y0|) / y0 := by
      filter_upwards [lem_app_sgd_reduction_i P μ D
        ⟨⟨hn, hm, hB⟩, hk2, hnK, hmK, hBK, hμ, hflo, hfhi, hcol⟩ j,
        lem_app_sgd_column_iv P μ D
          ⟨⟨hn, hm, hB⟩, hk2, hnK, hmK, hBK, hμ, hflo, hfhi, hcol⟩ j] with β hred hnz
      have hYpos : 0 < Y β := by
        dsimp [Y]
        simpa using (Matrix.dotProduct_self_star_pos_iff.mpr hnz)
      have hxy : X β / Y β = redR μ D β j := rfl
      have hx0 : x0 = a0 * y0 := by
        dsimp [x0, a0, y0]
        field_simp
        <;> ring
      have halg : redR μ D β j - a0 =
          ((X β - x0) + redR μ D β j * (y0 - Y β)) / y0 := by
        rw [← hxy, hx0]
        field_simp
        <;> ring
      rw [halg, abs_div, abs_of_pos hy0]
      refine div_le_div_of_nonneg_right ?_ hy0.le
      calc
        |(X β - x0) + redR μ D β j * (y0 - Y β)|
            ≤ |X β - x0| + |redR μ D β j * (y0 - Y β)| := abs_add_le _ _
        _ = |X β - x0| + redR μ D β j * |Y β - y0| := by
          rw [abs_mul, abs_of_nonneg (P.c_pos.le.trans hred.1)]
          congr 2
          exact abs_sub_comm _ _
        _ ≤ |X β - x0| + P.L * |Y β - y0| :=
          by simpa only [add_comm] using
            add_le_add_left (mul_le_mul_of_nonneg_right hred.2
              (abs_nonneg (Y β - y0))) |X β - x0|
    have hRint := hv_redR_integrable P μ D
      ⟨⟨hn, hm, hB⟩, hk2, hnK, hmK, hBK, hμ, hflo, hfhi, hcol⟩ j
    have hrhsint : Integrable (fun β => (|X β - x0| + P.L * |Y β - y0|) / y0)
        (batchLaw n m B) := (hXabsint.add (hYabsint.const_mul P.L)).div_const y0
    calc
      |(∫ β, redR μ D β j ∂(batchLaw n m B)) - a0|
          = |∫ β, (redR μ D β j - a0) ∂(batchLaw n m B)| := by
            rw [integral_sub hRint (integrable_const _)]
            simp
      _ ≤ ∫ β, |redR μ D β j - a0| ∂(batchLaw n m B) := abs_integral_le_integral_abs
      _ ≤ ∫ β, (|X β - x0| + P.L * |Y β - y0|) / y0
          ∂(batchLaw n m B) := integral_mono_ae (hRint.sub (integrable_const _)).abs hrhsint hpoint
      _ = ((∫ β, |X β - x0| ∂(batchLaw n m B)) +
          P.L * (∫ β, |Y β - y0| ∂(batchLaw n m B))) / y0 := by
            rw [integral_div, integral_add hXabsint (hYabsint.const_mul P.L),
              integral_const_mul]
      _ ≤ (Muon.External.matOpNorm (Matrix.diagonal μ) * E +
          P.L * (Muon.External.matOpNorm (1 : Matrix (Fin n) (Fin n) ℝ) * E)) / y0 := by
            gcongr
      _ ≤ (P.L * E + P.L * (1 * E)) / y0 := by
            gcongr
            exact hv_one_op_bound
      _ = 2 * P.L * E / y0 := by ring
      _ ≤ 2 * P.L * E / xmin := div_le_div_of_nonneg_left (by positivity) hxmin hymin
  have hEscale : E ≤ (Real.sqrt Vs + Ds) / Real.sqrt (kOf n m B : ℝ) := by
    dsimp [E]
    rw [Real.sqrt_div (by positivity : 0 ≤ Vs)]
    have hsle : Real.sqrt (kOf n m B : ℝ) ≤ (kOf n m B : ℝ) :=
      Real.sqrt_le_self_iff.mpr (Or.inr hk1)
    have hD : Ds / (kOf n m B : ℝ) ≤ Ds / Real.sqrt (kOf n m B : ℝ) :=
      div_le_div_of_nonneg_left hDs hsqrtk hsle
    calc
      Real.sqrt Vs / Real.sqrt (kOf n m B : ℝ) + Ds / (kOf n m B : ℝ)
          ≤ Real.sqrt Vs / Real.sqrt (kOf n m B : ℝ) +
            Ds / Real.sqrt (kOf n m B : ℝ) := add_le_add le_rfl hD
      _ = (Real.sqrt Vs + Ds) / Real.sqrt (kOf n m B : ℝ) := by ring
  have hQid := lem_app_sgd_reduction_iv P μ D ν hν
    ⟨⟨hn, hm, hB⟩, hk2, hnK, hmK, hBK, hμ, hflo, hfhi, hcol⟩
  have hQP : haarQPrint n m μ = (m : ℝ) * (1 - 2 / Real.pi) * trμ +
      2 / Real.pi * (n : ℝ) * ∑ _j : Fin m, a0 := by
    unfold haarQPrint
    dsimp [trμ, trμ2, a0]
    rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, Fintype.card_fin]
    ring
  have hmain : |haarQ B ν μ D - haarQPrint n m μ| ≤
      Cvol * ((n : ℝ) * m) / Real.sqrt (kOf n m B : ℝ) := by
    rw [hQid, hQP]
    have hsum : |(∑ j, ∫ β, redR μ D β j ∂(batchLaw n m B)) - ∑ _j : Fin m, a0| ≤
        (m : ℝ) * (2 * P.L * E / xmin) := by
      rw [← Finset.sum_sub_distrib]
      exact (Finset.abs_sum_le_sum_abs _ _).trans (by
        simpa only [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, Fintype.card_fin]
          using Finset.sum_le_sum (s := Finset.univ) (fun j _ => hcolerr j))
    have heq : (m : ℝ) * (1 - 2 / Real.pi) * trμ +
        2 / Real.pi * (n : ℝ) * (∑ j, ∫ β, redR μ D β j ∂(batchLaw n m B)) -
        ((m : ℝ) * (1 - 2 / Real.pi) * trμ +
          2 / Real.pi * (n : ℝ) * ∑ _j : Fin m, a0) =
        (2 / Real.pi * (n : ℝ)) *
          ((∑ j, ∫ β, redR μ D β j ∂(batchLaw n m B)) - ∑ _j : Fin m, a0) := by ring
    rw [heq, abs_mul, abs_of_nonneg (by positivity : 0 ≤ 2 / Real.pi * (n : ℝ))]
    calc
      _ ≤ (2 / Real.pi * (n : ℝ)) * ((m : ℝ) * (2 * P.L * E / xmin)) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
      _ ≤ (2 / Real.pi * (n : ℝ)) *
          ((m : ℝ) * (2 * P.L * ((Real.sqrt Vs + Ds) /
            Real.sqrt (kOf n m B : ℝ)) / xmin)) := by gcongr
      _ = Cvol * ((n : ℝ) * m) / Real.sqrt (kOf n m B : ℝ) := by
        dsimp [Cvol]
        ring
  have hER (j : Fin m) : P.c ≤ ∫ β, redR μ D β j ∂(batchLaw n m B) ∧
      ∫ β, redR μ D β j ∂(batchLaw n m B) ≤ P.L := by
    have hi := hv_redR_integrable P μ D
      ⟨⟨hn, hm, hB⟩, hk2, hnK, hmK, hBK, hμ, hflo, hfhi, hcol⟩ j
    have hae := lem_app_sgd_reduction_i P μ D
      ⟨⟨hn, hm, hB⟩, hk2, hnK, hmK, hBK, hμ, hflo, hfhi, hcol⟩ j
    constructor
    · calc
        P.c = ∫ _β, P.c ∂(batchLaw n m B) := by simp
        _ ≤ ∫ β, redR μ D β j ∂(batchLaw n m B) :=
          integral_mono_ae (integrable_const _) hi (hae.mono fun β h => h.1)
    · calc
        ∫ β, redR μ D β j ∂(batchLaw n m B) ≤ ∫ _β, P.L ∂(batchLaw n m B) :=
          integral_mono_ae hi (integrable_const _) (hae.mono fun β h => h.2)
        _ = P.L := by simp
  have ha0 : P.c ≤ a0 ∧ a0 ≤ P.L := by
    have hlo : P.c * trμ ≤ trμ2 := by
      dsimp [trμ, trμ2]
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum fun i _ => by
        simpa only [pow_two] using
          mul_le_mul_of_nonneg_right (hμ i).1 (P.c_pos.le.trans (hμ i).1)
    have hhi : trμ2 ≤ P.L * trμ := by
      dsimp [trμ, trμ2]
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum fun i _ => by
        simpa only [pow_two, mul_comm] using
          mul_le_mul_of_nonneg_right (hμ i).2 (P.c_pos.le.trans (hμ i).1)
    exact ⟨(le_div_iff₀ htrpos).2 hlo, (div_le_iff₀ htrpos).2 hhi⟩
  have hQrange : P.c * ((n : ℝ) * m) ≤ haarQ B ν μ D ∧
      haarQ B ν μ D ≤ P.L * ((n : ℝ) * m) := by
    rw [hQid]
    have hloR : (m : ℝ) * P.c ≤ ∑ j, ∫ β, redR μ D β j ∂(batchLaw n m B) := by
      simpa only [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, Fintype.card_fin]
        using Finset.sum_le_sum (s := Finset.univ) (fun j _ => (hER j).1)
    have hhiR : (∑ j, ∫ β, redR μ D β j ∂(batchLaw n m B)) ≤ (m : ℝ) * P.L := by
      simpa only [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, Fintype.card_fin]
        using Finset.sum_le_sum (s := Finset.univ) (fun j _ => (hER j).2)
    constructor
    · calc
        P.c * ((n : ℝ) * m) = (m : ℝ) * (1 - 2 / Real.pi) * (P.c * (n : ℝ)) +
            2 / Real.pi * (n : ℝ) * ((m : ℝ) * P.c) := by ring
        _ ≤ (m : ℝ) * (1 - 2 / Real.pi) * trμ +
            2 / Real.pi * (n : ℝ) *
              (∑ j, ∫ β, redR μ D β j ∂(batchLaw n m B)) :=
          add_le_add (mul_le_mul_of_nonneg_left htrlo (mul_nonneg hmR.le hb.le))
            (mul_le_mul_of_nonneg_left hloR (mul_nonneg ha.le hnR.le))
    · calc
        (m : ℝ) * (1 - 2 / Real.pi) * trμ +
            2 / Real.pi * (n : ℝ) *
              (∑ j, ∫ β, redR μ D β j ∂(batchLaw n m B))
            ≤ (m : ℝ) * (1 - 2 / Real.pi) * (P.L * (n : ℝ)) +
              2 / Real.pi * (n : ℝ) * ((m : ℝ) * P.L) :=
          add_le_add (mul_le_mul_of_nonneg_left htrhi (mul_nonneg hmR.le hb.le))
            (mul_le_mul_of_nonneg_left hhiR (mul_nonneg ha.le hnR.le))
        _ = P.L * ((n : ℝ) * m) := by ring
  have hQPrange : P.c * ((n : ℝ) * m) ≤ haarQPrint n m μ ∧
      haarQPrint n m μ ≤ P.L * ((n : ℝ) * m) := by
    rw [hQP]
    have hsuma0 : ∑ _j : Fin m, a0 = (m : ℝ) * a0 := by simp
    rw [hsuma0]
    constructor
    · calc
        P.c * ((n : ℝ) * m) = (m : ℝ) * (1 - 2 / Real.pi) * (P.c * (n : ℝ)) +
            2 / Real.pi * (n : ℝ) * ((m : ℝ) * P.c) := by ring
        _ ≤ (m : ℝ) * (1 - 2 / Real.pi) * trμ +
            2 / Real.pi * (n : ℝ) * ((m : ℝ) * a0) :=
          add_le_add (mul_le_mul_of_nonneg_left htrlo (mul_nonneg hmR.le hb.le))
            (mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left ha0.1 hmR.le) (mul_nonneg ha.le hnR.le))
    · calc
        (m : ℝ) * (1 - 2 / Real.pi) * trμ +
            2 / Real.pi * (n : ℝ) * ((m : ℝ) * a0)
            ≤ (m : ℝ) * (1 - 2 / Real.pi) * (P.L * (n : ℝ)) +
              2 / Real.pi * (n : ℝ) * ((m : ℝ) * P.L) :=
          add_le_add (mul_le_mul_of_nonneg_left htrhi (mul_nonneg hmR.le hb.le))
            (mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left ha0.2 hmR.le) (mul_nonneg ha.le hnR.le))
        _ = P.L * ((n : ℝ) * m) := by ring
  have hQPpos : 0 < haarQPrint n m μ :=
    (mul_pos P.c_pos (mul_pos hnR hmR)).trans_le hQPrange.1
  have hrel : |haarQ B ν μ D / haarQPrint n m μ - 1| ≤
      Cvol / (P.c * Real.sqrt (kOf n m B : ℝ)) := by
    have heq : haarQ B ν μ D / haarQPrint n m μ - 1 =
        (haarQ B ν μ D - haarQPrint n m μ) / haarQPrint n m μ := by
      field_simp
    rw [heq, abs_div, abs_of_pos hQPpos]
    calc
      _ ≤ (Cvol * ((n : ℝ) * m) / Real.sqrt (kOf n m B : ℝ)) /
          haarQPrint n m μ := by gcongr
      _ ≤ (Cvol * ((n : ℝ) * m) / Real.sqrt (kOf n m B : ℝ)) /
          (P.c * ((n : ℝ) * m)) :=
        div_le_div_of_nonneg_left (by positivity) (mul_pos P.c_pos (mul_pos hnR hmR)) hQPrange.1
      _ = Cvol / (P.c * Real.sqrt (kOf n m B : ℝ)) := by field_simp <;> ring
  exact ⟨hmain, hQrange.1, hQrange.2, hQPrange.1, hQPrange.2, hrel⟩

/-! ## One step of the risk (`cor:app-sgd-half-risk`) -/

private lemma hr_orth_entry_abs_le_one {n : ℕ}
    (U : Matrix.orthogonalGroup (Fin n) ℝ) (p i : Fin n) :
    |(U : Matrix (Fin n) (Fin n) ℝ) p i| ≤ 1 := by
  have hUU : (U : Matrix (Fin n) (Fin n) ℝ) *
      (U : Matrix (Fin n) (Fin n) ℝ)ᵀ = 1 :=
    (Matrix.mem_orthogonalGroup_iff (Fin n) ℝ).1 U.2
  have h := congrFun (congrFun hUU p) p
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply_eq] at h
  have hsingle : (U : Matrix (Fin n) (Fin n) ℝ) p i ^ 2
      ≤ ∑ k, (U : Matrix (Fin n) (Fin n) ℝ) p k ^ 2 :=
    Finset.single_le_sum (fun k _ => sq_nonneg _) (Finset.mem_univ i)
  have hs : (U : Matrix (Fin n) (Fin n) ℝ) p i ^ 2 ≤ 1 := by
    calc
      _ ≤ ∑ k, (U : Matrix (Fin n) (Fin n) ℝ) p k ^ 2 := hsingle
      _ = 1 := by simpa [sq] using h
  nlinarith [sq_abs ((U : Matrix (Fin n) (Fin n) ℝ) p i)]

private lemma hr_sign_abs_le_one (x : ℝ) : |Real.sign x| ≤ 1 := by
  rcases lt_trichotomy x 0 with hx | hx | hx
  · simp [Real.sign_of_neg hx]
  · simp [hx]
  · simp [Real.sign_of_pos hx]

private lemma hr_weighted_sign_integrable {n m B : ℕ} (μ : Fin n → ℝ)
    (D : Matrix (Fin n) (Fin m) ℝ) (ν : Measure (Matrix.orthogonalGroup (Fin n) ℝ))
    [IsProbabilityMeasure ν] (p i : Fin n) (j : Fin m) :
    Integrable (fun x => (x.1 : Matrix (Fin n) (Fin n) ℝ) p i *
      haarSign μ D x.1 x.2 p j) (ν.prod (batchLaw n m B)) := by
  haveI : IsProbabilityMeasure (gaussBatch n m) := by unfold gaussBatch; infer_instance
  haveI : IsProbabilityMeasure (batchLaw n m B) := by unfold batchLaw; infer_instance
  have hgrad : Continuous (fun x : Matrix.orthogonalGroup (Fin n) ℝ ×
      (Fin B → (Fin n → ℝ) × (Fin m → ℝ)) =>
      physGrad (haarDelta x.1 D) (haarBatch μ x.1 x.2) p j) := by
    unfold physGrad residual haarBatch linBatch haarDelta Matrix.mulVec dotProduct
    fun_prop
  have hmeas : Measurable (fun x : Matrix.orthogonalGroup (Fin n) ℝ ×
      (Fin B → (Fin n → ℝ) × (Fin m → ℝ)) =>
      (x.1 : Matrix (Fin n) (Fin n) ℝ) p i * haarSign μ D x.1 x.2 p j) :=
    ((continuous_subtype_val.matrix_elem p i).comp continuous_fst).measurable.mul
      (hv_sign_measurable.comp hgrad.measurable)
  refine Integrable.of_bound hmeas.aestronglyMeasurable 1
    (Filter.Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_mul]
  have hsign : |haarSign μ D x.1 x.2 p j| ≤ 1 := by
    simpa only [haarSign, Matrix.map_apply] using
      hr_sign_abs_le_one (physGrad (haarDelta x.1 D) (haarBatch μ x.1 x.2) p j)
  nlinarith [mul_nonneg
    (sub_nonneg.mpr (hr_orth_entry_abs_le_one x.1 p i))
    (abs_nonneg (haarSign μ D x.1 x.2 p j))]

private lemma hr_risk_pair_eq {n m : ℕ} (μ : Fin n → ℝ)
    (D : Matrix (Fin n) (Fin m) ℝ) (U : Matrix.orthogonalGroup (Fin n) ℝ)
    (A : Matrix (Fin n) (Fin m) ℝ) :
    pairIdIn (haarSigmaOut U μ) (haarDelta U D) A
      = ∑ i, ∑ j, μ i * D i j * (((U : Matrix (Fin n) (Fin n) ℝ)ᵀ * A) i j) := by
  have hUt : (U : Matrix (Fin n) (Fin n) ℝ)ᵀ *
      (U : Matrix (Fin n) (Fin n) ℝ) = 1 :=
    (Matrix.mem_orthogonalGroup_iff' (Fin n) ℝ).1 U.2
  have hSD : haarSigmaOut U μ * haarDelta U D
      = (U : Matrix (Fin n) (Fin n) ℝ) * Matrix.diagonal μ * D := by
    unfold haarSigmaOut haarDelta
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (U : Matrix (Fin n) (Fin n) ℝ)ᵀ
      (U : Matrix (Fin n) (Fin n) ℝ), hUt, Matrix.one_mul]
  unfold pairIdIn
  rw [hSD]
  have htrace : ((U : Matrix (Fin n) (Fin n) ℝ) * (Matrix.diagonal μ * D * Aᵀ)).trace
      = ((Matrix.diagonal μ * D * Aᵀ) * (U : Matrix (Fin n) (Fin n) ℝ)).trace :=
    Matrix.trace_mul_comm _ _
  have hDA : (Matrix.diagonal μ * D) * Aᵀ =
      fun i p => ∑ j, μ i * D i j * A p j := by
    ext i p
    rw [Matrix.mul_apply]
    apply Finset.sum_congr rfl
    intro j _
    rw [Matrix.transpose_apply, Matrix.diagonal_mul]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (Matrix.diagonal μ) D Aᵀ, htrace]
  rw [hDA]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply]
  apply Finset.sum_congr rfl
  intro i _
  change (∑ p, (∑ j, μ i * D i j * A p j) *
      (U : Matrix (Fin n) (Fin n) ℝ) p i) =
    ∑ j, μ i * D i j * ∑ p, (U : Matrix (Fin n) (Fin n) ℝ) p i * A p j
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p _
  ring

private lemma hr_risk_pair_integrable {n m B : ℕ} (μ : Fin n → ℝ)
    (D : Matrix (Fin n) (Fin m) ℝ) (ν : Measure (Matrix.orthogonalGroup (Fin n) ℝ))
    [IsProbabilityMeasure ν] :
    Integrable (fun x => pairIdIn (haarSigmaOut x.1 μ) (haarDelta x.1 D)
      (haarSign μ D x.1 x.2)) (ν.prod (batchLaw n m B)) := by
  haveI : IsProbabilityMeasure (gaussBatch n m) := by unfold gaussBatch; infer_instance
  haveI : IsProbabilityMeasure (batchLaw n m B) := by unfold batchLaw; infer_instance
  have hsum : Integrable (fun x => ∑ i, ∑ j, μ i * D i j * ∑ p,
      (x.1 : Matrix (Fin n) (Fin n) ℝ) p i * haarSign μ D x.1 x.2 p j)
      (ν.prod (batchLaw n m B)) := by
    apply integrable_finset_sum
    intro i _
    apply integrable_finset_sum
    intro j _
    apply (integrable_finset_sum _ fun p _ => hr_weighted_sign_integrable μ D ν p i j).const_mul
  refine hsum.congr (Filter.Eventually.of_forall fun x => ?_)
  change (∑ i, ∑ j, μ i * D i j * ∑ p,
      (x.1 : Matrix (Fin n) (Fin n) ℝ) p i * haarSign μ D x.1 x.2 p j) =
    pairIdIn (haarSigmaOut x.1 μ) (haarDelta x.1 D) (haarSign μ D x.1 x.2)
  symm
  calc
    _ = ∑ i, ∑ j, μ i * D i j *
        (((x.1 : Matrix (Fin n) (Fin n) ℝ)ᵀ * haarSign μ D x.1 x.2) i j) :=
      hr_risk_pair_eq μ D x.1 (haarSign μ D x.1 x.2)
    _ = _ := by simp only [Matrix.mul_apply, Matrix.transpose_apply]

private lemma hr_pair_comm {n m : ℕ} (Sg : Matrix (Fin n) (Fin n) ℝ)
    (hSg : Sgᵀ = Sg) (V W : Matrix (Fin n) (Fin m) ℝ) :
    pairIdIn Sg V W = pairIdIn Sg W V := by
  unfold pairIdIn
  rw [← Matrix.trace_transpose (Sg * V * Wᵀ)]
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose, hSg]
  rw [show W * (Vᵀ * Sg) = (W * Vᵀ) * Sg by simp only [Matrix.mul_assoc]]
  rw [show Sg * W * Vᵀ = Sg * (W * Vᵀ) by simp only [Matrix.mul_assoc]]
  exact Matrix.trace_mul_comm _ _

private lemma hr_risk_step {n m : ℕ} (Sg : Matrix (Fin n) (Fin n) ℝ)
    (hSg : Sgᵀ = Sg) (D S : Matrix (Fin n) (Fin m) ℝ) (η : ℝ) :
    riskTwo Sg (D - η • S) / 2 = riskTwo Sg D / 2 - η * pairIdIn Sg D S
      + η ^ 2 / 2 * riskTwo Sg S := by
  have hc := hr_pair_comm Sg hSg S D
  unfold riskTwo pairIdIn at *
  simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.transpose_sub, Matrix.transpose_smul,
    Matrix.mul_smul, Matrix.smul_mul, Matrix.trace_sub, Matrix.trace_smul, smul_eq_mul]
  rw [hc]
  ring

/-- **cor:app-sgd-half-risk**: for `k ≥ k_*` and every deterministic `η ≥ 0`,
`E 𝓡(Δ - η S) = 𝓡 - η L_B ‖Λ D‖²_F + (η²/2) 𝒬_print + 𝓔_η`, with
`|𝓔_η| ≤ η L f₊ √C_* + (η²/2) C_vol N_out N_in / √k`, for admissible `C_*` and `C_vol`.
The risk of the update is `𝓡 = ‖Δ⁺‖²_Σ / 2` with `Σ = U Λ Uᵀ` and `Δ⁺ = Δ - η S`.

cr-2026-10-23. LaTeX statement (verbatim):
\begin{corollary}[One step of the risk]
In the Haar model with $k\ge k_*$, for every deterministic $\lr\ge0$,
\[
\EE\,\cR(\Delta-\lr S)=\cR-\lr L_B\norm{\Lambda D}_\F^2+\frac{\lr^2}2\,\mathcal Q_{\rm print}+\mathcal E_\lr,\qquad
\abs{\mathcal E_\lr}\le\lr Lf_+\sqrt{C_*}+\frac{\lr^2}2\,C_{\rm vol}\frac{\Nout\Nin}{\sqrt k}.
\]
\end{corollary}
-/
theorem cor_app_sgd_half_risk (P : HaarParams) :
    ∃ Cstar Cvol : ℝ, 0 ≤ Cstar ∧ 0 ≤ Cvol ∧
      ∀ (n m B : ℕ) (μ : Fin n → ℝ) (D : Matrix (Fin n) (Fin m) ℝ)
        (ν : Measure (Matrix.orthogonalGroup (Fin n) ℝ)),
        Muon.Foundations.IsOrthHaar ν → def_app_sgd_state_law P n m B μ D →
        haarKStar P ≤ kOf n m B →
        ∀ η : ℝ, 0 ≤ η →
          |(∫ p, riskTwo (haarSigmaOut p.1 μ)
                (def_app_sgd_update η (haarDelta p.1 D) (haarBatch μ p.1 p.2)) / 2
              ∂(ν.prod (batchLaw n m B)))
            - (twoR μ D / 2 - η * LB B μ D * frobNorm (Matrix.diagonal μ * D) ^ 2
                + η ^ 2 / 2 * haarQPrint n m μ)|
          ≤ η * (P.L * P.fMax) * Real.sqrt Cstar
            + η ^ 2 / 2 * (Cvol * ((n : ℝ) * m) / Real.sqrt (kOf n m B : ℝ)) := by
  obtain ⟨Cstar, hCstar, hpair⟩ := cor_app_sgd_half_pairings P
  obtain ⟨Cvol, hCvol, hvol⟩ := thm_app_sgd_half_volatility P
  refine ⟨Cstar, Cvol, hCstar, hCvol, ?_⟩
  intro n m B μ D ν hν hstate hk η hη
  letI : IsProbabilityMeasure ν := hν.1
  letI : IsProbabilityMeasure (gaussBatch n m) := by unfold gaussBatch; infer_instance
  letI : IsProbabilityMeasure (batchLaw n m B) := by unfold batchLaw; infer_instance
  let drift : ℝ := ∫ x, pairIdIn (haarSigmaOut x.1 μ) (haarDelta x.1 D)
    (haarSign μ D x.1 x.2) ∂(ν.prod (batchLaw n m B))
  have hdrift : |drift - LB B μ D * frobNorm (Matrix.diagonal μ * D) ^ 2| ≤
      P.L * P.fMax * Real.sqrt Cstar := by
    exact (hpair n m B μ D ν hν hstate hk).2.2.1
  have hvolatility : |haarQ B ν μ D - haarQPrint n m μ| ≤
      Cvol * ((n : ℝ) * m) / Real.sqrt (kOf n m B : ℝ) :=
    (hvol n m B μ D ν hν hstate).1
  have hcross : Integrable (fun x => pairIdIn (haarSigmaOut x.1 μ)
      (haarDelta x.1 D) (haarSign μ D x.1 x.2))
      (ν.prod (batchLaw n m B)) := hr_risk_pair_integrable μ D ν
  have hquad : Integrable (fun x => riskTwo (haarSigmaOut x.1 μ)
      (haarSign μ D x.1 x.2)) (ν.prod (batchLaw n m B)) :=
    hv_risk_integrable μ D ν
  have hsigma (U : Matrix.orthogonalGroup (Fin n) ℝ) :
      (haarSigmaOut U μ)ᵀ = haarSigmaOut U μ := by
    unfold haarSigmaOut
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.diagonal_transpose,
      Matrix.mul_assoc]
  have hpoint (x : Matrix.orthogonalGroup (Fin n) ℝ ×
      (Fin B → (Fin n → ℝ) × (Fin m → ℝ))) :
      riskTwo (haarSigmaOut x.1 μ)
          (def_app_sgd_update η (haarDelta x.1 D) (haarBatch μ x.1 x.2)) / 2
        = twoR μ D / 2 - η * pairIdIn (haarSigmaOut x.1 μ) (haarDelta x.1 D)
            (haarSign μ D x.1 x.2)
          + η ^ 2 / 2 * riskTwo (haarSigmaOut x.1 μ) (haarSign μ D x.1 x.2) := by
    rw [def_app_sgd_update_eq_signGrad]
    change riskTwo (haarSigmaOut x.1 μ) (haarDelta x.1 D - η • haarSign μ D x.1 x.2) / 2 = _
    rw [hr_risk_step _ (hsigma x.1)]
    rw [(haar_forms_app_sgd P μ D hstate x.1
      ⟨0, hstate.1.1⟩ ⟨0, hstate.1.2.1⟩ ⟨0, hstate.1.1⟩).1]
  have hidentity :
      (∫ x, riskTwo (haarSigmaOut x.1 μ)
            (def_app_sgd_update η (haarDelta x.1 D) (haarBatch μ x.1 x.2)) / 2
          ∂(ν.prod (batchLaw n m B)))
        = twoR μ D / 2 - η * drift + η ^ 2 / 2 * haarQ B ν μ D := by
    rw [integral_congr_ae (Filter.Eventually.of_forall hpoint)]
    calc
      (∫ x, twoR μ D / 2 - η * pairIdIn (haarSigmaOut x.1 μ) (haarDelta x.1 D)
            (haarSign μ D x.1 x.2) + η ^ 2 / 2 *
              riskTwo (haarSigmaOut x.1 μ) (haarSign μ D x.1 x.2)
          ∂(ν.prod (batchLaw n m B))) =
          (∫ x, twoR μ D / 2 - η * pairIdIn (haarSigmaOut x.1 μ) (haarDelta x.1 D)
            (haarSign μ D x.1 x.2) ∂(ν.prod (batchLaw n m B))) +
          ∫ x, η ^ 2 / 2 * riskTwo (haarSigmaOut x.1 μ) (haarSign μ D x.1 x.2)
            ∂(ν.prod (batchLaw n m B)) :=
        integral_add ((integrable_const _).sub (hcross.const_mul η))
          (hquad.const_mul (η ^ 2 / 2))
      _ = twoR μ D / 2 - η * drift + η ^ 2 / 2 * haarQ B ν μ D := by
        rw [integral_sub (integrable_const _) (hcross.const_mul η), integral_const,
          integral_const_mul, integral_const_mul]
        simp only [measureReal_def, measure_univ, ENNReal.toReal_one, one_smul]
        rfl
  rw [hidentity]
  have htri : |-η * (drift - LB B μ D * frobNorm (Matrix.diagonal μ * D) ^ 2) +
      η ^ 2 / 2 * (haarQ B ν μ D - haarQPrint n m μ)|
      ≤ |η| * |drift - LB B μ D * frobNorm (Matrix.diagonal μ * D) ^ 2| +
        |η ^ 2 / 2| *
        |haarQ B ν μ D - haarQPrint n m μ| := by
    calc
      _ ≤ |-η * (drift - LB B μ D * frobNorm (Matrix.diagonal μ * D) ^ 2)| +
          |η ^ 2 / 2 * (haarQ B ν μ D - haarQPrint n m μ)| := abs_add_le _ _
      _ = _ := by rw [abs_mul, abs_mul, abs_neg]
  calc
    |twoR μ D / 2 - η * drift + η ^ 2 / 2 * haarQ B ν μ D -
        (twoR μ D / 2 - η * LB B μ D * frobNorm (Matrix.diagonal μ * D) ^ 2
          + η ^ 2 / 2 * haarQPrint n m μ)|
        = |-η * (drift - LB B μ D * frobNorm (Matrix.diagonal μ * D) ^ 2) +
            η ^ 2 / 2 * (haarQ B ν μ D - haarQPrint n m μ)| := by ring
    _ ≤ |η| * |drift - LB B μ D * frobNorm (Matrix.diagonal μ * D) ^ 2| +
        |η ^ 2 / 2| *
        |haarQ B ν μ D - haarQPrint n m μ| := htri
    _ ≤ η * (P.L * P.fMax * Real.sqrt Cstar) + η ^ 2 / 2 *
        (Cvol * ((n : ℝ) * m) / Real.sqrt (kOf n m B : ℝ)) := by
      rw [abs_of_nonneg hη, abs_of_nonneg (by positivity : 0 ≤ η ^ 2 / 2)]
      exact add_le_add (mul_le_mul_of_nonneg_left hdrift hη)
        (mul_le_mul_of_nonneg_left hvolatility (by positivity))
    _ = η * (P.L * P.fMax) * Real.sqrt Cstar
          + η ^ 2 / 2 * (Cvol * ((n : ℝ) * m) / Real.sqrt (kOf n m B : ℝ)) := by ring

end Muon.SignSGD
