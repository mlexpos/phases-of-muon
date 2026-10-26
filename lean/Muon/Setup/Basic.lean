import Muon.Foundations.Conventions

/-!
# Appendix A: mode and row decomposition

Snapshot `cr-2026-10-23`. Source: `sections/01-setup/section.tex` l.173–182
(`lem:app-setup-decomposition`), card `sections/01-setup/CARD.md` §2 and §5 row L-A.1.

Objects: `SpectralData C` (orthonormal eigenbases of `Σ_out` and `Σ_in`, with eigenvalues `μ`
and `lam`), the pairing `pairSigma` (`eqn:app-setup-pairing`), `riskSigma`, the mode and row
quantities `modeQ` (`𝒬_ij`) and `rowQ` (`𝒬_i`), and the normalized state `Arot`, `Ahat`.

Representation choice: each eigenbasis is held as an orthogonal matrix (columns `u_i`, `v_j`)
rather than an `OrthonormalBasis`, so that Parseval is matrix algebra. Every `SpectralData` is an
arbitrary orthonormal eigenbasis; no ordering is imposed. Lean names: `Σ` is not an identifier
character, so `pairΣ` is `pairSigma` and `riskΣ` is `riskSigma`.
-/

noncomputable section

open scoped Matrix MatrixOrder
open Matrix

namespace Muon.Setup

/-! ## Spectral data -/

/-- Orthonormal eigenbases of `Σ_out` and `Σ_in` with eigenvalues `μ` and `lam`
(`def:app-setup-model`, `section.tex` l.51–56: `Σ_out = Σ_i μ_i u_i ⊗ u_i` and
`Σ_in = Σ_j λ_j v_j ⊗ v_j` "in orthonormal eigenbases, all eigenvalues included").
The column `uOut · i` is `u_i` and the column `vIn · j` is `v_j`. -/
structure SpectralData {m n : ℕ} (C : Covariances m n) where
  /-- Output eigenbasis `u_i` as the columns of an orthogonal matrix. -/
  uOut : Matrix (Fin m) (Fin m) ℝ
  /-- Input eigenbasis `v_j` as the columns of an orthogonal matrix. -/
  vIn : Matrix (Fin n) (Fin n) ℝ
  /-- Output eigenvalues `μ_i`. -/
  μ : Fin m → ℝ
  /-- Input eigenvalues `λ_j` (`lam`, since `λ` is a keyword). -/
  lam : Fin n → ℝ
  huOut : uOutᵀ * uOut = 1
  hvIn : vInᵀ * vIn = 1
  eigOut : ∀ i : Fin m, C.Sout *ᵥ (fun k => uOut k i) = μ i • (fun k => uOut k i)
  eigIn : ∀ j : Fin n, C.Sin *ᵥ (fun k => vIn k j) = lam j • (fun k => vIn k j)

namespace SpectralData

variable {m n : ℕ} {C : Covariances m n}

/-- The output eigenvector `u_i` (`section.tex` l.51–56). -/
def u (S : SpectralData C) (i : Fin m) : Fin m → ℝ := fun k => S.uOut k i

/-- The input eigenvector `v_j` (`section.tex` l.51–56). -/
def v (S : SpectralData C) (j : Fin n) : Fin n → ℝ := fun k => S.vIn k j

end SpectralData

/-- The eigen-equation of `u_i`, in vector form. -/
lemma eig_u {m n : ℕ} {C : Covariances m n} (S : SpectralData C) (i : Fin m) :
    C.Sout *ᵥ S.u i = S.μ i • S.u i :=
  S.eigOut i

/-- The eigen-equation of `v_j`, in vector form. -/
lemma eig_v {m n : ℕ} {C : Covariances m n} (S : SpectralData C) (j : Fin n) :
    C.Sin *ᵥ S.v j = S.lam j • S.v j :=
  S.eigIn j

/-! ## Pairing, risk, mode and row quantities -/

variable {m n : ℕ}

/-- The Σ-pairing `⟨V, W⟩_Σ = Tr(Σ_out V Σ_in Wᵀ)` (`eqn:app-setup-pairing`,
`section.tex` l.64–71). Its square norm is `‖V‖_Σ² = ⟨V, V⟩_Σ`. -/
def pairSigma (C : Covariances m n) (V W : Mat m n) : ℝ :=
  (C.Sout * V * C.Sin * Wᵀ).trace

/-- Population risk in trace form, `riskSigma C Δ = ½ ‖Δ‖_Σ²`
(`eqn:app-setup-risk-trace`, `section.tex`). -/
def riskSigma (C : Covariances m n) (Δ : Mat m n) : ℝ :=
  pairSigma C Δ Δ / 2

/-- Mode quantity `𝒬_ij(Δ) = (u_iᵀ Δ v_j)²` (`eqn:app-setup-pairing`, `section.tex` l.64–71). -/
def modeQ {C : Covariances m n} (S : SpectralData C) (Δ : Mat m n) (i : Fin m) (j : Fin n) : ℝ :=
  (S.u i ⬝ᵥ (Δ *ᵥ S.v j)) ^ 2

/-- Row quantity `𝒬_i(Δ) = ‖Δᵀ u_i‖²` (`eqn:app-setup-pairing`, `section.tex` l.64–71). -/
def rowQ {C : Covariances m n} (S : SpectralData C) (Δ : Mat m n) (i : Fin m) : ℝ :=
  ∑ k, ((Δᵀ *ᵥ S.u i) k) ^ 2

/-- Regularization-free rotation factor `r_out` of `Σ_out` (`section.tex` l.51–56,
`rOut := CFC.sqrt Σ_out`). -/
def rOut {m n : ℕ} (C : Covariances m n) : Matrix (Fin m) (Fin m) ℝ :=
  CFC.sqrt C.Sout

/-- Regularization-free rotation factor `r_in` of `Σ_in`. -/
def rIn {m n : ℕ} (C : Covariances m n) : Matrix (Fin n) (Fin n) ℝ :=
  CFC.sqrt C.Sin

/-- The rotated state `Arot = r_out Δ r_in` (`eqn:app-setup-normalized`, `section.tex` l.209–215). -/
def Arot {m n : ℕ} (C : Covariances m n) (Δ : Mat m n) : Mat m n :=
  rOut C * Δ * rIn C

/-- The normalized state `Ahat = (√(2 riskΣ))⁻¹ Arot` (`eqn:app-setup-normalized`). -/
def Ahat {m n : ℕ} (C : Covariances m n) (Δ : Mat m n) : Mat m n :=
  (Real.sqrt (2 * riskSigma C Δ))⁻¹ • Arot C Δ

/-! ## Matrix-algebra helpers -/

/-- Column normalization: `∑_a A a j * A a j = 1` when `Aᵀ A = 1`. -/
lemma sum_col_sq_eq_one {k : ℕ} (A : Matrix (Fin k) (Fin k) ℝ) (hA : Aᵀ * A = 1) (j : Fin k) :
    ∑ a, A a j * A a j = 1 := by
  have h := congrFun (congrFun hA j) j
  simpa [Matrix.mul_apply] using h

/-- Parseval for an orthogonal matrix: `∑_j (∑_a A a j x_a)(∑_a A a j y_a) = x ⬝ᵥ y`. -/
lemma sum_proj_mul_eq_dot {k : ℕ} (A : Matrix (Fin k) (Fin k) ℝ) (hA : Aᵀ * A = 1)
    (x y : Fin k → ℝ) :
    ∑ j, (∑ a, A a j * x a) * (∑ a, A a j * y a) = x ⬝ᵥ y := by
  have hAA : A * Aᵀ = 1 := mul_eq_one_comm.mp hA
  calc ∑ j, (∑ a, A a j * x a) * (∑ a, A a j * y a)
      = (Aᵀ *ᵥ x) ⬝ᵥ (Aᵀ *ᵥ y) := by
        simp [dotProduct, Matrix.mulVec, Matrix.transpose_apply]
    _ = x ⬝ᵥ (A *ᵥ (Aᵀ *ᵥ y)) := by
        rw [Matrix.mulVec_transpose]
        exact (Matrix.dotProduct_mulVec _ _ _).symm
    _ = x ⬝ᵥ ((A * Aᵀ) *ᵥ y) := by rw [Matrix.mulVec_mulVec]
    _ = x ⬝ᵥ y := by rw [hAA, Matrix.one_mulVec]

/-- The output spectral resolution `Σ_out = U diag(μ) Uᵀ`. -/
lemma Sout_eq_spectral {m n : ℕ} {C : Covariances m n} (S : SpectralData C) :
    C.Sout = S.uOut * diagonal S.μ * S.uOutᵀ := by
  have hUU : S.uOut * S.uOutᵀ = 1 := mul_eq_one_comm.mp S.huOut
  have h1 : C.Sout * S.uOut = S.uOut * diagonal S.μ := by
    ext i j
    have h := congrFun (S.eigOut j) i
    simp [Matrix.mulVec, dotProduct] at h
    rw [Matrix.mul_diagonal]
    simp only [Matrix.mul_apply]
    linear_combination h
  calc C.Sout = C.Sout * (S.uOut * S.uOutᵀ) := by rw [hUU, Matrix.mul_one]
    _ = (C.Sout * S.uOut) * S.uOutᵀ := by rw [Matrix.mul_assoc]
    _ = S.uOut * diagonal S.μ * S.uOutᵀ := by rw [h1]

/-- The input spectral resolution `Σ_in = V diag(λ) Vᵀ`. -/
lemma Sin_eq_spectral {m n : ℕ} {C : Covariances m n} (S : SpectralData C) :
    C.Sin = S.vIn * diagonal S.lam * S.vInᵀ := by
  have hVV : S.vIn * S.vInᵀ = 1 := mul_eq_one_comm.mp S.hvIn
  have h1 : C.Sin * S.vIn = S.vIn * diagonal S.lam := by
    ext i j
    have h := congrFun (S.eigIn j) i
    simp [Matrix.mulVec, dotProduct] at h
    rw [Matrix.mul_diagonal]
    simp only [Matrix.mul_apply]
    linear_combination h
  calc C.Sin = C.Sin * (S.vIn * S.vInᵀ) := by rw [hVV, Matrix.mul_one]
    _ = (C.Sin * S.vIn) * S.vInᵀ := by rw [Matrix.mul_assoc]
    _ = S.vIn * diagonal S.lam * S.vInᵀ := by rw [h1]

/-- Entries of `Uᵀ V Vi`: `(Uᵀ V Vi)_ij = u_i ⬝ᵥ (V v_j)`. -/
lemma P_apply {m n : ℕ} {C : Covariances m n} (S : SpectralData C) (V : Mat m n)
    (i : Fin m) (j : Fin n) :
    (S.uOutᵀ * V * S.vIn) i j = S.u i ⬝ᵥ (V *ᵥ S.v j) := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.mulVec, dotProduct,
    SpectralData.u, SpectralData.v, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring

/-- Trace of a diagonally weighted product, entrywise. -/
lemma trace_diag_form {m n : ℕ} (μ : Fin m → ℝ) (lam : Fin n → ℝ) (M N : Mat m n) :
    Matrix.trace (diagonal μ * M * diagonal lam * Nᵀ)
      = ∑ i, ∑ j, μ i * lam j * (M i j * N i j) := by
  have hA : ∀ i k, (diagonal μ * M * diagonal lam) i k = μ i * M i k * lam k := fun i k => by
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  simp only [Matrix.trace, Matrix.diag_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.mul_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [hA, Matrix.transpose_apply]
  ring

/-- Bilinear eigen-expansion of the pairing (`pairSigma_eq_sum`, used in the proof of
`prop:app-setup-risk-recursion`, `section.tex` l.531–535). -/
theorem pairSigma_eq_sum {m n : ℕ} {C : Covariances m n} (S : SpectralData C) (V W : Mat m n) :
    pairSigma C V W
      = ∑ i, ∑ j, S.μ i * S.lam j * ((S.u i ⬝ᵥ (V *ᵥ S.v j)) * (S.u i ⬝ᵥ (W *ᵥ S.v j))) := by
  have htr : pairSigma C V W
      = Matrix.trace (diagonal S.μ * (S.uOutᵀ * V * S.vIn) * diagonal S.lam
          * (S.uOutᵀ * W * S.vIn)ᵀ) := by
    unfold pairSigma
    rw [Sout_eq_spectral S, Sin_eq_spectral S]
    simp only [Matrix.mul_assoc, Matrix.transpose_mul, Matrix.transpose_transpose]
    rw [Matrix.trace_mul_comm]
    simp only [Matrix.mul_assoc]
  rw [htr, trace_diag_form]
  simp only [P_apply]

/-- Output eigenvalues are nonnegative (from `Σ_out ⪰ 0`). -/
lemma μ_nonneg {m n : ℕ} {C : Covariances m n} (S : SpectralData C) (i : Fin m) :
    0 ≤ S.μ i := by
  have hu : S.u i ⬝ᵥ S.u i = 1 := by
    simpa [dotProduct, SpectralData.u, sq] using sum_col_sq_eq_one S.uOut S.huOut i
  have h1 : S.u i ⬝ᵥ (C.Sout *ᵥ S.u i) = S.μ i := by
    rw [eig_u, dotProduct_smul, hu, smul_eq_mul, mul_one]
  rw [← h1]
  have := C.psdOut.dotProduct_mulVec_nonneg (S.u i)
  simpa using this

/-- Input eigenvalues are nonnegative (from `Σ_in ⪰ 0`). -/
lemma lam_nonneg {m n : ℕ} {C : Covariances m n} (S : SpectralData C) (j : Fin n) :
    0 ≤ S.lam j := by
  have hv : S.v j ⬝ᵥ S.v j = 1 := by
    simpa [dotProduct, SpectralData.v, sq] using sum_col_sq_eq_one S.vIn S.hvIn j
  have h1 : S.v j ⬝ᵥ (C.Sin *ᵥ S.v j) = S.lam j := by
    rw [eig_v, dotProduct_smul, hv, smul_eq_mul, mul_one]
  rw [← h1]
  have := C.psdIn.dotProduct_mulVec_nonneg (S.v j)
  simpa using this

/-! ## The lemma -/

/-- `lem:app-setup-decomposition`, part (i), snapshot `cr-2026-10-23`. Row identity
`𝒬_i(Δ) = ∑_j 𝒬_ij(Δ)`. Source statement (verbatim, `section.tex` l.173–182):

```
\begin{lemma}[Mode and row decomposition]\label{lem:app-setup-decomposition}
For every $\Delta\in\R^{\Nout\times\Nin}$,
\begin{equation}\label{eqn:app-setup-decomposition}
\CMscr Q_i(\Delta)=\sum_{j=1}^{\Nin}\CMscr Q_{ij}(\Delta),\qquad
\tfrac12\norm{\Delta}_\Sigma^2=\tfrac12\sum_{i,j}\mu_i\lambda_j\,\CMscr Q_{ij}(\Delta),
\end{equation}
and if $\Sigmain=\Id_{\Nin}$ then $\frac12\norm{\Delta}_\Sigma^2=\frac12\sum_i\mu_i\CMscr Q_i(\Delta)$.
Moreover $\norm{\Delta}_\Sigma=0$ if and only if $u_i^\T\Delta v_j=0$ for every
pair $(i,j)$ with $\mu_i\lambda_j>0$.
\end{lemma}
```
-/
theorem lem_app_setup_decomposition_i {m n : ℕ} {C : Covariances m n} (S : SpectralData C)
    (Δ : Mat m n) (i : Fin m) :
    rowQ S Δ i = ∑ j, modeQ S Δ i j := by
  have hx : ∀ j : Fin n, (∑ a, S.vIn a j * (Δᵀ *ᵥ S.u i) a) = S.u i ⬝ᵥ (Δ *ᵥ S.v j) := by
    intro j
    simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, SpectralData.u, SpectralData.v,
      Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => by ring
  have h := sum_proj_mul_eq_dot S.vIn S.hvIn (Δᵀ *ᵥ S.u i) (Δᵀ *ᵥ S.u i)
  simp only [hx] at h
  simp only [rowQ, modeQ, sq]
  simp only [dotProduct] at h
  exact h.symm

/-- `lem:app-setup-decomposition`, part (ii), snapshot `cr-2026-10-23`. Risk identity
`½‖Δ‖_Σ² = ½ ∑_{i,j} μ_i λ_j 𝒬_ij(Δ)`. Source statement (verbatim, `section.tex` l.173–182):

```
\begin{lemma}[Mode and row decomposition]\label{lem:app-setup-decomposition}
For every $\Delta\in\R^{\Nout\times\Nin}$,
\begin{equation}\label{eqn:app-setup-decomposition}
\CMscr Q_i(\Delta)=\sum_{j=1}^{\Nin}\CMscr Q_{ij}(\Delta),\qquad
\tfrac12\norm{\Delta}_\Sigma^2=\tfrac12\sum_{i,j}\mu_i\lambda_j\,\CMscr Q_{ij}(\Delta),
\end{equation}
and if $\Sigmain=\Id_{\Nin}$ then $\frac12\norm{\Delta}_\Sigma^2=\frac12\sum_i\mu_i\CMscr Q_i(\Delta)$.
Moreover $\norm{\Delta}_\Sigma=0$ if and only if $u_i^\T\Delta v_j=0$ for every
pair $(i,j)$ with $\mu_i\lambda_j>0$.
\end{lemma}
```
-/
theorem lem_app_setup_decomposition_ii {m n : ℕ} {C : Covariances m n} (S : SpectralData C)
    (Δ : Mat m n) :
    (1 / 2) * pairSigma C Δ Δ = (1 / 2) * ∑ i, ∑ j, S.μ i * S.lam j * modeQ S Δ i j := by
  rw [pairSigma_eq_sum S Δ Δ]
  congr 1
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [modeQ, sq]

/-- `lem:app-setup-decomposition`, part (iii), snapshot `cr-2026-10-23`. If `Σ_in = Id` then
`½‖Δ‖_Σ² = ½ ∑_i μ_i 𝒬_i(Δ)`. Source statement (verbatim, `section.tex` l.173–182):

```
\begin{lemma}[Mode and row decomposition]\label{lem:app-setup-decomposition}
For every $\Delta\in\R^{\Nout\times\Nin}$,
\begin{equation}\label{eqn:app-setup-decomposition}
\CMscr Q_i(\Delta)=\sum_{j=1}^{\Nin}\CMscr Q_{ij}(\Delta),\qquad
\tfrac12\norm{\Delta}_\Sigma^2=\tfrac12\sum_{i,j}\mu_i\lambda_j\,\CMscr Q_{ij}(\Delta),
\end{equation}
and if $\Sigmain=\Id_{\Nin}$ then $\frac12\norm{\Delta}_\Sigma^2=\frac12\sum_i\mu_i\CMscr Q_i(\Delta)$.
Moreover $\norm{\Delta}_\Sigma=0$ if and only if $u_i^\T\Delta v_j=0$ for every
pair $(i,j)$ with $\mu_i\lambda_j>0$.
\end{lemma}
```
-/
theorem lem_app_setup_decomposition_iii {m n : ℕ} {C : Covariances m n} (S : SpectralData C)
    (hSin : C.Sin = 1) (Δ : Mat m n) :
    (1 / 2) * pairSigma C Δ Δ = (1 / 2) * ∑ i, S.μ i * rowQ S Δ i := by
  have hlam : ∀ j, S.lam j = 1 := by
    intro j
    have h := eig_v S j
    rw [hSin, Matrix.one_mulVec] at h
    have hn := sum_col_sq_eq_one S.vIn S.hvIn j
    have hvv : S.v j ⬝ᵥ S.v j = 1 := by
      simpa [dotProduct, SpectralData.v, sq] using hn
    have h2 := congrArg (fun w => S.v j ⬝ᵥ w) h
    simp only [dotProduct_smul, smul_eq_mul] at h2
    rw [hvv] at h2
    linarith
  rw [lem_app_setup_decomposition_ii S Δ]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [lem_app_setup_decomposition_i S Δ i, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hlam j, mul_one]

/-- `lem:app-setup-decomposition`, part (iv), snapshot `cr-2026-10-23`. Zero-norm criterion:
`‖Δ‖_Σ = 0` (written `√(pairSigma C Δ Δ) = 0`) iff `u_iᵀ Δ v_j = 0` for every pair with
`μ_i λ_j > 0`. Source statement (verbatim, `section.tex` l.173–182):

```
\begin{lemma}[Mode and row decomposition]\label{lem:app-setup-decomposition}
For every $\Delta\in\R^{\Nout\times\Nin}$,
\begin{equation}\label{eqn:app-setup-decomposition}
\CMscr Q_i(\Delta)=\sum_{j=1}^{\Nin}\CMscr Q_{ij}(\Delta),\qquad
\tfrac12\norm{\Delta}_\Sigma^2=\tfrac12\sum_{i,j}\mu_i\lambda_j\,\CMscr Q_{ij}(\Delta),
\end{equation}
and if $\Sigmain=\Id_{\Nin}$ then $\frac12\norm{\Delta}_\Sigma^2=\frac12\sum_i\mu_i\CMscr Q_i(\Delta)$.
Moreover $\norm{\Delta}_\Sigma=0$ if and only if $u_i^\T\Delta v_j=0$ for every
pair $(i,j)$ with $\mu_i\lambda_j>0$.
\end{lemma}
```
-/
theorem lem_app_setup_decomposition_iv {m n : ℕ} {C : Covariances m n} (S : SpectralData C)
    (Δ : Mat m n) :
    Real.sqrt (pairSigma C Δ Δ) = 0
      ↔ ∀ i j, 0 < S.μ i * S.lam j → S.u i ⬝ᵥ (Δ *ᵥ S.v j) = 0 := by
  have hnn : ∀ i j, 0 ≤ S.μ i * S.lam j :=
    fun i j => mul_nonneg (μ_nonneg S i) (lam_nonneg S j)
  have hterm : ∀ i j, 0 ≤ S.μ i * S.lam j * ((S.u i ⬝ᵥ (Δ *ᵥ S.v j)) * (S.u i ⬝ᵥ (Δ *ᵥ S.v j))) :=
    fun i j => mul_nonneg (hnn i j) (mul_self_nonneg _)
  rw [Real.sqrt_eq_zero', pairSigma_eq_sum S Δ Δ]
  constructor
  · intro h i j hpos
    have hz : ∑ i, ∑ j, S.μ i * S.lam j * ((S.u i ⬝ᵥ (Δ *ᵥ S.v j)) * (S.u i ⬝ᵥ (Δ *ᵥ S.v j)))
        = 0 :=
      le_antisymm h (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => hterm i j)
    have hi := (Finset.sum_eq_zero_iff_of_nonneg
      (fun i _ => Finset.sum_nonneg fun j _ => hterm i j)).mp hz i (Finset.mem_univ _)
    have hij := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hterm i j)).mp hi j
      (Finset.mem_univ _)
    rcases mul_eq_zero.mp hij with h0 | h0
    · exact absurd h0 hpos.ne'
    · exact mul_self_eq_zero.mp h0
  · intro h
    refine le_of_eq (Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_)
    by_cases hpos : 0 < S.μ i * S.lam j
    · rw [h i j hpos]
      ring
    · have h0 : S.μ i * S.lam j = 0 := le_antisymm (not_lt.mp hpos) (hnn i j)
      rw [h0]
      ring

end Muon.Setup

end
