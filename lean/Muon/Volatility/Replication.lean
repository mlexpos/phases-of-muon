import Muon.Volatility.Defs
import Muon.DetEquiv.Branch
import Muon.Setup.Regime

/-!
# Appendix D, part 8: spectral replication

Work package L-D.8 (interface draft). Snapshot `cr-2026-10-23`. Source of record:
`sections/04-volatility/section.tex`: `def:app-vol-replication` (l.642–652) and the paragraph after
it (l.654–661), whose claims are the helper statements `def_app_vol_replication_i`–`_viii`.
Card: `sections/04-volatility/CARD.md` §2, §3, §5 (row L-D.8), §6 (R5, R24).

Index-type decision (card §8 question on index types; cited as "§8 Q2" in §2 of the card):
the Kronecker layer `repKron` is defined for an arbitrary index type `ι`, with the replicated index
`ι × Fin N` as in the paper's `Σ ⊗ Id_N`. The Fin-indexed objects of the project (`Covariances`,
`SpectralData`, `FrozenParams`) are reached by one reindexing along `replIdx : Fin m × Fin N ≃ Fin (N * m)`,
so the replicated dimensions are `N * m`, `N * n`, `N * B`, as in the paper.

Encoding decisions:
* Replicated covariances `replCov C N` are a real `Covariances` structure (PSD from
  `Matrix.PosSemidef.kronecker`), so `nuOut`, `nuIn`, `SizeFin`, `FrozenParams` apply to them directly.
* The replicated eigenbases are the columns of `replMat S.uOut N` and `replMat S.vIn N`, where
  `S : SpectralData C` is the base eigenbasis (`Muon.Setup.SpectralData`), not a new one.
* The state `Â^(N)` of the paper ("the replicated eigenbases", R5 in the card) is fixed as a rank-`r_N`
  partial isometry: the replicated eigenvector of output index `k` is paired with the replicated
  eigenvector of input index `k` (same index, both in `Fin (N * m)` resp. `Fin (N * n)` order), for
  the first `r_N = min(N m, N n)` indices. Scaling `r_N^{-1/2}` gives unit Frobenius norm and operator norm
  `r_N^{-1/2}`. This is one admissible choice of the paper's unspecified enumeration.
* `def_app_vol_replication` returns a `FrozenParams` (the replicated frozen-state parameters). Its
  unit-Frobenius-norm field `hA` is an explicit argument, discharged by the theorem
  `def_app_vol_replication_vi`; the definition is therefore sorry-free and the proof obligation is
  visible at every use.
* The regime of the replicated states (`assum:app-setup-regime`) is stated as the existence of a
  `SetupRegime` along `N = k + 1` (`def_app_vol_replication_regime`, part (ix)), with the base `γ⋆`, `C_Σ`,
  `β`, ridge interval; its proof fields carry the unit-norm (`_vi`) and diffuseness (`_viii`) conditions.

Reused, not redefined: `Muon.Covariances`, `Muon.Setup.FrozenParams`, `Muon.Setup.SpectralData`
(`Muon.Setup.Basic`), `Muon.nuOut`, `Muon.nuIn`, `Muon.fro`, `Muon.opNorm` (`Muon.Foundations.Conventions`),
`Muon.Volatility.SizeFin` (`Muon.Volatility.Defs`), `Muon.DetEquiv.branchSol` (`Muon.DetEquiv.Branch`).
-/

noncomputable section

open scoped Matrix MatrixOrder
open MeasureTheory Filter Topology
open Muon Muon.Setup

namespace Muon.Volatility

variable {m n B : ℕ}

/-! ## Index layer -/

/-- Kronecker replication `S ⊗ Id_N` on an arbitrary index type `ι`, indexed by `ι × Fin N`
(the paper's `Σ ⊗ Id_N`, `def:app-vol-replication`). -/
def repKron {ι : Type*} [Fintype ι] (S : Matrix ι ι ℝ) (N : ℕ) :
    Matrix (ι × Fin N) (ι × Fin N) ℝ :=
  Matrix.kronecker S (1 : Matrix (Fin N) (Fin N) ℝ)

/-- Reindexing equivalence `Fin m × Fin N ≃ Fin (N * m)`: the replicated index as a `Fin`-type with
the dimension `N * m` of the replicated covariance. -/
def replIdx (m N : ℕ) : Fin m × Fin N ≃ Fin (N * m) :=
  finProdFinEquiv.trans (finCongr (Nat.mul_comm m N))

/-- The `Fin`-indexed replicated matrix `S ⊗ Id_N` of size `N * m`. For a test matrix `F` that is
diagonal in the output eigenbasis, `replMat F N` is the replicated test matrix `F ⊗ Id_N` of the
paper. -/
def replMat {m : ℕ} (S : Matrix (Fin m) (Fin m) ℝ) (N : ℕ) :
    Matrix (Fin (N * m)) (Fin (N * m)) ℝ :=
  (repKron S N).submatrix (replIdx m N).symm (replIdx m N).symm

/-! ## The replicated model -/

/-- Replicated covariances `(Σ_out ⊗ Id_N, Σ_in ⊗ Id_N)` as a `Covariances` structure of size
`(N * m, N * n)`. -/
def replCov {m n : ℕ} (C : Covariances m n) (N : ℕ) : Covariances (N * m) (N * n) where
  Sout := replMat C.Sout N
  Sin := replMat C.Sin N
  psdOut := (C.psdOut.kronecker Matrix.PosSemidef.one).submatrix (replIdx m N).symm
  psdIn := (C.psdIn.kronecker Matrix.PosSemidef.one).submatrix (replIdx n N).symm

/-- Replicated eigenbasis selector: the `(a, b)` entry is `1` exactly when `a = b < r_N`,
`r_N = min(N m, N n)`. It pairs the replicated output index `k` with the input index `k`. -/
def replSel (m n N : ℕ) : Matrix (Fin (N * m)) (Fin (N * n)) ℝ :=
  Matrix.of fun a b => if (a : ℕ) = (b : ℕ) ∧ (a : ℕ) < min (N * m) (N * n) then 1 else 0

/-- Normalized replicated state `Â^(N) = r_N^{-1/2} ∑_{k=0}^{r_N - 1} (u_k ⊗ e_k)(v_k ⊗ e_k)ᵀ` in the
replicated eigenbases (`replMat S.uOut N`, `replMat S.vIn N`), `r_N = min(N m, N n)`. -/
def replState {m n : ℕ} (C : Covariances m n) (S : SpectralData C) (N : ℕ) :
    Mat (N * m) (N * n) :=
  ((Real.sqrt ((min (N * m) (N * n) : ℕ) : ℝ))⁻¹) •
    (replMat S.uOut N * replSel m n N * (replMat S.vIn N)ᵀ)

/-- `def:app-vol-replication`, snapshot `cr-2026-10-23`. Declaration of record: the replicated
frozen-state parameters `(N Nout, N Nin, NB, Σout ⊗ Id_N, Σin ⊗ Id_N)` with state `Â^(N)`
(`replCov`, `replState`), momentum `β` unchanged. The explicit argument `hA` is the unit
Frobenius norm of the state (`def_app_vol_replication_vi`). The definition, verbatim from `section.tex`:
```latex
\begin{definition}[Spectral replication]\label{def:app-vol-replication}
Fix a finite dimension $(\Nout,\Nin,B,\Sigmaout,\Sigmain)$ and an integer
$N\ge1$. The $N$-fold replication is
$(N\Nout,N\Nin,NB,\Sigmaout\tensor\Id_N,\Sigmain\tensor\Id_N)$, with the
eigenbases $(u_i\tensor e_k)$ and $(v_j\tensor e_k)$. A matrix $F$ that is
diagonal in $(u_i)$, respectively $G$ diagonal in $(v_j)$, is replicated as
$F\tensor\Id_N$, respectively $G\tensor\Id_N$. When an actual model is
needed along a replication, the state is
$\Ahat^{(N)}\defeq r_N^{-1/2}\sum_{k\le r_N}e_k\tensor e_k'$ with
$r_N=\min(N\Nout,N\Nin)$, in the replicated eigenbases.
\end{definition}
```
-/
def def_app_vol_replication (F : FrozenParams m n B) (S : SpectralData F.C) (N : ℕ) (hN : 0 < N)
    (hA : fro (replState F.C S N) = 1) : FrozenParams (N * m) (N * n) (N * B) where
  C := replCov F.C N
  A := replState F.C S N
  hA := hA
  β := F.β
  hβ := F.hβ
  hB := Nat.mul_pos hN F.hB

/-! ## Invariance, sizes and regime of the replications (helper statements)

Paragraph after `def:app-vol-replication` (`section.tex` l.654–661), verbatim:
```latex
The spectral measures \cref{eqn:app-setup-spectral-measures} of a replication
are those of the base, since each eigenvalue is repeated $N$ times and
normalized by $NB$. Hence the branch of \cref{def:app-de-branch} and every
deterministic quantity of this section built from it is the same at every
order $N$. The replications satisfy the size conditions with the same constants and with
$N\Nout/(NB)$ and $N\Nin/(NB)$ constant; the state $\Ahat^{(N)}$ has unit
Frobenius norm and operator norm $r_N^{-1/2}\to0$, so the replications with
this state satisfy \cref{assum:app-setup-regime}.
```
-/

/-- `(A * B) ⊗ Id_N = (A ⊗ Id_N) * (B ⊗ Id_N)` (the Kronecker product with the identity is
multiplicative; `erw` is needed to see through the `kronecker` / `kroneckerMap` unfolding). -/
private lemma kron_one_mul_aux {k N : ℕ} (A B : Matrix (Fin k) (Fin k) ℝ) :
    Matrix.kronecker (A * B) (1 : Matrix (Fin N) (Fin N) ℝ) =
      Matrix.kronecker A 1 * Matrix.kronecker B 1 := by
  erw [← Matrix.mul_kronecker_mul, mul_one]
  rfl

/-- Characteristic polynomial of the Kronecker replication: `χ(S ⊗ Id_N) = χ(S)^N` for Hermitian `S`.
Proof by the spectral theorem: `S = V D Vᵀ` with `V` orthogonal, and `D ⊗ Id_N` is diagonal. -/
private lemma repKron_charpoly_aux {k : ℕ} (S : Matrix (Fin k) (Fin k) ℝ) (hS : S.IsHermitian)
    (N : ℕ) :
    (Matrix.kronecker S (1 : Matrix (Fin N) (Fin N) ℝ)).charpoly = S.charpoly ^ N := by
  have hsp := hS.spectral_theorem
  simp only [Unitary.conjStarAlgAut_apply] at hsp
  have hUU : star ((hS.eigenvectorUnitary : Matrix.unitaryGroup (Fin k) ℝ) : Matrix (Fin k) (Fin k) ℝ)
      * ((hS.eigenvectorUnitary : Matrix.unitaryGroup (Fin k) ℝ) : Matrix (Fin k) (Fin k) ℝ) = 1 :=
    Matrix.mem_unitaryGroup_iff'.1 hS.eigenvectorUnitary.2
  have hK : Matrix.kronecker S (1 : Matrix (Fin N) (Fin N) ℝ) =
      Matrix.kronecker ((hS.eigenvectorUnitary : Matrix.unitaryGroup (Fin k) ℝ) : Matrix (Fin k) (Fin k) ℝ) 1 *
        (Matrix.kronecker (Matrix.diagonal (RCLike.ofReal ∘ hS.eigenvalues)) 1 *
          Matrix.kronecker (star ((hS.eigenvectorUnitary : Matrix.unitaryGroup (Fin k) ℝ) : Matrix (Fin k) (Fin k) ℝ)) 1) := by
    conv_lhs => rw [hsp]
    rw [kron_one_mul_aux, kron_one_mul_aux, mul_assoc]
  have hW : Matrix.kronecker (star ((hS.eigenvectorUnitary : Matrix.unitaryGroup (Fin k) ℝ) : Matrix (Fin k) (Fin k) ℝ))
        (1 : Matrix (Fin N) (Fin N) ℝ) *
      Matrix.kronecker ((hS.eigenvectorUnitary : Matrix.unitaryGroup (Fin k) ℝ) : Matrix (Fin k) (Fin k) ℝ)
        (1 : Matrix (Fin N) (Fin N) ℝ) = 1 := by
    rw [← kron_one_mul_aux, hUU]
    exact Matrix.one_kronecker_one
  have hD : Matrix.kronecker (Matrix.diagonal (RCLike.ofReal ∘ hS.eigenvalues)) (1 : Matrix (Fin N) (Fin N) ℝ) =
      Matrix.diagonal (fun p : Fin k × Fin N => (RCLike.ofReal ∘ hS.eigenvalues) p.1) := by
    rw [← Matrix.diagonal_one]
    refine (Matrix.diagonal_kronecker_diagonal _ _).trans ?_
    congr 1
    funext p
    simp
  rw [hK, Matrix.charpoly_mul_comm, mul_assoc, hW, mul_one, hD, Matrix.charpoly_diagonal,
    Fintype.prod_prod_type, hS.charpoly_eq, ← Finset.prod_pow]
  simp [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- The characteristic polynomial of the replicated matrix `replMat S N` is `χ(S)^N`. -/
private lemma replMat_charpoly_aux {k : ℕ} (S : Matrix (Fin k) (Fin k) ℝ) (hS : S.IsHermitian)
    (N : ℕ) : (replMat S N).charpoly = S.charpoly ^ N := by
  unfold replMat
  rw [← Matrix.reindex_apply, Matrix.charpoly_reindex]
  exact repKron_charpoly_aux S hS N

/-- Spectral multiset of a replication: if `χ(T) = χ(S)^N`, the Dirac sum of the eigenvalues of `T`
is `N` times the Dirac sum of the eigenvalues of `S`. -/
private lemma repl_eig_sum_aux {k N : ℕ} (S : Matrix (Fin k) (Fin k) ℝ) (hS : S.IsHermitian)
    (T : Matrix (Fin (N * k)) (Fin (N * k)) ℝ) (hT : T.IsHermitian)
    (hTc : T.charpoly = S.charpoly ^ N) :
    ∑ i, Measure.dirac (hT.eigenvalues i) = N • ∑ j, Measure.dirac (hS.eigenvalues j) := by
  have hr : Multiset.map hT.eigenvalues Finset.univ.val =
      N • Multiset.map hS.eigenvalues Finset.univ.val := by
    have h := congrArg Polynomial.roots hTc
    rw [Polynomial.roots_pow, hT.roots_charpoly_eq_eigenvalues, hS.roots_charpoly_eq_eigenvalues] at h
    simpa [Function.comp_def] using h
  have key : ∀ {K : ℕ} (g : Fin K → ℝ),
      ∑ i, Measure.dirac (g i) = (Multiset.map Measure.dirac (Multiset.map g Finset.univ.val)).sum := by
    intro K g
    simp [Finset.sum_eq_multiset_sum, Function.comp_def]
  rw [key, key, hr, Multiset.map_nsmul, Multiset.sum_nsmul]

/-- Scalar cancellation `(N B)⁻¹ N = B⁻¹` in `ℝ≥0∞`. -/
private lemma enn_scale_repl_aux (N B : ℕ) (hN : 0 < N) :
    ((N * B : ℕ) : ENNReal)⁻¹ * (N : ENNReal) = (B : ENNReal)⁻¹ := by
  rw [Nat.cast_mul, ENNReal.mul_inv (Or.inl (by exact_mod_cast hN.ne'))
    (Or.inl (ENNReal.natCast_ne_top N)), mul_comm, ← mul_assoc,
    ENNReal.mul_inv_cancel (by exact_mod_cast hN.ne') (ENNReal.natCast_ne_top N), one_mul]

/-- `def:app-vol-replication` (i), snapshot `cr-2026-10-23`. Output spectral measure is that of the base: `ν_out` of the replication at dimension `N B`
equals `ν_out` of the base at `B`, since each eigenvalue is repeated `N` times and normalized by `NB`.
Sorried: proof card P1. -/
theorem def_app_vol_replication_i (C : Covariances m n) (hB : 0 < B) (N : ℕ) (hN : 0 < N) :
    Muon.nuOut (replCov C N) (N * B) = Muon.nuOut C B := by
  unfold Muon.nuOut
  rw [repl_eig_sum_aux C.Sout C.psdOut.isHermitian (replCov C N).Sout
    (replCov C N).psdOut.isHermitian (replMat_charpoly_aux C.Sout C.psdOut.isHermitian N),
    ← Nat.cast_smul_eq_nsmul ENNReal, smul_smul, enn_scale_repl_aux N B hN]

/-- `def:app-vol-replication` (ii), snapshot `cr-2026-10-23`. Input spectral measure is that of the base (as `_i`, for `ν_in`). Sorried: proof card P1. -/
theorem def_app_vol_replication_ii (C : Covariances m n) (hB : 0 < B) (N : ℕ) (hN : 0 < N) :
    Muon.nuIn (replCov C N) (N * B) = Muon.nuIn C B := by
  unfold Muon.nuIn
  rw [repl_eig_sum_aux C.Sin C.psdIn.isHermitian (replCov C N).Sin
    (replCov C N).psdIn.isHermitian (replMat_charpoly_aux C.Sin C.psdIn.isHermitian N),
    ← Nat.cast_smul_eq_nsmul ENNReal, smul_smul, enn_scale_repl_aux N B hN]

/-- `def:app-vol-replication` (iii), snapshot `cr-2026-10-23`. The branch of `def:app-de-branch` is the same at every order `N`: equal spectral measures give
equal solutions `branchSol`. Sorried: proof card P1 (rewrite the coercions in `IsBranchSol`). -/
theorem def_app_vol_replication_iii (F : ℝ → ℝ) (ν ν' νN ν'N : FiniteMeasure ℝ) (s : ℝ)
    (h1 : (νN : Measure ℝ) = (ν : Measure ℝ)) (h2 : (ν'N : Measure ℝ) = (ν' : Measure ℝ)) :
    Muon.DetEquiv.branchSol F νN ν'N s = Muon.DetEquiv.branchSol F ν ν' s := by
  have hI : Muon.DetEquiv.IsBranchSol F νN ν'N s = Muon.DetEquiv.IsBranchSol F ν ν' s := by
    funext x
    obtain ⟨σ, σ', a, c⟩ := x
    simp only [Muon.DetEquiv.IsBranchSol, h1, h2]
  unfold Muon.DetEquiv.branchSol
  rw [hI]

/-- Column bound: `∑ᵢ (S v)ᵢ² ≤ ‖S‖² ∑ⱼ vⱼ²`, from `Matrix.l2_opNorm_mulVec`. -/
private lemma mulVec_sq_le_aux {m : ℕ} (S : Matrix (Fin m) (Fin m) ℝ) (v : Fin m → ℝ) :
    ∑ i, (∑ j, S i j * v j) ^ 2 ≤ opNorm S ^ 2 * ∑ j, v j ^ 2 := by
  rw [opNorm_eq_norm]
  have h := Matrix.l2_opNorm_mulVec S (WithLp.toLp 2 v)
  have hsq := pow_le_pow_left₀ (norm_nonneg _) h 2
  rw [mul_pow, EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq] at hsq
  simpa [Matrix.mulVec, dotProduct] using hsq

/-- Sum-of-squares bound for the Kronecker replication: `∑ₐ (S ⊗ Id_N x)ₐ² ≤ opNorm S² ∑ᵦ xᵦ²`. -/
private lemma replMat_mulVec_sq_aux {m N : ℕ} (S : Matrix (Fin m) (Fin m) ℝ)
    (x : Fin (N * m) → ℝ) :
    ∑ a, (∑ b, replMat S N a b * x b) ^ 2 ≤ opNorm S ^ 2 * ∑ b, x b ^ 2 := by
  set e := replIdx m N with he
  have hL : ∀ a : Fin (N * m), ∑ b, replMat S N a b * x b =
      ∑ j : Fin m, S (e.symm a).1 j * x (e (j, (e.symm a).2)) := by
    intro a
    rw [← Equiv.sum_comp e (fun b => replMat S N a b * x b)]
    simp [replMat, repKron, Matrix.one_apply, Fintype.sum_prod_type, he, Equiv.symm_apply_apply]
  calc ∑ a, (∑ b, replMat S N a b * x b) ^ 2
      = ∑ p : Fin m × Fin N, (∑ j : Fin m, S p.1 j * x (e (j, p.2))) ^ 2 := by
        rw [← Equiv.sum_comp e (fun a => (∑ b, replMat S N a b * x b) ^ 2)]
        refine Finset.sum_congr rfl fun p _ => ?_
        rw [hL, Equiv.symm_apply_apply]
    _ = ∑ k : Fin N, ∑ i : Fin m, (∑ j : Fin m, S i j * x (e (j, k))) ^ 2 := by
        rw [Fintype.sum_prod_type_right]
    _ ≤ ∑ k : Fin N, opNorm S ^ 2 * ∑ j : Fin m, x (e (j, k)) ^ 2 :=
        Finset.sum_le_sum fun k _ => mulVec_sq_le_aux S (fun j => x (e (j, k)))
    _ = opNorm S ^ 2 * ∑ b, x b ^ 2 := by
        rw [← Finset.mul_sum, ← Equiv.sum_comp e (fun b => x b ^ 2), Fintype.sum_prod_type_right]

/-- Operator norm of the Kronecker replication: `‖S ⊗ Id_N‖ ≤ ‖S‖` (reindexing is an isometry). -/
private lemma replMat_opNorm_le_aux {m N : ℕ} (S : Matrix (Fin m) (Fin m) ℝ) :
    opNorm (replMat S N) ≤ opNorm S := by
  have hM : 0 ≤ opNorm S := by unfold opNorm; exact norm_nonneg _
  rw [opNorm_eq_norm (replMat S N), ← Matrix.l2_opNorm_toEuclideanCLM]
  refine ContinuousLinearMap.opNorm_le_bound _ hM fun x => ?_
  have hsq := replMat_mulVec_sq_aux S (WithLp.ofLp x)
  have hK : ‖Matrix.toEuclideanCLM (n := Fin (N * m)) (𝕜 := ℝ) (replMat S N) x‖ ^ 2 =
      ∑ a, (∑ b, replMat S N a b * WithLp.ofLp x b) ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    rfl
  have hx : ‖x‖ ^ 2 = ∑ b, WithLp.ofLp x b ^ 2 := EuclideanSpace.real_norm_sq_eq x
  have h2 : ‖Matrix.toEuclideanCLM (n := Fin (N * m)) (𝕜 := ℝ) (replMat S N) x‖ ^ 2 ≤ (opNorm S * ‖x‖) ^ 2 := by
    rw [mul_pow, hK, hx]; exact hsq
  nlinarith [norm_nonneg (Matrix.toEuclideanCLM (n := Fin (N * m)) (𝕜 := ℝ) (replMat S N) x), mul_nonneg hM (norm_nonneg x)]

/-- `def:app-vol-replication` (iv), snapshot `cr-2026-10-23`. Size conditions pass to the replications with the same constants: `SizeFin C B γ⋆ C_Σ` implies
`SizeFin (replCov C N) (N B) γ⋆ C_Σ`, since `‖S ⊗ Id_N‖ = ‖S‖` and `max(N m, N n) = N max(m, n)`.
Sorried: proof card P2. -/
theorem def_app_vol_replication_iv (C : Covariances m n) (γstar CSig : ℝ)
    (hS : SizeFin C B γstar CSig) (N : ℕ) (hN : 0 < N) :
    SizeFin (replCov C N) (N * B) γstar CSig := by
  unfold SizeFin at hS ⊢
  obtain ⟨h1, h2, h3⟩ := hS
  have hmax : max (N * m) (N * n) = N * max m n := by
    rcases le_total m n with h | h
    · rw [max_eq_right h, max_eq_right (Nat.mul_le_mul_left N h)]
    · rw [max_eq_left h, max_eq_left (Nat.mul_le_mul_left N h)]
  refine ⟨?_, ?_, ?_⟩
  · rw [hmax, Nat.cast_mul, Nat.cast_mul]
    have hN' : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    nlinarith [mul_le_mul_of_nonneg_left h1 hN']
  · exact (replMat_opNorm_le_aux C.Sout).trans h2
  · exact (replMat_opNorm_le_aux C.Sin).trans h3

/-- `def:app-vol-replication` (v), snapshot `cr-2026-10-23`. Aspect ratios are unchanged: `N m / (N B) = m / B` and `N n / (N B) = n / B` for `N, B > 0`.
Sorried: proof card P2. -/
theorem def_app_vol_replication_v (N : ℕ) (hN : 0 < N) (hB : 0 < B) :
    ((N * m : ℕ) : ℝ) / ((N * B : ℕ) : ℝ) = (m : ℝ) / (B : ℝ) ∧
      ((N * n : ℕ) : ℝ) / ((N * B : ℕ) : ℝ) = (n : ℝ) / (B : ℝ) := by
  have hN' : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  constructor
  · rw [Nat.cast_mul, Nat.cast_mul, mul_div_mul_left _ _ hN']
  · rw [Nat.cast_mul, Nat.cast_mul, mul_div_mul_left _ _ hN']

/-- Sum of squares as a trace: `∑ᵢⱼ Xᵢⱼ² = tr(Xᵀ X)`. -/
private lemma vi_fro_sq_eq_trace {a b : ℕ} (X : Matrix (Fin a) (Fin b) ℝ) :
    ∑ i, ∑ j, X i j * X i j = Matrix.trace (Xᵀ * X) := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply]
  exact Finset.sum_comm

/-- Left multiplication by an orthogonal matrix preserves the sum of squares. -/
private lemma vi_fro_sq_mul_orth_left {a b : ℕ} (U : Matrix (Fin a) (Fin a) ℝ) (hU : Uᵀ * U = 1)
    (X : Matrix (Fin a) (Fin b) ℝ) :
    ∑ i, ∑ j, (U * X) i j * (U * X) i j = ∑ i, ∑ j, X i j * X i j := by
  rw [vi_fro_sq_eq_trace, vi_fro_sq_eq_trace, Matrix.transpose_mul, Matrix.mul_assoc Xᵀ Uᵀ,
    ← Matrix.mul_assoc Uᵀ U X, hU, Matrix.one_mul]

/-- Right multiplication by `W` with `W Wᵀ = 1` preserves the sum of squares. -/
private lemma vi_fro_sq_mul_orth_right {a b : ℕ} (Y : Matrix (Fin a) (Fin b) ℝ)
    (W : Matrix (Fin b) (Fin b) ℝ) (hW : W * Wᵀ = 1) :
    ∑ i, ∑ j, (Y * W) i j * (Y * W) i j = ∑ i, ∑ j, Y i j * Y i j := by
  rw [vi_fro_sq_eq_trace, vi_fro_sq_eq_trace]
  have h1 : (Y * W)ᵀ * (Y * W) = Wᵀ * (Yᵀ * Y) * W := by
    simp only [Matrix.transpose_mul, Matrix.mul_assoc]
  rw [h1, Matrix.trace_mul_comm (Wᵀ * (Yᵀ * Y)) W, ← Matrix.mul_assoc W Wᵀ (Yᵀ * Y), hW,
    Matrix.one_mul]

/-- The replicated eigenbasis matrix is orthogonal: `(S ⊗ Id_N)ᵀ (S ⊗ Id_N) = 1` for `Sᵀ S = 1`. -/
private lemma vi_replMat_transpose_mul {m : ℕ} (S : Matrix (Fin m) (Fin m) ℝ) (hS : Sᵀ * S = 1)
    (N : ℕ) : (replMat S N)ᵀ * replMat S N = 1 := by
  unfold replMat
  rw [Matrix.transpose_submatrix, Matrix.submatrix_mul_equiv]
  have hK : (repKron S N)ᵀ * repKron S N = 1 := by
    unfold repKron
    have hT : (Matrix.kronecker S (1 : Matrix (Fin N) (Fin N) ℝ))ᵀ =
        Matrix.kronecker Sᵀ (1 : Matrix (Fin N) (Fin N) ℝ)ᵀ :=
      (Matrix.kroneckerMap_transpose _ _ _).symm
    rw [hT, Matrix.transpose_one]
    erw [← Matrix.mul_kronecker_mul]
    rw [hS, Matrix.mul_one, Matrix.one_kronecker_one]
  rw [hK, Matrix.submatrix_one_equiv]

/-- Inner count of the selector: for fixed `a`, `∑_{j<q} [a = j ∧ a < r] = [a < r ∧ a < q]`. -/
private lemma vi_sel_inner (r q a : ℕ) :
    ∑ j ∈ Finset.range q, (if a = j ∧ a < r then (1:ℝ) else 0) = if a < r ∧ a < q then 1 else 0 := by
  by_cases h : a < r
  · by_cases hq : a < q
    · simp [h, hq]
    · simp only [h, hq, and_false, ite_false, true_and, ite_eq_right_iff, not_false_eq_true]
      apply Finset.sum_eq_zero
      intro j hj
      rw [Finset.mem_range] at hj
      rw [if_neg]
      omega
  · simp [h]

/-- The selector `replSel` has squared Frobenius norm `min(p, q)`. -/
private lemma vi_sel_count (p q : ℕ) :
    ∑ i : Fin p, ∑ j : Fin q, (if (i:ℕ) = (j:ℕ) ∧ (i:ℕ) < min p q then (1:ℝ) else 0) *
      (if (i:ℕ) = (j:ℕ) ∧ (i:ℕ) < min p q then (1:ℝ) else 0) = ((min p q : ℕ) : ℝ) := by
  have hterm : ∀ (i : Fin p) (j : Fin q),
      (if (i:ℕ) = (j:ℕ) ∧ (i:ℕ) < min p q then (1:ℝ) else 0) *
        (if (i:ℕ) = (j:ℕ) ∧ (i:ℕ) < min p q then (1:ℝ) else 0) =
      (if (i:ℕ) = (j:ℕ) ∧ (i:ℕ) < min p q then (1:ℝ) else 0) := by
    intro i j
    split_ifs <;> norm_num
  simp only [hterm]
  have e1 : ∑ i : Fin p, ∑ j : Fin q, (if (i:ℕ) = (j:ℕ) ∧ (i:ℕ) < min p q then (1:ℝ) else 0) =
      ∑ i ∈ Finset.range p, ∑ j ∈ Finset.range q, (if i = j ∧ i < min p q then (1:ℝ) else 0) := by
    rw [← Fin.sum_univ_eq_sum_range (fun i => ∑ j ∈ Finset.range q,
      (if i = j ∧ i < min p q then (1:ℝ) else 0)) p]
    refine Finset.sum_congr rfl fun i _ => ?_
    exact Fin.sum_univ_eq_sum_range (fun j => (if (i:ℕ) = j ∧ (i:ℕ) < min p q then (1:ℝ) else 0)) q
  rw [e1]
  simp only [vi_sel_inner]
  rw [Finset.sum_boole]
  have hf : (Finset.range p).filter (fun i => i < min p q ∧ i < q) = Finset.range (min p q) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_range]
    constructor
    · exact fun h => h.2.1
    · intro h
      have h1 : min p q ≤ p := min_le_left p q
      have h2 : min p q ≤ q := min_le_right p q
      exact ⟨by omega, by omega⟩
  rw [hf, Finset.card_range]

/-- `def:app-vol-replication` (vi), snapshot `cr-2026-10-23`. Unit Frobenius norm of the replicated state `Â^(N)` (needed for `hA` of
`def_app_vol_replication`), for `m, n, N > 0`. Sorried: proof card P3. -/
theorem def_app_vol_replication_vi {m n : ℕ} (C : Covariances m n) (S : SpectralData C) (N : ℕ)
    (hm : 0 < m) (hn : 0 < n) (hN : 0 < N) :
    fro (replState C S N) = 1 := by
  have hU : (replMat S.uOut N)ᵀ * replMat S.uOut N = 1 :=
    vi_replMat_transpose_mul S.uOut S.huOut N
  have hW : (replMat S.vIn N)ᵀ * ((replMat S.vIn N)ᵀ)ᵀ = 1 := by
    rw [Matrix.transpose_transpose]
    exact vi_replMat_transpose_mul S.vIn S.hvIn N
  have hr : (0 : ℝ) < ((min (N * m) (N * n) : ℕ) : ℝ) :=
    Nat.cast_pos.mpr (lt_min (Nat.mul_pos hN hm) (Nat.mul_pos hN hn))
  have hX : ∑ i, ∑ j, (replMat S.uOut N * replSel m n N * (replMat S.vIn N)ᵀ) i j *
      (replMat S.uOut N * replSel m n N * (replMat S.vIn N)ᵀ) i j =
        ((min (N * m) (N * n) : ℕ) : ℝ) := by
    rw [vi_fro_sq_mul_orth_right (replMat S.uOut N * replSel m n N) ((replMat S.vIn N)ᵀ) hW,
      vi_fro_sq_mul_orth_left (replMat S.uOut N) hU (replSel m n N)]
    simp only [replSel, Matrix.of_apply]
    exact vi_sel_count (N * m) (N * n)
  unfold fro replState
  have key : ∑ i, ∑ j, ‖((Real.sqrt ((min (N * m) (N * n) : ℕ) : ℝ))⁻¹ •
      (replMat S.uOut N * replSel m n N * (replMat S.vIn N)ᵀ)) i j‖ ^ 2 =
      ((Real.sqrt ((min (N * m) (N * n) : ℕ) : ℝ))⁻¹) ^ 2 *
        ∑ i, ∑ j, (replMat S.uOut N * replSel m n N * (replMat S.vIn N)ᵀ) i j *
          (replMat S.uOut N * replSel m n N * (replMat S.vIn N)ᵀ) i j := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [Matrix.smul_apply, smul_eq_mul, Real.norm_eq_abs, sq_abs]
    ring
  rw [key, hX, inv_pow, Real.sq_sqrt hr.le, inv_mul_cancel₀ hr.ne', Real.sqrt_one]

open scoped Matrix.Norms.L2Operator in
/-- Left multiplication by an orthogonal matrix preserves the L2 operator norm. -/
private lemma vvii_norm_left_orth {a b : ℕ} (U : Matrix (Fin a) (Fin a) ℝ) (hU : Uᵀ * U = 1)
    (X : Matrix (Fin a) (Fin b) ℝ) : ‖U * X‖ = ‖X‖ := by
  have hUh : Uᴴ * U = 1 := by rw [Matrix.conjTranspose_eq_transpose_of_trivial]; exact hU
  have h : ‖U * X‖ * ‖U * X‖ = ‖X‖ * ‖X‖ := by
    rw [← Matrix.l2_opNorm_conjTranspose_mul_self, ← Matrix.l2_opNorm_conjTranspose_mul_self]
    congr 1
    rw [Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Uᴴ U X, hUh, Matrix.one_mul]
  exact (mul_self_inj (norm_nonneg _) (norm_nonneg _)).mp h

open scoped Matrix.Norms.L2Operator in
/-- Right multiplication by an orthogonal matrix preserves the L2 operator norm. -/
private lemma vvii_norm_right_orth {a b : ℕ} (X : Matrix (Fin a) (Fin b) ℝ)
    (W : Matrix (Fin b) (Fin b) ℝ) (hW : Wᵀ * W = 1) : ‖X * W‖ = ‖X‖ := by
  calc ‖X * W‖ = ‖(X * W)ᴴ‖ := (Matrix.l2_opNorm_conjTranspose _).symm
    _ = ‖Wᴴ * Xᴴ‖ := by rw [Matrix.conjTranspose_mul]
    _ = ‖Xᴴ‖ := by
      refine vvii_norm_left_orth Wᴴ ?_ Xᴴ
      rw [Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.transpose_transpose]
      exact mul_eq_one_comm.mp hW
    _ = ‖X‖ := Matrix.l2_opNorm_conjTranspose X

/-- Gram matrix of the replicated selector: `Pᵀ P = diag(1_{j < r})` for `r ≤ p`. -/
private lemma vvii_sel_gram {p q r : ℕ} (hrp : r ≤ p) :
    (Matrix.of fun (a : Fin p) (b : Fin q) => if (a:ℕ) = (b:ℕ) ∧ (a:ℕ) < r then (1:ℝ) else 0)ᵀ *
      (Matrix.of fun (a : Fin p) (b : Fin q) => if (a:ℕ) = (b:ℕ) ∧ (a:ℕ) < r then (1:ℝ) else 0)
      = Matrix.diagonal (fun j : Fin q => if (j:ℕ) < r then (1:ℝ) else 0) := by
  ext j k
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply, Matrix.diagonal_apply]
  by_cases hj : (j:ℕ) < r
  · have hjp : (j:ℕ) < p := lt_of_lt_of_le hj hrp
    rw [Finset.sum_eq_single (⟨j, hjp⟩ : Fin p)]
    · by_cases hjk : j = k
      · subst hjk; simp [hj]
      · have hne : (j:ℕ) ≠ (k:ℕ) := fun h => hjk (Fin.ext h)
        simp [hj, hjk, hne]
    · intro i _ hi
      by_cases h1 : (i:ℕ) = (j:ℕ) ∧ (i:ℕ) < r
      · exact absurd (Fin.ext h1.1) hi
      · simp [h1]
    · intro h; exact absurd (Finset.mem_univ _) h
  · rw [Finset.sum_eq_zero]
    · simp [hj]
    · intro i _
      have h1 : ¬((i:ℕ) = (j:ℕ) ∧ (i:ℕ) < r) := fun h => hj (h.1 ▸ h.2)
      simp [h1]

open scoped Matrix.Norms.L2Operator in
/-- The selector `replSel`-shaped matrix (`r ≤ p`, `r ≤ q`, `r > 0`) has operator norm `1`. -/
private lemma vvii_sel_norm {p q r : ℕ} (hrp : r ≤ p) (hrq : r ≤ q) (hr : 0 < r) :
    ‖(Matrix.of fun (a : Fin p) (b : Fin q) => if (a:ℕ) = (b:ℕ) ∧ (a:ℕ) < r then (1:ℝ) else 0)‖
      = 1 := by
  have hq0 : 0 < q := lt_of_lt_of_le hr hrq
  have hsq : ‖(Matrix.of fun (a : Fin p) (b : Fin q) => if (a:ℕ) = (b:ℕ) ∧ (a:ℕ) < r then (1:ℝ) else 0)‖
      * ‖(Matrix.of fun (a : Fin p) (b : Fin q) => if (a:ℕ) = (b:ℕ) ∧ (a:ℕ) < r then (1:ℝ) else 0)‖
      = 1 := by
    rw [← Matrix.l2_opNorm_conjTranspose_mul_self, Matrix.conjTranspose_eq_transpose_of_trivial,
      vvii_sel_gram hrp, Matrix.l2_opNorm_diagonal]
    apply le_antisymm
    · refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun j => ?_
      split_ifs <;> simp
    · have h := norm_le_pi_norm (fun j : Fin q => if (j:ℕ) < r then (1:ℝ) else 0) ⟨0, hq0⟩
      simpa [hr] using h
  rcases mul_self_eq_one_iff.mp hsq with h | h
  · exact h
  · linarith [norm_nonneg (Matrix.of fun (a : Fin p) (b : Fin q) =>
      if (a:ℕ) = (b:ℕ) ∧ (a:ℕ) < r then (1:ℝ) else 0)]

open scoped Matrix.Norms.L2Operator in
/-- `def:app-vol-replication` (vii), snapshot `cr-2026-10-23`. Operator norm of the replicated state: `‖Â^(N)‖ = r_N^{-1/2}` (partial isometry scaled by
`r_N^{-1/2}`). Sorried: proof card P4. -/
theorem def_app_vol_replication_vii {m n : ℕ} (C : Covariances m n) (S : SpectralData C) (N : ℕ) :
    opNorm (replState C S N) = (Real.sqrt ((min (N * m) (N * n) : ℕ) : ℝ))⁻¹ := by
  have hU : (replMat S.uOut N)ᵀ * replMat S.uOut N = 1 :=
    vi_replMat_transpose_mul S.uOut S.huOut N
  have hW : ((replMat S.vIn N)ᵀ)ᵀ * (replMat S.vIn N)ᵀ = 1 := by
    rw [Matrix.transpose_transpose]
    exact mul_eq_one_comm.mp (vi_replMat_transpose_mul S.vIn S.hvIn N)
  unfold replState
  rcases Nat.eq_zero_or_pos (min (N * m) (N * n)) with h0 | hpos
  · rw [h0]
    simp [opNorm_eq_norm]
  · rw [opNorm_eq_norm, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (inv_nonneg.2 (Real.sqrt_nonneg _))]
    rw [vvii_norm_right_orth _ _ hW, vvii_norm_left_orth _ hU]
    have hP := vvii_sel_norm (p := N * m) (q := N * n) (r := min (N * m) (N * n))
      (min_le_left _ _) (min_le_right _ _) hpos
    unfold replSel
    rw [hP, mul_one]

/-- `def:app-vol-replication` (viii), snapshot `cr-2026-10-23`. The normalized replicated state is spectrally diffuse: `‖Â^(N)‖ → 0` as `N → ∞`, for `m, n > 0`
(so `r_N → ∞`). Sorried: proof card P4. -/
theorem def_app_vol_replication_viii {m n : ℕ} (C : Covariances m n) (S : SpectralData C)
    (hm : 0 < m) (hn : 0 < n) :
    Tendsto (fun N : ℕ => opNorm (replState C S N)) atTop (𝓝 0) := by
  have h_le : ∀ N : ℕ, (N : ℝ) ≤ ((min (N * m) (N * n) : ℕ) : ℝ) := fun N => by
    exact_mod_cast le_min (Nat.le_mul_of_pos_right N hm) (Nat.le_mul_of_pos_right N hn)
  have hg : Tendsto (fun N : ℕ => ((min (N * m) (N * n) : ℕ) : ℝ)) atTop atTop :=
    tendsto_atTop_mono h_le tendsto_natCast_atTop_atTop
  have hlim : Tendsto (fun N : ℕ => (Real.sqrt ((min (N * m) (N * n) : ℕ) : ℝ))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp hg)
  exact Tendsto.congr (fun N => (def_app_vol_replication_vii C S N).symm) hlim

/-- `def:app-vol-replication` (ix), snapshot `cr-2026-10-23`. Declaration of record for the regime
clause of the remark (l.660–661): along the replications `N = k + 1`, `k : ℕ`, with dimensions
`(N m, N n, N B)`, the base constants `γ⋆`, `C_Σ` (`1 ≤ C_Σ`), momentum `β` and ridge interval
`[ϱ₋, ϱ₊]`, and states `replState`, there is a `SetupRegime` (`assum:app-setup-regime`) with these
data. Stated as an existence claim: the proof fields of the structure are the regime conditions.
Verbatim LaTeX:
```latex
Frobenius norm and operator norm $r_N^{-1/2}\to0$, so the replications with
this state satisfy \cref{assum:app-setup-regime}.
```
Sorried: proof card P5. -/
theorem def_app_vol_replication_regime (F0 : FrozenParams m n B) (S : SpectralData F0.C)
    (γstar CSig ϱlo ϱhi : ℝ) (hC : 1 ≤ CSig) (hsize : SizeFin F0.C B γstar CSig)
    (hm : 0 < m) (hn : 0 < n) (hϱ : 0 < ϱlo ∧ ϱlo ≤ ϱhi) :
    ∃ R : SetupRegime,
      R.m = (fun k : ℕ => (k + 1) * m) ∧ R.n = (fun k : ℕ => (k + 1) * n) ∧
      R.B = (fun k : ℕ => (k + 1) * B) ∧ R.γstar = γstar ∧ R.CSig = CSig ∧ R.β = F0.β ∧
      R.ϱlo = ϱlo ∧ R.ϱhi = ϱhi ∧
      ∀ k : ℕ, HEq (R.F k).C (replCov F0.C (k + 1)) ∧
        HEq (R.F k).A (replState F0.C S (k + 1)) := by
  have hBpos : 0 < B := F0.hB
  have hNpos : ∀ k : ℕ, 0 < k + 1 := fun k => Nat.succ_pos k
  have hBr : (0 : ℝ) < (B : ℝ) := by exact_mod_cast hBpos
  have hmr : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hnr : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hsz : ∀ k : ℕ, SizeFin (replCov F0.C (k + 1)) ((k + 1) * B) γstar CSig :=
    fun k => def_app_vol_replication_iv F0.C γstar CSig hsize (k + 1) (hNpos k)
  have hA : ∀ k : ℕ, fro (replState F0.C S (k + 1)) = 1 :=
    fun k => def_app_vol_replication_vi F0.C S (k + 1) hm hn (hNpos k)
  let F : ∀ k : ℕ, FrozenParams ((k + 1) * m) ((k + 1) * n) ((k + 1) * B) := fun k =>
    def_app_vol_replication F0 S (k + 1) (hNpos k) (hA k)
  have hv : ∀ k : ℕ,
      ((((k + 1) * m : ℕ)) : ℝ) / ((((k + 1) * B : ℕ)) : ℝ) = (m : ℝ) / (B : ℝ) ∧
      ((((k + 1) * n : ℕ)) : ℝ) / ((((k + 1) * B : ℕ)) : ℝ) = (n : ℝ) / (B : ℝ) :=
    fun k => def_app_vol_replication_v (k + 1) (hNpos k) hBpos
  have hprop : ProportionalRegime (fun k : ℕ => (k + 1) * m) (fun k : ℕ => (k + 1) * n)
      (fun k : ℕ => (k + 1) * B) (fun k : ℕ => (F k).C) :=
    { γin := (n : ℝ) / (B : ℝ)
      γout := (m : ℝ) / (B : ℝ)
      γin_pos := div_pos hnr hBr
      γout_pos := div_pos hmr hBr
      B_top := tendsto_atTop_mono (fun k : ℕ => le_trans (Nat.le_succ k)
        (Nat.le_mul_of_pos_right (k + 1) hBpos)) tendsto_id
      ratio_in := Tendsto.congr (fun k => ((hv k).2).symm) tendsto_const_nhds
      ratio_out := Tendsto.congr (fun k => ((hv k).1).symm) tendsto_const_nhds
      bdd := ⟨CSig, by linarith, fun k => ⟨(hsz k).2.2, (hsz k).2.1⟩⟩ }
  refine ⟨{ m := fun k : ℕ => (k + 1) * m
            n := fun k : ℕ => (k + 1) * n
            B := fun k : ℕ => (k + 1) * B
            F := F
            prop := hprop
            γstar := γstar
            CSig := CSig
            hC := hC
            dims := fun k => (hsz k).1
            normOut := fun k => (hsz k).2.1
            normIn := fun k => (hsz k).2.2
            β := F0.β
            hβ := fun _ => rfl
            ϱlo := ϱlo
            ϱhi := ϱhi
            hϱ := hϱ
            diffuse := (def_app_vol_replication_viii F0.C S hm hn).comp (tendsto_add_atTop_nat 1) },
    rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun k => ⟨HEq.rfl, HEq.rfl⟩⟩

end Muon.Volatility

end
