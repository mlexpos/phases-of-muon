import Mathlib
import Muon.Foundations.Conventions

/-!
# Appendix H: the deterministic row model (task L-H.1)

Snapshot `cr-2026-10-22`. Source: `sections/07-phase-comparison/section.tex`,
`def:app-phase-model` (l.65–99), the forcing/kernel display `eqn:app-phase-Fk` (l.190–194),
the first-hit convention (l.47–48, l.71–75) and `prop:app-phase-row-identity` (l.115–123).
Card: `sections/07-phase-comparison/CARD.md` §2, §3, §5 (L-H.1).

Declarations of record:
* `Muon.Phase.RowModel` (with fields (M1)), `Muon.Phase.IsRowSolution` (predicate (M3)) for
  `def:app-phase-model`; items (M2) and (M4) are modelling clauses and appear only in the
  docstring;
* `Muon.Phase.prop_app_phase_row_identity` for `prop:app-phase-row-identity`.

Index set: the model is written for a general index type `ι`; the paper's `{1,…,N}` or `ℕ`
are instances (`Fin N`, `ℕ`), with the paper's first index `1` corresponding to `0` in Lean.
Every series over `ι` is a `tsum`, so every summability needed for a `tsum` to mean the
paper's sum is a structure field or a predicate clause, never inferred. In Lean a
non-summable `tsum` is `0`.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal Matrix

noncomputable section

namespace Muon.Phase

/-- Deterministic row model, `def:app-phase-model` (M1), snapshot `cr-2026-10-22`.

LaTeX (verbatim, `section.tex` l.65–99):
```
\begin{definition}[Deterministic row model]\label{def:app-phase-model}
Let the index set $\mathcal I$ be $\{1,\dots,N\}$ for an integer $N\ge1$,
or $\N$. The deterministic row model consists of the following four
items.
\begin{enumerate}[label=(M\arabic*)]
\item \emph{Adopted coefficients.} Numbers $\mu_i>0$, $\mathfrak d_i>0$,
$\mathfrak v_i\ge0$ and initial row energies $\fQ_i(0)\ge0$, $i\in\mathcal I$,
and a constant step $\lr>0$ are fixed, with
\begin{equation}\label{eqn:app-phase-F0S}
F_0\defeq\frac12\sum_{i\in\mathcal I}\mu_i\fQ_i(0)\in(0,\infty),\qquad
\mathcal S\defeq\sum_{i\in\mathcal I}\frac{\mu_i\mathfrak v_i}{2\mathfrak d_i}<\infty .
\end{equation}
They do not depend on time or on the state. An array carrying the
superscript $\text{s-SVD}$ or $\text{s-SGD}$, such as
$\mathfrak d_i^{\text{s-SVD}}$ or $\mathfrak v_i^{\text{s-SGD}}$, is an array
adopted in this sense, and not a coefficient proved for an algorithm.
\item \emph{Kernel replacement.} For an update matrix ${\mathsf S}$ computed at a
state $\Delta$ of positive risk $\cR(\Delta)$, the conditional row pairing
and the conditional raw second moment of the row are replaced by
\[
\EE\big[\langle\Delta^\T u_i,{\mathsf S}^\T u_i\rangle\,\big|\,\Delta\big]\ \leadsto\ \frac{\mathfrak d_i\,\norm{\Delta^\T u_i}^2}{\sqrt{\cR(\Delta)}},\qquad
\EE\big[\norm{{\mathsf S}^\T u_i}^2\,\big|\,\Delta\big]\ \leadsto\ \mathfrak v_i .
\]
\item \emph{Dynamical closure.} The row energies $\fQ_i(t)$ solve
\begin{equation}\label{eqn:app-phase-rows}
\frac{\dif\fQ_i}{\dif t}=-\frac{2\lr\,\mathfrak d_i}{\sqrt{\fRisk(t)}}\,\fQ_i(t)+\lr^2\mathfrak v_i,\qquad
\fRisk(t)\defeq\frac12\sum_{i\in\mathcal I}\mu_i\fQ_i(t),
\end{equation}
from the initial values of (M1), on an interval starting at $0$ on which
$\fRisk$ is continuous and positive.
\item \emph{Transfer.} A statement about the stochastic algorithm is drawn
from the model only through an approximation theorem with its own regime,
horizon and observable.
\end{enumerate}
\end{definition}
```

Lean encoding. The structure carries (M1): positivity and nonnegativity of the coefficients,
the step `η > 0`, the summability of the two series in `eqn:app-phase-F0S`, and `0 < F0`.
(M2) and (M4) are modelling clauses and are not fields. (M3) is `IsRowSolution` below.
-/
structure RowModel (ι : Type*) where
  /-- Eigenvalue weights `μ_i > 0` (M1). -/
  μ : ι → ℝ
  /-- Drift coefficients `𝔡_i > 0` (M1). -/
  d : ι → ℝ
  /-- Volatility coefficients `𝔳_i ≥ 0` (M1). -/
  v : ι → ℝ
  /-- Initial row energies `𝔔_i(0) ≥ 0` (M1). -/
  Q0 : ι → ℝ
  /-- The constant step `η > 0` (M1), written `\lr` in the paper. -/
  η : ℝ
  μ_pos : ∀ i, 0 < μ i
  d_pos : ∀ i, 0 < d i
  v_nonneg : ∀ i, 0 ≤ v i
  Q0_nonneg : ∀ i, 0 ≤ Q0 i
  η_pos : 0 < η
  /-- `∑ μ_i 𝔔_i(0)` is summable, so `F_0` is a genuine series (M1). -/
  summable_μQ0 : Summable (fun i => μ i * Q0 i)
  /-- `F_0 = ½ ∑ μ_i 𝔔_i(0) ∈ (0, ∞)` (M1, `eqn:app-phase-F0S`). -/
  F0_pos : 0 < (1 / 2 : ℝ) * ∑' i, μ i * Q0 i
  /-- `𝒮 = ∑ μ_i 𝔳_i / (2 𝔡_i) < ∞` (M1, `eqn:app-phase-F0S`). -/
  summable_S : Summable (fun i => μ i * v i / (2 * d i))

namespace RowModel

variable {ι : Type*}

/-- The initial-value constant `F_0 = ½ ∑_i μ_i 𝔔_i(0)` (`eqn:app-phase-F0S`). -/
def F0 (m : RowModel ι) : ℝ := (1 / 2 : ℝ) * ∑' i, m.μ i * m.Q0 i

/-- The constant `𝒮 = ∑_i μ_i 𝔳_i / (2 𝔡_i)` (`eqn:app-phase-F0S`). -/
def S (m : RowModel ι) : ℝ := ∑' i, m.μ i * m.v i / (2 * m.d i)

/-- The risk `𝔑(t) = ½ ∑_i μ_i 𝔔_i(t)` of a family of row energies `Q`
(`eqn:app-phase-rows`). -/
def risk (m : RowModel ι) (Q : ι → ℝ → ℝ) (t : ℝ) : ℝ :=
  (1 / 2 : ℝ) * ∑' i, m.μ i * Q i t

/-- The forcing `F(s) = ½ ∑_i μ_i 𝔔_i(0) e^{-2 𝔡_i s}` (`eqn:app-phase-Fk`). -/
def forcing (m : RowModel ι) (s : ℝ) : ℝ :=
  (1 / 2 : ℝ) * ∑' i, m.μ i * m.Q0 i * Real.exp (-(2 * m.d i * s))

/-- The kernel `k(s) = (η/2) ∑_i μ_i 𝔳_i e^{-2 𝔡_i s}` (`eqn:app-phase-Fk`).
The paper defines `k` on `(0,∞)` only: for countable `ι` the series may diverge at `s = 0`
(`eqn:app-phase-Fk`, l.192–193). Lean's value at `0` is an artifact of `tsum` and must not be
used; every statement about `k` restricts to `s > 0`. -/
def kernel (m : RowModel ι) (s : ℝ) : ℝ :=
  (m.η / 2) * ∑' i, m.μ i * m.v i * Real.exp (-(2 * m.d i * s))

/-- The constant `k̄ = η 𝒮 / 2` (`eqn:app-phase-Fk`). -/
def kbar (m : RowModel ι) : ℝ := m.η * m.S / 2

end RowModel

/-- The solution concept (M3) of `def:app-phase-model`: `Q` solves the row equations
`eqn:app-phase-rows` on `[0, t₁)` from the initial values of (M1), with the risk
`𝔑 = ½ ∑ μ_i Q_i` summable at each time, continuous and positive on the interval.

The derivative is taken within `[0, t₁)` (`HasDerivWithinAt … (Ico 0 t₁) t`): two-sided at
interior times and one-sided at `t = 0`, which the paper leaves implicit. A right derivative
alone would admit right-continuous jumps of individual rows (review L-H.1, defect D1). The summability clause is part of the predicate, since a non-summable
`tsum` would silently read as `0`. -/
def IsRowSolution {ι : Type*} (m : RowModel ι) (t₁ : ℝ) (Q : ι → ℝ → ℝ) : Prop :=
  (∀ i, Q i 0 = m.Q0 i) ∧
  (∀ t ∈ Ico (0 : ℝ) t₁, Summable (fun i => m.μ i * Q i t)) ∧
  ContinuousOn (m.risk Q) (Ico (0 : ℝ) t₁) ∧
  (∀ t ∈ Ico (0 : ℝ) t₁, 0 < m.risk Q t) ∧
  (∀ t ∈ Ico (0 : ℝ) t₁, ∀ i,
    HasDerivWithinAt (Q i)
      (-(2 * m.η * m.d i) / Real.sqrt (m.risk Q t) * Q i t + m.η ^ 2 * m.v i)
      (Ico (0 : ℝ) t₁) t)

/-- The first hitting time `t_a = inf {t ≥ 0 : R(t) ≤ a}` in `[0, +∞]` (paper l.71–75,
convention `inf ∅ = +∞` at l.47–48). Values are in `ℝ≥0∞`: an `ℝ`-valued `sInf` would give
`0` on the empty set. -/
def firstHit (R : ℝ → ℝ) (a : ℝ) : ℝ≥0∞ :=
  ⨅ (t : ℝ≥0) (_ : R (t : ℝ) ≤ a), (t : ℝ≥0∞)

/-- Algebraic expansion of a squared norm of `a - c • b`. -/
lemma dot_sub_smul_self {n : ℕ} (a b : Muon.Vec n) (c : ℝ) :
    dotProduct (a - c • b) (a - c • b)
      = dotProduct a a - (2 * c) * dotProduct a b + c ^ 2 * dotProduct b b := by
  simp only [dotProduct_sub, sub_dotProduct, dotProduct_smul, smul_dotProduct, smul_eq_mul,
    dotProduct_comm b a]
  ring

/-- Integrated expansion, for a random vector `b` with square-integrable coordinates. -/
lemma integral_dot_sub_smul {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {n : ℕ} (a : Muon.Vec n) (c : ℝ) (b : Ω → Muon.Vec n)
    (hb : ∀ j, MemLp (fun ω => b ω j) 2 P) :
    ∫ ω, dotProduct (a - c • b ω) (a - c • b ω) ∂P - dotProduct a a
      = -(2 * c) * ∫ ω, dotProduct a (b ω) ∂P + c ^ 2 * ∫ ω, dotProduct (b ω) (b ω) ∂P := by
  have hg : Integrable (fun ω => dotProduct a (b ω)) P := by
    have : (fun ω => dotProduct a (b ω)) = fun ω => ∑ j, a j * b ω j := by
      funext ω; simp [dotProduct]
    rw [this]
    exact integrable_finsetSum _ fun j _ => ((hb j).integrable one_le_two).const_mul (a j)
  have hh : Integrable (fun ω => dotProduct (b ω) (b ω)) P := by
    have : (fun ω => dotProduct (b ω) (b ω)) = fun ω => ∑ j, b ω j ^ 2 := by
      funext ω; simp [dotProduct, sq]
    rw [this]
    exact integrable_finsetSum _ fun j _ => (hb j).integrable_sq
  have hpt : (fun ω => dotProduct (a - c • b ω) (a - c • b ω))
      = fun ω => dotProduct a a - (2 * c) * dotProduct a (b ω)
          + c ^ 2 * dotProduct (b ω) (b ω) := by
    funext ω; exact dot_sub_smul_self a (b ω) c
  have h1 : Integrable (fun ω => dotProduct a a - (2 * c) * dotProduct a (b ω)) P :=
    (integrable_const _).sub (hg.const_mul (2 * c))
  have h2 : Integrable (fun ω => c ^ 2 * dotProduct (b ω) (b ω)) P := hh.const_mul (c ^ 2)
  rw [hpt, integral_add h1 h2, integral_sub (integrable_const _) (hg.const_mul (2 * c)),
    integral_const_mul, integral_const_mul, integral_const]
  simp only [probReal_univ, one_smul]
  ring

/-- One step of a row, `prop:app-phase-row-identity`, snapshot `cr-2026-10-22`.

LaTeX (verbatim, `section.tex` l.115–123):
```
\begin{proposition}[One step of a row]\label{prop:app-phase-row-identity}
Let $\Delta\in\R^{\Nout\times\Nin}$ be fixed, let $u$ be a unit vector in
$\R^{\Nout}$, let $\lr>0$, and let ${\mathsf S}$ be a random matrix with
$\EE\norm {\mathsf S}_\F^2<\infty$. Then
\[
\EE\norm{(\Delta-\lr {\mathsf S})^\T u}^2-\norm{\Delta^\T u}^2
=-2\lr\,\EE\langle\Delta^\T u,{\mathsf S}^\T u\rangle+\lr^2\,\EE\norm{{\mathsf S}^\T u}^2 .
\]
\end{proposition}
```

Encoding: `Δ : Mat m n` with `m = N_out`, `n = N_in`; `u : Vec m` with `u ⬝ u = 1`; the
random matrix is `S : Ω → Mat m n` with measurable entries and `E‖S‖_F² < ∞` written as
`MemLp (‖S‖_F) 2`, which is `E‖S‖_F² < ∞` for the Frobenius norm `Muon.fro`. Expectations are
Bochner integrals under a probability measure `P`. All integrability is part of the claim
(card §3: "integrability of each term is proved, not assumed"), so no integrability
hypothesis is added. Norms of vectors are the Euclidean norm squared, `x ⬝ᵥ x`.
-/
theorem prop_app_phase_row_identity {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {m n : ℕ} (Δ : Muon.Mat m n) (u : Muon.Vec m)
    (hu : dotProduct u u = 1) (lr : ℝ) (hlr : 0 < lr)
    (S : Ω → Muon.Mat m n) (hS : ∀ i j, Measurable fun ω => S ω i j)
    (hSF : MemLp (fun ω => Muon.fro (S ω)) 2 P) :
    ∫ ω, dotProduct (Matrix.mulVec (Matrix.transpose (Δ - lr • S ω)) u)
          (Matrix.mulVec (Matrix.transpose (Δ - lr • S ω)) u) ∂P
        - dotProduct (Matrix.mulVec (Matrix.transpose Δ) u) (Matrix.mulVec (Matrix.transpose Δ) u)
      = -2 * lr * ∫ ω, dotProduct (Matrix.mulVec (Matrix.transpose Δ) u)
          (Matrix.mulVec (Matrix.transpose (S ω)) u) ∂P
        + lr ^ 2 * ∫ ω, dotProduct (Matrix.mulVec (Matrix.transpose (S ω)) u)
          (Matrix.mulVec (Matrix.transpose (S ω)) u) ∂P := by
  classical
  have hfro : ∀ ω i j, ‖S ω i j‖ ≤ Muon.fro (S ω) := by
    intro ω i j
    unfold Muon.fro
    rw [← Real.sqrt_sq (norm_nonneg (S ω i j))]
    apply Real.sqrt_le_sqrt
    calc ‖S ω i j‖ ^ 2 ≤ ∑ j', ‖S ω i j'‖ ^ 2 :=
          Finset.single_le_sum (f := fun j' => ‖S ω i j'‖ ^ 2)
            (fun _ _ => sq_nonneg _) (Finset.mem_univ j)
      _ ≤ ∑ i', ∑ j', ‖S ω i' j'‖ ^ 2 :=
          Finset.single_le_sum (f := fun i' => ∑ j', ‖S ω i' j'‖ ^ 2)
            (fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _) (Finset.mem_univ i)
  have hentry : ∀ i j, MemLp (fun ω => S ω i j) 2 P := fun i j =>
    MemLp.of_le hSF (hS i j).aestronglyMeasurable (Eventually.of_forall fun ω => by
      have h0 : 0 ≤ Muon.fro (S ω) := Real.sqrt_nonneg _
      rw [Real.norm_of_nonneg h0]
      exact hfro ω i j)
  have hb : ∀ j, MemLp (fun ω => Matrix.mulVec (Matrix.transpose (S ω)) u j) 2 P := by
    intro j
    have : (fun ω => Matrix.mulVec (Matrix.transpose (S ω)) u j)
        = fun ω => ∑ i, u i * S ω i j := by
      funext ω; simp [Matrix.mulVec, dotProduct, mul_comm]
    rw [this]
    exact memLp_finsetSum _ fun i _ => (hentry i j).const_mul (u i)
  have hpt : ∀ ω, Matrix.mulVec (Matrix.transpose (Δ - lr • S ω)) u
      = Matrix.mulVec (Matrix.transpose Δ) u - lr • Matrix.mulVec (Matrix.transpose (S ω)) u := by
    intro ω
    simp only [Matrix.transpose_sub, Matrix.transpose_smul, Matrix.sub_mulVec,
      Matrix.smul_mulVec]
  have key := integral_dot_sub_smul P (Matrix.mulVec (Matrix.transpose Δ) u) lr
    (fun ω => Matrix.mulVec (Matrix.transpose (S ω)) u) hb
  simp only [hpt]
  linear_combination key

end Muon.Phase

end
