import Mathlib
import Muon.Phase.FirstHit
import Muon.Phase.Clock

/-!
# Appendix H: adopted power-law arrays and the prefactor identities (task L-H.5)

Snapshot `cr-2026-10-23`. Source: `sections/07-phase-comparison/section.tex`:
`def:app-phase-arrays` (l.1070–1098), `prop:app-phase-prefactors` (l.1116–1166), and the
window displays `eqn:app-phase-eps0`, `eqn:app-phase-height`, `eqn:app-phase-Pi` (l.1206–1225).
Card: `sections/07-phase-comparison/CARD.md` §2, §3, §5 (L-H.5).

Declarations of record:
* `Muon.Phase.def_app_phase_arrays` for `def:app-phase-arrays` (the pair of the two arrays);
* `Muon.Phase.prop_app_phase_prefactors_m1` (the leading clause "satisfies (M1), with `F_0`"),
  `_i`, `_ii`, `_ii_props`, `_iii`, `_iv` for the parts of `prop:app-phase-prefactors`.

Reused, not redefined: `RowModel`, `RowModel.forcing`, `RowModel.kernel` (`Muon.Phase.Model`);
`IsVolterraSol` (`Muon.Phase.Volterra`); `riskClock`, `thm_app_phase_hitting_i`
(`Muon.Phase.Clock`);
`Ir` (`I_r`), `clockEps0`
(`Muon.Phase.FirstHit`); `Hsum`, `zetaR`, `Lsum`, `fNq`, `rq`, `Cpq`,
`Aconst` (`Muon.Phase.PowerSums`); `firstHit` (`Muon.Phase.Model`);
`oneSidedConv` (`Muon.Foundations`).

Encoding decisions:
* Index: the paper's `i ∈ {1,…,N}` is `i : Fin N` with value `(i : ℕ) + 1` (`idxR`).
* `PhaseArrays ι` carries the coefficient part of `def:app-phase-model` (M1) without the step.
  Its `F0` and `S` are the formulas of `eqn:app-phase-F0S` on arrays; they coincide with
  `RowModel.F0`/`RowModel.S` for any model with these arrays.
* (M1) for the arrays is stated as existence of a `RowModel (Fin N)` with these coefficients and
  any prescribed step `η > 0` (`prop_app_phase_prefactors_m1`). The model fields are thus
  discharged in that proof, not inside definitions; no `sorry`, no axioms in definitions.
* `IsMatchedModel A m ε` pins a model to the arrays `A` and the matched step `η⋆ = 2√ε/𝒮`.
* `dimKernel m T₀ ε` is the dimensionless kernel `g_j(u) = T₀ k_j(T₀u)/√ε` of
  `eqn:app-phase-kernels`, read off the `RowModel` kernel. The dimensionless risk is `u ↦ Q(T₀u)`.
* `k_{N,j}` (`eqn:app-phase-heights`) is `phaseKsvd`/`phaseKsgd` in closed form; the identity
  `g_j(0) = k_{N,j}` is a clause of `prop_app_phase_prefactors_ii_props`.
* `phaseEps0 α ς T` is the minimum of `clockEps0 (α+ς) (α/2) T` and `clockEps0 (α+ς) α T`. The
  paper's minimum over `{j : r_j < 1}` with empty minimum `1` is the same number, because each
  `clockEps0` carries the terms `1/4`, `1/(8T)`, `C_j²`, `(A_p/T)²` and the `r_j < 1` term only
  when `r_j < 1`, and `1/4` already dominates the empty-set convention.
* `phasePi r ε` is the display `eqn:app-phase-Pi`; the paper takes `r > 0`, which is not
  encoded (the `r ≤ 0` values are never used).
* `prop_app_phase_prefactors_iii` assumes `0 < T`: the hitting theorem `thm_app_phase_hitting_i`
  needs a positive level `Tε`. The paper states no sign for `T` at this point (open question).
* `prop_app_phase_prefactors_iv` uses `phaseDN` (closed form of `eqn:app-phase-DN`);
  `prop_app_phase_prefactors_i` contains the ratio identity `D_N = S_sgd T0_sgd / (S_svd T0_svd)`.
-/

set_option linter.style.longLine false

open MeasureTheory Set Filter Topology Asymptotics
open scoped ENNReal NNReal
open Muon.Foundations

noncomputable section

namespace Muon.Phase

/-! ## Coefficient arrays -/

/-- Coefficient arrays `(μ_i, 𝔡_i, 𝔳_i, 𝔔_i(0))_{i ∈ ι}` of the deterministic row model: the
coefficient part of `def:app-phase-model` (M1), without the step `η`. -/
structure PhaseArrays (ι : Type*) where
  /-- Eigenvalue weights `μ_i`. -/
  μ : ι → ℝ
  /-- Drift coefficients `𝔡_i`. -/
  d : ι → ℝ
  /-- Volatility coefficients `𝔳_i`. -/
  v : ι → ℝ
  /-- Initial row energies `𝔔_i(0)`. -/
  Q0 : ι → ℝ

namespace PhaseArrays

variable {ι : Type*}

/-- `F_0 = ½ ∑_i μ_i 𝔔_i(0)` (`eqn:app-phase-F0S`), for arrays. -/
def F0 (A : PhaseArrays ι) : ℝ := (1 / 2 : ℝ) * ∑' i, A.μ i * A.Q0 i

/-- `𝒮 = ∑_i μ_i 𝔳_i / (2 𝔡_i)` (`eqn:app-phase-F0S`), for arrays. -/
def S (A : PhaseArrays ι) : ℝ := ∑' i, A.μ i * A.v i / (2 * A.d i)

end PhaseArrays

/-- The paper's index `i ∈ {1,…,N}` as the real number `i`, for `i : Fin N` (Lean is 0-based). -/
def idxR {N : ℕ} (i : Fin N) : ℝ := ((i : ℕ) : ℝ) + 1

/-- `γ = N / B` (`def:app-phase-arrays`). -/
def gammaRat (N B : ℕ) : ℝ := (N : ℝ) / (B : ℝ)

/-- `μ̄ = H_N(α)/N` (`def:app-phase-arrays`). -/
def muBarOf (α : ℝ) (N : ℕ) : ℝ := Hsum α N / (N : ℝ)

/-- `μ_i = i^{-α}` (`def:app-phase-arrays`). -/
def muOf (α : ℝ) (N : ℕ) (i : Fin N) : ℝ := idxR i ^ (-α)

/-- `𝔔_i(0) = i^{-ς}` (`def:app-phase-arrays`); `ς` is the target exponent `\texp`. -/
def Q0Of (ς : ℝ) (N : ℕ) (i : Fin N) : ℝ := idxR i ^ (-ς)

/-- The \SignSVD arrays: `𝔡_i = γ^{-1/2} i^{-α/2}`, `𝔳_i = 1` (`eqn:app-phase-arrays`). -/
def svdArrays (α ς : ℝ) (N B : ℕ) : PhaseArrays (Fin N) where
  μ := muOf α N
  d := fun i => gammaRat N B ^ (-(1 / 2 : ℝ)) * idxR i ^ (-(α / 2))
  v := fun _ => 1
  Q0 := Q0Of ς N

/-- The \SignSGD arrays: `𝔡_i = μ_i √(B/(π μ̄))`, `𝔳_i = N[1 + (2/π)(μ_i/μ̄ - 1)]`
(`eqn:app-phase-arrays`). -/
def sgdArrays (α ς : ℝ) (N B : ℕ) : PhaseArrays (Fin N) where
  μ := muOf α N
  d := fun i => muOf α N i * Real.sqrt ((B : ℝ) / (Real.pi * muBarOf α N))
  v := fun i => (N : ℝ) * (1 + 2 / Real.pi * (muOf α N i / muBarOf α N - 1))
  Q0 := Q0Of ς N

/-- The time scales `T_0^{\text{s-SVD}} = √γ` and `T_0^{\text{s-SGD}} = √(π μ̄/B)`
(`def:app-phase-arrays`). -/
def svdT0 (N B : ℕ) : ℝ := Real.sqrt (gammaRat N B)

/-- See `svdT0`. -/
def sgdT0 (α : ℝ) (N B : ℕ) : ℝ := Real.sqrt (Real.pi * muBarOf α N / (B : ℝ))

/-- Label `def:app-phase-arrays`, declaration of record for the adopted arrays, as the pair
(\SignSVD, \SignSGD). Snapshot `cr-2026-10-23`. Statement (verbatim, `sections/07-phase-comparison/section.tex`):

Source lines: section.tex l.1070–1098.
```latex
\begin{definition}[Adopted power-law arrays]\label{def:app-phase-arrays}
Fix $\alpha>0$ and $\texp\in\R$ with $p\defeq\alpha+\texp>1$, and integers
$B\ge N\ge1$. Put $\gamma\defeq N/B\in(0,1]$ and
$\bar\mu\defeq H_N(\alpha)/N$, and for $1\le i\le N$ let $\mu_i\defeq i^{-\alpha}$
and $\fQ_i(0)\defeq i^{-\texp}$. The \SignSVD and \SignSGD arrays are
\begin{equation}\label{eqn:app-phase-arrays}
\begin{aligned}
\mathfrak d_i^{\text{s-SVD}}&\defeq\gamma^{-1/2}i^{-\alpha/2}=\sqrt{\mu_i}\sqrt{B/N},&\qquad
\mathfrak v_i^{\text{s-SVD}}&\defeq1,\\
\mathfrak d_i^{\text{s-SGD}}&\defeq\mu_i\sqrt{\frac B{\pi\bar\mu}},&\qquad
\mathfrak v_i^{\text{s-SGD}}&\defeq N\Big[1+\frac2\pi\Big(\frac{\mu_i}{\bar\mu}-1\Big)\Big].
\end{aligned}
\end{equation}
For $j\in\{\text{s-SVD},\text{s-SGD}\}$, the time scales, rate exponents and
forcing exponents are
\[
T_0^{\text{s-SVD}}\defeq\sqrt\gamma,\quad T_0^{\text{s-SGD}}\defeq\sqrt{\frac{\pi\bar\mu}B},\qquad
q_{\text{s-SVD}}\defeq\frac\alpha2,\quad q_{\text{s-SGD}}\defeq\alpha,\qquad
r_j\defeq r_{q_j}=\frac{p-1}{2q_j} .
\]
For $\epsilon>0$ each model is run at its matched step
$\lr^\star_j\defeq2\sqrt\epsilon/\mathcal S_j$. Its risk $Q_j$ solves
\cref{eqn:app-phase-volterra} with forcing $F_j$ and kernel $k_j$, and its
dimensionless risk, kernel and first hit at a fixed multiplier $T$ are
\[
Y_j(u)\defeq Q_j(T_0^ju),\qquad g_j(u)\defeq\frac{T_0^j\,k_j(T_0^ju)}{\sqrt\epsilon},\qquad
\hat u_j\defeq\inf\{u\ge0:\ Y_j(u)\le T\epsilon\} .
\]
\end{definition}
``` -/
def def_app_phase_arrays (α ς : ℝ) (N B : ℕ) : PhaseArrays (Fin N) × PhaseArrays (Fin N) :=
  (svdArrays α ς N B, sgdArrays α ς N B)

/-- The matched step `η⋆ = 2√ε / 𝒮` of a model with arrays `A` (`def:app-phase-arrays`, the
step at which each model is run; `thm_app_phase_hitting_i` hypothesis `η = 2√ε/𝒮`). -/
def matchedStep {ι : Type*} (A : PhaseArrays ι) (ε : ℝ) : ℝ := 2 * Real.sqrt ε / A.S

/-- A model `m` with the coefficients of the arrays `A` and the matched step at level `ε`. -/
def IsMatchedModel {ι : Type*} (A : PhaseArrays ι) (m : RowModel ι) (ε : ℝ) : Prop :=
  m.μ = A.μ ∧ m.d = A.d ∧ m.v = A.v ∧ m.Q0 = A.Q0 ∧ m.η = matchedStep A ε

/-- The dimension factor `D_N = π H_N(α)/H_N(α/2)` (`eqn:app-phase-DN`, closed form). -/
def phaseDN (α : ℝ) (N : ℕ) : ℝ := Real.pi * Hsum α N / Hsum (α / 2) N

/-- The \SignSVD height `k_{N,s-SVD} = 2H_N(α)/H_N(α/2)` (`eqn:app-phase-heights`). -/
def phaseKsvd (α : ℝ) (N : ℕ) : ℝ := 2 * Hsum α N / Hsum (α / 2) N

/-- The \SignSGD height `k_{N,s-SGD} = 2(1-2/π)H_N(α)/N + 4H_N(2α)/(π H_N(α))`
(`eqn:app-phase-heights`). -/
def phaseKsgd (α : ℝ) (N : ℕ) : ℝ :=
  2 * (1 - 2 / Real.pi) * Hsum α N / (N : ℝ) + 4 * Hsum (2 * α) N / (Real.pi * Hsum α N)

/-- The dimensionless kernel `g_j(u) = T_0 k_j(T_0 u)/√ε` of a model `m` (`eqn:app-phase-kernels`,
with `k_j` the kernel `RowModel.kernel` of `m`). -/
def dimKernel {ι : Type*} (m : RowModel ι) (T0 ε u : ℝ) : ℝ :=
  T0 * m.kernel (T0 * u) / Real.sqrt ε

/-! ## Windows -/

/-- The window threshold `ε_0` of `eqn:app-phase-eps0`, with `p = α + ς`: the minimum of the
two proof-local thresholds `clockEps0 p (α/2) T` and `clockEps0 p α T` of `Muon.Phase.FirstHit`
(each collects `1/4`, `1/(8T)`, `C_j²`, `(A_p/T)²`, and the `r_j < 1` term when `r_j < 1`).

Source lines: section.tex l.1210–1212.
```latex
\begin{equation}\label{eqn:app-phase-eps0}
\epsilon_0\defeq\min\Big\{\frac14,\ \frac1{8T},\ C_{\text{s-SVD}}^2,\ C_{\text{s-SGD}}^2,\ \Big(\frac AT\Big)^2,\ \min_{j:\,r_j<1}\frac A{T\,2^{2r_j/(1-r_j)}}\Big\},
\end{equation}
``` -/
def phaseEps0 (α ς T : ℝ) : ℝ :=
  min (clockEps0 (α + ς) (α / 2) T) (clockEps0 (α + ς) α T)

/-- The height `H_j(ε) = (C_j/√ε)^{1/r_j} - 1` of `eqn:app-phase-height` (`r_j` in the
exponent). Defined for `0 < ε < C_j²`, which the window guarantees.

Source lines: section.tex l.1219–1221.
```latex
\begin{equation}\label{eqn:app-phase-height}
k_{N,j}\,C_j\,I_{r_j}\big(H_j(\epsilon)\big)\le\sqrt\epsilon,\qquad\text{and}\qquad H_j(\epsilon)\le(N/4)^{q_j}\ \text{ if }r_j\le1 .
\end{equation}
``` -/
def phaseHeight (C r ε : ℝ) : ℝ := (C / Real.sqrt ε) ^ (1 / r) - 1

/-- The low-exponent window of `eqn:app-phase-eps0`–`eqn:app-phase-height`: the set of
`(N, B, ε)` with `N ≥ 4`, `B ≥ N`, `0 < ε < ε_0`, and for both `j`
`k_{N,j} C_j I_{r_j}(H_j(ε)) ≤ √ε`, and `H_j(ε) ≤ (N/4)^{q_j}` when `r_j ≤ 1`.
`C_j = C_{p,q_j}`, `r_j = r_{q_j}`, `p = α + ς` (`Cpq`, `rq`, `Ir` reused). -/
def PhaseLowWindow (α ς T : ℝ) (N B : ℕ) (ε : ℝ) : Prop :=
  4 ≤ N ∧ N ≤ B ∧ 0 < ε ∧ ε < phaseEps0 α ς T ∧
    phaseKsvd α N * Cpq (α + ς) (α / 2) *
        Ir (rq (α + ς) (α / 2)) (phaseHeight (Cpq (α + ς) (α / 2)) (rq (α + ς) (α / 2)) ε)
      ≤ Real.sqrt ε ∧
    phaseKsgd α N * Cpq (α + ς) α *
        Ir (rq (α + ς) α) (phaseHeight (Cpq (α + ς) α) (rq (α + ς) α) ε)
      ≤ Real.sqrt ε ∧
    (rq (α + ς) (α / 2) ≤ 1 →
      phaseHeight (Cpq (α + ς) (α / 2)) (rq (α + ς) (α / 2)) ε ≤ ((N : ℝ) / 4) ^ (α / 2)) ∧
    (rq (α + ς) α ≤ 1 → phaseHeight (Cpq (α + ς) α) (rq (α + ς) α) ε ≤ ((N : ℝ) / 4) ^ α)

/-- The scale `Π_r(ε)` of `eqn:app-phase-Pi` (for `r > 0`, as in the paper).

Source lines: section.tex l.1223–1225.
```latex
\begin{equation}\label{eqn:app-phase-Pi}
\Pi_r(\epsilon)\defeq\begin{cases}\epsilon^{-1/(2r)},&0<r<1,\\ \epsilon^{-1/2}\log(1/\epsilon),&r=1,\\ \epsilon^{-1/2},&r>1.\end{cases}
\end{equation}
``` -/
def phasePi (r ε : ℝ) : ℝ :=
  if r < 1 then ε ^ (-(1 / (2 * r)))
  else if r = 1 then ε ^ (-(1 / 2 : ℝ)) * Real.log (1 / ε)
  else ε ^ (-(1 / 2 : ℝ))

/-! ### Proof helpers for `prop:app-phase-prefactors` (P-H.5.P1) -/

lemma pa_idx_pos {N : ℕ} (i : Fin N) : 0 < idxR i := by
  unfold idxR; positivity

lemma pa_sum_fin (a : ℝ) (N : ℕ) : ∑ i : Fin N, idxR i ^ (-a) = Hsum a N := by
  induction N with
  | zero => simp [Hsum]
  | succ n ih =>
    rw [Fin.sum_univ_castSucc]
    have h1 : ∀ i : Fin n, idxR (Fin.castSucc i) ^ (-a) = idxR i ^ (-a) := by
      intro i; simp [idxR]
    simp only [h1, ih]
    unfold Hsum
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ n + 1)]
    simp [idxR]

lemma pa_Hsum_pos (a : ℝ) {N : ℕ} (hN : 1 ≤ N) : 0 < Hsum a N := by
  rw [← pa_sum_fin]
  exact Finset.sum_pos (fun i _ => Real.rpow_pos_of_pos (pa_idx_pos i) _)
    ⟨⟨0, by omega⟩, Finset.mem_univ _⟩

lemma pa_sum_mu (α : ℝ) (N : ℕ) : ∑ i : Fin N, muOf α N i = Hsum α N := by
  unfold muOf; exact pa_sum_fin α N

lemma pa_gamma_pos {N B : ℕ} (hN : 1 ≤ N) (hNB : N ≤ B) : 0 < gammaRat N B := by
  unfold gammaRat
  exact div_pos (Nat.cast_pos.mpr (by omega)) (Nat.cast_pos.mpr (by omega))

lemma pa_muBar_pos (α : ℝ) {N : ℕ} (hN : 1 ≤ N) : 0 < muBarOf α N := by
  unfold muBarOf
  exact div_pos (pa_Hsum_pos α hN) (Nat.cast_pos.mpr (by omega))

lemma pa_mu_Q0 (α ς : ℝ) {N : ℕ} (i : Fin N) :
    muOf α N i * Q0Of ς N i = idxR i ^ (-(α + ς)) := by
  unfold muOf Q0Of
  rw [← Real.rpow_add (pa_idx_pos i)]
  congr 1; ring

lemma pa_rowModel {N : ℕ} (hN : 1 ≤ N) (A : PhaseArrays (Fin N))
    (hμ : ∀ i, 0 < A.μ i) (hd : ∀ i, 0 < A.d i) (hv : ∀ i, 0 ≤ A.v i)
    (hQ : ∀ i, 0 < A.Q0 i) (eta : ℝ) (heta : 0 < eta) :
    ∃ m : RowModel (Fin N), m.μ = A.μ ∧ m.d = A.d ∧ m.v = A.v ∧ m.Q0 = A.Q0 ∧ m.η = eta := by
  let m : RowModel (Fin N) :=
    { μ := A.μ
      d := A.d
      v := A.v
      Q0 := A.Q0
      η := eta
      μ_pos := hμ
      d_pos := hd
      v_nonneg := hv
      Q0_nonneg := fun i => le_of_lt (hQ i)
      η_pos := heta
      summable_μQ0 := Summable.of_finite
      F0_pos := ?_
      summable_S := Summable.of_finite }
  refine ⟨m, rfl, rfl, rfl, rfl, rfl⟩
  apply mul_pos (by norm_num)
  rw [tsum_fintype]
  exact Finset.sum_pos (fun i _ => mul_pos (hμ i) (hQ i)) ⟨⟨0, by omega⟩, Finset.mem_univ _⟩

lemma pa_svd_term (x a g : ℝ) (hx : 0 < x) (hg : 0 < g) :
    x ^ (-a) * 1 / (2 * (g ^ (-(1 / 2 : ℝ)) * x ^ (-(a / 2))))
      = 1 / 2 * Real.sqrt g * x ^ (-(a / 2)) := by
  have h1 : x ^ (-a) = x ^ (-(a / 2)) * x ^ (-(a / 2)) := by
    rw [← Real.rpow_add hx]; congr 1; ring
  have h2 : g ^ (-(1 / 2 : ℝ)) = (Real.sqrt g)⁻¹ := by
    rw [Real.sqrt_eq_rpow, Real.rpow_neg hg.le]
  have hs : 0 < Real.sqrt g := Real.sqrt_pos.2 hg
  have hp : 0 < x ^ (-(a / 2)) := Real.rpow_pos_of_pos hx _
  rw [h1, h2]
  field_simp

lemma pa_sgd_term (u m Bn Nr : ℝ) (hu : 0 < u) (hm : 0 < m) (hB : 0 < Bn) :
    u * (Nr * (1 + 2 / Real.pi * (u / m - 1))) / (2 * (u * Real.sqrt (Bn / (Real.pi * m))))
      = 1 / 2 * Real.sqrt (Real.pi * m / Bn) * Nr * (1 + 2 / Real.pi * (u / m - 1)) := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have hpm : 0 < Real.pi * m := mul_pos hpi hm
  have hs : Real.sqrt (Bn / (Real.pi * m)) * Real.sqrt (Real.pi * m / Bn) = 1 := by
    rw [← Real.sqrt_mul (div_pos hB hpm).le]
    rw [show Bn / (Real.pi * m) * (Real.pi * m / Bn) = 1 by
      have := hB.ne'; have := hpm.ne'; field_simp]
    exact Real.sqrt_one
  have hsp : 0 < Real.sqrt (Bn / (Real.pi * m)) := Real.sqrt_pos.2 (div_pos hB hpm)
  rw [div_eq_iff (by positivity)]
  linear_combination (-(u * Nr * (1 + 2 / Real.pi * (u / m - 1)))) * hs

lemma pa_svd_S (α ς : ℝ) (N B : ℕ) (hN : 1 ≤ N) (hNB : N ≤ B) :
    (svdArrays α ς N B).S = 1 / 2 * Real.sqrt (gammaRat N B) * Hsum (α / 2) N := by
  have hγ := pa_gamma_pos hN hNB
  unfold PhaseArrays.S
  show ∑' i : Fin N, muOf α N i * 1 / (2 * (gammaRat N B ^ (-(1 / 2 : ℝ)) * idxR i ^ (-(α / 2))))
      = 1 / 2 * Real.sqrt (gammaRat N B) * Hsum (α / 2) N
  rw [tsum_fintype]
  calc ∑ i : Fin N, muOf α N i * 1 / (2 * (gammaRat N B ^ (-(1 / 2 : ℝ)) * idxR i ^ (-(α / 2))))
      = ∑ i : Fin N, 1 / 2 * Real.sqrt (gammaRat N B) * idxR i ^ (-(α / 2)) := by
        apply Finset.sum_congr rfl
        intro i _
        exact pa_svd_term (idxR i) α (gammaRat N B) (pa_idx_pos i) hγ
    _ = 1 / 2 * Real.sqrt (gammaRat N B) * Hsum (α / 2) N := by
        rw [← Finset.mul_sum, pa_sum_fin]

lemma pa_sgd_S (α ς : ℝ) (N B : ℕ) (hN : 1 ≤ N) (hNB : N ≤ B) :
    (sgdArrays α ς N B).S = (N : ℝ) ^ 2 / 2 * Real.sqrt (Real.pi * muBarOf α N / (B : ℝ)) := by
  have hB : (0 : ℝ) < B := Nat.cast_pos.mpr (by omega)
  have hm := pa_muBar_pos α hN
  have hNpos : (0 : ℝ) < N := Nat.cast_pos.mpr (by omega)
  have hH : Hsum α N / muBarOf α N = (N : ℝ) := by
    unfold muBarOf
    have := (pa_Hsum_pos α hN).ne'
    have := hNpos.ne'
    field_simp
  have hsum1 : ∑ i : Fin N, (1 + 2 / Real.pi * (muOf α N i / muBarOf α N - 1)) = (N : ℝ) := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib, ← Finset.sum_div,
      pa_sum_mu, hH]
    simp
  unfold PhaseArrays.S
  show ∑' i : Fin N, muOf α N i * ((N : ℝ) * (1 + 2 / Real.pi * (muOf α N i / muBarOf α N - 1)))
      / (2 * (muOf α N i * Real.sqrt ((B : ℝ) / (Real.pi * muBarOf α N))))
      = (N : ℝ) ^ 2 / 2 * Real.sqrt (Real.pi * muBarOf α N / (B : ℝ))
  rw [tsum_fintype]
  calc ∑ i : Fin N, muOf α N i * ((N : ℝ) * (1 + 2 / Real.pi * (muOf α N i / muBarOf α N - 1)))
        / (2 * (muOf α N i * Real.sqrt ((B : ℝ) / (Real.pi * muBarOf α N))))
      = ∑ i : Fin N, 1 / 2 * Real.sqrt (Real.pi * muBarOf α N / (B : ℝ)) * (N : ℝ)
          * (1 + 2 / Real.pi * (muOf α N i / muBarOf α N - 1)) := by
        apply Finset.sum_congr rfl
        intro i _
        exact pa_sgd_term (muOf α N i) (muBarOf α N) (B : ℝ) (N : ℝ)
          (Real.rpow_pos_of_pos (pa_idx_pos i) _) hm hB
    _ = 1 / 2 * Real.sqrt (Real.pi * muBarOf α N / (B : ℝ)) * (N : ℝ) * (N : ℝ) := by
        rw [← Finset.mul_sum, hsum1]
    _ = (N : ℝ) ^ 2 / 2 * Real.sqrt (Real.pi * muBarOf α N / (B : ℝ)) := by ring


/-! ## Declarations of record: `prop:app-phase-prefactors` -/

/-- Label `prop:app-phase-prefactors`, leading clause "the arrays satisfy (M1), with `F_0 = ½H_N(p)`".
Snapshot `cr-2026-10-23`. Statement (verbatim, `sections/07-phase-comparison/section.tex`):

Source lines: section.tex l.1116–1166.
```latex
\begin{proposition}[Noise constants, kernels and clocks]\label{prop:app-phase-prefactors}
The arrays of \cref{def:app-phase-arrays} satisfy (M1), with
$F_0=\frac12H_N(p)$, and the following hold.
\begin{enumerate}[label=(\roman*)]
\item The noise constants, matched steps and time-scale products are
\begin{equation}\label{eqn:app-phase-ST0}
\begin{aligned}
\mathcal S_{\text{s-SVD}}&=\tfrac12\sqrt\gamma\,H_N(\alpha/2),&\quad
\lr^\star_{\text{s-SVD}}&=\frac{4\sqrt\epsilon}{\sqrt\gamma\,H_N(\alpha/2)},\\
\mathcal S_{\text{s-SGD}}&=\frac{N^2}2\sqrt{\frac{\pi\bar\mu}B},&\quad
\lr^\star_{\text{s-SGD}}&=\frac{4\sqrt\epsilon}{N^2}\sqrt{\frac B{\pi\bar\mu}},\\
\mathcal S_{\text{s-SVD}}T_0^{\text{s-SVD}}&=\tfrac\gamma2H_N(\alpha/2),&\quad
\mathcal S_{\text{s-SGD}}T_0^{\text{s-SGD}}&=\frac{\pi N^2\bar\mu}{2B}=\tfrac{\pi\gamma}2H_N(\alpha),
\end{aligned}
\end{equation}
and the dimension factor is
\begin{equation}\label{eqn:app-phase-DN}
D_N\defeq\frac{\mathcal S_{\text{s-SGD}}T_0^{\text{s-SGD}}}{\mathcal S_{\text{s-SVD}}T_0^{\text{s-SVD}}}=\frac{\pi H_N(\alpha)}{H_N(\alpha/2)} .
\end{equation}
\item The dimensionless risks solve
$Y_j=f_{N,q_j}+\sqrt\epsilon\,g_j*\sqrt{Y_j}$, with $f_{N,q}$ of
\cref{eqn:app-phase-fNq} and
\begin{equation}\label{eqn:app-phase-kernels}
g_{\text{s-SVD}}=\frac2{H_N(\alpha/2)}L_{N,\alpha,\alpha/2},\qquad
g_{\text{s-SGD}}=\frac{2(1-2/\pi)}N\,L_{N,\alpha,\alpha}+\frac4{\pi H_N(\alpha)}\,L_{N,2\alpha,\alpha} .
\end{equation}
Both kernels are positive, continuous and decreasing. The kernel
$g_{\text{s-SVD}}$ has integral $1$, and the two terms of $g_{\text{s-SGD}}$
have integrals $1-2/\pi$ and $2/\pi$. Their maxima are
\begin{equation}\label{eqn:app-phase-heights}
\begin{gathered}
k_{N,\text{s-SVD}}\defeq g_{\text{s-SVD}}(0)=\frac{2H_N(\alpha)}{H_N(\alpha/2)},\\
k_{N,\text{s-SGD}}\defeq g_{\text{s-SGD}}(0)=\frac{2(1-2/\pi)H_N(\alpha)}N+\frac{4H_N(2\alpha)}{\pi H_N(\alpha)} .
\end{gathered}
\end{equation}
\item If $\hat u_j<\infty$, then
\begin{equation}\label{eqn:app-phase-time}
t^j_{T\epsilon}=\frac{\mathcal S_jT_0^j}{2\sqrt\epsilon}\int_0^{\hat u_j}\sqrt{Y_j(u)}\,\dif u .
\end{equation}
\item As $N\to\infty$ at fixed $\alpha$,
\begin{equation}\label{eqn:app-phase-DN-asymp}
D_N\sim\begin{cases}
\pi\,\dfrac{1-\alpha/2}{1-\alpha}\,N^{-\alpha/2},&0<\alpha<1,\\[4pt]
\dfrac\pi2N^{-1/2}\log N,&\alpha=1,\\[4pt]
\pi(1-\alpha/2)\,\zeta(\alpha)\,N^{\alpha/2-1},&1<\alpha<2,\\[4pt]
\pi\zeta(2)/\log N,&\alpha=2,\\[4pt]
\pi\zeta(\alpha)/\zeta(\alpha/2),&\alpha>2.
\end{cases}
\end{equation}
\end{enumerate}
\end{proposition}
``` -/
theorem prop_app_phase_prefactors_m1 (α ς : ℝ) (N B : ℕ) (hα : 0 < α) (hp : 1 < α + ς)
    (hN : 1 ≤ N) (hNB : N ≤ B) :
    (∀ η : ℝ, 0 < η → ∃ m : RowModel (Fin N),
        m.μ = (svdArrays α ς N B).μ ∧ m.d = (svdArrays α ς N B).d ∧
        m.v = (svdArrays α ς N B).v ∧ m.Q0 = (svdArrays α ς N B).Q0 ∧ m.η = η) ∧
    (∀ η : ℝ, 0 < η → ∃ m : RowModel (Fin N),
        m.μ = (sgdArrays α ς N B).μ ∧ m.d = (sgdArrays α ς N B).d ∧
        m.v = (sgdArrays α ς N B).v ∧ m.Q0 = (sgdArrays α ς N B).Q0 ∧ m.η = η) ∧
    (svdArrays α ς N B).F0 = (1 / 2 : ℝ) * Hsum (α + ς) N ∧
    (sgdArrays α ς N B).F0 = (1 / 2 : ℝ) * Hsum (α + ς) N := by
  have hB' : (0 : ℝ) < B := Nat.cast_pos.mpr (by omega)
  have hNpos : (0 : ℝ) < N := Nat.cast_pos.mpr (by omega)
  have hγ := pa_gamma_pos hN hNB
  have hμ : ∀ i : Fin N, 0 < muOf α N i := fun i => Real.rpow_pos_of_pos (pa_idx_pos i) _
  have hQ : ∀ i : Fin N, 0 < Q0Of ς N i := fun i => Real.rpow_pos_of_pos (pa_idx_pos i) _
  have hF : (svdArrays α ς N B).F0 = (1 / 2 : ℝ) * Hsum (α + ς) N := by
    unfold PhaseArrays.F0
    show (1 / 2 : ℝ) * ∑' i : Fin N, muOf α N i * Q0Of ς N i = _
    simp only [pa_mu_Q0]
    rw [tsum_fintype, pa_sum_fin]
  have hF' : (sgdArrays α ς N B).F0 = (1 / 2 : ℝ) * Hsum (α + ς) N := by
    unfold PhaseArrays.F0
    show (1 / 2 : ℝ) * ∑' i : Fin N, muOf α N i * Q0Of ς N i = _
    simp only [pa_mu_Q0]
    rw [tsum_fintype, pa_sum_fin]
  have hdS : ∀ i : Fin N, 0 < (svdArrays α ς N B).d i := fun i =>
    mul_pos (Real.rpow_pos_of_pos hγ _) (Real.rpow_pos_of_pos (pa_idx_pos i) _)
  have hdG : ∀ i : Fin N, 0 < (sgdArrays α ς N B).d i := fun i =>
    mul_pos (hμ i) (Real.sqrt_pos.2 (div_pos hB' (mul_pos Real.pi_pos (pa_muBar_pos α hN))))
  have hvG : ∀ i : Fin N, 0 ≤ (sgdArrays α ς N B).v i := by
    intro i
    have ht : 0 < muOf α N i / muBarOf α N := div_pos (hμ i) (pa_muBar_pos α hN)
    have hc : 0 < 2 / Real.pi := by positivity
    have h2 : 2 / Real.pi < 1 := by
      rw [div_lt_one Real.pi_pos]; linarith [Real.pi_gt_three]
    show 0 ≤ (N : ℝ) * (1 + 2 / Real.pi * (muOf α N i / muBarOf α N - 1))
    apply mul_nonneg hNpos.le
    nlinarith [mul_pos hc ht]
  refine ⟨?_, ?_, hF, hF'⟩
  · intro η hη
    exact pa_rowModel hN (svdArrays α ς N B) hμ hdS (fun _ => zero_le_one) hQ η hη
  · intro η hη
    exact pa_rowModel hN (sgdArrays α ς N B) hμ hdG hvG hQ η hη

/-- Label `prop:app-phase-prefactors`, part (i): the noise constants, matched steps and time-scale
products, and the dimension factor `D_N` (`eqn:app-phase-ST0`, `eqn:app-phase-DN`).
Snapshot `cr-2026-10-23`. Statement (verbatim, `sections/07-phase-comparison/section.tex`):

Source lines: section.tex l.1116–1166.
```latex
\begin{proposition}[Noise constants, kernels and clocks]\label{prop:app-phase-prefactors}
The arrays of \cref{def:app-phase-arrays} satisfy (M1), with
$F_0=\frac12H_N(p)$, and the following hold.
\begin{enumerate}[label=(\roman*)]
\item The noise constants, matched steps and time-scale products are
\begin{equation}\label{eqn:app-phase-ST0}
\begin{aligned}
\mathcal S_{\text{s-SVD}}&=\tfrac12\sqrt\gamma\,H_N(\alpha/2),&\quad
\lr^\star_{\text{s-SVD}}&=\frac{4\sqrt\epsilon}{\sqrt\gamma\,H_N(\alpha/2)},\\
\mathcal S_{\text{s-SGD}}&=\frac{N^2}2\sqrt{\frac{\pi\bar\mu}B},&\quad
\lr^\star_{\text{s-SGD}}&=\frac{4\sqrt\epsilon}{N^2}\sqrt{\frac B{\pi\bar\mu}},\\
\mathcal S_{\text{s-SVD}}T_0^{\text{s-SVD}}&=\tfrac\gamma2H_N(\alpha/2),&\quad
\mathcal S_{\text{s-SGD}}T_0^{\text{s-SGD}}&=\frac{\pi N^2\bar\mu}{2B}=\tfrac{\pi\gamma}2H_N(\alpha),
\end{aligned}
\end{equation}
and the dimension factor is
\begin{equation}\label{eqn:app-phase-DN}
D_N\defeq\frac{\mathcal S_{\text{s-SGD}}T_0^{\text{s-SGD}}}{\mathcal S_{\text{s-SVD}}T_0^{\text{s-SVD}}}=\frac{\pi H_N(\alpha)}{H_N(\alpha/2)} .
\end{equation}
\item The dimensionless risks solve
$Y_j=f_{N,q_j}+\sqrt\epsilon\,g_j*\sqrt{Y_j}$, with $f_{N,q}$ of
\cref{eqn:app-phase-fNq} and
\begin{equation}\label{eqn:app-phase-kernels}
g_{\text{s-SVD}}=\frac2{H_N(\alpha/2)}L_{N,\alpha,\alpha/2},\qquad
g_{\text{s-SGD}}=\frac{2(1-2/\pi)}N\,L_{N,\alpha,\alpha}+\frac4{\pi H_N(\alpha)}\,L_{N,2\alpha,\alpha} .
\end{equation}
Both kernels are positive, continuous and decreasing. The kernel
$g_{\text{s-SVD}}$ has integral $1$, and the two terms of $g_{\text{s-SGD}}$
have integrals $1-2/\pi$ and $2/\pi$. Their maxima are
\begin{equation}\label{eqn:app-phase-heights}
\begin{gathered}
k_{N,\text{s-SVD}}\defeq g_{\text{s-SVD}}(0)=\frac{2H_N(\alpha)}{H_N(\alpha/2)},\\
k_{N,\text{s-SGD}}\defeq g_{\text{s-SGD}}(0)=\frac{2(1-2/\pi)H_N(\alpha)}N+\frac{4H_N(2\alpha)}{\pi H_N(\alpha)} .
\end{gathered}
\end{equation}
\item If $\hat u_j<\infty$, then
\begin{equation}\label{eqn:app-phase-time}
t^j_{T\epsilon}=\frac{\mathcal S_jT_0^j}{2\sqrt\epsilon}\int_0^{\hat u_j}\sqrt{Y_j(u)}\,\dif u .
\end{equation}
\item As $N\to\infty$ at fixed $\alpha$,
\begin{equation}\label{eqn:app-phase-DN-asymp}
D_N\sim\begin{cases}
\pi\,\dfrac{1-\alpha/2}{1-\alpha}\,N^{-\alpha/2},&0<\alpha<1,\\[4pt]
\dfrac\pi2N^{-1/2}\log N,&\alpha=1,\\[4pt]
\pi(1-\alpha/2)\,\zeta(\alpha)\,N^{\alpha/2-1},&1<\alpha<2,\\[4pt]
\pi\zeta(2)/\log N,&\alpha=2,\\[4pt]
\pi\zeta(\alpha)/\zeta(\alpha/2),&\alpha>2.
\end{cases}
\end{equation}
\end{enumerate}
\end{proposition}
``` -/
theorem prop_app_phase_prefactors_i (α ς : ℝ) (N B : ℕ) (hα : 0 < α) (hp : 1 < α + ς)
    (hN : 1 ≤ N) (hNB : N ≤ B) (ε : ℝ) (hε : 0 < ε) :
    (svdArrays α ς N B).S = 1 / 2 * Real.sqrt (gammaRat N B) * Hsum (α / 2) N ∧
    matchedStep (svdArrays α ς N B) ε
        = 4 * Real.sqrt ε / (Real.sqrt (gammaRat N B) * Hsum (α / 2) N) ∧
    (sgdArrays α ς N B).S = (N : ℝ) ^ 2 / 2 * Real.sqrt (Real.pi * muBarOf α N / (B : ℝ)) ∧
    matchedStep (sgdArrays α ς N B) ε
        = 4 * Real.sqrt ε / (N : ℝ) ^ 2 * Real.sqrt ((B : ℝ) / (Real.pi * muBarOf α N)) ∧
    (svdArrays α ς N B).S * svdT0 N B = gammaRat N B / 2 * Hsum (α / 2) N ∧
    (sgdArrays α ς N B).S * sgdT0 α N B
        = Real.pi * (N : ℝ) ^ 2 * muBarOf α N / (2 * (B : ℝ)) ∧
    Real.pi * (N : ℝ) ^ 2 * muBarOf α N / (2 * (B : ℝ))
        = Real.pi * gammaRat N B / 2 * Hsum α N ∧
    (sgdArrays α ς N B).S * sgdT0 α N B / ((svdArrays α ς N B).S * svdT0 N B)
        = phaseDN α N := by
  have hγ := pa_gamma_pos hN hNB
  have hγne : gammaRat N B ≠ 0 := hγ.ne'
  have hsγ : 0 < Real.sqrt (gammaRat N B) := Real.sqrt_pos.2 hγ
  have hH1 : 0 < Hsum (α / 2) N := pa_Hsum_pos (α / 2) hN
  have hHα : 0 < Hsum α N := pa_Hsum_pos α hN
  have hNpos : (0 : ℝ) < N := Nat.cast_pos.mpr (by omega)
  have hB : (0 : ℝ) < B := Nat.cast_pos.mpr (by omega)
  have hm := pa_muBar_pos α hN
  have hS1 := pa_svd_S α ς N B hN hNB
  have hS2 := pa_sgd_S α ς N B hN hNB
  have hsq1 : Real.sqrt (gammaRat N B) * Real.sqrt (gammaRat N B) = gammaRat N B :=
    Real.mul_self_sqrt hγ.le
  have hsq2 : Real.sqrt (Real.pi * muBarOf α N / (B : ℝ)) * Real.sqrt (Real.pi * muBarOf α N / (B : ℝ))
      = Real.pi * muBarOf α N / (B : ℝ) :=
    Real.mul_self_sqrt (div_pos (mul_pos Real.pi_pos hm) hB).le
  have hst : Real.sqrt ((B : ℝ) / (Real.pi * muBarOf α N)) * Real.sqrt (Real.pi * muBarOf α N / (B : ℝ)) = 1 := by
    rw [← Real.sqrt_mul (div_pos hB (mul_pos Real.pi_pos hm)).le]
    rw [show (B : ℝ) / (Real.pi * muBarOf α N) * (Real.pi * muBarOf α N / (B : ℝ)) = 1 by
      have := hB.ne'; have := hm.ne'; have := Real.pi_pos.ne'; field_simp]
    exact Real.sqrt_one
  have hsG : 0 < Real.sqrt (Real.pi * muBarOf α N / (B : ℝ)) :=
    Real.sqrt_pos.2 (div_pos (mul_pos Real.pi_pos hm) hB)
  have h5 : (svdArrays α ς N B).S * svdT0 N B = gammaRat N B / 2 * Hsum (α / 2) N := by
    unfold svdT0; rw [hS1]; linear_combination (Hsum (α / 2) N / 2) * hsq1
  have h6 : (sgdArrays α ς N B).S * sgdT0 α N B
      = Real.pi * (N : ℝ) ^ 2 * muBarOf α N / (2 * (B : ℝ)) := by
    unfold sgdT0; rw [hS2]; linear_combination ((N : ℝ) ^ 2 / 2) * hsq2
  have h7 : Real.pi * (N : ℝ) ^ 2 * muBarOf α N / (2 * (B : ℝ))
      = Real.pi * gammaRat N B / 2 * Hsum α N := by
    unfold muBarOf gammaRat
    have := hB.ne'; have := hNpos.ne'
    field_simp
  refine ⟨hS1, ?_, hS2, ?_, h5, h6, h7, ?_⟩
  · unfold matchedStep; rw [hS1]
    have := hsγ.ne'; have := hH1.ne'
    field_simp
    norm_num
  · unfold matchedStep; rw [hS2, eq_inv_of_mul_eq_one_left hst]
    have := hsG.ne'; have := hNpos.ne'
    field_simp
    norm_num
  · unfold phaseDN; rw [h6, h5, h7]
    have := hγne; have := hH1.ne'
    field_simp

/-! ### Proof helpers for `prop:app-phase-prefactors` part (ii) (P-H.5.P2) -/

lemma pa_sum_fin_g (g : ℝ → ℝ) (N : ℕ) :
    ∑ i : Fin N, g (idxR i) = ∑ n ∈ Finset.Icc 1 N, g (n : ℝ) := by
  induction N with
  | zero => simp
  | succ n ih =>
    rw [Fin.sum_univ_castSucc]
    have h1 : ∀ i : Fin n, g (idxR (Fin.castSucc i)) = g (idxR i) := by
      intro i; simp [idxR]
    simp only [h1, ih]
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ n + 1)]
    simp [idxR]

lemma pa_Lsum_fin (N : ℕ) (a q u : ℝ) :
    Lsum (N : ℕ∞) a q u
      = ∑ i : Fin N, idxR i ^ (-a) * Real.exp (-(2 * u) * idxR i ^ (-q)) := by
  unfold Lsum
  rw [tsum_eq_sum (s := Finset.Icc 1 N)]
  · have hcongr : ∑ n ∈ Finset.Icc 1 N,
        (if 0 < n ∧ ((n : ℕ∞) ≤ (N : ℕ∞)) then
          (n : ℝ) ^ (-a) * Real.exp (-(2 * u) * (n : ℝ) ^ (-q)) else 0)
        = ∑ n ∈ Finset.Icc 1 N,
          (fun x : ℝ => x ^ (-a) * Real.exp (-(2 * u) * x ^ (-q))) (n : ℝ) := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [Finset.mem_Icc] at hn
      have h1 : 0 < n ∧ ((n : ℕ∞) ≤ (N : ℕ∞)) := ⟨by omega, by exact_mod_cast hn.2⟩
      rw [if_pos h1]
    rw [hcongr]
    exact (pa_sum_fin_g (fun x : ℝ => x ^ (-a) * Real.exp (-(2 * u) * x ^ (-q))) N).symm
  · intro b hb
    rw [if_neg]
    rintro ⟨h1, h2⟩
    apply hb
    rw [Finset.mem_Icc]
    exact ⟨by omega, by exact_mod_cast h2⟩

lemma pa_forcing_fin {N : ℕ} (m : RowModel (Fin N)) (s : ℝ) :
    m.forcing s = 1 / 2 * ∑ i : Fin N, m.μ i * m.Q0 i * Real.exp (-(2 * m.d i * s)) := by
  unfold RowModel.forcing
  rw [tsum_fintype]

lemma pa_dimKernel_fin {N : ℕ} (m : RowModel (Fin N)) (T0 ε S' u : ℝ) (hε : 0 < ε)
    (hS0 : S' ≠ 0) (hη : m.η = 2 * Real.sqrt ε / S') :
    dimKernel m T0 ε u
      = T0 / S' * ∑ i : Fin N, m.μ i * m.v i * Real.exp (-(2 * m.d i * (T0 * u))) := by
  unfold dimKernel RowModel.kernel
  rw [hη, tsum_fintype]
  have h1 := (Real.sqrt_pos.2 hε).ne'
  have hc : T0 * (2 * Real.sqrt ε / S' / 2) / Real.sqrt ε = T0 / S' := by
    field_simp
    try ring
  linear_combination (∑ i : Fin N, m.μ i * m.v i * Real.exp (-(2 * m.d i * (T0 * u)))) * hc

lemma pa_exp_cancel_l (x c c' u : ℝ) (h : c * c' = 1) :
    Real.exp (-(2 * (c * x) * (c' * u))) = Real.exp (-(2 * u) * x) := by
  congr 1
  linear_combination (-2 * x * u) * h

lemma pa_exp_cancel_r (x c c' u : ℝ) (h : c * c' = 1) :
    Real.exp (-(2 * (x * c) * (c' * u))) = Real.exp (-(2 * u) * x) := by
  congr 1
  linear_combination (-2 * x * u) * h

lemma pa_svd_cc (g : ℝ) (hg : 0 < g) : g ^ (-(1 / 2 : ℝ)) * Real.sqrt g = 1 := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_add hg]; norm_num

lemma pa_sgd_cc (B' m : ℝ) (hB : 0 < B') (hm : 0 < m) :
    Real.sqrt (B' / (Real.pi * m)) * Real.sqrt (Real.pi * m / B') = 1 := by
  have h1 := hB.ne'
  have h2 := hm.ne'
  have h3 := Real.pi_pos.ne'
  rw [← Real.sqrt_mul (div_pos hB (mul_pos Real.pi_pos hm)).le]
  rw [show B' / (Real.pi * m) * (Real.pi * m / B') = 1 by field_simp]
  exact Real.sqrt_one

lemma pa_muOf_eq (α : ℝ) (N : ℕ) (i : Fin N) : muOf α N i = idxR i ^ (-α) := rfl

lemma pa_svd_forcing_term (α ς : ℝ) (N B : ℕ) (hN : 1 ≤ N) (hNB : N ≤ B) (u : ℝ)
    (i : Fin N) :
    (svdArrays α ς N B).μ i * (svdArrays α ς N B).Q0 i
        * Real.exp (-(2 * (svdArrays α ς N B).d i * (svdT0 N B * u)))
      = idxR i ^ (-(α + ς)) * Real.exp (-(2 * u) * idxR i ^ (-(α / 2))) := by
  have hγ := pa_gamma_pos hN hNB
  show muOf α N i * Q0Of ς N i
      * Real.exp (-(2 * (gammaRat N B ^ (-(1 / 2 : ℝ)) * idxR i ^ (-(α / 2)))
          * (Real.sqrt (gammaRat N B) * u))) = _
  rw [pa_mu_Q0, pa_exp_cancel_l _ _ _ _ (pa_svd_cc _ hγ)]

lemma pa_svd_kernel_term (α ς : ℝ) (N B : ℕ) (hN : 1 ≤ N) (hNB : N ≤ B) (u : ℝ)
    (i : Fin N) :
    (svdArrays α ς N B).μ i * (svdArrays α ς N B).v i
        * Real.exp (-(2 * (svdArrays α ς N B).d i * (svdT0 N B * u)))
      = idxR i ^ (-α) * Real.exp (-(2 * u) * idxR i ^ (-(α / 2))) := by
  have hγ := pa_gamma_pos hN hNB
  show muOf α N i * 1
      * Real.exp (-(2 * (gammaRat N B ^ (-(1 / 2 : ℝ)) * idxR i ^ (-(α / 2)))
          * (Real.sqrt (gammaRat N B) * u))) = _
  rw [mul_one, pa_muOf_eq, pa_exp_cancel_l _ _ _ _ (pa_svd_cc _ hγ)]

lemma pa_sgd_forcing_term (α ς : ℝ) (N B : ℕ) (hN : 1 ≤ N) (hNB : N ≤ B) (u : ℝ)
    (i : Fin N) :
    (sgdArrays α ς N B).μ i * (sgdArrays α ς N B).Q0 i
        * Real.exp (-(2 * (sgdArrays α ς N B).d i * (sgdT0 α N B * u)))
      = idxR i ^ (-(α + ς)) * Real.exp (-(2 * u) * idxR i ^ (-α)) := by
  have hB : (0 : ℝ) < B := Nat.cast_pos.mpr (by omega)
  have hm := pa_muBar_pos α hN
  show muOf α N i * Q0Of ς N i
      * Real.exp (-(2 * (muOf α N i * Real.sqrt ((B : ℝ) / (Real.pi * muBarOf α N)))
          * (Real.sqrt (Real.pi * muBarOf α N / (B : ℝ)) * u))) = _
  rw [pa_mu_Q0, pa_exp_cancel_r _ _ _ _ (pa_sgd_cc (B : ℝ) (muBarOf α N) hB hm), pa_muOf_eq]

lemma pa_sgd_kernel_alg (x E Nr H : ℝ) (hN : 0 < Nr) (hH : 0 < H) :
    2 / Nr ^ 2 * (x * (Nr * (1 + 2 / Real.pi * (x / (H / Nr) - 1))) * E)
      = 2 * (1 - 2 / Real.pi) / Nr * (x * E) + 4 / (Real.pi * H) * (x * x * E) := by
  have h1 := hN.ne'
  have h2 := hH.ne'
  have h3 := Real.pi_pos.ne'
  field_simp
  ring

lemma pa_sgd_kernel_term (α ς : ℝ) (N B : ℕ) (hN : 1 ≤ N) (hNB : N ≤ B) (u : ℝ)
    (i : Fin N) :
    2 / (N : ℝ) ^ 2 * ((sgdArrays α ς N B).μ i * (sgdArrays α ς N B).v i
        * Real.exp (-(2 * (sgdArrays α ς N B).d i * (sgdT0 α N B * u))))
      = 2 * (1 - 2 / Real.pi) / (N : ℝ) * (idxR i ^ (-α) * Real.exp (-(2 * u) * idxR i ^ (-α)))
        + 4 / (Real.pi * Hsum α N) * (idxR i ^ (-(2 * α)) * Real.exp (-(2 * u) * idxR i ^ (-α))) := by
  have hB : (0 : ℝ) < B := Nat.cast_pos.mpr (by omega)
  have hN0 : (0 : ℝ) < N := Nat.cast_pos.mpr (by omega)
  have hm := pa_muBar_pos α hN
  have hH : 0 < Hsum α N := pa_Hsum_pos α hN
  have hx2 : idxR i ^ (-(2 * α)) = idxR i ^ (-α) * idxR i ^ (-α) := by
    rw [← Real.rpow_add (pa_idx_pos i)]; congr 1; ring
  show 2 / (N : ℝ) ^ 2 * (muOf α N i * ((N : ℝ) * (1 + 2 / Real.pi * (muOf α N i / muBarOf α N - 1)))
      * Real.exp (-(2 * (muOf α N i * Real.sqrt ((B : ℝ) / (Real.pi * muBarOf α N)))
          * (Real.sqrt (Real.pi * muBarOf α N / (B : ℝ)) * u)))) = _
  rw [pa_exp_cancel_r _ _ _ _ (pa_sgd_cc (B : ℝ) (muBarOf α N) hB hm), hx2, pa_muOf_eq]
  unfold muBarOf
  exact pa_sgd_kernel_alg _ _ _ _ hN0 hH

lemma pa_conv_scale (f k : ℝ → ℝ) (T0 ε u : ℝ) (hT : 0 < T0) (hε : 0 < ε) :
    oneSidedConv (fun v => f (T0 * v)) (fun s => T0 * k (T0 * s) / Real.sqrt ε) u
      = 1 / Real.sqrt ε * oneSidedConv f k (T0 * u) := by
  have hs : Real.sqrt ε ≠ 0 := (Real.sqrt_pos.2 hε).ne'
  have hT0 : T0 ≠ 0 := hT.ne'
  have h1 : ∫ s in (0 : ℝ)..u, f (T0 * (u - s)) * (T0 * k (T0 * s) / Real.sqrt ε)
      = (T0 / Real.sqrt ε) * ∫ s in (0 : ℝ)..u, f (T0 * u - T0 * s) * k (T0 * s) := by
    rw [← intervalIntegral.integral_const_mul]
    congr 1
    funext s
    rw [mul_sub]
    ring
  have h2 := intervalIntegral.integral_comp_mul_left (f := fun x => f (T0 * u - x) * k x)
    (a := (0 : ℝ)) (b := u) (c := T0) hT0
  simp only [mul_zero, smul_eq_mul] at h2
  simp only [oneSidedConv]
  rw [h1, h2]
  field_simp
  try ring

/-- Label `prop:app-phase-prefactors`, part (ii): the dimensionless risks solve
`Y_j = f_{N,q_j} + √ε g_j * √Y_j` with `Y_j(u) = Q_j(T_0 u)`, the forcing is `F_j(T_0 u) = f_{N,q_j}(u)`,
and the kernels are the closed forms of `eqn:app-phase-kernels`. Here `Q_j` is any Volterra solution
(`IsVolterraSol`) of the model with the matched step. Snapshot `cr-2026-10-23`. Statement (verbatim,
`sections/07-phase-comparison/section.tex`):

Source lines: section.tex l.1116–1166.
```latex
\begin{proposition}[Noise constants, kernels and clocks]\label{prop:app-phase-prefactors}
The arrays of \cref{def:app-phase-arrays} satisfy (M1), with
$F_0=\frac12H_N(p)$, and the following hold.
\begin{enumerate}[label=(\roman*)]
\item The noise constants, matched steps and time-scale products are
\begin{equation}\label{eqn:app-phase-ST0}
\begin{aligned}
\mathcal S_{\text{s-SVD}}&=\tfrac12\sqrt\gamma\,H_N(\alpha/2),&\quad
\lr^\star_{\text{s-SVD}}&=\frac{4\sqrt\epsilon}{\sqrt\gamma\,H_N(\alpha/2)},\\
\mathcal S_{\text{s-SGD}}&=\frac{N^2}2\sqrt{\frac{\pi\bar\mu}B},&\quad
\lr^\star_{\text{s-SGD}}&=\frac{4\sqrt\epsilon}{N^2}\sqrt{\frac B{\pi\bar\mu}},\\
\mathcal S_{\text{s-SVD}}T_0^{\text{s-SVD}}&=\tfrac\gamma2H_N(\alpha/2),&\quad
\mathcal S_{\text{s-SGD}}T_0^{\text{s-SGD}}&=\frac{\pi N^2\bar\mu}{2B}=\tfrac{\pi\gamma}2H_N(\alpha),
\end{aligned}
\end{equation}
and the dimension factor is
\begin{equation}\label{eqn:app-phase-DN}
D_N\defeq\frac{\mathcal S_{\text{s-SGD}}T_0^{\text{s-SGD}}}{\mathcal S_{\text{s-SVD}}T_0^{\text{s-SVD}}}=\frac{\pi H_N(\alpha)}{H_N(\alpha/2)} .
\end{equation}
\item The dimensionless risks solve
$Y_j=f_{N,q_j}+\sqrt\epsilon\,g_j*\sqrt{Y_j}$, with $f_{N,q}$ of
\cref{eqn:app-phase-fNq} and
\begin{equation}\label{eqn:app-phase-kernels}
g_{\text{s-SVD}}=\frac2{H_N(\alpha/2)}L_{N,\alpha,\alpha/2},\qquad
g_{\text{s-SGD}}=\frac{2(1-2/\pi)}N\,L_{N,\alpha,\alpha}+\frac4{\pi H_N(\alpha)}\,L_{N,2\alpha,\alpha} .
\end{equation}
Both kernels are positive, continuous and decreasing. The kernel
$g_{\text{s-SVD}}$ has integral $1$, and the two terms of $g_{\text{s-SGD}}$
have integrals $1-2/\pi$ and $2/\pi$. Their maxima are
\begin{equation}\label{eqn:app-phase-heights}
\begin{gathered}
k_{N,\text{s-SVD}}\defeq g_{\text{s-SVD}}(0)=\frac{2H_N(\alpha)}{H_N(\alpha/2)},\\
k_{N,\text{s-SGD}}\defeq g_{\text{s-SGD}}(0)=\frac{2(1-2/\pi)H_N(\alpha)}N+\frac{4H_N(2\alpha)}{\pi H_N(\alpha)} .
\end{gathered}
\end{equation}
\item If $\hat u_j<\infty$, then
\begin{equation}\label{eqn:app-phase-time}
t^j_{T\epsilon}=\frac{\mathcal S_jT_0^j}{2\sqrt\epsilon}\int_0^{\hat u_j}\sqrt{Y_j(u)}\,\dif u .
\end{equation}
\item As $N\to\infty$ at fixed $\alpha$,
\begin{equation}\label{eqn:app-phase-DN-asymp}
D_N\sim\begin{cases}
\pi\,\dfrac{1-\alpha/2}{1-\alpha}\,N^{-\alpha/2},&0<\alpha<1,\\[4pt]
\dfrac\pi2N^{-1/2}\log N,&\alpha=1,\\[4pt]
\pi(1-\alpha/2)\,\zeta(\alpha)\,N^{\alpha/2-1},&1<\alpha<2,\\[4pt]
\pi\zeta(2)/\log N,&\alpha=2,\\[4pt]
\pi\zeta(\alpha)/\zeta(\alpha/2),&\alpha>2.
\end{cases}
\end{equation}
\end{enumerate}
\end{proposition}
``` -/
theorem prop_app_phase_prefactors_ii (α ς : ℝ) (N B : ℕ) (hα : 0 < α) (hp : 1 < α + ς)
    (hN : 1 ≤ N) (hNB : N ≤ B) (ε : ℝ) (hε : 0 < ε) (mS mG : RowModel (Fin N))
    (hmS : IsMatchedModel (svdArrays α ς N B) mS ε)
    (hmG : IsMatchedModel (sgdArrays α ς N B) mG ε)
    (QS QG : ℝ → ℝ) (hQS : IsVolterraSol mS QS) (hQG : IsVolterraSol mG QG) :
    (∀ u, 0 ≤ u → mS.forcing (svdT0 N B * u) = fNq (N : ℕ∞) (α + ς) (α / 2) u) ∧
    (∀ u, 0 ≤ u → mG.forcing (sgdT0 α N B * u) = fNq (N : ℕ∞) (α + ς) α u) ∧
    (∀ u, 0 ≤ u → QS (svdT0 N B * u) = fNq (N : ℕ∞) (α + ς) (α / 2) u +
        Real.sqrt ε * oneSidedConv (fun v => Real.sqrt (QS (svdT0 N B * v)))
          (dimKernel mS (svdT0 N B) ε) u) ∧
    (∀ u, 0 ≤ u → QG (sgdT0 α N B * u) = fNq (N : ℕ∞) (α + ς) α u +
        Real.sqrt ε * oneSidedConv (fun v => Real.sqrt (QG (sgdT0 α N B * v)))
          (dimKernel mG (sgdT0 α N B) ε) u) ∧
    (∀ u, 0 ≤ u → dimKernel mS (svdT0 N B) ε u
        = 2 / Hsum (α / 2) N * Lsum (N : ℕ∞) α (α / 2) u) ∧
    (∀ u, 0 ≤ u → dimKernel mG (sgdT0 α N B) ε u
        = 2 * (1 - 2 / Real.pi) / (N : ℝ) * Lsum (N : ℕ∞) α α u
          + 4 / (Real.pi * Hsum α N) * Lsum (N : ℕ∞) (2 * α) α u) := by
  have hN0 : (0 : ℝ) < N := Nat.cast_pos.mpr (by omega)
  have hB0 : (0 : ℝ) < B := Nat.cast_pos.mpr (by omega)
  have hγ := pa_gamma_pos hN hNB
  have hsγ : 0 < Real.sqrt (gammaRat N B) := Real.sqrt_pos.2 hγ
  have hH1 : 0 < Hsum (α / 2) N := pa_Hsum_pos (α / 2) hN
  have hm := pa_muBar_pos α hN
  have hT : 0 < svdT0 N B := hsγ
  have hsG : 0 < Real.sqrt (Real.pi * muBarOf α N / (B : ℝ)) :=
    Real.sqrt_pos.2 (div_pos (mul_pos Real.pi_pos hm) hB0)
  have hT' : 0 < sgdT0 α N B := hsG
  have hsε : 0 < Real.sqrt ε := Real.sqrt_pos.2 hε
  obtain ⟨hμS, hdS, hvS, hQS0, hηS⟩ := hmS
  obtain ⟨hμG, hdG, hvG, hQG0, hηG⟩ := hmG
  have hηS' : mS.η = 2 * Real.sqrt ε / (svdArrays α ς N B).S := hηS
  have hηG' : mG.η = 2 * Real.sqrt ε / (sgdArrays α ς N B).S := hηG
  have hSS : (svdArrays α ς N B).S ≠ 0 := by
    rw [pa_svd_S α ς N B hN hNB]
    exact (mul_pos (mul_pos (by norm_num) hsγ) hH1).ne'
  have hSG : (sgdArrays α ς N B).S ≠ 0 := by
    rw [pa_sgd_S α ς N B hN hNB]
    exact (mul_pos (div_pos (pow_pos hN0 2) two_pos) hsG).ne'
  have hrS : svdT0 N B / (svdArrays α ς N B).S = 2 / Hsum (α / 2) N := by
    rw [pa_svd_S α ς N B hN hNB]
    unfold svdT0
    have := hsγ.ne'
    have := hH1.ne'
    field_simp
    try ring
  have hrG : sgdT0 α N B / (sgdArrays α ς N B).S = 2 / (N : ℝ) ^ 2 := by
    rw [pa_sgd_S α ς N B hN hNB]
    unfold sgdT0
    have := hsG.ne'
    have := hN0.ne'
    field_simp
    try ring
  have hFS : ∀ u, 0 ≤ u → mS.forcing (svdT0 N B * u) = fNq (N : ℕ∞) (α + ς) (α / 2) u := by
    intro u _
    unfold fNq
    rw [pa_Lsum_fin, pa_forcing_fin, hμS, hQS0, hdS]
    congr 1
    exact Finset.sum_congr rfl (fun i _ => pa_svd_forcing_term α ς N B hN hNB u i)
  have hFG : ∀ u, 0 ≤ u → mG.forcing (sgdT0 α N B * u) = fNq (N : ℕ∞) (α + ς) α u := by
    intro u _
    unfold fNq
    rw [pa_Lsum_fin, pa_forcing_fin, hμG, hQG0, hdG]
    congr 1
    exact Finset.sum_congr rfl (fun i _ => pa_sgd_forcing_term α ς N B hN hNB u i)
  refine ⟨hFS, hFG, ?_, ?_, ?_, ?_⟩
  · intro u hu
    have hV := hQS.2.2 (svdT0 N B * u) (Set.mem_Ici.2 (mul_nonneg hT.le hu))
    have hc := pa_conv_scale (fun w => Real.sqrt (QS w)) mS.kernel (svdT0 N B) ε u hT hε
    try simp only at hc
    rw [hV, hFS u hu]
    change _ = _ + Real.sqrt ε * oneSidedConv (fun v => Real.sqrt (QS (svdT0 N B * v)))
      (fun s => svdT0 N B * mS.kernel (svdT0 N B * s) / Real.sqrt ε) u
    rw [hc, ← mul_assoc, mul_one_div_cancel hsε.ne', one_mul]
  · intro u hu
    have hV := hQG.2.2 (sgdT0 α N B * u) (Set.mem_Ici.2 (mul_nonneg hT'.le hu))
    have hc := pa_conv_scale (fun w => Real.sqrt (QG w)) mG.kernel (sgdT0 α N B) ε u hT' hε
    try simp only at hc
    rw [hV, hFG u hu]
    change _ = _ + Real.sqrt ε * oneSidedConv (fun v => Real.sqrt (QG (sgdT0 α N B * v)))
      (fun s => sgdT0 α N B * mG.kernel (sgdT0 α N B * s) / Real.sqrt ε) u
    rw [hc, ← mul_assoc, mul_one_div_cancel hsε.ne', one_mul]
  · intro u _
    rw [pa_dimKernel_fin mS (svdT0 N B) ε (svdArrays α ς N B).S u hε hSS hηS', hrS,
      pa_Lsum_fin, Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [hμS, hvS, hdS, pa_svd_kernel_term α ς N B hN hNB u i]
  · intro u _
    rw [pa_dimKernel_fin mG (sgdT0 α N B) ε (sgdArrays α ς N B).S u hε hSG hηG', hrG,
      pa_Lsum_fin, pa_Lsum_fin]
    simp only [Finset.mul_sum]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [hμG, hvG, hdG]
    exact pa_sgd_kernel_term α ς N B hN hNB u i

/-! ### Proof helpers for `prop:app-phase-prefactors` part (ii) kernel properties (P-H.5.P3) -/

lemma pa_idx_pow_pos {N : ℕ} (a : ℝ) (i : Fin N) : 0 < idxR i ^ (-a) :=
  Real.rpow_pos_of_pos (pa_idx_pos i) _

lemma pa_pow_split (x a : ℝ) (hx : 0 < x) :
    x ^ (-a) = x ^ (-(a / 2)) * x ^ (-(a / 2)) := by
  rw [← Real.rpow_add hx]; congr 1; ring

lemma pa_exp_int_Ioi (c : ℝ) (hc : 0 < c) :
    IntegrableOn (fun u : ℝ => Real.exp (-(2 * u) * c)) (Ioi 0) := by
  refine (exp_neg_integrableOn_Ioi 0 (show (0 : ℝ) < 2 * c by positivity)).congr_fun ?_
    measurableSet_Ioi
  intro u _
  show Real.exp (-(2 * c) * u) = Real.exp (-(2 * u) * c)
  congr 1; ring

lemma pa_exp_integral_Ioi (c : ℝ) (hc : 0 < c) :
    ∫ u in Ioi (0 : ℝ), Real.exp (-(2 * u) * c) = 1 / (2 * c) := by
  have h : ∫ x in Ioi (0 : ℝ), Real.exp (-((2 * c) * x))
      = (2 * c)⁻¹ • ∫ x in Ioi ((2 * c) * 0), Real.exp (-x) :=
    integral_comp_mul_left_Ioi (fun x : ℝ => Real.exp (-x)) 0 (show (0 : ℝ) < 2 * c by positivity)
  have h2 : (fun u : ℝ => Real.exp (-(2 * u) * c)) = fun u => Real.exp (-((2 * c) * u)) := by
    funext u; congr 1; ring
  rw [h2, h, mul_zero, integral_exp_neg_Ioi_zero, smul_eq_mul, mul_one, one_div]

lemma pa_fin_pos {N : ℕ} (a b : Fin N → ℝ) (ha : ∀ i, 0 < a i) (hN : 1 ≤ N) (u : ℝ) :
    0 < ∑ i, a i * Real.exp (-(2 * u) * b i) :=
  Finset.sum_pos (fun i _ => mul_pos (ha i) (Real.exp_pos _)) ⟨⟨0, by omega⟩, Finset.mem_univ _⟩

lemma pa_fin_cont {N : ℕ} (a b : Fin N → ℝ) :
    Continuous (fun u : ℝ => ∑ i, a i * Real.exp (-(2 * u) * b i)) := by
  apply continuous_finset_sum
  intro i _
  fun_prop

lemma pa_fin_anti {N : ℕ} (a b : Fin N → ℝ) (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i) :
    Antitone (fun u : ℝ => ∑ i, a i * Real.exp (-(2 * u) * b i)) := by
  intro u v huv
  show ∑ i, a i * Real.exp (-(2 * v) * b i) ≤ ∑ i, a i * Real.exp (-(2 * u) * b i)
  apply Finset.sum_le_sum
  intro i _
  refine mul_le_mul_of_nonneg_left ?_ (ha i)
  apply Real.exp_le_exp.2
  nlinarith [mul_nonneg (hb i) (sub_nonneg.2 huv)]

lemma pa_fin_exp_integrable {N : ℕ} (a b : Fin N → ℝ) (hb : ∀ i, 0 < b i) :
    IntegrableOn (fun u : ℝ => ∑ i, a i * Real.exp (-(2 * u) * b i)) (Ioi 0) :=
  integrable_finset_sum Finset.univ
    (fun i _ => Integrable.const_mul (pa_exp_int_Ioi (b i) (hb i)) (a i))

lemma pa_fin_exp_integral {N : ℕ} (a b : Fin N → ℝ) (hb : ∀ i, 0 < b i) :
    ∫ u in Ioi (0 : ℝ), ∑ i, a i * Real.exp (-(2 * u) * b i) = ∑ i, a i / (2 * b i) := by
  rw [integral_finset_sum Finset.univ
    (fun i _ => Integrable.const_mul (pa_exp_int_Ioi (b i) (hb i)) (a i))]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_const_mul, pa_exp_integral_Ioi (b i) (hb i), mul_one_div]

/-- Label `prop:app-phase-prefactors`, part (ii) (kernel properties): both dimensionless kernels are
positive, continuous and decreasing on `[0,∞)`; the \SignSVD kernel has integral `1`; the two terms
of the \SignSGD kernel have integrals `1 - 2/π` and `2/π`; the maxima are at `0` and equal
`k_{N,j} = g_j(0)` (`eqn:app-phase-heights`). Snapshot `cr-2026-10-23`. Statement (verbatim,
`sections/07-phase-comparison/section.tex`):

Source lines: section.tex l.1116–1166.
```latex
\begin{proposition}[Noise constants, kernels and clocks]\label{prop:app-phase-prefactors}
The arrays of \cref{def:app-phase-arrays} satisfy (M1), with
$F_0=\frac12H_N(p)$, and the following hold.
\begin{enumerate}[label=(\roman*)]
\item The noise constants, matched steps and time-scale products are
\begin{equation}\label{eqn:app-phase-ST0}
\begin{aligned}
\mathcal S_{\text{s-SVD}}&=\tfrac12\sqrt\gamma\,H_N(\alpha/2),&\quad
\lr^\star_{\text{s-SVD}}&=\frac{4\sqrt\epsilon}{\sqrt\gamma\,H_N(\alpha/2)},\\
\mathcal S_{\text{s-SGD}}&=\frac{N^2}2\sqrt{\frac{\pi\bar\mu}B},&\quad
\lr^\star_{\text{s-SGD}}&=\frac{4\sqrt\epsilon}{N^2}\sqrt{\frac B{\pi\bar\mu}},\\
\mathcal S_{\text{s-SVD}}T_0^{\text{s-SVD}}&=\tfrac\gamma2H_N(\alpha/2),&\quad
\mathcal S_{\text{s-SGD}}T_0^{\text{s-SGD}}&=\frac{\pi N^2\bar\mu}{2B}=\tfrac{\pi\gamma}2H_N(\alpha),
\end{aligned}
\end{equation}
and the dimension factor is
\begin{equation}\label{eqn:app-phase-DN}
D_N\defeq\frac{\mathcal S_{\text{s-SGD}}T_0^{\text{s-SGD}}}{\mathcal S_{\text{s-SVD}}T_0^{\text{s-SVD}}}=\frac{\pi H_N(\alpha)}{H_N(\alpha/2)} .
\end{equation}
\item The dimensionless risks solve
$Y_j=f_{N,q_j}+\sqrt\epsilon\,g_j*\sqrt{Y_j}$, with $f_{N,q}$ of
\cref{eqn:app-phase-fNq} and
\begin{equation}\label{eqn:app-phase-kernels}
g_{\text{s-SVD}}=\frac2{H_N(\alpha/2)}L_{N,\alpha,\alpha/2},\qquad
g_{\text{s-SGD}}=\frac{2(1-2/\pi)}N\,L_{N,\alpha,\alpha}+\frac4{\pi H_N(\alpha)}\,L_{N,2\alpha,\alpha} .
\end{equation}
Both kernels are positive, continuous and decreasing. The kernel
$g_{\text{s-SVD}}$ has integral $1$, and the two terms of $g_{\text{s-SGD}}$
have integrals $1-2/\pi$ and $2/\pi$. Their maxima are
\begin{equation}\label{eqn:app-phase-heights}
\begin{gathered}
k_{N,\text{s-SVD}}\defeq g_{\text{s-SVD}}(0)=\frac{2H_N(\alpha)}{H_N(\alpha/2)},\\
k_{N,\text{s-SGD}}\defeq g_{\text{s-SGD}}(0)=\frac{2(1-2/\pi)H_N(\alpha)}N+\frac{4H_N(2\alpha)}{\pi H_N(\alpha)} .
\end{gathered}
\end{equation}
\item If $\hat u_j<\infty$, then
\begin{equation}\label{eqn:app-phase-time}
t^j_{T\epsilon}=\frac{\mathcal S_jT_0^j}{2\sqrt\epsilon}\int_0^{\hat u_j}\sqrt{Y_j(u)}\,\dif u .
\end{equation}
\item As $N\to\infty$ at fixed $\alpha$,
\begin{equation}\label{eqn:app-phase-DN-asymp}
D_N\sim\begin{cases}
\pi\,\dfrac{1-\alpha/2}{1-\alpha}\,N^{-\alpha/2},&0<\alpha<1,\\[4pt]
\dfrac\pi2N^{-1/2}\log N,&\alpha=1,\\[4pt]
\pi(1-\alpha/2)\,\zeta(\alpha)\,N^{\alpha/2-1},&1<\alpha<2,\\[4pt]
\pi\zeta(2)/\log N,&\alpha=2,\\[4pt]
\pi\zeta(\alpha)/\zeta(\alpha/2),&\alpha>2.
\end{cases}
\end{equation}
\end{enumerate}
\end{proposition}
``` -/
theorem prop_app_phase_prefactors_ii_props (α ς : ℝ) (N B : ℕ) (hα : 0 < α) (hp : 1 < α + ς)
    (hN : 1 ≤ N) (hNB : N ≤ B) (ε : ℝ) (hε : 0 < ε) (mS mG : RowModel (Fin N))
    (hmS : IsMatchedModel (svdArrays α ς N B) mS ε)
    (hmG : IsMatchedModel (sgdArrays α ς N B) mG ε) :
    ((∀ u, 0 ≤ u → 0 < dimKernel mS (svdT0 N B) ε u) ∧
      ContinuousOn (dimKernel mS (svdT0 N B) ε) (Ici 0) ∧
      AntitoneOn (dimKernel mS (svdT0 N B) ε) (Ici 0) ∧
      IntegrableOn (dimKernel mS (svdT0 N B) ε) (Ioi (0 : ℝ)) ∧
      ∫ u in Ioi (0 : ℝ), dimKernel mS (svdT0 N B) ε u = 1 ∧
      IsMaxOn (dimKernel mS (svdT0 N B) ε) (Ici 0) 0 ∧
      dimKernel mS (svdT0 N B) ε 0 = phaseKsvd α N) ∧
    ((∀ u, 0 ≤ u → 0 < dimKernel mG (sgdT0 α N B) ε u) ∧
      ContinuousOn (dimKernel mG (sgdT0 α N B) ε) (Ici 0) ∧
      AntitoneOn (dimKernel mG (sgdT0 α N B) ε) (Ici 0) ∧
      IsMaxOn (dimKernel mG (sgdT0 α N B) ε) (Ici 0) 0 ∧
      dimKernel mG (sgdT0 α N B) ε 0 = phaseKsgd α N ∧
      IntegrableOn (fun u => 2 * (1 - 2 / Real.pi) / (N : ℝ) * Lsum (N : ℕ∞) α α u)
        (Ioi (0 : ℝ)) ∧
      ∫ u in Ioi (0 : ℝ), 2 * (1 - 2 / Real.pi) / (N : ℝ) * Lsum (N : ℕ∞) α α u
        = 1 - 2 / Real.pi ∧
      IntegrableOn (fun u => 4 / (Real.pi * Hsum α N) * Lsum (N : ℕ∞) (2 * α) α u)
        (Ioi (0 : ℝ)) ∧
      ∫ u in Ioi (0 : ℝ), 4 / (Real.pi * Hsum α N) * Lsum (N : ℕ∞) (2 * α) α u
        = 2 / Real.pi) := by
  have hγ := pa_gamma_pos hN hNB
  have hB : (0 : ℝ) < B := Nat.cast_pos.mpr (by omega)
  have hN0 : (0 : ℝ) < N := Nat.cast_pos.mpr (by omega)
  have hm := pa_muBar_pos α hN
  have hH0 : 0 < Hsum α N := pa_Hsum_pos α hN
  have hH1 : 0 < Hsum (α / 2) N := pa_Hsum_pos (α / 2) hN
  have hpi : 0 < Real.pi := Real.pi_pos
  -- ## SVD kernel
  have hS_svd : (svdArrays α ς N B).S ≠ 0 := by
    rw [pa_svd_S α ς N B hN hNB]
    have := Real.sqrt_pos.2 hγ
    exact (mul_pos (mul_pos (by norm_num) this) hH1).ne'
  have hη_s : mS.η = 2 * Real.sqrt ε / (svdArrays α ς N B).S := hmS.2.2.2.2
  have hT_s : svdT0 N B / (1 / 2 * Real.sqrt (gammaRat N B) * Hsum (α / 2) N)
      = 2 / Hsum (α / 2) N := by
    unfold svdT0
    have := Real.sqrt_pos.2 hγ
    have := hH1.ne'
    field_simp
  have hKs : ∀ u, dimKernel mS (svdT0 N B) ε u
      = 2 / Hsum (α / 2) N * ∑ i : Fin N,
          idxR i ^ (-α) * Real.exp (-(2 * u) * idxR i ^ (-(α / 2))) := by
    intro u
    rw [pa_dimKernel_fin mS _ ε _ u hε hS_svd hη_s, hmS.1, hmS.2.1, hmS.2.2.1,
      pa_svd_S α ς N B hN hNB, hT_s]
    congr 1
    exact Finset.sum_congr rfl (fun i _ => pa_svd_kernel_term α ς N B hN hNB u i)
  have hKs_fun : dimKernel mS (svdT0 N B) ε = fun u => 2 / Hsum (α / 2) N * ∑ i : Fin N,
      idxR i ^ (-α) * Real.exp (-(2 * u) * idxR i ^ (-(α / 2))) := funext hKs
  have hsumA : ∑ i : Fin N, idxR i ^ (-α) / (2 * idxR i ^ (-(α / 2))) = Hsum (α / 2) N / 2 := by
    rw [← pa_sum_fin (α / 2) N, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i _
    have := (pa_idx_pow_pos (α / 2) i).ne'
    rw [pa_pow_split (idxR i) α (pa_idx_pos i)]
    field_simp
  have hI1 : ∫ u in Ioi (0 : ℝ), ∑ i : Fin N,
      idxR i ^ (-α) * Real.exp (-(2 * u) * idxR i ^ (-(α / 2))) = Hsum (α / 2) N / 2 := by
    rw [← hsumA]
    exact pa_fin_exp_integral (fun i => idxR i ^ (-α)) (fun i => idxR i ^ (-(α / 2)))
      (fun i => pa_idx_pow_pos (α / 2) i)
  have hPosS : ∀ u, 0 ≤ u → 0 < dimKernel mS (svdT0 N B) ε u := by
    intro u _
    rw [hKs u]
    exact mul_pos (div_pos two_pos hH1) (pa_fin_pos _ _ (fun i => pa_idx_pow_pos α i) hN u)
  have hContS : ContinuousOn (dimKernel mS (svdT0 N B) ε) (Ici 0) := by
    rw [hKs_fun]
    exact (continuous_const.mul (pa_fin_cont (fun i => idxR i ^ (-α))
      (fun i => idxR i ^ (-(α / 2))))).continuousOn
  have hAntiS : AntitoneOn (dimKernel mS (svdT0 N B) ε) (Ici 0) := by
    intro u _ v _ huv
    rw [hKs u, hKs v]
    exact mul_le_mul_of_nonneg_left (pa_fin_anti (fun i => idxR i ^ (-α))
      (fun i => idxR i ^ (-(α / 2))) (fun i => (pa_idx_pow_pos α i).le)
      (fun i => (pa_idx_pow_pos (α / 2) i).le) huv) (div_pos two_pos hH1).le
  have hMaxS : IsMaxOn (dimKernel mS (svdT0 N B) ε) (Ici 0) 0 :=
    isMaxOn_iff.2 fun x hx => hAntiS (Set.mem_Ici.2 le_rfl) hx (Set.mem_Ici.1 hx)
  have hIntS : IntegrableOn (dimKernel mS (svdT0 N B) ε) (Ioi 0) := by
    rw [hKs_fun]
    exact Integrable.const_mul (pa_fin_exp_integrable (fun i => idxR i ^ (-α))
      (fun i => idxR i ^ (-(α / 2))) (fun i => pa_idx_pow_pos (α / 2) i)) _
  have hIntS' : ∫ u in Ioi (0 : ℝ), dimKernel mS (svdT0 N B) ε u = 1 := by
    have e : ∫ u in Ioi (0 : ℝ), dimKernel mS (svdT0 N B) ε u
        = ∫ u in Ioi (0 : ℝ), 2 / Hsum (α / 2) N * ∑ i : Fin N,
          idxR i ^ (-α) * Real.exp (-(2 * u) * idxR i ^ (-(α / 2))) := by
      simp only [hKs]
    have := hH1.ne'
    rw [e, integral_const_mul, hI1]
    field_simp
  have hf0S : dimKernel mS (svdT0 N B) ε 0 = phaseKsvd α N := by
    rw [hKs 0]
    simp only [mul_zero, neg_zero, zero_mul, Real.exp_zero, mul_one]
    rw [pa_sum_fin α N]
    unfold phaseKsvd
    ring
  -- ## SGD kernel
  have hs_g : 0 < Real.sqrt (Real.pi * muBarOf α N / (B : ℝ)) :=
    Real.sqrt_pos.2 (div_pos (mul_pos hpi hm) hB)
  have hη_g : mG.η = 2 * Real.sqrt ε / (sgdArrays α ς N B).S := hmG.2.2.2.2
  have hS_sgd : (sgdArrays α ς N B).S ≠ 0 := by
    rw [pa_sgd_S α ς N B hN hNB]
    exact (mul_pos (div_pos (pow_pos hN0 2) two_pos) hs_g).ne'
  have hT_g : sgdT0 α N B / ((N : ℝ) ^ 2 / 2 * Real.sqrt (Real.pi * muBarOf α N / (B : ℝ)))
      = 2 / (N : ℝ) ^ 2 := by
    unfold sgdT0
    have := hs_g.ne'
    field_simp
  have hKg : ∀ u, dimKernel mG (sgdT0 α N B) ε u
      = 2 * (1 - 2 / Real.pi) / (N : ℝ) * ∑ i : Fin N,
          idxR i ^ (-α) * Real.exp (-(2 * u) * idxR i ^ (-α))
        + 4 / (Real.pi * Hsum α N) * ∑ i : Fin N,
          idxR i ^ (-(2 * α)) * Real.exp (-(2 * u) * idxR i ^ (-α)) := by
    intro u
    rw [pa_dimKernel_fin mG _ ε _ u hε hS_sgd hη_g, hmG.1, hmG.2.1, hmG.2.2.1,
      pa_sgd_S α ς N B hN hNB, hT_g]
    simp only [Finset.mul_sum]
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun i _ => pa_sgd_kernel_term α ς N B hN hNB u i)
  have hKg_fun : dimKernel mG (sgdT0 α N B) ε = fun u =>
      2 * (1 - 2 / Real.pi) / (N : ℝ) * ∑ i : Fin N,
          idxR i ^ (-α) * Real.exp (-(2 * u) * idxR i ^ (-α))
        + 4 / (Real.pi * Hsum α N) * ∑ i : Fin N,
          idxR i ^ (-(2 * α)) * Real.exp (-(2 * u) * idxR i ^ (-α)) := funext hKg
  have hc1 : 0 < 2 * (1 - 2 / Real.pi) / (N : ℝ) := by
    have h23 : 2 / Real.pi < 1 := (div_lt_one Real.pi_pos).2 (by linarith [Real.pi_gt_three])
    exact div_pos (mul_pos two_pos (by linarith)) hN0
  have hc2 : 0 < 4 / (Real.pi * Hsum α N) := div_pos (by norm_num) (mul_pos hpi hH0)
  have ha1 : ∀ i : Fin N, 0 < idxR i ^ (-α) := fun i => pa_idx_pow_pos α i
  have ha2 : ∀ i : Fin N, 0 < idxR i ^ (-(2 * α)) := fun i => pa_idx_pow_pos (2 * α) i
  have hContG : ContinuousOn (dimKernel mG (sgdT0 α N B) ε) (Ici 0) := by
    rw [hKg_fun]
    exact (((continuous_const.mul (pa_fin_cont (fun i => idxR i ^ (-α))
      (fun i => idxR i ^ (-α)))).add (continuous_const.mul (pa_fin_cont
      (fun i => idxR i ^ (-(2 * α))) (fun i => idxR i ^ (-α)))))).continuousOn
  have hAntiG : AntitoneOn (dimKernel mG (sgdT0 α N B) ε) (Ici 0) := by
    intro u _ v _ huv
    rw [hKg u, hKg v]
    exact add_le_add
      (mul_le_mul_of_nonneg_left (pa_fin_anti (fun i => idxR i ^ (-α))
        (fun i => idxR i ^ (-α)) (fun i => (ha1 i).le) (fun i => (ha1 i).le) huv) hc1.le)
      (mul_le_mul_of_nonneg_left (pa_fin_anti (fun i => idxR i ^ (-(2 * α)))
        (fun i => idxR i ^ (-α)) (fun i => (ha2 i).le) (fun i => (ha1 i).le) huv) hc2.le)
  have hMaxG : IsMaxOn (dimKernel mG (sgdT0 α N B) ε) (Ici 0) 0 :=
    isMaxOn_iff.2 fun x hx => hAntiG (Set.mem_Ici.2 le_rfl) hx (Set.mem_Ici.1 hx)
  have hPosG : ∀ u, 0 ≤ u → 0 < dimKernel mG (sgdT0 α N B) ε u := by
    intro u _
    rw [hKg u]
    exact add_pos (mul_pos hc1 (pa_fin_pos _ _ ha1 hN u))
      (mul_pos hc2 (pa_fin_pos _ _ ha2 hN u))
  have hf0G : dimKernel mG (sgdT0 α N B) ε 0 = phaseKsgd α N := by
    rw [hKg 0]
    simp only [mul_zero, neg_zero, zero_mul, Real.exp_zero, mul_one]
    rw [pa_sum_fin α N, pa_sum_fin (2 * α) N]
    unfold phaseKsgd
    ring
  -- ## SGD Lsum forms and masses
  have hL1 : ∀ u, Lsum (N : ℕ∞) α α u
      = ∑ i : Fin N, idxR i ^ (-α) * Real.exp (-(2 * u) * idxR i ^ (-α)) :=
    fun u => pa_Lsum_fin N α α u
  have hL2 : ∀ u, Lsum (N : ℕ∞) (2 * α) α u
      = ∑ i : Fin N, idxR i ^ (-(2 * α)) * Real.exp (-(2 * u) * idxR i ^ (-α)) :=
    fun u => pa_Lsum_fin N (2 * α) α u
  have hsumC : ∑ i : Fin N, idxR i ^ (-α) / (2 * idxR i ^ (-α)) = (N : ℝ) / 2 := by
    rw [Finset.sum_congr rfl (g := fun _ => (1 : ℝ) / 2) (fun i _ => by
      have := (pa_idx_pow_pos α i).ne'
      field_simp)]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  have hsumB : ∑ i : Fin N, idxR i ^ (-(2 * α)) / (2 * idxR i ^ (-α)) = Hsum α N / 2 := by
    rw [← pa_sum_fin α N, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i _
    have := (pa_idx_pow_pos α i).ne'
    rw [show -(2 * α) = -α + -α by ring, Real.rpow_add (pa_idx_pos i)]
    field_simp
  have hIA : ∫ u in Ioi (0 : ℝ), ∑ i : Fin N,
      idxR i ^ (-α) * Real.exp (-(2 * u) * idxR i ^ (-α)) = (N : ℝ) / 2 := by
    rw [← hsumC]
    exact pa_fin_exp_integral (fun i => idxR i ^ (-α)) (fun i => idxR i ^ (-α))
      (fun i => pa_idx_pow_pos α i)
  have hIB : ∫ u in Ioi (0 : ℝ), ∑ i : Fin N,
      idxR i ^ (-(2 * α)) * Real.exp (-(2 * u) * idxR i ^ (-α)) = Hsum α N / 2 := by
    rw [← hsumB]
    exact pa_fin_exp_integral (fun i => idxR i ^ (-(2 * α))) (fun i => idxR i ^ (-α))
      (fun i => pa_idx_pow_pos α i)
  have hIntG1 : IntegrableOn (fun u => 2 * (1 - 2 / Real.pi) / (N : ℝ) * Lsum (N : ℕ∞) α α u)
      (Ioi (0 : ℝ)) := by
    simp only [hL1]
    exact Integrable.const_mul (pa_fin_exp_integrable (fun i => idxR i ^ (-α))
      (fun i => idxR i ^ (-α)) (fun i => pa_idx_pow_pos α i)) _
  have hJ1 : ∫ u in Ioi (0 : ℝ), 2 * (1 - 2 / Real.pi) / (N : ℝ) * Lsum (N : ℕ∞) α α u
      = 1 - 2 / Real.pi := by
    simp only [hL1]
    rw [integral_const_mul, hIA]
    have := hN0.ne'
    field_simp
  have hIntG2 : IntegrableOn (fun u => 4 / (Real.pi * Hsum α N) * Lsum (N : ℕ∞) (2 * α) α u)
      (Ioi (0 : ℝ)) := by
    simp only [hL2]
    exact Integrable.const_mul (pa_fin_exp_integrable (fun i => idxR i ^ (-(2 * α)))
      (fun i => idxR i ^ (-α)) (fun i => pa_idx_pow_pos α i)) _
  have hJ2 : ∫ u in Ioi (0 : ℝ), 4 / (Real.pi * Hsum α N) * Lsum (N : ℕ∞) (2 * α) α u
      = 2 / Real.pi := by
    simp only [hL2]
    rw [integral_const_mul, hIB]
    have := hH0.ne'
    field_simp
    norm_num
  exact ⟨⟨hPosS, hContS, hAntiS, hIntS, hIntS', hMaxS, hf0S⟩,
    ⟨hPosG, hContG, hAntiG, hMaxG, hf0G, hIntG1, hJ1, hIntG2, hJ2⟩⟩

/-- Scaling of the first hitting time: `H_R(a) = c · H_{R(c·)}(a)` for `c > 0`. -/
lemma pa_firstHit_scale (R : ℝ → ℝ) (c : ℝ) (hc : 0 < c) (a : ℝ) :
    firstHit R a = ENNReal.ofReal c * firstHit (fun u => R (c * u)) a := by
  set c' : NNReal := c.toNNReal with hc'def
  have hc'R : (c' : ℝ) = c := Real.coe_toNNReal _ hc.le
  have hc'0 : c' ≠ 0 := by
    intro h
    have h2 : (c' : ℝ) = 0 := by rw [h]; rfl
    rw [hc'R] at h2
    linarith
  have hofr : ENNReal.ofReal c = (c' : ENNReal) := rfl
  have h0 : ENNReal.ofReal c ≠ 0 := by
    rw [hofr]; exact ENNReal.coe_ne_zero.2 hc'0
  have htop : ENNReal.ofReal c ≠ ⊤ := ENNReal.ofReal_ne_top
  unfold firstHit
  simp only [ENNReal.mul_iInf_of_ne h0 htop]
  apply le_antisymm
  · refine le_iInf fun (u : NNReal) => le_iInf fun (hu : R (c * (u : ℝ)) ≤ a) => ?_
    have hmul : ENNReal.ofReal c * (u : ENNReal) = ((c' * u : NNReal) : ENNReal) := by
      rw [hofr, ENNReal.coe_mul]
    rw [hmul]
    refine iInf₂_le (c' * u) ?_
    rw [NNReal.coe_mul, hc'R]
    exact hu
  · refine le_iInf₂ fun (t : NNReal) (ht : R (t : ℝ) ≤ a) => ?_
    have hcoe : c * ((c'⁻¹ * t : NNReal) : ℝ) = (t : ℝ) := by
      rw [NNReal.coe_mul, NNReal.coe_inv, hc'R]
      field_simp
    have hu0 : R (c * ((c'⁻¹ * t : NNReal) : ℝ)) ≤ a := by
      rw [hcoe]; exact ht
    refine (iInf₂_le (c'⁻¹ * t) hu0).trans (le_of_eq ?_)
    rw [hofr, ← ENNReal.coe_mul, mul_inv_cancel_left₀ hc'0]

/-- Substitution in the clock: `t(c τ) = η⁻¹ · c · ∫_0^τ √(Q(c u)) du` for `c ≠ 0`. -/
lemma pa_clockTime_scale {ι : Type*} (m : RowModel ι) (Q : ℝ → ℝ) (c τ : ℝ) (hc : 0 < c) :
    clockTime m Q (c * τ) = (1 / m.η) * (c * ∫ u in (0:ℝ)..τ, Real.sqrt (Q (c * u))) := by
  unfold clockTime
  congr 1
  have h := intervalIntegral.integral_comp_mul_left (fun v => Real.sqrt (Q v))
    (a := 0) (b := τ) hc.ne'
  simp only [mul_zero, smul_eq_mul] at h
  rw [h, ← mul_assoc, mul_inv_cancel₀ hc.ne', one_mul]

/-- Time formula for one model, at a general multiplier `c > 0` of the risk argument. -/
lemma pa_hitting_scaled {ι : Type*} [Countable ι] (m : RowModel ι) (Q : ℝ → ℝ)
    (hQ : IsVolterraSol m Q) (hS : 0 < m.S) (ε : ℝ) (hε : 0 < ε)
    (hη : m.η = 2 * Real.sqrt ε / m.S) (c a : ℝ) (hc : 0 < c) (ha : 0 < a)
    (hτ : firstHit (fun u => Q (c * u)) a ≠ ⊤) :
    firstHit (riskClock m Q) a = ENNReal.ofReal
      (m.S * c / (2 * Real.sqrt ε) *
        ∫ u in (0 : ℝ)..(firstHit (fun u => Q (c * u)) a).toReal, Real.sqrt (Q (c * u))) := by
  have hsc := pa_firstHit_scale Q c hc a
  have hfin : firstHit Q a ≠ ⊤ := by
    rw [hsc]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hτ
  have hclk := (thm_app_phase_hitting_i m Q hQ hS ε hε hη a ha).2.2 hfin
  have hreal : (firstHit Q a).toReal = c * (firstHit (fun u => Q (c * u)) a).toReal := by
    rw [hsc, ENNReal.toReal_mul, ENNReal.toReal_ofReal hc.le]
  rw [hclk, hreal, pa_clockTime_scale m Q c _ hc, hη, one_div_div]
  congr 1
  ring

/-- Label `prop:app-phase-prefactors`, part (iii): the time formula
`t^j_{Tε} = S_j T_0^j/(2√ε) ∫_0^{û_j} √Y_j(u) du` whenever `û_j < ∞`, where `û_j` is the first hit
of `Tε` by `Y_j(u) = Q_j(T_0 u)` and `t^j_{Tε}` is the first hit of `Tε` by the step-time risk
`riskClock` (`firstHit`, `ℝ≥0∞`). The level `T` is positive (see the module note). Snapshot
`cr-2026-10-23`. Statement (verbatim, `sections/07-phase-comparison/section.tex`):

Source lines: section.tex l.1116–1166.
```latex
\begin{proposition}[Noise constants, kernels and clocks]\label{prop:app-phase-prefactors}
The arrays of \cref{def:app-phase-arrays} satisfy (M1), with
$F_0=\frac12H_N(p)$, and the following hold.
\begin{enumerate}[label=(\roman*)]
\item The noise constants, matched steps and time-scale products are
\begin{equation}\label{eqn:app-phase-ST0}
\begin{aligned}
\mathcal S_{\text{s-SVD}}&=\tfrac12\sqrt\gamma\,H_N(\alpha/2),&\quad
\lr^\star_{\text{s-SVD}}&=\frac{4\sqrt\epsilon}{\sqrt\gamma\,H_N(\alpha/2)},\\
\mathcal S_{\text{s-SGD}}&=\frac{N^2}2\sqrt{\frac{\pi\bar\mu}B},&\quad
\lr^\star_{\text{s-SGD}}&=\frac{4\sqrt\epsilon}{N^2}\sqrt{\frac B{\pi\bar\mu}},\\
\mathcal S_{\text{s-SVD}}T_0^{\text{s-SVD}}&=\tfrac\gamma2H_N(\alpha/2),&\quad
\mathcal S_{\text{s-SGD}}T_0^{\text{s-SGD}}&=\frac{\pi N^2\bar\mu}{2B}=\tfrac{\pi\gamma}2H_N(\alpha),
\end{aligned}
\end{equation}
and the dimension factor is
\begin{equation}\label{eqn:app-phase-DN}
D_N\defeq\frac{\mathcal S_{\text{s-SGD}}T_0^{\text{s-SGD}}}{\mathcal S_{\text{s-SVD}}T_0^{\text{s-SVD}}}=\frac{\pi H_N(\alpha)}{H_N(\alpha/2)} .
\end{equation}
\item The dimensionless risks solve
$Y_j=f_{N,q_j}+\sqrt\epsilon\,g_j*\sqrt{Y_j}$, with $f_{N,q}$ of
\cref{eqn:app-phase-fNq} and
\begin{equation}\label{eqn:app-phase-kernels}
g_{\text{s-SVD}}=\frac2{H_N(\alpha/2)}L_{N,\alpha,\alpha/2},\qquad
g_{\text{s-SGD}}=\frac{2(1-2/\pi)}N\,L_{N,\alpha,\alpha}+\frac4{\pi H_N(\alpha)}\,L_{N,2\alpha,\alpha} .
\end{equation}
Both kernels are positive, continuous and decreasing. The kernel
$g_{\text{s-SVD}}$ has integral $1$, and the two terms of $g_{\text{s-SGD}}$
have integrals $1-2/\pi$ and $2/\pi$. Their maxima are
\begin{equation}\label{eqn:app-phase-heights}
\begin{gathered}
k_{N,\text{s-SVD}}\defeq g_{\text{s-SVD}}(0)=\frac{2H_N(\alpha)}{H_N(\alpha/2)},\\
k_{N,\text{s-SGD}}\defeq g_{\text{s-SGD}}(0)=\frac{2(1-2/\pi)H_N(\alpha)}N+\frac{4H_N(2\alpha)}{\pi H_N(\alpha)} .
\end{gathered}
\end{equation}
\item If $\hat u_j<\infty$, then
\begin{equation}\label{eqn:app-phase-time}
t^j_{T\epsilon}=\frac{\mathcal S_jT_0^j}{2\sqrt\epsilon}\int_0^{\hat u_j}\sqrt{Y_j(u)}\,\dif u .
\end{equation}
\item As $N\to\infty$ at fixed $\alpha$,
\begin{equation}\label{eqn:app-phase-DN-asymp}
D_N\sim\begin{cases}
\pi\,\dfrac{1-\alpha/2}{1-\alpha}\,N^{-\alpha/2},&0<\alpha<1,\\[4pt]
\dfrac\pi2N^{-1/2}\log N,&\alpha=1,\\[4pt]
\pi(1-\alpha/2)\,\zeta(\alpha)\,N^{\alpha/2-1},&1<\alpha<2,\\[4pt]
\pi\zeta(2)/\log N,&\alpha=2,\\[4pt]
\pi\zeta(\alpha)/\zeta(\alpha/2),&\alpha>2.
\end{cases}
\end{equation}
\end{enumerate}
\end{proposition}
``` -/
theorem prop_app_phase_prefactors_iii (α ς : ℝ) (N B : ℕ) (hα : 0 < α) (hp : 1 < α + ς)
    (hN : 1 ≤ N) (hNB : N ≤ B) (ε T : ℝ) (hε : 0 < ε) (hT : 0 < T)
    (mS mG : RowModel (Fin N))
    (hmS : IsMatchedModel (svdArrays α ς N B) mS ε)
    (hmG : IsMatchedModel (sgdArrays α ς N B) mG ε)
    (QS QG : ℝ → ℝ) (hQS : IsVolterraSol mS QS) (hQG : IsVolterraSol mG QG) :
    (firstHit (fun u => QS (svdT0 N B * u)) (T * ε) ≠ ⊤ →
      firstHit (riskClock mS QS) (T * ε) = ENNReal.ofReal
        (mS.S * svdT0 N B / (2 * Real.sqrt ε) *
          ∫ u in (0 : ℝ)..(firstHit (fun u => QS (svdT0 N B * u)) (T * ε)).toReal,
            Real.sqrt (QS (svdT0 N B * u)))) ∧
    (firstHit (fun u => QG (sgdT0 α N B * u)) (T * ε) ≠ ⊤ →
      firstHit (riskClock mG QG) (T * ε) = ENNReal.ofReal
        (mG.S * sgdT0 α N B / (2 * Real.sqrt ε) *
          ∫ u in (0 : ℝ)..(firstHit (fun u => QG (sgdT0 α N B * u)) (T * ε)).toReal,
            Real.sqrt (QG (sgdT0 α N B * u)))) := by
  have hγ := pa_gamma_pos hN hNB
  have hB0 : (0 : ℝ) < B := Nat.cast_pos.mpr (by omega)
  have hN0 : (0 : ℝ) < N := Nat.cast_pos.mpr (by omega)
  have hm := pa_muBar_pos α hN
  have hT0 : 0 < svdT0 N B := Real.sqrt_pos.2 hγ
  have hT0' : 0 < sgdT0 α N B :=
    Real.sqrt_pos.2 (div_pos (mul_pos Real.pi_pos hm) hB0)
  have hSS : 0 < (svdArrays α ς N B).S := by
    rw [pa_svd_S α ς N B hN hNB]
    exact mul_pos (mul_pos (by norm_num) (Real.sqrt_pos.2 hγ)) (pa_Hsum_pos (α / 2) hN)
  have hSG : 0 < (sgdArrays α ς N B).S := by
    rw [pa_sgd_S α ς N B hN hNB]
    exact mul_pos (div_pos (pow_pos hN0 2) two_pos)
      (Real.sqrt_pos.2 (div_pos (mul_pos Real.pi_pos hm) hB0))
  obtain ⟨hμS, hdS, hvS, -, hηS⟩ := hmS
  obtain ⟨hμG, hdG, hvG, -, hηG⟩ := hmG
  have hmSS : mS.S = (svdArrays α ς N B).S := by
    unfold RowModel.S PhaseArrays.S
    rw [hμS, hdS, hvS]
  have hmGS : mG.S = (sgdArrays α ς N B).S := by
    unfold RowModel.S PhaseArrays.S
    rw [hμG, hdG, hvG]
  have hηS' : mS.η = 2 * Real.sqrt ε / mS.S := by
    rw [hmSS]; exact hηS
  have hηG' : mG.η = 2 * Real.sqrt ε / mG.S := by
    rw [hmGS]; exact hηG
  have hTε : 0 < T * ε := mul_pos hT hε
  refine ⟨fun hτ => ?_, fun hτ => ?_⟩
  · exact pa_hitting_scaled mS QS hQS (by rw [hmSS]; exact hSS) ε hε hηS' (svdT0 N B) (T * ε)
      hT0 hTε hτ
  · exact pa_hitting_scaled mG QG hQG (by rw [hmGS]; exact hSG) ε hε hηG' (sgdT0 α N B) (T * ε)
      hT0' hTε hτ

lemma pa_H_tendsto {a : ℝ} (ha : 1 < a) :
    Tendsto (fun N : ℕ => Hsum a N) atTop (𝓝 (zetaR a)) := by
  have hp : Tendsto (fun N : ℕ => (N : ℝ) ^ (1 - a) / (a - 1)) atTop (𝓝 0) := by
    have h : Tendsto (fun N : ℕ => (N : ℝ) ^ (1 - a)) atTop (𝓝 0) := by
      rw [show (1 : ℝ) - a = -(a - 1) by ring]
      exact (tendsto_rpow_neg_atTop (by linarith)).comp tendsto_natCast_atTop_atTop
    have h2 := h.div_const (a - 1)
    rw [zero_div] at h2
    exact h2
  have hlim : Tendsto (fun N : ℕ => zetaR a - Hsum a N) atTop (𝓝 0) := by
    refine squeeze_zero' ?_ ?_ hp
    · filter_upwards [eventually_ge_atTop 1] with N hN
      exact (lem_app_phase_harmonic_vi ha N hN).1
    · filter_upwards [eventually_ge_atTop 1] with N hN
      exact (lem_app_phase_harmonic_vi ha N hN).2
  have h2 := (tendsto_const_nhds (x := zetaR a)).sub hlim
  simpa using h2

lemma pa_one_le_zeta {a : ℝ} (ha : 1 < a) : 1 ≤ zetaR a := by
  have h := (lem_app_phase_harmonic_vi ha 1 le_rfl).1
  have h1 : Hsum a 1 = 1 := by simp [Hsum]
  linarith


/-- Label `prop:app-phase-prefactors`, part (iv): the asymptotics of `D_N` as `N → ∞` at fixed `α`,
in the five cases of the display (`eqn:app-phase-DN-asymp`). Snapshot `cr-2026-10-23`. Statement
(verbatim, `sections/07-phase-comparison/section.tex`):

Source lines: section.tex l.1116–1166.
```latex
\begin{proposition}[Noise constants, kernels and clocks]\label{prop:app-phase-prefactors}
The arrays of \cref{def:app-phase-arrays} satisfy (M1), with
$F_0=\frac12H_N(p)$, and the following hold.
\begin{enumerate}[label=(\roman*)]
\item The noise constants, matched steps and time-scale products are
\begin{equation}\label{eqn:app-phase-ST0}
\begin{aligned}
\mathcal S_{\text{s-SVD}}&=\tfrac12\sqrt\gamma\,H_N(\alpha/2),&\quad
\lr^\star_{\text{s-SVD}}&=\frac{4\sqrt\epsilon}{\sqrt\gamma\,H_N(\alpha/2)},\\
\mathcal S_{\text{s-SGD}}&=\frac{N^2}2\sqrt{\frac{\pi\bar\mu}B},&\quad
\lr^\star_{\text{s-SGD}}&=\frac{4\sqrt\epsilon}{N^2}\sqrt{\frac B{\pi\bar\mu}},\\
\mathcal S_{\text{s-SVD}}T_0^{\text{s-SVD}}&=\tfrac\gamma2H_N(\alpha/2),&\quad
\mathcal S_{\text{s-SGD}}T_0^{\text{s-SGD}}&=\frac{\pi N^2\bar\mu}{2B}=\tfrac{\pi\gamma}2H_N(\alpha),
\end{aligned}
\end{equation}
and the dimension factor is
\begin{equation}\label{eqn:app-phase-DN}
D_N\defeq\frac{\mathcal S_{\text{s-SGD}}T_0^{\text{s-SGD}}}{\mathcal S_{\text{s-SVD}}T_0^{\text{s-SVD}}}=\frac{\pi H_N(\alpha)}{H_N(\alpha/2)} .
\end{equation}
\item The dimensionless risks solve
$Y_j=f_{N,q_j}+\sqrt\epsilon\,g_j*\sqrt{Y_j}$, with $f_{N,q}$ of
\cref{eqn:app-phase-fNq} and
\begin{equation}\label{eqn:app-phase-kernels}
g_{\text{s-SVD}}=\frac2{H_N(\alpha/2)}L_{N,\alpha,\alpha/2},\qquad
g_{\text{s-SGD}}=\frac{2(1-2/\pi)}N\,L_{N,\alpha,\alpha}+\frac4{\pi H_N(\alpha)}\,L_{N,2\alpha,\alpha} .
\end{equation}
Both kernels are positive, continuous and decreasing. The kernel
$g_{\text{s-SVD}}$ has integral $1$, and the two terms of $g_{\text{s-SGD}}$
have integrals $1-2/\pi$ and $2/\pi$. Their maxima are
\begin{equation}\label{eqn:app-phase-heights}
\begin{gathered}
k_{N,\text{s-SVD}}\defeq g_{\text{s-SVD}}(0)=\frac{2H_N(\alpha)}{H_N(\alpha/2)},\\
k_{N,\text{s-SGD}}\defeq g_{\text{s-SGD}}(0)=\frac{2(1-2/\pi)H_N(\alpha)}N+\frac{4H_N(2\alpha)}{\pi H_N(\alpha)} .
\end{gathered}
\end{equation}
\item If $\hat u_j<\infty$, then
\begin{equation}\label{eqn:app-phase-time}
t^j_{T\epsilon}=\frac{\mathcal S_jT_0^j}{2\sqrt\epsilon}\int_0^{\hat u_j}\sqrt{Y_j(u)}\,\dif u .
\end{equation}
\item As $N\to\infty$ at fixed $\alpha$,
\begin{equation}\label{eqn:app-phase-DN-asymp}
D_N\sim\begin{cases}
\pi\,\dfrac{1-\alpha/2}{1-\alpha}\,N^{-\alpha/2},&0<\alpha<1,\\[4pt]
\dfrac\pi2N^{-1/2}\log N,&\alpha=1,\\[4pt]
\pi(1-\alpha/2)\,\zeta(\alpha)\,N^{\alpha/2-1},&1<\alpha<2,\\[4pt]
\pi\zeta(2)/\log N,&\alpha=2,\\[4pt]
\pi\zeta(\alpha)/\zeta(\alpha/2),&\alpha>2.
\end{cases}
\end{equation}
\end{enumerate}
\end{proposition}
``` -/
theorem prop_app_phase_prefactors_iv (α : ℝ) (hα : 0 < α) :
    (α < 1 → Asymptotics.IsEquivalent atTop (fun N : ℕ => phaseDN α N)
        (fun N : ℕ => Real.pi * (1 - α / 2) / (1 - α) * (N : ℝ) ^ (-(α / 2)))) ∧
    (α = 1 → Asymptotics.IsEquivalent atTop (fun N : ℕ => phaseDN α N)
        (fun N : ℕ => Real.pi / 2 * (N : ℝ) ^ (-(1 / 2 : ℝ)) * Real.log (N : ℝ))) ∧
    (1 < α → α < 2 → Asymptotics.IsEquivalent atTop (fun N : ℕ => phaseDN α N)
        (fun N : ℕ => Real.pi * (1 - α / 2) * zetaR α * (N : ℝ) ^ (α / 2 - 1))) ∧
    (α = 2 → Asymptotics.IsEquivalent atTop (fun N : ℕ => phaseDN α N)
        (fun N : ℕ => Real.pi * zetaR 2 / Real.log (N : ℝ))) ∧
    (2 < α → Asymptotics.IsEquivalent atTop (fun N : ℕ => phaseDN α N)
        (fun _ : ℕ => Real.pi * zetaR α / zetaR (α / 2))) := by
  refine ⟨fun hα1 => ?_, fun hα1 => ?_, fun hα1 hα2 => ?_, fun hα2 => ?_, fun hα2 => ?_⟩
  · -- 0 < α < 1
    have h1 := lem_app_phase_harmonic_iii hα hα1
    have h2 := lem_app_phase_harmonic_iii (a := α / 2) (by linarith) (by linarith)
    have hnum : Asymptotics.IsEquivalent atTop (fun N : ℕ => Real.pi * Hsum α N)
        (fun N : ℕ => Real.pi * ((N : ℝ) ^ (1 - α) / (1 - α))) :=
      (Asymptotics.IsEquivalent.refl :
        Asymptotics.IsEquivalent atTop (fun _ : ℕ => Real.pi) (fun _ : ℕ => Real.pi)).mul h1
    refine (hnum.div h2).congr_right ?_
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hNpos : (0 : ℝ) < N := by
      have : (1 : ℝ) ≤ N := by exact_mod_cast hN
      linarith
    have hB : (N : ℝ) ^ (1 - α / 2) ≠ 0 := (Real.rpow_pos_of_pos hNpos _).ne'
    have hsub : (N : ℝ) ^ (1 - α) / (N : ℝ) ^ (1 - α / 2) = (N : ℝ) ^ (-(α / 2)) := by
      rw [← Real.rpow_sub hNpos]
      congr 1
      ring
    have hd1 : (1 - α) ≠ 0 := (by linarith : (0 : ℝ) < 1 - α).ne'
    have hd2 : (1 - α / 2) ≠ 0 := (by linarith : (0 : ℝ) < 1 - α / 2).ne'
    simp only [Pi.div_apply]
    rw [← hsub]
    field_simp
  · -- α = 1
    subst hα1
    have h1 := lem_app_phase_harmonic_iv
    have h2 := lem_app_phase_harmonic_iii (a := (1 : ℝ) / 2) (by norm_num) (by norm_num)
    have hnum : Asymptotics.IsEquivalent atTop (fun N : ℕ => Real.pi * Hsum 1 N)
        (fun N : ℕ => Real.pi * Real.log N) :=
      (Asymptotics.IsEquivalent.refl :
        Asymptotics.IsEquivalent atTop (fun _ : ℕ => Real.pi) (fun _ : ℕ => Real.pi)).mul h1
    unfold phaseDN
    rw [show (1 : ℝ) / 2 = 1 / 2 from rfl]
    refine (hnum.div h2).congr_right ?_
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hNpos : (0 : ℝ) < N := by
      have : (1 : ℝ) ≤ N := by exact_mod_cast hN
      linarith
    have hs : (N : ℝ) ^ (1 - (1 : ℝ) / 2) = (N : ℝ) ^ ((1 : ℝ) / 2) := by norm_num
    have hpos : (N : ℝ) ^ ((1 : ℝ) / 2) ≠ 0 := (Real.rpow_pos_of_pos hNpos _).ne'
    simp only [Pi.div_apply]
    rw [hs, Real.rpow_neg hNpos.le]
    field_simp
    ring
  · -- 1 < α < 2
    have hζ : zetaR α ≠ 0 := (by linarith [pa_one_le_zeta hα1] : (0 : ℝ) < zetaR α).ne'
    have hπζ : Real.pi * zetaR α ≠ 0 := mul_ne_zero Real.pi_pos.ne' hζ
    have hA : Asymptotics.IsEquivalent atTop (fun N : ℕ => Real.pi * Hsum α N)
        (fun _ : ℕ => Real.pi * zetaR α) :=
      (Asymptotics.isEquivalent_const_iff_tendsto hπζ).2
        ((pa_H_tendsto hα1).const_mul Real.pi)
    have h2 := lem_app_phase_harmonic_iii (a := α / 2) (by linarith) (by linarith)
    refine (hA.div h2).congr_right ?_
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hNpos : (0 : ℝ) < N := by
      have : (1 : ℝ) ≤ N := by exact_mod_cast hN
      linarith
    have hB : (N : ℝ) ^ (1 - α / 2) ≠ 0 := (Real.rpow_pos_of_pos hNpos _).ne'
    have hd2 : (1 - α / 2) ≠ 0 := (by linarith : (0 : ℝ) < 1 - α / 2).ne'
    have hs : (N : ℝ) ^ (α / 2 - 1) = ((N : ℝ) ^ (1 - α / 2))⁻¹ := by
      rw [show α / 2 - 1 = -(1 - α / 2) by ring, Real.rpow_neg hNpos.le]
    simp only [Pi.div_apply]
    rw [hs]
    field_simp
  · -- α = 2
    subst hα2
    have h22 : (2 : ℝ) / 2 = 1 := by norm_num
    have hζ : zetaR 2 ≠ 0 := (by linarith [pa_one_le_zeta (by norm_num : (1 : ℝ) < 2)] :
      (0 : ℝ) < zetaR 2).ne'
    have hπζ : Real.pi * zetaR 2 ≠ 0 := mul_ne_zero Real.pi_pos.ne' hζ
    have hA : Asymptotics.IsEquivalent atTop (fun N : ℕ => Real.pi * Hsum 2 N)
        (fun _ : ℕ => Real.pi * zetaR 2) :=
      (Asymptotics.isEquivalent_const_iff_tendsto hπζ).2
        ((pa_H_tendsto (by norm_num : (1 : ℝ) < 2)).const_mul Real.pi)
    have h1 := lem_app_phase_harmonic_iv
    unfold phaseDN
    rw [h22]
    exact hA.div h1
  · -- 2 < α
    have hα0 : (1 : ℝ) < α / 2 := by linarith
    have hζ1 : (0 : ℝ) < zetaR α := by linarith [pa_one_le_zeta (by linarith : (1 : ℝ) < α)]
    have hζ2 : (0 : ℝ) < zetaR (α / 2) := by linarith [pa_one_le_zeta hα0]
    have hc : Real.pi * zetaR α / zetaR (α / 2) ≠ 0 :=
      (div_pos (mul_pos Real.pi_pos hζ1) hζ2).ne'
    have hT : Tendsto (fun N : ℕ => Real.pi * Hsum α N / Hsum (α / 2) N) atTop
        (𝓝 (Real.pi * zetaR α / zetaR (α / 2))) :=
      Tendsto.div ((pa_H_tendsto (by linarith : (1 : ℝ) < α)).const_mul Real.pi)
        (pa_H_tendsto hα0) hζ2.ne'
    exact (Asymptotics.isEquivalent_const_iff_tendsto hc).2 hT

end Muon.Phase

end
