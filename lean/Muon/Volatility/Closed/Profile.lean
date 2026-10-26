import Muon.DetEquiv.Branch
import Muon.Foundations.Conventions
import Muon.Volatility.TreeDef

/-!
# Appendix D, §D.7: profiles, branch of a profile, 2×2 Perron bound, closed-form determinant

Work package L-D.15 (interface draft). Snapshot `cr-2026-10-23`. Source:
`sections/04-volatility/section.tex`, §D.7 (closed form), with
`def:app-vol-closed-profile` (l.1676–1691), `lem:app-vol-closed-profile` (l.1712–1738),
`lem:app-vol-closed-branch` (l.1794–1827), `lem:app-vol-closed-perron` (l.1922–1930) and
`lem:app-vol-closed-determinant` (l.1961–1971). The objects these statements use and that are
defined here: `eqn:app-vol-closed-objects` (l.1470), the constants `kappa`, `theta`, `qhat`,
`epsilon` (l.1497–1506), `eqn:app-vol-closed-profile-kernel` (the determinant `Δ_ξ`) and the EMA
paired profile of the paragraph after `def:app-vol-closed-profile`. Card:
`sections/04-volatility/CARD.md` §2, §3, §5 (row L-D.15), §6 (R20–R22 are not in this package).

Encoding decisions:
* A profile is a countable family `ξ : ι → Ω → ℝ` of real random variables on a probability space
  `(Ω, P)`, with the moment and nonvanishing hypotheses as fields. `F_ξ, r_ξ, b, e` depend only on
  the per-label laws, so no independence across labels is assumed (CARD §2).
* `F_ξ, b, e` are `tsum`s of Bochner integrals of nonnegative integrands. The derivative series
  `r'_ξ` and `-F'_ξ` are given as explicit series (the source's formulas). Lean's `tsum`/`∫` are junk
  off their domain; every statement that uses a series carries the summability or integrability
  it needs as a conjunct or hypothesis.
* `-F'_ξ(q)` may be `+∞` at `q = 0` (source, `lem:app-vol-closed-profile`(a)). The finiteness and the
  formula for `-F'_ξ` are therefore stated for `q > 0`. The square-root bound on `e` in (c) is stated
  for `q₁, q₂ > 0` for the same reason (at `0` the right side is junk).
* EMA paired profile at lag `ℓ`: labels `ℕ ⊕ Fin ℓ`; `inl j` is the shared batch `j ≥ 0`, and
  `inr i` is the fresh batch `m = i + 1 ∈ {1,…,ℓ}`. `g` is a family of independent standard Gaussians
  (`IsStdGaussianFamily`), passed as a hypothesis wherever the source uses the EMA profile.
* Branch points are quadruples `(σ, σ̃, s̃₁, s₁)` as in `Muon.DetEquiv.IsBranchSol`. `branchPt` is
  `Classical.choose` with default `0` (the total map, as `Muon.DetEquiv.branchSol`). Its existence
  and uniqueness are proved in the statements below, not assumed.
* The determinant `Δ_ξ` takes the branch point of `ξ₁` at `s` and of `ξ₂` at `u`; the first
  resolvent of `T^out, T^in` uses the first branch point, the second uses the second.
* The constants `ε_β` use `qhat_β := sup {q ≥ 0 : r_β(q) ≤ γ⋆}`, which equals `r_β⁻¹(γ⋆)` because
  `r_β` is continuous and strictly increasing (`lem:app-vol-closed-profile`(b), at the EMA weights).
* `Muon.DetEquiv.classK` is used as the class `𝒦` of the B-branch theorem in the EMA branch
  statement. Its mass and support conditions are the source's `eqn:app-de-class`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal Matrix MatrixOrder

namespace Muon.Volatility

variable {Ω : Type*} [MeasurableSpace Ω] {ι : Type*} [Countable ι]

/-! ## Profiles and their scalar functions -/

/-- `def:app-vol-closed-profile`, snapshot `cr-2026-10-23`. Declaration of record: a profile. The fields are the moment
and nonvanishing conditions of the source, with `∑_α E ξ_α² < ∞` as summability of the integrals.
`ι` is the countable label set.

LaTeX (`sections/04-volatility/section.tex` l.1676–1691, verbatim):
```latex
\begin{definition}[Profiles]\label{def:app-vol-closed-profile}
A \emph{profile} is a countable family $\xi=(\xi_\alpha)_{\alpha\in\mathcal A}$ of real
random variables with $\sum_\alpha\EE\xi_\alpha^2<\infty$ and $\Pr(\xi_\alpha\ne0)>0$ for
some $\alpha$. Its scalar functions are, for $q\ge0$,
\[
F_\xi(q)\defeq\sum_\alpha\EE\frac{\xi_\alpha^2}{1+q\xi_\alpha^2},\qquad r_\xi(q)\defeq qF_\xi(q).
\]
A \emph{paired profile} is a countable family $(\xi_{1,\alpha},\xi_{2,\alpha})_{\alpha\in\mathcal A}$
such that $\xi_1=(\xi_{1,\alpha})$ and $\xi_2=(\xi_{2,\alpha})$ are profiles,
$\xi_{1,\alpha}\xi_{2,\alpha}\ge0$, and $\sum_\alpha\EE[\xi_{1,\alpha}^2\xi_{2,\alpha}^2]<\infty$. Its
two-point functions are, for $q_1,q_2\ge0$,
\[
b(q_1,q_2)\defeq\sum_\alpha\EE\frac{\xi_{1,\alpha}\xi_{2,\alpha}}{(1+q_1\xi_{1,\alpha}^2)(1+q_2\xi_{2,\alpha}^2)},\qquad
e(q_1,q_2)\defeq\sum_\alpha\EE\frac{\xi_{1,\alpha}^2\xi_{2,\alpha}^2}{(1+q_1\xi_{1,\alpha}^2)(1+q_2\xi_{2,\alpha}^2)}.
\]
\end{definition}
```
-/
structure def_app_vol_closed_profile (P : Measure Ω) (ξ : ι → Ω → ℝ) : Prop where
  measurable : ∀ α, Measurable (ξ α)
  integrable_sq : ∀ α, Integrable (fun ω => ξ α ω ^ 2) P
  summable_sq : Summable (fun α => ∫ ω, ξ α ω ^ 2 ∂P)
  exists_ne_zero : ∃ α, 0 < P {ω | ξ α ω ≠ 0}

/-- `def:app-vol-closed-profile`, snapshot `cr-2026-10-23`. Declaration of record: a paired profile (the second half of the definition). Both coordinates are profiles,
`ξ₁_α ξ₂_α ≥ 0` pointwise, and `∑_α E[ξ₁_α² ξ₂_α²] < ∞` (integrability of each term plus summability).

LaTeX (`sections/04-volatility/section.tex` l.1676–1691, verbatim):
```latex
\begin{definition}[Profiles]\label{def:app-vol-closed-profile}
A \emph{profile} is a countable family $\xi=(\xi_\alpha)_{\alpha\in\mathcal A}$ of real
random variables with $\sum_\alpha\EE\xi_\alpha^2<\infty$ and $\Pr(\xi_\alpha\ne0)>0$ for
some $\alpha$. Its scalar functions are, for $q\ge0$,
\[
F_\xi(q)\defeq\sum_\alpha\EE\frac{\xi_\alpha^2}{1+q\xi_\alpha^2},\qquad r_\xi(q)\defeq qF_\xi(q).
\]
A \emph{paired profile} is a countable family $(\xi_{1,\alpha},\xi_{2,\alpha})_{\alpha\in\mathcal A}$
such that $\xi_1=(\xi_{1,\alpha})$ and $\xi_2=(\xi_{2,\alpha})$ are profiles,
$\xi_{1,\alpha}\xi_{2,\alpha}\ge0$, and $\sum_\alpha\EE[\xi_{1,\alpha}^2\xi_{2,\alpha}^2]<\infty$. Its
two-point functions are, for $q_1,q_2\ge0$,
\[
b(q_1,q_2)\defeq\sum_\alpha\EE\frac{\xi_{1,\alpha}\xi_{2,\alpha}}{(1+q_1\xi_{1,\alpha}^2)(1+q_2\xi_{2,\alpha}^2)},\qquad
e(q_1,q_2)\defeq\sum_\alpha\EE\frac{\xi_{1,\alpha}^2\xi_{2,\alpha}^2}{(1+q_1\xi_{1,\alpha}^2)(1+q_2\xi_{2,\alpha}^2)}.
\]
\end{definition}
```
-/
structure def_app_vol_closed_profile_ii (P : Measure Ω) (ξ₁ ξ₂ : ι → Ω → ℝ) : Prop where
  profile₁ : def_app_vol_closed_profile P ξ₁
  profile₂ : def_app_vol_closed_profile P ξ₂
  nonneg_prod : ∀ α ω, 0 ≤ ξ₁ α ω * ξ₂ α ω
  integrable_sq_prod : ∀ α, Integrable (fun ω => ξ₁ α ω ^ 2 * ξ₂ α ω ^ 2) P
  summable_sq_prod : Summable (fun α => ∫ ω, ξ₁ α ω ^ 2 * ξ₂ α ω ^ 2 ∂P)

/-- `F_ξ(q) = ∑_α E[ξ_α² / (1 + q ξ_α²)]` (`def:app-vol-closed-profile`). -/
def profileF (P : Measure Ω) (ξ : ι → Ω → ℝ) (q : ℝ) : ℝ :=
  ∑' α, ∫ ω, ξ α ω ^ 2 / (1 + q * ξ α ω ^ 2) ∂P

/-- `r_ξ(q) = q F_ξ(q)` (`def:app-vol-closed-profile`). -/
def profileR (P : Measure Ω) (ξ : ι → Ω → ℝ) (q : ℝ) : ℝ :=
  q * profileF P ξ q

/-- The series `∑_α E[ξ_α² / (1 + q ξ_α²)²]` of `lem:app-vol-closed-profile`(a), the derivative
`r'_ξ(q)`. -/
def profileRDeriv (P : Measure Ω) (ξ : ι → Ω → ℝ) (q : ℝ) : ℝ :=
  ∑' α, ∫ ω, ξ α ω ^ 2 / (1 + q * ξ α ω ^ 2) ^ 2 ∂P

/-- The series `∑_α E[ξ_α⁴ / (1 + q ξ_α²)²]` of `lem:app-vol-closed-profile`(a), which is `-F'_ξ(q)`
for `q > 0`. -/
def profileNegFDeriv (P : Measure Ω) (ξ : ι → Ω → ℝ) (q : ℝ) : ℝ :=
  ∑' α, ∫ ω, ξ α ω ^ 4 / (1 + q * ξ α ω ^ 2) ^ 2 ∂P

/-- The two-point function `b(q₁, q₂) = ∑_α E[ξ₁_α ξ₂_α / ((1 + q₁ ξ₁_α²)(1 + q₂ ξ₂_α²))]`
(`def:app-vol-closed-profile`). -/
def pairedB (P : Measure Ω) (ξ₁ ξ₂ : ι → Ω → ℝ) (q₁ q₂ : ℝ) : ℝ :=
  ∑' α, ∫ ω, ξ₁ α ω * ξ₂ α ω / ((1 + q₁ * ξ₁ α ω ^ 2) * (1 + q₂ * ξ₂ α ω ^ 2)) ∂P

/-- The two-point function `e(q₁, q₂) = ∑_α E[ξ₁_α² ξ₂_α² / ((1 + q₁ ξ₁_α²)(1 + q₂ ξ₂_α²))]`
(`def:app-vol-closed-profile`). -/
def pairedE (P : Measure Ω) (ξ₁ ξ₂ : ι → Ω → ℝ) (q₁ q₂ : ℝ) : ℝ :=
  ∑' α, ∫ ω, ξ₁ α ω ^ 2 * ξ₂ α ω ^ 2 / ((1 + q₁ * ξ₁ α ω ^ 2) * (1 + q₂ * ξ₂ α ω ^ 2)) ∂P

/-! ## The EMA paired profile -/

/-- `g` is a family of independent standard Gaussians (the `g_α` of the EMA paragraph after
`def:app-vol-closed-profile`). -/
def IsStdGaussianFamily {A : Type*} (P : Measure Ω) (g : A → Ω → ℝ) : Prop :=
  (∀ a, Measurable (g a)) ∧ iIndepFun g P ∧ ∀ a, HasLaw (g a) (gaussianReal 0 1) P

/-- First coordinate of the EMA paired profile at lag `ℓ` and weight `β`: `(emaw_j g_j)` on the
shared labels `j ≥ 0`, and `0` on the fresh labels `m ∈ {1,…,ℓ}` (`inr i`, `m = i + 1`). -/
def emaXi₁ (β : ℝ) (ℓ : ℕ) (g : ℕ ⊕ Fin ℓ → Ω → ℝ) : ℕ ⊕ Fin ℓ → Ω → ℝ
  | Sum.inl j => fun ω => Muon.emaW β j * g (Sum.inl j) ω
  | Sum.inr _ => fun _ => 0

/-- Second coordinate of the EMA paired profile at lag `ℓ`: `β^ℓ emaw_j g_j` on the shared labels,
and `emaw_{ℓ-m} g_m` on the fresh labels `m = i + 1`. -/
def emaXi₂ (β : ℝ) (ℓ : ℕ) (g : ℕ ⊕ Fin ℓ → Ω → ℝ) : ℕ ⊕ Fin ℓ → Ω → ℝ
  | Sum.inl j => fun ω => β ^ ℓ * Muon.emaW β j * g (Sum.inl j) ω
  | Sum.inr i => fun ω => Muon.emaW β (ℓ - (i.val + 1)) * g (Sum.inr i) ω

/-! ## Branch points of a profile -/

/-- A branch point of the scalar function `F` at `s`, in the source's unknowns `(σ, σ̃, s̃₁, s₁)`
(`lem:app-vol-closed-branch`, `eqn:app-vol-closed-branch`). With `q = s σ σ̃`:
`σ = (1/B) Tr Σ_out (s Id + s̃₁ Σ_out)⁻¹`, `σ̃ = (1/B) Tr Σ_in (s Id + s₁ Σ_in)⁻¹`,
`s̃₁ = s σ̃ F(q)`, `s₁ = s σ F(q)`, all four entries nonnegative. -/
def IsBranchPoint {m n : ℕ} (F : ℝ → ℝ) (C : Muon.Covariances m n) (B : ℕ) (s : ℝ) :
    ℝ × ℝ × ℝ × ℝ → Prop
  | (σ, σ', a, c) =>
    0 ≤ σ ∧ 0 ≤ σ' ∧ 0 ≤ a ∧ 0 ≤ c ∧
    σ = (B : ℝ)⁻¹ * (C.Sout * (s • (1 : Matrix (Fin m) (Fin m) ℝ) + a • C.Sout)⁻¹).trace ∧
    σ' = (B : ℝ)⁻¹ * (C.Sin * (s • (1 : Matrix (Fin n) (Fin n) ℝ) + c • C.Sin)⁻¹).trace ∧
    a = s * σ' * F (s * σ * σ') ∧ c = s * σ * F (s * σ * σ')

open scoped Classical in
/-- The branch point of `F` at `s`: the chosen solution when one exists, and `0` otherwise
(the total map, as `Muon.DetEquiv.branchSol`). -/
def branchPt {m n : ℕ} (F : ℝ → ℝ) (C : Muon.Covariances m n) (B : ℕ) (s : ℝ) :
    ℝ × ℝ × ℝ × ℝ :=
  if h : ∃ x, IsBranchPoint F C B s x then h.choose else 0

/-! ## Two-point quantities and the determinant -/

/-- `𝒯^out[F](s,u) = (1/B) Tr(F Σ_out R̄(-s) R̄(-u))` with the first buffer's branch point `x` at `s`
and the second's `y` at `u` (`eqn:app-vol-closed-objects`). -/
def toutT {m n : ℕ} (C : Muon.Covariances m n) (B : ℕ) (x y : ℝ × ℝ × ℝ × ℝ) (s u : ℝ)
    (F : Matrix (Fin m) (Fin m) ℝ) : ℝ :=
  (B : ℝ)⁻¹ * (F * C.Sout * (s • (1 : Matrix (Fin m) (Fin m) ℝ) + x.2.2.1 • C.Sout)⁻¹ *
    (u • (1 : Matrix (Fin m) (Fin m) ℝ) + y.2.2.1 • C.Sout)⁻¹).trace

/-- `𝒯^in[G](s,u) = (1/B) Tr(G Σ_in R̃(-s) R̃(-u))`, with the fourth branch coordinates
(`eqn:app-vol-closed-objects`). -/
def tinT {m n : ℕ} (C : Muon.Covariances m n) (B : ℕ) (x y : ℝ × ℝ × ℝ × ℝ) (s u : ℝ)
    (G : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  (B : ℝ)⁻¹ * (G * C.Sin * (s • (1 : Matrix (Fin n) (Fin n) ℝ) + x.2.2.2 • C.Sin)⁻¹ *
    (u • (1 : Matrix (Fin n) (Fin n) ℝ) + y.2.2.2 • C.Sin)⁻¹).trace

/-- The determinant `Δ_ξ` of `eqn:app-vol-closed-profile-kernel` and `eqn:app-vol-closed-Delta`,
written in terms of the two branch points `x` (at `s`) and `y` (at `u`), the two-point functions
`b, e` at `(q, q')`. The source's `𝖴 = 𝒯^out[Σ_out]`, `𝖵 = 𝒯^in[Σ_in]`. -/
def closedDelta {m n : ℕ} (C : Muon.Covariances m n) (B : ℕ) (x y : ℝ × ℝ × ℝ × ℝ) (s u b e : ℝ) :
    ℝ :=
  (1 - s * u * toutT C B x y s u C.Sout * x.2.1 * y.2.1 * e) *
      (1 - s * u * tinT C B x y s u C.Sin * x.1 * y.1 * e) -
    s * u * toutT C B x y s u C.Sout * tinT C B x y s u C.Sin * b ^ 2

/-- `Δ_ξ(s,u)` of a paired profile: the branch points of `ξ₁` at `s` and of `ξ₂` at `u`, and the
two-point functions at `q = s σ σ̃` and `q' = u σ' σ̃'` (`eqn:app-vol-closed-profile-kernel`). -/
def profileDelta (P : Measure Ω) {m n : ℕ} (C : Muon.Covariances m n) (B : ℕ)
    (ξ₁ ξ₂ : ι → Ω → ℝ) (s u : ℝ) : ℝ :=
  let x := branchPt (profileF P ξ₁) C B s
  let y := branchPt (profileF P ξ₂) C B u
  closedDelta C B x y s u (pairedB P ξ₁ ξ₂ (s * x.1 * x.2.1) (u * y.1 * y.2.1))
    (pairedE P ξ₁ ξ₂ (s * x.1 * x.2.1) (u * y.1 * y.2.1))

/-- `κ_Σ = max((1/B) Tr Σ_in ‖Σ_out‖, (1/B) Tr Σ_out ‖Σ_in‖)` (`eqn:app-vol-closed-Delta`
constants, l.1497–1506). -/
def kappaSigma {m n : ℕ} (C : Muon.Covariances m n) (B : ℕ) : ℝ :=
  max ((B : ℝ)⁻¹ * C.Sin.trace * Muon.opNorm C.Sout)
    ((B : ℝ)⁻¹ * C.Sout.trace * Muon.opNorm C.Sin)

/-- `θ_Σ(t) = t / (t + κ_Σ)` for `t > 0` (l.1497–1506). -/
def thetaSigma {m n : ℕ} (C : Muon.Covariances m n) (B : ℕ) (t : ℝ) : ℝ :=
  t / (t + kappaSigma C B)

/-- `qh_β = r_β⁻¹(γ⋆)`, encoded as the supremum of `{q ≥ 0 : r_β(q) ≤ γ⋆}` at the EMA weights
`Muon.emaW β` (l.1497–1506; `r_β` is continuous and strictly increasing). -/
def qhatBeta (β γ : ℝ) : ℝ :=
  sSup {q : ℝ | 0 ≤ q ∧ Muon.DetEquiv.rW (Muon.emaW β) q ≤ γ}

/-- `ε_β = min_{q ∈ [0, qh_β]} min{ (e₀² E[g²(1+q e₀²g²)⁻²]) / r'_β(q), (e₀⁴ E[g⁴(1+q e₀²g²)⁻²]) /
(-F'_β(q)) }` with `e₀ = emaw_0` and `g` standard Gaussian (l.1497–1506). The derivatives are the right
derivatives on `Ici 0` (`derivWithin`), since `r_β` and `F_β` are defined by the source only on `q ≥ 0`. -/
def epsBeta (β γ : ℝ) : ℝ :=
  sInf ((fun q : ℝ =>
    min ((Muon.emaW β 0 ^ 2 * ∫ g, g ^ 2 / (1 + q * Muon.emaW β 0 ^ 2 * g ^ 2) ^ 2
        ∂(gaussianReal 0 1)) / derivWithin (Muon.DetEquiv.rW (Muon.emaW β)) (Ici 0) q)
      ((Muon.emaW β 0 ^ 4 * ∫ g, g ^ 4 / (1 + q * Muon.emaW β 0 ^ 2 * g ^ 2) ^ 2
        ∂(gaussianReal 0 1)) / (-derivWithin (Muon.DetEquiv.Fw (Muon.emaW β)) (Ici 0) q))) ''
    Icc 0 (qhatBeta β γ))

/-- The cutoff label set `𝒜 = {-j : 0 ≤ j ≤ J} ∪ {m : 1 ≤ m ≤ ℓ}` (`sec:app-vol-tree`). -/
def cutoffLabels (J ℓ : ℕ) : Finset ℤ :=
  Finset.Icc (-(J : ℤ)) 0 ∪ Finset.Icc 1 (ℓ : ℤ)

/-- The cutoff coefficients `ϖ_{l,α}` of `eqn:app-vol-tree-coefficients` on `𝒜` and `0` off `𝒜`, so
that the labels of the cutoff profile are finite (`Muon.Volatility.treeVarpi`, TreeDef.lean). -/
def cutoffVarpi (β : ℝ) (ℓ J l : ℕ) (α : ℤ) : ℝ :=
  if α ∈ cutoffLabels J ℓ then treeVarpi β ℓ l α else 0

/-- The cutoff paired profile at `(ℓ, J, R)`: `ξ_{l,α} = ϖ_{l,α} g̃_α` with
`g̃_α = g_α 1_{|g_α| ≤ R}`, one truncated variable per label, shared by the two buffers. -/
def cutoffXi (β : ℝ) (ℓ J : ℕ) (R : ℝ) (l : ℕ) (g : ℤ → Ω → ℝ) : ℤ → Ω → ℝ :=
  fun α ω => cutoffVarpi β ℓ J l α * (if |g α ω| ≤ R then g α ω else 0)

/-! ## Statements -/

/-! ### Private helpers for `lem:app-vol-closed-profile`(a) (task P-D.15.P1) -/

private theorem p1a_term_bound {f : Ω → ℝ} (q : ℝ) (hq : 0 ≤ q) (ω : Ω) :
    ‖f ω ^ 2 / (1 + q * f ω ^ 2)‖ ≤ f ω ^ 2 := by
  have h1 : 0 ≤ q * f ω ^ 2 := mul_nonneg hq (sq_nonneg _)
  have h2 : 1 ≤ 1 + q * f ω ^ 2 := by linarith
  rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (sq_nonneg _) (by linarith))]
  exact div_le_self (sq_nonneg _) h2

private theorem p1a_term_nonneg {f : Ω → ℝ} {q : ℝ} (hq : 0 ≤ q) (ω : Ω) :
    0 ≤ f ω ^ 2 / (1 + q * f ω ^ 2) :=
  div_nonneg (sq_nonneg _) (by
    have : 0 ≤ q * f ω ^ 2 := mul_nonneg hq (sq_nonneg _)
    linarith)

private theorem p1a_term_integrable {P : Measure Ω} {f : Ω → ℝ} (hf : Measurable f) {q : ℝ} (hq : 0 ≤ q)
    (hsq : Integrable (fun ω => f ω ^ 2) P) :
    Integrable (fun ω => f ω ^ 2 / (1 + q * f ω ^ 2)) P :=
  Integrable.mono' hsq
    ((((hf.pow_const 2)).div (measurable_const.add (measurable_const.mul (hf.pow_const 2)))).aestronglyMeasurable)
    (ae_of_all _ (p1a_term_bound q hq))

private theorem p1a_int_term_le {P : Measure Ω} {f : Ω → ℝ} {q : ℝ} (hq : 0 ≤ q)
    (hsq : Integrable (fun ω => f ω ^ 2) P) :
    ∫ ω, f ω ^ 2 / (1 + q * f ω ^ 2) ∂P ≤ ∫ ω, f ω ^ 2 ∂P :=
  integral_mono_of_nonneg (ae_of_all _ (p1a_term_nonneg hq)) hsq
    (ae_of_all _ (fun ω => (le_abs_self _).trans (p1a_term_bound (f := f) q hq ω)))

private theorem p1a_summable_term {ι : Type*} {P : Measure Ω} {ξ : ι → Ω → ℝ}
    (hsq : ∀ α, Integrable (fun ω => ξ α ω ^ 2) P)
    (hsum : Summable (fun α => ∫ ω, ξ α ω ^ 2 ∂P)) {q : ℝ} (hq : 0 ≤ q) :
    Summable (fun α => ∫ ω, ξ α ω ^ 2 / (1 + q * ξ α ω ^ 2) ∂P) :=
  Summable.of_nonneg_of_le
    (fun α => integral_nonneg (p1a_term_nonneg hq))
    (fun α => p1a_int_term_le hq (hsq α)) hsum

private theorem p1a_profileF_antitoneOn {ι : Type*} {P : Measure Ω} {ξ : ι → Ω → ℝ}
    (hmeas : ∀ α, Measurable (ξ α))
    (hsq : ∀ α, Integrable (fun ω => ξ α ω ^ 2) P)
    (hsum : Summable (fun α => ∫ ω, ξ α ω ^ 2 ∂P)) :
    AntitoneOn (fun q : ℝ => ∑' α, ∫ ω, ξ α ω ^ 2 / (1 + q * ξ α ω ^ 2) ∂P) (Ici 0) := by
  intro q hq q' hq' hqq'
  have hq0 : (0 : ℝ) ≤ q := hq
  have hq0' : (0 : ℝ) ≤ q' := hq'
  apply Summable.tsum_le_tsum _ (p1a_summable_term hsq hsum hq0') (p1a_summable_term hsq hsum hq0)
  intro α
  apply integral_mono_of_nonneg (ae_of_all _ (p1a_term_nonneg hq0')) 
    (p1a_term_integrable (hmeas α) hq0 (hsq α))
  refine ae_of_all _ (fun ω => ?_)
  have h1 : 0 ≤ ξ α ω ^ 2 := sq_nonneg _
  have h2 : 0 < 1 + q * ξ α ω ^ 2 := by
    have : 0 ≤ q * ξ α ω ^ 2 := mul_nonneg hq0 (sq_nonneg _)
    linarith
  have h3 : 1 + q * ξ α ω ^ 2 ≤ 1 + q' * ξ α ω ^ 2 := by
    have : q * ξ α ω ^ 2 ≤ q' * ξ α ω ^ 2 := mul_le_mul_of_nonneg_right hqq' (sq_nonneg _)
    linarith
  exact div_le_div_of_nonneg_left h1 h2 h3

private theorem p1a_profileF_pos {ι : Type*} {P : Measure Ω} {ξ : ι → Ω → ℝ}
    (hmeas : ∀ α, Measurable (ξ α))
    (hsq : ∀ α, Integrable (fun ω => ξ α ω ^ 2) P)
    (hsum : Summable (fun α => ∫ ω, ξ α ω ^ 2 ∂P)) {α₀ : ι}
    (hα₀ : 0 < P {ω | ξ α₀ ω ≠ 0}) {q : ℝ} (hq : 0 ≤ q) :
    0 < ∑' α, ∫ ω, ξ α ω ^ 2 / (1 + q * ξ α ω ^ 2) ∂P := by
  refine (p1a_summable_term hsq hsum hq).tsum_pos (fun α => integral_nonneg (p1a_term_nonneg hq)) α₀ ?_
  rw [integral_pos_iff_support_of_nonneg (p1a_term_nonneg hq) (p1a_term_integrable (hmeas α₀) hq (hsq α₀))]
  refine lt_of_lt_of_le hα₀ (measure_mono ?_)
  intro ω hω
  simp only [mem_setOf_eq] at hω
  simp only [Function.mem_support, ne_eq]
  have h1 : 0 < ξ α₀ ω ^ 2 := by positivity
  have h2 : 0 < 1 + q * ξ α₀ ω ^ 2 := by
    have : 0 ≤ q * ξ α₀ ω ^ 2 := mul_nonneg hq (sq_nonneg _)
    linarith
  exact (div_pos h1 h2).ne'

private theorem p1a_term_continuousOn {P : Measure Ω} {f : Ω → ℝ} (hf : Measurable f)
    (hsq : Integrable (fun ω => f ω ^ 2) P) :
    ContinuousOn (fun q : ℝ => ∫ ω, f ω ^ 2 / (1 + q * f ω ^ 2) ∂P) (Ici 0) := by
  apply continuousOn_of_dominated (bound := fun ω => f ω ^ 2)
  · intro q hq
    exact ((hf.pow_const 2).div (measurable_const.add (measurable_const.mul (hf.pow_const 2)))).aestronglyMeasurable
  · intro q hq
    exact ae_of_all _ (fun ω => p1a_term_bound (f := f) q hq ω)
  · exact hsq
  · refine ae_of_all _ (fun ω q hq => ?_)
    have hpos : 1 + q * f ω ^ 2 ≠ 0 := by
      have : 0 ≤ q * f ω ^ 2 := mul_nonneg hq (sq_nonneg _)
      linarith
    have hc : ContinuousAt (fun x : ℝ => f ω ^ 2 / (1 + x * f ω ^ 2)) q :=
      ContinuousAt.div (by fun_prop) (by fun_prop) hpos
    exact hc.continuousWithinAt

private theorem p1a_tsum_continuousOn {ι : Type*} {P : Measure Ω} [IsProbabilityMeasure P] {ξ : ι → Ω → ℝ}
    (hmeas : ∀ α, Measurable (ξ α)) (hsq : ∀ α, Integrable (fun ω => ξ α ω ^ 2) P)
    (hsum : Summable (fun α => ∫ ω, ξ α ω ^ 2 ∂P)) :
    ContinuousOn (fun q : ℝ => ∑' α, ∫ ω, ξ α ω ^ 2 / (1 + q * ξ α ω ^ 2) ∂P) (Ici 0) := by
  apply continuousOn_tsum (u := fun α => ∫ ω, ξ α ω ^ 2 ∂P)
  · exact fun α => p1a_term_continuousOn (hmeas α) (hsq α)
  · exact hsum
  · intro α q hq
    have hnn : 0 ≤ ∫ ω, ξ α ω ^ 2 / (1 + q * ξ α ω ^ 2) ∂P :=
      integral_nonneg (fun ω => div_nonneg (sq_nonneg _) (by
        have : 0 ≤ q * ξ α ω ^ 2 := mul_nonneg hq (sq_nonneg _)
        linarith))
    rw [Real.norm_eq_abs, abs_of_nonneg hnn]
    apply integral_mono_of_nonneg (ae_of_all _ (fun ω => ?_)) (hsq α)
      (ae_of_all _ (fun ω => ?_))
    · exact div_nonneg (sq_nonneg _) (by
        have : 0 ≤ q * ξ α ω ^ 2 := mul_nonneg hq (sq_nonneg _)
        linarith)
    · exact (le_abs_self _).trans (p1a_term_bound (f := fun ω => ξ α ω) q hq ω)

private theorem p1b_norm_den {a : ℝ} (ha : 0 ≤ a) {z : ℂ} (hz : 0 ≤ z.re) :
    1 + z.re * a ≤ ‖1 + z * (a : ℂ)‖ := by
  have h := Complex.abs_re_le_norm (1 + z * (a : ℂ))
  have h2 : (1 + z * (a : ℂ)).re = 1 + z.re * a := by simp
  rw [h2] at h
  exact (le_abs_self _).trans h

private theorem p1b_term_bound {a : ℝ} (ha : 0 ≤ a) {z : ℂ} (hz : 0 ≤ z.re) :
    ‖(a : ℂ) / (1 + z * (a : ℂ))‖ ≤ a := by
  have h := p1b_norm_den ha hz
  have h1 : 1 ≤ ‖1 + z * (a : ℂ)‖ := by nlinarith [mul_nonneg hz ha]
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ha]
  exact div_le_self ha h1

private theorem p1b_deriv_bound {a : ℝ} (ha : 0 ≤ a) {c : ℝ} (hc : 0 < c) {z : ℂ} (hz : c ≤ z.re) :
    ‖(a : ℂ) ^ 2 / (1 + z * (a : ℂ)) ^ 2‖ ≤ a / c := by
  have h := p1b_norm_den ha (hc.le.trans hz)
  have h0 : 0 < 1 + c * a := by nlinarith [mul_nonneg hc.le ha]
  have h1 : 1 + c * a ≤ ‖1 + z * (a : ℂ)‖ := by nlinarith [mul_le_mul_of_nonneg_right hz ha]
  rw [norm_div, norm_pow, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ha]
  rw [div_le_div_iff₀ (pow_pos (lt_of_lt_of_le h0 h1) 2) hc]
  have h2 : (1 + c * a) ^ 2 ≤ ‖1 + z * (a : ℂ)‖ ^ 2 := by gcongr
  nlinarith [mul_nonneg ha hc.le, mul_nonneg ha (sq_nonneg (c * a)), sq_nonneg a, mul_nonneg ha ha]

private theorem p1b_measurable_cast {Ω : Type*} [MeasurableSpace Ω] {f : Ω → ℝ} (hf : Measurable f) :
    Measurable (fun ω => ((f ω ^ 2 : ℝ) : ℂ)) :=
  Complex.measurable_ofReal.comp (hf.pow_const 2)

private theorem p1b_term_hasDerivAt {P : Measure Ω} {f : Ω → ℝ} (hf : Measurable f)
    (hsq : Integrable (fun ω => f ω ^ 2) P) {z₀ : ℂ} (hz₀ : 0 < z₀.re) :
    HasDerivAt (fun z : ℂ => ∫ ω, ((f ω ^ 2 : ℝ) : ℂ) / (1 + z * ((f ω ^ 2 : ℝ) : ℂ)) ∂P)
      (-∫ ω, ((f ω ^ 2 : ℝ) : ℂ) ^ 2 / (1 + z₀ * ((f ω ^ 2 : ℝ) : ℂ)) ^ 2 ∂P) z₀ := by
  have hm := p1b_measurable_cast hf
  have hcpos : 0 < z₀.re / 2 := by linarith
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := P) (𝕜 := ℂ)
    (F := fun z ω => ((f ω ^ 2 : ℝ) : ℂ) / (1 + z * ((f ω ^ 2 : ℝ) : ℂ)))
    (F' := fun z ω => -(((f ω ^ 2 : ℝ) : ℂ) ^ 2 / (1 + z * ((f ω ^ 2 : ℝ) : ℂ)) ^ 2))
    (x₀ := z₀) (bound := fun ω => f ω ^ 2 / (z₀.re / 2)) (s := Metric.ball z₀ (z₀.re / 2))
    (Metric.ball_mem_nhds _ hcpos) ?_ ?_ ?_ ?_ ?_ ?_
  · have := key.2
    simpa [integral_neg] using this
  · exact Filter.Eventually.of_forall (fun z =>
      (hm.div (measurable_const.add (measurable_const.mul hm))).aestronglyMeasurable)
  · refine Integrable.mono' hsq
      (hm.div (measurable_const.add (measurable_const.mul hm))).aestronglyMeasurable
      (ae_of_all _ (fun ω => ?_))
    simpa using p1b_term_bound (sq_nonneg (f ω)) hz₀.le
  · exact ((hm.pow_const 2).div ((measurable_const.add (measurable_const.mul hm)).pow_const 2)).neg.aestronglyMeasurable
  · refine ae_of_all _ (fun ω z hz => ?_)
    have hre : z₀.re / 2 ≤ z.re := by
      have h1 := Complex.abs_re_le_norm (z - z₀)
      have h2 : ‖z - z₀‖ < z₀.re / 2 := by simpa [dist_eq_norm] using hz
      have h3 : (z - z₀).re = z.re - z₀.re := by simp
      rw [h3] at h1
      have := neg_abs_le (z.re - z₀.re)
      linarith
    rw [norm_neg]
    exact p1b_deriv_bound (sq_nonneg (f ω)) hcpos hre
  · exact hsq.div_const _
  · refine ae_of_all _ (fun ω z hz => ?_)
    have hre : z₀.re / 2 ≤ z.re := by
      have h1 := Complex.abs_re_le_norm (z - z₀)
      have h2 : ‖z - z₀‖ < z₀.re / 2 := by simpa [dist_eq_norm] using hz
      have h3 : (z - z₀).re = z.re - z₀.re := by simp
      rw [h3] at h1
      have := neg_abs_le (z.re - z₀.re)
      linarith
    have hne : (1 + z * ((f ω ^ 2 : ℝ) : ℂ)) ≠ 0 := by
      have := p1b_norm_den (sq_nonneg (f ω)) (hcpos.le.trans hre)
      intro h0
      rw [h0, norm_zero] at this
      nlinarith [mul_nonneg (hcpos.le.trans hre) (sq_nonneg (f ω))]
    have hd : HasDerivAt (fun x : ℂ => 1 + x * ((f ω ^ 2 : ℝ) : ℂ)) ((f ω ^ 2 : ℝ) : ℂ) z := by
      exact (((hasDerivAt_id z).mul_const ((f ω ^ 2 : ℝ) : ℂ)).const_add 1).congr_deriv (one_mul _)
    have := (hasDerivAt_const z ((f ω ^ 2 : ℝ) : ℂ)).div hd hne
    convert this using 1
    ring

private theorem p1b_FC_hasDerivAt {ι : Type*} {P : Measure Ω} {ξ : ι → Ω → ℝ}
    (hmeas : ∀ α, Measurable (ξ α)) (hsq : ∀ α, Integrable (fun ω => ξ α ω ^ 2) P)
    (hsum : Summable (fun α => ∫ ω, ξ α ω ^ 2 ∂P)) {z₀ : ℂ} (hz₀ : 0 < z₀.re) :
    HasDerivAt (fun z : ℂ => ∑' α, ∫ ω, ((ξ α ω ^ 2 : ℝ) : ℂ) / (1 + z * ((ξ α ω ^ 2 : ℝ) : ℂ)) ∂P)
      (∑' α, -∫ ω, ((ξ α ω ^ 2 : ℝ) : ℂ) ^ 2 / (1 + z₀ * ((ξ α ω ^ 2 : ℝ) : ℂ)) ^ 2 ∂P) z₀ := by
  have hc : 0 < z₀.re / 2 := by linarith
  have hre : ∀ z : ℂ, z₀.re / 2 < z.re → 0 < z.re := fun z hz => by linarith
  refine hasDerivAt_tsum_of_isPreconnected (t := {z : ℂ | z₀.re / 2 < z.re})
    (u := fun α => (∫ ω, ξ α ω ^ 2 ∂P) / (z₀.re / 2))
    (g := fun α z => ∫ ω, ((ξ α ω ^ 2 : ℝ) : ℂ) / (1 + z * ((ξ α ω ^ 2 : ℝ) : ℂ)) ∂P)
    (g' := fun α z => -∫ ω, ((ξ α ω ^ 2 : ℝ) : ℂ) ^ 2 / (1 + z * ((ξ α ω ^ 2 : ℝ) : ℂ)) ^ 2 ∂P)
    (y₀ := z₀) (hsum.div_const _) (isOpen_lt continuous_const Complex.continuous_re)
    (convex_halfSpace_re_gt _).isPreconnected ?_ ?_ (by simp [hz₀, hc]) ?_ (by simpa using hc)
  · intro α z hz
    exact p1b_term_hasDerivAt (hmeas α) (hsq α) (hre z hz)
  · intro α z hz
    rw [norm_neg]
    refine (norm_integral_le_of_norm_le ((hsq α).div_const (z₀.re / 2)) (ae_of_all _ (fun ω => ?_))).trans ?_
    · exact p1b_deriv_bound (sq_nonneg (ξ α ω)) hc (le_of_lt hz)
    · rw [integral_div]
  · refine Summable.of_norm_bounded hsum (fun α => ?_)
    refine norm_integral_le_of_norm_le (hsq α) (ae_of_all _ (fun ω => ?_))
    exact p1b_term_bound (sq_nonneg (ξ α ω)) hz₀.le

private theorem p1b_FC_ofReal {ι : Type*} {P : Measure Ω} {ξ : ι → Ω → ℝ} (x : ℝ) :
    (∑' α, ∫ ω, ((ξ α ω ^ 2 : ℝ) : ℂ) / (1 + (x : ℂ) * ((ξ α ω ^ 2 : ℝ) : ℂ)) ∂P) =
      ((∑' α, ∫ ω, ξ α ω ^ 2 / (1 + x * ξ α ω ^ 2) ∂P : ℝ) : ℂ) := by
  rw [Complex.ofReal_tsum]
  refine tsum_congr (fun α => ?_)
  rw [← integral_complex_ofReal]
  refine integral_congr_ae (ae_of_all _ (fun ω => ?_))
  push_cast
  rfl

private theorem p1b_F_hasDerivAt {ι : Type*} {P : Measure Ω} {ξ : ι → Ω → ℝ}
    (hmeas : ∀ α, Measurable (ξ α)) (hsq : ∀ α, Integrable (fun ω => ξ α ω ^ 2) P)
    (hsum : Summable (fun α => ∫ ω, ξ α ω ^ 2 ∂P)) {q : ℝ} (hq : 0 < q) :
    HasDerivAt (fun x : ℝ => ∑' α, ∫ ω, ξ α ω ^ 2 / (1 + x * ξ α ω ^ 2) ∂P)
      (-∑' α, ∫ ω, ξ α ω ^ 4 / (1 + q * ξ α ω ^ 2) ^ 2 ∂P) q := by
  have hC := (p1b_FC_hasDerivAt hmeas hsq hsum (z₀ := (q : ℂ)) (by simpa using hq)).real_of_complex
  have hfun : (fun x : ℝ => ((∑' α, ∫ ω, ((ξ α ω ^ 2 : ℝ) : ℂ) /
      (1 + (x : ℂ) * ((ξ α ω ^ 2 : ℝ) : ℂ)) ∂P)).re) =
      (fun x : ℝ => ∑' α, ∫ ω, ξ α ω ^ 2 / (1 + x * ξ α ω ^ 2) ∂P) := by
    funext x
    rw [p1b_FC_ofReal (P := P) (ξ := ξ) x, Complex.ofReal_re]
  have hval : (∑' α, -∫ ω, ((ξ α ω ^ 2 : ℝ) : ℂ) ^ 2 /
      (1 + (q : ℂ) * ((ξ α ω ^ 2 : ℝ) : ℂ)) ^ 2 ∂P).re =
      -∑' α, ∫ ω, ξ α ω ^ 4 / (1 + q * ξ α ω ^ 2) ^ 2 ∂P := by
    have : (∑' α, -∫ ω, ((ξ α ω ^ 2 : ℝ) : ℂ) ^ 2 /
        (1 + (q : ℂ) * ((ξ α ω ^ 2 : ℝ) : ℂ)) ^ 2 ∂P) =
        ((-∑' α, ∫ ω, ξ α ω ^ 4 / (1 + q * ξ α ω ^ 2) ^ 2 ∂P : ℝ) : ℂ) := by
      rw [Complex.ofReal_neg, Complex.ofReal_tsum, ← tsum_neg]
      refine tsum_congr (fun α => ?_)
      rw [← integral_complex_ofReal]
      congr 1
      refine integral_congr_ae (ae_of_all _ (fun ω => ?_))
      push_cast
      ring_nf
    rw [this, Complex.ofReal_re]
  rw [hfun, hval] at hC
  exact hC

private theorem p1b_F_analyticOn {ι : Type*} {P : Measure Ω} {ξ : ι → Ω → ℝ}
    (hmeas : ∀ α, Measurable (ξ α)) (hsq : ∀ α, Integrable (fun ω => ξ α ω ^ 2) P)
    (hsum : Summable (fun α => ∫ ω, ξ α ω ^ 2 ∂P)) :
    AnalyticOnNhd ℝ (fun x : ℝ => ∑' α, ∫ ω, ξ α ω ^ 2 / (1 + x * ξ α ω ^ 2) ∂P) (Ioi 0) := by
  have hd : DifferentiableOn ℂ (fun z : ℂ => ∑' α, ∫ ω, ((ξ α ω ^ 2 : ℝ) : ℂ) /
      (1 + z * ((ξ α ω ^ 2 : ℝ) : ℂ)) ∂P) {z : ℂ | 0 < z.re} :=
    fun z hz => (p1b_FC_hasDerivAt hmeas hsq hsum hz).differentiableAt.differentiableWithinAt
  have ha := hd.analyticOnNhd (isOpen_lt continuous_const Complex.continuous_re)
  intro x hx
  have h1 : AnalyticAt ℂ (fun z : ℂ => ∑' α, ∫ ω, ((ξ α ω ^ 2 : ℝ) : ℂ) /
      (1 + z * ((ξ α ω ^ 2 : ℝ) : ℂ)) ∂P) (x : ℂ) := ha _ (by simpa using hx)
  have h2 := h1.restrictScalars (𝕜 := ℝ)
  have h3 := (Complex.reCLM.analyticAt _).comp (h2.comp (Complex.ofRealCLM.analyticAt x))
  have hfun : (fun x : ℝ => ((∑' α, ∫ ω, ((ξ α ω ^ 2 : ℝ) : ℂ) /
      (1 + (x : ℂ) * ((ξ α ω ^ 2 : ℝ) : ℂ)) ∂P)).re) =
      (fun x : ℝ => ∑' α, ∫ ω, ξ α ω ^ 2 / (1 + x * ξ α ω ^ 2) ∂P) := by
    funext x
    rw [p1b_FC_ofReal (P := P) (ξ := ξ) x, Complex.ofReal_re]
  rw [← hfun]
  exact h3

private theorem p1c_meas_d {f : Ω → ℝ} (hf : Measurable f) (q : ℝ) :
    Measurable (fun ω => f ω ^ 2 / (1 + q * f ω ^ 2) ^ 2) :=
  (hf.pow_const 2).div ((measurable_const.add (measurable_const.mul (hf.pow_const 2))).pow_const 2)

private theorem p1c_meas_n {f : Ω → ℝ} (hf : Measurable f) (q : ℝ) :
    Measurable (fun ω => f ω ^ 4 / (1 + q * f ω ^ 2) ^ 2) :=
  (hf.pow_const 4).div ((measurable_const.add (measurable_const.mul (hf.pow_const 2))).pow_const 2)

private theorem p1c_d_nonneg (f : Ω → ℝ) {q : ℝ} (hq : 0 ≤ q) (ω : Ω) :
    0 ≤ f ω ^ 2 / (1 + q * f ω ^ 2) ^ 2 := by
  positivity

private theorem p1c_n_nonneg (f : Ω → ℝ) {q : ℝ} (hq : 0 ≤ q) (ω : Ω) :
    0 ≤ f ω ^ 4 / (1 + q * f ω ^ 2) ^ 2 := by
  positivity

private theorem p1c_d_le (f : Ω → ℝ) {q : ℝ} (hq : 0 ≤ q) (ω : Ω) :
    f ω ^ 2 / (1 + q * f ω ^ 2) ^ 2 ≤ f ω ^ 2 := by
  have h1 : 0 ≤ q * f ω ^ 2 := mul_nonneg hq (sq_nonneg _)
  apply div_le_self (sq_nonneg _)
  nlinarith

private theorem p1c_n_le (f : Ω → ℝ) {q : ℝ} (hq : 0 < q) (ω : Ω) :
    f ω ^ 4 / (1 + q * f ω ^ 2) ^ 2 ≤ f ω ^ 2 / q := by
  have h1 : 0 ≤ q * f ω ^ 2 := mul_nonneg hq.le (sq_nonneg _)
  rw [div_le_div_iff₀ (by positivity) hq]
  have : f ω ^ 4 * q = f ω ^ 2 * (q * f ω ^ 2) := by ring
  rw [this]
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
  nlinarith

private theorem p1c_d_integrable {P : Measure Ω} {f : Ω → ℝ} (hf : Measurable f) {q : ℝ}
    (hq : 0 ≤ q) (hsq : Integrable (fun ω => f ω ^ 2) P) :
    Integrable (fun ω => f ω ^ 2 / (1 + q * f ω ^ 2) ^ 2) P :=
  Integrable.mono' hsq (p1c_meas_d hf q).aestronglyMeasurable (ae_of_all _ (fun ω => by
    rw [Real.norm_eq_abs, abs_of_nonneg (p1c_d_nonneg f hq ω)]
    exact p1c_d_le f hq ω))

private theorem p1c_n_integrable {P : Measure Ω} {f : Ω → ℝ} (hf : Measurable f) {q : ℝ}
    (hq : 0 < q) (hsq : Integrable (fun ω => f ω ^ 2) P) :
    Integrable (fun ω => f ω ^ 4 / (1 + q * f ω ^ 2) ^ 2) P :=
  Integrable.mono' (hsq.div_const q) (p1c_meas_n hf q).aestronglyMeasurable (ae_of_all _ (fun ω => by
    rw [Real.norm_eq_abs, abs_of_nonneg (p1c_n_nonneg f hq.le ω)]
    exact p1c_n_le f hq ω))

private theorem p1c_summable_d {ι : Type*} {P : Measure Ω} {ξ : ι → Ω → ℝ}
    (hmeas : ∀ α, Measurable (ξ α)) (hsq : ∀ α, Integrable (fun ω => ξ α ω ^ 2) P)
    (hsum : Summable (fun α => ∫ ω, ξ α ω ^ 2 ∂P)) {q : ℝ} (hq : 0 ≤ q) :
    Summable (fun α => ∫ ω, ξ α ω ^ 2 / (1 + q * ξ α ω ^ 2) ^ 2 ∂P) :=
  Summable.of_nonneg_of_le (fun α => integral_nonneg (p1c_d_nonneg (ξ α) hq))
    (fun α => integral_mono (p1c_d_integrable (hmeas α) hq (hsq α)) (hsq α)
      (fun ω => p1c_d_le (ξ α) hq ω)) hsum

private theorem p1c_summable_n {ι : Type*} {P : Measure Ω} {ξ : ι → Ω → ℝ}
    (hmeas : ∀ α, Measurable (ξ α)) (hsq : ∀ α, Integrable (fun ω => ξ α ω ^ 2) P)
    (hsum : Summable (fun α => ∫ ω, ξ α ω ^ 2 ∂P)) {q : ℝ} (hq : 0 < q) :
    Summable (fun α => ∫ ω, ξ α ω ^ 4 / (1 + q * ξ α ω ^ 2) ^ 2 ∂P) := by
  refine Summable.of_nonneg_of_le (fun α => integral_nonneg (p1c_n_nonneg (ξ α) hq.le))
    (fun α => ?_) (hsum.div_const q)
  calc ∫ ω, ξ α ω ^ 4 / (1 + q * ξ α ω ^ 2) ^ 2 ∂P ≤ ∫ ω, ξ α ω ^ 2 / q ∂P :=
        integral_mono (p1c_n_integrable (hmeas α) hq (hsq α)) ((hsq α).div_const q)
          (fun ω => p1c_n_le (ξ α) hq ω)
    _ = (∫ ω, ξ α ω ^ 2 ∂P) / q := integral_div _ _

private theorem p1c_ident {ι : Type*} {P : Measure Ω} {ξ : ι → Ω → ℝ}
    (hmeas : ∀ α, Measurable (ξ α)) (hsq : ∀ α, Integrable (fun ω => ξ α ω ^ 2) P)
    (hsum : Summable (fun α => ∫ ω, ξ α ω ^ 2 ∂P)) {q : ℝ} (hq : 0 < q) :
    (∑' α, ∫ ω, ξ α ω ^ 2 / (1 + q * ξ α ω ^ 2) ^ 2 ∂P) +
      q * (∑' α, ∫ ω, ξ α ω ^ 4 / (1 + q * ξ α ω ^ 2) ^ 2 ∂P) =
      ∑' α, ∫ ω, ξ α ω ^ 2 / (1 + q * ξ α ω ^ 2) ∂P := by
  rw [← tsum_mul_left, ← Summable.tsum_add (p1c_summable_d hmeas hsq hsum hq.le)
    ((p1c_summable_n hmeas hsq hsum hq).mul_left q)]
  refine tsum_congr (fun α => ?_)
  rw [← integral_const_mul, ← integral_add (p1c_d_integrable (hmeas α) hq.le (hsq α))
    ((p1c_n_integrable (hmeas α) hq (hsq α)).const_mul q)]
  refine integral_congr_ae (ae_of_all _ (fun ω => ?_))
  have h1 : 0 < 1 + q * ξ α ω ^ 2 := by
    have : 0 ≤ q * ξ α ω ^ 2 := mul_nonneg hq.le (sq_nonneg _)
    linarith
  simp only
  field_simp

private theorem p1c_rderiv_pos {ι : Type*} {P : Measure Ω} {ξ : ι → Ω → ℝ}
    (hmeas : ∀ α, Measurable (ξ α)) (hsq : ∀ α, Integrable (fun ω => ξ α ω ^ 2) P)
    (hsum : Summable (fun α => ∫ ω, ξ α ω ^ 2 ∂P)) {α₀ : ι}
    (hα₀ : 0 < P {ω | ξ α₀ ω ≠ 0}) {q : ℝ} (hq : 0 ≤ q) :
    0 < ∑' α, ∫ ω, ξ α ω ^ 2 / (1 + q * ξ α ω ^ 2) ^ 2 ∂P := by
  refine (p1c_summable_d hmeas hsq hsum hq).tsum_pos
    (fun α => integral_nonneg (p1c_d_nonneg (ξ α) hq)) α₀ ?_
  rw [integral_pos_iff_support_of_nonneg (p1c_d_nonneg (ξ α₀) hq)
    (p1c_d_integrable (hmeas α₀) hq (hsq α₀))]
  refine lt_of_lt_of_le hα₀ (measure_mono ?_)
  intro ω hω
  simp only [mem_setOf_eq] at hω
  simp only [Function.mem_support, ne_eq]
  have h1 : 0 < ξ α₀ ω ^ 2 := by positivity
  have h2 : 0 < 1 + q * ξ α₀ ω ^ 2 := by
    have : 0 ≤ q * ξ α₀ ω ^ 2 := mul_nonneg hq (sq_nonneg _)
    linarith
  exact (div_pos h1 (pow_pos h2 2)).ne'

private theorem p1c_R_hasDerivWithinAt_zero {ι : Type*} {P : Measure Ω} [IsProbabilityMeasure P]
    {ξ : ι → Ω → ℝ} (hξ : def_app_vol_closed_profile P ξ) :
    HasDerivWithinAt (profileR P ξ) (profileRDeriv P ξ 0) (Ici 0) 0 := by
  have hcont : ContinuousWithinAt (profileF P ξ) (Ici 0) 0 :=
    (p1a_tsum_continuousOn hξ.measurable hξ.integrable_sq hξ.summable_sq) 0 (mem_Ici.2 le_rfl)
  have h0 : profileRDeriv P ξ 0 = profileF P ξ 0 := by simp [profileRDeriv, profileF]
  rw [h0, hasDerivWithinAt_iff_isLittleO]
  have hlo : (fun x' => profileF P ξ x' - profileF P ξ 0) =o[𝓝[Ici 0] 0] (fun _ => (1 : ℝ)) := by
    rw [Asymptotics.isLittleO_one_iff]
    have := hcont.tendsto.sub_const (profileF P ξ 0)
    simpa using this
  have := (Asymptotics.isBigO_refl (fun x' : ℝ => x' - 0) (𝓝[Ici 0] 0)).mul_isLittleO hlo
  refine this.congr' ?_ ?_
  · refine Filter.Eventually.of_forall (fun x => ?_)
    simp only [profileR, zero_mul, smul_eq_mul]
    ring
  · exact Filter.Eventually.of_forall (fun x => by simp)

/-- `lem:app-vol-closed-profile`, snapshot `cr-2026-10-23`. Declaration of record for part (a) of `lem:app-vol-closed-profile`:
regularity of `F_ξ` and `r_ξ`, their derivative formulas, the positivity of `r'_ξ`, the formula for `-F'_ξ`
for `q > 0` and the identity `eqn:app-vol-closed-b0e0`. The source's `-F'_ξ(q) ∈ [0,∞]` is finite for
`q > 0` and is stated as `HasDerivAt`, which forces finiteness.

LaTeX (`sections/04-volatility/section.tex` l.1712–1738, verbatim):
```latex
\begin{lemma}[Profile functions]\label{lem:app-vol-closed-profile}
Let $\xi$ be a profile.
\begin{enumerate}[label=(\alph*)]
\item $F_\xi$ and $r_\xi$ are continuous on $[0,\infty)$ and real-analytic on
$(0,\infty)$. $F_\xi$ is nonincreasing with $0<F_\xi\le F_\xi(0)=\sum_\alpha\EE\xi_\alpha^2$, and
$r_\xi(0)=0$. For $q\ge0$,
\[
r_\xi'(q)=\sum_\alpha\EE\frac{\xi_\alpha^2}{(1+q\xi_\alpha^2)^2}>0,\qquad -F_\xi'(q)=\sum_\alpha\EE\frac{\xi_\alpha^4}{(1+q\xi_\alpha^2)^2}\in[0,\infty],
\]
the latter finite for $q>0$, and
\begin{equation}\label{eqn:app-vol-closed-b0e0}
r_\xi'(q)+q\,\big(-F_\xi'(q)\big)=F_\xi(q)\qquad(q>0).
\end{equation}
\item $r_\xi$ increases strictly to $n_\xi\defeq\sum_\alpha\Pr(\xi_\alpha\ne0)\in(0,\infty]$.
\item For a paired profile, $b$ and $e$ are continuous on $[0,\infty)^2$, real-analytic
in each variable on $(0,\infty)$ when the other is fixed, and
\[
0\le b(q_1,q_2)\le\min\Big(\sqrt{r_{\xi_1}'(q_1)\,r_{\xi_2}'(q_2)},\ \sum_\alpha\EE[\xi_{1,\alpha}\xi_{2,\alpha}]\Big),
\]
\[
0\le e(q_1,q_2)\le\sqrt{\big(-F_{\xi_1}'(q_1)\big)\big(-F_{\xi_2}'(q_2)\big)} .
\]
\item For the EMA paired profile at lag $\ell$, the divided-difference forms
\cref{eqn:app-vol-closed-divided} hold, and $0\le b_\ell\le\sw2\,\bmom^\ell$. At $\ell=0$
and $q=q'$ they read $b_0=r_{\bmom}'(q)$ and $e_0=-\Fw'(q)$.
\end{enumerate}
\end{lemma}
```
-/
theorem lem_app_vol_closed_profile_i {P : Measure Ω} [IsProbabilityMeasure P]
    {ξ : ι → Ω → ℝ} (hξ : def_app_vol_closed_profile P ξ) :
    ContinuousOn (profileF P ξ) (Ici 0) ∧ ContinuousOn (profileR P ξ) (Ici 0) ∧
    AnalyticOnNhd ℝ (profileF P ξ) (Ioi 0) ∧ AnalyticOnNhd ℝ (profileR P ξ) (Ioi 0) ∧
    AntitoneOn (profileF P ξ) (Ici 0) ∧
    profileF P ξ 0 = ∑' α, ∫ ω, ξ α ω ^ 2 ∂P ∧ profileR P ξ 0 = 0 ∧
    (∀ q ∈ Ici (0 : ℝ), 0 < profileF P ξ q) ∧
    (∀ q ∈ Ici (0 : ℝ), HasDerivWithinAt (profileR P ξ) (profileRDeriv P ξ q) (Ici 0) q) ∧
    (∀ q ∈ Ici (0 : ℝ), 0 < profileRDeriv P ξ q) ∧
    (∀ q, 0 < q → HasDerivAt (profileF P ξ) (-profileNegFDeriv P ξ q) q ∧
      0 ≤ profileNegFDeriv P ξ q) ∧
    (∀ q, 0 < q → profileRDeriv P ξ q + q * profileNegFDeriv P ξ q = profileF P ξ q) := by
  obtain ⟨hmeas, hsq, hsum, α₀, hα₀⟩ := hξ
  have hξ' : def_app_vol_closed_profile P ξ := ⟨hmeas, hsq, hsum, α₀, hα₀⟩
  have hFcont : ContinuousOn (profileF P ξ) (Ici 0) := p1a_tsum_continuousOn hmeas hsq hsum
  have hFan : AnalyticOnNhd ℝ (profileF P ξ) (Ioi 0) := p1b_F_analyticOn hmeas hsq hsum
  refine ⟨hFcont, continuousOn_id.mul hFcont, hFan, analyticOnNhd_id.mul hFan,
    p1a_profileF_antitoneOn hmeas hsq hsum, by simp [profileF], by simp [profileR],
    fun q hq => p1a_profileF_pos hmeas hsq hsum hα₀ hq, ?_, ?_, ?_, ?_⟩
  · intro q hq
    rcases (mem_Ici.1 hq).eq_or_lt with h | h
    · subst h
      exact p1c_R_hasDerivWithinAt_zero hξ'
    · have hF' := p1b_F_hasDerivAt hmeas hsq hsum h
      have := ((hasDerivAt_id q).mul hF').hasDerivWithinAt (s := Ici 0)
      have hid := p1c_ident hmeas hsq hsum h
      exact this.congr_deriv (by simp only [profileRDeriv, id]; linarith)
  · intro q hq
    exact p1c_rderiv_pos hmeas hsq hsum hα₀ hq
  · intro q hq
    exact ⟨p1b_F_hasDerivAt hmeas hsq hsum hq,
      tsum_nonneg (fun α => integral_nonneg (p1c_n_nonneg (ξ α) hq.le))⟩
  · intro q hq
    exact p1c_ident hmeas hsq hsum hq

private theorem p1d_pt_le {f : Ω → ℝ} {q : ℝ} (hq : 0 ≤ q) (ω : Ω) :
    q * (f ω ^ 2 / (1 + q * f ω ^ 2)) ≤ ({ω | f ω ≠ 0} : Set Ω).indicator 1 ω := by
  have h1 : 0 ≤ q * f ω ^ 2 := mul_nonneg hq (sq_nonneg _)
  by_cases h : f ω = 0
  · have : ω ∉ ({ω | f ω ≠ 0} : Set Ω) := by simp [h]
    simp [Set.indicator_of_notMem this, h]
  · have : ω ∈ ({ω | f ω ≠ 0} : Set Ω) := h
    rw [Set.indicator_of_mem this]
    have hp : 0 < 1 + q * f ω ^ 2 := by linarith
    rw [Pi.one_apply, ← mul_div_assoc, div_le_one hp]
    nlinarith [sq_nonneg (f ω)]

private theorem p1d_pt_nonneg {f : Ω → ℝ} {q : ℝ} (hq : 0 ≤ q) (ω : Ω) :
    0 ≤ q * (f ω ^ 2 / (1 + q * f ω ^ 2)) :=
  mul_nonneg hq (p1a_term_nonneg hq ω)

private theorem p1d_pt_tendsto {f : Ω → ℝ} (ω : Ω) :
    Tendsto (fun q : ℝ => q * (f ω ^ 2 / (1 + q * f ω ^ 2))) atTop
      (𝓝 (({ω | f ω ≠ 0} : Set Ω).indicator 1 ω)) := by
  by_cases h : f ω = 0
  · have : ω ∉ ({ω | f ω ≠ 0} : Set Ω) := by simp [h]
    simp [Set.indicator_of_notMem this, h]
  · have : ω ∈ ({ω | f ω ≠ 0} : Set Ω) := h
    rw [Set.indicator_of_mem this]
    have ha : 0 < f ω ^ 2 := by positivity
    have h1 : Tendsto (fun q : ℝ => 1 + q * f ω ^ 2) atTop atTop :=
      tendsto_atTop_add_const_left _ _ (tendsto_id.atTop_mul_const ha)
    have h2 : Tendsto (fun q : ℝ => 1 - 1 / (1 + q * f ω ^ 2)) atTop (𝓝 (1 - 0)) :=
      tendsto_const_nhds.sub (tendsto_const_nhds.div_atTop h1)
    rw [sub_zero] at h2
    refine h2.congr' ?_
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with q hq
    have hp : 0 < 1 + q * f ω ^ 2 := by nlinarith [mul_nonneg hq ha.le]
    field_simp
    ring

private theorem p1d_term_tendsto {P : Measure Ω} [IsProbabilityMeasure P] {f : Ω → ℝ}
    (hf : Measurable f) :
    Tendsto (fun q : ℝ => ENNReal.ofReal (q * ∫ ω, f ω ^ 2 / (1 + q * f ω ^ 2) ∂P)) atTop
      (𝓝 (P {ω | f ω ≠ 0})) := by
  have hS : MeasurableSet {ω | f ω ≠ 0} := hf (measurableSet_singleton (0 : ℝ)).compl
  have hmeasq : ∀ q : ℝ, Measurable (fun ω => q * (f ω ^ 2 / (1 + q * f ω ^ 2))) := fun q =>
    measurable_const.mul ((hf.pow_const 2).div (measurable_const.add
      (measurable_const.mul (hf.pow_const 2))))
  have hdc : Tendsto (fun q : ℝ => ∫ ω, q * (f ω ^ 2 / (1 + q * f ω ^ 2)) ∂P) atTop
      (𝓝 (∫ ω, ({ω | f ω ≠ 0} : Set Ω).indicator 1 ω ∂P)) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun _ => (1 : ℝ)) ?_ ?_
      (integrable_const _) (ae_of_all _ (fun ω => p1d_pt_tendsto ω))
    · exact Filter.Eventually.of_forall (fun q => (hmeasq q).aestronglyMeasurable)
    · filter_upwards [eventually_ge_atTop (0 : ℝ)] with q hq
      refine ae_of_all _ (fun ω => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (p1d_pt_nonneg hq ω)]
      refine (p1d_pt_le hq ω).trans ?_
      exact Set.indicator_le_self' (fun _ _ => zero_le_one) ω |>.trans le_rfl
  rw [integral_indicator_one hS] at hdc
  have h3 := (ENNReal.tendsto_ofReal hdc)
  rw [Measure.real, ENNReal.ofReal_toReal (measure_ne_top _ _)] at h3
  refine h3.congr (fun q => ?_)
  rw [integral_const_mul]

private theorem p1d_term_le {P : Measure Ω} [IsProbabilityMeasure P] {f : Ω → ℝ}
    (hf : Measurable f) {q : ℝ} (hq : 0 ≤ q) :
    ENNReal.ofReal (q * ∫ ω, f ω ^ 2 / (1 + q * f ω ^ 2) ∂P) ≤ P {ω | f ω ≠ 0} := by
  have hS : MeasurableSet {ω | f ω ≠ 0} := hf (measurableSet_singleton (0 : ℝ)).compl
  have hmq : Measurable (fun ω => q * (f ω ^ 2 / (1 + q * f ω ^ 2))) :=
    measurable_const.mul ((hf.pow_const 2).div (measurable_const.add
      (measurable_const.mul (hf.pow_const 2))))
  have hint : Integrable (fun ω => q * (f ω ^ 2 / (1 + q * f ω ^ 2))) P := by
    refine Integrable.mono' (integrable_const (1 : ℝ)) hmq.aestronglyMeasurable
      (ae_of_all _ (fun ω => ?_))
    rw [Real.norm_eq_abs, abs_of_nonneg (p1d_pt_nonneg hq ω)]
    exact (p1d_pt_le hq ω).trans (Set.indicator_le_self' (fun _ _ => zero_le_one) ω)
  have h1 : ∫ ω, q * (f ω ^ 2 / (1 + q * f ω ^ 2)) ∂P ≤ ∫ ω, ({ω | f ω ≠ 0} : Set Ω).indicator 1 ω ∂P :=
    integral_mono hint ((integrable_const (1 : ℝ)).indicator hS) (fun ω => p1d_pt_le hq ω)
  rw [integral_indicator_one hS, integral_const_mul] at h1
  calc ENNReal.ofReal (q * ∫ ω, f ω ^ 2 / (1 + q * f ω ^ 2) ∂P) ≤ ENNReal.ofReal (P.real {ω | f ω ≠ 0}) :=
        ENNReal.ofReal_le_ofReal h1
    _ = P {ω | f ω ≠ 0} := by rw [Measure.real, ENNReal.ofReal_toReal (measure_ne_top _ _)]

private theorem p1d_tendsto_tsum {ι : Type*} (g : ι → ℝ → ℝ≥0∞) (c : ι → ℝ≥0∞)
    (hlim : ∀ α, Tendsto (g α) atTop (𝓝 (c α)))
    (hle : ∀ α, ∀ q : ℝ, 0 ≤ q → g α q ≤ c α) :
    Tendsto (fun q => ∑' α, g α q) atTop (𝓝 (∑' α, c α)) := by
  rw [tendsto_order]
  constructor
  · intro a ha
    rw [ENNReal.tsum_eq_iSup_sum, lt_iSup_iff] at ha
    obtain ⟨S, hS⟩ := ha
    have h1 : Tendsto (fun q => ∑ α ∈ S, g α q) atTop (𝓝 (∑ α ∈ S, c α)) :=
      tendsto_finset_sum _ (fun α _ => hlim α)
    filter_upwards [(tendsto_order.1 h1).1 a hS] with q hq
    exact lt_of_lt_of_le hq (ENNReal.sum_le_tsum S)
  · intro a ha
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with q hq
    exact lt_of_le_of_lt (ENNReal.tsum_le_tsum (fun α => hle α q hq)) ha

/-- `lem:app-vol-closed-profile`, snapshot `cr-2026-10-23`. Declaration of record for part (b) of `lem:app-vol-closed-profile`:
`r_ξ` increases strictly to `n_ξ = ∑_α P(ξ_α ≠ 0) ∈ (0, ∞]`. The limit is stated in `ℝ≥0∞` through
`ENNReal.ofReal`, since `n_ξ` may be infinite.

LaTeX (`sections/04-volatility/section.tex` l.1712–1738, verbatim):
```latex
\begin{lemma}[Profile functions]\label{lem:app-vol-closed-profile}
Let $\xi$ be a profile.
\begin{enumerate}[label=(\alph*)]
\item $F_\xi$ and $r_\xi$ are continuous on $[0,\infty)$ and real-analytic on
$(0,\infty)$. $F_\xi$ is nonincreasing with $0<F_\xi\le F_\xi(0)=\sum_\alpha\EE\xi_\alpha^2$, and
$r_\xi(0)=0$. For $q\ge0$,
\[
r_\xi'(q)=\sum_\alpha\EE\frac{\xi_\alpha^2}{(1+q\xi_\alpha^2)^2}>0,\qquad -F_\xi'(q)=\sum_\alpha\EE\frac{\xi_\alpha^4}{(1+q\xi_\alpha^2)^2}\in[0,\infty],
\]
the latter finite for $q>0$, and
\begin{equation}\label{eqn:app-vol-closed-b0e0}
r_\xi'(q)+q\,\big(-F_\xi'(q)\big)=F_\xi(q)\qquad(q>0).
\end{equation}
\item $r_\xi$ increases strictly to $n_\xi\defeq\sum_\alpha\Pr(\xi_\alpha\ne0)\in(0,\infty]$.
\item For a paired profile, $b$ and $e$ are continuous on $[0,\infty)^2$, real-analytic
in each variable on $(0,\infty)$ when the other is fixed, and
\[
0\le b(q_1,q_2)\le\min\Big(\sqrt{r_{\xi_1}'(q_1)\,r_{\xi_2}'(q_2)},\ \sum_\alpha\EE[\xi_{1,\alpha}\xi_{2,\alpha}]\Big),
\]
\[
0\le e(q_1,q_2)\le\sqrt{\big(-F_{\xi_1}'(q_1)\big)\big(-F_{\xi_2}'(q_2)\big)} .
\]
\item For the EMA paired profile at lag $\ell$, the divided-difference forms
\cref{eqn:app-vol-closed-divided} hold, and $0\le b_\ell\le\sw2\,\bmom^\ell$. At $\ell=0$
and $q=q'$ they read $b_0=r_{\bmom}'(q)$ and $e_0=-\Fw'(q)$.
\end{enumerate}
\end{lemma}
```
-/
theorem lem_app_vol_closed_profile_ii {P : Measure Ω} [IsProbabilityMeasure P]
    {ξ : ι → Ω → ℝ} (hξ : def_app_vol_closed_profile P ξ) :
    StrictMonoOn (profileR P ξ) (Ici 0) ∧
    Tendsto (fun q => ENNReal.ofReal (profileR P ξ q)) atTop
      (𝓝 (∑' α, P {ω | ξ α ω ≠ 0})) ∧
    0 < ∑' α, P {ω | ξ α ω ≠ 0} := by
  have hi := lem_app_vol_closed_profile_i hξ
  obtain ⟨hmeas, hsq, hsum, α₀, hα₀⟩ := hξ
  refine ⟨?_, ?_, ?_⟩
  · refine strictMonoOn_of_deriv_pos (convex_Ici 0) hi.2.1 (fun x hx => ?_)
    rw [interior_Ici] at hx
    have hx' : (0 : ℝ) < x := hx
    have hd := (hi.2.2.2.2.2.2.2.2.1 x hx'.le).hasDerivAt (Ici_mem_nhds hx')
    rw [hd.deriv]
    exact hi.2.2.2.2.2.2.2.2.2.1 x hx'.le
  · have hsumq : ∀ q : ℝ, 0 ≤ q → ENNReal.ofReal (profileR P ξ q) =
        ∑' α, ENNReal.ofReal (q * ∫ ω, ξ α ω ^ 2 / (1 + q * ξ α ω ^ 2) ∂P) := by
      intro q hq
      unfold profileR profileF
      rw [← tsum_mul_left]
      exact ENNReal.ofReal_tsum_of_nonneg
        (fun α => mul_nonneg hq (integral_nonneg (p1a_term_nonneg hq)))
        ((p1a_summable_term hsq hsum hq).mul_left q)
    have := p1d_tendsto_tsum
      (fun α q => ENNReal.ofReal (q * ∫ ω, ξ α ω ^ 2 / (1 + q * ξ α ω ^ 2) ∂P))
      (fun α => P {ω | ξ α ω ≠ 0}) (fun α => p1d_term_tendsto (hmeas α))
      (fun α q hq => p1d_term_le (hmeas α) hq)
    refine this.congr' ?_
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with q hq
    exact (hsumq q hq).symm
  · exact lt_of_lt_of_le hα₀ (ENNReal.le_tsum (f := fun α => P {ω | ξ α ω ≠ 0}) α₀)

private theorem p2g_term_bound {a : ℝ} (ha : 0 ≤ a) (c : ℝ) {z : ℂ} (hz : 0 ≤ z.re) :
    ‖(c : ℂ) / (1 + z * (a : ℂ))‖ ≤ |c| := by
  have h := p1b_norm_den ha hz
  have h1 : 1 ≤ ‖1 + z * (a : ℂ)‖ := by nlinarith [mul_nonneg hz ha]
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs]
  exact div_le_self (abs_nonneg c) h1

private theorem p2g_deriv_bound {a : ℝ} (ha : 0 ≤ a) (c : ℝ) {δ : ℝ} (hδ : 0 < δ) {z : ℂ}
    (hz : δ ≤ z.re) :
    ‖(c : ℂ) * (a : ℂ) / (1 + z * (a : ℂ)) ^ 2‖ ≤ |c| / δ := by
  have h := p1b_norm_den ha (hδ.le.trans hz)
  have h1 : 1 + δ * a ≤ ‖1 + z * (a : ℂ)‖ := by nlinarith [mul_le_mul_of_nonneg_right hz ha]
  have h0 : 0 < 1 + δ * a := by nlinarith [mul_nonneg hδ.le ha]
  rw [norm_div, norm_mul, norm_pow, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
    Real.norm_eq_abs, abs_of_nonneg ha]
  have h2 : (1 + δ * a) ^ 2 ≤ ‖1 + z * (a : ℂ)‖ ^ 2 := by gcongr
  have h3 : a * δ ≤ ‖1 + z * (a : ℂ)‖ ^ 2 := by
    nlinarith [mul_nonneg ha hδ.le, sq_nonneg (δ * a)]
  rw [div_le_div_iff₀ (by nlinarith) hδ]
  calc |c| * a * δ = |c| * (a * δ) := by ring
    _ ≤ |c| * ‖1 + z * (a : ℂ)‖ ^ 2 := mul_le_mul_of_nonneg_left h3 (abs_nonneg c)

private theorem p2g_term_hasDerivAt {P : Measure Ω} {c a : Ω → ℝ} (hc : Measurable c)
    (ha : Measurable a) (ha0 : ∀ ω, 0 ≤ a ω) (hci : Integrable c P) {z₀ : ℂ} (hz₀ : 0 < z₀.re) :
    HasDerivAt (fun z : ℂ => ∫ ω, (c ω : ℂ) / (1 + z * (a ω : ℂ)) ∂P)
      (-∫ ω, (c ω : ℂ) * (a ω : ℂ) / (1 + z₀ * (a ω : ℂ)) ^ 2 ∂P) z₀ := by
  have hcm : Measurable (fun ω => (c ω : ℂ)) := Complex.measurable_ofReal.comp hc
  have ham : Measurable (fun ω => (a ω : ℂ)) := Complex.measurable_ofReal.comp ha
  have hcpos : 0 < z₀.re / 2 := by linarith
  have hre : ∀ z ∈ Metric.ball z₀ (z₀.re / 2), z₀.re / 2 ≤ z.re := by
    intro z hz
    have h1 := Complex.abs_re_le_norm (z - z₀)
    have h2 : ‖z - z₀‖ < z₀.re / 2 := by simpa [dist_eq_norm] using hz
    have h3 : (z - z₀).re = z.re - z₀.re := by simp
    rw [h3] at h1
    have := neg_abs_le (z.re - z₀.re)
    linarith
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := P) (𝕜 := ℂ)
    (F := fun z ω => (c ω : ℂ) / (1 + z * (a ω : ℂ)))
    (F' := fun z ω => -((c ω : ℂ) * (a ω : ℂ) / (1 + z * (a ω : ℂ)) ^ 2))
    (x₀ := z₀) (bound := fun ω => |c ω| / (z₀.re / 2)) (s := Metric.ball z₀ (z₀.re / 2))
    (Metric.ball_mem_nhds _ hcpos) ?_ ?_ ?_ ?_ ?_ ?_
  · have := key.2
    simpa [integral_neg] using this
  · exact Filter.Eventually.of_forall (fun z =>
      (hcm.div (measurable_const.add (measurable_const.mul ham))).aestronglyMeasurable)
  · refine Integrable.mono' hci.abs
      (hcm.div (measurable_const.add (measurable_const.mul ham))).aestronglyMeasurable
      (ae_of_all _ (fun ω => ?_))
    simpa using p2g_term_bound (ha0 ω) (c ω) hz₀.le
  · exact ((hcm.mul ham).div ((measurable_const.add (measurable_const.mul ham)).pow_const 2)).neg.aestronglyMeasurable
  · refine ae_of_all _ (fun ω z hz => ?_)
    rw [norm_neg]
    exact p2g_deriv_bound (ha0 ω) (c ω) hcpos (hre z hz)
  · exact hci.abs.div_const _
  · refine ae_of_all _ (fun ω z hz => ?_)
    have hr := hre z hz
    have hne : (1 + z * (a ω : ℂ)) ≠ 0 := by
      have := p1b_norm_den (ha0 ω) (hcpos.le.trans hr)
      intro h0
      rw [h0, norm_zero] at this
      nlinarith [mul_nonneg (hcpos.le.trans hr) (ha0 ω)]
    have hd : HasDerivAt (fun x : ℂ => 1 + x * (a ω : ℂ)) (a ω : ℂ) z := by
      exact (((hasDerivAt_id z).mul_const (a ω : ℂ)).const_add 1).congr_deriv (one_mul _)
    have := (hasDerivAt_const z (c ω : ℂ)).div hd hne
    convert this using 1
    ring

private theorem p2g_FC_hasDerivAt {ι : Type*} {P : Measure Ω} {c a : ι → Ω → ℝ}
    (hc : ∀ α, Measurable (c α)) (ha : ∀ α, Measurable (a α)) (ha0 : ∀ α ω, 0 ≤ a α ω)
    (hci : ∀ α, Integrable (c α) P) (hsum : Summable (fun α => ∫ ω, |c α ω| ∂P))
    {z₀ : ℂ} (hz₀ : 0 < z₀.re) :
    HasDerivAt (fun z : ℂ => ∑' α, ∫ ω, (c α ω : ℂ) / (1 + z * (a α ω : ℂ)) ∂P)
      (∑' α, -∫ ω, (c α ω : ℂ) * (a α ω : ℂ) / (1 + z₀ * (a α ω : ℂ)) ^ 2 ∂P) z₀ := by
  have hc2 : 0 < z₀.re / 2 := by linarith
  have hre : ∀ z : ℂ, z₀.re / 2 < z.re → 0 < z.re := fun z hz => by linarith
  refine hasDerivAt_tsum_of_isPreconnected (t := {z : ℂ | z₀.re / 2 < z.re})
    (u := fun α => (∫ ω, |c α ω| ∂P) / (z₀.re / 2))
    (g := fun α z => ∫ ω, (c α ω : ℂ) / (1 + z * (a α ω : ℂ)) ∂P)
    (g' := fun α z => -∫ ω, (c α ω : ℂ) * (a α ω : ℂ) / (1 + z * (a α ω : ℂ)) ^ 2 ∂P)
    (y₀ := z₀) (hsum.div_const _) (isOpen_lt continuous_const Complex.continuous_re)
    (convex_halfSpace_re_gt _).isPreconnected ?_ ?_ (by simp [hz₀, hc2]) ?_ (by simpa using hc2)
  · intro α z hz
    exact p2g_term_hasDerivAt (hc α) (ha α) (ha0 α) (hci α) (hre z hz)
  · intro α z hz
    rw [norm_neg]
    refine (norm_integral_le_of_norm_le ((hci α).abs.div_const (z₀.re / 2))
      (ae_of_all _ (fun ω => ?_))).trans ?_
    · exact p2g_deriv_bound (ha0 α ω) (c α ω) hc2 (le_of_lt hz)
    · rw [integral_div]
  · refine Summable.of_norm_bounded hsum (fun α => ?_)
    refine norm_integral_le_of_norm_le (hci α).abs (ae_of_all _ (fun ω => ?_))
    exact p2g_term_bound (ha0 α ω) (c α ω) hz₀.le

private theorem p2g_FC_ofReal {ι : Type*} {P : Measure Ω} {c a : ι → Ω → ℝ} (x : ℝ) :
    (∑' α, ∫ ω, (c α ω : ℂ) / (1 + (x : ℂ) * (a α ω : ℂ)) ∂P) =
      ((∑' α, ∫ ω, c α ω / (1 + x * a α ω) ∂P : ℝ) : ℂ) := by
  rw [Complex.ofReal_tsum]
  refine tsum_congr (fun α => ?_)
  rw [← integral_complex_ofReal]
  refine integral_congr_ae (ae_of_all _ (fun ω => ?_))
  push_cast
  rfl

private theorem p2g_analyticOn {ι : Type*} {P : Measure Ω} {c a : ι → Ω → ℝ}
    (hc : ∀ α, Measurable (c α)) (ha : ∀ α, Measurable (a α)) (ha0 : ∀ α ω, 0 ≤ a α ω)
    (hci : ∀ α, Integrable (c α) P) (hsum : Summable (fun α => ∫ ω, |c α ω| ∂P)) :
    AnalyticOnNhd ℝ (fun x : ℝ => ∑' α, ∫ ω, c α ω / (1 + x * a α ω) ∂P) (Ioi 0) := by
  have hd : DifferentiableOn ℂ (fun z : ℂ => ∑' α, ∫ ω, (c α ω : ℂ) /
      (1 + z * (a α ω : ℂ)) ∂P) {z : ℂ | 0 < z.re} :=
    fun z hz => (p2g_FC_hasDerivAt hc ha ha0 hci hsum hz).differentiableAt.differentiableWithinAt
  have han := hd.analyticOnNhd (isOpen_lt continuous_const Complex.continuous_re)
  intro x hx
  have h1 : AnalyticAt ℂ (fun z : ℂ => ∑' α, ∫ ω, (c α ω : ℂ) /
      (1 + z * (a α ω : ℂ)) ∂P) (x : ℂ) := han _ (by simpa using hx)
  have h2 := h1.restrictScalars (𝕜 := ℝ)
  have h3 := (Complex.reCLM.analyticAt _).comp (h2.comp (Complex.ofRealCLM.analyticAt x))
  have hfun : (fun x : ℝ => ((∑' α, ∫ ω, (c α ω : ℂ) /
      (1 + (x : ℂ) * (a α ω : ℂ)) ∂P)).re) =
      (fun x : ℝ => ∑' α, ∫ ω, c α ω / (1 + x * a α ω) ∂P) := by
    funext x
    rw [p2g_FC_ofReal (P := P) (c := c) (a := a) x, Complex.ofReal_re]
  rw [← hfun]
  exact h3

section PairedHelpers
variable {P : Measure Ω} [IsProbabilityMeasure P] {ξ₁ ξ₂ : ι → Ω → ℝ}

private theorem p2_den_pos {q x : ℝ} (hq : 0 ≤ q) : 0 < 1 + q * x ^ 2 := by
  have := mul_nonneg hq (sq_nonneg x)
  linarith

private theorem p2_prod_int (hξ : def_app_vol_closed_profile_ii P ξ₁ ξ₂) (α : ι) :
    Integrable (fun ω => ξ₁ α ω * ξ₂ α ω) P := by
  have h1 := hξ.profile₁.integrable_sq α
  have h2 := hξ.profile₂.integrable_sq α
  refine Integrable.mono' ((h1.add h2).div_const 2)
    ((hξ.profile₁.measurable α).mul (hξ.profile₂.measurable α)).aestronglyMeasurable
    (ae_of_all _ (fun ω => ?_))
  rw [Real.norm_eq_abs, abs_of_nonneg (hξ.nonneg_prod α ω)]
  simp only [Pi.add_apply]
  nlinarith [sq_nonneg (ξ₁ α ω - ξ₂ α ω)]

private theorem p2_prod_sum (hξ : def_app_vol_closed_profile_ii P ξ₁ ξ₂) :
    Summable (fun α => ∫ ω, ξ₁ α ω * ξ₂ α ω ∂P) := by
  have hs := (hξ.profile₁.summable_sq.add hξ.profile₂.summable_sq).div_const 2
  refine Summable.of_nonneg_of_le (fun α => integral_nonneg (hξ.nonneg_prod α)) (fun α => ?_) hs
  have h1 := hξ.profile₁.integrable_sq α
  have h2 := hξ.profile₂.integrable_sq α
  calc ∫ ω, ξ₁ α ω * ξ₂ α ω ∂P ≤ ∫ ω, (ξ₁ α ω ^ 2 + ξ₂ α ω ^ 2) / 2 ∂P :=
        integral_mono (p2_prod_int hξ α) ((h1.add h2).div_const 2)
          (fun ω => by nlinarith [sq_nonneg (ξ₁ α ω - ξ₂ α ω)])
    _ = (∫ ω, ξ₁ α ω ^ 2 ∂P + ∫ ω, ξ₂ α ω ^ 2 ∂P) / 2 := by
        rw [integral_div, integral_add h1 h2]

private theorem p2_swap (hξ : def_app_vol_closed_profile_ii P ξ₁ ξ₂) :
    def_app_vol_closed_profile_ii P ξ₂ ξ₁ where
  profile₁ := hξ.profile₂
  profile₂ := hξ.profile₁
  nonneg_prod := fun α ω => by rw [mul_comm]; exact hξ.nonneg_prod α ω
  integrable_sq_prod := fun α => by
    simpa [mul_comm] using hξ.integrable_sq_prod α
  summable_sq_prod := by
    simpa [mul_comm] using hξ.summable_sq_prod

private theorem p2_B_swap (q₁ q₂ : ℝ) :
    pairedB P ξ₂ ξ₁ q₂ q₁ = pairedB P ξ₁ ξ₂ q₁ q₂ := by
  unfold pairedB
  refine tsum_congr (fun α => integral_congr_ae (ae_of_all _ (fun ω => ?_)))
  simp only
  rw [mul_comm (ξ₂ α ω), mul_comm (1 + q₂ * ξ₂ α ω ^ 2)]

private theorem p2_E_swap (q₁ q₂ : ℝ) :
    pairedE P ξ₂ ξ₁ q₂ q₁ = pairedE P ξ₁ ξ₂ q₁ q₂ := by
  unfold pairedE
  refine tsum_congr (fun α => integral_congr_ae (ae_of_all _ (fun ω => ?_)))
  simp only
  rw [mul_comm (ξ₂ α ω ^ 2), mul_comm (1 + q₂ * ξ₂ α ω ^ 2)]

private theorem p2_B_analytic (hξ : def_app_vol_closed_profile_ii P ξ₁ ξ₂) {q₂ : ℝ} (hq₂ : 0 ≤ q₂) :
    AnalyticOnNhd ℝ (fun q₁ => pairedB P ξ₁ ξ₂ q₁ q₂) (Ioi 0) := by
  have hm1 := hξ.profile₁.measurable
  have hm2 := hξ.profile₂.measurable
  have hcm : ∀ α, Measurable (fun ω => ξ₁ α ω * ξ₂ α ω / (1 + q₂ * ξ₂ α ω ^ 2)) := fun α =>
    ((hm1 α).mul (hm2 α)).div (measurable_const.add (measurable_const.mul ((hm2 α).pow_const 2)))
  have hbd : ∀ α ω, |ξ₁ α ω * ξ₂ α ω / (1 + q₂ * ξ₂ α ω ^ 2)| ≤ ξ₁ α ω * ξ₂ α ω := by
    intro α ω
    have h0 := hξ.nonneg_prod α ω
    have hd := p2_den_pos (x := ξ₂ α ω) hq₂
    rw [abs_of_nonneg (div_nonneg h0 hd.le)]
    exact div_le_self h0 (by nlinarith [mul_nonneg hq₂ (sq_nonneg (ξ₂ α ω))])
  have hci : ∀ α, Integrable (fun ω => ξ₁ α ω * ξ₂ α ω / (1 + q₂ * ξ₂ α ω ^ 2)) P := fun α =>
    Integrable.mono' (p2_prod_int hξ α) (hcm α).aestronglyMeasurable
      (ae_of_all _ (fun ω => by rw [Real.norm_eq_abs]; exact hbd α ω))
  have hsum : Summable (fun α => ∫ ω, |ξ₁ α ω * ξ₂ α ω / (1 + q₂ * ξ₂ α ω ^ 2)| ∂P) :=
    Summable.of_nonneg_of_le (fun α => integral_nonneg (fun ω => abs_nonneg _))
      (fun α => integral_mono (hci α).abs (p2_prod_int hξ α) (fun ω => hbd α ω)) (p2_prod_sum hξ)
  have := p2g_analyticOn (P := P) (c := fun α ω => ξ₁ α ω * ξ₂ α ω / (1 + q₂ * ξ₂ α ω ^ 2))
    (a := fun α ω => ξ₁ α ω ^ 2) hcm (fun α => (hm1 α).pow_const 2) (fun α ω => sq_nonneg _) hci hsum
  convert this using 2 with q₁
  unfold pairedB
  refine tsum_congr (fun α => integral_congr_ae (ae_of_all _ (fun ω => ?_)))
  simp only
  rw [div_div, mul_comm (1 + q₂ * ξ₂ α ω ^ 2)]

private theorem p2_E_analytic (hξ : def_app_vol_closed_profile_ii P ξ₁ ξ₂) {q₂ : ℝ} (hq₂ : 0 ≤ q₂) :
    AnalyticOnNhd ℝ (fun q₁ => pairedE P ξ₁ ξ₂ q₁ q₂) (Ioi 0) := by
  have hm1 := hξ.profile₁.measurable
  have hm2 := hξ.profile₂.measurable
  have hcm : ∀ α, Measurable (fun ω => ξ₁ α ω ^ 2 * ξ₂ α ω ^ 2 / (1 + q₂ * ξ₂ α ω ^ 2)) := fun α =>
    (((hm1 α).pow_const 2).mul ((hm2 α).pow_const 2)).div
      (measurable_const.add (measurable_const.mul ((hm2 α).pow_const 2)))
  have hbd : ∀ α ω, |ξ₁ α ω ^ 2 * ξ₂ α ω ^ 2 / (1 + q₂ * ξ₂ α ω ^ 2)| ≤
      ξ₁ α ω ^ 2 * ξ₂ α ω ^ 2 := by
    intro α ω
    have h0 : 0 ≤ ξ₁ α ω ^ 2 * ξ₂ α ω ^ 2 := by positivity
    have hd := p2_den_pos (x := ξ₂ α ω) hq₂
    rw [abs_of_nonneg (div_nonneg h0 hd.le)]
    exact div_le_self h0 (by nlinarith [mul_nonneg hq₂ (sq_nonneg (ξ₂ α ω))])
  have hci : ∀ α, Integrable (fun ω => ξ₁ α ω ^ 2 * ξ₂ α ω ^ 2 / (1 + q₂ * ξ₂ α ω ^ 2)) P :=
    fun α => Integrable.mono' (hξ.integrable_sq_prod α) (hcm α).aestronglyMeasurable
      (ae_of_all _ (fun ω => by rw [Real.norm_eq_abs]; exact hbd α ω))
  have hsum : Summable (fun α => ∫ ω, |ξ₁ α ω ^ 2 * ξ₂ α ω ^ 2 / (1 + q₂ * ξ₂ α ω ^ 2)| ∂P) :=
    Summable.of_nonneg_of_le (fun α => integral_nonneg (fun ω => abs_nonneg _))
      (fun α => integral_mono (hci α).abs (hξ.integrable_sq_prod α) (fun ω => hbd α ω))
      hξ.summable_sq_prod
  have := p2g_analyticOn (P := P)
    (c := fun α ω => ξ₁ α ω ^ 2 * ξ₂ α ω ^ 2 / (1 + q₂ * ξ₂ α ω ^ 2))
    (a := fun α ω => ξ₁ α ω ^ 2) hcm (fun α => (hm1 α).pow_const 2) (fun α ω => sq_nonneg _) hci hsum
  convert this using 2 with q₁
  unfold pairedE
  refine tsum_congr (fun α => integral_congr_ae (ae_of_all _ (fun ω => ?_)))
  simp only
  rw [div_div, mul_comm (1 + q₂ * ξ₂ α ω ^ 2)]

private theorem p2_cont_gen {n : ι → Ω → ℝ} {a₁ a₂ : ι → Ω → ℝ}
    (hn : ∀ α, Measurable (n α)) (h1 : ∀ α, Measurable (a₁ α)) (h2 : ∀ α, Measurable (a₂ α))
    (hn0 : ∀ α ω, 0 ≤ n α ω) (hni : ∀ α, Integrable (n α) P)
    (hs : Summable (fun α => ∫ ω, n α ω ∂P)) :
    ContinuousOn (fun p : ℝ × ℝ => ∑' α, ∫ ω, n α ω /
      ((1 + p.1 * a₁ α ω ^ 2) * (1 + p.2 * a₂ α ω ^ 2)) ∂P) (Ici 0 ×ˢ Ici 0) := by
  have hden : ∀ (α : ι) (ω : Ω) (p : ℝ × ℝ), p ∈ Ici (0 : ℝ) ×ˢ Ici (0 : ℝ) →
      1 ≤ (1 + p.1 * a₁ α ω ^ 2) * (1 + p.2 * a₂ α ω ^ 2) := by
    intro α ω p hp
    have hp1 : 0 ≤ p.1 := hp.1
    have hp2 : 0 ≤ p.2 := hp.2
    have e1 : 1 ≤ 1 + p.1 * a₁ α ω ^ 2 := by nlinarith [mul_nonneg hp1 (sq_nonneg (a₁ α ω))]
    have e2 : 1 ≤ 1 + p.2 * a₂ α ω ^ 2 := by nlinarith [mul_nonneg hp2 (sq_nonneg (a₂ α ω))]
    nlinarith
  have hterm : ∀ α, ∀ p ∈ Ici (0 : ℝ) ×ˢ Ici (0 : ℝ), ∀ ω,
      ‖n α ω / ((1 + p.1 * a₁ α ω ^ 2) * (1 + p.2 * a₂ α ω ^ 2))‖ ≤ n α ω := by
    intro α p hp ω
    have := hden α ω p hp
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (hn0 α ω) (by linarith))]
    exact div_le_self (hn0 α ω) this
  apply continuousOn_tsum (u := fun α => ∫ ω, n α ω ∂P)
  · intro α
    apply continuousOn_of_dominated (bound := n α)
    · intro p hp
      exact ((hn α).div ((measurable_const.add (measurable_const.mul ((h1 α).pow_const 2))).mul
        (measurable_const.add (measurable_const.mul ((h2 α).pow_const 2))))).aestronglyMeasurable
    · intro p hp
      exact ae_of_all _ (hterm α p hp)
    · exact hni α
    · refine ae_of_all _ (fun ω => ?_)
      intro p hp
      have hpos : (1 + p.1 * a₁ α ω ^ 2) * (1 + p.2 * a₂ α ω ^ 2) ≠ 0 := by
        have := hden α ω p hp
        linarith
      have hc : ContinuousAt (fun x : ℝ × ℝ => n α ω /
          ((1 + x.1 * a₁ α ω ^ 2) * (1 + x.2 * a₂ α ω ^ 2))) p :=
        ContinuousAt.div (by fun_prop) (by fun_prop) hpos
      exact hc.continuousWithinAt
  · exact hs
  · intro α p hp
    refine (norm_integral_le_of_norm_le (hni α) (ae_of_all _ (hterm α p hp))).trans ?_
    exact le_rfl

private theorem p2_B_cont (hξ : def_app_vol_closed_profile_ii P ξ₁ ξ₂) :
    ContinuousOn (fun p : ℝ × ℝ => pairedB P ξ₁ ξ₂ p.1 p.2) (Ici 0 ×ˢ Ici 0) :=
  p2_cont_gen (n := fun α ω => ξ₁ α ω * ξ₂ α ω) (a₁ := ξ₁) (a₂ := ξ₂)
    (fun α => (hξ.profile₁.measurable α).mul (hξ.profile₂.measurable α))
    hξ.profile₁.measurable hξ.profile₂.measurable hξ.nonneg_prod (p2_prod_int hξ) (p2_prod_sum hξ)

private theorem p2_E_cont (hξ : def_app_vol_closed_profile_ii P ξ₁ ξ₂) :
    ContinuousOn (fun p : ℝ × ℝ => pairedE P ξ₁ ξ₂ p.1 p.2) (Ici 0 ×ˢ Ici 0) :=
  p2_cont_gen (n := fun α ω => ξ₁ α ω ^ 2 * ξ₂ α ω ^ 2) (a₁ := ξ₁) (a₂ := ξ₂)
    (fun α => ((hξ.profile₁.measurable α).pow_const 2).mul ((hξ.profile₂.measurable α).pow_const 2))
    hξ.profile₁.measurable hξ.profile₂.measurable (fun α ω => by positivity)
    hξ.integrable_sq_prod hξ.summable_sq_prod

private theorem p2_cs_sum {f g : ι → Ω → ℝ}
    (hfi : ∀ α, Integrable (fun ω => f α ω ^ 2) P) (hgi : ∀ α, Integrable (fun ω => g α ω ^ 2) P)
    (hfg : ∀ α, Integrable (fun ω => f α ω * g α ω) P)
    (hsf : Summable fun α => ∫ ω, f α ω ^ 2 ∂P) (hsg : Summable fun α => ∫ ω, g α ω ^ 2 ∂P)
    (hsfg : Summable fun α => ∫ ω, f α ω * g α ω ∂P)
    (hA : 0 < ∑' α, ∫ ω, f α ω ^ 2 ∂P) (hB : 0 < ∑' α, ∫ ω, g α ω ^ 2 ∂P) :
    ∑' α, ∫ ω, f α ω * g α ω ∂P ≤
      Real.sqrt ((∑' α, ∫ ω, f α ω ^ 2 ∂P) * (∑' α, ∫ ω, g α ω ^ 2 ∂P)) := by
  set A := ∑' α, ∫ ω, f α ω ^ 2 ∂P with hAdef
  set B := ∑' α, ∫ ω, g α ω ^ 2 ∂P with hBdef
  have hu : 0 < Real.sqrt A := Real.sqrt_pos.2 hA
  have hv : 0 < Real.sqrt B := Real.sqrt_pos.2 hB
  set s := Real.sqrt B / Real.sqrt A with hs
  have hspos : 0 < s := div_pos hv hu
  have hpt : ∀ α, ∫ ω, f α ω * g α ω ∂P ≤ (s * ∫ ω, f α ω ^ 2 ∂P + (∫ ω, g α ω ^ 2 ∂P) / s) / 2 := by
    intro α
    have h1 : ∫ ω, f α ω * g α ω ∂P ≤ ∫ ω, (s * f α ω ^ 2 + g α ω ^ 2 / s) / 2 ∂P := by
      refine integral_mono (hfg α) ((((hfi α).const_mul s).add ((hgi α).div_const s)).div_const 2)
        (fun ω => ?_)
      simp only
      rw [← sub_nonneg]
      have : (s * f α ω ^ 2 + g α ω ^ 2 / s) / 2 - f α ω * g α ω =
          (s * f α ω - g α ω) ^ 2 / (2 * s) := by
        field_simp
        ring
      rw [this]
      positivity
    refine h1.trans (le_of_eq ?_)
    rw [integral_div, integral_add ((hfi α).const_mul s) ((hgi α).div_const s), integral_const_mul,
      integral_div]
  have hsum1 : Summable (fun α => (s * ∫ ω, f α ω ^ 2 ∂P + (∫ ω, g α ω ^ 2 ∂P) / s) / 2) :=
    ((hsf.mul_left s).add (hsg.div_const s)).div_const 2
  refine (Summable.tsum_le_tsum hpt hsfg hsum1).trans (le_of_eq ?_)
  rw [tsum_div_const, Summable.tsum_add (hsf.mul_left s) (hsg.div_const s), tsum_mul_left,
    tsum_div_const, ← hAdef, ← hBdef, Real.sqrt_mul hA.le]
  have hA2 : Real.sqrt A * Real.sqrt A = A := Real.mul_self_sqrt hA.le
  have hB2 : Real.sqrt B * Real.sqrt B = B := Real.mul_self_sqrt hB.le
  rw [hs]
  field_simp
  nlinarith [hA2, hB2]

private theorem p2_negF_pos (hξ : def_app_vol_closed_profile P ξ₁) {q : ℝ} (hq : 0 < q) :
    0 < profileNegFDeriv P ξ₁ q := by
  obtain ⟨α₀, hα₀⟩ := hξ.exists_ne_zero
  have hmeas := hξ.measurable
  have hsq := hξ.integrable_sq
  refine (p1c_summable_n hmeas hsq hξ.summable_sq hq).tsum_pos
    (fun α => integral_nonneg (p1c_n_nonneg (ξ₁ α) hq.le)) α₀ ?_
  rw [integral_pos_iff_support_of_nonneg (p1c_n_nonneg (ξ₁ α₀) hq.le)
    (p1c_n_integrable (hmeas α₀) hq (hsq α₀))]
  refine lt_of_lt_of_le hα₀ (measure_mono ?_)
  intro ω hω
  simp only [mem_setOf_eq] at hω
  simp only [Function.mem_support, ne_eq]
  have h1 : 0 < ξ₁ α₀ ω ^ 4 := by positivity
  have h2 : 0 < 1 + q * ξ₁ α₀ ω ^ 2 := p2_den_pos hq.le
  exact (div_pos h1 (pow_pos h2 2)).ne'

private theorem p2_den_ge {q₁ q₂ x y : ℝ} (h1 : 0 ≤ q₁) (h2 : 0 ≤ q₂) :
    1 ≤ (1 + q₁ * x ^ 2) * (1 + q₂ * y ^ 2) := by
  have e1 : 1 ≤ 1 + q₁ * x ^ 2 := by nlinarith [mul_nonneg h1 (sq_nonneg x)]
  have e2 : 1 ≤ 1 + q₂ * y ^ 2 := by nlinarith [mul_nonneg h2 (sq_nonneg y)]
  nlinarith

private theorem p2_B_term_meas (hξ : def_app_vol_closed_profile_ii P ξ₁ ξ₂) (q₁ q₂ : ℝ) (α : ι) :
    Measurable (fun ω => ξ₁ α ω * ξ₂ α ω / ((1 + q₁ * ξ₁ α ω ^ 2) * (1 + q₂ * ξ₂ α ω ^ 2))) :=
  ((hξ.profile₁.measurable α).mul (hξ.profile₂.measurable α)).div
    ((measurable_const.add (measurable_const.mul ((hξ.profile₁.measurable α).pow_const 2))).mul
      (measurable_const.add (measurable_const.mul ((hξ.profile₂.measurable α).pow_const 2))))

private theorem p2_E_term_meas (hξ : def_app_vol_closed_profile_ii P ξ₁ ξ₂) (q₁ q₂ : ℝ) (α : ι) :
    Measurable (fun ω => ξ₁ α ω ^ 2 * ξ₂ α ω ^ 2 /
      ((1 + q₁ * ξ₁ α ω ^ 2) * (1 + q₂ * ξ₂ α ω ^ 2))) :=
  (((hξ.profile₁.measurable α).pow_const 2).mul ((hξ.profile₂.measurable α).pow_const 2)).div
    ((measurable_const.add (measurable_const.mul ((hξ.profile₁.measurable α).pow_const 2))).mul
      (measurable_const.add (measurable_const.mul ((hξ.profile₂.measurable α).pow_const 2))))

private theorem p2_B_term_le (hξ : def_app_vol_closed_profile_ii P ξ₁ ξ₂) {q₁ q₂ : ℝ}
    (h1 : 0 ≤ q₁) (h2 : 0 ≤ q₂) (α : ι) (ω : Ω) :
    0 ≤ ξ₁ α ω * ξ₂ α ω / ((1 + q₁ * ξ₁ α ω ^ 2) * (1 + q₂ * ξ₂ α ω ^ 2)) ∧
    ξ₁ α ω * ξ₂ α ω / ((1 + q₁ * ξ₁ α ω ^ 2) * (1 + q₂ * ξ₂ α ω ^ 2)) ≤ ξ₁ α ω * ξ₂ α ω := by
  have hge := p2_den_ge (x := ξ₁ α ω) (y := ξ₂ α ω) h1 h2
  exact ⟨div_nonneg (hξ.nonneg_prod α ω) (by linarith), div_le_self (hξ.nonneg_prod α ω) hge⟩

private theorem p2_B_term_int (hξ : def_app_vol_closed_profile_ii P ξ₁ ξ₂) {q₁ q₂ : ℝ}
    (h1 : 0 ≤ q₁) (h2 : 0 ≤ q₂) (α : ι) :
    Integrable (fun ω => ξ₁ α ω * ξ₂ α ω / ((1 + q₁ * ξ₁ α ω ^ 2) * (1 + q₂ * ξ₂ α ω ^ 2))) P :=
  Integrable.mono' (p2_prod_int hξ α) (p2_B_term_meas hξ q₁ q₂ α).aestronglyMeasurable
    (ae_of_all _ (fun ω => by
      have := p2_B_term_le hξ h1 h2 α ω
      rw [Real.norm_eq_abs, abs_of_nonneg this.1]
      exact this.2))

private theorem p2_B_term_sum (hξ : def_app_vol_closed_profile_ii P ξ₁ ξ₂) {q₁ q₂ : ℝ}
    (h1 : 0 ≤ q₁) (h2 : 0 ≤ q₂) :
    Summable (fun α => ∫ ω, ξ₁ α ω * ξ₂ α ω /
      ((1 + q₁ * ξ₁ α ω ^ 2) * (1 + q₂ * ξ₂ α ω ^ 2)) ∂P) :=
  Summable.of_nonneg_of_le (fun α => integral_nonneg (fun ω => (p2_B_term_le hξ h1 h2 α ω).1))
    (fun α => integral_mono (p2_B_term_int hξ h1 h2 α) (p2_prod_int hξ α)
      (fun ω => (p2_B_term_le hξ h1 h2 α ω).2)) (p2_prod_sum hξ)

private theorem p2_E_term_le (hξ : def_app_vol_closed_profile_ii P ξ₁ ξ₂) {q₁ q₂ : ℝ}
    (h1 : 0 ≤ q₁) (h2 : 0 ≤ q₂) (α : ι) (ω : Ω) :
    0 ≤ ξ₁ α ω ^ 2 * ξ₂ α ω ^ 2 / ((1 + q₁ * ξ₁ α ω ^ 2) * (1 + q₂ * ξ₂ α ω ^ 2)) ∧
    ξ₁ α ω ^ 2 * ξ₂ α ω ^ 2 / ((1 + q₁ * ξ₁ α ω ^ 2) * (1 + q₂ * ξ₂ α ω ^ 2)) ≤
      ξ₁ α ω ^ 2 * ξ₂ α ω ^ 2 := by
  have hge := p2_den_ge (x := ξ₁ α ω) (y := ξ₂ α ω) h1 h2
  have h0 : 0 ≤ ξ₁ α ω ^ 2 * ξ₂ α ω ^ 2 := by positivity
  exact ⟨div_nonneg h0 (by linarith), div_le_self h0 hge⟩

private theorem p2_E_term_int (hξ : def_app_vol_closed_profile_ii P ξ₁ ξ₂) {q₁ q₂ : ℝ}
    (h1 : 0 ≤ q₁) (h2 : 0 ≤ q₂) (α : ι) :
    Integrable (fun ω => ξ₁ α ω ^ 2 * ξ₂ α ω ^ 2 /
      ((1 + q₁ * ξ₁ α ω ^ 2) * (1 + q₂ * ξ₂ α ω ^ 2))) P :=
  Integrable.mono' (hξ.integrable_sq_prod α) (p2_E_term_meas hξ q₁ q₂ α).aestronglyMeasurable
    (ae_of_all _ (fun ω => by
      have := p2_E_term_le hξ h1 h2 α ω
      rw [Real.norm_eq_abs, abs_of_nonneg this.1]
      exact this.2))

private theorem p2_E_term_sum (hξ : def_app_vol_closed_profile_ii P ξ₁ ξ₂) {q₁ q₂ : ℝ}
    (h1 : 0 ≤ q₁) (h2 : 0 ≤ q₂) :
    Summable (fun α => ∫ ω, ξ₁ α ω ^ 2 * ξ₂ α ω ^ 2 /
      ((1 + q₁ * ξ₁ α ω ^ 2) * (1 + q₂ * ξ₂ α ω ^ 2)) ∂P) :=
  Summable.of_nonneg_of_le (fun α => integral_nonneg (fun ω => (p2_E_term_le hξ h1 h2 α ω).1))
    (fun α => integral_mono (p2_E_term_int hξ h1 h2 α) (hξ.integrable_sq_prod α)
      (fun ω => (p2_E_term_le hξ h1 h2 α ω).2)) hξ.summable_sq_prod

private theorem p2_B_bounds (hξ : def_app_vol_closed_profile_ii P ξ₁ ξ₂) {q₁ q₂ : ℝ}
    (h1 : 0 ≤ q₁) (h2 : 0 ≤ q₂) :
    0 ≤ pairedB P ξ₁ ξ₂ q₁ q₂ ∧
      pairedB P ξ₁ ξ₂ q₁ q₂ ≤ min (Real.sqrt (profileRDeriv P ξ₁ q₁ * profileRDeriv P ξ₂ q₂))
        (∑' α, ∫ ω, ξ₁ α ω * ξ₂ α ω ∂P) := by
  refine ⟨tsum_nonneg (fun α => integral_nonneg (fun ω => (p2_B_term_le hξ h1 h2 α ω).1)),
    le_min ?_ ?_⟩
  · have hR1 := p1c_rderiv_pos hξ.profile₁.measurable hξ.profile₁.integrable_sq
      hξ.profile₁.summable_sq hξ.profile₁.exists_ne_zero.choose_spec h1
    have hR2 := p1c_rderiv_pos hξ.profile₂.measurable hξ.profile₂.integrable_sq
      hξ.profile₂.summable_sq hξ.profile₂.exists_ne_zero.choose_spec h2
    have key := p2_cs_sum (P := P)
      (f := fun α ω => ξ₁ α ω / (1 + q₁ * ξ₁ α ω ^ 2))
      (g := fun α ω => ξ₂ α ω / (1 + q₂ * ξ₂ α ω ^ 2))
      (fun α => by simpa only [div_pow] using
        p1c_d_integrable (hξ.profile₁.measurable α) h1 (hξ.profile₁.integrable_sq α))
      (fun α => by simpa only [div_pow] using
        p1c_d_integrable (hξ.profile₂.measurable α) h2 (hξ.profile₂.integrable_sq α))
      (fun α => by simpa only [div_mul_div_comm] using p2_B_term_int hξ h1 h2 α)
      (by simpa only [div_pow] using
        p1c_summable_d hξ.profile₁.measurable hξ.profile₁.integrable_sq hξ.profile₁.summable_sq h1)
      (by simpa only [div_pow] using
        p1c_summable_d hξ.profile₂.measurable hξ.profile₂.integrable_sq hξ.profile₂.summable_sq h2)
      (by simpa only [div_mul_div_comm] using p2_B_term_sum hξ h1 h2)
      (by simpa only [div_pow] using hR1)
      (by simpa only [div_pow] using hR2)
    simpa only [div_pow, div_mul_div_comm, pairedB, profileRDeriv] using key
  · unfold pairedB
    refine Summable.tsum_le_tsum (fun α => ?_) (p2_B_term_sum hξ h1 h2) (p2_prod_sum hξ)
    exact integral_mono (p2_B_term_int hξ h1 h2 α) (p2_prod_int hξ α)
      (fun ω => (p2_B_term_le hξ h1 h2 α ω).2)

private theorem p2_E_bounds (hξ : def_app_vol_closed_profile_ii P ξ₁ ξ₂) {q₁ q₂ : ℝ}
    (h1 : 0 < q₁) (h2 : 0 < q₂) :
    0 ≤ pairedE P ξ₁ ξ₂ q₁ q₂ ∧
      pairedE P ξ₁ ξ₂ q₁ q₂ ≤ Real.sqrt (profileNegFDeriv P ξ₁ q₁ * profileNegFDeriv P ξ₂ q₂) := by
  refine ⟨tsum_nonneg (fun α => integral_nonneg
    (fun ω => (p2_E_term_le hξ h1.le h2.le α ω).1)), ?_⟩
  have hq1 : ∀ α ω, (ξ₁ α ω ^ 2 / (1 + q₁ * ξ₁ α ω ^ 2)) ^ 2 =
      ξ₁ α ω ^ 4 / (1 + q₁ * ξ₁ α ω ^ 2) ^ 2 := fun α ω => by rw [div_pow]; ring
  have hq2 : ∀ α ω, (ξ₂ α ω ^ 2 / (1 + q₂ * ξ₂ α ω ^ 2)) ^ 2 =
      ξ₂ α ω ^ 4 / (1 + q₂ * ξ₂ α ω ^ 2) ^ 2 := fun α ω => by rw [div_pow]; ring
  have key := p2_cs_sum (P := P)
    (f := fun α ω => ξ₁ α ω ^ 2 / (1 + q₁ * ξ₁ α ω ^ 2))
    (g := fun α ω => ξ₂ α ω ^ 2 / (1 + q₂ * ξ₂ α ω ^ 2))
    (fun α => by simpa only [hq1] using
      p1c_n_integrable (hξ.profile₁.measurable α) h1 (hξ.profile₁.integrable_sq α))
    (fun α => by simpa only [hq2] using
      p1c_n_integrable (hξ.profile₂.measurable α) h2 (hξ.profile₂.integrable_sq α))
    (fun α => by simpa only [div_mul_div_comm] using p2_E_term_int hξ h1.le h2.le α)
    (by simpa only [hq1] using
      p1c_summable_n hξ.profile₁.measurable hξ.profile₁.integrable_sq hξ.profile₁.summable_sq h1)
    (by simpa only [hq2] using
      p1c_summable_n hξ.profile₂.measurable hξ.profile₂.integrable_sq hξ.profile₂.summable_sq h2)
    (by simpa only [div_mul_div_comm] using p2_E_term_sum hξ h1.le h2.le)
    (by simpa only [hq1, profileNegFDeriv] using p2_negF_pos hξ.profile₁ h1)
    (by simpa only [hq2, profileNegFDeriv] using p2_negF_pos hξ.profile₂ h2)
  simpa only [hq1, hq2, div_mul_div_comm, pairedE, profileNegFDeriv] using key

end PairedHelpers
section EmaHelpers
variable {P : Measure Ω} [IsProbabilityMeasure P]

private lemma p2e_gauss_sq : ∫ x, x ^ 2 ∂(gaussianReal 0 1) = 1 := by
  have hL : MemLp (id : ℝ → ℝ) 2 (gaussianReal 0 1) := memLp_id_gaussianReal' (2 : ℝ≥0∞) (by simp)
  have h := variance_eq_sub hL
  rw [variance_id_gaussianReal] at h
  simp only [Pi.pow_apply, id] at h
  have hm : ∫ x, x ∂(gaussianReal 0 1) = 0 := integral_id_gaussianReal
  rw [hm] at h
  norm_num at h ⊢
  linarith

private lemma p2e_gsq {g' : Ω → ℝ} (hg : HasLaw g' (gaussianReal 0 1) P) :
    Integrable (fun ω => g' ω ^ 2) P ∧ ∫ ω, g' ω ^ 2 ∂P = 1 := by
  have hL : MemLp (id : ℝ → ℝ) 2 (gaussianReal 0 1) := memLp_id_gaussianReal' (2 : ℝ≥0∞) (by simp)
  have h2 : Integrable (fun x : ℝ => x ^ 2) (gaussianReal 0 1) := hL.integrable_sq
  refine ⟨hg.integrable_comp h2, ?_⟩
  have h := hg.integral_comp (f := fun x : ℝ => x ^ 2) (continuous_pow 2).aestronglyMeasurable
  rw [p2e_gauss_sq] at h
  exact h

private lemma p2e_g4 {g' : Ω → ℝ} (hg : HasLaw g' (gaussianReal 0 1) P) :
    Integrable (fun ω => g' ω ^ 4) P := by
  have hL : MemLp (id : ℝ → ℝ) ((4 : ℕ) : ℝ≥0∞) (gaussianReal 0 1) :=
    memLp_id_gaussianReal' ((4 : ℕ) : ℝ≥0∞) (by simp)
  have h2 := hL.integrable_norm_pow (by norm_num)
  have h3 : Integrable (fun x : ℝ => x ^ 4) (gaussianReal 0 1) := by
    refine h2.congr (ae_of_all _ (fun x => ?_))
    simp only [id, Real.norm_eq_abs]
    exact Even.pow_abs (by decide) x
  exact hg.integrable_comp h3

private lemma p2e_pos {g' : Ω → ℝ} (hg : HasLaw g' (gaussianReal 0 1) P) {c : ℝ} (hc : c ≠ 0) :
    0 < P {ω | c * g' ω ≠ 0} := by
  have hS : MeasurableSet (Ioc (0 : ℝ) 1) := measurableSet_Ioc
  have h1 : 0 < gaussianReal 0 1 (Ioc (0 : ℝ) 1) := by
    rw [pos_iff_ne_zero]
    intro h0
    have := gaussianReal_absolutelyContinuous' 0 (one_ne_zero) h0
    simp [Real.volume_Ioc] at this
  have h2 : P ((g') ⁻¹' (Ioc (0 : ℝ) 1)) = gaussianReal 0 1 (Ioc (0 : ℝ) 1) := by
    rw [← hg.map_eq, Measure.map_apply_of_aemeasurable hg.aemeasurable hS]
  refine lt_of_lt_of_le (h2 ▸ h1) (measure_mono ?_)
  intro ω hω
  simp only [mem_preimage, mem_Ioc] at hω
  exact mul_ne_zero hc hω.1.ne'

private lemma p2e_term {g' : Ω → ℝ} (hg : HasLaw g' (gaussianReal 0 1) P) (c q : ℝ) :
    ∫ ω, (c * g' ω) ^ 2 / (1 + q * (c * g' ω) ^ 2) ∂P =
      c ^ 2 * Muon.DetEquiv.J (c ^ 2 * q) := by
  have hφ : Measurable (fun x : ℝ => x ^ 2 / (1 + c ^ 2 * q * x ^ 2)) := by fun_prop
  have h := hg.integral_comp (f := fun x : ℝ => x ^ 2 / (1 + c ^ 2 * q * x ^ 2))
    hφ.aestronglyMeasurable
  unfold Muon.DetEquiv.J
  rw [← h, ← integral_const_mul]
  refine integral_congr_ae (ae_of_all _ (fun ω => ?_))
  have hd : 1 + q * (c * g' ω) ^ 2 = 1 + c ^ 2 * q * g' ω ^ 2 := by ring
  simp only [Function.comp]
  rw [hd]
  ring

private lemma p2e_w_nonneg {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) (j : ℕ) :
    0 ≤ Muon.emaW β j := by
  unfold Muon.emaW
  exact mul_nonneg (by linarith) (pow_nonneg hβ0 _)

private lemma p2e_w_le_one {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) (j : ℕ) :
    Muon.emaW β j ≤ 1 := by
  unfold Muon.emaW
  have h1 : β ^ j ≤ 1 := pow_le_one₀ hβ0 hβ1.le
  have h2 : 0 ≤ β ^ j := pow_nonneg hβ0 _
  nlinarith

private lemma p2e_w_summable {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {p : ℕ} (hp : p ≠ 0) :
    Summable (fun j : ℕ => Muon.emaW β j ^ p) := by
  have key : ∀ j : ℕ, Muon.emaW β j ^ p = (1 - β) ^ p * (β ^ p) ^ j := by
    intro j
    unfold Muon.emaW
    rw [mul_pow, ← pow_mul, ← pow_mul, mul_comm j p]
  simp_rw [key]
  exact (summable_geometric_of_lt_one (pow_nonneg hβ0 p) (pow_lt_one₀ hβ0 hβ1 hp)).mul_left _

private lemma p2e_cg_profile {g' : Ω → ℝ} (hg : HasLaw g' (gaussianReal 0 1) P) (c : ℝ) :
    Integrable (fun ω => (c * g' ω) ^ 2) P ∧ ∫ ω, (c * g' ω) ^ 2 ∂P = c ^ 2 := by
  obtain ⟨h1, h2⟩ := p2e_gsq hg
  simp_rw [mul_pow]
  exact ⟨h1.const_mul _, by rw [integral_const_mul, h2, mul_one]⟩

private lemma p2e_W_profile {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {ℓ : ℕ}
    {g : ℕ ⊕ Fin ℓ → Ω → ℝ} (hg : IsStdGaussianFamily P g) :
    def_app_vol_closed_profile P (fun (j : ℕ) ω => Muon.emaW β j * g (Sum.inl j) ω) where
  measurable := fun j => measurable_const.mul (hg.1 _)
  integrable_sq := fun j => (p2e_cg_profile (hg.2.2 _) _).1
  summable_sq := by
    simp_rw [(p2e_cg_profile (hg.2.2 _) _).2]
    exact p2e_w_summable hβ0 hβ1 (by norm_num)
  exists_ne_zero := ⟨0, p2e_pos (hg.2.2 _) (by
    unfold Muon.emaW
    simp only [pow_zero, mul_one]
    linarith)⟩

private lemma p2e_tsum_inl {ℓ : ℕ} (f : ℕ ⊕ Fin ℓ → ℝ) (h : ∀ i, f (Sum.inr i) = 0) :
    ∑' a, f a = ∑' j : ℕ, f (Sum.inl j) := by
  refine (Function.Injective.tsum_eq Sum.inl_injective (f := f) ?_).symm
  intro a ha
  rcases a with j | i
  · exact ⟨j, rfl⟩
  · exact absurd (h i) ha

private lemma p2e_F_W {β : ℝ} {ℓ : ℕ} {g : ℕ ⊕ Fin ℓ → Ω → ℝ} (hg : IsStdGaussianFamily P g) :
    profileF P (fun (j : ℕ) ω => Muon.emaW β j * g (Sum.inl j) ω) =
      Muon.DetEquiv.Fw (Muon.emaW β) := by
  funext q
  unfold profileF Muon.DetEquiv.Fw
  exact tsum_congr (fun j => p2e_term (hg.2.2 _) _ _)

private lemma p2e_F1 {β : ℝ} {ℓ : ℕ} {g : ℕ ⊕ Fin ℓ → Ω → ℝ} (hg : IsStdGaussianFamily P g) :
    profileF P (emaXi₁ β ℓ g) = Muon.DetEquiv.Fw (Muon.emaW β) := by
  rw [← p2e_F_W hg]
  funext q
  unfold profileF
  rw [p2e_tsum_inl]
  · rfl
  · intro i
    simp [emaXi₁]

private lemma p2e_equiv (ℓ : ℕ) : ∃ e : ℕ ⊕ Fin ℓ ≃ ℕ,
    (∀ j, e (Sum.inl j) = j + ℓ) ∧ (∀ i : Fin ℓ, e (Sum.inr i) = ℓ - (i.val + 1)) := by
  refine ⟨
    { toFun := fun a => match a with
        | Sum.inl j => j + ℓ
        | Sum.inr i => ℓ - (i.val + 1)
      invFun := fun n => if h : n < ℓ then Sum.inr ⟨ℓ - (n + 1), by omega⟩ else Sum.inl (n - ℓ)
      left_inv := ?_
      right_inv := ?_ }, fun j => rfl, fun i => rfl⟩
  · intro a
    rcases a with j | i
    · simp
    · have := i.isLt
      simp only [show ¬ (ℓ - (i.val + 1) ≥ ℓ) by omega, not_false_eq_true, ge_iff_le]
      simp only [show ℓ - (i.val + 1) < ℓ by omega, dite_true]
      congr 1
      ext
      simp only
      omega
  · intro n
    by_cases h : n < ℓ
    · simp only [h, dite_true]
      omega
    · simp only [h, dite_false]
      omega

private lemma p2e_F2 {β : ℝ} {ℓ : ℕ} {g : ℕ ⊕ Fin ℓ → Ω → ℝ} (hg : IsStdGaussianFamily P g) :
    profileF P (emaXi₂ β ℓ g) = Muon.DetEquiv.Fw (Muon.emaW β) := by
  obtain ⟨e, he1, he2⟩ := p2e_equiv ℓ
  funext q
  unfold profileF Muon.DetEquiv.Fw
  rw [← e.tsum_eq (fun k => Muon.emaW β k ^ 2 * Muon.DetEquiv.J (Muon.emaW β k ^ 2 * q))]
  refine tsum_congr (fun a => ?_)
  rcases a with j | i
  · have hc : β ^ ℓ * Muon.emaW β j = Muon.emaW β (j + ℓ) := by
      unfold Muon.emaW; ring
    simp only [emaXi₂, he1]
    rw [← hc]
    exact p2e_term (hg.2.2 _) _ _
  · simp only [emaXi₂, he2]
    exact p2e_term (hg.2.2 _) _ _

private lemma p2e_g4_int {A : Type*} {g : A → Ω → ℝ} (hg : ∀ a, HasLaw (g a) (gaussianReal 0 1) P)
    (c : A → ℝ) (a : A) : Integrable (fun ω => (c a * g a ω) ^ 4) P := by
  simp_rw [mul_pow]
  exact (p2e_g4 (hg a)).const_mul _

private lemma p2e_cg_family {A : Type*} [Countable A] {g : A → Ω → ℝ}
    (hgm : ∀ a, Measurable (g a)) (hg : ∀ a, HasLaw (g a) (gaussianReal 0 1) P)
    (c : A → ℝ) (hs : Summable (fun a => c a ^ 2)) (hne : ∃ a, c a ≠ 0) :
    def_app_vol_closed_profile P (fun a ω => c a * g a ω) where
  measurable := fun a => measurable_const.mul (hgm a)
  integrable_sq := fun a => (p2e_cg_profile (hg a) _).1
  summable_sq := by
    simp_rw [(p2e_cg_profile (hg _) _).2]
    exact hs
  exists_ne_zero := by
    obtain ⟨a, ha⟩ := hne
    exact ⟨a, p2e_pos (hg a) ha⟩

private lemma p2e_pair_family {A : Type*} [Countable A] {g : A → Ω → ℝ}
    (hgm : ∀ a, Measurable (g a)) (hg : ∀ a, HasLaw (g a) (gaussianReal 0 1) P)
    (c₁ c₂ : A → ℝ) (h₁ : Summable (fun a => c₁ a ^ 2)) (h₂ : Summable (fun a => c₂ a ^ 2))
    (hne₁ : ∃ a, c₁ a ≠ 0) (hne₂ : ∃ a, c₂ a ≠ 0) (hnn : ∀ a, 0 ≤ c₁ a * c₂ a)
    (hs : Summable (fun a => c₁ a ^ 2 * c₂ a ^ 2)) :
    def_app_vol_closed_profile_ii P (fun a ω => c₁ a * g a ω) (fun a ω => c₂ a * g a ω) where
  profile₁ := p2e_cg_family hgm hg c₁ h₁ hne₁
  profile₂ := p2e_cg_family hgm hg c₂ h₂ hne₂
  nonneg_prod := fun a ω => by
    have : c₁ a * g a ω * (c₂ a * g a ω) = (c₁ a * c₂ a) * g a ω ^ 2 := by ring
    rw [this]
    exact mul_nonneg (hnn a) (sq_nonneg _)
  integrable_sq_prod := fun a => by
    have := (p2e_g4 (hg a)).const_mul (c₁ a ^ 2 * c₂ a ^ 2)
    refine this.congr (ae_of_all _ (fun ω => ?_))
    simp only
    ring
  summable_sq_prod := by
    have hM : ∀ a, ∫ ω, (c₁ a * g a ω) ^ 2 * (c₂ a * g a ω) ^ 2 ∂P =
        (c₁ a ^ 2 * c₂ a ^ 2) * ∫ x, x ^ 4 ∂(gaussianReal 0 1) := by
      intro a
      have h := (hg a).integral_comp (f := fun x : ℝ => x ^ 4) (continuous_pow 4).aestronglyMeasurable
      simp only [Function.comp] at h
      rw [← h, ← integral_const_mul]
      refine integral_congr_ae (ae_of_all _ (fun ω => ?_))
      simp only
      ring
    simp_rw [hM]
    exact hs.mul_right _

private lemma p2e_xi1_eq (β : ℝ) (ℓ : ℕ) (g : ℕ ⊕ Fin ℓ → Ω → ℝ) :
    emaXi₁ β ℓ g = fun a ω => (Sum.elim (fun j : ℕ => Muon.emaW β j) (fun _ => (0 : ℝ)) a) * g a ω := by
  funext a ω
  rcases a with j | i
  · simp [emaXi₁]
  · simp [emaXi₁]

private lemma p2e_xi2_eq (β : ℝ) (ℓ : ℕ) (g : ℕ ⊕ Fin ℓ → Ω → ℝ) (e : ℕ ⊕ Fin ℓ ≃ ℕ)
    (he1 : ∀ j, e (Sum.inl j) = j + ℓ) (he2 : ∀ i : Fin ℓ, e (Sum.inr i) = ℓ - (i.val + 1)) :
    emaXi₂ β ℓ g = fun a ω => Muon.emaW β (e a) * g a ω := by
  funext a ω
  rcases a with j | i
  · have hc : β ^ ℓ * Muon.emaW β j = Muon.emaW β (j + ℓ) := by
      unfold Muon.emaW; ring
    simp only [emaXi₂, he1, ← hc]
  · simp only [emaXi₂, he2]

private lemma p2e_profile_ii {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {ℓ : ℕ}
    {g : ℕ ⊕ Fin ℓ → Ω → ℝ} (hg : IsStdGaussianFamily P g) :
    def_app_vol_closed_profile_ii P (emaXi₁ β ℓ g) (emaXi₂ β ℓ g) := by
  obtain ⟨e, he1, he2⟩ := p2e_equiv ℓ
  rw [p2e_xi1_eq, p2e_xi2_eq β ℓ g e he1 he2]
  have hb : 0 < 1 - β := by linarith
  have hw2 := p2e_w_summable hβ0 hβ1 (p := 2) (by norm_num)
  refine p2e_pair_family hg.1 hg.2.2 _ _ ?_ ?_ ?_ ?_ ?_ ?_
  · refine Summable.sum _ ?_ ?_
    · exact hw2
    · exact Summable.of_finite
  · exact (Equiv.summable_iff e (f := fun k => Muon.emaW β k ^ 2)).2 hw2
  · exact ⟨Sum.inl 0, by simp [Muon.emaW, hb.ne']⟩
  · exact ⟨e.symm 0, by simp [Muon.emaW, hb.ne']⟩
  · intro a
    refine mul_nonneg ?_ (p2e_w_nonneg hβ0 hβ1 _)
    rcases a with j | i
    · exact p2e_w_nonneg hβ0 hβ1 j
    · simp
  · refine Summable.sum _ ?_ ?_
    · refine Summable.of_nonneg_of_le (fun j => ?_) (fun j => ?_) hw2
      · simp only [Function.comp, Sum.elim_inl, he1]; positivity
      simp only [Function.comp, Sum.elim_inl, he1]
      have h0 := p2e_w_nonneg hβ0 hβ1 (j + ℓ)
      have h1 := p2e_w_le_one hβ0 hβ1 (j + ℓ)
      have : Muon.emaW β (j + ℓ) ^ 2 ≤ 1 := by nlinarith
      exact mul_le_of_le_one_right (sq_nonneg _) this
    · exact Summable.of_finite

private lemma p2e_R_diff {A : Type*} {ξ : A → Ω → ℝ} (hξ : def_app_vol_closed_profile P ξ)
    {p p' : ℝ} (hp : 0 ≤ p) (hp' : 0 ≤ p') :
    profileR P ξ p - profileR P ξ p' = (p - p') *
      ∑' α, ∫ ω, ξ α ω ^ 2 / ((1 + p * ξ α ω ^ 2) * (1 + p' * ξ α ω ^ 2)) ∂P := by
  have hs1 := p1a_summable_term hξ.integrable_sq hξ.summable_sq hp
  have hs2 := p1a_summable_term hξ.integrable_sq hξ.summable_sq hp'
  unfold profileR profileF
  rw [← tsum_mul_left, ← tsum_mul_left, ← Summable.tsum_sub (hs1.mul_left p) (hs2.mul_left p'),
    ← tsum_mul_left]
  refine tsum_congr (fun α => ?_)
  have i1 := p1a_term_integrable (hξ.measurable α) hp (hξ.integrable_sq α)
  have i2 := p1a_term_integrable (hξ.measurable α) hp' (hξ.integrable_sq α)
  rw [← integral_const_mul, ← integral_const_mul, ← integral_sub (i1.const_mul p) (i2.const_mul p'),
    ← integral_const_mul]
  refine integral_congr_ae (ae_of_all _ (fun ω => ?_))
  have d1 : 0 < 1 + p * ξ α ω ^ 2 := p2_den_pos hp
  have d2 : 0 < 1 + p' * ξ α ω ^ 2 := p2_den_pos hp'
  simp only
  field_simp
  ring

private lemma p2e_F_diff {A : Type*} {ξ : A → Ω → ℝ} (hξ : def_app_vol_closed_profile P ξ)
    {p p' : ℝ} (hp : 0 ≤ p) (hp' : 0 ≤ p') :
    profileF P ξ p - profileF P ξ p' = (p' - p) *
      ∑' α, ∫ ω, ξ α ω ^ 4 / ((1 + p * ξ α ω ^ 2) * (1 + p' * ξ α ω ^ 2)) ∂P := by
  have hs1 := p1a_summable_term hξ.integrable_sq hξ.summable_sq hp
  have hs2 := p1a_summable_term hξ.integrable_sq hξ.summable_sq hp'
  unfold profileF
  rw [← Summable.tsum_sub hs1 hs2, ← tsum_mul_left]
  refine tsum_congr (fun α => ?_)
  have i1 := p1a_term_integrable (hξ.measurable α) hp (hξ.integrable_sq α)
  have i2 := p1a_term_integrable (hξ.measurable α) hp' (hξ.integrable_sq α)
  rw [← integral_sub i1 i2, ← integral_const_mul]
  refine integral_congr_ae (ae_of_all _ (fun ω => ?_))
  have d1 : 0 < 1 + p * ξ α ω ^ 2 := p2_den_pos hp
  have d2 : 0 < 1 + p' * ξ α ω ^ 2 := p2_den_pos hp'
  simp only
  field_simp
  ring

private lemma p2e_B_eq (β : ℝ) (ℓ : ℕ) (g : ℕ ⊕ Fin ℓ → Ω → ℝ) (q q' : ℝ) :
    pairedB P (emaXi₁ β ℓ g) (emaXi₂ β ℓ g) q q' = β ^ ℓ * ∑' j : ℕ, ∫ ω,
      (Muon.emaW β j * g (Sum.inl j) ω) ^ 2 / ((1 + q * (Muon.emaW β j * g (Sum.inl j) ω) ^ 2) *
        (1 + (β ^ (2 * ℓ) * q') * (Muon.emaW β j * g (Sum.inl j) ω) ^ 2)) ∂P := by
  unfold pairedB
  rw [p2e_tsum_inl, ← tsum_mul_left]
  · refine tsum_congr (fun j => ?_)
    rw [← integral_const_mul]
    refine integral_congr_ae (ae_of_all _ (fun ω => ?_))
    simp only [emaXi₁, emaXi₂]
    have hd : 1 + q' * (β ^ ℓ * Muon.emaW β j * g (Sum.inl j) ω) ^ 2 =
        1 + β ^ (2 * ℓ) * q' * (Muon.emaW β j * g (Sum.inl j) ω) ^ 2 := by ring
    rw [hd]
    ring
  · intro i
    simp [emaXi₁]

private lemma p2e_E_eq (β : ℝ) (ℓ : ℕ) (g : ℕ ⊕ Fin ℓ → Ω → ℝ) (q q' : ℝ) :
    pairedE P (emaXi₁ β ℓ g) (emaXi₂ β ℓ g) q q' = β ^ (2 * ℓ) * ∑' j : ℕ, ∫ ω,
      (Muon.emaW β j * g (Sum.inl j) ω) ^ 4 / ((1 + q * (Muon.emaW β j * g (Sum.inl j) ω) ^ 2) *
        (1 + (β ^ (2 * ℓ) * q') * (Muon.emaW β j * g (Sum.inl j) ω) ^ 2)) ∂P := by
  unfold pairedE
  rw [p2e_tsum_inl, ← tsum_mul_left]
  · refine tsum_congr (fun j => ?_)
    rw [← integral_const_mul]
    refine integral_congr_ae (ae_of_all _ (fun ω => ?_))
    simp only [emaXi₁, emaXi₂]
    have hd : 1 + q' * (β ^ ℓ * Muon.emaW β j * g (Sum.inl j) ω) ^ 2 =
        1 + β ^ (2 * ℓ) * q' * (Muon.emaW β j * g (Sum.inl j) ω) ^ 2 := by ring
    rw [hd]
    ring
  · intro i
    simp [emaXi₁]

private lemma p2e_N_cont {A : Type*} {ξ : A → Ω → ℝ} (hξ : def_app_vol_closed_profile P ξ)
    (h4 : ∀ α, Integrable (fun ω => ξ α ω ^ 4) P)
    (hs4 : Summable (fun α => ∫ ω, ξ α ω ^ 4 ∂P)) :
    ContinuousOn (profileNegFDeriv P ξ) (Ici 0) := by
  have hb : ∀ α (q : ℝ), 0 ≤ q → ∀ ω, ‖ξ α ω ^ 4 / (1 + q * ξ α ω ^ 2) ^ 2‖ ≤ ξ α ω ^ 4 := by
    intro α q hq ω
    rw [Real.norm_eq_abs, abs_of_nonneg (p1c_n_nonneg (ξ α) hq ω)]
    have h1 : 0 ≤ q * ξ α ω ^ 2 := mul_nonneg hq (sq_nonneg _)
    apply div_le_self (by positivity)
    nlinarith
  unfold profileNegFDeriv
  apply continuousOn_tsum (u := fun α => ∫ ω, ξ α ω ^ 4 ∂P)
  · intro α
    apply continuousOn_of_dominated (bound := fun ω => ξ α ω ^ 4)
    · intro q hq
      exact (p1c_meas_n (hξ.measurable α) q).aestronglyMeasurable
    · intro q hq
      exact ae_of_all _ (hb α q hq)
    · exact h4 α
    · refine ae_of_all _ (fun ω q hq => ?_)
      have hpos : (1 + q * ξ α ω ^ 2) ^ 2 ≠ 0 := by
        have : 0 < 1 + q * ξ α ω ^ 2 := p2_den_pos (x := ξ α ω) hq
        positivity
      have hc : ContinuousAt (fun x : ℝ => ξ α ω ^ 4 / (1 + x * ξ α ω ^ 2) ^ 2) q :=
        ContinuousAt.div (by fun_prop) (by fun_prop) hpos
      exact hc.continuousWithinAt
  · exact hs4
  · intro α q hq
    exact norm_integral_le_of_norm_le (h4 α) (ae_of_all _ (hb α q hq))

private lemma p2e_F_hasDerivWithinAt_zero {A : Type*} [Countable A] {ξ : A → Ω → ℝ}
    (hξ : def_app_vol_closed_profile P ξ)
    (h4 : ∀ α, Integrable (fun ω => ξ α ω ^ 4) P)
    (hs4 : Summable (fun α => ∫ ω, ξ α ω ^ 4 ∂P)) :
    HasDerivWithinAt (profileF P ξ) (-profileNegFDeriv P ξ 0) (Ici 0) 0 := by
  obtain ⟨hFc, hRc, hFa, hRa, hAnti, hF0, hR0, hFpos, hRd, hRpos, hFd, hid⟩ :=
    lem_app_vol_closed_profile_i hξ
  have hN := p2e_N_cont hξ h4 hs4 0 (mem_Ici.2 le_rfl)
  refine hasDerivWithinAt_Ici_of_tendsto_deriv (s := Ioi 0) ?_ ?_ self_mem_nhdsWithin ?_
  · intro x hx
    exact (hFd x hx).1.differentiableAt.differentiableWithinAt
  · exact (hFc 0 (mem_Ici.2 le_rfl)).mono Ioi_subset_Ici_self
  · have h1 : Tendsto (profileNegFDeriv P ξ) (𝓝[>] 0) (𝓝 (profileNegFDeriv P ξ 0)) :=
      hN.tendsto.mono_left (nhdsWithin_mono _ Ioi_subset_Ici_self)
    refine h1.neg.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact ((hFd x hx).1.deriv).symm

private lemma p2e_part3 {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {ℓ : ℕ} {g : ℕ ⊕ Fin ℓ → Ω → ℝ}
    (hg : IsStdGaussianFamily P g) {q q' : ℝ} (hq : 0 ≤ q) (hq' : 0 ≤ q')
    (hne : q ≠ β ^ (2 * ℓ) * q') :
    pairedB P (emaXi₁ β ℓ g) (emaXi₂ β ℓ g) q q' =
        β ^ ℓ * (Muon.DetEquiv.rW (Muon.emaW β) q -
          Muon.DetEquiv.rW (Muon.emaW β) (β ^ (2 * ℓ) * q')) / (q - β ^ (2 * ℓ) * q') ∧
    pairedE P (emaXi₁ β ℓ g) (emaXi₂ β ℓ g) q q' =
        β ^ (2 * ℓ) * (Muon.DetEquiv.Fw (Muon.emaW β) q -
          Muon.DetEquiv.Fw (Muon.emaW β) (β ^ (2 * ℓ) * q')) / (β ^ (2 * ℓ) * q' - q) := by
  have hW := p2e_W_profile hβ0 hβ1 hg
  have hp' : 0 ≤ β ^ (2 * ℓ) * q' := mul_nonneg (pow_nonneg hβ0 _) hq'
  have hR : ∀ x, profileR P (fun (j : ℕ) ω => Muon.emaW β j * g (Sum.inl j) ω) x =
      Muon.DetEquiv.rW (Muon.emaW β) x := by
    intro x
    unfold profileR Muon.DetEquiv.rW
    rw [congrFun (p2e_F_W hg) x]
  have hF : ∀ x, profileF P (fun (j : ℕ) ω => Muon.emaW β j * g (Sum.inl j) ω) x =
      Muon.DetEquiv.Fw (Muon.emaW β) x := fun x => congrFun (p2e_F_W hg) x
  have hd1 := p2e_R_diff hW hq hp'
  have hd2 := p2e_F_diff hW hq hp'
  rw [hR, hR] at hd1
  rw [hF, hF] at hd2
  have hne' : q - β ^ (2 * ℓ) * q' ≠ 0 := sub_ne_zero.2 hne
  have hne'' : β ^ (2 * ℓ) * q' - q ≠ 0 := sub_ne_zero.2 (Ne.symm hne)
  refine ⟨?_, ?_⟩
  · rw [p2e_B_eq, eq_div_iff hne', hd1]
    ring
  · rw [p2e_E_eq, eq_div_iff hne'', hd2]
    ring

private lemma p2e_part4 {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {ℓ : ℕ} {g : ℕ ⊕ Fin ℓ → Ω → ℝ}
    (hg : IsStdGaussianFamily P g) {q q' : ℝ} (hq : 0 ≤ q) (heq : q = β ^ (2 * ℓ) * q') :
    pairedB P (emaXi₁ β ℓ g) (emaXi₂ β ℓ g) q q' =
        β ^ ℓ * derivWithin (Muon.DetEquiv.rW (Muon.emaW β)) (Ici 0) q ∧
    pairedE P (emaXi₁ β ℓ g) (emaXi₂ β ℓ g) q q' =
        β ^ (2 * ℓ) * (-derivWithin (Muon.DetEquiv.Fw (Muon.emaW β)) (Ici 0) q) := by
  have hW := p2e_W_profile hβ0 hβ1 hg
  have hR : profileR P (fun (j : ℕ) ω => Muon.emaW β j * g (Sum.inl j) ω) =
      Muon.DetEquiv.rW (Muon.emaW β) := by
    funext x
    unfold profileR Muon.DetEquiv.rW
    rw [congrFun (p2e_F_W hg) x]
  have hF := p2e_F_W (β := β) hg
  obtain ⟨hFc, hRc, hFa, hRa, hAnti, hF0, hR0, hFpos, hRd, hRpos, hFd, hid⟩ :=
    lem_app_vol_closed_profile_i hW
  have hq0 : q ∈ Ici (0 : ℝ) := hq
  have hRder : derivWithin (Muon.DetEquiv.rW (Muon.emaW β)) (Ici 0) q =
      profileRDeriv P (fun (j : ℕ) ω => Muon.emaW β j * g (Sum.inl j) ω) q := by
    rw [← hR]
    exact (hRd q hq0).derivWithin (uniqueDiffOn_Ici 0 q hq0)
  have hFder : derivWithin (Muon.DetEquiv.Fw (Muon.emaW β)) (Ici 0) q =
      -profileNegFDeriv P (fun (j : ℕ) ω => Muon.emaW β j * g (Sum.inl j) ω) q := by
    rw [← hF]
    rcases hq.eq_or_lt with h0 | hpos
    · subst h0
      have h4 : ∀ j : ℕ, Integrable (fun ω => (Muon.emaW β j * g (Sum.inl j) ω) ^ 4) P :=
        fun j => p2e_g4_int (A := ℕ ⊕ Fin ℓ) (g := g) hg.2.2 (fun _ => Muon.emaW β j) (Sum.inl j)
      have hs4 : Summable (fun j : ℕ => ∫ ω, (Muon.emaW β j * g (Sum.inl j) ω) ^ 4 ∂P) := by
        have hM : ∀ j : ℕ, ∫ ω, (Muon.emaW β j * g (Sum.inl j) ω) ^ 4 ∂P =
            Muon.emaW β j ^ 4 * ∫ x, x ^ 4 ∂(gaussianReal 0 1) := by
          intro j
          have h := (hg.2.2 (Sum.inl j)).integral_comp (f := fun x : ℝ => x ^ 4)
            (continuous_pow 4).aestronglyMeasurable
          simp only [Function.comp] at h
          rw [← h, ← integral_const_mul]
          refine integral_congr_ae (ae_of_all _ (fun ω => ?_))
          simp only
          ring
        simp_rw [hM]
        exact (p2e_w_summable hβ0 hβ1 (p := 4) (by norm_num)).mul_right _
      exact (p2e_F_hasDerivWithinAt_zero hW h4 hs4).derivWithin (uniqueDiffWithinAt_Ici 0)
    · exact ((hFd q hpos).1.hasDerivWithinAt).derivWithin (uniqueDiffOn_Ici 0 q hq0)
  rw [hRder, hFder]
  rw [p2e_B_eq, p2e_E_eq, ← heq]
  refine ⟨?_, ?_⟩
  · congr 1
    unfold profileRDeriv
    refine tsum_congr (fun j => integral_congr_ae (ae_of_all _ (fun ω => ?_)))
    simp only
    rw [← sq]
  · rw [neg_neg]
    congr 1
    unfold profileNegFDeriv
    refine tsum_congr (fun j => integral_congr_ae (ae_of_all _ (fun ω => ?_)))
    simp only
    rw [← sq]

private lemma p2e_cross (β : ℝ) (ℓ : ℕ) {g : ℕ ⊕ Fin ℓ → Ω → ℝ} (hg : IsStdGaussianFamily P g) :
    ∑' α, ∫ ω, emaXi₁ β ℓ g α ω * emaXi₂ β ℓ g α ω ∂P = Muon.sPow β 2 * β ^ ℓ := by
  rw [p2e_tsum_inl]
  · unfold Muon.sPow
    rw [← tsum_mul_right]
    refine tsum_congr (fun j => ?_)
    obtain ⟨h1, h2⟩ := p2e_gsq (hg.2.2 (Sum.inl j))
    simp only [emaXi₁, emaXi₂]
    have : ∀ ω, Muon.emaW β j * g (Sum.inl j) ω * (β ^ ℓ * Muon.emaW β j * g (Sum.inl j) ω) =
        (Muon.emaW β j ^ 2 * β ^ ℓ) * g (Sum.inl j) ω ^ 2 := fun ω => by ring
    simp_rw [this]
    rw [integral_const_mul, h2, mul_one]
  · intro i
    simp [emaXi₁]

end EmaHelpers

/-- `lem:app-vol-closed-profile`, snapshot `cr-2026-10-23`. Declaration of record for part (c) of `lem:app-vol-closed-profile`:
regularity of the two-point functions `b, e` of a paired profile, and the two Cauchy–Schwarz bounds.
The square-root bound on `e` is stated for `q₁, q₂ > 0` (see the module note on `-F'_ξ(0)`).

LaTeX (`sections/04-volatility/section.tex` l.1712–1738, verbatim):
```latex
\begin{lemma}[Profile functions]\label{lem:app-vol-closed-profile}
Let $\xi$ be a profile.
\begin{enumerate}[label=(\alph*)]
\item $F_\xi$ and $r_\xi$ are continuous on $[0,\infty)$ and real-analytic on
$(0,\infty)$. $F_\xi$ is nonincreasing with $0<F_\xi\le F_\xi(0)=\sum_\alpha\EE\xi_\alpha^2$, and
$r_\xi(0)=0$. For $q\ge0$,
\[
r_\xi'(q)=\sum_\alpha\EE\frac{\xi_\alpha^2}{(1+q\xi_\alpha^2)^2}>0,\qquad -F_\xi'(q)=\sum_\alpha\EE\frac{\xi_\alpha^4}{(1+q\xi_\alpha^2)^2}\in[0,\infty],
\]
the latter finite for $q>0$, and
\begin{equation}\label{eqn:app-vol-closed-b0e0}
r_\xi'(q)+q\,\big(-F_\xi'(q)\big)=F_\xi(q)\qquad(q>0).
\end{equation}
\item $r_\xi$ increases strictly to $n_\xi\defeq\sum_\alpha\Pr(\xi_\alpha\ne0)\in(0,\infty]$.
\item For a paired profile, $b$ and $e$ are continuous on $[0,\infty)^2$, real-analytic
in each variable on $(0,\infty)$ when the other is fixed, and
\[
0\le b(q_1,q_2)\le\min\Big(\sqrt{r_{\xi_1}'(q_1)\,r_{\xi_2}'(q_2)},\ \sum_\alpha\EE[\xi_{1,\alpha}\xi_{2,\alpha}]\Big),
\]
\[
0\le e(q_1,q_2)\le\sqrt{\big(-F_{\xi_1}'(q_1)\big)\big(-F_{\xi_2}'(q_2)\big)} .
\]
\item For the EMA paired profile at lag $\ell$, the divided-difference forms
\cref{eqn:app-vol-closed-divided} hold, and $0\le b_\ell\le\sw2\,\bmom^\ell$. At $\ell=0$
and $q=q'$ they read $b_0=r_{\bmom}'(q)$ and $e_0=-\Fw'(q)$.
\end{enumerate}
\end{lemma}
```
-/
theorem lem_app_vol_closed_profile_iii {P : Measure Ω} [IsProbabilityMeasure P]
    {ξ₁ ξ₂ : ι → Ω → ℝ} (hξ : def_app_vol_closed_profile_ii P ξ₁ ξ₂) :
    ContinuousOn (fun p : ℝ × ℝ => pairedB P ξ₁ ξ₂ p.1 p.2) (Ici 0 ×ˢ Ici 0) ∧
    ContinuousOn (fun p : ℝ × ℝ => pairedE P ξ₁ ξ₂ p.1 p.2) (Ici 0 ×ˢ Ici 0) ∧
    (∀ q₂ ∈ Ici (0 : ℝ), AnalyticOnNhd ℝ (fun q₁ => pairedB P ξ₁ ξ₂ q₁ q₂) (Ioi 0)) ∧
    (∀ q₂ ∈ Ici (0 : ℝ), AnalyticOnNhd ℝ (fun q₁ => pairedE P ξ₁ ξ₂ q₁ q₂) (Ioi 0)) ∧
    (∀ q₁ ∈ Ici (0 : ℝ), AnalyticOnNhd ℝ (fun q₂ => pairedB P ξ₁ ξ₂ q₁ q₂) (Ioi 0)) ∧
    (∀ q₁ ∈ Ici (0 : ℝ), AnalyticOnNhd ℝ (fun q₂ => pairedE P ξ₁ ξ₂ q₁ q₂) (Ioi 0)) ∧
    (∀ q₁ ∈ Ici (0 : ℝ), ∀ q₂ ∈ Ici (0 : ℝ),
      0 ≤ pairedB P ξ₁ ξ₂ q₁ q₂ ∧
      pairedB P ξ₁ ξ₂ q₁ q₂ ≤ min (Real.sqrt (profileRDeriv P ξ₁ q₁ * profileRDeriv P ξ₂ q₂))
        (∑' α, ∫ ω, ξ₁ α ω * ξ₂ α ω ∂P)) ∧
    (∀ q₁ ∈ Ioi (0 : ℝ), ∀ q₂ ∈ Ioi (0 : ℝ),
      0 ≤ pairedE P ξ₁ ξ₂ q₁ q₂ ∧
      pairedE P ξ₁ ξ₂ q₁ q₂ ≤
        Real.sqrt (profileNegFDeriv P ξ₁ q₁ * profileNegFDeriv P ξ₂ q₂)) := by
  refine ⟨p2_B_cont hξ, p2_E_cont hξ, fun q₂ hq₂ => p2_B_analytic hξ hq₂,
    fun q₂ hq₂ => p2_E_analytic hξ hq₂, fun q₁ hq₁ => ?_, fun q₁ hq₁ => ?_,
    fun q₁ hq₁ q₂ hq₂ => p2_B_bounds hξ hq₁ hq₂,
    fun q₁ hq₁ q₂ hq₂ => p2_E_bounds hξ hq₁ hq₂⟩
  · have := p2_B_analytic (p2_swap hξ) hq₁
    simpa only [p2_B_swap] using this
  · have := p2_E_analytic (p2_swap hξ) hq₁
    simpa only [p2_E_swap] using this

/-- `lem:app-vol-closed-profile`, snapshot `cr-2026-10-23`. Declaration of record for part (d) of `lem:app-vol-closed-profile`:
the EMA paired profile at lag `ℓ` has both marginals equal to `F_w` (`Muon.DetEquiv.Fw`), its two-point
functions are the divided differences of `r_w` and `F_w` (`eqn:app-vol-closed-divided`), with the
derivatives at coincident arguments, and `0 ≤ b_ℓ ≤ sw₂ β^ℓ`.

LaTeX (`sections/04-volatility/section.tex` l.1712–1738, verbatim):
```latex
\begin{lemma}[Profile functions]\label{lem:app-vol-closed-profile}
Let $\xi$ be a profile.
\begin{enumerate}[label=(\alph*)]
\item $F_\xi$ and $r_\xi$ are continuous on $[0,\infty)$ and real-analytic on
$(0,\infty)$. $F_\xi$ is nonincreasing with $0<F_\xi\le F_\xi(0)=\sum_\alpha\EE\xi_\alpha^2$, and
$r_\xi(0)=0$. For $q\ge0$,
\[
r_\xi'(q)=\sum_\alpha\EE\frac{\xi_\alpha^2}{(1+q\xi_\alpha^2)^2}>0,\qquad -F_\xi'(q)=\sum_\alpha\EE\frac{\xi_\alpha^4}{(1+q\xi_\alpha^2)^2}\in[0,\infty],
\]
the latter finite for $q>0$, and
\begin{equation}\label{eqn:app-vol-closed-b0e0}
r_\xi'(q)+q\,\big(-F_\xi'(q)\big)=F_\xi(q)\qquad(q>0).
\end{equation}
\item $r_\xi$ increases strictly to $n_\xi\defeq\sum_\alpha\Pr(\xi_\alpha\ne0)\in(0,\infty]$.
\item For a paired profile, $b$ and $e$ are continuous on $[0,\infty)^2$, real-analytic
in each variable on $(0,\infty)$ when the other is fixed, and
\[
0\le b(q_1,q_2)\le\min\Big(\sqrt{r_{\xi_1}'(q_1)\,r_{\xi_2}'(q_2)},\ \sum_\alpha\EE[\xi_{1,\alpha}\xi_{2,\alpha}]\Big),
\]
\[
0\le e(q_1,q_2)\le\sqrt{\big(-F_{\xi_1}'(q_1)\big)\big(-F_{\xi_2}'(q_2)\big)} .
\]
\item For the EMA paired profile at lag $\ell$, the divided-difference forms
\cref{eqn:app-vol-closed-divided} hold, and $0\le b_\ell\le\sw2\,\bmom^\ell$. At $\ell=0$
and $q=q'$ they read $b_0=r_{\bmom}'(q)$ and $e_0=-\Fw'(q)$.
\end{enumerate}
\end{lemma}
```
-/
theorem lem_app_vol_closed_profile_iv {P : Measure Ω} [IsProbabilityMeasure P] {β : ℝ}
    (hβ0 : 0 ≤ β) (hβ1 : β < 1) {ℓ : ℕ} {g : ℕ ⊕ Fin ℓ → Ω → ℝ}
    (hg : IsStdGaussianFamily P g) :
    profileF P (emaXi₁ β ℓ g) = Muon.DetEquiv.Fw (Muon.emaW β) ∧
    profileF P (emaXi₂ β ℓ g) = Muon.DetEquiv.Fw (Muon.emaW β) ∧
    (∀ q q' : ℝ, 0 ≤ q → 0 ≤ q' → q ≠ β ^ (2 * ℓ) * q' →
      pairedB P (emaXi₁ β ℓ g) (emaXi₂ β ℓ g) q q' =
          β ^ ℓ * (Muon.DetEquiv.rW (Muon.emaW β) q -
            Muon.DetEquiv.rW (Muon.emaW β) (β ^ (2 * ℓ) * q')) / (q - β ^ (2 * ℓ) * q') ∧
      pairedE P (emaXi₁ β ℓ g) (emaXi₂ β ℓ g) q q' =
          β ^ (2 * ℓ) * (Muon.DetEquiv.Fw (Muon.emaW β) q -
            Muon.DetEquiv.Fw (Muon.emaW β) (β ^ (2 * ℓ) * q')) /
            (β ^ (2 * ℓ) * q' - q)) ∧
    (∀ q q' : ℝ, 0 ≤ q → 0 ≤ q' → q = β ^ (2 * ℓ) * q' →
      pairedB P (emaXi₁ β ℓ g) (emaXi₂ β ℓ g) q q' =
          β ^ ℓ * derivWithin (Muon.DetEquiv.rW (Muon.emaW β)) (Ici 0) q ∧
      pairedE P (emaXi₁ β ℓ g) (emaXi₂ β ℓ g) q q' =
          β ^ (2 * ℓ) * (-derivWithin (Muon.DetEquiv.Fw (Muon.emaW β)) (Ici 0) q)) ∧
    (∀ q q' : ℝ, 0 ≤ q → 0 ≤ q' →
      0 ≤ pairedB P (emaXi₁ β ℓ g) (emaXi₂ β ℓ g) q q' ∧
      pairedB P (emaXi₁ β ℓ g) (emaXi₂ β ℓ g) q q' ≤ Muon.sPow β 2 * β ^ ℓ) ∧
    def_app_vol_closed_profile_ii P (emaXi₁ β ℓ g) (emaXi₂ β ℓ g) := by
  have hii := p2e_profile_ii hβ0 hβ1 hg
  refine ⟨p2e_F1 hg, p2e_F2 hg, fun q q' hq hq' hne => p2e_part3 hβ0 hβ1 hg hq hq' hne,
    fun q q' hq hq' heq => p2e_part4 hβ0 hβ1 hg hq heq, fun q q' hq hq' => ?_, hii⟩
  have h := (lem_app_vol_closed_profile_iii hii).2.2.2.2.2.2.1 q hq q' hq'
  rw [p2e_cross β ℓ hg] at h
  exact ⟨h.1, h.2.trans (min_le_right _ _)⟩

/-! ### Private helpers for `eqn:app-vol-closed-cutoff-masses` (task P-D.15.P1) -/

private lemma p1_emaW_nonneg {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) (j : ℕ) :
    0 ≤ Muon.emaW β j := by
  unfold Muon.emaW
  exact mul_nonneg (by linarith) (pow_nonneg hβ0 _)

private lemma p1_emaW_le_one {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) (j : ℕ) :
    Muon.emaW β j ≤ 1 := by
  unfold Muon.emaW
  have h1 : β ^ j ≤ 1 := pow_le_one₀ hβ0 hβ1.le
  have h2 : 0 ≤ β ^ j := pow_nonneg hβ0 _
  nlinarith

private lemma p1_emaW_partial (β : ℝ) (k : ℕ) :
    ∑ j ∈ Finset.range k, Muon.emaW β j = 1 - β ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, ih]
    unfold Muon.emaW
    ring

private lemma p1_varpi_nonneg {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) (ℓ l : ℕ) (α : ℤ) :
    0 ≤ treeVarpi β ℓ l α := by
  unfold treeVarpi
  split_ifs <;> first
    | exact p1_emaW_nonneg hβ0 hβ1 _
    | exact mul_nonneg (pow_nonneg hβ0 _) (p1_emaW_nonneg hβ0 hβ1 _)
    | exact le_rfl

private lemma p1_varpi_le_one {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) (ℓ l : ℕ) (α : ℤ) :
    treeVarpi β ℓ l α ≤ 1 := by
  have hb : β ^ ℓ ≤ 1 := pow_le_one₀ hβ0 hβ1.le
  unfold treeVarpi
  split_ifs <;> first
    | exact p1_emaW_le_one hβ0 hβ1 _
    | exact mul_le_one₀ hb (p1_emaW_nonneg hβ0 hβ1 _) (p1_emaW_le_one hβ0 hβ1 _)
    | exact zero_le_one

private lemma p1_sum_Icc_neg (J : ℕ) (f : ℤ → ℝ) :
    ∑ α ∈ Finset.Icc (-(J : ℤ)) 0, f α = ∑ j ∈ Finset.range (J + 1), f (-(j : ℤ)) := by
  apply Finset.sum_nbij' (fun α : ℤ => (-α).toNat) (fun j : ℕ => -(j : ℤ))
  · intro α hα; simp only [Finset.mem_Icc, Finset.mem_range] at hα ⊢; omega
  · intro j hj; simp only [Finset.mem_Icc, Finset.mem_range] at hj ⊢; omega
  · intro α hα; simp only [Finset.mem_Icc] at hα; try dsimp only
    omega
  · intro j hj; simp only [Finset.mem_range] at hj; try dsimp only
    omega
  · intro α hα; simp only [Finset.mem_Icc] at hα; try dsimp only
    congr 1
    omega

private lemma p1_sum_Icc_pos (ℓ : ℕ) (f : ℤ → ℝ) :
    ∑ α ∈ Finset.Icc (1 : ℤ) (ℓ : ℤ), f α = ∑ k ∈ Finset.range ℓ, f ((ℓ : ℤ) - (k : ℤ)) := by
  apply Finset.sum_nbij' (fun α : ℤ => ℓ - α.toNat) (fun k : ℕ => (ℓ : ℤ) - (k : ℤ))
  · intro α hα; simp only [Finset.mem_Icc, Finset.mem_range] at hα ⊢; omega
  · intro k hk; simp only [Finset.mem_Icc, Finset.mem_range] at hk ⊢; omega
  · intro α hα; simp only [Finset.mem_Icc] at hα; try dsimp only
    omega
  · intro k hk; simp only [Finset.mem_range] at hk; try dsimp only
    omega
  · intro α hα; simp only [Finset.mem_Icc] at hα; try dsimp only
    congr 1
    omega

private lemma p1_disj (J ℓ : ℕ) : Disjoint (Finset.Icc (-(J : ℤ)) 0) (Finset.Icc 1 (ℓ : ℤ)) := by
  rw [Finset.disjoint_left]
  intro α h1 h2
  simp only [Finset.mem_Icc] at h1 h2
  omega

private lemma p1_varpi_sum_le (β : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β < 1) (ℓ J : ℕ) (l : ℕ)
    (hl : l = 1 ∨ l = 2) :
    ∑ α ∈ cutoffLabels J ℓ, treeVarpi β ℓ l α ≤ 1 := by
  unfold cutoffLabels
  have hpart := p1_emaW_partial β (J + 1)
  have hβl : 0 ≤ β ^ ℓ := pow_nonneg hβ0 ℓ
  have hβJ : 0 ≤ β ^ (J + 1) := pow_nonneg hβ0 _
  have hβk := p1_emaW_partial β ℓ
  rw [Finset.sum_union (p1_disj J ℓ), p1_sum_Icc_neg, p1_sum_Icc_pos]
  rcases hl with rfl | rfl
  · have e1 : ∀ j ∈ Finset.range (J + 1),
        treeVarpi β ℓ 1 (-(j : ℤ)) = Muon.emaW β j := by
      intro j _
      unfold treeVarpi
      simp
    have e2 : ∀ k ∈ Finset.range ℓ, treeVarpi β ℓ 1 ((ℓ : ℤ) - (k : ℤ)) = 0 := by
      intro k hk
      simp only [Finset.mem_range] at hk
      have h : ¬ ((ℓ : ℤ) - (k : ℤ) ≤ 0) := by omega
      unfold treeVarpi
      simp [h]
    rw [Finset.sum_congr rfl e1, Finset.sum_congr rfl e2, Finset.sum_const_zero, add_zero, hpart]
    linarith
  · have e1 : ∀ j ∈ Finset.range (J + 1),
        treeVarpi β ℓ 2 (-(j : ℤ)) = β ^ ℓ * Muon.emaW β j := by
      intro j _
      unfold treeVarpi
      simp
    have e2 : ∀ k ∈ Finset.range ℓ, treeVarpi β ℓ 2 ((ℓ : ℤ) - (k : ℤ)) = Muon.emaW β k := by
      intro k hk
      simp only [Finset.mem_range] at hk
      have h : ¬ ((ℓ : ℤ) - (k : ℤ) ≤ 0) := by omega
      have hto : ((ℓ : ℤ) - (k : ℤ)).toNat = ℓ - k := by omega
      unfold treeVarpi
      rw [if_neg h, if_neg (by norm_num : ¬ (2 : ℕ) = 1), hto]
      congr 1
      omega
    rw [Finset.sum_congr rfl e1, Finset.sum_congr rfl e2, ← Finset.mul_sum, hpart, hβk]
    nlinarith [mul_nonneg hβl hβJ]

private lemma p1_cut_nonneg {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) (ℓ J l : ℕ) (α : ℤ) :
    0 ≤ cutoffVarpi β ℓ J l α := by
  unfold cutoffVarpi
  split_ifs
  · exact p1_varpi_nonneg hβ0 hβ1 ℓ l α
  · exact le_rfl

private lemma p1_gauss_sq_integral : ∫ x, x ^ 2 ∂(gaussianReal 0 1) = 1 := by
  have hL : MemLp (id : ℝ → ℝ) 2 (gaussianReal 0 1) := memLp_id_gaussianReal' (2 : ℝ≥0∞) (by simp)
  have h := variance_eq_sub hL
  rw [variance_id_gaussianReal] at h
  simp only [Pi.pow_apply, id] at h
  have hm : ∫ x, x ∂(gaussianReal 0 1) = 0 := integral_id_gaussianReal
  rw [hm] at h
  norm_num at h ⊢
  linarith

private lemma p1_term_le {P : Measure Ω} [IsProbabilityMeasure P] {g : Ω → ℝ}
    (hg : HasLaw g (gaussianReal 0 1) P) (R c : ℝ) :
    ∫ ω, (c * (if |g ω| ≤ R then g ω else 0)) ^ 2 ∂P ≤ c ^ 2 := by
  have hint : Integrable (fun ω => g ω ^ 2) P := by
    have hL : MemLp (id : ℝ → ℝ) 2 (gaussianReal 0 1) := memLp_id_gaussianReal' (2 : ℝ≥0∞) (by simp)
    have h2 : Integrable (fun x : ℝ => x ^ 2) (gaussianReal 0 1) := hL.integrable_sq
    exact hg.integrable_comp h2
  have hI : ∫ ω, g ω ^ 2 ∂P = 1 := by
    have h := hg.integral_comp (f := fun x : ℝ => x ^ 2) (continuous_pow 2).aestronglyMeasurable
    rw [p1_gauss_sq_integral] at h
    exact h
  have hle : ∀ ω, (c * (if |g ω| ≤ R then g ω else 0)) ^ 2 ≤ c ^ 2 * g ω ^ 2 := by
    intro ω
    rw [mul_pow]
    refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg c)
    split_ifs with h
    · exact le_rfl
    · nlinarith [sq_nonneg (g ω)]
  calc ∫ ω, (c * (if |g ω| ≤ R then g ω else 0)) ^ 2 ∂P
      ≤ ∫ ω, c ^ 2 * g ω ^ 2 ∂P :=
        integral_mono_of_nonneg (Eventually.of_forall fun ω => sq_nonneg _)
          (hint.const_mul _) (Eventually.of_forall hle)
    _ = c ^ 2 := by rw [integral_const_mul, hI, mul_one]

/-- `eqn:app-vol-closed-cutoff-masses`, snapshot `cr-2026-10-23`. Declaration of record for the cutoff-masses lemma: for
`l ∈ {1,2}` the cutoff coefficients bound the cutoff variables, `|ξ_{l,α}| ≤ ϖ_{l,α} R`, the sum
of `E ξ_{l,α}²` is at most `1`, and `F_{ξ_l}(0) ≤ 1`. The hypotheses are `0 ≤ β < 1` and `R > 0`.

LaTeX (`sections/04-volatility/section.tex` l.1706–1708, verbatim):
```latex
\begin{equation}\label{eqn:app-vol-closed-cutoff-masses}
\abs{\xi_{l,\alpha}}\le\varpi_{l,\alpha}R,\qquad \sum_\alpha\EE\xi_{l,\alpha}^2\le1,\qquad F_{\xi_l}(0)\le1 ,
\end{equation}
```
-/
theorem lem_app_vol_closed_cutoff_masses {P : Measure Ω} [IsProbabilityMeasure P] {β : ℝ}
    (hβ0 : 0 ≤ β) (hβ1 : β < 1) {ℓ J : ℕ} {R : ℝ} (hR : 0 < R) {g : ℤ → Ω → ℝ}
    (hg : IsStdGaussianFamily P g) {l : ℕ} (hl : l = 1 ∨ l = 2) :
    (∀ α ω, |cutoffXi β ℓ J R l g α ω| ≤ cutoffVarpi β ℓ J l α * R) ∧
    Summable (fun α => ∫ ω, cutoffXi β ℓ J R l g α ω ^ 2 ∂P) ∧
    ∑' α, ∫ ω, cutoffXi β ℓ J R l g α ω ^ 2 ∂P ≤ 1 ∧
    profileF P (cutoffXi β ℓ J R l g) 0 ≤ 1 := by
  have hzero : ∀ α ∉ cutoffLabels J ℓ, ∫ ω, cutoffXi β ℓ J R l g α ω ^ 2 ∂P = 0 := by
    intro α hα
    have hv : cutoffVarpi β ℓ J l α = 0 := by
      unfold cutoffVarpi
      rw [if_neg hα]
    have h0 : ∀ ω, cutoffXi β ℓ J R l g α ω ^ 2 = 0 := by
      intro ω
      simp [cutoffXi, hv]
    simp [h0]
  have hterm : ∀ α, ∫ ω, cutoffXi β ℓ J R l g α ω ^ 2 ∂P ≤ cutoffVarpi β ℓ J l α ^ 2 :=
    fun α => p1_term_le (hg.2.2 α) R _
  have hsumle : ∑ α ∈ cutoffLabels J ℓ, cutoffVarpi β ℓ J l α ≤ 1 := by
    have hcongr : ∀ α ∈ cutoffLabels J ℓ, cutoffVarpi β ℓ J l α = treeVarpi β ℓ l α := by
      intro α hα
      unfold cutoffVarpi
      rw [if_pos hα]
    rw [Finset.sum_congr rfl hcongr]
    exact p1_varpi_sum_le β hβ0 hβ1 ℓ J l hl
  have htsum : ∑' α, ∫ ω, cutoffXi β ℓ J R l g α ω ^ 2 ∂P ≤ 1 := by
    rw [tsum_eq_sum hzero]
    calc ∑ α ∈ cutoffLabels J ℓ, ∫ ω, cutoffXi β ℓ J R l g α ω ^ 2 ∂P
        ≤ ∑ α ∈ cutoffLabels J ℓ, cutoffVarpi β ℓ J l α ^ 2 :=
          Finset.sum_le_sum fun α _ => hterm α
      _ ≤ ∑ α ∈ cutoffLabels J ℓ, cutoffVarpi β ℓ J l α :=
          Finset.sum_le_sum fun α _ => by
            have h0 := p1_cut_nonneg hβ0 hβ1 ℓ J l α
            have h1 : cutoffVarpi β ℓ J l α ≤ 1 := by
              unfold cutoffVarpi
              split_ifs <;> first
                | exact p1_varpi_le_one hβ0 hβ1 ℓ l α
                | exact zero_le_one
            nlinarith [mul_nonneg h0 (sub_nonneg.2 h1)]
      _ ≤ 1 := hsumle
  refine ⟨fun α ω => ?_, summable_of_ne_finset_zero hzero, htsum, ?_⟩
  · have h0 := p1_cut_nonneg hβ0 hβ1 ℓ J l α
    simp only [cutoffXi]
    split_ifs with h
    · rw [abs_mul, abs_of_nonneg h0]
      exact mul_le_mul_of_nonneg_left h h0
    · simp only [mul_zero, abs_zero]
      exact mul_nonneg h0 hR.le
  · simp only [profileF, zero_mul, add_zero, div_one]
    exact htsum

private lemma p2_cut_le_one {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) (ℓ J l : ℕ) (α : ℤ) :
    cutoffVarpi β ℓ J l α ≤ 1 := by
  unfold cutoffVarpi
  split_ifs
  · exact p1_varpi_le_one hβ0 hβ1 ℓ l α
  · exact zero_le_one

private lemma p2_cut_meas {P : Measure Ω} {β : ℝ} {ℓ J : ℕ} {R : ℝ} {l : ℕ} {g : ℤ → Ω → ℝ}
    (hg : IsStdGaussianFamily P g) (α : ℤ) : Measurable (cutoffXi β ℓ J R l g α) := by
  unfold cutoffXi
  exact measurable_const.mul
    (Measurable.ite (measurableSet_le (hg.1 α).abs measurable_const) (hg.1 α) measurable_const)

private lemma p2_cut_sq_le {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {ℓ J : ℕ} {R : ℝ} (hR : 0 < R)
    (l : ℕ) (g : ℤ → Ω → ℝ) (α : ℤ) (ω : Ω) :
    cutoffXi β ℓ J R l g α ω ^ 2 ≤ R ^ 2 := by
  have h0 := p1_cut_nonneg hβ0 hβ1 ℓ J l α
  have h1 := p2_cut_le_one hβ0 hβ1 ℓ J l α
  have : |cutoffXi β ℓ J R l g α ω| ≤ R := by
    simp only [cutoffXi]
    split_ifs with h
    · rw [abs_mul, abs_of_nonneg h0]
      nlinarith [abs_nonneg (g α ω)]
    · simp [hR.le]
  exact sq_le_sq' (by linarith [(abs_le.1 this).1]) (abs_le.1 this).2

private lemma p2_cut_pos {P : Measure Ω} [IsProbabilityMeasure P] {β : ℝ} {ℓ J : ℕ} {R : ℝ}
    (hR : 0 < R) {g : ℤ → Ω → ℝ} (hg : IsStdGaussianFamily P g) {l : ℕ} {α : ℤ}
    (hα : 0 < cutoffVarpi β ℓ J l α) : 0 < P {ω | cutoffXi β ℓ J R l g α ω ≠ 0} := by
  have hS : MeasurableSet (Ioc (0 : ℝ) R) := measurableSet_Ioc
  have h1 : 0 < gaussianReal 0 1 (Ioc (0 : ℝ) R) := by
    rw [pos_iff_ne_zero]
    intro h0
    have := gaussianReal_absolutelyContinuous' 0 (one_ne_zero) h0
    simp [Real.volume_Ioc] at this
    linarith
  have h2 : P ((g α) ⁻¹' (Ioc (0 : ℝ) R)) = gaussianReal 0 1 (Ioc (0 : ℝ) R) := by
    rw [← (hg.2.2 α).map_eq, Measure.map_apply (hg.1 α) hS]
  refine lt_of_lt_of_le (h2 ▸ h1) (measure_mono ?_)
  intro ω hω
  simp only [mem_preimage, mem_Ioc] at hω
  simp only [mem_setOf_eq, cutoffXi]
  rw [if_pos (by rw [abs_of_pos hω.1]; exact hω.2)]
  exact mul_ne_zero hα.ne' hω.1.ne'

private lemma p2_cut_label {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) (ℓ J : ℕ) :
    (0 < cutoffVarpi β ℓ J 1 0) ∧ ∃ α : ℤ, 0 < cutoffVarpi β ℓ J 2 α := by
  have hb : 0 < 1 - β := by linarith
  have h0 : (0 : ℤ) ∈ cutoffLabels J ℓ := by
    simp [cutoffLabels]
  refine ⟨?_, ?_⟩
  · unfold cutoffVarpi
    rw [if_pos h0]
    unfold treeVarpi
    simp [Muon.emaW, hb]
  · rcases Nat.eq_zero_or_pos ℓ with hℓ | hℓ
    · refine ⟨0, ?_⟩
      unfold cutoffVarpi
      rw [if_pos h0]
      unfold treeVarpi
      simp [Muon.emaW, hb, hℓ]
    · refine ⟨(ℓ : ℤ), ?_⟩
      have hm : (ℓ : ℤ) ∈ cutoffLabels J ℓ := by
        simp only [cutoffLabels, Finset.mem_union, Finset.mem_Icc]
        right; omega
      unfold cutoffVarpi
      rw [if_pos hm]
      unfold treeVarpi
      rw [if_neg (by omega), if_neg (by norm_num)]
      simp [Muon.emaW, hb]

private lemma p2_cut_profile {P : Measure Ω} [IsProbabilityMeasure P] {β : ℝ}
    (hβ0 : 0 ≤ β) (hβ1 : β < 1) {ℓ J : ℕ} {R : ℝ} (hR : 0 < R) {g : ℤ → Ω → ℝ}
    (hg : IsStdGaussianFamily P g) {l : ℕ} (hl : l = 1 ∨ l = 2)
    (hex : ∃ α : ℤ, 0 < cutoffVarpi β ℓ J l α) :
    def_app_vol_closed_profile P (cutoffXi β ℓ J R l g) := by
  refine ⟨p2_cut_meas hg, fun α => ?_, (lem_app_vol_closed_cutoff_masses hβ0 hβ1 hR hg hl).2.1, ?_⟩
  · refine Integrable.mono' (integrable_const (R ^ 2)) ((p2_cut_meas hg α).pow_const 2).aestronglyMeasurable
      (ae_of_all _ (fun ω => ?_))
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact p2_cut_sq_le hβ0 hβ1 hR l g α ω
  · obtain ⟨α, hα⟩ := hex
    exact ⟨α, p2_cut_pos hR hg hα⟩

/-- `def:app-vol-closed-profile-paragraph`, snapshot `cr-2026-10-23`. Declaration of record for the cutoff paired profile
(the constructor of the paragraph after `def:app-vol-closed-profile`): with `0 ≤ β < 1`, `R > 0` and
`g` a family of independent standard Gaussians, `(ξ_{1,α}, ξ_{2,α})` is a paired profile.

LaTeX (`sections/04-volatility/section.tex` l.1693–1710, verbatim):
```latex
Two paired profiles are used. The \emph{EMA paired profile at lag $\ell$} has the
labels $j\ge0$, with $(\xi_{1,j},\xi_{2,j})=(\emaw jg_j,\bmom^\ell\emaw jg_j)$, and the
labels $m\in\{1,\dots,\ell\}$, with $(\xi_{1,m},\xi_{2,m})=(0,\emaw{\ell-m}g_m)$; all
$g_\alpha$ are independent standard Gaussians. The first labels are the batches
shared by the two buffers and the second the fresh batches seen only by the
later buffer. Since $\bmom^\ell\emaw j=\emaw{j+\ell}$, both marginals have the scalar
function $\Fw$ of \cref{eqn:app-de-JFL}, and at $(q_1,q_2)=(q,q')$ the two-point
functions are $b_\ell$ and $e_\ell$ of \cref{eqn:app-vol-closed-objects}. The
\emph{cutoff paired profile} at $(\ell,J,R)$ has the labels $\mathcal A$ of
\cref{sec:app-vol-tree} and $\xi_{l,\alpha}\defeq\varpi_{l,\alpha}\tilde g_\alpha$ for $l=1,2$, with
the coefficients \cref{eqn:app-vol-tree-coefficients} and one variable
$\tilde g_\alpha=g_\alpha\mathbf 1_{\abs{g_\alpha}\le R}$ per label, shared by the two buffers.
Since $\varpi_{l,\alpha}\le1$ and $\sum_\alpha\varpi_{l,\alpha}\le1$,
\begin{equation}\label{eqn:app-vol-closed-cutoff-masses}
\abs{\xi_{l,\alpha}}\le\varpi_{l,\alpha}R,\qquad \sum_\alpha\EE\xi_{l,\alpha}^2\le1,\qquad F_{\xi_l}(0)\le1 ,
\end{equation}
and the latent value of a class $V$ in \cref{def:app-vol-tree} is
$\sum_\alpha\EE\prod_{r\in S_V}\xi_{l_r,\alpha}$.
```
-/
theorem lem_app_vol_closed_cutoff_paired {P : Measure Ω} [IsProbabilityMeasure P] {β : ℝ}
    (hβ0 : 0 ≤ β) (hβ1 : β < 1) {ℓ J : ℕ} {R : ℝ} (hR : 0 < R) {g : ℤ → Ω → ℝ}
    (hg : IsStdGaussianFamily P g) :
    def_app_vol_closed_profile_ii P (cutoffXi β ℓ J R 1 g) (cutoffXi β ℓ J R 2 g) := by
  obtain ⟨h1, h2⟩ := p2_cut_label hβ0 hβ1 ℓ J
  have hbd : ∀ α ω, cutoffXi β ℓ J R 1 g α ω ^ 2 * cutoffXi β ℓ J R 2 g α ω ^ 2 ≤ R ^ 2 * R ^ 2 :=
    fun α ω => mul_le_mul (p2_cut_sq_le hβ0 hβ1 hR 1 g α ω) (p2_cut_sq_le hβ0 hβ1 hR 2 g α ω)
      (sq_nonneg _) (sq_nonneg _)
  refine ⟨p2_cut_profile hβ0 hβ1 hR hg (Or.inl rfl) ⟨0, h1⟩,
    p2_cut_profile hβ0 hβ1 hR hg (Or.inr rfl) h2, fun α ω => ?_, fun α => ?_, ?_⟩
  · simp only [cutoffXi]
    have a1 := p1_cut_nonneg hβ0 hβ1 ℓ J 1 α
    have a2 := p1_cut_nonneg hβ0 hβ1 ℓ J 2 α
    have : 0 ≤ (cutoffVarpi β ℓ J 1 α * cutoffVarpi β ℓ J 2 α) *
        ((if |g α ω| ≤ R then g α ω else 0) * (if |g α ω| ≤ R then g α ω else 0)) := by
      apply mul_nonneg (mul_nonneg a1 a2)
      exact mul_self_nonneg _
    nlinarith [this]
  · refine Integrable.mono' (integrable_const (R ^ 2 * R ^ 2))
      (((p2_cut_meas hg α).pow_const 2).mul ((p2_cut_meas hg α).pow_const 2)).aestronglyMeasurable
      (ae_of_all _ (fun ω => ?_))
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))]
    exact hbd α ω
  · have hz : ∀ α ∉ cutoffLabels J ℓ, ∫ ω, cutoffXi β ℓ J R 1 g α ω ^ 2 * cutoffXi β ℓ J R 2 g α ω ^ 2 ∂P = 0 := by
      intro α hα
      have hv : cutoffVarpi β ℓ J 1 α = 0 := by unfold cutoffVarpi; rw [if_neg hα]
      simp [cutoffXi, hv]
    exact summable_of_ne_finset_zero hz

private lemma p3_admissible {P : Measure Ω} [IsProbabilityMeasure P]
    {ξ : ι → Ω → ℝ} (hξ : def_app_vol_closed_profile P ξ) :
    Muon.DetEquiv.AdmissibleWeightFn (profileF P ξ) := by
  have h := lem_app_vol_closed_profile_i hξ
  exact ⟨h.1, fun q hq => h.2.2.2.2.2.2.2.1 q hq,
    fun q hq => h.2.2.2.2.1 (by simp) hq hq,
    (lem_app_vol_closed_profile_ii hξ).1, by simp⟩

private lemma p3_eigen_le_trace {d : ℕ} {S : Matrix (Fin d) (Fin d) ℝ}
    (hS : S.PosSemidef) (i : Fin d) : hS.isHermitian.eigenvalues i ≤ S.trace := by
  rw [hS.isHermitian.trace_eq_sum_eigenvalues]
  exact Finset.single_le_sum (fun j _ => hS.eigenvalues_nonneg j) (Finset.mem_univ i)

private lemma p3_discrete_support {d : ℕ} (e : Fin d → ℝ) (k : ℝ≥0∞) (Cs : ℝ)
    (he : ∀ i, e i ∈ Icc 0 Cs) :
    (k • ∑ i, Measure.dirac (e i)) (Icc 0 Cs)ᶜ = 0 := by
  simp [Measure.smul_apply, Measure.finset_sum_apply, Measure.dirac_apply', he]

private lemma p3_class {ν ν' : FiniteMeasure ℝ} {Cs : ℝ}
    (hν : (ν : Measure ℝ) (Icc 0 Cs)ᶜ = 0)
    (hν' : (ν' : Measure ℝ) (Icc 0 Cs)ᶜ = 0) :
    ∃ γ : ℝ, 0 < γ ∧ (ν, ν') ∈ Muon.DetEquiv.classK Cs γ := by
  let γ := (ν : Measure ℝ).real univ + (ν' : Measure ℝ).real univ + 1
  have h1 : 0 ≤ (ν : Measure ℝ).real univ := measureReal_nonneg
  have h2 : 0 ≤ (ν' : Measure ℝ).real univ := measureReal_nonneg
  refine ⟨γ, by dsimp [γ]; linarith, ?_, hν, ?_, hν'⟩
  · refine (measure_mono (subset_univ _)).trans ?_
    rw [← ENNReal.ofReal_toReal (measure_ne_top (ν : Measure ℝ) univ)]
    apply ENNReal.ofReal_le_ofReal
    change (ν : Measure ℝ).real univ ≤ γ
    dsimp [γ]
    linarith
  · refine (measure_mono (subset_univ _)).trans ?_
    rw [← ENNReal.ofReal_toReal (measure_ne_top (ν' : Measure ℝ) univ)]
    apply ENNReal.ofReal_le_ofReal
    change (ν' : Measure ℝ).real univ ≤ γ
    dsimp [γ]
    linarith

private lemma p3_exists_unique {m n B : ℕ} (hB : 0 < B) {P : Measure Ω}
    [IsProbabilityMeasure P] {ξ : ι → Ω → ℝ} (hξ : def_app_vol_closed_profile P ξ)
    {s : ℝ} (hs : 0 < s) (C : Muon.Covariances m n) :
    ∃! x, IsBranchPoint (profileF P ξ) C B s x := by
  have hB0 : (B : ℝ≥0∞) ≠ 0 := by exact_mod_cast hB.ne'
  haveI : IsFiniteMeasure (Muon.nuOut C B) :=
    Measure.smul_finite _ (ENNReal.inv_ne_top.2 hB0)
  haveI : IsFiniteMeasure (Muon.nuIn C B) :=
    Measure.smul_finite _ (ENNReal.inv_ne_top.2 hB0)
  let ν : FiniteMeasure ℝ := ⟨Muon.nuOut C B, inferInstance⟩
  let ν' : FiniteMeasure ℝ := ⟨Muon.nuIn C B, inferInstance⟩
  let Cs := C.Sout.trace + C.Sin.trace + 1
  have ho := C.psdOut.trace_nonneg
  have hi := C.psdIn.trace_nonneg
  have hCs : 0 < Cs := by dsimp [Cs]; linarith
  have hν : (ν : Measure ℝ) (Icc 0 Cs)ᶜ = 0 := by
    apply p3_discrete_support
    intro i
    exact ⟨C.psdOut.eigenvalues_nonneg i,
      (p3_eigen_le_trace C.psdOut i).trans (by dsimp [Cs]; linarith)⟩
  have hν' : (ν' : Measure ℝ) (Icc 0 Cs)ᶜ = 0 := by
    apply p3_discrete_support
    intro i
    exact ⟨C.psdIn.eigenvalues_nonneg i,
      (p3_eigen_le_trace C.psdIn i).trans (by dsimp [Cs]; linarith)⟩
  obtain ⟨γ, hγ, hK⟩ := p3_class hν hν'
  have heq : ∀ x, IsBranchPoint (profileF P ξ) C B s x ↔
      Muon.DetEquiv.IsBranchSol (profileF P ξ) ν ν' s x := by
    rintro ⟨σ, σ', a, c⟩
    simp only [IsBranchPoint, Muon.DetEquiv.IsBranchSol]
    change (_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _) ↔
      (0 ≤ σ ∧ 0 ≤ σ' ∧ 0 ≤ a ∧ 0 ≤ c ∧
        σ = ∫ t, t / (a * t + s) ∂(Muon.nuOut C B) ∧
        σ' = ∫ t, t / (c * t + s) ∂(Muon.nuIn C B) ∧
        a = s * σ' * profileF P ξ (s * σ * σ') ∧
        c = s * σ * profileF P ξ (s * σ * σ'))
    constructor <;> rintro ⟨hσ0, hσ'0, ha0, hc0, hσ, hσ', ha, hc⟩
    · refine ⟨hσ0, hσ'0, ha0, hc0, ?_, ?_, ha, hc⟩
      · rw [Muon.DetEquiv.def_app_de_branch_trace C hB hs ha0 |>.1, add_comm]
        exact hσ
      · rw [Muon.DetEquiv.def_app_de_branch_trace C hB hs hc0 |>.2, add_comm]
        exact hσ'
    · refine ⟨hσ0, hσ'0, ha0, hc0, ?_, ?_, ha, hc⟩
      · rw [Muon.DetEquiv.def_app_de_branch_trace C hB hs ha0 |>.1, add_comm] at hσ
        exact hσ
      · rw [Muon.DetEquiv.def_app_de_branch_trace C hB hs hc0 |>.2, add_comm] at hσ'
        exact hσ'
  obtain ⟨x, hx, hu⟩ :=
    (Muon.DetEquiv.thm_app_de_branch_i (p3_admissible hξ) hCs hγ ν ν' hK s hs).1
  exact ⟨x, (heq x).2 hx, fun y hy => hu y ((heq y).1 hy)⟩

private lemma p3_trace_resolvent {d : ℕ} {S : Matrix (Fin d) (Fin d) ℝ}
    (hS : S.PosSemidef) {s a : ℝ} (hs : 0 < s) (ha : 0 ≤ a) :
    (S * (s • (1 : Matrix (Fin d) (Fin d) ℝ) + a • S)⁻¹).trace =
      ∑ i, hS.isHermitian.eigenvalues i / (a * hS.isHermitian.eigenvalues i + s) := by
  let C : Muon.Covariances d d := ⟨S, S, hS, hS⟩
  have h := (Muon.DetEquiv.def_app_de_branch_trace C (B := 1) (by decide) hs ha).1
  unfold Muon.nuOut at h
  rw [integral_smul_measure,
    integral_finsetSum_measure (fun i _ => integrable_dirac (by simp))] at h
  simpa [C, add_comm] using h.symm

private lemma p3_trace_resolvent_pos {d : ℕ} {S : Matrix (Fin d) (Fin d) ℝ}
    (hS : S.PosSemidef) (hS0 : S ≠ 0) {s a : ℝ} (hs : 0 < s) (ha : 0 ≤ a) :
    0 < (S * (s • (1 : Matrix (Fin d) (Fin d) ℝ) + a • S)⁻¹).trace := by
  rw [p3_trace_resolvent hS hs ha]
  have he : ∃ i, hS.isHermitian.eigenvalues i ≠ 0 := by
    by_contra! h
    exact hS0 (hS.isHermitian.eigenvalues_eq_zero_iff.1 (funext h))
  obtain ⟨i, hi⟩ := he
  have hd : ∀ j, 0 < a * hS.isHermitian.eigenvalues j + s := by
    intro j
    exact add_pos_of_nonneg_of_pos (mul_nonneg ha (hS.eigenvalues_nonneg j)) hs
  exact Finset.sum_pos' (fun j _ => div_nonneg (hS.eigenvalues_nonneg j) (hd j).le)
    ⟨i, Finset.mem_univ i, div_pos (lt_of_le_of_ne (hS.eigenvalues_nonneg i) hi.symm) (hd i)⟩

private lemma p3_trace_resolvent_le {d : ℕ} {S : Matrix (Fin d) (Fin d) ℝ}
    (hS : S.PosSemidef) {s a : ℝ} (hs : 0 < s) (ha : 0 ≤ a) :
    (S * (s • (1 : Matrix (Fin d) (Fin d) ℝ) + a • S)⁻¹).trace ≤ S.trace / s := by
  rw [p3_trace_resolvent hS hs ha, hS.isHermitian.trace_eq_sum_eigenvalues,
    Finset.sum_div]
  apply Finset.sum_le_sum
  intro i _
  exact div_le_div_of_nonneg_left (hS.eigenvalues_nonneg i) hs
    (le_add_of_nonneg_left (mul_nonneg ha (hS.eigenvalues_nonneg i)))

private lemma p3_trace_resolvent_rank {d : ℕ} {S : Matrix (Fin d) (Fin d) ℝ}
    (hS : S.PosSemidef) (hS0 : S ≠ 0) {s a : ℝ} (hs : 0 < s) (ha : 0 ≤ a) :
    a * (S * (s • (1 : Matrix (Fin d) (Fin d) ℝ) + a • S)⁻¹).trace < S.rank := by
  classical
  rw [p3_trace_resolvent hS hs ha, Finset.mul_sum,
    hS.isHermitian.rank_eq_card_non_zero_eigs]
  have he : ∃ i, hS.isHermitian.eigenvalues i ≠ 0 := by
    by_contra! h
    exact hS0 (hS.isHermitian.eigenvalues_eq_zero_iff.1 (funext h))
  have hz : ∑ i : {i // ¬ hS.isHermitian.eigenvalues i ≠ 0},
      a * (hS.isHermitian.eigenvalues i / (a * hS.isHermitian.eigenvalues i + s)) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    simp [not_ne_iff.mp i.property]
  rw [← Fintype.sum_subtype_add_sum_subtype (fun i => hS.isHermitian.eigenvalues i ≠ 0),
    hz, add_zero]
  have hlt : ∀ i : {i // hS.isHermitian.eigenvalues i ≠ 0},
      a * (hS.isHermitian.eigenvalues i / (a * hS.isHermitian.eigenvalues i + s)) < 1 := by
    intro i
    rw [← mul_div_assoc]
    exact (div_lt_one (add_pos_of_nonneg_of_pos
      (mul_nonneg ha (hS.eigenvalues_nonneg i)) hs)).2 (by linarith)
  obtain ⟨i, hi⟩ := he
  calc
    _ < ∑ _j : {j // hS.isHermitian.eigenvalues j ≠ 0}, (1 : ℝ) :=
      Finset.sum_lt_sum (fun j _ => (hlt j).le) ⟨⟨i, hi⟩, Finset.mem_univ _, hlt _⟩
    _ = _ := by simp

private lemma p3_resolvent_cross_strict {d : ℕ} {S : Matrix (Fin d) (Fin d) ℝ}
    (hS : S.PosSemidef) (hS0 : S ≠ 0) {s t a b : ℝ}
    (hs : 0 < s) (ht : 0 < t) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hc : b * s < a * t) :
    b * (S * (t • (1 : Matrix (Fin d) (Fin d) ℝ) + b • S)⁻¹).trace <
      a * (S * (s • (1 : Matrix (Fin d) (Fin d) ℝ) + a • S)⁻¹).trace := by
  rw [p3_trace_resolvent hS ht hb, p3_trace_resolvent hS hs ha,
    Finset.mul_sum, Finset.mul_sum]
  have hd : ∀ i, 0 < a * hS.isHermitian.eigenvalues i + s ∧
      0 < b * hS.isHermitian.eigenvalues i + t := by
    intro i
    exact ⟨add_pos_of_nonneg_of_pos (mul_nonneg ha (hS.eigenvalues_nonneg i)) hs,
      add_pos_of_nonneg_of_pos (mul_nonneg hb (hS.eigenvalues_nonneg i)) ht⟩
  have he : ∃ i, hS.isHermitian.eigenvalues i ≠ 0 := by
    by_contra! h
    exact hS0 (hS.isHermitian.eigenvalues_eq_zero_iff.1 (funext h))
  apply Finset.sum_lt_sum
  · intro i _
    rw [← mul_div_assoc, ← mul_div_assoc, div_le_div_iff₀ (hd i).2 (hd i).1]
    nlinarith [mul_nonneg (sub_nonneg.2 hc.le) (hS.eigenvalues_nonneg i)]
  · obtain ⟨i, hi⟩ := he
    refine ⟨i, Finset.mem_univ _, ?_⟩
    rw [← mul_div_assoc, ← mul_div_assoc, div_lt_div_iff₀ (hd i).2 (hd i).1]
    have hp : 0 < hS.isHermitian.eigenvalues i :=
      lt_of_le_of_ne (hS.eigenvalues_nonneg i) hi.symm
    nlinarith [mul_pos (sub_pos.2 hc) hp]

private lemma p3_resolvent_cross_le {d : ℕ} {S : Matrix (Fin d) (Fin d) ℝ}
    (hS : S.PosSemidef) {s t a b : ℝ}
    (hs : 0 < s) (ht : 0 < t) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hc : a * t ≤ b * s) :
    t * (S * (t • (1 : Matrix (Fin d) (Fin d) ℝ) + b • S)⁻¹).trace ≤
      s * (S * (s • (1 : Matrix (Fin d) (Fin d) ℝ) + a • S)⁻¹).trace := by
  rw [p3_trace_resolvent hS ht hb, p3_trace_resolvent hS hs ha,
    Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  have hEig := hS.eigenvalues_nonneg i
  have hd1 : 0 < a * hS.isHermitian.eigenvalues i + s :=
    add_pos_of_nonneg_of_pos (mul_nonneg ha hEig) hs
  have hd2 : 0 < b * hS.isHermitian.eigenvalues i + t :=
    add_pos_of_nonneg_of_pos (mul_nonneg hb hEig) ht
  rw [← mul_div_assoc, ← mul_div_assoc, div_le_div_iff₀ hd2 hd1]
  nlinarith [mul_nonneg (sub_nonneg.2 hc) (sq_nonneg (hS.isHermitian.eigenvalues i))]

private lemma p3_branchPt_spec {m n B : ℕ} (hB : 0 < B) {P : Measure Ω}
    [IsProbabilityMeasure P] {ξ : ι → Ω → ℝ} (hξ : def_app_vol_closed_profile P ξ)
    {s : ℝ} (hs : 0 < s) (C : Muon.Covariances m n) :
    IsBranchPoint (profileF P ξ) C B s (branchPt (profileF P ξ) C B s) := by
  have h := (p3_exists_unique hB hξ hs C).exists
  unfold branchPt
  rw [dif_pos h]
  exact h.choose_spec

private lemma p3_q_strictAnti {m n B : ℕ} (hB : 0 < B) {P : Measure Ω}
    [IsProbabilityMeasure P] {ξ : ι → Ω → ℝ} (hξ : def_app_vol_closed_profile P ξ)
    (C : Muon.Covariances m n) (hout : C.Sout ≠ 0) (hin : C.Sin ≠ 0) :
    StrictAntiOn (fun s => s * (branchPt (profileF P ξ) C B s).1 *
      (branchPt (profileF P ξ) C B s).2.1) (Ioi 0) := by
  intro s hs t ht hst
  have hs0 : 0 < s := hs
  have ht0 : 0 < t := ht
  rcases hsx : branchPt (profileF P ξ) C B s with ⟨σ, σ', a, c⟩
  rcases hty : branchPt (profileF P ξ) C B t with ⟨τ, τ', b, d⟩
  have hx := p3_branchPt_spec hB hξ hs0 C
  have hy := p3_branchPt_spec hB hξ ht0 C
  rw [hsx] at hx
  rw [hty] at hy
  obtain ⟨hσ0, hσ'0, ha0, hc0, hσ, hσ', ha, hc⟩ := hx
  obtain ⟨hτ0, hτ'0, hb0, hd0, hτ, hτ', hb, hd⟩ := hy
  dsimp only at hσ0 hσ'0 ha0 hc0 hσ hσ' ha hc hτ0 hτ'0 hb0 hd0 hτ hτ' hb hd ⊢
  have hBr : (0 : ℝ) < B := by exact_mod_cast hB
  have hσp : 0 < σ := by
    rw [hσ]
    exact mul_pos (inv_pos.2 hBr) (p3_trace_resolvent_pos C.psdOut hout hs0 ha0)
  have hσ'p : 0 < σ' := by
    rw [hσ']
    exact mul_pos (inv_pos.2 hBr) (p3_trace_resolvent_pos C.psdIn hin hs0 hc0)
  have hτp : 0 < τ := by
    rw [hτ]
    exact mul_pos (inv_pos.2 hBr) (p3_trace_resolvent_pos C.psdOut hout ht0 hb0)
  have hτ'p : 0 < τ' := by
    rw [hτ']
    exact mul_pos (inv_pos.2 hBr) (p3_trace_resolvent_pos C.psdIn hin ht0 hd0)
  rw [hsx, hty]
  dsimp only
  by_contra! hq
  have hR := (p3_admissible hξ).r_strictMonoOn.monotoneOn
    (show 0 ≤ s * σ * σ' by positivity)
    (show 0 ≤ t * τ * τ' by positivity) hq
  have hH : a * σ ≤ b * τ := by
    rw [ha, hb]
    nlinarith only [hR]
  have hH' : c * σ' ≤ d * τ' := by
    rw [hc, hd]
    nlinarith only [hR]
  have hab : a * t ≤ b * s := by
    by_contra! hcon
    have hlt := mul_lt_mul_of_pos_left
      (p3_resolvent_cross_strict C.psdOut hout hs0 ht0 ha0 hb0 hcon) (inv_pos.2 hBr)
    rw [hσ, hτ] at hH
    nlinarith only [hH, hlt]
  have hcd : c * t ≤ d * s := by
    by_contra! hcon
    have hlt := mul_lt_mul_of_pos_left
      (p3_resolvent_cross_strict C.psdIn hin hs0 ht0 hc0 hd0 hcon) (inv_pos.2 hBr)
    rw [hσ', hτ'] at hH'
    nlinarith only [hH', hlt]
  have hG : t * τ ≤ s * σ := by
    have hh := mul_le_mul_of_nonneg_left
      (p3_resolvent_cross_le C.psdOut hs0 ht0 ha0 hb0 hab) (inv_nonneg.2 hBr.le)
    rw [hσ, hτ]
    nlinarith only [hh]
  have hG' : t * τ' ≤ s * σ' := by
    have hh := mul_le_mul_of_nonneg_left
      (p3_resolvent_cross_le C.psdIn hs0 ht0 hc0 hd0 hcd) (inv_nonneg.2 hBr.le)
    rw [hσ', hτ']
    nlinarith only [hh]
  have hp : (t * τ) * (t * τ') ≤ (s * σ) * (s * σ') :=
    mul_le_mul hG hG' (by positivity) (by positivity)
  have hqpos : 0 < t * τ * τ' := by positivity
  have h1 := mul_le_mul_of_nonneg_left hq hs0.le
  have h2 := mul_lt_mul_of_pos_right hst hqpos
  nlinarith only [hp, h1, h2]

private lemma p3_trace_scalar_inv {d : ℕ} (S : Matrix (Fin d) (Fin d) ℝ)
    {s : ℝ} (hs : 0 < s) :
    (S * (s • (1 : Matrix (Fin d) (Fin d) ℝ))⁻¹).trace = S.trace / s := by
  haveI : Invertible s := invertibleOfNonzero hs.ne'
  rw [Matrix.inv_smul (A := (1 : Matrix (Fin d) (Fin d) ℝ)) s (by simp),
    invOf_eq_inv, inv_one, Matrix.mul_smul,
    Matrix.mul_one, Matrix.trace_smul]
  simp only [smul_eq_mul, div_eq_mul_inv]
  ring

/-- `lem:app-vol-closed-branch`, snapshot `cr-2026-10-23`. Declaration of record for part (i) of `lem:app-vol-closed-branch`:
if `Σ_out = 0` the unique branch point at `s` is `σ = s₁ = 0`, `σ̃ = B⁻¹ Tr Σ_in / s`,
`s̃₁ = B⁻¹ Tr Σ_in F(0)`, with `q = 0`; the case `Σ_in = 0` is symmetric.

LaTeX (`sections/04-volatility/section.tex` l.1794–1827, verbatim):
```latex
\begin{lemma}[Branch of a profile]\label{lem:app-vol-closed-branch}
Let $\xi$ be a profile and $s>0$. A \emph{branch point} of $\xi$ at $s$ is a
quadruple $(\sigma,\tilde\sigma,\tilde s_1,s_1)\in[0,\infty)^4$ with
\begin{equation}\label{eqn:app-vol-closed-branch}
\begin{gathered}
\sigma=\frac1B\Tr\Sigmaout(s\Id+\tilde s_1\Sigmaout)^{-1},\qquad
\tilde\sigma=\frac1B\Tr\Sigmain(s\Id+s_1\Sigmain)^{-1},\\
\tilde s_1=s\tilde\sigma F_\xi(q),\qquad s_1=s\sigma F_\xi(q),
\end{gathered}
\end{equation}
where $q\defeq s\sigma\tilde\sigma$.
\begin{enumerate}[label=(\roman*)]
\item If $\Sigmaout=0$, the unique branch point at $s$ is $\sigma=s_1=0$,
$\tilde\sigma=B^{-1}\Tr\Sigmain/s$, $\tilde s_1=B^{-1}\Tr\Sigmain\,F_\xi(0)$, with $q=0$. The
case $\Sigmain=0$ is symmetric.
\item If $\Sigmaout\ne0$ and $\Sigmain\ne0$, then \cref{eqn:app-vol-closed-branch} has
exactly one solution in $[0,\infty)^4$. It lies in $(0,\infty)^4$ and in the box
\[
\sigma\le\frac{\Tr\Sigmaout}{Bs},\qquad \tilde\sigma\le\frac{\Tr\Sigmain}{Bs},\qquad
\tilde s_1\le\frac{\Tr\Sigmain}B\,F_\xi(0),\qquad s_1\le\frac{\Tr\Sigmaout}B\,F_\xi(0),
\]
and $r_\xi(q)=\tilde s_1\sigma=s_1\tilde\sigma<\min(\operatorname{rank}\Sigmaout,\operatorname{rank}\Sigmain)/B\le\gamma_\star$.
\item In case (ii), $s\mapsto(\sigma,\tilde\sigma,\tilde s_1,s_1,q)(s)$ is real-analytic on
$(0,\infty)$, and $q$ is strictly decreasing in $s$.
\item (Stability.) Let $\xi^{(n)}$ be profiles with
$\sup_{q\ge0}\abs{F_{\xi^{(n)}}(q)-F_\xi(q)}\to0$ and $\sup_nF_{\xi^{(n)}}(0)<\infty$. Then for
each $s>0$ the branch points of $\xi^{(n)}$ at $s$ converge to the branch point of
$\xi$ at $s$.
\end{enumerate}
For the EMA weights, \cref{eqn:app-vol-closed-branch} is the system
\cref{eqn:app-de-system} at $z=-s$ for the spectral measures of
\cref{eqn:app-setup-spectral-measures}, and its branch point is the solution of
\cref{thm:app-de-branch}.
\end{lemma}
```
-/
theorem lem_app_vol_closed_branch_i {m n B : ℕ} (hB : 0 < B) {P : Measure Ω} [IsProbabilityMeasure P]
    {ξ : ι → Ω → ℝ} (hξ : def_app_vol_closed_profile P ξ) {s : ℝ} (hs : 0 < s)
    (C : Muon.Covariances m n) :
    (C.Sout = 0 →
      IsBranchPoint (profileF P ξ) C B s
          (0, (B : ℝ)⁻¹ * C.Sin.trace / s, (B : ℝ)⁻¹ * C.Sin.trace * profileF P ξ 0, 0) ∧
      ∀ x, IsBranchPoint (profileF P ξ) C B s x →
          x = (0, (B : ℝ)⁻¹ * C.Sin.trace / s, (B : ℝ)⁻¹ * C.Sin.trace * profileF P ξ 0, 0)) ∧
    (C.Sin = 0 →
      IsBranchPoint (profileF P ξ) C B s
          ((B : ℝ)⁻¹ * C.Sout.trace / s, 0, 0, (B : ℝ)⁻¹ * C.Sout.trace * profileF P ξ 0) ∧
      ∀ x, IsBranchPoint (profileF P ξ) C B s x →
          x = ((B : ℝ)⁻¹ * C.Sout.trace / s, 0, 0, (B : ℝ)⁻¹ * C.Sout.trace * profileF P ξ 0)) := by
  have hF : 0 ≤ profileF P ξ 0 :=
    ((lem_app_vol_closed_profile_i hξ).2.2.2.2.2.2.2.1 0 (by simp)).le
  have hBo : 0 ≤ (B : ℝ)⁻¹ * C.Sout.trace :=
    mul_nonneg (by positivity) C.psdOut.trace_nonneg
  have hBi : 0 ≤ (B : ℝ)⁻¹ * C.Sin.trace :=
    mul_nonneg (by positivity) C.psdIn.trace_nonneg
  constructor
  · intro hout
    constructor
    · refine ⟨le_rfl, div_nonneg hBi hs.le, mul_nonneg hBi hF, le_rfl, ?_, ?_, ?_, ?_⟩
      · simp [hout]
      · simp only [zero_smul, add_zero, p3_trace_scalar_inv _ hs]
        ring
      · simp only [mul_zero, zero_mul]
        field_simp
      · simp
    · rintro ⟨σ, σ', a, c⟩ ⟨hσ0, hσ'0, ha0, hc0, hσ, hσ', ha, hc⟩
      have hσz : σ = 0 := by simpa [hout] using hσ
      clear hσ
      subst σ
      have hcz : c = 0 := by simpa using hc
      clear hc
      subst c
      have hσ'e : σ' = (B : ℝ)⁻¹ * C.Sin.trace / s := by
        simpa only [zero_smul, add_zero, p3_trace_scalar_inv _ hs, mul_div_assoc] using hσ'
      clear hσ'
      subst σ'
      have hae : a = (B : ℝ)⁻¹ * C.Sin.trace * profileF P ξ 0 := by
        simp only [mul_zero, zero_mul] at ha
        rw [ha]
        field_simp
      clear ha
      subst a
      rfl
  · intro hin
    constructor
    · refine ⟨div_nonneg hBo hs.le, le_rfl, le_rfl, mul_nonneg hBo hF, ?_, ?_, ?_, ?_⟩
      · simp only [zero_smul, add_zero, p3_trace_scalar_inv _ hs]
        ring
      · simp [hin]
      · simp
      · simp only [mul_zero]
        field_simp
    · rintro ⟨σ, σ', a, c⟩ ⟨hσ0, hσ'0, ha0, hc0, hσ, hσ', ha, hc⟩
      have hσ'z : σ' = 0 := by simpa [hin] using hσ'
      clear hσ'
      subst σ'
      have haz : a = 0 := by simpa using ha
      clear ha
      subst a
      have hσe : σ = (B : ℝ)⁻¹ * C.Sout.trace / s := by
        simpa only [zero_smul, add_zero, p3_trace_scalar_inv _ hs, mul_div_assoc] using hσ
      clear hσ
      subst σ
      have hce : c = (B : ℝ)⁻¹ * C.Sout.trace * profileF P ξ 0 := by
        simp only [mul_zero] at hc
        rw [hc]
        field_simp
      clear hc
      subst c
      rfl

/-- `lem:app-vol-closed-branch`, snapshot `cr-2026-10-23`. Declaration of record for part (ii) of `lem:app-vol-closed-branch`:
if `Σ_out ≠ 0` and `Σ_in ≠ 0` there is exactly one branch point; it lies in `(0,∞)⁴` and in the box
of the source, and `r_ξ(q) = s̃₁ σ = s₁ σ̃ < min(rank Σ_out, rank Σ_in)/B ≤ γ⋆`, where the size
condition is `max(N_out, N_in) ≤ γ⋆ B`.

LaTeX (`sections/04-volatility/section.tex` l.1794–1827, verbatim):
```latex
\begin{lemma}[Branch of a profile]\label{lem:app-vol-closed-branch}
Let $\xi$ be a profile and $s>0$. A \emph{branch point} of $\xi$ at $s$ is a
quadruple $(\sigma,\tilde\sigma,\tilde s_1,s_1)\in[0,\infty)^4$ with
\begin{equation}\label{eqn:app-vol-closed-branch}
\begin{gathered}
\sigma=\frac1B\Tr\Sigmaout(s\Id+\tilde s_1\Sigmaout)^{-1},\qquad
\tilde\sigma=\frac1B\Tr\Sigmain(s\Id+s_1\Sigmain)^{-1},\\
\tilde s_1=s\tilde\sigma F_\xi(q),\qquad s_1=s\sigma F_\xi(q),
\end{gathered}
\end{equation}
where $q\defeq s\sigma\tilde\sigma$.
\begin{enumerate}[label=(\roman*)]
\item If $\Sigmaout=0$, the unique branch point at $s$ is $\sigma=s_1=0$,
$\tilde\sigma=B^{-1}\Tr\Sigmain/s$, $\tilde s_1=B^{-1}\Tr\Sigmain\,F_\xi(0)$, with $q=0$. The
case $\Sigmain=0$ is symmetric.
\item If $\Sigmaout\ne0$ and $\Sigmain\ne0$, then \cref{eqn:app-vol-closed-branch} has
exactly one solution in $[0,\infty)^4$. It lies in $(0,\infty)^4$ and in the box
\[
\sigma\le\frac{\Tr\Sigmaout}{Bs},\qquad \tilde\sigma\le\frac{\Tr\Sigmain}{Bs},\qquad
\tilde s_1\le\frac{\Tr\Sigmain}B\,F_\xi(0),\qquad s_1\le\frac{\Tr\Sigmaout}B\,F_\xi(0),
\]
and $r_\xi(q)=\tilde s_1\sigma=s_1\tilde\sigma<\min(\operatorname{rank}\Sigmaout,\operatorname{rank}\Sigmain)/B\le\gamma_\star$.
\item In case (ii), $s\mapsto(\sigma,\tilde\sigma,\tilde s_1,s_1,q)(s)$ is real-analytic on
$(0,\infty)$, and $q$ is strictly decreasing in $s$.
\item (Stability.) Let $\xi^{(n)}$ be profiles with
$\sup_{q\ge0}\abs{F_{\xi^{(n)}}(q)-F_\xi(q)}\to0$ and $\sup_nF_{\xi^{(n)}}(0)<\infty$. Then for
each $s>0$ the branch points of $\xi^{(n)}$ at $s$ converge to the branch point of
$\xi$ at $s$.
\end{enumerate}
For the EMA weights, \cref{eqn:app-vol-closed-branch} is the system
\cref{eqn:app-de-system} at $z=-s$ for the spectral measures of
\cref{eqn:app-setup-spectral-measures}, and its branch point is the solution of
\cref{thm:app-de-branch}.
\end{lemma}
```
-/
theorem lem_app_vol_closed_branch_ii {m n B : ℕ} (hB : 0 < B) {P : Measure Ω}
    [IsProbabilityMeasure P] {ξ : ι → Ω → ℝ} (hξ : def_app_vol_closed_profile P ξ) {s : ℝ}
    (hs : 0 < s) (C : Muon.Covariances m n) (hout : C.Sout ≠ 0) (hin : C.Sin ≠ 0)
    (γ : ℝ) (hγ : (max m n : ℝ) ≤ γ * B) :
    (∃! x, IsBranchPoint (profileF P ξ) C B s x) ∧
    ∀ x, IsBranchPoint (profileF P ξ) C B s x →
      (0 < x.1 ∧ 0 < x.2.1 ∧ 0 < x.2.2.1 ∧ 0 < x.2.2.2) ∧
      x.1 ≤ C.Sout.trace / (B * s) ∧ x.2.1 ≤ C.Sin.trace / (B * s) ∧
      x.2.2.1 ≤ C.Sin.trace / B * profileF P ξ 0 ∧
      x.2.2.2 ≤ C.Sout.trace / B * profileF P ξ 0 ∧
      profileR P ξ (s * x.1 * x.2.1) = x.2.2.1 * x.1 ∧
      x.2.2.1 * x.1 = x.2.2.2 * x.2.1 ∧
      x.2.2.1 * x.1 < (min C.Sout.rank C.Sin.rank : ℝ) / B ∧
      (min C.Sout.rank C.Sin.rank : ℝ) / B ≤ γ := by
  refine ⟨p3_exists_unique hB hξ hs C, ?_⟩
  rintro ⟨σ, σ', a, c⟩ ⟨hσ0, hσ'0, ha0, hc0, hσ, hσ', ha, hc⟩
  dsimp only at hσ0 hσ'0 ha0 hc0 hσ hσ' ha hc ⊢
  have hBr : (0 : ℝ) < B := by exact_mod_cast hB
  have hσp : 0 < σ := by
    rw [hσ]
    exact mul_pos (inv_pos.2 hBr) (p3_trace_resolvent_pos C.psdOut hout hs ha0)
  have hσ'p : 0 < σ' := by
    rw [hσ']
    exact mul_pos (inv_pos.2 hBr) (p3_trace_resolvent_pos C.psdIn hin hs hc0)
  have hq : 0 < s * σ * σ' := by positivity
  have hF := (p3_admissible hξ).pos _ hq.le
  have hap : 0 < a := by rw [ha]; positivity
  have hcp : 0 < c := by rw [hc]; positivity
  have hσb : σ ≤ C.Sout.trace / (B * s) := by
    calc σ ≤ (B : ℝ)⁻¹ * (C.Sout.trace / s) := by
          rw [hσ]
          exact mul_le_mul_of_nonneg_left (p3_trace_resolvent_le C.psdOut hs ha0)
            (inv_nonneg.2 hBr.le)
      _ = _ := by field_simp
  have hσ'b : σ' ≤ C.Sin.trace / (B * s) := by
    calc σ' ≤ (B : ℝ)⁻¹ * (C.Sin.trace / s) := by
          rw [hσ']
          exact mul_le_mul_of_nonneg_left (p3_trace_resolvent_le C.psdIn hs hc0)
            (inv_nonneg.2 hBr.le)
      _ = _ := by field_simp
  have hF0 : 0 ≤ profileF P ξ 0 := ((p3_admissible hξ).pos 0 le_rfl).le
  have hFle := (p3_admissible hξ).le_zero _ hq.le
  have hr : profileR P ξ (s * σ * σ') = a * σ := by rw [profileR, ha]; ring
  have hac : a * σ = c * σ' := by rw [ha, hc]; ring
  have hro : a * σ < (C.Sout.rank : ℝ) / B := by
    calc a * σ = (B : ℝ)⁻¹ *
          (a * (C.Sout * (s • 1 + a • C.Sout)⁻¹).trace) := by rw [hσ]; ring
      _ < (B : ℝ)⁻¹ * C.Sout.rank := mul_lt_mul_of_pos_left
        (p3_trace_resolvent_rank C.psdOut hout hs ha0) (inv_pos.2 hBr)
      _ = _ := by ring
  have hri : a * σ < (C.Sin.rank : ℝ) / B := by
    calc a * σ = (B : ℝ)⁻¹ *
          (c * (C.Sin * (s • 1 + c • C.Sin)⁻¹).trace) := by rw [hac, hσ']; ring
      _ < (B : ℝ)⁻¹ * C.Sin.rank := mul_lt_mul_of_pos_left
        (p3_trace_resolvent_rank C.psdIn hin hs hc0) (inv_pos.2 hBr)
      _ = _ := by ring
  refine ⟨⟨hσp, hσ'p, hap, hcp⟩, hσb, hσ'b, ?_, ?_, hr, hac, ?_, ?_⟩
  · rw [ha]
    calc s * σ' * profileF P ξ (s * σ * σ') ≤ s * σ' * profileF P ξ 0 :=
          mul_le_mul_of_nonneg_left hFle (by positivity)
      _ ≤ s * (C.Sin.trace / (B * s)) * profileF P ξ 0 :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hσ'b hs.le) hF0
      _ = _ := by field_simp
  · rw [hc]
    calc s * σ * profileF P ξ (s * σ * σ') ≤ s * σ * profileF P ξ 0 :=
          mul_le_mul_of_nonneg_left hFle (by positivity)
      _ ≤ s * (C.Sout.trace / (B * s)) * profileF P ξ 0 :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hσb hs.le) hF0
      _ = _ := by field_simp
  · rw [← min_div_div_right hBr.le]
    exact lt_min hro hri
  · apply (div_le_iff₀ hBr).2
    have ho : (C.Sout.rank : ℝ) ≤ m := by exact_mod_cast C.Sout.rank_le_width
    have hi : (C.Sin.rank : ℝ) ≤ n := by exact_mod_cast C.Sin.rank_le_width
    calc (min C.Sout.rank C.Sin.rank : ℝ) ≤ (C.Sout.rank : ℝ) := by
          exact_mod_cast min_le_left C.Sout.rank C.Sin.rank
      _ ≤ m := ho
      _ ≤ (max m n : ℝ) := by exact_mod_cast le_max_left m n
      _ ≤ γ * B := hγ

private lemma p3_analytic_inverse {f : ℝ → ℝ} {x d : ℝ}
    (ha : AnalyticAt ℝ f x) (hd : HasDerivAt f d x) (hne : d ≠ 0) :
    ∃ A : ℝ → ℝ, AnalyticAt ℝ A (f x) ∧ HasDerivAt A d⁻¹ (f x) ∧
      A (f x) = x ∧ ∀ᶠ y in 𝓝 (f x), f (A y) = y := by
  have hne' : deriv f x ≠ 0 := by rw [hd.deriv]; exact hne
  let A := ha.hasStrictDerivAt.localInverse f (deriv f x) x hne'
  refine ⟨A, ha.analyticAt_localInverse hne', ?_, ?_, ?_⟩
  · simpa only [hd.deriv] using
      (ha.hasStrictDerivAt.to_localInverse hne').hasDerivAt
  · exact HasStrictFDerivAt.localInverse_apply_image ..
  · exact ha.hasStrictDerivAt.eventually_right_inverse hne'

private lemma p3_spectral_chart {d B : ℕ} (hB : 0 < B) (e : Fin d → ℝ)
    (he : ∀ i, 0 ≤ e i) (hp : ∃ i, 0 < e i) {x : ℝ} (hx : 0 < x) :
    let H := fun t : ℝ => (B : ℝ)⁻¹ * ∑ i, t * e i / (1 + t * e i)
    ∃ (A : ℝ → ℝ) (D : ℝ), AnalyticAt ℝ A (H x) ∧ HasDerivAt A D (H x) ∧
      A (H x) = x ∧ 0 < D ∧ x ≤ H x * D ∧
      ∀ᶠ y in 𝓝 (H x), H (A y) = y := by
  dsimp only
  let H := fun t : ℝ => (B : ℝ)⁻¹ * ∑ i, t * e i / (1 + t * e i)
  let D := (B : ℝ)⁻¹ * ∑ i, e i / (1 + x * e i) ^ 2
  have hBr : (0 : ℝ) < B := by exact_mod_cast hB
  have hden : ∀ i, 0 < 1 + x * e i := fun i =>
    add_pos_of_pos_of_nonneg zero_lt_one (mul_nonneg hx.le (he i))
  have ha : AnalyticAt ℝ H x := by
    have ht : ∀ i, AnalyticAt ℝ (fun t : ℝ => t * e i / (1 + t * e i)) x := by
      intro i
      have hi : AnalyticAt ℝ (fun t : ℝ => t * e i) x :=
        analyticAt_id.mul analyticAt_const
      exact hi.div (analyticAt_const.add hi) (hden i).ne'
    have hh : AnalyticAt ℝ (fun t : ℝ => ∑ i, t * e i / (1 + t * e i)) x := by
      convert Finset.analyticAt_sum Finset.univ (fun i _ => ht i) using 1
      ext t
      simp
    exact analyticAt_const.mul hh
  have hd : HasDerivAt H D x := by
    have ht : ∀ i, HasDerivAt (fun t : ℝ => t * e i / (1 + t * e i))
        (e i / (1 + x * e i) ^ 2) x := by
      intro i
      convert (((hasDerivAt_id x).mul_const (e i)).div
        ((hasDerivAt_const x 1).add ((hasDerivAt_id x).mul_const (e i)))
        (hden i).ne') using 1 <;> (try rfl)
      dsimp only [id, Pi.add_apply, Pi.div_apply]
      congr 1
      ring
    exact (HasDerivAt.fun_sum (fun i (_ : i ∈ Finset.univ) => ht i)).const_mul _
  have hD : 0 < D := by
    apply mul_pos (inv_pos.2 hBr)
    obtain ⟨i, hi⟩ := hp
    exact Finset.sum_pos' (fun j _ => div_nonneg (he j) (sq_nonneg _))
      ⟨i, Finset.mem_univ _, div_pos hi (sq_pos_of_pos (hden i))⟩
  have hbound : x * D ≤ H x := by
    dsimp [D, H]
    rw [mul_left_comm, Finset.mul_sum]
    apply mul_le_mul_of_nonneg_left _ (inv_nonneg.2 hBr.le)
    apply Finset.sum_le_sum
    intro i _
    rw [← mul_div_assoc, div_le_div_iff₀ (sq_pos_of_pos (hden i)) (hden i)]
    have hxe : 0 ≤ x * e i := mul_nonneg hx.le (he i)
    nlinarith [sq_nonneg (x * e i)]
  obtain ⟨A, hAa, hAd, hAx, hAi⟩ := p3_analytic_inverse ha hd hD.ne'
  refine ⟨A, D⁻¹, hAa, hAd, hAx, inv_pos.2 hD, ?_, hAi⟩
  exact (le_div_iff₀ hD).2 hbound

private lemma p3_trace_scaled {d B : ℕ} {S : Matrix (Fin d) (Fin d) ℝ}
    (hS : S.PosSemidef) {s x : ℝ} (hs : 0 < s) (hx : 0 < x) :
    (B : ℝ)⁻¹ * (S * (s • 1 + (s * x) • S)⁻¹).trace =
      ((B : ℝ)⁻¹ * ∑ i, x * hS.isHermitian.eigenvalues i /
        (1 + x * hS.isHermitian.eigenvalues i)) / (s * x) := by
  rw [p3_trace_resolvent hS hs (mul_nonneg hs.le hx.le), mul_div_assoc,
    Finset.sum_div]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  have hd : 0 < 1 + x * hS.isHermitian.eigenvalues i :=
    add_pos_of_pos_of_nonneg zero_lt_one (mul_nonneg hx.le (hS.eigenvalues_nonneg i))
  have hd' : 0 < s * x * hS.isHermitian.eigenvalues i + s :=
    add_pos_of_nonneg_of_pos
      (mul_nonneg (mul_nonneg hs.le hx.le) (hS.eigenvalues_nonneg i)) hs
  field_simp
  ring

private lemma p3_scalar_deriv_neg {r A D : ℝ → ℝ} {q dr da dd : ℝ}
    (hq : 0 < q) (hr : 0 < r q) (ha : 0 < A (r q)) (hd : 0 < D (r q))
    (hdr : HasDerivAt r dr q) (hda : HasDerivAt A da (r q))
    (hdd : HasDerivAt D dd (r q)) (hdr0 : 0 ≤ dr)
    (hba : A (r q) ≤ r q * da) (hbd : D (r q) ≤ r q * dd) :
    deriv (fun t => (r t / A (r t)) * (r t / D (r t)) / t) q < 0 := by
  have hu := hdr.div (hda.comp q hdr) ha.ne'
  have hv := hdr.div (hdd.comp q hdr) hd.ne'
  have hu0 : (dr * A (r q) - r q * (da * dr)) / A (r q) ^ 2 ≤ 0 := by
    apply div_nonpos_of_nonpos_of_nonneg _ (sq_nonneg _)
    nlinarith [mul_le_mul_of_nonneg_right hba hdr0]
  have hv0 : (dr * D (r q) - r q * (dd * dr)) / D (r q) ^ 2 ≤ 0 := by
    apply div_nonpos_of_nonpos_of_nonneg _ (sq_nonneg _)
    nlinarith [mul_le_mul_of_nonneg_right hbd hdr0]
  have hU : 0 < r q / A (r q) := div_pos hr ha
  have hV : 0 < r q / D (r q) := div_pos hr hd
  have hsum : (dr * A (r q) - r q * (da * dr)) / A (r q) ^ 2 *
      (r q / D (r q)) + (r q / A (r q)) *
      ((dr * D (r q) - r q * (dd * dr)) / D (r q) ^ 2) ≤ 0 :=
    add_nonpos (mul_nonpos_of_nonpos_of_nonneg hu0 hV.le)
      (mul_nonpos_of_nonneg_of_nonpos hU.le hv0)
  have hz := (hu.mul hv).div (hasDerivAt_id q) hq.ne'
  change HasDerivAt (fun t => (r t / A (r t)) * (r t / D (r t)) / t) _ q at hz
  rw [hz.deriv]
  dsimp only [Function.comp_apply, Pi.div_apply, Pi.mul_apply, id]
  apply div_neg_of_neg_of_pos _ (sq_pos_of_pos hq)
  nlinarith [mul_nonpos_of_nonpos_of_nonneg hsum hq.le, mul_pos hU hV]

private lemma p3_scalar_converse {m n B : ℕ} {P : Measure Ω}
    [IsProbabilityMeasure P] {ξ : ι → Ω → ℝ} (hξ : def_app_vol_closed_profile P ξ)
    (C : Muon.Covariances m n) {t u v : ℝ} (ht : 0 < t) (hu : 0 < u) (hv : 0 < v)
    (ho : (B : ℝ)⁻¹ * ∑ i, u * C.psdOut.isHermitian.eigenvalues i /
      (1 + u * C.psdOut.isHermitian.eigenvalues i) = profileR P ξ t)
    (hi : (B : ℝ)⁻¹ * ∑ i, v * C.psdIn.isHermitian.eigenvalues i /
      (1 + v * C.psdIn.isHermitian.eigenvalues i) = profileR P ξ t) :
    let z := (profileR P ξ t / u) * (profileR P ξ t / v) / t
    IsBranchPoint (profileF P ξ) C B z
      (profileR P ξ t / (z * u), profileR P ξ t / (z * v), z * u, z * v) := by
  let R := profileR P ξ t
  let z := (R / u) * (R / v) / t
  change IsBranchPoint (profileF P ξ) C B z (R / (z * u), R / (z * v), z * u, z * v)
  have hF := (p3_admissible hξ).pos t ht.le
  have hR : 0 < R := mul_pos ht hF
  have hz : 0 < z := div_pos (mul_pos (div_pos hR hu) (div_pos hR hv)) ht
  have hqt : z * (R / (z * u)) * (R / (z * v)) = t := by
    dsimp [z]
    field_simp
  have hzu : z * u = z * (R / (z * v)) * profileF P ξ t := by
    dsimp [z, R, profileR]
    field_simp
  have hzv : z * v = z * (R / (z * u)) * profileF P ξ t := by
    dsimp [z, R, profileR]
    field_simp
  refine ⟨(div_pos hR (mul_pos hz hu)).le, (div_pos hR (mul_pos hz hv)).le,
    (mul_pos hz hu).le, (mul_pos hz hv).le, ?_, ?_, ?_, ?_⟩
  · rw [p3_trace_scaled C.psdOut hz hu, ho]
  · rw [p3_trace_scaled C.psdIn hz hv, hi]
  · rw [hqt]
    exact hzu
  · rw [hqt]
    exact hzv

/-- `lem:app-vol-closed-branch`, snapshot `cr-2026-10-23`. Declaration of record for part (iii) of `lem:app-vol-closed-branch`:
in the case `Σ_out, Σ_in ≠ 0`, `s ↦ (σ, σ̃, s̃₁, s₁)(s)` is real-analytic on `(0,∞)` and
`q(s) = s σ(s) σ̃(s)` is strictly decreasing.

LaTeX (`sections/04-volatility/section.tex` l.1794–1827, verbatim):
```latex
\begin{lemma}[Branch of a profile]\label{lem:app-vol-closed-branch}
Let $\xi$ be a profile and $s>0$. A \emph{branch point} of $\xi$ at $s$ is a
quadruple $(\sigma,\tilde\sigma,\tilde s_1,s_1)\in[0,\infty)^4$ with
\begin{equation}\label{eqn:app-vol-closed-branch}
\begin{gathered}
\sigma=\frac1B\Tr\Sigmaout(s\Id+\tilde s_1\Sigmaout)^{-1},\qquad
\tilde\sigma=\frac1B\Tr\Sigmain(s\Id+s_1\Sigmain)^{-1},\\
\tilde s_1=s\tilde\sigma F_\xi(q),\qquad s_1=s\sigma F_\xi(q),
\end{gathered}
\end{equation}
where $q\defeq s\sigma\tilde\sigma$.
\begin{enumerate}[label=(\roman*)]
\item If $\Sigmaout=0$, the unique branch point at $s$ is $\sigma=s_1=0$,
$\tilde\sigma=B^{-1}\Tr\Sigmain/s$, $\tilde s_1=B^{-1}\Tr\Sigmain\,F_\xi(0)$, with $q=0$. The
case $\Sigmain=0$ is symmetric.
\item If $\Sigmaout\ne0$ and $\Sigmain\ne0$, then \cref{eqn:app-vol-closed-branch} has
exactly one solution in $[0,\infty)^4$. It lies in $(0,\infty)^4$ and in the box
\[
\sigma\le\frac{\Tr\Sigmaout}{Bs},\qquad \tilde\sigma\le\frac{\Tr\Sigmain}{Bs},\qquad
\tilde s_1\le\frac{\Tr\Sigmain}B\,F_\xi(0),\qquad s_1\le\frac{\Tr\Sigmaout}B\,F_\xi(0),
\]
and $r_\xi(q)=\tilde s_1\sigma=s_1\tilde\sigma<\min(\operatorname{rank}\Sigmaout,\operatorname{rank}\Sigmain)/B\le\gamma_\star$.
\item In case (ii), $s\mapsto(\sigma,\tilde\sigma,\tilde s_1,s_1,q)(s)$ is real-analytic on
$(0,\infty)$, and $q$ is strictly decreasing in $s$.
\item (Stability.) Let $\xi^{(n)}$ be profiles with
$\sup_{q\ge0}\abs{F_{\xi^{(n)}}(q)-F_\xi(q)}\to0$ and $\sup_nF_{\xi^{(n)}}(0)<\infty$. Then for
each $s>0$ the branch points of $\xi^{(n)}$ at $s$ converge to the branch point of
$\xi$ at $s$.
\end{enumerate}
For the EMA weights, \cref{eqn:app-vol-closed-branch} is the system
\cref{eqn:app-de-system} at $z=-s$ for the spectral measures of
\cref{eqn:app-setup-spectral-measures}, and its branch point is the solution of
\cref{thm:app-de-branch}.
\end{lemma}
```
-/
theorem lem_app_vol_closed_branch_iii {m n B : ℕ} (hB : 0 < B) {P : Measure Ω}
    [IsProbabilityMeasure P] {ξ : ι → Ω → ℝ} (hξ : def_app_vol_closed_profile P ξ)
    (C : Muon.Covariances m n) (hout : C.Sout ≠ 0) (hin : C.Sin ≠ 0) :
    AnalyticOnNhd ℝ (fun s => branchPt (profileF P ξ) C B s) (Ioi 0) ∧
    StrictAntiOn (fun s => s * (branchPt (profileF P ξ) C B s).1 *
      (branchPt (profileF P ξ) C B s).2.1) (Ioi 0) := by
  refine ⟨?_, p3_q_strictAnti hB hξ C hout hin⟩
  intro s hs
  have hs0 : 0 < s := hs
  rcases hpt : branchPt (profileF P ξ) C B s with ⟨σ, τ, a, c⟩
  have hspec := p3_branchPt_spec hB hξ hs0 C
  rw [hpt] at hspec
  obtain ⟨hσ0, hτ0, ha0, hc0, hσ, hτ, ha, hc⟩ := hspec
  have hBr : (0 : ℝ) < B := by exact_mod_cast hB
  have hσp : 0 < σ := by
    rw [hσ]
    exact mul_pos (inv_pos.2 hBr) (p3_trace_resolvent_pos C.psdOut hout hs0 ha0)
  have hτp : 0 < τ := by
    rw [hτ]
    exact mul_pos (inv_pos.2 hBr) (p3_trace_resolvent_pos C.psdIn hin hs0 hc0)
  let q := s * σ * τ
  let r := profileR P ξ
  have hq : 0 < q := by dsimp [q]; positivity
  have hF := (p3_admissible hξ).pos q hq.le
  have hap : 0 < a := by rw [ha]; exact mul_pos (mul_pos hs0 hτp) hF
  have hcp : 0 < c := by rw [hc]; exact mul_pos (mul_pos hs0 hσp) hF
  have hro : r q = a * σ := by dsimp [r, profileR, q]; rw [ha]; ring
  have hri : r q = c * τ := by dsimp [r, profileR, q]; rw [hc]; ring
  have hr : 0 < r q := by rw [hro]; positivity
  let x := a / s
  let y := c / s
  have hx : 0 < x := div_pos hap hs0
  have hy : 0 < y := div_pos hcp hs0
  have hsx : s * x = a := by dsimp [x]; field_simp
  have hsy : s * y = c := by dsimp [y]; field_simp
  let Ho := fun t : ℝ => (B : ℝ)⁻¹ * ∑ i,
    t * C.psdOut.isHermitian.eigenvalues i / (1 + t * C.psdOut.isHermitian.eigenvalues i)
  let Hi := fun t : ℝ => (B : ℝ)⁻¹ * ∑ i,
    t * C.psdIn.isHermitian.eigenvalues i / (1 + t * C.psdIn.isHermitian.eigenvalues i)
  have hHo : Ho x = r q := by
    have hh := p3_trace_scaled (B := B) C.psdOut hs0 hx
    change _ = Ho x / (s * x) at hh
    rw [hsx] at hh
    rw [hro]
    simpa only [mul_comm] using (div_eq_iff hap.ne').1 (hσ.trans hh).symm
  have hHi : Hi y = r q := by
    have hh := p3_trace_scaled (B := B) C.psdIn hs0 hy
    change _ = Hi y / (s * y) at hh
    rw [hsy] at hh
    rw [hri]
    simpa only [mul_comm] using (div_eq_iff hcp.ne').1 (hτ.trans hh).symm
  have heo : ∃ i, 0 < C.psdOut.isHermitian.eigenvalues i := by
    by_contra! h
    apply hout
    apply C.psdOut.isHermitian.eigenvalues_eq_zero_iff.mp
    funext i
    exact le_antisymm (h i) (C.psdOut.eigenvalues_nonneg i)
  have hei : ∃ i, 0 < C.psdIn.isHermitian.eigenvalues i := by
    by_contra! h
    apply hin
    apply C.psdIn.isHermitian.eigenvalues_eq_zero_iff.mp
    funext i
    exact le_antisymm (h i) (C.psdIn.eigenvalues_nonneg i)
  obtain ⟨A, da, hAa, hAd, hAx, hda, hAb, hAi⟩ := p3_spectral_chart hB
    C.psdOut.isHermitian.eigenvalues C.psdOut.eigenvalues_nonneg heo hx
  obtain ⟨D, dd, hDa, hDd, hDy, hdd, hDb, hDi⟩ := p3_spectral_chart hB
    C.psdIn.isHermitian.eigenvalues C.psdIn.eigenvalues_nonneg hei hy
  change AnalyticAt ℝ A (Ho x) at hAa
  change HasDerivAt A da (Ho x) at hAd
  change A (Ho x) = x at hAx
  change x ≤ Ho x * da at hAb
  change ∀ᶠ z in 𝓝 (Ho x), Ho (A z) = z at hAi
  change AnalyticAt ℝ D (Hi y) at hDa
  change HasDerivAt D dd (Hi y) at hDd
  change D (Hi y) = y at hDy
  change y ≤ Hi y * dd at hDb
  change ∀ᶠ z in 𝓝 (Hi y), Hi (D z) = z at hDi
  rw [hHo] at hAa hAd hAx hAb hAi
  rw [hHi] at hDa hDd hDy hDb hDi
  obtain ⟨hFc, hRc, hFa, hRa, hAnti, hFzero, hRzero, hFp, hRd, hRdp, hFd, hid⟩ :=
    lem_app_vol_closed_profile_i hξ
  have hra : AnalyticAt ℝ r q := hRa q hq
  have hrd : HasDerivAt r (profileRDeriv P ξ q) q :=
    (hRd q hq.le).hasDerivAt (Ici_mem_nhds hq)
  let Z := fun t : ℝ => (r t / A (r t)) * (r t / D (r t)) / t
  have hza : AnalyticAt ℝ Z q :=
    ((hra.div (hAa.comp hra) (by simpa only [Function.comp_apply, hAx] using hx.ne')).mul
      (hra.div (hDa.comp hra) (by simpa only [Function.comp_apply, hDy] using hy.ne'))).div
        analyticAt_id hq.ne'
  have hzd : deriv Z q < 0 := p3_scalar_deriv_neg hq hr
    (by rw [hAx]; exact hx) (by rw [hDy]; exact hy) hrd hAd hDd
    (hRdp q hq.le).le (by rwa [hAx]) (by rwa [hDy])
  have hZq : Z q = s := by
    dsimp only [Z]
    rw [hAx, hDy, hro]
    dsimp [x, y, q]
    have hac : a * σ = c * τ := hro.symm.trans hri
    field_simp
    nlinarith only [hac]
  let X := fun t : ℝ => (r t / (Z t * A (r t)), r t / (Z t * D (r t)),
    Z t * A (r t), Z t * D (r t))
  have hAcomp : AnalyticAt ℝ (fun t => A (r t)) q := hAa.comp hra
  have hDcomp : AnalyticAt ℝ (fun t => D (r t)) q := hDa.comp hra
  have hXa : AnalyticAt ℝ X q := by
    have huo : AnalyticAt ℝ (fun t => Z t * A (r t)) q := hza.mul hAcomp
    have hui : AnalyticAt ℝ (fun t => Z t * D (r t)) q := hza.mul hDcomp
    have hno : Z q * A (r q) ≠ 0 := by rw [hZq, hAx]; positivity
    have hni : Z q * D (r q) ≠ 0 := by rw [hZq, hDy]; positivity
    exact (hra.div huo hno).prod ((hra.div hui hni).prod (huo.prod hui))
  have heq : ∀ᶠ t in 𝓝 q, branchPt (profileF P ξ) C B (Z t) = X t := by
    have hAn : ∀ᶠ t in 𝓝 q, 0 < A (r t) :=
      hAcomp.continuousAt.eventually (Ioi_mem_nhds (by change 0 < A (r q); rw [hAx]; exact hx))
    have hDn : ∀ᶠ t in 𝓝 q, 0 < D (r t) :=
      hDcomp.continuousAt.eventually (Ioi_mem_nhds (by change 0 < D (r q); rw [hDy]; exact hy))
    have hAin := hra.continuousAt.tendsto.eventually hAi
    have hDin := hra.continuousAt.tendsto.eventually hDi
    filter_upwards [Ioi_mem_nhds hq, hAn, hDn, hAin, hDin] with t ht hAt hDt hAo hDo
    have hrt : 0 < r t := mul_pos ht ((p3_admissible hξ).pos t ht.le)
    have hzt : 0 < Z t := div_pos (mul_pos (div_pos hrt hAt) (div_pos hrt hDt)) ht
    have hsol : IsBranchPoint (profileF P ξ) C B (Z t) (X t) :=
      p3_scalar_converse hξ C ht hAt hDt hAo hDo
    exact (p3_exists_unique hB hξ hzt C).unique (p3_branchPt_spec hB hξ hzt C) hsol
  have hcomp : AnalyticAt ℝ ((fun t => branchPt (profileF P ξ) C B t) ∘ Z) q :=
    hXa.congr (Filter.Eventually.mono heq (fun _ ht => ht.symm))
  have hfinal := (analyticAt_comp_iff_of_deriv_ne_zero hza hzd.ne).mp hcomp
  rwa [hZq] at hfinal

private lemma p4_profile_tendsto {P : Measure Ω} [IsProbabilityMeasure P]
    {ξ : ι → Ω → ℝ} (hξ : def_app_vol_closed_profile P ξ)
    {ξn : ℕ → ι → Ω → ℝ}
    (hconv : ∀ ε > (0 : ℝ), ∃ N : ℕ, ∀ k ≥ N, ∀ q ∈ Ici (0 : ℝ),
      |profileF P (ξn k) q - profileF P ξ q| ≤ ε)
    {k : ℕ → ℕ} (hk : Tendsto k atTop atTop) {q : ℕ → ℝ} {q₀ : ℝ}
    (hq : Tendsto q atTop (𝓝 q₀)) (hq0 : ∀ j, 0 ≤ q j) (hq₀ : 0 ≤ q₀) :
    Tendsto (fun j => profileF P (ξn (k j)) (q j)) atTop (𝓝 (profileF P ξ q₀)) := by
  have hqw : Tendsto q atTop (𝓝[Ici 0] q₀) :=
    tendsto_nhdsWithin_iff.2 ⟨hq, Filter.Eventually.of_forall hq0⟩
  have hFc : Tendsto (fun j => profileF P ξ (q j)) atTop (𝓝 (profileF P ξ q₀)) :=
    ((lem_app_vol_closed_profile_i hξ).1 q₀ hq₀).tendsto.comp hqw
  rw [Metric.tendsto_nhds] at hFc ⊢
  intro ε hε
  obtain ⟨N, hN⟩ := hconv (ε / 2) (by linarith)
  have hkN : ∀ᶠ j in atTop, N ≤ k j := hk.eventually (eventually_ge_atTop N)
  filter_upwards [hkN, hFc (ε / 2) (by linarith)] with j hj hFj
  rw [Real.dist_eq] at hFj ⊢
  calc
    |profileF P (ξn (k j)) (q j) - profileF P ξ q₀| ≤
        |profileF P (ξn (k j)) (q j) - profileF P ξ (q j)| +
          |profileF P ξ (q j) - profileF P ξ q₀| := abs_sub_le _ _ _
    _ < ε := by
      have := hN (k j) hj (q j) (hq0 j)
      linarith

private lemma p4_trace_tendsto {d : ℕ} {S : Matrix (Fin d) (Fin d) ℝ}
    (hS : S.PosSemidef) {s : ℝ} (hs : 0 < s) {a : ℕ → ℝ} {a₀ : ℝ}
    (ha : Tendsto a atTop (𝓝 a₀)) (ha0 : ∀ j, 0 ≤ a j) (ha₀ : 0 ≤ a₀) :
    Tendsto (fun j => (S * (s • (1 : Matrix (Fin d) (Fin d) ℝ) + a j • S)⁻¹).trace)
      atTop (𝓝 ((S * (s • (1 : Matrix (Fin d) (Fin d) ℝ) + a₀ • S)⁻¹).trace)) := by
  have hc : Tendsto (fun t : ℝ => ∑ i,
      hS.isHermitian.eigenvalues i / (t * hS.isHermitian.eigenvalues i + s))
      (𝓝 a₀) (𝓝 (∑ i, hS.isHermitian.eigenvalues i /
        (a₀ * hS.isHermitian.eigenvalues i + s))) := by
    apply tendsto_finset_sum
    intro i hi
    refine (continuousAt_const.div
      (continuousAt_id.mul continuousAt_const |>.add continuousAt_const) ?_).tendsto
    have he := hS.eigenvalues_nonneg i
    exact (add_pos_of_nonneg_of_pos (mul_nonneg ha₀ he) hs).ne'
  rw [p3_trace_resolvent hS hs ha₀]
  refine (hc.comp ha).congr' (Filter.Eventually.of_forall (fun j => ?_))
  simp only [Function.comp_apply]
  rw [p3_trace_resolvent hS hs (ha0 j)]

private lemma p4_branch_iff_de {m n B : ℕ} (hB : 0 < B) (C : Muon.Covariances m n)
    (F : ℝ → ℝ) (ν ν' : FiniteMeasure ℝ)
    (hν : (ν : Measure ℝ) = Muon.nuOut C B)
    (hν' : (ν' : Measure ℝ) = Muon.nuIn C B) {s : ℝ} (hs : 0 < s)
    (x : ℝ × ℝ × ℝ × ℝ) :
    IsBranchPoint F C B s x ↔ Muon.DetEquiv.IsBranchSol F ν ν' s x := by
  rcases x with ⟨σ, σ', a, c⟩
  simp only [IsBranchPoint, Muon.DetEquiv.IsBranchSol]
  change (_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _) ↔
    (0 ≤ σ ∧ 0 ≤ σ' ∧ 0 ≤ a ∧ 0 ≤ c ∧
      σ = ∫ t, t / (a * t + s) ∂(ν : Measure ℝ) ∧
      σ' = ∫ t, t / (c * t + s) ∂(ν' : Measure ℝ) ∧
      a = s * σ' * F (s * σ * σ') ∧ c = s * σ * F (s * σ * σ'))
  rw [hν, hν']
  constructor <;> rintro ⟨hσ0, hσ'0, ha0, hc0, hσ, hσ', ha, hc⟩
  · refine ⟨hσ0, hσ'0, ha0, hc0, ?_, ?_, ha, hc⟩
    · rw [Muon.DetEquiv.def_app_de_branch_trace C hB hs ha0 |>.1, add_comm]
      exact hσ
    · rw [Muon.DetEquiv.def_app_de_branch_trace C hB hs hc0 |>.2, add_comm]
      exact hσ'
  · refine ⟨hσ0, hσ'0, ha0, hc0, ?_, ?_, ha, hc⟩
    · rw [Muon.DetEquiv.def_app_de_branch_trace C hB hs ha0 |>.1, add_comm] at hσ
      exact hσ
    · rw [Muon.DetEquiv.def_app_de_branch_trace C hB hs hc0 |>.2, add_comm] at hσ'
      exact hσ'

/-- `lem:app-vol-closed-branch`, snapshot `cr-2026-10-23`. Declaration of record for part (iv) of `lem:app-vol-closed-branch`
(stability): if `sup_{q ≥ 0} |F_{ξ^(k)}(q) - F_ξ(q)| → 0` and `sup_k F_{ξ^(k)}(0) < ∞`, then for each
`s > 0` the branch points of `ξ^(k)` at `s` converge to the branch point of `ξ` at `s`. The
uniform convergence is written as an `ε`–`N` statement, which is equivalent.

LaTeX (`sections/04-volatility/section.tex` l.1794–1827, verbatim):
```latex
\begin{lemma}[Branch of a profile]\label{lem:app-vol-closed-branch}
Let $\xi$ be a profile and $s>0$. A \emph{branch point} of $\xi$ at $s$ is a
quadruple $(\sigma,\tilde\sigma,\tilde s_1,s_1)\in[0,\infty)^4$ with
\begin{equation}\label{eqn:app-vol-closed-branch}
\begin{gathered}
\sigma=\frac1B\Tr\Sigmaout(s\Id+\tilde s_1\Sigmaout)^{-1},\qquad
\tilde\sigma=\frac1B\Tr\Sigmain(s\Id+s_1\Sigmain)^{-1},\\
\tilde s_1=s\tilde\sigma F_\xi(q),\qquad s_1=s\sigma F_\xi(q),
\end{gathered}
\end{equation}
where $q\defeq s\sigma\tilde\sigma$.
\begin{enumerate}[label=(\roman*)]
\item If $\Sigmaout=0$, the unique branch point at $s$ is $\sigma=s_1=0$,
$\tilde\sigma=B^{-1}\Tr\Sigmain/s$, $\tilde s_1=B^{-1}\Tr\Sigmain\,F_\xi(0)$, with $q=0$. The
case $\Sigmain=0$ is symmetric.
\item If $\Sigmaout\ne0$ and $\Sigmain\ne0$, then \cref{eqn:app-vol-closed-branch} has
exactly one solution in $[0,\infty)^4$. It lies in $(0,\infty)^4$ and in the box
\[
\sigma\le\frac{\Tr\Sigmaout}{Bs},\qquad \tilde\sigma\le\frac{\Tr\Sigmain}{Bs},\qquad
\tilde s_1\le\frac{\Tr\Sigmain}B\,F_\xi(0),\qquad s_1\le\frac{\Tr\Sigmaout}B\,F_\xi(0),
\]
and $r_\xi(q)=\tilde s_1\sigma=s_1\tilde\sigma<\min(\operatorname{rank}\Sigmaout,\operatorname{rank}\Sigmain)/B\le\gamma_\star$.
\item In case (ii), $s\mapsto(\sigma,\tilde\sigma,\tilde s_1,s_1,q)(s)$ is real-analytic on
$(0,\infty)$, and $q$ is strictly decreasing in $s$.
\item (Stability.) Let $\xi^{(n)}$ be profiles with
$\sup_{q\ge0}\abs{F_{\xi^{(n)}}(q)-F_\xi(q)}\to0$ and $\sup_nF_{\xi^{(n)}}(0)<\infty$. Then for
each $s>0$ the branch points of $\xi^{(n)}$ at $s$ converge to the branch point of
$\xi$ at $s$.
\end{enumerate}
For the EMA weights, \cref{eqn:app-vol-closed-branch} is the system
\cref{eqn:app-de-system} at $z=-s$ for the spectral measures of
\cref{eqn:app-setup-spectral-measures}, and its branch point is the solution of
\cref{thm:app-de-branch}.
\end{lemma}
```
-/
theorem lem_app_vol_closed_branch_iv {m n B : ℕ} (hB : 0 < B) {P : Measure Ω}
    [IsProbabilityMeasure P] {ξ : ι → Ω → ℝ} (hξ : def_app_vol_closed_profile P ξ)
    (C : Muon.Covariances m n) {ξn : ℕ → ι → Ω → ℝ}
    (hξn : ∀ k, def_app_vol_closed_profile P (ξn k))
    (hconv : ∀ ε > (0 : ℝ), ∃ N : ℕ, ∀ k ≥ N, ∀ q ∈ Ici (0 : ℝ),
      |profileF P (ξn k) q - profileF P ξ q| ≤ ε)
    (hbdd : BddAbove (Set.range fun k => profileF P (ξn k) 0)) :
    ∀ s : ℝ, 0 < s →
      Tendsto (fun k => branchPt (profileF P (ξn k)) C B s) atTop
        (𝓝 (branchPt (profileF P ξ) C B s)) := by
  intro s hs
  by_cases hout : C.Sout = 0
  · have hform : ∀ k, branchPt (profileF P (ξn k)) C B s =
        (0, (B : ℝ)⁻¹ * C.Sin.trace / s,
          (B : ℝ)⁻¹ * C.Sin.trace * profileF P (ξn k) 0, 0) := by
      intro k
      exact (lem_app_vol_closed_branch_i hB (hξn k) hs C).1 hout |>.2 _
        (p3_branchPt_spec hB (hξn k) hs C)
    have hlim : Tendsto (fun k => profileF P (ξn k) 0) atTop (𝓝 (profileF P ξ 0)) :=
      p4_profile_tendsto hξ hconv tendsto_id (tendsto_const_nhds (x := (0 : ℝ)))
        (fun _ => le_rfl) le_rfl
    have ht : Tendsto (fun k =>
        ((0 : ℝ), (B : ℝ)⁻¹ * C.Sin.trace / s,
          (B : ℝ)⁻¹ * C.Sin.trace * profileF P (ξn k) 0, (0 : ℝ))) atTop
        (𝓝 ((0 : ℝ), (B : ℝ)⁻¹ * C.Sin.trace / s,
          (B : ℝ)⁻¹ * C.Sin.trace * profileF P ξ 0, (0 : ℝ))) :=
      tendsto_const_nhds.prodMk_nhds (tendsto_const_nhds.prodMk_nhds
        ((tendsto_const_nhds.mul hlim).prodMk_nhds tendsto_const_nhds))
    have htarget := (lem_app_vol_closed_branch_i hB hξ hs C).1 hout |>.2 _
      (p3_branchPt_spec hB hξ hs C)
    rw [htarget]
    exact ht.congr' (Filter.Eventually.of_forall (fun k => (hform k).symm))
  · by_cases hin : C.Sin = 0
    · have hform : ∀ k, branchPt (profileF P (ξn k)) C B s =
          ((B : ℝ)⁻¹ * C.Sout.trace / s, 0, 0,
            (B : ℝ)⁻¹ * C.Sout.trace * profileF P (ξn k) 0) := by
        intro k
        exact (lem_app_vol_closed_branch_i hB (hξn k) hs C).2 hin |>.2 _
          (p3_branchPt_spec hB (hξn k) hs C)
      have hlim : Tendsto (fun k => profileF P (ξn k) 0) atTop (𝓝 (profileF P ξ 0)) :=
        p4_profile_tendsto hξ hconv tendsto_id (tendsto_const_nhds (x := (0 : ℝ)))
          (fun _ => le_rfl) le_rfl
      have ht : Tendsto (fun k =>
          ((B : ℝ)⁻¹ * C.Sout.trace / s, (0 : ℝ), (0 : ℝ),
            (B : ℝ)⁻¹ * C.Sout.trace * profileF P (ξn k) 0)) atTop
          (𝓝 ((B : ℝ)⁻¹ * C.Sout.trace / s, (0 : ℝ), (0 : ℝ),
            (B : ℝ)⁻¹ * C.Sout.trace * profileF P ξ 0)) :=
        tendsto_const_nhds.prodMk_nhds (tendsto_const_nhds.prodMk_nhds
          (tendsto_const_nhds.prodMk_nhds (tendsto_const_nhds.mul hlim)))
      have htarget := (lem_app_vol_closed_branch_i hB hξ hs C).2 hin |>.2 _
        (p3_branchPt_spec hB hξ hs C)
      rw [htarget]
      exact ht.congr' (Filter.Eventually.of_forall (fun k => (hform k).symm))
    · rw [bddAbove_def] at hbdd
      obtain ⟨M, hM⟩ := hbdd
      have hMk : ∀ k, profileF P (ξn k) 0 ≤ M := fun k => hM _ ⟨k, rfl⟩
      have hBr : (0 : ℝ) < B := by exact_mod_cast hB
      have hB1 : (1 : ℝ) ≤ B := by exact_mod_cast hB
      have hγ : (max m n : ℝ) ≤ (max m n : ℝ) * B := by
        have hm : (0 : ℝ) ≤ max (m : ℝ) (n : ℝ) := by positivity
        nlinarith
      let K : Set (ℝ × ℝ × ℝ × ℝ) :=
        Icc 0 (C.Sout.trace / (B * s)) ×ˢ
          (Icc 0 (C.Sin.trace / (B * s)) ×ˢ
            (Icc 0 (C.Sin.trace / B * M) ×ˢ Icc 0 (C.Sout.trace / B * M)))
      have hKc : IsCompact K :=
        isCompact_Icc.prod (isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc))
      have hmem : ∀ k, branchPt (profileF P (ξn k)) C B s ∈ K := by
        intro k
        have hb := (lem_app_vol_closed_branch_ii hB (hξn k) hs C hout hin
          (max m n : ℝ) hγ).2 _ (p3_branchPt_spec hB (hξn k) hs C)
        obtain ⟨⟨hσ, hσ', ha, hc⟩, hσb, hσ'b, hab, hcb, hr, hac, hrr, hrg⟩ := hb
        exact ⟨⟨hσ.le, hσb⟩, ⟨⟨hσ'.le, hσ'b⟩,
          ⟨⟨ha.le, hab.trans (mul_le_mul_of_nonneg_left (hMk k)
            (div_nonneg C.psdIn.trace_nonneg hBr.le))⟩,
            ⟨hc.le, hcb.trans (mul_le_mul_of_nonneg_left (hMk k)
              (div_nonneg C.psdOut.trace_nonneg hBr.le))⟩⟩⟩⟩
      refine Filter.tendsto_of_subseq_tendsto (fun ns hns => ?_)
      obtain ⟨y, hyK, φ, hφ, hy⟩ := hKc.tendsto_subseq (fun j => hmem (ns j))
      let k := fun j => ns (φ j)
      have hk : Tendsto k atTop atTop := hns.comp hφ.tendsto_atTop
      rcases y with ⟨σ, σ', a, c⟩
      have hyσ := hy.fst_nhds
      have hyσ' := hy.snd_nhds.fst_nhds
      have hya := hy.snd_nhds.snd_nhds.fst_nhds
      have hyc := hy.snd_nhds.snd_nhds.snd_nhds
      simp only [K, mem_prod, mem_Icc] at hyK
      have hy0 : 0 ≤ σ ∧ 0 ≤ σ' ∧ 0 ≤ a ∧ 0 ≤ c :=
        ⟨hyK.1.1, hyK.2.1.1, hyK.2.2.1.1, hyK.2.2.2.1⟩
      have hspec : ∀ j, IsBranchPoint (profileF P (ξn (k j))) C B s
          (branchPt (profileF P (ξn (k j))) C B s) :=
        fun j => p3_branchPt_spec hB (hξn (k j)) hs C
      have hq : Tendsto (fun j => s * (branchPt (profileF P (ξn (k j))) C B s).1 *
          (branchPt (profileF P (ξn (k j))) C B s).2.1) atTop (𝓝 (s * σ * σ')) :=
        (tendsto_const_nhds.mul hyσ).mul hyσ'
      have hq0 : ∀ j, 0 ≤ s * (branchPt (profileF P (ξn (k j))) C B s).1 *
          (branchPt (profileF P (ξn (k j))) C B s).2.1 := fun j =>
        mul_nonneg (mul_nonneg hs.le (hspec j).1) (hspec j).2.1
      have hFt := p4_profile_tendsto hξ hconv hk hq hq0
        (mul_nonneg (mul_nonneg hs.le hy0.1) hy0.2.1)
      have hto := p4_trace_tendsto C.psdOut hs hya
        (fun j => (hspec j).2.2.1) hy0.2.2.1
      have hti := p4_trace_tendsto C.psdIn hs hyc
        (fun j => (hspec j).2.2.2.1) hy0.2.2.2
      have hσeq : σ = (B : ℝ)⁻¹ *
          (C.Sout * (s • (1 : Matrix (Fin m) (Fin m) ℝ) + a • C.Sout)⁻¹).trace := by
        apply tendsto_nhds_unique hyσ
        exact (tendsto_const_nhds.mul hto).congr'
          (Filter.Eventually.of_forall (fun j => (hspec j).2.2.2.2.1.symm))
      have hσ'eq : σ' = (B : ℝ)⁻¹ *
          (C.Sin * (s • (1 : Matrix (Fin n) (Fin n) ℝ) + c • C.Sin)⁻¹).trace := by
        apply tendsto_nhds_unique hyσ'
        exact (tendsto_const_nhds.mul hti).congr'
          (Filter.Eventually.of_forall (fun j => (hspec j).2.2.2.2.2.1.symm))
      have haeq : a = s * σ' * profileF P ξ (s * σ * σ') := by
        apply tendsto_nhds_unique
          (hya.congr' (Filter.Eventually.of_forall (fun j => (hspec j).2.2.2.2.2.2.1)))
        exact (tendsto_const_nhds.mul hyσ').mul hFt
      have hceq : c = s * σ * profileF P ξ (s * σ * σ') := by
        apply tendsto_nhds_unique
          (hyc.congr' (Filter.Eventually.of_forall (fun j => (hspec j).2.2.2.2.2.2.2)))
        exact (tendsto_const_nhds.mul hyσ).mul hFt
      have hsol : IsBranchPoint (profileF P ξ) C B s (σ, σ', a, c) :=
        ⟨hy0.1, hy0.2.1, hy0.2.2.1, hy0.2.2.2, hσeq, hσ'eq, haeq, hceq⟩
      have heq := (p3_exists_unique hB hξ hs C).unique hsol
        (p3_branchPt_spec hB hξ hs C)
      refine ⟨φ, ?_⟩
      rw [← heq]
      convert hy using 1
      funext j
      rfl

/-- `lem:app-vol-closed-branch`, snapshot `cr-2026-10-23`. Declaration of record for the EMA clause of `lem:app-vol-closed-branch`
(the final sentence): for the EMA weights the EMA profile has marginal `F_w`, and its branch point is the
solution of the B-branch system (`Muon.DetEquiv.branchSol`) for the spectral measures `ν_out = nuOut`,
`ν_in = nuIn` in the class `𝒦` (`Muon.DetEquiv.classK`).

LaTeX (`sections/04-volatility/section.tex` l.1794–1827, verbatim):
```latex
\begin{lemma}[Branch of a profile]\label{lem:app-vol-closed-branch}
Let $\xi$ be a profile and $s>0$. A \emph{branch point} of $\xi$ at $s$ is a
quadruple $(\sigma,\tilde\sigma,\tilde s_1,s_1)\in[0,\infty)^4$ with
\begin{equation}\label{eqn:app-vol-closed-branch}
\begin{gathered}
\sigma=\frac1B\Tr\Sigmaout(s\Id+\tilde s_1\Sigmaout)^{-1},\qquad
\tilde\sigma=\frac1B\Tr\Sigmain(s\Id+s_1\Sigmain)^{-1},\\
\tilde s_1=s\tilde\sigma F_\xi(q),\qquad s_1=s\sigma F_\xi(q),
\end{gathered}
\end{equation}
where $q\defeq s\sigma\tilde\sigma$.
\begin{enumerate}[label=(\roman*)]
\item If $\Sigmaout=0$, the unique branch point at $s$ is $\sigma=s_1=0$,
$\tilde\sigma=B^{-1}\Tr\Sigmain/s$, $\tilde s_1=B^{-1}\Tr\Sigmain\,F_\xi(0)$, with $q=0$. The
case $\Sigmain=0$ is symmetric.
\item If $\Sigmaout\ne0$ and $\Sigmain\ne0$, then \cref{eqn:app-vol-closed-branch} has
exactly one solution in $[0,\infty)^4$. It lies in $(0,\infty)^4$ and in the box
\[
\sigma\le\frac{\Tr\Sigmaout}{Bs},\qquad \tilde\sigma\le\frac{\Tr\Sigmain}{Bs},\qquad
\tilde s_1\le\frac{\Tr\Sigmain}B\,F_\xi(0),\qquad s_1\le\frac{\Tr\Sigmaout}B\,F_\xi(0),
\]
and $r_\xi(q)=\tilde s_1\sigma=s_1\tilde\sigma<\min(\operatorname{rank}\Sigmaout,\operatorname{rank}\Sigmain)/B\le\gamma_\star$.
\item In case (ii), $s\mapsto(\sigma,\tilde\sigma,\tilde s_1,s_1,q)(s)$ is real-analytic on
$(0,\infty)$, and $q$ is strictly decreasing in $s$.
\item (Stability.) Let $\xi^{(n)}$ be profiles with
$\sup_{q\ge0}\abs{F_{\xi^{(n)}}(q)-F_\xi(q)}\to0$ and $\sup_nF_{\xi^{(n)}}(0)<\infty$. Then for
each $s>0$ the branch points of $\xi^{(n)}$ at $s$ converge to the branch point of
$\xi$ at $s$.
\end{enumerate}
For the EMA weights, \cref{eqn:app-vol-closed-branch} is the system
\cref{eqn:app-de-system} at $z=-s$ for the spectral measures of
\cref{eqn:app-setup-spectral-measures}, and its branch point is the solution of
\cref{thm:app-de-branch}.
\end{lemma}
```
-/
theorem lem_app_vol_closed_branch_ema {m n B : ℕ} (hB : 0 < B) {P : Measure Ω}
    [IsProbabilityMeasure P] {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {ℓ : ℕ}
    {g : ℕ ⊕ Fin ℓ → Ω → ℝ} (hg : IsStdGaussianFamily P g)
    (C : Muon.Covariances m n) (Cs γ : ℝ) (ν ν' : FiniteMeasure ℝ)
    (hν : (ν : Measure ℝ) = Muon.nuOut C B) (hν' : (ν' : Measure ℝ) = Muon.nuIn C B)
    (hK : (ν, ν') ∈ Muon.DetEquiv.classK Cs γ) {s : ℝ} (hs : 0 < s) :
    profileF P (emaXi₁ β ℓ g) = Muon.DetEquiv.Fw (Muon.emaW β) ∧
    branchPt (profileF P (emaXi₁ β ℓ g)) C B s =
      Muon.DetEquiv.branchSol (Muon.DetEquiv.Fw (Muon.emaW β)) ν ν' s := by
  have hp := lem_app_vol_closed_profile_iv hβ0 hβ1 hg
  refine ⟨hp.1, ?_⟩
  rw [hp.1]
  have hξema := hp.2.2.2.2.2
  have hx : IsBranchPoint (Muon.DetEquiv.Fw (Muon.emaW β)) C B s
      (branchPt (Muon.DetEquiv.Fw (Muon.emaW β)) C B s) := by
    have hx0 := p3_branchPt_spec hB hξema.profile₁ hs C
    rw [hp.1] at hx0
    exact hx0
  have heq := p4_branch_iff_de hB C (Muon.DetEquiv.Fw (Muon.emaW β)) ν ν' hν hν' hs
  have hex : ∃ x, Muon.DetEquiv.IsBranchSol (Muon.DetEquiv.Fw (Muon.emaW β)) ν ν' s x :=
    ⟨_, (heq _).1 hx⟩
  have hbranch : Muon.DetEquiv.IsBranchSol (Muon.DetEquiv.Fw (Muon.emaW β)) ν ν' s
      (Muon.DetEquiv.branchSol (Muon.DetEquiv.Fw (Muon.emaW β)) ν ν' s) := by
    unfold Muon.DetEquiv.branchSol
    rw [dif_pos hex]
    exact hex.choose_spec
  have hu := p3_exists_unique hB hξema.profile₁ hs C
  rw [hp.1] at hu
  exact hu.unique hx ((heq _).2 hbranch)

/-- `lem:app-vol-closed-perron`, snapshot `cr-2026-10-23`. Declaration of record for `lem:app-vol-closed-perron`: a `2×2` Perron
bound. The source's nonnegativity and positivity hypotheses are explicit, and `c ∈ (0,1]`.

LaTeX (`sections/04-volatility/section.tex` l.1922–1930, verbatim):
```latex
\begin{lemma}[A $2\times2$ Perron bound]\label{lem:app-vol-closed-perron}
Let $L,L_s,L_u$ be nonnegative $2\times2$ matrices, let $c\in(0,1]$, and suppose
$L_{kl}\le c\sqrt{(L_s)_{kl}(L_u)_{kl}}$ for all $k,l$. Suppose there are positive
vectors $v_s,v_u$ and numbers $\vartheta_s,\vartheta_u\in[0,1]$ with
$L_sv_s\le(1-\vartheta_s)v_s$ and $L_uv_u\le(1-\vartheta_u)v_u$ componentwise. Then
\[
\det(\Id-L)\ge\Big(1-c\sqrt{(1-\vartheta_s)(1-\vartheta_u)}\Big)^2 .
\]
\end{lemma}
```
-/
theorem lem_app_vol_closed_perron (L Ls Lu : Matrix (Fin 2) (Fin 2) ℝ) (c : ℝ)
    (hc0 : 0 < c) (hc1 : c ≤ 1)
    (hL : ∀ k l, 0 ≤ L k l) (hLs : ∀ k l, 0 ≤ Ls k l) (hLu : ∀ k l, 0 ≤ Lu k l)
    (hdom : ∀ k l, L k l ≤ c * Real.sqrt (Ls k l * Lu k l))
    (vs vu : Fin 2 → ℝ) (hvs : ∀ k, 0 < vs k) (hvu : ∀ k, 0 < vu k)
    (θs θu : ℝ) (hθs : θs ∈ Icc (0 : ℝ) 1) (hθu : θu ∈ Icc (0 : ℝ) 1)
    (hs : ∀ k, (Ls.mulVec vs) k ≤ (1 - θs) * vs k)
    (hu : ∀ k, (Lu.mulVec vu) k ≤ (1 - θu) * vu k) :
    (1 - c * Real.sqrt ((1 - θs) * (1 - θu))) ^ 2 ≤ (1 - L).det := by
  let v : Fin 2 → ℝ := fun k => Real.sqrt (vs k * vu k)
  let η : ℝ := c * Real.sqrt ((1 - θs) * (1 - θu))
  have hθs0 : 0 ≤ 1 - θs := sub_nonneg.mpr hθs.2
  have hθu0 : 0 ≤ 1 - θu := sub_nonneg.mpr hθu.2
  have hv : ∀ k, 0 < v k := fun k => Real.sqrt_pos.2 (mul_pos (hvs k) (hvu k))
  have hη0 : 0 ≤ η := mul_nonneg hc0.le (Real.sqrt_nonneg _)
  have hη1 : η ≤ 1 := by
    have hprod : (1 - θs) * (1 - θu) ≤ 1 := by
      exact mul_le_one₀ (by linarith [hθs.1]) hθu0 (by linarith [hθu.1])
    exact mul_le_one₀ hc1 (Real.sqrt_nonneg _) (Real.sqrt_le_one.mpr hprod)
  have hterm (k l : Fin 2) :
      Real.sqrt (Ls k l * Lu k l) * v l =
        Real.sqrt (Ls k l * vs l) * Real.sqrt (Lu k l * vu l) := by
    dsimp [v]
    rw [Real.sqrt_mul (hLs k l), Real.sqrt_mul (hLu k l),
      Real.sqrt_mul (hvs l).le, Real.sqrt_mul (hLs k l)]
    ring
  have hLv : ∀ k, (L.mulVec v) k ≤ η * v k := by
    intro k
    have hsumS : (∑ l : Fin 2, Ls k l * vs l) ≤ (1 - θs) * vs k := by
      simpa [Matrix.mulVec, dotProduct] using hs k
    have hsumU : (∑ l : Fin 2, Lu k l * vu l) ≤ (1 - θu) * vu k := by
      simpa [Matrix.mulVec, dotProduct] using hu k
    calc
      (L.mulVec v) k = ∑ l : Fin 2, L k l * v l := by
        simp [Matrix.mulVec, dotProduct]
      _ ≤ ∑ l : Fin 2, (c * Real.sqrt (Ls k l * Lu k l)) * v l := by
        exact Finset.sum_le_sum fun l _ =>
          mul_le_mul_of_nonneg_right (hdom k l) (hv l).le
      _ = c * ∑ l : Fin 2,
          Real.sqrt (Ls k l * vs l) * Real.sqrt (Lu k l * vu l) := by
        simp_rw [mul_assoc, hterm]
        rw [Finset.mul_sum]
      _ ≤ c * (Real.sqrt (∑ l : Fin 2, Ls k l * vs l) *
          Real.sqrt (∑ l : Fin 2, Lu k l * vu l)) := by
        apply mul_le_mul_of_nonneg_left _ hc0.le
        exact Real.sum_sqrt_mul_sqrt_le Finset.univ
          (fun l => mul_nonneg (hLs k l) (hvs l).le)
          (fun l => mul_nonneg (hLu k l) (hvu l).le)
      _ ≤ c * (Real.sqrt ((1 - θs) * vs k) *
          Real.sqrt ((1 - θu) * vu k)) := by
        apply mul_le_mul_of_nonneg_left _ hc0.le
        exact mul_le_mul (Real.sqrt_le_sqrt hsumS) (Real.sqrt_le_sqrt hsumU)
          (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
      _ = η * v k := by
        dsimp [η, v]
        rw [Real.sqrt_mul hθs0, Real.sqrt_mul hθu0,
          Real.sqrt_mul (hvs k).le, Real.sqrt_mul hθs0]
        ring
  have hrow0 := hLv (0 : Fin 2)
  have hrow1 := hLv (1 : Fin 2)
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two] at hrow0 hrow1
  have h00 : L 0 0 ≤ η := by
    apply le_of_mul_le_mul_right _ (hv 0)
    nlinarith [mul_nonneg (hL 0 1) (hv 1).le]
  have h11 : L 1 1 ≤ η := by
    apply le_of_mul_le_mul_right _ (hv 1)
    nlinarith [mul_nonneg (hL 1 0) (hv 0).le]
  have h01 : L 0 1 * v 1 ≤ (η - L 0 0) * v 0 := by
    linarith
  have h10 : L 1 0 * v 0 ≤ (η - L 1 1) * v 1 := by
    linarith
  have hweighted :
      (L 0 1 * v 1) * (L 1 0 * v 0) ≤
        ((η - L 0 0) * v 0) * ((η - L 1 1) * v 1) := by
    exact mul_le_mul h01 h10
      (mul_nonneg (hL 1 0) (hv 0).le)
      (mul_nonneg (sub_nonneg.mpr h00) (hv 0).le)
  have hvprod : 0 < v 0 * v 1 := mul_pos (hv 0) (hv 1)
  have hoff : L 0 1 * L 1 0 ≤ (η - L 0 0) * (η - L 1 1) := by
    apply le_of_mul_le_mul_right _ hvprod
    calc
      (L 0 1 * L 1 0) * (v 0 * v 1) =
          (L 0 1 * v 1) * (L 1 0 * v 0) := by ring
      _ ≤ ((η - L 0 0) * v 0) * ((η - L 1 1) * v 1) := hweighted
      _ = ((η - L 0 0) * (η - L 1 1)) * (v 0 * v 1) := by ring
  have hgap : 0 ≤ (1 - η) * (2 * η - L 0 0 - L 1 1) :=
    mul_nonneg (sub_nonneg.mpr hη1) (by linarith)
  have hfinal : (1 - η) ^ 2 ≤
      (1 - L 0 0) * (1 - L 1 1) - L 0 1 * L 1 0 := by
    nlinarith
  simpa [η, Matrix.det_fin_two, Matrix.one_apply] using hfinal

/-! ### Private helpers for `lem:app-vol-closed-determinant` (task P-D.15.P6) -/

private lemma d_trace_cfc {d : ℕ} {S : Matrix (Fin d) (Fin d) ℝ} (hS : S.PosSemidef) (φ : ℝ → ℝ) :
    (cfc φ S).trace = ∑ i, φ (hS.isHermitian.eigenvalues i) := by
  rw [hS.isHermitian.cfc_eq φ, Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply,
    Matrix.trace_mul_comm, ← mul_assoc, Unitary.coe_star_mul_self, one_mul, Matrix.trace_diagonal]
  simp only [Function.comp_apply, RCLike.ofReal_real_eq_id, id]

private lemma d_cfc_inv {d : ℕ} {S : Matrix (Fin d) (Fin d) ℝ} (hS : S.PosSemidef) {s a : ℝ}
    (hs : 0 < s) (ha : 0 ≤ a) :
    cfc (fun t => (s + a * t)⁻¹) S = (s • (1 : Matrix (Fin d) (Fin d) ℝ) + a • S)⁻¹ := by
  have hH : IsSelfAdjoint S := hS.isHermitian
  have hspec : spectrum ℝ S ⊆ {t : ℝ | 0 ≤ t} :=
    (Matrix.posSemidef_iff_isHermitian_and_spectrum_nonneg.1 hS).2
  have hadd : cfc (fun t => s + a * t) S = s • (1 : Matrix (Fin d) (Fin d) ℝ) + a • S := by
    rw [cfc_add (a := S) (fun _ => s) (fun t => a * t), cfc_const_mul_id a S hH, cfc_const s S hH,
      Algebra.algebraMap_eq_smul_one]
  have hne : ∀ t ∈ spectrum ℝ S, (fun t => s + a * t) t ≠ 0 := by
    intro t ht
    have h1' : (0 : ℝ) ≤ t := hspec ht
    have h2' : 0 ≤ a * t := mul_nonneg ha h1'
    show s + a * t ≠ 0
    exact (by linarith : (0 : ℝ) < s + a * t).ne'
  rw [← hadd, Matrix.nonsing_inv_eq_ringInverse]
  exact cfc_inv (a := S) (f := fun t => s + a * t) hne

private lemma d_trace_two {d : ℕ} {S : Matrix (Fin d) (Fin d) ℝ} (hS : S.PosSemidef) {s a u c : ℝ}
    (hs : 0 < s) (hu : 0 < u) (ha : 0 ≤ a) (hc : 0 ≤ c) :
    (S * S * (s • (1 : Matrix (Fin d) (Fin d) ℝ) + a • S)⁻¹ *
        (u • (1 : Matrix (Fin d) (Fin d) ℝ) + c • S)⁻¹).trace =
      ∑ i, hS.isHermitian.eigenvalues i ^ 2 /
        ((s + a * hS.isHermitian.eigenvalues i) * (u + c * hS.isHermitian.eigenvalues i)) := by
  have hH : IsSelfAdjoint S := hS.isHermitian
  have hspec : spectrum ℝ S ⊆ {t : ℝ | 0 ≤ t} :=
    (Matrix.posSemidef_iff_isHermitian_and_spectrum_nonneg.1 hS).2
  have hne1 : ∀ t ∈ spectrum ℝ S, s + a * t ≠ 0 := fun t ht =>
    (by have := hspec ht; have : 0 ≤ a * t := mul_nonneg ha this; linarith : (0 : ℝ) < s + a * t).ne'
  have hne2 : ∀ t ∈ spectrum ℝ S, u + c * t ≠ 0 := fun t ht =>
    (by have := hspec ht; have : 0 ≤ c * t := mul_nonneg hc this; linarith : (0 : ℝ) < u + c * t).ne'
  have hc1 : ContinuousOn (fun t : ℝ => (s + a * t)⁻¹) (spectrum ℝ S) :=
    ContinuousOn.inv₀ (by fun_prop) hne1
  have hc2 : ContinuousOn (fun t : ℝ => (u + c * t)⁻¹) (spectrum ℝ S) :=
    ContinuousOn.inv₀ (by fun_prop) hne2
  have h : cfc (fun t : ℝ => t * t * (s + a * t)⁻¹ * (u + c * t)⁻¹) S =
      S * S * (s • (1 : Matrix (Fin d) (Fin d) ℝ) + a • S)⁻¹ *
        (u • (1 : Matrix (Fin d) (Fin d) ℝ) + c • S)⁻¹ := by
    rw [← d_cfc_inv hS hs ha, ← d_cfc_inv hS hu hc]
    rw [cfc_mul (fun t : ℝ => t * t * (s + a * t)⁻¹) (fun t : ℝ => (u + c * t)⁻¹) S
      (by fun_prop) hc2]
    rw [cfc_mul (fun t : ℝ => t * t) (fun t : ℝ => (s + a * t)⁻¹) S (by fun_prop) hc1]
    rw [cfc_mul (fun t : ℝ => t) (fun t : ℝ => t) S (by fun_prop) (by fun_prop)]
    rw [cfc_id' ℝ S]
  rw [← h, d_trace_cfc hS]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  field_simp

private lemma d_eig_le_opNorm {d : ℕ} {S : Matrix (Fin d) (Fin d) ℝ} (hS : S.PosSemidef) (i : Fin d) :
    hS.isHermitian.eigenvalues i ≤ Muon.opNorm S := by
  have hv := hS.isHermitian.mulVec_eigenvectorBasis i
  set v := hS.isHermitian.eigenvectorBasis i with hvdef
  have hn : ‖v‖ = 1 := hS.isHermitian.eigenvectorBasis.orthonormal.1 i
  have h1 : ‖(LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin S)) v‖ ≤ Muon.opNorm S * ‖v‖ :=
    ContinuousLinearMap.le_opNorm _ _
  have h2 : (LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin S)) v =
      hS.isHermitian.eigenvalues i • v := by
    ext j
    have := congrFun hv j
    simpa [Matrix.toEuclideanLin, Matrix.toLpLin_apply, hvdef] using this
  rw [h2, norm_smul, hn] at h1
  simp only [mul_one, Real.norm_eq_abs] at h1
  exact (le_abs_self _).trans h1

private lemma d_sqrt_four {s u x y A B C D : ℝ} (hs : 0 ≤ s) (hu : 0 ≤ u) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (_hC : 0 ≤ C) (_hD : 0 ≤ D) :
    Real.sqrt ((s ^ 2 * A * x ^ 2 * C) * (u ^ 2 * B * y ^ 2 * D)) =
      s * u * x * y * Real.sqrt (A * B) * Real.sqrt (C * D) := by
  have h1 : (s ^ 2 * A * x ^ 2 * C) * (u ^ 2 * B * y ^ 2 * D) =
      (s * u * x * y) ^ 2 * ((A * B) * (C * D)) := by ring
  rw [h1, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity),
    Real.sqrt_mul (mul_nonneg hA hB)]
  ring

private lemma d_sqrt_two {s u A B C D : ℝ} (hs : 0 ≤ s) (hu : 0 ≤ u)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (_hC : 0 ≤ C) (_hD : 0 ≤ D) :
    Real.sqrt ((s * A * C) * (u * B * D)) =
      Real.sqrt (s * u) * Real.sqrt (A * B) * Real.sqrt (C * D) := by
  have h1 : (s * A * C) * (u * B * D) = (s * u) * ((A * B) * (C * D)) := by ring
  rw [h1, Real.sqrt_mul (mul_nonneg hs hu), Real.sqrt_mul (mul_nonneg hA hB)]
  ring

private lemma d_core_real {s u σx σx' σy σy' U V Us Vs Uu Vu b e bs es bu eu c θs θu : ℝ}
    (hs : 0 < s) (hu : 0 < u)
    (hσx : 0 < σx) (hσx' : 0 < σx') (hσy : 0 < σy) (hσy' : 0 < σy')
    (hU : 0 ≤ U) (hV : 0 ≤ V) (hUs : 0 ≤ Us) (hVs : 0 ≤ Vs) (hUu : 0 ≤ Uu) (hVu : 0 ≤ Vu)
    (hb : 0 ≤ b) (he : 0 ≤ e) (hbs : 0 ≤ bs) (hes : 0 ≤ es) (hbu : 0 ≤ bu) (heu : 0 ≤ eu)
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (hθs : θs ∈ Icc (0 : ℝ) 1) (hθu : θu ∈ Icc (0 : ℝ) 1)
    (hUle : U ≤ Real.sqrt (Us * Uu)) (hVle : V ≤ Real.sqrt (Vs * Vu))
    (hble : b ≤ c * Real.sqrt (bs * bu)) (hele : e ≤ c * Real.sqrt (es * eu))
    (hs1 : s ^ 2 * Us * σx' ^ 2 * es * σx + s * Us * bs * σx' ≤ (1 - θs) * σx)
    (hs2 : s * Vs * bs * σx + s ^ 2 * Vs * σx ^ 2 * es * σx' ≤ (1 - θs) * σx')
    (hu1 : u ^ 2 * Uu * σy' ^ 2 * eu * σy + u * Uu * bu * σy' ≤ (1 - θu) * σy)
    (hu2 : u * Vu * bu * σy + u ^ 2 * Vu * σy ^ 2 * eu * σy' ≤ (1 - θu) * σy') :
    (1 - c * Real.sqrt ((1 - θs) * (1 - θu))) ^ 2 ≤
      (1 - s * u * U * σx' * σy' * e) * (1 - s * u * V * σx * σy * e) - s * u * U * V * b ^ 2 := by
  rcases hc0.eq_or_lt with hc | hc
  · subst hc
    have hb0 : b = 0 := le_antisymm (by simpa using hble) hb
    have he0 : e = 0 := le_antisymm (by simpa using hele) he
    simp [hb0, he0]
  · have hsu : 0 ≤ s * u := by positivity
    set L : Matrix (Fin 2) (Fin 2) ℝ :=
      !![s * u * U * σx' * σy' * e, Real.sqrt (s * u) * U * b;
        Real.sqrt (s * u) * V * b, s * u * V * σx * σy * e] with hL
    set Ls : Matrix (Fin 2) (Fin 2) ℝ :=
      !![s ^ 2 * Us * σx' ^ 2 * es, s * Us * bs; s * Vs * bs, s ^ 2 * Vs * σx ^ 2 * es] with hLs
    set Lu : Matrix (Fin 2) (Fin 2) ℝ :=
      !![u ^ 2 * Uu * σy' ^ 2 * eu, u * Uu * bu; u * Vu * bu, u ^ 2 * Vu * σy ^ 2 * eu] with hLu
    have key := lem_app_vol_closed_perron L Ls Lu c hc hc1 ?_ ?_ ?_ ?_ ![σx, σx'] ![σy, σy']
      ?_ ?_ θs θu hθs hθu ?_ ?_
    · have hdet : (1 - L).det = (1 - s * u * U * σx' * σy' * e) * (1 - s * u * V * σx * σy * e)
          - s * u * U * V * b ^ 2 := by
        simp only [hL, Matrix.det_fin_two, Matrix.sub_apply, Matrix.one_apply, Matrix.of_apply,
          Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
          Matrix.cons_val_fin_one]
        simp
        have h := Real.mul_self_sqrt hsu
        linear_combination (U * V * b ^ 2) * h
      rw [hdet] at key
      exact key
    · intro k l
      fin_cases k <;> fin_cases l <;> simp [hL] <;> positivity
    · intro k l
      fin_cases k <;> fin_cases l <;> simp [hLs] <;> positivity
    · intro k l
      fin_cases k <;> fin_cases l <;> simp [hLu] <;> positivity
    · intro k l
      have hsq : 0 ≤ Real.sqrt (Us * Uu) := Real.sqrt_nonneg _
      have hUU : U * e ≤ Real.sqrt (Us * Uu) * (c * Real.sqrt (es * eu)) :=
        mul_le_mul hUle hele he hsq
      have hVV : V * e ≤ Real.sqrt (Vs * Vu) * (c * Real.sqrt (es * eu)) :=
        mul_le_mul hVle hele he (Real.sqrt_nonneg _)
      have hUb : U * b ≤ Real.sqrt (Us * Uu) * (c * Real.sqrt (bs * bu)) :=
        mul_le_mul hUle hble hb hsq
      have hVb : V * b ≤ Real.sqrt (Vs * Vu) * (c * Real.sqrt (bs * bu)) :=
        mul_le_mul hVle hble hb (Real.sqrt_nonneg _)
      fin_cases k <;> fin_cases l
      · simp only [hL, hLs, hLu, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
          Matrix.empty_val', Matrix.cons_val_fin_one, Fin.zero_eta,
          Fin.isValue]
        rw [d_sqrt_four hs.le hu.le hσx'.le hσy'.le hUs hUu hes heu]
        have h0 : 0 ≤ s * u * σx' * σy' := by positivity
        calc s * u * U * σx' * σy' * e = (s * u * σx' * σy') * (U * e) := by ring
          _ ≤ (s * u * σx' * σy') * (Real.sqrt (Us * Uu) * (c * Real.sqrt (es * eu))) :=
            mul_le_mul_of_nonneg_left hUU h0
          _ = _ := by ring
      · simp only [hL, hLs, hLu, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
          Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, Fin.zero_eta,
          Fin.isValue, Fin.mk_one]
        rw [d_sqrt_two hs.le hu.le hUs hUu hbs hbu]
        have h0 : 0 ≤ Real.sqrt (s * u) := Real.sqrt_nonneg _
        calc Real.sqrt (s * u) * U * b = Real.sqrt (s * u) * (U * b) := by ring
          _ ≤ Real.sqrt (s * u) * (Real.sqrt (Us * Uu) * (c * Real.sqrt (bs * bu))) :=
            mul_le_mul_of_nonneg_left hUb h0
          _ = _ := by ring
      · simp only [hL, hLs, hLu, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
          Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, Fin.zero_eta,
          Fin.isValue, Fin.mk_one]
        rw [d_sqrt_two hs.le hu.le hVs hVu hbs hbu]
        have h0 : 0 ≤ Real.sqrt (s * u) := Real.sqrt_nonneg _
        calc Real.sqrt (s * u) * V * b = Real.sqrt (s * u) * (V * b) := by ring
          _ ≤ Real.sqrt (s * u) * (Real.sqrt (Vs * Vu) * (c * Real.sqrt (bs * bu))) :=
            mul_le_mul_of_nonneg_left hVb h0
          _ = _ := by ring
      · simp only [hL, hLs, hLu, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
          Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, Fin.zero_eta,
          Fin.isValue, Fin.mk_one]
        rw [d_sqrt_four hs.le hu.le hσx.le hσy.le hVs hVu hes heu]
        have h0 : 0 ≤ s * u * σx * σy := by positivity
        calc s * u * V * σx * σy * e = (s * u * σx * σy) * (V * e) := by ring
          _ ≤ (s * u * σx * σy) * (Real.sqrt (Vs * Vu) * (c * Real.sqrt (es * eu))) :=
            mul_le_mul_of_nonneg_left hVV h0
          _ = _ := by ring
    · intro k; fin_cases k <;> simp [hσx, hσx']
    · intro k; fin_cases k <;> simp [hσy, hσy']
    · intro k
      fin_cases k
      · simpa [hLs, Matrix.mulVec, dotProduct, Fin.sum_univ_two] using hs1
      · simp [hLs, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
        linarith
    · intro k
      fin_cases k
      · simpa [hLu, Matrix.mulVec, dotProduct, Fin.sum_univ_two] using hu1
      · simp [hLu, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
        linarith

private lemma d_sum_cs {d : ℕ} {B : ℕ} (μ : Fin d → ℝ) (hμ : ∀ i, 0 ≤ μ i) {s u a a' : ℝ}
    (hs : 0 < s) (hu : 0 < u) (ha : 0 ≤ a) (ha' : 0 ≤ a') :
    (B : ℝ)⁻¹ * ∑ i, μ i ^ 2 / ((s + a * μ i) * (u + a' * μ i)) ≤
      Real.sqrt (((B : ℝ)⁻¹ * ∑ i, μ i ^ 2 / ((s + a * μ i) * (s + a * μ i))) *
        ((B : ℝ)⁻¹ * ∑ i, μ i ^ 2 / ((u + a' * μ i) * (u + a' * μ i)))) := by
  have hB0 : (0 : ℝ) ≤ (B : ℝ)⁻¹ := inv_nonneg.2 (Nat.cast_nonneg _)
  have hd1 : ∀ i, 0 < s + a * μ i := fun i => add_pos_of_pos_of_nonneg hs (mul_nonneg ha (hμ i))
  have hd2 : ∀ i, 0 < u + a' * μ i := fun i => add_pos_of_pos_of_nonneg hu (mul_nonneg ha' (hμ i))
  have h := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ (fun i => μ i / (s + a * μ i))
    (fun i => μ i / (u + a' * μ i))
  have e1 : ∀ i, μ i ^ 2 / ((s + a * μ i) * (u + a' * μ i)) =
      μ i / (s + a * μ i) * (μ i / (u + a' * μ i)) := fun i => by
    rw [div_mul_div_comm, sq]
  have e2 : ∀ i, μ i ^ 2 / ((s + a * μ i) * (s + a * μ i)) = (μ i / (s + a * μ i)) ^ 2 := fun i => by
    rw [div_pow]; ring
  have e3 : ∀ i, μ i ^ 2 / ((u + a' * μ i) * (u + a' * μ i)) = (μ i / (u + a' * μ i)) ^ 2 := fun i => by
    rw [div_pow]; ring
  simp_rw [e1, e2, e3]
  have hf : 0 ≤ ∑ i, (μ i / (s + a * μ i)) ^ 2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hg : 0 ≤ ∑ i, (μ i / (u + a' * μ i)) ^ 2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hprod : ((B : ℝ)⁻¹ * ∑ i, (μ i / (s + a * μ i)) ^ 2) *
      ((B : ℝ)⁻¹ * ∑ i, (μ i / (u + a' * μ i)) ^ 2) =
      ((B : ℝ)⁻¹) ^ 2 * ((∑ i, (μ i / (s + a * μ i)) ^ 2) * ∑ i, (μ i / (u + a' * μ i)) ^ 2) := by
    ring
  rw [hprod, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hB0, Real.sqrt_mul hf]
  exact mul_le_mul_of_nonneg_left h hB0

private lemma d_term_side {μ a s θ : ℝ} (hμ : 0 ≤ μ) (ha : 0 ≤ a) (hs : 0 < s)
    (hθ : θ * (s + a * μ) ≤ s) :
    a * (μ ^ 2 / ((s + a * μ) * (s + a * μ))) ≤ (1 - θ) * (μ / (a * μ + s)) := by
  have hd : 0 < s + a * μ := add_pos_of_pos_of_nonneg hs (mul_nonneg ha hμ)
  have hd' : a * μ + s = s + a * μ := add_comm _ _
  rw [hd']
  have : (1 - θ) * (μ / (s + a * μ)) - a * (μ ^ 2 / ((s + a * μ) * (s + a * μ))) =
      μ * (s - θ * (s + a * μ)) / ((s + a * μ) * (s + a * μ)) := by
    field_simp
    ring
  have h2 : 0 ≤ μ * (s - θ * (s + a * μ)) / ((s + a * μ) * (s + a * μ)) :=
    div_nonneg (mul_nonneg hμ (by linarith)) (by positivity)
  linarith

private lemma d_tout_eq {m n B : ℕ} (C : Muon.Covariances m n) (x y : ℝ × ℝ × ℝ × ℝ) {s u : ℝ}
    (hs : 0 < s) (hu : 0 < u) (hax : 0 ≤ x.2.2.1) (hay : 0 ≤ y.2.2.1) :
    toutT C B x y s u C.Sout = (B : ℝ)⁻¹ * ∑ i, C.psdOut.isHermitian.eigenvalues i ^ 2 /
      ((s + x.2.2.1 * C.psdOut.isHermitian.eigenvalues i) *
        (u + y.2.2.1 * C.psdOut.isHermitian.eigenvalues i)) := by
  unfold toutT
  rw [d_trace_two C.psdOut hs hu hax hay]

private lemma d_tin_eq {m n B : ℕ} (C : Muon.Covariances m n) (x y : ℝ × ℝ × ℝ × ℝ) {s u : ℝ}
    (hs : 0 < s) (hu : 0 < u) (hax : 0 ≤ x.2.2.2) (hay : 0 ≤ y.2.2.2) :
    tinT C B x y s u C.Sin = (B : ℝ)⁻¹ * ∑ i, C.psdIn.isHermitian.eigenvalues i ^ 2 /
      ((s + x.2.2.2 * C.psdIn.isHermitian.eigenvalues i) *
        (u + y.2.2.2 * C.psdIn.isHermitian.eigenvalues i)) := by
  unfold tinT
  rw [d_trace_two C.psdIn hs hu hax hay]

private lemma d_sum_nonneg {d B : ℕ} (μ : Fin d → ℝ) (hμ : ∀ i, 0 ≤ μ i) {s u a a' : ℝ}
    (hs : 0 < s) (hu : 0 < u) (ha : 0 ≤ a) (ha' : 0 ≤ a') :
    0 ≤ (B : ℝ)⁻¹ * ∑ i, μ i ^ 2 / ((s + a * μ i) * (u + a' * μ i)) := by
  have hd1 : ∀ i, 0 < s + a * μ i := fun i => add_pos_of_pos_of_nonneg hs (mul_nonneg ha (hμ i))
  have hd2 : ∀ i, 0 < u + a' * μ i := fun i => add_pos_of_pos_of_nonneg hu (mul_nonneg ha' (hμ i))
  exact mul_nonneg (inv_nonneg.2 (Nat.cast_nonneg _))
    (Finset.sum_nonneg (fun i _ => div_nonneg (sq_nonneg _) (mul_pos (hd1 i) (hd2 i)).le))

private lemma d_tout_nonneg {m n B : ℕ} (C : Muon.Covariances m n) (x y : ℝ × ℝ × ℝ × ℝ) {s u : ℝ}
    (hs : 0 < s) (hu : 0 < u) (hax : 0 ≤ x.2.2.1) (hay : 0 ≤ y.2.2.1) :
    0 ≤ toutT C B x y s u C.Sout := by
  rw [d_tout_eq C x y hs hu hax hay]
  exact d_sum_nonneg _ C.psdOut.eigenvalues_nonneg hs hu hax hay

private lemma d_tin_nonneg {m n B : ℕ} (C : Muon.Covariances m n) (x y : ℝ × ℝ × ℝ × ℝ) {s u : ℝ}
    (hs : 0 < s) (hu : 0 < u) (hax : 0 ≤ x.2.2.2) (hay : 0 ≤ y.2.2.2) :
    0 ≤ tinT C B x y s u C.Sin := by
  rw [d_tin_eq C x y hs hu hax hay]
  exact d_sum_nonneg _ C.psdIn.eigenvalues_nonneg hs hu hax hay

private lemma d_tout_le {m n B : ℕ} (C : Muon.Covariances m n) (x y : ℝ × ℝ × ℝ × ℝ) {s u : ℝ}
    (hs : 0 < s) (hu : 0 < u) (hax : 0 ≤ x.2.2.1) (hay : 0 ≤ y.2.2.1) :
    toutT C B x y s u C.Sout ≤
      Real.sqrt (toutT C B x x s s C.Sout * toutT C B y y u u C.Sout) := by
  rw [d_tout_eq C x y hs hu hax hay, d_tout_eq C x x hs hs hax hax, d_tout_eq C y y hu hu hay hay]
  exact d_sum_cs _ C.psdOut.eigenvalues_nonneg hs hu hax hay

private lemma d_tin_le {m n B : ℕ} (C : Muon.Covariances m n) (x y : ℝ × ℝ × ℝ × ℝ) {s u : ℝ}
    (hs : 0 < s) (hu : 0 < u) (hax : 0 ≤ x.2.2.2) (hay : 0 ≤ y.2.2.2) :
    tinT C B x y s u C.Sin ≤
      Real.sqrt (tinT C B x x s s C.Sin * tinT C B y y u u C.Sin) := by
  rw [d_tin_eq C x y hs hu hax hay, d_tin_eq C x x hs hs hax hax, d_tin_eq C y y hu hu hay hay]
  exact d_sum_cs _ C.psdIn.eigenvalues_nonneg hs hu hax hay

/-- side supersolution, output component: `ã 𝖴_t ≤ (1-θ) σ` when `θ (s + ã μ_i) ≤ s` for all `i`. -/
private lemma d_side_out {m n B : ℕ} (C : Muon.Covariances m n)
    {s : ℝ} (hs : 0 < s) {x : ℝ × ℝ × ℝ × ℝ} {F : ℝ → ℝ} (hx : IsBranchPoint F C B s x)
    {θ : ℝ} (hθ : ∀ i, θ * (s + x.2.2.1 * C.psdOut.isHermitian.eigenvalues i) ≤ s) :
    x.2.2.1 * toutT C B x x s s C.Sout ≤ (1 - θ) * x.1 := by
  obtain ⟨hσ0, hσ'0, ha0, hc0, hσ, hσ', ha, hc⟩ := hx
  rw [d_tout_eq C x x hs hs ha0 ha0]
  have hσ2 : x.1 = (B : ℝ)⁻¹ * ∑ i, C.psdOut.isHermitian.eigenvalues i /
      (x.2.2.1 * C.psdOut.isHermitian.eigenvalues i + s) := by
    rw [hσ, p3_trace_resolvent C.psdOut hs ha0]
  have k1 : x.2.2.1 * ((B : ℝ)⁻¹ * ∑ i, C.psdOut.isHermitian.eigenvalues i ^ 2 /
      ((s + x.2.2.1 * C.psdOut.isHermitian.eigenvalues i) *
        (s + x.2.2.1 * C.psdOut.isHermitian.eigenvalues i))) =
      (B : ℝ)⁻¹ * ∑ i, x.2.2.1 * (C.psdOut.isHermitian.eigenvalues i ^ 2 /
      ((s + x.2.2.1 * C.psdOut.isHermitian.eigenvalues i) *
        (s + x.2.2.1 * C.psdOut.isHermitian.eigenvalues i))) := by
    rw [← Finset.mul_sum]; ring
  have k2 : (1 - θ) * ((B : ℝ)⁻¹ * ∑ i, C.psdOut.isHermitian.eigenvalues i /
      (x.2.2.1 * C.psdOut.isHermitian.eigenvalues i + s)) =
      (B : ℝ)⁻¹ * ∑ i, (1 - θ) * (C.psdOut.isHermitian.eigenvalues i /
      (x.2.2.1 * C.psdOut.isHermitian.eigenvalues i + s)) := by
    rw [← Finset.mul_sum]; ring
  rw [hσ2, k1, k2]
  refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i _ => ?_)) (by positivity : (0:ℝ) ≤ (B:ℝ)⁻¹)
  exact d_term_side (C.psdOut.eigenvalues_nonneg i) ha0 hs (hθ i)

private lemma d_side_in {m n B : ℕ} (C : Muon.Covariances m n)
    {s : ℝ} (hs : 0 < s) {x : ℝ × ℝ × ℝ × ℝ} {F : ℝ → ℝ} (hx : IsBranchPoint F C B s x)
    {θ : ℝ} (hθ : ∀ i, θ * (s + x.2.2.2 * C.psdIn.isHermitian.eigenvalues i) ≤ s) :
    x.2.2.2 * tinT C B x x s s C.Sin ≤ (1 - θ) * x.2.1 := by
  obtain ⟨hσ0, hσ'0, ha0, hc0, hσ, hσ', ha, hc⟩ := hx
  rw [d_tin_eq C x x hs hs hc0 hc0]
  have hσ2 : x.2.1 = (B : ℝ)⁻¹ * ∑ i, C.psdIn.isHermitian.eigenvalues i /
      (x.2.2.2 * C.psdIn.isHermitian.eigenvalues i + s) := by
    rw [hσ', p3_trace_resolvent C.psdIn hs hc0]
  have k1 : x.2.2.2 * ((B : ℝ)⁻¹ * ∑ i, C.psdIn.isHermitian.eigenvalues i ^ 2 /
      ((s + x.2.2.2 * C.psdIn.isHermitian.eigenvalues i) *
        (s + x.2.2.2 * C.psdIn.isHermitian.eigenvalues i))) =
      (B : ℝ)⁻¹ * ∑ i, x.2.2.2 * (C.psdIn.isHermitian.eigenvalues i ^ 2 /
      ((s + x.2.2.2 * C.psdIn.isHermitian.eigenvalues i) *
        (s + x.2.2.2 * C.psdIn.isHermitian.eigenvalues i))) := by
    rw [← Finset.mul_sum]; ring
  have k2 : (1 - θ) * ((B : ℝ)⁻¹ * ∑ i, C.psdIn.isHermitian.eigenvalues i /
      (x.2.2.2 * C.psdIn.isHermitian.eigenvalues i + s)) =
      (B : ℝ)⁻¹ * ∑ i, (1 - θ) * (C.psdIn.isHermitian.eigenvalues i /
      (x.2.2.2 * C.psdIn.isHermitian.eigenvalues i + s)) := by
    rw [← Finset.mul_sum]; ring
  rw [hσ2, k1, k2]
  refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i _ => ?_)) (by positivity : (0:ℝ) ≤ (B:ℝ)⁻¹)
  exact d_term_side (C.psdIn.eigenvalues_nonneg i) hc0 hs (hθ i)

private lemma d_core {m n B : ℕ} (hB : 0 < B) {P : Measure Ω} [IsProbabilityMeasure P]
    {ξ₁ ξ₂ : ι → Ω → ℝ} (hξ : def_app_vol_closed_profile_ii P ξ₁ ξ₂)
    (C : Muon.Covariances m n) (hout : C.Sout ≠ 0) (hin : C.Sin ≠ 0) {s u : ℝ}
    (hs : 0 < s) (hu : 0 < u)
    {x y : ℝ × ℝ × ℝ × ℝ} (hx : IsBranchPoint (profileF P ξ₁) C B s x)
    (hy : IsBranchPoint (profileF P ξ₂) C B u y)
    {c θs θu : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (hθs : θs ∈ Icc (0 : ℝ) 1)
    (hθu : θu ∈ Icc (0 : ℝ) 1)
    (hs1 : x.2.2.1 * toutT C B x x s s C.Sout ≤ (1 - θs) * x.1)
    (hs2 : x.2.2.2 * tinT C B x x s s C.Sin ≤ (1 - θs) * x.2.1)
    (hu1 : y.2.2.1 * toutT C B y y u u C.Sout ≤ (1 - θu) * y.1)
    (hu2 : y.2.2.2 * tinT C B y y u u C.Sin ≤ (1 - θu) * y.2.1)
    (hble : pairedB P ξ₁ ξ₂ (s * x.1 * x.2.1) (u * y.1 * y.2.1) ≤
      c * Real.sqrt (profileRDeriv P ξ₁ (s * x.1 * x.2.1) * profileRDeriv P ξ₂ (u * y.1 * y.2.1)))
    (hele : pairedE P ξ₁ ξ₂ (s * x.1 * x.2.1) (u * y.1 * y.2.1) ≤
      c * Real.sqrt (profileNegFDeriv P ξ₁ (s * x.1 * x.2.1) *
        profileNegFDeriv P ξ₂ (u * y.1 * y.2.1))) :
    (1 - c * Real.sqrt ((1 - θs) * (1 - θu))) ^ 2 ≤
      closedDelta C B x y s u (pairedB P ξ₁ ξ₂ (s * x.1 * x.2.1) (u * y.1 * y.2.1))
        (pairedE P ξ₁ ξ₂ (s * x.1 * x.2.1) (u * y.1 * y.2.1)) := by
  have hBr : (0 : ℝ) < B := by exact_mod_cast hB
  obtain ⟨hσ0, hσ'0, ha0, hc0', hσ, hσ', ha, hc⟩ := hx
  obtain ⟨hτ0, hτ'0, hb0, hd0, hτ, hτ', hb, hd⟩ := hy
  have hσp : 0 < x.1 := by
    rw [hσ]; exact mul_pos (inv_pos.2 hBr) (p3_trace_resolvent_pos C.psdOut hout hs ha0)
  have hσ'p : 0 < x.2.1 := by
    rw [hσ']; exact mul_pos (inv_pos.2 hBr) (p3_trace_resolvent_pos C.psdIn hin hs hc0')
  have hτp : 0 < y.1 := by
    rw [hτ]; exact mul_pos (inv_pos.2 hBr) (p3_trace_resolvent_pos C.psdOut hout hu hb0)
  have hτ'p : 0 < y.2.1 := by
    rw [hτ']; exact mul_pos (inv_pos.2 hBr) (p3_trace_resolvent_pos C.psdIn hin hu hd0)
  have hq : 0 < s * x.1 * x.2.1 := by positivity
  have hq' : 0 < u * y.1 * y.2.1 := by positivity
  obtain ⟨-, -, -, -, -, -, -, -, -, hR1, hF1, hid1⟩ := lem_app_vol_closed_profile_i hξ.profile₁
  obtain ⟨-, -, -, -, -, -, -, -, -, hR2, hF2, hid2⟩ := lem_app_vol_closed_profile_i hξ.profile₂
  obtain ⟨-, -, -, -, -, -, hBb, hEb⟩ := lem_app_vol_closed_profile_iii hξ
  have hbs : 0 ≤ profileRDeriv P ξ₁ (s * x.1 * x.2.1) := (hR1 _ (mem_Ici.2 hq.le)).le
  have hbu : 0 ≤ profileRDeriv P ξ₂ (u * y.1 * y.2.1) := (hR2 _ (mem_Ici.2 hq'.le)).le
  have hes : 0 ≤ profileNegFDeriv P ξ₁ (s * x.1 * x.2.1) := (hF1 _ hq).2
  have heu : 0 ≤ profileNegFDeriv P ξ₂ (u * y.1 * y.2.1) := (hF2 _ hq').2
  have hbb := hBb _ (mem_Ici.2 hq.le) _ (mem_Ici.2 hq'.le)
  have hee := hEb _ hq _ hq'
  have hkx : x.2.2.1 = s * x.2.1 * (profileRDeriv P ξ₁ (s * x.1 * x.2.1) +
      (s * x.1 * x.2.1) * profileNegFDeriv P ξ₁ (s * x.1 * x.2.1)) := by
    rw [hid1 _ hq]; exact ha
  have hky : y.2.2.1 = u * y.2.1 * (profileRDeriv P ξ₂ (u * y.1 * y.2.1) +
      (u * y.1 * y.2.1) * profileNegFDeriv P ξ₂ (u * y.1 * y.2.1)) := by
    rw [hid2 _ hq']; exact hb
  have hkx' : x.2.2.2 = s * x.1 * (profileRDeriv P ξ₁ (s * x.1 * x.2.1) +
      (s * x.1 * x.2.1) * profileNegFDeriv P ξ₁ (s * x.1 * x.2.1)) := by
    rw [hid1 _ hq]; exact hc
  have hky' : y.2.2.2 = u * y.1 * (profileRDeriv P ξ₂ (u * y.1 * y.2.1) +
      (u * y.1 * y.2.1) * profileNegFDeriv P ξ₂ (u * y.1 * y.2.1)) := by
    rw [hid2 _ hq']; exact hd
  unfold closedDelta
  refine d_core_real hs hu hσp hσ'p hτp hτ'p (d_tout_nonneg C x y hs hu ha0 hb0)
    (d_tin_nonneg C x y hs hu hc0' hd0) (d_tout_nonneg C x x hs hs ha0 ha0)
    (d_tin_nonneg C x x hs hs hc0' hc0') (d_tout_nonneg C y y hu hu hb0 hb0)
    (d_tin_nonneg C y y hu hu hd0 hd0) hbb.1 hee.1 hbs hes hbu heu hc0 hc1 hθs hθu
    (d_tout_le C x y hs hu ha0 hb0) (d_tin_le C x y hs hu hc0' hd0) hble hele ?_ ?_ ?_ ?_
  · rw [hkx] at hs1
    exact (le_of_eq (by ring)).trans hs1
  · rw [hkx'] at hs2
    exact (le_of_eq (by ring)).trans hs2
  · rw [hky] at hu1
    exact (le_of_eq (by ring)).trans hu1
  · rw [hky'] at hu2
    exact (le_of_eq (by ring)).trans hu2

private lemma d_kappa_nonneg {m n B : ℕ} (C : Muon.Covariances m n) : 0 ≤ kappaSigma C B := by
  unfold kappaSigma
  refine le_max_of_le_left (mul_nonneg (mul_nonneg (by positivity) C.psdIn.trace_nonneg)
    (norm_nonneg _))

private lemma d_theta_mem {m n B : ℕ} (C : Muon.Covariances m n) {t : ℝ} (ht : 0 < t) :
    thetaSigma C B t ∈ Icc (0 : ℝ) 1 := by
  have hk := d_kappa_nonneg (B := B) C
  unfold thetaSigma
  exact ⟨div_nonneg ht.le (by linarith), (div_le_one (by linarith)).2 (by linarith)⟩

private lemma d_theta_mono {m n B : ℕ} (C : Muon.Covariances m n) {t t' : ℝ} (ht : 0 < t)
    (htt : t ≤ t') : thetaSigma C B t ≤ thetaSigma C B t' := by
  have hk := d_kappa_nonneg (B := B) C
  unfold thetaSigma
  rw [div_le_div_iff₀ (by linarith) (by linarith)]
  nlinarith

private lemma d_theta_out {m n B : ℕ} (C : Muon.Covariances m n) {t a F0 : ℝ} (ht : 0 < t)
    (ha0 : 0 ≤ a) (haF : a ≤ C.Sin.trace / B * F0) (hF0 : F0 ≤ 1) (i : Fin m) :
    thetaSigma C B t * (t + a * C.psdOut.isHermitian.eigenvalues i) ≤ t := by
  have hk := d_kappa_nonneg (B := B) C
  have hT : 0 ≤ C.Sin.trace / B := div_nonneg C.psdIn.trace_nonneg (Nat.cast_nonneg _)
  have ha : a ≤ C.Sin.trace / B := haF.trans (mul_le_of_le_one_right hT hF0)
  have hμ0 := C.psdOut.eigenvalues_nonneg i
  have hμ := d_eig_le_opNorm C.psdOut i
  have h1 : a * C.psdOut.isHermitian.eigenvalues i ≤ kappaSigma C B := by
    calc a * C.psdOut.isHermitian.eigenvalues i ≤ (C.Sin.trace / B) * Muon.opNorm C.Sout :=
          mul_le_mul ha hμ hμ0 hT
      _ = (B : ℝ)⁻¹ * C.Sin.trace * Muon.opNorm C.Sout := by ring
      _ ≤ kappaSigma C B := le_max_left _ _
  unfold thetaSigma
  rw [div_mul_eq_mul_div, div_le_iff₀ (by linarith)]
  nlinarith

private lemma d_theta_in {m n B : ℕ} (C : Muon.Covariances m n) {t a F0 : ℝ} (ht : 0 < t)
    (ha0 : 0 ≤ a) (haF : a ≤ C.Sout.trace / B * F0) (hF0 : F0 ≤ 1) (i : Fin n) :
    thetaSigma C B t * (t + a * C.psdIn.isHermitian.eigenvalues i) ≤ t := by
  have hk := d_kappa_nonneg (B := B) C
  have hT : 0 ≤ C.Sout.trace / B := div_nonneg C.psdOut.trace_nonneg (Nat.cast_nonneg _)
  have ha : a ≤ C.Sout.trace / B := haF.trans (mul_le_of_le_one_right hT hF0)
  have hμ0 := C.psdIn.eigenvalues_nonneg i
  have hμ := d_eig_le_opNorm C.psdIn i
  have h1 : a * C.psdIn.isHermitian.eigenvalues i ≤ kappaSigma C B := by
    calc a * C.psdIn.isHermitian.eigenvalues i ≤ (C.Sout.trace / B) * Muon.opNorm C.Sin :=
          mul_le_mul ha hμ hμ0 hT
      _ = (B : ℝ)⁻¹ * C.Sout.trace * Muon.opNorm C.Sin := by ring
      _ ≤ kappaSigma C B := le_max_right _ _
  unfold thetaSigma
  rw [div_mul_eq_mul_div, div_le_iff₀ (by linarith)]
  nlinarith


private lemma d_gauss_compl_pos : (0 : ENNReal) < gaussianReal 0 1 ({(0 : ℝ)}ᶜ) := by
  have h0 : gaussianReal 0 1 {(0 : ℝ)} = 0 :=
    gaussianReal_absolutelyContinuous 0 one_ne_zero Real.volume_singleton
  have h1 : gaussianReal 0 1 ({(0 : ℝ)}ᶜ) = 1 := by
    rw [measure_compl (measurableSet_singleton 0) (by simp [h0]), h0]
    simp
  rw [h1]
  exact one_pos

private lemma d_H_den {a : ℝ} (ha : 0 ≤ a) (g : ℝ) : 0 < (1 + a * g ^ 2) ^ 2 := by
  have := mul_nonneg ha (sq_nonneg g)
  positivity

private lemma d_H_integrable {w : ℝ → ℝ} (hw : Integrable w (gaussianReal 0 1))
    (hw0 : ∀ g, 0 ≤ w g) (hwm : Measurable w) {a : ℝ} (ha : 0 ≤ a) :
    Integrable (fun g => w g / (1 + a * g ^ 2) ^ 2) (gaussianReal 0 1) := by
  refine Integrable.mono' hw
    (hwm.div (by fun_prop : Measurable fun g : ℝ => (1 + a * g ^ 2) ^ 2)).aestronglyMeasurable ?_
  refine Filter.Eventually.of_forall fun g => ?_
  rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (hw0 g) (d_H_den ha g).le)]
  refine div_le_self (hw0 g) ?_
  have := mul_nonneg ha (sq_nonneg g)
  nlinarith

private lemma d_H_pos {w : ℝ → ℝ} (hw : Integrable w (gaussianReal 0 1))
    (hw0 : ∀ g, 0 ≤ w g) (hwm : Measurable w) (hwp : ∀ g, g ≠ 0 → 0 < w g) {a : ℝ} (ha : 0 ≤ a) :
    0 < ∫ g, w g / (1 + a * g ^ 2) ^ 2 ∂(gaussianReal 0 1) := by
  rw [integral_pos_iff_support_of_nonneg (fun g => div_nonneg (hw0 g) (d_H_den ha g).le)
    (d_H_integrable hw hw0 hwm ha)]
  refine lt_of_lt_of_le d_gauss_compl_pos (measure_mono ?_)
  intro g hg
  have hg0 : g ≠ 0 := hg
  change w g / (1 + a * g ^ 2) ^ 2 ≠ 0
  exact (div_pos (hwp g hg0) (d_H_den ha g)).ne'

private lemma d_H_anti {w : ℝ → ℝ} (hw : Integrable w (gaussianReal 0 1))
    (hw0 : ∀ g, 0 ≤ w g) (hwm : Measurable w) {a a' : ℝ} (ha : 0 ≤ a) (haa : a ≤ a') :
    ∫ g, w g / (1 + a' * g ^ 2) ^ 2 ∂(gaussianReal 0 1) ≤
      ∫ g, w g / (1 + a * g ^ 2) ^ 2 ∂(gaussianReal 0 1) := by
  have ha' : 0 ≤ a' := ha.trans haa
  refine integral_mono (d_H_integrable hw hw0 hwm ha') (d_H_integrable hw hw0 hwm ha) (fun g => ?_)
  refine div_le_div_of_nonneg_left (hw0 g) (d_H_den ha g) ?_
  have : 1 + a * g ^ 2 ≤ 1 + a' * g ^ 2 := by nlinarith [sq_nonneg g]
  have h1 : 0 ≤ 1 + a * g ^ 2 := by have := mul_nonneg ha (sq_nonneg g); linarith
  nlinarith


private lemma d_emaW_weightSeq {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) :
    Muon.DetEquiv.WeightSeq (Muon.emaW β) := by
  refine ⟨fun j => ?_, ?_, 0, ?_⟩
  · unfold Muon.emaW
    exact mul_nonneg (by linarith) (pow_nonneg hβ0 j)
  · unfold Muon.emaW
    exact (summable_geometric_of_lt_one hβ0 hβ1).mul_left _
  · unfold Muon.emaW
    rw [pow_zero, mul_one]
    exact (by linarith : (0:ℝ) < 1 - β).ne'

private lemma d_ema_qhat_bdd {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (γ : ℝ) :
    BddAbove {q : ℝ | 0 ≤ q ∧ Muon.DetEquiv.rW (Muon.emaW β) q ≤ γ} := by
  have hw := d_emaW_weightSeq hβ0.le hβ1
  have h := (Muon.DetEquiv.lem_app_de_scalar_iii hw).2.2.2.2.2.2
  have hset : {j : ℕ | 0 < Muon.emaW β j} = Set.univ := by
    ext j
    simp only [mem_setOf_eq, mem_univ, iff_true]
    unfold Muon.emaW
    exact mul_pos (by linarith) (pow_pos hβ0 j)
  rw [hset, Set.encard_univ] at h
  have htop : (ENat.card ℕ).toENNReal = ⊤ := by simp
  rw [htop] at h
  have hev := h.eventually_const_lt (ENNReal.ofReal_lt_top (r := γ))
  obtain ⟨Q, hQ⟩ := eventually_atTop.1 hev
  refine ⟨Q, fun q hq => ?_⟩
  by_contra hlt
  push_neg at hlt
  have h1 := hQ q hlt.le
  have h2 := (ENNReal.ofReal_lt_ofReal_iff'.1 h1).1
  linarith [hq.2]

private lemma d_law_int {P : Measure Ω} {g' : Ω → ℝ} (hg : HasLaw g' (gaussianReal 0 1) P)
    (c q : ℝ) (p : ℕ) :
    ∫ ω, (c * g' ω) ^ p / (1 + q * (c * g' ω) ^ 2) ^ 2 ∂P =
      c ^ p * ∫ x, x ^ p / (1 + q * c ^ 2 * x ^ 2) ^ 2 ∂(gaussianReal 0 1) := by
  have hφ : Measurable (fun x : ℝ => x ^ p / (1 + q * c ^ 2 * x ^ 2) ^ 2) := by fun_prop
  have h := hg.integral_comp (f := fun x : ℝ => x ^ p / (1 + q * c ^ 2 * x ^ 2) ^ 2)
    hφ.aestronglyMeasurable
  rw [← h, ← integral_const_mul]
  refine integral_congr_ae (ae_of_all _ (fun ω => ?_))
  simp only [Function.comp]
  have hd : 1 + q * (c * g' ω) ^ 2 = 1 + q * c ^ 2 * g' ω ^ 2 := by ring
  rw [hd, mul_pow]
  ring

private lemma d_sum_inl_le {ℓ : ℕ} (T : ℕ ⊕ Fin ℓ → ℝ) (hT0 : ∀ a, 0 ≤ T a) (hT : Summable T)
    (i : Fin ℓ) : ∑' j : ℕ, T (Sum.inl j) + T (Sum.inr i) ≤ ∑' a, T a := by
  rw [Summable.tsum_sum (hT.comp_injective Sum.inl_injective) (Summable.of_finite)]
  refine add_le_add le_rfl ?_
  rw [tsum_fintype]
  exact Finset.single_le_sum (f := fun i => T (Sum.inr i)) (fun i _ => hT0 _) (Finset.mem_univ i)


private lemma d_restr_profile_ii {P : Measure Ω} [IsProbabilityMeasure P] {β : ℝ}
    (hβ0 : 0 < β) (hβ1 : β < 1) {ℓ : ℕ} {g : ℕ ⊕ Fin ℓ → Ω → ℝ} (hg : IsStdGaussianFamily P g) :
    def_app_vol_closed_profile_ii P (fun (j : ℕ) ω => Muon.emaW β j * g (Sum.inl j) ω)
      (fun (j : ℕ) ω => β ^ ℓ * Muon.emaW β j * g (Sum.inl j) ω) := by
  have hb : 0 < 1 - β := by linarith
  have hw2 := p2e_w_summable hβ0.le hβ1 (p := 2) (by norm_num)
  have hβℓ : 0 < β ^ ℓ := pow_pos hβ0 ℓ
  refine p2e_pair_family (A := ℕ) (g := fun j => g (Sum.inl j)) (fun j => hg.1 _)
    (fun j => hg.2.2 _) (fun j => Muon.emaW β j) (fun j => β ^ ℓ * Muon.emaW β j) hw2 ?_ ?_ ?_ ?_ ?_
  · simp_rw [mul_pow]
    exact hw2.mul_left _
  · exact ⟨0, by simp [Muon.emaW, hb.ne']⟩
  · exact ⟨0, by simp [Muon.emaW, hb.ne', hβ0.ne']⟩
  · intro j
    exact mul_nonneg (p2e_w_nonneg hβ0.le hβ1 j)
      (mul_nonneg hβℓ.le (p2e_w_nonneg hβ0.le hβ1 j))
  · refine Summable.of_nonneg_of_le (fun j => ?_) (fun j => ?_) (hw2.mul_left ((β ^ ℓ) ^ 2))
    · positivity
    · have h1 := p2e_w_le_one hβ0.le hβ1 j
      have h0 := p2e_w_nonneg hβ0.le hβ1 j
      have : Muon.emaW β j ^ 2 ≤ 1 := by nlinarith
      calc Muon.emaW β j ^ 2 * (β ^ ℓ * Muon.emaW β j) ^ 2
          = (β ^ ℓ) ^ 2 * (Muon.emaW β j ^ 2 * Muon.emaW β j ^ 2) := by ring
        _ ≤ (β ^ ℓ) ^ 2 * Muon.emaW β j ^ 2 := by
          refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
          exact mul_le_of_le_one_left (sq_nonneg _) this

private lemma d_restr_B {P : Measure Ω} (β : ℝ) (ℓ : ℕ) (g : ℕ ⊕ Fin ℓ → Ω → ℝ) (q q' : ℝ) :
    pairedB P (emaXi₁ β ℓ g) (emaXi₂ β ℓ g) q q' =
      pairedB P (fun (j : ℕ) ω => Muon.emaW β j * g (Sum.inl j) ω)
        (fun (j : ℕ) ω => β ^ ℓ * Muon.emaW β j * g (Sum.inl j) ω) q q' := by
  unfold pairedB
  rw [p2e_tsum_inl]
  · rfl
  · intro i
    simp [emaXi₁]

private lemma d_restr_E {P : Measure Ω} (β : ℝ) (ℓ : ℕ) (g : ℕ ⊕ Fin ℓ → Ω → ℝ) (q q' : ℝ) :
    pairedE P (emaXi₁ β ℓ g) (emaXi₂ β ℓ g) q q' =
      pairedE P (fun (j : ℕ) ω => Muon.emaW β j * g (Sum.inl j) ω)
        (fun (j : ℕ) ω => β ^ ℓ * Muon.emaW β j * g (Sum.inl j) ω) q q' := by
  unfold pairedE
  rw [p2e_tsum_inl]
  · rfl
  · intro i
    simp [emaXi₁]

private lemma d_restr_R1 {P : Measure Ω} (β : ℝ) (ℓ : ℕ) (g : ℕ ⊕ Fin ℓ → Ω → ℝ) (q : ℝ) :
    profileRDeriv P (emaXi₁ β ℓ g) q =
      profileRDeriv P (fun (j : ℕ) ω => Muon.emaW β j * g (Sum.inl j) ω) q := by
  unfold profileRDeriv
  rw [p2e_tsum_inl]
  · rfl
  · intro i
    simp [emaXi₁]

private lemma d_restr_N1 {P : Measure Ω} (β : ℝ) (ℓ : ℕ) (g : ℕ ⊕ Fin ℓ → Ω → ℝ) (q : ℝ) :
    profileNegFDeriv P (emaXi₁ β ℓ g) q =
      profileNegFDeriv P (fun (j : ℕ) ω => Muon.emaW β j * g (Sum.inl j) ω) q := by
  unfold profileNegFDeriv
  rw [p2e_tsum_inl]
  · rfl
  · intro i
    simp [emaXi₁]


private lemma d_shared_R {P : Measure Ω} [IsProbabilityMeasure P] {β : ℝ} (hβ0 : 0 < β)
    (hβ1 : β < 1) {ℓ : ℕ} (hℓ : 1 ≤ ℓ) {g : ℕ ⊕ Fin ℓ → Ω → ℝ} (hg : IsStdGaussianFamily P g)
    {q : ℝ} (hq : 0 ≤ q) :
    profileRDeriv P (fun (j : ℕ) ω => β ^ ℓ * Muon.emaW β j * g (Sum.inl j) ω) q +
      Muon.emaW β 0 ^ 2 * ∫ x, x ^ 2 / (1 + q * Muon.emaW β 0 ^ 2 * x ^ 2) ^ 2
        ∂(gaussianReal 0 1) ≤ profileRDeriv P (emaXi₂ β ℓ g) q := by
  have hξ := (p2e_profile_ii hβ0.le hβ1 hg).profile₂
  let i₀ : Fin ℓ := ⟨ℓ - 1, by omega⟩
  have hT := d_sum_inl_le (fun a => ∫ ω, emaXi₂ β ℓ g a ω ^ 2 / (1 + q * emaXi₂ β ℓ g a ω ^ 2) ^ 2 ∂P)
    (fun a => integral_nonneg (p1c_d_nonneg (emaXi₂ β ℓ g a) hq))
    (p1c_summable_d hξ.measurable hξ.integrable_sq hξ.summable_sq hq) i₀
  have h0 : ℓ - (i₀.val + 1) = 0 := by simp [i₀]; omega
  have hinr : (∫ ω, emaXi₂ β ℓ g (Sum.inr i₀) ω ^ 2 /
      (1 + q * emaXi₂ β ℓ g (Sum.inr i₀) ω ^ 2) ^ 2 ∂P) =
      Muon.emaW β 0 ^ 2 * ∫ x, x ^ 2 / (1 + q * Muon.emaW β 0 ^ 2 * x ^ 2) ^ 2
        ∂(gaussianReal 0 1) := by
    simp only [emaXi₂, h0]
    exact d_law_int (hg.2.2 _) _ _ 2
  rw [hinr] at hT
  exact hT

private lemma d_shared_N {P : Measure Ω} [IsProbabilityMeasure P] {β : ℝ} (hβ0 : 0 < β)
    (hβ1 : β < 1) {ℓ : ℕ} (hℓ : 1 ≤ ℓ) {g : ℕ ⊕ Fin ℓ → Ω → ℝ} (hg : IsStdGaussianFamily P g)
    {q : ℝ} (hq : 0 < q) :
    profileNegFDeriv P (fun (j : ℕ) ω => β ^ ℓ * Muon.emaW β j * g (Sum.inl j) ω) q +
      Muon.emaW β 0 ^ 4 * ∫ x, x ^ 4 / (1 + q * Muon.emaW β 0 ^ 2 * x ^ 2) ^ 2
        ∂(gaussianReal 0 1) ≤ profileNegFDeriv P (emaXi₂ β ℓ g) q := by
  have hξ := (p2e_profile_ii hβ0.le hβ1 hg).profile₂
  let i₀ : Fin ℓ := ⟨ℓ - 1, by omega⟩
  have hT := d_sum_inl_le (fun a => ∫ ω, emaXi₂ β ℓ g a ω ^ 4 / (1 + q * emaXi₂ β ℓ g a ω ^ 2) ^ 2 ∂P)
    (fun a => integral_nonneg (p1c_n_nonneg (emaXi₂ β ℓ g a) hq.le))
    (p1c_summable_n hξ.measurable hξ.integrable_sq hξ.summable_sq hq) i₀
  have h0 : ℓ - (i₀.val + 1) = 0 := by simp [i₀]; omega
  have hinr : (∫ ω, emaXi₂ β ℓ g (Sum.inr i₀) ω ^ 4 /
      (1 + q * emaXi₂ β ℓ g (Sum.inr i₀) ω ^ 2) ^ 2 ∂P) =
      Muon.emaW β 0 ^ 4 * ∫ x, x ^ 4 / (1 + q * Muon.emaW β 0 ^ 2 * x ^ 2) ^ 2
        ∂(gaussianReal 0 1) := by
    simp only [emaXi₂, h0]
    exact d_law_int (hg.2.2 _) _ _ 4
  rw [hinr] at hT
  exact hT


private lemma d_derivR {P : Measure Ω} [IsProbabilityMeasure P] {ξ : ι → Ω → ℝ}
    (hξ : def_app_vol_closed_profile P ξ) {r : ℝ → ℝ} (hr : profileR P ξ = r) {q : ℝ} (hq : 0 ≤ q) :
    derivWithin r (Ici 0) q = profileRDeriv P ξ q := by
  have h := (lem_app_vol_closed_profile_i hξ).2.2.2.2.2.2.2.2.1 q (mem_Ici.2 hq)
  rw [hr] at h
  exact h.derivWithin (uniqueDiffOn_Ici 0 q (mem_Ici.2 hq))

private lemma d_law_int0 {P : Measure Ω} {g' : Ω → ℝ} (hg : HasLaw g' (gaussianReal 0 1) P)
    (c : ℝ) :
    ∫ ω, (c * g' ω) ^ 4 ∂P = c ^ 4 * ∫ x, x ^ 4 ∂(gaussianReal 0 1) := by
  have h := d_law_int hg c 0 4
  simpa using h

private lemma d_ema_h4 {P : Measure Ω} [IsProbabilityMeasure P] {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    {ℓ : ℕ} {g : ℕ ⊕ Fin ℓ → Ω → ℝ} (hg : IsStdGaussianFamily P g) :
    (∀ α, Integrable (fun ω => emaXi₁ β ℓ g α ω ^ 4) P) ∧
    Summable (fun α => ∫ ω, emaXi₁ β ℓ g α ω ^ 4 ∂P) := by
  rw [p2e_xi1_eq]
  refine ⟨fun a => p2e_g4_int hg.2.2 _ a, ?_⟩
  simp_rw [fun a => d_law_int0 (hg.2.2 a)]
  refine Summable.mul_right _ ?_
  refine Summable.sum _ ?_ ?_
  · exact p2e_w_summable hβ0 hβ1 (p := 4) (by norm_num)
  · exact Summable.of_finite

private lemma d_N_term_int {P : Measure Ω} {f : Ω → ℝ} (hf : Measurable f)
    (h4 : Integrable (fun ω => f ω ^ 4) P) {q : ℝ} (hq : 0 ≤ q) :
    Integrable (fun ω => f ω ^ 4 / (1 + q * f ω ^ 2) ^ 2) P := by
  refine Integrable.mono' h4 (p1c_meas_n hf q).aestronglyMeasurable (ae_of_all _ (fun ω => ?_))
  rw [Real.norm_eq_abs, abs_of_nonneg (p1c_n_nonneg f hq ω)]
  have h1 : 0 ≤ q * f ω ^ 2 := mul_nonneg hq (sq_nonneg _)
  apply div_le_self (by positivity)
  nlinarith

private lemma d_N_le {P : Measure Ω} [IsProbabilityMeasure P] {ξ : ι → Ω → ℝ}
    (hξ : def_app_vol_closed_profile P ξ) (h4 : ∀ α, Integrable (fun ω => ξ α ω ^ 4) P)
    (hs4 : Summable (fun α => ∫ ω, ξ α ω ^ 4 ∂P)) {q : ℝ} (hq : 0 ≤ q) :
    Summable (fun α => ∫ ω, ξ α ω ^ 4 / (1 + q * ξ α ω ^ 2) ^ 2 ∂P) ∧
    profileNegFDeriv P ξ q ≤ ∑' α, ∫ ω, ξ α ω ^ 4 ∂P := by
  have hle : ∀ α, ∫ ω, ξ α ω ^ 4 / (1 + q * ξ α ω ^ 2) ^ 2 ∂P ≤ ∫ ω, ξ α ω ^ 4 ∂P := by
    intro α
    refine integral_mono (d_N_term_int (hξ.measurable α) (h4 α) hq) (h4 α) (fun ω => ?_)
    have h1 : 0 ≤ q * ξ α ω ^ 2 := mul_nonneg hq (sq_nonneg _)
    apply div_le_self (by positivity)
    nlinarith
  have hsum := Summable.of_nonneg_of_le (fun α => integral_nonneg (p1c_n_nonneg (ξ α) hq)) hle hs4
  exact ⟨hsum, Summable.tsum_le_tsum hle hsum hs4⟩

private lemma d_N_pos {P : Measure Ω} [IsProbabilityMeasure P] {ξ : ι → Ω → ℝ}
    (hξ : def_app_vol_closed_profile P ξ) (h4 : ∀ α, Integrable (fun ω => ξ α ω ^ 4) P)
    (hs4 : Summable (fun α => ∫ ω, ξ α ω ^ 4 ∂P)) {q : ℝ} (hq : 0 ≤ q) :
    0 < profileNegFDeriv P ξ q := by
  obtain ⟨α₀, hα₀⟩ := hξ.exists_ne_zero
  refine (d_N_le hξ h4 hs4 hq).1.tsum_pos
    (fun α => integral_nonneg (p1c_n_nonneg (ξ α) hq)) α₀ ?_
  rw [integral_pos_iff_support_of_nonneg (p1c_n_nonneg (ξ α₀) hq)
    (d_N_term_int (hξ.measurable α₀) (h4 α₀) hq)]
  refine lt_of_lt_of_le hα₀ (measure_mono ?_)
  intro ω hω
  simp only [mem_setOf_eq] at hω
  simp only [Function.mem_support, ne_eq]
  have h1 : 0 < ξ α₀ ω ^ 4 := by positivity
  have h2 : 0 < 1 + q * ξ α₀ ω ^ 2 := p2_den_pos hq
  exact (div_pos h1 (pow_pos h2 2)).ne'

private lemma d_derivF {P : Measure Ω} [IsProbabilityMeasure P] {ξ : ι → Ω → ℝ}
    (hξ : def_app_vol_closed_profile P ξ) (h4 : ∀ α, Integrable (fun ω => ξ α ω ^ 4) P)
    (hs4 : Summable (fun α => ∫ ω, ξ α ω ^ 4 ∂P)) {F : ℝ → ℝ} (hF : profileF P ξ = F)
    {q : ℝ} (hq : 0 ≤ q) :
    -derivWithin F (Ici 0) q = profileNegFDeriv P ξ q := by
  rcases hq.eq_or_lt with h | h
  · subst h
    have := p2e_F_hasDerivWithinAt_zero hξ h4 hs4
    rw [hF] at this
    rw [this.derivWithin (uniqueDiffWithinAt_Ici 0), neg_neg]
  · have := (lem_app_vol_closed_profile_i hξ).2.2.2.2.2.2.2.2.2.2.1 q h
    rw [hF] at this
    rw [(this.1.hasDerivWithinAt (s := Ici 0)).derivWithin (uniqueDiffOn_Ici 0 q (mem_Ici.2 hq)), neg_neg]


private lemma d_R_le {P : Measure Ω} [IsProbabilityMeasure P] {ξ : ι → Ω → ℝ}
    (hξ : def_app_vol_closed_profile P ξ) {q : ℝ} (hq : 0 ≤ q) :
    profileRDeriv P ξ q ≤ ∑' α, ∫ ω, ξ α ω ^ 2 ∂P := by
  unfold profileRDeriv
  exact Summable.tsum_le_tsum
    (fun α => integral_mono (p1c_d_integrable (hξ.measurable α) hq (hξ.integrable_sq α))
      (hξ.integrable_sq α) (fun ω => p1c_d_le (ξ α) hq ω))
    (p1c_summable_d hξ.measurable hξ.integrable_sq hξ.summable_sq hq) hξ.summable_sq

private lemma d_N_eq {P : Measure Ω} [IsProbabilityMeasure P] {ξ₁ ξ₂ : ι → Ω → ℝ}
    (hξ₁ : def_app_vol_closed_profile P ξ₁) (hξ₂ : def_app_vol_closed_profile P ξ₂)
    (hF : profileF P ξ₁ = profileF P ξ₂) {q : ℝ} (hq : 0 < q) :
    profileNegFDeriv P ξ₂ q = profileNegFDeriv P ξ₁ q := by
  have h1 := ((lem_app_vol_closed_profile_i hξ₁).2.2.2.2.2.2.2.2.2.2.1 q hq).1
  have h2 := ((lem_app_vol_closed_profile_i hξ₂).2.2.2.2.2.2.2.2.2.2.1 q hq).1
  rw [hF] at h1
  have := h1.unique h2
  linarith

private lemma d_eps_main {P : Measure Ω} [IsProbabilityMeasure P] {β : ℝ} (hβ0 : 0 < β)
    (hβ1 : β < 1) {ℓ : ℕ} (hℓ : 1 ≤ ℓ) {g : ℕ ⊕ Fin ℓ → Ω → ℝ} (hg : IsStdGaussianFamily P g)
    {γ : ℝ} (hγ : 0 < γ) :
    0 < epsBeta β γ ∧ epsBeta β γ ≤ 1 ∧
    (∀ q : ℝ, 0 ≤ q → q ≤ qhatBeta β γ → epsBeta β γ * profileRDeriv P (emaXi₂ β ℓ g) q ≤
      Muon.emaW β 0 ^ 2 * ∫ x, x ^ 2 / (1 + q * Muon.emaW β 0 ^ 2 * x ^ 2) ^ 2
        ∂(gaussianReal 0 1)) ∧
    (∀ q : ℝ, 0 < q → q ≤ qhatBeta β γ → epsBeta β γ * profileNegFDeriv P (emaXi₂ β ℓ g) q ≤
      Muon.emaW β 0 ^ 4 * ∫ x, x ^ 4 / (1 + q * Muon.emaW β 0 ^ 2 * x ^ 2) ^ 2
        ∂(gaussianReal 0 1)) := by
  have hii := p2e_profile_ii hβ0.le hβ1 hg
  have hξ₁ := hii.profile₁
  have hξ₂ := hii.profile₂
  have hF1 := p2e_F1 (β := β) hg
  have hF2 := p2e_F2 (β := β) hg
  have hr1 : profileR P (emaXi₁ β ℓ g) = Muon.DetEquiv.rW (Muon.emaW β) := by
    funext q; simp only [profileR, Muon.DetEquiv.rW, hF1]
  have hr2 : profileR P (emaXi₂ β ℓ g) = Muon.DetEquiv.rW (Muon.emaW β) := by
    funext q; simp only [profileR, Muon.DetEquiv.rW, hF2]
  obtain ⟨h4, hs4⟩ := d_ema_h4 hβ0.le hβ1 hg
  have he0 : 0 < Muon.emaW β 0 := by simp [Muon.emaW]; linarith
  set e0 := Muon.emaW β 0 with he0def
  set qh := qhatBeta β γ with hqhdef
  have hbdd := d_ema_qhat_bdd hβ0 hβ1 γ
  have hqh0 : 0 ≤ qh := le_csSup hbdd ⟨le_rfl, by simp [Muon.DetEquiv.rW]; exact hγ.le⟩
  -- the two ratios
  set f : ℝ → ℝ := fun q =>
    min ((e0 ^ 2 * ∫ g, g ^ 2 / (1 + q * e0 ^ 2 * g ^ 2) ^ 2 ∂(gaussianReal 0 1)) /
        derivWithin (Muon.DetEquiv.rW (Muon.emaW β)) (Ici 0) q)
      ((e0 ^ 4 * ∫ g, g ^ 4 / (1 + q * e0 ^ 2 * g ^ 2) ^ 2 ∂(gaussianReal 0 1)) /
        (-derivWithin (Muon.DetEquiv.Fw (Muon.emaW β)) (Ici 0) q)) with hf
  have hε : epsBeta β γ = sInf (f '' Icc 0 qh) := rfl
  have hRd : ∀ q, 0 ≤ q → derivWithin (Muon.DetEquiv.rW (Muon.emaW β)) (Ici 0) q =
      profileRDeriv P (emaXi₂ β ℓ g) q := fun q hq => d_derivR hξ₂ hr2 hq
  have hNd : ∀ q, 0 ≤ q → -derivWithin (Muon.DetEquiv.Fw (Muon.emaW β)) (Ici 0) q =
      profileNegFDeriv P (emaXi₁ β ℓ g) q := fun q hq => d_derivF hξ₁ h4 hs4 hF1 hq
  have hRpos : ∀ q, 0 ≤ q → 0 < profileRDeriv P (emaXi₂ β ℓ g) q := fun q hq =>
    (lem_app_vol_closed_profile_i hξ₂).2.2.2.2.2.2.2.2.2.1 q (mem_Ici.2 hq)
  have hNpos : ∀ q, 0 ≤ q → 0 < profileNegFDeriv P (emaXi₁ β ℓ g) q := fun q hq =>
    d_N_pos hξ₁ h4 hs4 hq
  have hK0 : ∀ q, 0 ≤ q → 0 ≤ e0 ^ 2 * ∫ g, g ^ 2 / (1 + q * e0 ^ 2 * g ^ 2) ^ 2 ∂(gaussianReal 0 1) :=
    fun q hq => mul_nonneg (sq_nonneg _) (integral_nonneg (fun x => div_nonneg (sq_nonneg x)
      (d_H_den (mul_nonneg hq (sq_nonneg _)) x).le))
  have hK0' : ∀ q, 0 ≤ q → 0 ≤ e0 ^ 4 * ∫ g, g ^ 4 / (1 + q * e0 ^ 2 * g ^ 2) ^ 2 ∂(gaussianReal 0 1) :=
    fun q hq => mul_nonneg (by positivity) (integral_nonneg (fun x => div_nonneg (by positivity)
      (d_H_den (mul_nonneg hq (sq_nonneg _)) x).le))
  -- lower bounds
  have hw2 : Integrable (fun x : ℝ => x ^ 2) (gaussianReal 0 1) := Muon.Foundations.gaussian_integrable_pow 2
  have hw4 : Integrable (fun x : ℝ => x ^ 4) (gaussianReal 0 1) := Muon.Foundations.gaussian_integrable_pow 4
  have hm1 : 0 < e0 ^ 2 * ∫ g, g ^ 2 / (1 + qh * e0 ^ 2 * g ^ 2) ^ 2 ∂(gaussianReal 0 1) :=
    mul_pos (pow_pos he0 2) (d_H_pos (w := fun x : ℝ => x ^ 2) hw2 (fun x => sq_nonneg x)
      (by fun_prop) (fun x hx => by positivity) (a := qh * e0 ^ 2) (by positivity))
  have hm2 : 0 < e0 ^ 4 * ∫ g, g ^ 4 / (1 + qh * e0 ^ 2 * g ^ 2) ^ 2 ∂(gaussianReal 0 1) :=
    mul_pos (pow_pos he0 4) (d_H_pos (w := fun x : ℝ => x ^ 4) hw4 (fun x => by positivity)
      (by fun_prop) (fun x hx => by positivity) (a := qh * e0 ^ 2) (by positivity))
  have hK0ge : ∀ q, 0 ≤ q → q ≤ qh → e0 ^ 2 * ∫ g, g ^ 2 / (1 + qh * e0 ^ 2 * g ^ 2) ^ 2 ∂(gaussianReal 0 1) ≤
      e0 ^ 2 * ∫ g, g ^ 2 / (1 + q * e0 ^ 2 * g ^ 2) ^ 2 ∂(gaussianReal 0 1) := by
    intro q hq hqq
    exact mul_le_mul_of_nonneg_left (d_H_anti (w := fun x : ℝ => x ^ 2) hw2 (fun x => sq_nonneg x)
      (by fun_prop) (a := q * e0 ^ 2) (a' := qh * e0 ^ 2) (by positivity)
      (mul_le_mul_of_nonneg_right hqq (sq_nonneg _))) (sq_nonneg _)
  have hK0'ge : ∀ q, 0 ≤ q → q ≤ qh → e0 ^ 4 * ∫ g, g ^ 4 / (1 + qh * e0 ^ 2 * g ^ 2) ^ 2 ∂(gaussianReal 0 1) ≤
      e0 ^ 4 * ∫ g, g ^ 4 / (1 + q * e0 ^ 2 * g ^ 2) ^ 2 ∂(gaussianReal 0 1) := by
    intro q hq hqq
    exact mul_le_mul_of_nonneg_left (d_H_anti (w := fun x : ℝ => x ^ 4) hw4 (fun x => by positivity)
      (by fun_prop) (a := q * e0 ^ 2) (a' := qh * e0 ^ 2) (by positivity)
      (mul_le_mul_of_nonneg_right hqq (sq_nonneg _))) (by positivity)
  set S2 := ∑' α, ∫ ω, emaXi₂ β ℓ g α ω ^ 2 ∂P with hS2
  set S4 := ∑' α, ∫ ω, emaXi₁ β ℓ g α ω ^ 4 ∂P with hS4
  have hS2pos : 0 < S2 := (hRpos 0 le_rfl).trans_le (d_R_le hξ₂ le_rfl)
  have hS4pos : 0 < S4 := (hNpos 0 le_rfl).trans_le (d_N_le hξ₁ h4 hs4 le_rfl).2
  set m₁ := e0 ^ 2 * ∫ g, g ^ 2 / (1 + qh * e0 ^ 2 * g ^ 2) ^ 2 ∂(gaussianReal 0 1) with hm₁
  set m₂ := e0 ^ 4 * ∫ g, g ^ 4 / (1 + qh * e0 ^ 2 * g ^ 2) ^ 2 ∂(gaussianReal 0 1) with hm₂
  have hδ : 0 < min (m₁ / S2) (m₂ / S4) := lt_min (div_pos hm1 hS2pos) (div_pos hm2 hS4pos)
  have hlow : ∀ q ∈ Icc 0 qh, min (m₁ / S2) (m₂ / S4) ≤ f q := by
    intro q hq
    have hq0 : 0 ≤ q := hq.1
    simp only [hf]
    rw [hRd q hq0, hNd q hq0]
    refine le_min ((min_le_left _ _).trans ?_) ((min_le_right _ _).trans ?_)
    · exact div_le_div₀ (hK0 q hq0) (hK0ge q hq0 hq.2) (hRpos q hq0) (d_R_le hξ₂ hq0)
    · exact div_le_div₀ (hK0' q hq0) (hK0'ge q hq0 hq.2) (hNpos q hq0)
        (d_N_le hξ₁ h4 hs4 hq0).2
  have hne : (f '' Icc 0 qh).Nonempty := ⟨f 0, mem_image_of_mem f ⟨le_rfl, hqh0⟩⟩
  have hbb : BddBelow (f '' Icc 0 qh) := by
    refine ⟨min (m₁ / S2) (m₂ / S4), ?_⟩
    rintro y ⟨q, hq, rfl⟩
    exact hlow q hq
  have hεpos : 0 < epsBeta β γ := by
    rw [hε]
    exact lt_of_lt_of_le hδ (le_csInf hne (by rintro y ⟨q, hq, rfl⟩; exact hlow q hq))
  have hεle : ∀ q ∈ Icc 0 qh, epsBeta β γ ≤ f q := fun q hq => by
    rw [hε]; exact csInf_le hbb (mem_image_of_mem f hq)
  refine ⟨hεpos, ?_, ?_, ?_⟩
  · refine (hεle 0 ⟨le_rfl, hqh0⟩).trans ?_
    refine (min_le_left _ _).trans ?_
    rw [hRd 0 le_rfl]
    rw [div_le_one (hRpos 0 le_rfl)]
    have := d_shared_R hβ0 hβ1 hℓ hg (le_refl (0 : ℝ))
    have h0 : 0 ≤ profileRDeriv P (fun (j : ℕ) ω => β ^ ℓ * Muon.emaW β j * g (Sum.inl j) ω) 0 :=
      tsum_nonneg (fun j => integral_nonneg (p1c_d_nonneg _ le_rfl))
    linarith
  · intro q hq0 hqq
    have h := (hεle q ⟨hq0, hqq⟩).trans (min_le_left _ _)
    rw [hRd q hq0] at h
    exact (le_div_iff₀ (hRpos q hq0)).1 h
  · intro q hq0 hqq
    have h := (hεle q ⟨hq0.le, hqq⟩).trans (min_le_right _ _)
    rw [hNd q hq0.le] at h
    rw [d_N_eq hξ₁ hξ₂ (by rw [hF1, hF2]) hq0]
    exact (le_div_iff₀ (hNpos q hq0.le)).1 h


private lemma d_ema_delta {m n B : ℕ} (hB : 0 < B) {P : Measure Ω} [IsProbabilityMeasure P]
    {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {ℓ : ℕ} (hℓ : 1 ≤ ℓ) {g : ℕ ⊕ Fin ℓ → Ω → ℝ}
    (hg : IsStdGaussianFamily P g) (C : Muon.Covariances m n) (hout : C.Sout ≠ 0)
    (hin : C.Sin ≠ 0) {γ : ℝ} (hγ : 0 < γ) (hγsize : (max m n : ℝ) ≤ γ * B) {s u : ℝ}
    (hs : 0 < s) (hu : 0 < u) :
    (1 - Real.sqrt (1 - epsBeta β γ)) ^ 2 ≤
      profileDelta P C B (emaXi₁ β ℓ g) (emaXi₂ β ℓ g) s u := by
  have hii := p2e_profile_ii hβ0.le hβ1 hg
  obtain ⟨hε0, hε1, hRε, hNε⟩ := d_eps_main hβ0 hβ1 hℓ hg hγ
  have hbdd := d_ema_qhat_bdd hβ0 hβ1 γ
  have hF2 := p2e_F2 (β := β) hg
  have hr2 : profileR P (emaXi₂ β ℓ g) = Muon.DetEquiv.rW (Muon.emaW β) := by
    funext q; simp only [profileR, Muon.DetEquiv.rW, hF2]
  have hc0 : 0 ≤ Real.sqrt (1 - epsBeta β γ) := Real.sqrt_nonneg _
  have hc1 : Real.sqrt (1 - epsBeta β γ) ≤ 1 := Real.sqrt_le_one.mpr (by linarith)
  have hx := p3_branchPt_spec hB hii.profile₁ hs C
  have hy := p3_branchPt_spec hB hii.profile₂ hu C
  have hbx := (lem_app_vol_closed_branch_ii hB hii.profile₁ hs C hout hin γ hγsize).2 _ hx
  have hby := (lem_app_vol_closed_branch_ii hB hii.profile₂ hu C hout hin γ hγsize).2 _ hy
  unfold profileDelta
  simp only []
  generalize branchPt (profileF P (emaXi₁ β ℓ g)) C B s = x at hx hbx ⊢
  generalize branchPt (profileF P (emaXi₂ β ℓ g)) C B u = y at hy hby ⊢
  obtain ⟨⟨hp1, hp2, hp3, hp4⟩, -, -, -, -, -, -, -, -⟩ := hbx
  obtain ⟨⟨hq1, hq2, hq3, hq4⟩, -, -, -, -, hrq, -, hlt, hle⟩ := hby
  obtain ⟨hσ0, hσ'0, ha0, hc0', hσ, hσ', ha, hc⟩ := hx
  obtain ⟨hτ0, hτ'0, hb0, hd0, hτ, hτ', hb, hd⟩ := hy
  have hx' : IsBranchPoint (profileF P (emaXi₁ β ℓ g)) C B s x :=
    ⟨hσ0, hσ'0, ha0, hc0', hσ, hσ', ha, hc⟩
  have hy' : IsBranchPoint (profileF P (emaXi₂ β ℓ g)) C B u y :=
    ⟨hτ0, hτ'0, hb0, hd0, hτ, hτ', hb, hd⟩
  have hq : 0 < s * x.1 * x.2.1 := by positivity
  have hq' : 0 < u * y.1 * y.2.1 := by positivity
  have hqh : u * y.1 * y.2.1 ≤ qhatBeta β γ := by
    refine le_csSup hbdd ⟨hq'.le, ?_⟩
    rw [← hr2, hrq]
    exact hlt.le.trans hle
  have hpr := d_restr_profile_ii hβ0 hβ1 hg
  obtain ⟨-, -, -, -, -, -, hBb, hEb⟩ := lem_app_vol_closed_profile_iii hpr
  have hBq := (hBb _ (mem_Ici.2 hq.le) _ (mem_Ici.2 hq'.le)).2.trans (min_le_left _ _)
  have hEq := (hEb _ hq _ hq').2
  have hS := d_shared_R hβ0 hβ1 hℓ hg hq'.le
  have hSN := d_shared_N hβ0 hβ1 hℓ hg hq'
  have hεR := hRε _ hq'.le hqh
  have hεN := hNε _ hq' hqh
  have hR1 : 0 ≤ profileRDeriv P (emaXi₁ β ℓ g) (s * x.1 * x.2.1) :=
    ((lem_app_vol_closed_profile_i hii.profile₁).2.2.2.2.2.2.2.2.2.1 _ (mem_Ici.2 hq.le)).le
  have hN1 : 0 ≤ profileNegFDeriv P (emaXi₁ β ℓ g) (s * x.1 * x.2.1) :=
    ((lem_app_vol_closed_profile_i hii.profile₁).2.2.2.2.2.2.2.2.2.2.1 _ hq).2
  have h1e : 0 ≤ 1 - epsBeta β γ := by linarith
  have hble : pairedB P (emaXi₁ β ℓ g) (emaXi₂ β ℓ g) (s * x.1 * x.2.1) (u * y.1 * y.2.1) ≤
      Real.sqrt (1 - epsBeta β γ) * Real.sqrt (profileRDeriv P (emaXi₁ β ℓ g) (s * x.1 * x.2.1) *
        profileRDeriv P (emaXi₂ β ℓ g) (u * y.1 * y.2.1)) := by
    rw [d_restr_B, ← Real.sqrt_mul h1e]
    refine hBq.trans ?_
    rw [← d_restr_R1]
    refine Real.sqrt_le_sqrt ?_
    have : profileRDeriv P (fun (j : ℕ) ω => β ^ ℓ * Muon.emaW β j * g (Sum.inl j) ω)
        (u * y.1 * y.2.1) ≤ (1 - epsBeta β γ) *
        profileRDeriv P (emaXi₂ β ℓ g) (u * y.1 * y.2.1) := by linarith
    calc _ ≤ profileRDeriv P (emaXi₁ β ℓ g) (s * x.1 * x.2.1) *
          ((1 - epsBeta β γ) * profileRDeriv P (emaXi₂ β ℓ g) (u * y.1 * y.2.1)) :=
          mul_le_mul_of_nonneg_left this hR1
      _ = _ := by ring
  have hele : pairedE P (emaXi₁ β ℓ g) (emaXi₂ β ℓ g) (s * x.1 * x.2.1) (u * y.1 * y.2.1) ≤
      Real.sqrt (1 - epsBeta β γ) * Real.sqrt (profileNegFDeriv P (emaXi₁ β ℓ g) (s * x.1 * x.2.1) *
        profileNegFDeriv P (emaXi₂ β ℓ g) (u * y.1 * y.2.1)) := by
    rw [d_restr_E, ← Real.sqrt_mul h1e]
    refine hEq.trans ?_
    rw [← d_restr_N1]
    refine Real.sqrt_le_sqrt ?_
    have : profileNegFDeriv P (fun (j : ℕ) ω => β ^ ℓ * Muon.emaW β j * g (Sum.inl j) ω)
        (u * y.1 * y.2.1) ≤ (1 - epsBeta β γ) *
        profileNegFDeriv P (emaXi₂ β ℓ g) (u * y.1 * y.2.1) := by linarith
    calc _ ≤ profileNegFDeriv P (emaXi₁ β ℓ g) (s * x.1 * x.2.1) *
          ((1 - epsBeta β γ) * profileNegFDeriv P (emaXi₂ β ℓ g) (u * y.1 * y.2.1)) :=
          mul_le_mul_of_nonneg_left this hN1
      _ = _ := by ring
  have key := d_core hB hii C hout hin hs hu hx' hy' (c := Real.sqrt (1 - epsBeta β γ))
    (θs := 0) (θu := 0) hc0 hc1 ⟨le_rfl, zero_le_one⟩ ⟨le_rfl, zero_le_one⟩
    (d_side_out C hs hx' (θ := 0) (fun i => by rw [zero_mul]; exact hs.le))
    (d_side_in C hs hx' (θ := 0) (fun i => by rw [zero_mul]; exact hs.le))
    (d_side_out C hu hy' (θ := 0) (fun i => by rw [zero_mul]; exact hu.le))
    (d_side_in C hu hy' (θ := 0) (fun i => by rw [zero_mul]; exact hu.le)) hble hele
  simpa using key

/-- `lem:app-vol-closed-determinant`, snapshot `cr-2026-10-23`. Declaration of record for part (a) of
`lem:app-vol-closed-determinant`: if `Σ_out = 0` or `Σ_in = 0` then `Δ_ξ = 1` and
`𝒯^out[F] 𝒯^in[G] = 0` for all `F, G` (no diagonality is needed: `Σ_out = 0` or `Σ_in = 0` kills the trace factor). The hypothesis `F_{ξ₁}(0), F_{ξ₂}(0) ≤ 1` is explicit.

LaTeX (`sections/04-volatility/section.tex` l.1961–1971, verbatim):
```latex
\begin{lemma}[Determinant]\label{lem:app-vol-closed-determinant}
Let $(\xi_1,\xi_2)$ be a paired profile with $F_{\xi_1}(0),F_{\xi_2}(0)\le1$, and $s,u>0$.
\begin{enumerate}[label=(\alph*)]
\item If $\Sigmaout=0$ or $\Sigmain=0$, then $\Delta_\xi=1$ and
$\mathcal T^{\mathrm{out}}[F]\,\mathcal T^{\mathrm{in}}[G]=0$ for all diagonal $F,G$.
\item If $\Sigmaout\ne0$ and $\Sigmain\ne0$, then $\Delta_\xi\ge\theta_\Sigma(\min(s,u))^2>0$.
\item For the EMA paired profile with $0<\bmom<1$ and $\ell\ge1$, if $\Sigmaout,\Sigmain\ne0$,
then $\epsilon_\bmom\in(0,1]$ and
$\Delta_\ell\ge\big(1-\sqrt{1-\epsilon_\bmom}\big)^2\ge\epsilon_\bmom^2/4$ for all $s,u>0$.
\end{enumerate}
\end{lemma}
```
-/
theorem lem_app_vol_closed_determinant_i {m n B : ℕ} (hB : 0 < B) {P : Measure Ω}
    [IsProbabilityMeasure P] {ξ₁ ξ₂ : ι → Ω → ℝ} (hξ : def_app_vol_closed_profile_ii P ξ₁ ξ₂)
    (hF₁ : profileF P ξ₁ 0 ≤ 1) (hF₂ : profileF P ξ₂ 0 ≤ 1)
    (C : Muon.Covariances m n) (hC : C.Sout = 0 ∨ C.Sin = 0) {s u : ℝ} (hs : 0 < s) (hu : 0 < u) :
    profileDelta P C B ξ₁ ξ₂ s u = 1 ∧
    ∀ (F : Matrix (Fin m) (Fin m) ℝ) (G : Matrix (Fin n) (Fin n) ℝ),
      toutT C B (branchPt (profileF P ξ₁) C B s) (branchPt (profileF P ξ₂) C B u) s u F *
        tinT C B (branchPt (profileF P ξ₁) C B s) (branchPt (profileF P ξ₂) C B u) s u G = 0 := by
  have hx := p3_branchPt_spec hB hξ.profile₁ hs C
  have hy := p3_branchPt_spec hB hξ.profile₂ hu C
  have hb1 := lem_app_vol_closed_branch_i hB hξ.profile₁ hs C
  have hb2 := lem_app_vol_closed_branch_i hB hξ.profile₂ hu C
  unfold profileDelta
  simp only []
  generalize branchPt (profileF P ξ₁) C B s = x at hx ⊢
  generalize branchPt (profileF P ξ₂) C B u = y at hy ⊢
  rcases hC with h | h
  · have hx1 : x.1 = 0 := by rw [(hb1.1 h).2 x hx]
    have hy1 : y.1 = 0 := by rw [(hb2.1 h).2 y hy]
    have hT : ∀ F, toutT C B x y s u F = 0 := by intro F; simp [toutT, h]
    refine ⟨?_, fun F G => by rw [hT F, zero_mul]⟩
    simp only [closedDelta, hT, hx1, hy1]
    simp
  · have hx1 : x.2.1 = 0 := by rw [(hb1.2 h).2 x hx]
    have hy1 : y.2.1 = 0 := by rw [(hb2.2 h).2 y hy]
    have hT : ∀ G, tinT C B x y s u G = 0 := by intro G; simp [tinT, h]
    refine ⟨?_, fun F G => by rw [hT G, mul_zero]⟩
    simp only [closedDelta, hT, hx1, hy1]
    simp

/-- `lem:app-vol-closed-determinant`, snapshot `cr-2026-10-23`. Declaration of record for part (b) of
`lem:app-vol-closed-determinant`: if `Σ_out ≠ 0` and `Σ_in ≠ 0` then `Δ_ξ ≥ θ_Σ(min(s,u))² > 0`.

LaTeX (`sections/04-volatility/section.tex` l.1961–1971, verbatim):
```latex
\begin{lemma}[Determinant]\label{lem:app-vol-closed-determinant}
Let $(\xi_1,\xi_2)$ be a paired profile with $F_{\xi_1}(0),F_{\xi_2}(0)\le1$, and $s,u>0$.
\begin{enumerate}[label=(\alph*)]
\item If $\Sigmaout=0$ or $\Sigmain=0$, then $\Delta_\xi=1$ and
$\mathcal T^{\mathrm{out}}[F]\,\mathcal T^{\mathrm{in}}[G]=0$ for all diagonal $F,G$.
\item If $\Sigmaout\ne0$ and $\Sigmain\ne0$, then $\Delta_\xi\ge\theta_\Sigma(\min(s,u))^2>0$.
\item For the EMA paired profile with $0<\bmom<1$ and $\ell\ge1$, if $\Sigmaout,\Sigmain\ne0$,
then $\epsilon_\bmom\in(0,1]$ and
$\Delta_\ell\ge\big(1-\sqrt{1-\epsilon_\bmom}\big)^2\ge\epsilon_\bmom^2/4$ for all $s,u>0$.
\end{enumerate}
\end{lemma}
```
-/
theorem lem_app_vol_closed_determinant_ii {m n B : ℕ} (hB : 0 < B) {P : Measure Ω}
    [IsProbabilityMeasure P] {ξ₁ ξ₂ : ι → Ω → ℝ} (hξ : def_app_vol_closed_profile_ii P ξ₁ ξ₂)
    (hF₁ : profileF P ξ₁ 0 ≤ 1) (hF₂ : profileF P ξ₂ 0 ≤ 1)
    (C : Muon.Covariances m n) (hout : C.Sout ≠ 0) (hin : C.Sin ≠ 0) {s u : ℝ} (hs : 0 < s)
    (hu : 0 < u) :
    thetaSigma C B (min s u) ^ 2 ≤ profileDelta P C B ξ₁ ξ₂ s u ∧
    0 < thetaSigma C B (min s u) ^ 2 := by
  have hmin : 0 < min s u := lt_min hs hu
  have hθm := d_theta_mem (B := B) C hmin
  refine ⟨?_, pow_pos (by unfold thetaSigma; have := d_kappa_nonneg (B := B) C; positivity) 2⟩
  have hx := p3_branchPt_spec hB hξ.profile₁ hs C
  have hy := p3_branchPt_spec hB hξ.profile₂ hu C
  have hγ : (max m n : ℝ) ≤ ((max m n : ℝ) / B) * B := by
    have hBr : (B : ℝ) ≠ 0 := by exact_mod_cast hB.ne'
    rw [div_mul_cancel₀ _ hBr]
  have hbx := (lem_app_vol_closed_branch_ii hB hξ.profile₁ hs C hout hin _ hγ).2 _ hx
  have hby := (lem_app_vol_closed_branch_ii hB hξ.profile₂ hu C hout hin _ hγ).2 _ hy
  unfold profileDelta
  simp only []
  generalize branchPt (profileF P ξ₁) C B s = x at hx hbx ⊢
  generalize branchPt (profileF P ξ₂) C B u = y at hy hby ⊢
  obtain ⟨⟨hp1, hp2, hp3, hp4⟩, -, -, hx3, hx4, -⟩ := hbx
  obtain ⟨⟨hq1, hq2, hq3, hq4⟩, -, -, hy3, hy4, -⟩ := hby
  have hθs := d_theta_mem (B := B) C hs
  have hθu := d_theta_mem (B := B) C hu
  obtain ⟨-, -, -, -, -, -, hBb, hEb⟩ := lem_app_vol_closed_profile_iii hξ
  have hxspec := hx
  have hyspec := hy
  obtain ⟨hσ0, hσ'0, ha0, hc0', hσ, hσ', ha, hc⟩ := hxspec
  obtain ⟨hτ0, hτ'0, hb0, hd0, hτ, hτ', hb, hd⟩ := hyspec
  have hq : 0 < s * x.1 * x.2.1 := by positivity
  have hq' : 0 < u * y.1 * y.2.1 := by positivity
  have key := d_core hB hξ C hout hin hs hu hx hy (c := 1) (θs := thetaSigma C B s)
    (θu := thetaSigma C B u) zero_le_one le_rfl hθs hθu
    (d_side_out C hs hx (fun i => d_theta_out C hs ha0 hx3 hF₁ i))
    (d_side_in C hs hx (fun i => d_theta_in C hs hc0' hx4 hF₁ i))
    (d_side_out C hu hy (fun i => d_theta_out C hu hb0 hy3 hF₂ i))
    (d_side_in C hu hy (fun i => d_theta_in C hu hd0 hy4 hF₂ i))
    (by rw [one_mul]; exact ((hBb _ (mem_Ici.2 hq.le) _ (mem_Ici.2 hq'.le)).2).trans (min_le_left _ _))
    (by rw [one_mul]; exact (hEb _ hq _ hq').2)
  refine le_trans ?_ key
  have hm1 : thetaSigma C B (min s u) ≤ thetaSigma C B s := d_theta_mono C hmin (min_le_left _ _)
  have hm2 : thetaSigma C B (min s u) ≤ thetaSigma C B u := d_theta_mono C hmin (min_le_right _ _)
  have hsq : Real.sqrt ((1 - thetaSigma C B s) * (1 - thetaSigma C B u)) ≤
      1 - thetaSigma C B (min s u) := by
    rw [Real.sqrt_le_left (by linarith [hθm.2, hθm.1])]
    have h1 : 0 ≤ 1 - thetaSigma C B s := by linarith [hθs.2]
    have h2 : 0 ≤ 1 - thetaSigma C B u := by linarith [hθu.2]
    nlinarith
  rw [one_mul]
  exact pow_le_pow_left₀ hθm.1 (by linarith) 2

/-- `lem:app-vol-closed-determinant`, snapshot `cr-2026-10-23`. Declaration of record for part (c) of
`lem:app-vol-closed-determinant`: for the EMA paired profile with `0 < β < 1`, `ℓ ≥ 1`, and
`Σ_out, Σ_in ≠ 0`, the constant `ε_β` lies in `(0,1]` and `Δ_ℓ(s,u) ≥ (1 - √(1-ε_β))² ≥ ε_β²/4`
for all `s, u > 0`. The size condition `max(N_out, N_in) ≤ γ⋆ B` is explicit.

LaTeX (`sections/04-volatility/section.tex` l.1961–1971, verbatim):
```latex
\begin{lemma}[Determinant]\label{lem:app-vol-closed-determinant}
Let $(\xi_1,\xi_2)$ be a paired profile with $F_{\xi_1}(0),F_{\xi_2}(0)\le1$, and $s,u>0$.
\begin{enumerate}[label=(\alph*)]
\item If $\Sigmaout=0$ or $\Sigmain=0$, then $\Delta_\xi=1$ and
$\mathcal T^{\mathrm{out}}[F]\,\mathcal T^{\mathrm{in}}[G]=0$ for all diagonal $F,G$.
\item If $\Sigmaout\ne0$ and $\Sigmain\ne0$, then $\Delta_\xi\ge\theta_\Sigma(\min(s,u))^2>0$.
\item For the EMA paired profile with $0<\bmom<1$ and $\ell\ge1$, if $\Sigmaout,\Sigmain\ne0$,
then $\epsilon_\bmom\in(0,1]$ and
$\Delta_\ell\ge\big(1-\sqrt{1-\epsilon_\bmom}\big)^2\ge\epsilon_\bmom^2/4$ for all $s,u>0$.
\end{enumerate}
\end{lemma}
```
-/
theorem lem_app_vol_closed_determinant_iii {m n B : ℕ} (hB : 0 < B) {P : Measure Ω}
    [IsProbabilityMeasure P] {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {ℓ : ℕ} (hℓ : 1 ≤ ℓ)
    {g : ℕ ⊕ Fin ℓ → Ω → ℝ} (hg : IsStdGaussianFamily P g)
    (C : Muon.Covariances m n) (hout : C.Sout ≠ 0) (hin : C.Sin ≠ 0)
    (γ : ℝ) (hγ : 0 < γ) (hγsize : (max m n : ℝ) ≤ γ * B)
    (hF₁ : profileF P (emaXi₁ β ℓ g) 0 ≤ 1) (hF₂ : profileF P (emaXi₂ β ℓ g) 0 ≤ 1) :
    0 < epsBeta β γ ∧ epsBeta β γ ≤ 1 ∧
    ∀ s u : ℝ, 0 < s → 0 < u →
      (1 - Real.sqrt (1 - epsBeta β γ)) ^ 2 ≤
          profileDelta P C B (emaXi₁ β ℓ g) (emaXi₂ β ℓ g) s u ∧
        epsBeta β γ ^ 2 / 4 ≤ (1 - Real.sqrt (1 - epsBeta β γ)) ^ 2 := by
  obtain ⟨hε0, hε1, -, -⟩ := d_eps_main hβ0 hβ1 hℓ hg hγ
  refine ⟨hε0, hε1, fun s u hs hu => ⟨d_ema_delta hB hβ0 hβ1 hℓ hg C hout hin hγ hγsize hs hu, ?_⟩⟩
  have h1 : epsBeta β γ / 2 ≤ 1 - Real.sqrt (1 - epsBeta β γ) := by
    have : Real.sqrt (1 - epsBeta β γ) ≤ 1 - epsBeta β γ / 2 := by
      rw [Real.sqrt_le_left (by linarith)]
      nlinarith
    linarith
  have h2 := pow_le_pow_left₀ (by linarith) h1 2
  calc epsBeta β γ ^ 2 / 4 = (epsBeta β γ / 2) ^ 2 := by ring
    _ ≤ _ := h2

end Muon.Volatility
