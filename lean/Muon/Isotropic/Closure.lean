import Muon.Isotropic.Helpers
import Muon.DetEquiv.Branch
import Muon.Foundations.Gaussian
import Muon.Foundations.Conventions

/-!
# Appendix F: the isotropic closure and the root comparison (task L-F.2, drift part)

Snapshot `cr-2026-10-23`. Source: `sections/05b-isotropic/section.tex`, `prop:app-iso-closure`
(l.114–142) and `lem:app-iso-comparison` (l.1140–1156). Card `sections/05b-isotropic/CARD.md`
§3 rows `prop:app-iso-closure` and `lem:app-iso-comparison`, §5 item 2 (L-F.2). The volatility
labels of card F.2 (`prop:app-iso-volatility-zero`, `prop:app-iso-vol-momentum`) are deferred
(ruling U5) and are not in this file.

Representation choices:

* The spectral measures `ν_out = γ_out δ₁`, `ν_in = γ_in δ₁` (`eqn:app-iso-measures`) are
  `isoSpecMeasure γ`. The branch solution `(σ, σ̃, s̃₁, s₁)` of `eqn:app-de-system` is an
  `IsBranchSol (Fw w) ν ν' s x` with `ν` the out measure and `ν'` the in measure, as in
  `Muon.DetEquiv.IsBranchSol`. The measures are hypotheses `(ν : Measure ℝ) = isoSpecMeasure γ`.
* `q = q(−s)` is `isoQ s x = s σ σ̃`; `ψ(s) = q F_w(q)` (`eqn:app-iso-psi`) is `isoPsi β s x`,
  i.e. `rW (Muon.emaW β)` at `q`. The bulk weight is `Muon.emaW β`, `β = bmom ∈ [0,1)`.
* `Φ` is `isoPhi` and `f` is `isoF` (`Muon.Isotropic.Helpers`); `ξ = (2q)^{-1/2}` is `isoXi`;
  `erfc` is `Muon.Foundations.erfc`.
* `γ_∧ = min γ_in γ_out`. A link `r` is `IsIsoLink r` (continuous, strictly increasing on
  `[0,∞)`, `r(0)=0`). `D_r = isoDr r γin γout`, `G_r(q) = isoG r γin γout s q`.
* `q_r(s)` is `isoRoot r γin γout s`: the chosen zero when one exists, `0` otherwise (the
  same pattern as `Muon.DetEquiv.branchSol`). Existence and uniqueness are part of
  `lem_app_iso_comparison_i`, so `isoRoot` is the zero there.
-/

open MeasureTheory Filter Topology Set
open Muon.DetEquiv (IsBranchSol Fw rW)
open scoped ENNReal

noncomputable section

namespace Muon.Isotropic

/-! ## Definitions -/

/-- The spectral measure `γ δ₁` of `eqn:app-iso-measures` (`ν_out = γ_out δ₁`,
`ν_in = γ_in δ₁`), as a `Measure ℝ`. -/
def isoSpecMeasure (γ : ℝ) : Measure ℝ :=
  ENNReal.ofReal γ • Measure.dirac 1

/-- `q(−s) = s σ σ̃` of a branch solution `x = (σ, σ̃, s̃₁, s₁)` (`prop:app-iso-closure`(ii),
`eqn:app-iso-psi`; `z = −s` in `eqn:app-de-system`: `q = −z σ σ̃`). -/
def isoQ (s : ℝ) (x : ℝ × ℝ × ℝ × ℝ) : ℝ :=
  s * x.1 * x.2.1

/-- `ψ(s) = q(−s) F_w(q(−s))` (`eqn:app-iso-psi`) at the weight `Muon.emaW β`, for the branch
solution `x`; `ψ(s) = r_β(q(−s))` with `r_β = rW (Muon.emaW β)`. -/
def isoPsi (β s : ℝ) (x : ℝ × ℝ × ℝ × ℝ) : ℝ :=
  rW (Muon.emaW β) (isoQ s x)

/-- `ξ = (2q)^{-1/2}` (`eqn:app-iso-closure-f`, `prop:app-iso-closure`(iii)). -/
def isoXi (q : ℝ) : ℝ :=
  (2 * q) ^ (-(1 / 2 : ℝ))

/-- The hypotheses on the link of `lem:app-iso-comparison`: `r` continuous and strictly
increasing on `[0,∞)` with `r(0) = 0`. -/
def IsIsoLink (r : ℝ → ℝ) : Prop :=
  ContinuousOn r (Ici 0) ∧ StrictMonoOn r (Ici 0) ∧ r 0 = 0

/-- `D_r = {q ≥ 0 : r(q) < γ_∧}`, with `γ_∧ = min(γ_in, γ_out)`
(`lem:app-iso-comparison`, `section.tex` l.1141). -/
def isoDr (r : ℝ → ℝ) (γin γout : ℝ) : Set ℝ :=
  {q | 0 ≤ q ∧ r q < min γin γout}

/-- `G_r(q) = s q − (γ_out − r(q))(γ_in − r(q))` (`lem:app-iso-comparison`(i)). -/
def isoG (r : ℝ → ℝ) (γin γout s q : ℝ) : ℝ :=
  s * q - (γout - r q) * (γin - r q)

open scoped Classical in
/-- `q_r(s)`: the zero of `G_r` in `D_r` (`lem:app-iso-comparison`(i)), taken as the chosen zero
when one exists and `0` otherwise. Uniqueness is `lem_app_iso_comparison_i`. -/
def isoRoot (r : ℝ → ℝ) (γin γout s : ℝ) : ℝ :=
  if h : ∃ q, q ∈ isoDr r γin γout ∧ isoG r γin γout s q = 0 then h.choose else 0

/-! ## The isotropic closure -/

/-- Private helper (task P-F.2.P1): the one-atom integral `∫ t/(a t+s) dν = γ/(a+s)` for
`ν = γ δ₁`. -/
private lemma p1_spec_integral (γ a s : ℝ) (hγ : 0 ≤ γ) :
    ∫ t, t / (a * t + s) ∂(isoSpecMeasure γ) = γ / (a + s) := by
  unfold isoSpecMeasure
  rw [integral_smul_measure, integral_dirac, ENNReal.toReal_ofReal hγ, smul_eq_mul, mul_one,
    mul_one_div]

/-- `prop:app-iso-closure`(i), snapshot `cr-2026-10-23`. The whole proposition environment, verbatim
(`sections/05b-isotropic/section.tex`):
```latex
\begin{proposition}[Isotropic closure]\label{prop:app-iso-closure}
Let $\bmom\in[0,1)$, $\gin,\gout>0$ and $s>0$, and let
$(\sigma,\tilde\sigma,\tilde s_1,s_1,q)=(\sigma,\tilde\sigma,\tilde s_1,s_1,q)(-s)$
be the solution of \cref{eqn:app-de-system} for the measures
\cref{eqn:app-iso-measures}.
\begin{enumerate}[label=(\roman*)]
\item The branch satisfies
\begin{equation}\label{eqn:app-iso-closure}
\sigma=\frac{\gout}{s+\tilde s_1},\qquad
\tilde\sigma=\frac{\gin}{s+s_1},\qquad
\tilde s_1\sigma=s_1\tilde\sigma=\psi(s),
\end{equation}
and the two anchors and their consequences
\begin{equation}\label{eqn:app-iso-anchors}
\psi(s)=\gout-s\sigma=\gin-s\tilde\sigma,\qquad
\tilde\sigma-\sigma=\frac{\gin-\gout}{s},\qquad
(s+\tilde s_1)(s+s_1)=\frac{s\,\gin\gout}{q}.
\end{equation}
\item The number $q=q(-s)$ is the unique $q>0$ with
$q\Fw(q)<\min(\gin,\gout)$ and
\begin{equation}\label{eqn:app-iso-scalar-q}
s\,q=\big(\gout-q\Fw(q)\big)\big(\gin-q\Fw(q)\big).
\end{equation}
\item At $\bmom=0$, with $\xi\defeq(2q)^{-1/2}=(2s\sigma\tilde\sigma)^{-1/2}$,
\begin{equation}\label{eqn:app-iso-closure-f}
\psi(s)=\Phi(q)=f(\xi)=1-\sqrt\pi\,\xi\,e^{\xi^2}\erfc(\xi).
\end{equation}
\end{enumerate}
\end{proposition}
```
Part (i). Encoding: the solution is `x = (σ, σ̃, s̃₁, s₁)` of `IsBranchSol`, with `ν` the out measure and `ν'` the in measure; `ψ(s) = isoPsi β s x`, `q = isoQ s x`. The four anchor identities are the four displayed relations of (i). -/
theorem prop_app_iso_closure_i {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {γin γout s : ℝ}
    (hγin : 0 < γin) (hγout : 0 < γout) (hs : 0 < s)
    {ν ν' : FiniteMeasure ℝ} (hν : (ν : Measure ℝ) = isoSpecMeasure γout)
    (hν' : (ν' : Measure ℝ) = isoSpecMeasure γin)
    {x : ℝ × ℝ × ℝ × ℝ} (hx : IsBranchSol (Fw (Muon.emaW β)) ν ν' s x) :
    x.1 = γout / (s + x.2.2.1) ∧
    x.2.1 = γin / (s + x.2.2.2) ∧
    x.2.2.1 * x.1 = isoPsi β s x ∧
    x.2.2.2 * x.2.1 = isoPsi β s x ∧
    isoPsi β s x = γout - s * x.1 ∧
    isoPsi β s x = γin - s * x.2.1 ∧
    x.2.1 - x.1 = (γin - γout) / s ∧
    (s + x.2.2.1) * (s + x.2.2.2) = s * γin * γout / isoQ s x := by
  rcases x with ⟨σ, σ', a, c⟩
  simp only [IsBranchSol] at hx
  obtain ⟨hσ0, hσ'0, ha0, hc0, hσ, hσ', ha, hc⟩ := hx
  rw [hν, p1_spec_integral γout a s hγout.le] at hσ
  rw [hν', p1_spec_integral γin c s hγin.le] at hσ'
  dsimp only
  have hsa : 0 < a + s := by linarith
  have hsc : 0 < c + s := by linarith
  have hsa' : a + s ≠ 0 := hsa.ne'
  have hsc' : c + s ≠ 0 := hsc.ne'
  have hσ_eq : σ * (s + a) = γout := by
    rw [hσ, add_comm s a]; exact div_mul_cancel₀ γout hsa'
  have hσ'_eq : σ' * (s + c) = γin := by
    rw [hσ', add_comm s c]; exact div_mul_cancel₀ γin hsc'
  have hσpos : 0 < σ := by rw [hσ]; exact div_pos hγout hsa
  have hσ'pos : 0 < σ' := by rw [hσ']; exact div_pos hγin hsc
  have hq0 : s * σ * σ' ≠ 0 := by positivity
  have hψa : a * σ = isoPsi β s (σ, σ', a, c) := by
    simp only [isoPsi, isoQ, rW]
    rw [ha]
    ring
  have hψc : c * σ' = isoPsi β s (σ, σ', a, c) := by
    simp only [isoPsi, isoQ, rW]
    rw [hc]
    ring
  have h5 : isoPsi β s (σ, σ', a, c) = γout - s * σ := by
    linear_combination hσ_eq - hψa
  have h6 : isoPsi β s (σ, σ', a, c) = γin - s * σ' := by
    linear_combination hσ'_eq - hψc
  refine ⟨by rw [hσ, add_comm s a], by rw [hσ', add_comm s c], hψa, hψc, h5, h6, ?_, ?_⟩
  · rw [eq_div_iff hs.ne']
    linear_combination h6 - h5
  · simp only [isoQ]
    rw [eq_div_iff hq0]
    linear_combination (s * σ' * (s + c)) * hσ_eq + (s * γout) * hσ'_eq

/-- Private helper (task P-F.2.P2): the EMA weights are a weight sequence. -/
private lemma cl_ii_emaW_weightSeq {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) :
    Muon.DetEquiv.WeightSeq (Muon.emaW β) := by
  refine ⟨fun j => ?_, ?_, 0, ?_⟩
  · unfold Muon.emaW
    exact mul_nonneg (by linarith) (pow_nonneg hβ0 j)
  · unfold Muon.emaW
    exact (summable_geometric_of_lt_one hβ0 hβ1).mul_left _
  · unfold Muon.emaW
    rw [pow_zero, mul_one]
    exact (by linarith : (0:ℝ) < 1 - β).ne'

/-- Private helper (task P-F.2.P2): `r_β = rW (Muon.emaW β)` is an isotropic link for
`β ∈ [0,1)`. -/
private lemma cl_ii_isoLink {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) :
    IsIsoLink (rW (Muon.emaW β)) := by
  have hw := cl_ii_emaW_weightSeq hβ0 hβ1
  refine ⟨ContinuousOn.mul continuousOn_id (Muon.DetEquiv.Fw_admissible hw).contOn,
    (Muon.DetEquiv.lem_app_de_scalar_iii hw).2.1,
    (Muon.DetEquiv.lem_app_de_scalar_iii hw).2.2.1⟩

/-- Private helper (task P-F.2.P2): on `{q ≥ 0 : r q < γ_∧}` the scalar equation
`s q = (γout - r q)(γin - r q)` admits no pair of solutions `a < b` (the right side strictly
decreases in `r`, and `r` strictly increases). -/
private lemma cl_ii_no_lt {r : ℝ → ℝ} (hr : StrictMonoOn r (Ici 0)) {γin γout s a b : ℝ}
    (hs : 0 < s) (ha : 0 ≤ a) (hab : a < b)
    (hra : r a < min γin γout) (hrb : r b < min γin γout)
    (ea : s * a = (γout - r a) * (γin - r a)) (eb : s * b = (γout - r b) * (γin - r b)) :
    False := by
  have hb : 0 ≤ b := ha.trans hab.le
  have hrab : r a < r b := hr (Set.mem_Ici.mpr ha) (Set.mem_Ici.mpr hb) hab
  have hbo : r b < γout := lt_of_lt_of_le hrb (min_le_right γin γout)
  have hbi : r b < γin := lt_of_lt_of_le hrb (min_le_left γin γout)
  have hprod : 0 < (r b - r a) * (γout + γin - r a - r b) :=
    mul_pos (by linarith) (by linarith)
  have hlt : s * a < s * b := mul_lt_mul_of_pos_left hab hs
  nlinarith [hprod]

/-- `prop:app-iso-closure`(ii), snapshot `cr-2026-10-23`. The whole proposition environment, verbatim
(`sections/05b-isotropic/section.tex`):
```latex
\begin{proposition}[Isotropic closure]\label{prop:app-iso-closure}
Let $\bmom\in[0,1)$, $\gin,\gout>0$ and $s>0$, and let
$(\sigma,\tilde\sigma,\tilde s_1,s_1,q)=(\sigma,\tilde\sigma,\tilde s_1,s_1,q)(-s)$
be the solution of \cref{eqn:app-de-system} for the measures
\cref{eqn:app-iso-measures}.
\begin{enumerate}[label=(\roman*)]
\item The branch satisfies
\begin{equation}\label{eqn:app-iso-closure}
\sigma=\frac{\gout}{s+\tilde s_1},\qquad
\tilde\sigma=\frac{\gin}{s+s_1},\qquad
\tilde s_1\sigma=s_1\tilde\sigma=\psi(s),
\end{equation}
and the two anchors and their consequences
\begin{equation}\label{eqn:app-iso-anchors}
\psi(s)=\gout-s\sigma=\gin-s\tilde\sigma,\qquad
\tilde\sigma-\sigma=\frac{\gin-\gout}{s},\qquad
(s+\tilde s_1)(s+s_1)=\frac{s\,\gin\gout}{q}.
\end{equation}
\item The number $q=q(-s)$ is the unique $q>0$ with
$q\Fw(q)<\min(\gin,\gout)$ and
\begin{equation}\label{eqn:app-iso-scalar-q}
s\,q=\big(\gout-q\Fw(q)\big)\big(\gin-q\Fw(q)\big).
\end{equation}
\item At $\bmom=0$, with $\xi\defeq(2q)^{-1/2}=(2s\sigma\tilde\sigma)^{-1/2}$,
\begin{equation}\label{eqn:app-iso-closure-f}
\psi(s)=\Phi(q)=f(\xi)=1-\sqrt\pi\,\xi\,e^{\xi^2}\erfc(\xi).
\end{equation}
\end{enumerate}
\end{proposition}
```
Part (ii). Encoding: the solution's `q = isoQ s x` is the unique `q > 0` with `q F_w(q) < min(γ_in, γ_out)` and the scalar equation; `q F_w(q)` is `rW (Muon.emaW β) q`. -/
theorem prop_app_iso_closure_ii {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {γin γout s : ℝ}
    (hγin : 0 < γin) (hγout : 0 < γout) (hs : 0 < s)
    {ν ν' : FiniteMeasure ℝ} (hν : (ν : Measure ℝ) = isoSpecMeasure γout)
    (hν' : (ν' : Measure ℝ) = isoSpecMeasure γin)
    {x : ℝ × ℝ × ℝ × ℝ} (hx : IsBranchSol (Fw (Muon.emaW β)) ν ν' s x) :
    0 < isoQ s x ∧
    rW (Muon.emaW β) (isoQ s x) < min γin γout ∧
    s * isoQ s x =
      (γout - rW (Muon.emaW β) (isoQ s x)) * (γin - rW (Muon.emaW β) (isoQ s x)) ∧
    ∀ q : ℝ, 0 < q → rW (Muon.emaW β) q < min γin γout →
      s * q = (γout - rW (Muon.emaW β) q) * (γin - rW (Muon.emaW β) q) →
      q = isoQ s x := by
  have hnn : 0 ≤ x.1 ∧ 0 ≤ x.2.1 ∧ 0 ≤ x.2.2.1 ∧ 0 ≤ x.2.2.2 := by
    rcases x with ⟨σ, σ', a, c⟩
    simp only [IsBranchSol] at hx
    obtain ⟨hσ0, hσ'0, ha0, hc0, -, -, -, -⟩ := hx
    exact ⟨hσ0, hσ'0, ha0, hc0⟩
  obtain ⟨h1, h2, -, -, h5, h6, -, -⟩ :=
    prop_app_iso_closure_i hβ0 hβ1 hγin hγout hs hν hν' hx
  have hσpos : 0 < x.1 := by
    rw [h1]; exact div_pos hγout (by linarith [hnn.2.2.1])
  have hσ'pos : 0 < x.2.1 := by
    rw [h2]; exact div_pos hγin (by linarith [hnn.2.2.2])
  have hr5 : rW (Muon.emaW β) (isoQ s x) = γout - s * x.1 := h5
  have hr6 : rW (Muon.emaW β) (isoQ s x) = γin - s * x.2.1 := h6
  have hQpos : 0 < isoQ s x := by
    unfold isoQ; exact mul_pos (mul_pos hs hσpos) hσ'pos
  have hlt : rW (Muon.emaW β) (isoQ s x) < min γin γout := by
    have hsσ : 0 < s * x.1 := mul_pos hs hσpos
    have hsσ' : 0 < s * x.2.1 := mul_pos hs hσ'pos
    refine lt_min ?_ ?_
    · rw [hr5]; linarith
    · rw [hr6]; linarith
  have e1 : γout - rW (Muon.emaW β) (isoQ s x) = s * x.1 := by rw [hr5]; ring
  have e2 : γin - rW (Muon.emaW β) (isoQ s x) = s * x.2.1 := by rw [hr6]; ring
  have hsc : s * isoQ s x =
      (γout - rW (Muon.emaW β) (isoQ s x)) * (γin - rW (Muon.emaW β) (isoQ s x)) := by
    rw [e1, e2]; unfold isoQ; ring
  refine ⟨hQpos, hlt, hsc, ?_⟩
  intro q hq hrq hsq
  have hmono := (cl_ii_isoLink hβ0 hβ1).2.1
  rcases lt_trichotomy q (isoQ s x) with h | h | h
  · exact (cl_ii_no_lt hmono hs hq.le h hrq hlt hsq hsc).elim
  · exact h
  · exact (cl_ii_no_lt hmono hs hQpos.le h hlt hrq hsc hsq).elim

/-- `prop:app-iso-closure`(iii), snapshot `cr-2026-10-23`. The whole proposition environment, verbatim
(`sections/05b-isotropic/section.tex`):
```latex
\begin{proposition}[Isotropic closure]\label{prop:app-iso-closure}
Let $\bmom\in[0,1)$, $\gin,\gout>0$ and $s>0$, and let
$(\sigma,\tilde\sigma,\tilde s_1,s_1,q)=(\sigma,\tilde\sigma,\tilde s_1,s_1,q)(-s)$
be the solution of \cref{eqn:app-de-system} for the measures
\cref{eqn:app-iso-measures}.
\begin{enumerate}[label=(\roman*)]
\item The branch satisfies
\begin{equation}\label{eqn:app-iso-closure}
\sigma=\frac{\gout}{s+\tilde s_1},\qquad
\tilde\sigma=\frac{\gin}{s+s_1},\qquad
\tilde s_1\sigma=s_1\tilde\sigma=\psi(s),
\end{equation}
and the two anchors and their consequences
\begin{equation}\label{eqn:app-iso-anchors}
\psi(s)=\gout-s\sigma=\gin-s\tilde\sigma,\qquad
\tilde\sigma-\sigma=\frac{\gin-\gout}{s},\qquad
(s+\tilde s_1)(s+s_1)=\frac{s\,\gin\gout}{q}.
\end{equation}
\item The number $q=q(-s)$ is the unique $q>0$ with
$q\Fw(q)<\min(\gin,\gout)$ and
\begin{equation}\label{eqn:app-iso-scalar-q}
s\,q=\big(\gout-q\Fw(q)\big)\big(\gin-q\Fw(q)\big).
\end{equation}
\item At $\bmom=0$, with $\xi\defeq(2q)^{-1/2}=(2s\sigma\tilde\sigma)^{-1/2}$,
\begin{equation}\label{eqn:app-iso-closure-f}
\psi(s)=\Phi(q)=f(\xi)=1-\sqrt\pi\,\xi\,e^{\xi^2}\erfc(\xi).
\end{equation}
\end{enumerate}
\end{proposition}
```
Part (iii), at `β = 0` (weight `Muon.emaW 0`). Encoding: `ξ = isoXi q = (2q)^{-1/2}`; `Φ` is `isoPhi`, `f` is `isoF`; `erfc` is `Muon.Foundations.erfc`. The identity `ψ(s) = Φ(q)` is `rW (Muon.emaW 0) q = q J(q)`. -/
theorem prop_app_iso_closure_iii {γin γout s : ℝ}
    (hγin : 0 < γin) (hγout : 0 < γout) (hs : 0 < s)
    {ν ν' : FiniteMeasure ℝ} (hν : (ν : Measure ℝ) = isoSpecMeasure γout)
    (hν' : (ν' : Measure ℝ) = isoSpecMeasure γin)
    {x : ℝ × ℝ × ℝ × ℝ} (hx : IsBranchSol (Fw (Muon.emaW 0)) ν ν' s x) :
    isoPsi 0 s x = isoPhi (isoQ s x) ∧
    isoPhi (isoQ s x) = isoF (isoXi (isoQ s x)) ∧
    isoPhi (isoQ s x) =
      1 - Real.sqrt Real.pi * isoXi (isoQ s x) * Real.exp (isoXi (isoQ s x) ^ 2) *
        Muon.Foundations.erfc (isoXi (isoQ s x)) := by
  have hF : ∀ q : ℝ, Muon.DetEquiv.Fw (Muon.emaW 0) q = Muon.DetEquiv.J q := by
    intro q
    unfold Muon.DetEquiv.Fw
    rw [tsum_eq_single 0]
    · simp [Muon.emaW]
    · intro j hj
      simp [Muon.emaW, hj]
  have hpos : 0 < isoQ s x := by
    have hA := prop_app_iso_closure_i (β := 0) le_rfl zero_lt_one hγin hγout hs hν hν' hx
    have hnn : 0 ≤ x.2.2.1 ∧ 0 ≤ x.2.2.2 := by
      rcases x with ⟨σ, σ', a, c⟩
      simp only [IsBranchSol] at hx
      obtain ⟨-, -, ha0, hc0, -⟩ := hx
      exact ⟨ha0, hc0⟩
    have h1 : 0 < x.1 := by
      rw [hA.1]; exact div_pos hγout (by linarith [hnn.1])
    have h2 : 0 < x.2.1 := by
      rw [hA.2.1]; exact div_pos hγin (by linarith [hnn.2])
    unfold isoQ
    exact mul_pos (mul_pos hs h1) h2
  have hcore := Muon.DetEquiv.prop_app_de_nomomentum (isoQ s x) (isoXi (isoQ s x)) hpos rfl
  refine ⟨?_, ?_, ?_⟩
  · simp only [isoPsi, rW, hF, isoPhi]
  · exact lem_app_iso_gaussian_i _ hpos
  · rw [lem_app_iso_gaussian_i _ hpos]
    exact hcore.2.2

/-! ## Root comparison -/

/-- Private helper (task P-F.2.P4): membership in `isoDr`. -/
private lemma pf4_mem_D {r : ℝ → ℝ} {γin γout q : ℝ} :
    q ∈ isoDr r γin γout ↔ 0 ≤ q ∧ r q < min γin γout := Iff.rfl

/-- Private helper (task P-F.2.P4): `D_r` is order-connected (initial segment of `[0,∞)`). -/
private lemma pf4_D_ordConnected {r : ℝ → ℝ} (hr : IsIsoLink r) {γin γout : ℝ} :
    (isoDr r γin γout).OrdConnected := by
  refine ⟨fun x hx y hy z hz => ?_⟩
  obtain ⟨hx0, _⟩ := (pf4_mem_D).1 hx
  obtain ⟨_, hy2⟩ := (pf4_mem_D).1 hy
  have hz0 : (0:ℝ) ≤ z := le_trans hx0 hz.1
  have hzy : r z ≤ r y :=
    hr.2.1.monotoneOn (Set.mem_Ici.mpr hz0) (Set.mem_Ici.mpr (le_trans hz0 hz.2)) hz.2
  exact (pf4_mem_D).2 ⟨hz0, lt_of_le_of_lt hzy hy2⟩

/-- Private helper (task P-F.2.P4): `G_s` is strictly increasing on `D_r` for `s > 0`. -/
private lemma pf4_G_strictMonoOn {r : ℝ → ℝ} (hr : IsIsoLink r) {γin γout s : ℝ}
    (hγin : 0 < γin) (hγout : 0 < γout) (hs : 0 < s) :
    StrictMonoOn (isoG r γin γout s) (isoDr r γin γout) := by
  intro a ha b hb hab
  obtain ⟨ha0, ha2⟩ := (pf4_mem_D).1 ha
  obtain ⟨hb0, hb2⟩ := (pf4_mem_D).1 hb
  have hrab : r a < r b := hr.2.1 (Set.mem_Ici.mpr ha0) (Set.mem_Ici.mpr hb0) hab
  have hbγin : r b < γin := lt_of_lt_of_le hb2 (min_le_left _ _)
  have hbγout : r b < γout := lt_of_lt_of_le hb2 (min_le_right _ _)
  have haγout : r a < γout := lt_of_lt_of_le ha2 (min_le_right _ _)
  have hk1 : 0 < s * (b - a) := mul_pos hs (by linarith)
  have hk2 : 0 < (r b - r a) * (γout + γin - r a - r b) :=
    mul_pos (by linarith) (by linarith)
  unfold isoG
  nlinarith [hk1, hk2]

/-- Private helper (task P-F.2.P4): a zero of `G_s` in `D_r` is positive. -/
private lemma pf4_pos_of_zero {r : ℝ → ℝ} (hr : IsIsoLink r) {γin γout s q : ℝ}
    (hγin : 0 < γin) (hγout : 0 < γout) (hs : 0 < s) (hqD : q ∈ isoDr r γin γout)
    (hG : isoG r γin γout s q = 0) : 0 < q := by
  obtain ⟨hq0, hqm⟩ := (pf4_mem_D).1 hqD
  have h1 : 0 < γout - r q := by linarith [min_le_right γin γout]
  have h2 : 0 < γin - r q := by linarith [min_le_left γin γout]
  have hP : 0 < (γout - r q) * (γin - r q) := mul_pos h1 h2
  unfold isoG at hG
  have hsq : 0 < s * q := by linarith
  nlinarith

/-- Private helper (task P-F.2.P4): a product bound `(a - x)(b - x) ≤ a b` for `0 ≤ x < a, b`. -/
private lemma pf4_prod_le (x a b : ℝ) (hx : 0 ≤ x) (h1 : x < a) (h2 : x < b) :
    (a - x) * (b - x) ≤ a * b := by
  nlinarith [mul_nonneg hx (show (0:ℝ) ≤ a + b - x by linarith)]

/-- Private helper (task P-F.2.P4): existence of a zero of `G_s` in `D_r` for `s > 0`, by the
intermediate value theorem applied to the continuous truncation `K` of `G_s`. -/
private lemma pf4_exists_root {r : ℝ → ℝ} (hr : IsIsoLink r) {γin γout s : ℝ}
    (hγin : 0 < γin) (hγout : 0 < γout) (hs : 0 < s) :
    ∃ q, q ∈ isoDr r γin γout ∧ isoG r γin γout s q = 0 := by
  have hm0 : 0 < min γin γout := lt_min hγin hγout
  have hsne : s ≠ 0 := hs.ne'
  have hprod0 : (γout - min γin γout) * (γin - min γin γout) = 0 := by
    rcases min_choice γin γout with h | h <;> rw [h] <;> ring
  obtain ⟨K, hKdef⟩ : ∃ K : ℝ → ℝ, K = fun q =>
      s * q - (γout - min (r q) (min γin γout)) * (γin - min (r q) (min γin γout)) :=
    ⟨_, rfl⟩
  have hKapp : ∀ q, K q =
      s * q - (γout - min (r q) (min γin γout)) * (γin - min (r q) (min γin γout)) := by
    intro q
    rw [hKdef]
  have hρ : ContinuousOn (fun q => min (r q) (min γin γout)) (Set.Ici 0) :=
    (continuous_id.min continuous_const).comp_continuousOn hr.1
  have hKc : ContinuousOn K (Set.Ici 0) := by
    rw [hKdef]
    exact ContinuousOn.sub (ContinuousOn.mul continuousOn_const continuousOn_id)
      (ContinuousOn.mul (ContinuousOn.sub continuousOn_const hρ)
        (ContinuousOn.sub continuousOn_const hρ))
  have hK0 : K 0 = -(γout * γin) := by
    rw [hKapp, hr.2.2, min_eq_left hm0.le]
    ring
  have hcand : ∃ Q, 0 ≤ Q ∧ 0 ≤ K Q := by
    by_cases hex : ∃ Q, 0 ≤ Q ∧ min γin γout ≤ r Q
    · obtain ⟨Q, hQ0, hQm⟩ := hex
      refine ⟨Q, hQ0, ?_⟩
      rw [hKapp, min_eq_right hQm, hprod0]
      nlinarith [mul_nonneg hs.le hQ0]
    · push_neg at hex
      have hQ0 : (0:ℝ) ≤ γin * γout / s := div_nonneg (mul_pos hγin hγout).le hs.le
      refine ⟨γin * γout / s, hQ0, ?_⟩
      have hrQ0 : 0 ≤ r (γin * γout / s) := by
        have := hr.2.1.monotoneOn (Set.mem_Ici.mpr (le_refl (0:ℝ))) (Set.mem_Ici.mpr hQ0) hQ0
        rw [hr.2.2] at this
        exact this
      have hrQm := hex _ hQ0
      have hsQ : s * (γin * γout / s) = γin * γout := by field_simp
      have h1 : r (γin * γout / s) < γin := lt_of_lt_of_le hrQm (min_le_left _ _)
      have h2 : r (γin * γout / s) < γout := lt_of_lt_of_le hrQm (min_le_right _ _)
      rw [hKapp, min_eq_left hrQm.le, hsQ]
      linarith [pf4_prod_le _ γout γin hrQ0 h2 h1]
  obtain ⟨Q, hQ0, hKQ⟩ := hcand
  have hIVT := intermediate_value_Icc hQ0 (hKc.mono Set.Icc_subset_Ici_self)
  obtain ⟨z, hz, hKz⟩ := hIVT (show (0:ℝ) ∈ Set.Icc (K 0) (K Q) from
    ⟨by rw [hK0]; linarith [mul_pos hγout hγin], hKQ⟩)
  have hz0 : 0 ≤ z := hz.1
  by_cases hzm : min γin γout ≤ r z
  · exfalso
    have hKz' : s * z = 0 := by
      rw [hKapp, min_eq_right hzm, hprod0] at hKz
      linarith
    have hz00 : z = 0 := by
      rcases mul_eq_zero.1 hKz' with h | h
      · exact absurd h hsne
      · exact h
    rw [hz00, hr.2.2] at hzm
    linarith
  · push_neg at hzm
    refine ⟨z, (pf4_mem_D).2 ⟨hz0, hzm⟩, ?_⟩
    rw [hKapp, min_eq_left hzm.le] at hKz
    unfold isoG
    linarith

/-- Private helper (task P-F.2.P4): the chosen root `isoRoot` is a zero of `G_s` in `D_r`. -/
private lemma pf4_root_spec {r : ℝ → ℝ} (hr : IsIsoLink r) {γin γout s : ℝ}
    (hγin : 0 < γin) (hγout : 0 < γout) (hs : 0 < s) :
    isoRoot r γin γout s ∈ isoDr r γin γout ∧
      isoG r γin γout s (isoRoot r γin γout s) = 0 := by
  have hex := pf4_exists_root hr hγin hγout hs
  unfold isoRoot
  rw [dif_pos hex]
  exact hex.choose_spec

/-- Private helper (task P-F.2.P4): local perturbation bound for the zero of `G_{s0}`. -/
private lemma pf4_perturb {r : ℝ → ℝ} (hr : IsIsoLink r) {γin γout s0 q0 : ℝ}
    (hγin : 0 < γin) (hγout : 0 < γout) (hs0 : 0 < s0)
    (hq0 : q0 ∈ isoDr r γin γout) (hG0 : isoG r γin γout s0 q0 = 0) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ s : ℝ, 0 < s → |s - s0| < δ → ∀ q, q ∈ isoDr r γin γout →
      isoG r γin γout s q = 0 → |q - q0| < ε := by
  have hD : (isoDr r γin γout).OrdConnected := pf4_D_ordConnected hr
  have hm0 : 0 < min γin γout := lt_min hγin hγout
  have hq0pos : 0 < q0 := pf4_pos_of_zero hr hγin hγout hs0 hq0 hG0
  obtain ⟨hq0a, hq0b⟩ := (pf4_mem_D).1 hq0
  have hz0D : (0:ℝ) ∈ isoDr r γin γout := (pf4_mem_D).2 ⟨le_refl _, by rw [hr.2.2]; exact hm0⟩
  have hmin_pos : 0 < min ε q0 := lt_min hε hq0pos
  have hmin_le_ε : min ε q0 ≤ ε := min_le_left _ _
  have hmin_le_q0 : min ε q0 ≤ q0 := min_le_right _ _
  -- lower point a = q0 - min(ε, q0)/2 in D
  obtain ⟨a, ha_def⟩ : ∃ a, a = q0 - min ε q0 / 2 := ⟨_, rfl⟩
  have haD : a ∈ isoDr r γin γout :=
    hD.out hz0D hq0 (show a ∈ Set.Icc 0 q0 from ⟨by linarith, by linarith⟩)
  -- upper point b = q0 + t in D, with t < ε (uses continuity of r at q0)
  obtain ⟨δr, hδr, hδr'⟩ := Metric.continuousOn_iff.1 hr.1 q0 (Set.mem_Ici.mpr hq0a)
    (min γin γout - r q0) (by linarith [min_le_right γin γout])
  obtain ⟨t, ht_def⟩ : ∃ t, t = min δr ε / 2 := ⟨_, rfl⟩
  have hmin2 : 0 < min δr ε := lt_min hδr hε
  have htpos : 0 < t := by linarith
  have htε : t < ε := by linarith [min_le_right δr ε]
  have hbD : q0 + t ∈ isoDr r γin γout := by
    refine (pf4_mem_D).2 ⟨by linarith, ?_⟩
    have hd : dist (q0 + t) q0 < δr := by
      rw [Real.dist_eq, show q0 + t - q0 = t by ring, abs_of_pos htpos]
      linarith [min_le_left δr ε]
    have := hδr' (q0 + t) (Set.mem_Ici.mpr (by linarith)) hd
    rw [Real.dist_eq, abs_lt] at this
    linarith [this.2]
  have hGa : isoG r γin γout s0 a < 0 := by
    have := pf4_G_strictMonoOn hr hγin hγout hs0 haD hq0 (show a < q0 by linarith)
    rw [hG0] at this
    exact this
  have hGb : 0 < isoG r γin γout s0 (q0 + t) := by
    have := pf4_G_strictMonoOn hr hγin hγout hs0 hq0 hbD (show q0 < q0 + t by linarith)
    rw [hG0] at this
    exact this
  obtain ⟨ν, hν⟩ : ∃ ν, ν = min (-isoG r γin γout s0 a) (isoG r γin γout s0 (q0 + t)) :=
    ⟨_, rfl⟩
  have hνpos : 0 < ν := by rw [hν]; exact lt_min (by linarith) hGb
  have hνa : ν ≤ -isoG r γin γout s0 a := by rw [hν]; exact min_le_left _ _
  have hνb : ν ≤ isoG r γin γout s0 (q0 + t) := by rw [hν]; exact min_le_right _ _
  have hB1 : 0 < q0 + t + 1 := by linarith
  refine ⟨ν / (q0 + t + 1), div_pos hνpos hB1, ?_⟩
  intro s hs hsd q hqD hGq
  have hsd' : |s - s0| * (q0 + t + 1) < ν := by
    have h1 := mul_lt_mul_of_pos_right hsd hB1
    rwa [div_mul_cancel₀ _ hB1.ne'] at h1
  have hab : a ≤ q0 + t := by linarith
  have hA : (s - s0) * a < ν := by
    have h1 : (s - s0) * a ≤ |s - s0| * a :=
      mul_le_mul_of_nonneg_right (le_abs_self _) (by linarith)
    have h2 : |s - s0| * a ≤ |s - s0| * (q0 + t) :=
      mul_le_mul_of_nonneg_left hab (abs_nonneg _)
    have h3 : |s - s0| * (q0 + t) ≤ |s - s0| * (q0 + t + 1) :=
      mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg _)
    linarith
  have hB : -((s - s0) * (q0 + t)) < ν := by
    have h1 : -(s - s0) * (q0 + t) ≤ |s - s0| * (q0 + t) :=
      mul_le_mul_of_nonneg_right (neg_le_abs _) (by linarith)
    have h3 : |s - s0| * (q0 + t) ≤ |s - s0| * (q0 + t + 1) :=
      mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg _)
    linarith
  have hGsa : isoG r γin γout s a < 0 := by
    unfold isoG at hGa hνa ⊢
    linarith
  have hGsb : 0 < isoG r γin γout s (q0 + t) := by
    unfold isoG at hGb hνb ⊢
    linarith
  have hsmono := pf4_G_strictMonoOn hr hγin hγout hs
  have hlo : a < q := by
    by_contra h
    push_neg at h
    have := hsmono.monotoneOn hqD haD h
    linarith
  have hhi : q < q0 + t := by
    by_contra h
    push_neg at h
    have := hsmono.monotoneOn hbD hqD h
    linarith
  rw [abs_sub_lt_iff]
  constructor <;> linarith

/-- Private helper (task P-F.2.P4): `s ↦ q_r(s)` is continuous on `(0,∞)`. -/
private lemma pf4_root_continuousOn {r : ℝ → ℝ} (hr : IsIsoLink r) {γin γout : ℝ}
    (hγin : 0 < γin) (hγout : 0 < γout) :
    ContinuousOn (isoRoot r γin γout) (Set.Ioi 0) := by
  intro s0 hs0
  have hs0' : (0:ℝ) < s0 := hs0
  obtain ⟨hq0D, hq0G⟩ := pf4_root_spec hr hγin hγout hs0'
  rw [Metric.continuousWithinAt_iff]
  intro ε hε
  obtain ⟨δ, hδ, hpert⟩ := pf4_perturb hr hγin hγout hs0' hq0D hq0G hε
  refine ⟨δ, hδ, fun {x} hx hxd => ?_⟩
  have hxpos : (0:ℝ) < x := hx
  rw [Real.dist_eq] at hxd ⊢
  exact hpert x hxpos hxd _ (pf4_root_spec hr hγin hγout hxpos).1
    (pf4_root_spec hr hγin hγout hxpos).2

/-- Private helper (task P-F.2.P4): `s ↦ q_r(s)` is strictly decreasing on `(0,∞)`. -/
private lemma pf4_root_strictAnti {r : ℝ → ℝ} (hr : IsIsoLink r) {γin γout : ℝ}
    (hγin : 0 < γin) (hγout : 0 < γout) :
    StrictAntiOn (isoRoot r γin γout) (Set.Ioi 0) := by
  intro s1 hs1 s2 hs2 hlt
  have h1 : (0:ℝ) < s1 := hs1
  have h2 : (0:ℝ) < s2 := hs2
  obtain ⟨hD1, hG1⟩ := pf4_root_spec hr hγin hγout h1
  obtain ⟨hD2, hG2⟩ := pf4_root_spec hr hγin hγout h2
  by_contra hcon
  push_neg at hcon
  have hmono := (pf4_G_strictMonoOn hr hγin hγout h1).monotoneOn hD1 hD2 hcon
  have hq2pos := pf4_pos_of_zero hr hγin hγout h2 hD2 hG2
  have hneg : (s1 - s2) * isoRoot r γin γout s2 < 0 :=
    mul_neg_of_neg_of_pos (by linarith) hq2pos
  unfold isoG at hmono hG1 hG2
  linarith


/-- `lem:app-iso-comparison`(i), snapshot `cr-2026-10-23`. The whole lemma environment, verbatim
(`sections/05b-isotropic/section.tex`):
```latex
\begin{lemma}[Root comparison]\label{lem:app-iso-comparison}
Let $r$ be continuous and strictly increasing on $[0,\infty)$ with $r(0)=0$,
let $\gin,\gout,s>0$, and put $D_r\defeq\{q\ge0:\ r(q)<\gamma_\wedge\}$.
\begin{enumerate}[label=(\roman*)]
\item The function
\[
G_r(q)\defeq s\,q-\big(\gout-r(q)\big)\big(\gin-r(q)\big)
\]
is strictly increasing on the interval $D_r$ and has exactly one zero
$q_r(s)$ there. The map $s\mapsto q_r(s)$ is continuous and strictly decreasing.
\item Let $r_1,r_2$ be two such functions, with zeros $q_1=q_{r_1}(s)$ and
$q_2=q_{r_2}(s)$ at the same $s$. If $r_1(q_i)\le r_2(q_i)$ for $i=1$ or for
$i=2$, then $q_2\le q_1$.
\end{enumerate}
For $r=r_\bmom$ the zero is the root of \cref{prop:app-iso-closure}(ii):
$q_{r_\bmom}(s)=q(-s)$.
\end{lemma}
```
Part (i). Encoding: `D_r = isoDr r γin γout` and `G_r = isoG r γin γout s`; `q_r(s) = isoRoot r γin γout s`. Continuity and strict decrease are on `s > 0`. -/
theorem lem_app_iso_comparison_i {r : ℝ → ℝ} (hr : IsIsoLink r) {γin γout : ℝ}
    (hγin : 0 < γin) (hγout : 0 < γout) :
    (isoDr r γin γout).OrdConnected ∧
    (∀ s : ℝ, 0 < s → ∃! q, q ∈ isoDr r γin γout ∧ isoG r γin γout s q = 0) ∧
    (∀ s : ℝ, 0 < s → StrictMonoOn (isoG r γin γout s) (isoDr r γin γout)) ∧
    (∀ s : ℝ, 0 < s →
      isoRoot r γin γout s ∈ isoDr r γin γout ∧ isoG r γin γout s (isoRoot r γin γout s) = 0) ∧
    ContinuousOn (isoRoot r γin γout) (Ioi 0) ∧
    StrictAntiOn (isoRoot r γin γout) (Ioi 0) := by
  refine ⟨pf4_D_ordConnected hr, ?_, fun s hs => pf4_G_strictMonoOn hr hγin hγout hs,
    fun s hs => pf4_root_spec hr hγin hγout hs, pf4_root_continuousOn hr hγin hγout,
    pf4_root_strictAnti hr hγin hγout⟩
  intro s hs
  obtain ⟨z, hzD, hzG⟩ := pf4_exists_root hr hγin hγout hs
  refine ⟨z, ⟨hzD, hzG⟩, fun y hy => ?_⟩
  obtain ⟨hyD, hyG⟩ := hy
  by_contra hne
  rcases lt_or_gt_of_ne hne with h | h
  · have := pf4_G_strictMonoOn hr hγin hγout hs hyD hzD h
    linarith
  · have := pf4_G_strictMonoOn hr hγin hγout hs hzD hyD h
    linarith

/-- `lem:app-iso-comparison`(ii), snapshot `cr-2026-10-23`. The whole lemma environment, verbatim
(`sections/05b-isotropic/section.tex`):
```latex
\begin{lemma}[Root comparison]\label{lem:app-iso-comparison}
Let $r$ be continuous and strictly increasing on $[0,\infty)$ with $r(0)=0$,
let $\gin,\gout,s>0$, and put $D_r\defeq\{q\ge0:\ r(q)<\gamma_\wedge\}$.
\begin{enumerate}[label=(\roman*)]
\item The function
\[
G_r(q)\defeq s\,q-\big(\gout-r(q)\big)\big(\gin-r(q)\big)
\]
is strictly increasing on the interval $D_r$ and has exactly one zero
$q_r(s)$ there. The map $s\mapsto q_r(s)$ is continuous and strictly decreasing.
\item Let $r_1,r_2$ be two such functions, with zeros $q_1=q_{r_1}(s)$ and
$q_2=q_{r_2}(s)$ at the same $s$. If $r_1(q_i)\le r_2(q_i)$ for $i=1$ or for
$i=2$, then $q_2\le q_1$.
\end{enumerate}
For $r=r_\bmom$ the zero is the root of \cref{prop:app-iso-closure}(ii):
$q_{r_\bmom}(s)=q(-s)$.
\end{lemma}
```
Part (ii). Encoding: `q_i = isoRoot r_i γin γout s`; the hypothesis `r₁(q_i) ≤ r₂(q_i)` for `i = 1` or `i = 2` is the disjunction `h`. -/
theorem lem_app_iso_comparison_ii {r₁ r₂ : ℝ → ℝ} (hr₁ : IsIsoLink r₁) (hr₂ : IsIsoLink r₂)
    {γin γout s : ℝ} (hγin : 0 < γin) (hγout : 0 < γout) (hs : 0 < s)
    (h : r₁ (isoRoot r₁ γin γout s) ≤ r₂ (isoRoot r₁ γin γout s) ∨
      r₁ (isoRoot r₂ γin γout s) ≤ r₂ (isoRoot r₂ γin γout s)) :
    isoRoot r₂ γin γout s ≤ isoRoot r₁ γin γout s := by
  have hprod : ∀ a b : ℝ, a ≤ b → b < min γin γout →
      (γout - b) * (γin - b) ≤ (γout - a) * (γin - a) := by
    intro a b hab hb
    have h1 : 0 < γout - b := by linarith [min_le_right γin γout]
    have h2 : 0 < γin - b := by linarith [min_le_left γin γout]
    exact mul_le_mul (by linarith) (by linarith) h2.le (by linarith)
  have hq1 := pf4_root_spec hr₁ hγin hγout hs
  have hq2 := pf4_root_spec hr₂ hγin hγout hs
  have hm1 := pf4_G_strictMonoOn hr₁ hγin hγout hs
  have hm2 := pf4_G_strictMonoOn hr₂ hγin hγout hs
  have hq1nn : 0 ≤ isoRoot r₁ γin γout s := ((pf4_mem_D).1 hq1.1).1
  have hq2nn : 0 ≤ isoRoot r₂ γin γout s := ((pf4_mem_D).1 hq2.1).1
  have hq2m : r₂ (isoRoot r₂ γin γout s) < min γin γout := ((pf4_mem_D).1 hq2.1).2
  by_contra hlt
  push_neg at hlt
  rcases h with h | h
  · have hD : isoRoot r₁ γin γout s ∈ isoDr r₂ γin γout :=
      (pf4_mem_D).2 ⟨hq1nn, lt_of_le_of_lt
        (hr₂.2.1.monotoneOn (Set.mem_Ici.mpr hq1nn) (Set.mem_Ici.mpr hq2nn) hlt.le) hq2m⟩
    have h1 := hm2 hD hq2.1 hlt
    have h2 := hprod _ _ h ((pf4_mem_D).1 hD).2
    have hG1 := hq1.2
    have hG2 := hq2.2
    unfold isoG at h1 hG1 hG2
    linarith
  · have hD : isoRoot r₂ γin γout s ∈ isoDr r₁ γin γout :=
      (pf4_mem_D).2 ⟨hq2nn, lt_of_le_of_lt h hq2m⟩
    have h1 := hm1 hq1.1 hD hlt
    have h2 := hprod _ _ h hq2m
    have hG1 := hq1.2
    have hG2 := hq2.2
    unfold isoG at h1 hG1 hG2
    linarith

/-- `lem:app-iso-comparison`(iii), snapshot `cr-2026-10-23`. The whole lemma environment, verbatim
(`sections/05b-isotropic/section.tex`):
```latex
\begin{lemma}[Root comparison]\label{lem:app-iso-comparison}
Let $r$ be continuous and strictly increasing on $[0,\infty)$ with $r(0)=0$,
let $\gin,\gout,s>0$, and put $D_r\defeq\{q\ge0:\ r(q)<\gamma_\wedge\}$.
\begin{enumerate}[label=(\roman*)]
\item The function
\[
G_r(q)\defeq s\,q-\big(\gout-r(q)\big)\big(\gin-r(q)\big)
\]
is strictly increasing on the interval $D_r$ and has exactly one zero
$q_r(s)$ there. The map $s\mapsto q_r(s)$ is continuous and strictly decreasing.
\item Let $r_1,r_2$ be two such functions, with zeros $q_1=q_{r_1}(s)$ and
$q_2=q_{r_2}(s)$ at the same $s$. If $r_1(q_i)\le r_2(q_i)$ for $i=1$ or for
$i=2$, then $q_2\le q_1$.
\end{enumerate}
For $r=r_\bmom$ the zero is the root of \cref{prop:app-iso-closure}(ii):
$q_{r_\bmom}(s)=q(-s)$.
\end{lemma}
```
Final sentence of the lemma, "For $r=r_\bmom$ the zero is the root of \cref{prop:app-iso-closure}(ii): $q_{r_\bmom}(s)=q(-s)$". Encoding: `r_β = rW (Muon.emaW β)`; `q(−s) = isoQ s x` for any branch solution `x`. -/
theorem lem_app_iso_comparison_iii {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {γin γout s : ℝ}
    (hγin : 0 < γin) (hγout : 0 < γout) (hs : 0 < s)
    {ν ν' : FiniteMeasure ℝ} (hν : (ν : Measure ℝ) = isoSpecMeasure γout)
    (hν' : (ν' : Measure ℝ) = isoSpecMeasure γin)
    {x : ℝ × ℝ × ℝ × ℝ} (hx : IsBranchSol (Fw (Muon.emaW β)) ν ν' s x) :
    isoRoot (rW (Muon.emaW β)) γin γout s = isoQ s x := by
  obtain ⟨hpos, hlt, hsc, huniq⟩ := prop_app_iso_closure_ii hβ0 hβ1 hγin hγout hs hν hν' hx
  have hr := cl_ii_isoLink hβ0 hβ1
  obtain ⟨hD, hG⟩ := pf4_root_spec hr hγin hγout hs
  have hqpos := pf4_pos_of_zero hr hγin hγout hs hD hG
  unfold isoG at hG
  exact huniq _ hqpos ((pf4_mem_D).1 hD).2 (by linarith)

end Muon.Isotropic

end
