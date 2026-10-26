import Muon.DetEquiv.Scalar
import Muon.DetEquiv.Concentration

/-!
# Muon.Drift: derivative bounds (work package L-C.3)

Statements of `lem:app-drift-derivatives` (parts `_i`..`_vi`, one theorem per displayed
inequality) of `sections/03-drift/section.tex`, snapshot `cr-2026-10-23`, together with the
two calculus helpers F15 and F9 of `sections/03-drift/CARD.md` §4. All proofs are `sorry`
(proof cards P1-P4 in `results/L-C.3-interface.json`).

The functions `fX x d = d/(1+x d^2)` and `psiX x d = d^2/(1+x d^2)` are the project's
`Muon.DetEquiv.fX`, `Muon.DetEquiv.psiX` (`lem:app-de-replace`); `J` is `Muon.DetEquiv.J`.
Sup-norm bounds `‖·‖_∞ ≤ c` over `d ∈ ℝ` are stated pointwise `∀ d`, which is equivalent and
has no `iSup` junk. The `x`-derivatives are two-sided `deriv`s at `x ≥ 0`; for fixed `d` the
map `y ↦ fX y d` is smooth on a neighbourhood of every `x ≥ 0` (the denominator `1 + y d²` is
positive for `|y| < 1/(1+d²)`), so the one-sided derivative at `x = 0` (card §6.13) equals the
two-sided one.
-/

open MeasureTheory Filter Topology Set Real
open Muon.DetEquiv

namespace Muon.Drift

private lemma drift_den_pos {x d : ℝ} (hx : 0 ≤ x) : 0 < 1 + x * d ^ 2 := by
  have := mul_nonneg hx (sq_nonneg d)
  linarith

private lemma drift_hden_nz {x d : ℝ} (hx : 0 ≤ x) : 1 + x * d ^ 2 ≠ 0 :=
  (drift_den_pos (d := d) hx).ne'

private lemma drift_hpow2 (d : ℝ) : HasDerivAt (fun y : ℝ => y ^ 2) (2 * d) d := by
  simpa using hasDerivAt_pow 2 d

private lemma drift_hpow3 (d : ℝ) : HasDerivAt (fun y : ℝ => y ^ 3) (3 * d ^ 2) d := by
  simpa using hasDerivAt_pow 3 d

private lemma drift_hden (x d : ℝ) :
    HasDerivAt (fun y : ℝ => 1 + x * y ^ 2) (x * (2 * d)) d :=
  ((drift_hpow2 d).const_mul x).const_add 1

private lemma drift_poly_bounds (t : ℝ) (ht : 0 ≤ t) :
    0 ≤ 36 * (1 + t) ^ 4 - (-6 + 36 * t - 6 * t ^ 2) ∧
      0 ≤ 36 * (1 + t) ^ 4 + (-6 + 36 * t - 6 * t ^ 2) := by
  constructor <;> nlinarith [mul_nonneg ht ht, mul_nonneg (mul_nonneg ht ht) ht, pow_nonneg ht 4]

private lemma drift_deriv1 {x : ℝ} (hx : 0 ≤ x) (d : ℝ) :
    HasDerivAt (fX x) ((1 - x * d ^ 2) / ((1 + x * d ^ 2) * (1 + x * d ^ 2))) d := by
  have hD := drift_hden_nz (d := d) hx
  have h := (hasDerivAt_id' d).div (drift_hden x d) hD
  exact h.congr_deriv (by (try simp only [Pi.mul_apply]); field_simp; ring)

private lemma drift_deriv2 {x : ℝ} (hx : 0 ≤ x) (d : ℝ) :
    HasDerivAt (fun y : ℝ => (1 - x * y ^ 2) / ((1 + x * y ^ 2) * (1 + x * y ^ 2)))
      ((-6 * x * d + 2 * x ^ 2 * d ^ 3) / ((1 + x * d ^ 2) * (1 + x * d ^ 2) * (1 + x * d ^ 2))) d := by
  have hD := drift_hden_nz (d := d) hx
  have hn : HasDerivAt (fun y : ℝ => 1 - x * y ^ 2) (-(x * (2 * d))) d :=
    ((drift_hpow2 d).const_mul x).const_sub 1
  have h := hn.div ((drift_hden x d).mul (drift_hden x d)) (mul_ne_zero hD hD)
  exact h.congr_deriv (by (try simp only [Pi.mul_apply]); field_simp; ring)

private lemma drift_deriv3 {x : ℝ} (hx : 0 ≤ x) (d : ℝ) :
    HasDerivAt (fun y : ℝ => (-6 * x * y + 2 * x ^ 2 * y ^ 3) /
        ((1 + x * y ^ 2) * (1 + x * y ^ 2) * (1 + x * y ^ 2)))
      ((-6 * x + 36 * x ^ 2 * d ^ 2 - 6 * x ^ 3 * d ^ 4) /
        ((1 + x * d ^ 2) * (1 + x * d ^ 2) * (1 + x * d ^ 2) * (1 + x * d ^ 2))) d := by
  have hD := drift_hden_nz (d := d) hx
  have hnum : HasDerivAt (fun y : ℝ => -6 * x * y + 2 * x ^ 2 * y ^ 3)
      (-6 * x + 2 * x ^ 2 * (3 * d ^ 2)) d :=
    (((hasDerivAt_id' d).const_mul (-6 * x)).add ((drift_hpow3 d).const_mul (2 * x ^ 2))).congr_deriv
      (by ring)
  have hden := ((drift_hden x d).mul (drift_hden x d)).mul (drift_hden x d)
  have h := hnum.div hden (mul_ne_zero (mul_ne_zero hD hD) hD)
  exact h.congr_deriv (by (try simp only [Pi.mul_apply]); field_simp; ring)

private lemma drift_psi1 {x : ℝ} (hx : 0 ≤ x) (d : ℝ) :
    HasDerivAt (psiX x) (2 * d / ((1 + x * d ^ 2) * (1 + x * d ^ 2))) d := by
  have hD := drift_hden_nz (d := d) hx
  have h := (drift_hpow2 d).div (drift_hden x d) hD
  exact h.congr_deriv (by (try simp only [Pi.mul_apply]); field_simp; ring)

private lemma drift_psi2 {x : ℝ} (hx : 0 ≤ x) (d : ℝ) :
    HasDerivAt (fun y : ℝ => 2 * y / ((1 + x * y ^ 2) * (1 + x * y ^ 2)))
      ((2 - 6 * x * d ^ 2) / ((1 + x * d ^ 2) * (1 + x * d ^ 2) * (1 + x * d ^ 2))) d := by
  have hD := drift_hden_nz (d := d) hx
  have hn : HasDerivAt (fun y : ℝ => 2 * y) 2 d := by
    simpa using (hasDerivAt_id' d).const_mul 2
  have h := hn.div ((drift_hden x d).mul (drift_hden x d)) (mul_ne_zero hD hD)
  exact h.congr_deriv (by (try simp only [Pi.mul_apply]); field_simp; ring)

private lemma drift_deriv_fX {x : ℝ} (hx : 0 ≤ x) :
    deriv (fX x) = fun d => (1 - x * d ^ 2) / ((1 + x * d ^ 2) * (1 + x * d ^ 2)) :=
  funext fun d => (drift_deriv1 hx d).deriv

private lemma drift_deriv_fX2 {x : ℝ} (hx : 0 ≤ x) :
    deriv (fun y : ℝ => (1 - x * y ^ 2) / ((1 + x * y ^ 2) * (1 + x * y ^ 2))) =
      fun d => (-6 * x * d + 2 * x ^ 2 * d ^ 3) /
        ((1 + x * d ^ 2) * (1 + x * d ^ 2) * (1 + x * d ^ 2)) :=
  funext fun d => (drift_deriv2 hx d).deriv

private lemma drift_deriv_fX3 {x : ℝ} (hx : 0 ≤ x) :
    deriv (fun y : ℝ => (-6 * x * y + 2 * x ^ 2 * y ^ 3) /
        ((1 + x * y ^ 2) * (1 + x * y ^ 2) * (1 + x * y ^ 2))) =
      fun d => (-6 * x + 36 * x ^ 2 * d ^ 2 - 6 * x ^ 3 * d ^ 4) /
        ((1 + x * d ^ 2) * (1 + x * d ^ 2) * (1 + x * d ^ 2) * (1 + x * d ^ 2)) :=
  funext fun d => (drift_deriv3 hx d).deriv

private lemma drift_deriv_psi {x : ℝ} (hx : 0 ≤ x) :
    deriv (psiX x) = fun d => 2 * d / ((1 + x * d ^ 2) * (1 + x * d ^ 2)) :=
  funext fun d => (drift_psi1 hx d).deriv

private lemma drift_deriv_psi2 {x : ℝ} (hx : 0 ≤ x) :
    deriv (fun y : ℝ => 2 * y / ((1 + x * y ^ 2) * (1 + x * y ^ 2))) =
      fun d => (2 - 6 * x * d ^ 2) / ((1 + x * d ^ 2) * (1 + x * d ^ 2) * (1 + x * d ^ 2)) :=
  funext fun d => (drift_psi2 hx d).deriv

private lemma drift_deriv1_ne {x d : ℝ} (hD : 1 + x * d ^ 2 ≠ 0) :
    HasDerivAt (fX x) ((1 - x * d ^ 2) / ((1 + x * d ^ 2) * (1 + x * d ^ 2))) d := by
  have h := (hasDerivAt_id' d).div (drift_hden x d) hD
  exact h.congr_deriv (by (try simp only [Pi.mul_apply]); field_simp; ring)

private lemma drift_hq (x d : ℝ) : HasDerivAt (fun y : ℝ => 1 + y * d ^ 2) (1 * d ^ 2) x :=
  ((hasDerivAt_id' x).mul_const (d ^ 2)).const_add 1

private lemma drift_dx_fX (x d : ℝ) (hD : 1 + x * d ^ 2 ≠ 0) :
    HasDerivAt (fun y : ℝ => d / (1 + y * d ^ 2))
      (-(d ^ 3) / ((1 + x * d ^ 2) * (1 + x * d ^ 2))) x := by
  have h := (hasDerivAt_const x d).div (drift_hq x d) hD
  exact h.congr_deriv (by field_simp; ring)

private lemma drift_dx_psiX (x d : ℝ) (hD : 1 + x * d ^ 2 ≠ 0) :
    HasDerivAt (fun y : ℝ => d ^ 2 / (1 + y * d ^ 2))
      (-(d ^ 4) / ((1 + x * d ^ 2) * (1 + x * d ^ 2))) x := by
  have h := (hasDerivAt_const x (d ^ 2)).div (drift_hq x d) hD
  exact h.congr_deriv (by field_simp; ring)

private lemma drift_dx_g (x d : ℝ) (hD : 1 + x * d ^ 2 ≠ 0) :
    HasDerivAt (fun y : ℝ => (1 - y * d ^ 2) / ((1 + y * d ^ 2) * (1 + y * d ^ 2)))
      (d ^ 2 * (x * d ^ 2 - 3) / ((1 + x * d ^ 2) * (1 + x * d ^ 2) * (1 + x * d ^ 2))) x := by
  have hn : HasDerivAt (fun y : ℝ => 1 - y * d ^ 2) (-(1 * d ^ 2)) x :=
    ((hasDerivAt_id' x).mul_const (d ^ 2)).const_sub 1
  have h := hn.div ((drift_hq x d).mul (drift_hq x d)) (mul_ne_zero hD hD)
  exact h.congr_deriv (by (try simp only [Pi.mul_apply]); field_simp; ring)


/-- `lem:app-drift-derivatives` (part (i)), snapshot `cr-2026-10-23`. Part `‖f_x'‖_∞ ≤ 1`, the first bound of `eqn:app-drift-derivatives`, stated pointwise in `d`.

Frozen LaTeX (`sections/03-drift/section.tex`, lines 590–599), verbatim:
```
\begin{lemma}[Derivative bounds]\label{lem:app-drift-derivatives}
For $x\ge0$ let $f_x(d)=d/(1+xd^2)$ and $\psi_x(d)=d^2/(1+xd^2)$ as in
\cref{lem:app-de-replace}. Then for all $d\in\R$,
\begin{equation}\label{eqn:app-drift-derivatives}
\begin{gathered}
\norm{f_x'}_\infty\le1,\qquad\norm{f_x'''}_\infty\le36x,\qquad\norm{\psi_x''}_\infty\le6,\\
\abs{\partial_xf_x(d)}\le\abs d^3,\qquad\abs{\partial_x\psi_x(d)}\le d^4,\qquad\abs{\partial_xf_x'(d)}\le3d^2 .
\end{gathered}
\end{equation}
\end{lemma}
```
-/
theorem lem_app_drift_derivatives_i {x : ℝ} (hx : 0 ≤ x) :
    ∀ d : ℝ, |deriv (fX x) d| ≤ 1 := by
  intro d
  rw [drift_deriv_fX hx]
  change |(1 - x * d ^ 2) / ((1 + x * d ^ 2) * (1 + x * d ^ 2))| ≤ 1
  have hD := drift_den_pos (d := d) hx
  have hDD : 0 < (1 + x * d ^ 2) * (1 + x * d ^ 2) := mul_pos hD hD
  have ht : 0 ≤ x * d ^ 2 := mul_nonneg hx (sq_nonneg d)
  rw [abs_div, abs_of_pos hDD, div_le_one hDD, abs_le]
  constructor <;> nlinarith [sq_nonneg (x * d ^ 2)]

/-- `lem:app-drift-derivatives` (part (ii)), snapshot `cr-2026-10-23`. Part `‖f_x'''‖_∞ ≤ 36x`, the second bound.

Frozen LaTeX (`sections/03-drift/section.tex`, lines 590–599), verbatim:
```
\begin{lemma}[Derivative bounds]\label{lem:app-drift-derivatives}
For $x\ge0$ let $f_x(d)=d/(1+xd^2)$ and $\psi_x(d)=d^2/(1+xd^2)$ as in
\cref{lem:app-de-replace}. Then for all $d\in\R$,
\begin{equation}\label{eqn:app-drift-derivatives}
\begin{gathered}
\norm{f_x'}_\infty\le1,\qquad\norm{f_x'''}_\infty\le36x,\qquad\norm{\psi_x''}_\infty\le6,\\
\abs{\partial_xf_x(d)}\le\abs d^3,\qquad\abs{\partial_x\psi_x(d)}\le d^4,\qquad\abs{\partial_xf_x'(d)}\le3d^2 .
\end{gathered}
\end{equation}
\end{lemma}
```
-/
theorem lem_app_drift_derivatives_ii {x : ℝ} (hx : 0 ≤ x) :
    ∀ d : ℝ, |iteratedDeriv 3 (fX x) d| ≤ 36 * x := by
  intro d
  have hit : iteratedDeriv 3 (fX x) = deriv (deriv (deriv (fX x))) := by
    rw [iteratedDeriv_eq_iterate]; rfl
  rw [hit, drift_deriv_fX hx, drift_deriv_fX2 hx, drift_deriv_fX3 hx]
  change |(-6 * x + 36 * x ^ 2 * d ^ 2 - 6 * x ^ 3 * d ^ 4) /
      ((1 + x * d ^ 2) * (1 + x * d ^ 2) * (1 + x * d ^ 2) * (1 + x * d ^ 2))| ≤ 36 * x
  have hD := drift_den_pos (d := d) hx
  have hb : 0 < (1 + x * d ^ 2) * (1 + x * d ^ 2) * (1 + x * d ^ 2) * (1 + x * d ^ 2) :=
    mul_pos (mul_pos (mul_pos hD hD) hD) hD
  have ht : 0 ≤ x * d ^ 2 := mul_nonneg hx (sq_nonneg d)
  obtain ⟨h1, h2⟩ := drift_poly_bounds (x * d ^ 2) ht
  have k1 := mul_nonneg hx h1
  have k2 := mul_nonneg hx h2
  rw [abs_div, abs_of_pos hb, div_le_iff₀ hb, abs_le]
  constructor <;> nlinarith [k1, k2]

/-- `lem:app-drift-derivatives` (part (iii)), snapshot `cr-2026-10-23`. Part `‖ψ_x''‖_∞ ≤ 6`, the third bound.

Frozen LaTeX (`sections/03-drift/section.tex`, lines 590–599), verbatim:
```
\begin{lemma}[Derivative bounds]\label{lem:app-drift-derivatives}
For $x\ge0$ let $f_x(d)=d/(1+xd^2)$ and $\psi_x(d)=d^2/(1+xd^2)$ as in
\cref{lem:app-de-replace}. Then for all $d\in\R$,
\begin{equation}\label{eqn:app-drift-derivatives}
\begin{gathered}
\norm{f_x'}_\infty\le1,\qquad\norm{f_x'''}_\infty\le36x,\qquad\norm{\psi_x''}_\infty\le6,\\
\abs{\partial_xf_x(d)}\le\abs d^3,\qquad\abs{\partial_x\psi_x(d)}\le d^4,\qquad\abs{\partial_xf_x'(d)}\le3d^2 .
\end{gathered}
\end{equation}
\end{lemma}
```
-/
theorem lem_app_drift_derivatives_iii {x : ℝ} (hx : 0 ≤ x) :
    ∀ d : ℝ, |iteratedDeriv 2 (psiX x) d| ≤ 6 := by
  intro d
  have hit : iteratedDeriv 2 (psiX x) = deriv (deriv (psiX x)) := by
    rw [iteratedDeriv_eq_iterate]; rfl
  rw [hit, drift_deriv_psi hx, drift_deriv_psi2 hx]
  change |(2 - 6 * x * d ^ 2) / ((1 + x * d ^ 2) * (1 + x * d ^ 2) * (1 + x * d ^ 2))| ≤ 6
  have hD := drift_den_pos (d := d) hx
  have hb : 0 < (1 + x * d ^ 2) * (1 + x * d ^ 2) * (1 + x * d ^ 2) :=
    mul_pos (mul_pos hD hD) hD
  have ht : 0 ≤ x * d ^ 2 := mul_nonneg hx (sq_nonneg d)
  rw [abs_div, abs_of_pos hb, div_le_iff₀ hb, abs_le]
  constructor <;> nlinarith [mul_nonneg ht ht, mul_nonneg (mul_nonneg ht ht) ht]

/-- `lem:app-drift-derivatives` (part (iv)), snapshot `cr-2026-10-23`. Part `|∂_x f_x(d)| ≤ |d|³`; `∂_x` is the derivative in the parameter `x` at the given `x ≥ 0` (two-sided, see module doc).

Frozen LaTeX (`sections/03-drift/section.tex`, lines 590–599), verbatim:
```
\begin{lemma}[Derivative bounds]\label{lem:app-drift-derivatives}
For $x\ge0$ let $f_x(d)=d/(1+xd^2)$ and $\psi_x(d)=d^2/(1+xd^2)$ as in
\cref{lem:app-de-replace}. Then for all $d\in\R$,
\begin{equation}\label{eqn:app-drift-derivatives}
\begin{gathered}
\norm{f_x'}_\infty\le1,\qquad\norm{f_x'''}_\infty\le36x,\qquad\norm{\psi_x''}_\infty\le6,\\
\abs{\partial_xf_x(d)}\le\abs d^3,\qquad\abs{\partial_x\psi_x(d)}\le d^4,\qquad\abs{\partial_xf_x'(d)}\le3d^2 .
\end{gathered}
\end{equation}
\end{lemma}
```
-/
theorem lem_app_drift_derivatives_iv {x : ℝ} (hx : 0 ≤ x) :
    ∀ d : ℝ, |deriv (fun y => fX y d) x| ≤ |d| ^ 3 := by
  intro d
  have hD := drift_den_pos (d := d) hx
  have hDD : 0 < (1 + x * d ^ 2) * (1 + x * d ^ 2) := mul_pos hD hD
  have ht : 0 ≤ x * d ^ 2 := mul_nonneg hx (sq_nonneg d)
  have h1 : 1 ≤ (1 + x * d ^ 2) * (1 + x * d ^ 2) := by nlinarith
  have e : deriv (fun y => fX y d) x = -(d ^ 3) / ((1 + x * d ^ 2) * (1 + x * d ^ 2)) :=
    (drift_dx_fX x d hD.ne').deriv
  rw [e, abs_div, abs_of_pos hDD, div_le_iff₀ hDD, abs_neg, abs_pow]
  nlinarith [mul_nonneg (pow_nonneg (abs_nonneg d) 3) (sub_nonneg.2 h1)]

/-- `lem:app-drift-derivatives` (part (v)), snapshot `cr-2026-10-23`. Part `|∂_x ψ_x(d)| ≤ d⁴`.

Frozen LaTeX (`sections/03-drift/section.tex`, lines 590–599), verbatim:
```
\begin{lemma}[Derivative bounds]\label{lem:app-drift-derivatives}
For $x\ge0$ let $f_x(d)=d/(1+xd^2)$ and $\psi_x(d)=d^2/(1+xd^2)$ as in
\cref{lem:app-de-replace}. Then for all $d\in\R$,
\begin{equation}\label{eqn:app-drift-derivatives}
\begin{gathered}
\norm{f_x'}_\infty\le1,\qquad\norm{f_x'''}_\infty\le36x,\qquad\norm{\psi_x''}_\infty\le6,\\
\abs{\partial_xf_x(d)}\le\abs d^3,\qquad\abs{\partial_x\psi_x(d)}\le d^4,\qquad\abs{\partial_xf_x'(d)}\le3d^2 .
\end{gathered}
\end{equation}
\end{lemma}
```
-/
theorem lem_app_drift_derivatives_v {x : ℝ} (hx : 0 ≤ x) :
    ∀ d : ℝ, |deriv (fun y => psiX y d) x| ≤ d ^ 4 := by
  intro d
  have hD := drift_den_pos (d := d) hx
  have hDD : 0 < (1 + x * d ^ 2) * (1 + x * d ^ 2) := mul_pos hD hD
  have ht : 0 ≤ x * d ^ 2 := mul_nonneg hx (sq_nonneg d)
  have h1 : 1 ≤ (1 + x * d ^ 2) * (1 + x * d ^ 2) := by nlinarith
  have e : deriv (fun y => psiX y d) x = -(d ^ 4) / ((1 + x * d ^ 2) * (1 + x * d ^ 2)) :=
    (drift_dx_psiX x d hD.ne').deriv
  have h4 : (0 : ℝ) ≤ d ^ 4 := by positivity
  rw [e, abs_div, abs_of_pos hDD, div_le_iff₀ hDD, abs_neg, abs_of_nonneg h4]
  nlinarith [mul_nonneg h4 (sub_nonneg.2 h1)]

/-- `lem:app-drift-derivatives` (part (vi)), snapshot `cr-2026-10-23`. Part `|∂_x f_x'(d)| ≤ 3d²`, where `f_x'` is the derivative in `d` of `f_x`.

Frozen LaTeX (`sections/03-drift/section.tex`, lines 590–599), verbatim:
```
\begin{lemma}[Derivative bounds]\label{lem:app-drift-derivatives}
For $x\ge0$ let $f_x(d)=d/(1+xd^2)$ and $\psi_x(d)=d^2/(1+xd^2)$ as in
\cref{lem:app-de-replace}. Then for all $d\in\R$,
\begin{equation}\label{eqn:app-drift-derivatives}
\begin{gathered}
\norm{f_x'}_\infty\le1,\qquad\norm{f_x'''}_\infty\le36x,\qquad\norm{\psi_x''}_\infty\le6,\\
\abs{\partial_xf_x(d)}\le\abs d^3,\qquad\abs{\partial_x\psi_x(d)}\le d^4,\qquad\abs{\partial_xf_x'(d)}\le3d^2 .
\end{gathered}
\end{equation}
\end{lemma}
```
-/
theorem lem_app_drift_derivatives_vi {x : ℝ} (hx : 0 ≤ x) :
    ∀ d : ℝ, |deriv (fun y => deriv (fX y) d) x| ≤ 3 * d ^ 2 := by
  intro d
  have hD := drift_den_pos (d := d) hx
  have hc : Continuous (fun y : ℝ => 1 + y * d ^ 2) := by fun_prop
  have hev : ∀ᶠ y in 𝓝 x, 0 < 1 + y * d ^ 2 :=
    hc.continuousAt.eventually (lt_mem_nhds hD)
  have hG := drift_dx_g x d hD.ne'
  have hfun : (fun y => deriv (fX y) d) =ᶠ[𝓝 x]
      (fun y : ℝ => (1 - y * d ^ 2) / ((1 + y * d ^ 2) * (1 + y * d ^ 2))) := by
    filter_upwards [hev] with y hy
    exact (drift_deriv1_ne (x := y) hy.ne').deriv
  have hD2 := (hG.congr_of_eventuallyEq hfun).deriv
  have hb : 0 < (1 + x * d ^ 2) * (1 + x * d ^ 2) * (1 + x * d ^ 2) :=
    mul_pos (mul_pos hD hD) hD
  have ht : 0 ≤ x * d ^ 2 := mul_nonneg hx (sq_nonneg d)
  have hc3 : |x * d ^ 2 - 3| ≤ 3 * ((1 + x * d ^ 2) * (1 + x * d ^ 2) * (1 + x * d ^ 2)) := by
    rw [abs_le]
    constructor <;> nlinarith [mul_nonneg ht ht, mul_nonneg (mul_nonneg ht ht) ht]
  rw [hD2, abs_div, abs_of_pos hb, div_le_iff₀ hb, abs_mul, abs_of_nonneg (sq_nonneg d)]
  nlinarith [mul_le_mul_of_nonneg_left hc3 (sq_nonneg d)]

private lemma abs_J_den_pos {v : ℝ} (hv : 0 ≤ v) (g : ℝ) : 0 < 1 + v * g ^ 2 := by
  have := mul_nonneg hv (sq_nonneg g)
  linarith

private lemma abs_J_g4_div_le {v : ℝ} (hv : 0 ≤ v) (g : ℝ) :
    g ^ 4 / (1 + v * g ^ 2) ^ 2 ≤ g ^ 4 := by
  have h1 : 1 ≤ (1 + v * g ^ 2) ^ 2 := by
    nlinarith [mul_nonneg hv (sq_nonneg g)]
  exact div_le_self (by positivity) h1

private lemma abs_J_integrable {v : ℝ} (hv : 0 ≤ v) :
    Integrable (fun g : ℝ => g ^ 2 / (1 + v * g ^ 2)) (ProbabilityTheory.gaussianReal 0 1) := by
  refine Integrable.mono' (Muon.Foundations.gaussian_integrable_pow 2) ?_ ?_
  · exact (by fun_prop : Measurable fun g : ℝ => g ^ 2 / (1 + v * g ^ 2)).aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun g => ?_
    show ‖g ^ 2 / (1 + v * g ^ 2)‖ ≤ g ^ 2
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (sq_nonneg g) (abs_J_den_pos hv g).le)]
    exact div_le_self (sq_nonneg g) (le_add_of_nonneg_right (mul_nonneg hv (sq_nonneg g)))

private lemma abs_J_hasDerivAt_term (g : ℝ) {v : ℝ} (hv : 0 ≤ v) :
    HasDerivAt (fun u : ℝ => g ^ 2 / (1 + u * g ^ 2)) (-(g ^ 4 / (1 + v * g ^ 2) ^ 2)) v := by
  have h1 : HasDerivAt (fun u : ℝ => u * g ^ 2) (1 * g ^ 2) v :=
    (hasDerivAt_id' v).mul_const (g ^ 2)
  have h2 : HasDerivAt (fun u : ℝ => 1 + u * g ^ 2) (1 * g ^ 2) v := h1.const_add 1
  have hne : 1 + v * g ^ 2 ≠ 0 := (abs_J_den_pos hv g).ne'
  refine ((hasDerivAt_const v (g ^ 2)).div h2 hne).congr_deriv ?_
  field_simp
  ring

private lemma abs_J_norm_le {x : ℝ} (hx : 0 ≤ x) (g : ℝ) :
    ‖-(g ^ 4 / (1 + x * g ^ 2) ^ 2)‖ ≤ g ^ 4 := by
  rw [norm_neg, Real.norm_eq_abs, abs_of_nonneg (div_nonneg (by positivity) (sq_nonneg _))]
  exact abs_J_g4_div_le hx g

/-- `J'(x) = -E[g⁴/(1+xg²)²]` for `x > 0` (differentiation under the integral sign). -/
private lemma abs_J_hasDerivAt {x0 : ℝ} (hx0 : 0 < x0) :
    HasDerivAt J (∫ g, -(g ^ 4 / (1 + x0 * g ^ 2) ^ 2) ∂(ProbabilityTheory.gaussianReal 0 1)) x0 := by
  have hfun : J = fun v => ∫ g, g ^ 2 / (1 + v * g ^ 2) ∂(ProbabilityTheory.gaussianReal 0 1) := rfl
  have hmain := (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := ProbabilityTheory.gaussianReal 0 1) (F := fun v g => g ^ 2 / (1 + v * g ^ 2))
    (F' := fun v g => -(g ^ 4 / (1 + v * g ^ 2) ^ 2)) (x₀ := x0) (bound := fun g => g ^ 4)
    (s := Ioi 0) (Ioi_mem_nhds hx0)
    (Filter.Eventually.of_forall fun v => (by fun_prop :
      Measurable fun g : ℝ => g ^ 2 / (1 + v * g ^ 2)).aestronglyMeasurable)
    (abs_J_integrable hx0.le)
    (by fun_prop : Measurable fun g : ℝ => -(g ^ 4 / (1 + x0 * g ^ 2) ^ 2)).aestronglyMeasurable
    (Filter.Eventually.of_forall fun g => fun x hx => abs_J_norm_le (Set.mem_Ioi.mp hx).le g)
    (Muon.Foundations.gaussian_integrable_pow 4)
    (Filter.Eventually.of_forall fun g => fun x hx =>
      abs_J_hasDerivAt_term g (Set.mem_Ioi.mp hx).le)).2
  rw [hfun]
  exact hmain

/-- The derivative `-E[g⁴/(1+xg²)²]` lies in `[-3, 0]` for `x ≥ 0`. -/
private lemma abs_J_deriv_bounds {x : ℝ} (hx : 0 ≤ x) :
    -3 ≤ ∫ g, -(g ^ 4 / (1 + x * g ^ 2) ^ 2) ∂(ProbabilityTheory.gaussianReal 0 1) ∧
      ∫ g, -(g ^ 4 / (1 + x * g ^ 2) ^ 2) ∂(ProbabilityTheory.gaussianReal 0 1) ≤ 0 := by
  have hI : Integrable (fun g : ℝ => g ^ 4 / (1 + x * g ^ 2) ^ 2) (ProbabilityTheory.gaussianReal 0 1) := by
    refine Integrable.mono' (Muon.Foundations.gaussian_integrable_pow 4) ?_ ?_
    · exact (by fun_prop : Measurable fun g : ℝ => g ^ 4 / (1 + x * g ^ 2) ^ 2).aestronglyMeasurable
    · refine Filter.Eventually.of_forall fun g => ?_
      show ‖g ^ 4 / (1 + x * g ^ 2) ^ 2‖ ≤ g ^ 4
      rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (by positivity) (sq_nonneg _))]
      exact abs_J_g4_div_le hx g
  have h3 : ∫ g, -(g ^ 4) ∂(ProbabilityTheory.gaussianReal 0 1) = -3 := by
    rw [integral_neg, Muon.Foundations.gaussian_moment_four]
  have hle : ∫ g, -(g ^ 4) ∂(ProbabilityTheory.gaussianReal 0 1) ≤
      ∫ g, -(g ^ 4 / (1 + x * g ^ 2) ^ 2) ∂(ProbabilityTheory.gaussianReal 0 1) :=
    integral_mono (Muon.Foundations.gaussian_integrable_pow 4).neg hI.neg
      (fun g => neg_le_neg (abs_J_g4_div_le hx g))
  constructor
  · linarith
  · refine integral_nonpos (fun g => ?_)
    exact neg_nonpos.mpr (div_nonneg (by positivity) (sq_nonneg _))

/-- Helper F15 of `sections/03-drift/CARD.md` §4 (source line 644; not a labelled environment):
`|J'(x)| ≤ 3` on `[0, ∞)` (cr-2026-10-23; stated as the two-sided bound for `x > 0` plus 3-Lipschitz on `[0, ∞)`, since `J` is not differentiable at `0` in Lean: `J y = 0` junk for `y < 0`), with `J(x) = 𝔼[g²/(1+xg²)]`, `g ~ N(0,1)` (`Muon.DetEquiv.J`).
The second clause of F15 (`|L_w(q)-L_w(q')| ≤ 3 s_3 |q-q'|`, source 976–977) concerns `Lw`
and is owned by B, not stated here. -/
theorem abs_deriv_J_le_three :
    (∀ x : ℝ, 0 < x → |deriv J x| ≤ 3) ∧ LipschitzOnWith 3 J (Set.Ici 0) := by
  have hderiv0 : HasDerivWithinAt J
      (∫ g, -(g ^ 4 / (1 + (0 : ℝ) * g ^ 2) ^ 2) ∂(ProbabilityTheory.gaussianReal 0 1)) (Set.Ici 0) 0 := by
    have h0 : ∫ g, -(g ^ 4 / (1 + (0 : ℝ) * g ^ 2) ^ 2) ∂(ProbabilityTheory.gaussianReal 0 1) = -3 := by
      simp only [zero_mul, add_zero, one_pow, div_one]
      rw [integral_neg, Muon.Foundations.gaussian_moment_four]
    rw [h0]
    exact (Muon.DetEquiv.lem_app_de_scalar_i).2.2.2.2.1
  have hderiv : ∀ x ∈ Set.Ici (0 : ℝ), HasDerivWithinAt J
      (∫ g, -(g ^ 4 / (1 + x * g ^ 2) ^ 2) ∂(ProbabilityTheory.gaussianReal 0 1)) (Set.Ici 0) x := by
    intro x hx
    rcases (Set.mem_Ici.mp hx).lt_or_eq with hpos | heq
    · exact (abs_J_hasDerivAt hpos).hasDerivWithinAt
    · subst heq
      exact hderiv0
  have hbound : ∀ x ∈ Set.Ici (0 : ℝ),
      ‖∫ g, -(g ^ 4 / (1 + x * g ^ 2) ^ 2) ∂(ProbabilityTheory.gaussianReal 0 1)‖₊ ≤ 3 := by
    intro x hx
    obtain ⟨h1, h2⟩ := abs_J_deriv_bounds (Set.mem_Ici.mp hx)
    have h : ‖∫ g, -(g ^ 4 / (1 + x * g ^ 2) ^ 2) ∂(ProbabilityTheory.gaussianReal 0 1)‖ ≤ 3 := by
      rw [Real.norm_eq_abs, abs_le]
      constructor <;> linarith
    exact_mod_cast h
  refine ⟨fun x hx => ?_, ?_⟩
  · rw [(abs_J_hasDerivAt hx).deriv, abs_le]
    obtain ⟨h1, h2⟩ := abs_J_deriv_bounds hx.le
    constructor <;> linarith
  · exact (convex_Ici (0 : ℝ)).lipschitzOnWith_of_nnnorm_hasDerivWithin_le hderiv hbound

/-- Helper F9 of `sections/03-drift/CARD.md` §4 (source lines 646–648; not a labelled
environment): a family of functions that is uniformly Lipschitz on `[0, Q]` and converges
pointwise there converges uniformly there. Used in the proof of `lem:app-drift-gaussian`. -/
theorem uniform_of_pointwise_lipschitz {Q L : ℝ} {f : ℕ → ℝ → ℝ} {g : ℝ → ℝ}
    (hL : ∀ n, ∀ x ∈ Icc (0 : ℝ) Q, ∀ y ∈ Icc (0 : ℝ) Q, |f n x - f n y| ≤ L * |x - y|)
    (hpt : ∀ x ∈ Icc (0 : ℝ) Q, Tendsto (fun n => f n x) atTop (𝓝 (g x))) :
    TendstoUniformlyOn f g atTop (Icc (0 : ℝ) Q) := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have hK0 : (|L| + 1) ≠ 0 := by positivity
  have hδpos : 0 < ε / (3 * (|L| + 1)) := by positivity
  have hKδ : (|L| + 1) * (ε / (3 * (|L| + 1))) = ε / 3 := by
    field_simp
  obtain ⟨t, htI, htfin, hcover⟩ :=
    finite_cover_balls_of_compact (isCompact_Icc : IsCompact (Icc (0 : ℝ) Q)) hδpos
  have hev : ∀ᶠ n in atTop, ∀ a ∈ t, |f n a - g a| < ε / 3 := by
    rw [Filter.eventually_all_finite htfin]
    intro a ha
    have h := (Metric.tendsto_nhds.mp (hpt a (htI ha))) (ε / 3) (by positivity)
    filter_upwards [h] with n hn
    rwa [Real.dist_eq] at hn
  filter_upwards [hev] with n hn x hx
  obtain ⟨a, hat, hxa⟩ := Set.mem_iUnion₂.mp (hcover hx)
  have hax : |x - a| < ε / (3 * (|L| + 1)) := by
    rw [← Real.dist_eq]
    exact Metric.mem_ball.mp hxa
  have hbd : ∀ m, |f m x - f m a| ≤ ε / 3 := fun m => by
    calc |f m x - f m a| ≤ L * |x - a| := hL m x hx a (htI hat)
      _ ≤ (|L| + 1) * |x - a| :=
          mul_le_mul_of_nonneg_right (by linarith [le_abs_self L]) (abs_nonneg _)
      _ ≤ (|L| + 1) * (ε / (3 * (|L| + 1))) :=
          mul_le_mul_of_nonneg_left hax.le (by positivity)
      _ = ε / 3 := hKδ
  have hga : |g a - g x| ≤ ε / 3 :=
    le_of_tendsto (((hpt a (htI hat)).sub (hpt x hx)).abs)
      (Filter.Eventually.of_forall fun m => by
        rw [abs_sub_comm]
        exact hbd m)
  rw [Real.dist_eq, abs_sub_comm]
  have key := abs_add_three (f n x - f n a) (f n a - g a) (g a - g x)
  rw [show (f n x - f n a) + (f n a - g a) + (g a - g x) = f n x - g x by ring] at key
  linarith [hbd n, hn a hat, hga]

end Muon.Drift
