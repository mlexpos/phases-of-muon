import Mathlib
import Muon.Phase.Arrays

/-!
# Appendix H: kernel estimates for the power-law phase map (task L-H.7)

Snapshot `cr-2026-10-23`. Source: `sections/07-phase-comparison/section.tex`, subsection
"Kernel estimates" (l.2217–2449): `lem:app-phase-mass`, `lem:app-phase-dilation`,
`lem:app-phase-svd-small`, `lem:app-phase-svd-main`, `lem:app-phase-log`,
`lem:app-phase-log-global`; with the definitions `eqn:app-phase-dilation` (`b`, `D`, `δ∘`)
and `eqn:app-phase-kernels` (the \SignSVD kernel). Card: `sections/07-phase-comparison/CARD.md`
§2, §3, §5 (L-H.7).

Encoding decisions:
* The paper's one-sided convolution `(g*h)(u)=∫_0^u g(v)h(u-v)dv` is
  `Muon.Foundations.oneSidedConv h g u` (substitute `v ↦ u-v`), as in `Muon.Phase.Volterra`.
* The \SignSVD kernel is `svdKernel α N = (2/H_N(α/2)) L_{N,α,α/2}`, the closed form of
  `eqn:app-phase-kernels` used by `prop_app_phase_prefactors_ii`. At `α = 2` the statements
  write `svdKernel 2 N`, `Hsum 1 N`, `Cpq (2+ς) 1`, `rq (2+ς) 1`, `Epq 2 1` for `α/2 = 1`
  (literal substitution; the arithmetic is identical).
* `Y_{s-SVD}(u) = Q(T_0 u)` is `fun u => QS (svdT0 N B * u)` for a solution `QS` of the Volterra
  equation of the matched \SignSVD model (`IsMatchedModel`), as in `prop_app_phase_prefactors_iii`.
  The first hit is `firstHit` (`ℝ≥0∞`, `inf ∅ = ∞`).
* `lem:app-phase-log-global` is split: `_i` (sandwich `f_{N,1} ≤ Y ≤ (h+w+√ε)²`), `_ii` (first
  hit and the bound on `ℰ = ∫_0^{û}(√Y-√f)`, `phaseErr`), and `_iii` (the closing "in particular").
  `_iii` is a sequence statement: it assumes the `ℰ` bound of `_ii` along the sequence (for all
  large `n`) and concludes `ℰ_n → 0`. It does not construct the models along the sequence.
* `N ≥ 1` is assumed in the `lem:app-phase-log` parts, where the paper's `H_N(1)` divides.
* `lem_app_phase_dilation` takes `IntegrableOn g (Ioi 0)` next to `∫_{(0,∞)} g ≤ 1`, because the
  paper's `∫_0^∞ g ≤ 1` is an improper integral. Continuity and nonnegativity are the paper's.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal
open Muon.Foundations

set_option linter.style.longLine false

noncomputable section

namespace Muon.Phase

/-! ## Definitions -/

/-- The \SignSVD kernel `g_{s-SVD}(u) = (2/H_N(α/2)) L_{N,α,α/2}(u)` (first entry of the
kernel display; reused from `prop_app_phase_prefactors_ii`).

`eqn:app-phase-kernels`, snapshot `cr-2026-10-23`. Source: `section.tex` l.1138–1141 (display).

LaTeX (verbatim, `section.tex` l.1138–1141):
```latex
\begin{equation}\label{eqn:app-phase-kernels}
g_{\text{s-SVD}}=\frac2{H_N(\alpha/2)}L_{N,\alpha,\alpha/2},\qquad
g_{\text{s-SGD}}=\frac{2(1-2/\pi)}N\,L_{N,\alpha,\alpha}+\frac4{\pi H_N(\alpha)}\,L_{N,2\alpha,\alpha} .
\end{equation}
``` -/
def svdKernel (α : ℝ) (N : ℕ) (u : ℝ) : ℝ := 2 / Hsum (α / 2) N * Lsum (N : ℕ∞) α (α / 2) u

/-- `δ∘ = 1 - (2/3)^{1/r_0}`. Part of the display `eqn:app-phase-dilation`.

`eqn:app-phase-dilation`, snapshot `cr-2026-10-23`. Source: `section.tex` l.2257–2263 (display).

LaTeX (verbatim, `section.tex` l.2257–2263):
```latex
\begin{equation}\label{eqn:app-phase-dilation}
\begin{gathered}
\delta_\circ\defeq1-(2/3)^{1/r_0},\qquad
b(r_0,\upsilon)\defeq\begin{cases}(1-r_0)^{-1},&r_0<1,\\ (e(\upsilon-1))^{-1},&r_0=1,\\ (r_0-1)^{-1},&r_0>1,\end{cases}\\
D(K,r_0,\upsilon)\defeq\max\Big\{1,\big[2K\delta_\circ^{-\upsilon}b(r_0,\upsilon)\big]^{1/(\upsilon-1)}\Big\} .
\end{gathered}
\end{equation}
``` -/
def dilDelta (r0 : ℝ) : ℝ := 1 - (2 / 3 : ℝ) ^ (1 / r0)

/-- `b(r_0, υ)` of `eqn:app-phase-dilation`. -/
def dilB (r0 υ : ℝ) : ℝ :=
  if r0 < 1 then (1 - r0)⁻¹ else if r0 = 1 then (Real.exp 1 * (υ - 1))⁻¹ else (r0 - 1)⁻¹

/-- `D(K, r_0, υ) = max{1, [2K δ∘^{-υ} b(r_0,υ)]^{1/(υ-1)}}` of `eqn:app-phase-dilation`. -/
def dilScale (K r0 υ : ℝ) : ℝ :=
  max 1 ((2 * K * dilDelta r0 ^ (-υ) * dilB r0 υ) ^ (1 / (υ - 1)))

/-- `r_0` of `lem:app-phase-svd-main`: `1` if `r_{s-SVD} = 1`, else `min{r_{s-SVD}, (1+2/α)/2}`,
where `r_{s-SVD} = r_q(α+ς)` at `q = α/2` (`rq`). -/
def svdMainR0 (α ς : ℝ) : ℝ :=
  if rq (α + ς) (α / 2) = 1 then 1 else min (rq (α + ς) (α / 2)) ((1 + 2 / α) / 2)

/-- The pair `(J_V, d_V)` of `lem:app-phase-svd-main`, with `υ∘ = 2 - 2/α`,
`K_V = 2 E_{α,α/2}` (`Epq`), `d_α = (α-1)(2-α)/(2α)`. -/
def svdMainJD (α ς : ℝ) : ℝ × ℝ :=
  let r0 := svdMainR0 α ς
  let uo := 2 - 2 / α
  let KV := 2 * Epq α (α / 2)
  let dAl := (α - 1) * (2 - α) / (2 * α)
  if r0 = 1 then (KV * dilDelta r0 ^ (-uo) / (Real.exp 1 * dAl), dAl / 2)
  else (KV * dilDelta r0 ^ (-uo) / (r0 - 1), 1 - α / 2 - (r0 - uo) / (2 * r0))

/-- `N_V = ⌈max{1, (2 J_V)^{1/d_V}}⌉` of `lem:app-phase-svd-main`. -/
def svdMainNV (α ς : ℝ) : ℕ :=
  ⌈max 1 ((2 * (svdMainJD α ς).1) ^ (1 / (svdMainJD α ς).2))⌉₊

/-- `δ_1 = [(1-r)/8]^{1/(1-α/2)}` of `lem:app-phase-svd-small`. -/
def svdSmallDelta1 (α r : ℝ) : ℝ := ((1 - r) / 8) ^ (1 / (1 - α / 2))

/-- `𝗰_1 = (1-r) δ_1^{α/2} / 8` of `lem:app-phase-svd-small`. -/
def svdSmallC1 (α r : ℝ) : ℝ := (1 - r) * svdSmallDelta1 α r ^ (α / 2) / 8

/-- `N_1 = ⌈max{4, 2^{1/(1-α/2)}, [8(1-α/2)/(1-r)]^{1/(1-α/2)}}⌉` of `lem:app-phase-svd-small`. -/
def svdSmallN1 (α r : ℝ) : ℕ :=
  ⌈max 4 (max ((2 : ℝ) ^ (1 / (1 - α / 2))) ((8 * (1 - α / 2) / (1 - r)) ^ (1 / (1 - α / 2))))⌉₊

/-- `A^{log}_r = 2^r (r + 1/(1-r)) + 16/(1-r)` of `lem:app-phase-log`. -/
def logAr (r : ℝ) : ℝ := (2 : ℝ) ^ r * (r + 1 / (1 - r)) + 16 / (1 - r)

/-- `𝖠_0 = C K/(r-1) (2^r/e + 2)` of `lem:app-phase-log-global`, with `p = 2+ς`,
`C = C_{p,1}` (`Cpq`), `K = 2 E_{2,1}` (`Epq`), `r = r_{s-SVD} = r_1(p)` (`rq`). -/
def logGlobalA0 (ς : ℝ) : ℝ :=
  Cpq (2 + ς) 1 * (2 * Epq 2 1) / (rq (2 + ς) 1 - 1) * ((2 : ℝ) ^ rq (2 + ς) 1 / Real.exp 1 + 2)

/-- `L_0 = max{1, 4K/(2-√2)}` of `lem:app-phase-log-global`, `K = 2 E_{2,1}`. -/
def logGlobalL0 : ℝ := max 1 (4 * (2 * Epq 2 1) / (2 - Real.sqrt 2))

/-- `h(u) = C (1+u)^{-r}` of `lem:app-phase-log-global` (`C = C_{2+ς,1}`, `r = r_1(2+ς)`). -/
def logGlobalH (ς u : ℝ) : ℝ := Cpq (2 + ς) 1 * (1 + u) ^ (-rq (2 + ς) 1)

/-- `𝗐(u) = √𝖠_0 ε^{1/4} L_N^{-1/2} (1+u)^{-1/2}` of `lem:app-phase-log-global`, `L_N = H_N(1)`. -/
def logGlobalW (ς : ℝ) (N : ℕ) (ε u : ℝ) : ℝ :=
  Real.sqrt (logGlobalA0 ς) * ε ^ (1 / 4 : ℝ) * Hsum 1 N ^ (-(1 / 2 : ℝ)) *
    (1 + u) ^ (-(1 / 2 : ℝ))

/-- The right-hand side of the bound on `ℰ` in `lem:app-phase-log-global`, as a function of
`(N, ς, ε)`: `ε^{1/8}√(C+√𝖠_0+1) + C/(r-1)(1+ε^{-1/8})^{1-r} + 2√𝖠_0 (2C)^{1/(2r)} L_N^{-1/2}
ε^{(r-1)/(4r)} + (2C)^{1/r} ε^{(r-1)/(2r)} + 8𝖠_0/L_N`. -/
def logGlobalErrBound (N : ℕ) (ς ε : ℝ) : ℝ :=
  let C := Cpq (2 + ς) 1
  let r := rq (2 + ς) 1
  let A0 := logGlobalA0 ς
  let L := Hsum 1 N
  ε ^ (1 / 8 : ℝ) * Real.sqrt (C + Real.sqrt A0 + 1)
    + C / (r - 1) * (1 + ε ^ (-(1 / 8 : ℝ))) ^ (1 - r)
    + 2 * Real.sqrt A0 * (2 * C) ^ (1 / (2 * r)) * L ^ (-(1 / 2 : ℝ)) * ε ^ ((r - 1) / (4 * r))
    + (2 * C) ^ (1 / r) * ε ^ ((r - 1) / (2 * r)) + 8 * A0 / L

/-- The error `ℰ = ∫_0^{û} (√Y - √f)` of `lem:app-phase-log-global` (`eqn` l.2013 form), for a
dimensionless risk `Y`, forcing `f` and the upper limit `û` (real). -/
def phaseErr (Y f : ℝ → ℝ) (uh : ℝ) : ℝ :=
  ∫ u in (0 : ℝ)..uh, (Real.sqrt (Y u) - Real.sqrt (f u))

/-! ## Local mass and dilated envelope -/

theorem mass_cheb (u : ℝ) (hu : 0 ≤ u) (g φ : ℝ → ℝ)
    (hg : ContinuousOn g (Icc 0 u)) (hφ : ContinuousOn φ (Icc 0 u))
    (hgm : AntitoneOn g (Icc 0 u)) (hφm : MonotoneOn φ (Icc 0 u)) :
    u * (∫ s in (0:ℝ)..u, g s * φ s) ≤ (∫ s in (0:ℝ)..u, g s) * (∫ s in (0:ℝ)..u, φ s) := by
  have hgi : IntervalIntegrable g volume 0 u := ContinuousOn.intervalIntegrable_of_Icc hu hg
  have hφi : IntervalIntegrable φ volume 0 u := ContinuousOn.intervalIntegrable_of_Icc hu hφ
  have hgφ : IntervalIntegrable (fun s => g s * φ s) volume 0 u :=
    ContinuousOn.intervalIntegrable_of_Icc hu (hg.mul hφ)
  -- pointwise sign
  have hpt : ∀ s ∈ Icc (0:ℝ) u, ∀ t ∈ Icc (0:ℝ) u, (g s - g t) * (φ s - φ t) ≤ 0 := by
    intro s hs t ht
    rcases le_total s t with h | h
    · have h1 : g t ≤ g s := hgm hs ht h
      have h2 : φ s ≤ φ t := hφm hs ht h
      nlinarith
    · have h1 : g s ≤ g t := hgm ht hs h
      have h2 : φ t ≤ φ s := hφm ht hs h
      nlinarith
  -- inner integral in t, for fixed s, expanded
  have hexp : ∀ s ∈ Icc (0:ℝ) u,
      ∫ t in (0:ℝ)..u, (g s - g t) * (φ s - φ t)
        = u * (g s * φ s) - g s * (∫ t in (0:ℝ)..u, φ t) - φ s * (∫ t in (0:ℝ)..u, g t)
          + ∫ t in (0:ℝ)..u, g t * φ t := by
    intro s _
    have e : ∀ t, (g s - g t) * (φ s - φ t)
        = (g s * φ s - g s * φ t - φ s * g t) + g t * φ t := by intro t; ring
    have i1 : IntervalIntegrable (fun _ : ℝ => g s * φ s) volume 0 u := intervalIntegrable_const
    have i2 : IntervalIntegrable (fun t => g s * φ t) volume 0 u := hφi.const_mul (g s)
    have i3 : IntervalIntegrable (fun t => φ s * g t) volume 0 u := hgi.const_mul (φ s)
    simp_rw [e]
    rw [intervalIntegral.integral_add ((i1.sub i2).sub i3) hgφ,
      intervalIntegral.integral_sub (i1.sub i2) i3, intervalIntegral.integral_sub i1 i2,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul]
    simp only [intervalIntegral.integral_const, smul_eq_mul, sub_zero]
    ring
  set P := ∫ t in (0:ℝ)..u, g t * φ t with hP
  set Φ := ∫ t in (0:ℝ)..u, φ t with hΦ
  set m := ∫ t in (0:ℝ)..u, g t with hm
  have hinner : ∀ s ∈ Icc (0:ℝ) u,
      u * (g s * φ s) - g s * Φ - φ s * m + P ≤ 0 := by
    intro s hs
    have hfi : IntervalIntegrable (fun t => (g s - g t) * (φ s - φ t)) volume 0 u :=
      (((continuousOn_const.sub hg).mul (continuousOn_const.sub hφ))).intervalIntegrable_of_Icc hu
    have := intervalIntegral.integral_mono_on hu hfi intervalIntegrable_const
      (fun t ht => hpt s hs t ht)
    rw [intervalIntegral.integral_zero, hexp s hs] at this
    exact this
  have hEi : IntervalIntegrable (fun s => u * (g s * φ s) - g s * Φ - φ s * m + P) volume 0 u := by
    have i1 : IntervalIntegrable (fun s => u * (g s * φ s)) volume 0 u := hgφ.const_mul u
    have i2 : IntervalIntegrable (fun s => g s * Φ) volume 0 u := hgi.mul_const Φ
    have i3 : IntervalIntegrable (fun s => φ s * m) volume 0 u := hφi.mul_const m
    exact ((i1.sub i2).sub i3).add intervalIntegrable_const
  have hout : ∫ s in (0:ℝ)..u, (u * (g s * φ s) - g s * Φ - φ s * m + P) ≤ 0 := by
    have := intervalIntegral.integral_mono_on hu hEi intervalIntegrable_const
      (fun s hs => hinner s hs)
    simpa using this
  have hlin : ∫ s in (0:ℝ)..u, (u * (g s * φ s) - g s * Φ - φ s * m + P)
      = 2 * (u * P - m * Φ) := by
    rw [intervalIntegral.integral_add ((hgφ.const_mul u |>.sub (hgi.mul_const Φ)).sub (hφi.mul_const m)) intervalIntegrable_const,
      intervalIntegral.integral_sub ((hgφ.const_mul u).sub (hgi.mul_const Φ)) (hφi.mul_const m),
      intervalIntegral.integral_sub (hgφ.const_mul u) (hgi.mul_const Φ),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_mul_const,
      intervalIntegral.integral_mul_const]
    simp only [intervalIntegral.integral_const, smul_eq_mul, sub_zero, ← hP, ← hΦ, ← hm]
    ring
  linarith

theorem mass_int_bound (C D r u : ℝ) (hC : 0 < C) (hD : 0 < D) (hr0 : 0 < r)
    (hr1 : r < 1) (hu : 0 ≤ u) :
    ∫ s in (0:ℝ)..u, C * (1 + (u - s) / D) ^ (-r) ≤ u * (C * (1 + u / D) ^ (-r)) / (1 - r) := by
  have hsub : ∫ s in (0:ℝ)..u, C * (1 + (u - s) / D) ^ (-r)
      = ∫ w in (0:ℝ)..u, C * (1 + w / D) ^ (-r) := by
    have := intervalIntegral.integral_comp_sub_left (fun w => C * (1 + w / D) ^ (-r)) u
      (a := 0) (b := u)
    simpa only [sub_self, sub_zero] using this
  have hcont : ContinuousOn (fun w => C * (1 + w / D) ^ (-r)) (Icc 0 u) := by
    apply ContinuousOn.mul continuousOn_const
    apply ContinuousOn.rpow_const (by fun_prop)
    intro w hw
    left
    have h0 : 0 ≤ w / D := div_nonneg hw.1 hD.le
    have : 0 < 1 + w / D := by linarith
    exact this.ne'
  have hint : IntervalIntegrable (fun w => C * (1 + w / D) ^ (-r)) volume 0 u :=
    ContinuousOn.intervalIntegrable_of_Icc hu hcont
  have hderiv : ∀ w ∈ uIcc (0:ℝ) u,
      HasDerivAt (fun w => C * D / (1 - r) * (1 + w / D) ^ (1 - r)) (C * (1 + w / D) ^ (-r)) w := by
    intro w hw
    rw [uIcc_of_le hu] at hw
    have h0 : 0 ≤ w / D := div_nonneg hw.1 hD.le
    have hpos : 0 < 1 + w / D := by linarith
    have h1 : HasDerivAt (fun w => 1 + w / D) (1 / D) w := by
      have := ((hasDerivAt_id w).div_const D).const_add 1
      simpa using this
    have h2 := (h1.rpow_const (p := 1 - r) (Or.inl hpos.ne')).const_mul (C * D / (1 - r))
    convert h2 using 1
    rw [show 1 - r - 1 = -r by ring]
    have hr' : (1 - r) ≠ 0 := by linarith
    have hD' : D ≠ 0 := hD.ne'
    generalize (1 + w / D) ^ (-r) = X
    field_simp
  rw [hsub, intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  simp only [zero_div, add_zero, Real.one_rpow, mul_one]
  obtain ⟨y, hy_def⟩ : ∃ y, y = 1 + u / D := ⟨_, rfl⟩
  rw [← hy_def]
  have hy : 1 ≤ y := by
    have := div_nonneg hu hD.le
    linarith
  have hp : 1 ≤ y ^ r := Real.one_le_rpow hy hr0.le
  have e1 : y ^ (1 - r) = y / y ^ r := by
    rw [Real.rpow_sub (by linarith : (0:ℝ) < y), Real.rpow_one]
  have e2 : y ^ (-r) = 1 / y ^ r := by
    rw [Real.rpow_neg (by linarith : (0:ℝ) ≤ y), one_div]
  have hu' : u = D * (y - 1) := by
    rw [hy_def]
    field_simp
    ring
  rw [e1, e2]
  have key : u * (C * (1 / y ^ r)) / (1 - r) - (C * D / (1 - r) * (y / y ^ r) - C * D / (1 - r) * 1)
      = C * D * (y ^ r - 1) / (y ^ r * (1 - r)) := by
    rw [hu']
    have : (y ^ r) ≠ 0 := by positivity
    have : (1 - r) ≠ 0 := by linarith
    field_simp
    ring
  have hnn : 0 ≤ C * D * (y ^ r - 1) / (y ^ r * (1 - r)) := by
    apply div_nonneg
    · exact mul_nonneg (mul_nonneg hC.le hD.le) (by linarith)
    · exact mul_nonneg (by linarith) (by linarith)
  linarith

/-- `lem:app-phase-mass`, snapshot `cr-2026-10-23`. Source: `section.tex` l.2230–2237 (environment).

LaTeX (verbatim, `section.tex` l.2230–2237):
```latex
\begin{lemma}[Local mass]\label{lem:app-phase-mass}
Let $g\ge0$ be continuous and nonincreasing on $[0,\infty)$, and put
$m_g(u)\defeq\int_0^ug(v)\,\dif v$. Let $C,D>0$, $0<r<1$ and
$h(u)\defeq C(1+u/D)^{-r}$. Then
\[
(g*h)(u)\le\frac{m_g(u)}{1-r}\,h(u)\qquad(u\ge0).
\]
\end{lemma}
``` -/
theorem lem_app_phase_mass (g : ℝ → ℝ) (hgc : ContinuousOn g (Ici 0))
    (hgnn : ∀ v ∈ Ici (0 : ℝ), 0 ≤ g v) (hgm : AntitoneOn g (Ici 0))
    (C D r : ℝ) (hC : 0 < C) (hD : 0 < D) (hr0 : 0 < r) (hr1 : r < 1) :
    ∀ u : ℝ, 0 ≤ u →
      oneSidedConv (fun w => C * (1 + w / D) ^ (-r)) g u
        ≤ (∫ v in (0 : ℝ)..u, g v) / (1 - r) * (C * (1 + u / D) ^ (-r)) := by
  intro u hu
  rcases hu.eq_or_lt with h0 | hpos
  · subst h0
    simp [oneSidedConv]
  have hUI : Icc (0:ℝ) u ⊆ Ici 0 := fun v hv => hv.1
  have hgI : ContinuousOn g (Icc 0 u) := hgc.mono hUI
  have hgmI : AntitoneOn g (Icc 0 u) := hgm.mono hUI
  have hgnnI : 0 ≤ ∫ v in (0:ℝ)..u, g v :=
    intervalIntegral.integral_nonneg hu (fun v hv => hgnn v hv.1)
  have hφc : ContinuousOn (fun s => C * (1 + (u - s) / D) ^ (-r)) (Icc 0 u) := by
    apply ContinuousOn.mul continuousOn_const
    apply ContinuousOn.rpow_const (by fun_prop)
    intro s hs
    left
    have h0 : 0 ≤ (u - s) / D := div_nonneg (by linarith [hs.2]) hD.le
    have : 0 < 1 + (u - s) / D := by linarith
    exact this.ne'
  have hφm : MonotoneOn (fun s => C * (1 + (u - s) / D) ^ (-r)) (Icc 0 u) := by
    intro a ha b hb hab
    have hdiv : (u - b) / D ≤ (u - a) / D := div_le_div_of_nonneg_right (by linarith) hD.le
    have hx : 0 < 1 + (u - b) / D := by
      have : 0 ≤ (u - b) / D := div_nonneg (by linarith [hb.2]) hD.le
      linarith
    have hpow : (1 + (u - a) / D) ^ (-r) ≤ (1 + (u - b) / D) ^ (-r) :=
      Real.rpow_le_rpow_of_nonpos hx (by linarith) (by linarith)
    exact mul_le_mul_of_nonneg_left hpow hC.le
  have hcheb := mass_cheb u hu g (fun s => C * (1 + (u - s) / D) ^ (-r)) hgI hφc hgmI hφm
  beta_reduce at hcheb
  have hΦ := mass_int_bound C D r u hC hD hr0 hr1 hu
  have hconv : oneSidedConv (fun w => C * (1 + w / D) ^ (-r)) g u
      = ∫ s in (0:ℝ)..u, g s * (C * (1 + (u - s) / D) ^ (-r)) := by
    unfold oneSidedConv
    congr 1
    funext s
    ring
  rw [hconv]
  have h1 : u * (∫ s in (0:ℝ)..u, g s * (C * (1 + (u - s) / D) ^ (-r)))
      ≤ u * ((∫ v in (0 : ℝ)..u, g v) / (1 - r) * (C * (1 + u / D) ^ (-r))) := by
    calc u * (∫ s in (0:ℝ)..u, g s * (C * (1 + (u - s) / D) ^ (-r)))
        ≤ (∫ v in (0:ℝ)..u, g v) * (∫ s in (0:ℝ)..u, C * (1 + (u - s) / D) ^ (-r)) := hcheb
      _ ≤ (∫ v in (0:ℝ)..u, g v) * (u * (C * (1 + u / D) ^ (-r)) / (1 - r)) :=
          mul_le_mul_of_nonneg_left hΦ hgnnI
      _ = u * ((∫ v in (0 : ℝ)..u, g v) / (1 - r) * (C * (1 + u / D) ^ (-r))) := by ring
  exact le_of_mul_le_mul_left h1 hpos

theorem dil_delta_facts (r0 : ℝ) (hr0 : 0 < r0) :
    0 < dilDelta r0 ∧ dilDelta r0 < 1 ∧ (1 - dilDelta r0) ^ r0 = 2 / 3 := by
  have hpos : (0:ℝ) < (2 / 3 : ℝ) ^ (1 / r0) := Real.rpow_pos_of_pos (by norm_num) _
  have hlt : (2 / 3 : ℝ) ^ (1 / r0) < 1 :=
    Real.rpow_lt_one (by norm_num) (by norm_num) (by positivity)
  refine ⟨by unfold dilDelta; linarith, by unfold dilDelta; linarith, ?_⟩
  unfold dilDelta
  rw [show 1 - (1 - (2 / 3 : ℝ) ^ (1 / r0)) = (2 / 3 : ℝ) ^ (1 / r0) by ring,
    ← Real.rpow_mul (by norm_num), one_div_mul_cancel hr0.ne', Real.rpow_one]

/-- early-part ratio: for `0 ≤ s ≤ δ a`, `(a-s)^{-r0} a^{r0} ≤ 3/2`. -/
theorem dil_early_ratio (a δ r0 s : ℝ) (ha : 0 < a) (hr0 : 0 < r0)
    (hδ : 0 < δ) (hδ1 : δ < 1) (hδr : (1 - δ) ^ r0 = 2 / 3)
    (hs0 : 0 ≤ s) (hs : s ≤ δ * a) :
    (a - s) ^ (-r0) * a ^ r0 ≤ 3 / 2 := by
  have h1a : 0 < (1 - δ) * a := mul_pos (by linarith) ha
  have hle : (1 - δ) * a ≤ a - s := by nlinarith
  have hpow : (a - s) ^ (-r0) ≤ ((1 - δ) * a) ^ (-r0) :=
    Real.rpow_le_rpow_of_nonpos h1a hle (by linarith)
  have hmul : ((1 - δ) * a) ^ (-r0) = (1 - δ) ^ (-r0) * a ^ (-r0) :=
    Real.mul_rpow (by linarith) ha.le
  have harp : a ^ r0 * a ^ (-r0) = 1 := by
    rw [Real.rpow_neg ha.le]; field_simp
  have hinv : (1 - δ) ^ (-r0) = 3 / 2 := by
    rw [Real.rpow_neg (by linarith), hδr]; norm_num
  have hpos : 0 ≤ a ^ r0 := Real.rpow_nonneg ha.le _
  calc (a - s) ^ (-r0) * a ^ r0 ≤ ((1 - δ) * a) ^ (-r0) * a ^ r0 :=
        mul_le_mul_of_nonneg_right hpow hpos
    _ = (1 - δ) ^ (-r0) * (a ^ (-r0) * a ^ r0) := by rw [hmul]; ring
    _ = 3 / 2 := by rw [mul_comm (a ^ (-r0)), harp, hinv, mul_one]

/-- `log x ≤ x^c / (e c)` type bound: `x^{-c} log x ≤ 1/(e c)`. -/
theorem dil_log_sup (x c : ℝ) (hx : 0 < x) (hc : 0 < c) :
    x ^ (-c) * Real.log x ≤ 1 / (Real.exp 1 * c) := by
  have hl : ∀ y : ℝ, 0 < y → Real.log y ≤ y / Real.exp 1 := by
    intro y hy
    have := Real.log_le_sub_one_of_pos (div_pos hy (Real.exp_pos 1))
    rw [Real.log_div hy.ne' (Real.exp_pos 1).ne', Real.log_exp] at this
    linarith
  have h2 : c * Real.log x ≤ x ^ c / Real.exp 1 := by
    rw [← Real.log_rpow hx]; exact hl _ (Real.rpow_pos_of_pos hx c)
  have h3 : Real.exp 1 * (c * Real.log x) ≤ x ^ c := by
    have := mul_le_mul_of_nonneg_left h2 (Real.exp_pos 1).le
    rwa [mul_div_cancel₀ _ (Real.exp_pos 1).ne'] at this
  have h4 : Real.log x ≤ x ^ c / (Real.exp 1 * c) := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith
  have h5 : x ^ (-c) * (x ^ c / (Real.exp 1 * c)) = 1 / (Real.exp 1 * c) := by
    rw [Real.rpow_neg hx.le]
    field_simp
  calc x ^ (-c) * Real.log x ≤ x ^ (-c) * (x ^ c / (Real.exp 1 * c)) :=
        mul_le_mul_of_nonneg_left h4 (Real.rpow_nonneg hx.le _)
    _ = 1 / (Real.exp 1 * c) := h5


theorem dil_J_lt (D M r0 : ℝ) (hD : 0 < D) (hDM : D ≤ M) (hr1 : r0 < 1) :
    ∫ t in D..M, t ^ (-r0) ≤ M ^ (1 - r0) / (1 - r0) := by
  have hr0 : 0 < 1 - r0 := by linarith
  rw [integral_rpow (Or.inl (by linarith)), show -r0 + 1 = 1 - r0 by ring]
  apply div_le_div_of_nonneg_right _ hr0.le
  linarith [Real.rpow_nonneg hD.le (1 - r0)]

theorem dil_J_gt (D M r0 : ℝ) (hD : 0 < D) (hDM : D ≤ M) (hr1 : 1 < r0) :
    ∫ t in D..M, t ^ (-r0) ≤ D ^ (1 - r0) / (r0 - 1) := by
  have hn : (1 - r0) ≠ 0 := by intro h; linarith
  have hp : (r0 - 1) ≠ 0 := by intro h; linarith
  rw [integral_rpow (Or.inr ⟨by intro h; linarith, fun h => by
      rw [uIcc_of_le hDM] at h; linarith [h.1]⟩), show -r0 + 1 = 1 - r0 by ring]
  have e : (M ^ (1 - r0) - D ^ (1 - r0)) / (1 - r0)
      = (D ^ (1 - r0) - M ^ (1 - r0)) / (r0 - 1) := by
    rw [div_eq_div_iff hn hp]; ring
  rw [e]
  apply div_le_div_of_nonneg_right _ (by linarith)
  linarith [Real.rpow_nonneg (le_trans hD.le hDM) (1 - r0)]

theorem dil_J_one (D M a : ℝ) (hD : 0 < D) (hDM : D ≤ M) (hMa : M ≤ a) :
    ∫ t in D..M, t ^ (-(1:ℝ)) ≤ Real.log (a / D) := by
  have hMpos : 0 < M := lt_of_lt_of_le hD hDM
  simp only [Real.rpow_neg_one]
  rw [integral_inv_of_pos hD hMpos]
  exact Real.log_le_log (div_pos hMpos hD) (div_le_div_of_nonneg_right hMa hD.le)

theorem dil_sub (a u δ r0 : ℝ) :
    ∫ s in δ * a..u, (a - s) ^ (-r0) = ∫ t in (a - u)..(a - δ * a), t ^ (-r0) :=
  intervalIntegral.integral_comp_sub_left (fun t : ℝ => t ^ (-r0)) a


theorem dil_ratio_id (u D s r0 : ℝ) (hD : 0 < D) (hu : 0 ≤ u) (hs : s ≤ u) :
    (1 + (u - s) / D) ^ (-r0) = (1 + u / D) ^ (-r0) * ((D + u - s) ^ (-r0) * (D + u) ^ r0) := by
  have h1 : 1 + (u - s) / D = (D + u - s) / D := by field_simp; ring
  have h2 : 1 + u / D = (D + u) / D := by field_simp
  have hp1 : 0 ≤ D + u - s := by linarith
  have hp2 : 0 ≤ D + u := by linarith
  have harp : (D + u) ^ (-r0) * (D + u) ^ r0 = 1 := by
    rw [Real.rpow_neg (by linarith)]; field_simp
  rw [h1, h2, Real.div_rpow hp1 hD.le, Real.div_rpow hp2 hD.le]
  rw [show (D + u) ^ (-r0) / D ^ (-r0) * ((D + u - s) ^ (-r0) * (D + u) ^ r0)
      = ((D + u) ^ (-r0) * (D + u) ^ r0) * (D + u - s) ^ (-r0) / D ^ (-r0) by ring, harp, one_mul]

theorem dil_int_le_one (g : ℝ → ℝ) (u : ℝ) (hu : 0 ≤ u)
    (hgnn : ∀ v ∈ Ici (0 : ℝ), 0 ≤ g v) (hgi : IntegrableOn g (Ioi 0))
    (hgint : ∫ v in Ioi (0 : ℝ), g v ≤ 1) : ∫ v in (0 : ℝ)..u, g v ≤ 1 := by
  rw [intervalIntegral.integral_of_le hu]
  refine le_trans ?_ hgint
  apply setIntegral_mono_set hgi
  · exact (ae_restrict_iff' measurableSet_Ioi).mpr
      (Filter.Eventually.of_forall fun v hv => hgnn v (Set.mem_Ici.mpr (Set.mem_Ioi.mp hv).le))
  · exact Filter.Eventually.of_forall (fun x (hx : x ∈ Ioc (0:ℝ) u) => (hx.1 : x ∈ Ioi 0))

theorem dil_late_final (D a M υ r0 Kp : ℝ) (hD : 0 < D) (hDa : D ≤ a) (hMa : M ≤ a)
    (hDM : D ≤ M) (hυ : 1 < υ) (hr0 : 0 < r0) (hr0υ : r0 ≤ υ) (hKp : 0 ≤ Kp) :
    Kp * (a ^ (-υ) * a ^ r0) * (∫ t in D..M, t ^ (-r0)) ≤ Kp * D ^ (1 - υ) * dilB r0 υ := by
  have ha : 0 < a := lt_of_lt_of_le hD hDa
  have hCst : 0 ≤ a ^ (-υ) * a ^ r0 := mul_nonneg (Real.rpow_nonneg ha.le _) (Real.rpow_nonneg ha.le _)
  rcases lt_trichotomy r0 1 with hr | hr | hr
  · have hJ := dil_J_lt D M r0 hD hDM hr
    have hb : dilB r0 υ = (1 - r0)⁻¹ := by unfold dilB; simp [hr]
    rw [hb]
    have hr' : 0 < 1 - r0 := by linarith
    have h1 : a ^ (-υ) * a ^ r0 * M ^ (1 - r0) ≤ a ^ (1 - υ) := by
      have e1 : a ^ (1 - υ) = a ^ (-υ) * a := by
        rw [show (1 - υ) = -υ + 1 by ring, Real.rpow_add ha, Real.rpow_one]
      have e2 : a ^ r0 * a ^ (1 - r0) = a := by
        rw [← Real.rpow_add ha, add_sub_cancel, Real.rpow_one]
      have hm : M ^ (1 - r0) ≤ a ^ (1 - r0) :=
        Real.rpow_le_rpow (le_trans hD.le hDM) hMa hr'.le
      calc a ^ (-υ) * a ^ r0 * M ^ (1 - r0) ≤ a ^ (-υ) * a ^ r0 * a ^ (1 - r0) :=
            mul_le_mul_of_nonneg_left hm hCst
        _ = a ^ (-υ) * (a ^ r0 * a ^ (1 - r0)) := by ring
        _ = a ^ (1 - υ) := by rw [e2, e1]
    have h2 : a ^ (1 - υ) ≤ D ^ (1 - υ) :=
      Real.rpow_le_rpow_of_nonpos hD hDa (by linarith)
    have hK' : 0 ≤ Kp / (1 - r0) := div_nonneg hKp hr'.le
    calc Kp * (a ^ (-υ) * a ^ r0) * (∫ t in D..M, t ^ (-r0))
        ≤ Kp * (a ^ (-υ) * a ^ r0) * (M ^ (1 - r0) / (1 - r0)) :=
          mul_le_mul_of_nonneg_left hJ (mul_nonneg hKp hCst)
      _ = (Kp / (1 - r0)) * (a ^ (-υ) * a ^ r0 * M ^ (1 - r0)) := by ring
      _ ≤ (Kp / (1 - r0)) * a ^ (1 - υ) := mul_le_mul_of_nonneg_left h1 hK'
      _ ≤ (Kp / (1 - r0)) * D ^ (1 - υ) := mul_le_mul_of_nonneg_left h2 hK'
      _ = Kp * D ^ (1 - υ) * (1 - r0)⁻¹ := by ring
  · subst hr
    have hMa' : M ≤ a := hMa
    have hJ := dil_J_one D M a hD hDM hMa'
    have hb : dilB 1 υ = (Real.exp 1 * (υ - 1))⁻¹ := by unfold dilB; simp
    rw [hb]
    have hx : 0 < a / D := div_pos ha hD
    have hc : 0 < υ - 1 := by linarith
    have e3 : a ^ (-υ) * a = D ^ (1 - υ) * (a / D) ^ (-(υ - 1)) := by
      calc a ^ (-υ) * a = a ^ (1 - υ) := by
            rw [show (1 - υ) = -υ + 1 by ring, Real.rpow_add ha, Real.rpow_one]
        _ = (D * (a / D)) ^ (1 - υ) := by congr 1; field_simp
        _ = D ^ (1 - υ) * (a / D) ^ (1 - υ) := Real.mul_rpow hD.le hx.le
        _ = D ^ (1 - υ) * (a / D) ^ (-(υ - 1)) := by rw [show -(υ - 1) = 1 - υ by ring]
    have hls := dil_log_sup (a / D) (υ - 1) hx hc
    rw [Real.rpow_one]
    calc Kp * (a ^ (-υ) * a) * (∫ t in D..M, t ^ (-(1:ℝ)))
        ≤ Kp * (a ^ (-υ) * a) * Real.log (a / D) :=
          mul_le_mul_of_nonneg_left hJ (mul_nonneg hKp (mul_nonneg (Real.rpow_nonneg ha.le _) ha.le))
      _ = Kp * D ^ (1 - υ) * ((a / D) ^ (-(υ - 1)) * Real.log (a / D)) := by rw [e3]; ring
      _ ≤ Kp * D ^ (1 - υ) * (1 / (Real.exp 1 * (υ - 1))) :=
          mul_le_mul_of_nonneg_left hls (mul_nonneg hKp (Real.rpow_nonneg hD.le _))
      _ = Kp * D ^ (1 - υ) * (Real.exp 1 * (υ - 1))⁻¹ := by ring
  · have hJ := dil_J_gt D M r0 hD hDM hr
    have hb : dilB r0 υ = (r0 - 1)⁻¹ := by
      unfold dilB
      rw [ite_eq_right_iff.mpr (fun h => absurd h (by linarith)), if_neg (by linarith)]
    rw [hb]
    have hp : 0 < r0 - 1 := by linarith
    have h1 : a ^ (-υ) * a ^ r0 ≤ D ^ (-υ + r0) := by
      rw [← Real.rpow_add ha]
      exact Real.rpow_le_rpow_of_nonpos hD hDa (by linarith)
    have h2 : D ^ (-υ + r0) * D ^ (1 - r0) = D ^ (1 - υ) := by
      rw [← Real.rpow_add hD]; congr 1; ring
    have hpos : 0 ≤ Kp * (a ^ (-υ) * a ^ r0) := mul_nonneg hKp hCst
    calc Kp * (a ^ (-υ) * a ^ r0) * (∫ t in D..M, t ^ (-r0))
        ≤ Kp * (a ^ (-υ) * a ^ r0) * (D ^ (1 - r0) / (r0 - 1)) := mul_le_mul_of_nonneg_left hJ hpos
      _ ≤ Kp * D ^ (-υ + r0) * (D ^ (1 - r0) / (r0 - 1)) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 hKp)
            (div_nonneg (Real.rpow_nonneg hD.le _) hp.le)
      _ = Kp * (D ^ (-υ + r0) * D ^ (1 - r0)) * (r0 - 1)⁻¹ := by ring
      _ = Kp * D ^ (1 - υ) * (r0 - 1)⁻¹ := by rw [h2]

theorem dil_final_half (K υ r0 : ℝ) (hK : 0 < K) (hυ : 1 < υ) (hb : 0 < dilB r0 υ)
    (hδ : 0 < dilDelta r0) :
    K * dilDelta r0 ^ (-υ) * dilScale K r0 υ ^ (1 - υ) * dilB r0 υ ≤ 1 / 2 := by
  set X := 2 * K * dilDelta r0 ^ (-υ) * dilB r0 υ with hXdef
  have hX : 0 < X := by
    rw [hXdef]; have := Real.rpow_pos_of_pos hδ (-υ); positivity
  have hc : 0 < υ - 1 := by linarith
  set Y := X ^ (1 / (υ - 1)) with hYdef
  have hY : 0 < Y := Real.rpow_pos_of_pos hX _
  have hD1 : Y ≤ dilScale K r0 υ := le_max_right _ _
  have hDpos : 0 < dilScale K r0 υ := lt_of_lt_of_le hY hD1
  set Z := dilScale K r0 υ ^ (υ - 1) with hZdef
  have hZX : X ≤ Z := by
    have h1 : Y ^ (υ - 1) = X := by
      rw [hYdef, ← Real.rpow_mul hX.le, one_div_mul_cancel hc.ne', Real.rpow_one]
    rw [← h1]
    exact Real.rpow_le_rpow hY.le hD1 hc.le
  have hZpos : 0 < Z := lt_of_lt_of_le hX hZX
  have hneg : dilScale K r0 υ ^ (1 - υ) = Z⁻¹ := by
    rw [hZdef, ← Real.rpow_neg hDpos.le]; congr 1; ring
  rw [hneg]
  have hW : K * dilDelta r0 ^ (-υ) * dilB r0 υ * 2 = X := by rw [hXdef]; ring
  have key : K * dilDelta r0 ^ (-υ) * Z⁻¹ * dilB r0 υ
      = (K * dilDelta r0 ^ (-υ) * dilB r0 υ) * Z⁻¹ := by ring
  rw [key, ← div_eq_mul_inv, div_le_iff₀ hZpos]
  linarith


theorem dil_B_pos (r0 υ : ℝ) (hr0 : 0 < r0) (hυ : 1 < υ) : 0 < dilB r0 υ := by
  unfold dilB
  split_ifs with h1 h2
  · exact inv_pos.mpr (by linarith)
  · exact inv_pos.mpr (mul_pos (Real.exp_pos 1) (by linarith))
  · have h3 : 1 < r0 := lt_of_le_of_ne (not_lt.mp h1) (Ne.symm h2)
    exact inv_pos.mpr (by linarith)

theorem dil_part1 (g : ℝ → ℝ) (hgc : ContinuousOn g (Ici 0))
    (hgnn : ∀ v ∈ Ici (0 : ℝ), 0 ≤ g v) (hgi : IntegrableOn g (Ioi 0))
    (hgint : ∫ v in Ioi (0 : ℝ), g v ≤ 1)
    (K υ Hs r0 : ℝ) (hK : 0 < K) (hυ : 1 < υ) (hHs : 0 < Hs)
    (hr0 : 0 < r0) (hr0υ : r0 ≤ υ)
    (hg : ∀ v ∈ Icc (0 : ℝ) Hs, g v ≤ K * (1 + v) ^ (-υ))
    (u : ℝ) (hu0 : 0 ≤ u) (huH : u ≤ Hs) :
    ∫ s in (0:ℝ)..u, g s * ((dilScale K r0 υ + u - s) ^ (-r0) * (dilScale K r0 υ + u) ^ r0)
      ≤ 3 / 2 + K * dilDelta r0 ^ (-υ) * dilScale K r0 υ ^ (1 - υ) * dilB r0 υ := by
  have hD1 : (1:ℝ) ≤ dilScale K r0 υ := le_max_left _ _
  have hD : 0 < dilScale K r0 υ := by linarith
  obtain ⟨hδ0, hδ1, hδr⟩ := dil_delta_facts r0 hr0
  have hb := dil_B_pos r0 υ hr0 hυ
  have hT : 0 ≤ K * dilDelta r0 ^ (-υ) * dilScale K r0 υ ^ (1 - υ) * dilB r0 υ :=
    mul_nonneg (mul_nonneg (mul_nonneg hK.le (Real.rpow_nonneg hδ0.le _))
      (Real.rpow_nonneg hD.le _)) hb.le
  set D := dilScale K r0 υ with hDdef
  set δ := dilDelta r0 with hδdef
  set a := D + u with hadef
  have ha : 0 < a := by linarith
  have hgI : ∀ x : ℝ, 0 ≤ x → IntervalIntegrable g volume 0 x := fun x hx =>
    ContinuousOn.intervalIntegrable_of_Icc hx (hgc.mono (fun v hv => hv.1))
  have hgcu : ContinuousOn g (Icc 0 u) := hgc.mono (fun v hv => hv.1)
  have hRc : ∀ x : ℝ, x ≤ u → ContinuousOn (fun s => (D + u - s) ^ (-r0) * a ^ r0) (Icc 0 x) := by
    intro x hx
    apply ContinuousOn.mul _ continuousOn_const
    apply ContinuousOn.rpow_const (by fun_prop)
    intro s hs
    left
    have : 0 < D + u - s := by linarith [hs.2]
    exact this.ne'
  have hgRi : ∀ x : ℝ, 0 ≤ x → x ≤ u → IntervalIntegrable
      (fun s => g s * ((D + u - s) ^ (-r0) * a ^ r0)) volume 0 x := by
    intro x hx hxu
    apply ContinuousOn.intervalIntegrable_of_Icc hx
    exact (hgcu.mono (Icc_subset_Icc le_rfl hxu)).mul ((hRc x hxu))
  have hgRc : ∀ x y : ℝ, 0 ≤ x → x ≤ y → y ≤ u → IntervalIntegrable
      (fun s => g s * ((D + u - s) ^ (-r0) * a ^ r0)) volume x y := by
    intro x y hx hxy hyu
    apply ContinuousOn.intervalIntegrable_of_Icc hxy
    exact (hgcu.mono (Icc_subset_Icc hx hyu)).mul ((hRc y hyu).mono (Icc_subset_Icc hx le_rfl))
  have hR_nonneg : ∀ s : ℝ, s ≤ u → 0 ≤ (D + u - s) ^ (-r0) * a ^ r0 := by
    intro s hs
    exact mul_nonneg (Real.rpow_nonneg (by linarith) _) (Real.rpow_nonneg ha.le _)
  by_cases hcu : δ * a ≤ u
  · have hc0 : 0 ≤ δ * a := by positivity
    have hcpos : 0 < δ * a := mul_pos hδ0 ha
    have hsplit := intervalIntegral.integral_add_adjacent_intervals (hgRc 0 (δ * a) le_rfl hc0 hcu)
      (hgRc (δ * a) u hc0 hcu le_rfl)
    rw [← hsplit]
    -- early piece
    have hE : ∫ s in (0:ℝ)..(δ * a), g s * ((D + u - s) ^ (-r0) * a ^ r0)
        ≤ ∫ s in (0:ℝ)..(δ * a), (3 / 2) * g s := by
      apply intervalIntegral.integral_mono_on hc0 (hgRc 0 (δ * a) le_rfl hc0 hcu)
        ((hgI (δ * a) hc0).const_mul _)
      intro s hs
      have hR := dil_early_ratio a δ r0 s ha hr0 hδ0 hδ1 hδr hs.1 hs.2
      have hgs := hgnn s (Set.mem_Ici.mpr hs.1)
      nlinarith
    rw [intervalIntegral.integral_const_mul] at hE
    have h1 := dil_int_le_one g (δ * a) hc0 hgnn hgi hgint
    have hI : 0 ≤ ∫ s in (0:ℝ)..(δ * a), g s := intervalIntegral.integral_nonneg hc0
      (fun v hv => hgnn v (Set.mem_Ici.mpr hv.1))
    -- late piece, pointwise
    have hpowc : ContinuousOn (fun s => (D + u - s) ^ (-r0)) (Icc 0 u) := by
      apply ContinuousOn.rpow_const (by fun_prop)
      intro s hs
      left
      have : 0 < D + u - s := by linarith [hs.2]
      exact this.ne'
    have hL : ∫ s in (δ * a)..u, g s * ((D + u - s) ^ (-r0) * a ^ r0)
        ≤ ∫ s in (δ * a)..u, (K * δ ^ (-υ) * (a ^ (-υ) * a ^ r0)) * (a - s) ^ (-r0) := by
      apply intervalIntegral.integral_mono_on hcu (hgRc (δ * a) u hc0 hcu le_rfl)
      · apply ContinuousOn.intervalIntegrable_of_Icc hcu
        exact (continuousOn_const.mul (hpowc.mono (Icc_subset_Icc hc0 le_rfl))).mono
          (fun s hs => hs)
      intro s hs
      have hgs : g s ≤ K * (1 + s) ^ (-υ) :=
        hg s ⟨by linarith [hs.1], by linarith [hs.2]⟩
      have hpow : (1 + s) ^ (-υ) ≤ (δ * a) ^ (-υ) :=
        Real.rpow_le_rpow_of_nonpos hcpos (by linarith [hs.1]) (by linarith)
      have hmul : (δ * a) ^ (-υ) = δ ^ (-υ) * a ^ (-υ) := Real.mul_rpow hδ0.le ha.le
      have hg2 : g s ≤ K * (δ ^ (-υ) * a ^ (-υ)) := by
        rw [← hmul]
        exact le_trans hgs (mul_le_mul_of_nonneg_left hpow hK.le)
      have hRs := hR_nonneg s hs.2
      calc g s * ((D + u - s) ^ (-r0) * a ^ r0)
          ≤ (K * (δ ^ (-υ) * a ^ (-υ))) * ((D + u - s) ^ (-r0) * a ^ r0) :=
            mul_le_mul_of_nonneg_right hg2 hRs
        _ = (K * δ ^ (-υ) * (a ^ (-υ) * a ^ r0)) * (a - s) ^ (-r0) := by
            rw [hadef]; ring
    have hau : a - u = D := by rw [hadef]; ring
    have hLate : ∫ s in (δ * a)..u, (K * δ ^ (-υ) * (a ^ (-υ) * a ^ r0)) * (a - s) ^ (-r0)
        ≤ K * δ ^ (-υ) * D ^ (1 - υ) * dilB r0 υ := by
      rw [intervalIntegral.integral_const_mul, dil_sub a u δ r0, hau]
      have := dil_late_final D a (a - δ * a) υ r0 (K * δ ^ (-υ)) hD
        (by linarith) (by linarith) (by linarith [hcu]) hυ hr0 hr0υ (mul_nonneg hK.le (Real.rpow_nonneg hδ0.le _))
      linarith [this]
    linarith
  · -- all of [0,u] lies in the early region
    have hle : ∫ s in (0:ℝ)..u, g s * ((D + u - s) ^ (-r0) * a ^ r0)
        ≤ ∫ s in (0:ℝ)..u, (3 / 2) * g s := by
      apply intervalIntegral.integral_mono_on hu0 (hgRi u hu0 le_rfl)
        ((hgI u hu0).const_mul _)
      intro s hs
      have hR := dil_early_ratio a δ r0 s ha hr0 hδ0 hδ1 hδr hs.1 (by linarith [hs.2, not_le.mp hcu])
      have hgs := hgnn s (Set.mem_Ici.mpr hs.1)
      nlinarith
    rw [intervalIntegral.integral_const_mul] at hle
    have h1 := dil_int_le_one g u hu0 hgnn hgi hgint
    have hI : 0 ≤ ∫ s in (0:ℝ)..u, g s := intervalIntegral.integral_nonneg hu0
      (fun v hv => hgnn v (Set.mem_Ici.mpr hv.1))
    linarith

/-- `lem:app-phase-dilation`, snapshot `cr-2026-10-23`. Source: `section.tex` l.2265–2273 (environment).

LaTeX (verbatim, `section.tex` l.2265–2273):
```latex
\begin{lemma}[Dilated envelope]\label{lem:app-phase-dilation}
Let $g\ge0$ be continuous on $[0,\infty)$ with $\int_0^\infty g\le1$, and
suppose $g(v)\le K(1+v)^{-\upsilon}$ for $0\le v\le H_*$, where $H_*>0$,
$\upsilon>1$ and $K>0$. Let $0<r_0\le\upsilon$, $C>0$, $D=D(K,r_0,\upsilon)$ and
$h(u)\defeq C(1+u/D)^{-r_0}$. Then
\[
\frac{(g*h)(u)}{h(u)}\le\frac32+K\delta_\circ^{-\upsilon}D^{1-\upsilon}b(r_0,\upsilon)\le2\qquad(0\le u\le H_*).
\]
\end{lemma}
``` -/
theorem lem_app_phase_dilation (g : ℝ → ℝ) (hgc : ContinuousOn g (Ici 0))
    (hgnn : ∀ v ∈ Ici (0 : ℝ), 0 ≤ g v) (hgi : IntegrableOn g (Ioi 0))
    (hgint : ∫ v in Ioi (0 : ℝ), g v ≤ 1)
    (K υ Hs r0 C : ℝ) (hK : 0 < K) (hυ : 1 < υ) (hHs : 0 < Hs)
    (hr0 : 0 < r0) (hr0υ : r0 ≤ υ) (hC : 0 < C)
    (hg : ∀ v ∈ Icc (0 : ℝ) Hs, g v ≤ K * (1 + v) ^ (-υ)) :
    (∀ u ∈ Icc (0 : ℝ) Hs,
      oneSidedConv (fun w => C * (1 + w / dilScale K r0 υ) ^ (-r0)) g u
          / (C * (1 + u / dilScale K r0 υ) ^ (-r0))
        ≤ 3 / 2 + K * dilDelta r0 ^ (-υ) * dilScale K r0 υ ^ (1 - υ) * dilB r0 υ) ∧
      3 / 2 + K * dilDelta r0 ^ (-υ) * dilScale K r0 υ ^ (1 - υ) * dilB r0 υ ≤ 2 := by
  have hD1 : (1:ℝ) ≤ dilScale K r0 υ := le_max_left _ _
  have hD : 0 < dilScale K r0 υ := by linarith
  have hb := dil_B_pos r0 υ hr0 hυ
  have hhalf := dil_final_half K υ r0 hK hυ hb (dil_delta_facts r0 hr0).1
  refine ⟨?_, by linarith⟩
  intro u hu
  obtain ⟨hu0, huH⟩ := hu
  have hP0 : 0 < (1 + u / dilScale K r0 υ) ^ (-r0) :=
    Real.rpow_pos_of_pos (by positivity) _
  have hconv : oneSidedConv (fun w => C * (1 + w / dilScale K r0 υ) ^ (-r0)) g u
      = C * (1 + u / dilScale K r0 υ) ^ (-r0) *
        ∫ s in (0:ℝ)..u, g s * ((dilScale K r0 υ + u - s) ^ (-r0) * (dilScale K r0 υ + u) ^ r0) := by
    unfold oneSidedConv
    have : ∫ s in (0:ℝ)..u, C * (1 + (u - s) / dilScale K r0 υ) ^ (-r0) * g s
        = ∫ s in (0:ℝ)..u, C * (1 + u / dilScale K r0 υ) ^ (-r0) *
            (g s * ((dilScale K r0 υ + u - s) ^ (-r0) * (dilScale K r0 υ + u) ^ r0)) := by
      apply intervalIntegral.integral_congr
      intro s hs
      rw [uIcc_of_le hu0] at hs
      simp only
      rw [dil_ratio_id u (dilScale K r0 υ) s r0 hD hu0 hs.2]
      ring
    rw [this, intervalIntegral.integral_const_mul]
  rw [hconv, mul_div_cancel_left₀ _ (mul_pos hC hP0).ne']
  exact dil_part1 g hgc hgnn hgi hgint K υ Hs r0 hK hυ hHs hr0 hr0υ hg u hu0 huH

/-! ## The \SignSVD kernel -/

/-! ### Proof helpers for `lem:app-phase-svd-small` (P-H.7.P2) -/

lemma sv_Lsum_fin (N : ℕ) (a q u : ℝ) :
    Lsum (N : ℕ∞) a q u
      = ∑ i ∈ Finset.Icc 1 N, (i : ℝ) ^ (-a) * Real.exp (-(2 * u) * (i : ℝ) ^ (-q)) := by
  unfold Lsum
  rw [tsum_eq_sum (s := Finset.Icc 1 N)]
  · apply Finset.sum_congr rfl
    intro n hn
    rw [Finset.mem_Icc] at hn
    have h1 : 0 < n ∧ ((n : ℕ∞) ≤ (N : ℕ∞)) := ⟨by omega, by exact_mod_cast hn.2⟩
    rw [if_pos h1]
  · intro b hb
    rw [if_neg]
    rintro ⟨h1, h2⟩
    apply hb
    rw [Finset.mem_Icc]
    exact ⟨by omega, by exact_mod_cast h2⟩

lemma sv_kernel_fin (α : ℝ) (N : ℕ) (u : ℝ) :
    svdKernel α N u = 2 / Hsum (α / 2) N *
      ∑ i ∈ Finset.Icc 1 N, (i : ℝ) ^ (-α) * Real.exp (-(2 * u) * (i : ℝ) ^ (-(α / 2))) := by
  unfold svdKernel
  rw [sv_Lsum_fin]

lemma sv_kernel_eq (α : ℝ) (N : ℕ) (v : ℝ) :
    svdKernel α N v = ∑ i ∈ Finset.Icc 1 N, (2 / Hsum (α / 2) N) *
      (((i : ℝ) ^ (-(α / 2)) * (i : ℝ) ^ (-(α / 2)))
        * Real.exp (-(2 * v) * (i : ℝ) ^ (-(α / 2)))) := by
  rw [sv_kernel_fin, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mem_Icc] at hi
  have hi0 : (0:ℝ) < i := by exact_mod_cast (by omega : 0 < i)
  have hc : (i : ℝ) ^ (-α) = (i : ℝ) ^ (-(α / 2)) * (i : ℝ) ^ (-(α / 2)) := by
    rw [← Real.rpow_add hi0]; congr 1; ring
  rw [hc]

lemma sv_exp_integral (k u : ℝ) (hk : 0 < k) :
    ∫ v in (0:ℝ)..u, Real.exp (-(2 * v) * k) = (1 - Real.exp (-(2 * u) * k)) / (2 * k) := by
  have hderiv : ∀ v ∈ uIcc (0:ℝ) u,
      HasDerivAt (fun v => -Real.exp (-(2 * v) * k) / (2 * k)) (Real.exp (-(2 * v) * k)) v := by
    intro v _
    have h1 : HasDerivAt (fun y : ℝ => -(2 * y) * k) (-(2 * 1) * k) v :=
      (((hasDerivAt_id' v).const_mul 2).neg).mul_const k
    have h2 := ((h1.exp).neg).div_const (2 * k)
    convert h2 using 1
    field_simp
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    (Continuous.intervalIntegrable (by fun_prop) _ _)]
  simp only [mul_zero, zero_mul, neg_zero, Real.exp_zero]
  ring

lemma sv_term_int (H k u : ℝ) (hH : H ≠ 0) (hk : 0 < k) :
    ∫ v in (0:ℝ)..u, (2 / H) * ((k * k) * Real.exp (-(2 * v) * k))
      = 1 / H * k * (1 - Real.exp (-(2 * u) * k)) := by
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    sv_exp_integral k u hk]
  field_simp

lemma sv_kernel_integral (α : ℝ) (N : ℕ) (u : ℝ) (hH : Hsum (α / 2) N ≠ 0) :
    ∫ v in (0:ℝ)..u, svdKernel α N v
      = ∑ i ∈ Finset.Icc 1 N, 1 / Hsum (α / 2) N * (i : ℝ) ^ (-(α / 2))
          * (1 - Real.exp (-(2 * u) * (i : ℝ) ^ (-(α / 2)))) := by
  simp only [sv_kernel_eq]
  rw [intervalIntegral.integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mem_Icc] at hi
    have hi0 : (0:ℝ) < i := by exact_mod_cast (by omega : 0 < i)
    exact sv_term_int _ _ u hH (Real.rpow_pos_of_pos hi0 _)
  · intro i _
    exact Continuous.intervalIntegrable (by fun_prop) _ _

lemma sv_hJ (q : ℝ) (hq0 : 0 < q) (hq1 : q < 1) (J : ℕ) :
    Hsum q J ≤ 1 + (J : ℝ) ^ (1 - q) / (1 - q) := by
  rcases Nat.eq_zero_or_pos J with hJ | hJ
  · subst hJ
    have h0 : (0:ℝ) ≤ ((0:ℕ):ℝ) ^ (1 - q) / (1 - q) :=
      div_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _) (by linarith)
    have hH0 : Hsum q 0 = 0 := by simp [Hsum]
    linarith
  · have h := (lem_app_phase_harmonic_i hq0 J hJ).2
    have hint : ∫ x in (1:ℝ)..(J:ℝ), x ^ (-q) = ((J:ℝ) ^ (1 - q) - 1) / (1 - q) := by
      rw [integral_rpow (Or.inl (by linarith)), show -q + 1 = 1 - q by ring, Real.one_rpow]
    rw [hint] at h
    have h2 : ((J:ℝ) ^ (1 - q) - 1) / (1 - q) ≤ (J:ℝ) ^ (1 - q) / (1 - q) :=
      div_le_div_of_nonneg_right (by linarith) (by linarith)
    linarith

lemma sv_Hlow (q : ℝ) (hq0 : 0 < q) (hq1 : q < 1) (N : ℕ) (hN1 : 1 ≤ N)
    (h2 : 2 ≤ (N : ℝ) ^ (1 - q)) :
    (N : ℝ) ^ (1 - q) / (2 * (1 - q)) ≤ Hsum q N := by
  have h := (lem_app_phase_harmonic_i hq0 N hN1).1
  have hint : ∫ x in (1:ℝ)..((N:ℝ) + 1), x ^ (-q) = (((N:ℝ) + 1) ^ (1 - q) - 1) / (1 - q) := by
    rw [integral_rpow (Or.inl (by linarith)), show -q + 1 = 1 - q by ring, Real.one_rpow]
  rw [hint] at h
  have hN0 : (0:ℝ) ≤ N := Nat.cast_nonneg N
  have hmono : (N : ℝ) ^ (1 - q) ≤ ((N:ℝ) + 1) ^ (1 - q) :=
    Real.rpow_le_rpow hN0 (by linarith) (by linarith)
  have hc : (0:ℝ) < 1 - q := by linarith
  have key : (N : ℝ) ^ (1 - q) / (2 * (1 - q)) ≤ (((N:ℝ) + 1) ^ (1 - q) - 1) / (1 - q) := by
    rw [div_le_div_iff₀ (by linarith) hc]
    nlinarith [mul_nonneg hc.le
      (by linarith : (0:ℝ) ≤ 2 * ((N:ℝ) + 1) ^ (1 - q) - 2 - (N:ℝ) ^ (1 - q))]
  linarith

lemma sv_rpow_le (X c N : ℝ) (hX : 0 < X) (hc : 0 < c) (h : X ^ (1 / c) ≤ N) :
    X ≤ N ^ c := by
  have h1 : (X ^ (1 / c)) ^ c ≤ N ^ c :=
    Real.rpow_le_rpow (Real.rpow_nonneg hX.le _) h hc.le
  rwa [← Real.rpow_mul hX.le, one_div_mul_cancel hc.ne', Real.rpow_one] at h1

lemma sv_small_core (q r δ : ℝ) (hq0 : 0 < q) (hq1 : q < 1) (hr0 : 0 < r) (hr1 : r < 1)
    (hδ : δ = ((1 - r) / 8) ^ (1 / (1 - q))) (N : ℕ) (hN1 : 1 ≤ N)
    (h2 : 2 ≤ (N : ℝ) ^ (1 - q)) (hNq : 8 * (1 - q) / (1 - r) ≤ (N : ℝ) ^ (1 - q))
    (u : ℝ) (hu0 : 0 ≤ u) (hu : u ≤ (1 - r) * δ ^ q / 8 * (N : ℝ) ^ q) :
    ∑ i ∈ Finset.Icc 1 N, 1 / Hsum q N * (i : ℝ) ^ (-q)
        * (1 - Real.exp (-(2 * u) * (i : ℝ) ^ (-q))) ≤ 3 / 4 * (1 - r) := by
  have hc : (0:ℝ) < 1 - q := by linarith
  have hr' : (0:ℝ) < 1 - r := by linarith
  have hN0 : (0:ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hA0 : (0:ℝ) < (N : ℝ) ^ (1 - q) := Real.rpow_pos_of_pos hN0 _
  have hδpos : 0 < δ := by
    rw [hδ]; exact Real.rpow_pos_of_pos (by linarith) _
  have hδ1 : δ ^ (1 - q) = (1 - r) / 8 := by
    rw [hδ, ← Real.rpow_mul (show (0:ℝ) ≤ (1 - r) / 8 by linarith), one_div_mul_cancel hc.ne',
      Real.rpow_one]
  have hδle : δ ≤ 1 := by
    rw [hδ]
    exact Real.rpow_le_one (by linarith) (by linarith) (le_of_lt (one_div_pos.mpr hc))
  have hHlow := sv_Hlow q hq0 hq1 N hN1 h2
  have hHpos : 0 < Hsum q N := lt_of_lt_of_le (div_pos hA0 (by linarith)) hHlow
  have hHne : Hsum q N ≠ 0 := hHpos.ne'
  set J : ℕ := ⌊δ * (N : ℝ)⌋₊ with hJdef
  have hJle : (J : ℝ) ≤ δ * N := Nat.floor_le (mul_nonneg hδpos.le hN0.le)
  have hJlt : δ * N < (J : ℝ) + 1 := Nat.lt_floor_add_one _
  have hJN : J ≤ N := by
    have : (J : ℝ) ≤ N := le_trans hJle (mul_le_of_le_one_left hN0.le hδle)
    exact_mod_cast this
  have hT0 : 0 ≤ 2 * u * (δ * (N : ℝ)) ^ (-q) :=
    mul_nonneg (by linarith) (Real.rpow_nonneg (mul_nonneg hδpos.le hN0.le) _)
  have hT : 2 * u * (δ * (N : ℝ)) ^ (-q) ≤ (1 - r) / 4 := by
    rw [Real.mul_rpow hδpos.le hN0.le, Real.rpow_neg hδpos.le, Real.rpow_neg hN0.le]
    have hδq : 0 < δ ^ q := Real.rpow_pos_of_pos hδpos _
    have hNq0 : 0 < (N : ℝ) ^ q := Real.rpow_pos_of_pos hN0 _
    have e : 2 * ((1 - r) * δ ^ q / 8 * (N : ℝ) ^ q) * ((δ ^ q)⁻¹ * ((N : ℝ) ^ q)⁻¹)
        = (1 - r) / 4 := by
      field_simp
      ring
    have hmul : 2 * u * ((δ ^ q)⁻¹ * ((N : ℝ) ^ q)⁻¹)
        ≤ 2 * ((1 - r) * δ ^ q / 8 * (N : ℝ) ^ q) * ((δ ^ q)⁻¹ * ((N : ℝ) ^ q)⁻¹) := by
      apply mul_le_mul_of_nonneg_right _
        (mul_nonneg (inv_nonneg.mpr hδq.le) (inv_nonneg.mpr hNq0.le))
      linarith
    linarith
  have hJb : Hsum q J ≤ 1 + (J : ℝ) ^ (1 - q) / (1 - q) := sv_hJ q hq0 hq1 J
  have hX : (J : ℝ) ^ (1 - q) ≤ (1 - r) / 8 * (N : ℝ) ^ (1 - q) := by
    have h1 : (J : ℝ) ^ (1 - q) ≤ (δ * (N : ℝ)) ^ (1 - q) :=
      Real.rpow_le_rpow (Nat.cast_nonneg J) hJle hc.le
    rw [Real.mul_rpow hδpos.le hN0.le, hδ1] at h1
    exact h1
  have hY1 : 1 - q ≤ (1 - r) / 8 * (N : ℝ) ^ (1 - q) := by
    have := (div_le_iff₀ hr').mp hNq
    linarith
  have hX' : (J : ℝ) ^ (1 - q) / (1 - q) ≤ (1 - r) / 8 * (N : ℝ) ^ (1 - q) / (1 - q) :=
    div_le_div_of_nonneg_right hX hc.le
  have hY2 : 1 ≤ (1 - r) / 8 * (N : ℝ) ^ (1 - q) / (1 - q) := by
    rw [le_div_iff₀ hc]; linarith
  have hHJ : Hsum q J ≤ (1 - r) / 2 * Hsum q N := by
    have hstep : (1 - r) / 2 * ((N : ℝ) ^ (1 - q) / (2 * (1 - q)))
        ≤ (1 - r) / 2 * Hsum q N :=
      mul_le_mul_of_nonneg_left hHlow (by linarith)
    have hid : (1 - r) / 2 * ((N : ℝ) ^ (1 - q) / (2 * (1 - q)))
        = 2 * ((1 - r) / 8 * (N : ℝ) ^ (1 - q) / (1 - q)) := by
      field_simp
      ring
    linarith
  have hfinal1 : 1 / Hsum q N * Hsum q J ≤ (1 - r) / 2 := by
    calc 1 / Hsum q N * Hsum q J ≤ 1 / Hsum q N * ((1 - r) / 2 * Hsum q N) :=
          mul_le_mul_of_nonneg_left hHJ (div_nonneg zero_le_one hHpos.le)
      _ = (1 - r) / 2 := by field_simp
  have hpt : ∀ i ∈ Finset.Icc 1 N,
      1 / Hsum q N * (i : ℝ) ^ (-q) * (1 - Real.exp (-(2 * u) * (i : ℝ) ^ (-q)))
        ≤ 1 / Hsum q N * (if i ≤ J then (i : ℝ) ^ (-q) else 0)
          + (2 * u * (δ * (N : ℝ)) ^ (-q)) / Hsum q N * (i : ℝ) ^ (-q) := by
    intro i hi
    rw [Finset.mem_Icc] at hi
    have hi0 : (0:ℝ) < i := by exact_mod_cast (by omega : 0 < i)
    have hk0 : 0 < (i : ℝ) ^ (-q) := Real.rpow_pos_of_pos hi0 _
    have hH' : 0 < 1 / Hsum q N := one_div_pos.mpr hHpos
    have hE1 : 1 - Real.exp (-(2 * u) * (i : ℝ) ^ (-q)) ≤ 2 * u * (i : ℝ) ^ (-q) := by
      have := Real.add_one_le_exp (-(2 * u) * (i : ℝ) ^ (-q))
      linarith
    have hE0 : 1 - Real.exp (-(2 * u) * (i : ℝ) ^ (-q)) ≤ 1 := by
      have := Real.exp_pos (-(2 * u) * (i : ℝ) ^ (-q))
      linarith
    have hT3 : 0 ≤ (2 * u * (δ * (N : ℝ)) ^ (-q)) / Hsum q N * (i : ℝ) ^ (-q) :=
      mul_nonneg (div_nonneg hT0 hHpos.le) hk0.le
    by_cases hiJ : i ≤ J
    · rw [if_pos hiJ]
      have h1 := mul_le_mul_of_nonneg_left hE0 (le_of_lt (mul_pos hH' hk0))
      have h2 : 1 / Hsum q N * (i : ℝ) ^ (-q) * (1 - Real.exp (-(2 * u) * (i : ℝ) ^ (-q)))
          ≤ 1 / Hsum q N * (i : ℝ) ^ (-q) * 1 := h1
      linarith
    · rw [if_neg hiJ]
      have hiJ' : (J : ℝ) + 1 ≤ i := by exact_mod_cast (by omega : J + 1 ≤ i)
      have hδi : δ * (N : ℝ) ≤ (i : ℝ) := le_trans hJlt.le hiJ'
      have hpow : (i : ℝ) ^ (-q) ≤ (δ * (N : ℝ)) ^ (-q) :=
        Real.rpow_le_rpow_of_nonpos (mul_pos hδpos hN0) hδi (by linarith)
      have hkT : 2 * u * (i : ℝ) ^ (-q) ≤ 2 * u * (δ * (N : ℝ)) ^ (-q) :=
        mul_le_mul_of_nonneg_left hpow (by linarith)
      have hA : (i : ℝ) ^ (-q) * (1 - Real.exp (-(2 * u) * (i : ℝ) ^ (-q)))
          ≤ 2 * u * (δ * (N : ℝ)) ^ (-q) * (i : ℝ) ^ (-q) := by
        calc (i : ℝ) ^ (-q) * (1 - Real.exp (-(2 * u) * (i : ℝ) ^ (-q)))
            ≤ (i : ℝ) ^ (-q) * (2 * u * (i : ℝ) ^ (-q)) :=
              mul_le_mul_of_nonneg_left hE1 hk0.le
          _ = 2 * u * (i : ℝ) ^ (-q) * (i : ℝ) ^ (-q) := by ring
          _ ≤ 2 * u * (δ * (N : ℝ)) ^ (-q) * (i : ℝ) ^ (-q) :=
              mul_le_mul_of_nonneg_right hkT hk0.le
      have h1 := mul_le_mul_of_nonneg_left hA hH'.le
      calc 1 / Hsum q N * (i : ℝ) ^ (-q) * (1 - Real.exp (-(2 * u) * (i : ℝ) ^ (-q)))
          = 1 / Hsum q N * ((i : ℝ) ^ (-q) * (1 - Real.exp (-(2 * u) * (i : ℝ) ^ (-q)))) := by
            ring
        _ ≤ 1 / Hsum q N * (2 * u * (δ * (N : ℝ)) ^ (-q) * (i : ℝ) ^ (-q)) := h1
        _ = 1 / Hsum q N * 0 + (2 * u * (δ * (N : ℝ)) ^ (-q)) / Hsum q N * (i : ℝ) ^ (-q) := by
            ring
  have hfilt : (Finset.Icc 1 N).filter (fun i => i ≤ J) = Finset.Icc 1 J := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_Icc]
    omega
  have hsum1 : ∑ i ∈ Finset.Icc 1 N, (if i ≤ J then (i : ℝ) ^ (-q) else 0) = Hsum q J := by
    rw [← Finset.sum_filter, hfilt]
    rfl
  have htot : ∑ i ∈ Finset.Icc 1 N, 1 / Hsum q N * (i : ℝ) ^ (-q)
        * (1 - Real.exp (-(2 * u) * (i : ℝ) ^ (-q)))
      ≤ 1 / Hsum q N * Hsum q J + (2 * u * (δ * (N : ℝ)) ^ (-q)) / Hsum q N * Hsum q N := by
    calc _ ≤ ∑ i ∈ Finset.Icc 1 N, (1 / Hsum q N * (if i ≤ J then (i : ℝ) ^ (-q) else 0)
          + (2 * u * (δ * (N : ℝ)) ^ (-q)) / Hsum q N * (i : ℝ) ^ (-q)) :=
          Finset.sum_le_sum hpt
      _ = 1 / Hsum q N * Hsum q J + (2 * u * (δ * (N : ℝ)) ^ (-q)) / Hsum q N * Hsum q N := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hsum1]
          rfl
  have hTH : (2 * u * (δ * (N : ℝ)) ^ (-q)) / Hsum q N * Hsum q N
      = 2 * u * (δ * (N : ℝ)) ^ (-q) := by
    field_simp
  linarith [htot, hTH, hfinal1, hT]

/-- `lem:app-phase-svd-small`, snapshot `cr-2026-10-23`. Source: `section.tex` l.2298–2309 (environment).

LaTeX (verbatim, `section.tex` l.2298–2309):
```latex
\begin{lemma}[\SignSVD kernel, $0<\alpha<2$, small times]\label{lem:app-phase-svd-small}
Let $0<\alpha<2$ and $0<r<1$, and put
\[
\delta_1\defeq\Big[\frac{1-r}8\Big]^{1/(1-q)},\qquad \mathsf c_1\defeq\frac{(1-r)\delta_1^q}8,
\]
\[
N_1\defeq\Big\lceil\max\Big\{4,\ 2^{1/(1-q)},\ \Big[\frac{8(1-q)}{1-r}\Big]^{1/(1-q)}\Big\}\Big\rceil .
\]
For $N\ge N_1$ and $0\le u\le\mathsf c_1N^q$, $m_g(u)\le\frac34(1-r)$. Consequently,
for every $C>0$ and $h(u)=C(1+u)^{-r}$, $(g*h)(u)\le\frac34h(u)$ on
$[0,\mathsf c_1N^q]$.
\end{lemma}
``` -/
theorem lem_app_phase_svd_small (α r : ℝ) (hα0 : 0 < α) (hα2 : α < 2)
    (hr0 : 0 < r) (hr1 : r < 1) (N : ℕ) (hN : svdSmallN1 α r ≤ N) :
    (∀ u : ℝ, 0 ≤ u → u ≤ svdSmallC1 α r * (N : ℝ) ^ (α / 2) →
        ∫ v in (0 : ℝ)..u, svdKernel α N v ≤ 3 / 4 * (1 - r)) ∧
    (∀ C : ℝ, 0 < C → ∀ u ∈ Icc (0 : ℝ) (svdSmallC1 α r * (N : ℝ) ^ (α / 2)),
        oneSidedConv (fun w => C * (1 + w) ^ (-r)) (svdKernel α N) u
          ≤ 3 / 4 * (C * (1 + u) ^ (-r))) := by
  have hq0 : 0 < α / 2 := by linarith
  have hq1 : α / 2 < 1 := by linarith
  have hr' : (0:ℝ) < 1 - r := by linarith
  unfold svdSmallN1 at hN
  have hNM : max 4 (max ((2 : ℝ) ^ (1 / (1 - α / 2)))
      ((8 * (1 - α / 2) / (1 - r)) ^ (1 / (1 - α / 2)))) ≤ (N : ℝ) :=
    le_trans (Nat.le_ceil _) (by exact_mod_cast hN)
  have h4 : (4 : ℝ) ≤ N := le_trans (le_max_left _ _) hNM
  have hN1 : 1 ≤ N := by
    have h4' : 4 ≤ N := by exact_mod_cast h4
    omega
  have hN0 : (0:ℝ) < N := by linarith
  have h2' : (2 : ℝ) ^ (1 / (1 - α / 2)) ≤ N :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hNM
  have hb' : (8 * (1 - α / 2) / (1 - r)) ^ (1 / (1 - α / 2)) ≤ N :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hNM
  have h2 : 2 ≤ (N : ℝ) ^ (1 - α / 2) :=
    sv_rpow_le 2 (1 - α / 2) N (by norm_num) (by linarith) h2'
  have hNq : 8 * (1 - α / 2) / (1 - r) ≤ (N : ℝ) ^ (1 - α / 2) :=
    sv_rpow_le _ _ N (div_pos (by linarith) hr') (by linarith) hb'
  have hHlow := sv_Hlow (α / 2) hq0 hq1 N hN1 h2
  have hHpos : 0 < Hsum (α / 2) N :=
    lt_of_lt_of_le (div_pos (Real.rpow_pos_of_pos hN0 _) (by linarith)) hHlow
  have hHne : Hsum (α / 2) N ≠ 0 := hHpos.ne'
  have hsmall := sv_small_core (α / 2) r (svdSmallDelta1 α r) hq0 hq1 hr0 hr1 rfl N hN1 h2 hNq
  have hpart1 : ∀ u : ℝ, 0 ≤ u → u ≤ svdSmallC1 α r * (N : ℝ) ^ (α / 2) →
      ∫ v in (0 : ℝ)..u, svdKernel α N v ≤ 3 / 4 * (1 - r) := by
    intro u hu0 hu
    rw [sv_kernel_integral α N u hHne]
    exact hsmall u hu0 hu
  refine ⟨hpart1, ?_⟩
  intro C hC u hu
  have hu0 : 0 ≤ u := hu.1
  have hf : svdKernel α N = fun v => ∑ i ∈ Finset.Icc 1 N, (2 / Hsum (α / 2) N) *
      (((i : ℝ) ^ (-(α / 2)) * (i : ℝ) ^ (-(α / 2)))
        * Real.exp (-(2 * v) * (i : ℝ) ^ (-(α / 2)))) :=
    funext (sv_kernel_eq α N)
  have hcont : Continuous (svdKernel α N) := by
    rw [hf]
    fun_prop
  have hnn : ∀ v ∈ Ici (0:ℝ), 0 ≤ svdKernel α N v := by
    intro v _
    rw [sv_kernel_eq]
    apply Finset.sum_nonneg
    intro i _
    have hi : (0:ℝ) ≤ (i : ℝ) ^ (-(α / 2)) := Real.rpow_nonneg (Nat.cast_nonneg i) _
    exact mul_nonneg (div_nonneg (by norm_num) hHpos.le)
      (mul_nonneg (mul_nonneg hi hi) (Real.exp_pos _).le)
  have hanti : AntitoneOn (svdKernel α N) (Ici (0:ℝ)) := by
    intro a _ b _ hab
    rw [sv_kernel_eq, sv_kernel_eq]
    apply Finset.sum_le_sum
    intro i hi
    rw [Finset.mem_Icc] at hi
    have hi0 : (0:ℝ) < i := by exact_mod_cast (by omega : 0 < i)
    have hk0 : 0 < (i : ℝ) ^ (-(α / 2)) := Real.rpow_pos_of_pos hi0 _
    have hkk : 0 ≤ (i : ℝ) ^ (-(α / 2)) * (i : ℝ) ^ (-(α / 2)) := mul_nonneg hk0.le hk0.le
    have hexp : Real.exp (-(2 * b) * (i : ℝ) ^ (-(α / 2)))
        ≤ Real.exp (-(2 * a) * (i : ℝ) ^ (-(α / 2))) :=
      Real.exp_le_exp.mpr (by nlinarith [mul_le_mul_of_nonneg_right hab hk0.le])
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hexp hkk)
      (div_nonneg (by norm_num) hHpos.le)
  have hm := lem_app_phase_mass (svdKernel α N) hcont.continuousOn hnn hanti C 1 r hC one_pos
    hr0 hr1 u hu0
  simp only [div_one] at hm
  have hI := hpart1 u hu0 hu.2
  have hratio : (∫ v in (0:ℝ)..u, svdKernel α N v) / (1 - r) ≤ 3 / 4 := by
    rw [div_le_iff₀ hr']
    linarith
  have hh : 0 ≤ C * (1 + u) ^ (-r) := mul_nonneg hC.le (Real.rpow_nonneg (by linarith) _)
  exact le_trans hm (mul_le_mul_of_nonneg_right hratio hh)

/-! ### Proof helpers for `lem:app-phase-svd-main` (P-H.7.P3): algebra and height bound -/

lemma svmain_rq_ge (α ς : ℝ) (hα1 : 1 < α) (hς : 1 ≤ ς) :
    1 ≤ rq (α + ς) (α / 2) := by
  unfold rq
  rw [one_le_div (by linarith)]
  linarith

lemma svmain_r0_bounds (α ς : ℝ) (hα1 : 1 < α) (hα2 : α < 2) (hς : 1 ≤ ς) :
    1 ≤ svdMainR0 α ς ∧ svdMainR0 α ς ≤ (1 + 2 / α) / 2 := by
  have h2a : 1 ≤ 2 / α := by
    rw [le_div_iff₀ (by linarith)]
    linarith
  have hcap : 1 ≤ (1 + 2 / α) / 2 := by linarith
  unfold svdMainR0
  split_ifs with h
  · exact ⟨le_refl _, hcap⟩
  · exact ⟨le_min (svmain_rq_ge α ς hα1 hς) hcap, min_le_right _ _⟩

lemma svmain_dV_pos (α ς : ℝ) (hα1 : 1 < α) (hα2 : α < 2) (hς : 1 ≤ ς) :
    0 < (svdMainJD α ς).2 := by
  have hα0 : 0 < α := by linarith
  obtain ⟨hr1, hr2⟩ := svmain_r0_bounds α ς hα1 hα2 hς
  unfold svdMainJD
  dsimp only
  split_ifs with h
  · exact div_pos (div_pos (mul_pos (by linarith) (by linarith)) (by linarith)) two_pos
  · set r0 := svdMainR0 α ς with hr0def
    show 0 < 1 - α / 2 - (r0 - (2 - 2 / α)) / (2 * r0)
    have hr0pos : 0 < r0 := by linarith
    have h2' : α * r0 ≤ (α + 2) / 2 := by
      have e : α * ((1 + 2 / α) / 2) = (α + 2) / 2 := by
        field_simp <;> ring
      have := mul_le_mul_of_nonneg_left hr2 hα0.le
      linarith
    have hD : α * ((1 - α / 2) * (2 * r0) - (r0 - (2 - 2 / α)))
        = (α - 1) * (2 - α * r0) := by
      field_simp <;> ring
    have hDpos : 0 < α * ((1 - α / 2) * (2 * r0) - (r0 - (2 - 2 / α))) := by
      rw [hD]
      exact mul_pos (by linarith) (by linarith)
    have hD' : 0 < (1 - α / 2) * (2 * r0) - (r0 - (2 - 2 / α)) :=
      pos_of_mul_pos_right hDpos hα0.le
    have hlt : (r0 - (2 - 2 / α)) / (2 * r0) < 1 - α / 2 := by
      rw [div_lt_iff₀ (by linarith)]
      linarith
    linarith

lemma svmain_Epq_pos (a q : ℝ) (ha : 1 < a) (hq : 0 < q) : 0 < Epq a q := by
  have hZ : 0 < Za a := by
    unfold Za
    have := div_pos one_pos (show (0 : ℝ) < a - 1 by linarith)
    linarith
  have hd : 0 < (2 : ℝ) ^ dAQ a q * Za a := mul_pos (Real.rpow_pos_of_pos (by norm_num) _) hZ
  exact lt_of_lt_of_le hd (le_max_left _ _)

lemma svmain_height_le (α ς ε : ℝ) (N : ℕ) (hα1 : 1 < α) (hα2 : α < 2) (hς : 1 ≤ ς)
    (hε : 0 < ε) (hC : 0 < Cpq (α + ς) (α / 2))
    (hεC : ε < Cpq (α + ς) (α / 2) ^ 2) (hεN : Cpq (α + ς) (α / 2) ^ 2 ≤ ε * N) :
    1 + phaseHeight (Cpq (α + ς) (α / 2)) (svdMainR0 α ς) ε ≤ Real.sqrt N := by
  obtain ⟨hr1, _⟩ := svmain_r0_bounds α ς hα1 hα2 hς
  set C := Cpq (α + ς) (α / 2) with hCdef
  set r0 := svdMainR0 α ς with hr0def
  have hsε : 0 < Real.sqrt ε := Real.sqrt_pos.mpr hε
  have hX1 : 1 ≤ C / Real.sqrt ε := by
    rw [one_le_div hsε]
    calc Real.sqrt ε ≤ Real.sqrt (C ^ 2) := Real.sqrt_le_sqrt hεC.le
      _ = C := Real.sqrt_sq hC.le
  have hXN : C / Real.sqrt ε ≤ Real.sqrt N := by
    rw [div_le_iff₀ hsε]
    have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    calc C = Real.sqrt (C ^ 2) := (Real.sqrt_sq hC.le).symm
      _ ≤ Real.sqrt (N * ε) := Real.sqrt_le_sqrt (by linarith [mul_comm ε (N:ℝ)])
      _ = Real.sqrt N * Real.sqrt ε := Real.sqrt_mul hN0 ε
  unfold phaseHeight
  have hle : (C / Real.sqrt ε) ^ (1 / r0) ≤ C / Real.sqrt ε := by
    calc (C / Real.sqrt ε) ^ (1 / r0) ≤ (C / Real.sqrt ε) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hX1 (by rw [div_le_one (by linarith)]; linarith)
      _ = C / Real.sqrt ε := Real.rpow_one _
  linarith

/-! ### Conjunct 3 of `lem:app-phase-svd-main` (P-H.7.P3): truncated convolution bound -/

lemma svmain_cont (α : ℝ) (N : ℕ) : Continuous (svdKernel α N) := by
  have hf : svdKernel α N = fun v => ∑ i ∈ Finset.Icc 1 N, (2 / Hsum (α / 2) N) *
      (((i : ℝ) ^ (-(α / 2)) * (i : ℝ) ^ (-(α / 2))) * Real.exp (-(2 * v) * (i : ℝ) ^ (-(α / 2)))) :=
    funext (sv_kernel_eq α N)
  rw [hf]
  fun_prop

lemma svmain_nonneg (α : ℝ) (N : ℕ) (hHpos : 0 < Hsum (α / 2) N) (v : ℝ) :
    0 ≤ svdKernel α N v := by
  rw [sv_kernel_eq]
  apply Finset.sum_nonneg
  intro i _
  have hi : (0:ℝ) ≤ (i : ℝ) ^ (-(α / 2)) := Real.rpow_nonneg (Nat.cast_nonneg i) _
  exact mul_nonneg (div_nonneg (by norm_num) hHpos.le)
    (mul_nonneg (mul_nonneg hi hi) (Real.exp_pos _).le)

lemma svmain_Hlow (q : ℝ) (hq : 0 ≤ q) (N : ℕ) (hN : 1 ≤ N) :
    (N : ℝ) ^ (1 - q) ≤ Hsum q N := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hterm : ∀ i ∈ Finset.Icc 1 N, (N : ℝ) ^ (-q) ≤ (i : ℝ) ^ (-q) := by
    intro i hi
    rw [Finset.mem_Icc] at hi
    have hi0 : (0 : ℝ) < i := by exact_mod_cast (by omega : 0 < i)
    exact Real.rpow_le_rpow_of_nonpos hi0 (by exact_mod_cast hi.2) (by linarith)
  have hsum := Finset.sum_le_sum hterm
  rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul] at hsum
  have e : (N : ℝ) ^ (1 - q) = (N : ℝ) * (N : ℝ) ^ (-q) := by
    rw [show (1 - q) = 1 + -q by ring, Real.rpow_add hN0, Real.rpow_one]
  have hcard : ((N + 1 - 1 : ℕ) : ℝ) = (N : ℝ) := by simp
  rw [hcard] at hsum
  rw [e]
  exact hsum

lemma svmain_mass (α : ℝ) (N : ℕ) (hα : 0 < α) (hN : 1 ≤ N) (x : ℝ) (hx : 0 ≤ x) :
    ∫ v in (0:ℝ)..x, svdKernel α N v ≤ 1 := by
  have hHN : (N : ℝ) ^ (1 - α / 2) ≤ Hsum (α / 2) N := svmain_Hlow (α / 2) (by linarith) N hN
  have hHpos : 0 < Hsum (α / 2) N :=
    lt_of_lt_of_le (Real.rpow_pos_of_pos (by exact_mod_cast hN) _) hHN
  rw [sv_kernel_integral α N x hHpos.ne']
  have hterm : ∀ i ∈ Finset.Icc 1 N,
      1 / Hsum (α / 2) N * (i : ℝ) ^ (-(α / 2))
          * (1 - Real.exp (-(2 * x) * (i : ℝ) ^ (-(α / 2))))
        ≤ 1 / Hsum (α / 2) N * (i : ℝ) ^ (-(α / 2)) := by
    intro i _
    have h0 : 0 ≤ 1 / Hsum (α / 2) N * (i : ℝ) ^ (-(α / 2)) :=
      mul_nonneg (one_div_nonneg.mpr hHpos.le) (Real.rpow_nonneg (Nat.cast_nonneg i) _)
    have h1 : 1 - Real.exp (-(2 * x) * (i : ℝ) ^ (-(α / 2))) ≤ 1 := by
      have := Real.exp_pos (-(2 * x) * (i : ℝ) ^ (-(α / 2)))
      linarith
    exact mul_le_of_le_one_right h0 h1
  calc _ ≤ ∑ i ∈ Finset.Icc 1 N, 1 / Hsum (α / 2) N * (i : ℝ) ^ (-(α / 2)) :=
        Finset.sum_le_sum hterm
    _ = 1 := by
        rw [← Finset.mul_sum]
        show 1 / Hsum (α / 2) N * Hsum (α / 2) N = 1
        exact one_div_mul_cancel hHpos.ne'

lemma svmain_env (α : ℝ) (N : ℕ) (hα1 : 1 < α) (hN : 1 ≤ N) (v : ℝ) (hv : 0 ≤ v) :
    svdKernel α N v
      ≤ (2 * Epq α (α / 2) / Hsum (α / 2) N) * (1 + v) ^ (-(2 - 2 / α)) := by
  have hHN : (N : ℝ) ^ (1 - α / 2) ≤ Hsum (α / 2) N := svmain_Hlow (α / 2) (by linarith) N hN
  have hHpos : 0 < Hsum (α / 2) N :=
    lt_of_lt_of_le (Real.rpow_pos_of_pos (by exact_mod_cast hN) _) hHN
  have hL := lem_app_phase_sums_i (a := α) (q := α / 2) hα1 (by linarith) (N : ℕ∞) hv
  have hd : dAQ α (α / 2) = 2 - 2 / α := by
    unfold dAQ
    field_simp <;> ring
  rw [hd] at hL
  unfold svdKernel
  have hpos : 0 ≤ 2 / Hsum (α / 2) N := div_nonneg (by norm_num) hHpos.le
  calc 2 / Hsum (α / 2) N * Lsum (N : ℕ∞) α (α / 2) v
      ≤ 2 / Hsum (α / 2) N * (Epq α (α / 2) * (1 + v) ^ (-(2 - 2 / α))) :=
        mul_le_mul_of_nonneg_left hL hpos
    _ = (2 * Epq α (α / 2) / Hsum (α / 2) N) * (1 + v) ^ (-(2 - 2 / α)) := by ring

lemma svmain_JN (α ς : ℝ) (N : ℕ) (hN : svdMainNV α ς ≤ N)
    (hd : 0 < (svdMainJD α ς).2) :
    2 * (svdMainJD α ς).1 ≤ (N : ℝ) ^ (svdMainJD α ς).2 := by
  unfold svdMainNV at hN
  have hM : max 1 ((2 * (svdMainJD α ς).1) ^ (1 / (svdMainJD α ς).2)) ≤ (N : ℝ) := by
    have h1 := Nat.le_ceil (max 1 ((2 * (svdMainJD α ς).1) ^ (1 / (svdMainJD α ς).2)))
    have h2 : ((⌈max 1 ((2 * (svdMainJD α ς).1) ^ (1 / (svdMainJD α ς).2))⌉₊ : ℕ) : ℝ) ≤ N := by
      exact_mod_cast hN
    linarith
  have hle : (2 * (svdMainJD α ς).1) ^ (1 / (svdMainJD α ς).2) ≤ (N : ℝ) :=
    le_trans (le_max_right _ _) hM
  rcases le_or_gt (2 * (svdMainJD α ς).1) 0 with h | h
  · exact h.trans (Real.rpow_nonneg (Nat.cast_nonneg N) _)
  · calc 2 * (svdMainJD α ς).1
        = ((2 * (svdMainJD α ς).1) ^ (1 / (svdMainJD α ς).2)) ^ (svdMainJD α ς).2 := by
          rw [← Real.rpow_mul h.le, one_div_mul_cancel hd.ne', Real.rpow_one]
      _ ≤ (N : ℝ) ^ (svdMainJD α ς).2 :=
          Real.rpow_le_rpow (Real.rpow_nonneg h.le _) hle hd.le

lemma svmain_Cpos (α ς : ℝ) (hα1 : 1 < α) (hς : 1 ≤ ς) :
    0 < Cpq (α + ς) (α / 2) := by
  unfold Cpq
  exact Real.sqrt_pos.mpr (div_pos (svmain_Epq_pos (α + ς) (α / 2) (by linarith) (by linarith)) two_pos)

lemma svmain_X_le (α ς ε : ℝ) (N : ℕ) (hα1 : 1 < α) (hς : 1 ≤ ς) (hε : 0 < ε)
    (hεC : ε < Cpq (α + ς) (α / 2) ^ 2) (hεN : Cpq (α + ς) (α / 2) ^ 2 ≤ ε * N) :
    Cpq (α + ς) (α / 2) / Real.sqrt ε ≤ Real.sqrt N := by
  have hC := svmain_Cpos α ς hα1 hς
  have hsε : 0 < Real.sqrt ε := Real.sqrt_pos.mpr hε
  rw [div_le_iff₀ hsε]
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  calc Cpq (α + ς) (α / 2) = Real.sqrt (Cpq (α + ς) (α / 2) ^ 2) := (Real.sqrt_sq hC.le).symm
    _ ≤ Real.sqrt (N * ε) := Real.sqrt_le_sqrt (by linarith [mul_comm ε (N:ℝ)])
    _ = Real.sqrt N * Real.sqrt ε := Real.sqrt_mul hN0 ε

lemma svmain_core (α r0 C u : ℝ) (N : ℕ) (hα1 : 1 < α) (hα2 : α < 2)
    (hr1 : 1 ≤ r0) (hN1 : 1 ≤ N)
    (hcase : (r0 = 1 ∧ 2 * (2 * Epq α (α / 2) * dilDelta r0 ^ (-(2 - 2 / α))
            / (Real.exp 1 * ((α - 1) * (2 - α) / (2 * α))))
          ≤ (N : ℝ) ^ ((α - 1) * (2 - α) / (2 * α) / 2))
        ∨ (1 < r0 ∧ 2 * (2 * Epq α (α / 2) * dilDelta r0 ^ (-(2 - 2 / α)) / (r0 - 1))
          ≤ (N : ℝ) ^ (1 - α / 2 - (r0 - (2 - 2 / α)) / (2 * r0))))
    (hC : 0 < C) (hu0 : 0 ≤ u) (ha : 1 + u ≤ (Real.sqrt N) ^ (1 / r0)) :
    oneSidedConv (fun w => C * (1 + w) ^ (-r0)) (svdKernel α N) u
      ≤ 2 * (C * (1 + u) ^ (-r0)) := by
  have hα0 : 0 < α := by linarith
  have hN1r : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hNpos : (0 : ℝ) < N := by linarith
  have hr0 : 0 < r0 := by linarith
  have hHN := svmain_Hlow (α / 2) (by linarith) N hN1
  have hHpos : 0 < Hsum (α / 2) N := lt_of_lt_of_le (Real.rpow_pos_of_pos hNpos _) hHN
  have hEpos : 0 < Epq α (α / 2) := svmain_Epq_pos α (α / 2) hα1 (by linarith)
  have h2a : 2 / α < 2 := by rw [div_lt_iff₀ hα0]; linarith
  have h2b : 1 < 2 / α := by rw [lt_div_iff₀ hα0]; linarith
  have hυ0 : 0 < 2 - 2 / α := by linarith
  have hυ1 : 2 - 2 / α < 1 := by linarith
  obtain ⟨hδ0, hδ1, hδr⟩ := dil_delta_facts r0 hr0
  obtain ⟨δ, hδdef⟩ : ∃ δ, δ = dilDelta r0 := ⟨_, rfl⟩
  rw [← hδdef] at hδ0 hδ1 hδr hcase
  have hK'N : 2 * Epq α (α / 2) / Hsum (α / 2) N
      ≤ 2 * Epq α (α / 2) * (N : ℝ) ^ (-(1 - α / 2)) := by
    rw [Real.rpow_neg hNpos.le, ← div_eq_mul_inv]
    exact div_le_div_of_nonneg_left (by linarith) (Real.rpow_pos_of_pos hNpos _) hHN
  have henv : ∀ v, 0 ≤ v → svdKernel α N v
      ≤ (2 * Epq α (α / 2) * (N : ℝ) ^ (-(1 - α / 2))) * (1 + v) ^ (-(2 - 2 / α)) :=
    fun v hv => (svmain_env α N hα1 hN1 v hv).trans
      (mul_le_mul_of_nonneg_right hK'N (Real.rpow_nonneg (by linarith) _))
  have hKc : 0 < 2 * Epq α (α / 2) * (N : ℝ) ^ (-(1 - α / 2)) :=
    mul_pos (by linarith) (Real.rpow_pos_of_pos hNpos _)
  have hgc := svmain_cont α N
  have hgnn := svmain_nonneg α N hHpos
  obtain ⟨a, ha_def⟩ : ∃ a, a = 1 + u := ⟨_, rfl⟩
  rw [← ha_def] at ha ⊢
  have ha0 : 0 < a := by linarith
  have hau : a - u = 1 := by linarith
  have hconv : oneSidedConv (fun w => C * (1 + w) ^ (-r0)) (svdKernel α N) u
      = C * a ^ (-r0) * ∫ s in (0:ℝ)..u, svdKernel α N s * ((a - s) ^ (-r0) * a ^ r0) := by
    unfold oneSidedConv
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro s hs
    rw [uIcc_of_le hu0] at hs
    have hsa : a - s = 1 + (u - s) := by rw [ha_def]; ring
    have harp : a ^ (-r0) * a ^ r0 = 1 := by
      rw [Real.rpow_neg ha0.le]
      exact inv_mul_cancel₀ (Real.rpow_pos_of_pos ha0 _).ne'
    dsimp only
    rw [hsa]
    linear_combination (-(C * svdKernel α N s * (1 + (u - s)) ^ (-r0))) * harp
  rw [hconv]
  have hpos : 0 ≤ C * a ^ (-r0) := mul_nonneg hC.le (Real.rpow_nonneg ha0.le _)
  suffices hkey : ∫ s in (0:ℝ)..u, svdKernel α N s * ((a - s) ^ (-r0) * a ^ r0) ≤ 2 by
    calc C * a ^ (-r0) * ∫ s in (0:ℝ)..u, svdKernel α N s * ((a - s) ^ (-r0) * a ^ r0)
        ≤ C * a ^ (-r0) * 2 := mul_le_mul_of_nonneg_left hkey hpos
      _ = 2 * (C * a ^ (-r0)) := by ring
  have hpowc : ContinuousOn (fun s => (a - s) ^ (-r0)) (Set.Icc 0 u) := by
    apply ContinuousOn.rpow_const (by fun_prop)
    intro s hs
    left
    exact (by linarith [hs.2] : (0:ℝ) < a - s).ne'
  have hRc : ∀ x, x ≤ u → ContinuousOn (fun s => (a - s) ^ (-r0) * a ^ r0) (Set.Icc 0 x) :=
    fun x hx => (hpowc.mono (Set.Icc_subset_Icc le_rfl hx)).mul continuousOn_const
  have hGi : ∀ x y, 0 ≤ x → x ≤ y → y ≤ u →
      IntervalIntegrable (fun s => svdKernel α N s * ((a - s) ^ (-r0) * a ^ r0)) MeasureTheory.volume x y := by
    intro x y hx hxy hyu
    apply ContinuousOn.intervalIntegrable_of_Icc hxy
    exact hgc.continuousOn.mul ((hRc y hyu).mono (Set.Icc_subset_Icc hx le_rfl))
  have hmass : ∀ x, 0 ≤ x → ∫ v in (0:ℝ)..x, svdKernel α N v ≤ 1 :=
    fun x hx => svmain_mass α N hα0 hN1 x hx
  by_cases hcu : δ * a ≤ u
  · have hc0 : 0 ≤ δ * a := mul_nonneg hδ0.le ha0.le
    have hsplit := intervalIntegral.integral_add_adjacent_intervals
      (hGi 0 (δ * a) le_rfl hc0 hcu) (hGi (δ * a) u hc0 hcu le_rfl)
    rw [← hsplit]
    have hE : ∫ s in (0:ℝ)..(δ * a), svdKernel α N s * ((a - s) ^ (-r0) * a ^ r0)
        ≤ ∫ s in (0:ℝ)..(δ * a), (3 / 2) * svdKernel α N s := by
      apply intervalIntegral.integral_mono_on hc0 (hGi 0 (δ * a) le_rfl hc0 hcu)
        ((hgc.intervalIntegrable _ _).const_mul _)
      intro s hs
      have hR := dil_early_ratio a δ r0 s ha0 hr0 hδ0 hδ1 hδr hs.1 hs.2
      have hgs := hgnn s
      calc svdKernel α N s * ((a - s) ^ (-r0) * a ^ r0)
          ≤ svdKernel α N s * (3 / 2) := mul_le_mul_of_nonneg_left hR hgs
        _ = (3 / 2) * svdKernel α N s := by ring
    rw [intervalIntegral.integral_const_mul] at hE
    have hEm := hmass (δ * a) hc0
    -- late part: pointwise envelope and substitution t = a - s
    set c := 2 * Epq α (α / 2) * (N : ℝ) ^ (-(1 - α / 2)) * δ ^ (-(2 - 2 / α))
      * (a ^ (-(2 - 2 / α)) * a ^ r0) with hcdef
    have hc_nonneg : 0 ≤ c := by
      rw [hcdef]
      exact mul_nonneg (mul_nonneg hKc.le (Real.rpow_nonneg hδ0.le _))
        (mul_nonneg (Real.rpow_nonneg ha0.le _) (Real.rpow_nonneg ha0.le _))
    have hL : ∫ s in (δ * a)..u, svdKernel α N s * ((a - s) ^ (-r0) * a ^ r0)
        ≤ c * ∫ s in (δ * a)..u, (a - s) ^ (-r0) := by
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_mono_on hcu (hGi (δ * a) u hc0 hcu le_rfl)
      · apply ContinuousOn.intervalIntegrable_of_Icc hcu
        exact continuousOn_const.mul (hpowc.mono (Set.Icc_subset_Icc hc0 le_rfl))
      · intro s hs
        have hgs : svdKernel α N s ≤ (2 * Epq α (α / 2) * (N : ℝ) ^ (-(1 - α / 2))) * (1 + s) ^ (-(2 - 2 / α)) :=
          henv s (by linarith [hs.1])
        have hp : (1 + s) ^ (-(2 - 2 / α)) ≤ (δ * a) ^ (-(2 - 2 / α)) :=
          Real.rpow_le_rpow_of_nonpos (mul_pos hδ0 ha0) (by linarith [hs.1]) (by linarith)
        have hmul : (δ * a) ^ (-(2 - 2 / α)) = δ ^ (-(2 - 2 / α)) * a ^ (-(2 - 2 / α)) :=
          Real.mul_rpow hδ0.le ha0.le
        have hg2 : svdKernel α N s ≤ 2 * Epq α (α / 2) * (N : ℝ) ^ (-(1 - α / 2))
            * (δ ^ (-(2 - 2 / α)) * a ^ (-(2 - 2 / α))) := by
          calc svdKernel α N s
              ≤ (2 * Epq α (α / 2) * (N : ℝ) ^ (-(1 - α / 2))) * (1 + s) ^ (-(2 - 2 / α)) := hgs
            _ ≤ (2 * Epq α (α / 2) * (N : ℝ) ^ (-(1 - α / 2))) * (δ * a) ^ (-(2 - 2 / α)) :=
                mul_le_mul_of_nonneg_left hp hKc.le
            _ = _ := by rw [hmul]
        have hR0 : 0 ≤ (a - s) ^ (-r0) * a ^ r0 :=
          mul_nonneg (Real.rpow_nonneg (by linarith [hs.2]) _) (Real.rpow_nonneg ha0.le _)
        calc svdKernel α N s * ((a - s) ^ (-r0) * a ^ r0)
            ≤ (2 * Epq α (α / 2) * (N : ℝ) ^ (-(1 - α / 2)) * (δ ^ (-(2 - 2 / α)) * a ^ (-(2 - 2 / α))))
                * ((a - s) ^ (-r0) * a ^ r0) := mul_le_mul_of_nonneg_right hg2 hR0
          _ = c * (a - s) ^ (-r0) := by rw [hcdef]; ring
    rw [dil_sub a u δ r0, hau] at hL
    -- the integral over t in [1, a - δ a]
    have hM1 : 1 ≤ a - δ * a := by linarith
    have hMa : a - δ * a ≤ a := by linarith
    have hfinal : c * ∫ t in (1:ℝ)..(a - δ * a), t ^ (-r0) ≤ 1 / 2 := by
      rcases hcase with ⟨h1, hJ⟩ | ⟨h1, hJ⟩
      · -- case r0 = 1: integral is a log, d = d_alpha / 2
        have hI : ∫ t in (1:ℝ)..(a - δ * a), t ^ (-r0) ≤ Real.log a := by
          have := dil_J_one 1 (a - δ * a) a one_pos hM1 hMa
          rw [div_one] at this
          rw [h1]
          exact this
        have ha' : a ≤ Real.sqrt N := by
          rw [h1, div_one, Real.rpow_one] at ha
          exact ha
        have hlog : Real.log a ≤ Real.log N / 2 := by
          have := Real.log_le_log ha0 ha'
          rwa [Real.log_sqrt hNpos.le] at this
        have hlogN : 0 ≤ Real.log N := Real.log_nonneg hN1r
        obtain ⟨dα, hdα⟩ : ∃ d, d = (α - 1) * (2 - α) / (2 * α) := ⟨_, rfl⟩
        rw [← hdα] at hJ
        have hdαpos : 0 < dα := by
          rw [hdα]; exact div_pos (mul_pos (by linarith) (by linarith)) (by linarith)
        have hcomp : a ^ (-(2 - 2 / α)) * a ^ (1:ℝ) ≤ (N : ℝ) ^ ((-(2 - 2 / α) + 1) / 2) := by
          rw [← Real.rpow_add ha0]
          calc a ^ (-(2 - 2 / α) + 1) ≤ (Real.sqrt N) ^ (-(2 - 2 / α) + 1) :=
                Real.rpow_le_rpow ha0.le ha' (by linarith)
            _ = (N : ℝ) ^ ((-(2 - 2 / α) + 1) / 2) := by
                rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hNpos.le]
                congr 1
                ring
        have hexp : (N : ℝ) ^ (-(1 - α / 2)) * (N : ℝ) ^ ((-(2 - 2 / α) + 1) / 2)
            = (N : ℝ) ^ (-(dα / 2)) * (N : ℝ) ^ (-(dα / 2)) := by
          rw [← Real.rpow_add hNpos, ← Real.rpow_add hNpos]
          congr 1
          rw [hdα]
          field_simp
          ring
        have hc_le : c ≤ 2 * Epq α (α / 2) * δ ^ (-(2 - 2 / α))
            * ((N : ℝ) ^ (-(dα / 2)) * (N : ℝ) ^ (-(dα / 2))) := by
          rw [hcdef, h1]
          calc 2 * Epq α (α / 2) * (N : ℝ) ^ (-(1 - α / 2)) * δ ^ (-(2 - 2 / α))
                * (a ^ (-(2 - 2 / α)) * a ^ (1:ℝ))
              ≤ (2 * Epq α (α / 2) * (N : ℝ) ^ (-(1 - α / 2)) * δ ^ (-(2 - 2 / α)))
                * (N : ℝ) ^ ((-(2 - 2 / α) + 1) / 2) :=
                mul_le_mul_of_nonneg_left hcomp
                  (mul_nonneg hKc.le (Real.rpow_nonneg hδ0.le _))
            _ = 2 * Epq α (α / 2) * δ ^ (-(2 - 2 / α))
                * ((N : ℝ) ^ (-(dα / 2)) * (N : ℝ) ^ (-(dα / 2))) := by
                rw [← hexp]
                ring
        have hdV : 0 < dα / 2 := by linarith
        have hlogbound := dil_log_sup (N : ℝ) (dα / 2) hNpos hdV
        have hnonneg1 : 0 ≤ Epq α (α / 2) * δ ^ (-(2 - 2 / α)) * (N : ℝ) ^ (-(dα / 2)) :=
          mul_nonneg (mul_nonneg hEpos.le (Real.rpow_nonneg hδ0.le _)) (Real.rpow_nonneg hNpos.le _)
        have hfin1 : c * ∫ t in (1:ℝ)..(a - δ * a), t ^ (-r0)
            ≤ (Epq α (α / 2) * δ ^ (-(2 - 2 / α)) * (N : ℝ) ^ (-(dα / 2)))
              * (1 / (Real.exp 1 * (dα / 2))) := by
          calc c * ∫ t in (1:ℝ)..(a - δ * a), t ^ (-r0)
              ≤ c * (Real.log N / 2) := mul_le_mul_of_nonneg_left (hI.trans hlog) hc_nonneg
            _ ≤ 2 * Epq α (α / 2) * δ ^ (-(2 - 2 / α))
                * ((N : ℝ) ^ (-(dα / 2)) * (N : ℝ) ^ (-(dα / 2))) * (Real.log N / 2) :=
                mul_le_mul_of_nonneg_right hc_le (div_nonneg hlogN (by norm_num))
            _ = (Epq α (α / 2) * δ ^ (-(2 - 2 / α)) * (N : ℝ) ^ (-(dα / 2)))
                * ((N : ℝ) ^ (-(dα / 2)) * Real.log N) := by ring
            _ ≤ (Epq α (α / 2) * δ ^ (-(2 - 2 / α)) * (N : ℝ) ^ (-(dα / 2)))
                * (1 / (Real.exp 1 * (dα / 2))) := mul_le_mul_of_nonneg_left hlogbound hnonneg1
        have hJform : (Epq α (α / 2) * δ ^ (-(2 - 2 / α)) * (N : ℝ) ^ (-(dα / 2)))
              * (1 / (Real.exp 1 * (dα / 2)))
            = (2 * Epq α (α / 2) * δ ^ (-(2 - 2 / α)) / (Real.exp 1 * dα)) * (N : ℝ) ^ (-(dα / 2)) := by
          field_simp <;> ring
        have hfinal2 : (2 * Epq α (α / 2) * δ ^ (-(2 - 2 / α)) / (Real.exp 1 * dα))
            * (N : ℝ) ^ (-(dα / 2)) ≤ 1 / 2 := by
          rw [Real.rpow_neg hNpos.le, ← div_eq_mul_inv,
            div_le_iff₀ (Real.rpow_pos_of_pos hNpos _)]
          linarith
        linarith [hfin1, hJform, hfinal2]
      · -- case r0 > 1: integral at most 1/(r0-1), d = 1 - q - (r0 - υ)/(2 r0)
        have hI : ∫ t in (1:ℝ)..(a - δ * a), t ^ (-r0) ≤ 1 / (r0 - 1) := by
          have := dil_J_gt 1 (a - δ * a) r0 one_pos hM1 h1
          rw [Real.one_rpow] at this
          exact this
        have hcomp : a ^ (-(2 - 2 / α)) * a ^ r0
            ≤ (N : ℝ) ^ ((r0 - (2 - 2 / α)) / (2 * r0)) := by
          rw [← Real.rpow_add ha0]
          calc a ^ (-(2 - 2 / α) + r0) ≤ ((Real.sqrt N) ^ (1 / r0)) ^ (-(2 - 2 / α) + r0) :=
                Real.rpow_le_rpow ha0.le ha (by linarith)
            _ = (N : ℝ) ^ ((r0 - (2 - 2 / α)) / (2 * r0)) := by
                rw [← Real.rpow_mul (Real.sqrt_nonneg (N : ℝ)), Real.sqrt_eq_rpow,
                  ← Real.rpow_mul hNpos.le]
                congr 1
                ring
        have hexpB : (N : ℝ) ^ (-(1 - α / 2)) * (N : ℝ) ^ ((r0 - (2 - 2 / α)) / (2 * r0))
            = (N : ℝ) ^ (-(1 - α / 2 - (r0 - (2 - 2 / α)) / (2 * r0))) := by
          rw [← Real.rpow_add hNpos]
          congr 1
          ring
        have hc_le : c ≤ 2 * Epq α (α / 2) * δ ^ (-(2 - 2 / α))
            * (N : ℝ) ^ (-(1 - α / 2 - (r0 - (2 - 2 / α)) / (2 * r0))) := by
          rw [hcdef]
          calc 2 * Epq α (α / 2) * (N : ℝ) ^ (-(1 - α / 2)) * δ ^ (-(2 - 2 / α))
                * (a ^ (-(2 - 2 / α)) * a ^ r0)
              ≤ (2 * Epq α (α / 2) * (N : ℝ) ^ (-(1 - α / 2)) * δ ^ (-(2 - 2 / α)))
                * (N : ℝ) ^ ((r0 - (2 - 2 / α)) / (2 * r0)) :=
                mul_le_mul_of_nonneg_left hcomp
                  (mul_nonneg hKc.le (Real.rpow_nonneg hδ0.le _))
            _ = 2 * Epq α (α / 2) * δ ^ (-(2 - 2 / α))
                * (N : ℝ) ^ (-(1 - α / 2 - (r0 - (2 - 2 / α)) / (2 * r0))) := by
                rw [← hexpB]
                ring
        have hfin1 : c * ∫ t in (1:ℝ)..(a - δ * a), t ^ (-r0)
            ≤ (2 * Epq α (α / 2) * δ ^ (-(2 - 2 / α)) / (r0 - 1))
              * (N : ℝ) ^ (-(1 - α / 2 - (r0 - (2 - 2 / α)) / (2 * r0))) := by
          calc c * ∫ t in (1:ℝ)..(a - δ * a), t ^ (-r0)
              ≤ c * (1 / (r0 - 1)) := mul_le_mul_of_nonneg_left hI hc_nonneg
            _ ≤ (2 * Epq α (α / 2) * δ ^ (-(2 - 2 / α))
                * (N : ℝ) ^ (-(1 - α / 2 - (r0 - (2 - 2 / α)) / (2 * r0))))
                * (1 / (r0 - 1)) :=
                mul_le_mul_of_nonneg_right hc_le (div_nonneg zero_le_one (by linarith))
            _ = (2 * Epq α (α / 2) * δ ^ (-(2 - 2 / α)) / (r0 - 1))
                * (N : ℝ) ^ (-(1 - α / 2 - (r0 - (2 - 2 / α)) / (2 * r0))) := by ring
        have hfinal2 : (2 * Epq α (α / 2) * δ ^ (-(2 - 2 / α)) / (r0 - 1))
            * (N : ℝ) ^ (-(1 - α / 2 - (r0 - (2 - 2 / α)) / (2 * r0))) ≤ 1 / 2 := by
          rw [Real.rpow_neg hNpos.le, ← div_eq_mul_inv,
            div_le_iff₀ (Real.rpow_pos_of_pos hNpos _)]
          linarith
        linarith [hfin1, hfinal2]
    linarith [hE, hL, hEm, hfinal]
  · -- all of [0, u] is early
    have hle : ∫ s in (0:ℝ)..u, svdKernel α N s * ((a - s) ^ (-r0) * a ^ r0)
        ≤ ∫ s in (0:ℝ)..u, (3 / 2) * svdKernel α N s := by
      apply intervalIntegral.integral_mono_on hu0 (hGi 0 u le_rfl hu0 le_rfl)
        ((hgc.intervalIntegrable _ _).const_mul _)
      intro s hs
      have hR := dil_early_ratio a δ r0 s ha0 hr0 hδ0 hδ1 hδr hs.1
        (by linarith [hs.2, not_le.mp hcu])
      have hgs := hgnn s
      calc svdKernel α N s * ((a - s) ^ (-r0) * a ^ r0)
          ≤ svdKernel α N s * (3 / 2) := mul_le_mul_of_nonneg_left hR hgs
        _ = (3 / 2) * svdKernel α N s := by ring
    rw [intervalIntegral.integral_const_mul] at hle
    have hEm := hmass u hu0
    linarith

/-- `lem:app-phase-svd-main`, snapshot `cr-2026-10-23`. Source: `section.tex` l.2332–2348 (environment).

LaTeX (verbatim, `section.tex` l.2332–2348):
```latex
\begin{lemma}[\SignSVD kernel, $1<\alpha<2$, $\texp\ge1$]\label{lem:app-phase-svd-main}
Let $1<\alpha<2$ and $\texp\ge1$, so that $r_{\text{s-SVD}}\ge1$. Put
$r_0\defeq1$ if $r_{\text{s-SVD}}=1$ and
$r_0\defeq\min\{r_{\text{s-SVD}},(1+2/\alpha)/2\}$ if $r_{\text{s-SVD}}>1$. Put
$\upsilon_\circ\defeq2-2/\alpha\in(0,1)$, $K_{\rm V}\defeq2E_{\alpha,q}$,
$\delta_\circ\defeq1-(2/3)^{1/r_0}$, $d_\alpha\defeq(\alpha-1)(2-\alpha)/(2\alpha)$,
\[
(J_{\rm V},d_{\rm V})\defeq\begin{cases}\big(K_{\rm V}\delta_\circ^{-\upsilon_\circ}/(e\,d_\alpha),\ d_\alpha/2\big),&r_0=1,\\[2pt]
\big(K_{\rm V}\delta_\circ^{-\upsilon_\circ}/(r_0-1),\ 1-q-(r_0-\upsilon_\circ)/(2r_0)\big),&r_0>1,\end{cases}
\]
\[
N_{\rm V}\defeq\big\lceil\max\{1,(2J_{\rm V})^{1/d_{\rm V}}\}\big\rceil .
\]
Then $d_{\rm V}>0$. Let $C=C_{p,q}$, $N\ge N_{\rm V}$, $0<\epsilon<C^2$ with
$\epsilon N\ge C^2$, $h(u)=C(1+u)^{-r_0}$ and $H=(C/\sqrt\epsilon)^{1/r_0}-1$.
Then $1+H\le\sqrt N$ and $(g*h)(u)\le2h(u)$ on $[0,H]$.
\end{lemma}
``` -/
theorem lem_app_phase_svd_main (α ς : ℝ) (hα1 : 1 < α) (hα2 : α < 2) (hς : 1 ≤ ς)
    (N : ℕ) (hN : svdMainNV α ς ≤ N) (ε : ℝ) (hε : 0 < ε)
    (hεC : ε < Cpq (α + ς) (α / 2) ^ 2) (hεN : Cpq (α + ς) (α / 2) ^ 2 ≤ ε * N) :
    0 < (svdMainJD α ς).2 ∧
      1 + phaseHeight (Cpq (α + ς) (α / 2)) (svdMainR0 α ς) ε ≤ Real.sqrt N ∧
      ∀ u ∈ Icc (0 : ℝ) (phaseHeight (Cpq (α + ς) (α / 2)) (svdMainR0 α ς) ε),
        oneSidedConv (fun w => Cpq (α + ς) (α / 2) * (1 + w) ^ (-svdMainR0 α ς)) (svdKernel α N) u
          ≤ 2 * (Cpq (α + ς) (α / 2) * (1 + u) ^ (-svdMainR0 α ς)) := by
  have hr := svmain_r0_bounds α ς hα1 hα2 hς
  have hd := svmain_dV_pos α ς hα1 hα2 hς
  have hC := svmain_Cpos α ς hα1 hς
  have hNr : (svdMainNV α ς : ℝ) ≤ N := by exact_mod_cast hN
  have hV1 : (1 : ℝ) ≤ svdMainNV α ς := by
    unfold svdMainNV
    exact le_trans (le_max_left _ _) (Nat.le_ceil _)
  have hN1 : 1 ≤ N := by
    have : (1 : ℝ) ≤ N := le_trans hV1 hNr
    exact_mod_cast this
  have hHt := svmain_height_le α ς ε N hα1 hα2 hς hε hC hεC hεN
  have hX := svmain_X_le α ς ε N hα1 hς hε hεC hεN
  have hJN := svmain_JN α ς N hN hd
  have hcase : (svdMainR0 α ς = 1 ∧ 2 * (2 * Epq α (α / 2) * dilDelta (svdMainR0 α ς) ^ (-(2 - 2 / α))
            / (Real.exp 1 * ((α - 1) * (2 - α) / (2 * α))))
          ≤ (N : ℝ) ^ ((α - 1) * (2 - α) / (2 * α) / 2))
        ∨ (1 < svdMainR0 α ς ∧ 2 * (2 * Epq α (α / 2) * dilDelta (svdMainR0 α ς) ^ (-(2 - 2 / α))
            / (svdMainR0 α ς - 1))
          ≤ (N : ℝ) ^ (1 - α / 2 - (svdMainR0 α ς - (2 - 2 / α)) / (2 * svdMainR0 α ς))) := by
    rcases eq_or_lt_of_le hr.1 with h | h
    · left
      refine ⟨h.symm, ?_⟩
      have hJ := hJN
      unfold svdMainJD at hJ
      dsimp only at hJ
      rw [if_pos h.symm] at hJ
      exact hJ
    · right
      refine ⟨h, ?_⟩
      have hJ := hJN
      unfold svdMainJD at hJ
      dsimp only at hJ
      rw [if_neg h.ne'] at hJ
      exact hJ
  refine ⟨hd, hHt, ?_⟩
  intro u hu
  obtain ⟨hu0, huH⟩ := hu
  have hsq : 0 ≤ Cpq (α + ς) (α / 2) / Real.sqrt ε := div_nonneg hC.le (Real.sqrt_nonneg _)
  have hpow : (Cpq (α + ς) (α / 2) / Real.sqrt ε) ^ (1 / svdMainR0 α ς)
      ≤ (Real.sqrt N) ^ (1 / svdMainR0 α ς) :=
    Real.rpow_le_rpow hsq hX (div_nonneg zero_le_one (by linarith [hr.1]))
  have ha : 1 + u ≤ (Real.sqrt N) ^ (1 / svdMainR0 α ς) := by
    unfold phaseHeight at huH
    linarith
  exact svmain_core α (svdMainR0 α ς) (Cpq (α + ς) (α / 2)) u N hα1 hα2 hr.1 hN1 hcase hC hu0 ha

lemma logI_f_eq (i : ℕ) :
    (if 0 < i then (i : ℝ) ^ (-(2:ℝ)) else 0) = (i : ℝ) ^ (-(2:ℝ)) := by
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · simp [Real.zero_rpow (by norm_num : (-(2:ℝ)) ≠ 0)]
  · simp [hi]

lemma logI_zeta_summable : Summable (fun i : ℕ => if 0 < i then (i : ℝ) ^ (-(2:ℝ)) else 0) := by
  simp_rw [logI_f_eq]
  exact Real.summable_nat_rpow.mpr (by norm_num)

/-- The termwise bound of the kernel summand by `i^{-2}`. -/
lemma logI_term_le (v : ℝ) (hv : 0 ≤ v) (i : ℕ) :
    (if 0 < i then (i : ℝ) ^ (-(2:ℝ)) * Real.exp (-(2 * v) * (i : ℝ) ^ (-(1:ℝ))) else 0)
      ≤ (if 0 < i then (i : ℝ) ^ (-(2:ℝ)) else 0) := by
  split_ifs with hi
  · have ht : 0 ≤ (i : ℝ) ^ (-(1:ℝ)) := Real.rpow_nonneg (Nat.cast_nonneg _) _
    have hx : -(2 * v) * (i : ℝ) ^ (-(1:ℝ)) ≤ 0 := by nlinarith
    exact mul_le_of_le_one_right (Real.rpow_nonneg (Nat.cast_nonneg _) _)
      (Real.exp_le_one_iff.mpr hx)
  · exact le_refl _

lemma logI_term_nonneg (v : ℝ) (i : ℕ) :
    0 ≤ (if 0 < i then (i : ℝ) ^ (-(2:ℝ)) * Real.exp (-(2 * v) * (i : ℝ) ^ (-(1:ℝ))) else 0) := by
  split_ifs
  · exact mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _) (Real.exp_pos _).le
  · exact le_refl _

lemma logI_Lsum_le (N : ℕ) (v : ℝ) (hv : 0 ≤ v) :
    Lsum (N : ℕ∞) 2 1 v ≤ ∑' i : ℕ, (if 0 < i then (i : ℝ) ^ (-(2:ℝ)) * Real.exp (-(2 * v) * (i : ℝ) ^ (-(1:ℝ))) else 0) := by
  unfold Lsum
  have hG : Summable (fun i : ℕ => if 0 < i then (i : ℝ) ^ (-(2:ℝ)) * Real.exp (-(2 * v) * (i : ℝ) ^ (-(1:ℝ))) else 0) :=
    Summable.of_nonneg_of_le (logI_term_nonneg v) (logI_term_le v hv) logI_zeta_summable
  have hF : Summable (fun i : ℕ => if 0 < i ∧ ((i : ℕ∞) ≤ (N : ℕ∞)) then
      (i : ℝ) ^ (-(2:ℝ)) * Real.exp (-(2 * v) * (i : ℝ) ^ (-(1:ℝ))) else 0) := by
    refine Summable.of_nonneg_of_le (fun i => ?_) (fun i => ?_) hG
    · split_ifs
      · exact mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _) (Real.exp_pos _).le
      · exact le_refl _
    · by_cases h : 0 < i ∧ ((i : ℕ∞) ≤ (N : ℕ∞))
      · rw [if_pos h, if_pos h.1]
      · rw [if_neg h]
        exact logI_term_nonneg v i
  refine Summable.tsum_le_tsum (fun i => ?_) hF hG
  by_cases h : 0 < i ∧ ((i : ℕ∞) ≤ (N : ℕ∞))
  · rw [if_pos h, if_pos h.1]
  · rw [if_neg h]
    exact logI_term_nonneg v i

lemma logI_Lsum_le_zeta (N : ℕ) (v : ℝ) (hv : 0 ≤ v) :
    Lsum (N : ℕ∞) 2 1 v ≤ zetaR 2 := by
  refine (logI_Lsum_le N v hv).trans ?_
  unfold zetaR
  exact Summable.tsum_le_tsum (logI_term_le v hv) (Summable.of_nonneg_of_le (logI_term_nonneg v) (logI_term_le v hv) logI_zeta_summable) logI_zeta_summable

lemma logI_Mpq_le : Mpq 2 1 ≤ 1 := by
  unfold Mpq
  have he : (2:ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1:ℝ)]
  apply Real.rpow_le_one (by positivity) _ (by norm_num)
  rw [mul_one, div_le_one (by linarith)]
  linarith

lemma logI_laplace (v : ℝ) (hv : 0 < v) :
    ∑' i : ℕ, (if 0 < i then (i : ℝ) ^ (-(2:ℝ)) * Real.exp (-(2 * v) * (i : ℝ) ^ (-(1:ℝ))) else 0)
      ≤ (2 * v)⁻¹ + (2 * v ^ 2)⁻¹ := by
  have h := lem_app_phase_laplace_i (p := 2) (q := 1) (a := 2 * v) (by norm_num) (by norm_num)
    (by linarith)
  rw [abs_le] at h
  obtain ⟨-, h2⟩ := h
  have e1 : ((2:ℝ) - 1) / 1 = 1 := by norm_num
  have e2 : (2:ℝ) / 1 = 2 := by norm_num
  rw [e1, e2, Real.Gamma_one, Real.rpow_neg_one,
    Real.rpow_neg (by linarith : (0:ℝ) ≤ 2 * v), Real.rpow_two] at h2
  have hX : 0 ≤ ((2 * v) ^ 2)⁻¹ := by positivity
  have hfin : 2 * Mpq 2 1 * ((2 * v) ^ 2)⁻¹ ≤ (2 * v ^ 2)⁻¹ := by
    have e : 2 * ((2 * v) ^ 2)⁻¹ = (2 * v ^ 2)⁻¹ := by
      field_simp
    calc 2 * Mpq 2 1 * ((2 * v) ^ 2)⁻¹ ≤ 2 * 1 * ((2 * v) ^ 2)⁻¹ := by
          gcongr; exact logI_Mpq_le
      _ = (2 * v ^ 2)⁻¹ := by rw [← e]; ring
  linarith

/-- Part (i) of `lem:app-phase-log` (the bound on the kernel at `α = 2`).

`lem:app-phase-log`, snapshot `cr-2026-10-23`. Source: `section.tex` l.2379–2395 (environment).

LaTeX (verbatim, `section.tex` l.2379–2395):
```latex
\begin{lemma}[\SignSVD kernel, $\alpha=2$]\label{lem:app-phase-log}
Let $\alpha=2$, so $q=1$ and $g=2L_{N,2,1}/H_N(1)$.
\begin{enumerate}[label=(\roman*)]
\item For every $v\ge0$,
\[
g(v)\le\frac1{H_N(1)}\Big[\frac1{1+v}+\frac{16}{(1+v)^2}\Big] .
\]
\item For $0<r<1$, $C>0$ and $h(u)=C(1+u)^{-r}$,
\[
\frac{(g*h)(u)}{h(u)}\le\frac{\log(1+u)+A^{\log}_r}{H_N(1)},\qquad A^{\log}_r\defeq2^r\Big(r+\frac1{1-r}\Big)+\frac{16}{1-r} .
\]
\item For $C>0$ and $h(u)=C(1+u)^{-1}$,
\[
\frac{(g*h)(u)}{h(u)}\le\frac{2\log(1+u)+64}{H_N(1)} .
\]
\end{enumerate}
\end{lemma}
``` -/
theorem lem_app_phase_log_i (N : ℕ) (hN : 1 ≤ N) :
    ∀ v : ℝ, 0 ≤ v →
      svdKernel 2 N v ≤ (1 / Hsum 1 N) * (1 / (1 + v) + 16 / (1 + v) ^ 2) := by
  intro v hv
  have hH : 0 < Hsum 1 N := by
    unfold Hsum
    apply Finset.sum_pos
    · intro i hi
      have h1 : 0 < i := (Finset.mem_Icc.mp hi).1
      apply Real.rpow_pos_of_pos
      exact_mod_cast h1
    · exact ⟨1, Finset.mem_Icc.mpr ⟨le_refl _, hN⟩⟩
  have hkern : svdKernel 2 N v = (1 / Hsum 1 N) * (2 * Lsum (N : ℕ∞) 2 1 v) := by
    unfold svdKernel
    have h21 : (2:ℝ) / 2 = 1 := by norm_num
    rw [h21]; ring
  rw [hkern]
  apply mul_le_mul_of_nonneg_left _ (le_of_lt (one_div_pos.mpr hH))
  have hz := lem_app_phase_harmonic_vii
  have hS := logI_Lsum_le_zeta N v hv
  rcases le_total v 1 with h1 | h1
  · have h4 : 4 ≤ 16 / (1 + v) ^ 2 := by
      rw [le_div_iff₀ (by positivity)]; nlinarith
    have : 0 ≤ 1 / (1 + v) := by positivity
    linarith
  · have hv0 : 0 < v := by linarith
    have hST := logI_Lsum_le N v hv
    have hl := logI_laplace v hv0
    have hA : 2 * (2 * v)⁻¹ = v⁻¹ := by field_simp
    have hB : 2 * (2 * v ^ 2)⁻¹ = (v ^ 2)⁻¹ := by field_simp
    have hmain : 2 * Lsum (N : ℕ∞) 2 1 v ≤ v⁻¹ + (v ^ 2)⁻¹ := by linarith
    have hkey : v⁻¹ + (v ^ 2)⁻¹ ≤ 1 / (1 + v) + 16 / (1 + v) ^ 2 := by
      have hv1 : 0 < 1 + v := by linarith
      rw [inv_eq_one_div, inv_eq_one_div, div_add_div _ _ (by positivity) (by positivity),
        div_add_div _ _ (by positivity) (by positivity),
        div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [mul_nonneg (sub_nonneg.mpr h1) hv0.le, mul_nonneg (mul_nonneg (sub_nonneg.mpr h1) hv0.le) hv0.le,
        sq_nonneg v, mul_pos hv0 hv0, mul_pos (mul_pos hv0 hv0) hv0, mul_pos hv0 hv1,
        mul_nonneg (mul_nonneg hv0.le hv0.le) (sub_nonneg.mpr h1)]
    linarith

lemma logIII_alg (U L : ℝ) (hU : 1 ≤ U) (hL0 : 0 ≤ L) (hL1 : L ≤ U - 1) :
    (1 / (U + 1)) * (1 + 16 / (U + 1)) * (2 * L) + 16 / (U + 1) ≤ (2 * L + 64) / U := by
  have hU0 : 0 < U := by linarith
  have hp : 0 < U + 1 := by linarith
  have h1 : U / (U + 1) ≤ 1 := by rw [div_le_one hp]; linarith
  have h2 : 16 / (U + 1) * U ≤ 16 := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hp]; linarith
  have h3 : U * L / (U + 1) ^ 2 ≤ 1 := by
    rw [div_le_iff₀ (by positivity)]; nlinarith
  have key : (1 / (U + 1)) * (1 + 16 / (U + 1)) * (2 * L) + 16 / (U + 1)
      = ((U / (U + 1)) * (2 * L) + 32 * (U * L / (U + 1) ^ 2) + (16 / (U + 1) * U)) / U := by
    field_simp
    ring
  rw [key]
  apply div_le_div_of_nonneg_right _ hU0.le
  nlinarith [mul_nonneg (div_nonneg hU0.le hp.le) hL0]

lemma logIII_int_inv_add (u : ℝ) (hu : 0 ≤ u) :
    ∫ s in (0:ℝ)..u, (1 + s)⁻¹ = Real.log (1 + u) := by
  have hc : ContinuousOn (fun s : ℝ => (1 + s)⁻¹) (Set.uIcc 0 u) := by
    apply ContinuousOn.inv₀ (by fun_prop)
    intro s hs
    rw [Set.uIcc_of_le hu] at hs
    exact (by linarith [hs.1] : (0:ℝ) < 1 + s).ne'
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun s : ℝ => Real.log (1 + s))]
  · simp
  · intro x hx
    rw [Set.uIcc_of_le hu] at hx
    have hx1 : (0:ℝ) < 1 + x := by linarith [hx.1]
    have := ((hasDerivAt_id x).const_add 1).log hx1.ne'
    simpa using this
  · exact hc.intervalIntegrable

lemma logIII_int_inv_sub (u : ℝ) (hu : 0 ≤ u) :
    ∫ s in (0:ℝ)..u, (1 + (u - s))⁻¹ = Real.log (1 + u) := by
  have hc : ContinuousOn (fun s : ℝ => (1 + (u - s))⁻¹) (Set.uIcc 0 u) := by
    apply ContinuousOn.inv₀ (by fun_prop)
    intro s hs
    rw [Set.uIcc_of_le hu] at hs
    exact (by linarith [hs.2] : (0:ℝ) < 1 + (u - s)).ne'
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun s : ℝ => -Real.log (1 + (u - s)))]
  · simp
  · intro x hx
    rw [Set.uIcc_of_le hu] at hx
    have hx1 : (0:ℝ) < 1 + (u - x) := by linarith [hx.2]
    have := (((((hasDerivAt_id x).const_sub u).const_add 1).log hx1.ne').neg)
    exact this.congr_deriv (by simp only [id]; ring)
  · exact hc.intervalIntegrable

lemma logIII_int_sq (u : ℝ) (hu : 0 ≤ u) :
    ∫ s in (0:ℝ)..u, ((1 + s)⁻¹) ^ 2 ≤ 1 := by
  have hc : ContinuousOn (fun s : ℝ => ((1 + s)⁻¹) ^ 2) (Set.uIcc 0 u) := by
    apply ContinuousOn.pow
    apply ContinuousOn.inv₀ (by fun_prop)
    intro s hs
    rw [Set.uIcc_of_le hu] at hs
    exact (by linarith [hs.1] : (0:ℝ) < 1 + s).ne'
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun s : ℝ => -(1 + s)⁻¹)]
  · simp
    have : 0 ≤ (1 + u)⁻¹ := by
      have : (0:ℝ) < 1 + u := by linarith
      positivity
    linarith
  · intro x hx
    rw [Set.uIcc_of_le hu] at hx
    have hx1 : (1 + x) ≠ 0 := (by linarith [hx.1] : (0:ℝ) < 1 + x).ne'
    have := (((hasDerivAt_id x).const_add 1).inv hx1).neg
    exact this.congr_deriv (by simp only [id]; field_simp)
  · exact hc.intervalIntegrable

lemma logIII_K3 (u : ℝ) (hu : 0 ≤ u) :
    ∫ s in (0:ℝ)..u, (1 + (u - s))⁻¹ * (1 / (1 + s) + 16 / (1 + s) ^ 2)
      ≤ (2 * Real.log (1 + u) + 64) / (1 + u) := by
  have hpos : ∀ s ∈ Set.uIcc (0:ℝ) u, (0:ℝ) < 1 + s ∧ (0:ℝ) < 1 + (u - s) := by
    intro s hs
    rw [Set.uIcc_of_le hu] at hs
    exact ⟨by linarith [hs.1], by linarith [hs.2]⟩
  have hI1 : IntervalIntegrable (fun s : ℝ => (1 + s)⁻¹) volume 0 u := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.inv₀ (by fun_prop)
    intro s hs
    exact (hpos s hs).1.ne'
  have hI2 : IntervalIntegrable (fun s : ℝ => (1 + (u - s))⁻¹) volume 0 u := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.inv₀ (by fun_prop)
    intro s hs
    exact (hpos s hs).2.ne'
  have hI3 : IntervalIntegrable (fun s : ℝ => ((1 + s)⁻¹) ^ 2) volume 0 u := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.pow
    apply ContinuousOn.inv₀ (by fun_prop)
    intro s hs
    exact (hpos s hs).1.ne'
  have hid : ∫ s in (0:ℝ)..u, (1 + (u - s))⁻¹ * (1 / (1 + s) + 16 / (1 + s) ^ 2)
      = ∫ s in (0:ℝ)..u, ((1 / (2 + u)) * (1 + 16 / (2 + u))) * ((1 + s)⁻¹ + (1 + (u - s))⁻¹)
        + (16 / (2 + u)) * ((1 + s)⁻¹) ^ 2 := by
    apply intervalIntegral.integral_congr
    intro s hs
    obtain ⟨ha, hb⟩ := hpos s hs
    simp only
    have hab : (2 + u) = (1 + s) + (1 + (u - s)) := by ring
    field_simp
    ring
  have hAint : IntervalIntegrable (fun s : ℝ => ((1 / (2 + u)) * (1 + 16 / (2 + u))) *
      ((1 + s)⁻¹ + (1 + (u - s))⁻¹)) volume 0 u := (hI1.add hI2).const_mul _
  have hBint : IntervalIntegrable (fun s : ℝ => (16 / (2 + u)) * ((1 + s)⁻¹) ^ 2) volume 0 u :=
    hI3.const_mul _
  rw [hid, intervalIntegral.integral_add hAint hBint, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_add hI1 hI2,
    logIII_int_inv_add u hu, logIII_int_inv_sub u hu]
  have hsq := logIII_int_sq u hu
  have hL0 : 0 ≤ Real.log (1 + u) := Real.log_nonneg (by linarith)
  have hL1 : Real.log (1 + u) ≤ (1 + u) - 1 := Real.log_le_sub_one_of_pos (by linarith)
  have halg : (1 / (2 + u)) * (1 + 16 / (2 + u)) * (2 * Real.log (1 + u)) + 16 / (2 + u)
      ≤ (2 * Real.log (1 + u) + 64) / (1 + u) := by
    have := logIII_alg (1 + u) (Real.log (1 + u)) (by linarith) hL0 hL1
    rw [show (1 + u) + 1 = 2 + u by ring] at this
    exact this
  have hB : 0 ≤ 16 / (2 + u) := by positivity
  have hBI : 16 / (2 + u) * (∫ s in (0:ℝ)..u, ((1 + s)⁻¹) ^ 2) ≤ 16 / (2 + u) :=
    mul_le_of_le_one_right hB hsq
  have hsum : ((1 / (2 + u)) * (1 + 16 / (2 + u))) * (Real.log (1 + u) + Real.log (1 + u))
      = (1 / (2 + u)) * (1 + 16 / (2 + u)) * (2 * Real.log (1 + u)) := by ring
  linarith

lemma logII_slope01 (r w : ℝ) (hr0 : 0 < r) (hr1 : r < 1) (hw0 : 0 ≤ w) (hw : w ≤ 1 / 2) :
    (1 - w) ^ (-r) ≤ 1 + 2 * ((2:ℝ) ^ r * r) * w := by
  have h1w : (0:ℝ) < 1 - w := by linarith
  have hlog2 : -Real.log 2 ≤ Real.log (1 - w) := by
    have h := Real.log_le_log (by norm_num : (0:ℝ) < 1 / 2) (by linarith : (1 / 2 : ℝ) ≤ 1 - w)
    rw [one_div, Real.log_inv] at h
    linarith
  have hL2 : -Real.log (1 - w) ≤ 2 * w := by
    have h := Real.one_sub_inv_le_log_of_pos h1w
    have hinv : (1 - w)⁻¹ ≤ 1 + 2 * w := by
      rw [inv_eq_one_div, div_le_iff₀ h1w]
      nlinarith
    linarith
  have hL0 : 0 ≤ -Real.log (1 - w) := by
    have := Real.log_nonpos h1w.le (by linarith : 1 - w ≤ 1)
    linarith
  have hLlog : -Real.log (1 - w) ≤ Real.log 2 := by linarith
  set L := -Real.log (1 - w) with hLdef
  have hpow : (1 - w) ^ (-r) = Real.exp (r * L) := by
    rw [Real.rpow_def_of_pos h1w, hLdef]
    congr 1
    ring
  set y := r * L with hy
  have hy0 : 0 ≤ y := mul_nonneg hr0.le hL0
  set P := (2:ℝ) ^ r with hP
  have hPdef : P = Real.exp (Real.log 2 * r) := by
    rw [hP, Real.rpow_def_of_pos (by norm_num : (0:ℝ) < 2)]
  have hexp_le : Real.exp y ≤ P := by
    rw [hPdef]
    apply Real.exp_le_exp.mpr
    rw [hy]
    nlinarith
  have hsub : Real.exp y - 1 ≤ y * Real.exp y := by
    have h := Real.add_one_le_exp (-y)
    have hE : Real.exp y * Real.exp (-y) = 1 := by rw [← Real.exp_add]; simp
    have := mul_le_mul_of_nonneg_left h (Real.exp_pos y).le
    nlinarith
  have hPpos : 0 ≤ P := by positivity
  rw [hpow]
  have hyL : y ≤ r * (2 * w) := by
    rw [hy]
    exact mul_le_mul_of_nonneg_left hL2 hr0.le
  nlinarith [mul_le_mul_of_nonneg_left hexp_le hy0, mul_le_mul_of_nonneg_left hyL hPpos]

lemma logII_slope_U (u s r : ℝ) (hu : 0 ≤ u) (hr0 : 0 < r) (hr1 : r < 1)
    (hs0 : 0 ≤ s) (hsu : s ≤ u / 2) :
    (1 + (u - s)) ^ (-r) ≤ (1 + u) ^ (-r) * (1 + 2 * ((2:ℝ) ^ r * r) * (s / (1 + u))) := by
  have hU : (0:ℝ) < 1 + u := by linarith
  have e : 1 + (u - s) = (1 + u) * (1 - s / (1 + u)) := by
    field_simp
    ring
  have hw0 : 0 ≤ s / (1 + u) := div_nonneg hs0 hU.le
  have hw : s / (1 + u) ≤ 1 / 2 := by
    rw [div_le_iff₀ hU]
    linarith
  rw [e, Real.mul_rpow hU.le (by linarith [div_le_one_of_le₀ (by linarith : s ≤ 1 + u) hU.le])]
  apply mul_le_mul_of_nonneg_left (logII_slope01 r (s / (1 + u)) hr0 hr1 hw0 hw)
  exact Real.rpow_nonneg hU.le _


lemma logII_partA (u r : ℝ) (hu : 0 ≤ u) (hr0 : 0 < r) (hr1 : r < 1) :
    ∫ s in (0:ℝ)..u / 2, (1 + (u - s)) ^ (-r) * (1 + s)⁻¹
      ≤ (1 + u) ^ (-r) * (Real.log (1 + u) + (2:ℝ) ^ r * r) := by
  have hU : (0:ℝ) < 1 + u := by linarith
  have hu2 : (0:ℝ) ≤ u / 2 := by linarith
  set c := 2 * ((2:ℝ) ^ r * r) with hc
  have hc0 : 0 ≤ c := by positivity
  have hV : 0 ≤ (1 + u) ^ (-r) := Real.rpow_nonneg hU.le _
  have hpt : ∀ s ∈ Set.Icc (0:ℝ) (u / 2),
      (1 + (u - s)) ^ (-r) * (1 + s)⁻¹ ≤ (1 + u) ^ (-r) * ((1 + s)⁻¹ + c / (1 + u)) := by
    intro s hs
    have hs1 : (0:ℝ) < 1 + s := by linarith [hs.1]
    have h1 := logII_slope_U u s r hu hr0 hr1 hs.1 hs.2
    have hsmall : s * (1 + s)⁻¹ ≤ 1 := by
      rw [← div_eq_mul_inv, div_le_one hs1]
      linarith
    have hq : s / (1 + u) * (1 + s)⁻¹ ≤ 1 / (1 + u) := by
      have e : s / (1 + u) * (1 + s)⁻¹ = (s * (1 + s)⁻¹) / (1 + u) := by ring
      rw [e]
      exact div_le_div_of_nonneg_right hsmall hU.le
    calc (1 + (u - s)) ^ (-r) * (1 + s)⁻¹
        ≤ ((1 + u) ^ (-r) * (1 + c * (s / (1 + u)) / 2 * 2)) * (1 + s)⁻¹ := by
          apply mul_le_mul_of_nonneg_right _ (inv_nonneg.mpr hs1.le)
          rw [hc]
          linarith [h1]
      _ = (1 + u) ^ (-r) * ((1 + s)⁻¹ + c * (s / (1 + u) * (1 + s)⁻¹)) := by ring
      _ ≤ (1 + u) ^ (-r) * ((1 + s)⁻¹ + c / (1 + u)) := by
          apply mul_le_mul_of_nonneg_left _ hV
          have : c * (s / (1 + u) * (1 + s)⁻¹) ≤ c * (1 / (1 + u)) :=
            mul_le_mul_of_nonneg_left hq hc0
          have e2 : c * (1 / (1 + u)) = c / (1 + u) := by ring
          linarith
  have hcont1 : ContinuousOn (fun s : ℝ => (1 + (u - s)) ^ (-r) * (1 + s)⁻¹) (Set.uIcc 0 (u / 2)) := by
    apply ContinuousOn.mul
    · apply ContinuousOn.rpow_const (by fun_prop)
      intro s hs
      left
      rw [Set.uIcc_of_le hu2] at hs
      exact (by linarith [hs.2] : (0:ℝ) < 1 + (u - s)).ne'
    · apply ContinuousOn.inv₀ (by fun_prop)
      intro s hs
      rw [Set.uIcc_of_le hu2] at hs
      exact (by linarith [hs.1] : (0:ℝ) < 1 + s).ne'
  have hI1 : IntervalIntegrable (fun s : ℝ => (1 + s)⁻¹) volume 0 (u / 2) := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.inv₀ (by fun_prop)
    intro s hs
    rw [Set.uIcc_of_le hu2] at hs
    exact (by linarith [hs.1] : (0:ℝ) < 1 + s).ne'
  have hmono := intervalIntegral.integral_mono_on hu2 hcont1.intervalIntegrable
    (((hI1.add (intervalIntegrable_const (c := c / (1 + u)))).const_mul ((1 + u) ^ (-r)))) hpt
  refine hmono.trans ?_
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add hI1
    (intervalIntegrable_const), intervalIntegral.integral_const, logIII_int_inv_add (u / 2) hu2]
  have hlog : Real.log (1 + u / 2) ≤ Real.log (1 + u) :=
    Real.log_le_log (by linarith) (by linarith)
  apply mul_le_mul_of_nonneg_left _ hV
  simp only [smul_eq_mul, sub_zero]
  have e : u / 2 * (c / (1 + u)) = c * ((u / 2) / (1 + u)) := by ring
  have hh : (u / 2) / (1 + u) ≤ 1 / 2 := by rw [div_le_iff₀ hU]; linarith
  have h4 : c * ((u / 2) / (1 + u)) ≤ c * (1 / 2) := mul_le_mul_of_nonneg_left hh hc0
  have e3 : c * (1 / 2) = (2:ℝ) ^ r * r := by rw [hc]; ring
  linarith


lemma logII_partB (u r : ℝ) (hu : 0 ≤ u) (hr0 : 0 < r) (hr1 : r < 1) :
    ∫ s in (u / 2)..u, (1 + (u - s)) ^ (-r) * (1 + s)⁻¹
      ≤ (1 + u) ^ (-r) * ((2:ℝ) ^ r / (1 - r)) := by
  have hU : (0:ℝ) < 1 + u := by linarith
  have hu2 : u / 2 ≤ u := by linarith
  have hr1' : (0:ℝ) < 1 - r := by linarith
  have hne : (1 - r) ≠ 0 := hr1'.ne'
  have hK0 : (0:ℝ) < 1 + u / 2 := by linarith
  -- pointwise replacement of (1+s)^{-1} by its maximal value on [u/2, u]
  have hpt : ∀ s ∈ Set.Icc (u / 2) u,
      (1 + (u - s)) ^ (-r) * (1 + s)⁻¹ ≤ (1 + (u - s)) ^ (-r) * (1 + u / 2)⁻¹ := by
    intro s hs
    apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg (by linarith [hs.2]) _)
    exact inv_anti₀ hK0 (by linarith [hs.1])
  have hcont : ContinuousOn (fun s : ℝ => (1 + (u - s)) ^ (-r)) (Set.uIcc (u / 2) u) := by
    apply ContinuousOn.rpow_const (by fun_prop)
    intro s hs
    left
    rw [Set.uIcc_of_le hu2] at hs
    exact (by linarith [hs.2] : (0:ℝ) < 1 + (u - s)).ne'
  have hFTC : ∫ s in (u / 2)..u, (1 + (u - s)) ^ (-r)
      = (-(1 + (u - u)) ^ (1 - r) / (1 - r)) - (-(1 + (u - u / 2)) ^ (1 - r) / (1 - r)) := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun s : ℝ => -(1 + (u - s)) ^ (1 - r) / (1 - r))
    · intro x hx
      rw [Set.uIcc_of_le hu2] at hx
      have hx1 : (0:ℝ) < 1 + (u - x) := by linarith [hx.2]
      have hd := ((((hasDerivAt_id x).const_sub u).const_add 1).rpow_const
        (p := 1 - r) (Or.inl hx1.ne')).neg.div_const (1 - r)
      exact hd.congr_deriv (by
        simp only [id]
        rw [show (1:ℝ) - r - 1 = -r by ring]
        field_simp)
    · exact hcont.intervalIntegrable
  have hX : (0:ℝ) ≤ (1 + u / 2) ^ (1 - r) := Real.rpow_nonneg hK0.le _
  have hval : ∫ s in (u / 2)..u, (1 + (u - s)) ^ (-r) ≤ (1 + u / 2) ^ (1 - r) / (1 - r) := by
    rw [hFTC]
    have e1 : (1:ℝ) + (u - u) = 1 := by ring
    have e2 : (1:ℝ) + (u - u / 2) = 1 + u / 2 := by ring
    rw [e1, e2, Real.one_rpow]
    have h0 : -(1:ℝ) / (1 - r) ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg (by norm_num) hr1'.le
    have e3 : -(-(1 + u / 2) ^ (1 - r) / (1 - r)) = (1 + u / 2) ^ (1 - r) / (1 - r) := by ring
    linarith
  have hcI : ContinuousOn (fun s : ℝ => (1 + s)⁻¹) (Set.uIcc (u / 2) u) := by
    apply ContinuousOn.inv₀ (by fun_prop)
    intro s hs
    rw [Set.uIcc_of_le hu2] at hs
    exact (by linarith [hs.1] : (0:ℝ) < 1 + s).ne'
  have hL : IntervalIntegrable (fun s : ℝ => (1 + (u - s)) ^ (-r) * (1 + s)⁻¹) volume (u / 2) u :=
    (hcont.mul hcI).intervalIntegrable
  have hR : IntervalIntegrable (fun s : ℝ => (1 + (u - s)) ^ (-r) * (1 + u / 2)⁻¹) volume (u / 2) u :=
    (hcont.mul continuousOn_const).intervalIntegrable
  have hmono := intervalIntegral.integral_mono_on hu2 hL hR hpt
  rw [intervalIntegral.integral_mul_const] at hmono
  refine hmono.trans ?_
  have hKX : (1 + u / 2)⁻¹ * (1 + u / 2) ^ (1 - r) = (1 + u / 2) ^ (-r) := by
    rw [show -r = (1 - r) - 1 by ring, Real.rpow_sub_one hK0.ne']
    ring
  have hle : (1 + u / 2) ^ (-r) ≤ (1 + u) ^ (-r) * (2:ℝ) ^ r := by
    have h1 : (1 + u / 2) ^ (-r) ≤ ((1 + u) / 2) ^ (-r) :=
      Real.rpow_le_rpow_of_nonpos (by linarith) (by linarith) (by linarith)
    have h2 : ((1 + u) / 2) ^ (-r) = (1 + u) ^ (-r) * (2:ℝ) ^ r := by
      rw [Real.div_rpow hU.le (by norm_num), Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2), div_inv_eq_mul]
    linarith
  calc (∫ s in (u / 2)..u, (1 + (u - s)) ^ (-r)) * (1 + u / 2)⁻¹
      ≤ (1 + u / 2) ^ (1 - r) / (1 - r) * (1 + u / 2)⁻¹ :=
        mul_le_mul_of_nonneg_right hval (inv_nonneg.mpr hK0.le)
    _ = (1 + u / 2) ^ (-r) / (1 - r) := by rw [← hKX]; ring
    _ ≤ ((1 + u) ^ (-r) * (2:ℝ) ^ r) / (1 - r) := div_le_div_of_nonneg_right hle hr1'.le
    _ = (1 + u) ^ (-r) * ((2:ℝ) ^ r / (1 - r)) := by ring


lemma logII_R2 (u r : ℝ) (hu : 0 ≤ u) (hr0 : 0 < r) (hr1 : r < 1) :
    ∫ s in (0:ℝ)..u, (1 + (u - s)) ^ (-r) * ((1 + s)⁻¹) ^ 2 ≤ (1 + u) ^ (-r) / (1 - r) := by
  have hgc : ContinuousOn (fun v : ℝ => ((1 + v)⁻¹) ^ 2) (Set.Ici 0) := by
    apply ContinuousOn.pow
    apply ContinuousOn.inv₀ (by fun_prop)
    intro x hx
    exact (by linarith [Set.mem_Ici.mp hx] : (0:ℝ) < 1 + x).ne'
  have hgnn : ∀ v ∈ Set.Ici (0:ℝ), 0 ≤ ((1 + v)⁻¹) ^ 2 := fun v _ => by positivity
  have hgm : AntitoneOn (fun v : ℝ => ((1 + v)⁻¹) ^ 2) (Set.Ici 0) := by
    intro a ha b hb hab
    have ha' := Set.mem_Ici.mp ha
    have hb' := Set.mem_Ici.mp hb
    exact pow_le_pow_left₀ (inv_nonneg.mpr (by linarith))
      (inv_anti₀ (by linarith) (by linarith)) 2
  have hm := lem_app_phase_mass (fun v : ℝ => ((1 + v)⁻¹) ^ 2) hgc hgnn hgm 1 1 r
    one_pos one_pos hr0 hr1 u hu
  simp only [div_one, one_mul] at hm
  unfold oneSidedConv at hm
  have hI := logIII_int_sq u hu
  have hU : (0:ℝ) ≤ (1 + u) ^ (-r) := Real.rpow_nonneg (by linarith) _
  have hr1' : (0:ℝ) < 1 - r := by linarith
  calc ∫ s in (0:ℝ)..u, (1 + (u - s)) ^ (-r) * ((1 + s)⁻¹) ^ 2
      ≤ (∫ v in (0:ℝ)..u, ((1 + v)⁻¹) ^ 2) / (1 - r) * (1 + u) ^ (-r) := hm
    _ ≤ 1 / (1 - r) * (1 + u) ^ (-r) :=
        mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hI hr1'.le) hU
    _ = (1 + u) ^ (-r) / (1 - r) := by ring


/-- Part (ii) of `lem:app-phase-log` (`0 < r < 1`).

`lem:app-phase-log`, snapshot `cr-2026-10-23`. Source: `section.tex` l.2379–2395 (environment).

LaTeX (verbatim, `section.tex` l.2379–2395):
```latex
\begin{lemma}[\SignSVD kernel, $\alpha=2$]\label{lem:app-phase-log}
Let $\alpha=2$, so $q=1$ and $g=2L_{N,2,1}/H_N(1)$.
\begin{enumerate}[label=(\roman*)]
\item For every $v\ge0$,
\[
g(v)\le\frac1{H_N(1)}\Big[\frac1{1+v}+\frac{16}{(1+v)^2}\Big] .
\]
\item For $0<r<1$, $C>0$ and $h(u)=C(1+u)^{-r}$,
\[
\frac{(g*h)(u)}{h(u)}\le\frac{\log(1+u)+A^{\log}_r}{H_N(1)},\qquad A^{\log}_r\defeq2^r\Big(r+\frac1{1-r}\Big)+\frac{16}{1-r} .
\]
\item For $C>0$ and $h(u)=C(1+u)^{-1}$,
\[
\frac{(g*h)(u)}{h(u)}\le\frac{2\log(1+u)+64}{H_N(1)} .
\]
\end{enumerate}
\end{lemma}
``` -/
theorem lem_app_phase_log_ii (N : ℕ) (hN : 1 ≤ N) (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1)
    (C : ℝ) (hC : 0 < C) :
    ∀ u : ℝ, 0 ≤ u →
      oneSidedConv (fun w => C * (1 + w) ^ (-r)) (svdKernel 2 N) u / (C * (1 + u) ^ (-r))
        ≤ (Real.log (1 + u) + logAr r) / Hsum 1 N := by
  intro u hu
  have hH : 0 < Hsum 1 N := by
    unfold Hsum
    apply Finset.sum_pos
    · intro i hi
      have h1 : 0 < i := (Finset.mem_Icc.mp hi).1
      apply Real.rpow_pos_of_pos
      exact_mod_cast h1
    · exact ⟨1, Finset.mem_Icc.mpr ⟨le_refl _, hN⟩⟩
  have hkb := lem_app_phase_log_i N hN
  have hK : Continuous (svdKernel 2 N) := svmain_cont 2 N
  have hU : (0:ℝ) < 1 + u := by linarith
  have hV : (0:ℝ) < (1 + u) ^ (-r) := Real.rpow_pos_of_pos hU _
  have hu2 : u / 2 ≤ u := by linarith
  have hnz1 : ∀ s ∈ Set.uIcc (0:ℝ) u, (1 + s) ≠ 0 := by
    intro s hs
    rw [Set.uIcc_of_le hu] at hs
    exact (by linarith [hs.1] : (0:ℝ) < 1 + s).ne'
  have hnz2 : ∀ s ∈ Set.uIcc (0:ℝ) u, (1 + (u - s)) ≠ 0 := by
    intro s hs
    rw [Set.uIcc_of_le hu] at hs
    exact (by linarith [hs.2] : (0:ℝ) < 1 + (u - s)).ne'
  have c1 : ContinuousOn (fun s : ℝ => 1 + s) (Set.uIcc 0 u) := by fun_prop
  have c2 : ContinuousOn (fun s : ℝ => 1 + (u - s)) (Set.uIcc 0 u) := by fun_prop
  have hA : ContinuousOn (fun s : ℝ => 1 / (1 + s)) (Set.uIcc 0 u) :=
    continuousOn_const.div c1 hnz1
  have hA2 : ContinuousOn (fun s : ℝ => 16 / (1 + s) ^ 2) (Set.uIcc 0 u) :=
    continuousOn_const.div (c1.pow 2) (fun s hs => pow_ne_zero 2 (hnz1 s hs))
  have hP : ContinuousOn (fun s : ℝ => (1 + (u - s)) ^ (-r)) (Set.uIcc 0 u) :=
    c2.rpow_const (fun s hs => Or.inl (hnz2 s hs))
  have hcI : ContinuousOn (fun s : ℝ => (1 + s)⁻¹) (Set.uIcc 0 u) :=
    ContinuousOn.inv₀ c1 hnz1
  have hcontR : ContinuousOn (fun s : ℝ =>
      C * (1 + (u - s)) ^ (-r) * ((1 / Hsum 1 N) * (1 / (1 + s) + 16 / (1 + s) ^ 2)))
      (Set.uIcc 0 u) :=
    ContinuousOn.mul (ContinuousOn.mul continuousOn_const hP)
      (continuousOn_const.mul (hA.add hA2))
  have hcontL : ContinuousOn (fun s : ℝ => C * (1 + (u - s)) ^ (-r) * svdKernel 2 N s)
      (Set.uIcc 0 u) :=
    ContinuousOn.mul (continuousOn_const.mul hP) hK.continuousOn
  have hone : oneSidedConv (fun w => C * (1 + w) ^ (-r)) (svdKernel 2 N) u
      ≤ ∫ s in (0:ℝ)..u, C * (1 + (u - s)) ^ (-r) *
          ((1 / Hsum 1 N) * (1 / (1 + s) + 16 / (1 + s) ^ 2)) := by
    unfold oneSidedConv
    apply intervalIntegral.integral_mono_on hu hcontL.intervalIntegrable hcontR.intervalIntegrable
    intro s hs
    have hnn : 0 ≤ C * (1 + (u - s)) ^ (-r) :=
      mul_nonneg hC.le (Real.rpow_nonneg (by linarith [hs.2]) _)
    exact mul_le_mul_of_nonneg_left (hkb s hs.1) hnn
  have hf1 : IntervalIntegrable (fun s : ℝ => (1 + (u - s)) ^ (-r) * (1 + s)⁻¹) volume 0 u :=
    (hP.mul hcI).intervalIntegrable
  have hf2 : IntervalIntegrable (fun s : ℝ => (1 + (u - s)) ^ (-r) * ((1 + s)⁻¹) ^ 2) volume 0 u :=
    (hP.mul (hcI.pow 2)).intervalIntegrable
  have hsplit : ∫ s in (0:ℝ)..u, C * (1 + (u - s)) ^ (-r) *
        ((1 / Hsum 1 N) * (1 / (1 + s) + 16 / (1 + s) ^ 2))
      = (C / Hsum 1 N) * ((∫ s in (0:ℝ)..u, (1 + (u - s)) ^ (-r) * (1 + s)⁻¹)
          + 16 * ∫ s in (0:ℝ)..u, (1 + (u - s)) ^ (-r) * ((1 + s)⁻¹) ^ 2) := by
    have hpt : ∀ s ∈ Set.uIcc (0:ℝ) u,
        C * (1 + (u - s)) ^ (-r) * ((1 / Hsum 1 N) * (1 / (1 + s) + 16 / (1 + s) ^ 2))
          = (C / Hsum 1 N) * ((1 + (u - s)) ^ (-r) * (1 + s)⁻¹
              + 16 * ((1 + (u - s)) ^ (-r) * ((1 + s)⁻¹) ^ 2)) := by
      intro s _
      simp only [one_div, inv_pow]
      ring
    rw [intervalIntegral.integral_congr hpt, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_add hf1 (hf2.const_mul 16), intervalIntegral.integral_const_mul]
  have hI1 : ∫ s in (0:ℝ)..u, (1 + (u - s)) ^ (-r) * (1 + s)⁻¹
      ≤ (1 + u) ^ (-r) * (Real.log (1 + u) + (2:ℝ) ^ r * (r + 1 / (1 - r))) := by
    have hs1 : IntervalIntegrable (fun s : ℝ => (1 + (u - s)) ^ (-r) * (1 + s)⁻¹) volume 0 (u / 2) :=
      hf1.mono_set (Set.uIcc_subset_uIcc Set.left_mem_uIcc
        (Set.mem_uIcc.mpr (Or.inl ⟨by linarith, hu2⟩)))
    have hs2 : IntervalIntegrable (fun s : ℝ => (1 + (u - s)) ^ (-r) * (1 + s)⁻¹) volume (u / 2) u :=
      hf1.mono_set (Set.uIcc_subset_uIcc (Set.mem_uIcc.mpr (Or.inl ⟨by linarith, hu2⟩))
        Set.right_mem_uIcc)
    rw [← intervalIntegral.integral_add_adjacent_intervals hs1 hs2]
    have pA := logII_partA u r hu hr0 hr1
    have pB := logII_partB u r hu hr0 hr1
    have e : (1 + u) ^ (-r) * (Real.log (1 + u) + (2:ℝ) ^ r * (r + 1 / (1 - r)))
        = (1 + u) ^ (-r) * (Real.log (1 + u) + (2:ℝ) ^ r * r)
          + (1 + u) ^ (-r) * ((2:ℝ) ^ r / (1 - r)) := by ring
    rw [e]
    linarith
  have hI2 := logII_R2 u r hu hr0 hr1
  have hH' : (0:ℝ) < C / Hsum 1 N := div_pos hC hH
  rw [div_le_iff₀ (mul_pos hC hV)]
  calc oneSidedConv (fun w => C * (1 + w) ^ (-r)) (svdKernel 2 N) u
      ≤ ∫ s in (0:ℝ)..u, C * (1 + (u - s)) ^ (-r) *
          ((1 / Hsum 1 N) * (1 / (1 + s) + 16 / (1 + s) ^ 2)) := hone
    _ = (C / Hsum 1 N) * ((∫ s in (0:ℝ)..u, (1 + (u - s)) ^ (-r) * (1 + s)⁻¹)
          + 16 * ∫ s in (0:ℝ)..u, (1 + (u - s)) ^ (-r) * ((1 + s)⁻¹) ^ 2) := hsplit
    _ ≤ (C / Hsum 1 N) * ((1 + u) ^ (-r) * (Real.log (1 + u) + (2:ℝ) ^ r * (r + 1 / (1 - r)))
          + 16 * ((1 + u) ^ (-r) / (1 - r))) :=
        mul_le_mul_of_nonneg_left (by linarith) hH'.le
    _ = (Real.log (1 + u) + logAr r) / Hsum 1 N * (C * (1 + u) ^ (-r)) := by
        unfold logAr
        ring

/-- Part (iii) of `lem:app-phase-log` (`h(u) = C(1+u)^{-1}`).

`lem:app-phase-log`, snapshot `cr-2026-10-23`. Source: `section.tex` l.2379–2395 (environment).

LaTeX (verbatim, `section.tex` l.2379–2395):
```latex
\begin{lemma}[\SignSVD kernel, $\alpha=2$]\label{lem:app-phase-log}
Let $\alpha=2$, so $q=1$ and $g=2L_{N,2,1}/H_N(1)$.
\begin{enumerate}[label=(\roman*)]
\item For every $v\ge0$,
\[
g(v)\le\frac1{H_N(1)}\Big[\frac1{1+v}+\frac{16}{(1+v)^2}\Big] .
\]
\item For $0<r<1$, $C>0$ and $h(u)=C(1+u)^{-r}$,
\[
\frac{(g*h)(u)}{h(u)}\le\frac{\log(1+u)+A^{\log}_r}{H_N(1)},\qquad A^{\log}_r\defeq2^r\Big(r+\frac1{1-r}\Big)+\frac{16}{1-r} .
\]
\item For $C>0$ and $h(u)=C(1+u)^{-1}$,
\[
\frac{(g*h)(u)}{h(u)}\le\frac{2\log(1+u)+64}{H_N(1)} .
\]
\end{enumerate}
\end{lemma}
``` -/
theorem lem_app_phase_log_iii (N : ℕ) (hN : 1 ≤ N) (C : ℝ) (hC : 0 < C) :
    ∀ u : ℝ, 0 ≤ u →
      oneSidedConv (fun w => C * (1 + w) ^ (-(1 : ℝ))) (svdKernel 2 N) u
          / (C * (1 + u) ^ (-(1 : ℝ)))
        ≤ (2 * Real.log (1 + u) + 64) / Hsum 1 N := by
  intro u hu
  have hH : 0 < Hsum 1 N := by
    unfold Hsum
    apply Finset.sum_pos
    · intro i hi
      have h1 : 0 < i := (Finset.mem_Icc.mp hi).1
      apply Real.rpow_pos_of_pos
      exact_mod_cast h1
    · exact ⟨1, Finset.mem_Icc.mpr ⟨le_refl _, hN⟩⟩
  have hkb := lem_app_phase_log_i N hN
  have hK : Continuous (svdKernel 2 N) := svmain_cont 2 N
  have hU : 0 < 1 + u := by linarith
  have hnz1 : ∀ s ∈ Set.uIcc (0:ℝ) u, (1 + s) ≠ 0 := by
    intro s hs
    rw [Set.uIcc_of_le hu] at hs
    exact (by linarith [hs.1] : (0:ℝ) < 1 + s).ne'
  have hnz2 : ∀ s ∈ Set.uIcc (0:ℝ) u, (1 + (u - s)) ≠ 0 := by
    intro s hs
    rw [Set.uIcc_of_le hu] at hs
    exact (by linarith [hs.2] : (0:ℝ) < 1 + (u - s)).ne'
  have c1 : ContinuousOn (fun s : ℝ => 1 + s) (Set.uIcc 0 u) := by fun_prop
  have c2 : ContinuousOn (fun s : ℝ => 1 + (u - s)) (Set.uIcc 0 u) := by fun_prop
  have hA : ContinuousOn (fun s : ℝ => 1 / (1 + s)) (Set.uIcc 0 u) :=
    continuousOn_const.div c1 hnz1
  have hA2 : ContinuousOn (fun s : ℝ => 16 / (1 + s) ^ 2) (Set.uIcc 0 u) :=
    continuousOn_const.div (c1.pow 2) (fun s hs => pow_ne_zero 2 (hnz1 s hs))
  have hcontR : ContinuousOn (fun s : ℝ =>
      C * (1 + (u - s))⁻¹ * ((1 / Hsum 1 N) * (1 / (1 + s) + 16 / (1 + s) ^ 2))) (Set.uIcc 0 u) :=
    ContinuousOn.mul (ContinuousOn.mul continuousOn_const (c2.inv₀ hnz2))
      (continuousOn_const.mul (hA.add hA2))
  have hcontL : ContinuousOn (fun s : ℝ => C * (1 + (u - s))⁻¹ * svdKernel 2 N s)
      (Set.uIcc 0 u) :=
    ContinuousOn.mul (continuousOn_const.mul (c2.inv₀ hnz2)) hK.continuousOn
  have hone : oneSidedConv (fun w => C * (1 + w)⁻¹) (svdKernel 2 N) u
      ≤ (C / Hsum 1 N) * ((2 * Real.log (1 + u) + 64) / (1 + u)) := by
    unfold oneSidedConv
    calc ∫ s in (0:ℝ)..u, (fun w => C * (1 + w)⁻¹) (u - s) * svdKernel 2 N s
        ≤ ∫ s in (0:ℝ)..u, C * (1 + (u - s))⁻¹ *
            ((1 / Hsum 1 N) * (1 / (1 + s) + 16 / (1 + s) ^ 2)) := by
          apply intervalIntegral.integral_mono_on hu
          · exact hcontL.intervalIntegrable
          · exact hcontR.intervalIntegrable
          · intro s hs
            have hnn : 0 ≤ C * (1 + (u - s))⁻¹ :=
              mul_nonneg hC.le (inv_nonneg.mpr (by linarith [hs.2]))
            exact mul_le_mul_of_nonneg_left (hkb s hs.1) hnn
      _ = (C / Hsum 1 N) * ∫ s in (0:ℝ)..u,
            (1 + (u - s))⁻¹ * (1 / (1 + s) + 16 / (1 + s) ^ 2) := by
          rw [← intervalIntegral.integral_const_mul]
          apply intervalIntegral.integral_congr
          intro s _
          ring
      _ ≤ (C / Hsum 1 N) * ((2 * Real.log (1 + u) + 64) / (1 + u)) :=
          mul_le_mul_of_nonneg_left (logIII_K3 u hu) (div_pos hC hH).le
  have hden : 0 < C * (1 + u)⁻¹ := mul_pos hC (inv_pos.mpr hU)
  simp only [Real.rpow_neg_one]
  rw [div_le_iff₀ hden]
  calc oneSidedConv (fun w => C * (1 + w)⁻¹) (svdKernel 2 N) u
      ≤ (C / Hsum 1 N) * ((2 * Real.log (1 + u) + 64) / (1 + u)) := hone
    _ = (2 * Real.log (1 + u) + 64) / Hsum 1 N * (C * (1 + u)⁻¹) := by ring


/-! ### Proof helpers for `lem:app-phase-log-global` (P-H.7.P5): convolution bounds -/

lemma lg_conv_const_mul (f g : ℝ → ℝ) (c t : ℝ) :
    oneSidedConv f (fun s => c * g s) t = c * oneSidedConv f g t := by
  unfold oneSidedConv
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro s _
  simp only
  ring

lemma lg_conv_ii (f g : ℝ → ℝ) (u : ℝ) (hu : 0 ≤ u)
    (hf : ContinuousOn f (Ici 0)) (hg : ContinuousOn g (Ici 0)) :
    IntervalIntegrable (fun s => f (u - s) * g s) volume 0 u := by
  apply ContinuousOn.intervalIntegrable
  rw [uIcc_of_le hu]
  have h1 : ContinuousOn (fun s => f (u - s)) (Icc 0 u) := by
    refine hf.comp (by fun_prop) ?_
    intro s hs
    exact sub_nonneg.2 hs.2
  exact h1.mul (hg.mono (fun s hs => hs.1))

lemma lg_conv_add3 (f1 f2 g : ℝ → ℝ) (c u : ℝ) (hu : 0 ≤ u)
    (h1 : ContinuousOn f1 (Ici 0)) (h2 : ContinuousOn f2 (Ici 0)) (hg : ContinuousOn g (Ici 0)) :
    oneSidedConv (fun v => f1 v + f2 v + c) g u
      = oneSidedConv f1 g u + oneSidedConv f2 g u + c * ∫ s in (0:ℝ)..u, g s := by
  have i1 := lg_conv_ii f1 g u hu h1 hg
  have i2 := lg_conv_ii f2 g u hu h2 hg
  have i3 : IntervalIntegrable (fun s => c * g s) volume 0 u :=
    (ContinuousOn.intervalIntegrable (by
      rw [uIcc_of_le hu]; exact continuousOn_const.mul (hg.mono (fun s hs => hs.1)))) 
  unfold oneSidedConv
  have : ∀ s, (f1 (u - s) + f2 (u - s) + c) * g s
      = f1 (u - s) * g s + f2 (u - s) * g s + c * g s := fun s => by ring
  simp_rw [this]
  rw [intervalIntegral.integral_add (i1.add i2) i3, intervalIntegral.integral_add i1 i2,
    intervalIntegral.integral_const_mul]

theorem lg_upper (ε : ℝ) (hε : 0 < ε) (f g h w Yf : ℝ → ℝ)
    (hg_cont : ContinuousOn g (Ici 0)) (hg_nn : ∀ s, 0 ≤ s → 0 ≤ g s)
    (hg_mass : ∀ x, 0 ≤ x → ∫ s in (0:ℝ)..x, g s ≤ 1)
    (hh_cont : ContinuousOn h (Ici 0)) (hh_nn : ∀ s, 0 ≤ s → 0 ≤ h s)
    (hw_cont : ContinuousOn w (Ici 0)) (hw_nn : ∀ s, 0 ≤ s → 0 ≤ w s)
    (hf_cont : ContinuousOn f (Ici 0)) (hf_nn : ∀ s, 0 ≤ s → 0 ≤ f s)
    (hfh : ∀ s, 0 ≤ s → f s ≤ h s ^ 2)
    (hY_cont : ContinuousOn Yf (Ici 0)) (hY_nn : ∀ s, 0 ≤ s → 0 ≤ Yf s)
    (hY : ∀ s, 0 ≤ s → Yf s = f s + Real.sqrt ε * oneSidedConv (fun v => Real.sqrt (Yf v)) g s)
    (hconvh : ∀ s, 0 ≤ s → Real.sqrt ε * oneSidedConv h g s ≤ w s ^ 2)
    (hconvw : ∀ s, 0 ≤ s → oneSidedConv w g s ≤ 2 * w s) :
    ∀ u, 0 ≤ u → Yf u ≤ (h u + w u + Real.sqrt ε) ^ 2 := by
  intro u hu
  have hse : 0 < Real.sqrt ε := Real.sqrt_pos.2 hε
  have hse2 : Real.sqrt ε ^ 2 = ε := Real.sq_sqrt hε.le
  set S' : ℝ := u + 1 with hS'
  have hS'pos : 0 < S' := by linarith
  have hsub : Icc (0:ℝ) S' ⊆ Ici 0 := fun s hs => hs.1
  have key := lem_app_phase_comparison S' hS'pos (fun s => Real.sqrt ε * g s)
    (fun s hs => mul_nonneg hse.le (hg_nn s hs.1.le))
    (by
      have : IntegrableOn g (Ioo 0 S') := by
        have : ContinuousOn g (Icc 0 S') := hg_cont.mono hsub
        exact (this.integrableOn_Icc).mono_set Ioo_subset_Icc_self
      exact this.const_mul _)
    f (hf_cont.mono hsub) (fun s hs => hf_nn s hs.1)
    ε hε Yf (fun s => (h s + w s + Real.sqrt ε) ^ 2) (hY_cont.mono hsub) (fun s hs => hY_nn s hs.1)
    (by
      have : ContinuousOn (fun s => h s + w s + Real.sqrt ε) (Icc 0 S') :=
        ((hh_cont.mono hsub).add (hw_cont.mono hsub)).add continuousOn_const
      exact this.pow 2)
    (fun s hs => sq_nonneg _)
    (fun s hs => by
      have := hh_nn s hs.1; have := hw_nn s hs.1
      nlinarith [hse2, mul_nonneg ‹0 ≤ h s› ‹0 ≤ w s›, mul_nonneg ‹0 ≤ h s› hse.le,
        mul_nonneg ‹0 ≤ w s› hse.le, sq_nonneg (h s), sq_nonneg (w s)])
    (fun s hs => by
      rw [lg_conv_const_mul, hY s hs.1])
    (fun s hs => by
      have hs0 := hs.1
      have e : oneSidedConv (fun v => Real.sqrt ((h v + w v + Real.sqrt ε) ^ 2)) (fun s => Real.sqrt ε * g s) s
          = oneSidedConv (fun v => h v + w v + Real.sqrt ε) (fun s => Real.sqrt ε * g s) s := by
        unfold oneSidedConv
        apply intervalIntegral.integral_congr
        intro t ht
        rw [uIcc_of_le hs0] at ht
        have h1 := hh_nn (s - t) (by linarith [ht.2]); have h2 := hw_nn (s - t) (by linarith [ht.2])
        simp only
        rw [Real.sqrt_sq (by positivity)]
      rw [e, lg_conv_const_mul, lg_conv_add3 h w g (Real.sqrt ε) s hs0 hh_cont hw_cont hg_cont]
      have c1 := hconvh s hs0
      have c2 := hconvw s hs0
      have c3 := hg_mass s hs0
      have f1 := hfh s hs0
      have h1 := hh_nn s hs0; have h2 := hw_nn s hs0
      have q : Real.sqrt ε * (Real.sqrt ε * ∫ t in (0:ℝ)..s, g t) ≤ ε := by
        calc _ ≤ Real.sqrt ε * (Real.sqrt ε * 1) := by gcongr
          _ = ε := by nlinarith [hse2]
      nlinarith [mul_le_mul_of_nonneg_left c2 hse.le, mul_nonneg h1 h2, mul_nonneg h1 hse.le])
  exact key u ⟨hu, by linarith⟩


lemma lg_ipow (r a b : ℝ) (hr : r ≠ 1) (ha : 0 ≤ a) (hab : a ≤ b) :
    ∫ z in a..b, (1 + z) ^ (-r) = ((1 + b) ^ (1 - r) - (1 + a) ^ (1 - r)) / (1 - r) := by
  have h1r : (1 - r) ≠ 0 := sub_ne_zero.2 (Ne.symm hr)
  have hd : ∀ z ∈ uIcc a b, HasDerivAt (fun z : ℝ => (1 + z) ^ (1 - r) / (1 - r)) ((1 + z) ^ (-r)) z := by
    intro z hz
    rw [uIcc_of_le hab] at hz
    have hz0 : 0 < 1 + z := by linarith [hz.1]
    have h1 : HasDerivAt (fun z : ℝ => 1 + z) 1 z := (hasDerivAt_id z).const_add 1
    have h2 := (h1.rpow_const (p := 1 - r) (Or.inl hz0.ne')).div_const (1 - r)
    convert h2 using 1
    rw [show (1 - r - 1) = -r by ring]
    field_simp
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd]
  · ring
  · apply ContinuousOn.intervalIntegrable
    intro z hz
    rw [uIcc_of_le hab] at hz
    have hz0 : 0 < 1 + z := by linarith [hz.1]
    exact (Real.continuousAt_rpow_const _ _ (Or.inl hz0.ne')).comp_continuousWithinAt
      (by fun_prop : ContinuousWithinAt (fun z : ℝ => 1 + z) _ z)

lemma lg_ilog (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) :
    ∫ z in a..b, (1 + z)⁻¹ = Real.log (1 + b) - Real.log (1 + a) := by
  have hd : ∀ z ∈ uIcc a b, HasDerivAt (fun z : ℝ => Real.log (1 + z)) ((1 + z)⁻¹) z := by
    intro z hz
    rw [uIcc_of_le hab] at hz
    have hz0 : 0 < 1 + z := by linarith [hz.1]
    have h1 : HasDerivAt (fun z : ℝ => 1 + z) 1 z := (hasDerivAt_id z).const_add 1
    have h2 := h1.log hz0.ne'
    simpa using h2
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd]
  apply ContinuousOn.intervalIntegrable
  intro z hz
  rw [uIcc_of_le hab] at hz
  have hz0 : 0 < 1 + z := by linarith [hz.1]
  exact (continuousAt_inv₀ hz0.ne').comp_continuousWithinAt
      (by fun_prop : ContinuousWithinAt (fun z : ℝ => 1 + z) _ z)

lemma lg_log_rpow (x r : ℝ) (hx : 1 ≤ x) (hr : 1 < r) :
    Real.log x ≤ x ^ (r - 1) / (Real.exp 1 * (r - 1)) := by
  have hx0 : 0 < x := by linarith
  have hr1 : 0 < r - 1 := by linarith
  have hy : 0 < x ^ (r - 1) := Real.rpow_pos_of_pos hx0 _
  have h := Real.log_le_sub_one_of_pos (div_pos hy (Real.exp_pos 1))
  rw [Real.log_div hy.ne' (Real.exp_pos 1).ne', Real.log_rpow hx0, Real.log_exp] at h
  rw [le_div_iff₀ (mul_pos (Real.exp_pos 1) hr1)]
  have : x ^ (r - 1) / Real.exp 1 ≤ x ^ (r - 1) / Real.exp 1 := le_rfl
  have h2 : (r - 1) * Real.log x ≤ x ^ (r - 1) / Real.exp 1 := by linarith
  calc Real.log x * (Real.exp 1 * (r - 1)) = Real.exp 1 * ((r - 1) * Real.log x) := by ring
    _ ≤ Real.exp 1 * (x ^ (r - 1) / Real.exp 1) := by gcongr
    _ = x ^ (r - 1) := by field_simp


lemma lg_split (F g : ℝ → ℝ) (u : ℝ) (hu : 0 ≤ u)
    (hF : ContinuousOn F (Ici 0)) (hg : ContinuousOn g (Ici 0)) :
    oneSidedConv F g u = (∫ s in (0:ℝ)..(u / 2), F (u - s) * g s)
      + ∫ s in (u / 2)..u, F (u - s) * g s := by
  have ii := lg_conv_ii F g u hu hF hg
  unfold oneSidedConv
  rw [intervalIntegral.integral_add_adjacent_intervals]
  · exact ii.mono_set (by rw [uIcc_of_le hu, uIcc_of_le (by linarith)]; exact Icc_subset_Icc le_rfl (by linarith))
  · exact ii.mono_set (by rw [uIcc_of_le hu, uIcc_of_le (by linarith)]; exact Icc_subset_Icc (by linarith) le_rfl)

lemma lg_half_pow (u s r : ℝ) (hu : 0 ≤ u) (hs0 : 0 ≤ s) (hs : s ≤ u / 2) (hr : 0 ≤ r) :
    (1 + (u - s)) ^ (-r) ≤ (2 : ℝ) ^ r * (1 + u) ^ (-r) := by
  have h1 : (1 + u) / 2 ≤ 1 + (u - s) := by linarith
  have h2 : ((1 + u) / 2) ^ (-r) = (2 : ℝ) ^ r * (1 + u) ^ (-r) := by
    rw [Real.div_rpow (by linarith) (by norm_num), Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2),
      Real.rpow_neg (by linarith : (0:ℝ) ≤ 1 + u)]
    field_simp
  rw [← h2]
  exact Real.rpow_le_rpow_of_nonpos (by linarith) h1 (by linarith)

theorem lg_convh (r C K L : ℝ) (hr : 1 < r) (hC : 0 < C) (hK : 0 ≤ K) (hL : 0 < L)
    (g : ℝ → ℝ) (hg_cont : ContinuousOn g (Ici 0)) (hg_nn : ∀ s, 0 ≤ s → 0 ≤ g s)
    (hgb : ∀ s, 0 ≤ s → g s ≤ K / (L * (1 + s))) (u : ℝ) (hu : 0 ≤ u) :
    oneSidedConv (fun x => C * (1 + x) ^ (-r)) g u
      ≤ C * K / (r - 1) * ((2 : ℝ) ^ r / Real.exp 1 + 2) / (L * (1 + u)) := by
  have hr1 : 0 < r - 1 := by linarith
  have hu1 : 0 < 1 + u := by linarith
  have hcont : ContinuousOn (fun x => C * (1 + x) ^ (-r)) (Ici 0) := by
    apply ContinuousOn.mul continuousOn_const
    intro z hz
    have hz0 : 0 < 1 + (z:ℝ) := by have := hz.out; linarith
    exact (Real.continuousAt_rpow_const _ _ (Or.inl hz0.ne')).comp_continuousWithinAt
      (by fun_prop : ContinuousWithinAt (fun z : ℝ => 1 + z) _ z)
  rw [lg_split _ g u hu hcont hg_cont]
  -- part 1
  have P1 : ∫ s in (0:ℝ)..(u / 2), C * (1 + (u - s)) ^ (-r) * g s
      ≤ (C * (2 : ℝ) ^ r * (1 + u) ^ (-r) * (K / L)) * Real.log (1 + u) := by
    have hmono : ∫ s in (0:ℝ)..(u / 2), C * (1 + (u - s)) ^ (-r) * g s
        ≤ ∫ s in (0:ℝ)..(u / 2), (C * (2 : ℝ) ^ r * (1 + u) ^ (-r) * (K / L)) * (1 + s)⁻¹ := by
      apply intervalIntegral.integral_mono_on (by linarith)
      · have := lg_conv_ii (fun x => C * (1 + x) ^ (-r)) g u hu hcont hg_cont
        exact this.mono_set (by rw [uIcc_of_le hu, uIcc_of_le (by linarith)]; exact Icc_subset_Icc le_rfl (by linarith))
      · apply ContinuousOn.intervalIntegrable
        apply ContinuousOn.mul continuousOn_const
        intro z hz
        rw [uIcc_of_le (by linarith)] at hz
        exact (continuousAt_inv₀ (by linarith [hz.1] : (1 + z) ≠ 0)).comp_continuousWithinAt
          (by fun_prop : ContinuousWithinAt (fun z : ℝ => 1 + z) _ z)
      · intro s hs
        have hs0 := hs.1
        have e1 := lg_half_pow u s r hu hs.1 hs.2 (by linarith)
        have e2 := hgb s hs0
        have hpos : 0 ≤ (1 + (u - s)) ^ (-r) := Real.rpow_nonneg (by linarith [hs.2]) _
        have e3 : g s ≤ K / L * (1 + s)⁻¹ := by
          calc g s ≤ K / (L * (1 + s)) := e2
            _ = K / L * (1 + s)⁻¹ := by rw [div_mul_eq_div_div, div_eq_mul_inv]
        calc C * (1 + (u - s)) ^ (-r) * g s
            ≤ (C * ((2 : ℝ) ^ r * (1 + u) ^ (-r))) * (K / L * (1 + s)⁻¹) := by
              apply mul_le_mul (by gcongr) e3 (hg_nn s hs0) (by positivity)
          _ = _ := by ring
    refine hmono.trans ?_
    rw [intervalIntegral.integral_const_mul, lg_ilog 0 (u / 2) le_rfl (by linarith)]
    simp only [add_zero, Real.log_one, sub_zero]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact Real.log_le_log (by linarith) (by linarith)
  -- part 2
  have P2 : ∫ s in (u / 2)..u, C * (1 + (u - s)) ^ (-r) * g s
      ≤ (2 * K / (L * (1 + u))) * (C / (r - 1)) := by
    have hI : ∫ s in (u / 2)..u, C * (1 + (u - s)) ^ (-r) = C * (((1 + u / 2) ^ (1 - r) - 1) / (1 - r)) := by
      have h1 := intervalIntegral.integral_comp_sub_left (a := u / 2) (b := u)
        (fun x : ℝ => C * (1 + x) ^ (-r)) u
      rw [h1, sub_self, show u - u / 2 = u / 2 by ring, intervalIntegral.integral_const_mul,
        lg_ipow r 0 (u / 2) hr.ne' le_rfl (by linarith)]
      simp
    have hmono : ∫ s in (u / 2)..u, C * (1 + (u - s)) ^ (-r) * g s
        ≤ ∫ s in (u / 2)..u, (C * (1 + (u - s)) ^ (-r)) * (2 * K / (L * (1 + u))) := by
      have hcI : ContinuousOn (fun s : ℝ => C * (1 + (u - s)) ^ (-r)) (uIcc (u / 2) u) := by
        rw [uIcc_of_le (by linarith)]
        apply ContinuousOn.mul continuousOn_const
        intro z hz
        have hz0 : 0 < 1 + (u - z) := by linarith [hz.2]
        exact (Real.continuousAt_rpow_const (1 + (u - z)) (-r) (Or.inl hz0.ne')).comp_continuousWithinAt
          (f := fun z : ℝ => 1 + (u - z)) (by fun_prop)
      apply intervalIntegral.integral_mono_on (by linarith)
      · have := lg_conv_ii (fun x => C * (1 + x) ^ (-r)) g u hu hcont hg_cont
        exact this.mono_set (by rw [uIcc_of_le hu, uIcc_of_le (by linarith)]; exact Icc_subset_Icc (by linarith) le_rfl)
      · exact (hcI.mul continuousOn_const).intervalIntegrable
      · intro s hs
        have hs0 : 0 ≤ s := by linarith [hs.1]
        have e2 := hgb s hs0
        have e3 : g s ≤ 2 * K / (L * (1 + u)) := by
          refine e2.trans ?_
          rw [div_le_div_iff₀ (by positivity) (by positivity)]
          nlinarith [mul_nonneg (mul_nonneg hK hL.le) (show 0 ≤ 2 * (1 + s) - (1 + u) by linarith [hs.1])]
        have hpos : 0 ≤ C * (1 + (u - s)) ^ (-r) := mul_nonneg hC.le (Real.rpow_nonneg (by linarith [hs.2]) _)
        exact mul_le_mul_of_nonneg_left e3 hpos
    refine hmono.trans ?_
    rw [intervalIntegral.integral_mul_const, hI]
    have hpow : 0 ≤ (1 + u / 2) ^ (1 - r) := Real.rpow_nonneg (by linarith) _
    have hnum : C * (((1 + u / 2) ^ (1 - r) - 1) / (1 - r)) ≤ C / (r - 1) := by
      have e : ((1 + u / 2) ^ (1 - r) - 1) / (1 - r) = (1 - (1 + u / 2) ^ (1 - r)) / (r - 1) := by
        rw [show (1 - r) = -(r - 1) by ring, div_neg, ← neg_div]; ring_nf
      rw [e, ← mul_div_assoc]
      apply div_le_div_of_nonneg_right _ hr1.le
      nlinarith
    have hM : 0 ≤ 2 * K / (L * (1 + u)) := by positivity
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_left hnum hM
  -- combine
  have hlog : (1 + u) ^ (-r) * Real.log (1 + u) ≤ (1 + u)⁻¹ / (Real.exp 1 * (r - 1)) := by
    have := lg_log_rpow (1 + u) r (by linarith) hr
    calc (1 + u) ^ (-r) * Real.log (1 + u) ≤ (1 + u) ^ (-r) * ((1 + u) ^ (r - 1) / (Real.exp 1 * (r - 1))) := by
          gcongr
      _ = (1 + u)⁻¹ / (Real.exp 1 * (r - 1)) := by
          rw [← mul_div_assoc, ← Real.rpow_add hu1, show -r + (r - 1) = -1 by ring, Real.rpow_neg_one]
  have hfin : (C * (2 : ℝ) ^ r * (1 + u) ^ (-r) * (K / L)) * Real.log (1 + u)
      ≤ C * K * (2 : ℝ) ^ r / (Real.exp 1 * (r - 1)) / (L * (1 + u)) := by
    have : (C * (2 : ℝ) ^ r * (1 + u) ^ (-r) * (K / L)) * Real.log (1 + u)
        = (C * (2 : ℝ) ^ r * (K / L)) * ((1 + u) ^ (-r) * Real.log (1 + u)) := by ring
    rw [this]
    calc _ ≤ (C * (2 : ℝ) ^ r * (K / L)) * ((1 + u)⁻¹ / (Real.exp 1 * (r - 1))) := by
          apply mul_le_mul_of_nonneg_left hlog (by positivity)
      _ = _ := by field_simp
  have hE : C * K / (r - 1) * ((2 : ℝ) ^ r / Real.exp 1 + 2) / (L * (1 + u))
      = C * K * (2 : ℝ) ^ r / (Real.exp 1 * (r - 1)) / (L * (1 + u))
        + (2 * K / (L * (1 + u))) * (C / (r - 1)) := by
    field_simp
  rw [hE]
  exact add_le_add (P1.trans hfin) P2


theorem lg_convw (c K L : ℝ) (hc : 0 ≤ c) (hK : 0 ≤ K) (hL : 0 < L)
    (g : ℝ → ℝ) (hg_cont : ContinuousOn g (Ici 0)) (hg_nn : ∀ s, 0 ≤ s → 0 ≤ g s)
    (hgb : ∀ s, 0 ≤ s → g s ≤ K / (L * (1 + s)))
    (hmass : ∀ x, 0 ≤ x → ∫ s in (0:ℝ)..x, g s ≤ 1) (u : ℝ) (hu : 0 ≤ u) :
    oneSidedConv (fun x => c * (1 + x) ^ (-(1 / 2 : ℝ))) g u
      ≤ ((2 : ℝ) ^ (1 / 2 : ℝ) + 4 * K / L) * (c * (1 + u) ^ (-(1 / 2 : ℝ))) := by
  have hu1 : 0 < 1 + u := by linarith
  have hcont : ContinuousOn (fun x => c * (1 + x) ^ (-(1 / 2 : ℝ))) (Ici 0) := by
    apply ContinuousOn.mul continuousOn_const
    intro z hz
    have hz0 : 0 < 1 + (z:ℝ) := by have := hz.out; linarith
    exact (Real.continuousAt_rpow_const _ _ (Or.inl hz0.ne')).comp_continuousWithinAt
      (by fun_prop : ContinuousWithinAt (fun z : ℝ => 1 + z) _ z)
  rw [lg_split _ g u hu hcont hg_cont]
  have hgi : IntervalIntegrable g volume 0 u :=
    (hg_cont.mono (fun s hs => by
      rw [uIcc_of_le hu] at hs; exact hs.1)).intervalIntegrable
  have P1 : ∫ s in (0:ℝ)..(u / 2), c * (1 + (u - s)) ^ (-(1 / 2 : ℝ)) * g s
      ≤ (2 : ℝ) ^ (1 / 2 : ℝ) * (c * (1 + u) ^ (-(1 / 2 : ℝ))) := by
    have hmono : ∫ s in (0:ℝ)..(u / 2), c * (1 + (u - s)) ^ (-(1 / 2 : ℝ)) * g s
        ≤ ∫ s in (0:ℝ)..(u / 2), (c * ((2 : ℝ) ^ (1 / 2 : ℝ) * (1 + u) ^ (-(1 / 2 : ℝ)))) * g s := by
      apply intervalIntegral.integral_mono_on (by linarith)
      · have := lg_conv_ii (fun x => c * (1 + x) ^ (-(1 / 2 : ℝ))) g u hu hcont hg_cont
        exact this.mono_set (by rw [uIcc_of_le hu, uIcc_of_le (by linarith)]; exact Icc_subset_Icc le_rfl (by linarith))
      · exact (hgi.mono_set (by rw [uIcc_of_le hu, uIcc_of_le (by linarith)]; exact Icc_subset_Icc le_rfl (by linarith))).const_mul _
      · intro s hs
        have e1 := lg_half_pow u s (1 / 2 : ℝ) hu hs.1 hs.2 (by norm_num)
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left e1 hc) (hg_nn s hs.1)
    refine hmono.trans ?_
    rw [intervalIntegral.integral_const_mul]
    have hm := hmass (u / 2) (by linarith)
    have hnn : 0 ≤ c * ((2 : ℝ) ^ (1 / 2 : ℝ) * (1 + u) ^ (-(1 / 2 : ℝ))) := by positivity
    calc _ ≤ (c * ((2 : ℝ) ^ (1 / 2 : ℝ) * (1 + u) ^ (-(1 / 2 : ℝ)))) * 1 :=
          mul_le_mul_of_nonneg_left hm hnn
      _ = _ := by ring
  have P2 : ∫ s in (u / 2)..u, c * (1 + (u - s)) ^ (-(1 / 2 : ℝ)) * g s
      ≤ (2 * K / (L * (1 + u))) * (2 * c * (1 + u) ^ (1 / 2 : ℝ)) := by
    have hI : ∫ s in (u / 2)..u, c * (1 + (u - s)) ^ (-(1 / 2 : ℝ))
        = c * (((1 + u / 2) ^ (1 - 1 / 2 : ℝ) - 1) / (1 - 1 / 2)) := by
      have h1 := intervalIntegral.integral_comp_sub_left (a := u / 2) (b := u)
        (fun x : ℝ => c * (1 + x) ^ (-(1 / 2 : ℝ))) u
      rw [h1, sub_self, show u - u / 2 = u / 2 by ring, intervalIntegral.integral_const_mul,
        lg_ipow (1 / 2 : ℝ) 0 (u / 2) (by norm_num) le_rfl (by linarith)]
      simp
    have hmono : ∫ s in (u / 2)..u, c * (1 + (u - s)) ^ (-(1 / 2 : ℝ)) * g s
        ≤ ∫ s in (u / 2)..u, (c * (1 + (u - s)) ^ (-(1 / 2 : ℝ))) * (2 * K / (L * (1 + u))) := by
      have hcI : ContinuousOn (fun s : ℝ => c * (1 + (u - s)) ^ (-(1 / 2 : ℝ))) (uIcc (u / 2) u) := by
        rw [uIcc_of_le (by linarith)]
        apply ContinuousOn.mul continuousOn_const
        intro z hz
        have hz0 : 0 < 1 + (u - z) := by linarith [hz.2]
        exact (Real.continuousAt_rpow_const (1 + (u - z)) (-(1 / 2 : ℝ)) (Or.inl hz0.ne')).comp_continuousWithinAt
          (f := fun z : ℝ => 1 + (u - z)) (by fun_prop)
      apply intervalIntegral.integral_mono_on (by linarith)
      · have := lg_conv_ii (fun x => c * (1 + x) ^ (-(1 / 2 : ℝ))) g u hu hcont hg_cont
        exact this.mono_set (by rw [uIcc_of_le hu, uIcc_of_le (by linarith)]; exact Icc_subset_Icc (by linarith) le_rfl)
      · exact (hcI.mul continuousOn_const).intervalIntegrable
      · intro s hs
        have hs0 : 0 ≤ s := by linarith [hs.1]
        have e2 := hgb s hs0
        have e3 : g s ≤ 2 * K / (L * (1 + u)) := by
          refine e2.trans ?_
          rw [div_le_div_iff₀ (by positivity) (by positivity)]
          nlinarith [mul_nonneg (mul_nonneg hK hL.le) (show 0 ≤ 2 * (1 + s) - (1 + u) by linarith [hs.1])]
        have hpos : 0 ≤ c * (1 + (u - s)) ^ (-(1 / 2 : ℝ)) := mul_nonneg hc (Real.rpow_nonneg (by linarith [hs.2]) _)
        exact mul_le_mul_of_nonneg_left e3 hpos
    refine hmono.trans ?_
    rw [intervalIntegral.integral_mul_const, hI]
    have hle : (1 + u / 2) ^ (1 - 1 / 2 : ℝ) ≤ (1 + u) ^ (1 / 2 : ℝ) := by
      norm_num
      exact Real.rpow_le_rpow (by linarith) (by linarith) (by norm_num)
    have hnum : c * (((1 + u / 2) ^ (1 - 1 / 2 : ℝ) - 1) / (1 - 1 / 2)) ≤ 2 * c * (1 + u) ^ (1 / 2 : ℝ) := by
      have h2 : ((1 + u / 2) ^ (1 - 1 / 2 : ℝ) - 1) / (1 - 1 / 2) ≤ 2 * (1 + u) ^ (1 / 2 : ℝ) := by
        rw [div_le_iff₀ (by norm_num)]; nlinarith
      calc _ ≤ c * (2 * (1 + u) ^ (1 / 2 : ℝ)) := mul_le_mul_of_nonneg_left h2 hc
        _ = _ := by ring
    have hM : 0 ≤ 2 * K / (L * (1 + u)) := by positivity
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_left hnum hM
  have hE : (2 * K / (L * (1 + u))) * (2 * c * (1 + u) ^ (1 / 2 : ℝ))
      = 4 * K / L * (c * (1 + u) ^ (-(1 / 2 : ℝ))) := by
    have : (1 + u) ^ (1 / 2 : ℝ) = (1 + u) * (1 + u) ^ (-(1 / 2 : ℝ)) := by
      conv_lhs => rw [show (1 / 2 : ℝ) = 1 + -(1 / 2 : ℝ) by norm_num, Real.rpow_add hu1, Real.rpow_one]
    rw [this]
    field_simp
    ring
  calc _ ≤ _ := add_le_add P1 P2
    _ = _ := by rw [hE]; ring


lemma lg_Cpos (ς : ℝ) (hς : 1 < ς) : 0 < Cpq (2 + ς) 1 := by
  unfold Cpq
  exact Real.sqrt_pos.mpr (div_pos (svmain_Epq_pos (2 + ς) 1 (by linarith) one_pos) two_pos)

lemma lg_rgt (ς : ℝ) (hς : 1 < ς) : 1 < rq (2 + ς) 1 := by
  unfold rq
  rw [lt_div_iff₀ (by norm_num)]
  linarith

lemma lg_Hge1 (N : ℕ) (hN : 1 ≤ N) : 1 ≤ Hsum 1 N := by
  unfold Hsum
  have h1 : (1:ℕ) ∈ Finset.Icc 1 N := Finset.mem_Icc.2 ⟨le_rfl, hN⟩
  have := Finset.single_le_sum (f := fun i : ℕ => (i : ℝ) ^ (-(1:ℝ))) (fun i _ => by positivity) h1
  simpa using this

lemma lg_Hlog (N : ℕ) (hN : 1 ≤ N) : Real.log ((N : ℝ) + 1) ≤ Hsum 1 N := by
  have h := (lem_app_phase_harmonic_i (a := 1) one_pos N hN).1
  have e : ∫ x in (1:ℝ)..((N:ℝ)+1), x ^ (-(1:ℝ)) = Real.log ((N:ℝ)+1) := by
    simp_rw [Real.rpow_neg_one]
    rw [integral_inv_of_pos one_pos (by positivity)]
    simp
  linarith

lemma lg_fNq_cont (N : ℕ) (p q : ℝ) : Continuous (fNq (N : ℕ∞) p q) := by
  unfold fNq
  show Continuous (fun u => 1 / 2 * Lsum (N : ℕ∞) p q u)
  simp_rw [sv_Lsum_fin]
  fun_prop

lemma lg_Lsum_nonneg (N : ℕ) (p q u : ℝ) : 0 ≤ Lsum (N : ℕ∞) p q u := by
  rw [sv_Lsum_fin]
  apply Finset.sum_nonneg
  intro i _
  positivity

lemma lg_fNq_le (ς : ℝ) (hς : 1 < ς) (N : ℕ) (u : ℝ) (hu : 0 ≤ u) :
    fNq (N : ℕ∞) (2 + ς) 1 u ≤ logGlobalH ς u ^ 2 := by
  have h := lem_app_phase_sums_i (a := 2 + ς) (q := 1) (by linarith) one_pos (N : ℕ∞) hu
  have hd : dAQ (2 + ς) 1 = 2 * rq (2 + ς) 1 := by unfold dAQ rq; field_simp
  rw [hd] at h
  have hE : 0 < Epq (2 + ς) 1 := svmain_Epq_pos _ _ (by linarith) one_pos
  have hC : Cpq (2 + ς) 1 ^ 2 = Epq (2 + ς) 1 / 2 := by
    unfold Cpq
    rw [Real.sq_sqrt (by positivity)]
  have hp : ((1 + u) ^ (-rq (2 + ς) 1)) ^ 2 = (1 + u) ^ (-(2 * rq (2 + ς) 1)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]
    congr 1
    push_cast
    ring
  unfold logGlobalH
  rw [mul_pow, hp, hC]
  unfold fNq
  linarith

lemma lg_volterra (ς : ℝ) (hς : 1 < ς) (N B : ℕ) (hN : 1 ≤ N) (hNB : N ≤ B) (ε : ℝ)
    (hε : 0 < ε) (mS : RowModel (Fin N)) (hmS : IsMatchedModel (svdArrays 2 ς N B) mS ε)
    (QS : ℝ → ℝ) (hQS : IsVolterraSol mS QS) :
    ∀ u, 0 ≤ u → QS (svdT0 N B * u) = fNq (N : ℕ∞) (2 + ς) 1 u +
      Real.sqrt ε * oneSidedConv (fun v => Real.sqrt (QS (svdT0 N B * v))) (svdKernel 2 N) u := by
  obtain ⟨-, hm1, -⟩ := prop_app_phase_prefactors_m1 2 ς N B (by norm_num) (by linarith) hN hNB
  have hsE := Real.sqrt_pos.2 hε
  have hSG : 0 < (sgdArrays 2 ς N B).S := by
    rw [(prop_app_phase_prefactors_i 2 ς N B (by norm_num) (by linarith) hN hNB ε hε).2.2.1]
    have hN0 : (0:ℝ) < N := by exact_mod_cast hN
    have hH : 0 < Hsum 2 N := by
      have := lg_Hge1 N hN
      unfold Hsum at this ⊢
      apply Finset.sum_pos
      · intro i hi
        have h1 : 0 < i := (Finset.mem_Icc.mp hi).1
        exact Real.rpow_pos_of_pos (by exact_mod_cast h1) _
      · exact ⟨1, Finset.mem_Icc.mpr ⟨le_refl _, hN⟩⟩
    have hB : (0:ℝ) < B := by exact_mod_cast (by omega : 0 < B)
    have hmu : 0 < muBarOf 2 N := by unfold muBarOf; positivity
    positivity
  obtain ⟨mG, hmG1, hmG2, hmG3, hmG4, hmG5⟩ := hm1 (matchedStep (sgdArrays 2 ς N B) ε)
    (by unfold matchedStep; positivity)
  have hmG : IsMatchedModel (sgdArrays 2 ς N B) mG ε := ⟨hmG1, hmG2, hmG3, hmG4, hmG5⟩
  obtain ⟨QG, hQG, -⟩ := thm_app_phase_volterra_i mG
  obtain ⟨-, -, h3, -, h5, -⟩ := prop_app_phase_prefactors_ii 2 ς N B (by norm_num)
    (by linarith) hN hNB ε hε mS mG hmS hmG QS QG hQS hQG
  have h22 : (2:ℝ) / 2 = 1 := by norm_num
  intro u hu
  have e : oneSidedConv (fun v => Real.sqrt (QS (svdT0 N B * v))) (dimKernel mS (svdT0 N B) ε) u
      = oneSidedConv (fun v => Real.sqrt (QS (svdT0 N B * v))) (svdKernel 2 N) u := by
    unfold oneSidedConv
    apply intervalIntegral.integral_congr
    intro s hs
    rw [uIcc_of_le hu] at hs
    simp only
    rw [h5 s hs.1]
    rfl
  rw [h3 u hu, e, h22]


/-! ### Proof helpers for `lem:app-phase-log-global` (ii) -/
theorem lg_Eabs (C r c e R0 Bc H uh : ℝ) (hC : 0 < C) (hr : 1 < r) (hc : 0 ≤ c) (he : 0 ≤ e)
    (hR0 : 0 ≤ R0) (hBc : 0 ≤ Bc) (hu0 : 0 ≤ uh) (huH : uh ≤ H) (φ : ℝ → ℝ)
    (hφ : ContinuousOn φ (Icc 0 H))
    (hb1 : ∀ s ∈ Icc (0:ℝ) uh, φ s ≤ Bc)
    (hb2 : ∀ s ∈ Icc (0:ℝ) uh, φ s ≤ C * (1 + s) ^ (-r) + c * (1 + s) ^ (-(1 / 2 : ℝ)) + e) :
    ∫ s in (0:ℝ)..uh, φ s ≤ R0 * Bc + C / (r - 1) * (1 + R0) ^ (1 - r)
      + 2 * c * (1 + H) ^ (1 / 2 : ℝ) + e * H := by
  have hr1 : 0 < r - 1 := by linarith
  have hH0 : 0 ≤ H := le_trans hu0 huH
  have hφi : ∀ a b, 0 ≤ a → a ≤ b → b ≤ uh → IntervalIntegrable φ volume a b := by
    intro a b ha hab hb
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hab]
    exact hφ.mono (fun s hs => ⟨by linarith [hs.1], by linarith [hs.2]⟩)
  have T2nn : 0 ≤ C / (r - 1) * (1 + R0) ^ (1 - r) := by positivity
  have T3nn : 0 ≤ 2 * c * (1 + H) ^ (1 / 2 : ℝ) := by positivity
  have T4nn : 0 ≤ e * H := mul_nonneg he hH0
  rcases le_or_gt uh R0 with hcase | hcase
  · have : ∫ s in (0:ℝ)..uh, φ s ≤ uh * Bc := by
      have := intervalIntegral.integral_mono_on hu0 (hφi 0 uh le_rfl hu0 le_rfl)
        (intervalIntegrable_const (c := Bc)) hb1
      simpa using this
    have h2 : uh * Bc ≤ R0 * Bc := mul_le_mul_of_nonneg_right hcase hBc
    linarith
  · rw [← intervalIntegral.integral_add_adjacent_intervals (b := R0)
      (hφi 0 R0 le_rfl hR0 hcase.le) (hφi R0 uh hR0 hcase.le le_rfl)]
    have A1 : ∫ s in (0:ℝ)..R0, φ s ≤ R0 * Bc := by
      have := intervalIntegral.integral_mono_on hR0 (hφi 0 R0 le_rfl hR0 hcase.le)
        (intervalIntegrable_const (c := Bc)) (fun s hs => hb1 s ⟨hs.1, hs.2.trans hcase.le⟩)
      simpa using this
    have hcR : ∀ s ∈ Icc R0 uh, 0 ≤ s := fun s hs => hR0.trans hs.1
    have A2 : ∫ s in R0..uh, φ s ≤ ∫ s in R0..uh, (C * (1 + s) ^ (-r) + c * (1 + s) ^ (-(1 / 2 : ℝ)) + e) := by
      apply intervalIntegral.integral_mono_on hcase.le (hφi R0 uh hR0 hcase.le le_rfl)
      · apply ContinuousOn.intervalIntegrable
        rw [uIcc_of_le hcase.le]
        have hcr : ∀ q : ℝ, ContinuousOn (fun x : ℝ => (1 + x) ^ q) (Icc R0 uh) := by
          intro q z hz
          have hz0 : 0 < 1 + (z:ℝ) := by linarith [hR0, hz.1]
          exact (Real.continuousAt_rpow_const _ _ (Or.inl hz0.ne')).comp_continuousWithinAt
            (by fun_prop : ContinuousWithinAt (fun z : ℝ => 1 + z) _ z)
        exact ((continuousOn_const.mul (hcr _)).add (continuousOn_const.mul (hcr _))).add continuousOn_const
      · intro s hs
        exact hb2 s ⟨hR0.trans hs.1, hs.2⟩
    have A3 : ∫ s in R0..uh, (C * (1 + s) ^ (-r) + c * (1 + s) ^ (-(1 / 2 : ℝ)) + e)
        = C * (((1 + uh) ^ (1 - r) - (1 + R0) ^ (1 - r)) / (1 - r))
          + c * (((1 + uh) ^ (1 - 1 / 2 : ℝ) - (1 + R0) ^ (1 - 1 / 2 : ℝ)) / (1 - 1 / 2))
          + e * (uh - R0) := by
      have hcr : ∀ q : ℝ, IntervalIntegrable (fun x : ℝ => (1 + x) ^ q) volume R0 uh := by
        intro q
        apply ContinuousOn.intervalIntegrable
        rw [uIcc_of_le hcase.le]
        intro z hz
        have hz0 : 0 < 1 + (z:ℝ) := by linarith [hR0, hz.1]
        exact (Real.continuousAt_rpow_const _ _ (Or.inl hz0.ne')).comp_continuousWithinAt
          (by fun_prop : ContinuousWithinAt (fun z : ℝ => 1 + z) _ z)
      rw [intervalIntegral.integral_add ((hcr _).const_mul C |>.add ((hcr _).const_mul c))
        intervalIntegrable_const, intervalIntegral.integral_add ((hcr _).const_mul C) ((hcr _).const_mul c),
        intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
        lg_ipow r R0 uh hr.ne' hR0 hcase.le, lg_ipow (1 / 2 : ℝ) R0 uh (by norm_num) hR0 hcase.le]
      simp
      ring
    have B1 : C * (((1 + uh) ^ (1 - r) - (1 + R0) ^ (1 - r)) / (1 - r))
        ≤ C / (r - 1) * (1 + R0) ^ (1 - r) := by
      have hp : 0 ≤ (1 + uh) ^ (1 - r) := Real.rpow_nonneg (by linarith) _
      have e : ((1 + uh) ^ (1 - r) - (1 + R0) ^ (1 - r)) / (1 - r)
          = ((1 + R0) ^ (1 - r) - (1 + uh) ^ (1 - r)) / (r - 1) := by
        rw [show (1 - r) = -(r - 1) by ring, div_neg, ← neg_div]; ring_nf
      rw [e]
      calc C * (((1 + R0) ^ (1 - r) - (1 + uh) ^ (1 - r)) / (r - 1))
          ≤ C * ((1 + R0) ^ (1 - r) / (r - 1)) :=
            mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right (by linarith) hr1.le) hC.le
        _ = _ := by ring
    have B2 : c * (((1 + uh) ^ (1 - 1 / 2 : ℝ) - (1 + R0) ^ (1 - 1 / 2 : ℝ)) / (1 - 1 / 2))
        ≤ 2 * c * (1 + H) ^ (1 / 2 : ℝ) := by
      have h1 : (1 + uh) ^ (1 - 1 / 2 : ℝ) ≤ (1 + H) ^ (1 / 2 : ℝ) := by
        norm_num
        exact Real.rpow_le_rpow (by linarith) (by linarith) (by norm_num)
      have h2 : 0 ≤ (1 + R0) ^ (1 - 1 / 2 : ℝ) := Real.rpow_nonneg (by linarith) _
      have h3 : ((1 + uh) ^ (1 - 1 / 2 : ℝ) - (1 + R0) ^ (1 - 1 / 2 : ℝ)) / (1 - 1 / 2)
          ≤ 2 * (1 + H) ^ (1 / 2 : ℝ) := by
        rw [div_le_iff₀ (by norm_num)]; nlinarith
      calc _ ≤ c * (2 * (1 + H) ^ (1 / 2 : ℝ)) := mul_le_mul_of_nonneg_left h3 hc
        _ = _ := by ring
    have B3 : e * (uh - R0) ≤ e * H := mul_le_mul_of_nonneg_left (by linarith) he
    linarith


lemma lg_sqrt_eps_rpow (ε a : ℝ) (hε : 0 < ε) : Real.sqrt ε ^ a = ε ^ (a / 2) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hε.le]; congr 1; ring

lemma lg_X_id (ε C r : ℝ) (hε : 0 < ε) (hC : 0 < C) (hr : 0 < r) :
    Real.sqrt ε * (2 * C / Real.sqrt ε) ^ (1 / r)
      = (2 * C) ^ (1 / r) * ε ^ ((r - 1) / (2 * r)) := by
  have hs := Real.sqrt_pos.2 hε
  rw [Real.div_rpow (by positivity) hs.le, lg_sqrt_eps_rpow ε _ hε]
  have : Real.sqrt ε = ε ^ (1 / 2 : ℝ) := Real.sqrt_eq_rpow ε
  rw [this]
  have e : ε ^ (1 / 2 : ℝ) = ε ^ ((r - 1) / (2 * r)) * ε ^ (1 / r / 2) := by
    rw [← Real.rpow_add hε]; congr 1; field_simp; ring
  rw [e]
  field_simp

lemma lg_Xsqrt_id (ε C r L A : ℝ) (hε : 0 < ε) (hC : 0 < C) (hr : 0 < r) (hL : 0 < L)
    (hA : 0 ≤ A) :
    2 * (Real.sqrt A * ε ^ (1 / 4 : ℝ) * L ^ (-(1 / 2 : ℝ))) * ((2 * C / Real.sqrt ε) ^ (1 / r)) ^ (1 / 2 : ℝ)
      = 2 * Real.sqrt A * (2 * C) ^ (1 / (2 * r)) * L ^ (-(1 / 2 : ℝ)) * ε ^ ((r - 1) / (4 * r)) := by
  have hs := Real.sqrt_pos.2 hε
  rw [← Real.rpow_mul (by positivity), Real.div_rpow (by positivity) hs.le, lg_sqrt_eps_rpow ε _ hε]
  have e1 : (2 * C) ^ (1 / r * (1 / 2)) = (2 * C) ^ (1 / (2 * r)) := by congr 1; field_simp
  have e2 : ε ^ (1 / 4 : ℝ) = ε ^ ((r - 1) / (4 * r)) * ε ^ ((1 / r * (1 / 2)) / 2) := by
    rw [← Real.rpow_add hε]; congr 1; field_simp; ring
  rw [e1, e2]
  have : 0 < ε ^ ((1 / r * (1 / 2)) / 2) := Real.rpow_pos_of_pos hε _
  field_simp

lemma lg_Z_id (ε A L : ℝ) (hε : 0 < ε) (hA : 0 < A) (hL : 0 < L) :
    Real.sqrt ε * (4 * A / (L * Real.sqrt ε)) = 4 * A / L := by
  have hs := Real.sqrt_pos.2 hε
  field_simp

lemma lg_Zsqrt_id (ε A L : ℝ) (hε : 0 < ε) (hA : 0 < A) (hL : 0 < L) :
    2 * (Real.sqrt A * ε ^ (1 / 4 : ℝ) * L ^ (-(1 / 2 : ℝ))) * (4 * A / (L * Real.sqrt ε)) ^ (1 / 2 : ℝ)
      = 4 * A / L := by
  have hs := Real.sqrt_pos.2 hε
  rw [← Real.sqrt_eq_rpow]
  have hq : Real.sqrt (4 * A / (L * Real.sqrt ε)) = 2 * Real.sqrt A * L ^ (-(1 / 2 : ℝ)) * ε ^ (-(1 / 4 : ℝ)) := by
    rw [Real.sqrt_div (by positivity), Real.sqrt_mul (by norm_num), Real.sqrt_mul hL.le,
      show Real.sqrt 4 = 2 by rw [show (4:ℝ) = 2 ^ 2 by norm_num]; exact Real.sqrt_sq (by norm_num),
      Real.sqrt_eq_rpow L, Real.sqrt_eq_rpow (Real.sqrt ε), Real.sqrt_eq_rpow ε,
      ← Real.rpow_mul hε.le, Real.rpow_neg hL.le, Real.rpow_neg hε.le]
    norm_num
    field_simp
  rw [hq]
  have h1 : L ^ (-(1 / 2 : ℝ)) * L ^ (-(1 / 2 : ℝ)) = L⁻¹ := by
    rw [← Real.rpow_add hL, show -(1 / 2 : ℝ) + -(1 / 2) = -1 by norm_num, Real.rpow_neg_one]
  have h2 : ε ^ (1 / 4 : ℝ) * ε ^ (-(1 / 4 : ℝ)) = 1 := by
    rw [← Real.rpow_add hε]; simp
  have h3 : Real.sqrt A * Real.sqrt A = A := Real.mul_self_sqrt hA.le
  calc _ = 4 * (Real.sqrt A * Real.sqrt A) * (L ^ (-(1 / 2 : ℝ)) * L ^ (-(1 / 2 : ℝ))) * (ε ^ (1 / 4 : ℝ) * ε ^ (-(1 / 4 : ℝ))) := by ring
    _ = _ := by rw [h1, h2, h3]; field_simp


lemma lg_tail (ε C r A L : ℝ) (hε : 0 < ε) (hC : 0 < C) (hr : 0 < r) (hA : 0 < A) (hL : 0 < L) :
    2 * (Real.sqrt A * ε ^ (1 / 4 : ℝ) * L ^ (-(1 / 2 : ℝ))) *
        (1 + (max ((2 * C / Real.sqrt ε) ^ (1 / r)) (4 * A / (L * Real.sqrt ε)) - 1)) ^ (1 / 2 : ℝ)
      + Real.sqrt ε * (max ((2 * C / Real.sqrt ε) ^ (1 / r)) (4 * A / (L * Real.sqrt ε)) - 1)
    ≤ 2 * Real.sqrt A * (2 * C) ^ (1 / (2 * r)) * L ^ (-(1 / 2 : ℝ)) * ε ^ ((r - 1) / (4 * r))
      + (2 * C) ^ (1 / r) * ε ^ ((r - 1) / (2 * r)) + 8 * A / L := by
  have hs := Real.sqrt_pos.2 hε
  set X := (2 * C / Real.sqrt ε) ^ (1 / r) with hX
  set Z := 4 * A / (L * Real.sqrt ε) with hZ
  have hX0 : 0 ≤ X := Real.rpow_nonneg (by positivity) _
  have hZ0 : 0 < Z := by positivity
  have hc0 : 0 ≤ 2 * (Real.sqrt A * ε ^ (1 / 4 : ℝ) * L ^ (-(1 / 2 : ℝ))) := by positivity
  have h1 : (max X Z) ^ (1 / 2 : ℝ) ≤ X ^ (1 / 2 : ℝ) + Z ^ (1 / 2 : ℝ) := by
    have a1 : 0 ≤ X ^ (1 / 2 : ℝ) := Real.rpow_nonneg hX0 _
    have a2 : 0 ≤ Z ^ (1 / 2 : ℝ) := Real.rpow_nonneg hZ0.le _
    rcases le_total X Z with h | h
    · rw [max_eq_right h]; linarith
    · rw [max_eq_left h]; linarith
  have h2 : max X Z - 1 ≤ X + Z := by
    have : max X Z ≤ X + Z := max_le (by linarith) (by linarith)
    linarith
  rw [add_sub_cancel]
  have e1 := lg_Xsqrt_id ε C r L A hε hC hr hL hA.le
  have e2 := lg_Zsqrt_id ε A L hε hA hL
  have e3 := lg_X_id ε C r hε hC hr
  have e4 := lg_Z_id ε A L hε hA hL
  calc _ ≤ 2 * (Real.sqrt A * ε ^ (1 / 4 : ℝ) * L ^ (-(1 / 2 : ℝ))) * (X ^ (1 / 2 : ℝ) + Z ^ (1 / 2 : ℝ))
        + Real.sqrt ε * (X + Z) := by
        apply add_le_add (mul_le_mul_of_nonneg_left h1 hc0)
        exact mul_le_mul_of_nonneg_left h2 hs.le
    _ = (2 * (Real.sqrt A * ε ^ (1 / 4 : ℝ) * L ^ (-(1 / 2 : ℝ))) * X ^ (1 / 2 : ℝ) + Real.sqrt ε * X)
        + (2 * (Real.sqrt A * ε ^ (1 / 4 : ℝ) * L ^ (-(1 / 2 : ℝ))) * Z ^ (1 / 2 : ℝ) + Real.sqrt ε * Z) := by ring
    _ = _ := by rw [e1, e2, e3, e4]; ring


lemma lg_firstHit_pos (R : ℝ → ℝ) (a : ℝ) (hR : ContinuousWithinAt R (Ici 0) 0)
    (h0 : a < R 0) : 0 < firstHit R a := by
  have hev : ∀ᶠ t in 𝓝[Ici 0] (0:ℝ), a < R t := hR.eventually (lt_mem_nhds h0)
  rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at hev
  obtain ⟨δ, hδ, hδ'⟩ := hev
  have hle : ENNReal.ofReal (δ / 2) ≤ firstHit R a := by
    unfold firstHit
    refine le_iInf₂ fun t ht => ?_
    by_contra hlt
    push_neg at hlt
    have h1 : (t : ℝ) < δ / 2 := by
      rw [← ENNReal.ofReal_coe_nnreal] at hlt
      exact (ENNReal.ofReal_lt_ofReal_iff (by positivity)).1 hlt
    have h2 := hδ' (y := (t : ℝ)) (by
      rw [Real.dist_eq, sub_zero, abs_of_nonneg (NNReal.coe_nonneg t)]; linarith) (Set.mem_Ici.2 t.2)
    linarith
  exact lt_of_lt_of_le (ENNReal.ofReal_pos.2 (by positivity)) hle

lemma lg_firstHit_le (R : ℝ → ℝ) (a H : ℝ) (hH : 0 ≤ H) (h : R H ≤ a) :
    firstHit R a ≤ ENNReal.ofReal H := by
  unfold firstHit
  have : R ((H.toNNReal : ℝ≥0) : ℝ) ≤ a := by rw [Real.coe_toNNReal _ hH]; exact h
  exact iInf₂_le H.toNNReal this

lemma lg_sqrt_sub (a b : ℝ) (hb : 0 ≤ b) (hab : b ≤ a) :
    Real.sqrt a - Real.sqrt b ≤ Real.sqrt (a - b) := by
  have h1 : Real.sqrt b ≤ Real.sqrt a := Real.sqrt_le_sqrt hab
  apply Real.le_sqrt_of_sq_le
  have ha := Real.sq_sqrt (hb.trans hab)
  have hb' := Real.sq_sqrt hb
  nlinarith [Real.sqrt_nonneg b, mul_le_mul_of_nonneg_right h1 (Real.sqrt_nonneg b)]

lemma lg_N1 (N : ℕ) (hN : Real.exp logGlobalL0 ≤ (N : ℝ)) : 1 ≤ N := by
  have h1 : (1:ℝ) ≤ logGlobalL0 := le_max_left _ _
  have h2 : Real.exp 1 ≤ (N : ℝ) := (Real.exp_le_exp.2 h1).trans hN
  have h3 : (2:ℝ) < Real.exp 1 := by
    have := Real.add_one_lt_exp (by norm_num : (1:ℝ) ≠ 0)
    linarith
  have : (1:ℝ) ≤ N := by linarith
  exact_mod_cast this

lemma lg_f0 (N : ℕ) (hN : 1 ≤ N) (p : ℝ) : 1 / 2 ≤ fNq (N : ℕ∞) p 1 0 := by
  unfold fNq
  rw [sv_Lsum_fin]
  have h1 : (1:ℕ) ∈ Finset.Icc 1 N := Finset.mem_Icc.2 ⟨le_rfl, hN⟩
  have := Finset.single_le_sum (f := fun i : ℕ => (i : ℝ) ^ (-p) * Real.exp (-(2 * (0:ℝ)) * (i : ℝ) ^ (-(1:ℝ))))
    (fun i _ => by positivity) h1
  simp at this
  simp only [mul_zero, neg_zero, zero_mul, Real.exp_zero, mul_one]
  linarith


/-- Part (i) of `lem:app-phase-log-global`: the sandwich `f_{N,1} ≤ Y ≤ (h+𝗐+√ε)²` on `[0,∞)`,
for the matched \SignSVD model at level `ε` (`Y(u) = Q(T_0 u)`).

`lem:app-phase-log-global`, snapshot `cr-2026-10-23`. Source: `section.tex` l.2430–2449 (environment).

LaTeX (verbatim, `section.tex` l.2430–2449):
```latex
\begin{lemma}[\SignSVD kernel, $\alpha=2$, $\texp>1$]\label{lem:app-phase-log-global}
Let $\alpha=2$ and $\texp>1$, so $q=1$ and $r\defeq r_{\text{s-SVD}}>1$. Put
$C\defeq C_{p,1}$, $K\defeq2E_{2,1}$, $L_N\defeq H_N(1)$ and
\[
\mathsf A_0\defeq\frac{CK}{r-1}\Big(\frac{2^r}e+2\Big),\qquad L_0\defeq\max\Big\{1,\frac{4K}{2-\sqrt2}\Big\},
\]
\[
h(u)\defeq C(1+u)^{-r},\qquad \mathsf w(u)\defeq\sqrt{\mathsf A_0}\,\epsilon^{1/4}L_N^{-1/2}(1+u)^{-1/2} .
\]
Let $N\ge e^{L_0}$, $B\ge N$ and $\epsilon>0$. Then
$f_{N,1}\le Y_{\text{s-SVD}}\le(h+\mathsf w+\sqrt\epsilon)^2$ on $[0,\infty)$. If moreover
$T\ge4$ and $0<\epsilon<\min\{1,C^2,1/(8T)\}$, the first hit satisfies
$0<\hat u\le H\defeq\max\{(2C/\sqrt\epsilon)^{1/r},4\mathsf A_0/(L_N\sqrt\epsilon)\}-1$, and
\begin{multline*}
0\le\mathcal E\le\epsilon^{1/8}\sqrt{C+\sqrt{\mathsf A_0}+1}+\frac C{r-1}\big(1+\epsilon^{-1/8}\big)^{1-r}\\
+2\sqrt{\mathsf A_0}(2C)^{1/(2r)}L_N^{-1/2}\epsilon^{(r-1)/(4r)}+(2C)^{1/r}\epsilon^{(r-1)/(2r)}+\frac{8\mathsf A_0}{L_N} .
\end{multline*}
In particular $\mathcal E\to0$ along every sequence with $N\to\infty$ and
$\epsilon\downarrow0$.
\end{lemma}
``` -/
theorem lem_app_phase_log_global_i (ς : ℝ) (hς : 1 < ς) (N B : ℕ)
    (hN : Real.exp logGlobalL0 ≤ (N : ℝ)) (hNB : N ≤ B) (ε : ℝ) (hε : 0 < ε)
    (mS : RowModel (Fin N)) (hmS : IsMatchedModel (svdArrays 2 ς N B) mS ε)
    (QS : ℝ → ℝ) (hQS : IsVolterraSol mS QS) :
    ∀ u : ℝ, 0 ≤ u →
      fNq (N : ℕ∞) (2 + ς) 1 u ≤ QS (svdT0 N B * u) ∧
        QS (svdT0 N B * u) ≤ (logGlobalH ς u + logGlobalW ς N ε u + Real.sqrt ε) ^ 2 := by
  intro u hu
  have hN1 : 1 ≤ N := by
    have h1 : (1:ℝ) ≤ logGlobalL0 := le_max_left _ _
    have h2 : Real.exp 1 ≤ (N : ℝ) := (Real.exp_le_exp.2 h1).trans hN
    have h3 : (2:ℝ) < Real.exp 1 := by
      have := Real.add_one_lt_exp (by norm_num : (1:ℝ) ≠ 0)
      linarith
    have : (1:ℝ) ≤ N := by linarith
    exact_mod_cast this
  have hL1 := lg_Hge1 N hN1
  have hLpos : 0 < Hsum 1 N := by linarith
  have hC := lg_Cpos ς hς
  have hr := lg_rgt ς hς
  have hEp : 0 < Epq 2 1 := svmain_Epq_pos 2 1 (by norm_num) one_pos
  set K : ℝ := 2 * Epq 2 1 with hKdef
  have hK : 0 ≤ K := by positivity
  have hA0 : 0 ≤ logGlobalA0 ς := by
    unfold logGlobalA0
    have : 0 < rq (2 + ς) 1 - 1 := by linarith
    positivity
  have h22 : (2:ℝ) / 2 = 1 := by norm_num
  have hHs : Hsum (2 / 2) N = Hsum 1 N := by rw [h22]
  have hkern_b : ∀ v, 0 ≤ v → svdKernel 2 N v ≤ K / (Hsum 1 N * (1 + v)) := by
    intro v hv
    have := svmain_env 2 N (by norm_num) hN1 v hv
    rw [h22] at this
    rw [show (2:ℝ) - 1 = 1 by norm_num, Real.rpow_neg_one] at this
    refine this.trans (le_of_eq ?_)
    rw [hKdef]
    field_simp
  have hg_cont : ContinuousOn (svdKernel 2 N) (Ici 0) := (svmain_cont 2 N).continuousOn
  have hg_nn : ∀ s, 0 ≤ s → 0 ≤ svdKernel 2 N s := fun s _ => by
    apply svmain_nonneg 2 N
    rw [hHs]; exact hLpos
  have hg_mass : ∀ x, 0 ≤ x → ∫ s in (0:ℝ)..x, svdKernel 2 N s ≤ 1 :=
    fun x hx => svmain_mass 2 N (by norm_num) hN1 x hx
  -- constants
  set c : ℝ := Real.sqrt (logGlobalA0 ς) * ε ^ (1 / 4 : ℝ) * Hsum 1 N ^ (-(1 / 2 : ℝ)) with hcdef
  have hc0 : 0 ≤ c := by positivity
  have hwdef : ∀ x, logGlobalW ς N ε x = c * (1 + x) ^ (-(1 / 2 : ℝ)) := fun x => rfl
  have hhdef : ∀ x, logGlobalH ς x = Cpq (2 + ς) 1 * (1 + x) ^ (-rq (2 + ς) 1) := fun x => rfl
  have hcont_rpow : ∀ e : ℝ, ContinuousOn (fun x : ℝ => (1 + x) ^ e) (Ici 0) := by
    intro e z hz
    have hz0 : 0 < 1 + (z:ℝ) := by have := hz.out; linarith
    exact (Real.continuousAt_rpow_const _ _ (Or.inl hz0.ne')).comp_continuousWithinAt
      (by fun_prop : ContinuousWithinAt (fun z : ℝ => 1 + z) _ z)
  have hh_cont : ContinuousOn (logGlobalH ς) (Ici 0) := by
    rw [show logGlobalH ς = fun x => Cpq (2 + ς) 1 * (1 + x) ^ (-rq (2 + ς) 1) from funext hhdef]; exact continuousOn_const.mul (hcont_rpow _)
  have hw_cont : ContinuousOn (logGlobalW ς N ε) (Ici 0) := by
    rw [show logGlobalW ς N ε = fun x => c * (1 + x) ^ (-(1 / 2 : ℝ)) from funext hwdef]; exact continuousOn_const.mul (hcont_rpow _)
  have hh_nn : ∀ s, 0 ≤ s → 0 ≤ logGlobalH ς s := fun s hs => by
    rw [hhdef]; have := hC; positivity
  have hw_nn : ∀ s, 0 ≤ s → 0 ≤ logGlobalW ς N ε s := fun s hs => by
    rw [hwdef]; positivity
  -- Y
  have hT0 : 0 < svdT0 N B := by
    unfold svdT0
    apply Real.sqrt_pos.2
    unfold gammaRat
    have : (0:ℝ) < N := by exact_mod_cast hN1
    have hB : (0:ℝ) < B := by exact_mod_cast (by omega : 0 < B)
    positivity
  have hY_cont : ContinuousOn (fun s => QS (svdT0 N B * s)) (Ici 0) := by
    refine hQS.1.comp (by fun_prop) ?_
    intro s hs
    exact mul_nonneg hT0.le hs
  have hY_nn : ∀ s, 0 ≤ s → 0 ≤ QS (svdT0 N B * s) := fun s hs =>
    hQS.2.1 _ (mul_nonneg hT0.le hs)
  have hV := lg_volterra ς hς N B hN1 hNB ε hε mS hmS QS hQS
  have hfnn : ∀ s, 0 ≤ s → 0 ≤ fNq (N : ℕ∞) (2 + ς) 1 s := fun s _ => by
    unfold fNq; have := lg_Lsum_nonneg N (2 + ς) 1 s; positivity
  have hcf := (lg_fNq_cont N (2 + ς) 1).continuousOn (s := Ici 0)
  -- lower bound
  have hconv_nn : ∀ s, 0 ≤ s → 0 ≤ oneSidedConv (fun v => Real.sqrt (QS (svdT0 N B * v))) (svdKernel 2 N) s := by
    intro s hs
    unfold oneSidedConv
    apply intervalIntegral.integral_nonneg hs
    intro t ht
    exact mul_nonneg (Real.sqrt_nonneg _) (hg_nn t ht.1)
  have hlow : fNq (N : ℕ∞) (2 + ς) 1 u ≤ QS (svdT0 N B * u) := by
    rw [hV u hu]
    have := hconv_nn u hu
    have := Real.sqrt_nonneg ε
    nlinarith [mul_nonneg ‹0 ≤ √ε› ‹0 ≤ oneSidedConv (fun v => Real.sqrt (QS (svdT0 N B * v))) (svdKernel 2 N) u›]
  refine ⟨hlow, ?_⟩
  -- upper bound
  have hLbig : 4 * K / (2 - Real.sqrt 2) ≤ Hsum 1 N := by
    have h1 : logGlobalL0 ≤ Real.log (N : ℝ) := by
      rw [Real.le_log_iff_exp_le (by exact_mod_cast hN1)]; exact hN
    have h2 : Real.log (N : ℝ) ≤ Real.log ((N : ℝ) + 1) :=
      Real.log_le_log (by exact_mod_cast hN1) (by linarith)
    have h3 : 4 * (2 * Epq 2 1) / (2 - Real.sqrt 2) ≤ logGlobalL0 := le_max_right _ _
    linarith [lg_Hlog N hN1]
  have hs2 : Real.sqrt 2 < 2 := by
    rw [Real.sqrt_lt' (by norm_num)]; norm_num
  have hKL : (2:ℝ) ^ (1 / 2 : ℝ) + 4 * K / Hsum 1 N ≤ 2 := by
    have h1 : 4 * K ≤ Hsum 1 N * (2 - Real.sqrt 2) := by
      rw [div_le_iff₀ (by linarith)] at hLbig; linarith
    have h2 : 4 * K / Hsum 1 N ≤ 2 - Real.sqrt 2 := by
      rw [div_le_iff₀ hLpos]; linarith
    rw [← Real.sqrt_eq_rpow]; linarith
  have hwsq : ∀ s, 0 ≤ s → logGlobalW ς N ε s ^ 2 = logGlobalA0 ς * Real.sqrt ε / (Hsum 1 N * (1 + s)) := by
    intro s hs
    have hs1 : 0 < 1 + s := by linarith
    rw [hwdef, hcdef, mul_pow, mul_pow, mul_pow, Real.sq_sqrt hA0]
    have e1 : (ε ^ (1 / 4 : ℝ)) ^ 2 = Real.sqrt ε := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hε.le, Real.sqrt_eq_rpow]; norm_num
    have e2 : (Hsum 1 N ^ (-(1 / 2 : ℝ))) ^ 2 = (Hsum 1 N)⁻¹ := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hLpos.le, ← Real.rpow_neg_one]; norm_num
    have e3 : ((1 + s) ^ (-(1 / 2 : ℝ))) ^ 2 = (1 + s)⁻¹ := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hs1.le, ← Real.rpow_neg_one]; norm_num
    rw [e1, e2, e3]
    field_simp
  refine lg_upper ε hε (fNq (N : ℕ∞) (2 + ς) 1) (svdKernel 2 N) (logGlobalH ς) (logGlobalW ς N ε)
    (fun s => QS (svdT0 N B * s)) hg_cont hg_nn hg_mass hh_cont hh_nn hw_cont hw_nn
    (hcf) hfnn (fun s hs => lg_fNq_le ς hς N s hs) hY_cont hY_nn hV ?_ ?_ u hu
  · intro s hs
    rw [hwsq s hs]
    have := lg_convh (rq (2 + ς) 1) (Cpq (2 + ς) 1) K (Hsum 1 N) hr hC hK hLpos (svdKernel 2 N)
      hg_cont hg_nn hkern_b s hs
    have h2 := mul_le_mul_of_nonneg_left this (Real.sqrt_nonneg ε)
    refine h2.trans (le_of_eq ?_)
    unfold logGlobalA0
    field_simp
    rw [hKdef]
  · intro s hs
    have := lg_convw c K (Hsum 1 N) hc0 hK hLpos (svdKernel 2 N) hg_cont hg_nn hkern_b hg_mass s hs
    have hw0 := hw_nn s hs
    rw [hwdef] at hw0 ⊢
    calc _ ≤ _ := this
      _ ≤ 2 * (c * (1 + s) ^ (-(1 / 2 : ℝ))) := mul_le_mul_of_nonneg_right hKL hw0

/-- Part (ii) of `lem:app-phase-log-global`: the first hit `0 < û ≤ H` and the bound
`0 ≤ ℰ ≤ logGlobalErrBound` for `T ≥ 4`, `0 < ε < min{1, C², 1/(8T)}`.

`lem:app-phase-log-global`, snapshot `cr-2026-10-23`. Source: `section.tex` l.2430–2449 (environment).

LaTeX (verbatim, `section.tex` l.2430–2449):
```latex
\begin{lemma}[\SignSVD kernel, $\alpha=2$, $\texp>1$]\label{lem:app-phase-log-global}
Let $\alpha=2$ and $\texp>1$, so $q=1$ and $r\defeq r_{\text{s-SVD}}>1$. Put
$C\defeq C_{p,1}$, $K\defeq2E_{2,1}$, $L_N\defeq H_N(1)$ and
\[
\mathsf A_0\defeq\frac{CK}{r-1}\Big(\frac{2^r}e+2\Big),\qquad L_0\defeq\max\Big\{1,\frac{4K}{2-\sqrt2}\Big\},
\]
\[
h(u)\defeq C(1+u)^{-r},\qquad \mathsf w(u)\defeq\sqrt{\mathsf A_0}\,\epsilon^{1/4}L_N^{-1/2}(1+u)^{-1/2} .
\]
Let $N\ge e^{L_0}$, $B\ge N$ and $\epsilon>0$. Then
$f_{N,1}\le Y_{\text{s-SVD}}\le(h+\mathsf w+\sqrt\epsilon)^2$ on $[0,\infty)$. If moreover
$T\ge4$ and $0<\epsilon<\min\{1,C^2,1/(8T)\}$, the first hit satisfies
$0<\hat u\le H\defeq\max\{(2C/\sqrt\epsilon)^{1/r},4\mathsf A_0/(L_N\sqrt\epsilon)\}-1$, and
\begin{multline*}
0\le\mathcal E\le\epsilon^{1/8}\sqrt{C+\sqrt{\mathsf A_0}+1}+\frac C{r-1}\big(1+\epsilon^{-1/8}\big)^{1-r}\\
+2\sqrt{\mathsf A_0}(2C)^{1/(2r)}L_N^{-1/2}\epsilon^{(r-1)/(4r)}+(2C)^{1/r}\epsilon^{(r-1)/(2r)}+\frac{8\mathsf A_0}{L_N} .
\end{multline*}
In particular $\mathcal E\to0$ along every sequence with $N\to\infty$ and
$\epsilon\downarrow0$.
\end{lemma}
``` -/
theorem lem_app_phase_log_global_ii (ς : ℝ) (hς : 1 < ς) (N B : ℕ)
    (hN : Real.exp logGlobalL0 ≤ (N : ℝ)) (hNB : N ≤ B) (T ε : ℝ) (hT : 4 ≤ T)
    (hε : 0 < ε) (hεT : ε < min 1 (min (Cpq (2 + ς) 1 ^ 2) (1 / (8 * T))))
    (mS : RowModel (Fin N)) (hmS : IsMatchedModel (svdArrays 2 ς N B) mS ε)
    (QS : ℝ → ℝ) (hQS : IsVolterraSol mS QS) :
    0 < firstHit (fun u => QS (svdT0 N B * u)) (T * ε) ∧
    firstHit (fun u => QS (svdT0 N B * u)) (T * ε) ≤
      ENNReal.ofReal (max ((2 * Cpq (2 + ς) 1 / Real.sqrt ε) ^ (1 / rq (2 + ς) 1))
        (4 * logGlobalA0 ς / (Hsum 1 N * Real.sqrt ε)) - 1) ∧
    0 ≤ phaseErr (fun u => QS (svdT0 N B * u)) (fNq (N : ℕ∞) (2 + ς) 1)
        (firstHit (fun u => QS (svdT0 N B * u)) (T * ε)).toReal ∧
    phaseErr (fun u => QS (svdT0 N B * u)) (fNq (N : ℕ∞) (2 + ς) 1)
        (firstHit (fun u => QS (svdT0 N B * u)) (T * ε)).toReal
      ≤ logGlobalErrBound N ς ε := by
  have hN1 := lg_N1 N hN
  have sand := lem_app_phase_log_global_i ς hς N B hN hNB ε hε mS hmS QS hQS
  have hV0 := lg_volterra ς hς N B hN1 hNB ε hε mS hmS QS hQS
  have hC : 0 < Cpq (2 + ς) 1 := lg_Cpos ς hς
  have hr : 1 < rq (2 + ς) 1 := lg_rgt ς hς
  have hEp : 0 < Epq 2 1 := svmain_Epq_pos 2 1 (by norm_num) one_pos
  have hA0 : 0 < logGlobalA0 ς := by
    unfold logGlobalA0
    have : 0 < rq (2 + ς) 1 - 1 := by linarith
    positivity
  have hL1 := lg_Hge1 N hN1
  have hLpos : 0 < Hsum 1 N := by linarith
  have hε1 : ε < 1 := lt_of_lt_of_le hεT (min_le_left _ _)
  have hεC : ε < Cpq (2 + ς) 1 ^ 2 := lt_of_lt_of_le hεT ((min_le_right _ _).trans (min_le_left _ _))
  have hεT' : ε < 1 / (8 * T) := lt_of_lt_of_le hεT ((min_le_right _ _).trans (min_le_right _ _))
  have hse := Real.sqrt_pos.2 hε
  have hse2 : Real.sqrt ε ^ 2 = ε := Real.sq_sqrt hε.le
  have hsC : Real.sqrt ε < Cpq (2 + ς) 1 := by rw [Real.sqrt_lt' hC]; exact hεC
  have hT0 : 0 < svdT0 N B := by
    unfold svdT0
    apply Real.sqrt_pos.2
    unfold gammaRat
    have : (0:ℝ) < N := by exact_mod_cast hN1
    have hB : (0:ℝ) < B := by exact_mod_cast (by omega : 0 < B)
    positivity
  have hg_cont : ContinuousOn (svdKernel 2 N) (Ici 0) := (svmain_cont 2 N).continuousOn
  have h22 : (2:ℝ) / 2 = 1 := by norm_num
  have hHs : Hsum (2 / 2) N = Hsum 1 N := by rw [h22]
  have hg_nn : ∀ s, 0 ≤ s → 0 ≤ svdKernel 2 N s := fun s _ => by
    apply svmain_nonneg 2 N
    rw [hHs]; exact hLpos
  have hg_mass : ∀ x, 0 ≤ x → ∫ s in (0:ℝ)..x, svdKernel 2 N s ≤ 1 :=
    fun x hx => svmain_mass 2 N (by norm_num) hN1 x hx
  have hTε : T * ε < 1 / 8 := by
    rw [lt_div_iff₀ (by linarith)] at hεT'
    nlinarith only [hεT', hT]
  obtain ⟨Y, hYdef⟩ : ∃ Y : ℝ → ℝ, Y = fun u => QS (svdT0 N B * u) := ⟨_, rfl⟩
  rw [← hYdef]
  have hY_cont : ContinuousOn Y (Ici 0) := by
    rw [hYdef]
    refine hQS.1.comp (by fun_prop) ?_
    intro s hs
    exact mul_nonneg hT0.le hs
  have hY_nn : ∀ s, 0 ≤ s → 0 ≤ Y s := fun s hs => by
    rw [hYdef]; exact hQS.2.1 _ (mul_nonneg hT0.le hs)
  have hsand : ∀ s, 0 ≤ s → fNq (N : ℕ∞) (2 + ς) 1 s ≤ Y s ∧
      Y s ≤ (logGlobalH ς s + logGlobalW ς N ε s + Real.sqrt ε) ^ 2 := by
    intro s hs; rw [hYdef]; exact sand s hs
  have hV : ∀ s, 0 ≤ s → Y s = fNq (N : ℕ∞) (2 + ς) 1 s +
      Real.sqrt ε * oneSidedConv (fun v => Real.sqrt (Y v)) (svdKernel 2 N) s := by
    intro s hs; rw [hYdef]; exact hV0 s hs
  have hcf : ContinuousOn (fNq (N : ℕ∞) (2 + ς) 1) (Ici 0) := (lg_fNq_cont N (2 + ς) 1).continuousOn
  -- the horizon
  set C := Cpq (2 + ς) 1 with hCdef
  set r := rq (2 + ς) 1 with hrdef
  set A := logGlobalA0 ς with hAdef
  set L := Hsum 1 N with hLdef
  set c : ℝ := Real.sqrt A * ε ^ (1 / 4 : ℝ) * L ^ (-(1 / 2 : ℝ)) with hcdef
  have hc0 : 0 ≤ c := by positivity
  have hwdef : ∀ x, logGlobalW ς N ε x = c * (1 + x) ^ (-(1 / 2 : ℝ)) := fun x => rfl
  have hhdef : ∀ x, logGlobalH ς x = C * (1 + x) ^ (-r) := fun x => rfl
  set X : ℝ := (2 * C / Real.sqrt ε) ^ (1 / r) with hXdef
  set Z : ℝ := 4 * A / (L * Real.sqrt ε) with hZdef
  have hr0 : 0 < r := by linarith
  have hX1 : 1 ≤ X := by
    apply Real.one_le_rpow _ (by positivity)
    rw [one_le_div hse]; linarith
  have hZpos : 0 < Z := by positivity
  have hH0 : 0 ≤ max X Z - 1 := by
    have := le_max_left X Z; linarith
  have hH1 : 1 + (max X Z - 1) = max X Z := by ring
  have hXpos : 0 < X := by linarith
  have hhH : logGlobalH ς (max X Z - 1) ≤ Real.sqrt ε / 2 := by
    rw [hhdef, hH1]
    have h1 : (max X Z) ^ (-r) ≤ X ^ (-r) :=
      Real.rpow_le_rpow_of_nonpos hXpos (le_max_left _ _) (by linarith)
    have h2 : X ^ (-r) = Real.sqrt ε / (2 * C) := by
      rw [hXdef, ← Real.rpow_mul (by positivity)]
      rw [show 1 / r * -r = -1 by field_simp, Real.rpow_neg_one]
      field_simp
    calc C * (max X Z) ^ (-r) ≤ C * X ^ (-r) := mul_le_mul_of_nonneg_left h1 hC.le
      _ = Real.sqrt ε / 2 := by rw [h2]; field_simp
  have hwsq : ∀ s, 0 ≤ s → logGlobalW ς N ε s ^ 2 = A * Real.sqrt ε / (L * (1 + s)) := by
    intro s hs
    have hs1 : 0 < 1 + s := by linarith
    rw [hwdef, hcdef, mul_pow, mul_pow, mul_pow, Real.sq_sqrt hA0.le]
    have e1 : (ε ^ (1 / 4 : ℝ)) ^ 2 = Real.sqrt ε := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hε.le, Real.sqrt_eq_rpow]; norm_num
    have e2 : (L ^ (-(1 / 2 : ℝ))) ^ 2 = L⁻¹ := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hLpos.le, ← Real.rpow_neg_one]; norm_num
    have e3 : ((1 + s) ^ (-(1 / 2 : ℝ))) ^ 2 = (1 + s)⁻¹ := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hs1.le, ← Real.rpow_neg_one]; norm_num
    rw [e1, e2, e3]
    field_simp
  have hwH : logGlobalW ς N ε (max X Z - 1) ≤ Real.sqrt ε / 2 := by
    have hw0 : 0 ≤ logGlobalW ς N ε (max X Z - 1) := by rw [hwdef]; positivity
    have hsq := hwsq _ hH0
    rw [hH1] at hsq
    have h3 : A * Real.sqrt ε / (L * max X Z) ≤ ε / 4 := by
      have hZle : Z ≤ max X Z := le_max_right _ _
      calc A * Real.sqrt ε / (L * max X Z) ≤ A * Real.sqrt ε / (L * Z) := by
            apply div_le_div_of_nonneg_left (by positivity) (by positivity)
            exact mul_le_mul_of_nonneg_left hZle hLpos.le
        _ = ε / 4 := by
            rw [hZdef]; field_simp; nlinarith only [hse2]
    by_contra hcon
    push_neg at hcon
    have hh4 : Real.sqrt ε / 2 < logGlobalW ς N ε (max X Z - 1) := hcon
    nlinarith only [hh4, hsq, h3, hse2, hse]
  have hYH : Y (max X Z - 1) ≤ T * ε := by
    have h1 := (hsand _ hH0).2
    have h2 : (logGlobalH ς (max X Z - 1) + logGlobalW ς N ε (max X Z - 1) + Real.sqrt ε) ^ 2
        ≤ (2 * Real.sqrt ε) ^ 2 := by
      apply pow_le_pow_left₀ (by
        have : 0 ≤ logGlobalH ς (max X Z - 1) := by rw [hhdef]; positivity
        have : 0 ≤ logGlobalW ς N ε (max X Z - 1) := by rw [hwdef]; positivity
        positivity)
      linarith
    calc Y (max X Z - 1) ≤ _ := h1
      _ ≤ (2 * Real.sqrt ε) ^ 2 := h2
      _ = 4 * ε := by rw [mul_pow, hse2]; norm_num
      _ ≤ T * ε := mul_le_mul_of_nonneg_right hT hε.le
  have hf0 : T * ε < Y 0 := by
    have := (hsand 0 le_rfl).1
    have := lg_f0 N hN1 (2 + ς)
    linarith
  have hpos := lg_firstHit_pos Y (T * ε) (hY_cont.continuousWithinAt (Set.mem_Ici.2 le_rfl)) hf0
  have hle := lg_firstHit_le Y (T * ε) (max X Z - 1) hH0 hYH
  refine ⟨hpos, hle, ?_, ?_⟩
  · unfold phaseErr
    apply intervalIntegral.integral_nonneg ENNReal.toReal_nonneg
    intro s hs
    exact sub_nonneg.2 (Real.sqrt_le_sqrt (hsand s hs.1).1)
  · unfold phaseErr
    set uh : ℝ := (firstHit Y (T * ε)).toReal with huhdef
    have hu0 : 0 ≤ uh := ENNReal.toReal_nonneg
    have huH : uh ≤ max X Z - 1 := ENNReal.toReal_le_of_le_ofReal hH0 hle
    -- Y - f bound
    have hsqrtY : ∀ s, 0 ≤ s → Real.sqrt (Y s) ≤ C * (1 + s) ^ (-r) + c * (1 + s) ^ (-(1 / 2 : ℝ)) + Real.sqrt ε := by
      intro s hs
      have h1 := (hsand s hs).2
      have hh : 0 ≤ C * (1 + s) ^ (-r) := by positivity
      have hw : 0 ≤ c * (1 + s) ^ (-(1 / 2 : ℝ)) := by positivity
      calc Real.sqrt (Y s) ≤ Real.sqrt ((logGlobalH ς s + logGlobalW ς N ε s + Real.sqrt ε) ^ 2) :=
            Real.sqrt_le_sqrt h1
        _ = _ := by
            rw [Real.sqrt_sq (by rw [hhdef, hwdef]; positivity), hhdef, hwdef]
    have hΦ : ∀ s, 0 ≤ s → Real.sqrt (Y s) ≤ C + c + Real.sqrt ε := by
      intro s hs
      refine (hsqrtY s hs).trans ?_
      have h1 : (1 + s) ^ (-r) ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by linarith)
      have h2 : (1 + s) ^ (-(1 / 2 : ℝ)) ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by norm_num)
      have := mul_le_mul_of_nonneg_left h1 hC.le
      have := mul_le_mul_of_nonneg_left h2 hc0
      linarith
    have hΦM : C + c + Real.sqrt ε ≤ C + Real.sqrt A + 1 := by
      have h1 : ε ^ (1 / 4 : ℝ) ≤ 1 := Real.rpow_le_one hε.le hε1.le (by norm_num)
      have h2 : L ^ (-(1 / 2 : ℝ)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hL1 (by norm_num)
      have h3 : Real.sqrt ε ≤ 1 := by nlinarith only [hse2, hε1, hse]
      have hsA := Real.sqrt_nonneg A
      have : c ≤ Real.sqrt A := by
        rw [hcdef]
        calc Real.sqrt A * ε ^ (1 / 4 : ℝ) * L ^ (-(1 / 2 : ℝ)) ≤ Real.sqrt A * 1 * 1 := by
              gcongr
          _ = Real.sqrt A := by ring
      linarith
    have hdiff : ∀ s, 0 ≤ s → Y s - fNq (N : ℕ∞) (2 + ς) 1 s ≤ Real.sqrt ε * (C + Real.sqrt A + 1) := by
      intro s hs
      rw [hV s hs]
      have hconv : oneSidedConv (fun v => Real.sqrt (Y v)) (svdKernel 2 N) s ≤ C + Real.sqrt A + 1 := by
        have hcY : ContinuousOn (fun v => Real.sqrt (Y v)) (Ici 0) := hY_cont.sqrt
        have ii := lg_conv_ii (fun v => Real.sqrt (Y v)) (svdKernel 2 N) s hs hcY hg_cont
        have hgi : IntervalIntegrable (svdKernel 2 N) volume 0 s :=
          ((svmain_cont 2 N).continuousOn).intervalIntegrable
        calc oneSidedConv (fun v => Real.sqrt (Y v)) (svdKernel 2 N) s
            ≤ ∫ t in (0:ℝ)..s, (C + c + Real.sqrt ε) * svdKernel 2 N t := by
              apply intervalIntegral.integral_mono_on hs ii (hgi.const_mul _)
              intro t ht
              exact mul_le_mul_of_nonneg_right (hΦ (s - t) (by linarith [ht.2])) (hg_nn t ht.1)
          _ = (C + c + Real.sqrt ε) * ∫ t in (0:ℝ)..s, svdKernel 2 N t :=
              intervalIntegral.integral_const_mul _ _
          _ ≤ (C + c + Real.sqrt ε) * 1 :=
              mul_le_mul_of_nonneg_left (hg_mass s hs) (by positivity)
          _ ≤ _ := by linarith
      have := mul_le_mul_of_nonneg_left hconv hse.le
      linarith
    have hb1 : ∀ s ∈ Icc (0:ℝ) uh, Real.sqrt (Y s) - Real.sqrt (fNq (N : ℕ∞) (2 + ς) 1 s)
        ≤ ε ^ (1 / 4 : ℝ) * Real.sqrt (C + Real.sqrt A + 1) := by
      intro s hs
      have hf0 : 0 ≤ fNq (N : ℕ∞) (2 + ς) 1 s := by
        unfold fNq; have := lg_Lsum_nonneg N (2 + ς) 1 s; positivity
      have h1 := lg_sqrt_sub (Y s) _ hf0 (hsand s hs.1).1
      refine h1.trans ?_
      calc Real.sqrt (Y s - fNq (N : ℕ∞) (2 + ς) 1 s)
          ≤ Real.sqrt (Real.sqrt ε * (C + Real.sqrt A + 1)) := Real.sqrt_le_sqrt (hdiff s hs.1)
        _ = _ := by
            rw [Real.sqrt_mul hse.le, Real.sqrt_eq_rpow (Real.sqrt ε), Real.sqrt_eq_rpow ε,
              ← Real.rpow_mul hε.le]
            norm_num
    have hb2 : ∀ s ∈ Icc (0:ℝ) uh, Real.sqrt (Y s) - Real.sqrt (fNq (N : ℕ∞) (2 + ς) 1 s)
        ≤ C * (1 + s) ^ (-r) + c * (1 + s) ^ (-(1 / 2 : ℝ)) + Real.sqrt ε := by
      intro s hs
      have := Real.sqrt_nonneg (fNq (N : ℕ∞) (2 + ς) 1 s)
      linarith [hsqrtY s hs.1]
    have hφ : ContinuousOn (fun s => Real.sqrt (Y s) - Real.sqrt (fNq (N : ℕ∞) (2 + ς) 1 s)) (Icc 0 (max X Z - 1)) :=
      ((hY_cont.mono (fun s hs => hs.1)).sqrt).sub (hcf.mono (fun s hs => hs.1)).sqrt
    have hR0 : 0 ≤ ε ^ (-(1 / 8 : ℝ)) := Real.rpow_nonneg hε.le _
    have hBc : 0 ≤ ε ^ (1 / 4 : ℝ) * Real.sqrt (C + Real.sqrt A + 1) := by positivity
    have hE := lg_Eabs C r c (Real.sqrt ε) (ε ^ (-(1 / 8 : ℝ)))
      (ε ^ (1 / 4 : ℝ) * Real.sqrt (C + Real.sqrt A + 1)) (max X Z - 1) uh hC hr hc0 hse.le hR0 hBc
      hu0 huH _ hφ hb1 hb2
    have htail := lg_tail ε C r A L hε hC hr0 hA0 hLpos
    have hR : ε ^ (-(1 / 8 : ℝ)) * (ε ^ (1 / 4 : ℝ) * Real.sqrt (C + Real.sqrt A + 1))
        = ε ^ (1 / 8 : ℝ) * Real.sqrt (C + Real.sqrt A + 1) := by
      rw [← mul_assoc, ← Real.rpow_add hε]; norm_num
    unfold logGlobalErrBound
    simp only
    rw [hR] at hE
    linarith

/-- Part (iii) of `lem:app-phase-log-global`, the closing "in particular": `ℰ → 0` along sequences
with `N → ∞`, `B ≥ N` and `ε ↓ 0`. For each `n` the matched \SignSVD model at level `εseq n`
(with dimensions `Nseq n`, `Bseq n`) and a Volterra solution `QS n` are given (eventually in `n`,
as in part (ii)); the error `ℰ_n = ∫_0^{û_n}(√Y_n-√f_n)` at the first hit tends to `0`. The
lower-level hypotheses of part (ii) (`N ≥ e^{L_0}`, `ε < min{1,C²,1/(8T)}`) hold eventually,
since `N → ∞` and `ε → 0`, so they are not assumed.

`lem:app-phase-log-global`, snapshot `cr-2026-10-23`. Source: `section.tex` l.2430–2449 (environment).

LaTeX (verbatim, `section.tex` l.2430–2449):
```latex
\begin{lemma}[\SignSVD kernel, $\alpha=2$, $\texp>1$]\label{lem:app-phase-log-global}
Let $\alpha=2$ and $\texp>1$, so $q=1$ and $r\defeq r_{\text{s-SVD}}>1$. Put
$C\defeq C_{p,1}$, $K\defeq2E_{2,1}$, $L_N\defeq H_N(1)$ and
\[
\mathsf A_0\defeq\frac{CK}{r-1}\Big(\frac{2^r}e+2\Big),\qquad L_0\defeq\max\Big\{1,\frac{4K}{2-\sqrt2}\Big\},
\]
\[
h(u)\defeq C(1+u)^{-r},\qquad \mathsf w(u)\defeq\sqrt{\mathsf A_0}\,\epsilon^{1/4}L_N^{-1/2}(1+u)^{-1/2} .
\]
Let $N\ge e^{L_0}$, $B\ge N$ and $\epsilon>0$. Then
$f_{N,1}\le Y_{\text{s-SVD}}\le(h+\mathsf w+\sqrt\epsilon)^2$ on $[0,\infty)$. If moreover
$T\ge4$ and $0<\epsilon<\min\{1,C^2,1/(8T)\}$, the first hit satisfies
$0<\hat u\le H\defeq\max\{(2C/\sqrt\epsilon)^{1/r},4\mathsf A_0/(L_N\sqrt\epsilon)\}-1$, and
\begin{multline*}
0\le\mathcal E\le\epsilon^{1/8}\sqrt{C+\sqrt{\mathsf A_0}+1}+\frac C{r-1}\big(1+\epsilon^{-1/8}\big)^{1-r}\\
+2\sqrt{\mathsf A_0}(2C)^{1/(2r)}L_N^{-1/2}\epsilon^{(r-1)/(4r)}+(2C)^{1/r}\epsilon^{(r-1)/(2r)}+\frac{8\mathsf A_0}{L_N} .
\end{multline*}
In particular $\mathcal E\to0$ along every sequence with $N\to\infty$ and
$\epsilon\downarrow0$.
\end{lemma}
``` -/
theorem lem_app_phase_log_global_iii (ς : ℝ) (hς : 1 < ς) (T : ℝ) (hT : 4 ≤ T)
    (Nseq Bseq : ℕ → ℕ) (εseq : ℕ → ℝ)
    (hN : Tendsto Nseq atTop atTop) (hNB : ∀ n, Nseq n ≤ Bseq n)
    (hε : Tendsto εseq atTop (𝓝[>] 0))
    (mS : ∀ n, RowModel (Fin (Nseq n))) (QS : ∀ n, ℝ → ℝ)
    (hmS : ∀ᶠ n in atTop, IsMatchedModel (svdArrays 2 ς (Nseq n) (Bseq n)) (mS n) (εseq n))
    (hQS : ∀ᶠ n in atTop, IsVolterraSol (mS n) (QS n)) :
    Tendsto (fun n => phaseErr (fun u => QS n (svdT0 (Nseq n) (Bseq n) * u))
        (fNq (Nseq n : ℕ∞) (2 + ς) 1)
        (firstHit (fun u => QS n (svdT0 (Nseq n) (Bseq n) * u)) (T * εseq n)).toReal)
      atTop (𝓝 0) := by
  have hε0 : Tendsto εseq atTop (𝓝 0) := hε.mono_right nhdsWithin_le_nhds
  have hr1 : 1 < rq (2 + ς) 1 := lg_rgt ς hς
  have hr0 : 0 < rq (2 + ς) 1 - 1 := by linarith
  have hrpos : 0 < rq (2 + ς) 1 := by linarith
  have hL : Tendsto (fun n => Hsum 1 (Nseq n)) atTop atTop := by
    have hlog : Tendsto (fun n => Real.log ((Nseq n : ℝ) + 1)) atTop atTop :=
      Real.tendsto_log_atTop.comp
        ((tendsto_natCast_atTop_atTop.comp hN).atTop_add tendsto_const_nhds)
    refine tendsto_atTop_mono' atTop ?_ hlog
    filter_upwards [hN.eventually_ge_atTop 1] with n hn
    exact lg_Hlog (Nseq n) hn
  have hNe : ∀ᶠ n in atTop, Real.exp logGlobalL0 ≤ (Nseq n : ℝ) := by
    filter_upwards [hN.eventually_ge_atTop ⌈Real.exp logGlobalL0⌉₊] with n hn
    exact le_trans (Nat.le_ceil _) (by exact_mod_cast hn)
  have hεpos : ∀ᶠ n in atTop, 0 < εseq n := by
    filter_upwards [hε.eventually eventually_mem_nhdsWithin] with n hn
    exact hn
  have hCpos : 0 < Cpq (2 + ς) 1 := lg_Cpos ς hς
  have hmin : (0 : ℝ) < min 1 (min (Cpq (2 + ς) 1 ^ 2) (1 / (8 * T))) :=
    lt_min one_pos (lt_min (pow_pos hCpos 2) (div_pos one_pos (by linarith)))
  have hεlt : ∀ᶠ n in atTop, εseq n < min 1 (min (Cpq (2 + ς) 1 ^ 2) (1 / (8 * T))) :=
    hε0.eventually (gt_mem_nhds hmin)
  have hpow : ∀ p : ℝ, 0 < p → Tendsto (fun n => εseq n ^ p) atTop (𝓝 0) := by
    intro p hp
    have h := hε0.rpow_const (Or.inr hp.le)
    rwa [Real.zero_rpow hp.ne'] at h
  have hE : Tendsto (fun n => logGlobalErrBound (Nseq n) ς (εseq n)) atTop (𝓝 0) := by
    have t1 : Tendsto (fun n => εseq n ^ (1 / 8 : ℝ) *
        Real.sqrt (Cpq (2 + ς) 1 + Real.sqrt (logGlobalA0 ς) + 1)) atTop (𝓝 0) := by
      simpa using (hpow (1 / 8) (by norm_num)).mul_const
        (Real.sqrt (Cpq (2 + ς) 1 + Real.sqrt (logGlobalA0 ς) + 1))
    have hs : Tendsto (fun n => εseq n ^ (-(1 / 8 : ℝ))) atTop atTop :=
      (tendsto_rpow_neg_nhdsGT_zero (y := -(1 / 8 : ℝ)) (by norm_num)).comp hε
    have hs1 : Tendsto (fun n => 1 + εseq n ^ (-(1 / 8 : ℝ))) atTop atTop :=
      tendsto_const_nhds.add_atTop hs
    have hp : Tendsto (fun n => (1 + εseq n ^ (-(1 / 8 : ℝ))) ^ (1 - rq (2 + ς) 1))
        atTop (𝓝 0) := by
      have h := (tendsto_rpow_neg_atTop (y := rq (2 + ς) 1 - 1) hr0).comp hs1
      have he : (-(rq (2 + ς) 1 - 1)) = 1 - rq (2 + ς) 1 := by ring
      rw [he] at h
      exact h
    have t2 : Tendsto (fun n => Cpq (2 + ς) 1 / (rq (2 + ς) 1 - 1) *
        (1 + εseq n ^ (-(1 / 8 : ℝ))) ^ (1 - rq (2 + ς) 1)) atTop (𝓝 0) := by
      simpa using hp.const_mul (Cpq (2 + ς) 1 / (rq (2 + ς) 1 - 1))
    have hLi : Tendsto (fun n => Hsum 1 (Nseq n) ^ (-(1 / 2 : ℝ))) atTop (𝓝 0) :=
      (tendsto_rpow_neg_atTop (y := 1 / 2) (by norm_num)).comp hL
    have t3 : Tendsto (fun n => 2 * Real.sqrt (logGlobalA0 ς) * (2 * Cpq (2 + ς) 1) ^ (1 / (2 * rq (2 + ς) 1))
        * Hsum 1 (Nseq n) ^ (-(1 / 2 : ℝ)) * εseq n ^ ((rq (2 + ς) 1 - 1) / (4 * rq (2 + ς) 1)))
        atTop (𝓝 0) := by
      simpa using (hLi.const_mul (2 * Real.sqrt (logGlobalA0 ς) * (2 * Cpq (2 + ς) 1) ^ (1 / (2 * rq (2 + ς) 1)))).mul
        (hpow ((rq (2 + ς) 1 - 1) / (4 * rq (2 + ς) 1)) (div_pos hr0 (by linarith)))
    have t4 : Tendsto (fun n => (2 * Cpq (2 + ς) 1) ^ (1 / rq (2 + ς) 1) *
        εseq n ^ ((rq (2 + ς) 1 - 1) / (2 * rq (2 + ς) 1))) atTop (𝓝 0) := by
      simpa using (hpow ((rq (2 + ς) 1 - 1) / (2 * rq (2 + ς) 1))
        (div_pos hr0 (by linarith))).const_mul ((2 * Cpq (2 + ς) 1) ^ (1 / rq (2 + ς) 1))
    have t5 : Tendsto (fun n => 8 * logGlobalA0 ς / Hsum 1 (Nseq n)) atTop (𝓝 0) :=
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => 8 * logGlobalA0 ς) atTop
        (𝓝 (8 * logGlobalA0 ς))).div_atTop hL
    have h := (((t1.add t2).add t3).add t4).add t5
    simp only [add_zero] at h
    exact h
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hE ?_ ?_
  · filter_upwards [hNe, hεpos, hεlt, hmS, hQS] with n h1 h2 h3 h4 h5
    exact (lem_app_phase_log_global_ii ς hς (Nseq n) (Bseq n) h1 (hNB n) T (εseq n) hT h2 h3
      (mS n) h4 (QS n) h5).2.2.1
  · filter_upwards [hNe, hεpos, hεlt, hmS, hQS] with n h1 h2 h3 h4 h5
    exact (lem_app_phase_log_global_ii ς hς (Nseq n) (Bseq n) h1 (hNB n) T (εseq n) hT h2 h3
      (mS n) h4 (QS n) h5).2.2.2

end Muon.Phase

end
