import Mathlib

/-!
# Oversampled profile layer (Appendix G2, work package L-G2.1)

Source of record: snapshot `cr-2026-10-22`, `sections/12-oversampled/section.tex`.
Scope: `lem:app-os-root`, `def:app-os-objects` (parts (i)–(iii); part (iv) belongs to L-G2.7),
`lem:app-os-profile`, `lem:app-os-compare`, `lem:app-os-scale`. Mathlib only; no project imports.

Measure representation (card §2, decision Q1): a Borel probability measure on `[0,∞)` is a
`ν : Measure ℝ` with `[IsProbabilityMeasure ν]` and the hypothesis `ν (Set.Iio 0) = 0`.
The objects are defined for every `ν : Measure ℝ`; the theorems assume the support hypothesis.
-/

open MeasureTheory Set

namespace Muon.Oversampled

noncomputable section

/-- Participation function `m_ν(c) = ∫ x/(c+x) ν(dx)` for `c > 0` (`eqn:app-os-m`, the
definition in the standing setup of the section). -/
def mNu (ν : Measure ℝ) (c : ℝ) : ℝ :=
  ∫ x, x / (c + x) ∂ν

/-- Extension `m_ν(ŝ/b) := ∫ b x/(ŝ + b x) ν(dx)` (`eqn:app-os-m`). For `b > 0` it agrees with
`mNu ν (ŝ / b)`; it vanishes at `b = 0`. Kept separate from `mNu`, as the card requires. -/
def mNuExt (ν : Measure ℝ) (sh b : ℝ) : ℝ :=
  ∫ x, b * x / (sh + b * x) ∂ν

/-- Profile root `b_0 = b_0^{ν,r}(ŝ)`, defined as the least `b ∈ [0,1]` with
`1 ≤ b + r m_ν(ŝ/b)`. No proof term is used; that this is the unique root in `(0,1]` is
`lem_app_os_root_i`.

Label `def:app-os-objects`, part (i). Snapshot `cr-2026-10-22`. Statement verbatim:

\begin{definition}[Oversampled objects]\label{def:app-os-objects}
Let $\nu$ be a probability measure and $r>0$.
\begin{enumerate}[label=(\roman*)]
\item The profile root $b_0=b_0^{\nu,r}$ is the function of
\cref{lem:app-os-root}.
\item For $\mu\ge0$ and $\hat\ridge\ge0$, the oversampled drift profile is
\begin{equation}\label{eqn:app-os-profile}
\mathfrak d^{\rm os}_{\nu,r}(\mu;\hat\ridge)\defeq\frac{\sqrt2}{\pi}\int_0^\infty
\frac{b_0(\hat s)\,\mu}{\hat s+b_0(\hat s)\,\mu}\,\dif v,\qquad \hat s=\hat\ridge+v^2 .
\end{equation}
In the square case we write $\mathfrak d^{\rm os}_\nu\defeq\mathfrak d^{\rm os}_{\nu,1}$
and $\mathfrak d^{\rm os}_\nu(\mu)\defeq\mathfrak d^{\rm os}_{\nu,1}(\mu;0)$.
\item The density $\varpi$ on $(0,\infty)$ and the square-root efficiency
$\chi_\nu$ are
\begin{equation}\label{eqn:app-os-chi}
\varpi(y)\defeq\frac2\pi\,\frac{\sqrt y}{(1+y)^2},\qquad
\chi_\nu(\mu)\defeq\int_0^\infty\varpi(y)\sqrt{1-m_\nu(\mu y)}\,\dif y\qquad(\mu>0).
\end{equation}
\item At a finite dimension, the empirical spectral probability measure of
$\Sigmaout$, the rescaled ridge and the small parameter are
\begin{equation}\label{eqn:app-os-eps}
\begin{gathered}
\hat\nu_{\mathrm{out}}\defeq\frac1{\Nout}\sum_{k=1}^{\Nout}\delta_{\mu_k}=\frac{\nu_{\mathrm{out}}}{\gout},\qquad
\hat\ridge\defeq\frac{\ridge}{\sw2\gin}\quad(\ridge\ge0),\\
\epsilon_{\rm os}\defeq3(1-\bmom^2)\gin=3(1+\bmom)^2\frac{\Nin}{B_{\rm eff}} .
\end{gathered}
\end{equation}
\end{enumerate}
\end{definition}
-/
def profileRoot (ν : Measure ℝ) (r sh : ℝ) : ℝ :=
  sInf {b : ℝ | b ∈ Icc (0 : ℝ) 1 ∧ 1 ≤ b + r * mNuExt ν sh b}

/-- Integrand of `eqn:app-os-profile` in the variable `v`, with `ŝ = ρ̂ + v²`. -/
def dOsIntegrand (ν : Measure ℝ) (r mu rh v : ℝ) : ℝ :=
  profileRoot ν r (rh + v ^ 2) * mu / ((rh + v ^ 2) + profileRoot ν r (rh + v ^ 2) * mu)

/-- Oversampled drift profile `𝔡^os_{ν,r}(μ; ρ̂) = (√2/π) ∫_0^∞ … dv` (`eqn:app-os-profile`).
The integral is over `Ioi 0`, so `ŝ = ρ̂ + v² > 0` throughout (card §6.2).

Label `def:app-os-objects`, part (ii). Snapshot `cr-2026-10-22`. Statement verbatim:

\begin{definition}[Oversampled objects]\label{def:app-os-objects}
Let $\nu$ be a probability measure and $r>0$.
\begin{enumerate}[label=(\roman*)]
\item The profile root $b_0=b_0^{\nu,r}$ is the function of
\cref{lem:app-os-root}.
\item For $\mu\ge0$ and $\hat\ridge\ge0$, the oversampled drift profile is
\begin{equation}\label{eqn:app-os-profile}
\mathfrak d^{\rm os}_{\nu,r}(\mu;\hat\ridge)\defeq\frac{\sqrt2}{\pi}\int_0^\infty
\frac{b_0(\hat s)\,\mu}{\hat s+b_0(\hat s)\,\mu}\,\dif v,\qquad \hat s=\hat\ridge+v^2 .
\end{equation}
In the square case we write $\mathfrak d^{\rm os}_\nu\defeq\mathfrak d^{\rm os}_{\nu,1}$
and $\mathfrak d^{\rm os}_\nu(\mu)\defeq\mathfrak d^{\rm os}_{\nu,1}(\mu;0)$.
\item The density $\varpi$ on $(0,\infty)$ and the square-root efficiency
$\chi_\nu$ are
\begin{equation}\label{eqn:app-os-chi}
\varpi(y)\defeq\frac2\pi\,\frac{\sqrt y}{(1+y)^2},\qquad
\chi_\nu(\mu)\defeq\int_0^\infty\varpi(y)\sqrt{1-m_\nu(\mu y)}\,\dif y\qquad(\mu>0).
\end{equation}
\item At a finite dimension, the empirical spectral probability measure of
$\Sigmaout$, the rescaled ridge and the small parameter are
\begin{equation}\label{eqn:app-os-eps}
\begin{gathered}
\hat\nu_{\mathrm{out}}\defeq\frac1{\Nout}\sum_{k=1}^{\Nout}\delta_{\mu_k}=\frac{\nu_{\mathrm{out}}}{\gout},\qquad
\hat\ridge\defeq\frac{\ridge}{\sw2\gin}\quad(\ridge\ge0),\\
\epsilon_{\rm os}\defeq3(1-\bmom^2)\gin=3(1+\bmom)^2\frac{\Nin}{B_{\rm eff}} .
\end{gathered}
\end{equation}
\end{enumerate}
\end{definition}
-/
def dOs (ν : Measure ℝ) (r mu rh : ℝ) : ℝ :=
  (Real.sqrt 2 / Real.pi) * ∫ v in Ioi (0 : ℝ), dOsIntegrand ν r mu rh v

/-- Square case `𝔡^os_ν(μ) := 𝔡^os_{ν,1}(μ; 0)`.

Label `def:app-os-objects`, part (ii). Snapshot `cr-2026-10-22`. Statement verbatim:

\begin{definition}[Oversampled objects]\label{def:app-os-objects}
Let $\nu$ be a probability measure and $r>0$.
\begin{enumerate}[label=(\roman*)]
\item The profile root $b_0=b_0^{\nu,r}$ is the function of
\cref{lem:app-os-root}.
\item For $\mu\ge0$ and $\hat\ridge\ge0$, the oversampled drift profile is
\begin{equation}\label{eqn:app-os-profile}
\mathfrak d^{\rm os}_{\nu,r}(\mu;\hat\ridge)\defeq\frac{\sqrt2}{\pi}\int_0^\infty
\frac{b_0(\hat s)\,\mu}{\hat s+b_0(\hat s)\,\mu}\,\dif v,\qquad \hat s=\hat\ridge+v^2 .
\end{equation}
In the square case we write $\mathfrak d^{\rm os}_\nu\defeq\mathfrak d^{\rm os}_{\nu,1}$
and $\mathfrak d^{\rm os}_\nu(\mu)\defeq\mathfrak d^{\rm os}_{\nu,1}(\mu;0)$.
\item The density $\varpi$ on $(0,\infty)$ and the square-root efficiency
$\chi_\nu$ are
\begin{equation}\label{eqn:app-os-chi}
\varpi(y)\defeq\frac2\pi\,\frac{\sqrt y}{(1+y)^2},\qquad
\chi_\nu(\mu)\defeq\int_0^\infty\varpi(y)\sqrt{1-m_\nu(\mu y)}\,\dif y\qquad(\mu>0).
\end{equation}
\item At a finite dimension, the empirical spectral probability measure of
$\Sigmaout$, the rescaled ridge and the small parameter are
\begin{equation}\label{eqn:app-os-eps}
\begin{gathered}
\hat\nu_{\mathrm{out}}\defeq\frac1{\Nout}\sum_{k=1}^{\Nout}\delta_{\mu_k}=\frac{\nu_{\mathrm{out}}}{\gout},\qquad
\hat\ridge\defeq\frac{\ridge}{\sw2\gin}\quad(\ridge\ge0),\\
\epsilon_{\rm os}\defeq3(1-\bmom^2)\gin=3(1+\bmom)^2\frac{\Nin}{B_{\rm eff}} .
\end{gathered}
\end{equation}
\end{enumerate}
\end{definition}
-/
def dOsSq (ν : Measure ℝ) (mu : ℝ) : ℝ :=
  dOs ν 1 mu 0

/-- Density `ϖ(y) = (2/π) √y / (1+y)²` on `(0,∞)` (`eqn:app-os-chi`).

Label `def:app-os-objects`, part (iii). Snapshot `cr-2026-10-22`. Statement verbatim:

\begin{definition}[Oversampled objects]\label{def:app-os-objects}
Let $\nu$ be a probability measure and $r>0$.
\begin{enumerate}[label=(\roman*)]
\item The profile root $b_0=b_0^{\nu,r}$ is the function of
\cref{lem:app-os-root}.
\item For $\mu\ge0$ and $\hat\ridge\ge0$, the oversampled drift profile is
\begin{equation}\label{eqn:app-os-profile}
\mathfrak d^{\rm os}_{\nu,r}(\mu;\hat\ridge)\defeq\frac{\sqrt2}{\pi}\int_0^\infty
\frac{b_0(\hat s)\,\mu}{\hat s+b_0(\hat s)\,\mu}\,\dif v,\qquad \hat s=\hat\ridge+v^2 .
\end{equation}
In the square case we write $\mathfrak d^{\rm os}_\nu\defeq\mathfrak d^{\rm os}_{\nu,1}$
and $\mathfrak d^{\rm os}_\nu(\mu)\defeq\mathfrak d^{\rm os}_{\nu,1}(\mu;0)$.
\item The density $\varpi$ on $(0,\infty)$ and the square-root efficiency
$\chi_\nu$ are
\begin{equation}\label{eqn:app-os-chi}
\varpi(y)\defeq\frac2\pi\,\frac{\sqrt y}{(1+y)^2},\qquad
\chi_\nu(\mu)\defeq\int_0^\infty\varpi(y)\sqrt{1-m_\nu(\mu y)}\,\dif y\qquad(\mu>0).
\end{equation}
\item At a finite dimension, the empirical spectral probability measure of
$\Sigmaout$, the rescaled ridge and the small parameter are
\begin{equation}\label{eqn:app-os-eps}
\begin{gathered}
\hat\nu_{\mathrm{out}}\defeq\frac1{\Nout}\sum_{k=1}^{\Nout}\delta_{\mu_k}=\frac{\nu_{\mathrm{out}}}{\gout},\qquad
\hat\ridge\defeq\frac{\ridge}{\sw2\gin}\quad(\ridge\ge0),\\
\epsilon_{\rm os}\defeq3(1-\bmom^2)\gin=3(1+\bmom)^2\frac{\Nin}{B_{\rm eff}} .
\end{gathered}
\end{equation}
\end{enumerate}
\end{definition}
-/
def varpi (y : ℝ) : ℝ :=
  (2 / Real.pi) * Real.sqrt y / (1 + y) ^ 2

/-- Square-root efficiency `χ_ν(μ) = ∫_0^∞ ϖ(y) √(1 - m_ν(μ y)) dy`, for `μ > 0`
(`eqn:app-os-chi`).

Label `def:app-os-objects`, part (iii). Snapshot `cr-2026-10-22`. Statement verbatim:

\begin{definition}[Oversampled objects]\label{def:app-os-objects}
Let $\nu$ be a probability measure and $r>0$.
\begin{enumerate}[label=(\roman*)]
\item The profile root $b_0=b_0^{\nu,r}$ is the function of
\cref{lem:app-os-root}.
\item For $\mu\ge0$ and $\hat\ridge\ge0$, the oversampled drift profile is
\begin{equation}\label{eqn:app-os-profile}
\mathfrak d^{\rm os}_{\nu,r}(\mu;\hat\ridge)\defeq\frac{\sqrt2}{\pi}\int_0^\infty
\frac{b_0(\hat s)\,\mu}{\hat s+b_0(\hat s)\,\mu}\,\dif v,\qquad \hat s=\hat\ridge+v^2 .
\end{equation}
In the square case we write $\mathfrak d^{\rm os}_\nu\defeq\mathfrak d^{\rm os}_{\nu,1}$
and $\mathfrak d^{\rm os}_\nu(\mu)\defeq\mathfrak d^{\rm os}_{\nu,1}(\mu;0)$.
\item The density $\varpi$ on $(0,\infty)$ and the square-root efficiency
$\chi_\nu$ are
\begin{equation}\label{eqn:app-os-chi}
\varpi(y)\defeq\frac2\pi\,\frac{\sqrt y}{(1+y)^2},\qquad
\chi_\nu(\mu)\defeq\int_0^\infty\varpi(y)\sqrt{1-m_\nu(\mu y)}\,\dif y\qquad(\mu>0).
\end{equation}
\item At a finite dimension, the empirical spectral probability measure of
$\Sigmaout$, the rescaled ridge and the small parameter are
\begin{equation}\label{eqn:app-os-eps}
\begin{gathered}
\hat\nu_{\mathrm{out}}\defeq\frac1{\Nout}\sum_{k=1}^{\Nout}\delta_{\mu_k}=\frac{\nu_{\mathrm{out}}}{\gout},\qquad
\hat\ridge\defeq\frac{\ridge}{\sw2\gin}\quad(\ridge\ge0),\\
\epsilon_{\rm os}\defeq3(1-\bmom^2)\gin=3(1+\bmom)^2\frac{\Nin}{B_{\rm eff}} .
\end{gathered}
\end{equation}
\end{enumerate}
\end{definition}
-/
def sqrtEff (ν : Measure ℝ) (mu : ℝ) : ℝ :=
  ∫ y in Ioi (0 : ℝ), varpi y * Real.sqrt (1 - mNu ν (mu * y))

/-- Pushforward `ν^a` of `ν` under `x ↦ a x` (the notation of `lem:app-os-scale`). -/
def scaleMeasure (ν : Measure ℝ) (a : ℝ) : Measure ℝ :=
  ν.map (fun x : ℝ => a * x)

private lemma os_ae_nonneg {ν : Measure ℝ} (hν : ν (Iio 0) = 0) : ∀ᵐ x ∂ν, 0 ≤ x := by
  rw [ae_iff]
  have h : {a : ℝ | ¬ (0 ≤ a)} = Iio 0 := by ext; simp
  rw [h]; exact hν

private lemma os_integrand_bounds {ν : Measure ℝ} (hν : ν (Iio 0) = 0) {sh b : ℝ}
    (hsh : 0 < sh) (hb : 0 ≤ b) :
    ∀ᵐ x ∂ν, 0 ≤ b * x / (sh + b * x) ∧ b * x / (sh + b * x) ≤ 1 := by
  filter_upwards [os_ae_nonneg hν] with x hx
  have h1 : 0 ≤ b * x := mul_nonneg hb hx
  have h2 : 0 < sh + b * x := by linarith
  exact ⟨div_nonneg h1 h2.le, (div_le_one h2).2 (by linarith)⟩

private lemma os_integrand_integrable {ν : Measure ℝ} [IsProbabilityMeasure ν]
    (hν : ν (Iio 0) = 0) {sh b : ℝ} (hsh : 0 < sh) (hb : 0 ≤ b) :
    Integrable (fun x : ℝ => b * x / (sh + b * x)) ν := by
  refine Integrable.mono' (integrable_const (1 : ℝ)) ?_ ?_
  · exact (by fun_prop : Measurable fun x : ℝ => b * x / (sh + b * x)).aestronglyMeasurable
  · filter_upwards [os_integrand_bounds hν hsh hb] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg hx.1]
    exact hx.2

private lemma os_mNuExt_nonneg {ν : Measure ℝ} (hν : ν (Iio 0) = 0) {sh b : ℝ}
    (hsh : 0 < sh) (hb : 0 ≤ b) : 0 ≤ mNuExt ν sh b := by
  unfold mNuExt
  exact integral_nonneg_of_ae (by filter_upwards [os_integrand_bounds hν hsh hb] with x hx using hx.1)

private lemma os_mNuExt_mono {ν : Measure ℝ} [IsProbabilityMeasure ν] (hν : ν (Iio 0) = 0)
    {sh b₁ b₂ : ℝ} (hsh : 0 < sh) (hb₁ : 0 ≤ b₁) (hb12 : b₁ ≤ b₂) :
    mNuExt ν sh b₁ ≤ mNuExt ν sh b₂ := by
  unfold mNuExt
  have hb2 : 0 ≤ b₂ := hb₁.trans hb12
  refine integral_mono_of_nonneg ?_ (os_integrand_integrable hν hsh hb2) ?_
  · filter_upwards [os_integrand_bounds hν hsh hb₁] with x hx using hx.1
  · filter_upwards [os_ae_nonneg hν] with x hx
    have h1 : 0 < sh + b₁ * x := by nlinarith [mul_nonneg hb₁ hx]
    have h2 : 0 < sh + b₂ * x := by nlinarith [mul_nonneg hb2 hx]
    show b₁ * x / (sh + b₁ * x) ≤ b₂ * x / (sh + b₂ * x)
    rw [div_le_div_iff₀ h1 h2]
    nlinarith [mul_nonneg (mul_nonneg (sub_nonneg.2 hb12) hx) hsh.le]

private lemma os_F_strict {ν : Measure ℝ} [IsProbabilityMeasure ν] (hν : ν (Iio 0) = 0)
    {r sh : ℝ} (hr : 0 < r) (hsh : 0 < sh) {b₁ b₂ : ℝ} (hb₁ : 0 ≤ b₁) (h12 : b₁ < b₂) :
    b₁ + r * mNuExt ν sh b₁ < b₂ + r * mNuExt ν sh b₂ := by
  have := mul_le_mul_of_nonneg_left (os_mNuExt_mono hν hsh hb₁ h12.le) hr.le
  linarith

private lemma os_mNuExt_continuousOn {ν : Measure ℝ} [IsProbabilityMeasure ν]
    (hν : ν (Iio 0) = 0) {sh : ℝ} (hsh : 0 < sh) :
    ContinuousOn (mNuExt ν sh) (Icc (0 : ℝ) 1) := by
  unfold mNuExt
  refine continuousOn_of_dominated (F := fun b x : ℝ => b * x / (sh + b * x))
    (bound := fun _ => (1 : ℝ)) ?_ ?_ (integrable_const _) ?_
  · intro b hb
    exact (os_integrand_integrable hν hsh hb.1).aestronglyMeasurable
  · intro b hb
    filter_upwards [os_integrand_bounds hν hsh hb.1] with x hx
    rw [Real.norm_eq_abs, abs_le]
    constructor <;> linarith [hx.1, hx.2]
  · filter_upwards [os_ae_nonneg hν] with x hx
    refine ContinuousOn.div ?_ ?_ ?_
    · fun_prop
    · fun_prop
    · intro b hb
      show sh + b * x ≠ 0
      have := mul_nonneg hb.1 hx
      exact (by linarith : (0 : ℝ) < sh + b * x).ne'

private lemma os_F_le {ν : Measure ℝ} [IsProbabilityMeasure ν] (hν : ν (Iio 0) = 0)
    {r sh : ℝ} (hr : 0 < r) (hsh : 0 < sh) {b₁ b₂ : ℝ} (hb₁ : 0 ≤ b₁) (h12 : b₁ ≤ b₂) :
    b₁ + r * mNuExt ν sh b₁ ≤ b₂ + r * mNuExt ν sh b₂ := by
  have := mul_le_mul_of_nonneg_left (os_mNuExt_mono hν hsh hb₁ h12) hr.le
  linarith

private lemma os_mNuExt_anti {ν : Measure ℝ} [IsProbabilityMeasure ν] (hν : ν (Iio 0) = 0)
    {s₁ s₂ b : ℝ} (hs₁ : 0 < s₁) (h12 : s₁ ≤ s₂) (hb : 0 ≤ b) :
    mNuExt ν s₂ b ≤ mNuExt ν s₁ b := by
  unfold mNuExt
  refine integral_mono_of_nonneg ?_ (os_integrand_integrable hν hs₁ hb) ?_
  · filter_upwards [os_integrand_bounds hν (hs₁.trans_le h12) hb] with x hx using hx.1
  · filter_upwards [os_ae_nonneg hν] with x hx
    have hx' : 0 ≤ b * x := mul_nonneg hb hx
    have h1 : 0 < s₁ + b * x := by linarith
    have h2 : 0 < s₂ + b * x := by linarith
    show b * x / (s₂ + b * x) ≤ b * x / (s₁ + b * x)
    rw [div_le_div_iff₀ h2 h1]
    nlinarith [mul_nonneg hx' (sub_nonneg.2 h12)]

private lemma os_mNuExt_continuousOn_sh {ν : Measure ℝ} [IsProbabilityMeasure ν]
    (hν : ν (Iio 0) = 0) {b : ℝ} (hb : 0 ≤ b) :
    ContinuousOn (fun sh : ℝ => mNuExt ν sh b) (Ioi (0 : ℝ)) := by
  unfold mNuExt
  refine continuousOn_of_dominated (F := fun sh x : ℝ => b * x / (sh + b * x))
    (bound := fun _ => (1 : ℝ)) ?_ ?_ (integrable_const _) ?_
  · intro sh hsh
    exact (os_integrand_integrable hν (Set.mem_Ioi.mp hsh) hb).aestronglyMeasurable
  · intro sh hsh
    filter_upwards [os_integrand_bounds hν (Set.mem_Ioi.mp hsh) hb] with x hx
    rw [Real.norm_eq_abs, abs_le]
    constructor <;> linarith [hx.1, hx.2]
  · filter_upwards [os_ae_nonneg hν] with x hx
    refine ContinuousOn.div ?_ ?_ ?_
    · fun_prop
    · fun_prop
    · intro sh hsh
      show sh + b * x ≠ 0
      have h1 := mul_nonneg hb hx
      have h2 : (0 : ℝ) < sh := Set.mem_Ioi.mp hsh
      exact (by linarith : (0 : ℝ) < sh + b * x).ne'

/-- Label `lem:app-os-root`, part (i) (existence and uniqueness of the profile root, and
identification of `profileRoot` as that root). Snapshot `cr-2026-10-22`. Statement verbatim:

\begin{lemma}[The profile equation]\label{lem:app-os-root}
Let $\nu$ be a probability measure and $r>0$. For every $\hat s>0$ the
equation
\begin{equation}\label{eqn:app-os-root}
b+r\,m_\nu(\hat s/b)=1
\end{equation}
has exactly one solution $b=b_0(\hat s)$ in $(0,1]$. The function $b_0$ is
continuous and nondecreasing on $(0,\infty)$.
\end{lemma}
-/
theorem lem_app_os_root_i (ν : Measure ℝ) [IsProbabilityMeasure ν] (hν : ν (Iio 0) = 0)
    {r : ℝ} (hr : 0 < r) {sh : ℝ} (hsh : 0 < sh) :
    (profileRoot ν r sh ∈ Ioc (0 : ℝ) 1 ∧
      profileRoot ν r sh + r * mNuExt ν sh (profileRoot ν r sh) = 1) ∧
    ∀ b ∈ Ioc (0 : ℝ) 1, b + r * mNuExt ν sh b = 1 → b = profileRoot ν r sh := by
  have hcont : ContinuousOn (fun b : ℝ => b + r * mNuExt ν sh b) (Icc (0 : ℝ) 1) :=
    continuousOn_id.add (continuousOn_const.mul (os_mNuExt_continuousOn hν hsh))
  have hF0 : (0 : ℝ) + r * mNuExt ν sh 0 = 0 := by
    have h0 : mNuExt ν sh 0 = 0 := by unfold mNuExt; simp
    rw [h0]; ring
  have hF1 : (1 : ℝ) ≤ 1 + r * mNuExt ν sh 1 := by
    have := mul_nonneg hr.le (os_mNuExt_nonneg hν hsh zero_le_one)
    linarith
  have hmem : (1 : ℝ) ∈ Icc ((fun b : ℝ => b + r * mNuExt ν sh b) 0)
      ((fun b : ℝ => b + r * mNuExt ν sh b) 1) :=
    ⟨by show (0 : ℝ) + r * mNuExt ν sh 0 ≤ 1; rw [hF0]; norm_num,
     by show (1 : ℝ) ≤ 1 + r * mNuExt ν sh 1; exact hF1⟩
  obtain ⟨c, hc, hFc⟩ := intermediate_value_Icc zero_le_one hcont hmem
  have hFc' : c + r * mNuExt ν sh c = 1 := hFc
  have hcpos : 0 < c := lt_of_le_of_ne hc.1 (fun h => by subst h; linarith [hF0, hFc'])
  have hS : IsLeast {b : ℝ | b ∈ Icc (0 : ℝ) 1 ∧ 1 ≤ b + r * mNuExt ν sh b} c := by
    refine ⟨⟨hc, by linarith [hFc']⟩, ?_⟩
    intro b hb
    by_contra hlt
    push_neg at hlt
    have := os_F_strict hν hr hsh hb.1.1 hlt
    linarith [hb.2]
  have hprof : profileRoot ν r sh = c := hS.csInf_eq
  rw [hprof]
  refine ⟨⟨⟨hcpos, hc.2⟩, hFc'⟩, ?_⟩
  intro b hb hbeq
  rcases lt_trichotomy b c with h | h | h
  · exfalso
    linarith [os_F_strict hν hr hsh hb.1.le h]
  · exact h
  · exfalso
    linarith [os_F_strict hν hr hsh hcpos.le h]

/-- Label `lem:app-os-root`, part (ii) (continuity of the profile root on `(0,∞)`).
Snapshot `cr-2026-10-22`. Statement verbatim:

\begin{lemma}[The profile equation]\label{lem:app-os-root}
Let $\nu$ be a probability measure and $r>0$. For every $\hat s>0$ the
equation
\begin{equation}\label{eqn:app-os-root}
b+r\,m_\nu(\hat s/b)=1
\end{equation}
has exactly one solution $b=b_0(\hat s)$ in $(0,1]$. The function $b_0$ is
continuous and nondecreasing on $(0,\infty)$.
\end{lemma}
-/
theorem lem_app_os_root_ii (ν : Measure ℝ) [IsProbabilityMeasure ν] (hν : ν (Iio 0) = 0)
    {r : ℝ} (hr : 0 < r) :
    ContinuousOn (profileRoot ν r) (Ioi (0 : ℝ)) := by
  intro sh0 hsh0
  have hsh0' : 0 < sh0 := hsh0
  apply ContinuousAt.continuousWithinAt
  unfold ContinuousAt
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨⟨hcmem, hceq⟩, -⟩ := lem_app_os_root_i ν hν hr hsh0'
  generalize profileRoot ν r sh0 = c at hcmem hceq ⊢
  have hc0 : 0 < c := hcmem.1
  obtain ⟨η, hη⟩ : ∃ η : ℝ, η = min (ε / 2) (c / 2) := ⟨_, rfl⟩
  have hη0 : 0 < η := by rw [hη]; exact lt_min (half_pos hε) (half_pos hc0)
  have hηε : η < ε := by
    rw [hη]; exact lt_of_le_of_lt (min_le_left _ _) (half_lt_self hε)
  have hηc : η < c := by
    rw [hη]; exact lt_of_le_of_lt (min_le_right _ _) (half_lt_self hc0)
  have hcont : ∀ b : ℝ, 0 ≤ b → ContinuousAt (fun sh : ℝ => b + r * mNuExt ν sh b) sh0 := by
    intro b hb
    apply ContinuousAt.add continuousAt_const
    apply ContinuousAt.mul continuousAt_const
    exact (os_mNuExt_continuousOn_sh hν hb).continuousAt (Ioi_mem_nhds hsh0)
  have hFup0 : 1 + η ≤ (c + η) + r * mNuExt ν sh0 (c + η) := by
    have hm := os_mNuExt_mono hν hsh0' hc0.le (le_add_of_nonneg_right hη0.le : c ≤ c + η)
    have := mul_le_mul_of_nonneg_left hm hr.le
    linarith
  have hdn0 : (c - η) + r * mNuExt ν sh0 (c - η) ≤ 1 - η := by
    have hm := os_mNuExt_mono hν hsh0' (by linarith : 0 ≤ c - η) (by linarith : c - η ≤ c)
    have := mul_le_mul_of_nonneg_left hm hr.le
    linarith
  have hev_up : ∀ᶠ sh in nhds sh0, 1 < (c + η) + r * mNuExt ν sh (c + η) :=
    ContinuousAt.eventually_lt (f := fun _ : ℝ => (1 : ℝ))
      (g := fun sh : ℝ => (c + η) + r * mNuExt ν sh (c + η))
      continuousAt_const (hcont (c + η) (by linarith)) (by show (1 : ℝ) < _; linarith)
  have hev_dn : ∀ᶠ sh in nhds sh0, (c - η) + r * mNuExt ν sh (c - η) < 1 :=
    ContinuousAt.eventually_lt (f := fun sh : ℝ => (c - η) + r * mNuExt ν sh (c - η))
      (g := fun _ : ℝ => (1 : ℝ))
      (hcont (c - η) (by linarith)) continuousAt_const (by show _ < (1 : ℝ); linarith)
  filter_upwards [hev_up, hev_dn, Ioi_mem_nhds hsh0'] with sh h1 h2 h3
  have hsh : 0 < sh := h3
  obtain ⟨⟨hmem, heq⟩, -⟩ := lem_app_os_root_i ν hν hr hsh
  generalize profileRoot ν r sh = c' at hmem heq ⊢
  have hlt1 : c' < c + η := by
    by_contra hge
    push_neg at hge
    have := os_F_le hν hr hsh (by linarith : 0 ≤ c + η) hge
    linarith
  have hlt2 : c - η < c' := by
    by_contra hle
    push_neg at hle
    have := os_F_le hν hr hsh hmem.1.le hle
    linarith
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith

/-- Label `lem:app-os-root`, part (iii) (monotonicity of the profile root on `(0,∞)`).
Snapshot `cr-2026-10-22`. Statement verbatim:

\begin{lemma}[The profile equation]\label{lem:app-os-root}
Let $\nu$ be a probability measure and $r>0$. For every $\hat s>0$ the
equation
\begin{equation}\label{eqn:app-os-root}
b+r\,m_\nu(\hat s/b)=1
\end{equation}
has exactly one solution $b=b_0(\hat s)$ in $(0,1]$. The function $b_0$ is
continuous and nondecreasing on $(0,\infty)$.
\end{lemma}
-/
theorem lem_app_os_root_iii (ν : Measure ℝ) [IsProbabilityMeasure ν] (hν : ν (Iio 0) = 0)
    {r : ℝ} (hr : 0 < r) :
    MonotoneOn (profileRoot ν r) (Ioi (0 : ℝ)) := by
  intro s1 hs1 s2 hs2 h12
  have hs1' : 0 < s1 := hs1
  have hs2' : 0 < s2 := hs2
  unfold profileRoot
  apply csInf_le_csInf
  · exact ⟨0, fun b hb => hb.1.1⟩
  · refine ⟨1, ⟨zero_le_one, le_rfl⟩, ?_⟩
    have := mul_nonneg hr.le (os_mNuExt_nonneg hν hs2' zero_le_one)
    linarith
  · intro b hb
    obtain ⟨hbI, hbF⟩ := hb
    have := mul_le_mul_of_nonneg_left (os_mNuExt_anti hν hs1' h12 hbI.1) hr.le
    exact ⟨hbI, by linarith⟩

private lemma os_root_mem {ν : Measure ℝ} [IsProbabilityMeasure ν] (hν : ν (Iio 0) = 0)
    {r : ℝ} (hr : 0 < r) {sh : ℝ} (hsh : 0 < sh) :
    0 < profileRoot ν r sh ∧ profileRoot ν r sh ≤ 1 := by
  obtain ⟨⟨h, -⟩, -⟩ := lem_app_os_root_i ν hν hr hsh
  exact ⟨h.1, h.2⟩

private lemma os_frac_bound {s b mu v : ℝ} (hv2 : 0 < v ^ 2) (hs : v ^ 2 ≤ s) (hs0 : 0 < s)
    (hb0 : 0 ≤ b) (hb1 : b ≤ 1) (hmu : 0 ≤ mu) :
    0 ≤ b * mu / (s + b * mu) ∧ b * mu / (s + b * mu) ≤ mu / (v ^ 2 + mu) := by
  have hbm : 0 ≤ b * mu := mul_nonneg hb0 hmu
  have hd : 0 < s + b * mu := by linarith
  have hdv : 0 < v ^ 2 + mu := by linarith
  refine ⟨div_nonneg hbm hd.le, ?_⟩
  have h1 : b * mu / (s + b * mu) ≤ mu / (s + mu) := by
    rw [div_le_div_iff₀ hd (by linarith)]
    nlinarith [mul_nonneg (mul_nonneg hmu hs0.le) (sub_nonneg.2 hb1)]
  have h2 : mu / (s + mu) ≤ mu / (v ^ 2 + mu) := by
    rw [div_le_div_iff₀ (by linarith) hdv]
    nlinarith [mul_le_mul_of_nonneg_left hs hmu]
  exact h1.trans h2

private lemma os_majorant_integrable {mu : ℝ} (hmu : 0 ≤ mu) :
    IntegrableOn (fun v : ℝ => mu / (v ^ 2 + mu)) (Ioi (0 : ℝ)) := by
  rcases hmu.eq_or_lt with h | h
  · subst h
    simp
  · have hs : Real.sqrt mu ≠ 0 := (Real.sqrt_pos.2 h).ne'
    have hm0 : mu ≠ 0 := h.ne'
    have heq : (fun v : ℝ => mu / (v ^ 2 + mu)) =
        fun v : ℝ => (fun x : ℝ => (1 + x ^ 2)⁻¹) (v / Real.sqrt mu) := by
      funext v
      have hd : v ^ 2 + mu ≠ 0 := (by nlinarith [sq_nonneg v] : (0 : ℝ) < v ^ 2 + mu).ne'
      simp only
      rw [div_pow, Real.sq_sqrt hmu]
      field_simp
      ring
    rw [heq]
    exact (integrable_inv_one_add_sq.comp_div hs).integrableOn

private lemma os_frac_cont {s : Set ℝ} {p c : ℝ → ℝ} (hp : ContinuousOn p s)
    (hc : ContinuousOn c s) (hp0 : ∀ x ∈ s, 0 < p x) (hc0 : ∀ x ∈ s, 0 ≤ c x)
    {mu : ℝ} (hmu : 0 ≤ mu) :
    ContinuousOn (fun x => c x * mu / (p x + c x * mu)) s := by
  refine ContinuousOn.div (hc.mul continuousOn_const) (hp.add (hc.mul continuousOn_const)) ?_
  intro x hx
  have h1 := hp0 x hx
  have h2 := mul_nonneg (hc0 x hx) hmu
  show p x + c x * mu ≠ 0
  exact ne_of_gt (by linarith)

private lemma os_dOsIntegrand_contOn_v {ν : Measure ℝ} [IsProbabilityMeasure ν]
    (hν : ν (Iio 0) = 0) {r : ℝ} (hr : 0 < r) {mu : ℝ} (hmu : 0 ≤ mu) {rh : ℝ}
    (hrh : 0 ≤ rh) :
    ContinuousOn (dOsIntegrand ν r mu rh) (Ioi (0 : ℝ)) := by
  have hp : ContinuousOn (fun v : ℝ => rh + v ^ 2) (Ioi (0 : ℝ)) := by fun_prop
  have hp0 : ∀ v ∈ Ioi (0 : ℝ), 0 < rh + v ^ 2 := by
    intro v hv
    have hv' : 0 < v := hv
    have := pow_pos hv' 2
    linarith
  have hc : ContinuousOn (fun v : ℝ => profileRoot ν r (rh + v ^ 2)) (Ioi (0 : ℝ)) :=
    (lem_app_os_root_ii ν hν hr).comp hp (fun v hv => hp0 v hv)
  have hc0 : ∀ v ∈ Ioi (0 : ℝ), 0 ≤ profileRoot ν r (rh + v ^ 2) := fun v hv =>
    (os_root_mem hν hr (hp0 v hv)).1.le
  exact os_frac_cont hp hc hp0 hc0 hmu

private lemma os_dOsIntegrand_contOn_rh {ν : Measure ℝ} [IsProbabilityMeasure ν]
    (hν : ν (Iio 0) = 0) {r : ℝ} (hr : 0 < r) {mu : ℝ} (hmu : 0 ≤ mu) {v : ℝ} (hv : 0 < v) :
    ContinuousOn (fun rh : ℝ => dOsIntegrand ν r mu rh v) (Ici (0 : ℝ)) := by
  have hp : ContinuousOn (fun rh : ℝ => rh + v ^ 2) (Ici (0 : ℝ)) := by fun_prop
  have hp0 : ∀ rh ∈ Ici (0 : ℝ), 0 < rh + v ^ 2 := by
    intro rh hrh
    have hrh' : 0 ≤ rh := hrh
    have := pow_pos hv 2
    linarith
  have hc : ContinuousOn (fun rh : ℝ => profileRoot ν r (rh + v ^ 2)) (Ici (0 : ℝ)) :=
    (lem_app_os_root_ii ν hν hr).comp hp (fun rh hrh => hp0 rh hrh)
  have hc0 : ∀ rh ∈ Ici (0 : ℝ), 0 ≤ profileRoot ν r (rh + v ^ 2) := fun rh hrh =>
    (os_root_mem hν hr (hp0 rh hrh)).1.le
  exact os_frac_cont hp hc hp0 hc0 hmu

private lemma os_dOs_bound {ν : Measure ℝ} [IsProbabilityMeasure ν] (hν : ν (Iio 0) = 0)
    {r : ℝ} (hr : 0 < r) {mu : ℝ} (hmu : 0 ≤ mu) {rh v : ℝ} (hrh : 0 ≤ rh) (hv : 0 < v) :
    0 ≤ dOsIntegrand ν r mu rh v ∧ dOsIntegrand ν r mu rh v ≤ mu / (v ^ 2 + mu) := by
  have hv2 : 0 < v ^ 2 := pow_pos hv 2
  have hs0 : 0 < rh + v ^ 2 := by linarith
  obtain ⟨hb0, hb1⟩ := os_root_mem hν hr hs0
  unfold dOsIntegrand
  exact os_frac_bound hv2 (by linarith) hs0 hb0.le hb1 hmu

private lemma os_frac_le_div {s b mu : ℝ} (hs : 0 < s) (hb0 : 0 ≤ b) (hb1 : b ≤ 1)
    (hmu : 0 ≤ mu) : b * mu / (s + b * mu) ≤ mu / s := by
  have hd : 0 < s + b * mu := by nlinarith [mul_nonneg hb0 hmu]
  rw [div_le_div_iff₀ hd hs]
  nlinarith [mul_nonneg (mul_nonneg hmu hs.le) (sub_nonneg.2 hb1), mul_nonneg (mul_nonneg hmu hmu) hb0]

private lemma os_integrable_inv_add_sq {a : ℝ} (ha : 0 < a) :
    IntegrableOn (fun v : ℝ => (a + v ^ 2)⁻¹) (Ioi (0 : ℝ)) := by
  have hs : Real.sqrt a ≠ 0 := (Real.sqrt_pos.2 ha).ne'
  have hsq : Real.sqrt a ^ 2 = a := Real.sq_sqrt ha.le
  have heq : (fun v : ℝ => (a + v ^ 2)⁻¹) =
      fun v : ℝ => a⁻¹ * (fun x : ℝ => (1 + x ^ 2)⁻¹) (v / Real.sqrt a) := by
    funext v
    have hd : a + v ^ 2 ≠ 0 := (by nlinarith [sq_nonneg v] : (0 : ℝ) < a + v ^ 2).ne'
    simp only
    rw [div_pow, hsq]
    field_simp
  rw [heq]
  exact ((integrable_inv_one_add_sq.comp_div hs).const_mul a⁻¹).integrableOn

private lemma os_integrable_mul_inv_add_sq {a c : ℝ} (ha : 0 < a) :
    IntegrableOn (fun v : ℝ => c * (a + v ^ 2)⁻¹) (Ioi (0 : ℝ)) := by
  have h := os_integrable_inv_add_sq ha
  unfold IntegrableOn at h ⊢
  exact h.const_mul c

private lemma os_int_inv_add_sq {a : ℝ} (ha : 0 < a) :
    ∫ v in Ioi (0 : ℝ), (a + v ^ 2)⁻¹ = Real.pi / (2 * Real.sqrt a) := by
  have hs : 0 < Real.sqrt a := Real.sqrt_pos.2 ha
  have hsq : Real.sqrt a ^ 2 = a := Real.sq_sqrt ha.le
  have h1 : ∫ x in Ioi (0 : ℝ), (a + (Real.sqrt a * x) ^ 2)⁻¹ =
      (Real.sqrt a)⁻¹ • ∫ v in Ioi (0 : ℝ), (a + v ^ 2)⁻¹ := by
    have := integral_comp_mul_left_Ioi (fun v : ℝ => (a + v ^ 2)⁻¹) 0 hs
    simpa only [mul_zero] using this
  have h2 : ∀ x : ℝ, (a + (Real.sqrt a * x) ^ 2)⁻¹ = a⁻¹ * (1 + x ^ 2)⁻¹ := by
    intro x
    have : a + (Real.sqrt a * x) ^ 2 = a * (1 + x ^ 2) := by
      rw [mul_pow, hsq]; ring
    rw [this, mul_inv]
  have h3 : ∫ x in Ioi (0 : ℝ), (a + (Real.sqrt a * x) ^ 2)⁻¹ = a⁻¹ * (Real.pi / 2) := by
    simp_rw [h2]
    rw [integral_const_mul, integral_Ioi_inv_one_add_sq, Real.arctan_zero, sub_zero]
  rw [h3, smul_eq_mul] at h1
  have hI : ∫ v in Ioi (0 : ℝ), (a + v ^ 2)⁻¹ = Real.sqrt a * (a⁻¹ * (Real.pi / 2)) := by
    rw [h1, ← mul_assoc, mul_inv_cancel₀ hs.ne', one_mul]
  have ha_inv : a⁻¹ = (Real.sqrt a)⁻¹ ^ 2 := by
    rw [inv_pow, hsq]
  rw [hI, ha_inv]
  field_simp

private lemma os_dOs_zero (ν : Measure ℝ) (r rh : ℝ) : dOs ν r 0 rh = 0 := by
  simp [dOs, dOsIntegrand]

private lemma os_sqrt_half (mu : ℝ) : Real.sqrt (mu / 2) = Real.sqrt mu * Real.sqrt 2 / 2 := by
  rw [Real.sqrt_div' mu (by norm_num : (0 : ℝ) ≤ 2),
    div_eq_div_iff (Real.sqrt_pos.2 two_pos).ne' two_ne_zero, mul_assoc,
    Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]

private lemma os_final_iv {mu : ℝ} (hpos : 0 < mu) :
    Real.sqrt 2 / Real.pi * (mu * (Real.pi / (2 * Real.sqrt mu))) = Real.sqrt (mu / 2) := by
  have hs : Real.sqrt mu ≠ 0 := (Real.sqrt_pos.2 hpos).ne'
  have hk : mu * (Real.pi / (2 * Real.sqrt mu)) = (mu / Real.sqrt mu) * (Real.pi / 2) := by
    field_simp
  rw [hk, Real.div_sqrt, os_sqrt_half]
  field_simp

private lemma os_final_v {mu rh : ℝ} (hrh : 0 < rh) :
    Real.sqrt 2 / Real.pi * (mu * (Real.pi / (2 * Real.sqrt rh))) =
      mu / Real.sqrt (2 * rh) := by
  have hs : Real.sqrt rh ≠ 0 := (Real.sqrt_pos.2 hrh).ne'
  have h2 : Real.sqrt 2 ≠ 0 := (Real.sqrt_pos.2 two_pos).ne'
  have h22 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2) rh]
  field_simp
  rw [h22]
  ring

/-- Label `lem:app-os-profile`, part (i) (the profile is finite: the integrand is integrable
on `(0,∞)` for every `ρ̂ ≥ 0`). Snapshot `cr-2026-10-22`. Statement verbatim:

\begin{lemma}[Ceilings of the profile]\label{lem:app-os-profile}
Let $\nu$ be a probability measure, $r>0$ and $\mu\ge0$. The profile
$\mathfrak d^{\rm os}_{\nu,r}(\mu;\hat\ridge)$ is finite, continuous in
$\hat\ridge\in[0,\infty)$, positive if and only if $\mu>0$, and
\begin{equation}\label{eqn:app-os-ceiling}
\mathfrak d^{\rm os}_{\nu,r}(\mu;\hat\ridge)\le\sqrt{\mu/2},\qquad
\mathfrak d^{\rm os}_{\nu,r}(\mu;\hat\ridge)\le\frac{\mu}{\sqrt{2\hat\ridge}}\quad(\hat\ridge>0).
\end{equation}
\end{lemma}
-/
theorem lem_app_os_profile_i (ν : Measure ℝ) [IsProbabilityMeasure ν] (hν : ν (Iio 0) = 0)
    {r : ℝ} (hr : 0 < r) {mu : ℝ} (hmu : 0 ≤ mu) :
    ∀ rh : ℝ, 0 ≤ rh → IntegrableOn (dOsIntegrand ν r mu rh) (Ioi (0 : ℝ)) := by
  intro rh hrh
  have hmaj := os_majorant_integrable hmu
  unfold IntegrableOn at hmaj ⊢
  refine Integrable.mono' hmaj ?_ ?_
  · exact (os_dOsIntegrand_contOn_v hν hr hmu hrh).aestronglyMeasurable measurableSet_Ioi
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
    have hv' : 0 < v := hv
    obtain ⟨h0, h1⟩ := os_dOs_bound hν hr hmu hrh hv'
    rw [Real.norm_eq_abs, abs_of_nonneg h0]
    exact h1

/-- Label `lem:app-os-profile`, part (ii) (continuity in `ρ̂ ∈ [0,∞)`).
Snapshot `cr-2026-10-22`. Statement verbatim:

\begin{lemma}[Ceilings of the profile]\label{lem:app-os-profile}
Let $\nu$ be a probability measure, $r>0$ and $\mu\ge0$. The profile
$\mathfrak d^{\rm os}_{\nu,r}(\mu;\hat\ridge)$ is finite, continuous in
$\hat\ridge\in[0,\infty)$, positive if and only if $\mu>0$, and
\begin{equation}\label{eqn:app-os-ceiling}
\mathfrak d^{\rm os}_{\nu,r}(\mu;\hat\ridge)\le\sqrt{\mu/2},\qquad
\mathfrak d^{\rm os}_{\nu,r}(\mu;\hat\ridge)\le\frac{\mu}{\sqrt{2\hat\ridge}}\quad(\hat\ridge>0).
\end{equation}
\end{lemma}
-/
theorem lem_app_os_profile_ii (ν : Measure ℝ) [IsProbabilityMeasure ν] (hν : ν (Iio 0) = 0)
    {r : ℝ} (hr : 0 < r) {mu : ℝ} (hmu : 0 ≤ mu) :
    ContinuousOn (fun rh : ℝ => dOs ν r mu rh) (Ici (0 : ℝ)) := by
  have hmaj := os_majorant_integrable hmu
  have hint : ContinuousOn (fun rh : ℝ => ∫ v in Ioi (0 : ℝ), dOsIntegrand ν r mu rh v)
      (Ici (0 : ℝ)) := by
    refine continuousOn_of_dominated (bound := fun v : ℝ => mu / (v ^ 2 + mu)) ?_ ?_ hmaj ?_
    · intro rh hrh
      exact (os_dOsIntegrand_contOn_v hν hr hmu hrh).aestronglyMeasurable measurableSet_Ioi
    · intro rh hrh
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
      have hv' : 0 < v := hv
      obtain ⟨h0, h1⟩ := os_dOs_bound hν hr hmu hrh hv'
      show ‖dOsIntegrand ν r mu rh v‖ ≤ mu / (v ^ 2 + mu)
      rw [Real.norm_eq_abs, abs_of_nonneg h0]
      exact h1
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
      have hv' : 0 < v := hv
      exact os_dOsIntegrand_contOn_rh hν hr hmu hv'
  show ContinuousOn (fun rh : ℝ => (Real.sqrt 2 / Real.pi) *
    ∫ v in Ioi (0 : ℝ), dOsIntegrand ν r mu rh v) (Ici (0 : ℝ))
  exact continuousOn_const.mul hint

/-- Label `lem:app-os-profile`, part (iii) (positive if and only if `μ > 0`).
Snapshot `cr-2026-10-22`. Statement verbatim:

\begin{lemma}[Ceilings of the profile]\label{lem:app-os-profile}
Let $\nu$ be a probability measure, $r>0$ and $\mu\ge0$. The profile
$\mathfrak d^{\rm os}_{\nu,r}(\mu;\hat\ridge)$ is finite, continuous in
$\hat\ridge\in[0,\infty)$, positive if and only if $\mu>0$, and
\begin{equation}\label{eqn:app-os-ceiling}
\mathfrak d^{\rm os}_{\nu,r}(\mu;\hat\ridge)\le\sqrt{\mu/2},\qquad
\mathfrak d^{\rm os}_{\nu,r}(\mu;\hat\ridge)\le\frac{\mu}{\sqrt{2\hat\ridge}}\quad(\hat\ridge>0).
\end{equation}
\end{lemma}
-/
theorem lem_app_os_profile_iii (ν : Measure ℝ) [IsProbabilityMeasure ν] (hν : ν (Iio 0) = 0)
    {r : ℝ} (hr : 0 < r) {mu : ℝ} (hmu : 0 ≤ mu) :
    ∀ rh : ℝ, 0 ≤ rh → (0 < dOs ν r mu rh ↔ 0 < mu) := by
  intro rh hrh
  have hzero : mu = 0 → dOs ν r mu rh = 0 := by
    rintro rfl
    exact os_dOs_zero ν r rh
  constructor
  · intro hpos
    by_contra hc
    have hmu0 : mu = 0 := le_antisymm (not_lt.1 hc) hmu
    rw [hzero hmu0] at hpos
    exact lt_irrefl _ hpos
  · intro hpos
    have hnn : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))]
        (fun v : ℝ => dOsIntegrand ν r mu rh v) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
      have hv' : 0 < v := hv
      exact (os_dOs_bound hν hr hmu hrh hv').1
    have hI : 0 < ∫ v in Ioi (0 : ℝ), dOsIntegrand ν r mu rh v := by
      rw [setIntegral_pos_iff_support_of_nonneg_ae hnn (lem_app_os_profile_i ν hν hr hmu rh hrh)]
      have hsub : Ioi (0 : ℝ) ⊆ Function.support (fun v : ℝ => dOsIntegrand ν r mu rh v) ∩
          Ioi (0 : ℝ) := by
        intro v hv
        have hv' : 0 < v := hv
        have hs : 0 < rh + v ^ 2 := by
          have := pow_pos hv' 2
          linarith
        obtain ⟨hb0, -⟩ := os_root_mem hν hr hs
        refine ⟨?_, hv⟩
        show dOsIntegrand ν r mu rh v ≠ 0
        unfold dOsIntegrand
        exact (div_pos (mul_pos hb0 hpos) (by linarith [mul_pos hb0 hpos])).ne'
      exact lt_of_lt_of_le (by simp) (measure_mono hsub)
    unfold dOs
    exact mul_pos (div_pos (Real.sqrt_pos.2 two_pos) Real.pi_pos) hI

/-- Label `lem:app-os-profile`, part (iv) (first ceiling `𝔡^os ≤ √(μ/2)`).
Snapshot `cr-2026-10-22`. Statement verbatim:

\begin{lemma}[Ceilings of the profile]\label{lem:app-os-profile}
Let $\nu$ be a probability measure, $r>0$ and $\mu\ge0$. The profile
$\mathfrak d^{\rm os}_{\nu,r}(\mu;\hat\ridge)$ is finite, continuous in
$\hat\ridge\in[0,\infty)$, positive if and only if $\mu>0$, and
\begin{equation}\label{eqn:app-os-ceiling}
\mathfrak d^{\rm os}_{\nu,r}(\mu;\hat\ridge)\le\sqrt{\mu/2},\qquad
\mathfrak d^{\rm os}_{\nu,r}(\mu;\hat\ridge)\le\frac{\mu}{\sqrt{2\hat\ridge}}\quad(\hat\ridge>0).
\end{equation}
\end{lemma}
-/
theorem lem_app_os_profile_iv (ν : Measure ℝ) [IsProbabilityMeasure ν] (hν : ν (Iio 0) = 0)
    {r : ℝ} (hr : 0 < r) {mu : ℝ} (hmu : 0 ≤ mu) :
    ∀ rh : ℝ, 0 ≤ rh → dOs ν r mu rh ≤ Real.sqrt (mu / 2) := by
  intro rh hrh
  rcases hmu.eq_or_lt with h0 | hpos
  · subst h0
    rw [os_dOs_zero ν r rh]
    simp
  · have hbd : ∀ v ∈ Ioi (0 : ℝ), dOsIntegrand ν r mu rh v ≤ mu * (mu + v ^ 2)⁻¹ := by
      intro v hv
      have hv' : 0 < v := hv
      rw [← div_eq_mul_inv, add_comm]
      exact (os_dOs_bound hν hr hmu hrh hv').2
    have hint := setIntegral_mono_on (lem_app_os_profile_i ν hν hr hmu rh hrh)
      (os_integrable_mul_inv_add_sq hpos) measurableSet_Ioi hbd
    rw [integral_const_mul, os_int_inv_add_sq hpos] at hint
    unfold dOs
    calc Real.sqrt 2 / Real.pi * ∫ v in Ioi (0 : ℝ), dOsIntegrand ν r mu rh v
        ≤ Real.sqrt 2 / Real.pi * (mu * (Real.pi / (2 * Real.sqrt mu))) :=
          mul_le_mul_of_nonneg_left hint (by positivity)
      _ = Real.sqrt (mu / 2) := os_final_iv hpos

/-- Label `lem:app-os-profile`, part (v) (second ceiling `𝔡^os ≤ μ/√(2ρ̂)`, for `ρ̂ > 0`).
Snapshot `cr-2026-10-22`. Statement verbatim:

\begin{lemma}[Ceilings of the profile]\label{lem:app-os-profile}
Let $\nu$ be a probability measure, $r>0$ and $\mu\ge0$. The profile
$\mathfrak d^{\rm os}_{\nu,r}(\mu;\hat\ridge)$ is finite, continuous in
$\hat\ridge\in[0,\infty)$, positive if and only if $\mu>0$, and
\begin{equation}\label{eqn:app-os-ceiling}
\mathfrak d^{\rm os}_{\nu,r}(\mu;\hat\ridge)\le\sqrt{\mu/2},\qquad
\mathfrak d^{\rm os}_{\nu,r}(\mu;\hat\ridge)\le\frac{\mu}{\sqrt{2\hat\ridge}}\quad(\hat\ridge>0).
\end{equation}
\end{lemma}
-/
theorem lem_app_os_profile_v (ν : Measure ℝ) [IsProbabilityMeasure ν] (hν : ν (Iio 0) = 0)
    {r : ℝ} (hr : 0 < r) {mu : ℝ} (hmu : 0 ≤ mu) :
    ∀ rh : ℝ, 0 < rh → dOs ν r mu rh ≤ mu / Real.sqrt (2 * rh) := by
  intro rh hrh
  have hbd : ∀ v ∈ Ioi (0 : ℝ), dOsIntegrand ν r mu rh v ≤ mu * (rh + v ^ 2)⁻¹ := by
    intro v hv
    have hv' : 0 < v := hv
    have hs : 0 < rh + v ^ 2 := by
      have := pow_pos hv' 2
      linarith
    obtain ⟨hb0, hb1⟩ := os_root_mem hν hr hs
    unfold dOsIntegrand
    rw [← div_eq_mul_inv]
    exact os_frac_le_div hs hb0.le hb1 hmu
  have hint := setIntegral_mono_on (lem_app_os_profile_i ν hν hr hmu rh hrh.le)
    (os_integrable_mul_inv_add_sq hrh) measurableSet_Ioi hbd
  rw [integral_const_mul, os_int_inv_add_sq hrh] at hint
  unfold dOs
  calc Real.sqrt 2 / Real.pi * ∫ v in Ioi (0 : ℝ), dOsIntegrand ν r mu rh v
      ≤ Real.sqrt 2 / Real.pi * (mu * (Real.pi / (2 * Real.sqrt rh))) :=
        mul_le_mul_of_nonneg_left hint (by positivity)
    _ = mu / Real.sqrt (2 * rh) := os_final_v hrh

private lemma os_Q_mono {s μ x y : ℝ} (hs : 0 < s) (hμ : 0 ≤ μ) (hx : 0 ≤ x) (hxy : x ≤ y) :
    x * μ / (s + x * μ) ≤ y * μ / (s + y * μ) := by
  have hxm : 0 ≤ x * μ := mul_nonneg hx hμ
  have hym : 0 ≤ y * μ := mul_nonneg (hx.trans hxy) hμ
  have h1 : 0 < s + x * μ := by linarith
  have h2 : 0 < s + y * μ := by linarith
  rw [div_le_div_iff₀ h1 h2]
  nlinarith [mul_nonneg (mul_nonneg (sub_nonneg.2 hxy) hμ) hs.le]

private lemma os_F_scale {s μ F a : ℝ} (hs : 0 < s) (hμ : 0 ≤ μ) (hF0 : 0 ≤ F) (hF1 : F ≤ 1)
    (ha : 0 ≤ a) :
    F * (a * μ / (s + a * μ)) ≤ (F * a) * μ / (s + (F * a) * μ) := by
  have ham : 0 ≤ a * μ := mul_nonneg ha hμ
  have h1 : 0 < s + a * μ := by linarith
  have hFa : 0 ≤ F * a := mul_nonneg hF0 ha
  have h2 : 0 < s + (F * a) * μ := by nlinarith [mul_nonneg hFa hμ]
  rw [← mul_div_assoc, div_le_div_iff₀ h1 h2]
  have hk : 0 ≤ F * (a * μ) * (a * μ) * (1 - F) :=
    mul_nonneg (mul_nonneg (mul_nonneg hF0 ham) ham) (sub_nonneg.2 hF1)
  nlinarith [hk]

/-- Label `lem:app-os-compare`, part (i) (`F̂ b_0(ŝ) ≤ b ≤ b_0(ŝ)`).
Snapshot `cr-2026-10-22`. Statement verbatim:

\begin{lemma}[Comparison]\label{lem:app-os-compare}
Let $\nu$ be a probability measure, $r>0$, $\hat s>0$ and $\widehat F\in(0,1]$,
and let $b>0$ satisfy $b/\widehat F+r\,m_\nu(\hat s/b)=1$. Then
$\widehat F\,b_0(\hat s)\le b\le b_0(\hat s)$, and for every $\mu\ge0$
\[
\widehat F\,\frac{b_0(\hat s)\,\mu}{\hat s+b_0(\hat s)\,\mu}\le\frac{b\mu}{\hat s+b\mu}
\le\frac{b_0(\hat s)\,\mu}{\hat s+b_0(\hat s)\,\mu}.
\]
\end{lemma}
-/
theorem lem_app_os_compare_i (ν : Measure ℝ) [IsProbabilityMeasure ν] (hν : ν (Iio 0) = 0)
    {r : ℝ} (hr : 0 < r) {sh : ℝ} (hsh : 0 < sh) {Fh b : ℝ}
    (hF : Fh ∈ Ioc (0 : ℝ) 1) (hb : 0 < b) (heq : b / Fh + r * mNuExt ν sh b = 1) :
    Fh * profileRoot ν r sh ≤ b ∧ b ≤ profileRoot ν r sh := by
  have hroot := (lem_app_os_root_i ν hν hr hsh).1
  have hb0 := os_root_mem hν hr hsh
  have hF0 : 0 < Fh := hF.1
  have hF1 : Fh ≤ 1 := hF.2
  have hmb : 0 ≤ mNuExt ν sh b := os_mNuExt_nonneg hν hsh hb.le
  have hrm : 0 ≤ r * mNuExt ν sh b := mul_nonneg hr.le hmb
  have hb_le_bF : b ≤ b / Fh := by
    rw [le_div_iff₀ hF0]
    nlinarith [mul_le_mul_of_nonneg_left hF1 hb.le]
  constructor
  · -- F̂ b_0 ≤ b, via b/F̂ ≥ b_0
    have hb' : profileRoot ν r sh ≤ b / Fh := by
      by_contra h2
      push_neg at h2
      have hpos : 0 ≤ b / Fh := div_nonneg hb.le hF0.le
      have hlt := os_F_strict hν hr hsh hpos h2
      have hm : mNuExt ν sh b ≤ mNuExt ν sh (b / Fh) :=
        os_mNuExt_mono hν hsh hb.le hb_le_bF
      have hm' := mul_le_mul_of_nonneg_left hm hr.le
      linarith [hroot.2]
    rw [mul_comm]
    exact (le_div_iff₀ hF0).1 hb'
  · -- b ≤ b_0, since g(b) ≤ 1 = g(b_0) with g strictly increasing
    by_contra h2
    push_neg at h2
    have hlt := os_F_strict hν hr hsh hb0.1.le h2
    linarith [hroot.2]

/-- Label `lem:app-os-compare`, part (ii) (the two-sided bound of the integrands, for every
`μ ≥ 0`). Snapshot `cr-2026-10-22`. Statement verbatim:

\begin{lemma}[Comparison]\label{lem:app-os-compare}
Let $\nu$ be a probability measure, $r>0$, $\hat s>0$ and $\widehat F\in(0,1]$,
and let $b>0$ satisfy $b/\widehat F+r\,m_\nu(\hat s/b)=1$. Then
$\widehat F\,b_0(\hat s)\le b\le b_0(\hat s)$, and for every $\mu\ge0$
\[
\widehat F\,\frac{b_0(\hat s)\,\mu}{\hat s+b_0(\hat s)\,\mu}\le\frac{b\mu}{\hat s+b\mu}
\le\frac{b_0(\hat s)\,\mu}{\hat s+b_0(\hat s)\,\mu}.
\]
\end{lemma}
-/
theorem lem_app_os_compare_ii (ν : Measure ℝ) [IsProbabilityMeasure ν] (hν : ν (Iio 0) = 0)
    {r : ℝ} (hr : 0 < r) {sh : ℝ} (hsh : 0 < sh) {Fh b : ℝ}
    (hF : Fh ∈ Ioc (0 : ℝ) 1) (hb : 0 < b) (heq : b / Fh + r * mNuExt ν sh b = 1) :
    ∀ mu : ℝ, 0 ≤ mu →
      Fh * (profileRoot ν r sh * mu / (sh + profileRoot ν r sh * mu))
          ≤ b * mu / (sh + b * mu) ∧
        b * mu / (sh + b * mu)
          ≤ profileRoot ν r sh * mu / (sh + profileRoot ν r sh * mu) := by
  intro mu hmu
  obtain ⟨h1, h2⟩ := lem_app_os_compare_i ν hν hr hsh hF hb heq
  have hb0 : 0 ≤ profileRoot ν r sh := (os_root_mem hν hr hsh).1.le
  have hFpos : 0 ≤ Fh := hF.1.le
  constructor
  · calc Fh * (profileRoot ν r sh * mu / (sh + profileRoot ν r sh * mu))
        ≤ (Fh * profileRoot ν r sh) * mu / (sh + (Fh * profileRoot ν r sh) * mu) :=
          os_F_scale hsh hmu hFpos hF.2 hb0
      _ ≤ b * mu / (sh + b * mu) := os_Q_mono hsh hmu (mul_nonneg hFpos hb0) h1
  · exact os_Q_mono hsh hmu hb.le h2

private lemma os_scale_mNuExt (ν : Measure ℝ) {a : ℝ} (ha : 0 < a) (sh b : ℝ) :
    mNuExt (scaleMeasure ν a) (a * sh) b = mNuExt ν sh b := by
  unfold mNuExt scaleMeasure
  rw [integral_map (by fun_prop : Measurable (fun x : ℝ => a * x)).aemeasurable
    (Measurable.aestronglyMeasurable (by fun_prop))]
  congr 1
  funext y
  show b * (a * y) / (a * sh + b * (a * y)) = b * y / (sh + b * y)
  rw [show b * (a * y) = a * (b * y) by ring, show a * sh + a * (b * y) = a * (sh + b * y) by ring,
    mul_div_mul_left _ _ ha.ne']

private lemma os_scale_mNu (ν : Measure ℝ) {a : ℝ} (ha : 0 < a) (c : ℝ) :
    mNu (scaleMeasure ν a) (a * c) = mNu ν c := by
  unfold mNu scaleMeasure
  rw [integral_map (by fun_prop : Measurable (fun x : ℝ => a * x)).aemeasurable
    (Measurable.aestronglyMeasurable (by fun_prop))]
  congr 1
  funext y
  show a * y / (a * c + a * y) = y / (c + y)
  rw [show a * c + a * y = a * (c + y) by ring, mul_div_mul_left _ _ ha.ne']

/-- Label `lem:app-os-scale`, part (i) (`b_0^{ν^a,r}(aŝ) = b_0^{ν,r}(ŝ)`, for `ŝ > 0`).
Snapshot `cr-2026-10-22`. Statement verbatim:

\begin{lemma}[Scale invariance]\label{lem:app-os-scale}
For $a>0$ let $\nu^a$ be the image of a probability measure $\nu$ under
$x\mapsto ax$, and let $r>0$. Then, for $\hat s,c,\mu>0$ and $\hat\ridge\ge0$,
\[
\begin{gathered}
b_0^{\nu^a,r}(a\hat s)=b_0^{\nu,r}(\hat s),\qquad
\mathfrak d^{\rm os}_{\nu^a,r}(a\mu;a\hat\ridge)=\sqrt a\,\mathfrak d^{\rm os}_{\nu,r}(\mu;\hat\ridge),\\
m_{\nu^a}(ac)=m_\nu(c),\qquad
\chi_{\nu^a}(a\mu)=\chi_\nu(\mu).
\end{gathered}
\]
\end{lemma}
-/
theorem lem_app_os_scale_i (ν : Measure ℝ) [IsProbabilityMeasure ν] (hν : ν (Iio 0) = 0)
    {r : ℝ} (hr : 0 < r) {a : ℝ} (ha : 0 < a) {sh : ℝ} (hsh : 0 < sh) :
    profileRoot (scaleMeasure ν a) r (a * sh) = profileRoot ν r sh := by
  unfold profileRoot
  simp only [os_scale_mNuExt ν ha]

/-- Label `lem:app-os-scale`, part (ii) (`𝔡^os_{ν^a,r}(aμ; aρ̂) = √a 𝔡^os_{ν,r}(μ; ρ̂)`,
for `μ > 0`, `ρ̂ ≥ 0`). Snapshot `cr-2026-10-22`. Statement verbatim:

\begin{lemma}[Scale invariance]\label{lem:app-os-scale}
For $a>0$ let $\nu^a$ be the image of a probability measure $\nu$ under
$x\mapsto ax$, and let $r>0$. Then, for $\hat s,c,\mu>0$ and $\hat\ridge\ge0$,
\[
\begin{gathered}
b_0^{\nu^a,r}(a\hat s)=b_0^{\nu,r}(\hat s),\qquad
\mathfrak d^{\rm os}_{\nu^a,r}(a\mu;a\hat\ridge)=\sqrt a\,\mathfrak d^{\rm os}_{\nu,r}(\mu;\hat\ridge),\\
m_{\nu^a}(ac)=m_\nu(c),\qquad
\chi_{\nu^a}(a\mu)=\chi_\nu(\mu).
\end{gathered}
\]
\end{lemma}
-/
theorem lem_app_os_scale_ii (ν : Measure ℝ) [IsProbabilityMeasure ν] (hν : ν (Iio 0) = 0)
    {r : ℝ} (hr : 0 < r) {a : ℝ} (ha : 0 < a) {mu : ℝ} (hmu : 0 < mu) :
    ∀ rh : ℝ, 0 ≤ rh →
      dOs (scaleMeasure ν a) r (a * mu) (a * rh) = Real.sqrt a * dOs ν r mu rh := by
  intro rh hrh
  set s := Real.sqrt a with hs_def
  have hs_pos : 0 < s := Real.sqrt_pos.2 ha
  have hs2 : s ^ 2 = a := Real.sq_sqrt ha.le
  have hpt : ∀ w : ℝ, 0 < w →
      dOsIntegrand (scaleMeasure ν a) r (a * mu) (a * rh) (s * w) = dOsIntegrand ν r mu rh w := by
    intro w hw
    have hw2 : 0 < w ^ 2 := pow_pos hw 2
    have hpos : 0 < rh + w ^ 2 := by linarith
    have harg : a * rh + (s * w) ^ 2 = a * (rh + w ^ 2) := by
      rw [mul_pow, hs2]; ring
    have key : ∀ G : ℝ, G * (a * mu) / (a * (rh + w ^ 2) + G * (a * mu))
        = G * mu / ((rh + w ^ 2) + G * mu) := by
      intro G
      rw [show G * (a * mu) = a * (G * mu) by ring,
        show a * (rh + w ^ 2) + a * (G * mu) = a * ((rh + w ^ 2) + G * mu) by ring,
        mul_div_mul_left _ _ ha.ne']
    unfold dOsIntegrand
    rw [harg, lem_app_os_scale_i ν hν hr ha hpos]
    exact key _
  have hc : ∫ x in Ioi (0 : ℝ), dOsIntegrand (scaleMeasure ν a) r (a * mu) (a * rh) (s * x)
      = s⁻¹ • ∫ x in Ioi (0 : ℝ), dOsIntegrand (scaleMeasure ν a) r (a * mu) (a * rh) x := by
    have := integral_comp_mul_left_Ioi (fun v => dOsIntegrand (scaleMeasure ν a) r (a * mu) (a * rh) v) 0 hs_pos
    rw [mul_zero] at this
    exact this
  have hc2 : ∫ x in Ioi (0 : ℝ), dOsIntegrand (scaleMeasure ν a) r (a * mu) (a * rh) (s * x)
      = ∫ x in Ioi (0 : ℝ), dOsIntegrand ν r mu rh x :=
    setIntegral_congr_fun measurableSet_Ioi (fun w hw => hpt w hw)
  have hint : ∫ v in Ioi (0 : ℝ), dOsIntegrand (scaleMeasure ν a) r (a * mu) (a * rh) v
      = s * ∫ w in Ioi (0 : ℝ), dOsIntegrand ν r mu rh w := by
    rw [hc2, smul_eq_mul] at hc
    rw [hc, ← mul_assoc, mul_inv_cancel₀ hs_pos.ne', one_mul]
  unfold dOs
  rw [hint]
  ring

/-- Label `lem:app-os-scale`, part (iii) (`m_{ν^a}(ac) = m_ν(c)`, for `c > 0`).
Snapshot `cr-2026-10-22`. Statement verbatim:

\begin{lemma}[Scale invariance]\label{lem:app-os-scale}
For $a>0$ let $\nu^a$ be the image of a probability measure $\nu$ under
$x\mapsto ax$, and let $r>0$. Then, for $\hat s,c,\mu>0$ and $\hat\ridge\ge0$,
\[
\begin{gathered}
b_0^{\nu^a,r}(a\hat s)=b_0^{\nu,r}(\hat s),\qquad
\mathfrak d^{\rm os}_{\nu^a,r}(a\mu;a\hat\ridge)=\sqrt a\,\mathfrak d^{\rm os}_{\nu,r}(\mu;\hat\ridge),\\
m_{\nu^a}(ac)=m_\nu(c),\qquad
\chi_{\nu^a}(a\mu)=\chi_\nu(\mu).
\end{gathered}
\]
\end{lemma}
-/
theorem lem_app_os_scale_iii (ν : Measure ℝ) [IsProbabilityMeasure ν] (hν : ν (Iio 0) = 0)
    {r : ℝ} (hr : 0 < r) {a : ℝ} (ha : 0 < a) {c : ℝ} (hc : 0 < c) :
    mNu (scaleMeasure ν a) (a * c) = mNu ν c :=
  os_scale_mNu ν ha c

/-- Label `lem:app-os-scale`, part (iv) (`χ_{ν^a}(aμ) = χ_ν(μ)`, for `μ > 0`).
Snapshot `cr-2026-10-22`. Statement verbatim:

\begin{lemma}[Scale invariance]\label{lem:app-os-scale}
For $a>0$ let $\nu^a$ be the image of a probability measure $\nu$ under
$x\mapsto ax$, and let $r>0$. Then, for $\hat s,c,\mu>0$ and $\hat\ridge\ge0$,
\[
\begin{gathered}
b_0^{\nu^a,r}(a\hat s)=b_0^{\nu,r}(\hat s),\qquad
\mathfrak d^{\rm os}_{\nu^a,r}(a\mu;a\hat\ridge)=\sqrt a\,\mathfrak d^{\rm os}_{\nu,r}(\mu;\hat\ridge),\\
m_{\nu^a}(ac)=m_\nu(c),\qquad
\chi_{\nu^a}(a\mu)=\chi_\nu(\mu).
\end{gathered}
\]
\end{lemma}
-/
theorem lem_app_os_scale_iv (ν : Measure ℝ) [IsProbabilityMeasure ν] (hν : ν (Iio 0) = 0)
    {r : ℝ} (hr : 0 < r) {a : ℝ} (ha : 0 < a) {mu : ℝ} (hmu : 0 < mu) :
    sqrtEff (scaleMeasure ν a) (a * mu) = sqrtEff ν mu := by
  have h : ∀ y : ℝ, mNu (scaleMeasure ν a) (a * mu * y) = mNu ν (mu * y) := fun y => by
    rw [mul_assoc]
    exact os_scale_mNu ν ha (mu * y)
  unfold sqrtEff
  simp only [h]

end

end Muon.Oversampled
