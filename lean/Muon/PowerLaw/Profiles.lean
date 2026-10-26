import Muon.PowerLaw.Continuum
import Muon.PowerLaw.Weights

/-!
# Appendix G: power-law profiles (work package L-G.4)

Snapshot `cr-2026-10-23`. Source: `sections/06-power-law/section.tex`: `def:app-pl-profiles`
(l.776-816), `eqn:app-pl-bulk-small` (l.826-836), `lem:app-pl-Psi` (l.1408-1412),
`lem:app-pl-matching` (l.2087-2090), and the positivity and continuity paragraph of the proof of
volatility (i) (l.2264-2265), stated as a helper for the Gamma profile.

Representation choices:

* `S_α`, `V_α` are `contS`, `contV` of `Muon.PowerLaw.Continuum` (shared with
  `lem:app-pl-continuum`); `c0`, `Kc`, `dAl` are the constants of `eqn:app-pl-constants`.
* The EMA scalar functions are Appendix B's `Lw`, `rW` at `emaW β`; `Qm`, `Efun`, `DLag`, `MLag`
  are those of `Muon.PowerLaw.Weights`.
* The definitions of `Φ`, `G`, `ζ`, `ϑ`, `Δ` are stated for every `α` (the source uses them for
  `α > 1` only); no hypothesis is built into a definition.
* `t_α(u,u) = (α-1)u/α` is the special value of the quotient, selected by `if u = v`.
* "Finite" means `IntervalIntegrable` for the integrals that define the profiles.
-/

set_option linter.style.longLine false

open MeasureTheory Filter Topology Set Asymptotics
open Muon.DetEquiv

namespace Muon.PowerLaw

/-!
## The profile definitions

Verbatim source of `def:app-pl-profiles` (l.776-816). The per-definition docstrings below cite the
displays they implement.

\begin{definition}[Profiles]\label{def:app-pl-profiles}
Let $S_\alpha(V)\defeq\int_0^1V(V+t^\alpha)^{-1}\dif t$ for $V>0$, a strictly increasing
bijection onto $(0,1)$, and $V_\alpha\defeq S_\alpha^{-1}$. For $0<x\le1$ and $0<p<1$ put
\[
f_x(p)\defeq\frac{V_\alpha(p)}{V_\alpha(p)+x^\alpha},\qquad U_\alpha(p)\defeq\frac{V_\alpha(p)}{p(1-p)} .
\]
The bulk profiles are
\begin{equation}\label{eqn:app-pl-bulk-profiles}
\begin{gathered}
\Psi_\alpha(x)\defeq c_0\int_0^1\sqrt{\frac{1-p}{p\,V_\alpha(p)}}\;f_x(p)\,\dif p,\\
C_{\alpha,x}(\tau)\defeq\int_0^{1-\tau}\frac{f_x(p+\tau)-f_x(p)}{\tau}\sqrt{\frac{U_\alpha(p)}{U_\alpha(p+\tau)}}\,\dif p\quad(0<\tau<1),\\
\Gamma_\alpha(x)\defeq2\int_0^1C_{\alpha,x}(\tau)\,\dif\tau .
\end{gathered}
\end{equation}
For $\alpha>1$, the crossover profiles are, for $y,X>0$,
\begin{equation}\label{eqn:app-pl-Phi}
\begin{aligned}
\Phi_{\alpha,\bmom}(y)\defeq\frac1\pi\int_0^\infty&\sqrt q\,\Lw(q)\,r_\bmom(q)^{-\frac{\alpha+1}2}\\
&\times\frac{y\,r_\bmom(q)^\alpha}{1+y\,r_\bmom(q)^\alpha}\Big(1+(\alpha-1)\frac{q\,r_\bmom'(q)}{r_\bmom(q)}\Big)\frac{\dif q}{q},
\end{aligned}
\end{equation}
\begin{equation}\label{eqn:app-pl-G}
\begin{aligned}
G_{\alpha,\bmom}(X)\defeq\frac1{\pi^2}\sum_{\ell\in\mathbb Z}\int_0^\infty\!\!\int_0^\infty
&\frac{\sqrt{\zeta_X(u)\big(1-\zeta_X(u)\big)\zeta_X(v)\big(1-\zeta_X(v)\big)}}{\sqrt{uv}}\\
&\times\frac{\mathsf D_\ell(u,v)\,\vartheta_\infty(u)\vartheta_\infty(v)}{\Delta_\ell^\infty(u,v)}\,\dif u\,\dif v,
\end{aligned}
\end{equation}
where $\mathsf D_\ell$ and $\mathsf M_\ell$ are the functions of
\cref{eqn:app-pl-participation-kernel}, which depend on $(m_1,m_2)=(u,v)$ only
through $(Q_u,Q_v)$, and
\[
\zeta_X(u)\defeq\frac{u^\alpha}{X^\alpha+u^\alpha},\qquad
\vartheta_\infty(u)\defeq\frac1{E(u)}+\frac{\alpha-1}u,\]
\[
t_\alpha(u,v)\defeq\frac{v^\alpha u-u^\alpha v}{v^\alpha-u^\alpha},\qquad
\Delta_\ell^\infty\defeq1-\frac{t_\alpha(u,v)\,\mathsf M_\ell(u,v)}{uv},
\]
with $t_\alpha(u,u)\defeq(\alpha-1)u/\alpha$, and with the convention of
\cref{eqn:app-pl-participation-kernel} for negative lags.
\end{definition}
-/

/-- `U_α(p) = V_α(p)/(p(1-p))`, part of `def:app-pl-profiles` (snapshot `cr-2026-10-23`),
`section.tex` l.778-779. -/
noncomputable def profU (α p : ℝ) : ℝ := contV α p / (p * (1 - p))

/-- `f_x(p) = V_α(p)/(V_α(p)+x^α)`, part of `def:app-pl-profiles` (snapshot `cr-2026-10-23`),
`section.tex` l.778-779. -/
noncomputable def profF (α x p : ℝ) : ℝ := contV α p / (contV α p + x ^ α)

/-- `Ψ_α(x)`, the bulk profile of `eqn:app-pl-bulk-profiles` (snapshot `cr-2026-10-23`):

\begin{equation}\label{eqn:app-pl-bulk-profiles}
\begin{gathered}
\Psi_\alpha(x)\defeq c_0\int_0^1\sqrt{\frac{1-p}{p\,V_\alpha(p)}}\;f_x(p)\,\dif p,\\
C_{\alpha,x}(\tau)\defeq\int_0^{1-\tau}\frac{f_x(p+\tau)-f_x(p)}{\tau}\sqrt{\frac{U_\alpha(p)}{U_\alpha(p+\tau)}}\,\dif p\quad(0<\tau<1),\\
\Gamma_\alpha(x)\defeq2\int_0^1C_{\alpha,x}(\tau)\,\dif\tau .
\end{gathered}
\end{equation} -/
noncomputable def profPsi (α x : ℝ) : ℝ :=
  c0 * ∫ p in (0:ℝ)..1, Real.sqrt ((1 - p) / (p * contV α p)) * profF α x p

/-- `C_{α,x}(τ)` for `0 < τ < 1`, the bulk profile of `eqn:app-pl-bulk-profiles` (snapshot
`cr-2026-10-23`):

\begin{equation}\label{eqn:app-pl-bulk-profiles}
\begin{gathered}
\Psi_\alpha(x)\defeq c_0\int_0^1\sqrt{\frac{1-p}{p\,V_\alpha(p)}}\;f_x(p)\,\dif p,\\
C_{\alpha,x}(\tau)\defeq\int_0^{1-\tau}\frac{f_x(p+\tau)-f_x(p)}{\tau}\sqrt{\frac{U_\alpha(p)}{U_\alpha(p+\tau)}}\,\dif p\quad(0<\tau<1),\\
\Gamma_\alpha(x)\defeq2\int_0^1C_{\alpha,x}(\tau)\,\dif\tau .
\end{gathered}
\end{equation} -/
noncomputable def profC (α x τ : ℝ) : ℝ :=
  ∫ p in (0:ℝ)..(1 - τ),
    (profF α x (p + τ) - profF α x p) / τ * Real.sqrt (profU α p / profU α (p + τ))

/-- `Γ_α(x) = 2 ∫_0^1 C_{α,x}(τ) dτ`, the bulk profile of `eqn:app-pl-bulk-profiles` (snapshot
`cr-2026-10-23`):

\begin{equation}\label{eqn:app-pl-bulk-profiles}
\begin{gathered}
\Psi_\alpha(x)\defeq c_0\int_0^1\sqrt{\frac{1-p}{p\,V_\alpha(p)}}\;f_x(p)\,\dif p,\\
C_{\alpha,x}(\tau)\defeq\int_0^{1-\tau}\frac{f_x(p+\tau)-f_x(p)}{\tau}\sqrt{\frac{U_\alpha(p)}{U_\alpha(p+\tau)}}\,\dif p\quad(0<\tau<1),\\
\Gamma_\alpha(x)\defeq2\int_0^1C_{\alpha,x}(\tau)\,\dif\tau .
\end{gathered}
\end{equation} -/
noncomputable def profGamma (α x : ℝ) : ℝ := 2 * ∫ τ in (0:ℝ)..1, profC α x τ

/-- `Φ_{α,β}(y)`, the crossover profile of `eqn:app-pl-Phi` (snapshot `cr-2026-10-23`):

\begin{equation}\label{eqn:app-pl-Phi}
\begin{aligned}
\Phi_{\alpha,\bmom}(y)\defeq\frac1\pi\int_0^\infty&\sqrt q\,\Lw(q)\,r_\bmom(q)^{-\frac{\alpha+1}2}\\
&\times\frac{y\,r_\bmom(q)^\alpha}{1+y\,r_\bmom(q)^\alpha}\Big(1+(\alpha-1)\frac{q\,r_\bmom'(q)}{r_\bmom(q)}\Big)\frac{\dif q}{q},
\end{aligned}
\end{equation}

The weight functions are the full EMA weights `emaW β`, and `r_β = rW (emaW β)`. -/
noncomputable def profPhi (α β y : ℝ) : ℝ :=
  (1 / Real.pi) * ∫ q in Ioi (0:ℝ),
    Real.sqrt q * Lw (emaW β) q * rW (emaW β) q ^ (-(α + 1) / 2) *
      (y * rW (emaW β) q ^ α / (1 + y * rW (emaW β) q ^ α)) *
      (1 + (α - 1) * q * deriv (rW (emaW β)) q / rW (emaW β) q) / q

/-- `ζ_X(u) = u^α/(X^α+u^α)`, auxiliary to `eqn:app-pl-G` (snapshot `cr-2026-10-23`):

where $\mathsf D_\ell$ and $\mathsf M_\ell$ are the functions of
\cref{eqn:app-pl-participation-kernel}, which depend on $(m_1,m_2)=(u,v)$ only
through $(Q_u,Q_v)$, and
\[
\zeta_X(u)\defeq\frac{u^\alpha}{X^\alpha+u^\alpha},\qquad
\vartheta_\infty(u)\defeq\frac1{E(u)}+\frac{\alpha-1}u,\]
\[
t_\alpha(u,v)\defeq\frac{v^\alpha u-u^\alpha v}{v^\alpha-u^\alpha},\qquad
\Delta_\ell^\infty\defeq1-\frac{t_\alpha(u,v)\,\mathsf M_\ell(u,v)}{uv},
\]
with $t_\alpha(u,u)\defeq(\alpha-1)u/\alpha$, and with the convention of
\cref{eqn:app-pl-participation-kernel} for negative lags. -/
noncomputable def profZeta (α X u : ℝ) : ℝ := u ^ α / (X ^ α + u ^ α)

/-- `ϑ_∞(u) = 1/E(u) + (α-1)/u`, auxiliary to `eqn:app-pl-G` (snapshot `cr-2026-10-23`):

where $\mathsf D_\ell$ and $\mathsf M_\ell$ are the functions of
\cref{eqn:app-pl-participation-kernel}, which depend on $(m_1,m_2)=(u,v)$ only
through $(Q_u,Q_v)$, and
\[
\zeta_X(u)\defeq\frac{u^\alpha}{X^\alpha+u^\alpha},\qquad
\vartheta_\infty(u)\defeq\frac1{E(u)}+\frac{\alpha-1}u,\]
\[
t_\alpha(u,v)\defeq\frac{v^\alpha u-u^\alpha v}{v^\alpha-u^\alpha},\qquad
\Delta_\ell^\infty\defeq1-\frac{t_\alpha(u,v)\,\mathsf M_\ell(u,v)}{uv},
\]
with $t_\alpha(u,u)\defeq(\alpha-1)u/\alpha$, and with the convention of
\cref{eqn:app-pl-participation-kernel} for negative lags. -/
noncomputable def profTheta (α β u : ℝ) : ℝ := 1 / Efun β u + (α - 1) / u

/-- `t_α(u,v)`, auxiliary to `eqn:app-pl-G` (snapshot `cr-2026-10-23`); the value on the diagonal
is `t_α(u,u) = (α-1)u/α`:

where $\mathsf D_\ell$ and $\mathsf M_\ell$ are the functions of
\cref{eqn:app-pl-participation-kernel}, which depend on $(m_1,m_2)=(u,v)$ only
through $(Q_u,Q_v)$, and
\[
\zeta_X(u)\defeq\frac{u^\alpha}{X^\alpha+u^\alpha},\qquad
\vartheta_\infty(u)\defeq\frac1{E(u)}+\frac{\alpha-1}u,\]
\[
t_\alpha(u,v)\defeq\frac{v^\alpha u-u^\alpha v}{v^\alpha-u^\alpha},\qquad
\Delta_\ell^\infty\defeq1-\frac{t_\alpha(u,v)\,\mathsf M_\ell(u,v)}{uv},
\]
with $t_\alpha(u,u)\defeq(\alpha-1)u/\alpha$, and with the convention of
\cref{eqn:app-pl-participation-kernel} for negative lags. -/
noncomputable def profT (α u v : ℝ) : ℝ :=
  if u = v then (α - 1) * u / α else (v ^ α * u - u ^ α * v) / (v ^ α - u ^ α)

/-- `Δ_ℓ^∞(u,v) = 1 - t_α(u,v) 𝖬_ℓ(u,v)/(uv)`, auxiliary to `eqn:app-pl-G` (snapshot
`cr-2026-10-23`). The arguments `(m₁,m₂) = (u,v)` of `𝖬_ℓ` enter through `(Q_u,Q_v)`:

where $\mathsf D_\ell$ and $\mathsf M_\ell$ are the functions of
\cref{eqn:app-pl-participation-kernel}, which depend on $(m_1,m_2)=(u,v)$ only
through $(Q_u,Q_v)$, and
\[
\zeta_X(u)\defeq\frac{u^\alpha}{X^\alpha+u^\alpha},\qquad
\vartheta_\infty(u)\defeq\frac1{E(u)}+\frac{\alpha-1}u,\]
\[
t_\alpha(u,v)\defeq\frac{v^\alpha u-u^\alpha v}{v^\alpha-u^\alpha},\qquad
\Delta_\ell^\infty\defeq1-\frac{t_\alpha(u,v)\,\mathsf M_\ell(u,v)}{uv},
\]
with $t_\alpha(u,u)\defeq(\alpha-1)u/\alpha$, and with the convention of
\cref{eqn:app-pl-participation-kernel} for negative lags. -/
noncomputable def profDelta (α β : ℝ) (ℓ : ℤ) (u v : ℝ) : ℝ :=
  1 - profT α u v * MLag β (Qm β u) (Qm β v) ℓ / (u * v)

/-- `G_{α,β}(X)`, the crossover profile of `eqn:app-pl-G` (snapshot `cr-2026-10-23`):

\begin{equation}\label{eqn:app-pl-G}
\begin{aligned}
G_{\alpha,\bmom}(X)\defeq\frac1{\pi^2}\sum_{\ell\in\mathbb Z}\int_0^\infty\!\!\int_0^\infty
&\frac{\sqrt{\zeta_X(u)\big(1-\zeta_X(u)\big)\zeta_X(v)\big(1-\zeta_X(v)\big)}}{\sqrt{uv}}\\
&\times\frac{\mathsf D_\ell(u,v)\,\vartheta_\infty(u)\vartheta_\infty(v)}{\Delta_\ell^\infty(u,v)}\,\dif u\,\dif v,
\end{aligned}
\end{equation}

The functions `𝖣_ℓ(u,v)` and `𝖬_ℓ(u,v)` are `DLag`, `MLag` at `(Q_u,Q_v)`. -/
noncomputable def profG (α β X : ℝ) : ℝ :=
  (1 / Real.pi ^ 2) * ∑' ℓ : ℤ, ∫ u in Ioi (0:ℝ), ∫ v in Ioi (0:ℝ),
    Real.sqrt (profZeta α X u * (1 - profZeta α X u) * (profZeta α X v * (1 - profZeta α X v))) /
        Real.sqrt (u * v) *
      (DLag β (Qm β u) (Qm β v) ℓ * profTheta α β u * profTheta α β v / profDelta α β ℓ u v)

/-!
## Statements

Helpers and declarations of record for the profile layer. Each theorem's docstring carries its
source label and the statement verbatim from `section.tex`.
-/

private lemma prof_cont_on {α V : ℝ} (hα0 : 0 < α) (hV : 0 < V) :
    ContinuousOn (fun t : ℝ => V / (V + t ^ α)) (Set.uIcc 0 1) := by
  apply ContinuousOn.div continuousOn_const
  · exact (continuous_const.add (Real.continuous_rpow_const hα0.le)).continuousOn
  · intro t ht
    have ht' : (0:ℝ) ≤ t := (by rwa [Set.uIcc_of_le (zero_le_one : (0:ℝ) ≤ 1)] at ht : t ∈ Set.Icc (0:ℝ) 1).1
    have h0 : 0 ≤ t ^ α := Real.rpow_nonneg ht' α
    exact (by linarith : (0:ℝ) < V + t ^ α).ne'

private lemma prof_contS_strictMonoOn {α : ℝ} (hα0 : 0 < α) :
    StrictMonoOn (contS α) (Set.Ioi 0) := by
  intro V hV W hW hVW
  have hV' : (0:ℝ) < V := Set.mem_Ioi.1 hV
  have hW' : (0:ℝ) < W := Set.mem_Ioi.1 hW
  show contS α V < contS α W
  have hdiff : 0 < ∫ t in (0:ℝ)..1, (W / (W + t ^ α) - V / (V + t ^ α)) := by
    apply intervalIntegral.intervalIntegral_pos_of_pos_on
    · exact ((prof_cont_on hα0 hW').sub (prof_cont_on hα0 hV')).intervalIntegrable
    · intro t ht
      have ht0 : (0:ℝ) < t := ht.1
      have h0 : 0 < t ^ α := Real.rpow_pos_of_pos ht0 α
      have h1 : 0 < V + t ^ α := by linarith
      have h2 : 0 < W + t ^ α := by linarith
      rw [div_sub_div _ _ h2.ne' h1.ne']
      apply div_pos _ (mul_pos h2 h1)
      nlinarith [mul_pos h0 (sub_pos.2 hVW)]
    · exact zero_lt_one
  rw [intervalIntegral.integral_sub ((prof_cont_on hα0 hW').intervalIntegrable)
    ((prof_cont_on hα0 hV').intervalIntegrable)] at hdiff
  unfold contS
  linarith

private lemma prof_contS_pos {α V : ℝ} (hα0 : 0 < α) (hV : 0 < V) : 0 < contS α V := by
  unfold contS
  refine intervalIntegral.intervalIntegral_pos_of_pos_on
    (prof_cont_on hα0 hV).intervalIntegrable ?_ zero_lt_one
  intro t ht
  have h0 : 0 ≤ t ^ α := Real.rpow_nonneg ht.1.le α
  exact div_pos hV (by linarith)

private lemma prof_contS_lt_one {α V : ℝ} (hα0 : 0 < α) (hV : 0 < V) : contS α V < 1 := by
  have hdiff : 0 < ∫ t in (0:ℝ)..1, (1 - V / (V + t ^ α)) := by
    apply intervalIntegral.intervalIntegral_pos_of_pos_on
    · exact (continuousOn_const.sub (prof_cont_on hα0 hV)).intervalIntegrable
    · intro t ht
      have ht0 : (0:ℝ) < t := ht.1
      have h0 : 0 < t ^ α := Real.rpow_pos_of_pos ht0 α
      have h1 : 0 < V + t ^ α := by linarith
      rw [one_sub_div h1.ne']
      apply div_pos _ h1
      linarith
    · exact zero_lt_one
  have hint : ∫ t in (0:ℝ)..1, (1 - V / (V + t ^ α)) = 1 - contS α V := by
    unfold contS
    rw [intervalIntegral.integral_sub intervalIntegrable_const (prof_cont_on hα0 hV).intervalIntegrable]
    simp
  linarith

private lemma prof_contS_continuousOn {α ε : ℝ} (hα0 : 0 < α) (hε : 0 < ε) :
    ContinuousOn (contS α) (Set.Ici ε) := by
  have hc : Continuous fun V : ℝ => ∫ t in (0:ℝ)..1, V / (max V ε + |t| ^ α) := by
    apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    have hden : Continuous fun p : ℝ × ℝ => max p.1 ε + |p.2| ^ α :=
      (continuous_fst.max continuous_const).add
        ((Real.continuous_rpow_const hα0.le).comp continuous_snd.abs)
    apply Continuous.div continuous_fst hden
    intro p
    have h1 : ε ≤ max p.1 ε := le_max_right _ _
    have h2 : 0 ≤ |p.2| ^ α := Real.rpow_nonneg (abs_nonneg _) α
    exact (by linarith : (0:ℝ) < max p.1 ε + |p.2| ^ α).ne'
  refine hc.continuousOn.congr ?_
  intro V hV
  have hV' : ε ≤ V := hV
  unfold contS
  apply intervalIntegral.integral_congr
  intro t ht
  have ht' : (0:ℝ) ≤ t := (by rwa [Set.uIcc_of_le (zero_le_one : (0:ℝ) ≤ 1)] at ht : t ∈ Set.Icc (0:ℝ) 1).1
  simp only
  rw [max_eq_left hV', abs_of_nonneg ht']

private lemma prof_contS_tendsto_zero {α : ℝ} (hα0 : 0 < α) :
    Tendsto (contS α) (𝓝[>] (0:ℝ)) (𝓝 0) := by
  have key : Tendsto (fun V : ℝ => ∫ t in (0:ℝ)..1, V / (V + t ^ α)) (𝓝[>] (0:ℝ))
      (𝓝 (∫ t in (0:ℝ)..1, (0:ℝ))) := by
    apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence (fun _ => (1:ℝ))
    · filter_upwards [self_mem_nhdsWithin] with V hV
      exact (ContinuousOn.aestronglyMeasurable (prof_cont_on hα0 hV)
        measurableSet_uIcc).mono_measure (Measure.restrict_mono Set.uIoc_subset_uIcc le_rfl)
    · filter_upwards [self_mem_nhdsWithin] with V hV
      refine ae_of_all _ (fun t ht => ?_)
      rw [Set.uIoc_of_le zero_le_one] at ht
      have h0 : 0 ≤ t ^ α := Real.rpow_nonneg ht.1.le α
      have hpos : (0:ℝ) < V + t ^ α := by have := (Set.mem_Ioi.1 hV); linarith
      rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (Set.mem_Ioi.1 hV).le hpos.le),
        div_le_one hpos]
      linarith
    · exact intervalIntegrable_const
    · refine ae_of_all _ (fun t ht => ?_)
      rw [Set.uIoc_of_le zero_le_one] at ht
      have h0 : 0 < t ^ α := Real.rpow_pos_of_pos ht.1 α
      have hcont : ContinuousAt (fun V : ℝ => V / (V + t ^ α)) 0 :=
        ContinuousAt.div continuousAt_id (continuousAt_id.add continuousAt_const)
          (by simp; exact h0.ne')
      have h : Tendsto (fun V : ℝ => V / (V + t ^ α)) (𝓝[>] (0:ℝ))
          (𝓝 ((0:ℝ) / (0 + t ^ α))) := hcont.tendsto.mono_left nhdsWithin_le_nhds
      simpa using h
  unfold contS
  simpa using key

private lemma prof_contS_tendsto_one {α : ℝ} (hα0 : 0 < α) :
    Tendsto (contS α) atTop (𝓝 1) := by
  have hv : Tendsto (fun V : ℝ => 1 / ((α + 1) * V)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (Tendsto.const_mul_atTop (by linarith : (0:ℝ) < α + 1) tendsto_id)
  have h1 : Tendsto (fun V => 1 - contS α V) atTop (𝓝 0) :=
    (lem_app_pl_continuum_i_infty hα0).symm.tendsto_nhds hv
  have h2 := (tendsto_const_nhds (x := (1:ℝ))).sub h1
  simpa using h2

/-- Helper for `def:app-pl-profiles` (snapshot `cr-2026-10-23`): the bijectivity claim of
`S_α` on `(0,∞)` onto `(0,1)`, used to define `V_α = S_α^{-1}`. Source: `section.tex` l.776-777:

\begin{definition}[Profiles]\label{def:app-pl-profiles}
Let $S_\alpha(V)\defeq\int_0^1V(V+t^\alpha)^{-1}\dif t$ for $V>0$, a strictly increasing -/
theorem def_app_pl_profiles_S_bij {α : ℝ} (hα : 0 < α) :
    StrictMonoOn (contS α) (Ioi 0) ∧ BijOn (contS α) (Ioi 0) (Ioo 0 1) := by
  refine ⟨prof_contS_strictMonoOn hα, ?_, ?_, ?_⟩
  · intro V hV
    exact ⟨prof_contS_pos hα (Set.mem_Ioi.1 hV), prof_contS_lt_one hα (Set.mem_Ioi.1 hV)⟩
  · exact (prof_contS_strictMonoOn hα).injOn
  · intro p hp
    obtain ⟨hp0, hp1⟩ := hp
    have hev0 : ∀ᶠ a in 𝓝[>] (0:ℝ), contS α a < p :=
      (prof_contS_tendsto_zero hα).eventually (gt_mem_nhds hp0)
    obtain ⟨a, ha1, ha2⟩ := (hev0.and self_mem_nhdsWithin).exists
    have hev1 : ∀ᶠ b in atTop, p < contS α b :=
      (prof_contS_tendsto_one hα).eventually (lt_mem_nhds hp1)
    obtain ⟨b, hb1, hb2⟩ := (hev1.and (eventually_ge_atTop a)).exists
    have ha0 : (0:ℝ) < a := ha2
    have hab : a ≤ b := hb2
    have hcont : ContinuousOn (contS α) (Icc a b) :=
      (prof_contS_continuousOn hα (lt_of_lt_of_le ha0 le_rfl)).mono
        Set.Icc_subset_Ici_self
    obtain ⟨V, hV, hVp⟩ := intermediate_value_Icc hab hcont ⟨ha1.le, hb1.le⟩
    exact ⟨V, lt_of_lt_of_le ha0 hV.1, hVp⟩


private lemma prof_c0_pos : 0 < c0 := by
  unfold c0
  exact Real.sqrt_pos.2 (by positivity)

private lemma prof_contV_spec {α p : ℝ} (hα : 0 < α) (hp : p ∈ Ioo (0:ℝ) 1) :
    0 < contV α p ∧ contS α (contV α p) = p := by
  have h : ∃ a ∈ Ioi (0:ℝ), contS α a = p := (def_app_pl_profiles_S_bij hα).2.surjOn hp
  exact ⟨Set.mem_Ioi.1 (Function.invFunOn_mem h), Function.invFunOn_eq h⟩

private lemma prof_contV_mono {α : ℝ} (hα : 0 < α) : MonotoneOn (contV α) (Ioo (0:ℝ) 1) := by
  intro p hp q hq hpq
  have hp' := prof_contV_spec hα hp
  have hq' := prof_contV_spec hα hq
  rw [← (prof_contS_strictMonoOn hα).le_iff_le (Set.mem_Ioi.2 hp'.1) (Set.mem_Ioi.2 hq'.1),
    hp'.2, hq'.2]
  exact hpq

private lemma prof_contV_aemeas {α : ℝ} (hα : 0 < α) :
    AEMeasurable (contV α) (volume.restrict (Ioc (0:ℝ) 1)) := by
  have h := aemeasurable_restrict_of_monotoneOn (μ := volume) measurableSet_Ioo
    (prof_contV_mono hα)
  have key : volume.restrict (Ioo (0:ℝ) 1) = volume.restrict (Ioc (0:ℝ) 1) :=
    Measure.restrict_congr_set Ioo_ae_eq_Ioc
  rw [← key]
  exact h

private lemma prof_V_mul_le {α p : ℝ} (hα : 0 < α) (hp : p ∈ Ioo (0:ℝ) 1) :
    (1 - p) * contV α p ≤ p := by
  have hV := (prof_contV_spec hα hp).1
  have hS : contV α p / (contV α p + 1) ≤ contS α (contV α p) := by
    unfold contS
    have hint : ∫ t in (0:ℝ)..1, contV α p / (contV α p + 1)
        ≤ ∫ t in (0:ℝ)..1, contV α p / (contV α p + t ^ α) := by
      apply intervalIntegral.integral_mono_on zero_le_one intervalIntegrable_const
        (prof_cont_on hα hV).intervalIntegrable
      intro t ht
      have h1 : t ^ α ≤ 1 := Real.rpow_le_one ht.1 ht.2 hα.le
      have h2 : 0 ≤ t ^ α := Real.rpow_nonneg ht.1 α
      exact div_le_div_of_nonneg_left hV.le (by linarith) (by linarith)
    have hc : ∫ t in (0:ℝ)..1, contV α p / (contV α p + 1)
        = contV α p / (contV α p + 1) := by simp
    rw [hc] at hint
    exact hint
  rw [(prof_contV_spec hα hp).2] at hS
  rw [div_le_iff₀ (by linarith)] at hS
  nlinarith

private lemma prof_u_bound {α x p : ℝ} (hα : 0 < α) (hx : 0 < x) (hp : p ∈ Ioc (0:ℝ) 1) :
    0 ≤ Real.sqrt ((1 - p) / (p * contV α p)) * profF α x p ∧
      Real.sqrt ((1 - p) / (p * contV α p)) * profF α x p ≤ 1 / x ^ α := by
  rcases eq_or_lt_of_le hp.2 with h1 | h1
  · rw [h1]
    simp only [sub_self, zero_div, Real.sqrt_zero, zero_mul]
    exact ⟨le_rfl, (one_div_pos.2 (Real.rpow_pos_of_pos hx α)).le⟩
  · have hp' : p ∈ Ioo (0:ℝ) 1 := ⟨hp.1, h1⟩
    have hV := (prof_contV_spec hα hp').1
    have hmul := prof_V_mul_le hα hp'
    have hp0 : 0 < p := hp.1
    have hpn : p ≠ 0 := hp0.ne'
    have hVn : contV α p ≠ 0 := hV.ne'
    have hD : 0 < x ^ α := Real.rpow_pos_of_pos hx α
    unfold profF
    set V := contV α p with hVdef
    have ha : 0 ≤ (1 - p) / (p * V) := div_nonneg (by linarith [hp'.2]) (mul_nonneg hp0.le hV.le)
    have hs2 : Real.sqrt ((1 - p) / (p * V)) ^ 2 = (1 - p) / (p * V) := Real.sq_sqrt ha
    set s := Real.sqrt ((1 - p) / (p * V)) with hs
    have hs0 : 0 ≤ s := Real.sqrt_nonneg _
    have hsV : s * V ≤ 1 := by
      have hsq : (s * V) ^ 2 ≤ 1 := by
        have e : (s * V) ^ 2 = (1 - p) * V / p := by
          rw [mul_pow, hs2]
          field_simp
        rw [e, div_le_one hp0]
        exact hmul
      nlinarith [mul_nonneg hs0 hV.le]
    refine ⟨mul_nonneg hs0 (div_nonneg hV.le (by linarith)), ?_⟩
    rw [← mul_div_assoc]
    calc s * V / (V + x ^ α) ≤ 1 / (V + x ^ α) :=
          div_le_div_of_nonneg_right hsV (by linarith)
      _ ≤ 1 / x ^ α := one_div_le_one_div_of_le hD (by linarith)

private lemma prof_u_aemeas {α x : ℝ} (hα : 0 < α) :
    AEMeasurable (fun p : ℝ => Real.sqrt ((1 - p) / (p * contV α p)) * profF α x p)
      (volume.restrict (Ioc (0:ℝ) 1)) := by
  have hV := prof_contV_aemeas hα
  have hA : AEMeasurable (fun p : ℝ => (1 - p) / (p * contV α p))
      (volume.restrict (Ioc (0:ℝ) 1)) :=
    ((by fun_prop : Measurable fun p : ℝ => 1 - p).aemeasurable).div
      (measurable_id.aemeasurable.mul hV)
  have hB : AEMeasurable (fun p : ℝ => contV α p / (contV α p + x ^ α))
      (volume.restrict (Ioc (0:ℝ) 1)) :=
    hV.div (hV.add (measurable_const : Measurable fun _ : ℝ => x ^ α).aemeasurable)
  unfold profF
  exact (Real.continuous_sqrt.measurable.comp_aemeasurable hA).mul hB

private lemma prof_u_integrable {α x : ℝ} (hα : 0 < α) (hx : x ∈ Ioc (0:ℝ) 1) :
    IntervalIntegrable (fun p : ℝ => Real.sqrt ((1 - p) / (p * contV α p)) * profF α x p)
      volume 0 1 := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
  refine Integrable.mono' (g := fun _ => 1 / x ^ α) (integrable_const _)
    (prof_u_aemeas hα).aestronglyMeasurable ?_
  refine (ae_restrict_iff' measurableSet_Ioc).2 (ae_of_all _ fun p hp => ?_)
  rw [Real.norm_of_nonneg (prof_u_bound hα hx.1 hp).1]
  exact (prof_u_bound hα hx.1 hp).2

private lemma prof_psi_lower_core {α : ℝ} (hα : 0 < α) :
    0 < ∫ p in (0:ℝ)..1, Real.sqrt ((1 - p) / (p * contV α p)) * profF α 1 p ∧
      ∀ x ∈ Ioc (0:ℝ) 1, (∫ p in (0:ℝ)..1, Real.sqrt ((1 - p) / (p * contV α p)) * profF α 1 p)
        ≤ ∫ p in (0:ℝ)..1, Real.sqrt ((1 - p) / (p * contV α p)) * profF α x p := by
  have h1 : (1:ℝ) ∈ Ioc (0:ℝ) 1 := ⟨zero_lt_one, le_rfl⟩
  refine ⟨?_, fun x hx => ?_⟩
  · apply intervalIntegral.intervalIntegral_pos_of_pos_on (prof_u_integrable hα h1)
    · intro p hp
      have hV := (prof_contV_spec hα hp).1
      apply mul_pos (Real.sqrt_pos.2 (div_pos (by linarith [hp.2]) (mul_pos hp.1 hV)))
      unfold profF
      apply div_pos hV
      rw [Real.one_rpow]
      linarith
    · exact zero_lt_one
  · apply intervalIntegral.integral_mono_on zero_le_one (prof_u_integrable hα h1)
      (prof_u_integrable hα hx)
    intro p hp
    rcases eq_or_lt_of_le hp.1 with h0 | h0
    · rw [← h0]
      simp
    rcases eq_or_lt_of_le hp.2 with h2 | h2
    · rw [h2]
      simp
    have hp' : p ∈ Ioo (0:ℝ) 1 := ⟨h0, h2⟩
    have hV := (prof_contV_spec hα hp').1
    have hx1 : x ^ α ≤ 1 := Real.rpow_le_one hx.1.le hx.2 hα.le
    apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
    unfold profF
    rw [Real.one_rpow]
    exact div_le_div_of_nonneg_left hV.le (add_pos_of_pos_of_nonneg hV (Real.rpow_nonneg hx.1.le α))
      (by linarith)

/-- `lem:app-pl-Psi` (snapshot `cr-2026-10-23`), part (i), finiteness: the integral defining
`Ψ_α(x)` converges for every `x ∈ (0,1]`. Statement verbatim:

\begin{lemma}[The profile $\Psi_\alpha$]\label{lem:app-pl-Psi}
$\Psi_\alpha$ is finite, positive and continuous on $(0,1]$, bounded below by a
positive constant, and satisfies the first equivalences of
\cref{eqn:app-pl-bulk-small}.
\end{lemma} -/
theorem lem_app_pl_Psi_i_integrable {α : ℝ} (hα : 0 < α) :
    ∀ x ∈ Ioc (0:ℝ) 1, IntervalIntegrable
      (fun p : ℝ => Real.sqrt ((1 - p) / (p * contV α p)) * profF α x p) volume 0 1 := by
  intro x hx
  exact prof_u_integrable hα hx

/-- `lem:app-pl-Psi` (snapshot `cr-2026-10-23`), part (i), continuity on `(0,1]`. Statement
verbatim:

\begin{lemma}[The profile $\Psi_\alpha$]\label{lem:app-pl-Psi}
$\Psi_\alpha$ is finite, positive and continuous on $(0,1]$, bounded below by a
positive constant, and satisfies the first equivalences of
\cref{eqn:app-pl-bulk-small}.
\end{lemma} -/
theorem lem_app_pl_Psi_i_cont {α : ℝ} (hα : 0 < α) :
    ContinuousOn (fun x : ℝ => profPsi α x) (Ioc 0 1) := by
  intro x0 hx0
  apply ContinuousAt.continuousWithinAt
  unfold profPsi
  apply ContinuousAt.const_mul
  have hx0' : 0 < x0 := hx0.1
  have hhalf : 0 < x0 / 2 := by linarith
  apply intervalIntegral.continuousAt_of_dominated_interval
    (F := fun x p => Real.sqrt ((1 - p) / (p * contV α p)) * profF α x p)
    (bound := fun _ => 1 / (x0 / 2) ^ α)
  · exact Filter.Eventually.of_forall fun x => by
      rw [Set.uIoc_of_le zero_le_one]
      exact (prof_u_aemeas hα).aestronglyMeasurable
  · filter_upwards [Ioi_mem_nhds (half_lt_self hx0')] with x hx
    refine ae_of_all _ fun t ht => ?_
    rw [Set.uIoc_of_le zero_le_one] at ht
    have hxpos : 0 < x := lt_trans hhalf (Set.mem_Ioi.1 hx)
    have hxge : x0 / 2 ≤ x := le_of_lt (Set.mem_Ioi.1 hx)
    rw [Real.norm_of_nonneg (prof_u_bound hα hxpos ht).1]
    exact (prof_u_bound hα hxpos ht).2.trans
      (one_div_le_one_div_of_le (Real.rpow_pos_of_pos hhalf α)
        (Real.rpow_le_rpow hhalf.le hxge hα.le))
  · exact intervalIntegrable_const
  · refine ae_of_all _ fun t ht => ?_
    rw [Set.uIoc_of_le zero_le_one] at ht
    unfold profF
    rcases eq_or_lt_of_le ht.2 with h1 | h1
    · rw [h1]
      simp only [sub_self, zero_div, Real.sqrt_zero, zero_mul]
      exact continuousAt_const
    · have hV := (prof_contV_spec hα ⟨ht.1, h1⟩).1
      exact continuousAt_const.mul (continuousAt_const.div
        (continuousAt_const.add (Real.continuousAt_rpow_const x0 α (Or.inl hx0'.ne')))
        (add_pos hV (Real.rpow_pos_of_pos hx0' α)).ne')

/-- `lem:app-pl-Psi` (snapshot `cr-2026-10-23`), part (i), positivity on `(0,1]`. Statement
verbatim:

\begin{lemma}[The profile $\Psi_\alpha$]\label{lem:app-pl-Psi}
$\Psi_\alpha$ is finite, positive and continuous on $(0,1]$, bounded below by a
positive constant, and satisfies the first equivalences of
\cref{eqn:app-pl-bulk-small}.
\end{lemma} -/
theorem lem_app_pl_Psi_i_pos {α : ℝ} (hα : 0 < α) :
    ∀ x ∈ Ioc (0:ℝ) 1, 0 < profPsi α x := by
  obtain ⟨hpos, hmono⟩ := prof_psi_lower_core hα
  intro x hx
  unfold profPsi
  exact lt_of_lt_of_le (mul_pos prof_c0_pos hpos)
    (mul_le_mul_of_nonneg_left (hmono x hx) prof_c0_pos.le)

/-- `lem:app-pl-Psi` (snapshot `cr-2026-10-23`), part (i), a positive lower bound on `(0,1]`.
Statement verbatim:

\begin{lemma}[The profile $\Psi_\alpha$]\label{lem:app-pl-Psi}
$\Psi_\alpha$ is finite, positive and continuous on $(0,1]$, bounded below by a
positive constant, and satisfies the first equivalences of
\cref{eqn:app-pl-bulk-small}.
\end{lemma} -/
theorem lem_app_pl_Psi_i_lower {α : ℝ} (hα : 0 < α) :
    ∃ c : ℝ, 0 < c ∧ ∀ x ∈ Ioc (0:ℝ) 1, c ≤ profPsi α x := by
  obtain ⟨hpos, hmono⟩ := prof_psi_lower_core hα
  refine ⟨c0 * ∫ p in (0:ℝ)..1, Real.sqrt ((1 - p) / (p * contV α p)) * profF α 1 p,
    mul_pos prof_c0_pos hpos, fun x hx => ?_⟩
  unfold profPsi
  exact mul_le_mul_of_nonneg_left (hmono x hx) prof_c0_pos.le

private lemma prof_gt_Kpos {α : ℝ} (hα1 : 1 < α) : 0 < Kc α := by
  have hα0 : 0 < α := by linarith
  unfold Kc
  have hsinpos : 0 < Real.sin (Real.pi / α) := by
    apply Real.sin_pos_of_pos_of_lt_pi (div_pos Real.pi_pos hα0)
    rw [div_lt_iff₀ hα0]
    nlinarith [Real.pi_pos]
  exact div_pos Real.pi_pos (mul_pos hα0 hsinpos)

private lemma prof_gt_r {α : ℝ} (hα1 : 1 < α) :
    Tendsto (fun p : ℝ => contV α p / (p / Kc α) ^ α) (𝓝[>] (0:ℝ)) (𝓝 1) := by
  have hKc := prof_gt_Kpos hα1
  have h := lem_app_pl_continuum_iii_gt hα1
  have hz : ∀ᶠ p in 𝓝[>] (0:ℝ), (fun p : ℝ => (p / Kc α) ^ α) p ≠ 0 := by
    filter_upwards [self_mem_nhdsWithin] with p hp
    exact (Real.rpow_pos_of_pos (div_pos (Set.mem_Ioi.1 hp) hKc) α).ne'
  exact (isEquivalent_iff_tendsto_one hz).1 h

private lemma prof_gt_p0 {α : ℝ} (hα1 : 1 < α) :
    ∃ p0 : ℝ, 0 < p0 ∧ p0 < 1 ∧ ∀ p ∈ Ioc (0:ℝ) p0,
      1 / 2 ≤ contV α p / (p / Kc α) ^ α ∧ contV α p / (p / Kc α) ^ α ≤ 2 := by
  have h := prof_gt_r hα1
  have h2 : ∀ᶠ p in 𝓝[>] (0:ℝ), 1 / 2 ≤ contV α p / (p / Kc α) ^ α ∧
      contV α p / (p / Kc α) ^ α ≤ 2 := by
    have a1 : ∀ᶠ p in 𝓝[>] (0:ℝ), 1 / 2 < contV α p / (p / Kc α) ^ α :=
      h.eventually (lt_mem_nhds (by norm_num))
    have a2 : ∀ᶠ p in 𝓝[>] (0:ℝ), contV α p / (p / Kc α) ^ α < 2 :=
      h.eventually (gt_mem_nhds (by norm_num))
    filter_upwards [a1, a2] with p h1 h2 using ⟨h1.le, h2.le⟩
  have h3 := h2.and (Ioo_mem_nhdsGT (zero_lt_one : (0:ℝ) < 1))
  obtain ⟨u, hu, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 h3
  have hu' := Set.mem_Ioi.1 hu
  refine ⟨u / 2, by linarith, ?_, ?_⟩
  · exact (hsub (⟨by linarith, by linarith⟩ : u / 2 ∈ Ioo (0:ℝ) u)).2.2
  · intro p hp
    exact (hsub ⟨hp.1, by linarith [hp.2]⟩).1

private lemma prof_gt_beta {α : ℝ} (hα1 : 1 < α) :
    IntegrableOn (fun u : ℝ => u ^ ((α - 1) / 2) / (1 + u ^ α)) (Ioi 0) ∧
    ∫ u in Ioi (0:ℝ), u ^ ((α - 1) / 2) / (1 + u ^ α)
      = Real.pi / (α * Real.cos (Real.pi / (2 * α))) := by
  have hα0 : 0 < α := by linarith
  have hne : α ≠ 0 := hα0.ne'
  have ha : 0 < (α + 1) / (2 * α) := by positivity
  have hb : 0 < 1 - (α + 1) / (2 * α) := by
    have : (α + 1) / (2 * α) < 1 := by rw [div_lt_one (by positivity)]; linarith
    linarith
  have hb' := Muon.Foundations.betaHalfLine ha hb
  rw [show ((α + 1) / (2 * α) + (1 - (α + 1) / (2 * α))) = (1:ℝ) by ring] at hb'
  simp only [Real.rpow_neg_one] at hb'
  rw [Real.Gamma_one, div_one, Real.Gamma_mul_Gamma_one_sub] at hb'
  have hcv : ∫ x in Ioi (0:ℝ), (α * x ^ (α - 1)) • (((x ^ α) ^ ((α + 1) / (2 * α) - 1)) * (1 + x ^ α)⁻¹)
      = ∫ y in Ioi (0:ℝ), y ^ ((α + 1) / (2 * α) - 1) * (1 + y)⁻¹ :=
    integral_comp_rpow_Ioi_of_pos
      (g := fun y : ℝ => y ^ ((α + 1) / (2 * α) - 1) * (1 + y)⁻¹) hα0
  have hpt : ∀ x ∈ Ioi (0:ℝ), (α * x ^ (α - 1)) • (((x ^ α) ^ ((α + 1) / (2 * α) - 1)) * (1 + x ^ α)⁻¹)
      = α * (x ^ ((α - 1) / 2) / (1 + x ^ α)) := by
    intro x hx
    have hx' : (0:ℝ) < x := hx
    have e1 : (x ^ α) ^ ((α + 1) / (2 * α) - 1) = x ^ ((1 - α) / 2) := by
      rw [← Real.rpow_mul hx'.le]
      congr 1
      field_simp
      ring
    have e2 : x ^ (α - 1) * x ^ ((1 - α) / 2) = x ^ ((α - 1) / 2) := by
      rw [← Real.rpow_add hx']
      congr 1
      ring
    rw [smul_eq_mul, e1]
    rw [show α * x ^ (α - 1) * (x ^ ((1 - α) / 2) * (1 + x ^ α)⁻¹)
      = α * (x ^ (α - 1) * x ^ ((1 - α) / 2)) * (1 + x ^ α)⁻¹ by ring, e2]
    ring
  have hcongr := setIntegral_congr_fun (μ := volume) measurableSet_Ioi hpt
  rw [hcv, integral_const_mul] at hcongr
  rw [hb'] at hcongr
  have hcos : 0 < Real.cos (Real.pi / (2 * α)) := by
    apply Real.cos_pos_of_mem_Ioo
    constructor
    · have : 0 < Real.pi / (2 * α) := by positivity
      linarith [Real.pi_pos]
    · have : Real.pi / (2 * α) < Real.pi / 2 := by
        apply div_lt_div_of_pos_left Real.pi_pos (by norm_num) (by linarith)
      exact this
  have hsin : Real.sin (Real.pi * ((α + 1) / (2 * α))) = Real.cos (Real.pi / (2 * α)) := by
    rw [← Real.cos_pi_div_two_sub]
    have : Real.pi / 2 - Real.pi * ((α + 1) / (2 * α)) = -(Real.pi / (2 * α)) := by
      field_simp
      ring
    rw [this, Real.cos_neg]
  have hJ : ∫ u in Ioi (0:ℝ), u ^ ((α - 1) / 2) / (1 + u ^ α)
      = Real.pi / (α * Real.cos (Real.pi / (2 * α))) := by
    rw [hsin] at hcongr
    field_simp at hcongr ⊢
    linarith
  refine ⟨?_, hJ⟩
  by_contra hn
  rw [integral_undef hn] at hJ
  have : 0 < Real.pi / (α * Real.cos (Real.pi / (2 * α))) :=
    div_pos Real.pi_pos (mul_pos hα0 hcos)
  linarith

private lemma prof_g_le_tail {α p0 : ℝ} (hα : 0 < α) (hp0 : 0 < p0) (hp01 : p0 < 1)
    {p : ℝ} (hp : p ∈ Ioc p0 1) :
    Real.sqrt ((1 - p) / (p * contV α p)) ≤ Real.sqrt (1 / (p0 * contV α p0)) := by
  apply Real.sqrt_le_sqrt
  rcases eq_or_lt_of_le hp.2 with h1 | h1
  · rw [h1]
    simp only [sub_self, zero_div]
    have hV0 := (prof_contV_spec hα ⟨hp0, hp01⟩).1
    positivity
  · have hpI : p ∈ Ioo (0:ℝ) 1 := ⟨lt_trans hp0 hp.1, h1⟩
    have hV0 := (prof_contV_spec hα ⟨hp0, hp01⟩).1
    have hV := (prof_contV_spec hα hpI).1
    have hmono : contV α p0 ≤ contV α p :=
      prof_contV_mono hα ⟨hp0, hp01⟩ hpI hp.1.le
    have hpp : 0 < p := hpI.1
    calc (1 - p) / (p * contV α p) ≤ 1 / (p * contV α p) :=
          div_le_div_of_nonneg_right (by linarith) (by positivity)
      _ ≤ 1 / (p0 * contV α p0) := by
          apply one_div_le_one_div_of_le (by positivity)
          exact mul_le_mul hp.1.le hmono hV0.le hpp.le

private lemma prof_F_bounds {α x p : ℝ} (hα : 0 < α) (hx : 0 < x) (hp : p ∈ Ioo (0:ℝ) 1) :
    0 ≤ profF α x p ∧ profF α x p ≤ 1 := by
  have hV := (prof_contV_spec hα hp).1
  have hD : 0 < x ^ α := Real.rpow_pos_of_pos hx α
  unfold profF
  exact ⟨div_nonneg hV.le (by linarith), (div_le_one (by linarith)).2 (by linarith)⟩

private lemma prof_gt_tail {α p0 : ℝ} (hα : 0 < α) (hp0 : 0 < p0) (hp01 : p0 < 1) :
    ∃ M : ℝ, ∀ x : ℝ, 0 < x →
      ‖∫ p in p0..1, Real.sqrt ((1 - p) / (p * contV α p)) * profF α x p‖ ≤ M := by
  refine ⟨Real.sqrt (1 / (p0 * contV α p0)) * |1 - p0|, fun x hx => ?_⟩
  apply intervalIntegral.norm_integral_le_of_norm_le_const
  intro p hp
  rw [Set.uIoc_of_le hp01.le] at hp
  have hg0 := Real.sqrt_nonneg ((1 - p) / (p * contV α p))
  have hgle := prof_g_le_tail hα hp0 hp01 hp
  have hm0 := Real.sqrt_nonneg (1 / (p0 * contV α p0))
  rcases eq_or_lt_of_le hp.2 with h1 | h1
  · rw [h1]
    simp only [sub_self, zero_div, Real.sqrt_zero, zero_mul, norm_zero]
    exact hm0
  · have hF := prof_F_bounds hα hx (⟨lt_trans hp0 hp.1, h1⟩ : p ∈ Ioo (0:ℝ) 1)
    rw [norm_mul, Real.norm_of_nonneg hg0, Real.norm_of_nonneg hF.1]
    calc Real.sqrt ((1 - p) / (p * contV α p)) * profF α x p
        ≤ Real.sqrt (1 / (p0 * contV α p0)) * 1 :=
          mul_le_mul hgle hF.2 hF.1 hm0
      _ = _ := mul_one _

private lemma prof_gt_H_eq {α K x u R : ℝ} (hK : 0 < K) (hx : 0 < x) (hu : 0 < u) (hR : 0 < R)
    (hp1 : K * x * u < 1) :
    x ^ ((α - 1) / 2) * (K * x) *
      (Real.sqrt ((1 - K * x * u) / ((K * x * u) * (R * (x * u) ^ α))) *
        (R * (x * u) ^ α / (R * (x * u) ^ α + x ^ α)))
    = Real.sqrt K *
      (Real.sqrt ((1 - K * x * u) / R) *
        (u ^ (-((α + 1) / 2)) * (R * u ^ α / (R * u ^ α + 1)))) := by
  have hxu : 0 < x * u := mul_pos hx hu
  have hxa : 0 < x ^ α := Real.rpow_pos_of_pos hx α
  have hua : 0 < u ^ α := Real.rpow_pos_of_pos hu α
  have hmul : (x * u) ^ α = x ^ α * u ^ α := Real.mul_rpow hx.le hu.le
  -- F part
  have hF : R * (x * u) ^ α / (R * (x * u) ^ α + x ^ α) = R * u ^ α / (R * u ^ α + 1) := by
    rw [hmul]
    field_simp
  -- sqrt part
  set s : ℝ := (x * u) ^ (-((α + 1) / 2)) with hs
  have hs0 : 0 < s := Real.rpow_pos_of_pos hxu _
  have hss : s * s = ((x * u) ^ α * (x * u))⁻¹ := by
    rw [hs, ← Real.rpow_add hxu, show -((α + 1) / 2) + -((α + 1) / 2) = -(α + 1) by ring,
      Real.rpow_neg hxu.le, Real.rpow_add hxu, Real.rpow_one]
  have hsq : (1 - K * x * u) / ((K * x * u) * (R * (x * u) ^ α))
      = ((1 - K * x * u) / R) * (1 / K) * (s * s) := by
    rw [hss]
    have : (x * u) ^ α ≠ 0 := (Real.rpow_pos_of_pos hxu α).ne'
    field_simp
  have hA : 0 ≤ (1 - K * x * u) / R := div_nonneg (by linarith) hR.le
  have hB : 0 ≤ 1 / K := by positivity
  have hsqrt : Real.sqrt ((1 - K * x * u) / ((K * x * u) * (R * (x * u) ^ α)))
      = Real.sqrt ((1 - K * x * u) / R) * (Real.sqrt (1 / K) * s) := by
    rw [hsq, Real.sqrt_mul (mul_nonneg hA hB), Real.sqrt_mul hA, Real.sqrt_mul_self hs0.le]
    ring
  have hxs : x ^ ((α - 1) / 2) * x * x ^ (-((α + 1) / 2)) = 1 := by
    rw [← Real.rpow_add_one hx.ne', ← Real.rpow_add hx]
    rw [show (α - 1) / 2 + 1 + -((α + 1) / 2) = 0 by ring, Real.rpow_zero]
  have hss2 : s = x ^ (-((α + 1) / 2)) * u ^ (-((α + 1) / 2)) := Real.mul_rpow hx.le hu.le
  have hKK : K = Real.sqrt K * Real.sqrt K := (Real.mul_self_sqrt hK.le).symm
  have hsK : 0 < Real.sqrt K := Real.sqrt_pos.2 hK
  have hsi : Real.sqrt (1 / K) = (Real.sqrt K)⁻¹ := by
    rw [one_div, Real.sqrt_inv]
  rw [hsqrt, hF, hsi, hss2]
  have h3 : x ^ ((α - 1) / 2) * (K * x) * ((Real.sqrt K)⁻¹ * (x ^ (-((α + 1) / 2)) * u ^ (-((α + 1) / 2))))
      = Real.sqrt K * u ^ (-((α + 1) / 2)) := by
    have : x ^ ((α - 1) / 2) * (K * x) * ((Real.sqrt K)⁻¹ * (x ^ (-((α + 1) / 2)) * u ^ (-((α + 1) / 2))))
        = (x ^ ((α - 1) / 2) * x * x ^ (-((α + 1) / 2))) * (K * (Real.sqrt K)⁻¹) * u ^ (-((α + 1) / 2)) := by ring
    rw [this, hxs]
    have hk : K * (Real.sqrt K)⁻¹ = Real.sqrt K := by
      field_simp
      nlinarith [Real.sq_sqrt hK.le]
    rw [hk]
    ring
  linear_combination (Real.sqrt ((1 - K * x * u) / R) * (R * u ^ α / (R * u ^ α + 1))) * h3

private lemma prof_gt_Hform {α p0 x u : ℝ} (hα1 : 1 < α) (hp0 : 0 < p0) (hp01 : p0 < 1)
    (hx : 0 < x) (hu : 0 < u) (hxu : Kc α * x * u ≤ p0) :
    x ^ ((α - 1) / 2) * (Kc α * x) *
      (Real.sqrt ((1 - Kc α * x * u) / ((Kc α * x * u) * contV α (Kc α * x * u))) *
        profF α x (Kc α * x * u))
    = Real.sqrt (Kc α) *
      (Real.sqrt ((1 - Kc α * x * u) / (contV α (Kc α * x * u) / (x * u) ^ α)) *
        (u ^ (-((α + 1) / 2)) *
          ((contV α (Kc α * x * u) / (x * u) ^ α) * u ^ α /
            ((contV α (Kc α * x * u) / (x * u) ^ α) * u ^ α + 1)))) := by
  have hK := prof_gt_Kpos hα1
  have hxu0 : 0 < x * u := mul_pos hx hu
  have hp : Kc α * x * u ∈ Ioc (0:ℝ) p0 := ⟨by positivity, hxu⟩
  have hpI : Kc α * x * u ∈ Ioo (0:ℝ) 1 := ⟨hp.1, lt_of_le_of_lt hp.2 hp01⟩
  have hV := (prof_contV_spec (α := α) (by linarith) hpI).1
  have key := prof_gt_H_eq (α := α) hK hx hu (div_pos hV (Real.rpow_pos_of_pos hxu0 α))
    (lt_of_le_of_lt hp.2 hp01)
  unfold profF
  set V := contV α (Kc α * x * u) with hVdef
  set R := V / (x * u) ^ α with hRdef
  have hVeq : V = R * (x * u) ^ α := by
    rw [hRdef]
    have : (x * u) ^ α ≠ 0 := (Real.rpow_pos_of_pos hxu0 α).ne'
    field_simp
  rw [hVeq]
  exact key

private lemma prof_gt_bound_alg {α K R p u : ℝ} (hK : 0 < K) (hu : 0 < u) (hR1 : 1 / 2 ≤ R)
    (hR2 : R ≤ 2) (hp0 : 0 ≤ p) (hp1 : p < 1) :
    ‖Real.sqrt K * (Real.sqrt ((1 - p) / R) *
      (u ^ (-((α + 1) / 2)) * (R * u ^ α / (R * u ^ α + 1))))‖
      ≤ 2 * Real.sqrt 2 * Real.sqrt K * (u ^ ((α - 1) / 2) / (1 + u ^ α)) := by
  have hR0 : 0 < R := by linarith
  have hB : 0 < u ^ α := Real.rpow_pos_of_pos hu α
  have he : 0 < u ^ (-((α + 1) / 2)) := Real.rpow_pos_of_pos hu _
  have heB : u ^ (-((α + 1) / 2)) * u ^ α = u ^ ((α - 1) / 2) := by
    rw [← Real.rpow_add hu]
    congr 1
    ring
  have hF0 : 0 ≤ R * u ^ α / (R * u ^ α + 1) := by positivity
  have hF1 : R * u ^ α / (R * u ^ α + 1) ≤ 2 * u ^ α / (1 + u ^ α) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_pos hB hB, mul_nonneg hB.le (sub_nonneg.2 hR2)]
  have hs2 : Real.sqrt ((1 - p) / R) ≤ Real.sqrt 2 := by
    apply Real.sqrt_le_sqrt
    rw [div_le_iff₀ hR0]
    nlinarith
  have hs0 := Real.sqrt_nonneg ((1 - p) / R)
  have hsK := Real.sqrt_nonneg K
  rw [Real.norm_of_nonneg (by positivity)]
  have hmain : Real.sqrt ((1 - p) / R) * (u ^ (-((α + 1) / 2)) * (R * u ^ α / (R * u ^ α + 1)))
      ≤ Real.sqrt 2 * (u ^ (-((α + 1) / 2)) * (2 * u ^ α / (1 + u ^ α))) := by
    apply mul_le_mul hs2 (mul_le_mul_of_nonneg_left hF1 he.le) (by positivity) (Real.sqrt_nonneg 2)
  calc Real.sqrt K * (Real.sqrt ((1 - p) / R) * (u ^ (-((α + 1) / 2)) * (R * u ^ α / (R * u ^ α + 1))))
      ≤ Real.sqrt K * (Real.sqrt 2 * (u ^ (-((α + 1) / 2)) * (2 * u ^ α / (1 + u ^ α)))) :=
        mul_le_mul_of_nonneg_left hmain hsK
    _ = 2 * Real.sqrt 2 * Real.sqrt K * ((u ^ (-((α + 1) / 2)) * u ^ α) / (1 + u ^ α)) := by
        ring
    _ = _ := by rw [heB]

private lemma prof_gt_main {α p0 : ℝ} (hα1 : 1 < α) (hp0 : 0 < p0) (hp01 : p0 < 1)
    (hr : ∀ p ∈ Ioc (0:ℝ) p0, 1 / 2 ≤ contV α p / (p / Kc α) ^ α ∧
      contV α p / (p / Kc α) ^ α ≤ 2) :
    Tendsto (fun x : ℝ => x ^ ((α - 1) / 2) *
        ∫ p in (0:ℝ)..p0, Real.sqrt ((1 - p) / (p * contV α p)) * profF α x p)
      (𝓝[>] (0:ℝ)) (𝓝 (Real.sqrt (Kc α) * (Real.pi / (α * Real.cos (Real.pi / (2 * α)))))) := by
  have hα0 : 0 < α := by linarith
  have hK : 0 < Kc α := prof_gt_Kpos hα1
  obtain ⟨hint, hJ⟩ := prof_gt_beta hα1
  set H : ℝ → ℝ → ℝ := fun x u => x ^ ((α - 1) / 2) * (Kc α * x) *
      (Real.sqrt ((1 - Kc α * x * u) / ((Kc α * x * u) * contV α (Kc α * x * u))) *
        profF α x (Kc α * x * u)) with hH
  have hscale : ∀ x : ℝ, 0 < x → x ^ ((α - 1) / 2) *
        ∫ p in (0:ℝ)..p0, Real.sqrt ((1 - p) / (p * contV α p)) * profF α x p
      = ∫ u in Ioi (0:ℝ), (Ioc (0:ℝ) (p0 / (Kc α * x))).indicator (H x) u := by
    intro x hx
    have hc : 0 < Kc α * x := mul_pos hK hx
    have hcomp := intervalIntegral.integral_comp_mul_left (a := 0) (b := p0 / (Kc α * x))
      (fun p : ℝ => Real.sqrt ((1 - p) / (p * contV α p)) * profF α x p) hc.ne'
    rw [mul_zero, mul_div_cancel₀ _ hc.ne', smul_eq_mul] at hcomp
    have hq : 0 ≤ p0 / (Kc α * x) := by positivity
    have hinter : Ioi (0:ℝ) ∩ Ioc 0 (p0 / (Kc α * x)) = Ioc 0 (p0 / (Kc α * x)) :=
      Set.inter_eq_right.2 (fun u hu => hu.1)
    rw [setIntegral_indicator measurableSet_Ioc, hinter,
      ← intervalIntegral.integral_of_le hq]
    have h2 : ∫ u in (0:ℝ)..p0 / (Kc α * x), H x u
        = x ^ ((α - 1) / 2) * (Kc α * x) *
          ∫ u in (0:ℝ)..p0 / (Kc α * x),
            Real.sqrt ((1 - Kc α * x * u) / ((Kc α * x * u) * contV α (Kc α * x * u))) *
              profF α x (Kc α * x * u) := by
      rw [← intervalIntegral.integral_const_mul]
    rw [h2, hcomp]
    field_simp
  set D : ℝ → ℝ := fun u => 2 * Real.sqrt 2 * Real.sqrt (Kc α) *
      (u ^ ((α - 1) / 2) / (1 + u ^ α)) with hD
  have hDint : Integrable D (volume.restrict (Ioi (0:ℝ))) := hint.const_mul _
  set L : ℝ → ℝ := fun u => Real.sqrt (Kc α) * (u ^ ((α - 1) / 2) / (1 + u ^ α)) with hL
  have hLint : ∫ u in Ioi (0:ℝ), L u
      = Real.sqrt (Kc α) * (Real.pi / (α * Real.cos (Real.pi / (2 * α)))) := by
    rw [hL, integral_const_mul, hJ]
  have hmeas : ∀ x : ℝ, 0 < x → AEStronglyMeasurable
      ((Ioc (0:ℝ) (p0 / (Kc α * x))).indicator (H x)) (volume.restrict (Ioi (0:ℝ))) := by
    intro x hx
    have hc : 0 < Kc α * x := mul_pos hK hx
    have hmono : MonotoneOn (fun u : ℝ => contV α (Kc α * x * u)) (Ioo (0:ℝ) (1 / (Kc α * x))) := by
      intro u hu v hv huv
      have h1 : ∀ w ∈ Ioo (0:ℝ) (1 / (Kc α * x)), Kc α * x * w ∈ Ioo (0:ℝ) 1 := by
        intro w hw
        refine ⟨mul_pos hc hw.1, ?_⟩
        have := (lt_div_iff₀ hc).1 hw.2
        linarith
      exact prof_contV_mono hα0 (h1 u hu) (h1 v hv) (mul_le_mul_of_nonneg_left huv hc.le)
    have hsub : Ioc (0:ℝ) (p0 / (Kc α * x)) ⊆ Ioo (0:ℝ) (1 / (Kc α * x)) := by
      intro u hu
      exact ⟨hu.1, lt_of_le_of_lt hu.2 (div_lt_div_of_pos_right hp01 hc)⟩
    have hV : AEMeasurable (fun u : ℝ => contV α (Kc α * x * u))
        (volume.restrict (Ioc (0:ℝ) (p0 / (Kc α * x)))) :=
      (aemeasurable_restrict_of_monotoneOn measurableSet_Ioo hmono).mono_measure
        (Measure.restrict_mono hsub le_rfl)
    have hHm : AEMeasurable (H x) (volume.restrict (Ioc (0:ℝ) (p0 / (Kc α * x)))) := by
      have hA : AEMeasurable (fun u : ℝ => (1 - Kc α * x * u) / ((Kc α * x * u) * contV α (Kc α * x * u)))
          (volume.restrict (Ioc (0:ℝ) (p0 / (Kc α * x)))) :=
        ((by fun_prop : Measurable fun u : ℝ => 1 - Kc α * x * u).aemeasurable).div
          (((by fun_prop : Measurable fun u : ℝ => Kc α * x * u).aemeasurable).mul hV)
      have hB : AEMeasurable (fun u : ℝ => contV α (Kc α * x * u) / (contV α (Kc α * x * u) + x ^ α))
          (volume.restrict (Ioc (0:ℝ) (p0 / (Kc α * x)))) :=
        hV.div (hV.add (measurable_const : Measurable fun _ : ℝ => x ^ α).aemeasurable)
      simp only [hH, profF]
      exact (measurable_const.aemeasurable).mul
        ((Real.continuous_sqrt.measurable.comp_aemeasurable hA).mul hB)
    exact (((aemeasurable_indicator_iff measurableSet_Ioc).2 hHm).mono_measure
      Measure.restrict_le_self).aestronglyMeasurable
  have hbound : ∀ x : ℝ, 0 < x → ∀ᵐ u ∂(volume.restrict (Ioi (0:ℝ))),
      ‖(Ioc (0:ℝ) (p0 / (Kc α * x))).indicator (H x) u‖ ≤ D u := by
    intro x hx
    refine (ae_restrict_iff' measurableSet_Ioi).2 (ae_of_all _ fun u hu => ?_)
    have hu0 : 0 < u := hu
    have hc : 0 < Kc α * x := mul_pos hK hx
    have hDnn : 0 ≤ D u := by
      simp only [hD]
      positivity
    by_cases hmem : u ∈ Ioc (0:ℝ) (p0 / (Kc α * x))
    · rw [Set.indicator_of_mem hmem]
      have hxu : Kc α * x * u ≤ p0 := by
        have := (le_div_iff₀ hc).1 hmem.2
        linarith
      simp only [hH]
      rw [prof_gt_Hform hα1 hp0 hp01 hx hu0 hxu]
      have hpp : Kc α * x * u ∈ Ioc (0:ℝ) p0 := ⟨by positivity, hxu⟩
      have hR := hr _ hpp
      have hdiv : Kc α * x * u / Kc α = x * u := by field_simp
      rw [hdiv] at hR
      exact prof_gt_bound_alg hK hu0 hR.1 hR.2 hpp.1.le (lt_of_le_of_lt hxu hp01)
    · rw [Set.indicator_of_notMem hmem, norm_zero]
      exact hDnn
  have hlim : ∀ᵐ u ∂(volume.restrict (Ioi (0:ℝ))), Tendsto
      (fun x : ℝ => (Ioc (0:ℝ) (p0 / (Kc α * x))).indicator (H x) u) (𝓝[>] (0:ℝ)) (𝓝 (L u)) := by
    refine (ae_restrict_iff' measurableSet_Ioi).2 (ae_of_all _ fun u hu => ?_)
    have hu0 : 0 < u := hu
    set Rf : ℝ → ℝ := fun x => contV α (Kc α * x * u) / (x * u) ^ α with hRf
    have hφ : Tendsto (fun x : ℝ => Kc α * x * u) (𝓝[>] (0:ℝ)) (𝓝[>] (0:ℝ)) := by
      apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
      · have hcont : Continuous fun x : ℝ => Kc α * x * u := by fun_prop
        have h := (hcont.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0:ℝ)))
        simpa using h
      · filter_upwards [self_mem_nhdsWithin] with x hx
        exact mul_pos (mul_pos hK hx) hu0
    have hRt : Tendsto Rf (𝓝[>] (0:ℝ)) (𝓝 1) := by
      have h := (prof_gt_r hα1).comp hφ
      refine h.congr (fun x => ?_)
      simp only [Function.comp, hRf]
      rw [show Kc α * x * u / Kc α = x * u by field_simp]
    have h1 : Tendsto (fun x : ℝ => 1 - Kc α * x * u) (𝓝[>] (0:ℝ)) (𝓝 1) := by
      have hcont : Continuous fun x : ℝ => 1 - Kc α * x * u := by fun_prop
      have h := (hcont.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0:ℝ)))
      simpa using h
    have h2 := (h1.div hRt one_ne_zero).sqrt
    have h3 := (hRt.mul_const (u ^ α)).div ((hRt.mul_const (u ^ α)).add_const 1)
      (by have := Real.rpow_pos_of_pos hu0 α; positivity)
    have h4 := (tendsto_const_nhds (x := Real.sqrt (Kc α))).mul
      (h2.mul ((tendsto_const_nhds (x := u ^ (-((α + 1) / 2)))).mul h3))
    have hlimeq : Real.sqrt (Kc α) * (Real.sqrt (1 / 1) * (u ^ (-((α + 1) / 2)) *
        (1 * u ^ α / (1 * u ^ α + 1)))) = L u := by
      have heB : u ^ (-((α + 1) / 2)) * u ^ α = u ^ ((α - 1) / 2) := by
        rw [← Real.rpow_add hu0]
        congr 1
        ring
      simp only [hL, div_one, Real.sqrt_one, one_mul]
      rw [← heB, add_comm (u ^ α) 1]
      ring
    rw [hlimeq] at h4
    refine h4.congr' ?_
    filter_upwards [Ioo_mem_nhdsGT (div_pos hp0 (mul_pos hK hu0))] with x hx
    have hx0 : 0 < x := hx.1
    have hc : 0 < Kc α * x := mul_pos hK hx0
    have hxu : Kc α * x * u ≤ p0 := by
      have := (lt_div_iff₀ (mul_pos hK hu0)).1 hx.2
      nlinarith
    have hmem : u ∈ Ioc (0:ℝ) (p0 / (Kc α * x)) := ⟨hu0, (le_div_iff₀ hc).2 (by nlinarith)⟩
    rw [Set.indicator_of_mem hmem]
    simp only [hH]
    rw [prof_gt_Hform hα1 hp0 hp01 hx0 hu0 hxu]
    rfl
  have hdct := tendsto_integral_filter_of_dominated_convergence (l := 𝓝[>] (0:ℝ)) D
    (Filter.eventually_of_mem self_mem_nhdsWithin hmeas)
    (Filter.eventually_of_mem self_mem_nhdsWithin hbound)
    hDint hlim
  rw [hLint] at hdct
  exact hdct.congr' (by
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact (hscale x hx).symm)

private lemma prof_exists_delta {P : ℝ → Prop} (h : ∀ᶠ p in 𝓝[>] (0:ℝ), P p) :
    ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧ ∀ p ∈ Ioc (0:ℝ) δ, P p := by
  have h3 := h.and (Ioo_mem_nhdsGT (zero_lt_one : (0:ℝ) < 1))
  obtain ⟨u, hu, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 h3
  have hu' := Set.mem_Ioi.1 hu
  refine ⟨u / 2, by linarith, ?_, ?_⟩
  · exact (hsub (⟨by linarith, by linarith⟩ : u / 2 ∈ Ioo (0:ℝ) u)).2.2
  · intro p hp
    exact (hsub ⟨hp.1, by linarith [hp.2]⟩).1

private lemma prof_equiv_of_squeeze {l : Filter ℝ} {u v : ℝ → ℝ}
    (hv : ∀ᶠ x in l, 0 ≤ v x)
    (h : ∀ ε : ℝ, 0 < ε → ε < 1 → ∀ᶠ x in l, (1 - ε) * v x ≤ u x ∧ u x ≤ (1 + ε) * v x) :
    IsEquivalent l u v := by
  rw [IsEquivalent, Asymptotics.isLittleO_iff]
  intro c hc
  have h2 := h (min c (1 / 2)) (lt_min hc (by norm_num)) (lt_of_le_of_lt (min_le_right _ _) (by norm_num))
  filter_upwards [hv, h2] with x hx0 hx
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hx0, abs_le]
  have hmin : min c (1 / 2) ≤ c := min_le_left _ _
  have hmv : min c (1 / 2) * v x ≤ c * v x := mul_le_mul_of_nonneg_right hmin hx0
  simp only [Pi.sub_apply]
  constructor <;> nlinarith [hx.1, hx.2]

private lemma prof_lt_rho {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) :
    Tendsto (fun p : ℝ => contV α p / ((1 - α) * p)) (𝓝[>] (0:ℝ)) (𝓝 1) := by
  have hm : 0 < 1 - α := by linarith
  have h := lem_app_pl_continuum_iii_lt hα0 hα1
  have hz : ∀ᶠ p in 𝓝[>] (0:ℝ), (fun p : ℝ => (1 - α) * p) p ≠ 0 := by
    filter_upwards [self_mem_nhdsWithin] with p hp
    exact (mul_pos hm (Set.mem_Ioi.1 hp)).ne'
  exact (isEquivalent_iff_tendsto_one hz).1 h

private lemma prof_lt_gm {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) :
    Tendsto (fun p : ℝ => Real.sqrt ((1 - p) / (p * contV α p)) * (Real.sqrt (1 - α) * p))
      (𝓝[>] (0:ℝ)) (𝓝 1) := by
  have hm : 0 < 1 - α := by linarith
  have hρ' := prof_lt_rho hα0 hα1
  have h1 : Tendsto (fun p : ℝ => 1 - p) (𝓝[>] (0:ℝ)) (𝓝 1) := by
    have hcont : Continuous fun p : ℝ => 1 - p := by fun_prop
    have h := (hcont.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0:ℝ)))
    simpa using h
  have h2 := (h1.div hρ' one_ne_zero).sqrt
  rw [div_one, Real.sqrt_one] at h2
  refine h2.congr' ?_
  filter_upwards [Ioo_mem_nhdsGT (zero_lt_one : (0:ℝ) < 1)] with p hp
  have hV := (prof_contV_spec (α := α) hα0 hp).1
  have hp0 := hp.1
  have hA : 0 ≤ (1 - p) / (p * contV α p) :=
    div_nonneg (by linarith [hp.2]) (by positivity)
  have e : (1 - p) / (contV α p / ((1 - α) * p))
      = ((1 - p) / (p * contV α p) * (1 - α)) * p ^ 2 := by
    field_simp
  simp only [Pi.div_apply]
  rw [e, Real.sqrt_mul (mul_nonneg hA hm.le), Real.sqrt_mul hA, Real.sqrt_sq hp0.le]
  ring

private lemma prof_log_int {δ b : ℝ} (hδ : 0 < δ) (hb : 0 < b) :
    IntervalIntegrable (fun p : ℝ => 1 / (p + b)) volume 0 δ ∧
    ∫ p in (0:ℝ)..δ, 1 / (p + b) = Real.log ((δ + b) / b) := by
  constructor
  · apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.div continuousOn_const (continuousOn_id.add continuousOn_const)
    intro p hp
    rw [Set.uIcc_of_le hδ.le] at hp
    have := hp.1
    show p + b ≠ 0
    linarith
  · have h := intervalIntegral.integral_comp_add_right (a := 0) (b := δ)
      (fun x : ℝ => 1 / x) b
    rw [zero_add] at h
    rw [h, integral_one_div_of_pos hb (by linarith)]

private lemma prof_F_le {c p a V : ℝ} (hc : 0 < c) (hp : 0 < p) (ha : 0 < a) (hV : 0 < V)
    (h : V ≤ c * p) : V / (V + a) ≤ p / (p + a / c) := by
  have : p / (p + a / c) = c * p / (c * p + a) := by field_simp
  rw [this, div_le_div_iff₀ (by linarith) (by positivity)]
  nlinarith

private lemma prof_F_ge {c p a V : ℝ} (hc : 0 < c) (hp : 0 < p) (ha : 0 < a)
    (h : c * p ≤ V) : p / (p + a / c) ≤ V / (V + a) := by
  have : p / (p + a / c) = c * p / (c * p + a) := by field_simp
  have hcp : 0 < c * p := mul_pos hc hp
  rw [this, div_le_div_iff₀ (by linarith) (by linarith)]
  nlinarith

private lemma prof_lt_pointwise {α ε x p : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (hε0 : 0 < ε) (hε1 : ε < 1) (hx : 0 < x) (hp : p ∈ Ioo (0:ℝ) 1)
    (hV1 : (1 - ε) * ((1 - α) * p) ≤ contV α p) (hV2 : contV α p ≤ (1 + ε) * ((1 - α) * p))
    (hg1 : 1 - ε ≤ Real.sqrt ((1 - p) / (p * contV α p)) * (Real.sqrt (1 - α) * p))
    (hg2 : Real.sqrt ((1 - p) / (p * contV α p)) * (Real.sqrt (1 - α) * p) ≤ 1 + ε) :
    (1 - ε) / Real.sqrt (1 - α) *
        (1 / (p + x ^ α / ((1 - ε) * (1 - α))))
      ≤ Real.sqrt ((1 - p) / (p * contV α p)) * profF α x p ∧
    Real.sqrt ((1 - p) / (p * contV α p)) * profF α x p ≤
      (1 + ε) / Real.sqrt (1 - α) * (1 / (p + x ^ α / ((1 + ε) * (1 - α)))) := by
  have hm : 0 < 1 - α := by linarith
  have hsm : 0 < Real.sqrt (1 - α) := Real.sqrt_pos.2 hm
  have hp0 := hp.1
  have hV := (prof_contV_spec (α := α) hα0 hp).1
  have ha : 0 < x ^ α := Real.rpow_pos_of_pos hx α
  have hc1 : 0 < (1 - ε) * (1 - α) := mul_pos (by linarith) hm
  have hc2 : 0 < (1 + ε) * (1 - α) := mul_pos (by linarith) hm
  have hg0 : 0 ≤ Real.sqrt ((1 - p) / (p * contV α p)) := Real.sqrt_nonneg _
  have hmp : 0 < Real.sqrt (1 - α) * p := mul_pos hsm hp0
  have hFup := prof_F_le hc2 hp0 ha hV (by linarith : contV α p ≤ ((1 + ε) * (1 - α)) * p)
  have hFlo := prof_F_ge hc1 hp0 ha (by linarith : ((1 - ε) * (1 - α)) * p ≤ contV α p)
  have hF0 : 0 ≤ profF α x p := (prof_F_bounds hα0 hx hp).1
  have hgup : Real.sqrt ((1 - p) / (p * contV α p)) ≤ (1 + ε) / (Real.sqrt (1 - α) * p) := by
    rw [le_div_iff₀ hmp]; exact hg2
  have hglo : (1 - ε) / (Real.sqrt (1 - α) * p) ≤ Real.sqrt ((1 - p) / (p * contV α p)) := by
    rw [div_le_iff₀ hmp]; exact hg1
  have hq1 : 0 < p + x ^ α / ((1 - ε) * (1 - α)) := by positivity
  have hq2 : 0 < p + x ^ α / ((1 + ε) * (1 - α)) := by positivity
  constructor
  · have e : (1 - ε) / Real.sqrt (1 - α) * (1 / (p + x ^ α / ((1 - ε) * (1 - α))))
        = (1 - ε) / (Real.sqrt (1 - α) * p) * (p / (p + x ^ α / ((1 - ε) * (1 - α)))) := by
      field_simp
    rw [e]
    unfold profF at hFlo ⊢
    exact mul_le_mul hglo hFlo (by positivity) hg0
  · have e : (1 + ε) / Real.sqrt (1 - α) * (1 / (p + x ^ α / ((1 + ε) * (1 - α))))
        = (1 + ε) / (Real.sqrt (1 - α) * p) * (p / (p + x ^ α / ((1 + ε) * (1 - α)))) := by
      field_simp
    rw [e]
    unfold profF at hFup ⊢
    exact mul_le_mul hgup hFup hF0 (by positivity)

private lemma prof_lt_bounds {α ε : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hε0 : 0 < ε) (hε1 : ε < 1) :
    ∃ C₁ C₂ : ℝ, ∀ x ∈ Ioc (0:ℝ) 1,
      (1 - ε) / Real.sqrt (1 - α) * (-α * Real.log x) + C₂ ≤
        ∫ p in (0:ℝ)..1, Real.sqrt ((1 - p) / (p * contV α p)) * profF α x p ∧
      ∫ p in (0:ℝ)..1, Real.sqrt ((1 - p) / (p * contV α p)) * profF α x p ≤
        (1 + ε) / Real.sqrt (1 - α) * (-α * Real.log x) + C₁ := by
  have hm : 0 < 1 - α := by linarith
  have hsm : 0 < Real.sqrt (1 - α) := Real.sqrt_pos.2 hm
  have hρ := prof_lt_rho hα0 hα1
  have hgm := prof_lt_gm hα0 hα1
  have hev : ∀ᶠ p in 𝓝[>] (0:ℝ),
      ((1 - ε) < contV α p / ((1 - α) * p) ∧ contV α p / ((1 - α) * p) < 1 + ε) ∧
      ((1 - ε) < Real.sqrt ((1 - p) / (p * contV α p)) * (Real.sqrt (1 - α) * p) ∧
        Real.sqrt ((1 - p) / (p * contV α p)) * (Real.sqrt (1 - α) * p) < 1 + ε) := by
    refine ((hρ.eventually (lt_mem_nhds (by linarith : 1 - ε < 1))).and
      (hρ.eventually (gt_mem_nhds (by linarith : (1:ℝ) < 1 + ε)))).and
      ((hgm.eventually (lt_mem_nhds (by linarith : 1 - ε < 1))).and
      (hgm.eventually (gt_mem_nhds (by linarith : (1:ℝ) < 1 + ε)))) |>.mono ?_
    intro p hp
    exact ⟨⟨hp.1.1, hp.1.2⟩, ⟨hp.2.1, hp.2.2⟩⟩
  obtain ⟨δ, hδ0, hδ1, hδ⟩ := prof_exists_delta hev
  obtain ⟨M, hM⟩ := prof_gt_tail hα0 hδ0 hδ1
  set c₁ : ℝ := (1 - ε) * (1 - α) with hc₁
  set c₂ : ℝ := (1 + ε) * (1 - α) with hc₂
  have hc₁0 : 0 < c₁ := mul_pos (by linarith) hm
  have hc₂0 : 0 < c₂ := mul_pos (by linarith) hm
  refine ⟨(1 + ε) / Real.sqrt (1 - α) * (Real.log (δ + 1 / c₂) + Real.log c₂) + M,
    (1 - ε) / Real.sqrt (1 - α) * (Real.log δ + Real.log c₁) - M, fun x hx => ?_⟩
  have hx0 : 0 < x := hx.1
  have ha : 0 < x ^ α := Real.rpow_pos_of_pos hx0 α
  have ha1 : x ^ α ≤ 1 := Real.rpow_le_one hx0.le hx.2 hα0.le
  have hI := prof_u_integrable hα0 hx
  have hsplit : ∫ p in (0:ℝ)..1, Real.sqrt ((1 - p) / (p * contV α p)) * profF α x p
      = (∫ p in (0:ℝ)..δ, Real.sqrt ((1 - p) / (p * contV α p)) * profF α x p)
        + ∫ p in δ..1, Real.sqrt ((1 - p) / (p * contV α p)) * profF α x p := by
    rw [intervalIntegral.integral_add_adjacent_intervals]
    · exact hI.mono_set (by
        rw [Set.uIcc_of_le hδ0.le, Set.uIcc_of_le zero_le_one]
        exact Icc_subset_Icc le_rfl hδ1.le)
    · exact hI.mono_set (by
        rw [Set.uIcc_of_le hδ1.le, Set.uIcc_of_le zero_le_one]
        exact Icc_subset_Icc hδ0.le le_rfl)
  have hIδ : IntervalIntegrable
      (fun p : ℝ => Real.sqrt ((1 - p) / (p * contV α p)) * profF α x p) volume 0 δ :=
    hI.mono_set (by
      rw [Set.uIcc_of_le hδ0.le, Set.uIcc_of_le zero_le_one]
      exact Icc_subset_Icc le_rfl hδ1.le)
  have hbp : 0 < x ^ α / c₂ := div_pos ha hc₂0
  have hbm : 0 < x ^ α / c₁ := div_pos ha hc₁0
  obtain ⟨hi1, hv1⟩ := prof_log_int hδ0 hbp
  obtain ⟨hi2, hv2⟩ := prof_log_int hδ0 hbm
  have hpt : ∀ p ∈ Ioo (0:ℝ) δ,
      (1 - ε) / Real.sqrt (1 - α) * (1 / (p + x ^ α / ((1 - ε) * (1 - α))))
        ≤ Real.sqrt ((1 - p) / (p * contV α p)) * profF α x p ∧
      Real.sqrt ((1 - p) / (p * contV α p)) * profF α x p ≤
        (1 + ε) / Real.sqrt (1 - α) * (1 / (p + x ^ α / ((1 + ε) * (1 - α)))) := by
    intro p hp
    have hpI : p ∈ Ioo (0:ℝ) 1 := ⟨hp.1, lt_trans hp.2 hδ1⟩
    have h := hδ p ⟨hp.1, hp.2.le⟩
    have hρp := h.1
    have hV1 : (1 - ε) * ((1 - α) * p) ≤ contV α p := by
      have := hρp.1
      rw [lt_div_iff₀ (mul_pos hm hp.1)] at this
      exact this.le
    have hV2 : contV α p ≤ (1 + ε) * ((1 - α) * p) := by
      have := hρp.2
      rw [div_lt_iff₀ (mul_pos hm hp.1)] at this
      exact this.le
    exact prof_lt_pointwise hα0 hα1 hε0 hε1 hx0 hpI hV1 hV2 h.2.1.le h.2.2.le
  have hup : ∫ p in (0:ℝ)..δ, Real.sqrt ((1 - p) / (p * contV α p)) * profF α x p
      ≤ (1 + ε) / Real.sqrt (1 - α) * Real.log ((δ + x ^ α / c₂) / (x ^ α / c₂)) := by
    rw [← hv1, ← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_mono_on_of_le_Ioo hδ0.le hIδ (hi1.const_mul _)
      (fun p hp => (hpt p hp).2)
  have hlo : (1 - ε) / Real.sqrt (1 - α) * Real.log ((δ + x ^ α / c₁) / (x ^ α / c₁))
      ≤ ∫ p in (0:ℝ)..δ, Real.sqrt ((1 - p) / (p * contV α p)) * profF α x p := by
    rw [← hv2, ← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_mono_on_of_le_Ioo hδ0.le (hi2.const_mul _) hIδ
      (fun p hp => (hpt p hp).1)
  have htail := abs_le.1 (by simpa [Real.norm_eq_abs] using hM x hx0)
  have hlogx : Real.log (x ^ α) = α * Real.log x := Real.log_rpow hx0 α
  constructor
  · -- lower bound
    have hl : Real.log δ + Real.log c₁ - α * Real.log x
        ≤ Real.log ((δ + x ^ α / c₁) / (x ^ α / c₁)) := by
      rw [Real.log_div (by positivity) hbm.ne', Real.log_div ha.ne' hc₁0.ne', hlogx]
      have : Real.log δ ≤ Real.log (δ + x ^ α / c₁) :=
        Real.log_le_log hδ0 (by linarith)
      linarith
    have hpos : 0 ≤ (1 - ε) / Real.sqrt (1 - α) := by
      apply div_nonneg (by linarith) hsm.le
    have := mul_le_mul_of_nonneg_left hl hpos
    rw [hsplit]
    nlinarith [htail.1, htail.2]
  · -- upper bound
    have hb1 : x ^ α / c₂ ≤ 1 / c₂ := div_le_div_of_nonneg_right ha1 hc₂0.le
    have hl : Real.log ((δ + x ^ α / c₂) / (x ^ α / c₂))
        ≤ Real.log (δ + 1 / c₂) + Real.log c₂ - α * Real.log x := by
      rw [Real.log_div (by positivity) hbp.ne', Real.log_div ha.ne' hc₂0.ne', hlogx]
      have : Real.log (δ + x ^ α / c₂) ≤ Real.log (δ + 1 / c₂) :=
        Real.log_le_log (by positivity) (by linarith)
      linarith
    have hpos : 0 ≤ (1 + ε) / Real.sqrt (1 - α) := by
      apply div_nonneg (by linarith) hsm.le
    have := mul_le_mul_of_nonneg_left hl hpos
    rw [hsplit]
    nlinarith [htail.1, htail.2]

/-- `lem:app-pl-Psi` (snapshot `cr-2026-10-23`), part (ii), the first equivalence in
`eqn:app-pl-bulk-small` for `0 < α < 1`. Statement verbatim:

\begin{lemma}[The profile $\Psi_\alpha$]\label{lem:app-pl-Psi}
$\Psi_\alpha$ is finite, positive and continuous on $(0,1]$, bounded below by a
positive constant, and satisfies the first equivalences of
\cref{eqn:app-pl-bulk-small}.
\end{lemma}

\begin{equation}\label{eqn:app-pl-bulk-small}
\begin{gathered}
\Psi_\alpha(x)\sim\begin{cases}\dfrac{c_0}{\sqrt{1-\alpha}}\log(x^{-\alpha}),&\alpha<1,\\[6pt]
\dfrac23c_0\big[\log(1/x)\big]^{3/2},&\alpha=1,\\[6pt]
d_\alpha\sqrt{K_\alpha}\,x^{-(\alpha-1)/2},&\alpha>1,\end{cases}
\\
\Gamma_\alpha(x)\sim\begin{cases}\dfrac{x^\alpha\big[\log(x^{-\alpha})\big]^2}{1-\alpha},&\alpha<1,\\[6pt]
\dfrac49x\big[\log(1/x)\big]^3,&\alpha=1,\\[6pt]
\dfrac{4K_\alpha^2}{\alpha-1}\,x,&\alpha>1.\end{cases}
\end{gathered}
\end{equation} -/
theorem lem_app_pl_Psi_ii_lt {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) :
    IsEquivalent (𝓝[>] (0:ℝ)) (fun x : ℝ => profPsi α x)
      (fun x : ℝ => c0 / Real.sqrt (1 - α) * Real.log (x ^ (-α))) := by
  have hm : 0 < 1 - α := by linarith
  have hsm : 0 < Real.sqrt (1 - α) := Real.sqrt_pos.2 hm
  have hc0 := prof_c0_pos
  have hT : Tendsto (fun x : ℝ => -α * Real.log x) (𝓝[>] (0:ℝ)) atTop :=
    Real.tendsto_log_nhdsGT_zero.const_mul_atBot_of_neg (neg_neg_of_pos hα0)
  refine prof_equiv_of_squeeze ?_ ?_
  · filter_upwards [Ioo_mem_nhdsGT (zero_lt_one : (0:ℝ) < 1)] with x hx
    rw [Real.log_rpow hx.1]
    have : Real.log x ≤ 0 := (Real.log_neg hx.1 hx.2).le
    have : 0 ≤ -α * Real.log x := by nlinarith
    show 0 ≤ c0 / Real.sqrt (1 - α) * (-α * Real.log x)
    positivity
  · intro ε hε0 hε1
    obtain ⟨C₁, C₂, hC⟩ := prof_lt_bounds hα0 hα1 (half_pos hε0) (by linarith : ε / 2 < 1)
    filter_upwards [Ioc_mem_nhdsGT (zero_lt_one : (0:ℝ) < 1),
      hT.eventually_ge_atTop (2 * Real.sqrt (1 - α) * (|C₁| + |C₂|) / ε + 1)] with x hx hTx
    have hx0 : 0 < x := hx.1
    obtain ⟨hlo, hup⟩ := hC x hx
    set T : ℝ := -α * Real.log x with hTdef
    set I : ℝ := ∫ p in (0:ℝ)..1, Real.sqrt ((1 - p) / (p * contV α p)) * profF α x p with hI
    have hlog : Real.log (x ^ (-α)) = T := by
      rw [Real.log_rpow hx0]
    have hq : 0 ≤ ε / 2 / Real.sqrt (1 - α) := by positivity
    have hmul := mul_le_mul_of_nonneg_left hTx hq
    have hval : ε / 2 / Real.sqrt (1 - α) * (2 * Real.sqrt (1 - α) * (|C₁| + |C₂|) / ε)
        = |C₁| + |C₂| := by
      field_simp
    have hC1 : C₁ ≤ ε / 2 / Real.sqrt (1 - α) * T := by
      have := le_abs_self C₁
      have := abs_nonneg C₂
      nlinarith [mul_nonneg hq (by norm_num : (0:ℝ) ≤ 1)]
    have hC2 : -(ε / 2 / Real.sqrt (1 - α) * T) ≤ C₂ := by
      have := neg_abs_le C₂
      have := abs_nonneg C₁
      nlinarith [mul_nonneg hq (by norm_num : (0:ℝ) ≤ 1)]
    have hIup : I ≤ (1 + ε) / Real.sqrt (1 - α) * T := by
      have : (1 + ε / 2) / Real.sqrt (1 - α) * T + ε / 2 / Real.sqrt (1 - α) * T
          = (1 + ε) / Real.sqrt (1 - α) * T := by ring
      linarith
    have hIlo : (1 - ε) / Real.sqrt (1 - α) * T ≤ I := by
      have : (1 - ε / 2) / Real.sqrt (1 - α) * T - ε / 2 / Real.sqrt (1 - α) * T
          = (1 - ε) / Real.sqrt (1 - α) * T := by ring
      linarith
    show (1 - ε) * (c0 / Real.sqrt (1 - α) * Real.log (x ^ (-α))) ≤ profPsi α x ∧
      profPsi α x ≤ (1 + ε) * (c0 / Real.sqrt (1 - α) * Real.log (x ^ (-α)))
    rw [hlog]
    unfold profPsi
    constructor
    · have := mul_le_mul_of_nonneg_left hIlo hc0.le
      calc (1 - ε) * (c0 / Real.sqrt (1 - α) * T) = c0 * ((1 - ε) / Real.sqrt (1 - α) * T) := by ring
        _ ≤ c0 * I := this
    · have := mul_le_mul_of_nonneg_left hIup hc0.le
      calc c0 * I ≤ c0 * ((1 + ε) / Real.sqrt (1 - α) * T) := this
        _ = (1 + ε) * (c0 / Real.sqrt (1 - α) * T) := by ring

private lemma prof_one_antideriv {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hb : b < 1) :
    ∫ p in a..b, Real.sqrt (-Real.log p) / p =
      2 / 3 * ((-Real.log a) * Real.sqrt (-Real.log a)
        - (-Real.log b) * Real.sqrt (-Real.log b)) := by
  have hderiv : ∀ p ∈ Set.uIcc a b, HasDerivAt
      (fun p : ℝ => -(2 / 3) * ((-Real.log p) * Real.sqrt (-Real.log p)))
      (Real.sqrt (-Real.log p) / p) p := by
    intro p hp
    rw [Set.uIcc_of_le hab] at hp
    have hp0 : 0 < p := lt_of_lt_of_le ha hp.1
    have hp1 : p < 1 := lt_of_le_of_lt hp.2 hb
    have hl : 0 < -Real.log p := neg_pos.2 (Real.log_neg hp0 hp1)
    have h1 : HasDerivAt (fun p : ℝ => -Real.log p) (-(p⁻¹)) p := (Real.hasDerivAt_log hp0.ne').neg
    have h2 := h1.sqrt hl.ne'
    have h3 := h1.mul h2
    have h4 := h3.const_mul (-(2 / 3))
    convert h4 using 1
    have hs : Real.sqrt (-Real.log p) ≠ 0 := (Real.sqrt_pos.2 hl).ne'
    have hss : Real.sqrt (-Real.log p) * Real.sqrt (-Real.log p) = -Real.log p :=
      Real.mul_self_sqrt hl.le
    field_simp
    nlinarith [hss]
  have hint : IntervalIntegrable (fun p : ℝ => Real.sqrt (-Real.log p) / p) volume a b := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hab]
    apply ContinuousOn.div
    · exact (Real.continuousOn_log.neg.sqrt).mono (by
        intro p hp
        exact (lt_of_lt_of_le ha hp.1).ne')
    · exact continuousOn_id
    · intro p hp
      exact (lt_of_lt_of_le ha hp.1).ne'
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  ring

private lemma prof_one_lam :
    Tendsto (fun p : ℝ => contV 1 p / (p / (-Real.log p))) (𝓝[>] (0:ℝ)) (𝓝 1) := by
  have h := lem_app_pl_continuum_iii_one
  have hz : ∀ᶠ p in 𝓝[>] (0:ℝ), (fun p : ℝ => p / Real.log (1 / p)) p ≠ 0 := by
    filter_upwards [Ioo_mem_nhdsGT (zero_lt_one : (0:ℝ) < 1)] with p hp
    have : 0 < Real.log (1 / p) := Real.log_pos (one_lt_one_div hp.1 hp.2)
    exact (div_pos hp.1 this).ne'
  have h2 := (isEquivalent_iff_tendsto_one hz).1 h
  refine h2.congr (fun p => ?_)
  simp only [Pi.div_apply, one_div, Real.log_inv]

private lemma prof_one_gh :
    Tendsto (fun p : ℝ => Real.sqrt ((1 - p) / (p * contV 1 p)) * p / Real.sqrt (-Real.log p))
      (𝓝[>] (0:ℝ)) (𝓝 1) := by
  have hlam := prof_one_lam
  have h1 : Tendsto (fun p : ℝ => 1 - p) (𝓝[>] (0:ℝ)) (𝓝 1) := by
    have hcont : Continuous fun p : ℝ => 1 - p := by fun_prop
    have h := (hcont.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0:ℝ)))
    simpa using h
  have h2 := (h1.div hlam one_ne_zero).sqrt
  rw [div_one, Real.sqrt_one] at h2
  refine h2.congr' ?_
  filter_upwards [Ioo_mem_nhdsGT (zero_lt_one : (0:ℝ) < 1)] with p hp
  have hV := (prof_contV_spec (α := 1) zero_lt_one hp).1
  have hp0 := hp.1
  have hl : 0 < -Real.log p := neg_pos.2 (Real.log_neg hp0 hp.2)
  have hsl : 0 < Real.sqrt (-Real.log p) := Real.sqrt_pos.2 hl
  have hlam0 : 0 < contV 1 p / (p / (-Real.log p)) := by positivity
  have hA : 0 ≤ (1 - p) / (contV 1 p / (p / (-Real.log p))) :=
    div_nonneg (by linarith [hp.2]) hlam0.le
  have e : (1 - p) / (p * contV 1 p)
      = ((1 - p) / (contV 1 p / (p / (-Real.log p)))) * (-Real.log p) * (1 / p) ^ 2 := by
    have hlp : Real.log p ≠ 0 := by
      intro h
      rw [h] at hl
      simp at hl
    field_simp
  simp only [Pi.div_apply]
  rw [e, Real.sqrt_mul (mul_nonneg hA hl.le), Real.sqrt_mul hA, Real.sqrt_sq (by positivity)]
  field_simp

private lemma prof_one_eps {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) :
    ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧ ∀ p ∈ Ioc (0:ℝ) δ,
      (1 - ε) * (p / (-Real.log p)) ≤ contV 1 p ∧ contV 1 p ≤ (1 + ε) * (p / (-Real.log p)) ∧
      (1 - ε) * (Real.sqrt (-Real.log p) / p) ≤ Real.sqrt ((1 - p) / (p * contV 1 p)) ∧
      Real.sqrt ((1 - p) / (p * contV 1 p)) ≤ (1 + ε) * (Real.sqrt (-Real.log p) / p) := by
  have hlam := prof_one_lam
  have hgh := prof_one_gh
  have hev : ∀ᶠ p in 𝓝[>] (0:ℝ),
      ((1 - ε < contV 1 p / (p / (-Real.log p)) ∧ contV 1 p / (p / (-Real.log p)) < 1 + ε) ∧
      (1 - ε < Real.sqrt ((1 - p) / (p * contV 1 p)) * p / Real.sqrt (-Real.log p) ∧
        Real.sqrt ((1 - p) / (p * contV 1 p)) * p / Real.sqrt (-Real.log p) < 1 + ε)) ∧
      p ∈ Ioo (0:ℝ) 1 := by
    refine (((hlam.eventually (lt_mem_nhds (by linarith : 1 - ε < 1))).and
      (hlam.eventually (gt_mem_nhds (by linarith : (1:ℝ) < 1 + ε)))).and
      ((hgh.eventually (lt_mem_nhds (by linarith : 1 - ε < 1))).and
      (hgh.eventually (gt_mem_nhds (by linarith : (1:ℝ) < 1 + ε))))).and
      (Ioo_mem_nhdsGT (zero_lt_one : (0:ℝ) < 1)) |>.mono ?_
    intro p hp
    exact ⟨⟨⟨hp.1.1.1, hp.1.1.2⟩, ⟨hp.1.2.1, hp.1.2.2⟩⟩, hp.2⟩
  obtain ⟨δ, hδ0, hδ1, hδ⟩ := prof_exists_delta hev
  refine ⟨δ, hδ0, hδ1, fun p hp => ?_⟩
  obtain ⟨⟨hl, hg⟩, hpI⟩ := hδ p hp
  have hp0 := hpI.1
  have hl' : 0 < -Real.log p := neg_pos.2 (Real.log_neg hp0 hpI.2)
  have hsl : 0 < Real.sqrt (-Real.log p) := Real.sqrt_pos.2 hl'
  have hpl : 0 < p / (-Real.log p) := div_pos hp0 hl'
  refine ⟨?_, ?_, ?_, ?_⟩
  · have := hl.1
    rw [lt_div_iff₀ hpl] at this
    exact this.le
  · have := hl.2
    rw [div_lt_iff₀ hpl] at this
    exact this.le
  · have := (lt_div_iff₀ hsl).1 hg.1
    rw [← mul_div_assoc, div_le_iff₀ hp0]
    exact this.le
  · have := (div_lt_iff₀ hsl).1 hg.2
    rw [← mul_div_assoc, le_div_iff₀ hp0]
    exact this.le

private lemma prof_one_Aint {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    IntervalIntegrable (fun p : ℝ => Real.sqrt (-Real.log p) / p) volume a b := by
  apply ContinuousOn.intervalIntegrable
  rw [Set.uIcc_of_le hab]
  apply ContinuousOn.div
  · exact (Real.continuousOn_log.neg.sqrt).mono (by
      intro p hp
      exact (lt_of_lt_of_le ha hp.1).ne')
  · exact continuousOn_id
  · intro p hp
    exact (lt_of_lt_of_le ha hp.1).ne'

private lemma prof_one_pt {ε x p : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) (hx : 0 < x)
    (hp : p ∈ Ioo (0:ℝ) 1)
    (hδp : (1 - ε) * (p / (-Real.log p)) ≤ contV 1 p ∧
      contV 1 p ≤ (1 + ε) * (p / (-Real.log p)) ∧
      (1 - ε) * (Real.sqrt (-Real.log p) / p) ≤ Real.sqrt ((1 - p) / (p * contV 1 p)) ∧
      Real.sqrt ((1 - p) / (p * contV 1 p)) ≤ (1 + ε) * (Real.sqrt (-Real.log p) / p)) :
    -- upper bound by g
    Real.sqrt ((1 - p) / (p * contV 1 p)) * profF 1 x p ≤ (1 + ε) * (Real.sqrt (-Real.log p) / p) ∧
    -- upper bound by V/x
    Real.sqrt ((1 - p) / (p * contV 1 p)) * profF 1 x p ≤
      ((1 + ε) * (Real.sqrt (-Real.log p) / p)) * ((1 + ε) * (p / (-Real.log p))) / x ∧
    0 ≤ Real.sqrt ((1 - p) / (p * contV 1 p)) * profF 1 x p := by
  obtain ⟨hV1, hV2, hg1, hg2⟩ := hδp
  have hp0 : 0 < p := hp.1
  have hV := (prof_contV_spec (α := 1) zero_lt_one hp).1
  have hF := prof_F_bounds (α := 1) zero_lt_one hx hp
  have hg0 := Real.sqrt_nonneg ((1 - p) / (p * contV 1 p))
  have hx1 : 0 < x ^ (1:ℝ) := Real.rpow_pos_of_pos hx 1
  rw [Real.rpow_one] at hx1
  refine ⟨?_, ?_, mul_nonneg hg0 hF.1⟩
  · calc Real.sqrt ((1 - p) / (p * contV 1 p)) * profF 1 x p
        ≤ Real.sqrt ((1 - p) / (p * contV 1 p)) * 1 := mul_le_mul_of_nonneg_left hF.2 hg0
      _ ≤ _ := by rw [mul_one]; exact hg2
  · have hFx : profF 1 x p ≤ contV 1 p / x := by
      unfold profF
      rw [Real.rpow_one]
      exact div_le_div_of_nonneg_left hV.le hx (by linarith)
    calc Real.sqrt ((1 - p) / (p * contV 1 p)) * profF 1 x p
        ≤ Real.sqrt ((1 - p) / (p * contV 1 p)) * (contV 1 p / x) :=
          mul_le_mul_of_nonneg_left hFx hg0
      _ = (Real.sqrt ((1 - p) / (p * contV 1 p)) * contV 1 p) / x := by ring
      _ ≤ _ := by
          apply div_le_div_of_nonneg_right _ hx.le
          exact mul_le_mul hg2 hV2 hV.le (by
            have : 0 ≤ Real.sqrt (-Real.log p) / p := by positivity
            positivity)

private lemma prof_one_Flo {ε x q η p : ℝ} (hε1 : ε < 1) (hx : 0 < x) (hη : 0 ≤ η)
    (hp : p ∈ Ioo (0:ℝ) 1) (hxq : x ≤ q) (hqp : q ≤ p)
    (hcut : x * (-Real.log x) ≤ η * ((1 - ε) * q))
    (hV1 : (1 - ε) * (p / (-Real.log p)) ≤ contV 1 p) :
    1 - η ≤ profF 1 x p := by
  have hp0 : 0 < p := hp.1
  have hxp : x ≤ p := hxq.trans hqp
  have hx1 : x < 1 := lt_of_le_of_lt hxp hp.2
  have hq0 : 0 < q := lt_of_lt_of_le hx hxq
  have hL : 0 < -Real.log x := neg_pos.2 (Real.log_neg hx hx1)
  have hLp : 0 < -Real.log p := neg_pos.2 (Real.log_neg hp0 hp.2)
  have hLle : -Real.log p ≤ -Real.log x := by
    have := Real.log_le_log hx hxp
    linarith
  have hV := (prof_contV_spec (α := 1) zero_lt_one hp).1
  have h1 : (1 - ε) * q / (-Real.log x) ≤ (1 - ε) * (p / (-Real.log p)) := by
    rw [← mul_div_assoc]
    apply div_le_div₀ (by nlinarith) (mul_le_mul_of_nonneg_left hqp (by linarith)) hLp hLle
  have h2 : x ≤ η * ((1 - ε) * q / (-Real.log x)) := by
    rw [← mul_div_assoc, le_div_iff₀ hL]
    nlinarith
  have h3 : x ≤ η * contV 1 p := by
    have := mul_le_mul_of_nonneg_left (h1.trans hV1) hη
    linarith
  unfold profF
  rw [Real.rpow_one, le_div_iff₀ (by linarith)]
  nlinarith [mul_nonneg hη hx.le]

private lemma prof_one_upper_pt {ε x q p : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) (hx : 0 < x)
    (hp : p ∈ Ioo (0:ℝ) q) (hq1 : q < 1)
    (h : Real.sqrt ((1 - p) / (p * contV 1 p)) * profF 1 x p ≤
      ((1 + ε) * (Real.sqrt (-Real.log p) / p)) * ((1 + ε) * (p / (-Real.log p))) / x) :
    Real.sqrt ((1 - p) / (p * contV 1 p)) * profF 1 x p ≤ 4 / (x * Real.sqrt (-Real.log q)) := by
  have hp0 : 0 < p := hp.1
  have hq0 : 0 < q := lt_trans hp0 hp.2
  have hLp : 0 < -Real.log p := neg_pos.2 (Real.log_neg hp0 (lt_trans hp.2 hq1))
  have hLq : 0 < -Real.log q := neg_pos.2 (Real.log_neg hq0 hq1)
  have hsq : 0 < Real.sqrt (-Real.log q) := Real.sqrt_pos.2 hLq
  have hsp : 0 < Real.sqrt (-Real.log p) := Real.sqrt_pos.2 hLp
  have hss : Real.sqrt (-Real.log p) * Real.sqrt (-Real.log p) = -Real.log p :=
    Real.mul_self_sqrt hLp.le
  have hle : Real.sqrt (-Real.log q) ≤ Real.sqrt (-Real.log p) := by
    apply Real.sqrt_le_sqrt
    have := Real.log_le_log hp0 hp.2.le
    linarith
  have e : ((1 + ε) * (Real.sqrt (-Real.log p) / p)) * ((1 + ε) * (p / (-Real.log p)))
      = (1 + ε) ^ 2 * (1 / Real.sqrt (-Real.log p)) := by
    have hLne : -Real.log p ≠ 0 := hLp.ne'
    field_simp
    rw [Real.sq_sqrt hLp.le]
    have hlp : Real.log p ≠ 0 := by
      intro h
      rw [h] at hLp
      simp at hLp
    field_simp
  rw [e] at h
  refine h.trans ?_
  have h1 : 1 / Real.sqrt (-Real.log p) ≤ 1 / Real.sqrt (-Real.log q) :=
    one_div_le_one_div_of_le hsq hle
  have h2 : (1 + ε) ^ 2 ≤ 4 := by nlinarith
  rw [div_le_div_iff₀ hx (by positivity)]
  have h3 : (1 + ε) ^ 2 * (1 / Real.sqrt (-Real.log p)) ≤ 4 * (1 / Real.sqrt (-Real.log q)) :=
    mul_le_mul h2 h1 (by positivity) (by norm_num)
  have h4 : 0 < 1 / Real.sqrt (-Real.log q) := by positivity
  calc (1 + ε) ^ 2 * (1 / Real.sqrt (-Real.log p)) * (x * Real.sqrt (-Real.log q))
      ≤ 4 * (1 / Real.sqrt (-Real.log q)) * (x * Real.sqrt (-Real.log q)) :=
        mul_le_mul_of_nonneg_right h3 (by positivity)
    _ = 4 * x := by field_simp

private lemma prof_one_bounds {ε δ M x q η : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1)
    (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hδ : ∀ p ∈ Ioc (0:ℝ) δ,
      (1 - ε) * (p / (-Real.log p)) ≤ contV 1 p ∧ contV 1 p ≤ (1 + ε) * (p / (-Real.log p)) ∧
      (1 - ε) * (Real.sqrt (-Real.log p) / p) ≤ Real.sqrt ((1 - p) / (p * contV 1 p)) ∧
      Real.sqrt ((1 - p) / (p * contV 1 p)) ≤ (1 + ε) * (Real.sqrt (-Real.log p) / p))
    (hM : ∀ y : ℝ, 0 < y →
      ‖∫ p in δ..1, Real.sqrt ((1 - p) / (p * contV 1 p)) * profF 1 y p‖ ≤ M)
    (hx : 0 < x) (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (hxq : x ≤ q) (hqδ : q ≤ δ)
    (hcut : x * (-Real.log x) ≤ η * ((1 - ε) * q)) :
    (1 - ε) * (1 - η) * (2 / 3 * ((-Real.log q) * Real.sqrt (-Real.log q)
        - (-Real.log δ) * Real.sqrt (-Real.log δ))) - M ≤
      ∫ p in (0:ℝ)..1, Real.sqrt ((1 - p) / (p * contV 1 p)) * profF 1 x p ∧
    ∫ p in (0:ℝ)..1, Real.sqrt ((1 - p) / (p * contV 1 p)) * profF 1 x p ≤
      (1 + ε) * (2 / 3 * ((-Real.log x) * Real.sqrt (-Real.log x))) + M
        + 4 * q / (x * Real.sqrt (-Real.log q)) := by
  have hq0 : 0 < q := lt_of_lt_of_le hx hxq
  have hx1 : x < 1 := lt_of_le_of_lt (hxq.trans hqδ) hδ1
  have hI := prof_u_integrable (α := 1) zero_lt_one ⟨hx, hx1.le⟩
  have hI0q : IntervalIntegrable
      (fun p : ℝ => Real.sqrt ((1 - p) / (p * contV 1 p)) * profF 1 x p) volume 0 q :=
    hI.mono_set (by
      rw [Set.uIcc_of_le hq0.le, Set.uIcc_of_le zero_le_one]
      exact Icc_subset_Icc le_rfl (by linarith))
  have hIqδ : IntervalIntegrable
      (fun p : ℝ => Real.sqrt ((1 - p) / (p * contV 1 p)) * profF 1 x p) volume q δ :=
    hI.mono_set (by
      rw [Set.uIcc_of_le hqδ, Set.uIcc_of_le zero_le_one]
      exact Icc_subset_Icc hq0.le (by linarith))
  have hIδ1 : IntervalIntegrable
      (fun p : ℝ => Real.sqrt ((1 - p) / (p * contV 1 p)) * profF 1 x p) volume δ 1 :=
    hI.mono_set (by
      rw [Set.uIcc_of_le hδ1.le, Set.uIcc_of_le zero_le_one]
      exact Icc_subset_Icc hδ0.le le_rfl)
  have hsplit : ∫ p in (0:ℝ)..1, Real.sqrt ((1 - p) / (p * contV 1 p)) * profF 1 x p
      = (∫ p in (0:ℝ)..q, Real.sqrt ((1 - p) / (p * contV 1 p)) * profF 1 x p)
        + (∫ p in q..δ, Real.sqrt ((1 - p) / (p * contV 1 p)) * profF 1 x p)
        + ∫ p in δ..1, Real.sqrt ((1 - p) / (p * contV 1 p)) * profF 1 x p := by
    rw [intervalIntegral.integral_add_adjacent_intervals hI0q hIqδ,
      intervalIntegral.integral_add_adjacent_intervals (hI0q.trans hIqδ) hIδ1]
  have htail := abs_le.1 (by simpa [Real.norm_eq_abs] using hM x hx)
  have hAint := prof_one_Aint hq0 hqδ
  have hAv := prof_one_antideriv hq0 hqδ hδ1
  have hnn : ∀ p ∈ Ioo (0:ℝ) δ, 0 ≤ Real.sqrt ((1 - p) / (p * contV 1 p)) * profF 1 x p := by
    intro p hp
    exact (prof_one_pt hε0 hε1 hx ⟨hp.1, lt_trans hp.2 hδ1⟩ (hδ p ⟨hp.1, hp.2.le⟩)).2.2
  have hLδ : 0 < -Real.log δ := neg_pos.2 (Real.log_neg hδ0 hδ1)
  have hLq : 0 < -Real.log q := neg_pos.2 (Real.log_neg hq0 (lt_of_le_of_lt hqδ hδ1))
  have hLx : 0 < -Real.log x := neg_pos.2 (Real.log_neg hx hx1)
  -- the middle piece
  have hmid_up : ∫ p in q..δ, Real.sqrt ((1 - p) / (p * contV 1 p)) * profF 1 x p ≤
      (1 + ε) * (2 / 3 * ((-Real.log x) * Real.sqrt (-Real.log x))) := by
    have h1 : ∫ p in q..δ, Real.sqrt ((1 - p) / (p * contV 1 p)) * profF 1 x p
        ≤ ∫ p in q..δ, (1 + ε) * (Real.sqrt (-Real.log p) / p) := by
      apply intervalIntegral.integral_mono_on_of_le_Ioo hqδ hIqδ (hAint.const_mul _)
      intro p hp
      exact (prof_one_pt hε0 hε1 hx ⟨lt_trans hq0 hp.1, lt_trans hp.2 hδ1⟩
        (hδ p ⟨lt_trans hq0 hp.1, hp.2.le⟩)).1
    rw [intervalIntegral.integral_const_mul, hAv] at h1
    refine h1.trans ?_
    have hmono : (-Real.log q) * Real.sqrt (-Real.log q) ≤ (-Real.log x) * Real.sqrt (-Real.log x) := by
      have hle : -Real.log q ≤ -Real.log x := by
        have := Real.log_le_log hx hxq
        linarith
      exact mul_le_mul hle (Real.sqrt_le_sqrt hle) (Real.sqrt_nonneg _) hLx.le
    have hpos : 0 ≤ (-Real.log δ) * Real.sqrt (-Real.log δ) := by positivity
    nlinarith
  have hmid_lo : (1 - ε) * (1 - η) * (2 / 3 * ((-Real.log q) * Real.sqrt (-Real.log q)
        - (-Real.log δ) * Real.sqrt (-Real.log δ))) ≤
      ∫ p in q..δ, Real.sqrt ((1 - p) / (p * contV 1 p)) * profF 1 x p := by
    have h1 : ∫ p in q..δ, (1 - ε) * (1 - η) * (Real.sqrt (-Real.log p) / p)
        ≤ ∫ p in q..δ, Real.sqrt ((1 - p) / (p * contV 1 p)) * profF 1 x p := by
      apply intervalIntegral.integral_mono_on_of_le_Ioo hqδ (hAint.const_mul _) hIqδ
      intro p hp
      have hpI : p ∈ Ioo (0:ℝ) 1 := ⟨lt_trans hq0 hp.1, lt_trans hp.2 hδ1⟩
      have hb := hδ p ⟨hpI.1, hp.2.le⟩
      have hF := prof_one_Flo hε1 hx hη0 hpI hxq hp.1.le hcut hb.1
      have hg := hb.2.2.1
      have hF0 := (prof_F_bounds (α := 1) zero_lt_one hx hpI).1
      have hA0 : 0 ≤ Real.sqrt (-Real.log p) / p := by
        have := hpI.1
        positivity
      calc (1 - ε) * (1 - η) * (Real.sqrt (-Real.log p) / p)
          = ((1 - ε) * (Real.sqrt (-Real.log p) / p)) * (1 - η) := by ring
        _ ≤ Real.sqrt ((1 - p) / (p * contV 1 p)) * profF 1 x p :=
          mul_le_mul hg hF (by linarith) (Real.sqrt_nonneg _)
    rw [intervalIntegral.integral_const_mul, hAv] at h1
    linarith
  have hfirst_up : ∫ p in (0:ℝ)..q, Real.sqrt ((1 - p) / (p * contV 1 p)) * profF 1 x p
      ≤ 4 * q / (x * Real.sqrt (-Real.log q)) := by
    have h1 : ∫ p in (0:ℝ)..q, Real.sqrt ((1 - p) / (p * contV 1 p)) * profF 1 x p
        ≤ ∫ p in (0:ℝ)..q, 4 / (x * Real.sqrt (-Real.log q)) := by
      apply intervalIntegral.integral_mono_on_of_le_Ioo hq0.le hI0q intervalIntegrable_const
      intro p hp
      have hpI : p ∈ Ioo (0:ℝ) 1 := ⟨hp.1, lt_trans hp.2 (lt_of_le_of_lt hqδ hδ1)⟩
      exact prof_one_upper_pt hε0 hε1 hx hp (lt_of_le_of_lt hqδ hδ1)
        (prof_one_pt hε0 hε1 hx hpI (hδ p ⟨hp.1, hp.2.le.trans hqδ⟩)).2.1
    rw [intervalIntegral.integral_const] at h1
    simp only [sub_zero, smul_eq_mul] at h1
    refine h1.trans (le_of_eq ?_)
    ring
  have hfirst_lo : 0 ≤ ∫ p in (0:ℝ)..q, Real.sqrt ((1 - p) / (p * contV 1 p)) * profF 1 x p := by
    have h1 : ∫ p in (0:ℝ)..q, (0:ℝ)
        ≤ ∫ p in (0:ℝ)..q, Real.sqrt ((1 - p) / (p * contV 1 p)) * profF 1 x p := by
      apply intervalIntegral.integral_mono_on_of_le_Ioo hq0.le intervalIntegrable_const hI0q
      intro p hp
      exact hnn p ⟨hp.1, lt_of_lt_of_le hp.2 hqδ⟩
    simpa using h1
  rw [hsplit]
  constructor
  · linarith [htail.1]
  · linarith [htail.2]

private lemma prof_pow32 {L : ℝ} (hL : 0 < L) : L ^ (3 / 2 : ℝ) = L * Real.sqrt L := by
  rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add hL, Real.rpow_one,
    ← Real.sqrt_eq_rpow]

private lemma prof_one_L_tendsto :
    Tendsto (fun x : ℝ => -Real.log x) (𝓝[>] (0:ℝ)) atTop :=
  tendsto_neg_atBot_atTop.comp Real.tendsto_log_nhdsGT_zero

private lemma prof_one_q_tendsto :
    Tendsto (fun x : ℝ => x * ((-Real.log x) * Real.sqrt (-Real.log x)))
      (𝓝[>] (0:ℝ)) (𝓝 0) := by
  have h := (tendsto_log_mul_rpow_nhdsGT_zero (r := 2 / 3) (by norm_num)).neg
  rw [neg_zero] at h
  have h3 : Tendsto (fun x : ℝ => (-(Real.log x * x ^ (2 / 3 : ℝ))) ^ (3 / 2 : ℝ))
      (𝓝[>] (0:ℝ)) (𝓝 ((0:ℝ) ^ (3 / 2 : ℝ))) :=
    ((Real.continuousAt_rpow_const 0 (3 / 2) (Or.inr (by norm_num))).tendsto).comp h
  rw [Real.zero_rpow (by norm_num)] at h3
  refine h3.congr' ?_
  filter_upwards [Ioo_mem_nhdsGT (zero_lt_one : (0:ℝ) < 1)] with x hx
  have hL : 0 < -Real.log x := neg_pos.2 (Real.log_neg hx.1 hx.2)
  have e : -(Real.log x * x ^ (2 / 3 : ℝ)) = (-Real.log x) * x ^ (2 / 3 : ℝ) := by ring
  rw [e, Real.mul_rpow hL.le (Real.rpow_nonneg hx.1.le _), ← Real.rpow_mul hx.1.le,
    show (2 / 3 : ℝ) * (3 / 2) = 1 by norm_num, Real.rpow_one, prof_pow32 hL]
  ring

private lemma prof_one_q_pos {x : ℝ} (hx : x ∈ Ioo (0:ℝ) 1) :
    0 < x * ((-Real.log x) * Real.sqrt (-Real.log x)) := by
  have hL : 0 < -Real.log x := neg_pos.2 (Real.log_neg hx.1 hx.2)
  have := Real.sqrt_pos.2 hL
  have := hx.1
  positivity

private lemma prof_one_q_nhds :
    Tendsto (fun x : ℝ => x * ((-Real.log x) * Real.sqrt (-Real.log x)))
      (𝓝[>] (0:ℝ)) (𝓝[>] (0:ℝ)) := by
  apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ prof_one_q_tendsto
  filter_upwards [Ioo_mem_nhdsGT (zero_lt_one : (0:ℝ) < 1)] with x hx
  exact prof_one_q_pos hx

private lemma prof_one_Lq_tendsto :
    Tendsto (fun x : ℝ => -Real.log (x * ((-Real.log x) * Real.sqrt (-Real.log x))))
      (𝓝[>] (0:ℝ)) atTop :=
  tendsto_neg_atBot_atTop.comp (Real.tendsto_log_nhdsGT_zero.comp prof_one_q_nhds)

private lemma prof_one_r_tendsto :
    Tendsto (fun x : ℝ => (-Real.log (x * ((-Real.log x) * Real.sqrt (-Real.log x)))) /
      (-Real.log x)) (𝓝[>] (0:ℝ)) (𝓝 1) := by
  have h1 : Tendsto (fun x : ℝ => Real.log (-Real.log x) / (-Real.log x)) (𝓝[>] (0:ℝ)) (𝓝 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp prof_one_L_tendsto
  have h2 : Tendsto (fun x : ℝ => 1 - 3 / 2 * (Real.log (-Real.log x) / (-Real.log x)))
      (𝓝[>] (0:ℝ)) (𝓝 (1 - 3 / 2 * 0)) :=
    (h1.const_mul (3 / 2)).const_sub 1
  rw [mul_zero, sub_zero] at h2
  refine h2.congr' ?_
  filter_upwards [Ioo_mem_nhdsGT (zero_lt_one : (0:ℝ) < 1)] with x hx
  have hL : 0 < -Real.log x := neg_pos.2 (Real.log_neg hx.1 hx.2)
  have hs := Real.sqrt_pos.2 hL
  rw [Real.log_mul hx.1.ne' (mul_pos hL hs).ne', Real.log_mul hL.ne' hs.ne', Real.log_sqrt hL.le]
  have hlx : Real.log x ≠ 0 := by
    intro h
    rw [h] at hL
    simp at hL
  field_simp
  ring

private lemma prof_one_phi_ratio :
    Tendsto (fun x : ℝ =>
      ((-Real.log (x * ((-Real.log x) * Real.sqrt (-Real.log x)))) *
        Real.sqrt (-Real.log (x * ((-Real.log x) * Real.sqrt (-Real.log x))))) /
      ((-Real.log x) * Real.sqrt (-Real.log x))) (𝓝[>] (0:ℝ)) (𝓝 1) := by
  have h := prof_one_r_tendsto.mul prof_one_r_tendsto.sqrt
  rw [Real.sqrt_one, mul_one] at h
  refine h.congr' ?_
  filter_upwards [Ioo_mem_nhdsGT (zero_lt_one : (0:ℝ) < 1),
    prof_one_Lq_tendsto.eventually_gt_atTop 0] with x hx hLq
  have hL : 0 < -Real.log x := neg_pos.2 (Real.log_neg hx.1 hx.2)
  have hs := Real.sqrt_pos.2 hL
  rw [Real.sqrt_div hLq.le]
  field_simp

/-- `lem:app-pl-Psi` (snapshot `cr-2026-10-23`), part (ii), the first equivalence in
`eqn:app-pl-bulk-small` at `α = 1`. Statement verbatim:

\begin{lemma}[The profile $\Psi_\alpha$]\label{lem:app-pl-Psi}
$\Psi_\alpha$ is finite, positive and continuous on $(0,1]$, bounded below by a
positive constant, and satisfies the first equivalences of
\cref{eqn:app-pl-bulk-small}.
\end{lemma}

\begin{equation}\label{eqn:app-pl-bulk-small}
\begin{gathered}
\Psi_\alpha(x)\sim\begin{cases}\dfrac{c_0}{\sqrt{1-\alpha}}\log(x^{-\alpha}),&\alpha<1,\\[6pt]
\dfrac23c_0\big[\log(1/x)\big]^{3/2},&\alpha=1,\\[6pt]
d_\alpha\sqrt{K_\alpha}\,x^{-(\alpha-1)/2},&\alpha>1,\end{cases}
\\
\Gamma_\alpha(x)\sim\begin{cases}\dfrac{x^\alpha\big[\log(x^{-\alpha})\big]^2}{1-\alpha},&\alpha<1,\\[6pt]
\dfrac49x\big[\log(1/x)\big]^3,&\alpha=1,\\[6pt]
\dfrac{4K_\alpha^2}{\alpha-1}\,x,&\alpha>1.\end{cases}
\end{gathered}
\end{equation} -/
theorem lem_app_pl_Psi_ii_one {α : ℝ} (hα : α = 1) :
    IsEquivalent (𝓝[>] (0:ℝ)) (fun x : ℝ => profPsi α x)
      (fun x : ℝ => 2 / 3 * c0 * Real.log (1 / x) ^ (3 / 2 : ℝ)) := by
  subst hα
  have hc0 := prof_c0_pos
  have hlogeq : ∀ x : ℝ, Real.log (1 / x) = -Real.log x := by
    intro x
    rw [one_div, Real.log_inv]
  refine prof_equiv_of_squeeze ?_ ?_
  · filter_upwards [Ioo_mem_nhdsGT (zero_lt_one : (0:ℝ) < 1)] with x hx
    have hL : 0 < -Real.log x := neg_pos.2 (Real.log_neg hx.1 hx.2)
    show 0 ≤ 2 / 3 * c0 * Real.log (1 / x) ^ (3 / 2 : ℝ)
    rw [hlogeq]
    positivity
  · intro ε hε0 hε1
    obtain ⟨δ, hδ0, hδ1, hδ⟩ := prof_one_eps (half_pos hε0) (by linarith : ε / 2 < 1)
    obtain ⟨M, hM⟩ := prof_gt_tail (α := 1) zero_lt_one hδ0 hδ1
    have hLt := prof_one_L_tendsto
    have hsqrtL : Tendsto (fun x : ℝ => Real.sqrt (-Real.log x)) (𝓝[>] (0:ℝ)) atTop :=
      Real.tendsto_sqrt_atTop.comp hLt
    have hφ : Tendsto (fun x : ℝ => (-Real.log x) * Real.sqrt (-Real.log x))
        (𝓝[>] (0:ℝ)) atTop := hLt.atTop_mul_atTop₀ hsqrtL
    have hMφ : Tendsto (fun x : ℝ => M / ((-Real.log x) * Real.sqrt (-Real.log x)))
        (𝓝[>] (0:ℝ)) (𝓝 0) := tendsto_const_nhds.div_atTop hφ
    have hδφ : Tendsto (fun x : ℝ => ((-Real.log δ) * Real.sqrt (-Real.log δ)) /
        ((-Real.log x) * Real.sqrt (-Real.log x))) (𝓝[>] (0:ℝ)) (𝓝 0) :=
      tendsto_const_nhds.div_atTop hφ
    have hsqLq : Tendsto (fun x : ℝ =>
        Real.sqrt (-Real.log (x * ((-Real.log x) * Real.sqrt (-Real.log x)))))
        (𝓝[>] (0:ℝ)) atTop := Real.tendsto_sqrt_atTop.comp prof_one_Lq_tendsto
    have hE : Tendsto (fun x : ℝ =>
        4 / Real.sqrt (-Real.log (x * ((-Real.log x) * Real.sqrt (-Real.log x)))))
        (𝓝[>] (0:ℝ)) (𝓝 0) := tendsto_const_nhds.div_atTop hsqLq
    have hη : Tendsto (fun x : ℝ => 1 / ((1 - ε / 2) * Real.sqrt (-Real.log x)))
        (𝓝[>] (0:ℝ)) (𝓝 0) :=
      tendsto_const_nhds.div_atTop (hsqrtL.const_mul_atTop (by linarith : 0 < 1 - ε / 2))
    have hρ := prof_one_phi_ratio
    -- the limits of the upper and lower quantities
    have hU : Tendsto (fun x : ℝ => (1 + ε / 2) * (2 / 3) +
        M / ((-Real.log x) * Real.sqrt (-Real.log x)) +
        4 / Real.sqrt (-Real.log (x * ((-Real.log x) * Real.sqrt (-Real.log x)))))
        (𝓝[>] (0:ℝ)) (𝓝 ((1 + ε / 2) * (2 / 3) + 0 + 0)) :=
      (tendsto_const_nhds.add hMφ).add hE
    have hΛ : Tendsto (fun x : ℝ => (1 - ε / 2) * (1 - 1 / ((1 - ε / 2) * Real.sqrt (-Real.log x))) *
        (2 / 3 * ((((-Real.log (x * ((-Real.log x) * Real.sqrt (-Real.log x)))) *
          Real.sqrt (-Real.log (x * ((-Real.log x) * Real.sqrt (-Real.log x))))) /
          ((-Real.log x) * Real.sqrt (-Real.log x)))
          - ((-Real.log δ) * Real.sqrt (-Real.log δ)) /
            ((-Real.log x) * Real.sqrt (-Real.log x)))) -
        M / ((-Real.log x) * Real.sqrt (-Real.log x)))
        (𝓝[>] (0:ℝ)) (𝓝 ((1 - ε / 2) * (1 - 0) * (2 / 3 * (1 - 0)) - 0)) :=
      (((tendsto_const_nhds.mul (tendsto_const_nhds.sub hη)).mul
        (tendsto_const_nhds.mul (hρ.sub hδφ)))).sub hMφ
    have hU' := hU.eventually (gt_mem_nhds (by linarith :
      (1 + ε / 2) * (2 / 3) + 0 + 0 < 2 / 3 * (1 + ε)))
    have hΛ' := hΛ.eventually (lt_mem_nhds (by linarith :
      2 / 3 * (1 - ε) < (1 - ε / 2) * (1 - 0) * (2 / 3 * (1 - 0)) - 0))
    have hη1 := hη.eventually (gt_mem_nhds (by norm_num : (0:ℝ) < 1))
    have hq1 := prof_one_q_tendsto.eventually (gt_mem_nhds hδ0)
    have hφ1 := hφ.eventually_ge_atTop 1
    filter_upwards [Ioo_mem_nhdsGT (zero_lt_one : (0:ℝ) < 1), hU', hΛ', hη1, hq1, hφ1]
      with x hx hUx hΛx hηx hqx hφx
    have hx0 : 0 < x := hx.1
    have hL : 0 < -Real.log x := neg_pos.2 (Real.log_neg hx.1 hx.2)
    have hsL := Real.sqrt_pos.2 hL
    set φx : ℝ := (-Real.log x) * Real.sqrt (-Real.log x) with hφx
    have hφpos : 0 < φx := by positivity
    set q : ℝ := x * φx with hq
    set η : ℝ := 1 / ((1 - ε / 2) * Real.sqrt (-Real.log x)) with hηdef
    have hη0 : 0 ≤ η := div_nonneg zero_le_one (mul_nonneg (by linarith) hsL.le)
    have hxq : x ≤ q := by
      rw [hq]
      nlinarith
    have hcut : x * (-Real.log x) ≤ η * ((1 - ε / 2) * q) := by
      rw [hηdef, hq, hφx]
      have : (1 - ε / 2) ≠ 0 := (by linarith : 0 < 1 - ε / 2).ne'
      field_simp
      have h2 : (2 - ε) ≠ 0 := (by linarith : 0 < 2 - ε).ne'
      rw [mul_div_assoc, div_self h2, mul_one]
    obtain ⟨hlo, hup⟩ := prof_one_bounds (half_pos hε0) (by linarith : ε / 2 < 1) hδ0 hδ1 hδ hM
      hx0 hη0 hηx.le hxq hqx.le hcut
    have hLq : 0 < -Real.log q := by
      have hq0 : 0 < q := by rw [hq]; positivity
      have hqx1 : q < 1 := lt_trans hqx hδ1
      exact neg_pos.2 (Real.log_neg hq0 hqx1)
    have hsLq := Real.sqrt_pos.2 hLq
    have e1 : (1 + ε / 2) * (2 / 3 * φx) + M + 4 * q / (x * Real.sqrt (-Real.log q))
        = φx * ((1 + ε / 2) * (2 / 3) + M / φx + 4 / Real.sqrt (-Real.log q)) := by
      rw [hq]
      field_simp
    have e2 : (1 - ε / 2) * (1 - η) * (2 / 3 * ((-Real.log q) * Real.sqrt (-Real.log q)
        - (-Real.log δ) * Real.sqrt (-Real.log δ))) - M
        = φx * ((1 - ε / 2) * (1 - η) *
          (2 / 3 * (((-Real.log q) * Real.sqrt (-Real.log q)) / φx
            - ((-Real.log δ) * Real.sqrt (-Real.log δ)) / φx)) - M / φx) := by
      field_simp
    have hIup : (∫ p in (0:ℝ)..1, Real.sqrt ((1 - p) / (p * contV 1 p)) * profF 1 x p)
        ≤ φx * (2 / 3 * (1 + ε)) := by
      calc _ ≤ _ := hup
        _ = _ := e1
        _ ≤ _ := mul_le_mul_of_nonneg_left hUx.le hφpos.le
    have hIlo : φx * (2 / 3 * (1 - ε)) ≤
        ∫ p in (0:ℝ)..1, Real.sqrt ((1 - p) / (p * contV 1 p)) * profF 1 x p := by
      calc φx * (2 / 3 * (1 - ε)) ≤ φx * ((1 - ε / 2) * (1 - η) *
          (2 / 3 * (((-Real.log q) * Real.sqrt (-Real.log q)) / φx
            - ((-Real.log δ) * Real.sqrt (-Real.log δ)) / φx)) - M / φx) :=
            mul_le_mul_of_nonneg_left hΛx.le hφpos.le
        _ = _ := e2.symm
        _ ≤ _ := hlo
    show (1 - ε) * (2 / 3 * c0 * Real.log (1 / x) ^ (3 / 2 : ℝ)) ≤ profPsi 1 x ∧
      profPsi 1 x ≤ (1 + ε) * (2 / 3 * c0 * Real.log (1 / x) ^ (3 / 2 : ℝ))
    rw [hlogeq, prof_pow32 hL]
    unfold profPsi
    constructor
    · have := mul_le_mul_of_nonneg_left hIlo hc0.le
      calc (1 - ε) * (2 / 3 * c0 * φx) = c0 * (φx * (2 / 3 * (1 - ε))) := by ring
        _ ≤ _ := this
    · have := mul_le_mul_of_nonneg_left hIup hc0.le
      calc c0 * _ ≤ c0 * (φx * (2 / 3 * (1 + ε))) := this
        _ = _ := by ring

/-- `lem:app-pl-Psi` (snapshot `cr-2026-10-23`), part (ii), the first equivalence in
`eqn:app-pl-bulk-small` for `α > 1`. Statement verbatim:

\begin{lemma}[The profile $\Psi_\alpha$]\label{lem:app-pl-Psi}
$\Psi_\alpha$ is finite, positive and continuous on $(0,1]$, bounded below by a
positive constant, and satisfies the first equivalences of
\cref{eqn:app-pl-bulk-small}.
\end{lemma}

\begin{equation}\label{eqn:app-pl-bulk-small}
\begin{gathered}
\Psi_\alpha(x)\sim\begin{cases}\dfrac{c_0}{\sqrt{1-\alpha}}\log(x^{-\alpha}),&\alpha<1,\\[6pt]
\dfrac23c_0\big[\log(1/x)\big]^{3/2},&\alpha=1,\\[6pt]
d_\alpha\sqrt{K_\alpha}\,x^{-(\alpha-1)/2},&\alpha>1,\end{cases}
\\
\Gamma_\alpha(x)\sim\begin{cases}\dfrac{x^\alpha\big[\log(x^{-\alpha})\big]^2}{1-\alpha},&\alpha<1,\\[6pt]
\dfrac49x\big[\log(1/x)\big]^3,&\alpha=1,\\[6pt]
\dfrac{4K_\alpha^2}{\alpha-1}\,x,&\alpha>1.\end{cases}
\end{gathered}
\end{equation} -/
theorem lem_app_pl_Psi_ii_gt {α : ℝ} (hα1 : 1 < α) :
    IsEquivalent (𝓝[>] (0:ℝ)) (fun x : ℝ => profPsi α x)
      (fun x : ℝ => dAl α * Real.sqrt (Kc α) * x ^ (-(α - 1) / 2)) := by
  have hα0 : 0 < α := by linarith
  have hK : 0 < Kc α := prof_gt_Kpos hα1
  obtain ⟨p0, hp0, hp01, hr⟩ := prof_gt_p0 hα1
  have hmain := prof_gt_main hα1 hp0 hp01 hr
  obtain ⟨M, hM⟩ := prof_gt_tail hα0 hp0 hp01
  have hexp : 0 < (α - 1) / 2 := by linarith
  have hT : Tendsto (fun x : ℝ => x ^ ((α - 1) / 2) *
      ∫ p in p0..1, Real.sqrt ((1 - p) / (p * contV α p)) * profF α x p)
      (𝓝[>] (0:ℝ)) (𝓝 0) := by
    have ha : Tendsto (fun x : ℝ => x ^ ((α - 1) / 2) * M) (𝓝[>] (0:ℝ)) (𝓝 0) := by
      have hc : Continuous fun x : ℝ => x ^ ((α - 1) / 2) * M :=
        (Real.continuous_rpow_const hexp.le).mul continuous_const
      have h := hc.tendsto 0
      rw [Real.zero_rpow hexp.ne', zero_mul] at h
      exact h.mono_left nhdsWithin_le_nhds
    refine squeeze_zero_norm' ?_ ha
    filter_upwards [self_mem_nhdsWithin] with x hx
    have hx0 : (0:ℝ) < x := hx
    rw [norm_mul, Real.norm_of_nonneg (Real.rpow_nonneg hx0.le _)]
    exact mul_le_mul_of_nonneg_left (hM x hx0) (Real.rpow_nonneg hx0.le _)
  have hsum := hmain.add hT
  rw [add_zero] at hsum
  have h1 : Tendsto (fun x : ℝ => x ^ ((α - 1) / 2) *
      ∫ p in (0:ℝ)..1, Real.sqrt ((1 - p) / (p * contV α p)) * profF α x p)
      (𝓝[>] (0:ℝ)) (𝓝 (Real.sqrt (Kc α) * (Real.pi / (α * Real.cos (Real.pi / (2 * α)))))) := by
    refine hsum.congr' ?_
    filter_upwards [Ioc_mem_nhdsGT (zero_lt_one : (0:ℝ) < 1)] with x hx
    have hI := prof_u_integrable hα0 hx
    rw [← mul_add]
    congr 1
    rw [intervalIntegral.integral_add_adjacent_intervals]
    · exact hI.mono_set (by
        rw [Set.uIcc_of_le hp0.le, Set.uIcc_of_le zero_le_one]
        exact Icc_subset_Icc le_rfl hp01.le)
    · exact hI.mono_set (by
        rw [Set.uIcc_of_le hp01.le, Set.uIcc_of_le zero_le_one]
        exact Icc_subset_Icc hp0.le le_rfl)
  have hcos : 0 < Real.cos (Real.pi / (2 * α)) := by
    apply Real.cos_pos_of_mem_Ioo
    constructor
    · have : 0 < Real.pi / (2 * α) := by positivity
      linarith [Real.pi_pos]
    · exact div_lt_div_of_pos_left Real.pi_pos (by norm_num) (by linarith)
  have hd : 0 < dAl α := by
    unfold dAl
    exact div_pos (mul_pos (Real.sqrt_pos.2 (by positivity)) Real.pi_pos) (mul_pos hα0 hcos)
  have hsK : 0 < Real.sqrt (Kc α) := Real.sqrt_pos.2 hK
  refine isEquivalent_of_tendsto_one ?_
  have h2 := (h1.const_mul c0).div_const (dAl α * Real.sqrt (Kc α))
  have hlim : c0 * (Real.sqrt (Kc α) * (Real.pi / (α * Real.cos (Real.pi / (2 * α)))))
      / (dAl α * Real.sqrt (Kc α)) = 1 := by
    unfold dAl
    have hc0 := prof_c0_pos.ne'
    generalize Real.cos (Real.pi / (2 * α)) = Cc at hcos ⊢
    have hCc := hcos.ne'
    field_simp
  rw [hlim] at h2
  refine h2.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with x hx
  have hx0 : (0:ℝ) < x := hx
  simp only [Pi.div_apply, profPsi]
  have hxx : x ^ (-(α - 1) / 2) = (x ^ ((α - 1) / 2))⁻¹ := by
    rw [← Real.rpow_neg hx0.le]
    congr 1
    ring
  rw [hxx]
  have : x ^ ((α - 1) / 2) ≠ 0 := (Real.rpow_pos_of_pos hx0 _).ne'
  field_simp














-- PGM-BEGIN (helpers for lem_app_pl_matching)
private lemma pgm_ci {α : ℝ} (hα : 0 < α) {G : ℝ → ℝ} (hG : ContinuousOn G (Ici 0)) :
    IntervalIntegrable (fun t : ℝ => G (t ^ α)) volume 0 1 := by
  apply ContinuousOn.intervalIntegrable
  refine hG.comp ((Real.continuous_rpow_const hα.le).continuousOn) ?_
  intro t ht
  rw [Set.uIcc_of_le zero_le_one] at ht
  exact Real.rpow_nonneg ht.1 α

private lemma pgm_K1 {α V W : ℝ} (hα : 0 < α) (hV : 0 < V) (hVW : V ≤ W) :
    V * contS α W ≤ W * contS α V := by
  have hW : 0 < W := lt_of_lt_of_le hV hVW
  unfold contS
  rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_mono_on zero_le_one
  · exact ((prof_cont_on hα hW).const_smul V).intervalIntegrable
  · exact ((prof_cont_on hα hV).const_smul W).intervalIntegrable
  intro t ht
  have h0 : 0 ≤ t ^ α := Real.rpow_nonneg ht.1 α
  rw [← mul_div_assoc, ← mul_div_assoc]
  have : V * W / (W + t ^ α) ≤ W * V / (V + t ^ α) := by
    rw [mul_comm W V]
    exact div_le_div_of_nonneg_left (by positivity) (by linarith) (by linarith)
  exact this

private lemma pgm_K2 {α V W : ℝ} (hα : 0 < α) (hV : 0 < V) (hVW : V ≤ W) :
    (W - V) * Tcont α W ≤ W * (contS α W - contS α V) := by
  have hW : 0 < W := lt_of_lt_of_le hV hVW
  unfold Tcont
  have hiT : IntervalIntegrable (fun t : ℝ => W * t ^ α / (W + t ^ α) ^ 2) volume 0 1 := by
    have := pgm_ci hα (G := fun a => W * a / (W + a) ^ 2) (by
      apply ContinuousOn.div (by fun_prop) (by fun_prop)
      intro a ha
      have : (0:ℝ) ≤ a := ha
      positivity)
    exact this
  have hiS : IntervalIntegrable (fun t : ℝ => W / (W + t ^ α) - V / (V + t ^ α)) volume 0 1 :=
    ((prof_cont_on hα hW).sub (prof_cont_on hα hV)).intervalIntegrable
  have hiS2 : IntervalIntegrable (fun t : ℝ => W * (W / (W + t ^ α) - V / (V + t ^ α))) volume 0 1 :=
    hiS.const_mul W
  have e1 : W * (contS α W - contS α V) = ∫ t in (0:ℝ)..1, W * (W / (W + t ^ α) - V / (V + t ^ α)) := by
    unfold contS
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_sub
      (prof_cont_on hα hW).intervalIntegrable (prof_cont_on hα hV).intervalIntegrable]
  rw [e1, ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_mono_on zero_le_one (hiT.const_mul (W - V)) hiS2
  intro t ht
  have h0 : 0 ≤ t ^ α := Real.rpow_nonneg ht.1 α
  have h1 : 0 < V + t ^ α := by linarith
  have h2 : 0 < W + t ^ α := by linarith
  have e : W * (W / (W + t ^ α) - V / (V + t ^ α)) = W * (W - V) * t ^ α / ((W + t ^ α) * (V + t ^ α)) := by
    field_simp
    ring
  have e2 : (W - V) * (W * t ^ α / (W + t ^ α) ^ 2) = W * (W - V) * t ^ α / (W + t ^ α) ^ 2 := by ring
  rw [e, e2]
  apply div_le_div_of_nonneg_left (by have := sub_nonneg.2 hVW; positivity) (by positivity)
  nlinarith

private lemma pgm_h_eq {V W p q s : ℝ} (hV : 0 < V) (hVW : V < W) (hp : 0 < p) (hpq : p < q)
    (hq : q < 1) (hs : 0 < s) :
    (W / (W + s) - V / (V + s)) / (q - p) *
        Real.sqrt ((V / (p * (1 - p))) / (W / (q * (1 - q)))) =
      s * (Real.sqrt ((1 - p) / (p * V)) * (V / (V + s))) *
        (Real.sqrt ((1 - q) / (q * W)) * (W / (W + s))) *
        (q * (W - V) / ((1 - p) * W * (q - p))) := by
  have hW : 0 < W := by linarith
  have hq0 : 0 < q := by linarith
  have h1p : 0 < 1 - p := by linarith
  have h1q : 0 < 1 - q := by linarith
  have hqp : 0 < q - p := by linarith
  have hX : (V / (p * (1 - p))) / (W / (q * (1 - q))) =
      ((1 - p) / (p * V) * ((1 - q) / (q * W))) * (V * q / (1 - p)) ^ 2 := by
    field_simp
  have hYn : 0 ≤ (1 - p) / (p * V) * ((1 - q) / (q * W)) := by positivity
  rw [hX, Real.sqrt_mul hYn, Real.sqrt_sq (by positivity), Real.sqrt_mul (by positivity)]
  have hVs : 0 < V + s := by linarith
  have hWs : 0 < W + s := by linarith
  field_simp
  ring

private lemma pgm_D_ge {V W p q : ℝ} (hV : 0 < V) (hVW : V < W) (hp : 0 < p) (hpq : p < q)
    (hK1 : V * q ≤ W * p) :
    (1 - p) * W * (q - p) ≤ q * (W - V) := by
  have hW : 0 < W := by linarith
  nlinarith [mul_pos (mul_pos hp hW) (sub_pos.2 hpq)]

private lemma pgm_D_diag {V W p q : ℝ} (hV : 0 < V) (hVW : V < W) (hp : 0 < p) (hpq : p < q)
    (hq : q < 1) :
    q * (W - V) / ((1 - p) * W * (q - p)) ≤ q / ((1 - p) * (q - p)) := by
  have hW : 0 < W := by linarith
  have h1p : 0 < 1 - p := by linarith
  have hqp : 0 < q - p := by linarith
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have : 0 < q * ((1 - p) * (q - p)) := by have : 0 < q := by linarith
                                           positivity
  nlinarith [mul_pos this hV]

private lemma pgm_D_el {c V W p q T : ℝ} (hc : 0 < c) (hV : 0 < V) (hVW : V < W) (hp : 0 < p)
    (hpq : p < q) (hq : q < 1) (hT : c * (q * (1 - q)) ≤ T) (hK2 : (W - V) * T ≤ W * (q - p)) :
    q * (W - V) / ((1 - p) * W * (q - p)) ≤ 1 / (c * ((1 - p) * (1 - q))) := by
  have hW : 0 < W := by linarith
  have h1p : 0 < 1 - p := by linarith
  have h1q : 0 < 1 - q := by linarith
  have hq0 : 0 < q := by linarith
  have hqp : 0 < q - p := by linarith
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have h1 : (W - V) * (c * (q * (1 - q))) ≤ W * (q - p) :=
    le_trans (mul_le_mul_of_nonneg_left hT (by linarith)) hK2
  nlinarith [mul_le_mul_of_nonneg_left h1 h1p.le]

private lemma pgm_inner_gt {G : ℝ → ℝ} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    ∫ q in Ioc (0:ℝ) 1, (if p < q then G q else 0) = ∫ q in p..1, G q := by
  have h1 : (fun q : ℝ => if p < q then G q else 0) = Set.indicator (Ioi p) G := by
    ext q
    simp [Set.indicator, Set.mem_Ioi]
  rw [h1, integral_indicator measurableSet_Ioi, Measure.restrict_restrict measurableSet_Ioi,
    intervalIntegral.integral_of_le hp1]
  congr 2
  ext q
  simp only [Set.mem_inter_iff, Set.mem_Ioi, Set.mem_Ioc]
  constructor
  · rintro ⟨h1, h2, h3⟩; exact ⟨h1, h3⟩
  · rintro ⟨h1, h2⟩; exact ⟨h1, by linarith, h2⟩

private lemma pgm_inner_lt {G : ℝ → ℝ} {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    ∫ p in Ioc (0:ℝ) 1, (if p < q then G p else 0) = ∫ p in (0:ℝ)..q, G p := by
  have h1 : (fun p : ℝ => if p < q then G p else 0) = Set.indicator (Iio q) G := by
    ext p
    simp [Set.indicator, Set.mem_Iio]
  rw [h1, integral_indicator measurableSet_Iio, Measure.restrict_restrict measurableSet_Iio,
    intervalIntegral.integral_of_le hq0, integral_Ioc_eq_integral_Ioo]
  congr 2
  ext p
  simp only [Set.mem_inter_iff, Set.mem_Iio, Set.mem_Ioc, Set.mem_Ioo]
  constructor
  · rintro ⟨h1, h2, h3⟩; exact ⟨h2, h1⟩
  · rintro ⟨h1, h2⟩; exact ⟨h2, h1, by linarith⟩

private lemma pgm_swap_lt {G : ℝ → ℝ → ℝ}
    (hG : Integrable (fun z : ℝ × ℝ => if z.1 < z.2 then G z.1 z.2 else 0)
      ((volume.restrict (Ioc (0:ℝ) 1)).prod (volume.restrict (Ioc (0:ℝ) 1)))) :
    ∫ p in (0:ℝ)..1, ∫ q in p..1, G p q = ∫ q in (0:ℝ)..1, ∫ p in (0:ℝ)..q, G p q := by
  have hs := integral_integral_swap (f := fun p q : ℝ => if p < q then G p q else 0) hG
  rw [intervalIntegral.integral_of_le zero_le_one, intervalIntegral.integral_of_le zero_le_one]
  have e1 : ∫ p in Ioc (0:ℝ) 1, ∫ q in p..1, G p q =
      ∫ p in Ioc (0:ℝ) 1, ∫ q in Ioc (0:ℝ) 1, (if p < q then G p q else 0) := by
    refine setIntegral_congr_fun measurableSet_Ioc (fun p hp => ?_)
    exact (pgm_inner_gt (G := G p) hp.1.le hp.2).symm
  have e2 : ∫ q in Ioc (0:ℝ) 1, ∫ p in (0:ℝ)..q, G p q =
      ∫ q in Ioc (0:ℝ) 1, ∫ p in Ioc (0:ℝ) 1, (if p < q then G p q else 0) := by
    refine setIntegral_congr_fun measurableSet_Ioc (fun q hq => ?_)
    exact (pgm_inner_lt (G := fun p => G p q) hq.1.le hq.2).symm
  rw [e1, e2]
  exact hs

private lemma pgm_inner_sum {G : ℝ → ℝ} {τ : ℝ} (h0 : 0 ≤ τ) (h1 : τ ≤ 1) :
    ∫ p in Ioc (0:ℝ) 1, (if τ + p < 1 then G p else 0) = ∫ p in (0:ℝ)..(1 - τ), G p := by
  have e : (fun p : ℝ => if τ + p < 1 then G p else 0) = Set.indicator (Iio (1 - τ)) G := by
    ext p
    simp only [Set.indicator, Set.mem_Iio]
    have : τ + p < 1 ↔ p < 1 - τ := by constructor <;> intro h <;> linarith
    simp only [this]
  rw [e, integral_indicator measurableSet_Iio, Measure.restrict_restrict measurableSet_Iio,
    intervalIntegral.integral_of_le (by linarith), integral_Ioc_eq_integral_Ioo]
  congr 2
  ext p
  simp only [Set.mem_inter_iff, Set.mem_Iio, Set.mem_Ioc, Set.mem_Ioo]
  constructor
  · rintro ⟨a, b, c⟩; exact ⟨b, a⟩
  · rintro ⟨a, b⟩; exact ⟨b, a, by linarith⟩

private lemma pgm_swap_sum {G : ℝ → ℝ → ℝ}
    (hG : Integrable (fun z : ℝ × ℝ => if z.1 + z.2 < 1 then G z.1 z.2 else 0)
      ((volume.restrict (Ioc (0:ℝ) 1)).prod (volume.restrict (Ioc (0:ℝ) 1)))) :
    ∫ τ in (0:ℝ)..1, ∫ p in (0:ℝ)..(1 - τ), G τ p =
      ∫ p in (0:ℝ)..1, ∫ τ in (0:ℝ)..(1 - p), G τ p := by
  have hs := integral_integral_swap (f := fun τ p : ℝ => if τ + p < 1 then G τ p else 0) hG
  rw [intervalIntegral.integral_of_le zero_le_one, intervalIntegral.integral_of_le zero_le_one]
  have e1 : ∫ τ in Ioc (0:ℝ) 1, ∫ p in (0:ℝ)..(1 - τ), G τ p =
      ∫ τ in Ioc (0:ℝ) 1, ∫ p in Ioc (0:ℝ) 1, (if τ + p < 1 then G τ p else 0) := by
    refine setIntegral_congr_fun measurableSet_Ioc (fun τ hτ => ?_)
    exact (pgm_inner_sum (G := G τ) hτ.1.le hτ.2).symm
  have e2 : ∫ p in Ioc (0:ℝ) 1, ∫ τ in (0:ℝ)..(1 - p), G τ p =
      ∫ p in Ioc (0:ℝ) 1, ∫ τ in Ioc (0:ℝ) 1, (if τ + p < 1 then G τ p else 0) := by
    refine setIntegral_congr_fun measurableSet_Ioc (fun p hp => ?_)
    have := pgm_inner_sum (G := fun τ => G τ p) (τ := p) hp.1.le hp.2
    simp only [add_comm _ p] at this ⊢
    rw [← this]
  rw [e1, e2]
  exact hs

private lemma pgm_half {w : ℝ → ℝ} (hwi : IntervalIntegrable w volume 0 1) :
    IntervalIntegrable (fun p => w p * ∫ q in p..1, w q) volume 0 1 ∧
      ∫ p in (0:ℝ)..1, w p * ∫ q in p..1, w q = (∫ p in (0:ℝ)..1, w p) ^ 2 / 2 := by
  have hwI : Integrable w (volume.restrict (Ioc (0:ℝ) 1)) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).1 hwi
  set μ : Measure ℝ := volume.restrict (Ioc (0:ℝ) 1) with hμ
  have hP : Integrable (fun z : ℝ × ℝ => w z.1 * w z.2) (μ.prod μ) := hwI.mul_prod hwI
  have hG : Integrable (fun z : ℝ × ℝ => if z.1 < z.2 then w z.1 * w z.2 else 0) (μ.prod μ) := by
    have := hP.indicator (measurableSet_lt measurable_fst measurable_snd)
    convert this using 1
    ext z
    simp [Set.indicator]
  have hswap := pgm_swap_lt (G := fun p q => w p * w q) hG
  have hL := hG.integral_prod_left
  have hR := hG.integral_prod_right
  have e1 : ∀ p ∈ Ioc (0:ℝ) 1, ∫ q in Ioc (0:ℝ) 1, (if p < q then w p * w q else 0) =
      w p * ∫ q in p..1, w q := by
    intro p hp
    rw [pgm_inner_gt (G := fun q => w p * w q) hp.1.le hp.2, intervalIntegral.integral_const_mul]
  have e2 : ∀ q ∈ Ioc (0:ℝ) 1, ∫ p in Ioc (0:ℝ) 1, (if p < q then w p * w q else 0) =
      (∫ p in (0:ℝ)..q, w p) * w q := by
    intro q hq
    rw [pgm_inner_lt (G := fun p => w p * w q) hq.1.le hq.2, intervalIntegral.integral_mul_const]
  have hL' : IntegrableOn (fun p => w p * ∫ q in p..1, w q) (Ioc (0:ℝ) 1) :=
    hL.congr (by
      refine (ae_restrict_iff' measurableSet_Ioc).2 (ae_of_all _ fun p hp => ?_)
      exact e1 p hp)
  have hR' : IntegrableOn (fun q => (∫ p in (0:ℝ)..q, w p) * w q) (Ioc (0:ℝ) 1) :=
    hR.congr (by
      refine (ae_restrict_iff' measurableSet_Ioc).2 (ae_of_all _ fun q hq => ?_)
      exact e2 q hq)
  have hL'' : IntervalIntegrable (fun p => w p * ∫ q in p..1, w q) volume 0 1 :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).2 hL'
  have hR'' : IntervalIntegrable (fun q => (∫ p in (0:ℝ)..q, w p) * w q) volume 0 1 :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).2 hR'
  have hsum : ∫ p in (0:ℝ)..1, (w p * (∫ q in p..1, w q) + (∫ q in (0:ℝ)..p, w q) * w p) =
      (∫ p in (0:ℝ)..1, w p) * (∫ p in (0:ℝ)..1, w p) := by
    have : ∀ p ∈ uIcc (0:ℝ) 1, (w p * (∫ q in p..1, w q) + (∫ q in (0:ℝ)..p, w q) * w p) =
        w p * ∫ q in (0:ℝ)..1, w q := by
      intro p hp
      rw [Set.uIcc_of_le zero_le_one] at hp
      have hs : (∫ q in (0:ℝ)..p, w q) + (∫ q in p..1, w q) = ∫ q in (0:ℝ)..1, w q :=
        intervalIntegral.integral_add_adjacent_intervals
          (hwi.mono_set (by rw [Set.uIcc_of_le hp.1, Set.uIcc_of_le zero_le_one]; exact Set.Icc_subset_Icc le_rfl hp.2))
          (hwi.mono_set (by rw [Set.uIcc_of_le hp.2, Set.uIcc_of_le zero_le_one]; exact Set.Icc_subset_Icc hp.1 le_rfl))
      rw [← hs]; ring
    rw [intervalIntegral.integral_congr this, intervalIntegral.integral_mul_const]
  rw [intervalIntegral.integral_add hL'' hR''] at hsum
  have : ∫ q in (0:ℝ)..1, (∫ p in (0:ℝ)..q, w p) * w q = ∫ p in (0:ℝ)..1, w p * ∫ q in p..1, w q := by
    rw [← intervalIntegral.integral_congr (a := 0) (b := 1) (f := fun p => ∫ q in p..1, w p * w q)
      (g := fun p => w p * ∫ q in p..1, w q) (fun p _ => by simp only; rw [intervalIntegral.integral_const_mul]), hswap]
    refine intervalIntegral.integral_congr (fun q _ => ?_)
    rw [intervalIntegral.integral_mul_const]
  rw [this] at hsum
  exact ⟨hL'', by nlinarith [hsum]⟩

private lemma pgm_sub {f : ℝ → ℝ} {a b c d : ℝ} (hf : IntervalIntegrable f volume a b)
    (hac : a ≤ c) (hcd : c ≤ d) (hdb : d ≤ b) : IntervalIntegrable f volume c d := by
  refine hf.mono_set ?_
  rw [Set.uIcc_of_le hcd, Set.uIcc_of_le (hac.trans (hcd.trans hdb))]
  exact Set.Icc_subset_Icc hac hdb

private lemma pgm_nn_ae {w : ℝ → ℝ} (hw0 : ∀ p, 0 ≤ p → p ≤ 1 → 0 ≤ w p) {c d : ℝ}
    (hc : 0 ≤ c) (hd : d ≤ 1) : 0 ≤ᵐ[volume.restrict (Ioc c d)] w := by
  refine (ae_restrict_iff' measurableSet_Ioc).2 (ae_of_all _ fun x hx => ?_)
  exact hw0 x (by linarith [hx.1]) (by linarith [hx.2])

private lemma pgm_skel {w g e : ℝ → ℝ} {H : ℝ → ℝ → ℝ} {η R L C0 K : ℝ}
    (hη0 : 0 < η) (hη1 : η < 1) (hR : 1 ≤ R) (hL : 1 ≤ L) (hC0 : 0 ≤ C0) (hK : 0 ≤ K)
    (hw0 : ∀ p, 0 ≤ p → p ≤ 1 → 0 ≤ w p)
    (hwi : IntervalIntegrable w volume 0 1)
    (hwg : ∀ p q, 0 < p → p ≤ q → q < 1 → w q ≤ g p)
    (hHi : ∀ p, 0 < p → p < 1 → IntervalIntegrable (H p) volume p 1)
    (hHo : IntervalIntegrable (fun p => ∫ q in p..1, H p q) volume 0 1)
    (R1 : ∀ p q, 0 < p → p < q → q < 1 → w p * w q ≤ H p q)
    (R2 : ∀ p q, 0 < p → p < q → q < η → H p q ≤ C0 * (w p * w q))
    (R3 : ∀ p q, 0 < p → R * p ≤ q → p < q → q < η → H p q ≤ L * (w p * w q))
    (R4 : ∀ p q, 0 < p → p < η / 2 → η ≤ q → q < 1 → H p q ≤ 4 * (w p * w q))
    (R5 : ∀ p q, η / 2 ≤ p → p < q → q < 1 → H p q ≤ K)
    (he : ∀ p, 0 < p → p < η / 2 → p * g p * w p ≤ e p)
    (hei : IntervalIntegrable e volume 0 (η / 2)) :
    (∫ p in (0:ℝ)..1, w p) ^ 2 / 2 ≤ ∫ p in (0:ℝ)..1, ∫ q in p..1, H p q ∧
    ∫ p in (0:ℝ)..1, ∫ q in p..1, H p q ≤ L * ((∫ p in (0:ℝ)..1, w p) ^ 2 / 2)
        + C0 * (R - 1) * (∫ p in (0:ℝ)..(η / 2), e p)
        + 4 * (∫ p in (0:ℝ)..1, w p) * (∫ q in η..1, w q) + K := by
  obtain ⟨hwAi, hwA⟩ := pgm_half hwi
  have hη2 : 0 < η / 2 := by linarith
  have hη2' : η / 2 ≤ 1 := by linarith
  have hw01 : ∀ p ∈ Icc (0:ℝ) 1, 0 ≤ w p := fun p hp => hw0 p hp.1 hp.2
  -- nonnegativity of integrals
  have hA0 : ∀ p, 0 ≤ p → p ≤ 1 → 0 ≤ ∫ q in p..1, w q := fun p hp0 hp1 =>
    intervalIntegral.integral_nonneg hp1 (fun q hq => hw0 q (hp0.trans hq.1) hq.2)
  have hT0 : 0 ≤ ∫ q in η..1, w q := hA0 η hη0.le hη1.le
  have hM0 : 0 ≤ ∫ p in (0:ℝ)..1, w p :=
    intervalIntegral.integral_nonneg zero_le_one hw01
  constructor
  · -- lower bound
    rw [← hwA]
    apply intervalIntegral.integral_mono_on_of_le_Ioo zero_le_one hwAi hHo
    intro p hp
    have hp1 : p < 1 := hp.2
    calc w p * ∫ q in p..1, w q = ∫ q in p..1, w p * w q := by
          rw [intervalIntegral.integral_const_mul]
      _ ≤ ∫ q in p..1, H p q := by
          apply intervalIntegral.integral_mono_on_of_le_Ioo hp1.le
            ((pgm_sub hwi hp.1.le hp1.le le_rfl).const_mul _) (hHi p hp.1 hp1)
          intro q hq
          exact R1 p q hp.1 hq.1 hq.2
  · -- upper bound
    set T := ∫ q in η..1, w q with hT
    set M := ∫ p in (0:ℝ)..1, w p with hM
    have key : ∀ p, 0 < p → p < η / 2 → ∫ q in p..1, H p q ≤
        C0 * (R - 1) * e p + L * (w p * ∫ q in p..1, w q) + 4 * T * w p := by
      intro p hp0 hpη
      have hp1 : p < 1 := by linarith
      have hwp : 0 ≤ w p := hw0 p hp0.le hp1.le
      have hgp : w p ≤ g p := hwg p p hp0 le_rfl hp1
      set m := min (R * p) η with hm
      have hpm : p ≤ m := le_min (by nlinarith) (by linarith)
      have hmη : m ≤ η := min_le_right _ _
      have hmR : m ≤ R * p := min_le_left _ _
      have hi := hHi p hp0 hp1
      have i1 : IntervalIntegrable (H p) volume p m := pgm_sub hi le_rfl hpm (by linarith)
      have i2 : IntervalIntegrable (H p) volume m η := pgm_sub hi hpm hmη hη1.le
      have i3 : IntervalIntegrable (H p) volume η 1 := pgm_sub hi (by linarith) hη1.le le_rfl
      have i12 : IntervalIntegrable (H p) volume p η := pgm_sub hi le_rfl (hpm.trans hmη) hη1.le
      have hsplit : ∫ q in p..1, H p q = (∫ q in p..m, H p q) + (∫ q in m..η, H p q) + ∫ q in η..1, H p q := by
        rw [intervalIntegral.integral_add_adjacent_intervals i1 i2,
          intervalIntegral.integral_add_adjacent_intervals i12 i3]
      have b1 : ∫ q in p..m, H p q ≤ C0 * (w p * g p) * (m - p) := by
        have := intervalIntegral.integral_mono_on_of_le_Ioo (a := p) (b := m) (f := H p)
          (g := fun _ => C0 * (w p * g p)) hpm i1 intervalIntegrable_const (by
            intro q hq
            have hq1 : q < 1 := by linarith [hq.2]
            have h1 := R2 p q hp0 hq.1 (by linarith [hq.2])
            have h2 := hwg p q hp0 hq.1.le hq1
            calc H p q ≤ C0 * (w p * w q) := h1
              _ ≤ C0 * (w p * g p) := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h2 hwp) hC0)
        simp only [intervalIntegral.integral_const, smul_eq_mul] at this
        linarith [this]
      have b2 : ∫ q in m..η, H p q ≤ L * (w p * ∫ q in m..η, w q) := by
        have := intervalIntegral.integral_mono_on_of_le_Ioo (a := m) (b := η) (f := H p)
          (g := fun q => L * (w p * w q)) hmη i2
          (((pgm_sub hwi (by linarith) hmη hη1.le).const_mul (w p)).const_mul L) (by
            intro q hq
            have hRq : R * p ≤ q := by
              by_contra hcon
              exact absurd (lt_min (not_le.1 hcon) hq.2) (not_lt.2 hq.1.le)
            exact R3 p q hp0 hRq (by linarith [hq.1]) hq.2)
        rwa [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at this
      have b3 : ∫ q in η..1, H p q ≤ 4 * (w p * T) := by
        have := intervalIntegral.integral_mono_on_of_le_Ioo (a := η) (b := 1) (f := H p)
          (g := fun q => 4 * (w p * w q)) hη1.le i3
          (((pgm_sub hwi (by linarith) hη1.le le_rfl).const_mul (w p)).const_mul 4) (by
            intro q hq
            exact R4 p q hp0 hpη hq.1.le hq.2)
        rwa [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at this
      have c1 : ∫ q in m..η, w q ≤ ∫ q in p..1, w q :=
        intervalIntegral.integral_mono_interval hpm hmη hη1.le (pgm_nn_ae hw0 hp0.le le_rfl)
          (pgm_sub hwi hp0.le hp1.le le_rfl)
      have c2 : C0 * (w p * g p) * (m - p) ≤ C0 * (R - 1) * e p := by
        have h1 : m - p ≤ (R - 1) * p := by nlinarith
        have h2 : 0 ≤ C0 * (w p * g p) := mul_nonneg hC0 (mul_nonneg hwp (hwp.trans hgp))
        calc C0 * (w p * g p) * (m - p) ≤ C0 * (w p * g p) * ((R - 1) * p) :=
              mul_le_mul_of_nonneg_left h1 h2
          _ = C0 * (R - 1) * (p * g p * w p) := by ring
          _ ≤ C0 * (R - 1) * e p :=
              mul_le_mul_of_nonneg_left (he p hp0 hpη) (mul_nonneg hC0 (by linarith))
      have c3 : L * (w p * ∫ q in m..η, w q) ≤ L * (w p * ∫ q in p..1, w q) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left c1 hwp) (by linarith)
      rw [hsplit]
      nlinarith
    have key2 : ∀ p, η / 2 ≤ p → p ≤ 1 → ∫ q in p..1, H p q ≤ K := by
      intro p hp1 hp2
      rcases eq_or_lt_of_le hp2 with h | h
      · rw [h]; simpa using hK
      · have hp0 : 0 < p := by linarith
        have := intervalIntegral.integral_mono_on_of_le_Ioo (a := p) (b := 1) (f := H p)
          (g := fun _ => K) hp2 (hHi p hp0 h) intervalIntegrable_const
          (fun q hq => R5 p q hp1 hq.1 hq.2)
        simp only [intervalIntegral.integral_const, smul_eq_mul] at this
        nlinarith
    -- split the outer integral
    have hHo1 : IntervalIntegrable (fun p => ∫ q in p..1, H p q) volume 0 (η / 2) :=
      pgm_sub hHo le_rfl hη2.le hη2'
    have hHo2 : IntervalIntegrable (fun p => ∫ q in p..1, H p q) volume (η / 2) 1 :=
      pgm_sub hHo hη2.le hη2' le_rfl
    rw [← intervalIntegral.integral_add_adjacent_intervals hHo1 hHo2]
    have part2 : ∫ p in (η / 2)..1, ∫ q in p..1, H p q ≤ K := by
      have := intervalIntegral.integral_mono_on (a := η / 2) (b := 1)
        (f := fun p => ∫ q in p..1, H p q) (g := fun _ => K) hη2' hHo2 intervalIntegrable_const
        (fun p hp => key2 p hp.1 hp.2)
      simp only [intervalIntegral.integral_const, smul_eq_mul] at this
      nlinarith
    have hwA_i1 : IntervalIntegrable (fun p => w p * ∫ q in p..1, w q) volume 0 (η / 2) :=
      pgm_sub hwAi le_rfl hη2.le hη2'
    have hw_i1 : IntervalIntegrable w volume 0 (η / 2) := pgm_sub hwi le_rfl hη2.le hη2'
    have part1 : ∫ p in (0:ℝ)..(η / 2), ∫ q in p..1, H p q ≤
        C0 * (R - 1) * (∫ p in (0:ℝ)..(η / 2), e p) + L * (M ^ 2 / 2) + 4 * M * T := by
      have hb := intervalIntegral.integral_mono_on_of_le_Ioo (a := 0) (b := η / 2) hη2.le hHo1
        (((hei.const_mul (C0 * (R - 1))).add (hwA_i1.const_mul L)).add (hw_i1.const_mul (4 * T)))
        (fun p hp => key p hp.1 hp.2)
      rw [intervalIntegral.integral_add ((hei.const_mul (C0 * (R - 1))).add (hwA_i1.const_mul L))
        (hw_i1.const_mul (4 * T)), intervalIntegral.integral_add (hei.const_mul (C0 * (R - 1)))
        (hwA_i1.const_mul L), intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
        intervalIntegral.integral_const_mul] at hb
      have d1 : ∫ p in (0:ℝ)..(η / 2), w p * ∫ q in p..1, w q ≤ M ^ 2 / 2 := by
        rw [← hwA]
        refine intervalIntegral.integral_mono_interval le_rfl hη2.le hη2' ?_ hwAi
        refine (ae_restrict_iff' measurableSet_Ioc).2 (ae_of_all _ fun p hp => ?_)
        exact mul_nonneg (hw0 p hp.1.le hp.2) (hA0 p hp.1.le hp.2)
      have d2 : ∫ p in (0:ℝ)..(η / 2), w p ≤ M :=
        intervalIntegral.integral_mono_interval le_rfl hη2.le hη2' (pgm_nn_ae hw0 le_rfl le_rfl) hwi
      have := mul_le_mul_of_nonneg_left d1 (by linarith : (0:ℝ) ≤ L)
      have := mul_le_mul_of_nonneg_left d2 (by linarith [hT0] : (0:ℝ) ≤ 4 * T)
      nlinarith
    nlinarith

private lemma pgm_V_lt {α p q : ℝ} (hα : 0 < α) (hp : p ∈ Ioo (0:ℝ) 1) (hq : q ∈ Ioo (0:ℝ) 1)
    (hpq : p < q) : contV α p < contV α q := by
  have hp' := prof_contV_spec hα hp
  have hq' := prof_contV_spec hα hq
  by_contra h
  have := (prof_contS_strictMonoOn hα).monotoneOn (Set.mem_Ioi.2 hq'.1) (Set.mem_Ioi.2 hp'.1)
    (not_lt.1 h)
  rw [hp'.2, hq'.2] at this
  linarith

/-- the factor `D(p,q)` of the continuum double-integral form -/
private lemma pgm_h_conc {α x p q : ℝ} (hα : 0 < α) (hx : 0 < x) (hp : 0 < p) (hpq : p < q)
    (hq : q < 1) :
    (profF α x q - profF α x p) / (q - p) * Real.sqrt (profU α p / profU α q) / x ^ α =
      (Real.sqrt ((1 - p) / (p * contV α p)) * profF α x p) *
        (Real.sqrt ((1 - q) / (q * contV α q)) * profF α x q) *
        (q * (contV α q - contV α p) / ((1 - p) * contV α q * (q - p))) := by
  have hp' : p ∈ Ioo (0:ℝ) 1 := ⟨hp, by linarith⟩
  have hq' : q ∈ Ioo (0:ℝ) 1 := ⟨by linarith, hq⟩
  have hV := (prof_contV_spec hα hp').1
  have hlt := pgm_V_lt hα hp' hq' hpq
  have hs : 0 < x ^ α := Real.rpow_pos_of_pos hx α
  have := pgm_h_eq (s := x ^ α) hV hlt hp hpq hq hs
  unfold profF profU
  rw [this]
  field_simp

private lemma pgm_D_one_le {α p q : ℝ} (hα : 0 < α) (hp : 0 < p) (hpq : p < q) (hq : q < 1) :
    1 ≤ q * (contV α q - contV α p) / ((1 - p) * contV α q * (q - p)) := by
  have hp' : p ∈ Ioo (0:ℝ) 1 := ⟨hp, by linarith⟩
  have hq' : q ∈ Ioo (0:ℝ) 1 := ⟨by linarith, hq⟩
  have hV := prof_contV_spec hα hp'
  have hW := prof_contV_spec hα hq'
  have hlt := pgm_V_lt hα hp' hq' hpq
  have hK1 := pgm_K1 hα hV.1 hlt.le
  rw [hV.2, hW.2] at hK1
  have hd := pgm_D_ge hV.1 hlt hp hpq hK1
  have h1p : 0 < 1 - p := by linarith
  rw [le_div_iff₀ (by have := hW.1; have : 0 < q - p := by linarith
                      positivity)]
  linarith

private lemma pgm_D_le_diag {α p q : ℝ} (hα : 0 < α) (hp : 0 < p) (hpq : p < q) (hq : q < 1) :
    q * (contV α q - contV α p) / ((1 - p) * contV α q * (q - p)) ≤ q / ((1 - p) * (q - p)) := by
  have hp' : p ∈ Ioo (0:ℝ) 1 := ⟨hp, by linarith⟩
  have hq' : q ∈ Ioo (0:ℝ) 1 := ⟨by linarith, hq⟩
  exact pgm_D_diag (prof_contV_spec hα hp').1 (pgm_V_lt hα hp' hq' hpq) hp hpq hq

private lemma pgm_D_le_el {α c p q : ℝ} (hα : 0 < α) (hc : 0 < c)
    (hT : ∀ V : ℝ, 0 < V → c * (contS α V * (1 - contS α V)) ≤ Tcont α V)
    (hp : 0 < p) (hpq : p < q) (hq : q < 1) :
    q * (contV α q - contV α p) / ((1 - p) * contV α q * (q - p)) ≤
      1 / (c * ((1 - p) * (1 - q))) := by
  have hp' : p ∈ Ioo (0:ℝ) 1 := ⟨hp, by linarith⟩
  have hq' : q ∈ Ioo (0:ℝ) 1 := ⟨by linarith, hq⟩
  have hV := prof_contV_spec hα hp'
  have hW := prof_contV_spec hα hq'
  have hlt := pgm_V_lt hα hp' hq' hpq
  have hK2 := pgm_K2 hα hV.1 hlt.le
  rw [hV.2, hW.2] at hK2
  have hT' := hT (contV α q) hW.1
  rw [hW.2] at hT'
  exact pgm_D_el hc hV.1 hlt hp hpq hq hT' hK2

private lemma pgm_w_nonneg {α x p : ℝ} (hα : 0 < α) (hx : 0 < x) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    0 ≤ Real.sqrt ((1 - p) / (p * contV α p)) * profF α x p := by
  rcases eq_or_lt_of_le hp0 with h | h
  · rw [← h]; simp
  rcases eq_or_lt_of_le hp1 with h1 | h1
  · rw [h1]; simp
  have hV := (prof_contV_spec hα ⟨h, h1⟩).1
  unfold profF
  have : 0 < x ^ α := Real.rpow_pos_of_pos hx α
  positivity

private lemma pgm_f_le_one {α x p : ℝ} (hα : 0 < α) (hx : 0 < x) (hp : p ∈ Ioo (0:ℝ) 1) :
    0 ≤ profF α x p ∧ profF α x p ≤ 1 := by
  have hV := (prof_contV_spec hα hp).1
  have : 0 < x ^ α := Real.rpow_pos_of_pos hx α
  unfold profF
  refine ⟨by positivity, ?_⟩
  rw [div_le_one (by positivity)]
  linarith

private lemma pgm_g_anti {α p q : ℝ} (hα : 0 < α) (hp : 0 < p) (hpq : p ≤ q) (hq : q < 1) :
    Real.sqrt ((1 - q) / (q * contV α q)) ≤ Real.sqrt ((1 - p) / (p * contV α p)) := by
  have hp' : p ∈ Ioo (0:ℝ) 1 := ⟨hp, by linarith⟩
  have hq' : q ∈ Ioo (0:ℝ) 1 := ⟨by linarith, hq⟩
  have hV := (prof_contV_spec hα hp').1
  have hVq := (prof_contV_spec hα hq').1
  have hm := prof_contV_mono hα hp' hq' hpq
  have hq0 : 0 < q := by linarith
  apply Real.sqrt_le_sqrt
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have h1 : p * contV α p ≤ q * contV α q := mul_le_mul hpq hm hV.le (by linarith)
  have h2 : 1 - q ≤ 1 - p := by linarith
  have h3 : 0 ≤ 1 - q := by linarith
  calc (1 - q) * (p * contV α p) ≤ (1 - q) * (q * contV α q) := mul_le_mul_of_nonneg_left h1 h3
    _ ≤ (1 - p) * (q * contV α q) := mul_le_mul_of_nonneg_right h2 (by positivity)

private lemma pgm_w_le_g {α x p : ℝ} (hα : 0 < α) (hx : 0 < x) (hp : p ∈ Ioo (0:ℝ) 1) :
    Real.sqrt ((1 - p) / (p * contV α p)) * profF α x p ≤ Real.sqrt ((1 - p) / (p * contV α p)) := by
  have := pgm_f_le_one hα hx hp
  have h0 := Real.sqrt_nonneg ((1 - p) / (p * contV α p))
  nlinarith [this.1, this.2]

private lemma pgm_pgw {α x p : ℝ} (hα : 0 < α) (hx : 0 < x) (hp : p ∈ Ioo (0:ℝ) 1) :
    p * Real.sqrt ((1 - p) / (p * contV α p)) *
        (Real.sqrt ((1 - p) / (p * contV α p)) * profF α x p) ≤ 1 / (contV α p + x ^ α) := by
  have hV := (prof_contV_spec hα hp).1
  have hs : 0 < x ^ α := Real.rpow_pos_of_pos hx α
  have hp0 := hp.1
  have hp1 : 0 < 1 - p := by linarith [hp.2]
  have hsq : Real.sqrt ((1 - p) / (p * contV α p)) * Real.sqrt ((1 - p) / (p * contV α p)) =
      (1 - p) / (p * contV α p) := Real.mul_self_sqrt (by positivity)
  have : p * Real.sqrt ((1 - p) / (p * contV α p)) *
        (Real.sqrt ((1 - p) / (p * contV α p)) * profF α x p) = (1 - p) / (contV α p + x ^ α) := by
    calc _ = p * (Real.sqrt ((1 - p) / (p * contV α p)) * Real.sqrt ((1 - p) / (p * contV α p))) * profF α x p := by ring
      _ = _ := by
        rw [hsq]; unfold profF; field_simp
  rw [this]
  exact div_le_div_of_nonneg_right (by linarith) (by positivity)

private lemma pgm_e_int {α x η : ℝ} (hα : 0 < α) (hx : 0 < x) (hη0 : 0 ≤ η) (hη : η < 1) :
    IntervalIntegrable (fun p => 1 / (contV α p + x ^ α)) volume 0 η := by
  have hs : 0 < x ^ α := Real.rpow_pos_of_pos hx α
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hη0]
  have hm : AEMeasurable (contV α) (volume.restrict (Ioc (0:ℝ) η)) :=
    (prof_contV_aemeas hα).mono_measure (Measure.restrict_mono (Ioc_subset_Ioc_right hη.le) le_rfl)
  have hm2 : AEMeasurable (fun p => 1 / (contV α p + x ^ α)) (volume.restrict (Ioc (0:ℝ) η)) :=
    (measurable_const.aemeasurable).div (hm.add measurable_const.aemeasurable)
  refine Integrable.mono' (g := fun _ => 1 / x ^ α) (integrable_const _) hm2.aestronglyMeasurable ?_
  refine (ae_restrict_iff' measurableSet_Ioc).2 (ae_of_all _ fun p hp => ?_)
  have hV := (prof_contV_spec hα ⟨hp.1, lt_of_le_of_lt hp.2 hη⟩).1
  rw [Real.norm_of_nonneg (by positivity)]
  exact one_div_le_one_div_of_le hs (by linarith)

private lemma pgm_one_sub_S {α V : ℝ} (hα : 0 < α) (hV : 0 < V) :
    1 / ((α + 1) * (V + 1)) ≤ 1 - contS α V := by
  have hint : ∫ t in (0:ℝ)..1, (1 - V / (V + t ^ α)) = 1 - contS α V := by
    unfold contS
    rw [intervalIntegral.integral_sub intervalIntegrable_const (prof_cont_on hα hV).intervalIntegrable]
    simp
  rw [← hint]
  have hrp : ∫ t in (0:ℝ)..1, t ^ α = 1 / (α + 1) := by
    rw [integral_rpow (Or.inl (by linarith))]
    simp [Real.zero_rpow (show α + 1 ≠ 0 by linarith)]
  have hmono : ∫ t in (0:ℝ)..1, t ^ α / (V + 1) ≤ ∫ t in (0:ℝ)..1, (1 - V / (V + t ^ α)) := by
    apply intervalIntegral.integral_mono_on zero_le_one
    · exact (intervalIntegral.intervalIntegrable_rpow' (by linarith)).div_const _
    · exact (continuousOn_const.sub (prof_cont_on hα hV)).intervalIntegrable
    · intro t ht
      have h0 : 0 ≤ t ^ α := Real.rpow_nonneg ht.1 α
      have h1 : t ^ α ≤ 1 := Real.rpow_le_one ht.1 ht.2 hα.le
      have h2 : 0 < V + t ^ α := by linarith
      rw [one_sub_div h2.ne']
      rw [show V + t ^ α - V = t ^ α by ring]
      exact div_le_div_of_nonneg_left h0 h2 (by linarith)
  have : ∫ t in (0:ℝ)..1, t ^ α / (V + 1) = 1 / ((α + 1) * (V + 1)) := by
    rw [intervalIntegral.integral_div, hrp]
    field_simp
  linarith

private lemma pgm_V_lower {α a : ℝ} (hα : 0 < α) (ha0 : 0 < a) (ha1 : a < 1) :
    ∃ k : ℝ, 0 < k ∧ ∀ p ∈ Ioo (0:ℝ) 1, a ≤ p → k ≤ contV α p * (1 - p) := by
  have hVa := (prof_contV_spec hα ⟨ha0, ha1⟩).1
  refine ⟨min 1 (contV α a) / (2 * (α + 1)), by positivity, ?_⟩
  intro p hp hap
  have hV := prof_contV_spec hα hp
  have h1 := pgm_one_sub_S hα hV.1
  rw [hV.2] at h1
  have hV0 := hV.1
  have hα1 : 0 < α + 1 := by linarith
  have h2 : 1 ≤ (α + 1) * (contV α p + 1) * (1 - p) := by
    have hp1 : 0 < 1 - p := by linarith [hp.2]
    rw [div_le_iff₀ (by positivity)] at h1
    linarith
  have hu : 0 < 1 - p := by linarith [hp.2]
  have hmin1 : min 1 (contV α a) ≤ 1 := min_le_left _ _
  have hmin2 : min 1 (contV α a) ≤ contV α a := min_le_right _ _
  have hVm : contV α a ≤ contV α p := prof_contV_mono hα ⟨ha0, ha1⟩ hp hap
  rcases le_total (1 - p) (1 / (2 * (α + 1))) with hc | hc
  · -- small 1-p
    have h3 : 1 / (2 * (α + 1)) ≤ contV α p * (1 - p) := by
      have : 1 / (α + 1) ≤ (contV α p + 1) * (1 - p) := by
        rw [div_le_iff₀ hα1]; nlinarith
      have e : 1 / (α + 1) = 2 * (1 / (2 * (α + 1))) := by field_simp
      nlinarith
    calc min 1 (contV α a) / (2 * (α + 1)) ≤ 1 / (2 * (α + 1)) :=
          div_le_div_of_nonneg_right hmin1 (by positivity)
      _ ≤ _ := h3
  · have h3 : contV α a * (1 / (2 * (α + 1))) ≤ contV α p * (1 - p) :=
      mul_le_mul hVm hc (by positivity) hV.1.le
    calc min 1 (contV α a) / (2 * (α + 1)) ≤ contV α a / (2 * (α + 1)) :=
          div_le_div_of_nonneg_right hmin2 (by positivity)
      _ = contV α a * (1 / (2 * (α + 1))) := by ring
      _ ≤ _ := h3

private lemma pgm_R1 {α x p q : ℝ} (hα : 0 < α) (hx : 0 < x) (hp : 0 < p) (hpq : p < q)
    (hq : q < 1) :
    (Real.sqrt ((1 - p) / (p * contV α p)) * profF α x p) *
        (Real.sqrt ((1 - q) / (q * contV α q)) * profF α x q) ≤
      (profF α x q - profF α x p) / (q - p) * Real.sqrt (profU α p / profU α q) / x ^ α := by
  rw [pgm_h_conc hα hx hp hpq hq]
  have h1 := pgm_w_nonneg hα hx (x := x) hp.le (by linarith : p ≤ 1)
  have h2 := pgm_w_nonneg hα hx (x := x) (by linarith : 0 ≤ q) hq.le
  have hD := pgm_D_one_le hα hp hpq hq
  have := mul_nonneg h1 h2
  nlinarith

private lemma pgm_R2 {α x c η p q : ℝ} (hα : 0 < α) (hx : 0 < x) (hc : 0 < c)
    (hT : ∀ V : ℝ, 0 < V → c * (contS α V * (1 - contS α V)) ≤ Tcont α V)
    (hη : η ≤ 1 / 2) (hp : 0 < p) (hpq : p < q) (hq : q < η) :
    (profF α x q - profF α x p) / (q - p) * Real.sqrt (profU α p / profU α q) / x ^ α ≤
      (4 / c) * ((Real.sqrt ((1 - p) / (p * contV α p)) * profF α x p) *
        (Real.sqrt ((1 - q) / (q * contV α q)) * profF α x q)) := by
  have hq1 : q < 1 := by linarith
  rw [pgm_h_conc hα hx hp hpq hq1]
  have h1 := pgm_w_nonneg hα hx (x := x) hp.le (by linarith : p ≤ 1)
  have h2 := pgm_w_nonneg hα hx (x := x) (by linarith : 0 ≤ q) hq1.le
  have hD := pgm_D_le_el hα hc hT hp hpq hq1
  have hb : 1 / (c * ((1 - p) * (1 - q))) ≤ 4 / c := by
    have e1 : 0 < 1 - p := by linarith
    have e2 : 0 < 1 - q := by linarith
    rw [div_le_div_iff₀ (by positivity) hc]
    have : 1 / 4 ≤ (1 - p) * (1 - q) := by nlinarith
    nlinarith
  have := mul_nonneg h1 h2
  calc _ = ((Real.sqrt ((1 - p) / (p * contV α p)) * profF α x p) *
        (Real.sqrt ((1 - q) / (q * contV α q)) * profF α x q)) * (q * (contV α q - contV α p) / ((1 - p) * contV α q * (q - p))) := rfl
    _ ≤ ((Real.sqrt ((1 - p) / (p * contV α p)) * profF α x p) *
        (Real.sqrt ((1 - q) / (q * contV α q)) * profF α x q)) * (4 / c) :=
        mul_le_mul_of_nonneg_left (hD.trans hb) this
    _ = _ := by ring

private lemma pgm_R3 {α x η R p q : ℝ} (hα : 0 < α) (hx : 0 < x) (hR : 1 < R)
    (hη : η < 1) (hp : 0 < p) (hRq : R * p ≤ q) (hpq : p < q) (hq : q < η) :
    (profF α x q - profF α x p) / (q - p) * Real.sqrt (profU α p / profU α q) / x ^ α ≤
      (1 / ((1 - η) * (1 - 1 / R))) * ((Real.sqrt ((1 - p) / (p * contV α p)) * profF α x p) *
        (Real.sqrt ((1 - q) / (q * contV α q)) * profF α x q)) := by
  have hq1 : q < 1 := by linarith
  rw [pgm_h_conc hα hx hp hpq hq1]
  have h1 := pgm_w_nonneg hα hx (x := x) hp.le (by linarith : p ≤ 1)
  have h2 := pgm_w_nonneg hα hx (x := x) (by linarith : 0 ≤ q) hq1.le
  have hD := pgm_D_le_diag hα hp hpq hq1
  have hq0 : 0 < q := by linarith
  have hR0 : 0 < R := by linarith
  have hb : q / ((1 - p) * (q - p)) ≤ 1 / ((1 - η) * (1 - 1 / R)) := by
    have e1 : 0 < 1 - 1 / R := by
      rw [sub_pos, div_lt_one hR0]; exact hR
    have e2 : 0 < 1 - η := by linarith
    have e3 : (1 - η) * q * (1 - 1 / R) ≤ (1 - p) * (q - p) := by
      have : p ≤ q / R := by rw [le_div_iff₀ hR0]; linarith
      have h3 : q * (1 - 1 / R) ≤ q - p := by
        have : q / R = q * (1 / R) := by ring
        nlinarith
      have h4 : 1 - η ≤ 1 - p := by linarith
      calc (1 - η) * q * (1 - 1 / R) = (1 - η) * (q * (1 - 1 / R)) := by ring
        _ ≤ (1 - p) * (q - p) :=
          mul_le_mul h4 h3 (by positivity) (by linarith)
    have e4 : 0 < 1 - p := by linarith
    have e5 : 0 < q - p := by linarith
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  have := mul_nonneg h1 h2
  calc _ = ((Real.sqrt ((1 - p) / (p * contV α p)) * profF α x p) *
        (Real.sqrt ((1 - q) / (q * contV α q)) * profF α x q)) * (q * (contV α q - contV α p) / ((1 - p) * contV α q * (q - p))) := rfl
    _ ≤ ((Real.sqrt ((1 - p) / (p * contV α p)) * profF α x p) *
        (Real.sqrt ((1 - q) / (q * contV α q)) * profF α x q)) * (1 / ((1 - η) * (1 - 1 / R))) :=
        mul_le_mul_of_nonneg_left (hD.trans hb) this
    _ = _ := by ring

private lemma pgm_R4 {α x η p q : ℝ} (hα : 0 < α) (hx : 0 < x) (hη : η < 1)
    (hp : 0 < p) (hpη : p < η / 2) (hηq : η ≤ q) (hq : q < 1) :
    (profF α x q - profF α x p) / (q - p) * Real.sqrt (profU α p / profU α q) / x ^ α ≤
      4 * ((Real.sqrt ((1 - p) / (p * contV α p)) * profF α x p) *
        (Real.sqrt ((1 - q) / (q * contV α q)) * profF α x q)) := by
  have hpq : p < q := by linarith
  rw [pgm_h_conc hα hx hp hpq hq]
  have h1 := pgm_w_nonneg hα hx (x := x) hp.le (by linarith : p ≤ 1)
  have h2 := pgm_w_nonneg hα hx (x := x) (by linarith : 0 ≤ q) hq.le
  have hD := pgm_D_le_diag hα hp hpq hq
  have hq0 : 0 < q := by linarith
  have hb : q / ((1 - p) * (q - p)) ≤ 4 := by
    have e2 : 1 / 2 ≤ 1 - p := by linarith
    have e3 : q / 2 ≤ q - p := by linarith
    have e4 : 0 < 1 - p := by linarith
    have e5 : 0 < q - p := by linarith
    rw [div_le_iff₀ (by positivity)]
    nlinarith [mul_le_mul e2 e3 (by linarith) (by linarith)]
  have := mul_nonneg h1 h2
  calc _ = ((Real.sqrt ((1 - p) / (p * contV α p)) * profF α x p) *
        (Real.sqrt ((1 - q) / (q * contV α q)) * profF α x q)) * (q * (contV α q - contV α p) / ((1 - p) * contV α q * (q - p))) := rfl
    _ ≤ ((Real.sqrt ((1 - p) / (p * contV α p)) * profF α x p) *
        (Real.sqrt ((1 - q) / (q * contV α q)) * profF α x q)) * 4 :=
        mul_le_mul_of_nonneg_left (hD.trans hb) this
    _ = _ := by ring

private lemma pgm_w_end {α a : ℝ} (hα : 0 < α) (ha0 : 0 < a) (ha1 : a < 1) :
    ∃ C1 : ℝ, 0 < C1 ∧ ∀ x : ℝ, 0 < x → ∀ p ∈ Ioo (0:ℝ) 1, a ≤ p →
      Real.sqrt ((1 - p) / (p * contV α p)) * profF α x p ≤ C1 * (1 - p) := by
  obtain ⟨k, hk, hkp⟩ := pgm_V_lower (α := α) hα ha0 ha1
  have hak : 0 < a * k := mul_pos ha0 hk
  refine ⟨1 / Real.sqrt (a * k), by positivity, ?_⟩
  intro x hx p hp hap
  refine (pgm_w_le_g hα hx hp).trans ?_
  have hV := (prof_contV_spec hα hp).1
  have hp1 : 0 < 1 - p := by linarith [hp.2]
  rw [Real.sqrt_le_iff]
  refine ⟨by positivity, ?_⟩
  rw [mul_pow, div_pow, one_pow, Real.sq_sqrt hak.le]
  have h1 := hkp p hp hap
  have h2 : a * k ≤ p * (contV α p * (1 - p)) :=
    mul_le_mul hap h1 hk.le hp.1.le
  have hp0 := hp.1
  rw [one_div_mul_eq_div, div_le_div_iff₀ (by positivity) hak]
  nlinarith [mul_le_mul_of_nonneg_left h2 hp1.le]

private lemma pgm_R5 {α c a : ℝ} (hα : 0 < α) (hc : 0 < c)
    (hT : ∀ V : ℝ, 0 < V → c * (contS α V * (1 - contS α V)) ≤ Tcont α V)
    (ha0 : 0 < a) (ha1 : a < 1) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ x : ℝ, 0 < x → ∀ p q : ℝ, a ≤ p → p < q → q < 1 →
      (profF α x q - profF α x p) / (q - p) * Real.sqrt (profU α p / profU α q) / x ^ α ≤ K := by
  obtain ⟨C1, hC1, hw⟩ := pgm_w_end hα ha0 ha1
  refine ⟨C1 ^ 2 / c, by positivity, ?_⟩
  intro x hx p q hap hpq hq
  have hp0 : 0 < p := by linarith
  rw [pgm_h_conc hα hx hp0 hpq hq]
  have hp1 : 0 < 1 - p := by linarith
  have hq1 : 0 < 1 - q := by linarith
  have h1 := hw x hx p ⟨hp0, by linarith⟩ hap
  have h2 := hw x hx q ⟨by linarith, hq⟩ (by linarith)
  have h1' := pgm_w_nonneg hα hx (x := x) hp0.le (by linarith : p ≤ 1)
  have h2' := pgm_w_nonneg hα hx (x := x) (by linarith : 0 ≤ q) hq.le
  have hD := pgm_D_le_el hα hc hT hp0 hpq hq
  have hD0 : 0 ≤ q * (contV α q - contV α p) / ((1 - p) * contV α q * (q - p)) :=
    le_trans zero_le_one (pgm_D_one_le hα hp0 hpq hq)
  have e : C1 * (1 - p) * (C1 * (1 - q)) * (1 / (c * ((1 - p) * (1 - q)))) = C1 ^ 2 / c := by
    field_simp
  calc _ ≤ C1 * (1 - p) * (C1 * (1 - q)) * (1 / (c * ((1 - p) * (1 - q)))) := by
        apply mul_le_mul (mul_le_mul h1 h2 h2' (by positivity)) hD hD0 (by positivity)
    _ = _ := e

private lemma pgm_contV_cont {α : ℝ} (hα : 0 < α) : ContinuousOn (contV α) (Ioo (0:ℝ) 1) := by
  intro a ha
  apply ContinuousAt.continuousWithinAt
  have hs : Ioo (0:ℝ) 1 ∈ 𝓝 a := Ioo_mem_nhds ha.1 ha.2
  refine continuousAt_of_monotoneOn_of_image_mem_nhds (prof_contV_mono hα) hs ?_
  have himg : contV α '' Ioo (0:ℝ) 1 = Ioi 0 := by
    ext V
    constructor
    · rintro ⟨p, hp, rfl⟩
      exact (prof_contV_spec hα hp).1
    · intro hV
      have hV' : (0:ℝ) < V := hV
      have hm : contS α V ∈ Ioo (0:ℝ) 1 := ⟨prof_contS_pos hα hV', prof_contS_lt_one hα hV'⟩
      refine ⟨contS α V, hm, ?_⟩
      have h := prof_contV_spec hα hm
      exact (prof_contS_strictMonoOn hα).injOn (Set.mem_Ioi.2 h.1) hV h.2
  rw [himg]
  exact Ioi_mem_nhds (prof_contV_spec hα ha).1


private lemma pgm_sqrtU_le_one {α p q : ℝ} (hα : 0 < α) (hp : 0 < p) (hpq : p < q) (hq : q < 1) :
    Real.sqrt (profU α p / profU α q) ≤ 1 := by
  have hp' : p ∈ Ioo (0:ℝ) 1 := ⟨hp, by linarith⟩
  have hq' : q ∈ Ioo (0:ℝ) 1 := ⟨by linarith, hq⟩
  have hVp := prof_contV_spec hα hp'
  have hVq := prof_contV_spec hα hq'
  have hlt := pgm_V_lt hα hp' hq' hpq
  have hK1 := pgm_K1 hα hVp.1 hlt.le
  rw [hVp.2, hVq.2] at hK1
  apply Real.sqrt_le_one.mpr
  unfold profU
  have h1p : 0 < 1 - p := by linarith
  have h1q : 0 < 1 - q := by linarith
  have hq0 : 0 < q := by linarith
  have hVq0 := hVq.1
  rw [div_le_one (by positivity)]
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have : contV α p * q ≤ contV α q * p := hK1
  nlinarith [mul_le_mul this (show 1 - q ≤ 1 - p by linarith) h1q.le (by positivity)]

private lemma pgm_diff_nonneg {α x p q : ℝ} (hα : 0 < α) (hx : 0 < x) (hp : 0 < p) (hpq : p < q)
    (hq : q < 1) : 0 ≤ profF α x q - profF α x p := by
  have hp' : p ∈ Ioo (0:ℝ) 1 := ⟨hp, by linarith⟩
  have hq' : q ∈ Ioo (0:ℝ) 1 := ⟨by linarith, hq⟩
  have hVp := prof_contV_spec hα hp'
  have hVq := prof_contV_spec hα hq'
  have hlt := pgm_V_lt hα hp' hq' hpq
  have hVp0 := hVp.1
  have hVq0 := hVq.1
  have e : profF α x q - profF α x p =
      x ^ α * (contV α q - contV α p) / ((contV α q + x ^ α) * (contV α p + x ^ α)) := by
    unfold profF; field_simp; ring
  rw [e]
  have := sub_nonneg.2 hlt.le
  positivity

private lemma pgm_hh_bd {α x p q : ℝ} (hα : 0 < α) (hx : 0 < x) (hp : 0 < p) (hpq : p < q)
    (hq : q < 1) :
    0 ≤ (profF α x q - profF α x p) / (q - p) * Real.sqrt (profU α p / profU α q) ∧
    (profF α x q - profF α x p) / (q - p) * Real.sqrt (profU α p / profU α q) ≤ 1 / (q - p) := by
  have hp' : p ∈ Ioo (0:ℝ) 1 := ⟨hp, by linarith⟩
  have hq' : q ∈ Ioo (0:ℝ) 1 := ⟨by linarith, hq⟩
  have hs : 0 < x ^ α := Real.rpow_pos_of_pos hx α
  have hqp : 0 < q - p := by linarith
  have hc := pgm_h_conc hα hx hp hpq hq
  have h1 := pgm_w_nonneg hα hx (x := x) hp.le (by linarith : p ≤ 1)
  have h2 := pgm_w_nonneg hα hx (x := x) (by linarith : 0 ≤ q) hq.le
  have hD := le_trans zero_le_one (pgm_D_one_le hα hp hpq hq)
  have hnn : 0 ≤ (profF α x q - profF α x p) / (q - p) * Real.sqrt (profU α p / profU α q) := by
    have : 0 ≤ (profF α x q - profF α x p) / (q - p) * Real.sqrt (profU α p / profU α q) / x ^ α := by
      rw [hc]; positivity
    exact (div_nonneg_iff.1 this).elim (fun h => h.1) (fun h => by
      exfalso; linarith [h.2, hs])
  refine ⟨hnn, ?_⟩
  have hVp := prof_contV_spec hα hp'
  have hVq := prof_contV_spec hα hq'
  have hlt := pgm_V_lt hα hp' hq' hpq
  have hK1 := pgm_K1 hα hVp.1 hlt.le
  rw [hVp.2, hVq.2] at hK1
  have hsq := pgm_sqrtU_le_one hα hp hpq hq
  have hdf : profF α x q - profF α x p ≤ 1 := by
    have a1 := (pgm_f_le_one hα hx hq').2
    have a2 := (pgm_f_le_one hα hx hp').1
    linarith
  have hdf0 := pgm_diff_nonneg hα hx hp hpq hq
  calc _ ≤ (profF α x q - profF α x p) / (q - p) * 1 :=
        mul_le_mul_of_nonneg_left hsq (div_nonneg hdf0 hqp.le)
    _ ≤ 1 / (q - p) := by rw [mul_one]; exact div_le_div_of_nonneg_right hdf hqp.le

private lemma pgm_F_int {α x : ℝ} (hα : 0 < α) (hx : 0 < x) :
    IntervalIntegrable (profF α x) volume 0 1 := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one,
    integrableOn_Ioc_iff_integrableOn_Ioo]
  have hs : 0 < x ^ α := Real.rpow_pos_of_pos hx α
  have hm : AEMeasurable (contV α) (volume.restrict (Ioo (0:ℝ) 1)) :=
    (prof_contV_aemeas hα).mono_measure (Measure.restrict_mono Ioo_subset_Ioc_self le_rfl)
  have hm2 : AEMeasurable (profF α x) (volume.restrict (Ioo (0:ℝ) 1)) := by
    unfold profF
    exact hm.div (hm.add measurable_const.aemeasurable)
  refine Integrable.mono' (g := fun _ => (1:ℝ)) (integrable_const _) hm2.aestronglyMeasurable ?_
  refine (ae_restrict_iff' measurableSet_Ioo).2 (ae_of_all _ fun p hp => ?_)
  have := pgm_f_le_one hα hx hp
  rw [Real.norm_of_nonneg this.1]
  exact this.2

private lemma pgm_C_le_one {α x τ : ℝ} (hα : 0 < α) (hx : 0 < x) (hτ0 : 0 < τ) (hτ1 : τ < 1) :
    profC α x τ ≤ 1 := by
  unfold profC
  by_cases hint : IntervalIntegrable (fun p => (profF α x (p + τ) - profF α x p) / τ *
      Real.sqrt (profU α p / profU α (p + τ))) volume 0 (1 - τ)
  swap
  · rw [intervalIntegral.integral_undef hint]; norm_num
  have hφ := pgm_F_int hα hx
  have h1 : IntervalIntegrable (fun p => profF α x (p + τ)) volume 0 (1 - τ) := by
    have hφ' : IntervalIntegrable (profF α x) volume τ 1 := by
      refine hφ.mono_set ?_
      rw [Set.uIcc_of_le hτ1.le, Set.uIcc_of_le zero_le_one]
      exact Set.Icc_subset_Icc hτ0.le le_rfl
    have := hφ'.comp_add_right τ
    simpa using this
  have h2 : IntervalIntegrable (profF α x) volume 0 (1 - τ) := by
    refine hφ.mono_set ?_
    rw [Set.uIcc_of_le (by linarith), Set.uIcc_of_le zero_le_one]
    exact Set.Icc_subset_Icc le_rfl (by linarith)
  have hmono : ∫ p in (0:ℝ)..(1 - τ), (profF α x (p + τ) - profF α x p) / τ *
        Real.sqrt (profU α p / profU α (p + τ)) ≤
      ∫ p in (0:ℝ)..(1 - τ), (profF α x (p + τ) - profF α x p) / τ := by
    apply intervalIntegral.integral_mono_on_of_le_Ioo (by linarith) hint ((h1.sub h2).div_const τ)
    intro p hp
    have hd := pgm_diff_nonneg (α := α) (x := x) hα hx hp.1 (by linarith : p < p + τ) (by linarith [hp.2])
    have hs := pgm_sqrtU_le_one (α := α) hα hp.1 (by linarith : p < p + τ) (by linarith [hp.2])
    have := div_nonneg hd hτ0.le
    nlinarith
  refine hmono.trans ?_
  rw [intervalIntegral.integral_div, intervalIntegral.integral_sub h1 h2,
    intervalIntegral.integral_comp_add_right (profF α x) τ, zero_add, sub_add_cancel]
  rw [div_le_one hτ0]
  have a1 : (∫ p in (0:ℝ)..τ, profF α x p) + ∫ p in τ..1, profF α x p = ∫ p in (0:ℝ)..1, profF α x p :=
    intervalIntegral.integral_add_adjacent_intervals
      (hφ.mono_set (by rw [Set.uIcc_of_le hτ0.le, Set.uIcc_of_le zero_le_one]; exact Set.Icc_subset_Icc le_rfl hτ1.le))
      (hφ.mono_set (by rw [Set.uIcc_of_le hτ1.le, Set.uIcc_of_le zero_le_one]; exact Set.Icc_subset_Icc hτ0.le le_rfl))
  have a2 : (∫ p in (0:ℝ)..(1 - τ), profF α x p) + ∫ p in (1 - τ)..1, profF α x p = ∫ p in (0:ℝ)..1, profF α x p :=
    intervalIntegral.integral_add_adjacent_intervals h2
      (hφ.mono_set (by rw [Set.uIcc_of_le (by linarith), Set.uIcc_of_le zero_le_one]; exact Set.Icc_subset_Icc (by linarith) le_rfl))
  have b1 : 0 ≤ ∫ p in (0:ℝ)..τ, profF α x p := by
    have := intervalIntegral.integral_mono_on_of_le_Ioo (a := 0) (b := τ) (f := fun _ => (0:ℝ)) (g := profF α x)
      hτ0.le intervalIntegrable_const
      (hφ.mono_set (by rw [Set.uIcc_of_le hτ0.le, Set.uIcc_of_le zero_le_one]; exact Set.Icc_subset_Icc le_rfl hτ1.le))
      (fun p hp => (pgm_f_le_one hα hx ⟨hp.1, by linarith [hp.2]⟩).1)
    simpa using this
  have b2 : ∫ p in (1 - τ)..1, profF α x p ≤ τ := by
    have := intervalIntegral.integral_mono_on_of_le_Ioo (a := 1 - τ) (b := 1) (f := profF α x) (g := fun _ => (1:ℝ))
      (by linarith) (hφ.mono_set (by rw [Set.uIcc_of_le (by linarith), Set.uIcc_of_le zero_le_one]; exact Set.Icc_subset_Icc (by linarith) le_rfl))
      intervalIntegrable_const (fun p hp => (pgm_f_le_one hα hx ⟨by linarith [hp.1], hp.2⟩).2)
    simpa using this
  linarith

private lemma pgm_profF_cont {α x : ℝ} (hα : 0 < α) (hx : 0 < x) :
    ContinuousOn (profF α x) (Ioo (0:ℝ) 1) := by
  unfold profF
  have hs : 0 < x ^ α := Real.rpow_pos_of_pos hx α
  refine (pgm_contV_cont hα).div ((pgm_contV_cont hα).add continuousOn_const) ?_
  intro p hp
  have := (prof_contV_spec hα hp).1
  linarith

private lemma pgm_profU_cont {α : ℝ} (hα : 0 < α) :
    ContinuousOn (profU α) (Ioo (0:ℝ) 1) := by
  unfold profU
  refine (pgm_contV_cont hα).div (by fun_prop) ?_
  intro p hp
  have : 0 < 1 - p := by linarith [hp.2]
  have := hp.1
  positivity

private lemma pgm_hh_cont {α x : ℝ} (hα : 0 < α) (hx : 0 < x) :
    ContinuousOn (fun z : ℝ × ℝ => (profF α x (z.2 + z.1) - profF α x z.2) / z.1 *
        Real.sqrt (profU α z.2 / profU α (z.2 + z.1)))
      {z : ℝ × ℝ | 0 < z.1 ∧ 0 < z.2 ∧ z.1 + z.2 < 1} := by
  have m1 : MapsTo (fun z : ℝ × ℝ => z.2 + z.1) {z : ℝ × ℝ | 0 < z.1 ∧ 0 < z.2 ∧ z.1 + z.2 < 1}
      (Ioo 0 1) := fun z hz => ⟨by linarith [hz.1, hz.2.1], by linarith [hz.2.2]⟩
  have m2 : MapsTo (fun z : ℝ × ℝ => z.2) {z : ℝ × ℝ | 0 < z.1 ∧ 0 < z.2 ∧ z.1 + z.2 < 1}
      (Ioo 0 1) := fun z hz => ⟨hz.2.1, by linarith [hz.1, hz.2.2]⟩
  have cF1 := (pgm_profF_cont hα hx).comp (by fun_prop : Continuous fun z : ℝ × ℝ => z.2 + z.1).continuousOn m1
  have cF2 := (pgm_profF_cont hα hx).comp (by fun_prop : Continuous fun z : ℝ × ℝ => z.2).continuousOn m2
  have cU1 := (pgm_profU_cont hα).comp (by fun_prop : Continuous fun z : ℝ × ℝ => z.2 + z.1).continuousOn m1
  have cU2 := (pgm_profU_cont hα).comp (by fun_prop : Continuous fun z : ℝ × ℝ => z.2).continuousOn m2
  refine ((cF1.sub cF2).div (by fun_prop : Continuous fun z : ℝ × ℝ => z.1).continuousOn
    (fun z hz => hz.1.ne')).mul (Real.continuous_sqrt.comp_continuousOn (cU2.div cU1 ?_))
  intro z hz
  have h := m1 hz
  have hV := (prof_contV_spec hα h).1
  unfold profU
  have : 0 < 1 - (z.2 + z.1) := by linarith [h.2]
  have : 0 < z.2 + z.1 := h.1
  positivity

private lemma pgm_Gam_int {α x : ℝ} (hα : 0 < α) (hx : 0 < x) :
    Integrable (fun z : ℝ × ℝ => if z.1 + z.2 < 1 then
        (profF α x (z.2 + z.1) - profF α x z.2) / z.1 *
          Real.sqrt (profU α z.2 / profU α (z.2 + z.1)) else 0)
      ((volume.restrict (Ioc (0:ℝ) 1)).prod (volume.restrict (Ioc (0:ℝ) 1))) := by
  have hx0 := hx
  set μ : Measure ℝ := volume.restrict (Ioc (0:ℝ) 1) with hμ
  set F : ℝ × ℝ → ℝ := fun z => if z.1 + z.2 < 1 then
        (profF α x (z.2 + z.1) - profF α x z.2) / z.1 *
          Real.sqrt (profU α z.2 / profU α (z.2 + z.1)) else 0 with hF
  have hO : MeasurableSet {z : ℝ × ℝ | 0 < z.1 ∧ 0 < z.2 ∧ z.1 + z.2 < 1} := by
    refine MeasurableSet.inter (measurableSet_lt measurable_const measurable_fst) ?_
    refine MeasurableSet.inter (measurableSet_lt measurable_const measurable_snd) ?_
    exact measurableSet_lt (measurable_fst.add measurable_snd) measurable_const
  have hmeas : AEStronglyMeasurable F (μ.prod μ) := by
    have h1 : AEStronglyMeasurable (Set.indicator {z : ℝ × ℝ | 0 < z.1 ∧ 0 < z.2 ∧ z.1 + z.2 < 1}
        (fun z : ℝ × ℝ => (profF α x (z.2 + z.1) - profF α x z.2) / z.1 *
          Real.sqrt (profU α z.2 / profU α (z.2 + z.1)))) (μ.prod μ) :=
      (aestronglyMeasurable_indicator_iff hO).2
        ((pgm_hh_cont hα hx0).aestronglyMeasurable hO)
    refine h1.congr ?_
    rw [hμ, Measure.prod_restrict]
    refine (ae_restrict_iff' (measurableSet_Ioc.prod measurableSet_Ioc)).2 (ae_of_all _ fun z hz => ?_)
    have a1 : 0 < z.1 := hz.1.1
    have a2 : 0 < z.2 := hz.2.1
    simp only [hF, Set.indicator, Set.mem_setOf_eq]
    by_cases h : z.1 + z.2 < 1
    · simp [h, a1, a2]
    · simp [h]
  rw [integrable_prod_iff hmeas]
  have hnn : ∀ τ ∈ Ioc (0:ℝ) 1, ∀ p ∈ Ioc (0:ℝ) 1, 0 ≤ F (τ, p) := by
    intro τ hτ p hp
    simp only [hF]
    by_cases h : τ + p < 1
    · rw [if_pos h]
      have := pgm_hh_bd (α := α) (x := x) hα hx0 hp.1 (by linarith [hτ.1] : p < p + τ) (by linarith)
      simpa using this.1
    · rw [if_neg h]
  constructor
  · have hs := hmeas.prodMk_left
    have hτae : ∀ᵐ τ ∂μ, τ ∈ Ioc (0:ℝ) 1 := by
      rw [hμ]; exact ae_restrict_mem measurableSet_Ioc
    filter_upwards [hs, hτae] with τ hsτ hτ
    refine Integrable.mono' (g := fun _ => 1 / τ) (integrable_const _) hsτ ?_
    refine (ae_restrict_iff' measurableSet_Ioc).2 (ae_of_all _ fun p hp => ?_)
    rw [Real.norm_of_nonneg (hnn τ hτ p hp)]
    simp only [hF]
    by_cases h : τ + p < 1
    · rw [if_pos h]
      have := (pgm_hh_bd (α := α) (x := x) hα hx0 hp.1 (by linarith [hτ.1] : p < p + τ) (by linarith)).2
      simpa using this
    · rw [if_neg h]; exact (one_div_pos.2 hτ.1).le
  · have heq : ∀ τ ∈ Ioc (0:ℝ) 1, ∫ y, ‖F (τ, y)‖ ∂μ = profC α x τ := by
      intro τ hτ
      have e1 : ∫ y, ‖F (τ, y)‖ ∂μ = ∫ y in Ioc (0:ℝ) 1, F (τ, y) := by
        rw [hμ]
        exact setIntegral_congr_fun measurableSet_Ioc (fun y hy => Real.norm_of_nonneg (hnn τ hτ y hy))
      rw [e1]
      have := pgm_inner_sum (G := fun p => (profF α x (p + τ) - profF α x p) / τ *
          Real.sqrt (profU α p / profU α (p + τ))) hτ.1.le hτ.2
      unfold profC
      rw [← this]
    refine Integrable.mono' (g := fun _ => (1:ℝ)) (integrable_const _)
      hmeas.norm.integral_prod_right' ?_
    have hτae : ∀ᵐ τ ∂μ, τ ∈ Ioo (0:ℝ) 1 := by
      rw [hμ, Measure.restrict_congr_set Ioo_ae_eq_Ioc.symm]
      exact ae_restrict_mem measurableSet_Ioo
    filter_upwards [hτae] with τ hτ
    have h0 : 0 ≤ ∫ y, ‖F (τ, y)‖ ∂μ := integral_nonneg (fun _ => norm_nonneg _)
    rw [Real.norm_of_nonneg h0, heq τ ⟨hτ.1, hτ.2.le⟩]
    exact pgm_C_le_one hα hx0 hτ.1 hτ.2

private lemma pgm_inner_eq {α x : ℝ} (hx : 0 < x) (p : ℝ) :
    ∫ τ in (0:ℝ)..(1 - p), (profF α x (p + τ) - profF α x p) / τ *
          Real.sqrt (profU α p / profU α (p + τ)) = x ^ α * ∫ q in p..1,
      (profF α x q - profF α x p) / (q - p) * Real.sqrt (profU α p / profU α q) / x ^ α := by
  have hs : 0 < x ^ α := Real.rpow_pos_of_pos hx α
  have := intervalIntegral.integral_comp_sub_right (fun τ => (profF α x (p + τ) - profF α x p) / τ *
          Real.sqrt (profU α p / profU α (p + τ))) (a := p) (b := 1) p
  simp only [sub_self] at this
  rw [← this, ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr (fun q _ => ?_)
  simp only [add_sub_cancel]
  field_simp

private lemma pgm_Gamma_eq {α x : ℝ} (hα : 0 < α) (hx : 0 < x) :
    profGamma α x = 2 * x ^ α * ∫ p in (0:ℝ)..1, ∫ q in p..1,
      (profF α x q - profF α x p) / (q - p) * Real.sqrt (profU α p / profU α q) / x ^ α := by
  have hs : 0 < x ^ α := Real.rpow_pos_of_pos hx α
  have hsw := pgm_swap_sum (G := fun τ p => (profF α x (p + τ) - profF α x p) / τ *
          Real.sqrt (profU α p / profU α (p + τ))) (pgm_Gam_int hα hx)
  unfold profGamma profC
  rw [hsw]
  simp only [pgm_inner_eq hx]
  rw [intervalIntegral.integral_const_mul]
  ring

private lemma pgm_Hc_outer {α x : ℝ} (hα : 0 < α) (hx : 0 < x) :
    IntervalIntegrable (fun p => ∫ q in p..1,
      (profF α x q - profF α x p) / (q - p) * Real.sqrt (profU α p / profU α q) / x ^ α)
      volume 0 1 := by
  have hs : 0 < x ^ α := Real.rpow_pos_of_pos hx α
  have hR := (pgm_Gam_int hα hx).integral_prod_right
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
  have h2 : IntegrableOn (fun p => x ^ α * ∫ q in p..1,
      (profF α x q - profF α x p) / (q - p) * Real.sqrt (profU α p / profU α q) / x ^ α)
      (Ioc (0:ℝ) 1) := by
    refine hR.congr ?_
    refine (ae_restrict_iff' measurableSet_Ioc).2 (ae_of_all _ fun p hp => ?_)
    have := pgm_inner_sum (G := fun τ => (profF α x (p + τ) - profF α x p) / τ *
          Real.sqrt (profU α p / profU α (p + τ))) hp.1.le hp.2
    show (∫ τ in Ioc (0:ℝ) 1, if τ + p < 1 then (profF α x (p + τ) - profF α x p) / τ *
          Real.sqrt (profU α p / profU α (p + τ)) else 0) = _
    simp only [show ∀ τ : ℝ, (τ + p < 1) = (p + τ < 1) from fun τ => by rw [add_comm]]
    exact this.trans (pgm_inner_eq hx p)
  refine (Integrable.const_mul h2 (x ^ α)⁻¹).congr ?_
  refine (ae_restrict_iff' measurableSet_Ioc).2 (ae_of_all _ fun p _ => ?_)
  field_simp

private lemma pgm_Hc_inner {α x p : ℝ} (hα : 0 < α) (hx : 0 < x) (hp : 0 < p) (hp1 : p < 1) :
    IntervalIntegrable (fun q => (profF α x q - profF α x p) / (q - p) *
      Real.sqrt (profU α p / profU α q) / x ^ α) volume p 1 := by
  have hs : 0 < x ^ α := Real.rpow_pos_of_pos hx α
  obtain ⟨c, C, hc, hC, hT⟩ := lem_app_pl_continuum_ii hα
  have hT' : ∀ V : ℝ, 0 < V → c * (contS α V * (1 - contS α V)) ≤ Tcont α V :=
    fun V hV => (hT V hV).1
  have hp' : p ∈ Ioo (0:ℝ) 1 := ⟨hp, hp1⟩
  have h1p : 0 < 1 - p := by linarith
  set m := min c 1 with hm
  have hm0 : 0 < m := lt_min hc one_pos
  set B := Real.sqrt ((1 - p) / (p * contV α p)) * Real.sqrt ((1 - p) / (p * contV α p)) *
    (2 / (m * (1 - p) ^ 2)) with hB
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hp1.le, integrableOn_Ioc_iff_integrableOn_Ioo]
  have hcont : ContinuousOn (fun q => (profF α x q - profF α x p) / (q - p) *
      Real.sqrt (profU α p / profU α q) / x ^ α) (Ioo p 1) := by
    have sub : Ioo p 1 ⊆ Ioo (0:ℝ) 1 := fun q hq => ⟨by linarith [hq.1], hq.2⟩
    have cF := (pgm_profF_cont hα hx).mono sub
    have cU := (pgm_profU_cont hα).mono sub
    refine (((cF.sub continuousOn_const).div (continuousOn_id.sub continuousOn_const)
      (fun q hq => (sub_pos.2 hq.1).ne')).mul
      (Real.continuous_sqrt.comp_continuousOn (continuousOn_const.div cU ?_))).div_const _
    intro q hq
    have h := sub hq
    have hV := (prof_contV_spec hα h).1
    unfold profU
    have : 0 < 1 - q := by linarith [h.2]
    have := h.1
    positivity
  refine Integrable.mono' (g := fun _ => B) (integrable_const _)
    (hcont.aestronglyMeasurable measurableSet_Ioo) ?_
  refine (ae_restrict_iff' measurableSet_Ioo).2 (ae_of_all _ fun q hq => ?_)
  have hq1 : q < 1 := hq.2
  rw [pgm_h_conc hα hx hp hq.1 hq1]
  have h1 := pgm_w_nonneg hα hx (x := x) hp.le hp1.le
  have h2 := pgm_w_nonneg hα hx (x := x) (by linarith [hq.1] : 0 ≤ q) hq1.le
  have hD1 := pgm_D_one_le hα hp hq.1 hq1
  have hD0 : 0 ≤ q * (contV α q - contV α p) / ((1 - p) * contV α q * (q - p)) :=
    le_trans zero_le_one hD1
  rw [Real.norm_of_nonneg (by positivity)]
  have hq' : q ∈ Ioo (0:ℝ) 1 := ⟨by linarith [hq.1], hq1⟩
  have hwq : Real.sqrt ((1 - q) / (q * contV α q)) * profF α x q ≤
      Real.sqrt ((1 - p) / (p * contV α p)) :=
    (pgm_w_le_g hα hx hq').trans (pgm_g_anti hα hp hq.1.le hq1)
  have hwp : Real.sqrt ((1 - p) / (p * contV α p)) * profF α x p ≤
      Real.sqrt ((1 - p) / (p * contV α p)) := pgm_w_le_g hα hx hp'
  have hD : q * (contV α q - contV α p) / ((1 - p) * contV α q * (q - p)) ≤ 2 / (m * (1 - p) ^ 2) := by
    rcases le_total q ((1 + p) / 2) with hq2 | hq2
    · refine (pgm_D_le_el hα hc hT' hp hq.1 hq1).trans ?_
      have h1q : 0 < 1 - q := by linarith
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have : (1 - p) / 2 ≤ 1 - q := by linarith
      have hmc : m ≤ c := min_le_left _ _
      nlinarith [mul_le_mul hmc this (by positivity) hc.le, mul_pos h1p h1p, mul_pos hc h1p]
    · refine (pgm_D_le_diag hα hp hq.1 hq1).trans ?_
      have hqp : 0 < q - p := by linarith [hq.1]
      have hm1 : m ≤ 1 := min_le_right _ _
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have : (1 - p) / 2 ≤ q - p := by linarith
      nlinarith [mul_pos h1p h1p, mul_pos h1p hqp, mul_le_mul_of_nonneg_left this h1p.le,
        mul_pos hm0 h1p, mul_pos (mul_pos hm0 h1p) h1p]
  have hg0 := Real.sqrt_nonneg ((1 - p) / (p * contV α p))
  calc _ ≤ (Real.sqrt ((1 - p) / (p * contV α p)) * Real.sqrt ((1 - p) / (p * contV α p))) *
        (q * (contV α q - contV α p) / ((1 - p) * contV α q * (q - p))) :=
        mul_le_mul_of_nonneg_right (mul_le_mul hwp hwq h2 hg0) hD0
    _ ≤ B := mul_le_mul_of_nonneg_left hD (by positivity)

private lemma pgm_main {α η R : ℝ} (hα : 0 < α) (hη0 : 0 < η) (hη : η ≤ 1 / 2) (hR : 1 < R) :
    ∃ C0 K KT : ℝ, 0 ≤ C0 ∧ 0 ≤ K ∧ 0 ≤ KT ∧ ∀ x : ℝ, 0 < x → x ≤ 1 →
      x ^ α * (∫ p in (0:ℝ)..1, Real.sqrt ((1 - p) / (p * contV α p)) * profF α x p) ^ 2 ≤
          profGamma α x ∧
      profGamma α x ≤ x ^ α * (1 / ((1 - η) * (1 - 1 / R)) *
          (∫ p in (0:ℝ)..1, Real.sqrt ((1 - p) / (p * contV α p)) * profF α x p) ^ 2 +
        2 * C0 * (R - 1) * (∫ p in (0:ℝ)..(η / 2), 1 / (contV α p + x ^ α)) +
        8 * (∫ p in (0:ℝ)..1, Real.sqrt ((1 - p) / (p * contV α p)) * profF α x p) * KT + 2 * K) := by
  obtain ⟨c, C, hc, hC, hT⟩ := lem_app_pl_continuum_ii hα
  have hT' : ∀ V : ℝ, 0 < V → c * (contS α V * (1 - contS α V)) ≤ Tcont α V :=
    fun V hV => (hT V hV).1
  have hη1 : η < 1 := by linarith
  have hη2 : η / 2 < 1 := by linarith
  obtain ⟨K, hK0, hK⟩ := pgm_R5 hα hc hT' (a := η / 2) (by linarith) hη2
  obtain ⟨C1, hC1, hw⟩ := pgm_w_end hα hη0 hη1
  refine ⟨4 / c, K, C1, by positivity, hK0, hC1.le, ?_⟩
  intro x hx hx1
  have hs : 0 < x ^ α := Real.rpow_pos_of_pos hx α
  have hR0 : 0 < R := by linarith
  have hLpos : 0 < (1 - η) * (1 - 1 / R) := by
    have : 0 < 1 - 1 / R := by rw [sub_pos, div_lt_one hR0]; exact hR
    have : 0 < 1 - η := by linarith
    positivity
  have hL1 : 1 ≤ 1 / ((1 - η) * (1 - 1 / R)) := by
    rw [le_div_iff₀ hLpos]
    have : 0 < 1 / R := by positivity
    nlinarith
  have hwi := lem_app_pl_Psi_i_integrable hα x ⟨hx, hx1⟩
  have hsk := pgm_skel (w := fun p => Real.sqrt ((1 - p) / (p * contV α p)) * profF α x p)
    (g := fun p => Real.sqrt ((1 - p) / (p * contV α p)))
    (e := fun p => 1 / (contV α p + x ^ α))
    (H := fun p q => (profF α x q - profF α x p) / (q - p) * Real.sqrt (profU α p / profU α q) / x ^ α)
    (η := η) (R := R) (L := 1 / ((1 - η) * (1 - 1 / R))) (C0 := 4 / c) (K := K)
    hη0 hη1 hR.le hL1 (by positivity) hK0
    (fun p hp0 hp1 => pgm_w_nonneg hα hx hp0 hp1) hwi
    (fun p q hp hpq hq => (pgm_w_le_g hα hx ⟨by linarith, hq⟩).trans (pgm_g_anti hα hp hpq hq))
    (fun p hp0 hp1 => pgm_Hc_inner hα hx hp0 hp1) (pgm_Hc_outer hα hx)
    (fun p q hp hpq hq => pgm_R1 hα hx hp hpq hq)
    (fun p q hp hpq hq => pgm_R2 hα hx hc hT' hη hp hpq hq)
    (fun p q hp hRq hpq hq => pgm_R3 hα hx hR hη1 hp hRq hpq hq)
    (fun p q hp hpη hηq hq => pgm_R4 hα hx hη1 hp hpη hηq hq)
    (fun p q hp hpq hq => hK x hx p q hp hpq hq)
    (fun p hp0 hpη => pgm_pgw hα hx ⟨hp0, by linarith⟩)
    (pgm_e_int hα hx (by linarith) hη2)
  obtain ⟨hlow, hup⟩ := hsk
  have hM0 : 0 ≤ ∫ p in (0:ℝ)..1, Real.sqrt ((1 - p) / (p * contV α p)) * profF α x p :=
    intervalIntegral.integral_nonneg zero_le_one (fun p hp => pgm_w_nonneg hα hx hp.1 hp.2)
  have hT0 : 0 ≤ ∫ q in η..1, Real.sqrt ((1 - q) / (q * contV α q)) * profF α x q :=
    intervalIntegral.integral_nonneg hη1.le (fun p hp => pgm_w_nonneg hα hx (by linarith [hp.1]) hp.2)
  have hTb : ∫ q in η..1, Real.sqrt ((1 - q) / (q * contV α q)) * profF α x q ≤ C1 := by
    have := intervalIntegral.integral_mono_on_of_le_Ioo (a := η) (b := 1)
      (f := fun q => Real.sqrt ((1 - q) / (q * contV α q)) * profF α x q) (g := fun _ => C1) hη1.le
      (hwi.mono_set (by rw [Set.uIcc_of_le hη1.le, Set.uIcc_of_le zero_le_one]; exact Set.Icc_subset_Icc hη0.le le_rfl))
      intervalIntegrable_const (fun q hq => by
        have := hw x hx q ⟨by linarith [hq.1], hq.2⟩ hq.1.le
        nlinarith [hq.1, hη0])
    simp only [intervalIntegral.integral_const, smul_eq_mul] at this
    nlinarith
  rw [pgm_Gamma_eq hα hx]
  set M := ∫ p in (0:ℝ)..1, Real.sqrt ((1 - p) / (p * contV α p)) * profF α x p with hM
  set J := ∫ p in (0:ℝ)..1, ∫ q in p..1, (profF α x q - profF α x p) / (q - p) *
    Real.sqrt (profU α p / profU α q) / x ^ α with hJ
  set E := ∫ p in (0:ℝ)..(η / 2), 1 / (contV α p + x ^ α) with hE
  set T := ∫ q in η..1, Real.sqrt ((1 - q) / (q * contV α q)) * profF α x q with hTT
  constructor
  · nlinarith
  · have h8 : M * T ≤ M * C1 := mul_le_mul_of_nonneg_left hTb hM0
    nlinarith

private lemma pgm_V_ge_lt {α p : ℝ} (hα : 0 < α) (hα1 : α < 1) (hp : p ∈ Ioo (0:ℝ) 1) :
    (1 - α) * p ≤ contV α p := by
  have hV := prof_contV_spec hα hp
  have h1 : contS α (contV α p) ≤ contV α p * (1 / (1 - α)) := by
    have hrp : ∫ t in (0:ℝ)..1, t ^ (-α) = 1 / (1 - α) := by
      rw [integral_rpow (Or.inl (by linarith))]
      have : -α + 1 ≠ 0 := by linarith
      simp [Real.zero_rpow this]
      ring_nf
    rw [← hrp, ← intervalIntegral.integral_const_mul]
    unfold contS
    apply intervalIntegral.integral_mono_on_of_le_Ioo zero_le_one (prof_cont_on hα hV.1).intervalIntegrable
      ((intervalIntegral.intervalIntegrable_rpow' (by linarith)).const_mul _)
    intro t ht
    have h0 : 0 < t ^ α := Real.rpow_pos_of_pos ht.1 α
    rw [Real.rpow_neg ht.1.le]
    rw [← div_eq_mul_inv]
    exact div_le_div_of_nonneg_left hV.1.le h0 (by linarith)
  rw [hV.2] at h1
  have hm : 0 < 1 - α := by linarith
  rw [← div_eq_mul_one_div, le_div_iff₀ hm] at h1
  linarith

private lemma pgm_E_lt {α x a : ℝ} (hα : 0 < α) (hα1 : α < 1) (hx : 0 < x) (hx1 : x ≤ 1)
    (ha0 : 0 < a) (ha1 : a < 1) :
    ∫ p in (0:ℝ)..a, 1 / (contV α p + x ^ α) ≤
      (1 / (1 - α)) * (α * Real.log (1 / x) + Real.log 2) := by
  have hs : 0 < x ^ α := Real.rpow_pos_of_pos hx α
  have hs1 : x ^ α ≤ 1 := Real.rpow_le_one hx.le hx1 hα.le
  have hk : 0 < 1 - α := by linarith
  have hmono : ∫ p in (0:ℝ)..a, 1 / (contV α p + x ^ α) ≤
      ∫ p in (0:ℝ)..a, ((1 - α) * p + x ^ α)⁻¹ := by
    apply intervalIntegral.integral_mono_on_of_le_Ioo ha0.le (pgm_e_int hα hx ha0.le ha1)
    · apply ContinuousOn.intervalIntegrable
      apply ContinuousOn.inv₀ (by fun_prop)
      intro p hp
      rw [Set.uIcc_of_le ha0.le] at hp
      have := hp.1
      positivity
    · intro p hp
      have hV := pgm_V_ge_lt hα hα1 ⟨hp.1, by linarith [hp.2]⟩
      rw [one_div]
      apply inv_anti₀ (by have := hp.1; positivity)
      linarith
  have hcomp := intervalIntegral.integral_comp_mul_add (a := 0) (b := a) (fun y : ℝ => y⁻¹) hk.ne' (x ^ α)
  simp only [mul_zero, zero_add, smul_eq_mul] at hcomp
  rw [integral_inv_of_pos hs (by positivity)] at hcomp
  have hlog : Real.log (((1 - α) * a + x ^ α) / x ^ α) ≤ α * Real.log (1 / x) + Real.log 2 := by
    rw [← Real.log_rpow (by positivity : (0:ℝ) < 1 / x) α, ← Real.log_mul (by positivity) (by norm_num)]
    apply Real.log_le_log (by positivity)
    rw [div_le_iff₀ hs, Real.div_rpow zero_le_one hx.le, Real.one_rpow]
    have : (1 / x ^ α) * x ^ α = 1 := by field_simp
    nlinarith [mul_pos hk ha0]
  calc _ ≤ _ := hmono
    _ = (1 - α)⁻¹ * Real.log (((1 - α) * a + x ^ α) / x ^ α) := hcomp
    _ ≤ (1 - α)⁻¹ * (α * Real.log (1 / x) + Real.log 2) :=
        mul_le_mul_of_nonneg_left hlog (by positivity)
    _ = _ := by ring

private lemma pgm_logsq {y : ℝ} (hy : 1 ≤ y) : Real.log y ^ 2 ≤ 4 * y := by
  have h := Real.log_le_rpow_div (x := y) (ε := 1 / 2) (by linarith) (by norm_num)
  have hl : 0 ≤ Real.log y := Real.log_nonneg hy
  have e : y ^ (1 / 2 : ℝ) = Real.sqrt y := (Real.sqrt_eq_rpow y).symm
  rw [e] at h
  have h2 : Real.log y ≤ 2 * Real.sqrt y := by linarith
  have := Real.sq_sqrt (by linarith : 0 ≤ y)
  nlinarith [Real.sqrt_nonneg y]

private lemma pgm_V_ge_one {p : ℝ} (hp0 : 0 < p) (hp : p ≤ 1 / 2) :
    p ≤ 8 * (1 + Real.log (1 / p)) * contV 1 p := by
  have hp' : p ∈ Ioo (0:ℝ) 1 := ⟨hp0, by linarith⟩
  have hV := prof_contV_spec (α := 1) one_pos hp'
  have hV0 := hV.1
  have hkey : p = contV 1 p * Real.log (1 + 1 / contV 1 p) := by
    have := (lem_app_pl_continuum_i_one.1 (contV 1 p) hV0)
    rw [hV.2] at this
    exact this
  have hVle : contV 1 p ≤ 1 := by
    have := prof_V_mul_le (α := 1) one_pos hp'
    nlinarith
  set V := contV 1 p with hVdef
  set L := Real.log (1 + 1 / V) with hL
  have hy1 : 0 < 1 / V := by positivity
  have hy : 1 ≤ 1 + 1 / V := by linarith
  have hL2 : L ^ 2 ≤ 4 * (1 + 1 / V) := pgm_logsq hy
  have hp2 : p ^ 2 ≤ 8 * V := by
    have : p ^ 2 = V ^ 2 * L ^ 2 := by rw [hkey]; ring
    have h3 : V ^ 2 * L ^ 2 ≤ V ^ 2 * (4 * (1 + 1 / V)) := mul_le_mul_of_nonneg_left hL2 (by positivity)
    have h4 : V ^ 2 * (4 * (1 + 1 / V)) = 4 * V ^ 2 + 4 * V := by field_simp
    nlinarith
  have hLle : L ≤ 8 * (1 + Real.log (1 / p)) := by
    have h1 : 1 + 1 / V ≤ 9 / p ^ 2 := by
      have : 1 / V ≤ 8 / p ^ 2 := by
        rw [div_le_div_iff₀ hV0 (by positivity)]; nlinarith
      have h5 : 1 ≤ 1 / p ^ 2 := by
        rw [le_div_iff₀ (by positivity)]; nlinarith
      have h9 : 9 / p ^ 2 = 1 / p ^ 2 + 8 / p ^ 2 := by ring
      linarith
    have h2 : L ≤ Real.log (9 / p ^ 2) := Real.log_le_log (by positivity) h1
    rw [Real.log_div (by norm_num) (by positivity), Real.log_pow] at h2
    have h9 : Real.log 9 ≤ 8 := by linarith [Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 9)]
    have h6 : Real.log p = - Real.log (1 / p) := by rw [one_div, Real.log_inv]; ring
    have h7 : 0 ≤ Real.log (1 / p) := Real.log_nonneg (by rw [le_div_iff₀ hp0]; linarith)
    push_cast at h2
    nlinarith
  calc p = V * L := hkey
    _ ≤ V * (8 * (1 + Real.log (1 / p))) := mul_le_mul_of_nonneg_left hLle hV0.le
    _ = _ := by ring

private lemma pgm_E_one {x a : ℝ} (hx : 0 < x) (hxa : x ≤ a) (ha : a ≤ 1 / 2) :
    ∫ p in (0:ℝ)..a, 1 / (contV 1 p + x ^ (1:ℝ)) ≤ 1 + 4 * (1 - Real.log x) ^ 2 := by
  have ha0 : 0 < a := lt_of_lt_of_le hx hxa
  have ha1 : a < 1 := by linarith
  rw [Real.rpow_one]
  have hi := pgm_e_int (α := 1) (x := x) one_pos hx ha0.le ha1
  simp only [Real.rpow_one] at hi
  have hi1 : IntervalIntegrable (fun p => 1 / (contV 1 p + x)) volume 0 x :=
    hi.mono_set (by rw [Set.uIcc_of_le hx.le, Set.uIcc_of_le ha0.le]; exact Set.Icc_subset_Icc le_rfl hxa)
  have hi2 : IntervalIntegrable (fun p => 1 / (contV 1 p + x)) volume x a :=
    hi.mono_set (by rw [Set.uIcc_of_le hxa, Set.uIcc_of_le ha0.le]; exact Set.Icc_subset_Icc hx.le le_rfl)
  rw [← intervalIntegral.integral_add_adjacent_intervals hi1 hi2]
  have part1 : ∫ p in (0:ℝ)..x, 1 / (contV 1 p + x) ≤ 1 := by
    have := intervalIntegral.integral_mono_on_of_le_Ioo (a := 0) (b := x) (f := fun p => 1 / (contV 1 p + x))
      (g := fun _ => 1 / x) hx.le hi1 intervalIntegrable_const (fun p hp => by
        have hV := (prof_contV_spec (α := 1) one_pos ⟨hp.1, by linarith [hp.2]⟩).1
        exact one_div_le_one_div_of_le hx (by linarith))
    simp only [intervalIntegral.integral_const, smul_eq_mul] at this
    rw [sub_zero, mul_one_div_cancel hx.ne'] at this
    exact this
  have hderiv : ∀ p ∈ Set.uIcc x a, HasDerivAt (fun p : ℝ => -(4 * (1 - Real.log p) ^ 2))
      (8 * (1 - Real.log p) / p) p := by
    intro p hp
    rw [Set.uIcc_of_le hxa] at hp
    have hp0 : 0 < p := lt_of_lt_of_le hx hp.1
    have h1 := ((Real.hasDerivAt_log hp0.ne').const_sub 1).pow 2
    have h2 := h1.const_mul 4 |>.neg
    convert h2 using 1
    field_simp
    ring
  have hint : IntervalIntegrable (fun p : ℝ => 8 * (1 - Real.log p) / p) volume x a := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hxa]
    have hne : ∀ p ∈ Set.Icc x a, p ≠ 0 := fun p hp => (lt_of_lt_of_le hx hp.1).ne'
    exact (continuousOn_const.mul (continuousOn_const.sub (Real.continuousOn_log.mono (fun p hp => hne p hp)))).div
      continuousOn_id hne
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  have part2 : ∫ p in x..a, 1 / (contV 1 p + x) ≤ 4 * (1 - Real.log x) ^ 2 := by
    have hm := intervalIntegral.integral_mono_on_of_le_Ioo (a := x) (b := a) (f := fun p => 1 / (contV 1 p + x))
      (g := fun p => 8 * (1 - Real.log p) / p) hxa hi2 hint (fun p hp => by
        have hp0 : 0 < p := lt_of_lt_of_le hx hp.1.le
        have hV := (prof_contV_spec (α := 1) one_pos ⟨hp0, by linarith [hp.2]⟩).1
        have hb := pgm_V_ge_one hp0 (by linarith [hp.2])
        have hl : 1 + Real.log (1 / p) = 1 - Real.log p := by
          rw [one_div, Real.log_inv]; ring
        rw [hl] at hb
        calc 1 / (contV 1 p + x) ≤ 1 / contV 1 p := one_div_le_one_div_of_le hV (by linarith)
          _ ≤ 8 * (1 - Real.log p) / p := by
            rw [div_le_div_iff₀ hV hp0]; nlinarith)
    rw [hftc] at hm
    have hla : 0 ≤ (1 - Real.log a) ^ 2 := sq_nonneg _
    linarith
  linarith

private lemma pgm_lim_generic {F : Filter ℝ} {Λ E M : ℝ → ℝ} {A κ C0' K1 K2 : ℝ} {a d : ℕ}
    (hΛ : Tendsto Λ F atTop) (hE : ∀ᶠ x in F, 0 ≤ E x ∧ E x ≤ A * (1 + Λ x) ^ a)
    (hM : ∀ᶠ x in F, κ * Λ x ^ (a + d) ≤ M x ^ 2) (hMinf : Tendsto M F atTop)
    (hκ : 0 < κ) (hA : 0 ≤ A) (hC : 0 ≤ C0') (hK1 : 0 ≤ K1) (hK2 : 0 ≤ K2) (hd : 0 < d) :
    Tendsto (fun x => (C0' * E x + K1 * M x + K2) / M x ^ 2) F (𝓝 0) := by
  have hΛpow : Tendsto (fun x => Λ x ^ d) F atTop :=
    (tendsto_pow_atTop hd.ne').comp hΛ
  have h1 : Tendsto (fun x => (Λ x ^ d)⁻¹) F (𝓝 0) := tendsto_inv_atTop_zero.comp hΛpow
  have h2 : Tendsto (fun x => (M x)⁻¹) F (𝓝 0) := tendsto_inv_atTop_zero.comp hMinf
  have h3 : Tendsto (fun x => (Λ x)⁻¹) F (𝓝 0) := tendsto_inv_atTop_zero.comp hΛ
  -- bound
  have hbound : Tendsto (fun x => C0' * A * 2 ^ a / κ * (Λ x ^ d)⁻¹ + K1 * (M x)⁻¹ +
      K2 * (M x)⁻¹ * (M x)⁻¹) F (𝓝 0) := by
    have := ((h1.const_mul (C0' * A * 2 ^ a / κ)).add (h2.const_mul K1)).add
      ((h2.const_mul K2).mul h2)
    simpa using this
  refine squeeze_zero' ?_ ?_ hbound
  · filter_upwards [hMinf.eventually_gt_atTop 0, hE] with x hx hEx
    have : 0 ≤ C0' * E x + K1 * M x + K2 := by
      have := mul_nonneg hC hEx.1
      have := mul_nonneg hK1 hx.le
      linarith
    positivity
  · filter_upwards [hE, hM, hMinf.eventually_gt_atTop 1, hΛ.eventually_ge_atTop 1] with x hEx hMx hMx1 hΛx
    have hM0 : 0 < M x := by linarith
    have hM2 : 0 < M x ^ 2 := by positivity
    have hΛ0 : 0 < Λ x := by linarith
    have hpow : 0 < Λ x ^ (a + d) := by positivity
    have hX : E x / M x ^ 2 ≤ A * 2 ^ a / κ * (Λ x ^ d)⁻¹ := by
      have h1 : (1 + Λ x) ^ a ≤ 2 ^ a * Λ x ^ a := by
        rw [← mul_pow]
        exact pow_le_pow_left₀ (by linarith) (by linarith) a
      calc E x / M x ^ 2 ≤ A * (1 + Λ x) ^ a / (κ * Λ x ^ (a + d)) :=
            div_le_div₀ (by positivity) hEx.2 (by positivity) hMx
        _ ≤ A * (2 ^ a * Λ x ^ a) / (κ * Λ x ^ (a + d)) :=
            div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left h1 hA) (by positivity)
        _ = A * 2 ^ a / κ * (Λ x ^ d)⁻¹ := by
            rw [pow_add]; field_simp
    have e : (C0' * E x + K1 * M x + K2) / M x ^ 2 =
        C0' * (E x / M x ^ 2) + K1 * (M x)⁻¹ + K2 * (M x)⁻¹ * (M x)⁻¹ := by
      field_simp
    rw [e]
    have := mul_le_mul_of_nonneg_left hX hC
    have e2 : C0' * A * 2 ^ a / κ * (Λ x ^ d)⁻¹ = C0' * (A * 2 ^ a / κ * (Λ x ^ d)⁻¹) := by ring
    linarith

private lemma pgm_E_nonneg {α x a : ℝ} (hα : 0 < α) (hx : 0 < x) (ha0 : 0 < a) (ha1 : a < 1) :
    0 ≤ ∫ p in (0:ℝ)..a, 1 / (contV α p + x ^ α) := by
  have hs : 0 < x ^ α := Real.rpow_pos_of_pos hx α
  have := intervalIntegral.integral_mono_on_of_le_Ioo (a := 0) (b := a) (f := fun _ => (0:ℝ))
    (g := fun p => 1 / (contV α p + x ^ α)) ha0.le intervalIntegrable_const
    (pgm_e_int hα hx ha0.le ha1) (fun p hp => by
      have hV := (prof_contV_spec hα ⟨hp.1, by linarith [hp.2]⟩).1
      positivity)
  simpa using this

private lemma pgm_Lam_tendsto : Tendsto (fun x : ℝ => Real.log (1 / x)) (𝓝[>] 0) atTop := by
  simp only [one_div]
  exact Real.tendsto_log_atTop.comp tendsto_inv_nhdsGT_zero

private lemma pgm_M_eq {α x : ℝ} :
    (∫ p in (0:ℝ)..1, Real.sqrt ((1 - p) / (p * contV α p)) * profF α x p) = profPsi α x / c0 := by
  unfold profPsi
  field_simp [prof_c0_pos.ne']

private lemma pgm_lim_lt {α η C0' K1 K2 : ℝ} (hα : 0 < α) (hα1 : α < 1) (hη0 : 0 < η)
    (hη : η ≤ 1 / 2) (hC : 0 ≤ C0') (hK1 : 0 ≤ K1) (hK2 : 0 ≤ K2) :
    Tendsto (fun x : ℝ => (C0' * (∫ p in (0:ℝ)..(η / 2), 1 / (contV α p + x ^ α)) +
        K1 * (∫ p in (0:ℝ)..1, Real.sqrt ((1 - p) / (p * contV α p)) * profF α x p) + K2) /
      (∫ p in (0:ℝ)..1, Real.sqrt ((1 - p) / (p * contV α p)) * profF α x p) ^ 2)
      (𝓝[>] 0) (𝓝 0) := by
  simp only [pgm_M_eq]
  have hm : 0 < 1 - α := by linarith
  have hsq : 0 < Real.sqrt (1 - α) := Real.sqrt_pos.2 hm
  set κ1 := α / (2 * Real.sqrt (1 - α)) with hκ1
  have hκ1p : 0 < κ1 := by positivity
  have hequiv := lem_app_pl_Psi_ii_lt hα hα1
  have hlo : ∀ᶠ x in 𝓝[>] (0:ℝ), κ1 * Real.log (1 / x) ≤ profPsi α x / c0 := by
    have h := hequiv.isLittleO.def (c := 1 / 2) (by norm_num)
    filter_upwards [h, Ioo_mem_nhdsGT (zero_lt_one : (0:ℝ) < 1)] with x hx hx01
    have hx0 : 0 < x := hx01.1
    have hlog : Real.log (x ^ (-α)) = α * Real.log (1 / x) := by
      rw [Real.log_rpow hx0, one_div, Real.log_inv]; ring
    have hL : 0 ≤ Real.log (1 / x) := Real.log_nonneg (by rw [le_div_iff₀ hx0]; linarith [hx01.2])
    simp only [Pi.sub_apply, hlog] at hx
    have hv : 0 ≤ c0 / Real.sqrt (1 - α) * (α * Real.log (1 / x)) := by
      have := prof_c0_pos; positivity
    rw [Real.norm_of_nonneg hv, Real.norm_eq_abs] at hx
    have := (abs_le.1 hx).1
    rw [le_div_iff₀ prof_c0_pos]
    have e : κ1 * Real.log (1 / x) * c0 = (c0 / Real.sqrt (1 - α) * (α * Real.log (1 / x))) / 2 := by
      rw [hκ1]; field_simp
    rw [e]
    linarith
  have hMinf : Tendsto (fun x : ℝ => profPsi α x / c0) (𝓝[>] 0) atTop := by
    refine tendsto_atTop_mono' _ hlo ?_
    exact (pgm_Lam_tendsto.const_mul_atTop hκ1p)
  refine pgm_lim_generic (a := 1) (d := 1) (A := (α + Real.log 2) / (1 - α)) (κ := κ1 ^ 2)
    pgm_Lam_tendsto ?_ ?_ hMinf (by positivity) (by have := Real.log_nonneg (by norm_num : (1:ℝ) ≤ 2); positivity) hC hK1 hK2 one_pos
  · filter_upwards [Ioo_mem_nhdsGT (zero_lt_one : (0:ℝ) < 1)] with x hx
    have hη2 : η / 2 < 1 := by linarith
    refine ⟨pgm_E_nonneg hα hx.1 (by linarith) hη2, ?_⟩
    have := pgm_E_lt hα hα1 hx.1 hx.2.le (by linarith : 0 < η / 2) hη2
    have hL : 0 ≤ Real.log (1 / x) := Real.log_nonneg (by rw [le_div_iff₀ hx.1]; linarith [hx.2])
    have hl2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    rw [pow_one]
    calc _ ≤ _ := this
      _ = (α * Real.log (1 / x) + Real.log 2) / (1 - α) := by ring
      _ ≤ (α + Real.log 2) * (1 + Real.log (1 / x)) / (1 - α) :=
          div_le_div_of_nonneg_right (by nlinarith [mul_nonneg hl2 hL, hα.le]) hm.le
      _ = _ := by ring
  · filter_upwards [hlo, Ioo_mem_nhdsGT (zero_lt_one : (0:ℝ) < 1)] with x hx hx01
    have hL : 0 ≤ Real.log (1 / x) := Real.log_nonneg (by rw [le_div_iff₀ hx01.1]; linarith [hx01.2])
    have := pow_le_pow_left₀ (by positivity) hx 2
    calc κ1 ^ 2 * Real.log (1 / x) ^ (1 + 1) = (κ1 * Real.log (1 / x)) ^ 2 := by ring
      _ ≤ _ := this

private lemma pgm_lim_one {α η C0' K1 K2 : ℝ} (hα : α = 1) (hη0 : 0 < η)
    (hη : η ≤ 1 / 2) (hC : 0 ≤ C0') (hK1 : 0 ≤ K1) (hK2 : 0 ≤ K2) :
    Tendsto (fun x : ℝ => (C0' * (∫ p in (0:ℝ)..(η / 2), 1 / (contV α p + x ^ α)) +
        K1 * (∫ p in (0:ℝ)..1, Real.sqrt ((1 - p) / (p * contV α p)) * profF α x p) + K2) /
      (∫ p in (0:ℝ)..1, Real.sqrt ((1 - p) / (p * contV α p)) * profF α x p) ^ 2)
      (𝓝[>] 0) (𝓝 0) := by
  simp only [pgm_M_eq]
  have hequiv := lem_app_pl_Psi_ii_one hα
  subst hα
  have hlo : ∀ᶠ x in 𝓝[>] (0:ℝ), 1 / 3 * Real.log (1 / x) ^ (3 / 2 : ℝ) ≤ profPsi 1 x / c0 := by
    have h := hequiv.isLittleO.def (c := 1 / 2) (by norm_num)
    filter_upwards [h, Ioo_mem_nhdsGT (zero_lt_one : (0:ℝ) < 1)] with x hx hx01
    have hx0 : 0 < x := hx01.1
    have hL : 0 ≤ Real.log (1 / x) := Real.log_nonneg (by rw [le_div_iff₀ hx0]; linarith [hx01.2])
    have hv : 0 ≤ 2 / 3 * c0 * Real.log (1 / x) ^ (3 / 2 : ℝ) := by
      have := prof_c0_pos; positivity
    simp only [Pi.sub_apply] at hx
    rw [Real.norm_of_nonneg hv, Real.norm_eq_abs] at hx
    have := (abs_le.1 hx).1
    rw [le_div_iff₀ prof_c0_pos]
    nlinarith
  have hpow : Tendsto (fun x : ℝ => Real.log (1 / x) ^ (3 / 2 : ℝ)) (𝓝[>] 0) atTop :=
    (tendsto_rpow_atTop (by norm_num : (0:ℝ) < 3 / 2)).comp pgm_Lam_tendsto
  have hMinf : Tendsto (fun x : ℝ => profPsi 1 x / c0) (𝓝[>] 0) atTop :=
    tendsto_atTop_mono' _ hlo (hpow.const_mul_atTop (by norm_num : (0:ℝ) < 1 / 3))
  refine pgm_lim_generic (a := 2) (d := 1) (A := 5) (κ := 1 / 9)
    pgm_Lam_tendsto ?_ ?_ hMinf (by norm_num) (by norm_num) hC hK1 hK2 one_pos
  · filter_upwards [Ioo_mem_nhdsGT (by linarith : (0:ℝ) < η / 2)] with x hx
    have hη2 : η / 2 < 1 := by linarith
    refine ⟨pgm_E_nonneg one_pos hx.1 (by linarith) hη2, ?_⟩
    have := pgm_E_one hx.1 hx.2.le (by linarith)
    have hl : Real.log (1 / x) = - Real.log x := by rw [one_div, Real.log_inv]
    have hL : 0 ≤ Real.log (1 / x) := Real.log_nonneg (by rw [le_div_iff₀ hx.1]; linarith [hx.2])
    rw [hl] at hL ⊢
    have e : 1 - Real.log x = 1 + -Real.log x := by ring
    rw [e] at this
    nlinarith [sq_nonneg (-Real.log x), mul_nonneg hL hL]
  · filter_upwards [hlo, Ioo_mem_nhdsGT (zero_lt_one : (0:ℝ) < 1)] with x hx hx01
    have hL : 0 ≤ Real.log (1 / x) := Real.log_nonneg (by rw [le_div_iff₀ hx01.1]; linarith [hx01.2])
    have h0 : 0 ≤ 1 / 3 * Real.log (1 / x) ^ (3 / 2 : ℝ) := by positivity
    have := pow_le_pow_left₀ h0 hx 2
    have e : (Real.log (1 / x) ^ (3 / 2 : ℝ)) ^ 2 = Real.log (1 / x) ^ 3 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hL]
      norm_num
    calc (1 / 9 : ℝ) * Real.log (1 / x) ^ (2 + 1) = (1 / 3 * Real.log (1 / x) ^ (3 / 2 : ℝ)) ^ 2 := by
          rw [mul_pow, e]; ring
      _ ≤ _ := this

-- PGM-END

/-- `lem:app-pl-matching` (snapshot `cr-2026-10-23`): for `0 < α ≤ 1`, `Γ_α(x)` is equivalent to
`x^α Ψ_α(x)^2/c_0^2` as `x ↓ 0`. Statement verbatim:

\begin{lemma}[Continuum matching below and at one]\label{lem:app-pl-matching}
For $0<\alpha\le1$, $\Gamma_\alpha(x)\sim x^\alpha\Psi_\alpha(x)^2/c_0^2$ as $x\downarrow0$; with
\cref{lem:app-pl-Psi} this is the second equivalence of \cref{eqn:app-pl-bulk-small}.
\end{lemma}

\begin{equation}\label{eqn:app-pl-bulk-small}
\begin{gathered}
\Psi_\alpha(x)\sim\begin{cases}\dfrac{c_0}{\sqrt{1-\alpha}}\log(x^{-\alpha}),&\alpha<1,\\[6pt]
\dfrac23c_0\big[\log(1/x)\big]^{3/2},&\alpha=1,\\[6pt]
d_\alpha\sqrt{K_\alpha}\,x^{-(\alpha-1)/2},&\alpha>1,\end{cases}
\\
\Gamma_\alpha(x)\sim\begin{cases}\dfrac{x^\alpha\big[\log(x^{-\alpha})\big]^2}{1-\alpha},&\alpha<1,\\[6pt]
\dfrac49x\big[\log(1/x)\big]^3,&\alpha=1,\\[6pt]
\dfrac{4K_\alpha^2}{\alpha-1}\,x,&\alpha>1.\end{cases}
\end{gathered}
\end{equation} -/
theorem lem_app_pl_matching {α : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1) :
    IsEquivalent (𝓝[>] (0:ℝ)) (fun x : ℝ => profGamma α x)
      (fun x : ℝ => x ^ α * profPsi α x ^ 2 / c0 ^ 2) := by
  have hc0 := prof_c0_pos
  have hvnn : ∀ᶠ x in 𝓝[>] (0:ℝ), 0 ≤ x ^ α * profPsi α x ^ 2 / c0 ^ 2 := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    have : 0 < x := hx
    positivity
  refine prof_equiv_of_squeeze hvnn ?_
  intro ε hε0 hε1
  set η := min (1 / 2) (ε / 8) with hη
  set R := max 2 (8 / ε) with hR
  have hη0 : 0 < η := lt_min (by norm_num) (by positivity)
  have hηle : η ≤ 1 / 2 := min_le_left _ _
  have hηε : η ≤ ε / 8 := min_le_right _ _
  have hR1 : 1 < R := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  have hRε : 1 / R ≤ ε / 8 := by
    have hRpos : 0 < R := by linarith
    rw [div_le_div_iff₀ hRpos (by norm_num)]
    have : 8 / ε ≤ R := le_max_right _ _
    rw [div_le_iff₀ hε0] at this
    nlinarith
  obtain ⟨C0, K, KT, hC0, hK, hKT, hmain⟩ := pgm_main hα0 hη0 hηle hR1
  have hlim : Tendsto (fun x : ℝ => (2 * C0 * (R - 1) * (∫ p in (0:ℝ)..(η / 2), 1 / (contV α p + x ^ α)) +
        (8 * KT) * (∫ p in (0:ℝ)..1, Real.sqrt ((1 - p) / (p * contV α p)) * profF α x p) + 2 * K) /
      (∫ p in (0:ℝ)..1, Real.sqrt ((1 - p) / (p * contV α p)) * profF α x p) ^ 2)
      (𝓝[>] 0) (𝓝 0) := by
    have h0 : 0 ≤ 2 * C0 * (R - 1) := by
      have : 0 ≤ R - 1 := by linarith
      positivity
    rcases lt_or_eq_of_le hα1 with h | h
    · exact pgm_lim_lt hα0 h hη0 hηle h0 (by positivity) (by positivity)
    · exact pgm_lim_one h hη0 hηle h0 (by positivity) (by positivity)
  have hlt := (hlim.eventually (gt_mem_nhds (by linarith : (0:ℝ) < ε / 2)))
  filter_upwards [hlt, Ioo_mem_nhdsGT (zero_lt_one : (0:ℝ) < 1)] with x hx hx01
  have hx0 : 0 < x := hx01.1
  obtain ⟨hlow, hup⟩ := hmain x hx0 hx01.2.le
  have hΨ := lem_app_pl_Psi_i_pos hα0 x ⟨hx0, hx01.2.le⟩
  have hs : 0 < x ^ α := Real.rpow_pos_of_pos hx0 α
  rw [pgm_M_eq] at hlow hup hx
  set M := profPsi α x / c0 with hM
  have hM0 : 0 < M := by positivity
  have hv : x ^ α * profPsi α x ^ 2 / c0 ^ 2 = x ^ α * M ^ 2 := by
    rw [hM]; field_simp
  rw [hv]
  have hLε : 1 / ((1 - η) * (1 - 1 / R)) ≤ 1 + ε / 2 := by
    have hD : 1 - ε / 4 ≤ (1 - η) * (1 - 1 / R) := by nlinarith [mul_nonneg hη0.le (by positivity : (0:ℝ) ≤ 1 / R)]
    have hDp : 0 < 1 - ε / 4 := by linarith
    calc _ ≤ 1 / (1 - ε / 4) := one_div_le_one_div_of_le hDp hD
      _ ≤ 1 + ε / 2 := by
        rw [div_le_iff₀ hDp]; nlinarith
  set Err := (2 * C0 * (R - 1) * (∫ p in (0:ℝ)..(η / 2), 1 / (contV α p + x ^ α)) +
        (8 * KT) * M + 2 * K) / M ^ 2 with hErr
  have hnum : 2 * C0 * (R - 1) * (∫ p in (0:ℝ)..(η / 2), 1 / (contV α p + x ^ α)) +
        (8 * KT) * M + 2 * K = Err * M ^ 2 := by
    rw [hErr]; field_simp
  constructor
  · have : 0 ≤ x ^ α * M ^ 2 := by positivity
    nlinarith
  · have h1 : profGamma α x ≤ x ^ α * (1 / ((1 - η) * (1 - 1 / R)) * M ^ 2 + Err * M ^ 2) := by
      refine hup.trans (le_of_eq ?_)
      congr 1
      rw [← hnum]; ring
    have h2 : (1 / ((1 - η) * (1 - 1 / R)) + Err) * M ^ 2 ≤ (1 + ε) * M ^ 2 :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    nlinarith [mul_le_mul_of_nonneg_left h2 hs.le]

private lemma pgm_ae_ne (c : ℝ) : ∀ᵐ t ∂(volume : Measure ℝ), t ≠ c := by
  have h : ({c}ᶜ : Set ℝ) ∈ MeasureTheory.ae (volume : Measure ℝ) :=
    compl_mem_ae_iff.2 (measure_singleton c)
  exact h

private lemma pgm_profU_pos {α q : ℝ} (hα : 0 < α) (hq : q ∈ Ioo (0:ℝ) 1) : 0 < profU α q := by
  unfold profU
  have hV := (prof_contV_spec hα hq).1
  have h1 : 0 < 1 - q := by linarith [hq.2]
  exact div_pos hV (mul_pos hq.1 h1)

private lemma pgm_profF_xcont {α x y : ℝ} (hα : 0 < α) (hx : 0 < x) (hy : y ∈ Ioo (0:ℝ) 1) :
    ContinuousAt (fun x' : ℝ => profF α x' y) x := by
  unfold profF
  have hV := (prof_contV_spec hα hy).1
  have hs : 0 < x ^ α := Real.rpow_pos_of_pos hx α
  refine ContinuousAt.div continuousAt_const (continuousAt_const.add ?_) ?_
  · exact Real.continuousAt_rpow_const x α (Or.inl hx.ne')
  · exact (add_pos hV hs).ne'

private lemma pgm_diff_pos {α x p q : ℝ} (hα : 0 < α) (hx : 0 < x) (hp : 0 < p) (hpq : p < q)
    (hq : q < 1) : 0 < profF α x q - profF α x p := by
  have hp' : p ∈ Ioo (0:ℝ) 1 := ⟨hp, by linarith⟩
  have hq' : q ∈ Ioo (0:ℝ) 1 := ⟨by linarith, hq⟩
  have hVp := prof_contV_spec hα hp'
  have hVq := prof_contV_spec hα hq'
  have hlt := pgm_V_lt hα hp' hq' hpq
  have hs : 0 < x ^ α := Real.rpow_pos_of_pos hx α
  have h1 : 0 < contV α q + x ^ α := add_pos hVq.1 hs
  have h2 : 0 < contV α p + x ^ α := add_pos hVp.1 hs
  unfold profF
  rw [div_sub_div _ _ h1.ne' h2.ne']
  refine div_pos ?_ (mul_pos h1 h2)
  nlinarith [mul_pos hs (sub_pos.2 hlt)]

private lemma pgm_G_bd {α x τ p : ℝ} (hα : 0 < α) (hx : 0 < x) (hτ0 : 0 < τ) (hτ1 : τ < 1)
    (hp : p ∈ Ioo (0:ℝ) (1 - τ)) :
    ‖(profF α x (p + τ) - profF α x p) / τ * Real.sqrt (profU α p / profU α (p + τ))‖ ≤ 1 / τ := by
  have hq : p + τ < 1 := by linarith [hp.2]
  have hpq : p < p + τ := by linarith
  have h := pgm_hh_bd (α := α) (x := x) hα hx hp.1 hpq hq
  have e : p + τ - p = τ := by ring
  rw [e] at h
  rw [Real.norm_of_nonneg h.1]
  exact h.2

private lemma pgm_G_cont {α x τ : ℝ} (hα : 0 < α) (hx : 0 < x) (hτ0 : 0 < τ) (hτ1 : τ < 1) :
    ContinuousOn (fun p : ℝ => (profF α x (p + τ) - profF α x p) / τ *
      Real.sqrt (profU α p / profU α (p + τ))) (Ioo 0 (1 - τ)) := by
  have m : MapsTo (fun p : ℝ => p + τ) (Ioo 0 (1 - τ)) (Ioo 0 1) :=
    fun p hp => ⟨by linarith [hp.1], by linarith [hp.2]⟩
  have sub : Ioo (0:ℝ) (1 - τ) ⊆ Ioo 0 1 := fun p hp => ⟨hp.1, by linarith [hp.2]⟩
  have cF1 := (pgm_profF_cont hα hx).comp (by fun_prop : Continuous fun p : ℝ => p + τ).continuousOn m
  have cF2 := (pgm_profF_cont hα hx).mono sub
  have cU1 := (pgm_profU_cont hα).comp (by fun_prop : Continuous fun p : ℝ => p + τ).continuousOn m
  have cU2 := (pgm_profU_cont hα).mono sub
  refine ((cF1.sub cF2).div_const τ).mul (Real.continuous_sqrt.comp_continuousOn (cU2.div cU1 ?_))
  intro p hp
  exact (pgm_profU_pos hα (m hp)).ne'

private lemma pgm_C_pos {α x τ : ℝ} (hα : 0 < α) (hx : 0 < x) (hτ0 : 0 < τ) (hτ1 : τ < 1) :
    0 < profC α x τ := by
  unfold profC
  have hint : IntervalIntegrable (fun p => (profF α x (p + τ) - profF α x p) / τ *
      Real.sqrt (profU α p / profU α (p + τ))) volume 0 (1 - τ) := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith : (0:ℝ) ≤ 1 - τ),
      integrableOn_Ioc_iff_integrableOn_Ioo]
    refine Integrable.mono' (g := fun _ => 1 / τ) (integrable_const _)
      ((pgm_G_cont hα hx hτ0 hτ1).aestronglyMeasurable measurableSet_Ioo) ?_
    exact (ae_restrict_iff' measurableSet_Ioo).2 (ae_of_all _ fun p hp => pgm_G_bd hα hx hτ0 hτ1 hp)
  have hpos : ∀ p ∈ Ioo (0:ℝ) (1 - τ), 0 < (profF α x (p + τ) - profF α x p) / τ *
      Real.sqrt (profU α p / profU α (p + τ)) := by
    intro p hp
    have hq1 : p + τ < 1 := by linarith [hp.2]
    have hd := pgm_diff_pos hα hx hp.1 (by linarith : p < p + τ) hq1
    have hU1 := pgm_profU_pos hα (⟨hp.1, by linarith [hp.2]⟩ : p ∈ Ioo (0:ℝ) 1)
    have hU2 := pgm_profU_pos hα (⟨by linarith [hp.1], hq1⟩ : p + τ ∈ Ioo (0:ℝ) 1)
    exact mul_pos (div_pos hd hτ0) (Real.sqrt_pos.2 (div_pos hU1 hU2))
  exact intervalIntegral.intervalIntegral_pos_of_pos_on hint hpos (by linarith)

private lemma pgm_C_dct {α x0 τ : ℝ} (hα : 0 < α) (hx0 : 0 < x0) (hτ0 : 0 < τ) (hτ1 : τ < 1) :
    ContinuousWithinAt (fun x => profC α x τ) (Ioc 0 1) x0 := by
  unfold profC
  have hne := pgm_ae_ne (1 - τ)
  refine intervalIntegral.continuousWithinAt_of_dominated_interval
    (F := fun x p => (profF α x (p + τ) - profF α x p) / τ * Real.sqrt (profU α p / profU α (p + τ)))
    (bound := fun _ => 1 / τ) ?_ ?_ intervalIntegrable_const ?_
  · refine eventually_nhdsWithin_of_forall (fun x hx => ?_)
    rw [Set.uIoc_of_le (show (0:ℝ) ≤ 1 - τ by linarith), ← Measure.restrict_congr_set Ioo_ae_eq_Ioc]
    exact (pgm_G_cont hα hx.1 hτ0 hτ1).aestronglyMeasurable measurableSet_Ioo
  · refine eventually_nhdsWithin_of_forall (fun x hx => ?_)
    filter_upwards [hne] with p hpne hp
    rw [Set.uIoc_of_le (show (0:ℝ) ≤ 1 - τ by linarith)] at hp
    exact pgm_G_bd hα hx.1 hτ0 hτ1 ⟨hp.1, lt_of_le_of_ne hp.2 hpne⟩
  · filter_upwards [hne] with p hpne hp
    rw [Set.uIoc_of_le (show (0:ℝ) ≤ 1 - τ by linarith)] at hp
    have hp' : p ∈ Ioo (0:ℝ) (1 - τ) := ⟨hp.1, lt_of_le_of_ne hp.2 hpne⟩
    have hq1 : p + τ < 1 := by linarith [hp'.2]
    have hy1 : p ∈ Ioo (0:ℝ) 1 := ⟨hp'.1, by linarith [hp'.2]⟩
    have hy2 : p + τ ∈ Ioo (0:ℝ) 1 := ⟨by linarith [hp'.1], hq1⟩
    have c1 := pgm_profF_xcont hα hx0 hy2
    have c2 := pgm_profF_xcont hα hx0 hy1
    have c3 : ContinuousAt (fun _ : ℝ => Real.sqrt (profU α p / profU α (p + τ))) x0 :=
      continuousAt_const
    exact (((c1.sub c2).div_const τ).mul c3).continuousWithinAt

private lemma pgm_C_eq_int {α x τ : ℝ} (hτ : τ ∈ Ioc (0:ℝ) 1) :
    ∫ y in Ioc (0:ℝ) 1, (if τ + y < 1 then (profF α x (y + τ) - profF α x y) / τ *
        Real.sqrt (profU α y / profU α (y + τ)) else 0) = profC α x τ := by
  have := pgm_inner_sum (G := fun p => (profF α x (p + τ) - profF α x p) / τ *
      Real.sqrt (profU α p / profU α (p + τ))) hτ.1.le hτ.2
  unfold profC
  exact this

private lemma pgm_profC_meas {α x : ℝ} (hα : 0 < α) (hx : 0 < x) :
    AEStronglyMeasurable (fun τ : ℝ => profC α x τ) (volume.restrict (Ioc (0:ℝ) 1)) := by
  refine ((pgm_Gam_int hα hx).integral_prod_left.aestronglyMeasurable).congr ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with τ hτ
  exact pgm_C_eq_int hτ

private lemma pgm_Gam_cont_int {α x0 : ℝ} (hα : 0 < α) (hx0 : x0 ∈ Ioc (0:ℝ) 1) :
    ContinuousWithinAt (fun x => ∫ τ in (0:ℝ)..1, profC α x τ) (Ioc 0 1) x0 := by
  refine intervalIntegral.continuousWithinAt_of_dominated_interval
    (F := fun x τ => profC α x τ) (bound := fun _ => (1:ℝ)) ?_ ?_ intervalIntegrable_const ?_
  · refine eventually_nhdsWithin_of_forall (fun x hxI => ?_)
    rw [Set.uIoc_of_le zero_le_one]
    exact pgm_profC_meas hα hxI.1
  · refine eventually_nhdsWithin_of_forall (fun x hxI => ?_)
    filter_upwards [pgm_ae_ne 1] with τ hτ1 hτI
    show ‖profC α x τ‖ ≤ 1
    rw [Set.uIoc_of_le zero_le_one] at hτI
    have hτ : τ < 1 := lt_of_le_of_ne hτI.2 hτ1
    rw [Real.norm_of_nonneg (pgm_C_pos hα hxI.1 hτI.1 hτ).le]
    exact pgm_C_le_one hα hxI.1 hτI.1 hτ
  · filter_upwards [pgm_ae_ne 1] with τ hτ1 hτI
    rw [Set.uIoc_of_le zero_le_one] at hτI
    exact pgm_C_dct hα hx0.1 hτI.1 (lt_of_le_of_ne hτI.2 hτ1)

/-- Helper for `prop:app-pl-profiles` (snapshot `cr-2026-10-23`), the finiteness of the
Gamma profile's integrand: `C_{α,x}` is integrable on `(0,1)` for every `x ∈ (0,1]`. Source: the
proof of volatility (i), l.2264-2265 (promoted to a helper, not a labelled statement):

Positivity and continuity of $\Gamma_\alpha$ follow: $f_x$ is strictly increasing, so
$C_{\alpha,x}>0$, and the bounds above are locally uniform in $x$. -/
theorem lem_app_pl_Gamma_helper_integrable {α : ℝ} (hα : 0 < α) :
    ∀ x ∈ Ioc (0:ℝ) 1, IntervalIntegrable (fun τ : ℝ => profC α x τ) volume 0 1 := by
  intro x hx
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
  refine (pgm_Gam_int hα hx.1).integral_prod_left.congr ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with τ hτ
  exact pgm_C_eq_int hτ

/-- Helper for `prop:app-pl-profiles` (snapshot `cr-2026-10-23`), continuity of `Γ_α` on
`(0,1]`. Source: `section.tex` l.2264-2265 (promoted, not a labelled statement):

Positivity and continuity of $\Gamma_\alpha$ follow: $f_x$ is strictly increasing, so
$C_{\alpha,x}>0$, and the bounds above are locally uniform in $x$. -/
theorem lem_app_pl_Gamma_helper_cont {α : ℝ} (hα : 0 < α) :
    ContinuousOn (fun x : ℝ => profGamma α x) (Ioc 0 1) := by
  intro x0 hx0
  unfold profGamma
  exact (pgm_Gam_cont_int hα hx0).const_mul 2

/-- Helper for `prop:app-pl-profiles` (snapshot `cr-2026-10-23`), positivity of `Γ_α` on
`(0,1]`. Source: `section.tex` l.2264-2265 (promoted, not a labelled statement):

Positivity and continuity of $\Gamma_\alpha$ follow: $f_x$ is strictly increasing, so
$C_{\alpha,x}>0$, and the bounds above are locally uniform in $x$. -/
theorem lem_app_pl_Gamma_helper_pos {α : ℝ} (hα : 0 < α) :
    ∀ x ∈ Ioc (0:ℝ) 1, 0 < profGamma α x := by
  intro x hx
  unfold profGamma
  have hP := intervalIntegral.intervalIntegral_pos_of_pos_on
    (lem_app_pl_Gamma_helper_integrable hα x hx) (fun τ hτ => pgm_C_pos hα hx.1 hτ.1 hτ.2) zero_lt_one
  exact mul_pos two_pos hP

end Muon.PowerLaw
