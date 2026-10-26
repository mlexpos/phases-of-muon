import Muon.PowerLaw.Profiles
import Muon.PowerLaw.DriftAsymptotics
import Muon.PowerLaw.VolBulk
import Muon.PowerLaw.VolMeso
import Muon.PowerLaw.VolSuper
import Muon.PowerLaw.ZeroRidge
import Muon.PowerLaw.BranchLink
import Muon.PowerLaw.VolShell
import Muon.Volatility.LagKernel
import Muon.Drift.Defs

/-!
# Appendix G: main assemblies and negligible ridge (work package L-G.15)

Snapshot `cr-2026-10-23`. Source: `sections/06-power-law/section.tex`: `prop:app-pl-profiles`
(l.821-848), `thm:app-pl-triple` (l.866-872), `cor:app-pl-endpoints` (l.947-979),
`cor:app-pl-weighted` (l.1012-1019), `prop:app-pl-ridge` (l.1028-1040).

This module states the labels of L-G.15 only. Records of `thm:app-pl-drift` and
`thm:app-pl-volatility` belong to other packages and are used here through their part-form
declarations and through `ZeroRidge`.

Representation choices:

* `𝔡_i(0)` is `dZero` (`Participation`). `𝔳_i(0)` is `vZero` (`ZeroRidge`, the limit
  `def:app-pl-coefficients`, identified by `def_app_pl_coefficients_ii`). It takes the size
  constants `(γ⋆, C_Σ)` of D's admissible class as explicit arguments, with `zeroAdmissible`
  as the admissibility condition of `ZeroRidge`. The source states no such constants; the
  statements quantify over all admissible choices, which is the paper's implicit claim that
  the coefficient does not depend on them (see the open questions of the report).
* The discharges of the part-form hypotheses (`volHBound`, `volHPSD`, `volHZero`) are
  `prop_app_pl_vol_zero_hBound`, `_hPSD`, `_hZero` with the certificate `cert`; the statements
  below do not restate them.
* Ridge coefficients: `𝔡_i(ϱ)` is `dRidge` (`Muon.Drift.kernel` at `λ = 1`; spectral measures
  `ν, ν'` as in `BranchLink`), `𝔳_i(ϱ)` is `ridgeV` and `C̄_{i,ℓ}(ϱ)` is `ridgeC`, both
  `Muon.Volatility.rowVBar` / `lagRowBar` at `Σ_in = Id`, `ϱ = ϱ'`.
* Volatility statements of `thm:app-pl-volatility` that are uniform in the row are stated in
  the uniform form of `section.tex`-card §6 #1 (sup over compact sets), not the sequential form.
-/

open MeasureTheory Filter Topology Set Asymptotics
open Muon.DetEquiv

noncomputable section

namespace Muon.PowerLaw

/-- Admissible size constants of the zero-ridge coefficients: `γ ≤ γ⋆`, `μ_i ≤ C_Σ`, `1 ≤ C_Σ`
(the hypotheses of `ZeroRidge`). -/
def zeroAdmissible (N B : ℕ) (μ : Fin N → ℝ) (γstar CSig : ℝ) : Prop :=
  gammaOf N B ≤ γstar ∧ (∀ i, μ i ≤ CSig) ∧ 1 ≤ CSig

/-- `i_⋆` (snapshot `cr-2026-10-23`) of `cor:app-pl-endpoints`: `i_{c,𝔡}` for `α ≤ 1` and `i_c` for `α > 1`. -/
def icStar (β α : ℝ) (N B : ℕ) : ℝ :=
  if α ≤ 1 then icdIdx β α N B else icCross α B

/-- Ridge drift coefficient `𝔡_i(ϱ) = 𝔡(μ_i, 1)` (`eqn:app-drift-kernel` with `λ = 1`), with the
spectral measures `ν, ν'` as in `BranchLink`. -/
noncomputable def dRidge (β : ℝ) (ν ν' : FiniteMeasure ℝ) {N : ℕ} (μ : Fin N → ℝ) (i : Fin N)
    (ϱ : ℝ) : ℝ :=
  Muon.Drift.kernel (emaW β) ν ν' ϱ (μ i) 1

/-- Ridge row volatility `𝔳_i(ϱ) = 𝔳_i(ϱ,ϱ)` at `Σ_in = Id` (`eqn:app-vol-rows`). -/
noncomputable def ridgeV (cert : Muon.External.GaussianOpNorm) (γstar CSig : ℝ) (β : ℝ) (B : ℕ)
    {N : ℕ} (μ : Fin N → ℝ) (i : Fin N) (ϱ : ℝ) : ℝ :=
  Muon.Volatility.rowVBar cert γstar CSig β B μ (fun _ : Fin N => (1 : ℝ)) i ϱ ϱ

/-- Ridge lag coefficient `C̄_{i,ℓ}(ϱ) = C̄_{i,ℓ}(ϱ,ϱ)` at `Σ_in = Id` (`eqn:app-vol-rows`). -/
noncomputable def ridgeC (cert : Muon.External.GaussianOpNorm) (γstar CSig : ℝ) (β : ℝ) (ℓ B : ℕ)
    {N : ℕ} (μ : Fin N → ℝ) (i : Fin N) (ϱ : ℝ) : ℝ :=
  Muon.Volatility.lagRowBar cert γstar CSig β ℓ B μ (fun _ : Fin N => (1 : ℝ)) i ϱ ϱ

/-- `D_⋆ = max_i D_i` (snapshot `cr-2026-10-23`) (`eqn:app-pl-ridge-constants`, with `D_i` of `eqn:app-pl-finite-constants`
as `plDcoef`). -/
noncomputable def ridgeDstar (β : ℝ) (B : ℕ) {N : ℕ} (μ : Fin N → ℝ) (hN : 0 < N) : ℝ :=
  ⨆ i : Fin N, plDcoef β B μ hN i

/-- `z̄_N = min(z_1, 1)` (snapshot `cr-2026-10-23`) (`eqn:app-pl-ridge-constants`, with `z_1 = plZ1`). -/
noncomputable def ridgeZbar (β : ℝ) (B : ℕ) {N : ℕ} (μ : Fin N → ℝ) : ℝ :=
  min (plZ1 β B μ) 1

/-- `E_⋆ = A_N z̄_N^{-1/2} + 2√D_⋆ z̄_N^{1/4}` (snapshot `cr-2026-10-23`) (`eqn:app-pl-ridge-constants`, `A_N` of
`eqn:app-pl-A` as `plAN`). -/
noncomputable def ridgeEstar (β : ℝ) (B : ℕ) {N : ℕ} (μ : Fin N → ℝ) (hN : 0 < N) : ℝ :=
  plAN β B μ * ridgeZbar β B μ ^ (-(1 : ℝ) / 2) +
    2 * Real.sqrt (ridgeDstar β B μ hN) * ridgeZbar β B μ ^ ((1 : ℝ) / 4)

/-- The ridge admissibility of `prop:app-pl-ridge`: `0 < ϱ_N ≤ z̄_N`, `H_N ∈ ℕ`, and the three
limits of `eqn:app-pl-ridge-window`. -/
def ridgeWindow {α β : ℝ} {N B : ℕ → ℕ} {c : ℕ → ℝ} (R : assum_app_pl_regime α β N B c)
    (ϱ : ℕ → ℝ) (H : ℕ → ℕ) : Prop :=
  (∀ n, 0 < ϱ n ∧ ϱ n ≤ ridgeZbar β (B n) (plSpec α (c n) (N n))) ∧
  Tendsto (fun n => ϱ n * Qm β (gammaOf (N n) (B n)) /
      (c n * (N n : ℝ) ^ (-α) * gammaOf (N n) (B n) ^ 2)) atTop (𝓝 0) ∧
  Tendsto (fun n => (1 + (H n : ℝ)) *
      Real.sqrt (ridgeDstar β (B n) (plSpec α (c n) (N n)) (R.hNpos n)) *
      ϱ n ^ ((1 : ℝ) / 4)) atTop (𝓝 0) ∧
  Tendsto (fun n => ridgeEstar β (B n) (plSpec α (c n) (N n)) (R.hNpos n) *
      β ^ ((H n : ℝ) / 3)) atTop (𝓝 0)

/-- Drift well-posedness at the ridges `ϱ_N` (the integrability clause of `eqn:app-drift-kernel`):
for every row `i`, the integrand of `𝔡_i(ϱ_N) = 𝔡(μ_i, 1)` is integrable on `(0,∞)`. Stated in the
conclusion of every ridge statement that uses `dRidge`. -/
def ridgeDriftWellPosed {α β : ℝ} {N B : ℕ → ℕ} {c : ℕ → ℝ} (R : assum_app_pl_regime α β N B c)
    (ν ν' : ℕ → FiniteMeasure ℝ) (ϱ : ℕ → ℝ) : Prop :=
  ∀ (n : ℕ) (i : Fin (N n)), IntegrableOn (fun u : ℝ =>
      (ϱ n + u ^ 2) * Lw (emaW β) (Muon.Drift.branchQ (emaW β) (ν n) (ν' n) (ϱ n + u ^ 2)) *
          plSpec α (c n) (N n) i * 1 /
        ((ϱ n + u ^ 2 + (branchSol (Fw (emaW β)) (ν n) (ν' n) (ϱ n + u ^ 2)).2.2.1 *
            plSpec α (c n) (N n) i) *
          (ϱ n + u ^ 2 + (branchSol (Fw (emaW β)) (ν n) (ν' n) (ϱ n + u ^ 2)).2.2.2 * 1)))
      (Ioi 0)

/-- Volatility well-posedness at the ridges `ϱ_N`: each lag limit defining `C̄_{i,ℓ}(ϱ_N)` exists
(`eqn:app-vol-rows`, `eqn:app-vol-Phi`), and the lag series of `𝔳_i(ϱ_N)` is summable. Stated in
the conclusion of every ridge statement that uses `ridgeV` or `ridgeC`. -/
def ridgeVolWellPosed {α β : ℝ} {N B : ℕ → ℕ} {c : ℕ → ℝ} (R : assum_app_pl_regime α β N B c)
    (cert : Muon.External.GaussianOpNorm) (γstar CSig : ℕ → ℝ) (ϱ : ℕ → ℝ) : Prop :=
  (∀ (n : ℕ) (i : Fin (N n)) (ℓ : ℕ), ∃ L : ℝ, Tendsto (fun p : ℕ × ℝ =>
      Muon.Volatility.lagRespCut cert (γstar n) (CSig n) β ℓ p.1 p.2 (B n)
        (plSpec α (c n) (N n)) (fun _ : Fin (N n) => (1 : ℝ)) (Pi.single i 1)
        (fun _ : Fin (N n) => (1 : ℝ)) (Muon.Volatility.omegaF (ϱ n)) (Muon.Volatility.omegaF (ϱ n)))
      atTop (𝓝 L)) ∧
  (∀ (n : ℕ) (i : Fin (N n)), Summable (fun ℓ : ℕ =>
      ridgeC cert (γstar n) (CSig n) β (ℓ + 1) (B n) (plSpec α (c n) (N n)) i (ϱ n)))

private lemma profiles_gamma_lt {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) :
    IsEquivalent (𝓝[>] (0 : ℝ)) (fun x : ℝ => profGamma α x)
      (fun x : ℝ => x ^ α * Real.log (x ^ (-α)) ^ 2 / (1 - α)) := by
  have hc0 : 0 < c0 := by
    unfold c0
    exact Real.sqrt_pos.2 (by positivity)
  have h := ((IsEquivalent.refl (u := fun x : ℝ => x ^ α)).mul
    ((lem_app_pl_Psi_ii_lt hα0 hα1).pow 2)).div
      (IsEquivalent.refl (u := fun _ : ℝ => c0 ^ 2))
  refine (lem_app_pl_matching hα0 hα1.le).trans (h.trans_eventuallyEq ?_)
  filter_upwards [] with x
  change x ^ α * (c0 / Real.sqrt (1 - α) * Real.log (x ^ (-α))) ^ 2 / c0 ^ 2 = _
  rw [mul_pow, div_pow, Real.sq_sqrt (by linarith : 0 ≤ 1 - α)]
  field_simp [hc0.ne']

private lemma profiles_gamma_one {α : ℝ} (hα : α = 1) :
    IsEquivalent (𝓝[>] (0 : ℝ)) (fun x : ℝ => profGamma α x)
      (fun x : ℝ => 4 / 9 * x * Real.log (1 / x) ^ (3 : ℕ)) := by
  have hc0 : 0 < c0 := by
    unfold c0
    exact Real.sqrt_pos.2 (by positivity)
  have h := ((IsEquivalent.refl (u := fun x : ℝ => x ^ α)).mul
    ((lem_app_pl_Psi_ii_one hα).pow 2)).div
      (IsEquivalent.refl (u := fun _ : ℝ => c0 ^ 2))
  refine (lem_app_pl_matching (by linarith) hα.le).trans (h.trans_eventuallyEq ?_)
  filter_upwards [Ioo_mem_nhdsGT (zero_lt_one : (0 : ℝ) < 1)] with x hx
  have hlog : 0 ≤ Real.log (1 / x) := Real.log_nonneg (by
    rw [le_div_iff₀ hx.1]
    linarith [hx.2])
  have hpow : (Real.log (1 / x) ^ (3 / 2 : ℝ)) ^ 2 =
      Real.log (1 / x) ^ (3 : ℕ) := by
    rw [← Real.rpow_mul_natCast hlog]
    norm_num
  change x ^ α * (2 / 3 * c0 * Real.log (1 / x) ^ (3 / 2 : ℝ)) ^ 2 / c0 ^ 2 = _
  rw [hα, Real.rpow_one, mul_pow, mul_pow, hpow]
  field_simp [hc0.ne']
  ring

/-- `prop:app-pl-profiles`(i) (snapshot `cr-2026-10-23`). Statement (LaTeX, verbatim from sections/06-power-law/section.tex):

\begin{proposition}[The profiles]\label{prop:app-pl-profiles}
\leavevmode
\begin{enumerate}[label=(\roman*)]
\item $\Psi_\alpha$ and $\Gamma_\alpha$ are finite, positive and continuous on
$(0,1]$, $\Psi_\alpha$ is bounded below by a positive constant there, and as $x\downarrow0$
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
\end{equation}
\item For $\alpha>1$, $\Phi_{\alpha,\bmom}$ and $G_{\alpha,\bmom}$ are finite, positive and
continuous on $(0,\infty)$, and
\begin{equation}\label{eqn:app-pl-crossover-ends}
\begin{gathered}
\Phi_{\alpha,\bmom}(y)\sim\sqrt{y/\sw2}\ (y\to\infty),\quad
\Phi_{\alpha,\bmom}(y)\sim d_\alpha\,y^{\frac{\alpha-1}{2\alpha}}\ (y\downarrow0),\\
G_{\alpha,\bmom}(X)\to\frac1{\sw2}\ (X\downarrow0),\quad
G_{\alpha,\bmom}(X)\sim\frac{4K_\alpha}{\alpha-1}X\ (X\to\infty).
\end{gathered}
\end{equation}
\end{enumerate}
\end{proposition}
-/
theorem prop_app_pl_profiles_i {α : ℝ} (hα : 0 < α) :
    (∀ x ∈ Ioc (0 : ℝ) 1, IntervalIntegrable
      (fun p : ℝ => Real.sqrt ((1 - p) / (p * contV α p)) * profF α x p) volume 0 1) ∧
    (∀ x ∈ Ioc (0 : ℝ) 1, IntervalIntegrable (fun τ : ℝ => profC α x τ) volume 0 1) ∧
    ContinuousOn (fun x : ℝ => profPsi α x) (Ioc 0 1) ∧
    ContinuousOn (fun x : ℝ => profGamma α x) (Ioc 0 1) ∧
    (∀ x ∈ Ioc (0 : ℝ) 1, 0 < profPsi α x ∧ 0 < profGamma α x) ∧
    (∃ κ : ℝ, 0 < κ ∧ ∀ x ∈ Ioc (0 : ℝ) 1, κ ≤ profPsi α x) ∧
    (α < 1 → IsEquivalent (𝓝[>] (0 : ℝ)) (fun x : ℝ => profPsi α x)
        (fun x : ℝ => c0 / Real.sqrt (1 - α) * Real.log (x ^ (-α))) ∧
      IsEquivalent (𝓝[>] (0 : ℝ)) (fun x : ℝ => profGamma α x)
        (fun x : ℝ => x ^ α * Real.log (x ^ (-α)) ^ 2 / (1 - α))) ∧
    (α = 1 → IsEquivalent (𝓝[>] (0 : ℝ)) (fun x : ℝ => profPsi α x)
        (fun x : ℝ => 2 / 3 * c0 * Real.log (1 / x) ^ (3 / 2 : ℝ)) ∧
      IsEquivalent (𝓝[>] (0 : ℝ)) (fun x : ℝ => profGamma α x)
        (fun x : ℝ => 4 / 9 * x * Real.log (1 / x) ^ (3 : ℕ))) ∧
    (1 < α → IsEquivalent (𝓝[>] (0 : ℝ)) (fun x : ℝ => profPsi α x)
        (fun x : ℝ => dAl α * Real.sqrt (Kc α) * x ^ (-(α - 1) / 2)) ∧
      IsEquivalent (𝓝[>] (0 : ℝ)) (fun x : ℝ => profGamma α x)
        (fun x : ℝ => 4 * Kc α ^ 2 / (α - 1) * x)) := by
  refine ⟨lem_app_pl_Psi_i_integrable hα, lem_app_pl_Gamma_helper_integrable hα,
    lem_app_pl_Psi_i_cont hα, lem_app_pl_Gamma_helper_cont hα,
    (fun x hx => ⟨lem_app_pl_Psi_i_pos hα x hx, lem_app_pl_Gamma_helper_pos hα x hx⟩),
    lem_app_pl_Psi_i_lower hα, ?_, ?_, ?_⟩
  · intro hlt
    exact ⟨lem_app_pl_Psi_ii_lt hα hlt, profiles_gamma_lt hα hlt⟩
  · intro heq
    exact ⟨lem_app_pl_Psi_ii_one heq, profiles_gamma_one heq⟩
  · intro hgt
    exact ⟨lem_app_pl_Psi_ii_gt hgt, lem_app_pl_supervol_iv_gamma hgt⟩

/-- `prop:app-pl-profiles`(ii) (snapshot `cr-2026-10-23`). Statement (LaTeX, verbatim from sections/06-power-law/section.tex):

\begin{proposition}[The profiles]\label{prop:app-pl-profiles}
\leavevmode
\begin{enumerate}[label=(\roman*)]
\item $\Psi_\alpha$ and $\Gamma_\alpha$ are finite, positive and continuous on
$(0,1]$, $\Psi_\alpha$ is bounded below by a positive constant there, and as $x\downarrow0$
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
\end{equation}
\item For $\alpha>1$, $\Phi_{\alpha,\bmom}$ and $G_{\alpha,\bmom}$ are finite, positive and
continuous on $(0,\infty)$, and
\begin{equation}\label{eqn:app-pl-crossover-ends}
\begin{gathered}
\Phi_{\alpha,\bmom}(y)\sim\sqrt{y/\sw2}\ (y\to\infty),\quad
\Phi_{\alpha,\bmom}(y)\sim d_\alpha\,y^{\frac{\alpha-1}{2\alpha}}\ (y\downarrow0),\\
G_{\alpha,\bmom}(X)\to\frac1{\sw2}\ (X\downarrow0),\quad
G_{\alpha,\bmom}(X)\sim\frac{4K_\alpha}{\alpha-1}X\ (X\to\infty).
\end{gathered}
\end{equation}
\end{enumerate}
\end{proposition}
-/
theorem prop_app_pl_profiles_ii {α β : ℝ} (hα : 1 < α) (hβ0 : 0 < β) (hβ1 : β < 1) :
    (∀ y ∈ Ioi (0 : ℝ), IntegrableOn (fun q : ℝ => Real.sqrt q * Lw (emaW β) q *
        rW (emaW β) q ^ (-(α + 1) / 2) *
        (y * rW (emaW β) q ^ α / (1 + y * rW (emaW β) q ^ α)) *
        (1 + (α - 1) * q * deriv (rW (emaW β)) q / rW (emaW β) q) / q) (Ioi 0)) ∧
    ContinuousOn (fun y : ℝ => profPhi α β y) (Ioi 0) ∧
    (∀ y ∈ Ioi (0 : ℝ), 0 < profPhi α β y) ∧
    IsEquivalent atTop (fun y : ℝ => profPhi α β y)
      (fun y : ℝ => Real.sqrt (y / sPow β 2)) ∧
    IsEquivalent (𝓝[>] (0 : ℝ)) (fun y : ℝ => profPhi α β y)
      (fun y : ℝ => dAl α * y ^ ((α - 1) / (2 * α))) ∧
    (∀ X ∈ Ioi (0 : ℝ),
      (∀ ℓ : ℤ, IntegrableOn (fun p : ℝ × ℝ =>
          Real.sqrt (profZeta α X p.1 * (1 - profZeta α X p.1) *
              (profZeta α X p.2 * (1 - profZeta α X p.2))) / Real.sqrt (p.1 * p.2) *
            (DLag β (Qm β p.1) (Qm β p.2) ℓ * profTheta α β p.1 * profTheta α β p.2 /
              profDelta α β ℓ p.1 p.2))
          (Ioi 0 ×ˢ Ioi 0)) ∧
      Summable (fun ℓ : ℤ => ∫ u in Ioi (0 : ℝ), ∫ v in Ioi (0 : ℝ),
          Real.sqrt (profZeta α X u * (1 - profZeta α X u) *
              (profZeta α X v * (1 - profZeta α X v))) / Real.sqrt (u * v) *
            (DLag β (Qm β u) (Qm β v) ℓ * profTheta α β u * profTheta α β v /
              profDelta α β ℓ u v))) ∧
    (∀ X ∈ Ioi (0 : ℝ), 0 < profG α β X) ∧
    ContinuousOn (fun X : ℝ => profG α β X) (Ioi 0) ∧
    Tendsto (fun X : ℝ => profG α β X) (𝓝[>] (0 : ℝ)) (𝓝 (1 / sPow β 2)) ∧
    IsEquivalent atTop (fun X : ℝ => profG α β X) (fun X : ℝ => 4 * Kc α / (α - 1) * X) := by
  have hPhi := lem_app_pl_super_i hα hβ0 hβ1
  refine ⟨(fun y hy => (hPhi.2 y hy).1), hPhi.1,
    (fun y hy => (hPhi.2 y hy).2), lem_app_pl_super_ii hα hβ0 hβ1,
    lem_app_pl_super_iii hα hβ0 hβ1, ?_,
    (fun X hX => lem_app_pl_supervol_i_pos hα hβ0 hβ1 X hX),
    lem_app_pl_supervol_i_cont hα hβ0 hβ1,
    lem_app_pl_supervol_ii_zero hα hβ0 hβ1,
    lem_app_pl_supervol_ii_inf hα hβ0 hβ1⟩
  intro X hX
  obtain ⟨hInt, hSum⟩ := lem_app_pl_supervol_i_finite hα hβ0 hβ1 X hX
  refine ⟨?_, hSum⟩
  intro ℓ
  simpa only [IntegrableOn, Measure.prod_restrict, ← Measure.volume_eq_prod] using hInt ℓ

private lemma pg15_plSpec_pos {α c : ℝ} (hc : 0 < c) {N : ℕ} (i : Fin N) :
    0 < plSpec α c N i := by
  unfold plSpec
  exact mul_pos hc (Real.rpow_pos_of_pos (by positivity) _)

private lemma pg15_plSpec_anti {α c : ℝ} (hα : 0 < α) (hc : 0 < c) {N : ℕ} :
    Antitone (plSpec α c N) := by
  intro i j hij
  unfold plSpec
  refine mul_le_mul_of_nonneg_left ?_ hc.le
  have hi : 0 < ((i : ℕ) : ℝ) + 1 := by positivity
  have hj : 0 < ((j : ℕ) : ℝ) + 1 := by positivity
  have hle : ((i : ℕ) : ℝ) + 1 ≤ ((j : ℕ) : ℝ) + 1 := by
    have hcast : ((i : ℕ) : ℝ) ≤ ((j : ℕ) : ℝ) := by exact_mod_cast hij
    linarith
  rw [Real.rpow_neg hi.le, Real.rpow_neg hj.le]
  exact inv_anti₀ (Real.rpow_pos_of_pos hi _) (Real.rpow_le_rpow hi.le hle hα.le)

private lemma pg15_cbarZero_eq_CbarPart {α β : ℝ} {N B : ℕ → ℕ} {c : ℕ → ℝ}
    (R : assum_app_pl_regime α β N B c)
    (cert : Muon.External.GaussianOpNorm) (γstar CSig : ℕ → ℝ)
    (hadm : ∀ n, zeroAdmissible (N n) (B n) (plSpec α (c n) (N n)) (γstar n) (CSig n))
    (n : ℕ) (i : Fin (N n)) (ℓ : ℤ) :
    cbarZero cert (γstar n) (CSig n) β (B n) (plSpec α (c n) (N n)) i ℓ.natAbs =
      CbarPart β (B n) (plSpec α (c n) (N n)) i ℓ := by
  rcases hadm n with ⟨hγ, hμC, hC1⟩
  exact (prop_app_pl_vol_zero_iii_b cert (γstar n) (CSig n)
    (R.hBpos n) (R.hNpos n) (plSpec α (c n) (N n))
    (pg15_plSpec_anti R.hα (R.hcpos n))
    (fun j => pg15_plSpec_pos (R.hcpos n) j) R.hβ0 R.hβ1 hγ hμC hC1 i ℓ).2.2

private lemma pg15_vZero_eq_vPart {α β : ℝ} {N B : ℕ → ℕ} {c : ℕ → ℝ}
    (R : assum_app_pl_regime α β N B c)
    (cert : Muon.External.GaussianOpNorm) (γstar CSig : ℕ → ℝ)
    (hadm : ∀ n, zeroAdmissible (N n) (B n) (plSpec α (c n) (N n)) (γstar n) (CSig n))
    (n : ℕ) (i : Fin (N n)) :
    vZero cert (γstar n) (CSig n) β (B n) (plSpec α (c n) (N n)) i =
      vPart β (B n) (plSpec α (c n) (N n)) i := by
  rcases hadm n with ⟨hγ, hμC, hC1⟩
  unfold vZero vPart
  apply congrArg (fun x : ℝ => 1 + 2 * x)
  exact tsum_congr fun ℓ => by
    have hbridge := (prop_app_pl_vol_zero_iii_b cert (γstar n) (CSig n)
      (R.hBpos n) (R.hNpos n) (plSpec α (c n) (N n))
      (pg15_plSpec_anti R.hα (R.hcpos n))
      (fun j => pg15_plSpec_pos (R.hcpos n) j) R.hβ0 R.hβ1 hγ hμC hC1 i
      (((ℓ + 1 : ℕ) : ℤ))).2.2
    have heq : ((ℓ : ℤ) + 1) = ((ℓ + 1 : ℕ) : ℤ) := by norm_num
    rw [Int.natAbs_natCast] at hbridge
    rw [heq]
    exact hbridge

private lemma pg15_rowNum_pos {N : ℕ} (i : Fin N) : 0 < rowNum i := by
  unfold rowNum
  positivity

private lemma pg15_rowNum_le {N : ℕ} (i : Fin N) : rowNum i ≤ (N : ℝ) := by
  unfold rowNum
  exact_mod_cast i.isLt

private lemma pg15_rowFrac_mem {N : ℕ} (hN : 0 < N) (i : Fin N) :
    rowNum i / (N : ℝ) ∈ Ioc (0 : ℝ) 1 := by
  exact ⟨div_pos (pg15_rowNum_pos i) (by exact_mod_cast hN),
    (div_le_one (by exact_mod_cast hN)).2 (pg15_rowNum_le i)⟩

private lemma pg15_Kc_pos {α : ℝ} (hα : 1 < α) : 0 < Kc α := by
  unfold Kc
  have hα0 : 0 < α := by linarith
  have hs : 0 < Real.sin (Real.pi / α) := by
    apply Real.sin_pos_of_pos_of_lt_pi
    · positivity
    · rw [div_lt_iff₀ hα0]
      nlinarith [Real.pi_pos]
  positivity

private lemma pg15_icCross_pos {α : ℝ} (hα : 1 < α) {B : ℕ} (hB : 0 < B) :
    0 < icCross α B := by
  unfold icCross
  have hK := pg15_Kc_pos hα
  have hBr : (0 : ℝ) < B := by exact_mod_cast hB
  positivity

private lemma pg15_dAl_pos {α : ℝ} (hα : 1 < α) : 0 < dAl α := by
  have hα0 : 0 < α := by linarith
  have hc : 0 < Real.cos (Real.pi / (2 * α)) := by
    apply Real.cos_pos_of_mem_Ioo
    constructor
    · have : 0 < Real.pi / (2 * α) := by positivity
      linarith [Real.pi_pos]
    · rw [div_lt_iff₀ (by positivity)]
      nlinarith [Real.pi_pos]
  unfold dAl c0
  positivity

private lemma pg15_c0_pos : 0 < c0 := by
  unfold c0
  exact Real.sqrt_pos.2 (by positivity)

private lemma pg15_dHat_pos {α β : ℝ} {N B : ℕ → ℕ} {c : ℕ → ℝ}
    (R : assum_app_pl_regime α β N B c) (n : ℕ) (i : Fin (N n)) :
    0 < dHatDrift α β (c n) (N n) (B n) i := by
  unfold dHatDrift
  apply div_pos _ (by positivity)
  rcases le_or_gt α 1 with hα | hα
  · unfold dHatSqrt2
    rw [if_pos hα]
    apply add_pos_of_nonneg_of_pos (Real.sqrt_nonneg _)
    apply mul_pos
    · unfold aN
      have hNr : (0 : ℝ) < N n := by exact_mod_cast R.hNpos n
      exact mul_pos (Real.sqrt_pos.2 (R.hcpos n)) (Real.rpow_pos_of_pos hNr _)
    · exact lem_app_pl_Psi_i_pos R.hα _ (pg15_rowFrac_mem (R.hNpos n) i)
  · unfold dHatSqrt2
    rw [if_neg (not_le_of_gt hα)]
    have hK := pg15_Kc_pos hα
    have hic := pg15_icCross_pos hα (R.hBpos n)
    have hx := (pg15_rowFrac_mem (R.hNpos n) i).1
    have hy : 0 < (icCross α (B n) / rowNum i) ^ α :=
      Real.rpow_pos_of_pos (div_pos hic (pg15_rowNum_pos i)) _
    have hPhi := (lem_app_pl_super_i hα R.hβ0 R.hβ1).2 _ hy
    have hPsi := lem_app_pl_Psi_i_pos R.hα _ (pg15_rowFrac_mem (R.hNpos n) i)
    have hb : 0 < bN α (c n) (N n) (B n) := by
      unfold bN
      have hNr : (0 : ℝ) < N n := by exact_mod_cast R.hNpos n
      have hBr : (0 : ℝ) < B n := by exact_mod_cast R.hBpos n
      have hNB : 0 < (N n : ℝ) / (B n : ℝ) := div_pos hNr hBr
      exact mul_pos (Real.sqrt_pos.2 (R.hcpos n))
        (Real.rpow_pos_of_pos (mul_pos hNB (Real.rpow_pos_of_pos hic _)) _)
    have hden : 0 < dAl α * Real.sqrt (Kc α) *
        (rowNum i / (N n : ℝ)) ^ (-(α - 1) / 2) := by
      exact mul_pos (mul_pos (pg15_dAl_pos hα) (Real.sqrt_pos.2 hK))
        (Real.rpow_pos_of_pos hx _)
    exact div_pos (mul_pos (mul_pos hb hPhi.2) hPsi) hden

private lemma pg15_vHat_pos {α β : ℝ} {N B : ℕ → ℕ} {c : ℕ → ℝ}
    (R : assum_app_pl_regime α β N B c) (n : ℕ) (i : Fin (N n)) :
    0 < if α ≤ 1 then vhatApprox β α (B n) i else vhatSuper β α (B n) i := by
  rcases le_or_gt α 1 with hα | hα
  · rw [if_pos hα]
    have hs : 0 < sPow β 2 := by
      rw [sPow_two R.hβ0.le R.hβ1]
      exact div_pos (by linarith [R.hβ1]) (by linarith [R.hβ0])
    have hγ : 0 < gammaOf (N n) (B n) := by
      unfold gammaOf
      exact div_pos (by exact_mod_cast R.hNpos n) (by exact_mod_cast R.hBpos n)
    have hG : 0 < profGamma α (rowFrac i) := by
      apply lem_app_pl_Gamma_helper_pos R.hα
      simpa [rowFrac, rowIdx, rowNum] using pg15_rowFrac_mem (R.hNpos n) i
    unfold vhatApprox
    have hfirst : 0 < 1 / sPow β 2 := one_div_pos.2 hs
    have hmid : 0 ≤ 2 * c0 / Real.sqrt (sPow β 2) *
        Real.sqrt (gammaOf (N n) (B n) * profGamma α (rowFrac i)) := by
      exact mul_nonneg (div_nonneg (mul_nonneg (by norm_num) pg15_c0_pos.le)
        (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)
    have hlast : 0 ≤ gammaOf (N n) (B n) * profGamma α (rowFrac i) := by positivity
    linarith
  · rw [if_neg (not_le_of_gt hα)]
    have hK := pg15_Kc_pos hα
    have hic := pg15_icCross_pos hα (R.hBpos n)
    have hrow : 0 < rowIdx i := by unfold rowIdx; positivity
    have hx : 0 < rowIdx i / icCross α (B n) := div_pos hrow hic
    have hfrac : rowFrac i ∈ Ioc (0 : ℝ) 1 := by
      simpa [rowFrac, rowIdx, rowNum] using pg15_rowFrac_mem (R.hNpos n) i
    have hG := lem_app_pl_supervol_i_pos hα R.hβ0 R.hβ1 _ hx
    have hGamma := lem_app_pl_Gamma_helper_pos R.hα _ hfrac
    unfold vhatSuper
    exact div_pos (mul_pos hG hGamma)
      (div_pos (mul_pos (mul_pos (by positivity) (sq_pos_of_pos hK)) hfrac.1) (sub_pos.2 hα))

private lemma pg15_weighted_ratio_le {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (a x y : ι → ℝ) (ha : ∀ i, 0 ≤ a i) (hy : ∀ i, 0 < y i)
    (hpos : 0 < ∑ i ∈ s, a i) {ε : ℝ}
    (h : ∀ i ∈ s, |x i / y i - 1| ≤ ε) :
    |(∑ i ∈ s, a i * x i) / (∑ i ∈ s, a i * y i) - 1| ≤ ε := by
  have hD : 0 < ∑ i ∈ s, a i * y i := by
    obtain ⟨i, hi, hai⟩ := (Finset.sum_pos_iff_of_nonneg fun i _ => ha i).mp hpos
    exact Finset.sum_pos' (fun i _ => mul_nonneg (ha i) (hy i).le) ⟨i, hi, mul_pos hai (hy i)⟩
  have hlo : (1 - ε) * (∑ i ∈ s, a i * y i) ≤ ∑ i ∈ s, a i * x i := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    have hlow : 1 - ε ≤ x i / y i := by linarith [(abs_le.mp (h i hi)).1]
    calc
      (1 - ε) * (a i * y i) = a i * ((1 - ε) * y i) := by ring
      _ ≤ a i * x i := mul_le_mul_of_nonneg_left
        ((le_div_iff₀ (hy i)).mp hlow) (ha i)
  have hhi : (∑ i ∈ s, a i * x i) ≤ (1 + ε) * (∑ i ∈ s, a i * y i) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    have hupp : x i / y i ≤ 1 + ε := by linarith [(abs_le.mp (h i hi)).2]
    calc
      a i * x i ≤ a i * ((1 + ε) * y i) := mul_le_mul_of_nonneg_left
        ((div_le_iff₀ (hy i)).mp hupp) (ha i)
      _ = (1 + ε) * (a i * y i) := by ring
  rw [abs_le]
  constructor
  · have := (le_div_iff₀ hD).2 hlo
    linarith
  · have := (div_le_iff₀ hD).2 hhi
    linarith

/-- `thm:app-pl-triple` (snapshot `cr-2026-10-23`). Statement (LaTeX, verbatim from sections/06-power-law/section.tex):

\begin{theorem}[The coefficient pair]\label{thm:app-pl-triple}
Under \cref{assum:app-pl-regime}, for every sequence of integers $1\le n_N\le N$
with $n_N\to\infty$,
\begin{equation}\label{eqn:app-pl-triple}
\sup_{n_N\le i\le N}\max\Big\{\Big|\frac{\mathfrak d_i(0)}{\widehat{\mathfrak d}_i}-1\Big|,\ \Big|\frac{\mathfrak v_i(0)}{\widehat{\mathfrak v}_i}-1\Big|\Big\}\longrightarrow0 .
\end{equation}
\end{theorem}
-/
theorem thm_app_pl_triple {α β : ℝ} {N B : ℕ → ℕ} {c : ℕ → ℝ}
    (R : assum_app_pl_regime α β N B c)
    (cert : Muon.External.GaussianOpNorm) (γstar CSig : ℕ → ℝ)
    (hadm : ∀ n, zeroAdmissible (N n) (B n) (plSpec α (c n) (N n)) (γstar n) (CSig n))
    (nN : ℕ → ℕ) (hnN : ∀ n, 1 ≤ nN n ∧ nN n ≤ N n)
    (hn : Tendsto (fun n => (nN n : ℝ)) atTop atTop) :
    ∀ ε > 0, ∀ᶠ n in atTop, ∀ i : Fin (N n), (nN n : ℝ) ≤ rowNum i →
      |dZero β (B n) (plSpec α (c n) (N n)) i / dHatDrift α β (c n) (N n) (B n) i - 1| ≤ ε ∧
      |vZero cert (γstar n) (CSig n) β (B n) (plSpec α (c n) (N n)) i /
          (if α ≤ 1 then vhatApprox β α (B n) i else vhatSuper β α (B n) i) - 1| ≤ ε := by
  have hnn : ∀ᶠ n in atTop, 1 ≤ nN n ∧ nN n ≤ N n := Filter.Eventually.of_forall hnN
  have hnnTop : Tendsto nN atTop atTop := tendsto_natCast_atTop_iff.mp hn
  rcases le_or_gt α 1 with hα | hα'
  · have hd := triple_drift_le_one R hα nN hnN hn
    have hv := triple_vol_le_one R hα (prop_app_pl_vol_zero_hBound cert R)
      (prop_app_pl_vol_zero_hPSD cert R) (prop_app_pl_vol_zero_hZero cert R) nN hnn hnnTop
    intro ε hε
    filter_upwards [hd ε hε, hv ε hε] with n hdn hvn
    intro i hi
    refine ⟨hdn i hi, ?_⟩
    rw [if_pos hα, pg15_vZero_eq_vPart R cert γstar CSig hadm n i]
    exact hvn i (by
      have hi' : (nN n : ℝ) ≤ (((i : ℕ) + 1 : ℕ) : ℝ) := by simpa [rowNum] using hi
      exact_mod_cast hi')
  ·
    have hd := triple_drift_gt_one R hα' nN hnN hn
    have hv := triple_vol_gt_one R hα' (prop_app_pl_vol_zero_hBound cert R)
      (prop_app_pl_vol_zero_hZero cert R) nN hnn hnnTop
    intro ε hε
    filter_upwards [hd ε hε, hv ε hε] with n hdn hvn
    intro i hi
    refine ⟨hdn i hi, ?_⟩
    rw [if_neg (not_le_of_gt hα'), pg15_vZero_eq_vPart R cert γstar CSig hadm n i]
    exact hvn i (by
      have hi' : (nN n : ℝ) ≤ (((i : ℕ) + 1 : ℕ) : ℝ) := by simpa [rowNum] using hi
      exact_mod_cast hi')

private lemma pg15_icvRow_eq (β α : ℝ) (B N : ℕ) (i : Fin N) :
    icvRow β α B i = (c0 ^ (2 / α))⁻¹ * (rowNum i / icdIdx β α N B) := by
  unfold icvRow icvIdx rowIdx rowNum
  rw [div_mul_eq_div_div, div_eq_inv_mul, div_eq_mul_inv, div_eq_mul_inv]
  ring

/-- `cor:app-pl-endpoints`(i) (snapshot `cr-2026-10-23`). Statement (LaTeX, verbatim from sections/06-power-law/section.tex):

\begin{corollary}[Crossover windows and joint endpoints]\label{cor:app-pl-endpoints}
Assume \cref{assum:app-pl-regime}, let $i=i_N\to\infty$ be a row sequence, and
let $i_\star\defeq i_{\mathrm c,\mathfrak d}$ for $\alpha\le1$ and $i_\star\defeq i_{\mathrm c}$ for $\alpha>1$.
\begin{enumerate}[label=(\roman*)]
\item If $\alpha\le1$ and $i/i_\star\to x\in(0,\infty)$, then
\[
\frac{\sqrt2\,\mathfrak d_i(0)}{a_{\mathfrak d}}\to1+x^{-\alpha/2},\qquad
\sw2\,\mathfrak v_i(0)\to1+2x^{\alpha/2}+c_0^{-2}x^\alpha,\qquad
\frac{\mu_i}{c_Ni_\star^{-\alpha}}\to x^{-\alpha}.
\]
\item The joint endpoint equivalents are
\begin{equation}\label{eqn:app-pl-endpoint-table}
\begin{array}{c|c|c}
 & i/i_\star\to0 & i/i_\star\to\infty\\\hline
\sqrt2\,\mathfrak d_i(0) & \sqrt{\mu_i/(\gamma\sw2)} & a_N\Psi_\alpha(i/N)\\[3pt]
\mathfrak v_i(0) & 1/\sw2 & \gamma\,\Gamma_\alpha(i/N)\\[3pt]
\mu_i & c_Ni^{-\alpha}\ \text{(exact)} & c_Ni^{-\alpha}\ \text{(exact)}
\end{array}
\end{equation}
\item One has $i_\star/N\to0$. There are row sequences $i\to\infty$ in both
windows $i/i_\star\to0$ and $i/i_\star\to\infty$ if and only if
\begin{equation}\label{eqn:app-pl-windows}
\frac{BN^{\alpha-1}}{\log^2\gamma}\to\infty\ \ (\alpha<1),\qquad
\frac{B}{\log^3\gamma}\to\infty\ \ (\alpha=1),\qquad
B\to\infty\ \ (\alpha>1),
\end{equation}
and then $1\ll i_\star\ll N$.
\item For $\alpha>1$, equating the two mesoscopic endpoint equivalents gives the
indices $i_{\mathrm c}/(\sw2d_\alpha^2)$ for the drift and
$B(\alpha-1)/(4\sw2K_\alpha^2)$ for the volatility, whose ratio is
$(\alpha-1)d_\alpha^2/(4K_\alpha)$; all indices of the corollary are independent of $c_N$.
\end{enumerate}
\end{corollary}
-/
theorem cor_app_pl_endpoints_i {α β : ℝ} {N B : ℕ → ℕ} {c : ℕ → ℝ}
    (R : assum_app_pl_regime α β N B c)
    (cert : Muon.External.GaussianOpNorm) (γstar CSig : ℕ → ℝ)
    (hadm : ∀ n, zeroAdmissible (N n) (B n) (plSpec α (c n) (N n)) (γstar n) (CSig n))
    (hα : α ≤ 1)
    (i : (n : ℕ) → Fin (N n)) (hi : Tendsto (fun n => rowNum (i n)) atTop atTop) :
    ∀ x ∈ Ioi (0 : ℝ),
      Tendsto (fun n => rowNum (i n) / icStar β α (N n) (B n)) atTop (𝓝 x) →
        Tendsto (fun n => Real.sqrt 2 * dZero β (B n) (plSpec α (c n) (N n)) (i n) /
            icdA α (c n) (N n) (B n)) atTop (𝓝 (1 + x ^ (-α / 2))) ∧
        Tendsto (fun n => sPow β 2 *
            vZero cert (γstar n) (CSig n) β (B n) (plSpec α (c n) (N n)) (i n)) atTop
          (𝓝 (1 + 2 * x ^ (α / 2) + (c0 ^ 2)⁻¹ * x ^ α)) ∧
        Tendsto (fun n => plSpec α (c n) (N n) (i n) / (c n * icStar β α (N n) (B n) ^ (-α)))
          atTop (𝓝 (x ^ (-α))) := by
  intro x hx h
  have e : ∀ n, icStar β α (N n) (B n) = icdIdx β α (N n) (B n) := fun n => by
    simp [icStar, hα]
  simp only [e] at h ⊢
  have hv : ∀ n, vZero cert (γstar n) (CSig n) β (B n) (plSpec α (c n) (N n)) (i n) =
      vPart β (B n) (plSpec α (c n) (N n)) (i n) :=
    fun n => pg15_vZero_eq_vPart R cert γstar CSig hadm n (i n)
  simp only [hv]
  have hx0 : 0 < x := hx
  have hc0 : 0 < c0 := by unfold c0; exact Real.sqrt_pos.2 (by positivity)
  refine ⟨(thm_app_pl_drift_i R hα i hi).1 x hx h, ?_, ?_⟩
  · have hBd := prop_app_pl_vol_zero_hBound cert R
    have hPSD := prop_app_pl_vol_zero_hPSD cert R
    have hZe := prop_app_pl_vol_zero_hZero cert R
    have hiI : Tendsto (fun n => rowIdx (i n)) atTop atTop := hi
    set y : ℝ := (c0 ^ (2 / α))⁻¹ * x with hydef
    have hypos : 0 < y := by positivity
    have hy : Tendsto (fun n => icvRow β α (B n) (i n)) atTop (𝓝 y) := by
      have : (fun n => icvRow β α (B n) (i n)) =
          fun n => (c0 ^ (2 / α))⁻¹ * (rowNum (i n) / icdIdx β α (N n) (B n)) :=
        funext fun n => pg15_icvRow_eq β α (B n) (N n) (i n)
      rw [this]
      exact h.const_mul _
    have hfy : Tendsto (fun n => 1 + 2 * c0 * icvRow β α (B n) (i n) ^ (α / 2) +
        icvRow β α (B n) (i n) ^ α) atTop (𝓝 (1 + 2 * c0 * y ^ (α / 2) + y ^ α)) := by
      have h1 := (hy.rpow_const (p := α / 2) (Or.inl hypos.ne'))
      have h2 := (hy.rpow_const (p := α) (Or.inl hypos.ne'))
      exact (tendsto_const_nhds.add (h1.const_mul _)).add h2
    have hval : 1 + 2 * c0 * y ^ (α / 2) + y ^ α =
        1 + 2 * x ^ (α / 2) + (c0 ^ 2)⁻¹ * x ^ α := by
      have hk : ((c0 ^ (2 / α))⁻¹) ^ (α / 2) = c0⁻¹ := by
        rw [Real.inv_rpow (by positivity), ← Real.rpow_mul hc0.le]
        have : 2 / α * (α / 2) = 1 := by field_simp [R.hα.ne']
        rw [this, Real.rpow_one]
      have hk2 : ((c0 ^ (2 / α))⁻¹) ^ α = (c0 ^ 2)⁻¹ := by
        rw [Real.inv_rpow (by positivity), ← Real.rpow_mul hc0.le]
        have : 2 / α * α = 2 := by field_simp [R.hα.ne']
        rw [this]
        norm_cast
      rw [hydef, Real.mul_rpow (by positivity) hx0.le, Real.mul_rpow (by positivity) hx0.le,
        hk, hk2]
      field_simp
    rw [← hval]
    refine Metric.tendsto_nhds.2 fun ε hε => ?_
    obtain ⟨M, hM⟩ := ((thm_app_pl_volatility_ii_part R hα hBd hPSD hZe).1
      (Icc (y / 2) (2 * y)) (fun t ht => lt_of_lt_of_le (by positivity) ht.1)
      isCompact_Icc (ε / 2) (by positivity))
    have hmem : ∀ᶠ n in atTop, icvRow β α (B n) (i n) ∈ Icc (y / 2) (2 * y) :=
      hy (Icc_mem_nhds (by linarith) (by linarith))
    have hMr : ∀ᶠ n in atTop, (M : ℝ) ≤ rowIdx (i n) := hiI.eventually_ge_atTop (M : ℝ)
    filter_upwards [hM, hmem, hMr, hfy.eventually (Metric.ball_mem_nhds _ (half_pos hε))]
      with n h1 h2 h3 h4
    have h5 := h1 (i n) h3 h2
    rw [Real.dist_eq] at h4 ⊢
    calc _ = |(sPow β 2 * vPart β (B n) (plSpec α (c n) (N n)) (i n) -
          (1 + 2 * c0 * icvRow β α (B n) (i n) ^ (α / 2) + icvRow β α (B n) (i n) ^ α)) +
        ((1 + 2 * c0 * icvRow β α (B n) (i n) ^ (α / 2) + icvRow β α (B n) (i n) ^ α) -
          (1 + 2 * c0 * y ^ (α / 2) + y ^ α))| := by ring_nf
      _ ≤ _ := abs_add_le _ _
      _ < ε := by linarith
  · have hpos : ∀ᶠ n in atTop, 0 < icdIdx β α (N n) (B n) := by
      filter_upwards [h.eventually (lt_mem_nhds hx0)] with n hn
      have hr : 0 < rowNum (i n) := by unfold rowNum; positivity
      by_contra hneg
      push_neg at hneg
      have : rowNum (i n) / icdIdx β α (N n) (B n) ≤ 0 := div_nonpos_of_nonneg_of_nonpos hr.le hneg
      linarith
    have h2 := h.rpow_const (p := -α) (Or.inl hx0.ne')
    refine h2.congr' ?_
    filter_upwards [hpos] with n hn
    have hr : 0 ≤ rowNum (i n) := by unfold rowNum; positivity
    have hcn := R.hcpos n
    rw [Real.div_rpow hr hn.le]
    simp only [plSpec, rowNum]
    have : 0 < Real.rpow (icdIdx β α (N n) (B n)) (-α) := Real.rpow_pos_of_pos hn _
    field_simp

/-- `cor:app-pl-endpoints`(ii) (snapshot `cr-2026-10-23`). Statement (LaTeX, verbatim from sections/06-power-law/section.tex):

\begin{corollary}[Crossover windows and joint endpoints]\label{cor:app-pl-endpoints}
Assume \cref{assum:app-pl-regime}, let $i=i_N\to\infty$ be a row sequence, and
let $i_\star\defeq i_{\mathrm c,\mathfrak d}$ for $\alpha\le1$ and $i_\star\defeq i_{\mathrm c}$ for $\alpha>1$.
\begin{enumerate}[label=(\roman*)]
\item If $\alpha\le1$ and $i/i_\star\to x\in(0,\infty)$, then
\[
\frac{\sqrt2\,\mathfrak d_i(0)}{a_{\mathfrak d}}\to1+x^{-\alpha/2},\qquad
\sw2\,\mathfrak v_i(0)\to1+2x^{\alpha/2}+c_0^{-2}x^\alpha,\qquad
\frac{\mu_i}{c_Ni_\star^{-\alpha}}\to x^{-\alpha}.
\]
\item The joint endpoint equivalents are
\begin{equation}\label{eqn:app-pl-endpoint-table}
\begin{array}{c|c|c}
 & i/i_\star\to0 & i/i_\star\to\infty\\\hline
\sqrt2\,\mathfrak d_i(0) & \sqrt{\mu_i/(\gamma\sw2)} & a_N\Psi_\alpha(i/N)\\[3pt]
\mathfrak v_i(0) & 1/\sw2 & \gamma\,\Gamma_\alpha(i/N)\\[3pt]
\mu_i & c_Ni^{-\alpha}\ \text{(exact)} & c_Ni^{-\alpha}\ \text{(exact)}
\end{array}
\end{equation}
\item One has $i_\star/N\to0$. There are row sequences $i\to\infty$ in both
windows $i/i_\star\to0$ and $i/i_\star\to\infty$ if and only if
\begin{equation}\label{eqn:app-pl-windows}
\frac{BN^{\alpha-1}}{\log^2\gamma}\to\infty\ \ (\alpha<1),\qquad
\frac{B}{\log^3\gamma}\to\infty\ \ (\alpha=1),\qquad
B\to\infty\ \ (\alpha>1),
\end{equation}
and then $1\ll i_\star\ll N$.
\item For $\alpha>1$, equating the two mesoscopic endpoint equivalents gives the
indices $i_{\mathrm c}/(\sw2d_\alpha^2)$ for the drift and
$B(\alpha-1)/(4\sw2K_\alpha^2)$ for the volatility, whose ratio is
$(\alpha-1)d_\alpha^2/(4K_\alpha)$; all indices of the corollary are independent of $c_N$.
\end{enumerate}
\end{corollary}
-/
theorem cor_app_pl_endpoints_ii {α β : ℝ} {N B : ℕ → ℕ} {c : ℕ → ℝ}
    (R : assum_app_pl_regime α β N B c)
    (cert : Muon.External.GaussianOpNorm) (γstar CSig : ℕ → ℝ)
    (hadm : ∀ n, zeroAdmissible (N n) (B n) (plSpec α (c n) (N n)) (γstar n) (CSig n))
    (i : (n : ℕ) → Fin (N n)) (hi : Tendsto (fun n => rowNum (i n)) atTop atTop) :
    (Tendsto (fun n => rowNum (i n) / icStar β α (N n) (B n)) atTop (𝓝 0) →
      IsEquivalent atTop (fun n => Real.sqrt 2 * dZero β (B n) (plSpec α (c n) (N n)) (i n))
          (fun n => Real.sqrt (plSpec α (c n) (N n) (i n) / (gammaOf (N n) (B n) * sPow β 2))) ∧
        Tendsto (fun n => vZero cert (γstar n) (CSig n) β (B n) (plSpec α (c n) (N n)) (i n))
          atTop (𝓝 (1 / sPow β 2))) ∧
    (Tendsto (fun n => rowNum (i n) / icStar β α (N n) (B n)) atTop atTop →
      IsEquivalent atTop (fun n => Real.sqrt 2 * dZero β (B n) (plSpec α (c n) (N n)) (i n))
          (fun n => aN α (c n) (N n) * profPsi α (rowNum (i n) / (N n : ℝ))) ∧
        IsEquivalent atTop
          (fun n => vZero cert (γstar n) (CSig n) β (B n) (plSpec α (c n) (N n)) (i n))
          (fun n => gammaOf (N n) (B n) * profGamma α (rowNum (i n) / (N n : ℝ)))) ∧
    (∀ n, plSpec α (c n) (N n) (i n) = c n * rowNum (i n) ^ (-α)) := by
  have hvf : (fun n => vZero cert (γstar n) (CSig n) β (B n) (plSpec α (c n) (N n)) (i n)) =
      fun n => vPart β (B n) (plSpec α (c n) (N n)) (i n) :=
    funext fun n => pg15_vZero_eq_vPart R cert γstar CSig hadm n (i n)
  have hBd := prop_app_pl_vol_zero_hBound cert R
  have hPSD := prop_app_pl_vol_zero_hPSD cert R
  have hZe := prop_app_pl_vol_zero_hZero cert R
  have hiI : Tendsto (fun n => rowIdx (i n)) atTop atTop := hi
  refine ⟨?_, ?_, fun n => ?_⟩
  · intro h
    rcases le_or_gt α 1 with hα | hα
    · have e : ∀ n, icStar β α (N n) (B n) = icdIdx β α (N n) (B n) := fun n => by
        simp [icStar, hα]
      simp only [e] at h
      refine ⟨(thm_app_pl_drift_i R hα i hi).2.1 h, ?_⟩
      rw [hvf]
      refine (thm_app_pl_volatility_ii_part R hα hBd hPSD hZe).2 i hiI |>.1 ?_
      have : (fun n => icvRow β α (B n) (i n)) =
          fun n => (c0 ^ (2 / α))⁻¹ * (rowNum (i n) / icdIdx β α (N n) (B n)) :=
        funext fun n => pg15_icvRow_eq β α (B n) (N n) (i n)
      rw [this]
      simpa using h.const_mul (c0 ^ (2 / α))⁻¹
    · have e : ∀ n, icStar β α (N n) (B n) = icCross α (B n) := fun n => by
        simp [icStar, not_le_of_gt hα]
      simp only [e] at h
      refine ⟨(thm_app_pl_drift_ii R hα i hi).2.1 h, ?_⟩
      rw [hvf]
      exact ((thm_app_pl_volatility_iii_part R hα hBd hZe) i hiI).2.1 h
  · intro h
    rcases le_or_gt α 1 with hα | hα
    · have e : ∀ n, icStar β α (N n) (B n) = icdIdx β α (N n) (B n) := fun n => by
        simp [icStar, hα]
      simp only [e] at h
      refine ⟨((thm_app_pl_drift_i R hα i hi).2.2 h).1, ?_⟩
      rw [hvf]
      refine (thm_app_pl_volatility_ii_part R hα hBd hPSD hZe).2 i hiI |>.2.1 ?_
      have : (fun n => icvRow β α (B n) (i n)) =
          fun n => (c0 ^ (2 / α))⁻¹ * (rowNum (i n) / icdIdx β α (N n) (B n)) :=
        funext fun n => pg15_icvRow_eq β α (B n) (N n) (i n)
      rw [this]
      have hc : 0 < (c0 ^ (2 / α))⁻¹ := by
        have : 0 < c0 := by unfold c0; exact Real.sqrt_pos.2 (by positivity)
        positivity
      exact h.const_mul_atTop hc
    · have e : ∀ n, icStar β α (N n) (B n) = icCross α (B n) := fun n => by
        simp [icStar, not_le_of_gt hα]
      simp only [e] at h
      refine ⟨((thm_app_pl_drift_ii R hα i hi).2.2 h).1, ?_⟩
      rw [hvf]
      exact ((thm_app_pl_volatility_iii_part R hα hBd hZe) i hiI).2.2.1 h
  · simp [plSpec, rowNum]

/-- `cor:app-pl-endpoints`(iii) (snapshot `cr-2026-10-23`). Statement (LaTeX, verbatim from sections/06-power-law/section.tex):

\begin{corollary}[Crossover windows and joint endpoints]\label{cor:app-pl-endpoints}
Assume \cref{assum:app-pl-regime}, let $i=i_N\to\infty$ be a row sequence, and
let $i_\star\defeq i_{\mathrm c,\mathfrak d}$ for $\alpha\le1$ and $i_\star\defeq i_{\mathrm c}$ for $\alpha>1$.
\begin{enumerate}[label=(\roman*)]
\item If $\alpha\le1$ and $i/i_\star\to x\in(0,\infty)$, then
\[
\frac{\sqrt2\,\mathfrak d_i(0)}{a_{\mathfrak d}}\to1+x^{-\alpha/2},\qquad
\sw2\,\mathfrak v_i(0)\to1+2x^{\alpha/2}+c_0^{-2}x^\alpha,\qquad
\frac{\mu_i}{c_Ni_\star^{-\alpha}}\to x^{-\alpha}.
\]
\item The joint endpoint equivalents are
\begin{equation}\label{eqn:app-pl-endpoint-table}
\begin{array}{c|c|c}
 & i/i_\star\to0 & i/i_\star\to\infty\\\hline
\sqrt2\,\mathfrak d_i(0) & \sqrt{\mu_i/(\gamma\sw2)} & a_N\Psi_\alpha(i/N)\\[3pt]
\mathfrak v_i(0) & 1/\sw2 & \gamma\,\Gamma_\alpha(i/N)\\[3pt]
\mu_i & c_Ni^{-\alpha}\ \text{(exact)} & c_Ni^{-\alpha}\ \text{(exact)}
\end{array}
\end{equation}
\item One has $i_\star/N\to0$. There are row sequences $i\to\infty$ in both
windows $i/i_\star\to0$ and $i/i_\star\to\infty$ if and only if
\begin{equation}\label{eqn:app-pl-windows}
\frac{BN^{\alpha-1}}{\log^2\gamma}\to\infty\ \ (\alpha<1),\qquad
\frac{B}{\log^3\gamma}\to\infty\ \ (\alpha=1),\qquad
B\to\infty\ \ (\alpha>1),
\end{equation}
and then $1\ll i_\star\ll N$.
\item For $\alpha>1$, equating the two mesoscopic endpoint equivalents gives the
indices $i_{\mathrm c}/(\sw2d_\alpha^2)$ for the drift and
$B(\alpha-1)/(4\sw2K_\alpha^2)$ for the volatility, whose ratio is
$(\alpha-1)d_\alpha^2/(4K_\alpha)$; all indices of the corollary are independent of $c_N$.
\end{enumerate}
\end{corollary}
-/
private lemma pg15p4_endpoints_sPow_two_pos {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    0 < sPow β 2 := by
  rw [sPow_two hβ0.le hβ1]
  positivity

private lemma pg15p4_endpoints_icdD_pos {α : ℝ} (hα : α ≤ 1) : 0 < icdD α := by
  unfold icdD c0
  split_ifs with h
  · positivity
  · positivity

private lemma pg15p4_endpoints_icd_over_N {α β : ℝ} {N B : ℕ → ℕ} {c : ℕ → ℝ}
    (R : assum_app_pl_regime α β N B c) (hα1 : α ≤ 1) :
    Tendsto (fun n => icdIdx β α (N n) (B n) / (N n : ℝ)) atTop (𝓝 0) := by
  have hs2 := pg15p4_endpoints_sPow_two_pos R.hβ0 R.hβ1
  have hd := pg15p4_endpoints_icdD_pos hα1
  have hLg : Tendsto (fun n => Real.log (gammaOf (N n) (B n))) atTop atTop :=
    Real.tendsto_log_atTop.comp R.hγ
  have hκ : 0 < sPow β 2 * icdD α ^ 2 := by positivity
  have hα0 := R.hα
  rcases hα1.lt_or_eq with hlt | heq
  · have hg : Tendsto (fun n => 1 / (gammaOf (N n) (B n) * (sPow β 2 * icdD α ^ 2 *
        Real.log (gammaOf (N n) (B n)) ^ 2))) atTop (𝓝 0) := by
      have h1 : Tendsto (fun n => sPow β 2 * icdD α ^ 2 *
          Real.log (gammaOf (N n) (B n)) ^ 2) atTop atTop :=
        ((tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)).comp hLg).const_mul_atTop hκ
      have h2 := Tendsto.atTop_mul_atTop₀ R.hγ h1
      exact (tendsto_const_nhds (x := (1 : ℝ))).div_atTop h2
    have h3 := (Real.continuousAt_rpow_const 0 (1 / α) (Or.inr (by positivity))).tendsto.comp hg
    rw [Real.zero_rpow (by positivity)] at h3
    refine h3.congr' ?_
    filter_upwards [hLg.eventually_gt_atTop 0] with n hn
    have hNr : (0 : ℝ) < N n := by exact_mod_cast R.hNpos n
    have hBr : (0 : ℝ) < B n := by exact_mod_cast R.hBpos n
    have hγ : 0 < gammaOf (N n) (B n) := by unfold gammaOf; positivity
    simp only [Function.comp]
    unfold icdIdx
    rw [if_pos hlt, eq_div_iff hNr.ne']
    have e : (N n : ℝ) = ((N n : ℝ) ^ α) ^ (1 / α) := by
      rw [← Real.rpow_mul hNr.le, mul_one_div_cancel R.hα.ne', Real.rpow_one]
    have hNα : 0 < (N n : ℝ) ^ α := Real.rpow_pos_of_pos hNr _
    have hgpos : 0 < 1 / (gammaOf (N n) (B n) * (sPow β 2 * icdD α ^ 2 *
        Real.log (gammaOf (N n) (B n)) ^ 2)) := by positivity
    conv_lhs => arg 2; rw [e]
    rw [← Real.mul_rpow hgpos.le hNα.le]
    congr 1
    rw [Real.rpow_sub hNr, Real.rpow_one]
    have : 0 < (N n : ℝ) ^ α := Real.rpow_pos_of_pos hNr _
    unfold gammaOf
    field_simp
  · subst heq
    have hg : Tendsto (fun n => 1 / (gammaOf (N n) (B n) * (sPow β 2 * icdD 1 ^ 2 *
        Real.log (gammaOf (N n) (B n)) ^ 3))) atTop (𝓝 0) := by
      have h1 : Tendsto (fun n => sPow β 2 * icdD 1 ^ 2 *
          Real.log (gammaOf (N n) (B n)) ^ 3) atTop atTop :=
        ((tendsto_pow_atTop (by norm_num : (3 : ℕ) ≠ 0)).comp hLg).const_mul_atTop hκ
      have h2 := Tendsto.atTop_mul_atTop₀ R.hγ h1
      exact (tendsto_const_nhds (x := (1 : ℝ))).div_atTop h2
    refine hg.congr' ?_
    filter_upwards [hLg.eventually_gt_atTop 0] with n hn
    have hNr : (0 : ℝ) < N n := by exact_mod_cast R.hNpos n
    have hBr : (0 : ℝ) < B n := by exact_mod_cast R.hBpos n
    unfold icdIdx gammaOf
    rw [if_neg (lt_irrefl _)]
    have : Real.log ((N n : ℝ) / B n) ≠ 0 := hn.ne'
    field_simp

private lemma pg15p4_endpoints_icStar_over_N {α β : ℝ} {N B : ℕ → ℕ} {c : ℕ → ℝ}
    (R : assum_app_pl_regime α β N B c) :
    Tendsto (fun n => icStar β α (N n) (B n) / (N n : ℝ)) atTop (𝓝 0) := by
  rcases le_or_gt α 1 with hα | hα
  · simpa [icStar, hα] using pg15p4_endpoints_icd_over_N R hα
  · have hK := pg15_Kc_pos hα
    have hγinv : Tendsto (fun n => 1 / gammaOf (N n) (B n)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop R.hγ
    have h := (tendsto_const_nhds (x := (1 / Kc α))).mul hγinv
    have h' : Tendsto (fun n => (1 / Kc α) * (1 / gammaOf (N n) (B n)))
        atTop (𝓝 0) := by simpa using h
    refine h'.congr' ?_
    filter_upwards with n
    have hNr : (0 : ℝ) < N n := by exact_mod_cast R.hNpos n
    have hBr : (0 : ℝ) < B n := by exact_mod_cast R.hBpos n
    simp only [icStar, if_neg (not_le_of_gt hα), icCross, gammaOf]
    field_simp

private lemma pg15p4_endpoints_icStar_atTop_iff {α β : ℝ} {N B : ℕ → ℕ} {c : ℕ → ℝ}
    (R : assum_app_pl_regime α β N B c) :
    Tendsto (fun n => icStar β α (N n) (B n)) atTop atTop ↔
      ((α < 1 → Tendsto (fun n => (B n : ℝ) * (N n : ℝ) ^ (α - 1) /
            Real.log (gammaOf (N n) (B n)) ^ 2) atTop atTop) ∧
        (α = 1 → Tendsto (fun n => (B n : ℝ) /
            Real.log (gammaOf (N n) (B n)) ^ 3) atTop atTop) ∧
        (1 < α → Tendsto (fun n => (B n : ℝ)) atTop atTop)) := by
  have hs := pg15p4_endpoints_sPow_two_pos R.hβ0 R.hβ1
  rcases lt_trichotomy α 1 with hα | hα | hα
  · have hd := pg15p4_endpoints_icdD_pos hα.le
    have hC : 0 < sPow β 2 * icdD α ^ 2 := by positivity
    constructor
    · intro hstar
      refine ⟨?_, (fun h => (hα.ne h).elim), (fun h => (by linarith))⟩
      intro _
      have hp := (tendsto_rpow_atTop R.hα).comp hstar
      have hm := hp.const_mul_atTop hC
      refine hm.congr' ?_
      filter_upwards with n
      have hNr : (0 : ℝ) < N n := by exact_mod_cast R.hNpos n
      have hBr : (0 : ℝ) < B n := by exact_mod_cast R.hBpos n
      have hq : 0 ≤ (B n : ℝ) * (N n : ℝ) ^ (α - 1) /
          (sPow β 2 * icdD α ^ 2 * Real.log (gammaOf (N n) (B n)) ^ 2) := by
        positivity
      simp only [icStar, if_pos hα.le, icdIdx, if_pos hα]
      dsimp only [Function.comp_apply]
      rw [← Real.rpow_mul hq]
      rw [one_div, inv_mul_cancel₀ R.hα.ne', Real.rpow_one]
      field_simp
    · rintro ⟨hlt, -, -⟩
      have hq := hlt hα
      have hdiv := (tendsto_div_const_atTop_of_pos hC).2 hq
      have hp := (tendsto_rpow_atTop (one_div_pos.mpr R.hα)).comp hdiv
      refine hp.congr' ?_
      filter_upwards with n
      simp only [icStar, if_pos hα.le, icdIdx, if_pos hα]
      apply congrArg (fun x : ℝ => x ^ (1 / α))
      ring
  · subst hα
    have hd := pg15p4_endpoints_icdD_pos (le_refl 1)
    have hC : 0 < sPow β 2 * icdD 1 ^ 2 := by positivity
    constructor
    · intro hstar
      refine ⟨(fun h => (lt_irrefl 1 h).elim), ?_, (fun h => (lt_irrefl 1 h).elim)⟩
      intro _
      have hm := hstar.const_mul_atTop hC
      refine hm.congr' ?_
      filter_upwards with n
      simp [icStar, icdIdx]
      field_simp [hs.ne', hd.ne']
    · rintro ⟨-, hone, -⟩
      have hq := hone rfl
      have hdiv := (tendsto_div_const_atTop_of_pos hC).2 hq
      refine hdiv.congr' ?_
      filter_upwards with n
      simp [icStar, icdIdx]
      field_simp [hs.ne', hd.ne']
  · have hK := pg15_Kc_pos hα
    constructor
    · intro _
      refine ⟨(fun h => (by linarith)), (fun h => (hα.ne' h).elim), fun _ => R.hB⟩
    · intro _
      have hdiv := (tendsto_div_const_atTop_of_pos hK).2 R.hB
      simpa [icStar, if_neg (not_le_of_gt hα), icCross] using hdiv

private lemma pg15p4_endpoints_icStar_eventually_pos {α β : ℝ} {N B : ℕ → ℕ}
    {c : ℕ → ℝ} (R : assum_app_pl_regime α β N B c) :
    ∀ᶠ n in atTop, 0 < icStar β α (N n) (B n) := by
  filter_upwards [R.hγ.eventually_gt_atTop 1] with n hγ
  rcases le_or_gt α 1 with hα | hα
  · rw [icStar, if_pos hα]
    unfold icdIdx
    split_ifs with h
    · have hs := pg15p4_endpoints_sPow_two_pos R.hβ0 R.hβ1
      have hd := pg15p4_endpoints_icdD_pos hα
      have hNr : (0 : ℝ) < N n := by exact_mod_cast R.hNpos n
      have hBr : (0 : ℝ) < B n := by exact_mod_cast R.hBpos n
      have hlog : 0 < Real.log (gammaOf (N n) (B n)) := Real.log_pos hγ
      exact Real.rpow_pos_of_pos (by positivity) _
    · have hs := pg15p4_endpoints_sPow_two_pos R.hβ0 R.hβ1
      have hd := pg15p4_endpoints_icdD_pos hα
      have hBr : (0 : ℝ) < B n := by exact_mod_cast R.hBpos n
      have hlog : 0 < Real.log (gammaOf (N n) (B n)) := Real.log_pos hγ
      positivity
  · rw [icStar, if_neg (not_le_of_gt hα)]
    exact pg15_icCross_pos hα (R.hBpos n)

private lemma pg15p4_endpoints_upper_window {α β : ℝ} {N B : ℕ → ℕ} {c : ℕ → ℝ}
    (R : assum_app_pl_regime α β N B c)
    (hsmall : Tendsto (fun n => icStar β α (N n) (B n) / (N n : ℝ)) atTop (𝓝 0)) :
    ∃ j : (n : ℕ) → Fin (N n), Tendsto (fun n => rowNum (j n)) atTop atTop ∧
      Tendsto (fun n => rowNum (j n) / icStar β α (N n) (B n)) atTop atTop := by
  let j : (n : ℕ) → Fin (N n) := fun n =>
    ⟨N n - 1, Nat.sub_lt (R.hNpos n) (by norm_num)⟩
  have hj : ∀ n, rowNum (j n) = (N n : ℝ) := by
    intro n
    simp only [j, rowNum]
    norm_cast
    exact Nat.sub_add_cancel (R.hNpos n)
  refine ⟨j, ?_, ?_⟩
  · simpa only [hj] using R.hN
  · have hpos : ∀ᶠ n in atTop, 0 < icStar β α (N n) (B n) / (N n : ℝ) := by
      filter_upwards [pg15p4_endpoints_icStar_eventually_pos R] with n hn
      exact div_pos hn (by exact_mod_cast R.hNpos n)
    have hwithin : Tendsto (fun n => icStar β α (N n) (B n) / (N n : ℝ))
        atTop (𝓝[>] 0) := tendsto_nhdsWithin_iff.2 ⟨hsmall, hpos⟩
    have hinv := hwithin.inv_tendsto_nhdsGT_zero
    refine hinv.congr' ?_
    filter_upwards [pg15p4_endpoints_icStar_eventually_pos R] with n hn
    rw [hj]
    simp only [Pi.inv_apply, inv_div]

private lemma pg15p4_endpoints_lower_window_imp_atTop {α β : ℝ} {N B : ℕ → ℕ}
    {c : ℕ → ℝ} (R : assum_app_pl_regime α β N B c)
    {i : (n : ℕ) → Fin (N n)}
    (hi : Tendsto (fun n => rowNum (i n)) atTop atTop)
    (hr : Tendsto (fun n => rowNum (i n) / icStar β α (N n) (B n)) atTop (𝓝 0)) :
    Tendsto (fun n => icStar β α (N n) (B n)) atTop atTop := by
  refine tendsto_atTop_mono' atTop ?_ hi
  filter_upwards [hr.eventually (Iio_mem_nhds zero_lt_one),
    pg15p4_endpoints_icStar_eventually_pos R] with n hn hs
  exact (div_lt_one hs).mp hn |>.le

private lemma pg15p4_endpoints_lower_window_of_atTop {α β : ℝ} {N B : ℕ → ℕ}
    {c : ℕ → ℝ} (R : assum_app_pl_regime α β N B c)
    (hsmall : Tendsto (fun n => icStar β α (N n) (B n) / (N n : ℝ)) atTop (𝓝 0))
    (hstar : Tendsto (fun n => icStar β α (N n) (B n)) atTop atTop) :
    ∃ i : (n : ℕ) → Fin (N n), Tendsto (fun n => rowNum (i n)) atTop atTop ∧
      Tendsto (fun n => rowNum (i n) / icStar β α (N n) (B n)) atTop (𝓝 0) := by
  let s : ℕ → ℝ := fun n => icStar β α (N n) (B n)
  let k : ℕ → ℕ := fun n => ⌊Real.sqrt (s n)⌋₊
  have hsqrt : Tendsto (fun n => Real.sqrt (s n)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp hstar
  have hk : Tendsto k atTop atTop := tendsto_nat_floor_atTop.comp hsqrt
  have hklt : ∀ᶠ n in atTop, k n < N n := by
    filter_upwards [hstar.eventually_ge_atTop 1,
      hsmall.eventually (Iio_mem_nhds zero_lt_one)] with n hs1 hsn
    have hNr : (0 : ℝ) < N n := by exact_mod_cast R.hNpos n
    have hsN : s n < (N n : ℝ) := (div_lt_one hNr).mp hsn
    have hsqrt_le : Real.sqrt (s n) ≤ s n := (Real.sqrt_le_iff).2 ⟨by linarith, by nlinarith⟩
    have hk_le : (k n : ℝ) ≤ Real.sqrt (s n) := Nat.floor_le (Real.sqrt_nonneg _)
    exact_mod_cast (hk_le.trans_lt (hsqrt_le.trans_lt hsN))
  let i : (n : ℕ) → Fin (N n) := fun n =>
    if h : k n < N n then ⟨k n, h⟩ else ⟨0, R.hNpos n⟩
  have hi_eq : ∀ᶠ n in atTop, rowNum (i n) = (k n : ℝ) + 1 := by
    filter_upwards [hklt] with n hn
    simp [i, hn, rowNum]
  refine ⟨i, ?_, ?_⟩
  · have hkR : Tendsto (fun n => (k n : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop.comp hk
    have hadd := tendsto_atTop_add_const_right atTop 1 hkR
    refine hadd.congr' ?_
    filter_upwards [hi_eq] with n hn
    exact hn.symm
  · have hspos := pg15p4_endpoints_icStar_eventually_pos R
    have hsInv : Tendsto (fun n => (s n)⁻¹) atTop (𝓝 0) := hstar.inv_tendsto_atTop
    have hsqrtInv : Tendsto (fun n => (Real.sqrt (s n))⁻¹) atTop (𝓝 0) :=
      hsqrt.inv_tendsto_atTop
    have hbound : Tendsto (fun n => (Real.sqrt (s n))⁻¹ + (s n)⁻¹) atTop (𝓝 0) := by
      simpa using hsqrtInv.add hsInv
    apply squeeze_zero' _ _ hbound
    · filter_upwards [hspos] with n hn
      exact div_nonneg (le_of_lt (pg15_rowNum_pos (i n))) hn.le
    · filter_upwards [hi_eq, hspos] with n hin hn
      change 0 < s n at hn
      have hk_le : (k n : ℝ) ≤ Real.sqrt (s n) := Nat.floor_le (Real.sqrt_nonneg _)
      rw [hin, div_le_iff₀ hn]
      have hsqrt_pos : 0 < Real.sqrt (s n) := Real.sqrt_pos.2 hn
      have hsqrt_sq : Real.sqrt (s n) * Real.sqrt (s n) = s n := by nlinarith [Real.sq_sqrt hn.le]
      have hinvSqrt : (Real.sqrt (s n))⁻¹ * s n = Real.sqrt (s n) := by
        calc
          _ = (Real.sqrt (s n))⁻¹ *
              (Real.sqrt (s n) * Real.sqrt (s n)) :=
            congrArg (fun x => (Real.sqrt (s n))⁻¹ * x) hsqrt_sq.symm
          _ = _ := by field_simp
      rw [add_mul, hinvSqrt, inv_mul_cancel₀ hn.ne']
      simpa [add_comm] using add_le_add_right hk_le 1

theorem cor_app_pl_endpoints_iii {α β : ℝ} {N B : ℕ → ℕ} {c : ℕ → ℝ}
    (R : assum_app_pl_regime α β N B c) :
    Tendsto (fun n => icStar β α (N n) (B n) / (N n : ℝ)) atTop (𝓝 0) ∧
    (((∃ i : (n : ℕ) → Fin (N n), Tendsto (fun n => rowNum (i n)) atTop atTop ∧
          Tendsto (fun n => rowNum (i n) / icStar β α (N n) (B n)) atTop (𝓝 0)) ∧
        (∃ j : (n : ℕ) → Fin (N n), Tendsto (fun n => rowNum (j n)) atTop atTop ∧
          Tendsto (fun n => rowNum (j n) / icStar β α (N n) (B n)) atTop atTop)) ↔
      ((α < 1 → Tendsto (fun n => (B n : ℝ) * (N n : ℝ) ^ (α - 1) /
            Real.log (gammaOf (N n) (B n)) ^ 2) atTop atTop) ∧
        (α = 1 → Tendsto (fun n => (B n : ℝ) / Real.log (gammaOf (N n) (B n)) ^ 3)
            atTop atTop) ∧
        (1 < α → Tendsto (fun n => (B n : ℝ)) atTop atTop))) ∧
    (((α < 1 → Tendsto (fun n => (B n : ℝ) * (N n : ℝ) ^ (α - 1) /
            Real.log (gammaOf (N n) (B n)) ^ 2) atTop atTop) ∧
        (α = 1 → Tendsto (fun n => (B n : ℝ) / Real.log (gammaOf (N n) (B n)) ^ 3)
            atTop atTop) ∧
        (1 < α → Tendsto (fun n => (B n : ℝ)) atTop atTop)) →
      Tendsto (fun n => icStar β α (N n) (B n)) atTop atTop) := by
  have hsmall := pg15p4_endpoints_icStar_over_N R
  refine ⟨hsmall, ?_, ?_⟩
  · constructor
    · rintro ⟨⟨i, hi, hir⟩, -⟩
      exact (pg15p4_endpoints_icStar_atTop_iff R).mp
        (pg15p4_endpoints_lower_window_imp_atTop R hi hir)
    · intro hcond
      have hstar := (pg15p4_endpoints_icStar_atTop_iff R).mpr hcond
      exact ⟨pg15p4_endpoints_lower_window_of_atTop R hsmall hstar,
        pg15p4_endpoints_upper_window R hsmall⟩
  · intro hcond
    exact (pg15p4_endpoints_icStar_atTop_iff R).mpr hcond

/-- `cor:app-pl-endpoints`(iv) (snapshot `cr-2026-10-23`). Statement (LaTeX, verbatim from sections/06-power-law/section.tex):

\begin{corollary}[Crossover windows and joint endpoints]\label{cor:app-pl-endpoints}
Assume \cref{assum:app-pl-regime}, let $i=i_N\to\infty$ be a row sequence, and
let $i_\star\defeq i_{\mathrm c,\mathfrak d}$ for $\alpha\le1$ and $i_\star\defeq i_{\mathrm c}$ for $\alpha>1$.
\begin{enumerate}[label=(\roman*)]
\item If $\alpha\le1$ and $i/i_\star\to x\in(0,\infty)$, then
\[
\frac{\sqrt2\,\mathfrak d_i(0)}{a_{\mathfrak d}}\to1+x^{-\alpha/2},\qquad
\sw2\,\mathfrak v_i(0)\to1+2x^{\alpha/2}+c_0^{-2}x^\alpha,\qquad
\frac{\mu_i}{c_Ni_\star^{-\alpha}}\to x^{-\alpha}.
\]
\item The joint endpoint equivalents are
\begin{equation}\label{eqn:app-pl-endpoint-table}
\begin{array}{c|c|c}
 & i/i_\star\to0 & i/i_\star\to\infty\\\hline
\sqrt2\,\mathfrak d_i(0) & \sqrt{\mu_i/(\gamma\sw2)} & a_N\Psi_\alpha(i/N)\\[3pt]
\mathfrak v_i(0) & 1/\sw2 & \gamma\,\Gamma_\alpha(i/N)\\[3pt]
\mu_i & c_Ni^{-\alpha}\ \text{(exact)} & c_Ni^{-\alpha}\ \text{(exact)}
\end{array}
\end{equation}
\item One has $i_\star/N\to0$. There are row sequences $i\to\infty$ in both
windows $i/i_\star\to0$ and $i/i_\star\to\infty$ if and only if
\begin{equation}\label{eqn:app-pl-windows}
\frac{BN^{\alpha-1}}{\log^2\gamma}\to\infty\ \ (\alpha<1),\qquad
\frac{B}{\log^3\gamma}\to\infty\ \ (\alpha=1),\qquad
B\to\infty\ \ (\alpha>1),
\end{equation}
and then $1\ll i_\star\ll N$.
\item For $\alpha>1$, equating the two mesoscopic endpoint equivalents gives the
indices $i_{\mathrm c}/(\sw2d_\alpha^2)$ for the drift and
$B(\alpha-1)/(4\sw2K_\alpha^2)$ for the volatility, whose ratio is
$(\alpha-1)d_\alpha^2/(4K_\alpha)$; all indices of the corollary are independent of $c_N$.
\end{enumerate}
\end{corollary}
-/
theorem cor_app_pl_endpoints_iv {α β : ℝ} {N B : ℕ → ℕ} {c : ℕ → ℝ}
    (R : assum_app_pl_regime α β N B c) (hα : 1 < α) (n : ℕ) :
    (∀ x : ℝ, 0 < x →
      (Real.sqrt (c n * x ^ (-α) / (gammaOf (N n) (B n) * sPow β 2)) =
          dAl α * Real.sqrt (c n * Kc α) * (N n : ℝ) ^ (-(1 : ℝ) / 2) * x ^ (-(α - 1) / 2) ↔
        x = icCross α (B n) / (sPow β 2 * dAl α ^ 2))) ∧
    (∀ x : ℝ, 0 < x →
      (1 / sPow β 2 = 4 * Kc α ^ 2 / (α - 1) * (x / (B n : ℝ)) ↔
        x = (B n : ℝ) * (α - 1) / (4 * sPow β 2 * Kc α ^ 2))) ∧
    ((B n : ℝ) * (α - 1) / (4 * sPow β 2 * Kc α ^ 2)) /
        (icCross α (B n) / (sPow β 2 * dAl α ^ 2)) =
      (α - 1) * dAl α ^ 2 / (4 * Kc α) := by
  have hs : 0 < sPow β 2 := by
    rw [sPow_two R.hβ0.le R.hβ1]
    exact div_pos (by linarith [R.hβ1]) (by linarith [R.hβ0])
  have hK := pg15_Kc_pos hα
  have hd := pg15_dAl_pos hα
  have hNr : (0 : ℝ) < N n := by exact_mod_cast R.hNpos n
  have hBr : (0 : ℝ) < B n := by exact_mod_cast R.hBpos n
  have hc := R.hcpos n
  have hgamma : 0 < gammaOf (N n) (B n) := by
    unfold gammaOf
    positivity
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    have hNpow : ((N n : ℝ) ^ (-(1 : ℝ) / 2)) ^ 2 = (N n : ℝ)⁻¹ := by
      rw [← Real.rpow_mul_natCast hNr.le]
      convert Real.rpow_neg_one (N n : ℝ) using 2 <;> norm_num
    have hxpow : (x ^ (-(α - 1) / 2)) ^ 2 = x ^ (-(α - 1)) := by
      rw [← Real.rpow_mul_natCast hx.le]
      congr 1
      ring
    have hxsplit : x ^ (-α) = x ^ (-(α - 1)) / x := by
      rw [show -α = -(α - 1) - 1 by ring, Real.rpow_sub hx, Real.rpow_one]
    constructor
    · intro h
      have harg : 0 ≤ c n * x ^ (-α) /
          (gammaOf (N n) (B n) * sPow β 2) := by positivity
      have hsq := congrArg (fun y : ℝ => y ^ 2) h
      rw [Real.sq_sqrt harg, mul_pow, mul_pow, mul_pow,
        Real.sq_sqrt (mul_nonneg hc.le hK.le), hNpow, hxpow, hxsplit] at hsq
      unfold gammaOf at hsq
      unfold icCross
      field_simp [hs.ne', hd.ne', hK.ne', hNr.ne', hBr.ne', hx.ne'] at hsq ⊢
      exact hsq.symm
    · intro h
      have harg : 0 ≤ c n * x ^ (-α) /
          (gammaOf (N n) (B n) * sPow β 2) := by positivity
      have hrhs : 0 ≤ dAl α * Real.sqrt (c n * Kc α) *
          (N n : ℝ) ^ (-(1 : ℝ) / 2) * x ^ (-(α - 1) / 2) := by positivity
      rw [Real.sqrt_eq_iff_eq_sq harg hrhs, mul_pow, mul_pow, mul_pow,
        Real.sq_sqrt (mul_nonneg hc.le hK.le), hNpow, hxpow, hxsplit]
      unfold gammaOf
      unfold icCross at h
      field_simp [hs.ne', hd.ne', hK.ne', hNr.ne', hBr.ne', hx.ne'] at h ⊢
      exact h.symm
  · intro x _
    constructor <;> intro h
    · field_simp [hs.ne', hK.ne', hBr.ne', (sub_pos.2 hα).ne'] at h ⊢
      linarith
    · field_simp [hs.ne', hK.ne', hBr.ne', (sub_pos.2 hα).ne'] at h ⊢
      linarith
  · unfold icCross
    field_simp [hs.ne', hK.ne', hd.ne', hBr.ne', (sub_pos.2 hα).ne']

private lemma pg15p4_wseq {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) :
    WeightSeq (emaW β) := by
  refine ⟨fun j => ?_, ?_, ⟨0, ?_⟩⟩
  · unfold emaW
    exact mul_nonneg (by linarith) (pow_nonneg hβ0 j)
  · exact (summable_geometric_of_lt_one hβ0 hβ1).mul_left (1 - β) |>.congr fun j => by
      simp [emaW]
  · simp [emaW]
    linarith

private lemma pg15p4_rW_atTop {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    Tendsto (rW (emaW β)) atTop atTop := by
  have hT := (lem_app_de_scalar_iii (pg15p4_wseq hβ0.le hβ1)).2.2.2.2.2.2
  have hset : {j : ℕ | 0 < emaW β j} = Set.univ := by
    ext j
    simp only [Set.mem_univ, iff_true]
    unfold emaW
    exact mul_pos (by linarith) (pow_pos hβ0 j)
  rw [hset, Set.Infinite.encard_eq Set.infinite_univ, ENat.toENNReal_top] at hT
  refine tendsto_atTop.2 fun K => ?_
  filter_upwards [hT.eventually_const_lt ENNReal.ofReal_lt_top] with q hq
  exact ((ENNReal.ofReal_lt_ofReal_iff').1 hq).1.le

private lemma pg15p4_Qm_pos {β m : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hm : 0 < m) :
    0 < Qm β m := by
  have hcont : ContinuousOn (rW (emaW β)) (Ici 0) := by
    exact continuousOn_id.mul (lem_app_de_scalar_ii (pg15p4_wseq hβ0.le hβ1)).2.2.1
  have hr0 : rW (emaW β) 0 = 0 :=
    (lem_app_de_scalar_iii (pg15p4_wseq hβ0.le hβ1)).2.2.1
  obtain ⟨b, hb⟩ := (((pg15p4_rW_atTop hβ0 hβ1).eventually_gt_atTop m).and
    (eventually_gt_atTop (0 : ℝ))).exists
  have hmem : m ∈ Icc (rW (emaW β) 0) (rW (emaW β) b) :=
    ⟨by rw [hr0]; exact hm.le, hb.1.le⟩
  obtain ⟨x, hx, hfx⟩ :=
    intermediate_value_Icc hb.2.le (hcont.mono Icc_subset_Ici_self) hmem
  have hxpos : 0 < x := by
    rcases hx.1.eq_or_lt with h | h
    · exfalso
      rw [← h, hr0] at hfx
      linarith
    · exact h
  have hex : ∃ a ∈ Ioi (0 : ℝ), rW (emaW β) a = m := ⟨x, hxpos, hfx⟩
  exact Function.invFunOn_mem hex

private lemma pg15p4_ridgeZbar_pos {α β : ℝ} {N B : ℕ → ℕ} {c : ℕ → ℝ}
    (R : assum_app_pl_regime α β N B c) (n : ℕ) :
    0 < ridgeZbar β (B n) (plSpec α (c n) (N n)) := by
  let μ := plSpec α (c n) (N n)
  have hμ : ∀ i, 0 < μ i := by
    intro i
    simp only [μ, plSpec]
    exact mul_pos (R.hcpos n) (Real.rpow_pos_of_pos (by positivity) _)
  have hm := (def_app_pl_participation_bij μ (R.hBpos n) (R.hNpos n) hμ).1.mapsTo
    (show (1 : ℝ) ∈ Ioi 0 by norm_num)
  have hLam := (def_app_pl_participation_bij μ (R.hBpos n) (R.hNpos n) hμ).2.1.mapsTo hm
  have hQ := pg15p4_Qm_pos R.hβ0 R.hβ1 hm.1
  unfold ridgeZbar plZ1 sN
  exact lt_min (div_pos (mul_pos (sub_pos.2 hm.2) hm.1) (mul_pos hQ hLam)) zero_lt_one

private lemma pg15p4_diag_bound {f : ℕ → ℝ}
    (h : ∀ n, |f n| ≤ ((n + 1 : ℕ) : ℝ)⁻¹) : Tendsto f atTop (𝓝 0) := by
  rw [tendsto_zero_iff_abs_tendsto_zero]
  apply squeeze_zero (fun n => abs_nonneg (f n)) h
  simpa [one_div, Nat.cast_add, Nat.cast_one] using
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))

private lemma pg15p4_small_ridges (z A C : ℕ → ℝ) (hz : ∀ n, 0 < z n) :
    ∃ r : ℕ → ℝ, (∀ n, 0 < r n ∧ r n ≤ z n) ∧
      Tendsto (fun n => A n * r n) atTop (𝓝 0) ∧
      Tendsto (fun n => C n * (r n) ^ ((1 : ℝ) / 4)) atTop (𝓝 0) := by
  let e : ℕ → ℝ := fun n => ((n + 1 : ℕ) : ℝ)⁻¹
  let d : ℕ → ℝ := fun n => e n / (|C n| + 1)
  let r : ℕ → ℝ := fun n => min (z n / 2)
    (min (e n / (|A n| + 1)) ((d n) ^ 4))
  have he : ∀ n, 0 < e n := fun n => by simp only [e]; positivity
  have hd : ∀ n, 0 < d n := fun n => by simp only [d]; positivity
  have hrpos : ∀ n, 0 < r n := fun n => by
    simp only [r]
    exact lt_min (by linarith [hz n])
      (lt_min (div_pos (he n) (by linarith [abs_nonneg (A n)])) (pow_pos (hd n) 4))
  refine ⟨r, fun n => ⟨hrpos n, (min_le_left _ _).trans (by linarith [hz n])⟩, ?_, ?_⟩
  · apply pg15p4_diag_bound
    intro n
    rw [abs_mul, abs_of_pos (hrpos n)]
    have hrle : r n ≤ e n / (|A n| + 1) :=
      (min_le_right _ _).trans (min_le_left _ _)
    calc
      |A n| * r n ≤ |A n| * (e n / (|A n| + 1)) :=
        mul_le_mul_of_nonneg_left hrle (abs_nonneg _)
      _ ≤ e n := by
        rw [show |A n| * (e n / (|A n| + 1)) =
          e n * (|A n| / (|A n| + 1)) by ring]
        simpa using mul_le_mul_of_nonneg_left
          ((div_le_one (by positivity : 0 < |A n| + 1)).2 (by linarith [abs_nonneg (A n)]))
          (he n).le
      _ = ((n + 1 : ℕ) : ℝ)⁻¹ := rfl
  · apply pg15p4_diag_bound
    intro n
    rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg (hrpos n).le _)]
    have hrle : r n ≤ (d n) ^ 4 := (min_le_right _ _).trans (min_le_right _ _)
    have hpow : (r n) ^ ((1 : ℝ) / 4) ≤ d n := by
      calc
        (r n) ^ ((1 : ℝ) / 4) ≤ ((d n) ^ 4) ^ ((1 : ℝ) / 4) :=
          Real.rpow_le_rpow (hrpos n).le hrle (by norm_num)
        _ = d n := by
          convert Real.pow_rpow_inv_natCast (hd n).le (n := 4) (by norm_num) using 1 <;>
            norm_num
    calc
      |C n| * (r n) ^ ((1 : ℝ) / 4) ≤ |C n| * d n :=
        mul_le_mul_of_nonneg_left hpow (abs_nonneg _)
      _ ≤ e n := by
        simp only [d]
        rw [show |C n| * (e n / (|C n| + 1)) =
          e n * (|C n| / (|C n| + 1)) by ring]
        simpa using mul_le_mul_of_nonneg_left
          ((div_le_one (by positivity : 0 < |C n| + 1)).2 (by linarith [abs_nonneg (C n)]))
          (he n).le
      _ = ((n + 1 : ℕ) : ℝ)⁻¹ := rfl

private lemma pg15p4_lag_cutoffs {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (E : ℕ → ℝ) :
    ∃ H : ℕ → ℕ, Tendsto (fun n => E n * β ^ ((H n : ℝ) / 3)) atTop (𝓝 0) := by
  have hex : ∀ n : ℕ, ∃ k : ℕ,
      |E n * β ^ ((k : ℝ) / 3)| ≤ ((n + 1 : ℕ) : ℝ)⁻¹ := by
    intro n
    have heps : 0 < ((n + 1 : ℕ) : ℝ)⁻¹ := by positivity
    have hexp : Tendsto (fun k : ℕ => (k : ℝ) / 3) atTop atTop :=
      tendsto_natCast_atTop_atTop.atTop_div_const (by norm_num)
    have hpow : Tendsto (fun k : ℕ => β ^ ((k : ℝ) / 3)) atTop (𝓝 0) :=
      (tendsto_rpow_atTop_of_base_lt_one β (by linarith) hβ1).comp hexp
    have hlim : Tendsto (fun k : ℕ => E n * β ^ ((k : ℝ) / 3)) atTop (𝓝 0) := by
      simpa using tendsto_const_nhds.mul hpow
    have hev : ∀ᶠ k : ℕ in atTop,
        |E n * β ^ ((k : ℝ) / 3)| < ((n + 1 : ℕ) : ℝ)⁻¹ := by
      simpa [Real.dist_eq] using hlim.eventually (Metric.ball_mem_nhds 0 heps)
    obtain ⟨k, hk⟩ := hev.exists
    exact ⟨k, hk.le⟩
  choose H hH using hex
  exact ⟨H, pg15p4_diag_bound hH⟩

private lemma pg15p4_icdD_pos {α : ℝ} (hα : α ≤ 1) : 0 < icdD α := by
  unfold icdD c0
  split_ifs with h
  · have : 0 < 1 - α := by linarith
    positivity
  · positivity

/-- `cor:app-pl-weighted` (snapshot `cr-2026-10-23`). Statement (LaTeX, verbatim from sections/06-power-law/section.tex):

\begin{corollary}[Nonnegative weighted sums]\label{cor:app-pl-weighted}
Assume \cref{assum:app-pl-regime}. Let $I_N\subset\{n_N,\dots,N\}$ with $n_N\to\infty$,
and let $a_{i,N}\ge0$ be deterministic weights, not all zero for each $N$. Then
\[
\frac{\sum_{i\in I_N}a_{i,N}\,\mathfrak d_i(0)}{\sum_{i\in I_N}a_{i,N}\,\widehat{\mathfrak d}_i}\longrightarrow1,\qquad
\frac{\sum_{i\in I_N}a_{i,N}\,\mathfrak v_i(0)}{\sum_{i\in I_N}a_{i,N}\,\widehat{\mathfrak v}_i}\longrightarrow1 .
\]
\end{corollary}
-/
theorem cor_app_pl_weighted {α β : ℝ} {N B : ℕ → ℕ} {c : ℕ → ℝ}
    (R : assum_app_pl_regime α β N B c)
    (cert : Muon.External.GaussianOpNorm) (γstar CSig : ℕ → ℝ)
    (hadm : ∀ n, zeroAdmissible (N n) (B n) (plSpec α (c n) (N n)) (γstar n) (CSig n))
    (nN : ℕ → ℕ) (hnN : ∀ n, 1 ≤ nN n ∧ nN n ≤ N n)
    (hn : Tendsto (fun n => (nN n : ℝ)) atTop atTop)
    (I : (n : ℕ) → Finset (Fin (N n))) (hI : ∀ n, ∀ i ∈ I n, nN n ≤ (i : ℕ) + 1)
    (a : (n : ℕ) → Fin (N n) → ℝ) (ha : ∀ n i, 0 ≤ a n i)
    (hpos : ∀ n, 0 < ∑ i ∈ I n, a n i) :
    Tendsto (fun n => (∑ i ∈ I n, a n i * dZero β (B n) (plSpec α (c n) (N n)) i) /
        (∑ i ∈ I n, a n i * dHatDrift α β (c n) (N n) (B n) i)) atTop (𝓝 1) ∧
    Tendsto (fun n => (∑ i ∈ I n, a n i *
          vZero cert (γstar n) (CSig n) β (B n) (plSpec α (c n) (N n)) i) /
        (∑ i ∈ I n, a n i *
          (if α ≤ 1 then vhatApprox β α (B n) i else vhatSuper β α (B n) i))) atTop (𝓝 1) := by
  constructor
  · rw [Metric.tendsto_atTop]
    intro ε hε
    have htriple := thm_app_pl_triple R cert γstar CSig hadm nN hnN hn (ε / 2) (by positivity)
    rw [Filter.eventually_atTop] at htriple
    obtain ⟨n0, hn0⟩ := htriple
    refine ⟨n0, fun n hn0n => ?_⟩
    have htriple_n := hn0 n hn0n
    rw [Real.dist_eq]
    apply lt_of_le_of_lt (pg15_weighted_ratio_le (I n)
      (a n)
      (fun i => dZero β (B n) (plSpec α (c n) (N n)) i)
      (fun i => dHatDrift α β (c n) (N n) (B n) i)
      (ha n) (pg15_dHat_pos R n) (hpos n) (ε := ε / 2) ?_) (by linarith)
    intro i hi
    exact (htriple_n i (by
      have hi' : nN n ≤ (i : ℕ) + 1 := hI n i hi
      have hi'' : (nN n : ℝ) ≤ (((i : ℕ) + 1 : ℕ) : ℝ) := by exact_mod_cast hi'
      simpa [rowNum] using hi'')).1
  · rw [Metric.tendsto_atTop]
    intro ε hε
    have htriple := thm_app_pl_triple R cert γstar CSig hadm nN hnN hn (ε / 2) (by positivity)
    rw [Filter.eventually_atTop] at htriple
    obtain ⟨n0, hn0⟩ := htriple
    refine ⟨n0, fun n hn0n => ?_⟩
    have htriple_n := hn0 n hn0n
    rw [Real.dist_eq]
    apply lt_of_le_of_lt (pg15_weighted_ratio_le (I n)
      (a n)
      (fun i => vZero cert (γstar n) (CSig n) β (B n) (plSpec α (c n) (N n)) i)
      (fun i => if α ≤ 1 then vhatApprox β α (B n) i else vhatSuper β α (B n) i)
      (ha n) (pg15_vHat_pos R n) (hpos n) (ε := ε / 2) ?_) (by linarith)
    intro i hi
    exact (htriple_n i (by
      have hi' : nN n ≤ (i : ℕ) + 1 := hI n i hi
      have hi'' : (nN n : ℝ) ≤ (((i : ℕ) + 1 : ℕ) : ℝ) := by exact_mod_cast hi'
      simpa [rowNum] using hi'')).2

/-! ### Record volatility (`thm:app-pl-volatility`) for the zero-ridge coefficients -/

/-- `thm:app-pl-volatility`(i) (snapshot `cr-2026-10-23`). Record form for the zero-ridge coefficients `vZero`/`cbarZero`; the part-form hypotheses `hBound`, `hPSD`, `hZero` are discharged by `prop_app_pl_vol_zero_*` and not restated. Statement (LaTeX, verbatim from sections/06-power-law/section.tex):

\begin{theorem}[Volatility crossover and bulk profile]\label{thm:app-pl-volatility}
Assume \cref{assum:app-pl-regime} and let $i=i_N$ be a row sequence.
\begin{enumerate}[label=(\roman*)]
\item (Bulk.) If $i/N\to x\in(0,1]$ and $\ell=\ell_N$ are integers with
$\ell/\gamma\to\tau\in(0,1)$, then
\[
\overline C_{i,\ell}(0)\longrightarrow C_{\alpha,x}(\tau),\qquad \frac{\mathfrak v_i(0)}{\gamma}\longrightarrow\Gamma_\alpha(x),
\]
locally uniformly in $x\in(0,1]$ and $\tau\in(0,1)$.
\item Let $0<\alpha\le1$, let $i\to\infty$, and put
\begin{equation}\label{eqn:app-pl-icv}
i_{\mathrm c,\mathfrak v}\defeq c_0^{2/\alpha}\,i_{\mathrm c,\mathfrak d}=\begin{cases}N\big[(1-\alpha)/(\sw2\gamma\log^2\gamma)\big]^{1/\alpha},&\alpha<1,\\ 9B/(4\sw2\log^3\gamma),&\alpha=1.\end{cases}
\end{equation}
If $i/i_{\mathrm c,\mathfrak v}\to y\in(0,\infty)$, then
$\sw2\,\mathfrak v_i(0)\to1+2c_0y^{\alpha/2}+y^\alpha$, uniformly for $y$ in compact subsets of
$(0,\infty)$. If $i/i_{\mathrm c,\mathfrak v}\to0$, then $\mathfrak v_i(0)\to1/\sw2$. If
$i/i_{\mathrm c,\mathfrak v}\to\infty$, then $\mathfrak v_i(0)\sim\gamma\Gamma_\alpha(i/N)$, and if moreover
$i/N\to0$,
\[
\mathfrak v_i(0)\sim\frac{\gamma(i/N)^\alpha\big[\log((N/i)^\alpha)\big]^2}{1-\alpha}\quad(\alpha<1),\qquad
\mathfrak v_i(0)\sim\frac49\,\frac iB\,\big[\log(N/i)\big]^3\quad(\alpha=1).
\]
\item Let $\alpha>1$ and $i\to\infty$. If $i/i_{\mathrm c}\to X_0\in(0,\infty)$, then
$\mathfrak v_i(0)\to G_{\alpha,\bmom}(X_0)$. If $i/i_{\mathrm c}\to0$, then $\mathfrak v_i(0)\to1/\sw2$. If
$i/i_{\mathrm c}\to\infty$, then $\mathfrak v_i(0)\sim\gamma\Gamma_\alpha(i/N)$, and if moreover $i/N\to0$,
\[
\mathfrak v_i(0)\sim\frac{4K_\alpha^2}{\alpha-1}\,\frac iB .
\]
\end{enumerate}
\end{theorem}
-/
theorem thm_app_pl_volatility_i {α β : ℝ} {N B : ℕ → ℕ} {c : ℕ → ℝ}
    (R : assum_app_pl_regime α β N B c)
    (cert : Muon.External.GaussianOpNorm) (γstar CSig : ℕ → ℝ)
    (hadm : ∀ n, zeroAdmissible (N n) (B n) (plSpec α (c n) (N n)) (γstar n) (CSig n)) :
    (∀ K : Set ℝ, K ⊆ Ioc 0 1 → IsCompact K → ∀ L : Set ℝ, L ⊆ Ioo 0 1 → IsCompact L →
      ∀ ε > 0, ∀ᶠ n in atTop, ∀ (i : Fin (N n)) (ℓ : ℤ),
        (((i : ℕ) : ℝ) + 1) / (N n : ℝ) ∈ K →
        (ℓ : ℝ) / gammaOf (N n) (B n) ∈ L →
          |cbarZero cert (γstar n) (CSig n) β (B n) (plSpec α (c n) (N n)) i ℓ.natAbs -
            profC α ((((i : ℕ) : ℝ) + 1) / (N n : ℝ)) ((ℓ : ℝ) / gammaOf (N n) (B n))| ≤ ε) ∧
    (∀ K : Set ℝ, K ⊆ Ioc 0 1 → IsCompact K → ∀ ε > 0, ∀ᶠ n in atTop, ∀ (i : Fin (N n)),
      (((i : ℕ) : ℝ) + 1) / (N n : ℝ) ∈ K →
        |vZero cert (γstar n) (CSig n) β (B n) (plSpec α (c n) (N n)) i / gammaOf (N n) (B n) -
          profGamma α ((((i : ℕ) : ℝ) + 1) / (N n : ℝ))| ≤ ε) := by
  have hpart := thm_app_pl_volatility_i_part R (prop_app_pl_vol_zero_hBound cert R)
  constructor
  · intro K hK hKc L hL hLc ε hε
    filter_upwards [hpart.1 K hK hKc L hL hLc ε hε] with n hn
    intro i ℓ hi hℓ
    rw [pg15_cbarZero_eq_CbarPart R cert γstar CSig hadm n i ℓ]
    exact hn i ℓ hi hℓ
  · intro K hK hKc ε hε
    filter_upwards [hpart.2 K hK hKc ε hε] with n hn
    intro i hi
    rw [pg15_vZero_eq_vPart R cert γstar CSig hadm n i]
    exact hn i hi

/-- `thm:app-pl-volatility`(ii) (snapshot `cr-2026-10-23`). Record form for the zero-ridge coefficients `vZero`/`cbarZero`; the part-form hypotheses `hBound`, `hPSD`, `hZero` are discharged by `prop_app_pl_vol_zero_*` and not restated. Statement (LaTeX, verbatim from sections/06-power-law/section.tex):

\begin{theorem}[Volatility crossover and bulk profile]\label{thm:app-pl-volatility}
Assume \cref{assum:app-pl-regime} and let $i=i_N$ be a row sequence.
\begin{enumerate}[label=(\roman*)]
\item (Bulk.) If $i/N\to x\in(0,1]$ and $\ell=\ell_N$ are integers with
$\ell/\gamma\to\tau\in(0,1)$, then
\[
\overline C_{i,\ell}(0)\longrightarrow C_{\alpha,x}(\tau),\qquad \frac{\mathfrak v_i(0)}{\gamma}\longrightarrow\Gamma_\alpha(x),
\]
locally uniformly in $x\in(0,1]$ and $\tau\in(0,1)$.
\item Let $0<\alpha\le1$, let $i\to\infty$, and put
\begin{equation}\label{eqn:app-pl-icv}
i_{\mathrm c,\mathfrak v}\defeq c_0^{2/\alpha}\,i_{\mathrm c,\mathfrak d}=\begin{cases}N\big[(1-\alpha)/(\sw2\gamma\log^2\gamma)\big]^{1/\alpha},&\alpha<1,\\ 9B/(4\sw2\log^3\gamma),&\alpha=1.\end{cases}
\end{equation}
If $i/i_{\mathrm c,\mathfrak v}\to y\in(0,\infty)$, then
$\sw2\,\mathfrak v_i(0)\to1+2c_0y^{\alpha/2}+y^\alpha$, uniformly for $y$ in compact subsets of
$(0,\infty)$. If $i/i_{\mathrm c,\mathfrak v}\to0$, then $\mathfrak v_i(0)\to1/\sw2$. If
$i/i_{\mathrm c,\mathfrak v}\to\infty$, then $\mathfrak v_i(0)\sim\gamma\Gamma_\alpha(i/N)$, and if moreover
$i/N\to0$,
\[
\mathfrak v_i(0)\sim\frac{\gamma(i/N)^\alpha\big[\log((N/i)^\alpha)\big]^2}{1-\alpha}\quad(\alpha<1),\qquad
\mathfrak v_i(0)\sim\frac49\,\frac iB\,\big[\log(N/i)\big]^3\quad(\alpha=1).
\]
\item Let $\alpha>1$ and $i\to\infty$. If $i/i_{\mathrm c}\to X_0\in(0,\infty)$, then
$\mathfrak v_i(0)\to G_{\alpha,\bmom}(X_0)$. If $i/i_{\mathrm c}\to0$, then $\mathfrak v_i(0)\to1/\sw2$. If
$i/i_{\mathrm c}\to\infty$, then $\mathfrak v_i(0)\sim\gamma\Gamma_\alpha(i/N)$, and if moreover $i/N\to0$,
\[
\mathfrak v_i(0)\sim\frac{4K_\alpha^2}{\alpha-1}\,\frac iB .
\]
\end{enumerate}
\end{theorem}
-/
theorem thm_app_pl_volatility_ii {α β : ℝ} {N B : ℕ → ℕ} {c : ℕ → ℝ}
    (R : assum_app_pl_regime α β N B c)
    (cert : Muon.External.GaussianOpNorm) (γstar CSig : ℕ → ℝ)
    (hadm : ∀ n, zeroAdmissible (N n) (B n) (plSpec α (c n) (N n)) (γstar n) (CSig n))
    (hα1 : α ≤ 1) :
    (∀ K : Set ℝ, K ⊆ Ioi 0 → IsCompact K → ∀ ε > 0, ∃ M : ℕ, ∀ᶠ n in atTop,
      ∀ i : Fin (N n), (M : ℝ) ≤ rowIdx i → icvRow β α (B n) i ∈ K →
        |sPow β 2 * vZero cert (γstar n) (CSig n) β (B n) (plSpec α (c n) (N n)) i -
          (1 + 2 * c0 * icvRow β α (B n) i ^ (α / 2) + icvRow β α (B n) i ^ α)| ≤ ε) ∧
    ∀ i : ∀ n, Fin (N n), Tendsto (fun n => rowIdx (i n)) atTop atTop →
      (Tendsto (fun n => icvRow β α (B n) (i n)) atTop (𝓝 0) →
        Tendsto (fun n => vZero cert (γstar n) (CSig n) β (B n) (plSpec α (c n) (N n)) (i n)) atTop (𝓝 (1 / sPow β 2))) ∧
      (Tendsto (fun n => icvRow β α (B n) (i n)) atTop atTop →
        IsEquivalent atTop
          (fun n => vZero cert (γstar n) (CSig n) β (B n) (plSpec α (c n) (N n)) (i n))
          (fun n => gammaOf (N n) (B n) * profGamma α (rowFrac (i n)))) ∧
      (Tendsto (fun n => icvRow β α (B n) (i n)) atTop atTop →
        Tendsto (fun n => rowFrac (i n)) atTop (𝓝 0) → α < 1 →
        IsEquivalent atTop
          (fun n => vZero cert (γstar n) (CSig n) β (B n) (plSpec α (c n) (N n)) (i n))
          (fun n => gammaOf (N n) (B n) * rowFrac (i n) ^ α *
            Real.log (((N n : ℝ) / rowIdx (i n)) ^ α) ^ 2 / (1 - α))) ∧
      (Tendsto (fun n => icvRow β α (B n) (i n)) atTop atTop →
        Tendsto (fun n => rowFrac (i n)) atTop (𝓝 0) → α = 1 →
        IsEquivalent atTop
          (fun n => vZero cert (γstar n) (CSig n) β (B n) (plSpec α (c n) (N n)) (i n))
          (fun n => 4 / 9 * (rowIdx (i n) / (B n : ℝ)) *
            Real.log ((N n : ℝ) / rowIdx (i n)) ^ 3)) := by
  simpa only [pg15_vZero_eq_vPart R cert γstar CSig hadm] using
    thm_app_pl_volatility_ii_part R hα1 (prop_app_pl_vol_zero_hBound cert R)
      (prop_app_pl_vol_zero_hPSD cert R) (prop_app_pl_vol_zero_hZero cert R)

/-- `thm:app-pl-volatility`(iii) (snapshot `cr-2026-10-23`). Record form for the zero-ridge coefficients `vZero`/`cbarZero`; the part-form hypotheses `hBound`, `hPSD`, `hZero` are discharged by `prop_app_pl_vol_zero_*` and not restated. Statement (LaTeX, verbatim from sections/06-power-law/section.tex):

\begin{theorem}[Volatility crossover and bulk profile]\label{thm:app-pl-volatility}
Assume \cref{assum:app-pl-regime} and let $i=i_N$ be a row sequence.
\begin{enumerate}[label=(\roman*)]
\item (Bulk.) If $i/N\to x\in(0,1]$ and $\ell=\ell_N$ are integers with
$\ell/\gamma\to\tau\in(0,1)$, then
\[
\overline C_{i,\ell}(0)\longrightarrow C_{\alpha,x}(\tau),\qquad \frac{\mathfrak v_i(0)}{\gamma}\longrightarrow\Gamma_\alpha(x),
\]
locally uniformly in $x\in(0,1]$ and $\tau\in(0,1)$.
\item Let $0<\alpha\le1$, let $i\to\infty$, and put
\begin{equation}\label{eqn:app-pl-icv}
i_{\mathrm c,\mathfrak v}\defeq c_0^{2/\alpha}\,i_{\mathrm c,\mathfrak d}=\begin{cases}N\big[(1-\alpha)/(\sw2\gamma\log^2\gamma)\big]^{1/\alpha},&\alpha<1,\\ 9B/(4\sw2\log^3\gamma),&\alpha=1.\end{cases}
\end{equation}
If $i/i_{\mathrm c,\mathfrak v}\to y\in(0,\infty)$, then
$\sw2\,\mathfrak v_i(0)\to1+2c_0y^{\alpha/2}+y^\alpha$, uniformly for $y$ in compact subsets of
$(0,\infty)$. If $i/i_{\mathrm c,\mathfrak v}\to0$, then $\mathfrak v_i(0)\to1/\sw2$. If
$i/i_{\mathrm c,\mathfrak v}\to\infty$, then $\mathfrak v_i(0)\sim\gamma\Gamma_\alpha(i/N)$, and if moreover
$i/N\to0$,
\[
\mathfrak v_i(0)\sim\frac{\gamma(i/N)^\alpha\big[\log((N/i)^\alpha)\big]^2}{1-\alpha}\quad(\alpha<1),\qquad
\mathfrak v_i(0)\sim\frac49\,\frac iB\,\big[\log(N/i)\big]^3\quad(\alpha=1).
\]
\item Let $\alpha>1$ and $i\to\infty$. If $i/i_{\mathrm c}\to X_0\in(0,\infty)$, then
$\mathfrak v_i(0)\to G_{\alpha,\bmom}(X_0)$. If $i/i_{\mathrm c}\to0$, then $\mathfrak v_i(0)\to1/\sw2$. If
$i/i_{\mathrm c}\to\infty$, then $\mathfrak v_i(0)\sim\gamma\Gamma_\alpha(i/N)$, and if moreover $i/N\to0$,
\[
\mathfrak v_i(0)\sim\frac{4K_\alpha^2}{\alpha-1}\,\frac iB .
\]
\end{enumerate}
\end{theorem}
-/
theorem thm_app_pl_volatility_iii {α β : ℝ} {N B : ℕ → ℕ} {c : ℕ → ℝ}
    (R : assum_app_pl_regime α β N B c)
    (cert : Muon.External.GaussianOpNorm) (γstar CSig : ℕ → ℝ)
    (hadm : ∀ n, zeroAdmissible (N n) (B n) (plSpec α (c n) (N n)) (γstar n) (CSig n))
    (hα1 : 1 < α) :
    ∀ i : ∀ n, Fin (N n), Tendsto (fun n => rowIdx (i n)) atTop atTop →
      (∀ X0 : ℝ, 0 < X0 → Tendsto (fun n => rowIdx (i n) / icCross α (B n)) atTop (𝓝 X0) →
        Tendsto (fun n => vZero cert (γstar n) (CSig n) β (B n) (plSpec α (c n) (N n)) (i n)) atTop (𝓝 (profG α β X0))) ∧
      (Tendsto (fun n => rowIdx (i n) / icCross α (B n)) atTop (𝓝 0) →
        Tendsto (fun n => vZero cert (γstar n) (CSig n) β (B n) (plSpec α (c n) (N n)) (i n)) atTop (𝓝 (1 / sPow β 2))) ∧
      (Tendsto (fun n => rowIdx (i n) / icCross α (B n)) atTop atTop →
        IsEquivalent atTop (fun n => vZero cert (γstar n) (CSig n) β (B n) (plSpec α (c n) (N n)) (i n))
          (fun n => gammaOf (N n) (B n) * profGamma α (rowFrac (i n)))) ∧
      (Tendsto (fun n => rowIdx (i n) / icCross α (B n)) atTop atTop →
        Tendsto (fun n => rowFrac (i n)) atTop (𝓝 0) →
        IsEquivalent atTop (fun n => vZero cert (γstar n) (CSig n) β (B n) (plSpec α (c n) (N n)) (i n))
          (fun n => 4 * Kc α ^ 2 / (α - 1) * (rowIdx (i n) / (B n : ℝ)))) := by
  simpa only [pg15_vZero_eq_vPart R cert γstar CSig hadm] using
    thm_app_pl_volatility_iii_part R hα1 (prop_app_pl_vol_zero_hBound cert R)
      (prop_app_pl_vol_zero_hZero cert R)

/-! ### Negligible ridge (`prop:app-pl-ridge`): one declaration per transferred statement -/

/-- `prop:app-pl-ridge` (snapshot `cr-2026-10-23`), existence clause. Statement (LaTeX, verbatim from sections/06-power-law/section.tex):

\begin{proposition}[Negligible ridge]\label{prop:app-pl-ridge}
Assume \cref{assum:app-pl-regime}. Let $0<\ridge_N\le\bar z_N$ and let $H_N\ge0$ be
integers with
\begin{equation}\label{eqn:app-pl-ridge-window}
\frac{\ridge_N\,Q_\gamma}{c_NN^{-\alpha}\gamma^2}\to0,\qquad
(1+H_N)\sqrt{D_\star}\,\ridge_N^{1/4}\to0,\qquad
E_\star\,\bmom^{H_N/3}\to0 .
\end{equation}
Then \cref{thm:app-pl-triple,thm:app-pl-drift,thm:app-pl-volatility},
\cref{cor:app-pl-endpoints,cor:app-pl-weighted} hold with $\mathfrak d_i(\ridge_N)$,
$\overline C_{i,\ell}(\ridge_N)$ and $\mathfrak v_i(\ridge_N)$ in place of the zero-ridge
coefficients. Such sequences $(\ridge_N,H_N)$ exist.
\end{proposition}
-/
theorem prop_app_pl_ridge_exists {α β : ℝ} {N B : ℕ → ℕ} {c : ℕ → ℝ}
    (R : assum_app_pl_regime α β N B c) :
    ∃ (ϱ : ℕ → ℝ) (H : ℕ → ℕ), ridgeWindow R ϱ H := by
  let E : ℕ → ℝ := fun n =>
    ridgeEstar β (B n) (plSpec α (c n) (N n)) (R.hNpos n)
  obtain ⟨H, hH⟩ := pg15p4_lag_cutoffs R.hβ0 R.hβ1 E
  let z : ℕ → ℝ := fun n => ridgeZbar β (B n) (plSpec α (c n) (N n))
  let A : ℕ → ℝ := fun n => Qm β (gammaOf (N n) (B n)) /
    (c n * (N n : ℝ) ^ (-α) * gammaOf (N n) (B n) ^ 2)
  let C : ℕ → ℝ := fun n => (1 + (H n : ℝ)) *
    Real.sqrt (ridgeDstar β (B n) (plSpec α (c n) (N n)) (R.hNpos n))
  obtain ⟨ϱ, hϱz, hA, hC⟩ :=
    pg15p4_small_ridges z A C (fun n => pg15p4_ridgeZbar_pos R n)
  refine ⟨ϱ, H, hϱz, ?_, ?_, ?_⟩
  · simpa only [A, div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using hA
  · simpa only [C] using hC
  · simpa only [E] using hH

private lemma pg15p5_Qm_spec {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {m : ℝ} (hm : 0 < m) :
    0 < Qm β m ∧ rW (emaW β) (Qm β m) = m := by
  have hcont : ContinuousOn (rW (emaW β)) (Ici 0) := by
    exact continuousOn_id.mul (lem_app_de_scalar_ii (pg15p4_wseq hβ0.le hβ1)).2.2.1
  have hr0 : rW (emaW β) 0 = 0 :=
    (lem_app_de_scalar_iii (pg15p4_wseq hβ0.le hβ1)).2.2.1
  obtain ⟨b, hb⟩ := (((pg15p4_rW_atTop hβ0 hβ1).eventually_gt_atTop m).and
    (eventually_gt_atTop (0 : ℝ))).exists
  have hmem : m ∈ Icc (rW (emaW β) 0) (rW (emaW β) b) :=
    ⟨by rw [hr0]; exact hm.le, hb.1.le⟩
  obtain ⟨x, hx, hfx⟩ :=
    intermediate_value_Icc hb.2.le (hcont.mono Icc_subset_Ici_self) hmem
  have hxpos : 0 < x := by
    rcases hx.1.eq_or_lt with h | h
    · exfalso
      rw [← h, hr0] at hfx
      linarith
    · exact h
  have hex : ∃ a ∈ Ioi (0 : ℝ), rW (emaW β) a = m := ⟨x, hxpos, hfx⟩
  exact ⟨Function.invFunOn_mem hex, Function.invFunOn_eq hex⟩

private lemma pg15p5_mOf_spec {N B : ℕ} {β : ℝ} (μ : Fin N → ℝ) (hβ0 : 0 < β)
    (hβ1 : β < 1) (hB : 0 < B) (hN : 0 < N) (hanti : Antitone μ)
    (hpos : ∀ i, 0 < μ i) {s : ℝ} (hs : 0 < s) :
    mOf β B μ s ∈ Ioo 0 (gammaOf N B) ∧ sN β B μ (mOf β B μ s) = s := by
  have hbij := (prop_app_pl_branch_i μ hβ0 hβ1 hB hN hanti hpos).2.2.1
  obtain ⟨x, hx, hfx⟩ := hbij.surjOn (show s ∈ Ioi (0 : ℝ) from hs)
  have hex : ∃ a ∈ Ioo (0 : ℝ) (gammaOf N B), sN β B μ a = s := ⟨x, hx, hfx⟩
  unfold mOf
  exact ⟨Function.invFunOn_mem hex, Function.invFunOn_eq hex⟩

private lemma pg15p5_kernel_pt {N B : ℕ} {β : ℝ} (μ : Fin N → ℝ) (hβ0 : 0 < β)
    (hβ1 : β < 1) (hB : 0 < B) (hN : 0 < N) (hanti : Antitone μ)
    (hpos : ∀ i, 0 < μ i) {ν ν' : FiniteMeasure ℝ} {Cs : ℝ}
    (hν : (ν : Measure ℝ) = ENNReal.ofReal ((B : ℝ)⁻¹) • ∑ i, Measure.dirac (μ i))
    (hν' : (ν' : Measure ℝ) = ENNReal.ofReal (gammaOf N B) • Measure.dirac (1 : ℝ))
    (hμCs : ∀ i, μ i ≤ Cs) (h1Cs : 1 ≤ Cs) {z : ℝ} (hz : 0 < z) (i : Fin N) :
    z * Lw (emaW β) (Muon.Drift.branchQ (emaW β) ν ν' z) * μ i * 1 /
      ((z + (branchSol (Fw (emaW β)) ν ν' z).2.2.1 * μ i) *
        (z + (branchSol (Fw (emaW β)) ν ν' z).2.2.2 * 1)) =
      (gammaOf N B)⁻¹ * Gfun β B μ i z := by
  have hγ : 0 < gammaOf N B := by
    unfold gammaOf
    exact div_pos (by exact_mod_cast hN) (by exact_mod_cast hB)
  obtain ⟨hmI, hsm⟩ := pg15p5_mOf_spec μ hβ0 hβ1 hB hN hanti hpos hz
  obtain ⟨-, hbLam, -, -⟩ := def_app_pl_participation_bij μ hB hN hpos
  obtain ⟨hb1, hb2, hb3, -, -, -⟩ :=
    prop_app_pl_branch_ii μ hβ0 hβ1 hB hN hanti hpos hν hν' hμCs h1Cs hz hmI hsm
  unfold Gfun Muon.Drift.branchQ
  generalize mOf β B μ z = m at *
  obtain ⟨hm0, hmγ⟩ := hmI
  have hmγ' : 0 < gammaOf N B - m := sub_pos.2 hmγ
  have hL : 0 < partLam B μ m := hbLam.mapsTo ⟨hm0, hmγ⟩
  have hQ : 0 < Qm β m := (pg15p5_Qm_spec hβ0 hβ1 hm0).1
  have hrQ : rW (emaW β) (Qm β m) = m := (pg15p5_Qm_spec hβ0 hβ1 hm0).2
  have hFQ : Fw (emaW β) (Qm β m) = m / Qm β m := by
    have h' : Qm β m * Fw (emaW β) (Qm β m) = m := hrQ
    exact eq_div_of_mul_eq hQ.ne' (by rw [mul_comm]; exact h')
  have hkey : z * (Qm β m * partLam B μ m) = (gammaOf N B - m) * m := by
    have hQL : Qm β m * partLam B μ m ≠ 0 := (mul_pos hQ hL).ne'
    rw [← hsm]
    unfold sN
    exact div_mul_cancel₀ _ hQL
  have hμ1 : 0 < 1 + partLam B μ m * μ i := by
    have := mul_pos hL (hpos i)
    linarith
  rw [hb1, hb2, hb3, hFQ]
  unfold partF
  have e1 : z + z * partLam B μ m * μ i = z * (1 + partLam B μ m * μ i) := by ring
  have e2 : z + z * m / (gammaOf N B - m) * 1 = z * gammaOf N B / (gammaOf N B - m) := by
    field_simp
    ring
  rw [e1, e2]
  field_simp [hz.ne', hm0.ne', hmγ'.ne', hQ.ne', hL.ne', hγ.ne', hμ1.ne']
  congr 1
  linear_combination (-(Lw (emaW β) (Qm β m) * μ i)) * hkey

private lemma pg15p5_dirac_compl {a Cs : ℝ} (h : a ∈ Icc (0 : ℝ) Cs) :
    Measure.dirac a (Icc 0 Cs)ᶜ = 0 := by
  rw [Measure.dirac_apply' _ measurableSet_Icc.compl]
  exact Set.indicator_of_notMem (show a ∉ (Icc (0 : ℝ) Cs)ᶜ from fun hh => hh h) _

private lemma pg15p5_classK {N B : ℕ} (μ : Fin N → ℝ) (hB : 0 < B) (hN : 0 < N)
    {ν ν' : FiniteMeasure ℝ} {Cs : ℝ}
    (hν : (ν : Measure ℝ) = ENNReal.ofReal ((B : ℝ)⁻¹) • ∑ i, Measure.dirac (μ i))
    (hν' : (ν' : Measure ℝ) = ENNReal.ofReal (gammaOf N B) • Measure.dirac (1 : ℝ))
    (hpos : ∀ i, 0 < μ i) (hμCs : ∀ i, μ i ≤ Cs) (h1Cs : 1 ≤ Cs) :
    (ν, ν') ∈ classK Cs (gammaOf N B) := by
  have hγ : 0 ≤ gammaOf N B := by
    unfold gammaOf
    positivity
  have hd : ∀ i, Measure.dirac (μ i) (Icc 0 Cs) = 1 := fun i =>
    Measure.dirac_apply_of_mem ⟨(hpos i).le, hμCs i⟩
  have hdc : ∀ i, Measure.dirac (μ i) (Icc 0 Cs)ᶜ = 0 := fun i =>
    pg15p5_dirac_compl ⟨(hpos i).le, hμCs i⟩
  have h1mem : (1 : ℝ) ∈ Icc (0 : ℝ) Cs := ⟨zero_le_one, h1Cs⟩
  simp only [classK, Set.mem_setOf_eq]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hν]
    simp only [Measure.smul_apply, Measure.finsetSum_apply, hd, smul_eq_mul,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (inv_nonneg.2 (Nat.cast_nonneg B))]
    apply le_of_eq
    congr 1
    unfold gammaOf
    ring
  · rw [hν]
    simp only [Measure.smul_apply, Measure.finsetSum_apply, hdc, smul_eq_mul,
      Finset.sum_const_zero, mul_zero]
  · rw [hν']
    simp only [Measure.smul_apply, Measure.dirac_apply_of_mem h1mem, smul_eq_mul, mul_one]
    exact le_rfl
  · rw [hν', Measure.smul_apply, pg15p5_dirac_compl h1mem, smul_zero]

private lemma pg15p5_Lw_bounds {w : ℕ → ℝ} (hw : WeightClass w) {q : ℝ} (hq : 0 ≤ q) :
    0 ≤ Lw w q ∧ Lw w q ≤ 1 := by
  obtain ⟨⟨hw0, hwS, -⟩, -, hw1⟩ := hw
  have hJ0 : ∀ j, 0 ≤ Muon.DetEquiv.J (w j ^ 2 * q) := fun j => by
    unfold Muon.DetEquiv.J
    apply integral_nonneg
    intro g
    have hm := mul_nonneg (mul_nonneg (sq_nonneg (w j)) hq) (sq_nonneg g)
    exact div_nonneg (sq_nonneg g) (by linarith)
  have hJ1 : ∀ j, Muon.DetEquiv.J (w j ^ 2 * q) ≤ 1 := fun j => by
    unfold Muon.DetEquiv.J
    have hx : 0 ≤ w j ^ 2 * q := mul_nonneg (sq_nonneg _) hq
    have hpt : ∀ g : ℝ, g ^ 2 / (1 + w j ^ 2 * q * g ^ 2) ≤ g ^ 2 := fun g => by
      have hm := mul_nonneg hx (sq_nonneg g)
      exact div_le_self (sq_nonneg g) (by linarith)
    calc
      (∫ g, g ^ 2 / (1 + w j ^ 2 * q * g ^ 2) ∂(ProbabilityTheory.gaussianReal 0 1)) ≤
          ∫ g, g ^ 2 ∂(ProbabilityTheory.gaussianReal 0 1) := integral_mono_of_nonneg
            (Filter.Eventually.of_forall fun g => div_nonneg (sq_nonneg g) (by
              have hm := mul_nonneg hx (sq_nonneg g); linarith))
            (Muon.Foundations.gaussian_integrable_pow 2) (Filter.Eventually.of_forall hpt)
      _ = 1 := Muon.Foundations.gaussian_moment_two
  have hterm : ∀ j, 0 ≤ w j * Muon.DetEquiv.J (w j ^ 2 * q) :=
    fun j => mul_nonneg (hw0 j) (hJ0 j)
  have hle : ∀ j, w j * Muon.DetEquiv.J (w j ^ 2 * q) ≤ w j :=
    fun j => mul_le_of_le_one_right (hw0 j) (hJ1 j)
  have hS : Summable (fun j => w j * Muon.DetEquiv.J (w j ^ 2 * q)) :=
    Summable.of_nonneg_of_le hterm hle hwS
  refine ⟨tsum_nonneg hterm, ?_⟩
  calc
    Lw w q = ∑' j, w j * Muon.DetEquiv.J (w j ^ 2 * q) := rfl
    _ ≤ ∑' j, w j := hS.tsum_le_tsum hle hwS
    _ ≤ 1 := hw1

private lemma pg15p5_branch_data {N B : ℕ} {β : ℝ} (μ : Fin N → ℝ)
    (hβ0 : 0 < β) (hβ1 : β < 1) (hB : 0 < B) (hN : 0 < N) (hpos : ∀ i, 0 < μ i)
    {ν ν' : FiniteMeasure ℝ} {Cs ϱ : ℝ}
    (hν : (ν : Measure ℝ) = ENNReal.ofReal ((B : ℝ)⁻¹) • ∑ i, Measure.dirac (μ i))
    (hν' : (ν' : Measure ℝ) = ENNReal.ofReal (gammaOf N B) • Measure.dirac (1 : ℝ))
    (hμCs : ∀ i, μ i ≤ Cs) (h1Cs : 1 ≤ Cs) (hϱ : 0 < ϱ) :
    Continuous (fun u : ℝ => (branchSol (Fw (emaW β)) ν ν' (ϱ + u ^ 2)).2.2.1) ∧
    Continuous (fun u : ℝ => (branchSol (Fw (emaW β)) ν ν' (ϱ + u ^ 2)).2.2.2) ∧
    Continuous (fun u : ℝ => Lw (emaW β)
      (Muon.Drift.branchQ (emaW β) ν ν' (ϱ + u ^ 2))) ∧
    (∀ u : ℝ, 0 ≤ (branchSol (Fw (emaW β)) ν ν' (ϱ + u ^ 2)).2.2.1) ∧
    (∀ u : ℝ, 0 ≤ (branchSol (Fw (emaW β)) ν ν' (ϱ + u ^ 2)).2.2.2) ∧
    (∀ u : ℝ, 0 ≤ Lw (emaW β) (Muon.Drift.branchQ (emaW β) ν ν' (ϱ + u ^ 2)) ∧
      Lw (emaW β) (Muon.Drift.branchQ (emaW β) ν ν' (ϱ + u ^ 2)) ≤ 1) := by
  have hC : 0 < Cs := one_pos.trans_le h1Cs
  have hγ : 0 < gammaOf N B := by unfold gammaOf; positivity
  have hp := pg15p5_classK μ hB hN hν hν' hpos hμCs h1Cs
  have hw := Muon.Drift.emaW_weightClass β ⟨hβ0.le, hβ1⟩
  have hs : Continuous (fun u : ℝ => ϱ + u ^ 2) := by fun_prop
  have hspos : ∀ u : ℝ, 0 < ϱ + u ^ 2 := fun u => by positivity
  have hcontP := (thm_app_de_branch_ii (Fw_admissible hw.1) hC hγ).1
  have hS : Continuous (fun u : ℝ => branchSol (Fw (emaW β)) ν ν' (ϱ + u ^ 2)) := by
    exact hcontP.comp_continuous (hs.prodMk continuous_const) (fun u => ⟨hspos u, hp⟩)
  have c1 : Continuous (fun u : ℝ => (branchSol (Fw (emaW β)) ν ν' (ϱ + u ^ 2)).1) :=
    continuous_fst.comp hS
  have c2 : Continuous (fun u : ℝ => (branchSol (Fw (emaW β)) ν ν' (ϱ + u ^ 2)).2.1) :=
    continuous_fst.comp (continuous_snd.comp hS)
  have c3 : Continuous (fun u : ℝ => (branchSol (Fw (emaW β)) ν ν' (ϱ + u ^ 2)).2.2.1) :=
    continuous_fst.comp (continuous_snd.comp (continuous_snd.comp hS))
  have c4 : Continuous (fun u : ℝ => (branchSol (Fw (emaW β)) ν ν' (ϱ + u ^ 2)).2.2.2) :=
    continuous_snd.comp (continuous_snd.comp (continuous_snd.comp hS))
  have hq : Continuous (fun u : ℝ => Muon.Drift.branchQ (emaW β) ν ν' (ϱ + u ^ 2)) := by
    unfold Muon.Drift.branchQ
    exact (hs.mul c1).mul c2
  have hnonneg : ∀ u : ℝ,
      0 ≤ (branchSol (Fw (emaW β)) ν ν' (ϱ + u ^ 2)).1 ∧
      0 ≤ (branchSol (Fw (emaW β)) ν ν' (ϱ + u ^ 2)).2.1 ∧
      0 ≤ (branchSol (Fw (emaW β)) ν ν' (ϱ + u ^ 2)).2.2.1 ∧
      0 ≤ (branchSol (Fw (emaW β)) ν ν' (ϱ + u ^ 2)).2.2.2 := fun u => by
    obtain ⟨a, b, c, d, -⟩ := branchSol_spec (Fw_admissible hw.1) hC hγ hp (hspos u)
    exact ⟨a, b, c, d⟩
  have hqnn : ∀ u : ℝ, 0 ≤ Muon.Drift.branchQ (emaW β) ν ν' (ϱ + u ^ 2) := fun u => by
    unfold Muon.Drift.branchQ
    exact mul_nonneg (mul_nonneg (hspos u).le (hnonneg u).1) (hnonneg u).2.1
  have hL : Continuous (fun u : ℝ => Lw (emaW β)
      (Muon.Drift.branchQ (emaW β) ν ν' (ϱ + u ^ 2))) :=
    (lem_app_de_scalar_ii hw.1).2.2.2.1.comp_continuous hq (fun u => hqnn u)
  exact ⟨c3, c4, hL, fun u => (hnonneg u).2.2.1, fun u => (hnonneg u).2.2.2,
    fun u => pg15p5_Lw_bounds hw (hqnn u)⟩

private lemma pg15p5_ioi_integrable {ϱ : ℝ} (hϱ : 0 < ϱ) :
    IntegrableOn (fun u : ℝ => (ϱ + u ^ 2)⁻¹) (Ioi 0) := by
  have hr : 0 < Real.sqrt ϱ := Real.sqrt_pos.mpr hϱ
  have hb : 0 < (Real.sqrt ϱ)⁻¹ := inv_pos.mpr hr
  have hfun : (fun u : ℝ => (ϱ + u ^ 2)⁻¹) =
      fun u => ϱ⁻¹ * (fun x : ℝ => (1 + x ^ 2)⁻¹) ((Real.sqrt ϱ)⁻¹ * u) := by
    funext u
    have : ϱ + u ^ 2 = ϱ * (1 + ((Real.sqrt ϱ)⁻¹ * u) ^ 2) := by
      rw [mul_pow, inv_pow, Real.sq_sqrt hϱ.le]
      field_simp
    rw [this, mul_inv]
  rw [hfun]
  refine Integrable.const_mul ?_ _
  exact (integrableOn_Ioi_comp_mul_left_iff (fun x : ℝ => (1 + x ^ 2)⁻¹) 0 hb).mpr
    (by simpa using integrable_inv_one_add_sq.integrableOn)

private lemma pg15p5_kernel_integrable {ϱ : ℝ} (hϱ : 0 < ϱ) {a b L : ℝ → ℝ}
    (hac : Continuous a) (hbc : Continuous b) (hLc : Continuous L)
    (ha : ∀ u, 0 ≤ a u) (hb : ∀ u, 0 ≤ b u) (hL0 : ∀ u, 0 ≤ L u)
    (hL1 : ∀ u, L u ≤ 1) {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    IntegrableOn (fun u : ℝ => (ϱ + u ^ 2) * L u * x * y /
      ((ϱ + u ^ 2 + a u * x) * (ϱ + u ^ 2 + b u * y))) (Ioi 0) := by
  have hcont : Continuous (fun u : ℝ => (ϱ + u ^ 2) * L u * x * y /
      ((ϱ + u ^ 2 + a u * x) * (ϱ + u ^ 2 + b u * y))) := by
    apply Continuous.div <;> try fun_prop
    intro u
    have h1 : 0 < ϱ + u ^ 2 + a u * x := by nlinarith [sq_nonneg u, mul_nonneg (ha u) hx]
    have h2 : 0 < ϱ + u ^ 2 + b u * y := by nlinarith [sq_nonneg u, mul_nonneg (hb u) hy]
    exact (mul_pos h1 h2).ne'
  have hg : IntegrableOn (fun u : ℝ => x * y * (ϱ + u ^ 2)⁻¹) (Ioi 0) :=
    (pg15p5_ioi_integrable hϱ).const_mul (x * y)
  refine Integrable.mono' hg hcont.aestronglyMeasurable.restrict ?_
  exact Filter.Eventually.of_forall fun u => by
    have hz : 0 < ϱ + u ^ 2 := by positivity
    have h1 : 0 < ϱ + u ^ 2 + a u * x := by nlinarith [mul_nonneg (ha u) hx]
    have h2 : 0 < ϱ + u ^ 2 + b u * y := by nlinarith [mul_nonneg (hb u) hy]
    have hnum : 0 ≤ (ϱ + u ^ 2) * L u * x * y :=
      mul_nonneg (mul_nonneg (mul_nonneg hz.le (hL0 u)) hx) hy
    rw [Real.norm_of_nonneg (div_nonneg hnum (mul_pos h1 h2).le), ← div_eq_mul_inv,
      div_le_div_iff₀ (mul_pos h1 h2) hz]
    have hd : (ϱ + u ^ 2) * (ϱ + u ^ 2) ≤
        (ϱ + u ^ 2 + a u * x) * (ϱ + u ^ 2 + b u * y) :=
      mul_le_mul (by nlinarith [mul_nonneg (ha u) hx]) (by nlinarith [mul_nonneg (hb u) hy])
        hz.le h1.le
    have hxy : 0 ≤ x * y := mul_nonneg hx hy
    calc
      (ϱ + u ^ 2) * L u * x * y * (ϱ + u ^ 2) ≤
          x * y * ((ϱ + u ^ 2) * (ϱ + u ^ 2)) := by
            rw [show (ϱ + u ^ 2) * L u * x * y * (ϱ + u ^ 2) =
              (x * y * ((ϱ + u ^ 2) * (ϱ + u ^ 2))) * L u by ring]
            exact mul_le_of_le_one_right (mul_nonneg hxy (mul_nonneg hz.le hz.le)) (hL1 u)
      _ ≤ x * y * ((ϱ + u ^ 2 + a u * x) * (ϱ + u ^ 2 + b u * y)) :=
        mul_le_mul_of_nonneg_left hd hxy

private lemma pg15p5_drift_wellPosed {α β : ℝ} {N B : ℕ → ℕ} {c : ℕ → ℝ}
    (R : assum_app_pl_regime α β N B c) (ν ν' : ℕ → FiniteMeasure ℝ)
    (hν : ∀ n, (ν n : Measure ℝ) =
      ENNReal.ofReal ((B n : ℝ)⁻¹) • ∑ i : Fin (N n), Measure.dirac (plSpec α (c n) (N n) i))
    (hν' : ∀ n, (ν' n : Measure ℝ) =
      ENNReal.ofReal (gammaOf (N n) (B n)) • Measure.dirac (1 : ℝ))
    (ϱ : ℕ → ℝ) (hϱ : ∀ n, 0 < ϱ n) : ridgeDriftWellPosed R ν ν' ϱ := by
  intro n i
  let μ := plSpec α (c n) (N n)
  let Cs := max 1 (∑ j : Fin (N n), μ j)
  have hpos : ∀ j, 0 < μ j := fun j => pg15_plSpec_pos (R.hcpos n) j
  have hμCs : ∀ j, μ j ≤ Cs := by
    intro j
    apply le_trans (Finset.single_le_sum (fun k _ => (hpos k).le) (Finset.mem_univ j))
    exact le_max_right _ _
  have h1Cs : 1 ≤ Cs := le_max_left _ _
  obtain ⟨hac, hbc, hLc, ha, hb, hLb⟩ := pg15p5_branch_data μ R.hβ0 R.hβ1
    (R.hBpos n) (R.hNpos n) hpos (hν n) (hν' n) hμCs h1Cs (hϱ n)
  exact pg15p5_kernel_integrable (hϱ n) hac hbc hLc ha hb
    (fun u => (hLb u).1) (fun u => (hLb u).2) (hpos i).le zero_le_one

private lemma pg15p5_aN_sq {α c : ℝ} (hc : 0 < c) {N : ℕ} (hN : 0 < N) :
    aN α c N ^ 2 = c * (N : ℝ) ^ (-α) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  unfold aN
  rw [mul_pow, Real.sq_sqrt hc.le, ← Real.rpow_natCast, ← Real.rpow_mul hNr.le]
  congr 2
  push_cast
  ring

private lemma pg15p5_scale_sqrt {α β c ϱ : ℝ} {N B : ℕ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hc : 0 < c) (hϱ : 0 < ϱ) (hN : 0 < N) (hB : 0 < B) :
    Real.sqrt (ϱ * Qm β (gammaOf N B) /
        (c * (N : ℝ) ^ (-α) * gammaOf N B ^ 2)) =
      Real.sqrt ϱ * Real.sqrt (Qm β (gammaOf N B)) /
        (aN α c N * gammaOf N B) := by
  have hγ : 0 < gammaOf N B := by
    unfold gammaOf
    exact div_pos (by exact_mod_cast hN) (by exact_mod_cast hB)
  have hQ : 0 < Qm β (gammaOf N B) := pg15p4_Qm_pos hβ0 hβ1 hγ
  have ha : 0 < aN α c N := by
    unfold aN
    exact mul_pos (Real.sqrt_pos.2 hc) (Real.rpow_pos_of_pos (by exact_mod_cast hN) _)
  have hden : 0 < c * (N : ℝ) ^ (-α) * gammaOf N B ^ 2 := by positivity
  have hL : 0 ≤ Real.sqrt (ϱ * Qm β (gammaOf N B) /
      (c * (N : ℝ) ^ (-α) * gammaOf N B ^ 2)) := Real.sqrt_nonneg _
  have hR : 0 ≤ Real.sqrt ϱ * Real.sqrt (Qm β (gammaOf N B)) /
      (aN α c N * gammaOf N B) := by positivity
  rw [← sq_eq_sq₀ hL hR, Real.sq_sqrt (div_nonneg (mul_nonneg hϱ.le hQ.le) hden.le),
    div_pow, mul_pow, Real.sq_sqrt hϱ.le, Real.sq_sqrt hQ.le]
  rw [mul_pow, pg15p5_aN_sq hc hN]

private lemma pg15p5_Qm_eventually_lower {α β : ℝ} {N B : ℕ → ℕ} {c : ℕ → ℝ}
    (R : assum_app_pl_regime α β N B c) :
    ∀ᶠ n in atTop, Qm β 1 ≤ Qm β (gammaOf (N n) (B n)) := by
  have hq1 := pg15p5_Qm_spec R.hβ0 R.hβ1 (zero_lt_one : (0 : ℝ) < 1)
  filter_upwards [R.hγ.eventually_ge_atTop 1] with n hn
  have hγ : 0 < gammaOf (N n) (B n) := by
    unfold gammaOf
    exact div_pos (by exact_mod_cast R.hNpos n) (by exact_mod_cast R.hBpos n)
  have hqγ := pg15p5_Qm_spec R.hβ0 R.hβ1 hγ
  change 1 ≤ gammaOf (N n) (B n) at hn
  by_contra hnot
  have hlt : Qm β (gammaOf (N n) (B n)) < Qm β 1 := lt_of_not_ge hnot
  have hs := (lem_app_de_scalar_iii (pg15p4_wseq R.hβ0.le R.hβ1)).2.1
    (Set.mem_Ici.2 hqγ.1.le) (Set.mem_Ici.2 hq1.1.le) hlt
  rw [hqγ.2, hq1.2] at hs
  linarith

private lemma pg15p5_drift_ratio_error {α β : ℝ} {N B : ℕ → ℕ} {c : ℕ → ℝ}
    (R : assum_app_pl_regime α β N B c) (ν ν' : ℕ → FiniteMeasure ℝ)
    (hν : ∀ n, (ν n : Measure ℝ) =
      ENNReal.ofReal ((B n : ℝ)⁻¹) • ∑ i : Fin (N n), Measure.dirac (plSpec α (c n) (N n) i))
    (hν' : ∀ n, (ν' n : Measure ℝ) =
      ENNReal.ofReal (gammaOf (N n) (B n)) • Measure.dirac (1 : ℝ))
    (ϱ : ℕ → ℝ) (H : ℕ → ℕ) (hW : ridgeWindow R ϱ H) :
    ∀ ε > 0, ∀ᶠ n in atTop, ∀ i : Fin (N n),
      |dRidge β (ν n) (ν' n) (plSpec α (c n) (N n)) i (ϱ n) /
          dHatDrift α β (c n) (N n) (B n) i -
        dZero β (B n) (plSpec α (c n) (N n)) i /
          dHatDrift α β (c n) (N n) (B n) i| ≤ ε := by
  obtain ⟨C, hC⟩ := prop_app_pl_drift_zero_ii_kernel R.hβ0 R.hβ1
  obtain ⟨κ, hκ, hκall⟩ := approx_drift_lower (α := α) (β := β)
  have hκlower := hκall N B c R
  have hq1 := pg15p5_Qm_spec R.hβ0 R.hβ1 (zero_lt_one : (0 : ℝ) < 1)
  let X : ℕ → ℝ := fun n => ϱ n * Qm β (gammaOf (N n) (B n)) /
    (c n * (N n : ℝ) ^ (-α) * gammaOf (N n) (B n) ^ 2)
  have hX : Tendsto X atTop (𝓝 0) := hW.2.1
  have hsqrtX : Tendsto (fun n => Real.sqrt (X n)) atTop (𝓝 0) := by
    convert Real.continuous_sqrt.continuousAt.tendsto.comp hX using 1 <;>
      simp [Function.comp_def]
  let K : ℝ := |C| * Real.sqrt 2 / κ * (1 / Real.sqrt (Qm β 1) + 1)
  have hKsqrt : Tendsto (fun n => K * Real.sqrt (X n)) atTop (𝓝 0) := by
    simpa using tendsto_const_nhds.mul hsqrtX
  intro ε hε
  have hev : ∀ᶠ n in atTop, |K * Real.sqrt (X n)| < ε := by
    simpa [Real.dist_eq] using hKsqrt.eventually (Metric.ball_mem_nhds 0 hε)
  filter_upwards [hev, hκlower, pg15p5_Qm_eventually_lower R] with n hn hlow hQlower
  intro i
  have hρ := (hW.1 n).1
  have hγ : 0 < gammaOf (N n) (B n) := by
    unfold gammaOf
    exact div_pos (by exact_mod_cast R.hNpos n) (by exact_mod_cast R.hBpos n)
  have hQ : 0 < Qm β (gammaOf (N n) (B n)) := pg15p4_Qm_pos R.hβ0 R.hβ1 hγ
  have ha : 0 < aN α (c n) (N n) := by
    unfold aN
    exact mul_pos (Real.sqrt_pos.2 (R.hcpos n))
      (Real.rpow_pos_of_pos (by exact_mod_cast R.hNpos n) _)
  have hd : 0 < dHatDrift α β (c n) (N n) (B n) i := pg15_dHat_pos R n i
  have hsQ1 : 0 < Real.sqrt (Qm β 1) := Real.sqrt_pos.2 hq1.1
  have hsQle : Real.sqrt (Qm β 1) ≤ Real.sqrt (Qm β (gammaOf (N n) (B n))) :=
    Real.sqrt_le_sqrt hQlower
  have hone : 1 + Real.sqrt (Qm β (gammaOf (N n) (B n))) ≤
      (1 / Real.sqrt (Qm β 1) + 1) * Real.sqrt (Qm β (gammaOf (N n) (B n))) := by
    have hdiv : 1 ≤ Real.sqrt (Qm β (gammaOf (N n) (B n))) / Real.sqrt (Qm β 1) := by
      apply (le_div_iff₀ hsQ1).2
      simpa using hsQle
    calc
      1 + Real.sqrt (Qm β (gammaOf (N n) (B n))) ≤
          Real.sqrt (Qm β (gammaOf (N n) (B n))) / Real.sqrt (Qm β 1) +
            Real.sqrt (Qm β (gammaOf (N n) (B n))) := add_le_add hdiv le_rfl
      _ = (1 / Real.sqrt (Qm β 1) + 1) *
          Real.sqrt (Qm β (gammaOf (N n) (B n))) := by ring
  have hpert := hC (N n) (B n) (plSpec α (c n) (N n)) (ν n) (ν' n)
    (max 1 (∑ j : Fin (N n), plSpec α (c n) (N n) j)) (R.hBpos n) (R.hNpos n)
    (pg15_plSpec_anti R.hα (R.hcpos n)) (fun j => pg15_plSpec_pos (R.hcpos n) j)
    (fun j => le_trans (Finset.single_le_sum
      (fun k _ => (pg15_plSpec_pos (R.hcpos n) k).le) (Finset.mem_univ j)) (le_max_right _ _))
    (le_max_left _ _) (hν n) (hν' n) (ϱ n) hρ i
  have hCbound : |dRidge β (ν n) (ν' n) (plSpec α (c n) (N n)) i (ϱ n) -
      dZero β (B n) (plSpec α (c n) (N n)) i| ≤
      |C| / gammaOf (N n) (B n) * Real.sqrt (ϱ n) *
        (1 + Real.sqrt (Qm β (gammaOf (N n) (B n)))) := by
    exact hpert.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right (le_abs_self C) hγ.le)
        (Real.sqrt_nonneg _)) (by positivity))
  have hdenlower : κ * aN α (c n) (N n) / Real.sqrt 2 ≤
      dHatDrift α β (c n) (N n) (B n) i := by
    unfold dHatDrift
    exact div_le_div_of_nonneg_right (hlow i) (Real.sqrt_nonneg _)
  have hmain : |dRidge β (ν n) (ν' n) (plSpec α (c n) (N n)) i (ϱ n) /
        dHatDrift α β (c n) (N n) (B n) i -
      dZero β (B n) (plSpec α (c n) (N n)) i /
        dHatDrift α β (c n) (N n) (B n) i| ≤ K * Real.sqrt (X n) := by
    rw [← sub_div, abs_div, abs_of_pos hd]
    calc
      _ ≤ (|C| / gammaOf (N n) (B n) * Real.sqrt (ϱ n) *
          (1 + Real.sqrt (Qm β (gammaOf (N n) (B n))))) /
          dHatDrift α β (c n) (N n) (B n) i := div_le_div_of_nonneg_right hCbound hd.le
      _ ≤ (|C| / gammaOf (N n) (B n) * Real.sqrt (ϱ n) *
          (1 + Real.sqrt (Qm β (gammaOf (N n) (B n))))) /
          (κ * aN α (c n) (N n) / Real.sqrt 2) := by
            apply div_le_div_of_nonneg_left (by positivity) (by positivity) hdenlower
      _ ≤ (|C| / gammaOf (N n) (B n) * Real.sqrt (ϱ n) *
          ((1 / Real.sqrt (Qm β 1) + 1) *
            Real.sqrt (Qm β (gammaOf (N n) (B n))))) /
          (κ * aN α (c n) (N n) / Real.sqrt 2) := by
            gcongr
      _ = K * Real.sqrt (X n) := by
            rw [show Real.sqrt (X n) = Real.sqrt (ϱ n) *
                Real.sqrt (Qm β (gammaOf (N n) (B n))) /
                  (aN α (c n) (N n) * gammaOf (N n) (B n)) by
              exact pg15p5_scale_sqrt R.hβ0 R.hβ1 (R.hcpos n) hρ
                (R.hNpos n) (R.hBpos n)]
            simp only [K]
            field_simp [hγ.ne', ha.ne', hκ.ne', hsQ1.ne']
  exact hmain.trans_lt (by simpa [abs_of_nonneg (by positivity : 0 ≤ K * Real.sqrt (X n))] using hn) |>.le

private lemma pg15p5_D_le (β : ℝ) (B : ℕ) {N : ℕ} (μ : Fin N → ℝ) (hN : 0 < N)
    (i : Fin N) : plDcoef β B μ hN i ≤ ridgeDstar β B μ hN := by
  unfold ridgeDstar
  exact le_ciSup (Finite.bddAbove_range _) i

private lemma pg15p5_E_le (β : ℝ) (B : ℕ) {N : ℕ} (μ : Fin N → ℝ) (hN : 0 < N)
    (i : Fin N) (hz : 0 ≤ ridgeZbar β B μ) :
    plEi β B μ hN i (ridgeZbar β B μ) ≤ ridgeEstar β B μ hN := by
  unfold plEi ridgeEstar
  exact add_le_add le_rfl (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (pg15p5_D_le β B μ hN i)) (by norm_num))
    (Real.rpow_nonneg hz _))

private lemma pg15p5_vol_wellPosed {α β : ℝ} {N B : ℕ → ℕ} {c : ℕ → ℝ}
    (R : assum_app_pl_regime α β N B c) (cert : Muon.External.GaussianOpNorm)
    (γstar CSig : ℕ → ℝ)
    (hadm : ∀ n, zeroAdmissible (N n) (B n) (plSpec α (c n) (N n)) (γstar n) (CSig n))
    (ϱ : ℕ → ℝ) (hϱ : ∀ n, 0 < ϱ n ∧
      ϱ n ≤ ridgeZbar β (B n) (plSpec α (c n) (N n))) :
    ridgeVolWellPosed R cert γstar CSig ϱ := by
  constructor
  · intro n i ℓ
    rcases hadm n with ⟨hγ, hμC, hC1⟩
    have hz := pg15p4_ridgeZbar_pos R n
    have hrow := (prop_app_pl_vol_zero_i cert (γstar n) (CSig n) (R.hBpos n) (R.hNpos n)
      (plSpec α (c n) (N n)) (pg15_plSpec_anti R.hα (R.hcpos n))
      (fun j => pg15_plSpec_pos (R.hcpos n) j) R.hβ0 R.hβ1 hγ hμC hC1 i hz
      (min_le_left _ _)).1
    refine ⟨Muon.Volatility.lagResp cert (γstar n) (CSig n) β ℓ (B n)
      (plSpec α (c n) (N n)) (fun _ : Fin (N n) => (1 : ℝ)) (Pi.single i 1)
      (fun _ : Fin (N n) => (1 : ℝ)) (Muon.Volatility.omegaF (ϱ n))
      (Muon.Volatility.omegaF (ϱ n)), ?_⟩
    simpa only [plLagExists, Filter.prod_atTop_atTop_eq] using hrow ℓ (ϱ n) (hϱ n).1
  · intro n i
    rcases hadm n with ⟨hγ, hμC, hC1⟩
    have hz := pg15p4_ridgeZbar_pos R n
    exact (prop_app_pl_vol_zero_ii cert (γstar n) (CSig n) (R.hBpos n) (R.hNpos n)
      (plSpec α (c n) (N n)) (pg15_plSpec_anti R.hα (R.hcpos n))
      (fun j => pg15_plSpec_pos (R.hcpos n) j) R.hβ0 R.hβ1 hγ hμC hC1 i hz
      (min_le_left _ _)).2.1 (ϱ n) (hϱ n).1 (hϱ n).2

private lemma pg15p5_vol_error {α β : ℝ} {N B : ℕ → ℕ} {c : ℕ → ℝ}
    (R : assum_app_pl_regime α β N B c) (cert : Muon.External.GaussianOpNorm)
    (γstar CSig : ℕ → ℝ)
    (hadm : ∀ n, zeroAdmissible (N n) (B n) (plSpec α (c n) (N n)) (γstar n) (CSig n))
    (ϱ : ℕ → ℝ) (H : ℕ → ℕ) (hW : ridgeWindow R ϱ H) :
    ∀ ε > 0, ∀ᶠ n in atTop, ∀ i : Fin (N n),
      |ridgeV cert (γstar n) (CSig n) β (B n) (plSpec α (c n) (N n)) i (ϱ n) -
        vZero cert (γstar n) (CSig n) β (B n) (plSpec α (c n) (N n)) i| ≤ ε := by
  let U : ℕ → ℝ := fun n => (1 + (H n : ℝ)) *
    Real.sqrt (ridgeDstar β (B n) (plSpec α (c n) (N n)) (R.hNpos n)) *
    ϱ n ^ ((1 : ℝ) / 4)
  let V : ℕ → ℝ := fun n =>
    ridgeEstar β (B n) (plSpec α (c n) (N n)) (R.hNpos n) * β ^ ((H n : ℝ) / 3)
  let K : ℝ := 4 * β ^ ((1 : ℝ) / 3) / (1 - β ^ ((1 : ℝ) / 3))
  have hlim : Tendsto (fun n => 4 * U n + K * V n) atTop (𝓝 0) := by
    simpa only [mul_zero, add_zero] using (tendsto_const_nhds.mul hW.2.2.1).add
      (tendsto_const_nhds.mul hW.2.2.2)
  intro ε hε
  have hev : ∀ᶠ n in atTop, |4 * U n + K * V n| < ε := by
    simpa [Real.dist_eq] using hlim.eventually (Metric.ball_mem_nhds 0 hε)
  filter_upwards [hev] with n hn
  intro i
  rcases hadm n with ⟨hγadm, hμC, hC1⟩
  have hρ := (hW.1 n).1
  have hρz := (hW.1 n).2
  have hz := pg15p4_ridgeZbar_pos R n
  have hraw := (prop_app_pl_vol_zero_ii cert (γstar n) (CSig n) (R.hBpos n) (R.hNpos n)
    (plSpec α (c n) (N n)) (pg15_plSpec_anti R.hα (R.hcpos n))
    (fun j => pg15_plSpec_pos (R.hcpos n) j) R.hβ0 R.hβ1 hγadm hμC hC1 i hz
    (min_le_left _ _)).2.2.2.2 (H n) (ϱ n) hρ hρz
  have hD := pg15p5_D_le β (B n) (plSpec α (c n) (N n)) (R.hNpos n) i
  have hE := pg15p5_E_le β (B n) (plSpec α (c n) (N n)) (R.hNpos n) i hz.le
  have hq0 : 0 < β ^ ((1 : ℝ) / 3) := Real.rpow_pos_of_pos R.hβ0 _
  have hq1 : β ^ ((1 : ℝ) / 3) < 1 := Real.rpow_lt_one R.hβ0.le R.hβ1 (by norm_num)
  have hpow : β ^ (((H n : ℝ) + 1) / 3) =
      β ^ ((H n : ℝ) / 3) * β ^ ((1 : ℝ) / 3) := by
    rw [show ((H n : ℝ) + 1) / 3 = (H n : ℝ) / 3 + (1 : ℝ) / 3 by ring,
      Real.rpow_add R.hβ0]
  have hbound : |ridgeV cert (γstar n) (CSig n) β (B n)
        (plSpec α (c n) (N n)) i (ϱ n) -
      vZero cert (γstar n) (CSig n) β (B n) (plSpec α (c n) (N n)) i| ≤
      4 * U n + K * V n := by
    apply hraw.trans
    rw [hpow]
    have hfirst : 2 * (1 + 2 * (H n : ℝ)) *
        Real.sqrt (plDcoef β (B n) (plSpec α (c n) (N n)) (R.hNpos n) i) *
          ϱ n ^ ((1 : ℝ) / 4) ≤ 4 * U n := by
      have hsqrt := Real.sqrt_le_sqrt hD
      simp only [U]
      have hh : 2 * (1 + 2 * (H n : ℝ)) ≤ 4 * (1 + (H n : ℝ)) := by
        linarith
      calc
        _ ≤ 4 * (1 + (H n : ℝ)) *
            Real.sqrt (ridgeDstar β (B n) (plSpec α (c n) (N n)) (R.hNpos n)) *
              ϱ n ^ ((1 : ℝ) / 4) := mul_le_mul_of_nonneg_right
                (mul_le_mul hh hsqrt (Real.sqrt_nonneg _) (by positivity))
                (Real.rpow_nonneg hρ.le _)
        _ = 4 * ((1 + (H n : ℝ)) *
            Real.sqrt (ridgeDstar β (B n) (plSpec α (c n) (N n)) (R.hNpos n)) *
              ϱ n ^ ((1 : ℝ) / 4)) := by ring
    have htail : 4 * plEi β (B n) (plSpec α (c n) (N n)) (R.hNpos n) i
          (ridgeZbar β (B n) (plSpec α (c n) (N n))) *
          (β ^ ((H n : ℝ) / 3) * β ^ ((1 : ℝ) / 3)) /
          (1 - β ^ ((1 : ℝ) / 3)) ≤ K * V n := by
      simp only [K, V]
      have hpowH : 0 ≤ β ^ ((H n : ℝ) / 3) := (Real.rpow_pos_of_pos R.hβ0 _).le
      have hden : 0 < 1 - β ^ ((1 : ℝ) / 3) := sub_pos.2 hq1
      have hnumer := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hE (mul_nonneg hpowH hq0.le)) (by norm_num : (0 : ℝ) ≤ 4)
      calc
        _ ≤ 4 * ridgeEstar β (B n) (plSpec α (c n) (N n)) (R.hNpos n) *
            (β ^ ((H n : ℝ) / 3) * β ^ ((1 : ℝ) / 3)) /
              (1 - β ^ ((1 : ℝ) / 3)) := by
                apply div_le_div_of_nonneg_right _ hden.le
                convert hnumer using 1 <;> ring
        _ = 4 * β ^ ((1 : ℝ) / 3) / (1 - β ^ ((1 : ℝ) / 3)) *
            (ridgeEstar β (B n) (plSpec α (c n) (N n)) (R.hNpos n) *
              β ^ ((H n : ℝ) / 3)) := by ring
    exact add_le_add hfirst htail
  have hnonneg : 0 ≤ 4 * U n + K * V n := by
    have hU : 0 ≤ U n := by
      simp only [U]
      exact mul_nonneg (mul_nonneg (by positivity) (Real.sqrt_nonneg _))
        (Real.rpow_nonneg hρ.le _)
    have hV : 0 ≤ V n := by
      simp only [V]
      have hE0 : 0 ≤ ridgeEstar β (B n) (plSpec α (c n) (N n)) (R.hNpos n) := by
        unfold ridgeEstar
        exact add_nonneg
          (mul_nonneg (Real.sqrt_nonneg _) (Real.rpow_nonneg hz.le _))
          (mul_nonneg (mul_nonneg (by norm_num) (Real.sqrt_nonneg _))
            (Real.rpow_nonneg hz.le _))
      exact mul_nonneg hE0 (Real.rpow_nonneg R.hβ0.le _)
    have hK : 0 ≤ K := by
      simp only [K]
      exact div_nonneg (mul_nonneg (by norm_num) hq0.le) (sub_nonneg.2 hq1.le)
    positivity
  exact hbound.trans_lt (by simpa [abs_of_nonneg hnonneg] using hn) |>.le

private lemma pg15p6_mOf_spec {N B : ℕ} {β : ℝ} (μ : Fin N → ℝ)
    (hβ0 : 0 < β) (hβ1 : β < 1) (hB : 0 < B) (hN : 0 < N)
    (hanti : Antitone μ) (hpos : ∀ i, 0 < μ i) {s : ℝ} (hs : 0 < s) :
    mOf β B μ s ∈ Ioo 0 (gammaOf N B) ∧ sN β B μ (mOf β B μ s) = s := by
  have hbij := (prop_app_pl_branch_i μ hβ0 hβ1 hB hN hanti hpos).2.2.1
  obtain ⟨x, hx, hfx⟩ := hbij.surjOn (show s ∈ Ioi (0 : ℝ) from hs)
  have hex : ∃ a ∈ Ioo (0 : ℝ) (gammaOf N B), sN β B μ a = s := ⟨x, hx, hfx⟩
  unfold mOf
  exact ⟨Function.invFunOn_mem hex, Function.invFunOn_eq hex⟩

private lemma pg15p6_lag_error {α β : ℝ} {N B : ℕ → ℕ} {c : ℕ → ℝ}
    (R : assum_app_pl_regime α β N B c) (cert : Muon.External.GaussianOpNorm)
    (γstar CSig : ℕ → ℝ)
    (hadm : ∀ n, zeroAdmissible (N n) (B n) (plSpec α (c n) (N n)) (γstar n) (CSig n))
    (ϱ : ℕ → ℝ) (H : ℕ → ℕ) (hW : ridgeWindow R ϱ H) :
    ∀ ε > 0, ∀ᶠ n in atTop, ∀ (i : Fin (N n)) (ℓ : ℕ),
      |ridgeC cert (γstar n) (CSig n) β ℓ (B n) (plSpec α (c n) (N n)) i (ϱ n) -
        cbarZero cert (γstar n) (CSig n) β (B n) (plSpec α (c n) (N n)) i ℓ| ≤ ε := by
  intro ε hε
  have hsmall : ∀ᶠ n in atTop,
      |(1 + (H n : ℝ)) *
        Real.sqrt (ridgeDstar β (B n) (plSpec α (c n) (N n)) (R.hNpos n)) *
        ϱ n ^ ((1 : ℝ) / 4)| < ε / 2 := by
    simpa [Real.dist_eq] using hW.2.2.1.eventually (Metric.ball_mem_nhds 0 (half_pos hε))
  filter_upwards [hsmall] with n hn
  intro i ℓ
  rcases hadm n with ⟨hγ, hμC, hC1⟩
  let μ : Fin (N n) → ℝ := plSpec α (c n) (N n)
  let ν : FiniteMeasure ℝ :=
    ⟨ENNReal.ofReal (((B n : ℕ) : ℝ)⁻¹) • ∑ j, Measure.dirac (μ j), by
      constructor
      rw [Measure.smul_apply, smul_eq_mul]
      exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top _ _)⟩
  let ν' : FiniteMeasure ℝ :=
    ⟨ENNReal.ofReal (gammaOf (N n) (B n)) • Measure.dirac (1 : ℝ), by
      constructor
      simp [Measure.smul_apply]⟩
  have hν : (ν : Measure ℝ) =
      ENNReal.ofReal ((B n : ℝ)⁻¹) • ∑ j, Measure.dirac (μ j) := rfl
  have hν' : (ν' : Measure ℝ) =
      ENNReal.ofReal (gammaOf (N n) (B n)) • Measure.dirac (1 : ℝ) := rfl
  have hρ := (hW.1 n).1
  have hρz := (hW.1 n).2
  have hz := pg15p4_ridgeZbar_pos R n
  have hanti : Antitone μ := pg15_plSpec_anti R.hα (R.hcpos n)
  have hpos : ∀ j, 0 < μ j := fun j => pg15_plSpec_pos (R.hcpos n) j
  have hd := prop_app_pl_drift_zero_i_volraw μ R.hβ0 R.hβ1 (R.hBpos n) (R.hNpos n)
    hanti hpos hν hν' hμC hC1 i hρ (hρz.trans (min_le_left _ _))
  have hm := pg15p6_mOf_spec μ R.hβ0 R.hβ1 (R.hBpos n) (R.hNpos n) hanti hpos hρ
  have hLam : 0 < partLam (B n) μ (mOf β (B n) μ (ϱ n)) :=
    (def_app_pl_participation_bij μ (R.hBpos n) (R.hNpos n) hpos).2.1.mapsTo hm.1
  have hp : 0 < 1 - Muon.Volatility.volraw β ν ν' (μ i) (ϱ n) := by
    rw [hd.1]
    exact one_div_pos.mpr (by nlinarith [mul_pos hLam (hpos i)])
  have hdef : 1 - Muon.Volatility.volraw β ν ν' (μ i) (ϱ n) ≤
      plDcoef β (B n) μ (R.hNpos n) i * Real.sqrt (ϱ n) := by
    rw [hd.1]
    simpa [plDcoef, plFstar, one_div] using hd.2
  have hD : 0 ≤ plDcoef β (B n) μ (R.hNpos n) i := by
    exact (pos_of_mul_pos_left (hp.trans_le hdef) (Real.sqrt_nonneg _)).le
  have htwo := (lem_app_pl_two_ridge_i cert (γstar n) (CSig n) (R.hBpos n) (R.hNpos n)
    μ hanti hpos R.hβ0 R.hβ1 hγ hμC hC1 hν hν' i).2
  have hev : ∀ᶠ η in 𝓝[>] (0 : ℝ),
      |Muon.Volatility.lagRowBar cert (γstar n) (CSig n) β ℓ (B n) μ
          (fun _ : Fin (N n) => (1 : ℝ)) i η η -
        Muon.Volatility.lagRowBar cert (γstar n) (CSig n) β ℓ (B n) μ
          (fun _ : Fin (N n) => (1 : ℝ)) i (ϱ n) (ϱ n)| ≤
        2 * Real.sqrt (plDcoef β (B n) μ (R.hNpos n) i) * ϱ n ^ ((1 : ℝ) / 4) := by
    filter_upwards [Ioo_mem_nhdsGT hρ] with η hη
    calc
      _ ≤ 2 * Real.sqrt (1 - Muon.Volatility.volraw β ν ν' (μ i) (ϱ n)) :=
        htwo η (ϱ n) ℓ hη.1 hη.2.le
      _ ≤ 2 * Real.sqrt (plDcoef β (B n) μ (R.hNpos n) i * Real.sqrt (ϱ n)) := by
        gcongr
      _ = 2 * Real.sqrt (plDcoef β (B n) μ (R.hNpos n) i) *
          ϱ n ^ ((1 : ℝ) / 4) := by
        rw [Real.sqrt_mul hD, show Real.sqrt (Real.sqrt (ϱ n)) = ϱ n ^ ((1 : ℝ) / 4) by
          rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul hρ.le]
          norm_num]
        ring
  have hlim := (prop_app_pl_vol_zero_i cert (γstar n) (CSig n) (R.hBpos n) (R.hNpos n)
    μ hanti hpos R.hβ0 R.hβ1 hγ hμC hC1 i hz (min_le_left _ _)).2.1 ℓ
  have hlag :
      |Muon.Volatility.lagRowBar cert (γstar n) (CSig n) β ℓ (B n) μ
          (fun _ : Fin (N n) => (1 : ℝ)) i (ϱ n) (ϱ n) -
        cbarZero cert (γstar n) (CSig n) β (B n) μ i ℓ| ≤
        2 * Real.sqrt (plDcoef β (B n) μ (R.hNpos n) i) * ϱ n ^ ((1 : ℝ) / 4) := by
    have := le_of_tendsto (hlim.sub tendsto_const_nhds |>.abs) hev
    rwa [abs_sub_comm] at this
  have hDle := pg15p5_D_le β (B n) μ (R.hNpos n) i
  have hbase : 0 ≤ Real.sqrt (ridgeDstar β (B n) μ (R.hNpos n)) *
      ϱ n ^ ((1 : ℝ) / 4) := mul_nonneg (Real.sqrt_nonneg _) (Real.rpow_nonneg hρ.le _)
  have hbound :
      2 * Real.sqrt (plDcoef β (B n) μ (R.hNpos n) i) * ϱ n ^ ((1 : ℝ) / 4) ≤
        2 * ((1 + (H n : ℝ)) * Real.sqrt (ridgeDstar β (B n) μ (R.hNpos n)) *
          ϱ n ^ ((1 : ℝ) / 4)) := by
    calc
      _ ≤ 2 * Real.sqrt (ridgeDstar β (B n) μ (R.hNpos n)) * ϱ n ^ ((1 : ℝ) / 4) := by
        gcongr
      _ ≤ 2 * ((1 + (H n : ℝ)) * Real.sqrt (ridgeDstar β (B n) μ (R.hNpos n)) *
          ϱ n ^ ((1 : ℝ) / 4)) := by
        nlinarith [show (0 : ℝ) ≤ (H n : ℝ) by positivity]
  have hU : 0 ≤ (1 + (H n : ℝ)) * Real.sqrt (ridgeDstar β (B n) μ (R.hNpos n)) *
      ϱ n ^ ((1 : ℝ) / 4) := by positivity
  have hUsmall : (1 + (H n : ℝ)) * Real.sqrt (ridgeDstar β (B n) μ (R.hNpos n)) *
      ϱ n ^ ((1 : ℝ) / 4) < ε / 2 := by
    simpa only [μ, abs_of_nonneg hU] using hn
  simpa only [ridgeC, μ] using hlag.trans_lt (hbound.trans_lt (by linarith)) |>.le

private lemma pg15p6_vol_sub_tendsto_zero {α β : ℝ} {N B : ℕ → ℕ} {c : ℕ → ℝ}
    (R : assum_app_pl_regime α β N B c) (cert : Muon.External.GaussianOpNorm)
    (γstar CSig : ℕ → ℝ)
    (hadm : ∀ n, zeroAdmissible (N n) (B n) (plSpec α (c n) (N n)) (γstar n) (CSig n))
    (ϱ : ℕ → ℝ) (H : ℕ → ℕ) (hW : ridgeWindow R ϱ H)
    (i : (n : ℕ) → Fin (N n)) :
    Tendsto (fun n =>
      ridgeV cert (γstar n) (CSig n) β (B n) (plSpec α (c n) (N n)) (i n) (ϱ n) -
      vZero cert (γstar n) (CSig n) β (B n) (plSpec α (c n) (N n)) (i n)) atTop (𝓝 0) := by
  refine Metric.tendsto_nhds.2 fun ε hε => ?_
  filter_upwards [pg15p5_vol_error R cert γstar CSig hadm ϱ H hW (ε / 2) (by positivity)]
    with n hn
  rw [Real.dist_eq, sub_zero]
  exact (hn (i n)).trans_lt (by linarith)

private lemma pg15p6_vol_equiv {α β : ℝ} {N B : ℕ → ℕ} {c : ℕ → ℝ}
    (R : assum_app_pl_regime α β N B c) (cert : Muon.External.GaussianOpNorm)
    (γstar CSig : ℕ → ℝ)
    (hadm : ∀ n, zeroAdmissible (N n) (B n) (plSpec α (c n) (N n)) (γstar n) (CSig n))
    (ϱ : ℕ → ℝ) (H : ℕ → ℕ) (hW : ridgeWindow R ϱ H)
    (i : (n : ℕ) → Fin (N n)) :
    IsEquivalent atTop
      (fun n => ridgeV cert (γstar n) (CSig n) β (B n) (plSpec α (c n) (N n)) (i n) (ϱ n))
      (fun n => vZero cert (γstar n) (CSig n) β (B n) (plSpec α (c n) (N n)) (i n)) := by
  have hne : ∀ᶠ n in atTop,
      vZero cert (γstar n) (CSig n) β (B n) (plSpec α (c n) (N n)) (i n) ≠ 0 :=
    Filter.Eventually.of_forall fun n => by
      rcases hadm n with ⟨hγ, hμC, hC1⟩
      exact ne_of_gt (lt_of_lt_of_le zero_lt_one
        (prop_app_pl_vol_zero_iii_c cert (γstar n) (CSig n) (R.hBpos n)
        (R.hNpos n) (plSpec α (c n) (N n)) (pg15_plSpec_anti R.hα (R.hcpos n))
        (fun j => pg15_plSpec_pos (R.hcpos n) j) R.hβ0 R.hβ1 hγ hμC hC1 (i n)).2.2)
  apply (isEquivalent_iff_tendsto_one hne).2
  refine Metric.tendsto_nhds.2 fun ε hε => ?_
  filter_upwards [pg15p5_vol_error R cert γstar CSig hadm ϱ H hW (ε / 2) (by positivity)]
    with n hn
  rcases hadm n with ⟨hγ, hμC, hC1⟩
  have hvone : 1 ≤ vZero cert (γstar n) (CSig n) β (B n)
      (plSpec α (c n) (N n)) (i n) :=
    (prop_app_pl_vol_zero_iii_c cert (γstar n) (CSig n) (R.hBpos n) (R.hNpos n)
      (plSpec α (c n) (N n)) (pg15_plSpec_anti R.hα (R.hcpos n))
      (fun j => pg15_plSpec_pos (R.hcpos n) j) R.hβ0 R.hβ1 hγ hμC hC1 (i n)).2.2
  change |ridgeV cert (γstar n) (CSig n) β (B n) (plSpec α (c n) (N n)) (i n) (ϱ n) /
      vZero cert (γstar n) (CSig n) β (B n) (plSpec α (c n) (N n)) (i n) - 1| < ε
  have hvne : vZero cert (γstar n) (CSig n) β (B n) (plSpec α (c n) (N n)) (i n) ≠ 0 :=
    ne_of_gt (zero_lt_one.trans_le hvone)
  rw [div_sub_one hvne, abs_div, abs_of_nonneg (zero_le_one.trans hvone)]
  exact (div_le_self (abs_nonneg _) hvone).trans_lt ((hn (i n)).trans_lt (by linarith))

/-- `prop:app-pl-ridge` (snapshot `cr-2026-10-23`), `thm:app-pl-triple` with `𝔡_i(ϱ_N)`, `𝔳_i(ϱ_N)`. Statement (LaTeX, verbatim from sections/06-power-law/section.tex):

\begin{proposition}[Negligible ridge]\label{prop:app-pl-ridge}
Assume \cref{assum:app-pl-regime}. Let $0<\ridge_N\le\bar z_N$ and let $H_N\ge0$ be
integers with
\begin{equation}\label{eqn:app-pl-ridge-window}
\frac{\ridge_N\,Q_\gamma}{c_NN^{-\alpha}\gamma^2}\to0,\qquad
(1+H_N)\sqrt{D_\star}\,\ridge_N^{1/4}\to0,\qquad
E_\star\,\bmom^{H_N/3}\to0 .
\end{equation}
Then \cref{thm:app-pl-triple,thm:app-pl-drift,thm:app-pl-volatility},
\cref{cor:app-pl-endpoints,cor:app-pl-weighted} hold with $\mathfrak d_i(\ridge_N)$,
$\overline C_{i,\ell}(\ridge_N)$ and $\mathfrak v_i(\ridge_N)$ in place of the zero-ridge
coefficients. Such sequences $(\ridge_N,H_N)$ exist.
\end{proposition}
-/
theorem prop_app_pl_ridge_triple {α β : ℝ} {N B : ℕ → ℕ} {c : ℕ → ℝ}
    (R : assum_app_pl_regime α β N B c)
    (cert : Muon.External.GaussianOpNorm) (γstar CSig : ℕ → ℝ)
    (hadm : ∀ n, zeroAdmissible (N n) (B n) (plSpec α (c n) (N n)) (γstar n) (CSig n))
    (ν ν' : ℕ → FiniteMeasure ℝ)
    (hν : ∀ n, (ν n : Measure ℝ) =
      ENNReal.ofReal ((B n : ℝ)⁻¹) • ∑ i : Fin (N n), Measure.dirac (plSpec α (c n) (N n) i))
    (hν' : ∀ n, (ν' n : Measure ℝ) = ENNReal.ofReal (gammaOf (N n) (B n)) • Measure.dirac (1 : ℝ))
    (ϱ : ℕ → ℝ) (H : ℕ → ℕ) (hW : ridgeWindow R ϱ H)
    (nN : ℕ → ℕ) (hnN : ∀ n, 1 ≤ nN n ∧ nN n ≤ N n)
    (hn : Tendsto (fun n => (nN n : ℝ)) atTop atTop) :
    ridgeDriftWellPosed R ν ν' ϱ ∧ ridgeVolWellPosed R cert γstar CSig ϱ ∧
    ∀ ε > 0, ∀ᶠ n in atTop, ∀ i : Fin (N n), (nN n : ℝ) ≤ rowNum i →
      |dRidge β (ν n) (ν' n) (plSpec α (c n) (N n)) i (ϱ n) /
          dHatDrift α β (c n) (N n) (B n) i - 1| ≤ ε ∧
      |ridgeV cert (γstar n) (CSig n) β (B n) (plSpec α (c n) (N n)) i (ϱ n) /
          (if α ≤ 1 then vhatApprox β α (B n) i else vhatSuper β α (B n) i) - 1| ≤ ε := by
  refine ⟨pg15p5_drift_wellPosed R ν ν' hν hν' ϱ (fun n => (hW.1 n).1),
    pg15p5_vol_wellPosed R cert γstar CSig hadm ϱ hW.1, ?_⟩
  intro ε hε
  have hz := thm_app_pl_triple R cert γstar CSig hadm nN hnN hn (ε / 2) (by positivity)
  have hz1 := thm_app_pl_triple R cert γstar CSig hadm nN hnN hn 1 one_pos
  have hd := pg15p5_drift_ratio_error R ν ν' hν hν' ϱ H hW (ε / 2) (by positivity)
  have hv := pg15p5_vol_error R cert γstar CSig hadm ϱ H hW (ε / 4) (by positivity)
  filter_upwards [hz, hz1, hd, hv] with n hzn hzn1 hdn hvn
  intro i hi
  have hzero := hzn i hi
  have hzero1 := hzn1 i hi
  have hdpos := pg15_dHat_pos R n i
  have hvpos := pg15_vHat_pos R n i
  constructor
  · have herr := hdn i
    calc
      |dRidge β (ν n) (ν' n) (plSpec α (c n) (N n)) i (ϱ n) /
          dHatDrift α β (c n) (N n) (B n) i - 1| =
          |(dRidge β (ν n) (ν' n) (plSpec α (c n) (N n)) i (ϱ n) /
              dHatDrift α β (c n) (N n) (B n) i -
            dZero β (B n) (plSpec α (c n) (N n)) i /
              dHatDrift α β (c n) (N n) (B n) i) +
            (dZero β (B n) (plSpec α (c n) (N n)) i /
              dHatDrift α β (c n) (N n) (B n) i - 1)| := by congr 1 <;> ring
      _ ≤ |dRidge β (ν n) (ν' n) (plSpec α (c n) (N n)) i (ϱ n) /
              dHatDrift α β (c n) (N n) (B n) i -
            dZero β (B n) (plSpec α (c n) (N n)) i /
              dHatDrift α β (c n) (N n) (B n) i| +
            |dZero β (B n) (plSpec α (c n) (N n)) i /
              dHatDrift α β (c n) (N n) (B n) i - 1| := abs_add_le _ _
      _ ≤ ε / 2 + ε / 2 := add_le_add herr hzero.1
      _ = ε := by ring
  · let vh := if α ≤ 1 then vhatApprox β α (B n) i else vhatSuper β α (B n) i
    let v0 := vZero cert (γstar n) (CSig n) β (B n) (plSpec α (c n) (N n)) i
    let vr := ridgeV cert (γstar n) (CSig n) β (B n) (plSpec α (c n) (N n)) i (ϱ n)
    have hvh : 0 < vh := hvpos
    have hv0 : 1 ≤ v0 := by
      rcases hadm n with ⟨hγadm, hμC, hC1⟩
      exact (prop_app_pl_vol_zero_iii_c cert (γstar n) (CSig n) (R.hBpos n) (R.hNpos n)
        (plSpec α (c n) (N n)) (pg15_plSpec_anti R.hα (R.hcpos n))
        (fun j => pg15_plSpec_pos (R.hcpos n) j) R.hβ0 R.hβ1 hγadm hμC hC1 i).2.2
    have hvhlower : 1 / 2 ≤ vh := by
      have hupp : v0 / vh ≤ 2 := by
        have := (abs_le.mp hzero1.2).2
        dsimp only [v0, vh]
        linarith
      have := (div_le_iff₀ hvh).mp hupp
      dsimp only [v0, vh] at hv0 ⊢
      nlinarith
    have herr : |vr - v0| ≤ ε / 4 := hvn i
    have herr' : |vr / vh - v0 / vh| ≤ ε / 2 := by
      rw [← sub_div, abs_div, abs_of_pos hvh]
      apply (div_le_iff₀ hvh).2
      nlinarith [abs_nonneg (vr - v0)]
    calc
      |vr / vh - 1| = |(vr / vh - v0 / vh) + (v0 / vh - 1)| := by congr 1 <;> ring
      _ ≤ |vr / vh - v0 / vh| + |v0 / vh - 1| := abs_add_le _ _
      _ ≤ ε / 2 + ε / 2 := add_le_add herr' hzero.2
      _ = ε := by ring

private lemma pg15p5_drift_equiv {α β : ℝ} {N B : ℕ → ℕ} {c : ℕ → ℝ}
    (R : assum_app_pl_regime α β N B c) (ν ν' : ℕ → FiniteMeasure ℝ)
    (hν : ∀ n, (ν n : Measure ℝ) =
      ENNReal.ofReal ((B n : ℝ)⁻¹) • ∑ i : Fin (N n), Measure.dirac (plSpec α (c n) (N n) i))
    (hν' : ∀ n, (ν' n : Measure ℝ) =
      ENNReal.ofReal (gammaOf (N n) (B n)) • Measure.dirac (1 : ℝ))
    (ϱ : ℕ → ℝ) (H : ℕ → ℕ) (hW : ridgeWindow R ϱ H)
    (i : (n : ℕ) → Fin (N n)) (hi : Tendsto (fun n => rowNum (i n)) atTop atTop)
    (hz : ∀ ε > 0, ∀ᶠ n in atTop,
      |dZero β (B n) (plSpec α (c n) (N n)) (i n) /
        dHatDrift α β (c n) (N n) (B n) (i n) - 1| ≤ ε) :
    IsEquivalent atTop
      (fun n => Real.sqrt 2 * dRidge β (ν n) (ν' n) (plSpec α (c n) (N n)) (i n) (ϱ n))
      (fun n => Real.sqrt 2 * dZero β (B n) (plSpec α (c n) (N n)) (i n)) := by
  have he := pg15p5_drift_ratio_error R ν ν' hν hν' ϱ H hW
  have hr : Tendsto (fun n => dRidge β (ν n) (ν' n) (plSpec α (c n) (N n)) (i n) (ϱ n) /
      dHatDrift α β (c n) (N n) (B n) (i n)) atTop (𝓝 1) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    have her := he (ε / 3) (by positivity)
    have hzr := hz (ε / 3) (by positivity)
    rw [Filter.eventually_atTop] at her hzr
    obtain ⟨nr, hnr⟩ := her
    obtain ⟨nz, hnz⟩ := hzr
    refine ⟨max nr nz, fun n hn => ?_⟩
    have her := hnr n (le_trans (le_max_left _ _) hn)
    have hzr := hnz n (le_trans (le_max_right _ _) hn)
    rw [Real.dist_eq]
    calc
      |dRidge β (ν n) (ν' n) (plSpec α (c n) (N n)) (i n) (ϱ n) /
          dHatDrift α β (c n) (N n) (B n) (i n) - 1| ≤
          |dRidge β (ν n) (ν' n) (plSpec α (c n) (N n)) (i n) (ϱ n) /
              dHatDrift α β (c n) (N n) (B n) (i n) -
            dZero β (B n) (plSpec α (c n) (N n)) (i n) /
              dHatDrift α β (c n) (N n) (B n) (i n)| +
            |dZero β (B n) (plSpec α (c n) (N n)) (i n) /
              dHatDrift α β (c n) (N n) (B n) (i n) - 1| := by
                convert abs_add_le
                  (dRidge β (ν n) (ν' n) (plSpec α (c n) (N n)) (i n) (ϱ n) /
                    dHatDrift α β (c n) (N n) (B n) (i n) -
                    dZero β (B n) (plSpec α (c n) (N n)) (i n) /
                      dHatDrift α β (c n) (N n) (B n) (i n))
                  (dZero β (B n) (plSpec α (c n) (N n)) (i n) /
                    dHatDrift α β (c n) (N n) (B n) (i n) - 1) using 1 <;> ring
      _ ≤ ε / 3 + ε / 3 := add_le_add (her (i n)) hzr
      _ < ε := by linarith
  have hzlim : Tendsto (fun n => dZero β (B n) (plSpec α (c n) (N n)) (i n) /
      dHatDrift α β (c n) (N n) (B n) (i n)) atTop (𝓝 1) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    have hev := hz (ε / 2) (by positivity)
    rw [Filter.eventually_atTop] at hev
    obtain ⟨n0, hn0⟩ := hev
    refine ⟨n0, fun n hn => ?_⟩
    rw [Real.dist_eq]
    exact (hn0 n hn).trans_lt (by linarith)
  have hne : ∀ᶠ n in atTop, dHatDrift α β (c n) (N n) (B n) (i n) ≠ 0 :=
    Filter.Eventually.of_forall fun n => (pg15_dHat_pos R n (i n)).ne'
  have hrE : IsEquivalent atTop
      (fun n => dRidge β (ν n) (ν' n) (plSpec α (c n) (N n)) (i n) (ϱ n))
      (fun n => dHatDrift α β (c n) (N n) (B n) (i n)) :=
    (isEquivalent_iff_tendsto_one hne).2 hr
  have hzE : IsEquivalent atTop
      (fun n => dZero β (B n) (plSpec α (c n) (N n)) (i n))
      (fun n => dHatDrift α β (c n) (N n) (B n) (i n)) :=
    (isEquivalent_iff_tendsto_one hne).2 hzlim
  exact (IsEquivalent.refl (u := fun _ : ℕ => Real.sqrt 2)).mul (hrE.trans hzE.symm)

/-- `prop:app-pl-ridge` (snapshot `cr-2026-10-23`), `thm:app-pl-drift`(i) with `𝔡_i(ϱ_N)`. Statement (LaTeX, verbatim from sections/06-power-law/section.tex):

\begin{proposition}[Negligible ridge]\label{prop:app-pl-ridge}
Assume \cref{assum:app-pl-regime}. Let $0<\ridge_N\le\bar z_N$ and let $H_N\ge0$ be
integers with
\begin{equation}\label{eqn:app-pl-ridge-window}
\frac{\ridge_N\,Q_\gamma}{c_NN^{-\alpha}\gamma^2}\to0,\qquad
(1+H_N)\sqrt{D_\star}\,\ridge_N^{1/4}\to0,\qquad
E_\star\,\bmom^{H_N/3}\to0 .
\end{equation}
Then \cref{thm:app-pl-triple,thm:app-pl-drift,thm:app-pl-volatility},
\cref{cor:app-pl-endpoints,cor:app-pl-weighted} hold with $\mathfrak d_i(\ridge_N)$,
$\overline C_{i,\ell}(\ridge_N)$ and $\mathfrak v_i(\ridge_N)$ in place of the zero-ridge
coefficients. Such sequences $(\ridge_N,H_N)$ exist.
\end{proposition}
-/
theorem prop_app_pl_ridge_drift_i {α β : ℝ} {N B : ℕ → ℕ} {c : ℕ → ℝ}
    (R : assum_app_pl_regime α β N B c)
    (ν ν' : ℕ → FiniteMeasure ℝ)
    (hν : ∀ n, (ν n : Measure ℝ) =
      ENNReal.ofReal ((B n : ℝ)⁻¹) • ∑ i : Fin (N n), Measure.dirac (plSpec α (c n) (N n) i))
    (hν' : ∀ n, (ν' n : Measure ℝ) = ENNReal.ofReal (gammaOf (N n) (B n)) • Measure.dirac (1 : ℝ))
    (ϱ : ℕ → ℝ) (H : ℕ → ℕ) (hW : ridgeWindow R ϱ H) (hα : α ≤ 1)
    (i : (n : ℕ) → Fin (N n)) (hi : Tendsto (fun n => rowNum (i n)) atTop atTop) :
    ridgeDriftWellPosed R ν ν' ϱ ∧
    (∀ x ∈ Ioi (0 : ℝ),
      Tendsto (fun n => rowNum (i n) / icdIdx β α (N n) (B n)) atTop (𝓝 x) →
        Tendsto (fun n => Real.sqrt 2 * dRidge β (ν n) (ν' n) (plSpec α (c n) (N n)) (i n) (ϱ n) /
          icdA α (c n) (N n) (B n)) atTop (𝓝 (1 + x ^ (-α / 2)))) ∧
    (Tendsto (fun n => rowNum (i n) / icdIdx β α (N n) (B n)) atTop (𝓝 0) →
      IsEquivalent atTop
        (fun n => Real.sqrt 2 * dRidge β (ν n) (ν' n) (plSpec α (c n) (N n)) (i n) (ϱ n))
        (fun n => Real.sqrt (plSpec α (c n) (N n) (i n) / (gammaOf (N n) (B n) * sPow β 2)))) ∧
    (Tendsto (fun n => rowNum (i n) / icdIdx β α (N n) (B n)) atTop atTop →
      IsEquivalent atTop
        (fun n => Real.sqrt 2 * dRidge β (ν n) (ν' n) (plSpec α (c n) (N n)) (i n) (ϱ n))
        (fun n => aN α (c n) (N n) * profPsi α (rowNum (i n) / (N n : ℝ))) ∧
      (Tendsto (fun n => rowNum (i n) / (N n : ℝ)) atTop (𝓝 0) →
        IsEquivalent atTop
          (fun n => Real.sqrt 2 * dRidge β (ν n) (ν' n) (plSpec α (c n) (N n)) (i n) (ϱ n))
          (fun n => icdD α * aN α (c n) (N n) *
            (if α < 1 then Real.log (((N n : ℝ) / rowNum (i n)) ^ α)
              else Real.log ((N n : ℝ) / rowNum (i n)) ^ ((3 : ℝ) / 2))))) := by
  let nN : ℕ → ℕ := fun n => (i n : ℕ) + 1
  have hnN : ∀ n, 1 ≤ nN n ∧ nN n ≤ N n := fun n => by
    simp only [nN]
    exact ⟨by omega, (i n).isLt⟩
  have hn : Tendsto (fun n => (nN n : ℝ)) atTop atTop := by
    simpa only [nN, rowNum, Nat.cast_add, Nat.cast_one] using hi
  have hz : ∀ ε > 0, ∀ᶠ n in atTop,
      |dZero β (B n) (plSpec α (c n) (N n)) (i n) /
        dHatDrift α β (c n) (N n) (B n) (i n) - 1| ≤ ε := by
    intro ε hε
    filter_upwards [triple_drift_le_one R hα nN hnN hn ε hε] with n hzero
    exact hzero (i n) (by simp [nN, rowNum])
  have heq := pg15p5_drift_equiv R ν ν' hν hν' ϱ H hW i hi hz
  have hzero := thm_app_pl_drift_i R hα i hi
  refine ⟨pg15p5_drift_wellPosed R ν ν' hν hν' ϱ (fun n => (hW.1 n).1), ?_, ?_, ?_⟩
  · intro x hx hcross
    have heq' := heq.div (IsEquivalent.refl
      (u := fun n => icdA α (c n) (N n) (B n)))
    exact heq'.symm.tendsto_nhds (hzero.1 x hx hcross)
  · intro hcross
    exact heq.trans (hzero.2.1 hcross)
  · intro hcross
    refine ⟨heq.trans (hzero.2.2 hcross).1, ?_⟩
    intro hfrac
    exact heq.trans ((hzero.2.2 hcross).2 hfrac)

/-- `prop:app-pl-ridge` (snapshot `cr-2026-10-23`), `thm:app-pl-drift`(ii) with `𝔡_i(ϱ_N)`. Statement (LaTeX, verbatim from sections/06-power-law/section.tex):

\begin{proposition}[Negligible ridge]\label{prop:app-pl-ridge}
Assume \cref{assum:app-pl-regime}. Let $0<\ridge_N\le\bar z_N$ and let $H_N\ge0$ be
integers with
\begin{equation}\label{eqn:app-pl-ridge-window}
\frac{\ridge_N\,Q_\gamma}{c_NN^{-\alpha}\gamma^2}\to0,\qquad
(1+H_N)\sqrt{D_\star}\,\ridge_N^{1/4}\to0,\qquad
E_\star\,\bmom^{H_N/3}\to0 .
\end{equation}
Then \cref{thm:app-pl-triple,thm:app-pl-drift,thm:app-pl-volatility},
\cref{cor:app-pl-endpoints,cor:app-pl-weighted} hold with $\mathfrak d_i(\ridge_N)$,
$\overline C_{i,\ell}(\ridge_N)$ and $\mathfrak v_i(\ridge_N)$ in place of the zero-ridge
coefficients. Such sequences $(\ridge_N,H_N)$ exist.
\end{proposition}
-/
theorem prop_app_pl_ridge_drift_ii {α β : ℝ} {N B : ℕ → ℕ} {c : ℕ → ℝ}
    (R : assum_app_pl_regime α β N B c)
    (ν ν' : ℕ → FiniteMeasure ℝ)
    (hν : ∀ n, (ν n : Measure ℝ) =
      ENNReal.ofReal ((B n : ℝ)⁻¹) • ∑ i : Fin (N n), Measure.dirac (plSpec α (c n) (N n) i))
    (hν' : ∀ n, (ν' n : Measure ℝ) = ENNReal.ofReal (gammaOf (N n) (B n)) • Measure.dirac (1 : ℝ))
    (ϱ : ℕ → ℝ) (H : ℕ → ℕ) (hW : ridgeWindow R ϱ H) (hα : 1 < α)
    (i : (n : ℕ) → Fin (N n)) (hi : Tendsto (fun n => rowNum (i n)) atTop atTop) :
    ridgeDriftWellPosed R ν ν' ϱ ∧
    (∀ x ∈ Ioi (0 : ℝ),
      Tendsto (fun n => rowNum (i n) / icCross α (B n)) atTop (𝓝 x) →
        Tendsto (fun n => Real.sqrt 2 * dRidge β (ν n) (ν' n) (plSpec α (c n) (N n)) (i n) (ϱ n) /
          bN α (c n) (N n) (B n)) atTop (𝓝 (profPhi α β (x ^ (-α))))) ∧
    (Tendsto (fun n => rowNum (i n) / icCross α (B n)) atTop (𝓝 0) →
      IsEquivalent atTop
        (fun n => Real.sqrt 2 * dRidge β (ν n) (ν' n) (plSpec α (c n) (N n)) (i n) (ϱ n))
        (fun n => Real.sqrt (plSpec α (c n) (N n) (i n) / (gammaOf (N n) (B n) * sPow β 2)))) ∧
    (Tendsto (fun n => rowNum (i n) / icCross α (B n)) atTop atTop →
      IsEquivalent atTop
        (fun n => Real.sqrt 2 * dRidge β (ν n) (ν' n) (plSpec α (c n) (N n)) (i n) (ϱ n))
        (fun n => aN α (c n) (N n) * profPsi α (rowNum (i n) / (N n : ℝ))) ∧
      (Tendsto (fun n => rowNum (i n) / (N n : ℝ)) atTop (𝓝 0) →
        IsEquivalent atTop
          (fun n => Real.sqrt 2 * dRidge β (ν n) (ν' n) (plSpec α (c n) (N n)) (i n) (ϱ n))
          (fun n => dAl α * Real.sqrt (c n * Kc α) * (N n : ℝ) ^ (-(1 : ℝ) / 2) *
            rowNum (i n) ^ (-(α - 1) / 2)))) := by
  let nN : ℕ → ℕ := fun n => (i n : ℕ) + 1
  have hnN : ∀ n, 1 ≤ nN n ∧ nN n ≤ N n := fun n => by
    simp only [nN]
    exact ⟨by omega, (i n).isLt⟩
  have hn : Tendsto (fun n => (nN n : ℝ)) atTop atTop := by
    simpa only [nN, rowNum, Nat.cast_add, Nat.cast_one] using hi
  have hz : ∀ ε > 0, ∀ᶠ n in atTop,
      |dZero β (B n) (plSpec α (c n) (N n)) (i n) /
        dHatDrift α β (c n) (N n) (B n) (i n) - 1| ≤ ε := by
    intro ε hε
    filter_upwards [triple_drift_gt_one R hα nN hnN hn ε hε] with n hzero
    exact hzero (i n) (by simp [nN, rowNum])
  have heq := pg15p5_drift_equiv R ν ν' hν hν' ϱ H hW i hi hz
  have hzero := thm_app_pl_drift_ii R hα i hi
  refine ⟨pg15p5_drift_wellPosed R ν ν' hν hν' ϱ (fun n => (hW.1 n).1), ?_, ?_, ?_⟩
  · intro x hx hcross
    have heq' := heq.div (IsEquivalent.refl
      (u := fun n => bN α (c n) (N n) (B n)))
    exact heq'.symm.tendsto_nhds (hzero.1 x hx hcross)
  · intro hcross
    exact heq.trans (hzero.2.1 hcross)
  · intro hcross
    refine ⟨heq.trans (hzero.2.2 hcross).1, ?_⟩
    intro hfrac
    exact heq.trans ((hzero.2.2 hcross).2 hfrac)

/-- `prop:app-pl-ridge` (snapshot `cr-2026-10-23`), `thm:app-pl-volatility`(i) bulk with `C̄_{i,ℓ}(ϱ_N)`, `𝔳_i(ϱ_N)`
(uniform form, card §6 #1). Statement (LaTeX, verbatim from sections/06-power-law/section.tex):

\begin{proposition}[Negligible ridge]\label{prop:app-pl-ridge}
Assume \cref{assum:app-pl-regime}. Let $0<\ridge_N\le\bar z_N$ and let $H_N\ge0$ be
integers with
\begin{equation}\label{eqn:app-pl-ridge-window}
\frac{\ridge_N\,Q_\gamma}{c_NN^{-\alpha}\gamma^2}\to0,\qquad
(1+H_N)\sqrt{D_\star}\,\ridge_N^{1/4}\to0,\qquad
E_\star\,\bmom^{H_N/3}\to0 .
\end{equation}
Then \cref{thm:app-pl-triple,thm:app-pl-drift,thm:app-pl-volatility},
\cref{cor:app-pl-endpoints,cor:app-pl-weighted} hold with $\mathfrak d_i(\ridge_N)$,
$\overline C_{i,\ell}(\ridge_N)$ and $\mathfrak v_i(\ridge_N)$ in place of the zero-ridge
coefficients. Such sequences $(\ridge_N,H_N)$ exist.
\end{proposition}
-/
theorem prop_app_pl_ridge_vol_i {α β : ℝ} {N B : ℕ → ℕ} {c : ℕ → ℝ}
    (R : assum_app_pl_regime α β N B c)
    (cert : Muon.External.GaussianOpNorm) (γstar CSig : ℕ → ℝ)
    (hadm : ∀ n, zeroAdmissible (N n) (B n) (plSpec α (c n) (N n)) (γstar n) (CSig n))
    (ϱ : ℕ → ℝ) (H : ℕ → ℕ) (hW : ridgeWindow R ϱ H) :
    ridgeVolWellPosed R cert γstar CSig ϱ ∧
    (∀ K : Set ℝ, K ⊆ Ioc 0 1 → IsCompact K → ∀ L : Set ℝ, L ⊆ Ioo 0 1 → IsCompact L →
      ∀ ε > 0, ∀ᶠ n in atTop, ∀ (i : Fin (N n)) (ℓ : ℕ),
        rowNum i / (N n : ℝ) ∈ K → (ℓ : ℝ) / gammaOf (N n) (B n) ∈ L →
          |ridgeC cert (γstar n) (CSig n) β ℓ (B n) (plSpec α (c n) (N n)) i (ϱ n) -
            profC α (rowNum i / (N n : ℝ)) ((ℓ : ℝ) / gammaOf (N n) (B n))| ≤ ε) ∧
    (∀ K : Set ℝ, K ⊆ Ioc 0 1 → IsCompact K → ∀ ε > 0, ∀ᶠ n in atTop, ∀ (i : Fin (N n)),
      rowNum i / (N n : ℝ) ∈ K →
        |ridgeV cert (γstar n) (CSig n) β (B n) (plSpec α (c n) (N n)) i (ϱ n) /
          gammaOf (N n) (B n) - profGamma α (rowNum i / (N n : ℝ))| ≤ ε) := by
  refine ⟨pg15p5_vol_wellPosed R cert γstar CSig hadm ϱ hW.1, ?_, ?_⟩
  · intro K hK hKc L hL hLc ε hε
    have hz := (thm_app_pl_volatility_i R cert γstar CSig hadm).1 K hK hKc L hL hLc
      (ε / 2) (by positivity)
    have hr := pg15p6_lag_error R cert γstar CSig hadm ϱ H hW (ε / 2) (by positivity)
    filter_upwards [hz, hr] with n hzn hrn
    intro i ℓ hi hℓ
    have hzero := hzn i (ℓ : ℤ) (by simpa [rowNum] using hi) (by simpa using hℓ)
    have herr := hrn i ℓ
    calc
      |ridgeC cert (γstar n) (CSig n) β ℓ (B n) (plSpec α (c n) (N n)) i (ϱ n) -
          profC α (rowNum i / (N n : ℝ)) ((ℓ : ℝ) / gammaOf (N n) (B n))| =
          |(ridgeC cert (γstar n) (CSig n) β ℓ (B n) (plSpec α (c n) (N n)) i (ϱ n) -
              cbarZero cert (γstar n) (CSig n) β (B n) (plSpec α (c n) (N n)) i ℓ) +
            (cbarZero cert (γstar n) (CSig n) β (B n) (plSpec α (c n) (N n)) i ℓ -
              profC α (rowNum i / (N n : ℝ)) ((ℓ : ℝ) / gammaOf (N n) (B n)))| := by
            congr 1 <;> ring
      _ ≤ _ := abs_add_le _ _
      _ ≤ ε / 2 + ε / 2 := add_le_add herr (by simpa [rowNum] using hzero)
      _ = ε := by ring
  · intro K hK hKc ε hε
    have hz := (thm_app_pl_volatility_i R cert γstar CSig hadm).2 K hK hKc
      (ε / 2) (by positivity)
    have hr := pg15p5_vol_error R cert γstar CSig hadm ϱ H hW (ε / 2) (by positivity)
    have hγ := R.hγ.eventually_ge_atTop 1
    filter_upwards [hz, hr, hγ] with n hzn hrn hγn
    intro i hi
    have hzero := hzn i (by simpa [rowNum] using hi)
    have herr := hrn i
    have hγpos : 0 < gammaOf (N n) (B n) := lt_of_lt_of_le zero_lt_one hγn
    calc
      |ridgeV cert (γstar n) (CSig n) β (B n) (plSpec α (c n) (N n)) i (ϱ n) /
          gammaOf (N n) (B n) - profGamma α (rowNum i / (N n : ℝ))| =
          |(ridgeV cert (γstar n) (CSig n) β (B n) (plSpec α (c n) (N n)) i (ϱ n) /
              gammaOf (N n) (B n) -
            vZero cert (γstar n) (CSig n) β (B n) (plSpec α (c n) (N n)) i /
              gammaOf (N n) (B n)) +
            (vZero cert (γstar n) (CSig n) β (B n) (plSpec α (c n) (N n)) i /
              gammaOf (N n) (B n) - profGamma α (rowNum i / (N n : ℝ)))| := by
            congr 1 <;> ring
      _ ≤ _ := abs_add_le _ _
      _ ≤ |ridgeV cert (γstar n) (CSig n) β (B n) (plSpec α (c n) (N n)) i (ϱ n) -
            vZero cert (γstar n) (CSig n) β (B n) (plSpec α (c n) (N n)) i| + ε / 2 := by
          rw [← sub_div, abs_div, abs_of_pos hγpos]
          exact add_le_add (div_le_self (abs_nonneg _) hγn) (by simpa [rowNum] using hzero)
      _ ≤ ε / 2 + ε / 2 := add_le_add herr le_rfl
      _ = ε := by ring

/-- `prop:app-pl-ridge` (snapshot `cr-2026-10-23`), `thm:app-pl-volatility`(ii) with `𝔳_i(ϱ_N)` (uniform form, card §6 #1).
Statement (LaTeX, verbatim from sections/06-power-law/section.tex):

\begin{proposition}[Negligible ridge]\label{prop:app-pl-ridge}
Assume \cref{assum:app-pl-regime}. Let $0<\ridge_N\le\bar z_N$ and let $H_N\ge0$ be
integers with
\begin{equation}\label{eqn:app-pl-ridge-window}
\frac{\ridge_N\,Q_\gamma}{c_NN^{-\alpha}\gamma^2}\to0,\qquad
(1+H_N)\sqrt{D_\star}\,\ridge_N^{1/4}\to0,\qquad
E_\star\,\bmom^{H_N/3}\to0 .
\end{equation}
Then \cref{thm:app-pl-triple,thm:app-pl-drift,thm:app-pl-volatility},
\cref{cor:app-pl-endpoints,cor:app-pl-weighted} hold with $\mathfrak d_i(\ridge_N)$,
$\overline C_{i,\ell}(\ridge_N)$ and $\mathfrak v_i(\ridge_N)$ in place of the zero-ridge
coefficients. Such sequences $(\ridge_N,H_N)$ exist.
\end{proposition}
-/
theorem prop_app_pl_ridge_vol_ii {α β : ℝ} {N B : ℕ → ℕ} {c : ℕ → ℝ}
    (R : assum_app_pl_regime α β N B c)
    (cert : Muon.External.GaussianOpNorm) (γstar CSig : ℕ → ℝ)
    (hadm : ∀ n, zeroAdmissible (N n) (B n) (plSpec α (c n) (N n)) (γstar n) (CSig n))
    (ϱ : ℕ → ℝ) (H : ℕ → ℕ) (hW : ridgeWindow R ϱ H) (hα1 : α ≤ 1)
    (i : (n : ℕ) → Fin (N n)) (hi : Tendsto (fun n => rowIdx (i n)) atTop atTop) :
    ridgeVolWellPosed R cert γstar CSig ϱ ∧
    (∀ K : Set ℝ, K ⊆ Ioi 0 → IsCompact K → ∀ ε > 0, ∃ M : ℕ, ∀ᶠ n in atTop,
      ∀ j : Fin (N n), (M : ℝ) ≤ rowIdx j → icvRow β α (B n) j ∈ K →
        |sPow β 2 * ridgeV cert (γstar n) (CSig n) β (B n) (plSpec α (c n) (N n)) j (ϱ n) -
          (1 + 2 * c0 * icvRow β α (B n) j ^ (α / 2) + icvRow β α (B n) j ^ α)| ≤ ε) ∧
    (Tendsto (fun n => icvRow β α (B n) (i n)) atTop (𝓝 0) →
      Tendsto (fun n => ridgeV cert (γstar n) (CSig n) β (B n) (plSpec α (c n) (N n)) (i n) (ϱ n))
        atTop (𝓝 (1 / sPow β 2))) ∧
    (Tendsto (fun n => icvRow β α (B n) (i n)) atTop atTop →
      IsEquivalent atTop
        (fun n => ridgeV cert (γstar n) (CSig n) β (B n) (plSpec α (c n) (N n)) (i n) (ϱ n))
        (fun n => gammaOf (N n) (B n) * profGamma α (rowFrac (i n)))) ∧
    (Tendsto (fun n => icvRow β α (B n) (i n)) atTop atTop →
      Tendsto (fun n => rowFrac (i n)) atTop (𝓝 0) → α < 1 →
      IsEquivalent atTop
        (fun n => ridgeV cert (γstar n) (CSig n) β (B n) (plSpec α (c n) (N n)) (i n) (ϱ n))
        (fun n => gammaOf (N n) (B n) * rowFrac (i n) ^ α *
          Real.log (((N n : ℝ) / rowIdx (i n)) ^ α) ^ 2 / (1 - α))) ∧
    (Tendsto (fun n => icvRow β α (B n) (i n)) atTop atTop →
      Tendsto (fun n => rowFrac (i n)) atTop (𝓝 0) → α = 1 →
      IsEquivalent atTop
        (fun n => ridgeV cert (γstar n) (CSig n) β (B n) (plSpec α (c n) (N n)) (i n) (ϱ n))
        (fun n => 4 / 9 * (rowIdx (i n) / (B n : ℝ)) *
          Real.log ((N n : ℝ) / rowIdx (i n)) ^ 3)) := by
  have hz := thm_app_pl_volatility_ii R cert γstar CSig hadm hα1
  have hseq := hz.2 i hi
  have heq := pg15p6_vol_equiv R cert γstar CSig hadm ϱ H hW i
  have hsub := pg15p6_vol_sub_tendsto_zero R cert γstar CSig hadm ϱ H hW i
  refine ⟨pg15p5_vol_wellPosed R cert γstar CSig hadm ϱ hW.1, ?_, ?_, ?_, ?_, ?_⟩
  · intro K hK hKc ε hε
    have hs : 0 < sPow β 2 := pg15p4_endpoints_sPow_two_pos R.hβ0 R.hβ1
    obtain ⟨M, hzero⟩ := hz.1 K hK hKc (ε / 2) (by positivity)
    have herr := pg15p5_vol_error R cert γstar CSig hadm ϱ H hW
      (ε / (2 * sPow β 2)) (by positivity)
    refine ⟨M, ?_⟩
    filter_upwards [hzero, herr] with n hzn hrn
    intro j hj hmem
    have h0 := hzn j hj hmem
    have hr := hrn j
    calc
      |sPow β 2 * ridgeV cert (γstar n) (CSig n) β (B n)
          (plSpec α (c n) (N n)) j (ϱ n) -
          (1 + 2 * c0 * icvRow β α (B n) j ^ (α / 2) + icvRow β α (B n) j ^ α)| =
          |sPow β 2 * (ridgeV cert (γstar n) (CSig n) β (B n)
              (plSpec α (c n) (N n)) j (ϱ n) -
            vZero cert (γstar n) (CSig n) β (B n) (plSpec α (c n) (N n)) j) +
            (sPow β 2 * vZero cert (γstar n) (CSig n) β (B n)
              (plSpec α (c n) (N n)) j -
            (1 + 2 * c0 * icvRow β α (B n) j ^ (α / 2) +
              icvRow β α (B n) j ^ α))| := by congr 1 <;> ring
      _ ≤ _ := abs_add_le _ _
      _ ≤ sPow β 2 * |ridgeV cert (γstar n) (CSig n) β (B n)
            (plSpec α (c n) (N n)) j (ϱ n) -
          vZero cert (γstar n) (CSig n) β (B n) (plSpec α (c n) (N n)) j| + ε / 2 := by
            rw [abs_mul, abs_of_pos hs]
            exact add_le_add le_rfl h0
      _ ≤ sPow β 2 * (ε / (2 * sPow β 2)) + ε / 2 :=
        add_le_add (mul_le_mul_of_nonneg_left hr hs.le) le_rfl
      _ = ε := by field_simp [hs.ne']; ring
  · intro h
    simpa only [sub_add_cancel, zero_add] using hsub.add (hseq.1 h)
  · intro h
    exact heq.trans (hseq.2.1 h)
  · intro h hfrac hα
    exact heq.trans (hseq.2.2.1 h hfrac hα)
  · intro h hfrac hα
    exact heq.trans (hseq.2.2.2 h hfrac hα)

/-- `prop:app-pl-ridge` (snapshot `cr-2026-10-23`), `thm:app-pl-volatility`(iii) with `𝔳_i(ϱ_N)` (`α > 1`).
Statement (LaTeX, verbatim from sections/06-power-law/section.tex):

\begin{proposition}[Negligible ridge]\label{prop:app-pl-ridge}
Assume \cref{assum:app-pl-regime}. Let $0<\ridge_N\le\bar z_N$ and let $H_N\ge0$ be
integers with
\begin{equation}\label{eqn:app-pl-ridge-window}
\frac{\ridge_N\,Q_\gamma}{c_NN^{-\alpha}\gamma^2}\to0,\qquad
(1+H_N)\sqrt{D_\star}\,\ridge_N^{1/4}\to0,\qquad
E_\star\,\bmom^{H_N/3}\to0 .
\end{equation}
Then \cref{thm:app-pl-triple,thm:app-pl-drift,thm:app-pl-volatility},
\cref{cor:app-pl-endpoints,cor:app-pl-weighted} hold with $\mathfrak d_i(\ridge_N)$,
$\overline C_{i,\ell}(\ridge_N)$ and $\mathfrak v_i(\ridge_N)$ in place of the zero-ridge
coefficients. Such sequences $(\ridge_N,H_N)$ exist.
\end{proposition}
-/
theorem prop_app_pl_ridge_vol_iii {α β : ℝ} {N B : ℕ → ℕ} {c : ℕ → ℝ}
    (R : assum_app_pl_regime α β N B c)
    (cert : Muon.External.GaussianOpNorm) (γstar CSig : ℕ → ℝ)
    (hadm : ∀ n, zeroAdmissible (N n) (B n) (plSpec α (c n) (N n)) (γstar n) (CSig n))
    (ϱ : ℕ → ℝ) (H : ℕ → ℕ) (hW : ridgeWindow R ϱ H) (hα1 : 1 < α)
    (i : (n : ℕ) → Fin (N n)) (hi : Tendsto (fun n => rowIdx (i n)) atTop atTop) :
    ridgeVolWellPosed R cert γstar CSig ϱ ∧
    ((∀ X0 : ℝ, 0 < X0 → Tendsto (fun n => rowIdx (i n) / icCross α (B n)) atTop (𝓝 X0) →
      Tendsto (fun n => ridgeV cert (γstar n) (CSig n) β (B n) (plSpec α (c n) (N n)) (i n) (ϱ n))
        atTop (𝓝 (profG α β X0))) ∧
    (Tendsto (fun n => rowIdx (i n) / icCross α (B n)) atTop (𝓝 0) →
      Tendsto (fun n => ridgeV cert (γstar n) (CSig n) β (B n) (plSpec α (c n) (N n)) (i n) (ϱ n))
        atTop (𝓝 (1 / sPow β 2))) ∧
    (Tendsto (fun n => rowIdx (i n) / icCross α (B n)) atTop atTop →
      IsEquivalent atTop
        (fun n => ridgeV cert (γstar n) (CSig n) β (B n) (plSpec α (c n) (N n)) (i n) (ϱ n))
        (fun n => gammaOf (N n) (B n) * profGamma α (rowFrac (i n)))) ∧
    (Tendsto (fun n => rowIdx (i n) / icCross α (B n)) atTop atTop →
      Tendsto (fun n => rowFrac (i n)) atTop (𝓝 0) →
      IsEquivalent atTop
        (fun n => ridgeV cert (γstar n) (CSig n) β (B n) (plSpec α (c n) (N n)) (i n) (ϱ n))
        (fun n => 4 * Kc α ^ 2 / (α - 1) * (rowIdx (i n) / (B n : ℝ))))) := by
  have hseq := thm_app_pl_volatility_iii R cert γstar CSig hadm hα1 i hi
  have heq := pg15p6_vol_equiv R cert γstar CSig hadm ϱ H hW i
  have hsub := pg15p6_vol_sub_tendsto_zero R cert γstar CSig hadm ϱ H hW i
  refine ⟨pg15p5_vol_wellPosed R cert γstar CSig hadm ϱ hW.1, ?_, ?_, ?_, ?_⟩
  · intro X0 hX0 h
    simpa only [sub_add_cancel, zero_add] using hsub.add (hseq.1 X0 hX0 h)
  · intro h
    simpa only [sub_add_cancel, zero_add] using hsub.add (hseq.2.1 h)
  · intro h
    exact heq.trans (hseq.2.2.1 h)
  · intro h hfrac
    exact heq.trans (hseq.2.2.2 h hfrac)

/-- `prop:app-pl-ridge` (snapshot `cr-2026-10-23`), `cor:app-pl-endpoints`(i) with `𝔡_i(ϱ_N)`, `𝔳_i(ϱ_N)`.
Statement (LaTeX, verbatim from sections/06-power-law/section.tex):

\begin{proposition}[Negligible ridge]\label{prop:app-pl-ridge}
Assume \cref{assum:app-pl-regime}. Let $0<\ridge_N\le\bar z_N$ and let $H_N\ge0$ be
integers with
\begin{equation}\label{eqn:app-pl-ridge-window}
\frac{\ridge_N\,Q_\gamma}{c_NN^{-\alpha}\gamma^2}\to0,\qquad
(1+H_N)\sqrt{D_\star}\,\ridge_N^{1/4}\to0,\qquad
E_\star\,\bmom^{H_N/3}\to0 .
\end{equation}
Then \cref{thm:app-pl-triple,thm:app-pl-drift,thm:app-pl-volatility},
\cref{cor:app-pl-endpoints,cor:app-pl-weighted} hold with $\mathfrak d_i(\ridge_N)$,
$\overline C_{i,\ell}(\ridge_N)$ and $\mathfrak v_i(\ridge_N)$ in place of the zero-ridge
coefficients. Such sequences $(\ridge_N,H_N)$ exist.
\end{proposition}
-/
theorem prop_app_pl_ridge_endpoints_i {α β : ℝ} {N B : ℕ → ℕ} {c : ℕ → ℝ}
    (R : assum_app_pl_regime α β N B c)
    (cert : Muon.External.GaussianOpNorm) (γstar CSig : ℕ → ℝ)
    (hadm : ∀ n, zeroAdmissible (N n) (B n) (plSpec α (c n) (N n)) (γstar n) (CSig n))
    (ν ν' : ℕ → FiniteMeasure ℝ)
    (hν : ∀ n, (ν n : Measure ℝ) =
      ENNReal.ofReal ((B n : ℝ)⁻¹) • ∑ i : Fin (N n), Measure.dirac (plSpec α (c n) (N n) i))
    (hν' : ∀ n, (ν' n : Measure ℝ) = ENNReal.ofReal (gammaOf (N n) (B n)) • Measure.dirac (1 : ℝ))
    (ϱ : ℕ → ℝ) (H : ℕ → ℕ) (hW : ridgeWindow R ϱ H) (hα : α ≤ 1)
    (i : (n : ℕ) → Fin (N n)) (hi : Tendsto (fun n => rowNum (i n)) atTop atTop) :
    ridgeDriftWellPosed R ν ν' ϱ ∧ ridgeVolWellPosed R cert γstar CSig ϱ ∧
    ∀ x ∈ Ioi (0 : ℝ),
      Tendsto (fun n => rowNum (i n) / icStar β α (N n) (B n)) atTop (𝓝 x) →
        Tendsto (fun n => Real.sqrt 2 *
            dRidge β (ν n) (ν' n) (plSpec α (c n) (N n)) (i n) (ϱ n) /
            icdA α (c n) (N n) (B n)) atTop (𝓝 (1 + x ^ (-α / 2))) ∧
        Tendsto (fun n => sPow β 2 *
            ridgeV cert (γstar n) (CSig n) β (B n) (plSpec α (c n) (N n)) (i n) (ϱ n)) atTop
          (𝓝 (1 + 2 * x ^ (α / 2) + (c0 ^ 2)⁻¹ * x ^ α)) := by
  have hd := prop_app_pl_ridge_drift_i R ν ν' hν hν' ϱ H hW hα i hi
  have hz := cor_app_pl_endpoints_i R cert γstar CSig hadm hα i hi
  have hsub := pg15p6_vol_sub_tendsto_zero R cert γstar CSig hadm ϱ H hW i
  refine ⟨hd.1, pg15p5_vol_wellPosed R cert γstar CSig hadm ϱ hW.1, ?_⟩
  intro x hx hcross
  have hcross' : Tendsto (fun n => rowNum (i n) / icdIdx β α (N n) (B n))
      atTop (𝓝 x) := by
    simpa [icStar, hα] using hcross
  have hzero := hz x hx hcross
  refine ⟨hd.2.1 x hx hcross', ?_⟩
  have herr := (tendsto_const_nhds (x := sPow β 2)).mul hsub
  simpa only [mul_sub, sub_add_cancel, mul_zero, zero_add] using herr.add hzero.2.1

/-- `prop:app-pl-ridge` (snapshot `cr-2026-10-23`), `cor:app-pl-endpoints`(ii) with `𝔡_i(ϱ_N)`, `𝔳_i(ϱ_N)`.
Statement (LaTeX, verbatim from sections/06-power-law/section.tex):

\begin{proposition}[Negligible ridge]\label{prop:app-pl-ridge}
Assume \cref{assum:app-pl-regime}. Let $0<\ridge_N\le\bar z_N$ and let $H_N\ge0$ be
integers with
\begin{equation}\label{eqn:app-pl-ridge-window}
\frac{\ridge_N\,Q_\gamma}{c_NN^{-\alpha}\gamma^2}\to0,\qquad
(1+H_N)\sqrt{D_\star}\,\ridge_N^{1/4}\to0,\qquad
E_\star\,\bmom^{H_N/3}\to0 .
\end{equation}
Then \cref{thm:app-pl-triple,thm:app-pl-drift,thm:app-pl-volatility},
\cref{cor:app-pl-endpoints,cor:app-pl-weighted} hold with $\mathfrak d_i(\ridge_N)$,
$\overline C_{i,\ell}(\ridge_N)$ and $\mathfrak v_i(\ridge_N)$ in place of the zero-ridge
coefficients. Such sequences $(\ridge_N,H_N)$ exist.
\end{proposition}
-/
theorem prop_app_pl_ridge_endpoints_ii {α β : ℝ} {N B : ℕ → ℕ} {c : ℕ → ℝ}
    (R : assum_app_pl_regime α β N B c)
    (cert : Muon.External.GaussianOpNorm) (γstar CSig : ℕ → ℝ)
    (hadm : ∀ n, zeroAdmissible (N n) (B n) (plSpec α (c n) (N n)) (γstar n) (CSig n))
    (ν ν' : ℕ → FiniteMeasure ℝ)
    (hν : ∀ n, (ν n : Measure ℝ) =
      ENNReal.ofReal ((B n : ℝ)⁻¹) • ∑ i : Fin (N n), Measure.dirac (plSpec α (c n) (N n) i))
    (hν' : ∀ n, (ν' n : Measure ℝ) = ENNReal.ofReal (gammaOf (N n) (B n)) • Measure.dirac (1 : ℝ))
    (ϱ : ℕ → ℝ) (H : ℕ → ℕ) (hW : ridgeWindow R ϱ H)
    (i : (n : ℕ) → Fin (N n)) (hi : Tendsto (fun n => rowNum (i n)) atTop atTop) :
    ridgeDriftWellPosed R ν ν' ϱ ∧ ridgeVolWellPosed R cert γstar CSig ϱ ∧
    ((Tendsto (fun n => rowNum (i n) / icStar β α (N n) (B n)) atTop (𝓝 0) →
      IsEquivalent atTop
          (fun n => Real.sqrt 2 * dRidge β (ν n) (ν' n) (plSpec α (c n) (N n)) (i n) (ϱ n))
          (fun n => Real.sqrt (plSpec α (c n) (N n) (i n) / (gammaOf (N n) (B n) * sPow β 2))) ∧
        Tendsto (fun n => ridgeV cert (γstar n) (CSig n) β (B n) (plSpec α (c n) (N n)) (i n) (ϱ n))
          atTop (𝓝 (1 / sPow β 2))) ∧
    (Tendsto (fun n => rowNum (i n) / icStar β α (N n) (B n)) atTop atTop →
      IsEquivalent atTop
          (fun n => Real.sqrt 2 * dRidge β (ν n) (ν' n) (plSpec α (c n) (N n)) (i n) (ϱ n))
          (fun n => aN α (c n) (N n) * profPsi α (rowNum (i n) / (N n : ℝ))) ∧
        IsEquivalent atTop
          (fun n => ridgeV cert (γstar n) (CSig n) β (B n) (plSpec α (c n) (N n)) (i n) (ϱ n))
          (fun n => gammaOf (N n) (B n) * profGamma α (rowNum (i n) / (N n : ℝ))))) := by
  rcases le_or_gt α 1 with hα | hα
  · have hd := prop_app_pl_ridge_drift_i R ν ν' hν hν' ϱ H hW hα i hi
    have hv := prop_app_pl_ridge_vol_ii R cert γstar CSig hadm ϱ H hW hα i hi
    refine ⟨hd.1, hv.1, ?_, ?_⟩
    · intro h
      have hs : Tendsto (fun n => rowNum (i n) / icdIdx β α (N n) (B n))
          atTop (𝓝 0) := by
        simpa [icStar, hα] using h
      refine ⟨hd.2.2.1 hs, hv.2.2.1 ?_⟩
      rw [show (fun n => icvRow β α (B n) (i n)) =
          fun n => (c0 ^ (2 / α))⁻¹ *
            (rowNum (i n) / icdIdx β α (N n) (B n)) from
        funext fun n => pg15_icvRow_eq β α (B n) (N n) (i n)]
      simpa using hs.const_mul (c0 ^ (2 / α))⁻¹
    · intro h
      have hs : Tendsto (fun n => rowNum (i n) / icdIdx β α (N n) (B n))
          atTop atTop := by
        simpa [icStar, hα] using h
      refine ⟨(hd.2.2.2 hs).1, hv.2.2.2.1 ?_⟩
      rw [show (fun n => icvRow β α (B n) (i n)) =
          fun n => (c0 ^ (2 / α))⁻¹ *
            (rowNum (i n) / icdIdx β α (N n) (B n)) from
        funext fun n => pg15_icvRow_eq β α (B n) (N n) (i n)]
      have hc : 0 < (c0 ^ (2 / α))⁻¹ := by
        have hc0 : 0 < c0 := by unfold c0; exact Real.sqrt_pos.2 (by positivity)
        positivity
      exact hs.const_mul_atTop hc
  · have hd := prop_app_pl_ridge_drift_ii R ν ν' hν hν' ϱ H hW hα i hi
    have hv := prop_app_pl_ridge_vol_iii R cert γstar CSig hadm ϱ H hW hα i hi
    refine ⟨hd.1, hv.1, ?_, ?_⟩
    · intro h
      have hs : Tendsto (fun n => rowNum (i n) / icCross α (B n)) atTop (𝓝 0) := by
        simpa [icStar, not_le_of_gt hα] using h
      exact ⟨hd.2.2.1 hs, hv.2.2.1 hs⟩
    · intro h
      have hs : Tendsto (fun n => rowNum (i n) / icCross α (B n)) atTop atTop := by
        simpa [icStar, not_le_of_gt hα] using h
      exact ⟨(hd.2.2.2 hs).1, hv.2.2.2.1 hs⟩

/-- `prop:app-pl-ridge` (snapshot `cr-2026-10-23`), `cor:app-pl-weighted` with `𝔡_i(ϱ_N)`, `𝔳_i(ϱ_N)`. Statement (LaTeX, verbatim from sections/06-power-law/section.tex):

\begin{proposition}[Negligible ridge]\label{prop:app-pl-ridge}
Assume \cref{assum:app-pl-regime}. Let $0<\ridge_N\le\bar z_N$ and let $H_N\ge0$ be
integers with
\begin{equation}\label{eqn:app-pl-ridge-window}
\frac{\ridge_N\,Q_\gamma}{c_NN^{-\alpha}\gamma^2}\to0,\qquad
(1+H_N)\sqrt{D_\star}\,\ridge_N^{1/4}\to0,\qquad
E_\star\,\bmom^{H_N/3}\to0 .
\end{equation}
Then \cref{thm:app-pl-triple,thm:app-pl-drift,thm:app-pl-volatility},
\cref{cor:app-pl-endpoints,cor:app-pl-weighted} hold with $\mathfrak d_i(\ridge_N)$,
$\overline C_{i,\ell}(\ridge_N)$ and $\mathfrak v_i(\ridge_N)$ in place of the zero-ridge
coefficients. Such sequences $(\ridge_N,H_N)$ exist.
\end{proposition}
-/
theorem prop_app_pl_ridge_weighted {α β : ℝ} {N B : ℕ → ℕ} {c : ℕ → ℝ}
    (R : assum_app_pl_regime α β N B c)
    (cert : Muon.External.GaussianOpNorm) (γstar CSig : ℕ → ℝ)
    (hadm : ∀ n, zeroAdmissible (N n) (B n) (plSpec α (c n) (N n)) (γstar n) (CSig n))
    (ν ν' : ℕ → FiniteMeasure ℝ)
    (hν : ∀ n, (ν n : Measure ℝ) =
      ENNReal.ofReal ((B n : ℝ)⁻¹) • ∑ i : Fin (N n), Measure.dirac (plSpec α (c n) (N n) i))
    (hν' : ∀ n, (ν' n : Measure ℝ) = ENNReal.ofReal (gammaOf (N n) (B n)) • Measure.dirac (1 : ℝ))
    (ϱ : ℕ → ℝ) (H : ℕ → ℕ) (hW : ridgeWindow R ϱ H)
    (nN : ℕ → ℕ) (hnN : ∀ n, 1 ≤ nN n ∧ nN n ≤ N n)
    (hn : Tendsto (fun n => (nN n : ℝ)) atTop atTop)
    (I : (n : ℕ) → Finset (Fin (N n))) (hI : ∀ n, ∀ i ∈ I n, nN n ≤ (i : ℕ) + 1)
    (a : (n : ℕ) → Fin (N n) → ℝ) (ha : ∀ n i, 0 ≤ a n i)
    (hpos : ∀ n, 0 < ∑ i ∈ I n, a n i) :
    ridgeDriftWellPosed R ν ν' ϱ ∧ ridgeVolWellPosed R cert γstar CSig ϱ ∧
    Tendsto (fun n => (∑ i ∈ I n, a n i * dRidge β (ν n) (ν' n) (plSpec α (c n) (N n)) i (ϱ n)) /
        (∑ i ∈ I n, a n i * dHatDrift α β (c n) (N n) (B n) i)) atTop (𝓝 1) ∧
    Tendsto (fun n => (∑ i ∈ I n, a n i *
          ridgeV cert (γstar n) (CSig n) β (B n) (plSpec α (c n) (N n)) i (ϱ n)) /
        (∑ i ∈ I n, a n i *
          (if α ≤ 1 then vhatApprox β α (B n) i else vhatSuper β α (B n) i))) atTop (𝓝 1) := by
  have ht := prop_app_pl_ridge_triple R cert γstar CSig hadm ν ν' hν hν' ϱ H hW nN hnN hn
  refine ⟨ht.1, ht.2.1, ?_, ?_⟩
  · rw [Metric.tendsto_atTop]
    intro ε hε
    have he := ht.2.2 (ε / 2) (by positivity)
    rw [Filter.eventually_atTop] at he
    obtain ⟨n0, hn0⟩ := he
    refine ⟨n0, fun n hn => ?_⟩
    rw [Real.dist_eq]
    apply lt_of_le_of_lt (pg15_weighted_ratio_le (I n) (a n)
      (fun i => dRidge β (ν n) (ν' n) (plSpec α (c n) (N n)) i (ϱ n))
      (fun i => dHatDrift α β (c n) (N n) (B n) i) (ha n) (pg15_dHat_pos R n)
      (hpos n) (ε := ε / 2) ?_) (by linarith)
    intro i hi
    exact (hn0 n hn i (by
      have hi' : (nN n : ℝ) ≤ (((i : ℕ) + 1 : ℕ) : ℝ) := by exact_mod_cast hI n i hi
      simpa [rowNum] using hi')).1
  · rw [Metric.tendsto_atTop]
    intro ε hε
    have he := ht.2.2 (ε / 2) (by positivity)
    rw [Filter.eventually_atTop] at he
    obtain ⟨n0, hn0⟩ := he
    refine ⟨n0, fun n hn => ?_⟩
    rw [Real.dist_eq]
    apply lt_of_le_of_lt (pg15_weighted_ratio_le (I n) (a n)
      (fun i => ridgeV cert (γstar n) (CSig n) β (B n) (plSpec α (c n) (N n)) i (ϱ n))
      (fun i => if α ≤ 1 then vhatApprox β α (B n) i else vhatSuper β α (B n) i)
      (ha n) (pg15_vHat_pos R n) (hpos n) (ε := ε / 2) ?_) (by linarith)
    intro i hi
    exact (hn0 n hn i (by
      have hi' : (nN n : ℝ) ≤ (((i : ℕ) + 1 : ℕ) : ℝ) := by exact_mod_cast hI n i hi
      simpa [rowNum] using hi')).2

end Muon.PowerLaw

end
