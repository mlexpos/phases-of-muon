import Muon.Volatility.LagReduction
import Muon.Volatility.Replacement
import Muon.Volatility.TreeClosure
import Muon.Volatility.Replication
import Muon.Volatility.HalfCandidates
import Muon.Setup.Regime

/-!
# Appendix D, work package L-D.13: tree extension, lag kernels, integrated identification

Work package L-D.13 (interface draft). Snapshot `cr-2026-10-23`.
Source of record: `sections/04-volatility/section.tex`:
`lem:app-vol-tree-extension` (l.1185–1202), `thm:app-vol-lag-kernel` (l.1276–1310),
`rem:app-vol-other-filters` (l.1343–1352), `thm:app-vol-integrated` (l.1354–1384),
and the display `eqn:app-vol-rows` (l.2776).
Card: `sections/04-volatility/CARD.md` §2, §3, §5 (row L-D.13), §6 (R3, R14, R15, R17, R22).
The measures `eqn:app-vol-measures` and `eqn:app-vol-vij(-actual)` of the card's L-D.13 row are stated here as definitions.

Reused, not redefined: `def_app_vol_tree`, `treeWord`, `cutoffMat`, `cutoffDelta`, `volDR`
(`TreeDef`, `TreeClosure`); `def_app_vol_replication`, `replIdx` (`Replication`);
`def_app_vol_lag`, `integratedLag`, `weightedGamma`, `def_app_vol_product`, `indepUpd`,
`indepSpaceLaw`, `SizeFin`, `SizeSeq` (`Defs`); `finiteTimeCov` (`LagReduction`);
`contraction`, `contractionRes`, `iotaF`, `omegaF`, `supNorm`, `lipConst`, `IsOddBddLip`
(`OddSpectral`); `zbarRaw` (`HalfCandidates`); `frozenBuf` (`Setup.Frozen`);
`SetupRegime` (`Setup.Regime`); `Muon.Dynamics.kStar`; `Muon.External.GaussianOpNorm`.

Encoding decisions:
* Diagonal tests. As in `lem_app_vol_tree_closure`, a test is diagonal in the eigenbasis
  `S.uOut` (resp. `S.vIn`) with entries `Fd` (resp. `Gd`): `Fm = S.uOut * diagonal Fd * S.uOutᵀ`.
  The response depends on a test only through `Fd`, `Gd`, the spectra and the batch size, so the
  response functions take `Fd`, `Gd` directly. `k_ℓ = k_ℓ[Σ_out, Σ_in]` is the response at
  `Fd = S.μ`, `Gd = S.lam`.
* Continuous extension (`lem:app-vol-tree-extension`(ii)). `treeApprox D f k` is a polynomial
  approximant of `f` on `[-D, D]` at accuracy `1/(k+1)` (`exists_polynomial_near_of_continuousOn`),
  chosen from `f` and `D` only. `treeRespExt` is the limit of the polynomial responses. Only odd
  coefficients enter `def_app_vol_tree`, so the limit is the odd extension. The radius `D` is a
  parameter (card R22); the cutoff response uses `D = volDR cert R CSig γstar` (`D_R`).
* Limits in `J, R` (`thm:app-vol-lag-kernel`). `lagResp` is `limUnder` over
  `atTop ×ˢ atTop : Filter (ℕ × ℝ)`. Its existence is the first conjunct of
  `thm_app_vol_lag_kernel_exists`; the value is junk without it (card §2).
* Constants. `γ⋆^{3/2}` is written `γstar * Real.sqrt γstar`; `K⋆` is
  `Muon.Dynamics.kStar CSig γstar ϱ₋`. Operator norms of the test matrices enter as `opNorm`.
* Integrals. Every integral is parenthesized. Integrability of the integrand over the square is
  a conjunct of `thm_app_vol_integrated_i`.
* Ridges. `I = Set.Icc ϱlo ϱhi` with `0 < ϱlo ≤ ϱhi` (as in `Setup.Regime`). The deterministic
  statements `thm:app-vol-integrated`(i)–(iii) are stated for an arbitrary compact interval in
  `(0,∞)` at a fixed dimension (card R17).
* Quantifier order. Time `t`, the lag-independent tests and the ridges are chosen after `ε` and
  the eventual index, because the source's bounds are uniform in them (card §3, R14).
* Standing assumptions. `SizeFin` for fixed-dimension statements (card R20); `SizeSeq` with
  `Ω : ℕ → Type` and `P : ∀ k, Measure (Ω k)` for sequence statements; `SetupRegime` for
  `assum:app-setup-regime`.
* Spectral measures. `thm_app_vol_integrated_v` uses `Muon.nuOut`/`Muon.nuIn` for the spectral measures
  of `eqn:app-setup-spectral-measures`.
* Replications. `replVec N x` is the eigenvalue vector `x` repeated `N` times on `Fin (N * m)`,
  matching `def_app_vol_replication` with batch `B ↦ N * B`.
-/

set_option linter.style.longLine false

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped Matrix MatrixOrder ENNReal
open Matrix
open Muon Muon.Setup Muon.DetEquiv

noncomputable section

namespace Muon.Volatility

/-! ## Continuous extension of the tree response (`lem:app-vol-tree-extension`) -/

/-- Sup norm `‖f‖_D = sup_{|x| ≤ D} |f(x)|` of `lem:app-vol-tree-extension` (snapshot
`cr-2026-10-23`). -/
def supOn (D : ℝ) (f : ℝ → ℝ) : ℝ := ⨆ x : Set.Icc (-D) D, |f x|

open Classical in
/-- snapshot `cr-2026-10-23`. Polynomial approximant of `f` on `[-D, D]` at accuracy `1/(k+1)` (`lem:app-vol-tree-extension`(ii),
Weierstrass theorem `rudin1976principles` Thm 7.26). It is chosen from `f` and `D` only, so it does not
depend on the spectral data. Junk value `0` when `f` is not continuous on `[-D, D]`. -/
def treeApprox (D : ℝ) (f : ℝ → ℝ) (k : ℕ) : Polynomial ℝ :=
  if h : ContinuousOn f (Set.Icc (-D) D) then
    Classical.choose
      (exists_polynomial_near_of_continuousOn (-D) D f h (1 / ((k : ℝ) + 1)) (by positivity))
  else 0

/-- snapshot `cr-2026-10-23`. Continuous extension of the tree response `𝔑^{J,R}_ℓ` to functions on `[-D, D]`
(`lem:app-vol-tree-extension`(ii)): the limit of the responses of the polynomial approximants
`treeApprox`, with `def_app_vol_tree` (`def:app-vol-tree`) on the approximants. -/
def treeRespExt {m n : ℕ} (β : ℝ) (ℓ J : ℕ) (R : ℝ) (B : ℕ) (μ : Fin m → ℝ) (lam : Fin n → ℝ)
    (Fd : Fin m → ℝ) (Gd : Fin n → ℝ) (D : ℝ) (f g : ℝ → ℝ) : ℝ :=
  limUnder atTop (fun k : ℕ =>
    def_app_vol_tree β ℓ J R B μ lam Fd Gd (treeApprox D f k) (treeApprox D g k))

/-- snapshot `cr-2026-10-23`. Cutoff response `𝔑^{J,R}_ℓ[F,G](f₁,f₂)` on the radius `D_R = volDR` (`eqn:app-vol-tree-closure`,
`lem:app-vol-tree-extension`). The certificate `cert` fixes `D_R` through its constant; `γ⋆`, `C_Σ`
enter `volDR`. -/
def lagRespCut (cert : Muon.External.GaussianOpNorm) (γstar CSig : ℝ) {m n : ℕ} (β : ℝ) (ℓ J : ℕ)
    (R : ℝ) (B : ℕ) (μ : Fin m → ℝ) (lam : Fin n → ℝ) (Fd : Fin m → ℝ) (Gd : Fin n → ℝ)
    (f g : ℝ → ℝ) : ℝ :=
  treeRespExt β ℓ J R B μ lam Fd Gd (volDR cert R CSig γstar) f g

/-- snapshot `cr-2026-10-23`. Deterministic joint moment response `𝔑_ℓ[F,G](f₁,f₂) = lim_{J,R→∞} 𝔑^{J,R}_ℓ[F,G](f₁,f₂)`
with `J ∈ ℕ` and `R ∈ ℝ` tending to infinity independently (`eqn:app-vol-Phi`), as `limUnder`
over `atTop ×ˢ atTop`. Its existence is `thm_app_vol_lag_kernel_exists`; the value is junk without it. -/
def lagResp (cert : Muon.External.GaussianOpNorm) (γstar CSig : ℝ) {m n : ℕ} (β : ℝ) (ℓ : ℕ)
    (B : ℕ) (μ : Fin m → ℝ) (lam : Fin n → ℝ) (Fd : Fin m → ℝ) (Gd : Fin n → ℝ)
    (f g : ℝ → ℝ) : ℝ :=
  limUnder (atTop ×ˢ atTop : Filter (ℕ × ℝ)) (fun p : ℕ × ℝ =>
    lagRespCut cert γstar CSig β ℓ p.1 p.2 B μ lam Fd Gd f g)

/-- snapshot `cr-2026-10-23`. Integrated response `Γ̄[F,G](ϱ,ϱ') = C̄_0[F,G](ϱ,ϱ') + ∑_{ℓ≥1} (C̄_ℓ[F,G](ϱ,ϱ') +
C̄_ℓ[F,G](ϱ',ϱ))` (`eqn:app-vol-Gammabar`), with `C̄_ℓ[F,G](ϱ,ϱ') = 𝔑_ℓ[F,G](ω_ϱ,ω_ϱ')`
(`eqn:app-vol-lag-kernel`). The series is a `tsum`; its absolute convergence is
`thm_app_vol_integrated_iii`. -/
def lagGammaBar (cert : Muon.External.GaussianOpNorm) (γstar CSig : ℝ) {m n : ℕ} (β : ℝ) (B : ℕ)
    (μ : Fin m → ℝ) (lam : Fin n → ℝ) (Fd : Fin m → ℝ) (Gd : Fin n → ℝ) (ϱ ϱ' : ℝ) : ℝ :=
  lagResp cert γstar CSig β 0 B μ lam Fd Gd (omegaF ϱ) (omegaF ϱ') +
    ∑' ℓ : ℕ, (lagResp cert γstar CSig β (ℓ + 1) B μ lam Fd Gd (omegaF ϱ) (omegaF ϱ') +
      lagResp cert γstar CSig β (ℓ + 1) B μ lam Fd Gd (omegaF ϱ') (omegaF ϱ))

/-- snapshot `cr-2026-10-23`. Row coefficient `C̄_{i,ℓ}(ϱ,ϱ') = B · C̄_ℓ[u_i ⊗ u_i, Id](ϱ,ϱ')` (`eqn:app-vol-rows`, first
display), for `Σ_in = Id`, with output eigenvalues `μ` and input eigenvalues `lam`. The test
`u_i ⊗ u_i` has diagonal entries `Pi.single i 1`; `Id` has entries `1`. -/
def lagRowBar (cert : Muon.External.GaussianOpNorm) (γstar CSig : ℝ) {m n : ℕ} (β : ℝ) (ℓ B : ℕ)
    (μ : Fin m → ℝ) (lam : Fin n → ℝ) (i : Fin m) (ϱ ϱ' : ℝ) : ℝ :=
  (B : ℝ) * lagResp cert γstar CSig β ℓ B μ lam (Pi.single i 1) (fun _ : Fin n => (1 : ℝ))
    (omegaF ϱ) (omegaF ϱ')

/-- snapshot `cr-2026-10-23`. Mode coefficient `𝔳_i(ϱ,ϱ') = C̄_{i,0}(ϱ,ϱ') + ∑_{ℓ≥1} (C̄_{i,ℓ}(ϱ,ϱ') + C̄_{i,ℓ}(ϱ',ϱ))`
(`eqn:app-vol-rows`, second display). The absolute convergence of the series is owned by L-D.14 (mode
kernels); `rowVBar` makes no summability claim here. -/
def rowVBar (cert : Muon.External.GaussianOpNorm) (γstar CSig : ℝ) {m n : ℕ} (β : ℝ) (B : ℕ)
    (μ : Fin m → ℝ) (lam : Fin n → ℝ) (i : Fin m) (ϱ ϱ' : ℝ) : ℝ :=
  lagRowBar cert γstar CSig β 0 B μ lam i ϱ ϱ' +
    ∑' ℓ : ℕ, (lagRowBar cert γstar CSig β (ℓ + 1) B μ lam i ϱ ϱ' +
      lagRowBar cert γstar CSig β (ℓ + 1) B μ lam i ϱ' ϱ)

/-- snapshot `cr-2026-10-23`. Replicated eigenvalue vector: the eigenvalue `x_i` repeated `N` times, indexed by `Fin (N * m)`
through `replIdx` (`def:app-vol-replication`; the spectral measures of a replication are those
of the base). -/
def replVec {m : ℕ} (N : ℕ) (x : Fin m → ℝ) : Fin (N * m) → ℝ :=
  fun k => x ((replIdx m N).symm k).1

/-! ## Spectral projections, measures and mode coefficients (`eqn:app-vol-measures`, `eqn:app-vol-vij`) -/

open Classical in
/-- Indicator entries of the eigenvalue class `{k : x k = μ}`: the diagonal of `P_μ` in the eigenbasis
(snapshot `cr-2026-10-23`, `eqn:app-vol-measures`: `P_μ = ∑_{i: μ_i = μ} u_i ⊗ u_i`). -/
def classDiag {m : ℕ} (x : Fin m → ℝ) (μ : ℝ) : Fin m → ℝ := fun i => if x i = μ then 1 else 0

/-- `P_μ = ∑_{i: μ_i = μ} u_i ⊗ u_i` as the diagonal test `U diag(classDiag μ) Uᵀ`, snapshot
`cr-2026-10-23`. -/
def projOut {m n : ℕ} {C : Covariances m n} (S : SpectralData C) (μ : ℝ) : Mat m m :=
  S.uOut * Matrix.diagonal (classDiag S.μ μ) * S.uOutᵀ

/-- `P'_λ = ∑_{j: λ_j = λ} v_j ⊗ v_j` as the diagonal test `V diag(classDiag λ) Vᵀ`, snapshot
`cr-2026-10-23`. -/
def projIn {m n : ℕ} {C : Covariances m n} (S : SpectralData C) (l : ℝ) : Mat n n :=
  S.vIn * Matrix.diagonal (classDiag S.lam l) * S.vInᵀ

open Classical in
/-- Distinct output eigenvalues, as a finset (snapshot `cr-2026-10-23`; index set of the measures). -/
def muVals {m n : ℕ} {C : Covariances m n} (S : SpectralData C) : Finset ℝ :=
  Finset.univ.image S.μ

open Classical in
/-- Distinct input eigenvalues, as a finset (snapshot `cr-2026-10-23`). -/
def lamVals {m n : ℕ} {C : Covariances m n} (S : SpectralData C) : Finset ℝ :=
  Finset.univ.image S.lam

/-- Finite signed measure on the rectangle with masses `val μ l` at the points `(μ, l)` of the given
finsets, snapshot `cr-2026-10-23` (the sums over distinct eigenvalue pairs of `eqn:app-vol-measures`). -/
def pairMeasure (μs ls : Finset ℝ) (val : ℝ → ℝ → ℝ) : (ℝ × ℝ) →₀ ℝ :=
  ∑ μ ∈ μs, ∑ l ∈ ls, Finsupp.single (μ, l) (val μ l)

/-- `eqn:app-vol-measures`, snapshot `cr-2026-10-23`. Declaration of record. LaTeX, verbatim from `section.tex` (the whole environment):

```latex
\begin{equation}\label{eqn:app-vol-measures}
\begin{gathered}
\mathfrak C_\ell(\ridge,\ridge')\defeq\sum_{\mu,\lambda}C_\ell[P_\mu,P'_\lambda](\ridge,\ridge')\,\delta_{(\mu,\lambda)},\qquad
\overline{\mathfrak C}_\ell(\ridge,\ridge')\defeq\sum_{\mu,\lambda}\overline C_\ell[P_\mu,P'_\lambda](\ridge,\ridge')\,\delta_{(\mu,\lambda)},\\
\mathfrak C_{\mathrm{int}}(\ridge)\defeq\sum_{\mu,\lambda}\Gamma[P_\mu,P'_\lambda](\ridge,\ridge)\,\delta_{(\mu,\lambda)},\qquad
\zeta_\ridge\defeq\sum_{\mu,\lambda}\overline\Gamma[P_\mu,P'_\lambda](\ridge,\ridge)\,\delta_{(\mu,\lambda)} .
\end{gathered}
\end{equation}
```
-/
def measureCl {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {m n B : ℕ}
    (F : FrozenParams m n B) (S0 : FrozenSamples P m n B) (SP : SpectralData F.C)
    (ℓ : ℕ) (t : ℤ) (ϱ ϱ' : ℝ) : (ℝ × ℝ) →₀ ℝ :=
  pairMeasure (muVals SP) (lamVals SP)
    (fun μ l => def_app_vol_lag F S0 ℓ t (projOut SP μ) (projIn SP l) ϱ ϱ')

/-- `eqn:app-vol-measures`, snapshot `cr-2026-10-23`. Declaration of record. LaTeX, verbatim from `section.tex` (the whole environment):

```latex
\begin{equation}\label{eqn:app-vol-measures}
\begin{gathered}
\mathfrak C_\ell(\ridge,\ridge')\defeq\sum_{\mu,\lambda}C_\ell[P_\mu,P'_\lambda](\ridge,\ridge')\,\delta_{(\mu,\lambda)},\qquad
\overline{\mathfrak C}_\ell(\ridge,\ridge')\defeq\sum_{\mu,\lambda}\overline C_\ell[P_\mu,P'_\lambda](\ridge,\ridge')\,\delta_{(\mu,\lambda)},\\
\mathfrak C_{\mathrm{int}}(\ridge)\defeq\sum_{\mu,\lambda}\Gamma[P_\mu,P'_\lambda](\ridge,\ridge)\,\delta_{(\mu,\lambda)},\qquad
\zeta_\ridge\defeq\sum_{\mu,\lambda}\overline\Gamma[P_\mu,P'_\lambda](\ridge,\ridge)\,\delta_{(\mu,\lambda)} .
\end{gathered}
\end{equation}
```
-/
def measureClBar (cert : Muon.External.GaussianOpNorm) (γstar CSig : ℝ) {m n B : ℕ}
    (F : FrozenParams m n B) (SP : SpectralData F.C) (ℓ : ℕ) (ϱ ϱ' : ℝ) : (ℝ × ℝ) →₀ ℝ :=
  pairMeasure (muVals SP) (lamVals SP)
    (fun μ l => lagResp cert γstar CSig F.β ℓ B SP.μ SP.lam (classDiag SP.μ μ) (classDiag SP.lam l)
      (omegaF ϱ) (omegaF ϱ'))

/-- `eqn:app-vol-measures`, snapshot `cr-2026-10-23`. Declaration of record. LaTeX, verbatim from `section.tex` (the whole environment):

```latex
\begin{equation}\label{eqn:app-vol-measures}
\begin{gathered}
\mathfrak C_\ell(\ridge,\ridge')\defeq\sum_{\mu,\lambda}C_\ell[P_\mu,P'_\lambda](\ridge,\ridge')\,\delta_{(\mu,\lambda)},\qquad
\overline{\mathfrak C}_\ell(\ridge,\ridge')\defeq\sum_{\mu,\lambda}\overline C_\ell[P_\mu,P'_\lambda](\ridge,\ridge')\,\delta_{(\mu,\lambda)},\\
\mathfrak C_{\mathrm{int}}(\ridge)\defeq\sum_{\mu,\lambda}\Gamma[P_\mu,P'_\lambda](\ridge,\ridge)\,\delta_{(\mu,\lambda)},\qquad
\zeta_\ridge\defeq\sum_{\mu,\lambda}\overline\Gamma[P_\mu,P'_\lambda](\ridge,\ridge)\,\delta_{(\mu,\lambda)} .
\end{gathered}
\end{equation}
```
-/
def measureInt {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {m n B : ℕ}
    (F : FrozenParams m n B) (S0 : FrozenSamples P m n B) (SP : SpectralData F.C)
    (t : ℤ) (ϱ : ℝ) : (ℝ × ℝ) →₀ ℝ :=
  pairMeasure (muVals SP) (lamVals SP)
    (fun μ l => integratedLag F S0 t (projOut SP μ) (projIn SP l) ϱ ϱ)

/-- `eqn:app-vol-measures`, snapshot `cr-2026-10-23`. Declaration of record. LaTeX, verbatim from `section.tex` (the whole environment):

```latex
\begin{equation}\label{eqn:app-vol-measures}
\begin{gathered}
\mathfrak C_\ell(\ridge,\ridge')\defeq\sum_{\mu,\lambda}C_\ell[P_\mu,P'_\lambda](\ridge,\ridge')\,\delta_{(\mu,\lambda)},\qquad
\overline{\mathfrak C}_\ell(\ridge,\ridge')\defeq\sum_{\mu,\lambda}\overline C_\ell[P_\mu,P'_\lambda](\ridge,\ridge')\,\delta_{(\mu,\lambda)},\\
\mathfrak C_{\mathrm{int}}(\ridge)\defeq\sum_{\mu,\lambda}\Gamma[P_\mu,P'_\lambda](\ridge,\ridge)\,\delta_{(\mu,\lambda)},\qquad
\zeta_\ridge\defeq\sum_{\mu,\lambda}\overline\Gamma[P_\mu,P'_\lambda](\ridge,\ridge)\,\delta_{(\mu,\lambda)} .
\end{gathered}
\end{equation}
```
-/
def measureZeta (cert : Muon.External.GaussianOpNorm) (γstar CSig : ℝ) {m n B : ℕ}
    (F : FrozenParams m n B) (SP : SpectralData F.C) (ϱ : ℝ) : (ℝ × ℝ) →₀ ℝ :=
  pairMeasure (muVals SP) (lamVals SP)
    (fun μ l => lagGammaBar cert γstar CSig F.β B SP.μ SP.lam (classDiag SP.μ μ) (classDiag SP.lam l)
      ϱ ϱ)

open Classical in
/-- `eqn:app-vol-vij`, snapshot `cr-2026-10-23`. Declaration of record. LaTeX, verbatim from `section.tex` (the whole environment):

```latex
\begin{equation}\label{eqn:app-vol-vij}
\mathfrak v_{ij}(\ridge)\defeq\frac{B\,\zeta_\ridge(\{(\mu_i,\lambda_j)\})}{r_{\mu_i}\,t_{\lambda_j}} .
\end{equation}
```
-/
def modeVij (cert : Muon.External.GaussianOpNorm) (γstar CSig : ℝ) {m n B : ℕ}
    (F : FrozenParams m n B) (SP : SpectralData F.C) (ϱ : ℝ) (i : Fin m) (j : Fin n) : ℝ :=
  (B : ℝ) * measureZeta cert γstar CSig F SP ϱ (SP.μ i, SP.lam j) /
    ((((Finset.univ.filter fun k => SP.μ k = SP.μ i).card : ℕ) : ℝ) *
      (((Finset.univ.filter fun k => SP.lam k = SP.lam j).card : ℕ) : ℝ))

open Classical in
/-- `eqn:app-vol-vij-actual`, snapshot `cr-2026-10-23`. Declaration of record. LaTeX, verbatim from `section.tex` (the whole environment):

```latex
\begin{equation}\label{eqn:app-vol-vij-actual}
\mathsf v_{ij}(\ridge)\defeq\EE\big(({\mathsf S}^{\mathrm c}_t(\ridge))_{ij}\big)^2+2\sum_{\ell\ge1}\EE\big[({\mathsf S}^{\mathrm c}_t(\ridge))_{ij}({\mathsf S}^{\mathrm c}_{t+\ell}(\ridge))_{ij}\big]
\end{equation}
```
-/
def modeVijActual {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {m n B : ℕ}
    (F : FrozenParams m n B) (S0 : FrozenSamples P m n B) (SP : SpectralData F.C) (t : ℤ) (ϱ : ℝ)
    (i : Fin m) (j : Fin n) : ℝ :=
  -- mode entries `V_ij = u_iᵀ V v_j` (section.tex l.160–161) in the eigenbases of `SP`
  (∫ ω, ((SP.uOutᵀ * centredUpd F S0 ϱ t ω * SP.vIn) i j) ^ 2 ∂P) +
    2 * ∑' ℓ : ℕ, (∫ ω, (SP.uOutᵀ * centredUpd F S0 ϱ t ω * SP.vIn) i j *
      (SP.uOutᵀ * centredUpd F S0 ϱ (t + ((ℓ : ℤ) + 1)) ω * SP.vIn) i j ∂P)

/-! ## Tree extension (`lem:app-vol-tree-extension`) -/

/-! ### Private helpers for `lem:app-vol-tree-extension`(i), (ii) (proved here) -/

open Polynomial in
private lemma tx_coeff_comp_neg_X (p : Polynomial ℝ) (k : ℕ) :
    (p.comp (-X)).coeff k = (-1) ^ k * p.coeff k := by
  induction p using Polynomial.induction_on' generalizing k with
  | add p q hp hq => simp [add_comp, hp, hq, mul_add]
  | monomial n a =>
    have : (monomial n a).comp (-X) = C (a * (-1) ^ n) * X ^ n := by
      have h1 : (-X : Polynomial ℝ) = C (-1) * X := by simp
      rw [monomial_comp, h1, mul_pow, ← C_pow, C_mul]
      ring
    rw [this, coeff_C_mul, coeff_X_pow, coeff_monomial]
    by_cases h : n = k
    · subst h; simp; ring
    · simp [h, Ne.symm h]

open Polynomial in
private lemma tx_odd_coeff (p : Polynomial ℝ) (h : ∀ x : ℝ, p.eval (-x) = -p.eval x) (a : ℕ) :
    p.coeff (2 * a) = 0 := by
  have hp : p.comp (-X) = -p := by
    apply Polynomial.funext; intro x; simp [eval_comp, h x]
  have := congrArg (fun q => q.coeff (2 * a)) hp
  simp only [tx_coeff_comp_neg_X, coeff_neg] at this
  rw [pow_mul] at this
  simp at this
  linarith

open Polynomial in
private lemma tx_oddPart (P : Polynomial ℝ) :
    ∃ Q : Polynomial ℝ, (∀ x : ℝ, Q.eval x = (P.eval x - P.eval (-x)) / 2) ∧
      (∀ a : ℕ, Q.coeff (2 * a + 1) = P.coeff (2 * a + 1)) ∧ (∀ a : ℕ, Q.coeff (2 * a) = 0) := by
  refine ⟨C (1 / 2 : ℝ) * (P - P.comp (-X)), ?_, ?_, ?_⟩
  · intro x; simp [eval_comp]; ring
  · intro a; simp only [coeff_C_mul, coeff_sub, tx_coeff_comp_neg_X, pow_succ, pow_mul]; norm_num; ring
  · intro a; simp only [coeff_C_mul, coeff_sub, tx_coeff_comp_neg_X, pow_mul]; norm_num


private lemma tx_tree_eq_range {m n : ℕ} (β : ℝ) (ℓ J : ℕ) (R : ℝ) (B : ℕ) (μ : Fin m → ℝ)
    (lam : Fin n → ℝ) (Fd : Fin m → ℝ) (Gd : Fin n → ℝ) (f₁ f₂ : Polynomial ℝ) (M : ℕ)
    (h1 : f₁.natDegree < M) (h2 : f₂.natDegree < M) :
    def_app_vol_tree β ℓ J R B μ lam Fd Gd f₁ f₂ =
      ∑ a ∈ Finset.range M, ∑ b ∈ Finset.range M,
        f₁.coeff (2 * a + 1) * f₂.coeff (2 * b + 1) * treeMono β ℓ J R B μ lam Fd Gd a b := by
  unfold def_app_vol_tree
  have hin : ∀ a ∈ Finset.range (f₁.natDegree + 1),
      ∑ b ∈ Finset.range (f₂.natDegree + 1),
        f₁.coeff (2 * a + 1) * f₂.coeff (2 * b + 1) * treeMono β ℓ J R B μ lam Fd Gd a b =
      ∑ b ∈ Finset.range M,
        f₁.coeff (2 * a + 1) * f₂.coeff (2 * b + 1) * treeMono β ℓ J R B μ lam Fd Gd a b := by
    intro a _
    apply Finset.sum_subset
    · intro b hb; simp only [Finset.mem_range] at hb ⊢; omega
    · intro b _ hb
      simp only [Finset.mem_range, not_lt] at hb
      rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega : f₂.natDegree < 2 * b + 1)]
      simp
  rw [Finset.sum_congr rfl hin]
  apply Finset.sum_subset
  · intro a ha; simp only [Finset.mem_range] at ha ⊢; omega
  · intro a _ ha
    simp only [Finset.mem_range, not_lt] at ha
    apply Finset.sum_eq_zero
    intro b _
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega : f₁.natDegree < 2 * a + 1)]
    simp

private lemma tx_tree_lin_left {m n : ℕ} (β : ℝ) (ℓ J : ℕ) (R : ℝ) (B : ℕ) (μ : Fin m → ℝ)
    (lam : Fin n → ℝ) (Fd : Fin m → ℝ) (Gd : Fin n → ℝ) (f g h : Polynomial ℝ) (c : ℝ) :
    def_app_vol_tree β ℓ J R B μ lam Fd Gd (f + Polynomial.C c * g) h =
      def_app_vol_tree β ℓ J R B μ lam Fd Gd f h +
        c * def_app_vol_tree β ℓ J R B μ lam Fd Gd g h := by
  set M := f.natDegree + g.natDegree + h.natDegree + 1 with hM
  have hfg : (f + Polynomial.C c * g).natDegree < M := by
    have := Polynomial.natDegree_add_le f (Polynomial.C c * g)
    have := Polynomial.natDegree_C_mul_le c g
    omega
  rw [tx_tree_eq_range _ _ _ _ _ _ _ _ _ _ _ M hfg (by omega),
    tx_tree_eq_range _ _ _ _ _ _ _ _ _ _ _ M (by omega) (by omega),
    tx_tree_eq_range _ _ _ _ _ _ _ _ _ _ _ M (by omega) (by omega), Finset.mul_sum]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul]
  ring

private lemma tx_tree_lin_right {m n : ℕ} (β : ℝ) (ℓ J : ℕ) (R : ℝ) (B : ℕ) (μ : Fin m → ℝ)
    (lam : Fin n → ℝ) (Fd : Fin m → ℝ) (Gd : Fin n → ℝ) (f g h : Polynomial ℝ) (c : ℝ) :
    def_app_vol_tree β ℓ J R B μ lam Fd Gd h (f + Polynomial.C c * g) =
      def_app_vol_tree β ℓ J R B μ lam Fd Gd h f +
        c * def_app_vol_tree β ℓ J R B μ lam Fd Gd h g := by
  set M := f.natDegree + g.natDegree + h.natDegree + 1 with hM
  have hfg : (f + Polynomial.C c * g).natDegree < M := by
    have := Polynomial.natDegree_add_le f (Polynomial.C c * g)
    have := Polynomial.natDegree_C_mul_le c g
    omega
  rw [tx_tree_eq_range _ _ _ _ _ _ _ _ _ _ _ M (by omega) hfg,
    tx_tree_eq_range _ _ _ _ _ _ _ _ _ _ _ M (by omega) (by omega),
    tx_tree_eq_range _ _ _ _ _ _ _ _ _ _ _ M (by omega) (by omega), Finset.mul_sum]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul]
  ring

private lemma tx_tree_congr {m n : ℕ} (β : ℝ) (ℓ J : ℕ) (R : ℝ) (B : ℕ) (μ : Fin m → ℝ)
    (lam : Fin n → ℝ) (Fd : Fin m → ℝ) (Gd : Fin n → ℝ) (f₁ f₂ g₁ g₂ : Polynomial ℝ)
    (h1 : ∀ a, f₁.coeff (2 * a + 1) = g₁.coeff (2 * a + 1))
    (h2 : ∀ a, f₂.coeff (2 * a + 1) = g₂.coeff (2 * a + 1)) :
    def_app_vol_tree β ℓ J R B μ lam Fd Gd f₁ f₂ = def_app_vol_tree β ℓ J R B μ lam Fd Gd g₁ g₂ := by
  set M := f₁.natDegree + f₂.natDegree + g₁.natDegree + g₂.natDegree + 1 with hM
  rw [tx_tree_eq_range _ _ _ _ _ _ _ _ _ _ _ M (by omega) (by omega),
    tx_tree_eq_range _ _ _ _ _ _ _ _ _ _ _ M (by omega) (by omega)]
  simp only [h1, h2]


private lemma tx_eqvgen_isLeft {k : ℕ} (p : TreeMatch k × TreeMatch k) (x y : TreeVtx k)
    (h : Relation.EqvGen (treeRel p) x y) : x.isLeft = y.isLeft := by
  induction h with
  | rel x y hr =>
    obtain ⟨s, h | h | h | h⟩ := hr <;> obtain ⟨hx, hy⟩ := h <;> subst hx <;> subst hy <;> rfl
  | refl x => rfl
  | symm x y _ ih => exact ih.symm
  | trans x y z _ _ ih1 ih2 => exact ih1.trans ih2

private lemma tx_truncMoment_zero (d : ℕ) (hd : d ≠ 0) (R : ℝ) (hR : R ≤ 0) :
    treeTruncMoment d R = 0 := by
  unfold treeTruncMoment
  rw [if_neg hd]
  have : (fun x : ℝ => if |x| ≤ R then x ^ d else 0) = fun _ => 0 := by
    funext x
    split_ifs with h
    · have : x = 0 := by
        have := abs_nonneg x
        exact abs_eq_zero.mp (le_antisymm (h.trans hR) this)
      subst this; simp [hd]
    · rfl
  rw [this]; simp

open Classical in
private lemma tx_treeMono_zero {m n : ℕ} (β : ℝ) (ℓ J : ℕ) (R : ℝ) (hR : R ≤ 0) (B : ℕ)
    (μ : Fin m → ℝ) (lam : Fin n → ℝ) (Fd : Fin m → ℝ) (Gd : Fin n → ℝ) (a b : ℕ) :
    treeMono β ℓ J R B μ lam Fd Gd a b = 0 := by
  unfold treeMono
  apply Finset.sum_eq_zero
  intro p _
  split_ifs with hp
  · have hk : 0 < treeK a b := by unfold treeK; omega
    set r0 : Fin (treeK a b) := ⟨0, hk⟩ with hr0
    apply Finset.prod_eq_zero (Finset.mem_univ (treeMk p (Sum.inr r0)))
    unfold treeClassFactor
    have hno : ¬ ∃ e : Fin (treeK a b), treeMk p (Sum.inl e) = treeMk p (Sum.inr r0) := by
      rintro ⟨e, he⟩
      have h1 := tx_eqvgen_isLeft p _ _ (Quotient.exact he)
      simp at h1
    rw [if_neg hno]
    have hcard : (Finset.univ.filter fun r => treeMk p (Sum.inr r) = treeMk p (Sum.inr r0)).card ≠ 0 := by
      apply Finset.card_ne_zero_of_mem (a := r0)
      simp
    simp only [tx_truncMoment_zero _ hcard R hR, zero_mul]
  · rfl

private lemma tx_tree_zero_of_nonpos {m n : ℕ} (β : ℝ) (ℓ J : ℕ) (R : ℝ) (hR : R ≤ 0) (B : ℕ)
    (μ : Fin m → ℝ) (lam : Fin n → ℝ) (Fd : Fin m → ℝ) (Gd : Fin n → ℝ) (f₁ f₂ : Polynomial ℝ) :
    def_app_vol_tree β ℓ J R B μ lam Fd Gd f₁ f₂ = 0 := by
  unfold def_app_vol_tree
  apply Finset.sum_eq_zero; intro a _
  apply Finset.sum_eq_zero; intro b _
  rw [tx_treeMono_zero β ℓ J R hR B μ lam Fd Gd a b, mul_zero]


private lemma tx_supOn_nonneg (D : ℝ) (f : ℝ → ℝ) : 0 ≤ supOn D f :=
  Real.iSup_nonneg fun _ => abs_nonneg _

private lemma tx_supOn_le (D : ℝ) (f : ℝ → ℝ) (c : ℝ) (hc : 0 ≤ c)
    (h : ∀ x ∈ Set.Icc (-D) D, |f x| ≤ c) : supOn D f ≤ c :=
  Real.iSup_le (fun x => h x x.2) hc

private lemma tx_le_supOn (D : ℝ) (f : ℝ → ℝ) (hf : ContinuousOn f (Set.Icc (-D) D))
    (x : ℝ) (hx : x ∈ Set.Icc (-D) D) : |f x| ≤ supOn D f := by
  have hb : BddAbove (Set.range fun y : Set.Icc (-D) D => |f y|) := by
    have := (isCompact_Icc (a := -D) (b := D)).bddAbove_image hf.abs
    rwa [Set.image_eq_range] at this
  exact le_ciSup hb (⟨x, hx⟩ : Set.Icc (-D) D)

private lemma tx_poly_bound (p : Polynomial ℝ) (ρ : ℝ) (hρ : 0 ≤ ρ) (x : ℝ) (hx : |x| ≤ ρ) :
    |p.eval x| ≤ (∑ i ∈ Finset.range (p.natDegree + 1), |p.coeff i|) * (1 + ρ) ^ p.natDegree := by
  rw [Polynomial.eval_eq_sum_range, Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i hi => ?_)
  rw [abs_mul, abs_pow]
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
  have hi' : i ≤ p.natDegree := by simpa [Nat.lt_succ_iff] using hi
  calc |x| ^ i ≤ (1 + ρ) ^ i := pow_le_pow_left₀ (abs_nonneg _) (by linarith) i
    _ ≤ (1 + ρ) ^ p.natDegree := pow_le_pow_right₀ (by linarith) hi'

private lemma tx_clamp_abs (ρ : ℝ) (hρ : 0 ≤ ρ) (x : ℝ) : |max (-ρ) (min ρ x)| ≤ ρ := by
  rw [abs_le]; constructor
  · exact le_max_left _ _
  · exact max_le (by linarith) (min_le_left _ _)

private lemma tx_clamp_self (ρ : ℝ) (x : ℝ) (hx : |x| ≤ ρ) : max (-ρ) (min ρ x) = x := by
  rw [abs_le] at hx
  rw [min_eq_right hx.2, max_eq_right hx.1]

private lemma tx_clamp_neg (ρ : ℝ) (hρ : 0 ≤ ρ) (x : ℝ) : max (-ρ) (min ρ (-x)) = -max (-ρ) (min ρ x) := by
  simp only [max_def, min_def]
  split_ifs <;> linarith

private lemma tx_clamp_lip (ρ : ℝ) (x y : ℝ) :
    |max (-ρ) (min ρ x) - max (-ρ) (min ρ y)| ≤ |x - y| := by
  have h : LipschitzWith 1 (fun x : ℝ => max (-ρ) (min ρ x)) :=
    (LipschitzWith.id.const_min ρ).const_max (-ρ)
  have := h.dist_le_mul x y
  simpa [Real.dist_eq] using this


private lemma tx_poly_lip (p : Polynomial ℝ) (ρ : ℝ) :
    ∃ L : ℝ, ∀ x ∈ Set.Icc (-ρ) ρ, ∀ y ∈ Set.Icc (-ρ) ρ, |p.eval x - p.eval y| ≤ L * |x - y| := by
  have h1 : ContDiff ℝ 1 (fun x : ℝ => p.eval x) := by
    induction p using Polynomial.induction_on' with
    | add p q hp hq => simpa [Polynomial.eval_add] using hp.add hq
    | monomial n a => simp only [Polynomial.eval_monomial]; fun_prop
  have h2 := h1.locallyLipschitz.locallyLipschitzOn (s := Set.Icc (-ρ) ρ)
  obtain ⟨K, hK⟩ := h2.exists_lipschitzOnWith_of_compact isCompact_Icc
  refine ⟨K, fun x hx y hy => ?_⟩
  have := hK.dist_le_mul x hx y hy
  simpa [Real.dist_eq] using this

private lemma tx_clampPoly_isOddBddLip (p : Polynomial ℝ) (hp : ∀ x : ℝ, p.eval (-x) = -p.eval x)
    (ρ : ℝ) (hρ : 0 ≤ ρ) : IsOddBddLip (fun x => p.eval (max (-ρ) (min ρ x))) := by
  refine ⟨fun x => ?_, ?_, ?_⟩
  · simp only [tx_clamp_neg ρ hρ x, hp]
  · refine ⟨(∑ i ∈ Finset.range (p.natDegree + 1), |p.coeff i|) * (1 + ρ) ^ p.natDegree, fun x => ?_⟩
    exact tx_poly_bound p ρ hρ _ (tx_clamp_abs ρ hρ x)
  · obtain ⟨L, hL⟩ := tx_poly_lip p ρ
    refine ⟨|L|, fun x y => ?_⟩
    have hx : max (-ρ) (min ρ x) ∈ Set.Icc (-ρ) ρ := abs_le.mp (tx_clamp_abs ρ hρ x)
    have hy : max (-ρ) (min ρ y) ∈ Set.Icc (-ρ) ρ := abs_le.mp (tx_clamp_abs ρ hρ y)
    calc |p.eval (max (-ρ) (min ρ x)) - p.eval (max (-ρ) (min ρ y))|
        ≤ L * |max (-ρ) (min ρ x) - max (-ρ) (min ρ y)| := hL _ hx _ hy
      _ ≤ |L| * |max (-ρ) (min ρ x) - max (-ρ) (min ρ y)| :=
          mul_le_mul_of_nonneg_right (le_abs_self L) (abs_nonneg _)
      _ ≤ |L| * |x - y| := mul_le_mul_of_nonneg_left (tx_clamp_lip ρ x y) (abs_nonneg _)

private lemma tx_clampPoly_supNorm (p : Polynomial ℝ) (ρ : ℝ) (hρ : 0 ≤ ρ) :
    supNorm (fun x => p.eval (max (-ρ) (min ρ x))) ≤ supOn ρ (fun x => p.eval x) := by
  refine Real.iSup_le (fun x => ?_) (tx_supOn_nonneg _ _)
  exact tx_le_supOn ρ _ p.continuous.continuousOn _ (abs_le.mp (tx_clamp_abs ρ hρ x))


private lemma tx_opNorm_nonneg {p q : ℕ} (K : Mat p q) : 0 ≤ opNorm K := by
  unfold opNorm
  exact norm_nonneg _

open scoped Matrix.Norms.L2Operator in
private lemma tx_opNorm_transpose {k l : ℕ} (A : Mat k l) : opNorm Aᵀ = opNorm A := by
  rw [opNorm_eq_norm, opNorm_eq_norm, ← Matrix.conjTranspose_eq_transpose_of_trivial,
    Matrix.l2_opNorm_conjTranspose]

private lemma tx_mulVec_sq_le {m n : ℕ} (S : Matrix (Fin m) (Fin n) ℝ) (v : Fin n → ℝ) :
    ∑ i, (∑ j, S i j * v j) ^ 2 ≤ opNorm S ^ 2 * ∑ j, v j ^ 2 := by
  rw [opNorm_eq_norm]
  have h := Matrix.l2_opNorm_mulVec S (WithLp.toLp 2 v)
  have hsq := pow_le_pow_left₀ (norm_nonneg _) h 2
  rw [mul_pow, EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq] at hsq
  simpa [Matrix.mulVec, dotProduct] using hsq

private lemma tx_spectrum_dilation {m n : ℕ} (K : Mat m n) (ρ : ℝ) (hK : opNorm K ≤ ρ) :
    spectrum ℝ (Muon.Foundations.hermDilation K) ⊆ Set.Icc (-ρ) ρ := by
  intro l hl
  have hH := Muon.Foundations.hermDilation_isHermitian K
  rw [hH.spectrum_real_eq_range_eigenvalues] at hl
  obtain ⟨i, rfl⟩ := hl
  set lam := hH.eigenvalues i with hlam
  set v := hH.eigenvectorBasis i with hvdef
  have hv : (Muon.Foundations.hermDilation K) *ᵥ ⇑v = lam • ⇑v := hH.mulVec_eigenvectorBasis i
  have hnorm : ∑ k, (v k) ^ 2 = 1 := by
    have h1 : ‖v‖ = 1 := hH.eigenvectorBasis.orthonormal.1 i
    rw [← EuclideanSpace.real_norm_sq_eq, h1]; norm_num
  set e := (finSumFinEquiv : Fin m ⊕ Fin n ≃ Fin (m + n)) with he
  set x : Fin m → ℝ := fun i => v (e (Sum.inl i)) with hx
  set y : Fin n → ℝ := fun j => v (e (Sum.inr j)) with hy
  have hsum : ∑ i, x i ^ 2 + ∑ j, y j ^ 2 = 1 := by
    rw [← hnorm, ← Equiv.sum_comp e, Fintype.sum_sum_type]
  have hu : (v ∘ e) = Sum.elim x y := by
    funext s; rcases s with s | s <;> rfl
  have hmv : (Muon.Foundations.hermDilation K) *ᵥ ⇑v =
      (((Matrix.fromBlocks 0 K Kᵀ 0 : Matrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℝ)) *ᵥ (v ∘ e)) ∘ e.symm := by
    unfold Muon.Foundations.hermDilation
    rw [Matrix.reindex_apply, Matrix.submatrix_mulVec_equiv]
    rfl
  have h1 : ∀ i, (K *ᵥ y) i = lam * x i := by
    intro i
    have := congrFun hv (e (Sum.inl i))
    rw [hmv] at this
    simp only [Function.comp, Equiv.symm_apply_apply, hu, Matrix.fromBlocks_mulVec] at this
    simpa using this
  have h2 : ∀ j, (Kᵀ *ᵥ x) j = lam * y j := by
    intro j
    have := congrFun hv (e (Sum.inr j))
    rw [hmv] at this
    simp only [Function.comp, Equiv.symm_apply_apply, hu, Matrix.fromBlocks_mulVec] at this
    simpa using this
  have e1 : lam ^ 2 * ∑ i, x i ^ 2 ≤ ρ ^ 2 * ∑ j, y j ^ 2 := by
    have := tx_mulVec_sq_le K y
    have e : ∑ i, (∑ j, K i j * y j) ^ 2 = lam ^ 2 * ∑ i, x i ^ 2 := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      have := h1 i
      simp only [Matrix.mulVec, dotProduct] at this
      rw [this]; ring
    rw [e] at this
    have h0 : 0 ≤ opNorm K := tx_opNorm_nonneg K
    have : opNorm K ^ 2 ≤ ρ ^ 2 := pow_le_pow_left₀ h0 hK 2
    nlinarith [Finset.sum_nonneg (fun j (_ : j ∈ Finset.univ) => sq_nonneg (y j))]
  have e2 : lam ^ 2 * ∑ j, y j ^ 2 ≤ ρ ^ 2 * ∑ i, x i ^ 2 := by
    have := tx_mulVec_sq_le Kᵀ x
    have e : ∑ j, (∑ i, Kᵀ j i * x i) ^ 2 = lam ^ 2 * ∑ j, y j ^ 2 := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      have := h2 j
      simp only [Matrix.mulVec, dotProduct] at this
      rw [this]; ring
    rw [e, tx_opNorm_transpose] at this
    have h0 : 0 ≤ opNorm K := tx_opNorm_nonneg K
    have : opNorm K ^ 2 ≤ ρ ^ 2 := pow_le_pow_left₀ h0 hK 2
    nlinarith [Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) => sq_nonneg (x i))]
  have h3 : lam ^ 2 ≤ ρ ^ 2 := by nlinarith
  exact abs_le_of_sq_le_sq' h3 ((tx_opNorm_nonneg K).trans hK)


private lemma tx_oddSharp_congr {m n : ℕ} (f g : ℝ → ℝ) (K : Mat m n) (ρ : ℝ) (hK : opNorm K ≤ ρ)
    (h : ∀ x ∈ Set.Icc (-ρ) ρ, f x = g x) : oddSharp f K = oddSharp g K := by
  unfold oddSharp
  congr 1
  exact cfc_congr (fun x hx => h x (tx_spectrum_dilation K ρ hK hx))

private lemma tx_contraction_poly_bound {m n B : ℕ} (hB : 0 < B) (γstar : ℝ) (hγ : 0 ≤ γstar)
    (hdim : ((min m n : ℕ) : ℝ) ≤ γstar * B)
    (F : Matrix (Fin m) (Fin m) ℝ) (G : Matrix (Fin n) (Fin n) ℝ)
    (hF : opNorm F ≤ 1) (hG : opNorm G ≤ 1)
    (f₁ f₂ : Polynomial ℝ) (hf₁ : ∀ x : ℝ, f₁.eval (-x) = -f₁.eval x)
    (hf₂ : ∀ x : ℝ, f₂.eval (-x) = -f₂.eval x) (K₁ K₂ : Mat m n) (ρ₁ ρ₂ : ℝ)
    (h₁ : opNorm K₁ ≤ ρ₁) (h₂ : opNorm K₂ ≤ ρ₂) :
    |contraction B F G (fun x => f₁.eval x) (fun x => f₂.eval x) K₁ K₂| ≤
      γstar * supOn ρ₁ (fun x => f₁.eval x) * supOn ρ₂ (fun x => f₂.eval x) := by
  have hρ₁ : 0 ≤ ρ₁ := (tx_opNorm_nonneg K₁).trans h₁
  have hρ₂ : 0 ≤ ρ₂ := (tx_opNorm_nonneg K₂).trans h₂
  have e : contraction B F G (fun x => f₁.eval x) (fun x => f₂.eval x) K₁ K₂ =
      contraction B F G (fun x => f₁.eval (max (-ρ₁) (min ρ₁ x)))
        (fun x => f₂.eval (max (-ρ₂) (min ρ₂ x))) K₁ K₂ := by
    unfold contraction
    rw [tx_oddSharp_congr (fun x => f₁.eval x) (fun x => f₁.eval (max (-ρ₁) (min ρ₁ x))) K₁ ρ₁ h₁
        (fun x hx => by simp only [tx_clamp_self ρ₁ x (abs_le.mpr hx)]),
      tx_oddSharp_congr (fun x => f₂.eval x) (fun x => f₂.eval (max (-ρ₂) (min ρ₂ x))) K₂ ρ₂ h₂
        (fun x hx => by simp only [tx_clamp_self ρ₂ x (abs_le.mpr hx)])]
  rw [e]
  refine (lem_app_vol_finite_i hB γstar hdim F G hF hG _ _
    (tx_clampPoly_isOddBddLip f₁ hf₁ ρ₁ hρ₁) (tx_clampPoly_isOddBddLip f₂ hf₂ ρ₂ hρ₂) K₁ K₂).trans ?_
  have s1 := tx_clampPoly_supNorm f₁ ρ₁ hρ₁
  have s2 := tx_clampPoly_supNorm f₂ ρ₂ hρ₂
  have n1 : 0 ≤ supNorm (fun x => f₁.eval (max (-ρ₁) (min ρ₁ x))) := Real.iSup_nonneg fun _ => abs_nonneg _
  have n2 : 0 ≤ supNorm (fun x => f₂.eval (max (-ρ₂) (min ρ₂ x))) := Real.iSup_nonneg fun _ => abs_nonneg _
  calc γstar * supNorm (fun x => f₁.eval (max (-ρ₁) (min ρ₁ x))) * supNorm (fun x => f₂.eval (max (-ρ₂) (min ρ₂ x)))
      ≤ γstar * supOn ρ₁ (fun x => f₁.eval x) * supOn ρ₂ (fun x => f₂.eval x) := by
        apply mul_le_mul (mul_le_mul_of_nonneg_left s1 hγ) s2 n2
        exact mul_nonneg hγ (tx_supOn_nonneg _ _)


section TxCont
open scoped Matrix.Norms.L2Operator

private lemma tx_opNorm_continuous {p q : ℕ} : Continuous (fun A : Mat p q => opNorm A) := by
  have : (fun A : Mat p q => opNorm A) = fun A => ‖A‖ := funext opNorm_eq_norm
  rw [this]
  exact continuous_norm

end TxCont

private lemma tx_meas_cutoffZ {m n B : ℕ} (t α : ℤ) :
    Measurable (fun ω : (ℤ × Fin B) → ℝ × (Vec m × Vec n) => (cutoffZ t α ω : Mat m B)) := by
  refine measurable_pi_iff.mpr fun i => measurable_pi_iff.mpr fun a => ?_
  unfold cutoffZ
  exact ((measurable_pi_apply i).comp (measurable_fst.comp (measurable_snd.comp (measurable_pi_apply (t + 1 + α, a)))))

private lemma tx_meas_cutoffMat {m n B : ℕ} (Fp : FrozenParams m n B) (ℓ J : ℕ) (R : ℝ) (t : ℤ) (l : ℕ) :
    Measurable (fun ω : (ℤ × Fin B) → ℝ × (Vec m × Vec n) => cutoffMat Fp ℓ J R t l ω) := by
  refine measurable_pi_iff.mpr fun i => measurable_pi_iff.mpr fun j => ?_
  unfold cutoffMat
  simp only [Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul]
  refine Measurable.const_mul (Finset.measurable_sum _ fun α _ => Finset.measurable_sum _ fun a _ => ?_) _
  have hg : Measurable (fun ω : (ℤ × Fin B) → ℝ × (Vec m × Vec n) => (ω (t + 1 + α, a)).1) :=
    measurable_fst.comp (measurable_pi_apply _)
  have hs : Measurable (fun ω : (ℤ × Fin B) → ℝ × (Vec m × Vec n) =>
      (if |(ω (t + 1 + α, a)).1| ≤ R then (ω (t + 1 + α, a)).1 else 0)) :=
    Measurable.ite (measurableSet_le (hg.abs) measurable_const) hg measurable_const
  refine (hs.const_mul _).mul ?_
  simp only [Matrix.mul_apply, outer, Matrix.vecMulVec_apply]
  have hz : ∀ k, Measurable (fun ω : (ℤ × Fin B) → ℝ × (Vec m × Vec n) => (ω (t + 1 + α, a)).2.1 k) :=
    fun k => (measurable_pi_apply k).comp (measurable_fst.comp (measurable_snd.comp (measurable_pi_apply _)))
  have hw : ∀ k, Measurable (fun ω : (ℤ × Fin B) → ℝ × (Vec m × Vec n) => (ω (t + 1 + α, a)).2.2 k) :=
    fun k => (measurable_pi_apply k).comp (measurable_snd.comp (measurable_snd.comp (measurable_pi_apply _)))
  refine Finset.measurable_sum _ fun p _ => ?_
  refine Measurable.mul_const (Finset.measurable_sum _ fun q _ => ?_) _
  exact (((hz q).mul (hw p)).const_mul _)


private lemma tx_meas_opNorm_cutoffMat {m n B : ℕ} (Fp : FrozenParams m n B) (ℓ J : ℕ) (R : ℝ) (t : ℤ) (l : ℕ) :
    Measurable (fun ω : (ℤ × Fin B) → ℝ × (Vec m × Vec n) => opNorm (cutoffMat Fp ℓ J R t l ω)) :=
  tx_opNorm_continuous.measurable.comp (tx_meas_cutoffMat Fp ℓ J R t l)

private lemma tx_meas_cutoffEvent (hG : Muon.External.GaussianOpNorm) (m n B ℓ J : ℕ) (γstar : ℝ) (t : ℤ) :
    MeasurableSet (cutoffEvent hG m n B ℓ J γstar t) := by
  unfold cutoffEvent
  simp only [Set.setOf_forall]
  refine MeasurableSet.iInter fun α => MeasurableSet.iInter fun _ => ?_
  refine MeasurableSet.inter ?_ ?_
  · exact measurableSet_le (tx_opNorm_continuous.measurable.comp (tx_meas_cutoffZ t α)) measurable_const
  · have : Measurable (fun ω : (ℤ × Fin B) → ℝ × (Vec m × Vec n) => (cutoffW t α ω : Mat n B)) := by
      refine measurable_pi_iff.mpr fun i => measurable_pi_iff.mpr fun a => ?_
      unfold cutoffW
      exact ((measurable_pi_apply i).comp (measurable_snd.comp (measurable_snd.comp (measurable_pi_apply (t + 1 + α, a)))))
    exact measurableSet_le (tx_opNorm_continuous.measurable.comp this) measurable_const


private lemma tx_replMat_apply {m : ℕ} (S : Matrix (Fin m) (Fin m) ℝ) (N : ℕ) (a b : Fin (N * m)) :
    replMat S N a b = S ((replIdx m N).symm a).1 ((replIdx m N).symm b).1 *
      (if ((replIdx m N).symm a).2 = ((replIdx m N).symm b).2 then 1 else 0) := by
  simp [replMat, repKron, Matrix.one_apply]

private lemma tx_replMat_mul {m : ℕ} (A B : Matrix (Fin m) (Fin m) ℝ) (N : ℕ) :
    replMat (A * B) N = replMat A N * replMat B N := by
  unfold replMat repKron
  rw [Matrix.submatrix_mul_equiv]
  congr 1
  erw [← Matrix.mul_kronecker_mul, mul_one]
  rfl

private lemma tx_replMat_transpose {m : ℕ} (A : Matrix (Fin m) (Fin m) ℝ) (N : ℕ) :
    (replMat A N)ᵀ = replMat Aᵀ N := by
  unfold replMat repKron
  rw [Matrix.transpose_submatrix]
  congr 1
  have hT : (Matrix.kronecker A (1 : Matrix (Fin N) (Fin N) ℝ))ᵀ =
      Matrix.kronecker Aᵀ (1 : Matrix (Fin N) (Fin N) ℝ)ᵀ :=
    (Matrix.kroneckerMap_transpose _ _ _).symm
  rw [hT, Matrix.transpose_one]

private lemma tx_replMat_diagonal {m : ℕ} (d : Fin m → ℝ) (N : ℕ) :
    replMat (Matrix.diagonal d) N = Matrix.diagonal (replVec N d) := by
  ext a b
  rw [tx_replMat_apply]
  unfold replVec
  simp only [Matrix.diagonal_apply]
  by_cases h : a = b
  · subst h; simp
  · have : ¬ (((replIdx m N).symm a).1 = ((replIdx m N).symm b).1 ∧
        ((replIdx m N).symm a).2 = ((replIdx m N).symm b).2) := by
      rintro ⟨h1, h2⟩
      exact h ((replIdx m N).symm.injective (Prod.ext h1 h2))
    by_cases h1 : ((replIdx m N).symm a).1 = ((replIdx m N).symm b).1
    · have h2 : ¬ ((replIdx m N).symm a).2 = ((replIdx m N).symm b).2 := fun h2 => this ⟨h1, h2⟩
      simp [h, h2]
    · simp [h, h1]

private lemma tx_replMat_one {m : ℕ} (N : ℕ) : replMat (1 : Matrix (Fin m) (Fin m) ℝ) N = 1 := by
  unfold replMat repKron
  have h : Matrix.kronecker (1 : Matrix (Fin m) (Fin m) ℝ) (1 : Matrix (Fin N) (Fin N) ℝ) = 1 :=
    Matrix.one_kronecker_one
  rw [h, Matrix.submatrix_one_equiv]

private lemma tx_replMat_orth {m : ℕ} (S : Matrix (Fin m) (Fin m) ℝ) (hS : Sᵀ * S = 1) (N : ℕ) :
    (replMat S N)ᵀ * replMat S N = 1 := by
  rw [tx_replMat_transpose, ← tx_replMat_mul, hS, tx_replMat_one]

private lemma tx_mulVec_sq_le' {m : ℕ} (S : Matrix (Fin m) (Fin m) ℝ) (v : Fin m → ℝ) :
    ∑ i, (∑ j, S i j * v j) ^ 2 ≤ opNorm S ^ 2 * ∑ j, v j ^ 2 := by
  rw [opNorm_eq_norm]
  have h := Matrix.l2_opNorm_mulVec S (WithLp.toLp 2 v)
  have hsq := pow_le_pow_left₀ (norm_nonneg _) h 2
  rw [mul_pow, EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq] at hsq
  simpa [Matrix.mulVec, dotProduct] using hsq


private lemma tx_replMat_mulVec_sq {m N : ℕ} (S : Matrix (Fin m) (Fin m) ℝ)
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
        Finset.sum_le_sum fun k _ => tx_mulVec_sq_le' S (fun j => x (e (j, k)))
    _ = opNorm S ^ 2 * ∑ b, x b ^ 2 := by
        rw [← Finset.mul_sum, ← Equiv.sum_comp e (fun b => x b ^ 2), Fintype.sum_prod_type_right]

private lemma tx_replMat_opNorm_le {m N : ℕ} (S : Matrix (Fin m) (Fin m) ℝ) :
    opNorm (replMat S N) ≤ opNorm S := by
  have hM : 0 ≤ opNorm S := by unfold opNorm; exact norm_nonneg _
  rw [opNorm_eq_norm (replMat S N), ← Matrix.l2_opNorm_toEuclideanCLM]
  refine ContinuousLinearMap.opNorm_le_bound _ hM fun x => ?_
  have hsq := tx_replMat_mulVec_sq S (WithLp.ofLp x)
  have hK : ‖Matrix.toEuclideanCLM (n := Fin (N * m)) (𝕜 := ℝ) (replMat S N) x‖ ^ 2 =
      ∑ a, (∑ b, replMat S N a b * WithLp.ofLp x b) ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    rfl
  have hx : ‖x‖ ^ 2 = ∑ b, WithLp.ofLp x b ^ 2 := EuclideanSpace.real_norm_sq_eq x
  have h2 : ‖Matrix.toEuclideanCLM (n := Fin (N * m)) (𝕜 := ℝ) (replMat S N) x‖ ^ 2 ≤ (opNorm S * ‖x‖) ^ 2 := by
    rw [mul_pow, hK, hx]; exact hsq
  nlinarith [norm_nonneg (Matrix.toEuclideanCLM (n := Fin (N * m)) (𝕜 := ℝ) (replMat S N) x), mul_nonneg hM (norm_nonneg x)]

private lemma tx_eig_matrix {k : ℕ} (S U : Matrix (Fin k) (Fin k) ℝ) (μ : Fin k → ℝ)
    (h : ∀ i : Fin k, S *ᵥ (fun r => U r i) = μ i • (fun r => U r i)) :
    S * U = U * Matrix.diagonal μ := by
  ext r i
  have := congrFun (h i) r
  simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at this
  rw [Matrix.mul_apply, Matrix.mul_diagonal]
  rw [this]; ring

private lemma tx_eig_vec {k : ℕ} (S U : Matrix (Fin k) (Fin k) ℝ) (μ : Fin k → ℝ)
    (h : S * U = U * Matrix.diagonal μ) (i : Fin k) :
    S *ᵥ (fun r => U r i) = μ i • (fun r => U r i) := by
  funext r
  have := congrFun (congrFun h r) i
  rw [Matrix.mul_apply, Matrix.mul_diagonal] at this
  simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul]
  rw [this]; ring

private lemma tx_exists_replSpec {m n : ℕ} (C : Covariances m n) (S : SpectralData C) (N : ℕ) :
    ∃ S' : SpectralData (replCov C N), S'.uOut = replMat S.uOut N ∧ S'.vIn = replMat S.vIn N ∧
      S'.μ = replVec N S.μ ∧ S'.lam = replVec N S.lam := by
  have h1 := tx_eig_matrix C.Sout S.uOut S.μ S.eigOut
  have h2 := tx_eig_matrix C.Sin S.vIn S.lam S.eigIn
  refine ⟨⟨replMat S.uOut N, replMat S.vIn N, replVec N S.μ, replVec N S.lam,
    tx_replMat_orth _ S.huOut N, tx_replMat_orth _ S.hvIn N, ?_, ?_⟩, rfl, rfl, rfl, rfl⟩
  · intro i
    refine tx_eig_vec _ _ _ ?_ i
    change replMat C.Sout N * replMat S.uOut N = replMat S.uOut N * Matrix.diagonal (replVec N S.μ)
    rw [← tx_replMat_diagonal, ← tx_replMat_mul, ← tx_replMat_mul, h1]
  · intro i
    refine tx_eig_vec _ _ _ ?_ i
    change replMat C.Sin N * replMat S.vIn N = replMat S.vIn N * Matrix.diagonal (replVec N S.lam)
    rw [← tx_replMat_diagonal, ← tx_replMat_mul, ← tx_replMat_mul, h2]


private lemma tx_pos_of_fro {m n : ℕ} (A : Mat m n) (h : fro A = 1) : 0 < m ∧ 0 < n := by
  constructor
  · rcases Nat.eq_zero_or_pos m with h0 | h0
    · subst h0; simp [fro] at h
    · exact h0
  · rcases Nat.eq_zero_or_pos n with h0 | h0
    · subst h0; simp [fro] at h
    · exact h0

private lemma tx_repl_test {m : ℕ} (U : Matrix (Fin m) (Fin m) ℝ) (d : Fin m → ℝ) (N : ℕ) :
    replMat U N * Matrix.diagonal (replVec N d) * (replMat U N)ᵀ =
      replMat (U * Matrix.diagonal d * Uᵀ) N := by
  rw [← tx_replMat_diagonal, tx_replMat_transpose, ← tx_replMat_mul, ← tx_replMat_mul]

private lemma tx_repl_setup {m n B : ℕ} (Fp : FrozenParams m n B) (S : SpectralData Fp.C)
    (N : ℕ) (hN : 0 < N) :
    ∃ (Fp' : FrozenParams (N * m) (N * n) (N * B)) (S' : SpectralData Fp'.C),
      Fp'.β = Fp.β ∧ S'.μ = replVec N S.μ ∧ S'.lam = replVec N S.lam ∧
      (∀ (Fd : Fin m → ℝ), opNorm (S.uOut * Matrix.diagonal Fd * S.uOutᵀ) ≤ 1 →
        opNorm (S'.uOut * Matrix.diagonal (replVec N Fd) * S'.uOutᵀ) ≤ 1) ∧
      (∀ (Gd : Fin n → ℝ), opNorm (S.vIn * Matrix.diagonal Gd * S.vInᵀ) ≤ 1 →
        opNorm (S'.vIn * Matrix.diagonal (replVec N Gd) * S'.vInᵀ) ≤ 1) ∧
      (∀ γstar CSig : ℝ, SizeFin Fp.C B γstar CSig → SizeFin Fp'.C (N * B) γstar CSig) := by
  obtain ⟨hm, hn⟩ := tx_pos_of_fro Fp.A Fp.hA
  obtain ⟨S', h1, h2, h3, h4⟩ := tx_exists_replSpec Fp.C S N
  refine ⟨def_app_vol_replication Fp S N hN (def_app_vol_replication_vi Fp.C S N hm hn hN),
    S', rfl, h3, h4, ?_, ?_, ?_⟩
  · intro Fd hF
    rw [h1, tx_repl_test]
    exact (tx_replMat_opNorm_le _).trans hF
  · intro Gd hG
    rw [h2, tx_repl_test]
    exact (tx_replMat_opNorm_le _).trans hG
  · intro γstar CSig hS
    exact def_app_vol_replication_iv Fp.C γstar CSig hS N hN


private lemma tx_tree_monomial {m n : ℕ} (β : ℝ) (ℓ J : ℕ) (R : ℝ) (B : ℕ) (μ : Fin m → ℝ)
    (lam : Fin n → ℝ) (Fd : Fin m → ℝ) (Gd : Fin n → ℝ) (a b : ℕ) :
    def_app_vol_tree β ℓ J R B μ lam Fd Gd (Polynomial.X ^ (2 * a + 1)) (Polynomial.X ^ (2 * b + 1)) =
      treeMono β ℓ J R B μ lam Fd Gd a b := by
  unfold def_app_vol_tree
  rw [Polynomial.natDegree_X_pow, Polynomial.natDegree_X_pow]
  rw [Finset.sum_eq_single a, Finset.sum_eq_single b]
  · simp [Polynomial.coeff_X_pow]
  · intro b' _ hb'
    simp [Polynomial.coeff_X_pow, hb']
  · intro hb; exfalso; apply hb; simp; omega
  · intro a' _ ha'
    apply Finset.sum_eq_zero
    intro b' _
    simp [Polynomial.coeff_X_pow, ha']
  · intro ha; exfalso; apply ha; simp; omega

private lemma tx_pow_bound (ρ : ℝ) (hρ : 0 ≤ ρ) (q : ℕ) : (1 + ρ) ^ q ≤ 2 ^ q * (1 + ρ ^ (q + 1)) := by
  rcases le_total ρ 1 with h | h
  · calc (1 + ρ) ^ q ≤ 2 ^ q := pow_le_pow_left₀ (by linarith) (by linarith) q
      _ ≤ 2 ^ q * (1 + ρ ^ (q + 1)) := by
        have : 0 ≤ ρ ^ (q + 1) := pow_nonneg hρ _
        nlinarith [pow_pos (by norm_num : (0:ℝ) < 2) q]
  · calc (1 + ρ) ^ q ≤ (2 * ρ) ^ q := pow_le_pow_left₀ (by linarith) (by linarith) q
      _ = 2 ^ q * ρ ^ q := mul_pow _ _ _
      _ ≤ 2 ^ q * ρ ^ (q + 1) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact pow_le_pow_right₀ h (by omega)
      _ ≤ 2 ^ q * (1 + ρ ^ (q + 1)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity); linarith

private lemma tx_prod_bound (ρ₁ ρ₂ : ℝ) (h₁ : 0 ≤ ρ₁) (h₂ : 0 ≤ ρ₂) (d₁ d₂ : ℕ) :
    (1 + ρ₁) ^ d₁ * (1 + ρ₂) ^ d₂ ≤
      2 ^ (d₁ + d₂) * (2 + ρ₁ ^ (d₁ + d₂ + 1) + ρ₂ ^ (d₁ + d₂ + 1)) := by
  set q := d₁ + d₂ with hq
  have hx : 1 ≤ 1 + ρ₁ := by linarith
  have hy : 1 ≤ 1 + ρ₂ := by linarith
  have key : (1 + ρ₁) ^ d₁ * (1 + ρ₂) ^ d₂ ≤ (1 + ρ₁) ^ q + (1 + ρ₂) ^ q := by
    rcases le_total (1 + ρ₁) (1 + ρ₂) with h | h
    · have : (1 + ρ₁) ^ d₁ ≤ (1 + ρ₂) ^ d₁ := pow_le_pow_left₀ (by linarith) h _
      calc (1 + ρ₁) ^ d₁ * (1 + ρ₂) ^ d₂ ≤ (1 + ρ₂) ^ d₁ * (1 + ρ₂) ^ d₂ :=
            mul_le_mul_of_nonneg_right this (by positivity)
        _ = (1 + ρ₂) ^ q := by rw [← pow_add]
        _ ≤ _ := by have : 0 ≤ (1 + ρ₁) ^ q := by positivity
                    linarith
    · have : (1 + ρ₂) ^ d₂ ≤ (1 + ρ₁) ^ d₂ := pow_le_pow_left₀ (by linarith) h _
      calc (1 + ρ₁) ^ d₁ * (1 + ρ₂) ^ d₂ ≤ (1 + ρ₁) ^ d₁ * (1 + ρ₁) ^ d₂ :=
            mul_le_mul_of_nonneg_left this (by positivity)
        _ = (1 + ρ₁) ^ q := by rw [← pow_add]
        _ ≤ _ := by have : 0 ≤ (1 + ρ₂) ^ q := by positivity
                    linarith
  have b1 := tx_pow_bound ρ₁ h₁ q
  have b2 := tx_pow_bound ρ₂ h₂ q
  nlinarith

private lemma tx_supOn_poly_le (p : Polynomial ℝ) (ρ : ℝ) (hρ : 0 ≤ ρ) :
    supOn ρ (fun x => p.eval x) ≤
      (∑ i ∈ Finset.range (p.natDegree + 1), |p.coeff i|) * (1 + ρ) ^ p.natDegree :=
  tx_supOn_le ρ _ _ (by positivity) fun x hx => tx_poly_bound p ρ hρ x (abs_le.mpr hx)


private lemma tx_tail {mm nn BB : ℕ → ℕ} (cert : Muon.External.GaussianOpNorm) (γstar CSig : ℝ)
    (ℓ J : ℕ) (R : ℝ) (hR : 0 < R) (Fp : ∀ k, FrozenParams (mm k) (nn k) (BB k))
    (hB : Tendsto BB atTop atTop) (hS : ∀ k, SizeFin (Fp k).C (BB k) γstar CSig)
    (q : ℕ) (c0 : ℝ) (hc0 : 0 ≤ c0) :
    Tendsto (fun k => ∫⁻ ω in (cutoffEvent cert (mm k) (nn k) (BB k) ℓ J γstar 0)ᶜ,
        ENNReal.ofReal (c0 * (2 + opNorm (cutoffMat (Fp k) ℓ J R 0 1 ω) ^ (q + 1) +
          opNorm (cutoffMat (Fp k) ℓ J R 0 2 ω) ^ (q + 1)))
        ∂(indepSpaceLaw (mm k) (nn k) (BB k))) atTop (𝓝 0) := by
  have hp : (1 : ℝ) ≤ ((q + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_add_left 1 q
  have h1 := lem_app_vol_norm_iii cert ℓ J R γstar CSig hR mm nn BB Fp hB hS 0 1 (Or.inl rfl) _ hp
  have h2 := lem_app_vol_norm_iii cert ℓ J R γstar CSig hR mm nn BB Fp hB hS 0 2 (Or.inr rfl) _ hp
  have h3 : Tendsto (fun k => indepSpaceLaw (mm k) (nn k) (BB k)
      (cutoffEvent cert (mm k) (nn k) (BB k) ℓ J γstar 0)ᶜ) atTop (𝓝 0) := by
    have hexp : Tendsto (fun k => ENNReal.ofReal (4 * ((Finset.Icc (-(J : ℤ)) (ℓ : ℤ)).card : ℝ) *
        Real.exp (-(BB k : ℝ)))) atTop (𝓝 0) := by
      have : Tendsto (fun k => 4 * ((Finset.Icc (-(J : ℤ)) (ℓ : ℤ)).card : ℝ) *
          Real.exp (-(BB k : ℝ))) atTop (𝓝 0) := by
        have := (Real.tendsto_exp_neg_atTop_nhds_zero.comp
          (tendsto_natCast_atTop_atTop.comp hB)).const_mul (4 * ((Finset.Icc (-(J : ℤ)) (ℓ : ℤ)).card : ℝ))
        simpa using this
      simpa using ENNReal.tendsto_ofReal this
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hexp (fun k => zero_le) (fun k => ?_)
    exact lem_app_vol_norm_i cert ℓ J γstar CSig (Fp k).C (hS k) 0
  have h4 : Tendsto (fun k => ENNReal.ofReal c0 * (2 * indepSpaceLaw (mm k) (nn k) (BB k)
      (cutoffEvent cert (mm k) (nn k) (BB k) ℓ J γstar 0)ᶜ +
      ∫⁻ ω in (cutoffEvent cert (mm k) (nn k) (BB k) ℓ J γstar 0)ᶜ,
        ENNReal.ofReal (opNorm (cutoffMat (Fp k) ℓ J R 0 1 ω) ^ ((q + 1 : ℕ) : ℝ))
          ∂(indepSpaceLaw (mm k) (nn k) (BB k)) +
      ∫⁻ ω in (cutoffEvent cert (mm k) (nn k) (BB k) ℓ J γstar 0)ᶜ,
        ENNReal.ofReal (opNorm (cutoffMat (Fp k) ℓ J R 0 2 ω) ^ ((q + 1 : ℕ) : ℝ))
          ∂(indepSpaceLaw (mm k) (nn k) (BB k)))) atTop (𝓝 0) := by
    have h3' := ENNReal.Tendsto.const_mul h3 (Or.inr (by norm_num) : (0 : ℝ≥0∞) ≠ 0 ∨ (2 : ℝ≥0∞) ≠ ⊤)
    have h5 := (h3'.add h1).add h2
    have := ENNReal.Tendsto.const_mul h5 (Or.inr ENNReal.ofReal_ne_top : (2 * 0 + 0 + 0 : ℝ≥0∞) ≠ 0 ∨ ENNReal.ofReal c0 ≠ ⊤)
    simpa using this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h4 (fun k => zero_le) (fun k => ?_)
  set E := cutoffEvent cert (mm k) (nn k) (BB k) ℓ J γstar 0 with hE
  have mA : Measurable (fun ω : (ℤ × Fin (BB k)) → ℝ × (Vec (mm k) × Vec (nn k)) =>
      ENNReal.ofReal (opNorm (cutoffMat (Fp k) ℓ J R 0 1 ω) ^ (q + 1))) :=
    ((tx_meas_opNorm_cutoffMat (Fp k) ℓ J R 0 1).pow_const (q + 1)).ennreal_ofReal
  have mB : Measurable (fun ω : (ℤ × Fin (BB k)) → ℝ × (Vec (mm k) × Vec (nn k)) =>
      ENNReal.ofReal (opNorm (cutoffMat (Fp k) ℓ J R 0 2 ω) ^ (q + 1))) :=
    ((tx_meas_opNorm_cutoffMat (Fp k) ℓ J R 0 2).pow_const (q + 1)).ennreal_ofReal
  have e1 : ∀ ω : (ℤ × Fin (BB k)) → ℝ × (Vec (mm k) × Vec (nn k)),
      ENNReal.ofReal (c0 * (2 + opNorm (cutoffMat (Fp k) ℓ J R 0 1 ω) ^ (q + 1) +
          opNorm (cutoffMat (Fp k) ℓ J R 0 2 ω) ^ (q + 1))) =
        ENNReal.ofReal c0 * (2 + ENNReal.ofReal (opNorm (cutoffMat (Fp k) ℓ J R 0 1 ω) ^ (q + 1)) +
          ENNReal.ofReal (opNorm (cutoffMat (Fp k) ℓ J R 0 2 ω) ^ (q + 1))) := by
    intro ω
    have hA : 0 ≤ opNorm (cutoffMat (Fp k) ℓ J R 0 1 ω) ^ (q + 1) := pow_nonneg (tx_opNorm_nonneg _) _
    have hB' : 0 ≤ opNorm (cutoffMat (Fp k) ℓ J R 0 2 ω) ^ (q + 1) := pow_nonneg (tx_opNorm_nonneg _) _
    rw [ENNReal.ofReal_mul hc0, ENNReal.ofReal_add (by linarith) hB', ENNReal.ofReal_add (by norm_num) hA]
    simp
  simp only [e1]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  rw [lintegral_add_right _ mB, lintegral_add_right _ mA, lintegral_const, Measure.restrict_apply_univ]
  simp only [← Real.rpow_natCast]
  exact le_of_eq rfl


private lemma tx_moment (γstar CSig : ℝ) (ℓ J : ℕ) (R : ℝ) (hR : 0 < R)
    (f₁ f₂ : Polynomial ℝ) (hf₁ : ∀ x : ℝ, f₁.eval (-x) = -f₁.eval x)
    (hf₂ : ∀ x : ℝ, f₂.eval (-x) = -f₂.eval x) :
    ∃ A : ℝ, ∀ (m n B : ℕ) (Fp : FrozenParams m n B) (S : SpectralData Fp.C)
      (Fd : Fin m → ℝ) (Gd : Fin n → ℝ) (Fm : Mat m m) (Gm : Mat n n),
      SizeFin Fp.C B γstar CSig →
      Fm = S.uOut * Matrix.diagonal Fd * S.uOutᵀ →
      Gm = S.vIn * Matrix.diagonal Gd * S.vInᵀ →
      opNorm Fm ≤ 1 → opNorm Gm ≤ 1 →
      Integrable (fun ω : (ℤ × Fin B) → ℝ × (Vec m × Vec n) =>
        contraction B Fm Gm (fun x => f₁.eval x) (fun x => f₂.eval x)
          (cutoffMat Fp ℓ J R 0 1 ω) (cutoffMat Fp ℓ J R 0 2 ω)) (indepSpaceLaw m n B) ∧
      |(∫ ω, contraction B Fm Gm (fun x => f₁.eval x) (fun x => f₂.eval x)
          (cutoffMat Fp ℓ J R 0 1 ω) (cutoffMat Fp ℓ J R 0 2 ω) ∂(indepSpaceLaw m n B)) -
        def_app_vol_tree Fp.β ℓ J R B S.μ S.lam Fd Gd f₁ f₂| ≤ A / (B : ℝ) := by
  choose CW hCW using fun a b : ℕ => lem_app_vol_tree_closure a b ℓ J R γstar CSig hR
  refine ⟨∑ a ∈ Finset.range (f₁.natDegree + 1), ∑ b ∈ Finset.range (f₂.natDegree + 1),
    |f₁.coeff (2 * a + 1)| * |f₂.coeff (2 * b + 1)| * CW a b, ?_⟩
  intro m n B Fp S Fd Gd Fm Gm hS hFm hGm hF hG
  have hcl := fun a b => hCW a b m n B Fp S 0 Fd Gd Fm Gm hS hFm hGm hF hG
  have hexp : ∀ ω : (ℤ × Fin B) → ℝ × (Vec m × Vec n),
      contraction B Fm Gm (fun x => f₁.eval x) (fun x => f₂.eval x)
          (cutoffMat Fp ℓ J R 0 1 ω) (cutoffMat Fp ℓ J R 0 2 ω) =
        ∑ a ∈ Finset.range (f₁.natDegree + 1), ∑ b ∈ Finset.range (f₂.natDegree + 1),
          f₁.coeff (2 * a + 1) * f₂.coeff (2 * b + 1) *
            ((B : ℝ)⁻¹ * Matrix.trace (treeWord Fm Gm (cutoffMat Fp ℓ J R 0 1 ω)
              (cutoffMat Fp ℓ J R 0 2 ω) a b)) := by
    intro ω
    unfold contraction
    exact def_app_vol_tree_word_expansion Fm Gm _ _ f₁ f₂ (tx_odd_coeff f₁ hf₁) (tx_odd_coeff f₂ hf₂)
  have hint : Integrable (fun ω : (ℤ × Fin B) → ℝ × (Vec m × Vec n) =>
        contraction B Fm Gm (fun x => f₁.eval x) (fun x => f₂.eval x)
          (cutoffMat Fp ℓ J R 0 1 ω) (cutoffMat Fp ℓ J R 0 2 ω)) (indepSpaceLaw m n B) := by
    simp only [hexp]
    refine integrable_finsetSum _ fun a _ => integrable_finsetSum _ fun b _ => ?_
    exact (hcl a b).1.const_mul _
  refine ⟨hint, ?_⟩
  simp only [hexp]
  rw [integral_finsetSum _ (fun a _ => integrable_finsetSum _ fun b _ => (hcl a b).1.const_mul _)]
  simp only [integral_finsetSum _ (fun b _ => ((hcl _ b).1.const_mul _)), integral_const_mul]
  unfold def_app_vol_tree
  rw [← Finset.sum_sub_distrib, div_eq_mul_inv, Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun a _ => ?_)
  rw [← Finset.sum_sub_distrib, Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun b _ => ?_)
  have h1 := (hcl a b).2
  rw [tx_tree_monomial] at h1
  simp only [integral_const_mul] at h1
  rw [← mul_sub, abs_mul, abs_mul]
  calc |f₁.coeff (2 * a + 1)| * |f₂.coeff (2 * b + 1)| * _ ≤ |f₁.coeff (2 * a + 1)| * |f₂.coeff (2 * b + 1)| * (CW a b / (B : ℝ)) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = _ := by ring


private lemma tx_split {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Φ : Ω → ℝ) (hΦ : Integrable Φ μ) (E : Set Ω) (hE : MeasurableSet E) (c : ℝ) (hc : 0 ≤ c)
    (hin : ∀ x ∈ E, |Φ x| ≤ c) (G : Ω → ℝ≥0∞) (hG : ∀ x, ENNReal.ofReal |Φ x| ≤ G x) (ε : ℝ)
    (hε : 0 < ε) (hlt : ∫⁻ x in Eᶜ, G x ∂μ < ENNReal.ofReal ε) : |∫ x, Φ x ∂μ| ≤ c + ε := by
  rw [← integral_add_compl hE hΦ]
  have h1 : ‖∫ x in E, Φ x ∂μ‖ ≤ c := by
    have := norm_setIntegral_le_of_norm_le_const (μ := μ) (s := E) (f := Φ) (C := c)
      (measure_lt_top μ E) (fun x hx => by simpa using hin x hx)
    refine this.trans ?_
    have : μ.real E ≤ 1 := by
      simpa [Measure.real] using (ENNReal.toReal_mono ENNReal.one_ne_top (prob_le_one (μ := μ) (s := E)))
    nlinarith
  have h2 : ‖∫ x in Eᶜ, Φ x ∂μ‖ ≤ ε := by
    refine (norm_integral_le_integral_norm _).trans ?_
    rw [integral_norm_eq_lintegral_enorm (hΦ.restrict.aestronglyMeasurable)]
    have hne : ∫⁻ x in Eᶜ, G x ∂μ ≠ ⊤ := ne_top_of_lt hlt
    have hle : ∫⁻ x in Eᶜ, ‖Φ x‖ₑ ∂μ ≤ ∫⁻ x in Eᶜ, G x ∂μ :=
      lintegral_mono fun x => by rw [← ofReal_norm]; simpa using hG x
    exact ((ENNReal.toReal_mono hne hle).trans (ENNReal.toReal_lt_of_lt_ofReal hlt).le)
  calc |∫ x in E, Φ x ∂μ + ∫ x in Eᶜ, Φ x ∂μ| ≤ |∫ x in E, Φ x ∂μ| + |∫ x in Eᶜ, Φ x ∂μ| := abs_add_le _ _
    _ ≤ c + ε := by simpa using add_le_add h1 h2


private lemma tx_main_pos (cert : Muon.External.GaussianOpNorm) (γstar CSig : ℝ)
    {m n B : ℕ} (Fp : FrozenParams m n B) (S : SpectralData Fp.C) (hS : SizeFin Fp.C B γstar CSig)
    (ℓ J : ℕ) (R : ℝ) (hR : 0 < R) (Fd : Fin m → ℝ) (Gd : Fin n → ℝ)
    (hF : opNorm (S.uOut * Matrix.diagonal Fd * S.uOutᵀ) ≤ 1)
    (hG : opNorm (S.vIn * Matrix.diagonal Gd * S.vInᵀ) ≤ 1)
    (D : ℝ) (hD : volDR cert R CSig γstar ≤ D)
    (f₁ f₂ : Polynomial ℝ) (hf₁ : ∀ x : ℝ, f₁.eval (-x) = -f₁.eval x)
    (hf₂ : ∀ x : ℝ, f₂.eval (-x) = -f₂.eval x) :
    |def_app_vol_tree Fp.β ℓ J R B S.μ S.lam Fd Gd f₁ f₂| ≤
      γstar * supOn D (fun x => f₁.eval x) * supOn D (fun x => f₂.eval x) := by
  obtain ⟨A, hA⟩ := tx_moment γstar CSig ℓ J R hR f₁ f₂ hf₁ hf₂
  choose Fp' S' hβ hμ hlam hFk hGk hSz using fun k : ℕ => tx_repl_setup Fp S (k + 1) (Nat.succ_pos k)
  have hBpos : 0 < B := Fp.hB
  obtain ⟨hm, hn⟩ := tx_pos_of_fro Fp.A Fp.hA
  have hγ : 0 ≤ γstar := by
    have h1 := hS.1
    have h2 : (1 : ℝ) ≤ ((max m n : ℕ) : ℝ) := by exact_mod_cast le_max_of_le_left hm
    have h3 : (0 : ℝ) < B := by exact_mod_cast hBpos
    by_contra h
    push Not at h
    nlinarith
  set d₁ := f₁.natDegree with hd₁
  set d₂ := f₂.natDegree with hd₂
  set C₁ := ∑ i ∈ Finset.range (d₁ + 1), |f₁.coeff i| with hC₁
  set C₂ := ∑ i ∈ Finset.range (d₂ + 1), |f₂.coeff i| with hC₂
  have hC₁0 : 0 ≤ C₁ := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hC₂0 : 0 ≤ C₂ := Finset.sum_nonneg fun _ _ => abs_nonneg _
  set c0 := γstar * C₁ * C₂ * 2 ^ (d₁ + d₂) with hc0def
  have hc0 : 0 ≤ c0 := by positivity
  set S₁ := supOn D (fun x => f₁.eval x) with hS₁
  set S₂ := supOn D (fun x => f₂.eval x) with hS₂
  have hS₁0 : 0 ≤ S₁ := tx_supOn_nonneg _ _
  have hS₂0 : 0 ≤ S₂ := tx_supOn_nonneg _ _
  set BB : ℕ → ℕ := fun k => (k + 1) * B with hBB
  have hBBtop : Tendsto BB atTop atTop := by
    refine tendsto_atTop_mono (fun k => ?_) tendsto_id
    show k ≤ (k + 1) * B
    nlinarith [Nat.succ_le_of_lt hBpos]
  have hSz' : ∀ k, SizeFin (Fp' k).C (BB k) γstar CSig := fun k => (hSz k) γstar CSig hS
  -- the tail
  have htail := tx_tail (mm := fun k => (k + 1) * m) (nn := fun k => (k + 1) * n) (BB := BB) cert γstar CSig
    ℓ J R hR Fp' hBBtop hSz' (d₁ + d₂) c0 hc0
  have hmom := fun k : ℕ => hA ((k + 1) * m) ((k + 1) * n) (BB k) (Fp' k) (S' k)
    (replVec (k + 1) Fd) (replVec (k + 1) Gd)
    ((S' k).uOut * Matrix.diagonal (replVec (k + 1) Fd) * (S' k).uOutᵀ)
    ((S' k).vIn * Matrix.diagonal (replVec (k + 1) Gd) * (S' k).vInᵀ) (hSz' k) rfl rfl
    (hFk k Fd hF) (hGk k Gd hG)
  have htree : ∀ k : ℕ, def_app_vol_tree (Fp' k).β ℓ J R (BB k) (S' k).μ (S' k).lam
      (replVec (k + 1) Fd) (replVec (k + 1) Gd) f₁ f₂ =
      def_app_vol_tree Fp.β ℓ J R B S.μ S.lam Fd Gd f₁ f₂ := by
    intro k
    rw [hβ k, hμ k, hlam k]
    exact def_app_vol_tree_replication Fp.β ℓ J R B S.μ S.lam Fd Gd (k + 1) (Nat.succ_le_succ (Nat.zero_le k)) f₁ f₂
  -- global pointwise bound
  have hpt : ∀ (k : ℕ) (ω : (ℤ × Fin (BB k)) → ℝ × (Vec ((k + 1) * m) × Vec ((k + 1) * n))),
      |contraction (BB k) ((S' k).uOut * Matrix.diagonal (replVec (k + 1) Fd) * (S' k).uOutᵀ)
        ((S' k).vIn * Matrix.diagonal (replVec (k + 1) Gd) * (S' k).vInᵀ)
        (fun x => f₁.eval x) (fun x => f₂.eval x)
        (cutoffMat (Fp' k) ℓ J R 0 1 ω) (cutoffMat (Fp' k) ℓ J R 0 2 ω)| ≤
      c0 * (2 + opNorm (cutoffMat (Fp' k) ℓ J R 0 1 ω) ^ (d₁ + d₂ + 1) +
        opNorm (cutoffMat (Fp' k) ℓ J R 0 2 ω) ^ (d₁ + d₂ + 1)) := by
    intro k ω
    have hdim : (((min ((k + 1) * m) ((k + 1) * n) : ℕ)) : ℝ) ≤ γstar * (BB k : ℝ) :=
      le_trans (by exact_mod_cast min_le_max) (hSz' k).1
    have h1 := tx_contraction_poly_bound (Fp' k).hB γstar hγ hdim _ _ (hFk k Fd hF) (hGk k Gd hG)
      f₁ f₂ hf₁ hf₂ (cutoffMat (Fp' k) ℓ J R 0 1 ω) (cutoffMat (Fp' k) ℓ J R 0 2 ω) _ _ le_rfl le_rfl
    refine h1.trans ?_
    set ρ₁ := opNorm (cutoffMat (Fp' k) ℓ J R 0 1 ω)
    set ρ₂ := opNorm (cutoffMat (Fp' k) ℓ J R 0 2 ω)
    have hρ₁ : 0 ≤ ρ₁ := tx_opNorm_nonneg _
    have hρ₂ : 0 ≤ ρ₂ := tx_opNorm_nonneg _
    have b1 := tx_supOn_poly_le f₁ ρ₁ hρ₁
    have b2 := tx_supOn_poly_le f₂ ρ₂ hρ₂
    have b3 := tx_prod_bound ρ₁ ρ₂ hρ₁ hρ₂ d₁ d₂
    calc γstar * supOn ρ₁ (fun x => f₁.eval x) * supOn ρ₂ (fun x => f₂.eval x)
        ≤ γstar * (C₁ * (1 + ρ₁) ^ d₁) * (C₂ * (1 + ρ₂) ^ d₂) := by
          apply mul_le_mul (mul_le_mul_of_nonneg_left b1 hγ) b2 (tx_supOn_nonneg _ _)
          exact mul_nonneg hγ (mul_nonneg hC₁0 (by positivity))
      _ = γstar * C₁ * C₂ * ((1 + ρ₁) ^ d₁ * (1 + ρ₂) ^ d₂) := by ring
      _ ≤ γstar * C₁ * C₂ * (2 ^ (d₁ + d₂) * (2 + ρ₁ ^ (d₁ + d₂ + 1) + ρ₂ ^ (d₁ + d₂ + 1))) :=
          mul_le_mul_of_nonneg_left b3 (by positivity)
      _ = _ := by rw [hc0def]; ring
  -- bound on the event
  have hin : ∀ (k : ℕ) (ω : (ℤ × Fin (BB k)) → ℝ × (Vec ((k + 1) * m) × Vec ((k + 1) * n))),
      ω ∈ cutoffEvent cert ((k + 1) * m) ((k + 1) * n) (BB k) ℓ J γstar 0 →
      |contraction (BB k) ((S' k).uOut * Matrix.diagonal (replVec (k + 1) Fd) * (S' k).uOutᵀ)
        ((S' k).vIn * Matrix.diagonal (replVec (k + 1) Gd) * (S' k).vInᵀ)
        (fun x => f₁.eval x) (fun x => f₂.eval x)
        (cutoffMat (Fp' k) ℓ J R 0 1 ω) (cutoffMat (Fp' k) ℓ J R 0 2 ω)| ≤ γstar * S₁ * S₂ := by
    intro k ω hω
    have hdim : (((min ((k + 1) * m) ((k + 1) * n) : ℕ)) : ℝ) ≤ γstar * (BB k : ℝ) :=
      le_trans (by exact_mod_cast min_le_max) (hSz' k).1
    obtain ⟨n1, n2⟩ := lem_app_vol_norm_ii cert (Fp' k) ℓ J R γstar CSig hR (hSz' k) 0 ω hω
    exact tx_contraction_poly_bound (Fp' k).hB γstar hγ hdim _ _ (hFk k Fd hF) (hGk k Gd hG)
      f₁ f₂ hf₁ hf₂ _ _ D D (n1.trans hD) (n2.trans hD)
  refine le_of_forall_pos_le_add fun ε hε => ?_
  have ev1 := (tendsto_order.1 htail).2 (ENNReal.ofReal (ε / 2)) (ENNReal.ofReal_pos.mpr (by positivity))
  have ev2 : ∀ᶠ k : ℕ in atTop, A / (BB k : ℝ) < ε / 2 := by
    have : Tendsto (fun k : ℕ => A / (BB k : ℝ)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.comp hBBtop)
    exact (tendsto_order.1 this).2 _ (by positivity)
  obtain ⟨k, hk1, hk2⟩ := (ev1.and ev2).exists
  obtain ⟨hint, hbd⟩ := hmom k
  rw [htree k] at hbd
  haveI : IsProbabilityMeasure (indepSpaceLaw ((k + 1) * m) ((k + 1) * n) (BB k)) := by
    unfold indepSpaceLaw
    infer_instance
  have hsp := tx_split (indepSpaceLaw ((k + 1) * m) ((k + 1) * n) (BB k)) _ hint
    (cutoffEvent cert ((k + 1) * m) ((k + 1) * n) (BB k) ℓ J γstar 0)
    (tx_meas_cutoffEvent cert _ _ _ ℓ J γstar 0) (γstar * S₁ * S₂)
    (mul_nonneg (mul_nonneg hγ hS₁0) hS₂0) (hin k)
    (fun ω => ENNReal.ofReal (c0 * (2 + opNorm (cutoffMat (Fp' k) ℓ J R 0 1 ω) ^ (d₁ + d₂ + 1) +
        opNorm (cutoffMat (Fp' k) ℓ J R 0 2 ω) ^ (d₁ + d₂ + 1))))
    (fun ω => ENNReal.ofReal_le_ofReal (hpt k ω)) (ε / 2) (by positivity) hk1
  have := abs_sub_abs_le_abs_sub (def_app_vol_tree Fp.β ℓ J R B S.μ S.lam Fd Gd f₁ f₂)
    (∫ ω, contraction (BB k) ((S' k).uOut * Matrix.diagonal (replVec (k + 1) Fd) * (S' k).uOutᵀ)
        ((S' k).vIn * Matrix.diagonal (replVec (k + 1) Gd) * (S' k).vInᵀ)
        (fun x => f₁.eval x) (fun x => f₂.eval x)
        (cutoffMat (Fp' k) ℓ J R 0 1 ω) (cutoffMat (Fp' k) ℓ J R 0 2 ω) ∂(indepSpaceLaw ((k + 1) * m) ((k + 1) * n) (BB k)))
  rw [abs_sub_comm] at this
  have hk2' : A / (((k + 1) * B : ℕ) : ℝ) < ε / 2 := hk2
  linarith


private lemma tx_gamma_nonneg {m n B : ℕ} (Fp : FrozenParams m n B) (γstar CSig : ℝ)
    (hS : SizeFin Fp.C B γstar CSig) : 0 ≤ γstar := by
  obtain ⟨hm, hn⟩ := tx_pos_of_fro Fp.A Fp.hA
  have h1 := hS.1
  have h2 : (1 : ℝ) ≤ ((max m n : ℕ) : ℝ) := by exact_mod_cast le_max_of_le_left hm
  have h3 : (0 : ℝ) < B := by exact_mod_cast Fp.hB
  by_contra h
  push Not at h
  nlinarith

private lemma tx_bound (cert : Muon.External.GaussianOpNorm) (γstar CSig : ℝ)
    {m n B : ℕ} (Fp : FrozenParams m n B) (S : SpectralData Fp.C) (hS : SizeFin Fp.C B γstar CSig)
    (ℓ J : ℕ) (R : ℝ) (Fd : Fin m → ℝ) (Gd : Fin n → ℝ)
    (hF : opNorm (S.uOut * Matrix.diagonal Fd * S.uOutᵀ) ≤ 1)
    (hG : opNorm (S.vIn * Matrix.diagonal Gd * S.vInᵀ) ≤ 1)
    (D : ℝ) (hD : volDR cert R CSig γstar ≤ D)
    (f₁ f₂ : Polynomial ℝ) (hf₁ : ∀ x : ℝ, f₁.eval (-x) = -f₁.eval x)
    (hf₂ : ∀ x : ℝ, f₂.eval (-x) = -f₂.eval x) :
    |def_app_vol_tree Fp.β ℓ J R B S.μ S.lam Fd Gd f₁ f₂| ≤
      γstar * supOn D (fun x => f₁.eval x) * supOn D (fun x => f₂.eval x) := by
  by_cases hR : 0 < R
  · exact tx_main_pos cert γstar CSig Fp S hS ℓ J R hR Fd Gd hF hG D hD f₁ f₂ hf₁ hf₂
  · rw [tx_tree_zero_of_nonpos _ _ _ R (not_lt.mp hR), abs_zero]
    exact mul_nonneg (mul_nonneg (tx_gamma_nonneg Fp γstar CSig hS) (tx_supOn_nonneg _ _))
      (tx_supOn_nonneg _ _)


private lemma tx_abs_diff (T : Polynomial ℝ → Polynomial ℝ → ℝ) (κ D : ℝ)
    (hL : ∀ P P' Q (c : ℝ), T (P + Polynomial.C c * P') Q = T P Q + c * T P' Q)
    (hR : ∀ P Q Q' (c : ℝ), T P (Q + Polynomial.C c * Q') = T P Q + c * T P Q')
    (hB : ∀ P Q, |T P Q| ≤ κ * supOn D (fun x => P.eval x) * supOn D (fun x => Q.eval x))
    (P P' Q Q' : Polynomial ℝ) :
    |T P Q - T P' Q'| ≤ κ * (supOn D (fun x => (P + Polynomial.C (-1) * P').eval x) *
        supOn D (fun x => Q.eval x) +
      supOn D (fun x => P'.eval x) * supOn D (fun x => (Q + Polynomial.C (-1) * Q').eval x)) := by
  have e : T P Q - T P' Q' = T (P + Polynomial.C (-1) * P') Q + T P' (Q + Polynomial.C (-1) * Q') := by
    rw [hL, hR]; ring
  rw [e]
  refine (abs_add_le _ _).trans ?_
  have h1 := hB (P + Polynomial.C (-1) * P') Q
  have h2 := hB P' (Q + Polynomial.C (-1) * Q')
  nlinarith

private lemma tx_sup_diff (D : ℝ) (P P' : Polynomial ℝ) (δ : ℝ) (hδ : 0 ≤ δ)
    (h : ∀ x ∈ Set.Icc (-D) D, |P.eval x - P'.eval x| ≤ δ) :
    supOn D (fun x => (P + Polynomial.C (-1) * P').eval x) ≤ δ :=
  tx_supOn_le D _ δ hδ fun x hx => by simpa [sub_eq_add_neg] using h x hx

private lemma tx_sup_near (D : ℝ) (P : Polynomial ℝ) (f : ℝ → ℝ) (hf : ContinuousOn f (Set.Icc (-D) D))
    (δ : ℝ) (hδ : 0 ≤ δ) (h : ∀ x ∈ Set.Icc (-D) D, |P.eval x - f x| ≤ δ) :
    supOn D (fun x => P.eval x) ≤ supOn D f + δ := by
  refine tx_supOn_le D _ _ (add_nonneg (tx_supOn_nonneg _ _) hδ) fun x hx => ?_
  have h1 := h x hx
  have h2 := tx_le_supOn D f hf x hx
  have : |P.eval x| ≤ |f x| + |P.eval x - f x| := by
    calc |P.eval x| = |f x + (P.eval x - f x)| := by ring_nf
      _ ≤ _ := abs_add_le _ _
  linarith

private lemma tx_cauchy (T : Polynomial ℝ → Polynomial ℝ → ℝ) (κ D : ℝ) (hκ : 0 ≤ κ)
    (hL : ∀ P P' Q (c : ℝ), T (P + Polynomial.C c * P') Q = T P Q + c * T P' Q)
    (hR : ∀ P Q Q' (c : ℝ), T P (Q + Polynomial.C c * Q') = T P Q + c * T P Q')
    (hB : ∀ P Q, |T P Q| ≤ κ * supOn D (fun x => P.eval x) * supOn D (fun x => Q.eval x))
    (f g : ℝ → ℝ) (hf : ContinuousOn f (Set.Icc (-D) D)) (hg : ContinuousOn g (Set.Icc (-D) D))
    (P Q : ℕ → Polynomial ℝ)
    (hP : ∀ k, ∀ x ∈ Set.Icc (-D) D, |(P k).eval x - f x| ≤ 1 / ((k : ℝ) + 1))
    (hQ : ∀ k, ∀ x ∈ Set.Icc (-D) D, |(Q k).eval x - g x| ≤ 1 / ((k : ℝ) + 1)) :
    ∃ L, Tendsto (fun k => T (P k) (Q k)) atTop (𝓝 L) := by
  apply cauchySeq_tendsto_of_complete
  set M := supOn D f + supOn D g + 2 with hM
  have hM0 : 0 ≤ M := by
    have := tx_supOn_nonneg D f; have := tx_supOn_nonneg D g; rw [hM]; linarith
  have hd : ∀ k : ℕ, 0 ≤ 1 / ((k : ℝ) + 1) := fun k => by positivity
  have hd1 : ∀ k : ℕ, 1 / ((k : ℝ) + 1) ≤ 1 := fun k => by
    rw [div_le_one (by positivity)]; linarith [(Nat.cast_nonneg k : (0:ℝ) ≤ k)]
  have sP : ∀ k, supOn D (fun x => (P k).eval x) ≤ supOn D f + 1 := fun k =>
    (tx_sup_near D _ f hf _ (hd k) (hP k)).trans (by linarith [hd1 k])
  have sQ : ∀ k, supOn D (fun x => (Q k).eval x) ≤ supOn D g + 1 := fun k =>
    (tx_sup_near D _ g hg _ (hd k) (hQ k)).trans (by linarith [hd1 k])
  refine cauchySeq_of_le_tendsto_0 (fun N => 2 * κ * M * (1 / ((N : ℝ) + 1))) (fun n m N hn hm => ?_) ?_
  · rw [Real.dist_eq]
    have hdn : 1 / ((n : ℝ) + 1) ≤ 1 / ((N : ℝ) + 1) :=
      one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hn 1)
    have hdm : 1 / ((m : ℝ) + 1) ≤ 1 / ((N : ℝ) + 1) :=
      one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hm 1)
    refine (tx_abs_diff T κ D hL hR hB (P n) (P m) (Q n) (Q m)).trans ?_
    have s1 := tx_sup_diff D (P n) (P m) (1 / ((n : ℝ) + 1) + 1 / ((m : ℝ) + 1)) (add_nonneg (hd n) (hd m))
      (fun x hx => by
        have a := hP n x hx; have b := hP m x hx
        calc |(P n).eval x - (P m).eval x| = |((P n).eval x - f x) - ((P m).eval x - f x)| := by ring_nf
          _ ≤ |(P n).eval x - f x| + |(P m).eval x - f x| := abs_sub _ _
          _ ≤ _ := add_le_add a b)
    have s2 := tx_sup_diff D (Q n) (Q m) (1 / ((n : ℝ) + 1) + 1 / ((m : ℝ) + 1)) (add_nonneg (hd n) (hd m))
      (fun x hx => by
        have a := hQ n x hx; have b := hQ m x hx
        calc |(Q n).eval x - (Q m).eval x| = |((Q n).eval x - g x) - ((Q m).eval x - g x)| := by ring_nf
          _ ≤ |(Q n).eval x - g x| + |(Q m).eval x - g x| := abs_sub _ _
          _ ≤ _ := add_le_add a b)
    have a0 := tx_supOn_nonneg D (fun x => (Q n).eval x)
    have a1 := tx_supOn_nonneg D (fun x => (P m).eval x)
    have a2 := tx_supOn_nonneg D f
    have a3 := tx_supOn_nonneg D g
    have e1 : supOn D (fun x => (P n + Polynomial.C (-1) * P m).eval x) * supOn D (fun x => (Q n).eval x) ≤
        (2 * (1 / ((N : ℝ) + 1))) * (supOn D g + 1) :=
      mul_le_mul (s1.trans (by linarith)) (sQ n) a0 (by positivity)
    have e2 : supOn D (fun x => (P m).eval x) * supOn D (fun x => (Q n + Polynomial.C (-1) * Q m).eval x) ≤
        (supOn D f + 1) * (2 * (1 / ((N : ℝ) + 1))) :=
      mul_le_mul (sP m) (s2.trans (by linarith)) (tx_supOn_nonneg _ _) (by linarith)
    have : κ * (supOn D (fun x => (P n + Polynomial.C (-1) * P m).eval x) * supOn D (fun x => (Q n).eval x) +
        supOn D (fun x => (P m).eval x) * supOn D (fun x => (Q n + Polynomial.C (-1) * Q m).eval x)) ≤
        κ * ((2 * (1 / ((N : ℝ) + 1))) * (supOn D g + 1) + (supOn D f + 1) * (2 * (1 / ((N : ℝ) + 1)))) :=
      mul_le_mul_of_nonneg_left (add_le_add e1 e2) hκ
    refine this.trans (le_of_eq ?_)
    rw [hM]; ring
  · have : Tendsto (fun N : ℕ => 1 / ((N : ℝ) + 1)) atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
    simpa using this.const_mul (2 * κ * M)


private lemma tx_close (T : Polynomial ℝ → Polynomial ℝ → ℝ) (κ D : ℝ) (hκ : 0 ≤ κ)
    (hL : ∀ P P' Q (c : ℝ), T (P + Polynomial.C c * P') Q = T P Q + c * T P' Q)
    (hR : ∀ P Q Q' (c : ℝ), T P (Q + Polynomial.C c * Q') = T P Q + c * T P Q')
    (hB : ∀ P Q, |T P Q| ≤ κ * supOn D (fun x => P.eval x) * supOn D (fun x => Q.eval x))
    (P Q P' Q' : ℕ → Polynomial ℝ) (a : ℕ → ℝ) (ha0 : ∀ k, 0 ≤ a k) (ha : Tendsto a atTop (𝓝 0))
    (M : ℝ) (hPP : ∀ k, supOn D (fun x => (P k + Polynomial.C (-1) * P' k).eval x) ≤ a k)
    (hQQ : ∀ k, supOn D (fun x => (Q k + Polynomial.C (-1) * Q' k).eval x) ≤ a k)
    (hQM : ∀ k, supOn D (fun x => (Q k).eval x) ≤ M) (hPM : ∀ k, supOn D (fun x => (P' k).eval x) ≤ M) :
    Tendsto (fun k => T (P k) (Q k) - T (P' k) (Q' k)) atTop (𝓝 0) := by
  have hM : 0 ≤ M := (tx_supOn_nonneg _ _).trans (hQM 0)
  have hlim : Tendsto (fun k => κ * (a k * M + M * a k)) atTop (𝓝 0) := by
    have := ((ha.mul_const M).add (ha.const_mul M)).const_mul κ
    simpa using this
  refine squeeze_zero_norm (fun k => ?_) hlim
  rw [Real.norm_eq_abs]
  refine (tx_abs_diff T κ D hL hR hB _ _ _ _).trans ?_
  apply mul_le_mul_of_nonneg_left _ hκ
  apply add_le_add
  · exact mul_le_mul (hPP k) (hQM k) (tx_supOn_nonneg _ _) (ha0 k)
  · exact mul_le_mul (hPM k) (hQQ k) (tx_supOn_nonneg _ _) hM

section TxOrth
open scoped Matrix.Norms.L2Operator

private lemma tx_norm_left_orth {a b : ℕ} (U : Matrix (Fin a) (Fin a) ℝ) (hU : Uᵀ * U = 1)
    (X : Matrix (Fin a) (Fin b) ℝ) : ‖U * X‖ = ‖X‖ := by
  have hUh : Uᴴ * U = 1 := by rw [Matrix.conjTranspose_eq_transpose_of_trivial]; exact hU
  have h : ‖U * X‖ * ‖U * X‖ = ‖X‖ * ‖X‖ := by
    rw [← Matrix.l2_opNorm_conjTranspose_mul_self, ← Matrix.l2_opNorm_conjTranspose_mul_self]
    congr 1
    rw [Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Uᴴ U X, hUh, Matrix.one_mul]
  exact (mul_self_inj (norm_nonneg _) (norm_nonneg _)).mp h

private lemma tx_norm_right_orth {a b : ℕ} (X : Matrix (Fin a) (Fin b) ℝ)
    (W : Matrix (Fin b) (Fin b) ℝ) (hW : Wᵀ * W = 1) : ‖X * W‖ = ‖X‖ := by
  calc ‖X * W‖ = ‖(X * W)ᴴ‖ := (Matrix.l2_opNorm_conjTranspose _).symm
    _ = ‖Wᴴ * Xᴴ‖ := by rw [Matrix.conjTranspose_mul]
    _ = ‖Xᴴ‖ := by
      refine tx_norm_left_orth Wᴴ ?_ Xᴴ
      rw [Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.transpose_transpose]
      exact mul_eq_one_comm.mp hW
    _ = ‖X‖ := Matrix.l2_opNorm_conjTranspose X

private theorem tx_opNorm_conj_diag {k : ℕ} (U : Matrix (Fin k) (Fin k) ℝ) (hU : Uᵀ * U = 1)
    (d : Fin k → ℝ) (hd : ∀ i, |d i| ≤ 1) : opNorm (U * Matrix.diagonal d * Uᵀ) ≤ 1 := by
  rw [opNorm_eq_norm]
  have hU' : (Uᵀ)ᵀ * Uᵀ = 1 := by rw [Matrix.transpose_transpose]; exact mul_eq_one_comm.mp hU
  rw [tx_norm_right_orth _ Uᵀ (by rw [Matrix.transpose_transpose]; exact mul_eq_one_comm.mp hU),
    tx_norm_left_orth U hU, Matrix.l2_opNorm_diagonal]
  exact (pi_norm_le_iff_of_nonneg zero_le_one).mpr fun i => by simpa using hd i

end TxOrth


private lemma tx_tree_smulF {m n : ℕ} (β : ℝ) (ℓ J : ℕ) (R : ℝ) (B : ℕ) (μ : Fin m → ℝ)
    (lam : Fin n → ℝ) (Fd : Fin m → ℝ) (Gd : Fin n → ℝ) (c : ℝ) (f₁ f₂ : Polynomial ℝ) :
    def_app_vol_tree β ℓ J R B μ lam (c • Fd) Gd f₁ f₂ =
      c * def_app_vol_tree β ℓ J R B μ lam Fd Gd f₁ f₂ := by
  have h0 := def_app_vol_tree_linear_F β ℓ J R B μ lam 0 0 Gd 1 f₁ f₂
  simp only [smul_zero, add_zero, one_mul] at h0
  have h1 := def_app_vol_tree_linear_F β ℓ J R B μ lam Fd 0 Gd c f₁ f₂
  simp only [add_zero] at h1
  rw [h1]; linarith

private lemma tx_tree_smulG {m n : ℕ} (β : ℝ) (ℓ J : ℕ) (R : ℝ) (B : ℕ) (μ : Fin m → ℝ)
    (lam : Fin n → ℝ) (Fd : Fin m → ℝ) (Gd : Fin n → ℝ) (c : ℝ) (f₁ f₂ : Polynomial ℝ) :
    def_app_vol_tree β ℓ J R B μ lam Fd (c • Gd) f₁ f₂ =
      c * def_app_vol_tree β ℓ J R B μ lam Fd Gd f₁ f₂ := by
  have h0 := def_app_vol_tree_linear_G β ℓ J R B μ lam Fd 0 0 1 f₁ f₂
  simp only [smul_zero, add_zero, one_mul] at h0
  have h1 := def_app_vol_tree_linear_G β ℓ J R B μ lam Fd Gd 0 c f₁ f₂
  simp only [add_zero] at h1
  rw [h1]; linarith

private lemma tx_K1 (cert : Muon.External.GaussianOpNorm) (γstar CSig : ℝ)
    {m n B : ℕ} (Fp : FrozenParams m n B) (S : SpectralData Fp.C) (hS : SizeFin Fp.C B γstar CSig)
    (ℓ J : ℕ) (R : ℝ) (Fd : Fin m → ℝ) (Gd : Fin n → ℝ)
    (hF : opNorm (S.uOut * Matrix.diagonal Fd * S.uOutᵀ) ≤ 1)
    (hG : opNorm (S.vIn * Matrix.diagonal Gd * S.vInᵀ) ≤ 1)
    (D : ℝ) (hD : volDR cert R CSig γstar ≤ D) (P Q : Polynomial ℝ) :
    |def_app_vol_tree Fp.β ℓ J R B S.μ S.lam Fd Gd P Q| ≤
      γstar * supOn D (fun x => P.eval x) * supOn D (fun x => Q.eval x) := by
  obtain ⟨P', hP1, hP2, -⟩ := tx_oddPart P
  obtain ⟨Q', hQ1, hQ2, -⟩ := tx_oddPart Q
  rw [tx_tree_congr _ _ _ _ _ _ _ _ _ P Q P' Q' (fun a => (hP2 a).symm) (fun a => (hQ2 a).symm)]
  have oP : ∀ x, P'.eval (-x) = -P'.eval x := fun x => by rw [hP1, hP1]; simp; ring
  have oQ : ∀ x, Q'.eval (-x) = -Q'.eval x := fun x => by rw [hQ1, hQ1]; simp; ring
  refine (tx_bound cert γstar CSig Fp S hS ℓ J R Fd Gd hF hG D hD P' Q' oP oQ).trans ?_
  have sle : ∀ P0 P0' : Polynomial ℝ, (∀ x, P0'.eval x = (P0.eval x - P0.eval (-x)) / 2) →
      supOn D (fun x => P0'.eval x) ≤ supOn D (fun x => P0.eval x) := by
    intro P0 P0' h
    refine tx_supOn_le D _ _ (tx_supOn_nonneg _ _) fun x hx => ?_
    have a := tx_le_supOn D _ P0.continuous.continuousOn x hx
    have b := tx_le_supOn D _ P0.continuous.continuousOn (-x) ⟨by linarith [hx.2], by linarith [hx.1]⟩
    rw [h]
    have : |(P0.eval x - P0.eval (-x)) / 2| ≤ (|P0.eval x| + |P0.eval (-x)|) / 2 := by
      rw [abs_div, abs_two]; gcongr; exact abs_sub _ _
    linarith
  have hγ := tx_gamma_nonneg Fp γstar CSig hS
  exact mul_le_mul (mul_le_mul_of_nonneg_left (sle P P' hP1) hγ) (sle Q Q' hQ1)
    (tx_supOn_nonneg _ _) (mul_nonneg hγ (tx_supOn_nonneg _ _))

private lemma tx_K1' (cert : Muon.External.GaussianOpNorm) (γstar CSig : ℝ)
    {m n B : ℕ} (Fp : FrozenParams m n B) (S : SpectralData Fp.C) (hS : SizeFin Fp.C B γstar CSig)
    (ℓ J : ℕ) (R : ℝ) (Fd : Fin m → ℝ) (Gd : Fin n → ℝ)
    (D : ℝ) (hD : volDR cert R CSig γstar ≤ D) :
    ∃ κ : ℝ, 0 ≤ κ ∧ ∀ P Q : Polynomial ℝ,
    |def_app_vol_tree Fp.β ℓ J R B S.μ S.lam Fd Gd P Q| ≤
      κ * supOn D (fun x => P.eval x) * supOn D (fun x => Q.eval x) := by
  set sF := 1 + ∑ i, |Fd i| with hsF
  set sG := 1 + ∑ j, |Gd j| with hsG
  have hsF0 : 1 ≤ sF := by have := Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) => abs_nonneg (Fd i)); linarith
  have hsG0 : 1 ≤ sG := by have := Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) => abs_nonneg (Gd i)); linarith
  have hγ := tx_gamma_nonneg Fp γstar CSig hS
  refine ⟨sF * sG * γstar, by positivity, fun P Q => ?_⟩
  have e1 : Fd = sF • (sF⁻¹ • Fd) := by rw [smul_smul, mul_inv_cancel₀ (by linarith), one_smul]
  have e2 : Gd = sG • (sG⁻¹ • Gd) := by rw [smul_smul, mul_inv_cancel₀ (by linarith), one_smul]
  have hF : opNorm (S.uOut * Matrix.diagonal (sF⁻¹ • Fd) * S.uOutᵀ) ≤ 1 := by
    refine tx_opNorm_conj_diag _ S.huOut _ fun i => ?_
    simp only [Pi.smul_apply, smul_eq_mul, abs_mul, abs_inv, abs_of_pos (by linarith : 0 < sF)]
    rw [inv_mul_le_iff₀ (by linarith)]
    have : |Fd i| ≤ ∑ i, |Fd i| := Finset.single_le_sum (fun j _ => abs_nonneg (Fd j)) (Finset.mem_univ i)
    linarith
  have hG : opNorm (S.vIn * Matrix.diagonal (sG⁻¹ • Gd) * S.vInᵀ) ≤ 1 := by
    refine tx_opNorm_conj_diag _ S.hvIn _ fun i => ?_
    simp only [Pi.smul_apply, smul_eq_mul, abs_mul, abs_inv, abs_of_pos (by linarith : 0 < sG)]
    rw [inv_mul_le_iff₀ (by linarith)]
    have : |Gd i| ≤ ∑ i, |Gd i| := Finset.single_le_sum (fun j _ => abs_nonneg (Gd j)) (Finset.mem_univ i)
    linarith
  have h := tx_K1 cert γstar CSig Fp S hS ℓ J R _ _ hF hG D hD P Q
  conv_lhs => rw [e1, e2, tx_tree_smulF, tx_tree_smulG]
  rw [abs_mul, abs_mul, abs_of_pos (by linarith : 0 < sF), abs_of_pos (by linarith : 0 < sG)]
  have := mul_le_mul_of_nonneg_left h (by positivity : 0 ≤ sF * sG)
  calc sF * (sG * |_|) = sF * sG * |_| := by ring
    _ ≤ _ := this
    _ = _ := by ring


private lemma tx_treeApprox_spec (D : ℝ) (f : ℝ → ℝ) (hf : ContinuousOn f (Set.Icc (-D) D)) (k : ℕ) :
    ∀ x ∈ Set.Icc (-D) D, |(treeApprox D f k).eval x - f x| ≤ 1 / ((k : ℝ) + 1) := by
  unfold treeApprox
  rw [dif_pos hf]
  exact fun x hx => (Classical.choose_spec
    (exists_polynomial_near_of_continuousOn (-D) D f hf (1 / ((k : ℝ) + 1)) (by positivity)) x hx).le

private lemma tx_ext_lim (cert : Muon.External.GaussianOpNorm) (γstar CSig : ℝ)
    {m n B : ℕ} (Fp : FrozenParams m n B) (S : SpectralData Fp.C) (hS : SizeFin Fp.C B γstar CSig)
    (ℓ J : ℕ) (R : ℝ) (D : ℝ) (hD : volDR cert R CSig γstar ≤ D) (f g : ℝ → ℝ)
    (hfc : ContinuousOn f (Set.Icc (-D) D)) (hgc : ContinuousOn g (Set.Icc (-D) D))
    (Fd : Fin m → ℝ) (Gd : Fin n → ℝ) :
    Tendsto (fun k : ℕ => def_app_vol_tree Fp.β ℓ J R B S.μ S.lam Fd Gd
        (treeApprox D f k) (treeApprox D g k)) atTop
      (𝓝 (treeRespExt Fp.β ℓ J R B S.μ S.lam Fd Gd D f g)) := by
  obtain ⟨κ, hκ, hB⟩ := tx_K1' cert γstar CSig Fp S hS ℓ J R Fd Gd D hD
  obtain ⟨L, hL⟩ := tx_cauchy (fun P Q => def_app_vol_tree Fp.β ℓ J R B S.μ S.lam Fd Gd P Q) κ D hκ
    (fun P P' Q c => tx_tree_lin_left _ _ _ _ _ _ _ _ _ P P' Q c)
    (fun P Q Q' c => tx_tree_lin_right _ _ _ _ _ _ _ _ _ Q Q' P c) hB f g hfc hgc
    (fun k => treeApprox D f k) (fun k => treeApprox D g k)
    (tx_treeApprox_spec D f hfc) (tx_treeApprox_spec D g hgc)
  have := hL.limUnder_eq
  unfold treeRespExt
  rw [this]
  exact hL


private lemma tx_ext_ii (cert : Muon.External.GaussianOpNorm) (γstar CSig : ℝ)
    {m n B : ℕ} (Fp : FrozenParams m n B) (S : SpectralData Fp.C) (hS : SizeFin Fp.C B γstar CSig)
    (ℓ J : ℕ) (R : ℝ) (D : ℝ) (hD : volDR cert R CSig γstar ≤ D) (f g : ℝ → ℝ)
    (hfc : ContinuousOn f (Set.Icc (-D) D)) (hfo : ∀ x ∈ Set.Icc (-D) D, f (-x) = -f x)
    (hgc : ContinuousOn g (Set.Icc (-D) D)) (hgo : ∀ x ∈ Set.Icc (-D) D, g (-x) = -g x) :
    (∀ (Fd : Fin m → ℝ) (Gd : Fin n → ℝ),
      Tendsto (fun k : ℕ => def_app_vol_tree Fp.β ℓ J R B S.μ S.lam Fd Gd
          (treeApprox D f k) (treeApprox D g k)) atTop
        (𝓝 (treeRespExt Fp.β ℓ J R B S.μ S.lam Fd Gd D f g))) ∧
    (∀ (Fd : Fin m → ℝ) (Gd : Fin n → ℝ) (Fm : Mat m m) (Gm : Mat n n),
      Fm = S.uOut * Matrix.diagonal Fd * S.uOutᵀ → Gm = S.vIn * Matrix.diagonal Gd * S.vInᵀ →
      opNorm Fm ≤ 1 → opNorm Gm ≤ 1 →
      |treeRespExt Fp.β ℓ J R B S.μ S.lam Fd Gd D f g| ≤
        γstar * supOn D f * supOn D g) ∧
    (∀ (N : ℕ), 0 < N → ∀ (Fd : Fin m → ℝ) (Gd : Fin n → ℝ),
      treeRespExt Fp.β ℓ J R (N * B) (replVec N S.μ) (replVec N S.lam) (replVec N Fd)
          (replVec N Gd) D f g =
        treeRespExt Fp.β ℓ J R B S.μ S.lam Fd Gd D f g) ∧
    (∀ (c : ℝ) (Fd₁ Fd₂ : Fin m → ℝ) (Gd : Fin n → ℝ),
      treeRespExt Fp.β ℓ J R B S.μ S.lam (fun i => c * Fd₁ i + Fd₂ i) Gd D f g =
        c * treeRespExt Fp.β ℓ J R B S.μ S.lam Fd₁ Gd D f g +
          treeRespExt Fp.β ℓ J R B S.μ S.lam Fd₂ Gd D f g) ∧
    (∀ (c : ℝ) (Fd : Fin m → ℝ) (Gd₁ Gd₂ : Fin n → ℝ),
      treeRespExt Fp.β ℓ J R B S.μ S.lam Fd (fun j => c * Gd₁ j + Gd₂ j) D f g =
        c * treeRespExt Fp.β ℓ J R B S.μ S.lam Fd Gd₁ D f g +
          treeRespExt Fp.β ℓ J R B S.μ S.lam Fd Gd₂ D f g) ∧
    (∀ (c : ℝ) (f' : ℝ → ℝ), ContinuousOn f' (Set.Icc (-D) D) →
      (∀ x ∈ Set.Icc (-D) D, f' (-x) = -f' x) → ∀ (Fd : Fin m → ℝ) (Gd : Fin n → ℝ),
      treeRespExt Fp.β ℓ J R B S.μ S.lam Fd Gd D (fun x => f x + c * f' x) g =
        treeRespExt Fp.β ℓ J R B S.μ S.lam Fd Gd D f g +
          c * treeRespExt Fp.β ℓ J R B S.μ S.lam Fd Gd D f' g) ∧
    (∀ (c : ℝ) (g' : ℝ → ℝ), ContinuousOn g' (Set.Icc (-D) D) →
      (∀ x ∈ Set.Icc (-D) D, g' (-x) = -g' x) → ∀ (Fd : Fin m → ℝ) (Gd : Fin n → ℝ),
      treeRespExt Fp.β ℓ J R B S.μ S.lam Fd Gd D f (fun x => g x + c * g' x) =
        treeRespExt Fp.β ℓ J R B S.μ S.lam Fd Gd D f g +
          c * treeRespExt Fp.β ℓ J R B S.μ S.lam Fd Gd D f g') ∧
    (∀ (p q : Polynomial ℝ), (∀ x : ℝ, p.eval (-x) = -p.eval x) →
      (∀ x : ℝ, q.eval (-x) = -q.eval x) → ∀ (Fd : Fin m → ℝ) (Gd : Fin n → ℝ),
      treeRespExt Fp.β ℓ J R B S.μ S.lam Fd Gd D (fun x => p.eval x) (fun x => q.eval x) =
        def_app_vol_tree Fp.β ℓ J R B S.μ S.lam Fd Gd p q) := by
  have lim := fun (f g : ℝ → ℝ) (hf : ContinuousOn f (Set.Icc (-D) D)) (hg : ContinuousOn g (Set.Icc (-D) D))
    (Fd : Fin m → ℝ) (Gd : Fin n → ℝ) => tx_ext_lim cert γstar CSig Fp S hS ℓ J R D hD f g hf hg Fd Gd
  have hδ0 : ∀ k : ℕ, 0 ≤ 1 / ((k : ℝ) + 1) := fun k => by positivity
  have hδ1 : ∀ k : ℕ, 1 / ((k : ℝ) + 1) ≤ 1 := fun k => by
    rw [div_le_one (by positivity)]; linarith [(Nat.cast_nonneg k : (0:ℝ) ≤ k)]
  have hδt : Tendsto (fun k : ℕ => 1 / ((k : ℝ) + 1)) atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  refine ⟨fun Fd Gd => lim f g hfc hgc Fd Gd, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- (b)
    intro Fd Gd Fm Gm hFm hGm hF hG
    subst hFm hGm
    have hl := lim f g hfc hgc Fd Gd
    have hb : Tendsto (fun k : ℕ => γstar * (supOn D f + 1 / ((k : ℝ) + 1)) * (supOn D g + 1 / ((k : ℝ) + 1)))
        atTop (𝓝 (γstar * (supOn D f + 0) * (supOn D g + 0))) :=
      ((tendsto_const_nhds.add hδt).const_mul γstar).mul (tendsto_const_nhds.add hδt)
    simp only [add_zero] at hb
    refine le_of_tendsto_of_tendsto hl.abs hb (Eventually.of_forall fun k => ?_)
    refine (tx_K1 cert γstar CSig Fp S hS ℓ J R Fd Gd hF hG D hD _ _).trans ?_
    have hγ := tx_gamma_nonneg Fp γstar CSig hS
    have s1 := tx_sup_near D _ f hfc _ (hδ0 k) (tx_treeApprox_spec D f hfc k)
    have s2 := tx_sup_near D _ g hgc _ (hδ0 k) (tx_treeApprox_spec D g hgc k)
    exact mul_le_mul (mul_le_mul_of_nonneg_left s1 hγ) s2 (tx_supOn_nonneg _ _)
      (mul_nonneg hγ (add_nonneg (tx_supOn_nonneg _ _) (hδ0 k)))
  · -- (c)
    intro N hN Fd Gd
    unfold treeRespExt
    refine congrArg (limUnder atTop) (funext fun k => ?_)
    exact def_app_vol_tree_replication Fp.β ℓ J R B S.μ S.lam Fd Gd N hN _ _
  · -- (d) F
    intro c Fd₁ Fd₂ Gd
    have e : (fun i => c * Fd₁ i + Fd₂ i) = c • Fd₁ + Fd₂ := by funext i; simp
    rw [e]
    refine tendsto_nhds_unique (lim f g hfc hgc _ Gd) ?_
    have := ((lim f g hfc hgc Fd₁ Gd).const_mul c).add (lim f g hfc hgc Fd₂ Gd)
    refine this.congr fun k => ?_
    rw [def_app_vol_tree_linear_F]
  · -- (d) G
    intro c Fd Gd₁ Gd₂
    have e : (fun i => c * Gd₁ i + Gd₂ i) = c • Gd₁ + Gd₂ := by funext i; simp
    rw [e]
    refine tendsto_nhds_unique (lim f g hfc hgc Fd _) ?_
    have := ((lim f g hfc hgc Fd Gd₁).const_mul c).add (lim f g hfc hgc Fd Gd₂)
    refine this.congr fun k => ?_
    rw [def_app_vol_tree_linear_G]
  · -- (e)
    intro c f' hf'c hf'o Fd Gd
    obtain ⟨κ, hκ, hB⟩ := tx_K1' cert γstar CSig Fp S hS ℓ J R Fd Gd D hD
    have hhc : ContinuousOn (fun x => f x + c * f' x) (Set.Icc (-D) D) :=
      hfc.add (continuousOn_const.mul hf'c)
    have hL := fun P P' Q (c : ℝ) => tx_tree_lin_left Fp.β ℓ J R B S.μ S.lam Fd Gd P P' Q c
    have hR := fun P Q Q' (c : ℝ) => tx_tree_lin_right Fp.β ℓ J R B S.μ S.lam Fd Gd Q Q' P c
    have hcl := tx_close (fun P Q => def_app_vol_tree Fp.β ℓ J R B S.μ S.lam Fd Gd P Q) κ D hκ hL hR hB
      (fun k => treeApprox D (fun x => f x + c * f' x) k) (fun k => treeApprox D g k)
      (fun k => treeApprox D f k + Polynomial.C c * treeApprox D f' k) (fun k => treeApprox D g k)
      (fun k => (2 + |c|) * (1 / ((k : ℝ) + 1)))
      (fun k => mul_nonneg (by positivity) (hδ0 k))
      (by simpa using hδt.const_mul (2 + |c|))
      ((supOn D g + 1) + (supOn D (fun x => f x + c * f' x) + 1 + |c|))
      (fun k => tx_sup_diff D _ _ _ (mul_nonneg (by positivity) (hδ0 k)) (fun x hx => by
        have a1 := tx_treeApprox_spec D (fun x => f x + c * f' x) hhc k x hx
        have a2 := tx_treeApprox_spec D f hfc k x hx
        have a3 := tx_treeApprox_spec D f' hf'c k x hx
        have a4 : |c * ((treeApprox D f' k).eval x - f' x)| ≤ |c| * (1 / ((k : ℝ) + 1)) := by
          rw [abs_mul]; exact mul_le_mul_of_nonneg_left a3 (abs_nonneg c)
        have : (treeApprox D (fun x => f x + c * f' x) k).eval x -
            (treeApprox D f k + Polynomial.C c * treeApprox D f' k).eval x =
            ((treeApprox D (fun x => f x + c * f' x) k).eval x - (f x + c * f' x)) -
            ((treeApprox D f k).eval x - f x) - c * ((treeApprox D f' k).eval x - f' x) := by
          simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C]; ring
        rw [this]
        calc _ ≤ |(treeApprox D (fun x => f x + c * f' x) k).eval x - (f x + c * f' x)| +
              |(treeApprox D f k).eval x - f x| + |c * ((treeApprox D f' k).eval x - f' x)| :=
              (abs_sub _ _).trans (add_le_add_left (le_refl _) _ |>.trans' (by
                have := abs_sub (((treeApprox D (fun x => f x + c * f' x) k).eval x - (f x + c * f' x)))
                  ((treeApprox D f k).eval x - f x)
                linarith))
          _ ≤ _ := by nlinarith))
      (fun k => tx_sup_diff D _ _ _ (mul_nonneg (by positivity) (hδ0 k)) (fun x hx => by
        rw [sub_self, abs_zero]; exact mul_nonneg (by positivity) (hδ0 k)))
      (fun k => (tx_sup_near D _ g hgc _ (hδ0 k) (tx_treeApprox_spec D g hgc k)).trans (by
        have := hδ1 k
        have := tx_supOn_nonneg D (fun x => f x + c * f' x)
        have := abs_nonneg c
        linarith))
      (fun k => (tx_sup_near D _ (fun x => f x + c * f' x) hhc ((1 + |c|) * (1 / ((k : ℝ) + 1)))
        (mul_nonneg (by positivity) (hδ0 k)) (fun x hx => by
          have a2 := tx_treeApprox_spec D f hfc k x hx
          have a3 := tx_treeApprox_spec D f' hf'c k x hx
          have a4 : |c * ((treeApprox D f' k).eval x - f' x)| ≤ |c| * (1 / ((k : ℝ) + 1)) := by
            rw [abs_mul]; exact mul_le_mul_of_nonneg_left a3 (abs_nonneg c)
          have : (treeApprox D f k + Polynomial.C c * treeApprox D f' k).eval x - (f x + c * f' x) =
              ((treeApprox D f k).eval x - f x) + c * ((treeApprox D f' k).eval x - f' x) := by
            simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C]; ring
          rw [this]
          nlinarith [abs_add_le (((treeApprox D f k).eval x - f x)) (c * ((treeApprox D f' k).eval x - f' x))])).trans (by
        have := hδ1 k
        have := tx_supOn_nonneg D g
        have := abs_nonneg c
        nlinarith))
    have h2 : Tendsto (fun k : ℕ => def_app_vol_tree Fp.β ℓ J R B S.μ S.lam Fd Gd (treeApprox D f k) (treeApprox D g k) +
        c * def_app_vol_tree Fp.β ℓ J R B S.μ S.lam Fd Gd (treeApprox D f' k) (treeApprox D g k)) atTop
        (𝓝 (treeRespExt Fp.β ℓ J R B S.μ S.lam Fd Gd D f g + c * treeRespExt Fp.β ℓ J R B S.μ S.lam Fd Gd D f' g)) :=
      (lim f g hfc hgc Fd Gd).add ((lim f' g hf'c hgc Fd Gd).const_mul c)
    have h3 := hcl.add (h2.congr fun k => (hL _ _ _ c).symm)
    refine tendsto_nhds_unique (lim _ g hhc hgc Fd Gd) ?_
    simpa using h3
  · -- (e2)
    intro c g' hg'c hg'o Fd Gd
    obtain ⟨κ, hκ, hB⟩ := tx_K1' cert γstar CSig Fp S hS ℓ J R Fd Gd D hD
    have hhc : ContinuousOn (fun x => g x + c * g' x) (Set.Icc (-D) D) :=
      hgc.add (continuousOn_const.mul hg'c)
    have hL := fun P P' Q (c : ℝ) => tx_tree_lin_left Fp.β ℓ J R B S.μ S.lam Fd Gd P P' Q c
    have hR := fun P Q Q' (c : ℝ) => tx_tree_lin_right Fp.β ℓ J R B S.μ S.lam Fd Gd Q Q' P c
    have hcl := tx_close (fun P Q => def_app_vol_tree Fp.β ℓ J R B S.μ S.lam Fd Gd P Q) κ D hκ hL hR hB
      (fun k => treeApprox D f k) (fun k => treeApprox D (fun x => g x + c * g' x) k)
      (fun k => treeApprox D f k) (fun k => treeApprox D g k + Polynomial.C c * treeApprox D g' k)
      (fun k => (2 + |c|) * (1 / ((k : ℝ) + 1)))
      (fun k => mul_nonneg (by positivity) (hδ0 k))
      (by simpa using hδt.const_mul (2 + |c|))
      ((supOn D f + 1) + (supOn D (fun x => g x + c * g' x) + 1 + |c|))
      (fun k => tx_sup_diff D _ _ _ (mul_nonneg (by positivity) (hδ0 k)) (fun x hx => by
        rw [sub_self, abs_zero]; exact mul_nonneg (by positivity) (hδ0 k)))
      (fun k => tx_sup_diff D _ _ _ (mul_nonneg (by positivity) (hδ0 k)) (fun x hx => by
        have a1 := tx_treeApprox_spec D (fun x => g x + c * g' x) hhc k x hx
        have a2 := tx_treeApprox_spec D g hgc k x hx
        have a3 := tx_treeApprox_spec D g' hg'c k x hx
        have a4 : |c * ((treeApprox D g' k).eval x - g' x)| ≤ |c| * (1 / ((k : ℝ) + 1)) := by
          rw [abs_mul]; exact mul_le_mul_of_nonneg_left a3 (abs_nonneg c)
        have : (treeApprox D (fun x => g x + c * g' x) k).eval x -
            (treeApprox D g k + Polynomial.C c * treeApprox D g' k).eval x =
            ((treeApprox D (fun x => g x + c * g' x) k).eval x - (g x + c * g' x)) -
            ((treeApprox D g k).eval x - g x) - c * ((treeApprox D g' k).eval x - g' x) := by
          simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C]; ring
        rw [this]
        have b1 := abs_sub (((treeApprox D (fun x => g x + c * g' x) k).eval x - (g x + c * g' x)))
          ((treeApprox D g k).eval x - g x)
        have b2 := abs_sub ((((treeApprox D (fun x => g x + c * g' x) k).eval x - (g x + c * g' x)) -
          ((treeApprox D g k).eval x - g x))) (c * ((treeApprox D g' k).eval x - g' x))
        nlinarith))
      (fun k => (tx_sup_near D _ (fun x => g x + c * g' x) hhc _ (hδ0 k)
        (tx_treeApprox_spec D _ hhc k)).trans (by
        have := hδ1 k
        have := tx_supOn_nonneg D f
        have := abs_nonneg c
        linarith))
      (fun k => (tx_sup_near D _ f hfc _ (hδ0 k) (tx_treeApprox_spec D f hfc k)).trans (by
        have := hδ1 k
        have := tx_supOn_nonneg D (fun x => g x + c * g' x)
        have := abs_nonneg c
        linarith))
    have h2 : Tendsto (fun k : ℕ => def_app_vol_tree Fp.β ℓ J R B S.μ S.lam Fd Gd (treeApprox D f k) (treeApprox D g k) +
        c * def_app_vol_tree Fp.β ℓ J R B S.μ S.lam Fd Gd (treeApprox D f k) (treeApprox D g' k)) atTop
        (𝓝 (treeRespExt Fp.β ℓ J R B S.μ S.lam Fd Gd D f g + c * treeRespExt Fp.β ℓ J R B S.μ S.lam Fd Gd D f g')) :=
      (lim f g hfc hgc Fd Gd).add ((lim f g' hfc hg'c Fd Gd).const_mul c)
    have h3 := hcl.add (h2.congr fun k => (hR _ _ _ c).symm)
    refine tendsto_nhds_unique (lim f _ hfc hhc Fd Gd) ?_
    simpa using h3
  · -- (f)
    intro p q _ _ Fd Gd
    obtain ⟨κ, hκ, hB⟩ := tx_K1' cert γstar CSig Fp S hS ℓ J R Fd Gd D hD
    have hpc : ContinuousOn (fun x => p.eval x) (Set.Icc (-D) D) := p.continuous.continuousOn
    have hqc : ContinuousOn (fun x => q.eval x) (Set.Icc (-D) D) := q.continuous.continuousOn
    have hL := fun P P' Q (c : ℝ) => tx_tree_lin_left Fp.β ℓ J R B S.μ S.lam Fd Gd P P' Q c
    have hR := fun P Q Q' (c : ℝ) => tx_tree_lin_right Fp.β ℓ J R B S.μ S.lam Fd Gd Q Q' P c
    have hcl := tx_close (fun P Q => def_app_vol_tree Fp.β ℓ J R B S.μ S.lam Fd Gd P Q) κ D hκ hL hR hB
      (fun k => treeApprox D (fun x => p.eval x) k) (fun k => treeApprox D (fun x => q.eval x) k)
      (fun _ => p) (fun _ => q) (fun k => 1 / ((k : ℝ) + 1)) hδ0 hδt
      ((supOn D (fun x => q.eval x) + 1) + supOn D (fun x => p.eval x))
      (fun k => tx_sup_diff D _ _ _ (hδ0 k) (tx_treeApprox_spec D _ hpc k))
      (fun k => tx_sup_diff D _ _ _ (hδ0 k) (tx_treeApprox_spec D _ hqc k))
      (fun k => (tx_sup_near D _ _ hqc _ (hδ0 k) (tx_treeApprox_spec D _ hqc k)).trans (by
        have := hδ1 k
        have := tx_supOn_nonneg D (fun x => p.eval x)
        linarith))
      (fun k => by
        have := tx_supOn_nonneg D (fun x => q.eval x)
        linarith)
    refine tendsto_nhds_unique (lim _ _ hpc hqc Fd Gd) ?_
    simpa using hcl.add_const (def_app_vol_tree Fp.β ℓ J R B S.μ S.lam Fd Gd p q)

/-! ### Helpers for `lem:app-vol-tree-extension`(iii): interpolation and pointwise comparison -/

private lemma tx_finite_lip (S : Finset ℝ) (h : ℝ → ℝ) :
    ∃ L : NNReal, LipschitzOnWith L h (S : Set ℝ) := by
  classical
  set L : ℝ := ∑ p ∈ S ×ˢ S, |h p.1 - h p.2| / |p.1 - p.2| with hL
  refine ⟨L.toNNReal, LipschitzOnWith.of_dist_le' fun x hx y hy => ?_⟩
  simp only [Real.dist_eq]
  by_cases hxy : x = y
  · subst hxy; simp
  · have hpos : 0 < |x - y| := abs_pos.mpr (sub_ne_zero.mpr hxy)
    have hmem : (x, y) ∈ S ×ˢ S := Finset.mem_product.mpr ⟨hx, hy⟩
    have h1 : |h x - h y| / |x - y| ≤ L :=
      Finset.single_le_sum (f := fun p : ℝ × ℝ => |h p.1 - h p.2| / |p.1 - p.2|)
        (fun p _ => by positivity) hmem
    rw [div_le_iff₀ hpos] at h1
    exact h1

private lemma tx_interp (S : Finset ℝ) (h : ℝ → ℝ) (hodd : ∀ x, h (-x) = -h x) (M : ℝ)
    (hM : ∀ x, |h x| ≤ M) :
    ∃ g : ℝ → ℝ, IsOddBddLip g ∧ (∀ x, |g x| ≤ M) ∧ ∀ x ∈ S, g x = h x := by
  classical
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  set S' : Finset ℝ := S ∪ S.image (fun x => -x) with hS'
  obtain ⟨L, hL⟩ := tx_finite_lip S' h
  obtain ⟨g0, hg0, heq⟩ := hL.extend_real
  set g1 : ℝ → ℝ := fun x => max (-M) (min M (g0 x)) with hg1
  have hg1lip : ∀ x y, |g1 x - g1 y| ≤ (L : ℝ) * |x - y| := by
    intro x y
    refine (tx_clamp_lip M (g0 x) (g0 y)).trans ?_
    have := hg0.dist_le_mul x y
    simpa [Real.dist_eq] using this
  have hg1b : ∀ x, |g1 x| ≤ M := fun x => tx_clamp_abs M hM0 _
  have hS'1 : ∀ x ∈ S, x ∈ (S' : Set ℝ) := fun x hx => by
    simp only [hS', Finset.coe_union, Set.mem_union, Finset.mem_coe]; exact Or.inl hx
  have hS'2 : ∀ x ∈ S, -x ∈ (S' : Set ℝ) := fun x hx => by
    simp only [hS', Finset.coe_union, Set.mem_union, Finset.mem_coe, Finset.mem_image]
    exact Or.inr ⟨x, hx, rfl⟩
  have hg1h : ∀ x ∈ S, g1 x = h x := fun x hx => by
    simp only [hg1, ← heq (hS'1 x hx)]
    exact tx_clamp_self M _ (hM x)
  have hg1h' : ∀ x ∈ S, g1 (-x) = -h x := fun x hx => by
    simp only [hg1, ← heq (hS'2 x hx)]
    rw [hodd x]
    exact tx_clamp_self M _ (by rw [abs_neg]; exact hM x)
  refine ⟨fun x => (g1 x - g1 (-x)) / 2, ⟨fun x => ?_, ⟨M, fun x => ?_⟩, ⟨L, fun x y => ?_⟩⟩, ?_, ?_⟩
  · simp only [neg_neg]; ring
  · have := abs_sub (g1 x) (g1 (-x))
    rw [abs_div, abs_two]
    linarith [hg1b x, hg1b (-x)]
  · have h1 := hg1lip x y
    have h2 := hg1lip (-x) (-y)
    have h3 : |(-x) - (-y)| = |x - y| := by rw [← abs_neg]; ring_nf
    rw [h3] at h2
    have : (g1 x - g1 (-x)) / 2 - (g1 y - g1 (-y)) / 2 =
        ((g1 x - g1 y) - (g1 (-x) - g1 (-y))) / 2 := by ring
    rw [this, abs_div, abs_two, div_le_iff₀ (by norm_num)]
    have := abs_sub (g1 x - g1 y) (g1 (-x) - g1 (-y))
    linarith
  · intro x
    have := abs_sub (g1 x) (g1 (-x))
    rw [abs_div, abs_two]
    linarith [hg1b x, hg1b (-x)]
  · intro x hx
    simp only [hg1h x hx, hg1h' x hx]; ring

private lemma tx_approx_Lip (f p : ℝ → ℝ) (hf : ∀ x, f (-x) = -f x) (hp : IsOddBddLip p)
    (D a : ℝ) (ha : 0 ≤ a) (hcl : ∀ x ∈ Set.Icc (-D) D, |f x - p x| ≤ a)
    (S : Finset ℝ) (hS : ∀ x ∈ S, |x| ≤ D) :
    ∃ g : ℝ → ℝ, IsOddBddLip g ∧ (∀ x ∈ S, g x = f x) ∧ ∀ x, |g x - p x| ≤ a := by
  obtain ⟨hpo, ⟨Mp, hMp⟩, ⟨Lp, hLp⟩⟩ := hp
  set h : ℝ → ℝ := fun x => max (-a) (min a (f x - p x)) with hh
  have hodd : ∀ x, h (-x) = -h x := fun x => by
    simp only [hh, hf x, hpo x]
    rw [show -f x - -p x = -(f x - p x) by ring]
    exact tx_clamp_neg a ha _
  obtain ⟨g1, ⟨hg1o, ⟨M1, hM1⟩, ⟨L1, hL1⟩⟩, hb1, he1⟩ :=
    tx_interp S h hodd a (fun x => tx_clamp_abs a ha _)
  refine ⟨fun x => p x + g1 x, ⟨fun x => ?_, ⟨Mp + M1, fun x => ?_⟩, ⟨Lp + L1, fun x y => ?_⟩⟩, ?_, ?_⟩
  · simp only [hpo x, hg1o x]; ring
  · exact (abs_add_le _ _).trans (add_le_add (hMp x) (hM1 x))
  · have h1 := hLp x y
    have h2 := hL1 x y
    have : p x + g1 x - (p y + g1 y) = (p x - p y) + (g1 x - g1 y) := by ring
    rw [this]
    nlinarith [abs_add_le (p x - p y) (g1 x - g1 y), abs_nonneg (x - y)]
  · intro x hx
    have hxI : x ∈ Set.Icc (-D) D := abs_le.mp (hS x hx)
    have e : h x = f x - p x := by
      simp only [hh]
      exact tx_clamp_self a _ (hcl x hxI)
    show p x + g1 x = f x
    rw [he1 x hx, e]; ring
  · intro x
    simpa using hb1 x

private lemma tx_le_supNorm (p : ℝ → ℝ) (hp : IsOddBddLip p) (x : ℝ) : |p x| ≤ supNorm p := by
  obtain ⟨_, ⟨M, hM⟩, _⟩ := hp
  exact le_ciSup (f := fun x => |p x|) ⟨M, by rintro _ ⟨y, rfl⟩; exact hM y⟩ x

private lemma tx_supNorm_le (g : ℝ → ℝ) (c : ℝ) (hc : 0 ≤ c) (h : ∀ x, |g x| ≤ c) : supNorm g ≤ c :=
  Real.iSup_le h hc

private lemma tx_supNorm_nonneg (g : ℝ → ℝ) : 0 ≤ supNorm g := Real.iSup_nonneg fun _ => abs_nonneg _

private lemma tx_oddSharp_lip {m n : ℕ} (f p : ℝ → ℝ) (hf : ∀ x, f (-x) = -f x) (hp : IsOddBddLip p)
    (K : Mat m n) (D a : ℝ) (ha : 0 ≤ a) (hK : opNorm K ≤ D)
    (hcl : ∀ x ∈ Set.Icc (-D) D, |f x - p x| ≤ a) :
    ∃ g : ℝ → ℝ, IsOddBddLip g ∧ oddSharp f K = oddSharp g K ∧ ∀ x, |g x - p x| ≤ a := by
  classical
  have hH := Muon.Foundations.hermDilation_isHermitian K
  have hfin : (spectrum ℝ (Muon.Foundations.hermDilation K)).Finite := by
    rw [hH.spectrum_real_eq_range_eigenvalues]; exact Set.finite_range _
  obtain ⟨g, hg, hgS, hgb⟩ := tx_approx_Lip f p hf hp D a ha hcl hfin.toFinset (fun x hx => by
    have := tx_spectrum_dilation K D hK (hfin.mem_toFinset.mp hx)
    exact abs_le.mpr this)
  refine ⟨g, hg, ?_, hgb⟩
  unfold oddSharp
  congr 1
  exact cfc_congr (fun x hx => (hgS x (hfin.mem_toFinset.mpr hx)).symm)

private lemma tx_contr_cmp {m n B : ℕ} (hB : 0 < B) (γ : ℝ) (hdim : ((min m n : ℕ) : ℝ) ≤ γ * B)
    (F : Matrix (Fin m) (Fin m) ℝ) (G : Matrix (Fin n) (Fin n) ℝ)
    (hF : opNorm F ≤ 1) (hG : opNorm G ≤ 1) (f₁ f₂ p₁ p₂ : ℝ → ℝ)
    (hf₁ : ∀ x, f₁ (-x) = -f₁ x) (hf₂ : ∀ x, f₂ (-x) = -f₂ x)
    (hp₁ : IsOddBddLip p₁) (hp₂ : IsOddBddLip p₂) (K H : Mat m n) (D₁ D₂ a₁ a₂ : ℝ)
    (ha₁ : 0 ≤ a₁) (ha₂ : 0 ≤ a₂) (hK : opNorm K ≤ D₁) (hH : opNorm H ≤ D₂)
    (hcl₁ : ∀ x ∈ Set.Icc (-D₁) D₁, |f₁ x - p₁ x| ≤ a₁)
    (hcl₂ : ∀ x ∈ Set.Icc (-D₂) D₂, |f₂ x - p₂ x| ≤ a₂) :
    |contraction B F G f₁ f₂ K H - contraction B F G p₁ p₂ K H| ≤
      γ * (a₁ * (supNorm p₂ + a₂) + supNorm p₁ * a₂) := by
  have hBpos : (0 : ℝ) < B := by exact_mod_cast hB
  have hγ : 0 ≤ γ := by
    by_contra h
    push Not at h
    have : γ * B < 0 := mul_neg_of_neg_of_pos h hBpos
    have h0 : (0 : ℝ) ≤ ((min m n : ℕ) : ℝ) := Nat.cast_nonneg _
    linarith
  obtain ⟨g₁, hg₁, he₁, hb₁⟩ := tx_oddSharp_lip f₁ p₁ hf₁ hp₁ K D₁ a₁ ha₁ hK hcl₁
  obtain ⟨g₂, hg₂, he₂, hb₂⟩ := tx_oddSharp_lip f₂ p₂ hf₂ hp₂ H D₂ a₂ ha₂ hH hcl₂
  have e : contraction B F G f₁ f₂ K H = contraction B F G g₁ g₂ K H := by
    unfold contraction; rw [he₁, he₂]
  rw [e]
  refine (lem_app_vol_finite_iii hB γ hdim F G hF hG g₁ g₂ p₁ p₂ hg₁ hg₂ hp₁ hp₂ K H).trans ?_
  have s1 : supNorm (fun x => g₁ x - p₁ x) ≤ a₁ := tx_supNorm_le _ _ ha₁ hb₁
  have s2 : supNorm (fun x => g₂ x - p₂ x) ≤ a₂ := tx_supNorm_le _ _ ha₂ hb₂
  have s3 : supNorm g₂ ≤ supNorm p₂ + a₂ :=
    tx_supNorm_le _ _ (add_nonneg (tx_supNorm_nonneg _) ha₂) fun x => by
      have h1 := tx_le_supNorm p₂ hp₂ x
      have h2 := hb₂ x
      calc |g₂ x| = |p₂ x + (g₂ x - p₂ x)| := by ring_nf
        _ ≤ |p₂ x| + |g₂ x - p₂ x| := abs_add_le _ _
        _ ≤ _ := by linarith
  refine mul_le_mul_of_nonneg_left ?_ hγ
  have n1 := tx_supNorm_nonneg (fun x => g₁ x - p₁ x)
  have n2 := tx_supNorm_nonneg g₂
  have n3 := tx_supNorm_nonneg p₁
  have n4 := tx_supNorm_nonneg (fun x => g₂ x - p₂ x)
  nlinarith [mul_le_mul s1 s3 n2 ha₁, mul_le_mul_of_nonneg_left s2 n3]

private lemma tx_contr_bdd {m n B : ℕ} (hB : 0 < B) (γ : ℝ) (hdim : ((min m n : ℕ) : ℝ) ≤ γ * B)
    (F : Matrix (Fin m) (Fin m) ℝ) (G : Matrix (Fin n) (Fin n) ℝ)
    (hF : opNorm F ≤ 1) (hG : opNorm G ≤ 1) (f₁ f₂ : ℝ → ℝ)
    (hf₁ : ∀ x, f₁ (-x) = -f₁ x) (hf₂ : ∀ x, f₂ (-x) = -f₂ x) (M₁ M₂ : ℝ)
    (hM₁ : ∀ x, |f₁ x| ≤ M₁) (hM₂ : ∀ x, |f₂ x| ≤ M₂) (K H : Mat m n) :
    |contraction B F G f₁ f₂ K H| ≤ γ * M₁ * M₂ := by
  have h0 : IsOddBddLip (fun _ : ℝ => (0 : ℝ)) := ⟨fun x => by simp, ⟨0, fun x => by simp⟩, ⟨0, fun x y => by simp⟩⟩
  have hM₁0 : 0 ≤ M₁ := (abs_nonneg _).trans (hM₁ 0)
  have hM₂0 : 0 ≤ M₂ := (abs_nonneg _).trans (hM₂ 0)
  obtain ⟨g₁, hg₁, he₁, hb₁⟩ := tx_oddSharp_lip f₁ _ hf₁ h0 K (opNorm K) M₁ hM₁0 le_rfl
    (fun x _ => by simpa using hM₁ x)
  obtain ⟨g₂, hg₂, he₂, hb₂⟩ := tx_oddSharp_lip f₂ _ hf₂ h0 H (opNorm H) M₂ hM₂0 le_rfl
    (fun x _ => by simpa using hM₂ x)
  have e : contraction B F G f₁ f₂ K H = contraction B F G g₁ g₂ K H := by
    unfold contraction; rw [he₁, he₂]
  rw [e]
  refine (lem_app_vol_finite_i hB γ hdim F G hF hG g₁ g₂ hg₁ hg₂ K H).trans ?_
  have hBpos : (0 : ℝ) < B := by exact_mod_cast hB
  have hγ : 0 ≤ γ := by
    by_contra h
    push Not at h
    have : γ * B < 0 := mul_neg_of_neg_of_pos h hBpos
    have h0 : (0 : ℝ) ≤ ((min m n : ℕ) : ℝ) := Nat.cast_nonneg _
    linarith
  have s1 : supNorm g₁ ≤ M₁ := tx_supNorm_le _ _ hM₁0 fun x => by simpa using hb₁ x
  have s2 : supNorm g₂ ≤ M₂ := tx_supNorm_le _ _ hM₂0 fun x => by simpa using hb₂ x
  have n1 := tx_supNorm_nonneg g₁
  have n2 := tx_supNorm_nonneg g₂
  calc γ * supNorm g₁ * supNorm g₂ ≤ γ * M₁ * M₂ :=
        mul_le_mul (mul_le_mul_of_nonneg_left s1 hγ) s2 n2 (mul_nonneg hγ hM₁0)

private lemma tx_oddSharp_zero {m n : ℕ} (f : ℝ → ℝ) (hf : ∀ x, f (-x) = -f x) :
    oddSharp f (0 : Mat m n) = 0 := by
  have h0 : f 0 = 0 := by have := hf 0; simp at this; linarith
  have hop : opNorm (0 : Mat m n) ≤ 0 := by unfold opNorm; simp
  rw [tx_oddSharp_congr f (fun _ => 0) (0 : Mat m n) 0 hop (fun x hx => by
    have : x = 0 := by
      have := hx.1; have := hx.2; simp at *; linarith
    subst this; simpa using h0)]
  unfold oddSharp
  have hz : cfc (fun _ : ℝ => (0 : ℝ)) (Muon.Foundations.hermDilation (0 : Mat m n)) = 0 := cfc_zero ℝ _
  rw [hz]
  ext i j
  simp [Muon.Foundations.upperRight]

private lemma tx_cutoffMat_nonpos {m n B : ℕ} (Fp : FrozenParams m n B) (ℓ J : ℕ) (R : ℝ)
    (hR : R ≤ 0) (t : ℤ) (l : ℕ) (ω : (ℤ × Fin B) → ℝ × (Vec m × Vec n)) :
    cutoffMat Fp ℓ J R t l ω = 0 := by
  unfold cutoffMat
  have : ∀ x : ℝ, (if |x| ≤ R then x else 0) = 0 := fun x => by
    split_ifs with h
    · have : x = 0 := abs_eq_zero.mp (le_antisymm (h.trans hR) (abs_nonneg x))
      exact this
    · rfl
  simp [this]

private lemma tx_nonpos_case (cert : Muon.External.GaussianOpNorm) (γstar CSig : ℝ)
    {m n B : ℕ} (Fp : FrozenParams m n B) (S : SpectralData Fp.C) (ℓ J : ℕ) (R : ℝ) (hR : R ≤ 0)
    (Fd : Fin m → ℝ) (Gd : Fin n → ℝ) (Fm : Mat m m) (Gm : Mat n n) (f₁ f₂ : ℝ → ℝ)
    (h₁ : ∀ x, f₁ (-x) = -f₁ x) (h₂ : ∀ x, f₂ (-x) = -f₂ x) (t : ℤ) :
    (∫ ω, contraction B Fm Gm f₁ f₂ (cutoffMat Fp ℓ J R t 1 ω) (cutoffMat Fp ℓ J R t 2 ω)
        ∂(indepSpaceLaw m n B)) = 0 ∧
      lagRespCut cert γstar CSig Fp.β ℓ J R B S.μ S.lam Fd Gd f₁ f₂ = 0 := by
  refine ⟨?_, ?_⟩
  · have : ∀ ω : (ℤ × Fin B) → ℝ × (Vec m × Vec n),
        contraction B Fm Gm f₁ f₂ (cutoffMat Fp ℓ J R t 1 ω) (cutoffMat Fp ℓ J R t 2 ω) = 0 := by
      intro ω
      unfold contraction
      rw [tx_cutoffMat_nonpos Fp ℓ J R hR t 1 ω, tx_cutoffMat_nonpos Fp ℓ J R hR t 2 ω,
        tx_oddSharp_zero f₁ h₁, tx_oddSharp_zero f₂ h₂]
      simp
    simp [this]
  · unfold lagRespCut treeRespExt
    have : (fun k : ℕ => def_app_vol_tree Fp.β ℓ J R B S.μ S.lam Fd Gd
        (treeApprox (volDR cert R CSig γstar) f₁ k) (treeApprox (volDR cert R CSig γstar) f₂ k)) =
        fun _ => 0 := funext fun k => tx_tree_zero_of_nonpos _ _ _ _ hR _ _ _ _ _ _ _
    rw [this]
    exact (tendsto_const_nhds (x := (0 : ℝ))).limUnder_eq

private lemma tx_shift_cutoff {m n B : ℕ} (Fp : FrozenParams m n B) (ℓ J : ℕ) (R : ℝ) (t : ℤ)
    (Ψ : Mat m n → Mat m n → ℝ) :
    ∫ ω, Ψ (cutoffMat Fp ℓ J R t 1 ω) (cutoffMat Fp ℓ J R t 2 ω) ∂(indepSpaceLaw m n B) =
    ∫ ω, Ψ (cutoffMat Fp ℓ J R 0 1 ω) (cutoffMat Fp ℓ J R 0 2 ω) ∂(indepSpaceLaw m n B) := by
  let e : (ℤ × Fin B) ≃ (ℤ × Fin B) := Equiv.prodCongr (Equiv.addRight t) (Equiv.refl _)
  let σ : ((ℤ × Fin B) → ℝ × (Vec m × Vec n)) ≃ᵐ ((ℤ × Fin B) → ℝ × (Vec m × Vec n)) :=
    MeasurableEquiv.piCongrLeft (fun _ : ℤ × Fin B => ℝ × (Vec m × Vec n)) e.symm
  have hmap : (indepSpaceLaw m n B).map σ = indepSpaceLaw m n B := by
    unfold indepSpaceLaw
    exact Measure.infinitePi_map_piCongrLeft (μ := fun _ : ℤ × Fin B => indepSlotLaw m n) e.symm
  have hσ : MeasurePreserving σ (indepSpaceLaw m n B) (indepSpaceLaw m n B) := ⟨σ.measurable, hmap⟩
  have hc : ∀ l ω, cutoffMat Fp ℓ J R t l ω = cutoffMat Fp ℓ J R 0 l (σ ω) := by
    intro l ω
    unfold cutoffMat
    have hσω : ∀ p : ℤ × Fin B, σ ω p = ω (e p) := fun p => by
      simp [σ, MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply]
    simp only [hσω, e, Equiv.prodCongr_apply, Prod.map_apply, Equiv.coe_addRight, Equiv.refl_apply]
    congr 1
    refine Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun a _ => ?_
    have : (0 : ℤ) + 1 + α + t = t + 1 + α := by ring
    rw [this]
  simp only [hc]
  exact hσ.integral_comp' (f := σ) (g := fun ω => Ψ (cutoffMat Fp ℓ J R 0 1 ω) (cutoffMat Fp ℓ J R 0 2 ω))

private lemma tx_fro_cont {m n : ℕ} : Continuous (fun K : Mat m n => fro K) := by
  unfold fro
  refine Real.continuous_sqrt.comp (continuous_finset_sum _ fun i _ => continuous_finset_sum _ fun j _ => ?_)
  have : Continuous fun K : Mat m n => K i j :=
    (continuous_apply j).comp (continuous_apply i)
  exact (continuous_norm.comp this).pow 2

private lemma tx_contr_cont_lip {m n B : ℕ} (hB : 0 < B) (γstar : ℝ)
    (hdim : ((min m n : ℕ) : ℝ) ≤ γstar * B)
    (F : Matrix (Fin m) (Fin m) ℝ) (G : Matrix (Fin n) (Fin n) ℝ)
    (hF : opNorm F ≤ 1) (hG : opNorm G ≤ 1)
    (f g : ℝ → ℝ) (hf : IsOddBddLip f) (hg : IsOddBddLip g) :
    Continuous (fun p : Mat m n × Mat m n => contraction B F G f g p.1 p.2) := by
  rw [continuous_iff_continuousAt]
  intro p
  rw [ContinuousAt, tendsto_iff_dist_tendsto_zero]
  have hb : Continuous fun q : Mat m n × Mat m n =>
      Real.sqrt (γstar / B) * (lipConst f * supNorm g * fro (q.1 - p.1) +
        supNorm f * lipConst g * fro (q.2 - p.2)) := by
    have h1 : Continuous fun q : Mat m n × Mat m n => fro (q.1 - p.1) :=
      tx_fro_cont.comp (continuous_fst.sub continuous_const)
    have h2 : Continuous fun q : Mat m n × Mat m n => fro (q.2 - p.2) :=
      tx_fro_cont.comp (continuous_snd.sub continuous_const)
    exact continuous_const.mul ((continuous_const.mul h1).add (continuous_const.mul h2))
  have h0 := hb.tendsto p
  have hz : fro (p.1 - p.1) = 0 ∧ fro (p.2 - p.2) = 0 := by simp [fro]
  rw [hz.1, hz.2] at h0
  simp only [mul_zero, add_zero, zero_add] at h0
  refine squeeze_zero (fun q => dist_nonneg) (fun q => ?_) h0
  rw [Real.dist_eq]
  exact lem_app_vol_finite_ii hB γstar hdim F G hF hG f g hf hg q.1 p.1 q.2 p.2

private lemma tx_odd_approx (D : ℝ) (hD : 0 ≤ D) (f : ℝ → ℝ) (hf : ContinuousOn f (Set.Icc (-D) D))
    (hodd : ∀ x, f (-x) = -f x) (k : ℕ) :
    ∃ Q : Polynomial ℝ, (∀ x, Q.eval (-x) = -Q.eval x) ∧
      (∀ x ∈ Set.Icc (-D) D, |Q.eval x - f x| ≤ 1 / ((k : ℝ) + 1)) ∧
      (∀ a, Q.coeff (2 * a + 1) = (treeApprox D f k).coeff (2 * a + 1)) := by
  obtain ⟨Q, hQ1, hQ2, -⟩ := tx_oddPart (treeApprox D f k)
  refine ⟨Q, fun x => ?_, fun x hx => ?_, fun a => hQ2 a⟩
  · rw [hQ1, hQ1]; simp only [neg_neg]; ring
  · have a1 := tx_treeApprox_spec D f hf k x hx
    have a2 := tx_treeApprox_spec D f hf k (-x) ⟨by linarith [hx.2], by linarith [hx.1]⟩
    rw [hQ1]
    have e : (((treeApprox D f k).eval x - (treeApprox D f k).eval (-x)) / 2 - f x) =
        (((treeApprox D f k).eval x - f x) - ((treeApprox D f k).eval (-x) - f (-x))) / 2 := by
      rw [hodd x]; ring
    rw [e, abs_div, abs_two, div_le_iff₀ (by norm_num)]
    have := abs_sub ((treeApprox D f k).eval x - f x) ((treeApprox D f k).eval (-x) - f (-x))
    linarith

private lemma tx_meas_contr {m n B : ℕ} (hB : 0 < B)
    (F : Matrix (Fin m) (Fin m) ℝ) (G : Matrix (Fin n) (Fin n) ℝ)
    (hF : opNorm F ≤ 1) (hG : opNorm G ≤ 1) (f₁ f₂ : ℝ → ℝ)
    (hc₁ : Continuous f₁) (hc₂ : Continuous f₂) (ho₁ : ∀ x, f₁ (-x) = -f₁ x)
    (ho₂ : ∀ x, f₂ (-x) = -f₂ x) (M₁ M₂ : ℝ) (hb₁ : ∀ x, |f₁ x| ≤ M₁) (hb₂ : ∀ x, |f₂ x| ≤ M₂) :
    Measurable (fun p : Mat m n × Mat m n => contraction B F G f₁ f₂ p.1 p.2) := by
  have hBpos : (0 : ℝ) < B := by exact_mod_cast hB
  set γ : ℝ := ((min m n : ℕ) : ℝ) / B with hγ
  have hdim : ((min m n : ℕ) : ℝ) ≤ γ * B := by
    rw [hγ, div_mul_cancel₀ _ hBpos.ne']
  have hγ0 : 0 ≤ γ := div_nonneg (Nat.cast_nonneg _) hBpos.le
  have hM₁0 : 0 ≤ M₁ := (abs_nonneg _).trans (hb₁ 0)
  have hM₂0 : 0 ≤ M₂ := (abs_nonneg _).trans (hb₂ 0)
  have key : ∀ (f : ℝ → ℝ) (hc : Continuous f) (ho : ∀ x, f (-x) = -f x) (M : ℝ) (hb : ∀ x, |f x| ≤ M)
      (N : ℕ), ∃ p : ℝ → ℝ, IsOddBddLip p ∧ (∀ x ∈ Set.Icc (-(N : ℝ)) N, |f x - p x| ≤ 1 / ((N : ℝ) + 1)) ∧
        supNorm p ≤ M + 1 := by
    intro f hc ho M hb N
    have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    obtain ⟨Q, hQo, hQc, -⟩ := tx_odd_approx (N : ℝ) hN f hc.continuousOn ho N
    refine ⟨fun x => Q.eval (max (-(N : ℝ)) (min (N : ℝ) x)), tx_clampPoly_isOddBddLip Q hQo N hN,
      fun x hx => ?_, ?_⟩
    · show |f x - Q.eval (max (-(N : ℝ)) (min (N : ℝ) x))| ≤ _
      rw [tx_clamp_self (N : ℝ) x (abs_le.mpr hx), abs_sub_comm]
      exact hQc x hx
    · refine (tx_clampPoly_supNorm Q N hN).trans (tx_supOn_le _ _ _ (by
        have : 0 ≤ M := (abs_nonneg _).trans (hb 0)
        linarith) fun x hx => ?_)
      have h1 := hQc x hx
      have h2 := hb x
      have h3 : 1 / ((N : ℝ) + 1) ≤ 1 := by
        rw [div_le_one (by positivity)]; linarith
      calc |Q.eval x| = |f x + (Q.eval x - f x)| := by ring_nf
        _ ≤ |f x| + |Q.eval x - f x| := abs_add_le _ _
        _ ≤ M + 1 := by linarith
  choose p₁ hp₁ hcl₁ hs₁ using key f₁ hc₁ ho₁ M₁ hb₁
  choose p₂ hp₂ hcl₂ hs₂ using key f₂ hc₂ ho₂ M₂ hb₂
  refine measurable_of_tendsto_metrizable (f := fun N (p : Mat m n × Mat m n) =>
    contraction B F G (p₁ N) (p₂ N) p.1 p.2)
    (fun N => (tx_contr_cont_lip hB γ hdim F G hF hG _ _ (hp₁ N) (hp₂ N)).measurable) ?_
  rw [tendsto_pi_nhds]
  intro p
  rw [tendsto_iff_dist_tendsto_zero]
  have hlim : Tendsto (fun N : ℕ => γ * ((1 / ((N : ℝ) + 1)) * (2 * M₁ + 2 * M₂ + 4))) atTop (𝓝 0) := by
    have := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).mul_const (2 * M₁ + 2 * M₂ + 4)
    simpa using this.const_mul γ
  refine squeeze_zero' (Eventually.of_forall fun N => dist_nonneg) ?_ hlim
  filter_upwards [eventually_ge_atTop (⌈max (opNorm p.1) (opNorm p.2)⌉₊)] with N hN
  have hK : opNorm p.1 ≤ N := (le_max_left _ _).trans ((Nat.le_ceil _).trans (by exact_mod_cast hN))
  have hH : opNorm p.2 ≤ N := (le_max_right _ _).trans ((Nat.le_ceil _).trans (by exact_mod_cast hN))
  rw [Real.dist_eq]
  have hcmp := tx_contr_cmp hB γ hdim F G hF hG f₁ f₂ (p₁ N) (p₂ N) ho₁ ho₂ (hp₁ N) (hp₂ N) p.1 p.2
    N N _ _ (by positivity) (by positivity) hK hH (hcl₁ N) (hcl₂ N)
  rw [abs_sub_comm] at hcmp
  refine hcmp.trans ?_
  refine mul_le_mul_of_nonneg_left ?_ hγ0
  have ha : 1 / ((N : ℝ) + 1) ≤ 1 := by
    rw [div_le_one (by positivity)]; linarith [(Nat.cast_nonneg N : (0 : ℝ) ≤ N)]
  have ha0 : 0 ≤ 1 / ((N : ℝ) + 1) := by positivity
  have s1 := hs₁ N
  have s2 := hs₂ N
  have n1 := tx_supNorm_nonneg (p₁ N)
  have n2 := tx_supNorm_nonneg (p₂ N)
  nlinarith [mul_le_mul_of_nonneg_left (add_le_add s2 ha) ha0, mul_le_mul_of_nonneg_left s1 ha0]

private lemma tx_cont_of_lip (f : ℝ → ℝ) (hf : IsOddBddLip f) : Continuous f := by
  obtain ⟨_, _, ⟨L, hL⟩⟩ := hf
  have : LipschitzWith (Real.toNNReal L) f := by
    refine LipschitzWith.of_dist_le' fun x y => ?_
    have h0 : 0 ≤ L := by
      have := hL 1 0
      norm_num at this
      linarith [abs_nonneg (f 1 - f 0)]
    simp only [Real.dist_eq, Real.coe_toNNReal _ h0]
    exact hL x y
  exact this.continuous

private lemma tx_integrable_contr {m n B : ℕ} (Fp : FrozenParams m n B) (ℓ J : ℕ) (R : ℝ) (t : ℤ)
    (γ : ℝ) (hdim : ((min m n : ℕ) : ℝ) ≤ γ * B)
    (F : Matrix (Fin m) (Fin m) ℝ) (G : Matrix (Fin n) (Fin n) ℝ)
    (hF : opNorm F ≤ 1) (hG : opNorm G ≤ 1) (f₁ f₂ : ℝ → ℝ)
    (hc₁ : Continuous f₁) (hc₂ : Continuous f₂) (ho₁ : ∀ x, f₁ (-x) = -f₁ x)
    (ho₂ : ∀ x, f₂ (-x) = -f₂ x) (M₁ M₂ : ℝ) (hb₁ : ∀ x, |f₁ x| ≤ M₁) (hb₂ : ∀ x, |f₂ x| ≤ M₂) :
    Integrable (fun ω : (ℤ × Fin B) → ℝ × (Vec m × Vec n) =>
      contraction B F G f₁ f₂ (cutoffMat Fp ℓ J R t 1 ω) (cutoffMat Fp ℓ J R t 2 ω))
      (indepSpaceLaw m n B) := by
  haveI : IsProbabilityMeasure (indepSpaceLaw m n B) := by
    unfold indepSpaceLaw; infer_instance
  have hmeas := (tx_meas_contr Fp.hB F G hF hG f₁ f₂ hc₁ hc₂ ho₁ ho₂ M₁ M₂ hb₁ hb₂).comp
    ((tx_meas_cutoffMat Fp ℓ J R t 1).prodMk (tx_meas_cutoffMat Fp ℓ J R t 2))
  exact Integrable.of_bound hmeas.aestronglyMeasurable (γ * M₁ * M₂)
    (Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs]
      exact tx_contr_bdd Fp.hB γ hdim F G hF hG f₁ f₂ ho₁ ho₂ M₁ M₂ hb₁ hb₂ _ _)

private lemma tx_ext_approx (cert : Muon.External.GaussianOpNorm) (γstar CSig : ℝ)
    {m n B : ℕ} (Fp : FrozenParams m n B) (S : SpectralData Fp.C) (hS : SizeFin Fp.C B γstar CSig)
    (ℓ J : ℕ) (R : ℝ) (D : ℝ) (hD : volDR cert R CSig γstar ≤ D) (f g : ℝ → ℝ)
    (hfc : ContinuousOn f (Set.Icc (-D) D)) (hgc : ContinuousOn g (Set.Icc (-D) D))
    (Fd : Fin m → ℝ) (Gd : Fin n → ℝ)
    (hF : opNorm (S.uOut * Matrix.diagonal Fd * S.uOutᵀ) ≤ 1)
    (hG : opNorm (S.vIn * Matrix.diagonal Gd * S.vInᵀ) ≤ 1) (j : ℕ) :
    |def_app_vol_tree Fp.β ℓ J R B S.μ S.lam Fd Gd (treeApprox D f j) (treeApprox D g j) -
        treeRespExt Fp.β ℓ J R B S.μ S.lam Fd Gd D f g| ≤
      γstar * (1 / ((j : ℝ) + 1)) * (supOn D f + supOn D g + 2) := by
  have hl := tx_ext_lim cert γstar CSig Fp S hS ℓ J R D hD f g hfc hgc Fd Gd
  have hγ := tx_gamma_nonneg Fp γstar CSig hS
  set T : Polynomial ℝ → Polynomial ℝ → ℝ :=
    fun P Q => def_app_vol_tree Fp.β ℓ J R B S.μ S.lam Fd Gd P Q with hT
  have hL := fun P P' Q (c : ℝ) => tx_tree_lin_left Fp.β ℓ J R B S.μ S.lam Fd Gd P P' Q c
  have hR := fun P Q Q' (c : ℝ) => tx_tree_lin_right Fp.β ℓ J R B S.μ S.lam Fd Gd Q Q' P c
  have hB : ∀ P Q, |T P Q| ≤ γstar * supOn D (fun x => P.eval x) * supOn D (fun x => Q.eval x) :=
    fun P Q => tx_K1 cert γstar CSig Fp S hS ℓ J R Fd Gd hF hG D hD P Q
  have hd : ∀ k : ℕ, 0 ≤ 1 / ((k : ℝ) + 1) := fun k => by positivity
  have hd1 : ∀ k : ℕ, 1 / ((k : ℝ) + 1) ≤ 1 := fun k => by
    rw [div_le_one (by positivity)]; linarith [(Nat.cast_nonneg k : (0:ℝ) ≤ k)]
  have sP : ∀ k, supOn D (fun x => (treeApprox D f k).eval x) ≤ supOn D f + 1 := fun k =>
    (tx_sup_near D _ f hfc _ (hd k) (tx_treeApprox_spec D f hfc k)).trans (by linarith [hd1 k])
  have sQ : ∀ k, supOn D (fun x => (treeApprox D g k).eval x) ≤ supOn D g + 1 := fun k =>
    (tx_sup_near D _ g hgc _ (hd k) (tx_treeApprox_spec D g hgc k)).trans (by linarith [hd1 k])
  have hbd : ∀ k : ℕ, |T (treeApprox D f j) (treeApprox D g j) - T (treeApprox D f k) (treeApprox D g k)| ≤
      γstar * ((1 / ((j : ℝ) + 1) + 1 / ((k : ℝ) + 1)) * (supOn D g + 1) +
        (supOn D f + 1) * (1 / ((j : ℝ) + 1) + 1 / ((k : ℝ) + 1))) := by
    intro k
    refine (tx_abs_diff T γstar D hL hR hB _ _ _ _).trans ?_
    refine mul_le_mul_of_nonneg_left (add_le_add ?_ ?_) hγ
    · have s1 := tx_sup_diff D (treeApprox D f j) (treeApprox D f k)
        (1 / ((j : ℝ) + 1) + 1 / ((k : ℝ) + 1)) (add_nonneg (hd j) (hd k))
        (fun x hx => by
          have a := tx_treeApprox_spec D f hfc j x hx; have b := tx_treeApprox_spec D f hfc k x hx
          calc |(treeApprox D f j).eval x - (treeApprox D f k).eval x| =
              |((treeApprox D f j).eval x - f x) - ((treeApprox D f k).eval x - f x)| := by ring_nf
            _ ≤ _ := (abs_sub _ _).trans (add_le_add a b))
      exact mul_le_mul s1 (sQ j) (tx_supOn_nonneg _ _) (add_nonneg (hd j) (hd k))
    · have s2 := tx_sup_diff D (treeApprox D g j) (treeApprox D g k)
        (1 / ((j : ℝ) + 1) + 1 / ((k : ℝ) + 1)) (add_nonneg (hd j) (hd k))
        (fun x hx => by
          have a := tx_treeApprox_spec D g hgc j x hx; have b := tx_treeApprox_spec D g hgc k x hx
          calc |(treeApprox D g j).eval x - (treeApprox D g k).eval x| =
              |((treeApprox D g j).eval x - g x) - ((treeApprox D g k).eval x - g x)| := by ring_nf
            _ ≤ _ := (abs_sub _ _).trans (add_le_add a b))
      exact mul_le_mul (sP k) s2 (tx_supOn_nonneg _ _) (by linarith [tx_supOn_nonneg D f])
  have hδt : Tendsto (fun k : ℕ => 1 / ((k : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hb2 : Tendsto (fun k : ℕ => γstar * ((1 / ((j : ℝ) + 1) + 1 / ((k : ℝ) + 1)) * (supOn D g + 1) +
        (supOn D f + 1) * (1 / ((j : ℝ) + 1) + 1 / ((k : ℝ) + 1)))) atTop
      (𝓝 (γstar * ((1 / ((j : ℝ) + 1) + 0) * (supOn D g + 1) +
        (supOn D f + 1) * (1 / ((j : ℝ) + 1) + 0)))) :=
    (((tendsto_const_nhds.add hδt).mul_const _).add (tendsto_const_nhds.mul (tendsto_const_nhds.add hδt))).const_mul γstar
  have h1 : Tendsto (fun k : ℕ => |T (treeApprox D f j) (treeApprox D g j) -
      T (treeApprox D f k) (treeApprox D g k)|) atTop
      (𝓝 |T (treeApprox D f j) (treeApprox D g j) - treeRespExt Fp.β ℓ J R B S.μ S.lam Fd Gd D f g|) :=
    (tendsto_const_nhds.sub hl).abs
  refine le_of_tendsto_of_tendsto h1 hb2 (Eventually.of_forall hbd) |>.trans (le_of_eq ?_)
  ring

private lemma tx_Ecompl_tendsto {mm nn BB : ℕ → ℕ} (cert : Muon.External.GaussianOpNorm)
    (γstar CSig : ℝ) (ℓ J : ℕ) (Fp : ∀ k, FrozenParams (mm k) (nn k) (BB k))
    (hB : Tendsto BB atTop atTop) (hS : ∀ k, SizeFin (Fp k).C (BB k) γstar CSig) :
    Tendsto (fun k => indepSpaceLaw (mm k) (nn k) (BB k)
      (cutoffEvent cert (mm k) (nn k) (BB k) ℓ J γstar 0)ᶜ) atTop (𝓝 0) := by
  have hexp : Tendsto (fun k => ENNReal.ofReal (4 * ((Finset.Icc (-(J : ℤ)) (ℓ : ℤ)).card : ℝ) *
      Real.exp (-(BB k : ℝ)))) atTop (𝓝 0) := by
    have : Tendsto (fun k => 4 * ((Finset.Icc (-(J : ℤ)) (ℓ : ℤ)).card : ℝ) *
        Real.exp (-(BB k : ℝ))) atTop (𝓝 0) := by
      have := (Real.tendsto_exp_neg_atTop_nhds_zero.comp
        (tendsto_natCast_atTop_atTop.comp hB)).const_mul (4 * ((Finset.Icc (-(J : ℤ)) (ℓ : ℤ)).card : ℝ))
      simpa using this
    simpa using ENNReal.tendsto_ofReal this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hexp (fun k => zero_le) (fun k => ?_)
  exact lem_app_vol_norm_i cert ℓ J γstar CSig (Fp k).C (hS k) 0

private lemma tx_poly_growth (γ : ℝ) (hγ : 0 ≤ γ) (f₁ f₂ : Polynomial ℝ)
    (hf₁ : ∀ x : ℝ, f₁.eval (-x) = -f₁.eval x) (hf₂ : ∀ x : ℝ, f₂.eval (-x) = -f₂.eval x) :
    ∃ c0 : ℝ, 0 ≤ c0 ∧ ∀ {m n B : ℕ} (hB : 0 < B) (hdim : ((min m n : ℕ) : ℝ) ≤ γ * B)
      (F : Matrix (Fin m) (Fin m) ℝ) (G : Matrix (Fin n) (Fin n) ℝ)
      (hF : opNorm F ≤ 1) (hG : opNorm G ≤ 1) (K H : Mat m n),
      |contraction B F G (fun x => f₁.eval x) (fun x => f₂.eval x) K H| ≤
        c0 * (2 + opNorm K ^ (f₁.natDegree + f₂.natDegree + 1) +
          opNorm H ^ (f₁.natDegree + f₂.natDegree + 1)) := by
  set d₁ := f₁.natDegree with hd₁
  set d₂ := f₂.natDegree with hd₂
  set C₁ := ∑ i ∈ Finset.range (d₁ + 1), |f₁.coeff i| with hC₁
  set C₂ := ∑ i ∈ Finset.range (d₂ + 1), |f₂.coeff i| with hC₂
  have hC₁0 : 0 ≤ C₁ := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hC₂0 : 0 ≤ C₂ := Finset.sum_nonneg fun _ _ => abs_nonneg _
  refine ⟨γ * C₁ * C₂ * 2 ^ (d₁ + d₂), by positivity, ?_⟩
  intro m n B hB hdim F G hF hG K H
  have h1 := tx_contraction_poly_bound hB γ hγ hdim F G hF hG f₁ f₂ hf₁ hf₂ K H _ _ le_rfl le_rfl
  refine h1.trans ?_
  set ρ₁ := opNorm K
  set ρ₂ := opNorm H
  have hρ₁ : 0 ≤ ρ₁ := tx_opNorm_nonneg _
  have hρ₂ : 0 ≤ ρ₂ := tx_opNorm_nonneg _
  have b1 := tx_supOn_poly_le f₁ ρ₁ hρ₁
  have b2 := tx_supOn_poly_le f₂ ρ₂ hρ₂
  have b3 := tx_prod_bound ρ₁ ρ₂ hρ₁ hρ₂ d₁ d₂
  calc γ * supOn ρ₁ (fun x => f₁.eval x) * supOn ρ₂ (fun x => f₂.eval x)
      ≤ γ * (C₁ * (1 + ρ₁) ^ d₁) * (C₂ * (1 + ρ₂) ^ d₂) := by
        apply mul_le_mul (mul_le_mul_of_nonneg_left b1 hγ) b2 (tx_supOn_nonneg _ _)
        exact mul_nonneg hγ (mul_nonneg hC₁0 (by positivity))
    _ = γ * C₁ * C₂ * ((1 + ρ₁) ^ d₁ * (1 + ρ₂) ^ d₂) := by ring
    _ ≤ γ * C₁ * C₂ * (2 ^ (d₁ + d₂) * (2 + ρ₁ ^ (d₁ + d₂ + 1) + ρ₂ ^ (d₁ + d₂ + 1))) :=
        mul_le_mul_of_nonneg_left b3 (by positivity)
    _ = _ := by ring

private lemma tx_iii_core (cert : Muon.External.GaussianOpNorm) (γstar CSig γout γin : ℝ)
    (m n B : ℕ → ℕ) (Fp : ∀ k : ℕ, FrozenParams (m k) (n k) (B k))
    (Sp : ∀ k : ℕ, SpectralData (Fp k).C)
    (hSize : SizeSeq (B := B) (fun k => (Fp k).C) γstar CSig γout γin)
    (ℓ J : ℕ) (R : ℝ) (hR : 0 < R) (f₁ f₂ : ℝ → ℝ)
    (hf₁c : Continuous f₁) (hf₁o : ∀ x, f₁ (-x) = -f₁ x) (hf₁b : ∃ M : ℝ, ∀ x, |f₁ x| ≤ M)
    (hf₂c : Continuous f₂) (hf₂o : ∀ x, f₂ (-x) = -f₂ x) (hf₂b : ∃ M : ℝ, ∀ x, |f₂ x| ≤ M) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, ∀ (Fd : Fin (m k) → ℝ) (Gd : Fin (n k) → ℝ),
      opNorm ((Sp k).uOut * Matrix.diagonal Fd * (Sp k).uOutᵀ) ≤ 1 →
      opNorm ((Sp k).vIn * Matrix.diagonal Gd * (Sp k).vInᵀ) ≤ 1 →
      |(∫ ω, contraction (B k) ((Sp k).uOut * Matrix.diagonal Fd * (Sp k).uOutᵀ)
            ((Sp k).vIn * Matrix.diagonal Gd * (Sp k).vInᵀ) f₁ f₂
            (cutoffMat (Fp k) ℓ J R 0 1 ω) (cutoffMat (Fp k) ℓ J R 0 2 ω)
          ∂(indepSpaceLaw (m k) (n k) (B k))) -
        lagRespCut cert γstar CSig (Fp k).β ℓ J R (B k) (Sp k).μ (Sp k).lam Fd Gd f₁ f₂| ≤ ε := by
  intro ε hε
  obtain ⟨M₁, hM₁⟩ := hf₁b
  obtain ⟨M₂, hM₂⟩ := hf₂b
  have hM₁0 : 0 ≤ M₁ := (abs_nonneg _).trans (hM₁ 0)
  have hM₂0 : 0 ≤ M₂ := (abs_nonneg _).trans (hM₂ 0)
  have hγ0 : 0 ≤ γstar := tx_gamma_nonneg (Fp 0) γstar CSig (hSize.1 0)
  have hCS : 0 ≤ CSig := (tx_opNorm_nonneg _).trans (hSize.1 0).2.1
  set D := volDR cert R CSig γstar with hDdef
  have hD0 : 0 ≤ D := by
    rw [hDdef]; unfold volDR
    exact mul_nonneg (mul_nonneg hR.le hCS) (sq_nonneg _)
  set K0 : ℝ := M₁ + M₂ + 3 with hK0
  have hK0pos : 0 < K0 := by rw [hK0]; linarith
  obtain ⟨j, hj⟩ := exists_nat_one_div_lt (show 0 < ε / (4 * (γstar + 1) * K0) by positivity)
  set a : ℝ := 1 / ((j : ℝ) + 1) with ha
  have ha0 : 0 ≤ a := by rw [ha]; positivity
  have ha1 : a ≤ 1 := by
    rw [ha, div_le_one (by positivity)]; linarith [(Nat.cast_nonneg j : (0:ℝ) ≤ j)]
  have hκ : γstar * a * K0 < ε / 4 := by
    have h1 : a * (4 * (γstar + 1) * K0) < ε := by
      rw [lt_div_iff₀ (by positivity)] at hj
      exact hj
    nlinarith [mul_nonneg hγ0 (mul_nonneg ha0 hK0pos.le), mul_pos hK0pos hK0pos, mul_nonneg ha0 hK0pos.le]
  obtain ⟨P₁, hP₁o, hP₁c, hP₁k⟩ := tx_odd_approx D hD0 f₁ hf₁c.continuousOn hf₁o j
  obtain ⟨P₂, hP₂o, hP₂c, hP₂k⟩ := tx_odd_approx D hD0 f₂ hf₂c.continuousOn hf₂o j
  obtain ⟨A, hA⟩ := tx_moment γstar CSig ℓ J R hR P₁ P₂ hP₁o hP₂o
  obtain ⟨c0, hc0, hgrow⟩ := tx_poly_growth γstar hγ0 P₁ P₂ hP₁o hP₂o
  -- the tail
  have htail : Tendsto (fun k => ∫⁻ ω in (cutoffEvent cert (m k) (n k) (B k) ℓ J γstar 0)ᶜ,
      (ENNReal.ofReal (γstar * M₁ * M₂) + ENNReal.ofReal (c0 * (2 +
        opNorm (cutoffMat (Fp k) ℓ J R 0 1 ω) ^ (P₁.natDegree + P₂.natDegree + 1) +
        opNorm (cutoffMat (Fp k) ℓ J R 0 2 ω) ^ (P₁.natDegree + P₂.natDegree + 1))))
        ∂(indepSpaceLaw (m k) (n k) (B k))) atTop (𝓝 0) := by
    have h1 := ENNReal.Tendsto.const_mul
      (tx_Ecompl_tendsto cert γstar CSig ℓ J Fp hSize.2.1 hSize.1)
      (Or.inr ENNReal.ofReal_ne_top : (0 : ℝ≥0∞) ≠ 0 ∨ ENNReal.ofReal (γstar * M₁ * M₂) ≠ ⊤)
    have h2 := tx_tail cert γstar CSig ℓ J R hR Fp hSize.2.1 hSize.1 (P₁.natDegree + P₂.natDegree) c0 hc0
    have h3 := h1.add h2
    simp only [mul_zero, add_zero] at h3
    refine h3.congr fun k => ?_
    rw [lintegral_add_left measurable_const, lintegral_const, Measure.restrict_apply_univ]
  have ev1 := (tendsto_order.1 htail).2 (ENNReal.ofReal (ε / 4)) (ENNReal.ofReal_pos.mpr (by positivity))
  have ev2 : ∀ᶠ k : ℕ in atTop, A / (B k : ℝ) < ε / 4 := by
    have : Tendsto (fun k : ℕ => A / (B k : ℝ)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.comp hSize.2.1)
    exact (tendsto_order.1 this).2 _ (by positivity)
  filter_upwards [ev1, ev2] with k hk1 hk2
  intro Fd Gd hF hG
  set Fm := (Sp k).uOut * Matrix.diagonal Fd * (Sp k).uOutᵀ with hFm
  set Gm := (Sp k).vIn * Matrix.diagonal Gd * (Sp k).vInᵀ with hGm
  haveI : IsProbabilityMeasure (indepSpaceLaw (m k) (n k) (B k)) := by
    unfold indepSpaceLaw; infer_instance
  have hdim : ((min (m k) (n k) : ℕ) : ℝ) ≤ γstar * (B k : ℝ) :=
    le_trans (by exact_mod_cast min_le_max) (hSize.1 k).1
  have hintf := tx_integrable_contr (Fp k) ℓ J R 0 γstar hdim Fm Gm hF hG f₁ f₂ hf₁c hf₂c hf₁o hf₂o
    M₁ M₂ hM₁ hM₂
  obtain ⟨hintP, hbdP⟩ := hA (m k) (n k) (B k) (Fp k) (Sp k) Fd Gd Fm Gm (hSize.1 k) rfl rfl hF hG
  -- clamped polynomials
  have hpc₁ := tx_clampPoly_isOddBddLip P₁ hP₁o D hD0
  have hpc₂ := tx_clampPoly_isOddBddLip P₂ hP₂o D hD0
  have hsP₁ : supNorm (fun x => P₁.eval (max (-D) (min D x))) ≤ M₁ + 1 := by
    refine (tx_clampPoly_supNorm P₁ D hD0).trans (tx_supOn_le _ _ _ (by linarith) fun x hx => ?_)
    have h1 := hP₁c x hx
    have h2 := hM₁ x
    calc |P₁.eval x| = |f₁ x + (P₁.eval x - f₁ x)| := by ring_nf
      _ ≤ |f₁ x| + |P₁.eval x - f₁ x| := abs_add_le _ _
      _ ≤ M₁ + 1 := by linarith
  have hsP₂ : supNorm (fun x => P₂.eval (max (-D) (min D x))) ≤ M₂ + 1 := by
    refine (tx_clampPoly_supNorm P₂ D hD0).trans (tx_supOn_le _ _ _ (by linarith) fun x hx => ?_)
    have h1 := hP₂c x hx
    have h2 := hM₂ x
    calc |P₂.eval x| = |f₂ x + (P₂.eval x - f₂ x)| := by ring_nf
      _ ≤ |f₂ x| + |P₂.eval x - f₂ x| := abs_add_le _ _
      _ ≤ M₂ + 1 := by linarith
  have hcl₁ : ∀ x ∈ Set.Icc (-D) D, |f₁ x - P₁.eval (max (-D) (min D x))| ≤ a := fun x hx => by
    rw [tx_clamp_self D x (abs_le.mpr hx), abs_sub_comm]; exact hP₁c x hx
  have hcl₂ : ∀ x ∈ Set.Icc (-D) D, |f₂ x - P₂.eval (max (-D) (min D x))| ≤ a := fun x hx => by
    rw [tx_clamp_self D x (abs_le.mpr hx), abs_sub_comm]; exact hP₂c x hx
  -- bound on the event
  have hin : ∀ ω ∈ cutoffEvent cert (m k) (n k) (B k) ℓ J γstar 0,
      |contraction (B k) Fm Gm f₁ f₂ (cutoffMat (Fp k) ℓ J R 0 1 ω) (cutoffMat (Fp k) ℓ J R 0 2 ω) -
        contraction (B k) Fm Gm (fun x => P₁.eval x) (fun x => P₂.eval x)
          (cutoffMat (Fp k) ℓ J R 0 1 ω) (cutoffMat (Fp k) ℓ J R 0 2 ω)| ≤ γstar * a * K0 := by
    intro ω hω
    obtain ⟨n1, n2⟩ := lem_app_vol_norm_ii cert (Fp k) ℓ J R γstar CSig hR (hSize.1 k) 0 ω hω
    have e : contraction (B k) Fm Gm (fun x => P₁.eval x) (fun x => P₂.eval x)
          (cutoffMat (Fp k) ℓ J R 0 1 ω) (cutoffMat (Fp k) ℓ J R 0 2 ω) =
        contraction (B k) Fm Gm (fun x => P₁.eval (max (-D) (min D x)))
          (fun x => P₂.eval (max (-D) (min D x)))
          (cutoffMat (Fp k) ℓ J R 0 1 ω) (cutoffMat (Fp k) ℓ J R 0 2 ω) := by
      unfold contraction
      rw [tx_oddSharp_congr (fun x => P₁.eval x) (fun x => P₁.eval (max (-D) (min D x)))
          (cutoffMat (Fp k) ℓ J R 0 1 ω) D n1 (fun x hx => by simp only [tx_clamp_self D x (abs_le.mpr hx)]),
        tx_oddSharp_congr (fun x => P₂.eval x) (fun x => P₂.eval (max (-D) (min D x)))
          (cutoffMat (Fp k) ℓ J R 0 2 ω) D n2 (fun x hx => by simp only [tx_clamp_self D x (abs_le.mpr hx)])]
    rw [e]
    have h := tx_contr_cmp (Fp k).hB γstar hdim Fm Gm hF hG f₁ f₂ _ _ hf₁o hf₂o hpc₁ hpc₂
      (cutoffMat (Fp k) ℓ J R 0 1 ω) (cutoffMat (Fp k) ℓ J R 0 2 ω) D D a a ha0 ha0 n1 n2 hcl₁ hcl₂
    refine h.trans ?_
    have n1' := tx_supNorm_nonneg (fun x => P₁.eval (max (-D) (min D x)))
    have n2' := tx_supNorm_nonneg (fun x => P₂.eval (max (-D) (min D x)))
    have : a * (supNorm (fun x => P₂.eval (max (-D) (min D x))) + a) +
        supNorm (fun x => P₁.eval (max (-D) (min D x))) * a ≤ a * K0 := by
      rw [hK0]
      nlinarith [mul_le_mul_of_nonneg_left hsP₂ ha0, mul_le_mul_of_nonneg_right hsP₁ ha0,
        mul_le_mul_of_nonneg_left ha1 ha0]
    calc γstar * (a * (supNorm (fun x => P₂.eval (max (-D) (min D x))) + a) +
        supNorm (fun x => P₁.eval (max (-D) (min D x))) * a) ≤ γstar * (a * K0) :=
          mul_le_mul_of_nonneg_left this hγ0
      _ = γstar * a * K0 := by ring
  have hsplit := tx_split (indepSpaceLaw (m k) (n k) (B k)) _ (hintf.sub hintP)
    (cutoffEvent cert (m k) (n k) (B k) ℓ J γstar 0)
    (tx_meas_cutoffEvent cert _ _ _ ℓ J γstar 0) (γstar * a * K0)
    (by positivity) hin
    (fun ω => ENNReal.ofReal (γstar * M₁ * M₂) + ENNReal.ofReal (c0 * (2 +
        opNorm (cutoffMat (Fp k) ℓ J R 0 1 ω) ^ (P₁.natDegree + P₂.natDegree + 1) +
        opNorm (cutoffMat (Fp k) ℓ J R 0 2 ω) ^ (P₁.natDegree + P₂.natDegree + 1))))
    (fun ω => by
      refine le_trans (ENNReal.ofReal_le_ofReal ?_) ENNReal.ofReal_add_le
      refine (abs_sub _ _).trans (add_le_add ?_ ?_)
      · exact tx_contr_bdd (Fp k).hB γstar hdim Fm Gm hF hG f₁ f₂ hf₁o hf₂o M₁ M₂ hM₁ hM₂ _ _
      · exact hgrow (Fp k).hB hdim Fm Gm hF hG _ _)
    (ε / 4) (by positivity) hk1
  simp only [Pi.sub_apply] at hsplit
  rw [integral_sub hintf hintP] at hsplit
  -- the response
  have hext := tx_ext_approx cert γstar CSig (Fp k) (Sp k) (hSize.1 k) ℓ J R D le_rfl f₁ f₂
    hf₁c.continuousOn hf₂c.continuousOn Fd Gd hF hG j
  have hcongr : def_app_vol_tree (Fp k).β ℓ J R (B k) (Sp k).μ (Sp k).lam Fd Gd
      (treeApprox D f₁ j) (treeApprox D f₂ j) =
      def_app_vol_tree (Fp k).β ℓ J R (B k) (Sp k).μ (Sp k).lam Fd Gd P₁ P₂ :=
    tx_tree_congr _ _ _ _ _ _ _ _ _ _ _ _ _ (fun a => (hP₁k a).symm) (fun a => (hP₂k a).symm)
  rw [hcongr] at hext
  have hs₁ : supOn D f₁ ≤ M₁ := tx_supOn_le D f₁ M₁ hM₁0 fun x _ => hM₁ x
  have hs₂ : supOn D f₂ ≤ M₂ := tx_supOn_le D f₂ M₂ hM₂0 fun x _ => hM₂ x
  have hext2 : |def_app_vol_tree (Fp k).β ℓ J R (B k) (Sp k).μ (Sp k).lam Fd Gd P₁ P₂ -
      lagRespCut cert γstar CSig (Fp k).β ℓ J R (B k) (Sp k).μ (Sp k).lam Fd Gd f₁ f₂| ≤
      γstar * a * K0 := by
    refine hext.trans ?_
    have : γstar * (1 / ((j : ℝ) + 1)) * (supOn D f₁ + supOn D f₂ + 2) ≤ γstar * a * K0 := by
      rw [← ha, hK0]
      exact mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg hγ0 ha0)
    exact this
  have hbd2 : |(∫ ω, contraction (B k) Fm Gm (fun x => P₁.eval x) (fun x => P₂.eval x)
      (cutoffMat (Fp k) ℓ J R 0 1 ω) (cutoffMat (Fp k) ℓ J R 0 2 ω) ∂(indepSpaceLaw (m k) (n k) (B k))) -
      def_app_vol_tree (Fp k).β ℓ J R (B k) (Sp k).μ (Sp k).lam Fd Gd P₁ P₂| ≤ A / (B k : ℝ) := hbdP
  have hfin := abs_sub_le (∫ ω, contraction (B k) Fm Gm f₁ f₂ (cutoffMat (Fp k) ℓ J R 0 1 ω)
      (cutoffMat (Fp k) ℓ J R 0 2 ω) ∂(indepSpaceLaw (m k) (n k) (B k)))
    (∫ ω, contraction (B k) Fm Gm (fun x => P₁.eval x) (fun x => P₂.eval x)
      (cutoffMat (Fp k) ℓ J R 0 1 ω) (cutoffMat (Fp k) ℓ J R 0 2 ω) ∂(indepSpaceLaw (m k) (n k) (B k)))
    (lagRespCut cert γstar CSig (Fp k).β ℓ J R (B k) (Sp k).μ (Sp k).lam Fd Gd f₁ f₂)
  have hfin2 := abs_sub_le (∫ ω, contraction (B k) Fm Gm (fun x => P₁.eval x) (fun x => P₂.eval x)
      (cutoffMat (Fp k) ℓ J R 0 1 ω) (cutoffMat (Fp k) ℓ J R 0 2 ω) ∂(indepSpaceLaw (m k) (n k) (B k)))
    (def_app_vol_tree (Fp k).β ℓ J R (B k) (Sp k).μ (Sp k).lam Fd Gd P₁ P₂)
    (lagRespCut cert γstar CSig (Fp k).β ℓ J R (B k) (Sp k).μ (Sp k).lam Fd Gd f₁ f₂)
  linarith

private lemma tx_iii_full (cert : Muon.External.GaussianOpNorm) (γstar CSig γout γin : ℝ)
    (m n B : ℕ → ℕ) (Fp : ∀ k : ℕ, FrozenParams (m k) (n k) (B k))
    (Sp : ∀ k : ℕ, SpectralData (Fp k).C) (hSize : SizeSeq (B := B) (fun k => (Fp k).C) γstar CSig γout γin)
    (ℓ J : ℕ) (R : ℝ) (f₁ f₂ : ℝ → ℝ)
    (hf₁c : Continuous f₁) (hf₁o : ∀ x, f₁ (-x) = -f₁ x) (hf₁b : ∃ M : ℝ, ∀ x, |f₁ x| ≤ M)
    (hf₂c : Continuous f₂) (hf₂o : ∀ x, f₂ (-x) = -f₂ x) (hf₂b : ∃ M : ℝ, ∀ x, |f₂ x| ≤ M) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, ∀ t : ℤ, ∀ (Fd : Fin (m k) → ℝ) (Gd : Fin (n k) → ℝ)
      (Fm : Mat (m k) (m k)) (Gm : Mat (n k) (n k)),
      Fm = (Sp k).uOut * Matrix.diagonal Fd * (Sp k).uOutᵀ →
      Gm = (Sp k).vIn * Matrix.diagonal Gd * (Sp k).vInᵀ →
      opNorm Fm ≤ 1 → opNorm Gm ≤ 1 →
      |(∫ ω, contraction (B k) Fm Gm f₁ f₂
            (cutoffMat (Fp k) ℓ J R t 1 ω) (cutoffMat (Fp k) ℓ J R t 2 ω)
          ∂(indepSpaceLaw (m k) (n k) (B k))) -
        lagRespCut cert γstar CSig (Fp k).β ℓ J R (B k) (Sp k).μ (Sp k).lam Fd Gd f₁ f₂| ≤ ε := by
  intro ε hε
  by_cases hR : R ≤ 0
  · refine Eventually.of_forall fun k => ?_
    intro t Fd Gd Fm Gm hFm hGm hF hG
    obtain ⟨h1, h2⟩ := tx_nonpos_case cert γstar CSig (Fp k) (Sp k) ℓ J R hR Fd Gd Fm Gm f₁ f₂
      hf₁o hf₂o t
    rw [h1, h2]
    simpa using hε.le
  · push Not at hR
    filter_upwards [tx_iii_core cert γstar CSig γout γin m n B Fp Sp hSize ℓ J R hR f₁ f₂
      hf₁c hf₁o hf₁b hf₂c hf₂o hf₂b ε hε] with k hk
    intro t Fd Gd Fm Gm hFm hGm hF hG
    subst hFm hGm
    rw [tx_shift_cutoff (Fp k) ℓ J R t (fun K H => contraction (B k)
      ((Sp k).uOut * Matrix.diagonal Fd * (Sp k).uOutᵀ)
      ((Sp k).vIn * Matrix.diagonal Gd * (Sp k).vInᵀ) f₁ f₂ K H)]
    exact hk Fd Gd hF hG

private lemma tx_ext_diff (cert : Muon.External.GaussianOpNorm) (γstar CSig : ℝ)
    {m n B : ℕ} (Fp : FrozenParams m n B) (S : SpectralData Fp.C) (hS : SizeFin Fp.C B γstar CSig)
    (ℓ J : ℕ) (R : ℝ) (Fd : Fin m → ℝ) (Gd : Fin n → ℝ)
    (hF : opNorm (S.uOut * Matrix.diagonal Fd * S.uOutᵀ) ≤ 1)
    (hG : opNorm (S.vIn * Matrix.diagonal Gd * S.vInᵀ) ≤ 1)
    (f₁ f₂ g₁ g₂ : ℝ → ℝ) (hf₁c : Continuous f₁) (hf₂c : Continuous f₂)
    (hg₁c : Continuous g₁) (hg₂c : Continuous g₂)
    (hf₁o : ∀ x, f₁ (-x) = -f₁ x) (hf₂o : ∀ x, f₂ (-x) = -f₂ x)
    (hg₁o : ∀ x, g₁ (-x) = -g₁ x) (hg₂o : ∀ x, g₂ (-x) = -g₂ x)
    (a N₁ N₂ : ℝ) (ha : 0 ≤ a) (h₁ : ∀ x, |g₁ x - f₁ x| ≤ a) (h₂ : ∀ x, |g₂ x - f₂ x| ≤ a)
    (hN₁ : ∀ x, |f₁ x| ≤ N₁) (hN₂ : ∀ x, |g₂ x| ≤ N₂) :
    |lagRespCut cert γstar CSig Fp.β ℓ J R B S.μ S.lam Fd Gd g₁ g₂ -
        lagRespCut cert γstar CSig Fp.β ℓ J R B S.μ S.lam Fd Gd f₁ f₂| ≤
      γstar * (a * N₂ + N₁ * a) := by
  unfold lagRespCut
  set D := volDR cert R CSig γstar with hD
  have hN₁0 : 0 ≤ N₁ := (abs_nonneg _).trans (hN₁ 0)
  have hN₂0 : 0 ≤ N₂ := (abs_nonneg _).trans (hN₂ 0)
  have hγ := tx_gamma_nonneg Fp γstar CSig hS
  set h : ℝ → ℝ := fun x => g₁ x + (-1) * f₁ x with hh
  set k : ℝ → ℝ := fun x => g₂ x + (-1) * f₂ x with hk
  have hhc : Continuous h := hg₁c.add (continuous_const.mul hf₁c)
  have hkc : Continuous k := hg₂c.add (continuous_const.mul hf₂c)
  have hho : ∀ x, h (-x) = -h x := fun x => by simp only [hh, hg₁o x, hf₁o x]; ring
  have hko : ∀ x, k (-x) = -k x := fun x => by simp only [hk, hg₂o x, hf₂o x]; ring
  have i1 := tx_ext_ii cert γstar CSig Fp S hS ℓ J R D le_rfl g₁ g₂ hg₁c.continuousOn
    (fun x _ => hg₁o x) hg₂c.continuousOn (fun x _ => hg₂o x)
  have i2 := tx_ext_ii cert γstar CSig Fp S hS ℓ J R D le_rfl f₁ g₂ hf₁c.continuousOn
    (fun x _ => hf₁o x) hg₂c.continuousOn (fun x _ => hg₂o x)
  have i3 := tx_ext_ii cert γstar CSig Fp S hS ℓ J R D le_rfl h g₂ hhc.continuousOn
    (fun x _ => hho x) hg₂c.continuousOn (fun x _ => hg₂o x)
  have i4 := tx_ext_ii cert γstar CSig Fp S hS ℓ J R D le_rfl f₁ k hf₁c.continuousOn
    (fun x _ => hf₁o x) hkc.continuousOn (fun x _ => hko x)
  obtain ⟨-, -, -, -, -, e1, -, -⟩ := i1
  obtain ⟨-, -, -, -, -, -, e2, -⟩ := i2
  obtain ⟨-, b3, -, -, -, -, -, -⟩ := i3
  obtain ⟨-, b4, -, -, -, -, -, -⟩ := i4
  have E1 := e1 (-1) f₁ hf₁c.continuousOn (fun x _ => hf₁o x) Fd Gd
  have E2 := e2 (-1) f₂ hf₂c.continuousOn (fun x _ => hf₂o x) Fd Gd
  have B3 := b3 Fd Gd _ _ rfl rfl hF hG
  have B4 := b4 Fd Gd _ _ rfl rfl hF hG
  have sh : supOn D h ≤ a := tx_supOn_le D h a ha fun x _ => by
    simpa [hh, sub_eq_add_neg] using h₁ x
  have sk : supOn D k ≤ a := tx_supOn_le D k a ha fun x _ => by
    simpa [hk, sub_eq_add_neg] using h₂ x
  have sg : supOn D g₂ ≤ N₂ := tx_supOn_le D g₂ N₂ hN₂0 fun x _ => hN₂ x
  have sf : supOn D f₁ ≤ N₁ := tx_supOn_le D f₁ N₁ hN₁0 fun x _ => hN₁ x
  have key : treeRespExt Fp.β ℓ J R B S.μ S.lam Fd Gd D g₁ g₂ -
      treeRespExt Fp.β ℓ J R B S.μ S.lam Fd Gd D f₁ f₂ =
      treeRespExt Fp.β ℓ J R B S.μ S.lam Fd Gd D h g₂ +
        treeRespExt Fp.β ℓ J R B S.μ S.lam Fd Gd D f₁ k := by
    simp only [hh, hk] at E1 E2 ⊢
    linarith
  rw [key]
  refine (abs_add_le _ _).trans ?_
  have n1 := tx_supOn_nonneg D h
  have n2 := tx_supOn_nonneg D g₂
  have n3 := tx_supOn_nonneg D f₁
  have n4 := tx_supOn_nonneg D k
  have c1 : γstar * supOn D h * supOn D g₂ ≤ γstar * (a * N₂) :=
    by rw [mul_assoc]; exact mul_le_mul_of_nonneg_left (mul_le_mul sh sg n2 ha) hγ
  have c2 : γstar * supOn D f₁ * supOn D k ≤ γstar * (N₁ * a) :=
    by rw [mul_assoc]; exact mul_le_mul_of_nonneg_left (mul_le_mul sf sk n4 hN₁0) hγ
  nlinarith [B3, B4, c1, c2]

private lemma tx_perturb (cert : Muon.External.GaussianOpNorm) (γstar CSig : ℝ)
    {m n B : ℕ} (Fp : FrozenParams m n B) (S : SpectralData Fp.C) (hS : SizeFin Fp.C B γstar CSig)
    (ℓ J : ℕ) (R : ℝ) (t : ℤ) (Fd : Fin m → ℝ) (Gd : Fin n → ℝ)
    (hF : opNorm (S.uOut * Matrix.diagonal Fd * S.uOutᵀ) ≤ 1)
    (hG : opNorm (S.vIn * Matrix.diagonal Gd * S.vInᵀ) ≤ 1)
    (f₁ f₂ g₁ g₂ : ℝ → ℝ) (hf₁ : IsOddBddLip f₁) (hf₂ : IsOddBddLip f₂)
    (hg₁ : IsOddBddLip g₁) (hg₂ : IsOddBddLip g₂)
    (a N₁ N₂ : ℝ) (ha : 0 ≤ a) (h₁ : ∀ x, |g₁ x - f₁ x| ≤ a) (h₂ : ∀ x, |g₂ x - f₂ x| ≤ a)
    (hN₁ : ∀ x, |f₁ x| ≤ N₁) (hN₂ : ∀ x, |g₂ x| ≤ N₂) (hN₁' : ∀ x, |g₁ x| ≤ N₁)
    (hN₂' : ∀ x, |f₂ x| ≤ N₂) :
    |(∫ ω, contraction B (S.uOut * Matrix.diagonal Fd * S.uOutᵀ) (S.vIn * Matrix.diagonal Gd * S.vInᵀ)
          g₁ g₂ (cutoffMat Fp ℓ J R t 1 ω) (cutoffMat Fp ℓ J R t 2 ω) ∂(indepSpaceLaw m n B)) -
        lagRespCut cert γstar CSig Fp.β ℓ J R B S.μ S.lam Fd Gd g₁ g₂| ≤
      |(∫ ω, contraction B (S.uOut * Matrix.diagonal Fd * S.uOutᵀ) (S.vIn * Matrix.diagonal Gd * S.vInᵀ)
          f₁ f₂ (cutoffMat Fp ℓ J R t 1 ω) (cutoffMat Fp ℓ J R t 2 ω) ∂(indepSpaceLaw m n B)) -
        lagRespCut cert γstar CSig Fp.β ℓ J R B S.μ S.lam Fd Gd f₁ f₂| +
      2 * (γstar * (a * N₂ + N₁ * a)) := by
  set Fm := S.uOut * Matrix.diagonal Fd * S.uOutᵀ with hFm
  set Gm := S.vIn * Matrix.diagonal Gd * S.vInᵀ with hGm
  haveI : IsProbabilityMeasure (indepSpaceLaw m n B) := by
    unfold indepSpaceLaw; infer_instance
  have hdim : ((min m n : ℕ) : ℝ) ≤ γstar * (B : ℝ) :=
    le_trans (by exact_mod_cast min_le_max) hS.1
  have hN₁0 : 0 ≤ N₁ := (abs_nonneg _).trans (hN₁ 0)
  have hN₂0 : 0 ≤ N₂ := (abs_nonneg _).trans (hN₂ 0)
  have hγ := tx_gamma_nonneg Fp γstar CSig hS
  have hg₁c := tx_cont_of_lip _ hg₁
  have hg₂c := tx_cont_of_lip _ hg₂
  have hf₁c := tx_cont_of_lip _ hf₁
  have hf₂c := tx_cont_of_lip _ hf₂
  have hig := tx_integrable_contr Fp ℓ J R t γstar hdim Fm Gm hF hG g₁ g₂ hg₁c hg₂c hg₁.1 hg₂.1
    N₁ N₂ hN₁' hN₂
  have hif := tx_integrable_contr Fp ℓ J R t γstar hdim Fm Gm hF hG f₁ f₂ hf₁c hf₂c hf₁.1 hf₂.1
    N₁ N₂ hN₁ hN₂'
  have hext := tx_ext_diff cert γstar CSig Fp S hS ℓ J R Fd Gd hF hG f₁ f₂ g₁ g₂ hf₁c hf₂c hg₁c hg₂c
    hf₁.1 hf₂.1 hg₁.1 hg₂.1 a N₁ N₂ ha h₁ h₂ hN₁ hN₂
  have hI : |(∫ ω, contraction B Fm Gm g₁ g₂ (cutoffMat Fp ℓ J R t 1 ω) (cutoffMat Fp ℓ J R t 2 ω)
        ∂(indepSpaceLaw m n B)) -
      (∫ ω, contraction B Fm Gm f₁ f₂ (cutoffMat Fp ℓ J R t 1 ω) (cutoffMat Fp ℓ J R t 2 ω)
        ∂(indepSpaceLaw m n B))| ≤ γstar * (a * N₂ + N₁ * a) := by
    rw [← integral_sub hig hif]
    have := norm_integral_le_of_norm_le_const (μ := indepSpaceLaw m n B)
      (f := fun ω => contraction B Fm Gm g₁ g₂ (cutoffMat Fp ℓ J R t 1 ω) (cutoffMat Fp ℓ J R t 2 ω) -
        contraction B Fm Gm f₁ f₂ (cutoffMat Fp ℓ J R t 1 ω) (cutoffMat Fp ℓ J R t 2 ω))
      (C := γstar * (a * N₂ + N₁ * a)) (Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs]
        have := lem_app_vol_finite_iii (Fp.hB) γstar hdim Fm Gm hF hG g₁ g₂ f₁ f₂ hg₁ hg₂ hf₁ hf₂
          (cutoffMat Fp ℓ J R t 1 ω) (cutoffMat Fp ℓ J R t 2 ω)
        refine this.trans (mul_le_mul_of_nonneg_left ?_ hγ)
        have s1 : supNorm (fun x => g₁ x - f₁ x) ≤ a := tx_supNorm_le _ _ ha h₁
        have s2 : supNorm (fun x => g₂ x - f₂ x) ≤ a := tx_supNorm_le _ _ ha h₂
        have s3 : supNorm g₂ ≤ N₂ := tx_supNorm_le _ _ hN₂0 hN₂
        have s4 : supNorm f₁ ≤ N₁ := tx_supNorm_le _ _ hN₁0 hN₁
        exact add_le_add (mul_le_mul s1 s3 (tx_supNorm_nonneg _) ha)
          (mul_le_mul s4 s2 (tx_supNorm_nonneg _) hN₁0))
    rw [Real.norm_eq_abs] at this
    simpa [Measure.real] using this
  have e : (∫ ω, contraction B Fm Gm g₁ g₂ (cutoffMat Fp ℓ J R t 1 ω) (cutoffMat Fp ℓ J R t 2 ω)
        ∂(indepSpaceLaw m n B)) - lagRespCut cert γstar CSig Fp.β ℓ J R B S.μ S.lam Fd Gd g₁ g₂ =
      ((∫ ω, contraction B Fm Gm f₁ f₂ (cutoffMat Fp ℓ J R t 1 ω) (cutoffMat Fp ℓ J R t 2 ω)
        ∂(indepSpaceLaw m n B)) - lagRespCut cert γstar CSig Fp.β ℓ J R B S.μ S.lam Fd Gd f₁ f₂) +
      (((∫ ω, contraction B Fm Gm g₁ g₂ (cutoffMat Fp ℓ J R t 1 ω) (cutoffMat Fp ℓ J R t 2 ω)
        ∂(indepSpaceLaw m n B)) - (∫ ω, contraction B Fm Gm f₁ f₂ (cutoffMat Fp ℓ J R t 1 ω)
          (cutoffMat Fp ℓ J R t 2 ω) ∂(indepSpaceLaw m n B))) -
        (lagRespCut cert γstar CSig Fp.β ℓ J R B S.μ S.lam Fd Gd g₁ g₂ -
          lagRespCut cert γstar CSig Fp.β ℓ J R B S.μ S.lam Fd Gd f₁ f₂)) := by ring
  rw [e]
  refine (abs_add_le _ _).trans ?_
  have := abs_sub _ _ |>.trans (add_le_add hI hext)
  linarith [this]

private lemma tx_unif_generic (cert : Muon.External.GaussianOpNorm) (γstar CSig γout γin : ℝ)
    (m n B : ℕ → ℕ) (Fp : ∀ k : ℕ, FrozenParams (m k) (n k) (B k))
    (Sp : ∀ k : ℕ, SpectralData (Fp k).C)
    (hSize : SizeSeq (B := B) (fun k => (Fp k).C) γstar CSig γout γin)
    (ℓ J : ℕ) (R : ℝ) {X : Type} [PseudoMetricSpace X] (P : Set X) (hP : IsCompact P)
    (F₁ F₂ : X → ℝ → ℝ) (h₁ : ∀ p ∈ P, IsOddBddLip (F₁ p)) (h₂ : ∀ p ∈ P, IsOddBddLip (F₂ p))
    (N Lc : ℝ) (hN : 0 ≤ N) (hLc : 0 ≤ Lc)
    (hN₁ : ∀ p ∈ P, ∀ x, |F₁ p x| ≤ N) (hN₂ : ∀ p ∈ P, ∀ x, |F₂ p x| ≤ N)
    (hL₁ : ∀ p ∈ P, ∀ q ∈ P, ∀ x, |F₁ p x - F₁ q x| ≤ Lc * dist p q)
    (hL₂ : ∀ p ∈ P, ∀ q ∈ P, ∀ x, |F₂ p x - F₂ q x| ≤ Lc * dist p q) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, ∀ t : ℤ, ∀ p ∈ P, ∀ (Fd : Fin (m k) → ℝ) (Gd : Fin (n k) → ℝ)
      (Fm : Mat (m k) (m k)) (Gm : Mat (n k) (n k)),
      Fm = (Sp k).uOut * Matrix.diagonal Fd * (Sp k).uOutᵀ →
      Gm = (Sp k).vIn * Matrix.diagonal Gd * (Sp k).vInᵀ →
      opNorm Fm ≤ 1 → opNorm Gm ≤ 1 →
      |(∫ ω, contraction (B k) Fm Gm (F₁ p) (F₂ p)
            (cutoffMat (Fp k) ℓ J R t 1 ω) (cutoffMat (Fp k) ℓ J R t 2 ω)
          ∂(indepSpaceLaw (m k) (n k) (B k))) -
        lagRespCut cert γstar CSig (Fp k).β ℓ J R (B k) (Sp k).μ (Sp k).lam Fd Gd
          (F₁ p) (F₂ p)| ≤ ε := by
  intro ε hε
  have hγ0 : 0 ≤ γstar := tx_gamma_nonneg (Fp 0) γstar CSig (hSize.1 0)
  set η : ℝ := ε / (8 * (γstar + 1) * (Lc + 1) * (N + 1)) with hη
  have hηpos : 0 < η := by positivity
  obtain ⟨T, hTP, hTfin, hcover⟩ := hP.finite_cover_balls hηpos
  have hnet : ∀ᶠ k in atTop, ∀ q ∈ T, ∀ t : ℤ, ∀ (Fd : Fin (m k) → ℝ) (Gd : Fin (n k) → ℝ)
      (Fm : Mat (m k) (m k)) (Gm : Mat (n k) (n k)),
      Fm = (Sp k).uOut * Matrix.diagonal Fd * (Sp k).uOutᵀ →
      Gm = (Sp k).vIn * Matrix.diagonal Gd * (Sp k).vInᵀ →
      opNorm Fm ≤ 1 → opNorm Gm ≤ 1 →
      |(∫ ω, contraction (B k) Fm Gm (F₁ q) (F₂ q)
            (cutoffMat (Fp k) ℓ J R t 1 ω) (cutoffMat (Fp k) ℓ J R t 2 ω)
          ∂(indepSpaceLaw (m k) (n k) (B k))) -
        lagRespCut cert γstar CSig (Fp k).β ℓ J R (B k) (Sp k).μ (Sp k).lam Fd Gd
          (F₁ q) (F₂ q)| ≤ ε / 2 := by
    refine (Filter.eventually_all_finite hTfin).2 fun q hq => ?_
    have hqP := hTP hq
    exact tx_iii_full cert γstar CSig γout γin m n B Fp Sp hSize ℓ J R
      (F₁ q) (F₂ q) (tx_cont_of_lip _ (h₁ q hqP)) (h₁ q hqP).1 (h₁ q hqP).2.1
      (tx_cont_of_lip _ (h₂ q hqP)) (h₂ q hqP).1 (h₂ q hqP).2.1 (ε / 2) (by positivity)
  filter_upwards [hnet] with k hk
  intro t p hp Fd Gd Fm Gm hFm hGm hF hG
  have hpc : p ∈ ⋃ x ∈ T, Metric.ball x η := hcover hp
  simp only [Set.mem_iUnion, Metric.mem_ball] at hpc
  obtain ⟨q, hqT, hpq⟩ := hpc
  have hqP := hTP hqT
  subst hFm hGm
  have hper := tx_perturb cert γstar CSig (Fp k) (Sp k) (hSize.1 k) ℓ J R t Fd Gd hF hG
    (F₁ q) (F₂ q) (F₁ p) (F₂ p) (h₁ q hqP) (h₂ q hqP) (h₁ p hp) (h₂ p hp) (Lc * dist p q) N N
    (mul_nonneg hLc dist_nonneg) (hL₁ p hp q hqP) (hL₂ p hp q hqP) (hN₁ q hqP) (hN₂ p hp)
    (hN₁ p hp) (hN₂ q hqP)
  refine hper.trans ?_
  have h1 := hk q hqT t Fd Gd _ _ rfl rfl hF hG
  have h2 : 2 * (γstar * (Lc * dist p q * N + N * (Lc * dist p q))) ≤ ε / 2 := by
    have hd : dist p q ≤ η := hpq.le
    have : 2 * (γstar * (Lc * dist p q * N + N * (Lc * dist p q))) = 4 * γstar * Lc * N * dist p q := by
      ring
    rw [this]
    have h3 : 4 * γstar * Lc * N * dist p q ≤ 4 * γstar * Lc * N * η :=
      mul_le_mul_of_nonneg_left hd (by positivity)
    refine h3.trans ?_
    rw [hη]
    have hpos : 0 < 8 * (γstar + 1) * (Lc + 1) * (N + 1) := by positivity
    rw [mul_div_assoc', div_le_div_iff₀ hpos (by norm_num : (0:ℝ) < 2)]
    nlinarith [mul_nonneg (mul_nonneg hγ0 hLc) hN, mul_nonneg hγ0 hLc, mul_nonneg hγ0 hN,
      mul_nonneg hLc hN, hγ0, hLc, hN, mul_pos hε hε]
  linarith

private lemma tx_diff_le_supNorm (g f : ℝ → ℝ) (hg : IsOddBddLip g) (hf : IsOddBddLip f) (x : ℝ) :
    |g x - f x| ≤ supNorm (fun x => g x - f x) := by
  obtain ⟨_, ⟨M1, hM1⟩, _⟩ := hg
  obtain ⟨_, ⟨M2, hM2⟩, _⟩ := hf
  exact le_ciSup (f := fun x => |g x - f x|) ⟨M1 + M2, by
    rintro _ ⟨y, rfl⟩
    exact (abs_sub _ _).trans (add_le_add (hM1 y) (hM2 y))⟩ x

/-! ### Helpers for `lag_closure_generic` -/

private lemma tx_tau_nonneg (R : ℝ) : 0 ≤ cutoffTau R := by
  unfold cutoffTau
  exact integral_nonneg fun x => by split_ifs <;> positivity

private lemma tx_tau_tendsto : Tendsto cutoffTau atTop (𝓝 0) := by
  have hint : Integrable (fun x : ℝ => x ^ 2) (gaussianReal 0 1) := by
    have := ProbabilityTheory.memLp_id_gaussianReal (μ := 0) (v := 1) 2
    simpa using this.integrable_sq
  have key := tendsto_integral_filter_of_dominated_convergence (μ := gaussianReal 0 1)
    (l := (atTop : Filter ℝ)) (F := fun (R : ℝ) (x : ℝ) => if R < |x| then x ^ 2 else 0)
    (f := fun _ : ℝ => (0 : ℝ)) (bound := fun x : ℝ => x ^ 2)
    (Eventually.of_forall fun R => by
      refine Measurable.aestronglyMeasurable ?_
      exact Measurable.ite (measurableSet_lt measurable_const measurable_id.abs)
        (by fun_prop) measurable_const)
    (Eventually.of_forall fun R => Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs]
      split_ifs
      · rw [abs_of_nonneg (sq_nonneg x)]
      · simp [sq_nonneg])
    hint
    (Eventually.of_forall fun x => by
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_ge_atTop |x|] with R hR
      simp [not_lt.mpr hR])
  have h0 : cutoffTau = fun R : ℝ => ∫ x, (if R < |x| then x ^ 2 else 0) ∂(gaussianReal 0 1) := rfl
  rw [h0]
  simpa using key

private lemma tx_lagCut_repl (cert : Muon.External.GaussianOpNorm) (γstar CSig : ℝ)
    {m n B : ℕ} (Fp : FrozenParams m n B) (S : SpectralData Fp.C) (hS : SizeFin Fp.C B γstar CSig)
    (ℓ J : ℕ) (R : ℝ) (f₁ f₂ : ℝ → ℝ) (hf₁c : Continuous f₁) (hf₂c : Continuous f₂)
    (hf₁o : ∀ x, f₁ (-x) = -f₁ x) (hf₂o : ∀ x, f₂ (-x) = -f₂ x) (N : ℕ) (hN : 0 < N)
    (Fd : Fin m → ℝ) (Gd : Fin n → ℝ) :
    lagRespCut cert γstar CSig Fp.β ℓ J R (N * B) (replVec N S.μ) (replVec N S.lam)
        (replVec N Fd) (replVec N Gd) f₁ f₂ =
      lagRespCut cert γstar CSig Fp.β ℓ J R B S.μ S.lam Fd Gd f₁ f₂ := by
  unfold lagRespCut
  obtain ⟨-, -, hc, -⟩ := tx_ext_ii cert γstar CSig Fp S hS ℓ J R (volDR cert R CSig γstar) le_rfl
    f₁ f₂ hf₁c.continuousOn (fun x _ => hf₁o x) hf₂c.continuousOn (fun x _ => hf₂o x)
  exact hc N hN Fd Gd

private lemma tx_cut_diff (cert : Muon.External.GaussianOpNorm) (γstar CSig : ℝ)
    {m n B : ℕ} (Fp : FrozenParams m n B) (S : SpectralData Fp.C) (hS : SizeFin Fp.C B γstar CSig)
    (ℓ : ℕ) (Fd : Fin m → ℝ) (Gd : Fin n → ℝ)
    (hF : opNorm (S.uOut * Matrix.diagonal Fd * S.uOutᵀ) ≤ 1)
    (hG : opNorm (S.vIn * Matrix.diagonal Gd * S.vInᵀ) ≤ 1)
    (f₁ f₂ : ℝ → ℝ) (hf₁ : IsOddBddLip f₁) (hf₂ : IsOddBddLip f₂) (J J' : ℕ) (R R' : ℝ)
    (hR : 0 < R) (hR' : 0 < R') :
    |lagRespCut cert γstar CSig Fp.β ℓ J R B S.μ S.lam Fd Gd f₁ f₂ -
        lagRespCut cert γstar CSig Fp.β ℓ J' R' B S.μ S.lam Fd Gd f₁ f₂| ≤
      Real.sqrt 3 * CSig * γstar ^ (3 / 2 : ℝ) *
        (lipConst f₁ * supNorm f₂ + supNorm f₁ * lipConst f₂) *
        (cutoffDelta Fp.β J R + cutoffDelta Fp.β J' R') := by
  refine le_of_forall_pos_le_add fun ε hε => ?_
  choose Fp' S' hβ hμ hlam hFk hGk hSz using fun k : ℕ => tx_repl_setup Fp S (k + 1) (Nat.succ_pos k)
  have hBpos : 0 < B := Fp.hB
  have hSize : SizeSeq (B := fun k : ℕ => (k + 1) * B) (fun k => (Fp' k).C) γstar CSig
      ((m : ℝ) / B) ((n : ℝ) / B) := by
    refine ⟨fun k => hSz k γstar CSig hS, ?_, ?_, ?_⟩
    · refine tendsto_atTop_mono (fun k => ?_) tendsto_id
      show k ≤ (k + 1) * B
      nlinarith [Nat.succ_le_of_lt hBpos]
    · refine tendsto_const_nhds.congr fun k => ?_
      have : ((k + 1 : ℕ) : ℝ) ≠ 0 := by positivity
      have h2 : (B : ℝ) ≠ 0 := by exact_mod_cast hBpos.ne'
      push_cast
      field_simp
    · refine tendsto_const_nhds.congr fun k => ?_
      have : ((k + 1 : ℕ) : ℝ) ≠ 0 := by positivity
      have h2 : (B : ℝ) ≠ 0 := by exact_mod_cast hBpos.ne'
      push_cast
      field_simp
  have hf₁c := tx_cont_of_lip _ hf₁
  have hf₂c := tx_cont_of_lip _ hf₂
  have ev1 := tx_iii_full cert γstar CSig _ _ (fun k : ℕ => (k + 1) * m) (fun k => (k + 1) * n)
    (fun k => (k + 1) * B) Fp' S' hSize ℓ J R f₁ f₂ hf₁c hf₁.1 hf₁.2.1 hf₂c hf₂.1 hf₂.2.1 (ε / 2)
    (by positivity)
  have ev2 := tx_iii_full cert γstar CSig _ _ (fun k : ℕ => (k + 1) * m) (fun k => (k + 1) * n)
    (fun k => (k + 1) * B) Fp' S' hSize ℓ J' R' f₁ f₂ hf₁c hf₁.1 hf₁.2.1 hf₂c hf₂.1 hf₂.2.1 (ε / 2)
    (by positivity)
  obtain ⟨k, hk1, hk2⟩ := (ev1.and ev2).exists
  have h1 := hk1 0 (replVec (k + 1) Fd) (replVec (k + 1) Gd) _ _ rfl rfl (hFk k Fd hF) (hGk k Gd hG)
  have h2 := hk2 0 (replVec (k + 1) Fd) (replVec (k + 1) Gd) _ _ rfl rfl (hFk k Fd hF) (hGk k Gd hG)
  rw [hβ k, hμ k, hlam k, tx_lagCut_repl cert γstar CSig Fp S hS ℓ J R f₁ f₂ hf₁c hf₂c hf₁.1 hf₂.1
    (k + 1) (Nat.succ_pos k) Fd Gd] at h1
  rw [hβ k, hμ k, hlam k, tx_lagCut_repl cert γstar CSig Fp S hS ℓ J' R' f₁ f₂ hf₁c hf₂c hf₁.1 hf₂.1
    (k + 1) (Nat.succ_pos k) Fd Gd] at h2
  have c1 := lem_app_vol_cutoff_ii (Fp' k) ℓ J R γstar CSig hR (hSz k γstar CSig hS) 0 _ _
    (hFk k Fd hF) (hGk k Gd hG) f₁ f₂ hf₁ hf₂
  have c2 := lem_app_vol_cutoff_ii (Fp' k) ℓ J' R' γstar CSig hR' (hSz k γstar CSig hS) 0 _ _
    (hFk k Fd hF) (hGk k Gd hG) f₁ f₂ hf₁ hf₂
  rw [hβ k] at c1 c2
  set a := lagRespCut cert γstar CSig Fp.β ℓ J R B S.μ S.lam Fd Gd f₁ f₂
  set a' := lagRespCut cert γstar CSig Fp.β ℓ J' R' B S.μ S.lam Fd Gd f₁ f₂
  set IK := ∫ ω, contraction ((k + 1) * B) ((S' k).uOut * Matrix.diagonal (replVec (k + 1) Fd) * (S' k).uOutᵀ)
    ((S' k).vIn * Matrix.diagonal (replVec (k + 1) Gd) * (S' k).vInᵀ) f₁ f₂
    (cutoffMat (Fp' k) ℓ J R 0 1 ω) (cutoffMat (Fp' k) ℓ J R 0 2 ω)
    ∂(indepSpaceLaw ((k + 1) * m) ((k + 1) * n) ((k + 1) * B))
  set IK' := ∫ ω, contraction ((k + 1) * B) ((S' k).uOut * Matrix.diagonal (replVec (k + 1) Fd) * (S' k).uOutᵀ)
    ((S' k).vIn * Matrix.diagonal (replVec (k + 1) Gd) * (S' k).vInᵀ) f₁ f₂
    (cutoffMat (Fp' k) ℓ J' R' 0 1 ω) (cutoffMat (Fp' k) ℓ J' R' 0 2 ω)
    ∂(indepSpaceLaw ((k + 1) * m) ((k + 1) * n) ((k + 1) * B))
  set IM := ∫ ω, contraction ((k + 1) * B) ((S' k).uOut * Matrix.diagonal (replVec (k + 1) Fd) * (S' k).uOutᵀ)
    ((S' k).vIn * Matrix.diagonal (replVec (k + 1) Gd) * (S' k).vInᵀ) f₁ f₂
    (def_app_vol_product (Fp' k) ω 0) (def_app_vol_product (Fp' k) ω (0 + (ℓ : ℤ)))
    ∂(indepSpaceLaw ((k + 1) * m) ((k + 1) * n) ((k + 1) * B))
  have t1 := abs_sub_le a IK a'
  have t2 := abs_sub_le IK IM a'
  have t3 := abs_sub_le IM IK' a'
  have u1 := abs_sub_comm a IK
  have u2 := abs_sub_comm IK IM
  have u3 := abs_sub_comm IM IK'
  have eq : Real.sqrt 3 * CSig * γstar ^ (3 / 2 : ℝ) *
        (lipConst f₁ * supNorm f₂ + supNorm f₁ * lipConst f₂) *
        (cutoffDelta Fp.β J R + cutoffDelta Fp.β J' R') =
      Real.sqrt 3 * CSig * γstar ^ (3 / 2 : ℝ) *
        (lipConst f₁ * supNorm f₂ + supNorm f₁ * lipConst f₂) * cutoffDelta Fp.β J R +
      Real.sqrt 3 * CSig * γstar ^ (3 / 2 : ℝ) *
        (lipConst f₁ * supNorm f₂ + supNorm f₁ * lipConst f₂) * cutoffDelta Fp.β J' R' := by ring
  rw [eq]
  linarith

private lemma tx_lip_nonneg (f : ℝ → ℝ) : 0 ≤ lipConst f :=
  Real.iSup_nonneg fun p => by
    split_ifs
    · exact le_rfl
    · positivity

private lemma tx_lagResp_cut (cert : Muon.External.GaussianOpNorm) (γstar CSig : ℝ)
    {m n B : ℕ} (Fp : FrozenParams m n B) (S : SpectralData Fp.C) (hS : SizeFin Fp.C B γstar CSig)
    (ℓ : ℕ) (Fd : Fin m → ℝ) (Gd : Fin n → ℝ)
    (hF : opNorm (S.uOut * Matrix.diagonal Fd * S.uOutᵀ) ≤ 1)
    (hG : opNorm (S.vIn * Matrix.diagonal Gd * S.vInᵀ) ≤ 1)
    (f₁ f₂ : ℝ → ℝ) (hf₁ : IsOddBddLip f₁) (hf₂ : IsOddBddLip f₂) (J : ℕ) (R : ℝ) (hR : 0 < R) :
    |lagResp cert γstar CSig Fp.β ℓ B S.μ S.lam Fd Gd f₁ f₂ -
        lagRespCut cert γstar CSig Fp.β ℓ J R B S.μ S.lam Fd Gd f₁ f₂| ≤
      Real.sqrt 3 * CSig * γstar ^ (3 / 2 : ℝ) *
        (lipConst f₁ * supNorm f₂ + supNorm f₁ * lipConst f₂) * cutoffDelta Fp.β J R := by
  have hγ := tx_gamma_nonneg Fp γstar CSig hS
  have hCS : 0 ≤ CSig := (tx_opNorm_nonneg _).trans hS.2.1
  set C : ℝ := Real.sqrt 3 * CSig * γstar ^ (3 / 2 : ℝ) *
    (lipConst f₁ * supNorm f₂ + supNorm f₁ * lipConst f₂) with hC
  have hC0 : 0 ≤ C := by
    have := Real.rpow_nonneg hγ (3 / 2 : ℝ)
    have h1 := tx_lip_nonneg f₁
    have h2 := tx_lip_nonneg f₂
    have h3 := tx_supNorm_nonneg f₁
    have h4 := tx_supNorm_nonneg f₂
    rw [hC]; positivity
  set a : ℕ × ℝ → ℝ := fun p => lagRespCut cert γstar CSig Fp.β ℓ p.1 p.2 B S.μ S.lam Fd Gd f₁ f₂
    with ha
  set δ : ℕ × ℝ → ℝ := fun p => cutoffDelta Fp.β p.1 p.2 with hδdef
  have hfst : Tendsto (Prod.fst : ℕ × ℝ → ℕ) (atTop ×ˢ atTop) atTop := tendsto_fst
  have hsnd : Tendsto (Prod.snd : ℕ × ℝ → ℝ) (atTop ×ˢ atTop) atTop := tendsto_snd
  have hδ : Tendsto δ (atTop ×ˢ atTop : Filter (ℕ × ℝ)) (𝓝 0) := by
    have h1 : Tendsto (fun p : ℕ × ℝ => Fp.β ^ (p.1 + 1)) (atTop ×ˢ atTop) (𝓝 0) :=
      (tendsto_pow_atTop_nhds_zero_of_lt_one Fp.hβ.1 Fp.hβ.2).comp
        ((tendsto_add_atTop_nat 1).comp hfst)
    have h2 : Tendsto (fun p : ℕ × ℝ => Real.sqrt (cutoffTau p.2)) (atTop ×ˢ atTop) (𝓝 0) := by
      have := (Real.continuous_sqrt.tendsto 0).comp (tx_tau_tendsto.comp hsnd)
      rw [Real.sqrt_zero] at this
      exact this
    have h3 := h1.add h2
    rw [add_zero] at h3
    exact h3
  have hδ0 : ∀ p, 0 ≤ δ p := fun p => add_nonneg (pow_nonneg Fp.hβ.1 _) (Real.sqrt_nonneg _)
  have hcauchy : Cauchy (Filter.map a (atTop ×ˢ atTop : Filter (ℕ × ℝ))) := by
    rw [Metric.cauchy_iff]
    refine ⟨inferInstance, fun ε hε => ?_⟩
    have hev : ∀ᶠ p in (atTop ×ˢ atTop : Filter (ℕ × ℝ)), C * δ p < ε / 2 ∧ 0 < p.2 := by
      have h1 := (tendsto_order.1 (hδ.const_mul C)).2 (ε / 2) (by simpa using (by positivity : 0 < ε / 2))
      exact h1.and (hsnd.eventually_gt_atTop 0)
    refine ⟨a '' {p | C * δ p < ε / 2 ∧ 0 < p.2}, Filter.image_mem_map hev, ?_⟩
    rintro _ ⟨p, hp, rfl⟩ _ ⟨q, hq, rfl⟩
    rw [Real.dist_eq]
    have := tx_cut_diff cert γstar CSig Fp S hS ℓ Fd Gd hF hG f₁ f₂ hf₁ hf₂ p.1 q.1 p.2 q.2 hp.2 hq.2
    refine this.trans_lt ?_
    have e : Real.sqrt 3 * CSig * γstar ^ (3 / 2 : ℝ) *
        (lipConst f₁ * supNorm f₂ + supNorm f₁ * lipConst f₂) *
        (cutoffDelta Fp.β p.1 p.2 + cutoffDelta Fp.β q.1 q.2) = C * δ p + C * δ q := by
      rw [hC]; simp only [hδdef]; ring
    rw [e]; linarith [hp.1, hq.1]
  obtain ⟨L, hL⟩ := CompleteSpace.complete hcauchy
  have hlim : Tendsto a (atTop ×ˢ atTop : Filter (ℕ × ℝ)) (𝓝 L) := hL
  have hLR : lagResp cert γstar CSig Fp.β ℓ B S.μ S.lam Fd Gd f₁ f₂ = L := hlim.limUnder_eq
  rw [hLR]
  have h1 : Tendsto (fun q => |a q - a (J, R)|) (atTop ×ˢ atTop : Filter (ℕ × ℝ)) (𝓝 |L - a (J, R)|) :=
    (hlim.sub_const _).abs
  have h2 : Tendsto (fun q => C * (δ (J, R) + δ q)) (atTop ×ˢ atTop : Filter (ℕ × ℝ))
      (𝓝 (C * (δ (J, R) + 0))) :=
    (tendsto_const_nhds.add hδ).const_mul C
  have hle := le_of_tendsto_of_tendsto h1 h2 (by
    filter_upwards [hsnd.eventually_gt_atTop (0 : ℝ)] with q hq
    have := tx_cut_diff cert γstar CSig Fp S hS ℓ Fd Gd hF hG f₁ f₂ hf₁ hf₂ J q.1 R q.2 hR hq
    rw [abs_sub_comm]
    refine this.trans (le_of_eq ?_)
    rw [hC])
  simp only [add_zero] at hle
  have e2 : a (J, R) = lagRespCut cert γstar CSig Fp.β ℓ J R B S.μ S.lam Fd Gd f₁ f₂ := rfl
  rw [e2] at hle
  exact hle

/-- Conditional form of `lag_closure_generic` (proved): the same conclusion under a uniform bound
`β_k ≤ b < 1` on the momenta. The frozen statement of `lag_closure_generic` has no such hypothesis;
the cutoff errors `δ_{J,R}` of `lem_app_vol_cutoff_ii` scale with `β_k^{J+1}` and are not uniform
in `k` without it. -/
private lemma tx_lag_closure_beta (cert : Muon.External.GaussianOpNorm) (γstar CSig γout γin : ℝ)
    (m n B : ℕ → ℕ) (Fp : ∀ k : ℕ, FrozenParams (m k) (n k) (B k))
    (Sp : ∀ k : ℕ, SpectralData (Fp k).C)
    (hSize : SizeSeq (B := B) (fun k => (Fp k).C) γstar CSig γout γin)
    (b : ℝ) (hb : b < 1) (hβ : ∀ k, (Fp k).β ≤ b)
    (ℓ : ℕ) (f₁ f₂ : ℝ → ℝ) (hf₁ : IsOddBddLip f₁) (hf₂ : IsOddBddLip f₂) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, ∀ t : ℤ, ∀ (Fd : Fin (m k) → ℝ) (Gd : Fin (n k) → ℝ)
      (Fm : Mat (m k) (m k)) (Gm : Mat (n k) (n k)),
      Fm = (Sp k).uOut * Matrix.diagonal Fd * (Sp k).uOutᵀ →
      Gm = (Sp k).vIn * Matrix.diagonal Gd * (Sp k).vInᵀ →
      opNorm Fm ≤ 1 → opNorm Gm ≤ 1 →
      |(∫ ω, contraction (B k) Fm Gm f₁ f₂ (def_app_vol_product (Fp k) ω t)
            (def_app_vol_product (Fp k) ω (t + (ℓ : ℤ)))
          ∂(indepSpaceLaw (m k) (n k) (B k))) -
        lagResp cert γstar CSig (Fp k).β ℓ (B k) (Sp k).μ (Sp k).lam Fd Gd f₁ f₂| ≤ ε := by
  intro ε hε
  have hγ : 0 ≤ γstar := tx_gamma_nonneg (Fp 0) γstar CSig (hSize.1 0)
  have hCS : 0 ≤ CSig := (tx_opNorm_nonneg _).trans (hSize.1 0).2.1
  have hb0 : 0 ≤ b := (Fp 0).hβ.1.trans (hβ 0)
  set C : ℝ := Real.sqrt 3 * CSig * γstar ^ (3 / 2 : ℝ) *
    (lipConst f₁ * supNorm f₂ + supNorm f₁ * lipConst f₂) with hC
  have hC0 : 0 ≤ C := by
    have := Real.rpow_nonneg hγ (3 / 2 : ℝ)
    have h1 := tx_lip_nonneg f₁
    have h2 := tx_lip_nonneg f₂
    have h3 := tx_supNorm_nonneg f₁
    have h4 := tx_supNorm_nonneg f₂
    rw [hC]; positivity
  set θ : ℝ := ε / (4 * (C + 1)) with hθ
  have hθ0 : 0 < θ := by positivity
  obtain ⟨J, hJ⟩ := (tendsto_pow_atTop_nhds_zero_of_lt_one hb0 hb |>.eventually
    (gt_mem_nhds (by positivity : 0 < θ / 2))).exists
  have hJ' : b ^ J < θ / 2 := hJ
  obtain ⟨R, hRτ, hR⟩ := ((tx_tau_tendsto.eventually (gt_mem_nhds (by positivity : 0 < (θ / 2) ^ 2))).and
    (eventually_gt_atTop (0 : ℝ))).exists
  have hsq : Real.sqrt (cutoffTau R) < θ / 2 := by
    have := Real.sqrt_lt_sqrt (tx_tau_nonneg R) hRτ
    rwa [Real.sqrt_sq (by positivity)] at this
  have hδ : ∀ k, cutoffDelta (Fp k).β J R < θ := by
    intro k
    unfold cutoffDelta
    have : (Fp k).β ^ (J + 1) ≤ b ^ J := by
      calc (Fp k).β ^ (J + 1) ≤ (Fp k).β ^ J := pow_le_pow_of_le_one (Fp k).hβ.1 (Fp k).hβ.2.le
            (Nat.le_succ J)
        _ ≤ b ^ J := pow_le_pow_left₀ (Fp k).hβ.1 (hβ k) J
    linarith
  filter_upwards [tx_iii_full cert γstar CSig γout γin m n B Fp Sp hSize ℓ J R f₁ f₂
    (tx_cont_of_lip _ hf₁) hf₁.1 hf₁.2.1 (tx_cont_of_lip _ hf₂) hf₂.1 hf₂.2.1 (ε / 2) (by positivity)]
    with k hk
  intro t Fd Gd Fm Gm hFd hGd hF hG
  have hS := hSize.1 k
  subst hFd hGd
  have c1 := lem_app_vol_cutoff_ii (Fp k) ℓ J R γstar CSig hR hS t _ _ hF hG f₁ f₂ hf₁ hf₂
  have c2 := tx_lagResp_cut cert γstar CSig (Fp k) (Sp k) hS ℓ Fd Gd hF hG f₁ f₂ hf₁ hf₂ J R hR
  have h3 := hk t Fd Gd _ _ rfl rfl hF hG
  have hCδ : C * cutoffDelta (Fp k).β J R ≤ C * θ := mul_le_mul_of_nonneg_left (hδ k).le hC0
  have hCθ : C * θ ≤ ε / 4 := by
    rw [hθ]
    rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  have t1 := abs_sub_le (∫ ω, contraction (B k) ((Sp k).uOut * Matrix.diagonal Fd * (Sp k).uOutᵀ)
      ((Sp k).vIn * Matrix.diagonal Gd * (Sp k).vInᵀ) f₁ f₂ (def_app_vol_product (Fp k) ω t)
      (def_app_vol_product (Fp k) ω (t + (ℓ : ℤ))) ∂(indepSpaceLaw (m k) (n k) (B k)))
    (∫ ω, contraction (B k) ((Sp k).uOut * Matrix.diagonal Fd * (Sp k).uOutᵀ)
      ((Sp k).vIn * Matrix.diagonal Gd * (Sp k).vInᵀ) f₁ f₂ (cutoffMat (Fp k) ℓ J R t 1 ω)
      (cutoffMat (Fp k) ℓ J R t 2 ω) ∂(indepSpaceLaw (m k) (n k) (B k)))
    (lagResp cert γstar CSig (Fp k).β ℓ (B k) (Sp k).μ (Sp k).lam Fd Gd f₁ f₂)
  have t2 := abs_sub_le (∫ ω, contraction (B k) ((Sp k).uOut * Matrix.diagonal Fd * (Sp k).uOutᵀ)
      ((Sp k).vIn * Matrix.diagonal Gd * (Sp k).vInᵀ) f₁ f₂ (cutoffMat (Fp k) ℓ J R t 1 ω)
      (cutoffMat (Fp k) ℓ J R t 2 ω) ∂(indepSpaceLaw (m k) (n k) (B k)))
    (lagRespCut cert γstar CSig (Fp k).β ℓ J R (B k) (Sp k).μ (Sp k).lam Fd Gd f₁ f₂)
    (lagResp cert γstar CSig (Fp k).β ℓ (B k) (Sp k).μ (Sp k).lam Fd Gd f₁ f₂)
  have u := abs_sub_comm (lagRespCut cert γstar CSig (Fp k).β ℓ J R (B k) (Sp k).μ (Sp k).lam Fd Gd f₁ f₂)
    (lagResp cert γstar CSig (Fp k).β ℓ (B k) (Sp k).μ (Sp k).lam Fd Gd f₁ f₂)
  have e : C * cutoffDelta (Fp k).β J R = Real.sqrt 3 * CSig * γstar ^ (3 / 2 : ℝ) *
        (lipConst f₁ * supNorm f₂ + supNorm f₁ * lipConst f₂) * cutoffDelta (Fp k).β J R := by
    rw [hC]
  linarith


/-- `lem:app-vol-tree-extension`, snapshot `cr-2026-10-23`. Declaration of record. LaTeX, verbatim from `section.tex` (the whole environment):

```latex
\begin{lemma}[Extension to continuous filters]\label{lem:app-vol-tree-extension}
Fix $(\ell,J,R)$ and diagonal $F,G$ with $\norm F,\norm G\le1$. Write
$\norm f_D\defeq\sup_{\abs x\le D}\abs{f(x)}$.
\begin{enumerate}[label=(\roman*)]
\item For odd polynomials $f_1,f_2$,
$\abs{\mathfrak R^{J,R}_\ell[F,G](f_1,f_2)}\le\gamma_\star\norm{f_1}_{D_R}\norm{f_2}_{D_R}$.
\item The response extends uniquely to a bilinear functional on pairs of odd
continuous functions on $[-D_R,D_R]$ with the same bound. The extension is
linear in $F$ and in $G$ and unchanged under replication.
\item For odd bounded continuous $f_1,f_2$ on $\R$, under the size conditions,
\[
\sup_{F,G}\abs{\EE\,\mathcal K^{F,G}[f_1,f_2](\mathsf K_1,\mathsf K_2)-\mathfrak R^{J,R}_\ell[F,G](f_1,f_2)}\longrightarrow0 ,
\]
the supremum over diagonal $F,G$ of norm at most one; the convergence is
uniform over $(f_1,f_2)=(\iota_s,\iota_u)$ with $s,u$ in a compact subset of
$(0,\infty)$, and over $(f_1,f_2)=(\omega_\ridge,\omega_{\ridge'})$ with $\ridge,\ridge'\in I$.
\end{enumerate}
\end{lemma}
```
-/
theorem lem_app_vol_tree_extension_i (cert : Muon.External.GaussianOpNorm) (γstar CSig : ℝ)
    {m n B : ℕ} (Fp : FrozenParams m n B) (S : SpectralData Fp.C) (hS : SizeFin Fp.C B γstar CSig)
    (ℓ J : ℕ) (R : ℝ) (Fm : Mat m m) (Gm : Mat n n) (Fd : Fin m → ℝ) (Gd : Fin n → ℝ)
    (hFd : Fm = S.uOut * Matrix.diagonal Fd * S.uOutᵀ) (hGd : Gm = S.vIn * Matrix.diagonal Gd * S.vInᵀ)
    (hF : opNorm Fm ≤ 1) (hG : opNorm Gm ≤ 1)
    (D : ℝ) (hD : volDR cert R CSig γstar ≤ D)
    (f₁ f₂ : Polynomial ℝ) (hf₁ : ∀ x : ℝ, f₁.eval (-x) = -f₁.eval x)
    (hf₂ : ∀ x : ℝ, f₂.eval (-x) = -f₂.eval x) :
    |def_app_vol_tree Fp.β ℓ J R B S.μ S.lam Fd Gd f₁ f₂| ≤
      γstar * supOn D (fun x => f₁.eval x) * supOn D (fun x => f₂.eval x) := by
  subst hFd hGd
  exact tx_bound cert γstar CSig Fp S hS ℓ J R Fd Gd hF hG D hD f₁ f₂ hf₁ hf₂

/-- `lem:app-vol-tree-extension`, snapshot `cr-2026-10-23`. Declaration of record. LaTeX, verbatim from `section.tex` (the whole environment):

```latex
\begin{lemma}[Extension to continuous filters]\label{lem:app-vol-tree-extension}
Fix $(\ell,J,R)$ and diagonal $F,G$ with $\norm F,\norm G\le1$. Write
$\norm f_D\defeq\sup_{\abs x\le D}\abs{f(x)}$.
\begin{enumerate}[label=(\roman*)]
\item For odd polynomials $f_1,f_2$,
$\abs{\mathfrak R^{J,R}_\ell[F,G](f_1,f_2)}\le\gamma_\star\norm{f_1}_{D_R}\norm{f_2}_{D_R}$.
\item The response extends uniquely to a bilinear functional on pairs of odd
continuous functions on $[-D_R,D_R]$ with the same bound. The extension is
linear in $F$ and in $G$ and unchanged under replication.
\item For odd bounded continuous $f_1,f_2$ on $\R$, under the size conditions,
\[
\sup_{F,G}\abs{\EE\,\mathcal K^{F,G}[f_1,f_2](\mathsf K_1,\mathsf K_2)-\mathfrak R^{J,R}_\ell[F,G](f_1,f_2)}\longrightarrow0 ,
\]
the supremum over diagonal $F,G$ of norm at most one; the convergence is
uniform over $(f_1,f_2)=(\iota_s,\iota_u)$ with $s,u$ in a compact subset of
$(0,\infty)$, and over $(f_1,f_2)=(\omega_\ridge,\omega_{\ridge'})$ with $\ridge,\ridge'\in I$.
\end{enumerate}
\end{lemma}
```
-/
theorem lem_app_vol_tree_extension_ii (cert : Muon.External.GaussianOpNorm) (γstar CSig : ℝ)
    {m n B : ℕ} (Fp : FrozenParams m n B) (S : SpectralData Fp.C) (hS : SizeFin Fp.C B γstar CSig)
    (ℓ J : ℕ) (R : ℝ) (D : ℝ) (hD : volDR cert R CSig γstar ≤ D) (f g : ℝ → ℝ)
    (hfc : ContinuousOn f (Set.Icc (-D) D)) (hfo : ∀ x ∈ Set.Icc (-D) D, f (-x) = -f x)
    (hgc : ContinuousOn g (Set.Icc (-D) D)) (hgo : ∀ x ∈ Set.Icc (-D) D, g (-x) = -g x) :
    -- (a) existence: the polynomial responses converge to the extension, for all test entries
    (∀ (Fd : Fin m → ℝ) (Gd : Fin n → ℝ),
      Tendsto (fun k : ℕ => def_app_vol_tree Fp.β ℓ J R B S.μ S.lam Fd Gd
          (treeApprox D f k) (treeApprox D g k)) atTop
        (𝓝 (treeRespExt Fp.β ℓ J R B S.μ S.lam Fd Gd D f g))) ∧
    -- (b) the bound on the extension, for diagonal tests of norm at most one
    (∀ (Fd : Fin m → ℝ) (Gd : Fin n → ℝ) (Fm : Mat m m) (Gm : Mat n n),
      Fm = S.uOut * Matrix.diagonal Fd * S.uOutᵀ → Gm = S.vIn * Matrix.diagonal Gd * S.vInᵀ →
      opNorm Fm ≤ 1 → opNorm Gm ≤ 1 →
      |treeRespExt Fp.β ℓ J R B S.μ S.lam Fd Gd D f g| ≤
        γstar * supOn D f * supOn D g) ∧
    -- (c) replication invariance (eigenvalues repeated N times, batch N * B)
    (∀ (N : ℕ), 0 < N → ∀ (Fd : Fin m → ℝ) (Gd : Fin n → ℝ),
      treeRespExt Fp.β ℓ J R (N * B) (replVec N S.μ) (replVec N S.lam) (replVec N Fd)
          (replVec N Gd) D f g =
        treeRespExt Fp.β ℓ J R B S.μ S.lam Fd Gd D f g) ∧
    -- (d) linearity in the output and in the input diagonal entries
    (∀ (c : ℝ) (Fd₁ Fd₂ : Fin m → ℝ) (Gd : Fin n → ℝ),
      treeRespExt Fp.β ℓ J R B S.μ S.lam (fun i => c * Fd₁ i + Fd₂ i) Gd D f g =
        c * treeRespExt Fp.β ℓ J R B S.μ S.lam Fd₁ Gd D f g +
          treeRespExt Fp.β ℓ J R B S.μ S.lam Fd₂ Gd D f g) ∧
    (∀ (c : ℝ) (Fd : Fin m → ℝ) (Gd₁ Gd₂ : Fin n → ℝ),
      treeRespExt Fp.β ℓ J R B S.μ S.lam Fd (fun j => c * Gd₁ j + Gd₂ j) D f g =
        c * treeRespExt Fp.β ℓ J R B S.μ S.lam Fd Gd₁ D f g +
          treeRespExt Fp.β ℓ J R B S.μ S.lam Fd Gd₂ D f g) ∧
    -- (e) bilinear extension: linearity in the first and in the second function
    (∀ (c : ℝ) (f' : ℝ → ℝ), ContinuousOn f' (Set.Icc (-D) D) →
      (∀ x ∈ Set.Icc (-D) D, f' (-x) = -f' x) → ∀ (Fd : Fin m → ℝ) (Gd : Fin n → ℝ),
      treeRespExt Fp.β ℓ J R B S.μ S.lam Fd Gd D (fun x => f x + c * f' x) g =
        treeRespExt Fp.β ℓ J R B S.μ S.lam Fd Gd D f g +
          c * treeRespExt Fp.β ℓ J R B S.μ S.lam Fd Gd D f' g) ∧
    (∀ (c : ℝ) (g' : ℝ → ℝ), ContinuousOn g' (Set.Icc (-D) D) →
      (∀ x ∈ Set.Icc (-D) D, g' (-x) = -g' x) → ∀ (Fd : Fin m → ℝ) (Gd : Fin n → ℝ),
      treeRespExt Fp.β ℓ J R B S.μ S.lam Fd Gd D f (fun x => g x + c * g' x) =
        treeRespExt Fp.β ℓ J R B S.μ S.lam Fd Gd D f g +
          c * treeRespExt Fp.β ℓ J R B S.μ S.lam Fd Gd D f g') ∧
    -- (f) agreement with the tree response on odd polynomials
    (∀ (p q : Polynomial ℝ), (∀ x : ℝ, p.eval (-x) = -p.eval x) →
      (∀ x : ℝ, q.eval (-x) = -q.eval x) → ∀ (Fd : Fin m → ℝ) (Gd : Fin n → ℝ),
      treeRespExt Fp.β ℓ J R B S.μ S.lam Fd Gd D (fun x => p.eval x) (fun x => q.eval x) =
        def_app_vol_tree Fp.β ℓ J R B S.μ S.lam Fd Gd p q) := by
  exact tx_ext_ii cert γstar CSig Fp S hS ℓ J R D hD f g hfc hfo hgc hgo

/-- `lem:app-vol-tree-extension`, snapshot `cr-2026-10-23`. Declaration of record. LaTeX, verbatim from `section.tex` (the whole environment):

```latex
\begin{lemma}[Extension to continuous filters]\label{lem:app-vol-tree-extension}
Fix $(\ell,J,R)$ and diagonal $F,G$ with $\norm F,\norm G\le1$. Write
$\norm f_D\defeq\sup_{\abs x\le D}\abs{f(x)}$.
\begin{enumerate}[label=(\roman*)]
\item For odd polynomials $f_1,f_2$,
$\abs{\mathfrak R^{J,R}_\ell[F,G](f_1,f_2)}\le\gamma_\star\norm{f_1}_{D_R}\norm{f_2}_{D_R}$.
\item The response extends uniquely to a bilinear functional on pairs of odd
continuous functions on $[-D_R,D_R]$ with the same bound. The extension is
linear in $F$ and in $G$ and unchanged under replication.
\item For odd bounded continuous $f_1,f_2$ on $\R$, under the size conditions,
\[
\sup_{F,G}\abs{\EE\,\mathcal K^{F,G}[f_1,f_2](\mathsf K_1,\mathsf K_2)-\mathfrak R^{J,R}_\ell[F,G](f_1,f_2)}\longrightarrow0 ,
\]
the supremum over diagonal $F,G$ of norm at most one; the convergence is
uniform over $(f_1,f_2)=(\iota_s,\iota_u)$ with $s,u$ in a compact subset of
$(0,\infty)$, and over $(f_1,f_2)=(\omega_\ridge,\omega_{\ridge'})$ with $\ridge,\ridge'\in I$.
\end{enumerate}
\end{lemma}
```
-/
theorem lem_app_vol_tree_extension_iii (cert : Muon.External.GaussianOpNorm) (γstar CSig γout γin : ℝ)
    (m n B : ℕ → ℕ) (Fp : ∀ k : ℕ, FrozenParams (m k) (n k) (B k))
    (Sp : ∀ k : ℕ, SpectralData (Fp k).C) (hSize : SizeSeq (B := B) (fun k => (Fp k).C) γstar CSig γout γin)
    (ℓ J : ℕ) (R : ℝ) (f₁ f₂ : ℝ → ℝ)
    (hf₁c : Continuous f₁) (hf₁o : ∀ x, f₁ (-x) = -f₁ x) (hf₁b : ∃ M : ℝ, ∀ x, |f₁ x| ≤ M)
    (hf₂c : Continuous f₂) (hf₂o : ∀ x, f₂ (-x) = -f₂ x) (hf₂b : ∃ M : ℝ, ∀ x, |f₂ x| ≤ M) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, ∀ t : ℤ, ∀ (Fd : Fin (m k) → ℝ) (Gd : Fin (n k) → ℝ)
      (Fm : Mat (m k) (m k)) (Gm : Mat (n k) (n k)),
      Fm = (Sp k).uOut * Matrix.diagonal Fd * (Sp k).uOutᵀ →
      Gm = (Sp k).vIn * Matrix.diagonal Gd * (Sp k).vInᵀ →
      opNorm Fm ≤ 1 → opNorm Gm ≤ 1 →
      |(∫ ω, contraction (B k) Fm Gm f₁ f₂
            (cutoffMat (Fp k) ℓ J R t 1 ω) (cutoffMat (Fp k) ℓ J R t 2 ω)
          ∂(indepSpaceLaw (m k) (n k) (B k))) -
        lagRespCut cert γstar CSig (Fp k).β ℓ J R (B k) (Sp k).μ (Sp k).lam Fd Gd f₁ f₂| ≤ ε := by
  exact tx_iii_full cert γstar CSig γout γin m n B Fp Sp hSize ℓ J R f₁ f₂ hf₁c hf₁o hf₁b hf₂c hf₂o hf₂b

/-- `lem:app-vol-tree-extension`, snapshot `cr-2026-10-23`. Declaration of record. LaTeX, verbatim from `section.tex` (the whole environment):

```latex
\begin{lemma}[Extension to continuous filters]\label{lem:app-vol-tree-extension}
Fix $(\ell,J,R)$ and diagonal $F,G$ with $\norm F,\norm G\le1$. Write
$\norm f_D\defeq\sup_{\abs x\le D}\abs{f(x)}$.
\begin{enumerate}[label=(\roman*)]
\item For odd polynomials $f_1,f_2$,
$\abs{\mathfrak R^{J,R}_\ell[F,G](f_1,f_2)}\le\gamma_\star\norm{f_1}_{D_R}\norm{f_2}_{D_R}$.
\item The response extends uniquely to a bilinear functional on pairs of odd
continuous functions on $[-D_R,D_R]$ with the same bound. The extension is
linear in $F$ and in $G$ and unchanged under replication.
\item For odd bounded continuous $f_1,f_2$ on $\R$, under the size conditions,
\[
\sup_{F,G}\abs{\EE\,\mathcal K^{F,G}[f_1,f_2](\mathsf K_1,\mathsf K_2)-\mathfrak R^{J,R}_\ell[F,G](f_1,f_2)}\longrightarrow0 ,
\]
the supremum over diagonal $F,G$ of norm at most one; the convergence is
uniform over $(f_1,f_2)=(\iota_s,\iota_u)$ with $s,u$ in a compact subset of
$(0,\infty)$, and over $(f_1,f_2)=(\omega_\ridge,\omega_{\ridge'})$ with $\ridge,\ridge'\in I$.
\end{enumerate}
\end{lemma}
```
-/
theorem lem_app_vol_tree_extension_iii_unif (cert : Muon.External.GaussianOpNorm)
    (γstar CSig γout γin : ℝ) (m n B : ℕ → ℕ) (Fp : ∀ k : ℕ, FrozenParams (m k) (n k) (B k))
    (Sp : ∀ k : ℕ, SpectralData (Fp k).C)
    (hSize : SizeSeq (B := B) (fun k => (Fp k).C) γstar CSig γout γin)
    (ℓ J : ℕ) (R : ℝ) (K : Set ℝ) (hK : IsCompact K) (hKpos : K ⊆ Set.Ioi 0)
    (ϱlo ϱhi : ℝ) (hϱ : 0 < ϱlo ∧ ϱlo ≤ ϱhi) :
    -- (a) uniform over the resolvent filters (ι_s, ι_u), s, u in a compact set K
    (∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, ∀ t : ℤ, ∀ s ∈ K, ∀ u ∈ K,
      ∀ (Fd : Fin (m k) → ℝ) (Gd : Fin (n k) → ℝ)
      (Fm : Mat (m k) (m k)) (Gm : Mat (n k) (n k)),
      Fm = (Sp k).uOut * Matrix.diagonal Fd * (Sp k).uOutᵀ →
      Gm = (Sp k).vIn * Matrix.diagonal Gd * (Sp k).vInᵀ →
      opNorm Fm ≤ 1 → opNorm Gm ≤ 1 →
      |(∫ ω, contractionRes (B k) Fm Gm s u
            (cutoffMat (Fp k) ℓ J R t 1 ω) (cutoffMat (Fp k) ℓ J R t 2 ω)
          ∂(indepSpaceLaw (m k) (n k) (B k))) -
        lagRespCut cert γstar CSig (Fp k).β ℓ J R (B k) (Sp k).μ (Sp k).lam Fd Gd
          (iotaF s) (iotaF u)| ≤ ε) ∧
    -- (b) uniform over the filters (ω_ϱ, ω_ϱ'), ϱ, ϱ' in I
    (∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, ∀ t : ℤ, ∀ ϱ ∈ Set.Icc ϱlo ϱhi, ∀ ϱ' ∈ Set.Icc ϱlo ϱhi,
      ∀ (Fd : Fin (m k) → ℝ) (Gd : Fin (n k) → ℝ)
      (Fm : Mat (m k) (m k)) (Gm : Mat (n k) (n k)),
      Fm = (Sp k).uOut * Matrix.diagonal Fd * (Sp k).uOutᵀ →
      Gm = (Sp k).vIn * Matrix.diagonal Gd * (Sp k).vInᵀ →
      opNorm Fm ≤ 1 → opNorm Gm ≤ 1 →
      |(∫ ω, contraction (B k) Fm Gm (omegaF ϱ) (omegaF ϱ')
            (cutoffMat (Fp k) ℓ J R t 1 ω) (cutoffMat (Fp k) ℓ J R t 2 ω)
          ∂(indepSpaceLaw (m k) (n k) (B k))) -
        lagRespCut cert γstar CSig (Fp k).β ℓ J R (B k) (Sp k).μ (Sp k).lam Fd Gd
          (omegaF ϱ) (omegaF ϱ')| ≤ ε) := by
  have hϱ0 := hϱ.1
  refine ⟨?_, ?_⟩
  · -- (a)
    rcases K.eq_empty_or_nonempty with hKe | hKne
    · intro ε hε
      exact Eventually.of_forall fun k t s hs => absurd hs (by simp [hKe])
    · obtain ⟨s₀, hs₀K, hmin⟩ := hK.exists_isMinOn hKne continuous_id.continuousOn
      have hs₀pos : 0 < s₀ := hKpos hs₀K
      have hle : ∀ s ∈ K, s₀ ≤ s := fun s hs => hmin hs
      have hCs : 0 < s₀ ^ ((3 : ℝ) / 2) := Real.rpow_pos_of_pos hs₀pos _
      have hio : ∀ s ∈ K, IsOddBddLip (iotaF s) := fun s hs =>
        (lem_app_vol_sharp_ii (hKpos hs) one_pos).1
      have hbd : ∀ s ∈ K, ∀ x, |iotaF s x| ≤ 1 / (2 * Real.sqrt s₀) := fun s hs x => by
        have h1 := tx_le_supNorm _ (hio s hs) x
        rw [(lem_app_vol_sharp_ii (hKpos hs) one_pos).2.2.1] at h1
        refine h1.trans ?_
        have hs : 0 < s := hKpos hs
        have : 2 * Real.sqrt s₀ ≤ 2 * Real.sqrt s := by
          have := Real.sqrt_le_sqrt (hle s ‹_›)
          linarith
        exact one_div_le_one_div_of_le (by positivity) this
      have hgen := tx_unif_generic cert γstar CSig γout γin m n B Fp Sp hSize ℓ J R (X := ℝ × ℝ)
        (K ×ˢ K) (hK.prod hK) (fun p => iotaF p.1) (fun p => iotaF p.2)
        (fun p hp => hio p.1 hp.1) (fun p hp => hio p.2 hp.2) (1 / (2 * Real.sqrt s₀))
        (1 / s₀ ^ ((3 : ℝ) / 2)) (by positivity) (by positivity)
        (fun p hp x => hbd p.1 hp.1 x) (fun p hp x => hbd p.2 hp.2 x)
        (fun p hp q hq x => by
          have h1 := tx_diff_le_supNorm _ _ (hio p.1 hp.1) (hio q.1 hq.1) x
          have h2 := (lem_app_vol_sharp_iii hs₀pos one_pos (hle _ hp.1) (hle _ hq.1)
            (le_refl (1 : ℝ)) (le_refl (1 : ℝ))).1
          refine h1.trans (h2.trans ?_)
          rw [div_eq_mul_inv, one_div, mul_comm]
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          rw [Prod.dist_eq, Real.dist_eq]
          exact le_max_left _ _)
        (fun p hp q hq x => by
          have h1 := tx_diff_le_supNorm _ _ (hio p.2 hp.2) (hio q.2 hq.2) x
          have h2 := (lem_app_vol_sharp_iii hs₀pos one_pos (hle _ hp.2) (hle _ hq.2)
            (le_refl (1 : ℝ)) (le_refl (1 : ℝ))).1
          refine h1.trans (h2.trans ?_)
          rw [div_eq_mul_inv, one_div, mul_comm]
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          rw [Prod.dist_eq, Real.dist_eq]
          exact le_max_right _ _)
      intro ε hε
      filter_upwards [hgen ε hε] with k hk
      intro t s hs u hu Fd Gd Fm Gm hFm hGm hF hG
      exact hk t (s, u) ⟨hs, hu⟩ Fd Gd Fm Gm hFm hGm hF hG
  · -- (b)
    obtain ⟨hϱ0, hϱle⟩ := hϱ
    have hIc : IsCompact (Set.Icc ϱlo ϱhi) := isCompact_Icc
    have hio : ∀ ϱ ∈ Set.Icc ϱlo ϱhi, IsOddBddLip (omegaF ϱ) := fun ϱ hϱm =>
      (lem_app_vol_sharp_ii one_pos (by linarith [hϱm.1] : 0 < ϱ)).2.1
    have hbd : ∀ ϱ ∈ Set.Icc ϱlo ϱhi, ∀ x, |omegaF ϱ x| ≤ 1 := fun ϱ hϱm x => by
      have h1 := tx_le_supNorm _ (hio ϱ hϱm) x
      rw [(lem_app_vol_sharp_ii one_pos (by linarith [hϱm.1] : 0 < ϱ)).2.2.2.2.1] at h1
      exact h1
    have hgen := tx_unif_generic cert γstar CSig γout γin m n B Fp Sp hSize ℓ J R (X := ℝ × ℝ)
      (Set.Icc ϱlo ϱhi ×ˢ Set.Icc ϱlo ϱhi) (hIc.prod hIc) (fun p => omegaF p.1)
      (fun p => omegaF p.2) (fun p hp => hio p.1 hp.1) (fun p hp => hio p.2 hp.2) 1
      (1 / (2 * ϱlo)) zero_le_one (by positivity)
      (fun p hp x => hbd p.1 hp.1 x) (fun p hp x => hbd p.2 hp.2 x)
      (fun p hp q hq x => by
        have h1 := tx_diff_le_supNorm _ _ (hio p.1 hp.1) (hio q.1 hq.1) x
        have h2 := (lem_app_vol_sharp_iii one_pos hϱ0 (le_refl (1 : ℝ)) (le_refl (1 : ℝ))
          hp.1.1 hq.1.1).2
        refine h1.trans (h2.trans ?_)
        rw [div_eq_mul_inv, one_div, mul_comm]
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        rw [Prod.dist_eq, Real.dist_eq]
        exact le_max_left _ _)
      (fun p hp q hq x => by
        have h1 := tx_diff_le_supNorm _ _ (hio p.2 hp.2) (hio q.2 hq.2) x
        have h2 := (lem_app_vol_sharp_iii one_pos hϱ0 (le_refl (1 : ℝ)) (le_refl (1 : ℝ))
          hp.2.1 hq.2.1).2
        refine h1.trans (h2.trans ?_)
        rw [div_eq_mul_inv, one_div, mul_comm]
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        rw [Prod.dist_eq, Real.dist_eq]
        exact le_max_right _ _)
    intro ε hε
    filter_upwards [hgen ε hε] with k hk
    intro t ϱ hϱm ϱ' hϱm' Fd Gd Fm Gm hFm hGm hF hG
    exact hk t (ϱ, ϱ') ⟨hϱm, hϱm'⟩ Fd Gd Fm Gm hFm hGm hF hG

/-! ## Remark: other filters (promoted to a lemma, card R15) -/

/-- `rem:app-vol-other-filters`, snapshot `cr-2026-10-23`. Declaration of record. LaTeX, verbatim from `section.tex` (the whole environment):

```latex
\begin{remark}[Other filters]\label{rem:app-vol-other-filters}
The proof of \cref{eqn:app-vol-lag-closure} uses of the filters only that they
are odd, bounded and Lipschitz. For any fixed odd, bounded, Lipschitz $f_1,f_2$
it therefore gives, with the supremum over diagonal $F,G$ of norm at most one,
\[
\sup_{F,G}\abs{\EE\,\mathcal K^{F,G}[f_1,f_2](M^{\mathrm g}_t,M^{\mathrm g}_{t+\ell})-\mathfrak R_\ell[F,G](f_1,f_2)}\longrightarrow0 ,
\]
and \cref{sec:app-pl} uses this for a fixed filter and for compactly
supported resolvent integrals.
\end{remark}
```
-/
theorem lag_closure_generic (cert : Muon.External.GaussianOpNorm) (γstar CSig γout γin : ℝ)
    (hCSig : 1 ≤ CSig) (m n B : ℕ → ℕ) (Fp : ∀ k : ℕ, FrozenParams (m k) (n k) (B k))
    (Sp : ∀ k : ℕ, SpectralData (Fp k).C) (hSize : SizeSeq (B := B) (fun k => (Fp k).C) γstar CSig γout γin)
    (b : ℝ) (hb : b < 1) (hβ : ∀ k, (Fp k).β ≤ b)
    (ℓ : ℕ) (f₁ f₂ : ℝ → ℝ) (hf₁ : IsOddBddLip f₁) (hf₂ : IsOddBddLip f₂) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, ∀ t : ℤ, ∀ (Fd : Fin (m k) → ℝ) (Gd : Fin (n k) → ℝ)
      (Fm : Mat (m k) (m k)) (Gm : Mat (n k) (n k)),
      Fm = (Sp k).uOut * Matrix.diagonal Fd * (Sp k).uOutᵀ →
      Gm = (Sp k).vIn * Matrix.diagonal Gd * (Sp k).vInᵀ →
      opNorm Fm ≤ 1 → opNorm Gm ≤ 1 →
      |(∫ ω, contraction (B k) Fm Gm f₁ f₂ (def_app_vol_product (Fp k) ω t)
            (def_app_vol_product (Fp k) ω (t + (ℓ : ℤ)))
          ∂(indepSpaceLaw (m k) (n k) (B k))) -
        lagResp cert γstar CSig (Fp k).β ℓ (B k) (Sp k).μ (Sp k).lam Fd Gd f₁ f₂| ≤ ε :=
  tx_lag_closure_beta cert γstar CSig γout γin m n B Fp Sp hSize b hb hβ ℓ f₁ f₂ hf₁ hf₂

/-! ## Deterministic joint moment response (`thm:app-vol-lag-kernel`) -/

private lemma p3_cut_scale (cert : Muon.External.GaussianOpNorm) (γstar CSig : ℝ)
    {m n B : ℕ} (Fp : FrozenParams m n B) (S : SpectralData Fp.C)
    (hS : SizeFin Fp.C B γstar CSig) (ℓ J : ℕ) (R c d : ℝ)
    (Fd : Fin m → ℝ) (Gd : Fin n → ℝ) (f g : ℝ → ℝ)
    (hf : Continuous f) (hg : Continuous g) :
    lagRespCut cert γstar CSig Fp.β ℓ J R B S.μ S.lam (c • Fd) (d • Gd) f g =
      c * d * lagRespCut cert γstar CSig Fp.β ℓ J R B S.μ S.lam Fd Gd f g := by
  have hl := tx_ext_lim cert γstar CSig Fp S hS ℓ J R _ le_rfl f g
    hf.continuousOn hg.continuousOn Fd Gd
  have hr := tx_ext_lim cert γstar CSig Fp S hS ℓ J R _ le_rfl f g
    hf.continuousOn hg.continuousOn (c • Fd) (d • Gd)
  apply tendsto_nhds_unique hr
  apply (hl.const_mul (c * d)).congr
  intro k
  rw [tx_tree_smulF, tx_tree_smulG]
  ring

open scoped Matrix.Norms.L2Operator in
private lemma p3_normalize {k : ℕ} (U : Mat k k) (hU : Uᵀ * U = 1) (d : Fin k → ℝ) :
    ∃ e : Fin k → ℝ, d = opNorm (U * Matrix.diagonal d * Uᵀ) • e ∧
      opNorm (U * Matrix.diagonal e * Uᵀ) ≤ 1 := by
  let a := opNorm (U * Matrix.diagonal d * Uᵀ)
  have ha : 0 ≤ a := tx_opNorm_nonneg _
  have hnorm : a = ‖d‖ := by
    dsimp [a]
    rw [opNorm_eq_norm, tx_norm_right_orth _ Uᵀ (by
      rw [Matrix.transpose_transpose]; exact mul_eq_one_comm.mp hU),
      tx_norm_left_orth U hU, Matrix.l2_opNorm_diagonal]
  by_cases hz : a = 0
  · have hd : d = 0 := norm_eq_zero.mp (hnorm.symm.trans hz)
    refine ⟨0, by simp [hd], ?_⟩
    change opNorm (U * Matrix.diagonal (fun _ => 0) * Uᵀ) ≤ 1
    rw [Matrix.diagonal_zero, Matrix.mul_zero, Matrix.zero_mul, opNorm_eq_norm]
    exact (norm_zero : ‖(0 : Mat k k)‖ = 0).le.trans zero_le_one
  · refine ⟨a⁻¹ • d, ?_, ?_⟩
    · change d = a • (a⁻¹ • d)
      rw [smul_smul, mul_inv_cancel₀ hz, one_smul]
    · rw [Matrix.diagonal_smul, Matrix.mul_smul, smul_mul_assoc,
        opNorm_eq_norm, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_nonneg ha,
        ← opNorm_eq_norm]
      change a⁻¹ * a ≤ 1
      rw [inv_mul_cancel₀ hz]

private lemma p3_delta (β : ℝ) (hβ : 0 ≤ β ∧ β < 1) :
    Tendsto (fun p : ℕ × ℝ => cutoffDelta β p.1 p.2)
      (atTop ×ˢ atTop : Filter (ℕ × ℝ)) (𝓝 0) := by
  have h1 := (tendsto_pow_atTop_nhds_zero_of_lt_one hβ.1 hβ.2).comp
    ((tendsto_add_atTop_nat 1).comp (tendsto_fst :
      Tendsto (Prod.fst : ℕ × ℝ → ℕ) (atTop ×ˢ atTop) atTop))
  have h2 := (Real.continuous_sqrt.tendsto 0).comp (tx_tau_tendsto.comp
    (tendsto_snd : Tendsto (Prod.snd : ℕ × ℝ → ℝ) (atTop ×ˢ atTop) atTop))
  simpa [cutoffDelta] using h1.add h2

private lemma p3_unit_tendsto (cert : Muon.External.GaussianOpNorm) (γstar CSig : ℝ)
    {m n B : ℕ} (Fp : FrozenParams m n B) (S : SpectralData Fp.C)
    (hS : SizeFin Fp.C B γstar CSig) (ℓ : ℕ) (Fd : Fin m → ℝ) (Gd : Fin n → ℝ)
    (hF : opNorm (S.uOut * Matrix.diagonal Fd * S.uOutᵀ) ≤ 1)
    (hG : opNorm (S.vIn * Matrix.diagonal Gd * S.vInᵀ) ≤ 1)
    (f g : ℝ → ℝ) (hf : IsOddBddLip f) (hg : IsOddBddLip g) :
    Tendsto (fun p : ℕ × ℝ => lagRespCut cert γstar CSig Fp.β ℓ p.1 p.2 B S.μ S.lam Fd Gd f g)
      (atTop ×ˢ atTop : Filter (ℕ × ℝ))
      (𝓝 (lagResp cert γstar CSig Fp.β ℓ B S.μ S.lam Fd Gd f g)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _)
    (g := fun p : ℕ × ℝ => Real.sqrt 3 * CSig * γstar ^ (3 / 2 : ℝ) *
      (lipConst f * supNorm g + supNorm f * lipConst g) * cutoffDelta Fp.β p.1 p.2) ?_ ?_
  · filter_upwards [(tendsto_snd : Tendsto (Prod.snd : ℕ × ℝ → ℝ)
      (atTop ×ˢ atTop) atTop).eventually_gt_atTop 0] with p hp
    rw [Real.norm_eq_abs, abs_sub_comm]
    exact tx_lagResp_cut cert γstar CSig Fp S hS ℓ Fd Gd hF hG f g hf hg p.1 p.2 hp
  · simpa using (p3_delta Fp.β Fp.hβ).const_mul
      (Real.sqrt 3 * CSig * γstar ^ (3 / 2 : ℝ) *
        (lipConst f * supNorm g + supNorm f * lipConst g))

private lemma p4_uniform_delta {m n B : ℕ → ℕ}
    (Fp : ∀ k : ℕ, FrozenParams (m k) (n k) (B k))
    (b : ℝ) (hb : b < 1) (hβ : ∀ k, (Fp k).β ≤ b) :
    ∀ θ : ℝ, 0 < θ → ∃ J : ℕ, ∃ R : ℝ, 0 < R ∧ ∀ k, cutoffDelta (Fp k).β J R < θ := by
  intro θ hθ
  have hb0 : 0 ≤ b := (Fp 0).hβ.1.trans (hβ 0)
  obtain ⟨J, hJ⟩ := (tendsto_pow_atTop_nhds_zero_of_lt_one hb0 hb |>.eventually
    (gt_mem_nhds (by positivity : 0 < θ / 2))).exists
  obtain ⟨R, hRτ, hR⟩ := ((tx_tau_tendsto.eventually
    (gt_mem_nhds (by positivity : 0 < (θ / 2) ^ 2))).and
      (eventually_gt_atTop (0 : ℝ))).exists
  have hsqrt : Real.sqrt (cutoffTau R) < θ / 2 := by
    have := Real.sqrt_lt_sqrt (tx_tau_nonneg R) hRτ
    rwa [Real.sqrt_sq (by positivity)] at this
  refine ⟨J, R, hR, fun k => ?_⟩
  unfold cutoffDelta
  have hp : (Fp k).β ^ (J + 1) ≤ b ^ J := by
    calc
      (Fp k).β ^ (J + 1) ≤ (Fp k).β ^ J :=
        pow_le_pow_of_le_one (Fp k).hβ.1 (Fp k).hβ.2.le (Nat.le_succ J)
      _ ≤ b ^ J := pow_le_pow_left₀ (Fp k).hβ.1 (hβ k) J
  linarith

private lemma p4_cut_coeff_le (gamma CSig L N : ℝ) (hgamma : 0 ≤ gamma)
    (hCSig : 0 ≤ CSig) (hL : 0 ≤ L) (hN : 0 ≤ N)
    (f₁ f₂ : ℝ → ℝ) (hL₁ : lipConst f₁ ≤ L) (hL₂ : lipConst f₂ ≤ L)
    (hN₁ : supNorm f₁ ≤ N) (hN₂ : supNorm f₂ ≤ N) :
    Real.sqrt 3 * CSig * gamma ^ (3 / 2 : ℝ) *
        (lipConst f₁ * supNorm f₂ + supNorm f₁ * lipConst f₂) ≤
      Real.sqrt 3 * CSig * gamma ^ (3 / 2 : ℝ) * (L * N + N * L) := by
  refine mul_le_mul_of_nonneg_left (add_le_add ?_ ?_) (by positivity)
  · exact mul_le_mul hL₁ hN₂ (tx_supNorm_nonneg _) hL
  · exact mul_le_mul hN₁ hL₂ (tx_lip_nonneg _) hN

/-- `thm:app-vol-lag-kernel`, snapshot `cr-2026-10-23`. Declaration of record. LaTeX, verbatim from `section.tex` (the whole environment):

```latex
\begin{theorem}[Deterministic joint moment response]\label{thm:app-vol-lag-kernel}
Fix a finite dimension, a lag $\ell\ge0$ and diagonal $F,G$. For odd bounded
Lipschitz $f_1,f_2$, the limit
\begin{equation}\label{eqn:app-vol-Phi}
\mathfrak R_\ell[F,G](f_1,f_2)\defeq\lim_{J,R\to\infty}\mathfrak R^{J,R}_\ell[F,G](f_1,f_2),
\end{equation}
with $J$ and $R$ tending to infinity independently, exists, and
\begin{equation}\label{eqn:app-vol-Phi-cutoff}
\begin{aligned}
&\abs{\mathfrak R_\ell[F,G](f_1,f_2)-\mathfrak R^{J,R}_\ell[F,G](f_1,f_2)}\\
&\qquad\le2\sqrt3\,C_\Sigma\gamma_\star^{3/2}\norm F\norm G\big(\operatorname{Lip}(f_1)\norm{f_2}_\infty+\norm{f_1}_\infty\operatorname{Lip}(f_2)\big)\delta_{J,R}.
\end{aligned}
\end{equation}
The response $\mathfrak R_\ell$ is bilinear in $(F,G)$ and in $(f_1,f_2)$, unchanged
under replication, and bounded by $\gamma_\star\norm F\norm G\norm{f_1}_\infty\norm{f_2}_\infty$.
The lag kernels and the filtered lag coefficients are
\begin{equation}\label{eqn:app-vol-lag-kernel}
\mathfrak k_\ell[F,G](s,u)\defeq\mathfrak R_\ell[F,G](\iota_s,\iota_u),\qquad
\overline C_\ell[F,G](\ridge,\ridge')\defeq\mathfrak R_\ell[F,G](\omega_\ridge,\omega_{\ridge'}),
\end{equation}
and $\mathfrak k_\ell\defeq\mathfrak k_\ell[\Sigmaout,\Sigmain]$,
$\overline C_\ell\defeq\overline C_\ell[\Sigmaout,\Sigmain]$. Along every sequence of
dimensions satisfying the size conditions, for every compact
$\mathcal J\subset(0,\infty)$,
\begin{equation}\label{eqn:app-vol-lag-closure}
\begin{gathered}
\sup_{s,u\in\mathcal J}\sup_{F,G}\abs{\EE\,\mathcal K^{F,G}_{s,u}(M^{\mathrm g}_t,M^{\mathrm g}_{t+\ell})-\mathfrak k_\ell[F,G](s,u)}\to0,\\
\sup_{\ridge,\ridge'\in I}\sup_{F,G}\abs{C^{\mathrm g}_\ell[F,G](\ridge,\ridge')-\overline C_\ell[F,G](\ridge,\ridge')}\to0,
\end{gathered}
\end{equation}
the suprema over diagonal $F,G$ of norm at most one. Under
\cref{assum:app-setup-regime} the same holds for the actual model, with
$\EE\,\mathcal K^{F,G}_{s,u}(\Mt,M_{t+\ell})$ and $C_\ell[F,G]$ in place of the
independent quantities.
\end{theorem}
```
-/
theorem thm_app_vol_lag_kernel_exists (cert : Muon.External.GaussianOpNorm) (γstar CSig : ℝ)
    {m n B : ℕ} (Fp : FrozenParams m n B) (S : SpectralData Fp.C) (hS : SizeFin Fp.C B γstar CSig)
    (hCSig : 1 ≤ CSig) (ℓ : ℕ) (Fm : Mat m m) (Gm : Mat n n) (Fd : Fin m → ℝ) (Gd : Fin n → ℝ)
    (hFd : Fm = S.uOut * Matrix.diagonal Fd * S.uOutᵀ) (hGd : Gm = S.vIn * Matrix.diagonal Gd * S.vInᵀ)
    (f₁ f₂ : ℝ → ℝ) (hf₁ : IsOddBddLip f₁) (hf₂ : IsOddBddLip f₂) :
    Tendsto (fun p : ℕ × ℝ => lagRespCut cert γstar CSig Fp.β ℓ p.1 p.2 B S.μ S.lam Fd Gd f₁ f₂)
      (atTop ×ˢ atTop : Filter (ℕ × ℝ))
      (𝓝 (lagResp cert γstar CSig Fp.β ℓ B S.μ S.lam Fd Gd f₁ f₂)) := by
  obtain ⟨F, hF, hFn⟩ := p3_normalize S.uOut S.huOut Fd
  obtain ⟨G, hG, hGn⟩ := p3_normalize S.vIn S.hvIn Gd
  have hl := (p3_unit_tendsto cert γstar CSig Fp S hS ℓ F G hFn hGn f₁ f₂ hf₁ hf₂).const_mul
    (opNorm (S.uOut * Matrix.diagonal Fd * S.uOutᵀ) *
      opNorm (S.vIn * Matrix.diagonal Gd * S.vInᵀ))
  have he : (fun p : ℕ × ℝ => lagRespCut cert γstar CSig Fp.β ℓ p.1 p.2 B S.μ S.lam Fd Gd f₁ f₂) =
      (fun p : ℕ × ℝ => opNorm (S.uOut * Matrix.diagonal Fd * S.uOutᵀ) *
        opNorm (S.vIn * Matrix.diagonal Gd * S.vInᵀ) *
          lagRespCut cert γstar CSig Fp.β ℓ p.1 p.2 B S.μ S.lam F G f₁ f₂) := by
    funext p
    conv_lhs => rw [hF, hG]
    exact p3_cut_scale cert γstar CSig Fp S hS ℓ p.1 p.2 _ _ F G f₁ f₂
      (tx_cont_of_lip _ hf₁) (tx_cont_of_lip _ hf₂)
  rw [← he] at hl
  have heq := hl.limUnder_eq
  change Tendsto _ _ (𝓝 (limUnder _ _))
  rw [heq]
  exact hl

private lemma p3_lag_scale (cert : Muon.External.GaussianOpNorm) (γstar CSig : ℝ)
    {m n B : ℕ} (Fp : FrozenParams m n B) (S : SpectralData Fp.C)
    (hS : SizeFin Fp.C B γstar CSig) (hCSig : 1 ≤ CSig) (ℓ : ℕ) (c d : ℝ)
    (Fd : Fin m → ℝ) (Gd : Fin n → ℝ) (f g : ℝ → ℝ)
    (hf : IsOddBddLip f) (hg : IsOddBddLip g) :
    lagResp cert γstar CSig Fp.β ℓ B S.μ S.lam (c • Fd) (d • Gd) f g =
      c * d * lagResp cert γstar CSig Fp.β ℓ B S.μ S.lam Fd Gd f g := by
  have lim := fun F G => thm_app_vol_lag_kernel_exists cert γstar CSig Fp S hS hCSig ℓ
    _ _ F G rfl rfl f g hf hg
  apply tendsto_nhds_unique (lim (c • Fd) (d • Gd))
  apply ((lim Fd Gd).const_mul (c * d)).congr
  intro p
  exact (p3_cut_scale cert γstar CSig Fp S hS ℓ p.1 p.2 c d Fd Gd f g
    (tx_cont_of_lip _ hf) (tx_cont_of_lip _ hg)).symm

private lemma p3_unit_bound (cert : Muon.External.GaussianOpNorm) (γstar CSig : ℝ)
    {m n B : ℕ} (Fp : FrozenParams m n B) (S : SpectralData Fp.C)
    (hS : SizeFin Fp.C B γstar CSig) (ℓ : ℕ) (Fd : Fin m → ℝ) (Gd : Fin n → ℝ)
    (hF : opNorm (S.uOut * Matrix.diagonal Fd * S.uOutᵀ) ≤ 1)
    (hG : opNorm (S.vIn * Matrix.diagonal Gd * S.vInᵀ) ≤ 1)
    (f g : ℝ → ℝ) (hf : IsOddBddLip f) (hg : IsOddBddLip g) :
    |lagResp cert γstar CSig Fp.β ℓ B S.μ S.lam Fd Gd f g| ≤
      γstar * supNorm f * supNorm g := by
  apply le_of_tendsto (p3_unit_tendsto cert γstar CSig Fp S hS ℓ Fd Gd hF hG f g hf hg).abs
  refine Eventually.of_forall fun p => ?_
  have hb := (lem_app_vol_tree_extension_ii cert γstar CSig Fp S hS ℓ p.1 p.2 _ le_rfl f g
    (tx_cont_of_lip _ hf).continuousOn (fun x _ => hf.1 x)
    (tx_cont_of_lip _ hg).continuousOn (fun x _ => hg.1 x)).2.1 Fd Gd _ _ rfl rfl hF hG
  have sf := tx_supOn_le (volDR cert p.2 CSig γstar) f (supNorm f) (tx_supNorm_nonneg f)
    (fun x _ => tx_le_supNorm f hf x)
  have sg := tx_supOn_le (volDR cert p.2 CSig γstar) g (supNorm g) (tx_supNorm_nonneg g)
    (fun x _ => tx_le_supNorm g hg x)
  exact hb.trans (mul_le_mul (mul_le_mul_of_nonneg_left sf (tx_gamma_nonneg Fp γstar CSig hS)) sg
    (tx_supOn_nonneg _ _) (mul_nonneg (tx_gamma_nonneg Fp γstar CSig hS) (tx_supNorm_nonneg f)))

private lemma p3_add_filter (f g : ℝ → ℝ) (hf : IsOddBddLip f) (hg : IsOddBddLip g) (c : ℝ) :
    IsOddBddLip (fun x => f x + c * g x) := by
  obtain ⟨M, hM⟩ := hf.2.1
  obtain ⟨N, hN⟩ := hg.2.1
  obtain ⟨L, hL⟩ := hf.2.2
  obtain ⟨K, hK⟩ := hg.2.2
  refine ⟨fun x => by
    change f (-x) + c * g (-x) = -(f x + c * g x)
    rw [hf.1, hg.1]; ring, ⟨M + |c| * N, fun x => ?_⟩,
    ⟨L + |c| * K, fun x y => ?_⟩⟩
  · calc |f x + c * g x| ≤ |f x| + |c * g x| := abs_add_le _ _
      _ ≤ M + |c| * N := by rw [abs_mul]; gcongr; exacts [hM x, hN x]
  · calc |f x + c * g x - (f y + c * g y)| = |(f x - f y) + c * (g x - g y)| := by congr 1; ring
      _ ≤ |f x - f y| + |c * (g x - g y)| := abs_add_le _ _
      _ ≤ L * |x - y| + |c| * (K * |x - y|) := by
        rw [abs_mul]; gcongr; exacts [hL x y, hK x y]
      _ = (L + |c| * K) * |x - y| := by ring

private lemma p3_tau_antitone : Antitone cutoffTau := by
  have hi : Integrable (fun x : ℝ => x ^ 2) (gaussianReal 0 1) := by
    exact (ProbabilityTheory.memLp_id_gaussianReal (μ := 0) (v := 1) 2).integrable_sq
  have hint : ∀ R : ℝ, Integrable (fun x : ℝ => if R < |x| then x ^ 2 else 0)
      (gaussianReal 0 1) := by
    intro R
    refine hi.mono' (Measurable.aestronglyMeasurable ?_) (Eventually.of_forall fun x => ?_)
    · exact Measurable.ite (measurableSet_lt measurable_const measurable_id.abs)
        (by fun_prop) measurable_const
    · rw [Real.norm_eq_abs]
      split_ifs <;> simp [sq_nonneg]
  intro R Q hRQ
  exact integral_mono (hint Q) (hint R) fun x => by
    split_ifs with hQ hR hR
    · exact le_rfl
    · exact False.elim (hR (hRQ.trans_lt hQ))
    · exact sq_nonneg x
    · exact le_rfl

private lemma p3_cut_small (cert : Muon.External.GaussianOpNorm) (γstar CSig : ℝ)
    {m n B : ℕ} (Fp : FrozenParams m n B) (S : SpectralData Fp.C)
    (hS : SizeFin Fp.C B γstar CSig) (ℓ J : ℕ) (Fd : Fin m → ℝ) (Gd : Fin n → ℝ)
    (hF : opNorm (S.uOut * Matrix.diagonal Fd * S.uOutᵀ) ≤ 1)
    (hG : opNorm (S.vIn * Matrix.diagonal Gd * S.vInᵀ) ≤ 1)
    (f g : ℝ → ℝ) (hf : IsOddBddLip f) (hg : IsOddBddLip g) :
    Tendsto (fun k : ℕ => lagRespCut cert γstar CSig Fp.β ℓ J (1 / ((k : ℝ) + 1))
      B S.μ S.lam Fd Gd f g) atTop (𝓝 0) := by
  obtain ⟨L, hL⟩ := hf.2.2
  have hf0 : f 0 = 0 := by have := hf.1 0; simp only [neg_zero] at this; linarith
  have hCS : 0 ≤ CSig := (tx_opNorm_nonneg _).trans hS.2.1
  have hγ := tx_gamma_nonneg Fp γstar CSig hS
  have hD : Tendsto (fun k : ℕ => volDR cert (1 / ((k : ℝ) + 1)) CSig γstar) atTop (𝓝 0) := by
    simpa [volDR] using (tendsto_one_div_add_atTop_nhds_zero_nat.mul_const CSig).mul_const
      (volTStar cert γstar ^ 2)
  apply squeeze_zero_norm (a := fun k : ℕ => γstar * (|L| * volDR cert (1 / ((k : ℝ) + 1)) CSig γstar) * supNorm g)
  · intro k
    rw [Real.norm_eq_abs]
    have hD0 : 0 ≤ volDR cert (1 / ((k : ℝ) + 1)) CSig γstar := by unfold volDR; positivity
    have hb := (lem_app_vol_tree_extension_ii cert γstar CSig Fp S hS ℓ J (1 / ((k : ℝ) + 1))
      _ le_rfl f g (tx_cont_of_lip _ hf).continuousOn (fun x _ => hf.1 x)
      (tx_cont_of_lip _ hg).continuousOn (fun x _ => hg.1 x)).2.1 Fd Gd _ _ rfl rfl hF hG
    have hs : supOn (volDR cert (1 / ((k : ℝ) + 1)) CSig γstar) f ≤
        |L| * volDR cert (1 / ((k : ℝ) + 1)) CSig γstar := by
      apply tx_supOn_le _ _ _ (mul_nonneg (abs_nonneg _) hD0)
      intro x hx
      have h := hL x 0
      simp only [hf0, sub_zero] at h
      exact h.trans ((mul_le_mul_of_nonneg_right (le_abs_self L) (abs_nonneg x)).trans
        (mul_le_mul_of_nonneg_left (abs_le.mpr hx) (abs_nonneg L)))
    have ht := tx_supOn_le (volDR cert (1 / ((k : ℝ) + 1)) CSig γstar) g (supNorm g)
      (tx_supNorm_nonneg g) (fun x _ => tx_le_supNorm g hg x)
    exact hb.trans (mul_le_mul (mul_le_mul_of_nonneg_left hs hγ) ht
      (tx_supOn_nonneg _ _) (mul_nonneg hγ (mul_nonneg (abs_nonneg L) hD0)))
  · simpa using ((hD.const_mul |L|).const_mul γstar).mul_const (supNorm g)

private lemma p3_unit_cut_all (cert : Muon.External.GaussianOpNorm) (γstar CSig : ℝ)
    {m n B : ℕ} (Fp : FrozenParams m n B) (S : SpectralData Fp.C)
    (hS : SizeFin Fp.C B γstar CSig) (ℓ J : ℕ) (R : ℝ) (Fd : Fin m → ℝ) (Gd : Fin n → ℝ)
    (hF : opNorm (S.uOut * Matrix.diagonal Fd * S.uOutᵀ) ≤ 1)
    (hG : opNorm (S.vIn * Matrix.diagonal Gd * S.vInᵀ) ≤ 1)
    (f g : ℝ → ℝ) (hf : IsOddBddLip f) (hg : IsOddBddLip g) :
    |lagResp cert γstar CSig Fp.β ℓ B S.μ S.lam Fd Gd f g -
      lagRespCut cert γstar CSig Fp.β ℓ J R B S.μ S.lam Fd Gd f g| ≤
      Real.sqrt 3 * CSig * γstar ^ (3 / 2 : ℝ) *
        (lipConst f * supNorm g + supNorm f * lipConst g) * cutoffDelta Fp.β J R := by
  by_cases hR : 0 < R
  · exact tx_lagResp_cut cert γstar CSig Fp S hS ℓ Fd Gd hF hG f g hf hg J R hR
  have hR0 : R ≤ 0 := le_of_not_gt hR
  have hz := (tx_nonpos_case cert γstar CSig Fp S ℓ J R hR0 Fd Gd (0 : Mat m m) (0 : Mat n n) f g hf.1 hg.1 0).2
  rw [hz, sub_zero]
  have hl := ((tendsto_const_nhds (x := lagResp cert γstar CSig Fp.β ℓ B S.μ S.lam Fd Gd f g)).sub (p3_cut_small cert γstar CSig Fp S hS ℓ J Fd Gd hF hG f g hf hg)).abs
  simp only [sub_zero] at hl
  apply le_of_tendsto hl
  refine Eventually.of_forall fun k => ?_
  have hq : 0 < 1 / ((k : ℝ) + 1) := by positivity
  have hb := tx_lagResp_cut cert γstar CSig Fp S hS ℓ Fd Gd hF hG f g hf hg J _ hq
  refine hb.trans (mul_le_mul_of_nonneg_left ?_ ?_)
  · unfold cutoffDelta
    exact add_le_add le_rfl (Real.sqrt_le_sqrt (p3_tau_antitone (hR0.trans hq.le)))
  · have hγ := tx_gamma_nonneg Fp γstar CSig hS
    have hCS : 0 ≤ CSig := (tx_opNorm_nonneg _).trans hS.2.1
    have := Real.rpow_nonneg hγ (3 / 2 : ℝ)
    have := tx_lip_nonneg f
    have := tx_lip_nonneg g
    have := tx_supNorm_nonneg f
    have := tx_supNorm_nonneg g
    positivity

/-- `thm:app-vol-lag-kernel`, snapshot `cr-2026-10-23`. Declaration of record. LaTeX, verbatim from `section.tex` (the whole environment):

```latex
\begin{theorem}[Deterministic joint moment response]\label{thm:app-vol-lag-kernel}
Fix a finite dimension, a lag $\ell\ge0$ and diagonal $F,G$. For odd bounded
Lipschitz $f_1,f_2$, the limit
\begin{equation}\label{eqn:app-vol-Phi}
\mathfrak R_\ell[F,G](f_1,f_2)\defeq\lim_{J,R\to\infty}\mathfrak R^{J,R}_\ell[F,G](f_1,f_2),
\end{equation}
with $J$ and $R$ tending to infinity independently, exists, and
\begin{equation}\label{eqn:app-vol-Phi-cutoff}
\begin{aligned}
&\abs{\mathfrak R_\ell[F,G](f_1,f_2)-\mathfrak R^{J,R}_\ell[F,G](f_1,f_2)}\\
&\qquad\le2\sqrt3\,C_\Sigma\gamma_\star^{3/2}\norm F\norm G\big(\operatorname{Lip}(f_1)\norm{f_2}_\infty+\norm{f_1}_\infty\operatorname{Lip}(f_2)\big)\delta_{J,R}.
\end{aligned}
\end{equation}
The response $\mathfrak R_\ell$ is bilinear in $(F,G)$ and in $(f_1,f_2)$, unchanged
under replication, and bounded by $\gamma_\star\norm F\norm G\norm{f_1}_\infty\norm{f_2}_\infty$.
The lag kernels and the filtered lag coefficients are
\begin{equation}\label{eqn:app-vol-lag-kernel}
\mathfrak k_\ell[F,G](s,u)\defeq\mathfrak R_\ell[F,G](\iota_s,\iota_u),\qquad
\overline C_\ell[F,G](\ridge,\ridge')\defeq\mathfrak R_\ell[F,G](\omega_\ridge,\omega_{\ridge'}),
\end{equation}
and $\mathfrak k_\ell\defeq\mathfrak k_\ell[\Sigmaout,\Sigmain]$,
$\overline C_\ell\defeq\overline C_\ell[\Sigmaout,\Sigmain]$. Along every sequence of
dimensions satisfying the size conditions, for every compact
$\mathcal J\subset(0,\infty)$,
\begin{equation}\label{eqn:app-vol-lag-closure}
\begin{gathered}
\sup_{s,u\in\mathcal J}\sup_{F,G}\abs{\EE\,\mathcal K^{F,G}_{s,u}(M^{\mathrm g}_t,M^{\mathrm g}_{t+\ell})-\mathfrak k_\ell[F,G](s,u)}\to0,\\
\sup_{\ridge,\ridge'\in I}\sup_{F,G}\abs{C^{\mathrm g}_\ell[F,G](\ridge,\ridge')-\overline C_\ell[F,G](\ridge,\ridge')}\to0,
\end{gathered}
\end{equation}
the suprema over diagonal $F,G$ of norm at most one. Under
\cref{assum:app-setup-regime} the same holds for the actual model, with
$\EE\,\mathcal K^{F,G}_{s,u}(\Mt,M_{t+\ell})$ and $C_\ell[F,G]$ in place of the
independent quantities.
\end{theorem}
```
-/
theorem thm_app_vol_lag_kernel_cutoff_bound (cert : Muon.External.GaussianOpNorm) (γstar CSig : ℝ)
    {m n B : ℕ} (Fp : FrozenParams m n B) (S : SpectralData Fp.C) (hS : SizeFin Fp.C B γstar CSig)
    (hCSig : 1 ≤ CSig) (ℓ : ℕ) (Fm : Mat m m) (Gm : Mat n n) (Fd : Fin m → ℝ) (Gd : Fin n → ℝ)
    (hFd : Fm = S.uOut * Matrix.diagonal Fd * S.uOutᵀ) (hGd : Gm = S.vIn * Matrix.diagonal Gd * S.vInᵀ)
    (f₁ f₂ : ℝ → ℝ) (hf₁ : IsOddBddLip f₁) (hf₂ : IsOddBddLip f₂) (J : ℕ) (R : ℝ) :
    |lagResp cert γstar CSig Fp.β ℓ B S.μ S.lam Fd Gd f₁ f₂ -
        lagRespCut cert γstar CSig Fp.β ℓ J R B S.μ S.lam Fd Gd f₁ f₂| ≤
      2 * Real.sqrt 3 * CSig * (γstar * Real.sqrt γstar) * opNorm Fm * opNorm Gm *
        (lipConst f₁ * supNorm f₂ + supNorm f₁ * lipConst f₂) * cutoffDelta Fp.β J R := by
  subst hFd hGd
  obtain ⟨F, hF, hFn⟩ := p3_normalize S.uOut S.huOut Fd
  obtain ⟨G, hG, hGn⟩ := p3_normalize S.vIn S.hvIn Gd
  have hb := p3_unit_cut_all cert γstar CSig Fp S hS ℓ J R F G hFn hGn f₁ f₂ hf₁ hf₂
  have hγ := tx_gamma_nonneg Fp γstar CSig hS
  have he : γstar ^ (3 / 2 : ℝ) = γstar * Real.sqrt γstar := by
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add' hγ (by norm_num),
      Real.rpow_one, ← Real.sqrt_eq_rpow]
  rw [he] at hb
  have hs := mul_le_mul_of_nonneg_left hb
    (mul_nonneg (tx_opNorm_nonneg (S.uOut * Matrix.diagonal Fd * S.uOutᵀ))
      (tx_opNorm_nonneg (S.vIn * Matrix.diagonal Gd * S.vInᵀ)))
  conv_lhs =>
    rw [hF, hG, p3_lag_scale cert γstar CSig Fp S hS hCSig ℓ _ _ F G f₁ f₂ hf₁ hf₂,
      p3_cut_scale cert γstar CSig Fp S hS ℓ J R _ _ F G f₁ f₂
        (tx_cont_of_lip _ hf₁) (tx_cont_of_lip _ hf₂)]
  rw [← mul_sub, abs_mul, abs_mul, abs_of_nonneg (tx_opNorm_nonneg _),
    abs_of_nonneg (tx_opNorm_nonneg _)]
  have hp : 0 ≤ opNorm (S.uOut * Matrix.diagonal Fd * S.uOutᵀ) *
      opNorm (S.vIn * Matrix.diagonal Gd * S.vInᵀ) *
        |lagResp cert γstar CSig Fp.β ℓ B S.μ S.lam F G f₁ f₂ -
          lagRespCut cert γstar CSig Fp.β ℓ J R B S.μ S.lam F G f₁ f₂| := by
    exact mul_nonneg (mul_nonneg (tx_opNorm_nonneg _) (tx_opNorm_nonneg _)) (abs_nonneg _)
  nlinarith [hs]

/-- `thm:app-vol-lag-kernel`, snapshot `cr-2026-10-23`. Declaration of record. LaTeX, verbatim from `section.tex` (the whole environment):

```latex
\begin{theorem}[Deterministic joint moment response]\label{thm:app-vol-lag-kernel}
Fix a finite dimension, a lag $\ell\ge0$ and diagonal $F,G$. For odd bounded
Lipschitz $f_1,f_2$, the limit
\begin{equation}\label{eqn:app-vol-Phi}
\mathfrak R_\ell[F,G](f_1,f_2)\defeq\lim_{J,R\to\infty}\mathfrak R^{J,R}_\ell[F,G](f_1,f_2),
\end{equation}
with $J$ and $R$ tending to infinity independently, exists, and
\begin{equation}\label{eqn:app-vol-Phi-cutoff}
\begin{aligned}
&\abs{\mathfrak R_\ell[F,G](f_1,f_2)-\mathfrak R^{J,R}_\ell[F,G](f_1,f_2)}\\
&\qquad\le2\sqrt3\,C_\Sigma\gamma_\star^{3/2}\norm F\norm G\big(\operatorname{Lip}(f_1)\norm{f_2}_\infty+\norm{f_1}_\infty\operatorname{Lip}(f_2)\big)\delta_{J,R}.
\end{aligned}
\end{equation}
The response $\mathfrak R_\ell$ is bilinear in $(F,G)$ and in $(f_1,f_2)$, unchanged
under replication, and bounded by $\gamma_\star\norm F\norm G\norm{f_1}_\infty\norm{f_2}_\infty$.
The lag kernels and the filtered lag coefficients are
\begin{equation}\label{eqn:app-vol-lag-kernel}
\mathfrak k_\ell[F,G](s,u)\defeq\mathfrak R_\ell[F,G](\iota_s,\iota_u),\qquad
\overline C_\ell[F,G](\ridge,\ridge')\defeq\mathfrak R_\ell[F,G](\omega_\ridge,\omega_{\ridge'}),
\end{equation}
and $\mathfrak k_\ell\defeq\mathfrak k_\ell[\Sigmaout,\Sigmain]$,
$\overline C_\ell\defeq\overline C_\ell[\Sigmaout,\Sigmain]$. Along every sequence of
dimensions satisfying the size conditions, for every compact
$\mathcal J\subset(0,\infty)$,
\begin{equation}\label{eqn:app-vol-lag-closure}
\begin{gathered}
\sup_{s,u\in\mathcal J}\sup_{F,G}\abs{\EE\,\mathcal K^{F,G}_{s,u}(M^{\mathrm g}_t,M^{\mathrm g}_{t+\ell})-\mathfrak k_\ell[F,G](s,u)}\to0,\\
\sup_{\ridge,\ridge'\in I}\sup_{F,G}\abs{C^{\mathrm g}_\ell[F,G](\ridge,\ridge')-\overline C_\ell[F,G](\ridge,\ridge')}\to0,
\end{gathered}
\end{equation}
the suprema over diagonal $F,G$ of norm at most one. Under
\cref{assum:app-setup-regime} the same holds for the actual model, with
$\EE\,\mathcal K^{F,G}_{s,u}(\Mt,M_{t+\ell})$ and $C_\ell[F,G]$ in place of the
independent quantities.
\end{theorem}
```
-/
theorem thm_app_vol_lag_kernel_bilinear_bound_replication (cert : Muon.External.GaussianOpNorm)
    (γstar CSig : ℝ) {m n B : ℕ} (Fp : FrozenParams m n B) (S : SpectralData Fp.C)
    (hS : SizeFin Fp.C B γstar CSig) (hCSig : 1 ≤ CSig) (ℓ : ℕ)
    (f₁ f₂ : ℝ → ℝ) (hf₁ : IsOddBddLip f₁) (hf₂ : IsOddBddLip f₂) :
    -- (a) the bound, for all diagonal tests (the norms enter as factors)
    (∀ (Fm : Mat m m) (Gm : Mat n n) (Fd : Fin m → ℝ) (Gd : Fin n → ℝ),
      Fm = S.uOut * Matrix.diagonal Fd * S.uOutᵀ → Gm = S.vIn * Matrix.diagonal Gd * S.vInᵀ →
      |lagResp cert γstar CSig Fp.β ℓ B S.μ S.lam Fd Gd f₁ f₂| ≤
        γstar * opNorm Fm * opNorm Gm * supNorm f₁ * supNorm f₂) ∧
    -- (b) linearity in the diagonal entries of the tests
    (∀ (c : ℝ) (Fd₁ Fd₂ : Fin m → ℝ) (Gd : Fin n → ℝ),
      lagResp cert γstar CSig Fp.β ℓ B S.μ S.lam (fun i => c * Fd₁ i + Fd₂ i) Gd f₁ f₂ =
        c * lagResp cert γstar CSig Fp.β ℓ B S.μ S.lam Fd₁ Gd f₁ f₂ +
          lagResp cert γstar CSig Fp.β ℓ B S.μ S.lam Fd₂ Gd f₁ f₂) ∧
    (∀ (c : ℝ) (Fd : Fin m → ℝ) (Gd₁ Gd₂ : Fin n → ℝ),
      lagResp cert γstar CSig Fp.β ℓ B S.μ S.lam Fd (fun j => c * Gd₁ j + Gd₂ j) f₁ f₂ =
        c * lagResp cert γstar CSig Fp.β ℓ B S.μ S.lam Fd Gd₁ f₁ f₂ +
          lagResp cert γstar CSig Fp.β ℓ B S.μ S.lam Fd Gd₂ f₁ f₂) ∧
    -- (c) linearity in the first filter (odd, bounded, Lipschitz)
    (∀ (c : ℝ) (f₁' : ℝ → ℝ), IsOddBddLip f₁' → ∀ (Fd : Fin m → ℝ) (Gd : Fin n → ℝ),
      lagResp cert γstar CSig Fp.β ℓ B S.μ S.lam Fd Gd (fun x => f₁ x + c * f₁' x) f₂ =
        lagResp cert γstar CSig Fp.β ℓ B S.μ S.lam Fd Gd f₁ f₂ +
          c * lagResp cert γstar CSig Fp.β ℓ B S.μ S.lam Fd Gd f₁' f₂) ∧
    -- (c') linearity in the second filter (odd, bounded, Lipschitz)
    (∀ (c : ℝ) (f₂' : ℝ → ℝ), IsOddBddLip f₂' → ∀ (Fd : Fin m → ℝ) (Gd : Fin n → ℝ),
      lagResp cert γstar CSig Fp.β ℓ B S.μ S.lam Fd Gd f₁ (fun x => f₂ x + c * f₂' x) =
        lagResp cert γstar CSig Fp.β ℓ B S.μ S.lam Fd Gd f₁ f₂ +
          c * lagResp cert γstar CSig Fp.β ℓ B S.μ S.lam Fd Gd f₁ f₂') ∧
    -- (d) invariance under replication (eigenvalues repeated N times, batch N * B)
    (∀ (N : ℕ), 0 < N → ∀ (Fd : Fin m → ℝ) (Gd : Fin n → ℝ),
      lagResp cert γstar CSig Fp.β ℓ (N * B) (replVec N S.μ) (replVec N S.lam)
          (replVec N Fd) (replVec N Gd) f₁ f₂ =
        lagResp cert γstar CSig Fp.β ℓ B S.μ S.lam Fd Gd f₁ f₂) := by
  have lim := fun (f g : ℝ → ℝ) (hf : IsOddBddLip f) (hg : IsOddBddLip g) F G =>
    thm_app_vol_lag_kernel_exists cert γstar CSig Fp S hS hCSig ℓ _ _ F G rfl rfl f g hf hg
  have ext := fun (p : ℕ × ℝ) => lem_app_vol_tree_extension_ii cert γstar CSig Fp S hS ℓ p.1 p.2
    _ le_rfl f₁ f₂ (tx_cont_of_lip _ hf₁).continuousOn (fun x _ => hf₁.1 x)
    (tx_cont_of_lip _ hf₂).continuousOn (fun x _ => hf₂.1 x)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro Fm Gm Fd Gd hFd hGd
    subst hFd hGd
    obtain ⟨F, hF, hFn⟩ := p3_normalize S.uOut S.huOut Fd
    obtain ⟨G, hG, hGn⟩ := p3_normalize S.vIn S.hvIn Gd
    have hb := p3_unit_bound cert γstar CSig Fp S hS ℓ F G hFn hGn f₁ f₂ hf₁ hf₂
    conv_lhs => rw [hF, hG, p3_lag_scale cert γstar CSig Fp S hS hCSig ℓ _ _ F G f₁ f₂ hf₁ hf₂]
    rw [abs_mul, abs_mul, abs_of_nonneg (tx_opNorm_nonneg _), abs_of_nonneg (tx_opNorm_nonneg _)]
    convert mul_le_mul_of_nonneg_left hb
      (mul_nonneg (tx_opNorm_nonneg (S.uOut * Matrix.diagonal Fd * S.uOutᵀ))
        (tx_opNorm_nonneg (S.vIn * Matrix.diagonal Gd * S.vInᵀ))) using 1 <;> ring
  · intro c F₁ F₂ G
    apply tendsto_nhds_unique (lim f₁ f₂ hf₁ hf₂ _ _)
    apply (((lim f₁ f₂ hf₁ hf₂ F₁ G).const_mul c).add (lim f₁ f₂ hf₁ hf₂ F₂ G)).congr
    intro p
    exact ((ext p).2.2.2.1 c F₁ F₂ G).symm
  · intro c F G₁ G₂
    apply tendsto_nhds_unique (lim f₁ f₂ hf₁ hf₂ _ _)
    apply (((lim f₁ f₂ hf₁ hf₂ F G₁).const_mul c).add (lim f₁ f₂ hf₁ hf₂ F G₂)).congr
    intro p
    exact ((ext p).2.2.2.2.1 c F G₁ G₂).symm
  · intro c f' hf' F G
    apply tendsto_nhds_unique (lim _ _ (p3_add_filter f₁ f' hf₁ hf' c) hf₂ F G)
    apply ((lim f₁ f₂ hf₁ hf₂ F G).add ((lim f' f₂ hf' hf₂ F G).const_mul c)).congr
    intro p
    exact ((ext p).2.2.2.2.2.1 c f' (tx_cont_of_lip _ hf').continuousOn
      (fun x _ => hf'.1 x) F G).symm
  · intro c g' hg' F G
    apply tendsto_nhds_unique (lim _ _ hf₁ (p3_add_filter f₂ g' hf₂ hg' c) F G)
    apply ((lim f₁ f₂ hf₁ hf₂ F G).add ((lim f₁ g' hf₁ hg' F G).const_mul c)).congr
    intro p
    exact ((ext p).2.2.2.2.2.2.1 c g' (tx_cont_of_lip _ hg').continuousOn
      (fun x _ => hg'.1 x) F G).symm
  · intro N hN F G
    unfold lagResp
    apply congrArg (limUnder (atTop ×ˢ atTop : Filter (ℕ × ℝ)))
    funext p
    exact tx_lagCut_repl cert γstar CSig Fp S hS ℓ p.1 p.2 f₁ f₂
      (tx_cont_of_lip _ hf₁) (tx_cont_of_lip _ hf₂) hf₁.1 hf₂.1 N hN F G

/-- `thm:app-vol-lag-kernel`, snapshot `cr-2026-10-23`. Declaration of record. LaTeX, verbatim from `section.tex` (the whole environment):

```latex
\begin{theorem}[Deterministic joint moment response]\label{thm:app-vol-lag-kernel}
Fix a finite dimension, a lag $\ell\ge0$ and diagonal $F,G$. For odd bounded
Lipschitz $f_1,f_2$, the limit
\begin{equation}\label{eqn:app-vol-Phi}
\mathfrak R_\ell[F,G](f_1,f_2)\defeq\lim_{J,R\to\infty}\mathfrak R^{J,R}_\ell[F,G](f_1,f_2),
\end{equation}
with $J$ and $R$ tending to infinity independently, exists, and
\begin{equation}\label{eqn:app-vol-Phi-cutoff}
\begin{aligned}
&\abs{\mathfrak R_\ell[F,G](f_1,f_2)-\mathfrak R^{J,R}_\ell[F,G](f_1,f_2)}\\
&\qquad\le2\sqrt3\,C_\Sigma\gamma_\star^{3/2}\norm F\norm G\big(\operatorname{Lip}(f_1)\norm{f_2}_\infty+\norm{f_1}_\infty\operatorname{Lip}(f_2)\big)\delta_{J,R}.
\end{aligned}
\end{equation}
The response $\mathfrak R_\ell$ is bilinear in $(F,G)$ and in $(f_1,f_2)$, unchanged
under replication, and bounded by $\gamma_\star\norm F\norm G\norm{f_1}_\infty\norm{f_2}_\infty$.
The lag kernels and the filtered lag coefficients are
\begin{equation}\label{eqn:app-vol-lag-kernel}
\mathfrak k_\ell[F,G](s,u)\defeq\mathfrak R_\ell[F,G](\iota_s,\iota_u),\qquad
\overline C_\ell[F,G](\ridge,\ridge')\defeq\mathfrak R_\ell[F,G](\omega_\ridge,\omega_{\ridge'}),
\end{equation}
and $\mathfrak k_\ell\defeq\mathfrak k_\ell[\Sigmaout,\Sigmain]$,
$\overline C_\ell\defeq\overline C_\ell[\Sigmaout,\Sigmain]$. Along every sequence of
dimensions satisfying the size conditions, for every compact
$\mathcal J\subset(0,\infty)$,
\begin{equation}\label{eqn:app-vol-lag-closure}
\begin{gathered}
\sup_{s,u\in\mathcal J}\sup_{F,G}\abs{\EE\,\mathcal K^{F,G}_{s,u}(M^{\mathrm g}_t,M^{\mathrm g}_{t+\ell})-\mathfrak k_\ell[F,G](s,u)}\to0,\\
\sup_{\ridge,\ridge'\in I}\sup_{F,G}\abs{C^{\mathrm g}_\ell[F,G](\ridge,\ridge')-\overline C_\ell[F,G](\ridge,\ridge')}\to0,
\end{gathered}
\end{equation}
the suprema over diagonal $F,G$ of norm at most one. Under
\cref{assum:app-setup-regime} the same holds for the actual model, with
$\EE\,\mathcal K^{F,G}_{s,u}(\Mt,M_{t+\ell})$ and $C_\ell[F,G]$ in place of the
independent quantities.
\end{theorem}
```
-/
theorem thm_app_vol_lag_kernel_closure_indep (cert : Muon.External.GaussianOpNorm)
    (γstar CSig γout γin : ℝ) (hCSig : 1 ≤ CSig) (ϱlo ϱhi : ℝ) (hϱ : 0 < ϱlo ∧ ϱlo ≤ ϱhi)
    (m n B : ℕ → ℕ) (Fp : ∀ k : ℕ, FrozenParams (m k) (n k) (B k))
    (Sp : ∀ k : ℕ, SpectralData (Fp k).C) (hSize : SizeSeq (B := B) (fun k => (Fp k).C) γstar CSig γout γin)
    (b : ℝ) (hb : b < 1) (hβ : ∀ k, (Fp k).β ≤ b)
    (ℓ : ℕ) (J : Set ℝ) (hJ : IsCompact J) (hJpos : J ⊆ Set.Ioi 0) :
    -- (a) kernels on the compact set J of the resolvent filters, uniform in the tests
    (∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, ∀ t : ℤ, ∀ s ∈ J, ∀ u ∈ J,
      ∀ (Fd : Fin (m k) → ℝ) (Gd : Fin (n k) → ℝ)
      (Fm : Mat (m k) (m k)) (Gm : Mat (n k) (n k)),
      Fm = (Sp k).uOut * Matrix.diagonal Fd * (Sp k).uOutᵀ →
      Gm = (Sp k).vIn * Matrix.diagonal Gd * (Sp k).vInᵀ →
      opNorm Fm ≤ 1 → opNorm Gm ≤ 1 →
      |(∫ ω, contractionRes (B k) Fm Gm s u (def_app_vol_product (Fp k) ω t)
            (def_app_vol_product (Fp k) ω (t + (ℓ : ℤ)))
          ∂(indepSpaceLaw (m k) (n k) (B k))) -
        lagResp cert γstar CSig (Fp k).β ℓ (B k) (Sp k).μ (Sp k).lam Fd Gd (iotaF s) (iotaF u)| ≤
          ε) ∧
    -- (b) tested lag covariances on the regime interval I, uniform in the tests
    (∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, ∀ t : ℤ, ∀ ϱ ∈ Set.Icc ϱlo ϱhi, ∀ ϱ' ∈ Set.Icc ϱlo ϱhi,
      ∀ (Fd : Fin (m k) → ℝ) (Gd : Fin (n k) → ℝ) (Fm : Mat (m k) (m k)) (Gm : Mat (n k) (n k)),
      Fm = (Sp k).uOut * Matrix.diagonal Fd * (Sp k).uOutᵀ →
      Gm = (Sp k).vIn * Matrix.diagonal Gd * (Sp k).vInᵀ →
      opNorm Fm ≤ 1 → opNorm Gm ≤ 1 →
      |(B k : ℝ)⁻¹ * (∫ ω, Matrix.trace (Fm * indepUpd (Fp k) ϱ ω t * Gm *
            (indepUpd (Fp k) ϱ' ω (t + (ℓ : ℤ)))ᵀ) ∂(indepSpaceLaw (m k) (n k) (B k))) -
        lagResp cert γstar CSig (Fp k).β ℓ (B k) (Sp k).μ (Sp k).lam Fd Gd (omegaF ϱ) (omegaF ϱ')| ≤
          ε) := by
  have hgamma : 0 ≤ γstar := tx_gamma_nonneg (Fp 0) γstar CSig (hSize.1 0)
  have hCS0 : 0 ≤ CSig := by linarith
  refine ⟨?_, ?_⟩
  · rcases J.eq_empty_or_nonempty with hJe | hJne
    · intro ε hε
      exact Eventually.of_forall fun k t s hs => (by simp [hJe] at hs)
    · obtain ⟨s₀, hs₀J, hmin⟩ := hJ.exists_isMinOn hJne continuous_id.continuousOn
      have hs₀pos : 0 < s₀ := hJpos hs₀J
      set N : ℝ := 1 / (2 * Real.sqrt s₀)
      set L : ℝ := 1 / s₀
      set C : ℝ := Real.sqrt 3 * CSig * γstar ^ (3 / 2 : ℝ) * (L * N + N * L)
      have hN : 0 ≤ N := by simp only [N]; positivity
      have hL : 0 ≤ L := by simp only [L]; positivity
      have hC : 0 ≤ C := by simp only [C]; positivity
      intro ε hε
      set θ : ℝ := ε / (4 * (C + 1))
      have hθ : 0 < θ := by simp only [θ]; positivity
      obtain ⟨j, r, hr, hδ⟩ := p4_uniform_delta Fp b hb hβ θ hθ
      have hmid := (lem_app_vol_tree_extension_iii_unif cert γstar CSig γout γin
        m n B Fp Sp hSize ℓ j r J hJ hJpos ϱlo ϱhi hϱ).1 (ε / 2) (by positivity)
      filter_upwards [hmid] with k hk
      intro t s hs u hu Fd Gd Fm Gm hFm hGm hF hG
      have hspos : 0 < s := hJpos hs
      have hupos : 0 < u := hJpos hu
      have hsle : s₀ ≤ s := hmin hs
      have hule : s₀ ≤ u := hmin hu
      have hss := lem_app_vol_sharp_ii hspos one_pos
      have hus := lem_app_vol_sharp_ii hupos one_pos
      have hsN : supNorm (iotaF s) ≤ N := by
        rw [hss.2.2.1]
        simp only [N]
        exact one_div_le_one_div_of_le (by positivity) (by
          have := Real.sqrt_le_sqrt hsle
          linarith)
      have huN : supNorm (iotaF u) ≤ N := by
        rw [hus.2.2.1]
        simp only [N]
        exact one_div_le_one_div_of_le (by positivity) (by
          have := Real.sqrt_le_sqrt hule
          linarith)
      have hsL : lipConst (iotaF s) ≤ L := by
        refine hss.2.2.2.1.trans ?_
        simp only [L]
        exact one_div_le_one_div_of_le hs₀pos hsle
      have huL : lipConst (iotaF u) ≤ L := by
        refine hus.2.2.2.1.trans ?_
        simp only [L]
        exact one_div_le_one_div_of_le hs₀pos hule
      have hcoef := p4_cut_coeff_le γstar CSig L N hgamma hCS0 hL hN
        (iotaF s) (iotaF u) hsL huL hsN huN
      have hδ0 : 0 ≤ cutoffDelta (Fp k).β j r :=
        add_nonneg (pow_nonneg (Fp k).hβ.1 _) (Real.sqrt_nonneg _)
      have hsmall : Real.sqrt 3 * CSig * γstar ^ (3 / 2 : ℝ) *
          (lipConst (iotaF s) * supNorm (iotaF u) +
            supNorm (iotaF s) * lipConst (iotaF u)) * cutoffDelta (Fp k).β j r ≤ ε / 4 := by
        refine (mul_le_mul_of_nonneg_right hcoef hδ0).trans ?_
        change C * cutoffDelta (Fp k).β j r ≤ ε / 4
        refine (mul_le_mul_of_nonneg_left (hδ k).le hC).trans ?_
        simp only [θ]
        rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num : (0 : ℝ) < 4)]
        nlinarith
      have hc := lem_app_vol_cutoff_ii (Fp k) ℓ j r γstar CSig hr (hSize.1 k) t Fm Gm
        hF hG (iotaF s) (iotaF u) hss.1 hus.1
      have hl := tx_lagResp_cut cert γstar CSig (Fp k) (Sp k) (hSize.1 k) ℓ Fd Gd
        (by simpa [hFm] using hF) (by simpa [hGm] using hG)
        (iotaF s) (iotaF u) hss.1 hus.1 j r hr
      have hm := hk t s hs u hu Fd Gd Fm Gm hFm hGm hF hG
      have htri₁ := abs_sub_le
        (∫ ω, contractionRes (B k) Fm Gm s u (def_app_vol_product (Fp k) ω t)
          (def_app_vol_product (Fp k) ω (t + (ℓ : ℤ))) ∂(indepSpaceLaw (m k) (n k) (B k)))
        (∫ ω, contractionRes (B k) Fm Gm s u (cutoffMat (Fp k) ℓ j r t 1 ω)
          (cutoffMat (Fp k) ℓ j r t 2 ω) ∂(indepSpaceLaw (m k) (n k) (B k)))
        (lagResp cert γstar CSig (Fp k).β ℓ (B k) (Sp k).μ (Sp k).lam Fd Gd
          (iotaF s) (iotaF u))
      have htri₂ := abs_sub_le
        (∫ ω, contractionRes (B k) Fm Gm s u (cutoffMat (Fp k) ℓ j r t 1 ω)
          (cutoffMat (Fp k) ℓ j r t 2 ω) ∂(indepSpaceLaw (m k) (n k) (B k)))
        (lagRespCut cert γstar CSig (Fp k).β ℓ j r (B k) (Sp k).μ (Sp k).lam Fd Gd
          (iotaF s) (iotaF u))
        (lagResp cert γstar CSig (Fp k).β ℓ (B k) (Sp k).μ (Sp k).lam Fd Gd
          (iotaF s) (iotaF u))
      have hlsmall : |lagRespCut cert γstar CSig (Fp k).β ℓ j r (B k)
          (Sp k).μ (Sp k).lam Fd Gd (iotaF s) (iotaF u) -
          lagResp cert γstar CSig (Fp k).β ℓ (B k) (Sp k).μ (Sp k).lam Fd Gd
            (iotaF s) (iotaF u)| ≤ ε / 4 := by
        rw [abs_sub_comm]
        exact hl.trans hsmall
      unfold contractionRes at hm htri₁ htri₂ ⊢
      linarith
  · set N : ℝ := 1
    set L : ℝ := 1 / Real.sqrt ϱlo
    set C : ℝ := Real.sqrt 3 * CSig * γstar ^ (3 / 2 : ℝ) * (L * N + N * L)
    have hN : 0 ≤ N := by simp only [N]; norm_num
    have hL : 0 ≤ L := by simp only [L]; positivity
    have hC : 0 ≤ C := by simp only [C]; positivity
    intro ε hε
    set θ : ℝ := ε / (4 * (C + 1))
    have hθ : 0 < θ := by simp only [θ]; positivity
    obtain ⟨j, r, hr, hδ⟩ := p4_uniform_delta Fp b hb hβ θ hθ
    have hmid := (lem_app_vol_tree_extension_iii_unif cert γstar CSig γout γin
      m n B Fp Sp hSize ℓ j r J hJ hJpos ϱlo ϱhi hϱ).2 (ε / 2) (by positivity)
    filter_upwards [hmid] with k hk
    intro t ϱ hϱm ϱ' hϱm' Fd Gd Fm Gm hFm hGm hF hG
    have hϱpos : 0 < ϱ := hϱ.1.trans_le hϱm.1
    have hϱpos' : 0 < ϱ' := hϱ.1.trans_le hϱm'.1
    have hϱs := lem_app_vol_sharp_ii one_pos hϱpos
    have hϱs' := lem_app_vol_sharp_ii one_pos hϱpos'
    have hϱN : supNorm (omegaF ϱ) ≤ N := by
      rw [hϱs.2.2.2.2.1]
    have hϱN' : supNorm (omegaF ϱ') ≤ N := by
      rw [hϱs'.2.2.2.2.1]
    have hϱL : lipConst (omegaF ϱ) ≤ L := by
      refine hϱs.2.2.2.2.2.trans ?_
      simp only [L]
      exact one_div_le_one_div_of_le (Real.sqrt_pos.mpr hϱ.1) (Real.sqrt_le_sqrt hϱm.1)
    have hϱL' : lipConst (omegaF ϱ') ≤ L := by
      refine hϱs'.2.2.2.2.2.trans ?_
      simp only [L]
      exact one_div_le_one_div_of_le (Real.sqrt_pos.mpr hϱ.1) (Real.sqrt_le_sqrt hϱm'.1)
    have hcoef := p4_cut_coeff_le γstar CSig L N hgamma hCS0 hL hN
      (omegaF ϱ) (omegaF ϱ') hϱL hϱL' hϱN hϱN'
    have hδ0 : 0 ≤ cutoffDelta (Fp k).β j r :=
      add_nonneg (pow_nonneg (Fp k).hβ.1 _) (Real.sqrt_nonneg _)
    have hsmall : Real.sqrt 3 * CSig * γstar ^ (3 / 2 : ℝ) *
        (lipConst (omegaF ϱ) * supNorm (omegaF ϱ') +
          supNorm (omegaF ϱ) * lipConst (omegaF ϱ')) * cutoffDelta (Fp k).β j r ≤ ε / 4 := by
      refine (mul_le_mul_of_nonneg_right hcoef hδ0).trans ?_
      change C * cutoffDelta (Fp k).β j r ≤ ε / 4
      refine (mul_le_mul_of_nonneg_left (hδ k).le hC).trans ?_
      simp only [θ]
      rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num : (0 : ℝ) < 4)]
      nlinarith
    have hc := lem_app_vol_cutoff_ii (Fp k) ℓ j r γstar CSig hr (hSize.1 k) t Fm Gm
      hF hG (omegaF ϱ) (omegaF ϱ') hϱs.2.1 hϱs'.2.1
    have hl := tx_lagResp_cut cert γstar CSig (Fp k) (Sp k) (hSize.1 k) ℓ Fd Gd
      (by simpa [hFm] using hF) (by simpa [hGm] using hG)
      (omegaF ϱ) (omegaF ϱ') hϱs.2.1 hϱs'.2.1 j r hr
    have hm := hk t ϱ hϱm ϱ' hϱm' Fd Gd Fm Gm hFm hGm hF hG
    have htri₁ := abs_sub_le
      (∫ ω, contraction (B k) Fm Gm (omegaF ϱ) (omegaF ϱ')
        (def_app_vol_product (Fp k) ω t) (def_app_vol_product (Fp k) ω (t + (ℓ : ℤ)))
        ∂(indepSpaceLaw (m k) (n k) (B k)))
      (∫ ω, contraction (B k) Fm Gm (omegaF ϱ) (omegaF ϱ')
        (cutoffMat (Fp k) ℓ j r t 1 ω) (cutoffMat (Fp k) ℓ j r t 2 ω)
        ∂(indepSpaceLaw (m k) (n k) (B k)))
      (lagResp cert γstar CSig (Fp k).β ℓ (B k) (Sp k).μ (Sp k).lam Fd Gd
        (omegaF ϱ) (omegaF ϱ'))
    have htri₂ := abs_sub_le
      (∫ ω, contraction (B k) Fm Gm (omegaF ϱ) (omegaF ϱ')
        (cutoffMat (Fp k) ℓ j r t 1 ω) (cutoffMat (Fp k) ℓ j r t 2 ω)
        ∂(indepSpaceLaw (m k) (n k) (B k)))
      (lagRespCut cert γstar CSig (Fp k).β ℓ j r (B k) (Sp k).μ (Sp k).lam Fd Gd
        (omegaF ϱ) (omegaF ϱ'))
      (lagResp cert γstar CSig (Fp k).β ℓ (B k) (Sp k).μ (Sp k).lam Fd Gd
        (omegaF ϱ) (omegaF ϱ'))
    have hlsmall : |lagRespCut cert γstar CSig (Fp k).β ℓ j r (B k)
        (Sp k).μ (Sp k).lam Fd Gd (omegaF ϱ) (omegaF ϱ') -
        lagResp cert γstar CSig (Fp k).β ℓ (B k) (Sp k).μ (Sp k).lam Fd Gd
          (omegaF ϱ) (omegaF ϱ')| ≤ ε / 4 := by
      rw [abs_sub_comm]
      exact hl.trans hsmall
    have hclose : |(∫ ω, contraction (B k) Fm Gm (omegaF ϱ) (omegaF ϱ')
          (def_app_vol_product (Fp k) ω t) (def_app_vol_product (Fp k) ω (t + (ℓ : ℤ)))
          ∂(indepSpaceLaw (m k) (n k) (B k))) -
        lagResp cert γstar CSig (Fp k).β ℓ (B k) (Sp k).μ (Sp k).lam Fd Gd
          (omegaF ϱ) (omegaF ϱ')| ≤ ε := by
      linarith
    have heq : (B k : ℝ)⁻¹ * (∫ ω, Matrix.trace (Fm * indepUpd (Fp k) ϱ ω t * Gm *
          (indepUpd (Fp k) ϱ' ω (t + (ℓ : ℤ)))ᵀ) ∂(indepSpaceLaw (m k) (n k) (B k))) =
        ∫ ω, contraction (B k) Fm Gm (omegaF ϱ) (omegaF ϱ')
          (def_app_vol_product (Fp k) ω t) (def_app_vol_product (Fp k) ω (t + (ℓ : ℤ)))
          ∂(indepSpaceLaw (m k) (n k) (B k)) := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with ω
      unfold contraction indepUpd
      rw [eqn_app_vol_filters_sharp_ii hϱpos, eqn_app_vol_filters_sharp_ii hϱpos']
    rw [heq]
    exact hclose

private lemma p4_borel (m n : ℕ) : BorelSpace (Mat m n) :=
  inferInstanceAs (BorelSpace (Fin m → Fin n → ℝ))

private lemma p4_sc (m n : ℕ) : SecondCountableTopology (Mat m n) :=
  inferInstanceAs (SecondCountableTopology (Fin m → Fin n → ℝ))

private lemma p4_batch_meas {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {m n B : ℕ} (F : FrozenParams m n B) (S : FrozenSamples P m n B) (s : ℤ) :
    Measurable (frozenBatchG F S s) := by
  haveI := p4_borel m n
  haveI := p4_sc m n
  unfold frozenBatchG
  refine Measurable.const_smul ?_ ((B : ℝ))⁻¹
  refine Finset.measurable_sum _ fun a _ => ?_
  have hc : Continuous (fun p : Vec m × Vec n =>
      (dotProduct p.1 (Matrix.mulVec F.A p.2)) • (rOut F.C * outer p.1 p.2 * rIn F.C)) := by
    fun_prop
  exact hc.measurable.comp (S.meas s a)

private lemma p4_tsum_meas {Ω : Type*} [MeasurableSpace Ω] {m n : ℕ}
    (f : ℕ → Ω → Mat m n) (hf : ∀ j, Measurable (f j)) : Measurable (fun ω => ∑' j, f j ω) := by
  haveI : TopologicalSpace.IsCompletelyPseudoMetrizableSpace (Mat m n) :=
    inferInstanceAs (TopologicalSpace.IsCompletelyPseudoMetrizableSpace (Fin m → Fin n → ℝ))
  haveI : SecondCountableTopology (Mat m n) :=
    inferInstanceAs (SecondCountableTopology (Fin m → Fin n → ℝ))
  exact Measurable.tsum hf

private lemma p4_buf_meas {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {m n B : ℕ} (F : FrozenParams m n B) (S : FrozenSamples P m n B) (t : ℤ) :
    Measurable (frozenBuf F S t) := by
  unfold frozenBuf
  exact p4_tsum_meas _ fun j => (p4_batch_meas F S _).const_smul (emaW F.β j)

private lemma p4_Q_meas {m n : ℕ} {ϱ : ℝ} (hϱ : 0 ≤ ϱ) :
    Measurable (fun K : Mat m n => Q ϱ K) :=
  (measurable_Q (m := m) (n := n)).comp
    ((measurable_const (a := (⟨ϱ, hϱ⟩ : Set.Ici (0 : ℝ)))).prodMk measurable_id)

private lemma p4_stat {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    {P : Measure Ω} (X : ℤ → Ω → E) (hst : StrictlyStationary P X)
    (Φ : (ℤ → E) → ℝ) (hΦ : Measurable Φ) (k : ℤ) :
    ∫ ω, Φ (fun t => X (t + k) ω) ∂P = ∫ ω, Φ (fun t => X t ω) ∂P := by
  have hsh : Measurable (fun x : ℤ → E => fun t => x (t + k)) :=
    measurable_pi_iff.mpr (fun t => measurable_pi_apply (t + k))
  have h1 : AEMeasurable (fun ω t => X (t + k) ω) P := hsh.comp_aemeasurable hst.1
  calc ∫ ω, Φ (fun t => X (t + k) ω) ∂P
      = ∫ x, Φ x ∂(P.map (fun ω t => X (t + k) ω)) :=
        (integral_map h1 hΦ.aestronglyMeasurable).symm
    _ = ∫ x, Φ x ∂(P.map (fun ω t => X t ω)) := by rw [hst.2 k]
    _ = ∫ ω, Φ (fun t => X t ω) ∂P := integral_map hst.1 hΦ.aestronglyMeasurable

private lemma p4_mean_shift {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {m n B : ℕ} (F : FrozenParams m n B)
    (S : FrozenSamples P m n B) {ϱ : ℝ} (hϱ : 0 ≤ ϱ) (s k : ℤ) :
    mean P (frozenUpd F S ϱ (s + k)) = mean P (frozenUpd F S ϱ s) := by
  haveI := p4_borel m n
  haveI := p4_sc m n
  have hst := (lem_app_setup_ema_law_ii F S).2
  ext i j
  simp only [mean, Matrix.of_apply]
  have h := p4_stat (frozenBuf F S) hst (fun x => Q ϱ (x s) i j) (by
    have h1 : Measurable (fun x : ℤ → Mat m n => Q ϱ (x s)) :=
      (p4_Q_meas hϱ).comp (measurable_pi_apply s)
    exact (measurable_pi_apply j).comp ((measurable_pi_apply i).comp h1)) k
  simpa [frozenUpd] using h

private lemma p4_fro_add {m n : ℕ} (A D : Mat m n) : fro (A + D) ≤ fro A + fro D := by
  open scoped Matrix.Norms.Frobenius in
  rw [fro_eq_norm, fro_eq_norm, fro_eq_norm]
  exact norm_add_le _ _

private lemma p4_le_biSup {f : ℝ → ℝ} {I : Set ℝ} (hb : BddAbove (f '' I))
    {s : ℝ} (hs : s ∈ I) : f s ≤ ⨆ s ∈ I, f s := by
  obtain ⟨b, hb'⟩ := hb
  have hbdd : BddAbove (Set.range fun s => ⨆ (_ : s ∈ I), f s) := by
    refine ⟨max b 0, ?_⟩
    rintro _ ⟨s', rfl⟩
    show (⨆ (_ : s' ∈ I), f s') ≤ max b 0
    by_cases hs' : s' ∈ I
    · rw [ciSup_pos hs']
      exact le_max_of_le_left (hb' ⟨s', hs', rfl⟩)
    · haveI : IsEmpty (s' ∈ I) := ⟨hs'⟩
      rw [Real.iSup_of_isEmpty]
      exact le_max_right _ _
  refine le_ciSup_of_le hbdd s ?_
  rw [ciSup_pos hs]

private lemma p4_diag_symm {m : ℕ} (U : Mat m m) (d : Fin m → ℝ) :
    (U * Matrix.diagonal d * Uᵀ)ᵀ = U * Matrix.diagonal d * Uᵀ := by
  have hd : (Matrix.diagonal d)ᵀ = Matrix.diagonal d := by
    ext i j
    by_cases h : i = j
    · subst j
      rfl
    · simp [Matrix.transpose_apply, Matrix.diagonal, h, Ne.symm h]
  rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, hd,
    Matrix.mul_assoc]

/-- `thm:app-vol-lag-kernel`, snapshot `cr-2026-10-23`. Declaration of record. LaTeX, verbatim from `section.tex` (the whole environment):

```latex
\begin{theorem}[Deterministic joint moment response]\label{thm:app-vol-lag-kernel}
Fix a finite dimension, a lag $\ell\ge0$ and diagonal $F,G$. For odd bounded
Lipschitz $f_1,f_2$, the limit
\begin{equation}\label{eqn:app-vol-Phi}
\mathfrak R_\ell[F,G](f_1,f_2)\defeq\lim_{J,R\to\infty}\mathfrak R^{J,R}_\ell[F,G](f_1,f_2),
\end{equation}
with $J$ and $R$ tending to infinity independently, exists, and
\begin{equation}\label{eqn:app-vol-Phi-cutoff}
\begin{aligned}
&\abs{\mathfrak R_\ell[F,G](f_1,f_2)-\mathfrak R^{J,R}_\ell[F,G](f_1,f_2)}\\
&\qquad\le2\sqrt3\,C_\Sigma\gamma_\star^{3/2}\norm F\norm G\big(\operatorname{Lip}(f_1)\norm{f_2}_\infty+\norm{f_1}_\infty\operatorname{Lip}(f_2)\big)\delta_{J,R}.
\end{aligned}
\end{equation}
The response $\mathfrak R_\ell$ is bilinear in $(F,G)$ and in $(f_1,f_2)$, unchanged
under replication, and bounded by $\gamma_\star\norm F\norm G\norm{f_1}_\infty\norm{f_2}_\infty$.
The lag kernels and the filtered lag coefficients are
\begin{equation}\label{eqn:app-vol-lag-kernel}
\mathfrak k_\ell[F,G](s,u)\defeq\mathfrak R_\ell[F,G](\iota_s,\iota_u),\qquad
\overline C_\ell[F,G](\ridge,\ridge')\defeq\mathfrak R_\ell[F,G](\omega_\ridge,\omega_{\ridge'}),
\end{equation}
and $\mathfrak k_\ell\defeq\mathfrak k_\ell[\Sigmaout,\Sigmain]$,
$\overline C_\ell\defeq\overline C_\ell[\Sigmaout,\Sigmain]$. Along every sequence of
dimensions satisfying the size conditions, for every compact
$\mathcal J\subset(0,\infty)$,
\begin{equation}\label{eqn:app-vol-lag-closure}
\begin{gathered}
\sup_{s,u\in\mathcal J}\sup_{F,G}\abs{\EE\,\mathcal K^{F,G}_{s,u}(M^{\mathrm g}_t,M^{\mathrm g}_{t+\ell})-\mathfrak k_\ell[F,G](s,u)}\to0,\\
\sup_{\ridge,\ridge'\in I}\sup_{F,G}\abs{C^{\mathrm g}_\ell[F,G](\ridge,\ridge')-\overline C_\ell[F,G](\ridge,\ridge')}\to0,
\end{gathered}
\end{equation}
the suprema over diagonal $F,G$ of norm at most one. Under
\cref{assum:app-setup-regime} the same holds for the actual model, with
$\EE\,\mathcal K^{F,G}_{s,u}(\Mt,M_{t+\ell})$ and $C_\ell[F,G]$ in place of the
independent quantities.
\end{theorem}
```
-/
theorem thm_app_vol_lag_kernel_closure_actual (cert : Muon.External.GaussianOpNorm)
    (R : SetupRegime) (Ω : ℕ → Type) [∀ k, MeasurableSpace (Ω k)]
    (P : ∀ k, Measure (Ω k)) [∀ k, IsProbabilityMeasure (P k)]
    (S : ∀ k, FrozenSamples (P k) (R.m k) (R.n k) (R.B k))
    (Sp : ∀ k : ℕ, SpectralData (R.F k).C) (ℓ : ℕ) (J : Set ℝ) (hJ : IsCompact J)
    (hJpos : J ⊆ Set.Ioi 0) :
    -- (a) kernels of the actual model on J
    (∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, ∀ t : ℤ, ∀ s ∈ J, ∀ u ∈ J,
      ∀ (Fd : Fin (R.m k) → ℝ) (Gd : Fin (R.n k) → ℝ)
      (Fm : Mat (R.m k) (R.m k)) (Gm : Mat (R.n k) (R.n k)),
      Fm = (Sp k).uOut * Matrix.diagonal Fd * (Sp k).uOutᵀ →
      Gm = (Sp k).vIn * Matrix.diagonal Gd * (Sp k).vInᵀ →
      opNorm Fm ≤ 1 → opNorm Gm ≤ 1 →
      |(∫ ω, contractionRes (R.B k) Fm Gm s u (frozenBuf (R.F k) (S k) t ω)
            (frozenBuf (R.F k) (S k) (t + (ℓ : ℤ)) ω) ∂(P k)) -
        lagResp cert R.γstar R.CSig (R.F k).β ℓ (R.B k) (Sp k).μ (Sp k).lam Fd Gd
          (iotaF s) (iotaF u)| ≤ ε) ∧
    -- (b) tested lag covariances of the actual model on I
    (∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, ∀ t : ℤ, ∀ ϱ ∈ Set.Icc R.ϱlo R.ϱhi,
      ∀ ϱ' ∈ Set.Icc R.ϱlo R.ϱhi,
      ∀ (Fd : Fin (R.m k) → ℝ) (Gd : Fin (R.n k) → ℝ)
      (Fm : Mat (R.m k) (R.m k)) (Gm : Mat (R.n k) (R.n k)),
      Fm = (Sp k).uOut * Matrix.diagonal Fd * (Sp k).uOutᵀ →
      Gm = (Sp k).vIn * Matrix.diagonal Gd * (Sp k).vInᵀ →
      opNorm Fm ≤ 1 → opNorm Gm ≤ 1 →
      |def_app_vol_lag (R.F k) (S k) ℓ t Fm Gm ϱ ϱ' -
        lagResp cert R.γstar R.CSig (R.F k).β ℓ (R.B k) (Sp k).μ (Sp k).lam Fd Gd
          (omegaF ϱ) (omegaF ϱ')| ≤ ε) := by
  have hSize : SizeSeq (B := R.B) (fun k => (R.F k).C) R.γstar R.CSig
      R.prop.γout R.prop.γin :=
    ⟨fun k => ⟨R.dims k, R.normOut k, R.normIn k⟩, R.prop.B_top,
      R.prop.ratio_in, R.prop.ratio_out⟩
  have hind := thm_app_vol_lag_kernel_closure_indep cert R.γstar R.CSig
    R.prop.γout R.prop.γin R.hC R.ϱlo R.ϱhi R.hϱ R.m R.n R.B R.F Sp hSize
    R.β (by rw [← R.hβ 0]; exact (R.F 0).hβ.2) (fun k => (R.hβ k).le) ℓ J hJ hJpos
  obtain ⟨δ, hδ, hrep⟩ := lem_app_vol_replacement_regime R P S J hJ hJpos
  let εB : ℕ → ℝ := fun k => Muon.Drift.epsB (emaW R.β) (R.F k) (S k) 0
    (Muon.Drift.specOutFM (R.F k)) (Muon.Drift.specInFM (R.F k)) R.ϱlo R.ϱhi
  have hm := Muon.Drift.thm_app_drift_mean R P S 0
  have hεB : Tendsto εB atTop (𝓝 0) := hm.2.2.1
  have hmean : ∀ k, ∀ s : ℤ, ∀ ϱ ∈ Set.Icc R.ϱlo R.ϱhi,
      fro (Muon.mean (P k) (frozenUpd (R.F k) (S k) ϱ s)) ≤
        R.CSig / Real.sqrt R.ϱlo + εB k := by
    intro k s ϱ hϱ
    have he : fro (Muon.Drift.EQ (emaW R.β) (R.F k) (S k) 0 ϱ -
        Muon.Drift.Gbar (emaW R.β) (R.F k) (Muon.Drift.specOutFM (R.F k))
          (Muon.Drift.specInFM (R.F k)) ϱ) ≤ εB k := p4_le_biSup (hm.2.1 k) hϱ
    have hg := (hm.1 k ϱ hϱ).2
    have hsqrt : R.CSig / Real.sqrt ϱ ≤ R.CSig / Real.sqrt R.ϱlo :=
      div_le_div_of_nonneg_left (by linarith [R.hC]) (Real.sqrt_pos.mpr R.hϱ.1)
        (Real.sqrt_le_sqrt hϱ.1)
    have hadd := p4_fro_add
      (Muon.Drift.EQ (emaW R.β) (R.F k) (S k) 0 ϱ -
        Muon.Drift.Gbar (emaW R.β) (R.F k) (Muon.Drift.specOutFM (R.F k))
          (Muon.Drift.specInFM (R.F k)) ϱ)
      (Muon.Drift.Gbar (emaW R.β) (R.F k) (Muon.Drift.specOutFM (R.F k))
          (Muon.Drift.specInFM (R.F k)) ϱ)
    rw [sub_add_cancel] at hadd
    have heq : Muon.Drift.EQ (emaW R.β) (R.F k) (S k) 0 ϱ =
        Muon.mean (P k) (frozenUpd (R.F k) (S k) ϱ 0) := by
      unfold Muon.Drift.EQ
      congr 1
      funext ω
      unfold frozenUpd WeightedBuf frozenBuf
      rw [R.hβ k]
    rw [heq] at hadd he
    have hzero : fro (Muon.mean (P k) (frozenUpd (R.F k) (S k) ϱ 0)) ≤
        R.CSig / Real.sqrt R.ϱlo + εB k := by
      linarith
    have hshift := p4_mean_shift (R.F k) (S k) (R.hϱ.1.le.trans hϱ.1) 0 s
    rw [zero_add] at hshift
    rw [hshift]
    exact hzero
  obtain ⟨η, hη, hcovrep⟩ := cor_app_vol_filtered_replacement_ii R P S εB hmean
  have hBreal : Tendsto (fun k => (R.B k : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp R.prop.B_top
  have hmeanTerm : Tendsto (fun k =>
      (R.CSig / Real.sqrt R.ϱlo + εB k) ^ 2 / (R.B k : ℝ)) atTop (𝓝 0) :=
    ((tendsto_const_nhds.add hεB).pow 2).div_atTop hBreal
  have hcovErr : Tendsto (fun k => η k +
      (R.CSig / Real.sqrt R.ϱlo + εB k) ^ 2 / (R.B k : ℝ)) atTop (𝓝 0) := by
    simpa using hη.add hmeanTerm
  constructor
  · intro ε hε
    have hi := hind.1 (ε / 2) (by positivity)
    have hδ2 : Tendsto (fun k => 2 * δ k) atTop (𝓝 0) := by
      simpa using hδ.const_mul 2
    have hr : ∀ᶠ k in atTop, 2 * δ k < ε / 2 :=
      (tendsto_order.1 hδ2).2 (ε / 2) (by positivity)
    filter_upwards [hi, hr] with k hik hrk
    intro t s hs u hu Fd Gd Fm Gm hFm hGm hF hG
    have hri := hrep t ℓ k s u hs hu Fm hF Gm hG
    have hii := hik t s hs u hu Fd Gd Fm Gm hFm hGm hF hG
    have htri := abs_sub_le
      (∫ ω, contractionRes (R.B k) Fm Gm s u (frozenBuf (R.F k) (S k) t ω)
        (frozenBuf (R.F k) (S k) (t + (ℓ : ℤ)) ω) ∂(P k))
      (∫ ω, contractionRes (R.B k) Fm Gm s u (def_app_vol_product (R.F k) ω t)
        (def_app_vol_product (R.F k) ω (t + (ℓ : ℤ)))
          ∂(indepSpaceLaw (R.m k) (R.n k) (R.B k)))
      (lagResp cert R.γstar R.CSig (R.F k).β ℓ (R.B k) (Sp k).μ (Sp k).lam
        Fd Gd (iotaF s) (iotaF u))
    linarith
  · intro ε hε
    have hi := hind.2 (ε / 2) (by positivity)
    have hr : ∀ᶠ k in atTop, η k +
        (R.CSig / Real.sqrt R.ϱlo + εB k) ^ 2 / (R.B k : ℝ) < ε / 2 :=
      (tendsto_order.1 hcovErr).2 (ε / 2) (by positivity)
    filter_upwards [hi, hr] with k hik hrk
    intro t ϱ hϱ ϱ' hϱ' Fd Gd Fm Gm hFm hGm hF hG
    have hFs : Fmᵀ = Fm := by rw [hFm]; exact p4_diag_symm _ _
    have hGs : Gmᵀ = Gm := by rw [hGm]; exact p4_diag_symm _ _
    have hri := hcovrep t ℓ k Fm Gm hFs hF hGs hG ϱ ϱ' hϱ hϱ'
    have hii := hik t ϱ hϱ ϱ' hϱ' Fd Gd Fm Gm hFm hGm hF hG
    have htri := abs_sub_le
      (def_app_vol_lag (R.F k) (S k) ℓ t Fm Gm ϱ ϱ')
      ((R.B k : ℝ)⁻¹ * (∫ ω, Matrix.trace (Fm * indepUpd (R.F k) ϱ ω t * Gm *
        (indepUpd (R.F k) ϱ' ω (t + (ℓ : ℤ)))ᵀ)
          ∂(indepSpaceLaw (R.m k) (R.n k) (R.B k))))
      (lagResp cert R.γstar R.CSig (R.F k).β ℓ (R.B k) (Sp k).μ (Sp k).lam
        Fd Gd (omegaF ϱ) (omegaF ϱ'))
    linarith

/-! ## Integrated identification (`thm:app-vol-integrated`) -/

-- P5-HELPERS-BEGIN
section P5Helpers

private lemma p5_repl_setup {m n B : ℕ} (Fp : FrozenParams m n B) (S : SpectralData Fp.C)
    (N : ℕ) (hN : 0 < N) (γstar CSig : ℝ) (hS : SizeFin Fp.C B γstar CSig) :
    ∃ (Fp' : FrozenParams (N * m) (N * n) (N * B)) (S' : SpectralData Fp'.C),
      Fp'.β = Fp.β ∧ S'.μ = replVec N S.μ ∧ S'.lam = replVec N S.lam ∧
      S'.uOut = replMat S.uOut N ∧ S'.vIn = replMat S.vIn N ∧
      SizeFin Fp'.C (N * B) γstar CSig := by
  obtain ⟨hm, hn⟩ := tx_pos_of_fro Fp.A Fp.hA
  obtain ⟨S', h1, h2, h3, h4⟩ := tx_exists_replSpec Fp.C S N
  exact ⟨def_app_vol_replication Fp S N hN (def_app_vol_replication_vi Fp.C S N hm hn hN),
    S', rfl, h3, h4, h1, h2, def_app_vol_replication_iv Fp.C γstar CSig hS N hN⟩

private lemma p5_repl_seq {m n B : ℕ} (Fp : FrozenParams m n B) (S : SpectralData Fp.C)
    (γstar CSig : ℝ) (hS : SizeFin Fp.C B γstar CSig) :
    ∃ (rF : ∀ k : ℕ, FrozenParams ((k + 1) * m) ((k + 1) * n) ((k + 1) * B))
      (Sp : ∀ k : ℕ, SpectralData (rF k).C),
      SizeSeq (B := fun k => (k + 1) * B) (fun k => (rF k).C) γstar CSig
        ((m : ℝ) / B) ((n : ℝ) / B) ∧
      (∀ k, (rF k).β = Fp.β) ∧ (∀ k, (Sp k).μ = replVec (k + 1) S.μ) ∧
      (∀ k, (Sp k).lam = replVec (k + 1) S.lam) ∧
      (∀ k (Fd : Fin m → ℝ), (Sp k).uOut * Matrix.diagonal (replVec (k + 1) Fd) * (Sp k).uOutᵀ =
        replMat (S.uOut * Matrix.diagonal Fd * S.uOutᵀ) (k + 1)) ∧
      (∀ k (Gd : Fin n → ℝ), (Sp k).vIn * Matrix.diagonal (replVec (k + 1) Gd) * (Sp k).vInᵀ =
        replMat (S.vIn * Matrix.diagonal Gd * S.vInᵀ) (k + 1)) := by
  have h := fun k : ℕ => p5_repl_setup Fp S (k + 1) (Nat.succ_pos k) γstar CSig hS
  choose rF Sp hβ hμ hl hU hV hsz using h
  have hBpos : 0 < B := Fp.hB
  have hBr : (0 : ℝ) < (B : ℝ) := by exact_mod_cast hBpos
  have hv : ∀ k : ℕ,
      ((((k + 1) * m : ℕ)) : ℝ) / ((((k + 1) * B : ℕ)) : ℝ) = (m : ℝ) / (B : ℝ) ∧
      ((((k + 1) * n : ℕ)) : ℝ) / ((((k + 1) * B : ℕ)) : ℝ) = (n : ℝ) / (B : ℝ) :=
    fun k => def_app_vol_replication_v (k + 1) (Nat.succ_pos k) hBpos
  refine ⟨rF, Sp, ⟨hsz, ?_, ?_, ?_⟩, hβ, hμ, hl, ?_, ?_⟩
  · exact tendsto_atTop_mono (fun k : ℕ => le_trans (Nat.le_succ k)
      (Nat.le_mul_of_pos_right (k + 1) hBpos)) tendsto_id
  · exact Tendsto.congr (fun k => ((hv k).2).symm) tendsto_const_nhds
  · exact Tendsto.congr (fun k => ((hv k).1).symm) tendsto_const_nhds
  · intro k Fd
    rw [hU k, ← tx_repl_test]
  · intro k Gd
    rw [hV k, ← tx_repl_test]

private lemma p5_indep_bound {m n B : ℕ} (F : FrozenParams m n B) (γstar CSig ϱlo ϱhi : ℝ)
    (hS : SizeFin F.C B γstar CSig) (hCSig : 1 ≤ CSig) (hϱ : 0 < ϱlo ∧ ϱlo ≤ ϱhi)
    (Fo : Mat m m) (Gi : Mat n n) (hFs : Fo.transpose = Fo) (hGs : Gi.transpose = Gi)
    (hF : opNorm Fo ≤ 1) (hG : opNorm Gi ≤ 1)
    (ϱ ϱ' : ℝ) (hϱI : ϱ ∈ Set.Icc ϱlo ϱhi) (hϱ'I : ϱ' ∈ Set.Icc ϱlo ϱhi) (t : ℤ) (ℓ : ℕ)
    (hℓ : 1 ≤ ℓ) :
    |(B : ℝ)⁻¹ * ∫ ω, Matrix.trace (Fo * indepUpd F ϱ ω t * Gi *
            (indepUpd F ϱ' ω (t + (ℓ : ℤ)))ᵀ) ∂(indepSpaceLaw m n B)| ≤
          Muon.Dynamics.kStar CSig γstar ϱlo * F.β ^ ℓ := by
  haveI : IsProbabilityMeasure (Measure.infinitePi fun _ : ℤ × Fin B =>
      (Muon.Foundations.stdGaussianPi m).prod (Muon.Foundations.stdGaussianPi n)) := inferInstance
  exact (thm_app_vol_lag_reduction_ii_indep F (frozenSamples_nonempty m n B).some γstar CSig
    ϱlo ϱhi hS hCSig hϱ Fo Gi hFs hGs hF hG ϱ ϱ' hϱI hϱ'I t).2 ℓ hℓ

private lemma p5_unit_lag_bound (cert : Muon.External.GaussianOpNorm) (γstar CSig : ℝ)
    {m n B : ℕ} (Fp : FrozenParams m n B) (S : SpectralData Fp.C)
    (hS : SizeFin Fp.C B γstar CSig) (hCSig : 1 ≤ CSig) (ϱlo ϱhi : ℝ)
    (hϱ : 0 < ϱlo ∧ ϱlo ≤ ϱhi) (ℓ : ℕ) (hℓ : 1 ≤ ℓ)
    (e1 : Fin m → ℝ) (e2 : Fin n → ℝ)
    (h1 : opNorm (S.uOut * Matrix.diagonal e1 * S.uOutᵀ) ≤ 1)
    (h2 : opNorm (S.vIn * Matrix.diagonal e2 * S.vInᵀ) ≤ 1)
    (ϱ ϱ' : ℝ) (hϱI : ϱ ∈ Set.Icc ϱlo ϱhi) (hϱ'I : ϱ' ∈ Set.Icc ϱlo ϱhi) :
    |lagResp cert γstar CSig Fp.β ℓ B S.μ S.lam e1 e2 (omegaF ϱ) (omegaF ϱ')| ≤
      Muon.Dynamics.kStar CSig γstar ϱlo * Fp.β ^ ℓ := by
  obtain ⟨rF, Sp, hSz, hβ, hμ, hl, hUF, hVG⟩ := p5_repl_seq Fp S γstar CSig hS
  have hclo := (thm_app_vol_lag_kernel_closure_indep cert γstar CSig ((m : ℝ) / B) ((n : ℝ) / B)
    hCSig ϱlo ϱhi hϱ (fun k => (k + 1) * m) (fun k => (k + 1) * n) (fun k => (k + 1) * B) rF Sp
    hSz Fp.β Fp.hβ.2 (fun k => (hβ k).le) ℓ {1} isCompact_singleton
    (by intro x hx; rcases hx with rfl; norm_num)).2
  have hϱ1 : 0 < ϱ := lt_of_lt_of_le hϱ.1 hϱI.1
  have hϱ2 : 0 < ϱ' := lt_of_lt_of_le hϱ.1 hϱ'I.1
  refine le_of_forall_pos_le_add fun ε hε => ?_
  obtain ⟨k, hk⟩ := (hclo ε hε).exists
  have hF1 : opNorm ((Sp k).uOut * Matrix.diagonal (replVec (k + 1) e1) * (Sp k).uOutᵀ) ≤ 1 := by
    rw [hUF k]; exact (tx_replMat_opNorm_le _).trans h1
  have hG1 : opNorm ((Sp k).vIn * Matrix.diagonal (replVec (k + 1) e2) * (Sp k).vInᵀ) ≤ 1 := by
    rw [hVG k]; exact (tx_replMat_opNorm_le _).trans h2
  have key := hk 0 ϱ hϱI ϱ' hϱ'I (replVec (k + 1) e1) (replVec (k + 1) e2) _ _ rfl rfl hF1 hG1
  have hw : lagResp cert γstar CSig (rF k).β ℓ ((k + 1) * B) (Sp k).μ (Sp k).lam
      (replVec (k + 1) e1) (replVec (k + 1) e2) (omegaF ϱ) (omegaF ϱ') =
      lagResp cert γstar CSig Fp.β ℓ B S.μ S.lam e1 e2 (omegaF ϱ) (omegaF ϱ') := by
    rw [hβ k, hμ k, hl k]
    exact (thm_app_vol_lag_kernel_bilinear_bound_replication cert γstar CSig Fp S hS hCSig ℓ
      (omegaF ϱ) (omegaF ϱ') (lem_app_vol_sharp_ii hϱ1 hϱ1).2.1
      (lem_app_vol_sharp_ii hϱ2 hϱ2).2.1).2.2.2.2.2 (k + 1) (Nat.succ_pos k) e1 e2
  rw [hw] at key
  have hb := p5_indep_bound (rF k) γstar CSig ϱlo ϱhi (hSz.1 k) hCSig hϱ _ _
    (p4_diag_symm _ _) (p4_diag_symm _ _) hF1 hG1 ϱ ϱ' hϱI hϱ'I 0 ℓ hℓ
  rw [hβ k] at hb
  have := abs_sub_abs_le_abs_sub
    (lagResp cert γstar CSig Fp.β ℓ B S.μ S.lam e1 e2 (omegaF ϱ) (omegaF ϱ'))
    (((((k + 1) * B : ℕ) : ℝ))⁻¹ * ∫ ω, Matrix.trace ((Sp k).uOut *
      Matrix.diagonal (replVec (k + 1) e1) * (Sp k).uOutᵀ * indepUpd (rF k) ϱ ω 0 *
      ((Sp k).vIn * Matrix.diagonal (replVec (k + 1) e2) * (Sp k).vInᵀ) *
      (indepUpd (rF k) ϱ' ω (0 + (ℓ : ℤ)))ᵀ)
        ∂(indepSpaceLaw ((k + 1) * m) ((k + 1) * n) ((k + 1) * B)))
  rw [abs_sub_comm] at this
  linarith

private lemma p5_tr_mul_nonneg {m : ℕ} (F Y : Matrix (Fin m) (Fin m) ℝ) (hF : F.PosSemidef)
    (hY : Y.PosSemidef) : 0 ≤ Matrix.trace (F * Y) := by
  have hF0 : 0 ≤ F := Matrix.nonneg_iff_posSemidef.mpr hF
  have hs : (CFC.sqrt F) * (CFC.sqrt F) = F := CFC.sqrt_mul_sqrt_self F hF0
  have hsa : (CFC.sqrt F)ᴴ = CFC.sqrt F := (CFC.sqrt_nonneg F).isSelfAdjoint.star_eq
  have h2 : (CFC.sqrt F * Y * (CFC.sqrt F)ᴴ).PosSemidef := hY.mul_mul_conjTranspose_same _
  rw [hsa] at h2
  have : Matrix.trace (F * Y) = Matrix.trace (CFC.sqrt F * Y * CFC.sqrt F) := by
    conv_lhs => rw [← hs]
    rw [Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc]
  rw [this]; exact h2.trace_nonneg

private lemma p5_tr_nonneg {m n : ℕ} (Fo : Mat m m) (Gi : Mat n n) (hF : Fo.PosSemidef)
    (hG : Gi.PosSemidef) (X : Mat m n) : 0 ≤ Matrix.trace (Fo * X * Gi * Xᵀ) := by
  have h2 : (X * Gi * Xᴴ).PosSemidef := hG.mul_mul_conjTranspose_same X
  rw [Matrix.conjTranspose_eq_transpose_of_trivial] at h2
  have := p5_tr_mul_nonneg Fo _ hF h2
  rwa [← Matrix.mul_assoc, ← Matrix.mul_assoc] at this

private lemma p5_err_tendsto (K β : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β < 1) :
    Tendsto (fun T : ℕ => 2 * K * (β ^ T / (1 - β) + β / ((T : ℝ) * (1 - β) ^ 2))) atTop (𝓝 0) := by
  have h1 : Tendsto (fun T : ℕ => β ^ T / (1 - β)) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hβ0 hβ1).div_const (1 - β)
  have h2 : Tendsto (fun T : ℕ => β / ((T : ℝ) * (1 - β) ^ 2)) atTop (𝓝 0) := by
    have := (tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop).const_mul (β / (1 - β) ^ 2)
    simp only [mul_zero] at this
    refine this.congr fun T => ?_
    simp only [Function.comp]
    field_simp
  simpa using (h1.add h2).const_mul (2 * K)

private lemma p5_actual_nonneg {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {m n B : ℕ}
    (F : FrozenParams m n B) (S : FrozenSamples P m n B)
    (γstar CSig ϱlo ϱhi : ℝ) (hS : SizeFin F.C B γstar CSig) (hCSig : 1 ≤ CSig)
    (hϱ : 0 < ϱlo ∧ ϱlo ≤ ϱhi)
    (Fo : Mat m m) (Gi : Mat n n) (hFs : Fo.transpose = Fo) (hGs : Gi.transpose = Gi)
    (hF : opNorm Fo ≤ 1) (hG : opNorm Gi ≤ 1) (hFp : Fo.PosSemidef) (hGp : Gi.PosSemidef)
    (ϱ : ℝ) (hϱI : ϱ ∈ Set.Icc ϱlo ϱhi) (t : ℤ) :
    0 ≤ integratedLag F S t Fo Gi ϱ ϱ := by
  have hfin : ∀ T : ℕ, 0 ≤ finiteTimeCov F S T ϱ ϱ Fo Gi := by
    intro T
    unfold finiteTimeCov
    refine mul_nonneg (inv_nonneg.mpr (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))) ?_
    exact integral_nonneg fun ω => p5_tr_nonneg Fo Gi hFp hGp _
  have hb := fun T (hT : 1 ≤ T) => thm_app_vol_lag_reduction_iii_bound F S γstar CSig ϱlo ϱhi hS
    hCSig hϱ Fo Gi hFs hGs hF hG ϱ ϱ hϱI hϱI T hT t
  have hlim := (p5_err_tendsto (Muon.Dynamics.kStar CSig γstar ϱlo) F.β F.hβ.1 F.hβ.2).const_add
    (integratedLag F S t Fo Gi ϱ ϱ)
  have := ge_of_tendsto (b := (0 : ℝ)) hlim (by
    filter_upwards [eventually_ge_atTop 1] with T hT
    have h1 := hb T hT
    have h2 := hfin T
    have := (abs_le.mp h1).2
    beta_reduce
    linarith)
  simpa using this

private lemma p5_psd_diag {k : ℕ} (U : Mat k k) (d : Fin k → ℝ) (hd : ∀ i, 0 ≤ d i) :
    (U * Matrix.diagonal d * Uᵀ).PosSemidef := by
  have h1 : (Matrix.diagonal d).PosSemidef := Matrix.posSemidef_diagonal_iff.mpr hd
  have h2 := h1.mul_mul_conjTranspose_same U
  rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at h2

private lemma p5_summable_shift (c β : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β < 1) (f : ℕ → ℝ)
    (hf : ∀ ℓ : ℕ, |f ℓ| ≤ c * β ^ (ℓ + 1)) : Summable f := by
  have hgeo : Summable (fun n : ℕ => β ^ n) := summable_geometric_of_lt_one hβ0 hβ1
  have hgeo1 : Summable (fun n : ℕ => β ^ (n + 1)) := (summable_nat_add_iff 1).mpr hgeo
  exact summable_abs_iff.mp (Summable.of_nonneg_of_le (fun _ => abs_nonneg _) hf
    (hgeo1.mul_left c))

private lemma p5_gamma_nonneg_unit (cert : Muon.External.GaussianOpNorm) (γstar CSig : ℝ)
    {m n B : ℕ} (Fp : FrozenParams m n B) (S : SpectralData Fp.C)
    (hS : SizeFin Fp.C B γstar CSig) (hCSig : 1 ≤ CSig) (ϱlo ϱhi : ℝ)
    (hϱ : 0 < ϱlo ∧ ϱlo ≤ ϱhi) (e1 : Fin m → ℝ) (e2 : Fin n → ℝ)
    (he1 : ∀ i, 0 ≤ e1 i) (he2 : ∀ j, 0 ≤ e2 j)
    (h1 : opNorm (S.uOut * Matrix.diagonal e1 * S.uOutᵀ) ≤ 1)
    (h2 : opNorm (S.vIn * Matrix.diagonal e2 * S.vInᵀ) ≤ 1)
    (ϱ : ℝ) (hϱI : ϱ ∈ Set.Icc ϱlo ϱhi) :
    0 ≤ lagGammaBar cert γstar CSig Fp.β B S.μ S.lam e1 e2 ϱ ϱ := by
  obtain ⟨hm, hn⟩ := tx_pos_of_fro Fp.A Fp.hA
  obtain ⟨R, hmR, hnR, hBR, hγR, hCR, hβR, hloR, hhiR, hR⟩ :=
    def_app_vol_replication_regime Fp S γstar CSig ϱlo ϱhi hCSig hS hm hn hϱ
  rcases R with ⟨rm, rn, rB, rF, rprop, rγ, rC, rhC, rdims, rnormO, rnormI,
    rβ, rhβ, rlo, rhi, rhϱ, rdiff⟩
  dsimp only at hmR hnR hBR hγR hCR hβR hloR hhiR hR
  subst rm rn rB rγ rC rβ rlo rhi
  let R : SetupRegime := ⟨_, _, _, rF, rprop, γstar, CSig, rhC, rdims, rnormO, rnormI,
    Fp.β, rhβ, ϱlo, ϱhi, rhϱ, rdiff⟩
  have hCov : ∀ k, (rF k).C = replCov Fp.C (k + 1) := fun k => eq_of_heq (hR k).1
  have hspec : ∀ k, ∃ Sp : SpectralData (rF k).C,
      Sp.μ = replVec (k + 1) S.μ ∧ Sp.lam = replVec (k + 1) S.lam ∧
      Sp.uOut = replMat S.uOut (k + 1) ∧ Sp.vIn = replMat S.vIn (k + 1) := by
    intro k
    rw [hCov k]
    obtain ⟨Sp, h1, h2, h3, h4⟩ := tx_exists_replSpec Fp.C S (k + 1)
    exact ⟨Sp, h3, h4, h1, h2⟩
  choose Sp hμ hl hU hV using hspec
  let Ω : ℕ → Type := fun k => (ℤ × Fin (R.B k)) → Vec (R.m k) × Vec (R.n k)
  let P : ∀ k, Measure (Ω k) := fun k => Measure.infinitePi fun _ : ℤ × Fin (R.B k) =>
    (Muon.Foundations.stdGaussianPi (R.m k)).prod (Muon.Foundations.stdGaussianPi (R.n k))
  let samples : ∀ k, FrozenSamples (P k) (R.m k) (R.n k) (R.B k) := fun k =>
    (frozenSamples_nonempty (R.m k) (R.n k) (R.B k)).some
  have hact := fun ℓ : ℕ => (thm_app_vol_lag_kernel_closure_actual cert R Ω P samples Sp ℓ {1}
    isCompact_singleton (by intro x hx; rcases hx with rfl; norm_num)).2
  have hϱ1 : 0 < ϱ := lt_of_lt_of_le hϱ.1 hϱI.1
  have hω := (lem_app_vol_sharp_ii hϱ1 hϱ1).2.1
  have hSz : ∀ k, SizeFin (rF k).C ((k + 1) * B) γstar CSig :=
    fun k => ⟨rdims k, rnormO k, rnormI k⟩
  have hrepl := fun ℓ : ℕ => (thm_app_vol_lag_kernel_bilinear_bound_replication cert γstar CSig
    Fp S hS hCSig ℓ (omegaF ϱ) (omegaF ϱ) hω hω).2.2.2.2.2
  have hFeq : ∀ k, (Sp k).uOut * Matrix.diagonal (replVec (k + 1) e1) * (Sp k).uOutᵀ =
      replMat (S.uOut * Matrix.diagonal e1 * S.uOutᵀ) (k + 1) := by
    intro k; rw [hU k, tx_repl_test]
  have hGeq : ∀ k, (Sp k).vIn * Matrix.diagonal (replVec (k + 1) e2) * (Sp k).vInᵀ =
      replMat (S.vIn * Matrix.diagonal e2 * S.vInᵀ) (k + 1) := by
    intro k; rw [hV k, tx_repl_test]
  have hF1 : ∀ k, opNorm ((Sp k).uOut * Matrix.diagonal (replVec (k + 1) e1) * (Sp k).uOutᵀ) ≤ 1 :=
    fun k => by rw [hFeq k]; exact (tx_replMat_opNorm_le _).trans h1
  have hG1 : ∀ k, opNorm ((Sp k).vIn * Matrix.diagonal (replVec (k + 1) e2) * (Sp k).vInᵀ) ≤ 1 :=
    fun k => by rw [hGeq k]; exact (tx_replMat_opNorm_le _).trans h2
  obtain ⟨Fm, hFm⟩ : ∃ Fm : ∀ k : ℕ, Mat ((k + 1) * m) ((k + 1) * m), ∀ k, Fm k =
      (Sp k).uOut * Matrix.diagonal (replVec (k + 1) e1) * (Sp k).uOutᵀ := ⟨_, fun _ => rfl⟩
  obtain ⟨Gm, hGm⟩ : ∃ Gm : ∀ k : ℕ, Mat ((k + 1) * n) ((k + 1) * n), ∀ k, Gm k =
      (Sp k).vIn * Matrix.diagonal (replVec (k + 1) e2) * (Sp k).vInᵀ := ⟨_, fun _ => rfl⟩
  obtain ⟨Cf, hCf⟩ : ∃ Cf : ℕ → ℕ → ℝ, ∀ k ℓ,
      Cf k ℓ = def_app_vol_lag (rF k) (samples k) ℓ 0 (Fm k) (Gm k) ϱ ϱ := ⟨_, fun _ _ => rfl⟩
  obtain ⟨Lf, hLf⟩ : ∃ Lf : ℕ → ℝ, ∀ ℓ,
      Lf ℓ = lagResp cert γstar CSig Fp.β ℓ B S.μ S.lam e1 e2 (omegaF ϱ) (omegaF ϱ) :=
    ⟨_, fun _ => rfl⟩
  have hnn : ∀ k, 0 ≤ Cf k 0 + ∑' ℓ : ℕ, (Cf k (ℓ + 1) + Cf k (ℓ + 1)) := by
    intro k
    have := p5_actual_nonneg (rF k) (samples k) γstar CSig ϱlo ϱhi (hSz k) hCSig hϱ (Fm k) (Gm k)
      (by rw [hFm k]; exact p4_diag_symm _ _) (by rw [hGm k]; exact p4_diag_symm _ _)
      (by rw [hFm k]; exact hF1 k) (by rw [hGm k]; exact hG1 k)
      (by rw [hFm k]; exact p5_psd_diag _ _ (fun i => he1 _))
      (by rw [hGm k]; exact p5_psd_diag _ _ (fun i => he2 _)) ϱ hϱI 0
    simpa only [integratedLag, hCf] using this
  have hconv : ∀ ℓ : ℕ, ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, |Cf k ℓ - Lf ℓ| ≤ ε := by
    intro ℓ ε hε
    filter_upwards [hact ℓ ε hε] with k hk
    have key := hk 0 ϱ hϱI ϱ hϱI (replVec (k + 1) e1) (replVec (k + 1) e2) (Fm k) (Gm k)
      (hFm k) (hGm k) (by rw [hFm k]; exact hF1 k) (by rw [hGm k]; exact hG1 k)
    have e : lagResp cert R.γstar R.CSig (R.F k).β ℓ (R.B k) (Sp k).μ (Sp k).lam
        (replVec (k + 1) e1) (replVec (k + 1) e2) (omegaF ϱ) (omegaF ϱ) = Lf ℓ := by
      rw [hLf]
      show lagResp cert γstar CSig (rF k).β ℓ ((k + 1) * B) (Sp k).μ (Sp k).lam
        (replVec (k + 1) e1) (replVec (k + 1) e2) (omegaF ϱ) (omegaF ϱ) = _
      rw [rhβ k, hμ k, hl k]
      exact hrepl ℓ (k + 1) (Nat.succ_pos k) e1 e2
    rw [e] at key
    rw [hCf]
    exact key
  have hCs : 0 ≤ CSig := by linarith
  have hK : 0 ≤ Muon.Dynamics.kStar CSig γstar ϱlo := by
    unfold Muon.Dynamics.kStar
    exact mul_nonneg hCs (Real.sqrt_nonneg _)
  obtain ⟨hβ0, hβ1⟩ := Fp.hβ
  have hCenv : ∀ k ℓ, 1 ≤ ℓ → |Cf k ℓ| ≤ Muon.Dynamics.kStar CSig γstar ϱlo * Fp.β ^ ℓ := by
    intro k ℓ hℓ
    have := (thm_app_vol_lag_reduction_ii_actual (rF k) (samples k) γstar CSig ϱlo ϱhi (hSz k)
      hCSig hϱ (Fm k) (Gm k)
      (by rw [hFm k]; exact p4_diag_symm _ _) (by rw [hGm k]; exact p4_diag_symm _ _)
      (by rw [hFm k]; exact hF1 k) (by rw [hGm k]; exact hG1 k) ϱ ϱ hϱI hϱI 0).2 ℓ hℓ
    rw [rhβ k] at this
    rw [hCf]
    exact this
  have hLenv : ∀ ℓ, 1 ≤ ℓ → |Lf ℓ| ≤ Muon.Dynamics.kStar CSig γstar ϱlo * Fp.β ^ ℓ := by
    intro ℓ hℓ
    rw [hLf]
    exact p5_unit_lag_bound cert γstar CSig Fp S hS hCSig ϱlo ϱhi hϱ ℓ hℓ e1 e2 h1 h2 ϱ ϱ hϱI hϱI
  have hbd : ∀ k : ℕ, ∀ p ∈ (fun _ : ℕ => (Set.univ : Set Unit)) k, ∀ ℓ : ℕ, 1 ≤ ℓ →
      |(fun (k ℓ : ℕ) (_ : Unit) => 2 * Cf k (ℓ + 1)) k ℓ p| +
        |(fun (k ℓ : ℕ) (_ : Unit) => 2 * Lf (ℓ + 1)) k ℓ p| ≤
          4 * Muon.Dynamics.kStar CSig γstar ϱlo * Fp.β ^ ℓ := by
    intro k p _ ℓ hℓ
    have h1' := hCenv k (ℓ + 1) (by omega)
    have h2' := hLenv (ℓ + 1) (by omega)
    have hp : Fp.β ^ (ℓ + 1) ≤ Fp.β ^ ℓ := pow_le_pow_of_le_one hβ0 hβ1.le (Nat.le_succ ℓ)
    have hKp : Muon.Dynamics.kStar CSig γstar ϱlo * Fp.β ^ (ℓ + 1) ≤
        Muon.Dynamics.kStar CSig γstar ϱlo * Fp.β ^ ℓ := mul_le_mul_of_nonneg_left hp hK
    show |2 * Cf k (ℓ + 1)| + |2 * Lf (ℓ + 1)| ≤ _
    rw [abs_mul, abs_mul]
    norm_num
    nlinarith
  have hsum := lem_app_vol_lagsum (fun _ : ℕ => (Set.univ : Set Unit))
    (fun (k ℓ : ℕ) (_ : Unit) => 2 * Cf k (ℓ + 1)) (fun (k ℓ : ℕ) (_ : Unit) => 2 * Lf (ℓ + 1))
    (4 * Muon.Dynamics.kStar CSig γstar ϱlo) Fp.β ⟨hβ0, hβ1⟩ hbd (by
      intro ℓ ε hε
      filter_upwards [hconv (ℓ + 1) (ε / 2) (by positivity)] with k hk p _
      show |2 * Cf k (ℓ + 1) - 2 * Lf (ℓ + 1)| ≤ ε
      rw [← mul_sub, abs_mul]
      norm_num
      linarith)
  have hsC : ∀ k, Summable (fun ℓ : ℕ => 2 * Cf k (ℓ + 1)) := by
    intro k
    refine p5_summable_shift (2 * Muon.Dynamics.kStar CSig γstar ϱlo) Fp.β hβ0 hβ1 _ fun ℓ => ?_
    rw [abs_mul]
    have := hCenv k (ℓ + 1) (by omega)
    norm_num
    nlinarith
  have hsL : Summable (fun ℓ : ℕ => 2 * Lf (ℓ + 1)) := by
    refine p5_summable_shift (2 * Muon.Dynamics.kStar CSig γstar ϱlo) Fp.β hβ0 hβ1 _ fun ℓ => ?_
    rw [abs_mul]
    have := hLenv (ℓ + 1) (by omega)
    norm_num
    nlinarith
  have hΓ : lagGammaBar cert γstar CSig Fp.β B S.μ S.lam e1 e2 ϱ ϱ =
      Lf 0 + ∑' ℓ : ℕ, 2 * Lf (ℓ + 1) := by
    unfold lagGammaBar
    rw [hLf]
    congr 1
    refine tsum_congr fun ℓ => ?_
    rw [hLf]
    ring
  refine le_of_forall_pos_le_add fun ε hε => ?_
  obtain ⟨k, hk0, hks⟩ := ((hconv 0 (ε / 2) (by positivity)).and (hsum (ε / 2) (by positivity))).exists
  have hks' := hks () (Set.mem_univ _)
  have hI : Cf k 0 + ∑' ℓ : ℕ, (Cf k (ℓ + 1) + Cf k (ℓ + 1)) =
      Cf k 0 + ∑' ℓ : ℕ, 2 * Cf k (ℓ + 1) := by
    congr 1
    exact tsum_congr fun ℓ => by ring
  have hdiff : ∑' ℓ : ℕ, (2 * Cf k (ℓ + 1) - 2 * Lf (ℓ + 1)) =
      ∑' ℓ : ℕ, 2 * Cf k (ℓ + 1) - ∑' ℓ : ℕ, 2 * Lf (ℓ + 1) := (hsC k).tsum_sub hsL
  have hn := hnn k
  rw [hI] at hn
  rw [hΓ]
  have h3 := (abs_le.mp hk0).2
  have h4 := (abs_le.mp (show |∑' ℓ : ℕ, (2 * Cf k (ℓ + 1) - 2 * Lf (ℓ + 1))| ≤ ε / 2 from hks')).2
  rw [hdiff] at h4
  linarith

private lemma p5_gamma_scale (cert : Muon.External.GaussianOpNorm) (γstar CSig : ℝ)
    {m n B : ℕ} (Fp : FrozenParams m n B) (S : SpectralData Fp.C)
    (hS : SizeFin Fp.C B γstar CSig) (hCSig : 1 ≤ CSig) (c d : ℝ)
    (Fd : Fin m → ℝ) (Gd : Fin n → ℝ) (ϱ ϱ' : ℝ) (hϱ : 0 < ϱ) (hϱ' : 0 < ϱ') :
    lagGammaBar cert γstar CSig Fp.β B S.μ S.lam (c • Fd) (d • Gd) ϱ ϱ' =
      c * d * lagGammaBar cert γstar CSig Fp.β B S.μ S.lam Fd Gd ϱ ϱ' := by
  have hf := (lem_app_vol_sharp_ii hϱ hϱ).2.1
  have hg := (lem_app_vol_sharp_ii hϱ' hϱ').2.1
  have h1 : ∀ ℓ : ℕ, lagResp cert γstar CSig Fp.β ℓ B S.μ S.lam (c • Fd) (d • Gd)
      (omegaF ϱ) (omegaF ϱ') = c * d * lagResp cert γstar CSig Fp.β ℓ B S.μ S.lam Fd Gd
      (omegaF ϱ) (omegaF ϱ') := fun ℓ =>
    p3_lag_scale cert γstar CSig Fp S hS hCSig ℓ c d Fd Gd _ _ hf hg
  have h2 : ∀ ℓ : ℕ, lagResp cert γstar CSig Fp.β ℓ B S.μ S.lam (c • Fd) (d • Gd)
      (omegaF ϱ') (omegaF ϱ) = c * d * lagResp cert γstar CSig Fp.β ℓ B S.μ S.lam Fd Gd
      (omegaF ϱ') (omegaF ϱ) := fun ℓ =>
    p3_lag_scale cert γstar CSig Fp S hS hCSig ℓ c d Fd Gd _ _ hg hf
  unfold lagGammaBar
  simp only [h1, h2]
  rw [mul_add, ← tsum_mul_left]
  congr 1
  exact tsum_congr fun ℓ => by ring

private lemma p5_diag_nonneg {k : ℕ} (U : Mat k k) (hU : Uᵀ * U = 1) (d : Fin k → ℝ)
    (h : (U * Matrix.diagonal d * Uᵀ).PosSemidef) (i : Fin k) : 0 ≤ d i := by
  have h2 := h.conjTranspose_mul_mul_same U
  rw [Matrix.conjTranspose_eq_transpose_of_trivial] at h2
  have e : Uᵀ * (U * Matrix.diagonal d * Uᵀ) * U = Matrix.diagonal d := by
    calc Uᵀ * (U * Matrix.diagonal d * Uᵀ) * U
        = (Uᵀ * U) * Matrix.diagonal d * (Uᵀ * U) := by simp only [Matrix.mul_assoc]
      _ = Matrix.diagonal d := by rw [hU]; simp
  rw [e] at h2
  simpa using h2.diag_nonneg (i := i)

private lemma p5r_indep_prob (m n B : ℕ) : IsProbabilityMeasure (indepSpaceLaw m n B) := by
  unfold indepSpaceLaw indepSlotLaw
  infer_instance

private lemma p5r_fro_zero {m n : ℕ} : fro (0 : Mat m n) = 0 := by
  unfold fro
  simp

private lemma p5r_product_fro_sq_integrable {m n B : ℕ} (Fp : FrozenParams m n B) (t : ℤ) :
    Integrable (fun ω => fro (def_app_vol_product Fp ω t) ^ 2) (indepSpaceLaw m n B) := by
  letI := p5r_indep_prob m n B
  have hout0 : 0 ≤ Matrix.trace Fp.C.Sout := Fp.C.psdOut.trace_nonneg
  have hin0 : 0 ≤ Matrix.trace Fp.C.Sin := Fp.C.psdIn.trace_nonneg
  by_cases hz : Matrix.trace Fp.C.Sout * Matrix.trace Fp.C.Sin = 0
  · rcases mul_eq_zero.mp hz with hout | hin
    · have hS : Fp.C.Sout = 0 := (Matrix.PosSemidef.trace_eq_zero_iff Fp.C.psdOut).mp hout
      have hr : rOut Fp.C = 0 := by simp [rOut, hS]
      have hp : (fun ω => def_app_vol_product Fp ω t) = fun _ => 0 := by
        funext ω
        simp [def_app_vol_product, indepBatchG, hr]
      have hp' : ∀ ω, def_app_vol_product Fp ω t = 0 := congrFun hp
      simpa only [hp', p5r_fro_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
        using (integrable_const (0 : ℝ) : Integrable (fun _ : (ℤ × Fin B) → ℝ × (Vec m × Vec n) => (0 : ℝ))
          (indepSpaceLaw m n B))
    · have hS : Fp.C.Sin = 0 := (Matrix.PosSemidef.trace_eq_zero_iff Fp.C.psdIn).mp hin
      have hr : rIn Fp.C = 0 := by simp [rIn, hS]
      have hp : (fun ω => def_app_vol_product Fp ω t) = fun _ => 0 := by
        funext ω
        simp [def_app_vol_product, indepBatchG, hr]
      have hp' : ∀ ω, def_app_vol_product Fp ω t = 0 := congrFun hp
      simpa only [hp', p5r_fro_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
        using (integrable_const (0 : ℝ) : Integrable (fun _ : (ℤ × Fin B) → ℝ × (Vec m × Vec n) => (0 : ℝ))
          (indepSpaceLaw m n B))
  · have htr : 0 < Matrix.trace Fp.C.Sout * Matrix.trace Fp.C.Sin :=
      lt_of_le_of_ne (mul_nonneg hout0 hin0) (Ne.symm hz)
    have hs : 0 < sPow Fp.β 2 := by
      rw [sPow_two Fp.hβ.1 Fp.hβ.2]
      exact div_pos (by linarith [Fp.hβ.2]) (by linarith [Fp.hβ.1])
    have houtp : 0 < Matrix.trace Fp.C.Sout := by
      by_contra h
      have : Matrix.trace Fp.C.Sout = 0 := le_antisymm (le_of_not_gt h) hout0
      exact hz (by rw [this, zero_mul])
    have hinp : 0 < Matrix.trace Fp.C.Sin := by
      by_contra h
      have : Matrix.trace Fp.C.Sin = 0 := le_antisymm (le_of_not_gt h) hin0
      exact hz (by rw [this, mul_zero])
    have hm := def_app_vol_product_moment Fp t
    have hpos : 0 < ∫ ω, fro (def_app_vol_product Fp ω t) ^ 2 ∂(indepSpaceLaw m n B) := by
      have hB : (0 : ℝ) < B := by exact_mod_cast Fp.hB
      have : 0 < ((B : ℝ))⁻¹ * ∫ ω, fro (def_app_vol_product Fp ω t) ^ 2
          ∂(indepSpaceLaw m n B) := by
        rw [hm]
        exact mul_pos (mul_pos (div_pos hs (sq_pos_of_pos hB)) houtp) hinp
      nlinarith [inv_pos.mpr hB]
    by_contra hnot
    rw [integral_undef hnot] at hpos
    linarith

private lemma p5r_product_moment_lintegral {m n B : ℕ} (Fp : FrozenParams m n B)
    (γstar CSig : ℝ) (hS : SizeFin Fp.C B γstar CSig) (t : ℤ) :
    ENNReal.ofReal ((B : ℝ)⁻¹) *
        ∫⁻ ω, ENNReal.ofReal (fro (def_app_vol_product Fp ω t) ^ 2)
          ∂(indepSpaceLaw m n B) ≤ ENNReal.ofReal (CSig ^ 2 * γstar ^ 2) := by
  rw [← ofReal_integral_eq_lintegral_ofReal (p5r_product_fro_sq_integrable Fp t)
    (Filter.Eventually.of_forall fun ω => sq_nonneg _),
    ← ENNReal.ofReal_mul (inv_nonneg.2 (Nat.cast_nonneg B))]
  exact ENNReal.ofReal_le_ofReal (def_app_vol_product_moment_le Fp γstar CSig hS t)


private lemma p5_prod_meas {m n B : ℕ} (F : FrozenParams m n B) (s : ℤ) :
    Measurable (fun ω : (ℤ × Fin B) → ℝ × (Vec m × Vec n) => def_app_vol_product F ω s) := by
  haveI : BorelSpace (Mat m n) := inferInstanceAs (BorelSpace (Fin m → Fin n → ℝ))
  haveI : TopologicalSpace.IsCompletelyPseudoMetrizableSpace (Mat m n) :=
    inferInstanceAs (TopologicalSpace.IsCompletelyPseudoMetrizableSpace (Fin m → Fin n → ℝ))
  haveI : SecondCountableTopology (Mat m n) :=
    inferInstanceAs (SecondCountableTopology (Fin m → Fin n → ℝ))
  unfold def_app_vol_product
  refine Measurable.tsum fun j => ?_
  refine Measurable.const_smul ?_ (emaW F.β j)
  unfold indepBatchG
  refine Measurable.const_smul ?_ ((B : ℝ))⁻¹
  refine Finset.measurable_sum _ fun a _ => ?_
  have hc : Continuous (fun p : ℝ × (Vec m × Vec n) =>
      p.1 • (rOut F.C * outer p.2.1 p.2.2 * rIn F.C)) := by
    fun_prop
  exact hc.measurable.comp (measurable_pi_apply (s + 1 - (j : ℤ), a))

private lemma p5_contr_integrable {m n B : ℕ} (F : FrozenParams m n B) (γ : ℝ)
    (hdim : ((min m n : ℕ) : ℝ) ≤ γ * B)
    (Fm : Mat m m) (Gm : Mat n n) (hF : opNorm Fm ≤ 1) (hG : opNorm Gm ≤ 1)
    (f g : ℝ → ℝ) (hf : IsOddBddLip f) (hg : IsOddBddLip g) (s t : ℤ) :
    Integrable (fun ω : (ℤ × Fin B) → ℝ × (Vec m × Vec n) =>
      contraction B Fm Gm f g (def_app_vol_product F ω s) (def_app_vol_product F ω t))
      (indepSpaceLaw m n B) := by
  haveI : IsProbabilityMeasure (indepSpaceLaw m n B) := p5r_indep_prob m n B
  obtain ⟨M₁, hM₁⟩ := hf.2.1
  obtain ⟨M₂, hM₂⟩ := hg.2.1
  have hmeas := (tx_meas_contr F.hB Fm Gm hF hG f g (tx_cont_of_lip _ hf) (tx_cont_of_lip _ hg)
    hf.1 hg.1 M₁ M₂ hM₁ hM₂).comp ((p5_prod_meas F s).prodMk (p5_prod_meas F t))
  exact Integrable.of_bound hmeas.aestronglyMeasurable (γ * M₁ * M₂)
    (Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs]
      exact tx_contr_bdd F.hB γ hdim Fm Gm hF hG f g hf.1 hg.1 M₁ M₂ hM₁ hM₂ _ _)

private lemma p5_L_filter_lip (cert : Muon.External.GaussianOpNorm) (γstar CSig : ℝ)
    {m n B : ℕ} (Fp : FrozenParams m n B) (S : SpectralData Fp.C)
    (hS : SizeFin Fp.C B γstar CSig) (hCSig : 1 ≤ CSig) (ℓ : ℕ)
    (e1 : Fin m → ℝ) (e2 : Fin n → ℝ)
    (h1 : opNorm (S.uOut * Matrix.diagonal e1 * S.uOutᵀ) ≤ 1)
    (h2 : opNorm (S.vIn * Matrix.diagonal e2 * S.vInᵀ) ≤ 1)
    (f g f' g' : ℝ → ℝ) (hf : IsOddBddLip f) (hg : IsOddBddLip g) (hf' : IsOddBddLip f')
    (hg' : IsOddBddLip g') :
    |lagResp cert γstar CSig Fp.β ℓ B S.μ S.lam e1 e2 f g -
        lagResp cert γstar CSig Fp.β ℓ B S.μ S.lam e1 e2 f' g'| ≤
      γstar * (supNorm (fun x => f x - f' x) * supNorm g +
        supNorm f' * supNorm (fun x => g x - g' x)) := by
  have hd1 := p3_add_filter f f' hf hf' (-1)
  have hd2 := p3_add_filter g g' hg hg' (-1)
  have e1' : (fun x => f x + -1 * f' x) = fun x => f x - f' x := by funext x; ring
  have e2' : (fun x => g x + -1 * g' x) = fun x => g x - g' x := by funext x; ring
  have lin1 := (thm_app_vol_lag_kernel_bilinear_bound_replication cert γstar CSig Fp S hS hCSig ℓ
    f g hf hg).2.2.2.1 (-1) f' hf' e1 e2
  have lin2 := (thm_app_vol_lag_kernel_bilinear_bound_replication cert γstar CSig Fp S hS hCSig ℓ
    f' g hf' hg).2.2.2.2.1 (-1) g' hg' e1 e2
  have b1 := p3_unit_bound cert γstar CSig Fp S hS ℓ e1 e2 h1 h2 _ g hd1 hg
  have b2 := p3_unit_bound cert γstar CSig Fp S hS ℓ e1 e2 h1 h2 f' _ hf' hd2
  rw [e1'] at b1 lin1
  rw [e2'] at b2 lin2
  have key : lagResp cert γstar CSig Fp.β ℓ B S.μ S.lam e1 e2 f g -
        lagResp cert γstar CSig Fp.β ℓ B S.μ S.lam e1 e2 f' g' =
      lagResp cert γstar CSig Fp.β ℓ B S.μ S.lam e1 e2 (fun x => f x - f' x) g +
        lagResp cert γstar CSig Fp.β ℓ B S.μ S.lam e1 e2 f' (fun x => g x - g' x) := by
    rw [lin1, lin2]; ring
  rw [key]
  calc _ ≤ _ := abs_add_le _ _
    _ ≤ _ := add_le_add b1 b2
    _ = _ := by ring

private lemma p5_contr_filter_lip {m n B : ℕ} (F : FrozenParams m n B) (γ : ℝ)
    (hdim : ((min m n : ℕ) : ℝ) ≤ γ * B)
    (Fm : Mat m m) (Gm : Mat n n) (hF : opNorm Fm ≤ 1) (hG : opNorm Gm ≤ 1) (s t : ℤ)
    (f g f' g' : ℝ → ℝ) (hf : IsOddBddLip f) (hg : IsOddBddLip g) (hf' : IsOddBddLip f')
    (hg' : IsOddBddLip g') :
    |(∫ ω, contraction B Fm Gm f g (def_app_vol_product F ω s) (def_app_vol_product F ω t)
        ∂(indepSpaceLaw m n B)) -
      ∫ ω, contraction B Fm Gm f' g' (def_app_vol_product F ω s) (def_app_vol_product F ω t)
        ∂(indepSpaceLaw m n B)| ≤
      γ * (supNorm (fun x => f x - f' x) * supNorm g +
        supNorm f' * supNorm (fun x => g x - g' x)) := by
  haveI : IsProbabilityMeasure (indepSpaceLaw m n B) := p5r_indep_prob m n B
  rw [← integral_sub (p5_contr_integrable F γ hdim Fm Gm hF hG f g hf hg s t)
    (p5_contr_integrable F γ hdim Fm Gm hF hG f' g' hf' hg' s t)]
  have := norm_integral_le_of_norm_le_const (μ := indepSpaceLaw m n B)
    (C := γ * (supNorm (fun x => f x - f' x) * supNorm g +
        supNorm f' * supNorm (fun x => g x - g' x)))
    (f := fun ω => contraction B Fm Gm f g (def_app_vol_product F ω s) (def_app_vol_product F ω t) -
      contraction B Fm Gm f' g' (def_app_vol_product F ω s) (def_app_vol_product F ω t))
    (Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs]
      exact lem_app_vol_finite_iii F.hB γ hdim Fm Gm hF hG f g f' g' hf hg hf' hg' _ _)
  simpa using this

private lemma p5_cont_param (Φ : (ℝ → ℝ) → (ℝ → ℝ) → ℝ) (γ : ℝ) (hγ : 0 ≤ γ)
    (hΦ : ∀ f g f' g' : ℝ → ℝ, IsOddBddLip f → IsOddBddLip g → IsOddBddLip f' → IsOddBddLip g' →
      |Φ f g - Φ f' g'| ≤ γ * (supNorm (fun x => f x - f' x) * supNorm g +
        supNorm f' * supNorm (fun x => g x - g' x)))
    (ϱ ϱ' : ℝ) (hϱ : 0 < ϱ) (hϱ' : 0 < ϱ') :
    Continuous (fun p : ℝ × ℝ => Φ (iotaF (ϱ + p.1 ^ 2)) (iotaF (ϱ' + p.2 ^ 2))) := by
  have hsq : ∀ x : ℝ, 0 ≤ x ^ 2 := fun x => sq_nonneg x
  have hp1 : 0 < ϱ ^ ((3 : ℝ) / 2) := Real.rpow_pos_of_pos hϱ _
  have hp2 : 0 < ϱ' ^ ((3 : ℝ) / 2) := Real.rpow_pos_of_pos hϱ' _
  have hr1 : 0 < Real.sqrt ϱ := Real.sqrt_pos.mpr hϱ
  have hr2 : 0 < Real.sqrt ϱ' := Real.sqrt_pos.mpr hϱ'
  set C1 : ℝ := γ / (ϱ ^ ((3 : ℝ) / 2) * (2 * Real.sqrt ϱ')) with hC1
  set C2 : ℝ := γ / ((2 * Real.sqrt ϱ) * ϱ' ^ ((3 : ℝ) / 2)) with hC2
  have hbound : ∀ x x' y y' : ℝ,
      |Φ (iotaF (ϱ + x ^ 2)) (iotaF (ϱ' + y ^ 2)) - Φ (iotaF (ϱ + x' ^ 2)) (iotaF (ϱ' + y' ^ 2))| ≤
        C1 * |x ^ 2 - x' ^ 2| + C2 * |y ^ 2 - y' ^ 2| := by
    intro x x' y y'
    have hs : 0 < ϱ + x ^ 2 := by linarith [hsq x]
    have hs' : 0 < ϱ + x' ^ 2 := by linarith [hsq x']
    have hu : 0 < ϱ' + y ^ 2 := by linarith [hsq y]
    have hu' : 0 < ϱ' + y' ^ 2 := by linarith [hsq y']
    have hl := hΦ _ _ _ _ (lem_app_vol_sharp_ii hs one_pos).1 (lem_app_vol_sharp_ii hu one_pos).1
      (lem_app_vol_sharp_ii hs' one_pos).1 (lem_app_vol_sharp_ii hu' one_pos).1
    have d1 := (lem_app_vol_sharp_iii hϱ one_pos (s := ϱ + x ^ 2) (s' := ϱ + x' ^ 2) (ϱ := 1)
      (ϱ' := 1) (ϱ₀ := 1) (by linarith [hsq x]) (by linarith [hsq x']) le_rfl le_rfl).1
    have d2 := (lem_app_vol_sharp_iii hϱ' one_pos (s := ϱ' + y ^ 2) (s' := ϱ' + y' ^ 2) (ϱ := 1)
      (ϱ' := 1) (ϱ₀ := 1) (by linarith [hsq y]) (by linarith [hsq y']) le_rfl le_rfl).1
    have n1 : supNorm (iotaF (ϱ' + y ^ 2)) ≤ 1 / (2 * Real.sqrt ϱ') := by
      rw [(lem_app_vol_sharp_ii hu one_pos).2.2.1]
      exact one_div_le_one_div_of_le (by positivity)
        (by have := Real.sqrt_le_sqrt (show ϱ' ≤ ϱ' + y ^ 2 by linarith [hsq y]); linarith)
    have n2 : supNorm (iotaF (ϱ + x' ^ 2)) ≤ 1 / (2 * Real.sqrt ϱ) := by
      rw [(lem_app_vol_sharp_ii hs' one_pos).2.2.1]
      exact one_div_le_one_div_of_le (by positivity)
        (by have := Real.sqrt_le_sqrt (show ϱ ≤ ϱ + x' ^ 2 by linarith [hsq x']); linarith)
    have e1 : |(ϱ + x ^ 2) - (ϱ + x' ^ 2)| = |x ^ 2 - x' ^ 2| := by congr 1; ring
    have e2 : |(ϱ' + y ^ 2) - (ϱ' + y' ^ 2)| = |y ^ 2 - y' ^ 2| := by congr 1; ring
    rw [e1] at d1
    rw [e2] at d2
    have s1 := tx_supNorm_nonneg (fun x_1 => iotaF (ϱ + x ^ 2) x_1 - iotaF (ϱ + x' ^ 2) x_1)
    have s2 := tx_supNorm_nonneg (fun x_1 => iotaF (ϱ' + y ^ 2) x_1 - iotaF (ϱ' + y' ^ 2) x_1)
    have s3 := tx_supNorm_nonneg (iotaF (ϱ' + y ^ 2))
    have s4 := tx_supNorm_nonneg (iotaF (ϱ + x' ^ 2))
    have hd1' : supNorm (fun x_1 => iotaF (ϱ + x ^ 2) x_1 - iotaF (ϱ + x' ^ 2) x_1) ≤
        |x ^ 2 - x' ^ 2| / ϱ ^ ((3 : ℝ) / 2) := by simpa using d1
    have hd2' : supNorm (fun x_1 => iotaF (ϱ' + y ^ 2) x_1 - iotaF (ϱ' + y' ^ 2) x_1) ≤
        |y ^ 2 - y' ^ 2| / ϱ' ^ ((3 : ℝ) / 2) := by simpa using d2
    refine hl.trans ?_
    have m1 := mul_le_mul hd1' n1 s3 (by positivity)
    have m2 := mul_le_mul n2 hd2' s2 (by positivity)
    have := mul_le_mul_of_nonneg_left (add_le_add m1 m2) hγ
    refine this.trans (le_of_eq ?_)
    rw [hC1, hC2]
    field_simp
  have hcont : Continuous (fun p : ℝ × ℝ => Φ (iotaF (ϱ + p.1 ^ 2)) (iotaF (ϱ' + p.2 ^ 2))) := by
    refine continuous_iff_continuousAt.mpr fun b => ?_
    have hb : Tendsto (fun a : ℝ × ℝ => C1 * |a.1 ^ 2 - b.1 ^ 2| + C2 * |a.2 ^ 2 - b.2 ^ 2|)
        (𝓝 b) (𝓝 0) := by
      have hc : Continuous (fun a : ℝ × ℝ => C1 * |a.1 ^ 2 - b.1 ^ 2| + C2 * |a.2 ^ 2 - b.2 ^ 2|) := by
        fun_prop
      simpa using hc.tendsto b
    refine tendsto_iff_dist_tendsto_zero.mpr (squeeze_zero (fun _ => dist_nonneg) (fun a => ?_) hb)
    rw [Real.dist_eq]
    exact hbound _ _ _ _
  exact hcont

private lemma p5_iter_diff (f g : ℝ → ℝ → ℝ) (hf : Continuous (Function.uncurry f))
    (hg : Continuous (Function.uncurry g)) (T ε : ℝ) (hT : 0 ≤ T)
    (h : ∀ x ∈ Set.Icc (0 : ℝ) T, ∀ y ∈ Set.Icc (0 : ℝ) T, |f x y - g x y| ≤ ε) :
    |(∫ x in (0 : ℝ)..T, ∫ y in (0 : ℝ)..T, f x y) - ∫ x in (0 : ℝ)..T, ∫ y in (0 : ℝ)..T, g x y| ≤
      ε * T * T := by
  have hif : Continuous (fun x => ∫ y in (0 : ℝ)..T, f x y) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hf 0 T
  have hig : Continuous (fun x => ∫ y in (0 : ℝ)..T, g x y) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hg 0 T
  rw [← intervalIntegral.integral_sub (hif.intervalIntegrable _ _) (hig.intervalIntegrable _ _)]
  have hinner : ∀ x ∈ Set.Icc (0 : ℝ) T, ‖(∫ y in (0 : ℝ)..T, f x y) - ∫ y in (0 : ℝ)..T, g x y‖ ≤
      ε * T := by
    intro x hx
    have hfx : Continuous (fun y => f x y) := hf.comp (Continuous.prodMk_right x)
    have hgx : Continuous (fun y => g x y) := hg.comp (Continuous.prodMk_right x)
    rw [← intervalIntegral.integral_sub (hfx.intervalIntegrable _ _) (hgx.intervalIntegrable _ _)]
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := T)
      (f := fun y => f x y - g x y) (C := ε) (fun y hy => by
        rw [Real.norm_eq_abs]
        exact h x hx y ⟨(Set.uIoc_of_le hT ▸ hy).1.le, (Set.uIoc_of_le hT ▸ hy).2⟩)
    simpa [abs_of_nonneg hT] using this
  have := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := T)
    (f := fun x => (∫ y in (0 : ℝ)..T, f x y) - ∫ y in (0 : ℝ)..T, g x y) (C := ε * T)
    (fun x hx => hinner x ⟨(Set.uIoc_of_le hT ▸ hx).1.le, (Set.uIoc_of_le hT ▸ hx).2⟩)
  rw [Real.norm_eq_abs] at this
  simpa [abs_of_nonneg hT] using this

private lemma p5_square_unit (cert : Muon.External.GaussianOpNorm) (γstar CSig : ℝ)
    {m n B : ℕ} (Fp : FrozenParams m n B) (S : SpectralData Fp.C)
    (hS : SizeFin Fp.C B γstar CSig) (hCSig : 1 ≤ CSig) (ℓ : ℕ) (T : ℝ) (hT : 1 ≤ T)
    (e1 : Fin m → ℝ) (e2 : Fin n → ℝ)
    (h1 : opNorm (S.uOut * Matrix.diagonal e1 * S.uOutᵀ) ≤ 1)
    (h2 : opNorm (S.vIn * Matrix.diagonal e2 * S.vInᵀ) ≤ 1)
    (ϱ ϱ' : ℝ) (hϱ : 0 < ϱ) (hϱ' : 0 < ϱ') :
    Continuous (fun p : ℝ × ℝ => lagResp cert γstar CSig Fp.β ℓ B S.μ S.lam e1 e2
        (iotaF (ϱ + p.1 ^ 2)) (iotaF (ϱ' + p.2 ^ 2))) ∧
    |lagResp cert γstar CSig Fp.β ℓ B S.μ S.lam e1 e2 (omegaF ϱ) (omegaF ϱ') -
        (4 / Real.pi ^ 2) * (∫ x in (0 : ℝ)..T, (∫ y in (0 : ℝ)..T,
          lagResp cert γstar CSig Fp.β ℓ B S.μ S.lam e1 e2 (iotaF (ϱ + x ^ 2))
            (iotaF (ϱ' + y ^ 2))))| ≤
      4 * CSig * (γstar * Real.sqrt γstar) / (Real.pi * T) := by
  have hγ := tx_gamma_nonneg Fp γstar CSig hS
  have hCs : 0 ≤ CSig := by linarith
  have hTpos : 0 < T := by linarith
  have hω1 := (lem_app_vol_sharp_ii hϱ hϱ).2.1
  have hω2 := (lem_app_vol_sharp_ii hϱ' hϱ').2.1
  have hgL : Continuous (fun p : ℝ × ℝ => lagResp cert γstar CSig Fp.β ℓ B S.μ S.lam e1 e2
        (iotaF (ϱ + p.1 ^ 2)) (iotaF (ϱ' + p.2 ^ 2))) :=
    p5_cont_param (fun f g => lagResp cert γstar CSig Fp.β ℓ B S.μ S.lam e1 e2 f g) γstar hγ
      (fun f g f' g' hf hg hf' hg' =>
        p5_L_filter_lip cert γstar CSig Fp S hS hCSig ℓ e1 e2 h1 h2 f g f' g' hf hg hf' hg')
      ϱ ϱ' hϱ hϱ'
  refine ⟨hgL, ?_⟩
  obtain ⟨rF, Sp, hSz, hβ, hμ, hl, hUF, hVG⟩ := p5_repl_seq Fp S γstar CSig hS
  have hF1 : ∀ k, opNorm ((Sp k).uOut * Matrix.diagonal (replVec (k + 1) e1) * (Sp k).uOutᵀ) ≤ 1 :=
    fun k => by rw [hUF k]; exact (tx_replMat_opNorm_le _).trans h1
  have hG1 : ∀ k, opNorm ((Sp k).vIn * Matrix.diagonal (replVec (k + 1) e2) * (Sp k).vInᵀ) ≤ 1 :=
    fun k => by rw [hVG k]; exact (tx_replMat_opNorm_le _).trans h2
  have hrep : ∀ f g : ℝ → ℝ, IsOddBddLip f → IsOddBddLip g → ∀ k : ℕ,
      lagResp cert γstar CSig (rF k).β ℓ ((k + 1) * B) (Sp k).μ (Sp k).lam
        (replVec (k + 1) e1) (replVec (k + 1) e2) f g =
      lagResp cert γstar CSig Fp.β ℓ B S.μ S.lam e1 e2 f g := by
    intro f g hf hg k
    rw [hβ k, hμ k, hl k]
    exact (thm_app_vol_lag_kernel_bilinear_bound_replication cert γstar CSig Fp S hS hCSig ℓ
      f g hf hg).2.2.2.2.2 (k + 1) (Nat.succ_pos k) e1 e2
  obtain ⟨J, hJ⟩ : ∃ J : Set ℝ, J = Set.Icc (min ϱ ϱ') (max (ϱ + T ^ 2) (ϱ' + T ^ 2)) := ⟨_, rfl⟩
  have hJc : IsCompact J := hJ ▸ isCompact_Icc
  have hJpos : J ⊆ Set.Ioi 0 := fun x hx => by
    rw [hJ] at hx
    exact lt_of_lt_of_le (lt_min hϱ hϱ') hx.1
  have hclo := (thm_app_vol_lag_kernel_closure_indep cert γstar CSig ((m : ℝ) / B) ((n : ℝ) / B)
    hCSig 1 1 ⟨one_pos, le_rfl⟩ (fun k => (k + 1) * m) (fun k => (k + 1) * n)
    (fun k => (k + 1) * B) rF Sp hSz Fp.β Fp.hβ.2 (fun k => (hβ k).le) ℓ J hJc hJpos).1
  have hgen := lag_closure_generic cert γstar CSig ((m : ℝ) / B) ((n : ℝ) / B) hCSig
    (fun k => (k + 1) * m) (fun k => (k + 1) * n) (fun k => (k + 1) * B) rF Sp hSz Fp.β
    Fp.hβ.2 (fun k => (hβ k).le) ℓ (omegaF ϱ) (omegaF ϱ') hω1 hω2
  have hπ : 0 < Real.pi := Real.pi_pos
  have hcore : ∀ ε : ℝ, 0 < ε →
      |lagResp cert γstar CSig Fp.β ℓ B S.μ S.lam e1 e2 (omegaF ϱ) (omegaF ϱ') -
        (4 / Real.pi ^ 2) * (∫ x in (0 : ℝ)..T, (∫ y in (0 : ℝ)..T,
          lagResp cert γstar CSig Fp.β ℓ B S.μ S.lam e1 e2 (iotaF (ϱ + x ^ 2))
            (iotaF (ϱ' + y ^ 2))))| ≤
      4 * CSig * (γstar * Real.sqrt γstar) / (Real.pi * T) +
        (ε + 4 / Real.pi ^ 2 * (ε * T * T)) := by
    intro ε hε
    obtain ⟨k, hk1, hk2⟩ := ((hclo ε hε).and (hgen ε hε)).exists
    have hsz := hSz.1 k
    have hdim : ((min ((k + 1) * m) ((k + 1) * n) : ℕ) : ℝ) ≤ γstar * (((k + 1) * B : ℕ) : ℝ) :=
      le_trans (by exact_mod_cast (min_le_max : min ((k + 1) * m) ((k + 1) * n) ≤
        max ((k + 1) * m) ((k + 1) * n))) hsz.1
    obtain ⟨Fm, hFm⟩ : ∃ Fm : Mat ((k + 1) * m) ((k + 1) * m), Fm =
      (Sp k).uOut * Matrix.diagonal (replVec (k + 1) e1) * (Sp k).uOutᵀ := ⟨_, rfl⟩
    obtain ⟨Gm, hGm⟩ : ∃ Gm : Mat ((k + 1) * n) ((k + 1) * n), Gm =
      (Sp k).vIn * Matrix.diagonal (replVec (k + 1) e2) * (Sp k).vInᵀ := ⟨_, rfl⟩
    have hF : opNorm Fm ≤ 1 := by rw [hFm]; exact hF1 k
    have hG : opNorm Gm ≤ 1 := by rw [hGm]; exact hG1 k
    -- the three comparison steps
    have a1 := hk2 0 (replVec (k + 1) e1) (replVec (k + 1) e2) Fm Gm hFm hGm hF hG
    rw [hrep _ _ hω1 hω2 k] at a1
    have hfk : Continuous (fun p : ℝ × ℝ => ∫ ω, contraction ((k + 1) * B) Fm Gm
        (iotaF (ϱ + p.1 ^ 2)) (iotaF (ϱ' + p.2 ^ 2)) (def_app_vol_product (rF k) ω 0)
        (def_app_vol_product (rF k) ω (0 + (ℓ : ℤ))) ∂(indepSpaceLaw ((k + 1) * m) ((k + 1) * n)
          ((k + 1) * B))) :=
      p5_cont_param (fun f g => ∫ ω, contraction ((k + 1) * B) Fm Gm f g
        (def_app_vol_product (rF k) ω 0) (def_app_vol_product (rF k) ω (0 + (ℓ : ℤ)))
          ∂(indepSpaceLaw ((k + 1) * m) ((k + 1) * n) ((k + 1) * B))) γstar hγ
        (fun f g f' g' hf hg hf' hg' =>
          p5_contr_filter_lip (rF k) γstar hdim Fm Gm hF hG 0 (0 + (ℓ : ℤ)) f g f' g' hf hg hf' hg')
        ϱ ϱ' hϱ hϱ'
    have hdiff : ∀ x ∈ Set.Icc (0 : ℝ) T, ∀ y ∈ Set.Icc (0 : ℝ) T,
        |(∫ ω, contraction ((k + 1) * B) Fm Gm (iotaF (ϱ + x ^ 2)) (iotaF (ϱ' + y ^ 2))
            (def_app_vol_product (rF k) ω 0) (def_app_vol_product (rF k) ω (0 + (ℓ : ℤ)))
            ∂(indepSpaceLaw ((k + 1) * m) ((k + 1) * n) ((k + 1) * B))) -
          lagResp cert γstar CSig Fp.β ℓ B S.μ S.lam e1 e2 (iotaF (ϱ + x ^ 2))
            (iotaF (ϱ' + y ^ 2))| ≤ ε := by
      intro x hx y hy
      have hs : ϱ + x ^ 2 ∈ J := by
        rw [hJ]
        refine ⟨le_trans (min_le_left _ _) (by nlinarith [sq_nonneg x]),
          le_trans ?_ (le_max_left _ _)⟩
        nlinarith [hx.2, hx.1]
      have hu : ϱ' + y ^ 2 ∈ J := by
        rw [hJ]
        refine ⟨le_trans (min_le_right _ _) (by nlinarith [sq_nonneg y]),
          le_trans ?_ (le_max_right _ _)⟩
        nlinarith [hy.2, hy.1]
      have := hk1 0 (ϱ + x ^ 2) hs (ϱ' + y ^ 2) hu (replVec (k + 1) e1) (replVec (k + 1) e2) Fm Gm
        hFm hGm hF hG
      rw [hrep _ _ (lem_app_vol_sharp_ii (by nlinarith [sq_nonneg x]) one_pos).1
        (lem_app_vol_sharp_ii (by nlinarith [sq_nonneg y]) one_pos).1 k] at this
      exact this
    have hit := p5_iter_diff
      (fun x y => ∫ ω, contraction ((k + 1) * B) Fm Gm (iotaF (ϱ + x ^ 2)) (iotaF (ϱ' + y ^ 2))
            (def_app_vol_product (rF k) ω 0) (def_app_vol_product (rF k) ω (0 + (ℓ : ℤ)))
            ∂(indepSpaceLaw ((k + 1) * m) ((k + 1) * n) ((k + 1) * B)))
      (fun x y => lagResp cert γstar CSig Fp.β ℓ B S.μ S.lam e1 e2 (iotaF (ϱ + x ^ 2))
            (iotaF (ϱ' + y ^ 2))) hfk hgL T ε hTpos.le hdiff
    haveI : IsProbabilityMeasure (indepSpaceLaw ((k + 1) * m) ((k + 1) * n) ((k + 1) * B)) :=
      p5r_indep_prob _ _ _
    have hsq := lem_app_vol_square_ii (indepSpaceLaw ((k + 1) * m) ((k + 1) * n) ((k + 1) * B))
      (rF k).hB γstar (CSig ^ 2 * γstar ^ 2) hdim Fm Gm hF hG
      (fun ω => def_app_vol_product (rF k) ω 0) (fun ω => def_app_vol_product (rF k) ω (0 + (ℓ : ℤ)))
      (fun i j => (measurable_pi_apply j).comp ((measurable_pi_apply i).comp (p5_prod_meas (rF k) 0)))
      (fun i j => (measurable_pi_apply j).comp ((measurable_pi_apply i).comp
        (p5_prod_meas (rF k) (0 + (ℓ : ℤ)))))
      (p5r_product_moment_lintegral (rF k) γstar CSig hsz 0)
      (p5r_product_moment_lintegral (rF k) γstar CSig hsz (0 + (ℓ : ℤ))) ϱ ϱ' T hϱ hϱ' hTpos
    have hrt : Real.sqrt (γstar * (CSig ^ 2 * γstar ^ 2)) = CSig * (γstar * Real.sqrt γstar) := by
      rw [show γstar * (CSig ^ 2 * γstar ^ 2) = (CSig * γstar) ^ 2 * γstar by ring,
        Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (mul_nonneg hCs hγ)]
      ring
    rw [hrt] at hsq
    set A := ∫ ω, contraction ((k + 1) * B) Fm Gm (omegaF ϱ) (omegaF ϱ')
      (def_app_vol_product (rF k) ω 0) (def_app_vol_product (rF k) ω (0 + (ℓ : ℤ)))
      ∂(indepSpaceLaw ((k + 1) * m) ((k + 1) * n) ((k + 1) * B)) with hA
    set Xf := ∫ x in (0 : ℝ)..T, ∫ y in (0 : ℝ)..T, ∫ ω, contraction ((k + 1) * B) Fm Gm
      (iotaF (ϱ + x ^ 2)) (iotaF (ϱ' + y ^ 2)) (def_app_vol_product (rF k) ω 0)
      (def_app_vol_product (rF k) ω (0 + (ℓ : ℤ)))
      ∂(indepSpaceLaw ((k + 1) * m) ((k + 1) * n) ((k + 1) * B)) with hXf
    set Xg := ∫ x in (0 : ℝ)..T, ∫ y in (0 : ℝ)..T, lagResp cert γstar CSig Fp.β ℓ B S.μ S.lam e1 e2
      (iotaF (ϱ + x ^ 2)) (iotaF (ϱ' + y ^ 2)) with hXg
    set Lw := lagResp cert γstar CSig Fp.β ℓ B S.μ S.lam e1 e2 (omegaF ϱ) (omegaF ϱ') with hLw
    have e : Lw - 4 / Real.pi ^ 2 * Xg = (Lw - A) + (A - 4 / Real.pi ^ 2 * Xf) +
        (4 / Real.pi ^ 2 * (Xf - Xg)) := by ring
    have hpi2 : 0 ≤ 4 / Real.pi ^ 2 := by positivity
    have t3 : |4 / Real.pi ^ 2 * (Xf - Xg)| ≤ 4 / Real.pi ^ 2 * (ε * T * T) := by
      rw [abs_mul, abs_of_nonneg hpi2]
      exact mul_le_mul_of_nonneg_left hit hpi2
    have t1 : |Lw - A| ≤ ε := by rw [abs_sub_comm]; exact a1
    rw [e]
    calc _ ≤ |Lw - A| + |A - 4 / Real.pi ^ 2 * Xf| + |4 / Real.pi ^ 2 * (Xf - Xg)| := by
          refine (abs_add_le _ _).trans ?_
          gcongr
          exact abs_add_le _ _
      _ ≤ _ := by
          have := hsq
          have h4 : 4 * (CSig * (γstar * Real.sqrt γstar)) / (Real.pi * T) =
              4 * CSig * (γstar * Real.sqrt γstar) / (Real.pi * T) := by ring
          linarith
  refine le_of_forall_pos_le_add fun δ hδ => ?_
  have hc : 0 < 1 + 4 / Real.pi ^ 2 * (T * T) := by positivity
  have := hcore (δ / (1 + 4 / Real.pi ^ 2 * (T * T))) (by positivity)
  refine this.trans (le_of_eq ?_)
  field_simp

end P5Helpers
-- P5-HELPERS-END

/-- `thm:app-vol-integrated`, snapshot `cr-2026-10-23`. Declaration of record. LaTeX, verbatim from `section.tex` (the whole environment):

```latex
\begin{theorem}[Integrated identification]\label{thm:app-vol-integrated}
Fix a finite dimension, diagonal $F,G$, and $\ridge,\ridge'\in I$.
\begin{enumerate}[label=(\roman*)]
\item For every $\ell\ge0$ and $T\ge1$,
\begin{equation}\label{eqn:app-vol-integrated-square}
\Big|\overline C_\ell[F,G](\ridge,\ridge')-\frac4{\pi^2}\int_0^T\!\!\int_0^T\mathfrak k_\ell[F,G](\ridge+x^2,\ridge'+y^2)\,dx\,dy\Big|\le\frac{4C_\Sigma\gamma_\star^{3/2}\norm F\norm G}{\pi T},
\end{equation}
so $\overline C_\ell[F,G]$ is the square-truncated double integral of the lag
kernel along the negative axis, with an error uniform in the dimension, the
lag and the ridges.
\item $\abs{\overline C_0[F,G]}\le\gamma_\star\norm F\norm G$ and
$\abs{\overline C_\ell[F,G]}\le\mathsf K_\star\norm F\norm G\,\bmom^\ell$ for $\ell\ge1$; at
$\bmom=0$, $\overline C_\ell[F,G]=0$ for every $\ell\ge1$.
\item The deterministic integrated coefficient
\begin{equation}\label{eqn:app-vol-Gammabar}
\overline\Gamma[F,G](\ridge,\ridge')\defeq\overline C_0[F,G](\ridge,\ridge')+\sum_{\ell\ge1}\Big(\overline C_\ell[F,G](\ridge,\ridge')+\overline C_\ell[F,G](\ridge',\ridge)\Big)
\end{equation}
converges absolutely, and $\overline\Gamma[F,G](\ridge,\ridge)\ge0$ whenever $F$ and
$G$ are positive semidefinite.
\item Under \cref{assum:app-setup-regime},
$\sup_{\ridge,\ridge'\in I}\sup_{F,G}\abs{\Gamma[F,G](\ridge,\ridge')-\overline\Gamma[F,G](\ridge,\ridge')}\to0$,
the supremum over diagonal $F,G$ of norm at most one, and the finite-time
contraction \cref{eqn:app-vol-finite-time} differs from $\overline\Gamma[F,G]$ by
$o(1)$ plus \cref{eqn:app-vol-finite-time-error}, along every joint sequence
of dimensions and block lengths $T$.
\item For the covariance-weighted coefficient
$\overline\Gamma\defeq\overline\Gamma[\Sigmaout,\Sigmain]$, $\sup_{I^2}\abs{\Gamma-\overline\Gamma}\to0$
under \cref{assum:app-setup-regime}. When $\Sigmain=\Id$,
$\overline C_0(\ridge,\ridge)=\overline Z(\ridge)$ of \cref{eqn:app-vol-half-candidates}.
\end{enumerate}
\end{theorem}
```
-/
theorem thm_app_vol_integrated_i (cert : Muon.External.GaussianOpNorm) (γstar CSig : ℝ)
    {m n B : ℕ} (Fp : FrozenParams m n B) (S : SpectralData Fp.C) (hS : SizeFin Fp.C B γstar CSig)
    (hCSig : 1 ≤ CSig) (ℓ : ℕ) (T : ℝ) (hT : 1 ≤ T) (Fm : Mat m m) (Gm : Mat n n)
    (Fd : Fin m → ℝ) (Gd : Fin n → ℝ)
    (hFd : Fm = S.uOut * Matrix.diagonal Fd * S.uOutᵀ) (hGd : Gm = S.vIn * Matrix.diagonal Gd * S.vInᵀ)
    (ϱ ϱ' : ℝ) (hϱ : 0 < ϱ) (hϱ' : 0 < ϱ') :
    IntegrableOn (fun p : ℝ × ℝ => lagResp cert γstar CSig Fp.β ℓ B S.μ S.lam Fd Gd
        (iotaF (ϱ + p.1 ^ 2)) (iotaF (ϱ' + p.2 ^ 2)))
      (Set.Icc 0 T ×ˢ Set.Icc 0 T) ∧
    |lagResp cert γstar CSig Fp.β ℓ B S.μ S.lam Fd Gd (omegaF ϱ) (omegaF ϱ') -
        (4 / Real.pi ^ 2) * (∫ x in (0 : ℝ)..T, (∫ y in (0 : ℝ)..T,
          lagResp cert γstar CSig Fp.β ℓ B S.μ S.lam Fd Gd (iotaF (ϱ + x ^ 2)) (iotaF (ϱ' + y ^ 2))))| ≤
      4 * CSig * (γstar * Real.sqrt γstar) * opNorm Fm * opNorm Gm / (Real.pi * T) := by
  subst hFd hGd
  obtain ⟨e1, he1, hn1⟩ := p3_normalize S.uOut S.huOut Fd
  obtain ⟨e2, he2, hn2⟩ := p3_normalize S.vIn S.hvIn Gd
  obtain ⟨hc, hb⟩ := p5_square_unit cert γstar CSig Fp S hS hCSig ℓ T hT e1 e2 hn1 hn2 ϱ ϱ' hϱ hϱ'
  obtain ⟨a, ha⟩ : ∃ a, a = opNorm (S.uOut * Matrix.diagonal Fd * S.uOutᵀ) := ⟨_, rfl⟩
  obtain ⟨b, hbb⟩ : ∃ b, b = opNorm (S.vIn * Matrix.diagonal Gd * S.vInᵀ) := ⟨_, rfl⟩
  rw [← ha] at he1
  rw [← hbb] at he2
  rw [← ha, ← hbb]
  have ha0 : 0 ≤ a := ha ▸ tx_opNorm_nonneg _
  have hb0 : 0 ≤ b := hbb ▸ tx_opNorm_nonneg _
  have hsc : ∀ f g : ℝ → ℝ, IsOddBddLip f → IsOddBddLip g →
      lagResp cert γstar CSig Fp.β ℓ B S.μ S.lam Fd Gd f g =
        a * b * lagResp cert γstar CSig Fp.β ℓ B S.μ S.lam e1 e2 f g := by
    intro f g hf hg
    have := p3_lag_scale cert γstar CSig Fp S hS hCSig ℓ a b e1 e2 f g hf hg
    rwa [← he1, ← he2] at this
  have hio : ∀ s : ℝ, 0 < s → IsOddBddLip (iotaF s) := fun s hs => (lem_app_vol_sharp_ii hs one_pos).1
  have hsc' : ∀ x y : ℝ, lagResp cert γstar CSig Fp.β ℓ B S.μ S.lam Fd Gd (iotaF (ϱ + x ^ 2))
      (iotaF (ϱ' + y ^ 2)) = a * b * lagResp cert γstar CSig Fp.β ℓ B S.μ S.lam e1 e2
        (iotaF (ϱ + x ^ 2)) (iotaF (ϱ' + y ^ 2)) := fun x y =>
    hsc _ _ (hio _ (by nlinarith [sq_nonneg x])) (hio _ (by nlinarith [sq_nonneg y]))
  have hωo := hsc _ _ (lem_app_vol_sharp_ii hϱ hϱ).2.1 (lem_app_vol_sharp_ii hϱ' hϱ').2.1
  refine ⟨?_, ?_⟩
  · have : (fun p : ℝ × ℝ => lagResp cert γstar CSig Fp.β ℓ B S.μ S.lam Fd Gd
        (iotaF (ϱ + p.1 ^ 2)) (iotaF (ϱ' + p.2 ^ 2))) = fun p : ℝ × ℝ =>
        a * b * lagResp cert γstar CSig Fp.β ℓ B S.μ S.lam e1 e2
          (iotaF (ϱ + p.1 ^ 2)) (iotaF (ϱ' + p.2 ^ 2)) := funext fun p => hsc' p.1 p.2
    rw [this]
    exact ((hc.const_mul (a * b)).continuousOn).integrableOn_compact
      (isCompact_Icc.prod isCompact_Icc)
  · simp only [hsc', hωo, intervalIntegral.integral_const_mul]
    have e : a * b * lagResp cert γstar CSig Fp.β ℓ B S.μ S.lam e1 e2 (omegaF ϱ) (omegaF ϱ') -
        4 / Real.pi ^ 2 * (a * b * ∫ x in (0 : ℝ)..T, ∫ y in (0 : ℝ)..T,
          lagResp cert γstar CSig Fp.β ℓ B S.μ S.lam e1 e2 (iotaF (ϱ + x ^ 2))
            (iotaF (ϱ' + y ^ 2))) = a * b * (lagResp cert γstar CSig Fp.β ℓ B S.μ S.lam e1 e2
          (omegaF ϱ) (omegaF ϱ') - 4 / Real.pi ^ 2 * ∫ x in (0 : ℝ)..T, ∫ y in (0 : ℝ)..T,
          lagResp cert γstar CSig Fp.β ℓ B S.μ S.lam e1 e2 (iotaF (ϱ + x ^ 2))
            (iotaF (ϱ' + y ^ 2))) := by ring
    rw [e, abs_mul, abs_of_nonneg (mul_nonneg ha0 hb0)]
    calc a * b * _ ≤ a * b * (4 * CSig * (γstar * Real.sqrt γstar) / (Real.pi * T)) :=
          mul_le_mul_of_nonneg_left hb (mul_nonneg ha0 hb0)
      _ = _ := by ring

/-- `thm:app-vol-integrated`, snapshot `cr-2026-10-23`. Declaration of record. LaTeX, verbatim from `section.tex` (the whole environment):

```latex
\begin{theorem}[Integrated identification]\label{thm:app-vol-integrated}
Fix a finite dimension, diagonal $F,G$, and $\ridge,\ridge'\in I$.
\begin{enumerate}[label=(\roman*)]
\item For every $\ell\ge0$ and $T\ge1$,
\begin{equation}\label{eqn:app-vol-integrated-square}
\Big|\overline C_\ell[F,G](\ridge,\ridge')-\frac4{\pi^2}\int_0^T\!\!\int_0^T\mathfrak k_\ell[F,G](\ridge+x^2,\ridge'+y^2)\,dx\,dy\Big|\le\frac{4C_\Sigma\gamma_\star^{3/2}\norm F\norm G}{\pi T},
\end{equation}
so $\overline C_\ell[F,G]$ is the square-truncated double integral of the lag
kernel along the negative axis, with an error uniform in the dimension, the
lag and the ridges.
\item $\abs{\overline C_0[F,G]}\le\gamma_\star\norm F\norm G$ and
$\abs{\overline C_\ell[F,G]}\le\mathsf K_\star\norm F\norm G\,\bmom^\ell$ for $\ell\ge1$; at
$\bmom=0$, $\overline C_\ell[F,G]=0$ for every $\ell\ge1$.
\item The deterministic integrated coefficient
\begin{equation}\label{eqn:app-vol-Gammabar}
\overline\Gamma[F,G](\ridge,\ridge')\defeq\overline C_0[F,G](\ridge,\ridge')+\sum_{\ell\ge1}\Big(\overline C_\ell[F,G](\ridge,\ridge')+\overline C_\ell[F,G](\ridge',\ridge)\Big)
\end{equation}
converges absolutely, and $\overline\Gamma[F,G](\ridge,\ridge)\ge0$ whenever $F$ and
$G$ are positive semidefinite.
\item Under \cref{assum:app-setup-regime},
$\sup_{\ridge,\ridge'\in I}\sup_{F,G}\abs{\Gamma[F,G](\ridge,\ridge')-\overline\Gamma[F,G](\ridge,\ridge')}\to0$,
the supremum over diagonal $F,G$ of norm at most one, and the finite-time
contraction \cref{eqn:app-vol-finite-time} differs from $\overline\Gamma[F,G]$ by
$o(1)$ plus \cref{eqn:app-vol-finite-time-error}, along every joint sequence
of dimensions and block lengths $T$.
\item For the covariance-weighted coefficient
$\overline\Gamma\defeq\overline\Gamma[\Sigmaout,\Sigmain]$, $\sup_{I^2}\abs{\Gamma-\overline\Gamma}\to0$
under \cref{assum:app-setup-regime}. When $\Sigmain=\Id$,
$\overline C_0(\ridge,\ridge)=\overline Z(\ridge)$ of \cref{eqn:app-vol-half-candidates}.
\end{enumerate}
\end{theorem}
```
-/
theorem thm_app_vol_integrated_ii (cert : Muon.External.GaussianOpNorm) (γstar CSig : ℝ)
    {m n B : ℕ} (Fp : FrozenParams m n B) (S : SpectralData Fp.C) (hS : SizeFin Fp.C B γstar CSig)
    (hCSig : 1 ≤ CSig) (ϱlo ϱhi : ℝ) (hϱ : 0 < ϱlo ∧ ϱlo ≤ ϱhi)
    (Fm : Mat m m) (Gm : Mat n n) (Fd : Fin m → ℝ) (Gd : Fin n → ℝ)
    (hFd : Fm = S.uOut * Matrix.diagonal Fd * S.uOutᵀ) (hGd : Gm = S.vIn * Matrix.diagonal Gd * S.vInᵀ)
    (ϱ ϱ' : ℝ)
    (hϱI : ϱ ∈ Set.Icc ϱlo ϱhi) (hϱ'I : ϱ' ∈ Set.Icc ϱlo ϱhi) :
    |lagResp cert γstar CSig Fp.β 0 B S.μ S.lam Fd Gd (omegaF ϱ) (omegaF ϱ')| ≤
        γstar * opNorm Fm * opNorm Gm ∧
      (∀ ℓ : ℕ, 1 ≤ ℓ → |lagResp cert γstar CSig Fp.β ℓ B S.μ S.lam Fd Gd (omegaF ϱ) (omegaF ϱ')| ≤
        Muon.Dynamics.kStar CSig γstar ϱlo * opNorm Fm * opNorm Gm * Fp.β ^ ℓ) ∧
      (Fp.β = 0 → ∀ ℓ : ℕ, 1 ≤ ℓ →
        lagResp cert γstar CSig Fp.β ℓ B S.μ S.lam Fd Gd (omegaF ϱ) (omegaF ϱ') = 0) := by
  have hϱ1 : 0 < ϱ := lt_of_lt_of_le hϱ.1 hϱI.1
  have hϱ2 : 0 < ϱ' := lt_of_lt_of_le hϱ.1 hϱ'I.1
  have hf := (lem_app_vol_sharp_ii hϱ1 hϱ1).2.1
  have hg := (lem_app_vol_sharp_ii hϱ2 hϱ2).2.1
  have h2 : ∀ ℓ : ℕ, 1 ≤ ℓ →
      |lagResp cert γstar CSig Fp.β ℓ B S.μ S.lam Fd Gd (omegaF ϱ) (omegaF ϱ')| ≤
        Muon.Dynamics.kStar CSig γstar ϱlo * opNorm Fm * opNorm Gm * Fp.β ^ ℓ := by
    intro ℓ hℓ
    obtain ⟨e1, he1, hn1⟩ := p3_normalize S.uOut S.huOut Fd
    obtain ⟨e2, he2, hn2⟩ := p3_normalize S.vIn S.hvIn Gd
    have hu := p5_unit_lag_bound cert γstar CSig Fp S hS hCSig ϱlo ϱhi hϱ ℓ hℓ e1 e2 hn1 hn2
      ϱ ϱ' hϱI hϱ'I
    subst hFd hGd
    conv_lhs => rw [he1, he2, p3_lag_scale cert γstar CSig Fp S hS hCSig ℓ _ _ e1 e2 _ _ hf hg]
    rw [abs_mul, abs_mul, abs_of_nonneg (tx_opNorm_nonneg _), abs_of_nonneg (tx_opNorm_nonneg _)]
    have := mul_le_mul_of_nonneg_left hu
      (mul_nonneg (tx_opNorm_nonneg (S.uOut * Matrix.diagonal Fd * S.uOutᵀ))
        (tx_opNorm_nonneg (S.vIn * Matrix.diagonal Gd * S.vInᵀ)))
    nlinarith [this]
  refine ⟨?_, h2, ?_⟩
  · have hb := (thm_app_vol_lag_kernel_bilinear_bound_replication cert γstar CSig Fp S hS hCSig 0
      (omegaF ϱ) (omegaF ϱ') hf hg).1 Fm Gm Fd Gd hFd hGd
    rw [(lem_app_vol_sharp_ii hϱ1 hϱ1).2.2.2.2.1, (lem_app_vol_sharp_ii hϱ2 hϱ2).2.2.2.2.1] at hb
    simpa using hb
  · intro hβ0 ℓ hℓ
    have h3 := h2 ℓ hℓ
    have h4 : Muon.Dynamics.kStar CSig γstar ϱlo * opNorm Fm * opNorm Gm * Fp.β ^ ℓ = 0 := by
      rw [hβ0, zero_pow (by omega), mul_zero]
    rw [h4] at h3
    exact abs_nonpos_iff.mp h3

/-- `thm:app-vol-integrated`, snapshot `cr-2026-10-23`. Declaration of record. LaTeX, verbatim from `section.tex` (the whole environment):

```latex
\begin{theorem}[Integrated identification]\label{thm:app-vol-integrated}
Fix a finite dimension, diagonal $F,G$, and $\ridge,\ridge'\in I$.
\begin{enumerate}[label=(\roman*)]
\item For every $\ell\ge0$ and $T\ge1$,
\begin{equation}\label{eqn:app-vol-integrated-square}
\Big|\overline C_\ell[F,G](\ridge,\ridge')-\frac4{\pi^2}\int_0^T\!\!\int_0^T\mathfrak k_\ell[F,G](\ridge+x^2,\ridge'+y^2)\,dx\,dy\Big|\le\frac{4C_\Sigma\gamma_\star^{3/2}\norm F\norm G}{\pi T},
\end{equation}
so $\overline C_\ell[F,G]$ is the square-truncated double integral of the lag
kernel along the negative axis, with an error uniform in the dimension, the
lag and the ridges.
\item $\abs{\overline C_0[F,G]}\le\gamma_\star\norm F\norm G$ and
$\abs{\overline C_\ell[F,G]}\le\mathsf K_\star\norm F\norm G\,\bmom^\ell$ for $\ell\ge1$; at
$\bmom=0$, $\overline C_\ell[F,G]=0$ for every $\ell\ge1$.
\item The deterministic integrated coefficient
\begin{equation}\label{eqn:app-vol-Gammabar}
\overline\Gamma[F,G](\ridge,\ridge')\defeq\overline C_0[F,G](\ridge,\ridge')+\sum_{\ell\ge1}\Big(\overline C_\ell[F,G](\ridge,\ridge')+\overline C_\ell[F,G](\ridge',\ridge)\Big)
\end{equation}
converges absolutely, and $\overline\Gamma[F,G](\ridge,\ridge)\ge0$ whenever $F$ and
$G$ are positive semidefinite.
\item Under \cref{assum:app-setup-regime},
$\sup_{\ridge,\ridge'\in I}\sup_{F,G}\abs{\Gamma[F,G](\ridge,\ridge')-\overline\Gamma[F,G](\ridge,\ridge')}\to0$,
the supremum over diagonal $F,G$ of norm at most one, and the finite-time
contraction \cref{eqn:app-vol-finite-time} differs from $\overline\Gamma[F,G]$ by
$o(1)$ plus \cref{eqn:app-vol-finite-time-error}, along every joint sequence
of dimensions and block lengths $T$.
\item For the covariance-weighted coefficient
$\overline\Gamma\defeq\overline\Gamma[\Sigmaout,\Sigmain]$, $\sup_{I^2}\abs{\Gamma-\overline\Gamma}\to0$
under \cref{assum:app-setup-regime}. When $\Sigmain=\Id$,
$\overline C_0(\ridge,\ridge)=\overline Z(\ridge)$ of \cref{eqn:app-vol-half-candidates}.
\end{enumerate}
\end{theorem}
```
-/
theorem thm_app_vol_integrated_iii (cert : Muon.External.GaussianOpNorm) (γstar CSig : ℝ)
    {m n B : ℕ} (Fp : FrozenParams m n B) (S : SpectralData Fp.C) (hS : SizeFin Fp.C B γstar CSig)
    (hCSig : 1 ≤ CSig) (Fm : Mat m m) (Gm : Mat n n) (Fd : Fin m → ℝ) (Gd : Fin n → ℝ)
    (hFd : Fm = S.uOut * Matrix.diagonal Fd * S.uOutᵀ) (hGd : Gm = S.vIn * Matrix.diagonal Gd * S.vInᵀ)
    (ϱlo ϱhi : ℝ) (hϱ : 0 < ϱlo ∧ ϱlo ≤ ϱhi)
    (ϱ ϱ' : ℝ) (hϱI : ϱ ∈ Set.Icc ϱlo ϱhi) (hϱ'I : ϱ' ∈ Set.Icc ϱlo ϱhi) :
    Summable (fun ℓ : ℕ => |lagResp cert γstar CSig Fp.β (ℓ + 1) B S.μ S.lam Fd Gd (omegaF ϱ) (omegaF ϱ') +
        lagResp cert γstar CSig Fp.β (ℓ + 1) B S.μ S.lam Fd Gd (omegaF ϱ') (omegaF ϱ)|) ∧
      (Fm.PosSemidef → Gm.PosSemidef →
        0 ≤ lagGammaBar cert γstar CSig Fp.β B S.μ S.lam Fd Gd ϱ ϱ) := by
  have hϱ1 : 0 < ϱ := lt_of_lt_of_le hϱ.1 hϱI.1
  have hϱ2 : 0 < ϱ' := lt_of_lt_of_le hϱ.1 hϱ'I.1
  have hii := fun (a b : ℝ) (ha : a ∈ Set.Icc ϱlo ϱhi) (hb : b ∈ Set.Icc ϱlo ϱhi) =>
    thm_app_vol_integrated_ii cert γstar CSig Fp S hS hCSig ϱlo ϱhi hϱ Fm Gm Fd Gd hFd hGd a b ha hb
  refine ⟨?_, ?_⟩
  · obtain ⟨hβ0, hβ1⟩ := Fp.hβ
    have hgeo : Summable (fun n : ℕ => Fp.β ^ n) := summable_geometric_of_lt_one hβ0 hβ1
    have hgeo1 : Summable (fun n : ℕ => Fp.β ^ (n + 1)) := (summable_nat_add_iff 1).mpr hgeo
    refine Summable.of_nonneg_of_le (fun ℓ => abs_nonneg _) (fun ℓ => ?_)
      (hgeo1.mul_left (2 * Muon.Dynamics.kStar CSig γstar ϱlo * opNorm Fm * opNorm Gm))
    have h1 := (hii ϱ ϱ' hϱI hϱ'I).2.1 (ℓ + 1) (by omega)
    have h2 := (hii ϱ' ϱ hϱ'I hϱI).2.1 (ℓ + 1) (by omega)
    calc _ ≤ _ := abs_add_le _ _
      _ ≤ _ := add_le_add h1 h2
      _ = _ := by ring
  · intro hF hG
    obtain ⟨e1, he1, hn1⟩ := p3_normalize S.uOut S.huOut Fd
    obtain ⟨e2, he2, hn2⟩ := p3_normalize S.vIn S.hvIn Gd
    have hsc := p5_gamma_scale cert γstar CSig Fp S hS hCSig
      (opNorm (S.uOut * Matrix.diagonal Fd * S.uOutᵀ))
      (opNorm (S.vIn * Matrix.diagonal Gd * S.vInᵀ)) e1 e2 ϱ ϱ hϱ1 hϱ1
    rw [← he1, ← he2] at hsc
    rw [hsc]
    have ha : 0 ≤ opNorm (S.uOut * Matrix.diagonal Fd * S.uOutᵀ) := tx_opNorm_nonneg _
    have hb : 0 ≤ opNorm (S.vIn * Matrix.diagonal Gd * S.vInᵀ) := tx_opNorm_nonneg _
    rcases ha.eq_or_lt with ha0 | ha0
    · rw [← ha0]; simp
    rcases hb.eq_or_lt with hb0 | hb0
    · rw [← hb0]; simp
    have hFd0 : ∀ i, 0 ≤ Fd i := by
      refine p5_diag_nonneg S.uOut S.huOut Fd ?_
      rw [← hFd]; exact hF
    have hGd0 : ∀ j, 0 ≤ Gd j := by
      refine p5_diag_nonneg S.vIn S.hvIn Gd ?_
      rw [← hGd]; exact hG
    have he10 : ∀ i, 0 ≤ e1 i := by
      intro i
      have := congrFun he1 i
      simp only [Pi.smul_apply, smul_eq_mul] at this
      have h0 := hFd0 i
      rw [this] at h0
      exact nonneg_of_mul_nonneg_right h0 ha0
    have he20 : ∀ j, 0 ≤ e2 j := by
      intro j
      have := congrFun he2 j
      simp only [Pi.smul_apply, smul_eq_mul] at this
      have h0 := hGd0 j
      rw [this] at h0
      exact nonneg_of_mul_nonneg_right h0 hb0
    exact mul_nonneg (mul_nonneg ha hb)
      (p5_gamma_nonneg_unit cert γstar CSig Fp S hS hCSig ϱlo ϱhi hϱ e1 e2 he10 he20 hn1 hn2 ϱ hϱI)

private lemma p6_tail (g : ℕ → ℝ) (c β : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (hg : ∀ ℓ : ℕ, 1 ≤ ℓ → |g ℓ| ≤ c * β ^ ℓ) (L : ℕ) (hL : 1 ≤ L) :
    Summable g ∧ |∑' ℓ, g ℓ - ∑ ℓ ∈ Finset.range L, g ℓ| ≤ c * β ^ L / (1 - β) := by
  have hgeo : Summable fun n : ℕ => c * β ^ n :=
    (summable_geometric_of_lt_one hβ0 hβ1).mul_left c
  have hsh : Summable fun n : ℕ => g (n + 1) :=
    Summable.of_norm_bounded ((summable_nat_add_iff 1).2 hgeo)
      (fun i => by rw [Real.norm_eq_abs]; exact hg (i + 1) (by omega))
  have hsumg : Summable g := (summable_nat_add_iff 1).1 hsh
  have hgeo' : Summable fun i : ℕ => c * β ^ L * β ^ i :=
    (summable_geometric_of_lt_one hβ0 hβ1).mul_left (c * β ^ L)
  have hbd : ∀ i : ℕ, ‖g (i + L)‖ ≤ c * β ^ L * β ^ i := by
    intro i
    rw [Real.norm_eq_abs, show c * β ^ L * β ^ i = c * β ^ (i + L) by ring]
    exact hg (i + L) (by omega)
  have habs : Summable fun i : ℕ => ‖g (i + L)‖ :=
    Summable.of_nonneg_of_le (fun i => norm_nonneg _) hbd hgeo'
  have htail : ‖∑' i : ℕ, g (i + L)‖ ≤ c * β ^ L * (1 - β)⁻¹ := by
    calc
      ‖∑' i : ℕ, g (i + L)‖ ≤ ∑' i : ℕ, ‖g (i + L)‖ := norm_tsum_le_tsum_norm habs
      _ ≤ ∑' i : ℕ, c * β ^ L * β ^ i := Summable.tsum_le_tsum hbd habs hgeo'
      _ = c * β ^ L * (1 - β)⁻¹ := by rw [tsum_mul_left, tsum_geometric_of_lt_one hβ0 hβ1]
  have hEq : ∑' ℓ, g ℓ - ∑ ℓ ∈ Finset.range L, g ℓ = ∑' i : ℕ, g (i + L) := by
    have := hsumg.sum_add_tsum_nat_add L
    linarith
  refine ⟨hsumg, ?_⟩
  rw [hEq, ← Real.norm_eq_abs, div_eq_mul_inv]
  exact htail

private lemma p6_lagsum_dep {ι : ℕ → Type*} (PP : ∀ k, Set (ι k))
    (a b : ∀ k, ℕ → ι k → ℝ) (K β : ℝ) (hβ : 0 ≤ β ∧ β < 1)
    (hbd : ∀ k, ∀ p ∈ PP k, ∀ ℓ : ℕ, 1 ≤ ℓ → |a k ℓ p| + |b k ℓ p| ≤ K * β ^ ℓ)
    (hlim : ∀ ℓ : ℕ, ∀ ε > 0, ∀ᶠ k in atTop, ∀ p ∈ PP k,
      |a k ℓ p - b k ℓ p| ≤ ε) :
    ∀ ε > 0, ∀ᶠ k in atTop, ∀ p ∈ PP k,
      |(a k 0 p + ∑' ℓ : ℕ, a k (ℓ + 1) p) -
        (b k 0 p + ∑' ℓ : ℕ, b k (ℓ + 1) p)| ≤ ε := by
  intro ε hε
  obtain ⟨hβ0, hβ1⟩ := hβ
  have hpow : Tendsto (fun L : ℕ => |K| * β ^ L / (1 - β)) atTop (𝓝 0) := by
    simpa using (((tendsto_pow_atTop_nhds_zero_of_lt_one hβ0 hβ1).const_mul |K|).div_const (1 - β))
  obtain ⟨L, hLε, hL1⟩ := ((hpow.eventually (gt_mem_nhds (by positivity : (0 : ℝ) < ε / 3))).and
    (eventually_ge_atTop 1)).exists
  let δ : ℝ := ε / (3 * ((L : ℝ) + 1))
  have hδpos : 0 < δ := by dsimp [δ]; positivity
  have hLδ : ((L : ℝ) + 1) * δ = ε / 3 := by dsimp [δ]; field_simp
  have hhead_ev : ∀ᶠ k in atTop, ∀ ℓ ∈ Finset.range L, ∀ p ∈ PP k,
      |a k ℓ p - b k ℓ p| ≤ δ :=
    (Filter.eventually_all_finset (Finset.range L)).2 (fun ℓ _ => hlim ℓ δ hδpos)
  filter_upwards [hhead_ev] with k hk
  intro p hp
  have hgb : ∀ ℓ : ℕ, 1 ≤ ℓ → |a k ℓ p - b k ℓ p| ≤ |K| * β ^ ℓ := fun ℓ hℓ =>
    (abs_sub _ _).trans ((hbd k p hp ℓ hℓ).trans
      (mul_le_mul_of_nonneg_right (le_abs_self K) (pow_nonneg hβ0 ℓ)))
  obtain ⟨hsd, htail⟩ := p6_tail (fun ℓ => a k ℓ p - b k ℓ p) |K| β hβ0 hβ1 hgb L hL1
  have hhead : |∑ ℓ ∈ Finset.range L, (a k ℓ p - b k ℓ p)| ≤ ε / 3 := by
    calc
      |∑ ℓ ∈ Finset.range L, (a k ℓ p - b k ℓ p)|
          ≤ ∑ ℓ ∈ Finset.range L, |a k ℓ p - b k ℓ p| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ ℓ ∈ Finset.range L, δ := Finset.sum_le_sum (fun ℓ hℓ => hk ℓ hℓ p hp)
      _ = (L : ℝ) * δ := by simp
      _ ≤ ε / 3 := by nlinarith
  have hdiff : |∑' ℓ : ℕ, (a k ℓ p - b k ℓ p)| ≤ ε := by
    have hsplit : ∑' ℓ, (a k ℓ p - b k ℓ p) =
        ∑ ℓ ∈ Finset.range L, (a k ℓ p - b k ℓ p) +
          (∑' ℓ, (a k ℓ p - b k ℓ p) - ∑ ℓ ∈ Finset.range L, (a k ℓ p - b k ℓ p)) := by ring
    rw [hsplit]
    calc
      _ ≤ _ := abs_add_le _ _
      _ ≤ ε / 3 + ε / 3 := add_le_add hhead (htail.trans hLε.le)
      _ ≤ ε := by linarith
  have hsa : Summable (fun ℓ => a k ℓ p) := by
    apply (summable_nat_add_iff 1).1
    refine Summable.of_norm_bounded
      ((summable_nat_add_iff 1).2 ((summable_geometric_of_lt_one hβ0 hβ1).mul_left K)) ?_
    intro ℓ
    rw [Real.norm_eq_abs]
    exact (le_add_of_nonneg_right (abs_nonneg _)).trans (hbd k p hp (ℓ + 1) (by omega))
  have hsb : Summable (fun ℓ => b k ℓ p) := by
    apply (summable_nat_add_iff 1).1
    refine Summable.of_norm_bounded
      ((summable_nat_add_iff 1).2 ((summable_geometric_of_lt_one hβ0 hβ1).mul_left K)) ?_
    intro ℓ
    rw [Real.norm_eq_abs]
    exact (le_add_of_nonneg_left (abs_nonneg _)).trans (hbd k p hp (ℓ + 1) (by omega))
  have haeq : ∑' ℓ : ℕ, a k ℓ p = a k 0 p + ∑' ℓ : ℕ, a k (ℓ + 1) p := by
    simpa using (hsa.sum_add_tsum_nat_add 1).symm
  have hbeq : ∑' ℓ : ℕ, b k ℓ p = b k 0 p + ∑' ℓ : ℕ, b k (ℓ + 1) p := by
    simpa using (hsb.sum_add_tsum_nat_add 1).symm
  rw [hsa.tsum_sub hsb, haeq, hbeq] at hdiff
  exact hdiff

private lemma p6_def_lag_scale {m n B : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} (F : FrozenParams m n B) (S : FrozenSamples P m n B)
    (ℓ : ℕ) (t : ℤ) (Fo : Mat m m) (Gi : Mat n n) (c d ϱ ϱ' : ℝ) :
    def_app_vol_lag F S ℓ t (c • Fo) (d • Gi) ϱ ϱ' =
      c * d * def_app_vol_lag F S ℓ t Fo Gi ϱ ϱ' := by
  unfold def_app_vol_lag
  simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul]
  rw [integral_const_mul, integral_const_mul]
  ring

private lemma p6_integrated_scale {m n B : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} (F : FrozenParams m n B) (S : FrozenSamples P m n B)
    (t : ℤ) (Fo : Mat m m) (Gi : Mat n n) (c d ϱ ϱ' : ℝ) :
    integratedLag F S t (c • Fo) (d • Gi) ϱ ϱ' =
      c * d * integratedLag F S t Fo Gi ϱ ϱ' := by
  unfold integratedLag
  simp_rw [p6_def_lag_scale]
  rw [mul_add, ← tsum_mul_left]
  congr 1
  exact tsum_congr fun ℓ => by ring

open scoped Matrix.Norms.L2Operator in
private lemma p6_opNorm_smul {p q : ℕ} (c : ℝ) (K : Mat p q) :
    opNorm (c • K) = |c| * opNorm K := by
  rw [opNorm_eq_norm, opNorm_eq_norm, norm_smul, Real.norm_eq_abs]

private lemma p6_diag_smul {d : ℕ} (c : ℝ) (U : Mat d d) (μ : Fin d → ℝ) :
    c • (U * Matrix.diagonal μ * Uᵀ) =
      U * Matrix.diagonal (fun i => c * μ i) * Uᵀ := by
  have hd : Matrix.diagonal (fun i => c * μ i) = c • Matrix.diagonal μ := by
    ext i j
    by_cases h : i = j
    · subst j; simp
    · simp [Matrix.diagonal_apply_ne _ h]
  rw [hd]
  simp only [Matrix.mul_smul, Matrix.smul_mul]

/-- `thm:app-vol-integrated`, snapshot `cr-2026-10-23`. Declaration of record. LaTeX, verbatim from `section.tex` (the whole environment):

```latex
\begin{theorem}[Integrated identification]\label{thm:app-vol-integrated}
Fix a finite dimension, diagonal $F,G$, and $\ridge,\ridge'\in I$.
\begin{enumerate}[label=(\roman*)]
\item For every $\ell\ge0$ and $T\ge1$,
\begin{equation}\label{eqn:app-vol-integrated-square}
\Big|\overline C_\ell[F,G](\ridge,\ridge')-\frac4{\pi^2}\int_0^T\!\!\int_0^T\mathfrak k_\ell[F,G](\ridge+x^2,\ridge'+y^2)\,dx\,dy\Big|\le\frac{4C_\Sigma\gamma_\star^{3/2}\norm F\norm G}{\pi T},
\end{equation}
so $\overline C_\ell[F,G]$ is the square-truncated double integral of the lag
kernel along the negative axis, with an error uniform in the dimension, the
lag and the ridges.
\item $\abs{\overline C_0[F,G]}\le\gamma_\star\norm F\norm G$ and
$\abs{\overline C_\ell[F,G]}\le\mathsf K_\star\norm F\norm G\,\bmom^\ell$ for $\ell\ge1$; at
$\bmom=0$, $\overline C_\ell[F,G]=0$ for every $\ell\ge1$.
\item The deterministic integrated coefficient
\begin{equation}\label{eqn:app-vol-Gammabar}
\overline\Gamma[F,G](\ridge,\ridge')\defeq\overline C_0[F,G](\ridge,\ridge')+\sum_{\ell\ge1}\Big(\overline C_\ell[F,G](\ridge,\ridge')+\overline C_\ell[F,G](\ridge',\ridge)\Big)
\end{equation}
converges absolutely, and $\overline\Gamma[F,G](\ridge,\ridge)\ge0$ whenever $F$ and
$G$ are positive semidefinite.
\item Under \cref{assum:app-setup-regime},
$\sup_{\ridge,\ridge'\in I}\sup_{F,G}\abs{\Gamma[F,G](\ridge,\ridge')-\overline\Gamma[F,G](\ridge,\ridge')}\to0$,
the supremum over diagonal $F,G$ of norm at most one, and the finite-time
contraction \cref{eqn:app-vol-finite-time} differs from $\overline\Gamma[F,G]$ by
$o(1)$ plus \cref{eqn:app-vol-finite-time-error}, along every joint sequence
of dimensions and block lengths $T$.
\item For the covariance-weighted coefficient
$\overline\Gamma\defeq\overline\Gamma[\Sigmaout,\Sigmain]$, $\sup_{I^2}\abs{\Gamma-\overline\Gamma}\to0$
under \cref{assum:app-setup-regime}. When $\Sigmain=\Id$,
$\overline C_0(\ridge,\ridge)=\overline Z(\ridge)$ of \cref{eqn:app-vol-half-candidates}.
\end{enumerate}
\end{theorem}
```
-/
theorem thm_app_vol_integrated_iv (cert : Muon.External.GaussianOpNorm)
    (R : SetupRegime) (Ω : ℕ → Type) [∀ k, MeasurableSpace (Ω k)]
    (P : ∀ k, Measure (Ω k)) [∀ k, IsProbabilityMeasure (P k)]
    (S : ∀ k, FrozenSamples (P k) (R.m k) (R.n k) (R.B k))
    (Sp : ∀ k : ℕ, SpectralData (R.F k).C) :
    -- (a) the integrated coefficient, uniformly on I^2 and in the tests
    (∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, ∀ t : ℤ, ∀ ϱ ∈ Set.Icc R.ϱlo R.ϱhi,
      ∀ ϱ' ∈ Set.Icc R.ϱlo R.ϱhi,
      ∀ (Fd : Fin (R.m k) → ℝ) (Gd : Fin (R.n k) → ℝ)
      (Fm : Mat (R.m k) (R.m k)) (Gm : Mat (R.n k) (R.n k)),
      Fm = (Sp k).uOut * Matrix.diagonal Fd * (Sp k).uOutᵀ →
      Gm = (Sp k).vIn * Matrix.diagonal Gd * (Sp k).vInᵀ →
      opNorm Fm ≤ 1 → opNorm Gm ≤ 1 →
      |integratedLag (R.F k) (S k) t Fm Gm ϱ ϱ' -
        lagGammaBar cert R.γstar R.CSig (R.F k).β (R.B k) (Sp k).μ (Sp k).lam Fd Gd ϱ ϱ'| ≤ ε) ∧
    -- (b) finite-time contraction: o(1) plus the explicit error, along every block length T
    (∀ T : ℕ → ℕ, (∀ k : ℕ, 1 ≤ T k) → ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop,
      ∀ ϱ ∈ Set.Icc R.ϱlo R.ϱhi, ∀ ϱ' ∈ Set.Icc R.ϱlo R.ϱhi,
      ∀ (Fd : Fin (R.m k) → ℝ) (Gd : Fin (R.n k) → ℝ)
      (Fm : Mat (R.m k) (R.m k)) (Gm : Mat (R.n k) (R.n k)),
      Fm = (Sp k).uOut * Matrix.diagonal Fd * (Sp k).uOutᵀ →
      Gm = (Sp k).vIn * Matrix.diagonal Gd * (Sp k).vInᵀ →
      opNorm Fm ≤ 1 → opNorm Gm ≤ 1 →
      |finiteTimeCov (R.F k) (S k) (T k) ϱ ϱ' Fm Gm -
        lagGammaBar cert R.γstar R.CSig (R.F k).β (R.B k) (Sp k).μ (Sp k).lam Fd Gd ϱ ϱ'| ≤
        ε + 2 * Muon.Dynamics.kStar R.CSig R.γstar R.ϱlo *
          ((R.F k).β ^ (T k) / (1 - (R.F k).β) +
            (R.F k).β / ((T k : ℝ) * (1 - (R.F k).β) ^ 2))) := by
  let X : ℕ → Type := fun k =>
    ℤ × ℝ × ℝ × (Fin (R.m k) → ℝ) × (Fin (R.n k) → ℝ) ×
      Mat (R.m k) (R.m k) × Mat (R.n k) (R.n k)
  have hRβ : 0 ≤ R.β ∧ R.β < 1 := by
    rw [← R.hβ 0]
    exact (R.F 0).hβ
  let PP : ∀ k, Set (X k) := fun k p => match p with
    | (t, ϱ, ϱ', Fd, Gd, Fm, Gm) =>
      ϱ ∈ Set.Icc R.ϱlo R.ϱhi ∧ ϱ' ∈ Set.Icc R.ϱlo R.ϱhi ∧
      Fm = (Sp k).uOut * Matrix.diagonal Fd * (Sp k).uOutᵀ ∧
      Gm = (Sp k).vIn * Matrix.diagonal Gd * (Sp k).vInᵀ ∧
      opNorm Fm ≤ 1 ∧ opNorm Gm ≤ 1
  let a : ∀ k, ℕ → X k → ℝ := fun k ℓ p => match p, ℓ with
    | (t, ϱ, ϱ', _, _, Fm, Gm), 0 =>
        def_app_vol_lag (R.F k) (S k) 0 t Fm Gm ϱ ϱ'
    | (t, ϱ, ϱ', _, _, Fm, Gm), ℓ + 1 =>
        def_app_vol_lag (R.F k) (S k) (ℓ + 1) t Fm Gm ϱ ϱ' +
          def_app_vol_lag (R.F k) (S k) (ℓ + 1) t Fm Gm ϱ' ϱ
  let b : ∀ k, ℕ → X k → ℝ := fun k ℓ p => match p, ℓ with
    | (_, ϱ, ϱ', Fd, Gd, _, _), 0 =>
        lagResp cert R.γstar R.CSig (R.F k).β 0 (R.B k) (Sp k).μ (Sp k).lam Fd Gd
          (omegaF ϱ) (omegaF ϱ')
    | (_, ϱ, ϱ', Fd, Gd, _, _), ℓ + 1 =>
        lagResp cert R.γstar R.CSig (R.F k).β (ℓ + 1) (R.B k) (Sp k).μ (Sp k).lam Fd Gd
            (omegaF ϱ) (omegaF ϱ') +
          lagResp cert R.γstar R.CSig (R.F k).β (ℓ + 1) (R.B k) (Sp k).μ (Sp k).lam Fd Gd
            (omegaF ϱ') (omegaF ϱ)
  have hbd : ∀ k, ∀ p ∈ PP k, ∀ ℓ : ℕ, 1 ≤ ℓ →
      |a k ℓ p| + |b k ℓ p| ≤
        (4 * Muon.Dynamics.kStar R.CSig R.γstar R.ϱlo) * R.β ^ ℓ := by
    intro k p hp ℓ hℓ
    rcases p with ⟨t, ϱ, ϱ', Fd, Gd, Fm, Gm⟩
    dsimp [PP] at hp
    obtain ⟨hϱI, hϱ'I, hFm, hGm, hF, hG⟩ := hp
    obtain ⟨j, rfl⟩ : ∃ j, j + 1 = ℓ := ⟨ℓ - 1, by omega⟩
    have hsz : SizeFin (R.F k).C (R.B k) R.γstar R.CSig :=
      ⟨R.dims k, R.normOut k, R.normIn k⟩
    have hFs : Fmᵀ = Fm := by rw [hFm]; exact p4_diag_symm _ _
    have hGs : Gmᵀ = Gm := by rw [hGm]; exact p4_diag_symm _ _
    have ha1 := (thm_app_vol_lag_reduction_ii_actual (R.F k) (S k) R.γstar R.CSig
      R.ϱlo R.ϱhi hsz R.hC R.hϱ Fm Gm hFs hGs hF hG ϱ ϱ' hϱI hϱ'I t).2
      (j + 1) (by omega)
    have ha2 := (thm_app_vol_lag_reduction_ii_actual (R.F k) (S k) R.γstar R.CSig
      R.ϱlo R.ϱhi hsz R.hC R.hϱ Fm Gm hFs hGs hF hG ϱ' ϱ hϱ'I hϱI t).2
      (j + 1) (by omega)
    have hb1 := (thm_app_vol_integrated_ii cert R.γstar R.CSig (R.F k) (Sp k) hsz R.hC
      R.ϱlo R.ϱhi R.hϱ Fm Gm Fd Gd hFm hGm ϱ ϱ' hϱI hϱ'I).2.1 (j + 1) (by omega)
    have hb2 := (thm_app_vol_integrated_ii cert R.γstar R.CSig (R.F k) (Sp k) hsz R.hC
      R.ϱlo R.ϱhi R.hϱ Fm Gm Fd Gd hFm hGm ϱ' ϱ hϱ'I hϱI).2.1 (j + 1) (by omega)
    rw [R.hβ k] at ha1 ha2 hb1 hb2
    dsimp [a, b]
    rw [R.hβ k]
    have hK : 0 ≤ Muon.Dynamics.kStar R.CSig R.γstar R.ϱlo := by
      unfold Muon.Dynamics.kStar
      exact mul_nonneg (by linarith [R.hC]) (Real.sqrt_nonneg _)
    have hpow : 0 ≤ R.β ^ (j + 1) := pow_nonneg hRβ.1 _
    have hFG : opNorm Fm * opNorm Gm ≤ 1 :=
      mul_le_one₀ hF (tx_opNorm_nonneg _) hG
    have hKP : 0 ≤ Muon.Dynamics.kStar R.CSig R.γstar R.ϱlo * R.β ^ (j + 1) :=
      mul_nonneg hK hpow
    have hb1' : |lagResp cert R.γstar R.CSig R.β (j + 1) (R.B k) (Sp k).μ (Sp k).lam Fd Gd
        (omegaF ϱ) (omegaF ϱ')| ≤ Muon.Dynamics.kStar R.CSig R.γstar R.ϱlo * R.β ^ (j + 1) :=
      hb1.trans (by
        rw [show Muon.Dynamics.kStar R.CSig R.γstar R.ϱlo * opNorm Fm * opNorm Gm * R.β ^ (j + 1) =
          (Muon.Dynamics.kStar R.CSig R.γstar R.ϱlo * R.β ^ (j + 1)) *
            (opNorm Fm * opNorm Gm) by ring]
        exact mul_le_of_le_one_right hKP hFG)
    have hb2' : |lagResp cert R.γstar R.CSig R.β (j + 1) (R.B k) (Sp k).μ (Sp k).lam Fd Gd
        (omegaF ϱ') (omegaF ϱ)| ≤ Muon.Dynamics.kStar R.CSig R.γstar R.ϱlo * R.β ^ (j + 1) :=
      hb2.trans (by
        rw [show Muon.Dynamics.kStar R.CSig R.γstar R.ϱlo * opNorm Fm * opNorm Gm * R.β ^ (j + 1) =
          (Muon.Dynamics.kStar R.CSig R.γstar R.ϱlo * R.β ^ (j + 1)) *
            (opNorm Fm * opNorm Gm) by ring]
        exact mul_le_of_le_one_right hKP hFG)
    calc
      _ ≤ (|def_app_vol_lag (R.F k) (S k) (j + 1) t Fm Gm ϱ ϱ'| +
          |def_app_vol_lag (R.F k) (S k) (j + 1) t Fm Gm ϱ' ϱ|) +
        (|lagResp cert R.γstar R.CSig R.β (j + 1) (R.B k) (Sp k).μ (Sp k).lam Fd Gd
            (omegaF ϱ) (omegaF ϱ')| +
          |lagResp cert R.γstar R.CSig R.β (j + 1) (R.B k) (Sp k).μ (Sp k).lam Fd Gd
            (omegaF ϱ') (omegaF ϱ)|) := add_le_add (abs_add_le _ _) (abs_add_le _ _)
      _ ≤ _ := by linarith
  have hcl := fun ℓ : ℕ => (thm_app_vol_lag_kernel_closure_actual cert R Ω P S Sp ℓ
    (Set.Icc R.ϱlo R.ϱhi) isCompact_Icc
    (fun x hx => R.hϱ.1.trans_le hx.1)).2
  have hlim : ∀ ℓ : ℕ, ∀ ε > 0, ∀ᶠ k in atTop, ∀ p ∈ PP k,
      |a k ℓ p - b k ℓ p| ≤ ε := by
    intro ℓ ε hε
    cases ℓ with
    | zero =>
        filter_upwards [hcl 0 ε hε] with k hk
        rintro ⟨t, ϱ, ϱ', Fd, Gd, Fm, Gm⟩ hp
        dsimp [PP] at hp
        obtain ⟨hϱI, hϱ'I, hFm, hGm, hF, hG⟩ := hp
        simpa [a, b] using hk t ϱ hϱI ϱ' hϱ'I Fd Gd Fm Gm hFm hGm hF hG
    | succ ℓ =>
        filter_upwards [hcl (ℓ + 1) (ε / 2) (by positivity)] with k hk
        rintro ⟨t, ϱ, ϱ', Fd, Gd, Fm, Gm⟩ hp
        dsimp [PP] at hp
        obtain ⟨hϱI, hϱ'I, hFm, hGm, hF, hG⟩ := hp
        have h1 := hk t ϱ hϱI ϱ' hϱ'I Fd Gd Fm Gm hFm hGm hF hG
        have h2 := hk t ϱ' hϱ'I ϱ hϱI Fd Gd Fm Gm hFm hGm hF hG
        dsimp [a, b]
        rw [show
          (def_app_vol_lag (R.F k) (S k) (ℓ + 1) t Fm Gm ϱ ϱ' +
              def_app_vol_lag (R.F k) (S k) (ℓ + 1) t Fm Gm ϱ' ϱ) -
            (lagResp cert R.γstar R.CSig (R.F k).β (ℓ + 1) (R.B k) (Sp k).μ (Sp k).lam Fd Gd
                (omegaF ϱ) (omegaF ϱ') +
              lagResp cert R.γstar R.CSig (R.F k).β (ℓ + 1) (R.B k) (Sp k).μ (Sp k).lam Fd Gd
                (omegaF ϱ') (omegaF ϱ)) =
            (def_app_vol_lag (R.F k) (S k) (ℓ + 1) t Fm Gm ϱ ϱ' -
              lagResp cert R.γstar R.CSig (R.F k).β (ℓ + 1) (R.B k) (Sp k).μ (Sp k).lam Fd Gd
                (omegaF ϱ) (omegaF ϱ')) +
            (def_app_vol_lag (R.F k) (S k) (ℓ + 1) t Fm Gm ϱ' ϱ -
              lagResp cert R.γstar R.CSig (R.F k).β (ℓ + 1) (R.B k) (Sp k).μ (Sp k).lam Fd Gd
                (omegaF ϱ') (omegaF ϱ)) by ring]
        exact (abs_add_le _ _).trans (by linarith)
  have hsum := p6_lagsum_dep PP a b (4 * Muon.Dynamics.kStar R.CSig R.γstar R.ϱlo)
    R.β hRβ hbd hlim
  constructor
  · intro ε hε
    filter_upwards [hsum ε hε] with k hk
    intro t ϱ hϱI ϱ' hϱ'I Fd Gd Fm Gm hFm hGm hF hG
    have hp : (t, ϱ, ϱ', Fd, Gd, Fm, Gm) ∈ PP k := by
      exact ⟨hϱI, hϱ'I, hFm, hGm, hF, hG⟩
    simpa [a, b, integratedLag, lagGammaBar] using
      hk (t, ϱ, ϱ', Fd, Gd, Fm, Gm) hp
  · intro T hT ε hε
    filter_upwards [hsum ε hε] with k hk
    intro ϱ hϱI ϱ' hϱ'I Fd Gd Fm Gm hFm hGm hF hG
    have hp : ((0 : ℤ), ϱ, ϱ', Fd, Gd, Fm, Gm) ∈ PP k := by
      exact ⟨hϱI, hϱ'I, hFm, hGm, hF, hG⟩
    have hi := hk ((0 : ℤ), ϱ, ϱ', Fd, Gd, Fm, Gm) hp
    have hsz : SizeFin (R.F k).C (R.B k) R.γstar R.CSig :=
      ⟨R.dims k, R.normOut k, R.normIn k⟩
    have hred := thm_app_vol_lag_reduction_iii_bound (R.F k) (S k) R.γstar R.CSig
      R.ϱlo R.ϱhi hsz R.hC R.hϱ Fm Gm
      (by rw [hFm]; exact p4_diag_symm _ _) (by rw [hGm]; exact p4_diag_symm _ _)
      hF hG ϱ ϱ' hϱI hϱ'I (T k) (hT k) 0
    have htri := abs_sub_le (finiteTimeCov (R.F k) (S k) (T k) ϱ ϱ' Fm Gm)
      (integratedLag (R.F k) (S k) 0 Fm Gm ϱ ϱ')
      (lagGammaBar cert R.γstar R.CSig (R.F k).β (R.B k) (Sp k).μ (Sp k).lam Fd Gd ϱ ϱ')
    simpa [a, b, integratedLag, lagGammaBar, add_comm] using (htri.trans (add_le_add hred hi))

private lemma p6_weighted_convergence (cert : Muon.External.GaussianOpNorm)
    (R : SetupRegime) (Ω : ℕ → Type) [∀ k, MeasurableSpace (Ω k)]
    (P : ∀ k, Measure (Ω k)) [∀ k, IsProbabilityMeasure (P k)]
    (S : ∀ k, FrozenSamples (P k) (R.m k) (R.n k) (R.B k))
    (Sp : ∀ k : ℕ, SpectralData (R.F k).C) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, ∀ t : ℤ, ∀ ϱ ∈ Set.Icc R.ϱlo R.ϱhi,
      ∀ ϱ' ∈ Set.Icc R.ϱlo R.ϱhi,
      |weightedGamma (R.F k) (S k) t ϱ ϱ' -
        lagGammaBar cert R.γstar R.CSig (R.F k).β (R.B k) (Sp k).μ (Sp k).lam
          (Sp k).μ (Sp k).lam ϱ ϱ'| ≤ ε := by
  have hc : 0 < R.CSig := by linarith [R.hC]
  intro ε hε
  have hiv := (thm_app_vol_integrated_iv cert R Ω P S Sp).1 (ε / R.CSig ^ 2) (by positivity)
  filter_upwards [hiv] with k hk
  intro t ϱ hϱI ϱ' hϱ'I
  let Fo : Mat (R.m k) (R.m k) := R.CSig⁻¹ • (R.F k).C.Sout
  let Gi : Mat (R.n k) (R.n k) := R.CSig⁻¹ • (R.F k).C.Sin
  let Fd : Fin (R.m k) → ℝ := fun i => R.CSig⁻¹ * (Sp k).μ i
  let Gd : Fin (R.n k) → ℝ := fun j => R.CSig⁻¹ * (Sp k).lam j
  have hFo : Fo = (Sp k).uOut * Matrix.diagonal Fd * (Sp k).uOutᵀ := by
    dsimp [Fo, Fd]
    rw [Sout_eq_spectral (Sp k)]
    exact p6_diag_smul _ _ _
  have hGi : Gi = (Sp k).vIn * Matrix.diagonal Gd * (Sp k).vInᵀ := by
    dsimp [Gi, Gd]
    rw [Sin_eq_spectral (Sp k)]
    exact p6_diag_smul _ _ _
  have hFo1 : opNorm Fo ≤ 1 := by
    dsimp [Fo]
    rw [p6_opNorm_smul, abs_of_pos (inv_pos.mpr hc)]
    calc
      R.CSig⁻¹ * opNorm (R.F k).C.Sout ≤ R.CSig⁻¹ * R.CSig :=
        mul_le_mul_of_nonneg_left (R.normOut k) (inv_pos.mpr hc).le
      _ = 1 := inv_mul_cancel₀ hc.ne'
  have hGi1 : opNorm Gi ≤ 1 := by
    dsimp [Gi]
    rw [p6_opNorm_smul, abs_of_pos (inv_pos.mpr hc)]
    calc
      R.CSig⁻¹ * opNorm (R.F k).C.Sin ≤ R.CSig⁻¹ * R.CSig :=
        mul_le_mul_of_nonneg_left (R.normIn k) (inv_pos.mpr hc).le
      _ = 1 := inv_mul_cancel₀ hc.ne'
  have h := hk t ϱ hϱI ϱ' hϱ'I Fd Gd Fo Gi hFo hGi hFo1 hGi1
  have hϱ0 : 0 < ϱ := R.hϱ.1.trans_le hϱI.1
  have hϱ'0 : 0 < ϱ' := R.hϱ.1.trans_le hϱ'I.1
  have hsz : SizeFin (R.F k).C (R.B k) R.γstar R.CSig :=
    ⟨R.dims k, R.normOut k, R.normIn k⟩
  rw [show Fo = R.CSig⁻¹ • (R.F k).C.Sout by rfl,
    show Gi = R.CSig⁻¹ • (R.F k).C.Sin by rfl,
    p6_integrated_scale] at h
  have hg := p5_gamma_scale cert R.γstar R.CSig (R.F k) (Sp k) hsz R.hC
    R.CSig⁻¹ R.CSig⁻¹ (Sp k).μ (Sp k).lam ϱ ϱ' hϱ0 hϱ'0
  change lagGammaBar cert R.γstar R.CSig (R.F k).β (R.B k) (Sp k).μ (Sp k).lam
      Fd Gd ϱ ϱ' = _ at hg
  rw [hg] at h
  have heq : R.CSig⁻¹ * R.CSig⁻¹ *
        integratedLag (R.F k) (S k) t (R.F k).C.Sout (R.F k).C.Sin ϱ ϱ' -
      R.CSig⁻¹ * R.CSig⁻¹ *
        lagGammaBar cert R.γstar R.CSig (R.F k).β (R.B k) (Sp k).μ (Sp k).lam
          (Sp k).μ (Sp k).lam ϱ ϱ' =
      (R.CSig⁻¹ * R.CSig⁻¹) *
        (integratedLag (R.F k) (S k) t (R.F k).C.Sout (R.F k).C.Sin ϱ ϱ' -
          lagGammaBar cert R.γstar R.CSig (R.F k).β (R.B k) (Sp k).μ (Sp k).lam
            (Sp k).μ (Sp k).lam ϱ ϱ') := by ring
  rw [heq, abs_mul, abs_of_pos (mul_pos (inv_pos.mpr hc) (inv_pos.mpr hc))] at h
  have ht := mul_le_mul_of_nonneg_left h (sq_nonneg R.CSig)
  unfold weightedGamma
  field_simp at ht
  exact ht

private lemma p6_repl_sum {m N : ℕ} (f : Fin m → ℝ) :
    ∑ x : Fin (N * m), f ((replIdx m N).symm x).1 = (N : ℝ) * ∑ i, f i := by
  have h := Equiv.sum_comp (replIdx m N).symm (fun y : Fin m × Fin N => f y.1)
  rw [h, Fintype.sum_prod_type]
  simp [Finset.mul_sum]

private lemma p6_zbar_repl {m B N : ℕ} (hN : 0 < N) (hB : 0 < B) (β : ℝ)
    (nu nu' nuN nuN' : FiniteMeasure ℝ) (mu : Fin m → ℝ) (ϱ : ℝ)
    (hnu : (nuN : Measure ℝ) = (nu : Measure ℝ))
    (hnu' : (nuN' : Measure ℝ) = (nu' : Measure ℝ)) :
    zbarRaw β (N * B) nuN nuN' (replVec N mu) ϱ = zbarRaw β B nu nu' mu ϱ := by
  have hbr := def_app_vol_replication_iii (Fw (emaW β)) nu nu' nuN nuN' ϱ hnu hnu'
  unfold zbarRaw volraw replVec
  rw [hbr, p6_repl_sum (N := N) (f := fun i => mu i *
    ((branchSol (Fw (emaW β)) nu nu' ϱ).2.2.1 * mu i /
      (ϱ + (branchSol (Fw (emaW β)) nu nu' ϱ).2.2.1 * mu i)))]
  have hNr : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  have hBr : (B : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hB.ne'
  have hscale : (((N * B : ℕ) : ℝ))⁻¹ * (N : ℝ) = (B : ℝ)⁻¹ := by
    rw [Nat.cast_mul]
    field_simp
  rw [← mul_assoc, hscale]

private lemma p6_raw_scale {m n B : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (Fo : Mat m m) (Gi : Mat n n) (X Y : Ω → Mat m n) (c d : ℝ) :
    (B : ℝ)⁻¹ * (∫ ω, Matrix.trace ((c • Fo) * X ω * (d • Gi) * (Y ω)ᵀ) ∂P) =
      c * d * ((B : ℝ)⁻¹ * (∫ ω, Matrix.trace (Fo * X ω * Gi * (Y ω)ᵀ) ∂P)) := by
  simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul]
  rw [integral_const_mul, integral_const_mul]
  ring

private lemma p6_zero_lag_zbar (cert : Muon.External.GaussianOpNorm) (γstar CSig : ℝ)
    {m n B : ℕ} (Fp : FrozenParams m n B) (S : SpectralData Fp.C)
    (hS : SizeFin Fp.C B γstar CSig) (hCSig : 1 ≤ CSig) (hId : Fp.C.Sin = 1)
    (nu nu' : FiniteMeasure ℝ)
    (hnu : (nu : Measure ℝ) = Muon.nuOut Fp.C B)
    (hnu' : (nu' : Measure ℝ) = Muon.nuIn Fp.C B) (ϱ : ℝ) (hϱ : 0 < ϱ) :
    lagResp cert γstar CSig Fp.β 0 B S.μ S.lam S.μ S.lam (omegaF ϱ) (omegaF ϱ) =
      zbarRaw Fp.β B nu nu' S.μ ϱ := by
  obtain ⟨hm, hn⟩ := tx_pos_of_fro Fp.A Fp.hA
  obtain ⟨R, hmR, hnR, hBR, hγR, hCR, hβR, hloR, hhiR, hrep⟩ :=
    def_app_vol_replication_regime Fp S γstar CSig ϱ ϱ hCSig hS hm hn ⟨hϱ, le_rfl⟩
  rcases R with ⟨rm, rn, rB, rF, rprop, rγ, rC, rhC, rdims, rnormO, rnormI,
    rβ, rhβ, rlo, rhi, rhϱ, rdiff⟩
  dsimp only at hmR hnR hBR hγR hCR hβR hloR hhiR hrep
  subst rm rn rB rγ rC rβ rlo rhi
  let R : SetupRegime := ⟨_, _, _, rF, rprop, γstar, CSig, rhC, rdims, rnormO, rnormI,
    Fp.β, rhβ, ϱ, ϱ, rhϱ, rdiff⟩
  have hCov : ∀ q, (rF q).C = replCov Fp.C (q + 1) := fun q => eq_of_heq (hrep q).1
  have hspec : ∀ q, ∃ Sq : SpectralData (rF q).C,
      Sq.μ = replVec (q + 1) S.μ ∧ Sq.lam = replVec (q + 1) S.lam ∧
      Sq.uOut = replMat S.uOut (q + 1) ∧ Sq.vIn = replMat S.vIn (q + 1) := by
    intro q
    rw [hCov q]
    obtain ⟨Sq, h1, h2, h3, h4⟩ := tx_exists_replSpec Fp.C S (q + 1)
    exact ⟨Sq, h3, h4, h1, h2⟩
  choose Sq hmu hlam hU hV using hspec
  let Ω : ℕ → Type := fun q => (ℤ × Fin (R.B q)) → Vec (R.m q) × Vec (R.n q)
  let P : ∀ q, Measure (Ω q) := fun q => Measure.infinitePi fun _ : ℤ × Fin (R.B q) =>
    (Muon.Foundations.stdGaussianPi (R.m q)).prod (Muon.Foundations.stdGaussianPi (R.n q))
  let samples : ∀ q, FrozenSamples (P q) (R.m q) (R.n q) (R.B q) := fun q =>
    (frozenSamples_nonempty (R.m q) (R.n q) (R.B q)).some
  have hSize : ∀ q, SizeFin (rF q).C ((q + 1) * B) γstar CSig :=
    fun q => ⟨rdims q, rnormO q, rnormI q⟩
  have hIn : ∀ q, (rF q).C.Sin = 1 := by
    intro q
    rw [hCov q]
    change replMat Fp.C.Sin (q + 1) = 1
    rw [hId, tx_replMat_one]
  have hnuO : ∀ q, ((Muon.Drift.specOutFM (rF q)) : Measure ℝ) = (nu : Measure ℝ) := by
    intro q
    change Muon.nuOut (rF q).C ((q + 1) * B) = (nu : Measure ℝ)
    rw [hCov q, def_app_vol_replication_i Fp.C Fp.hB (q + 1) (Nat.succ_pos q)]
    exact hnu.symm
  have hnuI : ∀ q, ((Muon.Drift.specInFM (rF q)) : Measure ℝ) = (nu' : Measure ℝ) := by
    intro q
    change Muon.nuIn (rF q).C ((q + 1) * B) = (nu' : Measure ℝ)
    rw [hCov q, def_app_vol_replication_ii Fp.C Fp.hB (q + 1) (Nat.succ_pos q)]
    exact hnu'.symm
  have hzbar : ∀ q,
      zbarRaw (rF q).β ((q + 1) * B) (Muon.Drift.specOutFM (rF q))
          (Muon.Drift.specInFM (rF q)) (Sq q).μ ϱ = zbarRaw Fp.β B nu nu' S.μ ϱ := by
    intro q
    rw [rhβ q, hmu q]
    exact p6_zbar_repl (Nat.succ_pos q) Fp.hB Fp.β nu nu'
      (Muon.Drift.specOutFM (rF q)) (Muon.Drift.specInFM (rF q)) S.μ ϱ
      (hnuO q) (hnuI q)
  have hc : 0 < CSig⁻¹ := inv_pos.mpr (lt_of_lt_of_le zero_lt_one hCSig)
  let c : ℝ := CSig⁻¹
  let Fo : ∀ q, Mat (R.m q) (R.m q) := fun q => c • (rF q).C.Sout
  let Gi : ∀ q, Mat (R.n q) (R.n q) := fun q => c • (rF q).C.Sin
  let Fd : ∀ q, Fin (R.m q) → ℝ := fun q i => c * (Sq q).μ i
  let Gd : ∀ q, Fin (R.n q) → ℝ := fun q j => c * (Sq q).lam j
  have hFo : ∀ q, Fo q = (Sq q).uOut * Matrix.diagonal (Fd q) * (Sq q).uOutᵀ := by
    intro q
    dsimp [Fo, Fd]
    rw [Sout_eq_spectral (Sq q)]
    exact p6_diag_smul _ _ _
  have hGi : ∀ q, Gi q = (Sq q).vIn * Matrix.diagonal (Gd q) * (Sq q).vInᵀ := by
    intro q
    dsimp [Gi, Gd]
    rw [Sin_eq_spectral (Sq q)]
    exact p6_diag_smul _ _ _
  have hFo1 : ∀ q, opNorm (Fo q) ≤ 1 := by
    intro q
    dsimp [Fo, c]
    rw [p6_opNorm_smul, abs_of_pos hc]
    calc
      CSig⁻¹ * opNorm (rF q).C.Sout ≤ CSig⁻¹ * CSig :=
        mul_le_mul_of_nonneg_left (rnormO q) hc.le
      _ = 1 := inv_mul_cancel₀ (ne_of_gt (lt_of_lt_of_le zero_lt_one hCSig))
  have hGi1 : ∀ q, opNorm (Gi q) ≤ 1 := by
    intro q
    dsimp [Gi, c]
    rw [p6_opNorm_smul, abs_of_pos hc]
    calc
      CSig⁻¹ * opNorm (rF q).C.Sin ≤ CSig⁻¹ * CSig :=
        mul_le_mul_of_nonneg_left (rnormI q) hc.le
      _ = 1 := inv_mul_cancel₀ (ne_of_gt (lt_of_lt_of_le zero_lt_one hCSig))
  let L := lagResp cert γstar CSig Fp.β 0 B S.μ S.lam S.μ S.lam (omegaF ϱ) (omegaF ϱ)
  let Z := zbarRaw Fp.β B nu nu' S.μ ϱ
  let A : ℕ → ℝ := fun q => def_app_vol_lag (rF q) (samples q) 0 0 (Fo q) (Gi q) ϱ ϱ
  let M : ℕ → ℝ := fun q => ∫ ω, sameTimeZ (rF q) (samples q) ϱ 0 ω ∂(P q)
  have hω := (lem_app_vol_sharp_ii hϱ hϱ).2.1
  have hrepl := (thm_app_vol_lag_kernel_bilinear_bound_replication cert γstar CSig
    Fp S hS hCSig 0 (omegaF ϱ) (omegaF ϱ) hω hω).2.2.2.2.2
  have hlag : ∀ q, lagResp cert γstar CSig (rF q).β 0 ((q + 1) * B)
      (Sq q).μ (Sq q).lam (Fd q) (Gd q) (omegaF ϱ) (omegaF ϱ) = c * c * L := by
    intro q
    have hs := p3_lag_scale cert γstar CSig (rF q) (Sq q) (hSize q) hCSig 0 c c
      (Sq q).μ (Sq q).lam (omegaF ϱ) (omegaF ϱ) hω hω
    dsimp [Fd, Gd]
    change lagResp cert γstar CSig (rF q).β 0 ((q + 1) * B) (Sq q).μ (Sq q).lam
      (c • (Sq q).μ) (c • (Sq q).lam) (omegaF ϱ) (omegaF ϱ) = c * c * L
    rw [hs]
    apply congrArg (fun x : ℝ => c * c * x)
    dsimp [L]
    rw [rhβ q, hmu q, hlam q]
    exact hrepl (q + 1) (Nat.succ_pos q) S.μ S.lam
  have hclose := (thm_app_vol_lag_kernel_closure_actual cert R Ω P samples Sq 0 {1}
    isCompact_singleton (by intro x hx; rcases hx with rfl; norm_num)).2
  have hA : Tendsto A atTop (𝓝 (c * c * L)) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    have hev := hclose (ε / 2) (by positivity)
    rw [Filter.eventually_atTop] at hev
    obtain ⟨q₀, hq₀⟩ := hev
    refine ⟨q₀, fun q hq => ?_⟩
    rw [Real.dist_eq]
    have ht := hq₀ q hq 0 ϱ ⟨le_rfl, le_rfl⟩ ϱ ⟨le_rfl, le_rfl⟩ (Fd q) (Gd q)
      (Fo q) (Gi q) (hFo q) (hGi q) (hFo1 q) (hGi1 q)
    rw [hlag q] at ht
    exact ht.trans_lt (by linarith)
  let eD : ℕ → ℝ := fun q => Muon.Drift.epsB (emaW R.β) (R.F q) (samples q) 0
    (Muon.Drift.specOutFM (R.F q)) (Muon.Drift.specInFM (R.F q)) R.ϱlo R.ϱhi
  have hmD := Muon.Drift.thm_app_drift_mean R P samples 0
  have heD : Tendsto eD atTop (𝓝 0) := hmD.2.2.1
  have hmean : ∀ q, ∀ s : ℤ, ∀ u ∈ Set.Icc R.ϱlo R.ϱhi,
      fro (Muon.mean (P q) (frozenUpd (R.F q) (samples q) u s)) ≤
        R.CSig / Real.sqrt R.ϱlo + eD q := by
    intro q s u hu
    have hu' : u = ϱ := le_antisymm hu.2 hu.1
    subst u
    have he : fro (Muon.Drift.EQ (emaW R.β) (R.F q) (samples q) 0 ϱ -
        Muon.Drift.Gbar (emaW R.β) (R.F q) (Muon.Drift.specOutFM (R.F q))
          (Muon.Drift.specInFM (R.F q)) ϱ) ≤ eD q :=
      p4_le_biSup (hmD.2.1 q) ⟨le_rfl, le_rfl⟩
    have hg := (hmD.1 q ϱ ⟨le_rfl, le_rfl⟩).2
    have hadd := p4_fro_add
      (Muon.Drift.EQ (emaW R.β) (R.F q) (samples q) 0 ϱ -
        Muon.Drift.Gbar (emaW R.β) (R.F q) (Muon.Drift.specOutFM (R.F q))
          (Muon.Drift.specInFM (R.F q)) ϱ)
      (Muon.Drift.Gbar (emaW R.β) (R.F q) (Muon.Drift.specOutFM (R.F q))
          (Muon.Drift.specInFM (R.F q)) ϱ)
    rw [sub_add_cancel] at hadd
    have heq : Muon.Drift.EQ (emaW R.β) (R.F q) (samples q) 0 ϱ =
        Muon.mean (P q) (frozenUpd (R.F q) (samples q) ϱ 0) := by
      unfold Muon.Drift.EQ
      congr 1
      funext ω
      unfold frozenUpd WeightedBuf frozenBuf
      rw [R.hβ q]
    rw [heq] at hadd he
    have hzero : fro (Muon.mean (P q) (frozenUpd (R.F q) (samples q) ϱ 0)) ≤
        R.CSig / Real.sqrt R.ϱlo + eD q := by linarith
    have hshift := p4_mean_shift (R.F q) (samples q) R.hϱ.1.le 0 s
    rw [zero_add] at hshift
    rw [hshift]
    exact hzero
  let eG : ℕ → ℝ := fun q => ⨆ u ∈ ({ϱ} : Set ℝ),
    (opNorm (expRes (emaW R.β) (R.F q) (samples q) 0 u -
      Rbar (Fw (emaW R.β)) (Muon.Drift.specOutFM (R.F q))
        (Muon.Drift.specInFM (R.F q)) (R.F q).C u) +
    opNorm (expResT (emaW R.β) (R.F q) (samples q) 0 u -
      Rtbar (Fw (emaW R.β)) (Muon.Drift.specOutFM (R.F q))
        (Muon.Drift.specInFM (R.F q)) (R.F q).C u))
  have heG : Tendsto eG atTop (𝓝 0) := by
    have hg := thm_app_de_gram R (emaW R.β) (Muon.Drift.emaW_weightClass_regime R)
      P samples (fun q => Muon.Drift.specOutFM (R.F q))
      (fun q => Muon.Drift.specInFM (R.F q)) (fun _ => rfl) (fun _ => rfl) 0
      {ϱ} isCompact_singleton (by intro x hx; rcases hx with rfl; exact hϱ)
    exact hg
  have heGbd : ∀ q, ∀ u ∈ Set.Icc ϱ ϱ,
      opNorm (expRes (emaW (rF q).β) (rF q) (samples q) 0 u -
        Rbar (Fw (emaW (rF q).β)) (Muon.Drift.specOutFM (rF q))
          (Muon.Drift.specInFM (rF q)) (rF q).C u) ≤ eG q := by
    intro q u hu
    have hu' : u = ϱ := le_antisymm hu.2 hu.1
    subst u
    rw [rhβ q]
    have hsum :
        opNorm (expRes (emaW R.β) (R.F q) (samples q) 0 ϱ -
          Rbar (Fw (emaW R.β)) (Muon.Drift.specOutFM (R.F q))
            (Muon.Drift.specInFM (R.F q)) (R.F q).C ϱ) +
        opNorm (expResT (emaW R.β) (R.F q) (samples q) 0 ϱ -
          Rtbar (Fw (emaW R.β)) (Muon.Drift.specOutFM (R.F q))
            (Muon.Drift.specInFM (R.F q)) (R.F q).C ϱ) ≤ eG q := by
      dsimp [eG]
      let g : ℝ → ℝ := fun u =>
        opNorm (expRes (emaW R.β) (R.F q) (samples q) 0 u -
          Rbar (Fw (emaW R.β)) (Muon.Drift.specOutFM (R.F q))
            (Muon.Drift.specInFM (R.F q)) (R.F q).C u) +
        opNorm (expResT (emaW R.β) (R.F q) (samples q) 0 u -
          Rtbar (Fw (emaW R.β)) (Muon.Drift.specOutFM (R.F q))
            (Muon.Drift.specInFM (R.F q)) (R.F q).C u)
      change g ϱ ≤ ⨆ u, ⨆ _ : u ∈ ({ϱ} : Set ℝ), g u
      simpa only [Set.mem_singleton_iff] using
        (le_ciSup_ciSup_eq_left (α := ℝ) (β := ℝ) (b := ϱ)
          (f := fun u (_ : u = ϱ) => g u))
    exact (le_add_of_nonneg_right (tx_opNorm_nonneg _)).trans hsum
  have hhalf : ∀ q, |M q - Z| ≤ γstar * CSig * ϱ * eG q := by
    intro q
    have hh := thm_app_vol_half_same_iii_mean (rF q) (samples q) 0 (Sq q)
      γstar CSig ϱ ϱ (eG q) (hSize q) (hIn q) hϱ (heGbd q) ϱ ⟨le_rfl, le_rfl⟩
    rw [hzbar q] at hh
    exact hh
  have hraw : ∀ q,
      (((((q + 1) * B : ℕ) : ℝ))⁻¹ * (∫ ω, Matrix.trace (Fo q *
        frozenUpd (rF q) (samples q) ϱ 0 ω * Gi q *
        (frozenUpd (rF q) (samples q) ϱ 0 ω)ᵀ) ∂(P q))) = c * c * M q := by
    intro q
    rw [show Fo q = c • (rF q).C.Sout by rfl, show Gi q = c • (rF q).C.Sin by rfl,
      p6_raw_scale]
    congr 1
    dsimp [M]
    unfold sameTimeZ pairSigma
    rw [hIn q]
    simp_rw [Matrix.mul_one]
    rw [integral_const_mul]
  have hcent : ∀ q, |c * c * M q - A q| ≤
      (CSig / Real.sqrt ϱ + eD q) ^ 2 / ((q + 1) * B : ℕ) := by
    intro q
    have hh := lem_app_vol_centering_i (rF q) (samples q) 0 ϱ ϱ CSig (eD q) hϱ
      (hmean q) 0 ⟨le_rfl, le_rfl⟩ ⟨le_rfl, le_rfl⟩ (Fo q) (Gi q) (hFo1 q) (hGi1 q)
    simp only [Int.cast_zero, add_zero] at hh
    change |(((((q + 1) * B : ℕ) : ℝ))⁻¹ * (∫ ω, Matrix.trace (Fo q *
        frozenUpd (rF q) (samples q) ϱ 0 ω * Gi q *
        (frozenUpd (rF q) (samples q) ϱ 0 ω)ᵀ) ∂(P q))) - A q| ≤
      (CSig / Real.sqrt ϱ + eD q) ^ 2 / ((q + 1) * B : ℕ) at hh
    rw [hraw q] at hh
    exact hh
  have hBtop : Tendsto (fun q => ((((q + 1) * B : ℕ)) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp R.prop.B_top
  have hcent0 : Tendsto (fun q => (CSig / Real.sqrt ϱ + eD q) ^ 2 /
      (((q + 1) * B : ℕ) : ℝ)) atTop (𝓝 0) :=
    ((tendsto_const_nhds.add heD).pow 2).div_atTop hBtop
  have hhalf0 : Tendsto (fun q => c * c * (γstar * CSig * ϱ * eG q)) atTop (𝓝 0) := by
    simpa only [mul_assoc, mul_zero] using heG.const_mul (c * c * (γstar * CSig * ϱ))
  have hAZ : Tendsto A atTop (𝓝 (c * c * Z)) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    have h1 : ∀ᶠ q in atTop, (CSig / Real.sqrt ϱ + eD q) ^ 2 /
        (((q + 1) * B : ℕ) : ℝ) < ε / 2 := (tendsto_order.1 hcent0).2 _ (by positivity)
    have h2 : ∀ᶠ q in atTop, c * c * (γstar * CSig * ϱ * eG q) < ε / 2 :=
      (tendsto_order.1 hhalf0).2 _ (by positivity)
    have hev := h1.and h2
    rw [Filter.eventually_atTop] at hev
    obtain ⟨q₀, hq₀⟩ := hev
    refine ⟨q₀, fun q hq => ?_⟩
    obtain ⟨h1q, h2q⟩ := hq₀ q hq
    rw [Real.dist_eq]
    have ht := abs_sub_le (A q) (c * c * M q) (c * c * Z)
    have hm := hhalf q
    have hc' : 0 < c := hc
    have hm' := mul_le_mul_of_nonneg_left hm
      (mul_nonneg (abs_nonneg c) (abs_nonneg c))
    rw [abs_sub_comm (A q) (c * c * M q),
      show c * c * M q - c * c * Z = (c * c) * (M q - Z) by ring,
      abs_mul, abs_mul] at ht
    have ht' := ht.trans (add_le_add (hcent q) hm')
    simp only [abs_of_pos hc'] at ht'
    exact ht'.trans_lt (by linarith)
  have heq := tendsto_nhds_unique hA hAZ
  have hcc : c * c ≠ 0 := mul_ne_zero hc.ne' hc.ne'
  dsimp [L, Z] at heq ⊢
  exact mul_left_cancel₀ hcc heq

/-- `thm:app-vol-integrated`, snapshot `cr-2026-10-23`. Declaration of record. LaTeX, verbatim from `section.tex` (the whole environment):

```latex
\begin{theorem}[Integrated identification]\label{thm:app-vol-integrated}
Fix a finite dimension, diagonal $F,G$, and $\ridge,\ridge'\in I$.
\begin{enumerate}[label=(\roman*)]
\item For every $\ell\ge0$ and $T\ge1$,
\begin{equation}\label{eqn:app-vol-integrated-square}
\Big|\overline C_\ell[F,G](\ridge,\ridge')-\frac4{\pi^2}\int_0^T\!\!\int_0^T\mathfrak k_\ell[F,G](\ridge+x^2,\ridge'+y^2)\,dx\,dy\Big|\le\frac{4C_\Sigma\gamma_\star^{3/2}\norm F\norm G}{\pi T},
\end{equation}
so $\overline C_\ell[F,G]$ is the square-truncated double integral of the lag
kernel along the negative axis, with an error uniform in the dimension, the
lag and the ridges.
\item $\abs{\overline C_0[F,G]}\le\gamma_\star\norm F\norm G$ and
$\abs{\overline C_\ell[F,G]}\le\mathsf K_\star\norm F\norm G\,\bmom^\ell$ for $\ell\ge1$; at
$\bmom=0$, $\overline C_\ell[F,G]=0$ for every $\ell\ge1$.
\item The deterministic integrated coefficient
\begin{equation}\label{eqn:app-vol-Gammabar}
\overline\Gamma[F,G](\ridge,\ridge')\defeq\overline C_0[F,G](\ridge,\ridge')+\sum_{\ell\ge1}\Big(\overline C_\ell[F,G](\ridge,\ridge')+\overline C_\ell[F,G](\ridge',\ridge)\Big)
\end{equation}
converges absolutely, and $\overline\Gamma[F,G](\ridge,\ridge)\ge0$ whenever $F$ and
$G$ are positive semidefinite.
\item Under \cref{assum:app-setup-regime},
$\sup_{\ridge,\ridge'\in I}\sup_{F,G}\abs{\Gamma[F,G](\ridge,\ridge')-\overline\Gamma[F,G](\ridge,\ridge')}\to0$,
the supremum over diagonal $F,G$ of norm at most one, and the finite-time
contraction \cref{eqn:app-vol-finite-time} differs from $\overline\Gamma[F,G]$ by
$o(1)$ plus \cref{eqn:app-vol-finite-time-error}, along every joint sequence
of dimensions and block lengths $T$.
\item For the covariance-weighted coefficient
$\overline\Gamma\defeq\overline\Gamma[\Sigmaout,\Sigmain]$, $\sup_{I^2}\abs{\Gamma-\overline\Gamma}\to0$
under \cref{assum:app-setup-regime}. When $\Sigmain=\Id$,
$\overline C_0(\ridge,\ridge)=\overline Z(\ridge)$ of \cref{eqn:app-vol-half-candidates}.
\end{enumerate}
\end{theorem}
```
-/
theorem thm_app_vol_integrated_v (cert : Muon.External.GaussianOpNorm)
    (R : SetupRegime) (Ω : ℕ → Type) [∀ k, MeasurableSpace (Ω k)]
    (P : ∀ k, Measure (Ω k)) [∀ k, IsProbabilityMeasure (P k)]
    (S : ∀ k, FrozenSamples (P k) (R.m k) (R.n k) (R.B k))
    (Sp : ∀ k : ℕ, SpectralData (R.F k).C) :
    -- (a) the covariance-weighted coefficient on I^2
    (∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, ∀ t : ℤ, ∀ ϱ ∈ Set.Icc R.ϱlo R.ϱhi,
      ∀ ϱ' ∈ Set.Icc R.ϱlo R.ϱhi,
      |weightedGamma (R.F k) (S k) t ϱ ϱ' -
        lagGammaBar cert R.γstar R.CSig (R.F k).β (R.B k) (Sp k).μ (Sp k).lam
          (Sp k).μ (Sp k).lam ϱ ϱ'| ≤ ε) ∧
    -- (b) with Σ_in = Id, the zero-lag diagonal is the same-time total Z̄ of
    -- eqn:app-vol-half-candidates, with the spectral measures nuOut and nuIn
    (∀ k : ℕ, (R.F k).C.Sin = 1 →
      ∀ ν ν' : FiniteMeasure ℝ,
      (ν : Measure ℝ) = Muon.nuOut (R.F k).C (R.B k) →
      (ν' : Measure ℝ) = Muon.nuIn (R.F k).C (R.B k) →
      ∀ ϱ ∈ Set.Icc R.ϱlo R.ϱhi,
        lagResp cert R.γstar R.CSig (R.F k).β 0 (R.B k) (Sp k).μ (Sp k).lam (Sp k).μ (Sp k).lam
            (omegaF ϱ) (omegaF ϱ) =
          zbarRaw (R.F k).β (R.B k) ν ν' (Sp k).μ ϱ) := by
  refine ⟨p6_weighted_convergence cert R Ω P S Sp, ?_⟩
  intro k hId ν ν' hν hν' ϱ hϱI
  exact p6_zero_lag_zbar cert R.γstar R.CSig (R.F k) (Sp k)
    ⟨R.dims k, R.normOut k, R.normIn k⟩ R.hC hId ν ν' hν hν' ϱ
      (R.hϱ.1.trans_le hϱI.1)

/-! ## Coordinator bridge: general filters (for lem:app-pl-pieces) -/

/-- Coordinator bridge (no source label), snapshot `cr-2026-10-23`. Integrated response of a pair of general
filters, `Γ̄[F,G](f₁,f₂) = 𝔑_0[F,G](f₁,f₂) + ∑_{ℓ≥1} (𝔑_ℓ[F,G](f₁,f₂) + 𝔑_ℓ[F,G](f₂,f₁))`: the series
`eqn:app-vol-Gammabar` with the regularized filters `ω_ϱ, ω_ϱ'` replaced by `f₁, f₂`, so that
`lagGammaBar … ϱ ϱ' = lagGammaGen … (omegaF ϱ) (omegaF ϱ')` holds by `rfl`. The series is a `tsum`; its
absolute convergence for odd, bounded, Lipschitz filters is `lag_envelope_generic`. It is the "integrated
covariance of $f$" of the proof of `lem:app-pl-pieces` (`sections/06-power-law/section.tex` l.1848–1866), for
`f₁ = f₂ = f`, verbatim:
```latex
nonnegative; the coupling of \cref{lem:app-pl-two-ridge}, with $\operatorname{Lip}(f)$
in place of $\ridge^{-1/2}$, gives the geometric lag envelope, so these sums converge
to the integrated covariance as in the proof of
\cref{thm:app-vol-integrated}(iii).
```
-/
def lagGammaGen (cert : Muon.External.GaussianOpNorm) (γstar CSig : ℝ) {m n : ℕ} (β : ℝ) (B : ℕ)
    (μ : Fin m → ℝ) (lam : Fin n → ℝ) (Fd : Fin m → ℝ) (Gd : Fin n → ℝ) (f₁ f₂ : ℝ → ℝ) : ℝ :=
  lagResp cert γstar CSig β 0 B μ lam Fd Gd f₁ f₂ +
    ∑' ℓ : ℕ, (lagResp cert γstar CSig β (ℓ + 1) B μ lam Fd Gd f₁ f₂ +
      lagResp cert γstar CSig β (ℓ + 1) B μ lam Fd Gd f₂ f₁)

private lemma lge_prob (m n B : ℕ) : IsProbabilityMeasure (indepSpaceLaw m n B) := by
  unfold indepSpaceLaw indepSlotLaw
  infer_instance

private lemma lge_borel (m n : ℕ) : BorelSpace (Mat m n) :=
  inferInstanceAs (BorelSpace (Fin m → Fin n → ℝ))

private lemma lge_sc (m n : ℕ) : SecondCountableTopology (Mat m n) :=
  inferInstanceAs (SecondCountableTopology (Fin m → Fin n → ℝ))

private lemma lge_tsum_meas {m n : ℕ} {Ω : Type*} (m1 : MeasurableSpace Ω) (f : ℕ → Ω → Mat m n)
    (hf : ∀ j, Measurable[m1] (f j)) : Measurable[m1] (fun ω ↦ ∑' j, f j ω) := by
  letI : MeasurableSpace Ω := m1
  haveI : TopologicalSpace.IsCompletelyPseudoMetrizableSpace (Mat m n) :=
    inferInstanceAs (TopologicalSpace.IsCompletelyPseudoMetrizableSpace (Fin m → Fin n → ℝ))
  haveI : SecondCountableTopology (Mat m n) := lge_sc m n
  exact Measurable.tsum hf

private lemma lge_batch_meas_sub {m n B : ℕ} (F : FrozenParams m n B) (s : ℤ) (T : Set (ℤ × Fin B))
    (hT : ∀ a, (s, a) ∈ T) :
    Measurable[⨆ i ∈ T, MeasurableSpace.comap
      (fun ω : (ℤ × Fin B) → ℝ × (Vec m × Vec n) ↦ ω i) inferInstance]
      (fun ω ↦ indepBatchG F ω s) := by
  have h : ∀ a, Measurable[⨆ i ∈ T, MeasurableSpace.comap
      (fun ω : (ℤ × Fin B) → ℝ × (Vec m × Vec n) ↦ ω i) inferInstance]
      (fun ω : (ℤ × Fin B) → ℝ × (Vec m × Vec n) ↦ ω (s, a)) := fun a ↦
    Measurable.of_comap_le (le_iSup₂ (f := fun i (_ : i ∈ T) ↦ MeasurableSpace.comap
      (fun ω : (ℤ × Fin B) → ℝ × (Vec m × Vec n) ↦ ω i) inferInstance) (s, a) (hT a))
  generalize (⨆ i ∈ T, MeasurableSpace.comap
      (fun ω : (ℤ × Fin B) → ℝ × (Vec m × Vec n) ↦ ω i) inferInstance) = m1 at h ⊢
  letI : MeasurableSpace ((ℤ × Fin B) → ℝ × (Vec m × Vec n)) := m1
  haveI := lge_borel m n
  haveI := lge_sc m n
  unfold indepBatchG
  refine Measurable.const_smul ?_ ((B : ℝ))⁻¹
  refine Finset.measurable_sum _ fun a _ ↦ ?_
  have hc : Continuous (fun p : ℝ × (Vec m × Vec n) ↦
      p.1 • (rOut F.C * outer p.2.1 p.2.2 * rIn F.C)) := by
    fun_prop
  exact hc.measurable.comp (h a)

private lemma lge_prod_meas {m n B : ℕ} (F : FrozenParams m n B) (s : ℤ) :
    Measurable (fun ω : (ℤ × Fin B) → ℝ × (Vec m × Vec n) ↦ def_app_vol_product F ω s) := by
  haveI := lge_borel m n
  haveI := lge_sc m n
  unfold def_app_vol_product
  refine lge_tsum_meas _ _ fun j ↦ ?_
  refine Measurable.const_smul ?_ (emaW F.β j)
  unfold indepBatchG
  refine Measurable.const_smul ?_ ((B : ℝ))⁻¹
  refine Finset.measurable_sum _ fun a _ ↦ ?_
  have hc : Continuous (fun p : ℝ × (Vec m × Vec n) ↦
      p.1 • (rOut F.C * outer p.2.1 p.2.2 * rIn F.C)) := by
    fun_prop
  exact hc.measurable.comp (measurable_pi_apply (s + 1 - (j : ℤ), a))

private lemma lge_batch_meas {m n B : ℕ} (F : FrozenParams m n B) (s : ℤ) :
    Measurable (fun ω : (ℤ × Fin B) → ℝ × (Vec m × Vec n) ↦ indepBatchG F ω s) := by
  haveI := lge_borel m n
  haveI := lge_sc m n
  unfold indepBatchG
  refine Measurable.const_smul ?_ ((B : ℝ))⁻¹
  refine Finset.measurable_sum _ fun a _ ↦ ?_
  have hc : Continuous (fun p : ℝ × (Vec m × Vec n) ↦
      p.1 • (rOut F.C * outer p.2.1 p.2.2 * rIn F.C)) := by
    fun_prop
  exact hc.measurable.comp (measurable_pi_apply (s, a))

private lemma lge_indep {m n B : ℕ} (F : FrozenParams m n B) (t : ℤ) (ℓ : ℕ) :
    IndepFun (fun ω : (ℤ × Fin B) → ℝ × (Vec m × Vec n) ↦ def_app_vol_product F ω t)
      (fun ω ↦ ∑ j ∈ Finset.range ℓ,
        emaW F.β j • indepBatchG F ω (t + (ℓ : ℤ) + 1 - (j : ℤ)))
      (indepSpaceLaw m n B) := by
  haveI := lge_prob m n B
  have hI : iIndepFun (fun (p : ℤ × Fin B) (ω : (ℤ × Fin B) → ℝ × (Vec m × Vec n)) ↦ ω p)
      (indepSpaceLaw m n B) :=
    iIndepFun_infinitePi (P := fun _ : ℤ × Fin B ↦ indepSlotLaw m n)
      (X := fun _ x ↦ x) (fun _ ↦ measurable_id)
  have hind := (iIndepFun_iff_iIndep
    (fun _ : ℤ × Fin B ↦ (inferInstance : MeasurableSpace (ℝ × (Vec m × Vec n))))
    (fun (p : ℤ × Fin B) (ω : (ℤ × Fin B) → ℝ × (Vec m × Vec n)) ↦ ω p)
    (indepSpaceLaw m n B)).mp hI
  have hdisj : Disjoint {p : ℤ × Fin B | p.1 ≤ t + 1} {p : ℤ × Fin B | t + 2 ≤ p.1} := by
    rw [Set.disjoint_left]
    intro p h1 h2
    simp only [Set.mem_setOf_eq] at h1 h2
    omega
  have key := indep_iSup_of_disjoint
    (fun p : ℤ × Fin B ↦ (measurable_pi_apply (X := fun _ : ℤ × Fin B ↦ ℝ × (Vec m × Vec n)) p).comap_le)
    hind hdisj
  have hA : Measurable[⨆ i ∈ {p : ℤ × Fin B | p.1 ≤ t + 1}, MeasurableSpace.comap
      (fun ω : (ℤ × Fin B) → ℝ × (Vec m × Vec n) ↦ ω i) inferInstance]
      (fun ω ↦ def_app_vol_product F ω t) := by
    unfold def_app_vol_product
    refine lge_tsum_meas _ _ fun j ↦ ?_
    refine Measurable.const_smul ?_ (emaW F.β j)
    exact lge_batch_meas_sub F _ _ (fun a ↦ by
      show t + 1 - (j : ℤ) ≤ t + 1
      omega)
  have hB : Measurable[⨆ i ∈ {p : ℤ × Fin B | t + 2 ≤ p.1}, MeasurableSpace.comap
      (fun ω : (ℤ × Fin B) → ℝ × (Vec m × Vec n) ↦ ω i) inferInstance]
      (fun ω ↦ ∑ j ∈ Finset.range ℓ,
        emaW F.β j • indepBatchG F ω (t + (ℓ : ℤ) + 1 - (j : ℤ))) := by
    refine Finset.measurable_sum _ fun j hj ↦ ?_
    rw [Finset.mem_range] at hj
    refine Measurable.const_smul ?_ (emaW F.β j)
    exact lge_batch_meas_sub F _ _ (fun a ↦ by
      show t + 2 ≤ t + (ℓ : ℤ) + 1 - (j : ℤ)
      omega)
  exact (IndepFun_iff_Indep _ _ (indepSpaceLaw m n B)).mpr
    (indep_of_indep_of_le_left (indep_of_indep_of_le_right key (measurable_iff_comap_le.mp hB))
      (measurable_iff_comap_le.mp hA))

open scoped Matrix.Norms.Frobenius in
private lemma lge_decomp {m n B : ℕ} (F : FrozenParams m n B) (t : ℤ) (ℓ : ℕ) :
    ∀ᵐ ω ∂(indepSpaceLaw m n B), def_app_vol_product F ω (t + (ℓ : ℤ)) =
      (∑ j ∈ Finset.range ℓ, emaW F.β j • indepBatchG F ω (t + (ℓ : ℤ) + 1 - (j : ℤ))) +
      F.β ^ ℓ • def_app_vol_product F ω t := by
  filter_upwards [def_app_vol_product_summable F] with ω hω
  have hs : Summable fun j : ℕ ↦
      emaW F.β j • indepBatchG F ω (t + (ℓ : ℤ) + 1 - (j : ℤ)) := by
    refine Summable.of_norm ?_
    simpa [fro_eq_norm] using hω (t + (ℓ : ℤ))
  unfold def_app_vol_product
  rw [← Summable.sum_add_tsum_nat_add' ((summable_nat_add_iff ℓ).2 hs)]
  congr 1
  have hshift : ∀ i : ℕ, emaW F.β (i + ℓ) • indepBatchG F ω
      (t + (ℓ : ℤ) + 1 - ((i + ℓ : ℕ) : ℤ)) =
      F.β ^ ℓ • (emaW F.β i • indepBatchG F ω (t + 1 - (i : ℤ))) := by
    intro i
    have e1 : t + (ℓ : ℤ) + 1 - ((i + ℓ : ℕ) : ℤ) = t + 1 - (i : ℤ) := by
      push_cast
      ring
    have e2 : emaW F.β (i + ℓ) = F.β ^ ℓ * emaW F.β i := by
      unfold emaW
      ring
    rw [e1, e2, smul_smul]
  simp_rw [hshift]
  exact tsum_const_smul'' _

private lemma lge_fro_nn {m n : ℕ} (K : Mat m n) : 0 ≤ fro K := Real.sqrt_nonneg _

private lemma lge_fro_transpose {m n : ℕ} (K : Mat m n) : fro Kᵀ = fro K := by
  unfold fro
  congr 1
  exact Finset.sum_comm

private lemma lge_fro_smul {m n : ℕ} (c : ℝ) (K : Mat m n) : fro (c • K) = |c| * fro K := by
  have h : ∀ i j, ‖(c • K) i j‖ ^ 2 = c ^ 2 * ‖K i j‖ ^ 2 := fun i j ↦ by
    rw [Matrix.smul_apply, smul_eq_mul, norm_mul, Real.norm_eq_abs, mul_pow, sq_abs]
  unfold fro
  simp only [h, ← Finset.mul_sum]
  rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs]

private lemma lge_fro_sq {m n : ℕ} (K : Mat m n) : fro K ^ 2 = ∑ i, ∑ j, K i j ^ 2 := by
  unfold fro
  rw [Real.sq_sqrt (Finset.sum_nonneg fun i _ ↦ Finset.sum_nonneg fun j _ ↦ by positivity)]
  simp [Real.norm_eq_abs, sq_abs]

private lemma lge_fro_mul_le_left {p q r : ℕ} (M : Mat p q) (N : Mat q r) :
    fro (M * N) ≤ opNorm M * fro N := by
  have hcol : ∀ j : Fin r, ∑ i, (M * N) i j ^ 2 ≤ opNorm M ^ 2 * ∑ k, N k j ^ 2 := by
    intro j
    obtain ⟨v, hv⟩ : ∃ v : EuclideanSpace ℝ (Fin q), ∀ k, v.ofLp k = N k j :=
      ⟨(EuclideanSpace.equiv (Fin q) ℝ).symm (fun k ↦ N k j), fun k ↦ rfl⟩
    have h1 : ‖(EuclideanSpace.equiv (Fin p) ℝ).symm (M *ᵥ v)‖ ≤ opNorm M * ‖v‖ := by
      rw [opNorm_eq_norm]
      exact Matrix.l2_opNorm_mulVec M v
    have h2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
    rw [mul_pow, EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq] at h2
    have e1 : ∀ i, ((EuclideanSpace.equiv (Fin p) ℝ).symm (M *ᵥ v)).ofLp i = (M * N) i j := by
      intro i
      simp [Matrix.mulVec, dotProduct, Matrix.mul_apply, hv]
    have e2 : ∑ k, v.ofLp k ^ 2 = ∑ k, N k j ^ 2 :=
      Finset.sum_congr rfl fun k _ ↦ by rw [hv]
    simp only [e1, e2] at h2
    exact h2
  have hfro : fro (M * N) ^ 2 ≤ (opNorm M * fro N) ^ 2 := by
    rw [lge_fro_sq, mul_pow, lge_fro_sq, Finset.sum_comm]
    calc ∑ j, ∑ i, (M * N) i j ^ 2 ≤ ∑ j : Fin r, opNorm M ^ 2 * ∑ k, N k j ^ 2 :=
          Finset.sum_le_sum fun j _ ↦ hcol j
      _ = opNorm M ^ 2 * ∑ k, ∑ j, N k j ^ 2 := by
          simp only [Finset.mul_sum]
          exact Finset.sum_comm
  exact (pow_le_pow_iff_left₀ (lge_fro_nn _) (mul_nonneg (tx_opNorm_nonneg M) (lge_fro_nn N))
    two_ne_zero).mp hfro

private lemma lge_fro_mul_le_right {p q r : ℕ} (M : Mat p q) (N : Mat q r) :
    fro (M * N) ≤ fro M * opNorm N := by
  have h := lge_fro_mul_le_left Nᵀ Mᵀ
  have hop : opNorm Nᵀ = opNorm N := by
    open scoped Matrix.Norms.L2Operator in
    rw [opNorm_eq_norm, opNorm_eq_norm, ← Matrix.conjTranspose_eq_transpose_of_trivial,
      Matrix.l2_opNorm_conjTranspose]
  rw [hop, lge_fro_transpose, ← Matrix.transpose_mul, lge_fro_transpose] at h
  linarith [mul_comm (opNorm N) (fro M)]

private lemma lge_trace_mul_transpose_le {m n : ℕ} (X C : Mat m n) :
    |Matrix.trace (X * Cᵀ)| ≤ fro X * fro C := by
  have htr : Matrix.trace (X * Cᵀ) = ∑ p : Fin m × Fin n, X p.1 p.2 * C p.1 p.2 := by
    simp [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Fintype.sum_prod_type]
  rw [htr]
  have cs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin m × Fin n))
    (fun p ↦ X p.1 p.2) (fun p ↦ C p.1 p.2)
  have hX : ∑ p : Fin m × Fin n, X p.1 p.2 ^ 2 = fro X ^ 2 := by
    rw [lge_fro_sq, Fintype.sum_prod_type]
  have hC : ∑ p : Fin m × Fin n, C p.1 p.2 ^ 2 = fro C ^ 2 := by
    rw [lge_fro_sq, Fintype.sum_prod_type]
  rw [hX, hC] at cs
  refine (pow_le_pow_iff_left₀ (abs_nonneg _) (mul_nonneg (lge_fro_nn X) (lge_fro_nn C))
    two_ne_zero).mp ?_
  rw [sq_abs, mul_pow]
  exact cs

private lemma lge_trace_le {m n : ℕ} (F : Mat m m) (G : Mat n n) (X Y : Mat m n) :
    |Matrix.trace (F * X * G * Yᵀ)| ≤ opNorm F * fro X * opNorm G * fro Y := by
  refine (lge_trace_mul_transpose_le (F * X * G) Y).trans ?_
  refine mul_le_mul_of_nonneg_right ?_ (lge_fro_nn _)
  calc fro (F * X * G) ≤ fro (F * X) * opNorm G := lge_fro_mul_le_right _ _
    _ ≤ (opNorm F * fro X) * opNorm G :=
        mul_le_mul_of_nonneg_right (lge_fro_mul_le_left _ _) (tx_opNorm_nonneg _)

private lemma lge_trace_meas {Ω : Type*} [MeasurableSpace Ω] {m n : ℕ}
    (F : Mat m m) (G : Mat n n) (X Y : Ω → Mat m n) (hX : Measurable X) (hY : Measurable Y) :
    Measurable (fun ω ↦ Matrix.trace (F * X ω * G * (Y ω)ᵀ)) := by
  unfold Matrix.trace
  refine Finset.measurable_sum _ fun i _ ↦ ?_
  simp only [Matrix.diag_apply, Matrix.mul_apply]
  fun_prop

private lemma lge_abs_entry_le_fro {m n : ℕ} (K : Mat m n) (i : Fin m) (j : Fin n) :
    |K i j| ≤ fro K := by
  unfold fro
  apply Real.abs_le_sqrt
  have h1 : ‖K i j‖ ^ 2 ≤ ∑ j', ‖K i j'‖ ^ 2 :=
    Finset.single_le_sum (f := fun j' ↦ ‖K i j'‖ ^ 2) (fun _ _ ↦ sq_nonneg _) (Finset.mem_univ j)
  have h2 : ∑ j', ‖K i j'‖ ^ 2 ≤ ∑ i', ∑ j', ‖K i' j'‖ ^ 2 :=
    Finset.single_le_sum (f := fun i' ↦ ∑ j', ‖K i' j'‖ ^ 2)
      (fun i' _ ↦ Finset.sum_nonneg (fun _ _ ↦ sq_nonneg _)) (Finset.mem_univ i)
  have h3 : ‖K i j‖ ^ 2 = K i j ^ 2 := by rw [Real.norm_eq_abs, sq_abs]
  linarith

open scoped Matrix.Norms.Frobenius in
private lemma lge_sharp_cont {m n : ℕ} (f : ℝ → ℝ) (hf : IsOddBddLip f) :
    Continuous (fun K : Mat m n ↦ oddSharp f K) := by
  have hnn : 0 ≤ lipConst f := tx_lip_nonneg f
  have hL : LipschitzWith (Real.toNNReal (lipConst f)) (fun K : Mat m n ↦ oddSharp f K) := by
    refine LipschitzWith.of_dist_le_mul fun K K' ↦ ?_
    rw [dist_eq_norm, dist_eq_norm, ← fro_eq_norm, ← fro_eq_norm, Real.coe_toNNReal _ hnn]
    exact (lem_app_vol_sharp_i f hf K K').2.2
  exact hL.continuous

private lemma lge_sharp_fro_le {m n : ℕ} (f : ℝ → ℝ) (hf : IsOddBddLip f) (K : Mat m n) :
    fro (oddSharp f K) ≤ lipConst f * fro K := by
  have h := (lem_app_vol_sharp_i f hf K 0).2.2
  rw [tx_oddSharp_zero f hf.1] at h
  simpa using h

private lemma lge_fro_meas {m n : ℕ} : Measurable (fun K : Mat m n ↦ fro K) := by
  unfold fro
  fun_prop

private lemma lge_moment {m n B : ℕ} (F : FrozenParams m n B) (γstar CSig : ℝ)
    (hS : SizeFin F.C B γstar CSig) (t : ℤ) :
    Integrable (fun ω ↦ fro (def_app_vol_product F ω t) ^ 2) (indepSpaceLaw m n B) ∧
    ∫ ω, fro (def_app_vol_product F ω t) ^ 2 ∂(indepSpaceLaw m n B) ≤
      CSig ^ 2 * γstar ^ 2 * B := by
  have hB : (0 : ℝ) < B := by exact_mod_cast F.hB
  have hβ0 := F.hβ.1
  have hβ1 := F.hβ.2
  refine ⟨?_, ?_⟩
  · by_contra hni
    have h0 := integral_undef hni
    have hm := def_app_vol_product_moment F t
    rw [h0, mul_zero, sPow_two hβ0 hβ1] at hm
    have hs2 : 0 < (1 - F.β) / (1 + F.β) := div_pos (by linarith) (by linarith)
    have hB2 : (0 : ℝ) < (B : ℝ) ^ 2 := by positivity
    have hprod : Matrix.trace F.C.Sout * Matrix.trace F.C.Sin = 0 := by
      have h1 : (1 - F.β) / (1 + F.β) / (B : ℝ) ^ 2 * Matrix.trace F.C.Sout *
          Matrix.trace F.C.Sin = 0 := hm.symm
      have h2 : (1 - F.β) / (1 + F.β) / (B : ℝ) ^ 2 ≠ 0 := (div_pos hs2 hB2).ne'
      rw [mul_assoc] at h1
      exact (mul_eq_zero.mp h1).resolve_left h2
    have hG : ∀ ω s, indepBatchG F ω s = 0 := by
      intro ω s
      rcases mul_eq_zero.mp hprod with h | h
      · have hz : F.C.Sout = 0 := (F.C.psdOut.trace_eq_zero_iff).mp h
        unfold indepBatchG
        simp [rOut, hz, CFC.sqrt_zero]
      · have hz : F.C.Sin = 0 := (F.C.psdIn.trace_eq_zero_iff).mp h
        unfold indepBatchG
        simp [rIn, hz, CFC.sqrt_zero]
    have hz : ∀ ω, def_app_vol_product F ω t = 0 := by
      intro ω
      unfold def_app_vol_product
      simp [hG]
    apply hni
    have he : (fun ω ↦ fro (def_app_vol_product F ω t) ^ 2) = fun _ ↦ 0 := by
      funext ω
      rw [hz]
      simp [fro]
    rw [he]
    exact integrable_zero _ _ _
  · have h := def_app_vol_product_moment_le F γstar CSig hS t
    rw [inv_mul_le_iff₀ hB] at h
    calc _ ≤ (B : ℝ) * (CSig ^ 2 * γstar ^ 2) := h
      _ = _ := by ring

private lemma lge_expand {m n : ℕ} (F : Mat m m) (G : Mat n n) (X N : Mat m n) :
    Matrix.trace (F * X * G * Nᵀ) = ∑ a, ∑ b, X a b * (G * Nᵀ * F) b a := by
  have h : Matrix.trace (F * X * G * Nᵀ) = Matrix.trace (X * (G * Nᵀ * F)) := by
    rw [show F * X * G * Nᵀ = F * (X * G * Nᵀ) by simp [Matrix.mul_assoc],
      Matrix.trace_mul_comm]
    simp [Matrix.mul_assoc]
  rw [h]
  simp [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]

private lemma lge_int_mul_bdd {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (f g : Ω → ℝ) (hf : Measurable f)
    (hg : Measurable g) (c d : ℝ) (hc : ∀ ω, |f ω| ≤ c) (hd : ∀ ω, |g ω| ≤ d) :
    Integrable (fun ω ↦ f ω * g ω) P := by
  refine Integrable.of_bound (C := c * d) (hf.mul hg).aestronglyMeasurable
    (Filter.Eventually.of_forall fun ω ↦ ?_)
  rw [Real.norm_eq_abs, abs_mul]
  exact mul_le_mul (hc ω) (hd ω) (abs_nonneg _) ((abs_nonneg _).trans (hc ω))

private lemma lge_zero {m n B : ℕ} (F : FrozenParams m n B) (Fm : Mat m m) (Gm : Mat n n)
    (f₁ f₂ : ℝ → ℝ) (hf₁ : IsOddBddLip f₁) (hf₂ : IsOddBddLip f₂) (t : ℤ)
    (N : ((ℤ × Fin B) → ℝ × (Vec m × Vec n)) → Mat m n) (hN : Measurable N)
    (hind : IndepFun (fun ω ↦ def_app_vol_product F ω t) N (indepSpaceLaw m n B)) :
    Integrable (fun ω ↦ Matrix.trace (Fm * oddSharp f₁ (def_app_vol_product F ω t) * Gm *
        (oddSharp f₂ (N ω))ᵀ)) (indepSpaceLaw m n B) ∧
      ∫ ω, Matrix.trace (Fm * oddSharp f₁ (def_app_vol_product F ω t) * Gm *
        (oddSharp f₂ (N ω))ᵀ) ∂(indepSpaceLaw m n B) = 0 := by
  haveI := lge_prob m n B
  haveI := lge_borel m n
  haveI := lge_sc m n
  let X : ((ℤ × Fin B) → ℝ × (Vec m × Vec n)) → Mat m n :=
    fun ω ↦ oddSharp f₁ (def_app_vol_product F ω t)
  let Y : ((ℤ × Fin B) → ℝ × (Vec m × Vec n)) → Mat m n :=
    fun ω ↦ oddSharp f₂ (N ω)
  have hXm : Measurable X := (lge_sharp_cont f₁ hf₁).measurable.comp (lge_prod_meas F t)
  have hYm : Measurable Y := (lge_sharp_cont f₂ hf₂).measurable.comp hN
  obtain ⟨f, hf⟩ : ∃ f : Fin m → Fin n → Mat m n → ℝ, f = fun a b K ↦ (oddSharp f₁ K) a b :=
    ⟨_, rfl⟩
  obtain ⟨g, hg⟩ : ∃ g : Fin m → Fin n → Mat m n → ℝ, g = fun a b K ↦
      (Gm * (oddSharp f₂ K)ᵀ * Fm) b a := ⟨_, rfl⟩
  have hfm : ∀ a b, Measurable (f a b) := fun a b ↦ by
    rw [hf]
    exact (measurable_pi_apply b).comp ((measurable_pi_apply a).comp
      (lge_sharp_cont f₁ hf₁).measurable)
  have hgm : ∀ a b, Measurable (g a b) := fun a b ↦ by
    rw [hg]
    have hc : Continuous (fun K : Mat m n ↦ Gm * (oddSharp f₂ K)ᵀ * Fm) :=
      (continuous_const.matrix_mul (lge_sharp_cont f₂ hf₂).matrix_transpose).matrix_mul
        continuous_const
    exact ((continuous_apply a).comp ((continuous_apply b).comp hc)).measurable
  let c₁ := Real.sqrt ((min m n : ℕ) : ℝ) * supNorm f₁
  let c₂ := opNorm Gm * (Real.sqrt ((min m n : ℕ) : ℝ) * supNorm f₂) * opNorm Fm
  have hfb : ∀ a b K, |f a b K| ≤ c₁ := by
    intro a b K
    rw [hf]
    exact (lge_abs_entry_le_fro _ a b).trans (lem_app_vol_sharp_i f₁ hf₁ K K).2.1
  have hgb : ∀ a b K, |g a b K| ≤ c₂ := by
    intro a b K
    rw [hg]
    refine (lge_abs_entry_le_fro _ b a).trans ?_
    calc fro (Gm * (oddSharp f₂ K)ᵀ * Fm)
        ≤ fro (Gm * (oddSharp f₂ K)ᵀ) * opNorm Fm := lge_fro_mul_le_right _ _
      _ ≤ (opNorm Gm * fro (oddSharp f₂ K)ᵀ) * opNorm Fm :=
          mul_le_mul_of_nonneg_right (lge_fro_mul_le_left _ _) (tx_opNorm_nonneg _)
      _ = opNorm Gm * fro (oddSharp f₂ K) * opNorm Fm := by rw [lge_fro_transpose]
      _ ≤ c₂ := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (lem_app_vol_sharp_i f₂ hf₂ K K).2.1
              (tx_opNorm_nonneg _)) (tx_opNorm_nonneg _)
  have hint : ∀ a b, Integrable (fun ω ↦
      f a b (def_app_vol_product F ω t) * g a b (N ω)) (indepSpaceLaw m n B) := by
    intro a b
    exact lge_int_mul_bdd _ _ ((hfm a b).comp (lge_prod_meas F t)) ((hgm a b).comp hN)
      c₁ c₂ (fun ω ↦ hfb a b _) (fun ω ↦ hgb a b _)
  have he : ∀ ω, Matrix.trace (Fm * X ω * Gm * (Y ω)ᵀ) = ∑ a, ∑ b,
      f a b (def_app_vol_product F ω t) * g a b (N ω) := by
    intro ω
    rw [lge_expand, hf, hg]
  have hi : Integrable (fun ω ↦ Matrix.trace (Fm * X ω * Gm * (Y ω)ᵀ))
      (indepSpaceLaw m n B) := by
    simp_rw [he]
    exact integrable_finsetSum _ fun a _ ↦ integrable_finsetSum _ fun b _ ↦ hint a b
  refine ⟨hi, ?_⟩
  change ∫ ω, Matrix.trace (Fm * X ω * Gm * (Y ω)ᵀ) ∂(indepSpaceLaw m n B) = 0
  simp_rw [he]
  rw [integral_finsetSum _ (fun a _ ↦ integrable_finsetSum _ (fun b _ ↦ hint a b))]
  refine Finset.sum_eq_zero fun a _ ↦ ?_
  rw [integral_finsetSum _ (fun b _ ↦ hint a b)]
  refine Finset.sum_eq_zero fun b _ ↦ ?_
  rw [hind.integral_fun_comp_mul_comp (lge_prod_meas F t).aemeasurable hN.aemeasurable
    (hfm a b).aestronglyMeasurable (hgm a b).aestronglyMeasurable]
  have hzero : ∫ ω, f a b (def_app_vol_product F ω t) ∂(indepSpaceLaw m n B) = 0 := by
    have hm := def_app_vol_product_mean_oddSharp F f₁ hf₁.1 hf₁.2.1 t
    have hm' := congrFun (congrFun hm a) b
    simpa [hf, mean] using hm'
  rw [hzero, zero_mul]

/-- Coordinator bridge (no source label), snapshot `cr-2026-10-23`. Geometric lag envelope for general filters,
independent model at a fixed dimension: for odd, bounded, Lipschitz `f₁, f₂`, any tests `F, G` and every
`t ∈ ℤ`, `ℓ ∈ ℕ`,
`|𝔼 𝒦^{F,G}[f₁,f₂](M^g_t, M^g_{t+ℓ})| ≤ √2 γ⋆² C_Σ² Lip(f₁) Lip(f₂) ‖F‖ ‖G‖ β^ℓ`.
This is the independent clause of `thm:app-vol-lag-reduction`(ii) (`thm_app_vol_lag_reduction_ii_indep`) and
the envelope `eqn:app-pl-envelope`, with `Lip(f₁) Lip(f₂)` in place of the ridge constant `ϱ₋^{-1/2}`; `ℓ = 0`
is included (`β^0 = 1`). Source: the proof of `lem:app-pl-pieces` (`sections/06-power-law/section.tex`
l.1855–1856), verbatim:
```latex
nonnegative; the coupling of \cref{lem:app-pl-two-ridge}, with $\operatorname{Lip}(f)$
in place of $\ridge^{-1/2}$, gives the geometric lag envelope,
```
and the proof of `lem:app-pl-two-ridge` (l.542–555), verbatim:
```latex
The envelope is the coupling of the proof of
\cref{thm:app-vol-lag-reduction}(ii). Let $M^*$ be built from an independent
past, so that $M^*$ is independent of $M^{\mathrm g}_t$, has the law of
$M^{\mathrm g}_{t+\ell}$, and $M^{\mathrm g}_{t+\ell}-M^*=\bmom^\ell(M^{\mathrm g}_t-M'_t)$
with $M'_t$ an independent copy of $M^{\mathrm g}_t$. The term with $M^*$ has
zero mean, so the Cauchy--Schwarz inequality over the copies and
\cref{eqn:app-setup-lipschitz} give
```
with, from the proof of `thm:app-vol-lag-reduction`(ii) (`sections/04-volatility/section.tex` l.954–956):
```latex
For the independent model the same coupling applies, with
$\EE\norm{M^{\mathrm g}_t-M^{\mathrm g\prime}_t}_\F^2=2\sw2B^{-1}\Tr\Sigmaout\Tr\Sigmain\le2C_\Sigma^2\gamma_\star^2B$
in place of $2\sw2\mathsf V_B$.
```
Proof route: as `thm_app_vol_lag_reduction_ii_indep`, with `oddSharp f₂` in place of `Q ϱ'`. Let `N_ℓ` be the
fresh part `∑_{j<ℓ} w_j G^g_{t+ℓ+1-j}`, independent of `M^g_t`, so `M^g_{t+ℓ} - N_ℓ = β^ℓ M^g_t`.
`𝔼 f₁^♯(M^g_t) = 0` (oddness of `f₁`, and `g ↦ -g` preserves the slot law), so the `N_ℓ` term vanishes. Then
`|Tr[F X G Yᵀ]| ≤ ‖F‖ ‖G‖ ‖X‖_F ‖Y‖_F`, `lem_app_vol_sharp_i` (Frobenius Lipschitz bound with `lipConst`, and
`f^♯(0) = 0`), and `𝔼‖M^g_t‖_F² = s₂ B⁻¹ Tr Σ_out Tr Σ_in ≤ γ⋆² C_Σ² B` (`SizeFin`, `s₂ ≤ 1`) give the bound
with constant `γ⋆² C_Σ²` (the `√2` is slack, matching the `M'_t` coupling of the source). -/
theorem lag_envelope_generic_indep {m n B : ℕ} (Fp : FrozenParams m n B) (γstar CSig : ℝ)
    (hS : SizeFin Fp.C B γstar CSig) (f₁ f₂ : ℝ → ℝ) (hf₁ : IsOddBddLip f₁) (hf₂ : IsOddBddLip f₂)
    (Fm : Mat m m) (Gm : Mat n n) (t : ℤ) (ℓ : ℕ) :
    |∫ ω, contraction B Fm Gm f₁ f₂ (def_app_vol_product Fp ω t)
        (def_app_vol_product Fp ω (t + (ℓ : ℤ))) ∂(indepSpaceLaw m n B)| ≤
      Real.sqrt 2 * γstar ^ 2 * CSig ^ 2 * lipConst f₁ * lipConst f₂ *
        opNorm Fm * opNorm Gm * Fp.β ^ ℓ := by
  haveI := lge_prob m n B
  haveI := lge_borel m n
  haveI := lge_sc m n
  let M : ((ℤ × Fin B) → ℝ × (Vec m × Vec n)) → Mat m n :=
    fun ω ↦ def_app_vol_product Fp ω t
  let H : ((ℤ × Fin B) → ℝ × (Vec m × Vec n)) → Mat m n :=
    fun ω ↦ def_app_vol_product Fp ω (t + (ℓ : ℤ))
  let N : ((ℤ × Fin B) → ℝ × (Vec m × Vec n)) → Mat m n := fun ω ↦
    ∑ j ∈ Finset.range ℓ, emaW Fp.β j • indepBatchG Fp ω (t + (ℓ : ℤ) + 1 - (j : ℤ))
  let X := fun ω ↦ oddSharp f₁ (M ω)
  let Y := fun ω ↦ oddSharp f₂ (H ω)
  let Nq := fun ω ↦ oddSharp f₂ (N ω)
  let D := fun ω ↦ Y ω - Nq ω
  have hMm : Measurable M := lge_prod_meas Fp t
  have hHm : Measurable H := lge_prod_meas Fp (t + (ℓ : ℤ))
  have hNm : Measurable N := by
    dsimp [N]
    exact Finset.measurable_sum _ fun j _ ↦
      (lge_batch_meas Fp (t + (ℓ : ℤ) + 1 - (j : ℤ))).const_smul (emaW Fp.β j)
  have hXm : Measurable X := (lge_sharp_cont f₁ hf₁).measurable.comp hMm
  have hYm : Measurable Y := (lge_sharp_cont f₂ hf₂).measurable.comp hHm
  have hNqm : Measurable Nq := (lge_sharp_cont f₂ hf₂).measurable.comp hNm
  have hDm : Measurable D := by
    have hsub : Measurable (fun p : Mat m n × Mat m n ↦ p.1 - p.2) :=
      (continuous_fst.sub continuous_snd).measurable
    exact hsub.comp (hYm.prodMk hNqm)
  have hzero := lge_zero Fp Fm Gm f₁ f₂ hf₁ hf₂ t N hNm (lge_indep Fp t ℓ)
  have hdec : ∀ᵐ ω ∂(indepSpaceLaw m n B), H ω = N ω + Fp.β ^ ℓ • M ω := by
    simpa [M, H, N] using lge_decomp Fp t ℓ
  let C : ℝ := opNorm Fm * lipConst f₁ * opNorm Gm * lipConst f₂ * Fp.β ^ ℓ
  have hL₁ : 0 ≤ lipConst f₁ := tx_lip_nonneg f₁
  have hL₂ : 0 ≤ lipConst f₂ := tx_lip_nonneg f₂
  have hC : 0 ≤ C := by
    dsimp [C]
    exact mul_nonneg
      (mul_nonneg (mul_nonneg (mul_nonneg (tx_opNorm_nonneg _) hL₁) (tx_opNorm_nonneg _)) hL₂)
      (pow_nonneg Fp.hβ.1 _)
  have hbound : ∀ᵐ ω ∂(indepSpaceLaw m n B),
      |Matrix.trace (Fm * X ω * Gm * (D ω)ᵀ)| ≤ C * fro (M ω) ^ 2 := by
    filter_upwards [hdec] with ω hω
    have hdiff : H ω - N ω = Fp.β ^ ℓ • M ω := by
      rw [hω]
      abel
    have hXb : fro (X ω) ≤ lipConst f₁ * fro (M ω) := lge_sharp_fro_le f₁ hf₁ (M ω)
    have hDb : fro (D ω) ≤ lipConst f₂ * (Fp.β ^ ℓ * fro (M ω)) := by
      have h := (lem_app_vol_sharp_i f₂ hf₂ (H ω) (N ω)).2.2
      rw [hdiff, lge_fro_smul, abs_of_nonneg (pow_nonneg Fp.hβ.1 _)] at h
      exact h
    calc |Matrix.trace (Fm * X ω * Gm * (D ω)ᵀ)|
        ≤ opNorm Fm * fro (X ω) * opNorm Gm * fro (D ω) := lge_trace_le _ _ _ _
      _ ≤ opNorm Fm * (lipConst f₁ * fro (M ω)) * opNorm Gm *
          (lipConst f₂ * (Fp.β ^ ℓ * fro (M ω))) := by
            have h1 : opNorm Fm * fro (X ω) ≤
                opNorm Fm * (lipConst f₁ * fro (M ω)) :=
              mul_le_mul_of_nonneg_left hXb (tx_opNorm_nonneg _)
            have h2 : opNorm Fm * fro (X ω) * opNorm Gm ≤
                opNorm Fm * (lipConst f₁ * fro (M ω)) * opNorm Gm :=
              mul_le_mul_of_nonneg_right h1 (tx_opNorm_nonneg _)
            exact mul_le_mul h2 hDb (lge_fro_nn _)
              (mul_nonneg (mul_nonneg (tx_opNorm_nonneg _)
                (mul_nonneg hL₁ (lge_fro_nn _))) (tx_opNorm_nonneg _))
      _ = C * fro (M ω) ^ 2 := by ring
  have hmom := lge_moment Fp γstar CSig hS t
  have htrm : Measurable (fun ω ↦ Matrix.trace (Fm * X ω * Gm * (D ω)ᵀ)) :=
    lge_trace_meas Fm Gm X D hXm hDm
  have hiD : Integrable (fun ω ↦ Matrix.trace (Fm * X ω * Gm * (D ω)ᵀ))
      (indepSpaceLaw m n B) := by
    refine (hmom.1.const_mul C).mono' htrm.aestronglyMeasurable ?_
    filter_upwards [hbound] with ω hb
    rw [Real.norm_eq_abs]
    simpa only [M] using hb
  have hpt : ∀ ω, Matrix.trace (Fm * X ω * Gm * (Y ω)ᵀ) =
      Matrix.trace (Fm * X ω * Gm * (D ω)ᵀ) +
        Matrix.trace (Fm * X ω * Gm * (Nq ω)ᵀ) := fun ω ↦ by
    dsimp [D]
    rw [Matrix.transpose_sub, Matrix.mul_sub, Matrix.trace_sub]
    ring
  have hI0 : ∫ ω, Matrix.trace (Fm * X ω * Gm * (Y ω)ᵀ) ∂(indepSpaceLaw m n B) =
      ∫ ω, Matrix.trace (Fm * X ω * Gm * (D ω)ᵀ) ∂(indepSpaceLaw m n B) := by
    simp_rw [hpt]
    rw [integral_add hiD hzero.1, hzero.2, add_zero]
  have habs : |∫ ω, Matrix.trace (Fm * X ω * Gm * (D ω)ᵀ) ∂(indepSpaceLaw m n B)| ≤
      C * ∫ ω, fro (M ω) ^ 2 ∂(indepSpaceLaw m n B) := by
    calc |∫ ω, Matrix.trace (Fm * X ω * Gm * (D ω)ᵀ) ∂(indepSpaceLaw m n B)|
        ≤ ∫ ω, |Matrix.trace (Fm * X ω * Gm * (D ω)ᵀ)| ∂(indepSpaceLaw m n B) :=
          abs_integral_le_integral_abs
      _ ≤ ∫ ω, C * fro (M ω) ^ 2 ∂(indepSpaceLaw m n B) :=
          integral_mono_ae hiD.abs (hmom.1.const_mul C) hbound
      _ = C * ∫ ω, fro (M ω) ^ 2 ∂(indepSpaceLaw m n B) := by rw [integral_const_mul]
  have hB : (0 : ℝ) < B := by exact_mod_cast Fp.hB
  have hscaled : |(B : ℝ)⁻¹ *
      ∫ ω, Matrix.trace (Fm * X ω * Gm * (D ω)ᵀ) ∂(indepSpaceLaw m n B)| ≤
      C * ((B : ℝ)⁻¹ * ∫ ω, fro (M ω) ^ 2 ∂(indepSpaceLaw m n B)) := by
    rw [abs_mul, abs_of_nonneg (inv_nonneg.mpr hB.le)]
    calc (B : ℝ)⁻¹ * |∫ ω, Matrix.trace (Fm * X ω * Gm * (D ω)ᵀ)
          ∂(indepSpaceLaw m n B)|
        ≤ (B : ℝ)⁻¹ * (C * ∫ ω, fro (M ω) ^ 2 ∂(indepSpaceLaw m n B)) :=
          mul_le_mul_of_nonneg_left habs (inv_nonneg.mpr hB.le)
      _ = C * ((B : ℝ)⁻¹ * ∫ ω, fro (M ω) ^ 2 ∂(indepSpaceLaw m n B)) := by ring
  have hcore : |(B : ℝ)⁻¹ *
      ∫ ω, Matrix.trace (Fm * X ω * Gm * (D ω)ᵀ) ∂(indepSpaceLaw m n B)| ≤
      C * (CSig ^ 2 * γstar ^ 2) :=
    hscaled.trans (mul_le_mul_of_nonneg_left
      (show (B : ℝ)⁻¹ * ∫ ω, fro (M ω) ^ 2 ∂(indepSpaceLaw m n B) ≤
          CSig ^ 2 * γstar ^ 2 by
        simpa [M] using def_app_vol_product_moment_le Fp γstar CSig hS t) hC)
  simp only [contraction, integral_const_mul, M, H, X, Y] at ⊢
  rw [hI0]
  refine hcore.trans ?_
  have hsqrt : (1 : ℝ) ≤ Real.sqrt 2 := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_le_sqrt (by norm_num)
  have hrest : 0 ≤ γstar ^ 2 * CSig ^ 2 * lipConst f₁ * lipConst f₂ *
      opNorm Fm * opNorm Gm * Fp.β ^ ℓ := by
    have h1 : 0 ≤ γstar ^ 2 * CSig ^ 2 := mul_nonneg (sq_nonneg _) (sq_nonneg _)
    have h2 : 0 ≤ γstar ^ 2 * CSig ^ 2 * lipConst f₁ := mul_nonneg h1 hL₁
    have h3 : 0 ≤ γstar ^ 2 * CSig ^ 2 * lipConst f₁ * lipConst f₂ := mul_nonneg h2 hL₂
    have h4 : 0 ≤ γstar ^ 2 * CSig ^ 2 * lipConst f₁ * lipConst f₂ * opNorm Fm :=
      mul_nonneg h3 (tx_opNorm_nonneg _)
    have h5 : 0 ≤ γstar ^ 2 * CSig ^ 2 * lipConst f₁ * lipConst f₂ * opNorm Fm * opNorm Gm :=
      mul_nonneg h4 (tx_opNorm_nonneg _)
    exact mul_nonneg h5 (pow_nonneg Fp.hβ.1 _)
  calc C * (CSig ^ 2 * γstar ^ 2)
      = 1 * (γstar ^ 2 * CSig ^ 2 * lipConst f₁ * lipConst f₂ *
          opNorm Fm * opNorm Gm * Fp.β ^ ℓ) := by simp [C]; ring
    _ ≤ Real.sqrt 2 * (γstar ^ 2 * CSig ^ 2 * lipConst f₁ * lipConst f₂ *
          opNorm Fm * opNorm Gm * Fp.β ^ ℓ) := mul_le_mul_of_nonneg_right hsqrt hrest
    _ = _ := by ring

/-- Coordinator bridge (no source label), snapshot `cr-2026-10-23`. Geometric lag envelope for general filters,
deterministic form: for odd, bounded, Lipschitz `f₁, f₂` and diagonal tests, at a fixed dimension under the size
conditions, `|𝔑_ℓ[F,G](f₁,f₂)| ≤ √2 γ⋆² C_Σ² Lip(f₁) Lip(f₂) ‖F‖ ‖G‖ β^ℓ` for every `ℓ ∈ ℕ` (conjunct 1),
so the lag series of `|𝔑_ℓ[F,G](f₁,f₂)|` is summable (conjunct 2). This is `thm_app_vol_integrated_ii` and
`eqn:app-pl-envelope` with `Lip(f₁) Lip(f₂)` in place of the ridge constant, uniform in the dimension. Source:
the proof of `lem:app-pl-pieces` (`sections/06-power-law/section.tex` l.1855–1856) and the proof of
`thm:app-vol-integrated`(ii) (`sections/04-volatility/section.tex`), verbatim:
```latex
nonnegative; the coupling of \cref{lem:app-pl-two-ridge}, with $\operatorname{Lip}(f)$
in place of $\ridge^{-1/2}$, gives the geometric lag envelope,
```
```latex
For (ii), the bounds of \cref{thm:app-vol-lag-reduction}(ii) for the
independent model hold at every order $N$ and pass to the limit.
```
Proof route: as `p5_unit_lag_bound`. Normalize the tests (`p3_normalize`, `p3_cut_scale`/`p3_lag_scale` style
scaling through `thm_app_vol_lag_kernel_bilinear_bound_replication`(b)). Along the replications `p5_repl_seq`
(same `β`, `SizeFin` with the same `γ⋆, C_Σ`, `opNorm` of `replMat` at most that of the base,
`tx_replMat_opNorm_le`), `lag_closure_generic` gives `𝔼 𝒦 → 𝔑_ℓ` at replicated tests, replication invariance
(`thm_app_vol_lag_kernel_bilinear_bound_replication`(d)) identifies the limit with the base `lagResp`, and
`lag_envelope_generic_indep` bounds every term uniformly. Conjunct 2: conjunct 1 with
`Fm := S.uOut * diagonal Fd * S.uOutᵀ` and `summable_geometric_of_lt_one` (`Fp.hβ`). -/
theorem lag_envelope_generic (cert : Muon.External.GaussianOpNorm) (γstar CSig : ℝ)
    {m n B : ℕ} (Fp : FrozenParams m n B) (S : SpectralData Fp.C) (hS : SizeFin Fp.C B γstar CSig)
    (hCSig : 1 ≤ CSig) (f₁ f₂ : ℝ → ℝ) (hf₁ : IsOddBddLip f₁) (hf₂ : IsOddBddLip f₂) :
    (∀ (ℓ : ℕ) (Fm : Mat m m) (Gm : Mat n n) (Fd : Fin m → ℝ) (Gd : Fin n → ℝ),
      Fm = S.uOut * Matrix.diagonal Fd * S.uOutᵀ → Gm = S.vIn * Matrix.diagonal Gd * S.vInᵀ →
      |lagResp cert γstar CSig Fp.β ℓ B S.μ S.lam Fd Gd f₁ f₂| ≤
        Real.sqrt 2 * γstar ^ 2 * CSig ^ 2 * lipConst f₁ * lipConst f₂ *
          opNorm Fm * opNorm Gm * Fp.β ^ ℓ) ∧
    (∀ (Fd : Fin m → ℝ) (Gd : Fin n → ℝ),
      Summable (fun ℓ : ℕ => |lagResp cert γstar CSig Fp.β ℓ B S.μ S.lam Fd Gd f₁ f₂|)) := by
  have hL₁ : 0 ≤ lipConst f₁ := tx_lip_nonneg f₁
  have hL₂ : 0 ≤ lipConst f₂ := tx_lip_nonneg f₂
  have hunit : ∀ (ℓ : ℕ) (Fd : Fin m → ℝ) (Gd : Fin n → ℝ),
      opNorm (S.uOut * Matrix.diagonal Fd * S.uOutᵀ) ≤ 1 →
      opNorm (S.vIn * Matrix.diagonal Gd * S.vInᵀ) ≤ 1 →
      |lagResp cert γstar CSig Fp.β ℓ B S.μ S.lam Fd Gd f₁ f₂| ≤
        Real.sqrt 2 * γstar ^ 2 * CSig ^ 2 * lipConst f₁ * lipConst f₂ * Fp.β ^ ℓ := by
    intro ℓ Fd Gd hF hG
    obtain ⟨rF, Sp, hSz, hβ, hμ, hlam, hUF, hVG⟩ := p5_repl_seq Fp S γstar CSig hS
    have hclo := lag_closure_generic cert γstar CSig ((m : ℝ) / B) ((n : ℝ) / B) hCSig
      (fun k ↦ (k + 1) * m) (fun k ↦ (k + 1) * n) (fun k ↦ (k + 1) * B) rF Sp hSz
      Fp.β Fp.hβ.2 (fun k ↦ (hβ k).le) ℓ f₁ f₂ hf₁ hf₂
    refine le_of_forall_pos_le_add fun ε hε ↦ ?_
    obtain ⟨k, hk⟩ := (hclo ε hε).exists
    have hF1 : opNorm ((Sp k).uOut * Matrix.diagonal (replVec (k + 1) Fd) * (Sp k).uOutᵀ) ≤ 1 := by
      rw [hUF k]
      exact (tx_replMat_opNorm_le _).trans hF
    have hG1 : opNorm ((Sp k).vIn * Matrix.diagonal (replVec (k + 1) Gd) * (Sp k).vInᵀ) ≤ 1 := by
      rw [hVG k]
      exact (tx_replMat_opNorm_le _).trans hG
    have key := hk 0 (replVec (k + 1) Fd) (replVec (k + 1) Gd) _ _ rfl rfl hF1 hG1
    have hw : lagResp cert γstar CSig (rF k).β ℓ ((k + 1) * B) (Sp k).μ (Sp k).lam
        (replVec (k + 1) Fd) (replVec (k + 1) Gd) f₁ f₂ =
        lagResp cert γstar CSig Fp.β ℓ B S.μ S.lam Fd Gd f₁ f₂ := by
      rw [hβ k, hμ k, hlam k]
      exact (thm_app_vol_lag_kernel_bilinear_bound_replication cert γstar CSig Fp S hS hCSig ℓ
        f₁ f₂ hf₁ hf₂).2.2.2.2.2 (k + 1) (Nat.succ_pos k) Fd Gd
    rw [hw] at key
    have hb := lag_envelope_generic_indep (rF k) γstar CSig (hSz.1 k) f₁ f₂ hf₁ hf₂
      ((Sp k).uOut * Matrix.diagonal (replVec (k + 1) Fd) * (Sp k).uOutᵀ)
      ((Sp k).vIn * Matrix.diagonal (replVec (k + 1) Gd) * (Sp k).vInᵀ) 0 ℓ
    rw [hβ k] at hb
    let K : ℝ := Real.sqrt 2 * γstar ^ 2 * CSig ^ 2 * lipConst f₁ * lipConst f₂ * Fp.β ^ ℓ
    have hK : 0 ≤ K := by
      dsimp [K]
      exact mul_nonneg
        (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (sq_nonneg _))
          (sq_nonneg _)) hL₁) hL₂) (pow_nonneg Fp.hβ.1 _)
    have hop : opNorm ((Sp k).uOut * Matrix.diagonal (replVec (k + 1) Fd) * (Sp k).uOutᵀ) *
        opNorm ((Sp k).vIn * Matrix.diagonal (replVec (k + 1) Gd) * (Sp k).vInᵀ) ≤ 1 := by
      nlinarith [tx_opNorm_nonneg ((Sp k).uOut * Matrix.diagonal (replVec (k + 1) Fd) * (Sp k).uOutᵀ),
        tx_opNorm_nonneg ((Sp k).vIn * Matrix.diagonal (replVec (k + 1) Gd) * (Sp k).vInᵀ)]
    have hb' : |∫ ω, contraction ((k + 1) * B)
        ((Sp k).uOut * Matrix.diagonal (replVec (k + 1) Fd) * (Sp k).uOutᵀ)
        ((Sp k).vIn * Matrix.diagonal (replVec (k + 1) Gd) * (Sp k).vInᵀ) f₁ f₂
        (def_app_vol_product (rF k) ω 0) (def_app_vol_product (rF k) ω (0 + (ℓ : ℤ)))
        ∂(indepSpaceLaw ((k + 1) * m) ((k + 1) * n) ((k + 1) * B))| ≤ K := by
      refine hb.trans ?_
      have hm := mul_le_mul_of_nonneg_left hop hK
      dsimp [K] at hm ⊢
      convert hm using 1 <;> ring
    have ht := abs_sub_abs_le_abs_sub
      (lagResp cert γstar CSig Fp.β ℓ B S.μ S.lam Fd Gd f₁ f₂)
      (∫ ω, contraction ((k + 1) * B)
        ((Sp k).uOut * Matrix.diagonal (replVec (k + 1) Fd) * (Sp k).uOutᵀ)
        ((Sp k).vIn * Matrix.diagonal (replVec (k + 1) Gd) * (Sp k).vInᵀ) f₁ f₂
        (def_app_vol_product (rF k) ω 0) (def_app_vol_product (rF k) ω (0 + (ℓ : ℤ)))
        ∂(indepSpaceLaw ((k + 1) * m) ((k + 1) * n) ((k + 1) * B)))
    rw [abs_sub_comm] at ht
    dsimp [K] at hb' ⊢
    linarith
  have hmain : ∀ (ℓ : ℕ) (Fm : Mat m m) (Gm : Mat n n) (Fd : Fin m → ℝ) (Gd : Fin n → ℝ),
      Fm = S.uOut * Matrix.diagonal Fd * S.uOutᵀ → Gm = S.vIn * Matrix.diagonal Gd * S.vInᵀ →
      |lagResp cert γstar CSig Fp.β ℓ B S.μ S.lam Fd Gd f₁ f₂| ≤
        Real.sqrt 2 * γstar ^ 2 * CSig ^ 2 * lipConst f₁ * lipConst f₂ *
          opNorm Fm * opNorm Gm * Fp.β ^ ℓ := by
    intro ℓ Fm Gm Fd Gd hFm hGm
    subst Fm
    subst Gm
    obtain ⟨F, hF, hFn⟩ := p3_normalize S.uOut S.huOut Fd
    obtain ⟨G, hG, hGn⟩ := p3_normalize S.vIn S.hvIn Gd
    have hu := hunit ℓ F G hFn hGn
    have hs := mul_le_mul_of_nonneg_left hu
      (mul_nonneg (tx_opNorm_nonneg (S.uOut * Matrix.diagonal Fd * S.uOutᵀ))
        (tx_opNorm_nonneg (S.vIn * Matrix.diagonal Gd * S.vInᵀ)))
    conv_lhs =>
      rw [hF, hG, p3_lag_scale cert γstar CSig Fp S hS hCSig ℓ _ _ F G f₁ f₂ hf₁ hf₂]
    rw [abs_mul, abs_mul, abs_of_nonneg (tx_opNorm_nonneg _),
      abs_of_nonneg (tx_opNorm_nonneg _)]
    convert hs using 1 <;> ring
  refine ⟨hmain, ?_⟩
  intro Fd Gd
  let Fm := S.uOut * Matrix.diagonal Fd * S.uOutᵀ
  let Gm := S.vIn * Matrix.diagonal Gd * S.vInᵀ
  let K : ℝ := Real.sqrt 2 * γstar ^ 2 * CSig ^ 2 * lipConst f₁ * lipConst f₂ *
    opNorm Fm * opNorm Gm
  have hgeo : Summable (fun ℓ : ℕ ↦ Fp.β ^ ℓ) := summable_geometric_of_lt_one Fp.hβ.1 Fp.hβ.2
  refine Summable.of_norm_bounded (hgeo.mul_left K) fun ℓ ↦ ?_
  rw [Real.norm_eq_abs, abs_of_nonneg (abs_nonneg _)]
  have hb := hmain ℓ Fm Gm Fd Gd rfl rfl
  dsimp [K]
  exact hb

private lemma pd20_shift_product {m n B : ℕ} (F : FrozenParams m n B) (s s' : ℤ)
    (Ψ : Mat m n → Mat m n → ℝ) :
    ∫ ω, Ψ (def_app_vol_product F ω s) (def_app_vol_product F ω s') ∂(indepSpaceLaw m n B) =
    ∫ ω, Ψ (def_app_vol_product F ω 0) (def_app_vol_product F ω (s' - s))
      ∂(indepSpaceLaw m n B) := by
  let e : (ℤ × Fin B) ≃ (ℤ × Fin B) := Equiv.prodCongr (Equiv.addRight s) (Equiv.refl _)
  let σ : ((ℤ × Fin B) → ℝ × (Vec m × Vec n)) ≃ᵐ
      ((ℤ × Fin B) → ℝ × (Vec m × Vec n)) :=
    MeasurableEquiv.piCongrLeft (fun _ : ℤ × Fin B => ℝ × (Vec m × Vec n)) e.symm
  have hmap : (indepSpaceLaw m n B).map σ = indepSpaceLaw m n B := by
    unfold indepSpaceLaw
    exact Measure.infinitePi_map_piCongrLeft
      (μ := fun _ : ℤ × Fin B => indepSlotLaw m n) e.symm
  have hσ : MeasurePreserving σ (indepSpaceLaw m n B) (indepSpaceLaw m n B) :=
    ⟨σ.measurable, hmap⟩
  have hprod : ∀ r ω, def_app_vol_product F ω r =
      def_app_vol_product F (σ ω) (r - s) := by
    intro r ω
    have hσω : ∀ p : ℤ × Fin B, σ ω p = ω (e p) := fun p => by
      simp [σ, MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply]
    unfold def_app_vol_product indepBatchG
    refine tsum_congr fun j => ?_
    congr 2
    refine Finset.sum_congr rfl fun a _ => ?_
    have ht : r - s + 1 - (j : ℤ) + s = r + 1 - (j : ℤ) := by ring
    simp only [hσω, e, Equiv.prodCongr_apply, Prod.map_apply, Equiv.coe_addRight,
      Equiv.refl_apply, ht]
  calc
    _ = ∫ ω, Ψ (def_app_vol_product F (σ ω) 0)
        (def_app_vol_product F (σ ω) (s' - s)) ∂(indepSpaceLaw m n B) := by
      exact integral_congr_ae (Filter.Eventually.of_forall fun ω => by
        change Ψ (def_app_vol_product F ω s) (def_app_vol_product F ω s') =
          Ψ (def_app_vol_product F (σ ω) 0)
            (def_app_vol_product F (σ ω) (s' - s))
        rw [hprod s ω, hprod s' ω]
        simp)
    _ = _ := hσ.integral_comp' (f := σ)
      (g := fun ω => Ψ (def_app_vol_product F ω 0)
        (def_app_vol_product F ω (s' - s)))

private lemma pd20_trace_symm {m n : ℕ} (F : Mat m m) (G : Mat n n)
    (hF : F.transpose = F) (hG : G.transpose = G) (X Y : Mat m n) :
    Matrix.trace (F * X * G * Yᵀ) = Matrix.trace (F * Y * G * Xᵀ) := by
  have h1 : Matrix.trace (F * X * G * Yᵀ) = Matrix.trace ((F * X * G * Yᵀ)ᵀ) :=
    (Matrix.trace_transpose _).symm
  have h2 : (F * X * G * Yᵀ)ᵀ = Y * G * Xᵀ * F := by
    simp [Matrix.transpose_mul, hF, hG, Matrix.mul_assoc]
  rw [h1, h2, Matrix.trace_mul_comm]
  simp [Matrix.mul_assoc]

private lemma pd20_Icc_sum (g : ℤ → ℝ) (T : ℕ) :
    ∑ s ∈ Finset.Icc (1 : ℤ) (T : ℤ), g s = ∑ a ∈ Finset.range T, g ((a : ℤ) + 1) := by
  have h : Finset.Icc (1 : ℤ) (T : ℤ) =
      (Finset.range T).image (fun a : ℕ => (a : ℤ) + 1) := by
    ext x
    simp only [Finset.mem_Icc, Finset.mem_image, Finset.mem_range]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨(x - 1).toNat, by omega, by omega⟩
    · rintro ⟨a, ha, rfl⟩
      omega
  rw [h, Finset.sum_image (fun a _ b _ hab => by simpa using hab)]

private lemma pd20_count_aux (c : ℤ → ℝ) (T : ℕ) :
    ∑ a ∈ Finset.range T, ∑ b ∈ Finset.range T, c ((b : ℤ) - (a : ℤ)) =
      ∑ ℓ ∈ Finset.range T, ((T : ℝ) - ℓ) * (c ℓ + c (-(ℓ : ℤ))) - (T : ℝ) * c 0 := by
  induction T with
  | zero => simp
  | succ T ih =>
    have e1 : ∑ a ∈ Finset.range (T + 1), ∑ b ∈ Finset.range (T + 1),
        c ((b : ℤ) - (a : ℤ)) =
        ∑ a ∈ Finset.range T, ∑ b ∈ Finset.range T, c ((b : ℤ) - (a : ℤ)) +
        ∑ a ∈ Finset.range T, c ((T : ℤ) - (a : ℤ)) +
        ∑ b ∈ Finset.range T, c ((b : ℤ) - (T : ℤ)) + c 0 := by
      rw [Finset.sum_range_succ]
      simp only [Finset.sum_range_succ, Finset.sum_add_distrib]
      simp
      ring
    have r1 : ∑ a ∈ Finset.range T, c ((T : ℤ) - (a : ℤ)) =
        ∑ ℓ ∈ Finset.range (T + 1), c (ℓ : ℤ) - c 0 := by
      rw [Finset.sum_range_succ', ← Finset.sum_range_reflect]
      simp only [Nat.cast_zero]
      have h : ∀ j ∈ Finset.range T,
          c ((T : ℤ) - ((T - 1 - j : ℕ) : ℤ)) = c (((j + 1 : ℕ)) : ℤ) := by
        intro j hj
        rw [Finset.mem_range] at hj
        congr 1
        omega
      rw [Finset.sum_congr rfl h]
      ring
    have r2 : ∑ b ∈ Finset.range T, c ((b : ℤ) - (T : ℤ)) =
        ∑ ℓ ∈ Finset.range (T + 1), c (-(ℓ : ℤ)) - c 0 := by
      rw [Finset.sum_range_succ', ← Finset.sum_range_reflect]
      simp only [Nat.cast_zero, neg_zero]
      have h : ∀ j ∈ Finset.range T,
          c (((T - 1 - j : ℕ) : ℤ) - (T : ℤ)) = c (-(((j + 1 : ℕ)) : ℤ)) := by
        intro j hj
        rw [Finset.mem_range] at hj
        congr 1
        omega
      rw [Finset.sum_congr rfl h]
      ring
    have e3 : ∑ ℓ ∈ Finset.range (T + 1),
        (((T + 1 : ℕ) : ℝ) - ℓ) * (c ℓ + c (-(ℓ : ℤ))) =
        ∑ ℓ ∈ Finset.range T, ((T : ℝ) - ℓ) * (c ℓ + c (-(ℓ : ℤ))) +
        ∑ ℓ ∈ Finset.range (T + 1), (c (ℓ : ℤ) + c (-(ℓ : ℤ))) := by
      have h : ∀ ℓ ∈ Finset.range T,
          (((T + 1 : ℕ) : ℝ) - ℓ) * (c ℓ + c (-(ℓ : ℤ))) =
          ((T : ℝ) - ℓ) * (c ℓ + c (-(ℓ : ℤ))) + (c ℓ + c (-(ℓ : ℤ))) := by
        intro ℓ _
        push_cast
        ring
      rw [Finset.sum_range_succ, Finset.sum_congr rfl h, Finset.sum_add_distrib,
        Finset.sum_range_succ (fun ℓ : ℕ => c (ℓ : ℤ) + c (-(ℓ : ℤ))) T]
      push_cast
      ring
    rw [e1, ih, r1, r2, e3]
    simp only [Finset.sum_add_distrib]
    push_cast
    ring

private lemma pd20_count (c : ℤ → ℝ) (T : ℕ) (hT : 1 ≤ T) :
    ∑ s ∈ Finset.Icc (1 : ℤ) (T : ℤ), ∑ s' ∈ Finset.Icc (1 : ℤ) (T : ℤ), c (s' - s) =
      (T : ℝ) * c 0 + ∑ ℓ ∈ Finset.Ico 1 T,
        ((T : ℝ) - ℓ) * (c ℓ + c (-(ℓ : ℤ))) := by
  rw [pd20_Icc_sum (fun s => ∑ s' ∈ Finset.Icc (1 : ℤ) (T : ℤ), c (s' - s)) T]
  simp only [pd20_Icc_sum (fun s' => c (s' - _)) T]
  have h : ∀ a ∈ Finset.range T,
      ∑ b ∈ Finset.range T, c (((b : ℤ) + 1) - ((a : ℤ) + 1)) =
      ∑ b ∈ Finset.range T, c ((b : ℤ) - (a : ℤ)) := by
    intro a _
    refine Finset.sum_congr rfl fun b _ => ?_
    congr 1
    ring
  rw [Finset.sum_congr rfl h, pd20_count_aux,
    Finset.sum_range_eq_add_Ico _ (by omega : 0 < T)]
  simp
  ring

private lemma pd20_trace_integrable {m n B : ℕ} (F : FrozenParams m n B)
    (f : ℝ → ℝ) (hf : IsOddBddLip f) (Fm : Mat m m) (Gm : Mat n n) (s s' : ℤ) :
    Integrable (fun ω => Matrix.trace (Fm * oddSharp f (def_app_vol_product F ω s) * Gm *
      (oddSharp f (def_app_vol_product F ω s'))ᵀ)) (indepSpaceLaw m n B) := by
  haveI := lge_prob m n B
  have hm := lge_trace_meas Fm Gm _ _
    ((lge_sharp_cont f hf).measurable.comp (lge_prod_meas F s))
    ((lge_sharp_cont f hf).measurable.comp (lge_prod_meas F s'))
  let q : ℝ := Real.sqrt ((min m n : ℕ) : ℝ) * supNorm f
  let C : ℝ := opNorm Fm * q * opNorm Gm * q
  refine Integrable.of_bound (C := |C|) hm.aestronglyMeasurable
    (Filter.Eventually.of_forall fun ω => ?_)
  rw [Real.norm_eq_abs]
  refine (lge_trace_le Fm Gm _ _).trans ?_
  have hx := (lem_app_vol_sharp_i f hf (def_app_vol_product F ω s)
    (def_app_vol_product F ω s)).2.1
  have hy := (lem_app_vol_sharp_i f hf (def_app_vol_product F ω s')
    (def_app_vol_product F ω s')).2.1
  have hq : 0 ≤ q := mul_nonneg (Real.sqrt_nonneg _) (tx_supNorm_nonneg f)
  calc
    opNorm Fm * fro (oddSharp f (def_app_vol_product F ω s)) * opNorm Gm *
        fro (oddSharp f (def_app_vol_product F ω s')) ≤
        opNorm Fm * q * opNorm Gm * fro (oddSharp f (def_app_vol_product F ω s')) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hx (tx_opNorm_nonneg Fm)) (tx_opNorm_nonneg Gm))
        (lge_fro_nn _)
    _ ≤ C := by
      dsimp [C]
      exact mul_le_mul_of_nonneg_left hy
        (mul_nonneg (mul_nonneg (tx_opNorm_nonneg Fm) hq) (tx_opNorm_nonneg Gm))
    _ ≤ |C| := le_abs_self C

private lemma pd20_finite_identity {m n B : ℕ} (F : FrozenParams m n B)
    (f : ℝ → ℝ) (hf : IsOddBddLip f) (Fm : Mat m m) (Gm : Mat n n)
    (hFs : Fm.transpose = Fm) (hGs : Gm.transpose = Gm) (T : ℕ) (hT : 1 ≤ T) :
    ((B : ℝ) * (T : ℝ))⁻¹ * ∫ ω, Matrix.trace (Fm *
        (∑ s ∈ Finset.Icc (1 : ℤ) (T : ℤ), oddSharp f (def_app_vol_product F ω s)) * Gm *
        (∑ s ∈ Finset.Icc (1 : ℤ) (T : ℤ), oddSharp f (def_app_vol_product F ω s))ᵀ)
          ∂(indepSpaceLaw m n B) =
      (∫ ω, contraction B Fm Gm f f (def_app_vol_product F ω 0)
        (def_app_vol_product F ω 0) ∂(indepSpaceLaw m n B)) +
      ∑ ℓ ∈ Finset.Ico 1 T, (1 - (ℓ : ℝ) / (T : ℝ)) *
        (2 * ∫ ω, contraction B Fm Gm f f (def_app_vol_product F ω 0)
          (def_app_vol_product F ω (ℓ : ℤ)) ∂(indepSpaceLaw m n B)) := by
  have hBpos : (0 : ℝ) < B := by exact_mod_cast F.hB
  have hTpos : (0 : ℝ) < T := by exact_mod_cast hT
  have hexp : ∀ ω, Matrix.trace (Fm *
        (∑ s ∈ Finset.Icc (1 : ℤ) (T : ℤ), oddSharp f (def_app_vol_product F ω s)) * Gm *
        (∑ s ∈ Finset.Icc (1 : ℤ) (T : ℤ), oddSharp f (def_app_vol_product F ω s))ᵀ) =
      ∑ s ∈ Finset.Icc (1 : ℤ) (T : ℤ), ∑ s' ∈ Finset.Icc (1 : ℤ) (T : ℤ),
        Matrix.trace (Fm * oddSharp f (def_app_vol_product F ω s) * Gm *
          (oddSharp f (def_app_vol_product F ω s'))ᵀ) := by
    intro ω
    simp only [Matrix.transpose_sum, Matrix.mul_sum, Matrix.sum_mul, Matrix.trace_sum]
    exact Finset.sum_comm
  let c : ℤ → ℝ := fun d => ∫ ω, Matrix.trace
    (Fm * oddSharp f (def_app_vol_product F ω 0) * Gm *
      (oddSharp f (def_app_vol_product F ω d))ᵀ) ∂(indepSpaceLaw m n B)
  have hpair : ∀ s s' : ℤ, ∫ ω, Matrix.trace
      (Fm * oddSharp f (def_app_vol_product F ω s) * Gm *
        (oddSharp f (def_app_vol_product F ω s'))ᵀ) ∂(indepSpaceLaw m n B) = c (s' - s) := by
    intro s s'
    exact pd20_shift_product F s s'
      (fun X Y => Matrix.trace (Fm * oddSharp f X * Gm * (oddSharp f Y)ᵀ))
  have hcp : ∀ ℓ : ℕ, c (ℓ : ℤ) = (B : ℝ) *
      ∫ ω, contraction B Fm Gm f f (def_app_vol_product F ω 0)
        (def_app_vol_product F ω (ℓ : ℤ)) ∂(indepSpaceLaw m n B) := by
    intro ℓ
    dsimp [c]
    unfold contraction
    rw [integral_const_mul]
    field_simp
  have hcn : ∀ ℓ : ℕ, c (-(ℓ : ℤ)) = (B : ℝ) *
      ∫ ω, contraction B Fm Gm f f (def_app_vol_product F ω 0)
        (def_app_vol_product F ω (ℓ : ℤ)) ∂(indepSpaceLaw m n B) := by
    intro ℓ
    have h1 : c (-(ℓ : ℤ)) = ∫ ω, Matrix.trace
        (Fm * oddSharp f (def_app_vol_product F ω (-(ℓ : ℤ))) * Gm *
          (oddSharp f (def_app_vol_product F ω 0))ᵀ) ∂(indepSpaceLaw m n B) := by
      dsimp [c]
      exact integral_congr_ae (Filter.Eventually.of_forall fun ω =>
        pd20_trace_symm Fm Gm hFs hGs _ _)
    rw [h1, pd20_shift_product F (-(ℓ : ℤ)) 0
      (fun X Y => Matrix.trace (Fm * oddSharp f X * Gm * (oddSharp f Y)ᵀ))]
    have he : (0 : ℤ) - -(ℓ : ℤ) = (ℓ : ℤ) := by omega
    rw [he]
    unfold contraction
    rw [integral_const_mul]
    field_simp
  have hmain : ((B : ℝ) * (T : ℝ))⁻¹ * ∫ ω, Matrix.trace (Fm *
        (∑ s ∈ Finset.Icc (1 : ℤ) (T : ℤ), oddSharp f (def_app_vol_product F ω s)) * Gm *
        (∑ s ∈ Finset.Icc (1 : ℤ) (T : ℤ), oddSharp f (def_app_vol_product F ω s))ᵀ)
          ∂(indepSpaceLaw m n B) =
      ((B : ℝ) * (T : ℝ))⁻¹ * ∑ s ∈ Finset.Icc (1 : ℤ) (T : ℤ),
        ∑ s' ∈ Finset.Icc (1 : ℤ) (T : ℤ), c (s' - s) := by
    congr 1
    simp_rw [hexp]
    rw [integral_finset_sum _ (fun s _ => integrable_finset_sum _ fun s' _ =>
      pd20_trace_integrable F f hf Fm Gm s s')]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [integral_finset_sum _ (fun s' _ => pd20_trace_integrable F f hf Fm Gm s s')]
    exact Finset.sum_congr rfl fun s' _ => hpair s s'
  rw [hmain, pd20_count c T hT]
  rw [mul_add (((B : ℝ) * (T : ℝ))⁻¹), Finset.mul_sum]
  have hterm : ∀ ℓ ∈ Finset.Ico 1 T,
      ((B : ℝ) * (T : ℝ))⁻¹ * (((T : ℝ) - ℓ) * (c ℓ + c (-(ℓ : ℤ)))) =
      (1 - (ℓ : ℝ) / (T : ℝ)) *
        (2 * ∫ ω, contraction B Fm Gm f f (def_app_vol_product F ω 0)
          (def_app_vol_product F ω (ℓ : ℤ)) ∂(indepSpaceLaw m n B)) := by
    intro ℓ _
    rw [hcp ℓ, hcn ℓ]
    field_simp
    ring
  rw [Finset.sum_congr rfl hterm]
  congr 1
  have h0 := hcp 0
  simp only [Nat.cast_zero] at h0
  rw [h0]
  field_simp

private lemma pd20_core (c : ℕ → ℝ) (M β : ℝ) (hM : 0 ≤ M) (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (hc : ∀ ℓ : ℕ, 1 ≤ ℓ → |c ℓ| ≤ M * β ^ ℓ) (T : ℕ) (hT : 1 ≤ T) (a0 : ℝ) :
    |(a0 + ∑' ℓ : ℕ, c (ℓ + 1)) -
      (a0 + ∑ ℓ ∈ Finset.Ico 1 T, (1 - (ℓ : ℝ) / (T : ℝ)) * c ℓ)| ≤
      M * (β ^ T / (1 - β) + β / ((T : ℝ) * (1 - β) ^ 2)) := by
  obtain ⟨T', rfl⟩ : ∃ T', T = T' + 1 := ⟨T - 1, by omega⟩
  push_cast
  have hr : ‖β‖ < 1 := by rw [Real.norm_eq_abs, abs_of_nonneg hβ0]; exact hβ1
  have hgeo : Summable (fun n : ℕ => β ^ n) := summable_geometric_of_lt_one hβ0 hβ1
  have hgeo1 : Summable (fun n : ℕ => β ^ (n + 1)) := (summable_nat_add_iff 1).mpr hgeo
  have hsl : Summable (fun n : ℕ => (n : ℝ) * β ^ n) := by
    simpa using summable_pow_mul_geometric_of_norm_lt_one 1 hr
  have hsumg : Summable (fun j : ℕ => c (j + 1)) :=
    Summable.of_norm_bounded (hgeo1.mul_left M) (fun j => by
      rw [Real.norm_eq_abs]; exact hc (j + 1) (by omega))
  have hsplit : ∑ j ∈ Finset.range T', c (j + 1) + ∑' i : ℕ, c (i + T' + 1) =
      ∑' j : ℕ, c (j + 1) := hsumg.sum_add_tsum_nat_add T'
  have hIco : ∑ j ∈ Finset.range T', c (j + 1) = ∑ ℓ ∈ Finset.Ico 1 (T' + 1), c ℓ := by
    rw [Finset.sum_Ico_eq_sum_range]
    simp only [Nat.add_sub_cancel]
    exact Finset.sum_congr rfl fun j _ => by rw [add_comm]
  have hb : Summable (fun j : ℕ => M * β ^ (j + T' + 1)) := by
    have h1 : Summable (fun j : ℕ => β ^ (j + (T' + 1))) :=
      (summable_nat_add_iff (T' + 1)).mpr hgeo
    have h2 : Summable (fun j : ℕ => β ^ (j + T' + 1)) := by
      simpa only [add_assoc] using h1
    exact h2.mul_left M
  have hab : Summable (fun j : ℕ => |c (j + T' + 1)|) :=
    Summable.of_nonneg_of_le (fun j => abs_nonneg _) (fun j => hc _ (by omega)) hb
  have htail : |∑' j : ℕ, c (j + T' + 1)| ≤ M * β ^ (T' + 1) / (1 - β) := by
    have hab' : Summable (fun j : ℕ => ‖c (j + T' + 1)‖) := by
      simpa only [Real.norm_eq_abs] using hab
    have e1 := norm_tsum_le_tsum_norm hab'
    have e2 : ∑' j : ℕ, |c (j + T' + 1)| ≤ ∑' j : ℕ, M * β ^ (j + T' + 1) :=
      Summable.tsum_le_tsum (fun j => hc (j + T' + 1) (by omega)) hab hb
    have e3 : ∑' j : ℕ, M * β ^ (j + T' + 1) = M * β ^ (T' + 1) / (1 - β) := by
      have h : (fun j : ℕ => M * β ^ (j + T' + 1)) =
          fun j => (M * β ^ (T' + 1)) * β ^ j := funext fun j => by ring
      rw [h, tsum_mul_left, tsum_geometric_of_lt_one hβ0 hβ1, div_eq_mul_inv]
    simp only [Real.norm_eq_abs] at e1
    linarith
  have hW1 : |∑ ℓ ∈ Finset.Ico 1 (T' + 1), ((ℓ : ℝ) / ((T' : ℝ) + 1)) * c ℓ| ≤
      ∑ ℓ ∈ Finset.Ico 1 (T' + 1), (M / ((T' : ℝ) + 1)) * ((ℓ : ℝ) * β ^ ℓ) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun ℓ hℓ => ?_)
    have hℓ1 : 1 ≤ ℓ := (Finset.mem_Ico.mp hℓ).1
    have hnn : (0 : ℝ) ≤ (ℓ : ℝ) / ((T' : ℝ) + 1) := by positivity
    rw [abs_mul, abs_of_nonneg hnn]
    calc
      (ℓ : ℝ) / ((T' : ℝ) + 1) * |c ℓ| ≤
          (ℓ : ℝ) / ((T' : ℝ) + 1) * (M * β ^ ℓ) :=
        mul_le_mul_of_nonneg_left (hc ℓ hℓ1) hnn
      _ = (M / ((T' : ℝ) + 1)) * ((ℓ : ℝ) * β ^ ℓ) := by ring
  have hW2 : ∑ ℓ ∈ Finset.Ico 1 (T' + 1),
      (M / ((T' : ℝ) + 1)) * ((ℓ : ℝ) * β ^ ℓ) ≤
      M / ((T' : ℝ) + 1) * (β / (1 - β) ^ 2) := by
    have h := Summable.sum_le_tsum (Finset.Ico 1 (T' + 1))
      (fun ℓ _ => mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hβ0 _)) hsl
    rw [tsum_coe_mul_geometric_of_norm_lt_one hr] at h
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left h (div_nonneg hM (by positivity))
  have hid : ∑ ℓ ∈ Finset.Ico 1 (T' + 1),
      (1 - (ℓ : ℝ) / ((T' : ℝ) + 1)) * c ℓ =
      ∑ ℓ ∈ Finset.Ico 1 (T' + 1), c ℓ -
        ∑ ℓ ∈ Finset.Ico 1 (T' + 1), ((ℓ : ℝ) / ((T' : ℝ) + 1)) * c ℓ := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun ℓ _ => by ring
  have key : (a0 + ∑' j : ℕ, c (j + 1)) -
      (a0 + ∑ ℓ ∈ Finset.Ico 1 (T' + 1),
        (1 - (ℓ : ℝ) / ((T' : ℝ) + 1)) * c ℓ) =
      ∑' i : ℕ, c (i + T' + 1) + ∑ ℓ ∈ Finset.Ico 1 (T' + 1),
        ((ℓ : ℝ) / ((T' : ℝ) + 1)) * c ℓ := by
    rw [hid, ← hIco, ← hsplit]
    ring
  rw [key]
  calc
    _ ≤ |∑' i : ℕ, c (i + T' + 1)| +
        |∑ ℓ ∈ Finset.Ico 1 (T' + 1), ((ℓ : ℝ) / ((T' : ℝ) + 1)) * c ℓ| :=
      abs_add_le _ _
    _ ≤ M * β ^ (T' + 1) / (1 - β) +
        M / ((T' : ℝ) + 1) * (β / (1 - β) ^ 2) := add_le_add htail (hW1.trans hW2)
    _ = M * (β ^ (T' + 1) / (1 - β) +
        β / (((T' : ℝ) + 1) * (1 - β) ^ 2)) := by field_simp

/-- Coordinator bridge (no source label), snapshot `cr-2026-10-23`. Finite-time sums for a general filter,
independent model at a fixed dimension. For an odd, bounded, Lipschitz `f`, positive semidefinite tests `F, G`
and `S_T = ∑_{s=1}^T f^♯(M^g_s)`, with `c_ℓ = 𝔼 𝒦^{F,G}[f,f](M^g_0, M^g_ℓ)`:
(1) the finite-time sums `(BT)⁻¹ 𝔼 Tr[F S_T G S_Tᵀ]` are nonnegative for every `T` (at `T = 0` the prefactor
is `0`); (2) `∑_ℓ |c_ℓ|` converges; (3) the finite-time sums converge, as `T → ∞`, to the independent integrated
covariance `c_0 + ∑_{ℓ≥1} 2 c_ℓ`; (4) hence that limit is nonnegative. Source: the proof of `lem:app-pl-pieces`
(`sections/06-power-law/section.tex` l.1853–1857), verbatim:
```latex
$a,b$ the filter $f\defeq af_I+bf_J$ has, in the independent model along the
replications, row covariances whose finite-time sums
$\frac1{nT}\sum_k\EE\norm{\sum_{t'\le T}f^\sharp(M^{\mathrm g}_{t'})^\T(u_i\tensor e_k)}^2$ are
nonnegative; the coupling of \cref{lem:app-pl-two-ridge}, with $\operatorname{Lip}(f)$
in place of $\ridge^{-1/2}$, gives the geometric lag envelope, so these sums converge
to the integrated covariance as in the proof of
\cref{thm:app-vol-integrated}(iii).
```
and the proof of `thm:app-vol-integrated`(iii) (`sections/04-volatility/section.tex` l.1406–1410), verbatim:
```latex
For (iii), absolute convergence follows from (ii). For positive
semidefinite $F,G$ and every $T$, the left side of \cref{eqn:app-vol-finite-time}
for the independent model is nonnegative, since
$\Tr[FSGS^\T]=\norm{F^{1/2}SG^{1/2}}_\F^2$; by \cref{thm:app-vol-lag-reduction}(iii)
the independent integrated coefficient $\Gamma^{\mathrm g,(N)}[F,G](\ridge,\ridge)$ is
nonnegative at every order.
```
Proof route: (1) pointwise `p5_tr_nonneg` and `integral_nonneg`. (2) `lag_envelope_generic_indep` at `t = 0`
and `summable_geometric_of_lt_one`. (3) as `thm_app_vol_lag_reduction_i`/`_iii_bound` for the independent
model: expand the double sum (the integrand is bounded, `lem_app_vol_sharp_i`), use stationarity of the slot
law under time shifts (`Measure.infinitePi` is shift invariant) and the symmetry
`Tr[F X G Yᵀ] = Tr[F Y G Xᵀ]` for symmetric `F, G` to get `c_0 + ∑_{ℓ<T} (1 - ℓ/T) 2 c_ℓ`, then the envelope
and the error `2K(β^T/(1-β) + β/(T(1-β)²))` (`p5_err_tendsto`). (4) `ge_of_tendsto` from (1) and (3). -/
theorem finite_time_generic_indep {m n B : ℕ} (Fp : FrozenParams m n B) (γstar CSig : ℝ)
    (hS : SizeFin Fp.C B γstar CSig) (f : ℝ → ℝ) (hf : IsOddBddLip f)
    (Fm : Mat m m) (Gm : Mat n n) (hF : Fm.PosSemidef) (hG : Gm.PosSemidef) :
    (∀ T : ℕ, 0 ≤ ((B : ℝ) * (T : ℝ))⁻¹ * ∫ ω, Matrix.trace (Fm *
        (∑ s ∈ Finset.Icc (1 : ℤ) (T : ℤ), oddSharp f (def_app_vol_product Fp ω s)) * Gm *
        (∑ s ∈ Finset.Icc (1 : ℤ) (T : ℤ), oddSharp f (def_app_vol_product Fp ω s))ᵀ)
          ∂(indepSpaceLaw m n B)) ∧
    Summable (fun ℓ : ℕ => |∫ ω, contraction B Fm Gm f f (def_app_vol_product Fp ω 0)
        (def_app_vol_product Fp ω (ℓ : ℤ)) ∂(indepSpaceLaw m n B)|) ∧
    Tendsto (fun T : ℕ => ((B : ℝ) * (T : ℝ))⁻¹ * ∫ ω, Matrix.trace (Fm *
        (∑ s ∈ Finset.Icc (1 : ℤ) (T : ℤ), oddSharp f (def_app_vol_product Fp ω s)) * Gm *
        (∑ s ∈ Finset.Icc (1 : ℤ) (T : ℤ), oddSharp f (def_app_vol_product Fp ω s))ᵀ)
          ∂(indepSpaceLaw m n B)) atTop
      (𝓝 ((∫ ω, contraction B Fm Gm f f (def_app_vol_product Fp ω 0)
          (def_app_vol_product Fp ω 0) ∂(indepSpaceLaw m n B)) +
        ∑' ℓ : ℕ, 2 * ∫ ω, contraction B Fm Gm f f (def_app_vol_product Fp ω 0)
          (def_app_vol_product Fp ω ((ℓ + 1 : ℕ) : ℤ)) ∂(indepSpaceLaw m n B))) ∧
    0 ≤ (∫ ω, contraction B Fm Gm f f (def_app_vol_product Fp ω 0)
          (def_app_vol_product Fp ω 0) ∂(indepSpaceLaw m n B)) +
        ∑' ℓ : ℕ, 2 * ∫ ω, contraction B Fm Gm f f (def_app_vol_product Fp ω 0)
          (def_app_vol_product Fp ω ((ℓ + 1 : ℕ) : ℤ)) ∂(indepSpaceLaw m n B) := by
  let c : ℕ → ℝ := fun ℓ => ∫ ω, contraction B Fm Gm f f
    (def_app_vol_product Fp ω 0) (def_app_vol_product Fp ω (ℓ : ℤ))
      ∂(indepSpaceLaw m n B)
  let K : ℝ := Real.sqrt 2 * γstar ^ 2 * CSig ^ 2 * lipConst f * lipConst f *
    opNorm Fm * opNorm Gm
  have hK : 0 ≤ K := by
    dsimp [K]
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg
          (mul_nonneg
            (mul_nonneg
              (mul_nonneg (Real.sqrt_nonneg _) (sq_nonneg _)) (sq_nonneg _))
            (tx_lip_nonneg f)) (tx_lip_nonneg f))
        (tx_opNorm_nonneg Fm)) (tx_opNorm_nonneg Gm)
  have henv : ∀ ℓ : ℕ, |c ℓ| ≤ K * Fp.β ^ ℓ := by
    intro ℓ
    simpa only [c, K, zero_add] using
      lag_envelope_generic_indep Fp γstar CSig hS f f hf hf Fm Gm 0 ℓ
  have hfin : ∀ T : ℕ, 0 ≤ ((B : ℝ) * (T : ℝ))⁻¹ * ∫ ω, Matrix.trace (Fm *
      (∑ s ∈ Finset.Icc (1 : ℤ) (T : ℤ), oddSharp f (def_app_vol_product Fp ω s)) * Gm *
      (∑ s ∈ Finset.Icc (1 : ℤ) (T : ℤ), oddSharp f (def_app_vol_product Fp ω s))ᵀ)
        ∂(indepSpaceLaw m n B) := by
    intro T
    refine mul_nonneg (inv_nonneg.mpr (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))) ?_
    exact integral_nonneg fun ω => p5_tr_nonneg Fm Gm hF hG _
  have hsum : Summable (fun ℓ : ℕ => |c ℓ|) := by
    have hgeo : Summable (fun ℓ : ℕ => Fp.β ^ ℓ) :=
      summable_geometric_of_lt_one Fp.hβ.1 Fp.hβ.2
    refine Summable.of_norm_bounded (hgeo.mul_left K) fun ℓ => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (abs_nonneg _)]
    exact henv ℓ
  have hFs : Fm.transpose = Fm := by
    rw [← Matrix.conjTranspose_eq_transpose_of_trivial]
    exact hF.1
  have hGs : Gm.transpose = Gm := by
    rw [← Matrix.conjTranspose_eq_transpose_of_trivial]
    exact hG.1
  have hid : ∀ T : ℕ, 1 ≤ T →
      ((B : ℝ) * (T : ℝ))⁻¹ * ∫ ω, Matrix.trace (Fm *
          (∑ s ∈ Finset.Icc (1 : ℤ) (T : ℤ), oddSharp f (def_app_vol_product Fp ω s)) * Gm *
          (∑ s ∈ Finset.Icc (1 : ℤ) (T : ℤ), oddSharp f (def_app_vol_product Fp ω s))ᵀ)
            ∂(indepSpaceLaw m n B) =
        c 0 + ∑ ℓ ∈ Finset.Ico 1 T, (1 - (ℓ : ℝ) / (T : ℝ)) * (2 * c ℓ) := by
    intro T hT
    exact pd20_finite_identity Fp f hf Fm Gm hFs hGs T hT
  have hc2 : ∀ ℓ : ℕ, 1 ≤ ℓ → |2 * c ℓ| ≤ 2 * K * Fp.β ^ ℓ := by
    intro ℓ _
    rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    convert mul_le_mul_of_nonneg_left (henv ℓ) (show (0 : ℝ) ≤ 2 by norm_num) using 1 <;>
      ring
  have hconv : Tendsto (fun T : ℕ => ((B : ℝ) * (T : ℝ))⁻¹ * ∫ ω, Matrix.trace (Fm *
      (∑ s ∈ Finset.Icc (1 : ℤ) (T : ℤ), oddSharp f (def_app_vol_product Fp ω s)) * Gm *
      (∑ s ∈ Finset.Icc (1 : ℤ) (T : ℤ), oddSharp f (def_app_vol_product Fp ω s))ᵀ)
        ∂(indepSpaceLaw m n B)) atTop (𝓝 (c 0 + ∑' ℓ : ℕ, 2 * c (ℓ + 1))) := by
    refine tendsto_iff_dist_tendsto_zero.mpr (squeeze_zero'
      (Filter.Eventually.of_forall fun _ => dist_nonneg) ?_
      (p5_err_tendsto K Fp.β Fp.hβ.1 Fp.hβ.2))
    filter_upwards [eventually_ge_atTop 1] with T hT
    rw [Real.dist_eq, hid T hT, abs_sub_comm]
    exact pd20_core (fun ℓ => 2 * c ℓ) (2 * K) Fp.β (mul_nonneg (by norm_num) hK)
      Fp.hβ.1 Fp.hβ.2 hc2 T hT (c 0)
  have hnon : 0 ≤ c 0 + ∑' ℓ : ℕ, 2 * c (ℓ + 1) :=
    ge_of_tendsto hconv (Filter.Eventually.of_forall hfin)
  simpa only [c, Nat.cast_zero] using And.intro hfin (And.intro hsum (And.intro hconv hnon))

private lemma pd20_gamma_scale (cert : Muon.External.GaussianOpNorm) (γstar CSig : ℝ)
    {m n B : ℕ} (Fp : FrozenParams m n B) (S : SpectralData Fp.C)
    (hS : SizeFin Fp.C B γstar CSig) (hCSig : 1 ≤ CSig) (c d : ℝ)
    (Fd : Fin m → ℝ) (Gd : Fin n → ℝ) (f : ℝ → ℝ) (hf : IsOddBddLip f) :
    lagGammaGen cert γstar CSig Fp.β B S.μ S.lam (c • Fd) (d • Gd) f f =
      c * d * lagGammaGen cert γstar CSig Fp.β B S.μ S.lam Fd Gd f f := by
  have hlag : ∀ ℓ : ℕ, lagResp cert γstar CSig Fp.β ℓ B S.μ S.lam
      (c • Fd) (d • Gd) f f =
      c * d * lagResp cert γstar CSig Fp.β ℓ B S.μ S.lam Fd Gd f f := fun ℓ =>
    p3_lag_scale cert γstar CSig Fp S hS hCSig ℓ c d Fd Gd f f hf hf
  unfold lagGammaGen
  simp only [hlag]
  rw [mul_add, ← tsum_mul_left]
  congr 1
  exact tsum_congr fun ℓ => by ring

private lemma pd20_gamma_unit (cert : Muon.External.GaussianOpNorm) (γstar CSig : ℝ)
    {m n B : ℕ} (Fp : FrozenParams m n B) (S : SpectralData Fp.C)
    (hS : SizeFin Fp.C B γstar CSig) (hCSig : 1 ≤ CSig) (f : ℝ → ℝ)
    (hf : IsOddBddLip f) (Fd : Fin m → ℝ) (Gd : Fin n → ℝ)
    (hFd : ∀ i, 0 ≤ Fd i) (hGd : ∀ j, 0 ≤ Gd j)
    (hF1 : opNorm (S.uOut * Matrix.diagonal Fd * S.uOutᵀ) ≤ 1)
    (hG1 : opNorm (S.vIn * Matrix.diagonal Gd * S.vInᵀ) ≤ 1) :
    0 ≤ lagGammaGen cert γstar CSig Fp.β B S.μ S.lam Fd Gd f f := by
  obtain ⟨rF, Sp, hSz, hβ, hμ, hlam, hUF, hVG⟩ := p5_repl_seq Fp S γstar CSig hS
  let Fm : ∀ k : ℕ, Mat ((k + 1) * m) ((k + 1) * m) := fun k =>
    (Sp k).uOut * Matrix.diagonal (replVec (k + 1) Fd) * (Sp k).uOutᵀ
  let Gm : ∀ k : ℕ, Mat ((k + 1) * n) ((k + 1) * n) := fun k =>
    (Sp k).vIn * Matrix.diagonal (replVec (k + 1) Gd) * (Sp k).vInᵀ
  have hFn : ∀ k, opNorm (Fm k) ≤ 1 := by
    intro k
    dsimp [Fm]
    rw [hUF k]
    exact (tx_replMat_opNorm_le _).trans hF1
  have hGn : ∀ k, opNorm (Gm k) ≤ 1 := by
    intro k
    dsimp [Gm]
    rw [hVG k]
    exact (tx_replMat_opNorm_le _).trans hG1
  let Cf : ℕ → ℕ → ℝ := fun k ℓ => ∫ ω, contraction ((k + 1) * B) (Fm k) (Gm k) f f
    (def_app_vol_product (rF k) ω 0) (def_app_vol_product (rF k) ω (ℓ : ℤ))
      ∂(indepSpaceLaw ((k + 1) * m) ((k + 1) * n) ((k + 1) * B))
  let Lf : ℕ → ℝ := fun ℓ =>
    lagResp cert γstar CSig Fp.β ℓ B S.μ S.lam Fd Gd f f
  have hnn : ∀ k, 0 ≤ Cf k 0 + ∑' ℓ : ℕ, 2 * Cf k (ℓ + 1) := by
    intro k
    have hpsdF : (Fm k).PosSemidef := by
      dsimp [Fm]
      exact p5_psd_diag _ _ (fun i => hFd _)
    have hpsdG : (Gm k).PosSemidef := by
      dsimp [Gm]
      exact p5_psd_diag _ _ (fun j => hGd _)
    exact (finite_time_generic_indep (rF k) γstar CSig (hSz.1 k) f hf
      (Fm k) (Gm k) hpsdF hpsdG).2.2.2
  have hrepl := fun ℓ : ℕ =>
    (thm_app_vol_lag_kernel_bilinear_bound_replication cert γstar CSig Fp S hS hCSig
      ℓ f f hf hf).2.2.2.2.2
  have hraw : ∀ ℓ : ℕ, ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, |Cf k ℓ - Lf ℓ| ≤ ε := by
    intro ℓ ε hε
    have hclo := lag_closure_generic cert γstar CSig ((m : ℝ) / B) ((n : ℝ) / B) hCSig
      (fun k ↦ (k + 1) * m) (fun k ↦ (k + 1) * n) (fun k ↦ (k + 1) * B)
      rF Sp hSz Fp.β Fp.hβ.2 (fun k ↦ (hβ k).le) ℓ f f hf hf
    filter_upwards [hclo ε hε] with k hk
    have key := hk 0 (replVec (k + 1) Fd) (replVec (k + 1) Gd) (Fm k) (Gm k)
      rfl rfl (hFn k) (hGn k)
    have hw : lagResp cert γstar CSig (rF k).β ℓ ((k + 1) * B) (Sp k).μ (Sp k).lam
        (replVec (k + 1) Fd) (replVec (k + 1) Gd) f f = Lf ℓ := by
      dsimp [Lf]
      rw [hβ k, hμ k, hlam k]
      exact hrepl ℓ (k + 1) (Nat.succ_pos k) Fd Gd
    rw [hw] at key
    simpa only [Cf, zero_add] using key
  let K : ℝ := Real.sqrt 2 * γstar ^ 2 * CSig ^ 2 * lipConst f * lipConst f
  have hK : 0 ≤ K := by
    dsimp [K]
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (sq_nonneg _)) (sq_nonneg _))
          (tx_lip_nonneg f)) (tx_lip_nonneg f)
  have hCenv : ∀ k ℓ, |Cf k ℓ| ≤ K * Fp.β ^ ℓ := by
    intro k ℓ
    have hb := lag_envelope_generic_indep (rF k) γstar CSig (hSz.1 k) f f hf hf
      (Fm k) (Gm k) 0 ℓ
    rw [hβ k] at hb
    have hb' : |Cf k ℓ| ≤ K * opNorm (Fm k) * opNorm (Gm k) * Fp.β ^ ℓ := by
      simpa only [Cf, K, zero_add] using hb
    have hop : K * opNorm (Fm k) * opNorm (Gm k) ≤ K := by
      calc
        K * opNorm (Fm k) * opNorm (Gm k) ≤ K * 1 * opNorm (Gm k) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hFn k) hK)
            (tx_opNorm_nonneg (Gm k))
        _ ≤ K * 1 * 1 := mul_le_mul_of_nonneg_left (hGn k) (mul_nonneg hK zero_le_one)
        _ = K := by ring
    exact hb'.trans (mul_le_mul_of_nonneg_right hop (pow_nonneg Fp.hβ.1 ℓ))
  have hLenv : ∀ ℓ, |Lf ℓ| ≤ K * Fp.β ^ ℓ := by
    intro ℓ
    have hb := (lag_envelope_generic cert γstar CSig Fp S hS hCSig f f hf hf).1
      ℓ _ _ Fd Gd rfl rfl
    have hb' : |Lf ℓ| ≤ K * opNorm (S.uOut * Matrix.diagonal Fd * S.uOutᵀ) *
        opNorm (S.vIn * Matrix.diagonal Gd * S.vInᵀ) * Fp.β ^ ℓ := by
      simpa only [Lf, K] using hb
    have hop : K * opNorm (S.uOut * Matrix.diagonal Fd * S.uOutᵀ) *
        opNorm (S.vIn * Matrix.diagonal Gd * S.vInᵀ) ≤ K := by
      calc
        _ ≤ K * 1 * opNorm (S.vIn * Matrix.diagonal Gd * S.vInᵀ) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hF1 hK)
            (tx_opNorm_nonneg _)
        _ ≤ K * 1 * 1 := mul_le_mul_of_nonneg_left hG1 (mul_nonneg hK zero_le_one)
        _ = K := by ring
    exact hb'.trans (mul_le_mul_of_nonneg_right hop (pow_nonneg Fp.hβ.1 ℓ))
  let a : ∀ k : ℕ, ℕ → Unit → ℝ := fun k ℓ _ => if ℓ = 0 then Cf k 0 else 2 * Cf k ℓ
  let b : ∀ k : ℕ, ℕ → Unit → ℝ := fun _ ℓ _ => if ℓ = 0 then Lf 0 else 2 * Lf ℓ
  have hbd : ∀ k, ∀ p ∈ (fun _ : ℕ => (Set.univ : Set Unit)) k, ∀ ℓ : ℕ, 1 ≤ ℓ →
      |a k ℓ p| + |b k ℓ p| ≤ 4 * K * Fp.β ^ ℓ := by
    intro k p _ ℓ hℓ
    have hn : ℓ ≠ 0 := by omega
    have h1 := hCenv k ℓ
    have h2 := hLenv ℓ
    simp only [a, b, hn, if_false, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    nlinarith
  have hlim : ∀ ℓ : ℕ, ∀ ε > 0, ∀ᶠ k in atTop, ∀ p ∈ (Set.univ : Set Unit),
      |a k ℓ p - b k ℓ p| ≤ ε := by
    intro ℓ ε hε
    rcases ℓ with _ | ℓ
    · filter_upwards [hraw 0 ε hε] with k hk p _
      simpa [a, b] using hk
    · filter_upwards [hraw (ℓ + 1) (ε / 2) (by positivity)] with k hk p _
      simp only [a, b, Nat.succ_ne_zero, if_false, ← mul_sub, abs_mul,
        abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      linarith
  have hsum := p6_lagsum_dep (fun _ : ℕ => (Set.univ : Set Unit)) a b (4 * K) Fp.β
    Fp.hβ hbd hlim
  have hΓ : lagGammaGen cert γstar CSig Fp.β B S.μ S.lam Fd Gd f f =
      Lf 0 + ∑' ℓ : ℕ, 2 * Lf (ℓ + 1) := by
    unfold lagGammaGen
    dsimp [Lf]
    congr 1
    exact tsum_congr fun ℓ => by ring
  refine le_of_forall_pos_le_add fun ε hε => ?_
  obtain ⟨k, hk⟩ := (hsum ε hε).exists
  have hd := hk () (Set.mem_univ _)
  have hd' : |(Cf k 0 + ∑' ℓ : ℕ, 2 * Cf k (ℓ + 1)) -
      (Lf 0 + ∑' ℓ : ℕ, 2 * Lf (ℓ + 1))| ≤ ε := by
    simpa [a, b] using hd
  rw [hΓ]
  have hu := (abs_le.mp hd').2
  linarith [hnn k]

/-- Coordinator bridge (no source label), snapshot `cr-2026-10-23`. Convergence and nonnegativity of the integrated
response of a single general filter: for an odd, bounded, Lipschitz `f` and diagonal tests with nonnegative
entries (equivalently, positive semidefinite diagonal tests), at a fixed dimension under the size conditions,
`∑_{ℓ≥1} |𝔑_ℓ[F,G](f,f)|` converges and `Γ̄[F,G](f,f) = 𝔑_0 + ∑_{ℓ≥1} 2 𝔑_ℓ ≥ 0` (`lagGammaGen`). This is
`thm_app_vol_integrated_iii` with `f` in place of `ω_ϱ`; the tests are given by their diagonal entries, so that
the row test `u_i ⊗ u_i, Id` of `sec:app-pl` is `Fd = Pi.single i 1`, `Gd = 1`. Source: the proof of
`lem:app-pl-pieces` (`sections/06-power-law/section.tex` l.1853–1862), verbatim:
```latex
$a,b$ the filter $f\defeq af_I+bf_J$ has, in the independent model along the
replications, row covariances whose finite-time sums
$\frac1{nT}\sum_k\EE\norm{\sum_{t'\le T}f^\sharp(M^{\mathrm g}_{t'})^\T(u_i\tensor e_k)}^2$ are
nonnegative; the coupling of \cref{lem:app-pl-two-ridge}, with $\operatorname{Lip}(f)$
in place of $\ridge^{-1/2}$, gives the geometric lag envelope, so these sums converge
to the integrated covariance as in the proof of
\cref{thm:app-vol-integrated}(iii).
```
and the proof of `thm:app-vol-integrated`(iii) (`sections/04-volatility/section.tex` l.1410–1412), verbatim:
```latex
nonnegative at every order. \Cref{lem:app-vol-lagsum}, with the fixed-lag
convergence $C^{\mathrm g,(N)}_\ell\to\overline C_\ell$ as $N\to\infty$ and the envelopes of
(ii), gives $\Gamma^{\mathrm g,(N)}\to\overline\Gamma$, which is therefore nonnegative.
```
Proof route: summability is `lag_envelope_generic` (conjunct 2, shifted by one). For nonnegativity, as
`p5_gamma_nonneg_unit` but in the independent model: normalize the tests (`p3_normalize`, nonnegativity of the
entries is kept, `p5_gamma_scale` style scaling); along `p5_repl_seq` the replicated tests are positive
semidefinite (`p5_psd_diag`), so `finite_time_generic_indep`(4) gives `0 ≤ Γ^{g,(k)}`; `lag_closure_generic` with
replication invariance (`thm_app_vol_lag_kernel_bilinear_bound_replication`(d)) gives `c^{(k)}_ℓ → 𝔑_ℓ` at every
fixed `ℓ`, and `lag_envelope_generic_indep` is a uniform envelope, so `p6_lagsum_dep` gives
`Γ^{g,(k)} → lagGammaGen … f f`; conclude with `ge_of_tendsto`. -/
theorem lag_gamma_generic_nonneg (cert : Muon.External.GaussianOpNorm) (γstar CSig : ℝ)
    {m n B : ℕ} (Fp : FrozenParams m n B) (S : SpectralData Fp.C) (hS : SizeFin Fp.C B γstar CSig)
    (hCSig : 1 ≤ CSig) (f : ℝ → ℝ) (hf : IsOddBddLip f)
    (Fd : Fin m → ℝ) (Gd : Fin n → ℝ) (hFd : ∀ i, 0 ≤ Fd i) (hGd : ∀ j, 0 ≤ Gd j) :
    Summable (fun ℓ : ℕ => |lagResp cert γstar CSig Fp.β (ℓ + 1) B S.μ S.lam Fd Gd f f|) ∧
      0 ≤ lagGammaGen cert γstar CSig Fp.β B S.μ S.lam Fd Gd f f := by
  have hs0 := (lag_envelope_generic cert γstar CSig Fp S hS hCSig f f hf hf).2 Fd Gd
  have hs : Summable (fun ℓ : ℕ =>
      |lagResp cert γstar CSig Fp.β (ℓ + 1) B S.μ S.lam Fd Gd f f|) :=
    (summable_nat_add_iff 1).mpr hs0
  refine ⟨hs, ?_⟩
  obtain ⟨e1, he1, hn1⟩ := p3_normalize S.uOut S.huOut Fd
  obtain ⟨e2, he2, hn2⟩ := p3_normalize S.vIn S.hvIn Gd
  let a := opNorm (S.uOut * Matrix.diagonal Fd * S.uOutᵀ)
  let b := opNorm (S.vIn * Matrix.diagonal Gd * S.vInᵀ)
  have ha : 0 ≤ a := tx_opNorm_nonneg _
  have hb : 0 ≤ b := tx_opNorm_nonneg _
  have hscale := pd20_gamma_scale cert γstar CSig Fp S hS hCSig a b e1 e2 f hf
  rw [← he1, ← he2] at hscale
  rw [hscale]
  rcases ha.eq_or_lt with ha0 | ha0
  · rw [← ha0]
    simp
  rcases hb.eq_or_lt with hb0 | hb0
  · rw [← hb0]
    simp
  have he10 : ∀ i, 0 ≤ e1 i := by
    intro i
    have hi := congrFun he1 i
    simp only [Pi.smul_apply, smul_eq_mul] at hi
    have h0 := hFd i
    rw [hi] at h0
    exact nonneg_of_mul_nonneg_right h0 ha0
  have he20 : ∀ j, 0 ≤ e2 j := by
    intro j
    have hj := congrFun he2 j
    simp only [Pi.smul_apply, smul_eq_mul] at hj
    have h0 := hGd j
    rw [hj] at h0
    exact nonneg_of_mul_nonneg_right h0 hb0
  exact mul_nonneg (mul_nonneg ha hb)
    (pd20_gamma_unit cert γstar CSig Fp S hS hCSig f hf e1 e2 he10 he20 hn1 hn2)

private lemma pd20_zero_filter : IsOddBddLip (fun _ : ℝ => 0) := by
  refine ⟨?_, ⟨0, ?_⟩, ⟨0, ?_⟩⟩ <;> simp

private lemma pd20_lag_scale_left (cert : Muon.External.GaussianOpNorm) (γstar CSig : ℝ)
    {m n B : ℕ} (Fp : FrozenParams m n B) (S : SpectralData Fp.C)
    (hS : SizeFin Fp.C B γstar CSig) (hCSig : 1 ≤ CSig) (ℓ : ℕ)
    (f g : ℝ → ℝ) (hf : IsOddBddLip f) (hg : IsOddBddLip g) (c : ℝ)
    (Fd : Fin m → ℝ) (Gd : Fin n → ℝ) :
    lagResp cert γstar CSig Fp.β ℓ B S.μ S.lam Fd Gd (fun x => c * f x) g =
      c * lagResp cert γstar CSig Fp.β ℓ B S.μ S.lam Fd Gd f g := by
  have hlin :=
    (thm_app_vol_lag_kernel_bilinear_bound_replication cert γstar CSig Fp S hS hCSig
      ℓ (fun _ : ℝ => 0) g pd20_zero_filter hg).2.2.2.1
  have hz := hlin 1 (fun _ : ℝ => 0) pd20_zero_filter Fd Gd
  have hz' : lagResp cert γstar CSig Fp.β ℓ B S.μ S.lam Fd Gd (fun _ : ℝ => 0) g = 0 := by
    simp only [zero_add, one_mul] at hz
    linarith
  have hc := hlin c f hf Fd Gd
  simp only [zero_add, hz'] at hc
  exact hc

private lemma pd20_lag_scale_right (cert : Muon.External.GaussianOpNorm) (γstar CSig : ℝ)
    {m n B : ℕ} (Fp : FrozenParams m n B) (S : SpectralData Fp.C)
    (hS : SizeFin Fp.C B γstar CSig) (hCSig : 1 ≤ CSig) (ℓ : ℕ)
    (f g : ℝ → ℝ) (hf : IsOddBddLip f) (hg : IsOddBddLip g) (c : ℝ)
    (Fd : Fin m → ℝ) (Gd : Fin n → ℝ) :
    lagResp cert γstar CSig Fp.β ℓ B S.μ S.lam Fd Gd f (fun x => c * g x) =
      c * lagResp cert γstar CSig Fp.β ℓ B S.μ S.lam Fd Gd f g := by
  have hlin :=
    (thm_app_vol_lag_kernel_bilinear_bound_replication cert γstar CSig Fp S hS hCSig
      ℓ f (fun _ : ℝ => 0) hf pd20_zero_filter).2.2.2.2.1
  have hz := hlin 1 (fun _ : ℝ => 0) pd20_zero_filter Fd Gd
  have hz' : lagResp cert γstar CSig Fp.β ℓ B S.μ S.lam Fd Gd f (fun _ : ℝ => 0) = 0 := by
    simp only [zero_add, one_mul] at hz
    linarith
  have hc := hlin c g hg Fd Gd
  simp only [zero_add, hz'] at hc
  exact hc

private lemma pd20_lag_filter_quadratic (cert : Muon.External.GaussianOpNorm) (γstar CSig : ℝ)
    {m n B : ℕ} (Fp : FrozenParams m n B) (S : SpectralData Fp.C)
    (hS : SizeFin Fp.C B γstar CSig) (hCSig : 1 ≤ CSig) (ℓ : ℕ)
    (g h : ℝ → ℝ) (hg : IsOddBddLip g) (hh : IsOddBddLip h) (a b : ℝ)
    (Fd : Fin m → ℝ) (Gd : Fin n → ℝ) :
    lagResp cert γstar CSig Fp.β ℓ B S.μ S.lam Fd Gd
        (fun x => a * g x + b * h x) (fun x => a * g x + b * h x) =
      a ^ 2 * lagResp cert γstar CSig Fp.β ℓ B S.μ S.lam Fd Gd g g +
        a * b * (lagResp cert γstar CSig Fp.β ℓ B S.μ S.lam Fd Gd g h +
          lagResp cert γstar CSig Fp.β ℓ B S.μ S.lam Fd Gd h g) +
        b ^ 2 * lagResp cert γstar CSig Fp.β ℓ B S.μ S.lam Fd Gd h h := by
  have hag : IsOddBddLip (fun x => a * g x) := by
    simpa only [zero_add] using p3_add_filter (fun _ : ℝ => 0) g pd20_zero_filter hg a
  have hq : IsOddBddLip (fun x => a * g x + b * h x) := p3_add_filter _ _ hag hh b
  have hmain :=
    (thm_app_vol_lag_kernel_bilinear_bound_replication cert γstar CSig Fp S hS hCSig
      ℓ (fun x => a * g x) (fun x => a * g x + b * h x) hag hq).2.2.2.1
      b h hh Fd Gd
  have hagq :=
    (thm_app_vol_lag_kernel_bilinear_bound_replication cert γstar CSig Fp S hS hCSig
      ℓ (fun x => a * g x) (fun x => a * g x) hag hag).2.2.2.2.1
      b h hh Fd Gd
  have hhq :=
    (thm_app_vol_lag_kernel_bilinear_bound_replication cert γstar CSig Fp S hS hCSig
      ℓ h (fun x => a * g x) hh hag).2.2.2.2.1 b h hh Fd Gd
  have haa := pd20_lag_scale_left cert γstar CSig Fp S hS hCSig ℓ g
    (fun x => a * g x) hg hag a Fd Gd
  have hga := pd20_lag_scale_right cert γstar CSig Fp S hS hCSig ℓ g g hg hg a Fd Gd
  have hagh := pd20_lag_scale_left cert γstar CSig Fp S hS hCSig ℓ g h hg hh a Fd Gd
  have hhag := pd20_lag_scale_right cert γstar CSig Fp S hS hCSig ℓ h g hh hg a Fd Gd
  rw [hmain, hagq, hhq, haa, hga, hagh, hhag]
  ring

private lemma pd20_tsum_quadratic (a b : ℝ) (x y z w : ℕ → ℝ)
    (hx : Summable x) (hy : Summable y) (hz : Summable z) (hw : Summable w) :
    (∑' q, ((a ^ 2 * x q + a * b * (y q + z q) + b ^ 2 * w q) +
      (a ^ 2 * x q + a * b * (y q + z q) + b ^ 2 * w q))) =
      a ^ 2 * (∑' q, (x q + x q)) +
        a * b * ((∑' q, (y q + z q)) + (∑' q, (z q + y q))) +
        b ^ 2 * (∑' q, (w q + w q)) := by
  have hpoint : ∀ q, ((a ^ 2 * x q + a * b * (y q + z q) + b ^ 2 * w q) +
      (a ^ 2 * x q + a * b * (y q + z q) + b ^ 2 * w q)) =
      a ^ 2 * (x q + x q) + a * b * ((y q + z q) + (z q + y q)) +
        b ^ 2 * (w q + w q) := fun q => by ring
  simp_rw [hpoint]
  rw [Summable.tsum_add (((hx.add hx).mul_left (a ^ 2)).add
        (((hy.add hz).add (hz.add hy)).mul_left (a * b)))
      ((hw.add hw).mul_left (b ^ 2)),
    Summable.tsum_add ((hx.add hx).mul_left (a ^ 2))
      (((hy.add hz).add (hz.add hy)).mul_left (a * b)),
    tsum_mul_left, tsum_mul_left, tsum_mul_left,
    Summable.tsum_add (hy.add hz) (hz.add hy), Summable.tsum_add hy hz,
    Summable.tsum_add hz hy]

/-- Coordinator bridge (no source label), snapshot `cr-2026-10-23`. Bilinear expansion of the integrated
response: for odd, bounded, Lipschitz `g, h` and real `a, b`,
`Γ̄(ag + bh, ag + bh) = a² Γ̄(g,g) + ab (Γ̄(g,h) + Γ̄(h,g)) + b² Γ̄(h,h)` (`lagGammaGen`), at a fixed dimension
under the size conditions and for any diagonal tests. Source: the proof of `lem:app-pl-pieces`
(`sections/06-power-law/section.tex` l.1859–1863), verbatim:
```latex
\cref{thm:app-vol-integrated}(iii). In the limit of the replications, the
integrated covariance of $f$ is, by bilinearity and the integral form of the
responses (proof of \cref{prop:app-pl-vol-zero}(iii)),
\[
a^2\mathfrak v_i[I,I]+2ab\,\mathfrak v_i[I,J]+b^2\mathfrak v_i[J,J]\ge0 .
\]
```
This is the "bilinearity" half; the "integral form of the responses", which identifies `B · lagGammaGen` at
`f_I, f_J` with `𝔳_i[I,J]`, is a `Muon.PowerLaw` fact and is not stated here. Proof route: the filter
linearity (c), (c') of `thm_app_vol_lag_kernel_bilinear_bound_replication`, with `𝔑_ℓ(0, ·) = 𝔑_ℓ(·, 0) = 0`
from its bound (a) (`supNorm 0 = 0`) to pass from `g + c h` to `a g + b h`, expands `𝔑_ℓ(ag+bh, ag+bh)` for
every `ℓ`; the four lag series are summable by `lag_envelope_generic`(2), so `tsum_add`/`tsum_mul_left` split
the series; finish with `ring`. -/
theorem lag_gamma_generic_quadratic (cert : Muon.External.GaussianOpNorm) (γstar CSig : ℝ)
    {m n B : ℕ} (Fp : FrozenParams m n B) (S : SpectralData Fp.C) (hS : SizeFin Fp.C B γstar CSig)
    (hCSig : 1 ≤ CSig) (g h : ℝ → ℝ) (hg : IsOddBddLip g) (hh : IsOddBddLip h) (a b : ℝ)
    (Fd : Fin m → ℝ) (Gd : Fin n → ℝ) :
    lagGammaGen cert γstar CSig Fp.β B S.μ S.lam Fd Gd (fun x => a * g x + b * h x)
        (fun x => a * g x + b * h x) =
      a ^ 2 * lagGammaGen cert γstar CSig Fp.β B S.μ S.lam Fd Gd g g +
        a * b * (lagGammaGen cert γstar CSig Fp.β B S.μ S.lam Fd Gd g h +
          lagGammaGen cert γstar CSig Fp.β B S.μ S.lam Fd Gd h g) +
        b ^ 2 * lagGammaGen cert γstar CSig Fp.β B S.μ S.lam Fd Gd h h := by
  let R : (ℝ → ℝ) → (ℝ → ℝ) → ℕ → ℝ := fun f₁ f₂ ℓ =>
    lagResp cert γstar CSig Fp.β ℓ B S.μ S.lam Fd Gd f₁ f₂
  let q : ℝ → ℝ := fun x => a * g x + b * h x
  have hquad : ∀ ℓ, R q q ℓ =
      a ^ 2 * R g g ℓ + a * b * (R g h ℓ + R h g ℓ) + b ^ 2 * R h h ℓ := by
    intro ℓ
    simpa only [R, q] using
      pd20_lag_filter_quadratic cert γstar CSig Fp S hS hCSig ℓ g h hg hh a b Fd Gd
  have hgg0 : Summable (fun ℓ => |R g g ℓ|) := by
    simpa only [R] using (lag_envelope_generic cert γstar CSig Fp S hS hCSig g g hg hg).2 Fd Gd
  have hgh0 : Summable (fun ℓ => |R g h ℓ|) := by
    simpa only [R] using (lag_envelope_generic cert γstar CSig Fp S hS hCSig g h hg hh).2 Fd Gd
  have hhg0 : Summable (fun ℓ => |R h g ℓ|) := by
    simpa only [R] using (lag_envelope_generic cert γstar CSig Fp S hS hCSig h g hh hg).2 Fd Gd
  have hhh0 : Summable (fun ℓ => |R h h ℓ|) := by
    simpa only [R] using (lag_envelope_generic cert γstar CSig Fp S hS hCSig h h hh hh).2 Fd Gd
  have hgg : Summable (fun ℓ => R g g (ℓ + 1)) :=
    (summable_nat_add_iff 1).mpr (summable_abs_iff.mp hgg0)
  have hgh : Summable (fun ℓ => R g h (ℓ + 1)) :=
    (summable_nat_add_iff 1).mpr (summable_abs_iff.mp hgh0)
  have hhg : Summable (fun ℓ => R h g (ℓ + 1)) :=
    (summable_nat_add_iff 1).mpr (summable_abs_iff.mp hhg0)
  have hhh : Summable (fun ℓ => R h h (ℓ + 1)) :=
    (summable_nat_add_iff 1).mpr (summable_abs_iff.mp hhh0)
  have hsum := pd20_tsum_quadratic a b (fun ℓ => R g g (ℓ + 1))
    (fun ℓ => R g h (ℓ + 1)) (fun ℓ => R h g (ℓ + 1))
    (fun ℓ => R h h (ℓ + 1)) hgg hgh hhg hhh
  unfold lagGammaGen
  change R q q 0 + (∑' ℓ, (R q q (ℓ + 1) + R q q (ℓ + 1))) =
    a ^ 2 * (R g g 0 + ∑' ℓ, (R g g (ℓ + 1) + R g g (ℓ + 1))) +
      a * b * ((R g h 0 + ∑' ℓ, (R g h (ℓ + 1) + R h g (ℓ + 1))) +
        (R h g 0 + ∑' ℓ, (R h g (ℓ + 1) + R g h (ℓ + 1)))) +
      b ^ 2 * (R h h 0 + ∑' ℓ, (R h h (ℓ + 1) + R h h (ℓ + 1)))
  rw [hquad 0, tsum_congr (fun ℓ => by rw [hquad (ℓ + 1)]), hsum]
  ring

/-! ## Lag reduction, part (iv): transfer to the independent model (work package L-D.10b)

`thm:app-vol-lag-reduction`(iv), snapshot `cr-2026-10-23` (`section.tex` l.866–894; proof l.966–970).
Parts (i)–(iii) are in `Muon.Volatility.LagReduction` (L-D.10a). Part (iv) is stated here, at the end
of this module, and not in `LagReduction.lean`: its proof uses `cor_app_vol_filtered_replacement_ii`
(`Muon.Volatility.Replacement`), the drift-mean sequence `ε_B` of `Muon.Drift.thm_app_drift_mean`
(imported through `Replacement`), `lem_app_vol_lagsum` and the envelopes
`thm_app_vol_lag_reduction_ii_actual`/`_ii_indep` (`LagReduction`), and this module is the lowest one
that imports both `LagReduction` and `Replacement`. No source statement uses (iv) (the proof of
`thm:app-vol-integrated`(iv) goes through the actual clause of `thm:app-vol-lag-kernel` instead), so
no consumer sits upstream of this placement.

Encoding decisions:
* Regime. `assum:app-setup-regime` is `R : SetupRegime` with samples `S k` on `P k`; the regime
  interval is `I = Set.Icc R.ϱlo R.ϱhi`. "`sup … → 0`" is read as
  `∀ ε > 0, ∀ᶠ k in atTop, ∀ (time, ridges, tests), |…| ≤ ε`, as in `lem_app_vol_lagsum`.
* The lag `ℓ` is fixed before `ε` ("for every fixed `ℓ ≥ 0`"). The time `t`, the ridges and the tests
  are chosen after the eventual index (the source's `C_ℓ` carry no time; (i)–(iii) are stated for
  every `t`).
* Tests: symmetric (`Fo.transpose = Fo`) with `opNorm ≤ 1`, as in (i)–(iii).
* `C^g_ℓ` is `indepLagCov` (the uncentred `B⁻¹ 𝔼 Tr[F S^g_t(ϱ) G S^g_{t+ℓ}(ϱ')ᵀ]` of
  `cor:app-vol-filtered-replacement`, written inline in `thm_app_vol_lag_reduction_ii_indep` and
  `cor_app_vol_filtered_replacement_ii`; equal to those inline forms by `rfl` up to `t + ((0 : ℕ) : ℤ)`
  at lag zero). `Γ^g` is `indepIntegratedLag`, the series `eqn:app-vol-Gamma` with `C^g_ℓ` in place of
  `C_ℓ`, mirroring `integratedLag`.
-/

/-- Independent tested lag covariance `C^g_ℓ[F,G](ϱ,ϱ') = B⁻¹ 𝔼 Tr[F S^g_t(ϱ) G S^g_{t+ℓ}(ϱ')ᵀ]`
(`cor:app-vol-filtered-replacement`, snapshot `cr-2026-10-23`), with `S^g = indepUpd` on
`indepSpaceLaw` (`def:app-vol-product`). Uncentred, as in the source (the independent updates have mean
zero). Helper for `thm:app-vol-lag-reduction`(iv); the argument order mirrors `def_app_vol_lag`. -/
def indepLagCov {m n B : ℕ} (F : FrozenParams m n B) (ℓ : ℕ) (t : ℤ) (Fo : Mat m m) (Gi : Mat n n)
    (ϱ ϱ' : ℝ) : ℝ :=
  ((B : ℝ))⁻¹ * ∫ ω, Matrix.trace (Fo * indepUpd F ϱ ω t * Gi *
    (indepUpd F ϱ' ω (t + (ℓ : ℤ)))ᵀ) ∂(indepSpaceLaw m n B)

/-- Independent integrated covariance `Γ^g[F,G](ϱ,ϱ') = C^g_0[F,G](ϱ,ϱ') + ∑_{ℓ≥1} (C^g_ℓ[F,G](ϱ,ϱ') +
C^g_ℓ[F,G](ϱ',ϱ))`: "the integrated sum of the `C^g_ℓ`" of `thm:app-vol-lag-reduction`(iv) (snapshot
`cr-2026-10-23`), defined as in `eqn:app-vol-Gamma` and mirroring `integratedLag`. The series is a
`tsum`; its absolute convergence under the size conditions follows from
`thm_app_vol_lag_reduction_ii_indep`. -/
def indepIntegratedLag {m n B : ℕ} (F : FrozenParams m n B) (t : ℤ) (Fo : Mat m m) (Gi : Mat n n)
    (ϱ ϱ' : ℝ) : ℝ :=
  indepLagCov F 0 t Fo Gi ϱ ϱ' +
    ∑' ℓ : ℕ, (indepLagCov F (ℓ + 1) t Fo Gi ϱ ϱ' + indepLagCov F (ℓ + 1) t Fo Gi ϱ' ϱ)

/-- `thm:app-vol-lag-reduction`, part (iv), fixed-lag clause (`_iv_lag`), snapshot `cr-2026-10-23`.
Declaration of record for the first statement of item (iv). The statement, verbatim from
`section.tex` (header and this part of the theorem):
```latex
\begin{theorem}[Lag reduction]\label{thm:app-vol-lag-reduction}
Under \cref{assum:app-setup-regime}, let $F,G$ be symmetric with
$\norm F,\norm G\le1$ and $\ridge,\ridge'\in I$.
\begin{enumerate}[label=(\roman*)]
\item For every fixed $\ell\ge0$,
$\sup_{\ridge,\ridge'\in I}\sup_{F,G}\abs{C_\ell[F,G]-C^{\mathrm g}_\ell[F,G]}\to0$, and
$\sup_{\ridge,\ridge'\in I}\sup_{F,G}\abs{\Gamma[F,G]-\Gamma^{\mathrm g}[F,G]}\to0$, where
$\Gamma^{\mathrm g}$ is the integrated sum of the $C^{\mathrm g}_\ell$ and the
suprema run over symmetric $F,G$ of norm at most one.
\end{enumerate}
\end{theorem}
```
The regime is `R : SetupRegime` with samples `S k` on `P k`, along `k → ∞`; `I = [R.ϱlo, R.ϱhi]`.
`C_ℓ` is `def_app_vol_lag` (centred) and `C^g_ℓ` is `indepLagCov` (uncentred, as in
`cor:app-vol-filtered-replacement`). The lag is fixed first; the eventual index is uniform in the time
`t`, the ridges `ϱ, ϱ' ∈ I` and the symmetric tests of operator norm at most one. Sorried: proof card
P1. -/
theorem thm_app_vol_lag_reduction_iv_lag (R : SetupRegime) (Ω : ℕ → Type)
    [∀ k, MeasurableSpace (Ω k)] (P : ∀ k, Measure (Ω k)) [∀ k, IsProbabilityMeasure (P k)]
    (S : ∀ k, FrozenSamples (P k) (R.m k) (R.n k) (R.B k)) (ℓ : ℕ) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, ∀ t : ℤ,
      ∀ ϱ ∈ Set.Icc R.ϱlo R.ϱhi, ∀ ϱ' ∈ Set.Icc R.ϱlo R.ϱhi,
      ∀ (Fo : Mat (R.m k) (R.m k)) (Gi : Mat (R.n k) (R.n k)),
        Fo.transpose = Fo → opNorm Fo ≤ 1 → Gi.transpose = Gi → opNorm Gi ≤ 1 →
        |def_app_vol_lag (R.F k) (S k) ℓ t Fo Gi ϱ ϱ' -
          indepLagCov (R.F k) ℓ t Fo Gi ϱ ϱ'| ≤ ε := by
  let εB : ℕ → ℝ := fun k => Muon.Drift.epsB (emaW R.β) (R.F k) (S k) 0
    (Muon.Drift.specOutFM (R.F k)) (Muon.Drift.specInFM (R.F k)) R.ϱlo R.ϱhi
  have hm := Muon.Drift.thm_app_drift_mean R P S 0
  have hεB : Tendsto εB atTop (𝓝 0) := hm.2.2.1
  have hmean : ∀ k, ∀ s : ℤ, ∀ ϱ ∈ Set.Icc R.ϱlo R.ϱhi,
      fro (Muon.mean (P k) (frozenUpd (R.F k) (S k) ϱ s)) ≤
        R.CSig / Real.sqrt R.ϱlo + εB k := by
    intro k s ϱ hϱ
    have he : fro (Muon.Drift.EQ (emaW R.β) (R.F k) (S k) 0 ϱ -
        Muon.Drift.Gbar (emaW R.β) (R.F k) (Muon.Drift.specOutFM (R.F k))
          (Muon.Drift.specInFM (R.F k)) ϱ) ≤ εB k := p4_le_biSup (hm.2.1 k) hϱ
    have hg := (hm.1 k ϱ hϱ).2
    have hsqrt : R.CSig / Real.sqrt ϱ ≤ R.CSig / Real.sqrt R.ϱlo :=
      div_le_div_of_nonneg_left (by linarith [R.hC]) (Real.sqrt_pos.mpr R.hϱ.1)
        (Real.sqrt_le_sqrt hϱ.1)
    have hadd := p4_fro_add
      (Muon.Drift.EQ (emaW R.β) (R.F k) (S k) 0 ϱ -
        Muon.Drift.Gbar (emaW R.β) (R.F k) (Muon.Drift.specOutFM (R.F k))
          (Muon.Drift.specInFM (R.F k)) ϱ)
      (Muon.Drift.Gbar (emaW R.β) (R.F k) (Muon.Drift.specOutFM (R.F k))
          (Muon.Drift.specInFM (R.F k)) ϱ)
    rw [sub_add_cancel] at hadd
    have heq : Muon.Drift.EQ (emaW R.β) (R.F k) (S k) 0 ϱ =
        Muon.mean (P k) (frozenUpd (R.F k) (S k) ϱ 0) := by
      unfold Muon.Drift.EQ
      congr 1
      funext ω
      unfold frozenUpd WeightedBuf frozenBuf
      rw [R.hβ k]
    rw [heq] at hadd he
    have hzero : fro (Muon.mean (P k) (frozenUpd (R.F k) (S k) ϱ 0)) ≤
        R.CSig / Real.sqrt R.ϱlo + εB k := by
      linarith
    have hshift := p4_mean_shift (R.F k) (S k) (R.hϱ.1.le.trans hϱ.1) 0 s
    rw [zero_add] at hshift
    rw [hshift]
    exact hzero
  obtain ⟨η, hη, hcovrep⟩ := cor_app_vol_filtered_replacement_ii R P S εB hmean
  have hBreal : Tendsto (fun k => (R.B k : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp R.prop.B_top
  have hmeanTerm : Tendsto (fun k =>
      (R.CSig / Real.sqrt R.ϱlo + εB k) ^ 2 / (R.B k : ℝ)) atTop (𝓝 0) :=
    ((tendsto_const_nhds.add hεB).pow 2).div_atTop hBreal
  have hcovErr : Tendsto (fun k => η k +
      (R.CSig / Real.sqrt R.ϱlo + εB k) ^ 2 / (R.B k : ℝ)) atTop (𝓝 0) := by
    simpa using hη.add hmeanTerm
  intro ε hε
  have hr : ∀ᶠ k in atTop, η k +
      (R.CSig / Real.sqrt R.ϱlo + εB k) ^ 2 / (R.B k : ℝ) < ε :=
    (tendsto_order.1 hcovErr).2 ε hε
  filter_upwards [hr] with k hrk
  intro t ϱ hϱ ϱ' hϱ' Fo Gi hFo hF hGi hG
  exact (hcovrep t ℓ k Fo Gi hFo hF hGi hG ϱ ϱ' hϱ hϱ').trans hrk.le

/-- `thm:app-vol-lag-reduction`, part (iv), integrated clause (`_iv_integrated`), snapshot
`cr-2026-10-23`. Declaration of record for the second statement of item (iv),
`sup_{ϱ,ϱ' ∈ I} sup_{F,G} |Γ[F,G] − Γ^g[F,G]| → 0` (LaTeX of item (iv) in the docstring of
`thm_app_vol_lag_reduction_iv_lag`). `Γ` is `integratedLag` (`eqn:app-vol-Gamma`) and `Γ^g` is
`indepIntegratedLag`, the integrated sum of the `C^g_ℓ`. The eventual index is uniform in the time `t`,
the ridges `ϱ, ϱ' ∈ I` and the symmetric tests of operator norm at most one. Sorried: proof card P2. -/
theorem thm_app_vol_lag_reduction_iv_integrated (R : SetupRegime) (Ω : ℕ → Type)
    [∀ k, MeasurableSpace (Ω k)] (P : ∀ k, Measure (Ω k)) [∀ k, IsProbabilityMeasure (P k)]
    (S : ∀ k, FrozenSamples (P k) (R.m k) (R.n k) (R.B k)) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, ∀ t : ℤ,
      ∀ ϱ ∈ Set.Icc R.ϱlo R.ϱhi, ∀ ϱ' ∈ Set.Icc R.ϱlo R.ϱhi,
      ∀ (Fo : Mat (R.m k) (R.m k)) (Gi : Mat (R.n k) (R.n k)),
        Fo.transpose = Fo → opNorm Fo ≤ 1 → Gi.transpose = Gi → opNorm Gi ≤ 1 →
        |integratedLag (R.F k) (S k) t Fo Gi ϱ ϱ' -
          indepIntegratedLag (R.F k) t Fo Gi ϱ ϱ'| ≤ ε := by
  let X : ℕ → Type := fun k =>
    ℤ × ℝ × ℝ × Mat (R.m k) (R.m k) × Mat (R.n k) (R.n k)
  have hRβ : 0 ≤ R.β ∧ R.β < 1 := by
    rw [← R.hβ 0]
    exact (R.F 0).hβ
  let PP : ∀ k, Set (X k) := fun k p => match p with
    | (_, ϱ, ϱ', Fo, Gi) =>
      ϱ ∈ Set.Icc R.ϱlo R.ϱhi ∧ ϱ' ∈ Set.Icc R.ϱlo R.ϱhi ∧
      Fo.transpose = Fo ∧ opNorm Fo ≤ 1 ∧ Gi.transpose = Gi ∧ opNorm Gi ≤ 1
  let a : ∀ k, ℕ → X k → ℝ := fun k ℓ p => match p, ℓ with
    | (t, ϱ, ϱ', Fo, Gi), 0 => def_app_vol_lag (R.F k) (S k) 0 t Fo Gi ϱ ϱ'
    | (t, ϱ, ϱ', Fo, Gi), ℓ + 1 =>
      def_app_vol_lag (R.F k) (S k) (ℓ + 1) t Fo Gi ϱ ϱ' +
        def_app_vol_lag (R.F k) (S k) (ℓ + 1) t Fo Gi ϱ' ϱ
  let b : ∀ k, ℕ → X k → ℝ := fun k ℓ p => match p, ℓ with
    | (t, ϱ, ϱ', Fo, Gi), 0 => indepLagCov (R.F k) 0 t Fo Gi ϱ ϱ'
    | (t, ϱ, ϱ', Fo, Gi), ℓ + 1 =>
      indepLagCov (R.F k) (ℓ + 1) t Fo Gi ϱ ϱ' +
        indepLagCov (R.F k) (ℓ + 1) t Fo Gi ϱ' ϱ
  have hbd : ∀ k, ∀ p ∈ PP k, ∀ ℓ : ℕ, 1 ≤ ℓ →
      |a k ℓ p| + |b k ℓ p| ≤
        (4 * Muon.Dynamics.kStar R.CSig R.γstar R.ϱlo) * R.β ^ ℓ := by
    intro k p hp ℓ hℓ
    rcases p with ⟨t, ϱ, ϱ', Fo, Gi⟩
    dsimp [PP] at hp
    obtain ⟨hϱI, hϱ'I, hFs, hF, hGs, hG⟩ := hp
    obtain ⟨j, rfl⟩ : ∃ j, j + 1 = ℓ := ⟨ℓ - 1, by omega⟩
    have hsz : SizeFin (R.F k).C (R.B k) R.γstar R.CSig :=
      ⟨R.dims k, R.normOut k, R.normIn k⟩
    have ha1 := (thm_app_vol_lag_reduction_ii_actual (R.F k) (S k) R.γstar R.CSig
      R.ϱlo R.ϱhi hsz R.hC R.hϱ Fo Gi hFs hGs hF hG ϱ ϱ' hϱI hϱ'I t).2
      (j + 1) (by omega)
    have ha2 := (thm_app_vol_lag_reduction_ii_actual (R.F k) (S k) R.γstar R.CSig
      R.ϱlo R.ϱhi hsz R.hC R.hϱ Fo Gi hFs hGs hF hG ϱ' ϱ hϱ'I hϱI t).2
      (j + 1) (by omega)
    have hb1 : |indepLagCov (R.F k) (j + 1) t Fo Gi ϱ ϱ'| ≤
        Muon.Dynamics.kStar R.CSig R.γstar R.ϱlo * (R.F k).β ^ (j + 1) :=
      (thm_app_vol_lag_reduction_ii_indep (R.F k) (S k) R.γstar R.CSig
        R.ϱlo R.ϱhi hsz R.hC R.hϱ Fo Gi hFs hGs hF hG ϱ ϱ' hϱI hϱ'I t).2
        (j + 1) (by omega)
    have hb2 : |indepLagCov (R.F k) (j + 1) t Fo Gi ϱ' ϱ| ≤
        Muon.Dynamics.kStar R.CSig R.γstar R.ϱlo * (R.F k).β ^ (j + 1) :=
      (thm_app_vol_lag_reduction_ii_indep (R.F k) (S k) R.γstar R.CSig
        R.ϱlo R.ϱhi hsz R.hC R.hϱ Fo Gi hFs hGs hF hG ϱ' ϱ hϱ'I hϱI t).2
        (j + 1) (by omega)
    rw [R.hβ k] at ha1 ha2 hb1 hb2
    dsimp [a, b]
    calc
      _ ≤ (|def_app_vol_lag (R.F k) (S k) (j + 1) t Fo Gi ϱ ϱ'| +
          |def_app_vol_lag (R.F k) (S k) (j + 1) t Fo Gi ϱ' ϱ|) +
        (|indepLagCov (R.F k) (j + 1) t Fo Gi ϱ ϱ'| +
          |indepLagCov (R.F k) (j + 1) t Fo Gi ϱ' ϱ|) :=
        add_le_add (abs_add_le _ _) (abs_add_le _ _)
      _ ≤ _ := by linarith
  have hlim : ∀ ℓ : ℕ, ∀ ε > 0, ∀ᶠ k in atTop, ∀ p ∈ PP k,
      |a k ℓ p - b k ℓ p| ≤ ε := by
    intro ℓ ε hε
    cases ℓ with
    | zero =>
        filter_upwards [thm_app_vol_lag_reduction_iv_lag R Ω P S 0 ε hε] with k hk
        rintro ⟨t, ϱ, ϱ', Fo, Gi⟩ hp
        dsimp [PP] at hp
        obtain ⟨hϱI, hϱ'I, hFs, hF, hGs, hG⟩ := hp
        simpa [a, b] using hk t ϱ hϱI ϱ' hϱ'I Fo Gi hFs hF hGs hG
    | succ ℓ =>
        filter_upwards [thm_app_vol_lag_reduction_iv_lag R Ω P S (ℓ + 1)
          (ε / 2) (by positivity)] with k hk
        rintro ⟨t, ϱ, ϱ', Fo, Gi⟩ hp
        dsimp [PP] at hp
        obtain ⟨hϱI, hϱ'I, hFs, hF, hGs, hG⟩ := hp
        have h1 := hk t ϱ hϱI ϱ' hϱ'I Fo Gi hFs hF hGs hG
        have h2 := hk t ϱ' hϱ'I ϱ hϱI Fo Gi hFs hF hGs hG
        dsimp [a, b]
        calc
          _ = |(def_app_vol_lag (R.F k) (S k) (ℓ + 1) t Fo Gi ϱ ϱ' -
              indepLagCov (R.F k) (ℓ + 1) t Fo Gi ϱ ϱ') +
            (def_app_vol_lag (R.F k) (S k) (ℓ + 1) t Fo Gi ϱ' ϱ -
              indepLagCov (R.F k) (ℓ + 1) t Fo Gi ϱ' ϱ)| := by congr 1 <;> ring
          _ ≤ _ := abs_add_le _ _
          _ ≤ ε := by linarith
  have hsum := p6_lagsum_dep PP a b (4 * Muon.Dynamics.kStar R.CSig R.γstar R.ϱlo)
    R.β hRβ hbd hlim
  intro ε hε
  filter_upwards [hsum ε hε] with k hk
  intro t ϱ hϱI ϱ' hϱ'I Fo Gi hFs hF hGs hG
  have hp : (t, ϱ, ϱ', Fo, Gi) ∈ PP k := ⟨hϱI, hϱ'I, hFs, hF, hGs, hG⟩
  simpa [a, b, integratedLag, indepIntegratedLag] using hk (t, ϱ, ϱ', Fo, Gi) hp

end Muon.Volatility
