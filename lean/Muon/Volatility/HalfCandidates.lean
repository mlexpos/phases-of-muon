import Muon.DetEquiv.Branch

/-!
# Appendix D: the same-time raw coefficients of rows and columns (`eqn:app-vol-half-candidates`)

Snapshot `cr-2026-10-23`. Source: `sections/04-volatility/section.tex` l.468–472 (subsection
"Same-time energies of rows and columns"), the display defining `volraw_i`, `ṽ^{(0)}_j` and `Z̄`.
Owner: L-G.12 (coordinator ruling: no package owned this display).

Representation choices:

* The objects are real functions of the branch `branchSol (Fw (emaW β)) ν ν'` of
  `Muon.DetEquiv` at `s = ϱ`, i.e. at `z = -ϱ`. The coordinates are `(σ, σ̃, s̃₁, s₁)`, so
  `s̃₁(-ϱ)` is the third component and `s₁(-ϱ)` the fourth.
* `ν` and `ν'` are the full output and input spectral measures (`FiniteMeasure ℝ`). They are
  arguments, not constructed.
* `μi` and `lj` are the spectral values (scalars), so `volraw` and `volTildeZero` take one
  spectral value each. `zbarRaw` takes the spectrum `μ : Fin N → ℝ`.
* The second expression of `Z̄` (trace form) is not stated here.
-/

set_option linter.style.longLine false

open MeasureTheory
open Muon.DetEquiv

noncomputable section

namespace Muon.Volatility

/-- `volraw_i(ϱ)` of `eqn:app-vol-half-candidates`, snapshot `cr-2026-10-23`. LaTeX, verbatim
from `section.tex` l.468–472:

\begin{equation}\label{eqn:app-vol-half-candidates}
\volraw_i(\ridge)\defeq\frac{\tilde s_1(-\ridge)\,\mu_i}{\ridge+\tilde s_1(-\ridge)\,\mu_i},\qquad
\widetilde{\mathfrak v}^{(0)}_j(\ridge)\defeq\frac{s_1(-\ridge)\,\lambda_j}{\ridge+s_1(-\ridge)\,\lambda_j},\qquad
\overline Z(\ridge)\defeq\frac1B\sum_{i=1}^{\Nout}\mu_i\,\volraw_i(\ridge)=\frac1B\Tr\Sigmaout-\ridge\,\sigma(-\ridge).
\end{equation} -/
def volraw (β : ℝ) (ν ν' : FiniteMeasure ℝ) (μi ϱ : ℝ) : ℝ :=
  (branchSol (Fw (emaW β)) ν ν' ϱ).2.2.1 * μi /
    (ϱ + (branchSol (Fw (emaW β)) ν ν' ϱ).2.2.1 * μi)

/-- `ṽ^{(0)}_j(ϱ)` of `eqn:app-vol-half-candidates`, snapshot `cr-2026-10-23`. LaTeX, verbatim
from `section.tex` l.468–472 (the display of `volraw`):

\begin{equation}\label{eqn:app-vol-half-candidates}
\volraw_i(\ridge)\defeq\frac{\tilde s_1(-\ridge)\,\mu_i}{\ridge+\tilde s_1(-\ridge)\,\mu_i},\qquad
\widetilde{\mathfrak v}^{(0)}_j(\ridge)\defeq\frac{s_1(-\ridge)\,\lambda_j}{\ridge+s_1(-\ridge)\,\lambda_j},\qquad
\overline Z(\ridge)\defeq\frac1B\sum_{i=1}^{\Nout}\mu_i\,\volraw_i(\ridge)=\frac1B\Tr\Sigmaout-\ridge\,\sigma(-\ridge).
\end{equation} -/
def volTildeZero (β : ℝ) (ν ν' : FiniteMeasure ℝ) (lj ϱ : ℝ) : ℝ :=
  (branchSol (Fw (emaW β)) ν ν' ϱ).2.2.2 * lj /
    (ϱ + (branchSol (Fw (emaW β)) ν ν' ϱ).2.2.2 * lj)

/-- `Z̄(ϱ)` of `eqn:app-vol-half-candidates`, first expression `(1/B) ∑_i μ_i volraw_i(ϱ)`,
snapshot `cr-2026-10-23`. LaTeX, verbatim from `section.tex` l.468–472 (the display of `volraw`).
The trace expression `(1/B) Tr Σ_out − ϱ σ(−ϱ)` is not stated here.

\begin{equation}\label{eqn:app-vol-half-candidates}
\volraw_i(\ridge)\defeq\frac{\tilde s_1(-\ridge)\,\mu_i}{\ridge+\tilde s_1(-\ridge)\,\mu_i},\qquad
\widetilde{\mathfrak v}^{(0)}_j(\ridge)\defeq\frac{s_1(-\ridge)\,\lambda_j}{\ridge+s_1(-\ridge)\,\lambda_j},\qquad
\overline Z(\ridge)\defeq\frac1B\sum_{i=1}^{\Nout}\mu_i\,\volraw_i(\ridge)=\frac1B\Tr\Sigmaout-\ridge\,\sigma(-\ridge).
\end{equation} -/
def zbarRaw {N : ℕ} (β : ℝ) (B : ℕ) (ν ν' : FiniteMeasure ℝ) (μ : Fin N → ℝ) (ϱ : ℝ) : ℝ :=
  (B : ℝ)⁻¹ * ∑ i, μ i * volraw β ν ν' (μ i) ϱ

/-- Private: the trace identity for any admissible weight function `F` (proof of
`eqn_app_vol_half_candidates_trace` modulo admissibility of `Fw (emaW β)`). -/
private lemma vol_trace_of_adm {F : ℝ → ℝ} (hF : AdmissibleWeightFn F) {N B : ℕ}
    (μ : Fin N → ℝ) {ν ν' : FiniteMeasure ℝ} {Cs γ : ℝ}
    (hν : (ν : Measure ℝ) = ENNReal.ofReal ((B : ℝ)⁻¹) • ∑ i, Measure.dirac (μ i))
    (hK : (ν, ν') ∈ classK Cs γ) (hμ : ∀ i, 0 ≤ μ i) {ϱ : ℝ} (hϱ : 0 < ϱ) :
    (B : ℝ)⁻¹ * ∑ i, μ i * ((branchSol F ν ν' ϱ).2.2.1 * μ i /
        (ϱ + (branchSol F ν ν' ϱ).2.2.1 * μ i)) =
      (B : ℝ)⁻¹ * ∑ i, μ i - ϱ * (branchSol F ν ν' ϱ).1 := by
  have hK' := hK
  simp only [classK] at hK'
  obtain ⟨hK1, hK2, hK3, hK4⟩ := hK'
  have enl : ∀ m : Measure ℝ, m (Set.Icc 0 Cs) ≤ ENNReal.ofReal γ → m (Set.Icc 0 Cs)ᶜ = 0 →
      m (Set.Icc 0 (max Cs 1)) ≤ ENNReal.ofReal (max γ 1) ∧ m (Set.Icc 0 (max Cs 1))ᶜ = 0 := by
    intro m h1 h2
    refine ⟨?_, ?_⟩
    · calc m (Set.Icc 0 (max Cs 1)) ≤ m (Set.Icc 0 Cs ∪ (Set.Icc 0 Cs)ᶜ) :=
            measure_mono (fun x _ => by by_cases h : x ∈ Set.Icc 0 Cs <;> simp [h])
        _ ≤ m (Set.Icc 0 Cs) + m (Set.Icc 0 Cs)ᶜ := measure_union_le _ _
        _ ≤ ENNReal.ofReal (max γ 1) := by
            rw [h2, add_zero]
            exact h1.trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))
    · refine measure_mono_null (fun x (hx : x ∈ (Set.Icc 0 (max Cs 1))ᶜ)
        (hx' : x ∈ Set.Icc 0 Cs) => hx ⟨hx'.1, hx'.2.trans (le_max_left _ _)⟩) h2
  have hmem : (ν, ν') ∈ classK (max Cs 1) (max γ 1) := by
    simp only [classK]
    exact ⟨(enl _ hK1 hK2).1, (enl _ hK1 hK2).2, (enl _ hK3 hK4).1, (enl _ hK3 hK4).2⟩
  have hsp := branchSol_spec hF (lt_of_lt_of_le one_pos (le_max_right _ _))
    (lt_of_lt_of_le one_pos (le_max_right _ _)) hmem hϱ
  generalize branchSol F ν ν' ϱ = x at hsp ⊢
  obtain ⟨σ, σ', a, c⟩ := x
  simp only [IsBranchSol] at hsp
  obtain ⟨_, _, ha0, _, hσ, _, _, _⟩ := hsp
  dsimp only at hσ ha0 ⊢
  have hint : ∫ t, t / (a * t + ϱ) ∂(ν : Measure ℝ) =
      (B : ℝ)⁻¹ * ∑ i, μ i / (a * μ i + ϱ) := by
    rw [hν, integral_smul_measure, integral_finsetSum_measure
      (fun i _ => integrable_dirac (by simp))]
    simp only [integral_dirac, ENNReal.toReal_ofReal (inv_nonneg.2 (Nat.cast_nonneg B)),
      smul_eq_mul, Finset.mul_sum]
  rw [hint] at hσ
  have key : ∀ i, μ i * (a * μ i / (ϱ + a * μ i)) = μ i - ϱ * (μ i / (a * μ i + ϱ)) := by
    intro i
    have h1 : ϱ + a * μ i ≠ 0 := (by have := mul_nonneg ha0 (hμ i); linarith : (0:ℝ) < _).ne'
    rw [add_comm (a * μ i) ϱ]
    simp only [div_eq_mul_inv]
    linear_combination (μ i) * mul_inv_cancel₀ h1
  rw [Finset.sum_congr rfl (fun i _ => key i), Finset.sum_sub_distrib, ← Finset.mul_sum, hσ]
  ring

/-- Private: the EMA weights `emaW β` with `0 ≤ β < 1` give an admissible `Fw`. The frozen
statement of `eqn_app_vol_half_candidates_trace` does not assume this range (the paper has
`β ∈ [0,1)`), which is the remaining gap. -/
private lemma vol_emaW_admissible {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) :
    AdmissibleWeightFn (Fw (emaW β)) := by
  refine Fw_admissible ⟨fun j => ?_, ?_, 0, ?_⟩
  · unfold emaW
    exact mul_nonneg (by linarith) (pow_nonneg hβ0 j)
  · unfold emaW
    exact (summable_geometric_of_lt_one hβ0 hβ1).mul_left _
  · unfold emaW
    rw [pow_zero, mul_one]
    exact (by linarith : (0:ℝ) < 1 - β).ne'

/-- Trace form of `Z̄` in `eqn:app-vol-half-candidates`, `eqn:app-vol-half-candidates` second
expression `Z̄(ϱ) = (1/B) Tr Σ_out − ϱ σ(−ϱ)`, snapshot `cr-2026-10-23`. LaTeX, verbatim from
`section.tex` l.473–475 (the sentence proving it, after the display of `volraw`):

The second expression of $\overline Z$ follows from
$\mu_i\volraw_i=\mu_i-\ridge\mu_i/(\ridge+\tilde s_1\mu_i)$ and the first equation
of \cref{eqn:app-de-system}. The letter $\volraw$ marks a deterministic

With `ν = B⁻¹ ∑ δ_{μ_i}` (so `Tr Σ_out = ∑ μ_i`) and `(ν, ν′) ∈ classK Cs γ` (so `branchSol`
solves the system; otherwise it is the junk value `0`). -/
theorem eqn_app_vol_half_candidates_trace {N B : ℕ} (β : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β < 1) (μ : Fin N → ℝ)
    {ν ν' : FiniteMeasure ℝ} {Cs γ : ℝ}
    (hν : (ν : Measure ℝ) = ENNReal.ofReal ((B : ℝ)⁻¹) • ∑ i, Measure.dirac (μ i))
    (hK : (ν, ν') ∈ classK Cs γ) (hμ : ∀ i, 0 ≤ μ i) {ϱ : ℝ} (hϱ : 0 < ϱ) :
    zbarRaw β B ν ν' μ ϱ = (B : ℝ)⁻¹ * ∑ i, μ i - ϱ * (branchSol (Fw (emaW β)) ν ν' ϱ).1 := by
  unfold zbarRaw volraw
  exact vol_trace_of_adm (vol_emaW_admissible hβ0 hβ1) μ hν hK hμ hϱ

end Muon.Volatility

end
