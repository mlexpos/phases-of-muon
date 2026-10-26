import Muon.Dynamics.SectorDrift
import Muon.Dynamics.MeanUniform
import Muon.Dynamics.Chains
import Muon.Setup.Resolvent
import Muon.DetEquiv.SampleModel

/-!
# Appendix E, work package L-E.7: finite mean and susceptibility (`lem:app-dyn-mean`)

Snapshot `cr-2026-10-23`. Source: `sections/05-dynamics/section.tex`, `lem:app-dyn-mean` (ll. 768–798),
with its display `eqn:app-dyn-mean-physical`. Card: `sections/05-dynamics/CARD.md` §2, §3 (row
`lem:app-dyn-mean`), §5 (L-E.7), §6 (risk 2). Interface draft: statements are `sorry`ed; proofs are
later work.

Reused, not redefined: `Muon.Setup.FrozenParams`, `FrozenSamples`, `frozenBuf`, `Rres` (the complex
output-side resolvent), `rOut`, `rIn`, `riskSigma`, `Muon.Q`, `Muon.mean`, `Muon.fro`, `Muon.opNorm`,
`Muon.ProportionalRegime`, `Muon.Covariances`; from `Muon.Dynamics` (`Chains`) `DynParams` (via
`Basic`), `ChainSamples`, `def_app_dyn_chains`, `physRidge` (`Basic`).

Representation choices (also in the result JSON `open_questions`):
* Complex matrices. The mixed resolvent `𝖷_z` and the mean `𝓗(z)` are complex for `z ∈ 𝕊`, so the
  entrywise mean is `cmean` (the `ℂ` analogue of `Muon.mean`) and `Xz K z = Rres K (-z) * K` (with
  `R_z(K) = (KKᵀ + z)⁻¹ = (KKᵀ − (−z))⁻¹`). At real `z = s` this is `Muon.DetEquiv.Xs K s`.
* `𝕊` is `sectorS`; `z.re` is the source's `Re z`, `|z.im| ≤ z.re/2` the source's `|Im z| ≤ Re z/2`.
* Derivatives are entrywise `deriv` in the real variable. Every `deriv` is paired with a
  `DifferentiableAt` conjunct (the source asserts the derivative exists), so no junk value is used.
  `dQ ϱ K` is the entrywise `∂_ϱ Q_ϱ(K)`.
* Integrability. Every expectation comes with an `Integrable` conjunct in the conclusion (the
  integrands are bounded and measurable: `‖Q_ϱ(K)‖ ≤ 1`, `‖𝖷_z(K)‖ ≤ 1/(2√Re z)`), not a hypothesis.
* Weights. The main declarations `_i`–`_iv` are stated for a general weight sequence `w` in
  `Muon.DetEquiv.WeightClass` (`eqn:app-de-weightclass`), with the buffer `Muon.DetEquiv.WeightedBuf w`.
  Constants are quantified before `w`, the models and the samples. The EMA forms `_i_ema`–`_iv_ema`
  (frozen buffer `frozenBuf`, weights `emaW F.β`) are separate declarations, each a corollary via
  `weightedBuf_emaW_eq_frozenBuf` and `Muon.Drift.emaW_weightClass`.
* Normalized states. `FrozenParams` fixes `‖Â‖_F = 1` (the source's standing normalization). The
  "for every normalized state" of (iv) is quantified through `withState`, which replaces the state
  `A` of a frozen-parameter record by another normalized `A` with the same covariances, momentum and
  batch size. The samples `FrozenSamples` do not depend on `A`.
* Operator norm. The source's unsubscripted `‖·‖` on matrices is `opNorm`; `‖·‖_F` is `fro`.
* Constants and quantifier order. (i)–(iii) are uniform in the dimension, the state, the weights and the
  samples, and depend only on `(γ⋆, C_Σ)`, `I`, or `(ϱ₋, ϱ₊)`: the constants are existentially quantified
  before the weights and models. (iv) is uniform in the state and depends on `(ϱ, γ⋆, C_Σ)`: `K` is
  chosen first, then the models, samples and weight sequences, then `r`, then the states.
* `eqn:app-dyn-mean-physical`: the constant `C` depends on `(γ⋆, C_Σ, ϱ, r₋, r₊)` and is chosen before
  the parameter record `p`, with field equalities linking `p`; so it cannot depend on `p.β`.
* Hypotheses for (iv) and `eqn:app-dyn-mean-physical`: `ProportionalRegime`, which carries the
  divergence `B → ∞` (the standing assumption `assum:app-setup-regime`).
* `eqn:app-dyn-mean-physical` is stated for the frozen chains of `Muon.Dynamics.Chains`
  (`def_app_dyn_chains`), with `N_0 = stat 1` and `V_0 = statV 1` (index `k = r + 1`).
-/

open scoped Matrix MatrixOrder ENNReal
open MeasureTheory ProbabilityTheory Filter Topology Set Matrix
open Muon Muon.Setup

noncomputable section

namespace Muon.Dynamics

/-! ## Objects of `lem:app-dyn-mean` -/

/-- The closed sector `𝕊 = {z : Re z > 0, |Im z| ≤ Re z / 2}` of `lem:app-dyn-mean`
(source ll. 758–760). Snapshot `cr-2026-10-23`. -/
def sectorS : Set ℂ := {z | 0 < z.re ∧ |z.im| ≤ z.re / 2}

/-- Entrywise expectation of a complex random matrix, the `ℂ` analogue of `Muon.mean`
(`section.tex` conventions: expectations of matrices are entrywise). -/
def cmean {Ω : Type*} [MeasurableSpace Ω] {m n : ℕ} (P : Measure Ω)
    (X : Ω → Matrix (Fin m) (Fin n) ℂ) : Matrix (Fin m) (Fin n) ℂ :=
  Matrix.of fun i j => ∫ ω, X ω i j ∂P

/-- Complex mixed resolvent `𝖷_z(K) = R_z(K) K`, `R_z(K) = (K Kᵀ + z Id)⁻¹ = Rres K (−z)`
(`lem:app-dyn-mean`, ll. 758–766). At real `z = s` it is `Muon.DetEquiv.Xs K s`. -/
def Xz {m n : ℕ} (K : Mat m n) (z : ℂ) : Matrix (Fin m) (Fin n) ℂ :=
  Rres K (-z) * K.map (fun x : ℝ => (x : ℂ))

/-- Expected mixed resolvent `𝓗(z) = 𝔼 𝖷_z(M_t)` of the buffer with weights `w`,
`M_t = WeightedBuf w F S t` (`lem:app-dyn-mean`, ll. 758–766; the general weight sequence of
`eqn:app-de-weightclass` is `Muon.DetEquiv.WeightClass`). -/
def Hz {Ω : Type*} [MeasurableSpace Ω] {m n B : ℕ} (w : ℕ → ℝ) (P : Measure Ω)
    (F : FrozenParams m n B) (S : FrozenSamples P m n B) (t : ℤ) (z : ℂ) :
    Matrix (Fin m) (Fin n) ℂ :=
  cmean P (fun ω => Xz (Muon.DetEquiv.WeightedBuf w F S t ω) z)

/-- The EMA case `𝓗(z) = 𝔼 𝖷_z(M_t)` with the frozen buffer `M_t = frozenBuf F S t`. -/
def HzF {Ω : Type*} [MeasurableSpace Ω] {m n B : ℕ} (P : Measure Ω) (F : FrozenParams m n B)
    (S : FrozenSamples P m n B) (t : ℤ) (z : ℂ) : Matrix (Fin m) (Fin n) ℂ :=
  cmean P (fun ω => Xz (frozenBuf F S t ω) z)

/-- Entrywise derivative `∂_ϱ Q_ϱ(K)` of the regularized map in the ridge (`lem:app-dyn-mean`(iii)). -/
def dQ {m n : ℕ} (ϱ : ℝ) (K : Mat m n) : Mat m n :=
  Matrix.of fun i j => deriv (fun r : ℝ => Q r K i j) ϱ

/-- Entrywise derivative `d𝓗(s)/ds` along real `s` for the weights `w` (`lem:app-dyn-mean`(ii)). -/
def dHz {Ω : Type*} [MeasurableSpace Ω] {m n B : ℕ} (w : ℕ → ℝ) (P : Measure Ω)
    (F : FrozenParams m n B) (S : FrozenSamples P m n B) (t : ℤ) (s : ℝ) :
    Matrix (Fin m) (Fin n) ℂ :=
  Matrix.of fun i j => deriv (fun x : ℝ => Hz w P F S t (x : ℂ) i j) s

/-- Entrywise derivative `d𝓗(s)/ds` in the EMA case (frozen buffer `frozenBuf`). -/
def dHzF {Ω : Type*} [MeasurableSpace Ω] {m n B : ℕ} (P : Measure Ω) (F : FrozenParams m n B)
    (S : FrozenSamples P m n B) (t : ℤ) (s : ℝ) : Matrix (Fin m) (Fin n) ℂ :=
  Matrix.of fun i j => deriv (fun x : ℝ => HzF P F S t (x : ℂ) i j) s

/-- The frozen-parameter record with normalized state `A` in place of `F.A`
(`‖A‖_F = 1`); used to quantify over every normalized state (`lem:app-dyn-mean`(iv)). The covariances,
momentum and batch size are those of `F`. -/
def withState {m n B : ℕ} (F : FrozenParams m n B) (A : Mat m n) (hA : fro A = 1) :
    FrozenParams m n B :=
  { F with A := A, hA := hA }

/-! ## The finite mean and susceptibility -/

/-- `lem:app-dyn-mean`(i), `cr-2026-10-23`. Sector bounds for a general weight sequence in
`eqn:app-de-weightclass`: for every compact `I ⊂ (0,∞)` there are `C_I` and `C`, depending only on
`(γ⋆, C_Σ)` and `I` and chosen before the weights, the models and the samples, such that for every weight
sequence `w` in the class, every frozen-state model with `‖Â‖_F = 1`, `‖Σ_out‖, ‖Σ_in‖ ≤ C_Σ`,
`max(N_in, N_out) ≤ γ⋆ B`, the sector mixed resolvent is integrable on `𝕊`, and `‖𝓗(z)‖_F ≤ C_I` when
`Re z ∈ I`, `‖𝓗(z)‖_F ≤ C/Re z` when `Re z ≥ 1`.
Source, verbatim (`sections/05-dynamics/section.tex`, ll. 768–798):
```latex
\begin{lemma}[Finite mean and susceptibility]\label{lem:app-dyn-mean}
In the frozen-state model with $\norm{\Ahat}_\F=1$, $\norm{\Sigmaout},\norm{\Sigmain}\le C_\Sigma$
and $\max(\Nin,\Nout)\le\gamma_\star B$, and with no condition on $\norm{\Ahat}$:
\begin{enumerate}[label=(\roman*)]
\item for every compact $I\subset(0,\infty)$ there is $C_I$ with
$\norm{\mathcal H(z)}_\F\le C_I$ for $z\in\mathbb S$ with $\Ree z\in I$, and
$\norm{\mathcal H(z)}_\F\le C/\Ree z$ for $z\in\mathbb S$ with $\Ree z\ge1$;
\item for real $s$, $\norm{\frac{\dif}{\dif s}\mathcal H(s)}_\F\le C_I$ for $s\in I$ and
$\norm{\frac{\dif}{\dif s}\mathcal H(s)}_\F\le C/s^2$ for $s\ge2$;
\item for $0<\ridge_-\le\ridge'\le\ridge_+$,
$\norm{\EE\,\Qridge{\ridge'}(\Mt)}_\F+\norm{\EE\,\partial_{\ridge'}\Qridge{\ridge'}(\Mt)}_\F\le C$,
with $C$ depending also on $(\ridge_-,\ridge_+)$;
\item for the fixed ridge $\ridge$ there are $C$ and a sequence $r_B\to0$,
depending only on $(\ridge,\gamma_\star,C_\Sigma)$ and on the sequence of
dimensions, such that $\norm{\EE\,\Qridge\ridge(\Mt)}\le C\norm{\Ahat}+r_B$ for
every normalized state.
\end{enumerate}
The constants depend only on $(\gamma_\star,C_\Sigma)$ and on $I$ where
indicated, not on $\Ahat$, on the dimension or on the weights within the
class \cref{eqn:app-de-weightclass}. Consequently, for the stationary chain
of \cref{def:app-dyn-chains} at a deterministic $D$ with
$r_-\le\cR(D)\le r_+$,
\begin{equation}\label{eqn:app-dyn-mean-physical}
\begin{gathered}
\norm{\overline V(D)}_\F\le C,\qquad
\big\|\EE\,\partial_\ell\Qridge\ell(N_0)\big|_{\ell=\ridgephys(D)}\big\|_\F\le C,\\
\norm{\Sigmaout^{1/2}\overline V(D)\Sigmain^{1/2}}\le C\norm{\Sigmaout^{1/2}D\Sigmain^{1/2}}+Cr_B ,
\end{gathered}
\end{equation}
with $C$ depending also on $(r_-,r_+)$.
\end{lemma}
```
-/
theorem lem_app_dyn_mean_i (γ CS : ℝ) (I : Set ℝ) (hI : IsCompact I) (hIpos : I ⊆ Ioi 0) :
    ∃ CI C : ℝ, ∀ (w : ℕ → ℝ), Muon.DetEquiv.WeightClass w →
      ∀ (m n B : ℕ) (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (S : FrozenSamples P m n B) (F : FrozenParams m n B) (t : ℤ),
      ((max m n : ℕ) : ℝ) ≤ γ * (B : ℝ) → opNorm F.C.Sout ≤ CS → opNorm F.C.Sin ≤ CS →
      (∀ z : ℂ, z ∈ sectorS → ∀ (i : Fin m) (j : Fin n),
        Integrable (fun ω => Xz (Muon.DetEquiv.WeightedBuf w F S t ω) z i j) P) ∧
      (∀ z ∈ sectorS, z.re ∈ I → fro (Hz w P F S t z) ≤ CI) ∧
      (∀ z ∈ sectorS, 1 ≤ z.re → fro (Hz w P F S t z) ≤ C / z.re) := by
  obtain ⟨s₁, hs₁, hs₁le⟩ : ∃ s₁ : ℝ, 0 < s₁ ∧ ∀ s ∈ I, s₁ ≤ s := by
    by_cases h : I.Nonempty
    · refine ⟨sInf I, hIpos (hI.sInf_mem h), fun s hs => csInf_le hI.bddBelow hs⟩
    · exact ⟨1, one_pos, fun s hs => (h ⟨s, hs⟩).elim⟩
  obtain ⟨C₁, h₁⟩ := thm_app_drift_mixed_ii_sector s₁ hs₁ CS γ
  obtain ⟨C₂, h₂⟩ := thm_app_drift_mixed_ii_sector 1 one_pos CS γ
  refine ⟨max C₁ 0 / s₁, C₂, ?_⟩
  intro w hw m n B Ω _ P _ S F t hγ hS1 hS2
  have hD : Muon.Drift.DriftBound F CS γ := ⟨hS1, hS2, hγ⟩
  obtain ⟨hint, hb1⟩ := h₁ Ω m n B P w F S t hw hD
  obtain ⟨-, hb2⟩ := h₂ Ω m n B P w F S t hw hD
  refine ⟨fun z hz i j => hint z hz.1 i j, ?_, ?_⟩
  · intro z hz hzI
    have h := hb1 z (hs₁le _ hzI) hz.2
    have hre : 0 < z.re := hz.1
    refine (show fro (Hz w P F S t z) ≤ C₁ / z.re from h).trans ?_
    calc C₁ / z.re ≤ max C₁ 0 / z.re := div_le_div_of_nonneg_right (le_max_left _ _) hre.le
      _ ≤ max C₁ 0 / s₁ :=
        div_le_div_of_nonneg_left (le_max_right _ _) hs₁ (hs₁le _ hzI)
  · intro z hz h1
    exact hb2 z h1 hz.2

private lemma fm_froC_sq {k l : ℕ} (A : Matrix (Fin k) (Fin l) ℂ) :
    fro A ^ 2 = ∑ i, ∑ j, ‖A i j‖ ^ 2 := by
  unfold fro
  exact Real.sq_sqrt (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => by positivity)

private lemma fm_froC_nonneg {k l : ℕ} (A : Matrix (Fin k) (Fin l) ℂ) : 0 ≤ fro A :=
  Real.sqrt_nonneg _

private lemma fm_cs {k l : ℕ} (A B : Matrix (Fin k) (Fin l) ℂ) :
    ∑ i, ∑ j, ‖A i j‖ * ‖B i j‖ ≤ fro A * fro B := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin k × Fin l))
    (fun p => ‖A p.1 p.2‖) (fun p => ‖B p.1 p.2‖)
  rw [Fintype.sum_prod_type] at h
  simp only [Fintype.sum_prod_type] at h
  have e1 : ∑ i, ∑ j, ‖A i j‖ ^ 2 = fro A ^ 2 := (fm_froC_sq A).symm
  have e2 : ∑ i, ∑ j, ‖B i j‖ ^ 2 = fro B ^ 2 := (fm_froC_sq B).symm
  rw [e1, e2, ← mul_pow] at h
  exact le_of_sq_le_sq (by simpa using h) (mul_nonneg (fm_froC_nonneg _) (fm_froC_nonneg _))
    |> fun h => by simpa using h


private lemma fm_cauchy_fro {m n : ℕ} (H : ℂ → Matrix (Fin m) (Fin n) ℂ) (s r M : ℝ) (hr : 0 < r)
    (hdiff : ∀ i j, DifferentiableOn ℂ (fun z => H z i j) (Metric.closedBall (s : ℂ) r))
    (hM : ∀ ζ : ℂ, ‖ζ - s‖ = r → fro (H ζ) ≤ M) :
    (∀ i j, DifferentiableAt ℝ (fun x : ℝ => H (x : ℂ) i j) s) ∧
      fro (Matrix.of fun i j => deriv (fun x : ℝ => H (x : ℂ) i j) s) ≤ M / r := by
  have hda : ∀ i j, DifferentiableAt ℂ (fun z => H z i j) (s : ℂ) := fun i j =>
    (hdiff i j).differentiableAt (Metric.closedBall_mem_nhds (s : ℂ) hr)
  have hreal : ∀ i j, HasDerivAt (fun x : ℝ => H (x : ℂ) i j)
      (deriv (fun z => H z i j) (s : ℂ)) s := fun i j => (hda i j).hasDerivAt.comp_ofReal
  refine ⟨fun i j => (hreal i j).differentiableAt, ?_⟩
  set D : Matrix (Fin m) (Fin n) ℂ := Matrix.of fun i j => deriv (fun z => H z i j) (s : ℂ) with hD
  have hDeq : (Matrix.of fun i j => deriv (fun x : ℝ => H (x : ℂ) i j) s) = D := by
    ext i j; simp [hD, (hreal i j).deriv]
  rw [hDeq]
  have hM0 : 0 ≤ M := le_trans (fm_froC_nonneg _) (hM ((s : ℂ) + r) (by simp [abs_of_pos hr]))
  set g : ℂ → ℂ := fun ζ => ∑ i, ∑ j, (starRingEnd ℂ) (D i j) * H ζ i j with hg
  have hgd : DifferentiableOn ℂ g (Metric.closedBall (s : ℂ) r) := by
    refine DifferentiableOn.fun_sum fun i _ => DifferentiableOn.fun_sum fun j _ => ?_
    exact (differentiableOn_const _).mul (hdiff i j)
  have hgc : DiffContOnCl ℂ g (Metric.ball (s : ℂ) r) :=
    ⟨hgd.mono Metric.ball_subset_closedBall,
      hgd.continuousOn.mono (Metric.closure_ball_subset_closedBall)⟩
  have hgs : ∀ ζ ∈ Metric.sphere (s : ℂ) r, ‖g ζ‖ ≤ fro D * M := by
    intro ζ hζ
    have h1 : ‖ζ - s‖ = r := by simpa [dist_eq_norm] using hζ
    calc ‖g ζ‖ ≤ ∑ i, ∑ j, ‖D i j‖ * ‖H ζ i j‖ := by
          refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
          refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
          simp
      _ ≤ fro D * fro (H ζ) := fm_cs _ _
      _ ≤ fro D * M := mul_le_mul_of_nonneg_left (hM ζ h1) (fm_froC_nonneg _)
  have hcauchy := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hr hgc hgs
  have hgder : HasDerivAt g (∑ i, ∑ j, (starRingEnd ℂ) (D i j) * D i j) (s : ℂ) := by
    refine HasDerivAt.fun_sum fun i _ => HasDerivAt.fun_sum fun j _ => ?_
    exact ((hda i j).hasDerivAt).const_mul _
  rw [hgder.deriv] at hcauchy
  have hsum : ∑ i, ∑ j, (starRingEnd ℂ) (D i j) * D i j = ((fro D ^ 2 : ℝ) : ℂ) := by
    rw [fm_froC_sq]
    push_cast
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [Complex.conj_mul']
  rw [hsum] at hcauchy
  simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (fro D))] at hcauchy
  have hF0 := fm_froC_nonneg D
  rcases hF0.eq_or_lt with h0 | hpos
  · rw [← h0]; positivity
  · rw [le_div_iff₀ hr]
    rw [le_div_iff₀ hr] at hcauchy
    refine le_of_mul_le_mul_left ?_ hpos
    nlinarith


private lemma fm_dHz_core {Ω : Type} [MeasurableSpace Ω] {m n B : ℕ} (P : Measure Ω)
    [IsProbabilityMeasure P] {w : ℕ → ℝ} (hw : Muon.DetEquiv.WeightClass w)
    (F : FrozenParams m n B) (S : FrozenSamples P m n B) (t : ℤ) (s s0 K : ℝ) (hs : 0 < s)
    (hs0 : s0 ≤ 3 * s / 4) (hK : 0 ≤ K)
    (hb : ∀ z : ℂ, s0 ≤ z.re → |z.im| ≤ z.re / 2 → fro (Hz w P F S t z) ≤ K / z.re) :
    (∀ (i : Fin m) (j : Fin n),
      DifferentiableAt ℝ (fun x : ℝ => Hz w P F S t (x : ℂ) i j) s) ∧
      fro (dHz w P F S t s) ≤ 16 * K / (3 * s ^ 2) := by
  have hr : 0 < s / 4 := by positivity
  have hcirc : ∀ ζ : ℂ, ‖ζ - (s : ℂ)‖ ≤ s / 4 → 3 * s / 4 ≤ ζ.re ∧ |ζ.im| ≤ ζ.re / 2 := by
    intro ζ hζ
    have h1 : |ζ.re - s| ≤ s / 4 := by
      refine le_trans ?_ hζ
      simpa using Complex.abs_re_le_norm (ζ - (s : ℂ))
    have h2 : |ζ.im| ≤ s / 4 := by
      refine le_trans ?_ hζ
      simpa using Complex.abs_im_le_norm (ζ - (s : ℂ))
    have h3 := abs_le.mp h1
    constructor <;> linarith [h3.1]
  have hdiff : ∀ i j, DifferentiableOn ℂ (fun z => Hz w P F S t z i j)
      (Metric.closedBall (s : ℂ) (s / 4)) := by
    intro i j
    refine (hmixC_differentiableOn hw F S t i j).mono ?_
    intro ζ hζ
    have := hcirc ζ (by simpa [dist_eq_norm] using hζ)
    show 0 < ζ.re
    linarith [this.1]
  have key := fm_cauchy_fro (Hz w P F S t) s (s / 4) (K / (3 * s / 4)) hr hdiff (by
    intro ζ hζ
    obtain ⟨h1, h2⟩ := hcirc ζ hζ.le
    refine (hb ζ (hs0.trans h1) h2).trans ?_
    exact div_le_div_of_nonneg_left hK (by positivity) h1)
  refine ⟨key.1, key.2.trans (le_of_eq ?_)⟩
  field_simp
  ring

/-- `lem:app-dyn-mean`(ii), `cr-2026-10-23`. Real derivatives for a general weight sequence in the class:
for every compact `I ⊂ (0,∞)` there are `C_I` and `C`, depending only on `(γ⋆, C_Σ)` and `I` and chosen
before the weights and the models, such that the sector integrability holds and `s ↦ 𝓗(s)` is
differentiable (entrywise) on `I` and on `[2,∞)`, with `‖d𝓗/ds (s)‖_F ≤ C_I` for `s ∈ I` and
`‖d𝓗/ds (s)‖_F ≤ C/s²` for `s ≥ 2`.
Source, verbatim (`sections/05-dynamics/section.tex`, ll. 768–798):
```latex
\begin{lemma}[Finite mean and susceptibility]\label{lem:app-dyn-mean}
In the frozen-state model with $\norm{\Ahat}_\F=1$, $\norm{\Sigmaout},\norm{\Sigmain}\le C_\Sigma$
and $\max(\Nin,\Nout)\le\gamma_\star B$, and with no condition on $\norm{\Ahat}$:
\begin{enumerate}[label=(\roman*)]
\item for every compact $I\subset(0,\infty)$ there is $C_I$ with
$\norm{\mathcal H(z)}_\F\le C_I$ for $z\in\mathbb S$ with $\Ree z\in I$, and
$\norm{\mathcal H(z)}_\F\le C/\Ree z$ for $z\in\mathbb S$ with $\Ree z\ge1$;
\item for real $s$, $\norm{\frac{\dif}{\dif s}\mathcal H(s)}_\F\le C_I$ for $s\in I$ and
$\norm{\frac{\dif}{\dif s}\mathcal H(s)}_\F\le C/s^2$ for $s\ge2$;
\item for $0<\ridge_-\le\ridge'\le\ridge_+$,
$\norm{\EE\,\Qridge{\ridge'}(\Mt)}_\F+\norm{\EE\,\partial_{\ridge'}\Qridge{\ridge'}(\Mt)}_\F\le C$,
with $C$ depending also on $(\ridge_-,\ridge_+)$;
\item for the fixed ridge $\ridge$ there are $C$ and a sequence $r_B\to0$,
depending only on $(\ridge,\gamma_\star,C_\Sigma)$ and on the sequence of
dimensions, such that $\norm{\EE\,\Qridge\ridge(\Mt)}\le C\norm{\Ahat}+r_B$ for
every normalized state.
\end{enumerate}
The constants depend only on $(\gamma_\star,C_\Sigma)$ and on $I$ where
indicated, not on $\Ahat$, on the dimension or on the weights within the
class \cref{eqn:app-de-weightclass}. Consequently, for the stationary chain
of \cref{def:app-dyn-chains} at a deterministic $D$ with
$r_-\le\cR(D)\le r_+$,
\begin{equation}\label{eqn:app-dyn-mean-physical}
\begin{gathered}
\norm{\overline V(D)}_\F\le C,\qquad
\big\|\EE\,\partial_\ell\Qridge\ell(N_0)\big|_{\ell=\ridgephys(D)}\big\|_\F\le C,\\
\norm{\Sigmaout^{1/2}\overline V(D)\Sigmain^{1/2}}\le C\norm{\Sigmaout^{1/2}D\Sigmain^{1/2}}+Cr_B ,
\end{gathered}
\end{equation}
with $C$ depending also on $(r_-,r_+)$.
\end{lemma}
```
-/
theorem lem_app_dyn_mean_ii (γ CS : ℝ) (I : Set ℝ) (hI : IsCompact I) (hIpos : I ⊆ Ioi 0) :
    ∃ CI C : ℝ, ∀ (w : ℕ → ℝ), Muon.DetEquiv.WeightClass w →
      ∀ (m n B : ℕ) (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (S : FrozenSamples P m n B) (F : FrozenParams m n B) (t : ℤ),
      ((max m n : ℕ) : ℝ) ≤ γ * (B : ℝ) → opNorm F.C.Sout ≤ CS → opNorm F.C.Sin ≤ CS →
      (∀ z : ℂ, z ∈ sectorS → ∀ (i : Fin m) (j : Fin n),
        Integrable (fun ω => Xz (Muon.DetEquiv.WeightedBuf w F S t ω) z i j) P) ∧
      (∀ s ∈ I, (∀ (i : Fin m) (j : Fin n),
          DifferentiableAt ℝ (fun x : ℝ => Hz w P F S t (x : ℂ) i j) s) ∧
        fro (dHz w P F S t s) ≤ CI) ∧
      (∀ s : ℝ, 2 ≤ s → (∀ (i : Fin m) (j : Fin n),
          DifferentiableAt ℝ (fun x : ℝ => Hz w P F S t (x : ℂ) i j) s) ∧
        fro (dHz w P F S t s) ≤ C / s ^ 2) := by
  obtain ⟨s₁, hs₁, hs₁le⟩ : ∃ s₁ : ℝ, 0 < s₁ ∧ ∀ s ∈ I, s₁ ≤ s := by
    by_cases h : I.Nonempty
    · refine ⟨sInf I, hIpos (hI.sInf_mem h), fun s hs => csInf_le hI.bddBelow hs⟩
    · exact ⟨1, one_pos, fun s hs => (h ⟨s, hs⟩).elim⟩
  obtain ⟨C₁, h₁⟩ := thm_app_drift_mixed_ii_sector (3 * s₁ / 4) (by positivity) CS γ
  obtain ⟨C₂, h₂⟩ := thm_app_drift_mixed_ii_sector 1 one_pos CS γ
  refine ⟨16 * max C₁ 0 / (3 * s₁ ^ 2), 16 * max C₂ 0 / 3, ?_⟩
  intro w hw m n B Ω _ P _ S F t hγ hS1 hS2
  have hD : Muon.Drift.DriftBound F CS γ := ⟨hS1, hS2, hγ⟩
  obtain ⟨hint, hb1⟩ := h₁ Ω m n B P w F S t hw hD
  obtain ⟨-, hb2⟩ := h₂ Ω m n B P w F S t hw hD
  refine ⟨fun z hz i j => hint z hz.1 i j, ?_, ?_⟩
  · intro s hs
    have hsp : 0 < s := lt_of_lt_of_le hs₁ (hs₁le s hs)
    have hcore := fm_dHz_core P hw F S t s (3 * s₁ / 4) (max C₁ 0) hsp
      (by linarith [hs₁le s hs]) (le_max_right _ _) (by
        intro z hz1 hz2
        have hre : 0 < z.re := lt_of_lt_of_le (by positivity) hz1
        refine (show fro (Hz w P F S t z) ≤ C₁ / z.re from hb1 z hz1 hz2).trans ?_
        exact div_le_div_of_nonneg_right (le_max_left _ _) hre.le)
    refine ⟨hcore.1, hcore.2.trans ?_⟩
    exact div_le_div_of_nonneg_left (by positivity) (by positivity)
      (by nlinarith [hs₁le s hs])
  · intro s hs
    have hsp : 0 < s := by linarith
    have hcore := fm_dHz_core P hw F S t s 1 (max C₂ 0) hsp
      (by linarith) (le_max_right _ _) (by
        intro z hz1 hz2
        have hre : 0 < z.re := lt_of_lt_of_le one_pos hz1
        refine (show fro (Hz w P F S t z) ≤ C₂ / z.re from hb2 z hz1 hz2).trans ?_
        exact div_le_div_of_nonneg_right (le_max_left _ _) hre.le)
    refine ⟨hcore.1, hcore.2.trans (le_of_eq ?_)⟩
    field_simp

/-! ### Private helpers for (iii) -/

private lemma fm_fro_nonneg {k l : ℕ} (A : Mat k l) : 0 ≤ fro A := Real.sqrt_nonneg _

private lemma fm_fro_sq {k l : ℕ} (A : Mat k l) : fro A ^ 2 = ∑ i, ∑ j, A i j ^ 2 := by
  unfold fro
  rw [Real.sq_sqrt (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => by positivity)]
  simp [Real.norm_eq_abs, sq_abs]

private lemma fm_abs_entry_le_fro {k l : ℕ} (A : Mat k l) (i : Fin k) (j : Fin l) :
    |A i j| ≤ fro A := by
  have h1 : A i j ^ 2 ≤ fro A ^ 2 := by
    rw [fm_fro_sq]
    calc A i j ^ 2 ≤ ∑ j', A i j' ^ 2 :=
          Finset.single_le_sum (f := fun j' => A i j' ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ j)
      _ ≤ ∑ i', ∑ j', A i' j' ^ 2 :=
          Finset.single_le_sum (f := fun i' => ∑ j', A i' j' ^ 2)
            (fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _) (Finset.mem_univ i)
  exact abs_le_of_sq_le_sq' h1 (fm_fro_nonneg _) |> fun h => abs_le.2 ⟨h.1, h.2⟩

private lemma fm_inner_le {m n : ℕ} (a b : Mat m n) :
    ∑ i, ∑ j, a i j * b i j ≤ fro a * fro b := by
  have e : ∀ x : Mat m n, fro x = Real.sqrt (∑ i, ∑ j, x i j ^ 2) := by
    intro x; unfold fro; simp [Real.norm_eq_abs, sq_abs]
  rw [e, e]
  have := Real.sum_mul_le_sqrt_mul_sqrt (Finset.univ : Finset (Fin m × Fin n))
    (fun x => a x.1 x.2) (fun x => b x.1 x.2)
  simpa [Fintype.sum_prod_type] using this

private lemma fm_fro_integral_le {α : Type*} [MeasurableSpace α] (μ : Measure α) {m n : ℕ}
    (F : α → Mat m n) (hF : ∀ i j, Integrable (fun x => F x i j) μ) (g : α → ℝ)
    (hg : Integrable g μ) (h : ∀ᵐ x ∂μ, fro (F x) ≤ g x) :
    fro (Matrix.of fun i j => ∫ x, F x i j ∂μ) ≤ ∫ x, g x ∂μ := by
  set E : Mat m n := Matrix.of fun i j => ∫ x, F x i j ∂μ with hE
  have hint : ∀ i k, Integrable (fun x => E i k * F x i k) μ := fun i k => (hF i k).const_mul _
  have h1 : fro E ^ 2 = ∫ x, ∑ i, ∑ k, E i k * F x i k ∂μ := by
    rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun k _ => hint i k))]
    rw [fm_fro_sq]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_finsetSum _ (fun k _ => hint i k)]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [integral_const_mul]
    simp only [hE, Matrix.of_apply]
    ring
  have h2 : ∫ x, ∑ i, ∑ k, E i k * F x i k ∂μ ≤ ∫ x, fro E * g x ∂μ := by
    refine integral_mono_ae (integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun k _ =>
      hint i k) (hg.const_mul _) ?_
    filter_upwards [h] with x hx
    exact (fm_inner_le E (F x)).trans (mul_le_mul_of_nonneg_left hx (fm_fro_nonneg _))
  rw [integral_const_mul] at h2
  have hG : 0 ≤ ∫ x, g x ∂μ :=
    integral_nonneg_of_ae (by filter_upwards [h] with x hx using (fm_fro_nonneg _).trans hx)
  have h3 : fro E ^ 2 ≤ fro E * ∫ x, g x ∂μ := h1 ▸ h2
  by_contra hc
  push Not at hc
  nlinarith [fm_fro_nonneg E]

private lemma fm_posDef {m n : ℕ} (M : Mat m n) {c : ℝ} (hc : 0 < c) :
    (M * Mᵀ + c • (1 : Mat m m)).PosDef := by
  have h0 : (M * Mᵀ).PosSemidef := by
    simpa using Matrix.posSemidef_self_mul_conjTranspose M
  have hd : (c • (1 : Mat m m)).PosDef := by
    have : c • (1 : Mat m m) = Matrix.diagonal (fun _ : Fin m => c) := by
      ext i j
      by_cases h : i = j <;> simp [h]
    rw [this]
    exact Matrix.posDef_diagonal_iff.mpr (fun _ => hc)
  rw [add_comm]
  exact hd.add_posSemidef h0

open scoped Matrix.Norms.L2Operator in
private lemma fm_abs_entry_le_opNorm {p q : ℕ} (K : Mat p q) (i : Fin p) (j : Fin q) :
    |K i j| ≤ opNorm K := by
  have h1 := Matrix.l2_opNorm_mulVec K (EuclideanSpace.single j (1 : ℝ))
  have h2 := PiLp.norm_apply_le ((EuclideanSpace.equiv (Fin p) ℝ).symm
    (K *ᵥ ⇑(EuclideanSpace.single j (1 : ℝ)))) i
  have h3 : ((EuclideanSpace.equiv (Fin p) ℝ).symm
      (K *ᵥ ⇑(EuclideanSpace.single j (1 : ℝ)))) i = K i j := by
    simp [Matrix.mulVec, dotProduct, EuclideanSpace.single_apply]
  simp only [EuclideanSpace.norm_single, norm_one, mul_one] at h1
  rw [h3, Real.norm_eq_abs] at h2
  rw [opNorm_eq_norm]
  linarith

private lemma fm_Phi_cont {m n : ℕ} {ϱ : ℝ} (hϱ : 0 < ϱ) (i : Fin m) (j : Fin n) :
    Continuous (fun p : Mat m n × ℝ =>
      ((p.1 * p.1ᵀ + (ϱ + p.2 ^ 2) • (1 : Mat m m))⁻¹ * p.1) i j) := by
  have hA : Continuous (fun p : Mat m n × ℝ => p.1 * p.1ᵀ + (ϱ + p.2 ^ 2) • (1 : Mat m m)) := by
    refine Continuous.add (continuous_fst.matrix_mul continuous_fst.matrix_transpose) ?_
    exact (continuous_const.add (continuous_snd.pow 2)).smul continuous_const
  have hI : Continuous (fun p : Mat m n × ℝ => (p.1 * p.1ᵀ + (ϱ + p.2 ^ 2) • (1 : Mat m m))⁻¹) := by
    rw [continuous_iff_continuousAt]
    intro p
    have hdet : (p.1 * p.1ᵀ + (ϱ + p.2 ^ 2) • (1 : Mat m m)).det ≠ 0 :=
      (fm_posDef p.1 (by positivity : 0 < ϱ + p.2 ^ 2)).det_pos.ne'
    have h1 := continuousAt_matrix_inv (p.1 * p.1ᵀ + (ϱ + p.2 ^ 2) • (1 : Mat m m))
      (by rw [Ring.inverse_eq_inv']; exact continuousAt_inv₀ hdet)
    exact h1.comp_of_eq hA.continuousAt rfl
  exact (continuous_apply j).comp ((continuous_apply i).comp (hI.matrix_mul continuous_fst))

private lemma fm_meas_gen {Ω : Type*} [MeasurableSpace Ω] {m n : ℕ} {ϱ : ℝ} (hϱ : 0 < ϱ) (i : Fin m) (j : Fin n)
   (WB : Ω → Mat m n) (hWBm : Measurable WB) :
   Measurable (fun p : Ω × ℝ => ((WB p.1 * (WB p.1)ᵀ + (ϱ + p.2 ^ 2) • (1 : Mat m m))⁻¹ * WB p.1) i j) := by
  have hmp : Measurable (fun p : Ω × ℝ => (WB p.1, p.2)) := (hWBm.comp measurable_fst).prodMk measurable_snd
  have hΦ : Measurable (fun p : Mat m n × ℝ =>
      ((p.1 * p.1ᵀ + (ϱ + p.2 ^ 2) • (1 : Mat m m))⁻¹ * p.1) i j) := (fm_Phi_cont hϱ i j).measurable
  exact Measurable.comp (g := fun p : Mat m n × ℝ =>
      ((p.1 * p.1ᵀ + (ϱ + p.2 ^ 2) • (1 : Mat m m))⁻¹ * p.1) i j) (f := fun p : Ω × ℝ => (WB p.1, p.2)) hΦ hmp

private lemma fm_swap {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {m n : ℕ} (WB : Ω → Mat m n) (hWBm : Measurable WB)
    {ϱ : ℝ} (hϱ : 0 < ϱ) (i : Fin m) (j : Fin n) :
    Integrable (fun u : ℝ => ∫ ω, Muon.DetEquiv.Xs (WB ω) (ϱ + u ^ 2) i j ∂P) (volume.restrict (Ioi 0)) ∧
      ∫ ω, Q ϱ (WB ω) i j ∂P =
        (2 / Real.pi) * ∫ u in Ioi (0 : ℝ), ∫ ω, Muon.DetEquiv.Xs (WB ω) (ϱ + u ^ 2) i j ∂P := by
  set g : Ω × ℝ → ℝ := fun p =>
    ((WB p.1 * (WB p.1)ᵀ + (ϱ + p.2 ^ 2) • (1 : Mat m m))⁻¹ * WB p.1) i j with hg
  have hgm : Measurable g := fm_meas_gen hϱ i j WB hWBm
  have hcont := fun ω => lem_app_setup_contour ϱ hϱ (WB ω)
  have hnorm : ∀ ω, ∀ u : ℝ, ‖g (ω, u)‖ ≤ nuc ((WB ω * (WB ω)ᵀ + (ϱ + u ^ 2) • (1 : Mat m m))⁻¹ * WB ω) := by
    intro ω u
    rw [Real.norm_eq_abs]
    exact (fm_abs_entry_le_opNorm ((WB ω * (WB ω)ᵀ + (ϱ + u ^ 2) • (1 : Mat m m))⁻¹ * WB ω) i j).trans
      (opNorm_le_nuc _)
  have hint : Integrable g (P.prod (volume.restrict (Ioi (0 : ℝ)))) := by
    rw [integrable_prod_iff hgm.aestronglyMeasurable]
    refine ⟨Filter.Eventually.of_forall fun ω => (hcont ω).2.1 i j, ?_⟩
    refine Integrable.of_bound (C := Real.pi / 2 * (min m n : ℝ)) ?_ ?_
    · exact hgm.norm.stronglyMeasurable.integral_prod_right'.aestronglyMeasurable
    · refine Filter.Eventually.of_forall fun ω => ?_
      have h0 : 0 ≤ ∫ u in Ioi (0 : ℝ), ‖g (ω, u)‖ := integral_nonneg fun u => norm_nonneg _
      rw [Real.norm_eq_abs, abs_of_nonneg h0]
      refine le_trans (integral_mono ((hcont ω).2.1 i j).norm (hcont ω).2.2.1 fun u => hnorm ω u)
        (hcont ω).2.2.2
  have hint' : Integrable (Function.uncurry fun ω u => g (ω, u))
      (P.prod (volume.restrict (Ioi (0 : ℝ)))) := hint
  have hswap := integral_integral_swap hint'
  have hH : ∀ u : ℝ, ∫ ω, Muon.DetEquiv.Xs (WB ω) (ϱ + u ^ 2) i j ∂P = ∫ ω, g (ω, u) ∂P := fun u => by
    simp only [Muon.DetEquiv.Xs, Muon.DetEquiv.Rs, hg]
  refine ⟨?_, ?_⟩
  · simp_rw [hH]
    exact hint.integral_prod_right
  · have hE : ∫ ω, Q ϱ (WB ω) i j ∂P = ∫ ω, ((2 / Real.pi) * ∫ u in Ioi (0 : ℝ), g (ω, u)) ∂P := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
      exact (hcont ω).1 i j
    rw [hE, integral_const_mul]
    simp_rw [hH]
    rw [← hswap]


private lemma fm_vec_entry_le {k : ℕ} (v : Vec k) (hv : v ⬝ᵥ v = 1) (i : Fin k) : |v i| ≤ 1 := by
  have h1 : v i ^ 2 ≤ ∑ l, v l ^ 2 :=
    Finset.single_le_sum (f := fun l => v l ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ i)
  have h2 : ∑ l, v l ^ 2 = 1 := by
    rw [← hv]; simp [dotProduct, sq]
  exact abs_le_one_iff_mul_self_le_one.2 (by nlinarith)

private lemma fm_Q_deriv {m n : ℕ} (K : Mat m n) :
    ∃ d : ℝ → Mat m n, (∀ r : ℝ, 0 < r → ∀ i j, HasDerivAt (fun x : ℝ => Q x K i j) (d r i j) r) ∧
      ∀ r : ℝ, 0 < r → ∀ i j, |d r i j| ≤ (m : ℝ) / (2 * r) := by
  obtain ⟨p, q, hp, hq, hK⟩ := Muon.Foundations.svd_rect_exists K
  set s : Fin K.rank → ℝ := fun k => (Matrix.toEuclideanLin K).singularValues (k : ℕ) with hsdef
  have hpos : ∀ k, 0 < s k := fun k => Muon.Foundations.singularValues_pos_of_lt_rank K k.2
  have hrank : K.rank ≤ m := Matrix.rank_le_height K
  have hQ : ∀ x : ℝ, 0 ≤ x → ∀ i j, Q x K i j =
      ∑ k, (s k / Real.sqrt (s k ^ 2 + x)) * (p k i * q k j) := by
    intro x hx i j
    rw [Q_eq_svd x hx K s p q hpos (fun k l => hp k l) (fun k l => hq k l) hK]
    simp only [Matrix.sum_apply, Matrix.smul_apply, Matrix.vecMulVec_apply, smul_eq_mul]
  let dd : ℝ → ℝ → Fin K.rank → ℝ := fun x _ k =>
    (0 * Real.sqrt (s k ^ 2 + x) - s k * ((1 : ℝ) / (2 * Real.sqrt (s k ^ 2 + x)))) /
      (Real.sqrt (s k ^ 2 + x)) ^ 2
  refine ⟨fun r => Matrix.of fun i j => ∑ k, dd r r k * (p k i * q k j), ?_, ?_⟩
  · intro r hr i j
    have hterm : ∀ k, HasDerivAt (fun x : ℝ => (s k / Real.sqrt (s k ^ 2 + x)) * (p k i * q k j))
        (dd r r k * (p k i * q k j)) r := by
      intro k
      have h1 : HasDerivAt (fun x : ℝ => s k ^ 2 + x) 1 r := by
        simpa using (hasDerivAt_id r).const_add (s k ^ 2)
      have hne : s k ^ 2 + r ≠ 0 := by have := hpos k; positivity
      have h2 := h1.sqrt hne
      have h3 := (hasDerivAt_const r (s k)).div h2 (Real.sqrt_ne_zero'.2 (by have := hpos k; positivity))
      exact h3.mul_const _
    have hsum := HasDerivAt.fun_sum (u := Finset.univ) (fun k _ => hterm k)
    refine (hsum.congr_of_eventuallyEq ?_)
    · filter_upwards [Ioi_mem_nhds hr] with x hx
      exact hQ x (le_of_lt hx) i j
  · intro r hr i j
    simp only [Matrix.of_apply]
    have hb : ∀ k, |dd r r k * (p k i * q k j)| ≤ 1 / (2 * r) := by
      intro k
      have hk := hpos k
      set a := Real.sqrt (s k ^ 2 + r) with ha
      have ha0 : 0 < a := Real.sqrt_pos.2 (by positivity)
      have ha2 : a ^ 2 = s k ^ 2 + r := Real.sq_sqrt (by positivity)
      have hsa : s k ≤ a := by nlinarith
      have hra : r ≤ a ^ 2 := by nlinarith
      have hd : |dd r r k| ≤ 1 / (2 * r) := by
        have : dd r r k = -(s k / (2 * a ^ 3)) := by
          simp only [dd, ← ha]; field_simp; ring
        rw [this, abs_neg, abs_of_nonneg (by positivity)]
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith [mul_pos ha0 ha0, mul_pos (mul_pos ha0 ha0) ha0]
      have hpq : |p k i * q k j| ≤ 1 := by
        rw [abs_mul]
        exact mul_le_one₀ (fm_vec_entry_le _ (hp k k |>.trans (by simp)) i) (abs_nonneg _)
          (fm_vec_entry_le _ (hq k k |>.trans (by simp)) j)
      rw [abs_mul]
      calc |dd r r k| * |p k i * q k j| ≤ (1 / (2 * r)) * 1 :=
            mul_le_mul hd hpq (abs_nonneg _) (by positivity)
        _ = 1 / (2 * r) := mul_one _
    calc |∑ k, dd r r k * (p k i * q k j)| ≤ ∑ k, |dd r r k * (p k i * q k j)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _k : Fin K.rank, 1 / (2 * r) := Finset.sum_le_sum fun k _ => hb k
      _ = (K.rank : ℝ) * (1 / (2 * r)) := by simp
      _ ≤ (m : ℝ) * (1 / (2 * r)) :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast hrank) (by positivity)
      _ = (m : ℝ) / (2 * r) := by ring


private lemma fm_meas_Q {Ω : Type*} [MeasurableSpace Ω] {m n : ℕ} {ϱ : ℝ} (hϱ : 0 < ϱ)
    {f : Ω → Mat m n} (hf : Measurable f) : Measurable (fun ω => Q ϱ (f ω)) := by
  have hc : Continuous (fun M : Mat m n => Q ϱ M) := by
    have := (continuousOn_Q_pos (m := m) (n := n)).comp
      ((continuous_const.prodMk continuous_id).continuousOn : ContinuousOn (fun M : Mat m n => (ϱ, M)) univ)
      (fun M _ => ⟨hϱ, trivial⟩)
    exact continuousOn_univ.1 this
  exact hc.measurable.comp hf

private lemma fm_Q_entry_bound {m n : ℕ} {ϱ : ℝ} (hϱ : 0 < ϱ) (K : Mat m n) (i : Fin m) (j : Fin n) :
    |Q ϱ K i j| ≤ Real.sqrt (min m n : ℕ) := by
  obtain ⟨-, h2, h3, -⟩ := lem_app_setup_filter_i ϱ hϱ.le K
  refine (fm_abs_entry_le_fro _ i j).trans (Real.le_sqrt_of_sq_le ?_)
  exact h2.trans (by exact_mod_cast h3)

private lemma fm_integrable_Q {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {m n : ℕ} {ϱ : ℝ} (hϱ : 0 < ϱ) {f : Ω → Mat m n} (hf : Measurable f) (i : Fin m) (j : Fin n) :
    Integrable (fun ω => Q ϱ (f ω) i j) P := by
  refine Integrable.of_bound (C := Real.sqrt (min m n : ℕ)) ?_ ?_
  · exact ((measurable_pi_apply j).comp ((measurable_pi_apply i).comp (fm_meas_Q hϱ hf))).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs]; exact fm_Q_entry_bound hϱ _ i j

private lemma fm_meas_dQ {Ω : Type*} [MeasurableSpace Ω] {m n : ℕ} {ϱ : ℝ} (hϱ : 0 < ϱ)
    {f : Ω → Mat m n} (hf : Measurable f) (i : Fin m) (j : Fin n) :
    Measurable (fun ω => dQ ϱ (f ω) i j) := by
  have hQm : ∀ r : ℝ, 0 < r → Measurable (fun ω => Q r (f ω) i j) := fun r hr =>
    (measurable_pi_apply j).comp ((measurable_pi_apply i).comp (fm_meas_Q hr hf))
  let g : ℕ → Ω → ℝ := fun N ω =>
    ((1 : ℝ) / ((N : ℝ) + 1))⁻¹ * (Q (ϱ + 1 / ((N : ℝ) + 1)) (f ω) i j - Q ϱ (f ω) i j)
  refine measurable_of_tendsto_metrizable (f := g) (fun N => ?_) ?_
  · have hN : (0 : ℝ) < 1 / ((N : ℝ) + 1) := by positivity
    exact ((hQm _ (by linarith)).sub (hQm ϱ hϱ)).const_mul _
  · rw [tendsto_pi_nhds]
    intro ω
    obtain ⟨d, hd, -⟩ := fm_Q_deriv (f ω)
    have hder : HasDerivAt (fun r : ℝ => Q r (f ω) i j) (d ϱ i j) ϱ := hd ϱ hϱ i j
    have hslope := (hasDerivAt_iff_tendsto_slope_zero.1 hder)
    have ht : Tendsto (fun N : ℕ => (1 : ℝ) / ((N : ℝ) + 1)) atTop (𝓝[≠] 0) := by
      refine tendsto_nhdsWithin_iff.2 ⟨tendsto_one_div_add_atTop_nhds_zero_nat, ?_⟩
      exact Filter.Eventually.of_forall fun N => by
        have : (0 : ℝ) < 1 / ((N : ℝ) + 1) := by positivity
        exact this.ne'
    have := hslope.comp ht
    have hdq : dQ ϱ (f ω) i j = d ϱ i j := (hder.deriv)
    rw [hdq]
    refine this.congr fun N => ?_
    simp [g, Function.comp, smul_eq_mul]

private lemma fm_dQ_bound {m n : ℕ} {ϱ : ℝ} (hϱ : 0 < ϱ) (K : Mat m n) (i : Fin m) (j : Fin n) :
    |dQ ϱ K i j| ≤ (m : ℝ) / (2 * ϱ) := by
  obtain ⟨d, hd, hb⟩ := fm_Q_deriv K
  have : dQ ϱ K i j = d ϱ i j := (hd ϱ hϱ i j).deriv
  rw [this]; exact hb ϱ hϱ i j

private lemma fm_integrable_dQ {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {m n : ℕ} {ϱ : ℝ} (hϱ : 0 < ϱ) {f : Ω → Mat m n} (hf : Measurable f) (i : Fin m) (j : Fin n) :
    Integrable (fun ω => dQ ϱ (f ω) i j) P := by
  refine Integrable.of_bound (C := (m : ℝ) / (2 * ϱ)) (fm_meas_dQ hϱ hf i j).aestronglyMeasurable ?_
  exact Filter.Eventually.of_forall fun ω => by
    rw [Real.norm_eq_abs]; exact fm_dQ_bound hϱ _ i j


private lemma fm_hasDerivAt_Q {m n : ℕ} {r : ℝ} (hr : 0 < r) (K : Mat m n) (i : Fin m) (j : Fin n) :
    HasDerivAt (fun x : ℝ => Q x K i j) (dQ r K i j) r := by
  obtain ⟨d, hd, -⟩ := fm_Q_deriv K
  have h := hd r hr i j
  have e : dQ r K i j = d r i j := h.deriv
  rw [e]; exact h

open scoped Matrix.Norms.Frobenius in
private lemma fm_fro_smul {k l : ℕ} (c : ℝ) (A : Mat k l) : fro (c • A) = |c| * fro A := by
  rw [fro_eq_norm, fro_eq_norm, norm_smul, Real.norm_eq_abs]

private lemma fm_core {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {m n : ℕ} (WB : Ω → Mat m n) (hWB : Measurable WB) (ϱlo ϱhi : ℝ) (hlo : 0 < ϱlo)
    (hle : ϱlo ≤ ϱhi) (K : ℝ)
    (hdiff : ∀ s : ℝ, ϱlo / 2 ≤ s → ∀ (i : Fin m) (j : Fin n),
      DifferentiableAt ℝ (fun x : ℝ => ∫ ω, Muon.DetEquiv.Xs (WB ω) x i j ∂P) s)
    (hK : ∀ ϱ : ℝ, ϱlo / 2 ≤ ϱ → ϱ ≤ ϱhi + ϱlo / 2 → ∀ u : ℝ,
      fro (Matrix.of fun i j => ∫ ω, Muon.DetEquiv.Xs (WB ω) (ϱ + u ^ 2) i j ∂P) ≤ K * (1 + u ^ 2)⁻¹ ∧
      fro (Matrix.of fun i j => deriv (fun x : ℝ => ∫ ω, Muon.DetEquiv.Xs (WB ω) x i j ∂P) (ϱ + u ^ 2)) ≤
        K * (1 + u ^ 2)⁻¹) :
    (∀ ϱ ∈ Icc ϱlo ϱhi, ∀ (i : Fin m) (j : Fin n), Integrable (fun ω => Q ϱ (WB ω) i j) P) ∧
    (∀ ϱ ∈ Icc ϱlo ϱhi, ∀ (i : Fin m) (j : Fin n), Integrable (fun ω => dQ ϱ (WB ω) i j) P) ∧
    (∀ ϱ' ∈ Icc ϱlo ϱhi, ∀ ω : Ω, ∀ (i : Fin m) (j : Fin n),
      DifferentiableAt ℝ (fun r : ℝ => Q r (WB ω) i j) ϱ') ∧
    (∀ ϱ' ∈ Icc ϱlo ϱhi,
      fro (mean P (fun ω => Q ϱ' (WB ω))) + fro (mean P (fun ω => dQ ϱ' (WB ω))) ≤
        2 * ((2 / Real.pi) * (K * ∫ u in Ioi (0 : ℝ), (1 + u ^ 2)⁻¹))) := by
  refine ⟨fun ϱ hϱ i j => fm_integrable_Q (lt_of_lt_of_le hlo hϱ.1) hWB i j,
    fun ϱ hϱ i j => fm_integrable_dQ (lt_of_lt_of_le hlo hϱ.1) hWB i j,
    fun ϱ hϱ ω i j => (fm_hasDerivAt_Q (lt_of_lt_of_le hlo hϱ.1) (WB ω) i j).differentiableAt, ?_⟩
  intro ϱ' hϱ'
  have hϱ0 : 0 < ϱ' := lt_of_lt_of_le hlo hϱ'.1
  set hf : Fin m → Fin n → ℝ → ℝ := fun i j x => ∫ ω, Muon.DetEquiv.Xs (WB ω) x i j ∂P with hhf
  set g : ℝ → ℝ := fun u => K * (1 + u ^ 2)⁻¹ with hg
  have hgint : IntegrableOn g (Ioi (0 : ℝ)) :=
    (integrable_inv_one_add_sq.const_mul K).integrableOn
  have hgval : ∫ u in Ioi (0 : ℝ), g u = K * ∫ u in Ioi (0 : ℝ), (1 + u ^ 2)⁻¹ := by
    simp only [hg]; rw [integral_const_mul]
  have hswap := fun i j => fm_swap (P := P) WB hWB hϱ0 i j
  have hconst : 0 ≤ 2 / Real.pi := by positivity
  -- part (a)
  have hA : fro (mean P (fun ω => Q ϱ' (WB ω))) ≤ (2 / Real.pi) * (K * ∫ u in Ioi (0 : ℝ), (1 + u ^ 2)⁻¹) := by
    have hrep : mean P (fun ω => Q ϱ' (WB ω)) =
        (2 / Real.pi) • (Matrix.of fun i j => ∫ u in Ioi (0 : ℝ), hf i j (ϱ' + u ^ 2)) := by
      ext i j
      simp only [mean, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul]
      exact (hswap i j).2
    rw [hrep, fm_fro_smul, abs_of_nonneg hconst]
    refine mul_le_mul_of_nonneg_left ?_ hconst
    rw [← hgval]
    exact fm_fro_integral_le (volume.restrict (Ioi (0 : ℝ))) (fun u => Matrix.of fun i j => hf i j (ϱ' + u ^ 2))
      (fun i j => (hswap i j).1) g hgint
      (ae_restrict_of_forall_mem measurableSet_Ioi fun u _ =>
        (hK ϱ' (by linarith [hϱ'.1]) (by linarith [hϱ'.2]) u).1)
  -- part (b)
  have hε : (0 : ℝ) < ϱlo / 2 := by linarith
  have hball : ∀ x : ℝ, x ∈ Metric.ball ϱ' (ϱlo / 2) → ϱlo / 2 < x ∧ x < ϱhi + ϱlo / 2 := by
    intro x hx
    have := abs_lt.1 (by simpa [Real.dist_eq] using hx)
    constructor <;> linarith [hϱ'.1, hϱ'.2, this.1, this.2]
  have hRall : ∀ i j, Integrable (fun u : ℝ => deriv (hf i j) (ϱ' + u ^ 2)) (volume.restrict (Ioi (0 : ℝ))) ∧
      HasDerivAt (fun ϱ : ℝ => ∫ u in Ioi (0 : ℝ), hf i j (ϱ + u ^ 2))
        (∫ u in Ioi (0 : ℝ), deriv (hf i j) (ϱ' + u ^ 2)) ϱ' := by
    intro i j
    refine hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume.restrict (Ioi (0 : ℝ)))
      (F := fun ϱ u => hf i j (ϱ + u ^ 2)) (F' := fun ϱ u => deriv (hf i j) (ϱ + u ^ 2))
      (bound := g) (Metric.ball_mem_nhds ϱ' hε) ?_ ?_ ?_ ?_ hgint ?_
    · filter_upwards [Metric.ball_mem_nhds ϱ' hε] with x hx
      have hx0 : 0 < x := by linarith [(hball x hx).1]
      exact (fm_swap (P := P) WB hWB hx0 i j).1.aestronglyMeasurable
    · exact (hswap i j).1
    · exact ((measurable_deriv (hf i j)).comp
        (measurable_const.add (measurable_id.pow_const 2))).aestronglyMeasurable
    · refine ae_restrict_of_forall_mem measurableSet_Ioi fun u _ x hx => ?_
      obtain ⟨hx1, hx2⟩ := hball x hx
      rw [Real.norm_eq_abs]
      refine (fm_abs_entry_le_fro (Matrix.of fun i j => deriv (hf i j) (x + u ^ 2)) i j).trans ?_
      exact (hK x hx1.le hx2.le u).2
    · refine ae_restrict_of_forall_mem measurableSet_Ioi fun u _ x hx => ?_
      obtain ⟨hx1, hx2⟩ := hball x hx
      have hd := (hdiff (x + u ^ 2) (by nlinarith [sq_nonneg u]) i j).hasDerivAt
      exact hd.comp_add_const x (u ^ 2)
  have hent : ∀ i j, ∫ ω, dQ ϱ' (WB ω) i j ∂P =
      (2 / Real.pi) * ∫ u in Ioi (0 : ℝ), deriv (hf i j) (ϱ' + u ^ 2) := by
    intro i j
    have hL : HasDerivAt (fun ϱ : ℝ => ∫ ω, Q ϱ (WB ω) i j ∂P) (∫ ω, dQ ϱ' (WB ω) i j ∂P) ϱ' := by
      refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (F := fun ϱ ω => Q ϱ (WB ω) i j)
        (F' := fun ϱ ω => dQ ϱ (WB ω) i j) (bound := fun _ => (m : ℝ) / ϱlo)
        (Metric.ball_mem_nhds ϱ' hε) ?_ ?_ ?_ ?_ (integrable_const _) ?_).2
      · filter_upwards [Metric.ball_mem_nhds ϱ' hε] with x hx
        have hx0 : 0 < x := by linarith [(hball x hx).1]
        exact (fm_integrable_Q hx0 hWB i j).aestronglyMeasurable
      · exact fm_integrable_Q hϱ0 hWB i j
      · exact (fm_meas_dQ hϱ0 hWB i j).aestronglyMeasurable
      · refine Filter.Eventually.of_forall fun ω x hx => ?_
        have hx0 : 0 < x := by linarith [(hball x hx).1]
        rw [Real.norm_eq_abs]
        refine (fm_dQ_bound hx0 _ i j).trans ?_
        rw [div_le_div_iff₀ (by positivity) hlo]
        nlinarith [Nat.cast_nonneg (α := ℝ) m, (hball x hx).1]
      · exact Filter.Eventually.of_forall fun ω x hx => by
          have hx0 : 0 < x := by linarith [(hball x hx).1]
          exact fm_hasDerivAt_Q hx0 (WB ω) i j
    have hR := ((hRall i j).2.const_mul (2 / Real.pi))
    have hL' : HasDerivAt (fun ϱ : ℝ => ∫ ω, Q ϱ (WB ω) i j ∂P)
        ((2 / Real.pi) * ∫ u in Ioi (0 : ℝ), deriv (hf i j) (ϱ' + u ^ 2)) ϱ' := by
      refine hR.congr_of_eventuallyEq ?_
      filter_upwards [Ioi_mem_nhds hϱ0] with x hx
      exact (fm_swap (P := P) WB hWB hx i j).2
    exact hL.unique hL'
  have hB : fro (mean P (fun ω => dQ ϱ' (WB ω))) ≤ (2 / Real.pi) * (K * ∫ u in Ioi (0 : ℝ), (1 + u ^ 2)⁻¹) := by
    have hrep : mean P (fun ω => dQ ϱ' (WB ω)) =
        (2 / Real.pi) • (Matrix.of fun i j => ∫ u in Ioi (0 : ℝ), deriv (hf i j) (ϱ' + u ^ 2)) := by
      ext i j
      simp only [mean, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul]
      exact hent i j
    rw [hrep, fm_fro_smul, abs_of_nonneg hconst]
    refine mul_le_mul_of_nonneg_left ?_ hconst
    rw [← hgval]
    exact fm_fro_integral_le (volume.restrict (Ioi (0 : ℝ)))
      (fun u => Matrix.of fun i j => deriv (hf i j) (ϱ' + u ^ 2))
      (fun i j => (hRall i j).1) g hgint
      (ae_restrict_of_forall_mem measurableSet_Ioi fun u _ =>
        (hK ϱ' (by linarith [hϱ'.1]) (by linarith [hϱ'.2]) u).2)
  linarith


private lemma fm_Xz_ofReal {m n : ℕ} (K : Mat m n) {x : ℝ} (hx : 0 < x) (i : Fin m) (j : Fin n) :
    Xz K (x : ℂ) i j = ((Muon.DetEquiv.Xs K x i j : ℝ) : ℂ) := by
  set A : Mat m m := K * Kᵀ + x • (1 : Mat m m) with hA
  have hdet : A.det ≠ 0 := (fm_posDef K hx).det_pos.ne'
  have h1 : (K * Kᵀ).map (fun r : ℝ => (r : ℂ)) - (-(x : ℂ)) • (1 : Matrix (Fin m) (Fin m) ℂ) =
      A.map (fun r : ℝ => (r : ℂ)) := by
    ext a b
    by_cases h : a = b <;> simp [hA, Matrix.map_apply, h]
  have e : A * A⁻¹ = 1 := Matrix.mul_nonsing_inv A (isUnit_iff_ne_zero.2 hdet)
  have h2 : A.map (fun r : ℝ => (r : ℂ)) * (A⁻¹).map (fun r : ℝ => (r : ℂ)) = 1 := by
    have := Matrix.map_mul (L := A) (M := A⁻¹) (f := Complex.ofRealHom)
    rw [e, Matrix.map_one _ (map_zero _) (map_one _)] at this
    exact this.symm
  have h4 : Rres K (-(x : ℂ)) = (A⁻¹).map (fun r : ℝ => (r : ℂ)) := by
    unfold Rres
    rw [h1]
    exact Matrix.inv_eq_right_inv h2
  have h5 : Xz K (x : ℂ) = (Muon.DetEquiv.Xs K x).map (fun r : ℝ => (r : ℂ)) := by
    unfold Xz
    rw [h4]
    have := Matrix.map_mul (L := A⁻¹) (M := K) (f := Complex.ofRealHom)
    exact this.symm
  rw [h5]; rfl


private lemma fm_split (f CI C : ℝ) (k : ℕ) (hk : 1 ≤ k) (s u : ℝ) (hsu : u ^ 2 ≤ s)
    (h1 : u ^ 2 ≤ 4 → f ≤ CI) (h2 : 4 < u ^ 2 → f ≤ C / s ^ k) :
    f ≤ (5 * max CI 0 + 2 * max C 0) * (1 + u ^ 2)⁻¹ := by
  have hu : 0 < 1 + u ^ 2 := by positivity
  have hmc := le_max_right CI 0
  have hmC := le_max_right C 0
  by_cases hc : u ^ 2 ≤ 4
  · have h := h1 hc
    have e1 : max CI 0 ≤ 5 * max CI 0 * (1 + u ^ 2)⁻¹ := by
      have hi : (5 : ℝ)⁻¹ ≤ (1 + u ^ 2)⁻¹ := inv_anti₀ hu (by linarith)
      calc max CI 0 = 5 * max CI 0 * 5⁻¹ := by ring
        _ ≤ 5 * max CI 0 * (1 + u ^ 2)⁻¹ := mul_le_mul_of_nonneg_left hi (by positivity)
    have e2 : 0 ≤ 2 * max C 0 * (1 + u ^ 2)⁻¹ := by positivity
    calc f ≤ CI := h
      _ ≤ max CI 0 := le_max_left _ _
      _ ≤ 5 * max CI 0 * (1 + u ^ 2)⁻¹ := e1
      _ ≤ _ := by nlinarith
  · push Not at hc
    have h := h2 hc
    have hs1 : 1 ≤ s := by linarith
    have hs0 : 0 < s := by linarith
    have hsk : s ≤ s ^ k := by
      calc s = s ^ 1 := (pow_one s).symm
        _ ≤ s ^ k := pow_le_pow_right₀ hs1 hk
    have hMC : 0 ≤ max C 0 := le_max_right _ _
    have e1 : C / s ^ k ≤ max C 0 / s ^ k :=
      div_le_div_of_nonneg_right (le_max_left C 0) (by positivity)
    have e2 : max C 0 / s ^ k ≤ max C 0 / s :=
      div_le_div_of_nonneg_left hMC hs0 hsk
    have e3 : max C 0 / s ≤ max C 0 / u ^ 2 :=
      div_le_div_of_nonneg_left hMC (by positivity) hsu
    have e4 : max C 0 / u ^ 2 ≤ 2 * max C 0 * (1 + u ^ 2)⁻¹ := by
      have hu2 : 0 < u ^ 2 := by positivity
      have hi : (2 * u ^ 2)⁻¹ ≤ (1 + u ^ 2)⁻¹ := inv_anti₀ hu (by linarith)
      calc max C 0 / u ^ 2 = 2 * max C 0 * (2 * u ^ 2)⁻¹ := by field_simp
        _ ≤ 2 * max C 0 * (1 + u ^ 2)⁻¹ := mul_le_mul_of_nonneg_left hi (by positivity)
    have e5 : 0 ≤ 5 * max CI 0 * (1 + u ^ 2)⁻¹ := by positivity
    calc f ≤ C / s ^ k := h
      _ ≤ 2 * max C 0 * (1 + u ^ 2)⁻¹ := e1.trans (e2.trans (e3.trans e4))
      _ ≤ _ := by nlinarith

private lemma fm_fro_ofReal {m n : ℕ} (a : Fin m → Fin n → ℝ) :
    fro (Matrix.of fun i j => ((a i j : ℝ) : ℂ)) = fro (Matrix.of a) := by
  unfold fro
  simp [Complex.norm_real]


private lemma fm_core2 {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {m n : ℕ} (WB : Ω → Mat m n) (hWB : Measurable WB) (ϱlo ϱhi : ℝ) (hlo : 0 < ϱlo)
    (hle : ϱlo ≤ ϱhi) (CI1 C1 CI2 C2 : ℝ) (H : ℂ → Matrix (Fin m) (Fin n) ℂ)
    (hH : ∀ s : ℝ, 0 < s → ∀ (i : Fin m) (j : Fin n),
      H (s : ℂ) i j = ((∫ ω, Muon.DetEquiv.Xs (WB ω) s i j ∂P : ℝ) : ℂ))
    (hI1 : ∀ s : ℝ, s ∈ Icc (ϱlo / 2) (ϱhi + ϱlo / 2 + 4) → fro (H (s : ℂ)) ≤ CI1)
    (hC1 : ∀ s : ℝ, 1 ≤ s → fro (H (s : ℂ)) ≤ C1 / s)
    (hD2 : ∀ s : ℝ, s ∈ Icc (ϱlo / 2) (ϱhi + ϱlo / 2 + 4) →
      (∀ (i : Fin m) (j : Fin n), DifferentiableAt ℝ (fun x : ℝ => H (x : ℂ) i j) s) ∧
        fro (Matrix.of fun i j => deriv (fun x : ℝ => H (x : ℂ) i j) s) ≤ CI2)
    (hDC : ∀ s : ℝ, 2 ≤ s →
      (∀ (i : Fin m) (j : Fin n), DifferentiableAt ℝ (fun x : ℝ => H (x : ℂ) i j) s) ∧
        fro (Matrix.of fun i j => deriv (fun x : ℝ => H (x : ℂ) i j) s) ≤ C2 / s ^ 2) :
    (∀ ϱ ∈ Icc ϱlo ϱhi, ∀ (i : Fin m) (j : Fin n), Integrable (fun ω => Q ϱ (WB ω) i j) P) ∧
    (∀ ϱ ∈ Icc ϱlo ϱhi, ∀ (i : Fin m) (j : Fin n), Integrable (fun ω => dQ ϱ (WB ω) i j) P) ∧
    (∀ ϱ' ∈ Icc ϱlo ϱhi, ∀ ω : Ω, ∀ (i : Fin m) (j : Fin n),
      DifferentiableAt ℝ (fun r : ℝ => Q r (WB ω) i j) ϱ') ∧
    (∀ ϱ' ∈ Icc ϱlo ϱhi,
      fro (mean P (fun ω => Q ϱ' (WB ω))) + fro (mean P (fun ω => dQ ϱ' (WB ω))) ≤
        2 * ((2 / Real.pi) * (((5 * max CI1 0 + 2 * max C1 0) + (5 * max CI2 0 + 2 * max C2 0)) *
          ∫ u in Ioi (0 : ℝ), (1 + u ^ 2)⁻¹))) := by
  set hf : Fin m → Fin n → ℝ → ℝ := fun i j x => ∫ ω, Muon.DetEquiv.Xs (WB ω) x i j ∂P with hhf
  have hdC : ∀ s : ℝ, ϱlo / 2 ≤ s → ∀ (i : Fin m) (j : Fin n),
      DifferentiableAt ℝ (fun x : ℝ => H (x : ℂ) i j) s := by
    intro s hs i j
    by_cases h : s ≤ ϱhi + ϱlo / 2 + 4
    · exact (hD2 s ⟨hs, h⟩).1 i j
    · exact (hDC s (by linarith)).1 i j
  have hev : ∀ s : ℝ, 0 < s → ∀ i j, (fun x : ℝ => H (x : ℂ) i j) =ᶠ[𝓝 s]
      fun x : ℝ => ((hf i j x : ℝ) : ℂ) := by
    intro s hs i j
    filter_upwards [Ioi_mem_nhds hs] with x hx
    exact hH x hx i j
  have hdiff : ∀ s : ℝ, ϱlo / 2 ≤ s → ∀ (i : Fin m) (j : Fin n), DifferentiableAt ℝ (hf i j) s := by
    intro s hs i j
    have hs0 : 0 < s := by linarith
    have h1 := Complex.reCLM.differentiableAt.comp s (hdC s hs i j)
    refine h1.congr_of_eventuallyEq ?_
    filter_upwards [hev s hs0 i j] with x hx
    simp [hx]
  have hder : ∀ s : ℝ, ϱlo / 2 ≤ s → ∀ (i : Fin m) (j : Fin n),
      deriv (fun x : ℝ => H (x : ℂ) i j) s = ((deriv (hf i j) s : ℝ) : ℂ) := by
    intro s hs i j
    have hs0 : 0 < s := by linarith
    have h1 := (hdiff s hs i j).hasDerivAt.ofReal_comp
    exact (h1.congr_of_eventuallyEq (hev s hs0 i j)).deriv
  have hfro1 : ∀ s : ℝ, 0 < s → fro (Matrix.of fun i j => hf i j s) = fro (H (s : ℂ)) := by
    intro s hs
    rw [← fm_fro_ofReal (fun i j => hf i j s)]
    congr 1
    ext i j
    simp [hH s hs i j, hhf]
  have hfro2 : ∀ s : ℝ, ϱlo / 2 ≤ s →
      fro (Matrix.of fun i j => deriv (hf i j) s) =
        fro (Matrix.of fun i j => deriv (fun x : ℝ => H (x : ℂ) i j) s) := by
    intro s hs
    rw [← fm_fro_ofReal (fun i j => deriv (hf i j) s)]
    congr 1
    ext i j
    simp [hder s hs i j]
  refine fm_core WB hWB ϱlo ϱhi hlo hle _ hdiff ?_
  intro ϱ hϱ1 hϱ2 u
  have hs : ϱlo / 2 ≤ ϱ + u ^ 2 := by nlinarith [sq_nonneg u]
  have hs0 : 0 < ϱ + u ^ 2 := by linarith
  have hsu : u ^ 2 ≤ ϱ + u ^ 2 := by linarith
  have hKa : 0 ≤ 5 * max CI2 0 + 2 * max C2 0 := by positivity
  have hKb : 0 ≤ 5 * max CI1 0 + 2 * max C1 0 := by positivity
  have hinv : 0 ≤ (1 + u ^ 2)⁻¹ := by positivity
  constructor
  · rw [hfro1 _ hs0]
    refine (fm_split _ CI1 C1 1 le_rfl (ϱ + u ^ 2) u hsu ?_ ?_).trans ?_
    · intro h4; exact hI1 _ ⟨hs, by linarith⟩
    · intro h4
      rw [pow_one]
      exact hC1 _ (by linarith)
    · exact mul_le_mul_of_nonneg_right (by linarith) hinv
  · rw [hfro2 _ hs]
    refine (fm_split _ CI2 C2 2 (by norm_num) (ϱ + u ^ 2) u hsu ?_ ?_).trans ?_
    · intro h4; exact (hD2 _ ⟨hs, by linarith⟩).2
    · intro h4
      exact (hDC _ (by linarith)).2
    · exact mul_le_mul_of_nonneg_right (by linarith) hinv


private lemma fm_hQ {m n B : ℕ} (F : FrozenParams m n B) :
    Measurable (fun x : Vec m × Vec n =>
      (dotProduct x.1 (Matrix.mulVec F.A x.2)) • (rOut F.C * Muon.outer x.1 x.2 * rIn F.C)) := by
  have hdot : Measurable (fun x : Vec m × Vec n => dotProduct x.1 (Matrix.mulVec F.A x.2)) := by
    show Measurable (fun x : Vec m × Vec n => ∑ i, x.1 i * ∑ j, F.A i j * x.2 j)
    exact Finset.measurable_sum _ (fun i _ => ((measurable_pi_apply i).comp measurable_fst).mul
      (Finset.measurable_sum _ (fun j _ =>
        measurable_const.mul ((measurable_pi_apply j).comp measurable_snd))))
  have hout : Continuous (fun x : Vec m × Vec n => Muon.outer x.1 x.2) :=
    continuous_pi fun i => continuous_pi fun j =>
      ((continuous_apply i).comp continuous_fst).mul ((continuous_apply j).comp continuous_snd)
  have hM : Measurable (fun x : Vec m × Vec n => rOut F.C * Muon.outer x.1 x.2 * rIn F.C) :=
    Continuous.measurable ((continuous_const.matrix_mul hout).matrix_mul continuous_const)
  exact hdot.smul hM

private lemma fm_meas_WB {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {m n B : ℕ}
    (w : ℕ → ℝ) (F : FrozenParams m n B)
    (S : FrozenSamples P m n B) (t : ℤ) : Measurable (Muon.DetEquiv.WeightedBuf w F S t) := by
  haveI : TopologicalSpace.IsCompletelyPseudoMetrizableSpace (Mat m n) :=
    inferInstanceAs (TopologicalSpace.IsCompletelyPseudoMetrizableSpace (Fin m → Fin n → ℝ))
  haveI : SecondCountableTopology (Mat m n) :=
    inferInstanceAs (SecondCountableTopology (Fin m → Fin n → ℝ))
  haveI : MeasurableAdd₂ (Mat m n) := inferInstanceAs (MeasurableAdd₂ (Fin m → Fin n → ℝ))
  have hQ := fm_hQ F
  unfold Muon.DetEquiv.WeightedBuf
  refine Measurable.tsum fun j => ?_
  refine Measurable.const_smul ?_ (w j)
  show Measurable (fun ω => ((B : ℝ))⁻¹ • ∑ a : Fin B,
    (dotProduct (S.zw (t + 1 - (j : ℤ)) a ω).1 (Matrix.mulVec F.A (S.zw (t + 1 - (j : ℤ)) a ω).2)) •
      (rOut F.C * outer (S.zw (t + 1 - (j : ℤ)) a ω).1 (S.zw (t + 1 - (j : ℤ)) a ω).2 * rIn F.C))
  exact (Finset.measurable_sum _ fun a _ => hQ.comp (S.meas _ _)).const_smul ((B : ℝ)⁻¹)

private lemma fm_sector {s : ℝ} (hs : 0 < s) : (s : ℂ) ∈ sectorS := by
  refine ⟨by simpa using hs, ?_⟩
  simp only [Complex.ofReal_im, Complex.ofReal_re, abs_zero]
  positivity

/-- `lem:app-dyn-mean`(iii), `cr-2026-10-23`. Ridge range for a general weight sequence in the class:
for `0 < ϱ₋ ≤ ϱ₊` there is `C`, depending only on `(γ⋆, C_Σ, ϱ₋, ϱ₊)` and chosen before the weights and
the models, such that for every `ϱ' ∈ [ϱ₋, ϱ₊]`: the integrands `Q_ϱ(M_t)` and `∂_ϱ Q_ϱ(M_t)` are integrable
for `ϱ ∈ [ϱ₋, ϱ₊]`, the pointwise ridge derivative exists, and `‖𝔼 Q_{ϱ'}(M_t)‖_F + ‖𝔼 ∂_{ϱ'} Q_{ϱ'}(M_t)‖_F ≤ C`.
Source, verbatim (`sections/05-dynamics/section.tex`, ll. 768–798):
```latex
\begin{lemma}[Finite mean and susceptibility]\label{lem:app-dyn-mean}
In the frozen-state model with $\norm{\Ahat}_\F=1$, $\norm{\Sigmaout},\norm{\Sigmain}\le C_\Sigma$
and $\max(\Nin,\Nout)\le\gamma_\star B$, and with no condition on $\norm{\Ahat}$:
\begin{enumerate}[label=(\roman*)]
\item for every compact $I\subset(0,\infty)$ there is $C_I$ with
$\norm{\mathcal H(z)}_\F\le C_I$ for $z\in\mathbb S$ with $\Ree z\in I$, and
$\norm{\mathcal H(z)}_\F\le C/\Ree z$ for $z\in\mathbb S$ with $\Ree z\ge1$;
\item for real $s$, $\norm{\frac{\dif}{\dif s}\mathcal H(s)}_\F\le C_I$ for $s\in I$ and
$\norm{\frac{\dif}{\dif s}\mathcal H(s)}_\F\le C/s^2$ for $s\ge2$;
\item for $0<\ridge_-\le\ridge'\le\ridge_+$,
$\norm{\EE\,\Qridge{\ridge'}(\Mt)}_\F+\norm{\EE\,\partial_{\ridge'}\Qridge{\ridge'}(\Mt)}_\F\le C$,
with $C$ depending also on $(\ridge_-,\ridge_+)$;
\item for the fixed ridge $\ridge$ there are $C$ and a sequence $r_B\to0$,
depending only on $(\ridge,\gamma_\star,C_\Sigma)$ and on the sequence of
dimensions, such that $\norm{\EE\,\Qridge\ridge(\Mt)}\le C\norm{\Ahat}+r_B$ for
every normalized state.
\end{enumerate}
The constants depend only on $(\gamma_\star,C_\Sigma)$ and on $I$ where
indicated, not on $\Ahat$, on the dimension or on the weights within the
class \cref{eqn:app-de-weightclass}. Consequently, for the stationary chain
of \cref{def:app-dyn-chains} at a deterministic $D$ with
$r_-\le\cR(D)\le r_+$,
\begin{equation}\label{eqn:app-dyn-mean-physical}
\begin{gathered}
\norm{\overline V(D)}_\F\le C,\qquad
\big\|\EE\,\partial_\ell\Qridge\ell(N_0)\big|_{\ell=\ridgephys(D)}\big\|_\F\le C,\\
\norm{\Sigmaout^{1/2}\overline V(D)\Sigmain^{1/2}}\le C\norm{\Sigmaout^{1/2}D\Sigmain^{1/2}}+Cr_B ,
\end{gathered}
\end{equation}
with $C$ depending also on $(r_-,r_+)$.
\end{lemma}
```
-/
theorem lem_app_dyn_mean_iii (γ CS ϱlo ϱhi : ℝ) (hlo : 0 < ϱlo) (hle : ϱlo ≤ ϱhi) :
    ∃ C : ℝ, ∀ (w : ℕ → ℝ), Muon.DetEquiv.WeightClass w →
      ∀ (m n B : ℕ) (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (S : FrozenSamples P m n B) (F : FrozenParams m n B) (t : ℤ),
      ((max m n : ℕ) : ℝ) ≤ γ * (B : ℝ) → opNorm F.C.Sout ≤ CS → opNorm F.C.Sin ≤ CS →
      (∀ ϱ ∈ Icc ϱlo ϱhi, ∀ (i : Fin m) (j : Fin n),
        Integrable (fun ω => Q ϱ (Muon.DetEquiv.WeightedBuf w F S t ω) i j) P) ∧
      (∀ ϱ ∈ Icc ϱlo ϱhi, ∀ (i : Fin m) (j : Fin n),
        Integrable (fun ω => dQ ϱ (Muon.DetEquiv.WeightedBuf w F S t ω) i j) P) ∧
      (∀ ϱ' ∈ Icc ϱlo ϱhi, ∀ ω : Ω, ∀ (i : Fin m) (j : Fin n),
          DifferentiableAt ℝ (fun r : ℝ => Q r (Muon.DetEquiv.WeightedBuf w F S t ω) i j) ϱ') ∧
      (∀ ϱ' ∈ Icc ϱlo ϱhi,
        fro (mean P (fun ω => Q ϱ' (Muon.DetEquiv.WeightedBuf w F S t ω))) +
          fro (mean P (fun ω => dQ ϱ' (Muon.DetEquiv.WeightedBuf w F S t ω))) ≤ C) := by
  set I : Set ℝ := Icc (ϱlo / 2) (ϱhi + ϱlo / 2 + 4) with hI
  have hIc : IsCompact I := isCompact_Icc
  have hIp : I ⊆ Ioi 0 := fun s hs => lt_of_lt_of_le (by linarith) hs.1
  obtain ⟨CI1, C1, h1⟩ := lem_app_dyn_mean_i γ CS I hIc hIp
  obtain ⟨CI2, C2, h2⟩ := lem_app_dyn_mean_ii γ CS I hIc hIp
  refine ⟨2 * ((2 / Real.pi) * (((5 * max CI1 0 + 2 * max C1 0) + (5 * max CI2 0 + 2 * max C2 0)) *
          ∫ u in Ioi (0 : ℝ), (1 + u ^ 2)⁻¹)), ?_⟩
  intro w hw m n B Ω _ P _ S F t hγ hS1 hS2
  obtain ⟨-, hI1, hC1⟩ := h1 w hw m n B Ω P S F t hγ hS1 hS2
  obtain ⟨-, hD2, hDC⟩ := h2 w hw m n B Ω P S F t hγ hS1 hS2
  refine fm_core2 (P := P) (Muon.DetEquiv.WeightedBuf w F S t) (fm_meas_WB w F S t) ϱlo ϱhi hlo hle
    CI1 C1 CI2 C2 (Hz w P F S t) ?_ ?_ ?_ ?_ ?_
  · intro s hs i j
    show ∫ ω, Xz (Muon.DetEquiv.WeightedBuf w F S t ω) (s : ℂ) i j ∂P = _
    rw [integral_congr_ae (Filter.Eventually.of_forall fun ω => fm_Xz_ofReal _ hs i j)]
    exact integral_ofReal
  · intro s hs
    exact hI1 (s : ℂ) (fm_sector (lt_of_lt_of_le (by linarith) hs.1))
      (by rw [Complex.ofReal_re]; exact hs)
  · intro s hs
    have := hC1 (s : ℂ) (fm_sector (by linarith)) (by rw [Complex.ofReal_re]; exact hs)
    simpa using this
  · intro s hs
    exact hD2 s hs
  · intro s hs
    exact hDC s hs

/-- `lem:app-dyn-mean`(iv), `cr-2026-10-23`. Fixed ridge and normalized states, general weights: for a
fixed `ϱ > 0` there is `K`, depending only on `(ϱ, γ⋆, C_Σ)` and chosen before the weights and the
models, such that for every sequence of frozen-state models in the proportional regime (with
`max(N_in,N_out) ≤ γ⋆ B`, `‖Σ‖ ≤ C_Σ`, `B → ∞` through `ProportionalRegime`) and every sequence of weight
sequences `w_k` in the class, there is `r_B → 0`, depending on the models and weights, such that for every
normalized state `Â` (`‖Â‖_F = 1`, via `withState`) and every time `t`, the integrands are integrable and
`‖𝔼 Q_ϱ(M_t)‖ ≤ K‖Â‖ + r_B` (operator norms).
Source, verbatim (`sections/05-dynamics/section.tex`, ll. 768–798):
```latex
\begin{lemma}[Finite mean and susceptibility]\label{lem:app-dyn-mean}
In the frozen-state model with $\norm{\Ahat}_\F=1$, $\norm{\Sigmaout},\norm{\Sigmain}\le C_\Sigma$
and $\max(\Nin,\Nout)\le\gamma_\star B$, and with no condition on $\norm{\Ahat}$:
\begin{enumerate}[label=(\roman*)]
\item for every compact $I\subset(0,\infty)$ there is $C_I$ with
$\norm{\mathcal H(z)}_\F\le C_I$ for $z\in\mathbb S$ with $\Ree z\in I$, and
$\norm{\mathcal H(z)}_\F\le C/\Ree z$ for $z\in\mathbb S$ with $\Ree z\ge1$;
\item for real $s$, $\norm{\frac{\dif}{\dif s}\mathcal H(s)}_\F\le C_I$ for $s\in I$ and
$\norm{\frac{\dif}{\dif s}\mathcal H(s)}_\F\le C/s^2$ for $s\ge2$;
\item for $0<\ridge_-\le\ridge'\le\ridge_+$,
$\norm{\EE\,\Qridge{\ridge'}(\Mt)}_\F+\norm{\EE\,\partial_{\ridge'}\Qridge{\ridge'}(\Mt)}_\F\le C$,
with $C$ depending also on $(\ridge_-,\ridge_+)$;
\item for the fixed ridge $\ridge$ there are $C$ and a sequence $r_B\to0$,
depending only on $(\ridge,\gamma_\star,C_\Sigma)$ and on the sequence of
dimensions, such that $\norm{\EE\,\Qridge\ridge(\Mt)}\le C\norm{\Ahat}+r_B$ for
every normalized state.
\end{enumerate}
The constants depend only on $(\gamma_\star,C_\Sigma)$ and on $I$ where
indicated, not on $\Ahat$, on the dimension or on the weights within the
class \cref{eqn:app-de-weightclass}. Consequently, for the stationary chain
of \cref{def:app-dyn-chains} at a deterministic $D$ with
$r_-\le\cR(D)\le r_+$,
\begin{equation}\label{eqn:app-dyn-mean-physical}
\begin{gathered}
\norm{\overline V(D)}_\F\le C,\qquad
\big\|\EE\,\partial_\ell\Qridge\ell(N_0)\big|_{\ell=\ridgephys(D)}\big\|_\F\le C,\\
\norm{\Sigmaout^{1/2}\overline V(D)\Sigmain^{1/2}}\le C\norm{\Sigmaout^{1/2}D\Sigmain^{1/2}}+Cr_B ,
\end{gathered}
\end{equation}
with $C$ depending also on $(r_-,r_+)$.
\end{lemma}
```
-/
theorem lem_app_dyn_mean_iv (γ CS ϱ : ℝ) (hϱ : 0 < ϱ) :
    ∃ K : ℝ, ∀ (m n B : ℕ → ℕ) (Ω : ℕ → Type) [∀ k, MeasurableSpace (Ω k)]
      (P : ∀ k, Measure (Ω k)) [∀ k, IsProbabilityMeasure (P k)]
      (S : ∀ k, FrozenSamples (P k) (m k) (n k) (B k)) (F : ∀ k, FrozenParams (m k) (n k) (B k))
      (w : ∀ k, ℕ → ℝ),
      (∀ k, Muon.DetEquiv.WeightClass (w k)) →
      (∀ k, ((max (m k) (n k) : ℕ) : ℝ) ≤ γ * (B k : ℝ)) →
      (∀ k, opNorm (F k).C.Sout ≤ CS) → (∀ k, opNorm (F k).C.Sin ≤ CS) →
      ProportionalRegime m n B (fun k => (F k).C) →
      ∃ r : ℕ → ℝ, Tendsto r atTop (𝓝 0) ∧
        ∀ (A : ∀ k, Mat (m k) (n k)) (hA : ∀ k, fro (A k) = 1) (t : ℤ),
          (∀ k (i : Fin (m k)) (j : Fin (n k)),
            Integrable (fun ω => Q ϱ (Muon.DetEquiv.WeightedBuf (w k) (withState (F k) (A k) (hA k))
              (S k) t ω) i j) (P k)) ∧
          ∀ k, opNorm (mean (P k) (fun ω =>
              Q ϱ (Muon.DetEquiv.WeightedBuf (w k) (withState (F k) (A k) (hA k)) (S k) t ω)))
            ≤ K * opNorm (A k) + r k := by
  obtain ⟨K, r, hr, hb⟩ := expected_update_opNorm_uniform ϱ CS γ hϱ
  refine ⟨K, ?_⟩
  intro m n B Ω _ P _ S F w hw hdim hSo hSi hreg
  refine ⟨fun k => r (B k), hr.comp hreg.B_top, ?_⟩
  intro A hA t
  refine ⟨fun k i j => (expected_update_contour (hw k) (withState (F k) (A k) (hA k)) (S k) t
    ϱ hϱ).1 i j, fun k => ?_⟩
  exact hb (Ω k) (m k) (n k) (B k) (P k) (w k) (withState (F k) (A k) (hA k)) (S k) t (hw k)
    (hSo k) (hSi k) (le_trans (Nat.cast_le.mpr (le_max_left _ _)) (hdim k))
    (le_trans (Nat.cast_le.mpr (le_max_right _ _)) (hdim k))

/-- `lem:app-dyn-mean`(i), EMA corollary, `cr-2026-10-23`. The case `w = emaW F.β` with the frozen buffer
`M_t = frozenBuf F S t` (`eqn:app-setup-frozen`); same constants as (i). Source, verbatim (`sections/05-dynamics/section.tex`, ll. 768–798):
```latex
\begin{lemma}[Finite mean and susceptibility]\label{lem:app-dyn-mean}
In the frozen-state model with $\norm{\Ahat}_\F=1$, $\norm{\Sigmaout},\norm{\Sigmain}\le C_\Sigma$
and $\max(\Nin,\Nout)\le\gamma_\star B$, and with no condition on $\norm{\Ahat}$:
\begin{enumerate}[label=(\roman*)]
\item for every compact $I\subset(0,\infty)$ there is $C_I$ with
$\norm{\mathcal H(z)}_\F\le C_I$ for $z\in\mathbb S$ with $\Ree z\in I$, and
$\norm{\mathcal H(z)}_\F\le C/\Ree z$ for $z\in\mathbb S$ with $\Ree z\ge1$;
\item for real $s$, $\norm{\frac{\dif}{\dif s}\mathcal H(s)}_\F\le C_I$ for $s\in I$ and
$\norm{\frac{\dif}{\dif s}\mathcal H(s)}_\F\le C/s^2$ for $s\ge2$;
\item for $0<\ridge_-\le\ridge'\le\ridge_+$,
$\norm{\EE\,\Qridge{\ridge'}(\Mt)}_\F+\norm{\EE\,\partial_{\ridge'}\Qridge{\ridge'}(\Mt)}_\F\le C$,
with $C$ depending also on $(\ridge_-,\ridge_+)$;
\item for the fixed ridge $\ridge$ there are $C$ and a sequence $r_B\to0$,
depending only on $(\ridge,\gamma_\star,C_\Sigma)$ and on the sequence of
dimensions, such that $\norm{\EE\,\Qridge\ridge(\Mt)}\le C\norm{\Ahat}+r_B$ for
every normalized state.
\end{enumerate}
The constants depend only on $(\gamma_\star,C_\Sigma)$ and on $I$ where
indicated, not on $\Ahat$, on the dimension or on the weights within the
class \cref{eqn:app-de-weightclass}. Consequently, for the stationary chain
of \cref{def:app-dyn-chains} at a deterministic $D$ with
$r_-\le\cR(D)\le r_+$,
\begin{equation}\label{eqn:app-dyn-mean-physical}
\begin{gathered}
\norm{\overline V(D)}_\F\le C,\qquad
\big\|\EE\,\partial_\ell\Qridge\ell(N_0)\big|_{\ell=\ridgephys(D)}\big\|_\F\le C,\\
\norm{\Sigmaout^{1/2}\overline V(D)\Sigmain^{1/2}}\le C\norm{\Sigmaout^{1/2}D\Sigmain^{1/2}}+Cr_B ,
\end{gathered}
\end{equation}
with $C$ depending also on $(r_-,r_+)$.
\end{lemma}
```
-/
theorem lem_app_dyn_mean_i_ema (γ CS : ℝ) (I : Set ℝ) (hI : IsCompact I) (hIpos : I ⊆ Ioi 0) :
    ∃ CI C : ℝ, ∀ (m n B : ℕ) (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (S : FrozenSamples P m n B) (F : FrozenParams m n B) (t : ℤ),
      ((max m n : ℕ) : ℝ) ≤ γ * (B : ℝ) → opNorm F.C.Sout ≤ CS → opNorm F.C.Sin ≤ CS →
      (∀ z : ℂ, z ∈ sectorS → ∀ (i : Fin m) (j : Fin n),
        Integrable (fun ω => Xz (frozenBuf F S t ω) z i j) P) ∧
      (∀ z ∈ sectorS, z.re ∈ I → fro (HzF P F S t z) ≤ CI) ∧
      (∀ z ∈ sectorS, 1 ≤ z.re → fro (HzF P F S t z) ≤ C / z.re) := by
  obtain ⟨CI, C, h⟩ := lem_app_dyn_mean_i γ CS I hI hIpos
  refine ⟨CI, C, ?_⟩
  intro m n B Ω _ P _ S F t hγ hS1 hS2
  exact h (Muon.emaW F.β) (Muon.Drift.emaW_weightClass F.β F.hβ) m n B Ω P S F t hγ hS1 hS2

/-- `lem:app-dyn-mean`(ii), EMA corollary, `cr-2026-10-23`. The case `w = emaW F.β`, `M_t = frozenBuf F S t`.
Source, verbatim (`sections/05-dynamics/section.tex`, ll. 768–798):
```latex
\begin{lemma}[Finite mean and susceptibility]\label{lem:app-dyn-mean}
In the frozen-state model with $\norm{\Ahat}_\F=1$, $\norm{\Sigmaout},\norm{\Sigmain}\le C_\Sigma$
and $\max(\Nin,\Nout)\le\gamma_\star B$, and with no condition on $\norm{\Ahat}$:
\begin{enumerate}[label=(\roman*)]
\item for every compact $I\subset(0,\infty)$ there is $C_I$ with
$\norm{\mathcal H(z)}_\F\le C_I$ for $z\in\mathbb S$ with $\Ree z\in I$, and
$\norm{\mathcal H(z)}_\F\le C/\Ree z$ for $z\in\mathbb S$ with $\Ree z\ge1$;
\item for real $s$, $\norm{\frac{\dif}{\dif s}\mathcal H(s)}_\F\le C_I$ for $s\in I$ and
$\norm{\frac{\dif}{\dif s}\mathcal H(s)}_\F\le C/s^2$ for $s\ge2$;
\item for $0<\ridge_-\le\ridge'\le\ridge_+$,
$\norm{\EE\,\Qridge{\ridge'}(\Mt)}_\F+\norm{\EE\,\partial_{\ridge'}\Qridge{\ridge'}(\Mt)}_\F\le C$,
with $C$ depending also on $(\ridge_-,\ridge_+)$;
\item for the fixed ridge $\ridge$ there are $C$ and a sequence $r_B\to0$,
depending only on $(\ridge,\gamma_\star,C_\Sigma)$ and on the sequence of
dimensions, such that $\norm{\EE\,\Qridge\ridge(\Mt)}\le C\norm{\Ahat}+r_B$ for
every normalized state.
\end{enumerate}
The constants depend only on $(\gamma_\star,C_\Sigma)$ and on $I$ where
indicated, not on $\Ahat$, on the dimension or on the weights within the
class \cref{eqn:app-de-weightclass}. Consequently, for the stationary chain
of \cref{def:app-dyn-chains} at a deterministic $D$ with
$r_-\le\cR(D)\le r_+$,
\begin{equation}\label{eqn:app-dyn-mean-physical}
\begin{gathered}
\norm{\overline V(D)}_\F\le C,\qquad
\big\|\EE\,\partial_\ell\Qridge\ell(N_0)\big|_{\ell=\ridgephys(D)}\big\|_\F\le C,\\
\norm{\Sigmaout^{1/2}\overline V(D)\Sigmain^{1/2}}\le C\norm{\Sigmaout^{1/2}D\Sigmain^{1/2}}+Cr_B ,
\end{gathered}
\end{equation}
with $C$ depending also on $(r_-,r_+)$.
\end{lemma}
```
-/
theorem lem_app_dyn_mean_ii_ema (γ CS : ℝ) (I : Set ℝ) (hI : IsCompact I) (hIpos : I ⊆ Ioi 0) :
    ∃ CI C : ℝ, ∀ (m n B : ℕ) (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (S : FrozenSamples P m n B) (F : FrozenParams m n B) (t : ℤ),
      ((max m n : ℕ) : ℝ) ≤ γ * (B : ℝ) → opNorm F.C.Sout ≤ CS → opNorm F.C.Sin ≤ CS →
      (∀ z : ℂ, z ∈ sectorS → ∀ (i : Fin m) (j : Fin n),
        Integrable (fun ω => Xz (frozenBuf F S t ω) z i j) P) ∧
      (∀ s ∈ I, (∀ (i : Fin m) (j : Fin n),
          DifferentiableAt ℝ (fun x : ℝ => HzF P F S t (x : ℂ) i j) s) ∧
        fro (dHzF P F S t s) ≤ CI) ∧
      (∀ s : ℝ, 2 ≤ s → (∀ (i : Fin m) (j : Fin n),
          DifferentiableAt ℝ (fun x : ℝ => HzF P F S t (x : ℂ) i j) s) ∧
        fro (dHzF P F S t s) ≤ C / s ^ 2) := by
  obtain ⟨CI, C, h⟩ := lem_app_dyn_mean_ii γ CS I hI hIpos
  refine ⟨CI, C, ?_⟩
  intro m n B Ω _ P _ S F t hγ hS1 hS2
  exact h (Muon.emaW F.β) (Muon.Drift.emaW_weightClass F.β F.hβ) m n B Ω P S F t hγ hS1 hS2

/-- `lem:app-dyn-mean`(iii), EMA corollary, `cr-2026-10-23`. The case `w = emaW F.β`, `M_t = frozenBuf F S t`.
Source, verbatim (`sections/05-dynamics/section.tex`, ll. 768–798):
```latex
\begin{lemma}[Finite mean and susceptibility]\label{lem:app-dyn-mean}
In the frozen-state model with $\norm{\Ahat}_\F=1$, $\norm{\Sigmaout},\norm{\Sigmain}\le C_\Sigma$
and $\max(\Nin,\Nout)\le\gamma_\star B$, and with no condition on $\norm{\Ahat}$:
\begin{enumerate}[label=(\roman*)]
\item for every compact $I\subset(0,\infty)$ there is $C_I$ with
$\norm{\mathcal H(z)}_\F\le C_I$ for $z\in\mathbb S$ with $\Ree z\in I$, and
$\norm{\mathcal H(z)}_\F\le C/\Ree z$ for $z\in\mathbb S$ with $\Ree z\ge1$;
\item for real $s$, $\norm{\frac{\dif}{\dif s}\mathcal H(s)}_\F\le C_I$ for $s\in I$ and
$\norm{\frac{\dif}{\dif s}\mathcal H(s)}_\F\le C/s^2$ for $s\ge2$;
\item for $0<\ridge_-\le\ridge'\le\ridge_+$,
$\norm{\EE\,\Qridge{\ridge'}(\Mt)}_\F+\norm{\EE\,\partial_{\ridge'}\Qridge{\ridge'}(\Mt)}_\F\le C$,
with $C$ depending also on $(\ridge_-,\ridge_+)$;
\item for the fixed ridge $\ridge$ there are $C$ and a sequence $r_B\to0$,
depending only on $(\ridge,\gamma_\star,C_\Sigma)$ and on the sequence of
dimensions, such that $\norm{\EE\,\Qridge\ridge(\Mt)}\le C\norm{\Ahat}+r_B$ for
every normalized state.
\end{enumerate}
The constants depend only on $(\gamma_\star,C_\Sigma)$ and on $I$ where
indicated, not on $\Ahat$, on the dimension or on the weights within the
class \cref{eqn:app-de-weightclass}. Consequently, for the stationary chain
of \cref{def:app-dyn-chains} at a deterministic $D$ with
$r_-\le\cR(D)\le r_+$,
\begin{equation}\label{eqn:app-dyn-mean-physical}
\begin{gathered}
\norm{\overline V(D)}_\F\le C,\qquad
\big\|\EE\,\partial_\ell\Qridge\ell(N_0)\big|_{\ell=\ridgephys(D)}\big\|_\F\le C,\\
\norm{\Sigmaout^{1/2}\overline V(D)\Sigmain^{1/2}}\le C\norm{\Sigmaout^{1/2}D\Sigmain^{1/2}}+Cr_B ,
\end{gathered}
\end{equation}
with $C$ depending also on $(r_-,r_+)$.
\end{lemma}
```
-/
theorem lem_app_dyn_mean_iii_ema (γ CS ϱlo ϱhi : ℝ) (hlo : 0 < ϱlo) (hle : ϱlo ≤ ϱhi) :
    ∃ C : ℝ, ∀ (m n B : ℕ) (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (S : FrozenSamples P m n B) (F : FrozenParams m n B) (t : ℤ),
      ((max m n : ℕ) : ℝ) ≤ γ * (B : ℝ) → opNorm F.C.Sout ≤ CS → opNorm F.C.Sin ≤ CS →
      (∀ ϱ ∈ Icc ϱlo ϱhi, ∀ (i : Fin m) (j : Fin n),
        Integrable (fun ω => Q ϱ (frozenBuf F S t ω) i j) P) ∧
      (∀ ϱ ∈ Icc ϱlo ϱhi, ∀ (i : Fin m) (j : Fin n),
        Integrable (fun ω => dQ ϱ (frozenBuf F S t ω) i j) P) ∧
      (∀ ϱ' ∈ Icc ϱlo ϱhi, ∀ ω : Ω, ∀ (i : Fin m) (j : Fin n),
          DifferentiableAt ℝ (fun r : ℝ => Q r (frozenBuf F S t ω) i j) ϱ') ∧
      (∀ ϱ' ∈ Icc ϱlo ϱhi,
        fro (mean P (fun ω => Q ϱ' (frozenBuf F S t ω))) +
          fro (mean P (fun ω => dQ ϱ' (frozenBuf F S t ω))) ≤ C) := by
  set I : Set ℝ := Icc (ϱlo / 2) (ϱhi + ϱlo / 2 + 4) with hI
  have hIc : IsCompact I := isCompact_Icc
  have hIp : I ⊆ Ioi 0 := fun s hs => lt_of_lt_of_le (by linarith) hs.1
  obtain ⟨CI1, C1, h1⟩ := lem_app_dyn_mean_i_ema γ CS I hIc hIp
  obtain ⟨CI2, C2, h2⟩ := lem_app_dyn_mean_ii_ema γ CS I hIc hIp
  refine ⟨2 * ((2 / Real.pi) * (((5 * max CI1 0 + 2 * max C1 0) + (5 * max CI2 0 + 2 * max C2 0)) *
          ∫ u in Ioi (0 : ℝ), (1 + u ^ 2)⁻¹)), ?_⟩
  intro m n B Ω _ P _ S F t hγ hS1 hS2
  obtain ⟨-, hI1, hC1⟩ := h1 m n B Ω P S F t hγ hS1 hS2
  obtain ⟨-, hD2, hDC⟩ := h2 m n B Ω P S F t hγ hS1 hS2
  refine fm_core2 (P := P) (frozenBuf F S t) (fm_meas_WB (Muon.emaW F.β) F S t) ϱlo ϱhi hlo hle
    CI1 C1 CI2 C2 (HzF P F S t) ?_ ?_ ?_ ?_ ?_
  · intro s hs i j
    show ∫ ω, Xz (frozenBuf F S t ω) (s : ℂ) i j ∂P = _
    rw [integral_congr_ae (Filter.Eventually.of_forall fun ω => fm_Xz_ofReal _ hs i j)]
    exact integral_ofReal
  · intro s hs
    exact hI1 (s : ℂ) (fm_sector (lt_of_lt_of_le (by linarith) hs.1))
      (by rw [Complex.ofReal_re]; exact hs)
  · intro s hs
    have := hC1 (s : ℂ) (fm_sector (by linarith)) (by rw [Complex.ofReal_re]; exact hs)
    simpa using this
  · intro s hs
    exact hD2 s hs
  · intro s hs
    exact hDC s hs

private lemma fm_emaW_weightClass (β : ℝ) (hβ : 0 ≤ β ∧ β < 1) :
    Muon.DetEquiv.WeightClass (Muon.emaW β) := by
  obtain ⟨hb0, hb1⟩ := hβ
  have hnn : ∀ j, 0 ≤ Muon.emaW β j := fun j =>
    mul_nonneg (by linarith) (pow_nonneg hb0 j)
  have hsum : Summable (Muon.emaW β) := by
    unfold Muon.emaW
    exact (summable_geometric_of_lt_one hb0 hb1).mul_left (1 - β)
  have htsum : ∑' j, Muon.emaW β j = 1 := by
    exact Muon.tsum_emaW hb0 hb1
  refine ⟨⟨hnn, hsum, ⟨0, ?_⟩⟩, ?_, htsum.le⟩
  · unfold Muon.emaW
    simp
    linarith
  · intro j
    have h1 : β ^ j ≤ 1 := pow_le_one₀ hb0 hb1.le
    have h2 : 0 ≤ β ^ j := pow_nonneg hb0 j
    unfold Muon.emaW
    nlinarith

/-- `lem:app-dyn-mean`(iv), EMA corollary, `cr-2026-10-23`. The case `w_k = emaW (F k).β`, `M_t = frozenBuf`:
for fixed `ϱ > 0`, the constant `K` of (iv) and a sequence `r_B → 0` such that for every normalized state and
every `t`, the frozen integrands are integrable and `‖𝔼 Q_ϱ(M_t)‖ ≤ K‖Â‖ + r_B`.
Source, verbatim (`sections/05-dynamics/section.tex`, ll. 768–798):
```latex
\begin{lemma}[Finite mean and susceptibility]\label{lem:app-dyn-mean}
In the frozen-state model with $\norm{\Ahat}_\F=1$, $\norm{\Sigmaout},\norm{\Sigmain}\le C_\Sigma$
and $\max(\Nin,\Nout)\le\gamma_\star B$, and with no condition on $\norm{\Ahat}$:
\begin{enumerate}[label=(\roman*)]
\item for every compact $I\subset(0,\infty)$ there is $C_I$ with
$\norm{\mathcal H(z)}_\F\le C_I$ for $z\in\mathbb S$ with $\Ree z\in I$, and
$\norm{\mathcal H(z)}_\F\le C/\Ree z$ for $z\in\mathbb S$ with $\Ree z\ge1$;
\item for real $s$, $\norm{\frac{\dif}{\dif s}\mathcal H(s)}_\F\le C_I$ for $s\in I$ and
$\norm{\frac{\dif}{\dif s}\mathcal H(s)}_\F\le C/s^2$ for $s\ge2$;
\item for $0<\ridge_-\le\ridge'\le\ridge_+$,
$\norm{\EE\,\Qridge{\ridge'}(\Mt)}_\F+\norm{\EE\,\partial_{\ridge'}\Qridge{\ridge'}(\Mt)}_\F\le C$,
with $C$ depending also on $(\ridge_-,\ridge_+)$;
\item for the fixed ridge $\ridge$ there are $C$ and a sequence $r_B\to0$,
depending only on $(\ridge,\gamma_\star,C_\Sigma)$ and on the sequence of
dimensions, such that $\norm{\EE\,\Qridge\ridge(\Mt)}\le C\norm{\Ahat}+r_B$ for
every normalized state.
\end{enumerate}
The constants depend only on $(\gamma_\star,C_\Sigma)$ and on $I$ where
indicated, not on $\Ahat$, on the dimension or on the weights within the
class \cref{eqn:app-de-weightclass}. Consequently, for the stationary chain
of \cref{def:app-dyn-chains} at a deterministic $D$ with
$r_-\le\cR(D)\le r_+$,
\begin{equation}\label{eqn:app-dyn-mean-physical}
\begin{gathered}
\norm{\overline V(D)}_\F\le C,\qquad
\big\|\EE\,\partial_\ell\Qridge\ell(N_0)\big|_{\ell=\ridgephys(D)}\big\|_\F\le C,\\
\norm{\Sigmaout^{1/2}\overline V(D)\Sigmain^{1/2}}\le C\norm{\Sigmaout^{1/2}D\Sigmain^{1/2}}+Cr_B ,
\end{gathered}
\end{equation}
with $C$ depending also on $(r_-,r_+)$.
\end{lemma}
```
-/
theorem lem_app_dyn_mean_iv_ema (γ CS ϱ : ℝ) (hϱ : 0 < ϱ) :
    ∃ K : ℝ, ∀ (m n B : ℕ → ℕ) (Ω : ℕ → Type) [∀ k, MeasurableSpace (Ω k)]
      (P : ∀ k, Measure (Ω k)) [∀ k, IsProbabilityMeasure (P k)]
      (S : ∀ k, FrozenSamples (P k) (m k) (n k) (B k)) (F : ∀ k, FrozenParams (m k) (n k) (B k)),
      (∀ k, ((max (m k) (n k) : ℕ) : ℝ) ≤ γ * (B k : ℝ)) →
      (∀ k, opNorm (F k).C.Sout ≤ CS) → (∀ k, opNorm (F k).C.Sin ≤ CS) →
      ProportionalRegime m n B (fun k => (F k).C) →
      ∃ r : ℕ → ℝ, Tendsto r atTop (𝓝 0) ∧
        ∀ (A : ∀ k, Mat (m k) (n k)) (hA : ∀ k, fro (A k) = 1) (t : ℤ),
          (∀ k (i : Fin (m k)) (j : Fin (n k)),
            Integrable (fun ω => Q ϱ (frozenBuf (withState (F k) (A k) (hA k)) (S k) t ω) i j) (P k)) ∧
          ∀ k, opNorm (mean (P k) (fun ω => Q ϱ (frozenBuf (withState (F k) (A k) (hA k)) (S k) t ω)))
            ≤ K * opNorm (A k) + r k := by
  obtain ⟨K, hK⟩ := lem_app_dyn_mean_iv γ CS ϱ hϱ
  refine ⟨K, ?_⟩
  intro m n B Ω _ P _ S F hdim hSo hSi hreg
  let w : ∀ k, ℕ → ℝ := fun k => Muon.emaW (F k).β
  have hw : ∀ k, Muon.DetEquiv.WeightClass (w k) := fun k =>
    fm_emaW_weightClass (F k).β (F k).hβ
  obtain ⟨r, hr, hall⟩ := hK m n B Ω P S F w hw hdim hSo hSi hreg
  refine ⟨r, hr, ?_⟩
  intro A hA t
  obtain ⟨hint, hbound⟩ := hall A hA t
  constructor
  · intro k i j
    have hbuf : ∀ ω,
        Muon.DetEquiv.WeightedBuf (w k) (withState (F k) (A k) (hA k)) (S k) t ω =
          frozenBuf (withState (F k) (A k) (hA k)) (S k) t ω := by
      intro ω
      simpa [w, withState] using
        Muon.DetEquiv.weightedBuf_emaW_eq_frozenBuf
          (withState (F k) (A k) (hA k)) (S k) t ω
    exact (hint k i j).congr (Filter.Eventually.of_forall fun ω =>
      congrArg (fun M : Mat (m k) (n k) => Q ϱ M i j) (hbuf ω))
  · intro k
    have hbuf : ∀ ω,
        Muon.DetEquiv.WeightedBuf (w k) (withState (F k) (A k) (hA k)) (S k) t ω =
          frozenBuf (withState (F k) (A k) (hA k)) (S k) t ω := by
      intro ω
      simpa [w, withState] using
        Muon.DetEquiv.weightedBuf_emaW_eq_frozenBuf
          (withState (F k) (A k) (hA k)) (S k) t ω
    simpa only [hbuf] using hbound k

/-! ### Helpers for `eqn_app_dyn_mean_physical` -/

open scoped Matrix.Norms.L2Operator in
private lemma fmp_opNorm_mul {a b c : ℕ} (A : Mat a b) (B : Mat b c) :
    opNorm (A * B) ≤ opNorm A * opNorm B := by
  simpa only [opNorm_eq_norm] using Matrix.l2_opNorm_mul A B

open scoped Matrix.Norms.L2Operator in
private lemma fmp_opNorm_smul {a b : ℕ} (c : ℝ) (A : Mat a b) :
    opNorm (c • A) = |c| * opNorm A := by
  rw [opNorm_eq_norm, opNorm_eq_norm, norm_smul, Real.norm_eq_abs]

private lemma fmp_opNorm_nonneg {a b : ℕ} (A : Mat a b) : 0 ≤ opNorm A := by
  unfold opNorm
  exact norm_nonneg _

open scoped Matrix.Norms.L2Operator in
private lemma fmp_opNorm_rOut_sq {m n : ℕ} (C : Covariances m n) :
    opNorm (rOut C) * opNorm (rOut C) = opNorm C.Sout := by
  have hh : (rOut C)ᴴ = rOut C :=
    (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg C.Sout)).isHermitian
  have hsq : rOut C * rOut C = C.Sout :=
    CFC.sqrt_mul_sqrt_self C.Sout (Matrix.nonneg_iff_posSemidef.mpr C.psdOut)
  have h := Matrix.l2_opNorm_conjTranspose_mul_self (rOut C)
  rw [hh, hsq] at h
  rw [opNorm_eq_norm, opNorm_eq_norm]
  exact h.symm

open scoped Matrix.Norms.L2Operator in
private lemma fmp_opNorm_rIn_sq {m n : ℕ} (C : Covariances m n) :
    opNorm (rIn C) * opNorm (rIn C) = opNorm C.Sin := by
  have hh : (rIn C)ᴴ = rIn C :=
    (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg C.Sin)).isHermitian
  have hsq : rIn C * rIn C = C.Sin :=
    CFC.sqrt_mul_sqrt_self C.Sin (Matrix.nonneg_iff_posSemidef.mpr C.psdIn)
  have h := Matrix.l2_opNorm_conjTranspose_mul_self (rIn C)
  rw [hh, hsq] at h
  rw [opNorm_eq_norm, opNorm_eq_norm]
  exact h.symm

private theorem fmp_Ahat_norm {m n : ℕ} (C : Covariances m n) (D : Mat m n)
    (hD : 0 < riskSigma C D) : fro (Ahat C D) = 1 := by
  have hsq : ∀ (c : ℝ) (K : Mat m n), fro (c • K) ^ 2 = c ^ 2 * fro K ^ 2 := by
    intro c K
    have hf : ∀ L : Mat m n, fro L ^ 2 = ∑ i, ∑ j, L i j ^ 2 := by
      intro L
      unfold fro
      rw [Real.sq_sqrt (by positivity)]
      simp only [Real.norm_eq_abs, sq_abs]
    simp only [hf, Matrix.smul_apply, smul_eq_mul, mul_pow, Finset.mul_sum]
  have hr := eqn_app_setup_whitened_risk C D
  have hs : fro (Ahat C D) ^ 2 = 1 := by
    rw [Ahat, hsq, inv_pow, Real.sq_sqrt (by linarith)]
    rw [show fro (Arot C D) ^ 2 = 2 * riskSigma C D by linarith,
      inv_mul_cancel₀ (by linarith)]
  have hn : 0 ≤ fro (Ahat C D) := Real.sqrt_nonneg _
  nlinarith

private theorem fmp_physgrad_cont {m n B : ℕ} (C : Covariances m n) (D : Mat m n) :
    Continuous (fun b : Fin B → Vec m × Vec n =>
      batchGrad D (fun a => phys C (b a))) := by
  unfold batchGrad grad resid phys outer
  fun_prop

private theorem fmp_stat_aesm {m n B : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (p : DynParams) (C : Covariances m n) (cs : ChainSamples P m n B) (t : ℕ)
    (D M : Mat m n)
    (hs : ∀ᵐ ω ∂P, Summable (fun j : ℕ =>
      emaW p.β j • batchGrad D (physBatch C (cs.aux (t : ℤ) j) ω))) (k : ℕ) :
    AEStronglyMeasurable (fun ω => (def_app_dyn_chains p C cs t D M ω).stat k) P := by
  induction k with
  | zero =>
    refine aestronglyMeasurable_of_tendsto_ae atTop (f := fun N ω =>
      ∑ j ∈ Finset.range N,
        emaW p.β j • batchGrad D (physBatch C (cs.aux (t : ℤ) j) ω))
      (fun N => ?_) ?_
    · refine (Finset.stronglyMeasurable_fun_sum (Finset.range N) fun j _ => ?_).aestronglyMeasurable
      exact ((fmp_physgrad_cont C D).measurable.comp
        (Measurable.of_eval fun a => cs.meas_aux (t : ℤ) j a)).stronglyMeasurable.const_smul
          (emaW p.β j)
    · filter_upwards [hs] with ω hω
      exact hω.hasSum.tendsto_sum_nat
  | succ k ih =>
    exact (ih.const_smul p.β).add
      (((fmp_physgrad_cont C D).measurable.comp (Measurable.of_eval fun a =>
        cs.meas_act ((t : ℤ) + k + 1) a)).stronglyMeasurable.aestronglyMeasurable.const_smul
          (1 - p.β))

private lemma fmp_dQ_scale {m n : ℕ} (K : Mat m n) {a ℓ : ℝ} (ha : 0 < a) (hℓ : 0 < ℓ) :
    dQ ℓ (a • K) = (a ^ 2)⁻¹ • dQ (ℓ / a ^ 2) K := by
  ext i j
  have e : (fun r : ℝ => Q r (a • K) i j) =ᶠ[𝓝 ℓ] (fun r : ℝ => Q (r / a ^ 2) K i j) := by
    filter_upwards [Ioi_mem_nhds hℓ] with r hr
    rw [prop_app_setup_scaling_i r (le_of_lt hr) K a ha]
  have hd : HasDerivAt (fun r : ℝ => Q (r / a ^ 2) K i j)
      (dQ (ℓ / a ^ 2) K i j * (a ^ 2)⁻¹) ℓ := by
    have h1 := fm_hasDerivAt_Q (div_pos hℓ (pow_pos ha 2)) K i j
    have h2 : HasDerivAt (fun r : ℝ => r / a ^ 2) ((a ^ 2)⁻¹) ℓ := by
      simpa [div_eq_mul_inv] using (hasDerivAt_id ℓ).mul_const ((a ^ 2)⁻¹)
    exact h1.comp ℓ h2
  show deriv (fun r : ℝ => Q r (a • K) i j) ℓ = (a ^ 2)⁻¹ * dQ (ℓ / a ^ 2) K i j
  rw [e.deriv_eq, hd.deriv]
  ring

private lemma fmp_dQ_phys {m n : ℕ} (K : Mat m n) {R ϱ : ℝ} (hR : 0 < R) (hϱ : 0 < ϱ) :
    dQ (2 * R * ϱ) (Real.sqrt (2 * R) • K) = (2 * R)⁻¹ • dQ ϱ K := by
  have ha : 0 < Real.sqrt (2 * R) := Real.sqrt_pos.mpr (by linarith)
  have h2 : Real.sqrt (2 * R) ^ 2 = 2 * R := Real.sq_sqrt (by linarith)
  rw [fmp_dQ_scale K ha (by positivity), h2]
  congr 2
  field_simp

private lemma fmp_transfer {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {P' : Measure Ω'} {m n : ℕ} {X : Ω → Mat m n} {Y : Ω' → Mat m n}
    (hX : AEMeasurable X P) (hY : AEMeasurable Y P') (h : P.map X = P'.map Y)
    {g : Mat m n → ℝ} (hg : Measurable g) :
    (Integrable (fun ω => g (X ω)) P ↔ Integrable (fun ω => g (Y ω)) P') ∧
    ∫ ω, g (X ω) ∂P = ∫ ω, g (Y ω) ∂P' := by
  have hg1 : AEStronglyMeasurable g (P.map X) := hg.aestronglyMeasurable
  have hg2 : AEStronglyMeasurable g (P'.map Y) := hg.aestronglyMeasurable
  refine ⟨?_, ?_⟩
  · have e1 := integrable_map_measure hg1 hX
    have e2 := integrable_map_measure hg2 hY
    rw [h] at e1
    exact e1.symm.trans e2
  · rw [← integral_map hX hg1, ← integral_map hY hg2, h]


/-- `eqn:app-dyn-mean-physical` (a consequence of `lem:app-dyn-mean`(iv)), `cr-2026-10-23`. Frozen chains
at deterministic `D` with `r₋ ≤ 𝓡(D) ≤ r₊`. The constant `C` depends only on `(γ⋆, C_Σ, ϱ, r₋, r₊)` and is chosen
before the parameter record `p` (the field equalities `p.γstar = γ`, `p.CSig = C_Σ`, `p.ϱ = ϱ` link them), so it
does not depend on `p.β` or on the unused fields. For every model sequence and deterministic `D` with
`r₋ ≤ 𝓡(D) ≤ r₊`: the chain quantities are integrable, `𝔼 V_0` (`statV 1`) and the ridge derivative
`𝔼 ∂_ℓ Q_ℓ(N_0)|_{ℓ = ϱ°(D)}` (`stat 1`) are bounded by `C` in Frobenius norm, and
`‖Σ_out^{1/2} V̄(D) Σ_in^{1/2}‖ ≤ C‖Σ_out^{1/2} D Σ_in^{1/2}‖ + C r_B` with `r_B → 0`.
The chain is `def_app_dyn_chains` at time `t` (`D = Δ_t`, `M = M°_{t-1}`; the bound does not depend on `M`).
Source, verbatim (`sections/05-dynamics/section.tex`, ll. 768–798):
```latex
\begin{lemma}[Finite mean and susceptibility]\label{lem:app-dyn-mean}
In the frozen-state model with $\norm{\Ahat}_\F=1$, $\norm{\Sigmaout},\norm{\Sigmain}\le C_\Sigma$
and $\max(\Nin,\Nout)\le\gamma_\star B$, and with no condition on $\norm{\Ahat}$:
\begin{enumerate}[label=(\roman*)]
\item for every compact $I\subset(0,\infty)$ there is $C_I$ with
$\norm{\mathcal H(z)}_\F\le C_I$ for $z\in\mathbb S$ with $\Ree z\in I$, and
$\norm{\mathcal H(z)}_\F\le C/\Ree z$ for $z\in\mathbb S$ with $\Ree z\ge1$;
\item for real $s$, $\norm{\frac{\dif}{\dif s}\mathcal H(s)}_\F\le C_I$ for $s\in I$ and
$\norm{\frac{\dif}{\dif s}\mathcal H(s)}_\F\le C/s^2$ for $s\ge2$;
\item for $0<\ridge_-\le\ridge'\le\ridge_+$,
$\norm{\EE\,\Qridge{\ridge'}(\Mt)}_\F+\norm{\EE\,\partial_{\ridge'}\Qridge{\ridge'}(\Mt)}_\F\le C$,
with $C$ depending also on $(\ridge_-,\ridge_+)$;
\item for the fixed ridge $\ridge$ there are $C$ and a sequence $r_B\to0$,
depending only on $(\ridge,\gamma_\star,C_\Sigma)$ and on the sequence of
dimensions, such that $\norm{\EE\,\Qridge\ridge(\Mt)}\le C\norm{\Ahat}+r_B$ for
every normalized state.
\end{enumerate}
The constants depend only on $(\gamma_\star,C_\Sigma)$ and on $I$ where
indicated, not on $\Ahat$, on the dimension or on the weights within the
class \cref{eqn:app-de-weightclass}. Consequently, for the stationary chain
of \cref{def:app-dyn-chains} at a deterministic $D$ with
$r_-\le\cR(D)\le r_+$,
\begin{equation}\label{eqn:app-dyn-mean-physical}
\begin{gathered}
\norm{\overline V(D)}_\F\le C,\qquad
\big\|\EE\,\partial_\ell\Qridge\ell(N_0)\big|_{\ell=\ridgephys(D)}\big\|_\F\le C,\\
\norm{\Sigmaout^{1/2}\overline V(D)\Sigmain^{1/2}}\le C\norm{\Sigmaout^{1/2}D\Sigmain^{1/2}}+Cr_B ,
\end{gathered}
\end{equation}
with $C$ depending also on $(r_-,r_+)$.
\end{lemma}
```
-/
theorem eqn_app_dyn_mean_physical (γ CS ϱ rlo rhi : ℝ) (hrlo : 0 < rlo) (hle : rlo ≤ rhi) :
    ∃ C : ℝ, ∀ (p : DynParams), p.γstar = γ → p.CSig = CS → p.ϱ = ϱ →
      ∀ (m n B : ℕ → ℕ) (Ω : ℕ → Type) [∀ k, MeasurableSpace (Ω k)]
      (P : ∀ k, Measure (Ω k)) [∀ k, IsProbabilityMeasure (P k)]
      (Cv : ∀ k, Covariances (m k) (n k)) (cs : ∀ k, ChainSamples (P k) (m k) (n k) (B k))
      (D M : ∀ k, Mat (m k) (n k)) (t : ℕ),
      (∀ k, ((max (m k) (n k) : ℕ) : ℝ) ≤ γ * (B k : ℝ)) →
      (∀ k, opNorm (Cv k).Sout ≤ CS) → (∀ k, opNorm (Cv k).Sin ≤ CS) →
      ProportionalRegime m n B Cv →
      (∀ k, rlo ≤ riskSigma (Cv k) (D k) ∧ riskSigma (Cv k) (D k) ≤ rhi) →
      ∃ r : ℕ → ℝ, Tendsto r atTop (𝓝 0) ∧ ∀ k,
        (∀ (i : Fin (m k)) (j : Fin (n k)),
          Integrable (fun ω => (def_app_dyn_chains p (Cv k) (cs k) t (D k) (M k) ω).statV 1 i j) (P k)) ∧
        (∀ (i : Fin (m k)) (j : Fin (n k)),
          Integrable (fun ω => dQ (physRidge p (Cv k) (D k))
            ((def_app_dyn_chains p (Cv k) (cs k) t (D k) (M k) ω).stat 1) i j) (P k)) ∧
        (∀ ω : Ω k, ∀ (i : Fin (m k)) (j : Fin (n k)),
          DifferentiableAt ℝ (fun ℓ : ℝ => Q ℓ ((def_app_dyn_chains p (Cv k) (cs k) t (D k) (M k) ω).stat 1) i j)
            (physRidge p (Cv k) (D k))) ∧
        fro (mean (P k) (fun ω => (def_app_dyn_chains p (Cv k) (cs k) t (D k) (M k) ω).statV 1)) ≤ C ∧
        fro (mean (P k) (fun ω => dQ (physRidge p (Cv k) (D k))
          ((def_app_dyn_chains p (Cv k) (cs k) t (D k) (M k) ω).stat 1))) ≤ C ∧
        opNorm (rOut (Cv k) * mean (P k) (fun ω => (def_app_dyn_chains p (Cv k) (cs k) t (D k) (M k) ω).statV 1)
            * rIn (Cv k)) ≤
          C * opNorm (rOut (Cv k) * D k * rIn (Cv k)) + C * r k := by
  by_cases hϱ : 0 < ϱ
  · obtain ⟨C3, h3⟩ := lem_app_dyn_mean_iii_ema γ CS ϱ ϱ hϱ le_rfl
    obtain ⟨K0, hK0⟩ := lem_app_dyn_mean_iv_ema γ CS ϱ hϱ
    refine ⟨|C3| + |C3| / (2 * rlo) + |CS| * |K0| / Real.sqrt (2 * rlo) + |CS|, ?_⟩
    intro p hpγ hpCS hpϱ m n B Ω _ P _ Cv cs D M t hdim hOut hIn hreg hrisk
    subst hpϱ
    have hDpos : ∀ k, 0 < riskSigma (Cv k) (D k) := fun k => lt_of_lt_of_le hrlo (hrisk k).1
    have hBpos : ∀ k, 0 < B k := by
      intro k
      by_contra hb
      have hb0 : B k = 0 := by omega
      have hmax : max (m k) (n k) = 0 := by
        have hh := hdim k
        simp only [hb0, Nat.cast_zero, mul_zero, Nat.cast_nonpos] at hh
        exact_mod_cast hh
      have hm0 : m k = 0 := by omega
      have hrisk0 := eqn_app_setup_whitened_risk (Cv k) (D k)
      have := hDpos k
      simp [hm0, fro] at hrisk0
      linarith
    let F : ∀ k, FrozenParams (m k) (n k) (B k) := fun k =>
      { C := Cv k
        A := Ahat (Cv k) (D k)
        hA := fmp_Ahat_norm (Cv k) (D k) (hDpos k)
        β := p.β
        hβ := p.hβ
        hB := hBpos k }
    let S : ∀ k, FrozenSamples (P k) (m k) (n k) (B k) := fun k =>
      { zw := (cs k).act
        meas := (cs k).meas_act
        indep := (cs k).indep.precomp Sum.inl_injective
        law := (cs k).law_act }
    obtain ⟨r0, hr0, hall⟩ := hK0 m n B Ω P S F hdim hOut hIn hreg
    obtain ⟨-, hboundQ⟩ := hall (fun k => (F k).A) (fun k => (F k).hA) (t : ℤ)
    refine ⟨fun k => |r0 k|, by simpa using hr0.abs, fun k => ?_⟩
    have hR := hDpos k
    have hRlo := (hrisk k).1
    obtain ⟨hsum, hlawN, -, ⟨hint, -⟩, hmean⟩ := lem_app_dyn_chains_i p (Cv k) (cs k) t (D k) (M k)
      hR (F k) rfl rfl rfl (S k)
    have hYm : ∀ s : ℤ, Measurable (frozenBuf (F k) (S k) s) := fun s =>
      fm_meas_WB (Muon.emaW (F k).β) (F k) (S k) s
    have hYpath : AEMeasurable (fun ω (j : ℕ) => frozenBuf (F k) (S k) ((t : ℤ) + (j : ℤ) - 1) ω) (P k) :=
      AEMeasurable.of_eval fun j => (hYm _).aemeasurable
    have hXpath : AEMeasurable (fun ω => normChainPath p (Cv k) (cs k) t (D k) (M k) ω) (P k) := by
      refine AEMeasurable.of_eval fun j => ?_
      exact ((fmp_stat_aesm p (Cv k) (cs k) t (D k) (M k) hsum j).const_smul
        ((Real.sqrt (2 * riskSigma (Cv k) (D k)))⁻¹)).aemeasurable
    set X : Ω k → Mat (m k) (n k) := fun ω => normChainPath p (Cv k) (cs k) t (D k) (M k) ω 1 with hXdef
    set Y : Ω k → Mat (m k) (n k) := fun ω => frozenBuf (F k) (S k) (t : ℤ) ω with hYdef
    have hXm : AEMeasurable X (P k) := (measurable_pi_apply 1).comp_aemeasurable hXpath
    have hYm1 : AEMeasurable Y (P k) := (hYm _).aemeasurable
    have hlaw1 : (P k).map X = (P k).map Y := by
      have e1 := AEMeasurable.map_map_of_aemeasurable (measurable_pi_apply (1 : ℕ)).aemeasurable hXpath
      have e2 := AEMeasurable.map_map_of_aemeasurable (measurable_pi_apply (1 : ℕ)).aemeasurable hYpath
      rw [hlawN] at e1
      have e3 := e1.symm.trans e2
      refine e3.trans ?_
      congr 1
      funext ω
      simp [hYdef]
    set R : ℝ := riskSigma (Cv k) (D k) with hRdef
    have hstat : ∀ ω, (def_app_dyn_chains p (Cv k) (cs k) t (D k) (M k) ω).stat 1 =
        Real.sqrt (2 * R) • X ω := by
      intro ω
      have ha : Real.sqrt (2 * R) ≠ 0 := (Real.sqrt_pos.mpr (by linarith)).ne'
      simp only [hXdef, normChainPath]
      rw [smul_inv_smul₀ ha]
    have hg : ∀ (i : Fin (m k)) (j : Fin (n k)),
        Measurable (fun K : Mat (m k) (n k) => dQ p.ϱ K i j) := fun i j =>
      fm_meas_dQ hϱ measurable_id i j
    have hTr := fun (i : Fin (m k)) (j : Fin (n k)) => fmp_transfer hXm hYm1 hlaw1 (hg i j)
    have hdQeq : ∀ ω i j, dQ (physRidge p (Cv k) (D k))
        ((def_app_dyn_chains p (Cv k) (cs k) t (D k) (M k) ω).stat 1) i j =
        (2 * R)⁻¹ * dQ p.ϱ (X ω) i j := by
      intro ω i j
      rw [hstat]
      unfold physRidge
      rw [fmp_dQ_phys (X ω) hR hϱ]
      rfl
    have hI2 : ∀ (i : Fin (m k)) (j : Fin (n k)), Integrable (fun ω => dQ (physRidge p (Cv k) (D k))
        ((def_app_dyn_chains p (Cv k) (cs k) t (D k) (M k) ω).stat 1) i j) (P k) := by
      intro i j
      have : (fun ω => dQ (physRidge p (Cv k) (D k))
          ((def_app_dyn_chains p (Cv k) (cs k) t (D k) (M k) ω).stat 1) i j) =
          fun ω => (2 * R)⁻¹ * dQ p.ϱ (X ω) i j := funext fun ω => hdQeq ω i j
      rw [this]
      exact ((hTr i j).1.mpr (fm_integrable_dQ hϱ (hYm (t : ℤ)) i j)).const_mul _
    have hmeanD : mean (P k) (fun ω => dQ (physRidge p (Cv k) (D k))
        ((def_app_dyn_chains p (Cv k) (cs k) t (D k) (M k) ω).stat 1)) =
        (2 * R)⁻¹ • mean (P k) (fun ω => dQ p.ϱ (frozenBuf (F k) (S k) (t : ℤ) ω)) := by
      ext i j
      simp only [mean, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul]
      simp_rw [hdQeq]
      rw [integral_const_mul, (hTr i j).2]
    obtain ⟨-, -, -, hb⟩ := h3 (m k) (n k) (B k) (Ω k) (P k) (S k) (F k) (t : ℤ) (hdim k) (hOut k) (hIn k)
    have hb' := hb p.ϱ ⟨le_rfl, le_rfl⟩
    have hf1 := fm_fro_nonneg (mean (P k) (fun ω => Q p.ϱ (frozenBuf (F k) (S k) (t : ℤ) ω)))
    have hf2 := fm_fro_nonneg (mean (P k) (fun ω => dQ p.ϱ (frozenBuf (F k) (S k) (t : ℤ) ω)))
    have hC3 : C3 ≤ |C3| := le_abs_self _
    have hCnn : 0 ≤ |C3| / (2 * rlo) := by positivity
    have hCnn2 : 0 ≤ |CS| * |K0| / Real.sqrt (2 * rlo) := by positivity
    have hCnn3 : 0 ≤ |CS| := abs_nonneg _
    have hCnn4 : 0 ≤ |C3| := abs_nonneg _
    refine ⟨hint, hI2, ?_, ?_, ?_, ?_⟩
    · intro ω i j
      exact (fm_hasDerivAt_Q (show 0 < physRidge p (Cv k) (D k) by
        unfold physRidge; have := p.hϱ; positivity) _ i j).differentiableAt
    · rw [hmean]
      change fro (mean (P k) (fun ω => Q p.ϱ (frozenBuf (F k) (S k) (t : ℤ) ω))) ≤ _
      linarith
    · rw [hmeanD, fm_fro_smul, abs_of_pos (by positivity : (0 : ℝ) < (2 * R)⁻¹)]
      have hinv : (2 * R)⁻¹ ≤ (2 * rlo)⁻¹ := inv_anti₀ (by positivity) (by linarith)
      have h1 : fro (mean (P k) (fun ω => dQ p.ϱ (frozenBuf (F k) (S k) (t : ℤ) ω))) ≤ |C3| := by
        linarith
      calc (2 * R)⁻¹ * fro (mean (P k) (fun ω => dQ p.ϱ (frozenBuf (F k) (S k) (t : ℤ) ω)))
          ≤ (2 * rlo)⁻¹ * |C3| := mul_le_mul hinv h1 hf2 (by positivity)
        _ = |C3| / (2 * rlo) := by rw [div_eq_inv_mul]
        _ ≤ _ := by linarith
    · rw [hmean]
      change opNorm (rOut (Cv k) * mean (P k) (fun ω => Q p.ϱ (frozenBuf (F k) (S k) (t : ℤ) ω))
        * rIn (Cv k)) ≤ _
      have hq : opNorm (mean (P k) (fun ω => Q p.ϱ (frozenBuf (F k) (S k) (t : ℤ) ω))) ≤
          K0 * opNorm (Ahat (Cv k) (D k)) + r0 k := hboundQ k
      have hCS : 0 ≤ CS := (fmp_opNorm_nonneg (Cv k).Sout).trans (hOut k)
      have hrO : opNorm (rOut (Cv k)) ≤ Real.sqrt CS := by
        have hs := fmp_opNorm_rOut_sq (Cv k)
        have hsCS : Real.sqrt CS ^ 2 = CS := Real.sq_sqrt hCS
        nlinarith [fmp_opNorm_nonneg (rOut (Cv k)), Real.sqrt_nonneg CS, hOut k]
      have hrI : opNorm (rIn (Cv k)) ≤ Real.sqrt CS := by
        have hs := fmp_opNorm_rIn_sq (Cv k)
        have hsCS : Real.sqrt CS ^ 2 = CS := Real.sq_sqrt hCS
        nlinarith [fmp_opNorm_nonneg (rIn (Cv k)), Real.sqrt_nonneg CS, hIn k]
      have hrOI : opNorm (rOut (Cv k)) * opNorm (rIn (Cv k)) ≤ |CS| := by
        have hh := mul_le_mul hrO hrI (fmp_opNorm_nonneg (rIn (Cv k))) (Real.sqrt_nonneg CS)
        rw [abs_of_nonneg hCS]
        nlinarith [Real.sq_sqrt hCS]
      have hAop : opNorm (Ahat (Cv k) (D k)) ≤
          opNorm (rOut (Cv k) * D k * rIn (Cv k)) / Real.sqrt (2 * rlo) := by
        have hspos : 0 < Real.sqrt (2 * R) := Real.sqrt_pos.mpr (by positivity)
        have hslo : 0 < Real.sqrt (2 * rlo) := Real.sqrt_pos.mpr (by positivity)
        have hsle : Real.sqrt (2 * rlo) ≤ Real.sqrt (2 * R) :=
          Real.sqrt_le_sqrt (by linarith)
        have hinv : (Real.sqrt (2 * R))⁻¹ ≤ (Real.sqrt (2 * rlo))⁻¹ :=
          (inv_le_inv₀ hspos hslo).2 hsle
        rw [Ahat, Arot, fmp_opNorm_smul, abs_of_pos (inv_pos.mpr hspos)]
        calc
          _ ≤ (Real.sqrt (2 * rlo))⁻¹ * opNorm (rOut (Cv k) * D k * rIn (Cv k)) :=
            mul_le_mul_of_nonneg_right hinv (fmp_opNorm_nonneg _)
          _ = _ := by rw [div_eq_mul_inv, mul_comm]
      set Mn := mean (P k) (fun ω => Q p.ϱ (frozenBuf (F k) (S k) (t : ℤ) ω)) with hMn
      have hmul1 := fmp_opNorm_mul (rOut (Cv k)) Mn
      have hmul2 := fmp_opNorm_mul (rOut (Cv k) * Mn) (rIn (Cv k))
      have hnM := fmp_opNorm_nonneg Mn
      have hnA := fmp_opNorm_nonneg (Ahat (Cv k) (D k))
      have hnD := fmp_opNorm_nonneg (rOut (Cv k) * D k * rIn (Cv k))
      have hs : 0 < Real.sqrt (2 * rlo) := Real.sqrt_pos.mpr (by positivity)
      have hbound : opNorm (rOut (Cv k) * Mn * rIn (Cv k)) ≤
          |CS| * (|K0| * opNorm (Ahat (Cv k) (D k)) + |r0 k|) := by
        have hq' : opNorm Mn ≤ |K0| * opNorm (Ahat (Cv k) (D k)) + |r0 k| :=
          hq.trans (add_le_add (mul_le_mul_of_nonneg_right (le_abs_self _) hnA) (le_abs_self _))
        calc opNorm (rOut (Cv k) * Mn * rIn (Cv k))
            ≤ (opNorm (rOut (Cv k)) * opNorm Mn) * opNorm (rIn (Cv k)) :=
              hmul2.trans (mul_le_mul_of_nonneg_right hmul1 (fmp_opNorm_nonneg _))
          _ ≤ (opNorm (rOut (Cv k)) * (|K0| * opNorm (Ahat (Cv k) (D k)) + |r0 k|)) *
                opNorm (rIn (Cv k)) :=
              mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_left hq' (fmp_opNorm_nonneg _)) (fmp_opNorm_nonneg _)
          _ = (opNorm (rOut (Cv k)) * opNorm (rIn (Cv k))) *
                (|K0| * opNorm (Ahat (Cv k) (D k)) + |r0 k|) := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_right hrOI (by positivity)
      refine hbound.trans ?_
      have hA2 : |CS| * (|K0| * opNorm (Ahat (Cv k) (D k))) ≤
          |CS| * |K0| / Real.sqrt (2 * rlo) * opNorm (rOut (Cv k) * D k * rIn (Cv k)) := by
        calc |CS| * (|K0| * opNorm (Ahat (Cv k) (D k)))
            ≤ |CS| * (|K0| * (opNorm (rOut (Cv k) * D k * rIn (Cv k)) / Real.sqrt (2 * rlo))) :=
              mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hAop (abs_nonneg _))
                (abs_nonneg _)
          _ = _ := by ring
      have hD2 : 0 ≤ (|C3| + |C3| / (2 * rlo)) * opNorm (rOut (Cv k) * D k * rIn (Cv k)) :=
        mul_nonneg (by positivity) hnD
      have hr2 : 0 ≤ (|C3| + |C3| / (2 * rlo) + |CS| * |K0| / Real.sqrt (2 * rlo)) * |r0 k| :=
        mul_nonneg (by positivity) (abs_nonneg _)
      have hD3 : 0 ≤ (|CS| * |K0| / Real.sqrt (2 * rlo)) *
          opNorm (rOut (Cv k) * D k * rIn (Cv k)) := mul_nonneg hCnn2 hnD
      nlinarith [mul_nonneg hCnn3 (abs_nonneg (r0 k)), mul_nonneg hCnn4 (abs_nonneg (r0 k)),
        mul_nonneg hCnn (abs_nonneg (r0 k)), mul_nonneg hCnn hnD, mul_nonneg hCnn3 hnD,
        mul_nonneg hCnn4 hnD, mul_nonneg hCnn2 (abs_nonneg (r0 k))]
  · refine ⟨0, ?_⟩
    intro p hpγ hpCS hpϱ
    exact absurd (hpϱ ▸ p.hϱ) hϱ

end Muon.Dynamics
