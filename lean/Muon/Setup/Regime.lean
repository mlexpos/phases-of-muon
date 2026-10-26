import Muon.Foundations.Conventions
import Muon.Setup.Frozen

/-!
# Appendix A: proportional and spectrally diffuse regimes, deterministic equivalents

Work package L-A.10 (interface draft). Snapshot `cr-2026-10-23`. Source of record:
`sections/01-setup/section.tex`: `assum:proportional-regime` l.1073–1087,
`assum:app-setup-regime` l.1089–1098 (with the consequence l.1106–1107),
`def:deterministic-equivalent` l.1115–1126.

Reused, not redefined: `Muon.ProportionalRegime`, `Muon.IsDetEquiv`, `Muon.PEq`, `Muon.opNorm`,
`Muon.nuOut`, `Muon.nuIn` (`Muon.Foundations.Conventions`), and `Muon.Setup.FrozenParams`
(`Muon.Setup.Frozen`). Every theorem has proof `sorry`; proof routes are in
`muon/phases-of-muon/appendix-nodes/results/L-A.10-interface.json`.
-/

open scoped Matrix MatrixOrder ENNReal
open MeasureTheory ProbabilityTheory Filter Topology

noncomputable section

namespace Muon.Setup

open Muon

/-! ## The proportional regime (`assum:proportional-regime`) -/

/-- `assum:proportional-regime`, snapshot `cr-2026-10-23`. Declaration of record: the proportional
regime is `Muon.ProportionalRegime` (`Muon.Foundations.Conventions`), reused and not restated; this
alias carries the label. The assumption, verbatim from `section.tex` (l.1073–1087):
```latex
\begin{assumption}[Proportional regime]\label{assum:proportional-regime}
The dimensions $\Nin$, $\Nout$, $B$ tend to infinity jointly, with aspect
ratios converging to constants:
\[
\frac{\Nin}{B} \to \gin \in (0,\infty), \qquad
\frac{\Nout}{B} \to \gout \in (0,\infty).
\]
The covariance operator norms remain uniformly bounded: there exists a
constant $C > 0$, independent of $\Nin$ and $\Nout$, such that
\[
\|\Sigmain\|_{\mathrm{op}} \;\leq\; C, \qquad
\|\Sigmaout\|_{\mathrm{op}} \;\leq\; C.
\]
We refer to the joint limit as the \emph{proportional regime}.
\end{assumption}
```
-/
abbrev assum_proportional_regime {m n B : ℕ → ℕ} (C : ∀ k : ℕ, Covariances (m k) (n k)) :
    Type :=
  ProportionalRegime m n B C

/-! ## The spectrally diffuse regime (`assum:app-setup-regime`) -/

/-- Note (not a field): all constants and o(1) limits under this regime are uniform in the ridge
`ϱ ∈ [ϱlo, ϱhi]` unless a statement fixes `ϱ` (`section.tex` l.1108–1110).

`assum:app-setup-regime`, snapshot `cr-2026-10-23`. Declaration of record: `Muon.Setup.SetupRegime`
(alias `assum_app_setup_regime` below). The data are the dimension sequences `(m k, n k, B k)`, the
frozen-state parameters `F k` (`Muon.Setup.FrozenParams`), the proportional-regime structure on the
covariances of `F`, and the constants `γ⋆`, `C_Σ`, the fixed momentum `β`, and the ridge interval
`[ϱ₋, ϱ₊]`. The regime is carried as an interval in `ϱ`; the uniformity of limits in `ϱ` is not part
of the structure (see `open_questions`). The assumption, verbatim from `section.tex` (l.1089–1098):
```latex
\begin{assumption}[Spectrally diffuse proportional regime]\label{assum:app-setup-regime}
\Cref{assum:data-target,assum:proportional-regime} hold, and we fix
$\gamma_\star<\infty$ and $C_\Sigma\ge1$ with $\max(\Nin,\Nout)\le\gamma_\star B$,
$\norm{\Sigmain}\le C_\Sigma$ and $\norm{\Sigmaout}\le C_\Sigma$ along the whole
sequence of dimensions; the covariances are deterministic. The momentum
$\bmom\in[0,1)$ is fixed, and the normalized ridge satisfies
$\ridge\in[\ridge_-,\ridge_+]$ for fixed $0<\ridge_-\le\ridge_+<\infty$. The
state is frozen as in \cref{def:app-setup-frozen}, with $\cR(t)>0$, and the
normalized state is spectrally diffuse: $\norm{\Ahat}\to0$.
\end{assumption}
```
-/
structure SetupRegime where
  /-- Output dimension `N_out k` (`m` in the Lean convention, `Mat m n`). -/
  m : ℕ → ℕ
  /-- Input dimension `N_in k`. -/
  n : ℕ → ℕ
  /-- Driving dimension (batch size) `B k`. -/
  B : ℕ → ℕ
  /-- Frozen-state parameters at index `k`: covariances, normalized state `Â`, momentum, batch. -/
  F : ∀ k : ℕ, FrozenParams (m k) (n k) (B k)
  /-- `assum:proportional-regime` for the covariances of `F`. -/
  prop : ProportionalRegime m n B (fun k => (F k).C)
  /-- The constant `γ⋆`, with `max(N_in, N_out) ≤ γ⋆ B` along the sequence. -/
  γstar : ℝ
  /-- The covariance bound `C_Σ ≥ 1`. -/
  CSig : ℝ
  hC : 1 ≤ CSig
  /-- `max(N_in, N_out) ≤ γ⋆ B` along the whole sequence. -/
  dims : ∀ k : ℕ, ((max (m k) (n k) : ℕ) : ℝ) ≤ γstar * (B k : ℝ)
  /-- `‖Σ_out‖ ≤ C_Σ` along the whole sequence. -/
  normOut : ∀ k : ℕ, opNorm (F k).C.Sout ≤ CSig
  /-- `‖Σ_in‖ ≤ C_Σ` along the whole sequence. -/
  normIn : ∀ k : ℕ, opNorm (F k).C.Sin ≤ CSig
  /-- The fixed momentum `β ∈ [0,1)`. -/
  β : ℝ
  hβ : ∀ k : ℕ, (F k).β = β
  /-- Lower end `ϱ₋` of the normalized ridge interval `ϱ ∈ [ϱ₋, ϱ₊]`. -/
  ϱlo : ℝ
  /-- Upper end `ϱ₊` of the normalized ridge interval. -/
  ϱhi : ℝ
  hϱ : 0 < ϱlo ∧ ϱlo ≤ ϱhi
  /-- Spectral diffuseness of the normalized state: `‖Â‖ → 0`. -/
  diffuse : Tendsto (fun k : ℕ => opNorm (F k).A) atTop (𝓝 0)

/-- Alias carrying the label `assum:app-setup-regime`; see `SetupRegime`. -/
abbrev assum_app_setup_regime := SetupRegime

open scoped Matrix.Norms.L2Operator in
/-- Private helper: each eigenvalue of a Hermitian matrix is bounded in absolute value by its
operator norm (apply the eigenvector equation and `Matrix.l2_opNorm_mulVec`). -/
private lemma abs_eigenvalues_le_opNorm_aux {p : ℕ} (A : Matrix (Fin p) (Fin p) ℝ)
    (hA : A.IsHermitian) (i : Fin p) :
    |hA.eigenvalues i| ≤ opNorm A := by
  have hv := hA.mulVec_eigenvectorBasis i
  have hn : ‖hA.eigenvectorBasis i‖ = 1 := hA.eigenvectorBasis.orthonormal.1 i
  have h1 := Matrix.l2_opNorm_mulVec A (hA.eigenvectorBasis i)
  have h2 : (EuclideanSpace.equiv (Fin p) ℝ).symm (A *ᵥ ⇑(hA.eigenvectorBasis i)) =
      hA.eigenvalues i • hA.eigenvectorBasis i := by
    rw [hv]
    ext
    simp
  rw [h2, norm_smul, hn, Real.norm_eq_abs] at h1
  simp only [mul_one] at h1
  rw [opNorm_eq_norm]
  exact h1

/-- Consequence of `assum:app-setup-regime`, `section.tex` l.1106–1107 (snapshot `cr-2026-10-23`):
under the regime the output spectral measure `ν_out` is a positive measure on `[0, C_Σ]` of total
mass at most `γ⋆`. Proof route: eigenvalues of the PSD matrix `Σ_out` lie in `[0, ‖Σ_out‖]`
(`normOut`); the mass is `N_out / B ≤ γ⋆` by `dims`. -/
theorem assum_app_setup_regime_nuOut (R : SetupRegime) (k : ℕ) :
    nuOut (R.F k).C (R.B k) (Set.Icc 0 R.CSig)ᶜ = 0 ∧
      nuOut (R.F k).C (R.B k) Set.univ ≤ ENNReal.ofReal R.γstar := by
  classical
  have hBn : 0 < R.B k := (R.F k).hB
  have hB : (0 : ℝ) < (R.B k : ℝ) := by exact_mod_cast hBn
  have hmem : ∀ i, (R.F k).C.psdOut.isHermitian.eigenvalues i ∈ Set.Icc 0 R.CSig := fun i =>
    ⟨(R.F k).C.psdOut.eigenvalues_nonneg i,
      (le_abs_self _).trans ((abs_eigenvalues_le_opNorm_aux _ _ i).trans (R.normOut k))⟩
  have hz : ∀ i, Measure.dirac ((R.F k).C.psdOut.isHermitian.eigenvalues i)
      (Set.Icc 0 R.CSig)ᶜ = 0 := fun i => by
    rw [Measure.dirac_apply' _ (measurableSet_Icc.compl)]
    exact Set.indicator_of_notMem (s := (Set.Icc 0 R.CSig)ᶜ) (fun h => h (hmem i)) _
  have hnull : nuOut (R.F k).C (R.B k) (Set.Icc 0 R.CSig)ᶜ = 0 := by
    unfold nuOut
    simp [Measure.smul_apply, Measure.coe_finsetSum, Finset.sum_apply, hz]
  refine ⟨hnull, ?_⟩
  have hmass : nuOut (R.F k).C (R.B k) Set.univ =
      (R.B k : ENNReal)⁻¹ * ((R.m k : ℕ) : ENNReal) := by
    unfold nuOut
    simp [Measure.smul_apply, Measure.coe_finsetSum, Finset.sum_apply, smul_eq_mul]
  have hle : ((R.m k : ℕ) : ℝ) ≤ R.γstar * (R.B k : ℝ) :=
    le_trans (Nat.cast_le.mpr (le_max_left _ _)) (R.dims k)
  have hdiv : ((R.m k : ℕ) : ℝ) / (R.B k : ℝ) ≤ R.γstar := (div_le_iff₀ hB).mpr hle
  rw [hmass]
  calc (R.B k : ENNReal)⁻¹ * ((R.m k : ℕ) : ENNReal)
      = ENNReal.ofReal (((R.m k : ℕ) : ℝ) / (R.B k : ℝ)) := by
        rw [ENNReal.ofReal_div_of_pos hB, ENNReal.ofReal_natCast, ENNReal.ofReal_natCast,
          ENNReal.div_eq_inv_mul]
    _ ≤ ENNReal.ofReal R.γstar := ENNReal.ofReal_le_ofReal hdiv

/-- Consequence of `assum:app-setup-regime`, `section.tex` l.1106–1107 (snapshot `cr-2026-10-23`):
under the regime the input spectral measure `ν_in` is a positive measure on `[0, C_Σ]` of total
mass at most `γ⋆`. Same route as `assum_app_setup_regime_nuOut`, with `Σ_in` and `N_in`. -/
theorem assum_app_setup_regime_nuIn (R : SetupRegime) (k : ℕ) :
    nuIn (R.F k).C (R.B k) (Set.Icc 0 R.CSig)ᶜ = 0 ∧
      nuIn (R.F k).C (R.B k) Set.univ ≤ ENNReal.ofReal R.γstar := by
  classical
  have hBn : 0 < R.B k := (R.F k).hB
  have hB : (0 : ℝ) < (R.B k : ℝ) := by exact_mod_cast hBn
  have hmem : ∀ i, (R.F k).C.psdIn.isHermitian.eigenvalues i ∈ Set.Icc 0 R.CSig := fun i =>
    ⟨(R.F k).C.psdIn.eigenvalues_nonneg i,
      (le_abs_self _).trans ((abs_eigenvalues_le_opNorm_aux _ _ i).trans (R.normIn k))⟩
  have hz : ∀ i, Measure.dirac ((R.F k).C.psdIn.isHermitian.eigenvalues i)
      (Set.Icc 0 R.CSig)ᶜ = 0 := fun i => by
    rw [Measure.dirac_apply' _ (measurableSet_Icc.compl)]
    exact Set.indicator_of_notMem (s := (Set.Icc 0 R.CSig)ᶜ) (fun h => h (hmem i)) _
  have hnull : nuIn (R.F k).C (R.B k) (Set.Icc 0 R.CSig)ᶜ = 0 := by
    unfold nuIn
    simp [Measure.smul_apply, Measure.coe_finsetSum, Finset.sum_apply, hz]
  refine ⟨hnull, ?_⟩
  have hmass : nuIn (R.F k).C (R.B k) Set.univ =
      (R.B k : ENNReal)⁻¹ * ((R.n k : ℕ) : ENNReal) := by
    unfold nuIn
    simp [Measure.smul_apply, Measure.coe_finsetSum, Finset.sum_apply, smul_eq_mul]
  have hle : ((R.n k : ℕ) : ℝ) ≤ R.γstar * (R.B k : ℝ) :=
    le_trans (Nat.cast_le.mpr (le_max_right _ _)) (R.dims k)
  have hdiv : ((R.n k : ℕ) : ℝ) / (R.B k : ℝ) ≤ R.γstar := (div_le_iff₀ hB).mpr hle
  rw [hmass]
  calc (R.B k : ENNReal)⁻¹ * ((R.n k : ℕ) : ENNReal)
      = ENNReal.ofReal (((R.n k : ℕ) : ℝ) / (R.B k : ℝ)) := by
        rw [ENNReal.ofReal_div_of_pos hB, ENNReal.ofReal_natCast, ENNReal.ofReal_natCast,
          ENNReal.div_eq_inv_mul]
    _ ≤ ENNReal.ofReal R.γstar := ENNReal.ofReal_le_ofReal hdiv

/-! ## Deterministic equivalents (`def:deterministic-equivalent`) -/

/-- `def:deterministic-equivalent`, snapshot `cr-2026-10-23`. Declaration of record: the
deterministic equivalent `Mbar` of `M` in the proportional regime `R`, with normalizer `N k` and
spectral parameter `z ∈ ℂ ∖ [0,∞)`. The normalizer is a dimension of the regime: the source says
the dimension parameter is `N_in`, `N_out` or `B`, "determined by context" (l.1116, l.1131). The
Prop therefore requires `N` to equal one of the regime's dimension sequences `n`, `m`, `B` (one
choice for the whole sequence) and then `Muon.IsDetEquiv` (`Muon.Foundations.Conventions`) with
the domain fixed to `ℂ ∖ [0,∞)`. Without this clause a zero normalizer would make every pair a
deterministic equivalent. The definition, verbatim from `section.tex` (l.1115–1126):
```latex
\begin{definition}[Deterministic equivalent]\label{def:deterministic-equivalent}
Let $M_N(z)$ be a sequence of random matrices indexed by the dimension
parameter $N$ and depending on a spectral parameter $z\in\mathbb C\setminus[0,\infty)$.
A deterministic matrix family $\overline M_N(z)$ of the same size is a
\emph{deterministic equivalent} of $M_N(z)$ in the proportional regime
(\cref{assum:proportional-regime}) if, for every sequence of deterministic
test matrices $T_N$ with $\norm{T_N}$ bounded uniformly in $N$,
\[
\frac{1}{N}\,\Tr\!\big[(M_N(z) - \overline M_N(z))\,T_N\big] \;\xrightarrow{\;\Pr\;}\; 0
\qquad \text{as } N \to \infty.
\]
\end{definition}
```
-/
def def_deterministic_equivalent {m n B : ℕ → ℕ} {C : ∀ k : ℕ, Covariances (m k) (n k)}
    (_R : ProportionalRegime m n B C) {Ω : ℕ → Type*} [∀ k, MeasurableSpace (Ω k)]
    {d₁ d₂ : ℕ → ℕ} (P : ∀ k : ℕ, Measure (Ω k)) [∀ k, IsProbabilityMeasure (P k)]
    (N : ℕ → ℕ) (M : ∀ k : ℕ, ℂ → Ω k → Matrix (Fin (d₁ k)) (Fin (d₂ k)) ℂ)
    (Mbar : ∀ k : ℕ, ℂ → Matrix (Fin (d₁ k)) (Fin (d₂ k)) ℂ) : Prop :=
  (N = n ∨ N = m ∨ N = B) ∧ IsDetEquiv P N {z : ℂ | ∀ x : ℝ, 0 ≤ x → z ≠ (x : ℂ)} M Mbar

/-- Bridge for `def_deterministic_equivalent` (`section.tex` l.1115–1126, snapshot
`cr-2026-10-23`): mean-square convergence of the trace pairing, pointwise in `z ∈ Z`, implies the in-probability
statement of `IsDetEquiv`. Proof route: Chebyshev/Markov on `{ε ≤ ‖·‖}` with the second moment
(`meas_ge_le_lintegral_div`), using `hmeas` for measurability. The mean-square form is the one
proved in Appendix B. -/
theorem isDetEquiv_of_meanSquare {Ω : ℕ → Type*} [∀ k, MeasurableSpace (Ω k)]
    (P : ∀ k : ℕ, Measure (Ω k)) [∀ k, IsProbabilityMeasure (P k)] (N : ℕ → ℕ)
    {d₁ d₂ : ℕ → ℕ} (Z : Set ℂ)
    (M : ∀ k : ℕ, ℂ → Ω k → Matrix (Fin (d₁ k)) (Fin (d₂ k)) ℂ)
    (Mbar : ∀ k : ℕ, ℂ → Matrix (Fin (d₁ k)) (Fin (d₂ k)) ℂ)
    (hmeas : ∀ k : ℕ, ∀ z ∈ Z, ∀ i j, Measurable fun ω => M k z ω i j)
    (h : ∀ z ∈ Z, ∀ T : ∀ k : ℕ, Matrix (Fin (d₂ k)) (Fin (d₁ k)) ℂ,
      (∃ c : ℝ, ∀ k : ℕ, opNorm (T k) ≤ c) →
      Tendsto (fun k : ℕ => ∫⁻ ω, ENNReal.ofReal
        (‖(N k : ℂ)⁻¹ * ((M k z ω - Mbar k z) * T k).trace‖ ^ 2) ∂(P k)) atTop (𝓝 0)) :
    IsDetEquiv P N Z M Mbar := by
  unfold IsDetEquiv
  intro z hz T hT ε hε
  have hX : ∀ k : ℕ, Measurable fun ω => (N k : ℂ)⁻¹ * ((M k z ω - Mbar k z) * T k).trace := by
    intro k
    apply Measurable.const_mul
    unfold Matrix.trace
    refine Finset.measurable_sum _ fun i _ => ?_
    simp only [Matrix.diag, Matrix.mul_apply, Matrix.sub_apply]
    refine Finset.measurable_sum _ fun j _ => ?_
    exact ((hmeas k z hz _ _).sub measurable_const).mul measurable_const
  have hf : ∀ k : ℕ, AEMeasurable (fun ω => ENNReal.ofReal
      (‖(N k : ℂ)⁻¹ * ((M k z ω - Mbar k z) * T k).trace‖ ^ 2)) (P k) :=
    fun k => ((((hX k).norm).pow_const 2).ennreal_ofReal).aemeasurable
  have hI := h z hz T hT
  have hε2 : ENNReal.ofReal (ε ^ 2) ≠ 0 := (ENNReal.ofReal_pos.mpr (by positivity)).ne'
  have hε2' : ENNReal.ofReal (ε ^ 2) ≠ ⊤ := ENNReal.ofReal_ne_top
  have hbd : ∀ k, P k {ω | ε ≤ ‖(N k : ℂ)⁻¹ * ((M k z ω - Mbar k z) * T k).trace‖} ≤
      (∫⁻ ω, ENNReal.ofReal (‖(N k : ℂ)⁻¹ * ((M k z ω - Mbar k z) * T k).trace‖ ^ 2) ∂(P k)) *
        (ENNReal.ofReal (ε ^ 2))⁻¹ := by
    intro k
    refine le_trans (measure_mono ?_)
      ((meas_ge_le_lintegral_div (hf k) hε2 hε2').trans_eq (div_eq_mul_inv _ _))
    intro ω hω
    simp only [Set.mem_setOf_eq] at hω ⊢
    exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ hε.le hω 2)
  have h2 := ENNReal.Tendsto.mul_const hI (ENNReal.inv_ne_top.mpr hε2 |> Or.inr)
  rw [zero_mul] at h2
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h2
    (Filter.Eventually.of_forall fun _ => by simp) (Filter.Eventually.of_forall hbd)

/-- Bridge for `def_deterministic_equivalent` (`section.tex` l.1115–1126, snapshot
`cr-2026-10-23`): the deterministic equivalence is invariant under replacing the normalizer `N` by `N'` when
`N / N' → c` with `c ∈ (0,∞)`. Proof route: `N⁻¹ X = (N'/N) · (N'⁻¹ X)` and `N'/N → 1/c`; apply
`IsDetEquiv` to the bounded factor and use that `o_P(1)` times a bounded deterministic factor is
`o_P(1)`. -/
theorem isDetEquiv_congr_normalizer {Ω : ℕ → Type*} [∀ k, MeasurableSpace (Ω k)]
    (P : ∀ k : ℕ, Measure (Ω k)) (N N' : ℕ → ℕ) {c : ℝ} (hc : 0 < c)
    (hratio : Tendsto (fun k : ℕ => (N k : ℝ) / (N' k : ℝ)) atTop (𝓝 c))
    {d₁ d₂ : ℕ → ℕ} (Z : Set ℂ)
    (M : ∀ k : ℕ, ℂ → Ω k → Matrix (Fin (d₁ k)) (Fin (d₂ k)) ℂ)
    (Mbar : ∀ k : ℕ, ℂ → Matrix (Fin (d₁ k)) (Fin (d₂ k)) ℂ) :
    IsDetEquiv P N Z M Mbar ↔ IsDetEquiv P N' Z M Mbar := by
  have hid : ∀ a b : ℕ, (a : ℝ) ≠ 0 → (b : ℝ) ≠ 0 → ∀ y : ℂ,
      ‖(b : ℂ)⁻¹ * y‖ = ((a : ℝ) / (b : ℝ)) * ‖(a : ℂ)⁻¹ * y‖ := by
    intro a b ha hb y
    rw [norm_mul, norm_mul, norm_inv, norm_inv, Complex.norm_natCast, Complex.norm_natCast]
    field_simp
  have key : ∀ (A B : ℕ → ℕ) (c₀ : ℝ), 0 < c₀ →
      Tendsto (fun k : ℕ => (A k : ℝ) / (B k : ℝ)) atTop (𝓝 c₀) →
      IsDetEquiv P A Z M Mbar → IsDetEquiv P B Z M Mbar := by
    intro A B c₀ hc₀ hr hA
    unfold IsDetEquiv at hA ⊢
    intro z hz T hT ε hε
    have hev : ∀ᶠ k in atTop, c₀ / 2 < (A k : ℝ) / (B k : ℝ) :=
      hr.eventually (lt_mem_nhds (by linarith))
    have hbd : ∀ᶠ k in atTop, (A k : ℝ) / (B k : ℝ) ≤ c₀ + 1 := by
      filter_upwards [hr.eventually (gt_mem_nhds (lt_add_one c₀))] with k hk using hk.le
    have hkey := hA z hz T hT (ε / (c₀ + 1)) (div_pos hε (by linarith))
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hkey
      (Filter.Eventually.of_forall fun _ => by simp) ?_
    filter_upwards [hev, hbd] with k hk1 hk2
    have hB : (B k : ℝ) ≠ 0 := by
      intro h0; rw [h0, div_zero] at hk1; linarith
    have hA' : (A k : ℝ) ≠ 0 := by
      intro h0; rw [h0, zero_div] at hk1; linarith
    apply measure_mono
    intro ω hω
    simp only [Set.mem_setOf_eq] at hω ⊢
    rw [hid (A k) (B k) hA' hB] at hω
    rw [div_le_iff₀ (by linarith)]
    have hW := norm_nonneg ((A k : ℂ)⁻¹ * ((M k z ω - Mbar k z) * T k).trace)
    nlinarith [mul_le_mul_of_nonneg_right hk2 hW]
  constructor
  · exact key N N' c hc hratio
  · exact key N' N c⁻¹ (inv_pos.mpr hc) (by simpa only [inv_div] using hratio.inv₀ hc.ne')

end Muon.Setup

end
