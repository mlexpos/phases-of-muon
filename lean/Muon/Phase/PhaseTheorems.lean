import Mathlib
import Muon.Phase.Arrays
import Muon.Phase.Clock
import Muon.Phase.FirstHit
import Muon.Phase.Kernels
import Muon.Phase.PowerSums

/-!
# Appendix H: the power-law phase map (task L-H.8)

Snapshot `cr-2026-10-23`. Source: `sections/07-phase-comparison/section.tex`, subsection
"The adopted power-law arrays and the phase map" (l.1067–1341), with the windowed statements
`thm:app-phase-map`, `thm:app-phase-A`, `thm:app-phase-B`, `thm:app-phase-C`,
`prop:app-phase-C-window`, `cor:app-phase-ratio`. Card: `sections/07-phase-comparison/CARD.md`
§2, §3, §5 (L-H.8), §6.1, §6.4, §6.9.

Encoding decisions (statements only; proofs are `sorry` and filled by proof workers):
* Step times `t^j_{Tε}` are `stepHit m Q T ε := firstHit (riskClock m Q) (Tε)` (in `ℝ≥0∞`,
  `∞` if not attained), the reading fixed by `prop_app_phase_prefactors_iii`.
* Dimensionless first hits `û_j` are `dimHit Q T₀ T ε := firstHit (Q (T₀ ·)) (Tε)`; "the first
  hit is attained" is `dimHit ≠ ⊤`.
* Two-sided bounds on hitting times are `SandwichE` (ℝ≥0∞ arithmetic, so `∞` violates the
  upper bound). Bounds on ratios and heights are `Sandwich` on `ℝ`; for a ratio of `toReal`s
  the positive lower bound excludes `∞` and `0` (`toReal ∞ = 0`).
* Window constants. `thm_app_phase_A` and `thm_app_phase_B` existentially quantify
  `(Nst, Est, cLo, cHi)` with conclusion the named Prop `PhaseAWindowHolds` /
  `PhaseBWindowHolds`. `thm_app_phase_B_ii` is the existential `PhaseBWindowHolds ∧
  PhaseBEquivHolds` at one and the same tuple. The ratio statements `cor_app_phase_ratio_i`,
  `_ii`, `_iv` quantify the window constants universally over those Props, so they cannot pick
  other constants; their ratio bounds use the derived constants `cLo/cHi` and `cHi/cLo`.
  `thm_app_phase_C`, `thm_app_phase_C_ii` and `cor_app_phase_ratio_iii`, `_v` use `PhaseLowWindow`,
  which has no window constants, so their constants are existential.
* Sequence statements quantify over dependent families: for each `n`, a matched model
  `mS n : RowModel (Fin (Nseq n))` with a Volterra solution `QS n` (any solution, as in
  `prop_app_phase_prefactors_iii`). The standing assumption `1 ≤ Nseq n ≤ Bseq n` for all `n`
  is that of `def:app-phase-arrays` (`B ≥ N ≥ 1`), needed for the models to exist.
* `cor_app_phase_ratio_iv` (α > 1) takes `PhaseBWindowHolds` and `PhaseBEquivHolds` at the same
  constants; `cor_app_phase_ratio_v` (α ≤ 1) takes the sequences eventually in `PhaseLowWindow`.
-/

open MeasureTheory Set Filter Topology Asymptotics
open scoped ENNReal NNReal

set_option linter.style.longLine false

noncomputable section

namespace Muon.Phase

/-! ## Transcription helpers

These name displays of the section; they add no mathematical content. -/

/-- The step time `t^j_{Tε} = firstHit (riskClock m Q) (Tε)` of a matched model `m` with risk `Q`
(`prop:app-phase-prefactors`(iii), `thm:app-phase-hitting`), in `[0, ∞]`. -/
def stepHit {ι : Type*} (m : RowModel ι) (Q : ℝ → ℝ) (T ε : ℝ) : ℝ≥0∞ :=
  firstHit (riskClock m Q) (T * ε)

/-- The dimensionless first hit `û_j = inf{u ≥ 0 : Y_j(u) ≤ Tε}` with `Y_j(u) = Q(T_0 u)`
(`def:app-phase-arrays`), in `[0, ∞]`. -/
def dimHit (Q : ℝ → ℝ) (T0 T ε : ℝ) : ℝ≥0∞ :=
  firstHit (fun u => Q (T0 * u)) (T * ε)

/-- The two-sided bound `cLo X ≤ y ≤ cHi X` (the section's `y ≍ X` with constants `cLo ≤ cHi`). -/
def Sandwich (cLo cHi X y : ℝ) : Prop := cLo * X ≤ y ∧ y ≤ cHi * X

/-- The two-sided bound `cLo X ≤ t ≤ cHi X` for a hitting time `t ∈ [0, ∞]`; `t = ∞` violates
the upper bound. -/
def SandwichE (cLo cHi X : ℝ) (t : ℝ≥0∞) : Prop :=
  ENNReal.ofReal cLo * ENNReal.ofReal X ≤ t ∧ t ≤ ENNReal.ofReal cHi * ENNReal.ofReal X

/-- The window of `thm:app-phase-A`: `N ≥ N_*`, `B ≥ N`, `0 < ε < ε_0`, `ε N^{p-1} ≥ E_*`
(`p = α + ς`). -/
def PhaseWinA (α ς T : ℝ) (Nst : ℕ) (Est : ℝ) (N B : ℕ) (ε : ℝ) : Prop :=
  Nst ≤ N ∧ N ≤ B ∧ 0 < ε ∧ ε < phaseEps0 α ς T ∧ Est ≤ ε * (N : ℝ) ^ (α + ς - 1)

/-- The window of `thm:app-phase-B`: `N ≥ N_*`, `B ≥ N`, `0 < ε < ε_0`, `ε N ≥ E_*`. -/
def PhaseWinB (α ς T : ℝ) (Nst : ℕ) (Est : ℝ) (N B : ℕ) (ε : ℝ) : Prop :=
  Nst ≤ N ∧ N ≤ B ∧ 0 < ε ∧ ε < phaseEps0 α ς T ∧ Est ≤ ε * (N : ℝ)

/-- The rate on the right of `eqn:app-phase-ratio`, as a case table in `ς = \texp`. -/
def phaseRatioRate (α ς ε : ℝ) : ℝ :=
  if ς < 1 then ε ^ (-(α / (2 * (α + ς - 1))))
  else if ς = 1 then ε ^ (-(1 / 2 : ℝ)) / Real.log (1 / ε)
  else if ς < α + 1 then ε ^ (-((α + 1 - ς) / (2 * (α + ς - 1))))
  else if ς = α + 1 then Real.log (1 / ε)
  else 1

/-- The conclusion of `thm:app-phase-A` at the window constants `(Nst, Est, cLo, cHi)`: positivity,
the two-sided bounds on the window `PhaseWinA` for every matched pair with Volterra solutions
(attainment, the `rq`-exponent form, and the in-particular explicit exponents), the sequence
claim that sequences with `N → ∞`, `ε ↓ 0`, `εN^{p-1} → ∞` lie in the window uniformly over
`B ≥ N`, and the example `ε = N^{-ω}`. -/
def PhaseAWindowHolds (α ς T : ℝ) (Nst : ℕ) (Est cLo cHi : ℝ) : Prop :=
  0 < cLo ∧ cLo ≤ cHi ∧
  (∀ (N B : ℕ) (ε : ℝ) (mS mG : RowModel (Fin N)) (QS QG : ℝ → ℝ),
    PhaseWinA α ς T Nst Est N B ε →
    IsMatchedModel (svdArrays α ς N B) mS ε → IsVolterraSol mS QS →
    IsMatchedModel (sgdArrays α ς N B) mG ε → IsVolterraSol mG QG →
    (dimHit QS (svdT0 N B) T ε ≠ ⊤ ∧ dimHit QG (sgdT0 α N B) T ε ≠ ⊤) ∧
    SandwichE cLo cHi ((svdArrays α ς N B).S * svdT0 N B *
        ε ^ (-(1 / (2 * rq (α + ς) (α / 2))))) (stepHit mS QS T ε) ∧
    SandwichE cLo cHi ((sgdArrays α ς N B).S * sgdT0 α N B *
        ε ^ (-(1 / (2 * rq (α + ς) α)))) (stepHit mG QG T ε) ∧
    SandwichE cLo cHi ((svdArrays α ς N B).S * svdT0 N B *
        ε ^ (-(α / (2 * (α + ς - 1))))) (stepHit mS QS T ε) ∧
    SandwichE cLo cHi ((sgdArrays α ς N B).S * sgdT0 α N B *
        ε ^ (-(α / (α + ς - 1)))) (stepHit mG QG T ε)) ∧
  (∀ (Nseq Bseq : ℕ → ℕ) (εseq : ℕ → ℝ), Tendsto (fun n => (Nseq n : ℝ)) atTop atTop →
    Tendsto εseq atTop (𝓝 0) → (∀ n, 0 < εseq n) → (∀ n, 1 ≤ Nseq n) →
    (∀ n, Nseq n ≤ Bseq n) →
    Tendsto (fun n => εseq n * (Nseq n : ℝ) ^ (α + ς - 1)) atTop atTop →
    ∀ᶠ n in atTop, PhaseWinA α ς T Nst Est (Nseq n) (Bseq n) (εseq n)) ∧
  (∀ ω : ℝ, 0 < ω → ω < α + ς - 1 → ∀ Bseq : ℕ → ℕ, (∀ N, N ≤ Bseq N) →
    ∀ᶠ N in atTop, PhaseWinA α ς T Nst Est N (Bseq N) ((N : ℝ) ^ (-ω)))

/-- The conclusion of `thm:app-phase-B` at the window constants `(Nst, Est, cLo, cHi)`: positivity,
the two-sided bounds with `Π_{r_j}` on the window `PhaseWinB` (attainment for both `j`), and the
sequence claim that sequences with `N → ∞`, `ε ↓ 0`, `εN → ∞` lie in the window uniformly over
`B ≥ N`. -/
def PhaseBWindowHolds (α ς T : ℝ) (Nst : ℕ) (Est cLo cHi : ℝ) : Prop :=
  0 < cLo ∧ cLo ≤ cHi ∧
  (∀ (N B : ℕ) (ε : ℝ) (mS mG : RowModel (Fin N)) (QS QG : ℝ → ℝ),
    PhaseWinB α ς T Nst Est N B ε →
    IsMatchedModel (svdArrays α ς N B) mS ε → IsVolterraSol mS QS →
    IsMatchedModel (sgdArrays α ς N B) mG ε → IsVolterraSol mG QG →
    (dimHit QS (svdT0 N B) T ε ≠ ⊤ ∧ dimHit QG (sgdT0 α N B) T ε ≠ ⊤) ∧
    SandwichE cLo cHi ((svdArrays α ς N B).S * svdT0 N B *
        phasePi (rq (α + ς) (α / 2)) ε) (stepHit mS QS T ε) ∧
    SandwichE cLo cHi ((sgdArrays α ς N B).S * sgdT0 α N B *
        phasePi (rq (α + ς) α) ε) (stepHit mG QG T ε)) ∧
  (∀ (Nseq Bseq : ℕ → ℕ) (εseq : ℕ → ℝ), Tendsto (fun n => (Nseq n : ℝ)) atTop atTop →
    Tendsto εseq atTop (𝓝 0) → (∀ n, 0 < εseq n) → (∀ n, 1 ≤ Nseq n) →
    (∀ n, Nseq n ≤ Bseq n) →
    Tendsto (fun n => εseq n * (Nseq n : ℝ)) atTop atTop →
    ∀ᶠ n in atTop, PhaseWinB α ς T Nst Est (Nseq n) (Bseq n) (εseq n))

/-- The equivalents of `thm:app-phase-B` at the window constants `(Nst, Est)`: along every
sequence with `N → ∞`, `ε ↓ 0`, `B ≥ N ≥ 1` (the standing `def:app-phase-arrays` assumption), and
eventually in the window `PhaseWinB` at these constants, the equivalents for each `j`, guarded
by `r_j = 1` and `r_j > 1` (the source states no equivalent for `r_j < 1`). -/
def PhaseBEquivHolds (α ς T : ℝ) (Nst : ℕ) (Est : ℝ) : Prop :=
  ∀ (Nseq Bseq : ℕ → ℕ) (εseq : ℕ → ℝ)
    (mS mG : ∀ n, RowModel (Fin (Nseq n))) (QS QG : ∀ n, ℝ → ℝ),
    Tendsto (fun n => (Nseq n : ℝ)) atTop atTop → Tendsto εseq atTop (𝓝 0) →
    (∀ n, 0 < εseq n) → (∀ n, 1 ≤ Nseq n) → (∀ n, Nseq n ≤ Bseq n) →
    (∀ n, IsMatchedModel (svdArrays α ς (Nseq n) (Bseq n)) (mS n) (εseq n)) →
    (∀ n, IsVolterraSol (mS n) (QS n)) →
    (∀ n, IsMatchedModel (sgdArrays α ς (Nseq n) (Bseq n)) (mG n) (εseq n)) →
    (∀ n, IsVolterraSol (mG n) (QG n)) →
    (∀ᶠ n in atTop, PhaseWinB α ς T Nst Est (Nseq n) (Bseq n) (εseq n)) →
    (rq (α + ς) (α / 2) = 1 →
      IsEquivalent atTop (fun n => (stepHit (mS n) (QS n) T (εseq n)).toReal)
        (fun n => (svdArrays α ς (Nseq n) (Bseq n)).S * svdT0 (Nseq n) (Bseq n) /
          (4 * Real.sqrt (8 * (α / 2))) * (εseq n) ^ (-(1 / 2 : ℝ)) *
          Real.log (1 / εseq n))) ∧
    (1 < rq (α + ς) (α / 2) →
      IsEquivalent atTop (fun n => (stepHit (mS n) (QS n) T (εseq n)).toReal)
        (fun n => (svdArrays α ς (Nseq n) (Bseq n)).S * svdT0 (Nseq n) (Bseq n) *
          Jpq (α + ς) (α / 2) / (2 * Real.sqrt (εseq n)))) ∧
    (rq (α + ς) α = 1 →
      IsEquivalent atTop (fun n => (stepHit (mG n) (QG n) T (εseq n)).toReal)
        (fun n => (sgdArrays α ς (Nseq n) (Bseq n)).S * sgdT0 α (Nseq n) (Bseq n) /
          (4 * Real.sqrt (8 * α)) * (εseq n) ^ (-(1 / 2 : ℝ)) *
          Real.log (1 / εseq n))) ∧
    (1 < rq (α + ς) α →
      IsEquivalent atTop (fun n => (stepHit (mG n) (QG n) T (εseq n)).toReal)
        (fun n => (sgdArrays α ς (Nseq n) (Bseq n)).S * sgdT0 α (Nseq n) (Bseq n) *
          Jpq (α + ς) α / (2 * Real.sqrt (εseq n))))

/-! ## Harmonic-sum helpers for `thm_app_phase_map_moreover` -/

lemma pm_sandwich_of_ratio {f X : ℕ → ℝ} {L : ℝ} (hL : 0 < L)
    (hX : ∀ᶠ N : ℕ in atTop, 0 < X N)
    (hr : Tendsto (fun N : ℕ => f N / X N) atTop (𝓝 L)) :
    ∃ cLo cHi : ℝ, 0 < cLo ∧ cLo ≤ cHi ∧ ∀ᶠ N : ℕ in atTop, Sandwich cLo cHi (X N) (f N) := by
  refine ⟨L / 2, 2 * L, by linarith, by linarith, ?_⟩
  filter_upwards [hr.eventually (Ioo_mem_nhds (by linarith : L / 2 < L) (by linarith : L < 2 * L)),
    hX] with N hN hXN
  obtain ⟨h1, h2⟩ := hN
  unfold Sandwich
  constructor
  · exact le_of_lt ((lt_div_iff₀ hXN).mp h1)
  · exact le_of_lt ((div_lt_iff₀ hXN).mp h2)

lemma pm_harm_lt2 {a : ℝ} (ha : 0 < a) (ha1 : a < 1) :
    ∃ cLo cHi : ℝ, 0 < cLo ∧ cLo ≤ cHi ∧
      ∀ᶠ N : ℕ in atTop, Sandwich cLo cHi ((N : ℝ) ^ (1 - a)) (Hsum a N) := by
  have hc : (0 : ℝ) < 1 - a := by linarith
  have hE := lem_app_phase_harmonic_iii ha ha1
  have hX : ∀ᶠ N : ℕ in atTop, 0 < (N : ℝ) ^ (1 - a) := by
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
    exact Real.rpow_pos_of_pos hNpos _
  have hz : ∀ᶠ N : ℕ in atTop, (fun N : ℕ => (N : ℝ) ^ (1 - a) / (1 - a)) N ≠ 0 := by
    filter_upwards [hX] with N hN
    exact div_ne_zero hN.ne' hc.ne'
  have h1 : Tendsto (fun N : ℕ => Hsum a N / ((N : ℝ) ^ (1 - a) / (1 - a))) atTop (𝓝 1) :=
    (Asymptotics.isEquivalent_iff_tendsto_one hz).mp hE
  have h2 : Tendsto (fun N : ℕ => Hsum a N / ((N : ℝ) ^ (1 - a))) atTop
      (𝓝 (1 / (1 - a))) := by
    have := h1.div_const (1 - a)
    refine this.congr (fun N => ?_)
    field_simp
  exact pm_sandwich_of_ratio (by positivity) hX h2

lemma pm_harm_eq1 :
    ∃ cLo cHi : ℝ, 0 < cLo ∧ cLo ≤ cHi ∧
      ∀ᶠ N : ℕ in atTop, Sandwich cLo cHi (Real.log (N : ℝ)) (Hsum 1 N) := by
  have key : ∀ b : ℝ, 0 < b → ∫ x in (1 : ℝ)..b, x ^ (-(1 : ℝ)) = Real.log b := by
    intro b hb
    simp only [Real.rpow_neg_one]
    rw [integral_inv_of_pos one_pos hb]
    simp
  refine ⟨1, 2, by norm_num, by norm_num, ?_⟩
  filter_upwards [eventually_ge_atTop 3] with N hN
  have hN3 : (3 : ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := by linarith
  have hi := lem_app_phase_harmonic_i (a := 1) one_pos N (by omega)
  rw [key _ (by linarith)] at hi
  rw [key _ hNpos] at hi
  have hlogN : Real.log (N : ℝ) ≤ Real.log ((N : ℝ) + 1) :=
    Real.log_le_log hNpos (by linarith)
  have hexp : Real.exp 1 ≤ (N : ℝ) := by
    have := Real.exp_one_lt_d9
    norm_num at this
    linarith
  have hlog1 : (1 : ℝ) ≤ Real.log (N : ℝ) := by
    have := Real.log_le_log (Real.exp_pos 1) hexp
    rwa [Real.log_exp] at this
  unfold Sandwich
  constructor
  · linarith [hi.1]
  · linarith [hi.2]

lemma pm_harm_gt1 {a : ℝ} (ha : 1 < a) :
    ∃ cLo cHi : ℝ, 0 < cLo ∧ cLo ≤ cHi ∧
      ∀ᶠ N : ℕ in atTop, Sandwich cLo cHi 1 (Hsum a N) := by
  have hpos : 0 < 1 / (a - 1) := div_pos one_pos (by linarith)
  refine ⟨1, 1 + 1 / (a - 1), by norm_num, by linarith, ?_⟩
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hH1 : (1 : ℝ) ≤ Hsum a N := by
    have := Finset.single_le_sum (f := fun i : ℕ => (i : ℝ) ^ (-a))
      (s := Finset.Icc 1 N) (fun i _ => Real.rpow_nonneg (Nat.cast_nonneg i) _)
      (Finset.mem_Icc.mpr ⟨le_refl 1, hN⟩)
    unfold Hsum
    simpa using this
  have hup : zetaR a - Hsum a 1 ≤ 1 / (a - 1) := by
    have := (lem_app_phase_harmonic_vi ha 1 le_rfl).2
    simpa [Hsum, one_div] using this
  have hs : Hsum a 1 = 1 := by simp [Hsum]
  have hz := (lem_app_phase_harmonic_vi ha N hN).1
  unfold Sandwich
  constructor
  · linarith
  · linarith

/-! ## The phase map -/

/-- Label `thm:app-phase-map`, declaration of record. Snapshot `cr-2026-10-23`.

Statement (verbatim, `sections/07-phase-comparison/section.tex`, l.1229–1252):

```latex
\begin{theorem}[Time to $T\epsilon$ in the power-law phases]\label{thm:app-phase-map}
Fix $\alpha>0$ and $\texp$ with $\alpha+\texp>1$ and $\texp\notin\{1,\alpha+1\}$,
and fix $T\ge4$. Consider the arrays of \cref{def:app-phase-arrays} at their
matched steps along a sequence of $(N,B,\epsilon)$ with $N\to\infty$,
$\epsilon\downarrow0$ and integers $B\ge N$, such that
\begin{itemize}
\item $\epsilon N^{\alpha+\texp-1}\to\infty$ if $\texp<1$;
\item $\epsilon N\to\infty$ if $\texp>1$ and $\alpha>1$;
\item $(N,B,\epsilon)$ lies in the low-exponent window \cref{eqn:app-phase-height}
for all large indices if $\texp>1$ and $\alpha\le1$.
\end{itemize}
Then there are constants $0<c_-\le c_+$, depending only on $\alpha$, $\texp$ and
$T$, such that for all large indices of the sequence, with $x\asymp y$ meaning
$c_-\le x/y\le c_+$,
\begin{align}
t^{\text{s-SVD}}_{T\epsilon}&\asymp\gamma\,H_N(\alpha/2)\,\epsilon^{-\alpha/[2(\alpha+\texp-1)]}\ \ (\texp<1),&
t^{\text{s-SVD}}_{T\epsilon}&\asymp\sqrt\gamma\,\mathcal S_{\text{s-SVD}}\,\epsilon^{-1/2}\ \ (\texp>1),\label{eqn:app-phase-tsvd}\\
t^{\text{s-SGD}}_{T\epsilon}&\asymp\frac{N^2\pi\bar\mu}B\,\epsilon^{-\alpha/(\alpha+\texp-1)}\ \ (\texp<\alpha+1),&
t^{\text{s-SGD}}_{T\epsilon}&\asymp\sqrt{\frac{\pi\bar\mu}B}\,\mathcal S_{\text{s-SGD}}\,\epsilon^{-1/2}\ \ (\texp>\alpha+1).\label{eqn:app-phase-tsgd}
\end{align}
Moreover $H_N(\alpha/2)\asymp N^{1-\alpha/2}$ for $\alpha<2$,
$H_N(\alpha/2)\asymp\log N$ for $\alpha=2$, and $H_N(\alpha/2)\asymp1$ for $\alpha>2$,
with constants depending only on $\alpha$.
\end{theorem}
```
-/
theorem thm_app_phase_map_moreover (α : ℝ) (hα : 0 < α) :
    (α < 2 → ∃ cLo cHi : ℝ, 0 < cLo ∧ cLo ≤ cHi ∧
      ∀ᶠ N : ℕ in atTop, Sandwich cLo cHi ((N : ℝ) ^ (1 - α / 2)) (Hsum (α / 2) N)) ∧
    (α = 2 → ∃ cLo cHi : ℝ, 0 < cLo ∧ cLo ≤ cHi ∧
      ∀ᶠ N : ℕ in atTop, Sandwich cLo cHi (Real.log (N : ℝ)) (Hsum (α / 2) N)) ∧
    (2 < α → ∃ cLo cHi : ℝ, 0 < cLo ∧ cLo ≤ cHi ∧
      ∀ᶠ N : ℕ in atTop, Sandwich cLo cHi 1 (Hsum (α / 2) N)) := by
  refine ⟨fun hα2 => pm_harm_lt2 (a := α / 2) (by linarith) (by linarith), fun hα2 => ?_,
    fun h2 => pm_harm_gt1 (a := α / 2) (by linarith)⟩
  have h21 : α / 2 = 1 := by linarith
  rw [h21]
  exact pm_harm_eq1

/-! ### Proof helpers for `thm:app-phase-A` (P-H.8.P1) -/

lemma pw_Lsum_fin (N : ℕ) (a q u : ℝ) :
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

lemma pw_fNq_cont (N : ℕ) (p q : ℝ) : Continuous (fNq (N : ℕ∞) p q) := by
  unfold fNq
  show Continuous (fun u => 1 / 2 * Lsum (N : ℕ∞) p q u)
  simp_rw [pw_Lsum_fin]
  fun_prop

lemma pw_Lsum_nonneg (N : ℕ) (p q u : ℝ) : 0 ≤ Lsum (N : ℕ∞) p q u := by
  rw [pw_Lsum_fin]
  apply Finset.sum_nonneg
  intro i _
  positivity

lemma pw_Hsum_ge_one (p : ℝ) (N : ℕ) (hN : 1 ≤ N) : 1 ≤ Hsum p N := by
  unfold Hsum
  have h1 : (1:ℕ) ∈ Finset.Icc 1 N := Finset.mem_Icc.2 ⟨le_rfl, hN⟩
  have := Finset.single_le_sum (f := fun i : ℕ => (i : ℝ) ^ (-p)) (fun i _ => by positivity) h1
  simpa using this

lemma pw_fNq_zero (N : ℕ) (p q : ℝ) :
    fNq (N : ℕ∞) p q 0 = 1 / 2 * Hsum p N := by
  unfold fNq Hsum
  rw [pw_Lsum_fin]
  simp

lemma pw_Epq_pos {p q : ℝ} (hp : 1 < p) (hq : 0 < q) : 0 < Epq p q := by
  unfold Epq
  refine lt_max_of_lt_left ?_
  have : 0 < Za p := by
    unfold Za
    have := div_pos one_pos (show (0 : ℝ) < p - 1 by linarith)
    linarith
  exact mul_pos (Real.rpow_pos_of_pos (by norm_num) _) this

lemma pw_Cpq_pos {p q : ℝ} (hp : 1 < p) (hq : 0 < q) : 0 < Cpq p q := by
  unfold Cpq
  exact Real.sqrt_pos.2 (by have := pw_Epq_pos hp hq; positivity)

lemma pw_rq_pos {p q : ℝ} (hp : 1 < p) (hq : 0 < q) : 0 < rq p q := by
  unfold rq; exact div_pos (by linarith) (by linarith)

lemma pw_fNq_le {p q : ℝ} (hp : 1 < p) (hq : 0 < q) (N : ℕ) {u : ℝ} (hu : 0 ≤ u) :
    fNq (N : ℕ∞) p q u ≤ Cpq p q ^ 2 * (1 + u) ^ (-(2 * rq p q)) := by
  have h := lem_app_phase_sums_i hp hq (N : ℕ∞) hu
  have hd : dAQ p q = 2 * rq p q := by unfold dAQ rq; field_simp
  rw [hd] at h
  have hC : Cpq p q ^ 2 = Epq p q / 2 := by
    unfold Cpq
    rw [Real.sq_sqrt]
    have := pw_Epq_pos hp hq; positivity
  rw [hC]
  unfold fNq
  linarith

lemma pw_alg {C D ε r : ℝ} (hC : 0 < C) (hD : 0 < D) (hε : 0 < ε) (hr0 : 0 < r) (hr1 : r < 1) :
    C * (D * (C / Real.sqrt ε) ^ (1 / r)) ^ (1 - r)
      = D ^ (1 - r) * C ^ (1 / r) * ε ^ (-((1 - r) / (2 * r))) := by
  have hs : 0 < Real.sqrt ε := Real.sqrt_pos.2 hε
  have hCs : 0 < C / Real.sqrt ε := div_pos hC hs
  have hX : 0 < (C / Real.sqrt ε) ^ (1 / r) := Real.rpow_pos_of_pos hCs _
  rw [Real.mul_rpow hD.le hX.le, ← Real.rpow_mul hCs.le, Real.div_rpow hC.le hs.le,
    Real.sqrt_eq_rpow, ← Real.rpow_mul hε.le]
  have e1 : 1 / r * (1 - r) = (1 - r) / r := by field_simp
  rw [e1]
  have e2 : C ^ ((1 - r) / r) * C = C ^ (1 / r) := by
    rw [← Real.rpow_add_one hC.ne']
    congr 1
    field_simp
    ring
  have e3 : ε ^ (1 / 2 * ((1 - r) / r)) = ε ^ ((1 - r) / (2 * r)) := by
    congr 1; field_simp
  rw [e3, Real.rpow_neg hε.le]
  have hε' : 0 < ε ^ ((1 - r) / (2 * r)) := Real.rpow_pos_of_pos hε _
  rw [← e2]
  field_simp


lemma pw_Ir_le {r x : ℝ} (hr0 : 0 < r) (hr1 : r < 1) (hx : 0 ≤ x) :
    Ir r x ≤ (1 + x) ^ (1 - r) / (1 - r) := by
  unfold Ir
  rw [intervalIntegral.integral_comp_add_left (fun y : ℝ => y ^ (-r)) 1]
  rw [integral_rpow (Or.inl (by linarith))]
  have h1 : (0:ℝ) ^ (-r + 1) = 0 := Real.zero_rpow (by linarith)
  simp only [add_zero]
  rw [Real.one_rpow] at *
  have e : -r + 1 = 1 - r := by ring
  rw [e]
  have hpos : 0 < 1 - r := by linarith
  have : (1 + x) ^ (1 - r) - 1 ≤ (1 + x) ^ (1 - r) := by linarith
  rw [div_le_div_iff_of_pos_right hpos]
  exact this

lemma pw_eps_facts {p q T : ℝ} (ε : ℝ) (h : ε < clockEps0 p q T) :
    ε < 1 / (8 * T) ∧ ε < Cpq p q ^ 2 := by
  unfold clockEps0 at h
  split_ifs at h <;> simp only [lt_min_iff] at h
  · exact ⟨h.1.1.1.2, h.1.1.2⟩
  · exact ⟨h.1.1.2, h.1.2⟩



lemma pw_core {p q T D : ℝ} (hp : 1 < p) (hq : 0 < q) (hT : 4 ≤ T) (hD : 1 ≤ D)
    (hr : rq p q < 1) :
    ∃ L U : ℝ, 0 < L ∧ 0 < U ∧ ∀ (N : ℕ) (ε : ℝ) (g Y : ℝ → ℝ), 4 ≤ N → 0 < ε →
      ε < clockEps0 p q T →
      ContinuousOn g (Ici 0) → (∀ u ∈ Ici (0:ℝ), 0 ≤ g u) → IntegrableOn g (Ioi 0) →
      ∫ u in Ioi (0:ℝ), g u ≤ 1 →
      ContinuousOn Y (Ici 0) → (∀ u ∈ Ici (0:ℝ), 0 < Y u) →
      (∀ u ∈ Ici (0:ℝ), Y u = fNq (N:ℕ∞) p q u +
          Real.sqrt ε * Muon.Foundations.oneSidedConv (fun v => Real.sqrt (Y v)) g u) →
      (∀ u ∈ Icc (0:ℝ) (D * ((Cpq p q / Real.sqrt ε) ^ (1 / rq p q) - 1)),
          Muon.Foundations.oneSidedConv (fun w => Cpq p q * (1 + w / D) ^ (-rq p q)) g u
            ≤ 2 * (Cpq p q * (1 + u / D) ^ (-rq p q))) →
      D * ((Cpq p q / Real.sqrt ε) ^ (1 / rq p q) - 1) ≤ ((N:ℝ) / 4) ^ q →
      ∃ û : ℝ, firstHit Y (T * ε) = ENNReal.ofReal û ∧ 0 < û ∧
        L * ε ^ (-((1 - rq p q) / (2 * rq p q))) ≤ ∫ u in (0:ℝ)..û, Real.sqrt (Y u) ∧
        ∫ u in (0:ℝ)..û, Real.sqrt (Y u) ≤ U * ε ^ (-((1 - rq p q) / (2 * rq p q))) := by
  have hr0 := pw_rq_pos hp hq
  have hC := pw_Cpq_pos hp hq
  have hA0 : 0 < Aconst p := by unfold Aconst; positivity
  have hT0 : 0 < T := by linarith
  have hD0 : 0 < D := by linarith
  set r := rq p q with hr_def
  set C := Cpq p q with hC_def
  refine ⟨Real.sqrt (Aconst p) / (2 * (1 - r)) * (Aconst p / T) ^ ((1 - r) / (2 * r)),
    D ^ (1 - r) * C ^ (1 / r) / (1 - r) + D * C ^ (1 / r) * (Real.sqrt 2 / (1 - r / 2) + 1),
    ?_, ?_, ?_⟩
  · have : 0 < 1 - r := by linarith
    have h1 : 0 < Real.sqrt (Aconst p) := Real.sqrt_pos.2 hA0
    positivity
  · have : 0 < 1 - r := by linarith
    have : 0 < 1 - r / 2 := by linarith
    have : 0 < C ^ (1 / r) := Real.rpow_pos_of_pos hC _
    have : 0 < D ^ (1 - r) := Real.rpow_pos_of_pos hD0 _
    positivity
  intro N ε g Y hN hε hε0 hg_cont hg_nn hg_int hg_mass hY_cont hY_pos hY hconv hHN
  obtain ⟨hε8, hεC⟩ := pw_eps_facts ε hε0
  have hs : 0 < Real.sqrt ε := Real.sqrt_pos.2 hε
  have hN1 : 1 ≤ N := by omega
  -- the envelope
  obtain ⟨hh_ge, hh_H, h1H, hint⟩ := lem_app_phase_square_iii (C := C) (D := D) (r0 := r)
    (ε := ε) (H := D * ((C / Real.sqrt ε) ^ (1 / r) - 1)) (h := fun u => C * (1 + u / D) ^ (-r))
    hC hD hr0 (by linarith) hε hεC (fun u => rfl) rfl
  set H := D * ((C / Real.sqrt ε) ^ (1 / r) - 1) with hH_def
  have hX1 : 1 < (C / Real.sqrt ε) ^ (1 / r) := by
    apply Real.one_lt_rpow _ (by positivity)
    rw [one_lt_div hs]
    calc Real.sqrt ε < Real.sqrt (C ^ 2) := Real.sqrt_lt_sqrt hε.le hεC
      _ = C := Real.sqrt_sq hC.le
  have hHpos : 0 < H := mul_pos hD0 (by linarith)
  have hf0 : T * ε < fNq (N : ℕ∞) p q 0 := by
    rw [pw_fNq_zero]
    have := pw_Hsum_ge_one p N hN1
    have h2 : T * ε < 1 / 8 := by
      have := mul_lt_mul_of_pos_left hε8 hT0
      rw [mul_one_div, mul_comm 8 T, ← div_div, div_self hT0.ne'] at this
      linarith
    linarith
  have hhc : ContinuousOn (fun u => C * (1 + u / D) ^ (-r)) (Icc 0 H) := by
    apply ContinuousOn.mul continuousOn_const
    apply ContinuousOn.rpow_const (by fun_prop)
    intro x hx
    left
    have : 0 ≤ x / D := div_nonneg hx.1 hD0.le
    linarith
  have hfh : ∀ u ∈ Icc (0:ℝ) H, fNq (N:ℕ∞) p q u ≤ (C * (1 + u / D) ^ (-r)) ^ 2 := by
    intro u hu
    have hle := pw_fNq_le hp hq N hu.1
    refine hle.trans ?_
    have hb : 0 < 1 + u / D := by have : 0 ≤ u / D := div_nonneg hu.1 hD0.le; linarith
    have hmono : (1 + u) ^ (-(2 * r)) ≤ (1 + u / D) ^ (-(2 * r)) := by
      apply Real.rpow_le_rpow_of_nonpos hb _ (by linarith)
      have : u / D ≤ u := by
        rw [div_le_iff₀ hD0]; nlinarith [hu.1]
      linarith
    have hsq : ((1 + u / D) ^ (-r)) ^ 2 = (1 + u / D) ^ (-(2 * r)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hb.le]
      congr 1; push_cast; ring
    rw [mul_pow, hsq]
    exact mul_le_mul_of_nonneg_left hmono (by positivity)
  have hf_nn : ∀ u ∈ Ici (0:ℝ), 0 ≤ fNq (N:ℕ∞) p q u := by
    intro u _; unfold fNq; have := pw_Lsum_nonneg N p q u; positivity
  have hsq_i := lem_app_phase_square_i (ε := ε) (T := T) (H := H) hε hT hHpos
    (f := fNq (N:ℕ∞) p q) (g := g) (h := fun u => C * (1 + u / D) ^ (-r)) (Y := Y)
    hg_cont hg_nn hg_int hg_mass (pw_fNq_cont N p q).continuousOn hf_nn hf0 hY_cont hY_pos hY
    hhc hh_ge hh_H hfh (Or.inl hconv)
  have hsq_ii := lem_app_phase_square_ii (ε := ε) (T := T) (H := H) hε hT hHpos
    (f := fNq (N:ℕ∞) p q) (g := g) (h := fun u => C * (1 + u / D) ^ (-r)) (Y := Y)
    hg_cont hg_nn hg_int hg_mass (pw_fNq_cont N p q).continuousOn hf_nn hf0 hY_cont hY_pos hY
    hhc hh_ge hh_H hfh (Or.inl hconv)
  obtain ⟨û, hhit, hû0, hûH, hYû, hE0, hE1, -⟩ := hsq_ii
  have hYf : ∀ u ∈ Ici (0:ℝ), fNq (N:ℕ∞) p q u ≤ Y u := by
    intro u hu
    rw [hY u hu]
    have hconv0 : 0 ≤ Muon.Foundations.oneSidedConv (fun v => Real.sqrt (Y v)) g u := by
      unfold Muon.Foundations.oneSidedConv
      apply intervalIntegral.integral_nonneg hu
      intro s hs
      exact mul_nonneg (Real.sqrt_nonneg _) (hg_nn s (Set.mem_Ici.2 hs.1))
    have := mul_nonneg hs.le hconv0
    linarith
  obtain ⟨hlow, hup⟩ := lem_app_phase_clock_integral_i (p := p) (q := q) (T := T) (ε := ε)
    (H := H) (û := û) hp hq hT N hN hε hε0 hY_cont hYf hhit hû0 hYû hûH hr hHN
  refine ⟨û, hhit, hû0, hlow, ?_⟩
  have hIr := pw_Ir_le hr0 hr (show 0 ≤ H from hHpos.le)
  have hpow1 : (1 + H) ^ (1 - r) ≤ (D * (C / Real.sqrt ε) ^ (1 / r)) ^ (1 - r) :=
    Real.rpow_le_rpow (by linarith) h1H (by linarith)
  have h1r : 0 < 1 - r := by linarith
  have hstep : C * Ir r H ≤ D ^ (1 - r) * C ^ (1 / r) / (1 - r) * ε ^ (-((1 - r) / (2 * r))) := by
    have h2 : C * Ir r H ≤ C * ((D * (C / Real.sqrt ε) ^ (1 / r)) ^ (1 - r) / (1 - r)) :=
      mul_le_mul_of_nonneg_left (hIr.trans (div_le_div_of_nonneg_right hpow1 h1r.le)) hC.le
    refine h2.trans (le_of_eq ?_)
    rw [← mul_div_assoc, pw_alg hC hD0 hε hr0 hr]
    ring
  have hE : ∫ u in (0:ℝ)..û, (Real.sqrt (Y u) - Real.sqrt (fNq (N:ℕ∞) p q u)) ≤
      D * C ^ (1 / r) * (Real.sqrt 2 / (1 - r / 2) + 1) * ε ^ (-((1 - r) / (2 * r))) := by
    refine hE1.trans (hint.trans (le_of_eq ?_))
    congr 2
    ring
  nlinarith [hstep, hE, hup]

lemma pw_exp_alg {ε r : ℝ} (hε : 0 < ε) (hr0 : 0 < r) :
    ε ^ (-(1 / (2 * r))) = (Real.sqrt ε)⁻¹ * ε ^ (-((1 - r) / (2 * r))) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_neg hε.le, ← Real.rpow_add hε]
  congr 1
  field_simp
  ring

lemma pw_gen {p q T D : ℝ} (hp : 1 < p) (hq : 0 < q) (hT : 4 ≤ T) (hD : 1 ≤ D)
    (hr : rq p q < 1) :
    ∃ cL cH : ℝ, 0 < cL ∧ 0 < cH ∧ ∀ (N : ℕ) (ε S T0 : ℝ) (m : RowModel (Fin N)) (Q : ℝ → ℝ)
      (g : ℝ → ℝ), 4 ≤ N → 0 < ε → ε < clockEps0 p q T → 0 < S → 0 < T0 →
      ContinuousOn g (Ici 0) → (∀ u ∈ Ici (0:ℝ), 0 ≤ g u) → IntegrableOn g (Ioi 0) →
      ∫ u in Ioi (0:ℝ), g u ≤ 1 →
      ContinuousOn (fun u => Q (T0 * u)) (Ici 0) → (∀ u ∈ Ici (0:ℝ), 0 < Q (T0 * u)) →
      (∀ u ∈ Ici (0:ℝ), Q (T0 * u) = fNq (N:ℕ∞) p q u +
          Real.sqrt ε * Muon.Foundations.oneSidedConv (fun v => Real.sqrt (Q (T0 * v))) g u) →
      (∀ u ∈ Icc (0:ℝ) (D * ((Cpq p q / Real.sqrt ε) ^ (1 / rq p q) - 1)),
          Muon.Foundations.oneSidedConv (fun w => Cpq p q * (1 + w / D) ^ (-rq p q)) g u
            ≤ 2 * (Cpq p q * (1 + u / D) ^ (-rq p q))) →
      D * ((Cpq p q / Real.sqrt ε) ^ (1 / rq p q) - 1) ≤ ((N:ℝ) / 4) ^ q →
      (dimHit Q T0 T ε ≠ ⊤ → stepHit m Q T ε = ENNReal.ofReal (S * T0 / (2 * Real.sqrt ε) *
          ∫ u in (0:ℝ)..(dimHit Q T0 T ε).toReal, Real.sqrt (Q (T0 * u)))) →
      dimHit Q T0 T ε ≠ ⊤ ∧
      SandwichE cL cH (S * T0 * ε ^ (-(1 / (2 * rq p q)))) (stepHit m Q T ε) := by
  obtain ⟨L, U, hL, hU, hcore⟩ := pw_core hp hq hT hD hr
  refine ⟨L / 2, U / 2, by positivity, by positivity, ?_⟩
  intro N ε S T0 m Q g hN hε hε0 hS hT0 hgc hgn hgi hgm hYc hYp hYe hconv hHN hstep
  obtain ⟨û, hhit, hû0, hlow, hup⟩ := hcore N ε g (fun u => Q (T0 * u)) hN hε hε0 hgc hgn hgi hgm
    hYc hYp hYe hconv hHN
  have hdim : dimHit Q T0 T ε = ENNReal.ofReal û := hhit
  have hne : dimHit Q T0 T ε ≠ ⊤ := by rw [hdim]; exact ENNReal.ofReal_ne_top
  refine ⟨hne, ?_⟩
  have hst := hstep hne
  rw [hdim, ENNReal.toReal_ofReal hû0.le] at hst
  rw [hst]
  have hr0 := pw_rq_pos hp hq
  have hs : 0 < Real.sqrt ε := Real.sqrt_pos.2 hε
  have hX : S * T0 * ε ^ (-(1 / (2 * rq p q))) = S * T0 * (Real.sqrt ε)⁻¹ * ε ^ (-((1 - rq p q) / (2 * rq p q))) := by
    rw [pw_exp_alg hε hr0]; ring
  have hpre : 0 < S * T0 / (2 * Real.sqrt ε) := by positivity
  have hXpos : 0 < S * T0 * ε ^ (-(1 / (2 * rq p q))) := by
    have := Real.rpow_pos_of_pos hε (-(1 / (2 * rq p q))); positivity
  have hcl : L / 2 * (S * T0 * ε ^ (-(1 / (2 * rq p q)))) ≤
      S * T0 / (2 * Real.sqrt ε) * ∫ u in (0:ℝ)..û, Real.sqrt (Q (T0 * u)) := by
    rw [hX]
    calc _ = S * T0 / (2 * Real.sqrt ε) * (L * ε ^ (-((1 - rq p q) / (2 * rq p q)))) := by
          field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left hlow hpre.le
  have hch : S * T0 / (2 * Real.sqrt ε) * ∫ u in (0:ℝ)..û, Real.sqrt (Q (T0 * u)) ≤
      U / 2 * (S * T0 * ε ^ (-(1 / (2 * rq p q)))) := by
    rw [hX]
    calc _ ≤ S * T0 / (2 * Real.sqrt ε) * (U * ε ^ (-((1 - rq p q) / (2 * rq p q)))) :=
          mul_le_mul_of_nonneg_left hup hpre.le
      _ = _ := by field_simp
  constructor
  · rw [← ENNReal.ofReal_mul (by positivity)]
    exact ENNReal.ofReal_le_ofReal hcl
  · rw [← ENNReal.ofReal_mul (by positivity)]
    exact ENNReal.ofReal_le_ofReal hch

lemma pw_Q_facts {N : ℕ} (m : RowModel (Fin N)) (Q : ℝ → ℝ) (hQ : IsVolterraSol m Q)
    (T0 : ℝ) (hT0 : 0 < T0) :
    ContinuousOn (fun u => Q (T0 * u)) (Ici 0) ∧ ∀ u ∈ Ici (0:ℝ), 0 < Q (T0 * u) := by
  refine ⟨hQ.1.comp (continuous_const.mul continuous_id).continuousOn ?_, ?_⟩
  · intro u hu
    exact mul_nonneg hT0.le hu
  · intro u hu
    have := thm_app_phase_volterra_iii m Q hQ (T0 * u) (mul_nonneg hT0.le hu)
    exact this.1.trans_le this.2.1

lemma pw_svd_facts (α ς : ℝ) (N B : ℕ) (hα : 0 < α) (hp : 1 < α + ς)
    (hN : 1 ≤ N) (hNB : N ≤ B) (ε : ℝ) (hε : 0 < ε) (mS mG : RowModel (Fin N))
    (hmS : IsMatchedModel (svdArrays α ς N B) mS ε)
    (hmG : IsMatchedModel (sgdArrays α ς N B) mG ε)
    (QS QG : ℝ → ℝ) (hQS : IsVolterraSol mS QS) (hQG : IsVolterraSol mG QG) :
    ContinuousOn (dimKernel mS (svdT0 N B) ε) (Ici 0) ∧
    (∀ u ∈ Ici (0:ℝ), 0 ≤ dimKernel mS (svdT0 N B) ε u) ∧
    IntegrableOn (dimKernel mS (svdT0 N B) ε) (Ioi 0) ∧
    ∫ u in Ioi (0:ℝ), dimKernel mS (svdT0 N B) ε u ≤ 1 ∧
    (∀ u ∈ Ici (0:ℝ), dimKernel mS (svdT0 N B) ε u = svdKernel α N u) ∧
    (∀ u ∈ Ici (0:ℝ), QS (svdT0 N B * u) = fNq (N : ℕ∞) (α + ς) (α / 2) u +
        Real.sqrt ε * Muon.Foundations.oneSidedConv (fun v => Real.sqrt (QS (svdT0 N B * v)))
          (dimKernel mS (svdT0 N B) ε) u) := by
  obtain ⟨-, -, hQ3, -, hK, -⟩ := prop_app_phase_prefactors_ii α ς N B hα hp hN hNB ε hε mS mG hmS hmG QS QG hQS hQG
  obtain ⟨⟨hpos, hcont, -, hint, hmass, -, -⟩, -⟩ :=
    prop_app_phase_prefactors_ii_props α ς N B hα hp hN hNB ε hε mS mG hmS hmG
  refine ⟨hcont, fun u hu => (hpos u hu).le, hint, hmass.le, fun u hu => ?_, fun u hu => hQ3 u hu⟩
  rw [hK u hu]
  rfl

lemma pw_sgd_facts (α ς : ℝ) (N B : ℕ) (hα : 0 < α) (hp : 1 < α + ς)
    (hN : 1 ≤ N) (hNB : N ≤ B) (ε : ℝ) (hε : 0 < ε) (mS mG : RowModel (Fin N))
    (hmS : IsMatchedModel (svdArrays α ς N B) mS ε)
    (hmG : IsMatchedModel (sgdArrays α ς N B) mG ε)
    (QS QG : ℝ → ℝ) (hQS : IsVolterraSol mS QS) (hQG : IsVolterraSol mG QG) :
    ContinuousOn (dimKernel mG (sgdT0 α N B) ε) (Ici 0) ∧
    (∀ u ∈ Ici (0:ℝ), 0 ≤ dimKernel mG (sgdT0 α N B) ε u) ∧
    AntitoneOn (dimKernel mG (sgdT0 α N B) ε) (Ici 0) ∧
    IntegrableOn (dimKernel mG (sgdT0 α N B) ε) (Ioi 0) ∧
    ∫ u in Ioi (0:ℝ), dimKernel mG (sgdT0 α N B) ε u ≤ 1 ∧
    (∀ u ∈ Ici (0:ℝ), QG (sgdT0 α N B * u) = fNq (N : ℕ∞) (α + ς) α u +
        Real.sqrt ε * Muon.Foundations.oneSidedConv (fun v => Real.sqrt (QG (sgdT0 α N B * v)))
          (dimKernel mG (sgdT0 α N B) ε) u) := by
  obtain ⟨-, -, -, hQ4, -, hK⟩ := prop_app_phase_prefactors_ii α ς N B hα hp hN hNB ε hε mS mG hmS hmG QS QG hQS hQG
  obtain ⟨-, ⟨hpos, hcont, hanti, -, -, hi1, hv1, hi2, hv2⟩⟩ :=
    prop_app_phase_prefactors_ii_props α ς N B hα hp hN hNB ε hε mS mG hmS hmG
  have hcongr : ∀ u ∈ Ioi (0:ℝ), dimKernel mG (sgdT0 α N B) ε u =
      2 * (1 - 2 / Real.pi) / (N : ℝ) * Lsum (N : ℕ∞) α α u
          + 4 / (Real.pi * Hsum α N) * Lsum (N : ℕ∞) (2 * α) α u := fun u hu => hK u (le_of_lt hu)
  have hint : IntegrableOn (dimKernel mG (sgdT0 α N B) ε) (Ioi 0) :=
    (hi1.add hi2).congr_fun (fun u hu => (hcongr u hu).symm) measurableSet_Ioi
  have hmass : ∫ u in Ioi (0:ℝ), dimKernel mG (sgdT0 α N B) ε u = 1 := by
    rw [setIntegral_congr_fun measurableSet_Ioi hcongr, integral_add hi1 hi2, hv1, hv2]
    ring
  exact ⟨hcont, fun u hu => (hpos u hu).le, hanti, hint, hmass.le, fun u hu => hQ4 u hu⟩

lemma pw_horizon {C D τ r q ε E N : ℝ} (hC : 0 < C) (hD : 0 < D) (hτ : 0 < τ)
    (hr : 0 < r) (hq : 0 < q) (hε : 0 < ε) (hN : 0 < N)
    (hE : C ^ 2 * (D / τ) ^ (2 * r) ≤ E) (hEε : E ≤ ε * N ^ (2 * q * r)) :
    D * ((C / Real.sqrt ε) ^ (1 / r) - 1) ≤ τ * N ^ q := by
  have hs : 0 < Real.sqrt ε := Real.sqrt_pos.2 hε
  set a := τ / D with ha_def
  have ha : 0 < a := div_pos hτ hD
  have hNq : 0 < N ^ q := Real.rpow_pos_of_pos hN _
  set W := a * N ^ q with hW_def
  have hW : 0 < W := mul_pos ha hNq
  have hWr : 0 < W ^ r := Real.rpow_pos_of_pos hW _
  have h1 : (D / τ) ^ (2 * r) * a ^ (2 * r) = 1 := by
    rw [← Real.mul_rpow (div_pos hD hτ).le ha.le, ha_def]
    rw [show D / τ * (τ / D) = 1 by field_simp]
    exact Real.one_rpow _
  have h2 : (W ^ r) ^ 2 = a ^ (2 * r) * N ^ (2 * q * r) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hW.le, hW_def, Real.mul_rpow ha.le hNq.le,
      ← Real.rpow_mul hN.le]
    congr 2
    · push_cast; ring
    · push_cast; ring
  have h3 : C ^ 2 ≤ ε * (W ^ r) ^ 2 := by
    rw [h2]
    have hA : 0 < a ^ (2 * r) := Real.rpow_pos_of_pos ha _
    have := mul_le_mul_of_nonneg_left (hE.trans hEε) hA.le
    calc C ^ 2 = a ^ (2 * r) * (C ^ 2 * (D / τ) ^ (2 * r)) := by
          linear_combination (-(C ^ 2)) * h1
      _ ≤ a ^ (2 * r) * (ε * N ^ (2 * q * r)) :=
          mul_le_mul_of_nonneg_left (hE.trans hEε) hA.le
      _ = _ := by ring
  have h4 : C / Real.sqrt ε ≤ W ^ r := by
    rw [div_le_iff₀ hs]
    have : C ^ 2 ≤ (W ^ r * Real.sqrt ε) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hε.le]; linarith
    exact (pow_le_pow_iff_left₀ hC.le (by positivity) (by norm_num : (2:ℕ) ≠ 0)).1 this
  have h5 : (C / Real.sqrt ε) ^ (1 / r) ≤ W := by
    calc (C / Real.sqrt ε) ^ (1 / r) ≤ (W ^ r) ^ (1 / r) :=
          Real.rpow_le_rpow (div_pos hC hs).le h4 (by positivity)
      _ = W := by
          rw [← Real.rpow_mul hW.le]
          rw [mul_one_div_cancel hr.ne', Real.rpow_one]
  have h6 : D * W = τ * N ^ q := by
    rw [hW_def, ha_def]; field_simp
  nlinarith [mul_le_mul_of_nonneg_left h5 hD.le]

lemma pw_muBar_pos (α : ℝ) {N : ℕ} (hN : 1 ≤ N) : 0 < muBarOf α N := by
  unfold muBarOf
  have h1 := pw_Hsum_ge_one α N hN
  have : (0:ℝ) < N := by exact_mod_cast hN
  positivity

lemma pw_S_eq (α ς : ℝ) (N : ℕ) (A : PhaseArrays (Fin N)) (m : RowModel (Fin N)) (ε : ℝ)
    (hm : IsMatchedModel A m ε) : m.S = A.S := by
  obtain ⟨hμ, hd, hv, -, -⟩ := hm
  unfold RowModel.S PhaseArrays.S
  rw [hμ, hd, hv]

lemma pw_sgd_main (α ς T : ℝ) (hα : 0 < α) (hς1 : 1 - α < ς) (hς2 : ς < 1)
    (hT : 4 ≤ T) :
    ∃ (N1 : ℕ) (E1 cL cH : ℝ), 4 ≤ N1 ∧ 0 < cL ∧ 0 < cH ∧
      ∀ (N B : ℕ) (ε : ℝ) (mS mG : RowModel (Fin N)) (QS QG : ℝ → ℝ), N1 ≤ N → N ≤ B →
        0 < ε → ε < clockEps0 (α + ς) α T → E1 ≤ ε * (N : ℝ) ^ (α + ς - 1) →
        IsMatchedModel (svdArrays α ς N B) mS ε → IsVolterraSol mS QS →
        IsMatchedModel (sgdArrays α ς N B) mG ε → IsVolterraSol mG QG →
        (dimHit QG (sgdT0 α N B) T ε ≠ ⊤ → stepHit mG QG T ε = ENNReal.ofReal
          (mG.S * sgdT0 α N B / (2 * Real.sqrt ε) *
            ∫ u in (0:ℝ)..(dimHit QG (sgdT0 α N B) T ε).toReal,
              Real.sqrt (QG (sgdT0 α N B * u)))) →
        dimHit QG (sgdT0 α N B) T ε ≠ ⊤ ∧
        SandwichE cL cH ((sgdArrays α ς N B).S * sgdT0 α N B *
          ε ^ (-(1 / (2 * rq (α + ς) α)))) (stepHit mG QG T ε) := by
  have hp : 1 < α + ς := by linarith
  have hr0 := pw_rq_pos hp hα
  have hr : rq (α + ς) α < 1 := by
    unfold rq
    rw [div_lt_one (by linarith)]
    linarith
  obtain ⟨cL, cH, hcL, hcH, hgen⟩ := pw_gen hp hα hT (le_refl (1:ℝ)) hr
  have hC := pw_Cpq_pos hp hα
  set τ : ℝ := (4:ℝ) ^ (-α) with hτ_def
  have hτ : 0 < τ := Real.rpow_pos_of_pos (by norm_num) _
  refine ⟨4, Cpq (α + ς) α ^ 2 * (1 / τ) ^ (2 * rq (α + ς) α), cL, cH, le_refl _, hcL, hcH, ?_⟩
  intro N B ε mS mG QS QG hN hNB hε hε0 hE hmS hQS hmG hQG hstep
  have hN1 : 1 ≤ N := by omega
  have hN0 : (0:ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hmuB := pw_muBar_pos α hN1
  have hB0 : (0:ℝ) < B := by exact_mod_cast (by omega : 0 < B)
  have hT0 : 0 < sgdT0 α N B := by
    unfold sgdT0; exact Real.sqrt_pos.2 (by positivity)
  have hS : 0 < mG.S := by
    rw [pw_S_eq α ς N _ mG ε hmG]
    obtain ⟨-, -, h3, -⟩ := prop_app_phase_prefactors_i α ς N B hα hp hN1 hNB ε hε
    rw [h3]
    have : 0 < Real.sqrt (Real.pi * muBarOf α N / (B : ℝ)) := Real.sqrt_pos.2 (by positivity)
    positivity
  obtain ⟨hgc, hgn, hga, hgi, hgm, hYe⟩ := pw_sgd_facts α ς N B hα hp hN1 hNB ε hε mS mG hmS hmG QS QG hQS hQG
  obtain ⟨hYc, hYp⟩ := pw_Q_facts mG QG hQG _ hT0
  have hr12 : rq (α + ς) α ≤ 1 / 2 := by
    unfold rq
    rw [div_le_iff₀ (by linarith)]
    linarith
  have hconv : ∀ u ∈ Icc (0:ℝ) (1 * ((Cpq (α + ς) α / Real.sqrt ε) ^ (1 / rq (α + ς) α) - 1)),
      Muon.Foundations.oneSidedConv (fun w => Cpq (α + ς) α * (1 + w / 1) ^ (-rq (α + ς) α))
        (dimKernel mG (sgdT0 α N B) ε) u
          ≤ 2 * (Cpq (α + ς) α * (1 + u / 1) ^ (-rq (α + ς) α)) := by
    intro u hu
    have hm := lem_app_phase_mass (dimKernel mG (sgdT0 α N B) ε) hgc hgn hga
      (Cpq (α + ς) α) 1 (rq (α + ς) α) hC one_pos hr0 hr u hu.1
    refine hm.trans ?_
    have hI : ∫ v in (0:ℝ)..u, dimKernel mG (sgdT0 α N B) ε v ≤ 1 := by
      rw [intervalIntegral.integral_of_le hu.1]
      refine le_trans ?_ hgm
      apply setIntegral_mono_set hgi
      · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
        exact hgn x (Set.mem_Ici.2 (le_of_lt hx))
      · exact Filter.Eventually.of_forall (fun x hx => hx.1)
    have h1r : 0 < 1 - rq (α + ς) α := by linarith
    have hhp : 0 ≤ Cpq (α + ς) α * (1 + u / 1) ^ (-rq (α + ς) α) := by
      have : 0 ≤ u / 1 := by have := hu.1; simpa using this
      have := Real.rpow_nonneg (show (0:ℝ) ≤ 1 + u / 1 by linarith) (-rq (α + ς) α)
      positivity
    have : (∫ v in (0:ℝ)..u, dimKernel mG (sgdT0 α N B) ε v) / (1 - rq (α + ς) α) ≤ 2 := by
      rw [div_le_iff₀ h1r]; linarith
    exact mul_le_mul_of_nonneg_right this hhp
  have hHN : 1 * ((Cpq (α + ς) α / Real.sqrt ε) ^ (1 / rq (α + ς) α) - 1) ≤ ((N:ℝ) / 4) ^ α := by
    have h2 : (2 * α * rq (α + ς) α) = α + ς - 1 := by unfold rq; field_simp
    have := pw_horizon (C := Cpq (α + ς) α) (D := 1) (τ := τ) (r := rq (α + ς) α) (q := α)
      (ε := ε) (E := Cpq (α + ς) α ^ 2 * (1 / τ) ^ (2 * rq (α + ς) α)) (N := (N:ℝ)) hC one_pos hτ hr0 hα hε hN0
      le_rfl (by rw [h2]; exact hE)
    have h4 : τ * (N:ℝ) ^ α = ((N:ℝ) / 4) ^ α := by
      rw [Real.div_rpow hN0.le (by norm_num), hτ_def, Real.rpow_neg (by norm_num)]
      ring
    linarith
  have key := hgen N ε mG.S (sgdT0 α N B) mG QG (dimKernel mG (sgdT0 α N B) ε) hN hε hε0 hS hT0
    hgc hgn hgi hgm hYc hYp hYe hconv hHN hstep
  rw [pw_S_eq α ς N _ mG ε hmG] at key
  exact key

lemma pw_conv_congr (f g g' : ℝ → ℝ) (hg : ∀ s ∈ Ici (0:ℝ), g s = g' s) {u : ℝ} (hu : 0 ≤ u) :
    Muon.Foundations.oneSidedConv f g u = Muon.Foundations.oneSidedConv f g' u := by
  unfold Muon.Foundations.oneSidedConv
  apply intervalIntegral.integral_congr
  intro s hs
  rw [Set.uIcc_of_le hu] at hs
  simp only
  rw [hg s (Set.mem_Ici.2 hs.1)]

lemma pw_svd_gen (α ς T D τ : ℝ) (N0 : ℕ) (hα : 0 < α) (hς1 : 1 - α < ς) (hς2 : ς < 1)
    (hT : 4 ≤ T) (hD : 1 ≤ D) (hτ : 0 < τ) (hτ4 : τ ≤ (4:ℝ) ^ (-(α / 2))) (hN0 : 4 ≤ N0)
    (hprov : ∀ N : ℕ, N0 ≤ N → ∀ Hh : ℝ, Hh ≤ τ * (N:ℝ) ^ (α / 2) →
      ∀ g : ℝ → ℝ, ContinuousOn g (Ici 0) → (∀ u ∈ Ici (0:ℝ), 0 ≤ g u) →
      IntegrableOn g (Ioi 0) → ∫ u in Ioi (0:ℝ), g u ≤ 1 →
      (∀ u ∈ Ici (0:ℝ), g u = svdKernel α N u) →
      ∀ u ∈ Icc (0:ℝ) Hh,
        Muon.Foundations.oneSidedConv
          (fun w => Cpq (α + ς) (α / 2) * (1 + w / D) ^ (-rq (α + ς) (α / 2)))
          g u
          ≤ 2 * (Cpq (α + ς) (α / 2) * (1 + u / D) ^ (-rq (α + ς) (α / 2)))) :
    ∃ (N1 : ℕ) (E1 cL cH : ℝ), 4 ≤ N1 ∧ 0 < cL ∧ 0 < cH ∧
      ∀ (N B : ℕ) (ε : ℝ) (mS mG : RowModel (Fin N)) (QS QG : ℝ → ℝ), N1 ≤ N → N ≤ B →
        0 < ε → ε < clockEps0 (α + ς) (α / 2) T → E1 ≤ ε * (N : ℝ) ^ (α + ς - 1) →
        IsMatchedModel (svdArrays α ς N B) mS ε → IsVolterraSol mS QS →
        IsMatchedModel (sgdArrays α ς N B) mG ε → IsVolterraSol mG QG →
        (dimHit QS (svdT0 N B) T ε ≠ ⊤ → stepHit mS QS T ε = ENNReal.ofReal
          (mS.S * svdT0 N B / (2 * Real.sqrt ε) *
            ∫ u in (0:ℝ)..(dimHit QS (svdT0 N B) T ε).toReal,
              Real.sqrt (QS (svdT0 N B * u)))) →
        dimHit QS (svdT0 N B) T ε ≠ ⊤ ∧
        SandwichE cL cH ((svdArrays α ς N B).S * svdT0 N B *
          ε ^ (-(1 / (2 * rq (α + ς) (α / 2))))) (stepHit mS QS T ε) := by
  have hp : 1 < α + ς := by linarith
  have hq : 0 < α / 2 := by linarith
  have hr0 := pw_rq_pos hp hq
  have hr : rq (α + ς) (α / 2) < 1 := by
    unfold rq
    rw [div_lt_one (by linarith)]
    linarith
  obtain ⟨cL, cH, hcL, hcH, hgen⟩ := pw_gen hp hq hT hD hr
  have hC := pw_Cpq_pos hp hq
  refine ⟨N0, Cpq (α + ς) (α / 2) ^ 2 * (D / τ) ^ (2 * rq (α + ς) (α / 2)), cL, cH, hN0, hcL, hcH, ?_⟩
  intro N B ε mS mG QS QG hN hNB hε hε0 hE hmS hQS hmG hQG hstep
  have hN4 : 4 ≤ N := le_trans hN0 hN
  have hN1 : 1 ≤ N := by omega
  have hN0' : (0:ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hB0 : (0:ℝ) < B := by exact_mod_cast (by omega : 0 < B)
  have hT0 : 0 < svdT0 N B := by
    unfold svdT0 gammaRat; exact Real.sqrt_pos.2 (by positivity)
  have hS : 0 < mS.S := by
    rw [pw_S_eq α ς N _ mS ε hmS]
    obtain ⟨h1, -⟩ := prop_app_phase_prefactors_i α ς N B hα hp hN1 hNB ε hε
    rw [h1]
    have h2 : 0 < Real.sqrt (gammaRat N B) := Real.sqrt_pos.2 (by unfold gammaRat; positivity)
    have h3 := pw_Hsum_ge_one (α / 2) N hN1
    positivity
  obtain ⟨hgc, hgn, hgi, hgm, hgk, hYe⟩ := pw_svd_facts α ς N B hα hp hN1 hNB ε hε mS mG hmS hmG QS QG hQS hQG
  obtain ⟨hYc, hYp⟩ := pw_Q_facts mS QS hQS _ hT0
  have hHN0 : D * ((Cpq (α + ς) (α / 2) / Real.sqrt ε) ^ (1 / rq (α + ς) (α / 2)) - 1)
      ≤ τ * (N:ℝ) ^ (α / 2) := by
    have h2 : (2 * (α / 2) * rq (α + ς) (α / 2)) = α + ς - 1 := by unfold rq; field_simp
    exact pw_horizon (C := Cpq (α + ς) (α / 2)) (D := D) (τ := τ) (r := rq (α + ς) (α / 2))
      (q := α / 2) (ε := ε) (E := Cpq (α + ς) (α / 2) ^ 2 * (D / τ) ^ (2 * rq (α + ς) (α / 2)))
      (N := (N:ℝ)) hC (by linarith) hτ hr0 hq hε hN0' le_rfl (by rw [h2]; exact hE)
  have hHN : D * ((Cpq (α + ς) (α / 2) / Real.sqrt ε) ^ (1 / rq (α + ς) (α / 2)) - 1)
      ≤ ((N:ℝ) / 4) ^ (α / 2) := by
    refine hHN0.trans ?_
    rw [Real.div_rpow hN0'.le (by norm_num)]
    have : τ ≤ ((4:ℝ) ^ (α / 2))⁻¹ := by
      rw [← Real.rpow_neg (by norm_num)]; exact hτ4
    have hNp : 0 < (N:ℝ) ^ (α / 2) := Real.rpow_pos_of_pos hN0' _
    calc τ * (N:ℝ) ^ (α / 2) ≤ ((4:ℝ) ^ (α / 2))⁻¹ * (N:ℝ) ^ (α / 2) :=
          mul_le_mul_of_nonneg_right this hNp.le
      _ = _ := by ring
  have hconv : ∀ u ∈ Icc (0:ℝ) (D * ((Cpq (α + ς) (α / 2) / Real.sqrt ε) ^ (1 / rq (α + ς) (α / 2)) - 1)),
      Muon.Foundations.oneSidedConv
        (fun w => Cpq (α + ς) (α / 2) * (1 + w / D) ^ (-rq (α + ς) (α / 2)))
        (dimKernel mS (svdT0 N B) ε) u
          ≤ 2 * (Cpq (α + ς) (α / 2) * (1 + u / D) ^ (-rq (α + ς) (α / 2))) := by
    intro u hu
    exact hprov N hN _ hHN0 _ hgc hgn hgi hgm hgk u hu
  have key := hgen N ε mS.S (svdT0 N B) mS QS (dimKernel mS (svdT0 N B) ε) hN4 hε hε0 hS hT0
    hgc hgn hgi hgm hYc hYp hYe hconv hHN hstep
  rw [pw_S_eq α ς N _ mS ε hmS] at key
  exact key

lemma pw_svd_lt2 (α ς T : ℝ) (hα : 0 < α) (hα2 : α < 2) (hς1 : 1 - α < ς) (hς2 : ς < 1)
    (hT : 4 ≤ T) :
    ∃ (N1 : ℕ) (E1 cL cH : ℝ), 4 ≤ N1 ∧ 0 < cL ∧ 0 < cH ∧
      ∀ (N B : ℕ) (ε : ℝ) (mS mG : RowModel (Fin N)) (QS QG : ℝ → ℝ), N1 ≤ N → N ≤ B →
        0 < ε → ε < clockEps0 (α + ς) (α / 2) T → E1 ≤ ε * (N : ℝ) ^ (α + ς - 1) →
        IsMatchedModel (svdArrays α ς N B) mS ε → IsVolterraSol mS QS →
        IsMatchedModel (sgdArrays α ς N B) mG ε → IsVolterraSol mG QG →
        (dimHit QS (svdT0 N B) T ε ≠ ⊤ → stepHit mS QS T ε = ENNReal.ofReal
          (mS.S * svdT0 N B / (2 * Real.sqrt ε) *
            ∫ u in (0:ℝ)..(dimHit QS (svdT0 N B) T ε).toReal,
              Real.sqrt (QS (svdT0 N B * u)))) →
        dimHit QS (svdT0 N B) T ε ≠ ⊤ ∧
        SandwichE cL cH ((svdArrays α ς N B).S * svdT0 N B *
          ε ^ (-(1 / (2 * rq (α + ς) (α / 2))))) (stepHit mS QS T ε) := by
  have hp : 1 < α + ς := by linarith
  have hq : 0 < α / 2 := by linarith
  have hr0 := pw_rq_pos hp hq
  have hr : rq (α + ς) (α / 2) < 1 := by
    unfold rq
    rw [div_lt_one (by linarith)]
    linarith
  set r := rq (α + ς) (α / 2) with hr_def
  have hC := pw_Cpq_pos hp hq
  have hd1 : 0 < svdSmallDelta1 α r := by
    unfold svdSmallDelta1
    apply Real.rpow_pos_of_pos
    linarith
  have hc1 : 0 < svdSmallC1 α r := by
    unfold svdSmallC1
    have : 0 < svdSmallDelta1 α r ^ (α / 2) := Real.rpow_pos_of_pos hd1 _
    have : 0 < 1 - r := by linarith
    positivity
  have h4 : (0:ℝ) < (4:ℝ) ^ (-(α / 2)) := Real.rpow_pos_of_pos (by norm_num) _
  refine pw_svd_gen α ς T 1 (min ((4:ℝ) ^ (-(α / 2))) (svdSmallC1 α r)) (max 4 (svdSmallN1 α r))
    hα hς1 hς2 hT le_rfl (lt_min h4 hc1) (min_le_left _ _) (le_max_left _ _) ?_
  intro N hN Hh hHh g hgc hgn hgi hgm hgk u hu
  have hN1 : svdSmallN1 α r ≤ N := le_trans (le_max_right _ _) hN
  have hNp : 0 ≤ (N:ℝ) ^ (α / 2) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hu' : u ≤ svdSmallC1 α r * (N:ℝ) ^ (α / 2) :=
    hu.2.trans (hHh.trans (mul_le_mul_of_nonneg_right (min_le_right _ _) hNp))
  have hsm := (lem_app_phase_svd_small α r hα hα2 hr0 hr N hN1).2 (Cpq (α + ς) (α / 2)) hC u
    ⟨hu.1, hu'⟩
  rw [pw_conv_congr _ g (svdKernel α N) hgk hu.1]
  simp only [div_one]
  have hh : 0 ≤ Cpq (α + ς) (α / 2) * (1 + u) ^ (-r) := by
    have := Real.rpow_nonneg (show (0:ℝ) ≤ 1 + u by linarith [hu.1]) (-r)
    positivity
  linarith

lemma pw_log_le_H (N : ℕ) (hN : 1 ≤ N) : Real.log ((N:ℝ) + 1) ≤ Hsum 1 N := by
  have h := (lem_app_phase_harmonic_i (a := 1) one_pos N hN).1
  have hN0 : (0:ℝ) < N := by exact_mod_cast hN
  have e : ∫ x in (1:ℝ)..((N:ℝ) + 1), x ^ (-(1:ℝ)) = Real.log ((N:ℝ) + 1) := by
    have : (fun x : ℝ => x ^ (-(1:ℝ))) = fun x => x⁻¹ := by
      funext x; exact Real.rpow_neg_one x
    rw [this, integral_inv_of_pos one_pos (by linarith)]
    simp
  rw [e] at h
  exact h

lemma pw_svd_eq2 (α ς T : ℝ) (hα2 : α = 2) (hς1 : 1 - α < ς) (hς2 : ς < 1)
    (hT : 4 ≤ T) :
    ∃ (N1 : ℕ) (E1 cL cH : ℝ), 4 ≤ N1 ∧ 0 < cL ∧ 0 < cH ∧
      ∀ (N B : ℕ) (ε : ℝ) (mS mG : RowModel (Fin N)) (QS QG : ℝ → ℝ), N1 ≤ N → N ≤ B →
        0 < ε → ε < clockEps0 (α + ς) (α / 2) T → E1 ≤ ε * (N : ℝ) ^ (α + ς - 1) →
        IsMatchedModel (svdArrays α ς N B) mS ε → IsVolterraSol mS QS →
        IsMatchedModel (sgdArrays α ς N B) mG ε → IsVolterraSol mG QG →
        (dimHit QS (svdT0 N B) T ε ≠ ⊤ → stepHit mS QS T ε = ENNReal.ofReal
          (mS.S * svdT0 N B / (2 * Real.sqrt ε) *
            ∫ u in (0:ℝ)..(dimHit QS (svdT0 N B) T ε).toReal,
              Real.sqrt (QS (svdT0 N B * u)))) →
        dimHit QS (svdT0 N B) T ε ≠ ⊤ ∧
        SandwichE cL cH ((svdArrays α ς N B).S * svdT0 N B *
          ε ^ (-(1 / (2 * rq (α + ς) (α / 2))))) (stepHit mS QS T ε) := by
  subst hα2
  have hp : 1 < 2 + ς := by linarith
  have hq : 0 < (2:ℝ) / 2 := by norm_num
  have hr0 := pw_rq_pos hp hq
  have hr : rq (2 + ς) (2 / 2) < 1 := by
    unfold rq
    rw [div_lt_one (by norm_num)]
    linarith
  set r := rq (2 + ς) (2 / 2) with hr_def
  have hC := pw_Cpq_pos hp hq
  have hτ4 : (1/4 : ℝ) ≤ (4:ℝ) ^ (-((2:ℝ) / 2)) := by
    norm_num [Real.rpow_neg]
  refine pw_svd_gen 2 ς T 1 (1/4) (max 4 ⌈Real.exp (logAr r)⌉₊)
    (by norm_num) hς1 hς2 hT le_rfl (by norm_num) hτ4 (le_max_left _ _) ?_
  intro N hN Hh hHh g hgc hgn hgi hgm hgk u hu
  have hN4 : 4 ≤ N := le_trans (le_max_left _ _) hN
  have hN1 : 1 ≤ N := by omega
  have hN0 : (0:ℝ) < N := by exact_mod_cast hN1
  have hexp : Real.exp (logAr r) ≤ N :=
    (Nat.le_ceil _).trans (by exact_mod_cast le_trans (le_max_right _ _) hN)
  have hA : logAr r ≤ Real.log N := by
    rw [← Real.log_exp (logAr r)]
    exact Real.log_le_log (Real.exp_pos _) hexp
  have hHh' : Hh ≤ (N:ℝ) / 4 := by
    have : (N:ℝ) ^ ((2:ℝ) / 2) = N := by norm_num
    rw [this] at hHh; linarith
  have hu0 : 0 ≤ u := hu.1
  have hu2 : u ≤ Hh := hu.2
  have h5 : u ≤ (N:ℝ) / 4 := le_trans hu2 hHh'
  have h6 : 1 + u ≤ (N:ℝ) + 1 := by
    have h7 : 0 ≤ (N:ℝ) := Nat.cast_nonneg N
    linarith only [h5, h7]
  have hlog1 := Real.log_le_log (show (0:ℝ) < 1 + u by linarith)
    h6
  have hlogN : Real.log (N:ℝ) ≤ Real.log ((N:ℝ) + 1) :=
    Real.log_le_log hN0 (by linarith)
  have hH := pw_log_le_H N hN1
  have hlog := (lem_app_phase_log_ii N hN1 r hr0 hr (Cpq (2 + ς) (2 / 2)) hC) u hu0
  have hHpos : 0 < Hsum 1 N := by have := pw_Hsum_ge_one 1 N hN1; linarith
  have hfrac : (Real.log (1 + u) + logAr r) / Hsum 1 N ≤ 2 := by
    rw [div_le_iff₀ hHpos]; linarith
  have hh : 0 < Cpq (2 + ς) (2 / 2) * (1 + u) ^ (-r) := by
    have := Real.rpow_pos_of_pos (show (0:ℝ) < 1 + u by linarith) (-r)
    positivity
  rw [pw_conv_congr _ g (svdKernel 2 N) hgk hu0]
  simp only [div_one, ← hr_def]
  rw [div_le_iff₀ hh] at hlog
  calc _ ≤ _ := hlog
    _ ≤ 2 * (Cpq (2 + ς) (2 / 2) * (1 + u) ^ (-r)) := by
      have := mul_le_mul_of_nonneg_right hfrac hh.le
      linarith

lemma pw_svd_gt2 (α ς T : ℝ) (hα : 2 < α) (hς1 : 1 - α < ς) (hς2 : ς < 1)
    (hT : 4 ≤ T) :
    ∃ (N1 : ℕ) (E1 cL cH : ℝ), 4 ≤ N1 ∧ 0 < cL ∧ 0 < cH ∧
      ∀ (N B : ℕ) (ε : ℝ) (mS mG : RowModel (Fin N)) (QS QG : ℝ → ℝ), N1 ≤ N → N ≤ B →
        0 < ε → ε < clockEps0 (α + ς) (α / 2) T → E1 ≤ ε * (N : ℝ) ^ (α + ς - 1) →
        IsMatchedModel (svdArrays α ς N B) mS ε → IsVolterraSol mS QS →
        IsMatchedModel (sgdArrays α ς N B) mG ε → IsVolterraSol mG QG →
        (dimHit QS (svdT0 N B) T ε ≠ ⊤ → stepHit mS QS T ε = ENNReal.ofReal
          (mS.S * svdT0 N B / (2 * Real.sqrt ε) *
            ∫ u in (0:ℝ)..(dimHit QS (svdT0 N B) T ε).toReal,
              Real.sqrt (QS (svdT0 N B * u)))) →
        dimHit QS (svdT0 N B) T ε ≠ ⊤ ∧
        SandwichE cL cH ((svdArrays α ς N B).S * svdT0 N B *
          ε ^ (-(1 / (2 * rq (α + ς) (α / 2))))) (stepHit mS QS T ε) := by
  have hα0 : 0 < α := by linarith
  have hp : 1 < α + ς := by linarith
  have hq : 0 < α / 2 := by linarith
  have hr0 := pw_rq_pos hp hq
  have hr : rq (α + ς) (α / 2) < 1 := by
    unfold rq
    rw [div_lt_one (by linarith)]
    linarith
  have hυ : 1 < 2 - 2 / α := by
    have : 2 / α < 1 := by rw [div_lt_one hα0]; exact hα
    linarith
  have hK : 0 < 2 * Epq α (α / 2) := by have := pw_Epq_pos (p := α) (q := α / 2) (by linarith) hq; positivity
  have hD1 : 1 ≤ dilScale (2 * Epq α (α / 2)) (rq (α + ς) (α / 2)) (2 - 2 / α) := le_max_left _ _
  have h4 : (0:ℝ) < (4:ℝ) ^ (-(α / 2)) := Real.rpow_pos_of_pos (by norm_num) _
  refine pw_svd_gen α ς T (dilScale (2 * Epq α (α / 2)) (rq (α + ς) (α / 2)) (2 - 2 / α))
    ((4:ℝ) ^ (-(α / 2))) 4 hα0 hς1 hς2 hT hD1 h4 le_rfl le_rfl ?_
  intro N hN Hh hHh g hgc hgn hgi hgm hgk u hu
  have hN1 : 1 ≤ N := by omega
  have hbound : ∀ v ∈ Icc (0:ℝ) (max Hh 1), g v ≤ 2 * Epq α (α / 2) * (1 + v) ^ (-(2 - 2 / α)) := by
    intro v hv
    have hv0 : 0 ≤ v := hv.1
    rw [hgk v (Set.mem_Ici.2 hv0)]
    unfold svdKernel
    have h1 := lem_app_phase_sums_i (a := α) (q := α / 2) (by linarith) hq (N : ℕ∞) hv0
    have hd : dAQ α (α / 2) = 2 - 2 / α := by unfold dAQ; field_simp
    rw [hd] at h1
    have hH := pw_Hsum_ge_one (α / 2) N hN1
    have hL := pw_Lsum_nonneg N α (α / 2) v
    have hpow : 0 ≤ Epq α (α / 2) * (1 + v) ^ (-(2 - 2 / α)) := by
      have := pw_Epq_pos (p := α) (q := α / 2) (by linarith) hq
      have := Real.rpow_nonneg (show (0:ℝ) ≤ 1 + v by linarith) (-(2 - 2 / α))
      positivity
    have : 2 / Hsum (α / 2) N ≤ 2 := by
      rw [div_le_iff₀ (by linarith)]; nlinarith
    calc 2 / Hsum (α / 2) N * Lsum (N : ℕ∞) α (α / 2) v ≤ 2 * (Epq α (α / 2) * (1 + v) ^ (-(2 - 2 / α))) :=
          mul_le_mul this h1 hL (by norm_num)
      _ = _ := by ring
  have hdil := (lem_app_phase_dilation g hgc hgn hgi hgm (2 * Epq α (α / 2)) (2 - 2 / α) (max Hh 1)
    (rq (α + ς) (α / 2)) (Cpq (α + ς) (α / 2)) hK hυ (by positivity) hr0
    (by have : 1 < 2 - 2 / α := hυ; linarith) (pw_Cpq_pos hp hq) hbound)
  have hu' : u ∈ Icc (0:ℝ) (max Hh 1) := ⟨hu.1, hu.2.trans (le_max_left _ _)⟩
  have hh : 0 < Cpq (α + ς) (α / 2) * (1 + u / dilScale (2 * Epq α (α / 2)) (rq (α + ς) (α / 2)) (2 - 2 / α)) ^ (-rq (α + ς) (α / 2)) := by
    have hD : 0 < dilScale (2 * Epq α (α / 2)) (rq (α + ς) (α / 2)) (2 - 2 / α) := by linarith
    have := Real.rpow_pos_of_pos (show (0:ℝ) < 1 + u / dilScale (2 * Epq α (α / 2)) (rq (α + ς) (α / 2)) (2 - 2 / α) by
      have : 0 ≤ u / dilScale (2 * Epq α (α / 2)) (rq (α + ς) (α / 2)) (2 - 2 / α) := div_nonneg hu.1 hD.le
      linarith) (-rq (α + ς) (α / 2))
    have := pw_Cpq_pos hp hq
    positivity
  have h1 := (div_le_iff₀ hh).1 ((hdil.1 u hu').trans hdil.2)
  exact h1

lemma pw_svd_main (α ς T : ℝ) (hα : 0 < α) (hς1 : 1 - α < ς) (hς2 : ς < 1)
    (hT : 4 ≤ T) :
    ∃ (N1 : ℕ) (E1 cL cH : ℝ), 4 ≤ N1 ∧ 0 < cL ∧ 0 < cH ∧
      ∀ (N B : ℕ) (ε : ℝ) (mS mG : RowModel (Fin N)) (QS QG : ℝ → ℝ), N1 ≤ N → N ≤ B →
        0 < ε → ε < clockEps0 (α + ς) (α / 2) T → E1 ≤ ε * (N : ℝ) ^ (α + ς - 1) →
        IsMatchedModel (svdArrays α ς N B) mS ε → IsVolterraSol mS QS →
        IsMatchedModel (sgdArrays α ς N B) mG ε → IsVolterraSol mG QG →
        (dimHit QS (svdT0 N B) T ε ≠ ⊤ → stepHit mS QS T ε = ENNReal.ofReal
          (mS.S * svdT0 N B / (2 * Real.sqrt ε) *
            ∫ u in (0:ℝ)..(dimHit QS (svdT0 N B) T ε).toReal,
              Real.sqrt (QS (svdT0 N B * u)))) →
        dimHit QS (svdT0 N B) T ε ≠ ⊤ ∧
        SandwichE cL cH ((svdArrays α ς N B).S * svdT0 N B *
          ε ^ (-(1 / (2 * rq (α + ς) (α / 2))))) (stepHit mS QS T ε) := by
  rcases lt_trichotomy α 2 with h | h | h
  · exact pw_svd_lt2 α ς T hα h hς1 hς2 hT
  · exact pw_svd_eq2 α ς T h hς1 hς2 hT
  · exact pw_svd_gt2 α ς T h hς1 hς2 hT

lemma pw_sandwich_mono {cL cH cL' cH' X : ℝ} {t : ℝ≥0∞} (h : SandwichE cL cH X t)
    (h1 : cL' ≤ cL) (h2 : cH ≤ cH') : SandwichE cL' cH' X t := by
  obtain ⟨a, b⟩ := h
  exact ⟨le_trans (mul_le_mul' (ENNReal.ofReal_le_ofReal h1) le_rfl) a,
    le_trans b (mul_le_mul' (ENNReal.ofReal_le_ofReal h2) le_rfl)⟩

lemma pw_clockEps0_pos {p q T : ℝ} (hp : 1 < p) (hq : 0 < q) (hT : 4 ≤ T) :
    0 < clockEps0 p q T := by
  have hT0 : 0 < T := by linarith
  have hC := pw_Cpq_pos hp hq
  have hA : 0 < Aconst p := by unfold Aconst; positivity
  unfold clockEps0
  split_ifs
  · simp only [lt_min_iff]
    refine ⟨⟨⟨⟨by norm_num, by positivity⟩, by positivity⟩, by positivity⟩, by positivity⟩
  · simp only [lt_min_iff]
    refine ⟨⟨⟨by norm_num, by positivity⟩, by positivity⟩, by positivity⟩

lemma pw_phaseEps0_pos {α ς T : ℝ} (hα : 0 < α) (hp : 1 < α + ς) (hT : 4 ≤ T) :
    0 < phaseEps0 α ς T := by
  unfold phaseEps0
  exact lt_min (pw_clockEps0_pos hp (by linarith) hT) (pw_clockEps0_pos hp hα hT)

lemma pw_thm_A (α ς T : ℝ) (hα : 0 < α) (hς₁ : 1 - α < ς) (hς₂ : ς < 1)
    (hT : 4 ≤ T) :
    ∃ (Nst : ℕ) (Est cLo cHi : ℝ), PhaseAWindowHolds α ς T Nst Est cLo cHi := by
  have hp : 1 < α + ς := by linarith
  have hp1 : 0 < α + ς - 1 := by linarith
  obtain ⟨N1, E1, cL1, cH1, hN1, hcL1, hcH1, h1⟩ := pw_svd_main α ς T hα hς₁ hς₂ hT
  obtain ⟨N2, E2, cL2, cH2, hN2, hcL2, hcH2, h2⟩ := pw_sgd_main α ς T hα hς₁ hς₂ hT
  set Nst : ℕ := max N1 N2 with hNst
  set Est : ℝ := max E1 E2 with hEst
  set cLo : ℝ := min cL1 cL2 with hcLo
  set cHi : ℝ := max (max cH1 cH2) cLo with hcHi
  have hcLo0 : 0 < cLo := lt_min hcL1 hcL2
  have hNst4 : 4 ≤ Nst := le_trans hN1 (le_max_left _ _)
  have hEps := pw_phaseEps0_pos hα hp hT
  refine ⟨Nst, Est, cLo, cHi, hcLo0, le_max_right _ _, ?_, ?_, ?_⟩
  · intro N B ε mS mG QS QG hW hmS hQS hmG hQG
    obtain ⟨hNN, hNB, hε, hε0, hE⟩ := hW
    have hN1' : 1 ≤ N := by omega
    have hε0' : ε < clockEps0 (α + ς) (α / 2) T ∧ ε < clockEps0 (α + ς) α T := by
      unfold phaseEps0 at hε0
      exact lt_min_iff.1 hε0
    have hpref := prop_app_phase_prefactors_iii α ς N B hα hp hN1' hNB ε T hε (by linarith) mS mG hmS hmG QS QG hQS hQG
    have hEl1 : E1 ≤ ε * (N:ℝ) ^ (α + ς - 1) := le_trans (le_max_left _ _) hE
    have hEl2 : E2 ≤ ε * (N:ℝ) ^ (α + ς - 1) := le_trans (le_max_right _ _) hE
    obtain ⟨hA1, hB1⟩ := h1 N B ε mS mG QS QG (le_trans (le_max_left _ _) hNN) hNB hε hε0'.1 hEl1
      hmS hQS hmG hQG hpref.1
    obtain ⟨hA2, hB2⟩ := h2 N B ε mS mG QS QG (le_trans (le_max_right _ _) hNN) hNB hε hε0'.2 hEl2
      hmS hQS hmG hQG hpref.2
    have e1 : 1 / (2 * rq (α + ς) (α / 2)) = α / (2 * (α + ς - 1)) := by
      unfold rq; field_simp
    have e2 : 1 / (2 * rq (α + ς) α) = α / (α + ς - 1) := by
      unfold rq; field_simp
    have hB1' := pw_sandwich_mono (cL' := cLo) (cH' := cHi) hB1 (min_le_left _ _) ((le_max_left _ _).trans (le_max_left _ _))
    have hB2' := pw_sandwich_mono (cL' := cLo) (cH' := cHi) hB2 (min_le_right _ _) ((le_max_right _ _).trans (le_max_left _ _))
    refine ⟨⟨hA1, hA2⟩, hB1', hB2', ?_, ?_⟩
    · rw [← e1]; exact hB1'
    · rw [← e2]; exact hB2'
  · intro Nseq Bseq εseq hN hε hε0 _ hNB hE
    have h1 : ∀ᶠ n in atTop, (Nst:ℝ) ≤ (Nseq n : ℝ) := hN.eventually_ge_atTop _
    have h2 : ∀ᶠ n in atTop, εseq n < phaseEps0 α ς T :=
      (tendsto_order.1 hε).2 _ hEps
    have h3 : ∀ᶠ n in atTop, Est ≤ εseq n * (Nseq n : ℝ) ^ (α + ς - 1) := hE.eventually_ge_atTop _
    filter_upwards [h1, h2, h3] with n a b c
    exact ⟨by exact_mod_cast a, hNB n, hε0 n, b, c⟩
  · intro ω hω hω' Bseq hB
    have hNt : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
    have h1 : ∀ᶠ N : ℕ in atTop, Nst ≤ N := eventually_ge_atTop _
    have h1' : ∀ᶠ N : ℕ in atTop, 1 ≤ N := eventually_ge_atTop _
    have h2 : ∀ᶠ N : ℕ in atTop, (N:ℝ) ^ (-ω) < phaseEps0 α ς T :=
      ((tendsto_rpow_neg_atTop hω).comp hNt |> fun h => (tendsto_order.1 h).2 _ hEps)
    have h3 : ∀ᶠ N : ℕ in atTop, Est ≤ (N:ℝ) ^ (α + ς - 1 - ω) :=
      ((tendsto_rpow_atTop (by linarith : 0 < α + ς - 1 - ω)).comp hNt).eventually_ge_atTop _
    filter_upwards [h1, h1', h2, h3] with N a a' b c
    have hN0 : (0:ℝ) < N := by exact_mod_cast a'
    refine ⟨a, hB N, Real.rpow_pos_of_pos hN0 _, b, ?_⟩
    rw [← Real.rpow_add hN0]
    convert c using 2
    ring

/-- Label `thm:app-phase-A`, declaration of record. Snapshot `cr-2026-10-23`.

Statement (verbatim, `sections/07-phase-comparison/section.tex`, l.1268–1282):

```latex
\begin{theorem}[The range $\texp<1$]\label{thm:app-phase-A}
Fix $\alpha>0$, $1-\alpha<\texp<1$ and $T\ge4$. There are $N_*$ and $E_*$ and
$0<c_-\le c_+$, all depending only on $\alpha$, $\texp$ and $T$, such that for all
$N\ge N_*$, $B\ge N$ and $0<\epsilon<\epsilon_0$ with $\epsilon N^{p-1}\ge E_*$,
and for both $j$, the first hit $\hat u_j$ is attained and
\[
c_-\le\frac{t^j_{T\epsilon}}{\mathcal S_jT_0^j\,\epsilon^{-1/(2r_j)}}\le c_+ .
\]
In particular $t^{\text{s-SVD}}_{T\epsilon}\asymp\mathcal S_{\text{s-SVD}}T_0^{\text{s-SVD}}\epsilon^{-\alpha/[2(p-1)]}$
and $t^{\text{s-SGD}}_{T\epsilon}\asymp\mathcal S_{\text{s-SGD}}T_0^{\text{s-SGD}}\epsilon^{-\alpha/(p-1)}$.
Every sequence with $N\to\infty$, $\epsilon\downarrow0$ and
$\epsilon N^{p-1}\to\infty$ lies in this window for all large indices,
uniformly over $B\ge N$; for example $\epsilon=N^{-\omega}$ with
$0<\omega<p-1$.
\end{theorem}
```
-/
theorem thm_app_phase_A (α ς T : ℝ) (hα : 0 < α) (hς₁ : 1 - α < ς) (hς₂ : ς < 1)
    (hT : 4 ≤ T) :
    ∃ (Nst : ℕ) (Est cLo cHi : ℝ), PhaseAWindowHolds α ς T Nst Est cLo cHi := by
  exact pw_thm_A α ς T hα hς₁ hς₂ hT

/-! ### Proof helpers for `thm:app-phase-B` (P-H.8.P2) -/

lemma pw_hitB {p q T D r0 : ℝ} (hp : 1 < p) (hq : 0 < q) (hT : 4 ≤ T) (hD : 1 ≤ D)
    (hr0 : 0 < r0) (hr02 : r0 < 2) (hr0r : r0 ≤ rq p q)
    (N : ℕ) (ε : ℝ) (g Y : ℝ → ℝ) (hN : 4 ≤ N) (hε : 0 < ε)
    (hε0 : ε < clockEps0 p q T)
    (hgc : ContinuousOn g (Ici 0)) (hgn : ∀ u ∈ Ici (0:ℝ), 0 ≤ g u) (hgi : IntegrableOn g (Ioi 0))
    (hgm : ∫ u in Ioi (0:ℝ), g u ≤ 1)
    (hYc : ContinuousOn Y (Ici 0)) (hYp : ∀ u ∈ Ici (0:ℝ), 0 < Y u)
    (hYe : ∀ u ∈ Ici (0:ℝ), Y u = fNq (N:ℕ∞) p q u +
          Real.sqrt ε * Muon.Foundations.oneSidedConv (fun v => Real.sqrt (Y v)) g u)
    (hconv : ∀ u ∈ Icc (0:ℝ) (D * ((Cpq p q / Real.sqrt ε) ^ (1 / r0) - 1)),
          Muon.Foundations.oneSidedConv (fun w => Cpq p q * (1 + w / D) ^ (-r0)) g u
            ≤ 2 * (Cpq p q * (1 + u / D) ^ (-r0))) :
    ∃ û : ℝ, firstHit Y (T * ε) = ENNReal.ofReal û ∧ 0 < û ∧
      û ≤ D * ((Cpq p q / Real.sqrt ε) ^ (1 / r0) - 1) ∧ Y û = T * ε ∧
      (∀ u ∈ Ici (0:ℝ), fNq (N:ℕ∞) p q u ≤ Y u) ∧
      0 ≤ ∫ u in (0:ℝ)..û, (Real.sqrt (Y u) - Real.sqrt (fNq (N:ℕ∞) p q u)) ∧
      ∫ u in (0:ℝ)..û, (Real.sqrt (Y u) - Real.sqrt (fNq (N:ℕ∞) p q u)) ≤
        D * Cpq p q ^ (1 / r0) * (Real.sqrt 2 / (1 - r0 / 2) + 1) * ε ^ ((r0 - 1) / (2 * r0)) := by
  have hC := pw_Cpq_pos hp hq
  have hT0 : 0 < T := by linarith
  have hD0 : 0 < D := by linarith
  set r := rq p q with hr_def
  set C := Cpq p q with hC_def
  obtain ⟨hε8, hεC⟩ := pw_eps_facts ε hε0
  have hs : 0 < Real.sqrt ε := Real.sqrt_pos.2 hε
  have hN1 : 1 ≤ N := by omega
  obtain ⟨hh_ge, hh_H, h1H, hint⟩ := lem_app_phase_square_iii (C := C) (D := D) (r0 := r0)
    (ε := ε) (H := D * ((C / Real.sqrt ε) ^ (1 / r0) - 1)) (h := fun u => C * (1 + u / D) ^ (-r0))
    hC hD hr0 hr02 hε hεC (fun u => rfl) rfl
  set H := D * ((C / Real.sqrt ε) ^ (1 / r0) - 1) with hH_def
  have hX1 : 1 < (C / Real.sqrt ε) ^ (1 / r0) := by
    apply Real.one_lt_rpow _ (by positivity)
    rw [one_lt_div hs]
    calc Real.sqrt ε < Real.sqrt (C ^ 2) := Real.sqrt_lt_sqrt hε.le hεC
      _ = C := Real.sqrt_sq hC.le
  have hHpos : 0 < H := mul_pos hD0 (by linarith)
  have hf0 : T * ε < fNq (N : ℕ∞) p q 0 := by
    rw [pw_fNq_zero]
    have := pw_Hsum_ge_one p N hN1
    have h2 : T * ε < 1 / 8 := by
      have := mul_lt_mul_of_pos_left hε8 hT0
      rw [mul_one_div, mul_comm 8 T, ← div_div, div_self hT0.ne'] at this
      linarith
    linarith
  have hhc : ContinuousOn (fun u => C * (1 + u / D) ^ (-r0)) (Icc 0 H) := by
    apply ContinuousOn.mul continuousOn_const
    apply ContinuousOn.rpow_const (by fun_prop)
    intro x hx
    left
    have : 0 ≤ x / D := div_nonneg hx.1 hD0.le
    linarith
  have hfh : ∀ u ∈ Icc (0:ℝ) H, fNq (N:ℕ∞) p q u ≤ (C * (1 + u / D) ^ (-r0)) ^ 2 := by
    intro u hu
    have hle := pw_fNq_le hp hq N hu.1
    refine hle.trans ?_
    have hb : 0 < 1 + u / D := by have : 0 ≤ u / D := div_nonneg hu.1 hD0.le; linarith
    have hb1 : 1 ≤ 1 + u := by linarith [hu.1]
    have hmono0 : (1 + u) ^ (-(2 * r)) ≤ (1 + u) ^ (-(2 * r0)) :=
      Real.rpow_le_rpow_of_exponent_le hb1 (by linarith)
    have hmono : (1 + u) ^ (-(2 * r0)) ≤ (1 + u / D) ^ (-(2 * r0)) := by
      apply Real.rpow_le_rpow_of_nonpos hb _ (by linarith)
      have : u / D ≤ u := by
        rw [div_le_iff₀ hD0]; nlinarith [hu.1]
      linarith
    have hsq : ((1 + u / D) ^ (-r0)) ^ 2 = (1 + u / D) ^ (-(2 * r0)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hb.le]
      congr 1; push_cast; ring
    rw [mul_pow, hsq]
    exact mul_le_mul_of_nonneg_left (hmono0.trans hmono) (by positivity)
  have hf_nn : ∀ u ∈ Ici (0:ℝ), 0 ≤ fNq (N:ℕ∞) p q u := by
    intro u _; unfold fNq; have := pw_Lsum_nonneg N p q u; positivity
  have hsq_ii := lem_app_phase_square_ii (ε := ε) (T := T) (H := H) hε hT hHpos
    (f := fNq (N:ℕ∞) p q) (g := g) (h := fun u => C * (1 + u / D) ^ (-r0)) (Y := Y)
    hgc hgn hgi hgm (pw_fNq_cont N p q).continuousOn hf_nn hf0 hYc hYp hYe
    hhc hh_ge hh_H hfh (Or.inl hconv)
  obtain ⟨û, hhit, hû0, hûH, hYû, hE0, hE1, -⟩ := hsq_ii
  have hYf : ∀ u ∈ Ici (0:ℝ), fNq (N:ℕ∞) p q u ≤ Y u := by
    intro u hu
    rw [hYe u hu]
    have hconv0 : 0 ≤ Muon.Foundations.oneSidedConv (fun v => Real.sqrt (Y v)) g u := by
      unfold Muon.Foundations.oneSidedConv
      apply intervalIntegral.integral_nonneg hu
      intro s hs
      exact mul_nonneg (Real.sqrt_nonneg _) (hgn s (Set.mem_Ici.2 hs.1))
    have := mul_nonneg hs.le hconv0
    linarith
  exact ⟨û, hhit, hû0, hûH, hYû, hYf, hE0, hE1.trans hint⟩

lemma pw_prepB {p q T D r0 : ℝ} (hp : 1 < p) (hq : 0 < q) (hT : 4 ≤ T) (hD : 1 ≤ D)
    (hr0 : 0 < r0) (hr02 : r0 < 2) (hr0r : r0 ≤ rq p q)
    (N : ℕ) (ε S T0 : ℝ) (m : RowModel (Fin N)) (Q : ℝ → ℝ) (g : ℝ → ℝ)
    (hN : 4 ≤ N) (hε : 0 < ε)
    (hε0 : ε < clockEps0 p q T)
    (hgc : ContinuousOn g (Ici 0)) (hgn : ∀ u ∈ Ici (0:ℝ), 0 ≤ g u) (hgi : IntegrableOn g (Ioi 0))
    (hgm : ∫ u in Ioi (0:ℝ), g u ≤ 1)
    (hYc : ContinuousOn (fun u => Q (T0 * u)) (Ici 0)) (hYp : ∀ u ∈ Ici (0:ℝ), 0 < Q (T0 * u))
    (hYe : ∀ u ∈ Ici (0:ℝ), Q (T0 * u) = fNq (N:ℕ∞) p q u +
          Real.sqrt ε * Muon.Foundations.oneSidedConv (fun v => Real.sqrt (Q (T0 * v))) g u)
    (hconv : ∀ u ∈ Icc (0:ℝ) (D * ((Cpq p q / Real.sqrt ε) ^ (1 / r0) - 1)),
          Muon.Foundations.oneSidedConv (fun w => Cpq p q * (1 + w / D) ^ (-r0)) g u
            ≤ 2 * (Cpq p q * (1 + u / D) ^ (-r0)))
    (hstep : dimHit Q T0 T ε ≠ ⊤ → stepHit m Q T ε = ENNReal.ofReal (S * T0 / (2 * Real.sqrt ε) *
          ∫ u in (0:ℝ)..(dimHit Q T0 T ε).toReal, Real.sqrt (Q (T0 * u)))) :
    ∃ û : ℝ, dimHit Q T0 T ε = ENNReal.ofReal û ∧ 0 < û ∧
      û ≤ D * ((Cpq p q / Real.sqrt ε) ^ (1 / r0) - 1) ∧ Q (T0 * û) = T * ε ∧
      (∀ u ∈ Ici (0:ℝ), fNq (N:ℕ∞) p q u ≤ Q (T0 * u)) ∧
      0 ≤ ∫ u in (0:ℝ)..û, (Real.sqrt (Q (T0 * u)) - Real.sqrt (fNq (N:ℕ∞) p q u)) ∧
      ∫ u in (0:ℝ)..û, (Real.sqrt (Q (T0 * u)) - Real.sqrt (fNq (N:ℕ∞) p q u)) ≤
        D * Cpq p q ^ (1 / r0) * (Real.sqrt 2 / (1 - r0 / 2) + 1) * ε ^ ((r0 - 1) / (2 * r0)) ∧
      stepHit m Q T ε = ENNReal.ofReal (S * T0 / (2 * Real.sqrt ε) *
          ∫ u in (0:ℝ)..û, Real.sqrt (Q (T0 * u))) := by
  obtain ⟨û, hhit, hû0, hûH, hYû, hYf, hE0, hE1⟩ := pw_hitB hp hq hT hD hr0 hr02 hr0r N ε g
    (fun u => Q (T0 * u)) hN hε hε0 hgc hgn hgi hgm hYc hYp hYe hconv
  have hdim : dimHit Q T0 T ε = ENNReal.ofReal û := hhit
  have hne : dimHit Q T0 T ε ≠ ⊤ := by rw [hdim]; exact ENNReal.ofReal_ne_top
  refine ⟨û, hdim, hû0, hûH, hYû, hYf, hE0, hE1, ?_⟩
  have hst := hstep hne
  rw [hdim, ENNReal.toReal_ofReal hû0.le] at hst
  exact hst

lemma pw_genEq1 {p q T D : ℝ} (hp : 1 < p) (hq : 0 < q) (hT : 4 ≤ T) (hD : 1 ≤ D)
    (hr1 : rq p q = 1)
    (N : ℕ) (ε S T0 : ℝ) (m : RowModel (Fin N)) (Q : ℝ → ℝ) (g : ℝ → ℝ)
    (hN : 4 ≤ N) (hε : 0 < ε)
    (hε0 : ε < clockEps0 p q T)
    (hgc : ContinuousOn g (Ici 0)) (hgn : ∀ u ∈ Ici (0:ℝ), 0 ≤ g u) (hgi : IntegrableOn g (Ioi 0))
    (hgm : ∫ u in Ioi (0:ℝ), g u ≤ 1)
    (hYc : ContinuousOn (fun u => Q (T0 * u)) (Ici 0)) (hYp : ∀ u ∈ Ici (0:ℝ), 0 < Q (T0 * u))
    (hYe : ∀ u ∈ Ici (0:ℝ), Q (T0 * u) = fNq (N:ℕ∞) p q u +
          Real.sqrt ε * Muon.Foundations.oneSidedConv (fun v => Real.sqrt (Q (T0 * v))) g u)
    (hconv : ∀ u ∈ Icc (0:ℝ) (D * ((Cpq p q / Real.sqrt ε) ^ (1 / (1:ℝ)) - 1)),
          Muon.Foundations.oneSidedConv (fun w => Cpq p q * (1 + w / D) ^ (-(1:ℝ))) g u
            ≤ 2 * (Cpq p q * (1 + u / D) ^ (-(1:ℝ))))
    (hHN : D * ((Cpq p q / Real.sqrt ε) ^ (1 / (1:ℝ)) - 1) ≤ ((N:ℝ) / 4) ^ q)
    (hstep : dimHit Q T0 T ε ≠ ⊤ → stepHit m Q T ε = ENNReal.ofReal (S * T0 / (2 * Real.sqrt ε) *
          ∫ u in (0:ℝ)..(dimHit Q T0 T ε).toReal, Real.sqrt (Q (T0 * u)))) :
    dimHit Q T0 T ε ≠ ⊤ ∧ ∃ I : ℝ,
      stepHit m Q T ε = ENNReal.ofReal (S * T0 / (2 * Real.sqrt ε) * I) ∧
      Real.sqrt (Aconst p) / 4 * Real.log (1 / ε) ≤ I ∧
      |I - aQ q / 2 * Real.log (1 / ε)| ≤
        (Cpq p q + aQ q * Real.log 2 + q * Mpq p q * (2 : ℝ) ^ (-(p / q)) / aQ q
          + aQ q / 2 * Real.log (T / Aconst p))
        + aQ q * max (Real.log (D * Cpq p q)) 0 + 1 / Real.sqrt (2 * (p - 1))
        + D * Cpq p q * (Real.sqrt 2 / (1 - 1 / 2) + 1) := by
  have hC := pw_Cpq_pos hp hq
  have hs : 0 < Real.sqrt ε := Real.sqrt_pos.2 hε
  obtain ⟨û, hdim, hû0, hûH, hYû, hYf, hE0, hE1, hst⟩ := pw_prepB (D := D) (r0 := 1) hp hq hT hD
    one_pos (by norm_num) hr1.ge N ε S T0 m Q g hN hε hε0 hgc hgn hgi hgm hYc hYp hYe hconv hstep
  have hne : dimHit Q T0 T ε ≠ ⊤ := by rw [hdim]; exact ENNReal.ofReal_ne_top
  refine ⟨hne, ∫ u in (0:ℝ)..û, Real.sqrt (Q (T0 * u)), hst, ?_⟩
  obtain ⟨hlow, hb⟩ := lem_app_phase_clock_integral_ii (p := p) (q := q) (T := T) (ε := ε)
    (H := D * ((Cpq p q / Real.sqrt ε) ^ (1 / (1:ℝ)) - 1)) (û := û) hp hq hT N hN hε hε0 hYc hYf
    (Y := fun u => Q (T0 * u)) hdim hû0 hYû hûH hr1 hHN
  beta_reduce at hb hlow
  refine ⟨hlow, ?_⟩
  refine hb.trans ?_
  have hX : 1 + D * ((Cpq p q / Real.sqrt ε) ^ (1 / (1:ℝ)) - 1) ≤ D * (Cpq p q / Real.sqrt ε) ^ (1 / (1:ℝ)) := by
    have : (1:ℝ) ≤ D := hD
    have h1 : (Cpq p q / Real.sqrt ε) ^ (1 / (1:ℝ)) = Cpq p q / Real.sqrt ε := by simp
    rw [h1]; nlinarith
  set H := D * ((Cpq p q / Real.sqrt ε) ^ (1 / (1:ℝ)) - 1) with hH
  have hHnn : 0 ≤ H := by
    exact hû0.le.trans hûH
  have hXpos : 0 < (1 + H) * Real.sqrt ε := by
    have : 0 ≤ H := hHnn
    positivity
  have hXle : (1 + H) * Real.sqrt ε ≤ D * Cpq p q := by
    have h1 : D * (Cpq p q / Real.sqrt ε) ^ (1 / (1:ℝ)) * Real.sqrt ε = D * Cpq p q := by
      simp only [div_one, Real.rpow_one]; field_simp
    rw [← h1]; exact mul_le_mul_of_nonneg_right hX hs.le
  have hlogb : max (Real.log ((1 + H) * Real.sqrt ε)) 0 ≤ max (Real.log (D * Cpq p q)) 0 :=
    max_le_max (Real.log_le_log hXpos hXle) le_rfl
  have hN4 : (4:ℝ) ≤ N := by exact_mod_cast hN
  have hNq : 0 < (N:ℝ) ^ q := Real.rpow_pos_of_pos (by linarith) _
  have h4q : (1:ℝ) ≤ (4:ℝ) ^ q := Real.one_le_rpow (by norm_num) hq.le
  have hHNq : H * (N:ℝ) ^ (-q) ≤ 1 := by
    rw [Real.rpow_neg (by positivity)]
    rw [← div_eq_mul_inv, div_le_one hNq]
    refine hHN.trans ?_
    rw [Real.div_rpow (by positivity) (by norm_num)]
    exact div_le_self hNq.le h4q
  have hsq : 0 < Real.sqrt (2 * (p - 1)) := Real.sqrt_pos.2 (by linarith)
  have hHterm : H * (N:ℝ) ^ (-q) / Real.sqrt (2 * (p - 1)) ≤ 1 / Real.sqrt (2 * (p - 1)) :=
    div_le_div_of_nonneg_right hHNq hsq.le
  have hEb : ∫ u in (0:ℝ)..û, (Real.sqrt (Q (T0 * u)) - Real.sqrt (fNq (N:ℕ∞) p q u)) ≤
      D * Cpq p q * (Real.sqrt 2 / (1 - 1 / 2) + 1) := by
    refine hE1.trans (le_of_eq ?_)
    norm_num
  have haq : 0 < aQ q := by unfold aQ; positivity
  have := mul_le_mul_of_nonneg_left hlogb haq.le
  gcongr

lemma pw_genGt1 {p q T D r0 : ℝ} (hp : 1 < p) (hq : 0 < q) (hT : 4 ≤ T) (hD : 1 ≤ D)
    (hr0 : 0 < r0) (hr02 : r0 < 2) (hr0r : r0 ≤ rq p q) (hr1 : 1 < rq p q)
    (N : ℕ) (ε S T0 : ℝ) (m : RowModel (Fin N)) (Q : ℝ → ℝ) (g : ℝ → ℝ)
    (hN : 4 ≤ N) (hε : 0 < ε)
    (hε0 : ε < clockEps0 p q T)
    (hgc : ContinuousOn g (Ici 0)) (hgn : ∀ u ∈ Ici (0:ℝ), 0 ≤ g u) (hgi : IntegrableOn g (Ioi 0))
    (hgm : ∫ u in Ioi (0:ℝ), g u ≤ 1)
    (hYc : ContinuousOn (fun u => Q (T0 * u)) (Ici 0)) (hYp : ∀ u ∈ Ici (0:ℝ), 0 < Q (T0 * u))
    (hYe : ∀ u ∈ Ici (0:ℝ), Q (T0 * u) = fNq (N:ℕ∞) p q u +
          Real.sqrt ε * Muon.Foundations.oneSidedConv (fun v => Real.sqrt (Q (T0 * v))) g u)
    (hconv : ∀ u ∈ Icc (0:ℝ) (D * ((Cpq p q / Real.sqrt ε) ^ (1 / r0) - 1)),
          Muon.Foundations.oneSidedConv (fun w => Cpq p q * (1 + w / D) ^ (-r0)) g u
            ≤ 2 * (Cpq p q * (1 + u / D) ^ (-r0)))
    (hstep : dimHit Q T0 T ε ≠ ⊤ → stepHit m Q T ε = ENNReal.ofReal (S * T0 / (2 * Real.sqrt ε) *
          ∫ u in (0:ℝ)..(dimHit Q T0 T ε).toReal, Real.sqrt (Q (T0 * u)))) :
    dimHit Q T0 T ε ≠ ⊤ ∧ ∃ I E : ℝ,
      stepHit m Q T ε = ENNReal.ofReal (S * T0 / (2 * Real.sqrt ε) * I) ∧
      1 / (2 * Real.sqrt 2) ≤ I ∧ I ≤ Jpq p q + E ∧ 0 ≤ E ∧
      E ≤ D * Cpq p q ^ (1 / r0) * (Real.sqrt 2 / (1 - r0 / 2) + 1) * ε ^ ((r0 - 1) / (2 * r0)) ∧
      |I - Jpq p q| ≤
        (1 / Real.sqrt (2 * (p - 1)) + Cpq p q / (rq p q - 1)) * (N : ℝ) ^ (-(q * (rq p q - 1)))
        + Cpq p q / (rq p q - 1) * (1 + 1 / 2 * Real.log (1 / (2 * T * ε))) ^ (1 - rq p q) + E := by
  obtain ⟨û, hdim, hû0, hûH, hYû, hYf, hE0, hE1, hst⟩ := pw_prepB (D := D) (r0 := r0) hp hq hT hD
    hr0 hr02 hr0r N ε S T0 m Q g hN hε hε0 hgc hgn hgi hgm hYc hYp hYe hconv hstep
  have hne : dimHit Q T0 T ε ≠ ⊤ := by rw [hdim]; exact ENNReal.ofReal_ne_top
  obtain ⟨h1, h2, h3⟩ := lem_app_phase_clock_integral_iii (p := p) (q := q) (T := T) (ε := ε)
    (H := D * ((Cpq p q / Real.sqrt ε) ^ (1 / r0) - 1)) (û := û) hp hq hT N hN hε hε0 hYc hYf
    (Y := fun u => Q (T0 * u)) hdim hû0 hYû hûH hr1
  beta_reduce at h1 h2 h3
  exact ⟨hne, _, _, hst, h1, h2, hE0, hE1, h3⟩

lemma pw_sandI {S T0 P a b ε I : ℝ} {t : ℝ≥0∞} (hS : 0 < S) (hT0 : 0 < T0) (hP : 0 < P)
    (hε : 0 < ε) (ha : 0 < a) (hI : t = ENNReal.ofReal (S * T0 / (2 * Real.sqrt ε) * I))
    (h1 : a * (2 * Real.sqrt ε * P) ≤ I) (h2 : I ≤ b * (2 * Real.sqrt ε * P)) :
    SandwichE a b (S * T0 * P) t := by
  have hs : 0 < Real.sqrt ε := Real.sqrt_pos.2 hε
  have hk : 0 < 2 * Real.sqrt ε * P := by positivity
  have hab : a ≤ b := by
    have := h1.trans h2
    exact le_of_mul_le_mul_right this hk
  have hb : 0 ≤ b := by linarith
  have hpre : 0 < S * T0 / (2 * Real.sqrt ε) := by positivity
  have hX : 0 < S * T0 * P := by positivity
  unfold SandwichE
  rw [hI]
  constructor
  · rw [← ENNReal.ofReal_mul ha.le]
    apply ENNReal.ofReal_le_ofReal
    have := mul_le_mul_of_nonneg_left h1 hpre.le
    calc a * (S * T0 * P) = S * T0 / (2 * Real.sqrt ε) * (a * (2 * Real.sqrt ε * P)) := by
          field_simp
      _ ≤ _ := this
  · rw [← ENNReal.ofReal_mul hb]
    apply ENNReal.ofReal_le_ofReal
    have := mul_le_mul_of_nonneg_left h2 hpre.le
    calc _ ≤ S * T0 / (2 * Real.sqrt ε) * (b * (2 * Real.sqrt ε * P)) := this
      _ = b * (S * T0 * P) := by field_simp

lemma pw_eps_lt_quarter {p q T : ℝ} {ε : ℝ} (h : ε < clockEps0 p q T) : ε < 1 / 4 := by
  unfold clockEps0 at h
  split_ifs at h <;> simp only [lt_min_iff] at h
  · exact h.1.1.1.1
  · exact h.1.1.1

lemma pw_packEq1 {p q T D : ℝ} (hp : 1 < p) (hq : 0 < q) (hT : 4 ≤ T) (hD : 1 ≤ D)
    (hr1 : rq p q = 1) :
    ∃ a b K : ℝ, 0 < a ∧ 0 < b ∧ 0 ≤ K ∧
    ∀ (N : ℕ) (ε S T0 : ℝ) (m : RowModel (Fin N)) (Q : ℝ → ℝ) (g : ℝ → ℝ),
    4 ≤ N → 0 < ε → ε < clockEps0 p q T → 0 < S → 0 < T0 →
    ContinuousOn g (Ici 0) → (∀ u ∈ Ici (0:ℝ), 0 ≤ g u) → IntegrableOn g (Ioi 0) →
    ∫ u in Ioi (0:ℝ), g u ≤ 1 →
    ContinuousOn (fun u => Q (T0 * u)) (Ici 0) → (∀ u ∈ Ici (0:ℝ), 0 < Q (T0 * u)) →
    (∀ u ∈ Ici (0:ℝ), Q (T0 * u) = fNq (N:ℕ∞) p q u +
          Real.sqrt ε * Muon.Foundations.oneSidedConv (fun v => Real.sqrt (Q (T0 * v))) g u) →
    (∀ u ∈ Icc (0:ℝ) (D * ((Cpq p q / Real.sqrt ε) ^ (1 / (1:ℝ)) - 1)),
          Muon.Foundations.oneSidedConv (fun w => Cpq p q * (1 + w / D) ^ (-(1:ℝ))) g u
            ≤ 2 * (Cpq p q * (1 + u / D) ^ (-(1:ℝ)))) →
    D * ((Cpq p q / Real.sqrt ε) ^ (1 / (1:ℝ)) - 1) ≤ ((N:ℝ) / 4) ^ q →
    (dimHit Q T0 T ε ≠ ⊤ → stepHit m Q T ε = ENNReal.ofReal (S * T0 / (2 * Real.sqrt ε) *
          ∫ u in (0:ℝ)..(dimHit Q T0 T ε).toReal, Real.sqrt (Q (T0 * u)))) →
    dimHit Q T0 T ε ≠ ⊤ ∧ SandwichE a b (S * T0 * phasePi (rq p q) ε) (stepHit m Q T ε) ∧
      ∃ I : ℝ, 0 < I ∧ stepHit m Q T ε = ENNReal.ofReal (S * T0 / (2 * Real.sqrt ε) * I) ∧
        |I - aQ q / 2 * Real.log (1 / ε)| ≤ K := by
  have hA0 : 0 < Aconst p := by unfold Aconst; positivity
  have haq : 0 < aQ q := by unfold aQ; positivity
  have hC := pw_Cpq_pos hp hq
  have hlog4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  set K : ℝ := (Cpq p q + aQ q * Real.log 2 + q * Mpq p q * (2 : ℝ) ^ (-(p / q)) / aQ q
          + aQ q / 2 * Real.log (T / Aconst p))
        + aQ q * max (Real.log (D * Cpq p q)) 0 + 1 / Real.sqrt (2 * (p - 1))
        + D * Cpq p q * (Real.sqrt 2 / (1 - 1 / 2) + 1) with hK
  have hA1 : Aconst p ≤ 1 := by
    unfold Aconst
    have h1 : (2:ℝ) ^ (-(2 * p)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by linarith)
    have h2 : Real.exp (-2) ≤ 1 := by rw [Real.exp_le_one_iff]; norm_num
    have h3 : 0 < Real.exp (-2) := Real.exp_pos _
    have h4 : 0 < (2:ℝ) ^ (-(2 * p)) := Real.rpow_pos_of_pos (by norm_num) _
    nlinarith
  have hlogTA : 0 ≤ Real.log (T / Aconst p) := by
    apply Real.log_nonneg
    rw [le_div_iff₀ hA0]; nlinarith
  have hKnn : 0 ≤ K := by
    have h1 : 0 ≤ Mpq p q := by unfold Mpq; positivity
    have h2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    have h3 : 0 ≤ max (Real.log (D * Cpq p q)) 0 := le_max_right _ _
    rw [hK]
    have h5 : 0 ≤ q * Mpq p q * (2 : ℝ) ^ (-(p / q)) / aQ q := by positivity
    have h6 : 0 ≤ 1 / Real.sqrt (2 * (p - 1)) := by positivity
    have h7 : 0 ≤ D * Cpq p q * (Real.sqrt 2 / (1 - 1 / 2) + 1) := by positivity
    have h8 : 0 ≤ aQ q / 2 * Real.log (T / Aconst p) := by positivity
    have h9 : 0 ≤ aQ q * Real.log 2 := by positivity
    have h10 : 0 ≤ aQ q * max (Real.log (D * Cpq p q)) 0 := by positivity
    linarith
  refine ⟨Real.sqrt (Aconst p) / 8, aQ q / 4 + K / (2 * Real.log 4), K, by positivity, by positivity, hKnn, ?_⟩
  intro N ε S T0 m Q g hN hε hε0 hS hT0 hgc hgn hgi hgm hYc hYp hYe hconv hHN hstep
  obtain ⟨hne, I, hst, hlow, hb⟩ := pw_genEq1 hp hq hT hD hr1 N ε S T0 m Q g hN hε hε0 hgc hgn hgi hgm
    hYc hYp hYe hconv hHN hstep
  have hε4 := pw_eps_lt_quarter hε0
  have hL : Real.log 4 ≤ Real.log (1 / ε) :=
    Real.log_le_log (by norm_num) (by rw [le_div_iff₀ hε]; linarith)
  have hL0 : 0 < Real.log (1 / ε) := by linarith
  have hsA : 0 < Real.sqrt (Aconst p) := Real.sqrt_pos.2 hA0
  have hIpos : 0 < I := lt_of_lt_of_le (by positivity) hlow
  refine ⟨hne, ?_, I, hIpos, hst, hb⟩
  have hs : 0 < Real.sqrt ε := Real.sqrt_pos.2 hε
  have hPi : phasePi (rq p q) ε = ε ^ (-(1 / 2 : ℝ)) * Real.log (1 / ε) := by
    unfold phasePi
    rw [hr1]
    simp
  have hP : 2 * Real.sqrt ε * (ε ^ (-(1 / 2 : ℝ)) * Real.log (1 / ε)) = 2 * Real.log (1 / ε) := by
    rw [Real.sqrt_eq_rpow, ← mul_assoc, mul_assoc 2, ← Real.rpow_add hε]
    norm_num
  have hPpos : 0 < ε ^ (-(1 / 2 : ℝ)) * Real.log (1 / ε) := by
    have := Real.rpow_pos_of_pos hε (-(1 / 2 : ℝ)); positivity
  rw [hPi]
  refine pw_sandI hS hT0 hPpos hε (by positivity) hst ?_ ?_
  · rw [hP]; nlinarith
  · rw [hP]
    have hI2 := (abs_le.1 hb).2
    have : K ≤ K / (2 * Real.log 4) * (2 * Real.log (1 / ε)) := by
      rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
      nlinarith [hKnn]
    nlinarith

lemma pw_packGt1 {p q T D r0 : ℝ} (hp : 1 < p) (hq : 0 < q) (hT : 4 ≤ T) (hD : 1 ≤ D)
    (hr01 : 1 < r0) (hr02 : r0 < 2) (hr0r : r0 ≤ rq p q) :
    ∃ a b : ℝ, 0 < a ∧ 0 < b ∧
    ∀ (N : ℕ) (ε S T0 : ℝ) (m : RowModel (Fin N)) (Q : ℝ → ℝ) (g : ℝ → ℝ),
    4 ≤ N → 0 < ε → ε < clockEps0 p q T → 0 < S → 0 < T0 →
    ContinuousOn g (Ici 0) → (∀ u ∈ Ici (0:ℝ), 0 ≤ g u) → IntegrableOn g (Ioi 0) →
    ∫ u in Ioi (0:ℝ), g u ≤ 1 →
    ContinuousOn (fun u => Q (T0 * u)) (Ici 0) → (∀ u ∈ Ici (0:ℝ), 0 < Q (T0 * u)) →
    (∀ u ∈ Ici (0:ℝ), Q (T0 * u) = fNq (N:ℕ∞) p q u +
          Real.sqrt ε * Muon.Foundations.oneSidedConv (fun v => Real.sqrt (Q (T0 * v))) g u) →
    (∀ u ∈ Icc (0:ℝ) (D * ((Cpq p q / Real.sqrt ε) ^ (1 / r0) - 1)),
          Muon.Foundations.oneSidedConv (fun w => Cpq p q * (1 + w / D) ^ (-r0)) g u
            ≤ 2 * (Cpq p q * (1 + u / D) ^ (-r0))) →
    (dimHit Q T0 T ε ≠ ⊤ → stepHit m Q T ε = ENNReal.ofReal (S * T0 / (2 * Real.sqrt ε) *
          ∫ u in (0:ℝ)..(dimHit Q T0 T ε).toReal, Real.sqrt (Q (T0 * u)))) →
    dimHit Q T0 T ε ≠ ⊤ ∧ SandwichE a b (S * T0 * phasePi (rq p q) ε) (stepHit m Q T ε) ∧
      ∃ I : ℝ, 0 < I ∧ stepHit m Q T ε = ENNReal.ofReal (S * T0 / (2 * Real.sqrt ε) * I) ∧
        1 / (2 * Real.sqrt 2) ≤ I ∧ |I - Jpq p q| ≤
        (1 / Real.sqrt (2 * (p - 1)) + Cpq p q / (rq p q - 1)) * (N : ℝ) ^ (-(q * (rq p q - 1)))
        + Cpq p q / (rq p q - 1) * (1 + 1 / 2 * Real.log (1 / (2 * T * ε))) ^ (1 - rq p q)
        + D * Cpq p q ^ (1 / r0) * (Real.sqrt 2 / (1 - r0 / 2) + 1) * ε ^ ((r0 - 1) / (2 * r0)) := by
  have hr1 : 1 < rq p q := lt_of_lt_of_le hr01 hr0r
  have hC := pw_Cpq_pos hp hq
  have hD0 : 0 < D := by linarith
  have hc3 : 0 < D * Cpq p q ^ (1 / r0) * (Real.sqrt 2 / (1 - r0 / 2) + 1) := by
    have : 0 < 1 - r0 / 2 := by linarith
    have : 0 < Cpq p q ^ (1 / r0) := Real.rpow_pos_of_pos hC _
    positivity
  set c3 := D * Cpq p q ^ (1 / r0) * (Real.sqrt 2 / (1 - r0 / 2) + 1) with hc3d
  refine ⟨1 / (4 * Real.sqrt 2), (|Jpq p q| + c3 + 1) / 2, by positivity, by positivity, ?_⟩
  intro N ε S T0 m Q g hN hε hε0 hS hT0 hgc hgn hgi hgm hYc hYp hYe hconv hstep
  obtain ⟨hne, I, E, hst, hlow, hup, hE0, hE1, hb⟩ := pw_genGt1 hp hq hT hD (by linarith) hr02 hr0r hr1
    N ε S T0 m Q g hN hε hε0 hgc hgn hgi hgm hYc hYp hYe hconv hstep
  have hε4 := pw_eps_lt_quarter hε0
  have hs2 : 0 < Real.sqrt 2 := by positivity
  have hIpos : 0 < I := lt_of_lt_of_le (by positivity) hlow
  have hPi : phasePi (rq p q) ε = ε ^ (-(1 / 2 : ℝ)) := by
    unfold phasePi
    rw [if_neg (by linarith), if_neg (by linarith)]
  have hP : 2 * Real.sqrt ε * ε ^ (-(1 / 2 : ℝ)) = 2 := by
    rw [Real.sqrt_eq_rpow, mul_assoc, ← Real.rpow_add hε]
    norm_num
  have hεle : ε ^ ((r0 - 1) / (2 * r0)) ≤ 1 :=
    Real.rpow_le_one hε.le (by linarith) (by positivity)
  have hE2 : E ≤ c3 := by
    refine hE1.trans ?_
    calc c3 * ε ^ ((r0 - 1) / (2 * r0)) ≤ c3 * 1 := mul_le_mul_of_nonneg_left hεle hc3.le
      _ = c3 := mul_one _
  refine ⟨hne, ?_, I, hIpos, hst, hlow, ?_⟩
  · rw [hPi]
    have hPpos := Real.rpow_pos_of_pos hε (-(1 / 2 : ℝ))
    refine pw_sandI hS hT0 hPpos hε (by positivity) hst ?_ ?_
    · rw [hP]
      have : 1 / (4 * Real.sqrt 2) * 2 = 1 / (2 * Real.sqrt 2) := by field_simp; ring
      rw [this]; exact hlow
    · rw [hP]
      have := le_abs_self (Jpq p q)
      linarith
  · refine hb.trans ?_
    have := mul_le_mul_of_nonneg_left hεle hc3.le
    have e : D * Cpq p q ^ (1 / r0) * (Real.sqrt 2 / (1 - r0 / 2) + 1) * ε ^ ((r0 - 1) / (2 * r0)) = c3 * ε ^ ((r0 - 1) / (2 * r0)) := rfl
    rw [e] at hE1 ⊢
    linarith

lemma pw_Bd_small {r κ1 κ T c1 c2 c3 : ℝ} (hr : 1 < r) (hκ1 : 0 < κ1) (hκ : 0 < κ)
    (hT : 0 < T) :
    ∀ δ : ℝ, 0 < δ → ∃ (N2 : ℕ) (ε2 : ℝ), 0 < ε2 ∧ ∀ (N : ℕ) (ε : ℝ), N2 ≤ N → 0 < ε → ε < ε2 →
      c1 * (N : ℝ) ^ (-κ1)
        + c2 * (1 + 1 / 2 * Real.log (1 / (2 * T * ε))) ^ (1 - r)
        + c3 * ε ^ κ ≤ δ := by
  intro δ hδ
  have hd3 : 0 < δ / 3 := by positivity
  -- term 1
  have t1 : Tendsto (fun N : ℕ => c1 * (N : ℝ) ^ (-κ1)) atTop (𝓝 0) := by
    have := ((tendsto_rpow_neg_atTop hκ1).comp tendsto_natCast_atTop_atTop).const_mul c1
    simpa using this
  obtain ⟨N2, hN2⟩ := eventually_atTop.1 ((tendsto_order.1 t1).2 _ hd3)
  -- term 3
  have t3 : Tendsto (fun ε : ℝ => c3 * ε ^ κ) (𝓝[>] 0) (𝓝 0) := by
    have h : Tendsto (fun ε : ℝ => c3 * ε ^ κ) (𝓝 0) (𝓝 (c3 * (0:ℝ) ^ κ)) :=
      ((Real.continuousAt_rpow_const 0 κ (Or.inr hκ.le)).tendsto).const_mul c3
    rw [Real.zero_rpow hκ.ne', mul_zero] at h
    exact tendsto_nhdsWithin_of_tendsto_nhds h
  -- term 2
  have t2 : Tendsto (fun ε : ℝ => c2 * (1 + 1 / 2 * Real.log (1 / (2 * T * ε))) ^ (1 - r))
      (𝓝[>] 0) (𝓝 0) := by
    have h1 : Tendsto (fun ε : ℝ => 1 / (2 * T * ε)) (𝓝[>] 0) atTop := by
      have := tendsto_inv_nhdsGT_zero.const_mul_atTop (show 0 < (2 * T)⁻¹ by positivity)
      refine this.congr (fun ε => ?_)
      field_simp
    have h2 := (Real.tendsto_log_atTop.comp h1)
    have h3 : Tendsto (fun ε : ℝ => 1 + 1 / 2 * Real.log (1 / (2 * T * ε))) (𝓝[>] 0) atTop :=
      tendsto_atTop_add_const_left _ 1 (h2.const_mul_atTop (by norm_num))
    have h4 := (tendsto_rpow_neg_atTop (show 0 < r - 1 by linarith)).comp h3
    have h5 := h4.const_mul c2
    simp only [mul_zero] at h5
    refine h5.congr (fun ε => ?_)
    simp only [Function.comp]
    congr 2
    ring
  have e23 := ((tendsto_order.1 t2).2 _ hd3).and ((tendsto_order.1 t3).2 _ hd3)
  obtain ⟨u, hu, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 e23
  refine ⟨N2, u, hu, fun N ε hN hε hεu => ?_⟩
  have h1 := hN2 N hN
  obtain ⟨h2, h3⟩ := hsub ⟨hε, hεu⟩
  linarith

lemma pw_sqrt_le {q : ℝ} (hq : 1 / 2 < q) :
    ∃ N0 : ℕ, 1 ≤ N0 ∧ ∀ N : ℕ, N0 ≤ N → Real.sqrt (N : ℝ) ≤ ((N : ℝ) / 4) ^ q := by
  have hd : 0 < q - 1 / 2 := by linarith
  refine ⟨⌈(4:ℝ) ^ (q / (q - 1 / 2))⌉₊ + 1, by omega, fun N hN => ?_⟩
  have hN1 : (4:ℝ) ^ (q / (q - 1 / 2)) ≤ N := by
    have h1 := Nat.le_ceil ((4:ℝ) ^ (q / (q - 1 / 2)))
    have h2 : ((⌈(4:ℝ) ^ (q / (q - 1 / 2))⌉₊ + 1 : ℕ) : ℝ) ≤ N := by exact_mod_cast hN
    push_cast at h2
    linarith
  have hN0 : (0:ℝ) < N := lt_of_lt_of_le (by positivity) hN1
  have h3 : ((4:ℝ) ^ (q / (q - 1 / 2))) ^ (q - 1 / 2) ≤ (N:ℝ) ^ (q - 1 / 2) :=
    Real.rpow_le_rpow (by positivity) hN1 hd.le
  rw [← Real.rpow_mul (by norm_num), div_mul_cancel₀ _ hd.ne'] at h3
  rw [Real.div_rpow hN0.le (by norm_num), Real.sqrt_eq_rpow, le_div_iff₀ (by positivity)]
  have : (N:ℝ) ^ q = (N:ℝ) ^ (q - 1 / 2) * (N:ℝ) ^ (1 / 2 : ℝ) := by
    rw [← Real.rpow_add hN0]; ring_nf
  rw [this, mul_comm ((N:ℝ) ^ (q - 1 / 2))]
  exact mul_le_mul_of_nonneg_left h3 (by positivity)

lemma pw_horizonB {C D r0 ε N : ℝ} (hC : 0 < C) (hD : 0 < D) (hr0 : 1 ≤ r0) (hε : 0 < ε)
    (hN : 1 ≤ N) (hE : C ^ 2 * D ^ (2 * r0) ≤ ε * N) :
    D * (C / Real.sqrt ε) ^ (1 / r0) ≤ Real.sqrt N := by
  have hs : 0 < Real.sqrt ε := Real.sqrt_pos.2 hε
  have hr : 0 < r0 := by linarith
  set X := D * (C / Real.sqrt ε) ^ (1 / r0) with hX
  have hXp : 0 < X := by positivity
  have h1 : X ^ (2 * r0) = D ^ (2 * r0) * (C ^ 2 / ε) := by
    rw [hX, Real.mul_rpow hD.le (by positivity), ← Real.rpow_mul (by positivity)]
    have : 1 / r0 * (2 * r0) = 2 := by field_simp
    rw [this, Real.div_rpow hC.le hs.le]
    have h2 : (C ^ (2:ℝ)) = C ^ 2 := by norm_cast
    have h3 : (Real.sqrt ε) ^ (2:ℝ) = ε := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hε.le]; norm_num
    rw [h2, h3]
  have h2 : X ^ (2 * r0) ≤ N := by
    rw [h1]
    have : D ^ (2 * r0) * (C ^ 2 / ε) = C ^ 2 * D ^ (2 * r0) / ε := by ring
    rw [this, div_le_iff₀ hε]
    linarith
  have h3 : X ≤ N ^ (1 / (2 * r0)) := by
    calc X = (X ^ (2 * r0)) ^ (1 / (2 * r0)) := by
          rw [← Real.rpow_mul hXp.le]; field_simp; simp
      _ ≤ N ^ (1 / (2 * r0)) := Real.rpow_le_rpow (by positivity) h2 (by positivity)
  have hN0 : (0:ℝ) < N := by linarith
  refine h3.trans ?_
  rw [Real.sqrt_eq_rpow]
  apply Real.rpow_le_rpow_of_exponent_le hN
  rw [div_le_div_iff₀ (by positivity) (by norm_num)]
  linarith

lemma pw_genB {p q T D r0 : ℝ} (hp : 1 < p) (hq : 1 / 2 < q) (hT : 4 ≤ T) (hD : 1 ≤ D)
    (hr0 : 1 ≤ r0) (hr02 : r0 < 2) (hr0r : r0 ≤ rq p q) (hr1 : 1 ≤ rq p q)
    (hgt : 1 < rq p q → 1 < r0) (N0 : ℕ) (hN0 : 4 ≤ N0) :
    ∃ (N1 : ℕ) (E1 a b K : ℝ) (Bd : ℕ → ℝ → ℝ), 4 ≤ N1 ∧ N0 ≤ N1 ∧ E1 = Cpq p q ^ 2 * D ^ (2 * r0) ∧ 0 < a ∧ 0 < b ∧ 0 ≤ K ∧
    (∀ δ : ℝ, 0 < δ → ∃ (N2 : ℕ) (ε2 : ℝ), 0 < ε2 ∧ ∀ (N : ℕ) (ε : ℝ), N2 ≤ N → 0 < ε → ε < ε2 →
      Bd N ε ≤ δ) ∧
    ∀ (N : ℕ) (ε S T0 : ℝ) (m : RowModel (Fin N)) (Q : ℝ → ℝ) (g : ℝ → ℝ),
    N1 ≤ N → 0 < ε → ε < clockEps0 p q T → E1 ≤ ε * (N : ℝ) → 0 < S → 0 < T0 →
    ContinuousOn g (Ici 0) → (∀ u ∈ Ici (0:ℝ), 0 ≤ g u) → IntegrableOn g (Ioi 0) →
    ∫ u in Ioi (0:ℝ), g u ≤ 1 →
    ContinuousOn (fun u => Q (T0 * u)) (Ici 0) → (∀ u ∈ Ici (0:ℝ), 0 < Q (T0 * u)) →
    (∀ u ∈ Ici (0:ℝ), Q (T0 * u) = fNq (N:ℕ∞) p q u +
          Real.sqrt ε * Muon.Foundations.oneSidedConv (fun v => Real.sqrt (Q (T0 * v))) g u) →
    (D * (Cpq p q / Real.sqrt ε) ^ (1 / r0) ≤ Real.sqrt (N : ℝ) →
      ∀ u ∈ Icc (0:ℝ) (D * ((Cpq p q / Real.sqrt ε) ^ (1 / r0) - 1)),
          Muon.Foundations.oneSidedConv (fun w => Cpq p q * (1 + w / D) ^ (-r0)) g u
            ≤ 2 * (Cpq p q * (1 + u / D) ^ (-r0))) →
    (dimHit Q T0 T ε ≠ ⊤ → stepHit m Q T ε = ENNReal.ofReal (S * T0 / (2 * Real.sqrt ε) *
          ∫ u in (0:ℝ)..(dimHit Q T0 T ε).toReal, Real.sqrt (Q (T0 * u)))) →
    dimHit Q T0 T ε ≠ ⊤ ∧ SandwichE a b (S * T0 * phasePi (rq p q) ε) (stepHit m Q T ε) ∧
      ∃ I : ℝ, 0 < I ∧ stepHit m Q T ε = ENNReal.ofReal (S * T0 / (2 * Real.sqrt ε) * I) ∧
        (rq p q = 1 → |I - aQ q / 2 * Real.log (1 / ε)| ≤ K) ∧
        (1 < rq p q → 1 / (2 * Real.sqrt 2) ≤ I ∧ |I - Jpq p q| ≤ Bd N ε) := by
  have hq0 : 0 < q := by linarith
  have hC := pw_Cpq_pos hp hq0
  have hD0 : 0 < D := by linarith
  obtain ⟨Nq, hNq1, hNq⟩ := pw_sqrt_le hq
  set E1 : ℝ := Cpq p q ^ 2 * D ^ (2 * r0) with hE1
  have hN14 : 4 ≤ max N0 Nq := le_trans hN0 (le_max_left _ _)
  rcases eq_or_lt_of_le hr1 with h1 | h1
  · -- r = 1
    have hr01 : r0 = 1 := le_antisymm (h1 ▸ hr0r) hr0
    subst hr01
    obtain ⟨a, b, K, ha, hb, hK, hpack⟩ := pw_packEq1 (D := D) hp hq0 hT hD h1.symm
    refine ⟨max N0 Nq, E1, a, b, K, fun _ _ => 0, hN14, le_max_left _ _, rfl, ha, hb, hK,
      fun δ hδ => ⟨0, 1, one_pos, fun N ε _ _ _ => hδ.le⟩, ?_⟩
    intro N ε S T0 m Q g hN hε hε0 hE hS hT0 hgc hgn hgi hgm hYc hYp hYe hconv hstep
    have hN4 : 4 ≤ N := le_trans hN14 hN
    have hN1r : (1:ℝ) ≤ N := by exact_mod_cast (by omega : 1 ≤ N)
    have hH := pw_horizonB hC hD0 hr0 hε hN1r hE
    have hconv' := hconv hH
    have hHN : D * ((Cpq p q / Real.sqrt ε) ^ (1 / (1:ℝ)) - 1) ≤ ((N:ℝ) / 4) ^ q := by
      have := hNq N (le_trans (le_max_right _ _) hN)
      linarith
    obtain ⟨hne, hsand, I, hI, hst, hb⟩ := hpack N ε S T0 m Q g hN4 hε hε0 hS hT0 hgc hgn hgi hgm hYc
      hYp hYe hconv' hHN hstep
    exact ⟨hne, hsand, I, hI, hst, fun _ => hb, fun h => absurd h (by rw [h1]; exact lt_irrefl _)⟩
  · -- r > 1
    have hr01 : 1 < r0 := hgt h1
    obtain ⟨a, b, ha, hb, hpack⟩ := pw_packGt1 (D := D) hp hq0 hT hD hr01 hr02 hr0r
    have hr1' : 0 < rq p q - 1 := by linarith
    have hκ1 : 0 < q * (rq p q - 1) := by positivity
    have hκ : 0 < (r0 - 1) / (2 * r0) := by apply div_pos <;> linarith
    refine ⟨max N0 Nq, E1, a, b, 0,
      fun N ε => (1 / Real.sqrt (2 * (p - 1)) + Cpq p q / (rq p q - 1)) * (N : ℝ) ^ (-(q * (rq p q - 1)))
        + Cpq p q / (rq p q - 1) * (1 + 1 / 2 * Real.log (1 / (2 * T * ε))) ^ (1 - rq p q)
        + D * Cpq p q ^ (1 / r0) * (Real.sqrt 2 / (1 - r0 / 2) + 1) * ε ^ ((r0 - 1) / (2 * r0)),
      hN14, le_max_left _ _, rfl, ha, hb, le_rfl,
      pw_Bd_small h1 hκ1 hκ (by linarith), ?_⟩
    intro N ε S T0 m Q g hN hε hε0 hE hS hT0 hgc hgn hgi hgm hYc hYp hYe hconv hstep
    have hN4 : 4 ≤ N := le_trans hN14 hN
    have hN1r : (1:ℝ) ≤ N := by exact_mod_cast (by omega : 1 ≤ N)
    have hH := pw_horizonB hC hD0 hr0 hε hN1r hE
    have hconv' := hconv hH
    obtain ⟨hne, hsand, I, hI, hst, hlow, hb⟩ := hpack N ε S T0 m Q g hN4 hε hε0 hS hT0 hgc hgn hgi hgm hYc
      hYp hYe hconv' hstep
    exact ⟨hne, hsand, I, hI, hst, fun h => absurd h (by linarith), fun _ => ⟨hlow, hb⟩⟩

lemma pw_svdB_gen (α ς T D r0 : ℝ) (N0 : ℕ) (hα : 1 < α) (hς : 1 ≤ ς) (hT : 4 ≤ T)
    (hD : 1 ≤ D) (hr0 : 1 ≤ r0) (hr02 : r0 < 2) (hr0r : r0 ≤ rq (α + ς) (α / 2))
    (hr1 : 1 ≤ rq (α + ς) (α / 2))
    (hgt : 1 < rq (α + ς) (α / 2) → 1 < r0) (hN0 : 4 ≤ N0)
    (hprov : ∀ N : ℕ, N0 ≤ N → ∀ ε : ℝ, 0 < ε → ε < clockEps0 (α + ς) (α / 2) T →
      Cpq (α + ς) (α / 2) ^ 2 * D ^ (2 * r0) ≤ ε * (N : ℝ) →
      D * (Cpq (α + ς) (α / 2) / Real.sqrt ε) ^ (1 / r0) ≤ Real.sqrt (N : ℝ) →
      ∀ g : ℝ → ℝ, ContinuousOn g (Ici 0) → (∀ u ∈ Ici (0:ℝ), 0 ≤ g u) →
      IntegrableOn g (Ioi 0) → ∫ u in Ioi (0:ℝ), g u ≤ 1 →
      (∀ u ∈ Ici (0:ℝ), g u = svdKernel α N u) →
      ∀ u ∈ Icc (0:ℝ) (D * ((Cpq (α + ς) (α / 2) / Real.sqrt ε) ^ (1 / r0) - 1)),
        Muon.Foundations.oneSidedConv
          (fun w => Cpq (α + ς) (α / 2) * (1 + w / D) ^ (-r0)) g u
          ≤ 2 * (Cpq (α + ς) (α / 2) * (1 + u / D) ^ (-r0))) :
    ∃ (N1 : ℕ) (E1 cL cH K : ℝ) (Bd : ℕ → ℝ → ℝ), 4 ≤ N1 ∧ 0 < cL ∧ 0 < cH ∧ 0 ≤ K ∧
      (∀ δ : ℝ, 0 < δ → ∃ (N2 : ℕ) (ε2 : ℝ), 0 < ε2 ∧ ∀ (N : ℕ) (ε : ℝ), N2 ≤ N → 0 < ε →
        ε < ε2 → Bd N ε ≤ δ) ∧
      ∀ (N B : ℕ) (ε : ℝ) (mS mG : RowModel (Fin N)) (QS QG : ℝ → ℝ), N1 ≤ N → N ≤ B →
        0 < ε → ε < clockEps0 (α + ς) (α / 2) T → E1 ≤ ε * (N : ℝ) →
        IsMatchedModel (svdArrays α ς N B) mS ε → IsVolterraSol mS QS →
        IsMatchedModel (sgdArrays α ς N B) mG ε → IsVolterraSol mG QG →
        (dimHit QS (svdT0 N B) T ε ≠ ⊤ → stepHit mS QS T ε = ENNReal.ofReal
          (mS.S * svdT0 N B / (2 * Real.sqrt ε) *
            ∫ u in (0:ℝ)..(dimHit QS (svdT0 N B) T ε).toReal,
              Real.sqrt (QS (svdT0 N B * u)))) →
        dimHit QS (svdT0 N B) T ε ≠ ⊤ ∧
        SandwichE cL cH ((svdArrays α ς N B).S * svdT0 N B *
          phasePi (rq (α + ς) (α / 2)) ε) (stepHit mS QS T ε) ∧
        ∃ I : ℝ, 0 < I ∧ stepHit mS QS T ε = ENNReal.ofReal
            ((svdArrays α ς N B).S * svdT0 N B / (2 * Real.sqrt ε) * I) ∧
          (rq (α + ς) (α / 2) = 1 → |I - aQ (α / 2) / 2 * Real.log (1 / ε)| ≤ K) ∧
          (1 < rq (α + ς) (α / 2) → 1 / (2 * Real.sqrt 2) ≤ I ∧ |I - Jpq (α + ς) (α / 2)| ≤ Bd N ε) := by
  have hα0 : 0 < α := by linarith
  have hp : 1 < α + ς := by linarith
  have hq : 1 / 2 < α / 2 := by linarith
  obtain ⟨N1, E1, a, b, K, Bd, hN1, hN01, hE1, ha, hb, hK, hsm, hgen⟩ :=
    pw_genB (D := D) (r0 := r0) hp hq hT hD hr0 hr02 hr0r hr1 hgt N0 hN0
  refine ⟨N1, E1, a, b, K, Bd, hN1, ha, hb, hK, hsm, ?_⟩
  intro N B ε mS mG QS QG hN hNB hε hε0 hE hmS hQS hmG hQG hstep
  have hN4 : 4 ≤ N := le_trans hN1 hN
  have hN1' : 1 ≤ N := by omega
  have hN0' : (0:ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hB0 : (0:ℝ) < B := by exact_mod_cast (by omega : 0 < B)
  have hT0 : 0 < svdT0 N B := by
    unfold svdT0 gammaRat; exact Real.sqrt_pos.2 (by positivity)
  have hS : 0 < mS.S := by
    rw [pw_S_eq α ς N _ mS ε hmS]
    obtain ⟨h1, -⟩ := prop_app_phase_prefactors_i α ς N B hα0 hp hN1' hNB ε hε
    rw [h1]
    have h2 : 0 < Real.sqrt (gammaRat N B) := Real.sqrt_pos.2 (by unfold gammaRat; positivity)
    have h3 := pw_Hsum_ge_one (α / 2) N hN1'
    positivity
  obtain ⟨hgc, hgn, hgi, hgm, hgk, hYe⟩ := pw_svd_facts α ς N B hα0 hp hN1' hNB ε hε mS mG hmS hmG QS QG hQS hQG
  obtain ⟨hYc, hYp⟩ := pw_Q_facts mS QS hQS _ hT0
  have key := hgen N ε mS.S (svdT0 N B) mS QS (dimKernel mS (svdT0 N B) ε) hN hε hε0 hE hS hT0
    hgc hgn hgi hgm hYc hYp hYe
    (fun hH => hprov N (le_trans hN01 hN) ε hε hε0 (hE1 ▸ hE) hH _ hgc hgn hgi hgm hgk) hstep
  rw [pw_S_eq α ς N _ mS ε hmS] at key
  exact key

lemma pw_sgd_facts2 (α ς : ℝ) (N B : ℕ) (hα : 0 < α) (hp : 1 < α + ς)
    (hN : 1 ≤ N) (hNB : N ≤ B) (ε : ℝ) (hε : 0 < ε) (mS mG : RowModel (Fin N))
    (hmS : IsMatchedModel (svdArrays α ς N B) mS ε)
    (hmG : IsMatchedModel (sgdArrays α ς N B) mG ε)
    (QS QG : ℝ → ℝ) (hQS : IsVolterraSol mS QS) (hQG : IsVolterraSol mG QG) :
    ContinuousOn (dimKernel mG (sgdT0 α N B) ε) (Ici 0) ∧
    (∀ u ∈ Ici (0:ℝ), 0 ≤ dimKernel mG (sgdT0 α N B) ε u) ∧
    IntegrableOn (dimKernel mG (sgdT0 α N B) ε) (Ioi 0) ∧
    ∫ u in Ioi (0:ℝ), dimKernel mG (sgdT0 α N B) ε u ≤ 1 ∧
    (∀ u ∈ Ici (0:ℝ), dimKernel mG (sgdT0 α N B) ε u =
      2 * (1 - 2 / Real.pi) / (N : ℝ) * Lsum (N : ℕ∞) α α u
          + 4 / (Real.pi * Hsum α N) * Lsum (N : ℕ∞) (2 * α) α u) ∧
    (∀ u ∈ Ici (0:ℝ), QG (sgdT0 α N B * u) = fNq (N : ℕ∞) (α + ς) α u +
        Real.sqrt ε * Muon.Foundations.oneSidedConv (fun v => Real.sqrt (QG (sgdT0 α N B * v)))
          (dimKernel mG (sgdT0 α N B) ε) u) := by
  obtain ⟨hgc, hgn, -, hgi, hgm, hYe⟩ := pw_sgd_facts α ς N B hα hp hN hNB ε hε mS mG hmS hmG QS QG hQS hQG
  obtain ⟨-, -, -, -, -, hK⟩ := prop_app_phase_prefactors_ii α ς N B hα hp hN hNB ε hε mS mG hmS hmG QS QG hQS hQG
  exact ⟨hgc, hgn, hgi, hgm, fun u hu => hK u hu, hYe⟩

lemma pw_sgdB_gen (α ς T D r0 : ℝ) (N0 : ℕ) (hα : 1 < α) (hς : 1 ≤ ς) (hT : 4 ≤ T)
    (hD : 1 ≤ D) (hr0 : 1 ≤ r0) (hr02 : r0 < 2) (hr0r : r0 ≤ rq (α + ς) α)
    (hr1 : 1 ≤ rq (α + ς) α)
    (hgt : 1 < rq (α + ς) α → 1 < r0) (hN0 : 4 ≤ N0)
    (hprov : ∀ N : ℕ, N0 ≤ N → ∀ ε : ℝ, 0 < ε → ε < clockEps0 (α + ς) α T →
      Cpq (α + ς) α ^ 2 * D ^ (2 * r0) ≤ ε * (N : ℝ) →
      D * (Cpq (α + ς) α / Real.sqrt ε) ^ (1 / r0) ≤ Real.sqrt (N : ℝ) →
      ∀ g : ℝ → ℝ, ContinuousOn g (Ici 0) → (∀ u ∈ Ici (0:ℝ), 0 ≤ g u) →
      IntegrableOn g (Ioi 0) → ∫ u in Ioi (0:ℝ), g u ≤ 1 →
      (∀ u ∈ Ici (0:ℝ), g u = 2 * (1 - 2 / Real.pi) / (N : ℝ) * Lsum (N : ℕ∞) α α u
          + 4 / (Real.pi * Hsum α N) * Lsum (N : ℕ∞) (2 * α) α u) →
      ∀ u ∈ Icc (0:ℝ) (D * ((Cpq (α + ς) α / Real.sqrt ε) ^ (1 / r0) - 1)),
        Muon.Foundations.oneSidedConv
          (fun w => Cpq (α + ς) α * (1 + w / D) ^ (-r0)) g u
          ≤ 2 * (Cpq (α + ς) α * (1 + u / D) ^ (-r0))) :
    ∃ (N1 : ℕ) (E1 cL cH K : ℝ) (Bd : ℕ → ℝ → ℝ), 4 ≤ N1 ∧ 0 < cL ∧ 0 < cH ∧ 0 ≤ K ∧
      (∀ δ : ℝ, 0 < δ → ∃ (N2 : ℕ) (ε2 : ℝ), 0 < ε2 ∧ ∀ (N : ℕ) (ε : ℝ), N2 ≤ N → 0 < ε →
        ε < ε2 → Bd N ε ≤ δ) ∧
      ∀ (N B : ℕ) (ε : ℝ) (mS mG : RowModel (Fin N)) (QS QG : ℝ → ℝ), N1 ≤ N → N ≤ B →
        0 < ε → ε < clockEps0 (α + ς) α T → E1 ≤ ε * (N : ℝ) →
        IsMatchedModel (svdArrays α ς N B) mS ε → IsVolterraSol mS QS →
        IsMatchedModel (sgdArrays α ς N B) mG ε → IsVolterraSol mG QG →
        (dimHit QG (sgdT0 α N B) T ε ≠ ⊤ → stepHit mG QG T ε = ENNReal.ofReal
          (mG.S * sgdT0 α N B / (2 * Real.sqrt ε) *
            ∫ u in (0:ℝ)..(dimHit QG (sgdT0 α N B) T ε).toReal,
              Real.sqrt (QG (sgdT0 α N B * u)))) →
        dimHit QG (sgdT0 α N B) T ε ≠ ⊤ ∧
        SandwichE cL cH ((sgdArrays α ς N B).S * sgdT0 α N B *
          phasePi (rq (α + ς) α) ε) (stepHit mG QG T ε) ∧
        ∃ I : ℝ, 0 < I ∧ stepHit mG QG T ε = ENNReal.ofReal
            ((sgdArrays α ς N B).S * sgdT0 α N B / (2 * Real.sqrt ε) * I) ∧
          (rq (α + ς) α = 1 → |I - aQ α / 2 * Real.log (1 / ε)| ≤ K) ∧
          (1 < rq (α + ς) α → 1 / (2 * Real.sqrt 2) ≤ I ∧ |I - Jpq (α + ς) α| ≤ Bd N ε) := by
  have hα0 : 0 < α := by linarith
  have hp : 1 < α + ς := by linarith
  have hq : 1 / 2 < α := by linarith
  obtain ⟨N1, E1, a, b, K, Bd, hN1, hN01, hE1, ha, hb, hK, hsm, hgen⟩ :=
    pw_genB (D := D) (r0 := r0) hp hq hT hD hr0 hr02 hr0r hr1 hgt N0 hN0
  refine ⟨N1, E1, a, b, K, Bd, hN1, ha, hb, hK, hsm, ?_⟩
  intro N B ε mS mG QS QG hN hNB hε hε0 hE hmS hQS hmG hQG hstep
  have hN4 : 4 ≤ N := le_trans hN1 hN
  have hN1' : 1 ≤ N := by omega
  have hN0' : (0:ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hB0 : (0:ℝ) < B := by exact_mod_cast (by omega : 0 < B)
  have hmuB := pw_muBar_pos α hN1'
  have hT0 : 0 < sgdT0 α N B := by
    unfold sgdT0; exact Real.sqrt_pos.2 (by positivity)
  have hS : 0 < mG.S := by
    rw [pw_S_eq α ς N _ mG ε hmG]
    obtain ⟨-, -, h3, -⟩ := prop_app_phase_prefactors_i α ς N B hα0 hp hN1' hNB ε hε
    rw [h3]
    have : 0 < Real.sqrt (Real.pi * muBarOf α N / (B : ℝ)) := Real.sqrt_pos.2 (by positivity)
    positivity
  obtain ⟨hgc, hgn, hgi, hgm, hgk, hYe⟩ := pw_sgd_facts2 α ς N B hα0 hp hN1' hNB ε hε mS mG hmS hmG QS QG hQS hQG
  obtain ⟨hYc, hYp⟩ := pw_Q_facts mG QG hQG _ hT0
  have key := hgen N ε mG.S (sgdT0 α N B) mG QG (dimKernel mG (sgdT0 α N B) ε) hN hε hε0 hE hS hT0
    hgc hgn hgi hgm hYc hYp hYe
    (fun hH => hprov N (le_trans hN01 hN) ε hε hε0 (hE1 ▸ hE) hH _ hgc hgn hgi hgm hgk) hstep
  rw [pw_S_eq α ς N _ mG ε hmG] at key
  exact key

lemma pw_hit_eq {Y : ℝ → ℝ} {a û : ℝ} (hYc : ContinuousOn Y (Ici 0))
    (hhit : firstHit Y a = ENNReal.ofReal û) (hû0 : 0 < û) : Y û = a := by
  have hcont : ContinuousAt Y û := hYc.continuousAt (Ici_mem_nhds hû0)
  have hlow : ∀ t : ℝ≥0, Y (t : ℝ) ≤ a → û ≤ (t : ℝ) := by
    intro t ht
    have h : ENNReal.ofReal û ≤ (t : ℝ≥0∞) := by
      rw [← hhit]
      unfold firstHit
      exact iInf₂_le t ht
    rw [← ENNReal.ofReal_coe_nnreal] at h
    exact (ENNReal.ofReal_le_ofReal_iff t.2).1 h
  have hupp : ∀ δ : ℝ, 0 < δ → ∃ t : ℝ≥0, Y (t : ℝ) ≤ a ∧ (t : ℝ) < û + δ := by
    intro δ hδ
    have hlt : firstHit Y a < ENNReal.ofReal (û + δ) := by
      rw [hhit]
      exact (ENNReal.ofReal_lt_ofReal_iff (by linarith)).2 (by linarith)
    unfold firstHit at hlt
    obtain ⟨t, ht⟩ := iInf_lt_iff.1 hlt
    obtain ⟨h1, h2⟩ := iInf_lt_iff.1 ht
    refine ⟨t, h1, ?_⟩
    rw [← ENNReal.ofReal_coe_nnreal] at h2
    exact (ENNReal.ofReal_lt_ofReal_iff (by linarith)).1 h2
  apply le_antisymm
  · by_contra hcon
    push_neg at hcon
    -- Y û > a
    have hev : ∀ᶠ x in 𝓝 û, a < Y x := hcont.eventually (lt_mem_nhds hcon)
    obtain ⟨δ, hδ, hδb⟩ := Metric.eventually_nhds_iff.1 hev
    obtain ⟨t, ht1, ht2⟩ := hupp (δ / 2) (by positivity)
    have h3 := hlow t ht1
    have : dist (t : ℝ) û < δ := by
      rw [Real.dist_eq, abs_lt]; constructor <;> linarith
    have := hδb this
    linarith
  · by_contra hcon
    push_neg at hcon
    have hev : ∀ᶠ x in 𝓝 û, Y x < a := hcont.eventually (gt_mem_nhds hcon)
    obtain ⟨δ, hδ, hδb⟩ := Metric.eventually_nhds_iff.1 hev
    set s : ℝ := max 0 (û - δ / 2) with hs
    have hs0 : 0 ≤ s := le_max_left _ _
    have hsû : s < û := max_lt hû0 (by linarith)
    have hsd : dist s û < δ := by
      rw [Real.dist_eq, abs_lt]
      constructor
      · have : û - δ / 2 ≤ s := le_max_right _ _
        linarith
      · linarith
    have hYs := hδb hsd
    have := hlow ⟨s, hs0⟩ hYs.le
    change û ≤ s at this
    linarith

lemma pw_horizonN {C D r0 ε N : ℝ} (hC : 0 < C) (hD : 0 < D) (hr0 : 1 / 2 ≤ r0) (hε : 0 < ε)
    (hN : 1 ≤ N) (hE : C ^ 2 * D ^ (2 * r0) ≤ ε * N) :
    D * (C / Real.sqrt ε) ^ (1 / r0) ≤ N := by
  have hs : 0 < Real.sqrt ε := Real.sqrt_pos.2 hε
  have hr : 0 < r0 := by linarith
  set X := D * (C / Real.sqrt ε) ^ (1 / r0) with hX
  have hXp : 0 < X := by positivity
  have h1 : X ^ (2 * r0) = D ^ (2 * r0) * (C ^ 2 / ε) := by
    rw [hX, Real.mul_rpow hD.le (by positivity), ← Real.rpow_mul (by positivity)]
    have : 1 / r0 * (2 * r0) = 2 := by field_simp
    rw [this, Real.div_rpow hC.le hs.le]
    have h2 : (C ^ (2:ℝ)) = C ^ 2 := by norm_cast
    have h3 : (Real.sqrt ε) ^ (2:ℝ) = ε := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hε.le]; norm_num
    rw [h2, h3]
  have h2 : X ^ (2 * r0) ≤ N := by
    rw [h1]
    have : D ^ (2 * r0) * (C ^ 2 / ε) = C ^ 2 * D ^ (2 * r0) / ε := by ring
    rw [this, div_le_iff₀ hε]
    linarith
  have h3 : X ≤ N ^ (1 / (2 * r0)) := by
    calc X = (X ^ (2 * r0)) ^ (1 / (2 * r0)) := by
          rw [← Real.rpow_mul hXp.le]; field_simp; simp
      _ ≤ N ^ (1 / (2 * r0)) := Real.rpow_le_rpow (by positivity) h2 (by positivity)
  refine h3.trans ?_
  calc (N:ℝ) ^ (1 / (2 * r0)) ≤ (N:ℝ) ^ (1:ℝ) := by
        apply Real.rpow_le_rpow_of_exponent_le hN
        rw [div_le_one (by positivity)]; linarith
    _ = N := Real.rpow_one _

lemma pw_errlog_le {C A0 r ε L : ℝ} (hC : 0 < C) (hA0 : 0 ≤ A0) (hr : 1 < r) (hε : 0 < ε)
    (hL : 1 ≤ L) :
    ε ^ (1 / 8 : ℝ) * Real.sqrt (C + Real.sqrt A0 + 1)
      + C / (r - 1) * (1 + ε ^ (-(1 / 8 : ℝ))) ^ (1 - r)
      + 2 * Real.sqrt A0 * (2 * C) ^ (1 / (2 * r)) * L ^ (-(1 / 2 : ℝ)) * ε ^ ((r - 1) / (4 * r))
      + (2 * C) ^ (1 / r) * ε ^ ((r - 1) / (2 * r)) + 8 * A0 / L
    ≤ (ε ^ (1 / 8 : ℝ) * Real.sqrt (C + Real.sqrt A0 + 1)
      + C / (r - 1) * ε ^ ((r - 1) / 8)
      + 2 * Real.sqrt A0 * (2 * C) ^ (1 / (2 * r)) * ε ^ ((r - 1) / (4 * r))
      + (2 * C) ^ (1 / r) * ε ^ ((r - 1) / (2 * r))) + 8 * A0 / L := by
  have hr0 : 0 < r := by linarith
  have hx : 0 < ε ^ (-(1 / 8 : ℝ)) := Real.rpow_pos_of_pos hε _
  have h2 : (1 + ε ^ (-(1 / 8 : ℝ))) ^ (1 - r) ≤ ε ^ ((r - 1) / 8) := by
    calc (1 + ε ^ (-(1 / 8 : ℝ))) ^ (1 - r) ≤ (ε ^ (-(1 / 8 : ℝ))) ^ (1 - r) :=
          Real.rpow_le_rpow_of_nonpos hx (by linarith) (by linarith)
      _ = ε ^ ((r - 1) / 8) := by
          rw [← Real.rpow_mul hε.le]; congr 1; ring
  have hL0 : 0 < L := by linarith
  have h3 : L ^ (-(1 / 2 : ℝ)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hL (by norm_num)
  have hAs : 0 ≤ Real.sqrt A0 := Real.sqrt_nonneg _
  have hcoef : 0 ≤ 2 * Real.sqrt A0 * (2 * C) ^ (1 / (2 * r)) * ε ^ ((r - 1) / (4 * r)) := by positivity
  have h4 : 2 * Real.sqrt A0 * (2 * C) ^ (1 / (2 * r)) * L ^ (-(1 / 2 : ℝ)) * ε ^ ((r - 1) / (4 * r))
      ≤ 2 * Real.sqrt A0 * (2 * C) ^ (1 / (2 * r)) * ε ^ ((r - 1) / (4 * r)) := by
    have : 2 * Real.sqrt A0 * (2 * C) ^ (1 / (2 * r)) * L ^ (-(1 / 2 : ℝ)) * ε ^ ((r - 1) / (4 * r))
        = (2 * Real.sqrt A0 * (2 * C) ^ (1 / (2 * r)) * ε ^ ((r - 1) / (4 * r))) * L ^ (-(1 / 2 : ℝ)) := by ring
    rw [this]
    calc _ ≤ (2 * Real.sqrt A0 * (2 * C) ^ (1 / (2 * r)) * ε ^ ((r - 1) / (4 * r))) * 1 :=
          mul_le_mul_of_nonneg_left h3 hcoef
      _ = _ := mul_one _
  have h5 : C / (r - 1) * (1 + ε ^ (-(1 / 8 : ℝ))) ^ (1 - r) ≤ C / (r - 1) * ε ^ ((r - 1) / 8) :=
    mul_le_mul_of_nonneg_left h2 (div_nonneg hC.le (by linarith))
  linarith

lemma pw_errlog_G_le {C A0 r ε : ℝ} (hC : 0 < C) (hA0 : 0 ≤ A0) (hr : 1 < r)
    (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ε ^ (1 / 8 : ℝ) * Real.sqrt (C + Real.sqrt A0 + 1)
      + C / (r - 1) * ε ^ ((r - 1) / 8)
      + 2 * Real.sqrt A0 * (2 * C) ^ (1 / (2 * r)) * ε ^ ((r - 1) / (4 * r))
      + (2 * C) ^ (1 / r) * ε ^ ((r - 1) / (2 * r))
    ≤ Real.sqrt (C + Real.sqrt A0 + 1) + C / (r - 1)
      + 2 * Real.sqrt A0 * (2 * C) ^ (1 / (2 * r)) + (2 * C) ^ (1 / r) := by
  have hr0 : 0 < r := by linarith
  have e1 : ε ^ (1 / 8 : ℝ) ≤ 1 := Real.rpow_le_one hε.le hε1 (by norm_num)
  have e2 : ε ^ ((r - 1) / 8) ≤ 1 := Real.rpow_le_one hε.le hε1 (by apply div_nonneg <;> linarith)
  have e3 : ε ^ ((r - 1) / (4 * r)) ≤ 1 := Real.rpow_le_one hε.le hε1 (by apply div_nonneg <;> linarith)
  have e4 : ε ^ ((r - 1) / (2 * r)) ≤ 1 := Real.rpow_le_one hε.le hε1 (by apply div_nonneg <;> linarith)
  have hAs : 0 ≤ Real.sqrt A0 := Real.sqrt_nonneg _
  have c1 : 0 ≤ Real.sqrt (C + Real.sqrt A0 + 1) := Real.sqrt_nonneg _
  have c2 : 0 ≤ C / (r - 1) := div_nonneg hC.le (by linarith)
  have c3 : 0 ≤ 2 * Real.sqrt A0 * (2 * C) ^ (1 / (2 * r)) := by positivity
  have c4 : 0 ≤ (2 * C) ^ (1 / r) := by positivity
  nlinarith [mul_le_mul_of_nonneg_left e1 c1, mul_le_mul_of_nonneg_left e2 c2,
    mul_le_mul_of_nonneg_left e3 c3, mul_le_mul_of_nonneg_left e4 c4]

lemma pw_tend_rpow (c κ : ℝ) (hκ : 0 < κ) :
    Tendsto (fun ε : ℝ => c * ε ^ κ) (𝓝[>] 0) (𝓝 0) := by
  have h : Tendsto (fun ε : ℝ => c * ε ^ κ) (𝓝 0) (𝓝 (c * (0:ℝ) ^ κ)) :=
    ((Real.continuousAt_rpow_const 0 κ (Or.inr hκ.le)).tendsto).const_mul c
  rw [Real.zero_rpow hκ.ne', mul_zero] at h
  exact tendsto_nhdsWithin_of_tendsto_nhds h

lemma pw_G_small {C A0 r : ℝ} (hr : 1 < r) :
    ∀ δ : ℝ, 0 < δ → ∃ ε2 : ℝ, 0 < ε2 ∧ ∀ ε : ℝ, 0 < ε → ε < ε2 →
      ε ^ (1 / 8 : ℝ) * Real.sqrt (C + Real.sqrt A0 + 1)
        + C / (r - 1) * ε ^ ((r - 1) / 8)
        + 2 * Real.sqrt A0 * (2 * C) ^ (1 / (2 * r)) * ε ^ ((r - 1) / (4 * r))
        + (2 * C) ^ (1 / r) * ε ^ ((r - 1) / (2 * r)) ≤ δ := by
  intro δ hδ
  have hr0 : 0 < r := by linarith
  have t1 := pw_tend_rpow (Real.sqrt (C + Real.sqrt A0 + 1)) (1 / 8) (by norm_num)
  have t2 := pw_tend_rpow (C / (r - 1)) ((r - 1) / 8) (by linarith)
  have t3 := pw_tend_rpow (2 * Real.sqrt A0 * (2 * C) ^ (1 / (2 * r))) ((r - 1) / (4 * r))
    (by apply div_pos <;> linarith)
  have t4 := pw_tend_rpow ((2 * C) ^ (1 / r)) ((r - 1) / (2 * r)) (by apply div_pos <;> linarith)
  have hsum := ((t1.add t2).add t3).add t4
  simp only [add_zero] at hsum
  have hev := (tendsto_order.1 hsum).2 δ hδ
  obtain ⟨u, hu, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 hev
  refine ⟨u, hu, fun ε hε hεu => ?_⟩
  have := hsub ⟨hε, hεu⟩
  simp only [Set.mem_setOf_eq] at this
  have e : ε ^ (1 / 8 : ℝ) * Real.sqrt (C + Real.sqrt A0 + 1) = Real.sqrt (C + Real.sqrt A0 + 1) * ε ^ (1 / 8 : ℝ) := mul_comm _ _
  have e2 : C / (r - 1) * ε ^ ((r - 1) / 8) = C / (r - 1) * ε ^ ((r - 1) / 8) := rfl
  have e3 : 2 * Real.sqrt A0 * (2 * C) ^ (1 / (2 * r)) * ε ^ ((r - 1) / (4 * r)) = 2 * Real.sqrt A0 * (2 * C) ^ (1 / (2 * r)) * ε ^ ((r - 1) / (4 * r)) := rfl
  linarith

lemma pw_L_small (A0 : ℝ) :
    ∀ δ : ℝ, 0 < δ → ∃ N2 : ℕ, 1 ≤ N2 ∧ ∀ N : ℕ, N2 ≤ N → 8 * A0 / Hsum 1 N ≤ δ := by
  intro δ hδ
  refine ⟨⌈Real.exp (8 * A0 / δ)⌉₊ + 1, by omega, fun N hN => ?_⟩
  have hN1 : 1 ≤ N := by omega
  have hN0 : (0:ℝ) < N := by exact_mod_cast hN1
  have hexp : Real.exp (8 * A0 / δ) ≤ N := by
    have h1 := Nat.le_ceil (Real.exp (8 * A0 / δ))
    have h2 : ((⌈Real.exp (8 * A0 / δ)⌉₊ + 1 : ℕ) : ℝ) ≤ N := by exact_mod_cast hN
    push_cast at h2
    linarith
  have hlog : 8 * A0 / δ ≤ Real.log N := by
    rw [← Real.log_exp (8 * A0 / δ)]
    exact Real.log_le_log (Real.exp_pos _) hexp
  have hlogN : Real.log (N:ℝ) ≤ Real.log ((N:ℝ) + 1) := Real.log_le_log hN0 (by linarith)
  have hH := pw_log_le_H N hN1
  have hHpos : 0 < Hsum 1 N := by have := pw_Hsum_ge_one 1 N hN1; linarith
  rw [div_le_iff₀ hHpos]
  rw [div_le_iff₀ hδ] at hlog
  nlinarith

lemma pw_logA0_nonneg {ς : ℝ} (hς : 1 < ς) : 0 ≤ logGlobalA0 ς := by
  have hp : 1 < 2 + ς := by linarith
  have hC := pw_Cpq_pos hp (one_pos : (0:ℝ) < 1)
  have hE := pw_Epq_pos (p := 2) (q := 1) (by norm_num) one_pos
  have hr : 1 < rq (2 + ς) 1 := by unfold rq; rw [lt_div_iff₀ (by norm_num)]; linarith
  unfold logGlobalA0
  have : 0 < rq (2 + ς) 1 - 1 := by linarith
  positivity

lemma pw_errb_le {ς : ℝ} (hς : 1 < ς) (N : ℕ) (hN : 1 ≤ N) {ε : ℝ} (hε : 0 < ε) :
    logGlobalErrBound N ς ε ≤
      (ε ^ (1 / 8 : ℝ) * Real.sqrt (Cpq (2 + ς) 1 + Real.sqrt (logGlobalA0 ς) + 1)
      + Cpq (2 + ς) 1 / (rq (2 + ς) 1 - 1) * ε ^ ((rq (2 + ς) 1 - 1) / 8)
      + 2 * Real.sqrt (logGlobalA0 ς) * (2 * Cpq (2 + ς) 1) ^ (1 / (2 * rq (2 + ς) 1)) *
          ε ^ ((rq (2 + ς) 1 - 1) / (4 * rq (2 + ς) 1))
      + (2 * Cpq (2 + ς) 1) ^ (1 / rq (2 + ς) 1) * ε ^ ((rq (2 + ς) 1 - 1) / (2 * rq (2 + ς) 1)))
      + 8 * logGlobalA0 ς / Hsum 1 N := by
  have hp : 1 < 2 + ς := by linarith
  have hC := pw_Cpq_pos hp (one_pos : (0:ℝ) < 1)
  have hr : 1 < rq (2 + ς) 1 := by unfold rq; rw [lt_div_iff₀ (by norm_num)]; linarith
  unfold logGlobalErrBound
  dsimp only
  exact pw_errlog_le hC (pw_logA0_nonneg hς) hr hε (pw_Hsum_ge_one 1 N hN)

lemma pw_svdB_gt2 (α ς T : ℝ) (hα : 2 < α) (hς : 1 ≤ ς) (hT : 4 ≤ T) :
    ∃ (N1 : ℕ) (E1 cL cH K : ℝ) (Bd : ℕ → ℝ → ℝ), 4 ≤ N1 ∧ 0 < cL ∧ 0 < cH ∧ 0 ≤ K ∧
      (∀ δ : ℝ, 0 < δ → ∃ (N2 : ℕ) (ε2 : ℝ), 0 < ε2 ∧ ∀ (N : ℕ) (ε : ℝ), N2 ≤ N → 0 < ε →
        ε < ε2 → Bd N ε ≤ δ) ∧
      ∀ (N B : ℕ) (ε : ℝ) (mS mG : RowModel (Fin N)) (QS QG : ℝ → ℝ), N1 ≤ N → N ≤ B →
        0 < ε → ε < clockEps0 (α + ς) (α / 2) T → E1 ≤ ε * (N : ℝ) →
        IsMatchedModel (svdArrays α ς N B) mS ε → IsVolterraSol mS QS →
        IsMatchedModel (sgdArrays α ς N B) mG ε → IsVolterraSol mG QG →
        (dimHit QS (svdT0 N B) T ε ≠ ⊤ → stepHit mS QS T ε = ENNReal.ofReal
          (mS.S * svdT0 N B / (2 * Real.sqrt ε) *
            ∫ u in (0:ℝ)..(dimHit QS (svdT0 N B) T ε).toReal,
              Real.sqrt (QS (svdT0 N B * u)))) →
        dimHit QS (svdT0 N B) T ε ≠ ⊤ ∧
        SandwichE cL cH ((svdArrays α ς N B).S * svdT0 N B *
          phasePi (rq (α + ς) (α / 2)) ε) (stepHit mS QS T ε) ∧
        ∃ I : ℝ, 0 < I ∧ stepHit mS QS T ε = ENNReal.ofReal
            ((svdArrays α ς N B).S * svdT0 N B / (2 * Real.sqrt ε) * I) ∧
          (rq (α + ς) (α / 2) = 1 → |I - aQ (α / 2) / 2 * Real.log (1 / ε)| ≤ K) ∧
          (1 < rq (α + ς) (α / 2) → 1 / (2 * Real.sqrt 2) ≤ I ∧ |I - Jpq (α + ς) (α / 2)| ≤ Bd N ε) := by
  have hα0 : 0 < α := by linarith
  have hp : 1 < α + ς := by linarith
  have hq : 0 < α / 2 := by linarith
  have hr1 : 1 ≤ rq (α + ς) (α / 2) := by
    unfold rq
    rw [le_div_iff₀ (by linarith)]
    linarith
  have hυ : 1 < 2 - 2 / α := by
    have : 2 / α < 1 := by rw [div_lt_one hα0]; exact hα
    linarith
  have hpos2α : 0 < 2 / α := by positivity
  have hK : 0 < 2 * Epq α (α / 2) := by
    have := pw_Epq_pos (p := α) (q := α / 2) (by linarith) hq; positivity
  set r := rq (α + ς) (α / 2) with hr_def
  set r0 : ℝ := if r = 1 then 1 else min r ((1 + (2 - 2 / α)) / 2) with hr0_def
  have hr0facts : 1 ≤ r0 ∧ r0 < 2 ∧ r0 ≤ r ∧ (1 < r → 1 < r0) ∧ r0 ≤ 2 - 2 / α := by
    by_cases h : r = 1
    · rw [hr0_def, if_pos h]
      refine ⟨le_rfl, by norm_num, h.ge, fun h' => by linarith, by linarith⟩
    · have h1 : 1 < r := lt_of_le_of_ne hr1 (Ne.symm h)
      rw [hr0_def, if_neg h]
      refine ⟨le_min h1.le (by linarith), ?_, min_le_left _ _, fun _ => lt_min h1 (by linarith), ?_⟩
      · exact lt_of_le_of_lt (min_le_right _ _) (by linarith)
      · exact (min_le_right _ _).trans (by linarith)
  obtain ⟨hr0a, hr0b, hr0c, hr0d, hr0e⟩ := hr0facts
  have hD1 : 1 ≤ dilScale (2 * Epq α (α / 2)) r0 (2 - 2 / α) := le_max_left _ _
  refine pw_svdB_gen α ς T (dilScale (2 * Epq α (α / 2)) r0 (2 - 2 / α)) r0 4 (by linarith) hς hT hD1
    hr0a hr0b hr0c hr1 hr0d le_rfl ?_
  intro N hN ε hε hε0 hE hH g hgc hgn hgi hgm hgk u hu
  have hN1 : 1 ≤ N := by omega
  set Hh := dilScale (2 * Epq α (α / 2)) r0 (2 - 2 / α) * ((Cpq (α + ς) (α / 2) / Real.sqrt ε) ^ (1 / r0) - 1) with hHh
  have hbound : ∀ v ∈ Icc (0:ℝ) (max Hh 1), g v ≤ 2 * Epq α (α / 2) * (1 + v) ^ (-(2 - 2 / α)) := by
    intro v hv
    have hv0 : 0 ≤ v := hv.1
    rw [hgk v (Set.mem_Ici.2 hv0)]
    unfold svdKernel
    have h1 := lem_app_phase_sums_i (a := α) (q := α / 2) (by linarith) hq (N : ℕ∞) hv0
    have hd : dAQ α (α / 2) = 2 - 2 / α := by unfold dAQ; field_simp
    rw [hd] at h1
    have hH := pw_Hsum_ge_one (α / 2) N hN1
    have hL := pw_Lsum_nonneg N α (α / 2) v
    have hpow : 0 ≤ Epq α (α / 2) * (1 + v) ^ (-(2 - 2 / α)) := by
      have := pw_Epq_pos (p := α) (q := α / 2) (by linarith) hq
      have := Real.rpow_nonneg (show (0:ℝ) ≤ 1 + v by linarith) (-(2 - 2 / α))
      positivity
    have : 2 / Hsum (α / 2) N ≤ 2 := by
      rw [div_le_iff₀ (by linarith)]; nlinarith
    calc 2 / Hsum (α / 2) N * Lsum (N : ℕ∞) α (α / 2) v ≤ 2 * (Epq α (α / 2) * (1 + v) ^ (-(2 - 2 / α))) :=
          mul_le_mul this h1 hL (by norm_num)
      _ = _ := by ring
  have hC := pw_Cpq_pos hp hq
  have hr0pos : 0 < r0 := by linarith
  have hdil := (lem_app_phase_dilation g hgc hgn hgi hgm (2 * Epq α (α / 2)) (2 - 2 / α) (max Hh 1)
    r0 (Cpq (α + ς) (α / 2)) hK hυ (by positivity) hr0pos hr0e hC hbound)
  have hu' : u ∈ Icc (0:ℝ) (max Hh 1) := ⟨hu.1, hu.2.trans (le_max_left _ _)⟩
  have hD : 0 < dilScale (2 * Epq α (α / 2)) r0 (2 - 2 / α) := by linarith
  have hh : 0 < Cpq (α + ς) (α / 2) * (1 + u / dilScale (2 * Epq α (α / 2)) r0 (2 - 2 / α)) ^ (-r0) := by
    have := Real.rpow_pos_of_pos (show (0:ℝ) < 1 + u / dilScale (2 * Epq α (α / 2)) r0 (2 - 2 / α) by
      have : 0 ≤ u / dilScale (2 * Epq α (α / 2)) r0 (2 - 2 / α) := div_nonneg hu.1 hD.le
      linarith) (-r0)
    positivity
  exact (div_le_iff₀ hh).1 ((hdil.1 u hu').trans hdil.2)

lemma pw_svdB_lt2 (α ς T : ℝ) (hα1 : 1 < α) (hα2 : α < 2) (hς : 1 ≤ ς) (hT : 4 ≤ T) :
    ∃ (N1 : ℕ) (E1 cL cH K : ℝ) (Bd : ℕ → ℝ → ℝ), 4 ≤ N1 ∧ 0 < cL ∧ 0 < cH ∧ 0 ≤ K ∧
      (∀ δ : ℝ, 0 < δ → ∃ (N2 : ℕ) (ε2 : ℝ), 0 < ε2 ∧ ∀ (N : ℕ) (ε : ℝ), N2 ≤ N → 0 < ε →
        ε < ε2 → Bd N ε ≤ δ) ∧
      ∀ (N B : ℕ) (ε : ℝ) (mS mG : RowModel (Fin N)) (QS QG : ℝ → ℝ), N1 ≤ N → N ≤ B →
        0 < ε → ε < clockEps0 (α + ς) (α / 2) T → E1 ≤ ε * (N : ℝ) →
        IsMatchedModel (svdArrays α ς N B) mS ε → IsVolterraSol mS QS →
        IsMatchedModel (sgdArrays α ς N B) mG ε → IsVolterraSol mG QG →
        (dimHit QS (svdT0 N B) T ε ≠ ⊤ → stepHit mS QS T ε = ENNReal.ofReal
          (mS.S * svdT0 N B / (2 * Real.sqrt ε) *
            ∫ u in (0:ℝ)..(dimHit QS (svdT0 N B) T ε).toReal,
              Real.sqrt (QS (svdT0 N B * u)))) →
        dimHit QS (svdT0 N B) T ε ≠ ⊤ ∧
        SandwichE cL cH ((svdArrays α ς N B).S * svdT0 N B *
          phasePi (rq (α + ς) (α / 2)) ε) (stepHit mS QS T ε) ∧
        ∃ I : ℝ, 0 < I ∧ stepHit mS QS T ε = ENNReal.ofReal
            ((svdArrays α ς N B).S * svdT0 N B / (2 * Real.sqrt ε) * I) ∧
          (rq (α + ς) (α / 2) = 1 → |I - aQ (α / 2) / 2 * Real.log (1 / ε)| ≤ K) ∧
          (1 < rq (α + ς) (α / 2) → 1 / (2 * Real.sqrt 2) ≤ I ∧ |I - Jpq (α + ς) (α / 2)| ≤ Bd N ε) := by
  have hα0 : 0 < α := by linarith
  have hp : 1 < α + ς := by linarith
  have hq : 0 < α / 2 := by linarith
  have hr1 : 1 ≤ rq (α + ς) (α / 2) := by
    unfold rq
    rw [le_div_iff₀ (by linarith)]
    linarith
  have h2α : 1 < 2 / α := by rw [lt_div_iff₀ hα0]; linarith
  have h2α' : 2 / α < 2 := by rw [div_lt_iff₀ hα0]; linarith
  have hr0facts : 1 ≤ svdMainR0 α ς ∧ svdMainR0 α ς < 2 ∧ svdMainR0 α ς ≤ rq (α + ς) (α / 2) ∧
      (1 < rq (α + ς) (α / 2) → 1 < svdMainR0 α ς) := by
    unfold svdMainR0
    by_cases h : rq (α + ς) (α / 2) = 1
    · rw [if_pos h]
      exact ⟨le_rfl, by norm_num, h.ge, fun h' => by linarith⟩
    · have h1 : 1 < rq (α + ς) (α / 2) := lt_of_le_of_ne hr1 (Ne.symm h)
      rw [if_neg h]
      refine ⟨le_min h1.le (by linarith), ?_, min_le_left _ _, fun _ => lt_min h1 (by linarith)⟩
      exact lt_of_le_of_lt (min_le_right _ _) (by linarith)
  obtain ⟨hr0a, hr0b, hr0c, hr0d⟩ := hr0facts
  refine pw_svdB_gen α ς T 1 (svdMainR0 α ς) (max 4 (svdMainNV α ς)) hα1 hς hT le_rfl
    hr0a hr0b hr0c hr1 hr0d (le_max_left _ _) ?_
  intro N hN ε hε hε0 hE hH g hgc hgn hgi hgm hgk u hu
  have hεC := (pw_eps_facts ε hε0).2
  have hEN : Cpq (α + ς) (α / 2) ^ 2 ≤ ε * (N : ℝ) := by
    simpa using hE
  have hsm := (lem_app_phase_svd_main α ς hα1 hα2 hς N (le_trans (le_max_right _ _) hN) ε hε hεC hEN).2.2
    u (by simpa [phaseHeight] using hu)
  rw [pw_conv_congr _ g (svdKernel α N) hgk hu.1]
  simpa using hsm

lemma pw_svdB_eq2a (α ς T : ℝ) (hα : α = 2) (hς : ς = 1) (hT : 4 ≤ T) :
    ∃ (N1 : ℕ) (E1 cL cH K : ℝ) (Bd : ℕ → ℝ → ℝ), 4 ≤ N1 ∧ 0 < cL ∧ 0 < cH ∧ 0 ≤ K ∧
      (∀ δ : ℝ, 0 < δ → ∃ (N2 : ℕ) (ε2 : ℝ), 0 < ε2 ∧ ∀ (N : ℕ) (ε : ℝ), N2 ≤ N → 0 < ε →
        ε < ε2 → Bd N ε ≤ δ) ∧
      ∀ (N B : ℕ) (ε : ℝ) (mS mG : RowModel (Fin N)) (QS QG : ℝ → ℝ), N1 ≤ N → N ≤ B →
        0 < ε → ε < clockEps0 (α + ς) (α / 2) T → E1 ≤ ε * (N : ℝ) →
        IsMatchedModel (svdArrays α ς N B) mS ε → IsVolterraSol mS QS →
        IsMatchedModel (sgdArrays α ς N B) mG ε → IsVolterraSol mG QG →
        (dimHit QS (svdT0 N B) T ε ≠ ⊤ → stepHit mS QS T ε = ENNReal.ofReal
          (mS.S * svdT0 N B / (2 * Real.sqrt ε) *
            ∫ u in (0:ℝ)..(dimHit QS (svdT0 N B) T ε).toReal,
              Real.sqrt (QS (svdT0 N B * u)))) →
        dimHit QS (svdT0 N B) T ε ≠ ⊤ ∧
        SandwichE cL cH ((svdArrays α ς N B).S * svdT0 N B *
          phasePi (rq (α + ς) (α / 2)) ε) (stepHit mS QS T ε) ∧
        ∃ I : ℝ, 0 < I ∧ stepHit mS QS T ε = ENNReal.ofReal
            ((svdArrays α ς N B).S * svdT0 N B / (2 * Real.sqrt ε) * I) ∧
          (rq (α + ς) (α / 2) = 1 → |I - aQ (α / 2) / 2 * Real.log (1 / ε)| ≤ K) ∧
          (1 < rq (α + ς) (α / 2) → 1 / (2 * Real.sqrt 2) ≤ I ∧ |I - Jpq (α + ς) (α / 2)| ≤ Bd N ε) := by
  subst hα
  subst hς
  have hp : 1 < 2 + (1:ℝ) := by norm_num
  have hq : 0 < (2:ℝ) / 2 := by norm_num
  have hr1 : rq (2 + 1) (2 / 2) = 1 := by unfold rq; norm_num
  have hC := pw_Cpq_pos hp hq
  refine pw_svdB_gen 2 1 T 1 1 (max 4 ⌈Real.exp 64⌉₊) (by norm_num) le_rfl hT le_rfl
    le_rfl (by norm_num) hr1.ge hr1.ge (fun h => absurd h (by rw [hr1]; exact lt_irrefl _))
    (le_max_left _ _) ?_
  intro N hN ε hε hε0 hE hH g hgc hgn hgi hgm hgk u hu
  have hN4 : 4 ≤ N := le_trans (le_max_left _ _) hN
  have hN1 : 1 ≤ N := by omega
  have hN0 : (0:ℝ) < N := by exact_mod_cast hN1
  have hexp : Real.exp 64 ≤ N :=
    (Nat.le_ceil _).trans (by exact_mod_cast le_trans (le_max_right _ _) hN)
  have h64 : (64:ℝ) ≤ Real.log N := by
    rw [← Real.log_exp 64]
    exact Real.log_le_log (Real.exp_pos _) hexp
  have hu0 : 0 ≤ u := hu.1
  have hu1 : 1 + u ≤ Real.sqrt N := by
    have := hu.2
    simp only [div_one, Real.rpow_one, one_mul] at this hH
    linarith
  have hsq : (1 + u) ^ 2 ≤ (N:ℝ) := by
    have h0 : 0 ≤ 1 + u := by linarith
    calc (1 + u) ^ 2 ≤ (Real.sqrt N) ^ 2 := pow_le_pow_left₀ h0 hu1 2
      _ = N := Real.sq_sqrt hN0.le
  have hlog1 : 2 * Real.log (1 + u) ≤ Real.log N := by
    have := Real.log_le_log (by positivity) hsq
    rw [Real.log_pow] at this
    push_cast at this
    linarith
  have hlogN : Real.log (N:ℝ) ≤ Real.log ((N:ℝ) + 1) :=
    Real.log_le_log hN0 (by linarith)
  have hH1 := pw_log_le_H N hN1
  have hHpos : 0 < Hsum 1 N := by have := pw_Hsum_ge_one 1 N hN1; linarith
  have hlog := lem_app_phase_log_iii N hN1 (Cpq (2 + 1) (2 / 2)) hC u hu0
  have hh : 0 < Cpq (2 + 1) (2 / 2) * (1 + u) ^ (-(1:ℝ)) := by
    have := Real.rpow_pos_of_pos (show (0:ℝ) < 1 + u by linarith) (-(1:ℝ))
    positivity
  have hfrac : (2 * Real.log (1 + u) + 64) / Hsum 1 N ≤ 2 := by
    rw [div_le_iff₀ hHpos]; linarith
  rw [pw_conv_congr _ g (svdKernel 2 N) hgk hu0]
  simp only [div_one, Real.rpow_one, one_mul] at hlog ⊢
  rw [div_le_iff₀ (by simpa using hh)] at hlog
  have := (hlog.trans (mul_le_mul_of_nonneg_right hfrac (by simpa using hh.le)))
  simpa using this

lemma pw_svdB_logg0 (α ς T : ℝ) (hα : α = 2) (hς : 1 < ς) (hT : 4 ≤ T) :
    ∃ (N1 : ℕ) (cL cH K : ℝ) (Bd : ℕ → ℝ → ℝ), 4 ≤ N1 ∧ 0 < cL ∧ 0 < cH ∧ 0 ≤ K ∧
      (∀ δ : ℝ, 0 < δ → ∃ (N2 : ℕ) (ε2 : ℝ), 0 < ε2 ∧ ∀ (N : ℕ) (ε : ℝ), N2 ≤ N → 0 < ε →
        ε < ε2 → Bd N ε ≤ δ) ∧
      ∀ (N B : ℕ) (ε : ℝ) (mS mG : RowModel (Fin N)) (QS QG : ℝ → ℝ), N1 ≤ N → N ≤ B →
        0 < ε → ε < clockEps0 (α + ς) (α / 2) T →
        IsMatchedModel (svdArrays α ς N B) mS ε → IsVolterraSol mS QS →
        IsMatchedModel (sgdArrays α ς N B) mG ε → IsVolterraSol mG QG →
        (dimHit QS (svdT0 N B) T ε ≠ ⊤ → stepHit mS QS T ε = ENNReal.ofReal
          (mS.S * svdT0 N B / (2 * Real.sqrt ε) *
            ∫ u in (0:ℝ)..(dimHit QS (svdT0 N B) T ε).toReal,
              Real.sqrt (QS (svdT0 N B * u)))) →
        dimHit QS (svdT0 N B) T ε ≠ ⊤ ∧
        SandwichE cL cH ((svdArrays α ς N B).S * svdT0 N B *
          phasePi (rq (α + ς) (α / 2)) ε) (stepHit mS QS T ε) ∧
        ∃ I : ℝ, 0 < I ∧ stepHit mS QS T ε = ENNReal.ofReal
            ((svdArrays α ς N B).S * svdT0 N B / (2 * Real.sqrt ε) * I) ∧
          (rq (α + ς) (α / 2) = 1 → |I - aQ (α / 2) / 2 * Real.log (1 / ε)| ≤ K) ∧
          (1 < rq (α + ς) (α / 2) → 1 / (2 * Real.sqrt 2) ≤ I ∧ |I - Jpq (α + ς) (α / 2)| ≤ Bd N ε) := by
  subst hα
  have e : (2:ℝ) / 2 = 1 := by norm_num
  simp only [e]
  have hp : 1 < 2 + ς := by linarith
  have hq : (0:ℝ) < 1 := one_pos
  have hr1 : 1 < rq (2 + ς) 1 := by unfold rq; rw [lt_div_iff₀ (by norm_num)]; linarith
  have hC := pw_Cpq_pos hp hq
  have hA0 := pw_logA0_nonneg hς
  have hr0 : 0 < rq (2 + ς) 1 - 1 := by linarith
  set C := Cpq (2 + ς) 1 with hC_def
  set r := rq (2 + ς) 1 with hr_def
  set A0 := logGlobalA0 ς with hA0_def
  set G1 : ℝ := Real.sqrt (C + Real.sqrt A0 + 1) + C / (r - 1)
      + 2 * Real.sqrt A0 * (2 * C) ^ (1 / (2 * r)) + (2 * C) ^ (1 / r) + 8 * A0 with hG1
  have hG1nn : 0 ≤ G1 := by positivity
  refine ⟨max 4 ⌈Real.exp logGlobalL0⌉₊, 1 / (4 * Real.sqrt 2),
    (|Jpq (2 + ς) 1| + G1 + 1) / 2, 0,
    fun N ε => (1 / Real.sqrt (2 * ((2 + ς) - 1)) + C / (r - 1)) * (N : ℝ) ^ (-(1 * (r - 1)))
        + C / (r - 1) * (1 + 1 / 2 * Real.log (1 / (2 * T * ε))) ^ (1 - r)
        + logGlobalErrBound N ς ε,
    le_max_left _ _, by positivity, by positivity, le_rfl, ?_, ?_⟩
  · -- smallness
    intro δ hδ
    have hd2 : 0 < δ / 2 := by positivity
    have hd4 : 0 < δ / 4 := by positivity
    obtain ⟨N2, ε2, hε2, hbd⟩ := pw_Bd_small (r := r) (κ1 := 1 * (r - 1)) (κ := 1) (T := T)
      (c1 := 1 / Real.sqrt (2 * ((2 + ς) - 1)) + C / (r - 1)) (c2 := C / (r - 1)) (c3 := 0)
      hr1 (by linarith) one_pos (by linarith) (δ / 2) hd2
    obtain ⟨ε3, hε3, hG⟩ := pw_G_small (C := C) (A0 := A0) hr1 (δ / 4) hd4
    obtain ⟨N3, hN3, hL⟩ := pw_L_small A0 (δ / 4) hd4
    refine ⟨max N2 N3, min ε2 ε3, lt_min hε2 hε3, fun N ε hN hε hεu => ?_⟩
    have h1 := hbd N ε (le_trans (le_max_left _ _) hN) hε (lt_of_lt_of_le hεu (min_le_left _ _))
    have h2 := hG ε hε (lt_of_lt_of_le hεu (min_le_right _ _))
    have h3 := hL N (le_trans (le_max_right _ _) hN)
    have h4 := pw_errb_le hς N (le_trans hN3 (le_trans (le_max_right _ _) hN)) hε
    simp only [zero_mul, add_zero] at h1
    show _ + _ + logGlobalErrBound N ς ε ≤ δ
    linarith
  · intro N B ε mS mG QS QG hN hNB hε hε0 hmS hQS hmG hQG hstep
    have hα0 : (0:ℝ) < 2 := by norm_num
    have hN4 : 4 ≤ N := le_trans (le_max_left _ _) hN
    have hN1' : 1 ≤ N := by omega
    have hN0' : (0:ℝ) < N := by exact_mod_cast hN1'
    have hB0 : (0:ℝ) < B := by exact_mod_cast (by omega : 0 < B)
    have hexp : Real.exp logGlobalL0 ≤ (N : ℝ) :=
      (Nat.le_ceil _).trans (by exact_mod_cast le_trans (le_max_right _ _) hN)
    obtain ⟨hε8, hεC⟩ := pw_eps_facts ε hε0
    have hε4 := pw_eps_lt_quarter hε0
    have hεT : ε < min 1 (min (Cpq (2 + ς) 1 ^ 2) (1 / (8 * T))) :=
      lt_min (by linarith) (lt_min hεC hε8)
    have hT0 : 0 < svdT0 N B := by
      unfold svdT0 gammaRat; exact Real.sqrt_pos.2 (by positivity)
    have hS : 0 < mS.S := by
      rw [pw_S_eq 2 ς N _ mS ε hmS]
      obtain ⟨h1, -⟩ := prop_app_phase_prefactors_i 2 ς N B hα0 hp hN1' hNB ε hε
      rw [h1]
      have h2 : 0 < Real.sqrt (gammaRat N B) := Real.sqrt_pos.2 (by unfold gammaRat; positivity)
      have h3 := pw_Hsum_ge_one (2 / 2) N hN1'
      positivity
    obtain ⟨hgc, hgn, hgi, hgm, hgk, hYe⟩ := pw_svd_facts 2 ς N B hα0 hp hN1' hNB ε hε mS mG hmS hmG QS QG hQS hQG
    obtain ⟨hYc, hYp⟩ := pw_Q_facts mS QS hQS _ hT0
    have gi := lem_app_phase_log_global_i ς hς N B hexp hNB ε hε mS hmS QS hQS
    obtain ⟨gpos, gle, gE0, gE1⟩ := lem_app_phase_log_global_ii ς hς N B hexp hNB T ε hT hε hεT mS hmS QS hQS
    have hne : firstHit (fun u => QS (svdT0 N B * u)) (T * ε) ≠ ⊤ :=
      ne_top_of_le_ne_top ENNReal.ofReal_ne_top gle
    set û := (firstHit (fun u => QS (svdT0 N B * u)) (T * ε)).toReal with hû
    have hhit : firstHit (fun u => QS (svdT0 N B * u)) (T * ε) = ENNReal.ofReal û :=
      (ENNReal.ofReal_toReal hne).symm
    have hû0 : 0 < û := by
      rw [hhit] at gpos
      exact ENNReal.ofReal_pos.1 gpos
    have hYf : ∀ u ∈ Ici (0:ℝ), fNq (N:ℕ∞) (2 + ς) 1 u ≤ QS (svdT0 N B * u) :=
      fun u hu => (gi u hu).1
    have hT0' : 0 < T := by linarith
    have hf0 : T * ε < QS (svdT0 N B * 0) := by
      have h1 := hYf 0 (Set.mem_Ici.2 le_rfl)
      rw [pw_fNq_zero] at h1
      have := pw_Hsum_ge_one (2 + ς) N hN1'
      have h2 : T * ε < 1 / 8 := by
        have := mul_lt_mul_of_pos_left hε8 hT0'
        rw [mul_one_div, mul_comm 8 T, ← div_div, div_self hT0'.ne'] at this
        linarith
      linarith
    have hYû : QS (svdT0 N B * û) = T * ε := by
      refine pw_hit_eq (Y := fun u => QS (svdT0 N B * u)) hYc hhit hû0
    have hdim : dimHit QS (svdT0 N B) T ε = ENNReal.ofReal û := hhit
    have hdne : dimHit QS (svdT0 N B) T ε ≠ ⊤ := by rw [hdim]; exact ENNReal.ofReal_ne_top
    have hst := hstep hdne
    rw [hdim, ENNReal.toReal_ofReal hû0.le] at hst
    rw [pw_S_eq 2 ς N _ mS ε hmS] at hst
    obtain ⟨h1, h2, h3⟩ := lem_app_phase_clock_integral_iii (p := 2 + ς) (q := 1) (T := T) (ε := ε)
      (H := û) (û := û) hp hq hT N hN4 hε (by simpa using hε0) hYc hYf
      (Y := fun u => QS (svdT0 N B * u)) hhit hû0 hYû le_rfl hr1
    beta_reduce at h1 h2 h3
    have hEdef : phaseErr (fun u => QS (svdT0 N B * u)) (fNq (N : ℕ∞) (2 + ς) 1) û =
        ∫ u in (0 : ℝ)..û, (Real.sqrt (QS (svdT0 N B * u)) - Real.sqrt (fNq (N : ℕ∞) (2 + ς) 1 u)) := rfl
    have gE1' : ∫ u in (0 : ℝ)..û, (Real.sqrt (QS (svdT0 N B * u)) - Real.sqrt (fNq (N : ℕ∞) (2 + ς) 1 u))
        ≤ logGlobalErrBound N ς ε := by rw [← hEdef]; exact gE1
    have hbd := pw_errb_le hς N hN1' hε
    have hGle := pw_errlog_G_le (C := C) (A0 := A0) (r := r) hC hA0 hr1 hε (by linarith : ε ≤ 1)
    have hLge : 8 * A0 / Hsum 1 N ≤ 8 * A0 := by
      have := pw_Hsum_ge_one 1 N hN1'
      rw [div_le_iff₀ (by linarith)]
      nlinarith
    have hEG : logGlobalErrBound N ς ε ≤ G1 := by
      rw [hG1]; linarith
    refine ⟨hdne, ?_, _, ?_, hst, fun h => absurd h (ne_of_gt hr1), fun _ => ⟨h1, ?_⟩⟩
    · have hs2 : 0 < Real.sqrt 2 := by positivity
      have hPi : phasePi r ε = ε ^ (-(1 / 2 : ℝ)) := by
        unfold phasePi
        rw [if_neg (by linarith), if_neg (by linarith)]
      have hS' : 0 < (svdArrays 2 ς N B).S := by rw [← pw_S_eq 2 ς N _ mS ε hmS]; exact hS
      have hPpos := Real.rpow_pos_of_pos hε (-(1 / 2 : ℝ))
      have hP : 2 * Real.sqrt ε * ε ^ (-(1 / 2 : ℝ)) = 2 := by
        rw [Real.sqrt_eq_rpow, mul_assoc, ← Real.rpow_add hε]
        norm_num
      rw [hPi]
      refine pw_sandI hS' hT0 hPpos hε (by positivity) hst ?_ ?_
      · rw [hP]
        have : 1 / (4 * Real.sqrt 2) * 2 = 1 / (2 * Real.sqrt 2) := by field_simp; ring
        rw [this]; exact h1
      · rw [hP]
        have := le_abs_self (Jpq (2 + ς) 1)
        linarith
    · exact lt_of_lt_of_le (by positivity) h1
    · refine h3.trans ?_
      show _ ≤ (_ + _ + logGlobalErrBound N ς ε)
      linarith

lemma pw_svdB_logg (α ς T : ℝ) (hα : α = 2) (hς : 1 < ς) (hT : 4 ≤ T) :
    ∃ (N1 : ℕ) (E1 cL cH K : ℝ) (Bd : ℕ → ℝ → ℝ), 4 ≤ N1 ∧ 0 < cL ∧ 0 < cH ∧ 0 ≤ K ∧
      (∀ δ : ℝ, 0 < δ → ∃ (N2 : ℕ) (ε2 : ℝ), 0 < ε2 ∧ ∀ (N : ℕ) (ε : ℝ), N2 ≤ N → 0 < ε →
        ε < ε2 → Bd N ε ≤ δ) ∧
      ∀ (N B : ℕ) (ε : ℝ) (mS mG : RowModel (Fin N)) (QS QG : ℝ → ℝ), N1 ≤ N → N ≤ B →
        0 < ε → ε < clockEps0 (α + ς) (α / 2) T → E1 ≤ ε * (N : ℝ) →
        IsMatchedModel (svdArrays α ς N B) mS ε → IsVolterraSol mS QS →
        IsMatchedModel (sgdArrays α ς N B) mG ε → IsVolterraSol mG QG →
        (dimHit QS (svdT0 N B) T ε ≠ ⊤ → stepHit mS QS T ε = ENNReal.ofReal
          (mS.S * svdT0 N B / (2 * Real.sqrt ε) *
            ∫ u in (0:ℝ)..(dimHit QS (svdT0 N B) T ε).toReal,
              Real.sqrt (QS (svdT0 N B * u)))) →
        dimHit QS (svdT0 N B) T ε ≠ ⊤ ∧
        SandwichE cL cH ((svdArrays α ς N B).S * svdT0 N B *
          phasePi (rq (α + ς) (α / 2)) ε) (stepHit mS QS T ε) ∧
        ∃ I : ℝ, 0 < I ∧ stepHit mS QS T ε = ENNReal.ofReal
            ((svdArrays α ς N B).S * svdT0 N B / (2 * Real.sqrt ε) * I) ∧
          (rq (α + ς) (α / 2) = 1 → |I - aQ (α / 2) / 2 * Real.log (1 / ε)| ≤ K) ∧
          (1 < rq (α + ς) (α / 2) → 1 / (2 * Real.sqrt 2) ≤ I ∧ |I - Jpq (α + ς) (α / 2)| ≤ Bd N ε) := by
  obtain ⟨N1, cL, cH, K, Bd, h4, hcL, hcH, hK, hsm, h⟩ := pw_svdB_logg0 α ς T hα hς hT
  refine ⟨N1, 0, cL, cH, K, Bd, h4, hcL, hcH, hK, hsm, ?_⟩
  intro N B ε mS mG QS QG hN hNB hε hε0 _ hmS hQS hmG hQG hstep
  exact h N B ε mS mG QS QG hN hNB hε hε0 hmS hQS hmG hQG hstep

lemma pw_sgd_kbound {α : ℝ} (hα : 1 < α) (N : ℕ) (hN : 1 ≤ N) {v : ℝ} (hv0 : 0 ≤ v)
    (hvN : v ≤ N) :
    2 * (1 - 2 / Real.pi) / (N : ℝ) * Lsum (N : ℕ∞) α α v
        + 4 / (Real.pi * Hsum α N) * Lsum (N : ℕ∞) (2 * α) α v
      ≤ (4 * (1 - 2 / Real.pi) * Epq α α + 4 / Real.pi * Epq (2 * α) α) * (1 + v) ^ (-(2 - 1 / α)) := by
  have hα0 : 0 < α := by linarith
  have hN0 : (0:ℝ) < N := by exact_mod_cast hN
  have hpi : 2 < Real.pi := by linarith [Real.pi_gt_three]
  have hc : 0 < 1 - 2 / Real.pi := by
    have : 2 / Real.pi < 1 := by rw [div_lt_one Real.pi_pos]; exact hpi
    linarith
  have h1 := lem_app_phase_sums_i (a := α) (q := α) hα hα0 (N : ℕ∞) hv0
  have h2 := lem_app_phase_sums_i (a := 2 * α) (q := α) (by linarith) hα0 (N : ℕ∞) hv0
  have hd1 : dAQ α α = 1 - 1 / α := by unfold dAQ; field_simp
  have hd2 : dAQ (2 * α) α = 2 - 1 / α := by unfold dAQ; field_simp
  rw [hd1] at h1
  rw [hd2] at h2
  have hE1 := pw_Epq_pos (p := α) (q := α) hα hα0
  have hE2 := pw_Epq_pos (p := 2 * α) (q := α) (by linarith) hα0
  have hL1 := pw_Lsum_nonneg N α α v
  have hL2 := pw_Lsum_nonneg N (2 * α) α v
  have hH := pw_Hsum_ge_one α N hN
  have hb : 0 < 1 + v := by linarith
  -- (1+v)^{-(1-1/α)} = (1+v) * (1+v)^{-(2-1/α)}
  have hsplit : (1 + v) ^ (-(1 - 1 / α)) = (1 + v) * (1 + v) ^ (-(2 - 1 / α)) := by
    conv_lhs => rw [show -(1 - 1 / α) = 1 + -(2 - 1 / α) by ring]
    rw [Real.rpow_add hb, Real.rpow_one]
  have hpow : 0 < (1 + v) ^ (-(2 - 1 / α)) := Real.rpow_pos_of_pos hb _
  have hvN' : (1 + v) / N ≤ 2 := by
    rw [div_le_iff₀ hN0]
    have : (1:ℝ) ≤ N := by exact_mod_cast hN
    linarith
  have t1 : 2 * (1 - 2 / Real.pi) / (N : ℝ) * Lsum (N : ℕ∞) α α v
      ≤ 4 * (1 - 2 / Real.pi) * Epq α α * (1 + v) ^ (-(2 - 1 / α)) := by
    have : 2 * (1 - 2 / Real.pi) / (N : ℝ) * Lsum (N : ℕ∞) α α v
        ≤ 2 * (1 - 2 / Real.pi) / (N : ℝ) * (Epq α α * (1 + v) ^ (-(1 - 1 / α))) :=
      mul_le_mul_of_nonneg_left h1 (by positivity)
    refine this.trans ?_
    rw [hsplit]
    have e : 2 * (1 - 2 / Real.pi) / (N : ℝ) * (Epq α α * ((1 + v) * (1 + v) ^ (-(2 - 1 / α))))
        = 2 * (1 - 2 / Real.pi) * Epq α α * ((1 + v) / N) * (1 + v) ^ (-(2 - 1 / α)) := by
      field_simp
    rw [e]
    have : 0 ≤ 2 * (1 - 2 / Real.pi) * Epq α α * (1 + v) ^ (-(2 - 1 / α)) := by positivity
    nlinarith
  have t2 : 4 / (Real.pi * Hsum α N) * Lsum (N : ℕ∞) (2 * α) α v
      ≤ 4 / Real.pi * Epq (2 * α) α * (1 + v) ^ (-(2 - 1 / α)) := by
    have h3 : 4 / (Real.pi * Hsum α N) ≤ 4 / Real.pi := by
      apply div_le_div_of_nonneg_left (by norm_num) Real.pi_pos
      nlinarith [Real.pi_pos]
    calc 4 / (Real.pi * Hsum α N) * Lsum (N : ℕ∞) (2 * α) α v
        ≤ 4 / Real.pi * (Epq (2 * α) α * (1 + v) ^ (-(2 - 1 / α))) :=
          mul_le_mul h3 h2 hL2 (by positivity)
      _ = _ := by ring
  linarith

lemma pw_sgdB_ge1 (α ς T : ℝ) (hα : 1 < α) (hς : 1 ≤ ς) (hT : 4 ≤ T)
    (hr1 : 1 ≤ rq (α + ς) α) :
    ∃ (N1 : ℕ) (E1 cL cH K : ℝ) (Bd : ℕ → ℝ → ℝ), 4 ≤ N1 ∧ 0 < cL ∧ 0 < cH ∧ 0 ≤ K ∧
      (∀ δ : ℝ, 0 < δ → ∃ (N2 : ℕ) (ε2 : ℝ), 0 < ε2 ∧ ∀ (N : ℕ) (ε : ℝ), N2 ≤ N → 0 < ε →
        ε < ε2 → Bd N ε ≤ δ) ∧
      ∀ (N B : ℕ) (ε : ℝ) (mS mG : RowModel (Fin N)) (QS QG : ℝ → ℝ), N1 ≤ N → N ≤ B →
        0 < ε → ε < clockEps0 (α + ς) α T → E1 ≤ ε * (N : ℝ) →
        IsMatchedModel (svdArrays α ς N B) mS ε → IsVolterraSol mS QS →
        IsMatchedModel (sgdArrays α ς N B) mG ε → IsVolterraSol mG QG →
        (dimHit QG (sgdT0 α N B) T ε ≠ ⊤ → stepHit mG QG T ε = ENNReal.ofReal
          (mG.S * sgdT0 α N B / (2 * Real.sqrt ε) *
            ∫ u in (0:ℝ)..(dimHit QG (sgdT0 α N B) T ε).toReal,
              Real.sqrt (QG (sgdT0 α N B * u)))) →
        dimHit QG (sgdT0 α N B) T ε ≠ ⊤ ∧
        SandwichE cL cH ((sgdArrays α ς N B).S * sgdT0 α N B *
          phasePi (rq (α + ς) α) ε) (stepHit mG QG T ε) ∧
        ∃ I : ℝ, 0 < I ∧ stepHit mG QG T ε = ENNReal.ofReal
            ((sgdArrays α ς N B).S * sgdT0 α N B / (2 * Real.sqrt ε) * I) ∧
          (rq (α + ς) α = 1 → |I - aQ α / 2 * Real.log (1 / ε)| ≤ K) ∧
          (1 < rq (α + ς) α → 1 / (2 * Real.sqrt 2) ≤ I ∧ |I - Jpq (α + ς) α| ≤ Bd N ε) := by
  have hα0 : 0 < α := by linarith
  have hp : 1 < α + ς := by linarith
  have hυ : 1 < 2 - 1 / α := by
    have : 1 / α < 1 := by rw [div_lt_one hα0]; exact hα
    linarith
  have hυ2 : 2 - 1 / α < 2 := by have : 0 < 1 / α := by positivity
                                 linarith
  have hKG : 0 < 4 * (1 - 2 / Real.pi) * Epq α α + 4 / Real.pi * Epq (2 * α) α := by
    have hpi : 2 < Real.pi := by linarith [Real.pi_gt_three]
    have hc : 0 < 1 - 2 / Real.pi := by
      have : 2 / Real.pi < 1 := by rw [div_lt_one Real.pi_pos]; exact hpi
      linarith
    have := pw_Epq_pos (p := α) (q := α) hα hα0
    have := pw_Epq_pos (p := 2 * α) (q := α) (by linarith) hα0
    positivity
  set r := rq (α + ς) α with hr_def
  set KG : ℝ := 4 * (1 - 2 / Real.pi) * Epq α α + 4 / Real.pi * Epq (2 * α) α with hKG_def
  set r0 : ℝ := if r = 1 then 1 else min r ((1 + (2 - 1 / α)) / 2) with hr0_def
  have hr0facts : 1 ≤ r0 ∧ r0 < 2 ∧ r0 ≤ r ∧ (1 < r → 1 < r0) ∧ r0 ≤ 2 - 1 / α := by
    by_cases h : r = 1
    · rw [hr0_def, if_pos h]
      refine ⟨le_rfl, by norm_num, h.ge, fun h' => by linarith, by linarith⟩
    · have h1 : 1 < r := lt_of_le_of_ne hr1 (Ne.symm h)
      rw [hr0_def, if_neg h]
      refine ⟨le_min h1.le (by linarith), ?_, min_le_left _ _, fun _ => lt_min h1 (by linarith), ?_⟩
      · exact lt_of_le_of_lt (min_le_right _ _) (by linarith)
      · exact (min_le_right _ _).trans (by linarith)
  obtain ⟨hr0a, hr0b, hr0c, hr0d, hr0e⟩ := hr0facts
  have hD1 : 1 ≤ dilScale KG r0 (2 - 1 / α) := le_max_left _ _
  refine pw_sgdB_gen α ς T (dilScale KG r0 (2 - 1 / α)) r0 4 hα hς hT hD1
    hr0a hr0b hr0c hr1 hr0d le_rfl ?_
  intro N hN ε hε hε0 hE hH g hgc hgn hgi hgm hgk u hu
  have hN1 : 1 ≤ N := by omega
  have hN4 : (4:ℝ) ≤ N := by exact_mod_cast hN
  set Hh := dilScale KG r0 (2 - 1 / α) * ((Cpq (α + ς) α / Real.sqrt ε) ^ (1 / r0) - 1) with hHh
  have hD0 : 0 < dilScale KG r0 (2 - 1 / α) := by linarith
  have hHhN : Hh ≤ Real.sqrt N := by
    have : Hh ≤ dilScale KG r0 (2 - 1 / α) * (Cpq (α + ς) α / Real.sqrt ε) ^ (1 / r0) := by
      rw [hHh]; nlinarith [hD0]
    exact this.trans hH
  have hsqN : Real.sqrt N ≤ N := by
    rw [Real.sqrt_le_left (by positivity)]
    nlinarith
  have hbound : ∀ v ∈ Icc (0:ℝ) (max Hh 1), g v ≤ KG * (1 + v) ^ (-(2 - 1 / α)) := by
    intro v hv
    have hv0 : 0 ≤ v := hv.1
    have hvN : v ≤ N := hv.2.trans (max_le (hHhN.trans hsqN) (by linarith))
    rw [hgk v (Set.mem_Ici.2 hv0)]
    exact pw_sgd_kbound hα N hN1 hv0 hvN
  have hC := pw_Cpq_pos hp hα0
  have hr0pos : 0 < r0 := by linarith
  have hdil := (lem_app_phase_dilation g hgc hgn hgi hgm KG (2 - 1 / α) (max Hh 1)
    r0 (Cpq (α + ς) α) hKG hυ (by positivity) hr0pos hr0e hC hbound)
  have hu' : u ∈ Icc (0:ℝ) (max Hh 1) := ⟨hu.1, hu.2.trans (le_max_left _ _)⟩
  have hh : 0 < Cpq (α + ς) α * (1 + u / dilScale KG r0 (2 - 1 / α)) ^ (-r0) := by
    have := Real.rpow_pos_of_pos (show (0:ℝ) < 1 + u / dilScale KG r0 (2 - 1 / α) by
      have : 0 ≤ u / dilScale KG r0 (2 - 1 / α) := div_nonneg hu.1 hD0.le
      linarith) (-r0)
    positivity
  exact (div_le_iff₀ hh).1 ((hdil.1 u hu').trans hdil.2)

lemma pw_sgd_lt1 (α ς T : ℝ) (hα : 1 < α) (hς : 1 ≤ ς) (hr : rq (α + ς) α < 1)
    (hT : 4 ≤ T) :
    ∃ (N1 : ℕ) (E1 cL cH : ℝ), 4 ≤ N1 ∧ 0 < cL ∧ 0 < cH ∧
      ∀ (N B : ℕ) (ε : ℝ) (mS mG : RowModel (Fin N)) (QS QG : ℝ → ℝ), N1 ≤ N → N ≤ B →
        0 < ε → ε < clockEps0 (α + ς) α T → E1 ≤ ε * (N : ℝ) →
        IsMatchedModel (svdArrays α ς N B) mS ε → IsVolterraSol mS QS →
        IsMatchedModel (sgdArrays α ς N B) mG ε → IsVolterraSol mG QG →
        (dimHit QG (sgdT0 α N B) T ε ≠ ⊤ → stepHit mG QG T ε = ENNReal.ofReal
          (mG.S * sgdT0 α N B / (2 * Real.sqrt ε) *
            ∫ u in (0:ℝ)..(dimHit QG (sgdT0 α N B) T ε).toReal,
              Real.sqrt (QG (sgdT0 α N B * u)))) →
        dimHit QG (sgdT0 α N B) T ε ≠ ⊤ ∧
        SandwichE cL cH ((sgdArrays α ς N B).S * sgdT0 α N B *
          ε ^ (-(1 / (2 * rq (α + ς) α)))) (stepHit mG QG T ε) ∧
        ∃ I : ℝ, 0 < I ∧ stepHit mG QG T ε = ENNReal.ofReal
            ((sgdArrays α ς N B).S * sgdT0 α N B / (2 * Real.sqrt ε) * I) := by
  have hα0 : 0 < α := by linarith
  have hp : 1 < α + ς := by linarith
  have hr0 := pw_rq_pos hp hα0
  have hr12 : 1 / 2 ≤ rq (α + ς) α := by
    unfold rq
    rw [le_div_iff₀ (by linarith)]
    linarith
  have hυ : 1 < 2 - 1 / α := by
    have : 1 / α < 1 := by rw [div_lt_one hα0]; exact hα
    linarith
  have hKG : 0 < 4 * (1 - 2 / Real.pi) * Epq α α + 4 / Real.pi * Epq (2 * α) α := by
    have hpi : 2 < Real.pi := by linarith [Real.pi_gt_three]
    have hc : 0 < 1 - 2 / Real.pi := by
      have : 2 / Real.pi < 1 := by rw [div_lt_one Real.pi_pos]; exact hpi
      linarith
    have := pw_Epq_pos (p := α) (q := α) hα hα0
    have := pw_Epq_pos (p := 2 * α) (q := α) (by linarith) hα0
    positivity
  set KG : ℝ := 4 * (1 - 2 / Real.pi) * Epq α α + 4 / Real.pi * Epq (2 * α) α with hKG_def
  set r := rq (α + ς) α with hr_def
  set D : ℝ := dilScale KG r (2 - 1 / α) with hD_def
  have hD1 : 1 ≤ D := le_max_left _ _
  have hD0 : 0 < D := by linarith
  obtain ⟨cL, cH, hcL, hcH, hgen⟩ := pw_gen hp hα0 hT hD1 hr
  have hC := pw_Cpq_pos hp hα0
  set τ : ℝ := (4:ℝ) ^ (-α) with hτ_def
  have hτ : 0 < τ := Real.rpow_pos_of_pos (by norm_num) _
  refine ⟨4, max (Cpq (α + ς) α ^ 2 * (D / τ) ^ (2 * rq (α + ς) α)) (Cpq (α + ς) α ^ 2 * D ^ (2 * rq (α + ς) α)), cL, cH, le_refl _, hcL, hcH, ?_⟩
  intro N B ε mS mG QS QG hN hNB hε hε0 hE hmS hQS hmG hQG hstep
  have hN1 : 1 ≤ N := by omega
  have hN0 : (0:ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hmuB := pw_muBar_pos α hN1
  have hB0 : (0:ℝ) < B := by exact_mod_cast (by omega : 0 < B)
  have hT0 : 0 < sgdT0 α N B := by
    unfold sgdT0; exact Real.sqrt_pos.2 (by positivity)
  have hS : 0 < mG.S := by
    rw [pw_S_eq α ς N _ mG ε hmG]
    obtain ⟨-, -, h3, -⟩ := prop_app_phase_prefactors_i α ς N B hα0 hp hN1 hNB ε hε
    rw [h3]
    have : 0 < Real.sqrt (Real.pi * muBarOf α N / (B : ℝ)) := Real.sqrt_pos.2 (by positivity)
    positivity
  obtain ⟨hgc, hgn, hgi, hgm, hgk, hYe⟩ := pw_sgd_facts2 α ς N B hα0 hp hN1 hNB ε hε mS mG hmS hmG QS QG hQS hQG
  obtain ⟨hYc, hYp⟩ := pw_Q_facts mG QG hQG _ hT0
  have hHN : D * ((Cpq (α + ς) α / Real.sqrt ε) ^ (1 / rq (α + ς) α) - 1) ≤ ((N:ℝ) / 4) ^ α := by
    have h2 : (2 * α * rq (α + ς) α) = α + ς - 1 := by unfold rq; field_simp
    have := pw_horizon (C := Cpq (α + ς) α) (D := D) (τ := τ) (r := rq (α + ς) α) (q := α)
      (ε := ε) (E := Cpq (α + ς) α ^ 2 * (D / τ) ^ (2 * rq (α + ς) α)) (N := (N:ℝ)) hC hD0 hτ hr0 hα0 hε hN0
      le_rfl (by
        rw [h2]
        have hNp : (N:ℝ) ≤ (N:ℝ) ^ (α + ς - 1) :=
          Real.self_le_rpow_of_one_le (by exact_mod_cast hN1) (by linarith)
        have := mul_le_mul_of_nonneg_left hNp hε.le
        exact (le_trans (le_max_left _ _) hE).trans this)
    have h4 : τ * (N:ℝ) ^ α = ((N:ℝ) / 4) ^ α := by
      rw [Real.div_rpow hN0.le (by norm_num), hτ_def, Real.rpow_neg (by norm_num)]
      ring
    linarith
  have hconv : ∀ u ∈ Icc (0:ℝ) (D * ((Cpq (α + ς) α / Real.sqrt ε) ^ (1 / rq (α + ς) α) - 1)),
      Muon.Foundations.oneSidedConv (fun w => Cpq (α + ς) α * (1 + w / D) ^ (-rq (α + ς) α))
        (dimKernel mG (sgdT0 α N B) ε) u
          ≤ 2 * (Cpq (α + ς) α * (1 + u / D) ^ (-rq (α + ς) α)) := by
    intro u hu
    set Hh := D * ((Cpq (α + ς) α / Real.sqrt ε) ^ (1 / rq (α + ς) α) - 1) with hHh
    have hN4 : (4:ℝ) ≤ N := by exact_mod_cast hN
    have hHhN : Hh ≤ N := by
      have h1 := pw_horizonN hC hD0 hr12 hε (by exact_mod_cast hN1)
        (le_trans (le_max_right _ _) hE)
      have h2 : Hh ≤ D * (Cpq (α + ς) α / Real.sqrt ε) ^ (1 / rq (α + ς) α) := by
        rw [hHh]; nlinarith [hD0]
      exact h2.trans h1
    have hbound : ∀ v ∈ Icc (0:ℝ) (max Hh 1), dimKernel mG (sgdT0 α N B) ε v ≤ KG * (1 + v) ^ (-(2 - 1 / α)) := by
      intro v hv
      have hv0 : 0 ≤ v := hv.1
      have hvN : v ≤ N := hv.2.trans (max_le hHhN (by linarith))
      rw [hgk v (Set.mem_Ici.2 hv0)]
      exact pw_sgd_kbound hα N hN1 hv0 hvN
    have hdil := (lem_app_phase_dilation _ hgc hgn hgi hgm KG (2 - 1 / α) (max Hh 1)
      r (Cpq (α + ς) α) hKG hυ (by positivity) hr0 (by linarith) hC hbound)
    have hu' : u ∈ Icc (0:ℝ) (max Hh 1) := ⟨hu.1, hu.2.trans (le_max_left _ _)⟩
    have hh : 0 < Cpq (α + ς) α * (1 + u / D) ^ (-r) := by
      have := Real.rpow_pos_of_pos (show (0:ℝ) < 1 + u / D by
        have : 0 ≤ u / D := div_nonneg hu.1 hD0.le
        linarith) (-r)
      positivity
    exact (div_le_iff₀ hh).1 ((hdil.1 u hu').trans hdil.2)
  have key := hgen N ε mG.S (sgdT0 α N B) mG QG (dimKernel mG (sgdT0 α N B) ε) hN hε hε0 hS hT0
    hgc hgn hgi hgm hYc hYp hYe hconv hHN hstep
  rw [pw_S_eq α ς N _ mG ε hmG] at key
  obtain ⟨hne, hsand⟩ := key
  refine ⟨hne, hsand, ?_⟩
  have hst := hstep hne
  rw [pw_S_eq α ς N _ mG ε hmG] at hst
  refine ⟨_, ?_, hst⟩
  have hs : 0 < Real.sqrt ε := Real.sqrt_pos.2 hε
  have hS' : 0 < (sgdArrays α ς N B).S := by rw [← pw_S_eq α ς N _ mG ε hmG]; exact hS
  have hpre : 0 < (sgdArrays α ς N B).S * sgdT0 α N B / (2 * Real.sqrt ε) := by positivity
  have hX : 0 < (sgdArrays α ς N B).S * sgdT0 α N B * ε ^ (-(1 / (2 * rq (α + ς) α))) := by
    have := Real.rpow_pos_of_pos hε (-(1 / (2 * rq (α + ς) α))); positivity
  have hlow := hsand.1
  have hpos : 0 < stepHit mG QG T ε := by
    refine lt_of_lt_of_le ?_ hlow
    exact ENNReal.mul_pos (by simpa using hcL) (by simpa using hX)
  rw [hst] at hpos
  have := ENNReal.ofReal_pos.1 hpos
  exact (mul_pos_iff_of_pos_left hpre).1 this

lemma pw_svdB (α ς T : ℝ) (hα : 1 < α) (hς : 1 ≤ ς) (hT : 4 ≤ T) :
    ∃ (N1 : ℕ) (E1 cL cH K : ℝ) (Bd : ℕ → ℝ → ℝ), 4 ≤ N1 ∧ 0 < cL ∧ 0 < cH ∧ 0 ≤ K ∧
      (∀ δ : ℝ, 0 < δ → ∃ (N2 : ℕ) (ε2 : ℝ), 0 < ε2 ∧ ∀ (N : ℕ) (ε : ℝ), N2 ≤ N → 0 < ε →
        ε < ε2 → Bd N ε ≤ δ) ∧
      ∀ (N B : ℕ) (ε : ℝ) (mS mG : RowModel (Fin N)) (QS QG : ℝ → ℝ), N1 ≤ N → N ≤ B →
        0 < ε → ε < clockEps0 (α + ς) (α / 2) T → E1 ≤ ε * (N : ℝ) →
        IsMatchedModel (svdArrays α ς N B) mS ε → IsVolterraSol mS QS →
        IsMatchedModel (sgdArrays α ς N B) mG ε → IsVolterraSol mG QG →
        (dimHit QS (svdT0 N B) T ε ≠ ⊤ → stepHit mS QS T ε = ENNReal.ofReal
          (mS.S * svdT0 N B / (2 * Real.sqrt ε) *
            ∫ u in (0:ℝ)..(dimHit QS (svdT0 N B) T ε).toReal,
              Real.sqrt (QS (svdT0 N B * u)))) →
        dimHit QS (svdT0 N B) T ε ≠ ⊤ ∧
        SandwichE cL cH ((svdArrays α ς N B).S * svdT0 N B *
          phasePi (rq (α + ς) (α / 2)) ε) (stepHit mS QS T ε) ∧
        ∃ I : ℝ, 0 < I ∧ stepHit mS QS T ε = ENNReal.ofReal
            ((svdArrays α ς N B).S * svdT0 N B / (2 * Real.sqrt ε) * I) ∧
          (rq (α + ς) (α / 2) = 1 → |I - aQ (α / 2) / 2 * Real.log (1 / ε)| ≤ K) ∧
          (1 < rq (α + ς) (α / 2) → 1 / (2 * Real.sqrt 2) ≤ I ∧ |I - Jpq (α + ς) (α / 2)| ≤ Bd N ε) := by
  rcases lt_trichotomy α 2 with h | h | h
  · exact pw_svdB_lt2 α ς T hα h hς hT
  · rcases eq_or_lt_of_le hς with h1 | h1
    · exact pw_svdB_eq2a α ς T h h1.symm hT
    · exact pw_svdB_logg α ς T h h1 hT
  · exact pw_svdB_gt2 α ς T h hς hT

lemma pw_sgdB (α ς T : ℝ) (hα : 1 < α) (hς : 1 ≤ ς) (hT : 4 ≤ T) :
    ∃ (N1 : ℕ) (E1 cL cH K : ℝ) (Bd : ℕ → ℝ → ℝ), 4 ≤ N1 ∧ 0 < cL ∧ 0 < cH ∧ 0 ≤ K ∧
      (∀ δ : ℝ, 0 < δ → ∃ (N2 : ℕ) (ε2 : ℝ), 0 < ε2 ∧ ∀ (N : ℕ) (ε : ℝ), N2 ≤ N → 0 < ε →
        ε < ε2 → Bd N ε ≤ δ) ∧
      ∀ (N B : ℕ) (ε : ℝ) (mS mG : RowModel (Fin N)) (QS QG : ℝ → ℝ), N1 ≤ N → N ≤ B →
        0 < ε → ε < clockEps0 (α + ς) α T → E1 ≤ ε * (N : ℝ) →
        IsMatchedModel (svdArrays α ς N B) mS ε → IsVolterraSol mS QS →
        IsMatchedModel (sgdArrays α ς N B) mG ε → IsVolterraSol mG QG →
        (dimHit QG (sgdT0 α N B) T ε ≠ ⊤ → stepHit mG QG T ε = ENNReal.ofReal
          (mG.S * sgdT0 α N B / (2 * Real.sqrt ε) *
            ∫ u in (0:ℝ)..(dimHit QG (sgdT0 α N B) T ε).toReal,
              Real.sqrt (QG (sgdT0 α N B * u)))) →
        dimHit QG (sgdT0 α N B) T ε ≠ ⊤ ∧
        SandwichE cL cH ((sgdArrays α ς N B).S * sgdT0 α N B *
          phasePi (rq (α + ς) α) ε) (stepHit mG QG T ε) ∧
        ∃ I : ℝ, 0 < I ∧ stepHit mG QG T ε = ENNReal.ofReal
            ((sgdArrays α ς N B).S * sgdT0 α N B / (2 * Real.sqrt ε) * I) ∧
          (rq (α + ς) α = 1 → |I - aQ α / 2 * Real.log (1 / ε)| ≤ K) ∧
          (1 < rq (α + ς) α → 1 / (2 * Real.sqrt 2) ≤ I ∧ |I - Jpq (α + ς) α| ≤ Bd N ε) := by
  have hα0 : 0 < α := by linarith
  have hp : 1 < α + ς := by linarith
  have hr0 := pw_rq_pos hp hα0
  by_cases hr : rq (α + ς) α < 1
  · obtain ⟨N1, E1, cL, cH, hN1, hcL, hcH, h⟩ := pw_sgd_lt1 α ς T hα hς hr hT
    refine ⟨N1, E1, cL, cH, 0, fun _ _ => 0, hN1, hcL, hcH, le_rfl,
      fun δ hδ => ⟨0, 1, one_pos, fun N ε _ _ _ => hδ.le⟩, ?_⟩
    intro N B ε mS mG QS QG hN hNB hε hε0 hE hmS hQS hmG hQG hstep
    obtain ⟨hne, hsand, I, hI, hst⟩ := h N B ε mS mG QS QG hN hNB hε hε0 hE hmS hQS hmG hQG hstep
    have hPi : phasePi (rq (α + ς) α) ε = ε ^ (-(1 / (2 * rq (α + ς) α))) := by
      unfold phasePi; rw [if_pos hr]
    rw [hPi]
    exact ⟨hne, hsand, I, hI, hst, fun h => absurd h (ne_of_lt hr),
      fun h => absurd h (not_lt.2 hr.le)⟩
  · exact pw_sgdB_ge1 α ς T hα hς hT (not_lt.1 hr)

lemma pw_svd_ST_pos (α ς : ℝ) (N B : ℕ) (hα : 0 < α) (hp : 1 < α + ς)
    (hN : 1 ≤ N) (hNB : N ≤ B) (ε : ℝ) (hε : 0 < ε) (mS : RowModel (Fin N))
    (hmS : IsMatchedModel (svdArrays α ς N B) mS ε) :
    0 < (svdArrays α ς N B).S * svdT0 N B := by
  have hN0' : (0:ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hB0 : (0:ℝ) < B := by exact_mod_cast (by omega : 0 < B)
  have hT0 : 0 < svdT0 N B := by
    unfold svdT0 gammaRat; exact Real.sqrt_pos.2 (by positivity)
  have hS : 0 < (svdArrays α ς N B).S := by
    obtain ⟨h1, -⟩ := prop_app_phase_prefactors_i α ς N B hα hp hN hNB ε hε
    rw [h1]
    have h2 : 0 < Real.sqrt (gammaRat N B) := Real.sqrt_pos.2 (by unfold gammaRat; positivity)
    have h3 := pw_Hsum_ge_one (α / 2) N hN
    positivity
  exact mul_pos hS hT0

lemma pw_sgd_ST_pos (α ς : ℝ) (N B : ℕ) (hα : 0 < α) (hp : 1 < α + ς)
    (hN : 1 ≤ N) (hNB : N ≤ B) (ε : ℝ) (hε : 0 < ε) (mG : RowModel (Fin N))
    (hmG : IsMatchedModel (sgdArrays α ς N B) mG ε) :
    0 < (sgdArrays α ς N B).S * sgdT0 α N B := by
  have hN0 : (0:ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hmuB := pw_muBar_pos α hN
  have hB0 : (0:ℝ) < B := by exact_mod_cast (by omega : 0 < B)
  have hT0 : 0 < sgdT0 α N B := by
    unfold sgdT0; exact Real.sqrt_pos.2 (by positivity)
  have hS : 0 < (sgdArrays α ς N B).S := by
    obtain ⟨-, -, h3, -⟩ := prop_app_phase_prefactors_i α ς N B hα hp hN hNB ε hε
    rw [h3]
    have : 0 < Real.sqrt (Real.pi * muBarOf α N / (B : ℝ)) := Real.sqrt_pos.2 (by positivity)
    positivity
  exact mul_pos hS hT0

lemma pw_eqv1 {u a L : ℕ → ℝ} {K : ℝ} (ha : ∀ᶠ n in atTop, 0 < a n)
    (hu : ∀ᶠ n in atTop, ∃ I : ℝ, u n = a n * I ∧ |I - L n| ≤ K)
    (hL : Tendsto L atTop atTop) :
    IsEquivalent atTop u (fun n => a n * L n) := by
  rw [IsEquivalent, Asymptotics.isLittleO_iff]
  intro c hc
  have hK : ∀ᶠ n in atTop, (|K| + 1) / c ≤ L n := hL.eventually_ge_atTop _
  filter_upwards [ha, hu, hK] with n han hn hLn
  obtain ⟨I, hI1, hI2⟩ := hn
  have hLpos : 0 < L n := lt_of_lt_of_le (by positivity) hLn
  have h1 : K ≤ c * L n := by
    have := (div_le_iff₀ hc).1 hLn
    have := le_abs_self K
    nlinarith
  simp only [Pi.sub_apply, Real.norm_eq_abs]
  rw [hI1]
  have : a n * I - a n * L n = a n * (I - L n) := by ring
  rw [this, abs_mul, abs_mul, abs_of_pos han, abs_of_pos hLpos]
  calc a n * |I - L n| ≤ a n * (c * L n) :=
        mul_le_mul_of_nonneg_left (hI2.trans h1) han.le
    _ = c * (a n * L n) := by ring

lemma pw_eqv2 {u a : ℕ → ℝ} {J : ℝ} (ha : ∀ᶠ n in atTop, 0 < a n)
    (hu : ∀ δ : ℝ, 0 < δ → ∀ᶠ n in atTop, ∃ I : ℝ,
      u n = a n * I ∧ 1 / (2 * Real.sqrt 2) ≤ I ∧ |I - J| ≤ δ) :
    IsEquivalent atTop u (fun n => a n * J) := by
  have hs2 : 0 < Real.sqrt 2 := by positivity
  have hJ : 0 < J := by
    obtain ⟨n, I, -, h1, h2⟩ := (hu (1 / (4 * Real.sqrt 2)) (by positivity)).exists
    have h3 := (abs_le.1 h2).2
    have e : 1 / (2 * Real.sqrt 2) = 2 * (1 / (4 * Real.sqrt 2)) := by field_simp; ring
    have h4 : 0 < 1 / (4 * Real.sqrt 2) := by positivity
    linarith
  rw [IsEquivalent, Asymptotics.isLittleO_iff]
  intro c hc
  filter_upwards [ha, hu (c * J) (by positivity)] with n han hn
  obtain ⟨I, hI1, -, hI2⟩ := hn
  simp only [Pi.sub_apply, Real.norm_eq_abs]
  rw [hI1]
  have : a n * I - a n * J = a n * (I - J) := by ring
  rw [this, abs_mul, abs_mul, abs_of_pos han, abs_of_pos hJ]
  calc a n * |I - J| ≤ a n * (c * J) := mul_le_mul_of_nonneg_left hI2 han.le
    _ = c * (a n * J) := by ring

lemma pw_log_tendsto {ε : ℕ → ℝ} (h0 : Tendsto ε atTop (𝓝 0)) (hpos : ∀ n, 0 < ε n) :
    Tendsto (fun n => Real.log (1 / ε n)) atTop atTop := by
  have h1 : Tendsto ε atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.2 ⟨h0, Eventually.of_forall hpos⟩
  have h2 : Tendsto (fun n => (ε n)⁻¹) atTop atTop := tendsto_inv_nhdsGT_zero.comp h1
  have h3 := Real.tendsto_log_atTop.comp h2
  refine h3.congr (fun n => ?_)
  simp [one_div]

lemma pw_target1 {S T0 ε q : ℝ} (hq : 0 < q) (hε : 0 < ε) :
    S * T0 / (4 * Real.sqrt (8 * q)) * ε ^ (-(1 / 2 : ℝ)) * Real.log (1 / ε)
      = S * T0 / (2 * Real.sqrt ε) * (aQ q / 2 * Real.log (1 / ε)) := by
  have hs : 0 < Real.sqrt ε := Real.sqrt_pos.2 hε
  have h8 : 0 < Real.sqrt (8 * q) := Real.sqrt_pos.2 (by positivity)
  have hsq : ε ^ (-(1 / 2 : ℝ)) = (Real.sqrt ε)⁻¹ := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_neg hε.le]
  have hq' : aQ q = (Real.sqrt (8 * q))⁻¹ := by
    unfold aQ
    rw [Real.sqrt_eq_rpow, ← Real.rpow_neg (by positivity)]
  rw [hsq, hq']
  field_simp
  ring

lemma pw_dummyG (α ς : ℝ) (N B : ℕ) (hα : 0 < α) (hp : 1 < α + ς)
    (hN : 1 ≤ N) (hNB : N ≤ B) (ε : ℝ) (hε : 0 < ε) (mS : RowModel (Fin N))
    (hmS : IsMatchedModel (svdArrays α ς N B) mS ε) :
    ∃ mG : RowModel (Fin N), IsMatchedModel (sgdArrays α ς N B) mG ε ∧
      ∃ QG : ℝ → ℝ, IsVolterraSol mG QG := by
  have hN0 : (0:ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hB0 : (0:ℝ) < B := by exact_mod_cast (by omega : 0 < B)
  have hmuB := pw_muBar_pos α hN
  have hSG : 0 < (sgdArrays α ς N B).S := by
    obtain ⟨-, -, h3, -⟩ := prop_app_phase_prefactors_i α ς N B hα hp hN hNB ε hε
    rw [h3]
    have : 0 < Real.sqrt (Real.pi * muBarOf α N / (B : ℝ)) := Real.sqrt_pos.2 (by positivity)
    positivity
  obtain ⟨hμS, -, -, hQ0S, -⟩ := hmS
  have hpi : 2 < Real.pi := by linarith [Real.pi_gt_three]
  have hdpos : ∀ i : Fin N, 0 < (sgdArrays α ς N B).d i := by
    intro i
    show 0 < muOf α N i * Real.sqrt ((B : ℝ) / (Real.pi * muBarOf α N))
    have hmu : 0 < muOf α N i := by
      have := mS.μ_pos i
      rw [hμS] at this
      exact this
    have : 0 < Real.sqrt ((B : ℝ) / (Real.pi * muBarOf α N)) :=
      Real.sqrt_pos.2 (by positivity)
    positivity
  have hvnn : ∀ i : Fin N, 0 ≤ (sgdArrays α ς N B).v i := by
    intro i
    show 0 ≤ (N : ℝ) * (1 + 2 / Real.pi * (muOf α N i / muBarOf α N - 1))
    have hmu : 0 < muOf α N i := by
      have := mS.μ_pos i
      rw [hμS] at this
      exact this
    have h1 : 0 ≤ muOf α N i / muBarOf α N := by positivity
    have h2 : 2 / Real.pi < 1 := by rw [div_lt_one Real.pi_pos]; exact hpi
    have h3 : 0 ≤ 2 / Real.pi := by positivity
    apply mul_nonneg hN0.le
    nlinarith
  let mG : RowModel (Fin N) :=
    { μ := mS.μ
      d := (sgdArrays α ς N B).d
      v := (sgdArrays α ς N B).v
      Q0 := mS.Q0
      η := matchedStep (sgdArrays α ς N B) ε
      μ_pos := mS.μ_pos
      d_pos := hdpos
      v_nonneg := hvnn
      Q0_nonneg := mS.Q0_nonneg
      η_pos := by
        unfold matchedStep
        exact div_pos (by have := Real.sqrt_pos.2 hε; linarith) hSG
      summable_μQ0 := mS.summable_μQ0
      F0_pos := mS.F0_pos
      summable_S := Summable.of_finite }
  refine ⟨mG, ⟨hμS, rfl, rfl, hQ0S, rfl⟩, ?_⟩
  obtain ⟨Q, hQ, -⟩ := thm_app_phase_volterra_i mG
  exact ⟨Q, hQ⟩

lemma pw_thm_B (α ς T : ℝ) (hα : 1 < α) (hς : 1 ≤ ς) (hT : 4 ≤ T) :
    ∃ (Nst : ℕ) (Est cLo cHi : ℝ), PhaseBWindowHolds α ς T Nst Est cLo cHi ∧
      PhaseBEquivHolds α ς T Nst Est := by
  have hα0 : 0 < α := by linarith
  have hp : 1 < α + ς := by linarith
  obtain ⟨N1, E1, cL1, cH1, K1, Bd1, hN1, hcL1, hcH1, hK1, hsm1, h1⟩ := pw_svdB α ς T hα hς hT
  obtain ⟨N2, E2, cL2, cH2, K2, Bd2, hN2, hcL2, hcH2, hK2, hsm2, h2⟩ := pw_sgdB α ς T hα hς hT
  set Nst : ℕ := max N1 N2 with hNst
  set Est : ℝ := max E1 E2 with hEst
  set cLo : ℝ := min cL1 cL2 with hcLo
  set cHi : ℝ := max (max cH1 cH2) cLo with hcHi
  have hcLo0 : 0 < cLo := lt_min hcL1 hcL2
  have hEps := pw_phaseEps0_pos hα0 hp hT
  have hargs : ∀ (N B : ℕ) (ε : ℝ), PhaseWinB α ς T Nst Est N B ε →
      N1 ≤ N ∧ N2 ≤ N ∧ N ≤ B ∧ 0 < ε ∧ ε < clockEps0 (α + ς) (α / 2) T ∧
        ε < clockEps0 (α + ς) α T ∧ E1 ≤ ε * (N : ℝ) ∧ E2 ≤ ε * (N : ℝ) := by
    rintro N B ε ⟨hNN, hNB, hε, hε0, hE⟩
    have hε0' : ε < clockEps0 (α + ς) (α / 2) T ∧ ε < clockEps0 (α + ς) α T := by
      unfold phaseEps0 at hε0
      exact lt_min_iff.1 hε0
    exact ⟨le_trans (le_max_left _ _) hNN, le_trans (le_max_right _ _) hNN, hNB, hε, hε0'.1, hε0'.2,
      le_trans (le_max_left _ _) hE, le_trans (le_max_right _ _) hE⟩
  refine ⟨Nst, Est, cLo, cHi, ⟨hcLo0, le_max_right _ _, ?_, ?_⟩, ?_⟩
  · intro N B ε mS mG QS QG hW hmS hQS hmG hQG
    obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8⟩ := hargs N B ε hW
    have hN1' : 1 ≤ N := by have : 4 ≤ N := le_trans hN1 a1; omega
    have hpref := prop_app_phase_prefactors_iii α ς N B hα0 hp hN1' a3 ε T a4 (by linarith) mS mG hmS hmG QS QG hQS hQG
    obtain ⟨hne1, hsand1, -⟩ := h1 N B ε mS mG QS QG a1 a3 a4 a5 a7 hmS hQS hmG hQG hpref.1
    obtain ⟨hne2, hsand2, -⟩ := h2 N B ε mS mG QS QG a2 a3 a4 a6 a8 hmS hQS hmG hQG hpref.2
    exact ⟨⟨hne1, hne2⟩,
      pw_sandwich_mono hsand1 (min_le_left _ _) ((le_max_left _ _).trans (le_max_left _ _)),
      pw_sandwich_mono hsand2 (min_le_right _ _) ((le_max_right _ _).trans (le_max_left _ _))⟩
  · intro Nseq Bseq εseq hN hε hε0 _ hNB hE
    have h1' : ∀ᶠ n in atTop, (Nst:ℝ) ≤ (Nseq n : ℝ) := hN.eventually_ge_atTop _
    have h2' : ∀ᶠ n in atTop, εseq n < phaseEps0 α ς T :=
      (tendsto_order.1 hε).2 _ hEps
    have h3' : ∀ᶠ n in atTop, Est ≤ εseq n * (Nseq n : ℝ) := hE.eventually_ge_atTop _
    filter_upwards [h1', h2', h3'] with n a b c
    exact ⟨by exact_mod_cast a, hNB n, hε0 n, b, c⟩
  · intro Nseq Bseq εseq mS mG QS QG hN hε hε0 hN1' hNB hmS hQS hmG hQG hwin
    have hevS : ∀ᶠ n in atTop,
        0 < (svdArrays α ς (Nseq n) (Bseq n)).S * svdT0 (Nseq n) (Bseq n) ∧
        ∃ I : ℝ, 0 < I ∧ stepHit (mS n) (QS n) T (εseq n) = ENNReal.ofReal
          ((svdArrays α ς (Nseq n) (Bseq n)).S * svdT0 (Nseq n) (Bseq n) / (2 * Real.sqrt (εseq n)) * I) ∧
          (rq (α + ς) (α / 2) = 1 → |I - aQ (α / 2) / 2 * Real.log (1 / εseq n)| ≤ K1) ∧
          (1 < rq (α + ς) (α / 2) → 1 / (2 * Real.sqrt 2) ≤ I ∧
            |I - Jpq (α + ς) (α / 2)| ≤ Bd1 (Nseq n) (εseq n)) := by
      filter_upwards [hwin] with n hW
      obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8⟩ := hargs (Nseq n) (Bseq n) (εseq n) hW
      have hN1'' : 1 ≤ Nseq n := hN1' n
      have hpref := prop_app_phase_prefactors_iii α ς (Nseq n) (Bseq n) hα0 hp hN1'' a3 (εseq n) T a4
        (by linarith) (mS n) (mG n) (hmS n) (hmG n) (QS n) (QG n) (hQS n) (hQG n)
      obtain ⟨-, -, hR⟩ := h1 (Nseq n) (Bseq n) (εseq n) (mS n) (mG n) (QS n) (QG n) a1 a3 a4 a5 a7
        (hmS n) (hQS n) (hmG n) (hQG n) hpref.1
      exact ⟨pw_svd_ST_pos α ς (Nseq n) (Bseq n) hα0 hp hN1'' a3 (εseq n) a4 (mS n) (hmS n), hR⟩
    have hevG : ∀ᶠ n in atTop,
        0 < (sgdArrays α ς (Nseq n) (Bseq n)).S * sgdT0 α (Nseq n) (Bseq n) ∧
        ∃ I : ℝ, 0 < I ∧ stepHit (mG n) (QG n) T (εseq n) = ENNReal.ofReal
          ((sgdArrays α ς (Nseq n) (Bseq n)).S * sgdT0 α (Nseq n) (Bseq n) / (2 * Real.sqrt (εseq n)) * I) ∧
          (rq (α + ς) α = 1 → |I - aQ α / 2 * Real.log (1 / εseq n)| ≤ K2) ∧
          (1 < rq (α + ς) α → 1 / (2 * Real.sqrt 2) ≤ I ∧
            |I - Jpq (α + ς) α| ≤ Bd2 (Nseq n) (εseq n)) := by
      filter_upwards [hwin] with n hW
      obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8⟩ := hargs (Nseq n) (Bseq n) (εseq n) hW
      have hN1'' : 1 ≤ Nseq n := hN1' n
      have hpref := prop_app_phase_prefactors_iii α ς (Nseq n) (Bseq n) hα0 hp hN1'' a3 (εseq n) T a4
        (by linarith) (mS n) (mG n) (hmS n) (hmG n) (QS n) (QG n) (hQS n) (hQG n)
      obtain ⟨-, -, hR⟩ := h2 (Nseq n) (Bseq n) (εseq n) (mS n) (mG n) (QS n) (QG n) a2 a3 a4 a6 a8
        (hmS n) (hQS n) (hmG n) (hQG n) hpref.2
      exact ⟨pw_sgd_ST_pos α ς (Nseq n) (Bseq n) hα0 hp hN1'' a3 (εseq n) a4 (mG n) (hmG n), hR⟩
    -- conversion of the step time
    have hconvS : ∀ n, 0 < (svdArrays α ς (Nseq n) (Bseq n)).S * svdT0 (Nseq n) (Bseq n) →
        ∀ I : ℝ, 0 < I → stepHit (mS n) (QS n) T (εseq n) = ENNReal.ofReal
          ((svdArrays α ς (Nseq n) (Bseq n)).S * svdT0 (Nseq n) (Bseq n) / (2 * Real.sqrt (εseq n)) * I) →
        (stepHit (mS n) (QS n) T (εseq n)).toReal =
          (svdArrays α ς (Nseq n) (Bseq n)).S * svdT0 (Nseq n) (Bseq n) / (2 * Real.sqrt (εseq n)) * I := by
      intro n hST I hI hst
      have hs : 0 < Real.sqrt (εseq n) := Real.sqrt_pos.2 (hε0 n)
      rw [hst, ENNReal.toReal_ofReal]
      positivity
    have hconvG : ∀ n, 0 < (sgdArrays α ς (Nseq n) (Bseq n)).S * sgdT0 α (Nseq n) (Bseq n) →
        ∀ I : ℝ, 0 < I → stepHit (mG n) (QG n) T (εseq n) = ENNReal.ofReal
          ((sgdArrays α ς (Nseq n) (Bseq n)).S * sgdT0 α (Nseq n) (Bseq n) / (2 * Real.sqrt (εseq n)) * I) →
        (stepHit (mG n) (QG n) T (εseq n)).toReal =
          (sgdArrays α ς (Nseq n) (Bseq n)).S * sgdT0 α (Nseq n) (Bseq n) / (2 * Real.sqrt (εseq n)) * I := by
      intro n hST I hI hst
      have hs : 0 < Real.sqrt (εseq n) := Real.sqrt_pos.2 (hε0 n)
      rw [hst, ENNReal.toReal_ofReal]
      positivity
    have haS : ∀ᶠ n in atTop, 0 < (svdArrays α ς (Nseq n) (Bseq n)).S * svdT0 (Nseq n) (Bseq n) /
        (2 * Real.sqrt (εseq n)) := by
      filter_upwards [hevS] with n hn
      have hs : 0 < Real.sqrt (εseq n) := Real.sqrt_pos.2 (hε0 n)
      have := hn.1
      positivity
    have haG : ∀ᶠ n in atTop, 0 < (sgdArrays α ς (Nseq n) (Bseq n)).S * sgdT0 α (Nseq n) (Bseq n) /
        (2 * Real.sqrt (εseq n)) := by
      filter_upwards [hevG] with n hn
      have hs : 0 < Real.sqrt (εseq n) := Real.sqrt_pos.2 (hε0 n)
      have := hn.1
      positivity
    refine ⟨fun hr1 => ?_, fun hr1 => ?_, fun hr1 => ?_, fun hr1 => ?_⟩
    · have hq : 0 < α / 2 := by linarith
      have hL : Tendsto (fun n => aQ (α / 2) / 2 * Real.log (1 / εseq n)) atTop atTop :=
        (pw_log_tendsto hε hε0).const_mul_atTop (by unfold aQ; positivity)
      have key := pw_eqv1 (u := fun n => (stepHit (mS n) (QS n) T (εseq n)).toReal)
        (a := fun n => (svdArrays α ς (Nseq n) (Bseq n)).S * svdT0 (Nseq n) (Bseq n) /
          (2 * Real.sqrt (εseq n))) (K := K1) haS ?_ hL
      · refine key.congr_right (Filter.Eventually.of_forall fun n => ?_)
        exact (pw_target1 hq (hε0 n)).symm
      · filter_upwards [hevS] with n hn
        obtain ⟨hST, I, hI, hst, hb, -⟩ := hn
        exact ⟨I, hconvS n hST I hI hst, hb hr1⟩
    · have key := pw_eqv2 (u := fun n => (stepHit (mS n) (QS n) T (εseq n)).toReal)
        (a := fun n => (svdArrays α ς (Nseq n) (Bseq n)).S * svdT0 (Nseq n) (Bseq n) /
          (2 * Real.sqrt (εseq n))) (J := Jpq (α + ς) (α / 2)) haS ?_
      · refine key.congr_right (Filter.Eventually.of_forall fun n => ?_)
        ring
      · intro δ hδ
        obtain ⟨N2', ε2, hε2, hbd⟩ := hsm1 δ hδ
        have e1 : ∀ᶠ n in atTop, (N2' : ℝ) ≤ (Nseq n : ℝ) := hN.eventually_ge_atTop _
        have e2 : ∀ᶠ n in atTop, εseq n < ε2 := (tendsto_order.1 hε).2 _ hε2
        filter_upwards [hevS, e1, e2] with n hn a b
        obtain ⟨hST, I, hI, hst, -, hb⟩ := hn
        obtain ⟨hl, hb'⟩ := hb hr1
        exact ⟨I, hconvS n hST I hI hst, hl, hb'.trans (hbd (Nseq n) (εseq n) (by exact_mod_cast a) (hε0 n) b)⟩
    · have hq : 0 < α := hα0
      have hL : Tendsto (fun n => aQ α / 2 * Real.log (1 / εseq n)) atTop atTop :=
        (pw_log_tendsto hε hε0).const_mul_atTop (by unfold aQ; positivity)
      have key := pw_eqv1 (u := fun n => (stepHit (mG n) (QG n) T (εseq n)).toReal)
        (a := fun n => (sgdArrays α ς (Nseq n) (Bseq n)).S * sgdT0 α (Nseq n) (Bseq n) /
          (2 * Real.sqrt (εseq n))) (K := K2) haG ?_ hL
      · refine key.congr_right (Filter.Eventually.of_forall fun n => ?_)
        exact (pw_target1 hq (hε0 n)).symm
      · filter_upwards [hevG] with n hn
        obtain ⟨hST, I, hI, hst, hb, -⟩ := hn
        exact ⟨I, hconvG n hST I hI hst, hb hr1⟩
    · have key := pw_eqv2 (u := fun n => (stepHit (mG n) (QG n) T (εseq n)).toReal)
        (a := fun n => (sgdArrays α ς (Nseq n) (Bseq n)).S * sgdT0 α (Nseq n) (Bseq n) /
          (2 * Real.sqrt (εseq n))) (J := Jpq (α + ς) α) haG ?_
      · refine key.congr_right (Filter.Eventually.of_forall fun n => ?_)
        ring
      · intro δ hδ
        obtain ⟨N2', ε2, hε2, hbd⟩ := hsm2 δ hδ
        have e1 : ∀ᶠ n in atTop, (N2' : ℝ) ≤ (Nseq n : ℝ) := hN.eventually_ge_atTop _
        have e2 : ∀ᶠ n in atTop, εseq n < ε2 := (tendsto_order.1 hε).2 _ hε2
        filter_upwards [hevG, e1, e2] with n hn a b
        obtain ⟨hST, I, hI, hst, -, hb⟩ := hn
        obtain ⟨hl, hb'⟩ := hb hr1
        exact ⟨I, hconvG n hST I hI hst, hl, hb'.trans (hbd (Nseq n) (εseq n) (by exact_mod_cast a) (hε0 n) b)⟩

lemma pw_thm_B_iii (α ς T : ℝ) (hα : α = 2) (hς : 1 < ς) (hT : 4 ≤ T) :
    ∀ (Nseq Bseq : ℕ → ℕ) (εseq : ℕ → ℝ) (mS : ∀ n, RowModel (Fin (Nseq n)))
      (QS : ∀ n, ℝ → ℝ),
      Tendsto (fun n => (Nseq n : ℝ)) atTop atTop → Tendsto εseq atTop (𝓝 0) →
      (∀ n, 0 < εseq n) → (∀ n, 1 ≤ Nseq n) → (∀ n, Nseq n ≤ Bseq n) →
      (∀ n, IsMatchedModel (svdArrays α ς (Nseq n) (Bseq n)) (mS n) (εseq n)) →
      (∀ n, IsVolterraSol (mS n) (QS n)) →
      IsEquivalent atTop (fun n => (stepHit (mS n) (QS n) T (εseq n)).toReal)
        (fun n => (svdArrays α ς (Nseq n) (Bseq n)).S * svdT0 (Nseq n) (Bseq n) *
          Jpq (α + ς) (α / 2) / (2 * Real.sqrt (εseq n))) := by
  intro Nseq Bseq εseq mS QS hN hε hε0 hN1' hNB hmS hQS
  have hα1 : 1 < α := by rw [hα]; norm_num
  have hα0 : 0 < α := by linarith
  have hp : 1 < α + ς := by linarith
  have hr1 : 1 < rq (α + ς) (α / 2) := by
    unfold rq
    rw [lt_div_iff₀ (by linarith)]
    rw [hα]; linarith
  obtain ⟨N1, cL, cH, K, Bd, hN1, hcL, hcH, hK, hsm, h⟩ := pw_svdB_logg0 α ς T hα hς hT
  have hEps := pw_clockEps0_pos hp (show 0 < α / 2 by linarith) hT
  have hev : ∀ᶠ n in atTop, (N1 : ℝ) ≤ (Nseq n : ℝ) ∧ εseq n < clockEps0 (α + ς) (α / 2) T :=
    (hN.eventually_ge_atTop _).and ((tendsto_order.1 hε).2 _ hEps)
  have hevS : ∀ᶠ n in atTop,
      0 < (svdArrays α ς (Nseq n) (Bseq n)).S * svdT0 (Nseq n) (Bseq n) ∧
      ∃ I : ℝ, 0 < I ∧ stepHit (mS n) (QS n) T (εseq n) = ENNReal.ofReal
        ((svdArrays α ς (Nseq n) (Bseq n)).S * svdT0 (Nseq n) (Bseq n) / (2 * Real.sqrt (εseq n)) * I) ∧
        (1 / (2 * Real.sqrt 2) ≤ I ∧ |I - Jpq (α + ς) (α / 2)| ≤ Bd (Nseq n) (εseq n)) := by
    filter_upwards [hev] with n ⟨a1, a4⟩
    have a1' : N1 ≤ Nseq n := by exact_mod_cast a1
    have hN1'' : 1 ≤ Nseq n := hN1' n
    obtain ⟨mG, hmG, QG, hQG⟩ := pw_dummyG α ς (Nseq n) (Bseq n) hα0 hp hN1'' (hNB n) (εseq n) (hε0 n) (mS n) (hmS n)
    have hpref := prop_app_phase_prefactors_iii α ς (Nseq n) (Bseq n) hα0 hp hN1'' (hNB n) (εseq n) T (hε0 n)
      (by linarith) (mS n) mG (hmS n) hmG (QS n) QG (hQS n) hQG
    obtain ⟨-, -, hR⟩ := h (Nseq n) (Bseq n) (εseq n) (mS n) mG (QS n) QG a1' (hNB n) (hε0 n) a4
      (hmS n) (hQS n) hmG hQG hpref.1
    obtain ⟨I, hI, hst, -, hb⟩ := hR
    exact ⟨pw_svd_ST_pos α ς (Nseq n) (Bseq n) hα0 hp hN1'' (hNB n) (εseq n) (hε0 n) (mS n) (hmS n),
      I, hI, hst, hb hr1⟩
  have hconvS : ∀ n, ∀ I : ℝ, 0 < I → 0 < (svdArrays α ς (Nseq n) (Bseq n)).S * svdT0 (Nseq n) (Bseq n) →
      stepHit (mS n) (QS n) T (εseq n) = ENNReal.ofReal
        ((svdArrays α ς (Nseq n) (Bseq n)).S * svdT0 (Nseq n) (Bseq n) / (2 * Real.sqrt (εseq n)) * I) →
      (stepHit (mS n) (QS n) T (εseq n)).toReal =
        (svdArrays α ς (Nseq n) (Bseq n)).S * svdT0 (Nseq n) (Bseq n) / (2 * Real.sqrt (εseq n)) * I := by
    intro n I hI hST hst
    have hs : 0 < Real.sqrt (εseq n) := Real.sqrt_pos.2 (hε0 n)
    rw [hst, ENNReal.toReal_ofReal]
    positivity
  have haS : ∀ᶠ n in atTop, 0 < (svdArrays α ς (Nseq n) (Bseq n)).S * svdT0 (Nseq n) (Bseq n) /
      (2 * Real.sqrt (εseq n)) := by
    filter_upwards [hevS] with n hn
    have hs : 0 < Real.sqrt (εseq n) := Real.sqrt_pos.2 (hε0 n)
    have := hn.1
    positivity
  have key := pw_eqv2 (u := fun n => (stepHit (mS n) (QS n) T (εseq n)).toReal)
    (a := fun n => (svdArrays α ς (Nseq n) (Bseq n)).S * svdT0 (Nseq n) (Bseq n) /
      (2 * Real.sqrt (εseq n))) (J := Jpq (α + ς) (α / 2)) haS ?_
  · refine key.congr_right (Filter.Eventually.of_forall fun n => ?_)
    ring
  · intro δ hδ
    obtain ⟨N2', ε2, hε2, hbd⟩ := hsm δ hδ
    have e1 : ∀ᶠ n in atTop, (N2' : ℝ) ≤ (Nseq n : ℝ) := hN.eventually_ge_atTop _
    have e2 : ∀ᶠ n in atTop, εseq n < ε2 := (tendsto_order.1 hε).2 _ hε2
    filter_upwards [hevS, e1, e2] with n hn a b
    obtain ⟨hST, I, hI, hst, hl, hb⟩ := hn
    exact ⟨I, hconvS n I hI hST hst, hl, hb.trans (hbd (Nseq n) (εseq n) (by exact_mod_cast a) (hε0 n) b)⟩

/-- Label `thm:app-phase-B`, declaration of record. Snapshot `cr-2026-10-23`.

Statement (verbatim, `sections/07-phase-comparison/section.tex`, l.1284–1303):

```latex
\begin{theorem}[Main covariance range]\label{thm:app-phase-B}
Fix $\alpha>1$, $\texp\ge1$ and $T\ge4$. There are $N_*$ and $E_*$ and
$0<c_-\le c_+$, all depending only on $\alpha$, $\texp$ and $T$, such that for all
$N\ge N_*$, $B\ge N$ and $0<\epsilon<\epsilon_0$ with $\epsilon N\ge E_*$, and
for both $j$, the first hit $\hat u_j$ is attained and
\[
c_-\le\frac{t^j_{T\epsilon}}{\mathcal S_jT_0^j\,\Pi_{r_j}(\epsilon)}\le c_+ .
\]
Along every sequence with $N\to\infty$ and $\epsilon\downarrow0$ in this
window, for each $j$,
\begin{equation}\label{eqn:app-phase-equivalents}
t^j_{T\epsilon}\sim\frac{\mathcal S_jT_0^j}{4\sqrt{8q_j}}\,\epsilon^{-1/2}\log\frac1\epsilon\quad(r_j=1),\qquad
t^j_{T\epsilon}\sim\frac{\mathcal S_jT_0^j\,J(p,q_j)}{2\sqrt\epsilon}\quad(r_j>1).
\end{equation}
If $\alpha=2$ and $\texp>1$, the second equivalent holds for
$j=\text{s-SVD}$ along every sequence with $N\to\infty$, $\epsilon\downarrow0$
and $B\ge N$, with no relation between $N$ and $\epsilon$. Every sequence
with $N\to\infty$, $\epsilon\downarrow0$ and $\epsilon N\to\infty$ lies in the
window for all large indices, uniformly over $B\ge N$.
\end{theorem}
```
-/
theorem thm_app_phase_B (α ς T : ℝ) (hα : 1 < α) (hς : 1 ≤ ς) (hT : 4 ≤ T) :
    ∃ (Nst : ℕ) (Est cLo cHi : ℝ), PhaseBWindowHolds α ς T Nst Est cLo cHi := by
  obtain ⟨Nst, Est, cLo, cHi, h, -⟩ := pw_thm_B α ς T hα hς hT
  exact ⟨Nst, Est, cLo, cHi, h⟩

/-- Label `thm:app-phase-B`, declaration of record. Snapshot `cr-2026-10-23`.

Statement (verbatim, `sections/07-phase-comparison/section.tex`, l.1284–1303):

```latex
\begin{theorem}[Main covariance range]\label{thm:app-phase-B}
Fix $\alpha>1$, $\texp\ge1$ and $T\ge4$. There are $N_*$ and $E_*$ and
$0<c_-\le c_+$, all depending only on $\alpha$, $\texp$ and $T$, such that for all
$N\ge N_*$, $B\ge N$ and $0<\epsilon<\epsilon_0$ with $\epsilon N\ge E_*$, and
for both $j$, the first hit $\hat u_j$ is attained and
\[
c_-\le\frac{t^j_{T\epsilon}}{\mathcal S_jT_0^j\,\Pi_{r_j}(\epsilon)}\le c_+ .
\]
Along every sequence with $N\to\infty$ and $\epsilon\downarrow0$ in this
window, for each $j$,
\begin{equation}\label{eqn:app-phase-equivalents}
t^j_{T\epsilon}\sim\frac{\mathcal S_jT_0^j}{4\sqrt{8q_j}}\,\epsilon^{-1/2}\log\frac1\epsilon\quad(r_j=1),\qquad
t^j_{T\epsilon}\sim\frac{\mathcal S_jT_0^j\,J(p,q_j)}{2\sqrt\epsilon}\quad(r_j>1).
\end{equation}
If $\alpha=2$ and $\texp>1$, the second equivalent holds for
$j=\text{s-SVD}$ along every sequence with $N\to\infty$, $\epsilon\downarrow0$
and $B\ge N$, with no relation between $N$ and $\epsilon$. Every sequence
with $N\to\infty$, $\epsilon\downarrow0$ and $\epsilon N\to\infty$ lies in the
window for all large indices, uniformly over $B\ge N$.
\end{theorem}
```
-/
theorem thm_app_phase_B_ii (α ς T : ℝ) (hα : 1 < α) (hς : 1 ≤ ς) (hT : 4 ≤ T) :
    ∃ (Nst : ℕ) (Est cLo cHi : ℝ), PhaseBWindowHolds α ς T Nst Est cLo cHi ∧
      PhaseBEquivHolds α ς T Nst Est := by
  exact pw_thm_B α ς T hα hς hT

/-- Label `thm:app-phase-B`, declaration of record. Snapshot `cr-2026-10-23`.

Statement (verbatim, `sections/07-phase-comparison/section.tex`, l.1284–1303):

```latex
\begin{theorem}[Main covariance range]\label{thm:app-phase-B}
Fix $\alpha>1$, $\texp\ge1$ and $T\ge4$. There are $N_*$ and $E_*$ and
$0<c_-\le c_+$, all depending only on $\alpha$, $\texp$ and $T$, such that for all
$N\ge N_*$, $B\ge N$ and $0<\epsilon<\epsilon_0$ with $\epsilon N\ge E_*$, and
for both $j$, the first hit $\hat u_j$ is attained and
\[
c_-\le\frac{t^j_{T\epsilon}}{\mathcal S_jT_0^j\,\Pi_{r_j}(\epsilon)}\le c_+ .
\]
Along every sequence with $N\to\infty$ and $\epsilon\downarrow0$ in this
window, for each $j$,
\begin{equation}\label{eqn:app-phase-equivalents}
t^j_{T\epsilon}\sim\frac{\mathcal S_jT_0^j}{4\sqrt{8q_j}}\,\epsilon^{-1/2}\log\frac1\epsilon\quad(r_j=1),\qquad
t^j_{T\epsilon}\sim\frac{\mathcal S_jT_0^j\,J(p,q_j)}{2\sqrt\epsilon}\quad(r_j>1).
\end{equation}
If $\alpha=2$ and $\texp>1$, the second equivalent holds for
$j=\text{s-SVD}$ along every sequence with $N\to\infty$, $\epsilon\downarrow0$
and $B\ge N$, with no relation between $N$ and $\epsilon$. Every sequence
with $N\to\infty$, $\epsilon\downarrow0$ and $\epsilon N\to\infty$ lies in the
window for all large indices, uniformly over $B\ge N$.
\end{theorem}
```
-/
theorem thm_app_phase_B_iii (α ς T : ℝ) (hα : α = 2) (hς : 1 < ς) (hT : 4 ≤ T) :
    ∀ (Nseq Bseq : ℕ → ℕ) (εseq : ℕ → ℝ) (mS : ∀ n, RowModel (Fin (Nseq n)))
      (QS : ∀ n, ℝ → ℝ),
      Tendsto (fun n => (Nseq n : ℝ)) atTop atTop → Tendsto εseq atTop (𝓝 0) →
      (∀ n, 0 < εseq n) → (∀ n, 1 ≤ Nseq n) → (∀ n, Nseq n ≤ Bseq n) →
      (∀ n, IsMatchedModel (svdArrays α ς (Nseq n) (Bseq n)) (mS n) (εseq n)) →
      (∀ n, IsVolterraSol (mS n) (QS n)) →
      IsEquivalent atTop (fun n => (stepHit (mS n) (QS n) T (εseq n)).toReal)
        (fun n => (svdArrays α ς (Nseq n) (Bseq n)).S * svdT0 (Nseq n) (Bseq n) *
          Jpq (α + ς) (α / 2) / (2 * Real.sqrt (εseq n))) := by
  exact pw_thm_B_iii α ς T hα hς hT

/-! ### Proof helpers for `thm:app-phase-C` (P-H.8.P3) -/

lemma pw_lowh {C r ε : ℝ} (hC : 0 < C) (hr : 0 < r) (hε : 0 < ε) (hεC : ε < C ^ 2) :
    0 < phaseHeight C r ε ∧
    (∀ u ∈ Icc (0:ℝ) (phaseHeight C r ε), Real.sqrt ε ≤ C * (1 + u) ^ (-r)) ∧
    C * (1 + phaseHeight C r ε) ^ (-r) = Real.sqrt ε := by
  have hs : 0 < Real.sqrt ε := Real.sqrt_pos.2 hε
  unfold phaseHeight
  set X := (C / Real.sqrt ε) ^ (1 / r) with hX
  have hX1 : 1 < X := by
    apply Real.one_lt_rpow _ (by positivity)
    rw [one_lt_div hs]
    calc Real.sqrt ε < Real.sqrt (C ^ 2) := Real.sqrt_lt_sqrt hε.le hεC
      _ = C := Real.sqrt_sq hC.le
  have hXr : X ^ r = C / Real.sqrt ε := by
    rw [hX, ← Real.rpow_mul (by positivity)]
    have : 1 / r * r = 1 := by field_simp
    rw [this, Real.rpow_one]
  have hXpos : 0 < X := by linarith
  refine ⟨by linarith, ?_, ?_⟩
  · intro u hu
    have h1 : 1 + u ≤ X := by linarith [hu.2]
    have h1pos : 0 < 1 + u := by linarith [hu.1]
    have h2 : X ^ (-r) ≤ (1 + u) ^ (-r) := Real.rpow_le_rpow_of_nonpos h1pos h1 (by linarith)
    have h3 : C * X ^ (-r) = Real.sqrt ε := by
      rw [Real.rpow_neg hXpos.le, hXr]; field_simp
    calc Real.sqrt ε = C * X ^ (-r) := h3.symm
      _ ≤ C * (1 + u) ^ (-r) := mul_le_mul_of_nonneg_left h2 hC.le
  · have : 1 + (X - 1) = X := by ring
    rw [this, Real.rpow_neg hXpos.le, hXr]; field_simp

lemma pw_lowConvB {C r k H ε : ℝ} {g : ℝ → ℝ}
    (hC : 0 < C) (hgc : ContinuousOn g (Ici 0)) (hgn : ∀ u ∈ Ici (0:ℝ), 0 ≤ g u) (hgk : ∀ u ∈ Ici (0:ℝ), g u ≤ k)
    (hH : 0 ≤ H) (hkH : k * C * Ir r H ≤ Real.sqrt ε) :
    ∀ u ∈ Icc (0:ℝ) H,
      Muon.Foundations.oneSidedConv (fun w => C * (1 + w) ^ (-r)) g u ≤ Real.sqrt ε := by
  intro u hu
  have hu0 : 0 ≤ u := hu.1
  have hfc0 : ContinuousOn (fun w : ℝ => (1 + w) ^ (-r)) (Ici 0) := by
    apply ContinuousOn.rpow_const (by fun_prop)
    intro x hx
    left
    have : 0 ≤ x := hx
    linarith
  have hfc : ContinuousOn (fun w : ℝ => C * (1 + w) ^ (-r)) (Ici 0) :=
    continuousOn_const.mul hfc0
  have hfn : ∀ w ∈ Ici (0:ℝ), 0 ≤ C * (1 + w) ^ (-r) := by
    intro w hw
    have : 0 ≤ w := hw
    exact mul_nonneg hC.le (Real.rpow_nonneg (by linarith) _)
  have hint1 : IntervalIntegrable (fun s => C * (1 + (u - s)) ^ (-r) * g s) MeasureTheory.volume 0 u := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hu0]
    apply ContinuousOn.mul
    · apply hfc.comp (by fun_prop : ContinuousOn (fun s : ℝ => u - s) _)
      intro s hs
      exact sub_nonneg.2 hs.2
    · exact hgc.mono (fun s hs => hs.1)
  have hint2 : IntervalIntegrable (fun s => C * (1 + (u - s)) ^ (-r) * k) MeasureTheory.volume 0 u := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hu0]
    apply ContinuousOn.mul _ continuousOn_const
    apply hfc.comp (by fun_prop : ContinuousOn (fun s : ℝ => u - s) _)
    intro s hs
    exact sub_nonneg.2 hs.2
  have hIr : Ir r u ≤ Ir r H := by
    have hi1 : IntervalIntegrable (fun w : ℝ => (1 + w) ^ (-r)) MeasureTheory.volume 0 u := by
      apply ContinuousOn.intervalIntegrable
      rw [Set.uIcc_of_le hu0]
      exact hfc0.mono (fun s hs => hs.1)
    have hi2 : IntervalIntegrable (fun w : ℝ => (1 + w) ^ (-r)) MeasureTheory.volume u H := by
      apply ContinuousOn.intervalIntegrable
      rw [Set.uIcc_of_le hu.2]
      exact hfc0.mono (fun s hs => le_trans hu0 hs.1)
    unfold Ir
    rw [← intervalIntegral.integral_add_adjacent_intervals hi1 hi2]
    have : 0 ≤ ∫ w in u..H, (1 + w) ^ (-r) :=
      intervalIntegral.integral_nonneg hu.2 (fun w hw => Real.rpow_nonneg (by linarith [hw.1]) _)
    linarith
  unfold Muon.Foundations.oneSidedConv
  calc ∫ s in (0:ℝ)..u, C * (1 + (u - s)) ^ (-r) * g s
      ≤ ∫ s in (0:ℝ)..u, C * (1 + (u - s)) ^ (-r) * k := by
        apply intervalIntegral.integral_mono_on hu0 hint1 hint2
        intro s hs
        exact mul_le_mul_of_nonneg_left (hgk s hs.1) (hfn _ (sub_nonneg.2 hs.2))
    _ = (∫ s in (0:ℝ)..u, C * (1 + (u - s)) ^ (-r)) * k := intervalIntegral.integral_mul_const _ _
    _ = (∫ s in (0:ℝ)..u, C * (1 + s) ^ (-r)) * k := by
        congr 1
        rw [intervalIntegral.integral_comp_sub_left (fun s => C * (1 + s) ^ (-r)) u]
        simp
    _ = C * Ir r u * k := by
        unfold Ir
        rw [intervalIntegral.integral_const_mul]
    _ ≤ C * Ir r H * k := by
        have hk : 0 ≤ k := (hgn 0 (Set.mem_Ici.2 le_rfl)).trans (hgk 0 (Set.mem_Ici.2 le_rfl))
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hIr hC.le) hk
    _ = k * C * Ir r H := by ring
    _ ≤ _ := hkH

lemma pw_lowHit {p q T : ℝ} (hp : 1 < p) (hq : 0 < q) (hT : 4 ≤ T)
    (N : ℕ) (ε : ℝ) (g Y : ℝ → ℝ) (hN : 4 ≤ N) (hε : 0 < ε)
    (hε0 : ε < clockEps0 p q T)
    (hgc : ContinuousOn g (Ici 0)) (hgn : ∀ u ∈ Ici (0:ℝ), 0 ≤ g u) (hgi : IntegrableOn g (Ioi 0))
    (hgm : ∫ u in Ioi (0:ℝ), g u ≤ 1)
    (hYc : ContinuousOn Y (Ici 0)) (hYp : ∀ u ∈ Ici (0:ℝ), 0 < Y u)
    (hYe : ∀ u ∈ Ici (0:ℝ), Y u = fNq (N:ℕ∞) p q u +
          Real.sqrt ε * Muon.Foundations.oneSidedConv (fun v => Real.sqrt (Y v)) g u)
    (hconv : ∀ u ∈ Icc (0:ℝ) (phaseHeight (Cpq p q) (rq p q) ε),
          Muon.Foundations.oneSidedConv (fun w => Cpq p q * (1 + w) ^ (-rq p q)) g u
            ≤ Real.sqrt ε) :
    ∃ û : ℝ, firstHit Y (T * ε) = ENNReal.ofReal û ∧ 0 < û ∧
      û ≤ phaseHeight (Cpq p q) (rq p q) ε ∧ Y û = T * ε ∧
      (∀ u ∈ Ici (0:ℝ), fNq (N:ℕ∞) p q u ≤ Y u) ∧
      0 ≤ ∫ u in (0:ℝ)..û, (Real.sqrt (Y u) - Real.sqrt (fNq (N:ℕ∞) p q u)) ∧
      ∫ u in (0:ℝ)..û, (Real.sqrt (Y u) - Real.sqrt (fNq (N:ℕ∞) p q u)) ≤
        Real.sqrt (2 * ε) * phaseHeight (Cpq p q) (rq p q) ε := by
  have hC := pw_Cpq_pos hp hq
  have hT0 : 0 < T := by linarith
  have hr0 := pw_rq_pos hp hq
  obtain ⟨hε8, hεC⟩ := pw_eps_facts ε hε0
  have hs : 0 < Real.sqrt ε := Real.sqrt_pos.2 hε
  have hN1 : 1 ≤ N := by omega
  obtain ⟨hHpos, hh_ge, hh_H⟩ := pw_lowh hC hr0 hε hεC
  set H := phaseHeight (Cpq p q) (rq p q) ε with hH_def
  set C := Cpq p q with hC_def
  set r := rq p q with hr_def
  have hf0 : T * ε < fNq (N : ℕ∞) p q 0 := by
    rw [pw_fNq_zero]
    have := pw_Hsum_ge_one p N hN1
    have h2 : T * ε < 1 / 8 := by
      have := mul_lt_mul_of_pos_left hε8 hT0
      rw [mul_one_div, mul_comm 8 T, ← div_div, div_self hT0.ne'] at this
      linarith
    linarith
  have hhc : ContinuousOn (fun u => C * (1 + u) ^ (-r)) (Icc 0 H) := by
    apply ContinuousOn.mul continuousOn_const
    apply ContinuousOn.rpow_const (by fun_prop)
    intro x hx
    left
    have : 0 ≤ x := hx.1
    linarith
  have hfh : ∀ u ∈ Icc (0:ℝ) H, fNq (N:ℕ∞) p q u ≤ (C * (1 + u) ^ (-r)) ^ 2 := by
    intro u hu
    have hle := pw_fNq_le hp hq N hu.1
    refine hle.trans (le_of_eq ?_)
    have hb : 0 < 1 + u := by linarith [hu.1]
    have hsq : ((1 + u) ^ (-r)) ^ 2 = (1 + u) ^ (-(2 * r)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hb.le]
      congr 1; push_cast; ring
    rw [mul_pow, hsq]
  have hf_nn : ∀ u ∈ Ici (0:ℝ), 0 ≤ fNq (N:ℕ∞) p q u := by
    intro u _; unfold fNq; have := pw_Lsum_nonneg N p q u; positivity
  have hsq_ii := lem_app_phase_square_ii (ε := ε) (T := T) (H := H) hε hT hHpos
    (f := fNq (N:ℕ∞) p q) (g := g) (h := fun u => C * (1 + u) ^ (-r)) (Y := Y)
    hgc hgn hgi hgm (pw_fNq_cont N p q).continuousOn hf_nn hf0 hYc hYp hYe
    hhc hh_ge hh_H hfh (Or.inr hconv)
  obtain ⟨û, hhit, hû0, hûH, hYû, hE0, hE1, hE2⟩ := hsq_ii
  have hYf : ∀ u ∈ Ici (0:ℝ), fNq (N:ℕ∞) p q u ≤ Y u := by
    intro u hu
    rw [hYe u hu]
    have hconv0 : 0 ≤ Muon.Foundations.oneSidedConv (fun v => Real.sqrt (Y v)) g u := by
      unfold Muon.Foundations.oneSidedConv
      apply intervalIntegral.integral_nonneg hu
      intro s hs
      exact mul_nonneg (Real.sqrt_nonneg _) (hgn s (Set.mem_Ici.2 hs.1))
    have := mul_nonneg hs.le hconv0
    linarith
  exact ⟨û, hhit, hû0, hûH, hYû, hYf, hE0, hE2 hconv⟩

lemma pw_E_bound {C r ε : ℝ} (hC : 0 < C) (hr : 0 < r) (hε : 0 < ε) :
    Real.sqrt (2 * ε) * phaseHeight C r ε
      ≤ Real.sqrt 2 * C ^ (1 / r) * ε ^ ((r - 1) / (2 * r)) := by
  have hs : 0 < Real.sqrt ε := Real.sqrt_pos.2 hε
  have h1 : Real.sqrt (2 * ε) = Real.sqrt 2 * Real.sqrt ε := Real.sqrt_mul (by norm_num) _
  have h2 : (C / Real.sqrt ε) ^ (1 / r) = C ^ (1 / r) * ε ^ (-(1 / (2 * r))) := by
    rw [Real.div_rpow hC.le hs.le, Real.sqrt_eq_rpow, ← Real.rpow_mul hε.le, div_eq_mul_inv,
      ← Real.rpow_neg hε.le]
    congr 3
    field_simp
  have h3 : Real.sqrt ε * ε ^ (-(1 / (2 * r))) = ε ^ ((r - 1) / (2 * r)) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hε]
    congr 1
    field_simp
    ring
  unfold phaseHeight
  rw [h1, h2]
  have hX : 0 ≤ C ^ (1 / r) * ε ^ (-(1 / (2 * r))) :=
    mul_nonneg (Real.rpow_nonneg hC.le _) (Real.rpow_nonneg hε.le _)
  calc Real.sqrt 2 * Real.sqrt ε * (C ^ (1 / r) * ε ^ (-(1 / (2 * r))) - 1)
      ≤ Real.sqrt 2 * Real.sqrt ε * (C ^ (1 / r) * ε ^ (-(1 / (2 * r)))) :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    _ = Real.sqrt 2 * C ^ (1 / r) * (Real.sqrt ε * ε ^ (-(1 / (2 * r)))) := by ring
    _ = _ := by rw [h3]

lemma pw_conv_a {C r ε : ℝ} {g : ℝ → ℝ} (hC : 0 < C) (hr : 0 < r) (hε : 0 < ε)
    (hεC : ε < C ^ 2)
    (hconv : ∀ u ∈ Icc (0:ℝ) (phaseHeight C r ε),
      Muon.Foundations.oneSidedConv (fun w => C * (1 + w) ^ (-r)) g u ≤ Real.sqrt ε) :
    ∀ u ∈ Icc (0:ℝ) (1 * ((C / Real.sqrt ε) ^ (1 / r) - 1)),
      Muon.Foundations.oneSidedConv (fun w => C * (1 + w / 1) ^ (-r)) g u
        ≤ 2 * (C * (1 + u / 1) ^ (-r)) := by
  obtain ⟨-, hge, -⟩ := pw_lowh hC hr hε hεC
  intro u hu
  simp only [one_mul] at hu
  simp only [div_one]
  have h1 := hconv u hu
  have h2 := hge u hu
  have h3 : 0 ≤ Real.sqrt ε := Real.sqrt_nonneg _
  linarith

lemma pw_lowGt1 {p q T : ℝ} (hp : 1 < p) (hq : 0 < q) (hT : 4 ≤ T) (hr1 : 1 < rq p q)
    (N : ℕ) (ε S T0 : ℝ) (m : RowModel (Fin N)) (Q : ℝ → ℝ) (g : ℝ → ℝ)
    (hN : 4 ≤ N) (hε : 0 < ε)
    (hε0 : ε < clockEps0 p q T)
    (hgc : ContinuousOn g (Ici 0)) (hgn : ∀ u ∈ Ici (0:ℝ), 0 ≤ g u) (hgi : IntegrableOn g (Ioi 0))
    (hgm : ∫ u in Ioi (0:ℝ), g u ≤ 1)
    (hYc : ContinuousOn (fun u => Q (T0 * u)) (Ici 0)) (hYp : ∀ u ∈ Ici (0:ℝ), 0 < Q (T0 * u))
    (hYe : ∀ u ∈ Ici (0:ℝ), Q (T0 * u) = fNq (N:ℕ∞) p q u +
          Real.sqrt ε * Muon.Foundations.oneSidedConv (fun v => Real.sqrt (Q (T0 * v))) g u)
    (hconv : ∀ u ∈ Icc (0:ℝ) (phaseHeight (Cpq p q) (rq p q) ε),
          Muon.Foundations.oneSidedConv (fun w => Cpq p q * (1 + w) ^ (-rq p q)) g u
            ≤ Real.sqrt ε)
    (hstep : dimHit Q T0 T ε ≠ ⊤ → stepHit m Q T ε = ENNReal.ofReal (S * T0 / (2 * Real.sqrt ε) *
          ∫ u in (0:ℝ)..(dimHit Q T0 T ε).toReal, Real.sqrt (Q (T0 * u)))) :
    dimHit Q T0 T ε ≠ ⊤ ∧ ∃ I E : ℝ,
      stepHit m Q T ε = ENNReal.ofReal (S * T0 / (2 * Real.sqrt ε) * I) ∧
      1 / (2 * Real.sqrt 2) ≤ I ∧ I ≤ Jpq p q + E ∧ 0 ≤ E ∧
      E ≤ Real.sqrt 2 * Cpq p q ^ (1 / rq p q) * ε ^ ((rq p q - 1) / (2 * rq p q)) ∧
      |I - Jpq p q| ≤
        (1 / Real.sqrt (2 * (p - 1)) + Cpq p q / (rq p q - 1)) * (N : ℝ) ^ (-(q * (rq p q - 1)))
        + Cpq p q / (rq p q - 1) * (1 + 1 / 2 * Real.log (1 / (2 * T * ε))) ^ (1 - rq p q) + E := by
  have hC := pw_Cpq_pos hp hq
  have hr0 := pw_rq_pos hp hq
  obtain ⟨û, hhit, hû0, hûH, hYû, hYf, hE0, hE1⟩ := pw_lowHit hp hq hT N ε g
    (fun u => Q (T0 * u)) hN hε hε0 hgc hgn hgi hgm hYc hYp hYe hconv
  have hdim : dimHit Q T0 T ε = ENNReal.ofReal û := hhit
  have hne : dimHit Q T0 T ε ≠ ⊤ := by rw [hdim]; exact ENNReal.ofReal_ne_top
  have hst := hstep hne
  rw [hdim, ENNReal.toReal_ofReal hû0.le] at hst
  obtain ⟨h1, h2, h3⟩ := lem_app_phase_clock_integral_iii (p := p) (q := q) (T := T) (ε := ε)
    (H := phaseHeight (Cpq p q) (rq p q) ε) (û := û) hp hq hT N hN hε hε0 hYc hYf
    (Y := fun u => Q (T0 * u)) hdim hû0 hYû hûH hr1
  beta_reduce at h1 h2 h3
  have hEb := hE1.trans (pw_E_bound hC hr0 hε)
  exact ⟨hne, _, _, hst, h1, h2, hE0, hEb, h3⟩

lemma pw_lowPackGt1 {p q T : ℝ} (hp : 1 < p) (hq : 0 < q) (hT : 4 ≤ T) (hr1 : 1 < rq p q) :
    ∃ a b : ℝ, 0 < a ∧ 0 < b ∧
    ∀ (N : ℕ) (ε S T0 : ℝ) (m : RowModel (Fin N)) (Q : ℝ → ℝ) (g : ℝ → ℝ),
    4 ≤ N → 0 < ε → ε < clockEps0 p q T → 0 < S → 0 < T0 →
    ContinuousOn g (Ici 0) → (∀ u ∈ Ici (0:ℝ), 0 ≤ g u) → IntegrableOn g (Ioi 0) →
    ∫ u in Ioi (0:ℝ), g u ≤ 1 →
    ContinuousOn (fun u => Q (T0 * u)) (Ici 0) → (∀ u ∈ Ici (0:ℝ), 0 < Q (T0 * u)) →
    (∀ u ∈ Ici (0:ℝ), Q (T0 * u) = fNq (N:ℕ∞) p q u +
          Real.sqrt ε * Muon.Foundations.oneSidedConv (fun v => Real.sqrt (Q (T0 * v))) g u) →
    (∀ u ∈ Icc (0:ℝ) (phaseHeight (Cpq p q) (rq p q) ε),
          Muon.Foundations.oneSidedConv (fun w => Cpq p q * (1 + w) ^ (-rq p q)) g u
            ≤ Real.sqrt ε) →
    (dimHit Q T0 T ε ≠ ⊤ → stepHit m Q T ε = ENNReal.ofReal (S * T0 / (2 * Real.sqrt ε) *
          ∫ u in (0:ℝ)..(dimHit Q T0 T ε).toReal, Real.sqrt (Q (T0 * u)))) →
    dimHit Q T0 T ε ≠ ⊤ ∧ SandwichE a b (S * T0 * phasePi (rq p q) ε) (stepHit m Q T ε) ∧
      ∃ I : ℝ, 0 < I ∧ stepHit m Q T ε = ENNReal.ofReal (S * T0 / (2 * Real.sqrt ε) * I) ∧
        1 / (2 * Real.sqrt 2) ≤ I ∧ |I - Jpq p q| ≤
        (1 / Real.sqrt (2 * (p - 1)) + Cpq p q / (rq p q - 1)) * (N : ℝ) ^ (-(q * (rq p q - 1)))
        + Cpq p q / (rq p q - 1) * (1 + 1 / 2 * Real.log (1 / (2 * T * ε))) ^ (1 - rq p q)
        + Real.sqrt 2 * Cpq p q ^ (1 / rq p q) * ε ^ ((rq p q - 1) / (2 * rq p q)) := by
  have hC := pw_Cpq_pos hp hq
  have hs2 : 0 < Real.sqrt 2 := by positivity
  have hc3 : 0 < Real.sqrt 2 * Cpq p q ^ (1 / rq p q) := by
    have : 0 < Cpq p q ^ (1 / rq p q) := Real.rpow_pos_of_pos hC _
    positivity
  set c3 := Real.sqrt 2 * Cpq p q ^ (1 / rq p q) with hc3d
  refine ⟨1 / (4 * Real.sqrt 2), (|Jpq p q| + c3 + 1) / 2, by positivity, by positivity, ?_⟩
  intro N ε S T0 m Q g hN hε hε0 hS hT0 hgc hgn hgi hgm hYc hYp hYe hconv hstep
  obtain ⟨hne, I, E, hst, hlow, hup, hE0, hE1, hb⟩ := pw_lowGt1 hp hq hT hr1
    N ε S T0 m Q g hN hε hε0 hgc hgn hgi hgm hYc hYp hYe hconv hstep
  have hε4 := pw_eps_lt_quarter hε0
  have hIpos : 0 < I := lt_of_lt_of_le (by positivity) hlow
  have hPi : phasePi (rq p q) ε = ε ^ (-(1 / 2 : ℝ)) := by
    unfold phasePi
    rw [if_neg (by linarith), if_neg (by linarith)]
  have hP : 2 * Real.sqrt ε * ε ^ (-(1 / 2 : ℝ)) = 2 := by
    rw [Real.sqrt_eq_rpow, mul_assoc, ← Real.rpow_add hε]
    norm_num
  have hκ : 0 ≤ (rq p q - 1) / (2 * rq p q) := by
    have := pw_rq_pos hp hq
    apply div_nonneg <;> linarith
  have hεle : ε ^ ((rq p q - 1) / (2 * rq p q)) ≤ 1 :=
    Real.rpow_le_one hε.le (by linarith) hκ
  have hE2 : E ≤ c3 := by
    refine hE1.trans ?_
    calc c3 * ε ^ ((rq p q - 1) / (2 * rq p q)) ≤ c3 * 1 := mul_le_mul_of_nonneg_left hεle hc3.le
      _ = c3 := mul_one _
  refine ⟨hne, ?_, I, hIpos, hst, hlow, ?_⟩
  · rw [hPi]
    have hPpos := Real.rpow_pos_of_pos hε (-(1 / 2 : ℝ))
    refine pw_sandI hS hT0 hPpos hε (by positivity) hst ?_ ?_
    · rw [hP]
      have : 1 / (4 * Real.sqrt 2) * 2 = 1 / (2 * Real.sqrt 2) := by field_simp; ring
      rw [this]; exact hlow
    · rw [hP]
      have := le_abs_self (Jpq p q)
      linarith
  · refine hb.trans ?_
    have := mul_le_mul_of_nonneg_left hεle hc3.le
    have e : Real.sqrt 2 * Cpq p q ^ (1 / rq p q) * ε ^ ((rq p q - 1) / (2 * rq p q)) = c3 * ε ^ ((rq p q - 1) / (2 * rq p q)) := rfl
    rw [e] at hE1 ⊢
    linarith

lemma pw_lowGen {p q T : ℝ} (hp : 1 < p) (hq : 0 < q) (hT : 4 ≤ T) :
    ∃ (cL cH K : ℝ) (Bd : ℕ → ℝ → ℝ), 0 < cL ∧ 0 < cH ∧ 0 ≤ K ∧
      (∀ δ : ℝ, 0 < δ → ∃ (N2 : ℕ) (ε2 : ℝ), 0 < ε2 ∧ ∀ (N : ℕ) (ε : ℝ), N2 ≤ N → 0 < ε →
        ε < ε2 → Bd N ε ≤ δ) ∧
    ∀ (N : ℕ) (ε S T0 : ℝ) (m : RowModel (Fin N)) (Q : ℝ → ℝ) (g : ℝ → ℝ),
    4 ≤ N → 0 < ε → ε < clockEps0 p q T → 0 < S → 0 < T0 →
    ContinuousOn g (Ici 0) → (∀ u ∈ Ici (0:ℝ), 0 ≤ g u) → IntegrableOn g (Ioi 0) →
    ∫ u in Ioi (0:ℝ), g u ≤ 1 →
    ContinuousOn (fun u => Q (T0 * u)) (Ici 0) → (∀ u ∈ Ici (0:ℝ), 0 < Q (T0 * u)) →
    (∀ u ∈ Ici (0:ℝ), Q (T0 * u) = fNq (N:ℕ∞) p q u +
          Real.sqrt ε * Muon.Foundations.oneSidedConv (fun v => Real.sqrt (Q (T0 * v))) g u) →
    (∀ u ∈ Icc (0:ℝ) (phaseHeight (Cpq p q) (rq p q) ε),
          Muon.Foundations.oneSidedConv (fun w => Cpq p q * (1 + w) ^ (-rq p q)) g u
            ≤ Real.sqrt ε) →
    (rq p q ≤ 1 → phaseHeight (Cpq p q) (rq p q) ε ≤ ((N : ℝ) / 4) ^ q) →
    (dimHit Q T0 T ε ≠ ⊤ → stepHit m Q T ε = ENNReal.ofReal (S * T0 / (2 * Real.sqrt ε) *
          ∫ u in (0:ℝ)..(dimHit Q T0 T ε).toReal, Real.sqrt (Q (T0 * u)))) →
    dimHit Q T0 T ε ≠ ⊤ ∧ SandwichE cL cH (S * T0 * phasePi (rq p q) ε) (stepHit m Q T ε) ∧
      (1 ≤ rq p q → ∃ I : ℝ, 0 < I ∧
        stepHit m Q T ε = ENNReal.ofReal (S * T0 / (2 * Real.sqrt ε) * I) ∧
        (rq p q = 1 → |I - aQ q / 2 * Real.log (1 / ε)| ≤ K) ∧
        (1 < rq p q → 1 / (2 * Real.sqrt 2) ≤ I ∧ |I - Jpq p q| ≤ Bd N ε)) := by
  have hC := pw_Cpq_pos hp hq
  have hr0 := pw_rq_pos hp hq
  rcases lt_trichotomy (rq p q) 1 with hlt | heq | hgt
  · obtain ⟨cL, cH, hcL, hcH, hgen⟩ := pw_gen (D := 1) hp hq hT le_rfl hlt
    refine ⟨cL, cH, 0, fun _ _ => 0, hcL, hcH, le_rfl,
      fun δ hδ => ⟨0, 1, one_pos, fun N ε _ _ _ => hδ.le⟩, ?_⟩
    intro N ε S T0 m Q g hN hε hε0 hS hT0 hgc hgn hgi hgm hYc hYp hYe hconv hHN hstep
    have hεC := (pw_eps_facts ε hε0).2
    have hH' := hHN hlt.le
    unfold phaseHeight at hH' hconv
    have key := hgen N ε S T0 m Q g hN hε hε0 hS hT0 hgc hgn hgi hgm hYc hYp hYe
      (pw_conv_a hC hr0 hε hεC hconv) (by rw [one_mul]; exact hH') hstep
    have hPi : phasePi (rq p q) ε = ε ^ (-(1 / (2 * rq p q))) := by
      unfold phasePi; rw [if_pos hlt]
    rw [hPi]
    exact ⟨key.1, key.2, fun h => absurd h (not_le.2 hlt)⟩
  · obtain ⟨a, b, K, ha, hb, hK, hpack⟩ := pw_packEq1 (D := 1) hp hq hT le_rfl heq
    refine ⟨a, b, K, fun _ _ => 0, ha, hb, hK,
      fun δ hδ => ⟨0, 1, one_pos, fun N ε _ _ _ => hδ.le⟩, ?_⟩
    intro N ε S T0 m Q g hN hε hε0 hS hT0 hgc hgn hgi hgm hYc hYp hYe hconv hHN hstep
    have hεC := (pw_eps_facts ε hε0).2
    have hH' := hHN heq.le
    have hca := pw_conv_a hC hr0 hε hεC hconv
    unfold phaseHeight at hH' hca
    rw [heq] at hH' hca
    have key := hpack N ε S T0 m Q g hN hε hε0 hS hT0 hgc hgn hgi hgm hYc hYp hYe
      hca (by rw [one_mul]; exact hH') hstep
    obtain ⟨hne, hsand, I, hI, hst, hbd⟩ := key
    exact ⟨hne, hsand, fun _ => ⟨I, hI, hst, fun _ => hbd, fun h => absurd h (not_lt.2 heq.le)⟩⟩
  · obtain ⟨a, b, ha, hb, hpack⟩ := pw_lowPackGt1 hp hq hT hgt
    refine ⟨a, b, 0, fun N ε =>
      (1 / Real.sqrt (2 * (p - 1)) + Cpq p q / (rq p q - 1)) * (N : ℝ) ^ (-(q * (rq p q - 1)))
        + Cpq p q / (rq p q - 1) * (1 + 1 / 2 * Real.log (1 / (2 * T * ε))) ^ (1 - rq p q)
        + Real.sqrt 2 * Cpq p q ^ (1 / rq p q) * ε ^ ((rq p q - 1) / (2 * rq p q)),
      ha, hb, le_rfl, ?_, ?_⟩
    · exact pw_Bd_small (r := rq p q) (κ1 := q * (rq p q - 1))
        (κ := (rq p q - 1) / (2 * rq p q)) (T := T)
        (c1 := 1 / Real.sqrt (2 * (p - 1)) + Cpq p q / (rq p q - 1))
        (c2 := Cpq p q / (rq p q - 1)) (c3 := Real.sqrt 2 * Cpq p q ^ (1 / rq p q))
        hgt (mul_pos hq (by linarith)) (div_pos (by linarith) (by linarith)) (by linarith)
    · intro N ε S T0 m Q g hN hε hε0 hS hT0 hgc hgn hgi hgm hYc hYp hYe hconv _ hstep
      obtain ⟨hne, hsand, I, hI, hst, hlow, hbd⟩ := hpack N ε S T0 m Q g hN hε hε0 hS hT0
        hgc hgn hgi hgm hYc hYp hYe hconv hstep
      exact ⟨hne, hsand, fun _ => ⟨I, hI, hst, fun h => absurd h (ne_of_gt hgt),
        fun _ => ⟨hlow, hbd⟩⟩⟩

lemma pw_lowSvd (α ς T : ℝ) (hα : 0 < α) (hς : 1 ≤ ς) (hT : 4 ≤ T) :
    ∃ (cL cH K : ℝ) (Bd : ℕ → ℝ → ℝ), 0 < cL ∧ 0 < cH ∧ 0 ≤ K ∧
      (∀ δ : ℝ, 0 < δ → ∃ (N2 : ℕ) (ε2 : ℝ), 0 < ε2 ∧ ∀ (N : ℕ) (ε : ℝ), N2 ≤ N → 0 < ε →
        ε < ε2 → Bd N ε ≤ δ) ∧
      ∀ (N B : ℕ) (ε : ℝ) (mS mG : RowModel (Fin N)) (QS QG : ℝ → ℝ), 4 ≤ N → N ≤ B →
        0 < ε → ε < clockEps0 (α + ς) (α / 2) T →
        phaseKsvd α N * Cpq (α + ς) (α / 2) *
          Ir (rq (α + ς) (α / 2)) (phaseHeight (Cpq (α + ς) (α / 2)) (rq (α + ς) (α / 2)) ε)
            ≤ Real.sqrt ε →
        (rq (α + ς) (α / 2) ≤ 1 →
          phaseHeight (Cpq (α + ς) (α / 2)) (rq (α + ς) (α / 2)) ε ≤ ((N : ℝ) / 4) ^ (α / 2)) →
        IsMatchedModel (svdArrays α ς N B) mS ε → IsVolterraSol mS QS →
        IsMatchedModel (sgdArrays α ς N B) mG ε → IsVolterraSol mG QG →
        (dimHit QS (svdT0 N B) T ε ≠ ⊤ → stepHit mS QS T ε = ENNReal.ofReal
          (mS.S * svdT0 N B / (2 * Real.sqrt ε) *
            ∫ u in (0:ℝ)..(dimHit QS (svdT0 N B) T ε).toReal,
              Real.sqrt (QS (svdT0 N B * u)))) →
        dimHit QS (svdT0 N B) T ε ≠ ⊤ ∧
        SandwichE cL cH ((svdArrays α ς N B).S * svdT0 N B *
          phasePi (rq (α + ς) (α / 2)) ε) (stepHit mS QS T ε) ∧
        (1 ≤ rq (α + ς) (α / 2) → ∃ I : ℝ, 0 < I ∧ stepHit mS QS T ε = ENNReal.ofReal
            ((svdArrays α ς N B).S * svdT0 N B / (2 * Real.sqrt ε) * I) ∧
          (rq (α + ς) (α / 2) = 1 → |I - aQ (α / 2) / 2 * Real.log (1 / ε)| ≤ K) ∧
          (1 < rq (α + ς) (α / 2) → 1 / (2 * Real.sqrt 2) ≤ I ∧
            |I - Jpq (α + ς) (α / 2)| ≤ Bd N ε)) := by
  have hp : 1 < α + ς := by linarith
  have hq : 0 < α / 2 := by linarith
  obtain ⟨cL, cH, K, Bd, hcL, hcH, hK, hsm, hgen⟩ := pw_lowGen hp hq hT
  refine ⟨cL, cH, K, Bd, hcL, hcH, hK, hsm, ?_⟩
  intro N B ε mS mG QS QG hN hNB hε hε0 hk hHN hmS hQS hmG hQG hstep
  have hN1' : 1 ≤ N := by omega
  have hN0' : (0:ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hB0 : (0:ℝ) < B := by exact_mod_cast (by omega : 0 < B)
  have hT0 : 0 < svdT0 N B := by
    unfold svdT0 gammaRat; exact Real.sqrt_pos.2 (by positivity)
  have hS : 0 < mS.S := by
    rw [pw_S_eq α ς N _ mS ε hmS]
    obtain ⟨h1, -⟩ := prop_app_phase_prefactors_i α ς N B hα hp hN1' hNB ε hε
    rw [h1]
    have h2 : 0 < Real.sqrt (gammaRat N B) := Real.sqrt_pos.2 (by unfold gammaRat; positivity)
    have h3 := pw_Hsum_ge_one (α / 2) N hN1'
    positivity
  obtain ⟨hgc, hgn, hgi, hgm, hgk, hYe⟩ := pw_svd_facts α ς N B hα hp hN1' hNB ε hε mS mG hmS hmG QS QG hQS hQG
  obtain ⟨⟨-, -, -, -, -, hmax, h0⟩, -⟩ :=
    prop_app_phase_prefactors_ii_props α ς N B hα hp hN1' hNB ε hε mS mG hmS hmG
  have hgle : ∀ u ∈ Ici (0:ℝ), dimKernel mS (svdT0 N B) ε u ≤ phaseKsvd α N := by
    intro u hu
    rw [← h0]
    exact isMaxOn_iff.1 hmax u hu
  obtain ⟨hYc, hYp⟩ := pw_Q_facts mS QS hQS _ hT0
  have hr0 := pw_rq_pos hp hq
  have hεC := (pw_eps_facts ε hε0).2
  have hH0 := (pw_lowh (pw_Cpq_pos hp hq) hr0 hε hεC).1
  have hconv := pw_lowConvB (pw_Cpq_pos hp hq) hgc hgn hgle hH0.le hk
  have key := hgen N ε mS.S (svdT0 N B) mS QS (dimKernel mS (svdT0 N B) ε) hN hε hε0 hS hT0
    hgc hgn hgi hgm hYc hYp hYe hconv hHN hstep
  rw [pw_S_eq α ς N _ mS ε hmS] at key
  exact key

lemma pw_lowSgd (α ς T : ℝ) (hα : 0 < α) (hς : 1 ≤ ς) (hT : 4 ≤ T) :
    ∃ (cL cH K : ℝ) (Bd : ℕ → ℝ → ℝ), 0 < cL ∧ 0 < cH ∧ 0 ≤ K ∧
      (∀ δ : ℝ, 0 < δ → ∃ (N2 : ℕ) (ε2 : ℝ), 0 < ε2 ∧ ∀ (N : ℕ) (ε : ℝ), N2 ≤ N → 0 < ε →
        ε < ε2 → Bd N ε ≤ δ) ∧
      ∀ (N B : ℕ) (ε : ℝ) (mS mG : RowModel (Fin N)) (QS QG : ℝ → ℝ), 4 ≤ N → N ≤ B →
        0 < ε → ε < clockEps0 (α + ς) α T →
        phaseKsgd α N * Cpq (α + ς) α *
          Ir (rq (α + ς) α) (phaseHeight (Cpq (α + ς) α) (rq (α + ς) α) ε)
            ≤ Real.sqrt ε →
        (rq (α + ς) α ≤ 1 →
          phaseHeight (Cpq (α + ς) α) (rq (α + ς) α) ε ≤ ((N : ℝ) / 4) ^ α) →
        IsMatchedModel (svdArrays α ς N B) mS ε → IsVolterraSol mS QS →
        IsMatchedModel (sgdArrays α ς N B) mG ε → IsVolterraSol mG QG →
        (dimHit QG (sgdT0 α N B) T ε ≠ ⊤ → stepHit mG QG T ε = ENNReal.ofReal
          (mG.S * sgdT0 α N B / (2 * Real.sqrt ε) *
            ∫ u in (0:ℝ)..(dimHit QG (sgdT0 α N B) T ε).toReal,
              Real.sqrt (QG (sgdT0 α N B * u)))) →
        dimHit QG (sgdT0 α N B) T ε ≠ ⊤ ∧
        SandwichE cL cH ((sgdArrays α ς N B).S * sgdT0 α N B *
          phasePi (rq (α + ς) α) ε) (stepHit mG QG T ε) ∧
        (1 ≤ rq (α + ς) α → ∃ I : ℝ, 0 < I ∧ stepHit mG QG T ε = ENNReal.ofReal
            ((sgdArrays α ς N B).S * sgdT0 α N B / (2 * Real.sqrt ε) * I) ∧
          (rq (α + ς) α = 1 → |I - aQ α / 2 * Real.log (1 / ε)| ≤ K) ∧
          (1 < rq (α + ς) α → 1 / (2 * Real.sqrt 2) ≤ I ∧
            |I - Jpq (α + ς) α| ≤ Bd N ε)) := by
  have hp : 1 < α + ς := by linarith
  obtain ⟨cL, cH, K, Bd, hcL, hcH, hK, hsm, hgen⟩ := pw_lowGen hp hα hT
  refine ⟨cL, cH, K, Bd, hcL, hcH, hK, hsm, ?_⟩
  intro N B ε mS mG QS QG hN hNB hε hε0 hk hHN hmS hQS hmG hQG hstep
  have hN1' : 1 ≤ N := by omega
  have hN0' : (0:ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hB0 : (0:ℝ) < B := by exact_mod_cast (by omega : 0 < B)
  have hmuB := pw_muBar_pos α hN1'
  have hT0 : 0 < sgdT0 α N B := by
    unfold sgdT0; exact Real.sqrt_pos.2 (by positivity)
  have hS : 0 < mG.S := by
    rw [pw_S_eq α ς N _ mG ε hmG]
    obtain ⟨-, -, h3, -⟩ := prop_app_phase_prefactors_i α ς N B hα hp hN1' hNB ε hε
    rw [h3]
    have : 0 < Real.sqrt (Real.pi * muBarOf α N / (B : ℝ)) := Real.sqrt_pos.2 (by positivity)
    positivity
  obtain ⟨hgc, hgn, -, hgi, hgm, hYe⟩ := pw_sgd_facts α ς N B hα hp hN1' hNB ε hε mS mG hmS hmG QS QG hQS hQG
  obtain ⟨-, ⟨-, -, -, hmax, h0, -⟩⟩ :=
    prop_app_phase_prefactors_ii_props α ς N B hα hp hN1' hNB ε hε mS mG hmS hmG
  have hgle : ∀ u ∈ Ici (0:ℝ), dimKernel mG (sgdT0 α N B) ε u ≤ phaseKsgd α N := by
    intro u hu
    rw [← h0]
    exact isMaxOn_iff.1 hmax u hu
  obtain ⟨hYc, hYp⟩ := pw_Q_facts mG QG hQG _ hT0
  have hr0 := pw_rq_pos hp hα
  have hεC := (pw_eps_facts ε hε0).2
  have hH0 := (pw_lowh (pw_Cpq_pos hp hα) hr0 hε hεC).1
  have hconv := pw_lowConvB (pw_Cpq_pos hp hα) hgc hgn hgle hH0.le hk
  have key := hgen N ε mG.S (sgdT0 α N B) mG QG (dimKernel mG (sgdT0 α N B) ε) hN hε hε0 hS hT0
    hgc hgn hgi hgm hYc hYp hYe hconv hHN hstep
  rw [pw_S_eq α ς N _ mG ε hmG] at key
  exact key

lemma pw_thm_C (α ς T : ℝ) (hα : 0 < α) (hς : 1 ≤ ς) (hT : 4 ≤ T) :
    ∃ cLo cHi : ℝ, 0 < cLo ∧ cLo ≤ cHi ∧
      ∀ (N B : ℕ) (ε : ℝ) (mS mG : RowModel (Fin N)) (QS QG : ℝ → ℝ),
        PhaseLowWindow α ς T N B ε →
        IsMatchedModel (svdArrays α ς N B) mS ε → IsVolterraSol mS QS →
        IsMatchedModel (sgdArrays α ς N B) mG ε → IsVolterraSol mG QG →
        (dimHit QS (svdT0 N B) T ε ≠ ⊤ ∧ dimHit QG (sgdT0 α N B) T ε ≠ ⊤) ∧
        SandwichE cLo cHi ((svdArrays α ς N B).S * svdT0 N B *
            phasePi (rq (α + ς) (α / 2)) ε) (stepHit mS QS T ε) ∧
        SandwichE cLo cHi ((sgdArrays α ς N B).S * sgdT0 α N B *
            phasePi (rq (α + ς) α) ε) (stepHit mG QG T ε) := by
  have hp : 1 < α + ς := by linarith
  obtain ⟨cL1, cH1, K1, Bd1, hcL1, hcH1, hK1, hsm1, h1⟩ := pw_lowSvd α ς T hα hς hT
  obtain ⟨cL2, cH2, K2, Bd2, hcL2, hcH2, hK2, hsm2, h2⟩ := pw_lowSgd α ς T hα hς hT
  set cLo : ℝ := min cL1 cL2 with hcLo
  set cHi : ℝ := max (max cH1 cH2) cLo with hcHi
  refine ⟨cLo, cHi, lt_min hcL1 hcL2, le_max_right _ _, ?_⟩
  intro N B ε mS mG QS QG hW hmS hQS hmG hQG
  obtain ⟨hN4, hNB, hε, hε0, hk1, hk2, hH1, hH2⟩ := hW
  have hε0' : ε < clockEps0 (α + ς) (α / 2) T ∧ ε < clockEps0 (α + ς) α T := by
    unfold phaseEps0 at hε0
    exact lt_min_iff.1 hε0
  have hN1' : 1 ≤ N := by omega
  have hpref := prop_app_phase_prefactors_iii α ς N B hα hp hN1' hNB ε T hε (by linarith) mS mG hmS hmG QS QG hQS hQG
  obtain ⟨hne1, hsand1, -⟩ := h1 N B ε mS mG QS QG hN4 hNB hε hε0'.1 hk1 hH1 hmS hQS hmG hQG hpref.1
  obtain ⟨hne2, hsand2, -⟩ := h2 N B ε mS mG QS QG hN4 hNB hε hε0'.2 hk2 hH2 hmS hQS hmG hQG hpref.2
  exact ⟨⟨hne1, hne2⟩,
    pw_sandwich_mono hsand1 (min_le_left _ _) ((le_max_left _ _).trans (le_max_left _ _)),
    pw_sandwich_mono hsand2 (min_le_right _ _) ((le_max_right _ _).trans (le_max_left _ _))⟩

lemma pw_thm_C_ii (α ς T : ℝ) (hα : 0 < α) (hς : 1 ≤ ς) (hT : 4 ≤ T) :
    ∀ (Nseq Bseq : ℕ → ℕ) (εseq : ℕ → ℝ)
      (mS mG : ∀ n, RowModel (Fin (Nseq n))) (QS QG : ∀ n, ℝ → ℝ),
      Tendsto (fun n => (Nseq n : ℝ)) atTop atTop → Tendsto εseq atTop (𝓝 0) →
      (∀ n, 0 < εseq n) → (∀ n, 1 ≤ Nseq n) → (∀ n, Nseq n ≤ Bseq n) →
      (∀ n, IsMatchedModel (svdArrays α ς (Nseq n) (Bseq n)) (mS n) (εseq n)) →
      (∀ n, IsVolterraSol (mS n) (QS n)) →
      (∀ n, IsMatchedModel (sgdArrays α ς (Nseq n) (Bseq n)) (mG n) (εseq n)) →
      (∀ n, IsVolterraSol (mG n) (QG n)) →
      (∀ᶠ n in atTop, PhaseLowWindow α ς T (Nseq n) (Bseq n) (εseq n)) →
      (rq (α + ς) (α / 2) = 1 →
        IsEquivalent atTop (fun n => (stepHit (mS n) (QS n) T (εseq n)).toReal)
          (fun n => (svdArrays α ς (Nseq n) (Bseq n)).S * svdT0 (Nseq n) (Bseq n) /
            (4 * Real.sqrt (8 * (α / 2))) * (εseq n) ^ (-(1 / 2 : ℝ)) *
            Real.log (1 / εseq n))) ∧
      (1 < rq (α + ς) (α / 2) →
        IsEquivalent atTop (fun n => (stepHit (mS n) (QS n) T (εseq n)).toReal)
          (fun n => (svdArrays α ς (Nseq n) (Bseq n)).S * svdT0 (Nseq n) (Bseq n) *
            Jpq (α + ς) (α / 2) / (2 * Real.sqrt (εseq n)))) ∧
      (rq (α + ς) α = 1 →
        IsEquivalent atTop (fun n => (stepHit (mG n) (QG n) T (εseq n)).toReal)
          (fun n => (sgdArrays α ς (Nseq n) (Bseq n)).S * sgdT0 α (Nseq n) (Bseq n) /
            (4 * Real.sqrt (8 * α)) * (εseq n) ^ (-(1 / 2 : ℝ)) *
            Real.log (1 / εseq n))) ∧
      (1 < rq (α + ς) α →
        IsEquivalent atTop (fun n => (stepHit (mG n) (QG n) T (εseq n)).toReal)
          (fun n => (sgdArrays α ς (Nseq n) (Bseq n)).S * sgdT0 α (Nseq n) (Bseq n) *
            Jpq (α + ς) α / (2 * Real.sqrt (εseq n)))) := by
  have hp : 1 < α + ς := by linarith
  obtain ⟨cL1, cH1, K1, Bd1, hcL1, hcH1, hK1, hsm1, h1⟩ := pw_lowSvd α ς T hα hς hT
  obtain ⟨cL2, cH2, K2, Bd2, hcL2, hcH2, hK2, hsm2, h2⟩ := pw_lowSgd α ς T hα hς hT
  intro Nseq Bseq εseq mS mG QS QG hN hε hε0 hN1' hNB hmS hQS hmG hQG hwin
  have hargs : ∀ (N B : ℕ) (ε : ℝ), PhaseLowWindow α ς T N B ε →
      4 ≤ N ∧ N ≤ B ∧ 0 < ε ∧ ε < clockEps0 (α + ς) (α / 2) T ∧
        ε < clockEps0 (α + ς) α T := by
    rintro N B ε ⟨hN4, hNB, hε, hε0, -⟩
    have hε0' : ε < clockEps0 (α + ς) (α / 2) T ∧ ε < clockEps0 (α + ς) α T := by
      unfold phaseEps0 at hε0
      exact lt_min_iff.1 hε0
    exact ⟨hN4, hNB, hε, hε0'.1, hε0'.2⟩
  have hevS : ∀ᶠ n in atTop,
      0 < (svdArrays α ς (Nseq n) (Bseq n)).S * svdT0 (Nseq n) (Bseq n) ∧
      (1 ≤ rq (α + ς) (α / 2) → ∃ I : ℝ, 0 < I ∧ stepHit (mS n) (QS n) T (εseq n) = ENNReal.ofReal
        ((svdArrays α ς (Nseq n) (Bseq n)).S * svdT0 (Nseq n) (Bseq n) / (2 * Real.sqrt (εseq n)) * I) ∧
        (rq (α + ς) (α / 2) = 1 → |I - aQ (α / 2) / 2 * Real.log (1 / εseq n)| ≤ K1) ∧
        (1 < rq (α + ς) (α / 2) → 1 / (2 * Real.sqrt 2) ≤ I ∧
          |I - Jpq (α + ς) (α / 2)| ≤ Bd1 (Nseq n) (εseq n))) := by
    filter_upwards [hwin] with n hW
    obtain ⟨hN4, hNB', hε', hε1, hε2⟩ := hargs (Nseq n) (Bseq n) (εseq n) hW
    obtain ⟨-, -, -, -, hk1, -, hH1, -⟩ := hW
    have hN1'' : 1 ≤ Nseq n := hN1' n
    have hpref := prop_app_phase_prefactors_iii α ς (Nseq n) (Bseq n) hα hp hN1'' hNB' (εseq n) T hε'
      (by linarith) (mS n) (mG n) (hmS n) (hmG n) (QS n) (QG n) (hQS n) (hQG n)
    obtain ⟨-, -, hR⟩ := h1 (Nseq n) (Bseq n) (εseq n) (mS n) (mG n) (QS n) (QG n) hN4 hNB' hε' hε1
      hk1 hH1 (hmS n) (hQS n) (hmG n) (hQG n) hpref.1
    exact ⟨pw_svd_ST_pos α ς (Nseq n) (Bseq n) hα hp hN1'' hNB' (εseq n) hε' (mS n) (hmS n), hR⟩
  have hevG : ∀ᶠ n in atTop,
      0 < (sgdArrays α ς (Nseq n) (Bseq n)).S * sgdT0 α (Nseq n) (Bseq n) ∧
      (1 ≤ rq (α + ς) α → ∃ I : ℝ, 0 < I ∧ stepHit (mG n) (QG n) T (εseq n) = ENNReal.ofReal
        ((sgdArrays α ς (Nseq n) (Bseq n)).S * sgdT0 α (Nseq n) (Bseq n) / (2 * Real.sqrt (εseq n)) * I) ∧
        (rq (α + ς) α = 1 → |I - aQ α / 2 * Real.log (1 / εseq n)| ≤ K2) ∧
        (1 < rq (α + ς) α → 1 / (2 * Real.sqrt 2) ≤ I ∧
          |I - Jpq (α + ς) α| ≤ Bd2 (Nseq n) (εseq n))) := by
    filter_upwards [hwin] with n hW
    obtain ⟨hN4, hNB', hε', hε1, hε2⟩ := hargs (Nseq n) (Bseq n) (εseq n) hW
    obtain ⟨-, -, -, -, -, hk2, -, hH2⟩ := hW
    have hN1'' : 1 ≤ Nseq n := hN1' n
    have hpref := prop_app_phase_prefactors_iii α ς (Nseq n) (Bseq n) hα hp hN1'' hNB' (εseq n) T hε'
      (by linarith) (mS n) (mG n) (hmS n) (hmG n) (QS n) (QG n) (hQS n) (hQG n)
    obtain ⟨-, -, hR⟩ := h2 (Nseq n) (Bseq n) (εseq n) (mS n) (mG n) (QS n) (QG n) hN4 hNB' hε' hε2
      hk2 hH2 (hmS n) (hQS n) (hmG n) (hQG n) hpref.2
    exact ⟨pw_sgd_ST_pos α ς (Nseq n) (Bseq n) hα hp hN1'' hNB' (εseq n) hε' (mG n) (hmG n), hR⟩
  -- conversion of the step time
  have hconvS : ∀ n, 0 < (svdArrays α ς (Nseq n) (Bseq n)).S * svdT0 (Nseq n) (Bseq n) →
      ∀ I : ℝ, 0 < I → stepHit (mS n) (QS n) T (εseq n) = ENNReal.ofReal
        ((svdArrays α ς (Nseq n) (Bseq n)).S * svdT0 (Nseq n) (Bseq n) / (2 * Real.sqrt (εseq n)) * I) →
      (stepHit (mS n) (QS n) T (εseq n)).toReal =
        (svdArrays α ς (Nseq n) (Bseq n)).S * svdT0 (Nseq n) (Bseq n) / (2 * Real.sqrt (εseq n)) * I := by
    intro n hST I hI hst
    have hs : 0 < Real.sqrt (εseq n) := Real.sqrt_pos.2 (hε0 n)
    rw [hst, ENNReal.toReal_ofReal]
    positivity
  have hconvG : ∀ n, 0 < (sgdArrays α ς (Nseq n) (Bseq n)).S * sgdT0 α (Nseq n) (Bseq n) →
      ∀ I : ℝ, 0 < I → stepHit (mG n) (QG n) T (εseq n) = ENNReal.ofReal
        ((sgdArrays α ς (Nseq n) (Bseq n)).S * sgdT0 α (Nseq n) (Bseq n) / (2 * Real.sqrt (εseq n)) * I) →
      (stepHit (mG n) (QG n) T (εseq n)).toReal =
        (sgdArrays α ς (Nseq n) (Bseq n)).S * sgdT0 α (Nseq n) (Bseq n) / (2 * Real.sqrt (εseq n)) * I := by
    intro n hST I hI hst
    have hs : 0 < Real.sqrt (εseq n) := Real.sqrt_pos.2 (hε0 n)
    rw [hst, ENNReal.toReal_ofReal]
    positivity
  have haS : ∀ᶠ n in atTop, 0 < (svdArrays α ς (Nseq n) (Bseq n)).S * svdT0 (Nseq n) (Bseq n) /
      (2 * Real.sqrt (εseq n)) := by
    filter_upwards [hevS] with n hn
    have hs : 0 < Real.sqrt (εseq n) := Real.sqrt_pos.2 (hε0 n)
    have := hn.1
    positivity
  have haG : ∀ᶠ n in atTop, 0 < (sgdArrays α ς (Nseq n) (Bseq n)).S * sgdT0 α (Nseq n) (Bseq n) /
      (2 * Real.sqrt (εseq n)) := by
    filter_upwards [hevG] with n hn
    have hs : 0 < Real.sqrt (εseq n) := Real.sqrt_pos.2 (hε0 n)
    have := hn.1
    positivity
  refine ⟨fun hr1 => ?_, fun hr1 => ?_, fun hr1 => ?_, fun hr1 => ?_⟩
  · have hq : 0 < α / 2 := by linarith
    have hL : Tendsto (fun n => aQ (α / 2) / 2 * Real.log (1 / εseq n)) atTop atTop :=
      (pw_log_tendsto hε hε0).const_mul_atTop (by unfold aQ; positivity)
    have key := pw_eqv1 (u := fun n => (stepHit (mS n) (QS n) T (εseq n)).toReal)
      (a := fun n => (svdArrays α ς (Nseq n) (Bseq n)).S * svdT0 (Nseq n) (Bseq n) /
        (2 * Real.sqrt (εseq n))) (K := K1) haS ?_ hL
    · refine key.congr_right (Filter.Eventually.of_forall fun n => ?_)
      exact (pw_target1 hq (hε0 n)).symm
    · filter_upwards [hevS] with n hn
      obtain ⟨hST, hI'⟩ := hn
      obtain ⟨I, hI, hst, hb, -⟩ := hI' hr1.ge
      exact ⟨I, hconvS n hST I hI hst, hb hr1⟩
  · have key := pw_eqv2 (u := fun n => (stepHit (mS n) (QS n) T (εseq n)).toReal)
      (a := fun n => (svdArrays α ς (Nseq n) (Bseq n)).S * svdT0 (Nseq n) (Bseq n) /
        (2 * Real.sqrt (εseq n))) (J := Jpq (α + ς) (α / 2)) haS ?_
    · refine key.congr_right (Filter.Eventually.of_forall fun n => ?_)
      ring
    · intro δ hδ
      obtain ⟨N2', ε2, hε2, hbd⟩ := hsm1 δ hδ
      have e1 : ∀ᶠ n in atTop, (N2' : ℝ) ≤ (Nseq n : ℝ) := hN.eventually_ge_atTop _
      have e2 : ∀ᶠ n in atTop, εseq n < ε2 := (tendsto_order.1 hε).2 _ hε2
      filter_upwards [hevS, e1, e2] with n hn a b
      obtain ⟨hST, hI'⟩ := hn
      obtain ⟨I, hI, hst, -, hb⟩ := hI' hr1.le
      obtain ⟨hl, hb'⟩ := hb hr1
      exact ⟨I, hconvS n hST I hI hst, hl, hb'.trans (hbd (Nseq n) (εseq n) (by exact_mod_cast a) (hε0 n) b)⟩
  · have hq : 0 < α := hα
    have hL : Tendsto (fun n => aQ α / 2 * Real.log (1 / εseq n)) atTop atTop :=
      (pw_log_tendsto hε hε0).const_mul_atTop (by unfold aQ; positivity)
    have key := pw_eqv1 (u := fun n => (stepHit (mG n) (QG n) T (εseq n)).toReal)
      (a := fun n => (sgdArrays α ς (Nseq n) (Bseq n)).S * sgdT0 α (Nseq n) (Bseq n) /
        (2 * Real.sqrt (εseq n))) (K := K2) haG ?_ hL
    · refine key.congr_right (Filter.Eventually.of_forall fun n => ?_)
      exact (pw_target1 hq (hε0 n)).symm
    · filter_upwards [hevG] with n hn
      obtain ⟨hST, hI'⟩ := hn
      obtain ⟨I, hI, hst, hb, -⟩ := hI' hr1.ge
      exact ⟨I, hconvG n hST I hI hst, hb hr1⟩
  · have key := pw_eqv2 (u := fun n => (stepHit (mG n) (QG n) T (εseq n)).toReal)
      (a := fun n => (sgdArrays α ς (Nseq n) (Bseq n)).S * sgdT0 α (Nseq n) (Bseq n) /
        (2 * Real.sqrt (εseq n))) (J := Jpq (α + ς) α) haG ?_
    · refine key.congr_right (Filter.Eventually.of_forall fun n => ?_)
      ring
    · intro δ hδ
      obtain ⟨N2', ε2, hε2, hbd⟩ := hsm2 δ hδ
      have e1 : ∀ᶠ n in atTop, (N2' : ℝ) ≤ (Nseq n : ℝ) := hN.eventually_ge_atTop _
      have e2 : ∀ᶠ n in atTop, εseq n < ε2 := (tendsto_order.1 hε).2 _ hε2
      filter_upwards [hevG, e1, e2] with n hn a b
      obtain ⟨hST, hI'⟩ := hn
      obtain ⟨I, hI, hst, -, hb⟩ := hI' hr1.le
      obtain ⟨hl, hb'⟩ := hb hr1
      exact ⟨I, hconvG n hST I hI hst, hl, hb'.trans (hbd (Nseq n) (εseq n) (by exact_mod_cast a) (hε0 n) b)⟩



/-- Label `thm:app-phase-C`, declaration of record. Snapshot `cr-2026-10-23`.

Statement (verbatim, `sections/07-phase-comparison/section.tex`, l.1305–1315):

```latex
\begin{theorem}[Low covariance exponents]\label{thm:app-phase-C}
Fix $0<\alpha\le1$, $\texp\ge1$ and $T\ge4$. There are $0<c_-\le c_+$, depending
only on $\alpha$, $\texp$ and $T$, such that for every $(N,B,\epsilon)$ in
the low-exponent window \cref{eqn:app-phase-height}, and for both $j$, the
first hit $\hat u_j$ is attained and
\[
c_-\le\frac{t^j_{T\epsilon}}{\mathcal S_jT_0^j\,\Pi_{r_j}(\epsilon)}\le c_+ .
\]
Along every sequence with $N\to\infty$ and $\epsilon\downarrow0$ in this
window, the equivalents \cref{eqn:app-phase-equivalents} hold.
\end{theorem}
```
-/
theorem thm_app_phase_C (α ς T : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (hς : 1 ≤ ς) (hT : 4 ≤ T) :
    ∃ cLo cHi : ℝ, 0 < cLo ∧ cLo ≤ cHi ∧
      ∀ (N B : ℕ) (ε : ℝ) (mS mG : RowModel (Fin N)) (QS QG : ℝ → ℝ),
        PhaseLowWindow α ς T N B ε →
        IsMatchedModel (svdArrays α ς N B) mS ε → IsVolterraSol mS QS →
        IsMatchedModel (sgdArrays α ς N B) mG ε → IsVolterraSol mG QG →
        (dimHit QS (svdT0 N B) T ε ≠ ⊤ ∧ dimHit QG (sgdT0 α N B) T ε ≠ ⊤) ∧
        SandwichE cLo cHi ((svdArrays α ς N B).S * svdT0 N B *
            phasePi (rq (α + ς) (α / 2)) ε) (stepHit mS QS T ε) ∧
        SandwichE cLo cHi ((sgdArrays α ς N B).S * sgdT0 α N B *
            phasePi (rq (α + ς) α) ε) (stepHit mG QG T ε) := by
  exact pw_thm_C α ς T hα hς hT


/-! ### Phase-map assembly helpers (P-H.8.P5) -/

lemma pm_half_scale {cLo cHi X : ℝ} {t : ℝ≥0∞}
    (h : SandwichE cLo cHi (X / 2) t) :
    SandwichE (cLo / 2) (cHi / 2) X t := by
  have he (c : ℝ) : ENNReal.ofReal (c / 2) * ENNReal.ofReal X =
      ENNReal.ofReal c * ENNReal.ofReal (X / 2) := by
    simp only [div_eq_mul_inv, ENNReal.ofReal_mul' (by norm_num : (0 : ℝ) ≤ (2 : ℝ)⁻¹)]
    ac_rfl
  exact ⟨by simpa only [he] using h.1, by simpa only [he] using h.2⟩

lemma pm_map_high_sandwich (α ς T : ℝ) (hα : 0 < α) (hς : 1 < ς)
    (N B : ℕ) (ε cLo cHi : ℝ) (hN : 1 ≤ N) (hNB : N ≤ B) (hε : 0 < ε)
    (hcLo : 0 < cLo) (hc : cLo ≤ cHi)
    (mS mG : RowModel (Fin N)) (QS QG : ℝ → ℝ)
    (hS : SandwichE cLo cHi ((svdArrays α ς N B).S * svdT0 N B *
      phasePi (rq (α + ς) (α / 2)) ε) (stepHit mS QS T ε))
    (hG : SandwichE cLo cHi ((sgdArrays α ς N B).S * sgdT0 α N B *
      phasePi (rq (α + ς) α) ε) (stepHit mG QG T ε)) :
    SandwichE (cLo / 2) cHi
      (Real.sqrt (gammaRat N B) * (svdArrays α ς N B).S * ε ^ (-(1 / 2 : ℝ)))
      (stepHit mS QS T ε) ∧
    (ς < α + 1 → SandwichE (cLo / 2) cHi
      ((N : ℝ) ^ 2 * (Real.pi * muBarOf α N / (B : ℝ)) * ε ^ (-(α / (α + ς - 1))))
      (stepHit mG QG T ε)) ∧
    (α + 1 < ς → SandwichE (cLo / 2) cHi
      (Real.sqrt (Real.pi * muBarOf α N / (B : ℝ)) * (sgdArrays α ς N B).S *
        ε ^ (-(1 / 2 : ℝ))) (stepHit mG QG T ε)) := by
  have hp : 1 < α + ς := by linarith
  have hrS : 1 < rq (α + ς) (α / 2) := by
    unfold rq
    rw [lt_div_iff₀ (by linarith : 0 < 2 * (α / 2))]
    linarith
  have hPiS : phasePi (rq (α + ς) (α / 2)) ε = ε ^ (-(1 / 2 : ℝ)) := by
    simp only [phasePi, if_neg (not_lt.mpr hrS.le), if_neg (ne_of_gt hrS)]
  have heS : (svdArrays α ς N B).S * svdT0 N B * phasePi (rq (α + ς) (α / 2)) ε =
      Real.sqrt (gammaRat N B) * (svdArrays α ς N B).S * ε ^ (-(1 / 2 : ℝ)) := by
    rw [hPiS]
    unfold svdT0
    ring
  refine ⟨?_, ?_, ?_⟩
  · rw [heS] at hS
    exact pw_sandwich_mono hS (by linarith) le_rfl
  · intro hςα
    have hrG : rq (α + ς) α < 1 := by
      unfold rq
      rw [div_lt_iff₀ (by positivity : 0 < 2 * α)]
      linarith
    have he : 1 / (2 * rq (α + ς) α) = α / (α + ς - 1) := by
      unfold rq
      field_simp
    obtain ⟨_, _, _, _, _, hST, _, _⟩ :=
      prop_app_phase_prefactors_i α ς N B hα hp hN hNB ε hε
    have heG : (sgdArrays α ς N B).S * sgdT0 α N B * phasePi (rq (α + ς) α) ε =
        ((N : ℝ) ^ 2 * (Real.pi * muBarOf α N / (B : ℝ)) *
          ε ^ (-(α / (α + ς - 1)))) / 2 := by
      rw [phasePi, if_pos hrG, he, hST]
      ring
    rw [heG] at hG
    exact pw_sandwich_mono (pm_half_scale hG) le_rfl (by linarith)
  · intro hςα
    have hrG : 1 < rq (α + ς) α := by
      unfold rq
      rw [lt_div_iff₀ (by positivity : 0 < 2 * α)]
      linarith
    have hPiG : phasePi (rq (α + ς) α) ε = ε ^ (-(1 / 2 : ℝ)) := by
      simp only [phasePi, if_neg (not_lt.mpr hrG.le), if_neg (ne_of_gt hrG)]
    have heG : (sgdArrays α ς N B).S * sgdT0 α N B * phasePi (rq (α + ς) α) ε =
        Real.sqrt (Real.pi * muBarOf α N / (B : ℝ)) * (sgdArrays α ς N B).S *
          ε ^ (-(1 / 2 : ℝ)) := by
      rw [hPiG]
      unfold sgdT0
      ring
    rw [heG] at hG
    exact pw_sandwich_mono hG (by linarith) le_rfl

theorem pm_phase_map_after_windows (α ς T : ℝ) (hα : 0 < α) (hp : 1 < α + ς) (hς₁ : ς ≠ 1)
    (hς₂ : ς ≠ α + 1) (hT : 4 ≤ T) :
    ∃ cLo cHi : ℝ, 0 < cLo ∧ cLo ≤ cHi ∧
      ∀ (Nseq Bseq : ℕ → ℕ) (εseq : ℕ → ℝ)
        (mS mG : ∀ n, RowModel (Fin (Nseq n))) (QS QG : ∀ n, ℝ → ℝ),
        Tendsto (fun n => (Nseq n : ℝ)) atTop atTop → Tendsto εseq atTop (𝓝 0) →
        (∀ n, 0 < εseq n) → (∀ n, 1 ≤ Nseq n) → (∀ n, Nseq n ≤ Bseq n) →
        (∀ n, IsMatchedModel (svdArrays α ς (Nseq n) (Bseq n)) (mS n) (εseq n)) →
        (∀ n, IsVolterraSol (mS n) (QS n)) →
        (∀ n, IsMatchedModel (sgdArrays α ς (Nseq n) (Bseq n)) (mG n) (εseq n)) →
        (∀ n, IsVolterraSol (mG n) (QG n)) →
        (ς < 1 → Tendsto (fun n => εseq n * (Nseq n : ℝ) ^ (α + ς - 1)) atTop atTop) →
        (1 < ς → 1 < α → Tendsto (fun n => εseq n * (Nseq n : ℝ)) atTop atTop) →
        (1 < ς → α ≤ 1 → ∀ᶠ n in atTop, PhaseLowWindow α ς T (Nseq n) (Bseq n) (εseq n)) →
        ∀ᶠ n in atTop,
          (ς < 1 → SandwichE cLo cHi
              (gammaRat (Nseq n) (Bseq n) * Hsum (α / 2) (Nseq n) *
                (εseq n) ^ (-(α / (2 * (α + ς - 1))))) (stepHit (mS n) (QS n) T (εseq n))) ∧
          (1 < ς → SandwichE cLo cHi
              (Real.sqrt (gammaRat (Nseq n) (Bseq n)) * (svdArrays α ς (Nseq n) (Bseq n)).S *
                (εseq n) ^ (-(1 / 2 : ℝ))) (stepHit (mS n) (QS n) T (εseq n))) ∧
          (ς < α + 1 → SandwichE cLo cHi
              ((Nseq n : ℝ) ^ 2 * (Real.pi * muBarOf α (Nseq n) / (Bseq n : ℝ)) *
                (εseq n) ^ (-(α / (α + ς - 1)))) (stepHit (mG n) (QG n) T (εseq n))) ∧
          (α + 1 < ς → SandwichE cLo cHi
              (Real.sqrt (Real.pi * muBarOf α (Nseq n) / (Bseq n : ℝ)) *
                (sgdArrays α ς (Nseq n) (Bseq n)).S * (εseq n) ^ (-(1 / 2 : ℝ)))
              (stepHit (mG n) (QG n) T (εseq n))) := by
  by_cases hς : ς < 1
  · obtain ⟨Nst, Est, cLo, cHi, hcLo, hc, hW, hseq, _⟩ :=
      thm_app_phase_A α ς T hα (by linarith) hς hT
    refine ⟨cLo / 2, cHi, by positivity, by linarith, ?_⟩
    intro Nseq Bseq εseq mS mG QS QG hN hε hεpos hNpos hNB hmS hQS hmG hQG hA _ _
    filter_upwards [hseq Nseq Bseq εseq hN hε hεpos hNpos hNB (hA hς)] with n hn
    obtain ⟨_, _, _, hS, hG⟩ := hW (Nseq n) (Bseq n) (εseq n)
      (mS n) (mG n) (QS n) (QG n) hn (hmS n) (hQS n) (hmG n) (hQG n)
    obtain ⟨_, _, _, _, hSTs, hSTg, _, _⟩ := prop_app_phase_prefactors_i α ς
      (Nseq n) (Bseq n) hα hp (hNpos n) (hNB n) (εseq n) (hεpos n)
    have heS : (svdArrays α ς (Nseq n) (Bseq n)).S * svdT0 (Nseq n) (Bseq n) *
        (εseq n) ^ (-(α / (2 * (α + ς - 1)))) =
        (gammaRat (Nseq n) (Bseq n) * Hsum (α / 2) (Nseq n) *
          (εseq n) ^ (-(α / (2 * (α + ς - 1))))) / 2 := by
      rw [hSTs]
      ring
    have heG : (sgdArrays α ς (Nseq n) (Bseq n)).S * sgdT0 α (Nseq n) (Bseq n) *
        (εseq n) ^ (-(α / (α + ς - 1))) =
        ((Nseq n : ℝ) ^ 2 * (Real.pi * muBarOf α (Nseq n) / (Bseq n : ℝ)) *
          (εseq n) ^ (-(α / (α + ς - 1)))) / 2 := by
      rw [hSTg]
      ring
    rw [heS] at hS
    rw [heG] at hG
    exact ⟨fun _ => pw_sandwich_mono (pm_half_scale hS) le_rfl (by linarith),
      fun h => False.elim (by linarith),
      fun _ => pw_sandwich_mono (pm_half_scale hG) le_rfl (by linarith),
      fun h => False.elim (by linarith)⟩
  · have hςgt : 1 < ς := lt_of_le_of_ne (not_lt.mp hς) (Ne.symm hς₁)
    by_cases hα1 : 1 < α
    · obtain ⟨Nst, Est, cLo, cHi, hcLo, hc, hW, hseq⟩ :=
        thm_app_phase_B α ς T hα1 hςgt.le hT
      refine ⟨cLo / 2, cHi, by positivity, by linarith, ?_⟩
      intro Nseq Bseq εseq mS mG QS QG hN hε hεpos hNpos hNB hmS hQS hmG hQG _ hB _
      filter_upwards [hseq Nseq Bseq εseq hN hε hεpos hNpos hNB (hB hςgt hα1)] with n hn
      obtain ⟨_, hS, hG⟩ := hW (Nseq n) (Bseq n) (εseq n)
        (mS n) (mG n) (QS n) (QG n) hn (hmS n) (hQS n) (hmG n) (hQG n)
      obtain ⟨hs, hglo, hghi⟩ := pm_map_high_sandwich α ς T hα hςgt
        (Nseq n) (Bseq n) (εseq n) cLo cHi (hNpos n) (hNB n) (hεpos n)
        hcLo hc (mS n) (mG n) (QS n) (QG n) hS hG
      exact ⟨fun h => False.elim (hς h), fun _ => hs, hglo, hghi⟩
    · have hαle : α ≤ 1 := not_lt.mp hα1
      obtain ⟨cLo, cHi, hcLo, hc, hW⟩ := thm_app_phase_C α ς T hα hαle hςgt.le hT
      refine ⟨cLo / 2, cHi, by positivity, by linarith, ?_⟩
      intro Nseq Bseq εseq mS mG QS QG _ _ hεpos hNpos hNB hmS hQS hmG hQG _ _ hC
      filter_upwards [hC hςgt hαle] with n hn
      obtain ⟨_, hS, hG⟩ := hW (Nseq n) (Bseq n) (εseq n)
        (mS n) (mG n) (QS n) (QG n) hn (hmS n) (hQS n) (hmG n) (hQG n)
      obtain ⟨hs, hglo, hghi⟩ := pm_map_high_sandwich α ς T hα hςgt
        (Nseq n) (Bseq n) (εseq n) cLo cHi (hNpos n) (hNB n) (hεpos n)
        hcLo hc (mS n) (mG n) (QS n) (QG n) hS hG
      exact ⟨fun h => False.elim (hς h), fun _ => hs, hglo, hghi⟩

/-- Label `thm:app-phase-C`, declaration of record. Snapshot `cr-2026-10-23`.

Statement (verbatim, `sections/07-phase-comparison/section.tex`, l.1305–1315):

```latex
\begin{theorem}[Low covariance exponents]\label{thm:app-phase-C}
Fix $0<\alpha\le1$, $\texp\ge1$ and $T\ge4$. There are $0<c_-\le c_+$, depending
only on $\alpha$, $\texp$ and $T$, such that for every $(N,B,\epsilon)$ in
the low-exponent window \cref{eqn:app-phase-height}, and for both $j$, the
first hit $\hat u_j$ is attained and
\[
c_-\le\frac{t^j_{T\epsilon}}{\mathcal S_jT_0^j\,\Pi_{r_j}(\epsilon)}\le c_+ .
\]
Along every sequence with $N\to\infty$ and $\epsilon\downarrow0$ in this
window, the equivalents \cref{eqn:app-phase-equivalents} hold.
\end{theorem}
```
-/
theorem thm_app_phase_C_ii (α ς T : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (hς : 1 ≤ ς) (hT : 4 ≤ T) :
    ∀ (Nseq Bseq : ℕ → ℕ) (εseq : ℕ → ℝ)
      (mS mG : ∀ n, RowModel (Fin (Nseq n))) (QS QG : ∀ n, ℝ → ℝ),
      Tendsto (fun n => (Nseq n : ℝ)) atTop atTop → Tendsto εseq atTop (𝓝 0) →
      (∀ n, 0 < εseq n) → (∀ n, 1 ≤ Nseq n) → (∀ n, Nseq n ≤ Bseq n) →
      (∀ n, IsMatchedModel (svdArrays α ς (Nseq n) (Bseq n)) (mS n) (εseq n)) →
      (∀ n, IsVolterraSol (mS n) (QS n)) →
      (∀ n, IsMatchedModel (sgdArrays α ς (Nseq n) (Bseq n)) (mG n) (εseq n)) →
      (∀ n, IsVolterraSol (mG n) (QG n)) →
      (∀ᶠ n in atTop, PhaseLowWindow α ς T (Nseq n) (Bseq n) (εseq n)) →
      (rq (α + ς) (α / 2) = 1 →
        IsEquivalent atTop (fun n => (stepHit (mS n) (QS n) T (εseq n)).toReal)
          (fun n => (svdArrays α ς (Nseq n) (Bseq n)).S * svdT0 (Nseq n) (Bseq n) /
            (4 * Real.sqrt (8 * (α / 2))) * (εseq n) ^ (-(1 / 2 : ℝ)) *
            Real.log (1 / εseq n))) ∧
      (1 < rq (α + ς) (α / 2) →
        IsEquivalent atTop (fun n => (stepHit (mS n) (QS n) T (εseq n)).toReal)
          (fun n => (svdArrays α ς (Nseq n) (Bseq n)).S * svdT0 (Nseq n) (Bseq n) *
            Jpq (α + ς) (α / 2) / (2 * Real.sqrt (εseq n)))) ∧
      (rq (α + ς) α = 1 →
        IsEquivalent atTop (fun n => (stepHit (mG n) (QG n) T (εseq n)).toReal)
          (fun n => (sgdArrays α ς (Nseq n) (Bseq n)).S * sgdT0 α (Nseq n) (Bseq n) /
            (4 * Real.sqrt (8 * α)) * (εseq n) ^ (-(1 / 2 : ℝ)) *
            Real.log (1 / εseq n))) ∧
      (1 < rq (α + ς) α →
        IsEquivalent atTop (fun n => (stepHit (mG n) (QG n) T (εseq n)).toReal)
          (fun n => (sgdArrays α ς (Nseq n) (Bseq n)).S * sgdT0 α (Nseq n) (Bseq n) *
            Jpq (α + ς) α / (2 * Real.sqrt (εseq n)))) := by
  exact pw_thm_C_ii α ς T hα hς hT

/-- Label `prop:app-phase-C-window`, declaration of record. Snapshot `cr-2026-10-23`.

Statement (verbatim, `sections/07-phase-comparison/section.tex`, l.1319–1335):

```latex
\begin{proposition}[The low-exponent window]\label{prop:app-phase-C-window}
Fix $0<\alpha\le1$. The kernel heights \cref{eqn:app-phase-heights} satisfy,
as $N\to\infty$,
\begin{align*}
k_{N,\text{s-SVD}}&\sim\begin{cases}2(1-\alpha/2)N^{-\alpha/2}/(1-\alpha),&0<\alpha<1,\\ N^{-1/2}\log N,&\alpha=1,\end{cases}\\
k_{N,\text{s-SGD}}&\sim\begin{cases}
2\big[(1-\frac2\pi)/(1-\alpha)+\frac2\pi(1-\alpha)/(1-2\alpha)\big]N^{-\alpha},&0<\alpha<\frac12,\\
\frac2\pi N^{-1/2}\log N,&\alpha=\frac12,\\
\frac4\pi(1-\alpha)\zeta(2\alpha)N^{\alpha-1},&\frac12<\alpha<1,\\
\frac4\pi\zeta(2)/\log N,&\alpha=1.
\end{cases}
\end{align*}
For fixed $\texp\ge1$ and $T\ge4$, the following sequences lie in the
low-exponent window for all large $N$, uniformly over integers $B_N\ge N$:
$\epsilon_N=N^{-\omega}$ with $0<\omega<\min(\alpha,1-\alpha)$ if $0<\alpha<1$, and
$\epsilon_N=(\log N)^{-\omega}$ with $0<\omega<1$ if $\alpha=1$.
\end{proposition}
```
-/
theorem prop_app_phase_C_window_i (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) :
    (α < 1 → IsEquivalent atTop (fun N : ℕ => phaseKsvd α N)
        (fun N : ℕ => 2 * (1 - α / 2) / (1 - α) * (N : ℝ) ^ (-(α / 2)))) ∧
    (α = 1 → IsEquivalent atTop (fun N : ℕ => phaseKsvd α N)
        (fun N : ℕ => (N : ℝ) ^ (-(1 / 2 : ℝ)) * Real.log (N : ℝ))) := by
  have hc : IsEquivalent atTop (fun _ : ℕ => 2 / Real.pi) (fun _ : ℕ => 2 / Real.pi) :=
    IsEquivalent.refl
  constructor
  · intro ha
    have he := hc.mul ((prop_app_phase_prefactors_iv α hα).1 ha)
    convert he using 1 <;> ext N <;> simp only [Pi.mul_apply, phaseKsvd, phaseDN] <;>
      field_simp <;> ring
  · intro ha
    have he := hc.mul ((prop_app_phase_prefactors_iv α hα).2.1 ha)
    convert he using 1 <;> ext N <;> simp only [Pi.mul_apply, phaseKsvd, phaseDN] <;>
      field_simp <;> ring

lemma cw_harm_norm {a : ℝ} (ha : 0 < a) (ha1 : a < 1) :
    Tendsto (fun N : ℕ => Hsum a N / (N : ℝ) ^ (1 - a)) atTop (𝓝 (1 / (1 - a))) := by
  have hX : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ (1 - a) / (1 - a) ≠ 0 := by
    filter_upwards [eventually_ge_atTop 1] with N hN
    exact div_ne_zero (Real.rpow_pos_of_pos (by exact_mod_cast hN : (0 : ℝ) < N) _).ne'
      (by linarith)
  have h1 := (isEquivalent_iff_tendsto_one hX).mp (lem_app_phase_harmonic_iii ha ha1)
  convert h1.div_const (1 - a) using 1
  ext N
  simp only [Pi.div_apply]
  field_simp [ne_of_gt (by linarith : 0 < 1 - a)]

lemma cw_harm_log :
    Tendsto (fun N : ℕ => Hsum 1 N / Real.log N) atTop (𝓝 1) := by
  apply (isEquivalent_iff_tendsto_one _).mp lem_app_phase_harmonic_iv
  filter_upwards [eventually_ge_atTop 2] with N hN
  exact (Real.log_pos (by exact_mod_cast hN : (1 : ℝ) < N)).ne'

lemma cw_harm_lim {a : ℝ} (ha : 1 < a) :
    Tendsto (fun N : ℕ => Hsum a N) atTop (𝓝 (zetaR a)) := by
  have hp : Tendsto (fun N : ℕ => (N : ℝ) ^ (1 - a) / (a - 1)) atTop (𝓝 0) := by
    have h : Tendsto (fun N : ℕ => (N : ℝ) ^ (1 - a)) atTop (𝓝 0) := by
      rw [show (1 : ℝ) - a = -(a - 1) by ring]
      exact (tendsto_rpow_neg_atTop (by linarith)).comp tendsto_natCast_atTop_atTop
    simpa using h.div_const (a - 1)
  have hlim : Tendsto (fun N : ℕ => zetaR a - Hsum a N) atTop (𝓝 0) := by
    refine squeeze_zero' ?_ ?_ hp
    · filter_upwards [eventually_ge_atTop 1] with N hN
      exact (lem_app_phase_harmonic_vi ha N hN).1
    · filter_upwards [eventually_ge_atTop 1] with N hN
      exact (lem_app_phase_harmonic_vi ha N hN).2
  simpa using (tendsto_const_nhds (x := zetaR a)).sub hlim

lemma cw_norm_equiv {f g : ℕ → ℝ} {c : ℝ} (hc : c ≠ 0)
    (ht : Tendsto (fun N => f N / g N) atTop (𝓝 c)) :
    IsEquivalent atTop f (fun N => c * g N) := by
  apply isEquivalent_of_tendsto_one
  have ht' := ht.div_const c
  simp only [div_self hc] at ht'
  convert ht' using 1
  ext N
  simp [div_div, mul_comm]

lemma cw_zeta_pos {a : ℝ} (ha : 1 < a) : 0 < zetaR a := by
  have h := (lem_app_phase_harmonic_vi ha 1 le_rfl).1
  norm_num [Hsum] at h
  linarith

lemma cw_sgd_lt {α : ℝ} (hα : 0 < α) (ha : α < 1 / 2) :
    IsEquivalent atTop (fun N : ℕ => phaseKsgd α N)
      (fun N => 2 * ((1 - 2 / Real.pi) / (1 - α) + 2 / Real.pi * (1 - α) / (1 - 2 * α)) *
        (N : ℝ) ^ (-α)) := by
  have h1 := cw_harm_norm hα (by linarith : α < 1)
  have h2 := cw_harm_norm (by linarith : 0 < 2 * α) (by linarith : 2 * α < 1)
  have hc : 0 < 1 - 2 / Real.pi := by
    have := Real.pi_gt_three
    rw [sub_pos, div_lt_one Real.pi_pos]
    linarith
  have hp : 0 < 1 - α := by linarith
  have hp2 : 0 < 1 - 2 * α := by linarith
  have hd : (1 / (1 - α) : ℝ) ≠ 0 := by positivity
  have ht := (h1.const_mul (2 * (1 - 2 / Real.pi))).add ((h2.div h1 hd).const_mul (4 / Real.pi))
  have he : (fun N : ℕ => phaseKsgd α N / (N : ℝ) ^ (-α)) =ᶠ[atTop]
      (fun N => 2 * (1 - 2 / Real.pi) * (Hsum α N / (N : ℝ) ^ (1 - α)) +
        4 / Real.pi * ((Hsum (2 * α) N / (N : ℝ) ^ (1 - 2 * α)) /
          (Hsum α N / (N : ℝ) ^ (1 - α)))) := by
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hn : (0 : ℝ) < N := by exact_mod_cast hN
    have hA : (N : ℝ) ^ (1 - α) = N * (N : ℝ) ^ (-α) := by
      rw [show 1 - α = 1 + -α by ring, Real.rpow_add hn, Real.rpow_one]
    have hB : (N : ℝ) ^ (1 - 2 * α) = (N : ℝ) ^ (1 - α) * (N : ℝ) ^ (-α) := by
      rw [← Real.rpow_add hn]; congr 1; ring
    unfold phaseKsgd
    rw [hB, hA]
    field_simp
  apply cw_norm_equiv (c := 2 * ((1 - 2 / Real.pi) / (1 - α) +
    2 / Real.pi * (1 - α) / (1 - 2 * α))) (by positivity)
  convert ht.congr' he.symm using 1
  congr 1
  field_simp
  <;> ring

lemma cw_sgd_half :
    IsEquivalent atTop (fun N : ℕ => phaseKsgd (1 / 2) N)
      (fun N => 2 / Real.pi * (N : ℝ) ^ (-(1 / 2 : ℝ)) * Real.log N) := by
  have h1 := cw_harm_norm (a := 1 / 2) (by norm_num) (by norm_num)
  norm_num at h1
  have hl : Tendsto (fun N : ℕ => 1 / Real.log N) atTop (𝓝 0) := by
    simpa [Function.comp_def] using (tendsto_inv_atTop_zero.comp
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop))
  have ht := ((h1.mul hl).const_mul (2 * (1 - 2 / Real.pi))).add
    ((cw_harm_log.div h1 (by norm_num)).const_mul (4 / Real.pi))
  have he : (fun N : ℕ => phaseKsgd (1 / 2) N /
      ((N : ℝ) ^ (-(1 / 2 : ℝ)) * Real.log N)) =ᶠ[atTop]
      (fun N => 2 * (1 - 2 / Real.pi) * (Hsum (1 / 2) N / (N : ℝ) ^ ((1 : ℝ) / 2) *
        (1 / Real.log N)) + 4 / Real.pi * ((Hsum 1 N / Real.log N) /
          (Hsum (1 / 2) N / (N : ℝ) ^ ((1 : ℝ) / 2)))) := by
    filter_upwards [eventually_ge_atTop 2] with N hN
    have hn : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
    have hA : (N : ℝ) ^ (1 / 2 : ℝ) * (N : ℝ) ^ (1 / 2 : ℝ) = N := by
      rw [← Real.rpow_add hn]; norm_num
    unfold phaseKsgd
    norm_num only [mul_one_div_cancel]
    rw [Real.rpow_neg hn.le]
    field_simp
    rw [← sq] at hA
    rw [hA]
    ring
  have hh := cw_norm_equiv (c := 2 / Real.pi) (by positivity)
    (show Tendsto (fun N : ℕ => phaseKsgd (1 / 2) N /
      ((N : ℝ) ^ (-(1 / 2 : ℝ)) * Real.log N)) atTop (𝓝 (2 / Real.pi)) by
      convert ht.congr' he.symm using 1 <;> norm_num [Pi.div_apply] <;> ring)
  convert hh using 1 <;> ext N <;> ring

lemma cw_sgd_mid {α : ℝ} (ha : 1 / 2 < α) (ha1 : α < 1) :
    IsEquivalent atTop (fun N : ℕ => phaseKsgd α N)
      (fun N => 4 / Real.pi * (1 - α) * zetaR (2 * α) * (N : ℝ) ^ (α - 1)) := by
  have hp : 0 < 1 - α := by linarith
  have h1 := cw_harm_norm (by linarith : 0 < α) ha1
  have h2 := cw_harm_lim (by linarith : 1 < 2 * α)
  have hz := cw_zeta_pos (by linarith : 1 < 2 * α)
  have hd : (1 / (1 - α) : ℝ) ≠ 0 := by positivity
  have hpow : Tendsto (fun N : ℕ => (N : ℝ) ^ (1 - 2 * α)) atTop (𝓝 0) := by
    have := (tendsto_rpow_neg_atTop (by linarith : 0 < 2 * α - 1)).comp
      (tendsto_natCast_atTop_atTop : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop)
    convert this using 1
    ext N
    congr 1
    ring
  have ht := ((h1.mul hpow).const_mul (2 * (1 - 2 / Real.pi))).add
    ((h2.div h1 hd).const_mul (4 / Real.pi))
  have he : (fun N : ℕ => phaseKsgd α N / (N : ℝ) ^ (α - 1)) =ᶠ[atTop]
      (fun N => 2 * (1 - 2 / Real.pi) * (Hsum α N / (N : ℝ) ^ (1 - α) *
        (N : ℝ) ^ (1 - 2 * α)) + 4 / Real.pi * (Hsum (2 * α) N /
          (Hsum α N / (N : ℝ) ^ (1 - α)))) := by
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hn : (0 : ℝ) < N := by exact_mod_cast hN
    have hA : (N : ℝ) ^ (α - 1) = ((N : ℝ) ^ (1 - α))⁻¹ := by
      rw [show α - 1 = -(1 - α) by ring, Real.rpow_neg hn.le]
    have hB : (N : ℝ) ^ (1 - 2 * α) = (N : ℝ) ^ (1 - α) *
        (N : ℝ) ^ (1 - α) / N := by
      calc
        _ = (N : ℝ) ^ ((1 - α) + (1 - α) - 1) := by congr 1; ring
        _ = _ := by rw [Real.rpow_sub hn, Real.rpow_add hn, Real.rpow_one]
    unfold phaseKsgd
    rw [hA, hB]
    field_simp
  apply cw_norm_equiv (c := 4 / Real.pi * (1 - α) * zetaR (2 * α)) (by positivity)
  convert ht.congr' he.symm using 1
  congr 1
  field_simp <;> ring

lemma cw_sgd_one :
    IsEquivalent atTop (fun N : ℕ => phaseKsgd 1 N)
      (fun N => 4 / Real.pi * zetaR 2 / Real.log N) := by
  have hlog2 : Tendsto (fun N : ℕ => Real.log (N : ℝ) ^ 2 / N) atTop (𝓝 0) :=
    Real.isLittleO_pow_log_id_atTop.tendsto_div_nhds_zero.comp tendsto_natCast_atTop_atTop
  have h2 := cw_harm_lim (by norm_num : (1 : ℝ) < 2)
  have ht := ((cw_harm_log.mul hlog2).const_mul (2 * (1 - 2 / Real.pi))).add
    ((h2.div cw_harm_log one_ne_zero).const_mul (4 / Real.pi))
  have he : (fun N : ℕ => phaseKsgd 1 N / (1 / Real.log N)) =ᶠ[atTop]
      (fun N => 2 * (1 - 2 / Real.pi) * (Hsum 1 N / Real.log N * (Real.log N ^ 2 / N)) +
        4 / Real.pi * (Hsum 2 N / (Hsum 1 N / Real.log N))) := by
    filter_upwards [eventually_ge_atTop 2] with N hN
    have hl : Real.log (N : ℝ) ≠ 0 := (Real.log_pos (by exact_mod_cast hN)).ne'
    unfold phaseKsgd
    norm_num only [mul_one]
    field_simp
  have hh := cw_norm_equiv (c := 4 / Real.pi * zetaR 2)
    (by have := cw_zeta_pos (by norm_num : (1 : ℝ) < 2); positivity)
    (show Tendsto (fun N : ℕ => phaseKsgd 1 N / (1 / Real.log N)) atTop
      (𝓝 (4 / Real.pi * zetaR 2)) by
      convert ht.congr' he.symm using 1 <;> simp)
  convert hh using 1 <;> ext N <;> simp [div_eq_mul_inv]


/-- Label `prop:app-phase-C-window`, declaration of record. Snapshot `cr-2026-10-23`.

Statement (verbatim, `sections/07-phase-comparison/section.tex`, l.1319–1335):

```latex
\begin{proposition}[The low-exponent window]\label{prop:app-phase-C-window}
Fix $0<\alpha\le1$. The kernel heights \cref{eqn:app-phase-heights} satisfy,
as $N\to\infty$,
\begin{align*}
k_{N,\text{s-SVD}}&\sim\begin{cases}2(1-\alpha/2)N^{-\alpha/2}/(1-\alpha),&0<\alpha<1,\\ N^{-1/2}\log N,&\alpha=1,\end{cases}\\
k_{N,\text{s-SGD}}&\sim\begin{cases}
2\big[(1-\frac2\pi)/(1-\alpha)+\frac2\pi(1-\alpha)/(1-2\alpha)\big]N^{-\alpha},&0<\alpha<\frac12,\\
\frac2\pi N^{-1/2}\log N,&\alpha=\frac12,\\
\frac4\pi(1-\alpha)\zeta(2\alpha)N^{\alpha-1},&\frac12<\alpha<1,\\
\frac4\pi\zeta(2)/\log N,&\alpha=1.
\end{cases}
\end{align*}
For fixed $\texp\ge1$ and $T\ge4$, the following sequences lie in the
low-exponent window for all large $N$, uniformly over integers $B_N\ge N$:
$\epsilon_N=N^{-\omega}$ with $0<\omega<\min(\alpha,1-\alpha)$ if $0<\alpha<1$, and
$\epsilon_N=(\log N)^{-\omega}$ with $0<\omega<1$ if $\alpha=1$.
\end{proposition}
```
-/
theorem prop_app_phase_C_window_ii (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) :
    (α < 1 / 2 → IsEquivalent atTop (fun N : ℕ => phaseKsgd α N)
        (fun N : ℕ => 2 * ((1 - 2 / Real.pi) / (1 - α) + 2 / Real.pi * (1 - α) / (1 - 2 * α)) *
          (N : ℝ) ^ (-α))) ∧
    (α = 1 / 2 → IsEquivalent atTop (fun N : ℕ => phaseKsgd α N)
        (fun N : ℕ => 2 / Real.pi * (N : ℝ) ^ (-(1 / 2 : ℝ)) * Real.log (N : ℝ))) ∧
    (1 / 2 < α → α < 1 → IsEquivalent atTop (fun N : ℕ => phaseKsgd α N)
        (fun N : ℕ => 4 / Real.pi * (1 - α) * zetaR (2 * α) * (N : ℝ) ^ (α - 1))) ∧
    (α = 1 → IsEquivalent atTop (fun N : ℕ => phaseKsgd α N)
        (fun N : ℕ => 4 / Real.pi * zetaR 2 / Real.log (N : ℝ))) := by
  refine ⟨fun ha => cw_sgd_lt hα ha, ?_, fun ha hb => cw_sgd_mid ha hb, ?_⟩
  · intro ha
    subst α
    exact cw_sgd_half
  · intro ha
    subst α
    exact cw_sgd_one

lemma cw_Ir_mono {r s H : ℝ} (hsr : s ≤ r) (hH : 0 ≤ H) : Ir r H ≤ Ir s H := by
  have hint (a : ℝ) : IntervalIntegrable (fun w : ℝ => (1 + w) ^ (-a)) volume 0 H := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.rpow_const (continuousOn_const.add continuousOn_id)
    intro w hw
    have hw' : 0 ≤ w := (uIcc_of_le hH ▸ hw).1
    left
    change 1 + w ≠ 0
    linarith
  apply intervalIntegral.integral_mono_on hH (hint r) (hint s)
  intro w hw
  apply Real.rpow_le_rpow_of_exponent_le (by linarith [hw.1])
  linarith

lemma cw_noise_bound {C r s ε k : ℝ} (hC : 0 < C) (hs : 0 < s) (hs1 : s < 1)
    (hsr : s ≤ r) (hε : 0 < ε) (hεC : ε < C ^ 2) (hk : 0 ≤ k) :
    k * C * Ir r (phaseHeight C r ε) / Real.sqrt ε ≤
      (C ^ (1 / s) / (1 - s)) * (k * ε ^ (-(1 / (2 * s)))) := by
  have hr : 0 < r := lt_of_lt_of_le hs hsr
  have hH := (pw_lowh hC hr hε hεC).1.le
  have hroot := Real.sqrt_pos.2 hε
  have hbase : 1 ≤ C / Real.sqrt ε := by
    rw [le_div_iff₀ hroot, one_mul]
    have : Real.sqrt ε < C := by
      calc _ < Real.sqrt (C ^ 2) := Real.sqrt_lt_sqrt hε.le hεC
           _ = C := Real.sqrt_sq hC.le
    exact this.le
  have h1 := le_trans (cw_Ir_mono hsr hH) (pw_Ir_le hs hs1 hH)
  have he : (1 + phaseHeight C r ε) ^ (1 - s) ≤
      (C / Real.sqrt ε) ^ ((1 - s) / s) := by
    unfold phaseHeight
    rw [show 1 + ((C / Real.sqrt ε) ^ (1 / r) - 1) =
      (C / Real.sqrt ε) ^ (1 / r) by ring, ← Real.rpow_mul (by positivity)]
    apply Real.rpow_le_rpow_of_exponent_le hbase
    have : (1 - s) / r ≤ (1 - s) / s :=
      div_le_div_of_nonneg_left (by linarith) hs hsr
    simpa [div_eq_mul_inv, mul_comm] using this
  have h2 : Ir r (phaseHeight C r ε) ≤ (C / Real.sqrt ε) ^ ((1 - s) / s) / (1 - s) :=
    h1.trans (div_le_div_of_nonneg_right he (by linarith))
  have halg : k * C * ((C / Real.sqrt ε) ^ ((1 - s) / s) / (1 - s)) / Real.sqrt ε =
      C ^ (1 / s) / (1 - s) * (k * ε ^ (-(1 / (2 * s)))) := by
    rw [Real.div_rpow hC.le hroot.le, Real.sqrt_eq_rpow, ← Real.rpow_mul hε.le]
    have hc : C * C ^ ((1 - s) / s) = C ^ (1 / s) := by
      calc
        _ = C ^ (1 + (1 - s) / s) := by rw [Real.rpow_add hC, Real.rpow_one]
        _ = _ := by congr 1; field_simp; ring
    have hεa : ε ^ ((1 / 2 : ℝ) * ((1 - s) / s)) * ε ^ (1 / 2 : ℝ) =
        ε ^ (1 / (2 * s)) := by
      rw [← Real.rpow_add hε]
      congr 1
      field_simp
      ring
    rw [Real.rpow_neg hε.le]
    field_simp
    simp only [mul_comm 2 s] at hεa
    rw [← hc, ← hεa]
    ring
  rw [← halg]
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left h2 (mul_nonneg hk hC.le)) hroot.le

lemma cw_noise_eventually {k ε : ℕ → ℝ} {C r s : ℝ} (hC : 0 < C)
    (hs : 0 < s) (hs1 : s < 1) (hsr : s ≤ r)
    (hk : ∀ᶠ N in atTop, 0 ≤ k N) (hε : ∀ᶠ N in atTop, 0 < ε N)
    (hε0 : Tendsto ε atTop (𝓝 0))
    (ht : Tendsto (fun N => k N * ε N ^ (-(1 / (2 * s)))) atTop (𝓝 0)) :
    ∀ᶠ N in atTop, k N * C * Ir r (phaseHeight C r (ε N)) ≤ Real.sqrt (ε N) := by
  have hC2 : 0 < C ^ 2 := by positivity
  have heC := (tendsto_order.1 hε0).2 _ hC2
  have hK := (ht.const_mul (C ^ (1 / s) / (1 - s)))
  simp only [mul_zero] at hK
  have hK1 : ∀ᶠ N in atTop, (C ^ (1 / s) / (1 - s)) *
      (k N * ε N ^ (-(1 / (2 * s)))) ≤ 1 := by
    exact ((tendsto_order.1 hK).2 1 (by norm_num)).mono (fun _ h => h.le)
  filter_upwards [hk, hε, heC, hK1] with N hkN heN heCN hKN
  have h := (cw_noise_bound hC hs hs1 hsr heN heCN hkN).trans hKN
  exact (div_le_one (Real.sqrt_pos.2 heN)).mp h

lemma cw_powlog_zero {a : ℝ} (b : ℝ) (ha : a < 0) :
    Tendsto (fun N : ℕ => (N : ℝ) ^ a * Real.log (N : ℝ) ^ b) atTop (𝓝 0) := by
  have h := (isLittleO_log_rpow_rpow_atTop b (by linarith : 0 < -a)).tendsto_div_nhds_zero.comp
    (tendsto_natCast_atTop_atTop : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop)
  apply h.congr'
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  simp only [Function.comp_apply]
  rw [Real.rpow_neg hn.le]
  simp [div_eq_mul_inv, mul_comm]

lemma cw_power_noise {k : ℕ → ℝ} {a b c ω s : ℝ}
    (he : IsEquivalent atTop k (fun N => c * (N : ℝ) ^ a * Real.log (N : ℝ) ^ b))
    (ha : a + ω / (2 * s) < 0) :
    Tendsto (fun N => k N * ((N : ℝ) ^ (-ω)) ^ (-(1 / (2 * s)))) atTop (𝓝 0) := by
  apply (he.isBigO.mul (isBigO_refl (fun N : ℕ => ((N : ℝ) ^ (-ω)) ^ (-(1 / (2 * s)))) _)).trans_tendsto
  have h := (cw_powlog_zero b ha).const_mul c
  simpa only [mul_zero] using h.congr' (by
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hn : (0 : ℝ) < N := by exact_mod_cast hN
    change c * _ = (c * _ * _) * _
    rw [← Real.rpow_mul hn.le]
    have : -ω * -(1 / (2 * s)) = ω / (2 * s) := by ring
    rw [this, Real.rpow_add hn]
    ring)

lemma cw_log_noise_pow {k : ℕ → ℝ} {a b c ω s : ℝ}
    (he : IsEquivalent atTop k (fun N => c * (N : ℝ) ^ a * Real.log (N : ℝ) ^ b))
    (ha : a < 0) :
    Tendsto (fun N => k N * (Real.log (N : ℝ) ^ (-ω)) ^ (-(1 / (2 * s)))) atTop (𝓝 0) := by
  apply (he.isBigO.mul (isBigO_refl (fun N : ℕ => (Real.log (N : ℝ) ^ (-ω)) ^ (-(1 / (2 * s)))) _)).trans_tendsto
  have h := (cw_powlog_zero (b + ω / (2 * s)) ha).const_mul c
  simpa only [mul_zero] using h.congr' (by
    filter_upwards [eventually_ge_atTop 2] with N hN
    have hn : (0 : ℝ) < Real.log N := Real.log_pos (by exact_mod_cast hN)
    change c * _ = (c * _ * _) * _
    rw [← Real.rpow_mul hn.le]
    have : -ω * -(1 / (2 * s)) = ω / (2 * s) := by ring
    rw [this, Real.rpow_add hn]
    ring)

lemma cw_log_noise_log {k : ℕ → ℝ} {b c ω s : ℝ}
    (he : IsEquivalent atTop k (fun N => c * Real.log (N : ℝ) ^ b))
    (hb : b + ω / (2 * s) < 0) :
    Tendsto (fun N => k N * (Real.log (N : ℝ) ^ (-ω)) ^ (-(1 / (2 * s)))) atTop (𝓝 0) := by
  apply (he.isBigO.mul (isBigO_refl (fun N : ℕ => (Real.log (N : ℝ) ^ (-ω)) ^ (-(1 / (2 * s)))) _)).trans_tendsto
  have h : Tendsto (fun N : ℕ => Real.log (N : ℝ) ^ (b + ω / (2 * s))) atTop (𝓝 0) := by
    have := (tendsto_rpow_neg_atTop (by linarith : 0 < -(b + ω / (2 * s)))).comp
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
    simpa only [neg_neg, Function.comp_def] using this
  simpa only [mul_zero] using (h.const_mul c).congr' (by
    filter_upwards [eventually_ge_atTop 2] with N hN
    have hn : (0 : ℝ) < Real.log N := Real.log_pos (by exact_mod_cast hN)
    change c * _ = (c * _) * _
    rw [← Real.rpow_mul hn.le]
    have : -ω * -(1 / (2 * s)) = ω / (2 * s) := by ring
    rw [this, Real.rpow_add hn]
    ring)

lemma cw_k_nonneg (α : ℝ) (N : ℕ) : 0 ≤ phaseKsvd α N ∧ 0 ≤ phaseKsgd α N := by
  have hH (a : ℝ) : 0 ≤ Hsum a N := by
    unfold Hsum
    exact Finset.sum_nonneg (fun i _ => Real.rpow_nonneg (Nat.cast_nonneg i) _)
  have hp : 0 ≤ 1 - 2 / Real.pi := by
    have := Real.pi_gt_three
    rw [sub_nonneg, div_le_one Real.pi_pos]
    linarith
  have hH1 := hH α
  have hH2 := hH (α / 2)
  have hH3 := hH (2 * α)
  constructor <;> simp only [phaseKsvd, phaseKsgd] <;> positivity

lemma cw_height_bound {C r ε : ℝ} (hC : 0 < C) (hε : 0 < ε) :
    phaseHeight C r ε ≤ C ^ (1 / r) * ε ^ (-(1 / (2 * r))) := by
  have hs := Real.sqrt_pos.2 hε
  have he : (C / Real.sqrt ε) ^ (1 / r) = C ^ (1 / r) * ε ^ (-(1 / (2 * r))) := by
    rw [Real.div_rpow hC.le hs.le, Real.sqrt_eq_rpow, ← Real.rpow_mul hε.le,
      div_eq_mul_inv, ← Real.rpow_neg hε.le]
    congr 3
    ring
  unfold phaseHeight
  rw [he]
  linarith

lemma cw_horizon_eventually {ε : ℕ → ℝ} {C r q : ℝ} (hC : 0 < C)
    (hε : ∀ᶠ N in atTop, 0 < ε N)
    (ht : Tendsto (fun N => ε N ^ (-(1 / (2 * r))) / (N : ℝ) ^ q) atTop (𝓝 0)) :
    ∀ᶠ N in atTop, phaseHeight C r (ε N) ≤ ((N : ℝ) / 4) ^ q := by
  have hK := ht.const_mul (C ^ (1 / r))
  simp only [mul_zero] at hK
  have hb : 0 < (4 : ℝ) ^ (-q) := by positivity
  have he := (tendsto_order.1 hK).2 _ hb
  filter_upwards [hε, he, eventually_ge_atTop 1] with N heN hN hNat
  have hn : (0 : ℝ) < N := by exact_mod_cast hNat
  have hd : 0 < (N : ℝ) ^ q := Real.rpow_pos_of_pos hn _
  have hle := (div_le_iff₀ hd).mp (show C ^ (1 / r) * ε N ^ (-(1 / (2 * r))) /
      (N : ℝ) ^ q ≤ (4 : ℝ) ^ (-q) by simpa [mul_div_assoc] using hN.le)
  apply (cw_height_bound hC heN).trans
  convert hle using 1
  rw [Real.div_rpow hn.le (by norm_num), Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 4)]
  ring

lemma cw_horizon_power {C r q ω : ℝ} (hC : 0 < C) (he : ω / (2 * r) < q) :
    ∀ᶠ N : ℕ in atTop, phaseHeight C r ((N : ℝ) ^ (-ω)) ≤ ((N : ℝ) / 4) ^ q := by
  apply cw_horizon_eventually hC
  · filter_upwards [eventually_ge_atTop 1] with N hN
    exact Real.rpow_pos_of_pos (by exact_mod_cast hN) _
  · have h := (tendsto_rpow_neg_atTop (by linarith : 0 < q - ω / (2 * r))).comp
      (tendsto_natCast_atTop_atTop : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop)
    apply h.congr'
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hn : (0 : ℝ) < N := by exact_mod_cast hN
    simp only [Function.comp_apply]
    rw [← Real.rpow_mul hn.le, ← Real.rpow_sub hn]
    congr 1
    ring

lemma cw_horizon_log {C r q ω : ℝ} (hC : 0 < C) (hq : 0 < q) :
    ∀ᶠ N : ℕ in atTop, phaseHeight C r (Real.log (N : ℝ) ^ (-ω)) ≤ ((N : ℝ) / 4) ^ q := by
  apply cw_horizon_eventually hC
  · filter_upwards [eventually_ge_atTop 2] with N hN
    exact Real.rpow_pos_of_pos (Real.log_pos (by exact_mod_cast hN)) _
  · apply (cw_powlog_zero (ω / (2 * r)) (by linarith : -q < 0)).congr'
    filter_upwards [eventually_ge_atTop 2] with N hN
    have hn : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
    have hl : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast hN)
    rw [← Real.rpow_mul hl.le, Real.rpow_neg hn.le]
    have : -ω * -(1 / (2 * r)) = ω / (2 * r) := by ring
    rw [this]
    ring

lemma cw_rq_exp {p q ω : ℝ} (hp : 1 < p) (hq : 0 < q) (hω : ω < p - 1) :
    ω / (2 * rq p q) < q := by
  have hr := pw_rq_pos hp hq
  rw [div_lt_iff₀ (by positivity : 0 < 2 * rq p q)]
  have he : q * (2 * rq p q) = p - 1 := by
    unfold rq
    field_simp
  rwa [he]

lemma cw_window_power (α ς T : ℝ) (hα : 0 < α) (ha1 : α < 1) (hς : 1 ≤ ς)
    (hT : 4 ≤ T) (ω : ℝ) (hω : 0 < ω) (hωa : ω < min α (1 - α))
    (Bseq : ℕ → ℕ) (hB : ∀ N, N ≤ Bseq N) :
    ∀ᶠ N : ℕ in atTop, PhaseLowWindow α ς T N (Bseq N) ((N : ℝ) ^ (-ω)) := by
  have hωα := lt_of_lt_of_le hωa (min_le_left _ _)
  have hωα' := lt_of_lt_of_le hωa (min_le_right _ _)
  have hp : 1 < α + ς := by linarith
  have hC1 := pw_Cpq_pos hp (by linarith : 0 < α / 2)
  have hC2 := pw_Cpq_pos hp hα
  have hr1 : 1 ≤ rq (α + ς) (α / 2) := by
    unfold rq
    rw [le_div_iff₀ (by linarith : 0 < 2 * (α / 2))]
    linarith
  have hr2 : (1 / 2 : ℝ) ≤ rq (α + ς) α := by
    unfold rq
    rw [le_div_iff₀ (by linarith : 0 < 2 * α)]
    linarith
  have hε0 : Tendsto (fun N : ℕ => (N : ℝ) ^ (-ω)) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop hω).comp tendsto_natCast_atTop_atTop
  have hεpos : ∀ᶠ N : ℕ in atTop, 0 < (N : ℝ) ^ (-ω) := by
    filter_upwards [eventually_ge_atTop 1] with N hN
    exact Real.rpow_pos_of_pos (by exact_mod_cast hN) _
  let s : ℝ := (α + ω) / (2 * α)
  have hs : 0 < s := by dsimp [s]; positivity
  have hs1 : s < 1 := by
    dsimp [s]
    rw [div_lt_one (by positivity)]
    linarith
  have hsexp : -(α / 2) + ω / (2 * s) < 0 := by
    have hsa : α * s = (α + ω) / 2 := by dsimp [s]; field_simp
    have hx : ω / (2 * s) < α / 2 := by
      rw [div_lt_iff₀ (by positivity)]
      nlinarith
    linarith
  have heS := (prop_app_phase_C_window_i α hα ha1.le).1 ha1
  have htS : Tendsto (fun N : ℕ => phaseKsvd α N * ((N : ℝ) ^ (-ω)) ^
      (-(1 / (2 * s)))) atTop (𝓝 0) := by
    apply cw_power_noise (b := 0) (by simpa using heS) hsexp
  have hS := cw_noise_eventually hC1 hs hs1 (hs1.le.trans hr1)
    (Eventually.of_forall (fun N => (cw_k_nonneg α N).1)) hεpos hε0 htS
  have htG : Tendsto (fun N : ℕ => phaseKsgd α N * ((N : ℝ) ^ (-ω)) ^
      (-(1 / (2 * (1 / 2 : ℝ))))) atTop (𝓝 0) := by
    rcases lt_trichotomy α (1 / 2) with ha | ha | ha
    · apply cw_power_noise (b := 0)
        (by simpa using (prop_app_phase_C_window_ii α hα ha1.le).1 ha)
      norm_num
      linarith
    · apply cw_power_noise (b := 1)
        (by simpa [ha] using (prop_app_phase_C_window_ii α hα ha1.le).2.1 ha)
      norm_num
      linarith
    · apply cw_power_noise (b := 0)
        (by simpa using (prop_app_phase_C_window_ii α hα ha1.le).2.2.1 ha ha1)
      norm_num
      linarith
  have hG := cw_noise_eventually hC2 (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num) hr2
    (Eventually.of_forall (fun N => (cw_k_nonneg α N).2)) hεpos hε0 htG
  have hhorS := cw_horizon_power hC1 (cw_rq_exp hp (by linarith : 0 < α / 2)
    (by linarith : ω < α + ς - 1))
  have hhorG := cw_horizon_power hC2 (cw_rq_exp hp hα (by linarith : ω < α + ς - 1))
  have heps := (tendsto_order.1 hε0).2 _ (pw_phaseEps0_pos hα hp hT)
  filter_upwards [eventually_ge_atTop 4, hεpos, heps, hS, hG, hhorS, hhorG] with N hn he he0 hs hg hhS hhG
  exact ⟨hn, hB N, he, he0, hs, hg, fun _ => hhS, fun _ => hhG⟩

lemma cw_window_log (ς T : ℝ) (hς : 1 ≤ ς) (hT : 4 ≤ T)
    (ω : ℝ) (hω : 0 < ω) (hω1 : ω < 1) (Bseq : ℕ → ℕ) (hB : ∀ N, N ≤ Bseq N) :
    ∀ᶠ N : ℕ in atTop, PhaseLowWindow 1 ς T N (Bseq N) (Real.log (N : ℝ) ^ (-ω)) := by
  have hp : 1 < (1 : ℝ) + ς := by linarith
  have hC1 := pw_Cpq_pos hp (by norm_num : (0 : ℝ) < 1 / 2)
  have hC2 := pw_Cpq_pos hp (by norm_num : (0 : ℝ) < 1)
  have hr1 : (1 / 2 : ℝ) ≤ rq (1 + ς) (1 / 2) := by unfold rq; norm_num; linarith
  have hr2 : (1 / 2 : ℝ) ≤ rq (1 + ς) 1 := by unfold rq; norm_num; linarith
  have hε0 : Tendsto (fun N : ℕ => Real.log (N : ℝ) ^ (-ω)) atTop (𝓝 0) := by
    simpa [Function.comp_def] using (tendsto_rpow_neg_atTop hω).comp
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  have hεpos : ∀ᶠ N : ℕ in atTop, 0 < Real.log (N : ℝ) ^ (-ω) := by
    filter_upwards [eventually_ge_atTop 2] with N hN
    exact Real.rpow_pos_of_pos (Real.log_pos (by exact_mod_cast hN)) _
  have heS := (prop_app_phase_C_window_i 1 (by norm_num) le_rfl).2 rfl
  have htS : Tendsto (fun N : ℕ => phaseKsvd 1 N * (Real.log (N : ℝ) ^ (-ω)) ^
      (-(1 / (2 * (1 / 2 : ℝ))))) atTop (𝓝 0) := by
    apply cw_log_noise_pow (a := -(1 / 2 : ℝ)) (b := 1) (c := 1)
      (by simpa using heS) (by norm_num)
  have hS := cw_noise_eventually hC1 (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num) hr1
    (Eventually.of_forall (fun N => (cw_k_nonneg 1 N).1)) hεpos hε0 htS
  have heG := (prop_app_phase_C_window_ii 1 (by norm_num) le_rfl).2.2.2 rfl
  have htG : Tendsto (fun N : ℕ => phaseKsgd 1 N * (Real.log (N : ℝ) ^ (-ω)) ^
      (-(1 / (2 * (1 / 2 : ℝ))))) atTop (𝓝 0) := by
    apply cw_log_noise_log (b := -1) (c := 4 / Real.pi * zetaR 2)
      (by simpa [Real.rpow_neg_one, div_eq_mul_inv] using heG)
    norm_num
    linarith
  have hG := cw_noise_eventually hC2 (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num) hr2
    (Eventually.of_forall (fun N => (cw_k_nonneg 1 N).2)) hεpos hε0 htG
  have hhorS := cw_horizon_log (ω := ω) (r := rq (1 + ς) (1 / 2)) hC1 (by norm_num : (0 : ℝ) < 1 / 2)
  have hhorG := cw_horizon_log (ω := ω) (r := rq (1 + ς) 1) hC2 (by norm_num : (0 : ℝ) < 1)
  have heps := (tendsto_order.1 hε0).2 _ (pw_phaseEps0_pos (by norm_num : (0 : ℝ) < 1) hp hT)
  filter_upwards [eventually_ge_atTop 4, hεpos, heps, hS, hG, hhorS, hhorG] with N hn he he0 hs hg hhS hhG
  exact ⟨hn, hB N, he, he0, hs, hg, fun _ => hhS, fun _ => hhG⟩


/-- Label `prop:app-phase-C-window`, declaration of record. Snapshot `cr-2026-10-23`.

Statement (verbatim, `sections/07-phase-comparison/section.tex`, l.1319–1335):

```latex
\begin{proposition}[The low-exponent window]\label{prop:app-phase-C-window}
Fix $0<\alpha\le1$. The kernel heights \cref{eqn:app-phase-heights} satisfy,
as $N\to\infty$,
\begin{align*}
k_{N,\text{s-SVD}}&\sim\begin{cases}2(1-\alpha/2)N^{-\alpha/2}/(1-\alpha),&0<\alpha<1,\\ N^{-1/2}\log N,&\alpha=1,\end{cases}\\
k_{N,\text{s-SGD}}&\sim\begin{cases}
2\big[(1-\frac2\pi)/(1-\alpha)+\frac2\pi(1-\alpha)/(1-2\alpha)\big]N^{-\alpha},&0<\alpha<\frac12,\\
\frac2\pi N^{-1/2}\log N,&\alpha=\frac12,\\
\frac4\pi(1-\alpha)\zeta(2\alpha)N^{\alpha-1},&\frac12<\alpha<1,\\
\frac4\pi\zeta(2)/\log N,&\alpha=1.
\end{cases}
\end{align*}
For fixed $\texp\ge1$ and $T\ge4$, the following sequences lie in the
low-exponent window for all large $N$, uniformly over integers $B_N\ge N$:
$\epsilon_N=N^{-\omega}$ with $0<\omega<\min(\alpha,1-\alpha)$ if $0<\alpha<1$, and
$\epsilon_N=(\log N)^{-\omega}$ with $0<\omega<1$ if $\alpha=1$.
\end{proposition}
```
-/
theorem prop_app_phase_C_window_iii (α ς T : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (hς : 1 ≤ ς)
    (hT : 4 ≤ T) :
    (α < 1 → ∀ Bseq : ℕ → ℕ, (∀ N, N ≤ Bseq N) → ∀ ω : ℝ, 0 < ω → ω < min α (1 - α) →
        ∀ᶠ N : ℕ in atTop, PhaseLowWindow α ς T N (Bseq N) ((N : ℝ) ^ (-ω))) ∧
    (α = 1 → ∀ Bseq : ℕ → ℕ, (∀ N, N ≤ Bseq N) → ∀ ω : ℝ, 0 < ω → ω < 1 →
        ∀ᶠ N : ℕ in atTop, PhaseLowWindow α ς T N (Bseq N) (Real.log (N : ℝ) ^ (-ω))) := by
  constructor
  · intro ha Bseq hB ω hω hωa
    exact cw_window_power α ς T hα ha hς hT ω hω hωa Bseq hB
  · intro ha
    subst α
    intro Bseq hB ω hω hω1
    exact cw_window_log ς T hς hT ω hω hω1 Bseq hB

lemma pr_pi_pos (r : ℝ) {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1) :
    0 < phasePi r ε := by
  have hlog : 0 < Real.log (1 / ε) := Real.log_pos ((one_lt_div hε).2 hε1)
  unfold phasePi
  split_ifs <;> positivity

lemma pr_pi_ratio {α ς ε : ℝ} (hα : 0 < α) (hς : 1 ≤ ς)
    (hε : 0 < ε) :
    phasePi (rq (α + ς) α) ε / phasePi (rq (α + ς) (α / 2)) ε =
      phaseRatioRate α ς ε := by
  have hn : ¬ς < 1 := not_lt.2 hς
  by_cases heq : ς = 1
  · subst ς
    have hrS : rq (α + 1) (α / 2) = 1 := by unfold rq; field_simp; ring
    have hrG : rq (α + 1) α = 1 / 2 := by unfold rq; field_simp; ring
    norm_num only [phasePi, hrS, hrG, phaseRatioRate]
    simp only [if_true, if_false]
    rw [div_mul_eq_div_div, ← Real.rpow_sub hε]
    norm_num
  · have hς1 : 1 < ς := lt_of_le_of_ne hς (Ne.symm heq)
    have hrS : 1 < rq (α + ς) (α / 2) := by
      unfold rq
      rw [lt_div_iff₀ (by linarith : 0 < 2 * (α / 2))]
      linarith
    have hS : phasePi (rq (α + ς) (α / 2)) ε = ε ^ (-(1 / 2 : ℝ)) := by
      simp [phasePi, not_lt.2 hrS.le, ne_of_gt hrS]
    rw [hS]
    by_cases hlt : ς < α + 1
    · have hrG : rq (α + ς) α < 1 := by
        unfold rq
        rw [div_lt_iff₀ (by positivity : 0 < 2 * α)]
        linarith
      have he : 1 / (2 * rq (α + ς) α) = α / (α + ς - 1) := by
        unfold rq
        field_simp
      simp only [phasePi, if_pos hrG, he, phaseRatioRate, if_neg hn, if_neg heq,
        if_pos hlt]
      rw [← Real.rpow_sub hε]
      congr 1
      field_simp [ne_of_gt (show 0 < α + ς - 1 by linarith)]
      <;> ring
    · by_cases heq2 : ς = α + 1
      · have hrG : rq (α + ς) α = 1 := by rw [heq2]; unfold rq; field_simp; ring
        simp only [phasePi, hrG, lt_self_iff_false, if_false, if_true,
          phaseRatioRate, if_neg hn, if_neg heq, if_neg hlt, if_pos heq2]
        exact mul_div_cancel_left₀ _ (Real.rpow_pos_of_pos hε _).ne'
      · have hrG : 1 < rq (α + ς) α := by
          unfold rq
          rw [lt_div_iff₀ (by positivity : 0 < 2 * α)]
          have : α + 1 < ς := lt_of_le_of_ne (not_lt.1 hlt) (Ne.symm heq2)
          linarith
        simp only [phasePi, if_neg (not_lt.2 hrG.le), if_neg (ne_of_gt hrG),
          phaseRatioRate, if_neg hn, if_neg heq, if_neg hlt, if_neg heq2]
        exact div_self (Real.rpow_pos_of_pos hε _).ne'

lemma pr_logquot (G S A J L ε : ℝ) (hε : 0 < ε) :
    (G / (4 * A) * ε ^ (-(1 / 2 : ℝ)) * L) / (S * J / (2 * Real.sqrt ε)) =
      (G / S) * L / (2 * A * J) := by
  have he : ε ^ (-(1 / 2 : ℝ)) = (Real.sqrt ε)⁻¹ := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_neg hε.le]
  have he2 : G / (4 * A) * ε ^ (-(1 / 2 : ℝ)) * L =
      (G * L / (2 * A)) / (2 * Real.sqrt ε) := by
    rw [he]
    simp only [div_eq_mul_inv, mul_inv_rev]
    norm_num
    <;> ring
  rw [he2, div_div_div_cancel_right₀ (by positivity)]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

lemma pr_satquot (G S JG JS ε : ℝ) (hε : 0 < ε) :
    (G * JG / (2 * Real.sqrt ε)) / (S * JS / (2 * Real.sqrt ε)) =
      (G / S) * JG / JS := by
  rw [div_div_div_cancel_right₀ (by positivity), mul_div_mul_comm]
  ring

lemma pr_Npos {N : ℕ} (m : RowModel (Fin N)) : 1 ≤ N := by
  by_contra h
  have hN : N = 0 := by omega
  subst N
  have := m.F0_pos
  simpa using this

lemma pr_toReal {l h X : ℝ} {t : ℝ≥0∞}
    (hl : 0 ≤ l) (hh : 0 ≤ h) (hX : 0 ≤ X) (ht : SandwichE l h X t) :
    Sandwich l h X t.toReal := by
  have hfin : t ≠ ⊤ := ne_top_of_le_ne_top (ENNReal.mul_ne_top (by simp) (by simp)) ht.2
  constructor
  · have := ENNReal.toReal_mono hfin ht.1
    simpa [ENNReal.toReal_mul, ENNReal.toReal_ofReal hl, ENNReal.toReal_ofReal hX] using this
  · have := ENNReal.toReal_mono (ENNReal.mul_ne_top (by simp) (by simp)) ht.2
    simpa [ENNReal.toReal_mul, ENNReal.toReal_ofReal hh, ENNReal.toReal_ofReal hX] using this

lemma pr_div {l h X Y : ℝ} {s t : ℝ≥0∞}
    (hl : 0 < l) (hlh : l ≤ h) (hX : 0 < X) (hY : 0 < Y)
    (hs : SandwichE l h X s) (ht : SandwichE l h Y t) :
    Sandwich (l / h) (h / l) (Y / X) (t.toReal / s.toReal) := by
  have hh : 0 < h := hl.trans_le hlh
  obtain ⟨hs1, hs2⟩ := pr_toReal hl.le hh.le hX.le hs
  obtain ⟨ht1, ht2⟩ := pr_toReal hl.le hh.le hY.le ht
  have hspos : 0 < s.toReal := (mul_pos hl hX).trans_le hs1
  constructor
  · calc
      l / h * (Y / X) = (l * Y) / (h * X) := by ring
      _ ≤ t.toReal / s.toReal := div_le_div₀ (by positivity) ht1 hspos hs2
  · calc
      t.toReal / s.toReal ≤ (h * Y) / (l * X) :=
        div_le_div₀ (by positivity) ht2 (by positivity) hs1
      _ = h / l * (Y / X) := by ring

/-- Label `cor:app-phase-ratio`, declaration of record. Snapshot `cr-2026-10-23`.

Statement (verbatim, `sections/07-phase-comparison/section.tex`, l.1360–1379):

```latex
\begin{corollary}[Ratio of the hitting times]\label{cor:app-phase-ratio}
In the windows of \cref{thm:app-phase-A} ($\texp<1$), \cref{thm:app-phase-B}
($\alpha>1$, $\texp\ge1$) and \cref{thm:app-phase-C} ($\alpha\le1$, $\texp\ge1$),
with constants depending only on $\alpha$, $\texp$ and $T$,
\begin{equation}\label{eqn:app-phase-ratio}
\frac{t^{\text{s-SGD}}_{T\epsilon}}{t^{\text{s-SVD}}_{T\epsilon}}\asymp D_N\cdot\begin{cases}
\epsilon^{-\alpha/[2(p-1)]},&\texp<1,\\
\epsilon^{-1/2}/\log(1/\epsilon),&\texp=1,\\
\epsilon^{-(\alpha+1-\texp)/[2(p-1)]},&1<\texp<\alpha+1,\\
\log(1/\epsilon),&\texp=\alpha+1,\\
1,&\texp>\alpha+1.
\end{cases}
\end{equation}
Along every sequence with $N\to\infty$ and $\epsilon\downarrow0$ in the window
of \cref{thm:app-phase-B} or \cref{thm:app-phase-C},
\[
\frac{t^{\text{s-SGD}}_{T\epsilon}}{t^{\text{s-SVD}}_{T\epsilon}}\sim\frac{D_N\log(1/\epsilon)}{2\sqrt{8\alpha}\,J(p,\alpha/2)}\quad(\texp=\alpha+1),\qquad
\frac{t^{\text{s-SGD}}_{T\epsilon}}{t^{\text{s-SVD}}_{T\epsilon}}\sim D_N\,\frac{J(p,\alpha)}{J(p,\alpha/2)}\quad(\texp>\alpha+1).
\]
\end{corollary}
```
-/
theorem cor_app_phase_ratio_i (α ς T : ℝ) (hα : 0 < α) (hς₁ : 1 - α < ς) (hς₂ : ς < 1)
    (hT : 4 ≤ T) :
    ∀ (Nst : ℕ) (Est cLo cHi : ℝ), PhaseAWindowHolds α ς T Nst Est cLo cHi →
      ∀ (N B : ℕ) (ε : ℝ) (mS mG : RowModel (Fin N)) (QS QG : ℝ → ℝ),
        PhaseWinA α ς T Nst Est N B ε →
        IsMatchedModel (svdArrays α ς N B) mS ε → IsVolterraSol mS QS →
        IsMatchedModel (sgdArrays α ς N B) mG ε → IsVolterraSol mG QG →
        Sandwich (cLo / cHi) (cHi / cLo) (phaseDN α N * phaseRatioRate α ς ε)
          ((stepHit mG QG T ε).toReal / (stepHit mS QS T ε).toReal) := by
  intro Nst Est cLo cHi hW N B ε mS mG QS QG hw hmS hQS hmG hQG
  have hp : 1 < α + ς := by linarith
  have hN := pr_Npos mS
  have hε := hw.2.2.1
  have hNB := hw.2.1
  obtain ⟨_, _, _, hs, hg⟩ := hW.2.2.1 N B ε mS mG QS QG hw hmS hQS hmG hQG
  have hS := pw_svd_ST_pos α ς N B hα hp hN hNB ε hε mS hmS
  have hG := pw_sgd_ST_pos α ς N B hα hp hN hNB ε hε mG hmG
  have hd := (prop_app_phase_prefactors_i α ς N B hα hp hN hNB ε hε).2.2.2.2.2.2.2
  have he :
      ((sgdArrays α ς N B).S * sgdT0 α N B * ε ^ (-(α / (α + ς - 1)))) /
        ((svdArrays α ς N B).S * svdT0 N B * ε ^ (-(α / (2 * (α + ς - 1))))) =
        phaseDN α N * phaseRatioRate α ς ε := by
    rw [mul_div_mul_comm, hd, ← Real.rpow_sub hε]
    simp only [phaseRatioRate, if_pos hς₂]
    congr 2
    field_simp
    <;> ring
  rw [← he]
  exact pr_div hW.1 hW.2.1 (mul_pos hS (Real.rpow_pos_of_pos hε _))
    (mul_pos hG (Real.rpow_pos_of_pos hε _)) hs hg


/-- Label `cor:app-phase-ratio`, declaration of record. Snapshot `cr-2026-10-23`.

Statement (verbatim, `sections/07-phase-comparison/section.tex`, l.1360–1379):

```latex
\begin{corollary}[Ratio of the hitting times]\label{cor:app-phase-ratio}
In the windows of \cref{thm:app-phase-A} ($\texp<1$), \cref{thm:app-phase-B}
($\alpha>1$, $\texp\ge1$) and \cref{thm:app-phase-C} ($\alpha\le1$, $\texp\ge1$),
with constants depending only on $\alpha$, $\texp$ and $T$,
\begin{equation}\label{eqn:app-phase-ratio}
\frac{t^{\text{s-SGD}}_{T\epsilon}}{t^{\text{s-SVD}}_{T\epsilon}}\asymp D_N\cdot\begin{cases}
\epsilon^{-\alpha/[2(p-1)]},&\texp<1,\\
\epsilon^{-1/2}/\log(1/\epsilon),&\texp=1,\\
\epsilon^{-(\alpha+1-\texp)/[2(p-1)]},&1<\texp<\alpha+1,\\
\log(1/\epsilon),&\texp=\alpha+1,\\
1,&\texp>\alpha+1.
\end{cases}
\end{equation}
Along every sequence with $N\to\infty$ and $\epsilon\downarrow0$ in the window
of \cref{thm:app-phase-B} or \cref{thm:app-phase-C},
\[
\frac{t^{\text{s-SGD}}_{T\epsilon}}{t^{\text{s-SVD}}_{T\epsilon}}\sim\frac{D_N\log(1/\epsilon)}{2\sqrt{8\alpha}\,J(p,\alpha/2)}\quad(\texp=\alpha+1),\qquad
\frac{t^{\text{s-SGD}}_{T\epsilon}}{t^{\text{s-SVD}}_{T\epsilon}}\sim D_N\,\frac{J(p,\alpha)}{J(p,\alpha/2)}\quad(\texp>\alpha+1).
\]
\end{corollary}
```
-/
theorem cor_app_phase_ratio_ii (α ς T : ℝ) (hα : 1 < α) (hς : 1 ≤ ς) (hT : 4 ≤ T) :
    ∀ (Nst : ℕ) (Est cLo cHi : ℝ), PhaseBWindowHolds α ς T Nst Est cLo cHi →
      ∀ (N B : ℕ) (ε : ℝ) (mS mG : RowModel (Fin N)) (QS QG : ℝ → ℝ),
        PhaseWinB α ς T Nst Est N B ε →
        IsMatchedModel (svdArrays α ς N B) mS ε → IsVolterraSol mS QS →
        IsMatchedModel (sgdArrays α ς N B) mG ε → IsVolterraSol mG QG →
        Sandwich (cLo / cHi) (cHi / cLo) (phaseDN α N * phaseRatioRate α ς ε)
          ((stepHit mG QG T ε).toReal / (stepHit mS QS T ε).toReal) := by
  intro Nst Est cLo cHi hW N B ε mS mG QS QG hw hmS hQS hmG hQG
  have hα0 : 0 < α := by linarith
  have hp : 1 < α + ς := by linarith
  have hN := pr_Npos mS
  have hε := hw.2.2.1
  have hNB := hw.2.1
  have hεq := pw_eps_lt_quarter (hw.2.2.2.1.trans_le (min_le_left _ _))
  have hε1 : ε < 1 := by linarith
  obtain ⟨_, hs, hg⟩ := hW.2.2.1 N B ε mS mG QS QG hw hmS hQS hmG hQG
  have hS := pw_svd_ST_pos α ς N B hα0 hp hN hNB ε hε mS hmS
  have hG := pw_sgd_ST_pos α ς N B hα0 hp hN hNB ε hε mG hmG
  have hd := (prop_app_phase_prefactors_i α ς N B hα0 hp hN hNB ε hε).2.2.2.2.2.2.2
  have he :
      ((sgdArrays α ς N B).S * sgdT0 α N B * phasePi (rq (α + ς) α) ε) /
        ((svdArrays α ς N B).S * svdT0 N B * phasePi (rq (α + ς) (α / 2)) ε) =
        phaseDN α N * phaseRatioRate α ς ε := by
    rw [mul_div_mul_comm, hd, pr_pi_ratio hα0 hς hε]
  rw [← he]
  exact pr_div hW.1 hW.2.1 (mul_pos hS (pr_pi_pos _ hε hε1))
    (mul_pos hG (pr_pi_pos _ hε hε1)) hs hg


/-- Label `cor:app-phase-ratio`, declaration of record. Snapshot `cr-2026-10-23`.

Statement (verbatim, `sections/07-phase-comparison/section.tex`, l.1360–1379):

```latex
\begin{corollary}[Ratio of the hitting times]\label{cor:app-phase-ratio}
In the windows of \cref{thm:app-phase-A} ($\texp<1$), \cref{thm:app-phase-B}
($\alpha>1$, $\texp\ge1$) and \cref{thm:app-phase-C} ($\alpha\le1$, $\texp\ge1$),
with constants depending only on $\alpha$, $\texp$ and $T$,
\begin{equation}\label{eqn:app-phase-ratio}
\frac{t^{\text{s-SGD}}_{T\epsilon}}{t^{\text{s-SVD}}_{T\epsilon}}\asymp D_N\cdot\begin{cases}
\epsilon^{-\alpha/[2(p-1)]},&\texp<1,\\
\epsilon^{-1/2}/\log(1/\epsilon),&\texp=1,\\
\epsilon^{-(\alpha+1-\texp)/[2(p-1)]},&1<\texp<\alpha+1,\\
\log(1/\epsilon),&\texp=\alpha+1,\\
1,&\texp>\alpha+1.
\end{cases}
\end{equation}
Along every sequence with $N\to\infty$ and $\epsilon\downarrow0$ in the window
of \cref{thm:app-phase-B} or \cref{thm:app-phase-C},
\[
\frac{t^{\text{s-SGD}}_{T\epsilon}}{t^{\text{s-SVD}}_{T\epsilon}}\sim\frac{D_N\log(1/\epsilon)}{2\sqrt{8\alpha}\,J(p,\alpha/2)}\quad(\texp=\alpha+1),\qquad
\frac{t^{\text{s-SGD}}_{T\epsilon}}{t^{\text{s-SVD}}_{T\epsilon}}\sim D_N\,\frac{J(p,\alpha)}{J(p,\alpha/2)}\quad(\texp>\alpha+1).
\]
\end{corollary}
```
-/
theorem cor_app_phase_ratio_iii (α ς T : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (hς : 1 ≤ ς)
    (hT : 4 ≤ T) :
    ∃ cLo cHi : ℝ, 0 < cLo ∧ cLo ≤ cHi ∧
      ∀ (N B : ℕ) (ε : ℝ) (mS mG : RowModel (Fin N)) (QS QG : ℝ → ℝ),
        PhaseLowWindow α ς T N B ε →
        IsMatchedModel (svdArrays α ς N B) mS ε → IsVolterraSol mS QS →
        IsMatchedModel (sgdArrays α ς N B) mG ε → IsVolterraSol mG QG →
        Sandwich cLo cHi (phaseDN α N * phaseRatioRate α ς ε)
          ((stepHit mG QG T ε).toReal / (stepHit mS QS T ε).toReal) := by
  obtain ⟨cLo, cHi, hcLo, hc, hW⟩ := thm_app_phase_C α ς T hα hα1 hς hT
  refine ⟨cLo / cHi, cHi / cLo, div_pos hcLo (hcLo.trans_le hc), ?_, ?_⟩
  · rw [div_le_div_iff₀ (hcLo.trans_le hc) hcLo]
    nlinarith
  · intro N B ε mS mG QS QG hw hmS hQS hmG hQG
    have hp : 1 < α + ς := by linarith
    have hN := pr_Npos mS
    have hε := hw.2.2.1
    have hNB := hw.2.1
    have hεq := pw_eps_lt_quarter (hw.2.2.2.1.trans_le (min_le_left _ _))
    have hε1 : ε < 1 := by linarith
    obtain ⟨_, hs, hg⟩ := hW N B ε mS mG QS QG hw hmS hQS hmG hQG
    have hS := pw_svd_ST_pos α ς N B hα hp hN hNB ε hε mS hmS
    have hG := pw_sgd_ST_pos α ς N B hα hp hN hNB ε hε mG hmG
    have hd := (prop_app_phase_prefactors_i α ς N B hα hp hN hNB ε hε).2.2.2.2.2.2.2
    have he :
        ((sgdArrays α ς N B).S * sgdT0 α N B * phasePi (rq (α + ς) α) ε) /
          ((svdArrays α ς N B).S * svdT0 N B * phasePi (rq (α + ς) (α / 2)) ε) =
          phaseDN α N * phaseRatioRate α ς ε := by
      rw [mul_div_mul_comm, hd, pr_pi_ratio hα hς hε]
    rw [← he]
    exact pr_div hcLo hc (mul_pos hS (pr_pi_pos _ hε hε1))
      (mul_pos hG (pr_pi_pos _ hε hε1)) hs hg

/-- Label `cor:app-phase-ratio`, declaration of record. Snapshot `cr-2026-10-23`.

Statement (verbatim, `sections/07-phase-comparison/section.tex`, l.1360–1379):

```latex
\begin{corollary}[Ratio of the hitting times]\label{cor:app-phase-ratio}
In the windows of \cref{thm:app-phase-A} ($\texp<1$), \cref{thm:app-phase-B}
($\alpha>1$, $\texp\ge1$) and \cref{thm:app-phase-C} ($\alpha\le1$, $\texp\ge1$),
with constants depending only on $\alpha$, $\texp$ and $T$,
\begin{equation}\label{eqn:app-phase-ratio}
\frac{t^{\text{s-SGD}}_{T\epsilon}}{t^{\text{s-SVD}}_{T\epsilon}}\asymp D_N\cdot\begin{cases}
\epsilon^{-\alpha/[2(p-1)]},&\texp<1,\\
\epsilon^{-1/2}/\log(1/\epsilon),&\texp=1,\\
\epsilon^{-(\alpha+1-\texp)/[2(p-1)]},&1<\texp<\alpha+1,\\
\log(1/\epsilon),&\texp=\alpha+1,\\
1,&\texp>\alpha+1.
\end{cases}
\end{equation}
Along every sequence with $N\to\infty$ and $\epsilon\downarrow0$ in the window
of \cref{thm:app-phase-B} or \cref{thm:app-phase-C},
\[
\frac{t^{\text{s-SGD}}_{T\epsilon}}{t^{\text{s-SVD}}_{T\epsilon}}\sim\frac{D_N\log(1/\epsilon)}{2\sqrt{8\alpha}\,J(p,\alpha/2)}\quad(\texp=\alpha+1),\qquad
\frac{t^{\text{s-SGD}}_{T\epsilon}}{t^{\text{s-SVD}}_{T\epsilon}}\sim D_N\,\frac{J(p,\alpha)}{J(p,\alpha/2)}\quad(\texp>\alpha+1).
\]
\end{corollary}
```
-/
theorem cor_app_phase_ratio_iv (α ς T : ℝ) (hα : 1 < α) (hς : 1 ≤ ς) (hT : 4 ≤ T) :
    ∀ (Nst : ℕ) (Est cLo cHi : ℝ), PhaseBWindowHolds α ς T Nst Est cLo cHi →
      PhaseBEquivHolds α ς T Nst Est →
      ∀ (Nseq Bseq : ℕ → ℕ) (εseq : ℕ → ℝ)
        (mS mG : ∀ n, RowModel (Fin (Nseq n))) (QS QG : ∀ n, ℝ → ℝ),
      Tendsto (fun n => (Nseq n : ℝ)) atTop atTop → Tendsto εseq atTop (𝓝 0) →
      (∀ n, 0 < εseq n) → (∀ n, 1 ≤ Nseq n) → (∀ n, Nseq n ≤ Bseq n) →
      (∀ n, IsMatchedModel (svdArrays α ς (Nseq n) (Bseq n)) (mS n) (εseq n)) →
      (∀ n, IsVolterraSol (mS n) (QS n)) →
      (∀ n, IsMatchedModel (sgdArrays α ς (Nseq n) (Bseq n)) (mG n) (εseq n)) →
      (∀ n, IsVolterraSol (mG n) (QG n)) →
      (∀ᶠ n in atTop, PhaseWinB α ς T Nst Est (Nseq n) (Bseq n) (εseq n)) →
      (ς = α + 1 →
        IsEquivalent atTop
          (fun n => (stepHit (mG n) (QG n) T (εseq n)).toReal /
            (stepHit (mS n) (QS n) T (εseq n)).toReal)
          (fun n => phaseDN α (Nseq n) * Real.log (1 / εseq n) /
            (2 * Real.sqrt (8 * α) * Jpq (α + ς) (α / 2)))) ∧
      (α + 1 < ς →
        IsEquivalent atTop
          (fun n => (stepHit (mG n) (QG n) T (εseq n)).toReal /
            (stepHit (mS n) (QS n) T (εseq n)).toReal)
          (fun n => phaseDN α (Nseq n) * Jpq (α + ς) α / Jpq (α + ς) (α / 2))) := by
  intro Nst Est cLo cHi hW hE Nseq Bseq εseq mS mG QS QG hNt hεt hε hN hNB
    hmS hQS hmG hQG hw
  have hα0 : 0 < α := by linarith
  have hp : 1 < α + ς := by linarith
  obtain ⟨_, hS, hGc, hGs⟩ :=
    hE Nseq Bseq εseq mS mG QS QG hNt hεt hε hN hNB hmS hQS hmG hQG hw
  have hd : ∀ n, (sgdArrays α ς (Nseq n) (Bseq n)).S * sgdT0 α (Nseq n) (Bseq n) /
      ((svdArrays α ς (Nseq n) (Bseq n)).S * svdT0 (Nseq n) (Bseq n)) =
        phaseDN α (Nseq n) := by
    intro n
    exact (prop_app_phase_prefactors_i α ς (Nseq n) (Bseq n) hα0 hp
      (hN n) (hNB n) (εseq n) (hε n)).2.2.2.2.2.2.2
  constructor
  · intro hc
    have hrG : rq (α + ς) α = 1 := by
      rw [hc]
      unfold rq
      field_simp
      <;> ring
    have hrS : 1 < rq (α + ς) (α / 2) := by
      unfold rq
      rw [lt_div_iff₀ (by linarith : 0 < 2 * (α / 2))]
      linarith
    refine ((hGc hrG).div (hS hrS)).congr_right ?_
    filter_upwards [] with n
    dsimp only [Pi.div_apply]
    rw [pr_logquot _ _ _ _ _ _ (hε n), hd n]
  · intro hs
    have hrG : 1 < rq (α + ς) α := by
      unfold rq
      rw [lt_div_iff₀ (by positivity : 0 < 2 * α)]
      linarith
    have hrS : 1 < rq (α + ς) (α / 2) := by
      unfold rq
      rw [lt_div_iff₀ (by linarith : 0 < 2 * (α / 2))]
      linarith
    refine ((hGs hrG).div (hS hrS)).congr_right ?_
    filter_upwards [] with n
    dsimp only [Pi.div_apply]
    rw [pr_satquot _ _ _ _ _ (hε n), hd n]


/-- Label `cor:app-phase-ratio`, declaration of record. Snapshot `cr-2026-10-23`.

Statement (verbatim, `sections/07-phase-comparison/section.tex`, l.1360–1379):

```latex
\begin{corollary}[Ratio of the hitting times]\label{cor:app-phase-ratio}
In the windows of \cref{thm:app-phase-A} ($\texp<1$), \cref{thm:app-phase-B}
($\alpha>1$, $\texp\ge1$) and \cref{thm:app-phase-C} ($\alpha\le1$, $\texp\ge1$),
with constants depending only on $\alpha$, $\texp$ and $T$,
\begin{equation}\label{eqn:app-phase-ratio}
\frac{t^{\text{s-SGD}}_{T\epsilon}}{t^{\text{s-SVD}}_{T\epsilon}}\asymp D_N\cdot\begin{cases}
\epsilon^{-\alpha/[2(p-1)]},&\texp<1,\\
\epsilon^{-1/2}/\log(1/\epsilon),&\texp=1,\\
\epsilon^{-(\alpha+1-\texp)/[2(p-1)]},&1<\texp<\alpha+1,\\
\log(1/\epsilon),&\texp=\alpha+1,\\
1,&\texp>\alpha+1.
\end{cases}
\end{equation}
Along every sequence with $N\to\infty$ and $\epsilon\downarrow0$ in the window
of \cref{thm:app-phase-B} or \cref{thm:app-phase-C},
\[
\frac{t^{\text{s-SGD}}_{T\epsilon}}{t^{\text{s-SVD}}_{T\epsilon}}\sim\frac{D_N\log(1/\epsilon)}{2\sqrt{8\alpha}\,J(p,\alpha/2)}\quad(\texp=\alpha+1),\qquad
\frac{t^{\text{s-SGD}}_{T\epsilon}}{t^{\text{s-SVD}}_{T\epsilon}}\sim D_N\,\frac{J(p,\alpha)}{J(p,\alpha/2)}\quad(\texp>\alpha+1).
\]
\end{corollary}
```
-/
theorem cor_app_phase_ratio_v (α ς T : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (hς : 1 ≤ ς)
    (hT : 4 ≤ T) :
    ∀ (Nseq Bseq : ℕ → ℕ) (εseq : ℕ → ℝ)
        (mS mG : ∀ n, RowModel (Fin (Nseq n))) (QS QG : ∀ n, ℝ → ℝ),
      Tendsto (fun n => (Nseq n : ℝ)) atTop atTop → Tendsto εseq atTop (𝓝 0) →
      (∀ n, 0 < εseq n) → (∀ n, 1 ≤ Nseq n) → (∀ n, Nseq n ≤ Bseq n) →
      (∀ n, IsMatchedModel (svdArrays α ς (Nseq n) (Bseq n)) (mS n) (εseq n)) →
      (∀ n, IsVolterraSol (mS n) (QS n)) →
      (∀ n, IsMatchedModel (sgdArrays α ς (Nseq n) (Bseq n)) (mG n) (εseq n)) →
      (∀ n, IsVolterraSol (mG n) (QG n)) →
      (∀ᶠ n in atTop, PhaseLowWindow α ς T (Nseq n) (Bseq n) (εseq n)) →
      (ς = α + 1 →
        IsEquivalent atTop
          (fun n => (stepHit (mG n) (QG n) T (εseq n)).toReal /
            (stepHit (mS n) (QS n) T (εseq n)).toReal)
          (fun n => phaseDN α (Nseq n) * Real.log (1 / εseq n) /
            (2 * Real.sqrt (8 * α) * Jpq (α + ς) (α / 2)))) ∧
      (α + 1 < ς →
        IsEquivalent atTop
          (fun n => (stepHit (mG n) (QG n) T (εseq n)).toReal /
            (stepHit (mS n) (QS n) T (εseq n)).toReal)
          (fun n => phaseDN α (Nseq n) * Jpq (α + ς) α / Jpq (α + ς) (α / 2))) := by
  intro Nseq Bseq εseq mS mG QS QG hNt hεt hε hN hNB hmS hQS hmG hQG hw
  have hp : 1 < α + ς := by linarith
  obtain ⟨hSc, hSs, hGc, hGs⟩ :=
    thm_app_phase_C_ii α ς T hα hα1 hς hT Nseq Bseq εseq mS mG QS QG
      hNt hεt hε hN hNB hmS hQS hmG hQG hw
  have hd : ∀ n, (sgdArrays α ς (Nseq n) (Bseq n)).S * sgdT0 α (Nseq n) (Bseq n) /
      ((svdArrays α ς (Nseq n) (Bseq n)).S * svdT0 (Nseq n) (Bseq n)) =
        phaseDN α (Nseq n) := by
    intro n
    exact (prop_app_phase_prefactors_i α ς (Nseq n) (Bseq n) hα hp
      (hN n) (hNB n) (εseq n) (hε n)).2.2.2.2.2.2.2
  constructor
  · intro hc
    have hrG : rq (α + ς) α = 1 := by
      rw [hc]
      unfold rq
      field_simp
      <;> ring
    have hrS : 1 < rq (α + ς) (α / 2) := by
      unfold rq
      rw [lt_div_iff₀ (by linarith : 0 < 2 * (α / 2))]
      linarith
    refine ((hGc hrG).div (hSs hrS)).congr_right ?_
    filter_upwards [] with n
    dsimp only [Pi.div_apply]
    rw [pr_logquot _ _ _ _ _ _ (hε n), hd n]
  · intro hs
    have hrG : 1 < rq (α + ς) α := by
      unfold rq
      rw [lt_div_iff₀ (by positivity : 0 < 2 * α)]
      linarith
    have hrS : 1 < rq (α + ς) (α / 2) := by
      unfold rq
      rw [lt_div_iff₀ (by linarith : 0 < 2 * (α / 2))]
      linarith
    refine ((hGs hrG).div (hSs hrS)).congr_right ?_
    filter_upwards [] with n
    dsimp only [Pi.div_apply]
    rw [pr_satquot _ _ _ _ _ (hε n), hd n]

/-- Label `thm:app-phase-map`, declaration of record. Snapshot `cr-2026-10-23`.

Statement (verbatim, `sections/07-phase-comparison/section.tex`, l.1229–1252):

```latex
\begin{theorem}[Time to $T\epsilon$ in the power-law phases]\label{thm:app-phase-map}
Fix $\alpha>0$ and $\texp$ with $\alpha+\texp>1$ and $\texp\notin\{1,\alpha+1\}$,
and fix $T\ge4$. Consider the arrays of \cref{def:app-phase-arrays} at their
matched steps along a sequence of $(N,B,\epsilon)$ with $N\to\infty$,
$\epsilon\downarrow0$ and integers $B\ge N$, such that
\begin{itemize}
\item $\epsilon N^{\alpha+\texp-1}\to\infty$ if $\texp<1$;
\item $\epsilon N\to\infty$ if $\texp>1$ and $\alpha>1$;
\item $(N,B,\epsilon)$ lies in the low-exponent window \cref{eqn:app-phase-height}
for all large indices if $\texp>1$ and $\alpha\le1$.
\end{itemize}
Then there are constants $0<c_-\le c_+$, depending only on $\alpha$, $\texp$ and
$T$, such that for all large indices of the sequence, with $x\asymp y$ meaning
$c_-\le x/y\le c_+$,
\begin{align}
t^{\text{s-SVD}}_{T\epsilon}&\asymp\gamma\,H_N(\alpha/2)\,\epsilon^{-\alpha/[2(\alpha+\texp-1)]}\ \ (\texp<1),&
t^{\text{s-SVD}}_{T\epsilon}&\asymp\sqrt\gamma\,\mathcal S_{\text{s-SVD}}\,\epsilon^{-1/2}\ \ (\texp>1),\label{eqn:app-phase-tsvd}\\
t^{\text{s-SGD}}_{T\epsilon}&\asymp\frac{N^2\pi\bar\mu}B\,\epsilon^{-\alpha/(\alpha+\texp-1)}\ \ (\texp<\alpha+1),&
t^{\text{s-SGD}}_{T\epsilon}&\asymp\sqrt{\frac{\pi\bar\mu}B}\,\mathcal S_{\text{s-SGD}}\,\epsilon^{-1/2}\ \ (\texp>\alpha+1).\label{eqn:app-phase-tsgd}
\end{align}
Moreover $H_N(\alpha/2)\asymp N^{1-\alpha/2}$ for $\alpha<2$,
$H_N(\alpha/2)\asymp\log N$ for $\alpha=2$, and $H_N(\alpha/2)\asymp1$ for $\alpha>2$,
with constants depending only on $\alpha$.
\end{theorem}
```
-/
theorem thm_app_phase_map (α ς T : ℝ) (hα : 0 < α) (hp : 1 < α + ς) (hς₁ : ς ≠ 1)
    (hς₂ : ς ≠ α + 1) (hT : 4 ≤ T) :
    ∃ cLo cHi : ℝ, 0 < cLo ∧ cLo ≤ cHi ∧
      ∀ (Nseq Bseq : ℕ → ℕ) (εseq : ℕ → ℝ)
        (mS mG : ∀ n, RowModel (Fin (Nseq n))) (QS QG : ∀ n, ℝ → ℝ),
        Tendsto (fun n => (Nseq n : ℝ)) atTop atTop → Tendsto εseq atTop (𝓝 0) →
        (∀ n, 0 < εseq n) → (∀ n, 1 ≤ Nseq n) → (∀ n, Nseq n ≤ Bseq n) →
        (∀ n, IsMatchedModel (svdArrays α ς (Nseq n) (Bseq n)) (mS n) (εseq n)) →
        (∀ n, IsVolterraSol (mS n) (QS n)) →
        (∀ n, IsMatchedModel (sgdArrays α ς (Nseq n) (Bseq n)) (mG n) (εseq n)) →
        (∀ n, IsVolterraSol (mG n) (QG n)) →
        (ς < 1 → Tendsto (fun n => εseq n * (Nseq n : ℝ) ^ (α + ς - 1)) atTop atTop) →
        (1 < ς → 1 < α → Tendsto (fun n => εseq n * (Nseq n : ℝ)) atTop atTop) →
        (1 < ς → α ≤ 1 → ∀ᶠ n in atTop, PhaseLowWindow α ς T (Nseq n) (Bseq n) (εseq n)) →
        ∀ᶠ n in atTop,
          (ς < 1 → SandwichE cLo cHi
              (gammaRat (Nseq n) (Bseq n) * Hsum (α / 2) (Nseq n) *
                (εseq n) ^ (-(α / (2 * (α + ς - 1))))) (stepHit (mS n) (QS n) T (εseq n))) ∧
          (1 < ς → SandwichE cLo cHi
              (Real.sqrt (gammaRat (Nseq n) (Bseq n)) * (svdArrays α ς (Nseq n) (Bseq n)).S *
                (εseq n) ^ (-(1 / 2 : ℝ))) (stepHit (mS n) (QS n) T (εseq n))) ∧
          (ς < α + 1 → SandwichE cLo cHi
              ((Nseq n : ℝ) ^ 2 * (Real.pi * muBarOf α (Nseq n) / (Bseq n : ℝ)) *
                (εseq n) ^ (-(α / (α + ς - 1)))) (stepHit (mG n) (QG n) T (εseq n))) ∧
          (α + 1 < ς → SandwichE cLo cHi
              (Real.sqrt (Real.pi * muBarOf α (Nseq n) / (Bseq n : ℝ)) *
                (sgdArrays α ς (Nseq n) (Bseq n)).S * (εseq n) ^ (-(1 / 2 : ℝ)))
              (stepHit (mG n) (QG n) T (εseq n))) := by
  exact pm_phase_map_after_windows α ς T hα hp hς₁ hς₂ hT

end Muon.Phase

end
