import Mathlib
import Muon.Phase.Frozen
import Muon.Phase.PhaseTheorems

/-!
# Appendix H: the unified clock and the ratio at every accuracy (task L-H.16)

Snapshot `cr-2026-10-23`. Source: `sections/07-phase-comparison/section.tex`, subsection
"The unified clock" (l.1741–1756, displays `eqn:app-phase-Upsilon`, `eqn:app-phase-Upsilon-max`;
`thm:app-phase-unified` l.1758–1772), `cor:app-phase-extended` (l.1780–1787), and
"The ratio at every accuracy" (l.1800–1837: `eqn:app-phase-ej`, `e_D`, `L`, `eqn:app-phase-chi`,
`cor:app-phase-unified-ratio`, `eqn:app-phase-ratioU`). The accuracy-exponent displays
`S(ω)`, `E`, `ω_c` (l.1855 on) belong to L-H.17 and are not encoded here.
Card: `sections/07-phase-comparison/CARD.md` §2, §3 (rows `unified`, `extended`, `unified-ratio`),
§5 (L-H.16), §6.

Standing assumptions of the source, carried into every statement: `α > 0`, `p = α + ς > 1`
(`hp : 1 < α + ς`), and `T ≥ 4` (`hT`). The source's "Fix ... $j\in\{\text{s-SVD},\text{s-SGD}\}$"
is the variable `j : PhaseKind`.

Encoding decisions:
* `PhaseKind` names the two models; `phaseKindArrays`, `phaseKindT0`, `phaseKindQ`, `phaseKindR`
  are the per-model arrays, time scale `T_0^j`, exponent `q_j`, and `r_j = r_{q_j}` (reused:
  `svdArrays`, `sgdArrays`, `svdT0`, `sgdT0`, `rq`).
* Models are universally quantified over their coefficient data: `m : RowModel (Fin N)` with
  `IsMatchedModel (phaseKindArrays ..) m ε` and any Volterra solution `Q` (`IsVolterraSol`), as in
  `PhaseTheorems.PhaseBWindowHolds`. The constants are existentially quantified before the
  quantifier over `N, B, ε, m, Q`, so they cannot depend on `B`.
* The dimensionless clock integral `𝖨_j` is `phaseClockI Q T_0 T ε` (`Frozen`), whose first hit is
  `dimHit` (`PhaseTheorems`). Lean's `toReal ⊤ = 0`: every lower bound on `𝖨_j` or on a time is
  paired with the attainment `dimHit ≠ ⊤` (or is positive, so `⊤` cannot satisfy it).
* `Υ_j(N,ε)` is `phaseUpsilon`; the source's `min{log(1/ε), log N}` for `r = 1` is written with
  `Real.log (1/ε)`, which is positive for `ε < 1`.
* `e_j`, `χ`, `e_D`, `L` are `phaseKindE`, `phaseChi`, `phaseExpD`, `phaseLogPow`.
  The case formula `eqn:app-phase-chi` is not a clause of the corollary and is not encoded.
* `ε_N` is `phaseEpsN (α+ς) N` (`Frozen`). `Π_r` is `phasePi` (`Arrays`).
* `thm_app_phase_unified_ii` also asserts the attainment `dimHit ≠ ⊤`, which the source's
  clause (ii) leaves implicit (clause (i) supplies it); without it the upper bound would be
  vacuous on `⊤`.
-/

set_option linter.style.longLine false

open MeasureTheory Set Filter Topology Asymptotics
open scoped ENNReal NNReal

noncomputable section

namespace Muon.Phase

/-! ## Model kinds, exponents and the unified clock -/

/-- The two models of the phase map: `svd` is \SignSVD, `sgd` is \SignSGD. Transcription helper
for the index `j ∈ {s-SVD, s-SGD}` of the section. -/
inductive PhaseKind where
  | svd
  | sgd
  deriving DecidableEq

/-- Adopted arrays of model `j` (`def:app-phase-arrays`). -/
def phaseKindArrays (α ς : ℝ) (N B : ℕ) : PhaseKind → PhaseArrays (Fin N)
  | .svd => svdArrays α ς N B
  | .sgd => sgdArrays α ς N B

/-- Time scale `T_0^j` of model `j` (`def:app-phase-arrays`). -/
def phaseKindT0 (α : ℝ) (N B : ℕ) : PhaseKind → ℝ
  | .svd => svdT0 N B
  | .sgd => sgdT0 α N B

/-- Rate exponent `q_j`: `q_{s-SVD} = α/2`, `q_{s-SGD} = α` (`def:app-phase-arrays`). -/
def phaseKindQ (α : ℝ) : PhaseKind → ℝ
  | .svd => α / 2
  | .sgd => α

/-- `r_j = r_{q_j} = (p-1)/(2 q_j)` with `p = α + ς` (`def:app-phase-arrays`, `rq`). -/
def phaseKindR (α ς : ℝ) (j : PhaseKind) : ℝ := rq (α + ς) (phaseKindQ α j)

/-- The set `𝒰` of `(α, ς, j)` in the source: `r_j < 1`, or `j = s-SVD` and `α ≠ 1`, or
`j = s-SGD` and `α ∉ {1/2, 1}`. Source: section.tex l.1733–1738 (the sentence defining `𝒰`). -/
def phaseInU (α ς : ℝ) : PhaseKind → Prop
  | .svd => phaseKindR α ς .svd < 1 ∨ α ≠ 1
  | .sgd => phaseKindR α ς .sgd < 1 ∨ (α ≠ 1 / 2 ∧ α ≠ 1)

/-- The unified clock exponent `Υ_j(N, ε)` of `eqn:app-phase-Upsilon`.

\begin{equation}\label{eqn:app-phase-Upsilon}
\Upsilon_j(N,\epsilon)\defeq\begin{cases}
\min\big\{\epsilon^{-(1-r)/(2r)},\ N^{q(1-r)}\big\},&r<1,\\
\min\big\{\log(1/\epsilon),\ \log N\big\},&r=1,\\
1,&r>1,
\end{cases}
\end{equation} -/
def phaseUpsilon (α ς : ℝ) (N : ℕ) (ε : ℝ) (j : PhaseKind) : ℝ :=
  if phaseKindR α ς j < 1 then
    min (ε ^ (-((1 - phaseKindR α ς j) / (2 * phaseKindR α ς j))))
      ((N : ℝ) ^ (phaseKindQ α j * (1 - phaseKindR α ς j)))
  else if phaseKindR α ς j = 1 then
    min (Real.log (1 / ε)) (Real.log (N : ℝ))
  else 1

/-- The exponent `e_j = max{1/2, 1/(2 r_j)}` of `eqn:app-phase-ej` (first display).

\begin{equation}\label{eqn:app-phase-ej}
e_j\defeq\max\Big\{\frac12,\ \frac1{2r_j}\Big\},\quad\text{that is}\quad
e_{\text{s-SVD}}=\max\Big\{\frac12,\ \frac\alpha{2(p-1)}\Big\},\quad
e_{\text{s-SGD}}=\max\Big\{\frac12,\ \frac\alpha{p-1}\Big\},
\end{equation} -/
def phaseKindE (α ς : ℝ) (j : PhaseKind) : ℝ :=
  max (1 / 2 : ℝ) (1 / (2 * phaseKindR α ς j))

/-- `χ = e_{s-SGD} - e_{s-SVD} ≥ 0`, the exponent called `κ` in the main text
(`eqn:app-phase-chi`, first display after `eqn:app-phase-ej`).

\begin{equation}\label{eqn:app-phase-chi}
\chi\,(p-1)=\max\Big\{\frac{p-1}2,\alpha\Big\}-\max\Big\{\frac{p-1}2,\frac\alpha2\Big\}
=\begin{cases}\frac\alpha2,&\texp<1,\\ \frac{\alpha+1-\texp}2,&1\le\texp\le\alpha+1,\\ 0,&\texp\ge\alpha+1.\end{cases}
\end{equation} -/
def phaseChi (α ς : ℝ) : ℝ := phaseKindE α ς .sgd - phaseKindE α ς .svd

/-- The dimension exponent `e_D` of the section (display after `eqn:app-phase-ej`, l.1807–1811).

\[
e_D\defeq\begin{cases}-\frac\alpha2,&0<\alpha<1,\\ -\frac12,&\alpha=1,\\ \frac\alpha2-1,&1<\alpha<2,\\ 0,&\alpha\ge2,\end{cases}
\qquad
L\defeq[\alpha=1]-[\alpha=2]+[\texp=\alpha+1]-[\texp=1],
\] -/
def phaseExpD (α : ℝ) : ℝ :=
  if α < 1 then -α / 2
  else if α = 1 then -1 / 2
  else if α < 2 then α / 2 - 1
  else 0

/-- The logarithmic exponent `L = [α=1] - [α=2] + [ς=α+1] - [ς=1]` (display after `eqn:app-phase-ej`,
l.1807–1811), with `[·]` the indicator of the condition.

\[
e_D\defeq\begin{cases}-\frac\alpha2,&0<\alpha<1,\\ -\frac12,&\alpha=1,\\ \frac\alpha2-1,&1<\alpha<2,\\ 0,&\alpha\ge2,\end{cases}
\qquad
L\defeq[\alpha=1]-[\alpha=2]+[\texp=\alpha+1]-[\texp=1],
\] -/
def phaseLogPow (α ς : ℝ) : ℝ :=
  (if α = 1 then 1 else 0) - (if α = 2 then 1 else 0)
    + (if ς = α + 1 then 1 else 0) - (if ς = 1 then 1 else 0)

/-! ### Helpers for `thm_app_phase_unified` (P-H.16.P1) -/

private lemma un_fNq_cont (N : ℕ) (p q : ℝ) : Continuous (fNq (N : ℕ∞) p q) := by
  have : ∀ u, Lsum (N : ℕ∞) p q u
      = ∑ i ∈ Finset.Icc 1 N, (i : ℝ) ^ (-p) * Real.exp (-(2 * u) * (i : ℝ) ^ (-q)) := by
    intro u
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
  unfold fNq
  show Continuous (fun u => 1 / 2 * Lsum (N : ℕ∞) p q u)
  simp_rw [this]
  fun_prop

private lemma un_Lsum_nonneg (N : ℕ) (p q u : ℝ) : 0 ≤ Lsum (N : ℕ∞) p q u := by
  unfold Lsum
  apply tsum_nonneg
  intro n
  split_ifs
  · positivity
  · exact le_refl _

private lemma un_fNq_nonneg (N : ℕ) (p q u : ℝ) : 0 ≤ fNq (N : ℕ∞) p q u := by
  unfold fNq; have := un_Lsum_nonneg N p q u; positivity

private lemma un_Q_facts {N : ℕ} (m : RowModel (Fin N)) (Q : ℝ → ℝ) (hQ : IsVolterraSol m Q)
    (T0 : ℝ) (hT0 : 0 < T0) :
    ContinuousOn (fun u => Q (T0 * u)) (Ici 0) ∧ ∀ u ∈ Ici (0:ℝ), 0 < Q (T0 * u) := by
  refine ⟨hQ.1.comp (continuous_const.mul continuous_id).continuousOn ?_, ?_⟩
  · intro u hu
    exact mul_nonneg hT0.le hu
  · intro u hu
    have := thm_app_phase_volterra_iii m Q hQ (T0 * u) (mul_nonneg hT0.le hu)
    exact this.1.trans_le this.2.1

private lemma un_Hsum_pos (a : ℝ) (N : ℕ) (hN : 1 ≤ N) : 0 < Hsum a N := by
  unfold Hsum
  have h1 : (1:ℕ) ∈ Finset.Icc 1 N := Finset.mem_Icc.2 ⟨le_rfl, hN⟩
  have := Finset.single_le_sum (f := fun i : ℕ => (i : ℝ) ^ (-a)) (fun i _ => by positivity) h1
  simp at this
  linarith

private lemma un_S_eq {N : ℕ} (A : PhaseArrays (Fin N)) (m : RowModel (Fin N)) (ε : ℝ)
    (hm : IsMatchedModel A m ε) : m.S = A.S := by
  obtain ⟨hμ, hd, hv, -, -⟩ := hm
  unfold RowModel.S PhaseArrays.S
  rw [hμ, hd, hv]

private lemma un_pos (α ς : ℝ) (N B : ℕ) (hα : 0 < α) (hp : 1 < α + ς)
    (hN : 1 ≤ N) (hNB : N ≤ B) (ε : ℝ) (hε : 0 < ε) :
    0 < (svdArrays α ς N B).S ∧ 0 < (sgdArrays α ς N B).S ∧ 0 < svdT0 N B ∧ 0 < sgdT0 α N B := by
  obtain ⟨h1, -, h3, -⟩ := prop_app_phase_prefactors_i α ς N B hα hp hN hNB ε hε
  have hNp : (0:ℝ) < N := by exact_mod_cast hN
  have hB : (0:ℝ) < B := by exact_mod_cast (by omega : 0 < B)
  have hγ : 0 < gammaRat N B := by unfold gammaRat; positivity
  have hH := un_Hsum_pos (α / 2) N hN
  have hHa := un_Hsum_pos α N hN
  have hmu : 0 < muBarOf α N := by unfold muBarOf; positivity
  have hs1 : 0 < Real.sqrt (gammaRat N B) := Real.sqrt_pos.2 hγ
  have hs2 : 0 < Real.sqrt (Real.pi * muBarOf α N / (B : ℝ)) :=
    Real.sqrt_pos.2 (by positivity)
  refine ⟨?_, ?_, hs1, hs2⟩
  · rw [h1]; positivity
  · rw [h3]; positivity

private lemma un_pair_svd (α ς : ℝ) (N B : ℕ) (hα : 0 < α) (hp : 1 < α + ς)
    (hN : 1 ≤ N) (hNB : N ≤ B) (ε : ℝ) (hε : 0 < ε) :
    ∃ (mG : RowModel (Fin N)) (QG : ℝ → ℝ),
      IsMatchedModel (sgdArrays α ς N B) mG ε ∧ IsVolterraSol mG QG := by
  obtain ⟨-, h2, -⟩ := prop_app_phase_prefactors_m1 α ς N B hα hp hN hNB
  obtain ⟨-, hSpos, -, -⟩ := un_pos α ς N B hα hp hN hNB ε hε
  obtain ⟨mG, h1, h2', h3, h4, h5⟩ := h2 (matchedStep (sgdArrays α ς N B) ε) (by
    unfold matchedStep
    positivity)
  obtain ⟨QG, hQG, -⟩ := thm_app_phase_volterra_i mG
  exact ⟨mG, QG, ⟨h1, h2', h3, h4, h5⟩, hQG⟩

private lemma un_pair_sgd (α ς : ℝ) (N B : ℕ) (hα : 0 < α) (hp : 1 < α + ς)
    (hN : 1 ≤ N) (hNB : N ≤ B) (ε : ℝ) (hε : 0 < ε) :
    ∃ (mS : RowModel (Fin N)) (QS : ℝ → ℝ),
      IsMatchedModel (svdArrays α ς N B) mS ε ∧ IsVolterraSol mS QS := by
  obtain ⟨h2, -, -⟩ := prop_app_phase_prefactors_m1 α ς N B hα hp hN hNB
  obtain ⟨hSpos, -, -, -⟩ := un_pos α ς N B hα hp hN hNB ε hε
  obtain ⟨mS, h1, h2', h3, h4, h5⟩ := h2 (matchedStep (svdArrays α ς N B) ε) (by
    unfold matchedStep
    positivity)
  obtain ⟨QS, hQS, -⟩ := thm_app_phase_volterra_i mS
  exact ⟨mS, QS, ⟨h1, h2', h3, h4, h5⟩, hQS⟩

/-- Single-model facts (svd): the dimensionless equation and kernel properties. -/
private lemma un_facts_svd (α ς : ℝ) (N B : ℕ) (hα : 0 < α) (hp : 1 < α + ς)
    (hN : 1 ≤ N) (hNB : N ≤ B) (ε : ℝ) (hε : 0 < ε) (mS : RowModel (Fin N))
    (hmS : IsMatchedModel (svdArrays α ς N B) mS ε) (QS : ℝ → ℝ) (hQS : IsVolterraSol mS QS) :
    0 < mS.S ∧
    ContinuousOn (dimKernel mS (svdT0 N B) ε) (Ici 0) ∧
    (∀ u ∈ Ici (0:ℝ), 0 ≤ dimKernel mS (svdT0 N B) ε u) ∧
    AntitoneOn (dimKernel mS (svdT0 N B) ε) (Ici 0) ∧
    IntegrableOn (dimKernel mS (svdT0 N B) ε) (Ioi 0) ∧
    ∫ u in Ioi (0:ℝ), dimKernel mS (svdT0 N B) ε u ≤ 1 ∧
    (∀ u ∈ Ici (0:ℝ), dimKernel mS (svdT0 N B) ε u = svdKernel α N u) ∧
    (∀ u ∈ Ici (0:ℝ), QS (svdT0 N B * u) = fNq (N : ℕ∞) (α + ς) (α / 2) u +
        Real.sqrt ε * Muon.Foundations.oneSidedConv (fun v => Real.sqrt (QS (svdT0 N B * v)))
          (dimKernel mS (svdT0 N B) ε) u) := by
  obtain ⟨mG, QG, hmG, hQG⟩ := un_pair_svd α ς N B hα hp hN hNB ε hε
  obtain ⟨-, -, hQ3, -, hK, -⟩ := prop_app_phase_prefactors_ii α ς N B hα hp hN hNB ε hε mS mG hmS hmG QS QG hQS hQG
  obtain ⟨⟨hpos, hcont, hanti, hint, hmass, -, -⟩, -⟩ :=
    prop_app_phase_prefactors_ii_props α ς N B hα hp hN hNB ε hε mS mG hmS hmG
  obtain ⟨hSs, -, -, -⟩ := un_pos α ς N B hα hp hN hNB ε hε
  refine ⟨by rw [un_S_eq _ mS ε hmS]; exact hSs, hcont, fun u hu => (hpos u hu).le, hanti, hint, hmass.le, fun u hu => ?_, fun u hu => hQ3 u hu⟩
  rw [hK u hu]
  rfl

private lemma un_facts_sgd (α ς : ℝ) (N B : ℕ) (hα : 0 < α) (hp : 1 < α + ς)
    (hN : 1 ≤ N) (hNB : N ≤ B) (ε : ℝ) (hε : 0 < ε) (mG : RowModel (Fin N))
    (hmG : IsMatchedModel (sgdArrays α ς N B) mG ε) (QG : ℝ → ℝ) (hQG : IsVolterraSol mG QG) :
    0 < mG.S ∧
    ContinuousOn (dimKernel mG (sgdT0 α N B) ε) (Ici 0) ∧
    (∀ u ∈ Ici (0:ℝ), 0 ≤ dimKernel mG (sgdT0 α N B) ε u) ∧
    AntitoneOn (dimKernel mG (sgdT0 α N B) ε) (Ici 0) ∧
    IntegrableOn (dimKernel mG (sgdT0 α N B) ε) (Ioi 0) ∧
    ∫ u in Ioi (0:ℝ), dimKernel mG (sgdT0 α N B) ε u ≤ 1 ∧
    (∀ u ∈ Ici (0:ℝ), dimKernel mG (sgdT0 α N B) ε u = sgdKernel α N u) ∧
    (∀ u ∈ Ici (0:ℝ), QG (sgdT0 α N B * u) = fNq (N : ℕ∞) (α + ς) α u +
        Real.sqrt ε * Muon.Foundations.oneSidedConv (fun v => Real.sqrt (QG (sgdT0 α N B * v)))
          (dimKernel mG (sgdT0 α N B) ε) u) := by
  obtain ⟨mS, QS, hmS, hQS⟩ := un_pair_sgd α ς N B hα hp hN hNB ε hε
  obtain ⟨-, -, -, hQ4, -, hK⟩ := prop_app_phase_prefactors_ii α ς N B hα hp hN hNB ε hε mS mG hmS hmG QS QG hQS hQG
  obtain ⟨-, ⟨hpos, hcont, hanti, -, -, hi1, hv1, hi2, hv2⟩⟩ :=
    prop_app_phase_prefactors_ii_props α ς N B hα hp hN hNB ε hε mS mG hmS hmG
  obtain ⟨-, hSs, -, -⟩ := un_pos α ς N B hα hp hN hNB ε hε
  have hcongr : ∀ u ∈ Ioi (0:ℝ), dimKernel mG (sgdT0 α N B) ε u = sgdKernel α N u := fun u hu => hK u (le_of_lt hu)
  have hint : IntegrableOn (dimKernel mG (sgdT0 α N B) ε) (Ioi 0) :=
    (hi1.add hi2).congr_fun (fun u hu => (hcongr u hu).symm) measurableSet_Ioi
  have hmass : ∫ u in Ioi (0:ℝ), dimKernel mG (sgdT0 α N B) ε u = 1 := by
    rw [setIntegral_congr_fun measurableSet_Ioi hcongr]
    unfold sgdKernel
    rw [integral_add hi1 hi2, hv1, hv2]
    ring
  exact ⟨by rw [un_S_eq _ mG ε hmG]; exact hSs, hcont, fun u hu => (hpos u hu).le, hanti, hint, hmass.le, fun u hu => hK u hu, fun u hu => hQ4 u hu⟩

private lemma un_hit_exists {Y : ℝ → ℝ} {a : ℝ} (hc : ContinuousOn Y (Ici 0)) (h0 : a < Y 0)
    (hex : ∃ u : ℝ, 0 ≤ u ∧ Y u ≤ a) :
    ∃ û : ℝ, 0 < û ∧ Y û = a ∧ firstHit Y a = ENNReal.ofReal û ∧
      ∀ u : ℝ, 0 ≤ u → u < û → a < Y u := by
  set S : Set ℝ := Ici 0 ∩ {t | Y t ≤ a} with hS
  have hSc : IsClosed S := by
    have : IsClosed (Ici (0:ℝ) ∩ Y ⁻¹' Iic a) :=
      hc.preimage_isClosed_of_isClosed isClosed_Ici isClosed_Iic
    exact this
  obtain ⟨u1, hu1, hu1a⟩ := hex
  have hne : S.Nonempty := ⟨u1, hu1, hu1a⟩
  have hbdd : BddBelow S := ⟨0, fun t ht => ht.1⟩
  set û := sInf S with hû
  have hmem : û ∈ S := hSc.csInf_mem hne hbdd
  have hû0 : 0 ≤ û := hmem.1
  have hYû : Y û ≤ a := hmem.2
  have hlt : ∀ u : ℝ, 0 ≤ u → u < û → a < Y u := by
    intro u hu hlt
    by_contra hcon
    push_neg at hcon
    have : u ∈ S := ⟨hu, hcon⟩
    have := csInf_le hbdd this
    linarith
  have hpos : 0 < û := by
    rcases hû0.eq_or_lt with h | h
    · exfalso
      have : Y û ≤ a := hYû
      rw [← h] at this
      linarith
    · exact h
  have hEq : Y û = a := by
    have hcû : ContinuousOn Y (Icc 0 û) := hc.mono (fun x hx => hx.1)
    obtain ⟨c, hc1, hc2⟩ := intermediate_value_Icc' hû0 hcû ⟨hYû, h0.le⟩
    rcases hc1.2.eq_or_lt with h | h
    · rw [← h]; exact hc2
    · exfalso
      have := hlt c hc1.1 h
      linarith
  refine ⟨û, hpos, hEq, ?_, hlt⟩
  apply le_antisymm
  · unfold firstHit
    have h1 : Y ((⟨û, hû0⟩ : ℝ≥0) : ℝ) ≤ a := hYû
    have := iInf₂_le (f := fun (t : ℝ≥0) (_ : Y (t : ℝ) ≤ a) => (t : ℝ≥0∞)) ⟨û, hû0⟩ h1
    refine this.trans (le_of_eq ?_)
    rw [ENNReal.ofReal, Real.toNNReal_of_nonneg hû0]
    rfl
  · unfold firstHit
    refine le_iInf₂ (fun t ht => ?_)
    have : û ≤ (t : ℝ) := csInf_le hbdd ⟨t.2, ht⟩
    rw [← ENNReal.ofReal_coe_nnreal]
    exact ENNReal.ofReal_le_ofReal this

private lemma un_Hsum_ge_one (p : ℝ) (N : ℕ) (hN : 1 ≤ N) : 1 ≤ Hsum p N := by
  unfold Hsum
  have h1 : (1:ℕ) ∈ Finset.Icc 1 N := Finset.mem_Icc.2 ⟨le_rfl, hN⟩
  have := Finset.single_le_sum (f := fun i : ℕ => (i : ℝ) ^ (-p)) (fun i _ => by positivity) h1
  simpa using this

private lemma un_fNq_zero (N : ℕ) (p q : ℝ) :
    fNq (N : ℕ∞) p q 0 = 1 / 2 * Hsum p N := by
  unfold fNq Hsum Lsum
  rw [tsum_eq_sum (s := Finset.Icc 1 N)]
  · simp only [mul_zero, neg_zero, zero_mul, Real.exp_zero, mul_one]
    congr 1
    apply Finset.sum_congr rfl
    intro n hn
    rw [Finset.mem_Icc] at hn
    have h1 : 0 < n ∧ ((n : ℕ∞) ≤ (N : ℕ∞)) := ⟨by omega, by exact_mod_cast hn.2⟩
    simp [h1]
  · intro b hb
    rw [if_neg]
    rintro ⟨h1, h2⟩
    apply hb
    rw [Finset.mem_Icc]
    exact ⟨by omega, by exact_mod_cast h2⟩

/-- Generic single-model package, for either kind. -/
private lemma un_facts (α ς : ℝ) (j : PhaseKind) (N B : ℕ) (hα : 0 < α) (hp : 1 < α + ς)
    (hN : 1 ≤ N) (hNB : N ≤ B) (ε : ℝ) (hε : 0 < ε) (m : RowModel (Fin N)) (Q : ℝ → ℝ)
    (hm : IsMatchedModel (phaseKindArrays α ς N B j) m ε) (hQ : IsVolterraSol m Q) :
    0 < phaseKindT0 α N B j ∧ 0 < m.S ∧
    ContinuousOn (dimKernel m (phaseKindT0 α N B j) ε) (Ici 0) ∧
    (∀ u ∈ Ici (0:ℝ), 0 ≤ dimKernel m (phaseKindT0 α N B j) ε u) ∧
    AntitoneOn (dimKernel m (phaseKindT0 α N B j) ε) (Ici 0) ∧
    IntegrableOn (dimKernel m (phaseKindT0 α N B j) ε) (Ioi 0) ∧
    ∫ u in Ioi (0:ℝ), dimKernel m (phaseKindT0 α N B j) ε u ≤ 1 ∧
    (∀ u ∈ Ici (0:ℝ), dimKernel m (phaseKindT0 α N B j) ε u
        = if j = PhaseKind.svd then svdKernel α N u else sgdKernel α N u) ∧
    (∀ u ∈ Ici (0:ℝ), Q (phaseKindT0 α N B j * u) = fNq (N : ℕ∞) (α + ς) (phaseKindQ α j) u +
        Real.sqrt ε * Muon.Foundations.oneSidedConv
          (fun v => Real.sqrt (Q (phaseKindT0 α N B j * v)))
          (dimKernel m (phaseKindT0 α N B j) ε) u) := by
  obtain ⟨-, -, hT1, hT2⟩ := un_pos α ς N B hα hp hN hNB ε hε
  cases j
  · obtain ⟨a, b, c, d, e, f, g, h⟩ := un_facts_svd α ς N B hα hp hN hNB ε hε m hm Q hQ
    exact ⟨hT1, a, b, c, d, e, f, fun u hu => by have := g u hu; simpa [phaseKindT0] using this, h⟩
  · obtain ⟨a, b, c, d, e, f, g, h⟩ := un_facts_sgd α ς N B hα hp hN hNB ε hε m hm Q hQ
    exact ⟨hT2, a, b, c, d, e, f, fun u hu => by have := g u hu; simpa [phaseKindT0] using this, h⟩

/-- Attainment: the risk tends to `ε < Tε`. -/
private lemma un_attain (α ς T : ℝ) (j : PhaseKind) (N B : ℕ) (hα : 0 < α) (hp : 1 < α + ς)
    (hT : 4 ≤ T) (hN : 1 ≤ N) (hNB : N ≤ B) (ε : ℝ) (hε : 0 < ε) (m : RowModel (Fin N))
    (Q : ℝ → ℝ) (hm : IsMatchedModel (phaseKindArrays α ς N B j) m ε) (hQ : IsVolterraSol m Q) :
    ∃ u : ℝ, 0 ≤ u ∧ Q (phaseKindT0 α N B j * u) ≤ T * ε := by
  obtain ⟨hT0, hS, -⟩ := un_facts α ς j N B hα hp hN hNB ε hε m Q hm hQ
  obtain ⟨hlim, hk⟩ := thm_app_phase_volterra_iv m Q hQ
  have hη : m.η = 2 * Real.sqrt ε / (phaseKindArrays α ς N B j).S := hm.2.2.2.2
  have hSeq := un_S_eq _ m ε hm
  have hkb : m.kbar ^ 2 = ε := by
    rw [hk, hη, hSeq]
    have hSA : (phaseKindArrays α ς N B j).S ≠ 0 := by rw [← hSeq]; exact hS.ne'
    field_simp
    rw [Real.sq_sqrt hε.le]
    ring
  rw [hkb] at hlim
  have hlt : ε < T * ε := by nlinarith
  have hev := (hlim.eventually (gt_mem_nhds hlt))
  obtain ⟨s0, hs0⟩ := Filter.eventually_atTop.1 hev
  refine ⟨max s0 0 / phaseKindT0 α N B j, by positivity, ?_⟩
  rw [mul_div_cancel₀ _ hT0.ne']
  exact (hs0 _ (le_max_left _ _)).le

private lemma un_hsq {p q : ℝ} (hp : 1 < p) (hq : 0 < q) {w : ℝ} (hw : 0 ≤ w) :
    (1 + w) ^ (-dAQ p q) = ((1 + w) ^ (-rq p q)) ^ 2 := by
  have hdr : dAQ p q = 2 * rq p q := by unfold dAQ rq; field_simp
  have hw1 : (0 : ℝ) ≤ 1 + w := by linarith
  rw [hdr, ← Real.rpow_natCast, ← Real.rpow_mul hw1]
  congr 1
  push_cast
  ring

/-- Lower envelope of `√f` on `[0, (N/4)^q]`. -/
private lemma un_low_pt {p q : ℝ} (hp : 1 < p) (hq : 0 < q) (N : ℕ) (hN : 4 ≤ N) {w : ℝ}
    (hw : 0 ≤ w) (hwN : w ≤ ((N : ℝ) / 4) ^ q) :
    Real.sqrt (Aconst p) * (1 + w) ^ (-rq p q) ≤ Real.sqrt (fNq (N : ℕ∞) p q w) := by
  have hA0 : 0 < Aconst p := by unfold Aconst; positivity
  have h := lem_app_phase_sums_ii hp hq N hN hw hwN
  have hs : 0 ≤ (1 + w) ^ (-rq p q) := Real.rpow_nonneg (by linarith) _
  rw [un_hsq hp hq hw] at h
  have hf : Aconst p * ((1 + w) ^ (-rq p q)) ^ 2 ≤ fNq (N : ℕ∞) p q w := by
    unfold fNq; linarith
  calc Real.sqrt (Aconst p) * (1 + w) ^ (-rq p q)
      = Real.sqrt ((Real.sqrt (Aconst p) * (1 + w) ^ (-rq p q)) ^ 2) :=
        (Real.sqrt_sq (mul_nonneg (Real.sqrt_nonneg _) hs)).symm
    _ ≤ Real.sqrt (fNq (N : ℕ∞) p q w) :=
        Real.sqrt_le_sqrt (by rw [mul_pow, Real.sq_sqrt hA0.le]; exact hf)

private lemma un_L1 {p q : ℝ} (hp : 1 < p) (hq : 0 < q) (N : ℕ) (hN : 4 ≤ N)
    {Y : ℝ → ℝ} (hYc : ContinuousOn Y (Ici 0))
    (hYf : ∀ u ∈ Ici (0 : ℝ), fNq (N : ℕ∞) p q u ≤ Y u)
    {V û : ℝ} (hV0 : 0 ≤ V) (hVN : V ≤ ((N : ℝ) / 4) ^ q) (hVû : V ≤ û) :
    Real.sqrt (Aconst p) * Ir (rq p q) V ≤ ∫ u in (0 : ℝ)..û, Real.sqrt (Y u) := by
  have hsubV : Icc (0 : ℝ) V ⊆ Ici 0 := fun x hx => hx.1
  have hsubû : Icc (0 : ℝ) û ⊆ Ici 0 := fun x hx => hx.1
  have hcr : ContinuousOn (fun w : ℝ => (1 + w) ^ (-rq p q)) (Icc 0 V) := by
    apply ContinuousOn.rpow_const
    · exact (continuous_const.add continuous_id).continuousOn
    · intro w hw
      left
      exact (show (0 : ℝ) < 1 + w by linarith [hw.1]).ne'
  have hcrI : IntervalIntegrable (fun w : ℝ => (1 + w) ^ (-rq p q)) volume 0 V :=
    hcr.intervalIntegrable_of_Icc hV0
  have hIY : IntervalIntegrable (fun u => Real.sqrt (Y u)) volume 0 û :=
    ((hYc.mono hsubû).sqrt).intervalIntegrable_of_Icc (hV0.trans hVû)
  have hIYV : IntervalIntegrable (fun u => Real.sqrt (Y u)) volume 0 V :=
    ((hYc.mono hsubV).sqrt).intervalIntegrable_of_Icc hV0
  have h1 : Real.sqrt (Aconst p) * Ir (rq p q) V ≤ ∫ u in (0 : ℝ)..V, Real.sqrt (Y u) := by
    unfold Ir
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_mono_on hV0 (hcrI.const_mul _) hIYV (fun w hw => ?_)
    exact (un_low_pt hp hq N hN hw.1 (hw.2.trans hVN)).trans
      (Real.sqrt_le_sqrt (hYf w hw.1))
  have h2 : ∫ u in (0 : ℝ)..V, Real.sqrt (Y u) ≤ ∫ u in (0 : ℝ)..û, Real.sqrt (Y u) := by
    have hsplit := intervalIntegral.integral_interval_sub_left hIY hIYV
    have hnn : 0 ≤ ∫ w in V..û, Real.sqrt (Y w) :=
      intervalIntegral.integral_nonneg hVû (fun w _ => Real.sqrt_nonneg _)
    linarith
  exact h1.trans h2

private lemma un_eps_facts {p q T ε : ℝ} (h : ε < clockEps0 p q T) :
    ε < 1 / (8 * T) ∧ ε < Cpq p q ^ 2 ∧ ε < (Aconst p / T) ^ 2 ∧ ε < 1 / 4 := by
  unfold clockEps0 at h
  split_ifs at h <;> simp only [lt_min_iff] at h
  · exact ⟨h.1.1.1.2, h.1.1.2, h.1.2, h.1.1.1.1⟩
  · exact ⟨h.1.1.2, h.1.2, h.2, h.1.1.1⟩

private lemma un_hitpkg {p q T : ℝ} (hp : 1 < p) (hT : 4 ≤ T) (N : ℕ) (hN : 1 ≤ N) {ε : ℝ}
    (hε : 0 < ε) (hε8 : ε < 1 / (8 * T)) {Y : ℝ → ℝ} (hYc : ContinuousOn Y (Ici 0))
    (hYf : ∀ u ∈ Ici (0 : ℝ), fNq (N : ℕ∞) p q u ≤ Y u)
    (hex : ∃ u : ℝ, 0 ≤ u ∧ Y u ≤ T * ε) :
    ∃ û : ℝ, 0 < û ∧ Y û = T * ε ∧ firstHit Y (T * ε) = ENNReal.ofReal û := by
  have hT0 : 0 < T := by linarith
  have h0 : T * ε < Y 0 := by
    have h1 := hYf 0 (Set.mem_Ici.2 le_rfl)
    rw [un_fNq_zero] at h1
    have := un_Hsum_ge_one p N hN
    have h2 : T * ε < 1 / 8 := by
      have := mul_lt_mul_of_pos_left hε8 hT0
      rw [mul_one_div, mul_comm 8 T, ← div_div, div_self hT0.ne'] at this
      linarith
    linarith
  obtain ⟨û, h1, h2, h3, -⟩ := un_hit_exists hYc h0 hex
  exact ⟨û, h1, h2, h3⟩

private lemma un_Ir_lt {r V : ℝ} (hr0 : 0 < r) (hr1 : r < 1) (hV : 0 ≤ V) :
    Ir r V = ((1 + V) ^ (1 - r) - 1) / (1 - r) := by
  unfold Ir
  rw [intervalIntegral.integral_comp_add_left (fun y : ℝ => y ^ (-r)) 1]
  rw [integral_rpow (Or.inl (by linarith))]
  have e : -r + 1 = 1 - r := by ring
  rw [e]
  simp

private lemma un_Ir_one {V : ℝ} (hV : 0 ≤ V) : Ir 1 V = Real.log (1 + V) := by
  unfold Ir
  rw [intervalIntegral.integral_comp_add_left (fun y : ℝ => y ^ (-(1:ℝ))) 1]
  simp only [Real.rpow_neg_one, add_zero]
  rw [integral_inv_of_pos (by norm_num) (by linarith)]
  simp

private lemma un_pow_ge_two {x s : ℝ} (hs : 0 < s) (hx : (2 : ℝ) ^ (1 / s) ≤ x) :
    2 ≤ x ^ s := by
  have h2 : (0:ℝ) ≤ (2:ℝ) ^ (1 / s) := by positivity
  calc (2 : ℝ) = ((2 : ℝ) ^ (1 / s)) ^ s := by
        rw [← Real.rpow_mul (by norm_num), one_div, inv_mul_cancel₀ hs.ne', Real.rpow_one]
    _ ≤ x ^ s := Real.rpow_le_rpow h2 hx hs.le

private lemma un_lower_lt {p q T : ℝ} (hp : 1 < p) (hq : 0 < q) (hT : 4 ≤ T) (hr : rq p q < 1) :
    ∃ (N0 : ℕ) (cm : ℝ), 4 ≤ N0 ∧ 0 < cm ∧ ∀ (N : ℕ) (ε : ℝ) (Y : ℝ → ℝ) (û : ℝ),
      N0 ≤ N → 0 < ε → ε < clockEps0 p q T → ContinuousOn Y (Ici 0) →
      (∀ u ∈ Ici (0 : ℝ), fNq (N : ℕ∞) p q u ≤ Y u) →
      firstHit Y (T * ε) = ENNReal.ofReal û → 0 < û → Y û = T * ε →
      cm * min (ε ^ (-((1 - rq p q) / (2 * rq p q)))) ((N : ℝ) ^ (q * (1 - rq p q)))
        ≤ ∫ u in (0 : ℝ)..û, Real.sqrt (Y u) := by
  have hr0 : 0 < rq p q := by unfold rq; exact div_pos (by linarith) (by linarith)
  have h1r : 0 < 1 - rq p q := by linarith
  have hA0 : 0 < Aconst p := by unfold Aconst; positivity
  have hT0 : 0 < T := by linarith
  have hsA : 0 < Real.sqrt (Aconst p) := Real.sqrt_pos.2 hA0
  set r := rq p q with hr_def
  set s := q * (1 - r) with hs_def
  have hs0 : 0 < s := mul_pos hq h1r
  refine ⟨max 4 (⌈4 * (2 : ℝ) ^ (1 / s)⌉₊), 
    min (Real.sqrt (Aconst p) / (2 * (1 - r)) * (Aconst p / T) ^ ((1 - r) / (2 * r)))
      (Real.sqrt (Aconst p) / (2 * (1 - r)) * (4 : ℝ) ^ (-s)),
    le_max_left _ _, ?_, ?_⟩
  · apply lt_min
    · have : 0 < (Aconst p / T) ^ ((1 - r) / (2 * r)) := Real.rpow_pos_of_pos (by positivity) _
      positivity
    · have : 0 < (4:ℝ) ^ (-s) := Real.rpow_pos_of_pos (by norm_num) _
      positivity
  intro N ε Y û hN hε hε0 hYc hYf hhit hû0 hYû
  have hN4 : 4 ≤ N := le_trans (le_max_left _ _) hN
  have hNc : 4 * (2 : ℝ) ^ (1 / s) ≤ (N : ℝ) := by
    have h1 : ⌈4 * (2 : ℝ) ^ (1 / s)⌉₊ ≤ N := le_trans (le_max_right _ _) hN
    exact (Nat.le_ceil _).trans (by exact_mod_cast h1)
  have hNr : (4 : ℝ) ≤ N := by exact_mod_cast hN4
  have hV0 : 0 ≤ ((N : ℝ) / 4) ^ q := by positivity
  set V := ((N : ℝ) / 4) ^ q with hV
  have hminle : min (ε ^ (-((1 - r) / (2 * r)))) ((N : ℝ) ^ s) ≤ ε ^ (-((1 - r) / (2 * r))) := min_le_left _ _
  have hminle2 : min (ε ^ (-((1 - r) / (2 * r)))) ((N : ℝ) ^ s) ≤ (N : ℝ) ^ s := min_le_right _ _
  have hmin0 : 0 ≤ min (ε ^ (-((1 - r) / (2 * r)))) ((N : ℝ) ^ s) :=
    le_min (Real.rpow_nonneg hε.le _) (Real.rpow_nonneg (by linarith) _)
  by_cases hcase : û ≤ V
  · obtain ⟨hlow, -⟩ := lem_app_phase_clock_integral_i hp hq hT N hN4 hε hε0 hYc hYf hhit hû0 hYû
      hcase hr (le_refl _)
    refine le_trans ?_ hlow
    calc _ ≤ (Real.sqrt (Aconst p) / (2 * (1 - r)) * (Aconst p / T) ^ ((1 - r) / (2 * r))) *
          min (ε ^ (-((1 - r) / (2 * r)))) ((N : ℝ) ^ s) :=
          mul_le_mul_of_nonneg_right (min_le_left _ _) hmin0
      _ ≤ _ := by
          exact mul_le_mul_of_nonneg_left hminle (by positivity)
  · push_neg at hcase
    have hL := un_L1 hp hq N hN4 hYc hYf hV0 le_rfl hcase.le
    rw [un_Ir_lt hr0 hr hV0] at hL
    have hVs : V ^ (1 - r) = (N : ℝ) ^ s * (4 : ℝ) ^ (-s) := by
      rw [hV, ← Real.rpow_mul (by positivity), Real.div_rpow (by positivity) (by norm_num),
        Real.rpow_neg (by norm_num), div_eq_mul_inv]
    have hVge : 2 ≤ V ^ (1 - r) := by
      have : 2 ≤ ((N : ℝ) / 4) ^ s := by
        apply un_pow_ge_two hs0
        rw [le_div_iff₀ (by norm_num)]
        linarith
      calc (2 : ℝ) ≤ ((N : ℝ) / 4) ^ s := this
        _ = V ^ (1 - r) := by
          rw [hV, ← Real.rpow_mul (by positivity)]
    have h1V : V ^ (1 - r) ≤ (1 + V) ^ (1 - r) :=
      Real.rpow_le_rpow hV0 (by linarith) h1r.le
    have hq2 : Real.sqrt (Aconst p) * (((1 + V) ^ (1 - r) - 1) / (1 - r))
        ≥ Real.sqrt (Aconst p) / (2 * (1 - r)) * V ^ (1 - r) := by
      have : V ^ (1 - r) / (2 * (1 - r)) ≤ ((1 + V) ^ (1 - r) - 1) / (1 - r) := by
        rw [div_le_div_iff₀ (by positivity) h1r]
        nlinarith
      calc Real.sqrt (Aconst p) / (2 * (1 - r)) * V ^ (1 - r)
          = Real.sqrt (Aconst p) * (V ^ (1 - r) / (2 * (1 - r))) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left this hsA.le
    refine le_trans ?_ (hq2.le.trans hL)
    rw [hVs]
    calc _ ≤ (Real.sqrt (Aconst p) / (2 * (1 - r)) * (4 : ℝ) ^ (-s)) *
          min (ε ^ (-((1 - r) / (2 * r)))) ((N : ℝ) ^ s) :=
          mul_le_mul_of_nonneg_right (min_le_right _ _) hmin0
      _ ≤ (Real.sqrt (Aconst p) / (2 * (1 - r)) * (4 : ℝ) ^ (-s)) * (N : ℝ) ^ s :=
          mul_le_mul_of_nonneg_left hminle2 (by positivity)
      _ = _ := by ring

private lemma un_lower_eq {p q T : ℝ} (hp : 1 < p) (hq : 0 < q) (hT : 4 ≤ T) (hr : rq p q = 1) :
    ∃ (N0 : ℕ) (cm : ℝ), 4 ≤ N0 ∧ 0 < cm ∧ ∀ (N : ℕ) (ε : ℝ) (Y : ℝ → ℝ) (û : ℝ),
      N0 ≤ N → 0 < ε → ε < clockEps0 p q T → ContinuousOn Y (Ici 0) →
      (∀ u ∈ Ici (0 : ℝ), fNq (N : ℕ∞) p q u ≤ Y u) →
      firstHit Y (T * ε) = ENNReal.ofReal û → 0 < û → Y û = T * ε →
      cm * min (Real.log (1 / ε)) (Real.log (N : ℝ)) ≤ ∫ u in (0 : ℝ)..û, Real.sqrt (Y u) := by
  have hA0 : 0 < Aconst p := by unfold Aconst; positivity
  have hsA : 0 < Real.sqrt (Aconst p) := Real.sqrt_pos.2 hA0
  refine ⟨16, min (Real.sqrt (Aconst p) / 4) (Real.sqrt (Aconst p) * (q / 2)), by norm_num,
    lt_min (by positivity) (by positivity), ?_⟩
  intro N ε Y û hN hε hε0 hYc hYf hhit hû0 hYû
  have hN4 : 4 ≤ N := by omega
  have hNr : (16 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0:ℝ) < N := by linarith
  obtain ⟨-, -, -, h14⟩ := un_eps_facts hε0
  have hlogε : 0 ≤ Real.log (1 / ε) := by
    apply Real.log_nonneg
    rw [le_div_iff₀ hε]; linarith
  have hlogN : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by linarith)
  have hmin0 : 0 ≤ min (Real.log (1 / ε)) (Real.log (N : ℝ)) := le_min hlogε hlogN
  have hV0 : 0 ≤ ((N : ℝ) / 4) ^ q := by positivity
  set V := ((N : ℝ) / 4) ^ q with hV
  by_cases hcase : û ≤ V
  · obtain ⟨hlow, -⟩ := lem_app_phase_clock_integral_ii hp hq hT N hN4 hε hε0 hYc hYf hhit hû0 hYû
      hcase hr (le_refl _)
    refine le_trans ?_ hlow
    calc _ ≤ Real.sqrt (Aconst p) / 4 * min (Real.log (1 / ε)) (Real.log (N : ℝ)) :=
          mul_le_mul_of_nonneg_right (min_le_left _ _) hmin0
      _ ≤ _ := mul_le_mul_of_nonneg_left (min_le_left _ _) (by positivity)
  · push_neg at hcase
    have hL := un_L1 hp hq N hN4 hYc hYf hV0 le_rfl hcase.le
    rw [hr, un_Ir_one hV0] at hL
    have hlogV : q / 2 * Real.log (N : ℝ) ≤ Real.log (1 + V) := by
      have h1 : Real.log (N : ℝ) ≤ 2 * Real.log ((N : ℝ) / 4) := by
        rw [← Real.log_rpow (by positivity)]
        apply Real.log_le_log hN0
        rw [show ((N : ℝ) / 4) ^ (2 : ℝ) = (N : ℝ) ^ 2 / 16 by
          rw [Real.rpow_two]; ring]
        rw [le_div_iff₀ (by norm_num)]; nlinarith
      have hVpos : 0 < V := by rw [hV]; positivity
      have h2 : Real.log V ≤ Real.log (1 + V) := Real.log_le_log hVpos (by linarith)
      have h3 : Real.log V = q * Real.log ((N : ℝ) / 4) := by
        rw [hV, Real.log_rpow (by positivity)]
      nlinarith
    calc _ ≤ (Real.sqrt (Aconst p) * (q / 2)) * min (Real.log (1 / ε)) (Real.log (N : ℝ)) :=
            mul_le_mul_of_nonneg_right (min_le_right _ _) hmin0
      _ ≤ (Real.sqrt (Aconst p) * (q / 2)) * Real.log (N : ℝ) :=
            mul_le_mul_of_nonneg_left (min_le_right _ _) (by positivity)
      _ = Real.sqrt (Aconst p) * (q / 2 * Real.log (N : ℝ)) := by ring
      _ ≤ Real.sqrt (Aconst p) * Real.log (1 + V) :=
            mul_le_mul_of_nonneg_left hlogV hsA.le
      _ ≤ _ := hL

private lemma un_lower_gt {p q T : ℝ} (hp : 1 < p) (hq : 0 < q) (hT : 4 ≤ T) (hr : 1 < rq p q) :
    ∃ (N0 : ℕ) (cm : ℝ), 4 ≤ N0 ∧ 0 < cm ∧ ∀ (N : ℕ) (ε : ℝ) (Y : ℝ → ℝ) (û : ℝ),
      N0 ≤ N → 0 < ε → ε < clockEps0 p q T → ContinuousOn Y (Ici 0) →
      (∀ u ∈ Ici (0 : ℝ), fNq (N : ℕ∞) p q u ≤ Y u) →
      firstHit Y (T * ε) = ENNReal.ofReal û → 0 < û → Y û = T * ε →
      cm * (1 : ℝ) ≤ ∫ u in (0 : ℝ)..û, Real.sqrt (Y u) := by
  refine ⟨4, 1 / (2 * Real.sqrt 2), le_refl _, by positivity, ?_⟩
  intro N ε Y û hN hε hε0 hYc hYf hhit hû0 hYû
  obtain ⟨hlow, -⟩ := lem_app_phase_clock_integral_iii hp hq hT N hN hε hε0 hYc hYf hhit hû0 hYû
    (le_refl _) hr
  simpa using hlow

private lemma un_clockEps0_pos {p q T : ℝ} (hp : 1 < p) (hq : 0 < q) (hT : 4 ≤ T) :
    0 < clockEps0 p q T := by
  have hT0 : 0 < T := by linarith
  have hC : 0 < Cpq p q := by
    unfold Cpq
    apply Real.sqrt_pos.2
    have : 0 < Epq p q := by
      unfold Epq
      refine lt_max_of_lt_left ?_
      have : 0 < Za p := by
        unfold Za
        have := div_pos one_pos (show (0 : ℝ) < p - 1 by linarith)
        linarith
      exact mul_pos (Real.rpow_pos_of_pos (by norm_num) _) this
    positivity
  have hA : 0 < Aconst p := by unfold Aconst; positivity
  unfold clockEps0
  split_ifs
  · simp only [lt_min_iff]
    refine ⟨⟨⟨⟨by norm_num, by positivity⟩, by positivity⟩, by positivity⟩, by positivity⟩
  · simp only [lt_min_iff]
    refine ⟨⟨⟨by norm_num, by positivity⟩, by positivity⟩, by positivity⟩

private lemma un_hit_j (α ς T : ℝ) (j : PhaseKind) (N B : ℕ) (hα : 0 < α) (hp : 1 < α + ς)
    (hT : 4 ≤ T) (hN : 1 ≤ N) (hNB : N ≤ B) (ε : ℝ) (hε : 0 < ε) (hε8 : ε < 1 / (8 * T))
    (m : RowModel (Fin N)) (Q : ℝ → ℝ) (hm : IsMatchedModel (phaseKindArrays α ς N B j) m ε)
    (hQ : IsVolterraSol m Q) :
    ContinuousOn (fun u => Q (phaseKindT0 α N B j * u)) (Ici 0) ∧
    (∀ u ∈ Ici (0 : ℝ), fNq (N : ℕ∞) (α + ς) (phaseKindQ α j) u ≤ Q (phaseKindT0 α N B j * u)) ∧
    ∃ û : ℝ, 0 < û ∧ Q (phaseKindT0 α N B j * û) = T * ε ∧
      firstHit (fun u => Q (phaseKindT0 α N B j * u)) (T * ε) = ENNReal.ofReal û := by
  obtain ⟨hT0, hS, hgc, hgn, -, -, -, -, hYe⟩ := un_facts α ς j N B hα hp hN hNB ε hε m Q hm hQ
  obtain ⟨hYc, -⟩ := un_Q_facts m Q hQ _ hT0
  have hYf : ∀ u ∈ Ici (0 : ℝ), fNq (N : ℕ∞) (α + ς) (phaseKindQ α j) u ≤ Q (phaseKindT0 α N B j * u) := by
    intro u hu
    rw [hYe u hu]
    have hconv0 : 0 ≤ Muon.Foundations.oneSidedConv
        (fun v => Real.sqrt (Q (phaseKindT0 α N B j * v))) (dimKernel m (phaseKindT0 α N B j) ε) u := by
      unfold Muon.Foundations.oneSidedConv
      apply intervalIntegral.integral_nonneg hu
      intro s hs
      exact mul_nonneg (Real.sqrt_nonneg _) (hgn s (Set.mem_Ici.2 hs.1))
    have := mul_nonneg (Real.sqrt_pos.2 hε).le hconv0
    linarith
  refine ⟨hYc, hYf, ?_⟩
  exact un_hitpkg hp hT N hN hε hε8 hYc hYf (un_attain α ς T j N B hα hp hT hN hNB ε hε m Q hm hQ)

private lemma un_I_eq (Q : ℝ → ℝ) (T0 T ε û : ℝ) (hû : 0 < û)
    (h : firstHit (fun u => Q (T0 * u)) (T * ε) = ENNReal.ofReal û) :
    phaseClockI Q T0 T ε = ∫ u in (0 : ℝ)..û, Real.sqrt (Q (T0 * u)) := by
  unfold phaseClockI dimClockI
  rw [h, ENNReal.toReal_ofReal hû.le]

private lemma un_q_pos (α : ℝ) (hα : 0 < α) (j : PhaseKind) : 0 < phaseKindQ α j := by
  cases j <;> simp [phaseKindQ] <;> linarith

private lemma un_ST_pos (α ς : ℝ) (j : PhaseKind) (N B : ℕ) (hα : 0 < α) (hp : 1 < α + ς)
    (hN : 1 ≤ N) (hNB : N ≤ B) (ε : ℝ) (hε : 0 < ε) :
    0 < PhaseArrays.S (phaseKindArrays α ς N B j) ∧ 0 < phaseKindT0 α N B j := by
  obtain ⟨h1, h2, h3, h4⟩ := un_pos α ς N B hα hp hN hNB ε hε
  cases j
  · exact ⟨h1, h3⟩
  · exact ⟨h2, h4⟩

private lemma un_Upsilon_nonneg (α ς : ℝ) (N : ℕ) (ε : ℝ) (j : PhaseKind) (hN : 1 ≤ N)
    (hε : 0 < ε) (hε1 : ε < 1) : 0 ≤ phaseUpsilon α ς N ε j := by
  unfold phaseUpsilon
  split_ifs
  · exact le_min (Real.rpow_nonneg hε.le _) (Real.rpow_nonneg (Nat.cast_nonneg N) _)
  · exact le_min (Real.log_nonneg (one_le_one_div hε hε1.le)) (Real.log_nonneg (by exact_mod_cast hN))
  · exact zero_le_one

/-- Time identity: the step time is `(S T0 / (2 √ε)) 𝖨_j` (from `prop_app_phase_prefactors_iii`). -/
private lemma un_step_eq (α ς T : ℝ) (hα : 0 < α) (hp : 1 < α + ς) (hT : 0 < T) (j : PhaseKind)
    (N B : ℕ) (hN : 1 ≤ N) (hNB : N ≤ B) (ε : ℝ) (hε : 0 < ε) (m : RowModel (Fin N))
    (Q : ℝ → ℝ) (hm : IsMatchedModel (phaseKindArrays α ς N B j) m ε) (hQ : IsVolterraSol m Q)
    (hfin : dimHit Q (phaseKindT0 α N B j) T ε ≠ ⊤) :
    (stepHit m Q T ε).toReal = PhaseArrays.S (phaseKindArrays α ς N B j) * phaseKindT0 α N B j
      / (2 * Real.sqrt ε) * phaseClockI Q (phaseKindT0 α N B j) T ε := by
  obtain ⟨hSp, hT0p⟩ := un_ST_pos α ς j N B hα hp hN hNB ε hε
  have hI : 0 ≤ ∫ u in (0 : ℝ)..(firstHit (fun u => Q (phaseKindT0 α N B j * u)) (T * ε)).toReal,
      Real.sqrt (Q (phaseKindT0 α N B j * u)) :=
    intervalIntegral.integral_nonneg ENNReal.toReal_nonneg (fun u _ => Real.sqrt_nonneg _)
  have hpos : 0 ≤ PhaseArrays.S (phaseKindArrays α ς N B j) * phaseKindT0 α N B j
      / (2 * Real.sqrt ε) :=
    div_nonneg (mul_nonneg hSp.le hT0p.le) (by positivity)
  unfold stepHit
  cases j with
  | svd =>
    obtain ⟨mG, QG, hmG, hQG⟩ := un_pair_svd α ς N B hα hp hN hNB ε hε
    have hm' : IsMatchedModel (svdArrays α ς N B) m ε := hm
    have hpref := (prop_app_phase_prefactors_iii α ς N B hα hp hN hNB ε T hε hT m mG hm' hmG
      Q QG hQ hQG).1 hfin
    have hS : m.S = (svdArrays α ς N B).S := un_S_eq _ m ε hm'
    rw [hpref, ENNReal.toReal_ofReal]
    · rw [hS]; rfl
    · rw [hS]; exact mul_nonneg hpos hI
  | sgd =>
    obtain ⟨mS, QS, hmS, hQS⟩ := un_pair_sgd α ς N B hα hp hN hNB ε hε
    have hm' : IsMatchedModel (sgdArrays α ς N B) m ε := hm
    have hpref := (prop_app_phase_prefactors_iii α ς N B hα hp hN hNB ε T hε hT mS m hmS hm'
      QS Q hQS hQ).2 hfin
    have hS : m.S = (sgdArrays α ς N B).S := un_S_eq _ m ε hm'
    rw [hpref, ENNReal.toReal_ofReal]
    · rw [hS]; rfl
    · rw [hS]; exact mul_nonneg hpos hI

private lemma un_sw_transfer {cL cH cL' cH' a G P Z y : ℝ} (hG : 0 ≤ G) (hP : 0 ≤ P)
    (hcL : 0 ≤ cL) (hcH : 0 ≤ cH) (hZlo : a * P ≤ Z) (hZhi : Z ≤ P)
    (hcL' : cL' ≤ cL * a) (hcH' : cH ≤ cH') (h1 : cL * (G * Z) ≤ y) (h2 : y ≤ cH * (G * Z)) :
    cL' * (G * P) ≤ y ∧ y ≤ cH' * (G * P) := by
  have hGP : 0 ≤ G * P := mul_nonneg hG hP
  refine ⟨?_, ?_⟩
  · calc cL' * (G * P) ≤ cL * a * (G * P) := mul_le_mul_of_nonneg_right hcL' hGP
      _ = cL * (G * (a * P)) := by ring
      _ ≤ cL * (G * Z) := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hZlo hG) hcL
      _ ≤ y := h1
  · calc y ≤ cH * (G * Z) := h2
      _ ≤ cH * (G * P) := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hZhi hG) hcH
      _ ≤ cH' * (G * P) := mul_le_mul_of_nonneg_right hcH' hGP

/-- Ratio of the extended window: on `ε ≥ ε_N`, `ε^{-1/2} Υ_j` is comparable to `Π_{r_j}(ε)`. -/
private lemma un_ratio (α ς : ℝ) (hα : 1 < α) (hς : 1 ≤ ς) (j : PhaseKind) (N : ℕ) (ε : ℝ)
    (hN : 1 ≤ N) (hε : 0 < ε) (hε1 : ε < 1) (hw : phaseEpsN (α + ς) N ≤ ε) :
    min 1 (1 / (2 * phaseKindQ α j)) * phasePi (phaseKindR α ς j) ε
        ≤ ε ^ (-(1 / 2 : ℝ)) * phaseUpsilon α ς N ε j ∧
      ε ^ (-(1 / 2 : ℝ)) * phaseUpsilon α ς N ε j ≤ phasePi (phaseKindR α ς j) ε ∧
      0 ≤ phasePi (phaseKindR α ς j) ε := by
  have hq : 0 < phaseKindQ α j := un_q_pos α (by linarith) j
  have hq0 : phaseKindQ α j ≠ 0 := hq.ne'
  have hp : 1 < α + ς := by linarith
  have hr : phaseKindR α ς j = (α + ς - 1) / (2 * phaseKindQ α j) := rfl
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hw' : (N : ℝ) ^ (-(α + ς - 1)) ≤ ε := hw
  have hs : 0 < ε ^ (-(1 / 2 : ℝ)) := Real.rpow_pos_of_pos hε _
  have hL0 : 0 ≤ Real.log (1 / ε) := Real.log_nonneg (one_le_one_div hε hε1.le)
  unfold phasePi phaseUpsilon
  rcases lt_trichotomy (phaseKindR α ς j) 1 with h | h | h
  · -- r < 1
    have hrpos : 0 < phaseKindR α ς j := by
      rw [hr]; exact div_pos (by linarith) (by linarith)
    have hr0 : phaseKindR α ς j ≠ 0 := hrpos.ne'
    simp only [if_pos h]
    have hinv : ε⁻¹ ≤ (N : ℝ) ^ (α + ς - 1) := by
      have h1 := inv_anti₀ (Real.rpow_pos_of_pos hN0 (-(α + ς - 1))) hw'
      rw [Real.rpow_neg hN0.le, inv_inv] at h1
      exact h1
    have hc0 : 0 ≤ (1 - phaseKindR α ς j) / (2 * phaseKindR α ς j) :=
      div_nonneg (by linarith) (by linarith)
    have hexp : (α + ς - 1) * ((1 - phaseKindR α ς j) / (2 * phaseKindR α ς j))
        = phaseKindQ α j * (1 - phaseKindR α ς j) := by
      have h2 : α + ς - 1 = 2 * phaseKindQ α j * phaseKindR α ς j := by
        rw [hr]; field_simp
      rw [h2]; field_simp; try ring
    have hA : ε ^ (-((1 - phaseKindR α ς j) / (2 * phaseKindR α ς j)))
        ≤ (N : ℝ) ^ (phaseKindQ α j * (1 - phaseKindR α ς j)) := by
      rw [Real.rpow_neg hε.le, ← Real.inv_rpow hε.le]
      calc ε⁻¹ ^ ((1 - phaseKindR α ς j) / (2 * phaseKindR α ς j))
          ≤ ((N : ℝ) ^ (α + ς - 1)) ^ ((1 - phaseKindR α ς j) / (2 * phaseKindR α ς j)) :=
            Real.rpow_le_rpow (inv_nonneg.2 hε.le) hinv hc0
        _ = (N : ℝ) ^ (phaseKindQ α j * (1 - phaseKindR α ς j)) := by
            rw [← Real.rpow_mul hN0.le, hexp]
    have hsplit : ε ^ (-(1 / 2 : ℝ)) * ε ^ (-((1 - phaseKindR α ς j) / (2 * phaseKindR α ς j)))
        = ε ^ (-(1 / (2 * phaseKindR α ς j))) := by
      rw [← Real.rpow_add hε]
      congr 1
      field_simp
      try ring
    rw [min_eq_left hA, hsplit]
    exact ⟨mul_le_of_le_one_left (Real.rpow_nonneg hε.le _) (min_le_left _ _), le_refl _,
      Real.rpow_nonneg hε.le _⟩
  · -- r = 1
    have hn : ¬ (phaseKindR α ς j < 1) := not_lt.2 h.ge
    simp only [if_neg hn, if_pos h]
    have h2q : α + ς - 1 = 2 * phaseKindQ α j := by
      have h' := h
      rw [hr] at h'
      exact (div_eq_one_iff_eq (mul_ne_zero two_ne_zero hq0)).1 h'
    have hl : -(α + ς - 1) * Real.log N ≤ Real.log ε := by
      have := Real.log_le_log (Real.rpow_pos_of_pos hN0 (-(α + ς - 1))) hw'
      rwa [Real.log_rpow hN0] at this
    have hlinv : Real.log (1 / ε) = -Real.log ε := by rw [one_div, Real.log_inv]
    have hlog : Real.log (1 / ε) ≤ 2 * phaseKindQ α j * Real.log N := by
      rw [hlinv, ← h2q]
      linarith
    have hc0 : min 1 (1 / (2 * phaseKindQ α j)) * Real.log (1 / ε) ≤ Real.log N := by
      calc min 1 (1 / (2 * phaseKindQ α j)) * Real.log (1 / ε)
          ≤ (1 / (2 * phaseKindQ α j)) * Real.log (1 / ε) :=
            mul_le_mul_of_nonneg_right (min_le_right _ _) hL0
        _ ≤ (1 / (2 * phaseKindQ α j)) * (2 * phaseKindQ α j * Real.log N) :=
            mul_le_mul_of_nonneg_left hlog (div_nonneg zero_le_one (by linarith))
        _ = Real.log N := by field_simp
    refine ⟨?_, ?_, mul_nonneg hs.le hL0⟩
    · calc min 1 (1 / (2 * phaseKindQ α j)) * (ε ^ (-(1 / 2 : ℝ)) * Real.log (1 / ε))
          = ε ^ (-(1 / 2 : ℝ)) * (min 1 (1 / (2 * phaseKindQ α j)) * Real.log (1 / ε)) := by ring
        _ ≤ ε ^ (-(1 / 2 : ℝ)) * min (Real.log (1 / ε)) (Real.log N) :=
            mul_le_mul_of_nonneg_left
              (le_min (mul_le_of_le_one_left hL0 (min_le_left _ _)) hc0) hs.le
    · exact mul_le_mul_of_nonneg_left (min_le_left _ _) hs.le
  · -- r > 1
    have hn1 : ¬ (phaseKindR α ς j < 1) := not_lt.2 h.le
    have hn2 : ¬ (phaseKindR α ς j = 1) := h.ne'
    simp only [if_neg hn1, if_neg hn2]
    refine ⟨?_, ?_, hs.le⟩
    · rw [mul_one]; exact mul_le_of_le_one_left hs.le (min_le_left _ _)
    · rw [mul_one]

/-- The exhaustive regime split used by the upper half of the unified-clock theorem.  The
noncriticality clauses in `phaseInU` remove exactly the three template endpoints. -/
private lemma un_upper_regimes (α ς : ℝ) (j : PhaseKind)
    (hU : phaseInU α ς j) :
    phaseKindR α ς j < 1 ∨
      (j = .svd ∧ ((α < 1) ∨ (1 < α ∧ α < 2) ∨ 2 ≤ α)) ∨
      (j = .sgd ∧ ((α < 1 / 2) ∨ (1 / 2 < α ∧ α < 1) ∨ 1 < α)) := by
  cases j with
  | svd =>
      simp only [phaseInU, true_and] at hU ⊢
      rcases hU with hr | hne
      · exact Or.inl hr
      · right; left
        rcases lt_trichotomy α 1 with ha | ha | ha
        · exact Or.inl ha
        · exact False.elim (hne ha)
        · rcases lt_or_ge α 2 with ha2 | ha2
          · exact Or.inr (Or.inl ⟨ha, ha2⟩)
          · exact Or.inr (Or.inr ha2)
  | sgd =>
      simp only [phaseInU, true_and] at hU ⊢
      rcases hU with hr | ⟨hne_half, hne_one⟩
      · exact Or.inl hr
      · right; right
        rcases lt_trichotomy α (1 / 2) with ha | ha | ha
        · exact Or.inl ha
        · exact False.elim (hne_half ha)
        · rcases lt_trichotomy α 1 with ha1 | ha1 | ha1
          · exact Or.inr (Or.inl ⟨ha, ha1⟩)
          · exact False.elim (hne_one ha1)
          · exact Or.inr (Or.inr ha1)

/-! ### Upper bound, regime `r_j < 1` (P-H.16.P1) -/


private lemma uu_eps_eq {p ε : ℝ} {N : ℕ} (hN : 1 ≤ N) (hε : 0 < ε) :
    ε = phaseX p N ε * (N : ℝ) ^ (-(p - 1)) := by
  have hNr : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hNp : 0 < (N : ℝ) ^ (-(p - 1)) := Real.rpow_pos_of_pos hNr _
  unfold phaseX phaseEpsN
  field_simp

/-- `ε^{-s} = x^{-s} N^{(p-1) s}`. -/
private lemma uu_eps_rpow {p ε : ℝ} {N : ℕ} (hN : 1 ≤ N) (hε : 0 < ε) (s : ℝ) :
    ε ^ (-s) = phaseX p N ε ^ (-s) * (N : ℝ) ^ ((p - 1) * s) := by
  have hNr : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hx : 0 < phaseX p N ε := by
    unfold phaseX phaseEpsN
    exact div_pos hε (Real.rpow_pos_of_pos hNr _)
  conv_lhs => rw [uu_eps_eq (p := p) hN hε]
  rw [Real.mul_rpow hx.le (Real.rpow_pos_of_pos hNr _).le, ← Real.rpow_mul hNr.le]
  congr 2
  ring


private lemma uu_pow_le {x X a : ℝ} (hx : 0 < x) (hxX : x ≤ X) (hX : 1 ≤ X) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    x ^ a ≤ X := by
  calc x ^ a ≤ X ^ a := Real.rpow_le_rpow hx.le hxX ha0
    _ ≤ X ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hX ha1
    _ = X := Real.rpow_one X

/-- The band bound: `frozenErrBound` is `≲ N^{q(1-r)}` for `x ≤ X` (`X ≥ 1`) once `J_N ≲ N^{q(1-r)}`. -/
private lemma uu_band {C q r D τ x X G : ℝ} {N : ℕ} {J : ℝ} (hC : 0 < C) (hr0 : 0 < r) (hr1 : r < 1)
    (hD : 0 < D) (hτ : 0 < τ) (hx : 0 < x) (hxX : x ≤ X) (hX : 1 ≤ X) (hG : 0 ≤ G)
    (hJ : J ≤ G * (N : ℝ) ^ (q * (1 - r))) (hN : 1 ≤ N) :
    frozenErrBound C q r D τ x N J ≤
      (G + (frozenC1 C r D τ + Real.sqrt (2 * frozenC2 C r D τ) + τ + 1) * X
        + 2 * Real.sqrt ((G + (Real.sqrt (2 * frozenC2 C r D τ) + 1) * X)
            * ((4 + 4 * Real.sqrt (frozenC2 C r D τ)) * X))
        + (4 + 4 * Real.sqrt (frozenC2 C r D τ)) * X) * (N : ℝ) ^ (q * (1 - r)) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  set M : ℝ := (N : ℝ) ^ (q * (1 - r)) with hM
  have hM0 : 0 < M := Real.rpow_pos_of_pos hNr _
  have hc2 : 0 ≤ frozenC2 C r D τ := by unfold frozenC2; positivity
  have hc1 : 0 ≤ frozenC1 C r D τ := by
    unfold frozenC1
    have : 0 < 1 - r / 2 := by linarith
    positivity
  have hq4 : x ^ (1 / 4 : ℝ) ≤ X := uu_pow_le hx hxX hX (by norm_num) (by norm_num)
  have hq2 : x ^ (1 / 2 : ℝ) ≤ X := uu_pow_le hx hxX hX (by norm_num) (by norm_num)
  have hq40 : 0 ≤ x ^ (1 / 4 : ℝ) := by positivity
  have hq20 : 0 ≤ x ^ (1 / 2 : ℝ) := by positivity
  have hs1 : 0 ≤ Real.sqrt (2 * frozenC2 C r D τ) := Real.sqrt_nonneg _
  have hs2 : 0 ≤ Real.sqrt (frozenC2 C r D τ) := Real.sqrt_nonneg _
  have hX0 : 0 ≤ X := by linarith
  have ha1 : frozenA1 C r D τ x ≤ (frozenC1 C r D τ + Real.sqrt (2 * frozenC2 C r D τ) + τ + 1) * X := by
    unfold frozenA1
    nlinarith [mul_le_mul_of_nonneg_left hq4 (add_nonneg hc1 hs1), mul_le_mul_of_nonneg_left hq2 (show 0 ≤ τ + 1 by linarith)]
  have ha2 : frozenA2 C r D τ x ≤ (Real.sqrt (2 * frozenC2 C r D τ) + 1) * X := by
    unfold frozenA2
    nlinarith [mul_le_mul_of_nonneg_left hq4 hs1]
  have hdt : frozenDt C r D τ x ≤ (4 + 4 * Real.sqrt (frozenC2 C r D τ)) * X := by
    unfold frozenDt
    refine (fz3_dt_bound hx hc2).2.trans ?_
    nlinarith [mul_le_mul_of_nonneg_left hq4 (show 0 ≤ 4 * Real.sqrt (frozenC2 C r D τ) by positivity)]
  have hdt0 : 0 ≤ frozenDt C r D τ x := (fz3_dt_bound hx hc2).1
  have ha20 : 0 ≤ frozenA2 C r D τ x := by unfold frozenA2; positivity
  unfold frozenErrBound
  rw [← hM]
  have hAA : 0 ≤ (Real.sqrt (2 * frozenC2 C r D τ) + 1) * X := by positivity
  have hDD : 0 ≤ (4 + 4 * Real.sqrt (frozenC2 C r D τ)) * X := by positivity
  have hprod : (J + frozenA2 C r D τ x * M) * (frozenDt C r D τ x * M) ≤
      ((G + (Real.sqrt (2 * frozenC2 C r D τ) + 1) * X) * ((4 + 4 * Real.sqrt (frozenC2 C r D τ)) * X)) * M ^ 2 := by
    have h1 : J + frozenA2 C r D τ x * M ≤ (G + (Real.sqrt (2 * frozenC2 C r D τ) + 1) * X) * M := by
      nlinarith [mul_le_mul_of_nonneg_right ha2 hM0.le]
    have h2 : frozenDt C r D τ x * M ≤ ((4 + 4 * Real.sqrt (frozenC2 C r D τ)) * X) * M :=
      mul_le_mul_of_nonneg_right hdt hM0.le
    calc _ ≤ ((G + (Real.sqrt (2 * frozenC2 C r D τ) + 1) * X) * M) * (((4 + 4 * Real.sqrt (frozenC2 C r D τ)) * X) * M) :=
          mul_le_mul h1 h2 (by positivity) (by positivity)
      _ = _ := by ring
  have hsq : Real.sqrt ((J + frozenA2 C r D τ x * M) * (frozenDt C r D τ x * M)) ≤
      Real.sqrt ((G + (Real.sqrt (2 * frozenC2 C r D τ) + 1) * X) * ((4 + 4 * Real.sqrt (frozenC2 C r D τ)) * X)) * M := by
    refine (Real.sqrt_le_sqrt hprod).trans ?_
    rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hM0.le]
  nlinarith [mul_le_mul_of_nonneg_right ha1 hM0.le, mul_le_mul_of_nonneg_right hdt hM0.le]


private lemma uu_H {p q D C τ' ε : ℝ} {N : ℕ} (hp : 1 < p) (hq : 0 < q) (hN : 1 ≤ N) (hε : 0 < ε)
    (hC : 0 < C) (hD : 0 < D) (hτ' : 0 < τ')
    (hxE : (D * C ^ (1 / rq p q) / τ') ^ (2 * rq p q) ≤ phaseX p N ε) :
    D * ((C / Real.sqrt ε) ^ (1 / rq p q) - 1) ≤ τ' * (N : ℝ) ^ q := by
  have hr0 := pw_rq_pos hp hq
  have hNr : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  set r := rq p q with hr_def
  set x := phaseX p N ε with hx_def
  have hxpos : 0 < x := by
    rw [hx_def]; unfold phaseX phaseEpsN
    exact div_pos hε (Real.rpow_pos_of_pos hNr _)
  have hsq : 0 < Real.sqrt ε := Real.sqrt_pos.2 hε
  have hCr : 0 < C ^ (1 / r) := Real.rpow_pos_of_pos hC _
  -- (C/√ε)^(1/r) = C^(1/r) * ε^(-(1/(2r)))
  have h1 : (C / Real.sqrt ε) ^ (1 / r) = C ^ (1 / r) * ε ^ (-(1 / (2 * r))) := by
    have : C / Real.sqrt ε = C * ε ^ (-(1 / 2 : ℝ)) := by
      rw [Real.sqrt_eq_rpow, Real.rpow_neg hε.le]; ring
    rw [this, Real.mul_rpow hC.le (Real.rpow_nonneg hε.le _), ← Real.rpow_mul hε.le]
    congr 2; field_simp
  have h2 : ε ^ (-(1 / (2 * r))) = x ^ (-(1 / (2 * r))) * (N : ℝ) ^ q := by
    have := uu_eps_rpow (p := p) hN hε (1 / (2 * r))
    rw [this]
    have hp1 : (p - 1) ≠ 0 := (by linarith : (0:ℝ) < p - 1).ne'
    have : (p - 1) * (1 / (2 * r)) = q := by
      rw [hr_def]; unfold rq; field_simp
    rw [this]
  -- x^(1/(2r)) ≥ D C^(1/r)/τ'
  have h3 : D * C ^ (1 / r) / τ' ≤ x ^ (1 / (2 * r)) := by
    have hbase : 0 < D * C ^ (1 / r) / τ' := by positivity
    have := Real.rpow_le_rpow (by positivity) hxE (show 0 ≤ 1 / (2 * r) by positivity)
    rwa [← Real.rpow_mul hbase.le, show 2 * r * (1 / (2 * r)) = 1 by field_simp, Real.rpow_one] at this
  have h4 : x ^ (-(1 / (2 * r))) * (D * C ^ (1 / r)) ≤ τ' := by
    rw [Real.rpow_neg hxpos.le]
    have hxr : 0 < x ^ (1 / (2 * r)) := Real.rpow_pos_of_pos hxpos _
    rw [← div_eq_inv_mul, div_le_iff₀ hxr]
    rw [div_le_iff₀ hτ'] at h3
    linarith
  rw [h1, h2]
  have hQ : 0 < (N : ℝ) ^ q := Real.rpow_pos_of_pos hNr _
  have hx0 : 0 ≤ x ^ (-(1 / (2 * r))) := Real.rpow_nonneg hxpos.le _
  calc D * (C ^ (1 / r) * (x ^ (-(1 / (2 * r))) * (N : ℝ) ^ q) - 1)
      ≤ D * (C ^ (1 / r) * (x ^ (-(1 / (2 * r))) * (N : ℝ) ^ q)) := by nlinarith
    _ = (x ^ (-(1 / (2 * r))) * (D * C ^ (1 / r))) * (N : ℝ) ^ q := by ring
    _ ≤ τ' * (N : ℝ) ^ q := mul_le_mul_of_nonneg_right h4 hQ.le

private lemma uu_lt1 {p q T D τ : ℝ} (hp : 1 < p) (hq : 0 < q) (hT : 4 ≤ T)
    (hr : rq p q < 1) (hD : 1 ≤ D) (hτ : 0 < τ) :
    ∃ (N2 : ℕ) (K : ℝ), 0 < K ∧ ∀ (N : ℕ) (ε : ℝ) (w c : Fin N → ℝ) (Y : ℝ → ℝ),
      N2 ≤ N → 0 < ε → ε < clockEps0 p q T → (∀ l, 0 ≤ w l) → ∑ l, w l = 1 →
      (∀ l, 2 * (N : ℝ) ^ (-q) ≤ c l) →
      PhaseOneBound (mixG w c) (Cpq p q) q (rq p q) D τ N →
      ContinuousOn Y (Ici 0) → (∀ u ∈ Ici (0 : ℝ), 0 < Y u) →
      (∀ u ∈ Ici (0 : ℝ), Y u = fNq (N : ℕ∞) p q u +
        Real.sqrt ε * Muon.Foundations.oneSidedConv (fun v => Real.sqrt (Y v)) (mixG w c) u) →
      dimClockI Y T ε ≤ K * min (ε ^ (-((1 - rq p q) / (2 * rq p q))))
        ((N : ℝ) ^ (q * (1 - rq p q))) := by
  have hr0 := pw_rq_pos hp hq
  have hC := pw_Cpq_pos hp hq
  have hDpos : 0 < D := by linarith
  have hTpos : 0 < T := by linarith
  set r := rq p q with hr_def
  set C := Cpq p q with hC_def
  set s : ℝ := (1 - r) / (2 * r) with hs_def
  have hs0 : 0 < s := div_pos (by linarith) (by linarith)
  set τ' : ℝ := min τ ((1 / 4 : ℝ) ^ q) with hτ'_def
  have hτ'0 : 0 < τ' := lt_min hτ (Real.rpow_pos_of_pos (by norm_num) _)
  have hτ'τ : τ' ≤ τ := min_le_left _ _
  have hτ'4 : τ' ≤ (1 / 4 : ℝ) ^ q := min_le_right _ _
  set E : ℝ := (D * C ^ (1 / r) / τ') ^ (2 * r) with hE_def
  have hE0 : 0 < E := Real.rpow_pos_of_pos (by have := Real.rpow_pos_of_pos hC (1 / r); positivity) _
  set X : ℝ := max 1 E with hX_def
  have hX1 : 1 ≤ X := le_max_left _ _
  have hEX : E ≤ X := le_max_right _ _
  obtain ⟨L, U, hL, hU, hcore⟩ := pw_core hp hq hT hD hr
  set G : ℝ := 2 * Real.Gamma (1 - r) * C with hG_def
  have hG0 : 0 ≤ G := by
    have : 0 < Real.Gamma (1 - r) := Real.Gamma_pos_of_pos (by linarith)
    positivity
  set Kb : ℝ := (G + (frozenC1 C r D τ + Real.sqrt (2 * frozenC2 C r D τ) + τ + 1) * X
        + 2 * Real.sqrt ((G + (Real.sqrt (2 * frozenC2 C r D τ) + 1) * X)
            * ((4 + 4 * Real.sqrt (frozenC2 C r D τ)) * X))
        + (4 + 4 * Real.sqrt (frozenC2 C r D τ)) * X) with hKb_def
  have hKb0 : 0 ≤ Kb := by
    have hc2 : 0 ≤ frozenC2 C r D τ := by unfold frozenC2; positivity
    have hc1 : 0 ≤ frozenC1 C r D τ := by
      unfold frozenC1
      have : 0 < 1 - r / 2 := by linarith
      positivity
    have hX0 : 0 ≤ X := by linarith
    positivity
  set κ1 : ℝ := max 1 (E ^ (-s)) with hκ1
  set κ2 : ℝ := max 1 (E ^ s) with hκ2
  have hκ1' : 1 ≤ κ1 := le_max_left _ _
  have hκ2' : 1 ≤ κ2 := le_max_left _ _
  -- large N
  have hNt : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hDt : ∀ᶠ n : ℕ in atTop, D ≤ τ * (n : ℝ) ^ q := by
    have ht := (tendsto_rpow_atTop hq).comp hNt
    filter_upwards [ht.eventually_ge_atTop (D / τ)] with n hn
    rw [div_le_iff₀ hτ] at hn
    change D ≤ (n : ℝ) ^ q * τ at hn
    linarith
  obtain ⟨ND, hND⟩ := eventually_atTop.1 hDt
  refine ⟨max 4 ND, max (U * κ1) (Kb * κ2) + 1, by positivity, ?_⟩
  intro N ε w c Y hN hε hε0 hw hw1 hc hg hYc hYp hY
  have hN4 : 4 ≤ N := (le_max_left _ _).trans hN
  have hN1 : 1 ≤ N := by omega
  have hNr : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN1
  have hDN : D ≤ τ * (N : ℝ) ^ q := hND N ((le_max_right _ _).trans hN)
  obtain ⟨hε8, hεC⟩ := pw_eps_facts ε hε0
  have hεT : ε < 1 / (2 * T) := by
    refine lt_of_lt_of_le hε8 ?_
    exact one_div_le_one_div_of_le (by positivity) (by linarith)
  set x : ℝ := phaseX p N ε with hx_def
  have hxpos : 0 < x := by
    rw [hx_def]; unfold phaseX phaseEpsN
    exact div_pos hε (Real.rpow_pos_of_pos hNr _)
  set M : ℝ := (N : ℝ) ^ (q * (1 - r)) with hM_def
  have hM0 : 0 < M := Real.rpow_pos_of_pos hNr _
  have hPi : ε ^ (-s) = x ^ (-s) * M := by
    have hps : (p - 1) * s = q * (1 - r) := by
      have hp1 : (p - 1) ≠ 0 := (by linarith : (0:ℝ) < p - 1).ne'
      rw [hs_def, hr_def]; unfold rq; field_simp
    rw [hx_def, uu_eps_rpow (p := p) hN1 hε s, hM_def, hps]
  have hPi0 : 0 < ε ^ (-s) := Real.rpow_pos_of_pos hε _
  have hmin0 : 0 ≤ min (ε ^ (-s)) M := le_min hPi0.le hM0.le
  by_cases hxE : E ≤ x
  · -- window: pw_core
    have hHle : D * ((Cpq p q / Real.sqrt ε) ^ (1 / rq p q) - 1) ≤ τ' * (N : ℝ) ^ q :=
      uu_H hp hq hN1 hε hC hDpos hτ'0 hxE
    have hNQ : 0 < (N : ℝ) ^ q := Real.rpow_pos_of_pos hNr _
    have hH4 : D * ((Cpq p q / Real.sqrt ε) ^ (1 / rq p q) - 1) ≤ ((N : ℝ) / 4) ^ q := by
      refine hHle.trans ?_
      have : ((N : ℝ) / 4) ^ q = (1 / 4 : ℝ) ^ q * (N : ℝ) ^ q := by
        rw [← Real.mul_rpow (by norm_num) hNr.le]; congr 1; ring
      rw [this]
      exact mul_le_mul_of_nonneg_right hτ'4 hNQ.le
    have hbmin : 0 < 2 * (N : ℝ) ^ (-q) := by positivity
    have hgc : ContinuousOn (mixG w c) (Ici 0) := by
      have : Continuous (mixG w c) := by unfold mixG; fun_prop
      exact this.continuousOn
    obtain ⟨hgi, hgm⟩ := fz_g_int w c _ hbmin hw hw1 hc
    obtain ⟨û, hhit, hû, -, hup⟩ := hcore N ε (mixG w c) Y hN4 hε hε0 hgc
      (fun u _ => fz_g_nonneg w c _ hw hc hbmin u) hgi hgm.le hYc hYp hY
      (fun u hu => hg u ⟨hu.1, hu.2.trans (hHle.trans (mul_le_mul_of_nonneg_right hτ'τ hNQ.le))⟩) hH4
    have hI : dimClockI Y T ε = ∫ u in (0 : ℝ)..û, Real.sqrt (Y u) := by
      unfold dimClockI; rw [hhit, ENNReal.toReal_ofReal hû.le]
    rw [hI]
    have hxs : x ^ (-s) ≤ E ^ (-s) := Real.rpow_le_rpow_of_nonpos hE0 hxE (by linarith)
    have hPiM : ε ^ (-s) ≤ κ1 * M := by
      rw [hPi]
      calc x ^ (-s) * M ≤ E ^ (-s) * M := mul_le_mul_of_nonneg_right hxs hM0.le
        _ ≤ κ1 * M := mul_le_mul_of_nonneg_right (le_max_right _ _) hM0.le
    have hPimin : ε ^ (-s) ≤ κ1 * min (ε ^ (-s)) M := by
      rcases le_total (ε ^ (-s)) M with h | h
      · rw [min_eq_left h]; exact le_mul_of_one_le_left hPi0.le hκ1'
      · rw [min_eq_right h]; exact hPiM
    calc _ ≤ U * ε ^ (-s) := hup
      _ ≤ U * (κ1 * min (ε ^ (-s)) M) := mul_le_mul_of_nonneg_left hPimin hU.le
      _ = (U * κ1) * min (ε ^ (-s)) M := by ring
      _ ≤ (max (U * κ1) (Kb * κ2) + 1) * min (ε ^ (-s)) M :=
          mul_le_mul_of_nonneg_right (by linarith [le_max_left (U * κ1) (Kb * κ2)]) hmin0
  · -- band: frozen error bound
    push_neg at hxE
    have hxX : x ≤ X := (hxE.trans_le hEX).le
    have hup := lem_app_phase_frozenerr hp hq hr hT hε hεT hN4 hD hτ hDN w c hw hw1 hc hg Y hYc hYp hY
    have hJ := prop_app_phase_forcing_r_i hp hq hr N hN1
    have hband := uu_band (q := q) (N := N) hC hr0 hr hDpos hτ hxpos hxX hX1 hG0 hJ hN1
    have hMPi : M ≤ κ2 * ε ^ (-s) := by
      have : M = x ^ s * ε ^ (-s) := by
        have hxs : x ^ s * x ^ (-s) = 1 := by
          rw [← Real.rpow_add hxpos]; simp
        rw [hPi, ← mul_assoc, hxs, one_mul]
      rw [this]
      have : x ^ s ≤ κ2 := (Real.rpow_le_rpow hxpos.le hxE.le hs0.le).trans (le_max_right _ _)
      exact mul_le_mul_of_nonneg_right this hPi0.le
    have hMmin : M ≤ κ2 * min (ε ^ (-s)) M := by
      rcases le_total (ε ^ (-s)) M with h | h
      · rw [min_eq_left h]; exact hMPi
      · rw [min_eq_right h]; exact le_mul_of_one_le_left hM0.le hκ2'
    calc dimClockI Y T ε ≤ Kb * M := hup.trans hband
      _ ≤ Kb * (κ2 * min (ε ^ (-s)) M) := mul_le_mul_of_nonneg_left hMmin hKb0
      _ = (Kb * κ2) * min (ε ^ (-s)) M := by ring
      _ ≤ (max (U * κ1) (Kb * κ2) + 1) * min (ε ^ (-s)) M :=
          mul_le_mul_of_nonneg_right (by linarith [le_max_right (U * κ1) (Kb * κ2)]) hmin0


/-- The upper bound in the regime `r_j < 1` (the pw_core window and the frozen-error band). -/
private lemma uu_upper_lt1 (α ς T : ℝ) (hα : 0 < α) (hp : 1 < α + ς) (hT : 4 ≤ T)
    (j : PhaseKind) (hr : phaseKindR α ς j < 1) :
    ∃ (N0 : ℕ) (ε0 cp : ℝ), 0 < ε0 ∧ 0 < cp ∧
      ∀ (N B : ℕ) (ε : ℝ) (m : RowModel (Fin N)) (Q : ℝ → ℝ),
        N0 ≤ N → N ≤ B → 0 < ε → ε < ε0 →
        IsMatchedModel (phaseKindArrays α ς N B j) m ε → IsVolterraSol m Q →
        phaseClockI Q (phaseKindT0 α N B j) T ε ≤ cp * phaseUpsilon α ς N ε j := by
  have hq := un_q_pos α hα j
  have hε0pos : 0 < clockEps0 (α + ς) (phaseKindQ α j) T := pw_clockEps0_pos hp hq hT
  have hr' : rq (α + ς) (phaseKindQ α j) < 1 := hr
  cases j with
  | svd =>
    have hς : ς < 1 := by
      have h := hr'
      unfold rq phaseKindQ at h
      rw [div_lt_one (by linarith)] at h
      linarith
    obtain ⟨D, τ, N0, hD, hτ, h1⟩ := fz4_svd_one α ς hα (by linarith) hς
    obtain ⟨N2, K, hK, hmain⟩ := uu_lt1 (T := T) hp hq hT hr' hD hτ
    refine ⟨max N0 (max 1 N2), clockEps0 (α + ς) (phaseKindQ α .svd) T, K, hε0pos, hK, ?_⟩
    intro N B ε m Q hN hNB hε hε0 hm hQ
    have hN0 : N0 ≤ N := (le_max_left _ _).trans hN
    have hN1 : 1 ≤ N := (le_max_left _ _).trans ((le_max_right _ _).trans hN)
    have hNN : N2 ≤ N := (le_max_right _ _).trans ((le_max_right _ _).trans hN)
    obtain ⟨mG, QG, hmG, hQG⟩ := un_pair_svd α ς N B hα hp hN1 hNB ε hε
    obtain ⟨w, c, hw, hw1, hc, hker, hYc, hYp, hY⟩ :=
      fz2_svd_model α ς N B hα hp hN1 hNB ε hε m mG hm hmG Q QG hQ hQG
    have := hmain N ε w c _ hNN hε hε0 hw hw1 hc (h1 N hN0 hN1 w c hw hw1 hc hker) hYc hYp hY
    unfold phaseClockI phaseUpsilon
    rw [if_pos hr]
    exact this
  | sgd =>
    obtain ⟨D, τ, N0, hD, hτ, h1⟩ := fz4_sgd_one α ς hα hp hr'
    obtain ⟨N2, K, hK, hmain⟩ := uu_lt1 (T := T) hp hq hT hr' hD hτ
    refine ⟨max N0 (max 1 N2), clockEps0 (α + ς) (phaseKindQ α .sgd) T, K, hε0pos, hK, ?_⟩
    intro N B ε m Q hN hNB hε hε0 hm hQ
    have hN0 : N0 ≤ N := (le_max_left _ _).trans hN
    have hN1 : 1 ≤ N := (le_max_left _ _).trans ((le_max_right _ _).trans hN)
    have hNN : N2 ≤ N := (le_max_right _ _).trans ((le_max_right _ _).trans hN)
    obtain ⟨mS, QS, hmS, hQS⟩ := un_pair_sgd α ς N B hα hp hN1 hNB ε hε
    obtain ⟨w, c, hw, hw1, hc, hker, hYc, hYp, hY⟩ :=
      fz2_sgd_model α ς N B hα hp hN1 hNB ε hε mS m hmS hm QS Q hQS hQ
    have := hmain N ε w c _ hNN hε hε0 hw hw1 hc (h1 N hN0 hN1 w c hker) hYc hYp hY
    unfold phaseClockI phaseUpsilon
    rw [if_pos hr]
    exact this


/-! ### Upper bound, templated regime `r_j ≥ 1` (P-H.16.P1) -/

/-- The tail weight of `lem:app-phase-square-tail` in the templated proof, in closed form. -/
private lemma uu_wf_eq {ε A D Nq b u : ℝ} (hε : 0 < ε) (hD : 0 < D) (hNq : 0 < Nq) (hu : 0 ≤ u) :
    ε ^ (1 / 4 : ℝ) * Real.sqrt A * Nq ^ (-(1 / 2 : ℝ)) * ((D + u) / Nq) ^ (-(b / 2))
      = (ε ^ (1 / 4 : ℝ) * Real.sqrt A * Nq ^ (-(1 / 2 : ℝ)) * (D / Nq) ^ (-(b / 2))) *
          (1 + u / D) ^ (-(b / 2)) := by
  have h1 : (D + u) / Nq = (D / Nq) * (1 + u / D) := by field_simp
  have h2 : 0 < 1 + u / D := by have := div_nonneg hu hD.le; linarith
  rw [h1, Real.mul_rpow (div_pos hD hNq).le h2.le]
  ring

private lemma uu_wf_sq {ε A D Nq b u : ℝ} (hε : 0 < ε) (hA : 0 ≤ A) (hD : 0 < D) (hNq : 0 < Nq)
    (hu : 0 ≤ u) :
    (ε ^ (1 / 4 : ℝ) * Real.sqrt A * Nq ^ (-(1 / 2 : ℝ)) * ((D + u) / Nq) ^ (-(b / 2))) ^ 2
        / Real.sqrt ε = A * Nq⁻¹ * ((D + u) / Nq) ^ (-b) := by
  have hq : (ε ^ (1 / 4 : ℝ)) ^ 2 = Real.sqrt ε := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hε.le, Real.sqrt_eq_rpow]; norm_num
  have hNn : (Nq ^ (-(1 / 2 : ℝ))) ^ 2 = Nq⁻¹ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hNq.le]
    rw [show (-(1 / 2 : ℝ)) * ((2 : ℕ) : ℝ) = -1 by push_cast; ring, Real.rpow_neg_one]
  have hb : (((D + u) / Nq) ^ (-(b / 2))) ^ 2 = ((D + u) / Nq) ^ (-b) := by
    have hpos : 0 ≤ (D + u) / Nq := div_nonneg (by linarith) hNq.le
    rw [← Real.rpow_natCast, ← Real.rpow_mul hpos]
    congr 1; push_cast; ring
  have hs : 0 < Real.sqrt ε := Real.sqrt_pos.2 hε
  rw [mul_pow, mul_pow, mul_pow, hq, Real.sq_sqrt hA, hNn, hb]
  field_simp

/-- `∫_0^z C (1+u/D)^{-r} = C D I_r(z/D)`. -/
private lemma uu_int_h {C D r z : ℝ} (hD : 0 < D) :
    ∫ u in (0 : ℝ)..z, C * (1 + u / D) ^ (-r) = C * D * Ir r (z / D) := by
  rw [intervalIntegral.integral_const_mul]
  have := intervalIntegral.integral_comp_div (a := (0 : ℝ)) (b := z) (fun t : ℝ => (1 + t) ^ (-r)) hD.ne'
  simp only [zero_div] at this
  rw [this]
  unfold Ir
  simp only [smul_eq_mul]
  ring

/-- `∫_0^z κ ((D+u)/Nq)^{-a} ≤ (D+z) κ ((D+z)/Nq)^{-a}/(1-a)` for `0 < a < 1`. -/
private lemma uu_int_wf {κ D Nq a z : ℝ} (hκ : 0 ≤ κ) (hD : 0 < D) (hNq : 0 < Nq) (ha0 : 0 < a)
    (ha1 : a < 1) (hz : 0 ≤ z) :
    ∫ u in (0 : ℝ)..z, κ * ((D + u) / Nq) ^ (-a)
      ≤ (D + z) * (κ * ((D + z) / Nq) ^ (-a)) / (1 - a) := by
  have hpt : ∀ u : ℝ, 0 ≤ u → κ * ((D + u) / Nq) ^ (-a) = (κ * Nq ^ a) * (D + u) ^ (-a) := by
    intro u hu
    rw [Real.div_rpow (by linarith) hNq.le, Real.rpow_neg hNq.le, div_inv_eq_mul]
    ring
  have h1 : ∫ u in (0 : ℝ)..z, κ * ((D + u) / Nq) ^ (-a)
      = (κ * Nq ^ a) * ∫ u in (0 : ℝ)..z, (D + u) ^ (-a) := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr (fun u hu => ?_)
    rw [Set.uIcc_of_le hz] at hu
    exact hpt u hu.1
  have h2 : ∫ u in (0 : ℝ)..z, (D + u) ^ (-a) = ∫ t in D..(D + z), t ^ (-a) := by
    have := intervalIntegral.integral_comp_add_left (a := (0 : ℝ)) (b := z) (fun t : ℝ => t ^ (-a)) D
    simpa using this
  have h3 := dil_J_lt D (D + z) a hD (by linarith) ha1
  have h4 : 0 ≤ κ * Nq ^ a := mul_nonneg hκ (Real.rpow_nonneg hNq.le _)
  have hDz : 0 < D + z := by linarith
  have h5 : (D + z) * (κ * ((D + z) / Nq) ^ (-a)) / (1 - a)
      = (κ * Nq ^ a) * ((D + z) ^ (1 - a) / (1 - a)) := by
    rw [Real.div_rpow hDz.le hNq.le, Real.rpow_neg hNq.le, div_inv_eq_mul,
      Real.rpow_sub hDz, Real.rpow_one, Real.rpow_neg hDz.le]
    field_simp
  rw [h1, h2, h5]
  exact mul_le_mul_of_nonneg_left h3 h4

private lemma uu_osc_congr {f f' g : ℝ → ℝ} {u : ℝ} (hu : 0 ≤ u)
    (h : ∀ v ∈ Icc (0 : ℝ) u, f v = f' v) :
    Muon.Foundations.oneSidedConv f g u = Muon.Foundations.oneSidedConv f' g u := by
  unfold Muon.Foundations.oneSidedConv
  refine intervalIntegral.integral_congr (fun s hs => ?_)
  rw [Set.uIcc_of_le hu] at hs
  rw [h (u - s) ⟨by linarith [hs.2], by linarith [hs.1]⟩]

/-- The envelope hypotheses of the two-phase lemma on `[0, τ N^q - D]`, for the templated kernels. -/
private lemma uu_env {p q : ℝ} (hp : 1 < p) (hq : 0 < q)
    {Kf Ks υ b D τ r0 L A ε : ℝ} (hKf : 0 ≤ Kf) (hKs : 0 < Ks) (hυ : 1 < υ) (hb0 : 0 < b)
    (hb1 : b < 1) (hD : 1 ≤ D) (hτ : 0 < τ) (hτ1 : τ ≤ 1) (hr0 : 0 < r0) (hr0υ : r0 ≤ υ)
    (hk1 : Kf * dilDelta r0 ^ (-υ) * D ^ (1 - υ) * dilB r0 υ ≤ 1 / 2)
    (hk2 : Kf * dilDelta (b / 2) ^ (-υ) * D ^ (1 - υ) * dilB (b / 2) υ ≤ 1 / 4)
    (hk3 : Ks * dilDelta (b / 2) ^ (-b) / (1 - b / 2) * τ ^ (1 - b) ≤ 1 / 4)
    (hL : 0 < L) (hA : A = Ks * dilDelta r0 ^ (-b) * Cpq p q * D * L) (hε : 0 < ε)
    {N : ℕ} (hN1 : 1 ≤ N) (hu0 : D < τ * (N : ℝ) ^ q)
    (hLI : ∀ z : ℝ, 0 ≤ z → z ≤ τ * (N : ℝ) ^ q / D - 1 → Ir r0 z ≤ L)
    {n' : ℕ} (w c : Fin n' → ℝ) (hw : ∀ l, 0 ≤ w l) (hw1 : ∑ l, w l = 1)
    (hc : ∀ l, 2 * (N : ℝ) ^ (-q) ≤ c l)
    (htemp : phaseTemplate (mixG w c) (N : ℝ) ((N : ℝ) ^ q - 1) q Kf Ks υ b) :
    (∀ u ∈ Icc (0 : ℝ) (τ * (N : ℝ) ^ q - D),
      Muon.Foundations.oneSidedConv (fun v => Cpq p q * (1 + v / D) ^ (-r0)) (mixG w c) u
        ≤ 2 * (Cpq p q * (1 + u / D) ^ (-r0)) +
          (ε ^ (1 / 4 : ℝ) * Real.sqrt A * ((N : ℝ) ^ q) ^ (-(1 / 2 : ℝ)) *
            ((D + u) / (N : ℝ) ^ q) ^ (-(b / 2))) ^ 2 / Real.sqrt ε) ∧
    (∀ u ∈ Icc (0 : ℝ) (τ * (N : ℝ) ^ q - D),
      Muon.Foundations.oneSidedConv
        (fun v => ε ^ (1 / 4 : ℝ) * Real.sqrt A * ((N : ℝ) ^ q) ^ (-(1 / 2 : ℝ)) *
          ((D + v) / (N : ℝ) ^ q) ^ (-(b / 2))) (mixG w c) u
        ≤ 2 * (ε ^ (1 / 4 : ℝ) * Real.sqrt A * ((N : ℝ) ^ q) ^ (-(1 / 2 : ℝ)) *
          ((D + u) / (N : ℝ) ^ q) ^ (-(b / 2)))) := by
  have hNr : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1
  have hNpos : (0 : ℝ) < (N : ℝ) := by linarith
  have hNq : 0 < (N : ℝ) ^ q := Real.rpow_pos_of_pos hNpos _
  have hDpos : 0 < D := by linarith
  have hC := pw_Cpq_pos hp hq
  have hbmin : 0 < 2 * (N : ℝ) ^ (-q) := by positivity
  have hgc : ContinuousOn (mixG w c) (Ici 0) := by
    have : Continuous (mixG w c) := by unfold mixG; fun_prop
    exact this.continuousOn
  obtain ⟨hgi, hgm⟩ := fz_g_int w c _ hbmin hw hw1 hc
  have hgnn : ∀ v ∈ Ici (0 : ℝ), 0 ≤ mixG w c v := fun v _ => fz_g_nonneg w c _ hw hc hbmin v
  have hδ0 := (dil_delta_facts r0 hr0).1
  have hδw := (dil_delta_facts (b / 2) (by linarith)).1
  have hA0 : 0 < A := by
    rw [hA]
    have := Real.rpow_pos_of_pos hδ0 (-b)
    positivity
  have hU0 : ∀ u : ℝ, u ≤ τ * (N : ℝ) ^ q - D → u ≤ (N : ℝ) ^ q - 1 := by
    intro u hu
    nlinarith
  have hsq : 0 < Real.sqrt ε := Real.sqrt_pos.2 hε
  refine ⟨fun u hu => ?_, fun u hu => ?_⟩
  · have hu0' : 0 ≤ u := hu.1
    have hs1 := (lem_app_phase_split hgc hgnn hgi hgm.le hKf hKs.le hυ hb0.le hb1 hNr hq hr0 hr0υ hD hC htemp).1
      u hu0' (hU0 u hu.2)
    refine hs1.trans ?_
    have hIr : Ir r0 (u / D) ≤ L := hLI _ (div_nonneg hu0' hDpos.le) (by
      have : u / D ≤ (τ * (N : ℝ) ^ q - D) / D := div_le_div_of_nonneg_right hu.2 hDpos.le
      rw [sub_div, div_self hDpos.ne'] at this
      exact this)
    have hcoef : (3 / 2 + Kf * dilDelta r0 ^ (-υ) * D ^ (1 - υ) * dilB r0 υ) *
        (Cpq p q * (1 + u / D) ^ (-r0)) ≤ 2 * (Cpq p q * (1 + u / D) ^ (-r0)) := by
      have : 0 ≤ Cpq p q * (1 + u / D) ^ (-r0) := by
        have : 0 < 1 + u / D := by have := div_nonneg hu0' hDpos.le; linarith
        positivity
      nlinarith
    have hrem : Ks * dilDelta r0 ^ (-b) * (N : ℝ) ^ (-q) * ((D + u) / (N : ℝ) ^ q) ^ (-b) *
        (Cpq p q * D * Ir r0 (u / D)) ≤
        (ε ^ (1 / 4 : ℝ) * Real.sqrt A * ((N : ℝ) ^ q) ^ (-(1 / 2 : ℝ)) *
          ((D + u) / (N : ℝ) ^ q) ^ (-(b / 2))) ^ 2 / Real.sqrt ε := by
      rw [uu_wf_sq hε hA0.le hDpos hNq hu0', hA, Real.rpow_neg hNpos.le]
      have hX : 0 ≤ ((D + u) / (N : ℝ) ^ q) ^ (-b) := Real.rpow_nonneg (by positivity) _
      have hK : 0 ≤ Ks * dilDelta r0 ^ (-b) * ((N : ℝ) ^ q)⁻¹ * ((D + u) / (N : ℝ) ^ q) ^ (-b) := by
        have := Real.rpow_nonneg hδ0.le (-b)
        positivity
      calc _ = Ks * dilDelta r0 ^ (-b) * ((N : ℝ) ^ q)⁻¹ * ((D + u) / (N : ℝ) ^ q) ^ (-b) *
            (Cpq p q * D * Ir r0 (u / D)) := by ring
        _ ≤ Ks * dilDelta r0 ^ (-b) * ((N : ℝ) ^ q)⁻¹ * ((D + u) / (N : ℝ) ^ q) ^ (-b) *
            (Cpq p q * D * L) := by
            apply mul_le_mul_of_nonneg_left _ hK
            exact mul_le_mul_of_nonneg_left hIr (by positivity)
        _ = _ := by ring
    linarith
  · have hu0' : 0 ≤ u := hu.1
    set cw : ℝ := ε ^ (1 / 4 : ℝ) * Real.sqrt A * ((N : ℝ) ^ q) ^ (-(1 / 2 : ℝ)) *
      (D / (N : ℝ) ^ q) ^ (-(b / 2)) with hcw_def
    have hcw : 0 < cw := by
      have h1 : 0 < ε ^ (1 / 4 : ℝ) := Real.rpow_pos_of_pos hε _
      have h2 : 0 < Real.sqrt A := Real.sqrt_pos.2 hA0
      have h3 : 0 < ((N : ℝ) ^ q) ^ (-(1 / 2 : ℝ)) := Real.rpow_pos_of_pos hNq _
      have h4 : 0 < (D / (N : ℝ) ^ q) ^ (-(b / 2)) := Real.rpow_pos_of_pos (div_pos hDpos hNq) _
      positivity
    have hcongr : Muon.Foundations.oneSidedConv
        (fun v => ε ^ (1 / 4 : ℝ) * Real.sqrt A * ((N : ℝ) ^ q) ^ (-(1 / 2 : ℝ)) *
          ((D + v) / (N : ℝ) ^ q) ^ (-(b / 2))) (mixG w c) u =
        Muon.Foundations.oneSidedConv (fun v => cw * (1 + v / D) ^ (-(b / 2))) (mixG w c) u := by
      refine uu_osc_congr hu0' (fun v hv => ?_)
      exact uu_wf_eq hε hDpos hNq hv.1
    rw [hcongr, uu_wf_eq hε hDpos hNq hu0']
    have hb2 : 0 < b / 2 := by linarith
    have hs := lem_app_phase_split hgc hgnn hgi hgm.le hKf hKs.le hυ hb0.le hb1 hNr hq hb2
      (by linarith) hD hcw htemp
    have hs1 := hs.1 u hu0' (hU0 u hu.2)
    have hs2 := hs.2 (by linarith) u hu0' (hU0 u hu.2)
    have hhw : 0 ≤ cw * (1 + u / D) ^ (-(b / 2)) := by
      have : 0 < 1 + u / D := by have := div_nonneg hu0' hDpos.le; linarith
      positivity
    have hfrac : (D + u) / (N : ℝ) ^ q ≤ τ := by
      rw [div_le_iff₀ hNq]; linarith [hu.2]
    have hpowle : ((D + u) / (N : ℝ) ^ q) ^ (1 - b) ≤ τ ^ (1 - b) :=
      Real.rpow_le_rpow (by positivity) hfrac (by linarith)
    have hKsd : 0 ≤ Ks * dilDelta (b / 2) ^ (-b) / (1 - b / 2) := by
      have := Real.rpow_nonneg hδw.le (-b)
      have h2 : 0 < 1 - b / 2 := by linarith
      positivity
    have hthird : Ks * dilDelta (b / 2) ^ (-b) / (1 - b / 2) * ((D + u) / (N : ℝ) ^ q) ^ (1 - b) ≤ 1 / 4 :=
      (mul_le_mul_of_nonneg_left hpowle hKsd).trans hk3
    nlinarith [mul_le_mul_of_nonneg_right hthird hhw]

private lemma uu_sqrt_sq_le {x y a b : ℝ} (hx : x ≤ a) (hy : y ≤ b) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (Real.sqrt x + Real.sqrt y) ^ 2 ≤ 2 * a + 2 * b := by
  have h1 := Real.sqrt_le_sqrt hx
  have h2 := Real.sqrt_le_sqrt hy
  have h3 : (Real.sqrt x + Real.sqrt y) ^ 2 ≤ (Real.sqrt a + Real.sqrt b) ^ 2 :=
    pow_le_pow_left₀ (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) (add_le_add h1 h2) 2
  nlinarith [sq_nonneg (Real.sqrt a - Real.sqrt b), Real.sq_sqrt ha, Real.sq_sqrt hb]

private lemma uu_xi {C D τ r0 Nq ε A b : ℝ} (hC : 0 < C) (hD : 0 < D) (hτ : 0 < τ) (hr0 : 1 ≤ r0)
    (hNq : 1 ≤ Nq) (hε : 0 < ε) :
    Nq * (C * (1 + (τ * Nq - D) / D) ^ (-r0) +
      ε ^ (1 / 4 : ℝ) * Real.sqrt A * Nq ^ (-(1 / 2 : ℝ)) * ((D + (τ * Nq - D)) / Nq) ^ (-(b / 2)))
      ≤ C * D ^ r0 * τ ^ (-r0) + Real.sqrt A * τ ^ (-(b / 2)) * (ε * Nq ^ 2) ^ (1 / 4 : ℝ) := by
  have hNq0 : 0 < Nq := by linarith
  have e1 : 1 + (τ * Nq - D) / D = (τ / D) * Nq := by field_simp; ring
  have e2 : (D + (τ * Nq - D)) / Nq = τ := by field_simp; ring
  rw [e1, e2, Real.mul_rpow (by positivity) hNq0.le, Real.div_rpow hτ.le hD.le, Real.rpow_neg hD.le]
  have h1 : Nq * Nq ^ (-r0) ≤ 1 := by
    have : Nq * Nq ^ (-r0) = Nq ^ (1 - r0) := by
      rw [show 1 - r0 = 1 + (-r0) by ring, Real.rpow_add hNq0, Real.rpow_one]
    rw [this]
    exact Real.rpow_le_one_of_one_le_of_nonpos hNq (by linarith)
  have h2 : (ε * Nq ^ 2) ^ (1 / 4 : ℝ) = ε ^ (1 / 4 : ℝ) * Nq ^ (1 / 2 : ℝ) := by
    rw [Real.mul_rpow hε.le (by positivity), ← Real.rpow_natCast Nq 2, ← Real.rpow_mul hNq0.le]
    norm_num
  have h3 : Nq * Nq ^ (-(1 / 2 : ℝ)) = Nq ^ (1 / 2 : ℝ) := by
    calc Nq * Nq ^ (-(1 / 2 : ℝ)) = Nq ^ (1 : ℝ) * Nq ^ (-(1 / 2 : ℝ)) := by rw [Real.rpow_one]
      _ = Nq ^ ((1 : ℝ) + -(1 / 2)) := (Real.rpow_add hNq0 _ _).symm
      _ = Nq ^ (1 / 2 : ℝ) := by norm_num
  have hDr : 0 < D ^ r0 := Real.rpow_pos_of_pos hD _
  have hτr : 0 < τ ^ (-r0) := Real.rpow_pos_of_pos hτ _
  have hNr : 0 < Nq ^ (-r0) := Real.rpow_pos_of_pos hNq0 _
  rw [h2, mul_add]
  have hA : Nq * (C * (τ ^ (-r0) / (D ^ r0)⁻¹ * Nq ^ (-r0))) ≤ C * D ^ r0 * τ ^ (-r0) := by
    have : Nq * (C * (τ ^ (-r0) / (D ^ r0)⁻¹ * Nq ^ (-r0))) = (C * D ^ r0 * τ ^ (-r0)) * (Nq * Nq ^ (-r0)) := by
      field_simp
    rw [this]
    exact mul_le_of_le_one_right (by positivity) h1
  have hB : Nq * (ε ^ (1 / 4 : ℝ) * Real.sqrt A * Nq ^ (-(1 / 2 : ℝ)) * τ ^ (-(b / 2)))
      = Real.sqrt A * τ ^ (-(b / 2)) * (ε ^ (1 / 4 : ℝ) * Nq ^ (1 / 2 : ℝ)) := by
    rw [← h3]; ring
  rw [hB]
  linarith

private lemma uu_core {p q T : ℝ} (hp : 1 < p) (hq : 0 < q) (hT : 4 ≤ T)
    {Kf Ks υ b D τ r0 L A ε : ℝ} (hKf : 0 ≤ Kf) (hKs : 0 < Ks) (hυ : 1 < υ) (hb0 : 0 < b)
    (hb1 : b < 1) (hD : 1 ≤ D) (hτ : 0 < τ) (hτ2 : τ ≤ 1 / 2) (hr0 : 1 ≤ r0) (hr0υ : r0 ≤ υ)
    (hr0r : r0 ≤ rq p q)
    (hk1 : Kf * dilDelta r0 ^ (-υ) * D ^ (1 - υ) * dilB r0 υ ≤ 1 / 2)
    (hk2 : Kf * dilDelta (b / 2) ^ (-υ) * D ^ (1 - υ) * dilB (b / 2) υ ≤ 1 / 4)
    (hk3 : Ks * dilDelta (b / 2) ^ (-b) / (1 - b / 2) * τ ^ (1 - b) ≤ 1 / 4)
    (hL : 0 < L) (hA : A = Ks * dilDelta r0 ^ (-b) * Cpq p q * D * L) (hε : 0 < ε)
    (hεT : ε < clockEps0 p q T)
    {N : ℕ} (hN4 : 4 ≤ N) (hu0 : D < τ * (N : ℝ) ^ q)
    (hLI : ∀ z : ℝ, 0 ≤ z → z ≤ τ * (N : ℝ) ^ q / D - 1 → Ir r0 z ≤ L)
    (w c : Fin N → ℝ) (hw : ∀ l, 0 ≤ w l) (hw1 : ∑ l, w l = 1)
    (hc : ∀ l, 2 * (N : ℝ) ^ (-q) ≤ c l)
    (htemp : phaseTemplate (mixG w c) (N : ℝ) ((N : ℝ) ^ q - 1) q Kf Ks υ b)
    (Y : ℝ → ℝ) (hYc : ContinuousOn Y (Ici 0)) (hYp : ∀ u ∈ Ici (0 : ℝ), 0 < Y u)
    (hY : ∀ u ∈ Ici (0 : ℝ), Y u = fNq (N : ℕ∞) p q u +
      Real.sqrt ε * Muon.Foundations.oneSidedConv (fun v => Real.sqrt (Y v)) (mixG w c) u) :
    dimClockI Y T ε ≤ Cpq p q * D * L + 2 * JN N p q + 3 * Real.sqrt (ε * ((N : ℝ) ^ q) ^ 2)
        + 8 * (Cpq p q * D ^ r0 * τ ^ (-r0) +
          Real.sqrt A * τ ^ (-(b / 2)) * (ε * ((N : ℝ) ^ q) ^ 2) ^ (1 / 4 : ℝ)) ∧
    ∀ H : ℝ, 0 ≤ H → H ≤ τ * (N : ℝ) ^ q - D →
      Cpq p q * (1 + H / D) ^ (-r0) + ε ^ (1 / 4 : ℝ) * Real.sqrt A * ((N : ℝ) ^ q) ^ (-(1 / 2 : ℝ)) *
        ((D + H) / (N : ℝ) ^ q) ^ (-(b / 2)) ≤ Real.sqrt ε →
      dimClockI Y T ε ≤ Cpq p q * D * Ir r0 (H / D) + 3 * (D + H) * Real.sqrt ε := by
  have hN1 : 1 ≤ N := by omega
  have hNr : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1
  have hNpos : (0 : ℝ) < (N : ℝ) := by linarith
  set Nq : ℝ := (N : ℝ) ^ q with hNq_def
  have hNq1 : 1 ≤ Nq := Real.one_le_rpow hNr hq.le
  have hNq : 0 < Nq := by linarith
  have hDpos : 0 < D := by linarith
  have hTpos : 0 < T := by linarith
  have hC := pw_Cpq_pos hp hq
  have hs : 0 < Real.sqrt ε := Real.sqrt_pos.2 hε
  obtain ⟨hε8, hεC⟩ := pw_eps_facts ε hεT
  have hδ0 := (dil_delta_facts r0 (by linarith)).1
  have hA0 : 0 < A := by
    rw [hA]
    have := Real.rpow_pos_of_pos hδ0 (-b)
    positivity
  -- mixture form of the forcing
  obtain ⟨aa, bb, hfa, haa, hF, hbb⟩ : ∃ aa bb : Fin N → ℝ,
      (∀ u, fNq (N : ℕ∞) p q u = mixF aa bb u) ∧ (∀ i, 0 ≤ aa i) ∧ 1 / 2 ≤ ∑ i, aa i ∧
      ∀ i, 2 * (N : ℝ) ^ (-q) ≤ bb i := by
    obtain ⟨h1, h2, h3⟩ := fz_ab N hN1 p q hq
    exact ⟨_, _, fz_fNq_eq N p q, h1, h2, h3⟩
  have hbmin : 0 < 2 * (N : ℝ) ^ (-q) := by positivity
  have hF0 : 0 < ∑ i, aa i := by linarith
  have hεF : ε < (∑ i, aa i) / T := by
    calc ε < 1 / (8 * T) := hε8
      _ ≤ (1 / 2) / T := by
        rw [div_le_div_iff₀ (by positivity) hTpos]; nlinarith
      _ ≤ (∑ i, aa i) / T := div_le_div_of_nonneg_right hF hTpos.le
  have hY' : ∀ u ∈ Ici (0 : ℝ), Y u = mixF aa bb u +
      Real.sqrt ε * Muon.Foundations.oneSidedConv (fun v => Real.sqrt (Y v)) (mixG w c) u := by
    intro u hu; rw [hY u hu, hfa]
  set u0 : ℝ := τ * Nq - D with hu0_def
  have hu0pos : 0 < u0 := by rw [hu0_def]; linarith
  obtain ⟨henv1, henv2⟩ := uu_env (p := p) (q := q) (Kf := Kf) (Ks := Ks) (υ := υ) (b := b) (D := D)
    (τ := τ) (r0 := r0) (L := L) (A := A) (ε := ε) hp hq hKf hKs hυ hb0 hb1 hD hτ (by linarith)
    (by linarith) hr0υ hk1 hk2 hk3 hL hA hε hN1 hu0 hLI w c hw hw1 hc htemp
  -- the envelopes
  set hfun : ℝ → ℝ := fun u => Cpq p q * (1 + u / D) ^ (-r0) with hfun_def
  set wfun : ℝ → ℝ := fun u => ε ^ (1 / 4 : ℝ) * Real.sqrt A * Nq ^ (-(1 / 2 : ℝ)) *
    ((D + u) / Nq) ^ (-(b / 2)) with hwfun_def
  have hpos1 : ∀ u ∈ Icc (0 : ℝ) u0, 0 < 1 + u / D := fun u hu => by
    have := div_nonneg hu.1 hDpos.le; linarith
  have hhc : ContinuousOn hfun (Icc 0 u0) := by
    rw [hfun_def]
    exact continuousOn_const.mul (ContinuousOn.rpow_const (by fun_prop)
      (fun u hu => Or.inl (hpos1 u hu).ne'))
  have hwc : ContinuousOn wfun (Icc 0 u0) := by
    rw [hwfun_def]
    refine continuousOn_const.mul (ContinuousOn.rpow_const (by fun_prop) (fun u hu => Or.inl ?_))
    have : 0 < D + u := by linarith [hu.1]
    exact (div_pos this hNq).ne'
  have hh0 : ∀ u ∈ Icc (0 : ℝ) u0, 0 ≤ hfun u := fun u hu => by
    rw [hfun_def]; have := hpos1 u hu; positivity
  have hw0 : ∀ u ∈ Icc (0 : ℝ) u0, 0 ≤ wfun u := fun u hu => by
    rw [hwfun_def]
    have : 0 < D + u := by linarith [hu.1]
    have h1 : 0 < ((D + u) / Nq) := div_pos this hNq
    have := Real.sqrt_nonneg A
    positivity
  have hfh : ∀ u ∈ Icc (0 : ℝ) u0, mixF aa bb u ≤ hfun u ^ 2 := by
    intro u hu
    rw [← hfa]
    refine (fz_fNq_le_h hp hq hD N hu.1).trans ?_
    have hb1' : 1 ≤ 1 + u / D := by have := div_nonneg hu.1 hDpos.le; linarith
    have h2 : (1 + u / D) ^ (-rq p q) ≤ (1 + u / D) ^ (-r0) :=
      Real.rpow_le_rpow_of_exponent_le hb1' (by linarith)
    have h3 : 0 ≤ (1 + u / D) ^ (-rq p q) := Real.rpow_nonneg (by linarith) _
    rw [hfun_def]
    exact pow_le_pow_left₀ (mul_nonneg hC.le h3) (mul_le_mul_of_nonneg_left h2 hC.le) 2
  have T1 := lem_app_phase_twophase_i aa bb w c _ hbmin haa hF0 hbb hw hw1 hc hT hε hεF hu0pos hYc hYp hY'
    hhc hh0 hwc hw0 hfh henv1 henv2
  have T2 := lem_app_phase_twophase_ii aa bb w c _ hbmin haa hF0 hbb hw hw1 hc hT hε hεF hu0pos hYc hYp hY'
    hhc hh0 hwc hw0 hfh henv1 henv2
  have T3 := lem_app_phase_twophase_iii aa bb w c _ hbmin haa hF0 hbb hw hw1 hc hT hε hεF hu0pos hYc hYp hY'
    hhc hh0 hwc hw0 hfh henv1 henv2
  -- integrals on `[0, t]`, `t ≤ u0`
  have hYs : ContinuousOn (fun v => Real.sqrt (Y v)) (Ici 0) := hYc.sqrt
  have hII_Y : ∀ t ∈ Icc (0 : ℝ) u0, IntervalIntegrable (fun v => Real.sqrt (Y v)) volume 0 t := by
    intro t ht
    exact ContinuousOn.intervalIntegrable_of_Icc ht.1
      (hYs.mono fun x hx => Set.mem_Ici.2 hx.1)
  have hII_h : ∀ t ∈ Icc (0 : ℝ) u0, IntervalIntegrable hfun volume 0 t := by
    intro t ht
    exact ContinuousOn.intervalIntegrable_of_Icc ht.1 (hhc.mono (Icc_subset_Icc le_rfl ht.2))
  have hII_w : ∀ t ∈ Icc (0 : ℝ) u0, IntervalIntegrable wfun volume 0 t := by
    intro t ht
    exact ContinuousOn.intervalIntegrable_of_Icc ht.1 (hwc.mono (Icc_subset_Icc le_rfl ht.2))
  have hbound : ∀ t ∈ Icc (0 : ℝ) u0, ∫ v in (0 : ℝ)..t, Real.sqrt (Y v) ≤
      Cpq p q * D * Ir r0 (t / D) + (D + t) * wfun t / (1 - b / 2) + Real.sqrt ε * t := by
    intro t ht
    have h1 : ∫ v in (0 : ℝ)..t, Real.sqrt (Y v) ≤
        ∫ v in (0 : ℝ)..t, (hfun v + wfun v + Real.sqrt ε) := by
      refine intervalIntegral.integral_mono_on ht.1 (hII_Y t ht)
        (((hII_h t ht).add (hII_w t ht)).add intervalIntegrable_const) (fun v hv => ?_)
      have hv' : v ∈ Icc (0 : ℝ) u0 := ⟨hv.1, hv.2.trans ht.2⟩
      have := (T1 v hv').1
      have hnn : 0 ≤ hfun v + wfun v + Real.sqrt ε := by
        linarith [hh0 v hv', hw0 v hv']
      calc Real.sqrt (Y v) ≤ Real.sqrt ((hfun v + wfun v + Real.sqrt ε) ^ 2) := Real.sqrt_le_sqrt this
        _ = _ := Real.sqrt_sq hnn
    have h2 : ∫ v in (0 : ℝ)..t, (hfun v + wfun v + Real.sqrt ε) =
        (∫ v in (0 : ℝ)..t, hfun v) + (∫ v in (0 : ℝ)..t, wfun v) + Real.sqrt ε * t := by
      rw [intervalIntegral.integral_add ((hII_h t ht).add (hII_w t ht)) intervalIntegrable_const,
        intervalIntegral.integral_add (hII_h t ht) (hII_w t ht)]
      simp
      ring
    have h3 : ∫ v in (0 : ℝ)..t, hfun v = Cpq p q * D * Ir r0 (t / D) := uu_int_h hDpos
    have h4 : ∫ v in (0 : ℝ)..t, wfun v ≤ (D + t) * wfun t / (1 - b / 2) := by
      have := uu_int_wf (κ := ε ^ (1 / 4 : ℝ) * Real.sqrt A * Nq ^ (-(1 / 2 : ℝ))) (D := D) (Nq := Nq)
        (a := b / 2) (z := t) (by positivity) hDpos hNq (by linarith) (by linarith) ht.1
      simpa [hwfun_def, mul_assoc] using this
    linarith
  refine ⟨?_, ?_⟩
  swap
  · -- the truncated bound
    intro H hH0 hHu hhw
    have hHm : H ∈ Icc (0 : ℝ) u0 := ⟨hH0, hHu⟩
    have hfhH := T2 H hHm hhw
    unfold dimClockI
    have hû0 : 0 ≤ (firstHit Y (T * ε)).toReal := ENNReal.toReal_nonneg
    have hûH : (firstHit Y (T * ε)).toReal ≤ H := by
      have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hfhH
      rwa [ENNReal.toReal_ofReal hH0] at this
    have hmono : ∫ v in (0 : ℝ)..(firstHit Y (T * ε)).toReal, Real.sqrt (Y v) ≤
        ∫ v in (0 : ℝ)..H, Real.sqrt (Y v) :=
      intervalIntegral.integral_mono_interval le_rfl hû0 hûH
        (Filter.Eventually.of_forall fun x => Real.sqrt_nonneg (Y x)) (hII_Y H hHm)
    refine hmono.trans ((hbound H hHm).trans ?_)
    have hwH0 := hw0 H hHm
    have hhH0 := hh0 H hHm
    have hwH : wfun H ≤ Real.sqrt ε := by
      have : hfun H + wfun H ≤ Real.sqrt ε := hhw
      linarith
    have hDH : 0 ≤ D + H := by linarith
    have h5 : (D + H) * wfun H / (1 - b / 2) ≤ 2 * ((D + H) * Real.sqrt ε) := by
      rw [div_le_iff₀ (by linarith only [hb1])]
      nlinarith only [mul_le_mul_of_nonneg_left hwH hDH, mul_nonneg hDH hs.le, hb1, hb0]
    nlinarith only [mul_nonneg hDH hs.le, h5, hH0, hs, hDpos]
  · -- the generic bound
    obtain ⟨-, -, û', hfirst', hû'pos, -⟩ := lem_app_phase_mixture aa bb w c _ hbmin haa hF0 hbb hw
      hw1 hc hT hε hεF rfl rfl hYc hYp hY'
    obtain ⟨û, hû, hI, hJ, hD'⟩ := T3
    have hû0 : 0 < û := by
      have hpos : 0 < ENNReal.ofReal û := by rw [← hû, hfirst']; exact ENNReal.ofReal_pos.2 hû'pos
      exact ENNReal.ofReal_pos.1 hpos
    have hdim : dimClockI Y T ε = ∫ u in (0 : ℝ)..û, Real.sqrt (Y u) := by
      unfold dimClockI; rw [hû, ENNReal.toReal_ofReal hû0.le]
    rw [hdim]
    have hu0m : u0 ∈ Icc (0 : ℝ) u0 := ⟨hu0pos.le, le_rfl⟩
    have hb2 : 2 / (2 * (N : ℝ) ^ (-q)) = Nq := by
      rw [Real.rpow_neg hNpos.le, hNq_def]; field_simp
    have hb4 : 4 / (2 * (N : ℝ) ^ (-q)) = 2 * Nq := by
      rw [Real.rpow_neg hNpos.le, hNq_def]; field_simp; ring
    -- pieces at `u0`
    set X : ℝ := hfun u0 + wfun u0 with hX_def
    have hX0 : 0 ≤ X := add_nonneg (hh0 u0 hu0m) (hw0 u0 hu0m)
    have hwX : wfun u0 ≤ X := by linarith [hh0 u0 hu0m]
    set sN : ℝ := Nq * Real.sqrt ε with hsN_def
    have hsN0 : 0 ≤ sN := by positivity
    -- the tail integral of the forcing
    have hJint := fz_mx_sqrt_integrable aa bb _ hbmin haa hbb
    have hJNeq : JN N p q = ∫ u in Ioi (0 : ℝ), Real.sqrt (mixF aa bb u) := by
      unfold JN; congr 1; funext u; rw [hfa]
    have hsplit := fz_split hJint hu0pos.le
    have hJt0 : 0 ≤ ∫ u in Ioi u0, Real.sqrt (mixF aa bb u) :=
      setIntegral_nonneg measurableSet_Ioi (fun _ _ => Real.sqrt_nonneg _)
    have hJn0 : 0 ≤ ∫ u in (0 : ℝ)..u0, Real.sqrt (mixF aa bb u) :=
      intervalIntegral.integral_nonneg hu0pos.le (fun _ _ => Real.sqrt_nonneg _)
    have hJtail : ∫ u in Ioi u0, Real.sqrt (mixF aa bb u) ≤ JN N p q := by
      rw [hJNeq, hsplit]; linarith
    have hJN0 : 0 ≤ JN N p q := by linarith
    have hJb : restartJ (mixF aa bb) (2 * (N : ℝ) ^ (-q)) ε
        (Muon.Foundations.oneSidedConv (fun v => Real.sqrt (Y v)) (mixG w c) u0) u0 ≤
        JN N p q + sN + Nq * X := by
      refine hJ.trans ?_
      rw [hb2]
      have : Nq * Real.sqrt ε * (1 + (hfun u0 + wfun u0) / Real.sqrt ε) = sN + Nq * X := by
        rw [hsN_def, hX_def]; field_simp
      linarith
    have hDb : restartD (2 * (N : ℝ) ^ (-q)) ε (Y u0) ≤ 2 * (Nq * X) := by
      refine hD'.trans ?_
      rw [hb4]
      have hlog : Real.log (1 + (hfun u0 + wfun u0) / Real.sqrt ε) ≤ (hfun u0 + wfun u0) / Real.sqrt ε := by
        have := Real.log_le_sub_one_of_pos (show 0 < 1 + (hfun u0 + wfun u0) / Real.sqrt ε by
          have := div_nonneg hX0 hs.le; linarith)
        linarith
      calc 2 * Nq * Real.sqrt ε * Real.log (1 + (hfun u0 + wfun u0) / Real.sqrt ε)
          ≤ 2 * Nq * Real.sqrt ε * ((hfun u0 + wfun u0) / Real.sqrt ε) :=
            mul_le_mul_of_nonneg_left hlog (by positivity)
        _ = 2 * (Nq * X) := by rw [hX_def]; field_simp
    have hJb0 : 0 ≤ JN N p q + sN + Nq * X := by
      have : 0 ≤ Nq * X := by positivity
      linarith
    have hsq : (Real.sqrt (restartJ (mixF aa bb) (2 * (N : ℝ) ^ (-q)) ε
          (Muon.Foundations.oneSidedConv (fun v => Real.sqrt (Y v)) (mixG w c) u0) u0)
        + Real.sqrt (restartD (2 * (N : ℝ) ^ (-q)) ε (Y u0))) ^ 2 ≤
        2 * (JN N p q + sN + Nq * X) + 2 * (2 * (Nq * X)) :=
      uu_sqrt_sq_le hJb hDb hJb0 (by positivity)
    -- the first phase
    have hfirst := hbound u0 hu0m
    have hIr0 : Ir r0 (u0 / D) ≤ L := hLI _ (div_nonneg hu0pos.le hDpos.le) (by
      rw [hu0_def, sub_div, div_self hDpos.ne'])
    have hDu0 : D + u0 = τ * Nq := by rw [hu0_def]; ring
    have hwtau : (D + u0) * wfun u0 / (1 - b / 2) ≤ Nq * X := by
      rw [hDu0, div_le_iff₀ (by linarith only [hb1])]
      have h1 : τ * Nq * wfun u0 ≤ Nq * X * (1 - b / 2) := by
        have : τ ≤ 1 - b / 2 := by linarith only [hτ2, hb1]
        have hp1 := mul_le_mul_of_nonneg_right this (mul_nonneg hNq.le (hw0 u0 hu0m))
        have hp2 := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hwX hNq.le)
          (show 0 ≤ 1 - b / 2 by linarith only [hb1])
        nlinarith only [hp1, hp2]
      exact h1
    have hsu0 : Real.sqrt ε * u0 ≤ τ * sN := by
      rw [hsN_def, hu0_def]
      nlinarith only [hs, hNq, hDpos]
    have hCL : Cpq p q * D * Ir r0 (u0 / D) ≤ Cpq p q * D * L :=
      mul_le_mul_of_nonneg_left hIr0 (by positivity)
    -- bound on `Nq * X`
    have hXi : Nq * X ≤ Cpq p q * D ^ r0 * τ ^ (-r0) +
        Real.sqrt A * τ ^ (-(b / 2)) * (ε * Nq ^ 2) ^ (1 / 4 : ℝ) := by
      exact uu_xi hC hDpos hτ hr0 hNq1 hε
    have hsNeq : sN = Real.sqrt (ε * Nq ^ 2) := by
      rw [hsN_def, Real.sqrt_mul hε.le, Real.sqrt_sq hNq.le]; ring
    rw [← hsNeq]
    have hXN0 : 0 ≤ Nq * X := mul_nonneg hNq.le hX0
    have htsN : τ * sN ≤ 1 / 2 * sN := mul_le_mul_of_nonneg_right hτ2 hsN0
    linarith only [hI, hsq, hfirst, hwtau, hsu0, hCL, hXi, hXN0, htsN, hsN0, hJN0]


private lemma uu_y4 {ε Nq : ℝ} (hε : 0 < ε) (hNq : 0 < Nq) :
    (ε * Nq ^ 2) ^ (1 / 4 : ℝ) = ε ^ (1 / 4 : ℝ) * Nq ^ (1 / 2 : ℝ) := by
  rw [Real.mul_rpow hε.le (by positivity), ← Real.rpow_natCast Nq 2, ← Real.rpow_mul hNq.le]
  norm_num

private lemma uu_eps4 {ε : ℝ} (hε : 0 < ε) :
    ε ^ (1 / 4 : ℝ) * ε ^ (1 / 4 : ℝ) = Real.sqrt ε := by
  rw [← Real.rpow_add hε, Real.sqrt_eq_rpow]; norm_num

/-- Choice of the truncation point `H` with `h(H) + w(H) ≤ √ε`. -/
private lemma uu_Hchoice {C D τ r0 b A ε Nq : ℝ} (hC : 0 < C) (hD : 0 < D) (hr0 : 1 ≤ r0)
    (hb0 : 0 < b) (hA : 0 < A) (hε : 0 < ε) (hNq : 1 ≤ Nq) (hs2C : Real.sqrt ε ≤ 2 * C) :
    0 ≤ max (D * (2 * C / Real.sqrt ε) ^ (1 / r0))
        (Nq * (2 * Real.sqrt A * (ε * Nq ^ 2) ^ (-(1 / 4 : ℝ))) ^ (2 / b)) - D ∧
    C * (1 + (max (D * (2 * C / Real.sqrt ε) ^ (1 / r0))
        (Nq * (2 * Real.sqrt A * (ε * Nq ^ 2) ^ (-(1 / 4 : ℝ))) ^ (2 / b)) - D) / D) ^ (-r0) +
      ε ^ (1 / 4 : ℝ) * Real.sqrt A * Nq ^ (-(1 / 2 : ℝ)) *
        ((D + (max (D * (2 * C / Real.sqrt ε) ^ (1 / r0))
        (Nq * (2 * Real.sqrt A * (ε * Nq ^ 2) ^ (-(1 / 4 : ℝ))) ^ (2 / b)) - D)) / Nq) ^ (-(b / 2))
      ≤ Real.sqrt ε := by
  have hNq0 : 0 < Nq := by linarith
  have hs : 0 < Real.sqrt ε := Real.sqrt_pos.2 hε
  have hr00 : 0 < r0 := by linarith
  set Eh : ℝ := D * (2 * C / Real.sqrt ε) ^ (1 / r0) with hEh
  set Ew : ℝ := Nq * (2 * Real.sqrt A * (ε * Nq ^ 2) ^ (-(1 / 4 : ℝ))) ^ (2 / b) with hEw
  have hy4 : (ε * Nq ^ 2) ^ (-(1 / 4 : ℝ)) = (ε ^ (1 / 4 : ℝ) * Nq ^ (1 / 2 : ℝ))⁻¹ := by
    rw [Real.rpow_neg (by positivity), uu_y4 hε hNq0]
  have hε4 : 0 < ε ^ (1 / 4 : ℝ) := Real.rpow_pos_of_pos hε _
  have hNh : 0 < Nq ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hNq0 _
  have hsA : 0 < Real.sqrt A := Real.sqrt_pos.2 hA
  have hbase : 0 < 2 * Real.sqrt A * (ε * Nq ^ 2) ^ (-(1 / 4 : ℝ)) := by
    have := Real.rpow_pos_of_pos (show 0 < ε * Nq ^ 2 by positivity) (-(1 / 4 : ℝ))
    positivity
  have hEh1 : D ≤ Eh := by
    have : 1 ≤ (2 * C / Real.sqrt ε) ^ (1 / r0) :=
      Real.one_le_rpow (by rw [le_div_iff₀ hs]; linarith) (by positivity)
    rw [hEh]; nlinarith
  have hEh0 : 0 < Eh := by linarith
  have hEw0 : 0 < Ew := by rw [hEw]; positivity
  set Z : ℝ := max Eh Ew with hZ
  have hZEh : Eh ≤ Z := le_max_left _ _
  have hZEw : Ew ≤ Z := le_max_right _ _
  have hZD : D ≤ Z := hEh1.trans hZEh
  refine ⟨by linarith, ?_⟩
  have hDZ : D + (Z - D) = Z := by ring
  have hZ0 : 0 < Z := by linarith
  rw [hDZ]
  have h1 : 1 + (Z - D) / D = Z / D := by field_simp; ring
  rw [h1]
  -- the `h` part
  have hhpart : C * (Z / D) ^ (-r0) ≤ Real.sqrt ε / 2 := by
    have hq : (2 * C / Real.sqrt ε) ^ (1 / r0) ≤ Z / D := by
      rw [le_div_iff₀ hD]; rw [hEh] at hZEh; linarith
    have hpos : 0 < (2 * C / Real.sqrt ε) ^ (1 / r0) := Real.rpow_pos_of_pos (by positivity) _
    have h2 := Real.rpow_le_rpow_of_nonpos hpos hq (show -r0 ≤ 0 by linarith)
    have h3 : ((2 * C / Real.sqrt ε) ^ (1 / r0)) ^ (-r0) = Real.sqrt ε / (2 * C) := by
      rw [← Real.rpow_mul (by positivity)]
      rw [show 1 / r0 * -r0 = -1 by field_simp, Real.rpow_neg_one, inv_div]
    rw [h3] at h2
    calc C * (Z / D) ^ (-r0) ≤ C * (Real.sqrt ε / (2 * C)) := mul_le_mul_of_nonneg_left h2 hC.le
      _ = Real.sqrt ε / 2 := by field_simp
  -- the `w` part
  have hwpart : ε ^ (1 / 4 : ℝ) * Real.sqrt A * Nq ^ (-(1 / 2 : ℝ)) * (Z / Nq) ^ (-(b / 2))
      ≤ Real.sqrt ε / 2 := by
    have hq : Ew / Nq ≤ Z / Nq := div_le_div_of_nonneg_right hZEw hNq0.le
    have hpos : 0 < Ew / Nq := div_pos hEw0 hNq0
    have h2 := Real.rpow_le_rpow_of_nonpos hpos hq (show -(b / 2) ≤ 0 by linarith)
    have h3 : (Ew / Nq) ^ (-(b / 2)) = (2 * Real.sqrt A * (ε * Nq ^ 2) ^ (-(1 / 4 : ℝ)))⁻¹ := by
      rw [hEw, mul_div_cancel_left₀ _ hNq0.ne', ← Real.rpow_mul hbase.le]
      rw [show 2 / b * -(b / 2) = -1 by field_simp, Real.rpow_neg_one]
    rw [h3] at h2
    have h4 : (2 * Real.sqrt A * (ε * Nq ^ 2) ^ (-(1 / 4 : ℝ)))⁻¹ =
        ε ^ (1 / 4 : ℝ) * Nq ^ (1 / 2 : ℝ) / (2 * Real.sqrt A) := by
      rw [hy4]; field_simp
    rw [h4] at h2
    have h5 : Nq ^ (-(1 / 2 : ℝ)) * Nq ^ (1 / 2 : ℝ) = 1 := by
      rw [← Real.rpow_add hNq0]; norm_num
    have hco : 0 ≤ ε ^ (1 / 4 : ℝ) * Real.sqrt A * Nq ^ (-(1 / 2 : ℝ)) := by positivity
    calc ε ^ (1 / 4 : ℝ) * Real.sqrt A * Nq ^ (-(1 / 2 : ℝ)) * (Z / Nq) ^ (-(b / 2))
        ≤ ε ^ (1 / 4 : ℝ) * Real.sqrt A * Nq ^ (-(1 / 2 : ℝ)) *
          (ε ^ (1 / 4 : ℝ) * Nq ^ (1 / 2 : ℝ) / (2 * Real.sqrt A)) := mul_le_mul_of_nonneg_left h2 hco
      _ = (ε ^ (1 / 4 : ℝ) * ε ^ (1 / 4 : ℝ)) * (Nq ^ (-(1 / 2 : ℝ)) * Nq ^ (1 / 2 : ℝ)) / 2 := by
          field_simp
      _ = Real.sqrt ε / 2 := by rw [h5, uu_eps4 hε]; ring
  linarith

private lemma uu_Dpow {M υ D : ℝ} (hυ : 1 < υ) (hM : 0 ≤ M) (hD : M ^ (1 / (υ - 1)) ≤ D) (hD1 : 1 ≤ D) :
    D ^ (1 - υ) * M ≤ 1 := by
  have hDpos : 0 < D := by linarith
  have hc : 0 < υ - 1 := by linarith
  have h1 : M ≤ D ^ (υ - 1) := by
    have := Real.rpow_le_rpow (Real.rpow_nonneg hM _) hD hc.le
    rwa [← Real.rpow_mul hM, one_div_mul_cancel hc.ne', Real.rpow_one] at this
  have h2 : D ^ (1 - υ) = (D ^ (υ - 1))⁻¹ := by
    rw [← Real.rpow_neg hDpos.le]; congr 1; ring
  rw [h2, ← div_eq_inv_mul, div_le_one (Real.rpow_pos_of_pos hDpos _)]
  exact h1

private lemma uu_consts {Kf Ks υ b r : ℝ} (hKf : 0 ≤ Kf) (hKs : 0 < Ks) (hυ : 1 < υ) (hb0 : 0 < b)
    (hb1 : b < 1) (hr : 1 ≤ r) :
    ∃ D τ r0 : ℝ, 1 ≤ D ∧ 0 < τ ∧ τ ≤ 1 / 2 ∧ 1 ≤ r0 ∧ r0 ≤ υ ∧ r0 ≤ r ∧ (r = 1 → r0 = 1) ∧
      (1 < r → 1 < r0) ∧
      Kf * dilDelta r0 ^ (-υ) * D ^ (1 - υ) * dilB r0 υ ≤ 1 / 2 ∧
      Kf * dilDelta (b / 2) ^ (-υ) * D ^ (1 - υ) * dilB (b / 2) υ ≤ 1 / 4 ∧
      Ks * dilDelta (b / 2) ^ (-b) / (1 - b / 2) * τ ^ (1 - b) ≤ 1 / 4 := by
  set r0 : ℝ := min r ((1 + υ) / 2) with hr0
  have hr01 : 1 ≤ r0 := le_min hr (by linarith)
  have hr0pos : 0 < r0 := by linarith
  have hδ0 := (dil_delta_facts r0 hr0pos).1
  have hδw := (dil_delta_facts (b / 2) (by linarith)).1
  have hB1 := dil_B_pos r0 υ hr0pos hυ
  have hB2 := dil_B_pos (b / 2) υ (by linarith) hυ
  set M1 : ℝ := 2 * Kf * dilDelta r0 ^ (-υ) * dilB r0 υ with hM1
  set M2 : ℝ := 4 * Kf * dilDelta (b / 2) ^ (-υ) * dilB (b / 2) υ with hM2
  have hM10 : 0 ≤ M1 := by
    have := Real.rpow_nonneg hδ0.le (-υ); rw [hM1]; positivity
  have hM20 : 0 ≤ M2 := by
    have := Real.rpow_nonneg hδw.le (-υ); rw [hM2]; positivity
  set D : ℝ := max 1 (max (M1 ^ (1 / (υ - 1))) (M2 ^ (1 / (υ - 1)))) with hD
  have hD1 : 1 ≤ D := le_max_left _ _
  have hDM1 : M1 ^ (1 / (υ - 1)) ≤ D := (le_max_left _ _).trans (le_max_right _ _)
  have hDM2 : M2 ^ (1 / (υ - 1)) ≤ D := (le_max_right _ _).trans (le_max_right _ _)
  have hQ : 0 < Ks * dilDelta (b / 2) ^ (-b) / (1 - b / 2) := by
    have := Real.rpow_pos_of_pos hδw (-b)
    have h2 : 0 < 1 - b / 2 := by linarith
    positivity
  set Q : ℝ := Ks * dilDelta (b / 2) ^ (-b) / (1 - b / 2) with hQdef
  set τ : ℝ := min (1 / 2) ((1 / (4 * Q)) ^ (1 / (1 - b))) with hτ
  have hτ0 : 0 < τ := lt_min (by norm_num) (Real.rpow_pos_of_pos (by positivity) _)
  refine ⟨D, τ, r0, hD1, hτ0, min_le_left _ _, hr01, ?_, min_le_left _ _, ?_, ?_, ?_, ?_, ?_⟩
  · exact (min_le_right _ _).trans (by linarith)
  · intro h; rw [hr0, h]; exact min_eq_left (by linarith)
  · intro h; rw [hr0]; exact lt_min h (by linarith)
  · have := uu_Dpow hυ hM10 hDM1 hD1
    have e : Kf * dilDelta r0 ^ (-υ) * D ^ (1 - υ) * dilB r0 υ = (1 / 2) * (D ^ (1 - υ) * M1) := by
      rw [hM1]; ring
    rw [e]; linarith
  · have := uu_Dpow hυ hM20 hDM2 hD1
    have e : Kf * dilDelta (b / 2) ^ (-υ) * D ^ (1 - υ) * dilB (b / 2) υ = (1 / 4) * (D ^ (1 - υ) * M2) := by
      rw [hM2]; ring
    rw [e]; linarith
  · have hτle : τ ^ (1 - b) ≤ 1 / (4 * Q) := by
      have h1 : τ ≤ (1 / (4 * Q)) ^ (1 / (1 - b)) := min_le_right _ _
      have := Real.rpow_le_rpow hτ0.le h1 (show 0 ≤ 1 - b by linarith)
      rwa [← Real.rpow_mul (by positivity), one_div_mul_cancel (by linarith : (1 - b) ≠ 0),
        Real.rpow_one] at this
    calc Q * τ ^ (1 - b) ≤ Q * (1 / (4 * Q)) := mul_le_mul_of_nonneg_left hτle hQ.le
      _ = 1 / 4 := by field_simp

private lemma uu_Ir_gt {r0 z : ℝ} (hr0 : 1 < r0) (hz : 0 ≤ z) : Ir r0 z ≤ 1 / (r0 - 1) := by
  unfold Ir
  have h2 : ∫ u in (0 : ℝ)..z, (1 + u) ^ (-r0) = ∫ t in (1 : ℝ)..(1 + z), t ^ (-r0) := by
    have := intervalIntegral.integral_comp_add_left (a := (0 : ℝ)) (b := z) (fun t : ℝ => t ^ (-r0)) 1
    simpa using this
  rw [h2]
  have := dil_J_gt 1 (1 + z) r0 one_pos (by linarith) hr0
  simpa using this

private lemma uu_Ew_le {A τ b y : ℝ} (hA : 0 < A) (hτ : 0 < τ) (hb : 0 < b)
    (hy : 16 * A ^ 2 * τ ^ (-(2 * b)) ≤ y) :
    (2 * Real.sqrt A * y ^ (-(1 / 4 : ℝ))) ^ (2 / b) ≤ τ := by
  have hy0 : 0 < y := lt_of_lt_of_le (by positivity) hy
  set z : ℝ := 2 * Real.sqrt A * y ^ (-(1 / 4 : ℝ)) with hz
  have hz0 : 0 ≤ z := by rw [hz]; positivity
  have hz4 : z ^ 4 = 16 * A ^ 2 * y⁻¹ := by
    have h1 : (y ^ (-(1 / 4 : ℝ))) ^ 4 = y⁻¹ := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hy0.le]
      rw [show (-(1 / 4 : ℝ)) * ((4 : ℕ) : ℝ) = -1 by push_cast; ring, Real.rpow_neg_one]
    have h2 : Real.sqrt A ^ 4 = A ^ 2 := by
      rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul, Real.sq_sqrt hA.le]
    rw [hz, mul_pow, mul_pow, h1, h2]; norm_num
  have hτb : 0 < τ ^ (b / 2) := Real.rpow_pos_of_pos hτ _
  have hτ4 : (τ ^ (b / 2)) ^ 4 = τ ^ (2 * b) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hτ.le]; congr 1; push_cast; ring
  have hle : z ^ 4 ≤ (τ ^ (b / 2)) ^ 4 := by
    rw [hz4, hτ4]
    have : 16 * A ^ 2 * y⁻¹ ≤ τ ^ (2 * b) := by
      rw [← div_eq_mul_inv, div_le_iff₀ hy0]
      have e : τ ^ (2 * b) * (16 * A ^ 2 * τ ^ (-(2 * b))) = 16 * A ^ 2 := by
        rw [mul_comm (16 * A ^ 2), ← mul_assoc, ← Real.rpow_add hτ]; simp
      have := mul_le_mul_of_nonneg_left hy (Real.rpow_nonneg hτ.le (2 * b))
      linarith
    exact this
  have hzτ : z ≤ τ ^ (b / 2) := le_of_pow_le_pow_left₀ (by norm_num) hτb.le hle
  have := Real.rpow_le_rpow hz0 hzτ (show 0 ≤ 2 / b by positivity)
  rwa [← Real.rpow_mul hτ.le, show b / 2 * (2 / b) = 1 by field_simp, Real.rpow_one] at this

private lemma uu_Eh_le {D C τ r0 ε Nq : ℝ} (hD : 0 < D) (hC : 0 < C) (hτ : 0 < τ) (hr0 : 1 ≤ r0)
    (hε : 0 < ε) (hNq : 1 ≤ Nq)
    (hy : (D * (2 * C) ^ (1 / r0) / τ) ^ (2 * r0) ≤ ε * Nq ^ 2) :
    D * (2 * C / Real.sqrt ε) ^ (1 / r0) ≤ τ * Nq := by
  have hNq0 : 0 < Nq := by linarith
  have hr00 : 0 < r0 := by linarith
  have hs : 0 < Real.sqrt ε := Real.sqrt_pos.2 hε
  set y : ℝ := ε * Nq ^ 2 with hydef
  have hy0 : 0 < y := by positivity
  set a : ℝ := y ^ (1 / (2 * r0)) with ha
  have ha0 : 0 < a := Real.rpow_pos_of_pos hy0 _
  have ha2 : a ^ (2 * r0) = y := by
    rw [ha, ← Real.rpow_mul hy0.le, one_div_mul_cancel (by positivity), Real.rpow_one]
  have hbase0 : 0 < D * (2 * C) ^ (1 / r0) / τ := by
    have := Real.rpow_pos_of_pos (show 0 < 2 * C by positivity) (1 / r0); positivity
  have h1 : D * (2 * C) ^ (1 / r0) / τ ≤ a := by
    rw [← ha2] at hy
    exact (Real.rpow_le_rpow_iff hbase0.le ha0.le (by positivity)).1 hy
  have hsy : Real.sqrt ε * Nq = Real.sqrt y := by
    rw [hydef, Real.sqrt_mul hε.le, Real.sqrt_sq hNq0.le]
  have hsa : (Real.sqrt y) ^ (1 / r0) = a := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hy0.le, ha]; congr 1; field_simp
  have e1 : 2 * C / Real.sqrt ε = (2 * C * Nq) / Real.sqrt y := by
    rw [← hsy]; field_simp
  rw [e1, Real.div_rpow (by positivity) (Real.sqrt_nonneg _), hsa,
    Real.mul_rpow (by positivity) hNq0.le]
  have hN1 : Nq ^ (1 / r0) ≤ Nq := by
    have := Real.rpow_le_rpow_of_exponent_le hNq (show 1 / r0 ≤ 1 by
      rw [div_le_one hr00]; exact hr0)
    rwa [Real.rpow_one] at this
  have hX0 : 0 < (2 * C) ^ (1 / r0) := Real.rpow_pos_of_pos (by positivity) _
  rw [div_le_iff₀ hτ] at h1
  calc D * ((2 * C) ^ (1 / r0) * Nq ^ (1 / r0) / a)
      ≤ D * ((2 * C) ^ (1 / r0) * Nq / a) := by
        apply mul_le_mul_of_nonneg_left _ hD.le
        apply div_le_div_of_nonneg_right _ ha0.le
        exact mul_le_mul_of_nonneg_left hN1 hX0.le
    _ = (D * (2 * C) ^ (1 / r0) / a) * Nq := by ring
    _ ≤ τ * Nq := by
        apply mul_le_mul_of_nonneg_right _ hNq0.le
        rw [div_le_iff₀ ha0]; linarith

private lemma uu_sEh {D C r0 ε : ℝ} (hD : 0 < D) (hC : 0 < C) (hr0 : 1 ≤ r0) (hε : 0 < ε)
    (hs1 : Real.sqrt ε ≤ 1) :
    Real.sqrt ε * (D * (2 * C / Real.sqrt ε) ^ (1 / r0)) ≤ D * (2 * C) ^ (1 / r0) := by
  have hs : 0 < Real.sqrt ε := Real.sqrt_pos.2 hε
  have hr00 : 0 < r0 := by linarith
  have h1 : Real.sqrt ε ≤ Real.sqrt ε ^ (1 / r0) := by
    have := Real.rpow_le_rpow_of_exponent_ge hs hs1 (show 1 / r0 ≤ 1 by
      rw [div_le_one hr00]; exact hr0)
    rwa [Real.rpow_one] at this
  have hp : 0 < Real.sqrt ε ^ (1 / r0) := Real.rpow_pos_of_pos hs _
  have hX : 0 < (2 * C) ^ (1 / r0) := Real.rpow_pos_of_pos (by positivity) _
  rw [Real.div_rpow (by positivity) hs.le]
  calc Real.sqrt ε * (D * ((2 * C) ^ (1 / r0) / Real.sqrt ε ^ (1 / r0)))
      = (D * (2 * C) ^ (1 / r0)) * (Real.sqrt ε / Real.sqrt ε ^ (1 / r0)) := by field_simp
    _ ≤ (D * (2 * C) ^ (1 / r0)) * 1 := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        rw [div_le_one hp]; exact h1
    _ = _ := mul_one _

private lemma uu_sEw {A b ε Nq : ℝ} (hA : 0 < A) (hb0 : 0 < b) (hb1 : b < 1) (hε : 0 < ε)
    (hNq : 1 ≤ Nq) (hy1 : 1 ≤ ε * Nq ^ 2) :
    Real.sqrt ε * (Nq * (2 * Real.sqrt A * (ε * Nq ^ 2) ^ (-(1 / 4 : ℝ))) ^ (2 / b))
      ≤ (2 * Real.sqrt A) ^ (2 / b) := by
  have hNq0 : 0 < Nq := by linarith
  set y : ℝ := ε * Nq ^ 2 with hydef
  have hy0 : 0 < y := by linarith
  have hsA : 0 < Real.sqrt A := Real.sqrt_pos.2 hA
  have hsy : Real.sqrt ε * Nq = Real.sqrt y := by
    rw [hydef, Real.sqrt_mul hε.le, Real.sqrt_sq hNq0.le]
  have h1 : (2 * Real.sqrt A * y ^ (-(1 / 4 : ℝ))) ^ (2 / b) =
      (2 * Real.sqrt A) ^ (2 / b) * y ^ (-(1 / (2 * b))) := by
    rw [Real.mul_rpow (by positivity) (Real.rpow_nonneg hy0.le _), ← Real.rpow_mul hy0.le]
    congr 2; field_simp; ring
  have h2 : Real.sqrt y * y ^ (-(1 / (2 * b))) ≤ 1 := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hy0]
    apply Real.rpow_le_one_of_one_le_of_nonpos hy1
    have : 1 / 2 ≤ 1 / (2 * b) := by
      rw [div_le_div_iff₀ (by norm_num) (by positivity)]; nlinarith
    linarith
  calc Real.sqrt ε * (Nq * (2 * Real.sqrt A * y ^ (-(1 / 4 : ℝ))) ^ (2 / b))
      = (Real.sqrt ε * Nq) * (2 * Real.sqrt A * y ^ (-(1 / 4 : ℝ))) ^ (2 / b) := by ring
    _ = (2 * Real.sqrt A) ^ (2 / b) * (Real.sqrt y * y ^ (-(1 / (2 * b)))) := by
        rw [hsy, h1]; ring
    _ ≤ (2 * Real.sqrt A) ^ (2 / b) * 1 := by
        apply mul_le_mul_of_nonneg_left h2
        exact Real.rpow_nonneg (by positivity) _
    _ = _ := mul_one _

/-- The templated regime `r > 1`: the clock integral is bounded. -/
private lemma uu_gt1 {p q T Kf Ks υ b : ℝ} (hp : 1 < p) (hq : 0 < q) (hT : 4 ≤ T)
    (hr : 1 < rq p q) (hKf : 0 ≤ Kf) (hKs : 0 < Ks) (hυ : 1 < υ) (hb0 : 0 < b) (hb1 : b < 1) :
    ∃ (N1 : ℕ) (K : ℝ), ∀ (N : ℕ) (ε : ℝ) (w c : Fin N → ℝ) (Y : ℝ → ℝ),
      N1 ≤ N → 0 < ε → ε < clockEps0 p q T → (∀ l, 0 ≤ w l) → ∑ l, w l = 1 →
      (∀ l, 2 * (N : ℝ) ^ (-q) ≤ c l) →
      phaseTemplate (mixG w c) (N : ℝ) ((N : ℝ) ^ q - 1) q Kf Ks υ b →
      ContinuousOn Y (Ici 0) → (∀ u ∈ Ici (0 : ℝ), 0 < Y u) →
      (∀ u ∈ Ici (0 : ℝ), Y u = fNq (N : ℕ∞) p q u +
        Real.sqrt ε * Muon.Foundations.oneSidedConv (fun v => Real.sqrt (Y v)) (mixG w c) u) →
      dimClockI Y T ε ≤ K := by
  obtain ⟨D, τ, r0, hD, hτ, hτ2, hr01, hr0υ, hr0r, -, hr0gt', hk1, hk2, hk3⟩ :=
    uu_consts hKf hKs hυ hb0 hb1 hr.le
  have hr0gt : 1 < r0 := hr0gt' hr
  have hDpos : 0 < D := by linarith
  have hC := pw_Cpq_pos hp hq
  set C : ℝ := Cpq p q with hC_def
  set L : ℝ := 1 / (r0 - 1) with hL_def
  have hL : 0 < L := by rw [hL_def]; exact one_div_pos.2 (by linarith)
  have hδ0 := (dil_delta_facts r0 (by linarith)).1
  set A : ℝ := Ks * dilDelta r0 ^ (-b) * C * D * L with hA_def
  have hA0 : 0 < A := by
    have := Real.rpow_pos_of_pos hδ0 (-b)
    rw [hA_def]; positivity
  set Ystar : ℝ := max 1 (max ((D * (2 * C) ^ (1 / r0) / τ) ^ (2 * r0))
    (16 * A ^ 2 * τ ^ (-(2 * b)))) with hYstar
  have hY1 : 1 ≤ Ystar := le_max_left _ _
  have hYh : (D * (2 * C) ^ (1 / r0) / τ) ^ (2 * r0) ≤ Ystar := (le_max_left _ _).trans (le_max_right _ _)
  have hYw : 16 * A ^ 2 * τ ^ (-(2 * b)) ≤ Ystar := (le_max_right _ _).trans (le_max_right _ _)
  have hNt : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hDt : ∀ᶠ n : ℕ in atTop, D < τ * (n : ℝ) ^ q := by
    have ht := (tendsto_rpow_atTop hq).comp hNt
    filter_upwards [ht.eventually_gt_atTop (D / τ)] with n hn
    rw [div_lt_iff₀ hτ] at hn
    change D < (n : ℝ) ^ q * τ at hn
    linarith
  obtain ⟨ND, hND⟩ := eventually_atTop.1 hDt
  refine ⟨max 4 ND, max (C * D * L + 2 * Jpq p q + 3 * Real.sqrt Ystar +
      8 * (C * D ^ r0 * τ ^ (-r0) + Real.sqrt A * τ ^ (-(b / 2)) * Ystar ^ (1 / 4 : ℝ)))
    (C * D * L + 3 * (D * (2 * C) ^ (1 / r0) + (2 * Real.sqrt A) ^ (2 / b))), ?_⟩
  intro N ε w c Y hN hε hε0 hw hw1 hc htemp hYc hYp hY
  have hN4 : 4 ≤ N := (le_max_left _ _).trans hN
  have hN1 : 1 ≤ N := by omega
  have hNr : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1
  have hNpos : (0 : ℝ) < (N : ℝ) := by linarith
  have hNq1 : 1 ≤ (N : ℝ) ^ q := Real.one_le_rpow hNr hq.le
  have hu0 : D < τ * (N : ℝ) ^ q := hND N ((le_max_right _ _).trans hN)
  have hLI : ∀ z : ℝ, 0 ≤ z → z ≤ τ * (N : ℝ) ^ q / D - 1 → Ir r0 z ≤ L :=
    fun z hz _ => uu_Ir_gt hr0gt hz
  have core := uu_core hp hq hT hKf hKs hυ hb0 hb1 hD hτ hτ2 hr01 hr0υ hr0r hk1 hk2 hk3 hL hA_def
    hε hε0 hN4 hu0 hLI w c hw hw1 hc htemp Y hYc hYp hY
  have hJ : JN N p q ≤ Jpq p q := by
    have := (lem_app_phase_clock_integral_rate hp hq hr N hN4).1
    linarith
  by_cases hy : ε * ((N : ℝ) ^ q) ^ 2 < Ystar
  · refine core.1.trans (le_trans ?_ (le_max_left _ _))
    have h2 : Real.sqrt (ε * ((N : ℝ) ^ q) ^ 2) ≤ Real.sqrt Ystar := Real.sqrt_le_sqrt hy.le
    have h3 : (ε * ((N : ℝ) ^ q) ^ 2) ^ (1 / 4 : ℝ) ≤ Ystar ^ (1 / 4 : ℝ) :=
      Real.rpow_le_rpow (by positivity) hy.le (by norm_num)
    have h4 : Real.sqrt A * τ ^ (-(b / 2)) * (ε * ((N : ℝ) ^ q) ^ 2) ^ (1 / 4 : ℝ) ≤
        Real.sqrt A * τ ^ (-(b / 2)) * Ystar ^ (1 / 4 : ℝ) :=
      mul_le_mul_of_nonneg_left h3 (by positivity)
    linarith only [core.1, h2, h4, hJ]
  · push_neg at hy
    refine le_trans ?_ (le_max_right _ _)
    obtain ⟨hε8, hεC⟩ := pw_eps_facts ε hε0
    have hs : 0 < Real.sqrt ε := Real.sqrt_pos.2 hε
    have hεq : ε < 1 / 4 := pw_eps_lt_quarter hε0
    have hs1 : Real.sqrt ε ≤ 1 := by
      rw [Real.sqrt_le_one]; linarith
    have hs2C : Real.sqrt ε ≤ 2 * C := by
      have : Real.sqrt ε ≤ Real.sqrt (C ^ 2) := Real.sqrt_le_sqrt hεC.le
      rw [Real.sqrt_sq hC.le] at this; linarith
    obtain ⟨hH0, hHw⟩ := uu_Hchoice (C := C) (D := D) (τ := τ) (r0 := r0) (b := b) (A := A)
      (ε := ε) (Nq := (N : ℝ) ^ q) hC hDpos hr01 hb0 hA0 hε hNq1 hs2C
    set Eh : ℝ := D * (2 * C / Real.sqrt ε) ^ (1 / r0) with hEh
    set Ew : ℝ := (N : ℝ) ^ q * (2 * Real.sqrt A * (ε * ((N : ℝ) ^ q) ^ 2) ^ (-(1 / 4 : ℝ))) ^ (2 / b)
      with hEw
    have hEh0 : 0 ≤ Eh := by
      have := Real.rpow_nonneg (show 0 ≤ 2 * C / Real.sqrt ε by positivity) (1 / r0); rw [hEh]; positivity
    have hEw0 : 0 ≤ Ew := by
      have := Real.rpow_nonneg (show 0 ≤ 2 * Real.sqrt A * (ε * ((N : ℝ) ^ q) ^ 2) ^ (-(1 / 4 : ℝ)) by
        have := Real.rpow_nonneg (show 0 ≤ ε * ((N : ℝ) ^ q) ^ 2 by positivity) (-(1 / 4 : ℝ)); positivity) (2 / b)
      rw [hEw]; positivity
    have hEhτ : Eh ≤ τ * (N : ℝ) ^ q :=
      uu_Eh_le hDpos hC hτ hr01 hε hNq1 (hYh.trans hy)
    have hEwτ : Ew ≤ τ * (N : ℝ) ^ q := by
      have := uu_Ew_le hA0 hτ hb0 (hYw.trans hy)
      rw [hEw]
      calc (N : ℝ) ^ q * (2 * Real.sqrt A * (ε * ((N : ℝ) ^ q) ^ 2) ^ (-(1 / 4 : ℝ))) ^ (2 / b)
          ≤ (N : ℝ) ^ q * τ := mul_le_mul_of_nonneg_left this (by linarith only [hNq1])
        _ = τ * (N : ℝ) ^ q := mul_comm _ _
    set Z : ℝ := max Eh Ew with hZ
    have hZτ : Z ≤ τ * (N : ℝ) ^ q := max_le hEhτ hEwτ
    have hHu : Z - D ≤ τ * (N : ℝ) ^ q - D := by linarith only [hZτ]
    have hX := core.2 (Z - D) hH0 hHu hHw
    have hIr : Ir r0 ((Z - D) / D) ≤ L := uu_Ir_gt hr0gt (div_nonneg hH0 hDpos.le)
    have hsEh := uu_sEh hDpos hC hr01 hε hs1
    have hsEw := uu_sEw hA0 hb0 hb1 hε hNq1 (le_trans hY1 hy)
    have hZsum : Z ≤ Eh + Ew := max_le (by linarith only [hEw0]) (by linarith only [hEh0])
    have hDH : D + (Z - D) = Z := by ring
    rw [hDH] at hX
    have hsZ : Real.sqrt ε * Z ≤ D * (2 * C) ^ (1 / r0) + (2 * Real.sqrt A) ^ (2 / b) := by
      have := mul_le_mul_of_nonneg_left hZsum hs.le
      linarith only [this, hsEh, hsEw, mul_add (Real.sqrt ε) Eh Ew]
    have hCDI : C * D * Ir r0 ((Z - D) / D) ≤ C * D * L :=
      mul_le_mul_of_nonneg_left hIr (by positivity)
    linarith only [hX, hCDI, hsZ]

private lemma uu_sEw_exact {A b ε Nq : ℝ} (hA : 0 < A) (hb0 : 0 < b) (hε : 0 < ε) (hNq : 1 ≤ Nq) :
    Real.sqrt ε * (Nq * (2 * Real.sqrt A * (ε * Nq ^ 2) ^ (-(1 / 4 : ℝ))) ^ (2 / b))
      = (2 * Real.sqrt A) ^ (2 / b) * (ε * Nq ^ 2) ^ (-((1 - b) / (2 * b))) := by
  have hNq0 : 0 < Nq := by linarith
  set y : ℝ := ε * Nq ^ 2 with hydef
  have hy0 : 0 < y := by positivity
  have hsA : 0 < Real.sqrt A := Real.sqrt_pos.2 hA
  have hsy : Real.sqrt ε * Nq = Real.sqrt y := by
    rw [hydef, Real.sqrt_mul hε.le, Real.sqrt_sq hNq0.le]
  have h1 : (2 * Real.sqrt A * y ^ (-(1 / 4 : ℝ))) ^ (2 / b) =
      (2 * Real.sqrt A) ^ (2 / b) * y ^ (-(1 / (2 * b))) := by
    rw [Real.mul_rpow (by positivity) (Real.rpow_nonneg hy0.le _), ← Real.rpow_mul hy0.le]
    congr 2; field_simp; ring
  have h2 : Real.sqrt y * y ^ (-(1 / (2 * b))) = y ^ (-((1 - b) / (2 * b))) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hy0]
    congr 1; field_simp; ring
  calc Real.sqrt ε * (Nq * (2 * Real.sqrt A * y ^ (-(1 / 4 : ℝ))) ^ (2 / b))
      = (Real.sqrt ε * Nq) * (2 * Real.sqrt A * y ^ (-(1 / 4 : ℝ))) ^ (2 / b) := by ring
    _ = (2 * Real.sqrt A) ^ (2 / b) * (Real.sqrt y * y ^ (-(1 / (2 * b)))) := by
        rw [hsy, h1]; ring
    _ = _ := by rw [h2]

private lemma uu_sEw2 {A τ b ε Nq : ℝ} (hA : 0 < A) (hτ : 0 < τ) (hb0 : 0 < b) (hb1 : b < 1)
    (hε : 0 < ε) (hNq : 1 ≤ Nq) (hy : 16 * A ^ 2 * τ ^ (-(2 * b)) ≤ ε * Nq ^ 2) :
    Real.sqrt ε * (Nq * (2 * Real.sqrt A * (ε * Nq ^ 2) ^ (-(1 / 4 : ℝ))) ^ (2 / b))
      ≤ 4 * A * τ ^ (1 - b) := by
  rw [uu_sEw_exact hA hb0 hε hNq]
  set y : ℝ := ε * Nq ^ 2 with hydef
  have hy0 : 0 < y := lt_of_lt_of_le (by positivity) hy
  set m : ℝ := 4 * A * τ ^ (-b) with hm
  have hm0 : 0 < m := by rw [hm]; positivity
  have hmy : m ^ 2 ≤ y := by
    have hτ2 : (τ ^ (-b)) ^ 2 = τ ^ (-(2 * b)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hτ.le]; push_cast; ring_nf
    have : m ^ 2 = 16 * A ^ 2 * τ ^ (-(2 * b)) := by
      rw [hm, mul_pow, mul_pow, hτ2]; ring
    rw [this]; exact hy
  have h1 : (2 * Real.sqrt A) ^ (2 / b) = m ^ (1 / b) * τ := by
    have : (2 * Real.sqrt A) ^ (2 / b) = (4 * A) ^ (1 / b) := by
      have h4 : (2 * Real.sqrt A) ^ 2 = 4 * A := by
        rw [mul_pow, Real.sq_sqrt hA.le]; norm_num
      rw [← h4, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
      congr 1; push_cast; ring
    rw [this]
    have : 4 * A = m * τ ^ b := by
      rw [hm, mul_assoc, ← Real.rpow_add hτ]; simp
    rw [this, Real.mul_rpow hm0.le (Real.rpow_nonneg hτ.le _), ← Real.rpow_mul hτ.le]
    rw [mul_one_div_cancel hb0.ne', Real.rpow_one]
  have h2 : y ^ (-((1 - b) / (2 * b))) ≤ m ^ (-((1 - b) / b)) := by
    have := Real.rpow_le_rpow_of_nonpos (by positivity : 0 < m ^ 2) hmy
      (show -((1 - b) / (2 * b)) ≤ 0 by
        have : 0 ≤ (1 - b) / (2 * b) := by apply div_nonneg <;> linarith
        linarith)
    rw [← Real.rpow_natCast, ← Real.rpow_mul hm0.le] at this
    refine this.trans (le_of_eq ?_)
    congr 1; push_cast; field_simp
  have hmb : 0 < m ^ (1 / b) := Real.rpow_pos_of_pos hm0 _
  calc (2 * Real.sqrt A) ^ (2 / b) * y ^ (-((1 - b) / (2 * b)))
      = (m ^ (1 / b) * τ) * y ^ (-((1 - b) / (2 * b))) := by rw [h1]
    _ ≤ (m ^ (1 / b) * τ) * m ^ (-((1 - b) / b)) :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = τ * m := by
        rw [mul_comm (m ^ (1 / b)) τ, mul_assoc, ← Real.rpow_add hm0]
        have : 1 / b + -((1 - b) / b) = 1 := by field_simp; ring
        rw [this, Real.rpow_one]
    _ = 4 * A * τ ^ (1 - b) := by
        rw [hm, show (1 - b) = 1 + (-b) by ring, Real.rpow_add hτ, Real.rpow_one]; ring

private lemma uu_sEw3 {A b ε Nq : ℝ} (hA : 0 < A) (hb0 : 0 < b) (hb1 : b < 1)
    (hε : 0 < ε) (hNq : 1 ≤ Nq) (hA4 : 4 * A ≤ Nq ^ ((1 - b) / 2))
    (hy : Nq ≤ ε * Nq ^ 2) :
    Real.sqrt ε * (Nq * (2 * Real.sqrt A * (ε * Nq ^ 2) ^ (-(1 / 4 : ℝ))) ^ (2 / b)) ≤ 1 := by
  rw [uu_sEw_exact hA hb0 hε hNq]
  have hNq0 : 0 < Nq := by linarith
  set y : ℝ := ε * Nq ^ 2 with hydef
  have hy0 : 0 < y := lt_of_lt_of_le hNq0 hy
  have h4 : (2 * Real.sqrt A) ^ (2 / b) = (4 * A) ^ (1 / b) := by
    have h4 : (2 * Real.sqrt A) ^ 2 = 4 * A := by
      rw [mul_pow, Real.sq_sqrt hA.le]; norm_num
    rw [← h4, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
    congr 1; push_cast; ring
  have h5 : (4 * A) ^ (1 / b) ≤ Nq ^ ((1 - b) / (2 * b)) := by
    have := Real.rpow_le_rpow (by positivity) hA4 (show 0 ≤ 1 / b by positivity)
    rw [← Real.rpow_mul hNq0.le] at this
    refine this.trans (le_of_eq ?_)
    congr 1; field_simp
  have h6 : y ^ (-((1 - b) / (2 * b))) ≤ Nq ^ (-((1 - b) / (2 * b))) :=
    Real.rpow_le_rpow_of_nonpos hNq0 hy
      (by have : 0 ≤ (1 - b) / (2 * b) := by apply div_nonneg <;> linarith
          linarith)
  rw [h4]
  calc (4 * A) ^ (1 / b) * y ^ (-((1 - b) / (2 * b)))
      ≤ Nq ^ ((1 - b) / (2 * b)) * Nq ^ (-((1 - b) / (2 * b))) :=
        mul_le_mul h5 h6 (Real.rpow_nonneg hy0.le _) (Real.rpow_nonneg hNq0.le _)
    _ = 1 := by rw [← Real.rpow_add hNq0]; simp

private lemma uu_Ew_eps {A b ε Nq : ℝ} (hA : 0 < A) (hb0 : 0 < b) (hb1 : b < 1)
    (hε : 0 < ε) (hNq : 1 ≤ Nq) (hA4 : 4 * A ≤ Nq ^ (1 - b)) :
    Nq * (2 * Real.sqrt A * (ε * Nq ^ 2) ^ (-(1 / 4 : ℝ))) ^ (2 / b) ≤ ε ^ (-(1 / (2 * b))) := by
  have hNq0 : 0 < Nq := by linarith
  set y : ℝ := ε * Nq ^ 2 with hydef
  have hy0 : 0 < y := by positivity
  have hsA : 0 < Real.sqrt A := Real.sqrt_pos.2 hA
  have h1 : (2 * Real.sqrt A * y ^ (-(1 / 4 : ℝ))) ^ (2 / b) =
      (2 * Real.sqrt A) ^ (2 / b) * y ^ (-(1 / (2 * b))) := by
    rw [Real.mul_rpow (by positivity) (Real.rpow_nonneg hy0.le _), ← Real.rpow_mul hy0.le]
    congr 2; field_simp; ring
  have h4 : (2 * Real.sqrt A) ^ (2 / b) = (4 * A) ^ (1 / b) := by
    have h4 : (2 * Real.sqrt A) ^ 2 = 4 * A := by
      rw [mul_pow, Real.sq_sqrt hA.le]; norm_num
    rw [← h4, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
    congr 1; push_cast; ring
  have h5 : (4 * A) ^ (1 / b) ≤ Nq ^ ((1 - b) / b) := by
    have := Real.rpow_le_rpow (by positivity) hA4 (show 0 ≤ 1 / b by positivity)
    rw [← Real.rpow_mul hNq0.le] at this
    refine this.trans (le_of_eq ?_)
    congr 1; field_simp
  have h6 : y ^ (-(1 / (2 * b))) = ε ^ (-(1 / (2 * b))) * Nq ^ (-(1 / b)) := by
    rw [hydef, Real.mul_rpow hε.le (by positivity), ← Real.rpow_natCast Nq 2,
      ← Real.rpow_mul hNq0.le]
    congr 2; push_cast; field_simp
  rw [h1, h4, h6]
  have hNN : Nq * (Nq ^ ((1 - b) / b) * Nq ^ (-(1 / b))) = 1 := by
    rw [← Real.rpow_add hNq0]
    calc Nq * Nq ^ ((1 - b) / b + -(1 / b)) = Nq * Nq ^ (-1 : ℝ) := by congr 2; field_simp; ring
      _ = 1 := by rw [Real.rpow_neg_one]; field_simp
  have hε' : 0 ≤ ε ^ (-(1 / (2 * b))) := Real.rpow_nonneg hε.le _
  calc Nq * ((4 * A) ^ (1 / b) * (ε ^ (-(1 / (2 * b))) * Nq ^ (-(1 / b))))
      = ((4 * A) ^ (1 / b)) * (Nq * Nq ^ (-(1 / b))) * ε ^ (-(1 / (2 * b))) := by ring
    _ ≤ (Nq ^ ((1 - b) / b)) * (Nq * Nq ^ (-(1 / b))) * ε ^ (-(1 / (2 * b))) := by
        apply mul_le_mul_of_nonneg_right _ hε'
        exact mul_le_mul_of_nonneg_right h5 (by positivity)
    _ = ε ^ (-(1 / (2 * b))) := by
        have : Nq ^ ((1 - b) / b) * (Nq * Nq ^ (-(1 / b))) * ε ^ (-(1 / (2 * b)))
            = (Nq * (Nq ^ ((1 - b) / b) * Nq ^ (-(1 / b)))) * ε ^ (-(1 / (2 * b))) := by ring
        rw [this, hNN, one_mul]

private lemma uu_thr_log {c s : ℝ} (hc : 0 < c) (hs : 0 < s) :
    ∀ᶠ N : ℕ in atTop, c * Real.log (N : ℝ) ≤ (N : ℝ) ^ s := by
  have hNt : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have ht := (tendsto_rpow_atTop (show 0 < s / 2 by linarith)).comp hNt
  filter_upwards [ht.eventually_ge_atTop (2 * c / s), eventually_ge_atTop 1] with N hN hN1
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have h1 := Real.log_le_rpow_div (show (0 : ℝ) ≤ N by linarith) (show 0 < s / 2 by linarith)
  have h2 : (N : ℝ) ^ s = (N : ℝ) ^ (s / 2) * (N : ℝ) ^ (s / 2) := by
    rw [← Real.rpow_add (by linarith)]; congr 1; ring
  have hN' : 2 * c / s ≤ (N : ℝ) ^ (s / 2) := hN
  have hp : 0 < (N : ℝ) ^ (s / 2) := Real.rpow_pos_of_pos (by linarith) _
  calc c * Real.log (N : ℝ) ≤ c * ((N : ℝ) ^ (s / 2) / (s / 2)) := mul_le_mul_of_nonneg_left h1 hc.le
    _ = (2 * c / s) * (N : ℝ) ^ (s / 2) := by field_simp
    _ ≤ (N : ℝ) ^ (s / 2) * (N : ℝ) ^ (s / 2) := mul_le_mul_of_nonneg_right hN' hp.le
    _ = _ := h2.symm

private lemma uu_thr_loglog {c q : ℝ} (hc : 0 < c) (hq : 0 < q) :
    ∀ᶠ N : ℕ in atTop, 2 * Real.log (c * Real.log (N : ℝ)) ≤ q * Real.log (N : ℝ) := by
  have hNt : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hl : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop := Real.tendsto_log_atTop.comp hNt
  set M : ℝ := 4 * c / q with hM
  have hM0 : 0 < M := by rw [hM]; positivity
  filter_upwards [hl.eventually_ge_atTop (4 * Real.log M / q + 1), hl.eventually_gt_atTop 0] with N hN hN0
  set ℓ : ℝ := Real.log (N : ℝ) with hℓ
  have h1 : Real.log (c * ℓ / M) ≤ c * ℓ / M - 1 := Real.log_le_sub_one_of_pos (by positivity)
  rw [Real.log_div (by positivity) hM0.ne', Real.log_mul hc.ne' hN0.ne'] at h1
  have h2 : c * ℓ / M = q * ℓ / 4 := by rw [hM]; field_simp
  rw [← Real.log_mul hc.ne' hN0.ne'] at h1
  have hlog : Real.log (c * ℓ) ≤ q * ℓ / 4 - 1 + Real.log M := by
    rw [Real.log_mul hc.ne' hN0.ne'] at h1 ⊢
    rw [h2] at h1
    linarith
  have h3 : 4 * Real.log M / q + 1 ≤ ℓ := hN
  have h4 : 4 * Real.log M ≤ q * ℓ := by
    have := (div_le_iff₀ hq).1 (show 4 * Real.log M / q ≤ ℓ - 1 by linarith)
    nlinarith
  nlinarith

/-- Truncated bound at the closed-form point `Z = max(Eh, Ew)`. -/
private lemma uu_trunc {C D τ r0 b A ε Nq I : ℝ} (hC : 0 < C) (hD : 0 < D) (hr0 : 1 ≤ r0)
    (hb0 : 0 < b) (hA : 0 < A) (hε : 0 < ε) (hNq : 1 ≤ Nq) (hs2C : Real.sqrt ε ≤ 2 * C)
    (hEhτ : D * (2 * C / Real.sqrt ε) ^ (1 / r0) ≤ τ * Nq)
    (hEwτ : Nq * (2 * Real.sqrt A * (ε * Nq ^ 2) ^ (-(1 / 4 : ℝ))) ^ (2 / b) ≤ τ * Nq)
    (hX : ∀ H : ℝ, 0 ≤ H → H ≤ τ * Nq - D →
      C * (1 + H / D) ^ (-r0) + ε ^ (1 / 4 : ℝ) * Real.sqrt A * Nq ^ (-(1 / 2 : ℝ)) *
        ((D + H) / Nq) ^ (-(b / 2)) ≤ Real.sqrt ε →
      I ≤ C * D * Ir r0 (H / D) + 3 * (D + H) * Real.sqrt ε) :
    I ≤ C * D * Ir r0 ((max (D * (2 * C / Real.sqrt ε) ^ (1 / r0))
        (Nq * (2 * Real.sqrt A * (ε * Nq ^ 2) ^ (-(1 / 4 : ℝ))) ^ (2 / b)) - D) / D) +
      3 * max (D * (2 * C / Real.sqrt ε) ^ (1 / r0))
        (Nq * (2 * Real.sqrt A * (ε * Nq ^ 2) ^ (-(1 / 4 : ℝ))) ^ (2 / b)) * Real.sqrt ε := by
  obtain ⟨hH0, hHw⟩ := uu_Hchoice (C := C) (D := D) (τ := τ) (r0 := r0) (b := b) (A := A)
    (ε := ε) (Nq := Nq) hC hD hr0 hb0 hA hε hNq hs2C
  have hZτ : max (D * (2 * C / Real.sqrt ε) ^ (1 / r0))
        (Nq * (2 * Real.sqrt A * (ε * Nq ^ 2) ^ (-(1 / 4 : ℝ))) ^ (2 / b)) ≤ τ * Nq :=
    max_le hEhτ hEwτ
  have := hX _ hH0 (by linarith only [hZτ]) hHw
  have hDH : D + (max (D * (2 * C / Real.sqrt ε) ^ (1 / r0))
        (Nq * (2 * Real.sqrt A * (ε * Nq ^ 2) ^ (-(1 / 4 : ℝ))) ^ (2 / b)) - D) =
      max (D * (2 * C / Real.sqrt ε) ^ (1 / r0))
        (Nq * (2 * Real.sqrt A * (ε * Nq ^ 2) ^ (-(1 / 4 : ℝ))) ^ (2 / b)) := by ring
  rw [hDH] at this
  exact this

private lemma uu_minfin {I Λ ℓ a b : ℝ} (h1 : I ≤ a * Λ) (h2 : I ≤ b * ℓ) (hΛ : 0 ≤ Λ) (hℓ : 0 ≤ ℓ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) : I ≤ max a b * min Λ ℓ := by
  rcases le_total Λ ℓ with h | h
  · rw [min_eq_left h]
    exact h1.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hΛ)
  · rw [min_eq_right h]
    exact h2.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hℓ)

private lemma uu_amgm {A y : ℝ} (hA : 0 ≤ A) (hy : 0 ≤ y) :
    Real.sqrt A * y ^ (1 / 4 : ℝ) ≤ (A + Real.sqrt y) / 2 := by
  have h1 : (y ^ (1 / 4 : ℝ)) ^ 2 = Real.sqrt y := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hy, Real.sqrt_eq_rpow]; norm_num
  nlinarith [sq_nonneg (Real.sqrt A - y ^ (1 / 4 : ℝ)), Real.sq_sqrt hA]

/-- The critical templated regime `r = 1`. -/
private lemma uu_eq1 {p q T Kf Ks υ b : ℝ} (hp : 1 < p) (hq : 0 < q) (hT : 4 ≤ T)
    (hr : rq p q = 1) (hKf : 0 ≤ Kf) (hKs : 0 < Ks) (hυ : 1 < υ) (hb0 : 0 < b) (hb1 : b < 1) :
    ∃ (N1 : ℕ) (K : ℝ), 0 < K ∧ ∀ (N : ℕ) (ε : ℝ) (w c : Fin N → ℝ) (Y : ℝ → ℝ),
      N1 ≤ N → 0 < ε → ε < clockEps0 p q T → (∀ l, 0 ≤ w l) → ∑ l, w l = 1 →
      (∀ l, 2 * (N : ℝ) ^ (-q) ≤ c l) →
      phaseTemplate (mixG w c) (N : ℝ) ((N : ℝ) ^ q - 1) q Kf Ks υ b →
      ContinuousOn Y (Ici 0) → (∀ u ∈ Ici (0 : ℝ), 0 < Y u) →
      (∀ u ∈ Ici (0 : ℝ), Y u = fNq (N : ℕ∞) p q u +
        Real.sqrt ε * Muon.Foundations.oneSidedConv (fun v => Real.sqrt (Y v)) (mixG w c) u) →
      dimClockI Y T ε ≤ K * min (Real.log (1 / ε)) (Real.log (N : ℝ)) := by
  obtain ⟨D, τ, r0, hD, hτ, hτ2, hr01, hr0υ, hr0r, hr0eq, -, hk1, hk2, hk3⟩ :=
    uu_consts hKf hKs hυ hb0 hb1 (le_of_eq hr.symm)
  have hr0 : r0 = 1 := hr0eq hr
  subst hr0
  have hDpos : 0 < D := by linarith
  have hC := pw_Cpq_pos hp hq
  set C : ℝ := Cpq p q with hC_def
  have hpq : p = 2 * q + 1 := by
    have h := hr
    unfold rq at h
    rw [div_eq_iff (mul_pos two_pos hq).ne'] at h
    linarith
  have hδ0 := (dil_delta_facts 1 one_pos).1
  set ce : ℝ := Ks * dilDelta 1 ^ (-b) * C * D with hce
  have hce0 : 0 < ce := by
    have := Real.rpow_pos_of_pos hδ0 (-b)
    rw [hce]; positivity
  have haQ : 0 < aQ q := by unfold aQ; positivity
  set aq : ℝ := aQ q * q with haq
  have haq0 : 0 < aq := by rw [haq]; positivity
  set KJ : ℝ := 2 * C + q * Mpq p q * (2 : ℝ) ^ (-(p / q)) / aQ q + 1 / Real.sqrt (2 * (p - 1)) with hKJ
  set c2 : ℝ := max (4 * ce * q * τ ^ (-b)) (max (2 * C * D / τ) 1) with hc2
  have hc2a : 4 * ce * q * τ ^ (-b) ≤ c2 := le_max_left _ _
  have hc2b : 2 * C * D / τ ≤ c2 := (le_max_left _ _).trans (le_max_right _ _)
  have hc2c : 1 ≤ c2 := (le_max_right _ _).trans (le_max_right _ _)
  have hc20 : 0 < c2 := by linarith
  have hNt : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hDt : ∀ᶠ n : ℕ in atTop, D < τ * (n : ℝ) ^ q := by
    have ht := (tendsto_rpow_atTop hq).comp hNt
    filter_upwards [ht.eventually_gt_atTop (D / τ)] with n hn
    rw [div_lt_iff₀ hτ] at hn
    change D < (n : ℝ) ^ q * τ at hn
    linarith
  have hthr3 := uu_thr_log (c := 4 * ce * q) (s := q * (1 - b) / 2) (by positivity) (by
    have : 0 < 1 - b := by linarith
    positivity)
  have hthr4 := uu_thr_loglog (c := c2) (q := q) hc20 hq
  obtain ⟨N1, hN1⟩ := eventually_atTop.1 (hDt.and (hthr3.and (hthr4.and (eventually_ge_atTop 4))))
  set K1 : ℝ := C * D * Real.log (2 * C + 1) + C * D / (2 * b) + 6 * C * D + 12 * ce * τ ^ (1 - b) + 3
    with hK1
  have hK10 : 0 < K1 := by
    have : 0 ≤ Real.log (2 * C + 1) := Real.log_nonneg (by linarith)
    have := Real.rpow_pos_of_pos hτ (1 - b)
    rw [hK1]; positivity
  set KG : ℝ := C * D * q + 2 * |aq| + 3 * c2 + 4 * τ ^ (-(b / 2)) * (ce * q + c2) + 2 * |KJ|
    + 8 * C * D / τ with hKG
  have hKG0 : 0 ≤ KG := by
    have := Real.rpow_pos_of_pos hτ (-(b / 2))
    rw [hKG]; positivity
  have hqm : 0 < min q 1 := lt_min hq one_pos
  refine ⟨N1, max (KG / min q 1) (max K1 (2 * q * K1)) + 1, by positivity, ?_⟩
  intro N ε w c Y hN hε hε0 hw hw1 hc htemp hYc hYp hY
  obtain ⟨hu0, hthr3N, hthr4N, hN4⟩ := hN1 N hN
  have hN1' : 1 ≤ N := by omega
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN1'
  have hNpos : (0 : ℝ) < N := by linarith
  set ℓ : ℝ := Real.log (N : ℝ) with hℓ
  have hℓ1 : 1 ≤ ℓ := by
    have h4 : (4 : ℝ) ≤ N := by exact_mod_cast hN4
    have h5 : Real.log 4 ≤ ℓ := Real.log_le_log (by norm_num) h4
    have h2 : (1 : ℝ) < Real.log 4 := by
      rw [show (4 : ℝ) = 2 * 2 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
      have := Real.log_two_gt_d9; linarith
    linarith
  set Nq : ℝ := (N : ℝ) ^ q with hNq_def
  have hNq1 : 1 ≤ Nq := Real.one_le_rpow hNr hq.le
  have hNq0 : 0 < Nq := by linarith
  have hlogNq : Real.log Nq = q * ℓ := by rw [hNq_def, Real.log_rpow hNpos]
  set L : ℝ := Real.log (τ * Nq / D) with hL_def
  have hτNqD : 1 < τ * Nq / D := by rw [lt_div_iff₀ hDpos]; linarith only [hu0]
  have hL0 : 0 < L := Real.log_pos hτNqD
  have hLle : L ≤ q * ℓ := by
    rw [← hlogNq]
    apply Real.log_le_log (by linarith only [hτNqD])
    rw [div_le_iff₀ hDpos]
    have : τ ≤ D := by linarith only [hτ2, hD]
    nlinarith only [mul_le_mul_of_nonneg_right this hNq0.le]
  set A : ℝ := ce * L with hA_def
  have hA0 : 0 < A := mul_pos hce0 hL0
  have hAle : A ≤ ce * (q * ℓ) := mul_le_mul_of_nonneg_left hLle hce0.le
  have hLI : ∀ z : ℝ, 0 ≤ z → z ≤ τ * Nq / D - 1 → Ir 1 z ≤ L := by
    intro z hz hz'
    rw [un_Ir_one hz]
    apply Real.log_le_log (by linarith only [hz])
    linarith only [hz']
  have core := uu_core (A := A) (L := L) hp hq hT hKf hKs hυ hb0 hb1 hD hτ hτ2 hr01 hr0υ hr0r hk1 hk2 hk3 hL0
    (by rw [hA_def, hce]) hε hε0 hN4 hu0 hLI w c hw hw1 hc htemp Y hYc hYp hY
  have hJN : JN N p q ≤ |aq| * ℓ + |KJ| := by
    have h := (abs_le.1 (lem_app_phase_forcing_integrals_i hq hpq N hN1')).2
    have h2 : aq * ℓ ≤ |aq| * ℓ := mul_le_mul_of_nonneg_right (le_abs_self _) (by linarith)
    have h3 : JN N p q - aQ q * q * ℓ ≤ KJ := h
    have h4 : KJ ≤ |KJ| := le_abs_self _
    have h5 : aQ q * q * ℓ = aq * ℓ := by rw [haq]
    linarith
  have hlog4 : (1 : ℝ) < Real.log 4 := by
    rw [show (4 : ℝ) = 2 * 2 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
    have := Real.log_two_gt_d9; linarith
  have hε14 : ε < 1 / 4 := pw_eps_lt_quarter hε0
  have hΛ : Real.log (1 / ε) = - Real.log ε := by rw [one_div, Real.log_inv]
  have hΛ1 : 1 ≤ Real.log (1 / ε) := by
    rw [hΛ]
    have h1 : Real.log ε < Real.log (1 / 4) := Real.log_lt_log hε hε14
    rw [one_div, Real.log_inv] at h1
    linarith only [h1, hlog4]
  have hlogy : Real.log (ε * Nq ^ 2) = Real.log ε + 2 * (q * ℓ) := by
    rw [Real.log_mul hε.ne' (by positivity), Real.log_pow, hlogNq]; push_cast; ring
  have hmq : min q 1 * ℓ ≤ q * ℓ := mul_le_mul_of_nonneg_right (min_le_left _ _) (by linarith only [hℓ1])
  have hmq1 : min q 1 * ℓ ≤ ℓ := by
    have := mul_le_mul_of_nonneg_right (min_le_right q 1) (show 0 ≤ ℓ by linarith only [hℓ1])
    linarith only [this]
  by_cases hy : ε * Nq ^ 2 < (c2 * ℓ) ^ 2
  · -- generic branch
    have hc2ℓ : 0 < c2 * ℓ := by positivity
    have hsy : Real.sqrt (ε * Nq ^ 2) ≤ c2 * ℓ := by
      calc _ ≤ Real.sqrt ((c2 * ℓ) ^ 2) := Real.sqrt_le_sqrt hy.le
        _ = c2 * ℓ := Real.sqrt_sq hc2ℓ.le
    have hΛlow : q * ℓ ≤ Real.log (1 / ε) := by
      have h1 : Real.log (ε * Nq ^ 2) < Real.log ((c2 * ℓ) ^ 2) := Real.log_lt_log (by positivity) hy
      rw [Real.log_pow, hlogy] at h1
      rw [hΛ]
      push_cast at h1
      linarith only [h1, hthr4N]
    have h1 := core.1
    simp only [Real.rpow_one, Real.rpow_neg_one, ← hNq_def, ← hC_def] at h1
    have hamgm := uu_amgm (A := A) (y := ε * Nq ^ 2) hA0.le (by positivity)
    have ht0 : 0 < τ ^ (-(b / 2)) := Real.rpow_pos_of_pos hτ _
    have e1 : C * D * L ≤ C * D * (q * ℓ) := mul_le_mul_of_nonneg_left hLle (by positivity)
    have e3 : Real.sqrt A * τ ^ (-(b / 2)) * (ε * Nq ^ 2) ^ (1 / 4 : ℝ) ≤
        τ ^ (-(b / 2)) * ((A + c2 * ℓ) / 2) := by
      have := mul_le_mul_of_nonneg_left (hamgm.trans (by linarith only [hsy] : (A + Real.sqrt (ε * Nq ^ 2)) / 2 ≤ (A + c2 * ℓ) / 2)) ht0.le
      linarith only [this]
    have e4 : τ ^ (-(b / 2)) * ((A + c2 * ℓ) / 2) ≤ τ ^ (-(b / 2)) * ((ce * (q * ℓ) + c2 * ℓ) / 2) :=
      mul_le_mul_of_nonneg_left (by linarith only [hAle]) ht0.le
    have e5 : |KJ| ≤ |KJ| * ℓ := le_mul_of_one_le_right (abs_nonneg _) hℓ1
    have e6 : 8 * C * D / τ ≤ 8 * C * D / τ * ℓ := le_mul_of_one_le_right (by positivity) hℓ1
    have e7 : C * D * τ⁻¹ = C * D / τ := by rw [div_eq_mul_inv]
    have hKGℓ : KG * ℓ = (C * D * q + 2 * |aq| + 3 * c2 + 4 * τ ^ (-(b / 2)) * (ce * q + c2)) * ℓ
        + (2 * |KJ| + 8 * C * D / τ) * ℓ := by rw [hKG]; ring
    have hIK : dimClockI Y T ε ≤ KG * ℓ := by
      rw [hKGℓ]
      have g1 : 8 * (C * D * τ⁻¹ + Real.sqrt A * τ ^ (-(b / 2)) * (ε * Nq ^ 2) ^ (1 / 4 : ℝ)) ≤
          8 * C * D / τ * ℓ + 4 * τ ^ (-(b / 2)) * (ce * q + c2) * ℓ := by
        have := e3.trans e4
        have e8 : 8 * (C * D * τ⁻¹) = 8 * C * D / τ := by rw [div_eq_mul_inv]; ring
        linarith only [this, e6, e8, e7]
      have g2 : 2 * JN N p q ≤ 2 * |aq| * ℓ + 2 * |KJ| * ℓ := by
        linarith only [hJN, e5]
      linarith only [h1, e1, g1, g2, hsy]
    have hmin : min q 1 * ℓ ≤ min (Real.log (1 / ε)) ℓ := le_min (hmq.trans hΛlow) hmq1
    have hKm : KG * ℓ ≤ KG / min q 1 * min (Real.log (1 / ε)) ℓ := by
      calc KG * ℓ = KG / min q 1 * (min q 1 * ℓ) := by field_simp
        _ ≤ _ := mul_le_mul_of_nonneg_left hmin (div_nonneg hKG0 hqm.le)
    have hmin0 : 0 ≤ min (Real.log (1 / ε)) ℓ := le_min (by linarith only [hΛ1]) (by linarith only [hℓ1])
    refine hIK.trans (hKm.trans ?_)
    nlinarith only [mul_le_mul_of_nonneg_right (le_max_left (KG / min q 1) (max K1 (2 * q * K1)))
      hmin0, hmin0]
  · -- large `y` branch
    push_neg at hy
    have hc2ℓ1 : 1 ≤ c2 * ℓ := by nlinarith only [hc2c, hℓ1]
    have hy1 : 1 ≤ ε * Nq ^ 2 := by nlinarith only [hy, hc2ℓ1]
    have ht0 : 0 < τ ^ (-b) := Real.rpow_pos_of_pos hτ _
    -- thresholds
    have hYh : (D * (2 * C) ^ (1 / (1 : ℝ)) / τ) ^ (2 * (1 : ℝ)) ≤ ε * Nq ^ 2 := by
      rw [show (1 : ℝ) / 1 = 1 by norm_num, Real.rpow_one, show (2 : ℝ) * 1 = 2 by norm_num,
        Real.rpow_two]
      have h1 : D * (2 * C) / τ ≤ c2 * ℓ := by
        have : D * (2 * C) / τ = 2 * C * D / τ := by ring
        rw [this]
        nlinarith only [hc2b, hℓ1, hc2c, mul_le_mul_of_nonneg_right hc2b (show 0 ≤ ℓ by linarith only [hℓ1])]
      have h0 : 0 ≤ D * (2 * C) / τ := by positivity
      nlinarith only [pow_le_pow_left₀ h0 h1 2, hy]
    have hAw : 4 * A * τ ^ (-b) ≤ c2 * ℓ := by
      have h1 : 4 * A * τ ^ (-b) ≤ 4 * (ce * (q * ℓ)) * τ ^ (-b) :=
        mul_le_mul_of_nonneg_right (by linarith only [hAle]) ht0.le
      have h2 : 4 * ce * q * τ ^ (-b) * ℓ ≤ c2 * ℓ :=
        mul_le_mul_of_nonneg_right hc2a (by linarith only [hℓ1])
      nlinarith only [h1, h2]
    have hYw : 16 * A ^ 2 * τ ^ (-(2 * b)) ≤ ε * Nq ^ 2 := by
      have hτ2' : (τ ^ (-b)) ^ 2 = τ ^ (-(2 * b)) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hτ.le]; push_cast; ring_nf
      have : 16 * A ^ 2 * τ ^ (-(2 * b)) = (4 * A * τ ^ (-b)) ^ 2 := by
        rw [← hτ2']; ring
      rw [this]
      have h0 : 0 ≤ 4 * A * τ ^ (-b) := by positivity
      nlinarith only [pow_le_pow_left₀ h0 hAw 2, hy]
    have hs1 : Real.sqrt ε ≤ 1 := by rw [Real.sqrt_le_one]; linarith only [hε14]
    obtain ⟨hε8, hεC⟩ := pw_eps_facts ε hε0
    have hs2C : Real.sqrt ε ≤ 2 * C := by
      have : Real.sqrt ε ≤ Real.sqrt (C ^ 2) := Real.sqrt_le_sqrt hεC.le
      rw [Real.sqrt_sq hC.le] at this; linarith only [this, hC]
    have hEhτ : D * (2 * C / Real.sqrt ε) ^ (1 / (1 : ℝ)) ≤ τ * Nq :=
      uu_Eh_le hDpos hC hτ hr01 hε hNq1 hYh
    have hEwτ : Nq * (2 * Real.sqrt A * (ε * Nq ^ 2) ^ (-(1 / 4 : ℝ))) ^ (2 / b) ≤ τ * Nq := by
      have := uu_Ew_le hA0 hτ hb0 (hYw.trans le_rfl)
      calc _ ≤ Nq * τ := mul_le_mul_of_nonneg_left this hNq0.le
        _ = τ * Nq := mul_comm _ _
    have core2 : ∀ H : ℝ, 0 ≤ H → H ≤ τ * Nq - D →
        C * (1 + H / D) ^ (-(1 : ℝ)) + ε ^ (1 / 4 : ℝ) * Real.sqrt A * Nq ^ (-(1 / 2 : ℝ)) *
          ((D + H) / Nq) ^ (-(b / 2)) ≤ Real.sqrt ε →
        dimClockI Y T ε ≤ C * D * Ir 1 (H / D) + 3 * (D + H) * Real.sqrt ε := core.2
    have htr := uu_trunc hC hDpos hr01 hb0 hA0 hε hNq1 hs2C hEhτ hEwτ core2
    obtain ⟨hZD, -⟩ := uu_Hchoice (C := C) (D := D) (τ := τ) (r0 := 1) (b := b) (A := A)
      (ε := ε) (Nq := Nq) hC hDpos hr01 hb0 hA0 hε hNq1 hs2C
    set Eh : ℝ := D * (2 * C / Real.sqrt ε) ^ (1 / (1 : ℝ)) with hEh
    set Ew : ℝ := Nq * (2 * Real.sqrt A * (ε * Nq ^ 2) ^ (-(1 / 4 : ℝ))) ^ (2 / b) with hEw
    set Z : ℝ := max Eh Ew with hZ
    have hs : 0 < Real.sqrt ε := Real.sqrt_pos.2 hε
    have hZD' : D ≤ Z := by linarith only [hZD]
    have hIr : Ir 1 ((Z - D) / D) = Real.log (Z / D) := by
      rw [un_Ir_one (div_nonneg (by linarith only [hZD']) hDpos.le)]
      congr 1; field_simp; ring
    rw [hIr] at htr
    -- the bounds for `Z`
    have hEhdef : Eh = 2 * C * D / Real.sqrt ε := by
      rw [hEh, show (1 : ℝ) / 1 = 1 by norm_num, Real.rpow_one]; field_simp
    have hA4 : 4 * A ≤ Nq ^ ((1 - b) / 2) := by
      have h1 : Nq ^ ((1 - b) / 2) = (N : ℝ) ^ (q * (1 - b) / 2) := by
        rw [hNq_def, ← Real.rpow_mul hNpos.le]; congr 1; ring
      have h2 : 4 * A ≤ 4 * ce * q * ℓ := by nlinarith only [hAle]
      rw [h1]
      exact h2.trans hthr3N
    have hA4' : 4 * A ≤ Nq ^ (1 - b) :=
      hA4.trans (Real.rpow_le_rpow_of_exponent_le hNq1 (by linarith only [hb1]))
    have hEwε : Ew ≤ ε ^ (-(1 / (2 * b))) := uu_Ew_eps hA0 hb0 hb1 hε hNq1 hA4'
    have hinvs : (Real.sqrt ε)⁻¹ ≤ ε ^ (-(1 / (2 * b))) := by
      have : (Real.sqrt ε)⁻¹ = ε ^ (-(1 / 2 : ℝ)) := by
        rw [Real.sqrt_eq_rpow, Real.rpow_neg hε.le]
      rw [this]
      exact Real.rpow_le_rpow_of_exponent_ge hε (by linarith only [hε14]) (by
        have : 1 / 2 ≤ 1 / (2 * b) := by
          rw [div_le_div_iff₀ (by norm_num) (by positivity)]; nlinarith only [hb1, hb0]
        linarith only [this])
    have hZle : Z / D ≤ (2 * C + 1) * ε ^ (-(1 / (2 * b))) := by
      have hZs : Z ≤ Eh + Ew := max_le (by linarith only [hEhdef, hEwε, show 0 ≤ Ew from by positivity]) (by
        have : 0 ≤ Eh := by rw [hEhdef]; positivity
        linarith only [this])
      have hEh' : Eh / D ≤ 2 * C * ε ^ (-(1 / (2 * b))) := by
        rw [hEhdef]
        have e : 2 * C * D / Real.sqrt ε / D = 2 * C * (Real.sqrt ε)⁻¹ := by field_simp
        rw [e]
        exact mul_le_mul_of_nonneg_left hinvs (by positivity)
      have hEw0 : 0 ≤ Ew := by positivity
      have hEw' : Ew / D ≤ ε ^ (-(1 / (2 * b))) := (div_le_self hEw0 hD).trans hEwε
      calc Z / D ≤ (Eh + Ew) / D := div_le_div_of_nonneg_right hZs hDpos.le
        _ = Eh / D + Ew / D := add_div _ _ _
        _ ≤ (2 * C + 1) * ε ^ (-(1 / (2 * b))) := by linarith only [hEh', hEw']
    have hZpos : 0 < Z / D := div_pos (by linarith only [hZD', hDpos]) hDpos
    have hlogZ : Real.log (Z / D) ≤ Real.log (2 * C + 1) + Real.log (1 / ε) / (2 * b) := by
      have h1 := Real.log_le_log hZpos hZle
      rw [Real.log_mul (by linarith only [hC]) (Real.rpow_pos_of_pos hε _).ne', Real.log_rpow hε] at h1
      rw [hΛ]
      have : -(1 / (2 * b)) * Real.log ε = -Real.log ε / (2 * b) := by field_simp
      linarith only [h1, this]
    have hsEh : Real.sqrt ε * Eh = 2 * C * D := by rw [hEhdef]; field_simp
    have hZs : Z ≤ Eh + Ew := max_le (by
        have : 0 ≤ Ew := by positivity
        linarith only [this]) (by
        have : 0 ≤ Eh := by rw [hEhdef]; positivity
        linarith only [this])
    have hsZ : Real.sqrt ε * Z ≤ 2 * C * D + Real.sqrt ε * Ew := by
      have := mul_le_mul_of_nonneg_left hZs hs.le
      linarith only [this, hsEh, mul_add (Real.sqrt ε) Eh Ew]
    have hCDlog : C * D * Real.log (Z / D) ≤ C * D * (Real.log (2 * C + 1) + Real.log (1 / ε) / (2 * b)) :=
      mul_le_mul_of_nonneg_left hlogZ (by positivity)
    have hI1 : dimClockI Y T ε ≤ C * D * (Real.log (2 * C + 1) + Real.log (1 / ε) / (2 * b))
        + 3 * (2 * C * D + Real.sqrt ε * Ew) := by
      linarith only [htr, hCDlog, hsZ, mul_comm (Real.sqrt ε) Z]
    have hlogy' := hlogy
    have hΛup : Real.log (1 / ε) ≤ 2 * (q * ℓ) := by
      have : 0 ≤ Real.log (ε * Nq ^ 2) := Real.log_nonneg hy1
      rw [hΛ]; linarith only [this, hlogy']
    have hlog2C : 0 ≤ Real.log (2 * C + 1) := Real.log_nonneg (by linarith only [hC])
    have hΛ1' := hΛ1
    have hIK1 : dimClockI Y T ε ≤ K1 * Real.log (1 / ε) := by
      by_cases hyN : ε * Nq ^ 2 ≤ Nq
      · have hΛlow : q * ℓ ≤ Real.log (1 / ε) := by
          have h1 : Real.log (ε * Nq ^ 2) ≤ Real.log Nq := Real.log_le_log (by positivity) hyN
          rw [hlogy, hlogNq] at h1
          rw [hΛ]; linarith only [h1]
        have hsw := uu_sEw2 hA0 hτ hb0 hb1 hε hNq1 hYw
        have hτ1b : 0 < τ ^ (1 - b) := Real.rpow_pos_of_pos hτ _
        have h4 : 4 * A * τ ^ (1 - b) ≤ 4 * ce * τ ^ (1 - b) * Real.log (1 / ε) := by
          have : 4 * A * τ ^ (1 - b) ≤ 4 * (ce * (q * ℓ)) * τ ^ (1 - b) :=
            mul_le_mul_of_nonneg_right (by linarith only [hAle]) hτ1b.le
          have h5 := mul_le_mul_of_nonneg_left hΛlow (show 0 ≤ 4 * ce * τ ^ (1 - b) by positivity)
          nlinarith only [this, h5]
        have hsw' : Real.sqrt ε * Ew ≤ 4 * ce * τ ^ (1 - b) * Real.log (1 / ε) := hsw.trans h4
        have hCD0 : 0 ≤ C * D := by positivity
        have hc1 : C * D * Real.log (2 * C + 1) ≤ C * D * Real.log (2 * C + 1) * Real.log (1 / ε) :=
          le_mul_of_one_le_right (by positivity) hΛ1
        have hc2' : 6 * C * D ≤ 6 * C * D * Real.log (1 / ε) :=
          le_mul_of_one_le_right (by positivity) hΛ1
        have e2 : K1 * Real.log (1 / ε) = C * D * Real.log (2 * C + 1) * Real.log (1 / ε)
            + C * D / (2 * b) * Real.log (1 / ε) + 6 * C * D * Real.log (1 / ε)
            + 12 * ce * τ ^ (1 - b) * Real.log (1 / ε) + 3 * Real.log (1 / ε) := by rw [hK1]; ring
        have e1 : C * D * (Real.log (2 * C + 1) + Real.log (1 / ε) / (2 * b)) +
            3 * (2 * C * D + Real.sqrt ε * Ew) = C * D * Real.log (2 * C + 1)
            + C * D / (2 * b) * Real.log (1 / ε) + 6 * C * D + 3 * (Real.sqrt ε * Ew) := by ring
        linarith only [hI1, e1, e2, hsw', hc1, hc2', hΛ1]
      · push_neg at hyN
        have hsw : Real.sqrt ε * Ew ≤ 1 := uu_sEw3 hA0 hb0 hb1 hε hNq1 hA4 hyN.le
        have hc1 : C * D * Real.log (2 * C + 1) ≤ C * D * Real.log (2 * C + 1) * Real.log (1 / ε) :=
          le_mul_of_one_le_right (by positivity) hΛ1
        have hc2' : 6 * C * D ≤ 6 * C * D * Real.log (1 / ε) :=
          le_mul_of_one_le_right (by positivity) hΛ1
        have hc3 : (3 : ℝ) ≤ 3 * Real.log (1 / ε) := by linarith only [hΛ1]
        have hCD0 : 0 ≤ C * D := by positivity
        have hτ1b : 0 < τ ^ (1 - b) := Real.rpow_pos_of_pos hτ _
        have e2 : K1 * Real.log (1 / ε) = C * D * Real.log (2 * C + 1) * Real.log (1 / ε)
            + C * D / (2 * b) * Real.log (1 / ε) + 6 * C * D * Real.log (1 / ε)
            + 12 * ce * τ ^ (1 - b) * Real.log (1 / ε) + 3 * Real.log (1 / ε) := by rw [hK1]; ring
        have e1 : C * D * (Real.log (2 * C + 1) + Real.log (1 / ε) / (2 * b)) +
            3 * (2 * C * D + Real.sqrt ε * Ew) = C * D * Real.log (2 * C + 1)
            + C * D / (2 * b) * Real.log (1 / ε) + 6 * C * D + 3 * (Real.sqrt ε * Ew) := by ring
        have hce12 : 0 ≤ 12 * ce * τ ^ (1 - b) * Real.log (1 / ε) :=
          mul_nonneg (by positivity) (by linarith only [hΛ1])
        linarith only [hI1, e1, e2, hsw, hc1, hc2', hΛ1, hce12]
    have hIK2 : dimClockI Y T ε ≤ (2 * q * K1) * ℓ := by
      have := mul_le_mul_of_nonneg_left hΛup hK10.le
      nlinarith only [hIK1, this]
    have hmin0 : 0 ≤ min (Real.log (1 / ε)) ℓ := le_min (by linarith only [hΛ1]) (by linarith only [hℓ1])
    have := uu_minfin hIK1 hIK2 (by linarith only [hΛ1]) (by linarith only [hℓ1]) hK10.le (by positivity)
    refine this.trans ?_
    nlinarith only [mul_le_mul_of_nonneg_right (le_max_right (KG / min q 1) (max K1 (2 * q * K1)))
      hmin0, hmin0]


/-- The templated regime `r ≥ 1`, in the form of the unified exponent. -/
private lemma uu_tpl_all {p q T Kf Ks υ b : ℝ} (hp : 1 < p) (hq : 0 < q) (hT : 4 ≤ T)
    (hr : 1 ≤ rq p q) (hKf : 0 ≤ Kf) (hKs : 0 < Ks) (hυ : 1 < υ) (hb0 : 0 < b) (hb1 : b < 1) :
    ∃ (N1 : ℕ) (K : ℝ), 0 < K ∧ ∀ (N : ℕ) (ε : ℝ) (w c : Fin N → ℝ) (Y : ℝ → ℝ),
      N1 ≤ N → 0 < ε → ε < clockEps0 p q T → (∀ l, 0 ≤ w l) → ∑ l, w l = 1 →
      (∀ l, 2 * (N : ℝ) ^ (-q) ≤ c l) →
      phaseTemplate (mixG w c) (N : ℝ) ((N : ℝ) ^ q - 1) q Kf Ks υ b →
      ContinuousOn Y (Ici 0) → (∀ u ∈ Ici (0 : ℝ), 0 < Y u) →
      (∀ u ∈ Ici (0 : ℝ), Y u = fNq (N : ℕ∞) p q u +
        Real.sqrt ε * Muon.Foundations.oneSidedConv (fun v => Real.sqrt (Y v)) (mixG w c) u) →
      dimClockI Y T ε ≤ K * (if rq p q = 1 then min (Real.log (1 / ε)) (Real.log (N : ℝ)) else 1) := by
  rcases hr.eq_or_lt with h | h
  · obtain ⟨N1, K, hK, hmain⟩ := uu_eq1 hp hq hT h.symm hKf hKs hυ hb0 hb1
    refine ⟨N1, K, hK, ?_⟩
    intro N ε w c Y hN hε hε0 hw hw1 hc htemp hYc hYp hY
    rw [if_pos h.symm]
    exact hmain N ε w c Y hN hε hε0 hw hw1 hc htemp hYc hYp hY
  · obtain ⟨N1, K, hmain⟩ := uu_gt1 hp hq hT h hKf hKs hυ hb0 hb1
    refine ⟨N1, max K 1, lt_max_of_lt_right one_pos, ?_⟩
    intro N ε w c Y hN hε hε0 hw hw1 hc htemp hYc hYp hY
    rw [if_neg (by linarith), mul_one]
    exact (hmain N ε w c Y hN hε hε0 hw hw1 hc htemp hYc hYp hY).trans (le_max_left _ _)

private lemma uu_templ_transfer {ker g : ℝ → ℝ} {N U0 q Kf Ks υ b : ℝ}
    (h : phaseTemplate ker N U0 q Kf Ks υ b) (hg : ∀ u ∈ Ici (0 : ℝ), g u = ker u) :
    phaseTemplate g N U0 q Kf Ks υ b := by
  intro v hv0 hvU
  rw [hg v (Set.mem_Ici.2 hv0)]
  exact h v hv0 hvU

/-- Upper bound for the templated models, `\SignSVD`. -/
private lemma uu_up_svd_tpl (α ς T : ℝ) (hα : 0 < α) (hp : 1 < α + ς) (hT : 4 ≤ T)
    (hr1 : 1 ≤ rq (α + ς) (α / 2)) {Kf Ks υ b : ℝ} (NT : ℕ) (hKf : 0 ≤ Kf) (hKs : 0 < Ks)
    (hυ : 1 < υ) (hb0 : 0 < b) (hb1 : b < 1)
    (htemp : ∀ N : ℕ, NT ≤ N →
      phaseTemplate (svdKernel α N) (N : ℝ) ((N : ℝ) ^ (α / 2) - 1) (α / 2) Kf Ks υ b) :
    ∃ (N0 : ℕ) (ε0 cp : ℝ), 0 < ε0 ∧ 0 < cp ∧
      ∀ (N B : ℕ) (ε : ℝ) (m : RowModel (Fin N)) (Q : ℝ → ℝ),
        N0 ≤ N → N ≤ B → 0 < ε → ε < ε0 →
        IsMatchedModel (phaseKindArrays α ς N B .svd) m ε → IsVolterraSol m Q →
        phaseClockI Q (phaseKindT0 α N B .svd) T ε ≤ cp * phaseUpsilon α ς N ε .svd := by
  have hq : 0 < α / 2 := by linarith
  obtain ⟨N1, K, hK, hmain⟩ := uu_tpl_all (T := T) hp hq hT hr1 hKf hKs hυ hb0 hb1
  refine ⟨max NT (max 1 N1), clockEps0 (α + ς) (α / 2) T, K, pw_clockEps0_pos hp hq hT, hK, ?_⟩
  intro N B ε m Q hN hNB hε hε0 hm hQ
  have hNT : NT ≤ N := (le_max_left _ _).trans hN
  have hN1 : 1 ≤ N := (le_max_left _ _).trans ((le_max_right _ _).trans hN)
  have hNN : N1 ≤ N := (le_max_right _ _).trans ((le_max_right _ _).trans hN)
  obtain ⟨mG, QG, hmG, hQG⟩ := un_pair_svd α ς N B hα hp hN1 hNB ε hε
  obtain ⟨w, c, hw, hw1, hc, hker, hYc, hYp, hY⟩ :=
    fz2_svd_model α ς N B hα hp hN1 hNB ε hε m mG hm hmG Q QG hQ hQG
  have := hmain N ε w c _ hNN hε hε0 hw hw1 hc (uu_templ_transfer (htemp N hNT) hker) hYc hYp hY
  unfold phaseClockI phaseUpsilon
  have hnot : ¬ phaseKindR α ς .svd < 1 := not_lt.2 hr1
  rw [if_neg hnot]
  exact this

/-- Upper bound for the templated models, `\SignSGD`. -/
private lemma uu_up_sgd_tpl (α ς T : ℝ) (hα : 0 < α) (hp : 1 < α + ς) (hT : 4 ≤ T)
    (hr1 : 1 ≤ rq (α + ς) α) {Kf Ks υ b : ℝ} (NT : ℕ) (hKf : 0 ≤ Kf) (hKs : 0 < Ks)
    (hυ : 1 < υ) (hb0 : 0 < b) (hb1 : b < 1)
    (htemp : ∀ N : ℕ, NT ≤ N →
      phaseTemplate (sgdKernel α N) (N : ℝ) ((N : ℝ) ^ α - 1) α Kf Ks υ b) :
    ∃ (N0 : ℕ) (ε0 cp : ℝ), 0 < ε0 ∧ 0 < cp ∧
      ∀ (N B : ℕ) (ε : ℝ) (m : RowModel (Fin N)) (Q : ℝ → ℝ),
        N0 ≤ N → N ≤ B → 0 < ε → ε < ε0 →
        IsMatchedModel (phaseKindArrays α ς N B .sgd) m ε → IsVolterraSol m Q →
        phaseClockI Q (phaseKindT0 α N B .sgd) T ε ≤ cp * phaseUpsilon α ς N ε .sgd := by
  obtain ⟨N1, K, hK, hmain⟩ := uu_tpl_all (T := T) hp hα hT hr1 hKf hKs hυ hb0 hb1
  refine ⟨max NT (max 1 N1), clockEps0 (α + ς) α T, K, pw_clockEps0_pos hp hα hT, hK, ?_⟩
  intro N B ε m Q hN hNB hε hε0 hm hQ
  have hNT : NT ≤ N := (le_max_left _ _).trans hN
  have hN1 : 1 ≤ N := (le_max_left _ _).trans ((le_max_right _ _).trans hN)
  have hNN : N1 ≤ N := (le_max_right _ _).trans ((le_max_right _ _).trans hN)
  obtain ⟨mS, QS, hmS, hQS⟩ := un_pair_sgd α ς N B hα hp hN1 hNB ε hε
  obtain ⟨w, c, hw, hw1, hc, hker, hYc, hYp, hY⟩ :=
    fz2_sgd_model α ς N B hα hp hN1 hNB ε hε mS m hmS hm QS Q hQS hQ
  have := hmain N ε w c _ hNN hε hε0 hw hw1 hc (uu_templ_transfer (htemp N hNT) hker) hYc hYp hY
  unfold phaseClockI phaseUpsilon
  have hnot : ¬ phaseKindR α ς .sgd < 1 := not_lt.2 hr1
  rw [if_neg hnot]
  exact this

private lemma uu_up_tpl_cases (α ς T : ℝ) (hα : 0 < α) (hp : 1 < α + ς) (hT : 4 ≤ T)
    (j : PhaseKind) (hr1 : 1 ≤ phaseKindR α ς j)
    (hcase : (j = .svd ∧ (α < 1 ∨ (1 < α ∧ α < 2))) ∨
      (j = .sgd ∧ (α < 1 / 2 ∨ (1 / 2 < α ∧ α < 1) ∨ 1 < α))) :
    ∃ (N0 : ℕ) (ε0 cp : ℝ), 0 < ε0 ∧ 0 < cp ∧
      ∀ (N B : ℕ) (ε : ℝ) (m : RowModel (Fin N)) (Q : ℝ → ℝ),
        N0 ≤ N → N ≤ B → 0 < ε → ε < ε0 →
        IsMatchedModel (phaseKindArrays α ς N B j) m ε → IsVolterraSol m Q →
        phaseClockI Q (phaseKindT0 α N B j) T ε ≤ cp * phaseUpsilon α ς N ε j := by
  have hpi : (2 : ℝ) < Real.pi := by linarith [Real.pi_gt_three]
  have hpi0 : 0 < 2 / Real.pi := by positivity
  have hpi1 : 2 / Real.pi < 1 := by rw [div_lt_one (by linarith)]; exact hpi
  rcases hcase with ⟨rfl, h⟩ | ⟨rfl, h⟩
  · rcases h with h | ⟨h1, h2⟩
    · obtain ⟨NT, υ, hυ, ht⟩ := lem_app_phase_templates_i hα h
      have h1 : 0 < 1 - α := by linarith
      have h2 : 0 < 1 - α / 2 := by linarith
      exact uu_up_svd_tpl α ς T hα hp hT hr1 NT le_rfl (by positivity) hυ (by norm_num)
        (by norm_num) ht
    · obtain ⟨NT, υ, hυ, ht⟩ := lem_app_phase_templates_ii h1 h2
      have h3 : 0 < 1 - α / 2 := by linarith
      have hE : 0 < Epq α (α / 2) := pw_Epq_pos (by linarith) (by linarith)
      have hb0 : 0 < 2 - 2 / α := by
        have : 2 / α < 2 := by rw [div_lt_iff₀ hα]; linarith
        linarith
      have hb1 : 2 - 2 / α < 1 := by
        have : 1 < 2 / α := by rw [lt_div_iff₀ hα]; linarith
        linarith
      exact uu_up_svd_tpl α ς T hα hp hT hr1 NT le_rfl (by positivity) hυ hb0 hb1 ht
  · rcases h with h | ⟨h1, h2⟩ | h
    · obtain ⟨NT, υ, hυ, ht⟩ := lem_app_phase_templates_iii hα h
      have h1 : 0 < 1 - α := by linarith
      have h2 : 0 < 1 - 2 * α := by linarith
      have h3 : 0 < 1 - 2 / Real.pi := by linarith
      exact uu_up_sgd_tpl α ς T hα hp hT hr1 NT le_rfl (by positivity) hυ (by norm_num)
        (by norm_num) ht
    · obtain ⟨NT, υ, hυ, ht⟩ := lem_app_phase_templates_iv h1 h2
      have h3 : 0 < 1 - α := by linarith
      have h4 : 0 < 1 - 2 / Real.pi := by linarith
      have hE : 0 < Epq (2 * α) α := pw_Epq_pos (by linarith) hα
      have hb0 : 0 < max (2 - 1 / α) (1 / 2) := lt_max_of_lt_right (by norm_num)
      have hb1 : max (2 - 1 / α) (1 / 2) < 1 := by
        refine max_lt ?_ (by norm_num)
        have : 1 < 1 / α := by rw [lt_div_iff₀ hα]; linarith
        linarith
      exact uu_up_sgd_tpl α ς T hα hp hT hr1 NT (by positivity) (by positivity) hυ hb0 hb1 ht
    · obtain ⟨NT, ht⟩ := lem_app_phase_templates_v h
      have hE1 : 0 < Epq (2 * α) α := pw_Epq_pos (by linarith) hα
      have hE2 : 0 < Epq α α := pw_Epq_pos h hα
      have h4 : 0 < 1 - 2 / Real.pi := by linarith
      have hυ : 1 < 2 - 1 / α := by
        have : 1 / α < 1 := by rw [div_lt_one hα]; exact h
        linarith
      have hb0 : 0 < 1 - 1 / α := by
        have : 1 / α < 1 := by rw [div_lt_one hα]; exact h
        linarith
      have hb1 : 1 - 1 / α < 1 := by
        have : 0 < 1 / α := by positivity
        linarith
      exact uu_up_sgd_tpl α ς T hα hp hT hr1 NT (Kf := 4 / Real.pi * Epq (2 * α) α)
        (Ks := 2 * (1 - 2 / Real.pi) * Epq α α) (υ := 2 - 1 / α) (b := 1 - 1 / α)
        (by positivity) (by positivity) hυ hb0 hb1 (fun N hN v hv0 _ => ht N hN v hv0)

private lemma uu_lgbound (ς : ℝ) (hς : 1 < ς) :
    ∃ K0 : ℝ, ∀ (N : ℕ) (ε : ℝ), 1 ≤ N → 0 < ε → ε < 1 → logGlobalErrBound N ς ε ≤ K0 := by
  have hC := lg_Cpos ς hς
  have hr := lg_rgt ς hς
  have hA0 := pw_logA0_nonneg hς
  set C := Cpq (2 + ς) 1 with hCdef
  set r := rq (2 + ς) 1 with hrdef
  set A0 := logGlobalA0 ς with hA0def
  have hr0 : 0 < r - 1 := by linarith
  have hrpos : 0 < r := by linarith
  refine ⟨Real.sqrt (C + Real.sqrt A0 + 1) + C / (r - 1) + 2 * Real.sqrt A0 * (2 * C) ^ (1 / (2 * r))
    + (2 * C) ^ (1 / r) + 8 * A0, ?_⟩
  intro N ε hN hε hε1
  have hL := lg_Hge1 N hN
  unfold logGlobalErrBound
  simp only
  rw [← hCdef, ← hrdef, ← hA0def]
  have t1 : ε ^ (1 / 8 : ℝ) * Real.sqrt (C + Real.sqrt A0 + 1) ≤ Real.sqrt (C + Real.sqrt A0 + 1) := by
    have : ε ^ (1 / 8 : ℝ) ≤ 1 := Real.rpow_le_one hε.le hε1.le (by norm_num)
    exact mul_le_of_le_one_left (Real.sqrt_nonneg _) this
  have t2 : C / (r - 1) * (1 + ε ^ (-(1 / 8 : ℝ))) ^ (1 - r) ≤ C / (r - 1) := by
    have hb : 1 ≤ 1 + ε ^ (-(1 / 8 : ℝ)) := by
      have := Real.rpow_nonneg hε.le (-(1 / 8 : ℝ)); linarith
    have : (1 + ε ^ (-(1 / 8 : ℝ))) ^ (1 - r) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hb (by linarith)
    exact mul_le_of_le_one_right (by positivity) this
  have t3 : 2 * Real.sqrt A0 * (2 * C) ^ (1 / (2 * r)) * Hsum 1 N ^ (-(1 / 2 : ℝ)) *
      ε ^ ((r - 1) / (4 * r)) ≤ 2 * Real.sqrt A0 * (2 * C) ^ (1 / (2 * r)) := by
    have h1 : Hsum 1 N ^ (-(1 / 2 : ℝ)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hL (by norm_num)
    have h2 : ε ^ ((r - 1) / (4 * r)) ≤ 1 :=
      Real.rpow_le_one hε.le hε1.le (by positivity)
    have h3 : 0 ≤ Hsum 1 N ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg (by linarith) _
    have h0 : 0 ≤ 2 * Real.sqrt A0 * (2 * C) ^ (1 / (2 * r)) := by positivity
    calc 2 * Real.sqrt A0 * (2 * C) ^ (1 / (2 * r)) * Hsum 1 N ^ (-(1 / 2 : ℝ)) *
          ε ^ ((r - 1) / (4 * r))
        ≤ 2 * Real.sqrt A0 * (2 * C) ^ (1 / (2 * r)) * 1 * 1 := by
          apply mul_le_mul _ h2 (Real.rpow_nonneg hε.le _) (by positivity)
          exact mul_le_mul_of_nonneg_left h1 h0
      _ = _ := by ring
  have t4 : (2 * C) ^ (1 / r) * ε ^ ((r - 1) / (2 * r)) ≤ (2 * C) ^ (1 / r) := by
    have h2 : ε ^ ((r - 1) / (2 * r)) ≤ 1 := Real.rpow_le_one hε.le hε1.le (by positivity)
    exact mul_le_of_le_one_right (by positivity) h2
  have t5 : 8 * A0 / Hsum 1 N ≤ 8 * A0 := by
    rw [div_le_iff₀ (by linarith)]; nlinarith
  linarith

private lemma uu_svd_gt2_templ (α : ℝ) (h2 : 2 < α) (N : ℕ) (hN : 1 ≤ N) (v : ℝ) (hv : 0 ≤ v) :
    svdKernel α N v ≤ 2 * Epq α (α / 2) * (1 + v) ^ (-(2 - 2 / α)) := by
  have hα0 : 0 < α := by linarith
  have hS := lem_app_phase_sums_i (a := α) (q := α / 2) (by linarith) (by linarith) (N : ℕ∞) hv
  have hd : dAQ α (α / 2) = 2 - 2 / α := by unfold dAQ; field_simp
  rw [hd] at hS
  have hH := un_Hsum_ge_one (α / 2) N hN
  have hcoef : 2 / Hsum (α / 2) N ≤ 2 := by
    rw [div_le_iff₀ (by linarith)]; nlinarith
  have hcoef0 : 0 ≤ 2 / Hsum (α / 2) N := div_nonneg (by norm_num) (by linarith)
  have hE : 0 ≤ Epq α (α / 2) := (pw_Epq_pos (by linarith) (by linarith)).le
  have hpow : 0 ≤ (1 + v) ^ (-(2 - 2 / α)) := Real.rpow_nonneg (by linarith) _
  calc svdKernel α N v = 2 / Hsum (α / 2) N * Lsum (N : ℕ∞) α (α / 2) v := rfl
    _ ≤ 2 / Hsum (α / 2) N * (Epq α (α / 2) * (1 + v) ^ (-(2 - 2 / α))) :=
        mul_le_mul_of_nonneg_left hS hcoef0
    _ ≤ 2 * (Epq α (α / 2) * (1 + v) ^ (-(2 - 2 / α))) :=
        mul_le_mul_of_nonneg_right hcoef (mul_nonneg hE hpow)
    _ = _ := by ring

private lemma uu_up_svd_gt2 (α ς T : ℝ) (hα : 0 < α) (hp : 1 < α + ς) (hT : 4 ≤ T)
    (hr1 : 1 ≤ phaseKindR α ς .svd) (h2 : 2 < α) :
    ∃ (N0 : ℕ) (ε0 cp : ℝ), 0 < ε0 ∧ 0 < cp ∧
      ∀ (N B : ℕ) (ε : ℝ) (m : RowModel (Fin N)) (Q : ℝ → ℝ),
        N0 ≤ N → N ≤ B → 0 < ε → ε < ε0 →
        IsMatchedModel (phaseKindArrays α ς N B .svd) m ε → IsVolterraSol m Q →
        phaseClockI Q (phaseKindT0 α N B .svd) T ε ≤ cp * phaseUpsilon α ς N ε .svd := by
  have hE : 0 < Epq α (α / 2) := pw_Epq_pos (by linarith) (by linarith)
  have hυ : 1 < 2 - 2 / α := by
    have : 2 / α < 1 := by rw [div_lt_one hα]; exact h2
    linarith
  refine uu_up_svd_tpl α ς T hα hp hT hr1 1 (Kf := 2 * Epq α (α / 2)) (Ks := 1) (υ := 2 - 2 / α)
    (b := 1 / 2) (by positivity) one_pos hυ (by norm_num) (by norm_num) ?_
  intro N hN v hv0 _
  have h1 := uu_svd_gt2_templ α h2 N hN v hv0
  have h3 : 0 ≤ 1 * (N : ℝ) ^ (-(α / 2)) * ((1 + v) / (N : ℝ) ^ (α / 2)) ^ (-(1 / 2 : ℝ)) := by positivity
  linarith

/-- `α = 2`, `ς > 1`: the global logarithmic envelope. -/
private lemma uu_up_svd_eq2_gt (ς T : ℝ) (hp : 1 < 2 + ς) (hT : 4 ≤ T) (hς : 1 < ς) :
    ∃ (N0 : ℕ) (ε0 cp : ℝ), 0 < ε0 ∧ 0 < cp ∧
      ∀ (N B : ℕ) (ε : ℝ) (m : RowModel (Fin N)) (Q : ℝ → ℝ),
        N0 ≤ N → N ≤ B → 0 < ε → ε < ε0 →
        IsMatchedModel (phaseKindArrays 2 ς N B .svd) m ε → IsVolterraSol m Q →
        phaseClockI Q (phaseKindT0 2 N B .svd) T ε ≤ cp * phaseUpsilon 2 ς N ε .svd := by
  obtain ⟨K0, hK0⟩ := uu_lgbound ς hς
  have hr : 1 < rq (2 + ς) 1 := lg_rgt ς hς
  have hC : 0 < Cpq (2 + ς) 1 := lg_Cpos ς hς
  have hTpos : 0 < T := by linarith
  have hε0pos : 0 < min (min 1 (min (Cpq (2 + ς) 1 ^ 2) (1 / (8 * T)))) (clockEps0 (2 + ς) 1 T) :=
    lt_min (lt_min one_pos (lt_min (pow_pos hC 2) (by positivity)))
      (pw_clockEps0_pos hp one_pos hT)
  have hQ1 : phaseKindQ 2 .svd = 1 := by norm_num [phaseKindQ]
  refine ⟨max 4 ⌈Real.exp logGlobalL0⌉₊,
    min (min 1 (min (Cpq (2 + ς) 1 ^ 2) (1 / (8 * T)))) (clockEps0 (2 + ς) 1 T),
    max (Jpq (2 + ς) 1 + K0) 1, hε0pos, lt_max_of_lt_right one_pos, ?_⟩
  intro N B ε m Q hN hNB hε hε' hm hQ
  have hN4 : 4 ≤ N := (le_max_left _ _).trans hN
  have hN1 : 1 ≤ N := by omega
  have hNe : Real.exp logGlobalL0 ≤ (N : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast (le_max_right _ _).trans hN)
  have hεlg : ε < min 1 (min (Cpq (2 + ς) 1 ^ 2) (1 / (8 * T))) :=
    lt_of_lt_of_le hε' (min_le_left _ _)
  have hεcl : ε < clockEps0 (2 + ς) 1 T := lt_of_lt_of_le hε' (min_le_right _ _)
  have hε8 : ε < 1 / (8 * T) :=
    lt_of_lt_of_le hεlg ((min_le_right _ _).trans (min_le_right _ _))
  have hε1 : ε < 1 := lt_of_lt_of_le hεlg (min_le_left _ _)
  obtain ⟨hYc, hYf, û, hû, hYû, hhit⟩ := un_hit_j 2 ς T .svd N B (by norm_num) hp hT hN1 hNB ε hε
    hε8 m Q hm hQ
  rw [hQ1] at hYf
  have hiii := lem_app_phase_clock_integral_iii (p := 2 + ς) (q := 1) (T := T) (ε := ε) (H := û)
    (û := û) hp one_pos hT N hN4 hε hεcl hYc hYf hhit hû hYû le_rfl hr
  obtain ⟨-, -, -, hE⟩ := lem_app_phase_log_global_ii ς hς N B hNe hNB T ε hT hε hεlg m hm Q hQ
  have hfh : (firstHit (fun u => Q (svdT0 N B * u)) (T * ε)).toReal = û := by
    have : firstHit (fun u => Q (svdT0 N B * u)) (T * ε) = ENNReal.ofReal û := hhit
    rw [this, ENNReal.toReal_ofReal hû.le]
  rw [hfh] at hE
  unfold phaseErr at hE
  have hKb := hK0 N ε hN1 hε hε1
  have hI := un_I_eq Q (phaseKindT0 2 N B .svd) T ε û hû hhit
  have hE' : (∫ u in (0 : ℝ)..û, (Real.sqrt (Q (phaseKindT0 2 N B .svd * u)) -
      Real.sqrt (fNq (N : ℕ∞) (2 + ς) 1 u))) ≤ logGlobalErrBound N ς ε := hE
  have hJ : (∫ u in (0 : ℝ)..û, Real.sqrt (Q (phaseKindT0 2 N B .svd * u))) ≤ Jpq (2 + ς) 1 + K0 :=
    hiii.2.1.trans (by linarith [hE', hKb])
  have hu1 : phaseUpsilon 2 ς N ε .svd = 1 := by
    unfold phaseUpsilon
    have h1 : ¬ phaseKindR 2 ς .svd < 1 := by
      show ¬ rq (2 + ς) (phaseKindQ 2 .svd) < 1
      rw [hQ1]; linarith
    have h2 : ¬ phaseKindR 2 ς .svd = 1 := by
      show ¬ rq (2 + ς) (phaseKindQ 2 .svd) = 1
      rw [hQ1]; linarith
    rw [if_neg h1, if_neg h2]
  rw [hu1, mul_one, hI]
  exact hJ.trans (le_max_left _ _)

/-- The two-phase consequences with `w = 0` (no tail term), `r_0 = 1`. -/
private lemma uu_core0 {p q T D τ ε : ℝ} (hp : 1 < p) (hq : 0 < q) (hT : 4 ≤ T)
    (hD : 1 ≤ D) (hτ : 0 < τ) (hτ2 : τ ≤ 1 / 2) (hε : 0 < ε) (hεT : ε < clockEps0 p q T)
    {N : ℕ} (hN4 : 4 ≤ N) (hu0 : D < τ * (N : ℝ) ^ q)
    (hr0r : 1 ≤ rq p q)
    (w c : Fin N → ℝ) (hw : ∀ l, 0 ≤ w l) (hw1 : ∑ l, w l = 1)
    (hc : ∀ l, 2 * (N : ℝ) ^ (-q) ≤ c l)
    (hconv : ∀ u ∈ Icc (0 : ℝ) (τ * (N : ℝ) ^ q - D),
      Muon.Foundations.oneSidedConv (fun v => Cpq p q * (1 + v / D) ^ (-(1 : ℝ))) (mixG w c) u
        ≤ 2 * (Cpq p q * (1 + u / D) ^ (-(1 : ℝ))))
    (Y : ℝ → ℝ) (hYc : ContinuousOn Y (Ici 0)) (hYp : ∀ u ∈ Ici (0 : ℝ), 0 < Y u)
    (hY : ∀ u ∈ Ici (0 : ℝ), Y u = fNq (N : ℕ∞) p q u +
      Real.sqrt ε * Muon.Foundations.oneSidedConv (fun v => Real.sqrt (Y v)) (mixG w c) u) :
    dimClockI Y T ε ≤ Cpq p q * D * Real.log (τ * (N : ℝ) ^ q / D) + 2 * JN N p q
        + 3 * Real.sqrt (ε * ((N : ℝ) ^ q) ^ 2) + 6 * (Cpq p q * D * τ⁻¹) ∧
    ∀ H : ℝ, 0 ≤ H → H ≤ τ * (N : ℝ) ^ q - D →
      Cpq p q * (1 + H / D) ^ (-(1 : ℝ)) ≤ Real.sqrt ε →
      dimClockI Y T ε ≤ Cpq p q * D * Real.log (1 + H / D) + Real.sqrt ε * H := by
  have hN1 : 1 ≤ N := by omega
  have hNr : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1
  have hNpos : (0 : ℝ) < (N : ℝ) := by linarith
  set Nq : ℝ := (N : ℝ) ^ q with hNq_def
  have hNq1 : 1 ≤ Nq := Real.one_le_rpow hNr hq.le
  have hNq : 0 < Nq := by linarith
  have hDpos : 0 < D := by linarith
  have hTpos : 0 < T := by linarith
  have hC := pw_Cpq_pos hp hq
  set C : ℝ := Cpq p q with hC_def
  have hs : 0 < Real.sqrt ε := Real.sqrt_pos.2 hε
  obtain ⟨hε8, hεC⟩ := pw_eps_facts ε hεT
  obtain ⟨aa, bb, hfa, haa, hF, hbb⟩ : ∃ aa bb : Fin N → ℝ,
      (∀ u, fNq (N : ℕ∞) p q u = mixF aa bb u) ∧ (∀ i, 0 ≤ aa i) ∧ 1 / 2 ≤ ∑ i, aa i ∧
      ∀ i, 2 * (N : ℝ) ^ (-q) ≤ bb i := by
    obtain ⟨h1, h2, h3⟩ := fz_ab N hN1 p q hq
    exact ⟨_, _, fz_fNq_eq N p q, h1, h2, h3⟩
  have hbmin : 0 < 2 * (N : ℝ) ^ (-q) := by positivity
  have hF0 : 0 < ∑ i, aa i := by linarith
  have hεF : ε < (∑ i, aa i) / T := by
    calc ε < 1 / (8 * T) := hε8
      _ ≤ (1 / 2) / T := by
        rw [div_le_div_iff₀ (by positivity) hTpos]; nlinarith
      _ ≤ (∑ i, aa i) / T := div_le_div_of_nonneg_right hF hTpos.le
  have hY' : ∀ u ∈ Ici (0 : ℝ), Y u = mixF aa bb u +
      Real.sqrt ε * Muon.Foundations.oneSidedConv (fun v => Real.sqrt (Y v)) (mixG w c) u := by
    intro u hu; rw [hY u hu, hfa]
  set u0 : ℝ := τ * Nq - D with hu0_def
  have hu0pos : 0 < u0 := by rw [hu0_def]; linarith
  set hfun : ℝ → ℝ := fun u => C * (1 + u / D) ^ (-(1 : ℝ)) with hfun_def
  set wfun : ℝ → ℝ := fun _ => 0 with hwfun_def
  have hpos1 : ∀ u ∈ Icc (0 : ℝ) u0, 0 < 1 + u / D := fun u hu => by
    have := div_nonneg hu.1 hDpos.le; linarith
  have hhc : ContinuousOn hfun (Icc 0 u0) := by
    rw [hfun_def]
    exact continuousOn_const.mul (ContinuousOn.rpow_const (by fun_prop)
      (fun u hu => Or.inl (hpos1 u hu).ne'))
  have hwc : ContinuousOn wfun (Icc 0 u0) := continuousOn_const
  have hh0 : ∀ u ∈ Icc (0 : ℝ) u0, 0 ≤ hfun u := fun u hu => by
    rw [hfun_def]; have := hpos1 u hu; positivity
  have hw0 : ∀ u ∈ Icc (0 : ℝ) u0, 0 ≤ wfun u := fun u _ => le_rfl
  have hfh : ∀ u ∈ Icc (0 : ℝ) u0, mixF aa bb u ≤ hfun u ^ 2 := by
    intro u hu
    rw [← hfa]
    refine (fz_fNq_le_h hp hq hD N hu.1).trans ?_
    have hb1' : 1 ≤ 1 + u / D := by have := div_nonneg hu.1 hDpos.le; linarith
    have h2 : (1 + u / D) ^ (-rq p q) ≤ (1 + u / D) ^ (-(1 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le hb1' (by linarith)
    have h3 : 0 ≤ (1 + u / D) ^ (-rq p q) := Real.rpow_nonneg (by linarith) _
    rw [hfun_def]
    exact pow_le_pow_left₀ (mul_nonneg hC.le h3) (mul_le_mul_of_nonneg_left h2 hC.le) 2
  have henv1 : ∀ u ∈ Icc (0 : ℝ) u0, Muon.Foundations.oneSidedConv hfun (mixG w c) u ≤
      2 * hfun u + wfun u ^ 2 / Real.sqrt ε := by
    intro u hu
    have h0 : wfun u ^ 2 / Real.sqrt ε = 0 := by simp [hwfun_def]
    rw [h0, add_zero]
    exact hconv u hu
  have henv2 : ∀ u ∈ Icc (0 : ℝ) u0, Muon.Foundations.oneSidedConv wfun (mixG w c) u ≤ 2 * wfun u := by
    intro u hu
    simp [hwfun_def, Muon.Foundations.oneSidedConv]
  have T1 := lem_app_phase_twophase_i aa bb w c _ hbmin haa hF0 hbb hw hw1 hc hT hε hεF hu0pos hYc hYp hY'
    hhc hh0 hwc hw0 hfh henv1 henv2
  have T2 := lem_app_phase_twophase_ii aa bb w c _ hbmin haa hF0 hbb hw hw1 hc hT hε hεF hu0pos hYc hYp hY'
    hhc hh0 hwc hw0 hfh henv1 henv2
  have T3 := lem_app_phase_twophase_iii aa bb w c _ hbmin haa hF0 hbb hw hw1 hc hT hε hεF hu0pos hYc hYp hY'
    hhc hh0 hwc hw0 hfh henv1 henv2
  have hYs : ContinuousOn (fun v => Real.sqrt (Y v)) (Ici 0) := hYc.sqrt
  have hII_Y : ∀ t ∈ Icc (0 : ℝ) u0, IntervalIntegrable (fun v => Real.sqrt (Y v)) volume 0 t := by
    intro t ht
    exact ContinuousOn.intervalIntegrable_of_Icc ht.1
      (hYs.mono fun x hx => Set.mem_Ici.2 hx.1)
  have hII_h : ∀ t ∈ Icc (0 : ℝ) u0, IntervalIntegrable hfun volume 0 t := by
    intro t ht
    exact ContinuousOn.intervalIntegrable_of_Icc ht.1 (hhc.mono (Icc_subset_Icc le_rfl ht.2))
  have hbound : ∀ t ∈ Icc (0 : ℝ) u0, ∫ v in (0 : ℝ)..t, Real.sqrt (Y v) ≤
      C * D * Real.log (1 + t / D) + Real.sqrt ε * t := by
    intro t ht
    have h1 : ∫ v in (0 : ℝ)..t, Real.sqrt (Y v) ≤
        ∫ v in (0 : ℝ)..t, (hfun v + Real.sqrt ε) := by
      refine intervalIntegral.integral_mono_on ht.1 (hII_Y t ht)
        ((hII_h t ht).add intervalIntegrable_const) (fun v hv => ?_)
      have hv' : v ∈ Icc (0 : ℝ) u0 := ⟨hv.1, hv.2.trans ht.2⟩
      have := (T1 v hv').1
      have hw0v : wfun v = 0 := rfl
      have hnn : 0 ≤ hfun v + Real.sqrt ε := by linarith [hh0 v hv']
      calc Real.sqrt (Y v) ≤ Real.sqrt ((hfun v + wfun v + Real.sqrt ε) ^ 2) := Real.sqrt_le_sqrt this
        _ = hfun v + Real.sqrt ε := by rw [hw0v, add_zero]; exact Real.sqrt_sq hnn
    have h2 : ∫ v in (0 : ℝ)..t, (hfun v + Real.sqrt ε) =
        (∫ v in (0 : ℝ)..t, hfun v) + Real.sqrt ε * t := by
      rw [intervalIntegral.integral_add (hII_h t ht) intervalIntegrable_const]
      simp
      ring
    have h3 : ∫ v in (0 : ℝ)..t, hfun v = C * D * Ir 1 (t / D) := uu_int_h hDpos
    have h4 : Ir 1 (t / D) = Real.log (1 + t / D) := un_Ir_one (div_nonneg ht.1 hDpos.le)
    rw [h4] at h3
    linarith
  refine ⟨?_, ?_⟩
  swap
  · intro H hH0 hHu hhw
    have hHm : H ∈ Icc (0 : ℝ) u0 := ⟨hH0, hHu⟩
    have hhw' : hfun H + wfun H ≤ Real.sqrt ε := by
      have : wfun H = 0 := rfl
      rw [this, add_zero]; exact hhw
    have hfhH := T2 H hHm hhw'
    unfold dimClockI
    have hû0 : 0 ≤ (firstHit Y (T * ε)).toReal := ENNReal.toReal_nonneg
    have hûH : (firstHit Y (T * ε)).toReal ≤ H := by
      have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hfhH
      rwa [ENNReal.toReal_ofReal hH0] at this
    have hmono : ∫ v in (0 : ℝ)..(firstHit Y (T * ε)).toReal, Real.sqrt (Y v) ≤
        ∫ v in (0 : ℝ)..H, Real.sqrt (Y v) :=
      intervalIntegral.integral_mono_interval le_rfl hû0 hûH
        (Filter.Eventually.of_forall fun x => Real.sqrt_nonneg (Y x)) (hII_Y H hHm)
    exact hmono.trans (hbound H hHm)
  · obtain ⟨-, -, û', hfirst', hû'pos, -⟩ := lem_app_phase_mixture aa bb w c _ hbmin haa hF0 hbb hw
      hw1 hc hT hε hεF rfl rfl hYc hYp hY'
    obtain ⟨û, hû, hI, hJ, hD'⟩ := T3
    have hû0 : 0 < û := by
      have hpos : 0 < ENNReal.ofReal û := by rw [← hû, hfirst']; exact ENNReal.ofReal_pos.2 hû'pos
      exact ENNReal.ofReal_pos.1 hpos
    have hdim : dimClockI Y T ε = ∫ u in (0 : ℝ)..û, Real.sqrt (Y u) := by
      unfold dimClockI; rw [hû, ENNReal.toReal_ofReal hû0.le]
    rw [hdim]
    have hu0m : u0 ∈ Icc (0 : ℝ) u0 := ⟨hu0pos.le, le_rfl⟩
    have hb2 : 2 / (2 * (N : ℝ) ^ (-q)) = Nq := by
      rw [Real.rpow_neg hNpos.le, hNq_def]; field_simp
    have hb4 : 4 / (2 * (N : ℝ) ^ (-q)) = 2 * Nq := by
      rw [Real.rpow_neg hNpos.le, hNq_def]; field_simp; ring
    set X : ℝ := hfun u0 + wfun u0 with hX_def
    have hX0 : 0 ≤ X := add_nonneg (hh0 u0 hu0m) (hw0 u0 hu0m)
    set sN : ℝ := Nq * Real.sqrt ε with hsN_def
    have hsN0 : 0 ≤ sN := by positivity
    have hJint := fz_mx_sqrt_integrable aa bb _ hbmin haa hbb
    have hJNeq : JN N p q = ∫ u in Ioi (0 : ℝ), Real.sqrt (mixF aa bb u) := by
      unfold JN; congr 1; funext u; rw [hfa]
    have hsplit := fz_split hJint hu0pos.le
    have hJt0 : 0 ≤ ∫ u in Ioi u0, Real.sqrt (mixF aa bb u) :=
      setIntegral_nonneg measurableSet_Ioi (fun _ _ => Real.sqrt_nonneg _)
    have hJn0 : 0 ≤ ∫ u in (0 : ℝ)..u0, Real.sqrt (mixF aa bb u) :=
      intervalIntegral.integral_nonneg hu0pos.le (fun _ _ => Real.sqrt_nonneg _)
    have hJtail : ∫ u in Ioi u0, Real.sqrt (mixF aa bb u) ≤ JN N p q := by
      rw [hJNeq, hsplit]; linarith
    have hJN0 : 0 ≤ JN N p q := by linarith
    have hJb : restartJ (mixF aa bb) (2 * (N : ℝ) ^ (-q)) ε
        (Muon.Foundations.oneSidedConv (fun v => Real.sqrt (Y v)) (mixG w c) u0) u0 ≤
        JN N p q + sN + Nq * X := by
      refine hJ.trans ?_
      rw [hb2]
      have : Nq * Real.sqrt ε * (1 + (hfun u0 + wfun u0) / Real.sqrt ε) = sN + Nq * X := by
        rw [hsN_def, hX_def]; field_simp
      linarith
    have hDb : restartD (2 * (N : ℝ) ^ (-q)) ε (Y u0) ≤ 2 * (Nq * X) := by
      refine hD'.trans ?_
      rw [hb4]
      have hlog : Real.log (1 + (hfun u0 + wfun u0) / Real.sqrt ε) ≤ (hfun u0 + wfun u0) / Real.sqrt ε := by
        have := Real.log_le_sub_one_of_pos (show 0 < 1 + (hfun u0 + wfun u0) / Real.sqrt ε by
          have := div_nonneg hX0 hs.le; linarith)
        linarith
      calc 2 * Nq * Real.sqrt ε * Real.log (1 + (hfun u0 + wfun u0) / Real.sqrt ε)
          ≤ 2 * Nq * Real.sqrt ε * ((hfun u0 + wfun u0) / Real.sqrt ε) :=
            mul_le_mul_of_nonneg_left hlog (by positivity)
        _ = 2 * (Nq * X) := by rw [hX_def]; field_simp
    have hJb0 : 0 ≤ JN N p q + sN + Nq * X := by
      have : 0 ≤ Nq * X := by positivity
      linarith
    have hsq : (Real.sqrt (restartJ (mixF aa bb) (2 * (N : ℝ) ^ (-q)) ε
          (Muon.Foundations.oneSidedConv (fun v => Real.sqrt (Y v)) (mixG w c) u0) u0)
        + Real.sqrt (restartD (2 * (N : ℝ) ^ (-q)) ε (Y u0))) ^ 2 ≤
        2 * (JN N p q + sN + Nq * X) + 2 * (2 * (Nq * X)) :=
      uu_sqrt_sq_le hJb hDb hJb0 (by positivity)
    have hfirst := hbound u0 hu0m
    have hDu0 : D + u0 = τ * Nq := by rw [hu0_def]; ring
    have h1u : 1 + u0 / D = τ * Nq / D := by rw [hu0_def]; field_simp; ring
    rw [h1u] at hfirst
    have hsu0 : Real.sqrt ε * u0 ≤ τ * sN := by
      rw [hsN_def, hu0_def]
      nlinarith only [hs, hNq, hDpos]
    have hXi : Nq * X = C * D * τ⁻¹ := by
      have hw00 : wfun u0 = 0 := rfl
      rw [hX_def, hw00, add_zero, hfun_def]
      show Nq * (C * (1 + u0 / D) ^ (-(1 : ℝ))) = C * D * τ⁻¹
      rw [h1u, Real.rpow_neg_one]
      field_simp
    have hsNeq : sN = Real.sqrt (ε * Nq ^ 2) := by
      rw [hsN_def, Real.sqrt_mul hε.le, Real.sqrt_sq hNq.le]; ring
    rw [← hsNeq]
    have htsN : τ * sN ≤ 1 / 2 * sN := mul_le_mul_of_nonneg_right hτ2 hsN0
    have hXN0 : 0 ≤ Nq * X := mul_nonneg hNq.le hX0
    linarith only [hI, hsq, hfirst, hsu0, hXi, htsN, hsN0, hJN0, hXN0]

/-- The convolution estimate for the critical `\SignSVD` kernel (`α = 2`, `ς = 1`). -/
private lemma uu_log_conv (N : ℕ) (hN : 1 ≤ N) (C : ℝ) (hC : 0 < C) (u : ℝ) (hu0 : 0 ≤ u)
    (hu : u ≤ Real.exp (-32) * (N : ℝ) - 1) :
    Muon.Foundations.oneSidedConv (fun w => C * (1 + w) ^ (-(1 : ℝ))) (svdKernel 2 N) u
      ≤ 2 * (C * (1 + u) ^ (-(1 : ℝ))) := by
  have h := lem_app_phase_log_iii N hN C hC u hu0
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hden : 0 < C * (1 + u) ^ (-(1 : ℝ)) := by
    have : 0 < 1 + u := by linarith
    positivity
  rw [div_le_iff₀ hden] at h
  have hH : Real.log ((N : ℝ) + 1) ≤ Hsum 1 N := lg_Hlog N hN
  have hHpos : 0 < Hsum 1 N := by have := lg_Hge1 N hN; linarith
  have hlogN : Real.log (1 + u) ≤ Real.log (N : ℝ) - 32 := by
    have h1 : 1 + u ≤ Real.exp (-32) * (N : ℝ) := by linarith
    have := Real.log_le_log (by linarith) h1
    rw [Real.log_mul (Real.exp_pos _).ne' (by linarith), Real.log_exp] at this
    linarith
  have hlogN2 : Real.log (N : ℝ) ≤ Real.log ((N : ℝ) + 1) :=
    Real.log_le_log (by linarith) (by linarith)
  have hratio : (2 * Real.log (1 + u) + 64) / Hsum 1 N ≤ 2 := by
    rw [div_le_iff₀ hHpos]; nlinarith
  calc _ ≤ (2 * Real.log (1 + u) + 64) / Hsum 1 N * (C * (1 + u) ^ (-(1 : ℝ))) := h
    _ ≤ 2 * (C * (1 + u) ^ (-(1 : ℝ))) := mul_le_mul_of_nonneg_right hratio hden.le

private lemma uu_log_main {T : ℝ} (hT : 4 ≤ T) :
    ∃ (N1 : ℕ) (K : ℝ), 0 < K ∧ ∀ (N : ℕ) (ε : ℝ) (w c : Fin N → ℝ) (Y : ℝ → ℝ),
      N1 ≤ N → 0 < ε → ε < clockEps0 3 1 T → (∀ l, 0 ≤ w l) → ∑ l, w l = 1 →
      (∀ l, 2 * (N : ℝ) ^ (-(1 : ℝ)) ≤ c l) →
      (∀ u ∈ Ici (0 : ℝ), mixG w c u = svdKernel 2 N u) →
      ContinuousOn Y (Ici 0) → (∀ u ∈ Ici (0 : ℝ), 0 < Y u) →
      (∀ u ∈ Ici (0 : ℝ), Y u = fNq (N : ℕ∞) 3 1 u +
        Real.sqrt ε * Muon.Foundations.oneSidedConv (fun v => Real.sqrt (Y v)) (mixG w c) u) →
      dimClockI Y T ε ≤ K * min (Real.log (1 / ε)) (Real.log (N : ℝ)) := by
  have hp : (1 : ℝ) < 3 := by norm_num
  have hq : (0 : ℝ) < 1 := one_pos
  have hr : rq 3 1 = 1 := by unfold rq; norm_num
  have hpq : (3 : ℝ) = 2 * 1 + 1 := by norm_num
  have hC := pw_Cpq_pos hp hq
  set C : ℝ := Cpq 3 1 with hC_def
  set τ : ℝ := Real.exp (-32) with hτ_def
  have hτ : 0 < τ := Real.exp_pos _
  have hτ2 : τ ≤ 1 / 2 := by
    have h1 : Real.exp (-32) ≤ Real.exp (-1) := Real.exp_le_exp.2 (by norm_num)
    have h2 : Real.exp (-1) = (Real.exp 1)⁻¹ := Real.exp_neg 1
    have h3 : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
    have h4 : (Real.exp 1)⁻¹ ≤ 1 / 2 := by
      rw [inv_eq_one_div, div_le_div_iff₀ (by linarith) (by norm_num)]; linarith
    linarith
  have hτ32 : τ * Real.exp 32 = 1 := by
    rw [hτ_def, ← Real.exp_add]; simp
  have haQ : 0 < aQ 1 := by unfold aQ; positivity
  set aq : ℝ := aQ 1 * 1 with haq
  set KJ : ℝ := 2 * C + 1 * Mpq 3 1 * (2 : ℝ) ^ (-(3 / 1 : ℝ)) / aQ 1 + 1 / Real.sqrt (2 * (3 - 1))
    with hKJ
  set lam0 : ℝ := |Real.log (C / τ)| with hlam0
  have hNt : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hlogt : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop := Real.tendsto_log_atTop.comp hNt
  obtain ⟨N1, hN1⟩ := eventually_atTop.1 ((hNt.eventually_gt_atTop (Real.exp 32)).and
    ((hlogt.eventually_ge_atTop (2 * lam0)).and (eventually_ge_atTop 4)))
  set KA : ℝ := C * |Real.log C| + C / 2 + C with hKA
  have hKA0 : 0 < KA := by
    have := abs_nonneg (Real.log C)
    rw [hKA]; positivity
  set KB : ℝ := C + 2 * |aq| + 2 * |KJ| + 9 * (C * τ⁻¹) with hKB
  have hKB0 : 0 < KB := by
    have := abs_nonneg aq; have := abs_nonneg KJ
    have : 0 < C * τ⁻¹ := by positivity
    rw [hKB]; positivity
  refine ⟨N1, max KA (max (KA * (2 + 2 * lam0)) KB) + 1, by positivity, ?_⟩
  intro N ε w c Y hN hε hε0 hw hw1 hc hker hYc hYp hY
  obtain ⟨hNe, hlog2, hN4⟩ := hN1 N hN
  have hN1' : 1 ≤ N := by omega
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN1'
  have hNpos : (0 : ℝ) < N := by linarith
  set ℓ : ℝ := Real.log (N : ℝ) with hℓ
  have hlog4 : (1 : ℝ) < Real.log 4 := by
    rw [show (4 : ℝ) = 2 * 2 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
    have := Real.log_two_gt_d9; linarith
  have hℓ1 : 1 ≤ ℓ := by
    have h4 : (4 : ℝ) ≤ N := by exact_mod_cast hN4
    have h5 : Real.log 4 ≤ ℓ := Real.log_le_log (by norm_num) h4
    linarith
  have hlam0 : 0 ≤ lam0 := abs_nonneg _
  have hNτ : 1 < τ * N := by
    have := mul_lt_mul_of_pos_left hNe hτ
    rw [mul_comm] at this
    linarith [hτ32, mul_comm τ (Real.exp 32)]
  have hs : 0 < Real.sqrt ε := Real.sqrt_pos.2 hε
  obtain ⟨hε8, hεC⟩ := pw_eps_facts ε hε0
  have hsC : Real.sqrt ε ≤ C := by
    have : Real.sqrt ε ≤ Real.sqrt (C ^ 2) := Real.sqrt_le_sqrt hεC.le
    rwa [Real.sqrt_sq hC.le] at this
  have hε14 : ε < 1 / 4 := pw_eps_lt_quarter hε0
  have hΛ : Real.log (1 / ε) = - Real.log ε := by rw [one_div, Real.log_inv]
  have hΛ1 : 1 ≤ Real.log (1 / ε) := by
    rw [hΛ]
    have h1 : Real.log ε < Real.log (1 / 4) := Real.log_lt_log hε hε14
    rw [one_div, Real.log_inv] at h1
    linarith only [h1, hlog4]
  have hlogy : Real.log (ε * (N : ℝ) ^ 2) = Real.log ε + 2 * ℓ := by
    rw [Real.log_mul hε.ne' (by positivity), Real.log_pow]; push_cast; ring
  have hsqrt : Real.sqrt (ε * (N : ℝ) ^ 2) = Real.sqrt ε * N := by
    rw [Real.sqrt_mul hε.le, Real.sqrt_sq hNpos.le]
  have hconv : ∀ u ∈ Icc (0 : ℝ) (τ * (N : ℝ) ^ (1 : ℝ) - 1),
      Muon.Foundations.oneSidedConv (fun v => C * (1 + v / 1) ^ (-(1 : ℝ))) (mixG w c) u
        ≤ 2 * (C * (1 + u / 1) ^ (-(1 : ℝ))) := by
    intro u hu
    rw [Real.rpow_one] at hu
    have hu0 : 0 ≤ u := hu.1
    have h1 := uu_log_conv N hN1' C hC u hu0 hu.2
    have hcong := fz2_conv_congr (fun w => C * (1 + w) ^ (-(1 : ℝ))) (mixG w c) (svdKernel 2 N) hker hu0
    simp only [div_one]
    rw [hcong]; exact h1
  have core := uu_core0 (p := 3) (q := 1) (T := T) (D := 1) (τ := τ) (ε := ε) hp hq hT le_rfl hτ hτ2
    hε hε0 hN4 (by rw [Real.rpow_one]; exact hNτ) hr.ge w c hw hw1 hc hconv Y hYc hYp hY
  obtain ⟨hG, hX⟩ := core
  have hJN : JN N 3 1 ≤ |aq| * ℓ + |KJ| := by
    have h := (abs_le.1 (lem_app_phase_forcing_integrals_i hq hpq N hN1')).2
    have h2 : aq * ℓ ≤ |aq| * ℓ := mul_le_mul_of_nonneg_right (le_abs_self _) (by linarith)
    have h3 : JN N 3 1 - aQ 1 * 1 * ℓ ≤ KJ := h
    have h4 : KJ ≤ |KJ| := le_abs_self _
    have h5 : aQ 1 * 1 * ℓ = aq * ℓ := by rw [haq]
    linarith
  have hmin0 : 0 ≤ min (Real.log (1 / ε)) ℓ := le_min (by linarith only [hΛ1]) (by linarith only [hℓ1])
  by_cases hcase : C ≤ Real.sqrt ε * (τ * N)
  · -- the window case
    have hCs : 1 ≤ C / Real.sqrt ε := by rw [le_div_iff₀ hs]; linarith only [hsC]
    set H : ℝ := C / Real.sqrt ε - 1 with hH
    have hH0 : 0 ≤ H := by linarith only [hCs]
    have hHu : H ≤ τ * (N : ℝ) ^ (1 : ℝ) - 1 := by
      rw [Real.rpow_one, hH]
      have : C / Real.sqrt ε ≤ τ * N := by rw [div_le_iff₀ hs]; linarith only [hcase]
      linarith only [this]
    have e1 : 1 + H / 1 = C / Real.sqrt ε := by rw [hH]; ring
    have hhw : C * (1 + H / 1) ^ (-(1 : ℝ)) ≤ Real.sqrt ε := by
      rw [e1, Real.rpow_neg_one, inv_div]
      have : C * (Real.sqrt ε / C) = Real.sqrt ε := by field_simp
      linarith only [this]
    have hXH := hX H hH0 hHu hhw
    rw [e1, Real.log_div hC.ne' hs.ne', Real.log_sqrt hε.le] at hXH
    have e2 : Real.sqrt ε * H = C - Real.sqrt ε := by rw [hH]; field_simp
    rw [e2] at hXH
    have hlogC : C * Real.log C ≤ C * |Real.log C| := mul_le_mul_of_nonneg_left (le_abs_self _) hC.le
    have hb1 : C * |Real.log C| ≤ C * |Real.log C| * Real.log (1 / ε) :=
      le_mul_of_one_le_right (by positivity) hΛ1
    have hb2 : C ≤ C * Real.log (1 / ε) := le_mul_of_one_le_right hC.le hΛ1
    have hIA : dimClockI Y T ε ≤ KA * Real.log (1 / ε) := by
      have hKAΛ : KA * Real.log (1 / ε) = C * |Real.log C| * Real.log (1 / ε)
          + C / 2 * Real.log (1 / ε) + C * Real.log (1 / ε) := by rw [hKA]; ring
      have hlogε : Real.log ε = - Real.log (1 / ε) := by rw [hΛ]; ring
      rw [hlogε] at hXH
      nlinarith only [hXH, hlogC, hb1, hb2, hKAΛ, hs, hΛ1, hC]
    have hy : (C / τ) ^ 2 ≤ ε * (N : ℝ) ^ 2 := by
      have h1 : C / τ ≤ Real.sqrt ε * N := by
        rw [div_le_iff₀ hτ]; linarith only [hcase]
      have h0 : 0 ≤ C / τ := by positivity
      have := pow_le_pow_left₀ h0 h1 2
      rw [mul_pow, Real.sq_sqrt hε.le] at this
      exact this
    have hΛle : Real.log (1 / ε) ≤ (2 + 2 * lam0) * ℓ := by
      have h1 : Real.log ((C / τ) ^ 2) ≤ Real.log (ε * (N : ℝ) ^ 2) :=
        Real.log_le_log (by positivity) hy
      rw [Real.log_pow, hlogy] at h1
      have h2 : -lam0 ≤ Real.log (C / τ) := neg_abs_le _
      push_cast at h1
      rw [hΛ]
      nlinarith only [h1, h2, hℓ1, hlam0]
    have h2 : dimClockI Y T ε ≤ (KA * (2 + 2 * lam0)) * ℓ :=
      hIA.trans (by nlinarith only [mul_le_mul_of_nonneg_left hΛle hKA0.le])
    have := uu_minfin hIA h2 (by linarith only [hΛ1]) (by linarith only [hℓ1]) hKA0.le (by positivity)
    refine this.trans ?_
    nlinarith only [mul_le_mul_of_nonneg_right (show max KA (KA * (2 + 2 * lam0)) ≤
      max KA (max (KA * (2 + 2 * lam0)) KB) + 1 by
        have := le_max_left KA (max (KA * (2 + 2 * lam0)) KB)
        have h5 := le_max_left (KA * (2 + 2 * lam0)) KB
        have : max KA (KA * (2 + 2 * lam0)) ≤ max KA (max (KA * (2 + 2 * lam0)) KB) :=
          max_le_max le_rfl h5
        linarith only [this]) hmin0, hmin0]
  · -- generic case
    push_neg at hcase
    rw [Real.rpow_one] at hG
    simp only [div_one, mul_one] at hG
    rw [hsqrt] at hG
    have hlogτ : Real.log (τ * N) ≤ ℓ := by
      apply Real.log_le_log (by positivity)
      nlinarith only [hτ2, hNpos]
    have hτi : 0 < τ⁻¹ := inv_pos.2 hτ
    have hsN : Real.sqrt ε * N ≤ C * τ⁻¹ := by
      have : Real.sqrt ε * (τ * N) ≤ C := hcase.le
      rw [← div_eq_mul_inv, le_div_iff₀ hτ]; linarith only [this]
    have hC1 : C * Real.log (τ * N) ≤ C * ℓ := mul_le_mul_of_nonneg_left hlogτ hC.le
    have hk1 : |KJ| ≤ |KJ| * ℓ := le_mul_of_one_le_right (abs_nonneg _) hℓ1
    have hk2 : C * τ⁻¹ ≤ C * τ⁻¹ * ℓ := le_mul_of_one_le_right (by positivity) hℓ1
    have hIB : dimClockI Y T ε ≤ KB * ℓ := by
      have hKBℓ : KB * ℓ = C * ℓ + 2 * |aq| * ℓ + 2 * |KJ| * ℓ + 9 * (C * τ⁻¹ * ℓ) := by
        rw [hKB]; ring
      rw [hKBℓ]
      nlinarith only [hG, hJN, hsN, hC1, hk1, hk2, hℓ1]
    have hΛge : ℓ ≤ Real.log (1 / ε) := by
      have hy : ε * (N : ℝ) ^ 2 < (C / τ) ^ 2 := by
        have h1 : Real.sqrt ε * N < C / τ := by
          rw [lt_div_iff₀ hτ]; linarith only [hcase]
        have h0 : 0 ≤ Real.sqrt ε * N := by positivity
        have := pow_lt_pow_left₀ h1 h0 (by norm_num : (2 : ℕ) ≠ 0)
        rw [mul_pow, Real.sq_sqrt hε.le] at this
        exact this
      have h1 : Real.log (ε * (N : ℝ) ^ 2) < Real.log ((C / τ) ^ 2) :=
        Real.log_lt_log (by positivity) hy
      rw [Real.log_pow, hlogy] at h1
      have h2 : Real.log (C / τ) ≤ lam0 := le_abs_self _
      push_cast at h1
      rw [hΛ]
      nlinarith only [h1, h2, hlog2]
    rw [min_eq_right hΛge]
    refine hIB.trans ?_
    have hKm : KB ≤ max KA (max (KA * (2 + 2 * lam0)) KB) + 1 := by
      have := le_max_right (KA * (2 + 2 * lam0)) KB
      have := le_max_right KA (max (KA * (2 + 2 * lam0)) KB)
      linarith only [this, ‹KB ≤ max (KA * (2 + 2 * lam0)) KB›]
    nlinarith only [mul_le_mul_of_nonneg_right hKm (show 0 ≤ ℓ by linarith only [hℓ1]), hℓ1]

/-- `α = 2`, `ς = 1`: the critical logarithmic case. -/
private lemma uu_up_svd_eq2_eq1 (T : ℝ) (hT : 4 ≤ T) :
    ∃ (N0 : ℕ) (ε0 cp : ℝ), 0 < ε0 ∧ 0 < cp ∧
      ∀ (N B : ℕ) (ε : ℝ) (m : RowModel (Fin N)) (Q : ℝ → ℝ),
        N0 ≤ N → N ≤ B → 0 < ε → ε < ε0 →
        IsMatchedModel (phaseKindArrays 2 1 N B .svd) m ε → IsVolterraSol m Q →
        phaseClockI Q (phaseKindT0 2 N B .svd) T ε ≤ cp * phaseUpsilon 2 1 N ε .svd := by
  have hp : (1 : ℝ) < 2 + 1 := by norm_num
  have e3 : (2 : ℝ) + 1 = 3 := by norm_num
  have e1 : (2 : ℝ) / 2 = 1 := by norm_num
  obtain ⟨N1, K, hK, hmain⟩ := uu_log_main hT
  refine ⟨max 1 N1, clockEps0 3 1 T, K, pw_clockEps0_pos (by norm_num) one_pos hT, hK, ?_⟩
  intro N B ε m Q hN hNB hε hε0 hm hQ
  have hN1 : 1 ≤ N := (le_max_left _ _).trans hN
  have hNN : N1 ≤ N := (le_max_right _ _).trans hN
  obtain ⟨mG, QG, hmG, hQG⟩ := un_pair_svd 2 1 N B (by norm_num) hp hN1 hNB ε hε
  obtain ⟨w, c, hw, hw1, hc, hker, hYc, hYp, hY⟩ :=
    fz2_svd_model 2 1 N B (by norm_num) hp hN1 hNB ε hε m mG hm hmG Q QG hQ hQG
  rw [e1] at hc
  simp only [e3, e1] at hY
  have := hmain N ε w c _ hNN hε hε0 hw hw1 hc hker hYc hYp hY
  have hR : phaseKindR 2 1 .svd = 1 := by unfold phaseKindR phaseKindQ rq; norm_num
  unfold phaseClockI phaseUpsilon
  rw [if_neg (by rw [hR]; norm_num), if_pos hR]
  exact this

private lemma uu_up_svd_ge2 (α ς T : ℝ) (hα : 0 < α) (hp : 1 < α + ς) (hT : 4 ≤ T)
    (hr1 : 1 ≤ phaseKindR α ς .svd) (h2 : 2 ≤ α) :
    ∃ (N0 : ℕ) (ε0 cp : ℝ), 0 < ε0 ∧ 0 < cp ∧
      ∀ (N B : ℕ) (ε : ℝ) (m : RowModel (Fin N)) (Q : ℝ → ℝ),
        N0 ≤ N → N ≤ B → 0 < ε → ε < ε0 →
        IsMatchedModel (phaseKindArrays α ς N B .svd) m ε → IsVolterraSol m Q →
        phaseClockI Q (phaseKindT0 α N B .svd) T ε ≤ cp * phaseUpsilon α ς N ε .svd := by
  rcases h2.lt_or_eq with h | h
  · exact uu_up_svd_gt2 α ς T hα hp hT hr1 h
  · subst h
    have hς : 1 ≤ ς := by
      have h1 : 1 ≤ rq (2 + ς) (2 / 2) := hr1
      unfold rq at h1
      rw [le_div_iff₀ (by norm_num)] at h1
      linarith
    rcases hς.lt_or_eq with h | h
    · exact uu_up_svd_eq2_gt ς T hp hT h
    · subst h
      exact uu_up_svd_eq2_eq1 T hT

/-! ## Declarations of record -/

/-- Label `thm:app-phase-unified`, part (i): the first hit is attained and the clock integral is bounded
below by `Υ_j`, for every `j`. Snapshot `cr-2026-10-23`. Statement (verbatim, `sections/07-phase-comparison/section.tex`):

\begin{theorem}[Unified clock]\label{thm:app-phase-unified}
Fix $\alpha>0$, $\texp$ with $\alpha+\texp>1$, $T\ge4$ and
$j\in\{\text{s-SVD},\text{s-SGD}\}$.
\begin{enumerate}[label=(\roman*)]
\item There are $N_0$, $\epsilon_0>0$ and $c_->0$ such that for all $N\ge N_0$,
$B\ge N$ and $0<\epsilon<\epsilon_0$ the first hit $\hat u_j$ is attained and
$\mathsf I_j\ge c_-\Upsilon_j(N,\epsilon)$.
\item If $(\alpha,\texp,j)\in\mathcal U$, there are $N_0$, $\epsilon_0>0$ and $c_+$
such that for all $N\ge N_0$, $B\ge N$ and $0<\epsilon<\epsilon_0$,
$\mathsf I_j\le c_+\Upsilon_j(N,\epsilon)$.
\end{enumerate}
In particular, for $(\alpha,\texp,j)\in\mathcal U$,
$t^j_{T\epsilon}\asymp\mathcal S_jT_0^j\,\epsilon^{-1/2}\,\Upsilon_j(N,\epsilon)$ for all
$N\ge N_0$, $B\ge N$ and $0<\epsilon<\epsilon_0$.
\end{theorem} -/
theorem thm_app_phase_unified_i (α ς T : ℝ) (hα : 0 < α) (hp : 1 < α + ς) (hT : 4 ≤ T)
    (j : PhaseKind) :
    ∃ (N0 : ℕ) (ε0 cm : ℝ), 0 < ε0 ∧ 0 < cm ∧
      ∀ (N B : ℕ) (ε : ℝ) (m : RowModel (Fin N)) (Q : ℝ → ℝ),
        N0 ≤ N → N ≤ B → 0 < ε → ε < ε0 →
        IsMatchedModel (phaseKindArrays α ς N B j) m ε → IsVolterraSol m Q →
        dimHit Q (phaseKindT0 α N B j) T ε ≠ ⊤ ∧
          cm * phaseUpsilon α ς N ε j ≤ phaseClockI Q (phaseKindT0 α N B j) T ε := by
  have hq := un_q_pos α hα j
  have hε0pos := un_clockEps0_pos hp hq hT
  have key : ∀ (N B : ℕ) (ε : ℝ) (m : RowModel (Fin N)) (Q : ℝ → ℝ), 1 ≤ N → N ≤ B → 0 < ε →
      ε < clockEps0 (α + ς) (phaseKindQ α j) T →
      IsMatchedModel (phaseKindArrays α ς N B j) m ε → IsVolterraSol m Q →
      ContinuousOn (fun u => Q (phaseKindT0 α N B j * u)) (Ici 0) ∧
      (∀ u ∈ Ici (0 : ℝ), fNq (N : ℕ∞) (α + ς) (phaseKindQ α j) u ≤ Q (phaseKindT0 α N B j * u)) ∧
      ∃ û : ℝ, 0 < û ∧ Q (phaseKindT0 α N B j * û) = T * ε ∧
        firstHit (fun u => Q (phaseKindT0 α N B j * u)) (T * ε) = ENNReal.ofReal û := by
    intro N B ε m Q hN hNB hε hε0 hm hQ
    exact un_hit_j α ς T j N B hα hp hT hN hNB ε hε (un_eps_facts hε0).1 m Q hm hQ
  rcases lt_trichotomy (rq (α + ς) (phaseKindQ α j)) 1 with hr | hr | hr
  · obtain ⟨N0, cm, hN0, hcm, h⟩ := un_lower_lt (T := T) hp hq hT hr
    refine ⟨N0, clockEps0 (α + ς) (phaseKindQ α j) T, cm, hε0pos, hcm, ?_⟩
    intro N B ε m Q hN hNB hε hε0 hm hQ
    obtain ⟨hYc, hYf, û, hû, hYû, hhit⟩ := key N B ε m Q (by omega) hNB hε hε0 hm hQ
    refine ⟨?_, ?_⟩
    · show firstHit _ _ ≠ ⊤
      rw [hhit]; exact ENNReal.ofReal_ne_top
    · rw [un_I_eq Q _ T ε û hû hhit]
      have := h N ε _ û hN hε hε0 hYc hYf hhit hû hYû
      have hr' : phaseKindR α ς j < 1 := hr
      unfold phaseUpsilon
      rw [if_pos hr']
      exact this
  · obtain ⟨N0, cm, hN0, hcm, h⟩ := un_lower_eq (T := T) hp hq hT hr
    refine ⟨N0, clockEps0 (α + ς) (phaseKindQ α j) T, cm, hε0pos, hcm, ?_⟩
    intro N B ε m Q hN hNB hε hε0 hm hQ
    obtain ⟨hYc, hYf, û, hû, hYû, hhit⟩ := key N B ε m Q (by omega) hNB hε hε0 hm hQ
    refine ⟨?_, ?_⟩
    · show firstHit _ _ ≠ ⊤
      rw [hhit]; exact ENNReal.ofReal_ne_top
    · rw [un_I_eq Q _ T ε û hû hhit]
      have := h N ε _ û hN hε hε0 hYc hYf hhit hû hYû
      have hr' : phaseKindR α ς j = 1 := hr
      unfold phaseUpsilon
      rw [if_neg (by rw [hr']; norm_num), if_pos hr']
      exact this
  · obtain ⟨N0, cm, hN0, hcm, h⟩ := un_lower_gt (T := T) hp hq hT hr
    refine ⟨N0, clockEps0 (α + ς) (phaseKindQ α j) T, cm, hε0pos, hcm, ?_⟩
    intro N B ε m Q hN hNB hε hε0 hm hQ
    obtain ⟨hYc, hYf, û, hû, hYû, hhit⟩ := key N B ε m Q (by omega) hNB hε hε0 hm hQ
    refine ⟨?_, ?_⟩
    · show firstHit _ _ ≠ ⊤
      rw [hhit]; exact ENNReal.ofReal_ne_top
    · rw [un_I_eq Q _ T ε û hû hhit]
      have := h N ε _ û hN hε hε0 hYc hYf hhit hû hYû
      have hr' : 1 < phaseKindR α ς j := hr
      unfold phaseUpsilon
      rw [if_neg (by linarith), if_neg (by linarith)]
      exact this

/-- Label `thm:app-phase-unified`, part (ii): for `(α, ς, j) ∈ 𝒰`, the clock integral is bounded above
by `Υ_j`. Snapshot `cr-2026-10-23`. Statement (verbatim, `sections/07-phase-comparison/section.tex`):

\begin{theorem}[Unified clock]\label{thm:app-phase-unified}
Fix $\alpha>0$, $\texp$ with $\alpha+\texp>1$, $T\ge4$ and
$j\in\{\text{s-SVD},\text{s-SGD}\}$.
\begin{enumerate}[label=(\roman*)]
\item There are $N_0$, $\epsilon_0>0$ and $c_->0$ such that for all $N\ge N_0$,
$B\ge N$ and $0<\epsilon<\epsilon_0$ the first hit $\hat u_j$ is attained and
$\mathsf I_j\ge c_-\Upsilon_j(N,\epsilon)$.
\item If $(\alpha,\texp,j)\in\mathcal U$, there are $N_0$, $\epsilon_0>0$ and $c_+$
such that for all $N\ge N_0$, $B\ge N$ and $0<\epsilon<\epsilon_0$,
$\mathsf I_j\le c_+\Upsilon_j(N,\epsilon)$.
\end{enumerate}
In particular, for $(\alpha,\texp,j)\in\mathcal U$,
$t^j_{T\epsilon}\asymp\mathcal S_jT_0^j\,\epsilon^{-1/2}\,\Upsilon_j(N,\epsilon)$ for all
$N\ge N_0$, $B\ge N$ and $0<\epsilon<\epsilon_0$.
\end{theorem} -/
theorem thm_app_phase_unified_ii (α ς T : ℝ) (hα : 0 < α) (hp : 1 < α + ς) (hT : 4 ≤ T)
    (j : PhaseKind) (hU : phaseInU α ς j) :
    ∃ (N0 : ℕ) (ε0 cp : ℝ), 0 < ε0 ∧ 0 < cp ∧
      ∀ (N B : ℕ) (ε : ℝ) (m : RowModel (Fin N)) (Q : ℝ → ℝ),
        N0 ≤ N → N ≤ B → 0 < ε → ε < ε0 →
        IsMatchedModel (phaseKindArrays α ς N B j) m ε → IsVolterraSol m Q →
        dimHit Q (phaseKindT0 α N B j) T ε ≠ ⊤ ∧
          phaseClockI Q (phaseKindT0 α N B j) T ε ≤ cp * phaseUpsilon α ς N ε j := by
  obtain ⟨N0, ε0, cp, hε0, hcp, hmain⟩ : ∃ (N0 : ℕ) (ε0 cp : ℝ), 0 < ε0 ∧ 0 < cp ∧
      ∀ (N B : ℕ) (ε : ℝ) (m : RowModel (Fin N)) (Q : ℝ → ℝ),
        N0 ≤ N → N ≤ B → 0 < ε → ε < ε0 →
        IsMatchedModel (phaseKindArrays α ς N B j) m ε → IsVolterraSol m Q →
        phaseClockI Q (phaseKindT0 α N B j) T ε ≤ cp * phaseUpsilon α ς N ε j := by
    rcases un_upper_regimes α ς j hU with hr | ⟨rfl, h⟩ | ⟨rfl, h⟩
    · exact uu_upper_lt1 α ς T hα hp hT j hr
    · by_cases hr : phaseKindR α ς .svd < 1
      · exact uu_upper_lt1 α ς T hα hp hT .svd hr
      · have hr1 : 1 ≤ phaseKindR α ς .svd := not_lt.1 hr
        rcases h with h | h | h
        · exact uu_up_tpl_cases α ς T hα hp hT .svd hr1 (Or.inl ⟨rfl, Or.inl h⟩)
        · exact uu_up_tpl_cases α ς T hα hp hT .svd hr1 (Or.inl ⟨rfl, Or.inr h⟩)
        · exact uu_up_svd_ge2 α ς T hα hp hT hr1 h
    · by_cases hr : phaseKindR α ς .sgd < 1
      · exact uu_upper_lt1 α ς T hα hp hT .sgd hr
      · have hr1 : 1 ≤ phaseKindR α ς .sgd := not_lt.1 hr
        exact uu_up_tpl_cases α ς T hα hp hT .sgd hr1 (Or.inr ⟨rfl, h⟩)
  refine ⟨max N0 1, min ε0 (1 / (8 * T)), cp, lt_min hε0 (by positivity), hcp, ?_⟩
  intro N B ε m Q hN hNB hε hε' hm hQ
  have hN1 : 1 ≤ N := (le_max_right _ _).trans hN
  have hN0 : N0 ≤ N := (le_max_left _ _).trans hN
  have hεa : ε < ε0 := lt_of_lt_of_le hε' (min_le_left _ _)
  have hεb : ε < 1 / (8 * T) := lt_of_lt_of_le hε' (min_le_right _ _)
  refine ⟨?_, hmain N B ε m Q hN0 hNB hε hεa hm hQ⟩
  obtain ⟨-, -, û, -, -, hhit⟩ := un_hit_j α ς T j N B hα hp hT hN1 hNB ε hε hεb m Q hm hQ
  show firstHit _ _ ≠ ⊤
  rw [hhit]; exact ENNReal.ofReal_ne_top

/-- Label `thm:app-phase-unified`, the "in particular" clause: for `(α, ς, j) ∈ 𝒰`, the step time
satisfies `t^j_{Tε} ≍ 𝒮_j T_0^j ε^{-1/2} Υ_j(N, ε)`. Snapshot `cr-2026-10-23`. Statement (verbatim,
`sections/07-phase-comparison/section.tex`):

\begin{theorem}[Unified clock]\label{thm:app-phase-unified}
Fix $\alpha>0$, $\texp$ with $\alpha+\texp>1$, $T\ge4$ and
$j\in\{\text{s-SVD},\text{s-SGD}\}$.
\begin{enumerate}[label=(\roman*)]
\item There are $N_0$, $\epsilon_0>0$ and $c_->0$ such that for all $N\ge N_0$,
$B\ge N$ and $0<\epsilon<\epsilon_0$ the first hit $\hat u_j$ is attained and
$\mathsf I_j\ge c_-\Upsilon_j(N,\epsilon)$.
\item If $(\alpha,\texp,j)\in\mathcal U$, there are $N_0$, $\epsilon_0>0$ and $c_+$
such that for all $N\ge N_0$, $B\ge N$ and $0<\epsilon<\epsilon_0$,
$\mathsf I_j\le c_+\Upsilon_j(N,\epsilon)$.
\end{enumerate}
In particular, for $(\alpha,\texp,j)\in\mathcal U$,
$t^j_{T\epsilon}\asymp\mathcal S_jT_0^j\,\epsilon^{-1/2}\,\Upsilon_j(N,\epsilon)$ for all
$N\ge N_0$, $B\ge N$ and $0<\epsilon<\epsilon_0$.
\end{theorem} -/
theorem thm_app_phase_unified_iii (α ς T : ℝ) (hα : 0 < α) (hp : 1 < α + ς) (hT : 4 ≤ T)
    (j : PhaseKind) (hU : phaseInU α ς j) :
    ∃ (N0 : ℕ) (ε0 cLo cHi : ℝ), 0 < ε0 ∧ 0 < cLo ∧ cLo ≤ cHi ∧
      ∀ (N B : ℕ) (ε : ℝ) (m : RowModel (Fin N)) (Q : ℝ → ℝ),
        N0 ≤ N → N ≤ B → 0 < ε → ε < ε0 →
        IsMatchedModel (phaseKindArrays α ς N B j) m ε → IsVolterraSol m Q →
        dimHit Q (phaseKindT0 α N B j) T ε ≠ ⊤ ∧
          Sandwich cLo cHi
            (PhaseArrays.S (phaseKindArrays α ς N B j) * phaseKindT0 α N B j *
              ε ^ (-(1 / 2 : ℝ)) * phaseUpsilon α ς N ε j)
            (stepHit m Q T ε).toReal := by
  obtain ⟨N0a, ε0a, cm, hε0a, hcm, ha⟩ := thm_app_phase_unified_i α ς T hα hp hT j
  obtain ⟨N0b, ε0b, cp, hε0b, hcp, hb⟩ := thm_app_phase_unified_ii α ς T hα hp hT j hU
  refine ⟨max (max N0a N0b) 1, min ε0a (min ε0b 1), cm / 2, max cm cp / 2,
    lt_min hε0a (lt_min hε0b one_pos), half_pos hcm, by linarith [le_max_left cm cp], ?_⟩
  intro N B ε m Q hN0 hNB hε hε0 hm hQ
  have hN : 1 ≤ N := le_trans (le_max_right _ _) hN0
  have hNa : N0a ≤ N := le_trans (le_trans (le_max_left N0a N0b) (le_max_left _ _)) hN0
  have hNb : N0b ≤ N := le_trans (le_trans (le_max_right N0a N0b) (le_max_left _ _)) hN0
  have hεa : ε < ε0a := lt_of_lt_of_le hε0 (min_le_left _ _)
  have hεb : ε < ε0b := lt_of_lt_of_le hε0 (le_trans (min_le_right _ _) (min_le_left _ _))
  have hε1 : ε < 1 := lt_of_lt_of_le hε0 (le_trans (min_le_right _ _) (min_le_right _ _))
  obtain ⟨hdim, hlo⟩ := ha N B ε m Q hNa hNB hε hεa hm hQ
  obtain ⟨-, hup⟩ := hb N B ε m Q hNb hNB hε hεb hm hQ
  refine ⟨hdim, ?_⟩
  unfold Sandwich
  rw [un_step_eq α ς T hα hp (by linarith) j N B hN hNB ε hε m Q hm hQ hdim]
  obtain ⟨hSp, hT0p⟩ := un_ST_pos α ς j N B hα hp hN hNB ε hε
  have hΥ := un_Upsilon_nonneg α ς N ε j hN hε hε1
  have hpow : ε ^ (-(1 / 2 : ℝ)) = (Real.sqrt ε)⁻¹ := by
    rw [Real.rpow_neg hε.le, Real.sqrt_eq_rpow]
  have hkey : PhaseArrays.S (phaseKindArrays α ς N B j) * phaseKindT0 α N B j
      / (2 * Real.sqrt ε)
      = PhaseArrays.S (phaseKindArrays α ς N B j) * phaseKindT0 α N B j
        * ε ^ (-(1 / 2 : ℝ)) / 2 := by
    rw [hpow]; ring
  have hK : 0 ≤ PhaseArrays.S (phaseKindArrays α ς N B j) * phaseKindT0 α N B j
      * ε ^ (-(1 / 2 : ℝ)) :=
    mul_nonneg (mul_nonneg hSp.le hT0p.le) (Real.rpow_nonneg hε.le _)
  rw [hkey]
  constructor
  · have g := mul_le_mul_of_nonneg_left hlo (div_nonneg hK zero_le_two)
    nlinarith [g]
  · have g := mul_le_mul_of_nonneg_left hup (div_nonneg hK zero_le_two)
    have h2 := mul_le_mul_of_nonneg_right
      (show cp / 2 ≤ max cm cp / 2 by linarith [le_max_right cm cp]) (mul_nonneg hK hΥ)
    nlinarith [g, h2]

/-- Label `cor:app-phase-extended`, snapshot `cr-2026-10-23`. Statement (verbatim,
`sections/07-phase-comparison/section.tex`, l.1780–1787):

\begin{corollary}[Extended main-range window]\label{cor:app-phase-extended}
Let $\alpha>1$, $\texp\ge1$ and $T\ge4$. There are $N_0$, $\epsilon_0>0$ and
$0<c_-\le c_+$ such that for all $N\ge N_0$, $B\ge N$ and $0<\epsilon<\epsilon_0$
with $\epsilon\ge\epsilon_N$, both first hits are attained and, for both $j$,
\[
c_-\le\frac{t^j_{T\epsilon}}{\mathcal S_jT_0^j\,\Pi_{r_j}(\epsilon)}\le c_+ .
\]
\end{corollary} -/
theorem cor_app_phase_extended (α ς T : ℝ) (hα : 1 < α) (hς : 1 ≤ ς) (hT : 4 ≤ T) :
    ∃ (N0 : ℕ) (ε0 cLo cHi : ℝ), 0 < ε0 ∧ 0 < cLo ∧ cLo ≤ cHi ∧
      ∀ (N B : ℕ) (ε : ℝ), N0 ≤ N → N ≤ B → 0 < ε → ε < ε0 → phaseEpsN (α + ς) N ≤ ε →
        ∀ (j : PhaseKind) (m : RowModel (Fin N)) (Q : ℝ → ℝ),
          IsMatchedModel (phaseKindArrays α ς N B j) m ε → IsVolterraSol m Q →
          dimHit Q (phaseKindT0 α N B j) T ε ≠ ⊤ ∧
            Sandwich cLo cHi
              (PhaseArrays.S (phaseKindArrays α ς N B j) * phaseKindT0 α N B j *
                phasePi (phaseKindR α ς j) ε)
              (stepHit m Q T ε).toReal := by
  have hα0 : 0 < α := by linarith
  have hp : 1 < α + ς := by linarith
  have hUs : phaseInU α ς PhaseKind.svd := Or.inr (by linarith : (1 : ℝ) < α).ne'
  have hUg : phaseInU α ς PhaseKind.sgd :=
    Or.inr ⟨(by linarith : (1 : ℝ) / 2 < α).ne', (by linarith : (1 : ℝ) < α).ne'⟩
  obtain ⟨N0s, ε0s, cLs, cHs, hε0s, hcLs, hcLHs, hs⟩ :=
    thm_app_phase_unified_iii α ς T hα0 hp hT PhaseKind.svd hUs
  obtain ⟨N0g, ε0g, cLg, cHg, hε0g, hcLg, hcLHg, hg⟩ :=
    thm_app_phase_unified_iii α ς T hα0 hp hT PhaseKind.sgd hUg
  have haS : 0 < min 1 (1 / (2 * phaseKindQ α PhaseKind.svd)) :=
    lt_min one_pos (div_pos one_pos (by linarith [un_q_pos α hα0 PhaseKind.svd]))
  have haG : 0 < min 1 (1 / (2 * phaseKindQ α PhaseKind.sgd)) :=
    lt_min one_pos (div_pos one_pos (by linarith [un_q_pos α hα0 PhaseKind.sgd]))
  refine ⟨max (max N0s N0g) 1, min ε0s (min ε0g 1),
    min (cLs * min 1 (1 / (2 * phaseKindQ α PhaseKind.svd)))
      (cLg * min 1 (1 / (2 * phaseKindQ α PhaseKind.sgd))),
    max cHs cHg, lt_min hε0s (lt_min hε0g one_pos),
    lt_min (mul_pos hcLs haS) (mul_pos hcLg haG), ?_, ?_⟩
  · exact le_trans (min_le_left _ _)
      (le_trans (mul_le_of_le_one_right hcLs.le (min_le_left _ _))
        (le_trans hcLHs (le_max_left _ _)))
  · intro N B ε hN0 hNB hε hε0 hw j m Q hm hQ
    have hN : 1 ≤ N := le_trans (le_max_right _ _) hN0
    have hNs : N0s ≤ N := le_trans (le_trans (le_max_left N0s N0g) (le_max_left _ _)) hN0
    have hNg : N0g ≤ N := le_trans (le_trans (le_max_right N0s N0g) (le_max_left _ _)) hN0
    have hεs : ε < ε0s := lt_of_lt_of_le hε0 (min_le_left _ _)
    have hεg : ε < ε0g := lt_of_lt_of_le hε0 (le_trans (min_le_right _ _) (min_le_left _ _))
    have hε1 : ε < 1 := lt_of_lt_of_le hε0 (le_trans (min_le_right _ _) (min_le_right _ _))
    cases j with
    | svd =>
      obtain ⟨hdim, hsw⟩ := hs N B ε m Q hNs hNB hε hεs hm hQ
      refine ⟨hdim, ?_⟩
      unfold Sandwich at hsw ⊢
      obtain ⟨hlo, hhi⟩ := hsw
      obtain ⟨hr1, hr2, hP0⟩ := un_ratio α ς hα hς PhaseKind.svd N ε hN hε hε1 hw
      obtain ⟨hSp, hT0p⟩ := un_ST_pos α ς PhaseKind.svd N B hα0 hp hN hNB ε hε
      exact un_sw_transfer (mul_nonneg hSp.le hT0p.le) hP0 hcLs.le (hcLs.le.trans hcLHs)
        hr1 hr2 (min_le_left _ _) (le_max_left _ _)
        (by simpa only [mul_assoc] using hlo) (by simpa only [mul_assoc] using hhi)
    | sgd =>
      obtain ⟨hdim, hsw⟩ := hg N B ε m Q hNg hNB hε hεg hm hQ
      refine ⟨hdim, ?_⟩
      unfold Sandwich at hsw ⊢
      obtain ⟨hlo, hhi⟩ := hsw
      obtain ⟨hr1, hr2, hP0⟩ := un_ratio α ς hα hς PhaseKind.sgd N ε hN hε hε1 hw
      obtain ⟨hSp, hT0p⟩ := un_ST_pos α ς PhaseKind.sgd N B hα0 hp hN hNB ε hε
      exact un_sw_transfer (mul_nonneg hSp.le hT0p.le) hP0 hcLg.le (hcLg.le.trans hcLHg)
        hr1 hr2 (min_le_right _ _) (le_max_right _ _)
        (by simpa only [mul_assoc] using hlo) (by simpa only [mul_assoc] using hhi)

private lemma un_Upsilon_pos (α ς : ℝ) (N : ℕ) (ε : ℝ) (j : PhaseKind) (hN : 2 ≤ N)
    (hε : 0 < ε) (hε1 : ε < 1) : 0 < phaseUpsilon α ς N ε j := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  unfold phaseUpsilon
  split_ifs
  · exact lt_min (Real.rpow_pos_of_pos hε _) (Real.rpow_pos_of_pos hNp _)
  · exact lt_min (Real.log_pos ((one_lt_div hε).2 hε1))
      (Real.log_pos (by exact_mod_cast (by omega : 1 < N)))
  · exact one_pos

private lemma un_scale_pos (α ς : ℝ) (j : PhaseKind) (N B : ℕ) (hα : 0 < α)
    (hp : 1 < α + ς) (hN : 2 ≤ N) (hNB : N ≤ B) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) :
    0 < PhaseArrays.S (phaseKindArrays α ς N B j) * phaseKindT0 α N B j *
      ε ^ (-(1 / 2 : ℝ)) * phaseUpsilon α ς N ε j := by
  obtain ⟨hS, ht⟩ := un_ST_pos α ς j N B hα hp (by omega) hNB ε hε
  exact mul_pos (mul_pos (mul_pos hS ht) (Real.rpow_pos_of_pos hε _))
    (un_Upsilon_pos α ς N ε j hN hε hε1)

private lemma un_scale_ratio (α ς : ℝ) (N B : ℕ) (hα : 0 < α) (hp : 1 < α + ς)
    (hN : 1 ≤ N) (hNB : N ≤ B) (ε : ℝ) (hε : 0 < ε) :
    (PhaseArrays.S (phaseKindArrays α ς N B .sgd) * phaseKindT0 α N B .sgd *
      ε ^ (-(1 / 2 : ℝ)) * phaseUpsilon α ς N ε .sgd) /
    (PhaseArrays.S (phaseKindArrays α ς N B .svd) * phaseKindT0 α N B .svd *
      ε ^ (-(1 / 2 : ℝ)) * phaseUpsilon α ς N ε .svd) =
      phaseDN α N * (phaseUpsilon α ς N ε .sgd / phaseUpsilon α ς N ε .svd) := by
  have he := (prop_app_phase_prefactors_i α ς N B hα hp hN hNB ε hε).2.2.2.2.2.2.2
  have hpw : ε ^ (-(1 / 2 : ℝ)) ≠ 0 := (Real.rpow_pos_of_pos hε _).ne'
  rw [mul_div_mul_comm, mul_div_mul_comm, div_self hpw, mul_one]
  exact congrArg (fun z => z * (phaseUpsilon α ς N ε .sgd / phaseUpsilon α ς N ε .svd)) he

private lemma un_div_lower {a b x y X Y : ℝ} (ha : 0 ≤ a) (hy : 0 ≤ y) (hX : 0 < X)
    (hl : a * y ≤ Y) (hu : X ≤ b * x) : (a / b) * (y / x) ≤ Y / X := by
  calc (a / b) * (y / x) = (a * y) / (b * x) := by ring
       _ ≤ Y / X := div_le_div₀ ((mul_nonneg ha hy).trans hl) hl hX hu

private lemma un_div_upper {a b x y X Y : ℝ} (ha : 0 < a) (hx : 0 < x)
    (hY : 0 ≤ Y) (hl : a * x ≤ X) (hu : Y ≤ b * y) : Y / X ≤ (b / a) * (y / x) := by
  calc Y / X ≤ (b * y) / (a * x) := div_le_div₀ (hY.trans hu) hu (mul_pos ha hx) hl
       _ = (b / a) * (y / x) := by ring

private lemma un_step_lower (α ς T : ℝ) (hα : 0 < α) (hp : 1 < α + ς) (hT : 4 ≤ T)
    (j : PhaseKind) :
    ∃ (N0 : ℕ) (ε0 c : ℝ), 0 < ε0 ∧ 0 < c ∧
      ∀ (N B : ℕ) (ε : ℝ) (m : RowModel (Fin N)) (Q : ℝ → ℝ),
        N0 ≤ N → N ≤ B → 0 < ε → ε < ε0 →
        IsMatchedModel (phaseKindArrays α ς N B j) m ε → IsVolterraSol m Q →
        c * (PhaseArrays.S (phaseKindArrays α ς N B j) * phaseKindT0 α N B j *
          ε ^ (-(1 / 2 : ℝ)) * phaseUpsilon α ς N ε j) ≤ (stepHit m Q T ε).toReal := by
  obtain ⟨N0, ε0, c, he, hc, h⟩ := thm_app_phase_unified_i α ς T hα hp hT j
  refine ⟨max N0 1, ε0, c / 2, he, half_pos hc, ?_⟩
  intro N B ε m Q hN hNB hε hε0 hm hQ
  obtain ⟨hf, hl⟩ := h N B ε m Q ((le_max_left _ _).trans hN) hNB hε hε0 hm hQ
  rw [un_step_eq α ς T hα hp (by linarith) j N B ((le_max_right _ _).trans hN)
    hNB ε hε m Q hm hQ hf]
  obtain ⟨hS, ht⟩ := un_ST_pos α ς j N B hα hp ((le_max_right _ _).trans hN) hNB ε hε
  have heq : ε ^ (-(1 / 2 : ℝ)) = (Real.sqrt ε)⁻¹ := by
    rw [Real.rpow_neg hε.le, Real.sqrt_eq_rpow]
  have hm := mul_le_mul_of_nonneg_left hl
    (div_nonneg (mul_nonneg hS.le ht.le) (by positivity : 0 ≤ 2 * Real.sqrt ε))
  rw [heq]
  convert hm using 1 <;> ring

/-- Label `cor:app-phase-unified-ratio`, part (i): when both models lie in `𝒰`, the ratio of the
step times is `≍ D_N Υ_{s-SGD}/Υ_{s-SVD}`. Snapshot `cr-2026-10-23`. Statement (verbatim,
`sections/07-phase-comparison/section.tex`, l.1819–1837):

\begin{corollary}[Ratio at every accuracy]\label{cor:app-phase-unified-ratio}
Fix $\alpha>0$, $\texp$ with $\alpha+\texp>1$, and $T\ge4$, and let $N_0$ and
$\epsilon_0$ be thresholds of \cref{thm:app-phase-unified} valid for both
models. If $(\alpha,\texp,\text{s-SVD})$ and $(\alpha,\texp,\text{s-SGD})$ both lie
in $\mathcal U$, then for $N\ge N_0$, $B\ge N$ and $0<\epsilon<\epsilon_0$,
\begin{equation}\label{eqn:app-phase-ratioU}
\frac{t^{\text{s-SGD}}_{T\epsilon}}{t^{\text{s-SVD}}_{T\epsilon}}\asymp
D_N\,\frac{\Upsilon_{\text{s-SGD}}(N,\epsilon)}{\Upsilon_{\text{s-SVD}}(N,\epsilon)} ,
\end{equation}
and if moreover $\texp\notin\{1,\alpha+1\}$, the right side equals
$D_N\max\{\epsilon,\epsilon_N\}^{-\chi}$. If only $(\alpha,\texp,\text{s-SGD})\in\mathcal U$,
the upper half of \cref{eqn:app-phase-ratioU} holds; if only
$(\alpha,\texp,\text{s-SVD})\in\mathcal U$, the lower half holds. For
$\epsilon=N^{-\omega}$ with fixed $\omega>0$,
\[
D_N\,\frac{\Upsilon_{\text{s-SGD}}(N,\epsilon)}{\Upsilon_{\text{s-SVD}}(N,\epsilon)}\asymp N^{e_D+\chi\min\{\omega,p-1\}}\,(\log N)^{L},
\]
with constants depending also on $\omega$.
\end{corollary} -/
theorem cor_app_phase_unified_ratio_i (α ς T : ℝ) (hα : 0 < α) (hp : 1 < α + ς) (hT : 4 ≤ T)
    (hUs : phaseInU α ς .svd) (hUg : phaseInU α ς .sgd) :
    ∃ (N0 : ℕ) (ε0 cLo cHi : ℝ), 0 < ε0 ∧ 0 < cLo ∧ cLo ≤ cHi ∧
      ∀ (N B : ℕ) (ε : ℝ) (mS mG : RowModel (Fin N)) (QS QG : ℝ → ℝ),
        N0 ≤ N → N ≤ B → 0 < ε → ε < ε0 →
        IsMatchedModel (phaseKindArrays α ς N B .svd) mS ε → IsVolterraSol mS QS →
        IsMatchedModel (phaseKindArrays α ς N B .sgd) mG ε → IsVolterraSol mG QG →
        Sandwich cLo cHi
          (phaseDN α N * (phaseUpsilon α ς N ε .sgd / phaseUpsilon α ς N ε .svd))
          ((stepHit mG QG T ε).toReal / (stepHit mS QS T ε).toReal) := by
  obtain ⟨Ns, es, ls, us, hes, hls, hlsus, hs⟩ :=
    thm_app_phase_unified_iii α ς T hα hp hT .svd hUs
  obtain ⟨Ng, eg, lg, ug, heg, hlg, hlgug, hg⟩ :=
    thm_app_phase_unified_iii α ς T hα hp hT .sgd hUg
  refine ⟨max (max Ns Ng) 2, min es (min eg 1), lg / us, ug / ls,
    lt_min hes (lt_min heg one_pos), div_pos hlg (hls.trans_le hlsus), ?_, ?_⟩
  · exact div_le_div₀ (hlg.le.trans hlgug) hlgug hls hlsus
  · intro N B ε mS mG QS QG hN hNB hε he hmS hQS hmG hQG
    have hNs : Ns ≤ N := (le_trans (le_max_left _ _) (le_max_left _ _)).trans hN
    have hNg : Ng ≤ N := (le_trans (le_max_right _ _) (le_max_left _ _)).trans hN
    have hN2 : 2 ≤ N := (le_max_right _ _).trans hN
    have hes' : ε < es := he.trans_le (min_le_left _ _)
    have heg' : ε < eg := he.trans_le ((min_le_right _ _).trans (min_le_left _ _))
    have he1 : ε < 1 := he.trans_le ((min_le_right _ _).trans (min_le_right _ _))
    obtain ⟨_, hsl, hsu⟩ := hs N B ε mS QS hNs hNB hε hes' hmS hQS
    obtain ⟨_, hgl, hgu⟩ := hg N B ε mG QG hNg hNB hε heg' hmG hQG
    have hsp := un_scale_pos α ς .svd N B hα hp hN2 hNB ε hε he1
    have hgp := un_scale_pos α ς .sgd N B hα hp hN2 hNB ε hε he1
    have hSpos := (mul_pos hls hsp).trans_le hsl
    have hr := un_scale_ratio α ς N B hα hp (by omega) hNB ε hε
    constructor
    · rw [← hr]
      exact un_div_lower hlg.le hgp.le hSpos hgl hsu
    · rw [← hr]
      exact un_div_upper hls hsp ENNReal.toReal_nonneg hsl hgu

/-- Label `cor:app-phase-unified-ratio`, the upper half of part (i): if only `(α, ς, s-SGD) ∈ 𝒰`, the
upper half of `eqn:app-phase-ratioU` holds. Snapshot `cr-2026-10-23`. Statement (verbatim,
`sections/07-phase-comparison/section.tex`, l.1819–1837):

\begin{corollary}[Ratio at every accuracy]\label{cor:app-phase-unified-ratio}
Fix $\alpha>0$, $\texp$ with $\alpha+\texp>1$, and $T\ge4$, and let $N_0$ and
$\epsilon_0$ be thresholds of \cref{thm:app-phase-unified} valid for both
models. If $(\alpha,\texp,\text{s-SVD})$ and $(\alpha,\texp,\text{s-SGD})$ both lie
in $\mathcal U$, then for $N\ge N_0$, $B\ge N$ and $0<\epsilon<\epsilon_0$,
\begin{equation}\label{eqn:app-phase-ratioU}
\frac{t^{\text{s-SGD}}_{T\epsilon}}{t^{\text{s-SVD}}_{T\epsilon}}\asymp
D_N\,\frac{\Upsilon_{\text{s-SGD}}(N,\epsilon)}{\Upsilon_{\text{s-SVD}}(N,\epsilon)} ,
\end{equation}
and if moreover $\texp\notin\{1,\alpha+1\}$, the right side equals
$D_N\max\{\epsilon,\epsilon_N\}^{-\chi}$. If only $(\alpha,\texp,\text{s-SGD})\in\mathcal U$,
the upper half of \cref{eqn:app-phase-ratioU} holds; if only
$(\alpha,\texp,\text{s-SVD})\in\mathcal U$, the lower half holds. For
$\epsilon=N^{-\omega}$ with fixed $\omega>0$,
\[
D_N\,\frac{\Upsilon_{\text{s-SGD}}(N,\epsilon)}{\Upsilon_{\text{s-SVD}}(N,\epsilon)}\asymp N^{e_D+\chi\min\{\omega,p-1\}}\,(\log N)^{L},
\]
with constants depending also on $\omega$.
\end{corollary} -/
theorem cor_app_phase_unified_ratio_ii (α ς T : ℝ) (hα : 0 < α) (hp : 1 < α + ς) (hT : 4 ≤ T)
    (hUg : phaseInU α ς .sgd) :
    ∃ (N0 : ℕ) (ε0 cHi : ℝ), 0 < ε0 ∧ 0 < cHi ∧
      ∀ (N B : ℕ) (ε : ℝ) (mS mG : RowModel (Fin N)) (QS QG : ℝ → ℝ),
        N0 ≤ N → N ≤ B → 0 < ε → ε < ε0 →
        IsMatchedModel (phaseKindArrays α ς N B .svd) mS ε → IsVolterraSol mS QS →
        IsMatchedModel (phaseKindArrays α ς N B .sgd) mG ε → IsVolterraSol mG QG →
        0 < (stepHit mS QS T ε).toReal ∧ stepHit mG QG T ε ≠ ⊤ ∧
        (stepHit mG QG T ε).toReal / (stepHit mS QS T ε).toReal ≤
          cHi * (phaseDN α N * (phaseUpsilon α ς N ε .sgd / phaseUpsilon α ς N ε .svd)) := by
  obtain ⟨Ns, es, ls, hes, hls, hs⟩ := un_step_lower α ς T hα hp hT .svd
  obtain ⟨Ng, eg, lg, ug, heg, hlg, hlgu, hg⟩ :=
    thm_app_phase_unified_iii α ς T hα hp hT .sgd hUg
  refine ⟨max (max Ns Ng) 2, min es (min eg 1), ug / ls,
    lt_min hes (lt_min heg one_pos), ?_, ?_⟩
  · exact div_pos (hlg.trans_le hlgu) hls
  · intro N B ε mS mG QS QG hN hNB hε he hmS hQS hmG hQG
    have hNs : Ns ≤ N := (le_trans (le_max_left _ _) (le_max_left _ _)).trans hN
    have hNg : Ng ≤ N := (le_trans (le_max_right _ _) (le_max_left _ _)).trans hN
    have hN2 : 2 ≤ N := (le_max_right _ _).trans hN
    have hes' : ε < es := he.trans_le (min_le_left _ _)
    have heg' : ε < eg := he.trans_le ((min_le_right _ _).trans (min_le_left _ _))
    have he1 : ε < 1 := he.trans_le ((min_le_right _ _).trans (min_le_right _ _))
    have hsl := hs N B ε mS QS hNs hNB hε hes' hmS hQS
    obtain ⟨_, hgl, hgu⟩ := hg N B ε mG QG hNg hNB hε heg' hmG hQG
    have hsp := un_scale_pos α ς .svd N B hα hp hN2 hNB ε hε he1
    have hgp := un_scale_pos α ς .sgd N B hα hp hN2 hNB ε hε he1
    have hSpos := (mul_pos hls hsp).trans_le hsl
    have hGpos := (mul_pos hlg hgp).trans_le hgl
    refine ⟨hSpos, ?_, ?_⟩
    · intro ht
      simp [ht] at hGpos
    · rw [← un_scale_ratio α ς N B hα hp (by omega) hNB ε hε]
      exact un_div_upper hls hsp ENNReal.toReal_nonneg hsl hgu

/-- Label `cor:app-phase-unified-ratio`, the lower half of part (i): if only `(α, ς, s-SVD) ∈ 𝒰`, the
lower half of `eqn:app-phase-ratioU` holds. Snapshot `cr-2026-10-23`. Statement (verbatim,
`sections/07-phase-comparison/section.tex`, l.1819–1837):

\begin{corollary}[Ratio at every accuracy]\label{cor:app-phase-unified-ratio}
Fix $\alpha>0$, $\texp$ with $\alpha+\texp>1$, and $T\ge4$, and let $N_0$ and
$\epsilon_0$ be thresholds of \cref{thm:app-phase-unified} valid for both
models. If $(\alpha,\texp,\text{s-SVD})$ and $(\alpha,\texp,\text{s-SGD})$ both lie
in $\mathcal U$, then for $N\ge N_0$, $B\ge N$ and $0<\epsilon<\epsilon_0$,
\begin{equation}\label{eqn:app-phase-ratioU}
\frac{t^{\text{s-SGD}}_{T\epsilon}}{t^{\text{s-SVD}}_{T\epsilon}}\asymp
D_N\,\frac{\Upsilon_{\text{s-SGD}}(N,\epsilon)}{\Upsilon_{\text{s-SVD}}(N,\epsilon)} ,
\end{equation}
and if moreover $\texp\notin\{1,\alpha+1\}$, the right side equals
$D_N\max\{\epsilon,\epsilon_N\}^{-\chi}$. If only $(\alpha,\texp,\text{s-SGD})\in\mathcal U$,
the upper half of \cref{eqn:app-phase-ratioU} holds; if only
$(\alpha,\texp,\text{s-SVD})\in\mathcal U$, the lower half holds. For
$\epsilon=N^{-\omega}$ with fixed $\omega>0$,
\[
D_N\,\frac{\Upsilon_{\text{s-SGD}}(N,\epsilon)}{\Upsilon_{\text{s-SVD}}(N,\epsilon)}\asymp N^{e_D+\chi\min\{\omega,p-1\}}\,(\log N)^{L},
\]
with constants depending also on $\omega$.
\end{corollary} -/
theorem cor_app_phase_unified_ratio_iii (α ς T : ℝ) (hα : 0 < α) (hp : 1 < α + ς) (hT : 4 ≤ T)
    (hUs : phaseInU α ς .svd) :
    ∃ (N0 : ℕ) (ε0 cLo : ℝ), 0 < ε0 ∧ 0 < cLo ∧
      ∀ (N B : ℕ) (ε : ℝ) (mS mG : RowModel (Fin N)) (QS QG : ℝ → ℝ),
        N0 ≤ N → N ≤ B → 0 < ε → ε < ε0 →
        IsMatchedModel (phaseKindArrays α ς N B .svd) mS ε → IsVolterraSol mS QS →
        IsMatchedModel (phaseKindArrays α ς N B .sgd) mG ε → IsVolterraSol mG QG →
        cLo * (phaseDN α N * (phaseUpsilon α ς N ε .sgd / phaseUpsilon α ς N ε .svd)) ≤
          (stepHit mG QG T ε).toReal / (stepHit mS QS T ε).toReal := by
  obtain ⟨Ns, es, ls, us, hes, hls, hlsus, hs⟩ :=
    thm_app_phase_unified_iii α ς T hα hp hT .svd hUs
  obtain ⟨Ng, eg, lg, heg, hlg, hg⟩ := un_step_lower α ς T hα hp hT .sgd
  refine ⟨max (max Ns Ng) 2, min es (min eg 1), lg / us,
    lt_min hes (lt_min heg one_pos), div_pos hlg (hls.trans_le hlsus), ?_⟩
  intro N B ε mS mG QS QG hN hNB hε he hmS hQS hmG hQG
  have hNs : Ns ≤ N := (le_trans (le_max_left _ _) (le_max_left _ _)).trans hN
  have hNg : Ng ≤ N := (le_trans (le_max_right _ _) (le_max_left _ _)).trans hN
  have hN2 : 2 ≤ N := (le_max_right _ _).trans hN
  have hes' : ε < es := he.trans_le (min_le_left _ _)
  have heg' : ε < eg := he.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have he1 : ε < 1 := he.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨_, hsl, hsu⟩ := hs N B ε mS QS hNs hNB hε hes' hmS hQS
  have hgl := hg N B ε mG QG hNg hNB hε heg' hmG hQG
  have hsp := un_scale_pos α ς .svd N B hα hp hN2 hNB ε hε he1
  have hgp := un_scale_pos α ς .sgd N B hα hp hN2 hNB ε hε he1
  have hSpos := (mul_pos hls hsp).trans_le hsl
  rw [← un_scale_ratio α ς N B hα hp (by omega) hNB ε hε]
  exact un_div_lower hlg.le hgp.le hSpos hgl hsu

private lemma un_ratio_r_svd (α ς : ℝ) :
    phaseKindR α ς .svd = (α + ς - 1) / α := by
  simp only [phaseKindR, rq, phaseKindQ]
  congr 1
  ring

private lemma un_ratio_r_sgd (α ς : ℝ) :
    phaseKindR α ς .sgd = (α + ς - 1) / (2 * α) := by
  simp only [phaseKindR, rq, phaseKindQ]

private lemma un_ratio_r_pos (α ς : ℝ) (hα : 0 < α) (hp : 1 < α + ς) (j : PhaseKind) :
    0 < phaseKindR α ς j := by
  rw [show phaseKindR α ς j = (α + ς - 1) / (2 * phaseKindQ α j) from rfl]
  exact div_pos (by linarith) (by linarith [un_q_pos α hα j])

private lemma un_ratio_r_svd_ne_one (α ς : ℝ) (hα : 0 < α) (hς1 : ς ≠ 1) :
    phaseKindR α ς .svd ≠ 1 := by
  rw [un_ratio_r_svd]
  intro h
  have hα0 : α ≠ 0 := hα.ne'
  field_simp [hα0] at h
  apply hς1
  linarith

private lemma un_ratio_r_sgd_ne_one (α ς : ℝ) (hα : 0 < α) (hς2 : ς ≠ α + 1) :
    phaseKindR α ς .sgd ≠ 1 := by
  rw [un_ratio_r_sgd]
  intro h
  have hα0 : α ≠ 0 := hα.ne'
  field_simp [hα0] at h
  apply hς2
  linarith

private lemma un_Upsilon_max_of_ne_one (α ς : ℝ) (j : PhaseKind) (hα : 0 < α)
    (hp : 1 < α + ς) (hr1 : phaseKindR α ς j ≠ 1) (N : ℕ) (hN : 1 ≤ N)
    (ε : ℝ) (hε : 0 < ε) :
    phaseUpsilon α ς N ε j =
      (max ε (phaseEpsN (α + ς) N)) ^ (-(phaseKindE α ς j - 1 / 2)) := by
  have hq : 0 < phaseKindQ α j := un_q_pos α hα j
  have hr0 : 0 < phaseKindR α ς j := un_ratio_r_pos α ς hα hp j
  have hNp : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hENp : 0 < phaseEpsN (α + ς) N :=
    Real.rpow_pos_of_pos hNp _
  rcases lt_or_gt_of_ne hr1 with hr | hr
  · have he : phaseKindE α ς j - 1 / 2 =
        (1 - phaseKindR α ς j) / (2 * phaseKindR α ς j) := by
      unfold phaseKindE
      rw [max_eq_right]
      · field_simp [hr0.ne']
      · rw [le_div_iff₀ (by linarith : 0 < 2 * phaseKindR α ς j)]
        linarith
    have ha0 : -(phaseKindE α ς j - 1 / 2) ≤ 0 := by
      rw [he]
      exact neg_nonpos.mpr (div_nonneg (by linarith) (by positivity))
    have hcut : (phaseEpsN (α + ς) N) ^ (-(phaseKindE α ς j - 1 / 2)) =
        (N : ℝ) ^ (phaseKindQ α j * (1 - phaseKindR α ς j)) := by
      unfold phaseEpsN
      rw [he, ← Real.rpow_mul hNp.le]
      congr 1
      have hR : α + ς - 1 = 2 * phaseKindQ α j * phaseKindR α ς j := by
        rw [show phaseKindR α ς j = (α + ς - 1) / (2 * phaseKindQ α j) from rfl]
        field_simp [hq.ne']
      rw [hR]
      field_simp [hr0.ne']
    rw [he] at hcut
    rw [he] at ha0
    unfold phaseUpsilon
    rw [if_pos hr, he]
    by_cases hle : ε ≤ phaseEpsN (α + ς) N
    · rw [max_eq_right hle, min_eq_right]
      · exact hcut.symm
      · rw [← hcut]
        exact Real.rpow_le_rpow_of_nonpos hε hle ha0
    · have hge : phaseEpsN (α + ς) N ≤ ε := le_of_not_ge hle
      rw [max_eq_left hge, min_eq_left]
      rw [← hcut]
      exact Real.rpow_le_rpow_of_nonpos hENp hge ha0
  · have he : phaseKindE α ς j = 1 / 2 := by
      unfold phaseKindE
      rw [max_eq_left]
      rw [div_le_iff₀ (by linarith : 0 < 2 * phaseKindR α ς j)]
      linarith
    unfold phaseUpsilon
    rw [if_neg (by linarith), if_neg hr.ne', he]
    norm_num

/-- Label `cor:app-phase-unified-ratio`, the identity "if moreover `ς ∉ {1, α+1}`": the right side of
`eqn:app-phase-ratioU` equals `D_N max{ε, ε_N}^{-χ}`. Snapshot `cr-2026-10-23`. Statement (verbatim,
`sections/07-phase-comparison/section.tex`, l.1819–1837, with `χ` of the display after `eqn:app-phase-ej`):

\begin{corollary}[Ratio at every accuracy]\label{cor:app-phase-unified-ratio}
Fix $\alpha>0$, $\texp$ with $\alpha+\texp>1$, and $T\ge4$, and let $N_0$ and
$\epsilon_0$ be thresholds of \cref{thm:app-phase-unified} valid for both
models. If $(\alpha,\texp,\text{s-SVD})$ and $(\alpha,\texp,\text{s-SGD})$ both lie
in $\mathcal U$, then for $N\ge N_0$, $B\ge N$ and $0<\epsilon<\epsilon_0$,
\begin{equation}\label{eqn:app-phase-ratioU}
\frac{t^{\text{s-SGD}}_{T\epsilon}}{t^{\text{s-SVD}}_{T\epsilon}}\asymp
D_N\,\frac{\Upsilon_{\text{s-SGD}}(N,\epsilon)}{\Upsilon_{\text{s-SVD}}(N,\epsilon)} ,
\end{equation}
and if moreover $\texp\notin\{1,\alpha+1\}$, the right side equals
$D_N\max\{\epsilon,\epsilon_N\}^{-\chi}$. If only $(\alpha,\texp,\text{s-SGD})\in\mathcal U$,
the upper half of \cref{eqn:app-phase-ratioU} holds; if only
$(\alpha,\texp,\text{s-SVD})\in\mathcal U$, the lower half holds. For
$\epsilon=N^{-\omega}$ with fixed $\omega>0$,
\[
D_N\,\frac{\Upsilon_{\text{s-SGD}}(N,\epsilon)}{\Upsilon_{\text{s-SVD}}(N,\epsilon)}\asymp N^{e_D+\chi\min\{\omega,p-1\}}\,(\log N)^{L},
\]
with constants depending also on $\omega$.
\end{corollary} -/
theorem cor_app_phase_unified_ratio_iv (α ς : ℝ) (hα : 0 < α) (hp : 1 < α + ς)
    (hς1 : ς ≠ 1) (hς2 : ς ≠ α + 1) (hUs : phaseInU α ς .svd) (hUg : phaseInU α ς .sgd)
    (N : ℕ) (hN : 1 ≤ N) (ε : ℝ) (hε : 0 < ε) :
    phaseDN α N * (phaseUpsilon α ς N ε .sgd / phaseUpsilon α ς N ε .svd) =
      phaseDN α N * (max ε (phaseEpsN (α + ς) N)) ^ (-(phaseChi α ς)) := by
  have hs := un_Upsilon_max_of_ne_one α ς .svd hα hp
    (un_ratio_r_svd_ne_one α ς hα hς1) N hN ε hε
  have hg := un_Upsilon_max_of_ne_one α ς .sgd hα hp
    (un_ratio_r_sgd_ne_one α ς hα hς2) N hN ε hε
  rw [hs, hg]
  congr 1
  have hM : 0 < max ε (phaseEpsN (α + ς) N) := hε.trans_le (le_max_left _ _)
  rw [← Real.rpow_sub hM]
  congr 1
  unfold phaseChi
  ring

private lemma un_phaseDN_pos (α : ℝ) {N : ℕ} (hN : 1 ≤ N) : 0 < phaseDN α N := by
  unfold phaseDN
  exact div_pos (mul_pos Real.pi_pos (un_Hsum_pos α N hN)) (un_Hsum_pos (α / 2) N hN)

private lemma un_power_max (α ς ω c : ℝ) (hp : 1 < α + ς) (hω : 0 < ω) {N : ℕ} (hN : 2 ≤ N) :
    (max ((N : ℝ) ^ (-ω)) (phaseEpsN (α + ς) N)) ^ (-c) =
      (N : ℝ) ^ (c * min ω (α + ς - 1)) := by
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (by omega : 1 ≤ N)
  have hN0 : (0 : ℝ) < N := by linarith
  have hbase : max ((N : ℝ) ^ (-ω)) (phaseEpsN (α + ς) N) =
      (N : ℝ) ^ (-(min ω (α + ς - 1))) := by
    unfold phaseEpsN
    by_cases hw : ω ≤ α + ς - 1
    · rw [min_eq_left hw, max_eq_left]
      exact Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
    · have hw' : α + ς - 1 ≤ ω := le_of_not_ge hw
      rw [min_eq_right hw', max_eq_right]
      exact Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
  rw [hbase, ← Real.rpow_mul hN0.le]
  congr 1
  ring

private lemma un_log_power_eps (ω : ℝ) {N : ℕ} (hN : 1 ≤ N) :
    Real.log (1 / ((N : ℝ) ^ (-ω))) = ω * Real.log (N : ℝ) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  rw [one_div, Real.rpow_neg hN0.le, inv_inv, Real.log_rpow hN0]

private lemma un_Uratio_power (α ς ω : ℝ) (hα : 0 < α) (hp : 1 < α + ς) (hω : 0 < ω) :
    ∃ c : ℝ, 0 < c ∧ ∀ N : ℕ, 2 ≤ N →
      phaseUpsilon α ς N ((N : ℝ) ^ (-ω)) .sgd /
          phaseUpsilon α ς N ((N : ℝ) ^ (-ω)) .svd =
        c * (N : ℝ) ^ (phaseChi α ς * min ω (α + ς - 1)) *
          (Real.log (N : ℝ)) ^
            (((if ς = α + 1 then 1 else 0) - (if ς = 1 then 1 else 0)) : ℝ) := by
  by_cases h1 : ς = 1
  · have h2 : ς ≠ α + 1 := by
      intro h
      rw [h1] at h
      linarith
    refine ⟨(min ω 1)⁻¹, inv_pos.mpr (lt_min hω one_pos), ?_⟩
    intro N hN
    have hN1 : 1 ≤ N := by omega
    have hNr : (1 : ℝ) < N := by exact_mod_cast (by omega : 1 < N)
    have hN0 : (0 : ℝ) < N := by linarith
    have hrS : phaseKindR α ς .svd = 1 := by
      rw [un_ratio_r_svd, h1]
      field_simp [hα.ne']
      ring
    have hrG : phaseKindR α ς .sgd = 1 / 2 := by
      rw [un_ratio_r_sgd, h1]
      field_simp [hα.ne']
      ring
    have heS : phaseKindE α ς .svd = 1 / 2 := by simp [phaseKindE, hrS]
    have heG : phaseKindE α ς .sgd = 1 := by
      unfold phaseKindE
      rw [hrG]
      norm_num
    have hchi : phaseChi α ς = 1 / 2 := by
      rw [phaseChi, heG, heS]
      norm_num
    have hs : phaseUpsilon α ς N ((N : ℝ) ^ (-ω)) .svd =
        min ω 1 * Real.log (N : ℝ) := by
      unfold phaseUpsilon
      rw [hrS, if_neg (by norm_num), if_pos rfl, un_log_power_eps ω hN1]
      calc min (ω * Real.log (N : ℝ)) (Real.log (N : ℝ)) =
            min (Real.log (N : ℝ) * ω) (Real.log (N : ℝ) * 1) := by congr 1 <;> ring
        _ = Real.log (N : ℝ) * min ω 1 :=
          (mul_min_of_nonneg ω 1 (Real.log_nonneg hNr.le)).symm
        _ = min ω 1 * Real.log (N : ℝ) := by ring
    have hg := un_Upsilon_max_of_ne_one α ς .sgd hα hp (by rw [hrG]; norm_num) N hN1
      ((N : ℝ) ^ (-ω)) (Real.rpow_pos_of_pos hN0 _)
    have hg' : phaseUpsilon α ς N ((N : ℝ) ^ (-ω)) .sgd =
        (N : ℝ) ^ (phaseChi α ς * min ω (α + ς - 1)) := by
      rw [hg, heG, hchi]
      norm_num
      simpa [hchi] using un_power_max α ς ω (phaseChi α ς) hp hω hN
    have hlogpow : ((if ς = α + 1 then 1 else 0) - (if ς = 1 then 1 else 0) : ℝ) = -1 := by
      rw [if_neg h2, if_pos h1]
      norm_num
    rw [hg', hs]
    rw [hlogpow, Real.rpow_neg_one, div_eq_mul_inv, mul_inv]
    ring
  · by_cases h2 : ς = α + 1
    · refine ⟨min ω 1, lt_min hω one_pos, ?_⟩
      intro N hN
      have hN1 : 1 ≤ N := by omega
      have hNr : (1 : ℝ) < N := by exact_mod_cast (by omega : 1 < N)
      have hrG : phaseKindR α ς .sgd = 1 := by
        rw [un_ratio_r_sgd, h2]
        field_simp [hα.ne']
        ring
      have hrSeq : phaseKindR α ς .svd = 2 := by
        rw [un_ratio_r_svd, h2]
        field_simp [hα.ne']
        ring
      have hrS : 1 < phaseKindR α ς .svd := by rw [hrSeq]; norm_num
      have heG : phaseKindE α ς .sgd = 1 / 2 := by simp [phaseKindE, hrG]
      have heS : phaseKindE α ς .svd = 1 / 2 := by
        unfold phaseKindE
        rw [max_eq_left]
        rw [div_le_iff₀ (by linarith : 0 < 2 * phaseKindR α ς .svd)]
        linarith
      have hchi : phaseChi α ς = 0 := by
        rw [phaseChi, heG, heS]
        ring
      have hg : phaseUpsilon α ς N ((N : ℝ) ^ (-ω)) .sgd =
          min ω 1 * Real.log (N : ℝ) := by
        unfold phaseUpsilon
        rw [hrG, if_neg (by norm_num), if_pos rfl, un_log_power_eps ω hN1]
        calc min (ω * Real.log (N : ℝ)) (Real.log (N : ℝ)) =
              min (Real.log (N : ℝ) * ω) (Real.log (N : ℝ) * 1) := by congr 1 <;> ring
          _ = Real.log (N : ℝ) * min ω 1 :=
            (mul_min_of_nonneg ω 1 (Real.log_nonneg hNr.le)).symm
          _ = min ω 1 * Real.log (N : ℝ) := by ring
      have hs : phaseUpsilon α ς N ((N : ℝ) ^ (-ω)) .svd = 1 := by
        unfold phaseUpsilon
        rw [if_neg (by linarith), if_neg (by linarith)]
      have hcrit : α + 1 ≠ (1 : ℝ) := by linarith
      rw [hg, hs, div_one, hchi]
      simp [h2, h1, hcrit]
    · refine ⟨1, one_pos, ?_⟩
      intro N hN
      have hN1 : 1 ≤ N := by omega
      have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
      have hR : phaseUpsilon α ς N ((N : ℝ) ^ (-ω)) .sgd /
          phaseUpsilon α ς N ((N : ℝ) ^ (-ω)) .svd =
          (max ((N : ℝ) ^ (-ω)) (phaseEpsN (α + ς) N)) ^ (-(phaseChi α ς)) := by
        have hs := un_Upsilon_max_of_ne_one α ς .svd hα hp
          (un_ratio_r_svd_ne_one α ς hα h1) N hN1 ((N : ℝ) ^ (-ω))
          (Real.rpow_pos_of_pos hN0 _)
        have hg := un_Upsilon_max_of_ne_one α ς .sgd hα hp
          (un_ratio_r_sgd_ne_one α ς hα h2) N hN1 ((N : ℝ) ^ (-ω))
          (Real.rpow_pos_of_pos hN0 _)
        rw [hg, hs, ← Real.rpow_sub (by positivity :
          0 < max ((N : ℝ) ^ (-ω)) (phaseEpsN (α + ς) N))]
        congr 1
        unfold phaseChi
        ring
      rw [hR, un_power_max α ς ω (phaseChi α ς) hp hω hN,
        if_neg h2, if_neg h1]
      norm_num

private lemma un_equiv_const_sandwich (u x : ℕ → ℝ) (C : ℝ) (hC : 0 < C)
    (h : Asymptotics.IsEquivalent atTop u (fun N => C * x N))
    (hx : ∀ᶠ N in atTop, 0 ≤ x N) :
    ∃ (N0 : ℕ) (cLo cHi : ℝ), 0 < cLo ∧ cLo ≤ cHi ∧
      ∀ N : ℕ, N0 ≤ N → Sandwich cLo cHi (x N) (u N) := by
  obtain ⟨φ, hφ, heq⟩ := h.exists_eq_mul
  have hb : ∀ᶠ N in atTop, φ N ∈ Set.Icc (1 / 2 : ℝ) 2 :=
    hφ.eventually (Icc_mem_nhds (by norm_num) (by norm_num))
  have hall : ∀ᶠ N in atTop, Sandwich (C / 2) (2 * C) (x N) (u N) := by
    filter_upwards [hb, heq, hx] with N hφN heqN hxN
    simp only [Pi.mul_apply] at heqN
    rw [heqN]
    constructor
    · calc C / 2 * x N = (1 / 2 : ℝ) * (C * x N) := by ring
        _ ≤ φ N * (C * x N) :=
          mul_le_mul_of_nonneg_right hφN.1 (mul_nonneg hC.le hxN)
    · calc φ N * (C * x N) ≤ 2 * (C * x N) :=
          mul_le_mul_of_nonneg_right hφN.2 (mul_nonneg hC.le hxN)
        _ = 2 * C * x N := by ring
  obtain ⟨N0, hN0⟩ := Filter.eventually_atTop.1 hall
  exact ⟨N0, C / 2, 2 * C, half_pos hC, by linarith, hN0⟩

private lemma un_one_le_zeta {a : ℝ} (ha : 1 < a) : 1 ≤ zetaR a := by
  have h := (lem_app_phase_harmonic_vi ha 1 le_rfl).1
  have h1 : Hsum a 1 = 1 := by simp [Hsum]
  linarith

private lemma un_DN_sandwich (α : ℝ) (hα : 0 < α) :
    ∃ (N0 : ℕ) (cLo cHi : ℝ), 0 < cLo ∧ cLo ≤ cHi ∧
      ∀ N : ℕ, N0 ≤ N →
        Sandwich cLo cHi
          ((N : ℝ) ^ phaseExpD α * (Real.log (N : ℝ)) ^
            (((if α = 1 then 1 else 0) - (if α = 2 then 1 else 0)) : ℝ))
          (phaseDN α N) := by
  obtain ⟨hA, hB, hC, hD, hE⟩ := prop_app_phase_prefactors_iv α hα
  by_cases ha1 : α < 1
  · have hα1 : α ≠ 1 := ne_of_lt ha1
    have hα2 : α ≠ 2 := by linarith
    have hK : 0 < Real.pi * (1 - α / 2) / (1 - α) :=
      div_pos (mul_pos Real.pi_pos (by linarith)) (by linarith)
    apply un_equiv_const_sandwich
      (u := fun N : ℕ => phaseDN α N)
      (x := fun N : ℕ => (N : ℝ) ^ phaseExpD α * (Real.log (N : ℝ)) ^
        (((if α = 1 then 1 else 0) - (if α = 2 then 1 else 0)) : ℝ))
      (C := Real.pi * (1 - α / 2) / (1 - α)) hK
    · refine (hA ha1).congr_right (Filter.Eventually.of_forall fun N => ?_)
      simp only [phaseExpD, if_pos ha1, if_neg hα1, if_neg hα2, sub_zero, Real.rpow_zero,
        mul_one]
      rw [show -(α / 2) = -α / 2 by ring]
    · filter_upwards with N
      simp [phaseExpD, ha1, hα1, hα2, Real.rpow_nonneg]
  · have ha1le : 1 ≤ α := le_of_not_gt ha1
    by_cases ha1eq : α = 1
    · subst α
      apply un_equiv_const_sandwich
        (u := fun N : ℕ => phaseDN 1 N)
        (x := fun N : ℕ => (N : ℝ) ^ phaseExpD 1 * (Real.log (N : ℝ)) ^
          (((if (1 : ℝ) = 1 then 1 else 0) - (if (1 : ℝ) = 2 then 1 else 0)) : ℝ))
        (C := Real.pi / 2) (by positivity)
      · refine (hB rfl).congr_right (Filter.Eventually.of_forall fun N => ?_)
        norm_num [phaseExpD]
        rw [show (-(1 / 2 : ℝ)) = -1 / 2 by ring]
        ring
      · filter_upwards [eventually_ge_atTop 2] with N hN
        have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
        have hlog : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ N))
        positivity
    · by_cases ha2 : α < 2
      · have hα2 : α ≠ 2 := ne_of_lt ha2
        have hαgt : 1 < α := lt_of_le_of_ne ha1le (Ne.symm ha1eq)
        have hz : 0 < zetaR α := lt_of_lt_of_le zero_lt_one (un_one_le_zeta hαgt)
        have hK : 0 < Real.pi * (1 - α / 2) * zetaR α :=
          mul_pos (mul_pos Real.pi_pos (by linarith)) hz
        apply un_equiv_const_sandwich
          (u := fun N : ℕ => phaseDN α N)
          (x := fun N : ℕ => (N : ℝ) ^ phaseExpD α * (Real.log (N : ℝ)) ^
            (((if α = 1 then 1 else 0) - (if α = 2 then 1 else 0)) : ℝ))
          (C := Real.pi * (1 - α / 2) * zetaR α) hK
        · simpa [phaseExpD, ha1, ha1eq, ha2, hα2, mul_assoc] using hC hαgt ha2
        · filter_upwards with N
          simp [phaseExpD, ha1, ha1eq, ha2, hα2, Real.rpow_nonneg]
      · have ha2le : 2 ≤ α := le_of_not_gt ha2
        by_cases ha2eq : α = 2
        · subst α
          have hz : 0 < zetaR 2 := lt_of_lt_of_le zero_lt_one (un_one_le_zeta (by norm_num))
          apply un_equiv_const_sandwich
            (u := fun N : ℕ => phaseDN 2 N)
            (x := fun N : ℕ => (N : ℝ) ^ phaseExpD 2 * (Real.log (N : ℝ)) ^
              (((if (2 : ℝ) = 1 then 1 else 0) - (if (2 : ℝ) = 2 then 1 else 0)) : ℝ))
            (C := Real.pi * zetaR 2) (mul_pos Real.pi_pos hz)
          · simpa [phaseExpD, div_eq_mul_inv, mul_assoc, Real.rpow_neg_one] using hD rfl
          · filter_upwards [eventually_ge_atTop 2] with N hN
            have hlog : 0 < Real.log (N : ℝ) :=
              Real.log_pos (by exact_mod_cast (by omega : 1 < N))
            positivity
        · have hαgt : 2 < α := lt_of_le_of_ne ha2le (Ne.symm ha2eq)
          have hz1 : 0 < zetaR α := lt_of_lt_of_le zero_lt_one (un_one_le_zeta (by linarith))
          have hz2 : 0 < zetaR (α / 2) := lt_of_lt_of_le zero_lt_one (un_one_le_zeta (by linarith))
          apply un_equiv_const_sandwich
            (u := fun N : ℕ => phaseDN α N)
            (x := fun N : ℕ => (N : ℝ) ^ phaseExpD α * (Real.log (N : ℝ)) ^
              (((if α = 1 then 1 else 0) - (if α = 2 then 1 else 0)) : ℝ))
            (C := Real.pi * zetaR α / zetaR (α / 2)) (div_pos (mul_pos Real.pi_pos hz1) hz2)
          · simpa [phaseExpD, ha1, ha1eq, ha2, ha2eq, mul_assoc] using hE hαgt
          · filter_upwards with N
            simp [phaseExpD, ha1, ha1eq, ha2, ha2eq]

/-- Label `cor:app-phase-unified-ratio`, the accuracy form `ε = N^{-ω}` with fixed `ω > 0`: the ratio
`D_N Υ_{s-SGD}/Υ_{s-SVD}` is `≍ N^{e_D + χ min{ω, p-1}} (log N)^L`, with constants depending also on
`ω`. Snapshot `cr-2026-10-23`. Statement (verbatim, `sections/07-phase-comparison/section.tex`, l.1819–1837):

\begin{corollary}[Ratio at every accuracy]\label{cor:app-phase-unified-ratio}
Fix $\alpha>0$, $\texp$ with $\alpha+\texp>1$, and $T\ge4$, and let $N_0$ and
$\epsilon_0$ be thresholds of \cref{thm:app-phase-unified} valid for both
models. If $(\alpha,\texp,\text{s-SVD})$ and $(\alpha,\texp,\text{s-SGD})$ both lie
in $\mathcal U$, then for $N\ge N_0$, $B\ge N$ and $0<\epsilon<\epsilon_0$,
\begin{equation}\label{eqn:app-phase-ratioU}
\frac{t^{\text{s-SGD}}_{T\epsilon}}{t^{\text{s-SVD}}_{T\epsilon}}\asymp
D_N\,\frac{\Upsilon_{\text{s-SGD}}(N,\epsilon)}{\Upsilon_{\text{s-SVD}}(N,\epsilon)} ,
\end{equation}
and if moreover $\texp\notin\{1,\alpha+1\}$, the right side equals
$D_N\max\{\epsilon,\epsilon_N\}^{-\chi}$. If only $(\alpha,\texp,\text{s-SGD})\in\mathcal U$,
the upper half of \cref{eqn:app-phase-ratioU} holds; if only
$(\alpha,\texp,\text{s-SVD})\in\mathcal U$, the lower half holds. For
$\epsilon=N^{-\omega}$ with fixed $\omega>0$,
\[
D_N\,\frac{\Upsilon_{\text{s-SGD}}(N,\epsilon)}{\Upsilon_{\text{s-SVD}}(N,\epsilon)}\asymp N^{e_D+\chi\min\{\omega,p-1\}}\,(\log N)^{L},
\]
with constants depending also on $\omega$.
\end{corollary} -/
theorem cor_app_phase_unified_ratio_v (α ς : ℝ) (hα : 0 < α) (hp : 1 < α + ς) (ω : ℝ) (hω : 0 < ω) :
    ∃ (N0 : ℕ) (cLo cHi : ℝ), 0 < cLo ∧ cLo ≤ cHi ∧
      ∀ N : ℕ, N0 ≤ N →
        Sandwich cLo cHi
          ((N : ℝ) ^ (phaseExpD α + phaseChi α ς * min ω (α + ς - 1)) *
            (Real.log (N : ℝ)) ^ phaseLogPow α ς)
          (phaseDN α N * (phaseUpsilon α ς N ((N : ℝ) ^ (-ω)) .sgd /
            phaseUpsilon α ς N ((N : ℝ) ^ (-ω)) .svd)) := by
  obtain ⟨ND, dLo, dHi, hdLo, hdLH, hD⟩ := un_DN_sandwich α hα
  obtain ⟨c, hc, hU⟩ := un_Uratio_power α ς ω hα hp hω
  refine ⟨max ND 2, dLo * c, dHi * c, mul_pos hdLo hc,
    mul_le_mul_of_nonneg_right hdLH hc.le, ?_⟩
  intro N hN
  have hND : ND ≤ N := (le_max_left _ _).trans hN
  have hN2 : 2 ≤ N := (le_max_right _ _).trans hN
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hN1 : (1 : ℝ) < N := by exact_mod_cast (by omega : 1 < N)
  have hlog : 0 < Real.log (N : ℝ) := Real.log_pos hN1
  obtain ⟨hDl, hDh⟩ := hD N hND
  have hUr := hU N hN2
  let dD : ℝ := (if α = 1 then 1 else 0) - (if α = 2 then 1 else 0)
  let dU : ℝ := (if ς = α + 1 then 1 else 0) - (if ς = 1 then 1 else 0)
  let eU : ℝ := phaseChi α ς * min ω (α + ς - 1)
  have hL : phaseLogPow α ς = dD + dU := by
    unfold phaseLogPow dD dU
    ring
  have hX :
      (N : ℝ) ^ (phaseExpD α + phaseChi α ς * min ω (α + ς - 1)) *
          (Real.log (N : ℝ)) ^ phaseLogPow α ς =
        ((N : ℝ) ^ phaseExpD α * (Real.log (N : ℝ)) ^ dD) *
          ((N : ℝ) ^ eU * (Real.log (N : ℝ)) ^ dU) := by
    rw [hL]
    change (N : ℝ) ^ (phaseExpD α + eU) * (Real.log (N : ℝ)) ^ (dD + dU) = _
    rw [Real.rpow_add hN0, Real.rpow_add hlog]
    ring
  have hUp : 0 < c * ((N : ℝ) ^ eU * (Real.log (N : ℝ)) ^ dU) := by
    exact mul_pos hc (mul_pos (Real.rpow_pos_of_pos hN0 _) (Real.rpow_pos_of_pos hlog _))
  have hUr' : phaseUpsilon α ς N ((N : ℝ) ^ (-ω)) .sgd /
      phaseUpsilon α ς N ((N : ℝ) ^ (-ω)) .svd =
      c * ((N : ℝ) ^ eU * (Real.log (N : ℝ)) ^ dU) := by
    simpa [eU, dU, mul_assoc] using hUr
  rw [hUr']
  unfold Sandwich
  constructor
  · rw [hX]
    calc (dLo * c) *
          (((N : ℝ) ^ phaseExpD α * (Real.log (N : ℝ)) ^ dD) *
            ((N : ℝ) ^ eU * (Real.log (N : ℝ)) ^ dU)) =
          (dLo * ((N : ℝ) ^ phaseExpD α * (Real.log (N : ℝ)) ^ dD)) *
            (c * ((N : ℝ) ^ eU * (Real.log (N : ℝ)) ^ dU)) := by ring
      _ ≤ phaseDN α N *
            (c * ((N : ℝ) ^ eU * (Real.log (N : ℝ)) ^ dU)) :=
        mul_le_mul_of_nonneg_right hDl hUp.le
  · rw [hX]
    calc phaseDN α N *
          (c * ((N : ℝ) ^ eU * (Real.log (N : ℝ)) ^ dU)) ≤
          (dHi * ((N : ℝ) ^ phaseExpD α * (Real.log (N : ℝ)) ^ dD)) *
            (c * ((N : ℝ) ^ eU * (Real.log (N : ℝ)) ^ dU)) :=
        mul_le_mul_of_nonneg_right hDh hUp.le
      _ = (dHi * c) *
          (((N : ℝ) ^ phaseExpD α * (Real.log (N : ℝ)) ^ dD) *
            ((N : ℝ) ^ eU * (Real.log (N : ℝ)) ^ dU)) := by ring

end Muon.Phase
