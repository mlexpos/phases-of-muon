import Mathlib
import Muon.Phase.Unified
import Muon.Phase.AccuracyFirst
import Muon.Phase.Winners

/-!
# Appendix H: the accuracy-exponent map and the phase diagram (task L-H.17)

Snapshot `cr-2026-10-23`. Source: `sections/07-phase-comparison/section.tex`, subsection
"The accuracy exponent" (l.1840–1850 set-up of `S(ω)`, `𝖤`, `𝖱`; l.1867–1871 `ω_c`;
`thm:app-phase-omega` l.1852–1861; `cor:app-phase-omega-winners`
l.1873–1894).
Card: `sections/07-phase-comparison/CARD.md` §2, §3 (rows `omega`, `omega-winners`),
§5 (L-H.17), §6.

Standing assumptions of the source, carried into every statement: `α > 0`, `p = α + ς > 1`
(`hp : 1 < α + ς`), `T ≥ 4` (`hT`), and the accuracy exponent `ω > 0` with
`ε = N^{-ω}`
(`hω0 : 0 < ω`).

Encoding decisions:
* `𝖱` is `phaseR` (`Winners`), evaluated at `ε = N^{-ω}`. The source says `𝖱` does not depend
  on `B` (`eqn:app-phase-clockint`); no Lean statement assumes this. Every statement quantifies
  over arbitrary `B N ≥ N`: for pointwise (`ℕ`-indexed) bounds, `B` is a universally quantified
  integer; for limit statements, `B : ℕ → ℕ` is an arbitrary sequence (`PhaseOmegaSeq`).
* Lean junk values: every ratio of hitting times is paired with `phaseOmegaTimesOK` (both first
  hits attained, both positive), so `toReal ⊤ = 0` and `x / 0 = 0` cannot make a claim vacuous
  or spuriously true. The corollary's limit claims carry `phaseOmegaAttained`.
* `S(ω)` is `phaseOmegaS`, `𝖤` is `phaseSetE`, `ω_c` is `phaseOmegaC` (its `ς ≥ 1` branch is
  `winnersOmegaC`, `Winners`). `Υ`, `e_D`, `χ`, `L`, `D_N`, `ρ_N`, `K_A`, `K_c`, `π^{3/2}` are
  reused: `phaseUpsilon`, `phaseExpD`, `phaseChi`, `phaseLogPow`, `phaseDN`, `phaseRhoN`,
  `phaseKA`, `phaseKc` (`Unified`, `AccuracyFirst`).
* "SGD wins", "SVD wins", "balanced" are `Tendsto 𝖱 atTop (𝓝 0)`, `Tendsto 𝖱 atTop atTop`,
  `phaseOmegaOrderU α ς T ω (fun _ => 1)` (that is `𝖱 ≍ 1`, constants uniform
  in the sequence), following the source's trichotomy
  "`𝖱 → ∞`, `𝖱 → 0`, or `𝖱 ≍ 1`". Orders `≍ log N` and `≍ 1/log N` use `phaseOrderOf`.
-/

set_option linter.style.longLine false

open MeasureTheory Set Filter Topology Asymptotics
open scoped ENNReal NNReal

noncomputable section

namespace Muon.Phase

/-! ## Exponents, sets and the threshold `ω_c` of the accuracy-exponent map -/

/-- The exponent `S(ω) = e_D + χ min{ω, p-1}` of the accuracy-exponent map, with `p = α + ς`.

Parametrize the accuracy by $\epsilon=N^{-\omega}$ with $\omega>0$. Then
$\omega>p-1$ is the frozen regime, and $\omega<p-1$ lies above the accuracy
scale. Put
\[
S(\omega)\defeq e_D+\chi\min\{\omega,p-1\},\qquad
\mathsf E\defeq\{\alpha=1,\ \texp\ge1\}\cup\{\alpha=\tfrac12,\ \texp\ge\tfrac32\} ,
\]
and let $\mathsf R\defeq t^{\text{s-SGD}}_{T\epsilon}/t^{\text{s-SVD}}_{T\epsilon}$ at $\epsilon=N^{-\omega}$,
with arbitrary integers $B_N\ge N$. By \cref{eqn:app-phase-chi},
$\chi\min\{\omega,p-1\}=\min\{\omega/(p-1),1\}\cdot\chi(p-1)$ is
$\frac\alpha2$, $\frac{\alpha+1-\texp}2$ or $0$ times $\min\{\omega/(p-1),1\}$. -/
def phaseOmegaS (α ς ω : ℝ) : ℝ := phaseExpD α + phaseChi α ς * min ω (α + ς - 1)

/-- The set `𝖤 = {α = 1, ς ≥ 1} ∪ {α = 1/2, ς ≥ 3/2}` of the accuracy-exponent map, excluded
from `thm:app-phase-omega`(ii) (the window of the power sums; source l.1841–1846). -/
def phaseSetE (α ς : ℝ) : Prop := (α = 1 ∧ 1 ≤ ς) ∨ (α = 1 / 2 ∧ 3 / 2 ≤ ς)

/-- The threshold `ω_c` of `eqn:app-phase-omegac` (for `1 < α < 2`, `ς < 2α - 1`). The branch
`1 ≤ ς` is `winnersOmegaC`.

\begin{equation}\label{eqn:app-phase-omegac}
\omega_c\defeq\begin{cases}\dfrac{(2-\alpha)(p-1)}{\alpha},&\texp<1,\\[6pt]
\dfrac{(2-\alpha)(p-1)}{\alpha+1-\texp},&1\le\texp<2\alpha-1,\end{cases}
\qquad\text{so that}\quad0<\omega_c<p-1 .
\end{equation} -/
def phaseOmegaC (α ς : ℝ) : ℝ :=
  if ς < 1 then (2 - α) * (α + ς - 1) / α else winnersOmegaC α ς

/-! ## Sequence-level objects -/

/-- The step-time ratio `𝖱 = t^{s-SGD}_{Tε} / t^{s-SVD}_{Tε}` at `ε = N^{-ω}` for a sequence of
matched models indexed by `N`. -/
def phaseOmegaSeqR (T ω : ℝ) (mS mG : (N : ℕ) → RowModel (Fin N)) (QS QG : ℕ → ℝ → ℝ) :
    ℕ → ℝ :=
  fun N => phaseR T ((N : ℝ) ^ (-ω)) (mS N) (mG N) (QS N) (QG N)

/-- Lean-side validity of one ratio `𝖱` at a fixed accuracy `ε`: both first hits are attained
(`≠ ⊤`) and positive. Without it, `toReal ⊤ = 0` and `x / 0 = 0` make the ratio junk. -/
def phaseOmegaTimesOK (T ε : ℝ) {N : ℕ} (mS mG : RowModel (Fin N)) (QS QG : ℝ → ℝ) : Prop :=
  stepHit mS QS T ε ≠ ⊤ ∧ stepHit mG QG T ε ≠ ⊤ ∧
    0 < (stepHit mS QS T ε).toReal ∧ 0 < (stepHit mG QG T ε).toReal

/-- The sequence hypotheses of the accuracy-exponent map: `B N ≥ N` for every `N` (arbitrary,
`B_N ≥ N` of the source), and for every `N ≥ 1` the matched SignSVD and SignSGD models at
`ε = N^{-ω}` with Volterra solutions (`def:app-phase-arrays`, `thm:app-phase-hitting`). -/
def PhaseOmegaSeq (α ς ω : ℝ) (B : ℕ → ℕ) (mS mG : (N : ℕ) → RowModel (Fin N))
    (QS QG : ℕ → ℝ → ℝ) : Prop :=
  (∀ N : ℕ, N ≤ B N) ∧ ∀ N : ℕ, 1 ≤ N →
    IsMatchedModel (phaseKindArrays α ς N (B N) .svd) (mS N) ((N : ℝ) ^ (-ω)) ∧
      IsVolterraSol (mS N) (QS N) ∧
      IsMatchedModel (phaseKindArrays α ς N (B N) .sgd) (mG N) ((N : ℝ) ^ (-ω)) ∧
      IsVolterraSol (mG N) (QG N)

/-- Eventually (as `N → ∞`) every step-time ratio of the sequence is valid in the sense of
`phaseOmegaTimesOK`. -/
def phaseOmegaAttained (T ω : ℝ) (mS mG : (N : ℕ) → RowModel (Fin N)) (QS QG : ℕ → ℝ → ℝ) :
    Prop :=
  ∀ᶠ N : ℕ in atTop, phaseOmegaTimesOK T ((N : ℝ) ^ (-ω)) (mS N) (mG N) (QS N) (QG N)

/-- `X ≍ R` along `N → ∞`: there are constants `0 < cLo ≤ cHi` with `cLo X N ≤ R N ≤ cHi X N`
eventually. -/
def phaseOrderOf (X R : ℕ → ℝ) : Prop :=
  ∃ cLo cHi : ℝ, 0 < cLo ∧ cLo ≤ cHi ∧ ∀ᶠ N : ℕ in atTop, Sandwich cLo cHi (X N) (R N)

/-- The uniform order `X ≍ 𝖱` of the accuracy-exponent map: the constants `0 < cLo ≤ cHi`
depend only on `α, ς, T, ω` (not on the sequence), and the bounds hold for every sequence
`B_N ≥ N` and every matched sequence of models (source l.1848; CARD §6.4 order
`∃ c₋ c₊, ∀ sequence, ∀ᶠ N`). Used for the balanced and order clauses of the corollary. -/
def phaseOmegaOrderU (α ς T ω : ℝ) (X : ℕ → ℝ) : Prop :=
  ∃ cLo cHi : ℝ, 0 < cLo ∧ cLo ≤ cHi ∧
    ∀ (B : ℕ → ℕ) (mS mG : (N : ℕ) → RowModel (Fin N)) (QS QG : ℕ → ℝ → ℝ),
      PhaseOmegaSeq α ς ω B mS mG QS QG →
        ∀ᶠ N : ℕ in atTop, Sandwich cLo cHi (X N) (phaseOmegaSeqR T ω mS mG QS QG N)

/-! ## Helpers for part (i) (proved from the frozen-regime sequence statements) -/

private lemma om_nonneg_JN (N : ℕ) (p q : ℝ) : 0 ≤ JN N p q := by
  unfold JN
  exact setIntegral_nonneg measurableSet_Ioi (fun u _ => Real.sqrt_nonneg _)

private lemma om_Hsum_pos (a : ℝ) {N : ℕ} (hN : 1 ≤ N) : 0 < Hsum a N := by
  unfold Hsum
  apply Finset.sum_pos
  · intro i hi
    have hi1 : (1 : ℝ) ≤ (i : ℝ) := by exact_mod_cast (Finset.mem_Icc.1 hi).1
    exact Real.rpow_pos_of_pos (by linarith) _
  · exact ⟨1, Finset.mem_Icc.2 ⟨le_refl _, hN⟩⟩

private lemma om_muBar_pos (α : ℝ) {N : ℕ} (hN : 1 ≤ N) : 0 < muBarOf α N := by
  unfold muBarOf
  exact div_pos (om_Hsum_pos α hN) (Nat.cast_pos.2 (by omega))

private lemma om_svdS (α ς : ℝ) (hα : 0 < α) (hp : 1 < α + ς) {N B : ℕ} (hN : 1 ≤ N)
    (hNB : N ≤ B) : 0 < (svdArrays α ς N B).S * svdT0 N B := by
  have hγ : 0 < gammaRat N B := div_pos (Nat.cast_pos.2 (by omega)) (Nat.cast_pos.2 (by omega))
  rw [(prop_app_phase_prefactors_i α ς N B hα hp hN hNB 1 one_pos).1]
  unfold svdT0
  exact mul_pos (mul_pos (mul_pos (by norm_num) (Real.sqrt_pos.2 hγ)) (om_Hsum_pos _ hN))
    (Real.sqrt_pos.2 hγ)

private lemma om_sgdS (α ς : ℝ) (hα : 0 < α) (hp : 1 < α + ς) {N B : ℕ} (hN : 1 ≤ N)
    (hNB : N ≤ B) : 0 < (sgdArrays α ς N B).S * sgdT0 α N B := by
  have hN0 : (0 : ℝ) < N := Nat.cast_pos.2 (by omega)
  have hB0 : (0 : ℝ) < B := Nat.cast_pos.2 (by omega)
  have hX : 0 < Real.pi * muBarOf α N / (B : ℝ) :=
    div_pos (mul_pos Real.pi_pos (om_muBar_pos α hN)) hB0
  rw [(prop_app_phase_prefactors_i α ς N B hα hp hN hNB 1 one_pos).2.2.1]
  unfold sgdT0
  exact mul_pos (mul_pos (div_pos (pow_pos hN0 2) two_pos) (Real.sqrt_pos.2 hX))
    (Real.sqrt_pos.2 hX)

private lemma om_shift_eventually {P : ℕ → Prop} (h : ∀ᶠ n in atTop, P (n + 1)) :
    ∀ᶠ N in atTop, P N := by
  obtain ⟨a, ha⟩ := Filter.eventually_atTop.1 h
  refine Filter.eventually_atTop.2 ⟨a + 1, fun N hN => ?_⟩
  have := ha (N - 1) (by omega)
  rwa [Nat.sub_add_cancel (by omega : 1 ≤ N)] at this

private lemma om_shift_equiv {u v : ℕ → ℝ}
    (h : Asymptotics.IsEquivalent atTop (fun n => u (n + 1)) (fun n => v (n + 1))) :
    Asymptotics.IsEquivalent atTop u v := by
  unfold Asymptotics.IsEquivalent at h ⊢
  rw [Asymptotics.isLittleO_iff] at h ⊢
  intro c hc
  have h2 := h hc
  exact om_shift_eventually (P := fun N => ‖(u - v) N‖ ≤ c * ‖v N‖) h2

private lemma om_pos_of_equiv {u v : ℕ → ℝ} (huv : Asymptotics.IsEquivalent atTop u v)
    (hv : ∀ᶠ n in atTop, 0 < v n) : ∀ᶠ n in atTop, 0 < u n := by
  have hz : ∀ᶠ n in atTop, v n ≠ 0 := by
    filter_upwards [hv] with n hn using hn.ne'
  have h1 := (Asymptotics.isEquivalent_iff_tendsto_one hz).1 huv
  have h2 : ∀ᶠ n in atTop, (1 / 2 : ℝ) < u n / v n := (tendsto_order.1 h1).1 (1 / 2) (by norm_num)
  filter_upwards [h2, hv] with n h2n hvn
  have h3 : 0 < u n / v n * v n := mul_pos (by linarith) hvn
  rwa [div_mul_cancel₀ _ hvn.ne'] at h3

/-- Core of part (i): the attainment and the asymptotic `𝖱 ~ ρ_N`, from `thm_app_phase_frozen`
applied to the shifted sequence `n ↦ n + 1` (so that `N ≥ 1`). -/
private lemma om_core (α ς T ω : ℝ) (hα : 0 < α) (hp : 1 < α + ς) (hT : 4 ≤ T)
    (hω : α + ς - 1 < ω) (B : ℕ → ℕ) (mS mG : (N : ℕ) → RowModel (Fin N))
    (QS QG : ℕ → ℝ → ℝ) (hM : PhaseOmegaSeq α ς ω B mS mG QS QG) :
    (∀ᶠ N : ℕ in atTop, phaseOmegaTimesOK T ((N : ℝ) ^ (-ω)) (mS N) (mG N) (QS N) (QG N)) ∧
      Asymptotics.IsEquivalent atTop (fun N : ℕ => phaseOmegaSeqR T ω mS mG QS QG N)
        (fun N : ℕ => phaseRhoN α ς N) := by
  have hN1 : ∀ n : ℕ, 1 ≤ n + 1 := fun n => by omega
  have hx : ∀ N : ℕ, 1 ≤ N →
      phaseX (α + ς) N ((N : ℝ) ^ (-ω)) = (N : ℝ) ^ (-(ω - (α + ς - 1))) := by
    intro N hN
    have hN0 : (0 : ℝ) < N := Nat.cast_pos.2 (by omega)
    unfold phaseX phaseEpsN
    rw [← Real.rpow_sub hN0]
    congr 1
    ring
  let D : FrozenSeq α ς :=
    { N := fun n => n + 1
      B := fun n => B (n + 1)
      ε := fun n => ((n + 1 : ℕ) : ℝ) ^ (-ω)
      tendsto_N := tendsto_add_atTop_nat 1
      le_B := fun n => ⟨hN1 n, hM.1 (n + 1)⟩
      ε_pos := fun n => Real.rpow_pos_of_pos (Nat.cast_pos.2 (by omega)) _
      x_tendsto := by
        have hc : 0 < ω - (α + ς - 1) := by linarith
        have hlim := (tendsto_rpow_neg_atTop hc).comp
          (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1))
        refine Tendsto.congr (fun n => ?_) hlim
        exact (hx (n + 1) (hN1 n)).symm
      mS := fun n => mS (n + 1)
      mG := fun n => mG (n + 1)
      QS := fun n => QS (n + 1)
      QG := fun n => QG (n + 1)
      matchS := fun n => (hM.2 (n + 1) (hN1 n)).1
      matchG := fun n => (hM.2 (n + 1) (hN1 n)).2.2.1
      volS := fun n => (hM.2 (n + 1) (hN1 n)).2.1
      volG := fun n => (hM.2 (n + 1) (hN1 n)).2.2.2 }
  have hIII := thm_app_phase_frozen_iii hα hp hT D
  have hII := thm_app_phase_frozen_ii hα hp hT D
  have hIV := thm_app_phase_frozen_iv hα hp hT D
  have hJS : ∀ᶠ n in atTop, 0 < JN (n + 1) (α + ς) (α / 2) := by
    have h2 : ∀ᶠ n in atTop, (1 / 2 : ℝ) < phaseClockI (QS (n + 1)) (svdT0 (n + 1) (B (n + 1))) T
        (((n + 1 : ℕ) : ℝ) ^ (-ω)) / JN (n + 1) (α + ς) (α / 2) :=
      (tendsto_order.1 hII.1).1 (1 / 2) (by norm_num)
    filter_upwards [h2] with n hn
    rcases (om_nonneg_JN (n + 1) (α + ς) (α / 2)).lt_or_eq with h | h
    · exact h
    · rw [← h, div_zero] at hn
      norm_num at hn
  have hJG : ∀ᶠ n in atTop, 0 < JN (n + 1) (α + ς) α := by
    have h2 : ∀ᶠ n in atTop, (1 / 2 : ℝ) < phaseClockI (QG (n + 1)) (sgdT0 α (n + 1) (B (n + 1))) T
        (((n + 1 : ℕ) : ℝ) ^ (-ω)) / JN (n + 1) (α + ς) α :=
      (tendsto_order.1 hII.2).1 (1 / 2) (by norm_num)
    filter_upwards [h2] with n hn
    rcases (om_nonneg_JN (n + 1) (α + ς) α).lt_or_eq with h | h
    · exact h
    · rw [← h, div_zero] at hn
      norm_num at hn
  have hvS : ∀ᶠ n in atTop, 0 < (svdArrays α ς (n + 1) (B (n + 1))).S * svdT0 (n + 1) (B (n + 1))
      * JN (n + 1) (α + ς) (α / 2) / (2 * Real.sqrt (((n + 1 : ℕ) : ℝ) ^ (-ω))) := by
    filter_upwards [hJS] with n hn
    apply div_pos (mul_pos (om_svdS α ς hα hp (hN1 n) (hM.1 (n + 1))) hn)
    exact mul_pos two_pos (Real.sqrt_pos.2 (Real.rpow_pos_of_pos (Nat.cast_pos.2 (by omega)) _))
  have hvG : ∀ᶠ n in atTop, 0 < (sgdArrays α ς (n + 1) (B (n + 1))).S * sgdT0 α (n + 1) (B (n + 1))
      * JN (n + 1) (α + ς) α / (2 * Real.sqrt (((n + 1 : ℕ) : ℝ) ^ (-ω))) := by
    filter_upwards [hJG] with n hn
    apply div_pos (mul_pos (om_sgdS α ς hα hp (hN1 n) (hM.1 (n + 1))) hn)
    exact mul_pos two_pos (Real.sqrt_pos.2 (Real.rpow_pos_of_pos (Nat.cast_pos.2 (by omega)) _))
  have hPS := om_pos_of_equiv hIII.1 hvS
  have hPG := om_pos_of_equiv hIII.2 hvG
  have hAtt : ∀ᶠ n in atTop, phaseOmegaTimesOK T (((n + 1 : ℕ) : ℝ) ^ (-ω))
      (mS (n + 1)) (mG (n + 1)) (QS (n + 1)) (QG (n + 1)) := by
    filter_upwards [hPS, hPG] with n h1 h2
    refine ⟨?_, ?_, h1, h2⟩
    · intro h
      rw [h, ENNReal.toReal_top] at h1
      exact lt_irrefl _ h1
    · intro h
      rw [h, ENNReal.toReal_top] at h2
      exact lt_irrefl _ h2
  have hR : Asymptotics.IsEquivalent atTop
      (fun n : ℕ => phaseR T (((n + 1 : ℕ) : ℝ) ^ (-ω)) (mS (n + 1)) (mG (n + 1))
        (QS (n + 1)) (QG (n + 1)))
      (fun n : ℕ => phaseRhoN α ς (n + 1)) := hIV
  refine ⟨om_shift_eventually (P := fun N => phaseOmegaTimesOK T ((N : ℝ) ^ (-ω)) (mS N) (mG N)
    (QS N) (QG N)) hAtt, ?_⟩
  exact om_shift_equiv (u := fun N : ℕ => phaseOmegaSeqR T ω mS mG QS QG N)
    (v := fun N : ℕ => phaseRhoN α ς N) hR

/-! ## Helpers for parts (ii), (iii) (from the frozen unified-ratio and unified statements) -/

private lemma om_r_svd (α ς : ℝ) : phaseKindR α ς PhaseKind.svd = (α + ς - 1) / α := by
  simp only [phaseKindR, rq, phaseKindQ]
  congr 1
  ring

private lemma om_r_sgd (α ς : ℝ) : phaseKindR α ς PhaseKind.sgd = (α + ς - 1) / (2 * α) := by
  simp only [phaseKindR, rq, phaseKindQ]

private lemma om_inU_of_notE (α ς : ℝ) (hE : ¬ phaseSetE α ς) :
    phaseInU α ς PhaseKind.svd ∧ phaseInU α ς PhaseKind.sgd := by
  unfold phaseSetE at hE
  push_neg at hE
  obtain ⟨h1, h2⟩ := hE
  constructor
  · show phaseKindR α ς PhaseKind.svd < 1 ∨ α ≠ 1
    rw [om_r_svd]
    by_cases hA : α = 1
    · have hς := h1 hA
      left
      rw [hA, div_lt_one (by norm_num : (0 : ℝ) < 1)]
      linarith
    · exact Or.inr hA
  · show phaseKindR α ς PhaseKind.sgd < 1 ∨ (α ≠ 1 / 2 ∧ α ≠ 1)
    rw [om_r_sgd]
    by_cases hA : α = 1 / 2
    · have hς := h2 hA
      left
      rw [hA, div_lt_one (by norm_num : (0 : ℝ) < 2 * (1 / 2))]
      linarith
    by_cases hB : α = 1
    · have hς := h1 hB
      left
      rw [hB, div_lt_one (by norm_num : (0 : ℝ) < 2 * 1)]
      linarith
    · exact Or.inr ⟨hA, hB⟩

private lemma om_eps_small (ω ε0 : ℝ) (hω : 0 < ω) (hε : 0 < ε0) :
    ∃ N1 : ℕ, ∀ N : ℕ, N1 ≤ N → (N : ℝ) ^ (-ω) < ε0 := by
  have h : Tendsto (fun N : ℕ => (N : ℝ) ^ (-ω)) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop hω).comp tendsto_natCast_atTop_atTop
  obtain ⟨N1, hN1⟩ := Filter.eventually_atTop.1 (h.eventually (gt_mem_nhds hε))
  exact ⟨N1, hN1⟩

private lemma om_X_pos (α ς ω : ℝ) {N : ℕ} (hN : 2 ≤ N) :
    0 < (N : ℝ) ^ (phaseExpD α + phaseChi α ς * min ω (α + ς - 1)) *
      (Real.log (N : ℝ)) ^ phaseLogPow α ς := by
  have hN1 : (1 : ℝ) < N := by exact_mod_cast (by omega : 1 < N)
  have hN0 : (0 : ℝ) < N := by linarith
  exact mul_pos (Real.rpow_pos_of_pos hN0 _) (Real.rpow_pos_of_pos (Real.log_pos hN1) _)

private lemma om_upsilon_pos (α ς : ℝ) (j : PhaseKind) {N : ℕ} (hN : 1 ≤ N) {ε : ℝ}
    (hε : 0 < ε) (hr0 : 0 < phaseKindR α ς j) (hr1 : phaseKindR α ς j < 1) :
    0 < phaseUpsilon α ς N ε j := by
  unfold phaseUpsilon
  rw [if_pos hr1]
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  exact lt_min (Real.rpow_pos_of_pos hε _) (Real.rpow_pos_of_pos hN0 _)

private lemma om_ok_of_pos {N : ℕ} (T ε : ℝ) (mS mG : RowModel (Fin N)) (QS QG : ℝ → ℝ)
    (hs : 0 < (stepHit mS QS T ε).toReal) (hg : 0 < (stepHit mG QG T ε).toReal) :
    phaseOmegaTimesOK T ε mS mG QS QG := by
  refine ⟨?_, ?_, hs, hg⟩
  · intro ht
    rw [ht, ENNReal.toReal_top] at hs
    exact lt_irrefl _ hs
  · intro ht
    rw [ht, ENNReal.toReal_top] at hg
    exact lt_irrefl _ hg

private lemma om_ok_of_ratio_pos {N : ℕ} (T ε : ℝ) (mS mG : RowModel (Fin N)) (QS QG : ℝ → ℝ)
    (h : 0 < (stepHit mG QG T ε).toReal / (stepHit mS QS T ε).toReal) :
    phaseOmegaTimesOK T ε mS mG QS QG := by
  rcases div_pos_iff.1 h with ⟨hg, hs⟩ | ⟨hg, _⟩
  · exact om_ok_of_pos T ε mS mG QS QG hs hg
  · exact absurd hg (not_lt.2 ENNReal.toReal_nonneg)

private lemma om_chain {X Y R cLo1 cHi1 cLo2 cHi2 : ℝ} (hc1 : 0 < cLo1) (hle1 : cLo1 ≤ cHi1)
    (hc2 : 0 < cLo2) (hle2 : cLo2 ≤ cHi2) (hV : Sandwich cLo2 cHi2 X Y)
    (hR : Sandwich cLo1 cHi1 Y R) :
    cLo1 * cLo2 * X ≤ R ∧ R ≤ cHi1 * cHi2 * X := by
  obtain ⟨hvl, hvh⟩ := hV
  obtain ⟨hrl, hrh⟩ := hR
  constructor
  · calc cLo1 * cLo2 * X = cLo1 * (cLo2 * X) := by ring
      _ ≤ cLo1 * Y := mul_le_mul_of_nonneg_left hvl hc1.le
      _ ≤ R := hrl
  · calc R ≤ cHi1 * Y := hrh
      _ ≤ cHi1 * (cHi2 * X) := mul_le_mul_of_nonneg_left hvh (by linarith)
      _ = cHi1 * cHi2 * X := by ring

private lemma om_upper {X Y R cHi1 cHi2 : ℝ} (hc1 : 0 ≤ cHi1) (hR : R ≤ cHi1 * Y)
    (hY : Y ≤ cHi2 * X) : R ≤ cHi1 * cHi2 * X := by
  calc R ≤ cHi1 * Y := hR
    _ ≤ cHi1 * (cHi2 * X) := mul_le_mul_of_nonneg_left hY hc1
    _ = cHi1 * cHi2 * X := by ring

/-! ## Declarations of record -/

/-- Label `thm:app-phase-omega`, part (i): if `ω > p - 1` (the frozen regime), then `𝖱 ~ ρ_N`
along the sequence, for arbitrary `B_N ≥ N`. Snapshot `cr-2026-10-23`. Statement (verbatim,
`sections/07-phase-comparison/section.tex`, l.1852–1861):

\begin{theorem}[Accuracy-exponent map]\label{thm:app-phase-omega}
Fix $\alpha>0$, $\texp$ with $p=\alpha+\texp>1$, $\omega>0$ and $T\ge4$. As
$N\to\infty$:
\begin{enumerate}[label=(\roman*)]
\item if $\omega>p-1$, then $\mathsf R\sim\rho_N$, so every conclusion of
\cref{thm:app-phase-accfirst,cor:app-phase-accfirst-winners} holds for $\mathsf R$;
\item if $(\alpha,\texp)\notin\mathsf E$, then $\mathsf R\asymp N^{S(\omega)}(\log N)^L$;
\item if $\alpha=1$ and $1\le\texp<2$, then $\mathsf R\lesssim N^{S(\omega)}(\log N)^L$.
\end{enumerate}
\end{theorem} -/
theorem thm_app_phase_omega_i (α ς T ω : ℝ) (hα : 0 < α) (hp : 1 < α + ς) (hT : 4 ≤ T)
    (hω0 : 0 < ω) (hω : α + ς - 1 < ω) (B : ℕ → ℕ) (mS mG : (N : ℕ) → RowModel (Fin N))
    (QS QG : ℕ → ℝ → ℝ) (hM : PhaseOmegaSeq α ς ω B mS mG QS QG) :
    phaseOmegaAttained T ω mS mG QS QG ∧
      Asymptotics.IsEquivalent atTop (phaseOmegaSeqR T ω mS mG QS QG)
        (fun N : ℕ => phaseRhoN α ς N) := by
  exact om_core α ς T ω hα hp hT hω B mS mG QS QG hM

/-- Label `thm:app-phase-omega`, part (i), the transfer clause: "every conclusion of
`thm:app-phase-accfirst` and `cor:app-phase-accfirst-winners` holds for `𝖱`" is stated here for
the limit conclusions (finite limit `c`, and divergence to `+∞`): `ρ_N → c` iff `𝖱 → c`, and
`ρ_N → +∞` iff `𝖱 → +∞`. Snapshot `cr-2026-10-23`. Statement of part (i) verbatim:

\begin{theorem}[Accuracy-exponent map]\label{thm:app-phase-omega}
Fix $\alpha>0$, $\texp$ with $p=\alpha+\texp>1$, $\omega>0$ and $T\ge4$. As
$N\to\infty$:
\begin{enumerate}[label=(\roman*)]
\item if $\omega>p-1$, then $\mathsf R\sim\rho_N$, so every conclusion of
\cref{thm:app-phase-accfirst,cor:app-phase-accfirst-winners} holds for $\mathsf R$;
\item if $(\alpha,\texp)\notin\mathsf E$, then $\mathsf R\asymp N^{S(\omega)}(\log N)^L$;
\item if $\alpha=1$ and $1\le\texp<2$, then $\mathsf R\lesssim N^{S(\omega)}(\log N)^L$.
\end{enumerate}
\end{theorem} -/
theorem thm_app_phase_omega_i_transfer (α ς T ω : ℝ) (hα : 0 < α) (hp : 1 < α + ς)
    (hT : 4 ≤ T) (hω0 : 0 < ω) (hω : α + ς - 1 < ω) (B : ℕ → ℕ)
    (mS mG : (N : ℕ) → RowModel (Fin N)) (QS QG : ℕ → ℝ → ℝ)
    (hM : PhaseOmegaSeq α ς ω B mS mG QS QG) :
    (∀ c : ℝ, Tendsto (fun N : ℕ => phaseRhoN α ς N) atTop (𝓝 c) ↔
        Tendsto (phaseOmegaSeqR T ω mS mG QS QG) atTop (𝓝 c)) ∧
      (Tendsto (fun N : ℕ => phaseRhoN α ς N) atTop atTop ↔
        Tendsto (phaseOmegaSeqR T ω mS mG QS QG) atTop atTop) := by
  have hEq := (om_core α ς T ω hα hp hT hω B mS mG QS QG hM).2
  exact ⟨fun c => hEq.symm.tendsto_nhds_iff, hEq.symm.tendsto_atTop_iff⟩

/-- Label `thm:app-phase-omega`, part (ii): if `(α, ς) ∉ 𝖤`, then `𝖱 ≍ N^{S(ω)} (log N)^L` with
constants depending only on `α, ς, T, ω`, uniformly in `B ≥ N`. Snapshot `cr-2026-10-23`.
Statement (verbatim, `sections/07-phase-comparison/section.tex`, l.1852–1861):

\begin{theorem}[Accuracy-exponent map]\label{thm:app-phase-omega}
Fix $\alpha>0$, $\texp$ with $p=\alpha+\texp>1$, $\omega>0$ and $T\ge4$. As
$N\to\infty$:
\begin{enumerate}[label=(\roman*)]
\item if $\omega>p-1$, then $\mathsf R\sim\rho_N$, so every conclusion of
\cref{thm:app-phase-accfirst,cor:app-phase-accfirst-winners} holds for $\mathsf R$;
\item if $(\alpha,\texp)\notin\mathsf E$, then $\mathsf R\asymp N^{S(\omega)}(\log N)^L$;
\item if $\alpha=1$ and $1\le\texp<2$, then $\mathsf R\lesssim N^{S(\omega)}(\log N)^L$.
\end{enumerate}
\end{theorem} -/
theorem thm_app_phase_omega_ii (α ς T ω : ℝ) (hα : 0 < α) (hp : 1 < α + ς) (hT : 4 ≤ T)
    (hω0 : 0 < ω) (hE : ¬ phaseSetE α ς) :
    ∃ (N0 : ℕ) (cLo cHi : ℝ), 0 < cLo ∧ cLo ≤ cHi ∧
      ∀ (N : ℕ), N0 ≤ N → ∀ (B : ℕ), N ≤ B →
        ∀ (mS mG : RowModel (Fin N)) (QS QG : ℝ → ℝ),
          IsMatchedModel (phaseKindArrays α ς N B .svd) mS ((N : ℝ) ^ (-ω)) →
          IsVolterraSol mS QS →
          IsMatchedModel (phaseKindArrays α ς N B .sgd) mG ((N : ℝ) ^ (-ω)) →
          IsVolterraSol mG QG →
          phaseOmegaTimesOK T ((N : ℝ) ^ (-ω)) mS mG QS QG ∧
            Sandwich cLo cHi
              ((N : ℝ) ^ phaseOmegaS α ς ω * (Real.log (N : ℝ)) ^ phaseLogPow α ς)
              (phaseR T ((N : ℝ) ^ (-ω)) mS mG QS QG) := by
  obtain ⟨hUs, hUg⟩ := om_inU_of_notE α ς hE
  obtain ⟨N0r, ε0r, cLo1, cHi1, hε0r, hc1, hle1, hr⟩ :=
    cor_app_phase_unified_ratio_i α ς T hα hp hT hUs hUg
  obtain ⟨N0v, cLo2, cHi2, hc2, hle2, hv⟩ := cor_app_phase_unified_ratio_v α ς hα hp ω hω0
  obtain ⟨N1, hN1⟩ := om_eps_small ω ε0r hω0 hε0r
  refine ⟨max (max N0r N0v) (max N1 2), cLo1 * cLo2, cHi1 * cHi2, mul_pos hc1 hc2,
    mul_le_mul hle1 hle2 hc2.le (by linarith), ?_⟩
  intro N hN B hNB mS mG QS QG hmS hqS hmG hqG
  simp only [max_le_iff] at hN
  obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hN
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hεpos : 0 < (N : ℝ) ^ (-ω) := Real.rpow_pos_of_pos hNpos _
  have hR := hr N B ((N : ℝ) ^ (-ω)) mS mG QS QG h1 hNB hεpos (hN1 N h3) hmS hqS hmG hqG
  have hV := hv N h2
  have hS := om_chain hc1 hle1 hc2 hle2 hV hR
  have hX := om_X_pos α ς ω h4
  have hRpos : 0 < (stepHit mG QG T ((N : ℝ) ^ (-ω))).toReal /
      (stepHit mS QS T ((N : ℝ) ^ (-ω))).toReal :=
    lt_of_lt_of_le (mul_pos (mul_pos hc1 hc2) hX) hS.1
  exact ⟨om_ok_of_ratio_pos T _ mS mG QS QG hRpos, hS⟩

/-- Label `thm:app-phase-omega`, part (iii): if `α = 1` and `1 ≤ ς < 2`, then
`𝖱 ≲ N^{S(ω)} (log N)^L` with a constant depending only on `α, ς, T, ω`, uniformly in `B ≥ N`.
Snapshot `cr-2026-10-23`. Statement (verbatim, `sections/07-phase-comparison/section.tex`,
l.1852–1861):

\begin{theorem}[Accuracy-exponent map]\label{thm:app-phase-omega}
Fix $\alpha>0$, $\texp$ with $p=\alpha+\texp>1$, $\omega>0$ and $T\ge4$. As
$N\to\infty$:
\begin{enumerate}[label=(\roman*)]
\item if $\omega>p-1$, then $\mathsf R\sim\rho_N$, so every conclusion of
\cref{thm:app-phase-accfirst,cor:app-phase-accfirst-winners} holds for $\mathsf R$;
\item if $(\alpha,\texp)\notin\mathsf E$, then $\mathsf R\asymp N^{S(\omega)}(\log N)^L$;
\item if $\alpha=1$ and $1\le\texp<2$, then $\mathsf R\lesssim N^{S(\omega)}(\log N)^L$.
\end{enumerate}
\end{theorem} -/
theorem thm_app_phase_omega_iii (α ς T ω : ℝ) (hα : 0 < α) (hp : 1 < α + ς) (hT : 4 ≤ T)
    (hω0 : 0 < ω) (hα1 : α = 1) (hς1 : 1 ≤ ς) (hς2 : ς < 2) :
    ∃ (N0 : ℕ) (cHi : ℝ), 0 < cHi ∧
      ∀ (N : ℕ), N0 ≤ N → ∀ (B : ℕ), N ≤ B →
        ∀ (mS mG : RowModel (Fin N)) (QS QG : ℝ → ℝ),
          IsMatchedModel (phaseKindArrays α ς N B .svd) mS ((N : ℝ) ^ (-ω)) →
          IsVolterraSol mS QS →
          IsMatchedModel (phaseKindArrays α ς N B .sgd) mG ((N : ℝ) ^ (-ω)) →
          IsVolterraSol mG QG →
          phaseOmegaTimesOK T ((N : ℝ) ^ (-ω)) mS mG QS QG ∧
            phaseR T ((N : ℝ) ^ (-ω)) mS mG QS QG ≤
              cHi * ((N : ℝ) ^ phaseOmegaS α ς ω * (Real.log (N : ℝ)) ^ phaseLogPow α ς) := by
  subst hα1
  have hr0 : 0 < phaseKindR 1 ς PhaseKind.sgd := by
    rw [om_r_sgd]
    exact div_pos (by linarith) (by norm_num)
  have hr1 : phaseKindR 1 ς PhaseKind.sgd < 1 := by
    rw [om_r_sgd, div_lt_one (by norm_num : (0 : ℝ) < 2 * 1)]
    linarith
  have hUg : phaseInU 1 ς PhaseKind.sgd := Or.inl hr1
  obtain ⟨N0u, ε0u, cLo3, cHi3, hε0u, hc3, hle3, hu⟩ :=
    thm_app_phase_unified_iii 1 ς T hα hp hT PhaseKind.sgd hUg
  obtain ⟨N0q, ε0q, cHi1, hε0q, hc1, hq⟩ := cor_app_phase_unified_ratio_ii 1 ς T hα hp hT hUg
  obtain ⟨N0v, cLo2, cHi2, hc2, hle2, hv⟩ := cor_app_phase_unified_ratio_v 1 ς hα hp ω hω0
  obtain ⟨N1, hN1⟩ := om_eps_small ω (min ε0u ε0q) hω0 (lt_min hε0u hε0q)
  refine ⟨max (max N0u N0q) (max N0v (max N1 2)), cHi1 * cHi2,
    mul_pos hc1 (lt_of_lt_of_le hc2 hle2), ?_⟩
  intro N hN B hNB mS mG QS QG hmS hqS hmG hqG
  simp only [max_le_iff] at hN
  obtain ⟨⟨h1, h2⟩, h3, h4, h5⟩ := hN
  have hN1' : 1 ≤ N := by omega
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hεpos : 0 < (N : ℝ) ^ (-ω) := Real.rpow_pos_of_pos hNpos _
  have hmin := hN1 N h4
  obtain ⟨_, hG⟩ := hu N B ((N : ℝ) ^ (-ω)) mG QG h1 hNB hεpos
    (lt_of_lt_of_le hmin (min_le_left _ _)) hmG hqG
  obtain ⟨hGlo, _⟩ := hG
  have hGpos : 0 < (stepHit mG QG T ((N : ℝ) ^ (-ω))).toReal :=
    lt_of_lt_of_le
      (mul_pos hc3 (mul_pos (mul_pos (om_sgdS 1 ς hα hp hN1' hNB)
        (Real.rpow_pos_of_pos hεpos _)) (om_upsilon_pos 1 ς PhaseKind.sgd hN1' hεpos hr0 hr1)))
      hGlo
  obtain ⟨hSpos, _, hRle⟩ := hq N B ((N : ℝ) ^ (-ω)) mS mG QS QG h2 hNB hεpos
    (lt_of_lt_of_le hmin (min_le_right _ _)) hmS hqS hmG hqG
  obtain ⟨_, hYhi⟩ := hv N h3
  exact ⟨om_ok_of_pos T _ mS mG QS QG hSpos hGpos, om_upper hc1.le hRle hYhi⟩

private lemma om_chi_formula (α ς : ℝ) (hα : 0 < α) (hp : 1 < α + ς) :
    phaseChi α ς = if ς < 1 then α / (2 * (α + ς - 1))
      else if ς ≤ α + 1 then (α + 1 - ς) / (2 * (α + ς - 1)) else 0 := by
  have hd : 0 < α + ς - 1 := by linarith
  have hs : 1 / (2 * phaseKindR α ς .svd) = α / (2 * (α + ς - 1)) := by
    unfold phaseKindR phaseKindQ rq
    field_simp
  have hg : 1 / (2 * phaseKindR α ς .sgd) = α / (α + ς - 1) := by
    unfold phaseKindR phaseKindQ rq
    field_simp
  unfold phaseChi phaseKindE
  rw [hs, hg]
  split_ifs with h1 h2
  · rw [max_eq_right (by apply (le_div_iff₀ hd).2; linarith),
      max_eq_right (by apply (le_div_iff₀ (mul_pos two_pos hd)).2; linarith)]
    field_simp
    ring
  · rw [max_eq_right (by apply (le_div_iff₀ hd).2; linarith),
      max_eq_left (by apply (div_le_iff₀ (mul_pos two_pos hd)).2; linarith)]
    field_simp
    ring
  · rw [max_eq_left (by apply (div_le_iff₀ hd).2; linarith),
      max_eq_left (by apply (div_le_iff₀ (mul_pos two_pos hd)).2; linarith)]
    ring

private lemma om_S_upper (α ς ω : ℝ) (hα : 0 < α) (hp : 1 < α + ς) :
    phaseOmegaS α ς ω ≤ phaseExpD α +
      (if ς < 1 then α / 2 else if ς ≤ α + 1 then (α + 1 - ς) / 2 else 0) := by
  have hd : 0 < α + ς - 1 := by linarith
  have hχ : 0 ≤ phaseChi α ς := by
    rw [om_chi_formula α ς hα hp]
    split_ifs <;> first | (apply div_nonneg <;> linarith) | rfl
  calc phaseOmegaS α ς ω ≤ phaseExpD α + phaseChi α ς * (α + ς - 1) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left (min_le_right _ _) hχ)
    _ = _ := by
      rw [om_chi_formula α ς hα hp]
      split_ifs <;> field_simp <;> ring

private lemma om_seq_bounds (α ς T ω : ℝ) (hα : 0 < α) (hp : 1 < α + ς) (hT : 4 ≤ T)
    (hω : 0 < ω) (hE : ¬ phaseSetE α ς) :
    phaseOmegaOrderU α ς T ω
      (fun N : ℕ => (N : ℝ) ^ phaseOmegaS α ς ω * (Real.log (N : ℝ)) ^ phaseLogPow α ς) ∧
    ∀ (B : ℕ → ℕ) (mS mG : (N : ℕ) → RowModel (Fin N)) (QS QG : ℕ → ℝ → ℝ),
      PhaseOmegaSeq α ς ω B mS mG QS QG → phaseOmegaAttained T ω mS mG QS QG := by
  obtain ⟨N0, cLo, cHi, hc, hle, hb⟩ := thm_app_phase_omega_ii α ς T ω hα hp hT hω hE
  have hall : ∀ (B : ℕ → ℕ) (mS mG : (N : ℕ) → RowModel (Fin N)) (QS QG : ℕ → ℝ → ℝ),
      PhaseOmegaSeq α ς ω B mS mG QS QG →
      ∀ᶠ N : ℕ in atTop, phaseOmegaTimesOK T ((N : ℝ) ^ (-ω)) (mS N) (mG N) (QS N) (QG N) ∧
        Sandwich cLo cHi ((N : ℝ) ^ phaseOmegaS α ς ω *
          (Real.log (N : ℝ)) ^ phaseLogPow α ς) (phaseOmegaSeqR T ω mS mG QS QG N) := by
    intro B mS mG QS QG hM
    filter_upwards [eventually_ge_atTop (max N0 1)] with N hN
    obtain ⟨hs, hvs, hg, hvg⟩ := hM.2 N (le_trans (le_max_right _ _) hN)
    exact hb N (le_trans (le_max_left _ _) hN) (B N) (hM.1 N) _ _ _ _ hs hvs hg hvg
  exact ⟨⟨cLo, cHi, hc, hle, fun B mS mG QS QG hM => (hall B mS mG QS QG hM).mono
    (fun _ h => h.2)⟩, fun B mS mG QS QG hM => (hall B mS mG QS QG hM).mono (fun _ h => h.1)⟩

private lemma om_power_log_zero (s l : ℝ) (hs : s < 0) :
    Tendsto (fun N : ℕ => (N : ℝ) ^ s * (Real.log (N : ℝ)) ^ l) atTop (𝓝 0) := by
  have h := ((isLittleO_log_rpow_rpow_atTop l (neg_pos.2 hs)).tendsto_div_nhds_zero).comp
    tendsto_natCast_atTop_atTop
  apply h.congr'
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with N hN
  have hN0 : 0 ≤ (N : ℝ) := Nat.cast_nonneg _
  simp only [Function.comp_apply, Real.rpow_neg hN0, div_inv_eq_mul]
  ring

private lemma om_power_log_top (s l : ℝ) (hs : 0 < s) :
    Tendsto (fun N : ℕ => (N : ℝ) ^ s * (Real.log (N : ℝ)) ^ l) atTop atTop := by
  have h := om_power_log_zero (-s) (-l) (neg_lt_zero.2 hs)
  have hpos : ∀ᶠ N : ℕ in atTop,
      0 < (N : ℝ) ^ (-s) * (Real.log (N : ℝ)) ^ (-l) := by
    filter_upwards [eventually_ge_atTop (2 : ℕ)] with N hN
    have hN1 : (1 : ℝ) < N := by exact_mod_cast (by omega : 1 < N)
    exact mul_pos (Real.rpow_pos_of_pos (by linarith) _) (Real.rpow_pos_of_pos (Real.log_pos hN1) _)
  have ht := tendsto_inv_nhdsGT_zero.comp (tendsto_nhdsWithin_iff.2 ⟨h, hpos⟩)
  apply ht.congr'
  filter_upwards [eventually_ge_atTop (2 : ℕ)] with N hN
  have hN1 : (1 : ℝ) < N := by exact_mod_cast (by omega : 1 < N)
  simp [Real.rpow_neg (by linarith : (0 : ℝ) ≤ N),
    Real.rpow_neg (Real.log_pos hN1).le, mul_comm]

private lemma om_order_zero {α ς T ω : ℝ} {X : ℕ → ℝ}
    (ho : phaseOmegaOrderU α ς T ω X) (hx : Tendsto X atTop (𝓝 0))
    (B : ℕ → ℕ) (mS mG : (N : ℕ) → RowModel (Fin N)) (QS QG : ℕ → ℝ → ℝ)
    (hM : PhaseOmegaSeq α ς ω B mS mG QS QG) :
    Tendsto (phaseOmegaSeqR T ω mS mG QS QG) atTop (𝓝 0) := by
  obtain ⟨cLo, cHi, hc, hle, hb⟩ := ho
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' (g := fun N => cLo * X N)
    (h := fun N => cHi * X N) (by simpa using hx.const_mul cLo) (by simpa using hx.const_mul cHi)
  · exact (hb B mS mG QS QG hM).mono (fun _ h => h.1)
  · exact (hb B mS mG QS QG hM).mono (fun _ h => h.2)

private lemma om_order_top {α ς T ω : ℝ} {X : ℕ → ℝ}
    (ho : phaseOmegaOrderU α ς T ω X) (hx : Tendsto X atTop atTop)
    (B : ℕ → ℕ) (mS mG : (N : ℕ) → RowModel (Fin N)) (QS QG : ℕ → ℝ → ℝ)
    (hM : PhaseOmegaSeq α ς ω B mS mG QS QG) :
    Tendsto (phaseOmegaSeqR T ω mS mG QS QG) atTop atTop := by
  obtain ⟨cLo, cHi, hc, hle, hb⟩ := ho
  exact tendsto_atTop_mono' _ ((hb B mS mG QS QG hM).mono (fun _ h => h.1))
    (hx.const_mul_atTop hc)

private lemma om_zero_of_S (α ς T ω : ℝ) (hα : 0 < α) (hp : 1 < α + ς) (hT : 4 ≤ T)
    (hω0 : 0 < ω) (hE : ¬ phaseSetE α ς) (hS : phaseOmegaS α ς ω < 0)
    (B : ℕ → ℕ) (mS mG : (N : ℕ) → RowModel (Fin N)) (QS QG : ℕ → ℝ → ℝ)
    (hM : PhaseOmegaSeq α ς ω B mS mG QS QG) :
    Tendsto (phaseOmegaSeqR T ω mS mG QS QG) atTop (𝓝 0) :=
  om_order_zero (om_seq_bounds α ς T ω hα hp hT hω0 hE).1 (om_power_log_zero _ _ hS) B mS mG QS QG
    hM

private lemma om_order_one_of (α ς T ω : ℝ) (hα : 0 < α) (hp : 1 < α + ς) (hT : 4 ≤ T)
    (hω0 : 0 < ω) (hE : ¬ phaseSetE α ς) (hS : phaseOmegaS α ς ω = 0)
    (hL : phaseLogPow α ς = 0) :
    phaseOmegaOrderU α ς T ω (fun _ : ℕ => (1 : ℝ)) := by
  have ho := (om_seq_bounds α ς T ω hα hp hT hω0 hE).1
  have e : (fun N : ℕ => (N : ℝ) ^ phaseOmegaS α ς ω * (Real.log (N : ℝ)) ^ phaseLogPow α ς)
      = fun _ : ℕ => (1 : ℝ) := by
    funext N
    simp [hS, hL]
  rwa [e] at ho

private lemma om_top_of_S (α ς T ω : ℝ) (hα : 0 < α) (hp : 1 < α + ς) (hT : 4 ≤ T)
    (hω0 : 0 < ω) (hE : ¬ phaseSetE α ς) (hS : 0 < phaseOmegaS α ς ω)
    (B : ℕ → ℕ) (mS mG : (N : ℕ) → RowModel (Fin N)) (QS QG : ℕ → ℝ → ℝ)
    (hM : PhaseOmegaSeq α ς ω B mS mG QS QG) :
    Tendsto (phaseOmegaSeqR T ω mS mG QS QG) atTop atTop :=
  om_order_top (om_seq_bounds α ς T ω hα hp hT hω0 hE).1 (om_power_log_top _ _ hS) B mS mG QS QG
    hM

private lemma om_order_inv_of (α ς T ω : ℝ) (hα : 0 < α) (hp : 1 < α + ς) (hT : 4 ≤ T)
    (hω0 : 0 < ω) (hE : ¬ phaseSetE α ς) (hS : phaseOmegaS α ς ω = 0)
    (hL : phaseLogPow α ς = -1) :
    phaseOmegaOrderU α ς T ω (fun N : ℕ => (Real.log (N : ℝ))⁻¹) := by
  have ho := (om_seq_bounds α ς T ω hα hp hT hω0 hE).1
  have e : (fun N : ℕ => (N : ℝ) ^ phaseOmegaS α ς ω * (Real.log (N : ℝ)) ^ phaseLogPow α ς)
      = fun N : ℕ => (Real.log (N : ℝ))⁻¹ := by
    funext N
    simp [hS, hL, Real.rpow_neg_one]
  rwa [e] at ho

private lemma om_upper_zero (ς T ω : ℝ) (hς1 : 1 ≤ ς) (hς2 : ς < 2) (hp : 1 < 1 + ς)
    (hT : 4 ≤ T) (hω0 : 0 < ω) (hS : phaseOmegaS 1 ς ω < 0)
    (B : ℕ → ℕ) (mS mG : (N : ℕ) → RowModel (Fin N)) (QS QG : ℕ → ℝ → ℝ)
    (hM : PhaseOmegaSeq 1 ς ω B mS mG QS QG) :
    Tendsto (phaseOmegaSeqR T ω mS mG QS QG) atTop (𝓝 0) := by
  obtain ⟨N0, cHi, _, hb⟩ := thm_app_phase_omega_iii 1 ς T ω one_pos hp hT hω0 rfl hς1 hς2
  have hX : Tendsto (fun N : ℕ => cHi * ((N : ℝ) ^ phaseOmegaS 1 ς ω *
      (Real.log (N : ℝ)) ^ phaseLogPow 1 ς)) atTop (𝓝 0) := by
    have h0 := (om_power_log_zero (phaseOmegaS 1 ς ω) (phaseLogPow 1 ς) hS).const_mul cHi
    rwa [mul_zero] at h0
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hX ?_ ?_
  · exact Eventually.of_forall (fun N => div_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg)
  · filter_upwards [eventually_ge_atTop (max N0 1)] with N hN
    have hN0 : N0 ≤ N := le_trans (le_max_left _ _) hN
    have hN1 : 1 ≤ N := le_trans (le_max_right _ _) hN
    obtain ⟨-, hle⟩ := hb N hN0 (B N) (hM.1 N) (mS N) (mG N) (QS N) (QG N)
      (hM.2 N hN1).1 (hM.2 N hN1).2.1 (hM.2 N hN1).2.2.1 (hM.2 N hN1).2.2.2
    exact hle

/-- Five non-attainment conjuncts of `cor:app-phase-omega-winners`(g) (`α = 1`), proved from the
frozen statements. -/
private lemma om_g_rest (α ς T ω : ℝ) (hG : α = 1) (hα : 0 < α) (hp : 1 < α + ς) (hT : 4 ≤ T)
    (hω0 : 0 < ω) (B : ℕ → ℕ) (mS mG : (N : ℕ) → RowModel (Fin N)) (QS QG : ℕ → ℝ → ℝ)
    (hM : PhaseOmegaSeq α ς ω B mS mG QS QG) :
    (ς < 1 → ω < α + ς - 1 → Tendsto (phaseOmegaSeqR T ω mS mG QS QG) atTop (𝓝 0)) ∧
    (ς < 1 → α + ς - 1 ≤ ω → phaseOmegaOrderU α ς T ω (fun N : ℕ => Real.log (N : ℝ))) ∧
    (ς = 1 → ω < 1 → Tendsto (phaseOmegaSeqR T ω mS mG QS QG) atTop (𝓝 0)) ∧
    (ς = 1 → 1 < ω →
      Tendsto (phaseOmegaSeqR T ω mS mG QS QG) atTop (𝓝 (Real.pi ^ (3 / 2 : ℝ)))) ∧
    (1 < ς → ς < 2 → Tendsto (phaseOmegaSeqR T ω mS mG QS QG) atTop (𝓝 0)) := by
  subst hG
  have hE1 : ς < 1 → ¬ phaseSetE 1 ς := by
    intro hς
    unfold phaseSetE
    rintro (⟨_, h⟩ | ⟨h, _⟩)
    · linarith
    · norm_num at h
  have hSf1 : ∀ ς' ω' : ℝ, phaseOmegaS 1 ς' ω' =
      -1 / 2 + phaseChi 1 ς' * min ω' (1 + ς' - 1) := by
    intro ς' ω'
    unfold phaseOmegaS
    rw [phaseExpD, if_neg (lt_irrefl _), if_pos rfl]
  have hχlt : ς < 1 → phaseChi 1 ς = 1 / (2 * (1 + ς - 1)) := by
    intro hς
    rw [om_chi_formula 1 ς one_pos hp, if_pos hς]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro hς hlt
    apply om_zero_of_S 1 ς T ω one_pos hp hT hω0 (hE1 hς) _ B mS mG QS QG hM
    rw [hSf1, hχlt hς, min_eq_left hlt.le]
    have h2 : 1 / (2 * (1 + ς - 1)) * ω < 1 / 2 := by
      rw [div_mul_eq_mul_div, div_lt_iff₀ (by linarith)]
      nlinarith
    linarith
  · intro hς hge
    have hL : phaseLogPow 1 ς = 1 := by
      unfold phaseLogPow
      simp [ne_of_lt (show ς < 1 + 1 by linarith), ne_of_lt hς]
    have hS : phaseOmegaS 1 ς ω = 0 := by
      rw [hSf1, hχlt hς, min_eq_right hge]
      have hd : (1 + ς - 1) ≠ 0 := (show (0 : ℝ) < 1 + ς - 1 by linarith).ne'
      have h3 : 1 / (2 * (1 + ς - 1)) * (1 + ς - 1) = 1 / 2 := by
        field_simp
      rw [h3]
      norm_num
    have ho := (om_seq_bounds 1 ς T ω one_pos hp hT hω0 (hE1 hς)).1
    have e : (fun N : ℕ => (N : ℝ) ^ phaseOmegaS 1 ς ω * (Real.log (N : ℝ)) ^ phaseLogPow 1 ς)
        = fun N : ℕ => Real.log (N : ℝ) := by
      funext N
      simp [hS, hL]
    rwa [e] at ho
  · intro hς hlt
    subst hς
    have hχ11 : phaseChi 1 1 = 1 / 2 := by
      rw [om_chi_formula 1 1 one_pos hp, if_neg (lt_irrefl _), if_pos (by norm_num)]
      norm_num
    have hS : phaseOmegaS 1 1 ω < 0 := by
      rw [hSf1, hχ11, show (1 : ℝ) + 1 - 1 = 1 by norm_num, min_eq_left hlt.le]
      linarith
    exact om_upper_zero 1 T ω le_rfl (by norm_num) hp hT hω0 hS B mS mG QS QG hM
  · intro hς hgt
    subst hς
    have hρ := ((cor_app_phase_accfirst_winners_ii one_pos hp).2.1 rfl rfl).1
    exact ((thm_app_phase_omega_i_transfer 1 1 T ω one_pos hp hT hω0 (by linarith) B mS mG QS QG
      hM).1 (Real.pi ^ (3 / 2 : ℝ))).mp hρ
  · intro hς1 hς2
    have hχ : phaseChi 1 ς = (1 + 1 - ς) / (2 * (1 + ς - 1)) := by
      rw [om_chi_formula 1 ς one_pos hp, if_neg (not_lt.2 hς1.le), if_pos (by linarith)]
    have hS : phaseOmegaS 1 ς ω < 0 := by
      rw [hSf1, hχ]
      have h1 : (1 + 1 - ς) / (2 * (1 + ς - 1)) * min ω (1 + ς - 1) ≤
          (1 + 1 - ς) / (2 * (1 + ς - 1)) * (1 + ς - 1) :=
        mul_le_mul_of_nonneg_left (min_le_right _ _) (div_nonneg (by linarith) (by linarith))
      have h2 : (1 + 1 - ς) / (2 * (1 + ς - 1)) * (1 + ς - 1) = (1 + 1 - ς) / 2 := by
        have hd : (1 + ς - 1) ≠ 0 := by intro h; linarith
        field_simp
      linarith
    exact om_upper_zero ς T ω hς1.le hς2 hp hT hω0 hS B mS mG QS QG hM

/-- Label `cor:app-phase-omega-winners`, part (a), Phase A: `α > 2`, `ς ≤ α + 1`: `SVD` wins for
every `ω`, i.e. `𝖱 → ∞`. Snapshot `cr-2026-10-23`. Statement of the corollary (verbatim,
`sections/07-phase-comparison/section.tex`, l.1873–1894):

\begin{corollary}[Phases of the accuracy-exponent map]\label{cor:app-phase-omega-winners}
Under the hypotheses of \cref{thm:app-phase-omega}:
\begin{enumerate}[label=(\alph*)]
\item \emph{Phase A}, $\alpha>2$, $\texp\le\alpha+1$: \SignSVD wins for every $\omega$.
\item \emph{Phase B}, $0<\alpha<1$ and $\texp\ge1$ with $(\alpha,\texp)\notin\mathsf E$, or
$1<\alpha<2$ and $\texp>2\alpha-1$: \SignSGD wins for every $\omega$.
\item \emph{Phase C}, $1<\alpha<2$, $\texp<2\alpha-1$: \SignSGD wins if $\omega<\omega_c$
and \SignSVD wins if $\omega>\omega_c$; at $\omega=\omega_c$ the two are balanced if
$\texp\ne1$, and \SignSGD wins, with order $1/\log N$, if $\texp=1$.
\item \emph{Phase D}, $0<\alpha<1$, $\texp<1$: \SignSGD wins if $\omega<p-1$, and the
two are balanced if $\omega\ge p-1$, with limit $K_A$ if $\omega>p-1$.
\item \emph{Tie}, $\alpha>2$, $\texp>\alpha+1$: balanced for every $\omega$.
\item \emph{Chord}, $1<\alpha<2$, $\texp=2\alpha-1$: \SignSGD wins if $\omega<p-1$, and
the two are balanced if $\omega\ge p-1$, with limit $K_c$ if $\omega>p-1$.
\item \emph{$\alpha=1$}: for $\texp<1$, \SignSGD wins if $\omega<p-1$ and \SignSVD wins,
with order $\log N$, if $\omega\ge p-1$; for $\texp=1$, \SignSGD wins if $\omega<1$,
and $\mathsf R\to\pi^{3/2}$ if $\omega>1$; for $1<\texp<2$, \SignSGD wins for every
$\omega$.
\item \emph{$\alpha=2$}: \SignSVD wins for $\texp<3$, the two are balanced for
$\texp=3$, and \SignSGD wins for $\texp>3$, for every $\omega$.
\end{enumerate}
\end{corollary} -/
theorem cor_app_phase_omega_winners_a (α ς T ω : ℝ) (hα : 0 < α) (hp : 1 < α + ς) (hT : 4 ≤ T)
    (hω0 : 0 < ω) (B : ℕ → ℕ) (mS mG : (N : ℕ) → RowModel (Fin N)) (QS QG : ℕ → ℝ → ℝ)
    (hM : PhaseOmegaSeq α ς ω B mS mG QS QG) (hA : 2 < α) (hς : ς ≤ α + 1) :
    phaseOmegaAttained T ω mS mG QS QG ∧
      Tendsto (phaseOmegaSeqR T ω mS mG QS QG) atTop atTop := by
  have hE : ¬ phaseSetE α ς := by
    unfold phaseSetE
    rintro (⟨h, _⟩ | ⟨h, _⟩) <;> linarith
  obtain ⟨ho, ha⟩ := om_seq_bounds α ς T ω hα hp hT hω0 hE
  refine ⟨ha B mS mG QS QG hM, ?_⟩
  by_cases heq : ς = α + 1
  · have hs : phaseOmegaS α ς ω = 0 := by
      rw [phaseOmegaS, om_chi_formula α ς hα hp]
      simp [phaseExpD, heq,
        show ¬ α < 1 by linarith, show α ≠ 1 by linarith, show ¬ α < 2 by linarith,
        show ¬ α + 1 < 1 by linarith]
    have hl : phaseLogPow α ς = 1 := by
      simp [phaseLogPow, heq, show α ≠ 1 by linarith, show α ≠ 2 by linarith,
        show α + 1 ≠ 1 by linarith]
    apply om_order_top ho _ B mS mG QS QG hM
    simp only [hs, hl, Real.rpow_zero, Real.rpow_one, one_mul]
    exact Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  · have hstrict : ς < α + 1 := lt_of_le_of_ne hς heq
    have hχ : 0 < phaseChi α ς := by
      rw [om_chi_formula α ς hα hp]
      split_ifs <;> apply div_pos <;> linarith
    have hs : 0 < phaseOmegaS α ς ω := by
      have hd : phaseExpD α = 0 := by
        simp [phaseExpD, show ¬ α < 1 by linarith, show α ≠ 1 by linarith,
          show ¬ α < 2 by linarith]
      rw [phaseOmegaS, hd, zero_add]
      exact mul_pos hχ (lt_min hω0 (by linarith))
    exact om_order_top ho (om_power_log_top _ _ hs) B mS mG QS QG hM

/-- Label `cor:app-phase-omega-winners`, part (b), Phase B: `0 < α < 1`, `ς ≥ 1`, `(α, ς) ∉ 𝖤`, or
`1 < α < 2`, `ς > 2α - 1`: `SGD` wins for every `ω`, i.e. `𝖱 → 0`. Snapshot `cr-2026-10-23`.
Statement of the corollary (verbatim, `sections/07-phase-comparison/section.tex`, l.1873–1894):

\begin{corollary}[Phases of the accuracy-exponent map]\label{cor:app-phase-omega-winners}
Under the hypotheses of \cref{thm:app-phase-omega}:
\begin{enumerate}[label=(\alph*)]
\item \emph{Phase A}, $\alpha>2$, $\texp\le\alpha+1$: \SignSVD wins for every $\omega$.
\item \emph{Phase B}, $0<\alpha<1$ and $\texp\ge1$ with $(\alpha,\texp)\notin\mathsf E$, or
$1<\alpha<2$ and $\texp>2\alpha-1$: \SignSGD wins for every $\omega$.
\item \emph{Phase C}, $1<\alpha<2$, $\texp<2\alpha-1$: \SignSGD wins if $\omega<\omega_c$
and \SignSVD wins if $\omega>\omega_c$; at $\omega=\omega_c$ the two are balanced if
$\texp\ne1$, and \SignSGD wins, with order $1/\log N$, if $\texp=1$.
\item \emph{Phase D}, $0<\alpha<1$, $\texp<1$: \SignSGD wins if $\omega<p-1$, and the
two are balanced if $\omega\ge p-1$, with limit $K_A$ if $\omega>p-1$.
\item \emph{Tie}, $\alpha>2$, $\texp>\alpha+1$: balanced for every $\omega$.
\item \emph{Chord}, $1<\alpha<2$, $\texp=2\alpha-1$: \SignSGD wins if $\omega<p-1$, and
the two are balanced if $\omega\ge p-1$, with limit $K_c$ if $\omega>p-1$.
\item \emph{$\alpha=1$}: for $\texp<1$, \SignSGD wins if $\omega<p-1$ and \SignSVD wins,
with order $\log N$, if $\omega\ge p-1$; for $\texp=1$, \SignSGD wins if $\omega<1$,
and $\mathsf R\to\pi^{3/2}$ if $\omega>1$; for $1<\texp<2$, \SignSGD wins for every
$\omega$.
\item \emph{$\alpha=2$}: \SignSVD wins for $\texp<3$, the two are balanced for
$\texp=3$, and \SignSGD wins for $\texp>3$, for every $\omega$.
\end{enumerate}
\end{corollary} -/
theorem cor_app_phase_omega_winners_b (α ς T ω : ℝ) (hα : 0 < α) (hp : 1 < α + ς) (hT : 4 ≤ T)
    (hω0 : 0 < ω) (B : ℕ → ℕ) (mS mG : (N : ℕ) → RowModel (Fin N)) (QS QG : ℕ → ℝ → ℝ)
    (hM : PhaseOmegaSeq α ς ω B mS mG QS QG)
    (hB : (0 < α ∧ α < 1 ∧ 1 ≤ ς ∧ ¬ phaseSetE α ς) ∨ (1 < α ∧ α < 2 ∧ 2 * α - 1 < ς)) :
    phaseOmegaAttained T ω mS mG QS QG ∧
      Tendsto (phaseOmegaSeqR T ω mS mG QS QG) atTop (𝓝 0) := by
  have hE : ¬ phaseSetE α ς := by
    rcases hB with hB | ⟨h1, h2, h3⟩
    · exact hB.2.2.2
    · unfold phaseSetE
      rintro (⟨h, _⟩ | ⟨h, _⟩) <;> linarith
  obtain ⟨ho, ha⟩ := om_seq_bounds α ς T ω hα hp hT hω0 hE
  refine ⟨ha B mS mG QS QG hM, ?_⟩
  have hsign : phaseOmegaS α ς ω < 0 ∨
      (phaseOmegaS α ς ω = 0 ∧ phaseLogPow α ς = -1) := by
    have hb := om_S_upper α ς ω hα hp
    rcases hB with ⟨_, h1, hς, _⟩ | ⟨h1, h2, hς⟩
    · have hlt : ¬ ς < 1 := not_lt.2 hς
      simp only [hlt, ite_false, phaseExpD, h1, ite_true] at hb
      by_cases hhi : ς ≤ α + 1
      · rw [if_pos hhi] at hb
        have hs : phaseOmegaS α ς ω ≤ 0 := by linarith
        rcases lt_or_eq_of_le hs with hs | hs
        · exact Or.inl hs
        · right
          have heq : ς = 1 := by linarith
          refine ⟨hs, ?_⟩
          simp [phaseLogPow, heq, show α ≠ 1 by linarith,
            show α ≠ 2 by linarith, show (1 : ℝ) ≠ α + 1 by linarith]
      · rw [if_neg hhi] at hb
        left
        linarith
    · have hlt : ¬ ς < 1 := by linarith
      have hαlt : ¬ α < 1 := by linarith
      have hαne : α ≠ 1 := by linarith
      simp only [hlt, ite_false, phaseExpD, hαlt, hαne, h2, ite_true] at hb
      left
      split_ifs at hb <;> linarith
  rcases hsign with hs | ⟨hs, hl⟩
  · exact om_order_zero ho (om_power_log_zero _ _ hs) B mS mG QS QG hM
  · apply om_order_zero ho _ B mS mG QS QG hM
    simp only [hs, hl, Real.rpow_zero, one_mul, Real.rpow_neg_one]
    exact (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).inv_tendsto_atTop

/-- Label `cor:app-phase-omega-winners`, part (c), Phase C: `1 < α < 2`, `ς < 2α - 1`: `SGD` wins
if `ω < ω_c`, `SVD` wins if `ω > ω_c`; at `ω = ω_c` the two are balanced if `ς ≠ 1`, and `SGD`
wins with order `1/log N` if `ς = 1`. Snapshot `cr-2026-10-23`. Statement of the corollary
(verbatim, `sections/07-phase-comparison/section.tex`, l.1873–1894):

\begin{corollary}[Phases of the accuracy-exponent map]\label{cor:app-phase-omega-winners}
Under the hypotheses of \cref{thm:app-phase-omega}:
\begin{enumerate}[label=(\alph*)]
\item \emph{Phase A}, $\alpha>2$, $\texp\le\alpha+1$: \SignSVD wins for every $\omega$.
\item \emph{Phase B}, $0<\alpha<1$ and $\texp\ge1$ with $(\alpha,\texp)\notin\mathsf E$, or
$1<\alpha<2$ and $\texp>2\alpha-1$: \SignSGD wins for every $\omega$.
\item \emph{Phase C}, $1<\alpha<2$, $\texp<2\alpha-1$: \SignSGD wins if $\omega<\omega_c$
and \SignSVD wins if $\omega>\omega_c$; at $\omega=\omega_c$ the two are balanced if
$\texp\ne1$, and \SignSGD wins, with order $1/\log N$, if $\texp=1$.
\item \emph{Phase D}, $0<\alpha<1$, $\texp<1$: \SignSGD wins if $\omega<p-1$, and the
two are balanced if $\omega\ge p-1$, with limit $K_A$ if $\omega>p-1$.
\item \emph{Tie}, $\alpha>2$, $\texp>\alpha+1$: balanced for every $\omega$.
\item \emph{Chord}, $1<\alpha<2$, $\texp=2\alpha-1$: \SignSGD wins if $\omega<p-1$, and
the two are balanced if $\omega\ge p-1$, with limit $K_c$ if $\omega>p-1$.
\item \emph{$\alpha=1$}: for $\texp<1$, \SignSGD wins if $\omega<p-1$ and \SignSVD wins,
with order $\log N$, if $\omega\ge p-1$; for $\texp=1$, \SignSGD wins if $\omega<1$,
and $\mathsf R\to\pi^{3/2}$ if $\omega>1$; for $1<\texp<2$, \SignSGD wins for every
$\omega$.
\item \emph{$\alpha=2$}: \SignSVD wins for $\texp<3$, the two are balanced for
$\texp=3$, and \SignSGD wins for $\texp>3$, for every $\omega$.
\end{enumerate}
\end{corollary} -/
theorem cor_app_phase_omega_winners_c (α ς T ω : ℝ) (hα : 0 < α) (hp : 1 < α + ς) (hT : 4 ≤ T)
    (hω0 : 0 < ω) (B : ℕ → ℕ) (mS mG : (N : ℕ) → RowModel (Fin N)) (QS QG : ℕ → ℝ → ℝ)
    (hM : PhaseOmegaSeq α ς ω B mS mG QS QG) (hC : 1 < α ∧ α < 2 ∧ ς < 2 * α - 1) :
    phaseOmegaAttained T ω mS mG QS QG ∧
      (ω < phaseOmegaC α ς → Tendsto (phaseOmegaSeqR T ω mS mG QS QG) atTop (𝓝 0)) ∧
      (phaseOmegaC α ς < ω → Tendsto (phaseOmegaSeqR T ω mS mG QS QG) atTop atTop) ∧
      (ω = phaseOmegaC α ς → ς ≠ 1 →
        phaseOmegaOrderU α ς T ω (fun _ : ℕ => (1 : ℝ))) ∧
      (ω = phaseOmegaC α ς → ς = 1 →
        phaseOmegaOrderU α ς T ω (fun N : ℕ => (Real.log (N : ℝ))⁻¹)) := by
  obtain ⟨hα1, hα2, hςc⟩ := hC
  have hE : ¬ phaseSetE α ς := by
    unfold phaseSetE
    rintro (⟨h, _⟩ | ⟨h, _⟩)
    · linarith
    · linarith
  obtain ⟨ho, ha⟩ := om_seq_bounds α ς T ω hα hp hT hω0 hE
  have hd : 0 < α + ς - 1 := by linarith
  have hfacts : 0 < phaseChi α ς ∧ 0 < phaseOmegaC α ς ∧ phaseOmegaC α ς < α + ς - 1 ∧
      phaseChi α ς * phaseOmegaC α ς = (2 - α) / 2 := by
    by_cases hs1 : ς < 1
    · have hχ : phaseChi α ς = α / (2 * (α + ς - 1)) := by
        rw [om_chi_formula α ς hα hp, if_pos hs1]
      have hc : phaseOmegaC α ς = (2 - α) * (α + ς - 1) / α := by
        unfold phaseOmegaC
        rw [if_pos hs1]
      rw [hχ, hc]
      refine ⟨div_pos hα (by linarith), div_pos (mul_pos (by linarith) hd) hα, ?_, ?_⟩
      · rw [div_lt_iff₀ hα]
        nlinarith [mul_lt_mul_of_pos_right (show 2 - α < α by linarith) hd]
      · field_simp
    · have hs2 : ς ≤ α + 1 := by linarith
      have hχ : phaseChi α ς = (α + 1 - ς) / (2 * (α + ς - 1)) := by
        rw [om_chi_formula α ς hα hp, if_neg hs1, if_pos hs2]
      have hc : phaseOmegaC α ς = (2 - α) * (α + ς - 1) / (α + 1 - ς) := by
        unfold phaseOmegaC winnersOmegaC
        rw [if_neg hs1]
      have he : 0 < α + 1 - ς := by linarith
      rw [hχ, hc]
      refine ⟨div_pos he (by linarith), div_pos (mul_pos (by linarith) hd) he, ?_, ?_⟩
      · rw [div_lt_iff₀ he]
        nlinarith [mul_lt_mul_of_pos_right (show 2 - α < α + 1 - ς by linarith) hd]
      · field_simp
  obtain ⟨hχpos, hcpos, hclt, hχc⟩ := hfacts
  have hSf : phaseOmegaS α ς ω = α / 2 - 1 + phaseChi α ς * min ω (α + ς - 1) := by
    unfold phaseOmegaS
    rw [phaseExpD, if_neg (not_lt.2 hα1.le), if_neg hα1.ne', if_pos hα2]
  have hS0 : ω = phaseOmegaC α ς → phaseOmegaS α ς ω = 0 := by
    intro hωc
    rw [hSf, hωc, min_eq_left hclt.le]
    linarith [hχc]
  refine ⟨ha B mS mG QS QG hM, ?_, ?_, ?_, ?_⟩
  · intro hlt
    apply om_zero_of_S α ς T ω hα hp hT hω0 hE _ B mS mG QS QG hM
    rw [hSf]
    have h1 : phaseChi α ς * min ω (α + ς - 1) ≤ phaseChi α ς * ω :=
      mul_le_mul_of_nonneg_left (min_le_left _ _) hχpos.le
    have h2 : phaseChi α ς * ω < phaseChi α ς * phaseOmegaC α ς :=
      mul_lt_mul_of_pos_left hlt hχpos
    linarith [hχc]
  · intro hgt
    apply om_top_of_S α ς T ω hα hp hT hω0 hE _ B mS mG QS QG hM
    rw [hSf]
    have h1 : phaseChi α ς * phaseOmegaC α ς < phaseChi α ς * min ω (α + ς - 1) :=
      mul_lt_mul_of_pos_left (lt_min hgt hclt) hχpos
    linarith [hχc]
  · intro hωc hς1
    have hL : phaseLogPow α ς = 0 := by
      unfold phaseLogPow
      simp [hα1.ne', hα2.ne, ne_of_lt (show ς < α + 1 by linarith), hς1]
    exact om_order_one_of α ς T ω hα hp hT hω0 hE (hS0 hωc) hL
  · intro hωc hς1
    have hL : phaseLogPow α ς = -1 := by
      unfold phaseLogPow
      rw [hς1]
      simp [hα1.ne', hα2.ne, ne_of_lt (show (1 : ℝ) < α + 1 by linarith)]
    exact om_order_inv_of α ς T ω hα hp hT hω0 hE (hS0 hωc) hL

/-- Label `cor:app-phase-omega-winners`, part (d), Phase D: `0 < α < 1`, `ς < 1`: `SGD` wins if
`ω < p - 1`; balanced if `ω ≥ p - 1`; with limit `K_A` if `ω > p - 1`. Snapshot `cr-2026-10-23`.
Statement of the corollary (verbatim, `sections/07-phase-comparison/section.tex`, l.1873–1894):

\begin{corollary}[Phases of the accuracy-exponent map]\label{cor:app-phase-omega-winners}
Under the hypotheses of \cref{thm:app-phase-omega}:
\begin{enumerate}[label=(\alph*)]
\item \emph{Phase A}, $\alpha>2$, $\texp\le\alpha+1$: \SignSVD wins for every $\omega$.
\item \emph{Phase B}, $0<\alpha<1$ and $\texp\ge1$ with $(\alpha,\texp)\notin\mathsf E$, or
$1<\alpha<2$ and $\texp>2\alpha-1$: \SignSGD wins for every $\omega$.
\item \emph{Phase C}, $1<\alpha<2$, $\texp<2\alpha-1$: \SignSGD wins if $\omega<\omega_c$
and \SignSVD wins if $\omega>\omega_c$; at $\omega=\omega_c$ the two are balanced if
$\texp\ne1$, and \SignSGD wins, with order $1/\log N$, if $\texp=1$.
\item \emph{Phase D}, $0<\alpha<1$, $\texp<1$: \SignSGD wins if $\omega<p-1$, and the
two are balanced if $\omega\ge p-1$, with limit $K_A$ if $\omega>p-1$.
\item \emph{Tie}, $\alpha>2$, $\texp>\alpha+1$: balanced for every $\omega$.
\item \emph{Chord}, $1<\alpha<2$, $\texp=2\alpha-1$: \SignSGD wins if $\omega<p-1$, and
the two are balanced if $\omega\ge p-1$, with limit $K_c$ if $\omega>p-1$.
\item \emph{$\alpha=1$}: for $\texp<1$, \SignSGD wins if $\omega<p-1$ and \SignSVD wins,
with order $\log N$, if $\omega\ge p-1$; for $\texp=1$, \SignSGD wins if $\omega<1$,
and $\mathsf R\to\pi^{3/2}$ if $\omega>1$; for $1<\texp<2$, \SignSGD wins for every
$\omega$.
\item \emph{$\alpha=2$}: \SignSVD wins for $\texp<3$, the two are balanced for
$\texp=3$, and \SignSGD wins for $\texp>3$, for every $\omega$.
\end{enumerate}
\end{corollary} -/
theorem cor_app_phase_omega_winners_d (α ς T ω : ℝ) (hα : 0 < α) (hp : 1 < α + ς) (hT : 4 ≤ T)
    (hω0 : 0 < ω) (B : ℕ → ℕ) (mS mG : (N : ℕ) → RowModel (Fin N)) (QS QG : ℕ → ℝ → ℝ)
    (hM : PhaseOmegaSeq α ς ω B mS mG QS QG) (hD : 0 < α ∧ α < 1 ∧ ς < 1) :
    phaseOmegaAttained T ω mS mG QS QG ∧
      (ω < α + ς - 1 → Tendsto (phaseOmegaSeqR T ω mS mG QS QG) atTop (𝓝 0)) ∧
      (α + ς - 1 ≤ ω → phaseOmegaOrderU α ς T ω (fun _ : ℕ => (1 : ℝ))) ∧
      (α + ς - 1 < ω →
        Tendsto (phaseOmegaSeqR T ω mS mG QS QG) atTop (𝓝 (phaseKA α ς))) := by
  obtain ⟨-, hα1, hς1⟩ := hD
  have hE : ¬ phaseSetE α ς := by
    unfold phaseSetE
    rintro (⟨h, _⟩ | ⟨_, h⟩)
    · linarith
    · linarith
  obtain ⟨ho, ha⟩ := om_seq_bounds α ς T ω hα hp hT hω0 hE
  have hd : 0 < α + ς - 1 := by linarith
  have hχ : phaseChi α ς = α / (2 * (α + ς - 1)) := by
    rw [om_chi_formula α ς hα hp, if_pos hς1]
  have hSf : phaseOmegaS α ς ω = -α / 2 + α / (2 * (α + ς - 1)) * min ω (α + ς - 1) := by
    unfold phaseOmegaS
    rw [hχ, phaseExpD, if_pos hα1]
  have hL : phaseLogPow α ς = 0 := by
    unfold phaseLogPow
    simp [ne_of_lt hα1, (by linarith : α < 2).ne, ne_of_lt (show ς < α + 1 by linarith),
      ne_of_lt hς1]
  refine ⟨ha B mS mG QS QG hM, ?_, ?_, ?_⟩
  · intro hlt
    apply om_zero_of_S α ς T ω hα hp hT hω0 hE _ B mS mG QS QG hM
    rw [hSf, min_eq_left hlt.le]
    have h1 : α * ω < α * (α + ς - 1) := mul_lt_mul_of_pos_left hlt hα
    have h2 : α * ω / (2 * (α + ς - 1)) < α / 2 := by
      rw [div_lt_iff₀ (by linarith)]
      nlinarith
    have h3 : α / (2 * (α + ς - 1)) * ω = α * ω / (2 * (α + ς - 1)) := by ring
    rw [h3]
    linarith
  · intro hge
    apply om_order_one_of α ς T ω hα hp hT hω0 hE _ hL
    rw [hSf, min_eq_right hge]
    have h3 : α / (2 * (α + ς - 1)) * (α + ς - 1) = α / 2 := by
      field_simp
    rw [h3]
    ring
  · intro hgt
    have hρ := ((cor_app_phase_accfirst_winners_ii hα hp).1 hα hα1 hς1).1
    exact ((thm_app_phase_omega_i_transfer α ς T ω hα hp hT hω0 hgt B mS mG QS QG hM).1
      (phaseKA α ς)).mp hρ

/-- Label `cor:app-phase-omega-winners`, part (e), Tie: `α > 2`, `ς > α + 1`: balanced for every
`ω`. Snapshot `cr-2026-10-23`. Statement of the corollary (verbatim,
`sections/07-phase-comparison/section.tex`, l.1873–1894):

\begin{corollary}[Phases of the accuracy-exponent map]\label{cor:app-phase-omega-winners}
Under the hypotheses of \cref{thm:app-phase-omega}:
\begin{enumerate}[label=(\alph*)]
\item \emph{Phase A}, $\alpha>2$, $\texp\le\alpha+1$: \SignSVD wins for every $\omega$.
\item \emph{Phase B}, $0<\alpha<1$ and $\texp\ge1$ with $(\alpha,\texp)\notin\mathsf E$, or
$1<\alpha<2$ and $\texp>2\alpha-1$: \SignSGD wins for every $\omega$.
\item \emph{Phase C}, $1<\alpha<2$, $\texp<2\alpha-1$: \SignSGD wins if $\omega<\omega_c$
and \SignSVD wins if $\omega>\omega_c$; at $\omega=\omega_c$ the two are balanced if
$\texp\ne1$, and \SignSGD wins, with order $1/\log N$, if $\texp=1$.
\item \emph{Phase D}, $0<\alpha<1$, $\texp<1$: \SignSGD wins if $\omega<p-1$, and the
two are balanced if $\omega\ge p-1$, with limit $K_A$ if $\omega>p-1$.
\item \emph{Tie}, $\alpha>2$, $\texp>\alpha+1$: balanced for every $\omega$.
\item \emph{Chord}, $1<\alpha<2$, $\texp=2\alpha-1$: \SignSGD wins if $\omega<p-1$, and
the two are balanced if $\omega\ge p-1$, with limit $K_c$ if $\omega>p-1$.
\item \emph{$\alpha=1$}: for $\texp<1$, \SignSGD wins if $\omega<p-1$ and \SignSVD wins,
with order $\log N$, if $\omega\ge p-1$; for $\texp=1$, \SignSGD wins if $\omega<1$,
and $\mathsf R\to\pi^{3/2}$ if $\omega>1$; for $1<\texp<2$, \SignSGD wins for every
$\omega$.
\item \emph{$\alpha=2$}: \SignSVD wins for $\texp<3$, the two are balanced for
$\texp=3$, and \SignSGD wins for $\texp>3$, for every $\omega$.
\end{enumerate}
\end{corollary} -/
theorem cor_app_phase_omega_winners_e (α ς T ω : ℝ) (hα : 0 < α) (hp : 1 < α + ς) (hT : 4 ≤ T)
    (hω0 : 0 < ω) (B : ℕ → ℕ) (mS mG : (N : ℕ) → RowModel (Fin N)) (QS QG : ℕ → ℝ → ℝ)
    (hM : PhaseOmegaSeq α ς ω B mS mG QS QG) (hE' : 2 < α ∧ α + 1 < ς) :
    phaseOmegaAttained T ω mS mG QS QG ∧
      phaseOmegaOrderU α ς T ω (fun _ : ℕ => (1 : ℝ)) := by
  have hE : ¬ phaseSetE α ς := by
    unfold phaseSetE
    rintro (⟨h, _⟩ | ⟨h, _⟩) <;> linarith [hE'.1]
  obtain ⟨ho, ha⟩ := om_seq_bounds α ς T ω hα hp hT hω0 hE
  have hs : phaseOmegaS α ς ω = 0 := by
    rw [phaseOmegaS, om_chi_formula α ς hα hp]
    simp [phaseExpD, show ¬ α < 1 by linarith [hE'.1],
      show α ≠ 1 by linarith [hE'.1], show ¬ α < 2 by linarith [hE'.1],
      show ¬ ς < 1 by linarith [hE'.1, hE'.2], not_le.2 hE'.2]
  have hl : phaseLogPow α ς = 0 := by
    simp [phaseLogPow, show α ≠ 1 by linarith [hE'.1],
      show α ≠ 2 by linarith [hE'.1], ne_of_gt hE'.2,
      show ς ≠ 1 by linarith [hE'.1, hE'.2]]
  exact ⟨ha B mS mG QS QG hM, by simpa only [hs, hl, Real.rpow_zero, mul_one] using ho⟩

/-- Label `cor:app-phase-omega-winners`, part (f), Chord: `1 < α < 2`, `ς = 2α - 1`: `SGD` wins if
`ω < p - 1`; balanced if `ω ≥ p - 1`; with limit `K_c` if `ω > p - 1`. Snapshot `cr-2026-10-23`.
Statement of the corollary (verbatim, `sections/07-phase-comparison/section.tex`, l.1873–1894):

\begin{corollary}[Phases of the accuracy-exponent map]\label{cor:app-phase-omega-winners}
Under the hypotheses of \cref{thm:app-phase-omega}:
\begin{enumerate}[label=(\alph*)]
\item \emph{Phase A}, $\alpha>2$, $\texp\le\alpha+1$: \SignSVD wins for every $\omega$.
\item \emph{Phase B}, $0<\alpha<1$ and $\texp\ge1$ with $(\alpha,\texp)\notin\mathsf E$, or
$1<\alpha<2$ and $\texp>2\alpha-1$: \SignSGD wins for every $\omega$.
\item \emph{Phase C}, $1<\alpha<2$, $\texp<2\alpha-1$: \SignSGD wins if $\omega<\omega_c$
and \SignSVD wins if $\omega>\omega_c$; at $\omega=\omega_c$ the two are balanced if
$\texp\ne1$, and \SignSGD wins, with order $1/\log N$, if $\texp=1$.
\item \emph{Phase D}, $0<\alpha<1$, $\texp<1$: \SignSGD wins if $\omega<p-1$, and the
two are balanced if $\omega\ge p-1$, with limit $K_A$ if $\omega>p-1$.
\item \emph{Tie}, $\alpha>2$, $\texp>\alpha+1$: balanced for every $\omega$.
\item \emph{Chord}, $1<\alpha<2$, $\texp=2\alpha-1$: \SignSGD wins if $\omega<p-1$, and
the two are balanced if $\omega\ge p-1$, with limit $K_c$ if $\omega>p-1$.
\item \emph{$\alpha=1$}: for $\texp<1$, \SignSGD wins if $\omega<p-1$ and \SignSVD wins,
with order $\log N$, if $\omega\ge p-1$; for $\texp=1$, \SignSGD wins if $\omega<1$,
and $\mathsf R\to\pi^{3/2}$ if $\omega>1$; for $1<\texp<2$, \SignSGD wins for every
$\omega$.
\item \emph{$\alpha=2$}: \SignSVD wins for $\texp<3$, the two are balanced for
$\texp=3$, and \SignSGD wins for $\texp>3$, for every $\omega$.
\end{enumerate}
\end{corollary} -/
theorem cor_app_phase_omega_winners_f (α ς T ω : ℝ) (hα : 0 < α) (hp : 1 < α + ς) (hT : 4 ≤ T)
    (hω0 : 0 < ω) (B : ℕ → ℕ) (mS mG : (N : ℕ) → RowModel (Fin N)) (QS QG : ℕ → ℝ → ℝ)
    (hM : PhaseOmegaSeq α ς ω B mS mG QS QG) (hF : 1 < α ∧ α < 2 ∧ ς = 2 * α - 1) :
    phaseOmegaAttained T ω mS mG QS QG ∧
      (ω < α + ς - 1 → Tendsto (phaseOmegaSeqR T ω mS mG QS QG) atTop (𝓝 0)) ∧
      (α + ς - 1 ≤ ω → phaseOmegaOrderU α ς T ω (fun _ : ℕ => (1 : ℝ))) ∧
      (α + ς - 1 < ω →
        Tendsto (phaseOmegaSeqR T ω mS mG QS QG) atTop (𝓝 (phaseKc α))) := by
  obtain ⟨hα1, hα2, hς⟩ := hF
  have hE : ¬ phaseSetE α ς := by
    unfold phaseSetE
    rintro (⟨h, _⟩ | ⟨h, _⟩)
    · linarith
    · linarith
  obtain ⟨ho, ha⟩ := om_seq_bounds α ς T ω hα hp hT hω0 hE
  have hd : 0 < α + ς - 1 := by linarith
  have he : 0 < α + 1 - ς := by linarith
  have hχ : phaseChi α ς = (α + 1 - ς) / (2 * (α + ς - 1)) := by
    rw [om_chi_formula α ς hα hp, if_neg (not_lt.2 (by linarith : (1 : ℝ) ≤ ς)),
      if_pos (by linarith : ς ≤ α + 1)]
  have hSf : phaseOmegaS α ς ω =
      α / 2 - 1 + (α + 1 - ς) / (2 * (α + ς - 1)) * min ω (α + ς - 1) := by
    unfold phaseOmegaS
    rw [hχ, phaseExpD, if_neg (not_lt.2 hα1.le), if_neg hα1.ne', if_pos hα2]
  have hL : phaseLogPow α ς = 0 := by
    unfold phaseLogPow
    simp [hα1.ne', hα2.ne, ne_of_lt (show ς < α + 1 by linarith),
      (show (1 : ℝ) < ς by linarith).ne']
  refine ⟨ha B mS mG QS QG hM, ?_, ?_, ?_⟩
  · intro hlt
    apply om_zero_of_S α ς T ω hα hp hT hω0 hE _ B mS mG QS QG hM
    rw [hSf, min_eq_left hlt.le]
    have h1 : (α + 1 - ς) * ω < (α + 1 - ς) * (α + ς - 1) := mul_lt_mul_of_pos_left hlt he
    have h2 : (α + 1 - ς) / (2 * (α + ς - 1)) * ω < (α + 1 - ς) / 2 := by
      rw [div_mul_eq_mul_div, div_lt_iff₀ (by linarith)]
      nlinarith
    linarith
  · intro hge
    apply om_order_one_of α ς T ω hα hp hT hω0 hE _ hL
    rw [hSf, min_eq_right hge]
    have h3 : (α + 1 - ς) / (2 * (α + ς - 1)) * (α + ς - 1) = (α + 1 - ς) / 2 := by
      field_simp
    rw [h3]
    linarith
  · intro hgt
    have hρ := ((cor_app_phase_accfirst_winners_ii hα hp).2.2.1 hα1 hα2 hς).1
    exact ((thm_app_phase_omega_i_transfer α ς T ω hα hp hT hω0 hgt B mS mG QS QG hM).1
      (phaseKc α)).mp hρ

/-- Label `cor:app-phase-omega-winners`, part (g), `α = 1`: for `ς < 1`, `SGD` wins if `ω < p - 1`
and `SVD` wins, with order `log N`, if `ω ≥ p - 1`; for `ς = 1`, `SGD` wins if `ω < 1` and
`𝖱 → π^{3/2}` if `ω > 1`; for `1 < ς < 2`, `SGD` wins for every `ω`. Snapshot `cr-2026-10-23`.
Statement of the corollary (verbatim, `sections/07-phase-comparison/section.tex`, l.1873–1894):

\begin{corollary}[Phases of the accuracy-exponent map]\label{cor:app-phase-omega-winners}
Under the hypotheses of \cref{thm:app-phase-omega}:
\begin{enumerate}[label=(\alph*)]
\item \emph{Phase A}, $\alpha>2$, $\texp\le\alpha+1$: \SignSVD wins for every $\omega$.
\item \emph{Phase B}, $0<\alpha<1$ and $\texp\ge1$ with $(\alpha,\texp)\notin\mathsf E$, or
$1<\alpha<2$ and $\texp>2\alpha-1$: \SignSGD wins for every $\omega$.
\item \emph{Phase C}, $1<\alpha<2$, $\texp<2\alpha-1$: \SignSGD wins if $\omega<\omega_c$
and \SignSVD wins if $\omega>\omega_c$; at $\omega=\omega_c$ the two are balanced if
$\texp\ne1$, and \SignSGD wins, with order $1/\log N$, if $\texp=1$.
\item \emph{Phase D}, $0<\alpha<1$, $\texp<1$: \SignSGD wins if $\omega<p-1$, and the
two are balanced if $\omega\ge p-1$, with limit $K_A$ if $\omega>p-1$.
\item \emph{Tie}, $\alpha>2$, $\texp>\alpha+1$: balanced for every $\omega$.
\item \emph{Chord}, $1<\alpha<2$, $\texp=2\alpha-1$: \SignSGD wins if $\omega<p-1$, and
the two are balanced if $\omega\ge p-1$, with limit $K_c$ if $\omega>p-1$.
\item \emph{$\alpha=1$}: for $\texp<1$, \SignSGD wins if $\omega<p-1$ and \SignSVD wins,
with order $\log N$, if $\omega\ge p-1$; for $\texp=1$, \SignSGD wins if $\omega<1$,
and $\mathsf R\to\pi^{3/2}$ if $\omega>1$; for $1<\texp<2$, \SignSGD wins for every
$\omega$.
\item \emph{$\alpha=2$}: \SignSVD wins for $\texp<3$, the two are balanced for
$\texp=3$, and \SignSGD wins for $\texp>3$, for every $\omega$.
\end{enumerate}
\end{corollary} -/
theorem cor_app_phase_omega_winners_g (α ς T ω : ℝ) (hα : 0 < α) (hp : 1 < α + ς) (hT : 4 ≤ T)
    (hω0 : 0 < ω) (B : ℕ → ℕ) (mS mG : (N : ℕ) → RowModel (Fin N)) (QS QG : ℕ → ℝ → ℝ)
    (hM : PhaseOmegaSeq α ς ω B mS mG QS QG) (hG : α = 1) :
    (ς < 2 → phaseOmegaAttained T ω mS mG QS QG) ∧
      (ς < 1 → ω < α + ς - 1 → Tendsto (phaseOmegaSeqR T ω mS mG QS QG) atTop (𝓝 0)) ∧
      (ς < 1 → α + ς - 1 ≤ ω →
        phaseOmegaOrderU α ς T ω (fun N : ℕ => Real.log (N : ℝ))) ∧
      (ς = 1 → ω < 1 → Tendsto (phaseOmegaSeqR T ω mS mG QS QG) atTop (𝓝 0)) ∧
      (ς = 1 → 1 < ω →
        Tendsto (phaseOmegaSeqR T ω mS mG QS QG) atTop (𝓝 (Real.pi ^ (3 / 2 : ℝ)))) ∧
      (1 < ς → ς < 2 → Tendsto (phaseOmegaSeqR T ω mS mG QS QG) atTop (𝓝 0)) := by
  subst α
  refine ⟨?_, om_g_rest 1 ς T ω rfl hα hp hT hω0 B mS mG QS QG hM⟩
  intro hς2
  by_cases hς1 : ς < 1
  · have hE : ¬ phaseSetE 1 ς := by
      unfold phaseSetE
      rintro (⟨_, h⟩ | ⟨h, _⟩)
      · linarith
      · norm_num at h
    exact (om_seq_bounds 1 ς T ω hα hp hT hω0 hE).2 B mS mG QS QG hM
  · have hς1' : 1 ≤ ς := le_of_not_gt hς1
    obtain ⟨N0, cHi, hcHi, hb⟩ :=
      thm_app_phase_omega_iii 1 ς T ω hα hp hT hω0 rfl hς1' hς2
    unfold phaseOmegaAttained
    filter_upwards [eventually_ge_atTop (max N0 1)] with N hN
    have hN0 : N0 ≤ N := le_trans (le_max_left _ _) hN
    have hN1 : 1 ≤ N := le_trans (le_max_right _ _) hN
    exact (hb N hN0 (B N) (hM.1 N) (mS N) (mG N) (QS N) (QG N)
      (hM.2 N hN1).1 (hM.2 N hN1).2.1 (hM.2 N hN1).2.2.1 (hM.2 N hN1).2.2.2).1

/-- Label `cor:app-phase-omega-winners`, part (h), `α = 2`: `SVD` wins for `ς < 3`, balanced for
`ς = 3`, and `SGD` wins for `ς > 3`, for every `ω`. Snapshot `cr-2026-10-23`. Statement of the
corollary (verbatim, `sections/07-phase-comparison/section.tex`, l.1873–1894):

\begin{corollary}[Phases of the accuracy-exponent map]\label{cor:app-phase-omega-winners}
Under the hypotheses of \cref{thm:app-phase-omega}:
\begin{enumerate}[label=(\alph*)]
\item \emph{Phase A}, $\alpha>2$, $\texp\le\alpha+1$: \SignSVD wins for every $\omega$.
\item \emph{Phase B}, $0<\alpha<1$ and $\texp\ge1$ with $(\alpha,\texp)\notin\mathsf E$, or
$1<\alpha<2$ and $\texp>2\alpha-1$: \SignSGD wins for every $\omega$.
\item \emph{Phase C}, $1<\alpha<2$, $\texp<2\alpha-1$: \SignSGD wins if $\omega<\omega_c$
and \SignSVD wins if $\omega>\omega_c$; at $\omega=\omega_c$ the two are balanced if
$\texp\ne1$, and \SignSGD wins, with order $1/\log N$, if $\texp=1$.
\item \emph{Phase D}, $0<\alpha<1$, $\texp<1$: \SignSGD wins if $\omega<p-1$, and the
two are balanced if $\omega\ge p-1$, with limit $K_A$ if $\omega>p-1$.
\item \emph{Tie}, $\alpha>2$, $\texp>\alpha+1$: balanced for every $\omega$.
\item \emph{Chord}, $1<\alpha<2$, $\texp=2\alpha-1$: \SignSGD wins if $\omega<p-1$, and
the two are balanced if $\omega\ge p-1$, with limit $K_c$ if $\omega>p-1$.
\item \emph{$\alpha=1$}: for $\texp<1$, \SignSGD wins if $\omega<p-1$ and \SignSVD wins,
with order $\log N$, if $\omega\ge p-1$; for $\texp=1$, \SignSGD wins if $\omega<1$,
and $\mathsf R\to\pi^{3/2}$ if $\omega>1$; for $1<\texp<2$, \SignSGD wins for every
$\omega$.
\item \emph{$\alpha=2$}: \SignSVD wins for $\texp<3$, the two are balanced for
$\texp=3$, and \SignSGD wins for $\texp>3$, for every $\omega$.
\end{enumerate}
\end{corollary} -/
theorem cor_app_phase_omega_winners_h (α ς T ω : ℝ) (hα : 0 < α) (hp : 1 < α + ς) (hT : 4 ≤ T)
    (hω0 : 0 < ω) (B : ℕ → ℕ) (mS mG : (N : ℕ) → RowModel (Fin N)) (QS QG : ℕ → ℝ → ℝ)
    (hM : PhaseOmegaSeq α ς ω B mS mG QS QG) (hH : α = 2) :
    phaseOmegaAttained T ω mS mG QS QG ∧
      (ς < 3 → Tendsto (phaseOmegaSeqR T ω mS mG QS QG) atTop atTop) ∧
      (ς = 3 → phaseOmegaOrderU α ς T ω (fun _ : ℕ => (1 : ℝ))) ∧
      (3 < ς → Tendsto (phaseOmegaSeqR T ω mS mG QS QG) atTop (𝓝 0)) := by
  subst α
  have hE : ¬ phaseSetE 2 ς := by norm_num [phaseSetE]
  obtain ⟨ho, ha⟩ := om_seq_bounds 2 ς T ω hα hp hT hω0 hE
  refine ⟨ha B mS mG QS QG hM, ?_, ?_, ?_⟩
  · intro hς
    have hχ : 0 < phaseChi 2 ς := by
      rw [om_chi_formula 2 ς hα hp]
      split_ifs <;> first | (apply div_pos <;> linarith) | linarith
    have hs : 0 < phaseOmegaS 2 ς ω := by
      simpa [phaseOmegaS, phaseExpD] using mul_pos hχ (lt_min hω0 (by linarith : 0 < 2 + ς - 1))
    exact om_order_top ho (om_power_log_top _ _ hs) B mS mG QS QG hM
  · intro hς
    have hs : phaseOmegaS 2 ς ω = 0 := by
      rw [phaseOmegaS, om_chi_formula 2 ς hα hp]
      norm_num [hς, phaseExpD]
    have hl : phaseLogPow 2 ς = 0 := by norm_num [phaseLogPow, hς]
    simpa only [hs, hl, Real.rpow_zero, mul_one] using ho
  · intro hς
    have hs : phaseOmegaS 2 ς ω = 0 := by
      rw [phaseOmegaS, om_chi_formula 2 ς hα hp]
      simp [phaseExpD, show ¬ ς < 1 by linarith, show ¬ ς ≤ 2 + 1 by linarith]
    have hl : phaseLogPow 2 ς = -1 := by
      norm_num [phaseLogPow, show ς ≠ 3 by linarith, show ς ≠ 1 by linarith]
    apply om_order_zero ho _ B mS mG QS QG hM
    simp only [hs, hl, Real.rpow_zero, one_mul, Real.rpow_neg_one]
    exact (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).inv_tendsto_atTop

end Muon.Phase
