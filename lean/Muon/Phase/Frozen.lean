import Mathlib
import Muon.Phase.AccuracyFirst
import Muon.Phase.TwoPhase

/-!
# Appendix H: the frozen regime (task L-H.15)

Snapshot `cr-2026-10-23`. Source: `sections/07-phase-comparison/section.tex`:
`thm:app-phase-frozen` (l.1715–1730), the accuracy-scale display `eqn:app-phase-epsN` (l.1551),
the scales `eqn:app-phase-scales` (l.1564), the clock integral `eqn:app-phase-clockint` (l.1574),
the frozen error bound `eqn:app-phase-frozenerr` (l.3492), with its constants `a_1, a_2` and
`c_1, c_2` (l.3463–3503), and the phase-one data of l.3354–3363.
Card: `sections/07-phase-comparison/CARD.md` §2, §3 (row `thm:app-phase-frozen`), §5 (L-H.15), §6.

Encoding decisions (statements only; proofs are `sorry`):
* `ε_N = N^{-(p-1)}` (`phaseEpsN`), `x = ε/ε_N` (`phaseX`), with `p = α + ς`.
* The clock integral `𝖨_j = ∫_0^{û_j} √Y_j` is `dimClockI Y T ε` for a dimensionless risk `Y`,
  where `û = (firstHit Y (Tε)).toReal`. The step model's clock integral is `phaseClockI Q T₀ T ε`,
  which is `dimClockI` of `u ↦ Q (T₀ u)` (the paper's `Y_j(u) = Q_j(T_0^j u)`). When the first hit
  is not attained, `toReal ⊤ = 0` and the Lean value is `0`; every limit in the theorem is stated
  for sequences where the hit is attained, which the limits force (`0 / J_N ↛ 1`).
* Times `t^j_{Tε}` are `stepHit` of `PhaseTheorems` (in `ℝ≥0∞`); their real values are taken with
  `toReal` and the asymptotic statements carry attainment through `∀ᶠ`/limit clauses.
* The sequence statements of `thm:app-phase-frozen` use the structure `FrozenSeq` (the sequences
  `N_n → ∞`, `B_n ≥ N_n ≥ 1`, `ε_n > 0`, `x_n → 0`, and for each `n` the two matched models with
  Volterra solutions, as in `PhaseTheorems`). `T ≥ 4` and `α > 0`, `α + ς > 1` are standing
  hypotheses of the source (`Fix α>0, ς, p>1, T≥4`).
* The "Moreover" clause (rate bound for `r_j < 1`) is two declarations (one per model), each with
  its own `∃ N_2, c`. Its constants `N_2, c` are quantified before the model, `B`, `ε` (uniform in
  `B ≥ N`), as the source's `c` depends only on `α, ς, T`.
* The frozen error bound `eqn:app-phase-frozenerr` is `lem_app_phase_frozenerr`, stated for a
  dimensionless risk `Y` solving the dimensionless equation `Y = f_{N,q} + √ε g * √Y` (the
  equation of section.tex l.1136, `prop:app-phase-prefactors`(ii)), with the phase-one
  kernel bound packaged as `PhaseOneBound`. The source's phase-one data `(D, τ, N°)` is a
  hypothesis here; its existence for `r_j < 1` is not a Lean declaration yet (see the result JSON).
* Name clash: `Φ`/`Φ_N` not used; `J` is `JN` (finite `N`) and `Jpq` (infinite), reused from
  `PowerSums`; `ρ_N` is `phaseRhoN` (`AccuracyFirst`, reused).
-/

open MeasureTheory Set Filter Topology Asymptotics
open scoped ENNReal NNReal
open Muon.Foundations

set_option linter.style.longLine false

noncomputable section

namespace Muon.Phase

/-! ## Transcription helpers

These name displays of the section; they add no mathematical content beyond the displayed formulas. -/

/-- Snapshot `cr-2026-10-23`. Accuracy scale `ε_N = N^{-(p-1)}`, `eqn:app-phase-epsN`, for `p = α + ς`. Source:
section.tex l.1551–1553.
```latex
\begin{equation}\label{eqn:app-phase-epsN}
\epsilon_N\defeq N^{-(p-1)} .
\end{equation}
``` -/
def phaseEpsN (p : ℝ) (N : ℕ) : ℝ := (N : ℝ) ^ (-(p - 1))

/-- Snapshot `cr-2026-10-23`. The scale `x = ε/ε_N = ε N^{p-1}`, `eqn:app-phase-scales`, for `p = α + ς`. Source:
section.tex l.1564–1568 (the `x` display; the `𝗒_j` identities are not used in the statements).
```latex
\begin{equation}\label{eqn:app-phase-scales}
x\defeq\frac{\epsilon}{\epsilon_N}=\epsilon N^{p-1},\qquad
\mathsf y_j\defeq\epsilon N^{2q_j},\qquad
\sqrt{\mathsf y_j}=\sqrt x\,N^{q_j(1-r_j)} ,
\end{equation}
``` -/
def phaseX (p : ℝ) (N : ℕ) (ε : ℝ) : ℝ := ε / phaseEpsN p N

/-- Snapshot `cr-2026-10-23`. The clock integral `𝖨 = ∫_0^{û} √Y` of a dimensionless risk `Y`, where
`û = inf{u ≥ 0 : Y(u) ≤ Tε}` is the first hit (`firstHit`, `ℝ≥0∞`, `toReal`). Source:
`eqn:app-phase-clockint`, section.tex l.1574–1576:
```latex
\begin{equation}\label{eqn:app-phase-clockint}
\mathsf I_j\defeq\int_0^{\hat u_j}\sqrt{Y_j(u)}\,\dif u,\qquad
\frac{t^{\text{s-SGD}}_{T\epsilon}}{t^{\text{s-SVD}}_{T\epsilon}}=D_N\,\frac{\mathsf I_{\text{s-SGD}}}{\mathsf I_{\text{s-SVD}}} ,
\end{equation}
``` -/
def dimClockI (Y : ℝ → ℝ) (T ε : ℝ) : ℝ :=
  ∫ u in (0 : ℝ)..(firstHit Y (T * ε)).toReal, Real.sqrt (Y u)

/-- Snapshot `cr-2026-10-23`. The clock integral `𝖨_j = ∫_0^{û_j} √Y_j` of a model with risk `Q` and time scale `T₀`, with
`Y_j(u) = Q(T₀ u)` (`def:app-phase-arrays`); it is `dimClockI` of `u ↦ Q (T₀ u)`, the same first hit
as `dimHit` of `PhaseTheorems`. -/
def phaseClockI (Q : ℝ → ℝ) (T0 T ε : ℝ) : ℝ := dimClockI (fun u => Q (T0 * u)) T ε

/-- Snapshot `cr-2026-10-23`. The phase-one kernel bound of a model with `r < 1` (section.tex l.3354–3363): for the
dimensionless kernel `g` at size `N`, `g * h ≤ 2h` on `[0, τ N^q]`, where
`h(u) = C (1 + u/D)^{-r}`. Paper convention: `(g * h)(u) = ∫_0^u g(v) h(u-v) dv`, which is
`oneSidedConv h g u`. -/
def PhaseOneBound (g : ℝ → ℝ) (C q r D τ : ℝ) (N : ℕ) : Prop :=
  ∀ u ∈ Icc (0 : ℝ) (τ * (N : ℝ) ^ q),
    oneSidedConv (fun v => C * (1 + v / D) ^ (-r)) g u ≤ 2 * (C * (1 + u / D) ^ (-r))

/-- Snapshot `cr-2026-10-23`. `c_2 = C (D/τ)^r` of the proof of `thm:app-phase-frozen`, case `r < 1` (section.tex l.3478, from
`h(u_0) ≤ C (D/τ)^r N^{-qr}`). -/
def frozenC2 (C r D τ : ℝ) : ℝ := C * (D / τ) ^ r

/-- Snapshot `cr-2026-10-23`. `c_1 = √(2C) D^{r/2} (2τ)^{1-r/2} / (1 - r/2)` of the first phase
(section.tex l.3472, `eqn:app-phase-phase1`). -/
def frozenC1 (C r D τ : ℝ) : ℝ :=
  Real.sqrt (2 * C) * D ^ (r / 2) * (2 * τ) ^ (1 - r / 2) / (1 - r / 2)

/-- Snapshot `cr-2026-10-23`. `a_1(x) = (c_1 + √(2c_2)) x^{1/4} + (τ+1) x^{1/2}` (section.tex l.3500–3501). -/
def frozenA1 (C r D τ x : ℝ) : ℝ :=
  (frozenC1 C r D τ + Real.sqrt (2 * frozenC2 C r D τ)) * x ^ (1 / 4 : ℝ) + (τ + 1) * x ^ (1 / 2 : ℝ)

/-- Snapshot `cr-2026-10-23`. `a_2(x) = √(2c_2) x^{1/4} + x^{1/2}` (section.tex l.3501). -/
def frozenA2 (C r D τ x : ℝ) : ℝ :=
  Real.sqrt (2 * frozenC2 C r D τ) * x ^ (1 / 4 : ℝ) + x ^ (1 / 2 : ℝ)

/-- Snapshot `cr-2026-10-23`. The bound on `d̃/N^{e_r}`: `2 x^{1/2} log(1 + c_2 x^{-1/2})` (section.tex l.3478–3481). -/
def frozenDt (C r D τ x : ℝ) : ℝ :=
  2 * x ^ (1 / 2 : ℝ) * Real.log (1 + frozenC2 C r D τ * x ^ (-(1 / 2 : ℝ)))

/-- Snapshot `cr-2026-10-23`. The right-hand side of `eqn:app-phase-frozenerr` with `J = J_N(p,q)`, `e_r = q(1-r)`,
`x = ε/ε_N`: `J + a_1 N^{e} + 2√((J + a_2 N^{e}) d̃) + d̃`, with `d̃ = dt · N^{e}`. -/
def frozenErrBound (C q r D τ x : ℝ) (N : ℕ) (J : ℝ) : ℝ :=
  J + frozenA1 C r D τ x * (N : ℝ) ^ (q * (1 - r))
    + 2 * Real.sqrt ((J + frozenA2 C r D τ x * (N : ℝ) ^ (q * (1 - r))) *
        (frozenDt C r D τ x * (N : ℝ) ^ (q * (1 - r))))
    + frozenDt C r D τ x * (N : ℝ) ^ (q * (1 - r))

/-- Snapshot `cr-2026-10-23`. The frozen rate `x^{1/4} + x^{1/2} log(e + x^{-1/2})` of `thm:app-phase-frozen` (its
"moreover" clause; section.tex l.1725–1727). -/
def frozenRate (x : ℝ) : ℝ :=
  x ^ (1 / 4 : ℝ) + x ^ (1 / 2 : ℝ) * Real.log (Real.exp 1 + x ^ (-(1 / 2 : ℝ)))

/-- Snapshot `cr-2026-10-23`. Data of the sequence statements of `thm:app-phase-frozen`: sizes `N_n → ∞`, integers
`B_n ≥ N_n ≥ 1`, accuracies `ε_n > 0` with `x_n = ε_n/ε_{N_n} → 0` (the frozen regime), and for each
`n` the two matched models (`IsMatchedModel` of the arrays `svdArrays`, `sgdArrays`) with Volterra
solutions `QS n`, `QG n` (`IsVolterraSol`). Source: `thm:app-phase-frozen` (l.1715–1718). -/
structure FrozenSeq (α ς : ℝ) where
  N : ℕ → ℕ
  B : ℕ → ℕ
  ε : ℕ → ℝ
  tendsto_N : Tendsto N atTop atTop
  le_B : ∀ n, 1 ≤ N n ∧ N n ≤ B n
  ε_pos : ∀ n, 0 < ε n
  x_tendsto : Tendsto (fun n => phaseX (α + ς) (N n) (ε n)) atTop (𝓝 0)
  mS : ∀ n, RowModel (Fin (N n))
  mG : ∀ n, RowModel (Fin (N n))
  QS : ℕ → ℝ → ℝ
  QG : ℕ → ℝ → ℝ
  matchS : ∀ n, IsMatchedModel (svdArrays α ς (N n) (B n)) (mS n) (ε n)
  matchG : ∀ n, IsMatchedModel (sgdArrays α ς (N n) (B n)) (mG n) (ε n)
  volS : ∀ n, IsVolterraSol (mS n) (QS n)
  volG : ∀ n, IsVolterraSol (mG n) (QG n)

/-! ## The frozen error bound -/

/-! ### Helpers for `lem_app_phase_frozenerr` (P-H.15.P1) -/

lemma fz_Lsum_fin (N : ℕ) (a q u : ℝ) :
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

lemma fz_Icc_range (F : ℕ → ℝ) (N : ℕ) :
    ∑ i ∈ Finset.Icc 1 N, F i = ∑ i ∈ Finset.range N, F (i + 1) := by
  induction N with
  | zero => simp
  | succ n ih => rw [Finset.sum_Icc_succ_top (by omega), ih, Finset.sum_range_succ]

lemma fz_fNq_eq (N : ℕ) (p q u : ℝ) :
    fNq (N : ℕ∞) p q u = mixF (fun i : Fin N => (1 / 2) * (((i : ℕ) : ℝ) + 1) ^ (-p))
      (fun i : Fin N => 2 * (((i : ℕ) : ℝ) + 1) ^ (-q)) u := by
  unfold fNq mixF
  rw [fz_Lsum_fin, Finset.mul_sum, fz_Icc_range, Fin.sum_univ_eq_sum_range
    (fun i : ℕ => (1 / 2) * (((i : ℕ) : ℝ) + 1) ^ (-p) * Real.exp (-(2 * (((i : ℕ) : ℝ) + 1) ^ (-q) * u))) N]
  refine Finset.sum_congr rfl fun i _ => ?_
  push_cast
  have : -(2 * u) * ((i : ℝ) + 1) ^ (-q) = -(2 * ((i : ℝ) + 1) ^ (-q) * u) := by ring
  rw [this]; ring

lemma fz_ab (N : ℕ) (hN : 1 ≤ N) (p q : ℝ) (hq : 0 < q) :
    (∀ i : Fin N, 0 ≤ (1 / 2) * (((i : ℕ) : ℝ) + 1) ^ (-p)) ∧
    (1 / 2 ≤ ∑ i : Fin N, (1 / 2) * (((i : ℕ) : ℝ) + 1) ^ (-p)) ∧
    (∀ i : Fin N, 2 * (N : ℝ) ^ (-q) ≤ 2 * (((i : ℕ) : ℝ) + 1) ^ (-q)) := by
  refine ⟨fun i => by positivity, ?_, fun i => ?_⟩
  · have h0 : (⟨0, by omega⟩ : Fin N) ∈ (Finset.univ : Finset (Fin N)) := Finset.mem_univ _
    have := Finset.single_le_sum (f := fun i : Fin N => (1 / 2 : ℝ) * (((i : ℕ) : ℝ) + 1) ^ (-p))
      (fun i _ => by positivity) h0
    simpa using this
  · have hi : ((i : ℕ) : ℝ) + 1 ≤ (N : ℝ) := by
      have := i.2
      exact_mod_cast this
    have hpos : (0 : ℝ) < ((i : ℕ) : ℝ) + 1 := by positivity
    have := Real.rpow_le_rpow_of_nonpos hpos hi (by linarith : -q ≤ 0)
    linarith

lemma fz_fNq_le_h {p q : ℝ} (hp : 1 < p) (hq : 0 < q) {D : ℝ} (hD : 1 ≤ D) (N : ℕ)
    {u : ℝ} (hu : 0 ≤ u) :
    fNq (N : ℕ∞) p q u ≤ (Cpq p q * (1 + u / D) ^ (-rq p q)) ^ 2 := by
  have h := lem_app_phase_sums_i hp hq (N : ℕ∞) hu
  have hd : dAQ p q = 2 * rq p q := by unfold dAQ rq; field_simp
  rw [hd] at h
  have hE : 0 < Epq p q := by
    unfold Epq
    refine lt_max_of_lt_left ?_
    have : 0 < Za p := by
      unfold Za
      have := div_pos one_pos (show (0 : ℝ) < p - 1 by linarith)
      linarith
    exact mul_pos (Real.rpow_pos_of_pos (by norm_num) _) this
  have hC : Cpq p q ^ 2 = Epq p q / 2 := by
    unfold Cpq
    rw [Real.sq_sqrt (by positivity)]
  have hDpos : 0 < D := by linarith
  have h1 : 1 + u / D ≤ 1 + u := by
    have : u / D ≤ u := div_le_self hu hD
    linarith
  have h2 : (1 + u) ^ (-(2 * rq p q)) ≤ (1 + u / D) ^ (-(2 * rq p q)) := by
    have hr : 0 < rq p q := by unfold rq; exact div_pos (by linarith) (by linarith)
    exact Real.rpow_le_rpow_of_nonpos (by positivity) h1 (by linarith)
  have h3 : (Cpq p q * (1 + u / D) ^ (-rq p q)) ^ 2 = Cpq p q ^ 2 * (1 + u / D) ^ (-(2 * rq p q)) := by
    rw [mul_pow]
    congr 1
    rw [← Real.rpow_natCast ((1 + u / D) ^ (-rq p q)) 2, ← Real.rpow_mul (by positivity)]
    congr 1
    push_cast; ring
  rw [h3, hC]
  unfold fNq
  nlinarith [h, h2, hE]

lemma fz_int_sqrt_h {C D r u0 : ℝ} (hC : 0 < C) (hD : 0 < D) (hr0 : 0 < r) (hr1 : r < 1)
    (hu0 : 0 ≤ u0) :
    ∫ u in (0 : ℝ)..u0, Real.sqrt (C * (1 + u / D) ^ (-r))
      ≤ Real.sqrt C * D ^ (r / 2) * (D + u0) ^ (1 - r / 2) / (1 - r / 2) := by
  have hs : 0 < 1 - r / 2 := by linarith
  have hpt : ∀ u ∈ Set.uIcc (0 : ℝ) u0, Real.sqrt (C * (1 + u / D) ^ (-r))
      = Real.sqrt C * D ^ (r / 2) * (D + u) ^ (-(r / 2)) := by
    intro u hu
    rw [Set.uIcc_of_le hu0] at hu
    have hDu : 0 < D + u := by linarith [hu.1]
    have h1 : 1 + u / D = (D + u) / D := by field_simp
    have e1 : ((D + u) ^ (-(r / 2))) ^ 2 = (D + u) ^ (-r) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hDu.le]; congr 1; push_cast; ring
    have e2 : (D ^ (r / 2)) ^ 2 = D ^ r := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hD.le]; congr 1; push_cast; ring
    have h2 : (1 + u / D) ^ (-r) = ((D + u) ^ (-(r / 2)) * D ^ (r / 2)) ^ 2 := by
      rw [h1, Real.div_rpow hDu.le hD.le, mul_pow, e1, e2, Real.rpow_neg hD.le]
      field_simp
    rw [h2, Real.sqrt_mul hC.le, Real.sqrt_sq (by positivity)]
    ring
  rw [intervalIntegral.integral_congr hpt, intervalIntegral.integral_const_mul]
  have hI : ∫ u in (0 : ℝ)..u0, (D + u) ^ (-(r / 2)) = ((D + u0) ^ (1 - r / 2) - D ^ (1 - r / 2)) / (1 - r / 2) := by
    rw [intervalIntegral.integral_comp_add_left (fun y : ℝ => y ^ (-(r / 2))) D]
    rw [integral_rpow (Or.inl (by linarith))]
    simp only [add_zero]
    rw [show -(r / 2) + 1 = 1 - r / 2 by ring]
  rw [hI]
  have hpos : 0 < Real.sqrt C * D ^ (r / 2) := by positivity
  have : 0 ≤ D ^ (1 - r / 2) := by positivity
  rw [mul_div_assoc]
  apply mul_le_mul_of_nonneg_left _ hpos.le
  apply div_le_div_of_nonneg_right _ hs.le
  linarith

lemma fz_g_term (w c : ℝ) (hw : 0 ≤ w) (hc : 0 < c) :
    IntegrableOn (fun u : ℝ => w * c * Real.exp (-(c * u))) (Ioi 0) ∧
      ∫ u in Ioi (0 : ℝ), w * c * Real.exp (-(c * u)) = w := by
  have e : (fun u : ℝ => Real.exp (-(c * u))) = fun u => Real.exp ((-c) * u) := by
    funext u; congr 1; ring
  refine ⟨?_, ?_⟩
  · have := Integrable.const_mul (exp_neg_integrableOn_Ioi 0 hc) (w * c)
    refine IntegrableOn.congr_fun this (fun u _ => ?_) measurableSet_Ioi
    simp only [neg_mul]
  · rw [integral_const_mul, e, integral_exp_mul_Ioi (by linarith) 0]
    simp only [mul_zero, Real.exp_zero]
    field_simp

lemma fz_g_int {n' : ℕ} (w c : Fin n' → ℝ) (bmin : ℝ) (hbmin : 0 < bmin)
    (hw : ∀ l, 0 ≤ w l) (hw1 : ∑ l, w l = 1) (hc : ∀ l, bmin ≤ c l) :
    IntegrableOn (mixG w c) (Ioi 0) ∧ ∫ u in Ioi (0 : ℝ), mixG w c u = 1 := by
  have hcp : ∀ l, 0 < c l := fun l => lt_of_lt_of_le hbmin (hc l)
  refine ⟨?_, ?_⟩
  · unfold mixG
    exact integrable_finset_sum _ fun l _ => (fz_g_term (w l) (c l) (hw l) (hcp l)).1
  · unfold mixG
    rw [integral_finset_sum _ fun l _ => (fz_g_term (w l) (c l) (hw l) (hcp l)).1]
    simp_rw [fun l => (fz_g_term (w l) (c l) (hw l) (hcp l)).2]
    exact hw1

lemma fz_g_nonneg {n' : ℕ} (w c : Fin n' → ℝ) (bmin : ℝ)
    (hw : ∀ l, 0 ≤ w l) (hc : ∀ l, bmin ≤ c l) (hbmin : 0 < bmin) (u : ℝ) : 0 ≤ mixG w c u :=
  Finset.sum_nonneg fun l _ =>
    mul_nonneg (mul_nonneg (hw l) (by linarith [hc l])) (Real.exp_pos _).le

lemma fz_sqtail {n n' : ℕ} (a b : Fin n → ℝ) (w c : Fin n' → ℝ) (bmin : ℝ) (hbmin : 0 < bmin)
    (ha : ∀ i, 0 ≤ a i) (hw : ∀ l, 0 ≤ w l) (hw1 : ∑ l, w l = 1) (hc : ∀ l, bmin ≤ c l)
    {ε u0 : ℝ} (hε : 0 < ε) (hu0 : 0 < u0)
    {Y : ℝ → ℝ} (hYc : ContinuousOn Y (Ici 0)) (hYpos : ∀ u ∈ Ici (0 : ℝ), 0 < Y u)
    (hY : ∀ u ∈ Ici (0 : ℝ),
      Y u = mixF a b u + Real.sqrt ε * oneSidedConv (fun v => Real.sqrt (Y v)) (mixG w c) u)
    {h : ℝ → ℝ} (hh_cont : ContinuousOn h (Icc 0 u0)) (hh_nonneg : ∀ u ∈ Icc (0 : ℝ) u0, 0 ≤ h u)
    (hfh : ∀ u ∈ Icc (0 : ℝ) u0, mixF a b u ≤ h u ^ 2)
    (hgh : ∀ u ∈ Icc (0 : ℝ) u0, oneSidedConv h (mixG w c) u ≤ 2 * h u) :
    ∀ u ∈ Icc (0 : ℝ) u0, oneSidedConv (fun v => Real.sqrt (Y v)) (mixG w c) u ≤ 2 * h u + Real.sqrt ε := by
  have hg := fz_g_int w c bmin hbmin hw hw1 hc
  have hgc : ContinuousOn (mixG w c) (Ici 0) := by
    have : Continuous (mixG w c) := by unfold mixG; fun_prop
    exact this.continuousOn
  have hfc : ContinuousOn (mixF a b) (Icc 0 u0) := by
    have : Continuous (mixF a b) := by unfold mixF; fun_prop
    exact this.continuousOn
  have key := lem_app_phase_square_tail (f := mixF a b) (h := h) (wt := fun _ => 0) (g := mixG w c) (Y := Y)
    hε hu0 hgc (fun u _ => fz_g_nonneg w c bmin hw hc hbmin u) hg.1 hg.2.le hfc
    (fun u _ => Finset.sum_nonneg fun i _ => mul_nonneg (ha i) (Real.exp_pos _).le)
    hh_cont hh_nonneg continuousOn_const (fun u _ => le_rfl) hfh
    (fun u hu => by simpa using hgh u hu)
    (fun u hu => by simp [oneSidedConv])
    (hYc.mono Icc_subset_Ici_self) (fun u hu => hYpos u (Icc_subset_Ici_self hu))
    (fun u hu => hY u (Icc_subset_Ici_self hu))
  intro u hu
  have := key.2 u hu
  unfold sqTailG at this
  simpa using this

lemma fz_eps_quarter (ε : ℝ) (hε : 0 < ε) : (ε ^ (1 / 4 : ℝ)) ^ 2 = Real.sqrt ε := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hε.le, Real.sqrt_eq_rpow]
  norm_num

lemma fz_eps {Nr x ε p q : ℝ} (hN : 0 < Nr) (hε : 0 < ε) (hq : 0 < q) (hp : 1 < p)
    (hx : x = ε / Nr ^ (-(p - 1))) :
    ε ^ (1 / 4 : ℝ) = x ^ (1 / 4 : ℝ) * Nr ^ (-(q * rq p q) / 2) ∧
    Real.sqrt ε = x ^ (1 / 2 : ℝ) * Nr ^ (-(q * rq p q)) ∧ 0 < x := by
  have hNp : 0 < Nr ^ (-(p - 1)) := Real.rpow_pos_of_pos hN _
  have hxpos : 0 < x := by rw [hx]; positivity
  have hε' : ε = x * (Nr ^ (-(q * rq p q) / 2)) ^ (4 : ℕ) := by
    have : x * Nr ^ (-(p - 1)) = ε := by rw [hx]; field_simp
    rw [← this, ← Real.rpow_natCast, ← Real.rpow_mul hN.le]
    congr 2
    unfold rq
    push_cast
    field_simp
    norm_num
  have h4 : ε ^ (1 / 4 : ℝ) = x ^ (1 / 4 : ℝ) * Nr ^ (-(q * rq p q) / 2) := by
    have hy : 0 < Nr ^ (-(q * rq p q) / 2) := Real.rpow_pos_of_pos hN _
    have h44 : ((Nr ^ (-(q * rq p q) / 2)) ^ (4 : ℕ)) ^ (1 / 4 : ℝ) = Nr ^ (-(q * rq p q) / 2) := by
      rw [show (1 / 4 : ℝ) = ((4 : ℕ) : ℝ)⁻¹ by norm_num]
      exact Real.pow_rpow_inv_natCast hy.le (by norm_num)
    rw [hε', Real.mul_rpow hxpos.le (by positivity), h44]
  refine ⟨h4, ?_, hxpos⟩
  rw [← fz_eps_quarter ε hε, h4, mul_pow, ← Real.rpow_natCast, ← Real.rpow_mul hxpos.le,
    ← Real.rpow_natCast (Nr ^ (-(q * rq p q) / 2)) 2, ← Real.rpow_mul hN.le]
  congr 2 <;> push_cast <;> ring

lemma fz_sqrt_add {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) :
    Real.sqrt (A + B) ≤ Real.sqrt A + Real.sqrt B := by
  rw [Real.sqrt_le_iff]
  refine ⟨by positivity, ?_⟩
  nlinarith [Real.sq_sqrt hA, Real.sq_sqrt hB, mul_nonneg (Real.sqrt_nonneg A) (Real.sqrt_nonneg B)]

lemma fz_phase1 {ε u0 : ℝ} (hε : 0 < ε) (hu0 : 0 < u0) {Y f h : ℝ → ℝ}
    (hYc : ContinuousOn Y (Icc 0 u0)) (hfc : ContinuousOn f (Icc 0 u0))
    (hhc : ContinuousOn h (Icc 0 u0)) (hf0 : ∀ u ∈ Icc (0 : ℝ) u0, 0 ≤ f u)
    (hh0 : ∀ u ∈ Icc (0 : ℝ) u0, 0 ≤ h u)
    (hpt : ∀ u ∈ Icc (0 : ℝ) u0,
      Real.sqrt (Y u) ≤ Real.sqrt (f u) + ε ^ (1 / 4 : ℝ) * Real.sqrt (2 * h u + Real.sqrt ε)) :
    ∫ u in (0 : ℝ)..u0, Real.sqrt (Y u) ≤
      (∫ u in (0 : ℝ)..u0, Real.sqrt (f u)) +
        ε ^ (1 / 4 : ℝ) * (Real.sqrt 2 * (∫ u in (0 : ℝ)..u0, Real.sqrt (h u)) + ε ^ (1 / 4 : ℝ) * u0) := by
  have hk : 0 < ε ^ (1 / 4 : ℝ) := Real.rpow_pos_of_pos hε _
  have hsq : Real.sqrt (Real.sqrt ε) = ε ^ (1 / 4 : ℝ) := by
    rw [← fz_eps_quarter ε hε, Real.sqrt_sq hk.le]
  have hI : ∀ g : ℝ → ℝ, ContinuousOn g (Icc 0 u0) → IntervalIntegrable g volume 0 u0 := by
    intro g hg
    exact (hg.mono (by rw [Set.uIcc_of_le hu0.le])).intervalIntegrable
  have hsY := hI _ hYc.sqrt
  have hsf := hI _ hfc.sqrt
  have hsh := hI _ hhc.sqrt
  have hrhs : ∫ u in (0 : ℝ)..u0, (Real.sqrt (f u) + ε ^ (1 / 4 : ℝ) * (Real.sqrt 2 * Real.sqrt (h u) + ε ^ (1 / 4 : ℝ)))
      = (∫ u in (0 : ℝ)..u0, Real.sqrt (f u)) +
        ε ^ (1 / 4 : ℝ) * (Real.sqrt 2 * (∫ u in (0 : ℝ)..u0, Real.sqrt (h u)) + ε ^ (1 / 4 : ℝ) * u0) := by
    have hP : IntervalIntegrable (fun u => Real.sqrt 2 * Real.sqrt (h u) + ε ^ (1 / 4 : ℝ)) volume 0 u0 :=
      (hsh.const_mul _).add intervalIntegrable_const
    rw [intervalIntegral.integral_add hsf (hP.const_mul _), intervalIntegral.integral_const_mul,
      intervalIntegral.integral_add (hsh.const_mul _) intervalIntegrable_const,
      intervalIntegral.integral_const_mul]
    simp
    left; ring
  rw [← hrhs]
  refine intervalIntegral.integral_mono_on hu0.le hsY ?_ ?_
  · exact hsf.add (((hsh.const_mul _).add intervalIntegrable_const).const_mul _)
  · intro u hu
    have h1 := hpt u hu
    have h2 : Real.sqrt (2 * h u + Real.sqrt ε) ≤ Real.sqrt 2 * Real.sqrt (h u) + ε ^ (1 / 4 : ℝ) := by
      calc Real.sqrt (2 * h u + Real.sqrt ε) ≤ Real.sqrt (2 * h u) + Real.sqrt (Real.sqrt ε) :=
            fz_sqrt_add (by linarith [hh0 u hu]) (Real.sqrt_nonneg _)
        _ = _ := by rw [Real.sqrt_mul (by norm_num), hsq]
    have := mul_le_mul_of_nonneg_left h2 hk.le
    linarith

lemma fz_assemble {I A0 Jn0 Jt JN P R Jtil dtil Dt : ℝ}
    (hmain : I ≤ A0 + (Real.sqrt Jtil + Real.sqrt dtil) ^ 2)
    (hA : A0 ≤ Jn0 + P) (hJ : Jtil ≤ Jt + R) (hd : dtil ≤ Dt) (hJt0 : 0 ≤ Jt) (hR : 0 ≤ R)
    (hDt : 0 ≤ Dt) (hJN : JN = Jn0 + Jt) (hJn0 : 0 ≤ Jn0) :
    I ≤ JN + (P + R) + 2 * Real.sqrt ((JN + R) * Dt) + Dt := by
  have h1 : Real.sqrt Jtil ≤ Real.sqrt (Jt + R) := Real.sqrt_le_sqrt hJ
  have h2 : Real.sqrt dtil ≤ Real.sqrt Dt := Real.sqrt_le_sqrt hd
  have h3 : (Real.sqrt Jtil + Real.sqrt dtil) ^ 2 ≤ (Real.sqrt (Jt + R) + Real.sqrt Dt) ^ 2 := by
    apply pow_le_pow_left₀ (by positivity)
    linarith
  have h4 : (Real.sqrt (Jt + R) + Real.sqrt Dt) ^ 2
      = (Jt + R) + 2 * Real.sqrt ((Jt + R) * Dt) + Dt := by
    rw [Real.sqrt_mul (by linarith)]
    nlinarith [Real.sq_sqrt (show 0 ≤ Jt + R by linarith), Real.sq_sqrt hDt]
  have h5 : Real.sqrt ((Jt + R) * Dt) ≤ Real.sqrt ((JN + R) * Dt) :=
    Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_right (by linarith) hDt)
  linarith

lemma fz_Cpq_pos {p q : ℝ} (hp : 1 < p) (hq : 0 < q) : 0 < Cpq p q := by
  have hE : 0 < Epq p q := by
    unfold Epq
    refine lt_max_of_lt_left ?_
    have : 0 < Za p := by
      unfold Za
      have := div_pos one_pos (show (0 : ℝ) < p - 1 by linarith)
      linarith
    exact mul_pos (Real.rpow_pos_of_pos (by norm_num) _) this
  unfold Cpq
  exact Real.sqrt_pos.2 (by positivity)

lemma fz_rq_pos {p q : ℝ} (hp : 1 < p) (hq : 0 < q) : 0 < rq p q := by
  unfold rq; exact div_pos (by linarith) (by linarith)

/-- `h(u0) ≤ c₂ N^{-qr}`. -/
lemma fz_hu0 {C r D τ Nr q : ℝ} (hC : 0 < C) (hr : 0 < r) (hD : 0 < D) (hτ : 0 < τ)
    (hN : 0 < Nr) :
    C * (1 + τ * Nr ^ q / D) ^ (-r) ≤ frozenC2 C r D τ * Nr ^ (-(q * r)) := by
  unfold frozenC2
  have hu : 0 < τ * Nr ^ q / D := by positivity
  have h1 : (1 + τ * Nr ^ q / D) ^ (-r) ≤ (τ * Nr ^ q / D) ^ (-r) :=
    Real.rpow_le_rpow_of_nonpos hu (by linarith) (by linarith)
  have h2 : (τ * Nr ^ q / D) ^ (-r) = (D / τ) ^ r * Nr ^ (-(q * r)) := by
    rw [Real.rpow_neg hu.le, ← Real.inv_rpow hu.le, show (τ * Nr ^ q / D)⁻¹ = D / τ * (Nr ^ q)⁻¹ by
      field_simp, Real.mul_rpow (by positivity) (by positivity), Real.inv_rpow (by positivity),
      ← Real.rpow_mul hN.le, ← Real.rpow_neg (by positivity)]
  calc C * (1 + τ * Nr ^ q / D) ^ (-r) ≤ C * ((D / τ) ^ r * Nr ^ (-(q * r))) := by
        rw [← h2]; exact mul_le_mul_of_nonneg_left h1 hC.le
    _ = _ := by ring

lemma fz_scaleP {C r D τ Nr q x ε : ℝ} (hC : 0 < C) (hr0 : 0 < r) (hr1 : r < 1) (hD : 0 < D)
    (hτ : 0 < τ) (hN : 0 < Nr) (hDu : D ≤ τ * Nr ^ q) (hε : 0 < ε) (hx : 0 < x)
    (hk4 : ε ^ (1 / 4 : ℝ) = x ^ (1 / 4 : ℝ) * Nr ^ (-(q * r) / 2))
    (hs2 : Real.sqrt ε = x ^ (1 / 2 : ℝ) * Nr ^ (-(q * r))) :
    ε ^ (1 / 4 : ℝ) * (Real.sqrt 2 * (Real.sqrt C * D ^ (r / 2) * (D + τ * Nr ^ q) ^ (1 - r / 2) / (1 - r / 2))
        + ε ^ (1 / 4 : ℝ) * (τ * Nr ^ q))
      ≤ (frozenC1 C r D τ * x ^ (1 / 4 : ℝ) + τ * x ^ (1 / 2 : ℝ)) * Nr ^ (q * (1 - r)) := by
  have hQ : 0 < Nr ^ q := Real.rpow_pos_of_pos hN _
  have hs : 0 < 1 - r / 2 := by linarith
  have hk : 0 < ε ^ (1 / 4 : ℝ) := Real.rpow_pos_of_pos hε _
  have e1 : Nr ^ (-(q * r) / 2) * Nr ^ (q * (1 - r / 2)) = Nr ^ (q * (1 - r)) := by
    rw [← Real.rpow_add hN]; congr 1; ring
  have e2 : Nr ^ (-(q * r)) * Nr ^ q = Nr ^ (q * (1 - r)) := by
    rw [← Real.rpow_add hN]; congr 1; ring
  have e3 : (Nr ^ q) ^ (1 - r / 2) = Nr ^ (q * (1 - r / 2)) := by
    rw [← Real.rpow_mul hN.le]
  have hkk : ε ^ (1 / 4 : ℝ) * ε ^ (1 / 4 : ℝ) = x ^ (1 / 2 : ℝ) * Nr ^ (-(q * r)) := by
    rw [← sq, fz_eps_quarter ε hε, hs2]
  have ha : (D + τ * Nr ^ q) ^ (1 - r / 2) ≤ (2 * τ) ^ (1 - r / 2) * Nr ^ (q * (1 - r / 2)) := by
    have : D + τ * Nr ^ q ≤ (2 * τ) * Nr ^ q := by nlinarith
    calc (D + τ * Nr ^ q) ^ (1 - r / 2) ≤ ((2 * τ) * Nr ^ q) ^ (1 - r / 2) :=
          Real.rpow_le_rpow (by positivity) this hs.le
      _ = _ := by rw [Real.mul_rpow (by positivity) hQ.le, e3]
  have hC1 : frozenC1 C r D τ = Real.sqrt 2 * (Real.sqrt C * D ^ (r / 2) * (2 * τ) ^ (1 - r / 2) / (1 - r / 2)) := by
    unfold frozenC1
    rw [Real.sqrt_mul (by norm_num)]
    ring
  have hpos : 0 ≤ Real.sqrt 2 * (Real.sqrt C * D ^ (r / 2) / (1 - r / 2)) := by positivity
  have hb : Real.sqrt 2 * (Real.sqrt C * D ^ (r / 2) * (D + τ * Nr ^ q) ^ (1 - r / 2) / (1 - r / 2))
      ≤ frozenC1 C r D τ * Nr ^ (q * (1 - r / 2)) := by
    rw [hC1]
    have : Real.sqrt 2 * (Real.sqrt C * D ^ (r / 2) * (D + τ * Nr ^ q) ^ (1 - r / 2) / (1 - r / 2))
        = Real.sqrt 2 * (Real.sqrt C * D ^ (r / 2) / (1 - r / 2)) * (D + τ * Nr ^ q) ^ (1 - r / 2) := by ring
    rw [this]
    calc _ ≤ Real.sqrt 2 * (Real.sqrt C * D ^ (r / 2) / (1 - r / 2)) *
          ((2 * τ) ^ (1 - r / 2) * Nr ^ (q * (1 - r / 2))) := mul_le_mul_of_nonneg_left ha hpos
      _ = _ := by ring
  have hc : ε ^ (1 / 4 : ℝ) * (Real.sqrt 2 * (Real.sqrt C * D ^ (r / 2) * (D + τ * Nr ^ q) ^ (1 - r / 2) / (1 - r / 2)))
      ≤ ε ^ (1 / 4 : ℝ) * (frozenC1 C r D τ * Nr ^ (q * (1 - r / 2))) :=
    mul_le_mul_of_nonneg_left hb hk.le
  have hd : ε ^ (1 / 4 : ℝ) * (frozenC1 C r D τ * Nr ^ (q * (1 - r / 2)))
      = frozenC1 C r D τ * x ^ (1 / 4 : ℝ) * Nr ^ (q * (1 - r)) := by
    rw [hk4, ← e1]; ring
  have hf : ε ^ (1 / 4 : ℝ) * (ε ^ (1 / 4 : ℝ) * (τ * Nr ^ q)) = τ * x ^ (1 / 2 : ℝ) * Nr ^ (q * (1 - r)) := by
    rw [← mul_assoc, hkk, ← e2]; ring
  calc _ = ε ^ (1 / 4 : ℝ) * (Real.sqrt 2 * (Real.sqrt C * D ^ (r / 2) * (D + τ * Nr ^ q) ^ (1 - r / 2) / (1 - r / 2)))
        + ε ^ (1 / 4 : ℝ) * (ε ^ (1 / 4 : ℝ) * (τ * Nr ^ q)) := by ring
    _ ≤ _ := by rw [hf]; nlinarith [hc, hd]

lemma fz_sqrt_rpow_half {x : ℝ} (hx : 0 ≤ x) : Real.sqrt (x ^ (1 / 2 : ℝ)) = x ^ (1 / 4 : ℝ) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hx]; norm_num

lemma fz_quarter_sq {x : ℝ} (hx : 0 ≤ x) : x ^ (1 / 4 : ℝ) * x ^ (1 / 4 : ℝ) = x ^ (1 / 2 : ℝ) := by
  rw [← Real.rpow_add' hx (by norm_num)]; norm_num

lemma fz_scaleJ {c2 h0 G0 Nr q r x ε : ℝ} (hN : 0 < Nr) (hε : 0 < ε) (hx : 0 < x) (hc2 : 0 ≤ c2)
    (hk4 : ε ^ (1 / 4 : ℝ) = x ^ (1 / 4 : ℝ) * Nr ^ (-(q * r) / 2))
    (hs2 : Real.sqrt ε = x ^ (1 / 2 : ℝ) * Nr ^ (-(q * r)))
    (hh0 : h0 ≤ c2 * Nr ^ (-(q * r))) (hG : G0 ≤ 2 * h0 + Real.sqrt ε) :
    (2 / (2 * Nr ^ (-q))) * ε ^ (1 / 4 : ℝ) * Real.sqrt G0 ≤
      (Real.sqrt (2 * c2) * x ^ (1 / 4 : ℝ) + x ^ (1 / 2 : ℝ)) * Nr ^ (q * (1 - r)) := by
  have hQ : 0 < Nr ^ q := Real.rpow_pos_of_pos hN _
  have hE1 : 0 < Nr ^ (-(q * r) / 2) := Real.rpow_pos_of_pos hN _
  have hx4 : 0 < x ^ (1 / 4 : ℝ) := Real.rpow_pos_of_pos hx _
  have hQ' : 2 / (2 * Nr ^ (-q)) = Nr ^ q := by
    rw [Real.rpow_neg hN.le]; field_simp
  have hE : Nr ^ (-(q * r) / 2) * Nr ^ (-(q * r) / 2) = Nr ^ (-(q * r)) := by
    rw [← Real.rpow_add hN]; congr 1; ring
  have e2 : Nr ^ q * Nr ^ (-(q * r)) = Nr ^ (q * (1 - r)) := by
    rw [← Real.rpow_add hN]; congr 1; ring
  have h1 : G0 ≤ (2 * c2 + x ^ (1 / 2 : ℝ)) * (Nr ^ (-(q * r) / 2)) ^ 2 := by
    rw [sq, hE]
    rw [hs2] at hG
    nlinarith [hh0]
  have h2 : Real.sqrt G0 ≤ (Real.sqrt (2 * c2) + x ^ (1 / 4 : ℝ)) * Nr ^ (-(q * r) / 2) := by
    calc Real.sqrt G0 ≤ Real.sqrt ((2 * c2 + x ^ (1 / 2 : ℝ)) * (Nr ^ (-(q * r) / 2)) ^ 2) :=
          Real.sqrt_le_sqrt h1
      _ = Real.sqrt (2 * c2 + x ^ (1 / 2 : ℝ)) * Nr ^ (-(q * r) / 2) := by
          rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hE1.le]
      _ ≤ _ := by
          apply mul_le_mul_of_nonneg_right _ hE1.le
          have := fz_sqrt_add (A := 2 * c2) (B := x ^ (1 / 2 : ℝ)) (by linarith) (by positivity)
          rwa [fz_sqrt_rpow_half hx.le] at this
  rw [hQ', hk4]
  calc Nr ^ q * (x ^ (1 / 4 : ℝ) * Nr ^ (-(q * r) / 2)) * Real.sqrt G0
      ≤ Nr ^ q * (x ^ (1 / 4 : ℝ) * Nr ^ (-(q * r) / 2)) *
        ((Real.sqrt (2 * c2) + x ^ (1 / 4 : ℝ)) * Nr ^ (-(q * r) / 2)) :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = (Real.sqrt (2 * c2) * x ^ (1 / 4 : ℝ) + x ^ (1 / 4 : ℝ) * x ^ (1 / 4 : ℝ)) *
        (Nr ^ q * (Nr ^ (-(q * r) / 2) * Nr ^ (-(q * r) / 2))) := by ring
    _ = _ := by rw [hE, fz_quarter_sq hx.le, e2]

lemma fz_scaleD {c2 h0 Nr q r x ε : ℝ} (hN : 0 < Nr) (hε : 0 < ε) (hx : 0 < x) (hc2 : 0 ≤ c2)
    (hs2 : Real.sqrt ε = x ^ (1 / 2 : ℝ) * Nr ^ (-(q * r)))
    (hh00 : 0 ≤ h0) (hh0 : h0 ≤ c2 * Nr ^ (-(q * r))) :
    (4 / (2 * Nr ^ (-q))) * Real.sqrt ε * Real.log (1 + (h0 + 0) / Real.sqrt ε) ≤
      2 * x ^ (1 / 2 : ℝ) * Real.log (1 + c2 * x ^ (-(1 / 2 : ℝ))) * Nr ^ (q * (1 - r)) := by
  have hQ : 0 < Nr ^ q := Real.rpow_pos_of_pos hN _
  have hE : 0 < Nr ^ (-(q * r)) := Real.rpow_pos_of_pos hN _
  have hxh : 0 < x ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hx _
  have hsε : 0 < Real.sqrt ε := Real.sqrt_pos.2 hε
  have hQ' : 4 / (2 * Nr ^ (-q)) = 2 * Nr ^ q := by
    rw [Real.rpow_neg hN.le]; field_simp; norm_num
  have e2 : Nr ^ q * Nr ^ (-(q * r)) = Nr ^ (q * (1 - r)) := by
    rw [← Real.rpow_add hN]; congr 1; ring
  have hdiv : (h0 + 0) / Real.sqrt ε ≤ c2 * x ^ (-(1 / 2 : ℝ)) := by
    rw [add_zero, div_le_iff₀ hsε, hs2, Real.rpow_neg hx.le]
    calc h0 ≤ c2 * Nr ^ (-(q * r)) := hh0
      _ = c2 * (x ^ (1 / 2 : ℝ))⁻¹ * (x ^ (1 / 2 : ℝ) * Nr ^ (-(q * r))) := by field_simp
  have hlog : Real.log (1 + (h0 + 0) / Real.sqrt ε) ≤ Real.log (1 + c2 * x ^ (-(1 / 2 : ℝ))) :=
    Real.log_le_log (by positivity) (by linarith)
  rw [hQ']
  calc 2 * Nr ^ q * Real.sqrt ε * Real.log (1 + (h0 + 0) / Real.sqrt ε)
      ≤ 2 * Nr ^ q * Real.sqrt ε * Real.log (1 + c2 * x ^ (-(1 / 2 : ℝ))) :=
        mul_le_mul_of_nonneg_left hlog (by positivity)
    _ = 2 * x ^ (1 / 2 : ℝ) * Real.log (1 + c2 * x ^ (-(1 / 2 : ℝ))) * (Nr ^ q * Nr ^ (-(q * r))) := by
        rw [hs2]; ring
    _ = _ := by rw [e2]

lemma fz_mx_bound_integrable {bmin c : ℝ} (hbmin : 0 < bmin) :
    IntegrableOn (fun u : ℝ => c * Real.exp (-(bmin * u) / 2)) (Ioi 0) := by
  have h : IntegrableOn (fun u : ℝ => c * Real.exp (-(bmin / 2) * u)) (Ioi 0) :=
    Integrable.const_mul (exp_neg_integrableOn_Ioi 0 (b := bmin / 2) (by positivity)) c
  refine IntegrableOn.congr_fun h (fun u _ => ?_) measurableSet_Ioi
  rw [show -(bmin * u) / 2 = -(bmin / 2) * u by ring]

lemma fz_mx_F_le {n : ℕ} (a b : Fin n → ℝ) (bmin : ℝ) (ha : ∀ i, 0 ≤ a i)
    (hb : ∀ i, bmin ≤ b i) {u : ℝ} (hu : 0 ≤ u) :
    mixF a b u ≤ (∑ i, a i) * Real.exp (-(bmin * u)) := by
  unfold mixF
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left ?_ (ha i)
  apply Real.exp_le_exp.2
  have := mul_le_mul_of_nonneg_right (hb i) hu
  linarith

lemma fz_mx_sqrt_le {n : ℕ} (a b : Fin n → ℝ) (bmin : ℝ) (ha : ∀ i, 0 ≤ a i)
    (hb : ∀ i, bmin ≤ b i) {u : ℝ} (hu : 0 ≤ u) :
    Real.sqrt (mixF a b u) ≤ Real.sqrt (∑ i, a i) * Real.exp (-(bmin * u) / 2) := by
  have hF0 : 0 ≤ ∑ i, a i := Finset.sum_nonneg fun i _ => ha i
  have hsq : Real.exp (-(bmin * u) / 2) ^ 2 = Real.exp (-(bmin * u)) := by
    rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  rw [Real.sqrt_le_iff]
  refine ⟨mul_nonneg (Real.sqrt_nonneg _) (Real.exp_pos _).le, ?_⟩
  rw [mul_pow, Real.sq_sqrt hF0, hsq]
  exact fz_mx_F_le a b bmin ha hb hu

lemma fz_mx_sqrt_integrable {n : ℕ} (a b : Fin n → ℝ) (bmin : ℝ) (hbmin : 0 < bmin)
    (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, bmin ≤ b i) :
    IntegrableOn (fun u => Real.sqrt (mixF a b u)) (Ioi 0) := by
  refine Integrable.mono' (fz_mx_bound_integrable (c := Real.sqrt (∑ i, a i)) hbmin) ?_ ?_
  · exact (by unfold mixF; fun_prop : Continuous fun u => Real.sqrt (mixF a b u)).aestronglyMeasurable
  · refine ae_restrict_of_forall_mem measurableSet_Ioi fun u hu => ?_
    rw [Real.norm_of_nonneg (Real.sqrt_nonneg _)]
    exact fz_mx_sqrt_le a b bmin ha hb (le_of_lt hu)

lemma fz_split {g : ℝ → ℝ} (hg : IntegrableOn g (Ioi 0)) {u0 : ℝ} (hu0 : 0 ≤ u0) :
    ∫ u in Ioi (0 : ℝ), g u = (∫ u in (0 : ℝ)..u0, g u) + ∫ u in Ioi u0, g u := by
  rw [intervalIntegral.integral_of_le hu0, ← setIntegral_union (Ioc_disjoint_Ioi le_rfl)
    measurableSet_Ioi]
  · rw [Set.Ioc_union_Ioi_eq_Ioi hu0]
  · exact hg.mono_set Ioc_subset_Ioi_self
  · exact hg.mono_set (Ioi_subset_Ioi hu0)

lemma fz_restartD {bmin ε Y0 h0 : ℝ} (hbmin : 0 < bmin) (hε : 0 < ε) (hY0 : 0 < Y0)
    (hh0 : 0 ≤ h0) (hYle : Y0 ≤ (h0 + 0 + Real.sqrt ε) ^ 2) :
    restartD bmin ε Y0 ≤ (4 / bmin) * Real.sqrt ε * Real.log (1 + (h0 + 0) / Real.sqrt ε) := by
  have hsε : 0 < Real.sqrt ε := Real.sqrt_pos.2 hε
  have hq2 : Real.sqrt ε ^ 2 = ε := Real.sq_sqrt hε.le
  have key : ∀ s : ℝ, 0 < s → Y0 ≤ (h0 + 0 + s) ^ 2 → Y0 / s ^ 2 ≤ (1 + (h0 + 0) / s) ^ 2 := by
    intro s hs hY
    rw [div_le_iff₀ (by positivity)]
    have : (1 + (h0 + 0) / s) ^ 2 * s ^ 2 = (h0 + 0 + s) ^ 2 := by field_simp; ring
    rw [this]; exact hY
  have h1 : Y0 / ε ≤ (1 + (h0 + 0) / Real.sqrt ε) ^ 2 := by
    have := key _ hsε hYle
    rwa [hq2] at this
  have h2 : Real.log (Y0 / ε) ≤ 2 * Real.log (1 + (h0 + 0) / Real.sqrt ε) := by
    have := Real.log_le_log (div_pos hY0 hε) h1
    rwa [Real.log_pow] at this
  unfold restartD
  have hco : 0 ≤ (2 / bmin) * Real.sqrt ε := by positivity
  calc 2 / bmin * Real.sqrt ε * Real.log (Y0 / ε)
      ≤ 2 / bmin * Real.sqrt ε * (2 * Real.log (1 + (h0 + 0) / Real.sqrt ε)) :=
        mul_le_mul_of_nonneg_left h2 hco
    _ = _ := by ring

lemma fz_firstHit_le {Y : ℝ → ℝ} {a u : ℝ} (hu : 0 ≤ u) (hYu : Y u ≤ a) :
    firstHit Y a ≤ ENNReal.ofReal u := by
  unfold firstHit
  refine iInf₂_le_of_le u.toNNReal ?_ le_rfl
  rwa [Real.coe_toNNReal u hu]


/-- Label `eqn:app-phase-frozenerr`, displayed in the proof of `thm:app-phase-frozen`, snapshot
`cr-2026-10-23`. Source: section.tex l.3492–3494 (valid for every `x > 0`, l.3571), with
`a_1, a_2` of l.3500–3501 (encoded in `frozenA1`, `frozenA2`), and the bound `d̃ ≤ dt N^{e}` of
l.3478–3481 (encoded in `frozenDt`). Verbatim display:
```latex
\begin{equation}\label{eqn:app-phase-frozenerr}
\mathsf I\le J_N+a_1(x)N^{\mathsf e_r}+2\sqrt{\big(J_N+a_2(x)N^{\mathsf e_r}\big)\tilde{\mathsf d}}+\tilde{\mathsf d},
\end{equation}
```
Hypotheses (proof-side, section.tex l.3440–3512): the phase-one data `(D, τ)` enters through
`PhaseOneBound` at size `N` (the caller supplies it for `N ≥ N°`); `D ≤ τ N^q` is the condition
`D ≤ u_0` of the proof; `ε < 1/(2T)` is the standing condition of the frozen section; `Y` is the
continuous positive solution of the dimensionless equation `Y_j = f_{N,q_j} + √ε g_j * √Y_j`
(section.tex l.1136, `prop:app-phase-prefactors`(ii)). Lemma reused by `thm:app-phase-unified` (card §3). -/
theorem lem_app_phase_frozenerr {p q T ε : ℝ} (hp : 1 < p) (hq : 0 < q) (hr : rq p q < 1)
    (hT : 4 ≤ T) (hε : 0 < ε) (hεT : ε < 1 / (2 * T))
    {N : ℕ} (hN : 4 ≤ N) {D τ : ℝ} (hD : 1 ≤ D) (hτ : 0 < τ) (hDτ : D ≤ τ * (N : ℝ) ^ q)
    {n' : ℕ} (w c : Fin n' → ℝ) (hw : ∀ l, 0 ≤ w l) (hw1 : ∑ l, w l = 1)
    (hc : ∀ l, 2 * (N : ℝ) ^ (-q) ≤ c l)
    (hg : PhaseOneBound (mixG w c) (Cpq p q) q (rq p q) D τ N)
    (Y : ℝ → ℝ) (hYc : ContinuousOn Y (Ici 0)) (hYpos : ∀ u ∈ Ici (0 : ℝ), 0 < Y u)
    (hY : ∀ u ∈ Ici (0 : ℝ),
      Y u = fNq (N : ℕ∞) p q u +
        Real.sqrt ε * oneSidedConv (fun v => Real.sqrt (Y v)) (mixG w c) u) :
    dimClockI Y T ε ≤
      frozenErrBound (Cpq p q) q (rq p q) D τ (phaseX p N ε) N (JN N p q) := by
  have hN1 : 1 ≤ N := by omega
  have hNr : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hr0 := fz_rq_pos hp hq
  have hC := fz_Cpq_pos hp hq
  have hDpos : 0 < D := by linarith
  have hTpos : 0 < T := by linarith
  obtain ⟨a, b, hfa, ha, hF, hb⟩ : ∃ a b : Fin N → ℝ, (∀ u, fNq (N : ℕ∞) p q u = mixF a b u) ∧
      (∀ i, 0 ≤ a i) ∧ 1 / 2 ≤ ∑ i, a i ∧ ∀ i, 2 * (N : ℝ) ^ (-q) ≤ b i := by
    obtain ⟨h1, h2, h3⟩ := fz_ab N hN1 p q hq
    exact ⟨_, _, fz_fNq_eq N p q, h1, h2, h3⟩
  have hbmin : 0 < 2 * (N : ℝ) ^ (-q) := by positivity
  have hF0 : 0 < ∑ i, a i := by linarith
  have hY' : ∀ u ∈ Ici (0 : ℝ),
      Y u = mixF a b u + Real.sqrt ε * oneSidedConv (fun v => Real.sqrt (Y v)) (mixG w c) u := by
    intro u hu; rw [hY u hu, hfa]
  have hQ : 0 < (N : ℝ) ^ q := Real.rpow_pos_of_pos hNr _
  obtain ⟨u0, hu0def⟩ : ∃ u0 : ℝ, u0 = τ * (N : ℝ) ^ q := ⟨_, rfl⟩
  have hu0 : 0 < u0 := by rw [hu0def]; positivity
  have hDu0 : D ≤ u0 := by rw [hu0def]; exact hDτ
  obtain ⟨h, hh⟩ : ∃ h : ℝ → ℝ, h = fun u => Cpq p q * (1 + u / D) ^ (-rq p q) := ⟨_, rfl⟩
  have hpos1 : ∀ u ∈ Icc (0 : ℝ) u0, 0 < 1 + u / D := fun u hu => by
    have : 0 ≤ u / D := div_nonneg hu.1 hDpos.le
    linarith
  have hhc : ContinuousOn h (Icc 0 u0) := by
    rw [hh]
    exact continuousOn_const.mul (ContinuousOn.rpow_const (by fun_prop)
      (fun u hu => Or.inl (hpos1 u hu).ne'))
  have hh0 : ∀ u ∈ Icc (0 : ℝ) u0, 0 ≤ h u := fun u hu => by
    rw [hh]; have := hpos1 u hu; positivity
  have hfh : ∀ u ∈ Icc (0 : ℝ) u0, mixF a b u ≤ h u ^ 2 := fun u hu => by
    rw [← hfa, hh]; exact fz_fNq_le_h hp hq hD N hu.1
  have hgh : ∀ u ∈ Icc (0 : ℝ) u0, oneSidedConv h (mixG w c) u ≤ 2 * h u := by
    intro u hu
    have := hg u (by rw [← hu0def]; exact hu)
    rw [hh]; exact this
  have hεF : ε < (∑ i, a i) / T := by
    calc ε < 1 / (2 * T) := hεT
      _ = (1 / 2) / T := by field_simp
      _ ≤ (∑ i, a i) / T := div_le_div_of_nonneg_right hF hTpos.le
  have hmix_nn : ∀ u, 0 ≤ mixF a b u := fun u =>
    Finset.sum_nonneg fun i _ => mul_nonneg (ha i) (Real.exp_pos _).le
  have hmix_c : Continuous (mixF a b) := by unfold mixF; fun_prop
  have hgh2 : ∀ u ∈ Icc (0 : ℝ) u0, oneSidedConv h (mixG w c) u ≤ 2 * h u + (fun _ : ℝ => (0 : ℝ)) u ^ 2 / Real.sqrt ε := by
    intro u hu; simpa using hgh u hu
  have hgw : ∀ u ∈ Icc (0 : ℝ) u0, oneSidedConv (fun _ : ℝ => (0 : ℝ)) (mixG w c) u ≤ 2 * (fun _ : ℝ => (0 : ℝ)) u := by
    intro u hu; simp [oneSidedConv]
  have T1 := lem_app_phase_twophase_i a b w c _ hbmin ha hF0 hb hw hw1 hc hT hε hεF hu0 hYc hYpos hY'
    hhc hh0 continuousOn_const (fun u _ => le_rfl) hfh hgh2 hgw
  have T3 := lem_app_phase_twophase_iii a b w c _ hbmin ha hF0 hb hw hw1 hc hT hε hεF hu0 hYc hYpos hY'
    hhc hh0 continuousOn_const (fun u _ => le_rfl) hfh hgh2 hgw
  have G0b := fz_sqtail a b w c _ hbmin ha hw hw1 hc hε hu0 hYc hYpos hY' hhc hh0 hfh hgh
  obtain ⟨û, hû, hI, -, hd⟩ := T3
  obtain ⟨hk4, hs2, hxpos⟩ := fz_eps (Nr := (N : ℝ)) (x := phaseX p N ε) (q := q) hNr hε hq hp rfl
  generalize phaseX p N ε = x at hk4 hs2 hxpos ⊢
  have hcc2 : 0 ≤ frozenC2 (Cpq p q) (rq p q) D τ := by unfold frozenC2; positivity
  have hhu0 : h u0 ≤ frozenC2 (Cpq p q) (rq p q) D τ * (N : ℝ) ^ (-(q * rq p q)) := by
    simp only [hh]; rw [hu0def]; exact fz_hu0 hC hr0 hDpos hτ hNr
  have hJint := fz_mx_sqrt_integrable a b _ hbmin ha hb
  have hJNeq : JN N p q = ∫ u in Ioi (0 : ℝ), Real.sqrt (mixF a b u) := by
    unfold JN; congr 1; funext u; rw [hfa]
  have hsplit := fz_split hJint hu0.le
  have hJt0 : 0 ≤ ∫ u in Ioi u0, Real.sqrt (mixF a b u) :=
    setIntegral_nonneg measurableSet_Ioi (fun _ _ => Real.sqrt_nonneg _)
  have hJn0 : 0 ≤ ∫ u in (0 : ℝ)..u0, Real.sqrt (mixF a b u) :=
    intervalIntegral.integral_nonneg hu0.le (fun _ _ => Real.sqrt_nonneg _)
  -- phase one
  have hP1 := fz_phase1 hε hu0 (Y := Y) (f := mixF a b) (h := h)
    (hYc.mono Icc_subset_Ici_self) hmix_c.continuousOn hhc (fun u _ => hmix_nn u) hh0
    (fun u hu => by
      have h1 := (T1 u hu).2
      have e : sqTailG h (fun _ => (0 : ℝ)) ε u = 2 * h u + Real.sqrt ε := by simp [sqTailG]
      rwa [e] at h1)
  have hIh : ∫ u in (0 : ℝ)..u0, Real.sqrt (h u) ≤
      Real.sqrt (Cpq p q) * D ^ (rq p q / 2) * (D + u0) ^ (1 - rq p q / 2) / (1 - rq p q / 2) := by
    simp only [hh]; exact fz_int_sqrt_h hC hDpos hr0 hr hu0.le
  have hk : 0 < ε ^ (1 / 4 : ℝ) := Real.rpow_pos_of_pos hε _
  have hsc := fz_scaleP (C := Cpq p q) (r := rq p q) (D := D) (τ := τ) (Nr := (N : ℝ)) (q := q) (x := x)
    (ε := ε) hC hr0 hr hDpos hτ hNr hDτ hε hxpos hk4 hs2
  have hA : ∫ u in (0 : ℝ)..u0, Real.sqrt (Y u) ≤ (∫ u in (0 : ℝ)..u0, Real.sqrt (mixF a b u)) +
      (frozenC1 (Cpq p q) (rq p q) D τ * x ^ (1 / 4 : ℝ) + τ * x ^ (1 / 2 : ℝ)) * (N : ℝ) ^ (q * (1 - rq p q)) := by
    have h2 : ε ^ (1 / 4 : ℝ) * (Real.sqrt 2 * (∫ u in (0 : ℝ)..u0, Real.sqrt (h u)) + ε ^ (1 / 4 : ℝ) * u0)
        ≤ ε ^ (1 / 4 : ℝ) * (Real.sqrt 2 * (Real.sqrt (Cpq p q) * D ^ (rq p q / 2) * (D + u0) ^ (1 - rq p q / 2) / (1 - rq p q / 2)) + ε ^ (1 / 4 : ℝ) * u0) := by
      gcongr
    rw [hu0def] at h2 hP1 ⊢
    rw [hu0def] at hIh
    linarith
  have hA2 : 0 ≤ frozenA2 (Cpq p q) (rq p q) D τ x := by
    unfold frozenA2; positivity
  have hDt0 : 0 ≤ frozenDt (Cpq p q) (rq p q) D τ x := by
    unfold frozenDt
    refine mul_nonneg (by positivity) (Real.log_nonneg ?_)
    have : 0 ≤ frozenC2 (Cpq p q) (rq p q) D τ * x ^ (-(1 / 2 : ℝ)) := by positivity
    linarith
  have hNe : 0 < (N : ℝ) ^ (q * (1 - rq p q)) := Real.rpow_pos_of_pos hNr _
  have hG0 := G0b u0 ⟨hu0.le, le_rfl⟩
  have hsJ := fz_scaleJ (c2 := frozenC2 (Cpq p q) (rq p q) D τ) (h0 := h u0) (Nr := (N : ℝ)) (q := q)
    (r := rq p q) (x := x) (ε := ε) hNr hε hxpos hcc2 hk4 hs2 hhu0 hG0
  have hsD := fz_scaleD (c2 := frozenC2 (Cpq p q) (rq p q) D τ) (h0 := h u0) (Nr := (N : ℝ)) (q := q)
    (r := rq p q) (x := x) (ε := ε) hNr hε hxpos hcc2 hs2 (hh0 u0 ⟨hu0.le, le_rfl⟩) hhu0
  have hJ : restartJ (mixF a b) (2 * (N : ℝ) ^ (-q)) ε
      (oneSidedConv (fun v => Real.sqrt (Y v)) (mixG w c) u0) u0 ≤
      (∫ u in Ioi u0, Real.sqrt (mixF a b u)) + frozenA2 (Cpq p q) (rq p q) D τ x * (N : ℝ) ^ (q * (1 - rq p q)) := by
    unfold restartJ frozenA2
    linarith
  have hDd : restartD (2 * (N : ℝ) ^ (-q)) ε (Y u0) ≤
      frozenDt (Cpq p q) (rq p q) D τ x * (N : ℝ) ^ (q * (1 - rq p q)) := by
    refine hd.trans ?_
    unfold frozenDt
    simpa using hsD
  have hsum : (frozenC1 (Cpq p q) (rq p q) D τ * x ^ (1 / 4 : ℝ) + τ * x ^ (1 / 2 : ℝ)) * (N : ℝ) ^ (q * (1 - rq p q))
      + frozenA2 (Cpq p q) (rq p q) D τ x * (N : ℝ) ^ (q * (1 - rq p q))
      = frozenA1 (Cpq p q) (rq p q) D τ x * (N : ℝ) ^ (q * (1 - rq p q)) := by
    unfold frozenA1 frozenA2; ring
  have hP0 : 0 ≤ (frozenC1 (Cpq p q) (rq p q) D τ * x ^ (1 / 4 : ℝ) + τ * x ^ (1 / 2 : ℝ)) * (N : ℝ) ^ (q * (1 - rq p q)) := by
    have hc1 : 0 ≤ frozenC1 (Cpq p q) (rq p q) D τ := by
      unfold frozenC1
      exact div_nonneg (by positivity) (by linarith)
    positivity
  have hYcI : ContinuousOn (fun u => Real.sqrt (Y u)) (Ici 0) := hYc.sqrt
  have hII : ∀ s t : ℝ, 0 ≤ s → 0 ≤ t → IntervalIntegrable (fun u => Real.sqrt (Y u)) volume s t := by
    intro s t hs ht
    refine (hYcI.mono ?_).intervalIntegrable
    intro u hu
    rw [Set.uIcc] at hu
    exact Set.mem_Ici.2 (le_trans (le_min hs ht) hu.1)
  unfold dimClockI
  by_cases hcase : ∀ u ∈ Icc (0 : ℝ) u0, T * ε < Y u
  · obtain ⟨û, hû, hlt, -, hint⟩ := lem_app_phase_restart a b w c _ hbmin ha hF0 hb hw hw1 hc hT hε hu0.le
      hYc hYpos hY' hcase
    rw [hû, ENNReal.toReal_ofReal (by linarith)]
    have hadj := intervalIntegral.integral_add_adjacent_intervals (hII 0 u0 le_rfl hu0.le) (hII u0 û hu0.le (by linarith))
    have hmain : ∫ u in (0 : ℝ)..û, Real.sqrt (Y u) ≤ (∫ u in (0 : ℝ)..u0, Real.sqrt (Y u)) +
        (Real.sqrt (restartJ (mixF a b) (2 * (N : ℝ) ^ (-q)) ε
          (oneSidedConv (fun v => Real.sqrt (Y v)) (mixG w c) u0) u0)
        + Real.sqrt (restartD (2 * (N : ℝ) ^ (-q)) ε (Y u0))) ^ 2 := by
      linarith
    have hDd : restartD (2 * (N : ℝ) ^ (-q)) ε (Y u0) ≤
        frozenDt (Cpq p q) (rq p q) D τ x * (N : ℝ) ^ (q * (1 - rq p q)) := by
      refine (fz_restartD hbmin hε (hYpos u0 (Set.mem_Ici.2 hu0.le)) (hh0 u0 ⟨hu0.le, le_rfl⟩)
        (by simpa using (T1 u0 ⟨hu0.le, le_rfl⟩).1)).trans ?_
      unfold frozenDt
      simpa using hsD
    have hfin := fz_assemble hmain hA hJ hDd hJt0
      (mul_nonneg hA2 hNe.le) (mul_nonneg hDt0 hNe.le) (hJNeq.trans hsplit) hJn0
    rw [hsum] at hfin
    unfold frozenErrBound
    exact hfin
  · simp only [not_forall, not_lt] at hcase
    obtain ⟨u1, hu1, hYu1⟩ := hcase
    have hfh1 := fz_firstHit_le (Y := Y) hu1.1 hYu1
    have hlt : firstHit Y (T * ε) ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hfh1
    have ht1 : (firstHit Y (T * ε)).toReal ≤ u0 := by
      have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hfh1
      rw [ENNReal.toReal_ofReal hu1.1] at this
      linarith [hu1.2]
    have ht0 : 0 ≤ (firstHit Y (T * ε)).toReal := ENNReal.toReal_nonneg
    have hadj := intervalIntegral.integral_add_adjacent_intervals
      (hII 0 (firstHit Y (T * ε)).toReal le_rfl ht0) (hII (firstHit Y (T * ε)).toReal u0 ht0 hu0.le)
    have hnn : 0 ≤ ∫ u in (firstHit Y (T * ε)).toReal..u0, Real.sqrt (Y u) :=
      intervalIntegral.integral_nonneg ht1 (fun _ _ => Real.sqrt_nonneg _)
    have hsq : 0 ≤ Real.sqrt ((JN N p q + frozenA2 (Cpq p q) (rq p q) D τ x * (N : ℝ) ^ (q * (1 - rq p q))) *
        (frozenDt (Cpq p q) (rq p q) D τ x * (N : ℝ) ^ (q * (1 - rq p q)))) := Real.sqrt_nonneg _
    have hRn : 0 ≤ frozenA2 (Cpq p q) (rq p q) D τ x * (N : ℝ) ^ (q * (1 - rq p q)) := mul_nonneg hA2 hNe.le
    have hDn : 0 ≤ frozenDt (Cpq p q) (rq p q) D τ x * (N : ℝ) ^ (q * (1 - rq p q)) := mul_nonneg hDt0 hNe.le
    unfold frozenErrBound
    rw [← hsum]
    have := hJNeq.trans hsplit
    linarith

/-! ### Helpers for `thm_app_phase_frozen_i`, `thm_app_phase_frozen_ii` (P-H.15.P2) -/

lemma fz2_Lsum_fin (N : ℕ) (a q u : ℝ) :
    Lsum (N : ℕ∞) a q u = ∑ i : Fin N, (((i : ℕ) : ℝ) + 1) ^ (-a) *
      Real.exp (-(2 * (((i : ℕ) : ℝ) + 1) ^ (-q) * u)) := by
  rw [fz_Lsum_fin, fz_Icc_range, Fin.sum_univ_eq_sum_range
    (fun i : ℕ => (((i : ℕ) : ℝ) + 1) ^ (-a) * Real.exp (-(2 * (((i : ℕ) : ℝ) + 1) ^ (-q) * u))) N]
  refine Finset.sum_congr rfl fun i _ => ?_
  push_cast
  have : -(2 * u) * ((i : ℝ) + 1) ^ (-q) = -(2 * ((i : ℝ) + 1) ^ (-q) * u) := by ring
  rw [this]

lemma fz2_Hsum_fin (a : ℝ) (N : ℕ) :
    Hsum a N = ∑ i : Fin N, (((i : ℕ) : ℝ) + 1) ^ (-a) := by
  unfold Hsum
  rw [fz_Icc_range, Fin.sum_univ_eq_sum_range (fun i : ℕ => (((i : ℕ) : ℝ) + 1) ^ (-a)) N]
  refine Finset.sum_congr rfl fun i _ => ?_
  push_cast; rfl

lemma fz2_Hsum_pos (a : ℝ) (N : ℕ) (hN : 1 ≤ N) : 0 < Hsum a N := by
  rw [fz2_Hsum_fin]
  have h0 : (⟨0, by omega⟩ : Fin N) ∈ (Finset.univ : Finset (Fin N)) := Finset.mem_univ _
  have := Finset.single_le_sum (f := fun i : Fin N => (((i : ℕ) : ℝ) + 1) ^ (-a))
    (fun i _ => by positivity) h0
  simp only [Nat.cast_zero, zero_add, Real.one_rpow] at this
  linarith

lemma fz2_svd_mix (α : ℝ) (N : ℕ) (hN : 1 ≤ N) :
    ∃ w c : Fin N → ℝ, (∀ l, 0 ≤ w l) ∧ ∑ l, w l = 1 ∧
      (∀ l, c l = 2 * (((l : ℕ) : ℝ) + 1) ^ (-(α / 2))) ∧
      ∀ u, svdKernel α N u = mixG w c u := by
  have hH := fz2_Hsum_pos (α / 2) N hN
  refine ⟨fun l => (((l : ℕ) : ℝ) + 1) ^ (-(α / 2)) / Hsum (α / 2) N,
    fun l => 2 * (((l : ℕ) : ℝ) + 1) ^ (-(α / 2)), fun l => by positivity, ?_, fun l => rfl, ?_⟩
  · rw [← Finset.sum_div, ← fz2_Hsum_fin, div_self hH.ne']
  · intro u
    unfold svdKernel mixG
    rw [fz2_Lsum_fin, Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    have hx : (0 : ℝ) < ((l : ℕ) : ℝ) + 1 := by positivity
    have e : (((l : ℕ) : ℝ) + 1) ^ (-α) = (((l : ℕ) : ℝ) + 1) ^ (-(α / 2)) * (((l : ℕ) : ℝ) + 1) ^ (-(α / 2)) := by
      rw [← Real.rpow_add hx]; congr 1; ring
    rw [e]
    field_simp

lemma fz2_sgd_mix (α : ℝ) (N : ℕ) (hN : 1 ≤ N) :
    ∃ w c : Fin N → ℝ, (∀ l, 0 ≤ w l) ∧ ∑ l, w l = 1 ∧
      (∀ l, c l = 2 * (((l : ℕ) : ℝ) + 1) ^ (-α)) ∧
      ∀ u, sgdKernel α N u = mixG w c u := by
  have hH := fz2_Hsum_pos α N hN
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hpi : 2 < Real.pi := by linarith [Real.pi_gt_three]
  have hpi0 : 0 < Real.pi := by linarith
  have hc : 0 ≤ 1 - 2 / Real.pi := by
    rw [sub_nonneg, div_le_one hpi0]; linarith
  refine ⟨fun l => (1 - 2 / Real.pi) / (N : ℝ) + 2 / (Real.pi * Hsum α N) * (((l : ℕ) : ℝ) + 1) ^ (-α),
    fun l => 2 * (((l : ℕ) : ℝ) + 1) ^ (-α), fun l => by positivity, ?_, fun l => rfl, ?_⟩
  · rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← fz2_Hsum_fin]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
    ring
  · intro u
    unfold sgdKernel mixG
    rw [fz2_Lsum_fin, fz2_Lsum_fin, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun l _ => ?_
    have hx : (0 : ℝ) < ((l : ℕ) : ℝ) + 1 := by positivity
    have e : (((l : ℕ) : ℝ) + 1) ^ (-(2 * α)) = (((l : ℕ) : ℝ) + 1) ^ (-α) * (((l : ℕ) : ℝ) + 1) ^ (-α) := by
      rw [← Real.rpow_add hx]; congr 1; ring
    rw [e]
    field_simp
    ring

lemma fz2_c_ge (N : ℕ) (hN : 1 ≤ N) (q : ℝ) (hq : 0 < q) (c : Fin N → ℝ)
    (hc : ∀ l, c l = 2 * (((l : ℕ) : ℝ) + 1) ^ (-q)) : ∀ l, 2 * (N : ℝ) ^ (-q) ≤ c l := by
  intro l
  rw [hc]
  have hi : ((l : ℕ) : ℝ) + 1 ≤ (N : ℝ) := by
    have := l.2
    exact_mod_cast this
  have hpos : (0 : ℝ) < ((l : ℕ) : ℝ) + 1 := by positivity
  have := Real.rpow_le_rpow_of_nonpos hpos hi (by linarith : -q ≤ 0)
  linarith

lemma fz2_svdT0_pos (N B : ℕ) (hN : 1 ≤ N) (hNB : N ≤ B) : 0 < svdT0 N B := by
  unfold svdT0 gammaRat
  have : (0 : ℝ) < N := by exact_mod_cast hN
  have : (0 : ℝ) < B := by exact_mod_cast (by omega : 0 < B)
  exact Real.sqrt_pos.2 (by positivity)

lemma fz2_sgdT0_pos (α : ℝ) (N B : ℕ) (hN : 1 ≤ N) (hNB : N ≤ B) : 0 < sgdT0 α N B := by
  unfold sgdT0 muBarOf
  have : (0 : ℝ) < N := by exact_mod_cast hN
  have : (0 : ℝ) < B := by exact_mod_cast (by omega : 0 < B)
  have := fz2_Hsum_pos α N hN
  exact Real.sqrt_pos.2 (by positivity)

lemma fz2_Q_facts {N : ℕ} (m : RowModel (Fin N)) (Q : ℝ → ℝ) (hQ : IsVolterraSol m Q)
    (T0 : ℝ) (hT0 : 0 < T0) :
    ContinuousOn (fun u => Q (T0 * u)) (Ici 0) ∧ ∀ u ∈ Ici (0:ℝ), 0 < Q (T0 * u) := by
  refine ⟨hQ.1.comp (continuous_const.mul continuous_id).continuousOn ?_, ?_⟩
  · intro u hu
    exact mul_nonneg hT0.le hu
  · intro u hu
    have := thm_app_phase_volterra_iii m Q hQ (T0 * u) (mul_nonneg hT0.le hu)
    exact this.1.trans_le this.2.1

lemma fz2_conv_congr (f g g' : ℝ → ℝ) (hg : ∀ s ∈ Ici (0:ℝ), g s = g' s) {u : ℝ} (hu : 0 ≤ u) :
    oneSidedConv f g u = oneSidedConv f g' u := by
  unfold oneSidedConv
  apply intervalIntegral.integral_congr
  intro s hs
  rw [Set.uIcc_of_le hu] at hs
  simp only
  rw [hg s (Set.mem_Ici.2 hs.1)]

/-- The per-index data of the svd model, in the form consumed by `fz2_gen`. -/
lemma fz2_svd_model (α ς : ℝ) (N B : ℕ) (hα : 0 < α) (hp : 1 < α + ς)
    (hN : 1 ≤ N) (hNB : N ≤ B) (ε : ℝ) (hε : 0 < ε) (mS mG : RowModel (Fin N))
    (hmS : IsMatchedModel (svdArrays α ς N B) mS ε)
    (hmG : IsMatchedModel (sgdArrays α ς N B) mG ε)
    (QS QG : ℝ → ℝ) (hQS : IsVolterraSol mS QS) (hQG : IsVolterraSol mG QG) :
    ∃ w c : Fin N → ℝ, (∀ l, 0 ≤ w l) ∧ ∑ l, w l = 1 ∧ (∀ l, 2 * (N : ℝ) ^ (-(α / 2)) ≤ c l) ∧
      (∀ u ∈ Ici (0:ℝ), mixG w c u = svdKernel α N u) ∧
      ContinuousOn (fun u => QS (svdT0 N B * u)) (Ici 0) ∧
      (∀ u ∈ Ici (0:ℝ), 0 < QS (svdT0 N B * u)) ∧
      ∀ u ∈ Ici (0:ℝ), QS (svdT0 N B * u) = fNq (N : ℕ∞) (α + ς) (α / 2) u +
        Real.sqrt ε * oneSidedConv (fun v => Real.sqrt (QS (svdT0 N B * v))) (mixG w c) u := by
  obtain ⟨w, c, hw, hw1, hc, hmix⟩ := fz2_svd_mix α N hN
  obtain ⟨-, -, hQ3, -, hK, -⟩ := prop_app_phase_prefactors_ii α ς N B hα hp hN hNB ε hε mS mG hmS hmG QS QG hQS hQG
  obtain ⟨hYc, hYp⟩ := fz2_Q_facts mS QS hQS _ (fz2_svdT0_pos N B hN hNB)
  refine ⟨w, c, hw, hw1, fz2_c_ge N hN (α / 2) (by linarith) c hc, fun u _ => (hmix u).symm, hYc, hYp, ?_⟩
  intro u hu
  have hu0 : 0 ≤ u := hu
  rw [hQ3 u hu0, fz2_conv_congr _ (dimKernel mS (svdT0 N B) ε) (mixG w c)
    (fun s hs => by rw [hK s hs, ← hmix s]; rfl) hu0]

lemma fz2_sgd_model (α ς : ℝ) (N B : ℕ) (hα : 0 < α) (hp : 1 < α + ς)
    (hN : 1 ≤ N) (hNB : N ≤ B) (ε : ℝ) (hε : 0 < ε) (mS mG : RowModel (Fin N))
    (hmS : IsMatchedModel (svdArrays α ς N B) mS ε)
    (hmG : IsMatchedModel (sgdArrays α ς N B) mG ε)
    (QS QG : ℝ → ℝ) (hQS : IsVolterraSol mS QS) (hQG : IsVolterraSol mG QG) :
    ∃ w c : Fin N → ℝ, (∀ l, 0 ≤ w l) ∧ ∑ l, w l = 1 ∧ (∀ l, 2 * (N : ℝ) ^ (-α) ≤ c l) ∧
      (∀ u ∈ Ici (0:ℝ), mixG w c u = sgdKernel α N u) ∧
      ContinuousOn (fun u => QG (sgdT0 α N B * u)) (Ici 0) ∧
      (∀ u ∈ Ici (0:ℝ), 0 < QG (sgdT0 α N B * u)) ∧
      ∀ u ∈ Ici (0:ℝ), QG (sgdT0 α N B * u) = fNq (N : ℕ∞) (α + ς) α u +
        Real.sqrt ε * oneSidedConv (fun v => Real.sqrt (QG (sgdT0 α N B * v))) (mixG w c) u := by
  obtain ⟨w, c, hw, hw1, hc, hmix⟩ := fz2_sgd_mix α N hN
  obtain ⟨-, -, -, hQ4, -, hK⟩ := prop_app_phase_prefactors_ii α ς N B hα hp hN hNB ε hε mS mG hmS hmG QS QG hQS hQG
  obtain ⟨hYc, hYp⟩ := fz2_Q_facts mG QG hQG _ (fz2_sgdT0_pos α N B hN hNB)
  refine ⟨w, c, hw, hw1, fz2_c_ge N hN α hα c hc, fun u _ => (hmix u).symm, hYc, hYp, ?_⟩
  intro u hu
  have hu0 : 0 ≤ u := hu
  rw [hQ4 u hu0, fz2_conv_congr _ (dimKernel mG (sgdT0 α N B) ε) (mixG w c)
    (fun s hs => by rw [hK s hs, ← hmix s]; rfl) hu0]

lemma fz2_F0_le (N : ℕ) (p : ℝ) (hp : 0 ≤ p) :
    ∑ i : Fin N, (1 / 2 : ℝ) * (((i : ℕ) : ℝ) + 1) ^ (-p) ≤ N := by
  have : ∀ i : Fin N, (1 / 2 : ℝ) * (((i : ℕ) : ℝ) + 1) ^ (-p) ≤ 1 := by
    intro i
    have h1 : (1 : ℝ) ≤ ((i : ℕ) : ℝ) + 1 := by
      have : (0 : ℝ) ≤ ((i : ℕ) : ℝ) := Nat.cast_nonneg _
      linarith
    have h2 : (((i : ℕ) : ℝ) + 1) ^ (-p) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos h1 (by linarith)
    linarith
  calc _ ≤ ∑ _i : Fin N, (1 : ℝ) := Finset.sum_le_sum fun i _ => this i
    _ = N := by simp

/-- The all-`r` part of the frozen clock-integral estimate at one index: the first hit is attained
and `J_N - √(Tε) N^q ≤ ∫_0^û √Y ≤ J_N + 2√(dJ_N) + d` with `d = √ε N^q (log N + log(1/ε))`. -/
lemma fz2_core {p q T ε : ℝ} (hp : 1 < p) (hq : 0 < q) (hT : 4 ≤ T) (hε : 0 < ε)
    (hεT : ε < 1 / (2 * T)) {N : ℕ} (hN : 1 ≤ N)
    {n' : ℕ} (w c : Fin n' → ℝ) (hw : ∀ l, 0 ≤ w l) (hw1 : ∑ l, w l = 1)
    (hc : ∀ l, 2 * (N : ℝ) ^ (-q) ≤ c l)
    (Y : ℝ → ℝ) (hYc : ContinuousOn Y (Ici 0)) (hYpos : ∀ u ∈ Ici (0 : ℝ), 0 < Y u)
    (hY : ∀ u ∈ Ici (0 : ℝ),
      Y u = fNq (N : ℕ∞) p q u +
        Real.sqrt ε * oneSidedConv (fun v => Real.sqrt (Y v)) (mixG w c) u) :
    ∃ û : ℝ, firstHit Y (T * ε) = ENNReal.ofReal û ∧ 0 < û ∧ 0 < JN N p q ∧
      JN N p q - Real.sqrt (T * ε) * (N : ℝ) ^ q ≤ ∫ u in (0 : ℝ)..û, Real.sqrt (Y u) ∧
      ∫ u in (0 : ℝ)..û, Real.sqrt (Y u) ≤ JN N p q
        + 2 * Real.sqrt (Real.sqrt ε * (N : ℝ) ^ q * (Real.log (N : ℝ) + Real.log (1 / ε)) * JN N p q)
        + Real.sqrt ε * (N : ℝ) ^ q * (Real.log (N : ℝ) + Real.log (1 / ε)) := by
  have hNr : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hTpos : 0 < T := by linarith
  obtain ⟨ha, hF, hb⟩ := fz_ab N hN p q hq
  have hfa := fz_fNq_eq N p q
  set a : Fin N → ℝ := fun i => (1 / 2) * (((i : ℕ) : ℝ) + 1) ^ (-p) with ha_def
  set b : Fin N → ℝ := fun i => 2 * (((i : ℕ) : ℝ) + 1) ^ (-q) with hb_def
  have hF0le : ∑ i, a i ≤ N := fz2_F0_le N p (by linarith)
  have hbmin : 0 < 2 * (N : ℝ) ^ (-q) := by positivity
  have hF0 : 0 < ∑ i, a i := by linarith
  have hTε : ε < (∑ i, a i) / T := by
    rw [lt_div_iff₀ hTpos]
    have h2 : ε * T < 1 / 2 := by
      rw [lt_div_iff₀ (by positivity)] at hεT; linarith
    linarith
  have hY' : ∀ u ∈ Ici (0 : ℝ),
      Y u = mixF a b u + Real.sqrt ε * oneSidedConv (fun v => Real.sqrt (Y v)) (mixG w c) u := by
    intro u hu; rw [hY u hu, hfa]
  obtain ⟨hJpos, -, û, hfh, hû0, -, -, hlow, hup⟩ := lem_app_phase_mixture a b w c _ hbmin
    ha hF0 hb hw hw1 hc hT hε hTε (H := (2 / (2 * (N : ℝ) ^ (-q))) * Real.log ((∑ i, a i) / ε))
    (d := Real.sqrt ε * ((2 / (2 * (N : ℝ) ^ (-q))) * Real.log ((∑ i, a i) / ε))) rfl rfl hYc hYpos hY'
  have hJN : JN N p q = mixJ a b := by
    unfold JN mixJ
    simp only [hfa]
  rw [← hJN] at hJpos hlow hup
  have hNq : (0 : ℝ) < (N : ℝ) ^ q := Real.rpow_pos_of_pos hNr _
  have hinv : 2 / (2 * (N : ℝ) ^ (-q)) = (N : ℝ) ^ q := by
    rw [Real.rpow_neg hNr.le]; field_simp
  rw [hinv] at hup
  have hlow' : JN N p q - Real.sqrt (T * ε) * (N : ℝ) ^ q ≤ ∫ u in (0 : ℝ)..û, Real.sqrt (Y u) := by
    have e : 2 * Real.sqrt (T * ε) / (2 * (N : ℝ) ^ (-q)) = Real.sqrt (T * ε) * (N : ℝ) ^ q := by
      rw [Real.rpow_neg hNr.le]; field_simp
    rw [e] at hlow; exact hlow
  refine ⟨û, hfh, hû0, hJpos, hlow', ?_⟩
  refine hup.trans ?_
  -- compare d with d'
  have hlogle : Real.log ((∑ i, a i) / ε) ≤ Real.log (N : ℝ) + Real.log (1 / ε) := by
    rw [div_eq_mul_one_div, Real.log_mul hF0.ne' (by positivity)]
    have : Real.log (∑ i, a i) ≤ Real.log (N : ℝ) := Real.log_le_log hF0 hF0le
    linarith
  have hd : Real.sqrt ε * ((N : ℝ) ^ q * Real.log ((∑ i, a i) / ε))
      ≤ Real.sqrt ε * (N : ℝ) ^ q * (Real.log (N : ℝ) + Real.log (1 / ε)) := by
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hlogle hNq.le) (Real.sqrt_nonneg _)
  have hs : Real.sqrt (Real.sqrt ε * ((N : ℝ) ^ q * Real.log ((∑ i, a i) / ε)) * JN N p q)
      ≤ Real.sqrt (Real.sqrt ε * (N : ℝ) ^ q * (Real.log (N : ℝ) + Real.log (1 / ε)) * JN N p q) :=
    Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_right hd hJpos.le)
  linarith

lemma fz3_scale {p q ε : ℝ} {N : ℕ} (hN : 1 ≤ N) (hε : 0 < ε) (hq : 0 < q) (hp : 1 < p) :
    0 < phaseX p N ε ∧
      Real.sqrt ε * (N : ℝ) ^ q = Real.sqrt (phaseX p N ε) * (N : ℝ) ^ (q * (1 - rq p q)) ∧
      Real.log (1 / ε) = Real.log (1 / phaseX p N ε) + (p - 1) * Real.log (N : ℝ) := by
  have hNr : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hxdef : phaseX p N ε = ε / (N : ℝ) ^ (-(p - 1)) := rfl
  obtain ⟨-, h2, hxpos⟩ := fz_eps (Nr := (N : ℝ)) (x := phaseX p N ε) (ε := ε) (p := p) (q := q) hNr hε hq hp hxdef
  refine ⟨hxpos, ?_, ?_⟩
  · rw [h2, ← Real.sqrt_eq_rpow, mul_assoc, ← Real.rpow_add hNr]
    congr 2; ring
  · have hNp : 0 < (N : ℝ) ^ (-(p - 1)) := Real.rpow_pos_of_pos hNr _
    have hε' : ε = phaseX p N ε * (N : ℝ) ^ (-(p - 1)) := by rw [hxdef]; field_simp
    have : Real.log ε = Real.log (phaseX p N ε) + -(p - 1) * Real.log (N : ℝ) := by
      conv_lhs => rw [hε']
      rw [Real.log_mul hxpos.ne' hNp.ne', Real.log_rpow hNr]
    rw [one_div, one_div, Real.log_inv, Real.log_inv, this]
    ring

lemma fz3_squeeze {J I δ d : ℕ → ℝ} (hJ : ∀ᶠ n in atTop, 0 < J n)
    (hd : ∀ᶠ n in atTop, 0 ≤ d n)
    (hδJ : Tendsto (fun n => δ n / J n) atTop (𝓝 0))
    (hdJ : Tendsto (fun n => d n / J n) atTop (𝓝 0))
    (hb : ∀ᶠ n in atTop, J n - δ n ≤ I n ∧ I n ≤ J n + 2 * Real.sqrt (d n * J n) + d n) :
    Tendsto (fun n => I n / J n) atTop (𝓝 1) := by
  have h1 : Tendsto (fun n => 1 - δ n / J n) atTop (𝓝 1) := by
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub hδJ
  have hsq : Tendsto (fun n => Real.sqrt (d n / J n)) atTop (𝓝 0) := by
    have := (Real.continuous_sqrt.tendsto 0).comp hdJ
    rw [Real.sqrt_zero] at this
    exact this
  have h2 : Tendsto (fun n => 1 + 2 * Real.sqrt (d n / J n) + d n / J n) atTop (𝓝 1) := by
    simpa using ((tendsto_const_nhds (x := (1 : ℝ))).add (hsq.const_mul 2)).add hdJ
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' h1 h2 ?_ ?_
  · filter_upwards [hJ, hb] with n hJn hbn
    rw [le_div_iff₀ hJn]
    have : (1 - δ n / J n) * J n = J n - δ n := by field_simp
    rw [this]; exact hbn.1
  · filter_upwards [hJ, hb, hd] with n hJn hbn hdn
    rw [div_le_iff₀ hJn]
    have e1 : Real.sqrt (d n / J n) * J n = Real.sqrt (d n * J n) := by
      have : d n / J n = (d n * J n) / J n ^ 2 := by field_simp
      rw [this, Real.sqrt_div (mul_nonneg hdn hJn.le), Real.sqrt_sq hJn.le]
      field_simp
    have : (1 + 2 * Real.sqrt (d n / J n) + d n / J n) * J n
        = J n + 2 * (Real.sqrt (d n / J n) * J n) + d n := by field_simp
    rw [this, e1]; exact hbn.2

lemma fz3_xlog {x : ℕ → ℝ} (hx0 : ∀ n, 0 < x n) (hx : Tendsto x atTop (𝓝 0)) :
    Tendsto (fun n => Real.sqrt (x n)) atTop (𝓝 0) ∧
      Tendsto (fun n => Real.sqrt (x n) * Real.log (1 / x n)) atTop (𝓝 0) := by
  have hs : Tendsto (fun n => Real.sqrt (x n)) atTop (𝓝 0) := by
    have := (Real.continuous_sqrt.tendsto 0).comp hx
    rw [Real.sqrt_zero] at this
    exact this
  refine ⟨hs, ?_⟩
  have hxw : Tendsto x atTop (𝓝[>] (0 : ℝ)) :=
    tendsto_nhdsWithin_iff.2 ⟨hx, Filter.Eventually.of_forall hx0⟩
  have hψ : Tendsto (fun ε : ℝ => Real.log ε * ε ^ (1 / 2 : ℝ)) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    tendsto_log_mul_rpow_nhdsGT_zero (by norm_num)
  have h := (hψ.comp hxw).neg
  rw [neg_zero] at h
  refine h.congr (fun n => ?_)
  simp only [Function.comp, one_div, Real.log_inv, Real.sqrt_eq_rpow]
  ring

lemma fz3_ge1_core {J δ d L x : ℕ → ℝ} {c P K : ℝ} (hc : 0 < c) (hP : 0 ≤ P) (hK : 0 ≤ K)
    (hx0 : ∀ n, 0 < x n)
    (hx : Tendsto x atTop (𝓝 0)) (hL : ∀ᶠ n in atTop, 1 ≤ L n)
    (hJ : ∀ᶠ n in atTop, c * L n ≤ J n) (hδ0 : ∀ n, 0 ≤ δ n)
    (hδ : ∀ᶠ n in atTop, δ n ≤ K * Real.sqrt (x n)) (hd0 : ∀ᶠ n in atTop, 0 ≤ d n)
    (hd : ∀ᶠ n in atTop, d n ≤ Real.sqrt (x n) * (P * L n + Real.log (1 / x n))) :
    Tendsto (fun n => δ n / J n) atTop (𝓝 0) ∧ Tendsto (fun n => d n / J n) atTop (𝓝 0) := by
  obtain ⟨hs, hsl⟩ := fz3_xlog hx0 hx
  have hx1 : ∀ᶠ n in atTop, x n < 1 := (tendsto_order.1 hx).2 1 one_pos
  have hJpos : ∀ᶠ n in atTop, 0 < J n := by
    filter_upwards [hL, hJ] with n hLn hJn
    nlinarith
  refine ⟨?_, ?_⟩
  · have hup : Tendsto (fun n => K / c * Real.sqrt (x n)) atTop (𝓝 0) := by
      simpa using hs.const_mul (K / c)
    refine squeeze_zero' ?_ ?_ hup
    · filter_upwards [hJpos] with n hJn
      exact div_nonneg (hδ0 n) hJn.le
    · filter_upwards [hL, hJ, hδ, hJpos] with n hLn hJn hδn hJp
      rw [div_le_iff₀ hJp]
      have hs0 := Real.sqrt_nonneg (x n)
      have h2 : K / c * Real.sqrt (x n) * J n ≥ K / c * Real.sqrt (x n) * c := by
        apply mul_le_mul_of_nonneg_left (by nlinarith) (by positivity)
      have : K / c * Real.sqrt (x n) * c = K * Real.sqrt (x n) := by field_simp
      linarith
  · have hup : Tendsto (fun n => (1 / c) * (P * Real.sqrt (x n) + Real.sqrt (x n) * Real.log (1 / x n)))
        atTop (𝓝 0) := by
      have := ((hs.const_mul P).add hsl).const_mul (1 / c)
      simpa using this
    refine squeeze_zero' ?_ ?_ hup
    · filter_upwards [hJpos, hd0] with n hJn hdn
      exact div_nonneg hdn hJn.le
    · filter_upwards [hL, hJ, hd, hJpos, hx1] with n hLn hJn hdn hJp hxn
      rw [div_le_iff₀ hJp]
      have hs0 := Real.sqrt_nonneg (x n)
      have hl0 : 0 ≤ Real.log (1 / x n) := Real.log_nonneg (by rw [le_div_iff₀ (hx0 n)]; linarith)
      have h2 : (1 / c) * (P * Real.sqrt (x n) + Real.sqrt (x n) * Real.log (1 / x n)) * J n
          ≥ (1 / c) * (P * Real.sqrt (x n) + Real.sqrt (x n) * Real.log (1 / x n)) * (c * L n) :=
        mul_le_mul_of_nonneg_left hJn (by positivity)
      have e : (1 / c) * (P * Real.sqrt (x n) + Real.sqrt (x n) * Real.log (1 / x n)) * (c * L n)
          = (P * Real.sqrt (x n) + Real.sqrt (x n) * Real.log (1 / x n)) * L n := by field_simp
      have h3 : (P * Real.sqrt (x n) + Real.sqrt (x n) * Real.log (1 / x n)) * L n
          ≥ Real.sqrt (x n) * (P * L n + Real.log (1 / x n)) := by
        have : 0 ≤ Real.sqrt (x n) * Real.log (1 / x n) := mul_nonneg hs0 hl0
        nlinarith
      linarith

lemma fz3_logNk {N : ℝ} (hN : 1 ≤ N) {κ : ℝ} (hκ : 0 < κ) :
    N ^ (-κ) * Real.log N ≤ 1 / κ := by
  have hN0 : 0 < N := by linarith
  have h := Real.log_le_rpow_div hN0.le hκ
  have h2 : N ^ (-κ) * Real.log N ≤ N ^ (-κ) * (N ^ κ / κ) :=
    mul_le_mul_of_nonneg_left h (Real.rpow_nonneg hN0.le _)
  have e : N ^ (-κ) * (N ^ κ / κ) = 1 / κ := by
    rw [← mul_div_assoc, ← Real.rpow_add hN0]; simp
  linarith

lemma fz3_gt1 {p q T : ℝ} (hp : 1 < p) (hq : 0 < q) (hT : 0 ≤ T) (hr : 1 < rq p q)
    {N : ℕ → ℕ} {ε J : ℕ → ℝ} (hN1 : ∀ n, 1 ≤ N n) (hε : ∀ n, 0 < ε n)
    (hx : Tendsto (fun n => phaseX p (N n) (ε n)) atTop (𝓝 0)) {c : ℝ} (hc : 0 < c)
    (hJ : ∀ᶠ n in atTop, c ≤ J n) :
    Tendsto (fun n => Real.sqrt (T * ε n) * (N n : ℝ) ^ q / J n) atTop (𝓝 0) ∧
      Tendsto (fun n => Real.sqrt (ε n) * (N n : ℝ) ^ q *
        (Real.log (N n : ℝ) + Real.log (1 / ε n)) / J n) atTop (𝓝 0) := by
  have hκ : 0 < q * (rq p q - 1) := mul_pos hq (by linarith)
  have hsc := fun n => fz3_scale (hN1 n) (hε n) hq hp
  have hx0 : ∀ n, 0 < phaseX p (N n) (ε n) := fun n => (hsc n).1
  have hNe : ∀ n, (N n : ℝ) ^ (q * (1 - rq p q)) ≤ 1 := fun n =>
    Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hN1 n) (by nlinarith)
  have hNpos : ∀ n, 0 < (N n : ℝ) ^ (q * (1 - rq p q)) := fun n =>
    Real.rpow_pos_of_pos (by exact_mod_cast hN1 n) _
  refine fz3_ge1_core (L := fun _ => 1) (P := p / (q * (rq p q - 1))) (K := Real.sqrt T) hc
    (div_nonneg (by linarith) hκ.le) (Real.sqrt_nonneg _) hx0 hx
    (Filter.Eventually.of_forall fun n => le_rfl)
    (hJ.mono fun n h => by simpa using h) (fun n => by positivity) ?_
    ?_ ?_
  · refine Filter.Eventually.of_forall fun n => ?_
    rw [Real.sqrt_mul hT, mul_assoc, (hsc n).2.1]
    have := Real.sqrt_nonneg T
    have := Real.sqrt_nonneg (phaseX p (N n) (ε n))
    nlinarith [hNe n, hNpos n, mul_nonneg ‹0 ≤ Real.sqrt T› ‹0 ≤ Real.sqrt (phaseX p (N n) (ε n))›]
  · filter_upwards [(tendsto_order.1 hx).2 1 one_pos] with n hxn
    have h1 := hN1 n
    have hN0 : (0 : ℝ) < (N n : ℝ) := by exact_mod_cast h1
    have hlog : 0 ≤ Real.log (N n : ℝ) := Real.log_nonneg (by exact_mod_cast h1)
    have hl0 : 0 ≤ Real.log (1 / phaseX p (N n) (ε n)) :=
      Real.log_nonneg (by rw [le_div_iff₀ (hx0 n)]; linarith)
    have hp0 : 0 ≤ (p - 1) * Real.log (N n : ℝ) := mul_nonneg (by linarith) hlog
    rw [(hsc n).2.1, (hsc n).2.2]
    have := Real.sqrt_nonneg (phaseX p (N n) (ε n))
    have := hNpos n
    positivity
  · filter_upwards [(tendsto_order.1 hx).2 1 one_pos] with n hxn
    rw [(hsc n).2.1, (hsc n).2.2]
    have hN0 : (1 : ℝ) ≤ (N n : ℝ) := by exact_mod_cast hN1 n
    have hl0 : 0 ≤ Real.log (1 / phaseX p (N n) (ε n)) :=
      Real.log_nonneg (by rw [le_div_iff₀ (hx0 n)]; linarith)
    have hs0 := Real.sqrt_nonneg (phaseX p (N n) (ε n))
    have hk := fz3_logNk hN0 hκ
    have e : q * (1 - rq p q) = -(q * (rq p q - 1)) := by ring
    rw [e] at hNe hNpos ⊢
    have h1 : (N n : ℝ) ^ (-(q * (rq p q - 1))) * (p * Real.log (N n : ℝ)) ≤ p / (q * (rq p q - 1)) := by
      have : (N n : ℝ) ^ (-(q * (rq p q - 1))) * (p * Real.log (N n : ℝ))
          = p * ((N n : ℝ) ^ (-(q * (rq p q - 1))) * Real.log (N n : ℝ)) := by ring
      rw [this]
      calc _ ≤ p * (1 / (q * (rq p q - 1))) := mul_le_mul_of_nonneg_left hk (by linarith)
        _ = _ := by ring
    have h2 : (N n : ℝ) ^ (-(q * (rq p q - 1))) * Real.log (1 / phaseX p (N n) (ε n))
        ≤ Real.log (1 / phaseX p (N n) (ε n)) := by
      have := hNe n
      nlinarith
    have e2 : Real.log (N n : ℝ) + (Real.log (1 / phaseX p (N n) (ε n)) + (p - 1) * Real.log (N n : ℝ))
        = p * Real.log (N n : ℝ) + Real.log (1 / phaseX p (N n) (ε n)) := by ring
    rw [e2]
    calc Real.sqrt (phaseX p (N n) (ε n)) * (N n : ℝ) ^ (-(q * (rq p q - 1))) *
          (p * Real.log (N n : ℝ) + Real.log (1 / phaseX p (N n) (ε n)))
        = Real.sqrt (phaseX p (N n) (ε n)) * ((N n : ℝ) ^ (-(q * (rq p q - 1))) * (p * Real.log (N n : ℝ))
            + (N n : ℝ) ^ (-(q * (rq p q - 1))) * Real.log (1 / phaseX p (N n) (ε n))) := by ring
      _ ≤ Real.sqrt (phaseX p (N n) (ε n)) * (p / (q * (rq p q - 1)) * 1 + Real.log (1 / phaseX p (N n) (ε n))) := by
          apply mul_le_mul_of_nonneg_left _ hs0
          linarith

lemma fz3_eq1 {p q T : ℝ} (hp : 1 < p) (hq : 0 < q) (hT : 0 ≤ T) (hr : rq p q = 1)
    {N : ℕ → ℕ} {ε J : ℕ → ℝ} (hN1 : ∀ n, 1 ≤ N n) (hε : ∀ n, 0 < ε n)
    (hNt : Tendsto (fun n => (N n : ℝ)) atTop atTop)
    (hx : Tendsto (fun n => phaseX p (N n) (ε n)) atTop (𝓝 0)) {c : ℝ} (hc : 0 < c)
    (hJ : ∀ᶠ n in atTop, c * Real.log (N n : ℝ) ≤ J n) :
    Tendsto (fun n => Real.sqrt (T * ε n) * (N n : ℝ) ^ q / J n) atTop (𝓝 0) ∧
      Tendsto (fun n => Real.sqrt (ε n) * (N n : ℝ) ^ q *
        (Real.log (N n : ℝ) + Real.log (1 / ε n)) / J n) atTop (𝓝 0) := by
  have hsc := fun n => fz3_scale (hN1 n) (hε n) hq hp
  have hx0 : ∀ n, 0 < phaseX p (N n) (ε n) := fun n => (hsc n).1
  have hL : ∀ᶠ n in atTop, 1 ≤ Real.log (N n : ℝ) := by
    have := (Real.tendsto_log_atTop.comp hNt).eventually_ge_atTop 1
    exact this
  have e0 : q * (1 - rq p q) = 0 := by rw [hr]; ring
  have hsc2 : ∀ n, Real.sqrt (ε n) * (N n : ℝ) ^ q = Real.sqrt (phaseX p (N n) (ε n)) := by
    intro n; rw [(hsc n).2.1, e0, Real.rpow_zero, mul_one]
  refine fz3_ge1_core (L := fun n => Real.log (N n : ℝ)) (P := p) (K := Real.sqrt T) hc
    (by linarith) (Real.sqrt_nonneg _) hx0 hx hL hJ (fun n => by positivity) ?_ ?_ ?_
  · refine Filter.Eventually.of_forall fun n => ?_
    rw [Real.sqrt_mul hT, mul_assoc, (hsc n).2.1, e0, Real.rpow_zero, mul_one]
  · filter_upwards [(tendsto_order.1 hx).2 1 one_pos] with n hxn
    have h1 := hN1 n
    have hlog : 0 ≤ Real.log (N n : ℝ) := Real.log_nonneg (by exact_mod_cast h1)
    have hl0 : 0 ≤ Real.log (1 / phaseX p (N n) (ε n)) :=
      Real.log_nonneg (by rw [le_div_iff₀ (hx0 n)]; linarith)
    have hp0 : 0 ≤ (p - 1) * Real.log (N n : ℝ) := mul_nonneg (by linarith) hlog
    rw [hsc2 n, (hsc n).2.2]
    have := Real.sqrt_nonneg (phaseX p (N n) (ε n))
    positivity
  · refine Filter.Eventually.of_forall fun n => le_of_eq ?_
    rw [hsc2 n, (hsc n).2.2]
    congr 1
    ring

lemma fz3_errratio {J M a1 a2 dt : ℕ → ℝ} {c1 : ℝ} (hc1 : 0 < c1)
    (hM : ∀ᶠ n in atTop, 0 < M n) (hJ : ∀ᶠ n in atTop, c1 * M n ≤ J n)
    (ha1 : ∀ n, 0 ≤ a1 n) (ha2 : ∀ n, 0 ≤ a2 n) (hdt : ∀ n, 0 ≤ dt n)
    (ha1t : Tendsto a1 atTop (𝓝 0)) (ha2t : Tendsto a2 atTop (𝓝 0))
    (hdtt : Tendsto dt atTop (𝓝 0)) :
    Tendsto (fun n => (J n + a1 n * M n + 2 * Real.sqrt ((J n + a2 n * M n) * (dt n * M n))
      + dt n * M n) / J n) atTop (𝓝 1) := by
  have hJpos : ∀ᶠ n in atTop, 0 < J n := by
    filter_upwards [hM, hJ] with n hMn hJn
    have := mul_pos hc1 hMn
    linarith
  have hrho : ∀ a : ℕ → ℝ, (∀ n, 0 ≤ a n) → Tendsto a atTop (𝓝 0) →
      Tendsto (fun n => a n * (M n / J n)) atTop (𝓝 0) := by
    intro a ha hat
    have hup : Tendsto (fun n => a n / c1) atTop (𝓝 0) := by simpa using hat.div_const c1
    refine squeeze_zero' ?_ ?_ hup
    · filter_upwards [hM, hJpos] with n hMn hJn
      exact mul_nonneg (ha n) (div_nonneg hMn.le hJn.le)
    · filter_upwards [hM, hJ, hJpos] with n hMn hJn hJp
      rw [← mul_div_assoc, div_le_div_iff₀ hJp hc1]
      have : a n * M n * c1 ≤ a n * J n := by
        have := mul_le_mul_of_nonneg_left hJn (ha n)
        nlinarith
      nlinarith
  have h1 := hrho a1 ha1 ha1t
  have h2 := hrho a2 ha2 ha2t
  have h3 := hrho dt hdt hdtt
  have h4 : Tendsto (fun n => Real.sqrt ((1 + a2 n * (M n / J n)) * (dt n * (M n / J n)))) atTop (𝓝 0) := by
    have := (Real.continuous_sqrt.tendsto ((1 + 0) * 0)).comp (((tendsto_const_nhds (x := (1 : ℝ))).add h2).mul h3)
    have e : ((1 : ℝ) + 0) * 0 = 0 := by norm_num
    rw [e, Real.sqrt_zero] at this
    exact this
  have h5 : Tendsto (fun n => 1 + a1 n * (M n / J n) + 2 * Real.sqrt ((1 + a2 n * (M n / J n)) * (dt n * (M n / J n)))
      + dt n * (M n / J n)) atTop (𝓝 1) := by
    simpa using (((tendsto_const_nhds (x := (1 : ℝ))).add h1).add (h4.const_mul 2)).add h3
  refine h5.congr' ?_
  filter_upwards [hJpos] with n hJn
  have e1 : (J n + a2 n * M n) * (dt n * M n) = J n ^ 2 * ((1 + a2 n * (M n / J n)) * (dt n * (M n / J n))) := by
    field_simp
  rw [e1, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hJn.le]
  field_simp

lemma fz3_dt_bound {x c2 : ℝ} (hx : 0 < x) (hc2 : 0 ≤ c2) :
    0 ≤ 2 * x ^ (1 / 2 : ℝ) * Real.log (1 + c2 * x ^ (-(1 / 2 : ℝ))) ∧
      2 * x ^ (1 / 2 : ℝ) * Real.log (1 + c2 * x ^ (-(1 / 2 : ℝ)))
        ≤ 4 * x ^ (1 / 2 : ℝ) + 4 * Real.sqrt c2 * x ^ (1 / 4 : ℝ) := by
  have hxh : 0 < x ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hx _
  have hxm : 0 < x ^ (-(1 / 2 : ℝ)) := Real.rpow_pos_of_pos hx _
  have hz : 0 ≤ c2 * x ^ (-(1 / 2 : ℝ)) := mul_nonneg hc2 hxm.le
  refine ⟨mul_nonneg (by positivity) (Real.log_nonneg (by linarith)), ?_⟩
  have h1 := Real.log_le_rpow_div (show (0 : ℝ) ≤ 1 + c2 * x ^ (-(1 / 2 : ℝ)) by linarith)
    (show (0 : ℝ) < 1 / 2 by norm_num)
  have h2 : (1 + c2 * x ^ (-(1 / 2 : ℝ))) ^ (1 / 2 : ℝ) ≤ 1 + Real.sqrt c2 * x ^ (-(1 / 4 : ℝ)) := by
    rw [← Real.sqrt_eq_rpow]
    refine (fz_sqrt_add (by norm_num) hz).trans ?_
    rw [Real.sqrt_one, Real.sqrt_mul hc2, Real.sqrt_eq_rpow (x ^ (-(1 / 2 : ℝ))),
      ← Real.rpow_mul hx.le]
    norm_num
  have h3 : Real.log (1 + c2 * x ^ (-(1 / 2 : ℝ))) ≤ 2 * (1 + Real.sqrt c2 * x ^ (-(1 / 4 : ℝ))) := by
    have : (1 + c2 * x ^ (-(1 / 2 : ℝ))) ^ (1 / 2 : ℝ) / (1 / 2) ≤ 2 * (1 + Real.sqrt c2 * x ^ (-(1 / 4 : ℝ))) := by
      rw [div_le_iff₀ (by norm_num)]; linarith
    linarith
  have h4 : x ^ (1 / 2 : ℝ) * x ^ (-(1 / 4 : ℝ)) = x ^ (1 / 4 : ℝ) := by
    rw [← Real.rpow_add hx]; norm_num
  calc 2 * x ^ (1 / 2 : ℝ) * Real.log (1 + c2 * x ^ (-(1 / 2 : ℝ)))
      ≤ 2 * x ^ (1 / 2 : ℝ) * (2 * (1 + Real.sqrt c2 * x ^ (-(1 / 4 : ℝ)))) :=
        mul_le_mul_of_nonneg_left h3 (by positivity)
    _ = 4 * x ^ (1 / 2 : ℝ) + 4 * Real.sqrt c2 * (x ^ (1 / 2 : ℝ) * x ^ (-(1 / 4 : ℝ))) := by ring
    _ = _ := by rw [h4]

lemma fz3_rpow_tendsto {x : ℕ → ℝ} (hx : Tendsto x atTop (𝓝 0)) {s : ℝ} (hs : 0 < s) :
    Tendsto (fun n => x n ^ s) atTop (𝓝 0) := by
  have h := (Real.continuousAt_rpow_const (0 : ℝ) s (Or.inr hs.le)).tendsto.comp hx
  rw [Real.zero_rpow hs.ne'] at h
  exact h

lemma fz3_frozen_small {C r D τ : ℝ} (hC : 0 ≤ C) (hD : 0 < D) (hτ : 0 < τ) (hr : r < 1)
    {x : ℕ → ℝ} (hx0 : ∀ n, 0 < x n) (hx : Tendsto x atTop (𝓝 0)) :
    (∀ n, 0 ≤ frozenA1 C r D τ (x n)) ∧ (∀ n, 0 ≤ frozenA2 C r D τ (x n)) ∧
      (∀ n, 0 ≤ frozenDt C r D τ (x n)) ∧
      Tendsto (fun n => frozenA1 C r D τ (x n)) atTop (𝓝 0) ∧
      Tendsto (fun n => frozenA2 C r D τ (x n)) atTop (𝓝 0) ∧
      Tendsto (fun n => frozenDt C r D τ (x n)) atTop (𝓝 0) := by
  have hc2 : 0 ≤ frozenC2 C r D τ := mul_nonneg hC (Real.rpow_nonneg (div_nonneg hD.le hτ.le) _)
  have hc1 : 0 ≤ frozenC1 C r D τ := by
    unfold frozenC1
    have : 0 < 1 - r / 2 := by linarith
    positivity
  have h4 := fz3_rpow_tendsto hx (show (0 : ℝ) < 1 / 4 by norm_num)
  have h2 := fz3_rpow_tendsto hx (show (0 : ℝ) < 1 / 2 by norm_num)
  refine ⟨fun n => ?_, fun n => ?_, fun n => ?_, ?_, ?_, ?_⟩
  · unfold frozenA1
    have := hx0 n
    have : 0 ≤ Real.sqrt (2 * frozenC2 C r D τ) := Real.sqrt_nonneg _
    positivity
  · unfold frozenA2
    have := hx0 n
    positivity
  · exact (fz3_dt_bound (hx0 n) hc2).1
  · unfold frozenA1
    simpa using ((h4.const_mul (frozenC1 C r D τ + Real.sqrt (2 * frozenC2 C r D τ))).add
      (h2.const_mul (τ + 1)))
  · unfold frozenA2
    simpa using ((h4.const_mul (Real.sqrt (2 * frozenC2 C r D τ))).add h2)
  · have hup : Tendsto (fun n => 4 * x n ^ (1 / 2 : ℝ) + 4 * Real.sqrt (frozenC2 C r D τ) * x n ^ (1 / 4 : ℝ))
        atTop (𝓝 0) := by
      simpa using (h2.const_mul 4).add (h4.const_mul (4 * Real.sqrt (frozenC2 C r D τ)))
    refine squeeze_zero (fun n => (fz3_dt_bound (hx0 n) hc2).1) (fun n => ?_) hup
    exact (fz3_dt_bound (hx0 n) hc2).2

lemma fz3_lt1 {p q T : ℝ} (hp : 1 < p) (hq : 0 < q) (hT : 0 ≤ T) (hr : rq p q < 1)
    {D τ : ℝ} (hD : 0 < D) (hτ : 0 < τ)
    {N : ℕ → ℕ} {ε J : ℕ → ℝ} (hN1 : ∀ n, 1 ≤ N n) (hε : ∀ n, 0 < ε n)
    (hx : Tendsto (fun n => phaseX p (N n) (ε n)) atTop (𝓝 0)) {c1 : ℝ} (hc1 : 0 < c1)
    (hJ : ∀ᶠ n in atTop, c1 * (N n : ℝ) ^ (q * (1 - rq p q)) ≤ J n) :
    Tendsto (fun n => Real.sqrt (T * ε n) * (N n : ℝ) ^ q / J n) atTop (𝓝 0) ∧
      Tendsto (fun n => frozenErrBound (Cpq p q) q (rq p q) D τ (phaseX p (N n) (ε n)) (N n) (J n)
        / J n) atTop (𝓝 1) := by
  have hsc := fun n => fz3_scale (hN1 n) (hε n) hq hp
  have hx0 : ∀ n, 0 < phaseX p (N n) (ε n) := fun n => (hsc n).1
  have hNpos : ∀ n, 0 < (N n : ℝ) ^ (q * (1 - rq p q)) := fun n =>
    Real.rpow_pos_of_pos (by exact_mod_cast hN1 n) _
  have hC : 0 ≤ Cpq p q := Real.sqrt_nonneg _
  obtain ⟨ha1, ha2, hdt, ha1t, ha2t, hdtt⟩ := fz3_frozen_small hC hD hτ hr hx0 hx
  have hJpos : ∀ᶠ n in atTop, 0 < J n := hJ.mono fun n h => lt_of_lt_of_le (mul_pos hc1 (hNpos n)) h
  refine ⟨?_, ?_⟩
  · obtain ⟨hs, -⟩ := fz3_xlog hx0 hx
    have hup : Tendsto (fun n => Real.sqrt T / c1 * Real.sqrt (phaseX p (N n) (ε n))) atTop (𝓝 0) := by
      simpa using hs.const_mul (Real.sqrt T / c1)
    refine squeeze_zero' ?_ ?_ hup
    · filter_upwards [hJpos] with n hJn
      have := Real.sqrt_nonneg (T * ε n)
      have := (hNpos n).le
      positivity
    · filter_upwards [hJ, hJpos] with n hJn hJp
      rw [div_le_iff₀ hJp, Real.sqrt_mul hT, mul_assoc, (hsc n).2.1]
      have hs0 := Real.sqrt_nonneg (phaseX p (N n) (ε n))
      have hsT := Real.sqrt_nonneg T
      have h2 : Real.sqrt T / c1 * Real.sqrt (phaseX p (N n) (ε n)) * J n
          ≥ Real.sqrt T / c1 * Real.sqrt (phaseX p (N n) (ε n)) * (c1 * (N n : ℝ) ^ (q * (1 - rq p q))) :=
        mul_le_mul_of_nonneg_left hJn (by positivity)
      have e : Real.sqrt T / c1 * Real.sqrt (phaseX p (N n) (ε n)) * (c1 * (N n : ℝ) ^ (q * (1 - rq p q)))
          = Real.sqrt T * (Real.sqrt (phaseX p (N n) (ε n)) * (N n : ℝ) ^ (q * (1 - rq p q))) := by
        field_simp
      linarith
  · have := fz3_errratio (J := J) (M := fun n => (N n : ℝ) ^ (q * (1 - rq p q)))
      (a1 := fun n => frozenA1 (Cpq p q) (rq p q) D τ (phaseX p (N n) (ε n)))
      (a2 := fun n => frozenA2 (Cpq p q) (rq p q) D τ (phaseX p (N n) (ε n)))
      (dt := fun n => frozenDt (Cpq p q) (rq p q) D τ (phaseX p (N n) (ε n))) hc1
      (Filter.Eventually.of_forall hNpos) hJ ha1 ha2 hdt ha1t ha2t hdtt
    refine this.congr (fun n => ?_)
    unfold frozenErrBound
    rfl

lemma fz4_Epq_pos {p q : ℝ} (hp : 1 < p) (hq : 0 < q) : 0 < Epq p q := by
  unfold Epq
  refine lt_max_of_lt_left ?_
  have : 0 < Za p := by
    unfold Za
    have := div_pos one_pos (show (0 : ℝ) < p - 1 by linarith)
    linarith
  exact mul_pos (Real.rpow_pos_of_pos (by norm_num) _) this

lemma fz4_Lsum_nonneg (N : ℕ) (p q u : ℝ) : 0 ≤ Lsum (N : ℕ∞) p q u := by
  rw [fz_Lsum_fin]
  apply Finset.sum_nonneg
  intro i _
  positivity

lemma fz4_Hsum_ge_one (p : ℝ) (N : ℕ) (hN : 1 ≤ N) : 1 ≤ Hsum p N := by
  unfold Hsum
  have h1 : (1:ℕ) ∈ Finset.Icc 1 N := Finset.mem_Icc.2 ⟨le_rfl, hN⟩
  have := Finset.single_le_sum (f := fun i : ℕ => (i : ℝ) ^ (-p)) (fun i _ => by positivity) h1
  simpa using this


lemma fz4_log_le_H (N : ℕ) (hN : 1 ≤ N) : Real.log ((N:ℝ) + 1) ≤ Hsum 1 N := by
  have h := (lem_app_phase_harmonic_i (a := 1) one_pos N hN).1
  have hN0 : (0:ℝ) < N := by exact_mod_cast hN
  have e : ∫ x in (1:ℝ)..((N:ℝ) + 1), x ^ (-(1:ℝ)) = Real.log ((N:ℝ) + 1) := by
    have : (fun x : ℝ => x ^ (-(1:ℝ))) = fun x => x⁻¹ := by
      funext x; exact Real.rpow_neg_one x
    rw [this, integral_inv_of_pos one_pos (by linarith)]
    simp
  rw [e] at h
  exact h


lemma fz4_svd_lt2 (α ς : ℝ) (hα : 0 < α) (hα2 : α < 2) (hς1 : 1 - α < ς) (hς2 : ς < 1) :
    ∃ (D τ : ℝ) (N0 : ℕ), 1 ≤ D ∧ 0 < τ ∧ ∀ N : ℕ, N0 ≤ N → ∀ Hh : ℝ, Hh ≤ τ * (N:ℝ) ^ (α / 2) →
      ∀ g : ℝ → ℝ, ContinuousOn g (Ici 0) → (∀ u ∈ Ici (0:ℝ), 0 ≤ g u) →
      IntegrableOn g (Ioi 0) → ∫ u in Ioi (0:ℝ), g u ≤ 1 →
      (∀ u ∈ Ici (0:ℝ), g u = svdKernel α N u) →
      ∀ u ∈ Icc (0:ℝ) Hh,
        oneSidedConv
          (fun w => Cpq (α + ς) (α / 2) * (1 + w / D) ^ (-rq (α + ς) (α / 2)))
          g u
          ≤ 2 * (Cpq (α + ς) (α / 2) * (1 + u / D) ^ (-rq (α + ς) (α / 2))) := by
  have hp : 1 < α + ς := by linarith
  have hq : 0 < α / 2 := by linarith
  have hr0 := fz_rq_pos hp hq
  have hr : rq (α + ς) (α / 2) < 1 := by
    unfold rq
    rw [div_lt_one (by linarith)]
    linarith
  set r := rq (α + ς) (α / 2) with hr_def
  have hC := fz_Cpq_pos hp hq
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
  refine ⟨1, min ((4:ℝ) ^ (-(α / 2))) (svdSmallC1 α r), max 4 (svdSmallN1 α r), le_rfl, lt_min h4 hc1, ?_⟩
  intro N hN Hh hHh g hgc hgn hgi hgm hgk u hu
  have hN1 : svdSmallN1 α r ≤ N := le_trans (le_max_right _ _) hN
  have hNp : 0 ≤ (N:ℝ) ^ (α / 2) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hu' : u ≤ svdSmallC1 α r * (N:ℝ) ^ (α / 2) :=
    hu.2.trans (hHh.trans (mul_le_mul_of_nonneg_right (min_le_right _ _) hNp))
  have hsm := (lem_app_phase_svd_small α r hα hα2 hr0 hr N hN1).2 (Cpq (α + ς) (α / 2)) hC u
    ⟨hu.1, hu'⟩
  rw [fz2_conv_congr _ g (svdKernel α N) hgk hu.1]
  simp only [div_one]
  have hh : 0 ≤ Cpq (α + ς) (α / 2) * (1 + u) ^ (-r) := by
    have := Real.rpow_nonneg (show (0:ℝ) ≤ 1 + u by linarith [hu.1]) (-r)
    positivity
  linarith


lemma fz4_svd_eq2 (ς : ℝ) (hς1 : 1 - 2 < ς) (hς2 : ς < 1) :
    ∃ (D τ : ℝ) (N0 : ℕ), 1 ≤ D ∧ 0 < τ ∧ ∀ N : ℕ, N0 ≤ N → ∀ Hh : ℝ, Hh ≤ τ * (N:ℝ) ^ ((2:ℝ) / 2) →
      ∀ g : ℝ → ℝ, ContinuousOn g (Ici 0) → (∀ u ∈ Ici (0:ℝ), 0 ≤ g u) →
      IntegrableOn g (Ioi 0) → ∫ u in Ioi (0:ℝ), g u ≤ 1 →
      (∀ u ∈ Ici (0:ℝ), g u = svdKernel (2:ℝ) N u) →
      ∀ u ∈ Icc (0:ℝ) Hh,
        oneSidedConv
          (fun w => Cpq (2 + ς) ((2:ℝ) / 2) * (1 + w / D) ^ (-rq (2 + ς) ((2:ℝ) / 2)))
          g u
          ≤ 2 * (Cpq (2 + ς) ((2:ℝ) / 2) * (1 + u / D) ^ (-rq (2 + ς) ((2:ℝ) / 2))) := by
  have hp : 1 < 2 + ς := by linarith
  have hq : 0 < (2:ℝ) / 2 := by norm_num
  have hr0 := fz_rq_pos hp hq
  have hr : rq (2 + ς) (2 / 2) < 1 := by
    unfold rq
    rw [div_lt_one (by norm_num)]
    linarith
  set r := rq (2 + ς) (2 / 2) with hr_def
  have hC := fz_Cpq_pos hp hq
  have hτ4 : (1/4 : ℝ) ≤ (4:ℝ) ^ (-((2:ℝ) / 2)) := by
    norm_num [Real.rpow_neg]
  refine ⟨1, 1/4, max 4 ⌈Real.exp (logAr r)⌉₊, le_rfl, by norm_num, ?_⟩
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
  have hH := fz4_log_le_H N hN1
  have hlog := (lem_app_phase_log_ii N hN1 r hr0 hr (Cpq (2 + ς) (2 / 2)) hC) u hu0
  have hHpos : 0 < Hsum 1 N := by have := fz4_Hsum_ge_one 1 N hN1; linarith
  have hfrac : (Real.log (1 + u) + logAr r) / Hsum 1 N ≤ 2 := by
    rw [div_le_iff₀ hHpos]; linarith
  have hh : 0 < Cpq (2 + ς) (2 / 2) * (1 + u) ^ (-r) := by
    have := Real.rpow_pos_of_pos (show (0:ℝ) < 1 + u by linarith) (-r)
    positivity
  rw [fz2_conv_congr _ g (svdKernel 2 N) hgk hu0]
  simp only [div_one, ← hr_def]
  rw [div_le_iff₀ hh] at hlog
  calc _ ≤ _ := hlog
    _ ≤ 2 * (Cpq (2 + ς) (2 / 2) * (1 + u) ^ (-r)) := by
      have := mul_le_mul_of_nonneg_right hfrac hh.le
      linarith


lemma fz4_svd_gt2 (α ς : ℝ) (hα : 2 < α) (hς1 : 1 - α < ς) (hς2 : ς < 1) :
    ∃ (D τ : ℝ) (N0 : ℕ), 1 ≤ D ∧ 0 < τ ∧ ∀ N : ℕ, N0 ≤ N → ∀ Hh : ℝ, Hh ≤ τ * (N:ℝ) ^ (α / 2) →
      ∀ g : ℝ → ℝ, ContinuousOn g (Ici 0) → (∀ u ∈ Ici (0:ℝ), 0 ≤ g u) →
      IntegrableOn g (Ioi 0) → ∫ u in Ioi (0:ℝ), g u ≤ 1 →
      (∀ u ∈ Ici (0:ℝ), g u = svdKernel α N u) →
      ∀ u ∈ Icc (0:ℝ) Hh,
        oneSidedConv
          (fun w => Cpq (α + ς) (α / 2) * (1 + w / D) ^ (-rq (α + ς) (α / 2)))
          g u
          ≤ 2 * (Cpq (α + ς) (α / 2) * (1 + u / D) ^ (-rq (α + ς) (α / 2))) := by
  have hα0 : 0 < α := by linarith
  have hp : 1 < α + ς := by linarith
  have hq : 0 < α / 2 := by linarith
  have hr0 := fz_rq_pos hp hq
  have hr : rq (α + ς) (α / 2) < 1 := by
    unfold rq
    rw [div_lt_one (by linarith)]
    linarith
  have hυ : 1 < 2 - 2 / α := by
    have : 2 / α < 1 := by rw [div_lt_one hα0]; exact hα
    linarith
  have hK : 0 < 2 * Epq α (α / 2) := by have := fz4_Epq_pos (p := α) (q := α / 2) (by linarith) hq; positivity
  have hD1 : 1 ≤ dilScale (2 * Epq α (α / 2)) (rq (α + ς) (α / 2)) (2 - 2 / α) := le_max_left _ _
  have h4 : (0:ℝ) < (4:ℝ) ^ (-(α / 2)) := Real.rpow_pos_of_pos (by norm_num) _
  refine ⟨dilScale (2 * Epq α (α / 2)) (rq (α + ς) (α / 2)) (2 - 2 / α), (4:ℝ) ^ (-(α / 2)), 4, hD1, h4, ?_⟩
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
    have hH := fz4_Hsum_ge_one (α / 2) N hN1
    have hL := fz4_Lsum_nonneg N α (α / 2) v
    have hpow : 0 ≤ Epq α (α / 2) * (1 + v) ^ (-(2 - 2 / α)) := by
      have := fz4_Epq_pos (p := α) (q := α / 2) (by linarith) hq
      have := Real.rpow_nonneg (show (0:ℝ) ≤ 1 + v by linarith) (-(2 - 2 / α))
      positivity
    have : 2 / Hsum (α / 2) N ≤ 2 := by
      rw [div_le_iff₀ (by linarith)]; nlinarith
    calc 2 / Hsum (α / 2) N * Lsum (N : ℕ∞) α (α / 2) v ≤ 2 * (Epq α (α / 2) * (1 + v) ^ (-(2 - 2 / α))) :=
          mul_le_mul this h1 hL (by norm_num)
      _ = _ := by ring
  have hdil := (lem_app_phase_dilation g hgc hgn hgi hgm (2 * Epq α (α / 2)) (2 - 2 / α) (max Hh 1)
    (rq (α + ς) (α / 2)) (Cpq (α + ς) (α / 2)) hK hυ (by positivity) hr0
    (by have : 1 < 2 - 2 / α := hυ; linarith) (fz_Cpq_pos hp hq) hbound)
  have hu' : u ∈ Icc (0:ℝ) (max Hh 1) := ⟨hu.1, hu.2.trans (le_max_left _ _)⟩
  have hh : 0 < Cpq (α + ς) (α / 2) * (1 + u / dilScale (2 * Epq α (α / 2)) (rq (α + ς) (α / 2)) (2 - 2 / α)) ^ (-rq (α + ς) (α / 2)) := by
    have hD : 0 < dilScale (2 * Epq α (α / 2)) (rq (α + ς) (α / 2)) (2 - 2 / α) := by linarith
    have := Real.rpow_pos_of_pos (show (0:ℝ) < 1 + u / dilScale (2 * Epq α (α / 2)) (rq (α + ς) (α / 2)) (2 - 2 / α) by
      have : 0 ≤ u / dilScale (2 * Epq α (α / 2)) (rq (α + ς) (α / 2)) (2 - 2 / α) := div_nonneg hu.1 hD.le
      linarith) (-rq (α + ς) (α / 2))
    have := fz_Cpq_pos hp hq
    positivity
  have h1 := (div_le_iff₀ hh).1 ((hdil.1 u hu').trans hdil.2)
  exact h1

lemma fz4_svd_phase1 (α ς : ℝ) (hα : 0 < α) (hς1 : 1 - α < ς) (hς2 : ς < 1) :
    ∃ (D τ : ℝ) (N0 : ℕ), 1 ≤ D ∧ 0 < τ ∧ ∀ N : ℕ, N0 ≤ N → ∀ Hh : ℝ, Hh ≤ τ * (N:ℝ) ^ (α / 2) →
      ∀ g : ℝ → ℝ, ContinuousOn g (Ici 0) → (∀ u ∈ Ici (0:ℝ), 0 ≤ g u) →
      IntegrableOn g (Ioi 0) → ∫ u in Ioi (0:ℝ), g u ≤ 1 →
      (∀ u ∈ Ici (0:ℝ), g u = svdKernel α N u) →
      ∀ u ∈ Icc (0:ℝ) Hh,
        oneSidedConv
          (fun w => Cpq (α + ς) (α / 2) * (1 + w / D) ^ (-rq (α + ς) (α / 2)))
          g u
          ≤ 2 * (Cpq (α + ς) (α / 2) * (1 + u / D) ^ (-rq (α + ς) (α / 2))) := by
  rcases lt_trichotomy α 2 with h | h | h
  · exact fz4_svd_lt2 α ς hα h hς1 hς2
  · subst h
    exact fz4_svd_eq2 ς hς1 hς2
  · exact fz4_svd_gt2 α ς h hς1 hς2

lemma fz4_svd_one (α ς : ℝ) (hα : 0 < α) (hς1 : 1 - α < ς) (hς2 : ς < 1) :
    ∃ (D τ : ℝ) (N0 : ℕ), 1 ≤ D ∧ 0 < τ ∧ ∀ N : ℕ, N0 ≤ N → 1 ≤ N →
      ∀ {n' : ℕ} (w c : Fin n' → ℝ), (∀ l, 0 ≤ w l) → ∑ l, w l = 1 →
      (∀ l, 2 * (N : ℝ) ^ (-(α / 2)) ≤ c l) →
      (∀ u ∈ Ici (0:ℝ), mixG w c u = svdKernel α N u) →
      PhaseOneBound (mixG w c) (Cpq (α + ς) (α / 2)) (α / 2) (rq (α + ς) (α / 2)) D τ N := by
  obtain ⟨D, τ, N0, hD, hτ, h⟩ := fz4_svd_phase1 α ς hα hς1 hς2
  refine ⟨D, τ, N0, hD, hτ, fun N hN hN1 n' w c hw hw1 hc hmix => ?_⟩
  have hNr : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN1
  have hbmin : 0 < 2 * (N : ℝ) ^ (-(α / 2)) := by positivity
  have hgc : ContinuousOn (mixG w c) (Ici 0) := by
    have : Continuous (mixG w c) := by unfold mixG; fun_prop
    exact this.continuousOn
  obtain ⟨hgi, hgm⟩ := fz_g_int w c _ hbmin hw hw1 hc
  intro u hu
  exact h N hN _ le_rfl (mixG w c) hgc (fun u _ => fz_g_nonneg w c _ hw hc hbmin u) hgi hgm.le hmix u hu

lemma fz4_sgd_one (α ς : ℝ) (hα : 0 < α) (hp : 1 < α + ς) (hr : rq (α + ς) α < 1) :
    ∃ (D τ : ℝ) (N0 : ℕ), 1 ≤ D ∧ 0 < τ ∧ ∀ N : ℕ, N0 ≤ N → 1 ≤ N →
      ∀ {n' : ℕ} (w c : Fin n' → ℝ),
      (∀ u ∈ Ici (0:ℝ), mixG w c u = sgdKernel α N u) →
      PhaseOneBound (mixG w c) (Cpq (α + ς) α) α (rq (α + ς) α) D τ N := by
  obtain ⟨D, τ, hD, hτ, N0, h⟩ := lem_app_phase_G_small hα (fz_rq_pos hp hα) hr
  refine ⟨D, τ, N0, hD, hτ, fun N hN hN1 n' w c hmix => ?_⟩
  intro u hu
  rw [fz2_conv_congr _ (mixG w c) (sgdKernel α N) hmix hu.1]
  exact h N hN _ (fz_Cpq_pos hp hα) u hu

lemma fz5_squeeze2 {J I δ U : ℕ → ℝ} (hJ : ∀ᶠ n in atTop, 0 < J n)
    (hδJ : Tendsto (fun n => δ n / J n) atTop (𝓝 0))
    (hU : Tendsto (fun n => U n / J n) atTop (𝓝 1))
    (hb : ∀ᶠ n in atTop, J n - δ n ≤ I n ∧ I n ≤ U n) :
    Tendsto (fun n => I n / J n) atTop (𝓝 1) := by
  have h1 : Tendsto (fun n => 1 - δ n / J n) atTop (𝓝 1) := by
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub hδJ
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' h1 hU ?_ ?_
  · filter_upwards [hJ, hb] with n hJn hbn
    rw [le_div_iff₀ hJn]
    have : (1 - δ n / J n) * J n = J n - δ n := by field_simp
    rw [this]; exact hbn.1
  · filter_upwards [hJ, hb] with n hJn hbn
    exact div_le_div_of_nonneg_right hbn.2 hJn.le

lemma fz5_eps_le {p : ℝ} (hp : 1 < p) {N : ℕ} (hN : 1 ≤ N) {ε : ℝ} (hε : 0 < ε) :
    ε ≤ phaseX p N ε := by
  have hNr : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hpos : 0 < (N : ℝ) ^ (-(p - 1)) := Real.rpow_pos_of_pos (by linarith) _
  have hle : (N : ℝ) ^ (-(p - 1)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hNr (by linarith)
  unfold phaseX phaseEpsN
  rw [le_div_iff₀ hpos]
  nlinarith

lemma fz5_Jgt1 {p q : ℝ} (hp : 1 < p) (hq : 0 < q) (hr : 1 < rq p q)
    {N : ℕ → ℕ} (hNt : Tendsto (fun n => (N n : ℝ)) atTop atTop) :
    Tendsto (fun n => Jpq p q - JN (N n) p q) atTop (𝓝 0) ∧ ∀ n, 4 ≤ N n → JN (N n) p q ≤ Jpq p q := by
  have hκ : 0 < q * (rq p q - 1) := mul_pos hq (by linarith)
  refine ⟨?_, fun n hn => by linarith [(lem_app_phase_clock_integral_rate hp hq hr (N n) hn).1]⟩
  have hup : Tendsto (fun n => (1 / Real.sqrt (2 * (p - 1)) + Cpq p q / (rq p q - 1)) *
      (N n : ℝ) ^ (-(q * (rq p q - 1)))) atTop (𝓝 0) := by
    have := ((tendsto_rpow_neg_atTop hκ).comp hNt).const_mul
      (1 / Real.sqrt (2 * (p - 1)) + Cpq p q / (rq p q - 1))
    simpa using this
  refine squeeze_zero' ?_ ?_ hup
  · filter_upwards [hNt.eventually_ge_atTop 4] with n hn
    exact (lem_app_phase_clock_integral_rate hp hq hr (N n) (by exact_mod_cast hn)).1
  · filter_upwards [hNt.eventually_ge_atTop 4] with n hn
    exact (lem_app_phase_clock_integral_rate hp hq hr (N n) (by exact_mod_cast hn)).2

lemma fz5_Jeq1 {p q : ℝ} (hp : 1 < p) (hq : 0 < q) (hr : rq p q = 1)
    {N : ℕ → ℕ} (hN1 : ∀ n, 1 ≤ N n) (hNt : Tendsto (fun n => (N n : ℝ)) atTop atTop) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ n in atTop, c * Real.log (N n : ℝ) ≤ JN (N n) p q := by
  have hpq : p = 2 * q + 1 := by
    unfold rq at hr
    rw [div_eq_iff (mul_pos two_pos hq).ne'] at hr
    linarith
  have haq : 0 < aQ q := by unfold aQ; positivity
  set K : ℝ := 2 * Cpq p q + q * Mpq p q * (2 : ℝ) ^ (-(p / q)) / aQ q + 1 / Real.sqrt (2 * (p - 1)) with hK
  refine ⟨aQ q * q / 2, by positivity, ?_⟩
  have hlog : Tendsto (fun n => Real.log (N n : ℝ)) atTop atTop := Real.tendsto_log_atTop.comp hNt
  filter_upwards [hlog.eventually_ge_atTop (K / (aQ q * q / 2))] with n hn
  have h := (abs_le.1 (lem_app_phase_forcing_integrals_i hq hpq (N n) (hN1 n))).1
  have : K ≤ aQ q * q / 2 * Real.log (N n : ℝ) := by
    rw [div_le_iff₀ (by positivity)] at hn
    linarith
  linarith

lemma fz5_Jlt1 {p q : ℝ} (hp : 1 < p) (hq : 0 < q) (hr : rq p q < 1)
    {N : ℕ → ℕ} (hNt : Tendsto (fun n => (N n : ℝ)) atTop atTop) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ n in atTop, c * (N n : ℝ) ^ (q * (1 - rq p q)) ≤ JN (N n) p q := by
  have he : 0 < q * (1 - rq p q) := mul_pos hq (by linarith)
  have hr0 : rq p q < 1 := hr
  refine ⟨Real.sqrt (Aconst p) / (2 * (1 - rq p q)) * (4 : ℝ) ^ (-(q * (1 - rq p q))), ?_, ?_⟩
  · have : 0 < Aconst p := by unfold Aconst; positivity
    have : 0 < 1 - rq p q := by linarith
    positivity
  · have h2 : Tendsto (fun n => ((N n : ℝ) / 4) ^ (q * (1 - rq p q))) atTop atTop :=
      (tendsto_rpow_atTop he).comp (hNt.atTop_div_const (by norm_num))
    filter_upwards [h2.eventually_ge_atTop 2] with n hn
    have := prop_app_phase_forcing_r_ii hp hq hr (N n) hn
    linarith

lemma fz5_gen {p q T : ℝ} (hp : 1 < p) (hq : 0 < q) (hT : 4 ≤ T)
    {N : ℕ → ℕ} {ε : ℕ → ℝ} {Y : ℕ → ℝ → ℝ} {ker : ℕ → ℝ → ℝ}
    (hNt : Tendsto (fun n => (N n : ℝ)) atTop atTop) (hN1 : ∀ n, 1 ≤ N n) (hε : ∀ n, 0 < ε n)
    (hx : Tendsto (fun n => phaseX p (N n) (ε n)) atTop (𝓝 0))
    (hdata : ∀ n, ∃ w c : Fin (N n) → ℝ, (∀ l, 0 ≤ w l) ∧ ∑ l, w l = 1 ∧
      (∀ l, 2 * (N n : ℝ) ^ (-q) ≤ c l) ∧ (∀ u ∈ Ici (0:ℝ), mixG w c u = ker n u) ∧
      ContinuousOn (Y n) (Ici 0) ∧ (∀ u ∈ Ici (0:ℝ), 0 < Y n u) ∧
      ∀ u ∈ Ici (0:ℝ), Y n u = fNq (N n : ℕ∞) p q u +
        Real.sqrt (ε n) * oneSidedConv (fun v => Real.sqrt (Y n v)) (mixG w c) u)
    (hph : rq p q < 1 → ∃ (D τ : ℝ) (N0 : ℕ), 1 ≤ D ∧ 0 < τ ∧ ∀ n, N0 ≤ N n →
      ∀ (w c : Fin (N n) → ℝ), (∀ l, 0 ≤ w l) → ∑ l, w l = 1 →
      (∀ l, 2 * (N n : ℝ) ^ (-q) ≤ c l) → (∀ u ∈ Ici (0:ℝ), mixG w c u = ker n u) →
      PhaseOneBound (mixG w c) (Cpq p q) q (rq p q) D τ (N n)) :
    (∀ᶠ n in atTop, firstHit (Y n) (T * ε n) ≠ ⊤) ∧
      Tendsto (fun n => dimClockI (Y n) T (ε n) / JN (N n) p q) atTop (𝓝 1) := by
  have hTpos : 0 < T := by linarith
  have hx0 : ∀ n, 0 < phaseX p (N n) (ε n) := fun n => (fz3_scale (hN1 n) (hε n) hq hp).1
  have hεt : Tendsto ε atTop (𝓝 0) :=
    squeeze_zero (fun n => (hε n).le) (fun n => fz5_eps_le hp (hN1 n) (hε n)) hx
  have hsmall : ∀ᶠ n in atTop, ε n < 1 / (2 * T) := (tendsto_order.1 hεt).2 _ (by positivity)
  have hε1 : ∀ᶠ n in atTop, ε n < 1 := (tendsto_order.1 hεt).2 1 one_pos
  have hcore : ∀ᶠ n in atTop, ∃ û : ℝ, firstHit (Y n) (T * ε n) = ENNReal.ofReal û ∧ 0 < û ∧
      0 < JN (N n) p q ∧
      JN (N n) p q - Real.sqrt (T * ε n) * (N n : ℝ) ^ q ≤ ∫ u in (0 : ℝ)..û, Real.sqrt (Y n u) ∧
      ∫ u in (0 : ℝ)..û, Real.sqrt (Y n u) ≤ JN (N n) p q
        + 2 * Real.sqrt (Real.sqrt (ε n) * (N n : ℝ) ^ q * (Real.log (N n : ℝ) + Real.log (1 / ε n))
            * JN (N n) p q)
        + Real.sqrt (ε n) * (N n : ℝ) ^ q * (Real.log (N n : ℝ) + Real.log (1 / ε n)) := by
    filter_upwards [hsmall] with n hn
    obtain ⟨w, c, hw, hw1, hc, -, hYc, hYp, hY⟩ := hdata n
    exact fz2_core hp hq hT (hε n) hn (hN1 n) w c hw hw1 hc (Y n) hYc hYp hY
  have hP : ∀ᶠ n in atTop, firstHit (Y n) (T * ε n) ≠ ⊤ ∧ 0 < JN (N n) p q ∧
      JN (N n) p q - Real.sqrt (T * ε n) * (N n : ℝ) ^ q ≤ dimClockI (Y n) T (ε n) ∧
      dimClockI (Y n) T (ε n) ≤ JN (N n) p q
        + 2 * Real.sqrt (Real.sqrt (ε n) * (N n : ℝ) ^ q * (Real.log (N n : ℝ) + Real.log (1 / ε n))
            * JN (N n) p q)
        + Real.sqrt (ε n) * (N n : ℝ) ^ q * (Real.log (N n : ℝ) + Real.log (1 / ε n)) := by
    filter_upwards [hcore] with n ⟨û, hfh, hû, hJ, hlo, hup⟩
    have hI : dimClockI (Y n) T (ε n) = ∫ u in (0 : ℝ)..û, Real.sqrt (Y n u) := by
      unfold dimClockI
      rw [hfh, ENNReal.toReal_ofReal hû.le]
    rw [hI]
    exact ⟨by rw [hfh]; exact ENNReal.ofReal_ne_top, hJ, hlo, hup⟩
  refine ⟨hP.mono fun n h => h.1, ?_⟩
  have hJpos : ∀ᶠ n in atTop, 0 < JN (N n) p q := hP.mono fun n h => h.2.1
  rcases lt_trichotomy (rq p q) 1 with hr | hr | hr
  · -- r < 1 : the frozen error bound
    obtain ⟨c1, hc1, hJc⟩ := fz5_Jlt1 hp hq hr hNt
    obtain ⟨D, τ, N0, hD, hτ, hphD⟩ := hph hr
    obtain ⟨hδ, hU⟩ := fz3_lt1 (J := fun n => JN (N n) p q) (D := D) (τ := τ) hp hq hTpos.le hr (by linarith) hτ hN1 hε hx hc1 hJc
    refine fz5_squeeze2 hJpos hδ hU ?_
    have hDτ : ∀ᶠ n in atTop, D ≤ τ * (N n : ℝ) ^ q := by
      have h2 : Tendsto (fun n => (N n : ℝ) ^ q) atTop atTop := (tendsto_rpow_atTop hq).comp hNt
      filter_upwards [h2.eventually_ge_atTop (D / τ)] with n hn
      rw [div_le_iff₀ hτ] at hn
      linarith
    filter_upwards [hP, hsmall, hDτ, hNt.eventually_ge_atTop (max 4 (N0 : ℝ)),
      hNt.eventually_ge_atTop 4] with n hPn hn hDn hNn _
    refine ⟨hPn.2.2.1, ?_⟩
    obtain ⟨w, c, hw, hw1, hc, hker, hYc, hYp, hY⟩ := hdata n
    have hN4 : 4 ≤ N n := by
      have : (4 : ℝ) ≤ (N n : ℝ) := (le_max_left _ _).trans hNn
      exact_mod_cast this
    have hN0 : N0 ≤ N n := by
      have : (N0 : ℝ) ≤ (N n : ℝ) := (le_max_right _ _).trans hNn
      exact_mod_cast this
    exact lem_app_phase_frozenerr hp hq hr hT (hε n) hn hN4 hD hτ hDn w c hw hw1 hc
      (hphD n hN0 w c hw hw1 hc hker) (Y n) hYc hYp hY
  · -- r = 1
    obtain ⟨c, hc, hJc⟩ := fz5_Jeq1 hp hq hr hN1 hNt
    obtain ⟨hδ, hd⟩ := fz3_eq1 (J := fun n => JN (N n) p q) hp hq hTpos.le hr hN1 hε hNt hx hc hJc
    refine fz3_squeeze (δ := fun n => Real.sqrt (T * ε n) * (N n : ℝ) ^ q) hJpos ?_ hδ hd
      (hP.mono fun n h => ⟨h.2.2.1, h.2.2.2⟩)
    filter_upwards [hε1] with n hn
    have h1 := hN1 n
    have hlog : 0 ≤ Real.log (N n : ℝ) := Real.log_nonneg (by exact_mod_cast h1)
    have hl0 : 0 ≤ Real.log (1 / ε n) := Real.log_nonneg (by rw [le_div_iff₀ (hε n)]; linarith)
    have := Real.sqrt_nonneg (ε n)
    have := Real.rpow_nonneg (Nat.cast_nonneg (N n) : (0 : ℝ) ≤ (N n : ℝ)) q
    positivity
  · -- r > 1
    obtain ⟨hJt, hJle⟩ := fz5_Jgt1 hp hq hr hNt
    have hJlim : Tendsto (fun n => JN (N n) p q) atTop (𝓝 (Jpq p q)) := by
      have := (tendsto_const_nhds (x := Jpq p q)).sub hJt
      simpa using this
    have hJinf : 0 < Jpq p q := by
      obtain ⟨n0, ⟨hJ0, hn4⟩⟩ := ((hJpos.and (hNt.eventually_ge_atTop 4))).exists
      have := hJle n0 (by exact_mod_cast hn4)
      linarith
    have hJc : ∀ᶠ n in atTop, Jpq p q / 2 ≤ JN (N n) p q :=
      (tendsto_order.1 hJlim).1 (Jpq p q / 2) (by linarith) |>.mono fun n h => h.le
    obtain ⟨hδ, hd⟩ := fz3_gt1 (J := fun n => JN (N n) p q) hp hq hTpos.le hr hN1 hε hx
      (show 0 < Jpq p q / 2 by linarith) hJc
    refine fz3_squeeze (δ := fun n => Real.sqrt (T * ε n) * (N n : ℝ) ^ q) hJpos ?_ hδ hd
      (hP.mono fun n h => ⟨h.2.2.1, h.2.2.2⟩)
    filter_upwards [hε1] with n hn
    have h1 := hN1 n
    have hlog : 0 ≤ Real.log (N n : ℝ) := Real.log_nonneg (by exact_mod_cast h1)
    have hl0 : 0 ≤ Real.log (1 / ε n) := Real.log_nonneg (by rw [le_div_iff₀ (hε n)]; linarith)
    have := Real.sqrt_nonneg (ε n)
    have := Real.rpow_nonneg (Nat.cast_nonneg (N n) : (0 : ℝ) ≤ (N n : ℝ)) q
    positivity

lemma fz6_Nt {α ς : ℝ} (D : FrozenSeq α ς) :
    Tendsto (fun n => (D.N n : ℝ)) atTop atTop :=
  tendsto_natCast_atTop_atTop.comp D.tendsto_N

lemma fz6_svd {α ς T : ℝ} (hα : 0 < α) (hp : 1 < α + ς) (hT : 4 ≤ T) (D : FrozenSeq α ς) :
    (∀ᶠ n in atTop, dimHit (D.QS n) (svdT0 (D.N n) (D.B n)) T (D.ε n) ≠ ⊤) ∧
      Tendsto (fun n => phaseClockI (D.QS n) (svdT0 (D.N n) (D.B n)) T (D.ε n) /
        JN (D.N n) (α + ς) (α / 2)) atTop (𝓝 1) := by
  refine fz5_gen (p := α + ς) (q := α / 2) (T := T) (N := D.N) (ε := D.ε)
    (Y := fun n u => D.QS n (svdT0 (D.N n) (D.B n) * u)) (ker := fun n => svdKernel α (D.N n))
    hp (by linarith) hT (fz6_Nt D) (fun n => (D.le_B n).1) D.ε_pos D.x_tendsto ?_ ?_
  · intro n
    exact fz2_svd_model α ς (D.N n) (D.B n) hα hp (D.le_B n).1 (D.le_B n).2 (D.ε n) (D.ε_pos n)
      (D.mS n) (D.mG n) (D.matchS n) (D.matchG n) (D.QS n) (D.QG n) (D.volS n) (D.volG n)
  · intro hr
    have hς2 : ς < 1 := by
      unfold rq at hr
      rw [div_lt_one (by linarith)] at hr
      linarith
    obtain ⟨Dd, τ, N0, hD, hτ, h⟩ := fz4_svd_one α ς hα (by linarith) hς2
    exact ⟨Dd, τ, N0, hD, hτ, fun n hn w c hw hw1 hc hker =>
      h (D.N n) hn (D.le_B n).1 w c hw hw1 hc hker⟩

lemma fz6_sgd {α ς T : ℝ} (hα : 0 < α) (hp : 1 < α + ς) (hT : 4 ≤ T) (D : FrozenSeq α ς) :
    (∀ᶠ n in atTop, dimHit (D.QG n) (sgdT0 α (D.N n) (D.B n)) T (D.ε n) ≠ ⊤) ∧
      Tendsto (fun n => phaseClockI (D.QG n) (sgdT0 α (D.N n) (D.B n)) T (D.ε n) /
        JN (D.N n) (α + ς) α) atTop (𝓝 1) := by
  refine fz5_gen (p := α + ς) (q := α) (T := T) (N := D.N) (ε := D.ε)
    (Y := fun n u => D.QG n (sgdT0 α (D.N n) (D.B n) * u)) (ker := fun n => sgdKernel α (D.N n))
    hp hα hT (fz6_Nt D) (fun n => (D.le_B n).1) D.ε_pos D.x_tendsto ?_ ?_
  · intro n
    exact fz2_sgd_model α ς (D.N n) (D.B n) hα hp (D.le_B n).1 (D.le_B n).2 (D.ε n) (D.ε_pos n)
      (D.mS n) (D.mG n) (D.matchS n) (D.matchG n) (D.QS n) (D.QG n) (D.volS n) (D.volG n)
  · intro hr
    obtain ⟨Dd, τ, N0, hD, hτ, h⟩ := fz4_sgd_one α ς hα hp hr
    exact ⟨Dd, τ, N0, hD, hτ, fun n hn w c _ _ _ hker =>
      h (D.N n) hn (D.le_B n).1 w c hker⟩

/-! ### Helpers for `thm_app_phase_frozen_iii`, `_iv` (P-H.15.P3) -/

lemma fz7_gamma_pos {N B : ℕ} (hN : 1 ≤ N) (hNB : N ≤ B) : 0 < gammaRat N B := by
  unfold gammaRat
  exact div_pos (Nat.cast_pos.2 (by omega)) (Nat.cast_pos.2 (by omega))

lemma fz7_svd_prod_pos (α ς : ℝ) (N B : ℕ) (hα : 0 < α) (hp : 1 < α + ς)
    (hN : 1 ≤ N) (hNB : N ≤ B) : 0 < (svdArrays α ς N B).S * svdT0 N B := by
  obtain ⟨-, -, -, -, h5, -, -, -⟩ := prop_app_phase_prefactors_i α ς N B hα hp hN hNB 1 one_pos
  rw [h5]
  exact mul_pos (div_pos (fz7_gamma_pos hN hNB) two_pos) (fz2_Hsum_pos (α / 2) N hN)

lemma fz7_sgd_prod_pos (α ς : ℝ) (N B : ℕ) (hα : 0 < α) (hp : 1 < α + ς)
    (hN : 1 ≤ N) (hNB : N ≤ B) : 0 < (sgdArrays α ς N B).S * sgdT0 α N B := by
  obtain ⟨-, -, -, -, -, h6, h7, -⟩ := prop_app_phase_prefactors_i α ς N B hα hp hN hNB 1 one_pos
  rw [h6, h7]
  exact mul_pos (div_pos (mul_pos Real.pi_pos (fz7_gamma_pos hN hNB)) two_pos)
    (fz2_Hsum_pos α N hN)

lemma fz7_S_eq {N : ℕ} (A : PhaseArrays (Fin N)) (m : RowModel (Fin N)) (ε : ℝ)
    (hm : IsMatchedModel A m ε) : m.S = A.S := by
  obtain ⟨hμ, hd, hv, -, -⟩ := hm
  unfold RowModel.S PhaseArrays.S
  rw [hμ, hd, hv]

/-- One-model time identity `t = (S T0 / (2√ε)) 𝖨` from the hitting clause of `prop_app_phase_prefactors_iii`. -/
lemma fz7_time_eq {N : ℕ} (m : RowModel (Fin N)) (Q : ℝ → ℝ) (T0 T ε : ℝ) (hε : 0 < ε)
    (hK : 0 ≤ m.S * T0)
    (hpref : firstHit (riskClock m Q) (T * ε) = ENNReal.ofReal (m.S * T0 / (2 * Real.sqrt ε) *
      ∫ u in (0 : ℝ)..(firstHit (fun u => Q (T0 * u)) (T * ε)).toReal, Real.sqrt (Q (T0 * u)))) :
    (stepHit m Q T ε).toReal = m.S * T0 / (2 * Real.sqrt ε) * phaseClockI Q T0 T ε := by
  have hI : 0 ≤ ∫ u in (0 : ℝ)..(firstHit (fun u => Q (T0 * u)) (T * ε)).toReal,
      Real.sqrt (Q (T0 * u)) :=
    intervalIntegral.integral_nonneg ENNReal.toReal_nonneg (fun u _ => Real.sqrt_nonneg _)
  have hK' : 0 ≤ m.S * T0 / (2 * Real.sqrt ε) := div_nonneg hK (by positivity)
  unfold stepHit
  rw [hpref, ENNReal.toReal_ofReal (mul_nonneg hK' hI)]
  rfl

lemma fz7_svd_time {α ς T : ℝ} (hα : 0 < α) (hp : 1 < α + ς) (hT : 4 ≤ T) {N B : ℕ}
    (hN : 1 ≤ N) (hNB : N ≤ B) {ε : ℝ} (hε : 0 < ε) {mS mG : RowModel (Fin N)} {QS QG : ℝ → ℝ}
    (hmS : IsMatchedModel (svdArrays α ς N B) mS ε) (hmG : IsMatchedModel (sgdArrays α ς N B) mG ε)
    (hQS : IsVolterraSol mS QS) (hQG : IsVolterraSol mG QG)
    (hfin : dimHit QS (svdT0 N B) T ε ≠ ⊤) :
    (stepHit mS QS T ε).toReal = (svdArrays α ς N B).S * svdT0 N B / (2 * Real.sqrt ε) *
      phaseClockI QS (svdT0 N B) T ε := by
  have hpref := (prop_app_phase_prefactors_iii α ς N B hα hp hN hNB ε T hε (by linarith)
    mS mG hmS hmG QS QG hQS hQG).1 hfin
  have hS := fz7_S_eq _ mS ε hmS
  have hK : 0 ≤ mS.S * svdT0 N B := by
    rw [hS]; exact (fz7_svd_prod_pos α ς N B hα hp hN hNB).le
  rw [fz7_time_eq mS QS (svdT0 N B) T ε hε hK hpref, hS]

lemma fz7_sgd_time {α ς T : ℝ} (hα : 0 < α) (hp : 1 < α + ς) (hT : 4 ≤ T) {N B : ℕ}
    (hN : 1 ≤ N) (hNB : N ≤ B) {ε : ℝ} (hε : 0 < ε) {mS mG : RowModel (Fin N)} {QS QG : ℝ → ℝ}
    (hmS : IsMatchedModel (svdArrays α ς N B) mS ε) (hmG : IsMatchedModel (sgdArrays α ς N B) mG ε)
    (hQS : IsVolterraSol mS QS) (hQG : IsVolterraSol mG QG)
    (hfin : dimHit QG (sgdT0 α N B) T ε ≠ ⊤) :
    (stepHit mG QG T ε).toReal = (sgdArrays α ς N B).S * sgdT0 α N B / (2 * Real.sqrt ε) *
      phaseClockI QG (sgdT0 α N B) T ε := by
  have hpref := (prop_app_phase_prefactors_iii α ς N B hα hp hN hNB ε T hε (by linarith)
    mS mG hmS hmG QS QG hQS hQG).2 hfin
  have hS := fz7_S_eq _ mG ε hmG
  have hK : 0 ≤ mG.S * sgdT0 α N B := by
    rw [hS]; exact (fz7_sgd_prod_pos α ς N B hα hp hN hNB).le
  rw [fz7_time_eq mG QG (sgdT0 α N B) T ε hε hK hpref, hS]

/-- Ratio-to-one from a time identity with a common factor `c` and eventual `u = c I`. -/
lemma fz7_equiv {u v c I J : ℕ → ℝ} (hc : ∀ n, 0 < c n)
    (huc : ∀ᶠ n in atTop, u n = c n * I n) (hvc : ∀ n, v n = c n * J n)
    (hIJ : Tendsto (fun n => I n / J n) atTop (𝓝 1)) :
    Asymptotics.IsEquivalent atTop u v := by
  apply Asymptotics.isEquivalent_of_tendsto_one
  refine hIJ.congr' ?_
  filter_upwards [huc] with n hun
  simp only [Pi.div_apply]
  rw [hun, hvc n, mul_div_mul_left _ _ (hc n).ne']

lemma fz7_ne_of_div {a b : ℝ} (h : a / b ≠ 0) : a ≠ 0 ∧ b ≠ 0 :=
  ⟨fun ha => h (by rw [ha, zero_div]), fun hb => h (by rw [hb, div_zero])⟩

lemma fz7_alg {PG PS s IG IS JG JS : ℝ} (hs : s ≠ 0) (hPG : PG ≠ 0) (hPS : PS ≠ 0)
    (hIS : IS ≠ 0) (hJG : JG ≠ 0) (hJS : JS ≠ 0) :
    PG / (2 * s) * IG / (PS / (2 * s) * IS) / (PG / PS * JG / JS) = IG / JG / (IS / JS) := by
  field_simp

/-! ## The frozen regime: sequence statements -/

/-- Label `thm:app-phase-frozen`, part (i): both first hits are attained for all large indices.
Snapshot `cr-2026-10-23`. Source: section.tex l.1715–1730, the sentence "For all large indices both
first hits are attained". Verbatim statement of the theorem (the parts are split by display):
```latex
\begin{theorem}[Frozen regime]\label{thm:app-phase-frozen}
Fix $\alpha>0$, $\texp$ with $p=\alpha+\texp>1$, and $T\ge4$. Consider a sequence
of $(N,B,\epsilon)$ with $N\to\infty$, integers $B\ge N$ and
$x=\epsilon/\epsilon_N\to0$. For all large indices both first hits are attained,
and for both $j$
\[
\frac{\mathsf I_j}{J_N(p,q_j)}\longrightarrow1,\qquad
t^j_{T\epsilon}\sim\frac{\mathcal S_jT_0^j\,J_N(p,q_j)}{2\sqrt\epsilon},\qquad
\frac{t^{\text{s-SGD}}_{T\epsilon}}{t^{\text{s-SVD}}_{T\epsilon}}\sim\rho_N .
\]
Moreover, if $r_j<1$, there are $N_2$ and $c$ such that
\[
\Big|\frac{\mathsf I_j}{J_N(p,q_j)}-1\Big|\le c\,\Big(x^{1/4}+x^{1/2}\log\big(e+x^{-1/2}\big)\Big)^{1/2}
\]
for all $N\ge N_2$, $B\ge N$, $\epsilon<1/(2T)$ and $x\le1$.
\end{theorem}
``` -/
theorem thm_app_phase_frozen_i {α ς T : ℝ} (hα : 0 < α) (hp : 1 < α + ς) (hT : 4 ≤ T)
    (D : FrozenSeq α ς) :
    ∀ᶠ n in atTop,
      dimHit (D.QS n) (svdT0 (D.N n) (D.B n)) T (D.ε n) ≠ ⊤ ∧
        dimHit (D.QG n) (sgdT0 α (D.N n) (D.B n)) T (D.ε n) ≠ ⊤ := by
  filter_upwards [(fz6_svd hα hp hT D).1, (fz6_sgd hα hp hT D).1] with n h1 h2
  exact ⟨h1, h2⟩

/-- Label `thm:app-phase-frozen`, part (ii): `𝖨_j / J_N(p,q_j) → 1` for both `j`, with
`q_{s-SVD} = α/2`, `q_{s-SGD} = α`. Snapshot `cr-2026-10-23`. Source: section.tex l.1721:
```latex
\frac{\mathsf I_j}{J_N(p,q_j)}\longrightarrow1,
``` -/
theorem thm_app_phase_frozen_ii {α ς T : ℝ} (hα : 0 < α) (hp : 1 < α + ς) (hT : 4 ≤ T)
    (D : FrozenSeq α ς) :
    Tendsto (fun n => phaseClockI (D.QS n) (svdT0 (D.N n) (D.B n)) T (D.ε n) /
        JN (D.N n) (α + ς) (α / 2)) atTop (𝓝 1) ∧
      Tendsto (fun n => phaseClockI (D.QG n) (sgdT0 α (D.N n) (D.B n)) T (D.ε n) /
        JN (D.N n) (α + ς) α) atTop (𝓝 1) := by
  exact ⟨(fz6_svd hα hp hT D).2, (fz6_sgd hα hp hT D).2⟩

/-- Label `thm:app-phase-frozen`, part (iii): the step times `t^j_{Tε} ∼ 𝒮_j T_0^j J_N(p,q_j) / (2√ε)`
for both `j`. Snapshot `cr-2026-10-23`. Source: section.tex l.1722 (with `eqn:app-phase-time`, the
identity `t^j = 𝒮_j T_0^j 𝖨_j/(2√ε)`, used in the proof, l.2888):
```latex
t^j_{T\epsilon}\sim\frac{\mathcal S_jT_0^j\,J_N(p,q_j)}{2\sqrt\epsilon},
``` -/
theorem thm_app_phase_frozen_iii {α ς T : ℝ} (hα : 0 < α) (hp : 1 < α + ς) (hT : 4 ≤ T)
    (D : FrozenSeq α ς) :
    IsEquivalent atTop (fun n => (stepHit (D.mS n) (D.QS n) T (D.ε n)).toReal)
        (fun n => (svdArrays α ς (D.N n) (D.B n)).S * svdT0 (D.N n) (D.B n) *
          JN (D.N n) (α + ς) (α / 2) / (2 * Real.sqrt (D.ε n))) ∧
      IsEquivalent atTop (fun n => (stepHit (D.mG n) (D.QG n) T (D.ε n)).toReal)
        (fun n => (sgdArrays α ς (D.N n) (D.B n)).S * sgdT0 α (D.N n) (D.B n) *
          JN (D.N n) (α + ς) α / (2 * Real.sqrt (D.ε n))) := by
  refine ⟨?_, ?_⟩
  · refine fz7_equiv (u := fun n => (stepHit (D.mS n) (D.QS n) T (D.ε n)).toReal)
      (v := fun n => (svdArrays α ς (D.N n) (D.B n)).S * svdT0 (D.N n) (D.B n) *
        JN (D.N n) (α + ς) (α / 2) / (2 * Real.sqrt (D.ε n)))
      (c := fun n => (svdArrays α ς (D.N n) (D.B n)).S * svdT0 (D.N n) (D.B n) /
        (2 * Real.sqrt (D.ε n)))
      (I := fun n => phaseClockI (D.QS n) (svdT0 (D.N n) (D.B n)) T (D.ε n))
      (J := fun n => JN (D.N n) (α + ς) (α / 2)) ?_ ?_ ?_ ?_
    · intro n
      exact div_pos (fz7_svd_prod_pos α ς (D.N n) (D.B n) hα hp (D.le_B n).1 (D.le_B n).2)
        (mul_pos two_pos (Real.sqrt_pos.2 (D.ε_pos n)))
    · filter_upwards [(fz6_svd hα hp hT D).1] with n hn
      exact fz7_svd_time hα hp hT (D.le_B n).1 (D.le_B n).2 (D.ε_pos n)
        (D.matchS n) (D.matchG n) (D.volS n) (D.volG n) hn
    · intro n
      ring
    · exact (fz6_svd hα hp hT D).2
  · refine fz7_equiv (u := fun n => (stepHit (D.mG n) (D.QG n) T (D.ε n)).toReal)
      (v := fun n => (sgdArrays α ς (D.N n) (D.B n)).S * sgdT0 α (D.N n) (D.B n) *
        JN (D.N n) (α + ς) α / (2 * Real.sqrt (D.ε n)))
      (c := fun n => (sgdArrays α ς (D.N n) (D.B n)).S * sgdT0 α (D.N n) (D.B n) /
        (2 * Real.sqrt (D.ε n)))
      (I := fun n => phaseClockI (D.QG n) (sgdT0 α (D.N n) (D.B n)) T (D.ε n))
      (J := fun n => JN (D.N n) (α + ς) α) ?_ ?_ ?_ ?_
    · intro n
      exact div_pos (fz7_sgd_prod_pos α ς (D.N n) (D.B n) hα hp (D.le_B n).1 (D.le_B n).2)
        (mul_pos two_pos (Real.sqrt_pos.2 (D.ε_pos n)))
    · filter_upwards [(fz6_sgd hα hp hT D).1] with n hn
      exact fz7_sgd_time hα hp hT (D.le_B n).1 (D.le_B n).2 (D.ε_pos n)
        (D.matchS n) (D.matchG n) (D.volS n) (D.volG n) hn
    · intro n
      ring
    · exact (fz6_sgd hα hp hT D).2

/-- Label `thm:app-phase-frozen`, part (iv): the ratio of step times is asymptotic to
`ρ_N = D_N J_N(p,α)/J_N(p,α/2)` (`eqn:app-phase-rhoN`, reused as `phaseRhoN`). Snapshot
`cr-2026-10-23`. Source: section.tex l.1723:
```latex
\frac{t^{\text{s-SGD}}_{T\epsilon}}{t^{\text{s-SVD}}_{T\epsilon}}\sim\rho_N .
``` -/
theorem thm_app_phase_frozen_iv {α ς T : ℝ} (hα : 0 < α) (hp : 1 < α + ς) (hT : 4 ≤ T)
    (D : FrozenSeq α ς) :
    IsEquivalent atTop
      (fun n => (stepHit (D.mG n) (D.QG n) T (D.ε n)).toReal /
        (stepHit (D.mS n) (D.QS n) T (D.ε n)).toReal)
      (fun n => phaseRhoN α ς (D.N n)) := by
  apply Asymptotics.isEquivalent_of_tendsto_one
  have hq := (fz6_sgd hα hp hT D).2.div (fz6_svd hα hp hT D).2 one_ne_zero
  rw [div_one] at hq
  refine hq.congr' ?_
  filter_upwards [(fz6_svd hα hp hT D).1, (fz6_sgd hα hp hT D).1,
    (fz6_svd hα hp hT D).2.eventually_ne one_ne_zero,
    (fz6_sgd hα hp hT D).2.eventually_ne one_ne_zero] with n hSn hGn hSne hGne
  have hN1 := (D.le_B n).1
  have hNB := (D.le_B n).2
  have hε := D.ε_pos n
  obtain ⟨-, -, -, -, -, -, -, hDn⟩ :=
    prop_app_phase_prefactors_i α ς (D.N n) (D.B n) hα hp hN1 hNB 1 one_pos
  obtain ⟨hIS, hJS⟩ := fz7_ne_of_div hSne
  obtain ⟨-, hJG⟩ := fz7_ne_of_div hGne
  have htS := fz7_svd_time hα hp hT hN1 hNB hε (D.matchS n) (D.matchG n) (D.volS n)
    (D.volG n) hSn
  have htG := fz7_sgd_time hα hp hT hN1 hNB hε (D.matchS n) (D.matchG n) (D.volS n)
    (D.volG n) hGn
  have hPS := (fz7_svd_prod_pos α ς (D.N n) (D.B n) hα hp hN1 hNB).ne'
  have hPG := (fz7_sgd_prod_pos α ς (D.N n) (D.B n) hα hp hN1 hNB).ne'
  have hs : Real.sqrt (D.ε n) ≠ 0 := (Real.sqrt_pos.2 hε).ne'
  simp only [Pi.div_apply]
  rw [htG, htS]
  unfold phaseRhoN
  rw [← hDn]
  exact (fz7_alg hs hPG hPS hIS hJG hJS).symm

/-! ## The frozen regime: the rate for `r_j < 1` -/

lemma fz8_coeff {C r D τ : ℝ} (hC : 0 ≤ C) (hD : 0 < D)
    (hτ : 0 < τ) (hr : r < 1) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ x : ℝ, 0 < x → x ≤ 1 →
      0 ≤ frozenA2 C r D τ x ∧ 0 ≤ frozenDt C r D τ x ∧
      frozenA1 C r D τ x ≤ K * x ^ (1 / 4 : ℝ) ∧
      frozenA2 C r D τ x ≤ K * x ^ (1 / 4 : ℝ) ∧
      frozenDt C r D τ x ≤ K * x ^ (1 / 4 : ℝ) := by
  have hc2 : 0 ≤ frozenC2 C r D τ := by unfold frozenC2; positivity
  have hc1 : 0 ≤ frozenC1 C r D τ := by
    unfold frozenC1
    have : 0 < 1 - r / 2 := by linarith
    positivity
  let K := frozenC1 C r D τ + Real.sqrt (2 * frozenC2 C r D τ) + τ + 6 +
    4 * Real.sqrt (frozenC2 C r D τ)
  have hK : 0 ≤ K := by dsimp [K]; positivity
  refine ⟨K, hK, fun x hx hx1 => ?_⟩
  have h24 : x ^ (1 / 2 : ℝ) ≤ x ^ (1 / 4 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_ge hx hx1 (by norm_num)
  have hz : 0 ≤ x ^ (1 / 4 : ℝ) := by positivity
  have hdt := fz3_dt_bound hx hc2
  refine ⟨by unfold frozenA2; positivity, hdt.1, ?_, ?_, ?_⟩
  · unfold frozenA1
    have := mul_le_mul_of_nonneg_left h24 (show 0 ≤ τ + 1 by linarith)
    dsimp [K]
    nlinarith [Real.sqrt_nonneg (frozenC2 C r D τ)]
  · unfold frozenA2
    dsimp [K]
    nlinarith [Real.sqrt_nonneg (frozenC2 C r D τ)]
  · unfold frozenDt
    dsimp [K]
    nlinarith [Real.sqrt_nonneg (2 * frozenC2 C r D τ),
      Real.sqrt_nonneg (frozenC2 C r D τ)]

lemma fz8_rate {x : ℝ} (hx : 0 < x) (hx1 : x ≤ 1) :
    0 ≤ x ^ (1 / 4 : ℝ) ∧ x ^ (1 / 4 : ℝ) ≤ 1 ∧
      Real.sqrt x ≤ Real.sqrt (x ^ (1 / 4 : ℝ)) ∧
      Real.sqrt (x ^ (1 / 4 : ℝ)) ≤ frozenRate x ^ (1 / 2 : ℝ) := by
  have hz : 0 ≤ x ^ (1 / 4 : ℝ) := by positivity
  have hz1 := Real.rpow_le_one hx.le hx1 (by norm_num : (0 : ℝ) ≤ 1 / 4)
  have hxz : x ≤ x ^ (1 / 4 : ℝ) := by
    simpa using Real.rpow_le_rpow_of_exponent_ge hx hx1 (show (1 / 4 : ℝ) ≤ 1 by norm_num)
  refine ⟨hz, hz1, Real.sqrt_le_sqrt hxz, ?_⟩
  rw [← Real.sqrt_eq_rpow]
  apply Real.sqrt_le_sqrt
  unfold frozenRate
  have he : 1 ≤ Real.exp (1 : ℝ) := Real.one_le_exp (by norm_num)
  have hl : 0 ≤ Real.log (Real.exp 1 + x ^ (-(1 / 2 : ℝ))) :=
    Real.log_nonneg (by linarith [Real.rpow_nonneg hx.le (-(1 / 2 : ℝ))])
  have : 0 ≤ x ^ (1 / 2 : ℝ) * Real.log (Real.exp 1 + x ^ (-(1 / 2 : ℝ))) := by positivity
  linarith

lemma fz8_algebra {I J M a b d z k L : ℝ}
    (hJ : 0 < J) (hM : 0 ≤ M) (hz : 0 ≤ z) (hz1 : z ≤ 1)
    (hk : 0 ≤ k) (hL : 0 ≤ L) (hb : 0 ≤ b) (hd : 0 ≤ d)
    (ha : a * M ≤ k * z * J) (hb' : b * M ≤ k * z * J)
    (hd' : d * M ≤ k * z * J)
    (hlo : J - L * Real.sqrt z * J ≤ I)
    (hup : I ≤ J + a * M + 2 * Real.sqrt ((J + b * M) * (d * M)) + d * M) :
    |I / J - 1| ≤ (L + 2 * k + 2 * Real.sqrt ((1 + k) * k)) * Real.sqrt z := by
  have hs := Real.sqrt_nonneg z
  have hs2 := Real.sq_sqrt hz
  have hzs : z ≤ Real.sqrt z := by nlinarith
  have hbM : 0 ≤ b * M := mul_nonneg hb hM
  have hdM : 0 ≤ d * M := mul_nonneg hd hM
  have hbJ : J + b * M ≤ (1 + k) * J := by
    have := mul_le_mul_of_nonneg_left hz1 (mul_nonneg hk hJ.le)
    nlinarith
  have hp : (J + b * M) * (d * M) ≤ ((1 + k) * J) * (k * z * J) :=
    mul_le_mul hbJ hd' hdM (by positivity)
  have hroot : Real.sqrt ((J + b * M) * (d * M)) ≤
      Real.sqrt ((1 + k) * k) * Real.sqrt z * J := by
    calc
      _ ≤ Real.sqrt (((1 + k) * J) * (k * z * J)) := Real.sqrt_le_sqrt hp
      _ = _ := by
        rw [show ((1 + k) * J) * (k * z * J) = ((1 + k) * k) * z * J ^ 2 by ring,
          Real.sqrt_mul (by positivity), Real.sqrt_mul (by positivity), Real.sqrt_sq hJ.le]
  have hzsJ : k * z * J ≤ k * Real.sqrt z * J :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hzs hk) hJ.le
  have hLn : 0 ≤ L * Real.sqrt z * J := by positivity
  have hkn : 0 ≤ k * Real.sqrt z * J := by positivity
  have hsn : 0 ≤ Real.sqrt ((1 + k) * k) * Real.sqrt z * J := by positivity
  apply abs_le.2
  constructor
  · rw [le_sub_iff_add_le, le_div_iff₀ hJ]
    nlinarith only [hlo, hkn, hsn]
  · rw [sub_le_iff_le_add, div_le_iff₀ hJ]
    nlinarith only [hup, ha, hd', hroot, hzsJ, hLn]

lemma fz8_dimrate {p q T D τ : ℝ} (hp : 1 < p) (hq : 0 < q)
    (hr : rq p q < 1) (hT : 4 ≤ T) (hD : 1 ≤ D) (hτ : 0 < τ) :
    ∃ (N2 : ℕ) (c0 : ℝ), ∀ (N : ℕ) (ε : ℝ), N2 ≤ N →
      0 < ε → ε < 1 / (2 * T) → phaseX p N ε ≤ 1 →
      ∀ {n' : ℕ} (w c : Fin n' → ℝ), (∀ l, 0 ≤ w l) → ∑ l, w l = 1 →
      (∀ l, 2 * (N : ℝ) ^ (-q) ≤ c l) →
      PhaseOneBound (mixG w c) (Cpq p q) q (rq p q) D τ N →
      ∀ Y : ℝ → ℝ, ContinuousOn Y (Ici 0) → (∀ u ∈ Ici (0 : ℝ), 0 < Y u) →
      (∀ u ∈ Ici (0 : ℝ), Y u = fNq (N : ℕ∞) p q u +
        Real.sqrt ε * oneSidedConv (fun v => Real.sqrt (Y v)) (mixG w c) u) →
      |dimClockI Y T ε / JN N p q - 1| ≤ c0 * frozenRate (phaseX p N ε) ^ (1 / 2 : ℝ) := by
  have hNt : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  obtain ⟨cJ, hcJ, hJ⟩ := fz5_Jlt1 hp hq hr hNt
  obtain ⟨NJ, hNJ⟩ := eventually_atTop.1 hJ
  have hDt : ∀ᶠ n : ℕ in atTop, D ≤ τ * (n : ℝ) ^ q := by
    have ht := (tendsto_rpow_atTop hq).comp hNt
    filter_upwards [ht.eventually_ge_atTop (D / τ)] with n hn
    rw [div_le_iff₀ hτ] at hn
    change D ≤ (n : ℝ) ^ q * τ at hn
    linarith
  obtain ⟨ND, hND⟩ := eventually_atTop.1 hDt
  obtain ⟨K, hK, hcoeff⟩ := fz8_coeff (fz_Cpq_pos hp hq).le (by linarith : 0 < D) hτ hr
  let k := K / cJ
  let L := Real.sqrt T / cJ
  let c0 := L + 2 * k + 2 * Real.sqrt ((1 + k) * k)
  have hk : 0 ≤ k := div_nonneg hK hcJ.le
  have hL : 0 ≤ L := div_nonneg (Real.sqrt_nonneg _) hcJ.le
  have hc0 : 0 ≤ c0 := by dsimp [c0]; positivity
  refine ⟨max 4 (max NJ ND), c0, ?_⟩
  intro N ε hN hε hεT hx1 n' w c hw hw1 hc hg Y hYc hYp hY
  have hN4 : 4 ≤ N := (le_max_left _ _).trans hN
  have hN1 : 1 ≤ N := by omega
  have hJN := hNJ N ((le_max_left NJ ND).trans ((le_max_right _ _).trans hN))
  have hDN := hND N ((le_max_right NJ ND).trans ((le_max_right _ _).trans hN))
  have hM : 0 < (N : ℝ) ^ (q * (1 - rq p q)) := Real.rpow_pos_of_pos (by exact_mod_cast hN1) _
  have hJpos : 0 < JN N p q := (mul_pos hcJ hM).trans_le hJN
  obtain ⟨hx, hsc, -⟩ := fz3_scale hN1 hε hq hp
  obtain ⟨hz, hz1, hxs, hrate⟩ := fz8_rate hx hx1
  obtain ⟨hb, hd, ha', hb', hd'⟩ := hcoeff _ hx hx1
  have hscale : ∀ a : ℝ, a ≤ K * phaseX p N ε ^ (1 / 4 : ℝ) →
      a * (N : ℝ) ^ (q * (1 - rq p q)) ≤ k * phaseX p N ε ^ (1 / 4 : ℝ) * JN N p q := by
    intro a ha
    calc
      _ ≤ (K * phaseX p N ε ^ (1 / 4 : ℝ)) * (N : ℝ) ^ (q * (1 - rq p q)) :=
        mul_le_mul_of_nonneg_right ha hM.le
      _ = (k * phaseX p N ε ^ (1 / 4 : ℝ)) * (cJ * (N : ℝ) ^ (q * (1 - rq p q))) := by
        dsimp [k]; field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left hJN (by positivity)
  obtain ⟨û, hfh, hû, -, hlo, -⟩ := fz2_core hp hq hT hε hεT hN1 w c hw hw1 hc Y hYc hYp hY
  have hI : dimClockI Y T ε = ∫ u in (0 : ℝ)..û, Real.sqrt (Y u) := by
    unfold dimClockI; rw [hfh, ENNReal.toReal_ofReal hû.le]
  have hδ : Real.sqrt (T * ε) * (N : ℝ) ^ q ≤
      L * Real.sqrt (phaseX p N ε ^ (1 / 4 : ℝ)) * JN N p q := by
    rw [Real.sqrt_mul (by linarith : 0 ≤ T), mul_assoc, hsc]
    calc
      _ ≤ Real.sqrt T * (Real.sqrt (phaseX p N ε ^ (1 / 4 : ℝ)) * (N : ℝ) ^ (q * (1 - rq p q))) := by
        gcongr
      _ = (L * Real.sqrt (phaseX p N ε ^ (1 / 4 : ℝ))) * (cJ * (N : ℝ) ^ (q * (1 - rq p q))) := by
        dsimp [L]; field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left hJN (by positivity)
  have hup := lem_app_phase_frozenerr hp hq hr hT hε hεT hN4 hD hτ hDN w c hw hw1 hc hg Y hYc hYp hY
  unfold frozenErrBound at hup
  have hresult := fz8_algebra hJpos hM.le hz hz1 hk hL hb hd (hscale _ ha')
    (hscale _ hb') (hscale _ hd') (show JN N p q - L * Real.sqrt (phaseX p N ε ^ (1 / 4 : ℝ)) * JN N p q ≤ dimClockI Y T ε by
      rw [hI]; linarith) hup
  exact hresult.trans (mul_le_mul_of_nonneg_left hrate hc0)

lemma fz8_matches {α ς ε : ℝ} {N B : ℕ} (hα : 0 < α)
    (hp : 1 < α + ς) (hN : 1 ≤ N) (hNB : N ≤ B) (hε : 0 < ε) :
    (∃ m : RowModel (Fin N), IsMatchedModel (svdArrays α ς N B) m ε) ∧
      (∃ m : RowModel (Fin N), IsMatchedModel (sgdArrays α ς N B) m ε) := by
  obtain ⟨hS, hG, -, -⟩ := prop_app_phase_prefactors_m1 α ς N B hα hp hN hNB
  constructor
  · have hprod := fz7_svd_prod_pos α ς N B hα hp hN hNB
    have htime := fz2_svdT0_pos N B hN hNB
    have hA : 0 < (svdArrays α ς N B).S := ((mul_pos_iff.1 hprod).resolve_right (by rintro ⟨_, ht⟩; linarith)).1
    exact hS (matchedStep (svdArrays α ς N B) ε) (by unfold matchedStep; positivity)
  · have hprod := fz7_sgd_prod_pos α ς N B hα hp hN hNB
    have htime := fz2_sgdT0_pos α N B hN hNB
    have hA : 0 < (sgdArrays α ς N B).S := ((mul_pos_iff.1 hprod).resolve_right (by rintro ⟨_, ht⟩; linarith)).1
    exact hG (matchedStep (sgdArrays α ς N B) ε) (by unfold matchedStep; positivity)

/-- Label `thm:app-phase-frozen`, "moreover" clause for the \SignSVD model (`r_{s-SVD} < 1`): there
are `N_2` and `c` such that `|𝖨_j/J_N(p,q_j) - 1| ≤ c (x^{1/4} + x^{1/2} log(e + x^{-1/2}))^{1/2}`
for all `N ≥ N_2`, `B ≥ N`, `ε < 1/(2T)` and `x ≤ 1`. Snapshot `cr-2026-10-23`. Source:
section.tex l.1724–1727:
```latex
Moreover, if $r_j<1$, there are $N_2$ and $c$ such that
\[
\Big|\frac{\mathsf I_j}{J_N(p,q_j)}-1\Big|\le c\,\Big(x^{1/4}+x^{1/2}\log\big(e+x^{-1/2}\big)\Big)^{1/2}
\]
for all $N\ge N_2$, $B\ge N$, $\epsilon<1/(2T)$ and $x\le1$.
``` -/
theorem thm_app_phase_frozen_v_i {α ς T : ℝ} (hα : 0 < α) (hp : 1 < α + ς) (hT : 4 ≤ T)
    (hr : rq (α + ς) (α / 2) < 1) :
    ∃ (N2 : ℕ) (c : ℝ), ∀ (N B : ℕ) (ε : ℝ) (m : RowModel (Fin N)) (Q : ℝ → ℝ),
      N2 ≤ N → N ≤ B → 0 < ε → ε < 1 / (2 * T) → phaseX (α + ς) N ε ≤ 1 →
      IsMatchedModel (svdArrays α ς N B) m ε → IsVolterraSol m Q →
      |phaseClockI Q (svdT0 N B) T ε / JN N (α + ς) (α / 2) - 1| ≤
        c * frozenRate (phaseX (α + ς) N ε) ^ (1 / 2 : ℝ) := by
  have hq : 0 < α / 2 := by linarith
  have hς : ς < 1 := by
    unfold rq at hr
    rw [div_lt_one (by linarith)] at hr
    linarith
  obtain ⟨D, τ, N0, hD, hτ, hphase⟩ := fz4_svd_one α ς hα (by linarith) hς
  obtain ⟨N1, c0, hrate⟩ := fz8_dimrate hp hq hr hT hD hτ
  refine ⟨max N0 (max 1 N1), c0, ?_⟩
  intro N B ε m Q hN hNB hε hεT hx hm hQ
  have hN0 : N0 ≤ N := (le_max_left _ _).trans hN
  have hN1 : 1 ≤ N := (le_max_left _ _).trans ((le_max_right _ _).trans hN)
  have hNN : N1 ≤ N := (le_max_right _ _).trans ((le_max_right _ _).trans hN)
  obtain ⟨mG, hmG⟩ := (fz8_matches hα hp hN1 hNB hε).2
  obtain ⟨QG, hQG, -⟩ := thm_app_phase_volterra_i mG
  obtain ⟨w, c, hw, hw1, hc, hker, hYc, hYp, hY⟩ :=
    fz2_svd_model α ς N B hα hp hN1 hNB ε hε m mG hm hmG Q QG hQ hQG
  exact hrate N ε hNN hε hεT hx w c hw hw1 hc
    (hphase N hN0 hN1 w c hw hw1 hc hker) _ hYc hYp hY

/-- Label `thm:app-phase-frozen`, "moreover" clause for the \SignSGD model (`r_{s-SGD} < 1`); the
same statement as `thm_app_phase_frozen_v_i` with `q = α`, `sgdArrays`, `sgdT0`. Snapshot
`cr-2026-10-23`. Source: section.tex l.1724–1727 (verbatim display as in
`thm_app_phase_frozen_v_i`). -/
theorem thm_app_phase_frozen_v_ii {α ς T : ℝ} (hα : 0 < α) (hp : 1 < α + ς) (hT : 4 ≤ T)
    (hr : rq (α + ς) α < 1) :
    ∃ (N2 : ℕ) (c : ℝ), ∀ (N B : ℕ) (ε : ℝ) (m : RowModel (Fin N)) (Q : ℝ → ℝ),
      N2 ≤ N → N ≤ B → 0 < ε → ε < 1 / (2 * T) → phaseX (α + ς) N ε ≤ 1 →
      IsMatchedModel (sgdArrays α ς N B) m ε → IsVolterraSol m Q →
      |phaseClockI Q (sgdT0 α N B) T ε / JN N (α + ς) α - 1| ≤
        c * frozenRate (phaseX (α + ς) N ε) ^ (1 / 2 : ℝ) := by
  obtain ⟨D, τ, N0, hD, hτ, hphase⟩ := fz4_sgd_one α ς hα hp hr
  obtain ⟨N1, c0, hrate⟩ := fz8_dimrate hp hα hr hT hD hτ
  refine ⟨max N0 (max 1 N1), c0, ?_⟩
  intro N B ε m Q hN hNB hε hεT hx hm hQ
  have hN0 : N0 ≤ N := (le_max_left _ _).trans hN
  have hN1 : 1 ≤ N := (le_max_left _ _).trans ((le_max_right _ _).trans hN)
  have hNN : N1 ≤ N := (le_max_right _ _).trans ((le_max_right _ _).trans hN)
  obtain ⟨mS, hmS⟩ := (fz8_matches hα hp hN1 hNB hε).1
  obtain ⟨QS, hQS, -⟩ := thm_app_phase_volterra_i mS
  obtain ⟨w, c, hw, hw1, hc, hker, hYc, hYp, hY⟩ :=
    fz2_sgd_model α ς N B hα hp hN1 hNB ε hε mS m hmS hm QS Q hQS hQ
  exact hrate N ε hNN hε hεT hx w c hw hw1 hc
    (hphase N hN0 hN1 w c hker) _ hYc hYp hY

end Muon.Phase
