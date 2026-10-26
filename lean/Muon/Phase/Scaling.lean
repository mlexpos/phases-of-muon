import Mathlib
import Muon.Phase.Arrays
import Muon.Phase.Clock

/-!
# Appendix H: adoption and momentum scaling of the adopted arrays (task L-H.10)

Snapshot `cr-2026-10-23`. Source: `sections/07-phase-comparison/section.tex`:
`rem:app-phase-adoption` (l.158–182; only the promoted scaling sentence, l.174–177) and
`rem:app-phase-momentum` (l.1496–1542; promoted parts (a), (b), (c)).
Card: `sections/07-phase-comparison/CARD.md` §3, §5 (L-H.10), §6.1.

Reused, not redefined: `RowModel`, `IsRowSolution`, `firstHit`, `riskClock`
(`Muon.Phase.Model`, `Muon.Phase.Clock`); `IsVolterraSol` (`Muon.Phase.Volterra`);
`PhaseArrays`, `svdArrays`, `matchedStep`, `IsMatchedModel`, `muOf`, `Q0Of`
(`Muon.Phase.Arrays`); `thm_app_phase_clock` (uniqueness of the row solution, clause 8).

Encoding decisions:
* `scaledArrays a b A` multiplies the drift by `a` and the volatility by `b`; weights and initial
  energies are unchanged. The adopted matched step of the scaled array is `2√ε/𝒮'` with
  `𝒮' = (b/a)𝒮`, so matched models satisfy `η' = η a/b`.
* The scaling lemmas (`scaling_row_solution`, `scaling_hitting`) are the one lemma of card §5.
  Time rescaling is `λ = a²/b`: a row solution `Q` for `(A, m)` gives `t ↦ Q(λt)` for the scaled
  model on `[0, t₁/λ)`, and the first hitting times satisfy `t' = t/λ` (ratio `b/a²`).
* The promoted statements are instances of the lemma: adoption `(a,b) = (c,1)`, momentum (c)
  `(a,b) = (1,c)`, momentum (b) `(a,b) = (c,c²)` with `c = √(B_eff/B)`.
* `momentumArrays α ς N B β` is the explicit formula of `rem:app-phase-momentum`:
  `𝔡^β_i = √μ_i √(B_eff/N)`, `𝔳^β_i = B_eff/B`, `B_eff = B(1+β)/(1-β)`, same `μ_i`, `𝔔_i(0)`.
* Matched models enter as hypotheses `IsMatchedModel _ m ε` (the RowModel fields are not
  constructed here); `ε > 0` is explicit. `S > 0` is not assumed: it follows from `η > 0`.
* Not encoded: the factor-½ consequences of §6.1 (the constant changes are the user's decision),
  `c_β ∈ (σ₂, 1)` (F's `lem:app-iso-V`), and the invariance of the dimensionless `Y_j`, `û_j`
  (depends on a momentum time scale `T₀^β` that the remark does not define; see
  `open_questions` in the result JSON).
-/

set_option linter.style.longLine false

open Set Filter Topology
open scoped ENNReal NNReal

noncomputable section

namespace Muon.Phase

variable {ι : Type*}

/-- Scaled coefficient arrays: drift `a 𝔡_i`, volatility `b 𝔳_i`, weights `μ_i` and initial
energies `𝔔_i(0)` unchanged. Used by the scaling statements of this file. -/
def scaledArrays (a b : ℝ) (A : PhaseArrays ι) : PhaseArrays ι where
  μ := A.μ
  d := fun i => a * A.d i
  v := fun i => b * A.v i
  Q0 := A.Q0

/-- `B_eff = B(1+β)/(1-β) = B/σ₂` of `rem:app-phase-momentum` (`β ∈ [0,1)`). -/
def momentumBeff (B : ℕ) (β : ℝ) : ℝ := (B : ℝ) * (1 + β) / (1 - β)

/-- Adopted momentum arrays of `rem:app-phase-momentum`: the weights `μ_i` and initial energies
`𝔔_i(0)` of `def:app-phase-arrays`, drift `𝔡^β_i = √μ_i √(B_eff/N)`, volatility
`𝔳^β_i = B_eff/B`. -/
def momentumArrays (α ς : ℝ) (N B : ℕ) (β : ℝ) : PhaseArrays (Fin N) where
  μ := muOf α N
  d := fun i => Real.sqrt (muOf α N i) * Real.sqrt (momentumBeff B β / (N : ℝ))
  v := fun _ => momentumBeff B β / (B : ℝ)
  Q0 := Q0Of ς N

/-- The right-hand side of the row equation `eqn:app-phase-rows` for one row at step `η`:
`-2η𝔡 x / √R + η²𝔳` with `x = 𝔔_i(t)` and `R = 𝔑(t)`. -/
def rowRHS (η d v x R : ℝ) : ℝ := -(2 * η * d) / Real.sqrt R * x + η ^ 2 * v

/-- Scaling of the row system (the mechanism behind `rem:app-phase-adoption` and
`rem:app-phase-momentum`). Let `m` be matched to `A` and `m'` to `scaledArrays a b A` at the
same level `ε`, so `η' = η a/b`. If `Q` solves the rows of `m` on `[0, t₁)`, then
`t ↦ Q(a²t/b)` solves the rows of `m'` on `[0, t₁ b/a²)`: the time rescaling is `λ = a²/b`
and the drift and volatility terms transform as `λ` times the original terms. -/
theorem scaling_row_solution (A : PhaseArrays ι) {a b ε : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hε : 0 < ε) (m m' : RowModel ι)
    (hm : IsMatchedModel A m ε) (hm' : IsMatchedModel (scaledArrays a b A) m' ε)
    (t₁ : ℝ) (Q : ι → ℝ → ℝ) (hQ : IsRowSolution m t₁ Q) :
    IsRowSolution m' (t₁ * (b / a ^ 2)) (fun i t => Q i ((a ^ 2 / b) * t)) := by
  obtain ⟨hμ, hd, hv, hQ0, hη⟩ := hm
  obtain ⟨hμ', hd', hv', hQ0', hη'⟩ := hm'
  have ha0 : a ≠ 0 := ha.ne'
  have hb0 : b ≠ 0 := hb.ne'
  have hμm : m'.μ = m.μ := hμ'.trans hμ.symm
  have hQ0m : m'.Q0 = m.Q0 := hQ0'.trans hQ0.symm
  have hdm : ∀ i, m'.d i = a * m.d i := fun i => by
    have h := congrFun hd' i
    have h2 := congrFun hd i
    simp only [scaledArrays] at h
    rw [h, ← h2]
  have hvm : ∀ i, m'.v i = b * m.v i := fun i => by
    have h := congrFun hv' i
    have h2 := congrFun hv i
    simp only [scaledArrays] at h
    rw [h, ← h2]
  have hdpos : ∀ i, 0 < A.d i := fun i => by
    have h := m.d_pos i
    rwa [hd] at h
  have hS : A.S ≠ 0 := by
    intro h
    have hp := m.η_pos
    rw [hη, matchedStep, h, div_zero] at hp
    exact lt_irrefl _ hp
  have hSS : (scaledArrays a b A).S = b / a * A.S := by
    unfold PhaseArrays.S
    rw [← tsum_mul_left]
    congr 1
    funext i
    have := hdpos i
    have hd0 : A.d i ≠ 0 := this.ne'
    simp only [scaledArrays]
    field_simp
  have hηm : m'.η = a / b * m.η := by
    rw [hη', hη]
    simp only [matchedStep]
    rw [hSS]
    field_simp
  have hk : 0 < a ^ 2 / b := div_pos (pow_pos ha 2) hb
  have hkt : a ^ 2 / b * (t₁ * (b / a ^ 2)) = t₁ := by
    field_simp
  have hmem : ∀ t ∈ Ico (0 : ℝ) (t₁ * (b / a ^ 2)), a ^ 2 / b * t ∈ Ico (0 : ℝ) t₁ := by
    intro t ht
    refine ⟨mul_nonneg hk.le ht.1, ?_⟩
    have := mul_lt_mul_of_pos_left ht.2 hk
    rwa [hkt] at this
  have hRmain : ∀ t, m'.risk (fun i t => Q i ((a ^ 2 / b) * t)) t = m.risk Q ((a ^ 2 / b) * t) :=
    fun t => by simp only [RowModel.risk, hμm]
  unfold IsRowSolution at hQ ⊢
  obtain ⟨hQ0v, hsum, hcont, hpos, hderiv⟩ := hQ
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro i
    change Q i (a ^ 2 / b * 0) = m'.Q0 i
    rw [mul_zero, hQ0v i, hQ0m]
  · intro t ht
    have := hsum _ (hmem t ht)
    rw [hμm]
    exact this
  · have hc : ContinuousOn (fun t => m.risk Q (a ^ 2 / b * t)) (Ico (0 : ℝ) (t₁ * (b / a ^ 2))) :=
      hcont.comp (continuous_const.mul continuous_id).continuousOn (fun t ht => hmem t ht)
    exact hc.congr (fun t _ => hRmain t)
  · intro t ht
    rw [hRmain t]
    exact hpos _ (hmem t ht)
  · intro t ht i
    have h1 := hderiv _ (hmem t ht) i
    have h2 : HasDerivAt (fun s => a ^ 2 / b * s) (a ^ 2 / b) t := by
      simpa using (hasDerivAt_id t).const_mul (a ^ 2 / b)
    have h3 := h1.comp t h2.hasDerivWithinAt (fun s hs => hmem s hs)
    refine h3.congr_deriv ?_
    simp only [hRmain, hηm, hdm, hvm]
    field_simp

/-- Private: `S > 0` for a model matched to `A` at a level `ε > 0` (from `η > 0`). -/
private lemma scl_S_pos {ι : Type*} (A : PhaseArrays ι) {ε : ℝ} (m : RowModel ι)
    (hm : IsMatchedModel A m ε) : 0 < m.S := by
  obtain ⟨hμ, hd, hv, _, hη'⟩ := hm
  have hpos := m.η_pos
  have hnn : 0 ≤ m.S := by
    unfold RowModel.S
    exact tsum_nonneg fun i =>
      div_nonneg (mul_nonneg (m.μ_pos i).le (m.v_nonneg i)) (by linarith [m.d_pos i])
  have hne : m.S ≠ 0 := by
    intro h
    have h' : A.S = 0 := by
      unfold RowModel.S at h
      unfold PhaseArrays.S
      rw [hμ, hd, hv] at h
      exact h
    rw [hη', matchedStep, h', div_zero] at hpos
    exact lt_irrefl _ hpos
  exact lt_of_le_of_ne hnn (Ne.symm hne)

/-- Private: on `[0,∞)` with `S > 0` (so `t_* = ⊤`), the clock is a genuine inverse. -/
private lemma scl_clock_top [Countable ι] (m : RowModel ι) (Q : ℝ → ℝ) (hQ : IsVolterraSol m Q)
    (htop : tStar m Q = ⊤) {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ clock m Q t ∧ clockTime m Q (clock m Q t) = t := by
  obtain ⟨_, _, _, _, c5, _, _, _, _, _, _⟩ := thm_app_phase_clock m Q hQ
  have hmem : t ∈ clockTime m Q '' Ici (0:ℝ) := by
    rw [c5]
    exact ⟨ht, by rw [htop]; exact ENNReal.ofReal_lt_top⟩
  obtain ⟨s, hs, hst⟩ := hmem
  obtain ⟨h1, h2⟩ := Function.invFunOn_pos (f := clockTime m Q) (s := Ici (0:ℝ)) (b := t)
    ⟨s, hs, hst⟩
  exact ⟨Set.mem_Ici.1 h1, h2⟩

/-- Private: the step-time risk is the risk of the step-time rows (`S > 0`). -/
private lemma scl_riskClock_top [Countable ι] (m : RowModel ι) (Q : ℝ → ℝ) (hQ : IsVolterraSol m Q)
    (htop : tStar m Q = ⊤) {t : ℝ} (ht : 0 ≤ t) :
    riskClock m Q t = m.risk (rowsInStepTime m Q) t := by
  obtain ⟨c1, _, _, _, _, _, _, _, _, _, _⟩ := thm_app_phase_clock m Q hQ
  have hc := (scl_clock_top m Q hQ htop ht).1
  simp only [riskClock, RowModel.risk, rowsInStepTime]
  exact (c1 _ (Set.mem_Ici.2 hc)).symm

/-- Private: the step-time risk of the scaled model at `t ≥ 0` is the original risk at `(a²/b) t`.
Uses uniqueness of the row solution (clause 8) for the scaled model and `scaling_row_solution`. -/
private lemma scl_riskClock_scale [Countable ι] (A : PhaseArrays ι) {a b ε : ℝ} (ha : 0 < a)
    (hb : 0 < b) (hε : 0 < ε) (m m' : RowModel ι)
    (hm : IsMatchedModel A m ε) (hm' : IsMatchedModel (scaledArrays a b A) m' ε)
    (Q Q' : ℝ → ℝ) (hQ : IsVolterraSol m Q) (hQ' : IsVolterraSol m' Q') {t : ℝ} (ht : 0 ≤ t) :
    riskClock m' Q' t = riskClock m Q ((a ^ 2 / b) * t) := by
  have ha0 : a ≠ 0 := ha.ne'
  have hb0 : b ≠ 0 := hb.ne'
  have hk : 0 < a ^ 2 / b := div_pos (pow_pos ha 2) hb
  obtain ⟨_, _, _, _, _, _, c7, c8, _, c10, _⟩ := thm_app_phase_clock m Q hQ
  obtain ⟨_, _, _, _, _, _, _, c8', _, c10', _⟩ := thm_app_phase_clock m' Q' hQ'
  have htop : tStar m Q = ⊤ := (c10 (scl_S_pos A m hm)).1
  have htop' : tStar m' Q' = ⊤ := (c10' (scl_S_pos _ m' hm')).1
  have hμm : m'.μ = m.μ := (hm'.1).trans hm.1.symm
  have hR : IsRowSolution m ((t + 1) * (a ^ 2 / b)) (rowsInStepTime m Q) :=
    c7 _ (by rw [htop]; exact le_top)
  have hS' := scaling_row_solution A ha hb hε m m' hm hm' _ (rowsInStepTime m Q) hR
  have e : (t + 1) * (a ^ 2 / b) * (b / a ^ 2) = t + 1 := by
    field_simp
  rw [e] at hS'
  have hpt : ∀ i, rowsInStepTime m' Q' i t = rowsInStepTime m Q i ((a ^ 2 / b) * t) := by
    intro i
    have hmem : t ∈ Ico (0:ℝ) (t + 1) := ⟨ht, by linarith⟩
    exact (c8' (t + 1) (by rw [htop']; exact le_top) _ hS' i t hmem).symm
  have hlam : 0 ≤ (a ^ 2 / b) * t := mul_nonneg hk.le ht
  rw [scl_riskClock_top m' Q' hQ' htop' ht, scl_riskClock_top m Q hQ htop hlam]
  unfold RowModel.risk
  congr 1
  apply tsum_congr
  intro i
  rw [hμm, hpt i]

/-- Private: reparametrization of the first hitting time by a positive linear change of time. -/
private lemma scl_firstHit_scale (R : ℝ → ℝ) {c : ℝ} (hc : 0 < c) (ℓ : ℝ) :
    firstHit (fun t : ℝ => R (c * t)) ℓ = ENNReal.ofReal (1 / c) * firstHit R ℓ := by
  have hc0 : c ≠ 0 := hc.ne'
  have hκ : (0:ℝ) ≤ 1 / c := (one_div_pos.2 hc).le
  have h0 : ENNReal.ofReal (1 / c) ≠ 0 := by
    rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]
    exact one_div_pos.2 hc
  have hT : ENNReal.ofReal (1 / c) ≠ ⊤ := ENNReal.ofReal_ne_top
  unfold firstHit
  simp only [ENNReal.mul_iInf_of_ne h0 hT]
  refine le_antisymm ?_ ?_
  · refine le_iInf₂ fun (u : NNReal) (hu : R u ≤ ℓ) => ?_
    have hcond : R (c * ((Real.toNNReal (1 / c) * u : NNReal) : ℝ)) ≤ ℓ := by
      have e : c * ((Real.toNNReal (1 / c) * u : NNReal) : ℝ) = (u : ℝ) := by
        rw [NNReal.coe_mul, Real.coe_toNNReal _ hκ]
        field_simp
      rw [e]
      exact hu
    refine le_trans (iInf₂_le (Real.toNNReal (1 / c) * u) hcond) (le_of_eq ?_)
    calc ((Real.toNNReal (1 / c) * u : NNReal) : ENNReal)
        = ENNReal.ofReal ((Real.toNNReal (1 / c) * u : NNReal) : ℝ) :=
          ENNReal.ofReal_coe_nnreal.symm
      _ = ENNReal.ofReal (1 / c * (u : ℝ)) := by
          rw [NNReal.coe_mul, Real.coe_toNNReal _ hκ]
      _ = ENNReal.ofReal (1 / c) * ENNReal.ofReal (u : ℝ) := ENNReal.ofReal_mul hκ
      _ = ENNReal.ofReal (1 / c) * (u : ENNReal) := by rw [ENNReal.ofReal_coe_nnreal]
  · refine le_iInf₂ fun (t : NNReal) (ht : R (c * (t : ℝ)) ≤ ℓ) => ?_
    have hcond : R ((Real.toNNReal c * t : NNReal) : ℝ) ≤ ℓ := by
      rw [NNReal.coe_mul, Real.coe_toNNReal _ hc.le]
      exact ht
    refine le_trans (iInf₂_le (Real.toNNReal c * t) hcond) (le_of_eq ?_)
    calc ENNReal.ofReal (1 / c) * ((Real.toNNReal c * t : NNReal) : ENNReal)
        = ENNReal.ofReal (1 / c) * ENNReal.ofReal ((Real.toNNReal c * t : NNReal) : ℝ) := by
          rw [ENNReal.ofReal_coe_nnreal]
      _ = ENNReal.ofReal (1 / c * ((Real.toNNReal c * t : NNReal) : ℝ)) :=
          (ENNReal.ofReal_mul hκ).symm
      _ = ENNReal.ofReal (t : ℝ) := by
          congr 1
          rw [NNReal.coe_mul, Real.coe_toNNReal _ hc.le]
          field_simp
      _ = (t : ENNReal) := ENNReal.ofReal_coe_nnreal

/-- Scaling of first hitting times for matched models. With the Volterra solutions `Q` of `m` and
`Q'` of `m'` (`IsVolterraSol`, global since `𝒮 > 0`), the step-time risks satisfy
`𝔑'(t) = 𝔑(a²t/b)`, so `t'_ℓ = (b/a²) t_ℓ` for every level `ℓ > 0`. Uniqueness of the row
solution is `thm_app_phase_clock`, clause 8. -/
theorem scaling_hitting [Countable ι] (A : PhaseArrays ι) {a b ε : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hε : 0 < ε) (m m' : RowModel ι)
    (hm : IsMatchedModel A m ε) (hm' : IsMatchedModel (scaledArrays a b A) m' ε)
    (Q Q' : ℝ → ℝ) (hQ : IsVolterraSol m Q) (hQ' : IsVolterraSol m' Q') (ℓ : ℝ) (hℓ : 0 < ℓ) :
    firstHit (riskClock m' Q') ℓ = ENNReal.ofReal (b / a ^ 2) * firstHit (riskClock m Q) ℓ := by
  have hk : 0 < a ^ 2 / b := div_pos (pow_pos ha 2) hb
  have hpt : ∀ t : NNReal, riskClock m' Q' (t : ℝ) =
      riskClock m Q ((a ^ 2 / b) * (t : ℝ)) := fun t =>
    scl_riskClock_scale A ha hb hε m m' hm hm' Q Q' hQ hQ' t.coe_nonneg
  have hfun : firstHit (riskClock m' Q') ℓ =
      firstHit (fun t : ℝ => riskClock m Q ((a ^ 2 / b) * t)) ℓ := by
    unfold firstHit
    simp only [hpt]
  rw [hfun, scl_firstHit_scale (riskClock m Q) hk ℓ, one_div_div]

/-- `rem:app-phase-adoption` (promoted sentence, l.174–177): a uniform factor `c`
in the drift at fixed volatility rescales the matched-step clock by `c⁻²`, so every matched-step
first hitting time is multiplied by `c⁻²` (`scaledArrays c 1`).

Snapshot `cr-2026-10-23`. Source: `sections/07-phase-comparison/section.tex` l.158–182.
```latex
\begin{remark}[Where the adopted coefficients come from]\label{rem:app-phase-adoption}
The power-law arrays of \cref{def:app-phase-arrays} are modelled on the coefficients of
the main text's half-anisotropic table in the oversampled regime $B\ge N$
(\cref{sec:half-aniso}), at zero momentum and zero ridge. For momentum
$\bmom\in(0,1)$, \cref{thm:app-pl-triple} computes the zero-ridge row
coefficients in the thin-batch regime $N/B\to\infty$, and
\cref{rem:app-pl-dynamics-scope} inserts them into the row equations as
adopted coefficients. The oversampled regime is not covered by that
theorem. The resolved-window endpoint of \cref{cor:app-pl-endpoints}(ii),
\[
\sqrt2\,\mathfrak d_i(0)\sim\sqrt{\frac{\mu_i}{\gamma\,\sw2}},\qquad \mathfrak v_i(0)\to\frac1{\sw2},
\]
has the dependence on $\mu_i$ and $\gamma$ of the adopted \SignSVD array, up
to constant factors, and is the evidence for that array. In the oversampled
regime itself, for $B\gg N$ and rows $i\ll N$ of the power law, the drift
coefficient is $\mathfrak d_i\sim\sqrt{\mu_iB/(2N)}$, the value in the main text's table; the adopted
\SignSVD array is larger by the uniform factor $\sqrt2$. A uniform factor $c$
in the drift at a fixed volatility rescales the matched-step clock of
\SignSVD by $c^{-2}$, so with the factor removed every ratio of first hitting
times below is halved; no exponent and no phase boundary changes. The adopted arrays with momentum reduce to it at a
rescaled step (\cref{rem:app-phase-momentum}). The \SignSGD array
is compared with the corrected mode array of the \SignSGD section in
\cref{rem:app-phase-sgd}. No statement of this section identifies a
trajectory of an algorithm.
\end{remark}
```
-/
theorem rem_app_phase_adoption_i [Countable ι] (A : PhaseArrays ι) {c ε : ℝ} (hc : 0 < c)
    (hε : 0 < ε) (m m' : RowModel ι)
    (hm : IsMatchedModel A m ε) (hm' : IsMatchedModel (scaledArrays c 1 A) m' ε)
    (Q Q' : ℝ → ℝ) (hQ : IsVolterraSol m Q) (hQ' : IsVolterraSol m' Q') (ℓ : ℝ) (hℓ : 0 < ℓ) :
    firstHit (riskClock m' Q') ℓ = ENNReal.ofReal (1 / c ^ 2) * firstHit (riskClock m Q) ℓ :=
  scaling_hitting A hc one_pos hε m m' hm hm' Q Q' hQ hQ' ℓ hℓ

private lemma scl_sqrt_mu (α x : ℝ) (hx : 0 < x) :
    Real.sqrt (x ^ (-α)) = x ^ (-(α / 2)) := by
  rw [show x ^ (-α) = (x ^ (-(α / 2))) ^ 2 by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx.le]; congr 1; push_cast; ring]
  exact Real.sqrt_sq (Real.rpow_nonneg hx.le _)

private lemma scl_sqrt_ratio (E N B : ℝ) (hE : 0 ≤ E) (hN : 0 < N) (hB : 0 < B) :
    Real.sqrt (E / N) = Real.sqrt (E / B) * (Real.sqrt (N / B))⁻¹ := by
  have hq : 0 < Real.sqrt (N / B) := Real.sqrt_pos.2 (div_pos hN hB)
  rw [show E / B = E / N * (N / B) by field_simp, Real.sqrt_mul (div_nonneg hE hN.le) (N / B)]
  rw [mul_assoc, mul_inv_cancel₀ hq.ne', mul_one]

private lemma scl_mom_d (α ς : ℝ) (N B : ℕ) (β : ℝ) (hN : 1 ≤ N) (hNB : N ≤ B)
    (hβ0 : 0 ≤ β) (hβ1 : β < 1) (i : Fin N) :
    (momentumArrays α ς N B β).d i = Real.sqrt (momentumBeff B β / B) * (svdArrays α ς N B).d i := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hB' : (0 : ℝ) < B := by exact_mod_cast (show 0 < B by omega)
  have hE : 0 < momentumBeff B β := by
    unfold momentumBeff
    exact div_pos (mul_pos hB' (by linarith)) (by linarith)
  have hx : 0 < idxR i := by unfold idxR; positivity
  show Real.sqrt (muOf α N i) * Real.sqrt (momentumBeff B β / (N : ℝ))
    = Real.sqrt (momentumBeff B β / B) * (gammaRat N B ^ (-(1 / 2 : ℝ)) * idxR i ^ (-(α / 2)))
  unfold muOf gammaRat
  rw [scl_sqrt_mu α _ hx, scl_sqrt_ratio _ _ _ hE.le hN' hB',
    Real.rpow_neg (div_nonneg hN'.le hB'.le), ← Real.sqrt_eq_rpow]
  ring

/-- `rem:app-phase-momentum`, part (a) (l.1496–1542): the momentum arrays are the
SignSVD arrays with `c = √(B_eff/B)` in the drift and `c²` in the volatility, the noise constant is
`𝒮^β = c 𝒮_{s-SVD}`, and the momentum array at step `η` equals the SignSVD array at step `η c`
in the row right-hand side. Only the array identities and the step correspondence are stated here;
the scalar sentence `𝒮^β` is clause 5.

Snapshot `cr-2026-10-23`. Source: `sections/07-phase-comparison/section.tex` l.1496–1542.
```latex
\begin{remark}[Momentum arrays]\label{rem:app-phase-momentum}
For $\bmom\in[0,1)$ put $B_{\rm eff}\defeq B(1+\bmom)/(1-\bmom)=B/\sw2$. The
adopted \Muon array with momentum $\bmom$ has the $\mu_i$ and $\fQ_i(0)$ of
\cref{def:app-phase-arrays}, the batch $B_{\rm eff}$ in place of $B$ in the
drift, and the volatility multiplied by $B_{\rm eff}/B$:
\[
\mathfrak d_i^{\bmom}\defeq\sqrt{\mu_i}\sqrt{\frac{B_{\rm eff}}N}=\sqrt{\frac{B_{\rm eff}}B}\;\mathfrak d_i^{\text{s-SVD}},\qquad
\mathfrak v_i^{\bmom}\defeq\frac{B_{\rm eff}}B=\frac{B_{\rm eff}}B\;\mathfrak v_i^{\text{s-SVD}} .
\]
At $\bmom=0$ it is the \SignSVD array. The evidence for it is the
resolved-window endpoint of \cref{cor:app-pl-endpoints}(ii), quoted in
\cref{rem:app-phase-adoption}, which reads
$\sqrt2\,\mathfrak d_i(0)\sim\sqrt{\mu_iB_{\rm eff}/N}$ and
$\mathfrak v_i(0)\to B_{\rm eff}/B$ in this notation.

The momentum array at a step $\lr$ is the \SignSVD array at the step
$\lr\sqrt{B_{\rm eff}/B}$. For every $\lr>0$, the right side of
\cref{eqn:app-phase-rows} satisfies
\[
-\frac{2\lr\,\mathfrak d_i^{\bmom}}{\sqrt{\fRisk}}\,\fQ_i+\lr^2\mathfrak v_i^{\bmom}
=-\frac{2\lr'\,\mathfrak d_i^{\text{s-SVD}}}{\sqrt{\fRisk}}\,\fQ_i+\lr'^2\mathfrak v_i^{\text{s-SVD}},
\qquad \lr'\defeq\lr\sqrt{\frac{B_{\rm eff}}B} .
\]
By \cref{eqn:app-phase-F0S} the noise constant of the momentum array is
$\mathcal S^{\bmom}=\sqrt{B_{\rm eff}/B}\,\mathcal S_{\text{s-SVD}}$, so its matched
step $2\sqrt\epsilon/\mathcal S^{\bmom}$ is mapped to the matched step
$\lr^\star_{\text{s-SVD}}$. At matched steps the two models therefore solve the
same row equations from the same initial values, and they have the same
solution by the uniqueness in \cref{thm:app-phase-clock}. In particular
$t^{\bmom}_{T\epsilon}=t^{\text{s-SVD}}_{T\epsilon}$, and
\cref{thm:app-phase-map}, \cref{cor:app-phase-ratio} and
\cref{prop:app-phase-winners} hold for the momentum array without change.
Written with the noise constant of the momentum array, the saturated
prefactor $\sqrt\gamma\,\mathcal S_{\text{s-SVD}}$ of \cref{eqn:app-phase-tsvd}
is $\sqrt{N/B_{\rm eff}}\,\mathcal S^{\bmom}$.

The oversampled isotropic case refines the volatility factor. There the
volatility with momentum is $c_\bmom B_{\rm eff}/B$ times the volatility
without momentum, with $c_\bmom\defeq\sw2V_\bmom\in(\sw2,1)$, up to a factor
$1+O(\gamma)$ (\cref{rem:app-iso-momentum,lem:app-iso-V}). A factor $c>0$
on every volatility of an array multiplies every matched-step hitting time
by $c$. Indeed, the noise constant becomes $c\,\mathcal S$ and the matched step
becomes $\lr^\star/c$, so the right side of \cref{eqn:app-phase-rows} becomes
$1/c$ times its value for the original array at its matched step. The risk
of the modified model at time $t$ is therefore the original risk at time
$t/c$.
\end{remark}
```
-/
theorem rem_app_phase_momentum_i (α ς : ℝ) (N B : ℕ) (hα : 0 < α) (hp : 1 < α + ς)
    (hN : 1 ≤ N) (hNB : N ≤ B) (β : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β < 1) :
    (∀ i : Fin N, (momentumArrays α ς N B β).μ i = (svdArrays α ς N B).μ i) ∧
    (∀ i : Fin N, (momentumArrays α ς N B β).Q0 i = (svdArrays α ς N B).Q0 i) ∧
    (∀ i : Fin N, (momentumArrays α ς N B β).d i =
        Real.sqrt (momentumBeff B β / B) * (svdArrays α ς N B).d i) ∧
    (∀ i : Fin N, (momentumArrays α ς N B β).v i =
        (momentumBeff B β / B) * (svdArrays α ς N B).v i) ∧
    PhaseArrays.S (momentumArrays α ς N B β) =
        Real.sqrt (momentumBeff B β / B) * PhaseArrays.S (svdArrays α ς N B) ∧
    (∀ ε : ℝ, 0 < ε →
        Real.sqrt (momentumBeff B β / B) * matchedStep (momentumArrays α ς N B β) ε =
          matchedStep (svdArrays α ς N B) ε) ∧
    (∀ η : ℝ, 0 < η → ∀ (i : Fin N) (x R : ℝ),
        rowRHS η ((momentumArrays α ς N B β).d i) ((momentumArrays α ς N B β).v i) x R =
          rowRHS (η * Real.sqrt (momentumBeff B β / B)) ((svdArrays α ς N B).d i)
            ((svdArrays α ς N B).v i) x R) := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hB' : (0 : ℝ) < B := by exact_mod_cast (show 0 < B by omega)
  have hE : 0 < momentumBeff B β := by
    unfold momentumBeff
    exact div_pos (mul_pos hB' (by linarith)) (by linarith)
  have hEB : 0 < momentumBeff B β / B := div_pos hE hB'
  have ha : 0 < Real.sqrt (momentumBeff B β / B) := Real.sqrt_pos.2 hEB
  have hD : ∀ i : Fin N, 0 < (svdArrays α ς N B).d i := fun i => by
    show 0 < gammaRat N B ^ (-(1 / 2 : ℝ)) * idxR i ^ (-(α / 2))
    have hg : 0 < gammaRat N B := div_pos hN' hB'
    have hx : 0 < idxR i := by unfold idxR; positivity
    exact mul_pos (Real.rpow_pos_of_pos hg _) (Real.rpow_pos_of_pos hx _)
  have hvs : ∀ i : Fin N, (momentumArrays α ς N B β).v i
      = Real.sqrt (momentumBeff B β / B) ^ 2 * (svdArrays α ς N B).v i := fun i => by
    rw [Real.sq_sqrt hEB.le]
    show momentumBeff B β / B = momentumBeff B β / B * 1
    ring
  have hv1 : ∀ i : Fin N, (svdArrays α ς N B).v i = 1 := fun i => rfl
  have hS : PhaseArrays.S (momentumArrays α ς N B β)
      = Real.sqrt (momentumBeff B β / B) * PhaseArrays.S (svdArrays α ς N B) := by
    unfold PhaseArrays.S
    rw [← tsum_mul_left]
    refine tsum_congr fun i => ?_
    rw [hvs i, scl_mom_d α ς N B β hN hNB hβ0 hβ1 i, hv1 i]
    have h1 := (hD i).ne'
    have h2 := ha.ne'
    show (svdArrays α ς N B).μ i * (Real.sqrt (momentumBeff B β / B) ^ 2 * 1)
        / (2 * (Real.sqrt (momentumBeff B β / B) * (svdArrays α ς N B).d i))
      = Real.sqrt (momentumBeff B β / B) * ((svdArrays α ς N B).μ i * 1 / (2 * (svdArrays α ς N B).d i))
    field_simp
  refine ⟨fun i => rfl, fun i => rfl, fun i => scl_mom_d α ς N B β hN hNB hβ0 hβ1 i,
    fun i => by rw [hvs i, Real.sq_sqrt hEB.le], hS, ?_, ?_⟩
  · intro ε _
    unfold matchedStep
    rw [hS, ← mul_div_assoc, mul_div_mul_left _ _ ha.ne']
  · intro η _ i x R
    unfold rowRHS
    rw [scl_mom_d α ς N B β hN hNB hβ0 hβ1 i, hvs i]
    ring

/-- `rem:app-phase-momentum`, part (b) (l.1496–1542): at matched steps the momentum
model and the SignSVD model have the same first hitting time, `t^β_{Tε} = t^{s-SVD}_{Tε}`
(relied on by the Fig. `fig:tte-four-panel` caption and `thm:tte-half-aniso`).

Snapshot `cr-2026-10-23`. Source: `sections/07-phase-comparison/section.tex` l.1496–1542.
```latex
\begin{remark}[Momentum arrays]\label{rem:app-phase-momentum}
For $\bmom\in[0,1)$ put $B_{\rm eff}\defeq B(1+\bmom)/(1-\bmom)=B/\sw2$. The
adopted \Muon array with momentum $\bmom$ has the $\mu_i$ and $\fQ_i(0)$ of
\cref{def:app-phase-arrays}, the batch $B_{\rm eff}$ in place of $B$ in the
drift, and the volatility multiplied by $B_{\rm eff}/B$:
\[
\mathfrak d_i^{\bmom}\defeq\sqrt{\mu_i}\sqrt{\frac{B_{\rm eff}}N}=\sqrt{\frac{B_{\rm eff}}B}\;\mathfrak d_i^{\text{s-SVD}},\qquad
\mathfrak v_i^{\bmom}\defeq\frac{B_{\rm eff}}B=\frac{B_{\rm eff}}B\;\mathfrak v_i^{\text{s-SVD}} .
\]
At $\bmom=0$ it is the \SignSVD array. The evidence for it is the
resolved-window endpoint of \cref{cor:app-pl-endpoints}(ii), quoted in
\cref{rem:app-phase-adoption}, which reads
$\sqrt2\,\mathfrak d_i(0)\sim\sqrt{\mu_iB_{\rm eff}/N}$ and
$\mathfrak v_i(0)\to B_{\rm eff}/B$ in this notation.

The momentum array at a step $\lr$ is the \SignSVD array at the step
$\lr\sqrt{B_{\rm eff}/B}$. For every $\lr>0$, the right side of
\cref{eqn:app-phase-rows} satisfies
\[
-\frac{2\lr\,\mathfrak d_i^{\bmom}}{\sqrt{\fRisk}}\,\fQ_i+\lr^2\mathfrak v_i^{\bmom}
=-\frac{2\lr'\,\mathfrak d_i^{\text{s-SVD}}}{\sqrt{\fRisk}}\,\fQ_i+\lr'^2\mathfrak v_i^{\text{s-SVD}},
\qquad \lr'\defeq\lr\sqrt{\frac{B_{\rm eff}}B} .
\]
By \cref{eqn:app-phase-F0S} the noise constant of the momentum array is
$\mathcal S^{\bmom}=\sqrt{B_{\rm eff}/B}\,\mathcal S_{\text{s-SVD}}$, so its matched
step $2\sqrt\epsilon/\mathcal S^{\bmom}$ is mapped to the matched step
$\lr^\star_{\text{s-SVD}}$. At matched steps the two models therefore solve the
same row equations from the same initial values, and they have the same
solution by the uniqueness in \cref{thm:app-phase-clock}. In particular
$t^{\bmom}_{T\epsilon}=t^{\text{s-SVD}}_{T\epsilon}$, and
\cref{thm:app-phase-map}, \cref{cor:app-phase-ratio} and
\cref{prop:app-phase-winners} hold for the momentum array without change.
Written with the noise constant of the momentum array, the saturated
prefactor $\sqrt\gamma\,\mathcal S_{\text{s-SVD}}$ of \cref{eqn:app-phase-tsvd}
is $\sqrt{N/B_{\rm eff}}\,\mathcal S^{\bmom}$.

The oversampled isotropic case refines the volatility factor. There the
volatility with momentum is $c_\bmom B_{\rm eff}/B$ times the volatility
without momentum, with $c_\bmom\defeq\sw2V_\bmom\in(\sw2,1)$, up to a factor
$1+O(\gamma)$ (\cref{rem:app-iso-momentum,lem:app-iso-V}). A factor $c>0$
on every volatility of an array multiplies every matched-step hitting time
by $c$. Indeed, the noise constant becomes $c\,\mathcal S$ and the matched step
becomes $\lr^\star/c$, so the right side of \cref{eqn:app-phase-rows} becomes
$1/c$ times its value for the original array at its matched step. The risk
of the modified model at time $t$ is therefore the original risk at time
$t/c$.
\end{remark}
```
-/
theorem rem_app_phase_momentum_ii (α ς : ℝ) (N B : ℕ) (hα : 0 < α) (hp : 1 < α + ς)
    (hN : 1 ≤ N) (hNB : N ≤ B) (β : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    {ε : ℝ} (hε : 0 < ε) (T : ℝ) (hT : 0 < T) (mβ ms : RowModel (Fin N))
    (hmβ : IsMatchedModel (momentumArrays α ς N B β) mβ ε)
    (hms : IsMatchedModel (svdArrays α ς N B) ms ε)
    (Qβ Qs : ℝ → ℝ) (hQβ : IsVolterraSol mβ Qβ) (hQs : IsVolterraSol ms Qs) :
    firstHit (riskClock mβ Qβ) (T * ε) = firstHit (riskClock ms Qs) (T * ε) := by
  have hB : (0 : ℝ) < B := by exact_mod_cast (show 0 < B by omega)
  have hE : 0 < momentumBeff B β := by
    unfold momentumBeff
    exact div_pos (mul_pos hB (by linarith)) (by linarith)
  have hEB : 0 < momentumBeff B β / B := div_pos hE hB
  let c : ℝ := Real.sqrt (momentumBeff B β / B)
  have hc : 0 < c := Real.sqrt_pos.2 hEB
  have hids := rem_app_phase_momentum_i α ς N B hα hp hN hNB β hβ0 hβ1
  have hd : (momentumArrays α ς N B β).d =
      (scaledArrays c (c ^ 2) (svdArrays α ς N B)).d :=
    funext hids.2.2.1
  have hv : (momentumArrays α ς N B β).v =
      (scaledArrays c (c ^ 2) (svdArrays α ς N B)).v := by
    funext i
    change (momentumArrays α ς N B β).v i = c ^ 2 * (svdArrays α ς N B).v i
    dsimp only [c]
    rw [Real.sq_sqrt hEB.le]
    exact hids.2.2.2.1 i
  have hA : momentumArrays α ς N B β = scaledArrays c (c ^ 2) (svdArrays α ς N B) := by
    change PhaseArrays.mk _ _ _ _ = PhaseArrays.mk _ _ _ _
    congr 1
  have hmβ' : IsMatchedModel (scaledArrays c (c ^ 2) (svdArrays α ς N B)) mβ ε := by
    rw [← hA]
    exact hmβ
  have h := scaling_hitting (svdArrays α ς N B) hc (pow_pos hc 2) hε ms mβ
    hms hmβ' Qs Qβ hQs hQβ (T * ε) (mul_pos hT hε)
  simpa only [div_self (pow_ne_zero 2 hc.ne'), ENNReal.ofReal_one, one_mul] using h

/-- `rem:app-phase-momentum`, part (c) (l.1496–1542): a factor `c > 0` on every
volatility multiplies every matched-step hitting time by `c` (`scaledArrays 1 c`; the risk of the
modified model at time `t` is the original risk at time `t/c`).

Snapshot `cr-2026-10-23`. Source: `sections/07-phase-comparison/section.tex` l.1496–1542.
```latex
\begin{remark}[Momentum arrays]\label{rem:app-phase-momentum}
For $\bmom\in[0,1)$ put $B_{\rm eff}\defeq B(1+\bmom)/(1-\bmom)=B/\sw2$. The
adopted \Muon array with momentum $\bmom$ has the $\mu_i$ and $\fQ_i(0)$ of
\cref{def:app-phase-arrays}, the batch $B_{\rm eff}$ in place of $B$ in the
drift, and the volatility multiplied by $B_{\rm eff}/B$:
\[
\mathfrak d_i^{\bmom}\defeq\sqrt{\mu_i}\sqrt{\frac{B_{\rm eff}}N}=\sqrt{\frac{B_{\rm eff}}B}\;\mathfrak d_i^{\text{s-SVD}},\qquad
\mathfrak v_i^{\bmom}\defeq\frac{B_{\rm eff}}B=\frac{B_{\rm eff}}B\;\mathfrak v_i^{\text{s-SVD}} .
\]
At $\bmom=0$ it is the \SignSVD array. The evidence for it is the
resolved-window endpoint of \cref{cor:app-pl-endpoints}(ii), quoted in
\cref{rem:app-phase-adoption}, which reads
$\sqrt2\,\mathfrak d_i(0)\sim\sqrt{\mu_iB_{\rm eff}/N}$ and
$\mathfrak v_i(0)\to B_{\rm eff}/B$ in this notation.

The momentum array at a step $\lr$ is the \SignSVD array at the step
$\lr\sqrt{B_{\rm eff}/B}$. For every $\lr>0$, the right side of
\cref{eqn:app-phase-rows} satisfies
\[
-\frac{2\lr\,\mathfrak d_i^{\bmom}}{\sqrt{\fRisk}}\,\fQ_i+\lr^2\mathfrak v_i^{\bmom}
=-\frac{2\lr'\,\mathfrak d_i^{\text{s-SVD}}}{\sqrt{\fRisk}}\,\fQ_i+\lr'^2\mathfrak v_i^{\text{s-SVD}},
\qquad \lr'\defeq\lr\sqrt{\frac{B_{\rm eff}}B} .
\]
By \cref{eqn:app-phase-F0S} the noise constant of the momentum array is
$\mathcal S^{\bmom}=\sqrt{B_{\rm eff}/B}\,\mathcal S_{\text{s-SVD}}$, so its matched
step $2\sqrt\epsilon/\mathcal S^{\bmom}$ is mapped to the matched step
$\lr^\star_{\text{s-SVD}}$. At matched steps the two models therefore solve the
same row equations from the same initial values, and they have the same
solution by the uniqueness in \cref{thm:app-phase-clock}. In particular
$t^{\bmom}_{T\epsilon}=t^{\text{s-SVD}}_{T\epsilon}$, and
\cref{thm:app-phase-map}, \cref{cor:app-phase-ratio} and
\cref{prop:app-phase-winners} hold for the momentum array without change.
Written with the noise constant of the momentum array, the saturated
prefactor $\sqrt\gamma\,\mathcal S_{\text{s-SVD}}$ of \cref{eqn:app-phase-tsvd}
is $\sqrt{N/B_{\rm eff}}\,\mathcal S^{\bmom}$.

The oversampled isotropic case refines the volatility factor. There the
volatility with momentum is $c_\bmom B_{\rm eff}/B$ times the volatility
without momentum, with $c_\bmom\defeq\sw2V_\bmom\in(\sw2,1)$, up to a factor
$1+O(\gamma)$ (\cref{rem:app-iso-momentum,lem:app-iso-V}). A factor $c>0$
on every volatility of an array multiplies every matched-step hitting time
by $c$. Indeed, the noise constant becomes $c\,\mathcal S$ and the matched step
becomes $\lr^\star/c$, so the right side of \cref{eqn:app-phase-rows} becomes
$1/c$ times its value for the original array at its matched step. The risk
of the modified model at time $t$ is therefore the original risk at time
$t/c$.
\end{remark}
```
-/
theorem rem_app_phase_momentum_iii [Countable ι] (A : PhaseArrays ι) {c ε : ℝ} (hc : 0 < c)
    (hε : 0 < ε) (m m' : RowModel ι)
    (hm : IsMatchedModel A m ε) (hm' : IsMatchedModel (scaledArrays 1 c A) m' ε)
    (Q Q' : ℝ → ℝ) (hQ : IsVolterraSol m Q) (hQ' : IsVolterraSol m' Q') (ℓ : ℝ) (hℓ : 0 < ℓ) :
    firstHit (riskClock m' Q') ℓ = ENNReal.ofReal c * firstHit (riskClock m Q) ℓ := by
  have h := scaling_hitting A one_pos hc hε m m' hm hm' Q Q' hQ hQ' ℓ hℓ
  rwa [show c / (1:ℝ) ^ 2 = c by norm_num] at h


end Muon.Phase

end
